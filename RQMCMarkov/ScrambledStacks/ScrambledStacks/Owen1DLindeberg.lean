/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# A Lindeberg CLT for triangular arrays of bounded independent terms (for post #2)

Copied from `RQMCMarkov/OwenScrambling`.

Mathlib has the CLT for i.i.d. sequences only. Post #2's claim about Owen scrambling ("a standard
CLT applies") concerns sums of independent but NOT identically distributed terms (one per cell of
the net, see `Owen1DScramble`), whose number grows with `n`: a triangular array. This module
proves the CLT for such arrays under the bounded form of Lindeberg's condition, by characteristic
functions and Lévy's continuity theorem (Mathlib's
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`).

## Main results

* `norm_prod_sub_prod_le`: `‖Πᵢ aᵢ − Πᵢ cᵢ‖ ≤ Σᵢ ‖aᵢ − cᵢ‖` when all `‖aᵢ‖, ‖cᵢ‖ ≤ 1`.
* `norm_charFun_sub_le_of_abs_le`: for centred `X` with `|X| ≤ δ` a.s. and `|t| δ ≤ 1`,
  `‖φ_X(t) − (1 − t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`.
* `tendstoInDistribution_sum_of_bounded` (**Lindeberg CLT, bounded form**): for each `n` let
  `X n 0, …, X n (L n − 1)` be independent and centred on a probability space `(Ωₙ, Pₙ)` with
  `|X n i| ≤ δₙ` a.s., `δₙ → 0`, and `Σᵢ E[(X n i)²] → v`. Then `Σᵢ X n i ⇒ N(0, v)`.

The bounded condition `max |X n i| ≤ δₙ → 0` with `Σᵢ Var → v` implies Lindeberg's condition
(each truncated second moment vanishes once `δₙ < ε`), and it is what the stratified estimator
satisfies for `C¹` integrands.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal Topology

/-- **Telescoping bound for products** of complex numbers of norm at most one:
`‖Πᵢ aᵢ − Πᵢ cᵢ‖ ≤ Σᵢ ‖aᵢ − cᵢ‖`. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a c : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hc : ∀ i ∈ s, ‖c i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, c i‖ ≤ ∑ i ∈ s, ‖a i - c i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, sub_self, norm_zero, Finset.sum_empty]
  | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      have ha' : ∀ i ∈ s, ‖a i‖ ≤ 1 := fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
      have hc' : ∀ i ∈ s, ‖c i‖ ≤ 1 := fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
      have hQ : ‖∏ i ∈ s, c i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun i _ ↦ norm_nonneg _) hc'
      have haj := ha j (Finset.mem_insert_self j s)
      have heq : a j * ∏ i ∈ s, a i - c j * ∏ i ∈ s, c i =
          a j * (∏ i ∈ s, a i - ∏ i ∈ s, c i) + (a j - c j) * ∏ i ∈ s, c i := by ring
      rw [heq]
      calc ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, c i) + (a j - c j) * ∏ i ∈ s, c i‖
          ≤ ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, c i‖ + ‖a j - c j‖ * ‖∏ i ∈ s, c i‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ 1 * ∑ i ∈ s, ‖a i - c i‖ + ‖a j - c j‖ * 1 := by
            gcongr
            exact ih ha' hc'
        _ = ‖a j - c j‖ + ∑ i ∈ s, ‖a i - c i‖ := by ring

/-- The cubic Taylor bound for `e^{iy}`: `‖e^{iy} − (1 − y²/2 + i y)‖ ≤ |y|³` for `|y| ≤ 1`. -/
theorem norm_cexp_mul_I_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp ((y : ℂ) * I) - (((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ |y| ^ 3 := by
  have hz : ‖(y : ℂ) * I‖ = |y| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hb := Complex.exp_bound (x := (y : ℂ) * I) (by rw [hz]; exact hy) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, ((y : ℂ) * I) ^ m / (m.factorial : ℂ) =
      ((1 - y ^ 2 / 2 : ℝ) : ℂ) + (y : ℂ) * I := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      mul_pow, I_sq, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two]
    push_cast
    ring
  rw [hsum, hz] at hb
  refine hb.trans ?_
  have h3 : (0 : ℝ) ≤ |y| ^ 3 := by positivity
  have hc : ((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * (3 : ℕ))⁻¹ ≤ 1 := by
    norm_num [Nat.factorial]
  calc |y| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * (3 : ℕ))⁻¹)
      ≤ |y| ^ 3 * 1 := mul_le_mul_of_nonneg_left hc h3
    _ = |y| ^ 3 := mul_one _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Characteristic function of a bounded centred variable**: if `|X| ≤ δ` a.s., `E[X] = 0` and
`|t| δ ≤ 1`, then `‖φ_X(t) − (1 − t² E[X²]/2)‖ ≤ |t|³ δ E[X²]`. -/
theorem norm_charFun_sub_le_of_abs_le {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) {δ : ℝ} (hb : ∀ᵐ ω ∂P, |X ω| ≤ δ) (h0 : ∫ ω, X ω ∂P = 0) {t : ℝ}
    (ht : |t| * δ ≤ 1) :
    ‖charFun (P.map X) t - ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ)‖ ≤
      |t| ^ 3 * δ * ∫ ω, X ω ^ 2 ∂P := by
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable δ
    (hb.mono fun ω hω ↦ by rw [Real.norm_eq_abs]; exact hω)
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) P := by
    refine Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (δ ^ 2) ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  set q : Ω → ℂ := fun ω ↦ ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ) + ((t * X ω : ℝ) : ℂ) * I with hq
  have hqi : Integrable q P := by
    refine Integrable.add ?_ ?_
    · exact ((integrable_const 1).sub ((hX2.const_mul (t ^ 2)).div_const 2)).ofReal.congr
        (Eventually.of_forall fun ω ↦ by
          change (((1 - t ^ 2 * X ω ^ 2 / 2 : ℝ)) : ℂ) = ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ)
          rw [mul_pow])
    · exact (hXi.const_mul t).ofReal.mul_const I
  have hqint : ∫ ω, q ω ∂P = ((1 - t ^ 2 * (∫ ω, X ω ^ 2 ∂P) / 2 : ℝ) : ℂ) := by
    rw [hq, integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_const_mul, h0, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]
    · congr 1
      rw [integral_sub (integrable_const 1) ((hX2.const_mul (t ^ 2)).div_const 2 |>.congr
        (Eventually.of_forall fun ω ↦ by
          change t ^ 2 * X ω ^ 2 / 2 = (t * X ω) ^ 2 / 2
          rw [mul_pow])), integral_const, integral_div,
        integral_congr_ae (Eventually.of_forall fun ω ↦ (mul_pow t (X ω) 2 : _)),
        integral_const_mul]
      rw [probReal_univ, one_smul]
    · exact ((integrable_const 1).sub ((hX2.const_mul (t ^ 2)).div_const 2)).ofReal.congr
        (Eventually.of_forall fun ω ↦ by
          change (((1 - t ^ 2 * X ω ^ 2 / 2 : ℝ)) : ℂ) = ((1 - (t * X ω) ^ 2 / 2 : ℝ) : ℂ)
          rw [mul_pow])
    · exact (hXi.const_mul t).ofReal.mul_const I
  have he : Integrable (fun ω ↦ cexp (((t * X ω : ℝ) : ℂ) * I)) P := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω ↦ ?_)
    · exact (Complex.continuous_exp.comp_aestronglyMeasurable
        ((Complex.continuous_ofReal.comp_aestronglyMeasurable
          (hX.const_mul t).aestronglyMeasurable).mul aestronglyMeasurable_const))
    · rw [Complex.norm_exp_ofReal_mul_I]
  have hcf : charFun (P.map X) t = ∫ ω, cexp (((t * X ω : ℝ) : ℂ) * I) ∂P := by
    rw [charFun_apply_real, integral_map hX]
    · congr 1
      funext ω
      push_cast
      rfl
    · exact (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
        continuous_const)).aestronglyMeasurable
  rw [hcf, ← hqint, ← integral_sub he hqi]
  refine (norm_integral_le_of_norm_le ((hX2.const_mul (|t| ^ 3 * δ))) ?_).trans ?_
  · filter_upwards [hb] with ω hω
    have hy : |t * X ω| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hω (abs_nonneg t)).trans ht
    refine (norm_cexp_mul_I_sub_le hy).trans ?_
    have h3 : |X ω| ^ 3 = |X ω| * X ω ^ 2 := by
      rw [← sq_abs (X ω)]
      ring
    rw [abs_mul, mul_pow, h3]
    have hX0 : 0 ≤ X ω ^ 2 := sq_nonneg _
    have ht0 : 0 ≤ |t| ^ 3 := by positivity
    calc |t| ^ 3 * (|X ω| * X ω ^ 2) ≤ |t| ^ 3 * (δ * X ω ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hω hX0) ht0
      _ = |t| ^ 3 * δ * X ω ^ 2 := by ring
  · rw [integral_const_mul]

/-- **Lindeberg CLT for triangular arrays, bounded form.** For each `n` let `X n i`, `i < L n`, be
independent, centred random variables on a probability space `(Ωₙ, Pₙ)`, with `|X n i| ≤ δₙ`
almost surely, `δₙ → 0`, and `Σᵢ E[(X n i)²] → v`. Then `Σᵢ X n i` converges in distribution to
`N(0, v)`. -/
theorem tendstoInDistribution_sum_of_bounded {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {L : ℕ → ℕ}
    {X : (n : ℕ) → Fin (L n) → Ω n → ℝ} (hXm : ∀ n i, AEMeasurable (X n i) (P n))
    (hind : ∀ n, iIndepFun (X n) (P n)) (h0 : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hbd : ∀ n i, ∀ᵐ ω ∂(P n), |X n i ω| ≤ δ n)
    {v : ℝ} (hv : Tendsto (fun n ↦ ∑ i, ∫ ω, X n i ω ^ 2 ∂(P n)) atTop (𝓝 v))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i, X n i ω) atTop Z P P' where
  forall_aemeasurable n := Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm n i
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    -- notation
    set w : (n : ℕ) → Fin (L n) → ℝ := fun n i ↦ ∫ ω, X n i ω ^ 2 ∂(P n) with hw
    set sv : ℕ → ℝ := fun n ↦ ∑ i, w n i with hsv
    have hw0 : ∀ n i, 0 ≤ w n i := fun n i ↦ integral_nonneg fun ω ↦ sq_nonneg _
    have hv0 : 0 ≤ v := ge_of_tendsto' hv fun n ↦ Finset.sum_nonneg fun i _ ↦ hw0 n i
    have hwδ : ∀ n i, w n i ≤ δ n ^ 2 := by
      intro n i
      have h : ∫ ω, X n i ω ^ 2 ∂(P n) ≤ ∫ _ω, δ n ^ 2 ∂(P n) := by
        refine integral_mono_ae ?_ (integrable_const _) ?_
        · refine Integrable.of_bound ((hXm n i).pow_const 2).aestronglyMeasurable (δ n ^ 2) ?_
          filter_upwards [hbd n i] with ω hω
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
        · filter_upwards [hbd n i] with ω hω
          rw [← sq_abs (X n i ω)]
          exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      rw [integral_const, probReal_univ, one_smul] at h
      exact h
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    change Tendsto (fun n ↦ charFun ((P n).map fun ω ↦ ∑ i, X n i ω) t) atTop
      (𝓝 (charFun (P'.map Z) t))
    have htarget : charFun (P'.map Z) t = ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ) := by
      rw [hZ.map_eq, charFun_gaussianReal, Real.coe_toNNReal _ hv0]
      push_cast
      congr 1
      ring
    rw [htarget]
    have hprod : ∀ n, charFun ((P n).map fun ω ↦ ∑ i, X n i ω) t =
        ∏ i, charFun ((P n).map (X n i)) t := fun n ↦ by
      rw [(hind n).charFun_map_fun_sum_eq_prod (hXm n), Finset.prod_apply]
    simp_rw [hprod]
    -- the Gaussian comparison products
    set a : (n : ℕ) → Fin (L n) → ℝ := fun n i ↦ t ^ 2 * w n i / 2 with ha
    have hcprod : ∀ n, ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ) =
        ((Real.exp (-(t ^ 2 * sv n / 2)) : ℝ) : ℂ) := fun n ↦ by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
      congr 3
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hlimc : Tendsto (fun n ↦ ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ)) := by
      simp_rw [hcprod]
      refine Tendsto.ofReal ((Real.continuous_exp.tendsto _).comp ?_)
      exact ((hv.const_mul (t ^ 2)).div_const 2).neg
    -- the error bound
    set B : ℕ → ℝ := fun n ↦ |t| ^ 3 * |δ n| * sv n + t ^ 2 * δ n ^ 2 / 2 * (t ^ 2 * sv n / 2)
      with hB
    have hB0 : Tendsto B atTop (𝓝 0) := by
      have h1 : Tendsto B atTop
          (𝓝 (|t| ^ 3 * |(0 : ℝ)| * v + t ^ 2 * (0 : ℝ) ^ 2 / 2 * (t ^ 2 * v / 2))) := by
        refine Tendsto.add ((tendsto_const_nhds.mul hδ.abs).mul hv) ?_
        exact (((tendsto_const_nhds.mul (hδ.pow 2)).div_const 2).mul
          ((hv.const_mul (t ^ 2)).div_const 2))
      rw [abs_zero] at h1
      convert h1 using 2
      ring
    have hev : ∀ᶠ n in atTop, |t| * |δ n| ≤ 1 := by
      have h := (tendsto_const_nhds (x := |t|)).mul hδ.abs
      rw [abs_zero, mul_zero] at h
      exact h.eventually (ge_mem_nhds one_pos)
    have hbound : ∀ᶠ n in atTop, ‖∏ i, charFun ((P n).map (X n i)) t -
        ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤ B n := by
      filter_upwards [hev] with n hn
      have hai0 : ∀ i, 0 ≤ a n i := fun i ↦ by
        rw [ha]
        have := hw0 n i
        positivity
      have haiδ : ∀ i, a n i ≤ t ^ 2 * δ n ^ 2 / 2 := fun i ↦ by
        rw [ha]
        have := hwδ n i
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        have := mul_le_mul_of_nonneg_left this ht2
        linarith
      have htd : t ^ 2 * δ n ^ 2 ≤ 1 := by
        have h1 : (|t| * |δ n|) ^ 2 ≤ 1 := by
          have h0' : 0 ≤ |t| * |δ n| := by positivity
          nlinarith
        rw [mul_pow, sq_abs, sq_abs] at h1
        exact h1
      have hai1 : ∀ i, a n i ≤ 1 := fun i ↦ by linarith [haiδ i]
      refine (norm_prod_sub_prod_le Finset.univ _ _ (fun i _ ↦ norm_charFun_le_one _)
        (fun i _ ↦ ?_)).trans ?_
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          Real.exp_le_one_iff]
        linarith [hai0 i]
      have hterm : ∀ i, ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
          |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := by
        intro i
        have h1 := norm_charFun_sub_le_of_abs_le (hXm n i)
          ((hbd n i).mono fun ω hω ↦ hω.trans (le_abs_self _)) (h0 n i) hn
        have h2 : |Real.exp (-a n i) - 1 - (-a n i)| ≤ (-a n i) ^ 2 :=
          Real.abs_exp_sub_one_sub_id_le (by rw [abs_neg, abs_of_nonneg (hai0 i)]; exact hai1 i)
        have h3 : ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤
            t ^ 2 * δ n ^ 2 / 2 * a n i := by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          have heq : 1 - t ^ 2 * w n i / 2 - Real.exp (-a n i) =
              -(Real.exp (-a n i) - 1 - (-a n i)) := by
            rw [ha]
            ring
          rw [heq, abs_neg]
          refine h2.trans ?_
          rw [neg_sq, sq]
          exact mul_le_mul_of_nonneg_right (haiδ i) (hai0 i)
        calc ‖charFun ((P n).map (X n i)) t - ((Real.exp (-a n i) : ℝ) : ℂ)‖
            ≤ ‖charFun ((P n).map (X n i)) t - (((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ)‖ +
              ‖(((1 - t ^ 2 * w n i / 2 : ℝ)) : ℂ) - ((Real.exp (-a n i) : ℝ) : ℂ)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ |t| ^ 3 * |δ n| * w n i + t ^ 2 * δ n ^ 2 / 2 * a n i := add_le_add h1 h3
      refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hB]
      congr 2
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hdiff : Tendsto (fun n ↦ ∏ i, charFun ((P n).map (X n i)) t -
        ∏ i, ((Real.exp (-a n i) : ℝ) : ℂ)) atTop (𝓝 0) :=
      squeeze_zero_norm' hbound hB0
    have := hdiff.add hlimc
    rw [zero_add] at this
    refine this.congr (fun n ↦ ?_)
    ring

end RQMCMarkov.ScrambledStacks
