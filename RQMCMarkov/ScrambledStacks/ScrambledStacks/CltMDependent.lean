/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ScrambledStacks.Owen1DLindeberg
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Variance
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A CLT for sums of locally dependent terms of an i.i.d. sequence (for post #3)

Post #3 reports that "normality cannot be rejected for the per-state Sobol sequences ((ii) and
(iii))". For base-2 scrambled van der Corput stacks the error of the chain is (up to a
negligible remainder) a sum over the binary levels `m` of terms that are functions of i.i.d.
fair coins `e_m, e_{m+1}, …` (`CltPathBits`), each depending on coins far above `m` only with
geometrically small probability. This module proves the central limit theorem for such sums,
by truncating every term at depth `L` (an `L`-dependent array) and Bernstein's big-block /
small-block method, with the bounded Lindeberg CLT (`Owen1DLindeberg`).

## Main results

* `IsLocal F S`: `F : (ι → α) → β` depends only on the coordinates in the finite set `S`;
  `IsLocal.measurable` (for countable discrete `α`), `IsLocal.indepFun` (functions local on
  disjoint sets are independent under a product measure `Measure.infinitePi`).
* `charFun_map_sum_range_eq_prod`: sequential independence makes the characteristic function of
  a sum the product of the characteristic functions.
* `tendstoInDistribution_sum_range_of_bounded`: the bounded Lindeberg CLT under sequential
  independence (sums over `range (L n)`).
* `tendstoInMeasure_of_integral_sq`: second moments tending to `0` give convergence in measure.
* `sq_covariance_le`: Cauchy–Schwarz for the covariance.
* `tendstoInDistribution_of_blocks`: if `X n = Σ_b U n b + D n` with sequentially independent
  bounded blocks, `max |U n b| = o(σ_n)` and `Var D n = o(σ_n²)`, then
  `(X n − E X n)/σ_n ⇒ N(0,1)`.
* `tendstoInDistribution_of_truncations` (**the dependent CLT**): let `Y n m`, `m < K n`, be
  bounded by `B`, and for every depth `L` let `Yt n m L` be bounded by `B`, depend only on
  coordinates of levels in `[m, m + L)`, with `E[(Y n m − Yt n m L)²] ≤ C 2^{-L}`. If
  `K n → ∞` and `Var(Σ_m Y n m) ≥ κ K n` eventually, then the normalised sums are
  asymptotically `N(0,1)`. The proof takes `L = 2(⌊log₂ K⌋ + 1)` (so `K² 2^{-L} ≤ 1`: the
  truncation costs `O(1)` in `L²`) and windows of length `p = L³` (so `p = o(√K)` and
  `L²/p → 0`): the condition `L_K² ≪ p_K ≪ √K`, made explicit.
* `tendsto_natLog_pow_six_div`, `sqrt_variance_sum_le`, `abs_sqrt_variance_sub_le`: tools.
-/

namespace RQMCMarkov.ScrambledStacks

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

/-! ### Local functions of a product -/

/-- `F` depends only on the coordinates in the finite set `S`. -/
def IsLocal {ι α β : Type*} (F : (ι → α) → β) (S : Finset ι) : Prop :=
  ∀ ω ω' : ι → α, (∀ i ∈ S, ω i = ω' i) → F ω = F ω'

variable {ι α β γ : Type*}

/-- Locality is inherited by larger coordinate sets. -/
theorem IsLocal.mono {F : (ι → α) → β} {S T : Finset ι} (h : IsLocal F S) (hST : S ⊆ T) :
    IsLocal F T :=
  fun ω ω' hω ↦ h ω ω' fun i hi ↦ hω i (hST hi)

/-- A function of a local function is local. -/
theorem IsLocal.comp {F : (ι → α) → β} {S : Finset ι} (h : IsLocal F S) (g : β → γ) :
    IsLocal (fun ω ↦ g (F ω)) S :=
  fun ω ω' hω ↦ congrArg g (h ω ω' hω)

/-- Constants are local on any set. -/
theorem isLocal_const (b : β) (S : Finset ι) : IsLocal (fun _ : ι → α ↦ b) S :=
  fun _ _ _ ↦ rfl

/-- Sums of functions local on `S` are local on `S`. -/
theorem isLocal_sum {κ : Type*} {F : κ → (ι → α) → ℝ} {S : Finset ι} (s : Finset κ)
    (h : ∀ k ∈ s, IsLocal (F k) S) : IsLocal (fun ω ↦ ∑ k ∈ s, F k ω) S :=
  fun ω ω' hω ↦ Finset.sum_congr rfl fun k hk ↦ h k hk ω ω' hω

/-- The sum of two functions local on `S` is local on `S`. -/
theorem IsLocal.add {F G : (ι → α) → ℝ} {S : Finset ι} (hF : IsLocal F S) (hG : IsLocal G S) :
    IsLocal (fun ω ↦ F ω + G ω) S :=
  fun ω ω' hω ↦ by simp only [hF ω ω' hω, hG ω ω' hω]

open Classical in
/-- Extension of a point of `S → α` to `ι → α` by a fixed point `ω₀` off `S`. -/
noncomputable def localExtend (S : Finset ι) (ω₀ : ι → α) (g : S → α) : ι → α :=
  fun i ↦ if h : i ∈ S then g ⟨i, h⟩ else ω₀ i

/-- A local function factors through the restriction to its coordinate set. -/
theorem IsLocal.eq_restrict {F : (ι → α) → β} {S : Finset ι} (h : IsLocal F S) (ω₀ : ι → α)
    (ω : ι → α) : F ω = F (localExtend S ω₀ (S.restrict ω)) := by
  refine h _ _ fun i hi ↦ ?_
  simp only [localExtend, hi, dite_true, Finset.restrict]

variable [MeasurableSpace α]

/-- **Local functions are measurable** (countable discrete coordinate space). -/
theorem IsLocal.measurable [Countable α] [MeasurableSingletonClass α] [Nonempty α]
    [MeasurableSpace β] {F : (ι → α) → β} {S : Finset ι} (h : IsLocal F S) : Measurable F := by
  have ω₀ : ι → α := fun _ ↦ Classical.arbitrary α
  have : F = (fun g ↦ F (localExtend S ω₀ g)) ∘ S.restrict := funext (h.eq_restrict ω₀)
  rw [this]
  exact (measurable_of_countable _).comp (Finset.measurable_restrict S)

/-- **Independence of local functions.** Under a product measure, functions depending on
disjoint finite sets of coordinates are independent. -/
theorem IsLocal.indepFun [Countable α] [MeasurableSingletonClass α] [Nonempty α]
    [MeasurableSpace β] [MeasurableSpace γ] (ν : ι → Measure α) [∀ i, IsProbabilityMeasure (ν i)]
    {F : (ι → α) → β} {G : (ι → α) → γ} {S T : Finset ι} (hF : IsLocal F S) (hG : IsLocal G T)
    (hST : Disjoint S T) : IndepFun F G (Measure.infinitePi ν) := by
  have ω₀ : ι → α := fun _ ↦ Classical.arbitrary α
  have hcoord : iIndepFun (fun i (ω : ι → α) ↦ ω i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  have hST' := hcoord.indepFun_finset S T hST (fun i ↦ measurable_pi_apply i)
  have h1 : F = (fun g ↦ F (localExtend S ω₀ g)) ∘ (fun ω (i : S) ↦ ω i) :=
    funext (hF.eq_restrict ω₀)
  have h2 : G = (fun g ↦ G (localExtend T ω₀ g)) ∘ (fun ω (i : T) ↦ ω i) :=
    funext (hG.eq_restrict ω₀)
  rw [h1, h2]
  exact hST'.comp (measurable_of_countable _) (measurable_of_countable _)

/-! ### The Lindeberg CLT under sequential independence -/

/-- **Characteristic function of a sequentially independent sum.** If each `X i` is independent
of the partial sum of its predecessors, the characteristic function of `Σ_{i<k} X i` is the
product of the characteristic functions. -/
theorem charFun_map_sum_range_eq_prod {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) P)
    (hind : ∀ i, IndepFun (fun ω ↦ ∑ j ∈ range i, X j ω) (X i) P) (k : ℕ) (t : ℝ) :
    charFun (P.map fun ω ↦ ∑ i ∈ range k, X i ω) t = ∏ i ∈ range k, charFun (P.map (X i)) t := by
  induction k with
  | zero =>
      simp only [range_zero, sum_empty, prod_empty, Measure.map_const, measure_univ, one_smul,
        charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  | succ k ih =>
      have hsum : (fun ω ↦ ∑ i ∈ range (k + 1), X i ω) =
          fun ω ↦ (∑ i ∈ range k, X i ω) + X k ω := funext fun ω ↦ sum_range_succ _ _
      rw [hsum, (hind k).charFun_map_fun_add_eq_mul
        (Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm i) (hXm k), Pi.mul_apply, ih,
        prod_range_succ]

/-- **Lindeberg CLT, bounded form, sequential independence.** For each `n` let `X n i`,
`i < L n`, be centred random variables on `(Ωₙ, Pₙ)`, each independent of the partial sum of its
predecessors, with `|X n i| ≤ δₙ` a.s., `δₙ → 0` and `Σ_{i<L n} E[(X n i)²] → v`. Then
`Σ_{i<L n} X n i ⇒ N(0, v)`. (The proof of `tendstoInDistribution_sum_of_bounded`, with the
product formula `charFun_map_sum_range_eq_prod` in place of mutual independence.) -/
theorem tendstoInDistribution_sum_range_of_bounded {Ω : ℕ → Type*}
    {mΩ : ∀ n, MeasurableSpace (Ω n)} {P : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)] {L : ℕ → ℕ} {X : (n : ℕ) → ℕ → Ω n → ℝ}
    (hXm : ∀ n i, AEMeasurable (X n i) (P n))
    (hind : ∀ n i, IndepFun (fun ω ↦ ∑ j ∈ range i, X n j ω) (X n i) (P n))
    (h0 : ∀ n i, ∫ ω, X n i ω ∂(P n) = 0)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hbd : ∀ n i, ∀ᵐ ω ∂(P n), |X n i ω| ≤ δ n)
    {v : ℝ} (hv : Tendsto (fun n ↦ ∑ i ∈ range (L n), ∫ ω, X n i ω ^ 2 ∂(P n)) atTop (𝓝 v))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 v.toNNReal) P') :
    TendstoInDistribution (fun n ω ↦ ∑ i ∈ range (L n), X n i ω) atTop Z P P' where
  forall_aemeasurable n := Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm n i
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    set w : (n : ℕ) → ℕ → ℝ := fun n i ↦ ∫ ω, X n i ω ^ 2 ∂(P n) with hw
    set sv : ℕ → ℝ := fun n ↦ ∑ i ∈ range (L n), w n i with hsv
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
    change Tendsto (fun n ↦ charFun ((P n).map fun ω ↦ ∑ i ∈ range (L n), X n i ω) t) atTop
      (𝓝 (charFun (P'.map Z) t))
    have htarget : charFun (P'.map Z) t = ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ) := by
      rw [hZ.map_eq, charFun_gaussianReal, Real.coe_toNNReal _ hv0]
      push_cast
      congr 1
      ring
    rw [htarget]
    have hprod : ∀ n, charFun ((P n).map fun ω ↦ ∑ i ∈ range (L n), X n i ω) t =
        ∏ i ∈ range (L n), charFun ((P n).map (X n i)) t := fun n ↦
      charFun_map_sum_range_eq_prod (hXm n) (hind n) (L n) t
    simp_rw [hprod]
    set a : (n : ℕ) → ℕ → ℝ := fun n i ↦ t ^ 2 * w n i / 2 with ha
    have hcprod : ∀ n, ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ) =
        ((Real.exp (-(t ^ 2 * sv n / 2)) : ℝ) : ℂ) := fun n ↦ by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.sum_neg_distrib]
      congr 3
      rw [ha, hsv, ← Finset.sum_div, ← Finset.mul_sum]
    have hlimc : Tendsto (fun n ↦ ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(t ^ 2 * v / 2)) : ℝ) : ℂ)) := by
      simp_rw [hcprod]
      refine Tendsto.ofReal ((Real.continuous_exp.tendsto _).comp ?_)
      exact ((hv.const_mul (t ^ 2)).div_const 2).neg
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
    have hbound : ∀ᶠ n in atTop, ‖∏ i ∈ range (L n), charFun ((P n).map (X n i)) t -
        ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ)‖ ≤ B n := by
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
      refine (norm_prod_sub_prod_le (range (L n)) _ _ (fun i _ ↦ norm_charFun_le_one _)
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
    have hdiff : Tendsto (fun n ↦ ∏ i ∈ range (L n), charFun ((P n).map (X n i)) t -
        ∏ i ∈ range (L n), ((Real.exp (-a n i) : ℝ) : ℂ)) atTop (𝓝 0) :=
      squeeze_zero_norm' hbound hB0
    have := hdiff.add hlimc
    rw [zero_add] at this
    refine this.congr (fun n ↦ ?_)
    ring

/-! ### Second-moment tools -/

/-- **Second moments to zero give convergence in measure** (Chebyshev). -/
theorem tendstoInMeasure_of_integral_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} (hf : ∀ n, MemLp (f n) 2 μ)
    (h : Tendsto (fun n ↦ ∫ ω, f n ω ^ 2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hε2 : 0 < ε ^ 2 := by positivity
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_)
    ((h.div_const (ε ^ 2)).trans (by rw [zero_div]))
  have hint : Integrable (fun ω ↦ f n ω ^ 2) μ := (hf n).integrable_sq
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω ↦ sq_nonneg (f n ω))
    hint (ε ^ 2)
  have hsub : {x | ε ≤ ‖f n x - 0‖} ⊆ {x | ε ^ 2 ≤ f n x ^ 2} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hx ⊢
    rw [← sq_abs (f n x)]
    exact pow_le_pow_left₀ hε.le hx 2
  calc μ.real {x | ε ≤ ‖f n x - 0‖} ≤ μ.real {x | ε ^ 2 ≤ f n x ^ 2} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (∫ ω, f n ω ^ 2 ∂μ) / ε ^ 2 := by
        rw [le_div_iff₀ hε2, mul_comm]
        exact hmk

/-- **Cauchy–Schwarz for the covariance**: `cov[X, Y]² ≤ Var X · Var Y`. -/
theorem sq_covariance_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  have hq : ∀ t : ℝ, 0 ≤ Var[X; μ] * (t * t) + 2 * cov[X, Y; μ] * t + Var[Y; μ] := by
    intro t
    have h := variance_fun_add (hX.const_mul t) hY
    rw [variance_const_mul, covariance_const_mul_left] at h
    have h0 := variance_nonneg (fun ω ↦ t * X ω + Y ω) μ
    rw [h] at h0
    nlinarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- `|cov[X, Y]| ≤ √Var X · √Var Y`. -/
theorem abs_covariance_le_sqrt {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |cov[X, Y; μ]| ≤ √Var[X; μ] * √Var[Y; μ] := by
  rw [← Real.sqrt_mul (variance_nonneg _ _), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_covariance_le hX hY)

/-- **Triangle inequality for the standard deviation.** -/
theorem sqrt_variance_add_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    √Var[fun ω ↦ X ω + Y ω; μ] ≤ √Var[X; μ] + √Var[Y; μ] := by
  have hc := abs_covariance_le_sqrt hX hY
  have hsX := Real.sq_sqrt (variance_nonneg X μ)
  have hsY := Real.sq_sqrt (variance_nonneg Y μ)
  rw [Real.sqrt_le_left (by positivity), variance_fun_add hX hY]
  nlinarith [le_abs_self (cov[X, Y; μ])]

/-- The standard deviations of `X` and `W` differ by at most that of `X − W`. -/
theorem abs_sqrt_variance_sub_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X W : Ω → ℝ} (hX : MemLp X 2 μ) (hW : MemLp W 2 μ) :
    |√Var[W; μ] - √Var[X; μ]| ≤ √Var[fun ω ↦ X ω - W ω; μ] := by
  have hD : MemLp (fun ω ↦ X ω - W ω) 2 μ := hX.sub hW
  have h1 := sqrt_variance_add_le hW hD
  have h2 := sqrt_variance_add_le hX hD.neg
  have e1 : (fun ω ↦ W ω + (X ω - W ω)) = X := funext fun ω ↦ by ring
  have e2 : (fun ω ↦ X ω + (-(fun ω ↦ X ω - W ω)) ω) = W := funext fun ω ↦ by simp
  have e3 : Var[-(fun ω ↦ X ω - W ω); μ] = Var[fun ω ↦ X ω - W ω; μ] := variance_neg
  rw [e1] at h1
  rw [e2, e3] at h2
  rw [abs_le]
  constructor <;> linarith

/-! ### The CLT from independent bounded blocks -/

/-- **CLT from sequentially independent bounded blocks.** On a fixed probability space let
`X n = Σ_{b < J n} U n b + D n`, where each block `U n b` is independent of the sum of the
previous blocks, the blocks are pairwise independent, `|U n b| ≤ M n` with `M n = o(σ_n)`, and
`Var (D n) = o(σ_n²)`, `σ_n² = Var (X n)`. Then `(X n − E X n)/σ_n ⇒ N(0,1)`. -/
theorem tendstoInDistribution_of_blocks {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {U : ℕ → ℕ → Ω → ℝ} {J : ℕ → ℕ} {M : ℕ → ℝ}
    (hX : ∀ n, MemLp (X n) 2 μ) (hUm : ∀ n b, Measurable (U n b))
    (hUb : ∀ n b ω, |U n b ω| ≤ M n)
    (hind : ∀ n b, IndepFun (fun ω ↦ ∑ j ∈ range b, U n j ω) (U n b) μ)
    (hpair : ∀ n b b', b ≠ b' → IndepFun (U n b) (U n b') μ)
    (hpos : ∀ᶠ n in atTop, 0 < Var[X n; μ])
    (hM : Tendsto (fun n ↦ M n / √Var[X n; μ]) atTop (𝓝 0))
    (hD : Tendsto (fun n ↦ Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] / Var[X n; μ])
      atTop (𝓝 0))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω ↦ (X n ω - μ[X n]) / √Var[X n; μ]) atTop Z
      (fun _ ↦ μ) P' := by
  have : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  set σ : ℕ → ℝ := fun n ↦ √Var[X n; μ] with hσ
  have hσ0 : ∀ n, 0 ≤ σ n := fun n ↦ Real.sqrt_nonneg _
  have hM0 : ∀ n, 0 ≤ M n := fun n ↦ (abs_nonneg _).trans (hUb n 0 (Classical.arbitrary Ω))
  have hU2 : ∀ n b, MemLp (U n b) 2 μ := fun n b ↦
    MemLp.of_bound (hUm n b).aestronglyMeasurable (M n)
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hUb n b ω)
  have hUi : ∀ n b, Integrable (U n b) μ := fun n b ↦ (hU2 n b).integrable one_le_two
  have hEU : ∀ n b, |μ[U n b]| ≤ M n := fun n b ↦ by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := U n b) (C := M n)
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hUb n b ω)
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h
  -- the normalised centred blocks
  set ξ : ℕ → ℕ → Ω → ℝ := fun n b ω ↦ (U n b ω - μ[U n b]) / σ n with hξ
  have hξm : ∀ n b, Measurable (ξ n b) := fun n b ↦
    ((hUm n b).sub measurable_const).div_const _
  have hW2 : ∀ n, MemLp (fun ω ↦ ∑ b ∈ range (J n), U n b ω) 2 μ := fun n ↦
    memLp_finsetSum _ fun b _ ↦ hU2 n b
  -- `Σ_b Var (U n b) = Var (Σ_b U n b)`
  have hvarsum : ∀ n, ∑ b ∈ range (J n), Var[U n b; μ] =
      Var[fun ω ↦ ∑ b ∈ range (J n), U n b ω; μ] := fun n ↦ by
    have h := IndepFun.variance_sum (μ := μ) (X := U n) (s := range (J n))
      (fun b _ ↦ hU2 n b) (fun b _ b' _ hbb' ↦ hpair n b b' hbb')
    rw [← h]
    congr 1
    funext ω
    simp only [Finset.sum_apply]
  -- the variance ratio of the block sum tends to one
  have hratio : Tendsto (fun n ↦ Var[fun ω ↦ ∑ b ∈ range (J n), U n b ω; μ] / σ n ^ 2) atTop
      (𝓝 1) := by
    have hsq : Tendsto (fun n ↦ √(Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] /
        Var[X n; μ])) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hD
      rwa [Real.sqrt_zero] at this
    have hr : Tendsto (fun n ↦ √Var[fun ω ↦ ∑ b ∈ range (J n), U n b ω; μ] / σ n) atTop
        (𝓝 1) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hsq
      filter_upwards [hpos] with n hn
      have hσn : 0 < σ n := Real.sqrt_pos.2 hn
      have h := abs_sqrt_variance_sub_le (hX n) (hW2 n)
      rw [Real.norm_eq_abs, div_sub_one hσn.ne', abs_div, abs_of_pos hσn,
        Real.sqrt_div' _ hn.le]
      exact div_le_div_of_nonneg_right h hσn.le
    have := hr.pow 2
    rw [one_pow] at this
    refine this.congr' ?_
    filter_upwards [hpos] with n hn
    rw [div_pow, Real.sq_sqrt (variance_nonneg _ _)]
  have hLind : TendstoInDistribution (fun n ω ↦ ∑ b ∈ range (J n), ξ n b ω) atTop Z
      (fun _ ↦ μ) P' := by
    refine tendstoInDistribution_sum_range_of_bounded (P := fun _ ↦ μ) (L := J) (X := ξ)
      (fun n b ↦ (hξm n b).aemeasurable) (fun n b ↦ ?_) (fun n b ↦ ?_)
      (δ := fun n ↦ 2 * M n / σ n) ?_ (fun n b ↦ Eventually.of_forall fun ω ↦ ?_) (v := 1) ?_
      (by rwa [Real.toNNReal_one])
    · -- sequential independence is preserved by the affine normalisation
      have h := (hind n b).comp (φ := fun y ↦ (y - ∑ j ∈ range b, μ[U n j]) / σ n)
        (ψ := fun y ↦ (y - μ[U n b]) / σ n) (by fun_prop) (by fun_prop)
      refine h.congr ?_ (Eventually.of_forall fun ω ↦ rfl)
      refine Eventually.of_forall fun ω ↦ ?_
      simp only [Function.comp_apply, hξ, ← Finset.sum_div, Finset.sum_sub_distrib]
    · rw [hξ]
      simp only
      rw [integral_div, integral_sub (hUi n b) (integrable_const _), integral_const,
        probReal_univ, one_smul, sub_self, zero_div]
    · have := hM.const_mul 2
      rw [mul_zero] at this
      refine this.congr fun n ↦ ?_
      ring
    · rw [hξ]
      simp only
      rw [abs_div, abs_of_nonneg (hσ0 n)]
      refine div_le_div_of_nonneg_right ?_ (hσ0 n)
      calc |U n b ω - μ[U n b]| ≤ |U n b ω| + |μ[U n b]| := abs_sub _ _
        _ ≤ M n + M n := add_le_add (hUb n b ω) (hEU n b)
        _ = 2 * M n := by ring
    · refine hratio.congr' ?_
      filter_upwards [hpos] with n hn
      rw [← hvarsum, Finset.sum_div]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [hξ]
      simp only
      rw [variance_eq_integral (hUm n b).aemeasurable, ← integral_div]
      congr 1
      funext ω
      rw [div_pow]
  -- the remainder tends to zero in measure
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hLind ?_
    (fun n ↦ (((hX n).aestronglyMeasurable.aemeasurable).sub aemeasurable_const).div_const _)
  have hDm : ∀ n, MemLp (fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω) 2 μ := fun n ↦
    (hX n).sub (hW2 n)
  set D : ℕ → Ω → ℝ := fun n ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω with hDdef
  have hED : ∀ n, μ[D n] = μ[X n] - ∑ b ∈ range (J n), μ[U n b] := fun n ↦ by
    rw [hDdef]
    simp only
    rw [integral_sub ((hX n).integrable one_le_two) (integrable_finsetSum _ fun b _ ↦ hUi n b),
      integral_finsetSum _ fun b _ ↦ hUi n b]
  have hpt : ∀ n, ((fun n ω ↦ (X n ω - μ[X n]) / √Var[X n; μ]) -
      fun n ω ↦ ∑ b ∈ range (J n), ξ n b ω) n = fun ω ↦ (D n ω - μ[D n]) * (σ n)⁻¹ := by
    intro n
    funext ω
    simp only [Pi.sub_apply, hξ, ← Finset.sum_div, Finset.sum_sub_distrib]
    rw [hED n]
    simp only [hDdef, hσ]
    ring
  refine tendstoInMeasure_of_integral_sq (fun n ↦ ?_) ?_
  · rw [hpt n]
    exact ((hDm n).sub (memLp_const _)).mul_const _
  · simp_rw [hpt]
    refine hD.congr' ?_
    filter_upwards [hpos] with n hn
    rw [variance_eq_integral (hDm n).aestronglyMeasurable.aemeasurable, div_eq_mul_inv,
      ← integral_mul_const]
    congr 1
    funext ω
    rw [mul_pow, inv_pow, Real.sq_sqrt hn.le]

/-! ### Asymptotics of the block lengths -/

/-- `⌊log₂ k⌋ → ∞`. -/
theorem tendsto_natLog_atTop : Tendsto (fun k : ℕ ↦ (Nat.log 2 k : ℝ)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.comp ?_
  refine tendsto_atTop_atTop.2 fun b ↦ ⟨2 ^ b, fun k hk ↦ Nat.le_log_of_pow_le one_lt_two hk⟩

/-- `(⌊log₂ k⌋ + 1)⁶ / k → 0`. -/
theorem tendsto_natLog_pow_six_div : Tendsto (fun k : ℕ ↦ ((Nat.log 2 k : ℝ) + 1) ^ 6 / k)
    atTop (𝓝 0) := by
  have hl : Tendsto (fun k : ℕ ↦ Real.log k ^ 6 / (1 * (k : ℝ) + 0)) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hc := hl.const_mul ((2 / Real.log 2) ^ 6)
  rw [mul_zero] at hc
  refine squeeze_zero' (Eventually.of_forall fun k ↦ by positivity) ?_ hc
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : 1 ≤ Nat.log 2 k := Nat.le_log_of_pow_le one_lt_two (by simpa using hk)
  have h2 : (Nat.log 2 k : ℝ) ≤ Real.log k / Real.log 2 := by
    have := Real.natLog_le_logb k 2
    rwa [Real.logb, Nat.cast_ofNat] at this
  have h3 : (Nat.log 2 k : ℝ) + 1 ≤ 2 / Real.log 2 * Real.log k := by
    have : (1 : ℝ) ≤ Nat.log 2 k := by exact_mod_cast h1
    have : (Nat.log 2 k : ℝ) + 1 ≤ 2 * (Real.log k / Real.log 2) := by linarith
    calc (Nat.log 2 k : ℝ) + 1 ≤ 2 * (Real.log k / Real.log 2) := this
      _ = 2 / Real.log 2 * Real.log k := by ring
  have h0 : (0 : ℝ) ≤ (Nat.log 2 k : ℝ) + 1 := by positivity
  rw [one_mul, add_zero, mul_div_assoc', ← mul_pow]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h3 6) hk0.le

/-- **Finite triangle inequality for the standard deviation.** -/
theorem sqrt_variance_sum_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {κ : Type*} (s : Finset κ) {X : κ → Ω → ℝ}
    (hX : ∀ k ∈ s, MemLp (X k) 2 μ) :
    √Var[fun ω ↦ ∑ k ∈ s, X k ω; μ] ≤ ∑ k ∈ s, √Var[X k; μ] := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [sum_empty]
      rw [show (fun _ : Ω ↦ (0 : ℝ)) = 0 from rfl, variance_zero, Real.sqrt_zero]
  | insert j s hj ih =>
      have hXs : ∀ k ∈ s, MemLp (X k) 2 μ := fun k hk ↦ hX k (mem_insert_of_mem hk)
      have e : (fun ω ↦ ∑ k ∈ insert j s, X k ω) = fun ω ↦ X j ω + ∑ k ∈ s, X k ω :=
        funext fun ω ↦ sum_insert hj
      rw [e, sum_insert hj]
      exact (sqrt_variance_add_le (hX j (mem_insert_self j s))
        (memLp_finsetSum s hXs)).trans (add_le_add le_rfl (ih hXs))

/-! ### The truncation CLT -/

/-- Finite sets of coordinates whose levels lie in disjoint ranges are disjoint. -/
theorem disjoint_of_lev {ι : Type*} (lev : ι → ℕ) {A A' : Finset ι} {a b : ℕ}
    (hA : ∀ i ∈ A, lev i < a) (hA' : ∀ i ∈ A', b ≤ lev i) (hab : a ≤ b) : Disjoint A A' :=
  Finset.disjoint_left.2 fun i hi hi' ↦ by
    have h1 := hA i hi
    have h2 := hA' i hi'
    omega

/-- The index window of `m` for blocks of length `p`: `p ⌊m/p⌋ ≤ m < p ⌊m/p⌋ + p`. -/
theorem div_mul_le_and_lt (m p : ℕ) (hp : 0 < p) : m / p * p ≤ m ∧ m < m / p * p + p :=
  ⟨Nat.div_mul_le_self m p, Nat.lt_div_mul_add hp⟩

variable {ι : Type*} [Countable α] [MeasurableSingletonClass α] [Nonempty α] in
/-- **CLT for sums of truncatable level terms of an independent sequence.** Coordinates `i : ι`
carry levels `lev i`; under the product measure `μ = ⊗ᵢ νᵢ` let `Y n m`, `m < K n`, be measurable
and bounded by `B`, and suppose each `Y n m` has, for every depth `L`, a truncation `Yt n m L`
bounded by `B` that depends only on finitely many coordinates of levels in `[m, m + L)`, with
`E[(Y n m − Yt n m L)²] ≤ C 2^{-L}`. If `K n → ∞` and `Var (Σ_{m<K n} Y n m) ≥ κ K n`
eventually (`κ > 0`), then the normalised sums converge in distribution to `N(0,1)`.

Proof: truncate at depth `L = 2(⌊log₂ K⌋ + 1)` (error `O(1)` in `L²`), cut the levels into
windows of length `p = L³`, keep in each window the terms whose truncation stays inside it
(independent bounded blocks of size `≤ p B = o(√K)`), and discard the last `L` levels of each
window (independent across windows, total variance `≤ (K/p + 1) L² B² = o(K)`); then
`tendstoInDistribution_of_blocks`. -/
theorem tendstoInDistribution_of_truncations (ν : ι → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (lev : ι → ℕ) {K : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    {Y : ℕ → ℕ → (ι → α) → ℝ} {Yt : ℕ → ℕ → ℕ → (ι → α) → ℝ} {B C κ : ℝ}
    (hYm : ∀ n m, Measurable (Y n m)) (hYb : ∀ n m ω, |Y n m ω| ≤ B)
    (hYtb : ∀ n m L ω, |Yt n m L ω| ≤ B)
    (hloc : ∀ n m L, ∃ S : Finset ι, (∀ i ∈ S, m ≤ lev i ∧ lev i < m + L) ∧
      IsLocal (Yt n m L) S)
    (htr : ∀ n m L,
      ∫ ω, (Y n m ω - Yt n m L ω) ^ 2 ∂(Measure.infinitePi ν) ≤ C * (1 / 2) ^ L)
    (hκ : 0 < κ)
    (hvar : ∀ᶠ n in atTop,
      κ * K n ≤ Var[fun ω ↦ ∑ m ∈ range (K n), Y n m ω; Measure.infinitePi ν])
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ω ↦ ((∑ m ∈ range (K n), Y n m ω) -
        (Measure.infinitePi ν)[fun ω ↦ ∑ m ∈ range (K n), Y n m ω]) /
        √Var[fun ω ↦ ∑ m ∈ range (K n), Y n m ω; Measure.infinitePi ν]) atTop Z
      (fun _ ↦ Measure.infinitePi ν) P' := by
  classical
  set μ := Measure.infinitePi ν with hμ
  choose S hSlev hSloc using hloc
  have hB : 0 ≤ B := (abs_nonneg _).trans (hYb 0 0 (fun _ ↦ Classical.arbitrary α))
  have hC : 0 ≤ C := by
    have h := htr 0 0 0
    rw [pow_zero, mul_one] at h
    exact (integral_nonneg fun ω ↦ sq_nonneg _).trans h
  -- block parameters
  set Lf : ℕ → ℕ := fun n ↦ 2 * (Nat.log 2 (K n) + 1) with hLf
  set pf : ℕ → ℕ := fun n ↦ Lf n ^ 3 with hpf
  set J : ℕ → ℕ := fun n ↦ K n / pf n + 1 with hJ
  have hL2 : ∀ n, 2 ≤ Lf n := fun n ↦ by simp only [hLf]; omega
  have hp : ∀ n, 0 < pf n := fun n ↦ pow_pos (by have := hL2 n; omega) 3
  have hLp : ∀ n, 2 * Lf n ≤ pf n := fun n ↦ by
    have h := hL2 n
    have e : pf n = Lf n * Lf n * Lf n := by simp only [hpf]; ring
    rw [e]
    have h1 : 2 * Lf n ≤ Lf n * Lf n := Nat.mul_le_mul_right _ h
    have h2 : Lf n * Lf n ≤ Lf n * Lf n * Lf n := Nat.le_mul_of_pos_right _ (by omega)
    omega
  set core : ℕ → ℕ → Prop := fun n m ↦ m % pf n + Lf n < pf n with hcore
  set X : ℕ → (ι → α) → ℝ := fun n ω ↦ ∑ m ∈ range (K n), Y n m ω with hX
  set FU : ℕ → ℕ → Finset ℕ := fun n b ↦
    ((range (K n)).filter (core n)).filter fun m ↦ m / pf n = b with hFU
  set FV : ℕ → ℕ → Finset ℕ := fun n b ↦
    ((range (K n)).filter fun m ↦ ¬ core n m).filter fun m ↦ m / pf n = b with hFV
  set U : ℕ → ℕ → (ι → α) → ℝ := fun n b ω ↦ ∑ m ∈ FU n b, Yt n m (Lf n) ω with hU
  set V : ℕ → ℕ → (ι → α) → ℝ := fun n b ω ↦ ∑ m ∈ FV n b, Yt n m (Lf n) ω with hV
  -- coordinate sets
  set SU : ℕ → ℕ → Finset ι := fun n b ↦ (FU n b).biUnion fun m ↦ S n m (Lf n) with hSU
  set SV : ℕ → ℕ → Finset ι := fun n b ↦ (FV n b).biUnion fun m ↦ S n m (Lf n) with hSV
  have hYtm : ∀ n m L, Measurable (Yt n m L) := fun n m L ↦ (hSloc n m L).measurable
  have hUloc : ∀ n b, IsLocal (U n b) (SU n b) := fun n b ↦
    isLocal_sum _ fun m hm ↦ (hSloc n m (Lf n)).mono
      (subset_biUnion_of_mem (fun m ↦ S n m (Lf n)) hm)
  have hVloc : ∀ n b, IsLocal (V n b) (SV n b) := fun n b ↦
    isLocal_sum _ fun m hm ↦ (hSloc n m (Lf n)).mono
      (subset_biUnion_of_mem (fun m ↦ S n m (Lf n)) hm)
  have hSUlev : ∀ n b, ∀ i ∈ SU n b, b * pf n ≤ lev i ∧ lev i < b * pf n + pf n := by
    intro n b i hi
    simp only [hSU, hFU, mem_biUnion, mem_filter, mem_range] at hi
    obtain ⟨m, ⟨⟨_, hcm⟩, hmb⟩, hiS⟩ := hi
    have h := hSlev n m (Lf n) i hiS
    have hw := Nat.div_add_mod' m (pf n)
    rw [hmb] at hw
    simp only [hcore] at hcm
    constructor
    · omega
    · omega
  have hSVlev : ∀ n b, ∀ i ∈ SV n b,
      b * pf n + pf n ≤ lev i + Lf n ∧ lev i < b * pf n + pf n + Lf n := by
    intro n b i hi
    simp only [hSV, hFV, mem_biUnion, mem_filter, mem_range] at hi
    obtain ⟨m, ⟨⟨_, hcm⟩, hmb⟩, hiS⟩ := hi
    have h := hSlev n m (Lf n) i hiS
    have hw := Nat.div_add_mod' m (pf n)
    have hlt := Nat.mod_lt m (hp n)
    rw [hmb] at hw
    simp only [hcore, not_lt] at hcm
    constructor
    · omega
    · omega
  -- cardinalities
  have hcardU : ∀ n b, (FU n b).card ≤ pf n := by
    intro n b
    refine (card_le_card (t := Finset.Ico (b * pf n) (b * pf n + pf n)) ?_).trans
      (by rw [Nat.card_Ico]; omega)
    intro m hm
    simp only [hFU, mem_filter] at hm
    have hw := div_mul_le_and_lt m (pf n) (hp n)
    rw [hm.2] at hw
    exact Finset.mem_Ico.2 hw
  have hcardV : ∀ n b, (FV n b).card ≤ Lf n := by
    intro n b
    refine (card_le_card (t := Finset.Ico (b * pf n + pf n - Lf n) (b * pf n + pf n)) ?_).trans
      (by rw [Nat.card_Ico]; have := hLp n; omega)
    intro m hm
    simp only [hFV, mem_filter, hcore, not_lt] at hm
    have hw := Nat.div_add_mod' m (pf n)
    have hlt := Nat.mod_lt m (hp n)
    rw [hm.2] at hw
    refine Finset.mem_Ico.2 ⟨?_, ?_⟩
    · have := hm.1.2
      omega
    · omega
  have hsum_le : ∀ (n : ℕ) (s : Finset ℕ) (ω : ι → α),
      |∑ m ∈ s, Yt n m (Lf n) ω| ≤ s.card * B := fun n s ω ↦ by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ s, |Yt n m (Lf n) ω| ≤ ∑ _m ∈ s, B := sum_le_sum fun m _ ↦ hYtb n m _ ω
      _ = s.card * B := by rw [sum_const, nsmul_eq_mul]
  have hUb : ∀ n b ω, |U n b ω| ≤ pf n * B := fun n b ω ↦
    (hsum_le n _ ω).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardU n b) hB)
  have hVb : ∀ n b ω, |V n b ω| ≤ Lf n * B := fun n b ω ↦
    (hsum_le n _ ω).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcardV n b) hB)
  -- integrability
  have hYt2 : ∀ n m L, MemLp (Yt n m L) 2 μ := fun n m L ↦
    MemLp.of_bound (hYtm n m L).aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYtb n m L ω)
  have hY2 : ∀ n m, MemLp (Y n m) 2 μ := fun n m ↦
    MemLp.of_bound (hYm n m).aestronglyMeasurable B
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hYb n m ω)
  have hX2 : ∀ n, MemLp (X n) 2 μ := fun n ↦ memLp_finsetSum _ fun m _ ↦ hY2 n m
  have hUm : ∀ n b, Measurable (U n b) := fun n b ↦ (hUloc n b).measurable
  have hV2 : ∀ n b, MemLp (V n b) 2 μ := fun n b ↦ memLp_finsetSum _ fun m _ ↦ hYt2 n m _
  have hR2 : ∀ n m, MemLp (fun ω ↦ Y n m ω - Yt n m (Lf n) ω) 2 μ := fun n m ↦
    (hY2 n m).sub (hYt2 n m _)
  -- the decomposition `X = Σ_b U_b + Σ_b V_b + R`
  have hmaps : ∀ n, ∀ m ∈ range (K n), m / pf n ∈ range (J n) := fun n m hm ↦ by
    simp only [mem_range, hJ] at hm ⊢
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hm.le)
  have hdecomp : ∀ n ω, X n ω - ∑ b ∈ range (J n), U n b ω =
      ∑ b ∈ range (J n), V n b ω + ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω) := by
    intro n ω
    have h1 : ∑ b ∈ range (J n), U n b ω =
        ∑ m ∈ (range (K n)).filter (core n), Yt n m (Lf n) ω :=
      sum_fiberwise_of_maps_to (fun m hm ↦ hmaps n m (mem_filter.1 hm).1) _
    have h2 : ∑ b ∈ range (J n), V n b ω =
        ∑ m ∈ (range (K n)).filter (fun m ↦ ¬ core n m), Yt n m (Lf n) ω :=
      sum_fiberwise_of_maps_to (fun m hm ↦ hmaps n m (mem_filter.1 hm).1) _
    rw [h1, h2, sum_sub_distrib, hX]
    simp only
    rw [← sum_filter_add_sum_filter_not (range (K n)) (core n) (fun m ↦ Yt n m (Lf n) ω)]
    ring
  -- independence of the blocks
  have hind : ∀ n b, IndepFun (fun ω ↦ ∑ j ∈ range b, U n j ω) (U n b) μ := by
    intro n b
    refine IsLocal.indepFun ν (S := (range b).biUnion (SU n)) (T := SU n b)
      (isLocal_sum _ fun j hj ↦ (hUloc n j).mono (subset_biUnion_of_mem (SU n) hj))
      (hUloc n b) (disjoint_of_lev lev (a := b * pf n) (b := b * pf n) ?_ ?_ le_rfl)
    · intro i hi
      obtain ⟨j, hj, hij⟩ := mem_biUnion.1 hi
      have h := (hSUlev n j i hij).2
      have hjb : (j + 1) * pf n ≤ b * pf n := Nat.mul_le_mul_right _ (mem_range.1 hj)
      rw [add_mul, one_mul] at hjb
      omega
    · exact fun i hi ↦ (hSUlev n b i hi).1
  have hpairU : ∀ n b b', b < b' → IndepFun (U n b) (U n b') μ := by
    intro n b b' hbb'
    refine IsLocal.indepFun ν (hUloc n b) (hUloc n b')
      (disjoint_of_lev lev (a := b * pf n + pf n) (b := b' * pf n) (fun i hi ↦
        (hSUlev n b i hi).2) (fun i hi ↦ (hSUlev n b' i hi).1) ?_)
    have h : (b + 1) * pf n ≤ b' * pf n := Nat.mul_le_mul_right _ hbb'
    rw [add_mul, one_mul] at h
    exact h
  have hpairV : ∀ n b b', b < b' → IndepFun (V n b) (V n b') μ := by
    intro n b b' hbb'
    have h : (b + 1) * pf n ≤ b' * pf n := Nat.mul_le_mul_right _ hbb'
    rw [add_mul, one_mul] at h
    have hl := hLp n
    refine IsLocal.indepFun ν (hVloc n b) (hVloc n b')
      (disjoint_of_lev lev (a := b * pf n + pf n + Lf n) (b := b' * pf n + pf n - Lf n)
        (fun i hi ↦ (hSVlev n b i hi).2) (fun i hi ↦ ?_) (by omega))
    have := (hSVlev n b' i hi).1
    omega
  -- the variance of the discarded part
  have hVvar : ∀ n, Var[fun ω ↦ ∑ b ∈ range (J n), V n b ω; μ] ≤ J n * (Lf n * B) ^ 2 := by
    intro n
    have h := IndepFun.variance_sum (μ := μ) (X := V n) (s := range (J n))
      (fun b _ ↦ hV2 n b) (fun b _ b' _ hbb' ↦ by
        rcases lt_or_gt_of_ne hbb' with h | h
        · exact hpairV n b b' h
        · exact (hpairV n b' b h).symm)
    have e : (fun ω ↦ ∑ b ∈ range (J n), V n b ω) = ∑ b ∈ range (J n), V n b := by
      funext ω
      simp only [Finset.sum_apply]
    rw [e, h]
    calc ∑ b ∈ range (J n), Var[V n b; μ] ≤ ∑ _b ∈ range (J n), (Lf n * B) ^ 2 := by
          refine sum_le_sum fun b _ ↦ ?_
          have hb := variance_le_sq_of_bounded (μ := μ) (a := -(Lf n * B)) (b := Lf n * B)
            (Eventually.of_forall fun ω ↦ abs_le.1 (hVb n b ω))
            (hV2 n b).aestronglyMeasurable.aemeasurable
          refine hb.trans (le_of_eq ?_)
          ring
      _ = J n * (Lf n * B) ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
  have hRvar : ∀ n, √Var[fun ω ↦ ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω); μ] ≤ √C := by
    intro n
    refine (sqrt_variance_sum_le _ fun m _ ↦ hR2 n m).trans ?_
    have hterm : ∀ m, √Var[fun ω ↦ Y n m ω - Yt n m (Lf n) ω; μ] ≤
        √C * (1 / 2) ^ (Nat.log 2 (K n) + 1) := by
      intro m
      have h1 := variance_le_expectation_sq (μ := μ)
        (hR2 n m).aestronglyMeasurable
      have h2 := htr n m (Lf n)
      have e : (1 / 2 : ℝ) ^ Lf n = ((1 / 2) ^ (Nat.log 2 (K n) + 1)) ^ 2 := by
        rw [← pow_mul]
        simp only [hLf]
        ring_nf
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hC, ← e]
      refine h1.trans (le_of_eq_of_le ?_ h2)
      congr 1
    calc ∑ m ∈ range (K n), √Var[fun ω ↦ Y n m ω - Yt n m (Lf n) ω; μ]
        ≤ ∑ _m ∈ range (K n), √C * (1 / 2) ^ (Nat.log 2 (K n) + 1) := sum_le_sum fun m _ ↦ hterm m
      _ = √C * ((K n : ℝ) * (1 / 2) ^ (Nat.log 2 (K n) + 1)) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          ring
      _ ≤ √C * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          have hk : (K n : ℝ) < 2 ^ (Nat.log 2 (K n) + 1) := by
            exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two (K n)
          rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
          exact hk.le
      _ = √C := mul_one _
  have hDvar : ∀ n, Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] ≤
      2 * (J n * (Lf n * B) ^ 2) + 2 * C := by
    intro n
    have e : (fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω) = fun ω ↦
        (∑ b ∈ range (J n), V n b ω) + ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω) :=
      funext (hdecomp n)
    rw [e]
    have h := sqrt_variance_add_le (μ := μ) (memLp_finsetSum (range (J n)) fun b _ ↦ hV2 n b)
      (memLp_finsetSum (range (K n)) fun m _ ↦ hR2 n m)
    have h1 := Real.sqrt_le_sqrt (hVvar n)
    have h2 := hRvar n
    have hs := Real.sq_sqrt (variance_nonneg (fun ω ↦ (∑ b ∈ range (J n), V n b ω) +
      ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω)) μ)
    have hJ0 : (0 : ℝ) ≤ J n * (Lf n * B) ^ 2 := by positivity
    have hs1 := Real.sq_sqrt hJ0
    have hs2 := Real.sq_sqrt hC
    have hn1 := Real.sqrt_nonneg (J n * (Lf n * B) ^ 2)
    have hn2 := Real.sqrt_nonneg C
    have hn3 := Real.sqrt_nonneg (Var[fun ω ↦ (∑ b ∈ range (J n), V n b ω) +
      ∑ m ∈ range (K n), (Y n m ω - Yt n m (Lf n) ω); μ])
    have hsle := h.trans (add_le_add h1 h2)
    rw [← hs, ← hs1, ← hs2]
    have hsq := pow_le_pow_left₀ hn3 hsle 2
    nlinarith [sq_nonneg (√(J n * (Lf n * B) ^ 2) - √C)]
  -- asymptotics
  have hKev : ∀ᶠ n in atTop, 1 ≤ K n := hK.eventually_ge_atTop 1
  have hpos : ∀ᶠ n in atTop, 0 < Var[X n; μ] := by
    filter_upwards [hvar, hKev] with n hn hk
    have : (1 : ℝ) ≤ K n := by exact_mod_cast hk
    exact lt_of_lt_of_le (by positivity) hn
  have hLR : ∀ n, (Lf n : ℝ) = 2 * ((Nat.log 2 (K n) : ℝ) + 1) := fun n ↦ by
    simp only [hLf]
    push_cast
    ring
  have hL1le : ∀ n, (1 : ℝ) ≤ Lf n := fun n ↦ by
    have := (Nat.log 2 (K n)).cast_nonneg (α := ℝ)
    rw [hLR]
    linarith
  have hL6 : Tendsto (fun n ↦ (Lf n : ℝ) ^ 6 / K n) atTop (𝓝 0) := by
    have h := (tendsto_natLog_pow_six_div.comp hK).const_mul 64
    rw [mul_zero] at h
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply, hLR]
    ring
  have hLtop : Tendsto (fun n ↦ (Lf n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n ↦ ?_) (tendsto_natLog_atTop.comp hK)
    rw [Function.comp_apply, hLR]
    have := (Nat.log 2 (K n)).cast_nonneg (α := ℝ)
    linarith
  have hL1 : Tendsto (fun n ↦ ((Lf n : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hLtop
  have hK1 : Tendsto (fun n ↦ ((K n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hK)
  -- the blocks are small
  have hM : Tendsto (fun n ↦ ((pf n : ℕ) : ℝ) * B / √Var[X n; μ]) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto 0).comp hL6).const_mul (B / √κ)
    rw [Real.sqrt_zero, mul_zero] at h
    refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ h
    filter_upwards [hvar, hKev] with n hn hk
    have hk0 : (0 : ℝ) < K n := by exact_mod_cast hk
    have hsq : √(κ * K n) ≤ √Var[X n; μ] := Real.sqrt_le_sqrt hn
    have hs0 : 0 < √(κ * K n) := Real.sqrt_pos.2 (by positivity)
    have hL0 : (0 : ℝ) ≤ Lf n := by linarith [hL1le n]
    calc ((pf n : ℕ) : ℝ) * B / √Var[X n; μ] ≤ ((pf n : ℕ) : ℝ) * B / √(κ * K n) :=
          div_le_div_of_nonneg_left (by positivity) hs0 hsq
      _ = B / √κ * √((Lf n : ℝ) ^ 6 / K n) := by
          rw [Real.sqrt_div' _ hk0.le, Real.sqrt_mul hκ.le,
            show (Lf n : ℝ) ^ 6 = ((Lf n : ℝ) ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
          simp only [hpf]
          push_cast
          field_simp
  -- the discarded part is negligible
  have hDlim : Tendsto (fun n ↦ (2 * B ^ 2 * (((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 6 / K n) +
      2 * C * ((K n : ℝ))⁻¹) / κ) atTop (𝓝 0) := by
    have h := (((hL1.add hL6).const_mul (2 * B ^ 2)).add (hK1.const_mul (2 * C))).div_const κ
    rwa [add_zero, mul_zero, mul_zero, add_zero, zero_div] at h
  have hD : Tendsto (fun n ↦ Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] /
      Var[X n; μ]) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n ↦
      div_nonneg (variance_nonneg _ _) (variance_nonneg _ _)) ?_ hDlim
    filter_upwards [hvar, hKev] with n hn hk
    have hk0 : (0 : ℝ) < K n := by exact_mod_cast hk
    have hL0 : (0 : ℝ) < Lf n := by linarith [hL1le n]
    have hJle : (J n : ℝ) ≤ K n / (Lf n : ℝ) ^ 3 + 1 := by
      have h := Nat.cast_div_le (m := K n) (n := pf n) (α := ℝ)
      simp only [hJ, hpf] at h ⊢
      push_cast at h ⊢
      linarith
    have hJL : (J n : ℝ) * (Lf n : ℝ) ^ 2 / K n ≤ ((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 6 / K n := by
      have h1 : (J n : ℝ) * (Lf n : ℝ) ^ 2 / K n ≤
          (K n / (Lf n : ℝ) ^ 3 + 1) * (Lf n : ℝ) ^ 2 / K n := by gcongr
      have h2 : (K n / (Lf n : ℝ) ^ 3 + 1) * (Lf n : ℝ) ^ 2 / K n =
          ((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 2 / K n := by
        field_simp
      have h3 : (Lf n : ℝ) ^ 2 ≤ (Lf n : ℝ) ^ 6 := pow_le_pow_right₀ (hL1le n) (by norm_num)
      have h4 : (Lf n : ℝ) ^ 2 / K n ≤ (Lf n : ℝ) ^ 6 / K n :=
        div_le_div_of_nonneg_right h3 hk0.le
      linarith
    calc Var[fun ω ↦ X n ω - ∑ b ∈ range (J n), U n b ω; μ] / Var[X n; μ]
        ≤ (2 * (J n * (Lf n * B) ^ 2) + 2 * C) / (κ * K n) :=
          div_le_div₀ (by positivity) (hDvar n) (by positivity) hn
      _ = (2 * B ^ 2 * ((J n : ℝ) * (Lf n : ℝ) ^ 2 / K n) + 2 * C * ((K n : ℝ))⁻¹) / κ := by
          field_simp
      _ ≤ (2 * B ^ 2 * (((Lf n : ℝ))⁻¹ + (Lf n : ℝ) ^ 6 / K n) + 2 * C * ((K n : ℝ))⁻¹) /
          κ := by gcongr
  exact tendstoInDistribution_of_blocks (M := fun n ↦ ((pf n : ℕ) : ℝ) * B) hX2 hUm hUb hind
    (fun n b b' hbb' ↦ by
      rcases lt_or_gt_of_ne hbb' with h | h
      · exact hpairU n b b' h
      · exact (hpairU n b' b h).symm) hpos hM hD hZ

end RQMCMarkov.ScrambledStacks
