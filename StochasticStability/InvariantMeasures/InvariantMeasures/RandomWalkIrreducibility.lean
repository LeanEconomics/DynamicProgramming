/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvariantMeasures.Accessibility
import InvariantMeasures.ModelLinearModels
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Cardinality

/-!
# ψ-irreducibility for random walk and scalar autoregressions (MT §4.3, §4.4.1)

Meyn and Tweedie, §4.3, pp. 87–89, and §4.4.1, pp. 89–90.

**General tools.**
* `exists_pow_pos_of_reach`: if `P(x, S) > 0` and every `y ∈ S` reaches `C`, so does `x`.
* `not_isPhiIrreducible_of_disjoint_absorbing`: a chain with two disjoint non-empty absorbing sets
  is `φ`-irreducible for no nonzero `φ` (Proposition 4.2.3 (i)).
* `isPhiIrreducible_of_skeleton`: irreducibility of a skeleton `Pᵐ`, `m ≥ 1`, passes to `P`.

**Random walk on a half line** (§4.3.1), `halfLineWalkKernel Γ` on `[0, ∞)`.
* `halfLine_pow_zero_ge`: if `Γ(−∞, −ε) ≥ δ`, then `Pⁿ⁺¹(x, {0}) ≥ δⁿ⁺¹` once `x < (n + 1)ε`.
* **Proposition 4.3.1** (`proposition_4_3_1`, p. 87): the walk is `δ₀`-irreducible iff
  `Γ(−∞, 0) > 0` (4.12), and then `C ⇝ {0}` for every compact `C`
  (`proposition_4_3_1_compact`).
* `halfLine_maximal` (p. 87): `ψ(A) = Σₙ Pⁿ(0, A) 2⁻ⁿ` is a maximal irreducibility measure.

**Unrestricted random walk** (§4.3.3) **and scalar AR(1)** (§4.4.1).
* `isPhiIrreducible_of_local_density`: a kernel with
  `Q(x, A) ≥ δ μ_Leb({w ∈ (−β, β) : αx + w ∈ A})`, `|α| ≤ 1`, is irreducible for Lebesgue
  measure on `(−β, β)`.
* `ar1_isPhiIrreducible_of_density`, `randomWalk_isPhiIrreducible_of_density` (p. 88–89): an
  increment law with a density `γ ≥ δ > 0` on `(−β, β)` makes AR(1) with `|α| ≤ 1`, and random
  walk, `μ_Leb`-irreducible on `(−β, β)`; `randomWalk_isPhiIrreducible_Icc`: in particular
  `μ_Leb` restricted to `C = [−β/2, β/2]` is an irreducibility measure, and
  `randomWalk_step_ge` (p. 89): `P(x, B) ≥ δ μ_Leb(B)` for `x ∈ C`, `B ⊆ C`.
* `randomWalk_isPhiIrreducible_of_convPow`: the same when only a convolution power `Γ^{m∗}` has
  such a density (a spread-out increment, (RW2)).
* `randomWalk_rational` (p. 89): increments concentrated on `ℚ` make every `x + ℚ` absorbing,
  uncountably many of them, and the walk is irreducible for no nonzero measure.
* `ar1_uniform_isPhiIrreducible` (p. 89): AR(1) with uniform noise on `[−1, 1]` and `|α| ≤ 1` is
  `μ_Leb`-irreducible on `[−1, 1]`; `ar1_abs_lt_step` and `ar1_explosive_not_irreducible`: if
  `|α| > 1` and the noise lies in `[−1, 1]`, `|Xₙ|` increases once it exceeds `(|α| − 1)⁻¹`,
  and the chain is irreducible for no nonzero measure.

**Corrections.** None. The storage-model discussion of §4.3.2 is the case of Proposition 4.3.1
with increment law the law of `Sₙ − Jₙ` (the reduction is in the `MarkovModels` project); the
content-dependent release discussion is informal and is not formalised. The AR(k) explosion and
stability heuristics of p. 90 (roots of `A(z)`) are not formalised; they are the subject of the
linear-model results of §4.4.3 and Chapter 7.
-/

namespace MeynTweedie.InvariantMeasures

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

/-! ### General tools -/

/-- If `P(x, S) > 0` and every `y ∈ S` reaches `C` (`Pⁿ(y, C) > 0` for some `n`), then `x`
reaches `C` in at least one step. -/
theorem exists_pow_pos_of_reach {X : Type*} [MeasurableSpace X] (P : Kernel X X) {C S : Set X}
    (hC : MeasurableSet C) {x : X} (hpos : 0 < P x S)
    (hreach : ∀ y ∈ S, ∃ n, 0 < (P ^ n) y C) : ∃ n, 0 < (P ^ (n + 1)) x C := by
  have hsub : S ⊆ ⋃ n, {y | 0 < (P ^ n) y C} := fun y hy => mem_iUnion.2 (hreach y hy)
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion (hpos.trans_le (measure_mono hsub))
  refine ⟨n, ?_⟩
  rw [add_comm]
  exact (pow_add_pos_iff P 1 n x hC).2 (by rwa [pow_one])

/-- A chain with two disjoint non-empty absorbing sets is `φ`-irreducible for no nonzero `φ`: by
Proposition 4.2.3 (i) both sets would be full. -/
theorem not_isPhiIrreducible_of_disjoint_absorbing {X : Type*} [MeasurableSpace X]
    {P : Kernel X X} [IsMarkovKernel P] {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : Disjoint A B)
    (hAabs : IsAbsorbing P A) (hBabs : IsAbsorbing P B) {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) : φ = 0 := by
  have h1 := proposition_4_2_3_i hφ hA hAne hAabs
  have h2 := proposition_4_2_3_i hφ hB hBne hBabs
  rw [← Measure.measure_univ_eq_zero]
  have : (univ : Set X) = Aᶜ ∪ Bᶜ := by
    rw [← compl_inter, hAB.inter_eq, compl_empty]
  rw [this]
  exact measure_union_null h1 h2

/-- Irreducibility of a skeleton `Pᵐ`, `m ≥ 1`, gives irreducibility of `P` (for the same
measure). -/
theorem isPhiIrreducible_of_skeleton {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] {m : ℕ} (hm : 1 ≤ m) [IsMarkovKernel (P ^ m)] {φ : Measure X}
    (h : IsPhiIrreducible (P ^ m) φ) : IsPhiIrreducible P φ := by
  intro A hA hpos x
  obtain ⟨n, hn⟩ := (hitProb_pos_iff (P ^ m) hA x).1 (h A hA hpos x)
  refine (hitProb_pos_iff P hA x).2 ⟨m * (n + 1) - 1, ?_⟩
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity)), pow_mul]
  exact hn

/-! ### Random walk on a half line (§4.3.1) -/

/-- MT p. 87: if `Γ(−∞, −ε) ≥ δ`, then `Pⁿ⁺¹(x, {0}) ≥ δⁿ⁺¹` whenever `x < (n + 1)ε`. -/
theorem halfLine_pow_zero_ge (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {ε : ℝ} (hε : 0 < ε)
    {δ : ℝ≥0∞} (hδ : δ ≤ Γ (Iio (-ε))) (n : ℕ) (x : ℝ≥0) (hx : (x : ℝ) < (n + 1) * ε) :
    δ ^ (n + 1) ≤ (halfLineWalkKernel Γ ^ (n + 1)) x {0} := by
  have := isMarkovKernel_halfLineWalkKernel Γ
  induction n generalizing x with
  | zero =>
    rw [zero_add, pow_one, pow_one, halfLineWalkKernel_apply_zero]
    refine hδ.trans (measure_mono fun w hw => ?_)
    simp only [mem_Iio, mem_Iic] at hw ⊢
    simp at hx
    linarith
  | succ n ih =>
    set S : Set ℝ≥0 := {y | (y : ℝ) < (n + 1) * ε}
    have hS : MeasurableSet S := measurableSet_lt measurable_coe_nnreal_real measurable_const
    have hPS : δ ≤ halfLineWalkKernel Γ x S := by
      rw [halfLineWalkKernel_apply' Γ x hS]
      refine hδ.trans (measure_mono fun w hw => ?_)
      simp only [mem_Iio, mem_ofPred_eq, S, Real.coe_toNNReal'] at hw ⊢
      push_cast at hx
      refine max_lt (by linarith) (by positivity)
    rw [pow_succ_apply _ (n + 1) x (measurableSet_singleton 0), pow_succ]
    calc δ ^ (n + 1) * δ ≤ δ ^ (n + 1) * halfLineWalkKernel Γ x S := by gcongr
      _ = ∫⁻ _ in S, δ ^ (n + 1) ∂halfLineWalkKernel Γ x := by rw [setLIntegral_const]
      _ ≤ ∫⁻ y in S, (halfLineWalkKernel Γ ^ (n + 1)) y {0} ∂halfLineWalkKernel Γ x :=
          setLIntegral_mono (Kernel.measurable_coe _ (measurableSet_singleton 0))
            fun y hy => ih y hy
      _ ≤ _ := setLIntegral_le_lintegral _ _

/-- If `Γ(−∞, 0) > 0` then `Γ(−∞, −ε) > 0` for some `ε > 0`. -/
theorem exists_Iio_neg_pos (Γ : Measure ℝ) (h : 0 < Γ (Iio 0)) :
    ∃ ε : ℝ, 0 < ε ∧ 0 < Γ (Iio (-ε)) := by
  have hU : Iio (0 : ℝ) = ⋃ k : ℕ, Iio (-(1 / ((k : ℝ) + 1))) := by
    ext w
    simp only [mem_Iio, mem_iUnion]
    constructor
    · intro hw
      obtain ⟨k, hk⟩ := exists_nat_gt (-1 / w)
      refine ⟨k, ?_⟩
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      rw [div_lt_iff_of_neg hw] at hk
      have : 1 / ((k : ℝ) + 1) < -w := by rw [div_lt_iff₀ hk1]; nlinarith
      linarith
    · rintro ⟨k, hk⟩
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hU] at h
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion h
  exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩

/-- If `Γ(−∞, 0) = 0`, a reflected walk started at `x > 0` never reaches `{0}`: the set
`[x, ∞)` is absorbing. -/
theorem halfLine_hitProb_zero_eq_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    [IsMarkovKernel (halfLineWalkKernel Γ)] (h : Γ (Iio 0) = 0) {x : ℝ≥0} (hx : 0 < x) :
    hitProb (halfLineWalkKernel Γ) {0} x = 0 := by
  have hAbs : IsAbsorbing (halfLineWalkKernel Γ) (Ici x) := by
    intro y hy
    rw [← prob_compl_eq_zero_iff measurableSet_Ici, compl_Ici,
      halfLineWalkKernel_apply' Γ y measurableSet_Iio]
    refine measure_mono_null (fun w hw => ?_) h
    simp only [mem_Ici, mem_ofPred_eq, mem_Iio] at hy hw ⊢
    by_contra hw0
    push Not at hw0
    have : (x : ℝ) ≤ (Real.toNNReal ((y : ℝ) + w) : ℝ) := by
      rw [Real.coe_toNNReal']
      exact le_max_of_le_left (by have : (x : ℝ) ≤ y := hy; linarith)
    exact absurd hw (not_lt.2 (by exact_mod_cast this))
  exact hAbs.hitProb_eq_zero measurableSet_Ici
    (Set.disjoint_left.2 fun y hy h0 => by
      rw [mem_singleton_iff.1 h0, mem_Ici] at hy
      exact absurd hy (not_le.2 hx)) (mem_Ici.2 le_rfl)

/-- **Proposition 4.3.1** (MT p. 87): random walk on a half line is `φ`-irreducible with
`φ = δ₀` (`φ(0, ∞) = 0`, `φ{0} = 1`) iff `Γ(−∞, 0) > 0` (4.12). -/
theorem proposition_4_3_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] :
    ∃ _ : IsMarkovKernel (halfLineWalkKernel Γ),
      (IsPhiIrreducible (halfLineWalkKernel Γ) (Measure.dirac 0) ↔ 0 < Γ (Iio 0)) := by
  have hM := isMarkovKernel_halfLineWalkKernel Γ
  refine ⟨hM, ?_⟩
  rw [isPhiIrreducible_dirac_iff]
  constructor
  · intro h
    by_contra h0
    have h0' : Γ (Iio 0) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
    have := h 1
    rw [halfLine_hitProb_zero_eq_zero Γ h0' one_pos] at this
    exact lt_irrefl _ this
  · intro h x
    obtain ⟨ε, hε, hΓε⟩ := exists_Iio_neg_pos Γ h
    obtain ⟨n, hn⟩ := exists_nat_gt ((x : ℝ) / ε)
    refine (hitProb_pos_iff _ (measurableSet_singleton 0) x).2 ⟨n, ?_⟩
    refine (ENNReal.pow_pos hΓε _).trans_le (halfLine_pow_zero_ge Γ hε le_rfl n x ?_)
    rw [div_lt_iff₀ hε] at hn
    nlinarith

/-- **Proposition 4.3.1**, second part (MT p. 87): if `Γ(−∞, 0) > 0`, then `C ⇝ {0}` for every
compact `C`. -/
theorem proposition_4_3_1_compact (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (h : 0 < Γ (Iio 0)) {C : Set ℝ≥0} (hC : IsCompact C) :
    ∃ _ : IsMarkovKernel (halfLineWalkKernel Γ), UnifAccessible (halfLineWalkKernel Γ) C {0} := by
  have hM := isMarkovKernel_halfLineWalkKernel Γ
  refine ⟨hM, ?_⟩
  obtain ⟨ε, hε, hΓε⟩ := exists_Iio_neg_pos Γ h
  obtain ⟨c, hc⟩ := hC.bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt ((c : ℝ) / ε)
  refine ⟨Γ (Iio (-ε)) ^ (n + 1), ENNReal.pow_pos hΓε _, fun x hx => ?_⟩
  refine (halfLine_pow_zero_ge Γ hε le_rfl n x ?_).trans
    (pow_le_hitProb _ (measurableSet_singleton 0) n x)
  have hxc : (x : ℝ) ≤ c := by exact_mod_cast hc hx
  rw [div_lt_iff₀ hε] at hn
  nlinarith

/-- MT p. 87: if `Γ(−∞, 0) > 0`, the measure `ψ(A) = Σₙ Pⁿ(0, A) 2⁻ⁿ`, i.e. `2 K_{a_{1/2}}(0, ·)`,
is a maximal irreducibility measure for random walk on a half line. -/
theorem halfLine_maximal (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : 0 < Γ (Iio 0)) :
    ∃ _ : IsMarkovKernel (halfLineWalkKernel Γ),
      IsMaximalIrreducibility (halfLineWalkKernel Γ)
        ((2 : ℝ≥0∞) • resolventHalf (halfLineWalkKernel Γ) 0) ∧
      ∀ A, MeasurableSet A → ((2 : ℝ≥0∞) • resolventHalf (halfLineWalkKernel Γ) 0) A =
        ∑' n, (halfLineWalkKernel Γ ^ n) 0 A * 2⁻¹ ^ n := by
  obtain ⟨hM, hirr⟩ := proposition_4_3_1 Γ
  refine ⟨hM, ?_, fun A hA => ?_⟩
  · have hmax := isMaximalIrreducibility_maxIrrMeasure _ (hirr.2 h) (Measure.dirac_ne_zero)
    rw [maxIrrMeasure, dirac_kernel] at hmax
    exact hmax.of_equiv (Measure.absolutelyContinuous_smul two_ne_zero)
      Measure.smul_absolutelyContinuous
  · rw [Measure.smul_apply, resolventHalf_apply _ 0 hA, smul_eq_mul, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun n => ?_
    have h2 : (2 : ℝ≥0∞) * 2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc 2 * ((halfLineWalkKernel Γ ^ n) 0 A * 2⁻¹ ^ (n + 1))
        = (halfLineWalkKernel Γ ^ n) 0 A * 2⁻¹ ^ n * (2 * 2⁻¹) := by ring
      _ = _ := by rw [h2, mul_one]

/-! ### Kernels with a local density (§4.3.3, §4.4.1) -/

/-- **Irreducibility from a local density** (MT pp. 88–89). Let `Q` be a transition kernel on
`ℝ` with `Q(x, A) ≥ δ μ_Leb{w ∈ (−β, β) : αx + w ∈ A}` for all `x` and `A`, where `|α| ≤ 1`,
`β > 0`, `δ > 0`. Then `Q` is irreducible for Lebesgue measure on `(−β, β)`. This covers the
unrestricted random walk (`α = 1`) and the scalar AR(1) model with `|α| ≤ 1`. -/
theorem isPhiIrreducible_of_local_density (Q : Kernel ℝ ℝ) [IsMarkovKernel Q] {α β : ℝ}
    {δ : ℝ≥0∞} (hα : |α| ≤ 1) (hβ : 0 < β) (hδ : δ ≠ 0)
    (hQ : ∀ x A, MeasurableSet A → δ * volume ({w | α * x + w ∈ A} ∩ Ioo (-β) β) ≤ Q x A) :
    IsPhiIrreducible Q (volume.restrict (Ioo (-β) β)) := by
  have hax : ∀ x : ℝ, |α * x| ≤ |x| := fun x => by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hα
  set C : Set ℝ := Ioo (-(β / 2)) (β / 2) with hCdef
  have hCm : MeasurableSet C := measurableSet_Ioo
  -- one step from a point with `|αx| < β/2` lands in `C`
  have hstepC : ∀ x : ℝ, |α * x| < β / 2 → 0 < Q x C := fun x hx => by
    rw [abs_lt] at hx
    refine lt_of_lt_of_le ?_ (hQ x C hCm)
    refine ENNReal.mul_pos hδ (ne_of_gt ?_)
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (-(β / 2) - α * x) (β / 2 - α * x))
      fun w hw => ?_)
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by linarith)
    · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, hCdef] at hw ⊢
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  -- every state reaches `C`
  have hreachk : ∀ k : ℕ, ∀ x : ℝ, |x| < (k + 1) * (β / 2) → ∃ n, 0 < (Q ^ n) x C := by
    intro k
    induction k with
    | zero =>
      intro x hx
      refine ⟨0, ?_⟩
      rw [pow_zero_apply, Measure.dirac_apply_of_mem]
      · exact one_pos
      · simp only [CharP.cast_eq_zero, zero_add, one_mul] at hx
        exact abs_lt.1 hx
    | succ k ih =>
      intro x hx
      by_cases h1 : |α * x| < β / 2
      · exact ⟨1, by rw [pow_one]; exact hstepC x h1⟩
      · push Not at h1
        set S : Set ℝ := {y | |y| < (k + 1) * (β / 2)}
        have hS : MeasurableSet S := measurableSet_lt continuous_abs.measurable measurable_const
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hxle := hax x
        push_cast at hx
        have hpos : 0 < Q x S := by
          refine lt_of_lt_of_le ?_ (hQ x S hS)
          refine ENNReal.mul_pos hδ (ne_of_gt ?_)
          rcases le_abs'.1 h1 with h2 | h2
          · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (β / 2) β) fun w hw => ?_)
            · rw [Real.volume_Ioo]
              exact ENNReal.ofReal_pos.2 (by linarith)
            · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, S] at hw ⊢
              have := neg_abs_le (α * x)
              have := neg_abs_le x
              refine ⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, by linarith, hw.2⟩
          · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (-β) (-(β / 2))) fun w hw => ?_)
            · rw [Real.volume_Ioo]
              exact ENNReal.ofReal_pos.2 (by linarith)
            · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, S] at hw ⊢
              have := le_abs_self (α * x)
              have := le_abs_self x
              refine ⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, hw.1, by linarith⟩
        obtain ⟨n, hn⟩ := exists_pow_pos_of_reach Q hCm hpos fun y hy => ih y hy
        exact ⟨n + 1, hn⟩
  have hreach : ∀ x : ℝ, ∃ n, 0 < (Q ^ n) x C := fun x => by
    obtain ⟨k, hk⟩ := exists_nat_gt (|x| / (β / 2))
    refine hreachk k x ?_
    rw [div_lt_iff₀ (by linarith)] at hk
    nlinarith
  -- irreducibility
  intro A hA hpos x
  rw [Measure.restrict_apply hA] at hpos
  have hsub : A ∩ Ioo (-β) β ⊆
      ⋃ k : ℕ, A ∩ Ioo (-β + β / ((k : ℝ) + 2)) (β - β / ((k : ℝ) + 2)) := by
    rintro w ⟨hwA, hw⟩
    rw [mem_Ioo] at hw
    have hd : 0 < β - |w| := by rw [sub_pos, abs_lt]; exact ⟨by linarith, hw.2⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (β / (β - |w|))
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : β / ((k : ℝ) + 2) < β - |w| := by
      rw [div_lt_iff₀ hk2]
      rw [div_lt_iff₀ hd] at hk
      nlinarith
    refine mem_iUnion.2 ⟨k, hwA, ?_, ?_⟩ <;>
      [linarith [neg_abs_le w]; linarith [le_abs_self w]]
  obtain ⟨k, hk⟩ := exists_measure_pos_of_iUnion (hpos.trans_le (measure_mono hsub))
  set η : ℝ := β / ((k : ℝ) + 2) with hηdef
  have hk2 : (2 : ℝ) ≤ (k : ℝ) + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hη : 0 < η := by positivity
  have hη2 : η ≤ β / 2 := div_le_div_of_nonneg_left hβ.le two_pos hk2
  set A' := A ∩ Ioo (-β + η) (β - η)
  set B : Set ℝ := Ioo (-η) η
  have hBm : MeasurableSet B := measurableSet_Ioo
  -- from `B` the set `A` is reached in one step
  have hBA : B ⊆ {y | 0 < (Q ^ 1) y A} := fun y hy => by
    rw [mem_ofPred_eq, pow_one]
    have hy' : |α * y| < η := (hax y).trans_lt (abs_lt.2 hy)
    rw [abs_lt] at hy'
    refine lt_of_lt_of_le ?_ (hQ y A hA)
    refine ENNReal.mul_pos hδ (ne_of_gt (hk.trans_le ?_))
    calc volume A' = volume ((fun w => α * y + w) ⁻¹' A') := (measure_preimage_add _ _ _).symm
      _ ≤ _ := measure_mono fun w hw => by
        simp only [mem_preimage, mem_inter_iff, mem_Ioo, A'] at hw
        exact ⟨hw.1, by linarith, by linarith⟩
  -- from `C` the set `B` is reached in one step
  have hCB : C ⊆ {y | 0 < (Q ^ 1) y B} := fun y hy => by
    rw [mem_ofPred_eq, pow_one]
    have hy' : |α * y| < β / 2 := (hax y).trans_lt (abs_lt.2 hy)
    rw [abs_lt] at hy'
    refine lt_of_lt_of_le ?_ (hQ y B hBm)
    refine ENNReal.mul_pos hδ (ne_of_gt ?_)
    refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (-η - α * y) (η - α * y)) fun w hw => ?_)
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by linarith)
    · simp only [mem_Ioo, mem_inter_iff, mem_ofPred_eq, B] at hw ⊢
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨n, hn⟩ := hreach x
  have h1 : 0 < (Q ^ (n + 1)) x B :=
    (pow_add_pos_iff Q n 1 x hBm).2 (hn.trans_le (measure_mono hCB))
  have h2 : 0 < (Q ^ (n + 1 + 1)) x A :=
    (pow_add_pos_iff Q (n + 1) 1 x hA).2 (h1.trans_le (measure_mono hBA))
  exact (hitProb_pos_iff Q hA x).2 ⟨n + 1, h2⟩

/-- A density `γ ≥ δ` on `(−β, β)` below the law `Γ` gives `Γ(A) ≥ δ μ_Leb(A ∩ (−β, β))`. -/
theorem le_of_density {Γ : Measure ℝ} {γ : ℝ → ℝ≥0∞} {β : ℝ} {δ : ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x)
    {A : Set ℝ} (hA : MeasurableSet A) : δ * volume (A ∩ Ioo (-β) β) ≤ Γ A := by
  calc δ * volume (A ∩ Ioo (-β) β) = ∫⁻ _ in A ∩ Ioo (-β) β, δ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in A ∩ Ioo (-β) β, γ x :=
        setLIntegral_mono' (hA.inter measurableSet_Ioo) fun x hx => hγδ x hx.2
    _ ≤ ∫⁻ x in A, γ x := lintegral_mono_set inter_subset_left
    _ ≤ Γ A := hγ A hA

/-- MT §4.4.1, p. 89: the AR(1) model `Xₙ₊₁ = αXₙ + Wₙ₊₁` with `|α| ≤ 1` and an innovation law
with a density `γ ≥ δ > 0` on `(−β, β)` is irreducible for Lebesgue measure on `(−β, β)`. -/
theorem ar1_isPhiIrreducible_of_density (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α β : ℝ}
    {δ : ℝ≥0∞} (hα : |α| ≤ 1) (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (ar1Kernel Γ α),
      IsPhiIrreducible (ar1Kernel Γ α) (volume.restrict (Ioo (-β) β)) := by
  have hM := isMarkovKernel_ar1Kernel Γ α
  refine ⟨hM, isPhiIrreducible_of_local_density _ hα hβ hδ fun x A hA => ?_⟩
  rw [ar1Kernel_apply' Γ α x hA]
  exact le_of_density hγ hγδ ((measurable_const_add (α * x)) hA)

/-- MT §4.3.3, pp. 88–89: random walk on `ℝ` whose increment law has a density `γ ≥ δ > 0` on
`(−β, β)` is irreducible for Lebesgue measure on `(−β, β)`. -/
theorem randomWalk_isPhiIrreducible_of_density (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ}
    {δ : ℝ≥0∞} (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      IsPhiIrreducible (randomWalkKernel Γ) (volume.restrict (Ioo (-β) β)) := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  refine ⟨hM, isPhiIrreducible_of_local_density _ (α := 1) (by simp) hβ hδ fun x A hA => ?_⟩
  rw [randomWalkKernel_apply' Γ x hA]
  simp only [one_mul]
  exact le_of_density hγ hγδ ((measurable_const_add x) hA)

/-- MT p. 89: in particular Lebesgue measure restricted to `C = [−β/2, β/2]` is an irreducibility
measure for the random walk. -/
theorem randomWalk_isPhiIrreducible_Icc (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ}
    {δ : ℝ≥0∞} (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A) (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      IsPhiIrreducible (randomWalkKernel Γ) (volume.restrict (Icc (-(β / 2)) (β / 2))) := by
  obtain ⟨hM, h⟩ := randomWalk_isPhiIrreducible_of_density Γ hβ hδ hγ hγδ
  refine ⟨hM, h.mono (Measure.absolutelyContinuous_of_le (Measure.restrict_mono ?_ le_rfl))⟩
  intro w hw
  rw [mem_Icc] at hw
  rw [mem_Ioo]
  constructor <;> linarith

/-- MT p. 89: for `x ∈ C = [−β/2, β/2]` and `B ⊆ C`, `P(x, B) ≥ δ μ_Leb(B)`. -/
theorem randomWalk_step_ge (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {β : ℝ} {δ : ℝ≥0∞}
    {γ : ℝ → ℝ≥0∞} (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ Γ A)
    (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) {x : ℝ} (hx : x ∈ Icc (-(β / 2)) (β / 2)) {B : Set ℝ}
    (hB : MeasurableSet B) (hBC : B ⊆ Icc (-(β / 2)) (β / 2)) :
    δ * volume B ≤ randomWalkKernel Γ x B := by
  rw [randomWalkKernel_apply' Γ x hB]
  refine le_trans (mul_le_mul_right ?_ δ) (le_of_density hγ hγδ ((measurable_const_add x) hB))
  rw [mem_Icc] at hx
  calc volume B = volume ((fun w => x + w) ⁻¹' B) := (measure_preimage_add _ _ _).symm
    _ ≤ volume ({w | x + w ∈ B} ∩ Ioo (-β) β ∪ {-β, β}) := measure_mono fun w hw => by
        have hb : x + w ∈ Icc (-(β / 2)) (β / 2) := hBC hw
        rw [mem_Icc] at hb
        by_cases h1 : w = -β
        · exact Or.inr (Or.inl h1)
        by_cases h2 : w = β
        · exact Or.inr (Or.inr h2)
        refine Or.inl ⟨hw, ?_, ?_⟩
        · exact lt_of_le_of_ne (by linarith) (Ne.symm h1)
        · exact lt_of_le_of_ne (by linarith) h2
    _ ≤ volume ({w | x + w ∈ B} ∩ Ioo (-β) β) + volume ({-β, β} : Set ℝ) := measure_union_le _ _
    _ = volume ({w | x + w ∈ B} ∩ Ioo (-β) β) := by
        rw [(Set.toFinite _ : ({-β, β} : Set ℝ).Finite).measure_zero, add_zero]

/-- A spread-out increment (MT (RW2), §4.3.3): if some convolution power `Γ^{m∗}`, `m ≥ 1`, has a
density `γ ≥ δ > 0` on `(−β, β)`, the random walk is irreducible for Lebesgue measure on
`(−β, β)`. -/
theorem randomWalk_isPhiIrreducible_of_convPow (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {m : ℕ}
    (hm : 1 ≤ m) {β : ℝ} {δ : ℝ≥0∞} (hβ : 0 < β) (hδ : δ ≠ 0) {γ : ℝ → ℝ≥0∞}
    (hγ : ∀ A, MeasurableSet A → ∫⁻ x in A, γ x ≤ convPow Γ m A)
    (hγδ : ∀ x ∈ Ioo (-β) β, δ ≤ γ x) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      IsPhiIrreducible (randomWalkKernel Γ) (volume.restrict (Ioo (-β) β)) := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  have hMm := isMarkovKernel_pow (randomWalkKernel Γ) m
  refine ⟨hM, isPhiIrreducible_of_skeleton _ hm ?_⟩
  refine isPhiIrreducible_of_local_density _ (α := 1) (by simp) hβ hδ fun x A hA => ?_
  rw [randomWalkKernel_pow_apply Γ m x, Measure.map_apply (measurable_const_add x) hA]
  simp only [one_mul]
  exact le_of_density hγ hγδ ((measurable_const_add x) hA)

/-- The set `x + ℚ`. -/
def ratCoset (x : ℝ) : Set ℝ := range fun q : ℚ => x + (q : ℝ)

/-- MT p. 89: if the increment law is concentrated on `ℚ`, every `x + ℚ` is absorbing, there are
uncountably many such sets, and the walk is irreducible for no nonzero measure. If moreover
`Γ{q} > 0` for every rational `q`, each `x + ℚ` is an absorbing irreducible set: every point of
it is reached in one step from every other. -/
theorem randomWalk_rational (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ : Γ (range (Rat.cast : ℚ → ℝ))ᶜ = 0) :
    ∃ _ : IsMarkovKernel (randomWalkKernel Γ),
      (∀ x, IsAbsorbing (randomWalkKernel Γ) (ratCoset x)) ∧
      ¬ (range ratCoset).Countable ∧
      (∀ φ : Measure ℝ, IsPhiIrreducible (randomWalkKernel Γ) φ → φ = 0) ∧
      ((∀ q : ℚ, Γ {(q : ℝ)} ≠ 0) →
        ∀ x, ∀ y ∈ ratCoset x, ∀ z ∈ ratCoset x, 0 < randomWalkKernel Γ y {z}) := by
  have hM := isMarkovKernel_randomWalkKernel Γ
  have hmeas : ∀ x, MeasurableSet (ratCoset x) := fun x => (countable_range _).measurableSet
  have hAbs : ∀ x, IsAbsorbing (randomWalkKernel Γ) (ratCoset x) := by
    rintro x y ⟨q, rfl⟩
    rw [← prob_compl_eq_zero_iff (hmeas x), randomWalkKernel_apply' Γ _ (hmeas x).compl]
    refine measure_mono_null (fun w hw => ?_) hΓ
    rintro ⟨r, rfl⟩
    exact hw ⟨q + r, by push_cast; ring⟩
  refine ⟨hM, hAbs, ?_, fun φ hφ => ?_, fun hpos x y hy z hz => ?_⟩
  · intro hc
    apply Cardinal.not_countable_real
    have : (univ : Set ℝ) = ⋃₀ range ratCoset :=
      (eq_univ_of_forall fun x =>
        mem_sUnion.2 ⟨ratCoset x, mem_range_self x, (0 : ℚ), by simp⟩).symm
    rw [this]
    exact hc.sUnion fun s ⟨x, hx⟩ => hx ▸ countable_range _
  · refine not_isPhiIrreducible_of_disjoint_absorbing (hmeas 0) (hmeas √2)
      (show (ratCoset 0).Nonempty from ⟨0, (0 : ℚ), by simp⟩)
      (show (ratCoset √2).Nonempty from ⟨√2, (0 : ℚ), by simp⟩) ?_ (hAbs 0) (hAbs √2) hφ
    refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
    obtain ⟨q, rfl⟩ := hy1
    obtain ⟨r, hr⟩ := hy2
    exact irrational_sqrt_two ⟨q - r, by push_cast; linarith⟩
  · obtain ⟨q, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    rw [randomWalkKernel_apply' Γ _ (measurableSet_singleton _), pos_iff_ne_zero]
    have : {w | x + (q : ℝ) + w ∈ ({x + (r : ℝ)} : Set ℝ)} = {((r - q : ℚ) : ℝ)} := by
      ext w
      simp only [mem_ofPred_eq, mem_singleton_iff]
      push_cast
      constructor <;> intro h <;> linarith
    rw [this]
    exact hpos _

/-- MT p. 89: the AR(1) model with innovations uniform on `[−1, 1]` and `|α| ≤ 1` is
`μ_Leb`-irreducible on `[−1, 1]`. -/
theorem ar1_uniform_isPhiIrreducible {α : ℝ} (hα : |α| ≤ 1) :
    ∃ _ : IsMarkovKernel (ar1Kernel ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)) α),
      IsPhiIrreducible (ar1Kernel ((2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)) α)
        (volume.restrict (Icc (-1) 1)) := by
  set Γ : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1 : ℝ) 1)
  have hΓ : IsProbabilityMeasure Γ := ⟨by
    simp only [Γ, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Icc, smul_eq_mul]
    norm_num
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top⟩
  have hM := isMarkovKernel_ar1Kernel Γ α
  refine ⟨hM, ?_⟩
  have hIoo : volume.restrict (Icc (-1 : ℝ) 1) = volume.restrict (Ioo (-1 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [hIoo]
  refine isPhiIrreducible_of_local_density _ (δ := (2 : ℝ≥0∞)⁻¹) hα one_pos (by simp)
    fun x A hA => ?_
  rw [ar1Kernel_apply' Γ α x hA]
  have hm : MeasurableSet {w | α * x + w ∈ A} := (measurable_const_add (α * x)) hA
  simp only [Γ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hm]
  gcongr
  exact Ioo_subset_Icc_self

/-- MT p. 89: if `|α| > 1` and the noise lies in `[−1, 1]`, then once `|x| > (|α| − 1)⁻¹` the next
state is larger in absolute value: the chain explodes monotonically. -/
theorem ar1_abs_lt_step {α x w : ℝ} (hα : 1 < |α|) (hx : (|α| - 1)⁻¹ < |x|) (hw : |w| ≤ 1) :
    |x| < |α * x + w| := by
  have h1 : 0 < |α| - 1 := by linarith
  have h2 : 1 < (|α| - 1) * |x| := by
    rwa [inv_lt_iff_one_lt_mul₀ h1, mul_comm] at hx
  calc |x| < |α| * |x| - 1 := by nlinarith
    _ ≤ |α * x| - |w| := by rw [abs_mul]; linarith
    _ ≤ |α * x + w| := by
        have := abs_add_le (α * x + w) (-w)
        rw [add_neg_cancel_right, abs_neg] at this
        linarith

/-- MT p. 89: if `|α| > 1` and the noise lies in `[−1, 1]`, the AR(1) chain is irreducible for no
nonzero measure: every set `{|x| ≥ c}`, `c > (|α| − 1)⁻¹`, is absorbing, so an irreducibility
measure charges no bounded set. -/
theorem ar1_explosive_not_irreducible (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {α : ℝ}
    (hα : 1 < |α|) (hΓ : Γ (Icc (-1) 1)ᶜ = 0) :
    ∃ _ : IsMarkovKernel (ar1Kernel Γ α),
      ∀ φ : Measure ℝ, IsPhiIrreducible (ar1Kernel Γ α) φ → φ = 0 := by
  have hM := isMarkovKernel_ar1Kernel Γ α
  refine ⟨hM, fun φ hφ => ?_⟩
  set c₀ : ℝ := (|α| - 1)⁻¹ + 1
  have hc₀ : (|α| - 1)⁻¹ < c₀ := by linarith
  have hAbs : ∀ k : ℕ, IsAbsorbing (ar1Kernel Γ α) {x | c₀ + k ≤ |x|} := by
    intro k y hy
    have hm : MeasurableSet {x : ℝ | c₀ + k ≤ |x|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    rw [← prob_compl_eq_zero_iff hm, ar1Kernel_apply' Γ α y hm.compl]
    refine measure_mono_null (fun w hw => ?_) hΓ
    intro hw1
    apply hw
    simp only [mem_ofPred_eq] at hy ⊢
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact hy.trans (ar1_abs_lt_step hα (by linarith) (abs_le.2 hw1)).le
  have hfull : ∀ k : ℕ, φ {x | c₀ + k ≤ |x|}ᶜ = 0 := fun k =>
    proposition_4_2_3_i hφ (measurableSet_le measurable_const continuous_abs.measurable)
      ⟨c₀ + k, by simp only [mem_ofPred_eq]; rw [abs_of_pos (by positivity)]⟩ (hAbs k)
  rw [← Measure.measure_univ_eq_zero]
  have : (univ : Set ℝ) = ⋃ k : ℕ, {x | c₀ + k ≤ |x|}ᶜ := by
    refine (eq_univ_of_forall fun x => ?_).symm
    obtain ⟨k, hk⟩ := exists_nat_gt |x|
    have : 0 < c₀ := by positivity
    exact mem_iUnion.2 ⟨k, by simp only [mem_compl_iff, mem_ofPred_eq, not_le]; linarith⟩
  rw [this]
  exact measure_iUnion_null hfull

end MeynTweedie.InvariantMeasures
