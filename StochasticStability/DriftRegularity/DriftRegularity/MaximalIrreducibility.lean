/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DriftRegularity.PsiIrreducibility

/-!
# Maximal irreducibility measures, full and absorbing sets (MT §4.0, §4.2.2)

Meyn and Tweedie, Theorem 4.0.1 (p. 75) and §4.2.2, pp. 82–85. `X` is an arbitrary measurable
space and the irreducibility measure `φ` an arbitrary nonzero measure: neither a countably
generated σ-algebra nor σ-finiteness of `φ` is needed.

* `exists_finite_equiv_of_ac`: a measure `φ ≪ μ`, `μ` finite, has an equivalent finite measure
  (`μ` restricted to the complement of a largest `φ`-null set); `exists_prob_equiv`: hence every
  nonzero irreducibility measure has an equivalent probability measure, the reduction "without
  loss of generality `φ(X) = 1`" of p. 83.
* `maxIrrMeasure P φ = ψ` (4.10): `ψ(A) = ∫ φ(dy) K_{a_{1/2}}(y, A)`;
  `isPhiIrreducible_maxIrrMeasure` (i), `ac_maxIrrMeasure` (ii), `maxIrrMeasure_hitSet_null`
  (iii), and
  `maxIrrMeasure_comp_pow_le`: the inequality `ψPᵐ ≤ 2ᵐ ψ` of the proof.
* `IsMaximalIrreducibility P ψ` (p. 84): `ψ ≠ 0` is an irreducibility measure and every
  irreducibility measure is absolutely continuous with respect to it.
* **Proposition 4.2.2** (`proposition_4_2_2`, p. 83): a nonzero irreducibility measure `φ` gives a
  probability measure `ψ` with (i)–(iv); `proposition_4_2_2_maximal`: `ψ` is maximal.
* **Theorem 4.0.1** (`theorem_4_0_1`, p. 75) and `theorem_4_0_1_unique`: existence and
  essential uniqueness of the maximal irreducibility measure.
* `posSets ψ = B⁺(X)` and `posSets_eq_of_maximal`: `B⁺(X)` does not depend on the choice of `ψ`
  (p. 84); `IsFull ψ A` (p. 84).
* **Proposition 4.2.3** (p. 84): (i) `proposition_4_2_3_i`, every non-empty absorbing set is full;
  (ii) `proposition_4_2_3_ii`, every full set contains a non-empty absorbing (and full) set.
* `IsAbsorbingIrreducibleSet` (p. 85) and **Proposition 4.2.4** (`proposition_4_2_4`, p. 85):
  the chain restricted to an absorbing set is a chain on that set, irreducible for the
  restricted measure.
* `isMaximalIrreducibility_count` (p. 83): for an irreducible chain on a countable space,
  counting measure is a maximal irreducibility measure.

**Corrections.**
* Proposition 4.2.2 and Theorem 4.0.1 need `φ ≠ 0`: every chain is `0`-irreducible, but the
  identity chain on `Bool` is `ψ`-irreducible for no probability measure `ψ`
  (`proposition_4_2_2_zero_counterexample`). In (iv) the measure `φ'` must be nonzero, and
  need not be finite.
* Proposition 4.2.3 (i) needs the absorbing set to be non-empty: `∅` is absorbing but full for no
  nonzero `ψ` (`proposition_4_2_3_i_counterexample`). Part (i) holds for every irreducibility
  measure, not only for a maximal one.
* Proposition 4.2.4 does not need Proposition 4.2.3: the restricted chain is irreducible for the
  restriction of any irreducibility measure.
-/

namespace MeynTweedie.DriftRegularity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A positive mass on a countable union sits on one of the sets. -/
theorem exists_measure_pos_of_iUnion {μ : Measure X} {s : ℕ → Set X}
    (h : 0 < μ (⋃ n, s n)) : ∃ n, 0 < μ (s n) := by
  by_contra hc
  push Not at hc
  rw [measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hc n)] at h
  exact lt_irrefl _ h

/-- `{y : K_{a_{1/2}}(y, A) > 0} = ⋃ₙ {y : Pⁿ(y, A) > 0}`. -/
theorem setOf_resolventHalf_pos (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) :
    {y | 0 < resolventHalf P y A} = ⋃ n, {y | 0 < (P ^ n) y A} := by
  ext y
  simp only [mem_ofPred_eq, mem_iUnion]
  exact resolventHalf_pos_iff P y hA

/-- `Ā = {y : L(y, A) > 0} = ⋃ₙ {y : Pⁿ⁺¹(y, A) > 0}`. -/
theorem setOf_hitProb_pos (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) :
    {y | 0 < hitProb P A y} = ⋃ n, {y | 0 < (P ^ (n + 1)) y A} := by
  ext y
  simp only [mem_ofPred_eq, mem_iUnion]
  exact hitProb_pos_iff P hA y

/-- `Ā = {y : L(y, A) > 0}` is measurable. -/
theorem measurableSet_hitProb_pos (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) : MeasurableSet {y | 0 < hitProb P A y} :=
  measurableSet_lt measurable_const (measurable_hitProb P hA)

/-! ### Equivalent probability measures -/

/-- **Exhaustion.** If `φ ≪ μ` with `μ` finite, then `μ` restricted to the complement of a
largest `φ`-null set is a finite measure equivalent to `φ`. No σ-finiteness of `φ` is needed. -/
theorem exists_finite_equiv_of_ac {φ μ : Measure X} [IsFiniteMeasure μ] (h : φ ≪ μ) :
    ∃ ν : Measure X, IsFiniteMeasure ν ∧ ν ≪ φ ∧ φ ≪ ν := by
  set N : Set (Set X) := {B | MeasurableSet B ∧ φ B = 0}
  set S : Set ℝ≥0∞ := μ '' N
  have hSne : S.Nonempty := ⟨μ ∅, ∅, ⟨MeasurableSet.empty, measure_empty⟩, rfl⟩
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne (OrderTop.bddAbove S)
  choose B hB hBu using huS
  set Bs := ⋃ n, B n
  have hBs : MeasurableSet Bs := MeasurableSet.iUnion fun n => (hB n).1
  have hφBs : φ Bs = 0 := measure_iUnion_null fun n => (hB n).2
  have hge : sSup S ≤ μ Bs :=
    le_of_tendsto' hu fun n => (hBu n) ▸ measure_mono (subset_iUnion B n)
  refine ⟨μ.restrict Bsᶜ, inferInstance, ?_, ?_⟩
  · refine Measure.AbsolutelyContinuous.mk fun A hA hφA => ?_
    rw [Measure.restrict_apply hA, ← sdiff_eq]
    have h1 : μ (A ∪ Bs) ≤ μ Bs :=
      (le_sSup (show μ (A ∪ Bs) ∈ S from
        ⟨A ∪ Bs, ⟨hA.union hBs, measure_union_null hφA hφBs⟩, rfl⟩)).trans hge
    rw [← sdiff_union_self, measure_union disjoint_sdiff_left hBs] at h1
    have h2 : μ (A \ Bs) + μ Bs ≤ 0 + μ Bs := by rwa [zero_add]
    exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_right (measure_ne_top μ Bs)).1 h2)
  · refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
    rw [Measure.restrict_apply hA] at h0
    rw [← inter_union_compl A Bs]
    exact measure_union_null (measure_mono_null inter_subset_right hφBs) (h h0)

/-- Every nonzero irreducibility measure is equivalent to a probability measure, which is again
an irreducibility measure (MT p. 83: "without loss of generality `φ(X) = 1`"). -/
theorem exists_prob_equiv (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ φ₀ : Measure X, IsProbabilityMeasure φ₀ ∧ φ₀ ≪ φ ∧ φ ≪ φ₀ := by
  have hne : (univ : Set X).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    exact h0 (Measure.measure_univ_eq_zero.1 (hc ▸ measure_empty))
  obtain ⟨x₀, -⟩ := hne
  have := isMarkovKernel_resolventHalf P
  have hac : φ ≪ resolventHalf P x₀ := Measure.AbsolutelyContinuous.mk fun A hA hK => by
    by_contra hc
    have := (proposition_4_2_1 P φ).2.2.1 hφ A hA (pos_iff_ne_zero.2 hc) x₀
    exact this.ne' hK
  obtain ⟨ν, hνf, hνφ, hφν⟩ := exists_finite_equiv_of_ac hac
  have hν0 : ν univ ≠ 0 := fun h => h0 (Measure.measure_univ_eq_zero.1 (hφν h))
  refine ⟨(ν univ)⁻¹ • ν, ⟨?_⟩, Measure.smul_absolutelyContinuous.trans hνφ,
    hφν.trans (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.2 (measure_ne_top ν _)))⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hν0 (measure_ne_top ν _)]

/-! ### The measure `ψ` of (4.10) -/

/-- The measure `ψ(A) = ∫ φ(dy) K_{a_{1/2}}(y, A)` of (4.10), MT p. 83. -/
noncomputable def maxIrrMeasure (P : Kernel X X) (φ : Measure X) : Measure X :=
  resolventHalf P ∘ₘ φ

/-- (4.10): `ψ(A) = ∫ φ(dy) K_{a_{1/2}}(y, A)`. -/
theorem maxIrrMeasure_apply (P : Kernel X X) (φ : Measure X) {A : Set X}
    (hA : MeasurableSet A) : maxIrrMeasure P φ A = ∫⁻ y, resolventHalf P y A ∂φ :=
  measure_kernel_apply φ _ hA

/-- `ψ(X) = φ(X)`; in particular `ψ` is a probability measure when `φ` is (MT p. 83). -/
theorem maxIrrMeasure_univ (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X) :
    maxIrrMeasure P φ univ = φ univ := by
  have := isMarkovKernel_resolventHalf P
  rw [maxIrrMeasure_apply P φ MeasurableSet.univ]
  simp

/-- `ψ` is a probability measure when `φ` is. -/
theorem isProbabilityMeasure_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    [IsProbabilityMeasure φ] : IsProbabilityMeasure (maxIrrMeasure P φ) :=
  ⟨by rw [maxIrrMeasure_univ, measure_univ]⟩

/-- **Proposition 4.2.2 (i)** for the measure (4.10): if `φ` is an irreducibility measure, so is
`ψ`. -/
theorem isPhiIrreducible_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) : IsPhiIrreducible P (maxIrrMeasure P φ) := by
  intro A hA hpos x
  rw [maxIrrMeasure_apply P φ hA, lintegral_pos_iff_support (Kernel.measurable_coe _ hA)] at hpos
  have hsupp : Function.support (fun y => resolventHalf P y A) = {y | 0 < resolventHalf P y A} := by
    ext y
    simp [Function.mem_support, pos_iff_ne_zero]
  rw [hsupp, setOf_resolventHalf_pos P hA] at hpos
  obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion hpos
  obtain ⟨m, hm⟩ := (hitProb_pos_iff P (measurableSet_pow_pos P n hA) x).1
    (hφ _ (measurableSet_pow_pos P n hA) hn x)
  refine (hitProb_pos_iff P hA x).2 ⟨m + n, ?_⟩
  rw [show m + n + 1 = (m + 1) + n by omega]
  exact (pow_add_pos_iff P (m + 1) n x hA).2 hm

/-- **Proposition 4.2.2 (ii)** for the measure (4.10): if `φ ≠ 0`, every irreducibility measure
is absolutely continuous with respect to `ψ`. -/
theorem ac_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P] {φ φ' : Measure X} (h0 : φ ≠ 0)
    (hφ' : IsPhiIrreducible P φ') : φ' ≪ maxIrrMeasure P φ := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hψ => ?_
  by_contra hc
  have hK := (proposition_4_2_1 P φ').2.2.1 hφ' A hA (pos_iff_ne_zero.2 hc)
  have hpos : 0 < ∫⁻ y, resolventHalf P y A ∂φ := by
    rw [lintegral_pos_iff_support (Kernel.measurable_coe _ hA)]
    have : Function.support (fun y => resolventHalf P y A) = univ :=
      eq_univ_of_forall fun y => (hK y).ne'
    rw [this, pos_iff_ne_zero]
    exact fun h => h0 (Measure.measure_univ_eq_zero.1 h)
  rw [maxIrrMeasure_apply P φ hA] at hψ
  exact hpos.ne' hψ

/-- **Proposition 4.2.2 (iii)** for the measure (4.10): if `ψ(A) = 0` then
`ψ{y : L(y, A) > 0} = 0`. -/
theorem maxIrrMeasure_hitSet_null (P : Kernel X X) [IsMarkovKernel P] (φ : Measure X)
    {A : Set X} (hA : MeasurableSet A) (h : maxIrrMeasure P φ A = 0) :
    maxIrrMeasure P φ {y | 0 < hitProb P A y} = 0 := by
  have hA' := measurableSet_hitProb_pos P hA
  rw [maxIrrMeasure_apply P φ hA, lintegral_eq_zero_iff (Kernel.measurable_coe _ hA)] at h
  rw [maxIrrMeasure_apply P φ hA', lintegral_eq_zero_iff (Kernel.measurable_coe _ hA')]
  filter_upwards [h] with y hy
  by_contra hne
  obtain ⟨n, hn⟩ := (resolventHalf_pos_iff P y hA').1 (pos_iff_ne_zero.2 hne)
  rw [setOf_hitProb_pos P hA] at hn
  obtain ⟨m, hm⟩ := exists_measure_pos_of_iUnion hn
  have hK : 0 < resolventHalf P y A :=
    (resolventHalf_pos_iff P y hA).2 ⟨_, (pow_add_pos_iff P n (m + 1) y hA).2 hm⟩
  exact hK.ne' hy

/-- The inequality in the proof of Proposition 4.2.2 (iii) (MT p. 84):
`∫ ψ(dy) Pᵐ(y, A) ≤ 2ᵐ ψ(A)`, i.e. `ψPᵐ ≤ 2ᵐ ψ`. -/
theorem maxIrrMeasure_comp_pow_le (P : Kernel X X) (φ : Measure X) (m : ℕ) {A : Set X}
    (hA : MeasurableSet A) : ((P ^ m) ∘ₘ maxIrrMeasure P φ) A ≤ 2 ^ m * maxIrrMeasure P φ A := by
  rw [measure_kernel_apply _ _ hA, maxIrrMeasure_apply P φ hA, maxIrrMeasure,
    Measure.lintegral_bind (Kernel.aemeasurable _) (Kernel.measurable_coe _ hA).aemeasurable,
    ← lintegral_const_mul _ (Kernel.measurable_coe _ hA)]
  refine lintegral_mono fun y => ?_
  set a : ℕ → ℝ≥0∞ := fun n => (1 - 2⁻¹) * 2⁻¹ ^ n with ha
  have hK : resolventHalf P y = Measure.sum fun n => a n • (P ^ n) y := rfl
  rw [hK, lintegral_sum_measure, Measure.sum_apply _ hA]
  simp_rw [lintegral_smul_measure, Measure.smul_apply, smul_eq_mul]
  have h2 : ∀ n, a n = 2 ^ m * a (n + m) := fun n => by
    simp only [ha, pow_add]
    have : (2 : ℝ≥0∞) ^ m * 2⁻¹ ^ m = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    calc ((1 : ℝ≥0∞) - 2⁻¹) * 2⁻¹ ^ n = (1 - 2⁻¹) * 2⁻¹ ^ n * (2 ^ m * 2⁻¹ ^ m) := by
          rw [this, mul_one]
      _ = _ := by ring
  calc ∑' n, a n * ∫⁻ z, (P ^ m) z A ∂(P ^ n) y
      = ∑' n, 2 ^ m * (a (n + m) * (P ^ (n + m)) y A) := by
        refine tsum_congr fun n => ?_
        rw [← Kernel.pow_add_apply_eq_lintegral P n m y hA, h2 n, mul_assoc]
    _ = 2 ^ m * ∑' n, a (n + m) * (P ^ (n + m)) y A := ENNReal.tsum_mul_left
    _ ≤ 2 ^ m * ∑' k, a k * (P ^ k) y A :=
        mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective m)
          (fun k => a k * (P ^ k) y A)) _

/-! ### Maximal irreducibility measures -/

/-- A *maximal irreducibility measure* (MT pp. 83–84): a nonzero irreducibility measure `ψ` such
that every irreducibility measure is absolutely continuous with respect to `ψ`. The chain is
*ψ-irreducible* when `ψ` is such a measure. -/
def IsMaximalIrreducibility (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) : Prop :=
  ψ ≠ 0 ∧ IsPhiIrreducible P ψ ∧ ∀ φ : Measure X, IsPhiIrreducible P φ → φ ≪ ψ

/-- The measure (4.10) of a nonzero irreducibility measure is maximal. -/
theorem isMaximalIrreducibility_maxIrrMeasure (P : Kernel X X) [IsMarkovKernel P]
    {φ : Measure X} (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    IsMaximalIrreducibility P (maxIrrMeasure P φ) := by
  refine ⟨fun h => h0 ?_, isPhiIrreducible_maxIrrMeasure P hφ,
    fun φ' h => ac_maxIrrMeasure P h0 h⟩
  rw [← Measure.measure_univ_eq_zero, ← maxIrrMeasure_univ P φ, h, Measure.coe_zero,
    Pi.zero_apply]

/-- **Proposition 4.2.2 (ii)** for a maximal `ψ`: `φ'` is an irreducibility measure iff
`φ' ≪ ψ`. -/
theorem IsMaximalIrreducibility.isPhiIrreducible_iff {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) (φ' : Measure X) :
    IsPhiIrreducible P φ' ↔ φ' ≪ ψ :=
  ⟨hψ.2.2 φ', fun h => hψ.2.1.mono h⟩

/-- Any two maximal irreducibility measures are equivalent (MT p. 84). -/
theorem IsMaximalIrreducibility.equiv {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hψ' : IsMaximalIrreducibility P ψ') :
    ψ ≪ ψ' ∧ ψ' ≪ ψ :=
  ⟨hψ'.2.2 ψ hψ.2.1, hψ.2.2 ψ' hψ'.2.1⟩

/-- A measure equivalent to a maximal irreducibility measure is maximal. -/
theorem IsMaximalIrreducibility.of_equiv {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (h1 : ψ ≪ ψ') (h2 : ψ' ≪ ψ) :
    IsMaximalIrreducibility P ψ' := by
  refine ⟨fun h => hψ.1 ?_, hψ.2.1.mono h2, fun φ hφ => (hψ.2.2 φ hφ).trans h1⟩
  rw [← Measure.measure_univ_eq_zero]
  exact h1 (by rw [h]; rfl)

/-- **Proposition 4.2.2 (iii)** for a maximal `ψ`: if `ψ(A) = 0` then
`ψ{y : L(y, A) > 0} = 0`. -/
theorem IsMaximalIrreducibility.hitSet_null {P : Kernel X X} [IsMarkovKernel P]
    {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A)
    (h : ψ A = 0) : ψ {y | 0 < hitProb P A y} = 0 := by
  have hψ₁ := isMaximalIrreducibility_maxIrrMeasure P hψ.2.1 hψ.1
  obtain ⟨h1, h2⟩ := hψ.equiv hψ₁
  exact h1 (maxIrrMeasure_hitSet_null P ψ hA (h2 h))

/-- **Proposition 4.2.2** (MT p. 83). If the chain is `φ`-irreducible for a nonzero measure `φ`,
there is a probability measure `ψ` such that (i) the chain is `ψ`-irreducible; (ii) the chain is
`φ'`-irreducible iff `φ' ≪ ψ`; (iii) `ψ(A) = 0` implies `ψ{y : L(y, A) > 0} = 0`; (iv) `ψ` is
equivalent to `ψ'(A) = ∫ φ'(dy) K_{a_{1/2}}(y, A)` for every nonzero irreducibility measure
`φ'`. -/
theorem proposition_4_2_2 (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ ψ : Measure X, IsProbabilityMeasure ψ ∧ IsPhiIrreducible P ψ ∧
      (∀ φ' : Measure X, IsPhiIrreducible P φ' ↔ φ' ≪ ψ) ∧
      (∀ A, MeasurableSet A → ψ A = 0 → ψ {y | 0 < hitProb P A y} = 0) ∧
      (∀ φ' : Measure X, IsPhiIrreducible P φ' → φ' ≠ 0 →
        maxIrrMeasure P φ' ≪ ψ ∧ ψ ≪ maxIrrMeasure P φ') := by
  obtain ⟨φ₀, hφ₀, h1, h2⟩ := exists_prob_equiv P hφ h0
  have hφ₀0 : φ₀ ≠ 0 := IsProbabilityMeasure.ne_zero φ₀
  have hmax := isMaximalIrreducibility_maxIrrMeasure P (hφ.mono h1) hφ₀0
  refine ⟨maxIrrMeasure P φ₀, isProbabilityMeasure_maxIrrMeasure P φ₀, hmax.2.1,
    hmax.isPhiIrreducible_iff, fun A hA h => hmax.hitSet_null hA h, fun φ' hφ' h0' => ?_⟩
  exact hmax.equiv (isMaximalIrreducibility_maxIrrMeasure P hφ' h0') |>.symm

/-- The measure of Proposition 4.2.2 is the construction (4.10) applied to a probability measure
`φ₀` equivalent to `φ`, and it is a maximal irreducibility measure. -/
theorem proposition_4_2_2_maximal (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ φ₀ : Measure X, IsProbabilityMeasure φ₀ ∧ φ₀ ≪ φ ∧ φ ≪ φ₀ ∧
      IsMaximalIrreducibility P (maxIrrMeasure P φ₀) := by
  obtain ⟨φ₀, hφ₀, h1, h2⟩ := exists_prob_equiv P hφ h0
  exact ⟨φ₀, hφ₀, h1, h2,
    isMaximalIrreducibility_maxIrrMeasure P (hφ.mono h1) (IsProbabilityMeasure.ne_zero φ₀)⟩

/-- **Correction to Proposition 4.2.2.** The hypothesis `φ ≠ 0` is needed: the identity chain on
`Bool` is `0`-irreducible, but it is `ψ`-irreducible for no probability measure `ψ`. -/
theorem proposition_4_2_2_zero_counterexample :
    IsPhiIrreducible (Kernel.id : Kernel Bool Bool) 0 ∧
      ¬ ∃ ψ : Measure Bool, IsProbabilityMeasure ψ ∧ IsPhiIrreducible Kernel.id ψ := by
  refine ⟨isPhiIrreducible_zero _, ?_⟩
  rintro ⟨ψ, hψ, hirr⟩
  have hAbs : ∀ b : Bool, IsAbsorbing (Kernel.id : Kernel Bool Bool) {b} := fun b x hx => by
    rw [Kernel.id_apply, Measure.dirac_apply_of_mem hx]
  have hb : ∀ b : Bool, ψ {b}ᶜ = 0 := fun b => by
    by_contra h
    have := hirr {b}ᶜ (measurableSet_singleton b).compl (pos_iff_ne_zero.2 h) b
    rw [(hAbs b).hitProb_compl (measurableSet_singleton b) (mem_singleton b)] at this
    exact lt_irrefl _ this
  have hu : (univ : Set Bool) = {true}ᶜ ∪ {false}ᶜ := by
    ext b
    cases b <;> simp
  have : ψ univ = 0 := by rw [hu]; exact measure_union_null (hb true) (hb false)
  rw [measure_univ] at this
  exact one_ne_zero this

/-! ### Full and absorbing sets -/

/-- `B⁺(X) = {A ∈ B(X) : ψ(A) > 0}` (MT p. 84). -/
def posSets (ψ : Measure X) : Set (Set X) := {A | MeasurableSet A ∧ 0 < ψ A}

/-- `B⁺(X)` does not depend on the choice of maximal irreducibility measure (MT p. 84). -/
theorem posSets_eq_of_maximal {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hψ' : IsMaximalIrreducibility P ψ') :
    posSets ψ = posSets ψ' := by
  obtain ⟨h1, h2⟩ := hψ.equiv hψ'
  ext A
  simp only [posSets, mem_ofPred_eq, pos_iff_ne_zero]
  exact and_congr_right fun _ => ⟨fun h h' => h (h1 h'), fun h h' => h (h2 h')⟩

/-- A set `A` is *full* if `ψ(Aᶜ) = 0` (MT p. 84). -/
def IsFull (ψ : Measure X) (A : Set X) : Prop := ψ Aᶜ = 0

/-- **Proposition 4.2.3 (i)** (MT p. 84): a non-empty absorbing set is full, for every
irreducibility measure. -/
theorem proposition_4_2_3_i {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {A : Set X} (hA : MeasurableSet A) (hne : A.Nonempty)
    (hAbs : IsAbsorbing P A) : IsFull φ A := by
  by_contra h
  obtain ⟨x, hx⟩ := hne
  have := hφ Aᶜ hA.compl (pos_iff_ne_zero.2 h) x
  rw [hAbs.hitProb_compl hA hx] at this
  exact lt_irrefl _ this

/-- **Correction to Proposition 4.2.3 (i).** The empty set is absorbing, but it is full for no
nonzero measure. -/
theorem proposition_4_2_3_i_counterexample (P : Kernel X X) {ψ : Measure X} (hψ : ψ ≠ 0) :
    IsAbsorbing P ∅ ∧ ¬ IsFull ψ ∅ := by
  refine ⟨fun x hx => absurd hx (notMem_empty x), fun h => hψ ?_⟩
  rw [IsFull, compl_empty] at h
  exact Measure.measure_univ_eq_zero.1 h

/-- **Proposition 4.2.3 (ii)** (MT p. 84): for a maximal irreducibility measure `ψ`, every full
set `A` contains a non-empty absorbing set, namely
`B = {y : Σ_{n ≥ 0} Pⁿ(y, Aᶜ) = 0} = {y : K_{a_{1/2}}(y, Aᶜ) = 0}`; `B` is also full. -/
theorem proposition_4_2_3_ii {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hfull : IsFull ψ A) :
    ∃ B ⊆ A, B.Nonempty ∧ MeasurableSet B ∧ IsAbsorbing P B ∧ IsFull ψ B := by
  set B := {y | resolventHalf P y Aᶜ = 0} with hBdef
  have hAc := hA.compl
  have hBm : MeasurableSet B :=
    (Kernel.measurable_coe _ hAc) (measurableSet_singleton 0)
  have hBc : Bᶜ = {y | 0 < resolventHalf P y Aᶜ} := by
    ext y
    simp [hBdef, pos_iff_ne_zero]
  have hBA : B ⊆ A := fun y hy => by
    by_contra hyA
    have : 0 < resolventHalf P y Aᶜ := (resolventHalf_pos_iff P y hAc).2
      ⟨0, by rw [pow_zero_apply, Measure.dirac_apply_of_mem hyA]; exact one_pos⟩
    exact this.ne' hy
  have hBfull : IsFull ψ B := by
    have hsub : Bᶜ ⊆ Aᶜ ∪ {y | 0 < hitProb P Aᶜ y} := fun y hy => by
      rw [hBc] at hy
      obtain ⟨n, hn⟩ := (resolventHalf_pos_iff P y hAc).1 hy
      rcases n with _ | n
      · left
        rw [pow_zero_apply, Measure.dirac_apply' _ hAc] at hn
        by_contra hc
        rw [indicator_of_notMem hc] at hn
        exact lt_irrefl _ hn
      · exact Or.inr ((hitProb_pos_iff P hAc y).2 ⟨n, hn⟩)
    exact measure_mono_null hsub (measure_union_null hfull (hψ.hitSet_null hAc hfull))
  refine ⟨B, hBA, ?_, hBm, ?_, hBfull⟩
  · by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    rw [IsFull, hc, compl_empty] at hBfull
    exact hψ.1 (Measure.measure_univ_eq_zero.1 hBfull)
  · intro y hy
    rw [← prob_compl_eq_zero_iff hBm]
    by_contra hc
    rw [hBc, setOf_resolventHalf_pos P hAc] at hc
    obtain ⟨n, hn⟩ := exists_measure_pos_of_iUnion (pos_iff_ne_zero.2 hc)
    have h1 : 0 < (P ^ (1 + n)) y Aᶜ := (pow_add_pos_iff P 1 n y hAc).2 (by rwa [pow_one])
    exact ((resolventHalf_pos_iff P y hAc).2 ⟨_, h1⟩).ne' hy

/-- **Theorem 4.0.1** (MT p. 75). If the chain is `φ`-irreducible for a nonzero `φ`, there is a
maximal irreducibility probability measure `ψ`, with `φ ≪ ψ`, such that (i) `ψ(A) > 0` implies
`L(x, A) > 0` for every `x`; (ii) `ψ(A) = 0` implies `ψ(Ā) = 0`, `Ā = {y : L(y, A) > 0}`;
(iii) if `ψ(Aᶜ) = 0` then `A = A₀ ∪ N` with `A₀` absorbing and `ψ(N) = 0`. -/
theorem theorem_4_0_1 (P : Kernel X X) [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) (h0 : φ ≠ 0) :
    ∃ ψ : Measure X, IsMaximalIrreducibility P ψ ∧ IsProbabilityMeasure ψ ∧ φ ≪ ψ ∧
      (∀ A, MeasurableSet A → 0 < ψ A → ∀ x, 0 < hitProb P A x) ∧
      (∀ A, MeasurableSet A → ψ A = 0 → ψ {y | 0 < hitProb P A y} = 0) ∧
      (∀ A, MeasurableSet A → ψ Aᶜ = 0 →
        ∃ A₀ N : Set X, A = A₀ ∪ N ∧ MeasurableSet A₀ ∧ IsAbsorbing P A₀ ∧ ψ N = 0) := by
  obtain ⟨φ₀, hφ₀, h1, h2, hmax⟩ := proposition_4_2_2_maximal P hφ h0
  refine ⟨maxIrrMeasure P φ₀, hmax, isProbabilityMeasure_maxIrrMeasure P φ₀, hmax.2.2 φ hφ,
    hmax.2.1, fun A hA h => hmax.hitSet_null hA h, fun A hA hfull => ?_⟩
  obtain ⟨B, hBA, -, hBm, hBabs, hBfull⟩ := proposition_4_2_3_ii hmax hA hfull
  refine ⟨B, A \ B, (union_sdiff_cancel hBA).symm, hBm, hBabs,
    measure_mono_null (fun y hy => hy.2) hBfull⟩

/-- **Theorem 4.0.1**, uniqueness: the maximal irreducibility measure is essentially unique. -/
theorem theorem_4_0_1_unique {P : Kernel X X} [IsMarkovKernel P] {ψ ψ' : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hψ' : IsMaximalIrreducibility P ψ') :
    ψ ≪ ψ' ∧ ψ' ≪ ψ :=
  hψ.equiv hψ'

/-! ### Restriction to an absorbing set -/

/-- An *absorbing ψ-irreducible set* (MT p. 85): `C` is absorbing and `ψ(B) > 0` implies
`L(x, B) > 0` for every `x ∈ C`. -/
def IsAbsorbingIrreducibleSet (P : Kernel X X) [IsMarkovKernel P] (ψ : Measure X) (C : Set X) :
    Prop :=
  IsAbsorbing P C ∧ ∀ B, MeasurableSet B → 0 < ψ B → ∀ x ∈ C, 0 < hitProb P B x

/-- **Proposition 4.2.4** (MT p. 85). The kernel `P_A` restricted to an absorbing set `A` is a
transition kernel on `A` (so the chain `Φ_A` exists, Theorem 3.4.1), and if the chain is
`φ`-irreducible then `Φ_A` is irreducible for the restriction of `φ` to `A`. -/
theorem proposition_4_2_4 (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (hAbs : IsAbsorbing P A) :
    ∃ _ : IsMarkovKernel (restrictKernel P hA), ∀ φ : Measure X, IsPhiIrreducible P φ →
      IsPhiIrreducible (restrictKernel P hA) (φ.comap Subtype.val) := by
  have hM := isMarkovKernel_restrictKernel P hA hAbs
  refine ⟨hM, fun φ hφ B hB hpos x => ?_⟩
  have hB' : MeasurableSet (Subtype.val '' B) :=
    (MeasurableEmbedding.subtype_coe hA).measurableSet_image.2 hB
  rw [comap_subtype_coe_apply hA] at hpos
  obtain ⟨n, hn⟩ := (hitProb_pos_iff P hB' x).1 (hφ _ hB' hpos x)
  refine (hitProb_pos_iff _ hB x).2 ⟨n, ?_⟩
  rwa [restrictKernel_pow_apply P hA hAbs (n + 1) x hB]

/-- For a maximal `ψ` and a non-empty absorbing `A`, the restriction of `ψ` to `A` is nonzero,
so Proposition 4.2.4 gives a nontrivial irreducibility measure for `Φ_A`; `A` is an absorbing
`ψ`-irreducible set. -/
theorem proposition_4_2_4_nonzero {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {A : Set X} (hA : MeasurableSet A) (hne : A.Nonempty)
    (hAbs : IsAbsorbing P A) :
    ψ.comap (Subtype.val : A → X) ≠ 0 ∧ IsAbsorbingIrreducibleSet P ψ A := by
  refine ⟨fun h => hψ.1 ?_, hAbs, fun B hB hpos x _ => hψ.2.1 B hB hpos x⟩
  have hfull := proposition_4_2_3_i hψ.2.1 hA hne hAbs
  have hAψ : ψ A = 0 := by
    have := congrArg (fun μ : Measure A => μ univ) h
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rwa [comap_subtype_coe_apply hA, image_univ, Subtype.range_coe] at this
  rw [← Measure.measure_univ_eq_zero, ← union_compl_self A]
  exact measure_union_null hAψ hfull

/-- MT p. 83: for an irreducible chain on a countable space, counting measure is a maximal
irreducibility measure. -/
theorem isMaximalIrreducibility_count [MeasurableSingletonClass X] [Countable X] [Nonempty X]
    (P : Kernel X X) [IsMarkovKernel P] (h : IsIrreducibleChain P) :
    IsMaximalIrreducibility P Measure.count := by
  refine ⟨fun h0 => ?_, (isIrreducibleChain_iff_count P).1 h, fun φ _ => ?_⟩
  · obtain ⟨x⟩ := ‹Nonempty X›
    have := congrArg (fun μ : Measure X => μ {x}) h0
    simp at this
  · exact Measure.AbsolutelyContinuous.mk fun A _ hA => by
      rw [Measure.count_eq_zero_iff.1 hA, measure_empty]

end MeynTweedie.DriftRegularity
