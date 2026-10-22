/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.FPeriodicErgodic

/-!
# Theorem 14.3.6 (i) with the cycle inside `S_f`

Meyn and Tweedie, Theorem 14.3.6 (i), p. 351: for a positive recurrent chain with `π(f) < ∞`
there are a full set `S_f`, a cycle `{Dᵢ}` contained in `S_f` and probabilities `πᵢ` with
`‖P^{nd+r}(x, ·) − π_r‖_f → 0` for `x ∈ D_r`.

* `exists_absorbing_subset`: inside every full set of a chain with an invariant probability
  `π ~ ψ` there is a measurable, full, absorbing set: the points from which the chain never charges
  the complement of a measurable full subset.
* `IsCycle.inter_absorbing`: the restriction `Dᵢ ∩ S` of a cycle to a measurable full absorbing
  set is a cycle, with the same probabilities `πᵢ = d π(· ∩ Dᵢ)` (`cycleInv_inter_of_null`).
* **Theorem 14.3.6 (i)** (`theorem_14_3_6_i_cycle`): there are the period `d`, a measurable full
  absorbing set `S_f`, a `d`-cycle `{Dᵢ}` with every `Dᵢ ⊆ S_f`, and for every class `i`, phase
  `r < d` and `x ∈ Dᵢ`, `‖P^{nd+r}(x, ·) − π_{i+r}‖_f → 0`.
* `theorem_14_3_6_i_book`: the labelling of (14.26). With the probabilities
  `π'_r = d π(· ∩ D_{2r})` (`r ∈ ℤ/d`), `‖P^{nd+r}(x, ·) − π'_r‖_f → 0` for `x ∈ D_r`: from `D_r`
  the chain is in `D_{2r}` at the times `nd + r`, so the book's `π_r` is the cycle probability of
  the class `2r`, not of `r`.
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- **An absorbing full subset**: if `π` is an invariant probability with `π ≪ ψ` and `ψ ≪ π`,
every full set `S` contains a measurable, full, absorbing set. -/
theorem exists_absorbing_subset {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) (hπψ : π ≪ ψ) (hψπ : ψ ≪ π)
    {S : Set X} (hS : ψ Sᶜ = 0) :
    ∃ S' : Set X, MeasurableSet S' ∧ S' ⊆ S ∧ IsAbsorbing P S' ∧ ψ S'ᶜ = 0 := by
  set N := toMeasurable ψ Sᶜ with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNψ : ψ N = 0 := by rw [hN, measure_toMeasurable]; exact hS
  have hNπ : π N = 0 := hπψ hNψ
  have hGS : Nᶜ ⊆ S := fun x hx => by
    by_contra h
    exact hx (subset_toMeasurable ψ Sᶜ h)
  have hpow : ∀ n, Measurable fun x => (P ^ n : Kernel X X) x N := fun n =>
    Kernel.measurable_coe _ hNm
  set S' := ⋂ n : ℕ, {x | (P ^ n : Kernel X X) x N = 0} with hS'
  have hS'm : MeasurableSet S' :=
    MeasurableSet.iInter fun n => hpow n (measurableSet_singleton 0)
  -- the null sets `{Pⁿ(·, N) > 0}`
  have hnullπ : ∀ n, π {x | (P ^ n : Kernel X X) x N ≠ 0} = 0 := fun n => by
    have h1 : ∫⁻ x, (P ^ n : Kernel X X) x N ∂π = 0 := by
      rw [← measure_kernel_apply π _ hNm, hπ.pow n]
      exact hNπ
    have h2 := (lintegral_eq_zero_iff (hpow n)).1 h1
    rw [Filter.EventuallyEq, ae_iff] at h2
    exact h2
  refine ⟨S', hS'm, fun x hx => hGS ?_, fun x hx => ?_, ?_⟩
  · have h0 := mem_iInter.1 hx 0
    change (P ^ 0 : Kernel X X) x N = 0 at h0
    rw [pow_zero_apply, Measure.dirac_apply' _ hNm] at h0
    intro hxN
    rw [indicator_of_mem hxN, Pi.one_apply] at h0
    exact one_ne_zero h0
  · -- absorbing
    refine (prob_compl_eq_zero_iff hS'm).1 ?_
    have hc : S'ᶜ = ⋃ n : ℕ, {y | (P ^ n : Kernel X X) y N ≠ 0} := by
      rw [hS', compl_iInter]
      rfl
    rw [hc]
    refine measure_iUnion_null fun n => ?_
    have h1 : ∫⁻ y, (P ^ n : Kernel X X) y N ∂P x = 0 := by
      rw [← pow_succ_apply P n x hNm]
      exact mem_iInter.1 hx (n + 1)
    have h2 := (lintegral_eq_zero_iff (hpow n)).1 h1
    rw [Filter.EventuallyEq, ae_iff] at h2
    exact h2
  · have hc : S'ᶜ = ⋃ n : ℕ, {y | (P ^ n : Kernel X X) y N ≠ 0} := by
      rw [hS', compl_iInter]
      rfl
    rw [hc]
    exact measure_iUnion_null fun n => hψπ (hnullπ n)

/-- If `π(Sᶜ) = 0`, the cycle probabilities of `Dᵢ ∩ S` and `Dᵢ` agree. -/
theorem cycleInv_inter_of_null {d : ℕ} (D : ZMod d → Set X) {π : Measure X} {S : Set X}
    (hSm : MeasurableSet S) (hπS : π Sᶜ = 0) (j : ZMod d) :
    cycleInv π (fun i => D i ∩ S) j = cycleInv π D j := by
  rw [cycleInv, cycleInv]
  congr 1
  ext B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
  refine le_antisymm (measure_mono (inter_subset_inter_right _ inter_subset_left)) ?_
  rw [← measure_inter_add_sdiff (B ∩ D j) hSm]
  have h0 : π ((B ∩ D j) \ S) = 0 := measure_mono_null (fun y hy => hy.2) hπS
  rw [h0, add_zero]
  exact measure_mono fun y hy => ⟨hy.1.1, hy.1.2, hy.2⟩

/-- The restriction of a cycle to a measurable, full, absorbing set is a cycle. -/
theorem IsCycle.inter_absorbing {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} {d : ℕ}
    {D : ZMod d → Set X} (hD : IsCycle P ψ d D) {S : Set X} (hSm : MeasurableSet S)
    (hSa : IsAbsorbing P S) (hSψ : ψ Sᶜ = 0) : IsCycle P ψ d (fun i => D i ∩ S) := by
  refine ⟨fun i => (hD.measurableSet i).inter hSm,
    fun i j hij => (hD.disjoint i j hij).mono inter_subset_left inter_subset_left,
    fun i x hx => ?_, ?_⟩
  · have h1 := hD.step i x hx.1
    have hc : P x (D (i + 1) ∩ S)ᶜ = 0 := by
      rw [compl_inter]
      exact measure_union_null ((prob_compl_eq_zero_iff (hD.measurableSet _)).2 h1)
        ((prob_compl_eq_zero_iff hSm).2 (hSa x hx.2))
    exact (prob_compl_eq_zero_iff ((hD.measurableSet _).inter hSm)).1 hc
  · refine measure_mono_null (fun y hy => ?_) (measure_union_null hD.null_compl hSψ)
    by_cases hyS : y ∈ S
    · refine Or.inl fun hyD => hy ?_
      obtain ⟨j, hj⟩ := mem_iUnion.1 hyD
      exact mem_iUnion.2 ⟨j, hj, hyS⟩
    · exact Or.inr hyS

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.3.6 (i)** with the cycle inside `S_f` (MT p. 351), (14.26): for a positive
recurrent chain with invariant probability `π`, `f ≥ 1` and `π(f) < ∞`, there are the period `d`,
a measurable full absorbing set `S_f` and a `d`-cycle `{Dᵢ}` with `Dᵢ ⊆ S_f`, such that
`‖P^{nd+r}(x, ·) − π_{i+r}‖_f → 0` for every class `i`, phase `r < d` and `x ∈ Dᵢ`, where
`πᵢ = d π(· ∩ Dᵢ)`. -/
theorem theorem_14_3_6_i_cycle {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ d : ℕ, IsPeriod P ψ d ∧ ∃ S : Set X, MeasurableSet S ∧ IsFull ψ S ∧ IsAbsorbing P S ∧
      ∃ D : ZMod d → Set X, IsCycle P ψ d D ∧ (∀ i, D i ⊆ S) ∧
        (∀ i, IsProbabilityMeasure (cycleInv π D i)) ∧
        ∀ i : ZMod d, ∀ r < d, ∀ x ∈ D i,
          Tendsto (fun n => fNorm f ((P ^ (d * n + r) : Kernel X X) x) (cycleInv π D (i + r)))
            atTop (𝓝 0) := by
  obtain ⟨d, hper, D, hD, hprob, S, hS, hconv⟩ := theorem_14_3_6_i hpos hπ hf hf1 hπf
  have hac := theorem_10_4_9_equiv (proposition_10_1_1 hpos) ⟨inferInstance, hπ⟩
    (IsProbabilityMeasure.ne_zero π)
  obtain ⟨S', hS'm, hS'S, hS'a, hS'ψ⟩ := exists_absorbing_subset hπ hac.1 hac.2 hS
  have hπS' : π S'ᶜ = 0 := hac.1 hS'ψ
  have hinv := cycleInv_inter_of_null D hS'm hπS'
  refine ⟨d, hper, S', hS'm, hS'ψ, hS'a, fun i => D i ∩ S', hD.inter_absorbing hS'm hS'a hS'ψ,
    fun i => inter_subset_right, fun i => by rw [hinv i]; exact hprob i,
    fun i r hr x hx => ?_⟩
  rw [hinv]
  exact hconv i r hr x ⟨hx.1, hS'S hx.2⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 14.3.6 (i) in the book's labelling** (MT (14.26)): with the cycle and full
absorbing `S_f` of `theorem_14_3_6_i_cycle`, the probabilities `π'_r = d π(· ∩ D_{2r})` satisfy
`‖P^{nd+r}(x, ·) − π'_r‖_f → 0` for `x ∈ D_r` (`r ∈ ℤ/d`, the phase being `r.val`). -/
theorem theorem_14_3_6_i_book {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π)
    {f : X → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ x, 1 ≤ f x) (hπf : ∫⁻ x, f x ∂π ≠ ∞) :
    ∃ d : ℕ, IsPeriod P ψ d ∧ ∃ S : Set X, MeasurableSet S ∧ IsFull ψ S ∧ IsAbsorbing P S ∧
      ∃ D : ZMod d → Set X, IsCycle P ψ d D ∧ (∀ i, D i ⊆ S) ∧
        ∃ πs : ZMod d → Measure X, (∀ r, IsProbabilityMeasure (πs r)) ∧
        ∀ r : ZMod d, ∀ x ∈ D r,
          Tendsto (fun n => fNorm f ((P ^ (d * n + r.val) : Kernel X X) x) (πs r))
            atTop (𝓝 0) := by
  obtain ⟨d, hper, S, hSm, hSf, hSa, D, hD, hDS, hprob, hconv⟩ :=
    theorem_14_3_6_i_cycle hpos hπ hf hf1 hπf
  have : NeZero d := ⟨hper.1.ne'⟩
  refine ⟨d, hper, S, hSm, hSf, hSa, D, hD, hDS, fun r => cycleInv π D (r + r),
    fun r => hprob _, fun r x hx => ?_⟩
  have h := hconv r r.val (ZMod.val_lt r) x hx
  rwa [ZMod.natCast_zmod_val] at h

end MeynTweedie.FErgodicity
