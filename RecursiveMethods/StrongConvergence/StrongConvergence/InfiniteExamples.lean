/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StrongConvergence.DoeblinErgodic

/-!
# Markov chains on a countable set: Examples 6 and 7

SLP §11.1, pp. 333–334. On `S = ℕ`:

* **Example 6** (`ex6`): the identity. Every `{sᵢ}` is an invariant set and every `δᵢ` an
  invariant distribution, so there are infinitely many of each.
* **Example 7** (`ex7`): the shift `sᵢ ↦ sᵢ₊₁`. Every state is transient (it is never revisited),
  `Πᵏ → 0` entrywise, and there is no invariant probability measure: "all of the probability
  wanders off to infinity".
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- **Example 6.** For the identity on `ℕ`, each `{i}` is an invariant set and each `δᵢ` an
invariant distribution; these are pairwise distinct. -/
theorem ex6 :
    (∀ i, IsInvariantSet (Kernel.deterministic (id : ℕ → ℕ) measurable_id) {i}) ∧
      (∀ i, adjointOp (Kernel.deterministic (id : ℕ → ℕ) measurable_id) (Measure.dirac i) =
        Measure.dirac i) ∧
      Function.Injective fun i : ℕ => Measure.dirac i := by
  refine ⟨fun i => ⟨measurableSet_singleton i, singleton_nonempty i, fun s hs n _ => ?_⟩,
    fun i => ?_, fun i j h => ?_⟩
  · rw [mem_singleton_iff] at hs
    subst hs
    rw [kpow_deterministic, Function.iterate_id, id, Measure.dirac_apply_of_mem (mem_singleton s)]
  · rw [adjointOp, Measure.dirac_bind (Kernel.measurable _), Kernel.deterministic_apply, id]
  · have := congrArg (fun μ : Measure ℕ => μ {i}) h
    simp only [Measure.dirac_apply_of_mem (mem_singleton i)] at this
    by_contra hij
    rw [Measure.dirac_apply' _ (measurableSet_singleton i), indicator_of_notMem
      (show j ∉ ({i} : Set ℕ) from fun h' => hij (mem_singleton_iff.1 h').symm)] at this
    exact one_ne_zero this

/-- **Example 7.** For the shift on `ℕ`: no state is ever revisited, so every state is transient;
`Πᵏ → 0` entrywise; and there is no invariant probability measure. -/
theorem ex7 :
    (∀ i n, 1 ≤ n → kpow (Kernel.deterministic Nat.succ measurable_from_top) n i {i} = 0) ∧
      (∀ i j, Tendsto (fun k =>
        (kpow (Kernel.deterministic Nat.succ measurable_from_top) k i).real {j}) atTop (𝓝 0)) ∧
      ∀ μ : Measure ℕ, IsProbabilityMeasure μ →
        adjointOp (Kernel.deterministic Nat.succ measurable_from_top) μ ≠ μ := by
  have hk : ∀ k i, kpow (Kernel.deterministic Nat.succ measurable_from_top) k i =
      Measure.dirac (i + k) := fun k i => by
    rw [kpow_deterministic, Nat.succ_iterate]
  refine ⟨fun i n hn => ?_, fun i j => ?_, fun μ hμ h => ?_⟩
  · rw [hk, Measure.dirac_apply' _ (measurableSet_singleton i), indicator_of_notMem]
    simp; omega
  · refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨j + 1, fun k hk' => ?_⟩)
    dsimp only
    rw [hk, measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton j),
      indicator_of_notMem (by simp; omega)]
    rfl
  · -- `μ = μ ∘ succ⁻¹` forces `μ{n} = 0` for all `n`
    have hmap : ∀ A, MeasurableSet A → μ (Nat.succ ⁻¹' A) = μ A := fun A hA => by
      have := congrArg (fun ν : Measure ℕ => ν A) h
      simp only [adjointOp] at this
      rw [Measure.bind_apply hA (Kernel.aemeasurable _)] at this
      rw [← this]
      simp only [Kernel.deterministic_apply]
      rw [← lintegral_indicator_one (measurable_from_top (f := Nat.succ) hA)]
      refine lintegral_congr fun n => ?_
      rw [Measure.dirac_apply' _ hA]
      by_cases hn : n + 1 ∈ A
      · rw [indicator_of_mem (show n ∈ Nat.succ ⁻¹' A from hn), indicator_of_mem hn]; rfl
      · rw [indicator_of_notMem (show n ∉ Nat.succ ⁻¹' A from hn), indicator_of_notMem hn]
    have h0 : ∀ n, μ {n} = 0 := by
      intro n
      induction n with
      | zero =>
        rw [← hmap _ (measurableSet_singleton 0)]
        have : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext m; simp
        rw [this, measure_empty]
      | succ n ih =>
        rw [← hmap _ (measurableSet_singleton _)]
        have : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by ext m; simp
        rw [this, ih]
    have : μ univ = 0 := by
      rw [← iUnion_of_singleton (α := ℕ)]
      exact measure_iUnion_null h0
    rw [measure_univ] at this
    exact one_ne_zero this

end StokeyLucasPrescott.StrongConvergence
