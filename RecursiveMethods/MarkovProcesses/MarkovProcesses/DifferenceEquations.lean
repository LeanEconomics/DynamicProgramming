/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovProcesses.TransitionFunctions

/-!
# Transitions defined by stochastic difference equations

SLP §8.4, pp. 234–237. Theorem 8.9: a stochastic difference equation `z_{t+1} = g(z_t, w_t)`
with i.i.d. shocks `w_t ~ μ` defines the transition function `Q(z, A) = μ{w : g(z, w) ∈ A}`
(`theorem_8_9`; its kernel is `sdeKernel`). Exercise 8.10: if `g` is continuous, `Q` has the
Feller property (`ex_8_10`). Exercise 8.11: a second-order process is a first-order process on
the expanded state space `W × W` (`ex_8_11`).
-/

namespace StokeyLucasPrescott.MarkovProcesses

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]

/-- **Theorem 8.9.** For a probability measure `μ` on `W` and measurable `g : Z × W → Z`,
`Q(z, A) = μ{w : g(z, w) ∈ A}` is a transition function. The book's proof: `Q(z, ·)` is the
image of `μ` under `g(z, ·)`, and `z ↦ μ([Γ(A)]_z)` is measurable because sections of measurable
sets have measurable measure (a monotone class argument). -/
theorem theorem_8_9 (μ : Measure W) [IsProbabilityMeasure μ] {g : Z × W → Z}
    (hg : Measurable g) : IsTransitionFunction fun z A => μ {w | g (z, w) ∈ A} := by
  refine ⟨fun z => ⟨μ.map fun w => g (z, w), inferInstance, fun A hA => ?_⟩, fun A hA => ?_⟩
  · have hgz : Measurable fun w => g (z, w) := hg.comp measurable_prodMk_left
    rw [Measure.map_apply hgz hA]
    rfl
  · exact measurable_measure_prodMk_left (hg hA)

/-- The transition kernel of the difference equation `z′ = g(z, w)`, `w ~ μ`. -/
noncomputable def sdeKernel (μ : Measure W) (g : Z × W → Z) : Kernel Z Z :=
  ((Kernel.deterministic id measurable_id) ×ₖ Kernel.const Z μ).map g

theorem sdeKernel_apply (μ : Measure W) [IsProbabilityMeasure μ] {g : Z × W → Z}
    (hg : Measurable g) (z : Z) : sdeKernel μ g z = μ.map fun w => g (z, w) := by
  rw [sdeKernel, Kernel.map_apply _ hg, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
  rfl

theorem isMarkovKernel_sdeKernel (μ : Measure W) [IsProbabilityMeasure μ] {g : Z × W → Z}
    (hg : Measurable g) : IsMarkovKernel (sdeKernel μ g) := by
  unfold sdeKernel
  exact Kernel.IsMarkovKernel.map _ hg

/-- **Exercise 8.10.** If `g` is continuous (on separable metric spaces with their Borel sets),
`Q` has the Feller property: `(Tf)(z) = ∫ f[g(z, w)] μ(dw)`, and `zₙ → z` gives
`∫ f[g(zₙ, w)] μ(dw) → ∫ f[g(z, w)] μ(dw)` by dominated convergence. -/
theorem ex_8_10 [TopologicalSpace Z] [TopologicalSpace W] [SecondCountableTopology Z]
    [SecondCountableTopology W] [BorelSpace Z] [BorelSpace W] (μ : Measure W)
    [IsProbabilityMeasure μ] {g : Z × W → Z} (hg : Continuous g) :
    IsFeller (sdeKernel μ g) := by
  intro f hf ⟨M, hM⟩
  have hgm : Measurable g := hg.measurable
  have heq : markovOpR (sdeKernel μ g) f = fun z => ∫ w, f (g (z, w)) ∂μ := by
    funext z
    have hgz : Measurable fun w => g (z, w) := hgm.comp measurable_prodMk_left
    rw [markovOpR, sdeKernel_apply μ hgm z, integral_map hgz.aemeasurable
      hf.measurable.aestronglyMeasurable]
  rw [heq]
  refine continuous_of_dominated (bound := fun _ => M) (fun z => ?_) (fun z => ?_)
    (integrable_const M) (Eventually.of_forall fun w => ?_)
  · exact (hf.measurable.comp (hgm.comp measurable_prodMk_left)).aestronglyMeasurable
  · exact Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hM _
  · exact hf.comp (hg.comp (continuous_id.prodMk continuous_const))

open Classical in
/-- **Exercise 8.11.** A second-order process `P(w, w′, ·)` on `W` is a first-order process on
`Z = W × W`: there is a unique transition function `Q` on `W × W` with
`Q[(w, w′), A × B] = P(w, w′, B)` if `w′ ∈ A` and `0` otherwise. -/
theorem ex_8_11 (P : Kernel (W × W) W) [IsMarkovKernel P] :
    ∃ κ : Kernel (W × W) (W × W), IsMarkovKernel κ ∧
      (∀ w w' A B, MeasurableSet A → MeasurableSet B →
        κ (w, w') (A ×ˢ B) = if w' ∈ A then P (w, w') B else 0) ∧
      ∀ κ' : Kernel (W × W) (W × W), IsMarkovKernel κ' →
        (∀ w w' A B, MeasurableSet A → MeasurableSet B →
          κ' (w, w') (A ×ˢ B) = if w' ∈ A then P (w, w') B else 0) → κ' = κ := by
  let κ : Kernel (W × W) (W × W) := Kernel.deterministic Prod.snd measurable_snd ×ₖ P
  have hκ : IsMarkovKernel κ := inferInstance
  have hval : ∀ w w' A B, MeasurableSet A → MeasurableSet B →
      κ (w, w') (A ×ˢ B) = if w' ∈ A then P (w, w') B else 0 := by
    intro w w' A B hA hB
    rw [Kernel.prod_apply_prod, Kernel.deterministic_apply' _ _ hA]
    by_cases h : w' ∈ A <;> simp [h]
  refine ⟨κ, hκ, hval, fun κ' hκ' hval' => ?_⟩
  ext ⟨w, w'⟩ : 1
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨A, hA, B, hB, rfl⟩
  rw [hval' w w' A B hA hB, hval w w' A B hA hB]

end StokeyLucasPrescott.MarkovProcesses
