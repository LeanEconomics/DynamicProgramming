/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticApplications.BoundedPolicy
import StochasticApplications.HistMarginals

/-!
# Policy functions and transition functions

SLP §9.6, pp. 283–287.

* **Theorem 9.13** (`theorem_9_13`): for a measurable policy `g : S → X`,
  `P[(x, z), A × B] = Q(z, B)` if `g(x, z) ∈ A` and `0` otherwise defines a unique transition
  function on `S = X × Z` (`policyKernel`, `δ_{g(s)} ⊗ Q(z, ·)`).
* **Exercise 9.15** (`ex_9_15a`, `ex_9_15b`): `∫ f dP[(x, z), ·] = ∫ f(g(x, z), z′) Q(z, dz′)` for
  nonnegative measurable and for `P`-integrable `f`.
* **Theorem 9.14** (`theorem_9_14`): if `Q` satisfies Assumption 9.5 (`M` preserves bounded
  continuous functions, Lemma 9.5) and `g` is continuous, `P` has the Feller property.
* **Exercise 9.17** (`ex_9_17a`, `ex_9_17b`): in the second formulation,
  `P[(x, z), A × B] = Q[z, B ∩ H(x, z, A)]` with `H(x, z, A) = {z′ : φ[x, g(x, z), z′] ∈ A}`
  defines a transition function (`policyKernel'`); it is Feller if `g` is continuous and a
  selection from `Γ` and `φ` is continuous on `D × Z` (Lemma 9.5′).
-/

namespace StokeyLucasPrescott.StochasticApplications

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- The transition function of the state `(x, z)` under the policy `g`: `δ_{g(x, z)} ⊗ Q(z, ·)`. -/
noncomputable def policyKernel (Q : Kernel Z Z) {g : X × Z → X} (hg : Measurable g) :
    Kernel (X × Z) (X × Z) :=
  Kernel.deterministic g hg ×ₖ Q.comap Prod.snd measurable_snd

theorem policyKernel_apply (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X}
    (hg : Measurable g) (s : X × Z) :
    policyKernel Q hg s = (Q s.2).map (Prod.mk (g s)) := by
  rw [policyKernel, Kernel.prod_apply, Kernel.deterministic_apply, Kernel.comap_apply,
    Measure.dirac_prod]

open Classical in
/-- **Theorem 9.13.** For measurable `g : S → X`, `P[(x, z), A × B] = Q(z, B)` if `g(x, z) ∈ A`
and `0` otherwise defines a transition function on `(S, 𝒮)`, and it is the only one with these
values on measurable rectangles. -/
theorem theorem_9_13 (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g) :
    IsMarkovKernel (policyKernel Q hg) ∧
      (∀ x z A B, MeasurableSet A → MeasurableSet B →
        policyKernel Q hg (x, z) (A ×ˢ B) = if g (x, z) ∈ A then Q z B else 0) ∧
      ∀ P : Kernel (X × Z) (X × Z), IsMarkovKernel P →
        (∀ x z A B, MeasurableSet A → MeasurableSet B →
          P (x, z) (A ×ˢ B) = if g (x, z) ∈ A then Q z B else 0) → P = policyKernel Q hg := by
  have hval : ∀ x z A B, MeasurableSet A → MeasurableSet B →
      policyKernel Q hg (x, z) (A ×ˢ B) = if g (x, z) ∈ A then Q z B else 0 := by
    intro x z A B hA hB
    rw [policyKernel, Kernel.prod_apply_prod, Kernel.deterministic_apply' _ _ hA,
      Kernel.comap_apply]
    by_cases h : g (x, z) ∈ A <;> simp [h]
  have hM : IsMarkovKernel (policyKernel Q hg) :=
    inferInstanceAs (IsMarkovKernel (Kernel.deterministic g hg ×ₖ _))
  refine ⟨hM, hval, fun P hP hval' => ?_⟩
  ext ⟨x, z⟩ : 1
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨A, hA, B, hB, rfl⟩
  rw [hval' x z A B hA hB, hval x z A B hA hB]

/-- **Exercise 9.15a.** For nonnegative measurable `f`,
`∫ f(x′, z′) P[(x, z), dx′ × dz′] = ∫ f[g(x, z), z′] Q(z, dz′)`. -/
theorem ex_9_15a (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g)
    {f : X × Z → ℝ≥0∞} (hf : Measurable f) (s : X × Z) :
    ∫⁻ p, f p ∂policyKernel Q hg s = ∫⁻ z', f (g s, z') ∂Q s.2 := by
  rw [policyKernel_apply, lintegral_map hf measurable_prodMk_left]

/-- **Exercise 9.15b.** The same equality for `P[(x, z), ·]`-integrable `f`. -/
theorem ex_9_15b (Q : Kernel Z Z) [IsMarkovKernel Q] {g : X × Z → X} (hg : Measurable g)
    {f : X × Z → ℝ} (s : X × Z) (hf : Integrable f (policyKernel Q hg s)) :
    ∫ p, f p ∂policyKernel Q hg s = ∫ z', f (g s, z') ∂Q s.2 := by
  rw [policyKernel_apply] at hf ⊢
  rw [integral_map measurable_prodMk_left.aemeasurable hf.aestronglyMeasurable]

/-- **Theorem 9.14.** If `M` maps bounded continuous functions on `X × Z` to continuous functions
(Assumption 9.5 via Lemma 9.5) and `g` is continuous, `P` has the Feller property:
`(M_P f)(x, z) = (M_Q f)[g(x, z), z]`. -/
theorem theorem_9_14 [TopologicalSpace X] [TopologicalSpace Z] [BorelSpace X]
    [OpensMeasurableSpace Z] [SecondCountableTopologyEither X Z] (Q : Kernel Z Z)
    [IsMarkovKernel Q] (hQ : PreservesBC X Q) {g : X × Z → X} (hgc : Continuous g) :
    IsFeller (policyKernel Q hgc.measurable) := by
  intro f hf hb
  have := (theorem_9_13 Q hgc.measurable).1
  have heq : markovOpR (policyKernel Q hgc.measurable) f = fun s => mop Q f (g s, s.2) := by
    funext s
    obtain ⟨B, hB⟩ := hb
    rw [markovOpR, ex_9_15b Q hgc.measurable s (integrable_of_abs_le hf.measurable hB)]
    rfl
  rw [heq]
  exact (hQ f hf hb).comp (hgc.prodMk continuous_snd)

variable {Y : Type*} [MeasurableSpace Y]

/-- The transition function of `(x, z)` in the second formulation: `z′ ~ Q(z, ·)` and
`x′ = φ[x, g(x, z), z′]`. -/
noncomputable def policyKernel' (Q : Kernel Z Z) (φ : X × Y × Z → X) (g : X × Z → Y) :
    Kernel (X × Z) (X × Z) :=
  (Kernel.deterministic id measurable_id ×ₖ Q.comap Prod.snd measurable_snd).map
    fun p => (φ (p.1.1, g p.1, p.2), p.2)

theorem measurable_policy' {φ : X × Y × Z → X} (hφ : Measurable φ) {g : X × Z → Y}
    (hg : Measurable g) : Measurable fun p : (X × Z) × Z => (φ (p.1.1, g p.1, p.2), p.2) :=
  (hφ.comp (measurable_fst.fst.prodMk ((hg.comp measurable_fst).prodMk measurable_snd))).prodMk
    measurable_snd

theorem policyKernel'_apply (Q : Kernel Z Z) [IsMarkovKernel Q] {φ : X × Y × Z → X}
    (hφ : Measurable φ) {g : X × Z → Y} (hg : Measurable g) (s : X × Z) :
    policyKernel' Q φ g s = (Q s.2).map fun z' => (φ (s.1, g s, z'), z') := by
  rw [policyKernel', Kernel.map_apply _ (measurable_policy' hφ hg), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (measurable_policy' hφ hg) measurable_prodMk_left]
  rfl

/-- **Exercise 9.17a.** `P[(x, z), A × B] = Q[z, B ∩ H(x, z, A)]`, with
`H(x, z, A) = {z′ : φ[x, g(x, z), z′] ∈ A}`, defines a transition function on `(S, 𝒮)`. -/
theorem ex_9_17a (Q : Kernel Z Z) [IsMarkovKernel Q] {φ : X × Y × Z → X} (hφ : Measurable φ)
    {g : X × Z → Y} (hg : Measurable g) :
    IsMarkovKernel (policyKernel' Q φ g) ∧
      ∀ x z A B, MeasurableSet A → MeasurableSet B →
        policyKernel' Q φ g (x, z) (A ×ˢ B) = Q z (B ∩ {z' | φ (x, g (x, z), z') ∈ A}) := by
  refine ⟨by unfold policyKernel'; exact Kernel.IsMarkovKernel.map _ (measurable_policy' hφ hg),
    fun x z A B hA hB => ?_⟩
  have hm : Measurable fun z' => (φ ((x, z).1, g (x, z), z'), z') :=
    (hφ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).prodMk
      measurable_id
  rw [policyKernel'_apply Q hφ hg, Measure.map_apply hm (hA.prod hB)]
  congr 1
  ext z'
  simp [and_comm]

/-- **Exercise 9.17b.** Under Assumptions 9.4, 9.5 (on `D × Z`), 9.16 and 9.17, if `g` is
continuous and a selection from `Γ`, then `P` has the Feller property:
`(M_P f)(x, z) = ∫ f[φ(x, g(x, z), z′), z′] Q(z, dz′)` is continuous by Lemma 9.5′. -/
theorem ex_9_17b {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [BorelSpace Y]
    [OpensMeasurableSpace (X × Z)] (M : Model X Y Z) [IsMarkovKernel M.Q] (hφm : Measurable M.φ)
    (hφc : ContinuousOn (fun q : (X × Y) × Z => M.φ (q.1.1, q.1.2, q.2)) (domD M ×ˢ univ))
    (hQ : PreservesBC (domD M) M.Q) {g : X × Z → Y} (hgc : Continuous g)
    (hgΓ : ∀ s, g s ∈ M.Γ s) : IsFeller (policyKernel' M.Q M.φ g) := by
  intro f hf hb
  have hcont := contExp_of_preservesBC M hφc hQ f hf hb
  have heq : markovOpR (policyKernel' M.Q M.φ g) f =
      fun s => ∫ z', f (M.φ (s.1, g s, z'), z') ∂M.Q s.2 := by
    funext s
    have hm : Measurable fun z' => (M.φ (s.1, g s, z'), z') :=
      (hφm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).prodMk
        measurable_id
    rw [markovOpR, policyKernel'_apply M.Q hφm hgc.measurable,
      integral_map hm.aemeasurable hf.measurable.aestronglyMeasurable]
  rw [heq]
  exact hcont.comp_continuous ((continuous_fst.prodMk hgc).prodMk continuous_snd)
    fun s => ⟨mem_domD M (hgΓ s), mem_univ _⟩

end StokeyLucasPrescott.StochasticApplications
