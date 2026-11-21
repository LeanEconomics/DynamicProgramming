/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.MDPObjective

/-!
# Transporting history measures between models

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Simulation`),
with the namespace renamed.

A tool for the examples of Miao, §5.2, pp. 143–154, where a problem stated in its own terms (a
stopping rule on an exogenous Markov chain, a control problem with a law of motion) is recast as
a Markov decision process. The text asserts that the recast problem *is* the original one; here
this is proved by showing that the MDP's history measure `μᵗ` is the image of the original
history measure under an explicit map of histories.

* `chainMDP Q`: an exogenous Markov chain with (possibly time-varying) transition functions
  `Q t` (the book's `Q_{t+1}`), seen as an MDP with a single action; `chainHist Q z₀ t` is the
  distribution of `(z₁, …, z_t)` (`chainHist_succ_lintegral`).
* `liftHist ψ`: histories `S₁ᵗ → S₂ᵗ` built one date at a time, `s₂,t+1 = ψ_t(s₂ᵗ, s₁,t+1)`.
* `mu_simulation`: if, along lifted histories, the kernel of the second model is the image of
  the kernel of the first under `ψ_t`, then `μ₂ᵗ = μ₁ᵗ ∘ Φ_t⁻¹`.
* `expRew_simulation`: the corresponding identity for expected rewards.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S₁ A₁ S₂ A₂ : Type*} [MeasurableSpace S₁] [MeasurableSpace A₁] [MeasurableSpace S₂]
  [MeasurableSpace A₂]

/-- The histories `Φ_t(s₁ᵗ) ∈ S₂ᵗ` built from the step maps `ψ_t`:
`Φ_{t+1}(s₁ᵗ, s) = (Φ_t(s₁ᵗ), ψ_t(Φ_t(s₁ᵗ), s))`. -/
def liftHist (ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂) : (t : ℕ) → (Fin t → S₁) → Fin t → S₂
  | 0, _ => Fin.elim0
  | t + 1, h => Fin.snoc (liftHist ψ t (Fin.init h)) (ψ t (liftHist ψ t (Fin.init h))
      (h (Fin.last t)))

omit [MeasurableSpace S₁] [MeasurableSpace S₂] in
theorem liftHist_snoc (ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂) {t : ℕ} (h : Fin t → S₁)
    (s : S₁) : liftHist ψ (t + 1) (Fin.snoc h s) =
      Fin.snoc (liftHist ψ t h) (ψ t (liftHist ψ t h) s) := by
  simp [liftHist, Fin.init_snoc]

theorem measurable_liftHist {ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂} {t : ℕ}
    (hψ : ∀ j < t, Measurable fun p : (Fin j → S₂) × S₁ => ψ j p.1 p.2) :
    Measurable (liftHist ψ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h1 := (ih fun j hj => hψ j (by omega)).comp (measurable_init t)
    exact (measurable_snoc t).comp (h1.prodMk ((hψ t (by omega)).comp
      (h1.prodMk (measurable_pi_apply _))))

/-- **Transport of history measures.** If, for every history `h` of the first model, the
second model's kernel at the lifted history is the image under `ψ_t(Φ_t h, ·)` of the first
model's kernel at `h`, then `μ₂ᵗ(s₂, ·; π₂)` is the image of `μ₁ᵗ(s₁, ·; π₁)` under `Φ_t`. -/
theorem mu_simulation (M₁ : MDP S₁ A₁) (M₂ : MDP S₂ A₂) (hP₁ : M₁.IsMarkov) (hP₂ : M₂.IsMarkov)
    (s₁ : S₁) (s₂ : S₂) {π₁ : Plan S₁ A₁} {π₂ : Plan S₂ A₂}
    {ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂}
    {t : ℕ} (hψ : ∀ j < t, Measurable fun p : (Fin j → S₂) × S₁ => ψ j p.1 p.2)
    (hπ₁ : ∀ j < t, Measurable (π₁ j)) (hπ₂ : ∀ j < t, Measurable (π₂ j))
    (hstep : ∀ j < t, ∀ h : Fin j → S₁,
      M₂.P j (lastState s₂ (liftHist ψ j h), π₂ j (liftHist ψ j h)) =
        (M₁.P j (lastState s₁ h, π₁ j h)).map (ψ j (liftHist ψ j h))) :
    mu M₂ s₂ π₂ t = (mu M₁ s₁ π₁ t).map (liftHist ψ t) := by
  induction t with
  | zero =>
    rw [mu_zero, mu_zero, Measure.map_dirac' (measurable_liftHist hψ)]
    congr 1
  | succ t ih =>
    have ih := ih (fun j hj => hψ j (by omega)) (fun j hj => hπ₁ j (by omega))
      (fun j hj => hπ₂ j (by omega)) (fun j hj => hstep j (by omega))
    have hm₁ := hπ₁ t (by omega)
    have hm₂ := hπ₂ t (by omega)
    have hΦ : Measurable (liftHist ψ t) := measurable_liftHist fun j hj => hψ j (by omega)
    have hΦ' : Measurable (liftHist ψ (t + 1)) := measurable_liftHist hψ
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    have := isMarkovKernel_stepKernel M₂ hP₂ s₂ hm₂
    have hg : Measurable fun g : Fin t → S₂ =>
        ∫⁻ s, f (Fin.snoc g s) ∂stepKernel M₂ s₂ π₂ t g :=
      (hf.comp (measurable_snoc t)).lintegral_kernel_prod_right'
    rw [lintegral_map hf hΦ', mu_succ_lintegral M₂ hP₂ s₂ hm₂ hf,
      mu_succ_lintegral M₁ hP₁ s₁ hm₁ (f := fun h => f (liftHist ψ (t + 1) h)) (hf.comp hΦ')]
    simp_rw [← stepKernel_apply M₂ s₂ hm₂]
    rw [ih, lintegral_map hg hΦ]
    refine lintegral_congr fun h => ?_
    have hψh : Measurable (ψ t (liftHist ψ t h)) :=
      (hψ t (by omega)).comp (measurable_const.prodMk measurable_id)
    rw [stepKernel_apply M₂ s₂ hm₂, hstep t (by omega) h,
      lintegral_map (f := fun s => f (Fin.snoc (liftHist ψ t h) s))
        (hf.comp ((measurable_snoc t).comp (measurable_const.prodMk measurable_id))) hψh]
    refine lintegral_congr fun s => ?_
    rw [liftHist_snoc]

/-- The expected rewards of the second model are expectations over the first model's histories:
`∫ u₂ dμ₂ᵗ = ∫ (u₂ ∘ Φ_t) dμ₁ᵗ`. -/
theorem expRew_simulation (M₁ : MDP S₁ A₁) (M₂ : MDP S₂ A₂) (hP₁ : M₁.IsMarkov)
    (hP₂ : M₂.IsMarkov) (s₁ : S₁) (s₂ : S₂) {π₁ : Plan S₁ A₁} {π₂ : Plan S₂ A₂}
    {ψ : (t : ℕ) → (Fin t → S₂) → S₁ → S₂}
    {t : ℕ} (hψ : ∀ j < t, Measurable fun p : (Fin j → S₂) × S₁ => ψ j p.1 p.2)
    (hπ₁ : ∀ j < t, Measurable (π₁ j)) (hπ₂ : ∀ j < t, Measurable (π₂ j))
    (hstep : ∀ j < t, ∀ h : Fin j → S₁,
      M₂.P j (lastState s₂ (liftHist ψ j h), π₂ j (liftHist ψ j h)) =
        (M₁.P j (lastState s₁ h, π₁ j h)).map (ψ j (liftHist ψ j h)))
    {f : (Fin t → S₂) → ℝ} (hf : Measurable f) :
    ∫ g, f g ∂mu M₂ s₂ π₂ t = ∫ h, f (liftHist ψ t h) ∂mu M₁ s₁ π₁ t := by
  rw [mu_simulation M₁ M₂ hP₁ hP₂ s₁ s₂ hψ hπ₁ hπ₂ hstep,
    integral_map (measurable_liftHist hψ).aemeasurable hf.aestronglyMeasurable]

/-- An exogenous Markov chain with transition functions `Q t` (the book's `Q_{t+1}`), as a
Markov decision process with a single action and no rewards. -/
noncomputable def chainMDP {Z : Type*} [MeasurableSpace Z] (Q : ℕ → Kernel Z Z) : MDP Z Unit where
  Γ := fun _ => Set.univ
  P := fun t => (Q t).comap Prod.fst measurable_fst
  u := fun _ _ => 0
  uT := fun _ => 0
  β := 0

/-- The distribution of `(z₁, …, z_t)` for the chain started at `z₀`. -/
noncomputable def chainHist {Z : Type*} [MeasurableSpace Z] (Q : ℕ → Kernel Z Z) (z₀ : Z)
    (t : ℕ) : Measure (Fin t → Z) :=
  mu (chainMDP Q) z₀ (fun _ _ => ()) t

theorem chainMDP_isMarkov {Z : Type*} [MeasurableSpace Z] {Q : ℕ → Kernel Z Z}
    (hQ : ∀ t, IsMarkovKernel (Q t)) : (chainMDP Q).IsMarkov := fun t => by
  have := hQ t
  exact inferInstanceAs (IsMarkovKernel ((Q t).comap Prod.fst measurable_fst))

theorem isProbabilityMeasure_chainHist {Z : Type*} [MeasurableSpace Z] {Q : ℕ → Kernel Z Z}
    (hQ : ∀ t, IsMarkovKernel (Q t)) (z₀ : Z) (t : ℕ) :
    IsProbabilityMeasure (chainHist Q z₀ t) :=
  isProbabilityMeasure_mu _ (chainMDP_isMarkov hQ) z₀ fun _ _ => measurable_const

/-- The chain's history distribution: `∫ f dμᵗ⁺¹ = ∫ [∫ f(zᵗ, z′) Q_{t+1}(z_t, dz′)] μᵗ(dzᵗ)`. -/
theorem chainHist_succ_lintegral {Z : Type*} [MeasurableSpace Z] {Q : ℕ → Kernel Z Z}
    (hQ : ∀ t, IsMarkovKernel (Q t)) (z₀ : Z) (t : ℕ) {f : (Fin (t + 1) → Z) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ h, f h ∂chainHist Q z₀ (t + 1) =
      ∫⁻ h, ∫⁻ z, f (Fin.snoc h z) ∂Q t (lastState z₀ h) ∂chainHist Q z₀ t :=
  mu_succ_lintegral _ (chainMDP_isMarkov hQ) z₀ measurable_const hf

/-- Miao, p. 137: "The state system is governed by a Markov process `(s_t)`." Under a Markovian
plan `π_t(sᵗ) = g_t(s_t)` (including `π₀ = g₀(s₀)`), the history measure `μᵗ(s₀, ·; π)` is the
distribution of the Markov chain with transition functions `s ↦ P_{t+1}(s, g_t(s); ·)`. -/
theorem mu_markovian (M : MDP S₁ A₁) (hP : M.IsMarkov) (s₀ : S₁) {g : ℕ → S₁ → A₁}
    (hg : ∀ t, Measurable (g t)) {π : Plan S₁ A₁}
    (hπ : ∀ t (h : Fin t → S₁), π t h = g t (lastState s₀ h)) (t : ℕ) :
    mu M s₀ π t = chainHist (fun t => (M.P t).comap (fun s => (s, g t s))
      (measurable_id.prodMk (hg t))) s₀ t := by
  have hπm : ∀ t, Measurable (π t) := fun t => by
    have : π t = fun h => g t (lastState s₀ h) := funext (hπ t)
    rw [this]
    exact (hg t).comp (measurable_lastState s₀ t)
  refine mu_eq_of_stepKernel s₀ fun j _ => ?_
  have := hP j
  ext h : 1
  rw [stepKernel_apply M s₀ (hπm j), stepKernel_apply _ s₀ measurable_const, hπ]
  rfl

end Miao.FiniteHorizonDP
