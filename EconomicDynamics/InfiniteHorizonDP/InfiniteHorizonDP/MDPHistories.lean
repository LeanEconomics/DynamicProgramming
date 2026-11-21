/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.MDPBasics
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The measures on histories induced by a plan

Copied from `EconomicDynamics/FiniteHorizonDP` (module `MDPHistories`), namespace renamed.

Copied from `EconomicDynamics/MarkovDecisionProcesses` (module `Histories`),
with the namespace renamed.

Miao, §5.1, (5.2), p. 139. Given an initial state `s₀`, a plan `π` and the stochastic kernels,
`μᵗ(s₀, ·; π)` (`mu M s₀ π t`) is the distribution of the history `sᵗ = (s₁, …, s_t)`, built as
in (5.2): `s₁ ~ P₁(s₀, π₀; ·)`, and given `sᵗ`, `s_{t+1} ~ P_{t+1}(s_t, π_t(sᵗ); ·)`
(`mu_succ_lintegral`). This is the finite-dimensional part of the Ionescu Tulcea theorem
(Miao's Theorem 3.2.4); the infinite-horizon measure `μ^∞` is in `Trajectory`.

* `isProbabilityMeasure_mu`: `μᵗ(s₀, ·; π)` is a probability measure ("well-defined
  probability measure on `Sᵗ`", p. 139).
* `eq_5_2`: (5.2) on measurable rectangles, in its recursive form
  `μᵗ⁺¹(B₁ × ⋯ × B_{t+1}) = ∫_{B₁×⋯×B_t} P_{t+1}(s_t, π_t(sᵗ); B_{t+1}) μᵗ(dsᵗ)`;
  unrolling it gives the iterated integral printed in (5.2).
* `mu_congr`: `μᵗ` depends on the plan only through `π₀, …, π_{t−1}`.
* `integral_mu_succ`: the corresponding identity for integrable functions.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

open Classical in
/-- The kernel of the next state given the history: `sᵗ ↦ P_{t+1}(s_t, π_t(sᵗ); ·)`
(the zero kernel if `π_t` is not measurable, a case that never arises for plans). -/
noncomputable def stepKernel (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) :
    Kernel (Fin t → S) S :=
  if hπ : Measurable (π t) then
    (M.P t).comap (fun h => (lastState s₀ h, π t h)) ((measurable_lastState s₀ t).prodMk hπ)
  else 0

/-- `μᵗ(s₀, ·; π)`, the distribution of the history `(s₁, …, s_t)` (Miao (5.2), p. 139). -/
noncomputable def mu (M : MDP S A) (s₀ : S) (π : Plan S A) : (t : ℕ) → Measure (Fin t → S)
  | 0 => Measure.dirac Fin.elim0
  | t + 1 =>
    ((mu M s₀ π t) ⊗ₘ stepKernel M s₀ π t).map fun p => (Fin.snoc p.1 p.2 : Fin (t + 1) → S)

theorem stepKernel_apply (M : MDP S A) (s₀ : S) {π : Plan S A} {t : ℕ} (hπ : Measurable (π t))
    (h : Fin t → S) : stepKernel M s₀ π t h = M.P t (lastState s₀ h, π t h) := by
  simp only [stepKernel, hπ, ↓reduceDIte, Kernel.comap_apply]

theorem isMarkovKernel_stepKernel (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A}
    {t : ℕ} (hπ : Measurable (π t)) : IsMarkovKernel (stepKernel M s₀ π t) := by
  have := hP t
  simp only [stepKernel, hπ, ↓reduceDIte]
  infer_instance

theorem isSFiniteKernel_stepKernel (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) (π : Plan S A)
    (t : ℕ) : IsSFiniteKernel (stepKernel M s₀ π t) := by
  by_cases hπ : Measurable (π t)
  · have := isMarkovKernel_stepKernel M hP s₀ hπ
    infer_instance
  · simp only [stepKernel, hπ, ↓reduceDIte]
    infer_instance

theorem sFinite_mu (M : MDP S A) (s₀ : S) (π : Plan S A) (t : ℕ) : SFinite (mu M s₀ π t) := by
  cases t with
  | zero => exact inferInstanceAs (SFinite (Measure.dirac _))
  | succ t => exact inferInstanceAs (SFinite (Measure.map _ _))

/-- `μᵗ(s₀, ·; π)` is a probability measure (Miao, p. 139). -/
theorem isProbabilityMeasure_mu (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A}
    {t : ℕ} (hπ : ∀ j < t, Measurable (π j)) : IsProbabilityMeasure (mu M s₀ π t) := by
  induction t with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  | succ t ih =>
    have := ih fun j hj => hπ j (by omega)
    have := isMarkovKernel_stepKernel M hP s₀ (hπ t (by omega))
    exact inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

theorem mu_zero (M : MDP S A) (s₀ : S) (π : Plan S A) : mu M s₀ π 0 = Measure.dirac Fin.elim0 :=
  rfl

theorem integral_mu_zero (M : MDP S A) (s₀ : S) (π : Plan S A) (f : (Fin 0 → S) → ℝ) :
    ∫ h, f h ∂mu M s₀ π 0 = f Fin.elim0 := by
  rw [mu_zero, integral_dirac]

/-- The last-date decomposition of `μᵗ⁺¹`: `∫ f dμᵗ⁺¹ = ∫ [∫ f(sᵗ, s′) P_{t+1}(s_t, π_t(sᵗ); ds′)]
μᵗ(dsᵗ)`. -/
theorem mu_succ_lintegral (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : Measurable (π t)) {f : (Fin (t + 1) → S) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ h, f h ∂mu M s₀ π (t + 1) =
      ∫⁻ h, ∫⁻ s, f (Fin.snoc h s) ∂M.P t (lastState s₀ h, π t h) ∂mu M s₀ π t := by
  have := sFinite_mu M s₀ π t
  have := isMarkovKernel_stepKernel M hP s₀ hπ
  rw [mu, lintegral_map hf (measurable_snoc t),
    Measure.lintegral_compProd (f := fun p : (Fin t → S) × S => f (Fin.snoc p.1 p.2))
      (hf.comp (measurable_snoc t))]
  refine lintegral_congr fun h => ?_
  rw [stepKernel_apply M s₀ hπ]

/-- **Miao (5.2)**, p. 139, on measurable rectangles: `μᵗ⁺¹(s₀, B₁ × ⋯ × B_{t+1}; π)` is the
integral over `B₁ × ⋯ × B_t` of `P_{t+1}(s_t, π_t(sᵗ); B_{t+1})` against `μᵗ(s₀, ·; π)`.
Iterating this identity gives the nested integral printed in (5.2). -/
theorem eq_5_2 (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : Measurable (π t)) {B : Fin (t + 1) → Set S} (hB : ∀ i, MeasurableSet (B i)) :
    mu M s₀ π (t + 1) (Set.pi Set.univ B) =
      ∫⁻ h in Set.pi Set.univ (Fin.init B), M.P t (lastState s₀ h, π t h) (B (Fin.last t))
        ∂mu M s₀ π t := by
  have hpi : MeasurableSet (Set.pi Set.univ B) := MeasurableSet.univ_pi hB
  have hpi' : MeasurableSet (Set.pi Set.univ (Fin.init B)) :=
    MeasurableSet.univ_pi fun i => hB _
  rw [← lintegral_indicator_one hpi, mu_succ_lintegral M hP s₀ hπ
    (measurable_one.indicator hpi), ← lintegral_indicator hpi']
  refine lintegral_congr fun h => ?_
  by_cases hh : h ∈ Set.pi Set.univ (Fin.init B)
  · rw [Set.indicator_of_mem hh, ← lintegral_indicator_one (hB _)]
    refine lintegral_congr fun s => ?_
    have : (Fin.snoc h s : Fin (t + 1) → S) ∈ Set.pi Set.univ B ↔ s ∈ B (Fin.last t) := by
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro H
        simpa using H (Fin.last t)
      · intro H i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using H
        · simpa [Fin.init] using hh j (Set.mem_univ _)
    by_cases hs : s ∈ B (Fin.last t)
    · rw [Set.indicator_of_mem (this.2 hs), Set.indicator_of_mem hs]
      rfl
    · rw [Set.indicator_of_notMem (fun H => hs (this.1 H)), Set.indicator_of_notMem hs]
  · rw [Set.indicator_of_notMem hh]
    refine (lintegral_congr fun s => ?_).trans lintegral_zero
    refine Set.indicator_of_notMem (fun H => hh ?_) _
    intro i _
    simpa [Fin.init] using H (Fin.castSucc i) (Set.mem_univ _)

/-- The integrable version of the last-date decomposition. -/
theorem integral_mu_succ (M : MDP S A) (hP : M.IsMarkov) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : Measurable (π t)) {f : (Fin (t + 1) → S) → ℝ}
    (hf : Integrable f (mu M s₀ π (t + 1))) :
    ∫ h, f h ∂mu M s₀ π (t + 1) =
      ∫ h, ∫ s, f (Fin.snoc h s) ∂M.P t (lastState s₀ h, π t h) ∂mu M s₀ π t := by
  have := sFinite_mu M s₀ π t
  have := isMarkovKernel_stepKernel M hP s₀ hπ
  rw [mu] at hf ⊢
  have hf' := (integrable_map_measure hf.1 (measurable_snoc t).aemeasurable).1 hf
  rw [integral_map (measurable_snoc t).aemeasurable hf.1,
    Measure.integral_compProd (f := fun p : (Fin t → S) × S => f (Fin.snoc p.1 p.2)) hf']
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [stepKernel_apply M s₀ hπ]

/-- `μᵗ(s₀, ·; π)` depends on `π` only through `π₀, …, π_{t−1}` and on the model only through
its kernels. -/
theorem mu_congr {M M' : MDP S A} (hMP : M.P = M'.P) (s₀ : S) {π π' : Plan S A} {t : ℕ}
    (hπ : ∀ j < t, π j = π' j) : mu M s₀ π t = mu M' s₀ π' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hk : stepKernel M s₀ π t = stepKernel M' s₀ π' t := by
      have h1 : π t = π' t := hπ t (by omega)
      unfold stepKernel
      rw [hMP]
      by_cases hm : Measurable (π t)
      · have hm' : Measurable (π' t) := h1 ▸ hm
        simp only [hm, hm', ↓reduceDIte]
        ext x : 1
        simp only [Kernel.comap_apply, h1]
      · have hm' : ¬ Measurable (π' t) := h1 ▸ hm
        simp only [hm, hm', ↓reduceDIte]
    simp only [mu, ih fun j hj => hπ j (by omega), hk]

/-- History measures of two models agree when their next-state kernels agree along the way. -/
theorem mu_eq_of_stepKernel {A' : Type*} [MeasurableSpace A'] {M : MDP S A} {M' : MDP S A'}
    (s₀ : S) {π : Plan S A} {π' : Plan S A'} {t : ℕ}
    (h : ∀ j < t, stepKernel M s₀ π j = stepKernel M' s₀ π' j) : mu M s₀ π t = mu M' s₀ π' t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [mu, ih fun j hj => h j (by omega), h t (by omega)]

end Miao.InfiniteHorizonDP
