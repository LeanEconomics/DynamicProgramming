/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Objective

/-!
# Deterministic decision problems

Miao, p. 142: "This model includes deterministic decision problems as a special case." With the
deterministic kernels `P_{t+1}(s, a; B) = 1_B(f(s, a))` (`detKernel`), a plan determines a single
path `s_{t+1} = f(s_t, π_t(sᵗ))` (`detPath`); the history measure is the point mass at that path
(`mu_det`), and the objective (5.3) is the discounted sum of rewards along it (`J0T_det`), as
in a deterministic problem.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- The path of a plan under the law of motion `s_{t+1} = f(s_t, π_t(sᵗ))`. -/
def detPath (f : S × A → S) (s₀ : S) (π : Plan S A) : (t : ℕ) → Fin t → S
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (detPath f s₀ π t) (f (lastState s₀ (detPath f s₀ π t), π t
      (detPath f s₀ π t)))

/-- Miao, p. 142: with deterministic kernels, `μᵗ(s₀, ·; π)` is the point mass at the path. -/
theorem mu_det (M : MDP S A) {f : S × A → S} (hf : Measurable f)
    (hMP : ∀ t, M.P t = detKernel hf) (s₀ : S) {π : Plan S A} {t : ℕ}
    (hπ : ∀ j < t, Measurable (π j)) : mu M s₀ π t = Measure.dirac (detPath f s₀ π t) := by
  have hP : M.IsMarkov := fun t => by
    rw [hMP t]
    exact inferInstanceAs (IsMarkovKernel (Kernel.deterministic f hf))
  induction t with
  | zero => exact (mu_zero M s₀ π).trans (congrArg _ (Subsingleton.elim _ _))
  | succ t ih =>
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    rw [mu_succ_lintegral M hP s₀ (hπ t (by omega)) hg, ih fun j hj => hπ j (by omega),
      lintegral_dirac' _ ?_, hMP t, detKernel, Kernel.deterministic_apply,
      lintegral_dirac' _ (f := fun s => g (Fin.snoc (detPath f s₀ π t) s))
        (hg.comp ((measurable_snoc t).comp (measurable_const.prodMk measurable_id))),
      lintegral_dirac' _ hg]
    · rfl
    · have := isMarkovKernel_stepKernel M hP s₀ (hπ t (by omega))
      have hm : Measurable fun h => ∫⁻ s, g (Fin.snoc h s) ∂stepKernel M s₀ π t h :=
        (hg.comp (measurable_snoc t)).lintegral_kernel_prod_right'
      simp only [stepKernel_apply M s₀ (hπ t (by omega))] at hm
      exact hm

/-- Miao, p. 142: with deterministic kernels, the objective (5.3) is the discounted sum of the
rewards along the path. -/
theorem J0T_det (M : MDP S A) {f : S × A → S} (hf : Measurable f)
    (hMP : ∀ t, M.P t = detKernel hf) (hu : ∀ t, Measurable (M.u t)) (huT : Measurable M.uT)
    (s₀ : S) {T : ℕ} {π : Plan S A} (hπ : ∀ j < T, Measurable (π j)) :
    J0T M T s₀ π = ∑ t ∈ Finset.range T, M.β ^ t *
        M.u t (lastState s₀ (detPath f s₀ π t), π t (detPath f s₀ π t)) +
      M.β ^ T * M.uT (lastState s₀ (detPath f s₀ π T)) := by
  rw [J0T, mu_det M hf hMP s₀ hπ, integral_dirac' (fun h => M.uT (lastState s₀ h)) _
    (huT.comp (measurable_lastState s₀ T)).stronglyMeasurable]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [expRew, mu_det M hf hMP s₀ fun j hj => hπ j (by omega), integral_dirac' (rew M s₀ π t) _
    (measurable_rew M s₀ (hu t) (hπ t ht')).stronglyMeasurable]
  rfl

end Miao.MarkovDecisionProcesses
