/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.POConverse

/-!
# Theorem 6.3.3 fails off the reachable histories

Copied from `EconomicDynamics/FiniteHorizonDP` (module `POCounterexample`), namespace renamed.

Miao, Theorem 6.3.3, p. 170, claims `π*_t(sᵗ) ∈ G_t(s_t)` for **all** histories `sᵗ`. Here is a
process satisfying every hypothesis of the theorem with an optimal plan that violates the claim
on a history of probability zero (`theorem_6_3_3_counterexample`).

`S = A = Bool`, `Γ(s) = A`, the next state is always `true` (`P_{t+1}(s, a; ·) = δ_true`), the
reward is `u_t(s, a) = 1` if `a = true` and `0` otherwise, `u_T = 0`, `β = 1`, `T = 2`. The value
functions are `V₀ = 2`, `V₁ = 1`, `V₂ = 0` and `G_t(s) = {true}`. The plan `π₀ = true`,
`π₁(s₁) = s₁` is optimal (the history `s₁ = true` has probability one), but
`π₁(false) = false ∉ G₁(false)`.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory

/-- The process of the counterexample. -/
noncomputable def po_cexModel : MDP Bool Bool where
  Γ := fun _ => Set.univ
  P := fun _ => Kernel.const _ (Measure.dirac true)
  u := fun _ x => if x.2 then 1 else 0
  uT := fun _ => 0
  β := 1

/-- Its value functions. -/
def po_cexW : ℕ → Bool → ℝ := fun t _ => if t = 0 then 2 else if t = 1 then 1 else 0

/-- The optimal plan `π₀ = true`, `π₁(s₁) = s₁` (and `π_t(sᵗ) = s₁` later). -/
def po_cexPlan : Plan Bool Bool := fun j h => if hj : 0 < j then h ⟨0, hj⟩ else true

theorem po_cex_markov : po_cexModel.IsMarkov := fun _ => by
  change IsMarkovKernel (Kernel.const _ (Measure.dirac true))
  infer_instance

theorem po_cex_bellmanVal (t : ℕ) (s a : Bool) :
    po_bellmanVal po_cexModel po_cexW t s a = (if a then 1 else 0) + po_cexW (t + 1) true := by
  simp only [po_bellmanVal, po_cexModel, Kernel.const_apply, integral_dirac, one_mul]

theorem po_cex_solves (t : ℕ) (ht : t < 2) (s : Bool) :
    po_SolvesAt po_cexModel po_cexW t s ∧ true ∈ po_G po_cexModel po_cexW t s := by
  refine po_solvesAt_of_max (fun a _ => ?_) (Set.mem_univ _) ?_
  · rw [po_cex_bellmanVal]
    interval_cases t <;> cases a <;> norm_num [po_cexW]
  · rw [po_cex_bellmanVal]
    interval_cases t <;> norm_num [po_cexW]

theorem po_cex_assumption (T : ℕ) : po_Assumption513 po_cexModel T :=
  po_assumption513_of_bounded po_cex_markov (B := 1)
    ⟨fun t x => by simp only [po_cexModel]; split_ifs <;> norm_num,
      fun s => by simp [po_cexModel]⟩
    (fun _ => measurable_of_countable _) (measurable_of_countable _) T

theorem po_cex_values (t : ℕ) (ht : t ≤ 2) (s : Bool) :
    V0 (po_shift po_cexModel t) (2 - t) s = po_cexW t s := by
  have := (theorem_6_3_2 po_cex_markov zero_le_one (po_cex_assumption 2) (g := fun _ _ => true)
    (fun t _ s a _ => by
      change Integrable _ (Measure.dirac true)
      exact Integrable.of_finite) (fun t ht s => (po_cex_solves t ht s).1)
    (fun _ _ => measurable_const) (fun t ht s => (po_cex_solves t ht s).2)
    (fun s => by simp [po_cexW, po_cexModel]) t ht (fun _ => s)).2.2
  rw [eq_6_14] at this
  exact this

/-- **Theorem 6.3.3 as printed is false** (Miao, p. 170): the counterexample process satisfies
the hypotheses of `theorem_6_3_3` (Markov kernels, `β > 0`, Assumption 5.1.3, measurable value
functions solving the Bellman equation with integrable continuation values) and `po_cexPlan` is
optimal from `s₀ = true`, yet `π₁(sᵗ) ∈ G₁(s₁)` fails at the history `s₁ = false`. -/
theorem theorem_6_3_3_counterexample :
    po_cexModel.IsMarkov ∧ 0 < po_cexModel.β ∧ Assumption513 po_cexModel 2 ∧
      (∀ t ≤ 2, Measurable (po_cexW t)) ∧
      (∀ t ≤ 2, ∀ s, V0 (po_shift po_cexModel t) (2 - t) s = po_cexW t s) ∧
      (∀ t < 2, ∀ s, ∀ a ∈ po_cexModel.Γ s,
        Integrable (po_cexW (t + 1)) (po_cexModel.P t (s, a))) ∧
      (∀ t < 2, ∀ s, po_SolvesAt po_cexModel po_cexW t s) ∧
      IsOptimalPlan0 po_cexModel 2 true po_cexPlan ∧
      ¬ ∀ t < 2, ∀ h : Fin t → Bool,
        po_cexPlan t h ∈ po_G po_cexModel po_cexW t (lastState true h) := by
  have hI := po_cex_assumption 2
  have hF : po_cexPlan ∈ feasiblePlans po_cexModel ((2 : ℕ) : ℕ∞) true :=
    ⟨fun _ _ => measurable_of_countable _, fun _ _ _ => Set.mem_univ _⟩
  refine ⟨po_cex_markov, one_pos, hI 0 (Nat.zero_le 2), fun _ _ => measurable_of_countable _,
    po_cex_values, fun _ _ _ _ _ => by
      change Integrable _ (Measure.dirac true)
      exact Integrable.of_finite,
    fun t ht s => (po_cex_solves t ht s).1, ⟨hF, ?_⟩, ?_⟩
  · have hV := po_cex_values 0 (Nat.zero_le 2) true
    rw [po_shift_zero, Nat.sub_zero] at hV
    rw [hV]
    have hF1 := po_cont_feasible hF true
    have hI1 : Assumption513 (po_shift po_cexModel 1) 1 := hI 1 (by norm_num)
    have h1 : J0T po_cexModel 2 true po_cexPlan =
        po_cexModel.u 0 (true, po_cexPlan 0 Fin.elim0) + po_cexModel.β *
          ∫ s', J0T (po_shift po_cexModel 1) 1 s' (po_cont po_cexPlan s') ∂Measure.dirac true :=
      po_J0T_succ (n := 1) po_cex_markov (po_plan_meas hF)
        (po_intPlan_of_assumption513 (hI 0 (Nat.zero_le 2)) hF)
    have h2 : J0T (po_shift po_cexModel 1) 1 true (po_cont po_cexPlan true) =
        (po_shift po_cexModel 1).u 0 (true, po_cont po_cexPlan true 0 Fin.elim0) +
          (po_shift po_cexModel 1).β * ∫ s', J0T (po_shift (po_shift po_cexModel 1) 1) 0 s'
            (po_cont (po_cont po_cexPlan true) s') ∂Measure.dirac true :=
      po_J0T_succ (n := 0) (po_shift_isMarkov po_cex_markov 1) (po_plan_meas hF1)
        (po_intPlan_of_assumption513 hI1 hF1)
    rw [integral_dirac] at h1 h2
    rw [po_J0T_zero] at h2
    rw [h1, h2]
    norm_num [po_cexW, po_cexModel, po_shift, po_cexPlan, po_cont]
  · intro h
    have := (h 1 (by norm_num) fun _ => false).2
    rw [po_cex_bellmanVal] at this
    simp [po_cexPlan, po_cexW] at this

end Miao.InfiniteHorizonDP
