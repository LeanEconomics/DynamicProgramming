/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.Histories

/-!
# Randomized actions

Miao, §5.1, pp. 142–143. The initial state is drawn from `P₀`; a date-`t` history is
`h_t = (s₀, a₀, …, a_{t−1}, s_t)`, here the pair `((s_j, a_j)_{j<t}, s_t)`; a randomized action is
a kernel `π_t(h_t; da)` from histories to actions (`RPlan`).

* `IsFeasibleR`: `π_t(h_t)(Γ(s_t)) = 1`. **Correction:** the book writes the measurability
  requirement as "`Γ(s) ∈ A`"; it should read `Γ(s) ∈ 𝒜` (each `Γ(s)` is a measurable subset of
  the action space), as `π_t(h_t)(Γ(s_t))` is otherwise undefined.
* `rmu M P₀ π t`: the measure `μ_t(ds₀, da₀, …, ds_{t−1}, da_{t−1}; π)` on `(S × A)ᵗ` of p. 143,
  built date by date: `s_t` from `P_t(s_{t−1}, a_{t−1}; ·)` (from `P₀` at `t = 0`), then
  `a_t ~ π_t(h_t; ·)`. `isProbabilityMeasure_rmu`: it is a probability measure.
* `detRPlan`: a deterministic plan as a randomized one, `π_t(h_t) = δ_{π_t(s₁, …, s_t)}`;
  `detRPlan_feasible_iff`: it is feasible exactly when the deterministic plan is
  (`π_t(sᵗ) ∈ Γ(s_t)` for all histories), so the deterministic model is the special case of the
  book's remark.

The infinite-horizon measure is obtained exactly as in `Trajectory` (Ionescu Tulcea); it is not
repeated here.
-/

namespace Miao.MarkovDecisionProcesses

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- A randomized plan: `π_t(((s_j, a_j)_{j<t}, s_t); ·)`, a probability on actions. -/
abbrev RPlan (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] :=
  (t : ℕ) → Kernel ((Fin t → S × A) × S) A

/-- Feasibility of a randomized plan (Miao, p. 142): `π_t(h_t)(Γ(s_t)) = 1`. -/
def IsFeasibleR (M : MDP S A) (π : RPlan S A) : Prop :=
  (∀ s, MeasurableSet (M.Γ s)) ∧ ∀ t h s, π t (h, s) (M.Γ s) = 1

/-- The kernel of the next state: `P₀` at date `0`, `P_t(s_{t−1}, a_{t−1}; ·)` after. -/
noncomputable def nextStateK (M : MDP S A) (P₀ : Measure S) :
    (t : ℕ) → Kernel (Fin t → S × A) S
  | 0 => Kernel.const _ P₀
  | t + 1 => (M.P t).comap (fun h => h (Fin.last t)) (measurable_pi_apply _)

/-- `μ_t(ds₀, da₀, …, ds_{t−1}, da_{t−1}; π)` (Miao, p. 143). -/
noncomputable def rmu (M : MDP S A) (P₀ : Measure S) (π : RPlan S A) :
    (t : ℕ) → Measure (Fin t → S × A)
  | 0 => Measure.dirac Fin.elim0
  | t + 1 => ((rmu M P₀ π t) ⊗ₘ (nextStateK M P₀ t ⊗ₖ π t)).map
      fun p => (Fin.snoc p.1 p.2 : Fin (t + 1) → S × A)

/-- Miao, p. 143: `μ_t(·; π)` is a probability measure. -/
theorem isProbabilityMeasure_rmu (M : MDP S A) (hP : M.IsMarkov) {P₀ : Measure S}
    [IsProbabilityMeasure P₀] {π : RPlan S A} (hπ : ∀ t, IsMarkovKernel (π t)) (t : ℕ) :
    IsProbabilityMeasure (rmu M P₀ π t) := by
  induction t with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  | succ t ih =>
    have hν : IsMarkovKernel (nextStateK M P₀ t) := by
      cases t with
      | zero => exact inferInstanceAs (IsMarkovKernel (Kernel.const _ _))
      | succ t =>
        have := hP t
        exact inferInstanceAs (IsMarkovKernel (Kernel.comap (M.P t)
          (fun h : Fin (t + 1) → S × A => h (Fin.last t)) (measurable_pi_apply _)))
    have := hπ t
    exact inferInstanceAs (IsProbabilityMeasure (Measure.map _ _))

/-- The states `(s₁, …, s_t)` of a history `((s_j, a_j)_{j<t}, s_t)` (the deterministic plans of
Definition 5.1.1 depend only on these, `s₀` being known). -/
def statesOf : (t : ℕ) → (Fin t → S × A) → S → Fin t → S
  | 0, _, _ => Fin.elim0
  | t + 1, h, s => Fin.snoc (fun j : Fin t => (h j.succ).1) s

theorem measurable_statesOf (t : ℕ) :
    Measurable fun p : (Fin t → S × A) × S => statesOf t p.1 p.2 := by
  cases t with
  | zero => exact measurable_const
  | succ t =>
    exact (measurable_snoc t).comp ((measurable_pi_iff.2 fun j =>
      ((measurable_pi_apply _).comp measurable_fst).fst).prodMk measurable_snd)

/-- A deterministic plan as a randomized plan: `π_t(h_t) = δ_{π_t(s₁, …, s_t)}`. -/
noncomputable def detRPlan (π : Plan S A) (hπ : ∀ t, Measurable (π t)) : RPlan S A :=
  fun t => Kernel.deterministic (fun p => π t (statesOf t p.1 p.2))
    ((hπ t).comp (measurable_statesOf t))

omit [MeasurableSpace S] [MeasurableSpace A] in
theorem lastState_statesOf (s₀ : S) (t : ℕ) (h : Fin t → S × A) (s : S) :
    lastState s₀ (statesOf t h s) = if t = 0 then s₀ else s := by
  cases t with
  | zero => rfl
  | succ t => simp [statesOf, lastState_snoc]

/-- Miao, p. 142: a deterministic plan is a feasible randomized plan exactly when it is a
feasible plan (here for `t ≥ 1`, and `π₀ ∈ Γ(s₀)` at `t = 0` when `P₀ = δ_{s₀}`): point masses
satisfy `δ_a(Γ(s)) = 1 ↔ a ∈ Γ(s)`. -/
theorem detRPlan_feasible_iff (M : MDP S A) (hΓ : ∀ s, MeasurableSet (M.Γ s)) (π : Plan S A)
    (hπ : ∀ t, Measurable (π t)) :
    IsFeasibleR M (detRPlan π hπ) ↔
      ∀ t (h : Fin t → S × A) s, π t (statesOf t h s) ∈ M.Γ s := by
  simp only [IsFeasibleR, detRPlan, hΓ, implies_true, true_and]
  refine forall_congr' fun t => forall_congr' fun h => forall_congr' fun s => ?_
  rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (hΓ s)]
  simp [Set.indicator]

end Miao.MarkovDecisionProcesses
