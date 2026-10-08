/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The value of information: Blackwell's sufficiency theorem

Blackwell (1951, 1953); Marschak and Miyasawa (1968).

A state `θ ∈ Θ` has prior `π`. An **experiment** `P(θ, y)` gives the probability of signal `y` in
state `θ`. A **garbling** is a Markov matrix `M(y, y')`, and `PM` is the experiment that reports
`y'` drawn from `M(y, ·)`. A decision problem is a finite set of actions `A` and a payoff
`u(a, θ)`; with signal `y` the agent maximizes `∑_θ π(θ)P(θ, y)u(a, θ)`, which is the posterior
expected payoff times the probability of `y`, so the value of the experiment is
`V_u(P) = ∑_y max_a ∑_θ π(θ)P(θ, y)u(a, θ)` — no division by signal probabilities is needed.

* `value_garble_le` (**Blackwell**): garbling never helps, `V_u(PM) ≤ V_u(P)`, in every decision
  problem.
* `sublinear_garble_le`: more generally, `∑_{y'} Φ(μ_{PM}(y')) ≤ ∑_y Φ(μ_P(y))` for every sublinear
  `Φ` of the unnormalized posteriors `μ_P(y) = π(·)P(·, y)`: the posterior distribution of `P` is a
  mean-preserving spread of that of `PM`. Decision values are the case
  `Φ(μ) = max_a ∑_θ μ(θ)u(a, θ)`.
* `value_noInfo_le`, `value_le_perfect`: information has nonnegative value, and no experiment beats
  observing the state.
-/

open Finset

namespace DPExtensions.ValueOfInformation

variable {Θ Y Y' A : Type*} [Fintype Θ] [Fintype Y] [Fintype Y'] [Fintype A] [Nonempty A]

/-- A Markov matrix. -/
def IsStochastic {Y Y' : Type*} [Fintype Y'] (M : Y → Y' → ℝ) : Prop :=
  (∀ y y', 0 ≤ M y y') ∧ ∀ y, ∑ y', M y y' = 1

/-- The garbled experiment `PM`. -/
def garble (P : Θ → Y → ℝ) (M : Y → Y' → ℝ) (θ : Θ) (y' : Y') : ℝ := ∑ y, P θ y * M y y'

/-- The unnormalized posterior after signal `y`, `μ_P(y)(θ) = π(θ)P(θ, y)`. -/
def joint (π : Θ → ℝ) (P : Θ → Y → ℝ) (y : Y) (θ : Θ) : ℝ := π θ * P θ y

/-- The expected payoff of action `a` jointly with signal `y`. -/
def payoff (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) (y : Y) (a : A) : ℝ :=
  ∑ θ, π θ * P θ y * u a θ

/-- The value of the experiment `P` in the decision problem `u`. -/
noncomputable def value (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) : ℝ :=
  ∑ y, univ.sup' univ_nonempty (payoff π u P y)

omit [Fintype Y'] [Fintype A] [Nonempty A] in
theorem payoff_garble (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) (M : Y → Y' → ℝ) (y' : Y')
    (a : A) : payoff π u (garble P M) y' a = ∑ y, M y y' * payoff π u P y a := by
  simp only [payoff, garble, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun y _ => sum_congr rfl fun θ _ => by ring

omit [Fintype Y'] in
/-- **Blackwell's theorem (sufficiency)**: garbling an experiment never raises its value. -/
theorem value_garble_le (π : Θ → ℝ) (u : A → Θ → ℝ) (P : Θ → Y → ℝ) {M : Y → Y' → ℝ}
    [Fintype Y'] (hM : IsStochastic M) : value π u (garble P M) ≤ value π u P := by
  simp only [value]
  calc ∑ y', univ.sup' univ_nonempty (payoff π u (garble P M) y')
      ≤ ∑ y', ∑ y, M y y' * univ.sup' univ_nonempty (payoff π u P y) := by
        refine sum_le_sum fun y' _ => sup'_le _ _ fun a _ => ?_
        rw [payoff_garble]
        exact sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (le_sup' (payoff π u P y) (mem_univ a)) (hM.1 y y')
    _ = ∑ y, univ.sup' univ_nonempty (payoff π u P y) := by
        rw [sum_comm]
        exact sum_congr rfl fun y _ => by rw [← sum_mul, hM.2 y, one_mul]

/-- A sublinear function: subadditive and positively homogeneous. -/
def IsSublinear (Φ : (Θ → ℝ) → ℝ) : Prop :=
  (∀ v w, Φ (v + w) ≤ Φ v + Φ w) ∧ ∀ (c : ℝ) v, 0 ≤ c → Φ (c • v) = c * Φ v

omit [Fintype Θ] in
theorem IsSublinear.sum_le {Φ : (Θ → ℝ) → ℝ} (hΦ : IsSublinear Φ) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (v : ι → Θ → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) :
    Φ (∑ i ∈ s, c i • v i) ≤ ∑ i ∈ s, c i * Φ (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hΦ.2 0 0 le_rfl
    rw [smul_zero, zero_mul] at h
    simp [h]
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi]
    refine (hΦ.1 _ _).trans ?_
    rw [hΦ.2 _ _ (hc i (mem_insert_self i s))]
    exact add_le_add le_rfl (ih fun j hj => hc j (mem_insert_of_mem hj))

omit [Fintype Θ] [Fintype Y'] in
theorem joint_garble (π : Θ → ℝ) (P : Θ → Y → ℝ) (M : Y → Y' → ℝ) (y' : Y') :
    joint π (garble P M) y' = ∑ y, M y y' • joint π P y := by
  funext θ
  simp only [joint, garble, mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_congr rfl fun y _ => by ring

omit [Fintype Θ] [Fintype Y'] in
/-- **Garbling contracts posteriors**: for every sublinear `Φ`,
`∑_{y'} Φ(μ_{PM}(y')) ≤ ∑_y Φ(μ_P(y))`. -/
theorem sublinear_garble_le (π : Θ → ℝ) (P : Θ → Y → ℝ) {M : Y → Y' → ℝ} [Fintype Y']
    (hM : IsStochastic M) {Φ : (Θ → ℝ) → ℝ} (hΦ : IsSublinear Φ) :
    ∑ y', Φ (joint π (garble P M) y') ≤ ∑ y, Φ (joint π P y) := by
  calc ∑ y', Φ (joint π (garble P M) y') ≤ ∑ y', ∑ y, M y y' * Φ (joint π P y) := by
        refine sum_le_sum fun y' _ => ?_
        rw [joint_garble]
        exact hΦ.sum_le _ _ _ fun y _ => hM.1 y y'
    _ = ∑ y, Φ (joint π P y) := by
        rw [sum_comm]
        exact sum_congr rfl fun y _ => by rw [← sum_mul, hM.2 y, one_mul]

/-- The decision value `Φ_u(μ) = max_a ∑_θ μ(θ)u(a, θ)` is sublinear, and `V_u(P)` is
`∑_y Φ_u(μ_P(y))`. -/
theorem decisionValue_sublinear (u : A → Θ → ℝ) :
    IsSublinear fun μ : Θ → ℝ => univ.sup' univ_nonempty fun a => ∑ θ, μ θ * u a θ := by
  refine ⟨fun v w => sup'_le _ _ fun a _ => ?_, fun c v hc => ?_⟩
  · simp only [Pi.add_apply, add_mul, sum_add_distrib]
    exact add_le_add (le_sup' (fun a => ∑ θ, v θ * u a θ) (mem_univ a))
      (le_sup' (fun a => ∑ θ, w θ * u a θ) (mem_univ a))
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
    exact (Finset.mul₀_sup' hc _ _ _).symm

/-- The uninformative experiment: a single signal. -/
def noInfo (_ : Θ) (_ : Unit) : ℝ := 1

omit [Fintype Y] in
/-- With a single signal, the value is `max_a ∑_θ π(θ)u(a, θ)`. -/
theorem value_noInfo (π : Θ → ℝ) (u : A → Θ → ℝ) :
    value π u (noInfo (Θ := Θ)) = univ.sup' univ_nonempty fun a => ∑ θ, π θ * u a θ := by
  simp only [value, Finset.univ_unique, Finset.sum_singleton]
  congr 1
  funext a
  simp [payoff, noInfo]

/-- **Information has nonnegative value.** -/
theorem value_noInfo_le (π : Θ → ℝ) (u : A → Θ → ℝ) {P : Θ → Y → ℝ}
    (hP : ∀ θ, ∑ y, P θ y = 1) : value π u (noInfo (Θ := Θ)) ≤ value π u P := by
  have e : (noInfo (Θ := Θ)) = garble P fun _ _ => 1 := by
    funext θ _
    simp [garble, noInfo, hP θ]
  rw [e]
  exact value_garble_le π u P ⟨fun _ _ => zero_le_one, fun _ => by simp⟩

/-- Observing the state. -/
def perfect [DecidableEq Θ] (θ θ' : Θ) : ℝ := if θ = θ' then 1 else 0

/-- **No experiment beats observing the state**: `V_u(P) ≤ ∑_θ π(θ) max_a u(a, θ)` for
`π ≥ 0`. -/
theorem value_le_perfect {π : Θ → ℝ} (hπ : ∀ θ, 0 ≤ π θ) (u : A → Θ → ℝ)
    {P : Θ → Y → ℝ} (hP : IsStochastic P) :
    value π u P ≤ ∑ θ, π θ * univ.sup' univ_nonempty fun a => u a θ := by
  classical
  have e : P = garble perfect P := by
    funext θ y
    simp [garble, perfect]
  rw [e]
  refine (value_garble_le π u perfect hP).trans (le_of_eq ?_)
  refine sum_congr rfl fun θ _ => ?_
  have e2 : payoff π u perfect θ = fun a => π θ * u a θ := by
    funext a
    simp [payoff, perfect]
  rw [e2]
  exact (Finset.mul₀_sup' (hπ θ) _ _ _).symm

end DPExtensions.ValueOfInformation
