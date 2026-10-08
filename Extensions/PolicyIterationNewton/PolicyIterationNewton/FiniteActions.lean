/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyIterationNewton.Rates

/-!
# Finite actions: policy iteration terminates, with an explicit bound

A finite MDP — finite states, finite feasible action sets `Γ(x)` — is a `PolicyModel` whose
policies are the feasible decision rules, with the greedy selector choosing a maximizing action at
each state (`FiniteMDP.toPolicyModel`).

* `exists_gap`: some `g > 0` separates the optimal actions at `v*` from the others: every action
  that is not greedy for `v*` loses at least `g`.
* `greedy_optimal_of_near`: if `‖v − v*‖ < g/(2β + 1)`, every action greedy for `v` is greedy for
  `v*`, so the policy is optimal.
* `pi_terminates_finite`: hence policy iteration reaches `v*` exactly at step `K + 1` as soon as
  `β^K‖v* − v₀‖ < g/(2β + 1)`: the number of iterations is at most
  `1 + log((2β + 1)‖v* − v₀‖/g)/log(1/β)` — logarithmic in the initial error and in `1/g`.
-/

open Finset Filter Topology

namespace DPExtensions.PolicyIterationNewton

variable (X A : Type*) [Fintype X] in
/-- A finite Markov decision process. -/
structure FiniteMDP where
  /-- feasible actions -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- rewards -/
  r : X → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x a y, 0 ≤ P x a y
  P_sum : ∀ x a, ∑ y, P x a y = 1

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- Feasible decision rules. -/
def Pol : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

/-- The action value `Q_v(x, a) = r(x, a) + β∑_y P(x, a, y)v(y)`. -/
def Q (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ y, M.P x a y * v y

/-- A maximizing action. -/
noncomputable def greedyAct (v : X → ℝ) (x : X) : A :=
  (exists_max_image (M.Γ x) (M.Q v x) (M.Γ_nonempty x)).choose

theorem greedyAct_mem (v : X → ℝ) (x : X) : M.greedyAct v x ∈ M.Γ x :=
  (exists_max_image (M.Γ x) (M.Q v x) (M.Γ_nonempty x)).choose_spec.1

theorem greedyAct_max (v : X → ℝ) (x : X) {a : A} (ha : a ∈ M.Γ x) :
    M.Q v x a ≤ M.Q v x (M.greedyAct v x) :=
  (exists_max_image (M.Γ x) (M.Q v x) (M.Γ_nonempty x)).choose_spec.2 a ha

/-- The finite MDP as a `PolicyModel`. -/
noncomputable def toPolicyModel : PolicyModel X M.Pol where
  r σ x := M.r x (σ.1 x)
  P σ x y := M.P x (σ.1 x) y
  P_nonneg σ x y := M.P_nonneg x (σ.1 x) y
  P_sum σ x := M.P_sum x (σ.1 x)
  β := M.β
  β_nonneg := M.β_nonneg
  β_lt_one := M.β_lt_one
  greedy v := ⟨M.greedyAct v, M.greedyAct_mem v⟩
  greedy_spec v σ x := M.greedyAct_max v x (σ.2 x)

theorem Tσ_eq (σ : M.Pol) (v : X → ℝ) (x : X) :
    M.toPolicyModel.Tσ σ v x = M.Q v x (σ.1 x) := rfl

theorem vstar_eq (x : X) :
    M.toPolicyModel.vstar x = M.Q M.toPolicyModel.vstar x (M.greedyAct M.toPolicyModel.vstar x) :=
  (congrFun M.toPolicyModel.T_vstar x).symm

theorem abs_Q_sub_le (v w : X → ℝ) (x : X) (a : A) :
    |M.Q v x a - M.Q w x a| ≤ M.β * ‖v - w‖ := by
  have e : M.Q v x a - M.Q w x a = M.β * ∑ y, M.P x a y * (v y - w y) := by
    simp only [Q, mul_sub, sum_sub_distrib]
    ring
  rw [e, abs_mul, abs_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ M.β_nonneg
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y, |M.P x a y * (v y - w y)| ≤ ∑ y, M.P x a y * ‖v - w‖ :=
        sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (M.P_nonneg x a y)]
          refine mul_le_mul_of_nonneg_left ?_ (M.P_nonneg x a y)
          have := norm_le_pi_norm (v - w) y
          rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    _ = ‖v - w‖ := by rw [← sum_mul, M.P_sum, one_mul]

/-- **The optimality gap**: some `g > 0` such that every feasible action that is not greedy for
`v*` is worse than the greedy ones by at least `g`. -/
theorem exists_gap : ∃ g > 0, ∀ x, ∀ a ∈ M.Γ x,
    M.Q M.toPolicyModel.vstar x a < M.toPolicyModel.vstar x →
      M.Q M.toPolicyModel.vstar x a ≤ M.toPolicyModel.vstar x - g := by
  classical
  set vs := M.toPolicyModel.vstar
  set S : Finset (X × A) := univ.biUnion fun x =>
    ((M.Γ x).filter fun a => M.Q vs x a < vs x).image fun a => (x, a)
  have hmem : ∀ x, ∀ a ∈ M.Γ x, M.Q vs x a < vs x → (x, a) ∈ S := fun x a ha hlt => by
    simp only [S, mem_biUnion, mem_univ, true_and, mem_image, mem_filter]
    exact ⟨x, a, ⟨ha, hlt⟩, rfl⟩
  have hS : ∀ p ∈ S, M.Q vs p.1 p.2 < vs p.1 := fun p hp => by
    simp only [S, mem_biUnion, mem_univ, true_and, mem_image, mem_filter] at hp
    obtain ⟨x, a, ⟨_, hlt⟩, rfl⟩ := hp
    exact hlt
  rcases S.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun x a ha hlt => ?_⟩
    have := hmem x a ha hlt
    rw [hE] at this
    exact absurd this (notMem_empty _)
  · obtain ⟨p0, hp0, hmin⟩ := exists_min_image S (fun p => vs p.1 - M.Q vs p.1 p.2) hne
    refine ⟨vs p0.1 - M.Q vs p0.1 p0.2, sub_pos.2 (hS p0 hp0), fun x a ha hlt => ?_⟩
    have := hmin (x, a) (hmem x a ha hlt)
    simp only at this
    linarith

/-- **Greedy policies near `v*` are optimal**: if every non-greedy action at `v*` loses at least
`g`, and `‖v − v*‖ < g/(2β + 1)`, then the policy greedy for `v` satisfies `T_σv* = v*`. -/
theorem greedy_optimal_of_near {g : ℝ}
    (hgap : ∀ x, ∀ a ∈ M.Γ x, M.Q M.toPolicyModel.vstar x a < M.toPolicyModel.vstar x →
      M.Q M.toPolicyModel.vstar x a ≤ M.toPolicyModel.vstar x - g)
    (v : X → ℝ) (hv : ‖v - M.toPolicyModel.vstar‖ < g / (2 * M.β + 1)) :
    M.toPolicyModel.Tσ (M.toPolicyModel.greedy v) M.toPolicyModel.vstar =
      M.toPolicyModel.vstar := by
  set vs := M.toPolicyModel.vstar
  have hβ0 := M.β_nonneg
  have h2β : 2 * M.β * ‖v - vs‖ < g := by
    have h1 : 0 < 2 * M.β + 1 := by linarith
    rw [lt_div_iff₀ h1] at hv
    nlinarith [norm_nonneg (v - vs)]
  funext x
  rw [Tσ_eq]
  change M.Q vs x (M.greedyAct v x) = vs x
  set a := M.greedyAct v x
  set as := M.greedyAct vs x
  have hmax := M.greedyAct_max v x (M.greedyAct_mem vs x)
  have h1 := abs_le.1 (M.abs_Q_sub_le v vs x a)
  have h2 := abs_le.1 (M.abs_Q_sub_le v vs x as)
  have hvs : vs x = M.Q vs x as := M.vstar_eq x
  have hle : M.Q vs x a ≤ vs x := by
    rw [hvs]
    exact M.greedyAct_max vs x (M.greedyAct_mem v x)
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have := hgap x a (M.greedyAct_mem v x) hlt
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Policy iteration terminates in a finite MDP**, at step `K + 1` as soon as
`β^K‖v* − v₀‖ < g/(2β + 1)`. -/
theorem pi_terminates_finite {g : ℝ}
    (hgap : ∀ x, ∀ a ∈ M.Γ x, M.Q M.toPolicyModel.vstar x a < M.toPolicyModel.vstar x →
      M.Q M.toPolicyModel.vstar x a ≤ M.toPolicyModel.vstar x - g)
    (σ₀ : M.Pol) {K : ℕ}
    (hK : M.β ^ K * ‖M.toPolicyModel.vstar - M.toPolicyModel.piValue σ₀ 0‖ <
      g / (2 * M.β + 1)) :
    ∀ k, K + 1 ≤ k → M.toPolicyModel.piValue σ₀ k = M.toPolicyModel.vstar :=
  M.toPolicyModel.pi_terminates (fun v hv => M.greedy_optimal_of_near hgap v hv) σ₀ hK

/-- In a finite MDP, policy iteration reaches `v*` after finitely many steps. -/
theorem exists_pi_terminates_finite (σ₀ : M.Pol) :
    ∃ K, ∀ k, K ≤ k → M.toPolicyModel.piValue σ₀ k = M.toPolicyModel.vstar := by
  obtain ⟨g, hg, hgap⟩ := M.exists_gap
  exact M.toPolicyModel.exists_pi_terminates (div_pos hg (by linarith [M.β_nonneg]))
    (fun v hv => M.greedy_optimal_of_near hgap v hv) σ₀

end FiniteMDP

end DPExtensions.PolicyIterationNewton
