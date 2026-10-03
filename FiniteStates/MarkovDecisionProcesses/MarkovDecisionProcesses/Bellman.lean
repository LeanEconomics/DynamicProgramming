/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDecisionProcesses.MDP
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi

/-!
# Optimality: the Bellman operator, greedy policies and the algorithms

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §5.1.3.2–§5.1.4
(pp. 136–145).

The value function is `v* = ⋁_σ v_σ` over the finitely many feasible policies,
(5.21); `σ` is optimal if `v_σ = v*`. The Bellman operator (5.24) maximises the
action value over `Γ(x)`; a `v`-greedy policy attains that maximum, (5.22).
Exercises 5.1.10–5.1.12: the family `{T_σ v}` has least and greatest elements,
greedy policies exist and are exactly those with `T_σ v = Tv`, `T = ⋁_σ T_σ`,
and `T` is a contraction of modulus `β`. Proposition 5.1.1: `v*` is the unique
solution of the Bellman equation, `Tᵏv → v*`, Bellman's principle of
optimality holds, and an optimal policy exists (Exercise 5.1.13).

For the algorithms: Lemma 5.1.2 (`βP_σ` is a subgradient of `T` at `v` for a
`v`-greedy `σ`), the identity that makes Howard policy iteration a Newton step,
the monotone improvement step of HPI with its termination criterion, and the
observations that optimistic policy iteration with `m = 1` is VFI and that its
inner iterates converge to `v_σ` as `m → ∞`.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.MarkovDecisionProcesses

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- The Bellman operator (5.24): `(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v(x')P(x, a, x')}`. -/
noncomputable def T (v : X → ℝ) : X → ℝ := fun x => (M.Γ x).sup' (M.Γ_nonempty x) (M.B v x)

theorem T_apply (v : X → ℝ) (x : X) :
    M.T v x = (M.Γ x).sup' (M.Γ_nonempty x) fun a => M.r x a + M.β * ∑ x', v x' * M.P x a x' := rfl

/-- `B(x, a, v) ≤ (Tv)(x)` for every feasible `a`. -/
theorem B_le_T (v : X → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : M.B v x a ≤ M.T v x :=
  Finset.le_sup' (M.B v x) ha

/-- `T_σ v ≤ Tv` for every feasible policy. -/
theorem Tσ_le_T (σ : M.Policy) (v : X → ℝ) : M.Tσ σ.1 v ≤ M.T v := fun x =>
  M.B_le_T v (σ.2 x)

/-- The action value is order preserving in `v`. -/
theorem B_mono {v v' : X → ℝ} (hvv' : v ≤ v') (x : X) (a : A) : M.B v x a ≤ M.B v' x a := by
  unfold B
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_le_sum fun x' _ => ?_) M.β_pos.le)
  exact mul_le_mul_of_nonneg_right (hvv' x') (M.P_nonneg x a x')

/-- `T` is an order-preserving self-map on `ℝ^X`. -/
theorem T_monotone : Monotone M.T := by
  intro v v' hvv' x
  exact Finset.sup'_mono_fun fun a _ => M.B_mono hvv' x a

/-- `|B(x, a, v) − B(x, a, v')| ≤ β‖v − v'‖`. -/
theorem abs_B_sub_le (v v' : X → ℝ) (x : X) (a : A) : |M.B v x a - M.B v' x a| ≤ M.β * ‖v - v'‖ :=
  M.abs_Tσ_sub_le (fun _ => a) v v' x

/-- Exercise 5.1.12 (p. 137): `T` is a contraction of modulus `β` on `ℝ^X` under the supremum
norm. -/
theorem isContractionOn_T : IsContractionOn M.T Set.univ M.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := M.β_pos.le
  lt_one := M.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg M.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs, T_apply, T_apply]
    refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a _ => ?_)
    exact M.abs_B_sub_le v v' x a

/-! ### Greedy policies (5.22) -/

/-- A `v`-greedy policy (5.22), p. 136: feasible, and `σ(x)` maximises the action value over
`Γ(x)`. -/
def IsGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, M.B v x a ≤ M.B v x (σ x)

/-- A `v`-greedy policy, chosen by maximising the action value in each state. -/
noncomputable def greedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose

theorem greedy_mem (v : X → ℝ) (x : X) : M.greedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- Exercise 5.1.11 (i), p. 137: a `v`-greedy policy exists. -/
theorem isGreedy_greedy (v : X → ℝ) : M.IsGreedy v (M.greedy v) :=
  ⟨M.greedy_mem v, fun x a ha =>
    ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 a ha⟩

/-- The greedy policy as an element of `Σ`. -/
noncomputable def greedyPolicy (v : X → ℝ) : M.Policy := ⟨M.greedy v, M.greedy_mem v⟩

/-- Exercise 5.1.11 (ii), p. 137: a feasible `σ` is `v`-greedy iff `T_σ v = Tv`. -/
theorem isGreedy_iff_Tσ_eq_T (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ.1 ↔ M.Tσ σ.1 v = M.T v := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact le_antisymm (M.B_le_T v (σ.2 x)) (Finset.sup'_le _ _ fun a ha => h x a ha)
  · intro h
    refine ⟨σ.2, fun x a ha => ?_⟩
    have := congrFun h x
    rw [Tσ] at this
    rw [this]
    exact M.B_le_T v ha

/-- For a `v`-greedy `σ`, `T_σ v = Tv`. -/
theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) : M.Tσ σ v = M.T v :=
  (M.isGreedy_iff_Tσ_eq_T v ⟨σ, hσ.1⟩).1 hσ

/-- Exercise 5.1.11 (iii), p. 137: `(Tv)(x) = max_σ (T_σ v)(x)`, i.e. `T = ⋁_σ T_σ`. -/
theorem T_apply_eq_sup' [DecidableEq X] [DecidableEq A] (v : X → ℝ) (x : X) :
    M.T v x =
      univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.Tσ σ.1 v x := by
  apply le_antisymm
  · have h := congrFun (M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy v)) x
    rw [← h]
    exact Finset.le_sup' (fun σ : M.Policy => M.Tσ σ.1 v x) (mem_univ (M.greedyPolicy v))
  · exact Finset.sup'_le _ _ fun σ _ => M.Tσ_le_T σ v x

/-- Exercise 5.1.10 (p. 136), greatest element: `Tv` is the greatest element of `{T_σ v}_σ`. -/
theorem isGreatest_T (v : X → ℝ) : IsGreatest (Set.range fun σ : M.Policy => M.Tσ σ.1 v) (M.T v) :=
  ⟨⟨M.greedyPolicy v, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy v)⟩, by
    rintro _ ⟨σ, rfl⟩
    exact M.Tσ_le_T σ v⟩

/-- The policy that minimises the action value in each state. -/
noncomputable def antiGreedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose

theorem antiGreedy_mem (v : X → ℝ) (x : X) : M.antiGreedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- Exercise 5.1.10 (p. 136), least element: `{T_σ v}_σ` has a least element, the value of the
policy that minimises the action value in each state. -/
theorem isLeast_Tσ_antiGreedy (v : X → ℝ) :
    IsLeast (Set.range fun σ : M.Policy => M.Tσ σ.1 v) (M.Tσ (M.antiGreedy v) v) :=
  ⟨⟨⟨M.antiGreedy v, M.antiGreedy_mem v⟩, rfl⟩, by
    rintro _ ⟨σ, rfl⟩ x
    exact ((M.Γ x).exists_min_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 _ (σ.2 x)⟩

/-! ### The value function and Proposition 5.1.1 -/

variable [DecidableEq X] [DecidableEq A]

/-- The value function (5.21), p. 136: `v*(x) = max_{σ ∈ Σ} v_σ(x)`. -/
noncomputable def vstar : X → ℝ := fun x =>
  univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.vσ σ.1 x

/-- `v_σ ≤ v*` for every feasible policy. -/
theorem vσ_le_vstar (σ : M.Policy) : M.vσ σ.1 ≤ M.vstar := fun x =>
  Finset.le_sup' (fun σ : M.Policy => M.vσ σ.1 x) (mem_univ σ)

/-- An optimal policy (p. 136): a feasible `σ` with `v_σ = v*`. -/
def IsOptimal (σ : X → A) : Prop := M.IsFeasible σ ∧ M.vσ σ = M.vstar

/-- **Proposition 5.1.1 (i)**, existence half (pp. 137–138): `v*` is a fixed point of `T`. -/
theorem isFixedPt_T_vstar : IsFixedPt M.T M.vstar := by
  obtain ⟨vbar, -, hvbar⟩ := M.isContractionOn_T.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  -- `v̄ ≤ v*`: `v̄` is the value of its own greedy policy
  have h1 : vbar ≤ M.vstar := by
    have hfix : IsFixedPt (M.Tσ (M.greedy vbar)) vbar := by
      rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy (M.isGreedy_greedy vbar)]
      exact hvbar
    rw [M.eq_vσ_of_isFixedPt _ hfix]
    exact M.vσ_le_vstar (M.greedyPolicy vbar)
  -- `v* ≤ v̄`: each `v_σ ≤ v̄` by Proposition 2.2.7, since `T_σ ≤ T`
  have h2 : M.vstar ≤ vbar := by
    intro x
    refine Finset.sup'_le _ _ fun σ _ => ?_
    exact fixedPt_le_of_le (M.Tσ_le_T σ) M.T_monotone (M.isFixedPt_vσ σ.1)
      (M.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ _) (Set.mem_univ _) hvbar) x
  have : M.vstar = vbar := le_antisymm h2 h1
  rw [this]
  exact hvbar

/-- Proposition 5.1.1 (i), uniqueness half: `v*` is the only fixed point of `T` in `ℝ^X`. -/
theorem eq_vstar_of_isFixedPt {v : X → ℝ} (hv : IsFixedPt M.T v) : v = M.vstar :=
  M.isContractionOn_T.fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv M.isFixedPt_T_vstar

/-- The Bellman equation (5.2): `v*(x) = max_{a ∈ Γ(x)} {r(x, a) + β ∑ v*(x')P(x, a, x')}`,
with `v*` its unique solution (Proposition 5.1.1 (i)). -/
theorem bellman_equation (x : X) :
    M.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) fun a =>
      M.r x a + M.β * ∑ x', M.vstar x' * M.P x a x' :=
  (congrFun M.isFixedPt_T_vstar.eq x).symm

/-- Proposition 5.1.1 (ii): `Tᵏv → v*` for all `v ∈ ℝ^X` (value function iteration, §5.1.4.1). -/
theorem tendsto_iterate_T (v : X → ℝ) : Tendsto (fun k : ℕ => M.T^[k] v) atTop (𝓝 M.vstar) :=
  M.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _) M.isFixedPt_T_vstar

theorem norm_iterate_T_sub_vstar_le (v : X → ℝ) (k : ℕ) :
    ‖M.T^[k] v - M.vstar‖ ≤ M.β ^ k * ‖v - M.vstar‖ :=
  M.isContractionOn_T.norm_iterate_sub_fixedPt_le (Set.mem_univ v) (Set.mem_univ _)
    M.isFixedPt_T_vstar k

omit [DecidableEq X] [DecidableEq A] in
/-- `T` is globally stable on `ℝ^X` (p. 137). -/
theorem globallyStable_T : GloballyStable M.T := M.isContractionOn_T.globallyStable_univ

/-- Optimality is `v_σ = v*` pointwise: `σ` is optimal iff it is feasible and `v_σ'(x) ≤ v_σ(x)` for
all feasible `σ'` and all `x`. -/
theorem isOptimal_iff (σ : X → A) :
    M.IsOptimal σ ↔
      M.IsFeasible σ ∧ ∀ (σ' : M.Policy) (x : X), M.vσ σ'.1 x ≤ M.vσ σ x := by
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, fun σ' x => ?_⟩
    rw [h]
    exact M.vσ_le_vstar σ' x
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, funext fun x => le_antisymm (M.vσ_le_vstar ⟨σ, hσ⟩ x) ?_⟩
    exact Finset.sup'_le _ _ fun σ' _ => h σ' x

/-- **Proposition 5.1.1 (iii)**, Bellman's principle of optimality (p. 137), via (5.25):
`σ` is optimal iff it is `v*`-greedy. -/
theorem isOptimal_iff_isGreedy (σ : X → A) : M.IsOptimal σ ↔ M.IsGreedy M.vstar σ := by
  constructor
  · rintro ⟨hσ, h⟩
    rw [M.isGreedy_iff_Tσ_eq_T M.vstar ⟨σ, hσ⟩]
    -- `T_σ v* = T_σ v_σ = v_σ = v* = Tv*`
    rw [← h, (M.isFixedPt_vσ σ).eq, h, M.isFixedPt_T_vstar.eq]
  · intro h
    refine ⟨h.1, ?_⟩
    have hfix : IsFixedPt (M.Tσ σ) M.vstar := by
      rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy h]
      exact M.isFixedPt_T_vstar
    exact (M.eq_vσ_of_isFixedPt σ hfix).symm

/-- Proposition 5.1.1 (iv), Exercise 5.1.13 (p. 139): an optimal policy exists, namely any
`v*`-greedy policy. -/
theorem isOptimal_greedy_vstar : M.IsOptimal (M.greedy M.vstar) :=
  (M.isOptimal_iff_isGreedy _).2 (M.isGreedy_greedy _)

theorem exists_isOptimal : ∃ σ : X → A, M.IsOptimal σ := ⟨_, M.isOptimal_greedy_vstar⟩

/-! ### Algorithms (§5.1.4) -/

omit [DecidableEq X] [DecidableEq A] in
/-- **Lemma 5.1.2** (p. 144): if `σ` is `v`-greedy then `βP_σ` is a subgradient of `T` at `v`:
`Tu ≥ Tv + βP_σ(u − v)` for all `u`. -/
theorem subgradient_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) (u : X → ℝ) :
    M.T v + M.β • (M.Pσ σ *ᵥ (u - v)) ≤ M.T u := by
  have h1 := M.Tσ_le_T ⟨σ, hσ.1⟩ u
  have h2 := M.Tσ_eq_T_of_isGreedy hσ
  rw [Tσ_eq] at h1 h2
  rw [← h2, mulVec_sub, smul_sub]
  intro x
  have := h1 x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  linarith

omit [DecidableEq A] in
/-- HPI as Newton's method (p. 144): for a `v`-greedy `σ`, the Newton step
`Qv = (I − βP_σ)⁻¹(Tv − βP_σ v)` equals `(I − βP_σ)⁻¹ r_σ = v_σ`, the next value in HPI. -/
theorem newton_step_eq_vσ {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (1 - M.β • M.Pσ σ)⁻¹ *ᵥ (M.T v - M.β • (M.Pσ σ *ᵥ v)) = M.vσ σ := by
  rw [← M.Tσ_eq_T_of_isGreedy hσ, Tσ_eq, add_sub_cancel_right, M.vσ_eq_inv]

omit [DecidableEq X] [DecidableEq A] in
/-- Howard policy iteration (Algorithm 5.3), the improvement step: if `σ'` is `v_σ`-greedy then
`v_σ ≤ v_σ'`, since `v_σ = T_σ v_σ ≤ Tv_σ = T_σ' v_σ` and `T_σ'ᵏ v_σ → v_σ'`. -/
theorem vσ_le_vσ_of_isGreedy {σ : X → A} (hσ : M.IsFeasible σ) {σ' : X → A}
    (hσ' : M.IsGreedy (M.vσ σ) σ') : M.vσ σ ≤ M.vσ σ' := by
  have h : M.vσ σ ≤ M.Tσ σ' (M.vσ σ) := by
    rw [M.Tσ_eq_T_of_isGreedy hσ']
    calc M.vσ σ = M.Tσ σ (M.vσ σ) := (M.isFixedPt_vσ σ).eq.symm
      _ ≤ M.T (M.vσ σ) := M.Tσ_le_T ⟨σ, hσ⟩ _
  exact le_fixedPt_of_le_apply (M.Tσ_monotone σ') h (M.tendsto_iterate_Tσ σ' _)

/-- HPI, the termination criterion (Algorithm 5.3, line 6): if `σ'` is `v_σ`-greedy and
`v_σ' = v_σ`, then `σ'` is optimal. -/
theorem isOptimal_of_hpi_fixed {σ σ' : X → A} (hσ' : M.IsGreedy (M.vσ σ) σ')
    (heq : M.vσ σ' = M.vσ σ) : M.IsOptimal σ' := by
  have hfix : IsFixedPt M.T (M.vσ σ) := by
    rw [IsFixedPt, ← M.Tσ_eq_T_of_isGreedy hσ', ← heq]
    exact (M.isFixedPt_vσ σ').eq
  refine ⟨hσ'.1, ?_⟩
  rw [heq]
  exact M.eq_vstar_of_isFixedPt hfix

omit [DecidableEq X] [DecidableEq A] in
/-- Optimistic policy iteration (Algorithm 5.4) with `m = 1` is value function iteration: for a
`v`-greedy `σ`, `T_σ v = Tv` (p. 145). -/
theorem opi_one_step_eq_vfi {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (M.Tσ σ)^[1] v = M.T v := by
  rw [iterate_one]
  exact M.Tσ_eq_T_of_isGreedy hσ

omit [DecidableEq X] [DecidableEq A] in
/-- OPI approximates HPI as `m → ∞`: `T_σᵐ v → v_σ` (p. 145). -/
theorem tendsto_opi_inner (σ : X → A) (v : X → ℝ) :
    Tendsto (fun m : ℕ => (M.Tσ σ)^[m] v) atTop (𝓝 (M.vσ σ)) :=
  M.tendsto_iterate_Tσ σ v

end MDP

end SargentStachurski.MarkovDecisionProcesses
