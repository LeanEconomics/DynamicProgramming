/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Problem
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi

/-!
# The value function, the Bellman operator and optimal policies

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.1.4–§4.1.1.7
(pp. 108–111).

The value function is `v* = ⋁_σ v_σ`, (4.6), the pointwise maximum over the
finitely many policies. The Bellman operator `Tv = e ∨ (c + βPv)`, (4.8), is an
order-preserving self-map (Exercise 4.1.4) and a contraction of modulus `β`
(Proposition 4.1.2 (i), Exercise 4.1.5); its unique fixed point is `v*`
(Proposition 4.1.2 (ii)), so `v*` is the unique solution of the Bellman
equation (4.7) and value function iteration converges to it. A policy is
optimal, (4.1), iff it is `v*`-greedy, (4.9) (Proposition 4.1.3, which the book
proves in Chapter 5 in a general setting; the proof here is direct).
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

namespace StoppingProblem

variable {X : Type*} [Fintype X] (S : StoppingProblem X)

/-- The Bellman operator (4.8): `(Tv)(x) = max{e(x), c(x) + β ∑ v(x')P(x, x')}`. -/
def T (v : X → ℝ) : X → ℝ := fun x => max (S.e x) (S.cont v x)

theorem T_apply (v : X → ℝ) (x : X) :
    S.T v x = max (S.e x) (S.c x + S.β * ∑ x', v x' * S.P x x') := by
  rw [T, cont_apply]

/-- Exercise 4.1.4 (p. 109): `T` is an order-preserving self-map on `ℝ^X`. -/
theorem T_monotone : Monotone S.T := by
  intro v v' hvv' x
  exact max_le_max le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (S.P_markov.mulVec_le_mulVec hvv' x) S.β_pos.le))

/-- `|(Tv)(x) − (Tv')(x)| ≤ β‖v − v'‖`, by `|α ∨ x − α ∨ y| ≤ |x − y|`. -/
theorem abs_T_sub_le (v v' : X → ℝ) (x : X) : |S.T v x - S.T v' x| ≤ S.β * ‖v - v'‖ := by
  unfold T cont
  rw [max_comm (S.e x), max_comm (S.e x)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_pos.le]
  exact mul_le_mul_of_nonneg_left (S.P_markov.abs_mulVec_sub_le v v' x) S.β_pos.le

/-- **Proposition 4.1.2 (i)** (p. 109, Exercise 4.1.5): `T` is a contraction of modulus `β` on
`ℝ^X` under the supremum norm. -/
theorem isContractionOn_T : IsContractionOn S.T Set.univ S.β where
  mapsTo := Set.mapsTo_univ _ _
  nonneg := S.β_pos.le
  lt_one := S.β_lt_one
  norm_sub_le v _ v' _ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg S.β_pos.le (norm_nonneg _))]
    intro x
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact S.abs_T_sub_le v v' x

/-- `T_σ v ≤ Tv` for every policy `σ` and every `v` (p. 110). -/
theorem Tσ_le_T (σ : Policy X) (v : X → ℝ) : S.Tσ σ v ≤ S.T v := by
  intro x
  unfold Tσ T
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- A `v`-greedy policy (4.9), p. 110: `σ(x)` maximises `a e(x) + (1 − a)[c(x) + β(Pv)(x)]` over
`a ∈ {0, 1}`: stopping is chosen only if `e(x) ≥ c(x) + β(Pv)(x)`, continuing only if `≤`. -/
def IsGreedy (v : X → ℝ) (σ : Policy X) : Prop :=
  ∀ x, (σ x = true → S.cont v x ≤ S.e x) ∧ (σ x = false → S.e x ≤ S.cont v x)

/-- The greedy policy that stops on ties: `σ(x) = 1{e(x) ≥ c(x) + β(Pv)(x)}`. -/
noncomputable def greedy (v : X → ℝ) : Policy X := fun x => decide (S.cont v x ≤ S.e x)

theorem isGreedy_greedy (v : X → ℝ) : S.IsGreedy v (S.greedy v) := fun x => by
  simp only [greedy, decide_eq_true_iff, decide_eq_false_iff_not]
  exact ⟨id, fun h => (not_le.1 h).le⟩

/-- For a `v`-greedy `σ`, `T_σ v = Tv` (p. 110). -/
theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : Policy X} (hσ : S.IsGreedy v σ) :
    S.Tσ σ v = S.T v := by
  funext x
  unfold Tσ T
  rcases Bool.eq_false_or_eq_true (σ x) with h | h
  · simp only [h, ↓reduceIte]
    exact (max_eq_left ((hσ x).1 h)).symm
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right ((hσ x).2 h)).symm

variable [DecidableEq X]

/-- The value function (4.6), p. 108: `v*(x) = max_σ v_σ(x)`. -/
noncomputable def vstar : X → ℝ := fun x => univ.sup' univ_nonempty fun σ : Policy X => S.vσ σ x

/-- `v_σ ≤ v*` for every policy. -/
theorem vσ_le_vstar (σ : Policy X) : S.vσ σ ≤ S.vstar := fun x =>
  Finset.le_sup' (fun σ : Policy X => S.vσ σ x) (mem_univ σ)

/-- `v*(x)` is attained by some policy. -/
theorem exists_vσ_eq_vstar (x : X) : ∃ σ : Policy X, S.vσ σ x = S.vstar x := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup' univ_nonempty fun σ : Policy X => S.vσ σ x
  exact ⟨σ, hσ.symm⟩

/-- **Proposition 4.1.2 (ii)** (p. 109): the value function `v*` is a fixed point of `T`. -/
theorem isFixedPt_T_vstar : IsFixedPt S.T S.vstar := by
  -- the fixed point `v̄` of `T` given by Banach's theorem
  obtain ⟨vbar, -, hvbar⟩ := S.isContractionOn_T.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  -- `v̄ ≤ v*`: `v̄` is the value of its own greedy policy
  have h1 : vbar ≤ S.vstar := by
    have hfix : IsFixedPt (S.Tσ (S.greedy vbar)) vbar := by
      rw [IsFixedPt, S.Tσ_eq_T_of_isGreedy (S.isGreedy_greedy vbar)]
      exact hvbar
    rw [S.eq_vσ_of_isFixedPt _ hfix]
    exact S.vσ_le_vstar _
  -- `v* ≤ v̄`: each `v_σ ≤ v̄` by Proposition 2.2.7, since `T_σ ≤ T`
  have h2 : S.vstar ≤ vbar := by
    intro x
    refine Finset.sup'_le _ _ fun σ _ => ?_
    exact fixedPt_le_of_le (S.Tσ_le_T σ) S.T_monotone (S.isFixedPt_vσ σ)
      (S.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ _) (Set.mem_univ _) hvbar) x
  have : S.vstar = vbar := le_antisymm h2 h1
  rw [this]
  exact hvbar

/-- Proposition 4.1.2 (ii): `v*` is the only fixed point of `T` in `ℝ^X`. -/
theorem eq_vstar_of_isFixedPt {v : X → ℝ} (hv : IsFixedPt S.T v) : v = S.vstar :=
  S.isContractionOn_T.fixedPt_unique (Set.mem_univ v) (Set.mem_univ _) hv S.isFixedPt_T_vstar

/-- The Bellman equation (4.7), p. 109: `v*(x) = max{e(x), c(x) + β ∑ v*(x')P(x, x')}`, with `v*`
its unique solution. -/
theorem bellman_equation (x : X) :
    S.vstar x = max (S.e x) (S.c x + S.β * ∑ x', S.vstar x' * S.P x x') := by
  have := congrFun S.isFixedPt_T_vstar.eq x
  rw [← this, T_apply]

/-- Value function iteration (§4.1.1.7, p. 111): `Tᵏv → v*` from every `v ∈ ℝ^X`, at rate `βᵏ`. -/
theorem tendsto_iterate_T (v : X → ℝ) : Tendsto (fun k : ℕ => S.T^[k] v) atTop (𝓝 S.vstar) :=
  S.isContractionOn_T.tendsto_iterate_fixedPt (Set.mem_univ v) (Set.mem_univ _) S.isFixedPt_T_vstar

theorem norm_iterate_T_sub_vstar_le (v : X → ℝ) (k : ℕ) :
    ‖S.T^[k] v - S.vstar‖ ≤ S.β ^ k * ‖v - S.vstar‖ :=
  S.isContractionOn_T.norm_iterate_sub_fixedPt_le (Set.mem_univ v) (Set.mem_univ _)
    S.isFixedPt_T_vstar k

omit [DecidableEq X] in
/-- `T` is globally stable on `ℝ^X` (p. 110). -/
theorem globallyStable_T : GloballyStable S.T := S.isContractionOn_T.globallyStable_univ

/-! ### Optimal policies (§4.1.1.6) -/

/-- An optimal policy (4.1), p. 107: `v_σ*(x) = max_σ v_σ(x)` for all `x`. -/
def IsOptimal (σ : Policy X) : Prop := ∀ (σ' : Policy X) (x : X), S.vσ σ' x ≤ S.vσ σ x

/-- `σ` is optimal iff `v_σ = v*`. -/
theorem isOptimal_iff_vσ_eq (σ : Policy X) : S.IsOptimal σ ↔ S.vσ σ = S.vstar := by
  constructor
  · intro h
    funext x
    refine le_antisymm (S.vσ_le_vstar σ x) ?_
    exact Finset.sup'_le _ _ fun σ' _ => h σ' x
  · intro h σ' x
    rw [h]
    exact S.vσ_le_vstar σ' x

/-- **Proposition 4.1.3** (Bellman's principle of optimality, p. 110): a policy is optimal iff it is
`v*`-greedy. -/
theorem isOptimal_iff_isGreedy (σ : Policy X) : S.IsOptimal σ ↔ S.IsGreedy S.vstar σ := by
  rw [isOptimal_iff_vσ_eq]
  constructor
  · intro h x
    -- `v* = T_σ v*` pointwise, and `v* = T v*`
    have h1 : S.vstar x = S.Tσ σ S.vstar x := by
      rw [← h]
      exact (congrFun (S.isFixedPt_vσ σ).eq x).symm
    have h2 : S.vstar x = max (S.e x) (S.cont S.vstar x) := (congrFun S.isFixedPt_T_vstar.eq x).symm
    constructor
    · intro hσ
      have h1' : S.vstar x = S.e x := by
        rw [h1, Tσ]
        simp [hσ]
      exact max_eq_left_iff.1 (h1'.symm.trans h2).symm
    · intro hσ
      have h1' : S.vstar x = S.cont S.vstar x := by
        rw [h1, Tσ]
        simp [hσ]
      exact max_eq_right_iff.1 (h1'.symm.trans h2).symm
  · intro h
    have hfix : IsFixedPt (S.Tσ σ) S.vstar := by
      rw [IsFixedPt, S.Tσ_eq_T_of_isGreedy h]
      exact S.isFixedPt_T_vstar
    exact (S.eq_vσ_of_isFixedPt σ hfix).symm

/-- An optimal policy exists: the `v*`-greedy policy that stops on ties. -/
theorem isOptimal_greedy_vstar : S.IsOptimal (S.greedy S.vstar) :=
  (S.isOptimal_iff_isGreedy _).2 (S.isGreedy_greedy _)

end StoppingProblem

end SargentStachurski.OptimalStopping
