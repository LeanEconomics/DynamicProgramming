/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Order.Field

/-!
# Policy iteration as Newton's method

Puterman and Brumelle (1979); Howard (1960).

A finite set of states `X` and an arbitrary set of policies `Pol` (possibly infinite, e.g.
continuous actions). Each policy `σ` has a reward `r_σ` and a Markov matrix `P_σ`, and
`T_σv = r_σ + βP_σv`. A greedy selector picks, for each `v`, a policy maximizing `T_σv` at every
state; then `Tv = T_{greedy v}v` is the Bellman operator.

* `contracting_T`, `contracting_Tσ`: both are `β`-contractions for the supremum norm, with fixed
  points `v*` and `v_σ`.
* `newton_identity`: **policy iteration is Newton's method** for `F(v) = Tv − v`: with
  `σ = greedy v`, `(I − βP_σ)(v_σ − v) = Tv − v`, i.e. `v_σ = v − (DF)⁻¹F(v)` with
  `DF = βP_σ − I`.
* `vσ_le_vstar`, `le_vσ_greedy`: `v_σ ≤ v*`, and `Tv ≤ v_{greedy v}` whenever `v ≤ Tv`.
-/

open Filter Topology Finset

namespace DPExtensions.PolicyIterationNewton

variable (X Pol : Type*) [Fintype X] in
/-- A family of Markov decision rules with a greedy selector. -/
structure PolicyModel where
  /-- rewards -/
  r : Pol → X → ℝ
  /-- transition matrices -/
  P : Pol → X → X → ℝ
  P_nonneg : ∀ σ x y, 0 ≤ P σ x y
  P_sum : ∀ σ x, ∑ y, P σ x y = 1
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the greedy selector -/
  greedy : (X → ℝ) → Pol
  greedy_spec : ∀ v σ x, r σ x + β * ∑ y, P σ x y * v y ≤
    r (greedy v) x + β * ∑ y, P (greedy v) x y * v y

namespace PolicyModel

variable {X Pol : Type*} [Fintype X] (M : PolicyModel X Pol)

/-- `(P_σv)(x)`. -/
def Pv (σ : Pol) (v : X → ℝ) (x : X) : ℝ := ∑ y, M.P σ x y * v y

/-- The policy operator `T_σv = r_σ + βP_σv`. -/
def Tσ (σ : Pol) (v : X → ℝ) (x : X) : ℝ := M.r σ x + M.β * M.Pv σ v x

/-- The Bellman operator `Tv = T_{greedy v}v`. -/
def T (v : X → ℝ) : X → ℝ := M.Tσ (M.greedy v) v

theorem Tσ_le_T (σ : Pol) (v : X → ℝ) : M.Tσ σ v ≤ M.T v := fun x => M.greedy_spec v σ x

theorem Pv_sub (σ : Pol) (v w : X → ℝ) (x : X) :
    M.Pv σ v x - M.Pv σ w x = M.Pv σ (fun y => v y - w y) x := by
  simp only [Pv, ← sum_sub_distrib, mul_sub]

theorem abs_Pv_le (σ : Pol) (v : X → ℝ) (x : X) : |M.Pv σ v x| ≤ ‖v‖ := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y, |M.P σ x y * v y| ≤ ∑ y, M.P σ x y * ‖v‖ := sum_le_sum fun y _ => by
        rw [abs_mul, abs_of_nonneg (M.P_nonneg σ x y)]
        refine mul_le_mul_of_nonneg_left ?_ (M.P_nonneg σ x y)
        have := norm_le_pi_norm v y
        rwa [Real.norm_eq_abs] at this
    _ = ‖v‖ := by rw [← sum_mul, M.P_sum, one_mul]

theorem Pv_mono (σ : Pol) {v w : X → ℝ} (h : v ≤ w) : M.Pv σ v ≤ M.Pv σ w := fun x =>
  sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (M.P_nonneg σ x y)

theorem Tσ_mono (σ : Pol) : Monotone (M.Tσ σ) := fun _ _ h x =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left (M.Pv_mono σ h x) M.β_nonneg)

theorem norm_Tσ_sub_le (σ : Pol) (v w : X → ℝ) : ‖M.Tσ σ v - M.Tσ σ w‖ ≤ M.β * ‖v - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun x => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  simp only [Tσ, add_sub_add_left_eq_sub, ← mul_sub, M.Pv_sub, abs_mul,
    abs_of_nonneg M.β_nonneg]
  exact mul_le_mul_of_nonneg_left (M.abs_Pv_le σ _ x) M.β_nonneg

theorem norm_T_sub_le (v w : X → ℝ) : ‖M.T v - M.T w‖ ≤ M.β * ‖v - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun x => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  have h1 := (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).1
    (M.norm_Tσ_sub_le (M.greedy v) v w) x
  have h2 := (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).1
    (M.norm_Tσ_sub_le (M.greedy w) v w) x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff] at h1 h2
  have h3 := M.Tσ_le_T (M.greedy v) w x
  have h4 := M.Tσ_le_T (M.greedy w) v x
  simp only [T] at h3 h4 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem contracting_T : ContractingWith ⟨M.β, M.β_nonneg⟩ M.T :=
  ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_T_sub_le v w⟩

theorem contracting_Tσ (σ : Pol) : ContractingWith ⟨M.β, M.β_nonneg⟩ (M.Tσ σ) :=
  ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_Tσ_sub_le σ v w⟩

/-- The value function. -/
noncomputable def vstar : X → ℝ := ContractingWith.fixedPoint M.T M.contracting_T

/-- The value of a policy. -/
noncomputable def vσ (σ : Pol) : X → ℝ :=
  ContractingWith.fixedPoint (M.Tσ σ) (M.contracting_Tσ σ)

theorem T_vstar : M.T M.vstar = M.vstar := ContractingWith.fixedPoint_isFixedPt _

theorem Tσ_vσ (σ : Pol) : M.Tσ σ (M.vσ σ) = M.vσ σ := ContractingWith.fixedPoint_isFixedPt _

/-- `v ≤ T_σv` implies `v ≤ v_σ`. -/
theorem le_vσ_of_le (σ : Pol) {v : X → ℝ} (h : v ≤ M.Tσ σ v) : v ≤ M.vσ σ := by
  have hit : ∀ n, v ≤ (M.Tσ σ)^[n] v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact h.trans (M.Tσ_mono σ ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint (M.contracting_Tσ σ) v) hit

/-- `v_σ ≤ v*`. -/
theorem vσ_le_vstar (σ : Pol) : M.vσ σ ≤ M.vstar := by
  have h : M.vσ σ ≤ M.T (M.vσ σ) := by
    have := M.Tσ_le_T σ (M.vσ σ)
    rwa [M.Tσ_vσ] at this
  have hit : ∀ n, M.vσ σ ≤ M.T^[n] (M.vσ σ) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine h.trans (fun x => ?_)
      have h1 := M.Tσ_mono (M.greedy (M.vσ σ)) ih x
      have h2 := M.Tσ_le_T (M.greedy (M.vσ σ)) (M.T^[n] (M.vσ σ)) x
      exact h1.trans h2
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint M.contracting_T _) hit

/-- `v* = v_{greedy v*}`: the greedy policy for `v*` is optimal. -/
theorem vσ_greedy_vstar : M.vσ (M.greedy M.vstar) = M.vstar := by
  have hfix : Function.IsFixedPt (M.Tσ (M.greedy M.vstar)) M.vstar := M.T_vstar
  exact (ContractingWith.fixedPoint_unique (M.contracting_Tσ _) hfix).symm

/-- If `v ≤ Tv`, the policy greedy for `v` improves on `Tv`: `Tv ≤ v_{greedy v}`. -/
theorem le_vσ_greedy {v : X → ℝ} (h : v ≤ M.T v) : M.T v ≤ M.vσ (M.greedy v) := by
  have h1 : M.T v ≤ M.Tσ (M.greedy v) (M.T v) := M.Tσ_mono _ h
  exact (M.le_vσ_of_le _ h1)

/-- **Policy iteration is Newton's method**: with `σ = greedy v`,
`(v_σ − v) − βP_σ(v_σ − v) = Tv − v`. -/
theorem newton_identity (v : X → ℝ) (x : X) :
    (M.vσ (M.greedy v) x - v x) - M.β * M.Pv (M.greedy v) (fun y => M.vσ (M.greedy v) y - v y) x =
      M.T v x - v x := by
  have h := congrFun (M.Tσ_vσ (M.greedy v)) x
  simp only [Tσ] at h
  simp only [T, Tσ, ← M.Pv_sub]
  linarith

end PolicyModel

end DPExtensions.PolicyIterationNewton
