import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence rates of policy iteration

Puterman and Brumelle (1979); Santos and Rust (2004).

Policy iteration starts from `σ₀` and sets `σ_{k+1} = greedy(v_{σ_k})`; write `v_k = v_{σ_k}` and
`e_k = v* − v_k`.

* `piValue_mono`, `linear_rate`, `pi_converges`: values increase, `‖e_{k+1}‖ ≤ β‖e_k‖`, and
  `v_k → v*` — at least as fast as value iteration.
* `pb_bound` (**Puterman–Brumelle**): for every `v`, with `σ = greedy v`,
  `0 ≤ v* − v_σ` and `‖v* − v_σ‖ ≤ (β/(1 − β))·δ·‖v* − v‖` whenever the rows of `P_σ` and
  `P_{greedy v*}` differ by at most `δ` in total variation.
* `quadratic_rate`: if greedy transitions are Lipschitz in `v` with constant `L`,
  `‖e_{k+1}‖ ≤ (βL/(1 − β))‖e_k‖²` — Newton's quadratic convergence.
* `superlinear_rate`: if greedy transitions are continuous at `v*`, `‖e_{k+1}‖/‖e_k‖ → 0`.
* `pi_terminates`: if every policy greedy for a `v` near `v*` is optimal, policy iteration reaches
  `v*` exactly after finitely many steps, once `β^K‖e₀‖` is below the radius.
-/

open Filter Topology Finset

namespace DPExtensions.PolicyIterationNewton

namespace PolicyModel

variable {X Pol : Type*} [Fintype X] (M : PolicyModel X Pol)

/-- The policies of policy iteration. -/
noncomputable def piPolicy (σ₀ : Pol) : ℕ → Pol
  | 0 => σ₀
  | k + 1 => M.greedy (M.vσ (piPolicy σ₀ k))

/-- The values of policy iteration. -/
noncomputable def piValue (σ₀ : Pol) (k : ℕ) : X → ℝ := M.vσ (M.piPolicy σ₀ k)

theorem piValue_succ (σ₀ : Pol) (k : ℕ) :
    M.piValue σ₀ (k + 1) = M.vσ (M.greedy (M.piValue σ₀ k)) := rfl

theorem le_T_vσ (σ : Pol) : M.vσ σ ≤ M.T (M.vσ σ) := by
  have := M.Tσ_le_T σ (M.vσ σ)
  rwa [M.Tσ_vσ] at this

/-- **Policy iteration improves**: `v_k ≤ Tv_k ≤ v_{k+1}`. -/
theorem piValue_mono (σ₀ : Pol) (k : ℕ) :
    M.piValue σ₀ k ≤ M.T (M.piValue σ₀ k) ∧ M.T (M.piValue σ₀ k) ≤ M.piValue σ₀ (k + 1) :=
  ⟨M.le_T_vσ _, M.le_vσ_greedy (M.le_T_vσ _)⟩

/-- **The linear rate**: `‖v* − v_{k+1}‖ ≤ β‖v* − v_k‖`. -/
theorem linear_rate (σ₀ : Pol) (k : ℕ) :
    ‖M.vstar - M.piValue σ₀ (k + 1)‖ ≤ M.β * ‖M.vstar - M.piValue σ₀ k‖ := by
  obtain ⟨-, h2⟩ := M.piValue_mono σ₀ k
  have h3 : M.piValue σ₀ (k + 1) ≤ M.vstar := M.vσ_le_vstar _
  have h4 := M.norm_T_sub_le M.vstar (M.piValue σ₀ k)
  rw [M.T_vstar] at h4
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun x => ?_
  have h5 := (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).1 h4 x
  rw [Pi.sub_apply, Real.norm_eq_abs] at h5 ⊢
  have h6 := h2 x
  have h7 := h3 x
  rw [abs_of_nonneg (by linarith)]
  rw [abs_le] at h5
  linarith [h5.2]

theorem error_le_geometric (σ₀ : Pol) (k : ℕ) :
    ‖M.vstar - M.piValue σ₀ k‖ ≤ M.β ^ k * ‖M.vstar - M.piValue σ₀ 0‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine (M.linear_rate σ₀ k).trans ?_
    rw [pow_succ]
    nlinarith [M.β_nonneg]

/-- **Policy iteration converges**: `v_k → v*`. -/
theorem pi_converges (σ₀ : Pol) : Tendsto (M.piValue σ₀) atTop (𝓝 M.vstar) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one).mul_const
    ‖M.vstar - M.piValue σ₀ 0‖
  rw [zero_mul] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun k => dist_nonneg) fun k => ?_
  rw [dist_eq_norm, norm_sub_rev]
  exact M.error_le_geometric σ₀ k

theorem abs_Pv_diff_le (σ τ : Pol) (v : X → ℝ) (x : X) {δ : ℝ}
    (hδ : ∑ y, |M.P σ x y - M.P τ x y| ≤ δ) : |M.Pv σ v x - M.Pv τ v x| ≤ δ * ‖v‖ := by
  simp only [Pv, ← sum_sub_distrib, ← sub_mul]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y, |(M.P σ x y - M.P τ x y) * v y| ≤ ∑ y, |M.P σ x y - M.P τ x y| * ‖v‖ :=
        sum_le_sum fun y _ => by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := norm_le_pi_norm v y
          rwa [Real.norm_eq_abs] at this
    _ = (∑ y, |M.P σ x y - M.P τ x y|) * ‖v‖ := by rw [sum_mul]
    _ ≤ δ * ‖v‖ := mul_le_mul_of_nonneg_right hδ (norm_nonneg _)

/-- **The Puterman–Brumelle bound**: with `σ = greedy v`,
`0 ≤ v* − v_σ` and `(1 − β)‖v* − v_σ‖ ≤ βδ‖v* − v‖` when the rows of `P_{greedy v*}` and `P_σ`
differ by at most `δ` in total variation. -/
theorem pb_bound (v : X → ℝ) {δ : ℝ}
    (hδ : ∀ x, ∑ y, |M.P (M.greedy M.vstar) x y - M.P (M.greedy v) x y| ≤ δ) :
    0 ≤ M.vstar - M.vσ (M.greedy v) ∧
      (1 - M.β) * ‖M.vstar - M.vσ (M.greedy v)‖ ≤ M.β * δ * ‖M.vstar - v‖ := by
  set σ := M.greedy v
  set σs := M.greedy M.vstar
  set dd := M.vstar - M.vσ σ
  have hd0 : 0 ≤ dd := fun x => sub_nonneg.2 (M.vσ_le_vstar σ x)
  refine ⟨hd0, ?_⟩
  have hβ0 := M.β_nonneg
  -- the one-step gap `v* − T_σv*` is at most `βδ‖v* − v‖`
  have hgap : ∀ x, 0 ≤ M.vstar x - M.Tσ σ M.vstar x ∧
      M.vstar x - M.Tσ σ M.vstar x ≤ M.β * (δ * ‖M.vstar - v‖) := by
    intro x
    have e1 : M.Tσ σs M.vstar x = M.vstar x := congrFun M.T_vstar x
    have e2 : M.Tσ σs v x ≤ M.Tσ σ v x := M.greedy_spec v σs x
    have e3 := M.abs_Pv_diff_le σs σ (fun y => M.vstar y - v y) x (hδ x)
    have e4 := M.Pv_sub σs M.vstar v x
    have e5 := M.Pv_sub σ M.vstar v x
    have e6 := M.Tσ_le_T σ M.vstar x
    rw [M.T_vstar] at e6
    have e7 : ‖fun y => M.vstar y - v y‖ = ‖M.vstar - v‖ := rfl
    rw [e7, abs_le] at e3
    refine ⟨sub_nonneg.2 e6, ?_⟩
    simp only [Tσ] at e1 e2 ⊢
    nlinarith [mul_le_mul_of_nonneg_left e3.2 hβ0]
  have hdx : ∀ x, dd x = (M.vstar x - M.Tσ σ M.vstar x) + M.β * M.Pv σ dd x := by
    intro x
    have h1 := congrFun (M.Tσ_vσ σ) x
    have h2 := M.Pv_sub σ M.vstar (M.vσ σ) x
    simp only [Tσ] at h1 ⊢
    simp only [dd, Pi.sub_apply]
    rw [show M.Pv σ (M.vstar - M.vσ σ) x = M.Pv σ M.vstar x - M.Pv σ (M.vσ σ) x from h2.symm]
    linarith
  rcases isEmpty_or_nonempty X with hX | hX
  · have h1 : dd = 0 := Subsingleton.elim _ _
    have h2 : M.vstar - v = 0 := Subsingleton.elim _ _
    simp [h1, h2]
  have hδ0 : 0 ≤ δ := (sum_nonneg fun y _ => abs_nonneg _).trans (hδ (Classical.arbitrary X))
  have hnorm : ‖dd‖ ≤ M.β * (δ * ‖M.vstar - v‖) + M.β * ‖dd‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x => ?_
    rw [Real.norm_eq_abs, hdx x]
    obtain ⟨g1, g2⟩ := hgap x
    have h3 := M.abs_Pv_le σ dd x
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg g1, abs_mul, abs_of_nonneg hβ0]
    nlinarith [mul_le_mul_of_nonneg_left h3 hβ0]
  nlinarith

/-- **Quadratic convergence** (Puterman and Brumelle, 1979): if the transitions of greedy policies
are Lipschitz in `v`, `∑_y |P_{greedy v}(x, y) − P_{greedy w}(x, y)| ≤ L‖v − w‖`, then
`(1 − β)‖v* − v_{k+1}‖ ≤ βL‖v* − v_k‖²`. -/
theorem quadratic_rate {L : ℝ}
    (hL : ∀ v w x, ∑ y, |M.P (M.greedy v) x y - M.P (M.greedy w) x y| ≤ L * ‖v - w‖)
    (σ₀ : Pol) (k : ℕ) :
    (1 - M.β) * ‖M.vstar - M.piValue σ₀ (k + 1)‖ ≤
      M.β * L * ‖M.vstar - M.piValue σ₀ k‖ ^ 2 := by
  have h := (M.pb_bound (M.piValue σ₀ k) (δ := L * ‖M.vstar - M.piValue σ₀ k‖)
    fun x => hL _ _ x).2
  rw [← M.piValue_succ] at h
  calc (1 - M.β) * ‖M.vstar - M.piValue σ₀ (k + 1)‖
      ≤ M.β * (L * ‖M.vstar - M.piValue σ₀ k‖) * ‖M.vstar - M.piValue σ₀ k‖ := h
    _ = M.β * L * ‖M.vstar - M.piValue σ₀ k‖ ^ 2 := by ring

/-- **Superlinear convergence**: if the transitions of greedy policies are continuous at `v*`,
then for every `ε > 0`, eventually `‖v* − v_{k+1}‖ ≤ ε‖v* − v_k‖`. -/
theorem superlinear_rate
    (hcont : ∀ ε > 0, ∃ ρ > 0, ∀ v, ‖v - M.vstar‖ < ρ →
      ∀ x, ∑ y, |M.P (M.greedy M.vstar) x y - M.P (M.greedy v) x y| ≤ ε)
    (σ₀ : Pol) : ∀ ε > 0, ∀ᶠ k in atTop,
      ‖M.vstar - M.piValue σ₀ (k + 1)‖ ≤ ε * ‖M.vstar - M.piValue σ₀ k‖ := by
  intro ε hε
  have hβ1 : 0 < 1 - M.β := sub_pos.2 M.β_lt_one
  obtain ⟨ρ, hρ, hcρ⟩ := hcont (ε * (1 - M.β) / (M.β + 1))
    (div_pos (mul_pos hε hβ1) (by linarith [M.β_nonneg]))
  have hconv := M.pi_converges σ₀
  rw [tendsto_iff_dist_tendsto_zero] at hconv
  filter_upwards [hconv.eventually (gt_mem_nhds hρ)] with k hk
  rw [dist_eq_norm] at hk
  have h := (M.pb_bound (M.piValue σ₀ k) (hcρ _ hk)).2
  rw [← M.piValue_succ] at h
  have hb : M.β * (ε * (1 - M.β) / (M.β + 1)) ≤ (1 - M.β) * ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith [M.β_nonneg])]
    nlinarith [M.β_nonneg]
  have h2 : (1 - M.β) * ‖M.vstar - M.piValue σ₀ (k + 1)‖ ≤
      (1 - M.β) * (ε * ‖M.vstar - M.piValue σ₀ k‖) :=
    h.trans (by nlinarith [norm_nonneg (M.vstar - M.piValue σ₀ k)])
  exact le_of_mul_le_mul_left h2 hβ1

/-- **Finite termination**: if every policy greedy for a `v` within `ρ` of `v*` is optimal,
policy iteration reaches `v*` exactly at step `K + 1` whenever `β^K‖v* − v₀‖ < ρ`, and stays
there. -/
theorem pi_terminates {ρ : ℝ}
    (hloc : ∀ v, ‖v - M.vstar‖ < ρ → M.Tσ (M.greedy v) M.vstar = M.vstar)
    (σ₀ : Pol) {K : ℕ} (hK : M.β ^ K * ‖M.vstar - M.piValue σ₀ 0‖ < ρ) :
    ∀ k, K + 1 ≤ k → M.piValue σ₀ k = M.vstar := by
  have hstep : ∀ k, ‖M.piValue σ₀ k - M.vstar‖ < ρ → M.piValue σ₀ (k + 1) = M.vstar := by
    intro k hk
    rw [M.piValue_succ]
    exact (ContractingWith.fixedPoint_unique (M.contracting_Tσ _) (hloc _ hk)).symm
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine hstep K ?_
    rw [norm_sub_rev]
    exact (M.error_le_geometric σ₀ K).trans_lt hK
  | succ k _ ih =>
    refine hstep k ?_
    rw [ih, sub_self, norm_zero]
    exact lt_of_le_of_lt (mul_nonneg (pow_nonneg M.β_nonneg K) (norm_nonneg _)) hK

/-- Policy iteration terminates whenever greedy policies near `v*` are optimal. -/
theorem exists_pi_terminates {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : ∀ v, ‖v - M.vstar‖ < ρ → M.Tσ (M.greedy v) M.vstar = M.vstar) (σ₀ : Pol) :
    ∃ K, ∀ k, K ≤ k → M.piValue σ₀ k = M.vstar := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one).mul_const
    ‖M.vstar - M.piValue σ₀ 0‖
  rw [zero_mul] at h
  obtain ⟨K, hK⟩ := (h.eventually (gt_mem_nhds hρ)).exists
  exact ⟨K + 1, M.pi_terminates hloc σ₀ hK⟩

end PolicyModel

end DPExtensions.PolicyIterationNewton

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

set_option linter.style.longLine false
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.mk
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.r
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.P
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.P_nonneg
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.P_sum
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.β
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.β_nonneg
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.β_lt_one
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.greedy
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.greedy_spec
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.Pv
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.Tσ
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.T
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.Tσ_le_T
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.Pv_sub
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.abs_Pv_le
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.Pv_mono
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.Tσ_mono
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.norm_Tσ_sub_le
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.norm_T_sub_le
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.contracting_T
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.contracting_Tσ
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.vstar
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.vσ
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.T_vstar
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.Tσ_vσ
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.le_vσ_of_le
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.vσ_le_vstar
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.vσ_greedy_vstar
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.le_vσ_greedy
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.newton_identity
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.piPolicy
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.piValue
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.piValue_succ
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.le_T_vσ
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.piValue_mono
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.linear_rate
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.error_le_geometric
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.pi_converges
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.abs_Pv_diff_le
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.pb_bound
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.quadratic_rate
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.superlinear_rate
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.pi_terminates
#print axioms DPExtensions.PolicyIterationNewton.PolicyModel.exists_pi_terminates
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.mk
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.Γ
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.Γ_nonempty
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.r
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.β
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.β_nonneg
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.β_lt_one
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.P
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.P_nonneg
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.P_sum
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.Pol
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.Q
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.greedyAct
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.greedyAct_mem
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.greedyAct_max
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.toPolicyModel
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.Tσ_eq
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.vstar_eq
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.abs_Q_sub_le
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.exists_gap
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.greedy_optimal_of_near
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.pi_terminates_finite
#print axioms DPExtensions.PolicyIterationNewton.FiniteMDP.exists_pi_terminates_finite
