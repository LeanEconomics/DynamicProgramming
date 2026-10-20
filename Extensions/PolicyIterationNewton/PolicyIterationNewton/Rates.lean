/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyIterationNewton.PolicyModel
import Mathlib.Analysis.SpecificLimits.Basic

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
