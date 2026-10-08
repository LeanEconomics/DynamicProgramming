/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.MDP

/-!
# The discounted problem

For `β < 1` the Bellman operator `T` and the policy operators `T_σ` are `β`-contractions for the
supremum norm, with fixed points `v*` (`vstar`) and `v_σ` (`vσ`), and monotonicity orders them.
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

theorem abs_Q_sub_le (v w : S → ℝ) (s : S) (a : A) :
    |M.Q v s a - M.Q w s a| ≤ M.β * ‖v - w‖ := by
  rw [M.Q_sub_Q, abs_mul, abs_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans ?_) M.β_nonneg
  calc ∑ t, |M.P s a t * (v t - w t)| ≤ ∑ t, M.P s a t * ‖v - w‖ := sum_le_sum fun t _ => by
        rw [abs_mul, abs_of_nonneg (M.P_nonneg s a t)]
        refine mul_le_mul_of_nonneg_left ?_ (M.P_nonneg s a t)
        have := norm_le_pi_norm (v - w) t
        rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    _ = ‖v - w‖ := by rw [← sum_mul, M.P_sum, one_mul]

theorem norm_T_sub_le (v w : S → ℝ) : ‖M.T v - M.T w‖ ≤ M.β * ‖v - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun s => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  obtain ⟨a, ha, hva, -⟩ := M.exists_greedyAct v s
  obtain ⟨b, hb, hwb, -⟩ := M.exists_greedyAct w s
  have h1 := abs_le.1 (M.abs_Q_sub_le v w s a)
  have h2 := abs_le.1 (M.abs_Q_sub_le v w s b)
  have h3 := M.Q_le_T w ha
  have h4 := M.Q_le_T v hb
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem norm_Tσ_sub_le (σ : S → A) (v w : S → ℝ) : ‖M.Tσ σ v - M.Tσ σ w‖ ≤ M.β * ‖v - w‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun s => by
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact M.abs_Q_sub_le v w s (σ s)

theorem T_mono : Monotone M.T := fun _ w h s =>
  sup'_le _ _ fun a ha => le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (M.P_nonneg s a t)) M.β_nonneg))
    (M.Q_le_T w ha)

theorem Tσ_mono (σ : S → A) : Monotone (M.Tσ σ) := fun _ _ h s =>
  add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (h t) (M.P_nonneg s (σ s) t)) M.β_nonneg)

theorem contracting_T (hβ : M.β < 1) : ContractingWith ⟨M.β, M.β_nonneg⟩ M.T :=
  ⟨hβ, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_T_sub_le v w⟩

theorem contracting_Tσ (hβ : M.β < 1) (σ : S → A) :
    ContractingWith ⟨M.β, M.β_nonneg⟩ (M.Tσ σ) :=
  ⟨hβ, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_Tσ_sub_le σ v w⟩

/-- The value function. -/
noncomputable def vstar (hβ : M.β < 1) : S → ℝ :=
  ContractingWith.fixedPoint M.T (M.contracting_T hβ)

/-- The value of a decision rule. -/
noncomputable def vσ (hβ : M.β < 1) (σ : S → A) : S → ℝ :=
  ContractingWith.fixedPoint (M.Tσ σ) (M.contracting_Tσ hβ σ)

theorem T_vstar (hβ : M.β < 1) : M.T (M.vstar hβ) = M.vstar hβ :=
  ContractingWith.fixedPoint_isFixedPt _

theorem Tσ_vσ (hβ : M.β < 1) (σ : S → A) : M.Tσ σ (M.vσ hβ σ) = M.vσ hβ σ :=
  ContractingWith.fixedPoint_isFixedPt _

/-- `w ≤ T_σw` implies `w ≤ v_σ`. -/
theorem le_vσ_of_le (hβ : M.β < 1) (σ : S → A) {w : S → ℝ} (h : w ≤ M.Tσ σ w) :
    w ≤ M.vσ hβ σ := by
  have hit : ∀ n, w ≤ (M.Tσ σ)^[n] w := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact h.trans (M.Tσ_mono σ ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint (M.contracting_Tσ hβ σ) w) hit

/-- `w ≤ Tw` implies `w ≤ v*`. -/
theorem le_vstar_of_le (hβ : M.β < 1) {w : S → ℝ} (h : w ≤ M.T w) : w ≤ M.vstar hβ := by
  have hit : ∀ n, w ≤ M.T^[n] w := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact h.trans (M.T_mono ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint (M.contracting_T hβ) w) hit

/-- `Tu ≤ u` implies `v* ≤ u`. -/
theorem vstar_le_of_T_le (hβ : M.β < 1) {u : S → ℝ} (h : M.T u ≤ u) : M.vstar hβ ≤ u := by
  have hit : ∀ n, M.T^[n] u ≤ u := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (M.T_mono ih).trans h
  exact le_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint (M.contracting_T hβ) u) hit

theorem vσ_le_vstar (hβ : M.β < 1) {σ : S → A} (hσ : M.IsPolicy σ) :
    M.vσ hβ σ ≤ M.vstar hβ :=
  M.le_vstar_of_le hβ (by
    have := M.Tσ_le_T hσ (M.vσ hβ σ)
    rwa [M.Tσ_vσ] at this)

end MDP

end DPExtensions.RelativeValueIteration
