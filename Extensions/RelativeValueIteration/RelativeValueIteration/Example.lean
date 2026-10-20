/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.Endogenous

/-!
# When relative value iteration does not help but endogenous value iteration does

Bray (2019, *Management Science*), Corollary 3: a non-ergodic exogenous variable voids the strong
convergence of relative value iteration but not that of endogenous value iteration.

The exogenous state `x ∈ {false, true}` alternates deterministically (a seasonal cycle), the
reward is `1` in state `true`, and there is no endogenous state or choice (`swapModel`).

* `swap_dobrushin_ge`: no Dobrushin bound below `1` holds — the chain does not mix.
* `swap_sp_iterate`, `swap_sp_vstar`: the span of the value-iteration error is exactly
  `βⁿ/(1 + β)` from `V₀ = 0`: relative value iteration converges at rate `β`, no faster.
* `swap_endo_exact`: endogenous value iteration is exact from the first step.
-/

open Finset

namespace DPExtensions.RelativeValueIteration

/-- The seasonal example. -/
noncomputable abbrev swapModel (β : ℝ) (h0 : 0 ≤ β) (h1 : β ≤ 1) : ExoMDP Bool Unit Unit where
  Γ _ := univ
  Γ_nonempty _ := univ_nonempty
  r s _ := if s.1 then 1 else 0
  β := β
  β_nonneg := h0
  β_le_one := h1
  Fx x x' := if x' = !x then 1 else 0
  Fx_nonneg x x' := by split_ifs <;> norm_num
  Fx_sum x := by cases x <;> simp
  Fy _ _ _ _ := 1
  Fy_nonneg _ _ _ _ := zero_le_one
  Fy_sum _ _ _ := by simp

variable {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1)

theorem swap_T (v : Bool × Unit → ℝ) (x : Bool) :
    (swapModel β h0 h1).toMDP.T v (x, ()) = (if x then 1 else 0) + β * v (!x, ()) := by
  simp only [MDP.T, MDP.Q, univ_unique, sup'_singleton]
  rw [Fintype.sum_prod_type]
  cases x <;> simp

/-- The two states' next-state distributions are disjoint, so no Dobrushin bound below `1`
holds. -/
theorem swap_dobrushin_ge {α : ℝ}
    (hα : ∀ s a s' a', a ∈ (swapModel β h0 h1).toMDP.Γ s → a' ∈ (swapModel β h0 h1).toMDP.Γ s' →
      1 - ∑ t, min ((swapModel β h0 h1).toMDP.P s a t) ((swapModel β h0 h1).toMDP.P s' a' t) ≤ α) :
    1 ≤ α := by
  have h := hα (true, ()) () (false, ()) () (mem_univ _) (mem_univ _)
  rw [Fintype.sum_prod_type] at h
  simpa using h

theorem sp_bool_unit (f : Bool × Unit → ℝ) : sp f = |f (true, ()) - f (false, ())| := by
  refine le_antisymm (sp_le fun a b => ?_) (abs_sub_le_sp f _ _)
  obtain ⟨x, ⟨⟩⟩ := a
  obtain ⟨y, ⟨⟩⟩ := b
  have h1 := le_abs_self (f (true, ()) - f (false, ()))
  have h2 := neg_abs_le (f (true, ()) - f (false, ()))
  have h3 := abs_nonneg (f (true, ()) - f (false, ()))
  cases x <;> cases y <;> (try simp only [sub_self]) <;> linarith

/-- **Value iteration's error shrinks exactly at rate `β` in span.** -/
theorem swap_sp_iterate (hβ : β < 1) (v : Bool × Unit → ℝ) (n : ℕ) :
    sp (fun s => (swapModel β h0 h1).toMDP.T^[n] v s - (swapModel β h0 h1).toMDP.vstar hβ s) =
      β ^ n * sp (fun s => v s - (swapModel β h0 h1).toMDP.vstar hβ s) := by
  set M := (swapModel β h0 h1).toMDP
  have hstep : ∀ (w : Bool × Unit → ℝ) (x : Bool),
      M.T w (x, ()) - M.vstar hβ (x, ()) = β * (w (!x, ()) - M.vstar hβ (!x, ())) := by
    intro w x
    have h := congrFun (M.T_vstar hβ) (x, ())
    rw [swap_T] at h
    rw [swap_T]
    linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sp_bool_unit] at ih ⊢
    rw [Function.iterate_succ_apply', hstep, hstep]
    simp only [Bool.not_true, Bool.not_false]
    rw [← mul_sub, abs_mul, abs_of_nonneg h0, abs_sub_comm, ih, pow_succ]
    ring

/-- `sp(v*) = 1/(1 + β)`. -/
theorem swap_sp_vstar (hβ : β < 1) :
    sp ((swapModel β h0 h1).toMDP.vstar hβ) = 1 / (1 + β) := by
  set M := (swapModel β h0 h1).toMDP
  have hfix := M.T_vstar hβ
  have ht := congrFun hfix (true, ())
  have hf := congrFun hfix (false, ())
  rw [swap_T] at ht hf
  norm_num at ht hf
  have e : M.vstar hβ (true, ()) - M.vstar hβ (false, ()) = 1 / (1 + β) := by
    field_simp
    linarith
  rw [sp_bool_unit, e, abs_of_pos (by positivity)]

/-- **Endogenous value iteration is exact**: with no endogenous variation, `Λv = 0` for every
`v`, so every endogenous iterate equals `Λv*`. -/
theorem swap_endo_exact (v : Bool × Unit → ℝ) : ExoMDP.endo v = 0 := by
  funext s
  obtain ⟨x, ⟨⟩⟩ := s
  simp [ExoMDP.endo, ExoMDP.mean]

/-- **Relative value iteration does not speed up; endogenous value iteration is exact.** For
`0 < β < 1`: no Dobrushin bound below `1` holds, the span error of value iteration from `0` is
exactly `βⁿ/(1 + β)`, and the endogenous iterates equal `Λv*` from the start. -/
theorem relative_slow_endogenous_exact (hβ : β < 1) :
    (∀ α : ℝ, (∀ s a s' a', a ∈ (swapModel β h0 h1).toMDP.Γ s →
        a' ∈ (swapModel β h0 h1).toMDP.Γ s' →
        1 - ∑ t, min ((swapModel β h0 h1).toMDP.P s a t)
          ((swapModel β h0 h1).toMDP.P s' a' t) ≤ α) → 1 ≤ α) ∧
    (∀ n, sp (fun s => (swapModel β h0 h1).toMDP.T^[n] 0 s -
        (swapModel β h0 h1).toMDP.vstar hβ s) = β ^ n / (1 + β)) ∧
    ∀ v n, ExoMDP.endo ((swapModel β h0 h1).toMDP.T^[n] v) =
      ExoMDP.endo ((swapModel β h0 h1).toMDP.vstar hβ) := by
  refine ⟨fun α hα => swap_dobrushin_ge h0 h1 hα, fun n => ?_, fun v n => by
    rw [swap_endo_exact, swap_endo_exact]⟩
  rw [swap_sp_iterate h0 h1 hβ]
  have e : (fun s => (0 : Bool × Unit → ℝ) s - (swapModel β h0 h1).toMDP.vstar hβ s) =
      fun s => -(swapModel β h0 h1).toMDP.vstar hβ s := by
    funext s
    simp
  rw [e, sp_neg, swap_sp_vstar h0 h1 hβ]
  ring

end DPExtensions.RelativeValueIteration
