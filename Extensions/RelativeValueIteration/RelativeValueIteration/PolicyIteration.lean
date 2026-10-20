/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.Endogenous

/-!
# Relative and endogenous policy iteration

Bray (2019a, *Quantitative Economics*), §4.1 and Proposition 4; Bray (2019b, *Management
Science*), §5 and Proposition 3.

Policy iteration sets `σ_{n+1}` greedy for `v_{σ_n}`. Relative policy iteration makes `σ_{n+1}`
greedy for the relative values `Δv_{σ_n}`, and endogenous policy iteration for the endogenous
values `Λv_{σ_n}`. Greedy policies ignore constants and functions of the exogenous state, so all
three produce the same policies; only the policy evaluation step differs, and the relative and
endogenous evaluations converge faster (`sp_policy_eval_le`, `endo_policy_eval_le`).

* `pi_improve`, `pi_mono`, `pi_terminates`: policy iteration improves monotonically and reaches
  `v*` after finitely many steps.
* `isGreedy_rel_iff`, `relPI_terminates`: relative policy iteration is policy iteration.
* `pi_residual_le`, `relPI_stopping`, `relPI_bray` (**Bray, 2019a, Prop 4**): Bray's stopping
  rule `|V_n − V_{n−1}| ≤ ε(1 − β)/(2β)` is met after finitely many iterations, and the policy it
  returns is `ε`-optimal.
* `policy_error_endo`: a policy greedy for `w` is within `β/(1 − β)·sp(Λ(Tw − w))` of optimal —
  only the endogenous part of the Bellman residual matters.
* `endoPI_terminates`, `endoPI_stopping`, `endoPI_bray` (**Bray, 2019b, Prop 3**): the same for
  endogenous policy iteration, with stopping statistic `Λ(TΛv) − Λv`.
-/

open Finset

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

/-- **Policy improvement**: a policy greedy for `v_σ` is at least as good as `σ`. -/
theorem pi_improve (hβ : M.β < 1) {σ σ' : S → A} (hσ : M.IsPolicy σ)
    (hσ' : M.IsGreedy σ' (M.vσ hβ σ)) : M.vσ hβ σ ≤ M.vσ hβ σ' := by
  refine M.le_vσ_of_le hβ σ' ?_
  rw [M.Tσ_eq_T_of_greedy hσ']
  conv_lhs => rw [← M.Tσ_vσ hβ σ]
  exact M.Tσ_le_T hσ _

/-- A fixed point of `T` is `v*`. -/
theorem eq_vstar_of_T_eq (hβ : M.β < 1) {w : S → ℝ} (h : M.T w = w) : w = M.vstar hβ :=
  le_antisymm (M.le_vstar_of_le hβ h.ge) (M.vstar_le_of_T_le hβ h.le)

/-- If policy improvement stalls, the policy is optimal. -/
theorem vσ_eq_vstar_of_stall (hβ : M.β < 1) {σ σ' : S → A}
    (hσ' : M.IsGreedy σ' (M.vσ hβ σ)) (h : M.vσ hβ σ' = M.vσ hβ σ) :
    M.vσ hβ σ = M.vstar hβ := by
  refine M.eq_vstar_of_T_eq hβ ?_
  rw [← M.Tσ_eq_T_of_greedy hσ']
  conv_lhs => rw [← h, M.Tσ_vσ hβ σ']
  exact h

/-- Policy iteration produces a monotone sequence of values. -/
theorem pi_mono (hβ : M.β < 1) {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (M.vσ hβ (σ n))) :
    Monotone fun n => M.vσ hβ (σ n) := by
  have hpol : ∀ n, M.IsPolicy (σ n) := fun n => by
    rcases n with _ | n
    · exact h0
    · exact fun s => (hstep n s).1
  exact monotone_nat_of_le_succ fun n => M.pi_improve hβ (hpol n) (hstep n)

/-- **Policy iteration terminates**: after finitely many steps the policy is optimal. -/
theorem pi_terminates (hβ : M.β < 1) {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (M.vσ hβ (σ n))) :
    ∃ N, ∀ n, N ≤ n → M.vσ hβ (σ n) = M.vstar hβ := by
  have hpol : ∀ n, M.IsPolicy (σ n) := fun n => by
    rcases n with _ | n
    · exact h0
    · exact fun s => (hstep n s).1
  have hmono := M.pi_mono hβ h0 hstep
  -- once optimal, always optimal
  have hstay : ∀ n, M.vσ hβ (σ n) = M.vstar hβ → M.vσ hβ (σ (n + 1)) = M.vstar hβ := by
    intro n hn
    refine le_antisymm (M.vσ_le_vstar hβ (hpol (n + 1))) ?_
    rw [← hn]
    exact hmono (Nat.le_succ n)
  suffices hex : ∃ N, M.vσ hβ (σ N) = M.vstar hβ by
    obtain ⟨N, hN⟩ := hex
    refine ⟨N, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base => exact hN
    | succ n _ ih => exact hstay n ih
  by_contra hne
  push Not at hne
  -- the policies are pairwise distinct ...
  have hinj : Function.Injective σ := by
    have hlt : ∀ n m, n < m → σ n ≠ σ m := by
      intro n m hnm heq
      have e : M.vσ hβ (σ (n + 1)) = M.vσ hβ (σ n) := le_antisymm
        ((hmono (Nat.succ_le_of_lt hnm)).trans (by rw [heq])) (hmono (Nat.le_succ n))
      exact hne n (M.vσ_eq_vstar_of_stall hβ (hstep n) e)
    intro n m heq
    rcases lt_trichotomy n m with h | h | h
    · exact absurd heq (hlt n m h)
    · exact h
    · exact absurd heq.symm (hlt m n h)
  -- ... but there are only finitely many policies
  have hfin : (Set.univ.pi fun s => (M.Γ s : Set A)).Finite :=
    Set.Finite.pi fun s => (M.Γ s).finite_toSet
  exact Set.infinite_of_injective_forall_mem hinj (fun n => Set.mem_univ_pi.2 (hpol n)) hfin

variable [Nonempty S]

omit [Nonempty S] in
/-- Greedy policies for the relative values are greedy for the values. -/
theorem isGreedy_rel_iff (s₀ : S) (σ : S → A) (v : S → ℝ) :
    M.IsGreedy σ (rel s₀ v) ↔ M.IsGreedy σ v := by
  rw [show rel s₀ v = fun t => v t + -v s₀ by funext t; simp [rel, sub_eq_add_neg]]
  exact M.isGreedy_add_const_iff σ v _

omit [Nonempty S] in
/-- **Relative policy iteration is policy iteration**, and so terminates. -/
theorem relPI_terminates (hβ : M.β < 1) (s₀ : S) {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (rel s₀ (M.vσ hβ (σ n)))) :
    ∃ N, ∀ n, N ≤ n → M.vσ hβ (σ n) = M.vstar hβ :=
  M.pi_terminates hβ h0 fun n => (M.isGreedy_rel_iff s₀ _ _).1 (hstep n)

/-- **The Bellman residual after a policy improvement step**: if `σ'` is greedy for `v_σ`, then
`0 ≤ Tv_{σ'} − v_{σ'} ≤ β·sp(v_{σ'} − v_σ)`. -/
theorem pi_residual_le (hβ : M.β < 1) {σ σ' : S → A} (hσ' : M.IsGreedy σ' (M.vσ hβ σ))
    (s : S) :
    0 ≤ M.T (M.vσ hβ σ') s - M.vσ hβ σ' s ∧
      M.T (M.vσ hβ σ') s - M.vσ hβ σ' s ≤ M.β * sp (fun t => M.vσ hβ σ' t - M.vσ hβ σ t) := by
  set v := M.vσ hβ σ'
  set w := M.vσ hβ σ
  have hv : v s = M.Q v s (σ' s) := (congrFun (M.Tσ_vσ hβ σ') s).symm
  refine ⟨?_, ?_⟩
  · rw [hv]
    exact sub_nonneg.2 (M.Q_le_T v (hσ' s).1)
  obtain ⟨a, ha, hTa, -⟩ := M.exists_greedyAct v s
  have hw : M.Q w s a ≤ M.Q w s (σ' s) := (hσ' s).2 a ha
  have e1 := M.Q_sub_Q v w s a
  have e2 := M.Q_sub_Q v w s (σ' s)
  have hd := dobrushin (M.P_sum s a) (M.P_sum s (σ' s)) fun t => v t - w t
  have hmin : 0 ≤ ∑ t, min (M.P s a t) (M.P s (σ' s) t) :=
    sum_nonneg fun t _ => le_min (M.P_nonneg s a t) (M.P_nonneg s (σ' s) t)
  have hsp := sp_nonneg fun t => v t - w t
  have hd' : ∑ t, M.P s a t * (v t - w t) - ∑ t, M.P s (σ' s) t * (v t - w t) ≤
      sp (fun t => v t - w t) := by nlinarith
  rw [hTa, hv]
  have := mul_le_mul_of_nonneg_left hd' M.β_nonneg
  nlinarith

/-- **Bray's stopping rule for relative policy iteration** (Bray, 2019a, Prop 4): if `σ'` is
greedy for `V_{n−1} = Δv_σ`, `V_n = Δv_{σ'}` and `|V_n − V_{n−1}| ≤ ε(1 − β)/(2β)`, then any
policy greedy for `V_n` is `ε`-optimal. -/
theorem relPI_stopping (hβ : M.β < 1) (hβ0 : 0 < M.β) {ε : ℝ} (s₀ : S) {σ σ' σ'' : S → A}
    (hσ' : M.IsGreedy σ' (rel s₀ (M.vσ hβ σ)))
    (hstop : ∀ s, |rel s₀ (M.vσ hβ σ') s - rel s₀ (M.vσ hβ σ) s| ≤ ε * (1 - M.β) / (2 * M.β))
    (hσ'' : M.IsGreedy σ'' (rel s₀ (M.vσ hβ σ'))) (s : S) :
    M.vstar hβ s - M.vσ hβ σ'' s ≤ ε := by
  have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
  have hε : 0 ≤ ε := by
    have h := (abs_nonneg _).trans (hstop s)
    have h2 : 0 < (1 - M.β) / (2 * M.β) := by positivity
    rw [mul_div_assoc] at h
    exact nonneg_of_mul_nonneg_left h h2
  have hσ'v := (M.isGreedy_rel_iff s₀ _ _).1 hσ'
  have hσ''v := (M.isGreedy_rel_iff s₀ _ _).1 hσ''
  -- span of the change in values, from the stopping statistic
  have hsp : sp (fun t => M.vσ hβ σ' t - M.vσ hβ σ t) ≤ ε * (1 - M.β) / M.β := by
    refine sp_le fun x y => ?_
    have h1 := abs_le.1 (hstop x)
    have h2 := abs_le.1 (hstop y)
    have e : ε * (1 - M.β) / M.β = 2 * (ε * (1 - M.β) / (2 * M.β)) := by field_simp
    simp only [rel] at h1 h2
    rw [e]
    linarith [h1.2, h2.1]
  -- the Bellman residual of `v_{σ'}`
  have hres : sp (fun t => M.T (M.vσ hβ σ') t - M.vσ hβ σ' t) ≤ M.β * (ε * (1 - M.β) / M.β) :=
    sp_le fun x y => by
      have hx := (M.pi_residual_le hβ hσ'v x).2
      have hy := (M.pi_residual_le hβ hσ'v y).1
      have := mul_le_mul_of_nonneg_left hsp M.β_nonneg
      linarith
  refine ((M.policy_error hβ hσ''v s).2).trans ?_
  calc M.β / (1 - M.β) * sp (fun t => M.T (M.vσ hβ σ') t - M.vσ hβ σ' t)
      ≤ M.β / (1 - M.β) * (M.β * (ε * (1 - M.β) / M.β)) :=
        mul_le_mul_of_nonneg_left hres (div_nonneg M.β_nonneg hβ1.le)
    _ = M.β * ε := by field_simp
    _ ≤ ε := mul_le_of_le_one_left hε M.β_le_one

/-- **Relative policy iteration returns an `ε`-optimal policy after finitely many iterations**
(Bray, 2019a, Prop 4). -/
theorem relPI_bray (hβ : M.β < 1) (hβ0 : 0 < M.β) {ε : ℝ} (hε : 0 ≤ ε) (s₀ : S)
    {σ : ℕ → S → A} (h0 : M.IsPolicy (σ 0))
    (hstep : ∀ n, M.IsGreedy (σ (n + 1)) (rel s₀ (M.vσ hβ (σ n)))) :
    ∃ N, (∀ s, |rel s₀ (M.vσ hβ (σ (N + 1))) s - rel s₀ (M.vσ hβ (σ N)) s| ≤
        ε * (1 - M.β) / (2 * M.β)) ∧
      ∀ σ'' : S → A, M.IsGreedy σ'' (rel s₀ (M.vσ hβ (σ (N + 1)))) →
        ∀ s, M.vstar hβ s - M.vσ hβ σ'' s ≤ ε := by
  obtain ⟨N, hN⟩ := M.relPI_terminates hβ s₀ h0 hstep
  have hstop : ∀ s, |rel s₀ (M.vσ hβ (σ (N + 1))) s - rel s₀ (M.vσ hβ (σ N)) s| ≤
      ε * (1 - M.β) / (2 * M.β) := fun s => by
    rw [hN (N + 1) (Nat.le_succ N), hN N le_rfl, sub_self, abs_zero]
    have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
    positivity
  exact ⟨N, hstop, fun σ'' hσ'' s => M.relPI_stopping hβ hβ0 s₀ (hstep N) hstop hσ'' s⟩

end MDP

namespace ExoMDP

variable {X Y A : Type*} [Fintype X] [Fintype Y] (E : ExoMDP X Y A)

/-- The exogenous chain with reward `m`, an MDP on `X` with a single action. -/
abbrev exoMDP (m : X → ℝ) : MDP X Unit where
  Γ _ := {()}
  Γ_nonempty _ := singleton_nonempty _
  r x _ := m x
  β := E.β
  β_nonneg := E.β_nonneg
  β_le_one := E.β_le_one
  P x _ x' := E.Fx x x'
  P_nonneg x _ x' := E.Fx_nonneg x x'
  P_sum x _ := E.Fx_sum x

/-- `c = m + βF_x c` has a solution when `β < 1`. -/
theorem exists_exo_solution (hβ : E.β < 1) (m : X → ℝ) :
    ∃ c : X → ℝ, ∀ x, c x = m x + E.β * E.Fxc c x := by
  refine ⟨(E.exoMDP m).vσ hβ fun _ => (), fun x => ?_⟩
  have h := congrFun ((E.exoMDP m).Tσ_vσ hβ fun _ => ()) x
  exact h.symm

/-- **Only the endogenous part of the Bellman residual matters**: a policy greedy for `w` is
within `β/(1 − β)·sp(Λ(Tw − w))` of optimal. -/
theorem policy_error_endo [Nonempty X] [Nonempty Y] (hβ : E.β < 1) {w : X × Y → ℝ}
    {σ : X × Y → A} (hσ : E.toMDP.IsGreedy σ w) (s : X × Y) :
    E.toMDP.vstar hβ s - E.toMDP.vσ hβ σ s ≤
      E.β / (1 - E.β) * sp (endo fun t => E.toMDP.T w t - w t) := by
  obtain ⟨c, hc⟩ := E.exists_exo_solution hβ (mean fun t => E.toMDP.T w t - w t)
  have hσ' : E.toMDP.IsGreedy σ (fun t => w t + lift c t) :=
    (E.isGreedy_add_lift_iff σ w c).2 hσ
  have hres : (fun t => E.toMDP.T (fun t => w t + lift c t) t - (w t + lift c t)) =
      endo fun t => E.toMDP.T w t - w t := by
    rw [E.T_add_lift]
    funext t
    simp only [endo, lift]
    have := hc t.1
    linarith
  have h := (E.toMDP.policy_error hβ hσ' s).2
  rwa [hres] at h

/-- **Endogenous policy iteration is policy iteration**, and so terminates. -/
theorem endoPI_terminates [Nonempty Y] (hβ : E.β < 1) {σ : ℕ → X × Y → A}
    (h0 : E.toMDP.IsPolicy (σ 0))
    (hstep : ∀ n, E.toMDP.IsGreedy (σ (n + 1)) (endo (E.toMDP.vσ hβ (σ n)))) :
    ∃ N, ∀ n, N ≤ n → E.toMDP.vσ hβ (σ n) = E.toMDP.vstar hβ :=
  E.toMDP.pi_terminates hβ h0 fun n => (E.isGreedy_endo_iff _ _).1 (hstep n)

/-- Bray's stopping statistic `Λ(TΛv) − Λv` is the endogenous Bellman residual `Λ(Tv − v)`. -/
theorem endo_T_endo_sub [Nonempty Y] (v : X × Y → ℝ) :
    (fun s => endo (E.toMDP.T (endo v)) s - endo v s) = endo fun t => E.toMDP.T v t - v t := by
  have h := E.endoT_iterate v 1
  simp only [Function.iterate_one] at h
  rw [h, ← endo_sub]

/-- **Bray's stopping rule for endogenous policy iteration** (Bray, 2019b, Prop 3): if
`|Λ(TΛv_σ) − Λv_σ| ≤ ε(1 − β)/(2β)`, any policy greedy for `Λv_σ` is `ε`-optimal. -/
theorem endoPI_stopping [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (hβ0 : 0 < E.β) {ε : ℝ}
    {σ σ' : X × Y → A}
    (hstop : ∀ s, |endo (E.toMDP.T (endo (E.toMDP.vσ hβ σ))) s - endo (E.toMDP.vσ hβ σ) s| ≤
      ε * (1 - E.β) / (2 * E.β))
    (hσ' : E.toMDP.IsGreedy σ' (endo (E.toMDP.vσ hβ σ))) (s : X × Y) :
    E.toMDP.vstar hβ s - E.toMDP.vσ hβ σ' s ≤ ε := by
  have hβ1 : 0 < 1 - E.β := sub_pos.2 hβ
  have hstop' : ∀ s, |(endo fun t => E.toMDP.T (E.toMDP.vσ hβ σ) t - E.toMDP.vσ hβ σ t) s| ≤
      ε * (1 - E.β) / (2 * E.β) := fun s => by
    rw [← E.endo_T_endo_sub]
    exact hstop s
  have hsp : sp (endo fun t => E.toMDP.T (E.toMDP.vσ hβ σ) t - E.toMDP.vσ hβ σ t) ≤
      ε * (1 - E.β) / E.β := by
    refine sp_le fun x y => ?_
    have h1 := abs_le.1 (hstop' x)
    have h2 := abs_le.1 (hstop' y)
    have e : ε * (1 - E.β) / E.β = 2 * (ε * (1 - E.β) / (2 * E.β)) := by field_simp
    rw [e]
    linarith [h1.2, h2.1]
  refine (E.policy_error_endo hβ ((E.isGreedy_endo_iff _ _).1 hσ') s).trans ?_
  calc E.β / (1 - E.β) * sp (endo fun t => E.toMDP.T (E.toMDP.vσ hβ σ) t - E.toMDP.vσ hβ σ t)
      ≤ E.β / (1 - E.β) * (ε * (1 - E.β) / E.β) :=
        mul_le_mul_of_nonneg_left hsp (div_nonneg E.β_nonneg hβ1.le)
    _ = ε := by field_simp

/-- **Endogenous policy iteration returns an `ε`-optimal policy after finitely many iterations**
(Bray, 2019b, Prop 3). -/
theorem endoPI_bray [Nonempty X] [Nonempty Y] (hβ : E.β < 1) (hβ0 : 0 < E.β) {ε : ℝ}
    (hε : 0 ≤ ε) {σ : ℕ → X × Y → A} (h0 : E.toMDP.IsPolicy (σ 0))
    (hstep : ∀ n, E.toMDP.IsGreedy (σ (n + 1)) (endo (E.toMDP.vσ hβ (σ n)))) :
    ∃ N, (∀ s, |endo (E.toMDP.T (endo (E.toMDP.vσ hβ (σ N)))) s -
        endo (E.toMDP.vσ hβ (σ N)) s| ≤ ε * (1 - E.β) / (2 * E.β)) ∧
      ∀ σ' : X × Y → A, E.toMDP.IsGreedy σ' (endo (E.toMDP.vσ hβ (σ N))) →
        ∀ s, E.toMDP.vstar hβ s - E.toMDP.vσ hβ σ' s ≤ ε := by
  obtain ⟨N, hN⟩ := E.endoPI_terminates hβ h0 hstep
  have hβ1 : 0 < 1 - E.β := sub_pos.2 hβ
  have hstop : ∀ s, |endo (E.toMDP.T (endo (E.toMDP.vσ hβ (σ N)))) s -
      endo (E.toMDP.vσ hβ (σ N)) s| ≤ ε * (1 - E.β) / (2 * E.β) := fun s => by
    have h := congrFun (E.endo_T_endo_sub (E.toMDP.vσ hβ (σ N))) s
    rw [h, hN N le_rfl, E.toMDP.T_vstar hβ]
    simp only [sub_self, endo, mean, sum_const_zero, zero_div, abs_zero]
    positivity
  exact ⟨N, hstop, fun σ' hσ' s => E.endoPI_stopping hβ hβ0 hstop hσ' s⟩

end ExoMDP

end DPExtensions.RelativeValueIteration
