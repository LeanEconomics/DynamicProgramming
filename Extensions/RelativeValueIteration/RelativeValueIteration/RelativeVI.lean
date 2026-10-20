/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.Discounted
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Relative value iteration

Morton and Wecker (1977); MacQueen (1966); Porteus (1971); Bray (2019, *Quantitative
Economics*), Propositions 1–3.

Relative value iteration sets `V_{n+1} = rel(TV_n)`, normalizing the value at a reference state
to zero; by `relT_iterate`, `V_n = rel(TⁿV₀)`.

* `sp_iterate_sub_vstar`, `rel_converges` (**strong convergence**, non-asymptotic): with `α`
  bounding the Dobrushin coefficient, `sp(TⁿV − v*) ≤ (βα)ⁿ sp(V − v*)` and the relative values
  converge to `rel(v*)` at rate `βα`, while the levels converge only at rate `β`. When `β` is
  close to `1` and the chain mixes (`α < 1`), relative value iteration needs far fewer steps.
* `policy_error` (**MacQueen–Porteus**): a policy greedy for any `v` is within
  `β/(1 − β)·sp(Tv − v)` of optimal — a bound that ignores constant shifts.
* `stopping_rule`, `stopping_rule_sup` (**Bray's stopping rule**): the policy greedy for `V_n`
  is `ε`-optimal once `sp(V_{n+1} − V_n) ≤ ε(1 − β)/β`, in particular once
  `|V_{n+1} − V_n| ≤ ε(1 − β)/(2β)` everywhere.
* `sp_relIter_succ_sub_le`, `stopping_eventually`: the stopping criterion is met after finitely
  many steps, geometrically fast at rate `βα`.
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

namespace MDP

variable {S A : Type*} [Fintype S] [Nonempty S] (M : MDP S A)

omit [Nonempty S] in
/-- The Dobrushin coefficient is at most `1`, so `α = 1` is always a valid bound. -/
theorem dobrushin_le_one (s : S) (a : A) (s' : S) (a' : A) :
    1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ 1 := by
  have : 0 ≤ ∑ t, min (M.P s a t) (M.P s' a' t) :=
    sum_nonneg fun t _ => le_min (M.P_nonneg s a t) (M.P_nonneg s' a' t)
  linarith

theorem alpha_nonneg {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α) :
    0 ≤ α := by
  obtain ⟨a, ha⟩ := M.Γ_nonempty (Classical.arbitrary S)
  set s := Classical.arbitrary S
  have h := hα s a s a ha ha
  have e : ∑ t, min (M.P s a t) (M.P s a t) = 1 := by simp [M.P_sum]
  linarith

theorem sp_T_iterate_sub_le {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (v w : S → ℝ) (n : ℕ) :
    sp (fun s => M.T^[n] v s - M.T^[n] w s) ≤ (M.β * α) ^ n * sp (fun s => v s - w s) := by
  have hc : 0 ≤ M.β * α := mul_nonneg M.β_nonneg (M.alpha_nonneg hα)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    calc sp (fun s => M.T (M.T^[n] v) s - M.T (M.T^[n] w) s)
        ≤ M.β * α * sp (fun s => M.T^[n] v s - M.T^[n] w s) := M.sp_T_sub_le hα _ _
      _ ≤ M.β * α * ((M.β * α) ^ n * sp (fun s => v s - w s)) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = (M.β * α) ^ n * (M.β * α) * sp (fun s => v s - w s) := by ring

/-- **Strong convergence**: `sp(TⁿV − v*) ≤ (βα)ⁿ sp(V − v*)`. -/
theorem sp_iterate_sub_vstar (hβ : M.β < 1) {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (v : S → ℝ) (n : ℕ) :
    sp (fun s => M.T^[n] v s - M.vstar hβ s) ≤
      (M.β * α) ^ n * sp (fun s => v s - M.vstar hβ s) := by
  have h := M.sp_T_iterate_sub_le hα v (M.vstar hβ) n
  have e : M.T^[n] (M.vstar hβ) = M.vstar hβ :=
    Function.iterate_fixed (M.T_vstar hβ) n
  rwa [e] at h

/-- **Relative values converge at rate `βα`**: `|rel(TⁿV)(s) − rel(v*)(s)| ≤ (βα)ⁿ sp(V − v*)`. -/
theorem rel_converges (hβ : M.β < 1) {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (s₀ : S) (v : S → ℝ) (n : ℕ) (s : S) :
    |rel s₀ (M.T^[n] v) s - rel s₀ (M.vstar hβ) s| ≤
      (M.β * α) ^ n * sp (fun s => v s - M.vstar hβ s) := by
  refine le_trans ?_ (M.sp_iterate_sub_vstar hβ hα v n)
  have := abs_sub_le_sp (fun s => M.T^[n] v s - M.vstar hβ s) s s₀
  simp only [rel]
  convert this using 2
  ring

/-- **The MacQueen–Porteus bound**: a policy greedy for `v` is within `β/(1 − β)·sp(Tv − v)` of
optimal. -/
theorem policy_error (hβ : M.β < 1) {v : S → ℝ} {σ : S → A} (hσ : M.IsGreedy σ v) (s : S) :
    0 ≤ M.vstar hβ s - M.vσ hβ σ s ∧
      M.vstar hβ s - M.vσ hβ σ s ≤ M.β / (1 - M.β) * sp (fun s => M.T v s - v s) := by
  have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
  have hpol : M.IsPolicy σ := fun s => (hσ s).1
  refine ⟨sub_nonneg.2 (M.vσ_le_vstar hβ hpol s), ?_⟩
  set d : S → ℝ := fun s => M.T v s - v s
  set hi := univ.sup' univ_nonempty d
  set lo := univ.inf' univ_nonempty d
  have hhi : ∀ s, M.T v s ≤ v s + hi := fun s => by linarith [le_sup'_sp d s]
  have hlo : ∀ s, v s + lo ≤ M.T v s := fun s => by linarith [inf'_le_sp d s]
  set kh := M.β * hi / (1 - M.β)
  set kl := M.β * lo / (1 - M.β)
  have ekh : M.β * hi + M.β * kh = kh := by simp only [kh]; field_simp; ring
  have ekl : M.β * lo + M.β * kl = kl := by simp only [kl]; field_simp; ring
  -- `v* ≤ Tv + βhi/(1 − β)`
  have hup : M.vstar hβ ≤ fun s => M.T v s + kh := by
    refine M.vstar_le_of_T_le hβ fun s => ?_
    rw [T_add_const]
    have h1 := M.T_mono (fun s => hhi s) s
    rw [T_add_const] at h1
    simp only at h1 ⊢
    linarith
  -- `v_σ ≥ Tv + βlo/(1 − β)`
  have hdown : (fun s => M.T v s + kl) ≤ M.vσ hβ σ := by
    refine M.le_vσ_of_le hβ σ fun s => ?_
    rw [Tσ_add_const]
    have h1 := M.Tσ_mono σ (fun s => hlo s) s
    rw [Tσ_add_const, M.Tσ_eq_T_of_greedy hσ] at h1
    simp only at h1 ⊢
    have h2 : M.Tσ σ (M.T v) s = M.Tσ σ (M.T v) s := rfl
    linarith
  have h1 := hup s
  have h2 := hdown s
  simp only at h1 h2
  have e : M.β / (1 - M.β) * sp d = kh - kl := by
    simp only [sp, kh, kl, hi, lo]
    field_simp
  rw [e]
  linarith

/-- The relative value iterates `V_n = rel(TⁿV₀)`. -/
noncomputable def relIter (s₀ : S) (V₀ : S → ℝ) (n : ℕ) : S → ℝ := rel s₀ (M.T^[n] V₀)

omit [Nonempty S] in
theorem relIter_succ (s₀ : S) (V₀ : S → ℝ) (n : ℕ) :
    M.relIter s₀ V₀ (n + 1) = rel s₀ (M.T (M.relIter s₀ V₀ n)) := by
  simp only [relIter]
  rw [← M.relT_iterate s₀ V₀ (n + 1), ← M.relT_iterate s₀ V₀ n, Function.iterate_succ_apply']

theorem sp_T_relIter_sub (s₀ : S) (V₀ : S → ℝ) (n : ℕ) :
    sp (fun s => M.T (M.relIter s₀ V₀ n) s - M.relIter s₀ V₀ n s) =
      sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) := by
  rw [M.relIter_succ]
  have := sp_add_const (fun s => rel s₀ (M.T (M.relIter s₀ V₀ n)) s - M.relIter s₀ V₀ n s)
    (M.T (M.relIter s₀ V₀ n) s₀)
  rw [← this]
  congr 1
  funext s
  simp only [rel]
  ring

/-- **Bray's stopping rule**: the policy greedy for `V_n` is `ε`-optimal as soon as
`β/(1 − β)·sp(V_{n+1} − V_n) ≤ ε`. -/
theorem stopping_rule (hβ : M.β < 1) (s₀ : S) (V₀ : S → ℝ) (n : ℕ) {σ : S → A}
    (hσ : M.IsGreedy σ (M.relIter s₀ V₀ n)) (s : S) :
    M.vstar hβ s - M.vσ hβ σ s ≤
      M.β / (1 - M.β) * sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) := by
  have h := (M.policy_error hβ hσ s).2
  rwa [M.sp_T_relIter_sub] at h

/-- **Bray's stopping rule in the supremum norm**: if `|V_{n+1}(s) − V_n(s)| ≤ ε(1 − β)/(2β)`
for all `s`, the policy greedy for `V_n` is `ε`-optimal. -/
theorem stopping_rule_sup (hβ : M.β < 1) (hβ0 : 0 < M.β) {ε : ℝ} (s₀ : S) (V₀ : S → ℝ) (n : ℕ)
    (hstop : ∀ s, |M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s| ≤ ε * (1 - M.β) / (2 * M.β))
    {σ : S → A} (hσ : M.IsGreedy σ (M.relIter s₀ V₀ n)) (s : S) :
    M.vstar hβ s - M.vσ hβ σ s ≤ ε := by
  have hβ1 : 0 < 1 - M.β := sub_pos.2 hβ
  have hsp : sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) ≤
      ε * (1 - M.β) / M.β := by
    refine sp_le fun x y => ?_
    have h1 := abs_le.1 (hstop x)
    have h2 := abs_le.1 (hstop y)
    have e : ε * (1 - M.β) / M.β = 2 * (ε * (1 - M.β) / (2 * M.β)) := by field_simp
    rw [e]
    linarith [h1.2, h2.1]
  refine (M.stopping_rule hβ s₀ V₀ n hσ s).trans ?_
  calc M.β / (1 - M.β) * sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s)
      ≤ M.β / (1 - M.β) * (ε * (1 - M.β) / M.β) :=
        mul_le_mul_of_nonneg_left hsp (div_nonneg M.β_nonneg hβ1.le)
    _ = ε := by field_simp

/-- The stopping statistic decays geometrically at rate `βα`. -/
theorem sp_relIter_succ_sub_le {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (s₀ : S) (V₀ : S → ℝ) (n : ℕ) :
    sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) ≤
      (M.β * α) ^ n * sp (fun s => M.T V₀ s - V₀ s) := by
  have e : (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) =
      fun s => (M.T^[n] (M.T V₀) s - M.T^[n] V₀ s) +
        -(M.T^[n + 1] V₀ s₀ - M.T^[n] V₀ s₀) := by
    funext s
    simp only [relIter, rel, Function.iterate_succ_apply]
    ring
  rw [e, sp_add_const]
  exact M.sp_T_iterate_sub_le hα _ _ n

/-- **Relative value iteration stops**: for `β < 1` the stopping statistic tends to `0`, so any
positive tolerance is met after finitely many steps. -/
theorem stopping_eventually (hβ : M.β < 1) (s₀ : S) (V₀ : S → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, sp (fun s => M.relIter s₀ V₀ (n + 1) s - M.relIter s₀ V₀ n s) < δ := by
  have hlim : Tendsto (fun n : ℕ => (M.β * 1) ^ n * sp (fun s => M.T V₀ s - V₀ s)) atTop
      (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg hβ).mul_const
      (sp (fun s => M.T V₀ s - V₀ s))
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  exact lt_of_le_of_lt (M.sp_relIter_succ_sub_le (fun s a s' a' _ _ =>
    M.dobrushin_le_one s a s' a') s₀ V₀ n) hn

end MDP

end DPExtensions.RelativeValueIteration
