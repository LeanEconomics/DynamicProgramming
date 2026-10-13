/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.Basics

/-!
# The finite-horizon log/Cobb–Douglas economy

SLP Exercise 2.2, p. 12: `f(k) = k^α`, `0 < α < 1`, `U(c) = ln c`.

* `euler_iff_z` (Ex 2.2a): with `z_t = k_t / k_{t−1}^α`, the Euler equation (5) becomes the
  first-order difference equation `αβ(1 − z_t) = z_t(1 − z_{t+1})`.
* `savingRate`, `savingRate_succ`, `z_unique` (Ex 2.2b): with `n` periods remaining,
  `s_n = αβ(1 − (αβ)ⁿ)/(1 − (αβ)ⁿ⁺¹)`; it is the unique solution with `s₀ = 0` (the boundary
  condition `z_{T+1} = 0`).
* `path`, `path_feasible`, `path_euler`, `path_optimal`, `path_unique` (Ex 2.2c): the path
  `k_{t+1} = s_{T−t} k_t^α` of (7) satisfies (5)–(6), and is therefore the unique optimum.
* `savingRate_tendsto` (equation (8), p. 12): `s_n → αβ`.
-/

open Finset Set Filter Topology Real

namespace StokeyLucasPrescott.Overview

/-- **Ex 2.2a.** With `A = k_{t−1}^α`, `B = k_t^α` and `z_t = k_t / A`, `z_{t+1} = k_{t+1} / B`,
the Euler equation `β α k_t^{α−1} / (k_t^α − k_{t+1}) = 1/(k_{t−1}^α − k_t)` is equivalent to
`αβ(1 − z_t) = z_t (1 − z_{t+1})`. -/
theorem euler_iff_z {α β a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a ^ α)
    (hbc : c < b ^ α) :
    β * (α * b ^ (α - 1)) * (b ^ α - c)⁻¹ = (a ^ α - b)⁻¹ ↔
      α * β * (1 - b / a ^ α) = b / a ^ α * (1 - c / b ^ α) := by
  have hA : 0 < a ^ α := rpow_pos_of_pos ha α
  have hB : 0 < b ^ α := rpow_pos_of_pos hb α
  have hb1 : b ^ (α - 1) = b ^ α / b := rpow_sub_one hb.ne' α
  rw [hb1]
  have h1 : (b ^ α - c) ≠ 0 := (sub_pos.2 hbc).ne'
  have h2 : (a ^ α - b) ≠ 0 := (sub_pos.2 hab).ne'
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination h
  · intro h
    field_simp at h ⊢
    linear_combination h

/-- The saving rate with `n` periods remaining, `s_n = αβ(1 − (αβ)ⁿ)/(1 − (αβ)ⁿ⁺¹)`. -/
noncomputable def savingRate (α β : ℝ) (n : ℕ) : ℝ :=
  α * β * (1 - (α * β) ^ n) / (1 - (α * β) ^ (n + 1))

theorem savingRate_zero (α β : ℝ) : savingRate α β 0 = 0 := by simp [savingRate]

/-- The backward recursion `s_{n+1} (1 + αβ − s_n) = αβ`. -/
theorem savingRate_succ {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (n : ℕ) :
    savingRate α β (n + 1) * (1 + α * β - savingRate α β n) = α * β := by
  have hp : ∀ m : ℕ, (α * β) ^ m < 1 → 1 - (α * β) ^ m ≠ 0 := fun m h => (sub_pos.2 h).ne'
  have hlt : ∀ m : ℕ, 0 < m → (α * β) ^ m < 1 := fun m hm => pow_lt_one₀ h0.le h1 hm.ne'
  have e1 := hp (n + 1) (hlt _ (by omega))
  have e2 := hp (n + 2) (hlt _ (by omega))
  simp only [savingRate]
  field_simp
  ring

theorem savingRate_pos {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {n : ℕ} (hn : 0 < n) :
    0 < savingRate α β n := by
  have := pow_lt_one₀ h0.le h1 hn.ne'
  have := pow_lt_one₀ h0.le h1 (n := n + 1) (by omega)
  unfold savingRate
  positivity

theorem savingRate_nonneg {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (n : ℕ) :
    0 ≤ savingRate α β n := by
  rcases n with _ | n
  · simp [savingRate_zero]
  · exact (savingRate_pos h0 h1 (Nat.succ_pos n)).le

theorem savingRate_lt_one {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (n : ℕ) :
    savingRate α β n < 1 := by
  have hn1 : (α * β) ^ (n + 1) < 1 := pow_lt_one₀ h0.le h1 (by omega)
  unfold savingRate
  rw [div_lt_one (sub_pos.2 hn1), pow_succ]
  have := pow_le_one₀ h0.le h1.le (n := n)
  nlinarith [pow_nonneg h0.le n]

/-- **Ex 2.2b.** The difference equation `αβ(1 − z_t) = z_t(1 − z_{t+1})` with the boundary
condition `z_{T+1} = 0` has the unique solution `z_t = s_{T+1−t}`. -/
theorem z_unique {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {z : ℕ → ℝ}
    (hT : z (T + 1) = 0) (hz : ∀ t, 1 ≤ t → t ≤ T → α * β * (1 - z t) = z t * (1 - z (t + 1))) :
    ∀ t, 1 ≤ t → t ≤ T + 1 → z t = savingRate α β (T + 1 - t) := by
  have key : ∀ n ≤ T, z (T + 1 - n) = savingRate α β n := by
    intro n hn
    induction n with
    | zero => simp [hT, savingRate_zero]
    | succ n ih =>
      have hih := ih (by omega)
      have hrec := hz (T - n) (by omega) (by omega)
      have heq : T - n + 1 = T + 1 - n := by omega
      rw [heq, hih] at hrec
      have hs := savingRate_succ h0 h1 n
      have hd : 1 + α * β - savingRate α β n ≠ 0 := by
        have := savingRate_lt_one h0 h1 n
        intro h; linarith
      have hidx : T + 1 - (n + 1) = T - n := by omega
      rw [hidx]
      have hprod : (z (T - n) - savingRate α β (n + 1)) * (1 + α * β - savingRate α β n) = 0 := by
        linear_combination -hrec - hs
      exact sub_eq_zero.1 ((mul_eq_zero.1 hprod).resolve_right hd)
  intro t ht1 htT
  have := key (T + 1 - t) (by omega)
  rwa [show T + 1 - (T + 1 - t) = t by omega] at this

/-- The path (7): `k₀` given, `k_{t+1} = s_{T−t} k_t^α`. -/
noncomputable def path (α β : ℝ) (T : ℕ) (k₀ : ℝ) : ℕ → ℝ
  | 0 => k₀
  | t + 1 => savingRate α β (T - t) * path α β T k₀ t ^ α

theorem path_pos {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∀ t ≤ T, 0 < path α β T k₀ t := by
  intro t ht
  induction t with
  | zero => exact hk₀
  | succ t ih =>
    have := ih (by omega)
    simp only [path]
    exact mul_pos (savingRate_pos h0 h1 (by omega)) (rpow_pos_of_pos this α)

theorem path_terminal {α β : ℝ} (T : ℕ) (k₀ : ℝ) : path α β T k₀ (T + 1) = 0 := by
  simp [path, savingRate_zero]

/-- Consumption along the path, `c_t = (1 − s_{T−t}) k_t^α`. -/
theorem path_consumption {α β : ℝ} (T : ℕ) (k₀ : ℝ) (t : ℕ) :
    path α β T k₀ t ^ α - path α β T k₀ (t + 1) =
      (1 - savingRate α β (T - t)) * path α β T k₀ t ^ α := by
  simp only [path]
  ring

/-- **Ex 2.2c (feasibility).** The path (7) is feasible with strictly positive consumption. -/
theorem path_feasible {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {k₀ : ℝ}
    (hk₀ : 0 < k₀) :
    Feasible (Ioi 0) (fun k => k ^ α) T k₀ (path α β T k₀) := by
  refine ⟨rfl, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [path]
    exact mul_nonneg (savingRate_nonneg h0 h1 _) (rpow_nonneg (path_pos h0 h1 hk₀ t ht).le α)
  · rw [Set.mem_Ioi, path_consumption]
    exact mul_pos (sub_pos.2 (savingRate_lt_one h0 h1 _))
      (rpow_pos_of_pos (path_pos h0 h1 hk₀ t ht) α)

/-- **Ex 2.2c (Euler).** The path (7) satisfies the Euler equation (5) for `t = 1, …, T`. -/
theorem path_euler {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {k₀ : ℝ}
    (hk₀ : 0 < k₀) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
    β * (α * path α β T k₀ t ^ (α - 1)) *
        (path α β T k₀ t ^ α - path α β T k₀ (t + 1))⁻¹ =
      (path α β T k₀ (t - 1) ^ α - path α β T k₀ t)⁻¹ := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hks := path_pos h0 h1 hk₀ (T := T) s (by omega)
  have hkt := path_pos h0 h1 hk₀ (s + 1) htT
  have hfe := path_feasible h0 h1 hk₀ (T := T)
  have hc1 := (hfe.2 s (by omega)).2
  have hc2 := (hfe.2 (s + 1) htT).2
  rw [Set.mem_Ioi] at hc1 hc2
  rw [euler_iff_z hks hkt (by linarith) (by linarith)]
  -- the ratios are saving rates
  have hz1 : path α β T k₀ (s + 1) / path α β T k₀ s ^ α = savingRate α β (T - s) := by
    simp only [path]
    field_simp [(rpow_pos_of_pos hks α).ne']
  have hz2 : path α β T k₀ (s + 1 + 1) / path α β T k₀ (s + 1) ^ α =
      savingRate α β (T - (s + 1)) := by
    conv_lhs => rw [path]
    field_simp [(rpow_pos_of_pos hkt α).ne']
  rw [hz1, hz2]
  have hrec := savingRate_succ h0 h1 (T - (s + 1))
  have hidx : T - (s + 1) + 1 = T - s := by omega
  rw [hidx] at hrec
  linarith

/-- **Ex 2.2c.** The path (7) is optimal: it maximizes `∑_{t=0}^T β^t ln(k_t^α − k_{t+1})` over
all feasible paths. -/
theorem path_optimal {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (h1 : α * β < 1)
    {T : ℕ} {k₀ : ℝ} (hk₀ : 0 < k₀) {k : ℕ → ℝ} (hk : Feasible (Ioi 0) (fun k => k ^ α) T k₀ k) :
    planValue β log (fun k => k ^ α) T k ≤ planValue β log (fun k => k ^ α) T (path α β T k₀) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hfe := path_feasible h0 h1 hk₀ (T := T)
  refine euler_optimal (U' := fun c => c⁻¹) (f' := fun k => α * k ^ (α - 1)) hβ.le
    strictConcaveOn_log_Ioi.concaveOn (strictConcaveOn_rpow hα hα1).concaveOn hfe hk₀.le
    (fun t ht => hasDerivAt_log (Set.mem_Ioi.1 (hfe.2 t ht).2).ne')
    (fun t ht => (inv_pos.2 (Set.mem_Ioi.1 (hfe.2 t ht).2)).le)
    (fun t _ ht2 => hasDerivAt_rpow_const (Or.inl (path_pos h0 h1 hk₀ t ht2).ne'))
    (fun t ht1 ht2 => by
      have := path_euler h0 h1 hk₀ t ht1 ht2
      simpa [mul_assoc] using this)
    (path_terminal T k₀) hk

/-- **Uniqueness** (SLP p. 11): the path (7) is the only optimum. -/
theorem path_unique {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (h1 : α * β < 1)
    {T : ℕ} {k₀ : ℝ} (hk₀ : 0 < k₀) {k : ℕ → ℝ} (hk : Feasible (Ioi 0) (fun k => k ^ α) T k₀ k)
    (hopt : planValue β log (fun k => k ^ α) T (path α β T k₀) ≤
      planValue β log (fun k => k ^ α) T k) :
    ∀ t ≤ T + 1, k t = path α β T k₀ t := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hfe := path_feasible h0 h1 hk₀ (T := T)
  exact euler_unique (U' := fun c => c⁻¹) (f' := fun k => α * k ^ (α - 1)) hβ
    strictConcaveOn_log_Ioi (strictConcaveOn_rpow hα hα1).concaveOn hfe hk₀.le
    (fun t ht => hasDerivAt_log (Set.mem_Ioi.1 (hfe.2 t ht).2).ne')
    (fun t ht => (inv_pos.2 (Set.mem_Ioi.1 (hfe.2 t ht).2)).le)
    (fun t _ ht2 => hasDerivAt_rpow_const (Or.inl (path_pos h0 h1 hk₀ t ht2).ne'))
    (fun t ht1 ht2 => by
      have := path_euler h0 h1 hk₀ t ht1 ht2
      simpa [mul_assoc] using this)
    (path_terminal T k₀) hk hopt

/-- **Equation (8).** As the horizon recedes the saving rate converges to `αβ`. -/
theorem savingRate_tendsto {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) :
    Tendsto (savingRate α β) atTop (𝓝 (α * β)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  have hp1 : Tendsto (fun n : ℕ => (α * β) ^ (n + 1)) atTop (𝓝 0) :=
    hp.comp (tendsto_add_atTop_nat 1)
  have := ((tendsto_const_nhds (x := α * β)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp1) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  rw [show α * β * (1 - 0) / (1 - 0) = α * β by ring] at this
  exact this

end StokeyLucasPrescott.Overview
