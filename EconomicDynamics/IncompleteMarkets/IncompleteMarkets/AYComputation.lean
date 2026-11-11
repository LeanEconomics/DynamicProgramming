/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.AYFirm
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# §17.1.4: the computation algorithm and the Lorenz curve and Gini coefficient

Miao, §17.1.4, pp. 564–569. The algorithm's numerical steps (solving the dynamic programme on a
grid, simulating 100,000 households, Aiyagari's calibrated numbers, Example 17.1.1 and
Figure 17.2) are computational and not formalised; the precise mathematical claims they contain
are proved here.

* `ay_bisect`, `ay_bisect_direction`, `ay_bisect_fixed` (Step 6): the update
  `r¹ = ½(r⁰ + F_K(Ea(r⁰), 1) − δ)` lowers `r` when `Ea(r⁰) > K(r⁰)` and raises it when
  `Ea(r⁰) < K(r⁰)`; `r¹ = r⁰` iff the asset market clears, `Ea(r⁰) = K(r⁰)`.
* `ay_gridUpdate`, `ay_gridUpdate_rect`, `ay_gridUpdate_mass` (Step 4, first method): the grid
  iteration `λ_{t+1}(a′, l′) = Σ_l Σ_{a : g(a,l) = a′} λ_t(a, l)π(l, l′)` is the discrete form
  of (17.7) on rectangles and preserves total mass.
* `ay_damp`, `ay_damp_fixed`, `ay_damp_between` (Ljungqvist–Sargent, p. 567): the damped update
  `K² = ξK¹ + (1 − ξ)K⁰` lies between `K⁰` and `K¹`, and `K² = K⁰` iff `K¹ = K⁰`.
* `ay_lorenz`, `ay_gini`, `ay_gini_eq_area` (p. 568): the Lorenz curve `z_i = Σ_{j≤i} y_j/Σ y_j`
  and the Gini coefficient, twice the area between the 45 degree line and the piecewise linear
  Lorenz curve.
* `ay_lorenz_zero`, `ay_lorenz_n`, `ay_lorenz_mono`, `ay_lorenz_le_diag`: `z` increases to
  `z_n = 1` and lies below the diagonal (`z_i ≤ i/n`) for sorted data.
* `ay_gini_nonneg`, `ay_gini_le`, `ay_gini_equal`: for `x_i ≥ 0` with positive total,
  `0 ≤ G ≤ 1 − 1/n ≤ 1`; complete equality gives `G = 0`.
* `ay_gini_concentrated`, `ay_gini_concentrated_ne_one`, `ay_gini_concentrated_tendsto`:
  complete concentration gives `G = 1 − 1/n`, **not** `1` as the book states; `G → 1` as
  `n → ∞`.

Indexing: the book's sorted sample `y_1 ≤ … ≤ y_n` is `y 0 ≤ … ≤ y (n − 1)` and its `z_i` is
`ay_lorenz y n i = (y 0 + … + y (i − 1))/(y 0 + … + y (n − 1))`, `i = 0, …, n`.
-/

namespace Miao.IncompleteMarkets

open Filter Topology

/-- Miao, Step 6, p. 566: the bisection update `r¹ = ½(r⁰ + F_K(Ea(r⁰), 1) − δ)`
(Cobb–Douglas, `L = 1`). -/
noncomputable def ay_bisect (A α δ r0 Ea : ℝ) : ℝ := (r0 + (ay_cdFK A α Ea 1 - δ)) / 2

/-- Miao, Step 6, p. 566: if `Ea(r⁰) > K(r⁰)` then `r¹ < r⁰`; if `Ea(r⁰) < K(r⁰)` then
`r¹ > r⁰` (`K(r⁰) = K^d(r⁰)` with `L = 1`, `Ea(r⁰) > 0`). -/
theorem ay_bisect_direction {A α δ r0 Ea : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hr : -δ < r0) (hE : 0 < Ea) :
    (ay_Kd A α δ 1 r0 < Ea → ay_bisect A α δ r0 Ea < r0) ∧
      (Ea < ay_Kd A α δ 1 r0 → r0 < ay_bisect A α δ r0 Ea) := by
  have hx : 0 < α * A / (r0 + δ) := div_pos (mul_pos hα0 hA) (by linarith)
  have hKd : 0 < ay_Kd A α δ 1 r0 := mul_pos one_pos (Real.rpow_pos_of_pos hx _)
  have hfoc := ay_Kd_foc hA hα0 hα1 one_pos hr
  have hanti := ay_cdFK_strictAnti hA hα0 hα1 (one_pos : (0 : ℝ) < 1)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hanti hKd hE h
    simp only at this
    rw [ay_bisect]
    linarith
  · have := hanti hE hKd h
    simp only at this
    rw [ay_bisect]
    linarith

/-- Miao, Steps 6–7, p. 566: the bisection update has `r¹ = r⁰` exactly when the asset market
clears, `Ea(r⁰) = K(r⁰)`. -/
theorem ay_bisect_fixed {A α δ r0 Ea : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1)
    (hr : -δ < r0) (hE : 0 < Ea) : ay_bisect A α δ r0 Ea = r0 ↔ Ea = ay_Kd A α δ 1 r0 := by
  constructor
  · intro h
    have : ay_cdFK A α Ea 1 = r0 + δ := by rw [ay_bisect] at h; linarith
    exact ay_Kd_unique hA hα0 hα1 one_pos hr hE this
  · intro h
    rw [ay_bisect, h, ay_Kd_foc hA hα0 hα1 one_pos hr]
    ring

/-- Miao, p. 567: the grid iteration
`λ_{t+1}(a′, l′) = Σ_l Σ_{a : g(a,l) = a′} λ_t(a, l)π(l, l′)` on finite grids. -/
def ay_gridUpdate {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] (g : α × ι → α)
    (pr : ι → ι → ℝ) (lam : α × ι → ℝ) (q : α × ι) : ℝ :=
  ∑ l, ∑ a ∈ Finset.univ.filter (fun a => g (a, l) = q.1), lam (a, l) * pr l q.2

/-- Miao, p. 567: the grid iteration is the discrete form of (17.7):
`λ_{t+1}(A × B) = Σ_{(a,l)} 1_{g(a,l) ∈ A} π(l, B) λ_t(a, l)`. -/
theorem ay_gridUpdate_rect {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]
    (g : α × ι → α) (pr : ι → ι → ℝ) (lam : α × ι → ℝ) (A : Finset α) (B : Finset ι) :
    ∑ a' ∈ A, ∑ l' ∈ B, ay_gridUpdate g pr lam (a', l') =
      ∑ l, ∑ a ∈ Finset.univ.filter (fun a => g (a, l) ∈ A), lam (a, l) * ∑ l' ∈ B, pr l l' := by
  simp only [ay_gridUpdate]
  have hR : ∀ l, ∑ a ∈ Finset.univ.filter (fun a => g (a, l) ∈ A),
      lam (a, l) * ∑ l' ∈ B, pr l l' = ∑ a' ∈ A,
        ∑ a ∈ Finset.univ.filter (fun a => g (a, l) = a'), ∑ l' ∈ B, lam (a, l) * pr l l' :=
    fun l => by
      rw [← Finset.sum_fiberwise_eq_sum_filter Finset.univ A (fun a => g (a, l))]
      simp_rw [Finset.mul_sum]
  simp_rw [hR]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]

/-- Miao, p. 567: if each row of `π` sums to one, the grid iteration preserves total mass. -/
theorem ay_gridUpdate_mass {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]
    (g : α × ι → α) (pr : ι → ι → ℝ) (hpr : ∀ l, ∑ l', pr l l' = 1) (lam : α × ι → ℝ) :
    ∑ q, ay_gridUpdate g pr lam q = ∑ q, lam q := by
  classical
  have h := ay_gridUpdate_rect g pr lam Finset.univ Finset.univ
  rw [Fintype.sum_prod_type, h, Fintype.sum_prod_type]
  simp only [hpr, mul_one, Finset.mem_univ, Finset.filter_true]
  rw [Finset.sum_comm]

/-- Miao, p. 567 (Ljungqvist–Sargent): the damped update `K² = ξK¹ + (1 − ξ)K⁰`. -/
def ay_damp (ξ K0 K1 : ℝ) : ℝ := ξ * K1 + (1 - ξ) * K0

/-- Miao, p. 567: for `ξ ∈ (0, 1)`, `K² = K⁰` iff `K¹ = K⁰`: the damped iteration has the same
fixed points (`K¹(K⁰) = K⁰`, market clearing) as the undamped one. -/
theorem ay_damp_fixed {ξ K0 K1 : ℝ} (hξ : 0 < ξ) : ay_damp ξ K0 K1 = K0 ↔ K1 = K0 := by
  rw [ay_damp]
  constructor
  · intro h
    have : ξ * (K1 - K0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith
  · intro h; rw [h]; ring

/-- Miao, p. 567: for `ξ ∈ (0, 1)`, `K²` lies between `K⁰` and `K¹`. -/
theorem ay_damp_between {ξ K0 K1 : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    min K0 K1 ≤ ay_damp ξ K0 K1 ∧ ay_damp ξ K0 K1 ≤ max K0 K1 := by
  rw [ay_damp]
  have h1 := min_le_left K0 K1
  have h2 := min_le_right K0 K1
  have h3 := le_max_left K0 K1
  have h4 := le_max_right K0 K1
  constructor <;> nlinarith

/-- Miao, p. 568: the **Lorenz curve** `z_i = Σ_{j<i} y_j / Σ_{j<n} y_j` of the sorted sample
`y 0 ≤ … ≤ y (n − 1)`, plotted against `i/n`. -/
noncomputable def ay_lorenz (y : ℕ → ℝ) (n i : ℕ) : ℝ :=
  (∑ j ∈ Finset.range i, y j) / ∑ j ∈ Finset.range n, y j

/-- Miao, p. 568: the **Gini coefficient** of the sample, computed from the Lorenz curve:
`G = 1 − (1/n) Σ_{i<n} (z_i + z_{i+1})`. -/
noncomputable def ay_gini (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 - (1 / n) * ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1))

/-- Miao, p. 568: the Gini coefficient is two times the area between the 45 degree line (area
`1/2` beneath it) and the piecewise linear Lorenz curve through `(i/n, z_i)` (trapezoid areas
`(1/n)(z_i + z_{i+1})/2`). -/
theorem ay_gini_eq_area (y : ℕ → ℝ) (n : ℕ) :
    ay_gini y n = 2 * (1 / 2 - ∑ i ∈ Finset.range n,
      (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) := by
  rw [ay_gini]
  simp only [div_eq_mul_inv, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem ay_lorenz_zero (y : ℕ → ℝ) (n : ℕ) : ay_lorenz y n 0 = 0 := by simp [ay_lorenz]

/-- Miao, p. 568: `z_n = 1` (positive total). -/
theorem ay_lorenz_n {y : ℕ → ℝ} {n : ℕ} (hT : 0 < ∑ j ∈ Finset.range n, y j) :
    ay_lorenz y n n = 1 := div_self hT.ne'

/-- Miao, p. 568: for `y ≥ 0`, `{z_i}` is an increasing sequence. -/
theorem ay_lorenz_mono {y : ℕ → ℝ} {n : ℕ} (hy : ∀ j, 0 ≤ y j)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) (i : ℕ) : ay_lorenz y n i ≤ ay_lorenz y n (i + 1) := by
  rw [ay_lorenz, ay_lorenz, Finset.sum_range_succ]
  exact div_le_div_of_nonneg_right (by linarith [hy i]) hT.le

/-- Miao, p. 568: for sorted data the Lorenz curve lies below the 45 degree line,
`z_i ≤ i/n` for `i ≤ n`. -/
theorem ay_lorenz_le_diag {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) {i : ℕ} (hi : i ≤ n) :
    ay_lorenz y n i ≤ i / n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact h
  rcases hi.lt_or_eq with hlt | heq
  · set a := ∑ j ∈ Finset.range i, y j
    set b := ∑ k ∈ Finset.Ico i n, y k
    have hab : a + b = ∑ j ∈ Finset.range n, y j := Finset.sum_range_add_sum_Ico y hi
    have ha : a ≤ (i : ℝ) * y i := by
      have := Finset.sum_le_card_nsmul (Finset.range i) y (y i)
        fun j hj => hsort j i (Finset.mem_range.1 hj).le hlt
      simpa using this
    have hb : ((n - i : ℕ) : ℝ) * y i ≤ b := by
      have := Finset.card_nsmul_le_sum (Finset.Ico i n) y (y i)
        fun k hk => hsort i k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2
      simpa using this
    rw [Nat.cast_sub hi] at hb
    have hni : (0 : ℝ) ≤ n - i := by
      have : (i : ℝ) ≤ n := by exact_mod_cast hi
      linarith
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h1 := mul_le_mul_of_nonneg_left ha hni
    have h2 := mul_le_mul_of_nonneg_left hb hi0
    rw [ay_lorenz, ← hab, div_le_div_iff₀ (by linarith) (by exact_mod_cast hn)]
    nlinarith
  · subst heq
    rw [ay_lorenz_n hT, div_self (by exact_mod_cast hn.ne')]

theorem ay_sum_odd (n : ℕ) : ∑ i ∈ Finset.range n, ((2 * i + 1 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Miao, p. 568: "if `x_i ≥ 0` for all `i`, then the Gini coefficient is between zero and
one": `G ≥ 0` for sorted data with positive total. -/
theorem ay_gini_nonneg {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) : 0 ≤ ay_gini y n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact h
  have hS : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) ≤ n := by
    calc ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1))
        ≤ ∑ i ∈ Finset.range n, (((2 * i + 1 : ℕ) : ℝ) / n) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have h1 := ay_lorenz_le_diag hsort hT hi'.le
          have h2 := ay_lorenz_le_diag hsort hT (Nat.succ_le_of_lt hi')
          have e : (((2 * i + 1 : ℕ) : ℝ)) / n = i / n + ((i : ℝ) + 1) / n := by
            push_cast; ring
          rw [e]
          simp only [Nat.succ_eq_add_one] at h2
          push_cast at h2
          linarith
      _ = n := by
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul, ay_sum_odd]
          field_simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ay_gini]
  have : 1 / (n : ℝ) * ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hnpos]
    exact hS
  linarith

/-- Miao, p. 568: for `x_i ≥ 0` with positive total, `G ≤ 1 − 1/n ≤ 1`. -/
theorem ay_gini_le {y : ℕ → ℝ} {n : ℕ} (hy : ∀ j, 0 ≤ y j)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) : ay_gini y n ≤ 1 - 1 / n ∧ ay_gini y n ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact ⟨n - 1, by omega⟩
  have hz : ∀ i, 0 ≤ ay_lorenz y (m + 1) i := fun i =>
    div_nonneg (Finset.sum_nonneg fun j _ => hy j) hT.le
  have hS : 1 ≤ ∑ i ∈ Finset.range (m + 1),
      (ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1)) := by
    rw [Finset.sum_range_succ, ay_lorenz_n hT]
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.range m) =>
      add_nonneg (hz i) (hz (i + 1))
    linarith [hz m]
  have hnpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have h1 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (m + 1),
      (ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1)) := by
    have := mul_le_mul_of_nonneg_left hS (one_div_pos.2 hnpos).le
    simpa using this
  refine ⟨by rw [ay_gini]; linarith, ?_⟩
  rw [ay_gini]
  linarith [one_div_pos.2 hnpos]

/-- Miao, p. 568: "for complete equality of income the Gini coefficient is zero". -/
theorem ay_gini_equal {y : ℕ → ℝ} {n : ℕ} {c : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hy : ∀ j, j < n → y j = c) : ay_gini y n = 0 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∀ i, i ≤ n → ∑ j ∈ Finset.range i, y j = i * c := fun i hi => by
    have : ∑ j ∈ Finset.range i, y j = ∑ j ∈ Finset.range i, c :=
      Finset.sum_congr rfl fun j hj => hy j ((Finset.mem_range.1 hj).trans_le hi)
    rw [this]
    simp
  have hz : ∀ i, i ≤ n → ay_lorenz y n i = i / n := fun i hi => by
    rw [ay_lorenz, hsum i hi, hsum n le_rfl]
    field_simp
  have hS : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) = n := by
    rw [Finset.sum_congr rfl fun i hi => by
      rw [hz i (Finset.mem_range.1 hi).le, hz (i + 1) (Finset.mem_range.1 hi)]]
    have : ∀ i : ℕ, (i : ℝ) / n + ((i + 1 : ℕ) : ℝ) / n = ((2 * i + 1 : ℕ) : ℝ) / n := by
      intro i; push_cast; ring
    simp_rw [this]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ay_sum_odd]
    field_simp
  rw [ay_gini, hS, one_div, inv_mul_cancel₀ hnr.ne', sub_self]

/-- Miao, p. 568, corrected: under complete concentration (the richest of `n = m + 1` people has
all income `Y > 0`) the Gini coefficient is `1 − 1/n`. -/
theorem ay_gini_concentrated {y : ℕ → ℝ} {m : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hy : ∀ j, j < m → y j = 0) (hm : y m = Y) : ay_gini y (m + 1) = 1 - 1 / (m + 1 : ℕ) := by
  have hpre : ∀ i, i ≤ m → ∑ j ∈ Finset.range i, y j = 0 := fun i hi =>
    Finset.sum_eq_zero fun j hj => hy j ((Finset.mem_range.1 hj).trans_le hi)
  have hT : ∑ j ∈ Finset.range (m + 1), y j = Y := by
    rw [Finset.sum_range_succ, hpre m le_rfl, hm, zero_add]
  have hS : ∑ i ∈ Finset.range (m + 1),
      (ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1)) = 1 := by
    rw [Finset.sum_range_succ, ay_lorenz_n (hT ▸ hY)]
    have h0 : ∀ i ∈ Finset.range m, ay_lorenz y (m + 1) i + ay_lorenz y (m + 1) (i + 1) = 0 :=
      fun i hi => by
        have hi' := Finset.mem_range.1 hi
        rw [ay_lorenz, ay_lorenz, hpre i hi'.le, hpre (i + 1) hi', zero_div, add_zero]
    rw [Finset.sum_eq_zero h0, ay_lorenz, hpre m le_rfl, zero_div]
    ring
  rw [ay_gini, hS, mul_one]

/-- Miao, p. 568: the book's "for complete concentration ... the Gini coefficient is `1`" is
false for a finite sample of `n ≥ 1` people. -/
theorem ay_gini_concentrated_ne_one {y : ℕ → ℝ} {m : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hy : ∀ j, j < m → y j = 0) (hm : y m = Y) : ay_gini y (m + 1) ≠ 1 := by
  rw [ay_gini_concentrated hY hy hm]
  have : (0 : ℝ) < 1 / (m + 1 : ℕ) := by positivity
  intro h
  linarith

/-- Miao, p. 568: under complete concentration the Gini coefficient tends to `1` as the sample
size grows. -/
theorem ay_gini_concentrated_tendsto :
    Tendsto (fun m : ℕ => 1 - 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h
  rw [sub_zero] at h2
  refine h2.congr fun m => ?_
  push_cast
  rfl

end Miao.IncompleteMarkets
