/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Long-term debt: perpetuities with geometrically declining coupons

AKMM, §24.2.2 (24.2), p. 731; §24.4.1 (24.7)–(24.8), pp. 742–743; §24.4.2 (24.11), p. 744;
Appendix 24.A.2, pp. 902–903.

A bond issued in period `t` pays `δ(1 − δ)^{j−1}` in period `t + j`, `j ≥ 1`.

* (24.7): the stock `B_{t+1} = (1 − δ)B_t + I_t` has the closed form
  `B_t = (1 − δ)^t B₀ + Σ_{s<t}(1 − δ)^{t−1−s} I_s` (`eq_24_7`).
* **`B_t` is a sufficient state** (p. 742): the payment due in period `t + j` on all bonds
  outstanding at the start of `t` is `δ(1 − δ)^j B_t`, whatever the issuance history
  (`ltd_payments_sufficient`); in particular the period-`t` coupon is `δB_t` (`ltd_coupon_due`).
* (24.8) with (24.7) gives the repayment budget of (24.11),
  `C = Y − δB + q[B′ − (1 − δ)B]` (`eq_24_8`).
* The present value of one bond at rate `r` is `δ/(δ + r)` (p. 903), the risk-free price
  (`ltd_pv_bond`); the yield `i` of (p. 903) solves `q = δ/(δ + i)` (`ltd_yield`,
  `ltd_yield_iff`); the Macaulay duration is `(1 + i)/(δ + i)` (p. 902, `ltd_duration`); the
  annualised spread is positive iff `i > r` (`ltd_spread_pos_iff`).
* The haircut (24.2) (`eq_24_2`).

On p. 903 "the present value of future payment obligations ... `δB_t/(δ + r)`" is the value one
period before `t` of the payments on `B_t` (equivalently, the value at `t` of the payments
from `t + 1` on of the end-of-period stock `B_{t+1}`); valued at `t` the payments of `B_t`
are worth `δ(1 + r)B_t/(δ + r)` with the current coupon and `δ(1 − δ)B_t/(δ + r)` without it
(`ltd_pv_stock_timing`).
-/

namespace AKMM.SovereignDefault

open Finset

/-- AKMM, (24.7), p. 742: the debt stock `B_{t+1} = (1 − δ)B_t + I_t`, from `B₀` and issuance
`I`. -/
def ltd_stock (δ B₀ : ℝ) (I : ℕ → ℝ) : ℕ → ℝ
  | 0 => B₀
  | t + 1 => (1 - δ) * ltd_stock δ B₀ I t + I t

/-- **AKMM, (24.7)**, p. 742, closed form:
`B_t = (1 − δ)^t B₀ + Σ_{s<t} (1 − δ)^{t−1−s} I_s`. -/
theorem eq_24_7 (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) :
    ltd_stock δ B₀ I t = (1 - δ) ^ t * B₀ + ∑ s ∈ range t, (1 - δ) ^ (t - 1 - s) * I s := by
  induction t with
  | zero => simp [ltd_stock]
  | succ n ih =>
    rw [ltd_stock, ih, sum_range_succ, mul_add, mul_sum]
    have : ∀ s ∈ range n, (1 - δ) * ((1 - δ) ^ (n - 1 - s) * I s) =
        (1 - δ) ^ (n + 1 - 1 - s) * I s := by
      intro s hs
      have hs' : s < n := mem_range.1 hs
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [sum_congr rfl this]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, pow_succ]
    ring

/-- The payment in period `t` on the bonds outstanding at the start of period `0` (`B₀` legacy
bonds, which pay `δ(1 − δ)^t` each in period `t`) and on the bonds issued in periods
`s < t` (`I_s` bonds paying `δ(1 − δ)^{t−s−1}` each). -/
def ltd_payment (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) : ℝ :=
  δ * (1 - δ) ^ t * B₀ + ∑ s ∈ range t, δ * (1 - δ) ^ (t - s - 1) * I s

/-- AKMM, p. 743: the coupon due in period `t` is `δB_t`. -/
theorem ltd_coupon_due (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) :
    ltd_payment δ B₀ I t = δ * ltd_stock δ B₀ I t := by
  rw [ltd_payment, eq_24_7, mul_add, mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun s _ => ?_
    rw [show t - s - 1 = t - 1 - s by omega]
    ring

/-- **AKMM, p. 742: the current stock is a sufficient state.** Absent new issuance, the payment
due in period `t + j` on all bonds outstanding at the start of period `t` (issued before `t`)
is `δ(1 − δ)^j B_t`: it depends on the history only through `B_t`. -/
theorem ltd_payments_sufficient (δ B₀ : ℝ) (I : ℕ → ℝ) (t j : ℕ) :
    δ * (1 - δ) ^ (t + j) * B₀ + ∑ s ∈ range t, δ * (1 - δ) ^ (t + j - s - 1) * I s =
      δ * (1 - δ) ^ j * ltd_stock δ B₀ I t := by
  rw [eq_24_7, mul_add, mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun s hs => ?_
    have hs' : s < t := mem_range.1 hs
    rw [show t + j - s - 1 = j + (t - 1 - s) by omega, pow_add]
    ring

/-- Two issuance histories with the same current stock owe the same future payments. -/
theorem ltd_same_stock_same_payments (δ B₀ B₀' : ℝ) (I I' : ℕ → ℝ) (t : ℕ)
    (h : ltd_stock δ B₀ I t = ltd_stock δ B₀' I' t) (j : ℕ) :
    δ * (1 - δ) ^ (t + j) * B₀ + ∑ s ∈ range t, δ * (1 - δ) ^ (t + j - s - 1) * I s =
      δ * (1 - δ) ^ (t + j) * B₀' + ∑ s ∈ range t, δ * (1 - δ) ^ (t + j - s - 1) * I' s := by
  rw [ltd_payments_sufficient, ltd_payments_sufficient, h]

/-- **AKMM, (24.8)**, p. 743, with (24.7): the budget `C_t + δB_t = Y_t + I_t q_t` with
`I_t = B_{t+1} − (1 − δ)B_t` is the repayment constraint of (24.11),
`C = Y − δB + q[B′ − (1 − δ)B]`. -/
theorem eq_24_8 (δ B₀ : ℝ) (I : ℕ → ℝ) (t : ℕ) (C Y q : ℝ)
    (h : C + δ * ltd_stock δ B₀ I t = Y + I t * q) :
    C = Y - δ * ltd_stock δ B₀ I t +
      q * (ltd_stock δ B₀ I (t + 1) - (1 - δ) * ltd_stock δ B₀ I t) := by
  rw [ltd_stock]
  linarith [mul_comm (I t) q]

/-- The geometric sum `Σ_{j≥0} δ(1 − δ)^j a^{j+1} = δa/(1 − (1 − δ)a)`. -/
theorem ltd_hasSum_coupons {δ a : ℝ} (h0 : 0 ≤ (1 - δ) * a) (h1 : (1 - δ) * a < 1) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j * a ^ (j + 1)) (δ * a / (1 - (1 - δ) * a)) := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (δ * a)
  convert this using 1
  · funext j; rw [mul_pow, pow_succ]; ring
  · rw [div_eq_mul_inv]

/-- **AKMM, p. 903**: at the risk-free rate `r` (with `0 < δ ≤ 1`, `0 < δ + r`, `r > −1`), the
present value of the payments `δ(1 − δ)^{j−1}`, `j ≥ 1`, of one bond is `δ/(δ + r)`; `B` bonds
are worth `δB/(δ + r)`. -/
theorem ltd_pv_bond {δ r : ℝ} (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r) (B : ℝ) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j / (1 + r) ^ (j + 1) * B) (δ / (δ + r) * B) := by
  have hr1 : 0 < 1 + r := by linarith
  have h0 : 0 ≤ (1 - δ) * (1 + r)⁻¹ := mul_nonneg (by linarith) (inv_nonneg.2 hr1.le)
  have h1 : (1 - δ) * (1 + r)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hr1]; linarith
  have := (ltd_hasSum_coupons h0 h1).mul_right B
  convert this using 1
  · funext j; rw [div_eq_mul_inv, ← inv_pow]
  · congr 1
    have hne : δ + r ≠ 0 := hδr.ne'
    rw [show 1 - (1 - δ) * (1 + r)⁻¹ = (δ + r) / (1 + r) by field_simp; ring]
    field_simp

/-- AKMM, p. 903, timing: valued at `t`, the payments `δ(1 − δ)^j B_t` (`j ≥ 0`) of the stock
`B_t` are worth `δ(1 + r)B_t/(δ + r)`; without the current coupon they are worth
`δ(1 − δ)B_t/(δ + r)`. The book's `δB_t/(δ + r)` is their value one period earlier. -/
theorem ltd_pv_stock_timing {δ r : ℝ} (hδ1 : δ ≤ 1) (hr : -1 < r) (hδr : 0 < δ + r) (B : ℝ) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j * B / (1 + r) ^ j) (δ * (1 + r) / (δ + r) * B) ∧
      HasSum (fun j : ℕ => δ * (1 - δ) ^ (j + 1) * B / (1 + r) ^ (j + 1))
        (δ * (1 - δ) / (δ + r) * B) := by
  have hr1 : 0 < 1 + r := by linarith
  have h := ltd_pv_bond hδ1 hr hδr B
  constructor
  · have := h.mul_left (1 + r)
    convert this using 1
    · funext j; rw [pow_succ]; field_simp
    · ring
  · have := h.mul_left (1 - δ)
    convert this using 1
    · funext j; rw [pow_succ]; field_simp
    · ring

/-- AKMM, p. 903: the yield `i` of a bond priced at `q` solves
`q = Σ_{j≥1} δ(1 − δ)^{j−1}/(1 + i)^j`, i.e. `q = δ/(δ + i)`. -/
theorem ltd_yield {δ i : ℝ} (hδ1 : δ ≤ 1) (hi : -1 < i) (hδi : 0 < δ + i) :
    HasSum (fun j : ℕ => δ * (1 - δ) ^ j / (1 + i) ^ (j + 1)) (δ / (δ + i)) := by
  simpa using ltd_pv_bond hδ1 hi hδi 1

/-- AKMM, p. 903: for `q > 0` the yield is `i = δ(1 − q)/q`. -/
theorem ltd_yield_iff {δ i q : ℝ} (hδi : 0 < δ + i) (hq : 0 < q) :
    q = δ / (δ + i) ↔ i = δ * (1 - q) / q := by
  constructor
  · intro h
    rw [h]
    rcases eq_or_ne δ 0 with hδ | hδ
    · rw [h, hδ] at hq; simp at hq
    · field_simp
      ring
  · intro h
    rw [h] at hδi ⊢
    have hq' : q ≠ 0 := hq.ne'
    have : δ + δ * (1 - q) / q = δ / q := by field_simp; ring
    rcases eq_or_ne δ 0 with hδ | hδ
    · rw [hδ] at hδi; simp at hδi
    · rw [this]; field_simp

/-- The coupon `x_t` of one bond issued at date `0`: `x_0 = 0` and `x_t = δ(1 − δ)^{t−1}`. -/
noncomputable def ltd_coupon (δ : ℝ) (t : ℕ) : ℝ := if t = 0 then 0 else δ * (1 - δ) ^ (t - 1)

/-- **AKMM, p. 902**: the Macaulay duration
`Σ_t t x_t/(1 + i)^t / Σ_t x_t/(1 + i)^t` of the bond is `(1 + i)/(δ + i)` (with
`0 < δ ≤ 1`, `i ≥ 0`). -/
theorem ltd_duration {δ i : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hi : 0 ≤ i) :
    (∑' t, t * ltd_coupon δ t / (1 + i) ^ t) / (∑' t, ltd_coupon δ t / (1 + i) ^ t) =
      (1 + i) / (δ + i) := by
  set a := (1 + i)⁻¹ with ha
  have hi1 : 0 < 1 + i := by linarith
  have ha0 : 0 < a := inv_pos.2 hi1
  set z := (1 - δ) * a with hz
  have hz0 : 0 ≤ z := mul_nonneg (by linarith) ha0.le
  have hz1 : z < 1 := by
    rw [hz, ha, ← div_eq_mul_inv, div_lt_one hi1]; linarith
  have h1z : 0 < 1 - z := by linarith
  -- the two series, shifted by one
  have hS0 : HasSum (fun t : ℕ => ltd_coupon δ t / (1 + i) ^ t) (δ * a / (1 - z)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ltd_coupon, ↓reduceIte, zero_div,
      sub_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
    convert ltd_hasSum_coupons hz0 hz1 using 1
    funext j
    rw [div_eq_mul_inv, ← inv_pow]
  have hgeo := hasSum_geometric_of_lt_one hz0 hz1
  have hnz : HasSum (fun n : ℕ => (n : ℝ) * z ^ n) (z / (1 - z) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hz0]; exact hz1)
  have hS1 : HasSum (fun t : ℕ => t * ltd_coupon δ t / (1 + i) ^ t)
      (δ * a / (1 - z) ^ 2) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ltd_coupon, ↓reduceIte, mul_zero,
      zero_div, sub_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
    have := (hnz.add hgeo).mul_left (δ * a)
    convert this using 1
    · funext j
      rw [div_eq_mul_inv, ← inv_pow, ← ha, hz, mul_pow, pow_succ]
      push_cast
      ring
    · field_simp
      ring
  rw [hS1.tsum_eq, hS0.tsum_eq]
  have hδa : 0 < δ * a := mul_pos hδ ha0
  rw [div_div_div_cancel_left' _ _ hδa.ne', pow_two, div_mul_cancel_right₀ h1z.ne']
  rw [hz, ha, show 1 - (1 - δ) * (1 + i)⁻¹ = (δ + i) / (1 + i) by field_simp; ring, inv_div]

/-- AKMM, p. 903: the annualised spread `r^s = ((1 + i)/(1 + r))^4 − 1`. -/
noncomputable def ltd_spread (i r : ℝ) : ℝ := ((1 + i) / (1 + r)) ^ 4 - 1

/-- The annualised spread is positive iff the bond yield exceeds the risk-free rate. -/
theorem ltd_spread_pos_iff {i r : ℝ} (hi : -1 < i) (hr : -1 < r) :
    0 < ltd_spread i r ↔ r < i := by
  have hr1 : 0 < 1 + r := by linarith
  have hx : 0 ≤ (1 + i) / (1 + r) := div_nonneg (by linarith) hr1.le
  rw [ltd_spread, sub_pos]
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have : (1 + i) / (1 + r) ≤ 1 := by rw [div_le_one hr1]; linarith
    have := pow_le_one₀ hx this (n := 4)
    linarith
  · intro h
    have : 1 < (1 + i) / (1 + r) := by rw [one_lt_div hr1]; linarith
    exact one_lt_pow₀ this (by norm_num)

/-- AKMM, (24.2), p. 731: the present-value haircut
`1 − Σ_t x_t^{post}/(1 + i)^t / Σ_t x_t^{pre}/(1 + i)^t`. -/
noncomputable def ltd_haircut (post pre : ℕ → ℝ) (i : ℝ) : ℝ :=
  1 - (∑' t, post (t + 1) / (1 + i) ^ (t + 1)) / (∑' t, pre (t + 1) / (1 + i) ^ (t + 1))

/-- AKMM, (24.2), p. 731: the haircut is the fraction of the pre-restructuring present value
lost, and lies in `[0, 1]` when the new obligations are worth between `0` and the old. -/
theorem eq_24_2 (post pre : ℕ → ℝ) (i : ℝ)
    (hpre : 0 < ∑' t, pre (t + 1) / (1 + i) ^ (t + 1))
    (hpost0 : 0 ≤ ∑' t, post (t + 1) / (1 + i) ^ (t + 1))
    (hle : ∑' t, post (t + 1) / (1 + i) ^ (t + 1) ≤ ∑' t, pre (t + 1) / (1 + i) ^ (t + 1)) :
    ltd_haircut post pre i = ((∑' t, pre (t + 1) / (1 + i) ^ (t + 1)) -
        ∑' t, post (t + 1) / (1 + i) ^ (t + 1)) / ∑' t, pre (t + 1) / (1 + i) ^ (t + 1) ∧
      0 ≤ ltd_haircut post pre i ∧ ltd_haircut post pre i ≤ 1 := by
  unfold ltd_haircut
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [sub_nonneg, div_le_one hpre]; exact hle
  · have := div_nonneg hpost0 hpre.le
    linarith

end AKMM.SovereignDefault
