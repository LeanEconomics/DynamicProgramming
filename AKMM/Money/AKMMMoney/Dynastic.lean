/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fiat money has no value in dynastic models

AKMM, §17.3.1, pp. 501–503. A dynastic household holds a real asset `a` (price `q_t = 1/(1+r_t)`),
money `M ≥ 0` and nominal bonds `B` (interest `i_t`); `p_{m,t}` is the price of money.

* `eq_17_11`: the budget (17.8) is the budget (17.11) in total real wealth
  `â_t = a_t + m_t + b_t(1 + i_{t−1})`.
* `eq_17_12`: if a finite optimum holds money in positive amount, the two "static" coefficients
  vanish, `q_t = p_{m,t}/p_{m,t+1} = p_{m,t}/(p_{m,t+1}(1 + i_t))`; `dyn_unbounded` is the
  unbounded-consumption argument; `eq_17_13`: the compact budget.
* `dyn_no_value_of_pos_rate`: with `i_t > 0` (17.12) cannot hold with valued money.
* `eq_17_14`: the discounted value of money telescopes, `q₀⋯q_{T−1}m_T = p_{m,0}M_T`; hence the
  transversality condition forces `p_{m,0} lim M_T ≤ 0` (`dyn_tvc_money_vanishes`), and money
  cannot be valued unless the stock vanishes (`dyn_no_valued_money`).
* `eq_17_15`: the Fisher equation `1 + i_t = (1 + r_t)(1 + π_t)`.

**Departure.** (17.14) is printed `q₀q₁⋯q_T m_T`, but its expansion stops at
`p_{m,T−1}/p_{m,T}`: the discount factor of `m_T` is `q₀⋯q_{T−1}` (`eq_17_14`;
`dyn_printed_product` shows the printed product is `p_{m,0}M_T q_T`). The conclusion is
unaffected. The transversality condition, which the book takes from Chapter 4, is a hypothesis.
-/

open Filter Topology

namespace AKMM.Money

/-- **AKMM, (17.11)**, p. 502: with `m = p_{m,t}M`, `b = p_{m,t}B`, `m′ = p_{m,t+1}M′`,
`b′ = p_{m,t+1}B′`, `â = a + m + b(1 + i_{t−1})` and `â′ = a′ + m′ + b′(1 + i_t)`, the budget
(17.8) is equivalent to (17.11). -/
theorem eq_17_11 {c q a a' pt pt1 M M' B B' i im1 w l τ : ℝ} (hpt1 : pt1 ≠ 0) :
    c + q * a' + pt * M' + pt * B' = w * (1 - l) + a + pt * M + pt * (1 + im1) * B - τ ↔
      c + q * (a' + pt1 * M' + pt1 * B' * (1 + i)) + (pt / pt1 - q) * (pt1 * M') +
        (pt / pt1 - q * (1 + i)) * (pt1 * B') =
          w * (1 - l) - τ + (a + pt * M + pt * B * (1 + im1)) := by
  have e : q * (a' + pt1 * M' + pt1 * B' * (1 + i)) + (pt / pt1 - q) * (pt1 * M') +
      (pt / pt1 - q * (1 + i)) * (pt1 * B') = q * a' + pt * M' + pt * B' := by
    field_simp; ring
  rw [show c + q * (a' + pt1 * M' + pt1 * B' * (1 + i)) + (pt / pt1 - q) * (pt1 * M') +
      (pt / pt1 - q * (1 + i)) * (pt1 * B') = c + (q * (a' + pt1 * M' + pt1 * B' * (1 + i)) +
      (pt / pt1 - q) * (pt1 * M') + (pt / pt1 - q * (1 + i)) * (pt1 * B')) by ring, e]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 502: if the return on bonds differs from the real interest rate, the coefficient
`k = p_{m,t}/p_{m,t+1} − q_t(1 + i_t)` is nonzero and consumption `Y − kb′` is unbounded in the
bond position `b′`. -/
theorem dyn_unbounded {k Y : ℝ} (hk : k ≠ 0) (C : ℝ) : ∃ b, C ≤ Y - k * b :=
  ⟨(Y - C) / k, by rw [mul_div_cancel₀ _ hk]; linarith⟩

/-- **AKMM, (17.12)**, p. 503: suppose `(m*, b*)` (`m* ≥ 0`) maximises consumption
`Y − k_m m − k_b b` over `m ≥ 0` and all `b`, with `k_m = p_{m,t}/p_{m,t+1} − q_t` and
`k_b = p_{m,t}/p_{m,t+1} − q_t(1 + i_t)`. If money is held, `m* > 0`, then `k_m = k_b = 0`. -/
theorem eq_17_12 {km kb Y ms bs : ℝ} (hms : 0 < ms)
    (hopt : ∀ m b, 0 ≤ m → Y - km * m - kb * b ≤ Y - km * ms - kb * bs) : km = 0 ∧ kb = 0 := by
  constructor
  · have h1 := hopt 0 bs le_rfl
    have h2 := hopt (2 * ms) bs (by linarith)
    nlinarith
  · by_contra hk
    obtain ⟨b, hb⟩ := dyn_unbounded (Y := Y - km * ms) hk (Y - km * ms - kb * bs + 1)
    have := hopt ms b hms.le
    linarith

/-- AKMM, (17.12), p. 503: in the book's notation `q_t = p_{m,t}/p_{m,t+1} =
p_{m,t}/(p_{m,t+1}(1 + i_t))`. -/
theorem eq_17_12_prices {q pt pt1 i : ℝ} (hi : 1 + i ≠ 0) (hm : pt / pt1 - q = 0)
    (hb : pt / pt1 - q * (1 + i) = 0) : q = pt / pt1 ∧ q = pt / pt1 / (1 + i) := by
  refine ⟨by linarith, ?_⟩
  rw [eq_div_iff hi]; linarith

/-- **AKMM, (17.13)**, p. 503: under the no-arbitrage conditions the budget (17.11) becomes
`c_t + q_tâ_{t+1} = w_t(1 − l_t) − τ_t + â_t`. -/
theorem eq_17_13 {c q ahat ahat' pt pt1 i m' b' w l τ : ℝ} (hm : pt / pt1 - q = 0)
    (hb : pt / pt1 - q * (1 + i) = 0) :
    c + q * ahat' + (pt / pt1 - q) * m' + (pt / pt1 - q * (1 + i)) * b' = w * (1 - l) - τ + ahat
      ↔ c + q * ahat' = w * (1 - l) - τ + ahat := by
  rw [hm, hb, zero_mul, zero_mul, add_zero, add_zero]

/-- AKMM, p. 503: with a positive nominal rate `i_t > 0` the two no-arbitrage conditions (17.12)
cannot both hold at a positive price of money: money is dominated by bonds. -/
theorem dyn_no_value_of_pos_rate {q pt pt1 i : ℝ} (hpt : 0 < pt) (hpt1 : 0 < pt1) (hi : 0 < i)
    (hm : pt / pt1 - q = 0) : pt / pt1 - q * (1 + i) ≠ 0 := by
  have : q = pt / pt1 := by linarith
  rw [this]
  have : 0 < pt / pt1 := div_pos hpt hpt1
  nlinarith

/-- **AKMM, (17.14)**, p. 503: with `q_s = p_{m,s}/p_{m,s+1}` the discounted real value of money
telescopes, `(∏_{s<T} q_s) p_{m,T}M_T = p_{m,0}M_T`. -/
theorem eq_17_14 {pm : ℕ → ℝ} (hpm : ∀ t, 0 < pm t) (M : ℕ → ℝ) (T : ℕ) :
    (∏ s ∈ Finset.range T, pm s / pm (s + 1)) * (pm T * M T) = pm 0 * M T := by
  have h : ∀ T, (∏ s ∈ Finset.range T, pm s / pm (s + 1)) = pm 0 / pm T := by
    intro T
    induction T with
    | zero => simp [div_self (hpm 0).ne']
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp [(hpm n).ne', (hpm (n + 1)).ne']
  rw [h, div_mul_eq_mul_div, mul_comm (pm 0), mul_assoc, mul_div_assoc]
  field_simp [(hpm T).ne']

/-- AKMM, (17.14) as printed: the product `q₀⋯q_T` multiplying `m_T` equals `p_{m,0}M_T q_T`, not
`p_{m,0}M_T`. -/
theorem dyn_printed_product {pm : ℕ → ℝ} (hpm : ∀ t, 0 < pm t) (M : ℕ → ℝ) (T : ℕ) :
    (∏ s ∈ Finset.range (T + 1), pm s / pm (s + 1)) * (pm T * M T) =
      pm 0 * M T * (pm T / pm (T + 1)) := by
  rw [Finset.prod_range_succ, mul_comm _ (pm T / pm (T + 1)), mul_assoc, eq_17_14 hpm]
  ring

/-- AKMM, (17.14), p. 503: if the transversality condition holds,
`(∏_{s<T} q_s) m_T → L ≤ 0`, and the price of money is positive, then `p_{m,0} lim M_T ≤ 0`:
`M_T → L/p_{m,0}` with `L ≤ 0`, so (as `M_T ≥ 0`) the money stock vanishes. -/
theorem dyn_tvc_money_vanishes {pm M : ℕ → ℝ} (hpm : ∀ t, 0 < pm t) (hM : ∀ t, 0 ≤ M t)
    {L : ℝ} (hL : L ≤ 0)
    (htvc : Tendsto (fun T => (∏ s ∈ Finset.range T, pm s / pm (s + 1)) * (pm T * M T)) atTop
      (𝓝 L)) : Tendsto M atTop (𝓝 0) := by
  simp only [eq_17_14 hpm] at htvc
  have hl : Tendsto M atTop (𝓝 (L / pm 0)) := by
    have := htvc.div_const (pm 0)
    refine this.congr fun T => ?_
    field_simp [(hpm 0).ne']
  have hge : 0 ≤ L / pm 0 := ge_of_tendsto hl (Eventually.of_forall hM)
  have hle : L / pm 0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hL (hpm 0).le
  rwa [le_antisymm hle hge] at hl

/-- AKMM, p. 503: "if fiat money is not vanishing … money cannot have value". If the money stock
is bounded below by `M̲ > 0`, no path of positive money prices satisfies the no-arbitrage
condition `q_s = p_{m,s}/p_{m,s+1}` together with the transversality condition. -/
theorem dyn_no_valued_money {pm M : ℕ → ℝ} {Mlow L : ℝ} (hMlow : 0 < Mlow)
    (hM : ∀ t, Mlow ≤ M t) (hpm : ∀ t, 0 < pm t) (hL : L ≤ 0)
    (htvc : Tendsto (fun T => (∏ s ∈ Finset.range T, pm s / pm (s + 1)) * (pm T * M T)) atTop
      (𝓝 L)) : False := by
  have h := dyn_tvc_money_vanishes hpm (fun t => hMlow.le.trans (hM t)) hL htvc
  have : Mlow ≤ 0 := ge_of_tendsto' h hM
  linarith

/-- **AKMM, (17.15)**, p. 503: with `q_t = 1/(1 + r_t)`, `1 + π_t = p_{m,t}/p_{m,t+1}` and the
no-arbitrage condition `q_t(1 + i_t) = p_{m,t}/p_{m,t+1}`, `1 + i_t = (1 + r_t)(1 + π_t)`. -/
theorem eq_17_15 {r i infl q : ℝ} (hr : 1 + r ≠ 0) (hq : q = 1 / (1 + r))
    (hna : q * (1 + i) = 1 + infl) : 1 + i = (1 + r) * (1 + infl) := by
  rw [← hna, hq]; field_simp

end AKMM.Money
