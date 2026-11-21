/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.BWMoney

/-!
# Missing assets: fiat money in the Huggett economy

AKMM, §17.5, pp. 528–529. The Huggett economy with the borrowing limit `a′ ≥ 0`, two income
states `ω_lo < ω_hi` with transition probabilities `π_{·|·}`, utility `u` with `u′` strictly
decreasing. In the autarky equilibrium nobody trades and the bond price is set by the agent who
values the bond most.

* `ma_valuation_high_gt_low`: the high-income agent values the bond strictly more than the
  low-income agent, `π_{hi|hi} + π_{lo|hi}R > π_{lo|lo} + π_{hi|lo}/R`, `R = u′(ω_lo)/u′(ω_hi)`;
  hence at the autarky price the low-income agent would like to borrow (`ma_low_constrained`).
* `ma_autarky_price`: `qu′(ω_hi) = β(π_{hi|hi}u′(ω_hi) + π_{lo|hi}u′(ω_lo))` gives
  `1/q = (1/β)/(π_{hi|hi} + π_{lo|hi}u′(ω_lo)/u′(ω_hi)) < 1/β`.
* `ma_negative_rate_iff`: the autarky net rate is negative iff
  `β(π_{hi|hi} + π_{lo|hi}R) > 1`; an instance with log utility (`ma_negative_rate_example`).
* `ma_price_level`: with a constant price level money has gross return one; if aggregate saving
  in the `q = 1` economy is `m > 0`, the price level is `P = M/m` (Miao's
  `bw_fiat_quantity_theory`, from the `IncompleteMarkets` dependency).
-/

namespace AKMM.Money

/-- AKMM, p. 528: the bond valuations of the two agents at autarky. With `R > 1`
(`u′(ω_lo) > u′(ω_hi)`), `π_{lo|hi} > 0` and rows summing to one,
`π_{hi|hi} + π_{lo|hi}R > 1 ≥ π_{lo|lo} + π_{hi|lo}/R`. -/
theorem ma_valuation_high_gt_low {phh plh pll phl R : ℝ} (hR : 1 < R) (hplh : 0 < plh)
    (hphl : 0 ≤ phl) (hrow1 : phh + plh = 1) (hrow2 : pll + phl = 1) :
    1 < phh + plh * R ∧ pll + phl / R ≤ 1 ∧ pll + phl / R < phh + plh * R := by
  have h1 : 1 < phh + plh * R := by nlinarith
  have h2 : pll + phl / R ≤ 1 := by
    have : phl / R ≤ phl := div_le_self hphl hR.le
    linarith
  exact ⟨h1, h2, lt_of_le_of_lt h2 h1⟩

/-- AKMM, p. 528: at the autarky price set by the high-income agent the low-income agent is
borrowing constrained: `qu′(ω_lo) > β(π_{lo|lo}u′(ω_lo) + π_{hi|lo}u′(ω_hi))`. -/
theorem ma_low_constrained {β q phh plh pll phl uhi ulo : ℝ} (hβ : 0 < β) (huhi : 0 < uhi)
    (hlt : uhi < ulo) (hplh : 0 < plh) (hphl : 0 ≤ phl) (hrow1 : phh + plh = 1)
    (hrow2 : pll + phl = 1) (hq : q * uhi = β * (phh * uhi + plh * ulo)) :
    β * (pll * ulo + phl * uhi) < q * ulo := by
  have hulo : 0 < ulo := huhi.trans hlt
  have hR : 1 < ulo / uhi := (one_lt_div huhi).2 hlt
  obtain ⟨-, -, h3⟩ := ma_valuation_high_gt_low hR hplh hphl hrow1 hrow2
  have hqv : q = β * (phh + plh * (ulo / uhi)) := by
    field_simp
    linear_combination hq
  rw [hqv]
  have : pll * ulo + phl * uhi = ulo * (pll + phl / (ulo / uhi)) := by field_simp
  rw [this]
  nlinarith [mul_lt_mul_of_pos_left h3 (mul_pos hβ hulo)]

/-- **AKMM, p. 529: the autarky interest rate.** From the high agent's Euler equation
`qu′(ω_hi) = β(π_{hi|hi}u′(ω_hi) + π_{lo|hi}u′(ω_lo))`:
`1/q = (1/β)·1/(π_{hi|hi} + π_{lo|hi}u′(ω_lo)/u′(ω_hi)) < 1/β`. -/
theorem ma_autarky_price {β q phh plh uhi ulo : ℝ} (hβ : 0 < β) (huhi : 0 < uhi)
    (hlt : uhi < ulo) (hplh : 0 < plh) (hrow1 : phh + plh = 1)
    (hq : q * uhi = β * (phh * uhi + plh * ulo)) :
    1 / q = 1 / β * (1 / (phh + plh * (ulo / uhi))) ∧ 1 / q < 1 / β := by
  have hR : 1 < ulo / uhi := (one_lt_div huhi).2 hlt
  have hv : 1 < phh + plh * (ulo / uhi) := by nlinarith
  have hqv : q = β * (phh + plh * (ulo / uhi)) := by
    field_simp
    linear_combination hq
  refine ⟨by rw [hqv]; field_simp, ?_⟩
  rw [hqv, div_lt_div_iff₀ (by positivity) hβ]
  nlinarith

/-- AKMM, p. 529: the autarky net real rate is negative (`1/q < 1`) iff
`β(π_{hi|hi} + π_{lo|hi}u′(ω_lo)/u′(ω_hi)) > 1`. -/
theorem ma_negative_rate_iff {β V : ℝ} (hβ : 0 < β) (hV : 0 < V) :
    1 / (β * V) < 1 ↔ 1 < β * V := by
  rw [div_lt_one (by positivity)]

/-- AKMM, p. 529 (an instance): with `u = log`, `ω_hi = 2`, `ω_lo = 1/2` (`R = 4`),
`π_{hi|hi} = π_{lo|hi} = 1/2` and `β = 1/2`, the autarky gross rate is `1/q = 4/5 < 1`. -/
theorem ma_negative_rate_example :
    1 / ((1 / 2 : ℝ) * (1 / 2 + 1 / 2 * ((1 / 2 : ℝ)⁻¹ / (2 : ℝ)⁻¹))) = 4 / 5 := by norm_num

/-- AKMM, p. 529 (via Miao's `bw_fiat_quantity_theory`): with a constant price level, money has
gross return one and the economy is the `q = 1` saving economy; if aggregate saving there is
`m > 0` and the money stock is `M > 0`, the money market clears at a positive price level iff
`P = M/m`. -/
theorem ma_price_level {M m P : ℝ} (hM : 0 < M) (hm : 0 < m) :
    (0 < P ∧ m = M / P) ↔ P = M / m :=
  Miao.IncompleteMarkets.bw_fiat_quantity_theory hM hm

end AKMM.Money
