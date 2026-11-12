/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.LogLinear

/-!
# The production economy: relative supply and global output

AKMM, §23.4, (23.32)–(23.38), pp. 720–722.

* Labour supply (23.33) and the production function (23.34) are exact in logs
  (`eq_23_33`, `eq_23_34`). Profit maximisation gives the labour demand `W = α p_H Z L^{α−1}`,
  with profits `(1 − α) p_H Y` (`prod_labour_demand`, `prod_profit`); the printed (23.36)
  `w = (p_H/P) Z L^{α−1}` omits the factor `α` and is not a first-order condition when `α < 1`
  (`eq_23_36_printed_counterexample`), but the omitted constant does not affect the
  log-linearisation (`eq_23_36_log`). The product price moves as `p̂_H − P̂ = −(1 − a)T̂` at home
  and `p̂_F − P̂* = (1 − a)T̂` abroad (`prod_relPrice_loglin`).
* (23.37): relative supply
  `Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η)·(Ẑ − Ẑ*) − α/(1 − α + η)·(Ŵ + T̂)` (`eq_23_37`); under
  complete markets its slope `−α/(1 − α + η)` does not depend on openness `a` and the schedule is
  increasing in the relative price of home goods (`prod_cm_slope`).
* (23.38): under financial autarky
  `Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ − Ẑ*) + 2α(1 − a)(σ − 1)/(1 − α + η + ασ)·T̂`
  (`eq_23_38`), whose slope has the sign of `σ − 1` (`prod_fa_slope_sign`).
* Global output `Ŷ_H + Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ + Ẑ*)` under every financial market
  structure (`prod_global_output`).
-/

namespace AKMM.InternationalMacro

open Real

/-- **(23.33)**, AKMM p. 721, exact in logs: `C^{−σ} w = ζ L^η` iff
`−σ log C + log w = log ζ + η log L`. -/
theorem eq_23_33 {σ η ζ C w L : ℝ} (hC : 0 < C) (hw : 0 < w) (hζ : 0 < ζ) (hL : 0 < L) :
    C ^ (-σ) * w = ζ * L ^ η ↔ -σ * log C + log w = log ζ + η * log L := by
  have h1 : 0 < C ^ (-σ) * w := mul_pos (rpow_pos_of_pos hC _) hw
  have h2 : 0 < ζ * L ^ η := mul_pos hζ (rpow_pos_of_pos hL _)
  rw [← log_injOn_pos.eq_iff h1 h2, log_mul (rpow_pos_of_pos hC _).ne' hw.ne',
    log_mul hζ.ne' (rpow_pos_of_pos hL _).ne', log_rpow hC, log_rpow hL]

/-- **(23.34)**, AKMM p. 721, exact in logs: `log(Z L^α) = log Z + α log L`. -/
theorem eq_23_34 {α Z L : ℝ} (hZ : 0 < Z) (hL : 0 < L) :
    log (Z * L ^ α) = log Z + α * log L := by
  rw [log_mul hZ.ne' (rpow_pos_of_pos hL _).ne', log_rpow hL]

/-- AKMM, p. 721: the firm's profit `p_H Z L^α − W L` has derivative `α p_H Z L^{α−1} − W`, so at
an interior maximum the nominal wage equals the value of the marginal product,
`W = α p_H Z L^{α−1}` (the labour demand behind (23.36)). -/
theorem prod_labour_demand {α pH Z W L : ℝ} (hL : 0 < L)
    (hmax : IsLocalMax (fun L => pH * (Z * L ^ α) - W * L) L) :
    W = α * pH * Z * L ^ (α - 1) := by
  have hd : HasDerivAt (fun L => pH * (Z * L ^ α) - W * L)
      (pH * (Z * (α * L ^ (α - 1))) - W * 1) L :=
    (((hasDerivAt_rpow_const (Or.inl hL.ne')).const_mul Z).const_mul pH).sub
      ((hasDerivAt_id L).const_mul W)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- AKMM, p. 721: at the labour demand `W = α p_H Z L^{α−1}` profits are `(1 − α) p_H Y`, with
`Y = Z L^α`; they are zero (as the book states) only when `α = 1`. -/
theorem prod_profit {α pH Z L : ℝ} (hL : 0 < L) :
    pH * (Z * L ^ α) - α * pH * Z * L ^ (α - 1) * L = (1 - α) * (pH * (Z * L ^ α)) := by
  rw [mul_assoc (α * pH * Z), ← rpow_add_one hL.ne', sub_add_cancel]
  ring

/-- AKMM, (23.36), p. 721 (corrected): the printed labour demand `W = p_H Z L^{α−1}` (the
average, not the marginal, product) is not a first-order condition of profit maximisation when
`α < 1`: at that wage the derivative of profits is `(α − 1) p_H Z L^{α−1} ≠ 0`. -/
theorem eq_23_36_printed_counterexample {α pH Z L : ℝ} (hα : α < 1) (hpH : 0 < pH) (hZ : 0 < Z)
    (hL : 0 < L) :
    HasDerivAt (fun x => pH * (Z * x ^ α) - pH * Z * L ^ (α - 1) * x)
        ((α - 1) * pH * Z * L ^ (α - 1)) L ∧ (α - 1) * pH * Z * L ^ (α - 1) ≠ 0 := by
  constructor
  · have hd : HasDerivAt (fun x => pH * (Z * x ^ α) - pH * Z * L ^ (α - 1) * x)
        (pH * (Z * (α * L ^ (α - 1))) - pH * Z * L ^ (α - 1) * 1) L :=
      (((hasDerivAt_rpow_const (Or.inl hL.ne')).const_mul Z).const_mul pH).sub
        ((hasDerivAt_id' L).const_mul (pH * Z * L ^ (α - 1)))
    refine hd.congr_deriv ?_
    ring
  · have : 0 < pH * Z * L ^ (α - 1) := by positivity
    have h1 : α - 1 ≠ 0 := by linarith
    have e : (α - 1) * pH * Z * L ^ (α - 1) = (α - 1) * (pH * Z * L ^ (α - 1)) := by ring
    rw [e]
    exact mul_ne_zero h1 this.ne'

/-- AKMM, (23.36), p. 721: whether or not the constant `α` is included, the log of the real
labour demand `w = c (p_H/P) Z L^{α−1}` is `log c + log(p_H/P) + log Z + (α − 1) log L`, so the
log-linearised labour demand `ŵ = (p̂_H − P̂) + Ẑ − (1 − α)L̂` is the same. -/
theorem eq_23_36_log {α c rp Z L : ℝ} (hc : 0 < c) (hrp : 0 < rp) (hZ : 0 < Z) (hL : 0 < L) :
    log (c * rp * Z * L ^ (α - 1)) = log c + log rp + log Z + (α - 1) * log L := by
  rw [log_mul (by positivity) (rpow_pos_of_pos hL _).ne', log_mul (by positivity) hZ.ne',
    log_mul hc.ne' hrp.ne', log_rpow hL]

/-- AKMM, p. 721: the product price relative to the CPI moves by `p̂_H − P̂ = −(1 − a)T̂` at home
and `p̂_F − P̂* = (1 − a)T̂` abroad (exact derivatives along the ray of `LogLinear`). -/
theorem prod_relPrice_loglin {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (exp (t * ph) / loglinP a φ ph pf t)) (-(1 - a) * (pf - ph)) 0 ∧
      HasDerivAt (fun t => log (exp (t * pf) / loglinP (1 - a) φ ph pf t))
        ((1 - a) * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hexp : ∀ k : ℝ, HasDerivAt (fun t => log (exp (t * k))) k 0 := by
    intro k; simpa using loglin_exp_ray 1 k one_pos
  constructor
  · have e : (fun t => log (exp (t * ph) / loglinP a φ ph pf t))
        = fun t => log (exp (t * ph)) - log (loglinP a φ ph pf t) := by
      funext t; rw [log_div (exp_pos _).ne' (loglinP_pos ha0 ha1 t).ne']
    rw [e]
    refine ((hexp ph).sub (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ)).congr_deriv ?_
    ring
  · have e : (fun t => log (exp (t * pf) / loglinP (1 - a) φ ph pf t))
        = fun t => log (exp (t * pf)) - log (loglinP (1 - a) φ ph pf t) := by
      funext t; rw [log_div (exp_pos _).ne' (loglinP_pos h1a (by linarith) t).ne']
    rw [e]
    refine ((hexp pf).sub
      (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ)).congr_deriv ?_
    ring

/-- **(23.37)**, AKMM p. 721: combining, in each country, labour supply (23.33)
`ŵ − σĈ = ηL̂`, labour demand (23.36) `ŵ = (p̂ − P̂) + Ẑ − (1 − α)L̂` with
`p̂_H − P̂ = −(1 − a)T̂`, `p̂_F − P̂* = (1 − a)T̂`, and production (23.34) `Ŷ = Ẑ + αL̂`, and the
wealth gap (23.22) `Ŵ = σ(Ĉ − Ĉ*) − (2a − 1)T̂`, relative supply is
`Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η)·(Ẑ − Ẑ*) − α/(1 − α + η)·(Ŵ + T̂)`. -/
theorem eq_23_37 {a α η σ τ c cs w ws l ls z zs y ys W : ℝ} (hk : 1 - α + η ≠ 0)
    (hsup : w - σ * c = η * l) (hsupS : ws - σ * cs = η * ls)
    (hdem : w = -(1 - a) * τ + z - (1 - α) * l) (hdemS : ws = (1 - a) * τ + zs - (1 - α) * ls)
    (hy : y = z + α * l) (hyS : ys = zs + α * ls) (hW : W = σ * (c - cs) - (2 * a - 1) * τ) :
    y - ys = (1 + η) / (1 - α + η) * (z - zs) - α / (1 - α + η) * (W + τ) := by
  have hl : l = (z - σ * c - (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  have hls : ls = (zs - σ * cs + (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  rw [hy, hyS, hl, hls, hW]
  field_simp
  ring

/-- AKMM, p. 722: under complete markets (`Ŵ = 0`) the relative supply (23.37) is
`Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η)·(Ẑ − Ẑ*) − α/(1 − α + η)·T̂`; its slope in `T̂` is negative
(relative supply increases with the relative price of home goods `1/T`) and involves only
technology and labour-supply parameters, not the openness parameter `a`. -/
theorem prod_cm_slope {a α η σ τ c cs w ws l ls z zs y ys : ℝ} (hα : 0 < α) (hk : 0 < 1 - α + η)
    (hsup : w - σ * c = η * l) (hsupS : ws - σ * cs = η * ls)
    (hdem : w = -(1 - a) * τ + z - (1 - α) * l) (hdemS : ws = (1 - a) * τ + zs - (1 - α) * ls)
    (hy : y = z + α * l) (hyS : ys = zs + α * ls) (hW : σ * (c - cs) - (2 * a - 1) * τ = 0) :
    y - ys = (1 + η) / (1 - α + η) * (z - zs) - α / (1 - α + η) * τ ∧ -(α / (1 - α + η)) < 0 := by
  constructor
  · have := eq_23_37 hk.ne' hsup hsupS hdem hdemS hy hyS rfl
    rw [hW, zero_add] at this
    exact this
  · have := div_pos hα hk
    linarith

/-- **(23.38)**, AKMM p. 722: under financial autarky, substituting the autarky wealth gap
(23.25) `Ŵ = σ(Ŷ_H − Ŷ*_F − 2(1 − a)T̂) − (2a − 1)T̂` into (23.37) gives
`Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ − Ẑ*) + 2α(1 − a)(σ − 1)/(1 − α + η + ασ)·T̂`. -/
theorem eq_23_38 {a α η σ τ y ys z zs W : ℝ} (hk : 1 - α + η ≠ 0) (hk' : 1 - α + η + α * σ ≠ 0)
    (h37 : y - ys = (1 + η) / (1 - α + η) * (z - zs) - α / (1 - α + η) * (W + τ))
    (h25 : W = σ * (y - ys - 2 * (1 - a) * τ) - (2 * a - 1) * τ) :
    y - ys = (1 + η) / (1 - α + η + α * σ) * (z - zs)
      + 2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) * τ := by
  rw [h25] at h37
  field_simp at h37
  field_simp
  linear_combination h37

/-- AKMM, p. 722: under financial autarky the relative supply (23.38) is increasing in the
terms of trade `T̂` (decreasing in the relative price of home goods) iff `σ > 1`, decreasing in
`T̂` iff `σ < 1`, and independent of the terms of trade under log utility `σ = 1`. -/
theorem prod_fa_slope_sign {a α η σ : ℝ} (ha1 : a < 1) (hα : 0 < α)
    (hk' : 0 < 1 - α + η + α * σ) :
    (0 < 2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) ↔ 1 < σ) ∧
      (2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) < 0 ↔ σ < 1) ∧
      (σ = 1 → 2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) = 0) := by
  have h1a : 0 < 1 - a := by linarith
  have hc : 0 < 2 * α * (1 - a) := by positivity
  refine ⟨?_, ?_, fun h => by rw [h]; ring⟩
  · rw [div_pos_iff_of_pos_right hk']
    constructor
    · intro h; by_contra hn; nlinarith
    · intro h; nlinarith
  · rw [div_neg_iff]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · by_contra hn; nlinarith
    · intro h; right; exact ⟨by nlinarith, hk'⟩

/-- AKMM, p. 722: global output. Summing the two countries' labour-market and production
equations and imposing world resource balance `Ĉ + Ĉ* = Ŷ_H + Ŷ*_F` gives
`Ŷ_H + Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ + Ẑ*)`, whatever the structure of financial
markets (no wealth-gap term enters). -/
theorem prod_global_output {a α η σ τ c cs w ws l ls z zs y ys : ℝ} (hk : 1 - α + η ≠ 0)
    (hk' : 1 - α + η + α * σ ≠ 0)
    (hsup : w - σ * c = η * l) (hsupS : ws - σ * cs = η * ls)
    (hdem : w = -(1 - a) * τ + z - (1 - α) * l) (hdemS : ws = (1 - a) * τ + zs - (1 - α) * ls)
    (hy : y = z + α * l) (hyS : ys = zs + α * ls) (hworld : c + cs = y + ys) :
    y + ys = (1 + η) / (1 - α + η + α * σ) * (z + zs) := by
  have hl : l = (z - σ * c - (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  have hls : ls = (zs - σ * cs + (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  have hsum : (1 - α + η) * (y + ys) = (1 + η) * (z + zs) - α * σ * (c + cs) := by
    rw [hy, hyS, hl, hls]
    field_simp
    ring
  rw [hworld] at hsum
  rw [div_mul_eq_mul_div, eq_div_iff hk']
  linear_combination hsum

end AKMM.InternationalMacro
