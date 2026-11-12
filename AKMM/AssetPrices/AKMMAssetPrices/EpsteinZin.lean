/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.Lognormal
import RecursiveUtility.PALogNormal

/-!
# Epstein–Zin utility separates the riskless rate from risk aversion

AKMM, §16.7, p. 490: "with Epstein–Zin utility, the intertemporal smoothing motive in (16.29) is
governed by the inverse of the elasticity of intertemporal substitution instead of risk aversion
`γ`, while the parameter that enters the equity premium is still risk aversion". The lognormal
Epstein–Zin pricing formulas are Miao's (20.33) and (20.35) (`Miao.RecursiveUtility.eq_20_33`,
`eq_20_35`), whose utility `[(1 − β)C^{1−ρ} + β(E U^{1−γ})^{(1−ρ)/(1−γ)}]^{1/(1−ρ)}` has risk
aversion `γ` and EIS `1/ρ`, the book's Epstein–Zin utility.

* Under Epstein–Zin the riskless rate responds to expected growth with slope `ρ = 1/EIS`, whatever
  `γ` (`ez_rf_smoothing`); with power utility the slope is `γ` (`lg_power_smoothing`).
* With `ρ = γ` Epstein–Zin is power utility and (20.33) reduces to (16.29) (`ez_power_case`).
* The premium weights in (20.35) involve `γ` (`ez_premium_weights`).
-/

namespace AKMM.AssetPrices

/-- AKMM, p. 490: with power utility the smoothing motive in (16.29) has slope `γ`:
`rᶠ(μ′) − rᶠ(μ) = γ(μ′ − μ)`. -/
theorem lg_power_smoothing (β γ μ μ' v : ℝ) :
    lgRf β γ μ' v - lgRf β γ μ v = γ * (μ' - μ) := by
  unfold lgRf
  ring

/-- AKMM, p. 490: under Epstein–Zin utility (Miao's (20.33)), two economies that differ only in
expected consumption growth `E_tΔc` have riskless rates differing by `ρ(μ′ − μ)`, with `ρ` the
inverse EIS, independently of risk aversion `γ`. -/
theorem ez_rf_smoothing {β ρ γ rf rf' m0 m0' m1 m1' v00 v01 v11 : ℝ} (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (hA : 0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + (1 - γ) / (1 - ρ) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * v11)
    (hB : 0 = rf + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0
      + ((1 - γ) / (1 - ρ) - 1) * m1 + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11)
    (hA' : 0 = (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0'
      + (1 - γ) / (1 - ρ) * m1' + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ)) ^ 2 * v11)
    (hB' : 0 = rf' + (1 - γ) / (1 - ρ) * Real.log β - ρ * ((1 - γ) / (1 - ρ)) * m0'
      + ((1 - γ) / (1 - ρ) - 1) * m1' + 1 / 2 * (ρ * ((1 - γ) / (1 - ρ))) ^ 2 * v00
      - ρ * ((1 - γ) / (1 - ρ)) * ((1 - γ) / (1 - ρ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - ρ) - 1) ^ 2 * v11) :
    rf' - rf = ρ * (m0' - m0) := by
  have e := Miao.RecursiveUtility.eq_20_33 hρ hγ hA hB
  have e' := Miao.RecursiveUtility.eq_20_33 hρ hγ hA' hB'
  rw [e, e']
  ring

/-- AKMM, p. 490: when `ρ = γ` (EIS `= 1/γ`) Epstein–Zin utility is power utility, and Miao's
(20.33) is the book's (16.29), `rᶠ = −log β + γE_tΔc − γ²σ_c²/2`. -/
theorem ez_power_case {β γ rf m0 m1 v00 v01 v11 : ℝ} (hγ : γ ≠ 1)
    (hA : 0 = (1 - γ) / (1 - γ) * Real.log β - γ * ((1 - γ) / (1 - γ)) * m0
      + (1 - γ) / (1 - γ) * m1 + 1 / 2 * (γ * ((1 - γ) / (1 - γ))) ^ 2 * v00
      - γ * ((1 - γ) / (1 - γ)) * ((1 - γ) / (1 - γ)) * v01
      + 1 / 2 * ((1 - γ) / (1 - γ)) ^ 2 * v11)
    (hB : 0 = rf + (1 - γ) / (1 - γ) * Real.log β - γ * ((1 - γ) / (1 - γ)) * m0
      + ((1 - γ) / (1 - γ) - 1) * m1 + 1 / 2 * (γ * ((1 - γ) / (1 - γ))) ^ 2 * v00
      - γ * ((1 - γ) / (1 - γ)) * ((1 - γ) / (1 - γ) - 1) * v01
      + 1 / 2 * ((1 - γ) / (1 - γ) - 1) ^ 2 * v11) :
    rf = lgRf β γ m0 v00 := by
  have e := Miao.RecursiveUtility.eq_20_33 hγ hγ hA hB
  have h1 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  rw [e, lgRf]
  field_simp
  ring

/-- AKMM, p. 490: in the Epstein–Zin premium (Miao's (20.35)) the weights
`ρ(1 − γ)/(1 − ρ)` on `σ_ic` and `(γ − ρ)/(1 − ρ)` on `σ_iw` move with risk aversion `γ` for
fixed `ρ`: for `ρ < 1` the second is strictly increasing in `γ`. -/
theorem ez_premium_weights {ρ γ₁ γ₂ : ℝ} (hρ1 : ρ < 1) (h : γ₁ < γ₂) :
    (γ₁ - ρ) / (1 - ρ) < (γ₂ - ρ) / (1 - ρ) :=
  div_lt_div_of_pos_right (by linarith) (by linarith)

end AKMM.AssetPrices
