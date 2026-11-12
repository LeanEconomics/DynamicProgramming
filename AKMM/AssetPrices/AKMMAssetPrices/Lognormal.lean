/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPLognormal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The lognormal model: the riskless rate and the consumption CAPM

AKMM, §16.7, pp. 488–490. Log endowment growth `g = log G ~ N(μ_g, σ_g²)` (16.28) and power
utility, so `log M = log β − γg`. Gaussian integrals are Miao's `bp_integral_exp_gaussian`.

* (16.29): `pᶠ = Eₜ[M] = βe^{−γμ_g + γ²σ_g²/2}` and `rᶠ = log(1/pᶠ) = −log β + γμ_g − γ²σ_g²/2`
  (`eq_16_29`).
* The two motives: `rᶠ` rises with `μ_g` and falls with `σ_g²` (`lg_rf_growth`,
  `lg_rf_precautionary`); in `γ` it increases exactly on `γ ≤ μ_g/σ_g²` and decreases beyond
  (`lg_rf_mono_iff`, `lg_rf_strictMonoOn`, `lg_rf_strictAntiOn`); with Table 16.1's
  `μ_g = 0.0175`, `σ_g = 0.0233`, `μ_g/σ_g² ∈ (32, 33)` (`lg_threshold_table`).
* The equity Euler equation with jointly lognormal `(g, rˢ)` gives
  `Eₜrˢ = −log β + γμ_g − γ²σ_g²/2 − σᵣ²/2 + γCovₜ(g, rˢ)` (`lg_equity_euler`) and **(16.30)**,
  `Eₜrˢ − rᶠ + σᵣ²/2 = γCovₜ(g, rˢ)` (`eq_16_30`); the Jensen term
  `log EₜRˢ = Eₜrˢ + σᵣ²/2` (`lg_jensen`).
* The numbers on p. 490: `σ_cσ_r = 0.0233 × 0.1836 ≈ 0.0043` (`lg_sd_product`); a premium of
  `0.07` needs `γ ≥ 16.36` even with perfect correlation (`lg_gamma_bound`), and `γ = 16` falls
  short (`lg_gamma_16_short`); with `β ≤ 1` and `γ ∈ [16, 48]` the riskless rate exceeds 1%
  (`lg_rf_high`).

Departures: the derivation of (16.30) mixes `μ_c, σ_c` with `μ_g, σ_g` (the same objects);
"`γ = 16`" understates the bound `γ ≥ 16.36` implied by Table 16.1. See `docs/corrections.md`.
-/

namespace AKMM.AssetPrices

open MeasureTheory ProbabilityTheory Miao.CompleteMarkets

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- AKMM, (16.29), p. 488: with `g ~ N(μ_g, σ_g²)`, the bond price is
`pᶠ = E[βe^{−γg}] = βe^{−γμ_g + γ²σ_g²/2}` and the riskless rate is
`rᶠ = log(1/pᶠ) = −log β + γμ_g − γ²σ_g²/2`. -/
theorem eq_16_29 {g : Ω → ℝ} {μ : ℝ} {v : NNReal} (hg : HasLaw g (gaussianReal μ v) P)
    {β : ℝ} (hβ : 0 < β) (γ : ℝ) :
    ∫ ω, β * Real.exp (-γ * g ω) ∂P = β * Real.exp (-γ * μ + γ ^ 2 * v / 2) ∧
      Real.log (1 / (β * Real.exp (-γ * μ + γ ^ 2 * v / 2))) =
        -Real.log β + γ * μ - γ ^ 2 * v / 2 := by
  have hm := gaussianReal_const_mul hg (-γ)
  have hE := bp_integral_exp_gaussian hm
  refine ⟨?_, ?_⟩
  · rw [integral_const_mul, hE]
    congr 2
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    ring
  · rw [one_div, Real.log_inv, Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

/-- The riskless rate (16.29) as a function of the parameters (`v = σ_g²`). -/
noncomputable def lgRf (β γ μ v : ℝ) : ℝ := -Real.log β + γ * μ - γ ^ 2 * v / 2

/-- AKMM, p. 488, the intertemporal smoothing motive: with `γ > 0`, higher expected growth
raises the riskless rate. -/
theorem lg_rf_growth {β γ μ₁ μ₂ v : ℝ} (hγ : 0 < γ) (h : μ₁ < μ₂) :
    lgRf β γ μ₁ v < lgRf β γ μ₂ v := by
  unfold lgRf
  nlinarith

/-- AKMM, p. 489, the precautionary motive: with `γ ≠ 0`, more volatile growth lowers the
riskless rate. -/
theorem lg_rf_precautionary {β γ μ v₁ v₂ : ℝ} (hγ : γ ≠ 0) (h : v₁ < v₂) :
    lgRf β γ μ v₂ < lgRf β γ μ v₁ := by
  unfold lgRf
  have : 0 < γ ^ 2 := by positivity
  nlinarith

/-- AKMM, p. 489: `∂rᶠ/∂γ = μ_g − γσ_g²`, positive iff `γ < μ_g/σ_g²`. -/
theorem lg_rf_mono_iff {β μ v : ℝ} (hv : 0 < v) (γ : ℝ) :
    HasDerivAt (fun γ' => lgRf β γ' μ v) (μ - γ * v) γ ∧ (0 < μ - γ * v ↔ γ < μ / v) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun γ' : ℝ => γ' * μ) μ γ := by
      simpa using (hasDerivAt_id γ).mul_const μ
    have h2 : HasDerivAt (fun γ' : ℝ => γ' ^ 2 * v / 2) (γ * v) γ := by
      have := ((hasDerivAt_pow 2 γ).mul_const v).div_const 2
      convert this using 1
      ring
    have h3 := (h1.sub h2).const_add (-Real.log β)
    have e : (fun γ' => lgRf β γ' μ v) = fun x => -Real.log β + (x * μ - x ^ 2 * v / 2) := by
      funext γ'
      simp only [lgRf]
      ring
    rw [e]
    exact h3
  · rw [lt_div_iff₀ hv, sub_pos]

/-- AKMM, p. 489: the riskless rate is strictly increasing in `γ` on `γ ≤ μ_g/σ_g²`. -/
theorem lg_rf_strictMonoOn {β μ v : ℝ} (hv : 0 < v) :
    StrictMonoOn (fun γ => lgRf β γ μ v) (Set.Iic (μ / v)) := by
  intro γ₁ h₁ γ₂ h₂ h12
  simp only [Set.mem_Iic, le_div_iff₀ hv] at h₁ h₂
  simp only [lgRf]
  have : 0 < μ - (γ₁ + γ₂) * v / 2 := by nlinarith
  nlinarith [mul_pos (sub_pos.2 h12) this]

/-- AKMM, p. 489: beyond `μ_g/σ_g²` the precautionary motive dominates and the riskless rate
decreases in `γ`. -/
theorem lg_rf_strictAntiOn {β μ v : ℝ} (hv : 0 < v) :
    StrictAntiOn (fun γ => lgRf β γ μ v) (Set.Ici (μ / v)) := by
  intro γ₁ h₁ γ₂ h₂ h12
  simp only [Set.mem_Ici, div_le_iff₀ hv] at h₁ h₂
  simp only [lgRf]
  have : μ - (γ₁ + γ₂) * v / 2 < 0 := by nlinarith
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.2 h12) this]

/-- AKMM, p. 489: with Table 16.1's `μ_g = 0.0175` and `σ_g = 0.0233` the threshold
`μ_g/σ_g²` lies in `(32, 33)`; the smoothing motive dominates below it. -/
theorem lg_threshold_table : 32 < (0.0175 : ℝ) / 0.0233 ^ 2 ∧ (0.0175 : ℝ) / 0.0233 ^ 2 < 33 := by
  constructor <;> rw [div_eq_mul_inv] <;> norm_num

/-- AKMM, p. 489: if `−γg + rˢ ~ N(−γμ_g + Eₜrˢ, γ²σ_g² + σᵣ² − 2γCov(g, rˢ))` (joint
lognormality) and `1 = Eₜ[βe^{−γg + rˢ}]`, then
`Eₜrˢ = −log β + γμ_g − γ²σ_g²/2 − σᵣ²/2 + γCovₜ(g, rˢ)`. -/
theorem lg_equity_euler {g r : Ω → ℝ} {β γ μg μr vg vr c : ℝ} (hβ : 0 < β)
    (hvar : 0 ≤ γ ^ 2 * vg + vr - 2 * γ * c)
    (hX : HasLaw (fun ω => -γ * g ω + r ω)
      (gaussianReal (-γ * μg + μr) ⟨γ ^ 2 * vg + vr - 2 * γ * c, hvar⟩) P)
    (heul : ∫ ω, β * Real.exp (-γ * g ω + r ω) ∂P = 1) :
    μr = -Real.log β + γ * μg - γ ^ 2 * vg / 2 - vr / 2 + γ * c := by
  have h : ∫ ω, Real.exp (-γ * g ω + r ω) * Real.exp (Real.log β) ∂P = 1 := by
    rw [Real.exp_log hβ]
    rw [← heul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have := bp_euler_gaussian hX _ h
  change -γ * μg + μr + (γ ^ 2 * vg + vr - 2 * γ * c) / 2 + Real.log β = 0 at this
  linarith

/-- **(16.30)** (AKMM, p. 489): the equity premium in the CCAPM,
`Eₜrˢ − rᶠ + σᵣ²/2 = γCovₜ(g, rˢ)`, with `rᶠ` from (16.29). -/
theorem eq_16_30 {g r : Ω → ℝ} {β γ μg μr vg vr c : ℝ} (hβ : 0 < β)
    (hvar : 0 ≤ γ ^ 2 * vg + vr - 2 * γ * c)
    (hX : HasLaw (fun ω => -γ * g ω + r ω)
      (gaussianReal (-γ * μg + μr) ⟨γ ^ 2 * vg + vr - 2 * γ * c, hvar⟩) P)
    (heul : ∫ ω, β * Real.exp (-γ * g ω + r ω) ∂P = 1) :
    μr - lgRf β γ μg vg + vr / 2 = γ * c := by
  have := lg_equity_euler hβ hvar hX heul
  unfold lgRf
  linarith

/-- AKMM, p. 489: the Jensen term, `log Eₜ[Rˢ] = Eₜrˢ + σᵣ²/2` for `rˢ = log Rˢ ~ N(Eₜrˢ, σᵣ²)`. -/
theorem lg_jensen {r : Ω → ℝ} {μr : ℝ} {vr : NNReal} (hr : HasLaw r (gaussianReal μr vr) P) :
    Real.log (∫ ω, Real.exp (r ω) ∂P) = μr + vr / 2 := by
  rw [bp_integral_exp_gaussian hr, Real.log_exp]

/-- AKMM, p. 490: `σ_cσ_r = 0.0233 × 0.1836 = 0.00427788`, which is `0.0043` to two significant
figures. -/
theorem lg_sd_product : (0.0233 : ℝ) * 0.1836 = 0.00427788 ∧
    |(0.0233 : ℝ) * 0.1836 - 0.0043| < 0.00003 := by
  constructor
  · norm_num
  · rw [abs_lt]
    constructor <;> norm_num

/-- AKMM, p. 490: since `Cov(g, rˢ) = ρσ_cσ_r ≤ σ_cσ_r`, a premium `γCov(g, rˢ) ≥ 0.07` with the
Table 16.1 volatilities needs `γ ≥ 16.36` (exact certificate:
`16.36 × 0.00427788 = 0.0699861… < 0.07`). -/
theorem lg_gamma_bound {γ ρ : ℝ} (hγ : 0 ≤ γ) (hρ : ρ ≤ 1)
    (h : 0.07 ≤ γ * (ρ * (0.0233 * 0.1836))) : (16.36 : ℝ) ≤ γ := by
  have h1 : γ * (ρ * (0.0233 * 0.1836)) ≤ γ * (0.0233 * 0.1836) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hγ
  by_contra hc
  push Not at hc
  nlinarith

/-- AKMM, p. 490: "risk aversion would need to be high, `γ = 16`" understates the bound: at
`γ = 16`, even with perfect correlation, `γσ_cσ_r = 0.0684… < 0.07`. -/
theorem lg_gamma_16_short : (16 : ℝ) * (0.0233 * 0.1836) < 0.07 := by norm_num

/-- AKMM, p. 490: with `β ≤ 1`, Table 16.1's `μ_g = 0.0175`, `σ_g = 0.0233` and any
`γ ∈ [16, 48]`, the riskless rate (16.29) exceeds its 1% sample mean. -/
theorem lg_rf_high {β γ : ℝ} (hβ0 : 0 < β) (hβ : β ≤ 1) (hγ1 : 16 ≤ γ) (hγ2 : γ ≤ 48) :
    0.01 < lgRf β γ 0.0175 (0.0233 ^ 2) := by
  have hlog : Real.log β ≤ 0 := Real.log_nonpos hβ0.le hβ
  unfold lgRf
  nlinarith [mul_nonneg (sub_nonneg.2 hγ1) (sub_nonneg.2 hγ2)]

end AKMM.AssetPrices
