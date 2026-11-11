/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PACampbellShiller
import Mathlib.Probability.Moments.Covariance

/-!
# Equity volatility and equity premium puzzles with a simple long-run risk process

Miao, *Economic Dynamics in Discrete Time*, §20.4.2 (pp. 719–722), equations (20.42)–(20.45).

Consumption growth is `Δc_{t+1} = z_t + ε_{c,t+1}`, `z_{t+1} = (1 − φ)g + φ z_t + ε_{z,t+1}`.

* Forecasts: `E_t Δc_{t+1+j} = E_t z_{t+j} = g + φʲ(z_t − g)` (`pa_forecast`, built by iterating
  the conditional mean `pa_forecast_succ`), and the revisions
  `(E_{t+1} − E_t)Δc_{t+1+j} = φ^{j−1} ε_{z,t+1}`, `j ≥ 1` (`pa_forecast_revision`).
* The discounted sums `∑ ϱⁱ E_t Δc_{t+1+i} = g/(1 − ϱ) + (z_t − g)/(1 − ϱφ)`
  (`pa_sum_forecast`) and `∑_{j≥1} ϱʲ φ^{j−1} ε_z = ϱ/(1 − ϱφ) ε_z` (`pa_sum_revision`).
* (20.42)–(20.43): `eq_20_42`, `eq_20_43`; the price–dividend ratio is procyclical when
  `λ > ρ` (`pa_pd_procyclical`); the real consol (`λ = 0`): `pa_consol_yield`,
  `pa_consol_news`, and the printed `λ = 1` is wrong (`pa_consol_lambda_one_counterexample`).
* The equity premium: `σ_iw = σ_ic + (1 − ρ) σ_ig` (`pa_sigma_iw`), the premium
  `E_t r_i − r_f + ½σ_i² = γ σ_ic + (γ − ρ) σ_ig` (`pa_premium_gamma`), the long-run-risk
  covariances (`pa_lrr_cov`), the equity premium (`pa_lrr_equity_premium`), (20.44)
  (`eq_20_44`) and (20.45) (`eq_20_45`). Covariances are Mathlib's `cov[X, Y; P]`.

Departures (see `docs/PA-corrections.md`): the consol bond is `λ = 0` (the text says "setting
`λ = 1`" for the bond formulas, which hold for `λ = 0` only); in the wealth-return news and in
`σ_ig` the revision sum starts at `j = 1` and is discounted by `ϱʲ` (the text writes `∑_{j≥0}`
and `ρⁱ`), as the derivation of the premium formula requires.
-/

namespace Miao.RecursiveUtility

open Real Filter Topology MeasureTheory ProbabilityTheory

/-- Miao, p. 719: the forecast `E_t Δc_{t+1+j} = E_t z_{t+j} = g + φʲ (z_t − g)`. -/
noncomputable def pa_forecast (g φ z : ℝ) (j : ℕ) : ℝ := g + φ ^ j * (z - g)

theorem pa_forecast_zero (g φ z : ℝ) : pa_forecast g φ z 0 = z := by
  simp [pa_forecast]

/-- The forecasts are obtained by iterating the conditional mean of the AR(1) process,
`E_t z_{t+j+1} = (1 − φ) g + φ E_t z_{t+j}` (the law of iterated expectations). -/
theorem pa_forecast_succ (g φ z : ℝ) (j : ℕ) :
    pa_forecast g φ z (j + 1) = (1 - φ) * g + φ * pa_forecast g φ z j := by
  simp only [pa_forecast, pow_succ]
  ring

/-- Miao, p. 721: the revision of the forecast of `Δc_{t+2+j}` between `t` and `t + 1`,
`E_{t+1} Δc_{t+2+j} − E_t Δc_{t+2+j} = φʲ ε_{z,t+1}`, `ε_{z,t+1} = z_{t+1} − (1 − φ)g − φ z_t`. -/
theorem pa_forecast_revision (g φ z z' : ℝ) (j : ℕ) :
    pa_forecast g φ z' j - pa_forecast g φ z (j + 1) = φ ^ j * (z' - (1 - φ) * g - φ * z) := by
  simp only [pa_forecast, pow_succ]
  ring

/-- Miao, p. 719: `∑_{i≥0} ϱⁱ E_t Δc_{t+1+i} = g/(1 − ϱ) + (z_t − g)/(1 − ϱφ)`. -/
theorem pa_sum_forecast {ϱ φ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1) (g z : ℝ) :
    HasSum (fun i => ϱ ^ i * pa_forecast g φ z i) (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  have hab : |ϱ * φ| < 1 := by
    rw [abs_mul, abs_of_nonneg hϱ0]
    calc ϱ * |φ| ≤ 1 * |φ| := mul_le_mul_of_nonneg_right hϱ1.le (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact hφ
  have h1 := (hasSum_geometric_of_lt_one hϱ0 hϱ1).mul_left g
  have h2 := (hasSum_geometric_of_abs_lt_one hab).mul_left (z - g)
  convert h1.add h2 using 1
  · funext i
    simp only [pa_forecast, mul_pow]
    ring
  · simp only [div_eq_mul_inv]

/-- Miao, p. 721: `(E_{t+1} − E_t) ∑_{j≥1} ϱʲ Δc_{t+1+j} = ∑_{j≥0} ϱ^{j+1} φʲ ε_z
= ϱ/(1 − ϱφ) ε_{z,t+1}`. -/
theorem pa_sum_revision {ϱ φ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1) (εz : ℝ) :
    HasSum (fun j : ℕ => ϱ ^ (j + 1) * (φ ^ j * εz)) (ϱ / (1 - ϱ * φ) * εz) := by
  have hab : |ϱ * φ| < 1 := by
    rw [abs_mul, abs_of_nonneg hϱ0]
    calc ϱ * |φ| ≤ 1 * |φ| := mul_le_mul_of_nonneg_right hϱ1.le (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact hφ
  convert (hasSum_geometric_of_abs_lt_one hab).mul_left (ϱ * εz) using 1
  · funext j
    rw [mul_pow, pow_succ]
    ring
  · rw [div_eq_mul_inv]
    ring

/-- Miao, (20.42), p. 719: substituting the long-run risk forecasts into (20.40),
`pe_t − de_t = k_e/(1 − ϱ) + (λ − ρ)(g/(1 − ϱ) + (z_t − g)/(1 − ϱφ))`. -/
theorem eq_20_42 {ϱ φ g z ke lam ρ pd Gbar : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1)
    (h40 : pd = ke / (1 - ϱ) + (lam - ρ) * Gbar)
    (hG : HasSum (fun i => ϱ ^ i * pa_forecast g φ z i) Gbar) :
    pd = ke / (1 - ϱ) + (lam - ρ) * (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  rw [h40, hG.unique (pa_sum_forecast hϱ0 hϱ1 hφ g z)]

/-- Miao, (20.43), p. 719: substituting the forecast revisions into (20.41),
`r_{e,t+1} − E_t r_{e,t+1} = λ ε_{c,t+1} + (λ − ρ) ϱ/(1 − ϱφ) ε_{z,t+1}`. -/
theorem eq_20_43 {ϱ φ g z z' lam ρ news εc εz Rev : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    (hφ : |φ| < 1) (h41 : news = lam * εc + (lam - ρ) * Rev)
    (hRev : HasSum (fun j : ℕ => ϱ ^ (j + 1) *
      (pa_forecast g φ z' j - pa_forecast g φ z (j + 1))) Rev)
    (hεz : εz = z' - (1 - φ) * g - φ * z) :
    news = lam * εc + (lam - ρ) * (ϱ / (1 - ϱ * φ)) * εz := by
  have h := pa_sum_revision hϱ0 hϱ1 hφ εz
  simp only [pa_forecast_revision, ← hεz] at hRev
  rw [h41, hRev.unique h]
  ring

/-- Miao, p. 719: by (20.42) the price–dividend ratio is procyclical (increasing in `z_t`) when
`λ > ρ`. -/
theorem pa_pd_procyclical {ϱ φ g ke lam ρ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1)
    (hlam : ρ < lam) :
    StrictMono fun z : ℝ => ke / (1 - ϱ) + (lam - ρ) * (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  have hpos : 0 < 1 - ϱ * φ := by
    have : ϱ * φ ≤ ϱ * |φ| := mul_le_mul_of_nonneg_left (le_abs_self φ) hϱ0
    have : ϱ * |φ| < 1 := by
      calc ϱ * |φ| ≤ 1 * |φ| := mul_le_mul_of_nonneg_right hϱ1.le (abs_nonneg _)
        _ < 1 := by rw [one_mul]; exact hφ
    linarith
  intro z₁ z₂ h
  have : (z₁ - g) / (1 - ϱ * φ) < (z₂ - g) / (1 - ϱ * φ) :=
    div_lt_div_of_pos_right (by linarith) hpos
  have := mul_lt_mul_of_pos_left this (sub_pos.2 hlam)
  simp only
  nlinarith

/-- Miao, p. 720: the real consol bond is the claim with `λ = 0`; its log yield is
`y_{bt} = d_{bt} − p_{bt} = −k_b/(1 − ϱ) + ρ(g/(1 − ϱ) + (z_t − g)/(1 − ϱφ))`. -/
theorem pa_consol_yield {ϱ φ g z kb ρ pd Gbar : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1) (hφ : |φ| < 1)
    (h40 : pd = kb / (1 - ϱ) + (0 - ρ) * Gbar)
    (hG : HasSum (fun i => ϱ ^ i * pa_forecast g φ z i) Gbar) :
    -pd = -(kb / (1 - ϱ)) + ρ * (g / (1 - ϱ) + (z - g) / (1 - ϱ * φ)) := by
  rw [eq_20_42 hϱ0 hϱ1 hφ h40 hG]
  ring

/-- Miao, p. 720: the unexpected return on the real consol (`λ = 0`),
`r_{b,t+1} − E_t r_{b,t+1} = −ρ ϱ/(1 − ϱφ) ε_{z,t+1}`. -/
theorem pa_consol_news {ϱ φ g z z' ρ news εc εz Rev : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ1 : ϱ < 1)
    (hφ : |φ| < 1) (h41 : news = 0 * εc + (0 - ρ) * Rev)
    (hRev : HasSum (fun j : ℕ => ϱ ^ (j + 1) *
      (pa_forecast g φ z' j - pa_forecast g φ z (j + 1))) Rev)
    (hεz : εz = z' - (1 - φ) * g - φ * z) :
    news = -ρ * (ϱ / (1 - ϱ * φ)) * εz := by
  rw [eq_20_43 hϱ0 hϱ1 hφ h41 hRev hεz]
  ring

/-- Miao, p. 720 (correction): "setting `λ = 1`" in (20.43) does not give the consol news
`−ρ ϱ/(1 − ϱφ) ε_z`: with `ε_c = 1`, `ε_z = 0` the `λ = 1` formula gives `1`. -/
theorem pa_consol_lambda_one_counterexample (ρ K : ℝ) :
    ¬ ∀ εc εz : ℝ, 1 * εc + (1 - ρ) * K * εz = -ρ * K * εz := by
  intro h
  have := h 1 0
  norm_num at this

/-- Miao, p. 720: the wealth portfolio is the case `λ = 1` of (20.41),
`r_w − E_t r_w = (Δc − E_t Δc) + (1 − ρ) G` with `G` the revision of
`∑_{j≥1} ϱʲ Δc_{t+1+j}`; hence for any asset `i`, `σ_iw = σ_ic + (1 − ρ) σ_ig`. -/
theorem pa_sigma_iw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ni εc G : Ω → ℝ} (hni : MemLp ni 2 P) (hεc : MemLp εc 2 P) (hG : MemLp G 2 P) (ρ : ℝ) :
    cov[ni, fun ω => εc ω + (1 - ρ) * G ω; P] = cov[ni, εc; P] + (1 - ρ) * cov[ni, G; P] := by
  rw [show (fun ω => εc ω + (1 - ρ) * G ω) = εc + fun ω => (1 - ρ) * G ω from rfl,
    covariance_add_right hni hεc (hG.const_mul _), covariance_const_mul_right]

/-- Miao, p. 721: substituting `σ_iw = σ_ic + (1 − ρ)σ_ig` into (20.35),
`E_t r_i − r_f + ½σ_i² = γ σ_ic + (γ − ρ) σ_ig`. -/
theorem pa_premium_gamma {ρ γ m rf vi σic σiw σig : ℝ} (hρ : ρ ≠ 1)
    (h35 : m - rf + 1 / 2 * vi = ρ * (1 - γ) / (1 - ρ) * σic + (γ - ρ) / (1 - ρ) * σiw)
    (hσ : σiw = σic + (1 - ρ) * σig) :
    m - rf + 1 / 2 * vi = γ * σic + (γ - ρ) * σig := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  rw [h35, hσ]
  field_simp
  ring

/-- Miao, p. 721: with the long-run risk news `n_e = λ ε_c + (λ − ρ) K ε_z` (20.43),
`K = ϱ/(1 − ϱφ)`, and revision `G = K ε_z`,
`σ_ec = λ σ_c² + (λ − ρ) K σ_cz` and `σ_eg = λ K σ_cz + (λ − ρ) K² σ_z²`. -/
theorem pa_lrr_cov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {εc εz : Ω → ℝ} (hc : MemLp εc 2 P) (hz : MemLp εz 2 P) (lam ρ K : ℝ) :
    cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, εc; P]
        = lam * cov[εc, εc; P] + (lam - ρ) * K * cov[εc, εz; P] ∧
      cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, fun ω => K * εz ω; P]
        = lam * K * cov[εc, εz; P] + (lam - ρ) * K ^ 2 * cov[εz, εz; P] := by
  have hsplit : (fun ω => lam * εc ω + (lam - ρ) * K * εz ω)
      = (fun ω => lam * εc ω) + fun ω => (lam - ρ) * K * εz ω := rfl
  rw [hsplit, covariance_add_left (hc.const_mul _) (hz.const_mul _) hc,
    covariance_add_left (hc.const_mul _) (hz.const_mul _) (hz.const_mul _),
    covariance_const_mul_left, covariance_const_mul_left, covariance_const_mul_left,
    covariance_const_mul_left, covariance_const_mul_right, covariance_const_mul_right,
    covariance_comm εz εc]
  constructor <;> ring

/-- Miao, p. 721: the equity premium in the long-run risk model,
`E_t r_e − r_f + σ_e²/2 = γ(λσ_c² + (λ − ρ)Kσ_cz) + (γ − ρ)(λKσ_cz + (λ − ρ)K²σ_z²)`. -/
theorem pa_lrr_equity_premium {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {εc εz : Ω → ℝ} (hc : MemLp εc 2 P) (hz : MemLp εz 2 P)
    {lam ρ γ K m rf ve : ℝ}
    (hprem : m - rf + 1 / 2 * ve = γ * cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, εc; P]
      + (γ - ρ) * cov[fun ω => lam * εc ω + (lam - ρ) * K * εz ω, fun ω => K * εz ω; P]) :
    m - rf + ve / 2 = γ * (lam * cov[εc, εc; P] + (lam - ρ) * K * cov[εc, εz; P])
      + (γ - ρ) * (lam * K * cov[εc, εz; P] + (lam - ρ) * K ^ 2 * cov[εz, εz; P]) := by
  obtain ⟨h1, h2⟩ := pa_lrr_cov hc hz lam ρ K
  rw [h1, h2] at hprem
  linarith

/-- Miao, (20.44), p. 721: the real bond premium (`λ = 0`),
`E_t r_b − r_f + σ_b²/2 = −ργ K σ_cz − (γ − ρ) ρ K² σ_z²`, `K = ϱ/(1 − ϱφ)`. -/
theorem eq_20_44 {ρ γ K mb rf vb vc vcz vz : ℝ}
    (h : mb - rf + vb / 2 = γ * (0 * vc + (0 - ρ) * K * vcz)
      + (γ - ρ) * (0 * K * vcz + (0 - ρ) * K ^ 2 * vz)) :
    mb - rf + vb / 2 = -ρ * γ * K * vcz - (γ - ρ) * ρ * K ^ 2 * vz := by
  linarith

/-- Miao, (20.45), p. 721: the premium of equities over real bonds,
`E_t[r_e − r_b] + σ_e²/2 − σ_b²/2 = γλ(σ_c² + Kσ_cz) + (γ − ρ)λ(Kσ_cz + K²σ_z²)`. -/
theorem eq_20_45 {ρ γ K lam me mb rf ve vb vc vcz vz : ℝ}
    (he : me - rf + ve / 2 = γ * (lam * vc + (lam - ρ) * K * vcz)
      + (γ - ρ) * (lam * K * vcz + (lam - ρ) * K ^ 2 * vz))
    (hb : mb - rf + vb / 2 = γ * (0 * vc + (0 - ρ) * K * vcz)
      + (γ - ρ) * (0 * K * vcz + (0 - ρ) * K ^ 2 * vz)) :
    (me - mb) + ve / 2 - vb / 2
      = γ * lam * (vc + K * vcz) + (γ - ρ) * lam * (K * vcz + K ^ 2 * vz) := by
  linear_combination he - hb

/-- Miao, p. 722: in (20.44) the power-utility term `−ργKσ_cz` is negative when `σ_cz > 0`
(real bonds hedge), and the Epstein–Zin term `−(γ − ρ)ρK²σ_z²` is negative when `γ > ρ`
(a negative term premium). -/
theorem pa_term_premium_signs {ρ γ K vcz vz : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hK : K ≠ 0)
    (hγρ : ρ < γ) (hvz : 0 < vz) :
    (0 < K * vcz → -ρ * γ * K * vcz < 0) ∧ -(γ - ρ) * ρ * K ^ 2 * vz < 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have : 0 < ρ * γ * (K * vcz) := by positivity
    linarith
  · have : 0 < (γ - ρ) * ρ * K ^ 2 * vz := by
      have := sub_pos.2 hγρ
      positivity
    linarith

end Miao.RecursiveUtility
