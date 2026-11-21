/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PAGaussianShocks

/-!
# The Bansal–Yaron long-run risk model

Miao, *Economic Dynamics in Discrete Time*, §20.4.3 (pp. 723–729), equations (20.46)–(20.57).

The model: `g_{t+1} = μ + x_t + σ_t η_{t+1}`, `gd_{t+1} = μ_d + φ x_t + φ_d σ_t u_{t+1}`,
`x_{t+1} = ρ_x x_t + φ_e σ_t e_{t+1}`, `σ²_{t+1} = σ̄² + ν₁(σ_t² − σ̄²) + σ_w w_{t+1}`, with
`η, u, e, w` IID `N(0, 1)`. The state is `(x_t, σ_t)` with `σ_t = s > 0`; the shocks are
`ξ 0 = η`, `ξ 1 = e`, `ξ 2 = w`, `ξ 3 = u` (`PAGaussianShocks`). The parameters are bundled
in the data structure `PABansalYaron` (`ρ` is the inverse EIS, `κ₀, κ₁` and `κ₀ₑ, κ₁ₑ` the
Campbell–Shiller constants of the consumption claim and of equity).

* (20.46): `eq_20_46` (exact identity and linearisation, `κ₁ < 1`); the log-linear wealth
  return `pa_by_rw`.
* (20.47)–(20.49): `eq_20_47`, `eq_20_48`; the log kernel `pa_by_m`.
* Price–consumption ratio `z_t = A₀ + A₁ x_t + A₂ σ_t²`: matching coefficients in (20.49)
  (`pa_by_matching_wealth`), `A₁ = (1 − ρ)/(1 − κ₁ρ_x)` (`pa_by_A1`, `pa_by_A1_pos`),
  `A₂` (`pa_by_A2`, `pa_by_A2_neg`, `pa_by_A2_magnified`).
* (20.50): `eq_20_50`, `pa_by_var_rw`. (20.51): `pa_by_Em`, `eq_20_51`, the prices of risk
  and their signs (`pa_by_lam_eta_neg`, `pa_by_lam_e_pos`, `pa_by_lam_w_neg`,
  `pa_by_lam_w_not_pos`, `pa_by_power_utility`). (20.52): `eq_20_52`. (20.53): `eq_20_53`.
* Equity: (20.54) `eq_20_54`, (20.55) `eq_20_55`, the equity news and variance
  (`pa_by_re_news`, `pa_by_var_re`), (20.56) `eq_20_56`, (20.57) and the coefficients
  (`pa_by_matching_equity`, `pa_by_A1e`, `pa_by_A1e_pos`, `pa_by_A2e`), the unconditional
  decomposition and variances (`pa_by_re_decomp`, `pa_by_uncond_var`).
* The riskfree rate (`pa_by_riskfree`, `pa_by_riskfree_final`, `pa_by_riskfree_state`) and its
  volatility (`pa_by_var_riskfree`).

Departures (see `docs/PA-corrections.md`): the market price of volatility risk
`λ_{m,w} = (γ − ρ)/(1 − ρ) A₂ κ₁` is negative, not positive, when `γ > 1 > ρ`
(`pa_by_lam_w_neg`, `pa_by_lam_w_not_pos`); the `x_t` coefficient of `r_{e,t+1} − E r_{e,t+1}`
is `+ρ`, not `−ρ` (`pa_by_re_decomp`); the riskfree-rate equation has `(γ − ρ)/(1 − ρ) E_t r_w`,
not `(ρ − γ)/(1 − ρ) E_t r_w` (`pa_by_riskfree`), and in `Q₁` the term is `+(γ − ρ)/(1 − ρ) B²`
(`pa_by_riskfree_state`); the equity Campbell–Shiller constant is `κ₁ₑ` throughout (the text
mixes `κ₁` and `κ₁ₑ` in (20.55)); `λ_{e,·}` in (20.56) and `Q₁, Q₂` are `λ_{m,·}`; "an
increase in `ν₁` raises `A₂`" means it raises `|A₂|` (`pa_by_A2_magnified`).
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real Filter Topology

/-- The parameters of the Bansal–Yaron model (Miao, p. 723) and the Campbell–Shiller
constants of the consumption claim (`κ₀, κ₁`) and of equity (`κ₀ₑ, κ₁ₑ`). -/
structure PABansalYaron where
  β : ℝ
  ρ : ℝ
  γ : ℝ
  μ : ℝ
  μd : ℝ
  ρx : ℝ
  φe : ℝ
  σbar2 : ℝ
  ν1 : ℝ
  σw : ℝ
  φ : ℝ
  φd : ℝ
  κ0 : ℝ
  κ1 : ℝ
  κ0e : ℝ
  κ1e : ℝ

/-- `θ = (1 − γ)/(1 − ρ)`. -/
noncomputable def pa_by_θ (M : PABansalYaron) : ℝ := (1 - M.γ) / (1 - M.ρ)

/-- Consumption growth `g_{t+1} = μ + x_t + σ_t η_{t+1}`. -/
def pa_by_g (M : PABansalYaron) (x s η : ℝ) : ℝ := M.μ + x + s * η

/-- `x_{t+1} = ρ_x x_t + φ_e σ_t e_{t+1}`. -/
def pa_by_x' (M : PABansalYaron) (x s e : ℝ) : ℝ := M.ρx * x + M.φe * s * e

/-- `σ²_{t+1} = σ̄² + ν₁(σ_t² − σ̄²) + σ_w w_{t+1}`. -/
def pa_by_v' (M : PABansalYaron) (s w : ℝ) : ℝ := M.σbar2 + M.ν1 * (s ^ 2 - M.σbar2) + M.σw * w

/-- Dividend growth `gd_{t+1} = μ_d + φ x_t + φ_d σ_t u_{t+1}`. -/
def pa_by_gd (M : PABansalYaron) (x s u : ℝ) : ℝ := M.μd + M.φ * x + M.φd * s * u

/-- Miao, (20.46), p. 723: the log return on the consumption claim
`r_{w,t+1} = κ₀ + κ₁ z_{t+1} − z_t + g_{t+1}` with `z_t = A₀ + A₁ x_t + A₂ σ_t²`. -/
def pa_by_rw (M : PABansalYaron) (A0 A1 A2 x s η e w : ℝ) : ℝ :=
  M.κ0 + M.κ1 * (A0 + A1 * pa_by_x' M x s e + A2 * pa_by_v' M s w) - (A0 + A1 * x + A2 * s ^ 2)
    + pa_by_g M x s η

/-- Miao, (20.47), p. 723: the log pricing kernel
`m_{t+1} = θ ln β − ρθ g_{t+1} + (θ − 1) r_{w,t+1}`. -/
noncomputable def pa_by_m (M : PABansalYaron) (A0 A1 A2 x s η e w : ℝ) : ℝ :=
  pa_by_θ M * Real.log M.β - M.ρ * pa_by_θ M * pa_by_g M x s η
    + (pa_by_θ M - 1) * pa_by_rw M A0 A1 A2 x s η e w

/-- Miao, (20.55), p. 727: the log equity return `r_{e,t+1} = κ₀ₑ + κ₁ₑ z_{e,t+1} − z_{e,t} +
gd_{t+1}` with `z_{e,t} = A₀ₑ + A₁ₑ x_t + A₂ₑ σ_t²`. -/
def pa_by_re (M : PABansalYaron) (A0e A1e A2e x s e w u : ℝ) : ℝ :=
  M.κ0e + M.κ1e * (A0e + A1e * pa_by_x' M x s e + A2e * pa_by_v' M s w)
    - (A0e + A1e * x + A2e * s ^ 2) + pa_by_gd M x s u

theorem pa_sum_four (a0 a1 a2 a3 : ℝ) (y : Fin 4 → ℝ) :
    ∑ k, ![a0, a1, a2, a3] k * y k = a0 * y 0 + a1 * y 1 + a2 * y 2 + a3 * y 3 := by
  simp [Fin.sum_univ_four]

/-- Matching coefficients: an identity `K₀ + K₁ x + K₂ s² = 0` for all `x` and all `s > 0`
forces `K₀ = K₁ = K₂ = 0`. -/
theorem pa_match_coeffs {K0 K1 K2 : ℝ}
    (h : ∀ x : ℝ, ∀ s : ℝ, 0 < s → K0 + K1 * x + K2 * s ^ 2 = 0) :
    K0 = 0 ∧ K1 = 0 ∧ K2 = 0 := by
  have h1 := h 0 1 one_pos
  have h2 := h 1 1 one_pos
  have h3 := h 0 2 two_pos
  refine ⟨by linarith, by linarith, by linarith⟩

theorem pa_by_θ_sub_one (M : PABansalYaron) (hρ : M.ρ ≠ 1) :
    pa_by_θ M - 1 = (M.ρ - M.γ) / (1 - M.ρ) := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  simp only [pa_by_θ]
  field_simp
  ring

theorem pa_by_θ_mul (M : PABansalYaron) (hρ : M.ρ ≠ 1) : pa_by_θ M * (1 - M.ρ) = 1 - M.γ := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  simp only [pa_by_θ]
  field_simp

/-- The mean of an affine function of the shocks: `E (c + ∑ a_k ξ_k) = c`. -/
theorem pa_integral_affine_shocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ξ : Fin n → Ω → ℝ}
    (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P) (c : ℝ) (a : Fin n → ℝ) :
    ∫ ω, (c + ∑ k, a k * ξ k ω) ∂P = c := by
  have hI : ∀ k, Integrable (ξ k) P := fun k =>
    memLp_one_iff_integrable.1 ((hlaw k).memLp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top))
  rw [integral_add (integrable_const c) (integrable_finsetSum _ fun k _ => (hI k).const_mul _),
    integral_finsetSum _ fun k _ => (hI k).const_mul _]
  simp only [integral_const_mul, (hlaw _).integral_eq, integral_id_gaussianReal, mul_zero,
    Finset.sum_const_zero, add_zero, integral_const, probReal_univ, one_smul]

/-! ### (20.46)–(20.49) -/

/-- Miao, (20.46), p. 723: with `z = ln(P/C)`, the exact log return on the consumption claim is
`r_{w,t+1} = ln(e^{z_{t+1}} + 1) − z_t + g_{t+1}`; its linearisation at `z̄` has slope
`κ₁ = e^{z̄}/(e^{z̄} + 1) < 1` and intercept `κ₀ = ln(e^{z̄} + 1) − z̄ κ₁`, with an error that is
`o(z_{t+1} − z̄)`. -/
theorem eq_20_46 (zbar : ℝ) :
    (∀ {P P' C C' : ℝ}, 0 < P → 0 < P' → 0 < C → 0 < C' →
      Real.log ((P' + C') / P) = Real.log (Real.exp (Real.log (P' / C')) + 1)
        - Real.log (P / C) + Real.log (C' / C)) ∧
    pa_varrho (-zbar) = Real.exp zbar / (Real.exp zbar + 1) ∧ pa_varrho (-zbar) < 1 ∧
    Real.log (Real.exp zbar + 1) - zbar * pa_varrho (-zbar) = pa_kappa (pa_varrho (-zbar)) ∧
    (fun z => Real.log (Real.exp z + 1) - pa_kappa (pa_varrho (-zbar))
      - pa_varrho (-zbar) * z) =o[𝓝 zbar] fun z => z - zbar := by
  refine ⟨fun {P P' C C'} hP hP' hC hC' => ?_, ?_, pa_varrho_lt_one _, ?_, ?_⟩
  · rw [Real.exp_log (div_pos hP' hC'), Real.log_div hP.ne' hC.ne', Real.log_div hC'.ne' hC.ne',
      Real.log_div (by positivity) hP.ne']
    have : P' / C' + 1 = (P' + C') / C' := by field_simp
    rw [this, Real.log_div (by positivity) hC'.ne']
    ring
  · simp only [pa_varrho, Real.exp_neg]
    have := Real.exp_pos zbar
    field_simp
  · rw [← pa_cs_kappa zbar, add_comm]
    ring
  · have h := (eq_20_36 zbar).2
    refine h.congr_left fun z => ?_
    rw [add_comm]

/-- Miao, (20.47), p. 723: the log of the kernel (20.30) with `C'/C = e^g`, `R_w = e^{r_w}` is
`ln M = (1 − γ)/(1 − ρ) ln β − (1 − γ)ρ/(1 − ρ) g + (ρ − γ)/(1 − ρ) r_w`. -/
theorem eq_20_47 {β ρ γ : ℝ} (hβ : 0 < β) (g r : ℝ) :
    Real.log (pa_Mbar β ρ γ 1 (fun _ : Unit => Real.exp g) (fun _ => Real.exp r) ())
      = (1 - γ) / (1 - ρ) * Real.log β - (1 - γ) * ρ / (1 - ρ) * g
        + (ρ - γ) / (1 - ρ) * r := by
  simp only [pa_Mbar, div_one]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_mul hβ.ne' (by positivity),
    Real.log_rpow (by positivity), Real.log_exp, Real.log_exp]
  ring

/-- Miao, (20.48), p. 724: `M_{t+1} R_{i,t+1} = exp(ln M_{t+1} + r_{i,t+1})`, so the Euler
equation `E_t[M R_i] = 1` is `E_t exp(θ ln β − ρθ g + (θ − 1) r_w + r_i) = 1`; for `r_i = r_w`
this is (20.49), `E_t exp(θ ln β − ρθ g + θ r_w) = 1`. -/
theorem eq_20_48 {β ρ γ : ℝ} (hβ : 0 < β) (g r ri : ℝ) :
    pa_Mbar β ρ γ 1 (fun _ : Unit => Real.exp g) (fun _ => Real.exp r) () * Real.exp ri
      = Real.exp ((1 - γ) / (1 - ρ) * Real.log β - (1 - γ) * ρ / (1 - ρ) * g
        + (ρ - γ) / (1 - ρ) * r + ri) := by
  rw [Real.exp_add, ← eq_20_47 hβ g r, Real.exp_log]
  simp only [pa_Mbar, div_one]
  positivity

/-! ### The price–consumption ratio -/

/-- Miao, p. 724: substituting the conjecture `z_t = A₀ + A₁ x_t + A₂ σ_t²` into (20.46) and
(20.49) and matching the coefficients of `x_t` and `σ_t²`:
`−(1 − γ)ρ/(1 − ρ) + (1 − γ)/(1 − ρ)(κ₁A₁ρ_x − A₁ + 1) = 0` and
`0 = (1 − γ)/(1 − ρ)(κ₁ν₁A₂ − A₂) + ½((1 − γ)² + ((1 − γ)/(1 − ρ) A₁κ₁φ_e)²)`. -/
theorem pa_by_matching_wealth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 : ℝ}
    (h49 : ∀ x s : ℝ, 0 < s → ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)) ∂P = 1) :
    -(1 - M.γ) * M.ρ / (1 - M.ρ) + (1 - M.γ) / (1 - M.ρ) * (M.κ1 * A1 * M.ρx - A1 + 1) = 0 ∧
    0 = (1 - M.γ) / (1 - M.ρ) * (M.κ1 * M.ν1 * A2 - A2)
      + 1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2) := by
  set θ := pa_by_θ M with hθ
  have hθ1 := pa_by_θ_mul M hρ
  rw [← hθ] at hθ1
  have hpt : ∀ x s : ℝ, 0 < s →
      (θ * Real.log M.β - M.ρ * θ * (M.μ + x) + θ * (M.κ0 + M.κ1 * (A0 + A1 * (M.ρx * x)
        + A2 * (M.σbar2 + M.ν1 * (s ^ 2 - M.σbar2))) - (A0 + A1 * x + A2 * s ^ 2) + M.μ + x))
        + (∑ k, ![θ * (1 - M.ρ) * s, θ * M.κ1 * A1 * M.φe * s, θ * M.κ1 * A2 * M.σw, 0] k ^ 2)
          / 2 = 0 := by
    intro x s hs
    rw [← pa_euler_shocks_iff hind hlaw]
    refine Eq.trans ?_ (h49 x s hs)
    congr 1
    funext ω
    congr 1
    rw [pa_sum_four]
    simp only [pa_by_m, pa_by_rw, pa_by_g, pa_by_x', pa_by_v', ← hθ]
    ring
  have hK := pa_match_coeffs (K0 := θ * Real.log M.β - M.ρ * θ * M.μ + θ * (M.κ0 + M.κ1 * (A0
      + A2 * M.σbar2 * (1 - M.ν1)) - A0 + M.μ) + (θ * M.κ1 * A2 * M.σw) ^ 2 / 2)
    (K1 := -M.ρ * θ + θ * (M.κ1 * A1 * M.ρx - A1 + 1))
    (K2 := θ * (M.κ1 * M.ν1 * A2 - A2) + ((θ * (1 - M.ρ)) ^ 2 + (θ * M.κ1 * A1 * M.φe) ^ 2) / 2)
    (fun x s hs => by
      have := hpt x s hs
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
      linear_combination this)
  obtain ⟨-, hK1, hK2⟩ := hK
  have e1 : -(1 - M.γ) * M.ρ / (1 - M.ρ) = -M.ρ * θ := by rw [hθ, pa_by_θ]; ring
  have e2 : (1 - M.γ) / (1 - M.ρ) = θ := by rw [hθ, pa_by_θ]
  rw [e1, e2, ← hθ1]
  constructor
  · linear_combination hK1
  · linear_combination -hK2

/-- Miao, p. 724: solving the `x_t` equation, `A₁ = (1 − ρ)/(1 − κ₁ρ_x)`. -/
theorem pa_by_A1 (M : PABansalYaron) (hρ : M.ρ ≠ 1) (hγ : M.γ ≠ 1) (hk : M.κ1 * M.ρx ≠ 1)
    {A1 : ℝ}
    (h : -(1 - M.γ) * M.ρ / (1 - M.ρ) + (1 - M.γ) / (1 - M.ρ) * (M.κ1 * A1 * M.ρx - A1 + 1) = 0) :
    A1 = (1 - M.ρ) / (1 - M.κ1 * M.ρx) := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - M.γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h3 : (1 : ℝ) - M.κ1 * M.ρx ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  rw [eq_div_iff h3]
  field_simp at h
  have : (1 - M.γ) * ((1 - M.ρ) - A1 * (1 - M.κ1 * M.ρx)) = 0 := by linear_combination h
  have := (mul_eq_zero.1 this).resolve_left h2
  linarith

/-- Miao, p. 724: `A₁ > 0` when the EIS exceeds one (`ρ < 1`) and `κ₁ρ_x < 1`. -/
theorem pa_by_A1_pos (M : PABansalYaron) (hρ : M.ρ < 1) (hk : M.κ1 * M.ρx < 1) :
    0 < (1 - M.ρ) / (1 - M.κ1 * M.ρx) :=
  div_pos (by linarith) (by linarith)

/-- Miao, p. 724: with CRRA utility and `γ = ρ > 1`, `A₁ < 0`: the price–consumption ratio is
countercyclical. -/
theorem pa_by_A1_neg (M : PABansalYaron) (hρ : 1 < M.ρ) (hk : M.κ1 * M.ρx < 1) :
    (1 - M.ρ) / (1 - M.κ1 * M.ρx) < 0 :=
  div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- The closed form `A₂ = ½((1 − γ)² + (θA₁κ₁φ_e)²)/(θ(1 − κ₁ν₁))`, `θ = (1 − γ)/(1 − ρ)`. -/
noncomputable def pa_by_A2formula (M : PABansalYaron) (A1 ν1 : ℝ) : ℝ :=
  1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2)
    / ((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1))

/-- Miao, pp. 724–725: solving the `σ_t²` equation for `A₂`. -/
theorem pa_by_A2 (M : PABansalYaron) (hρ : M.ρ ≠ 1) (hγ : M.γ ≠ 1) (hk : M.κ1 * M.ν1 ≠ 1)
    {A1 A2 : ℝ}
    (h : 0 = (1 - M.γ) / (1 - M.ρ) * (M.κ1 * M.ν1 * A2 - A2)
      + 1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2)) :
    A2 = pa_by_A2formula M A1 M.ν1 := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - M.γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h3 : (1 : ℝ) - M.κ1 * M.ν1 ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  have hθ : (1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * M.ν1) ≠ 0 :=
    mul_ne_zero (div_ne_zero h2 h1) h3
  simp only [pa_by_A2formula]
  rw [eq_div_iff hθ]
  linear_combination h

/-- Miao, p. 725: if `γ > 1` and `ρ < 1` (and `κ₁ν₁ < 1`), then `A₂ < 0`: a rise in volatility
lowers the price–consumption ratio. -/
theorem pa_by_A2_neg (M : PABansalYaron) (hρ : M.ρ < 1) (hγ : 1 < M.γ) (hk : M.κ1 * M.ν1 < 1)
    (A1 : ℝ) : pa_by_A2formula M A1 M.ν1 < 0 := by
  simp only [pa_by_A2formula]
  have hθ : (1 - M.γ) / (1 - M.ρ) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  apply div_neg_of_pos_of_neg
  · have : 0 < (1 - M.γ) ^ 2 := by nlinarith
    positivity
  · exact mul_neg_of_neg_of_pos hθ (by linarith)

/-- Miao, p. 725: an increase in `ν₁` magnifies the (negative) effect of volatility on the
price–consumption ratio: for `ν₁ < ν₁'` with `κ₁ν₁' < 1` and `κ₁ > 0`, `A₂(ν₁') < A₂(ν₁) < 0`
(the text's "raises `A₂`" is "raises `|A₂|`"). -/
theorem pa_by_A2_magnified (M : PABansalYaron) (hρ : M.ρ < 1) (hγ : 1 < M.γ) (hκ : 0 < M.κ1)
    {ν1 ν1' : ℝ} (hν : ν1 < ν1') (hk : M.κ1 * ν1' < 1) (A1 : ℝ) :
    pa_by_A2formula M A1 ν1' < pa_by_A2formula M A1 ν1 := by
  simp only [pa_by_A2formula]
  have hθ : (1 - M.γ) / (1 - M.ρ) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hN : 0 < 1 / 2 * ((1 - M.γ) ^ 2 + ((1 - M.γ) / (1 - M.ρ) * A1 * M.κ1 * M.φe) ^ 2) := by
    have : 0 < (1 - M.γ) ^ 2 := by nlinarith
    positivity
  have hk' : M.κ1 * ν1 < M.κ1 * ν1' := mul_lt_mul_of_pos_left hν hκ
  have hd1 : 0 < 1 - M.κ1 * ν1' := by linarith
  have hd2 : 1 - M.κ1 * ν1' < 1 - M.κ1 * ν1 := by linarith
  have hD1 : 0 < -((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1')) := by
    have := mul_neg_of_neg_of_pos hθ hd1; linarith
  have hD12 : -((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1'))
      < -((1 - M.γ) / (1 - M.ρ) * (1 - M.κ1 * ν1)) := by
    have := mul_lt_mul_of_neg_left hd2 hθ; linarith
  have := div_lt_div_of_pos_left hN hD1 hD12
  rw [div_neg, div_neg] at this
  linarith

end Miao.RecursiveUtility
