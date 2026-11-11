/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveUtility.PALongRunRisk

/-!
# The Bansal–Yaron model: pricing kernel, risk premia and the riskfree rate

Miao, *Economic Dynamics in Discrete Time*, §20.4.3 (pp. 725–729), equations (20.50)–(20.57)
and the riskfree rate. The setting and the notation are those of `PALongRunRisk`; the
shocks are `ξ 0 = η`, `ξ 1 = e`, `ξ 2 = w`, `ξ 3 = u`, IID `N(0, 1)` under `P`.

The conditional mean of a variable that is affine in the shocks is its value at zero shocks
(`pa_by_Erw`, `pa_by_Em_integral`, `pa_by_Ere`), and its news is the difference.
-/

namespace Miao.RecursiveUtility

open MeasureTheory ProbabilityTheory Real

/-- `B = κ₁A₁φ_e` (Miao, (20.50), p. 725). -/
def pa_by_B (M : PABansalYaron) (A1 : ℝ) : ℝ := M.κ1 * A1 * M.φe

/-- The market price of short-run risk `λ_{m,η} = −γ` (Miao, p. 725). -/
def pa_by_lam_eta (M : PABansalYaron) : ℝ := -M.γ

/-- The market price of long-run risk `λ_{m,e} = (γ − ρ)/(1 − ρ) A₁κ₁φ_e` (Miao, p. 725). -/
noncomputable def pa_by_lam_e (M : PABansalYaron) (A1 : ℝ) : ℝ :=
  (M.γ - M.ρ) / (1 - M.ρ) * (A1 * M.κ1 * M.φe)

/-- The market price of volatility risk `λ_{m,w} = (γ − ρ)/(1 − ρ) A₂κ₁` (Miao, p. 725). -/
noncomputable def pa_by_lam_w (M : PABansalYaron) (A2 : ℝ) : ℝ :=
  (M.γ - M.ρ) / (1 - M.ρ) * A2 * M.κ1

/-- `β_{e,e} = κ₁ₑA₁ₑφ_e` (Miao, p. 727). -/
def pa_by_bee (M : PABansalYaron) (A1e : ℝ) : ℝ := M.κ1e * A1e * M.φe

/-- `β_{e,w} = κ₁ₑA₂ₑ` (Miao, p. 727). -/
def pa_by_bew (M : PABansalYaron) (A2e : ℝ) : ℝ := M.κ1e * A2e

theorem pa_by_gamma_rho (M : PABansalYaron) (hρ : M.ρ ≠ 1) :
    (M.γ - M.ρ) / (1 - M.ρ) = 1 - pa_by_θ M := by
  have h1 : (1 : ℝ) - M.ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  simp only [pa_by_θ]
  field_simp
  ring

/-! ### The wealth return (20.50) -/

/-- Miao, (20.50), p. 725: `r_{w,t+1} − E_t r_{w,t+1} = σ_t η + Bσ_t e + A₂κ₁σ_w w`. -/
theorem eq_20_50 (M : PABansalYaron) (A0 A1 A2 x s η e w : ℝ) :
    pa_by_rw M A0 A1 A2 x s η e w - pa_by_rw M A0 A1 A2 x s 0 0 0
      = s * η + pa_by_B M A1 * s * e + A2 * M.κ1 * M.σw * w := by
  simp only [pa_by_rw, pa_by_x', pa_by_v', pa_by_g, pa_by_B]
  ring

theorem pa_by_rw_affine (M : PABansalYaron) (A0 A1 A2 x s : ℝ) {Ω : Type*}
    (ξ : Fin 4 → Ω → ℝ) (ω : Ω) :
    pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) = pa_by_rw M A0 A1 A2 x s 0 0 0
      + ∑ k, ![s, pa_by_B M A1 * s, A2 * M.κ1 * M.σw, 0] k * ξ k ω := by
  rw [pa_sum_four, ← eq_20_50]
  ring

/-- `E_t r_{w,t+1}` is `r_w` at zero shocks. -/
theorem pa_by_Erw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0 A1 A2 x s : ℝ) :
    ∫ ω, pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) ∂P = pa_by_rw M A0 A1 A2 x s 0 0 0 := by
  simp only [pa_by_rw_affine M A0 A1 A2 x s ξ]
  exact pa_integral_affine_shocks hlaw _ _

/-- Miao, p. 725: `Var_t(r_{w,t+1}) = (1 + B²)σ_t² + (A₂κ₁)²σ_w²`. -/
theorem pa_by_var_rw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0 A1 A2 x s : ℝ) :
    cov[fun ω => pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_rw M A0 A1 A2 x s 0 0 0,
      fun ω => pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_rw M A0 A1 A2 x s 0 0 0;
      P] = (1 + pa_by_B M A1 ^ 2) * s ^ 2 + (A2 * M.κ1) ^ 2 * M.σw ^ 2 := by
  simp only [pa_by_rw_affine M A0 A1 A2 x s ξ, add_sub_cancel_left]
  rw [pa_cov_shocks hind hlaw]
  simp [Fin.sum_univ_four]
  ring

/-! ### The pricing kernel (20.51)–(20.52) -/

/-- Miao, p. 725: `E_t m_{t+1} = m₀ − ρ x_t + A₂(κ₁ν₁ − 1)(ρ − γ)/(1 − ρ) σ_t²`, where
`m₀` is the value at `x_t = σ_t = 0` and `A₁` solves its matching equation. -/
theorem pa_by_Em (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 : ℝ}
    (hA1 : A1 * (1 - M.κ1 * M.ρx) = 1 - M.ρ) (x s : ℝ) :
    pa_by_m M A0 A1 A2 x s 0 0 0 = pa_by_m M A0 A1 A2 0 0 0 0 0 - M.ρ * x
      + A2 * (M.κ1 * M.ν1 - 1) * ((M.ρ - M.γ) / (1 - M.ρ)) * s ^ 2 := by
  rw [← pa_by_θ_sub_one M hρ]
  simp only [pa_by_m, pa_by_rw, pa_by_x', pa_by_v', pa_by_g]
  linear_combination -(pa_by_θ M - 1) * x * hA1

/-- Miao, (20.51), p. 725: the innovation of the log kernel,
`m_{t+1} − E_t m_{t+1} = λ_{m,η}σ_t η − λ_{m,e}σ_t e − λ_{m,w}σ_w w`. -/
theorem eq_20_51 (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s η e w : ℝ) :
    pa_by_m M A0 A1 A2 x s η e w - pa_by_m M A0 A1 A2 x s 0 0 0
      = pa_by_lam_eta M * s * η - pa_by_lam_e M A1 * s * e - pa_by_lam_w M A2 * M.σw * w := by
  have hθ1 := pa_by_θ_mul M hρ
  simp only [pa_by_lam_eta, pa_by_lam_e, pa_by_lam_w, pa_by_gamma_rho M hρ]
  simp only [pa_by_m, pa_by_rw, pa_by_x', pa_by_v', pa_by_g]
  linear_combination (s * η) * hθ1

theorem pa_by_m_affine (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s : ℝ) {Ω : Type*}
    (ξ : Fin 4 → Ω → ℝ) (ω : Ω) :
    pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) = pa_by_m M A0 A1 A2 x s 0 0 0
      + ∑ k, ![pa_by_lam_eta M * s, -(pa_by_lam_e M A1 * s), -(pa_by_lam_w M A2 * M.σw), 0] k
        * ξ k ω := by
  rw [pa_sum_four, ← sub_eq_iff_eq_add', eq_20_51 M hρ]
  ring

/-- `E_t m_{t+1}` is `m` at zero shocks. -/
theorem pa_by_Em_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : Fin 4 → Ω → ℝ} (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s : ℝ) :
    ∫ ω, pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) ∂P = pa_by_m M A0 A1 A2 x s 0 0 0 := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ]
  exact pa_integral_affine_shocks hlaw _ _

/-- Miao, p. 725: `λ_{m,η} = −γ < 0`. -/
theorem pa_by_lam_eta_neg (M : PABansalYaron) (hγ : 0 < M.γ) : pa_by_lam_eta M < 0 := by
  simp only [pa_by_lam_eta]; linarith

/-- Miao, p. 726: `λ_{m,e} > 0` when the agent prefers early resolution (`γ > ρ`), the EIS
exceeds one (`ρ < 1`) and `A₁κ₁φ_e > 0`. -/
theorem pa_by_lam_e_pos (M : PABansalYaron) (hγρ : M.ρ < M.γ) (hρ : M.ρ < 1) {A1 : ℝ}
    (hA : 0 < A1 * M.κ1 * M.φe) : 0 < pa_by_lam_e M A1 :=
  mul_pos (div_pos (by linarith) (by linarith)) hA

/-- Miao, p. 726 (correction): the market price of volatility risk is negative,
`λ_{m,w} = (γ − ρ)/(1 − ρ) A₂κ₁ < 0`, when `γ > ρ`, `ρ < 1`, `κ₁ > 0` and `A₂ < 0`. -/
theorem pa_by_lam_w_neg (M : PABansalYaron) (hγρ : M.ρ < M.γ) (hρ : M.ρ < 1) (hκ : 0 < M.κ1)
    {A2 : ℝ} (hA2 : A2 < 0) : pa_by_lam_w M A2 < 0 := by
  simp only [pa_by_lam_w]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (div_pos (by linarith) (by linarith)) hA2)
    hκ

/-- Miao, p. 726 (counterexample to "the last two terms are positive"): with `γ > 1 > ρ`,
`κ₁ > 0`, `κ₁ν₁ < 1` and `A₂` from its matching equation, `λ_{m,w}` is not positive. -/
theorem pa_by_lam_w_not_pos (M : PABansalYaron) (hρ : M.ρ < 1) (hγ : 1 < M.γ) (hκ : 0 < M.κ1)
    (hk : M.κ1 * M.ν1 < 1) (A1 : ℝ) : ¬ 0 < pa_by_lam_w M (pa_by_A2formula M A1 M.ν1) :=
  not_lt.2 (pa_by_lam_w_neg M (by linarith) hρ hκ (pa_by_A2_neg M hρ hγ hk A1)).le

/-- Miao, p. 726: for power utility (`γ = ρ`) `λ_{m,e} = λ_{m,w} = 0`. -/
theorem pa_by_power_utility (M : PABansalYaron) (h : M.γ = M.ρ) (A1 A2 : ℝ) :
    pa_by_lam_e M A1 = 0 ∧ pa_by_lam_w M A2 = 0 := by
  simp [pa_by_lam_e, pa_by_lam_w, h]

/-- Miao, (20.52), p. 726: `Var_t(m_{t+1}) = (λ_{m,η}² + λ_{m,e}²)σ_t² + λ_{m,w}²σ_w²`. -/
theorem eq_20_52 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) (A0 A1 A2 x s : ℝ) :
    cov[fun ω => pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_m M A0 A1 A2 x s 0 0 0,
      fun ω => pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) - pa_by_m M A0 A1 A2 x s 0 0 0; P]
      = (pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2) * s ^ 2
        + pa_by_lam_w M A2 ^ 2 * M.σw ^ 2 := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ, add_sub_cancel_left]
  rw [pa_cov_shocks hind hlaw]
  simp [Fin.sum_univ_four]
  ring

/-- Miao, (20.53), p. 726: the risk premium on the wealth portfolio. From the Euler equations
for `R_w` and `R_f` under lognormality,
`E_t(r_w − r_f) = −λ_{m,η}σ_t² + λ_{m,e}Bσ_t² + κ₁A₂λ_{m,w}σ_w² − ½Var_t(r_w)`. -/
theorem eq_20_53 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 x s rf : ℝ}
    (hw : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_rw M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    pa_by_rw M A0 A1 A2 x s 0 0 0 - rf
      = -pa_by_lam_eta M * s ^ 2 + pa_by_lam_e M A1 * pa_by_B M A1 * s ^ 2
        + M.κ1 * A2 * pa_by_lam_w M A2 * M.σw ^ 2
        - 1 / 2 * ((1 + pa_by_B M A1 ^ 2) * s ^ 2 + (A2 * M.κ1) ^ 2 * M.σw ^ 2) := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ,
    pa_by_rw_affine M A0 A1 A2 x s ξ] at hw hf
  rw [pa_lognormal_premium hind hlaw hw hf]
  simp [Fin.sum_univ_four]
  ring

/-! ### Equity (20.54)–(20.57) -/

/-- Miao, (20.55), p. 727: the Campbell–Shiller form of the equity return,
`r_{e,t+1} = gd_{t+1} + κ₁ₑA₁ₑx_{t+1} − A₁ₑx_t + κ₁ₑA₂ₑσ²_{t+1} − A₂ₑσ_t² + constant`. -/
theorem eq_20_55 (M : PABansalYaron) (A0e A1e A2e x s e w u : ℝ) :
    pa_by_re M A0e A1e A2e x s e w u = pa_by_gd M x s u + M.κ1e * A1e * pa_by_x' M x s e
      - A1e * x + M.κ1e * A2e * pa_by_v' M s w - A2e * s ^ 2
      + (M.κ0e + M.κ1e * A0e - A0e) := by
  simp only [pa_by_re]
  ring

/-- Miao, p. 727: `r_{e,t+1} − E_t r_{e,t+1} = φ_dσ_t u + β_{e,e}σ_t e + β_{e,w}σ_w w`. -/
theorem pa_by_re_news (M : PABansalYaron) (A0e A1e A2e x s e w u : ℝ) :
    pa_by_re M A0e A1e A2e x s e w u - pa_by_re M A0e A1e A2e x s 0 0 0
      = M.φd * s * u + pa_by_bee M A1e * s * e + pa_by_bew M A2e * M.σw * w := by
  simp only [pa_by_re, pa_by_x', pa_by_v', pa_by_gd, pa_by_bee, pa_by_bew]
  ring

theorem pa_by_re_affine (M : PABansalYaron) (A0e A1e A2e x s : ℝ) {Ω : Type*}
    (ξ : Fin 4 → Ω → ℝ) (ω : Ω) :
    pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω) = pa_by_re M A0e A1e A2e x s 0 0 0
      + ∑ k, ![0, pa_by_bee M A1e * s, pa_by_bew M A2e * M.σw, M.φd * s] k * ξ k ω := by
  rw [pa_sum_four, ← sub_eq_iff_eq_add', pa_by_re_news]
  ring

/-- `E_t r_{e,t+1}` is `r_e` at zero shocks. -/
theorem pa_by_Ere {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0e A1e A2e x s : ℝ) :
    ∫ ω, pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω) ∂P
      = pa_by_re M A0e A1e A2e x s 0 0 0 := by
  simp only [pa_by_re_affine M A0e A1e A2e x s ξ]
  exact pa_integral_affine_shocks hlaw _ _

/-- Miao, p. 727: `Var_t(r_{e,t+1}) = (φ_d² + β_{e,e}²)σ_t² + β_{e,w}²σ_w²`. -/
theorem pa_by_var_re {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (A0e A1e A2e x s : ℝ) :
    cov[fun ω => pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)
        - pa_by_re M A0e A1e A2e x s 0 0 0,
      fun ω => pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)
        - pa_by_re M A0e A1e A2e x s 0 0 0; P]
      = (M.φd ^ 2 + pa_by_bee M A1e ^ 2) * s ^ 2 + pa_by_bew M A2e ^ 2 * M.σw ^ 2 := by
  simp only [pa_by_re_affine M A0e A1e A2e x s ξ, add_sub_cancel_left]
  rw [pa_cov_shocks hind hlaw]
  simp [Fin.sum_univ_four]
  ring

/-- Miao, (20.54), p. 726: from `E_t[M(R_e − R_f)] = 0` under lognormality,
`E_t(r_e − r_f) + ½Var_t(r_e) = −Cov_t(m − E_t m, r_e − E_t r_e)`. -/
theorem eq_20_54 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 A0e A1e A2e x s rf : ℝ}
    (he : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    pa_by_re M A0e A1e A2e x s 0 0 0 - rf
      + 1 / 2 * ((M.φd ^ 2 + pa_by_bee M A1e ^ 2) * s ^ 2 + pa_by_bew M A2e ^ 2 * M.σw ^ 2)
      = -cov[fun ω => pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
            - pa_by_m M A0 A1 A2 x s 0 0 0,
          fun ω => pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)
            - pa_by_re M A0e A1e A2e x s 0 0 0; P] := by
  have : IsProbabilityMeasure P := inferInstance
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ,
    pa_by_re_affine M A0e A1e A2e x s ξ, add_sub_cancel_left] at he hf ⊢
  rw [pa_cov_shocks hind hlaw, pa_lognormal_premium hind hlaw he hf]
  simp [Fin.sum_univ_four]
  ring

/-- Miao, (20.56), p. 727: the conditional equity premium,
`E_t(r_e − r_f) = β_{e,e}λ_{m,e}σ_t² + β_{e,w}λ_{m,w}σ_w² − ½Var_t(r_e)` (the text's
`λ_{e,e}, λ_{e,w}` are `λ_{m,e}, λ_{m,w}`). -/
theorem eq_20_56 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 A0e A1e A2e x s rf : ℝ}
    (he : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)) ∂P = 1)
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    pa_by_re M A0e A1e A2e x s 0 0 0 - rf
      = pa_by_bee M A1e * pa_by_lam_e M A1 * s ^ 2 + pa_by_bew M A2e * pa_by_lam_w M A2 * M.σw ^ 2
        - 1 / 2 * ((M.φd ^ 2 + pa_by_bee M A1e ^ 2) * s ^ 2
          + pa_by_bew M A2e ^ 2 * M.σw ^ 2) := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ,
    pa_by_re_affine M A0e A1e A2e x s ξ] at he hf
  rw [pa_lognormal_premium hind hlaw he hf]
  simp [Fin.sum_univ_four]
  ring

/-- `H_e = λ_{m,η}² + (−λ_{m,e} + β_{e,e})² + φ_d²` (Miao, p. 728). -/
noncomputable def pa_by_He (M : PABansalYaron) (A1 A1e : ℝ) : ℝ :=
  pa_by_lam_eta M ^ 2 + (-pa_by_lam_e M A1 + pa_by_bee M A1e) ^ 2 + M.φd ^ 2

/-- Miao, (20.57), p. 728: substituting (20.46) and (20.55) into the Euler equation for equity
and matching the coefficients of `x_t` and `σ_t²`:
`−ρ + κ₁ₑA₁ₑρ_x − A₁ₑ + φ = 0` and
`(ρ − γ)/(1 − ρ) A₂(κ₁ν₁ − 1) + A₂ₑ(κ₁ₑν₁ − 1) + H_e/2 = 0`. -/
theorem pa_by_matching_equity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 A0e A1e A2e : ℝ}
    (hA1 : A1 * (1 - M.κ1 * M.ρx) = 1 - M.ρ)
    (h57 : ∀ x s : ℝ, 0 < s → ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω)
      + pa_by_re M A0e A1e A2e x s (ξ 1 ω) (ξ 2 ω) (ξ 3 ω)) ∂P = 1) :
    -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ = 0 ∧
    (M.ρ - M.γ) / (1 - M.ρ) * A2 * (M.κ1 * M.ν1 - 1) + A2e * (M.κ1e * M.ν1 - 1)
      + pa_by_He M A1 A1e / 2 = 0 := by
  have hpt : ∀ x s : ℝ, 0 < s →
      (pa_by_m M A0 A1 A2 x s 0 0 0 + pa_by_re M A0e A1e A2e x s 0 0 0)
        + (∑ k, ![pa_by_lam_eta M * s, -(pa_by_lam_e M A1 * s) + pa_by_bee M A1e * s,
          -(pa_by_lam_w M A2 * M.σw) + pa_by_bew M A2e * M.σw, M.φd * s] k ^ 2) / 2 = 0 := by
    intro x s hs
    rw [← pa_euler_shocks_iff hind hlaw]
    refine Eq.trans ?_ (h57 x s hs)
    congr 1
    funext ω
    congr 1
    rw [pa_by_m_affine M hρ A0 A1 A2 x s ξ ω, pa_by_re_affine M A0e A1e A2e x s ξ ω,
      pa_sum_four, pa_sum_four, pa_sum_four]
    ring
  set m0 := pa_by_m M A0 A1 A2 0 0 0 0 0
  have hK := pa_match_coeffs (K0 := m0 + (M.κ0e + M.κ1e * (A0e + A2e * M.σbar2 * (1 - M.ν1))
      - A0e + M.μd) + ((-(pa_by_lam_w M A2) + pa_by_bew M A2e) * M.σw) ^ 2 / 2)
    (K1 := -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ)
    (K2 := (M.ρ - M.γ) / (1 - M.ρ) * A2 * (M.κ1 * M.ν1 - 1) + A2e * (M.κ1e * M.ν1 - 1)
      + pa_by_He M A1 A1e / 2)
    (fun x s hs => by
      have := hpt x s hs
      rw [pa_by_Em M hρ hA1 x s] at this
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
        pa_by_re, pa_by_x', pa_by_v', pa_by_gd] at this
      simp only [pa_by_He]
      linear_combination this)
  exact ⟨hK.2.1, hK.2.2⟩

/-- Miao, p. 728: `A₁ₑ = (φ − ρ)/(1 − κ₁ₑρ_x)`. -/
theorem pa_by_A1e (M : PABansalYaron) (hk : M.κ1e * M.ρx ≠ 1) {A1e : ℝ}
    (h : -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ = 0) :
    A1e = (M.φ - M.ρ) / (1 - M.κ1e * M.ρx) := by
  have h3 : (1 : ℝ) - M.κ1e * M.ρx ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  rw [eq_div_iff h3]
  linarith

/-- Miao, p. 728: the price–dividend ratio is procyclical, `A₁ₑ > 0`, when `φ > ρ` (with
`κ₁ₑρ_x < 1`); e.g. when the EIS exceeds one and `φ ≥ 1`. -/
theorem pa_by_A1e_pos (M : PABansalYaron) (hφ : M.ρ < M.φ) (hk : M.κ1e * M.ρx < 1) :
    0 < (M.φ - M.ρ) / (1 - M.κ1e * M.ρx) :=
  div_pos (by linarith) (by linarith)

/-- Miao, p. 728: `A₂ₑ = ((γ − ρ)/(1 − ρ) A₂(1 − κ₁ν₁) + ½H_e)/(1 − κ₁ₑν₁)`. -/
theorem pa_by_A2e (M : PABansalYaron) (hk : M.κ1e * M.ν1 ≠ 1) {A1 A2 A1e A2e : ℝ}
    (h : (M.ρ - M.γ) / (1 - M.ρ) * A2 * (M.κ1 * M.ν1 - 1) + A2e * (M.κ1e * M.ν1 - 1)
      + pa_by_He M A1 A1e / 2 = 0) :
    A2e = ((M.γ - M.ρ) / (1 - M.ρ) * A2 * (1 - M.κ1 * M.ν1) + 1 / 2 * pa_by_He M A1 A1e)
      / (1 - M.κ1e * M.ν1) := by
  have h3 : (1 : ℝ) - M.κ1e * M.ν1 ≠ 0 := sub_ne_zero.2 (Ne.symm hk)
  rw [eq_div_iff h3]
  have e : (M.ρ - M.γ) / (1 - M.ρ) = -((M.γ - M.ρ) / (1 - M.ρ)) := by ring
  rw [e] at h
  linarith

/-! ### Unconditional moments -/

/-- Miao, p. 728: with `A₁ₑ` from (20.57), the equity return is
`r_{e,t+1} = c + ρ x_t + A₂ₑ(ν₁κ₁ₑ − 1)σ_t² + β_{e,e}σ_t e + φ_dσ_t u + β_{e,w}σ_w w`;
the coefficient of `x_t` is `+ρ` (the text prints `−ρ`). -/
theorem pa_by_re_decomp (M : PABansalYaron) {A0e A1e A2e : ℝ}
    (hA1e : -M.ρ + M.κ1e * A1e * M.ρx - A1e + M.φ = 0) (x s e w u : ℝ) :
    pa_by_re M A0e A1e A2e x s e w u = pa_by_re M A0e A1e A2e 0 0 0 0 0 + M.ρ * x
      + A2e * (M.ν1 * M.κ1e - 1) * s ^ 2 + pa_by_bee M A1e * s * e + M.φd * s * u
      + pa_by_bew M A2e * M.σw * w := by
  simp only [pa_by_re, pa_by_x', pa_by_v', pa_by_gd, pa_by_bee, pa_by_bew]
  linear_combination x * hA1e

/-- The variance of a linear combination of pairwise uncorrelated variables,
`Var(∑ a_k Z_k) = ∑ a_k² Var Z_k`. -/
theorem pa_cov_lin_uncorrelated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {Z : Fin n → Ω → ℝ} (hZ : ∀ k, MemLp (Z k) 2 P)
    (hunc : ∀ k l, k ≠ l → cov[Z k, Z l; P] = 0) (a : Fin n → ℝ) :
    cov[fun ω => ∑ k, a k * Z k ω, fun ω => ∑ k, a k * Z k ω; P]
      = ∑ k, a k ^ 2 * cov[Z k, Z k; P] := by
  rw [pa_cov_sum_uncorrelated (Y := fun k ω => a k * Z k ω) (fun k => (hZ k).const_mul _)
    (fun k l hkl => by
      rw [covariance_const_mul_left, covariance_const_mul_right, hunc k l hkl, mul_zero,
        mul_zero])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- Miao, p. 728: the unconditional variances of the equity return and of the price–dividend
ratio. With `Z = (x_t, σ_t e, σ_t u, σ_t² − Eσ_t², w)` pairwise uncorrelated,
`Var(σ_t e) = Var(σ_t u) = σ̄²`, `Var w = 1`:
`Var(r_e) = ρ²Var(x) + (β_{e,e}² + φ_d²)σ̄² + (A₂ₑ(ν₁κ₁ₑ − 1))²Var(σ²) + β_{e,w}²σ_w²`, and,
with `x_t, σ_t²` uncorrelated, `Var(z_e) = A₁ₑ²Var(x) + A₂ₑ²Var(σ²)`. -/
theorem pa_by_uncond_var {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : PABansalYaron) (A1e A2e : ℝ) {Z : Fin 5 → Ω → ℝ}
    (hZ : ∀ k, MemLp (Z k) 2 P) (hunc : ∀ k l, k ≠ l → cov[Z k, Z l; P] = 0)
    (h1 : cov[Z 1, Z 1; P] = M.σbar2) (h2 : cov[Z 2, Z 2; P] = M.σbar2)
    (h4 : cov[Z 4, Z 4; P] = 1) :
    cov[fun ω => M.ρ * Z 0 ω + pa_by_bee M A1e * Z 1 ω + M.φd * Z 2 ω
        + A2e * (M.ν1 * M.κ1e - 1) * Z 3 ω + pa_by_bew M A2e * M.σw * Z 4 ω,
      fun ω => M.ρ * Z 0 ω + pa_by_bee M A1e * Z 1 ω + M.φd * Z 2 ω
        + A2e * (M.ν1 * M.κ1e - 1) * Z 3 ω + pa_by_bew M A2e * M.σw * Z 4 ω; P]
      = M.ρ ^ 2 * cov[Z 0, Z 0; P] + (pa_by_bee M A1e ^ 2 + M.φd ^ 2) * M.σbar2
        + (A2e * (M.ν1 * M.κ1e - 1)) ^ 2 * cov[Z 3, Z 3; P]
        + pa_by_bew M A2e ^ 2 * M.σw ^ 2 ∧
    cov[fun ω => A1e * Z 0 ω + A2e * Z 3 ω, fun ω => A1e * Z 0 ω + A2e * Z 3 ω; P]
      = A1e ^ 2 * cov[Z 0, Z 0; P] + A2e ^ 2 * cov[Z 3, Z 3; P] := by
  constructor
  · have h := pa_cov_lin_uncorrelated hZ hunc
      ![M.ρ, pa_by_bee M A1e, M.φd, A2e * (M.ν1 * M.κ1e - 1), pa_by_bew M A2e * M.σw]
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons] at h
    rw [h, h1, h2, h4]
    ring
  · have h := pa_cov_lin_uncorrelated hZ hunc ![A1e, 0, 0, A2e, 0]
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at h
    exact h

/-! ### The riskfree rate -/

/-- Miao, p. 729: from `E_t[M R_f] = 1`,
`r_f = −(1 − γ)/(1 − ρ) ln β + (1 − γ)ρ/(1 − ρ) E_t g + (γ − ρ)/(1 − ρ) E_t r_w − ½Var_t(m)`
(the text prints `(ρ − γ)/(1 − ρ) E_t r_w`). -/
theorem pa_by_riskfree {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ξ : Fin 4 → Ω → ℝ} (hind : iIndepFun ξ P) (hlaw : ∀ k, HasLaw (ξ k) (gaussianReal 0 1) P)
    (M : PABansalYaron) (hρ : M.ρ ≠ 1) {A0 A1 A2 x s rf : ℝ}
    (hf : ∫ ω, Real.exp (pa_by_m M A0 A1 A2 x s (ξ 0 ω) (ξ 1 ω) (ξ 2 ω) + rf) ∂P = 1) :
    rf = -((1 - M.γ) / (1 - M.ρ)) * Real.log M.β + (1 - M.γ) * M.ρ / (1 - M.ρ) * (M.μ + x)
      + (M.γ - M.ρ) / (1 - M.ρ) * pa_by_rw M A0 A1 A2 x s 0 0 0
      - 1 / 2 * ((pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2) * s ^ 2
        + pa_by_lam_w M A2 ^ 2 * M.σw ^ 2) := by
  simp only [pa_by_m_affine M hρ A0 A1 A2 x s ξ] at hf
  have hf' : ∫ ω, Real.exp ((pa_by_m M A0 A1 A2 x s 0 0 0 + rf) + ∑ k,
      ![pa_by_lam_eta M * s, -(pa_by_lam_e M A1 * s), -(pa_by_lam_w M A2 * M.σw), 0] k
        * ξ k ω) ∂P = 1 := by
    refine Eq.trans ?_ hf
    congr 1
    funext ω
    congr 1
    ring
  rw [pa_euler_shocks_iff hind hlaw] at hf'
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at hf'
  rw [pa_by_gamma_rho M hρ]
  simp only [pa_by_m, pa_by_g, pa_by_θ] at hf' ⊢
  linear_combination hf'

/-- Miao, p. 729: subtracting `(1 − θ) r_f` from both sides,
`r_f = −ln β + ρE_t g + (γ − ρ)/(1 − γ) E_t[r_w − r_f] − (1 − ρ)/(2(1 − γ)) Var_t(m)`. -/
theorem pa_by_riskfree_final {β ρ γ rf Eg Erw Vm : ℝ} (hρ : ρ ≠ 1) (hγ : γ ≠ 1)
    (h : rf = -((1 - γ) / (1 - ρ)) * Real.log β + (1 - γ) * ρ / (1 - ρ) * Eg
      + (γ - ρ) / (1 - ρ) * Erw - 1 / 2 * Vm) :
    rf = -Real.log β + ρ * Eg + (γ - ρ) / (1 - γ) * (Erw - rf)
      - (1 - ρ) / (2 * (1 - γ)) * Vm := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ)
  have h2 : (1 : ℝ) - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  field_simp at h ⊢
  linear_combination h

/-- Miao, p. 729: `λ_{m,e} B = (γ − ρ)/(1 − ρ) B²`. -/
theorem pa_by_lam_e_B (M : PABansalYaron) (A1 : ℝ) :
    pa_by_lam_e M A1 * pa_by_B M A1 = (M.γ - M.ρ) / (1 - M.ρ) * pa_by_B M A1 ^ 2 := by
  simp only [pa_by_lam_e, pa_by_B]
  ring

/-- Miao, p. 729: the riskfree rate as a function of the state,
`r_f = R₀ + ρ x_t + ((γ − ρ)/(1 − γ) Q₁ − (1 − ρ)/(2(1 − γ)) Q₂) σ_t²` with
`Q₁ = −λ_{m,η} + (γ − ρ)/(1 − ρ) B² − ½(1 + B²)` (the time-varying part of the wealth premium
(20.53); the text prints `(ρ − γ)/(1 − ρ) B²`) and `Q₂ = λ_{m,η}² + λ_{m,e}²`. -/
theorem pa_by_riskfree_state (M : PABansalYaron) {A1 A2 rf x s Erw : ℝ}
    (hfin : rf = -Real.log M.β + M.ρ * (M.μ + x) + (M.γ - M.ρ) / (1 - M.γ) * (Erw - rf)
      - (1 - M.ρ) / (2 * (1 - M.γ)) * ((pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2) * s ^ 2
        + pa_by_lam_w M A2 ^ 2 * M.σw ^ 2))
    (h53 : Erw - rf = -pa_by_lam_eta M * s ^ 2 + pa_by_lam_e M A1 * pa_by_B M A1 * s ^ 2
        + M.κ1 * A2 * pa_by_lam_w M A2 * M.σw ^ 2
        - 1 / 2 * ((1 + pa_by_B M A1 ^ 2) * s ^ 2 + (A2 * M.κ1) ^ 2 * M.σw ^ 2)) :
    rf = (-Real.log M.β + M.ρ * M.μ
        + (M.γ - M.ρ) / (1 - M.γ) * (M.κ1 * A2 * pa_by_lam_w M A2 * M.σw ^ 2
          - 1 / 2 * (A2 * M.κ1) ^ 2 * M.σw ^ 2)
        - (1 - M.ρ) / (2 * (1 - M.γ)) * (pa_by_lam_w M A2 ^ 2 * M.σw ^ 2))
      + M.ρ * x
      + ((M.γ - M.ρ) / (1 - M.γ) * (-pa_by_lam_eta M + (M.γ - M.ρ) / (1 - M.ρ) * pa_by_B M A1 ^ 2
          - 1 / 2 * (1 + pa_by_B M A1 ^ 2))
        - (1 - M.ρ) / (2 * (1 - M.γ)) * (pa_by_lam_eta M ^ 2 + pa_by_lam_e M A1 ^ 2)) * s ^ 2 := by
  rw [pa_by_lam_e_B] at h53
  rw [hfin, h53]
  ring

/-- Miao, p. 729: the volatility of the riskfree rate. If `r_f = R₀ + ρ x_t + c σ_t²` with
`x_t` and `σ_t²` uncorrelated, `Var(r_f) = ρ²Var(x) + c²Var(σ²)`. -/
theorem pa_by_var_riskfree {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X V : Ω → ℝ} (hX : MemLp X 2 P) (hV : MemLp V 2 P)
    (hXV : cov[X, V; P] = 0) (ρ c : ℝ) :
    cov[fun ω => ρ * X ω + c * V ω, fun ω => ρ * X ω + c * V ω; P]
      = ρ ^ 2 * cov[X, X; P] + c ^ 2 * cov[V, V; P] := by
  have h := pa_cov_lin_uncorrelated (Z := ![X, V]) (fun k => by fin_cases k <;> assumption)
    (fun k l hkl => by
      fin_cases k <;> fin_cases l
      · exact absurd rfl hkl
      · exact hXV
      · rw [covariance_comm]; exact hXV
      · exact absurd rfl hkl) ![ρ, c]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

end Miao.RecursiveUtility
