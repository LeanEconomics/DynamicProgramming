/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.HasLaw

/-!
# The lognormal CCAPM: the riskfree rate and the equity premium

Miao, §13.8, pp. 449–451, equations (13.33)–(13.36). The SDF is `M = e^m` and a return is
`R_j = e^{r_j}`; joint lognormality enters through the Gaussian laws of `m`, `r_j` and `m + r_j`
on a probability space `(Ω, P)` (the conditional distribution at a node, which is the same at
every node under homoskedasticity).

* `bp_integral_exp_gaussian`: `E[e^X] = e^{μ + v/2}` for `X ~ N(μ, v)`.
* `eq_13_33`: `E[M R_f] = 1` gives `r_f = −E[m] − σ_m²/2`.
* `eq_13_34`: `E[M R_j] = 1` gives `E[r_j − r_f] + σ_j²/2 = −σ_{jm}` with
  `σ_{jm} = Cov(r_j, m)`; the covariance is recovered from `Var(m + r_j)`.
* CRRA utility and lognormal consumption growth `Δc = g + σ_c ε`, `ε ~ N(0, 1)`:
  `m = ln β − γΔc` (`bp_ccapm_log_sdf`), `eq_13_35` (`r_f = −ln β + γg − γ²σ_c²/2`) and the
  comparative statics stated after it (`eq_13_35_beta`, `eq_13_35_growth`, `eq_13_35_risk`);
  `eq_13_36` (corrected): `E[r_j − r_f] + σ_j²/2 = γσ_c Cov(r_j, ε) = γ Cov(r_j, Δc)`.

**Correction.** (13.36) as printed, `E[r_j − r_f] + σ_j²/2 = γσ_{jc}` with
`σ_{jc} = Cov(r_j − E r_j, ε)`, omits the factor `σ_c`: since `m − Em = −γσ_c ε`,
`−σ_{jm} = γσ_c Cov(r_j, ε)` (`eq_13_36`). The printed formula is right if `σ_{jc}` is the
covariance with consumption growth `Δc = g + σ_c ε`. Counterexample to the printed form:
`eq_13_36_counterexample` (`γ = 1`, `σ_c = 1/2`, `Cov(r_j, ε) = 1`: the premium is `1/2`, not `1`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Miao.CompleteMarkets

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem bp_integrable_id_gaussian (μ : ℝ) (v : ℝ≥0) :
    Integrable (id : ℝ → ℝ) (gaussianReal μ v) :=
  (memLp_id_gaussianReal 2).integrable one_le_two

/-- `E[e^X] = e^{μ + v/2}` for a Gaussian `X ~ N(μ, v)`. -/
theorem bp_integral_exp_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ v) P) : ∫ ω, Real.exp (X ω) ∂P = Real.exp (μ + v / 2) := by
  have := mgf_gaussianReal hX 1
  simpa [mgf] using this

theorem bp_mean_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) :
    ∫ ω, X ω ∂P = μ :=
  hX.integral_eq.trans integral_id_gaussianReal

theorem bp_var_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) :
    Var[X; P] = v :=
  hX.variance_eq.trans variance_id_gaussianReal

theorem bp_memLp_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P) :
    MemLp X 2 P :=
  hX.memLp (memLp_id_gaussianReal 2)

/-- An Euler equation `E[e^X e^a] = 1` with `X ~ N(μ, v)` pins down `a = −μ − v/2`. -/
theorem bp_euler_gaussian {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal μ v) P)
    (a : ℝ) (h : ∫ ω, Real.exp (X ω) * Real.exp a ∂P = 1) : μ + v / 2 + a = 0 := by
  rw [integral_mul_const, bp_integral_exp_gaussian hX, ← Real.exp_add] at h
  exact Real.exp_eq_one_iff _ |>.1 h

/-- Miao, (13.33), p. 449: with `M = e^m`, `m` Gaussian, and `E[M e^{r_f}] = 1`,
`r_f = −E[m] − σ_m²/2`. -/
theorem eq_13_33 {m : Ω → ℝ} {μm : ℝ} {vm : ℝ≥0} (hm : HasLaw m (gaussianReal μm vm) P)
    (rf : ℝ) (heul : ∫ ω, Real.exp (m ω) * Real.exp rf ∂P = 1) :
    rf = -(∫ ω, m ω ∂P) - Var[m; P] / 2 := by
  have := bp_euler_gaussian hm rf heul
  rw [bp_mean_gaussian hm, bp_var_gaussian hm]
  linarith

/-- Miao, (13.34), p. 450: if `m`, `r_j` and `m + r_j` are Gaussian (joint normality), the Euler
equations `E[M R_f] = 1` and `E[M R_j] = 1` give `E[r_j − r_f] + σ_j²/2 = −σ_{jm}` with
`σ_{jm} = Cov(r_j, m)`. -/
theorem eq_13_34 [IsProbabilityMeasure P] {m r : Ω → ℝ} {μm μj : ℝ} {vm vj vmr : ℝ≥0}
    (hm : HasLaw m (gaussianReal μm vm) P) (hr : HasLaw r (gaussianReal μj vj) P)
    (hmr : HasLaw (fun ω => m ω + r ω) (gaussianReal (μm + μj) vmr) P) (rf : ℝ)
    (hf : ∫ ω, Real.exp (m ω) * Real.exp rf ∂P = 1)
    (hj : ∫ ω, Real.exp (m ω) * Real.exp (r ω) ∂P = 1) :
    (∫ ω, r ω ∂P) - rf + Var[r; P] / 2 = -cov[r, m; P] := by
  have h1 := bp_euler_gaussian hm rf hf
  have h2 : μm + μj + vmr / 2 = 0 := by
    have := bp_euler_gaussian hmr 0 (by simpa [← Real.exp_add] using hj)
    linarith
  have hvar := variance_add (bp_memLp_gaussian hm) (bp_memLp_gaussian hr)
  have hvmr : Var[m + r; P] = vmr := bp_var_gaussian hmr
  rw [hvmr, bp_var_gaussian hm, bp_var_gaussian hr] at hvar
  rw [bp_mean_gaussian hr, bp_var_gaussian hr, covariance_comm]
  linarith

/-- Miao, p. 450: with `u(c) = c^{1−γ}/(1−γ)` the SDF `M = β(C_{t+1}/C_t)^{−γ}` has
`m = ln M = ln β − γΔc`, `Δc = ln(C_{t+1}/C_t)`. -/
theorem bp_ccapm_log_sdf (β γ C C' : ℝ) (hβ : 0 < β) (hC : 0 < C) (hC' : 0 < C') :
    Real.log (β * (C' / C) ^ (-γ)) = Real.log β - γ * Real.log (C' / C) := by
  have hr : 0 < C' / C := div_pos hC' hC
  rw [Real.log_mul hβ.ne' (Real.rpow_pos_of_pos hr _).ne', Real.log_rpow hr]
  ring

/-- With `ε ~ N(0, 1)`, `m = ln β − γ(g + σ_c ε) ~ N(ln β − γg, γ²σ_c²)`. -/
theorem bp_ccapm_m_law {ε : Ω → ℝ} (hε : HasLaw ε (gaussianReal 0 1) P) (β γ g σc : ℝ) :
    HasLaw (fun ω => Real.log β - γ * (g + σc * ε ω))
      (gaussianReal (Real.log β - γ * g) (.mk ((γ * σc) ^ 2) (sq_nonneg _))) P := by
  have h := gaussianReal_const_add (gaussianReal_const_mul hε (-(γ * σc)))
    (Real.log β - γ * g)
  have hf : (fun ω => Real.log β - γ * (g + σc * ε ω)) =
      fun ω => Real.log β - γ * g + -(γ * σc) * ε ω := by
    funext ω
    ring
  rw [hf]
  convert h using 2
  · ring
  · ext
    simp

/-- Miao, (13.35), p. 450: with CRRA utility and `Δc = g + σ_c ε`, `ε ~ N(0, 1)`, the riskfree
rate is `r_f = −ln β + γg − γ²σ_c²/2`. -/
theorem eq_13_35 {ε : Ω → ℝ} (hε : HasLaw ε (gaussianReal 0 1) P) (β γ g σc rf : ℝ)
    (heul : ∫ ω, Real.exp (Real.log β - γ * (g + σc * ε ω)) * Real.exp rf ∂P = 1) :
    rf = -Real.log β + γ * g - γ ^ 2 * σc ^ 2 / 2 := by
  have := bp_euler_gaussian (bp_ccapm_m_law hε β γ g σc) rf heul
  simp only [NNReal.coe_mk] at this
  linarith

/-- The riskfree rate of (13.35) as a function of the parameters. -/
noncomputable def bp_rf (β γ g σc : ℝ) : ℝ := -Real.log β + γ * g - γ ^ 2 * σc ^ 2 / 2

/-- Miao, p. 450: the riskfree rate decreases with the subjective discount factor `β`. -/
theorem eq_13_35_beta (β₁ β₂ γ g σc : ℝ) (h₁ : 0 < β₁) (h : β₁ < β₂) :
    bp_rf β₂ γ g σc < bp_rf β₁ γ g σc := by
  unfold bp_rf
  have := Real.log_lt_log h₁ h
  linarith

/-- Miao, p. 450: the riskfree rate increases with expected consumption growth (`γ > 0`). -/
theorem eq_13_35_growth (β γ g₁ g₂ σc : ℝ) (hγ : 0 < γ) (h : g₁ < g₂) :
    bp_rf β γ g₁ σc < bp_rf β γ g₂ σc := by
  unfold bp_rf
  nlinarith

/-- Miao, p. 451: the riskfree rate decreases with the variance of consumption growth
(precautionary saving, `γ ≠ 0`). -/
theorem eq_13_35_risk (β γ g σ₁ σ₂ : ℝ) (hγ : γ ≠ 0) (h : σ₁ ^ 2 < σ₂ ^ 2) :
    bp_rf β γ g σ₂ < bp_rf β γ g σ₁ := by
  unfold bp_rf
  have : 0 < γ ^ 2 := pow_pos (abs_pos.2 hγ) 2 |>.trans_eq (sq_abs γ)
  nlinarith

/-- Miao, (13.36), p. 450 (corrected): with CRRA utility, `Δc = g + σ_c ε`, `ε ~ N(0, 1)` and
`r_j`, `m + r_j` Gaussian, the equity premium satisfies
`E[r_j − r_f] + σ_j²/2 = γσ_c Cov(r_j, ε)`. -/
theorem eq_13_36 [IsProbabilityMeasure P] {ε r : Ω → ℝ} (hε : HasLaw ε (gaussianReal 0 1) P)
    (β γ g σc : ℝ) {μj : ℝ} {vj vmr : ℝ≥0} (hr : HasLaw r (gaussianReal μj vj) P)
    (hmr : HasLaw (fun ω => Real.log β - γ * (g + σc * ε ω) + r ω)
      (gaussianReal (Real.log β - γ * g + μj) vmr) P) (rf : ℝ)
    (hf : ∫ ω, Real.exp (Real.log β - γ * (g + σc * ε ω)) * Real.exp rf ∂P = 1)
    (hj : ∫ ω, Real.exp (Real.log β - γ * (g + σc * ε ω)) * Real.exp (r ω) ∂P = 1) :
    (∫ ω, r ω ∂P) - rf + Var[r; P] / 2 = γ * σc * cov[r, ε; P] := by
  have hm := bp_ccapm_m_law hε β γ g σc
  rw [eq_13_34 hm hr hmr rf hf hj]
  have hf' : (fun ω => Real.log β - γ * (g + σc * ε ω)) =
      fun ω => Real.log β - γ * g + -(γ * σc) * ε ω := by
    funext ω
    ring
  have hint : Integrable (fun ω => -(γ * σc) * ε ω) P :=
    (hε.integrable (bp_integrable_id_gaussian 0 1)).const_mul _
  rw [hf', covariance_const_add_right hint, covariance_const_mul_right]
  ring

/-- Counterexample to (13.36) as printed (Miao, p. 450). On `Ω = ℝ` with the standard normal
law, `ε = id`, `β = 1/2`, `γ = 1`, `g = 0`, `σ_c = 1/2`, `r_f = ln 2 − 1/8` and
`r_j = ln 2 − 1/8 + ε`: both Euler equations hold, `Cov(r_j, ε) = 1`, and the premium
`E[r_j − r_f] + σ_j²/2` is `γσ_c Cov(r_j, ε) = 1/2`, not `γ Cov(r_j, ε) = 1`. -/
theorem eq_13_36_counterexample :
    let P := gaussianReal 0 1
    let r : ℝ → ℝ := fun x => Real.log 2 - 1 / 8 + x
    let rf : ℝ := Real.log 2 - 1 / 8
    (∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp rf ∂P = 1) ∧
      (∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp (r x) ∂P = 1) ∧
      cov[r, id; P] = 1 ∧
      (∫ x, r x ∂P) - rf + Var[r; P] / 2 ≠ 1 * cov[r, id; P] := by
  intro P r rf
  have hε : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) P := HasLaw.id
  have hm := bp_ccapm_m_law hε (1 / 2) 1 0 (1 / 2)
  have hr : HasLaw r (gaussianReal (Real.log 2 - 1 / 8) 1) P := by
    have h := gaussianReal_const_add hε (Real.log 2 - 1 / 8)
    simpa [r] using h
  have hmr : HasLaw (fun x => Real.log (1 / 2) - 1 * (0 + 1 / 2 * x) + r x)
      (gaussianReal (Real.log (1 / 2) - 1 * 0 + (Real.log 2 - 1 / 8))
        (.mk ((1 / 2) ^ 2) (sq_nonneg _))) P := by
    have h := gaussianReal_const_add (gaussianReal_const_mul hε (1 / 2))
      (Real.log (1 / 2) - 1 * 0 + (Real.log 2 - 1 / 8))
    have hfun : (fun x => Real.log (1 / 2) - 1 * (0 + 1 / 2 * x) + r x) =
        fun x => Real.log (1 / 2) - 1 * 0 + (Real.log 2 - 1 / 8) + 1 / 2 * x := by
      funext x
      simp only [r]
      ring
    rw [hfun]
    convert h using 2
    · ring
    · simp
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hf : ∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp rf ∂P = 1 := by
    rw [integral_mul_const, bp_integral_exp_gaussian hm, ← Real.exp_add, Real.exp_eq_one_iff]
    simp only [NNReal.coe_mk, rf, hlog]
    ring
  have hj : ∫ x, Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp (r x) ∂P = 1 := by
    have e : (fun x => Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x)) * Real.exp (r x)) =
        fun x => Real.exp (Real.log (1 / 2) - 1 * (0 + 1 / 2 * x) + r x) := by
      funext x
      rw [← Real.exp_add]
    rw [e, bp_integral_exp_gaussian hmr, Real.exp_eq_one_iff]
    simp only [NNReal.coe_mk, hlog]
    ring
  have hcov : cov[r, id; P] = 1 := by
    have hint : Integrable (id : ℝ → ℝ) P := bp_integrable_id_gaussian 0 1
    have : r = fun x => (Real.log 2 - 1 / 8) + id x := rfl
    rw [this, covariance_const_add_left hint, covariance_self aemeasurable_id,
      variance_id_gaussianReal, NNReal.coe_one]
  have hmain := eq_13_36 hε (1 / 2) 1 0 (1 / 2) hr hmr rf hf hj
  refine ⟨hf, hj, hcov, ?_⟩
  have hcov' : cov[r, fun x => x; P] = 1 := hcov
  rw [hmain, hcov', hcov]
  norm_num

end Miao.CompleteMarkets
