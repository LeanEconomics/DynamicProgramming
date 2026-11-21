/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CompleteMarkets.BPLognormal
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Integration

/-!
# The static CCAPM with exponential utility (Exercise 13.10)

Miao, §13.9, Exercise 13.10 (p. 454): "Consider a static CCAPM with exponential utility and
normally distributed returns. Derive the CAPM."

The representative agent has `u(c) = −e^{−αc}/α` (`α > 0`), so `u'(C) = e^{−αC}` and the first-
order condition for an asset with return `R_j` is `E[e^{−αC}(R_j − R_f)] = 0`. Consumption
`C ~ N(μ, v)` is aggregate wealth `W_0 R_m` (the market return), and joint normality of
`(C, R_j)` is expressed by the regression decomposition `R_j = a_j + κ_j C + e_j` with `e_j`
independent of `C` and square integrable.

* `bp_gaussian_stein`: `E[C e^{tC}] = (μ + vt) E[e^{tC}]` (from the derivative of the moment
  generating function `t ↦ e^{μt + vt²/2}`).
* `ex_13_10_pricing`: `E[R_j] − R_f = α Cov(C, R_j)`.
* `ex_13_10_capm`: with `R_m = C/W_0`, `E[R_j] − R_f = β_j (E[R_m] − R_f)`,
  `β_j = Cov(R_j, R_m)/Var(R_m)`.

The first-order condition is taken as given (it is the static analogue of the Euler equation
derived in `bp_ccapm_euler`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Miao.CompleteMarkets

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

omit [MeasurableSpace Ω] in
theorem bp_integrableExpSet_gaussian [MeasurableSpace Ω] {P : Measure Ω} {C : Ω → ℝ} {μ : ℝ}
    {v : ℝ≥0} (hC : HasLaw C (gaussianReal μ v) P) : integrableExpSet C P = Set.univ := by
  ext s
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact hC.integrable_comp (f := fun x => Real.exp (s * x)) (integrable_exp_mul_gaussianReal s)

/-- A Stein-type identity for a Gaussian `C ~ N(μ, v)`: `E[C e^{tC}] = (μ + vt) E[e^{tC}]`. -/
theorem bp_gaussian_stein {C : Ω → ℝ} {μ : ℝ} {v : ℝ≥0} (hC : HasLaw C (gaussianReal μ v) P)
    (t : ℝ) :
    ∫ ω, C ω * Real.exp (t * C ω) ∂P = (μ + v * t) * ∫ ω, Real.exp (t * C ω) ∂P := by
  have hint : t ∈ interior (integrableExpSet C P) := by
    rw [bp_integrableExpSet_gaussian hC, interior_univ]
    trivial
  have h1 := hasDerivAt_mgf hint
  have hmgf : mgf C P = fun s => Real.exp (μ * s + v * s ^ 2 / 2) :=
    funext (mgf_gaussianReal hC)
  have h2 : HasDerivAt (fun s => Real.exp (μ * s + v * s ^ 2 / 2))
      (Real.exp (μ * t + v * t ^ 2 / 2) * (μ + v * t)) t := by
    have h3 : HasDerivAt (fun s => μ * s + v * s ^ 2 / 2) (μ + v * t) t := by
      have := ((hasDerivAt_id t).const_mul μ).add
        (((hasDerivAt_pow 2 t).const_mul (v : ℝ)).div_const 2)
      convert this using 1
      · funext s
        simp [mul_div_assoc]
      · simp only [mul_one, Nat.cast_ofNat]
        ring
    exact h3.exp
  rw [hmgf] at h1
  have heq := h1.unique h2
  have hm : ∫ ω, Real.exp (t * C ω) ∂P = Real.exp (μ * t + v * t ^ 2 / 2) :=
    mgf_gaussianReal hC t
  rw [hm, heq]
  ring

/-- **Exercise 13.10**, pricing (Miao, p. 454). With `u'(C) = e^{−αC}`, `C ~ N(μ, v)` and
`R_j = a + κC + e` (`e` independent of `C`, square integrable), the first-order condition
`E[e^{−αC}(R_j − R_f)] = 0` gives `E[R_j] − R_f = α Cov(C, R_j)`. -/
theorem ex_13_10_pricing [IsProbabilityMeasure P] {C e : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hC : HasLaw C (gaussianReal μ v) P) (he : MemLp e 2 P) (hind : IndepFun C e P)
    (α a κ Rf : ℝ)
    (hfoc : ∫ ω, Real.exp (-α * C ω) * (a + κ * C ω + e ω - Rf) ∂P = 0) :
    (∫ ω, (a + κ * C ω + e ω) ∂P) - Rf = α * cov[C, fun ω => a + κ * C ω + e ω; P] := by
  have hint : -α ∈ interior (integrableExpSet C P) := by
    rw [bp_integrableExpSet_gaussian hC, interior_univ]
    trivial
  have I1 : Integrable (fun ω => Real.exp (-α * C ω)) P := by
    have := bp_integrableExpSet_gaussian hC
    have hm : -α ∈ integrableExpSet C P := by rw [this]; trivial
    exact hm
  have I2 : Integrable (fun ω => C ω * Real.exp (-α * C ω)) P := by
    have := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hint 1
    simpa using this
  have hmeas : Measurable (fun x : ℝ => Real.exp (-α * x)) := by fun_prop
  have hind' : IndepFun (fun ω => Real.exp (-α * C ω)) e P :=
    hind.comp hmeas measurable_id
  have Ie : Integrable e P := he.integrable one_le_two
  have I3 : Integrable (fun ω => Real.exp (-α * C ω) * e ω) P := hind'.integrable_mul I1 Ie
  have hE3 : ∫ ω, Real.exp (-α * C ω) * e ω ∂P =
      (∫ ω, Real.exp (-α * C ω) ∂P) * ∫ ω, e ω ∂P :=
    hind'.integral_fun_mul_eq_mul_integral I1.aestronglyMeasurable Ie.aestronglyMeasurable
  have hstein := bp_gaussian_stein hC (-α)
  set E1 := ∫ ω, Real.exp (-α * C ω) ∂P with hE1
  have hE1pos : 0 < E1 := by
    rw [hE1, show (∫ ω, Real.exp (-α * C ω) ∂P) = mgf C P (-α) from rfl,
      mgf_gaussianReal hC]
    exact Real.exp_pos _
  have hsplit : (fun ω => Real.exp (-α * C ω) * (a + κ * C ω + e ω - Rf)) =
      fun ω => ((a - Rf) * Real.exp (-α * C ω) + κ * (C ω * Real.exp (-α * C ω))) +
        Real.exp (-α * C ω) * e ω := by
    funext ω
    ring
  have I12 : Integrable (fun ω => (a - Rf) * Real.exp (-α * C ω) +
      κ * (C ω * Real.exp (-α * C ω))) P := (I1.const_mul _).add (I2.const_mul _)
  rw [hsplit, integral_add I12 I3, integral_add (I1.const_mul _) (I2.const_mul _),
    integral_const_mul, integral_const_mul, hE3, hstein] at hfoc
  have hkey : (a - Rf) + κ * (μ + v * -α) + ∫ ω, e ω ∂P = 0 := by
    have : E1 * ((a - Rf) + κ * (μ + v * -α) + ∫ ω, e ω ∂P) = 0 := by
      rw [← hfoc]
      ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hE1pos.ne'
    · exact h
  have IC : Integrable C P := hC.integrable (bp_integrable_id_gaussian μ v)
  have hmean : ∫ ω, (a + κ * C ω + e ω) ∂P = a + κ * μ + ∫ ω, e ω ∂P := by
    have Iak : Integrable (fun ω => a + κ * C ω) P := (integrable_const a).add (IC.const_mul κ)
    rw [integral_add Iak Ie, integral_add (integrable_const a) (IC.const_mul κ),
      integral_const_mul,
      bp_mean_gaussian hC]
    simp
  have hCm : MemLp C 2 P := bp_memLp_gaussian hC
  have hcov : cov[C, fun ω => a + κ * C ω + e ω; P] = κ * v := by
    have hf : (fun ω => a + κ * C ω + e ω) = fun ω => a + ((fun ω => κ * C ω) + e) ω := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hf, covariance_const_add_right ((IC.const_mul κ).add Ie),
      covariance_add_right hCm (hCm.const_mul κ) he, covariance_const_mul_right,
      covariance_self hC.aemeasurable, bp_var_gaussian hC,
      hind.covariance_eq_zero hCm he]
    ring
  rw [hmean, hcov]
  linarith

/-- **Exercise 13.10**, the CAPM (Miao, p. 454). If consumption is `C = W_0 R_m` (`W_0 > 0`),
`C ~ N(μ, v)` with `v > 0`, and both the market return and asset `j` satisfy the first-order
condition, then `E[R_j] − R_f = β_j(E[R_m] − R_f)` with `β_j = Cov(R_j, R_m)/Var(R_m)`. -/
theorem ex_13_10_capm [IsProbabilityMeasure P] {C e : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hC : HasLaw C (gaussianReal μ v) P) (hv : 0 < (v : ℝ)) (he : MemLp e 2 P)
    (hind : IndepFun C e P) (α a κ Rf W0 : ℝ) (hW0 : 0 < W0)
    (hfoc : ∫ ω, Real.exp (-α * C ω) * (a + κ * C ω + e ω - Rf) ∂P = 0)
    (hfocm : ∫ ω, Real.exp (-α * C ω) * (C ω / W0 - Rf) ∂P = 0) :
    (∫ ω, (a + κ * C ω + e ω) ∂P) - Rf =
      cov[fun ω => a + κ * C ω + e ω, fun ω => C ω / W0; P] /
          cov[fun ω => C ω / W0, fun ω => C ω / W0; P] *
        ((∫ ω, C ω / W0 ∂P) - Rf) := by
  have hj := ex_13_10_pricing hC he hind α a κ Rf hfoc
  have he0 : MemLp (fun _ : Ω => (0 : ℝ)) 2 P := memLp_const 0
  have hind0 : IndepFun C (fun _ : Ω => (0 : ℝ)) P := indepFun_const_right C 0
  have hfocm' : ∫ ω, Real.exp (-α * C ω) * (0 + 1 / W0 * C ω + (fun _ => (0 : ℝ)) ω - Rf) ∂P
      = 0 := by
    have hfun : (fun ω => Real.exp (-α * C ω) * (0 + 1 / W0 * C ω + (fun _ => (0 : ℝ)) ω - Rf)) =
        fun ω => Real.exp (-α * C ω) * (C ω / W0 - Rf) := by
      funext ω
      ring
    rw [hfun]
    exact hfocm
  have hm := ex_13_10_pricing hC he0 hind0 α 0 (1 / W0) Rf hfocm'
  have hfm : (fun ω => 0 + 1 / W0 * C ω + (fun _ => (0 : ℝ)) ω) = fun ω => 1 / W0 * C ω := by
    funext ω
    ring
  have hfm2 : (fun ω => C ω / W0) = fun ω => 1 / W0 * C ω := by
    funext ω
    ring
  rw [hfm] at hm
  rw [hfm2, hm, hj, covariance_const_mul_right, covariance_const_mul_left,
    covariance_const_mul_right, covariance_self hC.aemeasurable, bp_var_gaussian hC,
    covariance_comm (fun ω => a + κ * C ω + e ω)]
  have := hW0.ne'
  have := hv.ne'
  field_simp

end Miao.CompleteMarkets
