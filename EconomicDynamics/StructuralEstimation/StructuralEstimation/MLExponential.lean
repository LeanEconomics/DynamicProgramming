/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Moments of the exponential distribution

Tools for Miao, Exercise 12.2, p. 408 (and Example 12.3.3, p. 405): the exponential
distribution `f(x) = θ e^{−θx}`, `x ≥ 0`, is Mathlib's `expMeasure θ`.

* `ml_integral_expMeasure`: `∫ g d(expMeasure θ) = ∫_{x > 0} θ e^{−θx} g(x) dx`.
* `ml_integrable_expMeasure_pow`: `x ↦ xⁿ` is integrable for `n = 1, 2`;
  `ml_memLp_two_expMeasure`: the identity is square integrable.
* `ml_mean_expMeasure`: the mean is `1/θ`; `ml_second_moment_expMeasure`: `E x² = 2/θ²`;
  `ml_variance_expMeasure`: the variance is `1/θ²`.
-/

namespace Miao.StructuralEstimation

open MeasureTheory ProbabilityTheory Real

/-- The density of `expMeasure θ` as a real indicator function. -/
theorem ml_gammaPDF_one_toReal {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    (gammaPDF 1 θ x).toReal = Set.indicator (Set.Ici 0) (fun x => θ * Real.exp (-(θ * x))) x := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hθ x)]
  by_cases hx : 0 ≤ x
  · rw [Set.indicator_of_mem (Set.mem_Ici.2 hx), gammaPDFReal]
    simp [hx]
  · rw [Set.indicator_of_notMem (by simpa using hx), gammaPDFReal]
    simp [hx]

/-- `∫ g d(expMeasure θ) = ∫_{x > 0} θ e^{−θx} g(x) dx`. -/
theorem ml_integral_expMeasure {θ : ℝ} (hθ : 0 < θ) (g : ℝ → ℝ) :
    ∫ x, g x ∂(expMeasure θ) = ∫ x in Set.Ioi 0, θ * Real.exp (-(θ * x)) * g x := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (gammaPDF 1 θ) from (measurable_gammaPDFReal 1 θ).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ml_gammaPDF_one_toReal hθ, smul_eq_mul]
  rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1
  funext x
  by_cases hx : x ∈ Set.Ici (0 : ℝ)
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-- `x ↦ xⁿ` is `expMeasure θ`-integrable for `n ≥ 1` (used for `n = 1, 2`). -/
theorem ml_integrable_expMeasure_pow {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (expMeasure θ) := by
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff_integrable_smul'
    (show Measurable (gammaPDF 1 θ) from (measurable_gammaPDFReal 1 θ).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ml_gammaPDF_one_toReal hθ, smul_eq_mul]
  have hfun : (fun x : ℝ => Set.indicator (Set.Ici 0) (fun x => θ * Real.exp (-(θ * x))) x *
      x ^ n) = Set.indicator (Set.Ici 0) (fun x => θ * Real.exp (-(θ * x)) * x ^ n) := by
    funext x
    by_cases hx : x ∈ Set.Ici (0 : ℝ)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  have hI := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := θ)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hθ
  refine IntegrableOn.congr_fun (Integrable.const_mul hI θ) (fun x _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]
  ring

/-- The identity is square integrable for `expMeasure θ`. -/
theorem ml_memLp_two_expMeasure {θ : ℝ} (hθ : 0 < θ) : MemLp id 2 (expMeasure θ) :=
  (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
    (by simpa using ml_integrable_expMeasure_pow hθ 2)

/-- `∫_{x > 0} θ e^{−θx} xⁿ dx = n!/θⁿ`. -/
theorem ml_integral_expMeasure_pow {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    ∫ x, x ^ n ∂(expMeasure θ) = n.factorial / θ ^ n := by
  rw [ml_integral_expMeasure hθ]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := θ) (by positivity) hθ
  have hcongr : ∫ x in Set.Ioi 0, θ * Real.exp (-(θ * x)) * x ^ n =
      θ * ∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) + 1 - 1) * Real.exp (-(θ * x)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    ring
  rw [hcongr, h, Real.Gamma_nat_eq_factorial, Real.rpow_add_one (by positivity),
    Real.rpow_natCast, one_div, inv_pow]
  field_simp

/-- The exponential distribution has mean `1/θ` (Miao, Exercise 12.2 and Example 12.3.3). -/
theorem ml_mean_expMeasure {θ : ℝ} (hθ : 0 < θ) : ∫ x, x ∂(expMeasure θ) = 1 / θ := by
  simpa using ml_integral_expMeasure_pow hθ 1

/-- The exponential distribution has second moment `2/θ²`. -/
theorem ml_second_moment_expMeasure {θ : ℝ} (hθ : 0 < θ) :
    ∫ x, x ^ 2 ∂(expMeasure θ) = 2 / θ ^ 2 := by
  simpa using ml_integral_expMeasure_pow hθ 2

/-- The exponential distribution has variance `1/θ²` (Miao, Exercise 12.2). -/
theorem ml_variance_expMeasure {θ : ℝ} (hθ : 0 < θ) :
    have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
    Var[id; expMeasure θ] = 1 / θ ^ 2 := by
  have : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  rw [variance_eq_sub (ml_memLp_two_expMeasure hθ)]
  have h2 := ml_second_moment_expMeasure hθ
  have h1 := ml_mean_expMeasure hθ
  simp only [Pi.pow_apply, id] at *
  rw [h2, h1]
  field_simp
  ring

end Miao.StructuralEstimation
