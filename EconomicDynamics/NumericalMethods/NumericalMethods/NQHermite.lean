/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NQQuadrature
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Gauss–Hermite quadrature and normal expectations (Miao, §11.1.1, p. 349)

Miao, p. 349: Gauss–Hermite quadrature computes `∫ f(x) e^{−x²} dx ≃ ∑ᵢ wᵢ f(xᵢ)`, and is
"very useful to compute integrals with respect to normal distributions":
`E f(Y) = π^{−1/2} ∑ᵢ wᵢ f(√2 σ xᵢ + μ)` for `Y ~ N(μ, σ²)`.

* `nq_normal_expectation_hermite`: the change of variables behind the formula, an exact identity
  `E f(Y) = π^{−1/2} ∫ f(√2 σ x + μ) e^{−x²} dx` for every `f` (Bochner integrals).
* `nq_normal_expectation_gauss_hermite`: with an `n`-point Gauss–Hermite rule, the book's formula
  is exact for every polynomial `f` of degree `≤ 2n − 1`.
* `nq_hermite_one_point` (node `0`, weight `√π`) and `nq_hermite_two_point` (nodes `∓1/√2`,
  weights `√π/2`) are Gauss–Hermite rules; `nq_integral_odd_eq_zero`,
  `nq_integral_sq_mul_exp_neg_sq` (`∫ x² e^{−x²} dx = √π/2`) are the moments used.

**Departures.** The normal law is Mathlib's `gaussianReal μ v` with `v = σ²` (as `ℝ≥0`), `σ > 0`.
The book's "≃" is an equality on polynomials of degree `≤ 2n − 1`; the book's `Ef(Y) = …` is
the quadrature approximation, exact on that class.
-/

namespace Miao.NumericalMethods

open MeasureTheory Polynomial Real ProbabilityTheory

/-- Miao, p. 349 (normal expectations by Gauss–Hermite, exact change of variables): for
`Y ~ N(μ, σ²)` with `σ > 0` and every `f`, `E f(Y) = π^{−1/2} ∫ f(√2 σ x + μ) e^{−x²} dx`. -/
theorem nq_normal_expectation_hermite (m : ℝ) {σ : ℝ} (hσ : 0 < σ) (f : ℝ → ℝ) :
    ∫ y, f y ∂(gaussianReal m (Real.toNNReal (σ ^ 2))) =
      (√π)⁻¹ * ∫ x, f (√2 * σ * x + m) * Real.exp (-x ^ 2) := by
  set v : NNReal := Real.toNNReal (σ ^ 2)
  have hv : v ≠ 0 := by rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have hvr : (v : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg σ)
  rw [integral_gaussianReal_eq_integral_smul hv]
  set c : ℝ := √2 * σ with hcdef
  have hc : 0 < c := by positivity
  have key : ∫ y, gaussianPDFReal m v y • f y =
      c * ∫ x, gaussianPDFReal m v (c * x + m) • f (c * x + m) := by
    have h1 := Measure.integral_comp_mul_left
      (fun z => gaussianPDFReal m v (z + m) • f (z + m)) c
    have h2 := integral_add_right_eq_self (μ := volume) (fun z => gaussianPDFReal m v z • f z) m
    rw [h1, h2, abs_inv, abs_of_pos hc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne',
      one_mul]
  rw [key, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext x
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : √(2 * π * (v : ℝ)) = √2 * √π * σ := by
    rw [hvr, Real.sqrt_mul' _ (sq_nonneg σ), Real.sqrt_sq hσ.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have harg : -(c * x + m - m) ^ 2 / (2 * (v : ℝ)) = -x ^ 2 := by
    rw [hvr, hcdef]
    field_simp
    ring_nf
    rw [h2]
    ring
  rw [gaussianPDFReal_def]
  simp only [smul_eq_mul]
  rw [harg, hs, hcdef]
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  field_simp

/-- Miao, p. 349: with an `n`-point Gauss–Hermite rule `(xᵢ, wᵢ)` for the weight `e^{−x²}`, the
formula `E p(Y) = π^{−1/2} ∑ᵢ wᵢ p(√2 σ xᵢ + μ)`, `Y ~ N(μ, σ²)`, is exact for every polynomial
`p` of degree `≤ 2n − 1`. -/
theorem nq_normal_expectation_gauss_hermite {n : ℕ} {w x : Fin n → ℝ}
    (hG : nqIsGaussRule volume (fun y => Real.exp (-y ^ 2)) w x) (m : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {p : ℝ[X]} (hp : p.natDegree < 2 * n) :
    ∫ y, p.eval y ∂(gaussianReal m (Real.toNNReal (σ ^ 2))) =
      (√π)⁻¹ * ∑ i, w i * p.eval (√2 * σ * x i + m) := by
  rw [nq_normal_expectation_hermite m hσ]
  set q : ℝ[X] := p.comp (C (√2 * σ) * X + C m)
  have hq : ∀ t, q.eval t = p.eval (√2 * σ * t + m) := by
    intro t; simp [q]
  have hqd : q.natDegree < 2 * n :=
    lt_of_le_of_lt (natDegree_comp_le.trans (by
      calc p.natDegree * (C (√2 * σ) * X + C m).natDegree ≤ p.natDegree * 1 :=
            Nat.mul_le_mul_left _ natDegree_linear_le
        _ = p.natDegree := mul_one _)) hp
  have hex := nq_gauss_exact hG hqd
  simp only [hq] at hex
  rw [hex]
  rfl

/-- The integral over `ℝ` of an odd function vanishes. -/
theorem nq_integral_odd_eq_zero {g : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x) : ∫ x, g x = 0 := by
  have h := integral_neg_eq_self g (volume : Measure ℝ)
  simp only [hg, integral_neg] at h
  linarith

/-- `x ↦ xᵏ e^{−x²}` is integrable on `ℝ`. -/
theorem nq_integrable_pow_mul_exp_neg_sq (k : ℕ) :
    Integrable (fun y : ℝ => y ^ k * Real.exp (-y ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
    (s := (k : ℝ)) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  simpa [Real.rpow_natCast] using h

/-- Miao, p. 349: `∫ e^{−x²} dx = √π`. -/
theorem nq_integral_exp_neg_sq : ∫ x : ℝ, Real.exp (-x ^ 2) = √π := by
  have h := integral_gaussian 1
  simpa using h

/-- Miao, p. 349: `∫ x² e^{−x²} dx = √π / 2` (via the variance of `N(0, 1/2)`). -/
theorem nq_integral_sq_mul_exp_neg_sq : ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = √π / 2 := by
  have hσ : (0 : ℝ) < (√2)⁻¹ := by positivity
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := nq_normal_expectation_hermite 0 hσ (fun y => y ^ 2)
  have hc : √2 * (√2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  simp only [hc, one_mul, add_zero] at h
  set v : NNReal := Real.toNNReal ((√2)⁻¹ ^ 2)
  have hvr : (v : ℝ) = 1 / 2 := by
    rw [Real.coe_toNNReal _ (sq_nonneg _), inv_pow, h2]; norm_num
  have hvar := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hvar
  simp only [Pi.pow_apply, id] at hvar
  rw [integral_id_gaussianReal, hvr] at hvar
  have hE : ∫ y, y ^ 2 ∂(gaussianReal 0 v) = 1 / 2 := by linarith
  rw [hE] at h
  have hpi : 0 < √π := Real.sqrt_pos.mpr pi_pos
  field_simp at h ⊢
  linarith

/-- Miao, p. 349 (Gauss–Hermite, `n = 1`): the node `0` with weight `√π` is the one-point
Gauss–Hermite rule. -/
theorem nq_hermite_one_point :
    nqIsGaussRule volume (fun y => Real.exp (-y ^ 2)) (fun _ : Fin 1 => √π) (fun _ => 0) := by
  intro k hk
  refine ⟨nq_integrable_pow_mul_exp_neg_sq k, ?_⟩
  interval_cases k
  · simpa [nqQuad] using nq_integral_exp_neg_sq
  · simp only [nqQuad, pow_one, Finset.univ_unique, Finset.sum_singleton, mul_zero]
    exact nq_integral_odd_eq_zero fun x => by ring_nf

/-- Miao, p. 349 (Gauss–Hermite, `n = 2`): the nodes `∓1/√2` with weights `√π/2` form the
two-point Gauss–Hermite rule. -/
theorem nq_hermite_two_point :
    nqIsGaussRule volume (fun y => Real.exp (-y ^ 2)) (fun _ : Fin 2 => √π / 2)
      ![-(1 / √2), 1 / √2] := by
  intro k hk
  refine ⟨nq_integrable_pow_mul_exp_neg_sq k, ?_⟩
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  simp only [nqQuad, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  interval_cases k
  · simp only [pow_zero, one_mul, mul_one]
    rw [nq_integral_exp_neg_sq]; ring
  · rw [nq_integral_odd_eq_zero fun x => by ring_nf]
    ring
  · rw [nq_integral_sq_mul_exp_neg_sq]
    field_simp
    rw [h2]; ring
  · rw [nq_integral_odd_eq_zero fun x => by ring_nf]
    ring

end Miao.NumericalMethods
