/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw

/-!
# The lognormal Euler equation: buffer stock (11.41) and Zeldes

AKMM, §11.3.4, (11.41), p. 310, and the box "Excess sensitivity and liquidity constraints",
p. 311.

With CRRA utility, `u′(cₜ₊₁)/u′(cₜ) = exp(−σΔlog cₜ₊₁)`, and the Euler equation (with a
borrowing-constraint multiplier `λ ≥ 0`, `λ = 0` when the constraint is slack) is
`1 = (1 + λ)βR E exp(−σΔlog cₜ₊₁)`. If `Δlog cₜ₊₁` is Gaussian with mean `m` and variance `v`,
the moment generating function `E e^{tX} = exp(mt + vt²/2)` (Mathlib's `mgf_gaussianReal`) solves
this exactly:

* `m = (log(1 + r) − log(1 + ρ))/σ + (σ/2)v + log(1 + λ)/σ` (`cs_lognormal_euler`), so
  **(11.41), corrected**: `E Δlog c = (log(1 + r) − log(1 + ρ))/σ + (σ/2)Var(Δlog c)`
  (`eq_11_41`), and the Zeldes equation with the coefficient `σ/2` and `ρ` (`cs_zeldes_euler`).
* The printed coefficient `(σ + 1)/2` is wrong whenever `Var > 0` (`eq_11_41_printed_false`):
  it is the coefficient of the uncentred second moment of the growth *rate* in (11.36), where
  relative prudence is `σ + 1`.

Departure: the book's `≃` (and `r`, `ρ` for `log(1 + r)`, `log(1 + ρ)`) becomes the exact identity
under joint lognormality.
-/

namespace AKMM.Consumption

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω]

/-- AKMM, pp. 310–311: the lognormal Euler equation, exactly. If `X = Δlog cₜ₊₁` has law
`N(m, v)` and `1 = (1 + λ)βR E exp(−σX)` with `β = 1/(1 + ρ)`, `R = 1 + r`, `σ > 0`, then
`m = (log(1 + r) − log(1 + ρ))/σ + (σ/2)v + log(1 + λ)/σ`. -/
theorem cs_lognormal_euler {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) {σ r ρ lam : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hρ : 0 < 1 + ρ) (hlam : 0 < 1 + lam)
    (heuler : 1 = (1 + lam) * (1 / (1 + ρ)) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    m = (Real.log (1 + r) - Real.log (1 + ρ)) / σ + σ / 2 * (v : ℝ) +
      Real.log (1 + lam) / σ := by
  have hmgf := mgf_gaussianReal hX (-σ)
  rw [mgf] at hmgf
  rw [hmgf] at heuler
  have hpos : 0 < (1 + lam) * (1 / (1 + ρ)) * (1 + r) := by positivity
  have hlog := congrArg Real.log heuler
  rw [Real.log_one, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by positivity) hr.ne', Real.log_mul hlam.ne' (by positivity), one_div,
    Real.log_inv] at hlog
  field_simp
  nlinarith [hlog]

/-- **AKMM, (11.41), p. 310, corrected.** With CRRA utility, an interior Euler equation
`1 = βR E exp(−σΔlog cₜ₊₁)` and `Δlog cₜ₊₁ ~ N(m, v)`:
`E Δlog cₜ₊₁ = (log(1 + r) − log(1 + ρ))/σ + (σ/2)Var(Δlog cₜ₊₁)`. -/
theorem eq_11_41 {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal m v) P) {σ r ρ : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hρ : 0 < 1 + ρ)
    (heuler : 1 = 1 / (1 + ρ) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    ∫ ω, X ω ∂P = (Real.log (1 + r) - Real.log (1 + ρ)) / σ + σ / 2 * Var[X; P] := by
  have h := cs_lognormal_euler hX (lam := 0) hσ hr hρ (by norm_num) (by simpa using heuler)
  rw [hX.integral_eq, integral_id_gaussianReal, hX.variance_eq, variance_id_gaussianReal, h]
  simp

/-- **AKMM, p. 311, the Zeldes (1989) Euler equation, corrected.** With the multiplier `λ ≥ 0`,
`1 = (1 + λ)βR E exp(−σΔlog cₜ₊₁)` and `Δlog cₜ₊₁ ~ N(m, v)`:
`E Δlog cₜ₊₁ = (log(1 + r) − log(1 + ρ))/σ + (σ/2)Var(Δlog cₜ₊₁) + log(1 + λ)/σ`; the
coefficient on `log(1 + λ)` is `1/σ > 0`, as printed, and on the variance `σ/2`. -/
theorem cs_zeldes_euler {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {m : ℝ}
    {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) {σ r ρ lam : ℝ} (hσ : 0 < σ)
    (hr : 0 < 1 + r) (hρ : 0 < 1 + ρ) (hlam : 0 ≤ lam)
    (heuler : 1 = (1 + lam) * (1 / (1 + ρ)) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    ∫ ω, X ω ∂P = (Real.log (1 + r) - Real.log (1 + ρ)) / σ + σ / 2 * Var[X; P] +
      Real.log (1 + lam) / σ ∧ 0 < 1 / σ := by
  have h := cs_lognormal_euler hX hσ hr hρ (by linarith) heuler
  rw [hX.integral_eq, integral_id_gaussianReal, hX.variance_eq, variance_id_gaussianReal, h]
  exact ⟨rfl, by positivity⟩

/-- **Correction to AKMM, (11.41), p. 310** (and the Zeldes equation, p. 311), which print the
coefficient `(σ + 1)/2` on `Var(Δlog c)`. Under the exact lognormal Euler equation the printed
formula fails whenever the variance is positive: it overstates the mean by `v/2`. -/
theorem eq_11_41_printed_false {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {m : ℝ}
    {v : NNReal} (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) {σ r ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < 1 + r) (hρ : 0 < 1 + ρ)
    (heuler : 1 = 1 / (1 + ρ) * (1 + r) * ∫ ω, Real.exp (-σ * X ω) ∂P) :
    ∫ ω, X ω ∂P ≠ (Real.log (1 + r) - Real.log (1 + ρ)) / σ + (σ + 1) / 2 * Var[X; P] := by
  rw [eq_11_41 hX hσ hr hρ heuler, hX.variance_eq, variance_id_gaussianReal]
  have : (0 : ℝ) < v := lt_of_le_of_ne v.2 (fun h => hv (NNReal.coe_eq_zero.1 h.symm))
  intro h
  nlinarith

end AKMM.Consumption
