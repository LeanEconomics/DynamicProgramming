/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Exercise 22.2: the AR(1) endowment (Miao, p. 798)

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, Exercise 22.2, p. 798. Income follows
`ln y_t = ρ ln y_{t-1} + σ ε_t` with `β = 0.98`, `ρ = 0.95`, `σ = 0.1`, and the outside option is
autarky.

(a) The Bellman equation is that of §22.1.1 with the AR(1) transition in place of `π`; for any
finite discretisation of the shock it is `lc_BellmanAt` (module `LCBellman`). Its mathematical
input that can be computed in closed form is the autarky value: with log utility and
`x = ln y`, `U_d(y) = ln y/(1 − βρ)`, which solves the autarky recursion
`U_d(x) = x + β E[U_d(ρx + σε)]` for any mean-zero integrable shock (`ex_22_2a`); in particular
`U_d(1) = 0`.

(b), (c): not formalised (computational: Matlab code, plots, and the numerical root of
`P(v, 1) = 0`).
-/

namespace Miao.RecursiveContracts

open MeasureTheory

/-- **Exercise 22.2(a)** (Miao, p. 798), the autarky value with log utility: for any probability
distribution `μ` of the shock with mean zero, `x/(1 − βρ)` (with `x = ln y`) solves the autarky
recursion `U_d(x) = x + β ∫ U_d(ρx + σε) dμ(ε)`, and `U_d(1) = 0`. -/
theorem ex_22_2a (β ρ σ : ℝ) (hβρ : β * ρ ≠ 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun ε : ℝ => ε) μ) (hmean : ∫ ε, ε ∂μ = 0) (x : ℝ) :
    x / (1 - β * ρ) = x + β * ∫ ε, (ρ * x + σ * ε) / (1 - β * ρ) ∂μ ∧
      (Real.log 1) / (1 - β * ρ) = 0 := by
  have h1 : 1 - β * ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβρ)
  refine ⟨?_, by simp⟩
  have : ∫ ε, (ρ * x + σ * ε) / (1 - β * ρ) ∂μ = ρ * x / (1 - β * ρ) := by
    have e : (fun ε : ℝ => (ρ * x + σ * ε) / (1 - β * ρ)) =
        fun ε => ρ * x / (1 - β * ρ) + σ / (1 - β * ρ) * ε := by
      funext ε; field_simp
    rw [e, integral_add (integrable_const _) (hint.const_mul _), integral_const,
      integral_const_mul, hmean]
    simp
  rw [this]
  field_simp
  ring

end Miao.RecursiveContracts
