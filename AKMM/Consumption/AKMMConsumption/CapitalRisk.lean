/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMConsumption.Prudence
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Capital income uncertainty

AKMM, §11.3.4, box "Capital income uncertainty", pp. 309–310.

With `y₀ = c₀ + a₁` and `c₁ = Ra₁` for a random gross return `R > 0`, the Euler equation is
`u′(y₀ − a₁) = βE[Ru′(Ra₁)]`. The box claims that "under prudence … the right-hand side is still
a convex function of `r` (it is the product of a linear and a convex function)", so that saving
rises with a mean-preserving spread of the return. This is false.

* `d²/dR²[Ru′(Ra)] = a[2u″(c) + cu‴(c)]`, `c = Ra` (`cr_deriv`, `cr_second_deriv`), which is
  `≥ 0` iff relative prudence `−cu‴(c)/u″(c) ≥ 2` (`cr_second_deriv_nonneg_iff`).
* **Corrected claim:** if relative prudence is at least `2`, `R ↦ Ru′(Ra)` is convex
  (`cr_convex_of_rel_prudence`) and a mean-preserving spread of the return raises saving
  (`cr_spread_raises_saving`). For CRRA (relative prudence `σ + 1`) this is `σ ≥ 1`.
* **Counterexamples:** with log utility (`σ = 1`, prudent) return risk has no effect on saving
  (`cr_log_return_risk_neutral`); with `σ = 1/2` (prudent, `u‴ > 0`) the two-point spread of
  `R = 1` into `R = 1/2, 3/2` (a convex-order spread, `cr_return_spread_instance`) strictly
  lowers saving (`cr_printed_counterexample`).
-/

namespace AKMM.Consumption

open MeasureTheory Filter Topology

/-- AKMM, p. 309: the first derivative of `R ↦ Ru′(Ra)`, `u′(Ra) + Rau″(Ra)`. -/
theorem cr_deriv {u1 u2 : ℝ → ℝ} {a R : ℝ} (h1 : HasDerivAt u1 (u2 (R * a)) (R * a)) :
    HasDerivAt (fun x => x * u1 (x * a)) (u1 (R * a) + R * a * u2 (R * a)) R := by
  have hl : HasDerivAt (fun x : ℝ => x * a) a R := by simpa using (hasDerivAt_id R).mul_const a
  have := (hasDerivAt_id R).mul (h1.comp R hl)
  exact this.congr_deriv (by simp only [id, Function.comp_apply]; ring)

/-- AKMM, p. 309: the second derivative of `R ↦ Ru′(Ra)` is `a[2u″(c) + cu‴(c)]`, `c = Ra`. -/
theorem cr_second_deriv {u1 u2 u3 : ℝ → ℝ} {a R : ℝ} (h1 : HasDerivAt u1 (u2 (R * a)) (R * a))
    (h2 : HasDerivAt u2 (u3 (R * a)) (R * a)) :
    HasDerivAt (fun x => u1 (x * a) + x * a * u2 (x * a))
      (a * (2 * u2 (R * a) + R * a * u3 (R * a))) R := by
  have hl : HasDerivAt (fun x : ℝ => x * a) a R := by simpa using (hasDerivAt_id R).mul_const a
  have := (h1.comp R hl).add (hl.mul (h2.comp R hl))
  exact this.congr_deriv (by simp only [Function.comp_apply]; ring)

/-- **AKMM, p. 309, corrected.** With `a > 0`, `c = Ra > 0` and `u″(c) < 0`, the second
derivative `a[2u″(c) + cu‴(c)]` is nonnegative iff relative prudence `−cu‴(c)/u″(c) ≥ 2`. -/
theorem cr_second_deriv_nonneg_iff {a c u2c u3c : ℝ} (ha : 0 < a) (hu2 : u2c < 0) :
    0 ≤ a * (2 * u2c + c * u3c) ↔ 2 ≤ -c * u3c / u2c := by
  rw [le_div_iff_of_neg hu2]
  constructor
  · intro h
    have := nonneg_of_mul_nonneg_right (by linarith [h] : 0 ≤ a * (2 * u2c + c * u3c)) ha
    linarith
  · intro h
    exact mul_nonneg ha.le (by linarith)

/-- **AKMM, p. 310, corrected.** If `u″ < 0` and relative prudence is at least `2` on `(0, ∞)`,
then for `a > 0` the return function `R ↦ Ru′(Ra)` is convex on `(0, ∞)`. -/
theorem cr_convex_of_rel_prudence {u1 u2 u3 : ℝ → ℝ} (h1 : ∀ c, 0 < c → HasDerivAt u1 (u2 c) c)
    (h2 : ∀ c, 0 < c → HasDerivAt u2 (u3 c) c) (hu2 : ∀ c, 0 < c → u2 c < 0)
    (hrp : ∀ c, 0 < c → 2 ≤ -c * u3 c / u2 c) {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Set.Ioi 0) fun R => R * u1 (R * a) := by
  have hpos : ∀ R ∈ Set.Ioi (0 : ℝ), 0 < R * a := fun R hR => mul_pos hR ha
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (f' := fun R => u1 (R * a) + R * a * u2 (R * a))
    (f'' := fun R => a * (2 * u2 (R * a) + R * a * u3 (R * a))) ?_ ?_ ?_ ?_
  · exact fun R hR => (cr_deriv (h1 _ (hpos R hR))).continuousAt.continuousWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact (cr_deriv (h1 _ (hpos R hR))).hasDerivWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact (cr_second_deriv (h1 _ (hpos R hR)) (h2 _ (hpos R hR))).hasDerivWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    exact (cr_second_deriv_nonneg_iff ha (hu2 _ (hpos R hR))).2 (hrp _ (hpos R hR))

/-- **AKMM, p. 310, corrected: return risk raises saving when relative prudence is at least 2.**
Let `u′` be strictly decreasing on `(0, ∞)`, `R ↦ Ru′(Ra₁)` convex on `Y ⊆ (0, ∞)` (by
`cr_convex_of_rel_prudence`), and let the law `ν` of the return be a mean-preserving spread of `μ`
on `Y`. If `a₁ > 0` solves `u′(y₀ − a) = βE_μ[Ru′(Ra)]` and `a₂ > 0` solves it under `ν`, with
positive first-period consumption, then `a₁ ≤ a₂`. -/
theorem cr_spread_raises_saving {du : ℝ → ℝ} (hdu : StrictAntiOn du (Set.Ioi 0)) {β y₀ a₁ a₂ : ℝ}
    (hβ : 0 < β) {Y : Set ℝ} (hYpos : Y ⊆ Set.Ioi 0) {μ ν : Measure ℝ}
    (hspread : pr_ConvexOrderOn Y μ ν) (hconv : ConvexOn ℝ Y fun R => R * du (R * a₁))
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hc₀₁ : 0 < y₀ - a₁) (hc₀₂ : 0 < y₀ - a₂)
    (hμ₁ : Integrable (fun R => R * du (R * a₁)) μ) (hν₁ : Integrable (fun R => R * du (R * a₁)) ν)
    (hν₂ : Integrable (fun R => R * du (R * a₂)) ν)
    (h₁ : du (y₀ - a₁) = β * ∫ R, R * du (R * a₁) ∂μ)
    (h₂ : du (y₀ - a₂) = β * ∫ R, R * du (R * a₂) ∂ν) : a₁ ≤ a₂ := by
  have hup : ∫ R, R * du (R * a₁) ∂μ ≤ ∫ R, R * du (R * a₁) ∂ν :=
    hspread.2.2 _ hconv hμ₁ hν₁
  by_contra hlt
  push Not at hlt
  have hF : du (y₀ - a₂) < du (y₀ - a₁) := hdu hc₀₁ hc₀₂ (by linarith)
  have hG : ∫ R, R * du (R * a₁) ∂ν ≤ ∫ R, R * du (R * a₂) ∂ν := by
    refine integral_mono_ae hν₁ hν₂ ?_
    filter_upwards [hspread.2.1] with R hR
    have hR0 : 0 < R := hYpos hR
    exact mul_le_mul_of_nonneg_left (hdu.antitoneOn (Set.mem_Ioi.2 (mul_pos hR0 ha₂))
      (Set.mem_Ioi.2 (mul_pos hR0 ha₁)) (by nlinarith)) hR0.le
  have := mul_le_mul_of_nonneg_left hup hβ.le
  have := mul_le_mul_of_nonneg_left hG hβ.le
  linarith

/-- **Counterexample to AKMM, p. 310, log utility.** With `u′(c) = 1/c` (prudent:
`u‴ = 2/c³ > 0`), `Ru′(Ra) = 1/a` does not depend on `R`: for every law of the return on
`(0, ∞)` the right side of the Euler equation is `β/a`, so return risk does not change saving. -/
theorem cr_log_return_risk_neutral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ R ∂μ, 0 < R) {a : ℝ} (ha : 0 < a) : ∫ R, R * (R * a)⁻¹ ∂μ = a⁻¹ := by
  have : ∫ R, R * (R * a)⁻¹ ∂μ = ∫ _R, a⁻¹ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ] with R hR
    field_simp
  rw [this, integral_const]
  simp

/-- The two-point return spread of the counterexample is a convex-order spread: `δ₁` is below
`½δ_{1/2} + ½δ_{3/2}` on `(0, ∞)`. -/
theorem cr_return_spread_instance :
    pr_ConvexOrderOn (Set.Ioi 0) (Measure.dirac 1)
      ((1 / 2 : ENNReal) • Measure.dirac (1 - 1 / 2) +
        (1 / 2 : ENNReal) • Measure.dirac (1 + 1 / 2)) :=
  pr_two_point_spread (convex_Ioi 0) (by norm_num) (by norm_num)

/-- **Counterexample to AKMM, p. 310** ("under prudence … the right-hand side is still a convex
function of `r` … precautionary saving behavior emerges even in the face of higher volatility of
returns"). CRRA with `σ = 1/2`, `u′(c) = 1/√c`, is prudent (`u‴(c) = (3/4)c^{−5/2} > 0`). Let
`a₁ ∈ (0, y₀)` solve the Euler equation with the sure return `R = 1` and `a₂ ∈ (0, y₀)` solve it
when `R` is `1/2` or `3/2` with probability `1/2` each (a mean-preserving spread,
`cr_return_spread_instance`). Then `a₂ < a₁`: return risk strictly lowers saving. -/
theorem cr_printed_counterexample {β y₀ a₁ a₂ : ℝ} (hβ : 0 < β) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hc₂ : 0 < y₀ - a₂)
    (h₁ : (Real.sqrt (y₀ - a₁))⁻¹ = β * (1 * (Real.sqrt (1 * a₁))⁻¹))
    (h₂ : (Real.sqrt (y₀ - a₂))⁻¹ = β * (1 / 2 * ((1 / 2) * (Real.sqrt ((1 / 2) * a₂))⁻¹) +
      1 / 2 * ((3 / 2) * (Real.sqrt ((3 / 2) * a₂))⁻¹))) :
    a₂ < a₁ ∧ ∀ c : ℝ, 0 < c → 0 < 1 / 2 * (1 / 2 + 1) * c ^ (-(1 / 2 : ℝ) - 2) := by
  refine ⟨?_, fun c hc => by positivity⟩
  -- the spread multiplies the right side by `m = (√(1/2) + √(3/2))/2 < 1`
  have hs1 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hs2 : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hp1 : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.2 (by norm_num)
  have hp2 : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.2 (by norm_num)
  have hm : (Real.sqrt (1 / 2) + Real.sqrt (3 / 2)) / 2 < 1 := by
    have hprod : Real.sqrt (1 / 2) * Real.sqrt (3 / 2) < 1 := by
      rw [← Real.sqrt_mul (by norm_num)]
      rw [show (1 / 2 : ℝ) * (3 / 2) = 3 / 4 by norm_num, Real.sqrt_lt' one_pos]
      norm_num
    nlinarith
  have hsq : ∀ R : ℝ, 0 < R → R * (Real.sqrt (R * a₂))⁻¹ = Real.sqrt R * (Real.sqrt a₂)⁻¹ := by
    intro R hR
    rw [Real.sqrt_mul hR.le]
    have := Real.sqrt_pos.2 hR
    have := Real.sqrt_pos.2 ha₂
    field_simp
    rw [Real.sq_sqrt hR.le]
  rw [hsq (1 / 2) (by norm_num), hsq (3 / 2) (by norm_num)] at h₂
  simp only [one_mul] at h₁
  have hrhs₂ : (Real.sqrt (y₀ - a₂))⁻¹ =
      β * ((Real.sqrt (1 / 2) + Real.sqrt (3 / 2)) / 2) * (Real.sqrt a₂)⁻¹ := by
    rw [h₂]; ring
  by_contra hle
  push Not at hle
  -- `F(a₁) ≤ F(a₂) = βm/√a₂ < β/√a₂ ≤ β/√a₁ = F(a₁)`
  have hF : (Real.sqrt (y₀ - a₁))⁻¹ ≤ (Real.sqrt (y₀ - a₂))⁻¹ := by
    apply inv_anti₀ (Real.sqrt_pos.2 hc₂)
    exact Real.sqrt_le_sqrt (by linarith)
  have hG : (Real.sqrt a₂)⁻¹ ≤ (Real.sqrt a₁)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 ha₁) (Real.sqrt_le_sqrt hle)
  have hpa : 0 < (Real.sqrt a₂)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ha₂)
  have h3 : β * ((Real.sqrt (1 / 2) + Real.sqrt (3 / 2)) / 2) * (Real.sqrt a₂)⁻¹ <
      β * (Real.sqrt a₂)⁻¹ := by
    rw [mul_assoc]
    apply mul_lt_mul_of_pos_left _ hβ
    nlinarith
  have h4 : β * (Real.sqrt a₂)⁻¹ ≤ β * (Real.sqrt a₁)⁻¹ := mul_le_mul_of_nonneg_left hG hβ.le
  linarith

end AKMM.Consumption
