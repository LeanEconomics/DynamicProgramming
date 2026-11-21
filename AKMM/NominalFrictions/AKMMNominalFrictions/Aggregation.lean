/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.PriceDispersion
import NewKeynesian.NKEquilibrium

/-!
# Calvo aggregation and price dispersion

AKMM, §18.3, pp. 540–542: the price index under Calvo pricing (18.9), inflation and the reset
price (18.10), the aggregate production function with price dispersion (18.11) and the
dispersion recursion (18.12).

The firms that cannot reset at `t` form a set `S` of measure `θ`, and (the book's "firms are
chosen randomly") the law of large numbers `∫_S f = θ ∫ f` holds for the relevant integrand;
both are hypotheses, as in Miao's `eq_19_13` and `eq_19_17`, which we import.

* `eq_18_9`: `P_t = [θP_{t−1}^{1−ε} + (1 − θ)(P^R_t)^{1−ε}]^{1/(1−ε)}`.
* `agg_reset_relprice`, `eq_18_10`: `p^R = [(1 − θ(1 + π)^{ε−1})/(1 − θ)]^{1/(1−ε)}` and
  `1 + π = [(1 − (1 − θ)(p^R)^{1−ε})/θ]^{1/(ε−1)}`.
* `eq_18_11`: `Y = A L/D` with `D = ∫ (P_j/P)^{−ε}`.
* `agg_dispersion_ge_one`, `agg_dispersion_eq_one_iff`: `D ≥ 1`, with equality iff all prices
  equal the index almost everywhere (Galí's Jensen argument, at `α = 0`).
* `eq_18_12`: `D_t = (1 − θ)(p^R_t)^{−ε} + θ(1 + π_t)^ε D_{t−1}`.
-/

namespace AKMM.NominalFrictions

open MeasureTheory Gali.BasicNewKeynesianModel.CES Gali.BasicNewKeynesianModel.PriceDispersion

/-- **AKMM, (18.9), p. 540**: prices at `t` are the old prices `p₀` on the non-adjusters `S`
(`μ(S) = θ`) and the reset price `P^R > 0` elsewhere; with the law of large numbers,
`P_t = [θ P_{t−1}^{1−ε} + (1 − θ)(P^R)^{1−ε}]^{1/(1−ε)}` (from Miao's `eq_19_13`). -/
theorem eq_18_9 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε PR : ℝ} (hε : 1 < ε) (hθ : μ.real S = θ)
    {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j) (hPR : 0 < PR)
    (hI : Integrable (fun j => p₀ j ^ (1 - ε)) μ) (hS1 : ∀ j ∈ S, p₁ j = p₀ j)
    (hSc : ∀ j ∉ S, p₁ j = PR)
    (hLLN : ∫ j in S, p₀ j ^ (1 - ε) ∂μ = θ * ∫ j, p₀ j ^ (1 - ε) ∂μ) :
    Miao.NewKeynesian.nk_priceIndex μ ε p₁ =
      (θ * Miao.NewKeynesian.nk_priceIndex μ ε p₀ ^ (1 - ε) + (1 - θ) * PR ^ (1 - ε)) ^
        (1 / (1 - ε)) := by
  have h := Miao.NewKeynesian.eq_19_13 hS hε hθ hp₀ hPR hI hS1 hSc hLLN
  rw [← h]
  have hpos : 0 ≤ Miao.NewKeynesian.nk_priceIndex μ ε p₁ := by
    change 0 ≤ (∫ j, p₁ j ^ (1 - ε) ∂μ) ^ (1 / (1 - ε))
    refine Real.rpow_nonneg (integral_nonneg fun j => Real.rpow_nonneg ?_ _) _
    by_cases hj : j ∈ S
    · rw [hS1 j hj]; exact (hp₀ j).le
    · rw [hSc j hj]; exact hPR.le
  have h1e : (1 : ℝ) - ε ≠ 0 := by linarith
  rw [← Real.rpow_mul hpos, mul_one_div_cancel h1e, Real.rpow_one]

/-- AKMM, p. 541: dividing (18.9) by `P_t^{1−ε}`, with `1 + π_t = P_t/P_{t−1}` and
`p^R = P^R/P_t`: `1 = θ(1 + π_t)^{ε−1} + (1 − θ)(p^R)^{1−ε}`. -/
theorem agg_index_relative {θ ε P Pm PR : ℝ} (hP : 0 < P) (hPm : 0 < Pm) (hPR : 0 < PR)
    (h9 : P ^ (1 - ε) = θ * Pm ^ (1 - ε) + (1 - θ) * PR ^ (1 - ε)) :
    1 = θ * (P / Pm) ^ (ε - 1) + (1 - θ) * (PR / P) ^ (1 - ε) := by
  have hx : 0 < P ^ (1 - ε) := Real.rpow_pos_of_pos hP _
  have e1 : (P / Pm) ^ (ε - 1) = Pm ^ (1 - ε) / P ^ (1 - ε) := by
    rw [show ε - 1 = -(1 - ε) by ring, Real.rpow_neg (div_pos hP hPm).le,
      Real.div_rpow hP.le hPm.le, inv_div]
  rw [e1, Real.div_rpow hPR.le hP.le]
  field_simp
  linarith

/-- AKMM, p. 541: the relative reset price in terms of inflation,
`p^R = [(1 − θ(1 + π)^{ε−1})/(1 − θ)]^{1/(1−ε)}`. -/
theorem agg_reset_relprice {θ ε Gπ pR : ℝ} (hε : 1 < ε) (hθ : θ < 1) (hpR : 0 < pR)
    (h : 1 = θ * Gπ ^ (ε - 1) + (1 - θ) * pR ^ (1 - ε)) :
    pR = ((1 - θ * Gπ ^ (ε - 1)) / (1 - θ)) ^ (1 / (1 - ε)) := by
  have e : (1 - θ * Gπ ^ (ε - 1)) / (1 - θ) = pR ^ (1 - ε) := by
    rw [div_eq_iff (by linarith)]; linarith
  have h1e : (1 : ℝ) - ε ≠ 0 := by linarith
  rw [e, ← Real.rpow_mul hpR.le, mul_one_div_cancel h1e, Real.rpow_one]

/-- **AKMM, (18.10), p. 541**: `1 + π_t = [(1 − (1 − θ)(p^R_t)^{1−ε})/θ]^{1/(ε−1)}`. -/
theorem eq_18_10 {θ ε Gπ pR : ℝ} (hε : 1 < ε) (hθ : 0 < θ) (hG : 0 < Gπ)
    (h : 1 = θ * Gπ ^ (ε - 1) + (1 - θ) * pR ^ (1 - ε)) :
    Gπ = ((1 - (1 - θ) * pR ^ (1 - ε)) / θ) ^ (1 / (ε - 1)) := by
  have e : (1 - (1 - θ) * pR ^ (1 - ε)) / θ = Gπ ^ (ε - 1) := by
    rw [div_eq_iff hθ.ne']; linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [e, ← Real.rpow_mul hG.le, show (ε - 1) * (1 / (ε - 1)) = 1 by field_simp, Real.rpow_one]

/-- **AKMM, (18.11), p. 541**: with `y_j = A ℓ_j` (18.3), demand `y_j = (P_j/P)^{−ε} Y` (18.4)
and labour-market clearing `L = ∫ ℓ_j`, `Y = A L/D` where `D = ∫ (P_j/P)^{−ε}` (`D > 0`). -/
theorem eq_18_11 {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε A Y P L : ℝ}
    (hA : 0 < A) {Pj ℓ : J → ℝ} (hD : 0 < ∫ j, (Pj j / P) ^ (-ε) ∂μ)
    (hprod : ∀ j, (Pj j / P) ^ (-ε) * Y = A * ℓ j) (hL : L = ∫ j, ℓ j ∂μ) :
    Y = A * L / ∫ j, (Pj j / P) ^ (-ε) ∂μ := by
  have hl : ∀ j, ℓ j = (Pj j / P) ^ (-ε) * (Y / A) := by
    intro j; rw [← mul_div_assoc, hprod j]; field_simp
  have : L = (∫ j, (Pj j / P) ^ (-ε) ∂μ) * (Y / A) := by
    rw [hL]; simp_rw [hl]; rw [integral_mul_const]
  rw [this]
  field_simp

/-- AKMM, p. 541: if all prices are equal, `D = 1` and `Y = A L`. -/
theorem agg_flex_output {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε P : ℝ} (hP : 0 < P) :
    ∫ _j : J, (P / P) ^ (-ε) ∂μ = 1 := by
  simp [div_self hP.ne']

/-- **AKMM, p. 541**: price dispersion `D = ∫ (P_j/P)^{−ε} ≥ 1`, `P` the CES price index
(Galí's `one_le_integral_disp` at `α = 0`). -/
theorem agg_dispersion_ge_one {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {Pj : J → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : Integrable (fun j => Pj j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (Pj j / priceIndex μ ε Pj) ^ (-ε)) μ) :
    1 ≤ ∫ j, (Pj j / priceIndex μ ε Pj) ^ (-ε) ∂μ := by
  have e : -ε / (1 - 0) = -ε := by simp
  have h := one_le_integral_disp (α := 0) hε le_rfl (by norm_num) hP hPi (by rw [e]; exact hD)
  rwa [e] at h

/-- **AKMM, p. 541**: `D = 1` iff every price equals the index almost everywhere, so `D > 1`
whenever prices are dispersed (Galí's `dispersion_eq_zero_iff` at `α = 0`). -/
theorem agg_dispersion_eq_one_iff {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {Pj : J → ℝ} (hP : ∀ j, 0 < Pj j)
    (hPi : Integrable (fun j => Pj j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (Pj j / priceIndex μ ε Pj) ^ (-ε)) μ) :
    ∫ j, (Pj j / priceIndex μ ε Pj) ^ (-ε) ∂μ = 1 ↔ ∀ᵐ j ∂μ, Pj j = priceIndex μ ε Pj := by
  have e : -ε / (1 - 0) = -ε := by simp
  have h := dispersion_eq_zero_iff (α := 0) hε le_rfl (by norm_num) hP hPi (by rw [e]; exact hD)
  rw [← h, dispersion, e, sub_zero, one_mul]
  have h1 := agg_dispersion_ge_one hε hP hPi hD
  constructor
  · intro h2; rw [h2, Real.log_one]
  · intro h2
    rcases Real.log_eq_zero.1 h2 with h3 | h3 | h3 <;> [linarith; exact h3; linarith]

/-- **AKMM, (18.12), p. 541**: prices at `t` are the old prices `p₀` on the non-adjusters `S`
(`μ(S) = θ`) and `P^R` elsewhere; with the law of large numbers
`∫_S (p₀/P_{t−1})^{−ε} = θ D_{t−1}`,
`D_t = (1 − θ)(P^R/P_t)^{−ε} + θ(1 + π_t)^ε D_{t−1}` (Miao's `eq_19_17` at `α = 0`). -/
theorem eq_18_12 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε PR P₀ P₁ : ℝ} (hθ : μ.real S = θ)
    (hP₀ : 0 < P₀) (hP₁ : 0 < P₁) {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j)
    (hI : Integrable (fun j => (p₀ j / P₀) ^ (-ε)) μ)
    (hS1 : ∀ j ∈ S, p₁ j = p₀ j) (hSc : ∀ j ∉ S, p₁ j = PR)
    (hLLN : ∫ j in S, (p₀ j / P₀) ^ (-ε) ∂μ = θ * ∫ j, (p₀ j / P₀) ^ (-ε) ∂μ) :
    ∫ j, (p₁ j / P₁) ^ (-ε) ∂μ =
      (1 - θ) * (PR / P₁) ^ (-ε) + θ * (P₁ / P₀) ^ ε * ∫ j, (p₀ j / P₀) ^ (-ε) ∂μ := by
  have e1 : -ε / (1 - 0) = -ε := by simp
  have e2 : ε / (1 - 0) = ε := by simp
  have h := Miao.NewKeynesian.eq_19_17 (α := 0) hS hθ hP₀ hP₁ hp₀ (by rw [e1]; exact hI) hS1
    hSc (by rw [Miao.NewKeynesian.nk_dispersion, e1]; exact hLLN)
  simp only [Miao.NewKeynesian.nk_dispersion, e1, e2] at h
  rw [h]
  ring

end AKMM.NominalFrictions
