/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The basic DNK model: final goods firms (Miao §19.1.2)

Miao, §19.1.2, pp. 618–619. The intermediate goods are indexed by `j` in a probability space
`(J, μ)` (the book's `[0, 1]` with Lebesgue measure is the leading case); `ε > 1`.

* (19.5): the Dixit–Stiglitz aggregator `Y = (∫ y_j^{(ε−1)/ε} dj)^{ε/(ε−1)}` (`nk_aggY`), and
  (19.7): the price index `P = (∫ p_j^{1−ε} dj)^{1/(1−ε)}` (`nk_priceIndex`).
* (19.6), the first-order condition: `P Y^{1/ε} y_j^{−1/ε} = p_j` iff `y_j = (p_j/P)^{−ε}Y`
  (`eq_19_6_foc`).
* (19.6) solves the final goods firm's problem: with `P` the index (19.7), every input profile
  `y ≥ 0` costs at least `P · Y(y)`, so the profit `P·Y(y) − ∫p_jy_j dj` is at most `0`
  (`eq_19_6`), and the demand curve (19.6) attains `0`: it delivers exactly `Y`
  (`nk_demand_agg`) at cost `PY` (`nk_demand_cost`). The proof is the tangent-line
  (weighted AM–GM) inequality `y^ρ ≤ ρyd^{ρ−1} + (1 − ρ)d^ρ`, integrated.
* (19.7) from the zero profit condition: along the demand curve, `∫p_jy_j dj = PY` iff `P` is
  the index (19.7) (`eq_19_7`).
-/

open MeasureTheory

namespace Miao.NewKeynesian

/-- **(19.5)** (Miao, p. 618): the Dixit–Stiglitz aggregate `(∫ y_j^{(ε−1)/ε} dj)^{ε/(ε−1)}`. -/
noncomputable def nk_aggY {J : Type*} [MeasurableSpace J] (μ : Measure J) (ε : ℝ) (y : J → ℝ) :
    ℝ :=
  (∫ j, y j ^ ((ε - 1) / ε) ∂μ) ^ (ε / (ε - 1))

/-- **(19.7)** (Miao, p. 619): the price index `(∫ p_j^{1−ε} dj)^{1/(1−ε)}`. -/
noncomputable def nk_priceIndex {J : Type*} [MeasurableSpace J] (μ : Measure J) (ε : ℝ)
    (p : J → ℝ) : ℝ :=
  (∫ j, p j ^ (1 - ε) ∂μ) ^ (1 / (1 - ε))

/-- **(19.6)**, the first-order condition (Miao, p. 619): for `y_j, p_j, Y, P > 0` and `ε > 0`,
`P Y^{1/ε} y_j^{−1/ε} = p_j` iff `y_j = (p_j/P)^{−ε}Y`. -/
theorem eq_19_6_foc {ε P Y yj pj : ℝ} (hε : 0 < ε) (hP : 0 < P) (hY : 0 < Y) (hy : 0 < yj)
    (hpj : 0 < pj) :
    P * Y ^ (1 / ε) * yj ^ (-1 / ε) = pj ↔ yj = (pj / P) ^ (-ε) * Y := by
  have hYe := Real.rpow_pos_of_pos hY (1 / ε)
  have hye := Real.rpow_pos_of_pos hy (-1 / ε)
  constructor
  · intro h
    have e : pj / P = Y ^ (1 / ε) * yj ^ (-1 / ε) := by
      rw [← h]
      field_simp
    rw [e, Real.mul_rpow hYe.le hye.le, ← Real.rpow_mul hY.le, ← Real.rpow_mul hy.le,
      show 1 / ε * -ε = -1 by field_simp, show -1 / ε * -ε = 1 by field_simp, Real.rpow_one,
      Real.rpow_neg_one]
    field_simp
  · intro h
    have hq : 0 < pj / P := div_pos hpj hP
    have e : yj / Y = (pj / P) ^ (-ε) := by
      rw [h]
      field_simp
    have e2 : yj ^ (-1 / ε) = (pj / P) * Y ^ (-1 / ε) := by
      have : yj = (pj / P) ^ (-ε) * Y := h
      rw [this, Real.mul_rpow (Real.rpow_nonneg hq.le _) hY.le, ← Real.rpow_mul hq.le,
        show -ε * (-1 / ε) = 1 by field_simp, Real.rpow_one]
    rw [e2, mul_comm (pj / P), ← mul_assoc, mul_assoc P, ← Real.rpow_add hY,
      show 1 / ε + -1 / ε = 0 by ring, Real.rpow_zero]
    field_simp

/-- The integral of `p_j^{1−ε}` is positive when every `p_j > 0` (`μ` a probability measure). -/
theorem nk_integral_rpow_pos {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε : ℝ} {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) : 0 < ∫ j, p j ^ (1 - ε) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun j => (Real.rpow_pos_of_pos (hp j) _).le) hI]
  have : Function.support (fun j => p j ^ (1 - ε)) = Set.univ :=
    Set.eq_univ_of_forall fun j => (Real.rpow_pos_of_pos (hp j) _).ne'
  rw [this, measure_univ]
  exact one_pos

/-- (19.7): `P^{1−ε} = ∫ p_j^{1−ε} dj` for the price index, `ε ≠ 1`. -/
theorem nk_priceIndex_rpow {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε : ℝ}
    (hε : ε ≠ 1) {p : J → ℝ} (hI : 0 ≤ ∫ j, p j ^ (1 - ε) ∂μ) :
    nk_priceIndex μ ε p ^ (1 - ε) = ∫ j, p j ^ (1 - ε) ∂μ := by
  have h1 : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  rw [nk_priceIndex, ← Real.rpow_mul hI, show 1 / (1 - ε) * (1 - ε) = 1 by field_simp,
    Real.rpow_one]

/-- The price index is positive. -/
theorem nk_priceIndex_pos {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε : ℝ} {p : J → ℝ}
    (hI : 0 < ∫ j, p j ^ (1 - ε) ∂μ) : 0 < nk_priceIndex μ ε p :=
  Real.rpow_pos_of_pos hI _

/-- Along the demand curve, `((p_j/P)^{−ε}Y)^{(ε−1)/ε} = (p_j/P)^{1−ε}Y^{(ε−1)/ε}`. -/
theorem nk_demand_rpow {ε P Y pj : ℝ} (hε : 0 < ε) (hq : 0 < pj / P) (hY : 0 < Y) :
    ((pj / P) ^ (-ε) * Y) ^ ((ε - 1) / ε) = (pj / P) ^ (1 - ε) * Y ^ ((ε - 1) / ε) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hq.le _) hY.le, ← Real.rpow_mul hq.le,
    show -ε * ((ε - 1) / ε) = 1 - ε by field_simp; ring]

/-- (19.5)–(19.7) (Miao, pp. 618–619): the demand curve `y_j = (p_j/P)^{−ε}Y`, with `P` the
index (19.7), aggregates to `Y`. -/
theorem nk_demand_agg {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε Y : ℝ} (hε : 1 < ε) (hY : 0 < Y) {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) :
    nk_aggY μ ε (fun j => (p j / nk_priceIndex μ ε p) ^ (-ε) * Y) = Y := by
  have hIp := nk_integral_rpow_pos hp hI
  have hP := nk_priceIndex_pos hIp
  have hPe := nk_priceIndex_rpow (by linarith : ε ≠ 1) hIp.le
  set P := nk_priceIndex μ ε p
  have hPr : 0 < P ^ (1 - ε) := Real.rpow_pos_of_pos hP _
  have hpt : ∀ j, ((p j / P) ^ (-ε) * Y) ^ ((ε - 1) / ε) =
      p j ^ (1 - ε) * (Y ^ ((ε - 1) / ε) / P ^ (1 - ε)) := fun j => by
    rw [nk_demand_rpow (by linarith) (div_pos (hp j) hP) hY, Real.div_rpow (hp j).le hP.le]
    ring
  have hint : ∫ j, ((p j / P) ^ (-ε) * Y) ^ ((ε - 1) / ε) ∂μ = Y ^ ((ε - 1) / ε) := by
    simp only [hpt]
    rw [integral_mul_const, ← hPe]
    field_simp
  rw [nk_aggY, hint, ← Real.rpow_mul hY.le, show (ε - 1) / ε * (ε / (ε - 1)) = 1 by
    have : ε - 1 ≠ 0 := by linarith
    field_simp, Real.rpow_one]

/-- (19.6)–(19.7) (Miao, p. 619): the demand curve costs `∫p_jy_j dj = PY`. -/
theorem nk_demand_cost {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε Y : ℝ} (hε : 1 < ε) {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) :
    ∫ j, p j * ((p j / nk_priceIndex μ ε p) ^ (-ε) * Y) ∂μ = nk_priceIndex μ ε p * Y := by
  have hIp := nk_integral_rpow_pos hp hI
  have hP := nk_priceIndex_pos hIp
  have hPe := nk_priceIndex_rpow (by linarith : ε ≠ 1) hIp.le
  set P := nk_priceIndex μ ε p
  have hpt : ∀ j, p j * ((p j / P) ^ (-ε) * Y) = p j ^ (1 - ε) * (P ^ ε * Y) := fun j => by
    have hpj := hp j
    rw [Real.div_rpow hpj.le hP.le, Real.rpow_neg hpj.le, Real.rpow_neg hP.le,
      Real.rpow_sub hpj, Real.rpow_one]
    field_simp
  simp only [hpt]
  rw [integral_mul_const, ← hPe, ← mul_assoc, ← Real.rpow_add hP,
    show 1 - ε + ε = 1 by ring, Real.rpow_one]

/-- **(19.7)** (Miao, p. 619), from zero profit: along the demand curve
`y_j = (p_j/P)^{−ε}Y` (`Y > 0`, `P > 0`), `∫p_jy_j dj = PY` iff `P = (∫p_j^{1−ε}dj)^{1/(1−ε)}`. -/
theorem eq_19_7 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε Y P : ℝ} (hε : 1 < ε) (hY : 0 < Y) (hP : 0 < P) {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) :
    ∫ j, p j * ((p j / P) ^ (-ε) * Y) ∂μ = P * Y ↔ P = nk_priceIndex μ ε p := by
  have hIp := nk_integral_rpow_pos hp hI
  set I := ∫ j, p j ^ (1 - ε) ∂μ
  have hpt : ∀ j, p j * ((p j / P) ^ (-ε) * Y) = p j ^ (1 - ε) * (P ^ ε * Y) := fun j => by
    have hpj := hp j
    rw [Real.div_rpow hpj.le hP.le, Real.rpow_neg hpj.le, Real.rpow_neg hP.le,
      Real.rpow_sub hpj, Real.rpow_one]
    field_simp
  simp only [hpt]
  rw [integral_mul_const]
  have hPe : 0 < P ^ ε := Real.rpow_pos_of_pos hP _
  have h1 : (1 : ℝ) - ε ≠ 0 := by linarith
  have key : I * (P ^ ε * Y) = P * Y ↔ P ^ (1 - ε) = I := by
    rw [Real.rpow_sub hP, Real.rpow_one]
    constructor
    · intro h
      field_simp
      nlinarith [h]
    · intro h
      rw [← h]
      field_simp
  rw [key]
  constructor
  · intro h
    change P = I ^ (1 / (1 - ε))
    rw [← h, ← Real.rpow_mul hP.le, show (1 - ε) * (1 / (1 - ε)) = 1 by
      field_simp, Real.rpow_one]
  · intro h
    rw [h]
    exact nk_priceIndex_rpow (by linarith) hIp.le

/-- The tangent-line inequality for `x ↦ x^ρ`, `0 < ρ < 1`: `y^ρ ≤ ρyd^{ρ−1} + (1 − ρ)d^ρ` for
`y ≥ 0`, `d > 0`. -/
theorem nk_rpow_tangent {ρ y d : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (hy : 0 ≤ y) (hd : 0 < d) :
    y ^ ρ ≤ ρ * y * d ^ (ρ - 1) + (1 - ρ) * d ^ ρ := by
  have h := Real.geom_mean_le_arith_mean2_weighted h0.le (by linarith : 0 ≤ 1 - ρ) hy hd.le
    (by ring)
  have hdm : 0 < d ^ (ρ - 1) := Real.rpow_pos_of_pos hd _
  have e1 : d ^ (1 - ρ) * d ^ (ρ - 1) = 1 := by
    rw [← Real.rpow_add hd]
    simp
  have e2 : d * d ^ (ρ - 1) = d ^ ρ := by
    rw [mul_comm, ← Real.rpow_add_one hd.ne']
    ring_nf
  have := mul_le_mul_of_nonneg_right h hdm.le
  calc y ^ ρ = y ^ ρ * (d ^ (1 - ρ) * d ^ (ρ - 1)) := by rw [e1, mul_one]
    _ = y ^ ρ * d ^ (1 - ρ) * d ^ (ρ - 1) := by ring
    _ ≤ (ρ * y + (1 - ρ) * d) * d ^ (ρ - 1) := this
    _ = ρ * y * d ^ (ρ - 1) + (1 - ρ) * (d * d ^ (ρ - 1)) := by ring
    _ = ρ * y * d ^ (ρ - 1) + (1 - ρ) * d ^ ρ := by rw [e2]

/-- **(19.6)** (Miao, p. 619): the demand curve solves the final goods firm's problem. With `P`
the index (19.7), every input profile `y ≥ 0` (with `y^{(ε−1)/ε}` and `py` integrable) costs at
least `P·Y(y)`: the profit `P·Y(y) − ∫p_jy_j dj` is at most `0`, the profit of the demand curve
(`nk_demand_agg`, `nk_demand_cost`). -/
theorem eq_19_6 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε : ℝ} (hε : 1 < ε) {p y : J → ℝ} (hp : ∀ j, 0 < p j) (hy : ∀ j, 0 ≤ y j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ)
    (hyI : Integrable (fun j => y j ^ ((ε - 1) / ε)) μ)
    (hpy : Integrable (fun j => p j * y j) μ) :
    nk_priceIndex μ ε p * nk_aggY μ ε y - ∫ j, p j * y j ∂μ ≤ 0 := by
  have hε0 : 0 < ε := by linarith
  have hIp := nk_integral_rpow_pos hp hI
  have hP := nk_priceIndex_pos hIp
  have hPe := nk_priceIndex_rpow (by linarith : ε ≠ 1) hIp.le
  set P := nk_priceIndex μ ε p
  set ρ := (ε - 1) / ε with hρ
  have hρ0 : 0 < ρ := div_pos (by linarith) hε0
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hε0]; linarith
  have hS : 0 ≤ ∫ j, y j ^ ρ ∂μ := integral_nonneg fun j => Real.rpow_nonneg (hy j) _
  have hpyn : 0 ≤ ∫ j, p j * y j ∂μ := integral_nonneg fun j => mul_nonneg (hp j).le (hy j)
  set Y := nk_aggY μ ε y with hYdef
  rcases hS.lt_or_eq with hSp | hS0
  swap
  · have : Y = 0 := by
      rw [hYdef, nk_aggY, ← hS0, Real.zero_rpow (by
        have : ε - 1 ≠ 0 := by linarith
        positivity)]
    rw [this, mul_zero]
    linarith
  have hY : 0 < Y := Real.rpow_pos_of_pos hSp _
  have hYρ : Y ^ ρ = ∫ j, y j ^ ρ ∂μ := by
    rw [hYdef, nk_aggY, ← Real.rpow_mul hS, show ε / (ε - 1) * ρ = 1 by
      rw [hρ]
      have : ε - 1 ≠ 0 := by linarith
      field_simp, Real.rpow_one]
  set d : J → ℝ := fun j => (p j / P) ^ (-ε) * Y
  have hd : ∀ j, 0 < d j := fun j => mul_pos (Real.rpow_pos_of_pos (div_pos (hp j) hP) _) hY
  have hdρ1 : ∀ j, d j ^ (ρ - 1) = p j * (Y ^ (ρ - 1) / P) := fun j => by
    have hq := div_pos (hp j) hP
    simp only [d]
    rw [Real.mul_rpow (Real.rpow_nonneg hq.le _) hY.le, ← Real.rpow_mul hq.le,
      show -ε * (ρ - 1) = 1 by rw [hρ]; field_simp; ring, Real.rpow_one]
    ring
  have hdρ : ∀ j, d j ^ ρ = p j ^ (1 - ε) * (Y ^ ρ / P ^ (1 - ε)) := fun j => by
    simp only [d]
    rw [nk_demand_rpow hε0 (div_pos (hp j) hP) hY, Real.div_rpow (hp j).le hP.le]
    ring
  have hpt : ∀ j, y j ^ ρ ≤ (p j * y j) * (ρ * (Y ^ (ρ - 1) / P)) +
      p j ^ (1 - ε) * ((1 - ρ) * (Y ^ ρ / P ^ (1 - ε))) := fun j => by
    have := nk_rpow_tangent hρ0 hρ1 (hy j) (hd j)
    rw [hdρ1, hdρ] at this
    linarith [this]
  set c1 := ρ * (Y ^ (ρ - 1) / P)
  set c2 := (1 - ρ) * (Y ^ ρ / P ^ (1 - ε))
  have hmono : ∫ j, y j ^ ρ ∂μ ≤ ∫ j, ((p j * y j) * c1 + p j ^ (1 - ε) * c2) ∂μ :=
    integral_mono hyI ((hpy.mul_const c1).add (hI.mul_const c2)) hpt
  rw [integral_add (hpy.mul_const c1) (hI.mul_const c2), integral_mul_const, integral_mul_const,
    ← hYρ, ← hPe] at hmono
  have hPr : 0 < P ^ (1 - ε) := Real.rpow_pos_of_pos hP _
  have e : P ^ (1 - ε) * ((1 - ρ) * (Y ^ ρ / P ^ (1 - ε))) = (1 - ρ) * Y ^ ρ := by
    field_simp
  rw [e] at hmono
  have hYr : Y ^ ρ = Y * Y ^ (ρ - 1) := by
    rw [← Real.rpow_one_add' hY.le (by linarith)]
    ring_nf
  have hYm : 0 < Y ^ (ρ - 1) := Real.rpow_pos_of_pos hY _
  have key : ρ * (Y * Y ^ (ρ - 1)) ≤ (∫ j, p j * y j ∂μ) * (ρ * (Y ^ (ρ - 1) / P)) := by
    rw [← hYr]
    linarith
  have key2 : P * Y ≤ ∫ j, p j * y j ∂μ := by
    have hc : 0 < ρ * Y ^ (ρ - 1) / P := by positivity
    have : (P * Y) * (ρ * Y ^ (ρ - 1) / P) ≤ (∫ j, p j * y j ∂μ) * (ρ * Y ^ (ρ - 1) / P) := by
      calc (P * Y) * (ρ * Y ^ (ρ - 1) / P) = ρ * (Y * Y ^ (ρ - 1)) := by field_simp
        _ ≤ (∫ j, p j * y j ∂μ) * (ρ * (Y ^ (ρ - 1) / P)) := key
        _ = (∫ j, p j * y j ∂μ) * (ρ * Y ^ (ρ - 1) / P) := by ring
    exact le_of_mul_le_mul_right this hc
  linarith

end Miao.NewKeynesian
