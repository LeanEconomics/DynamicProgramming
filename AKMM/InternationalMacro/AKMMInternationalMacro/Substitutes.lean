/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.Armington

/-!
# Substitutes and complements (footnote 15)

AKMM, §23.3.1, footnote 15, p. 706: "For given aggregate consumption `C_t`, one can show that home
and foreign goods are substitutes (complements) when `φ > 1` (`φ < 1`) by calculating the
second-order cross-partial derivatives of equation (23.2), `∂²C_t/∂c_{H,t}∂c_{F,t}`."

The cross partial of the Armington aggregator is **positive for every** `φ > 0`, `φ ≠ 1`
(`subst_cross_partial_pos`, from the exact first and second derivatives `subst_hasDerivAt_x`,
`subst_hasDerivAt_xy`): its sign does not distinguish `φ > 1` from `φ < 1`. What is true is the
demand-side statement: at given expenditure, the demand (23.3) for the home good rises with the
price of the foreign good iff `φ > 1` (gross substitutes) and falls iff `φ < 1` (gross
complements) (`subst_gross_substitutes`, `subst_gross_complements`).
-/

namespace AKMM.InternationalMacro

open Real Set
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesIndex cesPrice cesPrice_pos cesPrice_strictMonoOn)
open ObstfeldRogoff.StickyPriceModels (cesDemand)
open ObstfeldRogoff.StickyPriceModels.ReduxPrimitives (blocPriceIndex blocPriceIndex_pos)

/-- The inner sum `a^{1/φ} x^{(φ−1)/φ} + (1−a)^{1/φ} y^{(φ−1)/φ}` of the aggregator (23.2). -/
noncomputable def substSum (a φ x y : ℝ) : ℝ :=
  a ^ (1 / φ) * x ^ ((φ - 1) / φ) + (1 - a) ^ (1 / φ) * y ^ ((φ - 1) / φ)

/-- The marginal product `∂C/∂c_H = a^{1/φ} c_H^{−1/φ} S^{1/(φ−1)}` of the aggregator (23.2). -/
noncomputable def substMPx (a φ x y : ℝ) : ℝ :=
  a ^ (1 / φ) * x ^ ((φ - 1) / φ - 1) * substSum a φ x y ^ (φ / (φ - 1) - 1)

/-- The inner sum of the aggregator is positive at interior bundles. -/
theorem substSum_pos {a φ x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hy : 0 < y) :
    0 < substSum a φ x y := by
  have : 0 < 1 - a := by linarith
  unfold substSum; positivity

/-- AKMM, (23.2): the first partial derivative of the Armington aggregator in `c_H`. -/
theorem subst_hasDerivAt_x {a φ x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ0 : 0 < φ) (hφ : φ ≠ 1)
    (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun x => cesIndex a φ x y) (substMPx a φ x y) x := by
  have hφ1 : φ - 1 ≠ 0 := sub_ne_zero.mpr hφ
  have hS := substSum_pos (φ := φ) ha0 ha1 hx hy
  have hin : HasDerivAt (fun x => substSum a φ x y)
      (a ^ (1 / φ) * ((φ - 1) / φ * x ^ ((φ - 1) / φ - 1))) x := by
    unfold substSum
    exact ((hasDerivAt_rpow_const (Or.inl hx.ne')).const_mul _).add_const _
  have h := hin.rpow_const (p := φ / (φ - 1)) (Or.inl hS.ne')
  unfold cesIndex substMPx
  refine h.congr_deriv ?_
  field_simp

/-- AKMM, fn 15: the cross partial `∂²C/∂c_H∂c_F` of the aggregator (23.2), the derivative in
`c_F` of `∂C/∂c_H`, is `a^{1/φ}(1−a)^{1/φ} c_H^{−1/φ} c_F^{−1/φ} S^{1/(φ−1)−1}/φ`. -/
theorem subst_hasDerivAt_xy {a φ x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ0 : 0 < φ)
    (hφ : φ ≠ 1) (hx : 0 < x) (hy : 0 < y) :
    HasDerivAt (fun y => substMPx a φ x y)
      (a ^ (1 / φ) * (1 - a) ^ (1 / φ) * x ^ ((φ - 1) / φ - 1) * y ^ ((φ - 1) / φ - 1)
        * substSum a φ x y ^ (φ / (φ - 1) - 1 - 1) / φ) y := by
  have hφ1 : φ - 1 ≠ 0 := sub_ne_zero.mpr hφ
  have hS := substSum_pos (φ := φ) ha0 ha1 hx hy
  have hin : HasDerivAt (fun y => substSum a φ x y)
      ((1 - a) ^ (1 / φ) * ((φ - 1) / φ * y ^ ((φ - 1) / φ - 1))) y := by
    unfold substSum
    exact ((hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul _).const_add _
  have h := (hin.rpow_const (p := φ / (φ - 1) - 1) (Or.inl hS.ne')).const_mul
    (a ^ (1 / φ) * x ^ ((φ - 1) / φ - 1))
  unfold substMPx
  refine h.congr_deriv ?_
  have e : (φ / (φ - 1) - 1) * ((φ - 1) / φ) = 1 / φ := by field_simp; ring
  calc _ = a ^ (1 / φ) * (1 - a) ^ (1 / φ) * x ^ ((φ - 1) / φ - 1) * y ^ ((φ - 1) / φ - 1)
        * substSum a φ x y ^ (φ / (φ - 1) - 1 - 1) * ((φ / (φ - 1) - 1) * ((φ - 1) / φ)) := by
        ring
    _ = _ := by rw [e]; ring

/-- **Footnote 15** (corrected), AKMM p. 706: the cross partial of the Armington aggregator is
strictly positive at every interior bundle, **for every** `φ > 0`, `φ ≠ 1` — for complements
(`φ < 1`) as well as substitutes (`φ > 1`) in the book's sense — so its sign cannot
characterise substitutability. -/
theorem subst_cross_partial_pos {a φ x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ0 : 0 < φ)
    (hx : 0 < x) (hy : 0 < y) :
    0 < a ^ (1 / φ) * (1 - a) ^ (1 / φ) * x ^ ((φ - 1) / φ - 1) * y ^ ((φ - 1) / φ - 1)
        * substSum a φ x y ^ (φ / (φ - 1) - 1 - 1) / φ := by
  have h1a : 0 < 1 - a := by linarith
  have hS := substSum_pos (φ := φ) ha0 ha1 hx hy
  positivity

/-- The Marshallian demand (23.3) for the home good at expenditure `E`: with `C = E/P`,
`a (p_H/P)^{−φ} E/P`. -/
noncomputable def substDemandH (a φ pH E pF : ℝ) : ℝ :=
  a * cesDemand φ pH (blocPriceIndex φ a pH pF) (E / blocPriceIndex φ a pH pF)

/-- The Marshallian home demand equals `a p_H^{−φ} P^{φ−1} E`. -/
theorem substDemandH_eq {a φ pH E pF : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hpH : 0 < pH)
    (hpF : 0 < pF) :
    substDemandH a φ pH E pF = a * pH ^ (-φ) * blocPriceIndex φ a pH pF ^ (φ - 1) * E := by
  have hP := blocPriceIndex_pos (θ := φ) ha0 ha1 hpH hpF
  unfold substDemandH cesDemand
  rw [div_rpow hpH.le hP.le, rpow_neg hP.le, rpow_sub_one hP.ne']
  field_simp

/-- AKMM, fn 15 (corrected): for `φ > 1` the goods are **gross substitutes**: at given
expenditure the demand for the home good is strictly increasing in the price of the foreign
good. -/
theorem subst_gross_substitutes {a φ pH E : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : 1 < φ)
    (hpH : 0 < pH) (hE : 0 < E) : StrictMonoOn (substDemandH a φ pH E) (Ioi 0) := by
  intro p₁ h₁ p₂ h₂ h12
  simp only [mem_Ioi] at h₁ h₂
  rw [substDemandH_eq ha0 ha1 hpH h₁, substDemandH_eq ha0 ha1 hpH h₂,
    armington_price_homog ha0 ha1 hφ.ne' hpH h₁, armington_price_homog ha0 ha1 hφ.ne' hpH h₂]
  have hm := cesPrice_strictMonoOn (θ := φ) ha0 ha1 hφ.ne' (mem_Ioi.mpr (div_pos h₁ hpH))
    (mem_Ioi.mpr (div_pos h₂ hpH)) (div_lt_div_of_pos_right h12 hpH)
  have hc := cesPrice_pos (θ := φ) ha0 ha1 (div_pos h₁ hpH)
  have hlt : (pH * cesPrice a φ (p₁ / pH)) ^ (φ - 1) < (pH * cesPrice a φ (p₂ / pH)) ^ (φ - 1) :=
    rpow_lt_rpow (by positivity) (mul_lt_mul_of_pos_left hm hpH) (by linarith)
  have hk : 0 < a * pH ^ (-φ) := by positivity
  have := mul_lt_mul_of_pos_left hlt hk
  nlinarith

/-- AKMM, fn 15 (corrected): for `φ < 1` the goods are **gross complements**: at given
expenditure the demand for the home good is strictly decreasing in the price of the foreign
good. -/
theorem subst_gross_complements {a φ pH E : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ < 1)
    (hpH : 0 < pH) (hE : 0 < E) : StrictAntiOn (substDemandH a φ pH E) (Ioi 0) := by
  intro p₁ h₁ p₂ h₂ h12
  simp only [mem_Ioi] at h₁ h₂
  rw [substDemandH_eq ha0 ha1 hpH h₁, substDemandH_eq ha0 ha1 hpH h₂,
    armington_price_homog ha0 ha1 hφ.ne hpH h₁, armington_price_homog ha0 ha1 hφ.ne hpH h₂]
  have hm := cesPrice_strictMonoOn (θ := φ) ha0 ha1 hφ.ne (mem_Ioi.mpr (div_pos h₁ hpH))
    (mem_Ioi.mpr (div_pos h₂ hpH)) (div_lt_div_of_pos_right h12 hpH)
  have hc := cesPrice_pos (θ := φ) ha0 ha1 (div_pos h₁ hpH)
  have hlt : (pH * cesPrice a φ (p₂ / pH)) ^ (φ - 1) < (pH * cesPrice a φ (p₁ / pH)) ^ (φ - 1) :=
    rpow_lt_rpow_of_neg (by positivity) (mul_lt_mul_of_pos_left hm hpH) (by linarith)
  have hk : 0 < a * pH ^ (-φ) := by positivity
  have := mul_lt_mul_of_pos_left hlt hk
  nlinarith

end AKMM.InternationalMacro
