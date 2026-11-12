/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.CESIndex
import StickyPriceModels.ReduxPrimitives

/-!
# The Armington aggregator, CES demands and the CPI

AKMM, §23.3.1, (23.2)–(23.4) and (23.6), pp. 706–707.

The Armington aggregator (23.2) is Obstfeld–Rogoff's CES index
`CESIndex.cesIndex a φ c_H c_F = [a^{1/φ} c_H^{(φ−1)/φ} + (1−a)^{1/φ} c_F^{(φ−1)/φ}]^{φ/(φ−1)}`
(with `a = a_H`, `a_F = 1 − a_H`), the CPI (23.4) is Obstfeld–Rogoff's two-bloc index
`ReduxPrimitives.blocPriceIndex φ a p_H p_F = [a p_H^{1−φ} + (1−a) p_F^{1−φ}]^{1/(1−φ)}`, and the
demands (23.3) are `a · cesDemand φ p_H P C` and `(1 − a) · cesDemand φ p_F P C`, with
`cesDemand φ p P C = (p/P)^{−φ} C`. All three are imported. We prove:

* the CPI is homogeneous: `P(p_H, p_F) = p_H · P(1, T)` with `T = p_F/p_H` the terms of trade
  (23.5), linking the two imported indexes (`armington_price_homog`);
* the demands (23.3) cost exactly `P C` and deliver exactly `C` units of the aggregator
  (`eq_23_3_spending`, `eq_23_3_index`);
* **expenditure minimisation** (duality): every bundle costs at least `P` times the aggregate it
  delivers (`eq_23_3_cost_min`), so (23.3) solve the household's intratemporal problem and (23.4)
  is the minimum cost of one unit of `C` (`eq_23_4_least_cost`);
* the relative demand (23.6): `1/T = (a/(1−a))^{1/φ} (c_H/c_F)^{−1/φ}` (`eq_23_6`).

Throughout `0 < a < 1` and `φ > 0`, `φ ≠ 1` (the index is the Cobb–Douglas limit at `φ = 1`,
where the CES formulas are not defined); the book allows `a_H = 1`, where the foreign good is not
consumed at home.
-/

namespace AKMM.InternationalMacro

open Real
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesIndex cesPrice cesDenom cesDemandT cesDemandN
  cesPrice_pos cesPrice_rpow_one_sub cesDenom_pos cesIndex_demand cesIndex_le_div_price)
open ObstfeldRogoff.StickyPriceModels (cesDemand)
open ObstfeldRogoff.StickyPriceModels.ReduxPrimitives (blocPriceIndex blocPriceIndex_pos
  blocPriceIndex_rpow)

/-- AKMM, (23.4) and (23.5), p. 707: the CPI is homogeneous of degree one in prices,
`P(p_H, p_F) = p_H · P(1, T)` with `T = p_F/p_H`; the second factor is Obstfeld–Rogoff's
one-relative-price CES index `cesPrice a φ T = [a + (1−a)T^{1−φ}]^{1/(1−φ)}`. -/
theorem armington_price_homog {a φ pH pF : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) :
    blocPriceIndex φ a pH pF = pH * cesPrice a φ (pF / pH) := by
  have h1 : 1 - φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hφ)
  have hD := cesDenom_pos (θ := φ) ha0 ha1 (div_pos hpF hpH)
  unfold cesDenom at hD
  unfold blocPriceIndex cesPrice
  have hsplit : a * pH ^ (1 - φ) + (1 - a) * pF ^ (1 - φ)
      = pH ^ (1 - φ) * (a + (1 - a) * (pF / pH) ^ (1 - φ)) := by
    rw [div_rpow hpF.le hpH.le]
    have := (rpow_pos_of_pos hpH (1 - φ)).ne'
    field_simp
  rw [hsplit, mul_rpow (rpow_pos_of_pos hpH _).le hD.le, ← rpow_mul hpH.le,
    mul_one_div_cancel h1, rpow_one]

/-- AKMM, (23.3)–(23.4), pp. 706–707: the demands
`c_H = a (p_H/P)^{−φ} C`, `c_F = (1−a)(p_F/P)^{−φ} C` cost exactly `𝓔 = P C`. -/
theorem eq_23_3_spending {a φ pH pF C : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) :
    pH * (a * cesDemand φ pH (blocPriceIndex φ a pH pF) C)
      + pF * ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF) C)
      = blocPriceIndex φ a pH pF * C := by
  set P := blocPriceIndex φ a pH pF with hPdef
  have hP : 0 < P := blocPriceIndex_pos ha0 ha1 hpH hpF
  have key : ∀ p : ℝ, 0 < p → p * (p / P) ^ (-φ) = p ^ (1 - φ) * P ^ φ := by
    intro p hp
    have h1 := (rpow_pos_of_pos hp φ).ne'
    rw [div_rpow hp.le hP.le, rpow_neg hp.le, rpow_neg hP.le, rpow_sub hp, rpow_one]
    field_simp
  have hPP : P ^ φ * P ^ (1 - φ) = P := by
    rw [← rpow_add hP]
    simp
  have hrp : P ^ (1 - φ) = a * pH ^ (1 - φ) + (1 - a) * pF ^ (1 - φ) :=
    blocPriceIndex_rpow hφ ha0 ha1 hpH hpF
  unfold cesDemand
  have e1 := key pH hpH
  have e2 := key pF hpF
  calc pH * (a * ((pH / P) ^ (-φ) * C)) + pF * ((1 - a) * ((pF / P) ^ (-φ) * C))
      = (a * (pH * (pH / P) ^ (-φ)) + (1 - a) * (pF * (pF / P) ^ (-φ))) * C := by ring
    _ = P ^ φ * P ^ (1 - φ) * C := by rw [e1, e2, hrp]; ring
    _ = P * C := by rw [hPP]

/-- The home demand (23.3) as Obstfeld–Rogoff's demand (16): with `P = p_H · cesPrice a φ T`,
`a (p_H/P)^{−φ} C = cesDemandT a φ T (cesPrice a φ T · C)`, and likewise for the foreign good. -/
theorem armington_demand_eq {a φ pH pF C : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) :
    a * cesDemand φ pH (blocPriceIndex φ a pH pF) C
        = cesDemandT a φ (pF / pH) (cesPrice a φ (pF / pH) * C) ∧
      (1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF) C
        = cesDemandN a φ (pF / pH) (cesPrice a φ (pF / pH) * C) := by
  set T := pF / pH with hT
  have hTpos : 0 < T := div_pos hpF hpH
  have hc := cesPrice_pos (θ := φ) ha0 ha1 hTpos
  have hden : cesDenom a φ T = cesPrice a φ T ^ (1 - φ) := by
    rw [cesPrice_rpow_one_sub ha0 ha1 hTpos hφ]; rfl
  have hfrac : cesPrice a φ T / cesPrice a φ T ^ (1 - φ) = cesPrice a φ T ^ φ := by
    have := (rpow_pos_of_pos hc φ).ne'
    rw [rpow_sub hc, rpow_one]
    field_simp
  have hPeq := armington_price_homog ha0 ha1 hφ hpH hpF
  rw [← hT] at hPeq
  have hq1 : pH / blocPriceIndex φ a pH pF = (cesPrice a φ T)⁻¹ := by
    rw [hPeq]; field_simp
  have hq2 : pF / blocPriceIndex φ a pH pF = T / cesPrice a φ T := by
    rw [hPeq, hT]; field_simp
  constructor
  · unfold cesDemand cesDemandT
    rw [hq1, inv_rpow hc.le, rpow_neg hc.le, inv_inv, hden, ← hfrac]
    ring
  · unfold cesDemand cesDemandN
    rw [hq2, div_rpow hTpos.le hc.le, hden, rpow_neg hc.le, ← hfrac]
    field_simp

/-- AKMM, (23.2)–(23.3), p. 706: the demands (23.3) deliver exactly `C` units of the Armington
aggregate (23.2). -/
theorem eq_23_3_index {a φ pH pF C : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ0 : 0 < φ) (hφ : φ ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) (hC : 0 < C) :
    cesIndex a φ (a * cesDemand φ pH (blocPriceIndex φ a pH pF) C)
      ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF) C) = C := by
  obtain ⟨h1, h2⟩ := armington_demand_eq (C := C) ha0 ha1 hφ hpH hpF
  have hc := cesPrice_pos (θ := φ) ha0 ha1 (div_pos hpF hpH)
  rw [h1, h2, cesIndex_demand ha0 ha1 hφ0 hφ (div_pos hpF hpH) (mul_pos hc hC)]
  field_simp

/-- **Expenditure minimisation**, AKMM p. 706: every bundle `(c_H, c_F)` costs at least
`P · C(c_H, c_F)`, with `P` the CPI (23.4) and `C(·,·)` the Armington aggregate (23.2); equality
holds at the demands (23.3) (`eq_23_3_spending`, `eq_23_3_index`). For `φ < 1` both goods must be
consumed in positive amounts (both are essential). Proof: Obstfeld–Rogoff's duality theorem
after dividing prices by `p_H`. -/
theorem eq_23_3_cost_min {a φ pH pF cH cF : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ0 : 0 < φ)
    (hφ : φ ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) (hcH : 0 ≤ cH) (hcF : 0 ≤ cF)
    (hint : φ < 1 → 0 < cH ∧ 0 < cF) (hcost : 0 < pH * cH + pF * cF) :
    blocPriceIndex φ a pH pF * cesIndex a φ cH cF ≤ pH * cH + pF * cF := by
  have hT : 0 < pF / pH := div_pos hpF hpH
  have hsplit : pH * cH + pF * cF = pH * (cH + pF / pH * cF) := by field_simp
  have hZ : 0 < cH + pF / pH * cF := by
    rw [hsplit] at hcost
    exact pos_of_mul_pos_right hcost hpH.le
  have hle := cesIndex_le_div_price ha0 ha1 hφ0 hφ hT hcH hcF hint hZ
  have hc := cesPrice_pos (θ := φ) ha0 ha1 hT
  rw [armington_price_homog ha0 ha1 hφ hpH hpF, hsplit]
  rw [le_div_iff₀ hc] at hle
  calc pH * cesPrice a φ (pF / pH) * cesIndex a φ cH cF
      = pH * (cesIndex a φ cH cF * cesPrice a φ (pF / pH)) := by ring
    _ ≤ pH * (cH + pF / pH * cF) := mul_le_mul_of_nonneg_left hle hpH.le

/-- AKMM, (23.4), p. 707: the CPI is the least cost of one unit of the aggregate: every interior
bundle with `C(c_H, c_F) = 1` costs at least `P`, and the demands (23.3) at `C = 1` cost exactly
`P` and deliver one unit. -/
theorem eq_23_4_least_cost {a φ pH pF : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ0 : 0 < φ)
    (hφ : φ ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    (∀ cH cF : ℝ, 0 < cH → 0 < cF → cesIndex a φ cH cF = 1 →
      blocPriceIndex φ a pH pF ≤ pH * cH + pF * cF) ∧
    cesIndex a φ (a * cesDemand φ pH (blocPriceIndex φ a pH pF) 1)
      ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF) 1) = 1 ∧
    pH * (a * cesDemand φ pH (blocPriceIndex φ a pH pF) 1)
      + pF * ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF) 1)
      = blocPriceIndex φ a pH pF := by
  refine ⟨fun cH cF hcH hcF h1 => ?_, eq_23_3_index ha0 ha1 hφ0 hφ hpH hpF one_pos, ?_⟩
  · have := eq_23_3_cost_min ha0 ha1 hφ0 hφ hpH hpF hcH.le hcF.le (fun _ => ⟨hcH, hcF⟩)
      (by positivity)
    rwa [h1, mul_one] at this
  · rw [eq_23_3_spending ha0 ha1 hφ hpH hpF, mul_one]

/-- AKMM, (23.6), p. 707: at the demands (23.3) the relative price of home goods equals the
marginal rate of substitution, `1/T = (a/(1−a))^{1/φ} (c_H/c_F)^{−1/φ}` with `T = p_F/p_H`. The
same identity holds abroad with the foreign weights (apply it with `a*_H`), since under the law
of one price both countries face the same `T`. -/
theorem eq_23_6 {a φ pH pF P C : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ0 : 0 < φ)
    (hpH : 0 < pH) (hpF : 0 < pF) (hP : 0 < P) (hC : 0 < C) :
    1 / (pF / pH) = (a / (1 - a)) ^ (1 / φ) *
      ((a * cesDemand φ pH P C) / ((1 - a) * cesDemand φ pF P C)) ^ (-(1 / φ)) := by
  have h1a : 0 < 1 - a := by linarith
  have hk : 0 < a / (1 - a) := div_pos ha0 h1a
  have hx : 0 < pH / pF := div_pos hpH hpF
  have hratio : (a * cesDemand φ pH P C) / ((1 - a) * cesDemand φ pF P C)
      = a / (1 - a) * (pH / pF) ^ (-φ) := by
    unfold cesDemand
    have e : (pH / pF) ^ (-φ) = (pH / P) ^ (-φ) / (pF / P) ^ (-φ) := by
      rw [← div_rpow (div_pos hpH hP).le (div_pos hpF hP).le]
      congr 1
      field_simp
    rw [e]
    have := (rpow_pos_of_pos (div_pos hpF hP) (-φ)).ne'
    field_simp
  rw [hratio, mul_rpow hk.le (rpow_pos_of_pos hx _).le, ← rpow_mul hx.le, ← mul_assoc,
    ← rpow_add hk]
  have e2 : -φ * -(1 / φ) = 1 := by field_simp
  rw [e2, rpow_one, add_neg_cancel, rpow_zero, one_mul]
  field_simp

end AKMM.InternationalMacro
