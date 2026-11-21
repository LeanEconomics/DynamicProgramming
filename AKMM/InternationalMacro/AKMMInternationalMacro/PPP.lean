/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.Armington

/-!
# The real exchange rate, the terms of trade and PPP

AKMM, §23.3.1, (23.5), (23.7)–(23.8), pp. 707–708, and the relative price of p. 711.

With the nominal exchange rate normalised to one and the law of one price `p*_i = p_i`, the
foreign CPI is the two-bloc index with the foreign weight `a*_H` on the home good, and the real
exchange rate `Q = P*/P` (23.7) depends on prices only through the terms of trade `T = p_F/p_H`
(23.5). We prove:

* (23.8): `Q = P(a*_H, T)/P(a_H, T)` and `Q^{1−φ} = (a*_H + a*_F T^{1−φ})/(a_H + a_F T^{1−φ})`
  (`eq_23_8`, `eq_23_8_rpow`);
* PPP: under the law of one price, `Q ≡ 1` for every `T` **iff** the baskets coincide,
  `a_H = a*_H` (`ppp_iff_same_basket`); `Q = 1` at `T = 1` always (`ppp_at_one`);
* home bias drives co-movement: `Q` is strictly increasing in `T` **iff** `a*_H < a_H`
  (`ppp_strictMonoOn_iff`), strictly decreasing if `a_H < a*_H` (`ppp_strictAntiOn`); in the
  symmetric case `a*_H = 1 − a_H`, `Q` and `T` co-move positively iff `a_H > 1/2` and PPP holds
  iff `a_H = 1/2` (`ppp_symmetric`);
* the relative price of home output, `(p_H/P)^{1−φ} = 1/(a_H + (1−a_H)T^{1−φ})` (p. 711,
  `ppp_relPrice`).
-/

namespace AKMM.InternationalMacro

open Real Set
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesPrice cesDenom cesPrice_pos cesDenom_pos
  cesPrice_rpow_one_sub)
open ObstfeldRogoff.StickyPriceModels.ReduxPrimitives (blocPriceIndex blocPriceIndex_pos
  blocPriceIndex_rpow)

/-- AKMM, (23.7)–(23.8), pp. 707–708: under the law of one price (`𝓔 = 1`, `p*_i = p_i`) the
real exchange rate `Q = P*/P` is `P(a*_H, T)/P(a_H, T)`, a function of the terms of trade
`T = p_F/p_H` alone. -/
theorem eq_23_8 {a as φ pH pF : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as) (has1 : as < 1)
    (hφ : φ ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    blocPriceIndex φ as pH pF / blocPriceIndex φ a pH pF
      = cesPrice as φ (pF / pH) / cesPrice a φ (pF / pH) := by
  rw [armington_price_homog has0 has1 hφ hpH hpF, armington_price_homog ha0 ha1 hφ hpH hpF]
  have := hpH.ne'
  have := (cesPrice_pos (θ := φ) ha0 ha1 (div_pos hpF hpH)).ne'
  field_simp

/-- AKMM, (23.8), p. 708, as printed: `Q^{1−φ} = (a*_H + a*_F T^{1−φ})/(a_H + a_F T^{1−φ})`. -/
theorem eq_23_8_rpow {a as φ T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as) (has1 : as < 1)
    (hφ : φ ≠ 1) (hT : 0 < T) :
    (cesPrice as φ T / cesPrice a φ T) ^ (1 - φ)
      = (as + (1 - as) * T ^ (1 - φ)) / (a + (1 - a) * T ^ (1 - φ)) := by
  rw [div_rpow (cesPrice_pos has0 has1 hT).le (cesPrice_pos ha0 ha1 hT).le,
    cesPrice_rpow_one_sub has0 has1 hT hφ, cesPrice_rpow_one_sub ha0 ha1 hT hφ]

/-- AKMM, p. 708: at `T = 1` the CPIs coincide and `Q = 1`, whatever the baskets. -/
theorem ppp_at_one (a as φ : ℝ) : cesPrice as φ 1 / cesPrice a φ 1 = 1 := by
  simp [cesPrice]

/-- AKMM, p. 707: with the law of one price and identical baskets (`a*_H = a_H`) PPP holds,
`Q = 1`, at every terms of trade. -/
theorem ppp_same_basket {a φ T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T) :
    cesPrice a φ T / cesPrice a φ T = 1 :=
  div_self (cesPrice_pos ha0 ha1 hT).ne'

/-- AKMM, p. 707: "absolute PPP … will only hold if … (i) LOOP … and (ii) consumption baskets
being identical". Under the law of one price, `Q(T) = 1` for all `T > 0` **iff**
`a*_H = a_H`. -/
theorem ppp_iff_same_basket {a as φ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as)
    (has1 : as < 1) (hφ : φ ≠ 1) :
    (∀ T : ℝ, 0 < T → cesPrice as φ T / cesPrice a φ T = 1) ↔ as = a := by
  constructor
  · intro h
    have h2 := h 2 two_pos
    have hr := congrArg (fun x => x ^ (1 - φ)) h2
    rw [eq_23_8_rpow ha0 ha1 has0 has1 hφ two_pos, one_rpow] at hr
    have hD := cesDenom_pos (θ := φ) ha0 ha1 two_pos
    unfold cesDenom at hD
    rw [div_eq_one_iff_eq hD.ne'] at hr
    have hne : (2 : ℝ) ^ (1 - φ) ≠ 1 := by
      rcases lt_or_gt_of_ne (sub_ne_zero.mpr (Ne.symm hφ) : (1 : ℝ) - φ ≠ 0) with h3 | h3
      · exact (rpow_lt_one_of_one_lt_of_neg one_lt_two h3).ne
      · exact (one_lt_rpow one_lt_two h3).ne'
    have : (as - a) * (1 - 2 ^ (1 - φ)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h4 | h4
    · linarith
    · exact absurd (by linarith) hne
  · rintro rfl T hT
    exact ppp_same_basket has0 has1 hT

/-- The cross-multiplication behind (23.8): for `a*_H < a_H` the map
`x ↦ (a*_H + (1−a*_H)x)/(a_H + (1−a_H)x)` is strictly increasing on `x > 0`. -/
theorem ppp_ratio_lt {a as x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as)
    (hlt : as < a) (hx : 0 < x) (hxy : x < y) :
    (as + (1 - as) * x) / (a + (1 - a) * x) < (as + (1 - as) * y) / (a + (1 - a) * y) := by
  have hy : 0 < y := hx.trans hxy
  have hD1 : 0 < a + (1 - a) * x := by nlinarith
  have hD2 : 0 < a + (1 - a) * y := by nlinarith
  rw [div_lt_div_iff₀ hD1 hD2]
  nlinarith [mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hxy)]

/-- AKMM, p. 708: "If `a_H = a*_F > 0.5`, then the co-movement will be positive". With
`a*_H < a_H` (home bias, `a*_H = a_F = 1 − a_H`), the real exchange rate (23.8) is strictly
increasing in the terms of trade, for every `φ ≠ 1`. -/
theorem ppp_strictMonoOn {a as φ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as)
    (has1 : as < 1) (hφ : φ ≠ 1) (hlt : as < a) :
    StrictMonoOn (fun T => cesPrice as φ T / cesPrice a φ T) (Ioi 0) := by
  intro T1 hT1 T2 hT2 h12
  simp only [mem_Ioi] at hT1 hT2
  simp only
  have hq : ∀ T : ℝ, 0 < T → cesPrice as φ T / cesPrice a φ T
      = ((as + (1 - as) * T ^ (1 - φ)) / (a + (1 - a) * T ^ (1 - φ))) ^ (1 / (1 - φ)) := by
    intro T hT
    have hN := cesDenom_pos (θ := φ) has0 has1 hT
    have hD := cesDenom_pos (θ := φ) ha0 ha1 hT
    unfold cesDenom at hN hD
    unfold cesPrice
    rw [div_rpow hN.le hD.le]
  rw [hq T1 hT1, hq T2 hT2]
  have hpos : ∀ T : ℝ, 0 < T →
      0 < (as + (1 - as) * T ^ (1 - φ)) / (a + (1 - a) * T ^ (1 - φ)) := by
    intro T hT
    have hN := cesDenom_pos (θ := φ) has0 has1 hT
    have hD := cesDenom_pos (θ := φ) ha0 ha1 hT
    unfold cesDenom at hN hD
    exact div_pos hN hD
  rcases lt_or_gt_of_ne hφ with hlt1 | hgt1
  · have he : 0 < 1 - φ := by linarith
    have hx : T1 ^ (1 - φ) < T2 ^ (1 - φ) := rpow_lt_rpow hT1.le h12 he
    have hr := ppp_ratio_lt ha0 ha1 has0 hlt (rpow_pos_of_pos hT1 _) hx
    exact rpow_lt_rpow (hpos T1 hT1).le hr (by positivity)
  · have he : 1 - φ < 0 := by linarith
    have hx : T2 ^ (1 - φ) < T1 ^ (1 - φ) := rpow_lt_rpow_of_neg hT1 h12 he
    have hr := ppp_ratio_lt ha0 ha1 has0 hlt (rpow_pos_of_pos hT2 _) hx
    exact rpow_lt_rpow_of_neg (hpos T2 hT2) hr (one_div_neg.mpr he)

/-- AKMM, p. 708: if instead `a_H < a*_H` (foreign bias), the real exchange rate (23.8) is
strictly decreasing in the terms of trade. -/
theorem ppp_strictAntiOn {a as φ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as)
    (has1 : as < 1) (hφ : φ ≠ 1) (hlt : a < as) :
    StrictAntiOn (fun T => cesPrice as φ T / cesPrice a φ T) (Ioi 0) := by
  intro T1 hT1 T2 hT2 h12
  have h := ppp_strictMonoOn has0 has1 ha0 ha1 hφ hlt hT1 hT2 h12
  simp only [mem_Ioi] at hT1 hT2
  simp only at h ⊢
  have p1 := cesPrice_pos (θ := φ) ha0 ha1 hT1
  have p2 := cesPrice_pos (θ := φ) ha0 ha1 hT2
  have q1 := cesPrice_pos (θ := φ) has0 has1 hT1
  have q2 := cesPrice_pos (θ := φ) has0 has1 hT2
  rw [div_lt_div_iff₀ q1 q2] at h
  rw [div_lt_div_iff₀ p2 p1]
  linarith

/-- AKMM, p. 708: under the law of one price the real exchange rate co-moves positively with
the terms of trade (is strictly increasing in `T`) **iff** `a*_H < a_H`. -/
theorem ppp_strictMonoOn_iff {a as φ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as)
    (has1 : as < 1) (hφ : φ ≠ 1) :
    StrictMonoOn (fun T => cesPrice as φ T / cesPrice a φ T) (Ioi 0) ↔ as < a := by
  refine ⟨fun h => ?_, ppp_strictMonoOn ha0 ha1 has0 has1 hφ⟩
  by_contra hn
  have h12 := h (mem_Ioi.mpr one_pos) (mem_Ioi.mpr two_pos)
    one_lt_two
  simp only at h12
  rcases (not_lt.mp hn).lt_or_eq with hlt | heq
  · have := ppp_strictAntiOn ha0 ha1 has0 has1 hφ hlt (mem_Ioi.mpr one_pos)
      (mem_Ioi.mpr two_pos) one_lt_two
    simp only at this
    linarith
  · rw [← heq] at h12
    rw [ppp_same_basket ha0 ha1 one_pos, ppp_same_basket ha0 ha1 two_pos] at h12
    exact lt_irrefl _ h12

/-- AKMM, p. 708, the symmetric case `a*_H = a_F = 1 − a_H`: the real exchange rate co-moves
positively with the terms of trade iff there is home bias, `a_H > 1/2`, and PPP holds at every
`T` iff `a_H = 1/2`. -/
theorem ppp_symmetric {a φ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) :
    (StrictMonoOn (fun T => cesPrice (1 - a) φ T / cesPrice a φ T) (Ioi 0) ↔ 1 / 2 < a) ∧
    ((∀ T : ℝ, 0 < T → cesPrice (1 - a) φ T / cesPrice a φ T = 1) ↔ a = 1 / 2) := by
  have h0 : 0 < 1 - a := by linarith
  have h1 : 1 - a < 1 := by linarith
  constructor
  · rw [ppp_strictMonoOn_iff ha0 ha1 h0 h1 hφ]
    constructor <;> intro h <;> linarith
  · rw [ppp_iff_same_basket ha0 ha1 h0 h1 hφ]
    constructor <;> intro h <;> linarith

/-- AKMM, p. 711: the relative price of home output in terms of home consumption satisfies
`(p_H/P)^{1−φ} = 1/(a_H + (1 − a_H)T^{1−φ})`. -/
theorem ppp_relPrice {a φ pH pF : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hpH : 0 < pH)
    (hpF : 0 < pF) :
    (pH / blocPriceIndex φ a pH pF) ^ (1 - φ)
      = 1 / (a + (1 - a) * (pF / pH) ^ (1 - φ)) := by
  have hT := div_pos hpF hpH
  have hc := cesPrice_pos (θ := φ) ha0 ha1 hT
  rw [armington_price_homog ha0 ha1 hφ hpH hpF]
  have e : pH / (pH * cesPrice a φ (pF / pH)) = (cesPrice a φ (pF / pH))⁻¹ := by
    field_simp
  rw [e, inv_rpow hc.le, cesPrice_rpow_one_sub ha0 ha1 hT hφ, one_div]

end AKMM.InternationalMacro
