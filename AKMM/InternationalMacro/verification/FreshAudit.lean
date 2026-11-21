import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RealExchangeRate.CESIndex
import StickyPriceModels.ReduxPrimitives
import StickyPriceModels.ReduxLogLinear
import Mathlib.Analysis.SpecificLimits.Basic
import IntertemporalTrade.Stability
import CompleteMarkets.BPTree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import SmallOpenEconomyDynamics.StochasticConsumption
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# National accounting in the open economy

AKMM, §23.1.1 (pp. 694–695, footnote 4), §23.2.2 (pp. 701–702) and the bond-economy budget of
§23.3.2 (p. 713).

We prove the accounting identities of the chapter:

* national saving `S = Y − G − C` equals `I + NX` (p. 695);
* `CA = NX + NFI + NUT` (fn 4) and `CA + FA + KA = 0` (p. 694): the book's approximations
  `CA ≃ NX` and `CA ≃ −FA` are exact when `NFI = NUT = 0` and `KA = 0`, and in general the gaps
  are exactly `NFI + NUT` and `−KA`; so `S − I = −FA` up to `NFI + NUT + KA`;
* the real exchange rate `Q = 𝓔P*/P` gives `Δq = Δe + π* − π` exactly in logs, relative PPP
  (`Δq = 0`) iff `Δe = π − π*`, absolute PPP iff `Q = 1` (pp. 701–702);
* in the bond economy (p. 713) the trade balance is `(Q_t B_t − B_{t−1})/P_t` and the current
  account `ca_t = (B_t − B_{t−1})/P_t` is the trade balance plus the earnings `i_t Q_t B_t` on
  net foreign assets, where `Q_t = 1/(1 + i_t)`.
-/

namespace AKMM.InternationalMacro

/-- AKMM, p. 695: from `Y = C + I + G + NX`, national saving `S = Y − G − C` equals `I + NX`. -/
theorem accounting_saving {Y C I G NX : ℝ} (h : Y = C + I + G + NX) : Y - G - C = I + NX := by
  linarith

/-- AKMM, p. 694 and fn 4: with `CA = NX + NFI + NUT`, the gap `CA − NX` is exactly
`NFI + NUT`; in particular `CA = NX` when net factor income and net transfers vanish. -/
theorem accounting_ca_sub_nx {CA NX NFI NUT : ℝ} (h : CA = NX + NFI + NUT) :
    CA - NX = NFI + NUT ∧ (NFI = 0 → NUT = 0 → CA = NX) := by
  constructor
  · linarith
  · intro h1 h2
    rw [h, h1, h2]
    ring

/-- AKMM, pp. 694–695: from `CA + FA + KA = 0`, `CA + FA = −KA`, so `CA = −FA` when the capital
account is zero. -/
theorem accounting_ca_add_fa {CA FA KA : ℝ} (h : CA + FA + KA = 0) :
    CA + FA = -KA ∧ (KA = 0 → CA = -FA) := by
  constructor
  · linarith
  · intro hK
    rw [hK] at h
    linarith

/-- AKMM, p. 695: "trade deficits are financed by capital inflows". From the national accounts,
`CA = NX + NFI + NUT` and `CA + FA + KA = 0`: `S − I = NX = −FA − (KA + NFI + NUT)`, so a trade
deficit (`NX < 0`) is a financial-account surplus (`FA > 0`, a capital inflow) when
`KA = NFI = NUT = 0`. -/
theorem accounting_deficit_financed {Y C I G NX CA FA KA NFI NUT : ℝ}
    (hY : Y = C + I + G + NX) (hCA : CA = NX + NFI + NUT) (hB : CA + FA + KA = 0) :
    Y - G - C - I = -FA - (KA + NFI + NUT) ∧
      (KA = 0 → NFI = 0 → NUT = 0 → (NX < 0 ↔ 0 < FA)) := by
  constructor
  · linarith
  · intro h1 h2 h3
    constructor <;> intro h <;> linarith

/-- AKMM, p. 702: with `Q_t = 𝓔_t P*_t/P_t` (all positive), the log change of the real exchange
rate is exactly `Δq_t = Δe_t + π*_t − π_t`, with `π = Δ log P`. -/
theorem accounting_rer_log_change {E0 E1 P0 P1 Ps0 Ps1 : ℝ} (hE0 : 0 < E0) (hE1 : 0 < E1)
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hPs0 : 0 < Ps0) (hPs1 : 0 < Ps1) :
    Real.log (E1 * Ps1 / P1) - Real.log (E0 * Ps0 / P0) =
      (Real.log E1 - Real.log E0) + (Real.log Ps1 - Real.log Ps0)
        - (Real.log P1 - Real.log P0) := by
  rw [Real.log_div (by positivity) hP1.ne', Real.log_div (by positivity) hP0.ne',
    Real.log_mul hE1.ne' hPs1.ne', Real.log_mul hE0.ne' hPs0.ne']
  ring

/-- AKMM, p. 702: relative PPP. `Δq_t = 0` iff `Δe_t = π_t − π*_t`. -/
theorem accounting_relative_ppp_iff {E0 E1 P0 P1 Ps0 Ps1 : ℝ} (hE0 : 0 < E0) (hE1 : 0 < E1)
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hPs0 : 0 < Ps0) (hPs1 : 0 < Ps1) :
    Real.log (E1 * Ps1 / P1) - Real.log (E0 * Ps0 / P0) = 0 ↔
      Real.log E1 - Real.log E0 = (Real.log P1 - Real.log P0) - (Real.log Ps1 - Real.log Ps0) := by
  rw [accounting_rer_log_change hE0 hE1 hP0 hP1 hPs0 hPs1]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 701: absolute PPP `P = 𝓔P*` holds iff the real exchange rate `Q = 𝓔P*/P` is one. -/
theorem accounting_ppp_iff {E P Ps : ℝ} (hP : 0 < P) : E * Ps / P = 1 ↔ P = E * Ps := by
  rw [div_eq_one_iff_eq hP.ne']
  exact eq_comm

/-- AKMM, p. 713: in the bond economy, `C_t = (p_{H,t}Y_{H,t} − (Q_tB_t − B_{t−1}))/P_t`, so the
trade balance `p_{H,t}Y_{H,t}/P_t − C_t` is `(Q_tB_t − B_{t−1})/P_t`. -/
theorem accounting_bond_trade_balance {C pH Y Q B Bm P : ℝ} (hP : P ≠ 0)
    (hC : C = (pH * Y - (Q * B - Bm)) / P) : pH * Y / P - C = (Q * B - Bm) / P := by
  rw [hC]
  field_simp
  ring

/-- AKMM, p. 713: the current account `ca_t = (B_t − B_{t−1})/P_t` is the sum of the trade
balance `(Q_tB_t − B_{t−1})/P_t` and the earnings on net foreign assets `i_t Q_t B_t/P_t`, where the
bond price is `Q_t = 1/(1 + i_t)`. -/
theorem accounting_bond_current_account {i B Bm P : ℝ} (hi : 1 + i ≠ 0) :
    (B - Bm) / P = ((1 / (1 + i)) * B - Bm) / P + i * ((1 / (1 + i)) * B) / P := by
  field_simp
  ring

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Lagrange multiplier as the marginal utility of income

AKMM, §23.3.2, the box "Lagrange multiplier as the marginal utility of income (wealth)",
p. 712.

A consumer with increasing utility `u` of the Armington aggregate (23.2) and income `Y` chooses
`(c_H, c_F)` subject to `p_H c_H + p_F c_F = Y`. By duality (`eq_23_3_cost_min`) the maximised
utility is `u(Y/P)`, attained at the demands (23.3) (`env_value`); its derivative in income is
`u′(Y/P)/P = χ`, the multiplier of the first-order condition `u′(C) = χP` (`env_hasDerivAt`); and
when `u′` is strictly decreasing (strict concavity) `χ` is strictly decreasing in income
(`env_chi_strictAntiOn`). The CRRA utility of (23.1) is an instance (`env_crra`).
-/

namespace AKMM.InternationalMacro

open Real Set
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesIndex)
open ObstfeldRogoff.StickyPriceModels (cesDemand)
open ObstfeldRogoff.StickyPriceModels.ReduxPrimitives (blocPriceIndex blocPriceIndex_pos)

/-- AKMM, box p. 712: "the maximum utility equals `u(Y/P)`". For `u` increasing on `(0, ∞)`,
every interior bundle with `p_H c_H + p_F c_F = Y` gives at most `u(Y/P)`, and the demands (23.3)
at `C = Y/P` exhaust income and give exactly `u(Y/P)`. -/
theorem env_value {u : ℝ → ℝ} {a φ pH pF Y : ℝ} (hu : MonotoneOn u (Ioi 0)) (ha0 : 0 < a)
    (ha1 : a < 1) (hφ0 : 0 < φ) (hφ : φ ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) (hY : 0 < Y) :
    (∀ cH cF : ℝ, 0 < cH → 0 < cF → pH * cH + pF * cF = Y →
      u (cesIndex a φ cH cF) ≤ u (Y / blocPriceIndex φ a pH pF)) ∧
    pH * (a * cesDemand φ pH (blocPriceIndex φ a pH pF) (Y / blocPriceIndex φ a pH pF))
      + pF * ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF)
        (Y / blocPriceIndex φ a pH pF)) = Y ∧
    u (cesIndex a φ (a * cesDemand φ pH (blocPriceIndex φ a pH pF) (Y / blocPriceIndex φ a pH pF))
      ((1 - a) * cesDemand φ pF (blocPriceIndex φ a pH pF) (Y / blocPriceIndex φ a pH pF)))
      = u (Y / blocPriceIndex φ a pH pF) := by
  have hP := blocPriceIndex_pos (θ := φ) ha0 ha1 hpH hpF
  have h1a : 0 < 1 - a := by linarith
  refine ⟨fun cH cF hcH hcF hb => ?_, ?_, ?_⟩
  · have hle := eq_23_3_cost_min ha0 ha1 hφ0 hφ hpH hpF hcH.le hcF.le (fun _ => ⟨hcH, hcF⟩)
      (by rw [hb]; exact hY)
    rw [hb] at hle
    have hpos : 0 < cesIndex a φ cH cF := by unfold cesIndex; positivity
    exact hu hpos (div_pos hY hP) ((le_div_iff₀ hP).mpr (by linarith))
  · rw [eq_23_3_spending ha0 ha1 hφ hpH hpF]
    field_simp
  · rw [eq_23_3_index ha0 ha1 hφ0 hφ hpH hpF (div_pos hY hP)]

/-- AKMM, box p. 712: "the derivative of maximized utility with respect to income, `Y`, equals
`u′(Y/P)/P = χ`", where the first-order condition is `u′(C) = χP` at `C = Y/P`. -/
theorem env_hasDerivAt {u : ℝ → ℝ} {du : ℝ} {P Y : ℝ} (hP : P ≠ 0)
    (hu : HasDerivAt u du (Y / P)) :
    HasDerivAt (fun y => u (y / P)) (du / P) Y ∧ du = (du / P) * P := by
  refine ⟨?_, by field_simp⟩
  have h : HasDerivAt (fun y => u (y / P)) (du * (1 / P)) Y :=
    hu.comp Y ((hasDerivAt_id' Y).div_const P)
  exact h.congr_deriv (by ring)

/-- AKMM, box p. 712: "Given a strictly concave utility function `u`, therefore, `χ` is strictly
decreasing in income": if `u′` is strictly decreasing on `(0, ∞)` then
`Y ↦ u′(Y/P)/P` is strictly decreasing on `(0, ∞)`. -/
theorem env_chi_strictAntiOn {du : ℝ → ℝ} {P : ℝ} (hdu : StrictAntiOn du (Ioi 0)) (hP : 0 < P) :
    StrictAntiOn (fun Y => du (Y / P) / P) (Ioi 0) := by
  intro Y₁ h₁ Y₂ h₂ h12
  simp only [mem_Ioi] at h₁ h₂
  have := hdu (div_pos h₁ hP) (div_pos h₂ hP) (div_lt_div_of_pos_right h12 hP)
  exact div_lt_div_of_pos_right this hP

/-- AKMM, (23.1) and box p. 712: for CRRA utility `u(C) = (C^{1−σ} − 1)/(1 − σ)` (`σ > 0`,
`σ ≠ 1`), `u′(C) = C^{−σ}`, which is strictly decreasing, so `χ = (Y/P)^{−σ}/P` is strictly
decreasing in income. -/
theorem env_crra {σ P : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hP : 0 < P) :
    (∀ C : ℝ, 0 < C → HasDerivAt (fun c => (c ^ (1 - σ) - 1) / (1 - σ)) (C ^ (-σ)) C) ∧
      StrictAntiOn (fun Y => (Y / P) ^ (-σ) / P) (Ioi 0) := by
  have h1 : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ1)
  refine ⟨fun C hC => ?_, ?_⟩
  · have h := ((hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).div_const (1 - σ)
    refine h.congr_deriv ?_
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  · apply env_chi_strictAntiOn (du := fun c => c ^ (-σ)) _ hP
    intro x hx y hy hxy
    exact rpow_lt_rpow_of_neg hx hxy (by linarith)

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The symmetric steady state

AKMM, §23.3.3, p. 714: "We log-linearize the model around its symmetric non-stochastic steady
state with `Q = TOT = 1`".

Take symmetric endowments `Y_H = Y*_F = Y`, symmetric home bias `a*_H = 1 − a`, and the home good
as numeraire (`p_H = 1`, `p_F = T`). Under financial autarky (23.15) consumption is `C = Y/P`,
`C* = TY/P*`, and an equilibrium is a `T > 0` clearing the market for the home good (the foreign
market then clears by Walras' law, `ss_walras`). We prove:

* the excess demand for the home good is `Y[a/A + (1 − a)T/B − 1]` with
  `A = a + (1 − a)T^{1−φ}`, `B = (1 − a) + aT^{1−φ}`, and it vanishes iff
  `a(T − T^{2(1−φ)}) + (1 − a)T^{1−φ}(T − 1) = 0` (`ss_excess_eq`, `ss_equilibrium_iff`);
* **existence**: `T = 1` is an equilibrium, with `Q = 1`, `C = C* = Y`, `W = 1`
  (`ss_exists`), and it is also the complete-markets allocation with `κ₀ = 1` (`ss_cm_exists`);
* **uniqueness** for `φ ≥ 1/2`: `T = 1` is the only equilibrium (`ss_unique`);
* **non-uniqueness** with strong complementarity: for `a = 9/10`, `φ = 1/4` (below the threshold
  `1 − 1/(2a) = 4/9`) the autarky economy with symmetric endowments has a second equilibrium
  `T = ((9 + √77)/2)⁴ ≠ 1` (`ss_multiple`). The symmetric steady state the book linearises
  around exists for all parameters, but is not the only stationary equilibrium.
-/

namespace AKMM.InternationalMacro

open Real
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesPrice cesPrice_pos cesPrice_rpow_one_sub)
open ObstfeldRogoff.StickyPriceModels (cesDemand)

/-- The excess demand for the home good under financial autarky with symmetric endowments `Y`,
`p_H = 1` and `p_F = T`: home demand (23.3) at `C = Y/P` plus foreign demand at `C* = TY/P*`,
minus supply. -/
noncomputable def ssExcess (a φ Y T : ℝ) : ℝ :=
  a * cesDemand φ 1 (cesPrice a φ T) (Y / cesPrice a φ T)
    + (1 - a) * cesDemand φ 1 (cesPrice (1 - a) φ T) (T * Y / cesPrice (1 - a) φ T) - Y

/-- The excess demand for the foreign good in the same economy. -/
noncomputable def ssExcessF (a φ Y T : ℝ) : ℝ :=
  (1 - a) * cesDemand φ T (cesPrice a φ T) (Y / cesPrice a φ T)
    + a * cesDemand φ T (cesPrice (1 - a) φ T) (T * Y / cesPrice (1 - a) φ T) - Y

/-- `(1/P)^{−φ} · X/P = X/P^{1−φ}`. -/
theorem ss_demand_one {φ P X : ℝ} (hP : 0 < P) :
    cesDemand φ 1 P (X / P) = X / P ^ (1 - φ) := by
  unfold cesDemand
  rw [one_div, inv_rpow hP.le, rpow_neg hP.le, inv_inv, rpow_sub hP, rpow_one]
  have := (rpow_pos_of_pos hP φ).ne'
  field_simp

/-- The closed form of the home-good excess demand. -/
theorem ss_excess_eq {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hT : 0 < T) :
    ssExcess a φ Y T = Y * (a / (a + (1 - a) * T ^ (1 - φ))
      + (1 - a) * T / ((1 - a) + (1 - (1 - a)) * T ^ (1 - φ)) - 1) := by
  have h1a : 0 < 1 - a := by linarith
  unfold ssExcess
  rw [ss_demand_one (cesPrice_pos ha0 ha1 hT), ss_demand_one (cesPrice_pos h1a (by linarith) hT),
    cesPrice_rpow_one_sub ha0 ha1 hT hφ, cesPrice_rpow_one_sub h1a (by linarith) hT hφ]
  ring

/-- **Walras' law** (AKMM p. 707, market clearing): with the autarky budgets, the value of the
two excess demands is zero, `ED_H + T·ED_F = 0`; so when the home-good market clears, so does
the foreign-good market. -/
theorem ss_walras {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hT : 0 < T) :
    ssExcess a φ Y T + T * ssExcessF a φ Y T = 0 := by
  have h1a : 0 < 1 - a := by linarith
  have b1 := eq_23_3_spending (C := Y / cesPrice a φ T) ha0 ha1 hφ one_pos hT
  have b2 := eq_23_3_spending (C := T * Y / cesPrice (1 - a) φ T) h1a (by linarith : 1 - a < 1)
    hφ one_pos hT
  have hP1 : ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex φ a 1 T
      = cesPrice a φ T := by
    rw [armington_price_homog ha0 ha1 hφ one_pos hT, one_mul, div_one]
  have hP2 : ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex φ (1 - a) 1 T
      = cesPrice (1 - a) φ T := by
    rw [armington_price_homog h1a (by linarith) hφ one_pos hT, one_mul, div_one]
  rw [hP1] at b1
  rw [hP2] at b2
  have hc1 := (cesPrice_pos (θ := φ) ha0 ha1 hT).ne'
  have hc2 := (cesPrice_pos (θ := φ) h1a (by linarith) hT).ne'
  rw [one_mul, mul_div_cancel₀ _ hc1] at b1
  rw [one_mul, sub_sub_cancel, mul_div_cancel₀ _ hc2] at b2
  unfold ssExcess ssExcessF
  linear_combination b1 + b2

/-- The equilibrium condition in polynomial form: for `T > 0`, the home-good market clears iff
`a(T − T^{1−φ}T^{1−φ}) + (1 − a)T^{1−φ}(T − 1) = 0`. -/
theorem ss_equilibrium_iff {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hY : 0 < Y)
    (hT : 0 < T) :
    ssExcess a φ Y T = 0 ↔
      a * (T - T ^ (1 - φ) * T ^ (1 - φ)) + (1 - a) * T ^ (1 - φ) * (T - 1) = 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hx := rpow_pos_of_pos hT (1 - φ)
  have hA : 0 < a + (1 - a) * T ^ (1 - φ) := by positivity
  have hB : 0 < (1 - a) + (1 - (1 - a)) * T ^ (1 - φ) := by
    rw [sub_sub_cancel]; positivity
  rw [ss_excess_eq ha0 ha1 hφ hT, mul_eq_zero, or_iff_right hY.ne']
  rw [sub_sub_cancel] at hB ⊢
  constructor
  · intro h
    field_simp at h
    have h2 : (1 - a) * (a * (T - T ^ (1 - φ) * T ^ (1 - φ))
        + (1 - a) * T ^ (1 - φ) * (T - 1)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h2).resolve_left h1a.ne'
  · intro h
    field_simp
    linear_combination (1 - a) * h

/-- **Existence of the symmetric steady state**, AKMM p. 714: with symmetric endowments, `T = 1`
clears both goods markets under financial autarky, and there `Q = 1`, `C = C* = Y` and the
wealth gap `W = (C/C*)^σ/Q = 1`. -/
theorem ss_exists {a φ σ Y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hY : 0 < Y) :
    ssExcess a φ Y 1 = 0 ∧ ssExcessF a φ Y 1 = 0 ∧
      cesPrice (1 - a) φ 1 / cesPrice a φ 1 = 1 ∧
      Y / cesPrice a φ 1 = Y ∧ 1 * Y / cesPrice (1 - a) φ 1 = Y ∧
      ((Y / cesPrice a φ 1) / (1 * Y / cesPrice (1 - a) φ 1)) ^ σ
        / (cesPrice (1 - a) φ 1 / cesPrice a φ 1) = 1 := by
  have hone : ∀ γ : ℝ, cesPrice γ φ 1 = 1 := by intro γ; simp [cesPrice]
  have h1 : ssExcess a φ Y 1 = 0 := by
    rw [ss_equilibrium_iff ha0 ha1 hφ hY one_pos]; simp
  have h2 := ss_walras (Y := Y) ha0 ha1 hφ one_pos
  rw [h1, zero_add, one_mul] at h2
  simp only [hone, div_one, one_mul, div_self hY.ne', one_rpow]
  exact ⟨h1, h2, trivial, trivial, trivial, trivial⟩

/-- AKMM, pp. 710–711: the symmetric allocation is also the complete-markets equilibrium with
`κ₀ = 1`: at `T = 1` and `C = C* = Y` the demands (23.3) clear both goods markets and the risk
sharing condition (23.13) `Q = κ₀(C/C*)^σ` holds. -/
theorem ss_cm_exists {a φ σ Y : ℝ} (hY : 0 < Y) :
    a * cesDemand φ 1 (cesPrice a φ 1) Y + (1 - a) * cesDemand φ 1 (cesPrice (1 - a) φ 1) Y = Y ∧
      (1 - a) * cesDemand φ 1 (cesPrice a φ 1) Y + a * cesDemand φ 1 (cesPrice (1 - a) φ 1) Y
        = Y ∧
      cesPrice (1 - a) φ 1 / cesPrice a φ 1 = 1 * (Y / Y) ^ σ := by
  have hone : ∀ γ : ℝ, cesPrice γ φ 1 = 1 := by intro γ; simp [cesPrice]
  simp only [hone, cesDemand, div_one, one_rpow, one_mul, div_self hY.ne']
  exact ⟨by ring, by ring, trivial⟩

/-- **Uniqueness** for `φ ≥ 1/2` (and `φ ≠ 1`): with symmetric endowments the autarky
equilibrium terms of trade is `T = 1`. -/
theorem ss_unique {a φ Y T : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hφh : 1 / 2 ≤ φ)
    (hY : 0 < Y) (hT : 0 < T) (heq : ssExcess a φ Y T = 0) : T = 1 := by
  rw [ss_equilibrium_iff ha0 ha1 hφ hY hT] at heq
  have h1a : 0 < 1 - a := by linarith
  have hx := rpow_pos_of_pos hT (1 - φ)
  have hxx : T ^ (1 - φ) * T ^ (1 - φ) = T ^ (2 * (1 - φ)) := by
    rw [← rpow_add hT]; ring_nf
  rw [hxx] at heq
  have he : 2 * (1 - φ) ≤ 1 := by linarith
  rcases lt_trichotomy T 1 with hlt | heq1 | hgt
  · exfalso
    have h1 : T ≤ T ^ (2 * (1 - φ)) := by
      calc T = T ^ (1 : ℝ) := (rpow_one T).symm
        _ ≤ T ^ (2 * (1 - φ)) := rpow_le_rpow_of_exponent_ge hT hlt.le he
    have h2 : (1 - a) * T ^ (1 - φ) * (T - 1) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by linarith)
    nlinarith
  · exact heq1
  · exfalso
    have h1 : T ^ (2 * (1 - φ)) ≤ T := by
      calc T ^ (2 * (1 - φ)) ≤ T ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hgt.le he
        _ = T := rpow_one T
    have h2 : 0 < (1 - a) * T ^ (1 - φ) * (T - 1) := by
      have : 0 < T - 1 := by linarith
      positivity
    nlinarith

/-- **Multiple equilibria** with strong complementarity: for `a = 9/10` and `φ = 1/4`, the
autarky economy with symmetric endowments has the equilibrium `T = s⁴`, `s = (9 + √77)/2`, besides
`T = 1`. (`s² − 9s + 1 = 0`, and with `T = s⁴` the equilibrium condition factors as
`s³(1 − s²)(9s − 1 − s²)/10 = 0`.) -/
theorem ss_multiple {Y : ℝ} (hY : 0 < Y) :
    ssExcess (9 / 10) (1 / 4) Y (((9 + √77) / 2) ^ 4) = 0 ∧ ((9 + √77) / 2) ^ 4 ≠ (1 : ℝ) := by
  set s := (9 + √77) / 2 with hs
  have h77 : √77 ^ 2 = 77 := sq_sqrt (by norm_num)
  have hs8 : 8 < s := by
    have : 7 < √77 := by
      rw [show (7 : ℝ) = √49 by rw [show (49 : ℝ) = 7 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [hs]; linarith
  have hspos : 0 < s := by linarith
  have hquad : s ^ 2 - 9 * s + 1 = 0 := by rw [hs]; nlinarith [h77]
  clear_value s
  have hT : 0 < s ^ 4 := by positivity
  have hpow : (s ^ 4) ^ (1 - (1 / 4 : ℝ)) = s ^ 3 := by
    rw [← rpow_natCast s 4, ← rpow_mul hspos.le]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [ss_equilibrium_iff (by norm_num) (by norm_num) (by norm_num) hY hT, hpow]
    linear_combination (s ^ 3 / 10 * (s ^ 2 - 1)) * hquad
  · intro h
    have : 8 ^ 4 < s ^ 4 := by gcongr
    norm_num at this
    linarith

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The log-linear system as exact derivatives

AKMM, §23.3.3–§23.3.4, (23.21)–(23.27), pp. 714–718.

"Log-linearised" statements are made precise as exact derivatives at the symmetric
non-stochastic steady state `p_H = p_F = 1`, `P = P* = 1`, `Q = T = 1`, `C = C* = Ȳ`. We perturb
every variable along a ray: `p_H = e^{t·ph}`, `p_F = e^{t·pf}` (so the log terms of trade move by
`T̂ = pf − ph`), `C = Ȳe^{tĉ}`, `C* = Ȳe^{tĉ*}`, `Y_H = Ȳe^{tŷ}`, `Y_F = Ȳe^{tŷ*}`, and prove that
the derivative at `t = 0` of the log of each nonlinear object is the book's linear expression:

* the CPI (23.4): `P̂ = aph + (1−a)pf` (from Obstfeld–Rogoff's `hasDerivAt_log_bloc`);
* (23.21): `Q̂ = (a_H − a*_H)T̂`, i.e. `(2a_H − 1)T̂` when `a*_H = 1 − a_H` (`eq_23_21`);
* (23.22) is exact in logs: `log W = σ(log C − log C*) − log Q` (`eq_23_22`);
* the world demands for each good, `D̂_H = aĉ + (1−a)ĉ* + 2a(1−a)φT̂` and
  `D̂_F = (1−a)ĉ + aĉ* − 2a(1−a)φT̂` (`loglin_DH`, `loglin_DF`), hence (23.23) and world
  consumption `Ĉ + Ĉ* = D̂_H + D̂_F` (`eq_23_23`, `loglin_world`);
* (23.25): the autarky wealth gap (`eq_23_25`);
* (23.27): the bond-economy wealth gap (`eq_23_27`), with the bond position measured as in the
  correction recorded in `docs/corrections.md`.

The algebraic consequences (23.24) and (23.26) follow (`eq_23_24`, `eq_23_26`), with fn 28.
Throughout `0 < a < 1`, `φ > 0`, `φ ≠ 1` for the nonlinear objects.
-/

namespace AKMM.InternationalMacro

open Real
open ObstfeldRogoff.StickyPriceModels (cesDemand)
open ObstfeldRogoff.StickyPriceModels.ReduxPrimitives (blocPriceIndex blocPriceIndex_pos)
open ObstfeldRogoff.StickyPriceModels.ReduxLogLinear (hasDerivAt_log_bloc log_demand_exact)

/-- The CPI along the ray `p_H = e^{t·ph}`, `p_F = e^{t·pf}`. -/
noncomputable def loglinP (a φ ph pf t : ℝ) : ℝ := blocPriceIndex φ a (exp (t * ph)) (exp (t * pf))

/-- The CPI along the ray is positive. -/
theorem loglinP_pos {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) : 0 < loglinP a φ ph pf t :=
  blocPriceIndex_pos ha0 ha1 (exp_pos _) (exp_pos _)

/-- At the steady state `t = 0` the CPI is one. -/
theorem loglinP_zero (a φ ph pf : ℝ) : loglinP a φ ph pf 0 = 1 := by
  simp [loglinP, blocPriceIndex]

/-- AKMM, (23.4) log-linearised (used for (23.21)–(23.27)): `P̂ = a p̂_H + (1−a) p̂_F`. -/
theorem loglinP_hasDerivAt {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (loglinP a φ ph pf t)) (a * ph + (1 - a) * pf) 0 := by
  have h := hasDerivAt_log_bloc (θ := φ) (A := 1) (α := ph) (β := pf) hφ ha0 ha1 one_pos
  simpa [loglinP] using h

/-- A positive function whose log has derivative `d` at `0` has derivative `f 0 · d`. -/
theorem loglin_hasDerivAt_of_log {f : ℝ → ℝ} {d : ℝ} (hf : ∀ t, 0 < f t)
    (h : HasDerivAt (fun t => log (f t)) d 0) : HasDerivAt f (f 0 * d) 0 := by
  have h2 := h.exp
  rw [exp_log (hf 0)] at h2
  convert h2 using 1
  funext t
  rw [exp_log (hf t)]

/-- The log of a weighted sum of two positive functions that agree at `0` moves by the weighted
sum of their log-derivatives. -/
theorem loglin_log_weighted {f g : ℝ → ℝ} {n K df dg : ℝ} (hf : ∀ t, 0 < f t)
    (hg : ∀ t, 0 < g t) (hf0 : f 0 = K) (hg0 : g 0 = K) (hK : 0 < K)
    (hdf : HasDerivAt (fun t => log (f t)) df 0) (hdg : HasDerivAt (fun t => log (g t)) dg 0) :
    HasDerivAt (fun t => log (n * f t + (1 - n) * g t)) (n * df + (1 - n) * dg) 0 := by
  have h1 := loglin_hasDerivAt_of_log hf hdf
  have h2 := loglin_hasDerivAt_of_log hg hdg
  have hs : HasDerivAt (fun t => n * f t + (1 - n) * g t)
      (n * (f 0 * df) + (1 - n) * (g 0 * dg)) 0 := (h1.const_mul n).add (h2.const_mul (1 - n))
  have hv : n * f 0 + (1 - n) * g 0 = K := by rw [hf0, hg0]; ring
  have hl := hs.log (by rw [hv]; exact hK.ne')
  convert hl using 1
  rw [hv, hf0, hg0]
  field_simp

/-- **(23.21)** (general weights), AKMM p. 714: the log real exchange rate `log(P*/P)` moves by
`(a_H − a*_H)T̂`, `T̂ = pf − ph`. -/
theorem loglin_rer {a as φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (has0 : 0 < as) (has1 : as < 1)
    (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (loglinP as φ ph pf t / loglinP a φ ph pf t))
      ((a - as) * (pf - ph)) 0 := by
  have h := (loglinP_hasDerivAt (ph := ph) (pf := pf) has0 has1 hφ).sub
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ)
  have e : (fun t => log (loglinP as φ ph pf t / loglinP a φ ph pf t))
      = fun t => log (loglinP as φ ph pf t) - log (loglinP a φ ph pf t) := by
    funext t
    rw [log_div (loglinP_pos has0 has1 t).ne' (loglinP_pos ha0 ha1 t).ne']
  rw [e]
  convert h using 1
  ring

/-- **(23.21)**, AKMM p. 714: with symmetric home bias `a*_H = 1 − a_H`,
`Q̂_t = (2a_H − 1)T̂_t`. -/
theorem eq_23_21 {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t))
      ((2 * a - 1) * (pf - ph)) 0 := by
  have h := loglin_rer (ph := ph) (pf := pf) ha0 ha1 (by linarith : (0 : ℝ) < 1 - a)
    (by linarith : 1 - a < 1) hφ
  convert h using 1
  ring

/-- **(23.22)**, AKMM p. 714, exact in logs: with `W = (C/C*)^σ/Q` (23.16),
`log W = σ(log C − log C*) − log Q`. -/
theorem eq_23_22 {σ C Cs Q : ℝ} (hC : 0 < C) (hCs : 0 < Cs) (hQ : 0 < Q) :
    log ((C / Cs) ^ σ / Q) = σ * (log C - log Cs) - log Q := by
  rw [log_div (rpow_pos_of_pos (div_pos hC hCs) σ).ne' hQ.ne', log_rpow (div_pos hC hCs),
    log_div hC.ne' hCs.ne']

/-- The log of a CES demand `(p/P)^{−φ}C` along the ray moves by `−φ(p̂ − P̂) + Ĉ`. -/
theorem loglin_demand {φ dp dP dC : ℝ} {p P C : ℝ → ℝ} (hp : ∀ t, 0 < p t) (hP : ∀ t, 0 < P t)
    (hC : ∀ t, 0 < C t) (hdp : HasDerivAt (fun t => log (p t)) dp 0)
    (hdP : HasDerivAt (fun t => log (P t)) dP 0) (hdC : HasDerivAt (fun t => log (C t)) dC 0) :
    HasDerivAt (fun t => log (cesDemand φ (p t) (P t) (C t))) (-φ * (dp - dP) + dC) 0 := by
  have e : (fun t => log (cesDemand φ (p t) (P t) (C t)))
      = fun t => -φ * (log (p t) - log (P t)) + log (C t) := by
    funext t
    exact log_demand_exact (hp t) (hP t) (hC t)
  rw [e]
  exact ((hdp.sub hdP).const_mul (-φ)).add hdC

/-- `log(K e^{tc})` has derivative `c` at `0`. -/
theorem loglin_exp_ray (K c : ℝ) (hK : 0 < K) :
    HasDerivAt (fun t => log (K * exp (t * c))) c 0 := by
  have e : (fun t => log (K * exp (t * c))) = fun t => log K + t * c := by
    funext t; rw [log_mul hK.ne' (exp_pos _).ne', log_exp]
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (log K)

/-- The world demand `D_H = c_H + c*_H` for the home good along the ray (AKMM p. 715): home
demand (23.3) with weight `a` at the home CPI and foreign demand with weight `1 − a` at the foreign
CPI. -/
noncomputable def loglinDH (a φ ph pf c cs Ybar t : ℝ) : ℝ :=
  a * cesDemand φ (exp (t * ph)) (loglinP a φ ph pf t) (Ybar * exp (t * c))
    + (1 - a) * cesDemand φ (exp (t * ph)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs))

/-- The world demand `D*_F = c_F + c*_F` for the foreign good along the ray (AKMM p. 715). -/
noncomputable def loglinDF (a φ ph pf c cs Ybar t : ℝ) : ℝ :=
  (1 - a) * cesDemand φ (exp (t * pf)) (loglinP a φ ph pf t) (Ybar * exp (t * c))
    + a * cesDemand φ (exp (t * pf)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs))

/-- AKMM, p. 715: the world demand for the home good `D_H = c_H + c*_H` (with (23.3) at home and
abroad, weights `a` and `1 − a`) log-linearises to `D̂_H = aĈ + (1−a)Ĉ* + 2a(1−a)φT̂`. -/
theorem loglin_DH {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDH a φ ph pf c cs Ybar t))
      (a * c + (1 - a) * cs + 2 * a * (1 - a) * φ * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hexp : ∀ γ : ℝ, HasDerivAt (fun t => log (exp (t * γ))) γ 0 := by
    intro γ; simpa using loglin_exp_ray 1 γ one_pos
  have hf := loglin_demand (φ := φ) (p := fun t => exp (t * ph)) (fun t => exp_pos _)
    (loglinP_pos ha0 ha1) (fun t => mul_pos hY (exp_pos (t * c))) (hexp ph)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ) (loglin_exp_ray Ybar c hY)
  have hg := loglin_demand (φ := φ) (p := fun t => exp (t * ph)) (fun t => exp_pos _)
    (loglinP_pos h1a (by linarith)) (fun t => mul_pos hY (exp_pos (t * cs))) (hexp ph)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ) (loglin_exp_ray Ybar cs hY)
  have h0 : ∀ n : ℝ,
      cesDemand φ (exp (0 * ph)) (loglinP n φ ph pf 0) (Ybar * exp (0 * c)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have h0s : ∀ n : ℝ,
      cesDemand φ (exp (0 * ph)) (loglinP n φ ph pf 0) (Ybar * exp (0 * cs)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have hw := loglin_log_weighted (n := a)
    (f := fun t => cesDemand φ (exp (t * ph)) (loglinP a φ ph pf t) (Ybar * exp (t * c)))
    (g := fun t => cesDemand φ (exp (t * ph)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos ha0 ha1 t) (mul_pos hY (exp_pos _)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos h1a (by linarith) t) (mul_pos hY (exp_pos _))) (h0 a) (h0s (1 - a)) hY hf hg
  refine hw.congr_deriv ?_
  ring

/-- AKMM, p. 715: the world demand for the foreign good `D*_F = c_F + c*_F` log-linearises to
`D̂*_F = (1−a)Ĉ + aĈ* − 2a(1−a)φT̂`. -/
theorem loglin_DF {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDF a φ ph pf c cs Ybar t))
      ((1 - a) * c + a * cs - 2 * a * (1 - a) * φ * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hexp : ∀ γ : ℝ, HasDerivAt (fun t => log (exp (t * γ))) γ 0 := by
    intro γ; simpa using loglin_exp_ray 1 γ one_pos
  have hf := loglin_demand (φ := φ) (p := fun t => exp (t * pf)) (fun t => exp_pos _)
    (loglinP_pos ha0 ha1) (fun t => mul_pos hY (exp_pos (t * c))) (hexp pf)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ) (loglin_exp_ray Ybar c hY)
  have hg := loglin_demand (φ := φ) (p := fun t => exp (t * pf)) (fun t => exp_pos _)
    (loglinP_pos h1a (by linarith)) (fun t => mul_pos hY (exp_pos (t * cs))) (hexp pf)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ) (loglin_exp_ray Ybar cs hY)
  have h0 : ∀ n : ℝ,
      cesDemand φ (exp (0 * pf)) (loglinP n φ ph pf 0) (Ybar * exp (0 * c)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have h0s : ∀ n : ℝ,
      cesDemand φ (exp (0 * pf)) (loglinP n φ ph pf 0) (Ybar * exp (0 * cs)) = Ybar := by
    intro n; simp [cesDemand, loglinP_zero]
  have hw := loglin_log_weighted (n := 1 - a)
    (f := fun t => cesDemand φ (exp (t * pf)) (loglinP a φ ph pf t) (Ybar * exp (t * c)))
    (g := fun t => cesDemand φ (exp (t * pf)) (loglinP (1 - a) φ ph pf t) (Ybar * exp (t * cs)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos ha0 ha1 t) (mul_pos hY (exp_pos _)))
    (fun t => ObstfeldRogoff.StickyPriceModels.cesDemand_pos φ (exp_pos _)
      (loglinP_pos h1a (by linarith) t) (mul_pos hY (exp_pos _))) (h0 a) (h0s (1 - a)) hY hf hg
  have e : (fun t => log (loglinDF a φ ph pf c cs Ybar t)) = fun t =>
      log ((1 - a) * cesDemand φ (exp (t * pf)) (loglinP a φ ph pf t) (Ybar * exp (t * c))
        + (1 - (1 - a)) * cesDemand φ (exp (t * pf)) (loglinP (1 - a) φ ph pf t)
          (Ybar * exp (t * cs))) := by
    funext t; unfold loglinDF; ring_nf
  rw [e]
  refine hw.congr_deriv ?_
  ring

/-- **(23.23)**, AKMM p. 715: the relative world demand log-linearises to
`D̂_H − D̂*_F = (2a_H − 1)(Ĉ − Ĉ*) + 4a_H(1 − a_H)φT̂`. -/
theorem eq_23_23 {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDH a φ ph pf c cs Ybar t)
        - log (loglinDF a φ ph pf c cs Ybar t))
      ((2 * a - 1) * (c - cs) + 4 * a * (1 - a) * φ * (pf - ph)) 0 := by
  refine ((loglin_DH ha0 ha1 hφ hY).sub (loglin_DF ha0 ha1 hφ hY)).congr_deriv ?_
  ring

/-- AKMM, p. 715: world demand equals world consumption to first order,
`D̂_H + D̂*_F = Ĉ + Ĉ*`; with goods-market clearing `D = Y` this is `Ŷ_H + Ŷ*_F = Ĉ + Ĉ*`,
"independently of the structure of financial markets". -/
theorem loglin_world {a φ ph pf c cs Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinDH a φ ph pf c cs Ybar t)
        + log (loglinDF a φ ph pf c cs Ybar t)) (c + cs) 0 := by
  refine ((loglin_DH ha0 ha1 hφ hY).add (loglin_DF ha0 ha1 hφ hY)).congr_deriv ?_
  ring

/-- **(23.24)**, AKMM p. 716: substituting the wealth gap (23.22) `Ŵ = σ(Ĉ − Ĉ*) − Q̂` and
(23.21) `Q̂ = (2a − 1)T̂` into (23.23) gives
`D̂_H − D̂*_F = σ⁻¹(2a − 1)Ŵ + σ⁻¹[4a(1 − a)(σφ − 1) + 1]T̂`. -/
theorem eq_23_24 {a φ σ c cs q τ W : ℝ} (hσ : σ ≠ 0) (h21 : q = (2 * a - 1) * τ)
    (h22 : W = σ * (c - cs) - q) :
    (2 * a - 1) * (c - cs) + 4 * a * (1 - a) * φ * τ
      = σ⁻¹ * (2 * a - 1) * W + σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1) * τ := by
  rw [h22, h21]
  field_simp
  ring

/-- The coefficient of `T̂` in (23.24) equals `4a(1 − a)φ + (2a − 1)²/σ`. -/
theorem loglin_coef_eq {a φ σ : ℝ} (hσ : σ ≠ 0) :
    σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1) = 4 * a * (1 - a) * φ + (2 * a - 1) ^ 2 / σ := by
  field_simp
  ring

/-- **Footnote 28**, AKMM p. 716: the coefficient on `T̂` in (23.24) is positive and strictly
increasing in the trade elasticity `φ` (for `0 < a < 1`, `σ, φ > 0`). -/
theorem fn_28 {a σ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) :
    (∀ φ : ℝ, 0 < φ → 0 < σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1)) ∧
    StrictMono (fun φ : ℝ => σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1)) := by
  have h1a : 0 < 1 - a := by linarith
  constructor
  · intro φ hφ
    rw [loglin_coef_eq hσ.ne']
    have : 0 ≤ (2 * a - 1) ^ 2 / σ := div_nonneg (sq_nonneg _) hσ.le
    have : 0 < 4 * a * (1 - a) * φ := by positivity
    linarith
  · intro φ₁ φ₂ h
    simp only
    rw [loglin_coef_eq hσ.ne', loglin_coef_eq hσ.ne']
    have : 0 < 4 * a * (1 - a) := by positivity
    nlinarith

/-- The log of the autarky consumption `C = p_H Y_H/P` (23.15) along the ray. -/
theorem loglin_autarky_cons {a φ ph pf y Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t))
      (y - (1 - a) * (pf - ph)) 0 := by
  have e : (fun t => log (exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t))
      = fun t => log (exp (t * ph)) + log (Ybar * exp (t * y)) - log (loglinP a φ ph pf t) := by
    funext t
    rw [log_div (by positivity) (loglinP_pos ha0 ha1 t).ne',
      log_mul (exp_pos _).ne' (by positivity)]
  rw [e]
  have h1 : HasDerivAt (fun t => log (exp (t * ph))) ph 0 := by
    simpa using loglin_exp_ray 1 ph one_pos
  refine ((h1.add (loglin_exp_ray Ybar y hY)).sub
    (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ)).congr_deriv ?_
  ring

/-- **(23.25)**, AKMM p. 716: under financial autarky (`C = p_H Y_H/P`, `C* = p_F Y*_F/P*`) the
log wealth gap `log W = σ(log C − log C*) − log Q` (23.22) moves by
`Ŵ^{FA} = σ[Ŷ_H − Ŷ*_F − 2(1 − a_H)T̂] − (2a_H − 1)T̂`. -/
theorem eq_23_25 {a φ σ ph pf y ys Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t =>
        log (((exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t)
          / (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t)) ^ σ
          / (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t)))
      (σ * (y - ys - 2 * (1 - a) * (pf - ph)) - (2 * a - 1) * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have e : (fun t =>
        log (((exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t)
          / (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t)) ^ σ
          / (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t)))
      = fun t => σ * (log (exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t)
          - log (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t))
          - log (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t) := by
    funext t
    have hP := loglinP_pos (φ := φ) (ph := ph) (pf := pf) ha0 ha1 t
    have hPs := loglinP_pos (φ := φ) (ph := ph) (pf := pf) h1a (by linarith) t
    exact eq_23_22 (by positivity) (by positivity) (div_pos hPs hP)
  rw [e]
  have hC := loglin_autarky_cons (ph := ph) (pf := pf) (y := y) ha0 ha1 hφ hY
  have hCs : HasDerivAt (fun t => log (exp (t * pf) * (Ybar * exp (t * ys))
      / loglinP (1 - a) φ ph pf t)) (ys + (1 - a) * (pf - ph)) 0 := by
    have e2 : (fun t => log (exp (t * pf) * (Ybar * exp (t * ys)) / loglinP (1 - a) φ ph pf t))
        = fun t => log (exp (t * pf)) + log (Ybar * exp (t * ys))
          - log (loglinP (1 - a) φ ph pf t) := by
      funext t
      rw [log_div (by positivity) (loglinP_pos h1a (by linarith) t).ne',
        log_mul (exp_pos _).ne' (by positivity)]
    rw [e2]
    have h1 : HasDerivAt (fun t => log (exp (t * pf))) pf 0 := by
      simpa using loglin_exp_ray 1 pf one_pos
    refine ((h1.add (loglin_exp_ray Ybar ys hY)).sub
      (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ)).congr_deriv ?_
    ring
  have hQ := eq_23_21 (ph := ph) (pf := pf) ha0 ha1 hφ
  refine (((hC.sub hCs).const_mul σ).sub hQ).congr_deriv ?_
  ring

/-- **(23.26)**, AKMM p. 716: under financial autarky, with the consumption gap
`Ĉ − Ĉ* = Ŷ_H − Ŷ*_F − 2(1 − a)T̂` (from (23.15), `loglin_autarky_cons`), the relative demand
(23.23) and market clearing `D̂_H − D̂*_F = Ŷ_H − Ŷ*_F` give
`D̂_H − D̂*_F = [1 − 2a_H(1 − φ)]T̂` (for `a_H < 1`). -/
theorem eq_23_26 {a φ c cs y ys τ D : ℝ} (ha1 : a < 1)
    (h23 : D = (2 * a - 1) * (c - cs) + 4 * a * (1 - a) * φ * τ)
    (hFA : c - cs = y - ys - 2 * (1 - a) * τ) (hclear : D = y - ys) :
    D = (1 - 2 * a * (1 - φ)) * τ := by
  have h1a : (1 - a) ≠ 0 := by linarith
  have key : 2 * (1 - a) * D = 2 * (1 - a) * ((1 - 2 * a * (1 - φ)) * τ) := by
    rw [hFA] at h23
    nlinarith
  exact mul_left_cancel₀ (by positivity) key

/-- AKMM, p. 716: (23.26) equivalently from (23.24) and (23.25): substituting the autarky wealth
gap (23.25) into (23.24) and imposing `D̂ = Ŷ` gives the same schedule. -/
theorem eq_23_26_of_24_25 {a φ σ y ys τ W D : ℝ} (hσ : 0 < σ) (ha1 : a < 1)
    (h24 : D = σ⁻¹ * (2 * a - 1) * W + σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1) * τ)
    (h25 : W = σ * (y - ys - 2 * (1 - a) * τ) - (2 * a - 1) * τ) (hclear : D = y - ys) :
    D = (1 - 2 * a * (1 - φ)) * τ := by
  have h1a : 0 < 1 - a := by linarith
  have h' : D = (2 * a - 1) * (y - ys - 2 * (1 - a) * τ) + 4 * a * (1 - a) * φ * τ := by
    rw [h24, h25]
    field_simp
    ring
  exact eq_23_26 ha1 h' rfl hclear

/-- Bond-economy consumption along the ray (AKMM p. 713): `C = (p Y − Q_b B + B_{−1})/P`, with
income price `p = e^{t·pinc}`, output `Y = Ȳe^{ty}`, bond price `Q_b = β₀e^{t·qb}` and nominal bond
positions `B = tȲ·bb`, `B_{−1} = tȲ·bbm` (zero at the steady state, `P_{−1} = 1`), so that
`bb`, `bbm` are the first-order real bond positions `b/Ȳ`. -/
noncomputable def loglinBondCons (n φ ph pf pinc y bb bbm qb β₀ Ybar t : ℝ) : ℝ :=
  (exp (t * pinc) * (Ybar * exp (t * y)) - β₀ * exp (t * qb) * (t * Ybar * bb) + t * Ybar * bbm)
    / loglinP n φ ph pf t

/-- The log of bond-economy consumption moves by `p̂ + Ŷ − β₀ bb + bbm − P̂` (the linearised
budget constraint of AKMM p. 713). -/
theorem loglin_bond_cons {n φ ph pf pinc y bb bbm qb β₀ Ybar : ℝ} (hn0 : 0 < n) (hn1 : n < 1)
    (hφ : φ ≠ 1) (hY : 0 < Ybar) :
    HasDerivAt (fun t => log (loglinBondCons n φ ph pf pinc y bb bbm qb β₀ Ybar t))
      (pinc + y - β₀ * bb + bbm - (n * ph + (1 - n) * pf)) 0 := by
  have he : ∀ k : ℝ, HasDerivAt (fun t => exp (t * k)) k 0 := by
    intro k
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).exp
  have hlin : ∀ k : ℝ, HasDerivAt (fun t => t * k) k 0 := by
    intro k; simpa using (hasDerivAt_id (0 : ℝ)).mul_const k
  have h1 : HasDerivAt (fun t => exp (t * pinc) * (Ybar * exp (t * y))) (Ybar * (pinc + y)) 0 := by
    convert (he pinc).mul ((he y).const_mul Ybar) using 1
    simp; ring
  have h2 : HasDerivAt (fun t => β₀ * exp (t * qb) * (t * Ybar * bb)) (β₀ * Ybar * bb) 0 := by
    convert ((he qb).const_mul β₀).mul (hlin (Ybar * bb)) using 1
    · funext t; simp only [Pi.mul_apply]; ring
    · simp; ring
  have h3 : HasDerivAt (fun t => t * Ybar * bbm) (Ybar * bbm) 0 := by
    convert hlin (Ybar * bbm) using 1
    funext t; ring
  set N : ℝ → ℝ := fun t => exp (t * pinc) * (Ybar * exp (t * y))
      - β₀ * exp (t * qb) * (t * Ybar * bb) + t * Ybar * bbm with hNdef
  have hN : HasDerivAt N (Ybar * (pinc + y) - β₀ * Ybar * bb + Ybar * bbm) 0 := (h1.sub h2).add h3
  have hN0 : N 0 = Ybar := by simp [hNdef]
  have hP := loglin_hasDerivAt_of_log (loglinP_pos (φ := φ) (ph := ph) (pf := pf) hn0 hn1)
    (loglinP_hasDerivAt (ph := ph) (pf := pf) hn0 hn1 hφ)
  rw [loglinP_zero, one_mul] at hP
  have hP0 : loglinP n φ ph pf 0 ≠ 0 := by rw [loglinP_zero]; exact one_ne_zero
  have hq : HasDerivAt (fun t => N t / loglinP n φ ph pf t)
      (((Ybar * (pinc + y) - β₀ * Ybar * bb + Ybar * bbm) * loglinP n φ ph pf 0
        - N 0 * (n * ph + (1 - n) * pf)) / loglinP n φ ph pf 0 ^ 2) 0 := hN.div hP hP0
  have hv : N 0 / loglinP n φ ph pf 0 = Ybar := by rw [loglinP_zero, hN0, div_one]
  have hl := hq.log (by rw [hv]; exact hY.ne')
  unfold loglinBondCons
  refine hl.congr_deriv ?_
  rw [hv, loglinP_zero, hN0]
  field_simp

/-- **(23.27)**, AKMM p. 718: in the bond economy (bonds in zero net supply, so the foreign
position is the negative of the home one) the log wealth gap
`σ(log C − log C*) − log Q` (23.22) moves by
`σ[Ŷ_H − Ŷ*_F − 2(1 − a)T̂] − (2a − 1)T̂ + 2σ(bbm − β bb)`, where `bb`, `bbm` are the real bond
positions `b_t/Ȳ`, `b_{t−1}/Ȳ`. With `b̃ = β b/Ȳ` (the steady-state value of the position,
the convention of (23.30)) the last term is the printed `2σβ⁻¹[b̃_{t−1} − βb̃_t]`
(`loglin_bond_printed`). -/
theorem eq_23_27 {a φ σ ph pf y ys bb bbm qb β₀ Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : φ ≠ 1) (hY : 0 < Ybar) :
    HasDerivAt (fun t => σ * (log (loglinBondCons a φ ph pf ph y bb bbm qb β₀ Ybar t)
        - log (loglinBondCons (1 - a) φ ph pf pf ys (-bb) (-bbm) qb β₀ Ybar t))
        - log (loglinP (1 - a) φ ph pf t / loglinP a φ ph pf t))
      (σ * (y - ys - 2 * (1 - a) * (pf - ph)) - (2 * a - 1) * (pf - ph)
        + 2 * σ * (bbm - β₀ * bb)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hC := loglin_bond_cons (pinc := ph) (y := y) (bb := bb) (bbm := bbm) (qb := qb)
    (β₀ := β₀) (ph := ph) (pf := pf) ha0 ha1 hφ hY
  have hCs := loglin_bond_cons (pinc := pf) (y := ys) (bb := -bb) (bbm := -bbm) (qb := qb)
    (β₀ := β₀) (ph := ph) (pf := pf) h1a (by linarith) hφ hY
  have hQ := eq_23_21 (ph := ph) (pf := pf) ha0 ha1 hφ
  refine (((hC.sub hCs).const_mul σ).sub hQ).congr_deriv ?_
  ring

/-- AKMM, (23.27), p. 718: the bond term `2σ(bbm − β bb)` equals the printed
`2σβ⁻¹[b̃_{t−1} − βb̃_t]` when the positions are measured at steady-state value,
`b̃ = β·bb`. -/
theorem loglin_bond_printed {σ β₀ bb bbm : ℝ} (hβ : β₀ ≠ 0) :
    2 * σ * (bbm - β₀ * bb) = 2 * σ * β₀⁻¹ * (β₀ * bbm - β₀ * (β₀ * bb)) := by
  field_simp

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Equilibrium terms of trade: complete markets and financial autarky

AKMM, §23.3.4–§23.3.5, pp. 716–719, (23.28)–(23.29), footnotes 21, 28, 30 and 31, and
Figure 23.6.

Relative demand (23.24) meets the vertical relative supply `Ŷ_H − Ŷ*_F` of the endowment
economy. We prove:

* (23.28): under complete markets (`Ŵ = 0`)
  `T̂ = σ/[4a(1 − a)(σφ − 1) + 1] · (Ŷ_H − Ŷ*_F)`, with a positive denominator for every
  `0 < a < 1` (`eq_23_28`, `tot_cm_denom_pos`); a relative output boom worsens the terms of trade
  and depreciates the real exchange rate (`tot_cm_worsen`); the coefficient is strictly decreasing
  in `φ`, vanishes as `φ → ∞` and tends to its supremum `σ/(2a − 1)²` as `φ → 0`
  (`tot_cm_coef_strictAntiOn`, `tot_cm_tendsto_atTop`, `tot_cm_tendsto_zero`, `tot_cm_coef_lt`);
* (23.29): under financial autarky `T̂ = (Ŷ_H − Ŷ*_F)/[1 − 2a(1 − φ)]`, and the terms of trade
  worsen after a home boom iff `φ > 1 − 1/(2a)` (`eq_23_29`, `tot_fa_worsen_iff`);
* Cole–Obstfeld: at `σ = φ = 1` both coefficients are one, and with no home bias both are `1/φ`
  (`tot_cole_obstfeld`, `tot_no_home_bias`); fn 31 (`fn_31`);
* the slope of the relative demand schedule in Figure 23.6 (`tot_rd_slope`, correcting p. 717);
* the Backus–Smith patterns: perfect correlation under complete markets (fn 21,
  `tot_cm_backus_smith`) and the negative co-movement under autarky with a low elasticity
  (`tot_fa_backus_smith`);
* footnote 30: as `a_H → 1`, `Q̂ → (Ŷ_H − Ŷ*_F)/(2φ − 1)` (`fn_30`).

The book's (23.28)–(23.29) print the relative supply as `Ŷ_H − Ŷ*_H`; it is `Ŷ_H − Ŷ*_F`
(see `docs/corrections.md`).
-/

namespace AKMM.InternationalMacro

open Filter Topology Set

/-- AKMM, p. 718: the denominator `4a(1 − a)(σφ − 1) + 1` of (23.28) is positive (the book says
for `a ∈ (1/2, 1)`; it holds for every `a ∈ (0, 1)`). -/
theorem tot_cm_denom_pos {a σ φ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) (hφ : 0 < φ) :
    0 < 4 * a * (1 - a) * (σ * φ - 1) + 1 := by
  have h1a : 0 < 1 - a := by linarith
  have : 0 < 4 * a * (1 - a) * (σ * φ) := by positivity
  nlinarith [sq_nonneg (2 * a - 1)]

/-- **(23.28)**, AKMM p. 718: under complete markets (`Ŵ = 0`), equating relative demand (23.24)
with relative supply `Ŷ_H − Ŷ*_F` gives
`T̂ = σ/[4a(1 − a)(σφ − 1) + 1] · (Ŷ_H − Ŷ*_F)`. -/
theorem eq_23_28 {a σ φ y ys τ W D : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) (hφ : 0 < φ)
    (h24 : D = σ⁻¹ * (2 * a - 1) * W + σ⁻¹ * (4 * a * (1 - a) * (σ * φ - 1) + 1) * τ)
    (hW : W = 0) (hclear : D = y - ys) :
    τ = σ / (4 * a * (1 - a) * (σ * φ - 1) + 1) * (y - ys) := by
  have hd := tot_cm_denom_pos ha0 ha1 hσ hφ
  rw [hW, hclear] at h24
  field_simp
  field_simp at h24
  linarith

/-- AKMM, p. 718: under complete markets, "in equilibrium, the home TOT unambiguously worsen
and the RER depreciates with an increase in relative domestic productivity": if
`Ŷ_H > Ŷ*_F` then `T̂ > 0` and, with home bias `a > 1/2`, `Q̂ = (2a − 1)T̂ > 0`. -/
theorem tot_cm_worsen {a σ φ y ys : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) (hφ : 0 < φ)
    (hy : ys < y) :
    0 < σ / (4 * a * (1 - a) * (σ * φ - 1) + 1) * (y - ys) ∧
      (1 / 2 < a → 0 < (2 * a - 1) * (σ / (4 * a * (1 - a) * (σ * φ - 1) + 1) * (y - ys))) := by
  have hd := tot_cm_denom_pos ha0 ha1 hσ hφ
  have h1 : 0 < σ / (4 * a * (1 - a) * (σ * φ - 1) + 1) * (y - ys) :=
    mul_pos (div_pos hσ hd) (by linarith)
  exact ⟨h1, fun h => mul_pos (by linarith) h1⟩

/-- AKMM, p. 718: "the coefficient on the productivity differential vanishes when goods are
highly substitutable and is largest as `φ` approaches zero": the coefficient of (23.28) is
strictly decreasing in `φ > 0`. -/
theorem tot_cm_coef_strictAntiOn {a σ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) :
    StrictAntiOn (fun φ => σ / (4 * a * (1 - a) * (σ * φ - 1) + 1)) (Ioi 0) := by
  intro φ₁ h₁ φ₂ h₂ h12
  simp only [mem_Ioi] at h₁ h₂
  have d1 := tot_cm_denom_pos ha0 ha1 hσ h₁
  have d2 := tot_cm_denom_pos ha0 ha1 hσ h₂
  have h1a : 0 < 1 - a := by linarith
  apply div_lt_div_of_pos_left hσ d1
  have : 0 < 4 * a * (1 - a) * σ := by positivity
  nlinarith

/-- AKMM, p. 718: the coefficient of (23.28) tends to `0` as `φ → ∞`. -/
theorem tot_cm_tendsto_atTop {a σ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) :
    Tendsto (fun φ => σ / (4 * a * (1 - a) * (σ * φ - 1) + 1)) atTop (𝓝 0) := by
  have h1a : 0 < 1 - a := by linarith
  have hk : 0 < 4 * a * (1 - a) * σ := by positivity
  have hden : Tendsto (fun φ => 4 * a * (1 - a) * (σ * φ - 1) + 1) atTop atTop := by
    have e : (fun φ => 4 * a * (1 - a) * (σ * φ - 1) + 1)
        = fun φ => 4 * a * (1 - a) * σ * φ + (1 - 4 * a * (1 - a)) := by
      funext φ; ring
    rw [e]
    exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hk)
  exact hden.const_div_atTop σ

/-- AKMM, p. 718: with home bias (`a ≠ 1/2`) the coefficient of (23.28) tends to
`σ/(2a − 1)²` as `φ → 0⁺`. -/
theorem tot_cm_tendsto_zero {a σ : ℝ} (ha : a ≠ 1 / 2) :
    Tendsto (fun φ => σ / (4 * a * (1 - a) * (σ * φ - 1) + 1)) (𝓝[>] 0)
      (𝓝 (σ / (2 * a - 1) ^ 2)) := by
  have hne : (2 * a - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by intro h; apply ha; linarith)
  have hc : ContinuousAt (fun φ => σ / (4 * a * (1 - a) * (σ * φ - 1) + 1)) 0 := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    simp only [mul_zero, zero_sub]
    intro h; apply hne; linarith
  have hv : σ / (4 * a * (1 - a) * (σ * 0 - 1) + 1) = σ / (2 * a - 1) ^ 2 := by ring_nf
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- AKMM, p. 718: the limit `σ/(2a − 1)²` is the supremum of the coefficient of (23.28) over
`φ > 0`, not attained: the coefficient is strictly below it for every `φ > 0`. -/
theorem tot_cm_coef_lt {a σ φ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ha : a ≠ 1 / 2) (hσ : 0 < σ)
    (hφ : 0 < φ) :
    σ / (4 * a * (1 - a) * (σ * φ - 1) + 1) < σ / (2 * a - 1) ^ 2 := by
  have hd := tot_cm_denom_pos ha0 ha1 hσ hφ
  have hsq : 0 < (2 * a - 1) ^ 2 := by
    have : 2 * a - 1 ≠ 0 := by intro h; apply ha; linarith
    positivity
  apply div_lt_div_of_pos_left hσ hsq
  have h1a : 0 < 1 - a := by linarith
  have : 0 < 4 * a * (1 - a) * (σ * φ) := by positivity
  nlinarith

/-- **(23.29)**, AKMM p. 718: under financial autarky, the relative demand schedule (23.26)
`D̂_H − D̂*_F = [1 − 2a(1 − φ)]T̂` meets relative supply at
`T̂ = (Ŷ_H − Ŷ*_F)/[1 − 2a(1 − φ)]`, whenever the denominator is nonzero. -/
theorem eq_23_29 {a φ y ys τ D : ℝ} (hden : 1 - 2 * a * (1 - φ) ≠ 0)
    (h26 : D = (1 - 2 * a * (1 - φ)) * τ) (hclear : D = y - ys) :
    τ = (y - ys) / (1 - 2 * a * (1 - φ)) := by
  rw [eq_div_iff hden]
  linarith

/-- AKMM, p. 719: when `1 − 2a(1 − φ) = 0` the autarky equilibrium (23.26) with
`D̂ = Ŷ` has no solution `T̂` unless `Ŷ_H = Ŷ*_F` (a degenerate case the book does not treat). -/
theorem tot_fa_degenerate {a φ y ys τ D : ℝ} (hden : 1 - 2 * a * (1 - φ) = 0)
    (h26 : D = (1 - 2 * a * (1 - φ)) * τ) (hclear : D = y - ys) : y = ys := by
  rw [hden, zero_mul] at h26
  linarith

/-- AKMM, p. 719: the denominator of (23.29) is positive iff `φ > φ̃ = 1 − 1/(2a_H)`. -/
theorem tot_fa_threshold {a φ : ℝ} (ha0 : 0 < a) :
    0 < 1 - 2 * a * (1 - φ) ↔ 1 - 1 / (2 * a) < φ := by
  have h2a : 0 < 2 * a := by positivity
  have key : 1 - φ < 1 / (2 * a) ↔ (1 - φ) * (2 * a) < 1 := lt_div_iff₀ h2a
  constructor
  · intro h
    have : 1 - φ < 1 / (2 * a) := key.mpr (by linarith)
    linarith
  · intro h
    have := key.mp (by linarith)
    linarith

/-- AKMM, p. 719: under financial autarky "the home TOT worsen following a domestic productivity
improvement if and only if `φ > 1 − 1/(2a_H)`": for `Ŷ_H > Ŷ*_F` the equilibrium `T̂` of (23.29)
is positive iff `φ > 1 − 1/(2a)`. -/
theorem tot_fa_worsen_iff {a φ y ys : ℝ} (ha0 : 0 < a) (hden : 1 - 2 * a * (1 - φ) ≠ 0)
    (hy : ys < y) :
    0 < (y - ys) / (1 - 2 * a * (1 - φ)) ↔ 1 - 1 / (2 * a) < φ := by
  rw [← tot_fa_threshold ha0]
  have hy' : 0 < y - ys := by linarith
  constructor
  · intro h
    by_contra hn
    have hneg : 1 - 2 * a * (1 - φ) < 0 := lt_of_le_of_ne (not_lt.mp hn) hden
    exact absurd h (not_lt.mpr (div_nonpos_of_nonneg_of_nonpos hy'.le hneg.le))
  · intro h
    exact div_pos hy' h

/-- **Cole–Obstfeld**, AKMM p. 719: at `σ = φ = 1` the equilibrium terms of trade coincide under
complete markets (23.28) and financial autarky (23.29): both coefficients equal one. -/
theorem tot_cole_obstfeld (a : ℝ) :
    1 / (4 * a * (1 - a) * (1 * 1 - 1) + 1) = 1 ∧ 1 / (1 - 2 * a * (1 - 1)) = (1 : ℝ) := by
  constructor <;> ring

/-- AKMM, p. 716: with no home bias (`a = 1/2`) substitution is the only channel whatever the
risk sharing: the complete-markets and autarky coefficients of (23.28)–(23.29) both equal
`1/φ`, and the wealth coefficient `(2a − 1)/σ` of (23.24) vanishes. -/
theorem tot_no_home_bias {σ φ : ℝ} (hσ : σ ≠ 0) (hφ : φ ≠ 0) :
    σ / (4 * (1 / 2) * (1 - 1 / 2) * (σ * φ - 1) + 1) = 1 / φ ∧
      1 / (1 - 2 * (1 / 2) * (1 - φ)) = 1 / φ ∧ σ⁻¹ * (2 * (1 / 2) - 1) = 0 := by
  refine ⟨?_, ?_, by ring⟩
  · rw [show 4 * (1 / 2 : ℝ) * (1 - 1 / 2) * (σ * φ - 1) + 1 = σ * φ by ring]
    field_simp
  · ring_nf

/-- **Footnote 31**, AKMM p. 719: with `φ = σ = 1` the terms of trade move one-for-one with
relative output, so the relative value of national outputs `p_H Y_H/(p_F Y*_F)` is constant to
first order: `Ŷ_H − Ŷ*_F − T̂ = 0`. -/
theorem fn_31 {a y ys τ : ℝ} (h : τ = 1 / (4 * a * (1 - a) * (1 * 1 - 1) + 1) * (y - ys)) :
    y - ys - τ = 0 := by
  rw [h]; ring

/-- **Footnote 21**, AKMM p. 710: under complete markets the wealth gap (23.22) is zero, so
`Q̂ = σ(Ĉ − Ĉ*)`: the real exchange rate and relative consumption are perfectly positively
correlated. -/
theorem tot_cm_backus_smith {σ c cs q W : ℝ} (h22 : W = σ * (c - cs) - q) (hW : W = 0) :
    q = σ * (c - cs) := by
  linarith

/-- AKMM, p. 717: under financial autarky with home bias (`a > 1/2`) and a low elasticity
(`φ < 1 − 1/(2a)`), a home output boom `Ŷ_H > Ŷ*_F` strengthens the terms of trade (`T̂ < 0`),
appreciates the real exchange rate (`Q̂ < 0`) and raises relative consumption
(`Ĉ − Ĉ* > 0`): the negative real exchange rate–relative consumption co-movement of the
Backus–Smith puzzle. -/
theorem tot_fa_backus_smith {a φ y ys : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hbias : 1 / 2 < a)
    (hlow : φ < 1 - 1 / (2 * a)) (hy : ys < y) :
    (y - ys) / (1 - 2 * a * (1 - φ)) < 0 ∧
      (2 * a - 1) * ((y - ys) / (1 - 2 * a * (1 - φ))) < 0 ∧
      0 < y - ys - 2 * (1 - a) * ((y - ys) / (1 - 2 * a * (1 - φ))) := by
  have hneg : 1 - 2 * a * (1 - φ) < 0 := by
    by_contra h
    have h2a : 0 < 2 * a := by positivity
    have : 1 - φ ≤ 1 / (2 * a) := by rw [le_div_iff₀ h2a]; linarith
    linarith
  have hT : (y - ys) / (1 - 2 * a * (1 - φ)) < 0 := div_neg_of_pos_of_neg (by linarith) hneg
  have h1a : 0 < 1 - a := by linarith
  refine ⟨hT, mul_neg_of_pos_of_neg (by linarith) hT, ?_⟩
  have : 0 < -(2 * (1 - a) * ((y - ys) / (1 - 2 * a * (1 - φ)))) := by
    have := mul_pos (by positivity : (0 : ℝ) < 2 * (1 - a)) (neg_pos.mpr hT)
    linarith
  linarith

/-- AKMM, p. 717, Figure 23.6 (corrected): in the space `{log(Y_H/Y*_F), log(1/T)}` the autarky
relative demand schedule `Ŷ = k · T̂` with `k = 1 − 2a(1 − φ) ≠ 0` has slope `−1/k`: it slopes
**downward** when `φ > 1 − 1/(2a)` (`k > 0`) and upward when `φ < 1 − 1/(2a)` (`k < 0`). For
two points on the schedule with `Ŷ₁ < Ŷ₂`, `log(1/T)` falls iff `k > 0`. -/
theorem tot_rd_slope {k y₁ y₂ τ₁ τ₂ : ℝ} (hk : k ≠ 0) (h₁ : y₁ = k * τ₁) (h₂ : y₂ = k * τ₂)
    (hy : y₁ < y₂) : -τ₂ < -τ₁ ↔ 0 < k := by
  constructor
  · intro h
    by_contra hn
    have hk' : k < 0 := lt_of_le_of_ne (not_lt.mp hn) hk
    nlinarith
  · intro hk'
    nlinarith

/-- AKMM, p. 717: under financial autarky "the equilibrium relative demand for the home goods
will be increasing in its relative price (`∂(D̂_H − D̂*_F)/∂T̂ < 0`) with an elasticity
`φ < 1 − 1/(2a_H)`", and decreasing in it for `φ > 1 − 1/(2a_H)` (in particular when PPP holds,
`a = 1/2`, where the coefficient is `φ`). -/
theorem tot_rd_coefficient {a φ : ℝ} (ha0 : 0 < a) :
    (1 - 2 * a * (1 - φ) < 0 ↔ φ < 1 - 1 / (2 * a)) ∧ 1 - 2 * (1 / 2) * (1 - φ) = φ := by
  have h2a : 0 < 2 * a := by positivity
  have key : 1 / (2 * a) < 1 - φ ↔ 1 < (1 - φ) * (2 * a) := div_lt_iff₀ h2a
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by ring⟩
  · have := key.mpr (by linarith)
    linarith
  · have := key.mp (by linarith)
    linarith

/-- **Footnote 30**, AKMM p. 717: under financial autarky `Q̂ = (2a − 1)T̂` with
`T̂ = (Ŷ_H − Ŷ*_F)/[1 − 2a(1 − φ)]`; as `a_H → 1` the coefficient of `Ŷ_H − Ŷ*_F` in `Q̂` tends
to `1/(2φ − 1)` (for `φ ≠ 1/2`). The footnote prints `Q_t` for `Q̂_t`. -/
theorem fn_30 {φ : ℝ} (hφ : φ ≠ 1 / 2) :
    Tendsto (fun a => (2 * a - 1) / (1 - 2 * a * (1 - φ))) (𝓝[<] 1) (𝓝 (1 / (2 * φ - 1))) := by
  have hne : 1 - 2 * 1 * (1 - φ) ≠ 0 := by intro h; apply hφ; linarith
  have hc : ContinuousAt (fun a => (2 * a - 1) / (1 - 2 * a * (1 - φ))) 1 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hne
  have hv : (2 * 1 - 1) / (1 - 2 * 1 * (1 - φ)) = 1 / (2 * φ - 1) := by ring_nf
  rw [← hv]
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The trade balance, notional flows and the general-equilibrium Marshall–Lerner condition

AKMM, (23.14)–(23.15), p. 711, and §23.3.5, (23.30)–(23.31), pp. 719–720.

* Net exports (exports minus imports) in units of home consumption,
  `(p_H c*_H − p_F c_F)/P`, equal `p_H Y_H/P − C` under goods-market clearing and the budget
  identity (`nx_identity`). The book's (23.14) defines the trade balance with the opposite sign,
  `(p_F c_F − p_H c*_H)/P` (imports minus exports) (`eq_23_14_sign`); balanced trade (23.15) is
  unaffected (`eq_23_15`).
* Linearised, `n̂x = Ŷ_H − (1 − a)T̂ − Ĉ` (an exact derivative, `nx_loglin`).
* (23.30): under complete markets the notional asset `B̂_t − β⁻¹B̂_{t−1} = n̂x_t` moves by
  `(1 − a)σ⁻¹[2a(σφ − 1) + 1 − σ]T̂` (`eq_23_30`); from the steady state, a terms-of-trade
  worsening produces positive net exports iff (23.31) `φ > 1/σ + (1/(2a))(1 − 1/σ)`
  (`eq_23_31`), which is `φ > 1` with log utility (`nx_log_utility`).
* The classic **Marshall–Lerner** condition, proved with Obstfeld–Rogoff's
  `Stability.marshall_lerner` for the Armington import demands at given consumption: the trade
  balance improves with a terms-of-trade worsening iff the import elasticities `ζ = ζ* = aφ` sum
  to more than one, i.e. `φ > 1/(2a)` (`nx_marshall_lerner`); the general-equilibrium threshold
  (23.31) tends to this partial-equilibrium one as `σ → ∞` (`nx_ml_limit`).
-/

namespace AKMM.InternationalMacro

open Real Filter Topology
open ObstfeldRogoff.RealExchangeRate.CESIndex (cesPrice cesPrice_pos cesPrice_logDeriv_at_one)
open ObstfeldRogoff.StickyPriceModels (cesDemand)
open ObstfeldRogoff.IntertemporalTrade.Stability (zeta zetaStar marshall_lerner
  hasDerivAt_netImports)

/-- AKMM, p. 711 and (23.14): with goods-market clearing `Y_H = c_H + c*_H` and the budget
identity `PC = p_H c_H + p_F c_F`, net exports (exports `p_H c*_H` minus imports `p_F c_F`, in
units of home consumption) equal `p_H Y_H/P − C`. -/
theorem nx_identity {P C pH pF cH cF csH Y : ℝ} (hP : P ≠ 0) (hY : Y = cH + csH)
    (hbud : P * C = pH * cH + pF * cF) : (pH * csH - pF * cF) / P = pH * Y / P - C := by
  rw [hY]
  field_simp
  linarith

/-- AKMM, (23.14), p. 711 (sign corrected): the printed "trade balance … value of exports minus
value of imports", `(p_F/P)c_F − (p_H/P)c*_H`, is imports minus exports, the negative of net
exports `(p_H/P)c*_H − (p_F/P)c_F`. -/
theorem eq_23_14_sign (P pH pF cF csH : ℝ) :
    pF / P * cF - pH / P * csH = -(pH / P * csH - pF / P * cF) := by
  ring

/-- **(23.15)**, AKMM p. 711: balanced trade `T c_F − c*_H = 0` (`T = p_F/p_H`) holds iff
`C = (p_H/P) Y_H`, given `Y_H = c_H + c*_H` and `PC = p_H c_H + p_F c_F`. -/
theorem eq_23_15 {P C pH pF cH cF csH Y : ℝ} (hP : 0 < P) (hpH : 0 < pH) (hY : Y = cH + csH)
    (hbud : P * C = pH * cH + pF * cF) : pF / pH * cF - csH = 0 ↔ C = pH / P * Y := by
  rw [hY]
  constructor
  · intro h
    have h' : pF * cF = pH * csH := by
      field_simp at h; linarith
    field_simp
    linarith
  · intro h
    have h' : P * C = pH * (cH + csH) := by rw [h]; field_simp
    have : pF * cF = pH * csH := by linarith
    field_simp
    linarith

/-- AKMM, p. 719: net exports `(p_H Y_H/P − C)/Ȳ` linearise to `Ŷ_H − (1 − a)T̂ − Ĉ` (exact
derivative along the ray of `LogLinear`). -/
theorem nx_loglin {a φ ph pf y c Ybar : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hY : 0 < Ybar) :
    HasDerivAt (fun t => (exp (t * ph) * (Ybar * exp (t * y)) / loglinP a φ ph pf t
        - Ybar * exp (t * c)) / Ybar) (y - (1 - a) * (pf - ph) - c) 0 := by
  have hI := loglin_hasDerivAt_of_log
    (fun t => div_pos (mul_pos (exp_pos _) (mul_pos hY (exp_pos _))) (loglinP_pos ha0 ha1 t))
    (loglin_autarky_cons (ph := ph) (pf := pf) (y := y) ha0 ha1 hφ hY)
  have hC : HasDerivAt (fun t => Ybar * exp (t * c)) (Ybar * c) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).exp.const_mul Ybar
  have h := (hI.sub hC).div_const Ybar
  refine h.congr_deriv ?_
  simp only [zero_mul, exp_zero, mul_one, loglinP_zero, div_one]
  field_simp

/-- **(23.30)**, AKMM p. 719: under complete markets — risk sharing `σ(Ĉ − Ĉ*) = Q̂` with
`Q̂ = (2a − 1)T̂`, world consumption `Ĉ + Ĉ* = Ŷ_H + Ŷ*_F`, the equilibrium terms of trade
(23.28) `σ(Ŷ_H − Ŷ*_F) = [4a(1 − a)(σφ − 1) + 1]T̂` — the notional foreign asset accumulating net
exports, `B̂_t − β⁻¹B̂_{t−1} = Ŷ_H − (1 − a)T̂ − Ĉ`, satisfies
`B̂_t − β⁻¹B̂_{t−1} = (1 − a)σ⁻¹[2a(σφ − 1) + 1 − σ]T̂`. -/
theorem eq_23_30 {a σ φ β c cs y ys τ q B Bm : ℝ} (hσ : σ ≠ 0)
    (hrs : σ * (c - cs) = q) (h21 : q = (2 * a - 1) * τ) (hworld : c + cs = y + ys)
    (h28 : σ * (y - ys) = (4 * a * (1 - a) * (σ * φ - 1) + 1) * τ)
    (hB : B - β⁻¹ * Bm = y - (1 - a) * τ - c) :
    B - β⁻¹ * Bm = (1 - a) * σ⁻¹ * (2 * a * (σ * φ - 1) + 1 - σ) * τ := by
  rw [hB]
  set s := σ⁻¹ with hsdef
  have hs : σ * s = 1 := mul_inv_cancel₀ hσ
  linear_combination (s / 2) * h28 - (s / 2) * hrs - (s / 2) * h21 - (1 / 2) * hworld
    + (-(1 / 2) * ((y - ys) - (c - cs)) + (1 - a) * τ) * hs

/-- **(23.31)**, AKMM p. 719: starting from the steady state (`B̂_{t−1} = 0`), a terms-of-trade
worsening `T̂ > 0` makes net exports positive (`B̂_t > 0`: capital flows from home to foreign)
iff `φ > 1/σ + (1/(2a))(1 − 1/σ)`. -/
theorem eq_23_31 {a σ φ τ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < (1 - a) * σ⁻¹ * (2 * a * (σ * φ - 1) + 1 - σ) * τ ↔
      1 / σ + 1 / (2 * a) * (1 - 1 / σ) < φ := by
  have h1a : 0 < 1 - a := by linarith
  have hk : 0 < (1 - a) * σ⁻¹ := by positivity
  have e : 1 / σ + 1 / (2 * a) * (1 - 1 / σ) = (2 * a - 1 + σ) / (2 * a * σ) := by
    field_simp
    ring
  rw [e, div_lt_iff₀ (by positivity)]
  constructor
  · intro h
    have h2 : 0 < 2 * a * (σ * φ - 1) + 1 - σ := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos hk.le (not_lt.mp hn)
      nlinarith
    nlinarith
  · intro h
    have h2 : 0 < 2 * a * (σ * φ - 1) + 1 - σ := by nlinarith
    positivity

/-- AKMM, p. 720: "with log utility (`σ = 1`), the condition will boil down to gross
substitutability between home and foreign goods (`φ > 1`)". -/
theorem nx_log_utility (a φ : ℝ) :
    1 / 1 + 1 / (2 * a) * (1 - 1 / 1) < φ ↔ 1 < φ := by
  norm_num

/-- AKMM, p. 720: as `σ → ∞` the general-equilibrium threshold of (23.31) tends to `1/(2a)`,
the partial-equilibrium Marshall–Lerner threshold of `nx_marshall_lerner`. -/
theorem nx_ml_limit (a : ℝ) :
    Tendsto (fun σ : ℝ => 1 / σ + 1 / (2 * a) * (1 - 1 / σ)) atTop (𝓝 (1 / (2 * a))) := by
  have h : Tendsto (fun σ : ℝ => 1 / σ) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h2 : Tendsto (fun σ : ℝ => 1 / (2 * a) * (1 - 1 / σ)) atTop
      (𝓝 (1 / (2 * a) * (1 - 0))) := (tendsto_const_nhds.sub h).const_mul _
  have := h.add h2
  simpa using this

/-- The Armington import demand of the home country, `c_F(T) = (1 − a)(T/P)^{−φ}C` with
`p_H = 1`, `P = cesPrice a φ T`. -/
noncomputable def nxImportsHome (a φ C T : ℝ) : ℝ := (1 - a) * cesDemand φ T (cesPrice a φ T) C

/-- The Armington import demand of the foreign country (its demand for the home good),
`c*_H(T) = (1 − a)(1/P*)^{−φ}C*` with `P* = cesPrice (1 − a) φ T`. -/
noncomputable def nxImportsForeign (a φ Cs T : ℝ) : ℝ :=
  (1 - a) * cesDemand φ 1 (cesPrice (1 - a) φ T) Cs

/-- The log-derivatives of the Armington import demands at `T = 1`: `d log c_F/dT = −aφ`,
`d log c*_H/dT = aφ` (consumption held fixed). -/
theorem nx_imports_hasDerivAt {a φ C Cs : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1)
    (hC : 0 < C) (hCs : 0 < Cs) :
    HasDerivAt (nxImportsHome a φ C) (-(a * φ) * ((1 - a) * C)) 1 ∧
      HasDerivAt (nxImportsForeign a φ Cs) (a * φ * ((1 - a) * Cs)) 1 := by
  have h1a : 0 < 1 - a := by linarith
  have hP1 := cesPrice_logDeriv_at_one (θ := φ) ha0 ha1 hφ
  have hP2 := cesPrice_logDeriv_at_one (θ := φ) h1a (by linarith) hφ
  have hpos : ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ T : ℝ, 0 < T → 0 < cesPrice γ φ T :=
    fun γ h0 h1 T hT => cesPrice_pos h0 h1 hT
  have hone : ∀ γ : ℝ, cesPrice γ φ 1 = 1 := by intro γ; simp [cesPrice]
  -- home imports: `log c_F = log(1 − a) − φ(log T − log P) + log C` near `T = 1`
  have hlogF : HasDerivAt (fun T => log (1 - a) + (-φ * (log T - log (cesPrice a φ T)) + log C))
      (0 + (-φ * (1 - (1 - a)) + 0)) 1 := by
    refine (hasDerivAt_const _ _).add (((hasDerivAt_log one_ne_zero).sub hP1 |>.const_mul (-φ)
      |>.congr_deriv (by simp)).add (hasDerivAt_const _ _))
  have hlogH : HasDerivAt (fun T => log (1 - a) + (-φ * (log 1 - log (cesPrice (1 - a) φ T))
      + log Cs)) (0 + (-φ * (0 - (1 - (1 - a))) + 0)) 1 := by
    refine (hasDerivAt_const _ _).add ((((hasDerivAt_const _ _).sub hP2).const_mul (-φ)).add
      (hasDerivAt_const _ _))
  have eF : ∀ᶠ T in 𝓝 (1 : ℝ), nxImportsHome a φ C T
      = exp (log (1 - a) + (-φ * (log T - log (cesPrice a φ T)) + log C)) := by
    filter_upwards [Ioi_mem_nhds one_pos] with T hT
    have hP := hpos a ha0 ha1 T hT
    unfold nxImportsHome cesDemand
    rw [exp_add, exp_add, exp_log h1a, exp_log hC, ← log_div (ne_of_gt hT) hP.ne',
      mul_comm (-φ), exp_mul, exp_log (div_pos hT hP)]
  have eH : ∀ᶠ T in 𝓝 (1 : ℝ), nxImportsForeign a φ Cs T
      = exp (log (1 - a) + (-φ * (log 1 - log (cesPrice (1 - a) φ T)) + log Cs)) := by
    filter_upwards [Ioi_mem_nhds one_pos] with T hT
    have hP := hpos (1 - a) h1a (by linarith) T hT
    unfold nxImportsForeign cesDemand
    rw [exp_add, exp_add, exp_log h1a, exp_log hCs, ← log_div one_ne_zero hP.ne',
      mul_comm (-φ), exp_mul, exp_log (div_pos one_pos hP)]
  constructor
  · have := hlogF.exp.congr_of_eventuallyEq eF
    refine this.congr_deriv ?_
    rw [hone, log_one, sub_zero, mul_zero, zero_add, exp_add, exp_log h1a, exp_log hC]
    ring
  · have := hlogH.exp.congr_of_eventuallyEq eH
    refine this.congr_deriv ?_
    rw [hone, log_one, sub_zero, mul_zero, zero_add, exp_add, exp_log h1a, exp_log hCs]
    ring

/-- **The Marshall–Lerner condition** for the Armington model (AKMM p. 720, "the classic
Marshall–Lerner condition (on exports and imports elasticities)"), via Obstfeld–Rogoff's
`Stability.marshall_lerner`: at the symmetric point `T = 1`, `C = C*` (balanced trade), holding
consumption fixed, the home trade balance in foreign-good units `c*_H(T)/T − c_F(T)` has
derivative `δ` in `T` (written `T = 1 + r`), and it rises with a terms-of-trade worsening iff
the import elasticities `ζ = −T c_F′/c_F = aφ` and `ζ* = T c*_H′/c*_H = aφ` sum to more than one,
i.e. `2aφ > 1`. -/
theorem nx_marshall_lerner {a φ C : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) (hC : 0 < C) :
    ∃ δ : ℝ, HasDerivAt (fun r => nxImportsForeign a φ C (1 + r) / (1 + r)
        - nxImportsHome a φ C (1 + r)) δ 0 ∧
      (0 < δ ↔ 1 < zeta 0 ((1 - a) * C) (-(a * φ) * ((1 - a) * C))
        + zetaStar 0 ((1 - a) * C) (a * φ * ((1 - a) * C))) ∧
      zeta 0 ((1 - a) * C) (-(a * φ) * ((1 - a) * C))
        + zetaStar 0 ((1 - a) * C) (a * φ * ((1 - a) * C)) = 2 * a * φ := by
  have h1a : 0 < 1 - a := by linarith
  obtain ⟨hF, hH⟩ := nx_imports_hasDerivAt (C := C) (Cs := C) ha0 ha1 hφ hC hC
  have hF' : HasDerivAt (fun r => nxImportsHome a φ C (1 + r)) (-(a * φ) * ((1 - a) * C)) 0 := by
    exact HasDerivAt.comp_const_add 1 0 (by rw [add_zero]; exact hF)
  have hH' : HasDerivAt (fun r => nxImportsForeign a φ C (1 + r)) (a * φ * ((1 - a) * C)) 0 := by
    exact HasDerivAt.comp_const_add 1 0 (by rw [add_zero]; exact hH)
  have hone : ∀ γ : ℝ, cesPrice γ φ 1 = 1 := by intro γ; simp [cesPrice]
  have hIM1 : nxImportsHome a φ C (1 + 0) = (1 - a) * C := by
    simp [nxImportsHome, cesDemand, hone]
  have hIM2 : nxImportsForeign a φ C (1 + 0) = (1 - a) * C := by
    simp [nxImportsForeign, cesDemand, hone]
  have hd := hasDerivAt_netImports (r := 0) (by norm_num) hF' hH'
  refine ⟨_, hd, ?_, ?_⟩
  · rw [hIM2]
    exact marshall_lerner (by norm_num) (by positivity) (by norm_num)
  · unfold zeta zetaStar
    field_simp
    ring

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The production economy: relative supply and global output

AKMM, §23.4, (23.32)–(23.38), pp. 720–722.

* Labour supply (23.33) and the production function (23.34) are exact in logs
  (`eq_23_33`, `eq_23_34`). Profit maximisation gives the labour demand `W = α p_H Z L^{α−1}`,
  with profits `(1 − α) p_H Y` (`prod_labour_demand`, `prod_profit`); the printed (23.36)
  `w = (p_H/P) Z L^{α−1}` omits the factor `α` and is not a first-order condition when `α < 1`
  (`eq_23_36_printed_counterexample`), but the omitted constant does not affect the
  log-linearisation (`eq_23_36_log`). The product price moves as `p̂_H − P̂ = −(1 − a)T̂` at home
  and `p̂_F − P̂* = (1 − a)T̂` abroad (`prod_relPrice_loglin`).
* (23.37): relative supply
  `Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η)·(Ẑ − Ẑ*) − α/(1 − α + η)·(Ŵ + T̂)` (`eq_23_37`); under
  complete markets its slope `−α/(1 − α + η)` does not depend on openness `a` and the schedule is
  increasing in the relative price of home goods (`prod_cm_slope`).
* (23.38): under financial autarky
  `Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ − Ẑ*) + 2α(1 − a)(σ − 1)/(1 − α + η + ασ)·T̂`
  (`eq_23_38`), whose slope has the sign of `σ − 1` (`prod_fa_slope_sign`).
* Global output `Ŷ_H + Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ + Ẑ*)` under every financial market
  structure (`prod_global_output`).
-/

namespace AKMM.InternationalMacro

open Real

/-- **(23.33)**, AKMM p. 721, exact in logs: `C^{−σ} w = ζ L^η` iff
`−σ log C + log w = log ζ + η log L`. -/
theorem eq_23_33 {σ η ζ C w L : ℝ} (hC : 0 < C) (hw : 0 < w) (hζ : 0 < ζ) (hL : 0 < L) :
    C ^ (-σ) * w = ζ * L ^ η ↔ -σ * log C + log w = log ζ + η * log L := by
  have h1 : 0 < C ^ (-σ) * w := mul_pos (rpow_pos_of_pos hC _) hw
  have h2 : 0 < ζ * L ^ η := mul_pos hζ (rpow_pos_of_pos hL _)
  rw [← log_injOn_pos.eq_iff h1 h2, log_mul (rpow_pos_of_pos hC _).ne' hw.ne',
    log_mul hζ.ne' (rpow_pos_of_pos hL _).ne', log_rpow hC, log_rpow hL]

/-- **(23.34)**, AKMM p. 721, exact in logs: `log(Z L^α) = log Z + α log L`. -/
theorem eq_23_34 {α Z L : ℝ} (hZ : 0 < Z) (hL : 0 < L) :
    log (Z * L ^ α) = log Z + α * log L := by
  rw [log_mul hZ.ne' (rpow_pos_of_pos hL _).ne', log_rpow hL]

/-- AKMM, p. 721: the firm's profit `p_H Z L^α − W L` has derivative `α p_H Z L^{α−1} − W`, so at
an interior maximum the nominal wage equals the value of the marginal product,
`W = α p_H Z L^{α−1}` (the labour demand behind (23.36)). -/
theorem prod_labour_demand {α pH Z W L : ℝ} (hL : 0 < L)
    (hmax : IsLocalMax (fun L => pH * (Z * L ^ α) - W * L) L) :
    W = α * pH * Z * L ^ (α - 1) := by
  have hd : HasDerivAt (fun L => pH * (Z * L ^ α) - W * L)
      (pH * (Z * (α * L ^ (α - 1))) - W * 1) L :=
    (((hasDerivAt_rpow_const (Or.inl hL.ne')).const_mul Z).const_mul pH).sub
      ((hasDerivAt_id L).const_mul W)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- AKMM, p. 721: at the labour demand `W = α p_H Z L^{α−1}` profits are `(1 − α) p_H Y`, with
`Y = Z L^α`; they are zero (as the book states) only when `α = 1`. -/
theorem prod_profit {α pH Z L : ℝ} (hL : 0 < L) :
    pH * (Z * L ^ α) - α * pH * Z * L ^ (α - 1) * L = (1 - α) * (pH * (Z * L ^ α)) := by
  rw [mul_assoc (α * pH * Z), ← rpow_add_one hL.ne', sub_add_cancel]
  ring

/-- AKMM, (23.36), p. 721 (corrected): the printed labour demand `W = p_H Z L^{α−1}` (the
average, not the marginal, product) is not a first-order condition of profit maximisation when
`α < 1`: at that wage the derivative of profits is `(α − 1) p_H Z L^{α−1} ≠ 0`. -/
theorem eq_23_36_printed_counterexample {α pH Z L : ℝ} (hα : α < 1) (hpH : 0 < pH) (hZ : 0 < Z)
    (hL : 0 < L) :
    HasDerivAt (fun x => pH * (Z * x ^ α) - pH * Z * L ^ (α - 1) * x)
        ((α - 1) * pH * Z * L ^ (α - 1)) L ∧ (α - 1) * pH * Z * L ^ (α - 1) ≠ 0 := by
  constructor
  · have hd : HasDerivAt (fun x => pH * (Z * x ^ α) - pH * Z * L ^ (α - 1) * x)
        (pH * (Z * (α * L ^ (α - 1))) - pH * Z * L ^ (α - 1) * 1) L :=
      (((hasDerivAt_rpow_const (Or.inl hL.ne')).const_mul Z).const_mul pH).sub
        ((hasDerivAt_id' L).const_mul (pH * Z * L ^ (α - 1)))
    refine hd.congr_deriv ?_
    ring
  · have : 0 < pH * Z * L ^ (α - 1) := by positivity
    have h1 : α - 1 ≠ 0 := by linarith
    have e : (α - 1) * pH * Z * L ^ (α - 1) = (α - 1) * (pH * Z * L ^ (α - 1)) := by ring
    rw [e]
    exact mul_ne_zero h1 this.ne'

/-- AKMM, (23.36), p. 721: whether or not the constant `α` is included, the log of the real
labour demand `w = c (p_H/P) Z L^{α−1}` is `log c + log(p_H/P) + log Z + (α − 1) log L`, so the
log-linearised labour demand `ŵ = (p̂_H − P̂) + Ẑ − (1 − α)L̂` is the same. -/
theorem eq_23_36_log {α c rp Z L : ℝ} (hc : 0 < c) (hrp : 0 < rp) (hZ : 0 < Z) (hL : 0 < L) :
    log (c * rp * Z * L ^ (α - 1)) = log c + log rp + log Z + (α - 1) * log L := by
  rw [log_mul (by positivity) (rpow_pos_of_pos hL _).ne', log_mul (by positivity) hZ.ne',
    log_mul hc.ne' hrp.ne', log_rpow hL]

/-- AKMM, p. 721: the product price relative to the CPI moves by `p̂_H − P̂ = −(1 − a)T̂` at home
and `p̂_F − P̂* = (1 − a)T̂` abroad (exact derivatives along the ray of `LogLinear`). -/
theorem prod_relPrice_loglin {a φ ph pf : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hφ : φ ≠ 1) :
    HasDerivAt (fun t => log (exp (t * ph) / loglinP a φ ph pf t)) (-(1 - a) * (pf - ph)) 0 ∧
      HasDerivAt (fun t => log (exp (t * pf) / loglinP (1 - a) φ ph pf t))
        ((1 - a) * (pf - ph)) 0 := by
  have h1a : 0 < 1 - a := by linarith
  have hexp : ∀ k : ℝ, HasDerivAt (fun t => log (exp (t * k))) k 0 := by
    intro k; simpa using loglin_exp_ray 1 k one_pos
  constructor
  · have e : (fun t => log (exp (t * ph) / loglinP a φ ph pf t))
        = fun t => log (exp (t * ph)) - log (loglinP a φ ph pf t) := by
      funext t; rw [log_div (exp_pos _).ne' (loglinP_pos ha0 ha1 t).ne']
    rw [e]
    refine ((hexp ph).sub (loglinP_hasDerivAt (ph := ph) (pf := pf) ha0 ha1 hφ)).congr_deriv ?_
    ring
  · have e : (fun t => log (exp (t * pf) / loglinP (1 - a) φ ph pf t))
        = fun t => log (exp (t * pf)) - log (loglinP (1 - a) φ ph pf t) := by
      funext t; rw [log_div (exp_pos _).ne' (loglinP_pos h1a (by linarith) t).ne']
    rw [e]
    refine ((hexp pf).sub
      (loglinP_hasDerivAt (ph := ph) (pf := pf) h1a (by linarith) hφ)).congr_deriv ?_
    ring

/-- **(23.37)**, AKMM p. 721: combining, in each country, labour supply (23.33)
`ŵ − σĈ = ηL̂`, labour demand (23.36) `ŵ = (p̂ − P̂) + Ẑ − (1 − α)L̂` with
`p̂_H − P̂ = −(1 − a)T̂`, `p̂_F − P̂* = (1 − a)T̂`, and production (23.34) `Ŷ = Ẑ + αL̂`, and the
wealth gap (23.22) `Ŵ = σ(Ĉ − Ĉ*) − (2a − 1)T̂`, relative supply is
`Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η)·(Ẑ − Ẑ*) − α/(1 − α + η)·(Ŵ + T̂)`. -/
theorem eq_23_37 {a α η σ τ c cs w ws l ls z zs y ys W : ℝ} (hk : 1 - α + η ≠ 0)
    (hsup : w - σ * c = η * l) (hsupS : ws - σ * cs = η * ls)
    (hdem : w = -(1 - a) * τ + z - (1 - α) * l) (hdemS : ws = (1 - a) * τ + zs - (1 - α) * ls)
    (hy : y = z + α * l) (hyS : ys = zs + α * ls) (hW : W = σ * (c - cs) - (2 * a - 1) * τ) :
    y - ys = (1 + η) / (1 - α + η) * (z - zs) - α / (1 - α + η) * (W + τ) := by
  have hl : l = (z - σ * c - (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  have hls : ls = (zs - σ * cs + (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  rw [hy, hyS, hl, hls, hW]
  field_simp
  ring

/-- AKMM, p. 722: under complete markets (`Ŵ = 0`) the relative supply (23.37) is
`Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η)·(Ẑ − Ẑ*) − α/(1 − α + η)·T̂`; its slope in `T̂` is negative
(relative supply increases with the relative price of home goods `1/T`) and involves only
technology and labour-supply parameters, not the openness parameter `a`. -/
theorem prod_cm_slope {a α η σ τ c cs w ws l ls z zs y ys : ℝ} (hα : 0 < α) (hk : 0 < 1 - α + η)
    (hsup : w - σ * c = η * l) (hsupS : ws - σ * cs = η * ls)
    (hdem : w = -(1 - a) * τ + z - (1 - α) * l) (hdemS : ws = (1 - a) * τ + zs - (1 - α) * ls)
    (hy : y = z + α * l) (hyS : ys = zs + α * ls) (hW : σ * (c - cs) - (2 * a - 1) * τ = 0) :
    y - ys = (1 + η) / (1 - α + η) * (z - zs) - α / (1 - α + η) * τ ∧ -(α / (1 - α + η)) < 0 := by
  constructor
  · have := eq_23_37 hk.ne' hsup hsupS hdem hdemS hy hyS rfl
    rw [hW, zero_add] at this
    exact this
  · have := div_pos hα hk
    linarith

/-- **(23.38)**, AKMM p. 722: under financial autarky, substituting the autarky wealth gap
(23.25) `Ŵ = σ(Ŷ_H − Ŷ*_F − 2(1 − a)T̂) − (2a − 1)T̂` into (23.37) gives
`Ŷ_H − Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ − Ẑ*) + 2α(1 − a)(σ − 1)/(1 − α + η + ασ)·T̂`. -/
theorem eq_23_38 {a α η σ τ y ys z zs W : ℝ} (hk : 1 - α + η ≠ 0) (hk' : 1 - α + η + α * σ ≠ 0)
    (h37 : y - ys = (1 + η) / (1 - α + η) * (z - zs) - α / (1 - α + η) * (W + τ))
    (h25 : W = σ * (y - ys - 2 * (1 - a) * τ) - (2 * a - 1) * τ) :
    y - ys = (1 + η) / (1 - α + η + α * σ) * (z - zs)
      + 2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) * τ := by
  rw [h25] at h37
  field_simp at h37
  field_simp
  linear_combination h37

/-- AKMM, p. 722: under financial autarky the relative supply (23.38) is increasing in the
terms of trade `T̂` (decreasing in the relative price of home goods) iff `σ > 1`, decreasing in
`T̂` iff `σ < 1`, and independent of the terms of trade under log utility `σ = 1`. -/
theorem prod_fa_slope_sign {a α η σ : ℝ} (ha1 : a < 1) (hα : 0 < α)
    (hk' : 0 < 1 - α + η + α * σ) :
    (0 < 2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) ↔ 1 < σ) ∧
      (2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) < 0 ↔ σ < 1) ∧
      (σ = 1 → 2 * α * (1 - a) * (σ - 1) / (1 - α + η + α * σ) = 0) := by
  have h1a : 0 < 1 - a := by linarith
  have hc : 0 < 2 * α * (1 - a) := by positivity
  refine ⟨?_, ?_, fun h => by rw [h]; ring⟩
  · rw [div_pos_iff_of_pos_right hk']
    constructor
    · intro h; by_contra hn; nlinarith
    · intro h; nlinarith
  · rw [div_neg_iff]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · by_contra hn; nlinarith
    · intro h; right; exact ⟨by nlinarith, hk'⟩

/-- AKMM, p. 722: global output. Summing the two countries' labour-market and production
equations and imposing world resource balance `Ĉ + Ĉ* = Ŷ_H + Ŷ*_F` gives
`Ŷ_H + Ŷ*_F = (1 + η)/(1 − α + η + ασ)·(Ẑ + Ẑ*)`, whatever the structure of financial
markets (no wealth-gap term enters). -/
theorem prod_global_output {a α η σ τ c cs w ws l ls z zs y ys : ℝ} (hk : 1 - α + η ≠ 0)
    (hk' : 1 - α + η + α * σ ≠ 0)
    (hsup : w - σ * c = η * l) (hsupS : ws - σ * cs = η * ls)
    (hdem : w = -(1 - a) * τ + z - (1 - α) * l) (hdemS : ws = (1 - a) * τ + zs - (1 - α) * ls)
    (hy : y = z + α * l) (hyS : ys = zs + α * ls) (hworld : c + cs = y + ys) :
    y + ys = (1 + η) / (1 - α + η + α * σ) * (z + zs) := by
  have hl : l = (z - σ * c - (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  have hls : ls = (zs - σ * cs + (1 - a) * τ) / (1 - α + η) := by
    rw [eq_div_iff hk]; linarith
  have hsum : (1 - α + η) * (y + ys) = (1 + η) * (z + zs) - α * σ * (c + cs) := by
    rw [hy, hyS, hl, hls]
    field_simp
    ring
  rw [hworld] at hsum
  rw [div_mul_eq_mul_div, eq_div_iff hk']
  linear_combination hsum

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Complete markets: Euler equations, UIP and full risk sharing

AKMM, §23.3.2, (23.9)–(23.13) and (23.16), pp. 708–712.

Uncertainty is Miao's event tree `BPTree S` (histories are lists over a finite shock set, most
recent shock first, with strictly positive probabilities), so `Pr(s_{t+1}|sᵗ)` is
`T.pr (s :: h)/T.pr h` and `Eₜ` is `bp_condExp T 1`. A home Arrow–Debreu security bought at
history `h` pays one unit of currency in state `s` and costs `q h s`; with `𝓔 = 1` the foreign
securities pay the same currency and, by no arbitrage, cost the same (fn 19). With marginal
utility `μ = u′` (any function), we prove from the Euler equations (23.9) of the two countries:

* the riskless gross returns (23.10): `1/R = βEₜ[u′(C_{t+1})]/u′(C_t)` and its foreign analogue
  (`eq_23_10`), and the real UIP condition (23.11)
  `1/R* = βEₜ[u′(C_{t+1})Q_{t+1}/Q_t]/u′(C_t)` (`eq_23_11`);
* `R > 0` (`rs_return_pos`), but **not** the book's `R_t ≥ 1`: a deterministic economy with
  falling consumption has `R = 1/2` (`rs_return_lt_one`);
* state-by-state risk sharing (23.12) (`eq_23_12`), hence `u′(C_t)Q_t/u′(C*_t) = κ₀` at every
  history (`rs_kappa_const`), and under CRRA `Q_t = κ₀(C_t/C*_t)^σ` (23.13) (`eq_23_13`);
* the wealth gap (23.16) `W = χ*/χ = (C/C*)^σ/Q` (`eq_23_16`), constant and equal to `1/κ₀`
  under complete markets (`rs_wealth_const`).

The Euler equations are taken as hypotheses (first-order conditions of the household problem,
as in the book).
-/

namespace AKMM.InternationalMacro

open Real Finset
open Miao.CompleteMarkets (BPTree bp_condExp bp_condExp_succ bp_condExp_zero bp_detTree)

variable {S : Type*} [Fintype S]

/-- The conditional expectation `Eₜ[x_{t+1}]` at history `h` written out on the tree. -/
theorem rs_condExp_one (T : BPTree S) (x : List S → ℝ) (h : List S) :
    bp_condExp T 1 x h = ∑ s, T.pr (s :: h) / T.pr h * x (s :: h) := by
  rw [bp_condExp_succ]
  rfl

/-- **(23.10)**, AKMM p. 709: from the home Euler equations (23.9), the cost
`(1/P_t) Σ_s q_t(s) P_{t+1}(s)` of one sure unit of the home basket, `1/R_t`, equals
`βEₜ[u′(C_{t+1})]/u′(C_t)`; likewise abroad with the foreign Euler equations. -/
theorem eq_23_10 (T : BPTree S) {mu : ℝ → ℝ} {C P : List S → ℝ} {q : List S → S → ℝ} {β : ℝ}
    (h : List S) (hmu : mu (C h) ≠ 0) (hP : ∀ h, P h ≠ 0)
    (heuler : ∀ s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h)) :
    (∑ s, q h s * P (s :: h)) / P h = β * bp_condExp T 1 (fun h' => mu (C h')) h / mu (C h) := by
  rw [rs_condExp_one, Finset.sum_div, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e := heuler s
  have hPs := hP (s :: h)
  have hPh := hP h
  field_simp at e ⊢
  linear_combination e

/-- **(23.11)**, real UIP, AKMM p. 710: investing in foreign securities, which by no arbitrage
cost the same `q` (`𝓔 = 1`), the cost `(1/P*_t)Σ_s q_t(s)P*_{t+1}(s)` of a sure unit of the
foreign basket, `1/R*_t`, equals `βEₜ[u′(C_{t+1})Q_{t+1}/Q_t]/u′(C_t)` with `Q = P*/P`, using the
home Euler equations alone. -/
theorem eq_23_11 (T : BPTree S) {mu : ℝ → ℝ} {C P Ps : List S → ℝ} {q : List S → S → ℝ}
    {β : ℝ} (h : List S) (hmu : mu (C h) ≠ 0) (hP : ∀ h, P h ≠ 0) (hPs : ∀ h, Ps h ≠ 0)
    (heuler : ∀ s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h)) :
    (∑ s, q h s * Ps (s :: h)) / Ps h
      = β * bp_condExp T 1 (fun h' => mu (C h') * (Ps h' / P h')) h
        / (mu (C h) * (Ps h / P h)) := by
  rw [rs_condExp_one, Finset.sum_div, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e := heuler s
  have h1 := hP (s :: h)
  have h2 := hP h
  have h3 := hPs (s :: h)
  have h4 := hPs h
  field_simp at e ⊢
  linear_combination e

/-- AKMM, p. 709: with positive prices, probabilities and marginal utilities, the riskless cost
`1/R` is positive, so the gross real return `R` is positive. -/
theorem rs_return_pos (T : BPTree S) [Nonempty S] {mu : ℝ → ℝ} {C P : List S → ℝ}
    {q : List S → S → ℝ} {β : ℝ} (h : List S) (hβ : 0 < β) (hmu : ∀ h, 0 < mu (C h))
    (hP : ∀ h, 0 < P h)
    (heuler : ∀ s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h)) :
    0 < (∑ s, q h s * P (s :: h)) / P h := by
  rw [eq_23_10 T h (hmu h).ne' (fun h => (hP h).ne') heuler, rs_condExp_one]
  have hsum : 0 < ∑ s, T.pr (s :: h) / T.pr h * mu (C (s :: h)) :=
    Finset.sum_pos (fun s _ => mul_pos (div_pos (T.pr_pos _) (T.pr_pos _)) (hmu _))
      Finset.univ_nonempty
  exact div_pos (mul_pos hβ hsum) (hmu h)

/-- AKMM, p. 709 (corrected): "the gross real return `R_t ≥ 1`" does not follow. In the
deterministic tree with log utility (`u′(C) = 1/C`), `β = 1/2`, `P ≡ 1` and consumption falling
by a factor four each period, `C_t = 4^{−t}`, the Euler equation (23.9) holds with `q = 2`, so the
riskless cost is `1/R = 2` and `R = 1/2 < 1`. -/
theorem rs_return_lt_one :
    let C : List Unit → ℝ := fun h => (1 / 4) ^ h.length
    let q : List Unit → Unit → ℝ := fun _ _ => 2
    (∀ h s, (C h)⁻¹ * q h s / 1
        = bp_detTree.pr (s :: h) / bp_detTree.pr h * (1 / 2) * (C (s :: h))⁻¹ / 1) ∧
      ∀ h, (∑ s, q h s * 1) / 1 = (2 : ℝ) := by
  intro C q
  refine ⟨fun h s => ?_, fun h => ?_⟩
  · simp only [C, q, bp_detTree, List.length_cons, div_one, one_div, inv_pow, inv_inv, pow_succ]
    ring
  · simp [q]

/-- **(23.12)**, AKMM p. 710: if both countries' Euler equations (23.9) hold with the same
Arrow–Debreu prices (no arbitrage, `𝓔 = 1`), then
`u′(C_t)P*_t/(u′(C*_t)P_t) = u′(C_{t+1})P*_{t+1}/(u′(C*_{t+1})P_{t+1})` in every state. -/
theorem eq_23_12 (T : BPTree S) {mu : ℝ → ℝ} {C Cs P Ps : List S → ℝ} {q : List S → S → ℝ}
    {β : ℝ} (hβ : 0 < β) (hmu : ∀ h, 0 < mu (C h)) (hmus : ∀ h, 0 < mu (Cs h))
    (hP : ∀ h, 0 < P h) (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h))
    (heulers : ∀ h s, mu (Cs h) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * mu (Cs (s :: h)) / Ps (s :: h)) (h : List S) (s : S) :
    mu (C h) * Ps h / (mu (Cs h) * P h)
      = mu (C (s :: h)) * Ps (s :: h) / (mu (Cs (s :: h)) * P (s :: h)) := by
  have e1 := heuler h s
  have e2 := heulers h s
  have hpr : 0 < T.pr (s :: h) / T.pr h := div_pos (T.pr_pos _) (T.pr_pos _)
  have hq : 0 < q h s := by
    have : 0 < mu (C h) * q h s / P h := by
      rw [e1]; have := hmu (s :: h); have := hP (s :: h); positivity
    have h' : 0 < mu (C h) * q h s := by
      have := hP h
      exact (div_pos_iff_of_pos_right this).mp ‹_›
    exact pos_of_mul_pos_right h' (hmu h).le
  have := hmu h; have := hmus h; have := hP h; have := hPs h
  have := hmu (s :: h); have := hmus (s :: h); have := hP (s :: h); have := hPs (s :: h)
  field_simp at e1 e2 ⊢
  apply mul_left_cancel₀ hq.ne'
  linear_combination (Ps h * mu (Cs (s :: h))) * e1 - (P h * mu (C (s :: h))) * e2

/-- AKMM, p. 710: under complete markets the marginal-utility-weighted real exchange rate is
constant on the whole tree: `u′(C_t)Q_t/u′(C*_t) = κ₀ = u′(C₀)Q₀/u′(C*₀)` at every history,
with `Q = P*/P`. -/
theorem rs_kappa_const (T : BPTree S) {mu : ℝ → ℝ} {C Cs P Ps : List S → ℝ}
    {q : List S → S → ℝ} {β : ℝ} (hβ : 0 < β) (hmu : ∀ h, 0 < mu (C h))
    (hmus : ∀ h, 0 < mu (Cs h)) (hP : ∀ h, 0 < P h) (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, mu (C h) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * mu (C (s :: h)) / P (s :: h))
    (heulers : ∀ h s, mu (Cs h) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * mu (Cs (s :: h)) / Ps (s :: h)) (h : List S) :
    mu (C h) * Ps h / (mu (Cs h) * P h) = mu (C []) * Ps [] / (mu (Cs []) * P []) := by
  induction h with
  | nil => rfl
  | cons s h ih =>
    rw [← ih]
    exact (eq_23_12 T hβ hmu hmus hP hPs heuler heulers h s).symm

/-- **(23.13)**, AKMM p. 710: with CRRA utility, `u′(C) = C^{−σ}`, full risk sharing reads
`Q_t = κ₀(C_t/C*_t)^σ` at every history, `κ₀ = C₀^{−σ}Q₀/C*₀^{−σ}`. -/
theorem eq_23_13 (T : BPTree S) {C Cs P Ps : List S → ℝ} {q : List S → S → ℝ} {β σ : ℝ}
    (hβ : 0 < β) (hC : ∀ h, 0 < C h) (hCs : ∀ h, 0 < Cs h) (hP : ∀ h, 0 < P h)
    (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, C h ^ (-σ) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * C (s :: h) ^ (-σ) / P (s :: h))
    (heulers : ∀ h s, Cs h ^ (-σ) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * Cs (s :: h) ^ (-σ) / Ps (s :: h)) (h : List S) :
    Ps h / P h = C [] ^ (-σ) * Ps [] / (Cs [] ^ (-σ) * P []) * (C h / Cs h) ^ σ := by
  have hk := rs_kappa_const T (mu := fun c => c ^ (-σ)) hβ (fun h => rpow_pos_of_pos (hC h) _)
    (fun h => rpow_pos_of_pos (hCs h) _) hP hPs heuler heulers h
  rw [← hk, div_rpow (hC h).le (hCs h).le]
  have h1 := rpow_pos_of_pos (hC h) σ
  have h2 := rpow_pos_of_pos (hCs h) σ
  rw [rpow_neg (hC h).le, rpow_neg (hCs h).le]
  have := (hP h).ne'
  field_simp

/-- **(23.16)**, AKMM p. 712: with CRRA utility the ratio of the Lagrange multipliers
`χ = u′(C)/P` is `W = χ*/χ = (C/C*)^σ/Q`, `Q = P*/P`. -/
theorem eq_23_16 {σ C Cs P Ps : ℝ} (hC : 0 < C) (hCs : 0 < Cs) (hP : 0 < P) (hPs : 0 < Ps) :
    (Cs ^ (-σ) / Ps) / (C ^ (-σ) / P) = (C / Cs) ^ σ / (Ps / P) := by
  rw [rpow_neg hC.le, rpow_neg hCs.le, div_rpow hC.le hCs.le]
  have := (rpow_pos_of_pos hC σ).ne'
  have := (rpow_pos_of_pos hCs σ).ne'
  field_simp

/-- AKMM, p. 712: "`W_t` is constant over time in the complete-markets model": with CRRA utility
and complete markets, `W = χ*/χ = 1/κ₀` at every history. -/
theorem rs_wealth_const (T : BPTree S) {C Cs P Ps : List S → ℝ} {q : List S → S → ℝ} {β σ : ℝ}
    (hβ : 0 < β) (hC : ∀ h, 0 < C h) (hCs : ∀ h, 0 < Cs h) (hP : ∀ h, 0 < P h)
    (hPs : ∀ h, 0 < Ps h)
    (heuler : ∀ h s, C h ^ (-σ) * q h s / P h
      = T.pr (s :: h) / T.pr h * β * C (s :: h) ^ (-σ) / P (s :: h))
    (heulers : ∀ h s, Cs h ^ (-σ) * q h s / Ps h
      = T.pr (s :: h) / T.pr h * β * Cs (s :: h) ^ (-σ) / Ps (s :: h)) (h : List S) :
    (Cs h ^ (-σ) / Ps h) / (C h ^ (-σ) / P h)
      = (C [] ^ (-σ) * Ps [] / (Cs [] ^ (-σ) * P []))⁻¹ := by
  have hk := rs_kappa_const T (mu := fun c => c ^ (-σ)) hβ (fun h => rpow_pos_of_pos (hC h) _)
    (fun h => rpow_pos_of_pos (hCs h) _) hP hPs heuler heulers h
  rw [← hk]
  have := (rpow_pos_of_pos (hC h) (-σ)).ne'
  have := (rpow_pos_of_pos (hCs h) (-σ)).ne'
  have := (hP h).ne'
  have := (hPs h).ne'
  field_simp

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The bond economy: UIP, the covariance form and the zero-mean wealth wedge

AKMM, §23.3.2 "Riskless bonds only" and §23.3.3, (23.17)–(23.20), pp. 713–714.

On Miao's event tree, with the Euler equation (23.17) `Q_t = βEₜ[u′(C_{t+1})P_t/(u′(C_t)P_{t+1})]`
at home and abroad and one bond price (no arbitrage, `𝓔 = 1`), we prove:

* the real UIP condition (23.18) (`eq_23_18`);
* its covariance form (23.19) with the real rate `R⁻¹ = βEₜ[m]`, `m = u′(C_{t+1})/u′(C_t)`,
  `π = P_t/P_{t+1}`: `R⁻¹Eₜ[π] + β covₜ(m, π) = R*⁻¹Eₜ[π*] + β covₜ(m*, π*)` (`eq_23_19`). The
  book prints the covariances without the factor `β`; that version is false
  (`eq_23_19_printed_counterexample`);
* the wedge (23.20) `ε = χ_{t+1}/χ_t − χ*_{t+1}/χ*_t` has zero conditional mean (`eq_23_20`,
  `bond_wedge_mean_zero`);
* linearised, with `χ_{t+1}/χ_t = e^{a}` and `χ*_{t+1}/χ*_t = e^{b}`: if the UIP condition
  `Eₜ[e^{ta} − e^{tb}] = 0` holds along a path of equilibria, then the first-order wedge
  `ε̂ = a − b` has `Eₜ[ε̂] = 0`, and the log wealth gap `log W = log χ* − log χ` moves by exactly
  `b − a = −ε̂`, so `Eₜ[Ŵ_{t+1} − Ŵ_t] = 0` (`bond_wealth_loglin`).
-/

namespace AKMM.InternationalMacro

open Real Finset Filter
open Miao.CompleteMarkets (BPTree bp_condExp bp_condExp_sub_fun bp_markovTree)

variable {S : Type*} [Fintype S]

/-- **(23.18)**, AKMM p. 713: if the home and foreign Euler equations (23.17) hold with the same
bond price `Q_t` (no arbitrage under `𝓔 = 1`), then
`Eₜ[u′(C_{t+1})P_t/(u′(C_t)P_{t+1})] = Eₜ[u′(C*_{t+1})P*_t/(u′(C*_t)P*_{t+1})]`. -/
theorem eq_23_18 (T : BPTree S) {mu : ℝ → ℝ} {C Cs P Ps : List S → ℝ} {β Qb : ℝ} (h : List S)
    (hβ : β ≠ 0)
    (he : Qb = β * bp_condExp T 1 (fun h' => mu (C h') / mu (C h) * (P h / P h')) h)
    (hes : Qb = β * bp_condExp T 1 (fun h' => mu (Cs h') / mu (Cs h) * (Ps h / Ps h')) h) :
    bp_condExp T 1 (fun h' => mu (C h') / mu (C h) * (P h / P h')) h
      = bp_condExp T 1 (fun h' => mu (Cs h') / mu (Cs h) * (Ps h / Ps h')) h := by
  rw [he] at hes
  exact mul_left_cancel₀ hβ hes

/-- The conditional covariance `covₜ(x_{t+1}, y_{t+1})` at history `h`. -/
noncomputable def bondCov (T : BPTree S) (x y : List S → ℝ) (h : List S) : ℝ :=
  bp_condExp T 1 (fun h' => x h' * y h') h - bp_condExp T 1 x h * bp_condExp T 1 y h

/-- **(23.19)** (corrected), AKMM p. 713: with `R⁻¹ = βEₜ[m]` (the definition on p. 713),
`βEₜ[mπ] = R⁻¹Eₜ[π] + β covₜ(m, π)`; hence the UIP condition (23.18) `Eₜ[mπ] = Eₜ[m*π*]` is
equivalent to `R⁻¹Eₜ[π] + β covₜ(m, π) = R*⁻¹Eₜ[π*] + β covₜ(m*, π*)`. -/
theorem eq_23_19 (T : BPTree S) {β : ℝ} (hβ : β ≠ 0) (m pi ms pis : List S → ℝ) (h : List S) :
    bp_condExp T 1 (fun h' => m h' * pi h') h = bp_condExp T 1 (fun h' => ms h' * pis h') h ↔
      β * bp_condExp T 1 m h * bp_condExp T 1 pi h + β * bondCov T m pi h
        = β * bp_condExp T 1 ms h * bp_condExp T 1 pis h + β * bondCov T ms pis h := by
  unfold bondCov
  constructor
  · intro e; rw [← sub_eq_zero]; ring_nf; rw [e]; ring
  · intro e
    have : β * (bp_condExp T 1 (fun h' => m h' * pi h') h
        - bp_condExp T 1 (fun h' => ms h' * pis h') h) = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hβ
    · linarith

/-- The two-state event tree with probability `1/2` for each shock (Miao's Markov tree). -/
noncomputable def bondCoinTree : BPTree Bool :=
  bp_markovTree (fun _ _ => 1 / 2) true (fun _ _ => by norm_num)
    (fun _ => by simp)

/-- `E₀[x₁] = x(H)/2 + x(T)/2` on the coin tree. -/
theorem bondCoinTree_condExp (x : List Bool → ℝ) :
    bp_condExp bondCoinTree 1 x [] = x [true] / 2 + x [false] / 2 := by
  rw [rs_condExp_one, Fintype.sum_bool]
  simp [bondCoinTree, bp_markovTree, Miao.CompleteMarkets.bp_markovPr]
  ring

/-- AKMM, (23.19), p. 713 (printed version refuted): the printed
`R⁻¹Eₜ[π] + covₜ(m, π) = R*⁻¹Eₜ[π*] + covₜ(m*, π*)` (covariances without `β`) does not follow from
(23.17)–(23.18). Two equally likely states, log utility `u′(C) = 1/C`, `β = 1/2`; home:
`C ≡ 1`, `P ≡ 1`; foreign: `C*₀ = 1`, `C*₁ ∈ {2, 2/3}`, `P*₀ = 1`, `P*₁ ∈ {2/5, 2}`. Then
`m ≡ π ≡ 1`, `m* ∈ {1/2, 3/2}`, `π* ∈ {5/2, 1/2}`, both Euler equations hold with `Q = 1/2`
(so (23.18) holds), but the printed left side is `1/2` and its right side `1/4`. -/
theorem eq_23_19_printed_counterexample :
    let Cs : List Bool → ℝ := fun h => if h = [true] then 2 else if h = [false] then 2 / 3 else 1
    let Ps : List Bool → ℝ := fun h => if h = [true] then 2 / 5 else if h = [false] then 2 else 1
    let m : List Bool → ℝ := fun _ => (1 / 1 : ℝ) / (1 / 1)
    let pi : List Bool → ℝ := fun _ => (1 : ℝ) / 1
    let ms : List Bool → ℝ := fun h' => (1 / Cs h') / (1 / Cs [])
    let pis : List Bool → ℝ := fun h' => Ps [] / Ps h'
    (1 / 2 : ℝ) = 1 / 2 * bp_condExp bondCoinTree 1 (fun h' => m h' * pi h') [] ∧
      (1 / 2 : ℝ) = 1 / 2 * bp_condExp bondCoinTree 1 (fun h' => ms h' * pis h') [] ∧
      1 / 2 * bp_condExp bondCoinTree 1 m [] * bp_condExp bondCoinTree 1 pi []
          + bondCov bondCoinTree m pi [] = 1 / 2 ∧
      1 / 2 * bp_condExp bondCoinTree 1 ms [] * bp_condExp bondCoinTree 1 pis []
          + bondCov bondCoinTree ms pis [] = 1 / 4 := by
  intro Cs Ps m pi ms pis
  unfold bondCov
  simp only [bondCoinTree_condExp, m, pi, ms, pis, Cs, Ps]
  norm_num

/-- **(23.20)**, AKMM p. 714: the wedge `u′(C_{t+1})P_t/(u′(C_t)P_{t+1}) − (foreign)` is
`χ_{t+1}/χ_t − χ*_{t+1}/χ*_t` with `χ = u′(C)/P`. -/
theorem eq_23_20 {u0 u1 us0 us1 P0 P1 Ps0 Ps1 : ℝ} (hu0 : u0 ≠ 0) (hus0 : us0 ≠ 0)
    (hP1 : P1 ≠ 0) (hPs1 : Ps1 ≠ 0) :
    u1 / u0 * (P0 / P1) - us1 / us0 * (Ps0 / Ps1)
      = (u1 / P1) / (u0 / P0) - (us1 / Ps1) / (us0 / Ps0) := by
  field_simp

/-- AKMM, p. 714: "this wedge must equal zero in expectation": under (23.18),
`Eₜ[ε_{t+1}] = 0`. -/
theorem bond_wedge_mean_zero (T : BPTree S) (m ms : List S → ℝ) (h : List S)
    (h18 : bp_condExp T 1 m h = bp_condExp T 1 ms h) :
    bp_condExp T 1 (fun h' => m h' - ms h') h = 0 := by
  rw [bp_condExp_sub_fun, h18, sub_self]

/-- AKMM, p. 714, linearised: write `χ_{t+1}/χ_t = e^{a}` and `χ*_{t+1}/χ*_t = e^{b}` state by
state. If the UIP condition holds along a path of equilibria indexed by `t` (scaling the shocks,
`Eₜ[e^{ta} − e^{tb}] = 0` for all `t`), then its first-order term vanishes, `Eₜ[a − b] = 0`, i.e.
`Eₜ[ε̂] = 0`; and the log wealth gap `log W = log χ* − log χ` changes by exactly `b − a = −ε̂`,
so `Eₜ[Ŵ_{t+1} − Ŵ_t] = 0`. -/
theorem bond_wealth_loglin (T : BPTree S) (a b : List S → ℝ) (h : List S)
    (h18 : ∀ t : ℝ, bp_condExp T 1 (fun h' => exp (t * a h') - exp (t * b h')) h = 0)
    {chi chis : ℝ} (hchi : 0 < chi) (hchis : 0 < chis) :
    bp_condExp T 1 (fun h' => a h' - b h') h = 0 ∧
      bp_condExp T 1 (fun h' => log ((chis * exp (b h')) / (chi * exp (a h')))
        - log (chis / chi)) h = 0 := by
  have hfun : (fun t : ℝ => bp_condExp T 1 (fun h' => exp (t * a h') - exp (t * b h')) h)
      = fun t => ∑ s, T.pr (s :: h) / T.pr h * (exp (t * a (s :: h)) - exp (t * b (s :: h))) := by
    funext t; rw [rs_condExp_one]
  have hd : HasDerivAt (fun t => ∑ s, T.pr (s :: h) / T.pr h
      * (exp (t * a (s :: h)) - exp (t * b (s :: h))))
      (∑ s, T.pr (s :: h) / T.pr h * (a (s :: h) - b (s :: h))) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun s _ =>
      ((((hasDerivAt_id (0 : ℝ)).mul_const (a (s :: h))).exp.sub
        ((hasDerivAt_id (0 : ℝ)).mul_const (b (s :: h))).exp).const_mul (T.pr (s :: h) / T.pr h)))
    simpa using this
  have hzero : HasDerivAt (fun t => ∑ s, T.pr (s :: h) / T.pr h
      * (exp (t * a (s :: h)) - exp (t * b (s :: h)))) 0 0 := by
    rw [← hfun]
    have : (fun t : ℝ => bp_condExp T 1 (fun h' => exp (t * a h') - exp (t * b h')) h)
        = fun _ => 0 := funext h18
    rw [this]
    exact hasDerivAt_const _ _
  have h1 : bp_condExp T 1 (fun h' => a h' - b h') h = 0 := by
    rw [rs_condExp_one]
    exact hd.unique hzero
  refine ⟨h1, ?_⟩
  have e : (fun h' => log ((chis * exp (b h')) / (chi * exp (a h'))) - log (chis / chi))
      = fun h' => -(a h' - b h') := by
    funext h'
    rw [log_div (by positivity) (by positivity), log_mul hchis.ne' (exp_pos _).ne',
      log_mul hchi.ne' (exp_pos _).ne', log_div hchis.ne' hchi.ne', log_exp, log_exp]
    ring
  rw [e, rs_condExp_one]
  rw [rs_condExp_one] at h1
  simp only [mul_neg, Finset.sum_neg_distrib, h1, neg_zero]

end AKMM.InternationalMacro

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linearised bond economy has a unit root

AKMM, §23.3.3, pp. 714–715.

The linearised UIP condition says `Eₜ[Ŵ_{t+1}] = Ŵ_t` (see `bond_wealth_loglin`). The book: "in
the linearized version of the bond economy, relative wealth is non-stationary … due to the fact
that the model is linearized around a non-stochastic steady state in which … `βR = 1`". This is
Hall's random walk: a linear Euler equation `u′(Ŵ_t) = (1 + r)βEₜ u′(Ŵ_{t+1})` with linear
marginal utility `u′(x) = 1 − x` and `(1 + r)β = 1`. Using Obstfeld–Rogoff's Hall theorems
(`hall_martingale`, `hall_condExp_future`) in the measure-theoretic setting of a filtration, we
prove that the relative wealth gap is a martingale (`unitroot_martingale`), that every forecast
equals the current gap, `Eₜ[Ŵ_s] = Ŵ_t` for all `s ≥ t` — shocks are permanent, there is no mean
reversion (`unitroot_forecast`) — and that the gap is a unit-root process `Ŵ_{t+1} = Ŵ_t + ε_{t+1}`
with `Eₜ[ε_{t+1}] = 0` (`unitroot_innovation`). In contrast, with a debt-elastic (Uzawa) factor
`ρ ∈ (−1, 1)` the forecasts `ρᵏŴ_t` revert to zero (`unitroot_uzawa_contrast`).
-/

namespace AKMM.InternationalMacro

open MeasureTheory Filter Topology
open ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption (quadMU hall_martingale
  hall_condExp_future)

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The linearised UIP condition `Eₜ[Ŵ_{t+1}] = Ŵ_t` is Hall's Euler equation for the linear
marginal utility `1 − Ŵ` with `(1 + r)β = 1`. -/
theorem unitroot_hall_form [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    {r β : ℝ} (hrβ : (1 + r) * β = 1) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) (t : ℕ) :
    μ[fun ω => quadMU 1 (W (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU 1 (W t ω) / ((1 + r) * β) := by
  have h1 : (fun ω => quadMU 1 (W (t + 1) ω)) = (fun _ => (1 : ℝ)) - W (t + 1) := by
    funext ω; simp [quadMU]
  rw [h1, hrβ]
  filter_upwards [condExp_sub (integrable_const (1 : ℝ)) (hWi (t + 1)) (ℱ t), h18 t]
    with ω h2 h3
  rw [h2, Pi.sub_apply, condExp_const (ℱ.le t), h3]
  simp [quadMU]

/-- AKMM, p. 714: under the linearised UIP condition `Eₜ[Ŵ_{t+1}] = Ŵ_t` (and `βR = 1` at the
steady state), the relative wealth gap is a martingale. -/
theorem unitroot_martingale [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    {β : ℝ} (hβ : 0 < β) (hW : StronglyAdapted ℱ W) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) : Martingale W ℱ μ := by
  have hrβ : (1 + (1 / β - 1)) * β = 1 := by field_simp; ring
  exact hall_martingale ℱ one_ne_zero hrβ hW hWi (unitroot_hall_form ℱ hrβ hWi h18)

/-- AKMM, p. 714: "relative wealth is non-stationary: the economy does not converge back to the
symmetric steady state": every forecast of the wealth gap equals its current value,
`Eₜ[Ŵ_s] = Ŵ_t` for all `s ≥ t`. -/
theorem unitroot_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    {β : ℝ} (hβ : 0 < β) (hW : StronglyAdapted ℱ W) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) {t s : ℕ} (hts : t ≤ s) :
    μ[W s | ℱ t] =ᵐ[μ] W t := by
  have hrβ : (1 + (1 / β - 1)) * β = 1 := by field_simp; ring
  exact hall_condExp_future ℱ one_ne_zero hrβ hW hWi (unitroot_hall_form ℱ hrβ hWi h18) hts

/-- AKMM, pp. 714–715: the classic unit-root form `Ŵ_{t+1} = Ŵ_t + ε_{t+1}` with
`Eₜ[ε_{t+1}] = 0`. -/
theorem unitroot_innovation [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {W : ℕ → Ω → ℝ}
    (hW : StronglyAdapted ℱ W) (hWi : ∀ t, Integrable (W t) μ)
    (h18 : ∀ t, μ[W (t + 1) | ℱ t] =ᵐ[μ] W t) (t : ℕ) :
    μ[W (t + 1) - W t | ℱ t] =ᵐ[μ] 0 := by
  have hCt : μ[W t | ℱ t] = W t := condExp_of_stronglyMeasurable (ℱ.le t) (hW t) (hWi t)
  filter_upwards [condExp_sub (hWi (t + 1)) (hWi t) (ℱ t), h18 t] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, hCt, sub_self]
  rfl

/-- AKMM, p. 715: the contrast with debt-elastic (Uzawa) discounting, which restores
stationarity: if forecasts evolve as `e_{k+1} = ρ e_k` with `|ρ| < 1`, they revert to zero,
`e_k = ρᵏ e_0 → 0`; with the unit root `ρ = 1` they stay at `e_0`. -/
theorem unitroot_uzawa_contrast {ρ : ℝ} (e : ℕ → ℝ) (he : ∀ k, e (k + 1) = ρ * e k) :
    (∀ k, e k = ρ ^ k * e 0) ∧ (|ρ| < 1 → Tendsto e atTop (𝓝 0)) ∧ (ρ = 1 → ∀ k, e k = e 0) := by
  have hk : ∀ k, e k = ρ ^ k * e 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [he, ih, pow_succ]; ring
  refine ⟨hk, fun hρ => ?_, fun h1 k => by rw [hk, h1, one_pow, one_mul]⟩
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ).mul_const (e 0)
  rw [zero_mul] at this
  exact this.congr fun k => (hk k).symm

end AKMM.InternationalMacro

set_option linter.style.longLine false
#print axioms AKMM.InternationalMacro.accounting_saving
#print axioms AKMM.InternationalMacro.accounting_ca_sub_nx
#print axioms AKMM.InternationalMacro.accounting_ca_add_fa
#print axioms AKMM.InternationalMacro.accounting_deficit_financed
#print axioms AKMM.InternationalMacro.accounting_rer_log_change
#print axioms AKMM.InternationalMacro.accounting_relative_ppp_iff
#print axioms AKMM.InternationalMacro.accounting_ppp_iff
#print axioms AKMM.InternationalMacro.accounting_bond_trade_balance
#print axioms AKMM.InternationalMacro.accounting_bond_current_account
#print axioms AKMM.InternationalMacro.armington_price_homog
#print axioms AKMM.InternationalMacro.eq_23_3_spending
#print axioms AKMM.InternationalMacro.armington_demand_eq
#print axioms AKMM.InternationalMacro.eq_23_3_index
#print axioms AKMM.InternationalMacro.eq_23_3_cost_min
#print axioms AKMM.InternationalMacro.eq_23_4_least_cost
#print axioms AKMM.InternationalMacro.eq_23_6
#print axioms AKMM.InternationalMacro.substSum
#print axioms AKMM.InternationalMacro.substMPx
#print axioms AKMM.InternationalMacro.substSum_pos
#print axioms AKMM.InternationalMacro.subst_hasDerivAt_x
#print axioms AKMM.InternationalMacro.subst_hasDerivAt_xy
#print axioms AKMM.InternationalMacro.subst_cross_partial_pos
#print axioms AKMM.InternationalMacro.substDemandH
#print axioms AKMM.InternationalMacro.substDemandH_eq
#print axioms AKMM.InternationalMacro.subst_gross_substitutes
#print axioms AKMM.InternationalMacro.subst_gross_complements
#print axioms AKMM.InternationalMacro.eq_23_8
#print axioms AKMM.InternationalMacro.eq_23_8_rpow
#print axioms AKMM.InternationalMacro.ppp_at_one
#print axioms AKMM.InternationalMacro.ppp_same_basket
#print axioms AKMM.InternationalMacro.ppp_iff_same_basket
#print axioms AKMM.InternationalMacro.ppp_ratio_lt
#print axioms AKMM.InternationalMacro.ppp_strictMonoOn
#print axioms AKMM.InternationalMacro.ppp_strictAntiOn
#print axioms AKMM.InternationalMacro.ppp_strictMonoOn_iff
#print axioms AKMM.InternationalMacro.ppp_symmetric
#print axioms AKMM.InternationalMacro.ppp_relPrice
#print axioms AKMM.InternationalMacro.env_value
#print axioms AKMM.InternationalMacro.env_hasDerivAt
#print axioms AKMM.InternationalMacro.env_chi_strictAntiOn
#print axioms AKMM.InternationalMacro.env_crra
#print axioms AKMM.InternationalMacro.ssExcess
#print axioms AKMM.InternationalMacro.ssExcessF
#print axioms AKMM.InternationalMacro.ss_demand_one
#print axioms AKMM.InternationalMacro.ss_excess_eq
#print axioms AKMM.InternationalMacro.ss_walras
#print axioms AKMM.InternationalMacro.ss_equilibrium_iff
#print axioms AKMM.InternationalMacro.ss_exists
#print axioms AKMM.InternationalMacro.ss_cm_exists
#print axioms AKMM.InternationalMacro.ss_unique
#print axioms AKMM.InternationalMacro.ss_multiple
#print axioms AKMM.InternationalMacro.loglinP
#print axioms AKMM.InternationalMacro.loglinP_pos
#print axioms AKMM.InternationalMacro.loglinP_zero
#print axioms AKMM.InternationalMacro.loglinP_hasDerivAt
#print axioms AKMM.InternationalMacro.loglin_hasDerivAt_of_log
#print axioms AKMM.InternationalMacro.loglin_log_weighted
#print axioms AKMM.InternationalMacro.loglin_rer
#print axioms AKMM.InternationalMacro.eq_23_21
#print axioms AKMM.InternationalMacro.eq_23_22
#print axioms AKMM.InternationalMacro.loglin_demand
#print axioms AKMM.InternationalMacro.loglin_exp_ray
#print axioms AKMM.InternationalMacro.loglinDH
#print axioms AKMM.InternationalMacro.loglinDF
#print axioms AKMM.InternationalMacro.loglin_DH
#print axioms AKMM.InternationalMacro.loglin_DF
#print axioms AKMM.InternationalMacro.eq_23_23
#print axioms AKMM.InternationalMacro.loglin_world
#print axioms AKMM.InternationalMacro.eq_23_24
#print axioms AKMM.InternationalMacro.loglin_coef_eq
#print axioms AKMM.InternationalMacro.fn_28
#print axioms AKMM.InternationalMacro.loglin_autarky_cons
#print axioms AKMM.InternationalMacro.eq_23_25
#print axioms AKMM.InternationalMacro.eq_23_26
#print axioms AKMM.InternationalMacro.eq_23_26_of_24_25
#print axioms AKMM.InternationalMacro.loglinBondCons
#print axioms AKMM.InternationalMacro.loglin_bond_cons
#print axioms AKMM.InternationalMacro.eq_23_27
#print axioms AKMM.InternationalMacro.loglin_bond_printed
#print axioms AKMM.InternationalMacro.tot_cm_denom_pos
#print axioms AKMM.InternationalMacro.eq_23_28
#print axioms AKMM.InternationalMacro.tot_cm_worsen
#print axioms AKMM.InternationalMacro.tot_cm_coef_strictAntiOn
#print axioms AKMM.InternationalMacro.tot_cm_tendsto_atTop
#print axioms AKMM.InternationalMacro.tot_cm_tendsto_zero
#print axioms AKMM.InternationalMacro.tot_cm_coef_lt
#print axioms AKMM.InternationalMacro.eq_23_29
#print axioms AKMM.InternationalMacro.tot_fa_degenerate
#print axioms AKMM.InternationalMacro.tot_fa_threshold
#print axioms AKMM.InternationalMacro.tot_fa_worsen_iff
#print axioms AKMM.InternationalMacro.tot_cole_obstfeld
#print axioms AKMM.InternationalMacro.tot_no_home_bias
#print axioms AKMM.InternationalMacro.fn_31
#print axioms AKMM.InternationalMacro.tot_cm_backus_smith
#print axioms AKMM.InternationalMacro.tot_fa_backus_smith
#print axioms AKMM.InternationalMacro.tot_rd_slope
#print axioms AKMM.InternationalMacro.tot_rd_coefficient
#print axioms AKMM.InternationalMacro.fn_30
#print axioms AKMM.InternationalMacro.nx_identity
#print axioms AKMM.InternationalMacro.eq_23_14_sign
#print axioms AKMM.InternationalMacro.eq_23_15
#print axioms AKMM.InternationalMacro.nx_loglin
#print axioms AKMM.InternationalMacro.eq_23_30
#print axioms AKMM.InternationalMacro.eq_23_31
#print axioms AKMM.InternationalMacro.nx_log_utility
#print axioms AKMM.InternationalMacro.nx_ml_limit
#print axioms AKMM.InternationalMacro.nxImportsHome
#print axioms AKMM.InternationalMacro.nxImportsForeign
#print axioms AKMM.InternationalMacro.nx_imports_hasDerivAt
#print axioms AKMM.InternationalMacro.nx_marshall_lerner
#print axioms AKMM.InternationalMacro.eq_23_33
#print axioms AKMM.InternationalMacro.eq_23_34
#print axioms AKMM.InternationalMacro.prod_labour_demand
#print axioms AKMM.InternationalMacro.prod_profit
#print axioms AKMM.InternationalMacro.eq_23_36_printed_counterexample
#print axioms AKMM.InternationalMacro.eq_23_36_log
#print axioms AKMM.InternationalMacro.prod_relPrice_loglin
#print axioms AKMM.InternationalMacro.eq_23_37
#print axioms AKMM.InternationalMacro.prod_cm_slope
#print axioms AKMM.InternationalMacro.eq_23_38
#print axioms AKMM.InternationalMacro.prod_fa_slope_sign
#print axioms AKMM.InternationalMacro.prod_global_output
#print axioms AKMM.InternationalMacro.rs_condExp_one
#print axioms AKMM.InternationalMacro.eq_23_10
#print axioms AKMM.InternationalMacro.eq_23_11
#print axioms AKMM.InternationalMacro.rs_return_pos
#print axioms AKMM.InternationalMacro.rs_return_lt_one
#print axioms AKMM.InternationalMacro.eq_23_12
#print axioms AKMM.InternationalMacro.rs_kappa_const
#print axioms AKMM.InternationalMacro.eq_23_13
#print axioms AKMM.InternationalMacro.eq_23_16
#print axioms AKMM.InternationalMacro.rs_wealth_const
#print axioms AKMM.InternationalMacro.eq_23_18
#print axioms AKMM.InternationalMacro.bondCov
#print axioms AKMM.InternationalMacro.eq_23_19
#print axioms AKMM.InternationalMacro.bondCoinTree
#print axioms AKMM.InternationalMacro.bondCoinTree_condExp
#print axioms AKMM.InternationalMacro.eq_23_19_printed_counterexample
#print axioms AKMM.InternationalMacro.eq_23_20
#print axioms AKMM.InternationalMacro.bond_wedge_mean_zero
#print axioms AKMM.InternationalMacro.bond_wealth_loglin
#print axioms AKMM.InternationalMacro.unitroot_hall_form
#print axioms AKMM.InternationalMacro.unitroot_martingale
#print axioms AKMM.InternationalMacro.unitroot_forecast
#print axioms AKMM.InternationalMacro.unitroot_innovation
#print axioms AKMM.InternationalMacro.unitroot_uzawa_contrast
