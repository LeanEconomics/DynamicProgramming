/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
