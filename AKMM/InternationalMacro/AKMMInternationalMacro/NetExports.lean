/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.TermsOfTrade
import IntertemporalTrade.Stability

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
