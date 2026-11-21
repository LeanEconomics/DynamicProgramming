/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMInternationalMacro.LogLinear
import Mathlib.Analysis.SpecificLimits.Basic

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
