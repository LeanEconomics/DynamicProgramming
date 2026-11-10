/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.OXExistence
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The offer curve and the dynamics of the special case

Miao, §16.1, "A Special Case and Multiple Equilibria", pp. 532–536 (Figures 16.1–16.4).

* Saving `m_t = m_t^t/p_t = e₁ − c_t^t` and excess demand `z_t = m_t^t/p_{t+1} = m_t R_{t+1}`:
  the ray to a point of the offer curve has slope `R_{t+1}` (`ox_offer_z`), the offer curve lies
  left of `e₁` (`ox_offer_lt_e1`); in equilibrium with `g_n = g_m = 1`, `z_t = m_{t+1}` and the
  Euler equation is `u'(e₁ − m_t) = βu'(m_tR_{t+1} + e₂)R_{t+1}` (`ox_offer_equilibrium`).
* The slopes `dm_t/dR_{t+1}` and `dz_t/dR_{t+1} > 0` by implicit differentiation of the Euler
  equation (`ox_offer_slope_m`, `ox_offer_slope_z`, `ox_offer_slope_z_pos`); backward bending
  iff `βu'(c)(γ(c)z/c − 1) > 0` (`ox_offer_backward_iff`), which needs `γ(c_{t+1}^t) > 1`
  (`ox_offer_backward_necessary`); `γ ≤ 1` gives an upward-sloping curve (`ox_offer_upward`).
* The nonmonetary steady state at the origin: zero saving is optimal exactly at `R = R_aut`
  (`ox_offer_origin`), and the slope of the offer curve at the origin is `R_aut`
  (`ox_offer_slope_origin`); monetary steady states lie on the 45° line with `R = 1`
  (`ox_offer_steady_iff`) and exist iff `R_aut < 1` (`ox_offer_steady_exists_iff`).
* Along paths with real balances vanishing, `R_{t+1} → R_aut` and inflation
  `p_{t+1}/p_t → 1/R_aut`, the inverse of the slope at the origin (`ox_R_tendsto_Raut`).
* Stability of a steady state of `m_{t+1} = f(m_t)`: `|f'| < 1` gives local stability
  (`ox_fixed_stable`), `|f'| > 1` instability (`ox_fixed_unstable`); the locally stable case
  is indeterminate, a continuum of monetary equilibria converging to `m*`
  (`ox_indeterminacy`); two-period cycles (`ox_two_cycle`).

**Correction.** "A monetary steady state is unstable iff `|dm_{t+1}/dm_t| > 1`" fails at
`|f'| = 1`: `f(x) = x + x³` has `f'(0) = 1` and an unstable fixed point
(`ox_unstable_counterexample`). What is true is the two sufficient conditions above.
Figures 16.1–16.4 are not formalised beyond these statements; the convergence claims of
Figure 16.2 are proved for the logarithmic economy (`OXExamples`, Example 16.1.1).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, p. 532: with real saving `m = q_t m_t^t` and `z = q_{t+1} m_t^t`, `z = mR_{t+1}`: the
slope of the ray from the origin to a point of the offer curve is `p_t/p_{t+1}`. -/
theorem ox_offer_z (q : ℕ → ℝ) (t : ℕ) (hq : q t ≠ 0) (mm : ℝ) :
    q (t + 1) * mm = q t * mm * (q (t + 1) / q t) := by
  field_simp

/-- Miao, p. 532: the offer curve lies to the left of `e₁`: optimal saving is below `e₁`. -/
theorem ox_offer_lt_e1 {q : ℕ → ℝ} {t : ℕ} {c1 c2 m : ℝ} (h : E.ox_Optimal q t c1 c2 m) :
    q t * m < E.ox_e1 := by
  obtain ⟨⟨_, h1, _, hb1, _⟩, _⟩ := h
  linarith

/-- Miao, pp. 532–534: in a monetary equilibrium of the special case `g_n = g_m = 1`, demand
equals supply, `z_t = m_tR_{t+1} = m_{t+1}`, and the Euler equation reads
`u'(e₁ − m_t) = βu'(m_tR_{t+1} + e₂)R_{t+1}`. -/
theorem ox_offer_equilibrium (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_mhat q t * (q (t + 1) / q t) = E.ox_mhat q (t + 1) ∧
      E.ox_P.ox_du (E.ox_e1 - E.ox_mhat q t) = E.ox_P.ox_β *
        E.ox_P.ox_du (E.ox_mhat q t * (q (t + 1) / q t) + E.ox_e2) * (q (t + 1) / q t) := by
  obtain ⟨-, hpos, -, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  have h7 := E.eq_16_7 q (h.2 t ht)
  rw [hgn, hgm, one_mul, one_mul] at h7
  have hz : E.ox_mhat q t * (q (t + 1) / q t) = E.ox_mhat q (t + 1) := by
    rw [h7]; field_simp
  refine ⟨hz, ?_⟩
  have h6 := (E.eq_16_6 h ht).1
  rw [hgn, one_mul] at h6
  have hd := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + E.ox_mhat q (t + 1) by
    have := ((E.ox_monetary_alloc h).1 (t + 1) (by omega)).2.1
    linarith [E.ox_e2_pos])
  have hβ := E.ox_P.ox_β_pos
  rw [div_eq_iff (by positivity)] at h6
  rw [hz, add_comm, h6]; ring

end OXEconomy

namespace OXPrefs

variable (P : OXPrefs)

/-- Miao, p. 533: implicit differentiation of the Euler equation
`u'(e₁ − m(R)) = βu'(m(R)R + e₂)R` gives
`m'(u''(c₁) + βR²u''(c₂)) = −(Rmβu''(c₂) + βu'(c₂))`. -/
theorem ox_offer_slope_m {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R') :
    m' * (d1 + P.ox_β * R ^ 2 * d2) =
      -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) := by
  have hL : HasDerivAt (fun R' => P.ox_du (e1 - mf R')) (d1 * -m') R :=
    hd1.comp R (hm.const_sub e1)
  have hin : HasDerivAt (fun R' => mf R' * R' + e2) (m' * R + mf R * 1) R :=
    ((hm.mul (hasDerivAt_id R)).add_const e2)
  have hR : HasDerivAt (fun R' => P.ox_β * P.ox_du (mf R' * R' + e2) * R')
      (P.ox_β * (d2 * (m' * R + mf R * 1)) * R + P.ox_β * P.ox_du (mf R * R + e2) * 1) R :=
    ((hd2.comp R hin).const_mul P.ox_β).mul (hasDerivAt_id R)
  have := hL.unique (hR.congr_of_eventuallyEq (by
    filter_upwards [heul] with R' hR' using hR'))
  linear_combination (-1 : ℝ) * this

/-- Miao, p. 533: `dm_t/dR_{t+1} = −(R mβu''(c₂) + βu'(c₂))/(u''(c₁) + βR²u''(c₂))`. -/
theorem ox_offer_slope_m_eq {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 ≠ 0) :
    m' = -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) /
      (d1 + P.ox_β * R ^ 2 * d2) := by
  rw [eq_div_iff hD]; exact P.ox_offer_slope_m hm hd1 hd2 heul

/-- Miao, p. 533: with `z(R) = m(R)R`,
`dz_t/dR_{t+1} = (m u''(c₁) − βu'(c₂)R)/(u''(c₁) + βR²u''(c₂))`. -/
theorem ox_offer_slope_z {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 ≠ 0) :
    HasDerivAt (fun R' => mf R' * R')
      ((mf R * d1 - P.ox_β * P.ox_du (mf R * R + e2) * R) / (d1 + P.ox_β * R ^ 2 * d2)) R := by
  have h : HasDerivAt (fun R' => mf R' * R') (m' * R + mf R * 1) R := hm.mul (hasDerivAt_id' R)
  convert h using 1
  have hs := P.ox_offer_slope_m hm hd1 hd2 heul
  rw [div_eq_iff hD]
  linear_combination (-R) * hs

/-- Miao, p. 533: `dz_t/dR_{t+1} > 0` (with `u'' < 0` at both consumptions, `m ≥ 0`, `R > 0`). -/
theorem ox_offer_slope_z_pos {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hd1n : d1 < 0) (hd2n : d2 < 0) (hR : 0 < R) (hm0 : 0 ≤ mf R) (hc2 : 0 < mf R * R + e2) :
    ∃ z', HasDerivAt (fun R' => mf R' * R') z' R ∧ 0 < z' := by
  have hβ := P.ox_β_pos
  have hD : d1 + P.ox_β * R ^ 2 * d2 < 0 := by
    have : 0 ≤ P.ox_β * R ^ 2 := by positivity
    have := mul_nonpos_of_nonneg_of_nonpos this hd2n.le
    linarith
  refine ⟨_, P.ox_offer_slope_z hm hd1 hd2 heul hD.ne, div_pos_of_neg_of_neg ?_ hD⟩
  have := P.ox_du_pos _ hc2
  have : 0 < P.ox_β * P.ox_du (mf R * R + e2) * R := by positivity
  have := mul_nonpos_of_nonneg_of_nonpos hm0 hd1n.le
  linarith

/-- Miao, p. 533: the coefficient of relative risk aversion `γ(c) = −cu''(c)/u'(c)` enters
through the identity `−(Rmβu''(c₂) + βu'(c₂)) = βu'(c₂)(γ(c₂)z/c₂ − 1)`, `z = mR`; hence, as the
denominator is negative, `dm_t/dR_{t+1} < 0` iff `0 < βu'(c₂)(γ(c₂)z/c₂ − 1)`. -/
theorem ox_offer_backward_iff {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 < 0) (hc2 : 0 < mf R * R + e2) :
    -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) =
        P.ox_β * P.ox_du (mf R * R + e2) *
          ((-(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)) * (mf R * R / (mf R * R + e2)) - 1) ∧
      (m' < 0 ↔ 0 < P.ox_β * P.ox_du (mf R * R + e2) *
          ((-(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)) * (mf R * R / (mf R * R + e2)) - 1))
    := by
  have hdu := P.ox_du_pos _ hc2
  have hid : -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) =
      P.ox_β * P.ox_du (mf R * R + e2) *
        ((-(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)) * (mf R * R / (mf R * R + e2)) - 1) := by
    set w := P.ox_du (mf R * R + e2)
    set c := mf R * R + e2
    have hw : w ≠ 0 := hdu.ne'
    have hc : c ≠ 0 := hc2.ne'
    field_simp
    ring
  refine ⟨hid, ?_⟩
  rw [← hid]
  have hs := P.ox_offer_slope_m hm hd1 hd2 heul
  constructor
  · intro hm'; nlinarith
  · intro hpos
    by_contra hge
    have : 0 ≤ m' := not_lt.1 hge
    nlinarith [mul_nonpos_of_nonneg_of_nonpos this hD.le]

/-- Miao, p. 534: since `z < c_{t+1}^t` (`e₂ > 0`), a backward-bending offer curve
(`dm_t/dR_{t+1} < 0`) needs `γ(c_{t+1}^t) > 1`. -/
theorem ox_offer_backward_necessary {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ}
    (hm : HasDerivAt mf m' R) (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R))
    (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 < 0) (he2 : 0 < e2) (hz : 0 ≤ mf R * R) (hm' : m' < 0) :
    1 < -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2) := by
  have hc2 : 0 < mf R * R + e2 := by linarith
  obtain ⟨-, hiff⟩ := P.ox_offer_backward_iff hm hd1 hd2 heul hD hc2
  have hpos := hiff.1 hm'
  have hβ := P.ox_β_pos
  have hdu := P.ox_du_pos _ hc2
  set γ := -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)
  have h1 : 0 < γ * (mf R * R / (mf R * R + e2)) - 1 := by
    by_contra hle
    have : P.ox_β * P.ox_du (mf R * R + e2) *
        (γ * (mf R * R / (mf R * R + e2)) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hle)
    linarith
  have hfrac : mf R * R / (mf R * R + e2) < 1 := (div_lt_one hc2).2 (by linarith)
  have hfrac0 : 0 ≤ mf R * R / (mf R * R + e2) := div_nonneg hz hc2.le
  by_contra hγ
  have hγ' : γ ≤ 1 := not_lt.1 hγ
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · nlinarith
  · nlinarith

/-- Miao, p. 534: if `γ(c_{t+1}^t) ≤ 1` the offer curve is upward sloping: `dm_t/dR_{t+1} > 0`. -/
theorem ox_offer_upward {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 < 0) (he2 : 0 < e2) (hz : 0 ≤ mf R * R)
    (hγ : -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2) ≤ 1) : 0 < m' := by
  have hc2 : 0 < mf R * R + e2 := by linarith
  obtain ⟨hid, -⟩ := P.ox_offer_backward_iff hm hd1 hd2 heul hD hc2
  have hs := P.ox_offer_slope_m hm hd1 hd2 heul
  have hβ := P.ox_β_pos
  have hdu := P.ox_du_pos _ hc2
  set γ := -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)
  have hfrac : mf R * R / (mf R * R + e2) < 1 := (div_lt_one hc2).2 (by linarith)
  have hfrac0 : 0 ≤ mf R * R / (mf R * R + e2) := div_nonneg hz hc2.le
  have hneg : γ * (mf R * R / (mf R * R + e2)) - 1 < 0 := by
    rcases le_or_gt γ 0 with hγ0 | hγ0
    · nlinarith
    · nlinarith
  have : P.ox_β * P.ox_du (mf R * R + e2) * (γ * (mf R * R / (mf R * R + e2)) - 1) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg
  rw [← hid] at this
  by_contra hle
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (not_lt.1 hle) hD.le]

end OXPrefs

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, pp. 532–534 (the nonmonetary steady state at the origin): zero saving solves the
Euler equation `u'(e₁ − m) = βu'(mR + e₂)R` iff `R = R_aut`. -/
theorem ox_offer_origin {R : ℝ} :
    E.ox_P.ox_du (E.ox_e1 - 0) = E.ox_P.ox_β * E.ox_P.ox_du (0 * R + E.ox_e2) * R ↔
      R = E.ox_Raut := by
  have hd := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  simp only [sub_zero, zero_mul, zero_add]
  unfold ox_Raut
  rw [eq_div_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- Miao, p. 534: the slope of the offer curve `z = m(R)R` at the origin (`m(R_aut) = 0`) is
`dz/dm = R_aut`. -/
theorem ox_offer_slope_origin {mf : ℝ → ℝ} {m' : ℝ} (hm : HasDerivAt mf m' E.ox_Raut)
    (h0 : mf E.ox_Raut = 0) (hm' : m' ≠ 0) :
    HasDerivAt (fun R => mf R * R) (m' * E.ox_Raut) E.ox_Raut ∧
      m' * E.ox_Raut / m' = E.ox_Raut := by
  refine ⟨?_, by field_simp⟩
  have : HasDerivAt (fun R => mf R * R) (m' * E.ox_Raut + mf E.ox_Raut * 1) E.ox_Raut :=
    hm.mul (hasDerivAt_id' E.ox_Raut)
  simpa [h0] using this

/-- Miao, p. 534 (monetary steady states of the special case): with `g_n = g_m = 1`, the
constant path `m` is a monetary equilibrium iff `m ∈ (0, e₁)` and `u'(e₁ − m) = βu'(e₂ + m)`,
i.e. it lies on the 45° line with `R = 1`. -/
theorem ox_offer_steady_iff (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) {mh : ℝ} :
    E.ox_EulerRel mh mh ↔ 0 < mh ∧ mh < E.ox_e1 ∧
      E.ox_P.ox_du (E.ox_e1 - mh) = E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + mh) := by
  constructor
  · intro h
    have := (E.ox_eulerRel_const_iff h.1 h.2.1).1 h
    rw [hgn, hgm, div_one, mul_one, one_mul] at this
    exact ⟨h.1, h.2.1, this⟩
  · rintro ⟨h0, he, h⟩
    refine (E.ox_eulerRel_const_iff h0 he).2 ?_
    rw [hgn, hgm, div_one, mul_one, one_mul]; exact h

/-- Miao, p. 534: with `g_n = g_m = 1` there is a monetary steady state iff the slope of the
offer curve at the origin is below one, `R_aut < 1` (Proposition 16.1.1). -/
theorem ox_offer_steady_exists_iff (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) :
    (∃ mh, E.ox_EulerRel mh mh) ↔ E.ox_Raut < 1 := by
  constructor
  · rintro ⟨mh, h⟩
    have := E.proposition_16_1_1_necessity (E.ox_ofSaving_isMonetary (mh := fun _ => mh)
      fun _ _ => h)
    rwa [hgn, hgm, mul_one] at this
  · intro hR
    obtain ⟨mh, ⟨h0, he, hroot⟩, -⟩ :=
      E.proposition_16_1_1_root (by rw [hgn, hgm, mul_one]; exact hR)
    exact ⟨mh, (E.ox_eulerRel_const_iff h0 he).2 hroot⟩

/-- Miao, p. 535: along a monetary equilibrium whose real balances vanish, `m̂_t → 0`, the
interest rate tends to `R_aut` and the gross inflation rate `p_{t+1}/p_t = q_t/q_{t+1}` tends to
`1/R_aut`, the inverse of the slope of the offer curve at the origin. -/
theorem ox_R_tendsto_Raut {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m)
    (h0 : Tendsto (E.ox_mhat q) atTop (𝓝 0)) :
    Tendsto (fun t => q (t + 1) / q t) atTop (𝓝 E.ox_Raut) ∧
      Tendsto (fun t => q t / q (t + 1)) atTop (𝓝 E.ox_Raut⁻¹) := by
  set x := E.ox_mhat q
  have hx1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 0) := h0.comp (tendsto_add_atTop_nat 1)
  have hc1 : ContinuousAt E.ox_P.ox_du (E.ox_e1 - 0) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by simpa using E.ox_e1_pos))
  have hc2 : ContinuousAt E.ox_P.ox_du (E.ox_e2 + E.ox_gn * 0) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by simpa using E.ox_e2_pos))
  have hp2 := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  have hlhs : Tendsto (fun t => E.ox_P.ox_du (E.ox_e1 - x t) /
      (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (t + 1)))) atTop
      (𝓝 (E.ox_P.ox_du (E.ox_e1 - 0) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * 0)))) :=
    (hc1.tendsto.comp (h0.const_sub _)).div
      ((hc2.tendsto.comp ((hx1.const_mul _).const_add _)).const_mul _) (by simpa using
        (mul_pos hβ hp2).ne')
  simp only [sub_zero, mul_zero, add_zero] at hlhs
  have hR : Tendsto (fun t => q (t + 1) / q t) atTop (𝓝 E.ox_Raut) := by
    refine hlhs.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (E.eq_16_6 h ht).1
  refine ⟨hR, ?_⟩
  have hRa : E.ox_Raut ≠ 0 := by
    unfold ox_Raut; have := E.ox_P.ox_du_pos _ E.ox_e1_pos; positivity
  refine (hR.inv₀ hRa).congr' ?_
  filter_upwards with t
  rw [inv_div]

end OXEconomy

/-- Local stability of a steady state (Miao, p. 535, Figure 16.3): if `f(x*) = x*` and
`|f'(x*)| < 1`, every path `x_{n+1} = f(x_n)` starting close to `x*` stays at least as close
and converges to `x*`. -/
theorem ox_fixed_stable {f : ℝ → ℝ} {xs f' : ℝ} (hfix : f xs = xs) (hf : HasDerivAt f f' xs)
    (hlt : |f'| < 1) : ∃ δ > 0, ∀ x0, |x0 - xs| < δ →
      (∀ n, |f^[n] x0 - xs| ≤ |x0 - xs|) ∧ Tendsto (fun n => f^[n] x0) atTop (𝓝 xs) := by
  set k := (|f'| + 1) / 2
  have hk1 : k < 1 := by simp only [k]; linarith
  have hk0 : 0 ≤ k := by simp only [k]; positivity
  have hε : 0 < k - |f'| := by simp only [k]; linarith
  have ho := (hasDerivAt_iff_isLittleO.1 hf).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ho
  have hstep : ∀ x, |x - xs| < δ → |f x - xs| ≤ k * |x - xs| := fun x hx => by
    have h := hball (show dist x xs < δ by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |f x - xs| ≤ |f x - xs - (x - xs) * f'| + |(x - xs) * f'| := by
      have := abs_add_le (f x - xs - (x - xs) * f') ((x - xs) * f')
      simpa using this
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (x - xs)]
  refine ⟨δ, hδ, fun x0 hx0 => ?_⟩
  have hiter : ∀ n, |f^[n] x0 - xs| ≤ k ^ n * |x0 - xs| := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt' : |f^[n] x0 - xs| < δ :=
        lt_of_le_of_lt (ih.trans (mul_le_of_le_one_left (abs_nonneg _)
          (pow_le_one₀ hk0 hk1.le))) hx0
      rw [Function.iterate_succ_apply']
      calc |f (f^[n] x0) - xs| ≤ k * |f^[n] x0 - xs| := hstep _ hlt'
        _ ≤ k * (k ^ n * |x0 - xs|) := mul_le_mul_of_nonneg_left ih hk0
        _ = k ^ (n + 1) * |x0 - xs| := by ring
  refine ⟨fun n => (hiter n).trans (mul_le_of_le_one_left (abs_nonneg _)
    (pow_le_one₀ hk0 hk1.le)), ?_⟩
  have hk : Tendsto (fun n => k ^ n * |x0 - xs|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |x0 - xs|
  have : Tendsto (fun n => f^[n] x0 - xs) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using hiter n) hk
  simpa using this.add_const xs

/-- Instability of a steady state (Miao, p. 534, Figure 16.2): if `f(x*) = x*` and
`|f'(x*)| > 1`, every path starting at `x₀ ≠ x*` eventually leaves a fixed neighbourhood. -/
theorem ox_fixed_unstable {f : ℝ → ℝ} {xs f' : ℝ} (hfix : f xs = xs) (hf : HasDerivAt f f' xs)
    (hgt : 1 < |f'|) : ∃ δ > 0, ∀ x0, x0 ≠ xs → ∃ n, δ ≤ |f^[n] x0 - xs| := by
  set k := (|f'| + 1) / 2
  have hk1 : 1 < k := by simp only [k]; linarith
  have hε : 0 < |f'| - k := by simp only [k]; linarith
  have ho := (hasDerivAt_iff_isLittleO.1 hf).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ho
  have hstep : ∀ x, |x - xs| < δ → k * |x - xs| ≤ |f x - xs| := fun x hx => by
    have h := hball (show dist x xs < δ by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |(x - xs) * f'| ≤ |f x - xs| + |f x - xs - (x - xs) * f'| := by
      have := abs_add_le (f x - xs) ((x - xs) * f' - (f x - xs))
      have e : (f x - xs) + ((x - xs) * f' - (f x - xs)) = (x - xs) * f' := by ring
      rwa [e, abs_sub_comm ((x - xs) * f')] at this
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (x - xs)]
  refine ⟨δ, hδ, fun x0 hx0 => ?_⟩
  by_contra hall
  push Not at hall
  have hiter : ∀ n, k ^ n * |x0 - xs| ≤ |f^[n] x0 - xs| := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc k ^ (n + 1) * |x0 - xs| = k * (k ^ n * |x0 - xs|) := by ring
        _ ≤ k * |f^[n] x0 - xs| := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ |f (f^[n] x0) - xs| := hstep _ (hall n)
  have hpos : 0 < |x0 - xs| := abs_pos.2 (sub_ne_zero.2 hx0)
  have htend : Tendsto (fun n => k ^ n * |x0 - xs|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hk1).atTop_mul_const hpos
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop δ).exists
  linarith [hiter n, hall n]

/-- **Correction** (Miao, p. 534: "unstable iff `|dm_{t+1}/dm_t| > 1`"): `f(x) = x + x³` has the
fixed point `0` with `f'(0) = 1`, yet every path from `x₀ > 0` leaves every bounded set, so `0`
is unstable without `|f'(0)| > 1`. -/
theorem ox_unstable_counterexample :
    HasDerivAt (fun x : ℝ => x + x ^ 3) 1 0 ∧ ∀ x0 : ℝ, 0 < x0 → ∀ B : ℝ, ∃ n,
      B < (fun x : ℝ => x + x ^ 3)^[n] x0 := by
  refine ⟨?_, ?_⟩
  · have h : HasDerivAt (fun x : ℝ => x + x ^ 3) (1 + (3 : ℕ) * (0 : ℝ) ^ (3 - 1)) 0 :=
      (hasDerivAt_id' (0 : ℝ)).add (hasDerivAt_pow 3 (0 : ℝ))
    convert h using 1
    norm_num
  intro x0 hx0 B
  set f := fun x : ℝ => x + x ^ 3
  have hiter : ∀ n : ℕ, x0 + n * x0 ^ 3 ≤ f^[n] x0 := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hge : x0 ≤ f^[n] x0 := by
        have : (0 : ℝ) ≤ n * x0 ^ 3 := by positivity
        linarith
      have : x0 ^ 3 ≤ (f^[n] x0) ^ 3 := pow_le_pow_left₀ hx0.le hge 3
      simp only [f]; push_cast; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - x0) / x0 ^ 3)
  refine ⟨n, ?_⟩
  have h3 : 0 < x0 ^ 3 := by positivity
  rw [div_lt_iff₀ h3] at hn
  linarith [hiter n]

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, p. 535 (indeterminacy): if the equilibrium relation is given near a monetary steady
state `m*` by a map `f` (every `(a, f a)` with `a` near `m*` solves the saving difference
equation) with `|f'(m*)| < 1`, then for every `m₁` close to `m*` the path `m̂_t = f^{t−1}(m₁)` is a
monetary equilibrium converging to `m*`: a continuum of equilibria. -/
theorem ox_indeterminacy {f : ℝ → ℝ} {ms f' r : ℝ} (hr : 0 < r) (hfix : f ms = ms)
    (hf : HasDerivAt f f' ms) (hlt : |f'| < 1)
    (hrel : ∀ a, |a - ms| < r → E.ox_EulerRel a (f a)) :
    ∃ δ > 0, ∀ m1, |m1 - ms| < δ →
      E.ox_IsMonetary (E.ox_qOf fun t => f^[t - 1] m1) (fun t => E.ox_e1 - f^[t - 1] m1)
        (fun t => E.ox_e2 + E.ox_gn * f^[t + 1 - 1] m1) (fun t => E.ox_M t / E.ox_N t) ∧
      Tendsto (fun n => f^[n] m1) atTop (𝓝 ms) := by
  obtain ⟨δ, hδ, hst⟩ := ox_fixed_stable hfix hf hlt
  refine ⟨min δ r, lt_min hδ hr, fun m1 hm1 => ?_⟩
  obtain ⟨hstay, htend⟩ := hst m1 (lt_of_lt_of_le hm1 (min_le_left _ _))
  refine ⟨E.ox_ofSaving_isMonetary (mh := fun t => f^[t - 1] m1) fun t ht => ?_, htend⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Function.iterate_succ_apply']
  exact hrel _ (lt_of_le_of_lt (hstay s) (lt_of_lt_of_le hm1 (min_le_right _ _)))

/-- Miao, pp. 535–536 (Figure 16.4, a two-period cycle): if `(m_a, m_b)` and `(m_b, m_a)` both
solve the saving difference equation, real balances alternating `m_a, m_b, m_a, …` form a
monetary equilibrium. -/
theorem ox_two_cycle {ma mb : ℝ} (hab : E.ox_EulerRel ma mb) (hba : E.ox_EulerRel mb ma) :
    E.ox_IsMonetary (E.ox_qOf fun t => if Even t then mb else ma)
      (fun t => E.ox_e1 - if Even t then mb else ma)
      (fun t => E.ox_e2 + E.ox_gn * if Even (t + 1) then mb else ma)
      (fun t => E.ox_M t / E.ox_N t) := by
  refine E.ox_ofSaving_isMonetary (mh := fun t => if Even t then mb else ma) fun t _ => ?_
  rcases Nat.even_or_odd t with he | ho
  · have : ¬ Even (t + 1) := Nat.not_even_iff_odd.2 he.add_one
    simp only [he, this, ↓reduceIte]; exact hba
  · have : Even (t + 1) := ho.add_one
    have hne : ¬ Even t := Nat.not_even_iff_odd.2 ho
    simp only [hne, this, ↓reduceIte]; exact hab

end OXEconomy

end Miao.OverlappingGenerations
