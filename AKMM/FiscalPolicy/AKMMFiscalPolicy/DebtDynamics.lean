/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.LinearODE
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Government budget and the dynamics of the debt-to-GDP ratio

AKMM, §15.2, (15.1)–(15.2), pp. 441–444.

The government budget constraint (15.1) `G_t + T_t + i_tB_{t−1} = Rev_t + B_t − B_{t−1}`,
with the primary deficit `D_t = G_t + T_t − Rev_t`, gives `B_t = B_{t−1}(1 + i_t) + D_t`
(`dd_nominal_debt`). Dividing by nominal GDP, which grows by `(1 + γ_t)(1 + π_t)`, gives
`b_t = b_{t−1}(1 + i_t)/((1 + γ_t)(1 + π_t)) + d_t` (`dd_ratio_nominal`), and with the ex post
real rate `1 + r_t = (1 + i_t)/(1 + π_t)`, `b_t = b_{t−1}(1 + r_t)/(1 + γ_t) + d_t`
(`dd_ratio_real`). With constant rates this is Cochrane's discrete debt-to-GDP equation
(`dd_ratio_const`, from `Cochrane.FiscalConstraints.LinearODE.debt_gdp_discrete`).

* With a zero primary deficit the ratio rises iff `r > γ` (`dd_zero_deficit_rises_iff`).
* (15.2): `b_t > b_{t−1}` iff `d_t > (γ_t − r_t)b_{t−1}/(1 + γ_t)` (`eq_15_2`).
* With constant `r, γ, d` and `γ ≠ r` the unique stationary ratio is `b* = d(1 + γ)/(γ − r)`
  (`dd_stationary_iff`); the solution is `b_t − b* = ((1 + r)/(1 + γ))^t(b₀ − b*)`
  (`dd_sub_stationary`); for `−1 < r < γ` every path converges to `b*` (`dd_tendsto_stationary`)
  and for `r > γ`, `d > 0`, `b₀ ≥ 0` the ratio diverges to `+∞` (`dd_tendsto_atTop`).
* The box on p. 444: at `b = 1`, `γ = 0.03`, `r = 0.02` the largest deficit that does not raise
  the ratio is `0.01/1.03 ∈ (0.0097, 0.0098)`, and a 3% deficit is stable at `b* = 3.09`
  (`dd_box_threshold`, `dd_box_309`).

Departures: none. Time-varying `r_t`, `γ_t` are kept where the book keeps them.
-/

namespace AKMM.FiscalPolicy

open Filter Topology

/-- AKMM, (15.1), p. 441: with the primary deficit `D_t = G_t + T_t − Rev_t`, the budget
constraint `G_t + T_t + i_tB_{t−1} = Rev_t + B_t − B_{t−1}` is `B_t = B_{t−1}(1 + i_t) + D_t`
(p. 443). -/
theorem dd_nominal_debt {G T i Bm Rev B : ℝ} (h : G + T + i * Bm = Rev + B - Bm) :
    B = Bm * (1 + i) + (G + T - Rev) := by
  linarith

/-- AKMM, p. 443: dividing `B_t = B_{t−1}(1 + i_t) + D_t` by nominal GDP
`Y_t = (1 + γ_t)(1 + π_t)Y_{t−1}` gives `b_t = b_{t−1}(1 + i_t)/((1 + γ_t)(1 + π_t)) + d_t`. -/
theorem dd_ratio_nominal {Bm B D i γ π' Ym : ℝ} (hY : Ym ≠ 0) (hγ : 1 + γ ≠ 0)
    (hπ : 1 + π' ≠ 0) (hB : B = Bm * (1 + i) + D) :
    B / ((1 + γ) * (1 + π') * Ym) =
      Bm / Ym * ((1 + i) / ((1 + γ) * (1 + π'))) + D / ((1 + γ) * (1 + π') * Ym) := by
  rw [hB]
  field_simp

/-- AKMM, p. 444: with `1 + r_t = (1 + i_t)/(1 + π_t)` the ratio obeys
`b_t = b_{t−1}(1 + r_t)/(1 + γ_t) + d_t`. -/
theorem dd_ratio_real {bm b d i γ π' r : ℝ} (hγ : 1 + γ ≠ 0) (hπ : 1 + π' ≠ 0)
    (hr : 1 + r = (1 + i) / (1 + π')) (hb : b = bm * ((1 + i) / ((1 + γ) * (1 + π'))) + d) :
    b = bm * ((1 + r) / (1 + γ)) + d := by
  rw [hb, hr]
  field_simp

/-- AKMM, p. 444, with constant `r` and `γ`: the debt-to-GDP equation of Cochrane's §6.4.1
(`debt_gdp_discrete`, with surplus `s = −D`) is the book's
`b_{t+1} = b_t(1 + r)/(1 + γ) + d_{t+1}`. -/
theorem dd_ratio_const {B Y D : ℕ → ℝ} {r γ : ℝ}
    (hB : ∀ t, B (t + 1) = B t * (1 + r) + D (t + 1))
    (hY : ∀ t, Y (t + 1) = (1 + γ) * Y t) (hY0 : ∀ t, Y t ≠ 0) (hγ : 1 + γ ≠ 0) (t : ℕ) :
    B (t + 1) / Y (t + 1) = B t / Y t * ((1 + r) / (1 + γ)) + D (t + 1) / Y (t + 1) := by
  have h := Cochrane.FiscalConstraints.LinearODE.debt_gdp_discrete (b := B) (y := Y)
    (s := fun t => -D t) (r := r) (g := γ) (fun t => by rw [hB t]; ring) hY hY0 hγ t
  rw [h, neg_div]
  ring

/-- AKMM, p. 444: "When the primary deficit `d_t` is zero, the debt to GDP ratio will rise when
`r_t > γ_t`, and will fall when `r_t < γ_t`" (for positive debt). -/
theorem dd_zero_deficit_rises_iff {bm r γ : ℝ} (hbm : 0 < bm) (hγ : 0 < 1 + γ) :
    bm < bm * ((1 + r) / (1 + γ)) + 0 ↔ γ < r := by
  rw [add_zero, lt_mul_iff_one_lt_right hbm, one_lt_div hγ]
  constructor <;> intro h <;> linarith

/-- AKMM, (15.2), p. 444: debt rises, `b_t > b_{t−1}`, iff `d_t > (γ_t − r_t)b_{t−1}/(1 + γ_t)`. -/
theorem eq_15_2 {bm d r γ : ℝ} (hγ : 0 < 1 + γ) :
    bm < bm * ((1 + r) / (1 + γ)) + d ↔ (γ - r) / (1 + γ) * bm < d := by
  have : bm * ((1 + r) / (1 + γ)) = bm - (γ - r) / (1 + γ) * bm := by
    field_simp
    ring
  rw [this]
  constructor <;> intro h <;> linarith

/-- The stable debt-to-GDP ratio `b* = d(1 + γ)/(γ − r)` (AKMM, p. 444). -/
noncomputable def ddStationary (d r γ : ℝ) : ℝ := d * (1 + γ) / (γ - r)

/-- AKMM, p. 444: for `γ ≠ r`, `b` is a stationary point of `b ↦ b(1 + r)/(1 + γ) + d` iff
`b = d(1 + γ)/(γ − r)`; so the stationary ratio exists and is unique. -/
theorem dd_stationary_iff {b d r γ : ℝ} (hγ : 1 + γ ≠ 0) (hne : γ ≠ r) :
    b = b * ((1 + r) / (1 + γ)) + d ↔ b = ddStationary d r γ := by
  have hgr : γ - r ≠ 0 := sub_ne_zero.mpr hne
  unfold ddStationary
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- AKMM, p. 444: along `b_{t+1} = b_t(1 + r)/(1 + γ) + d`, the gap to the stationary ratio
evolves geometrically: `b_t − b* = ((1 + r)/(1 + γ))^t(b₀ − b*)`. -/
theorem dd_sub_stationary {b : ℕ → ℝ} {d r γ : ℝ} (hγ : 1 + γ ≠ 0) (hne : γ ≠ r)
    (hb : ∀ t, b (t + 1) = b t * ((1 + r) / (1 + γ)) + d) (t : ℕ) :
    b t - ddStationary d r γ = ((1 + r) / (1 + γ)) ^ t * (b 0 - ddStationary d r γ) := by
  have hs := (dd_stationary_iff (b := ddStationary d r γ) (d := d) hγ hne).mpr rfl
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hb n, pow_succ]
    have : b n * ((1 + r) / (1 + γ)) + d - ddStationary d r γ =
        (1 + r) / (1 + γ) * (b n - ddStationary d r γ) := by
      linear_combination (-1 : ℝ) * hs
    rw [this, ih]
    ring

/-- AKMM, p. 444, **global stability**: "given constant values for `r` and `γ > r`, any size
primary deficit is consistent with a stable debt to GDP ratio": for `−1 < r < γ` every path of
`b_{t+1} = b_t(1 + r)/(1 + γ) + d` converges to `b* = d(1 + γ)/(γ − r)`. -/
theorem dd_tendsto_stationary {b : ℕ → ℝ} {d r γ : ℝ} (hr : -1 < r) (hrg : r < γ)
    (hb : ∀ t, b (t + 1) = b t * ((1 + r) / (1 + γ)) + d) :
    Tendsto b atTop (𝓝 (ddStationary d r γ)) := by
  have hγ : 0 < 1 + γ := by linarith
  have h0 : 0 ≤ (1 + r) / (1 + γ) := div_nonneg (by linarith) hγ.le
  have h1 : (1 + r) / (1 + γ) < 1 := (div_lt_one hγ).mpr (by linarith)
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const
    (b 0 - ddStationary d r γ)
  rw [zero_mul] at hp
  have hfun : b = fun t => ((1 + r) / (1 + γ)) ^ t * (b 0 - ddStationary d r γ) +
      ddStationary d r γ := by
    funext t
    rw [← dd_sub_stationary hγ.ne' hrg.ne' hb t]
    ring
  rw [hfun]
  simpa using hp.add_const (ddStationary d r γ)

/-- AKMM, p. 444, **divergence**: "once the differential between `γ` and `r` changes sign,
stabilizing the debt to GDP ratio will require primary surpluses": for `r > γ > −1`, a constant
deficit `d > 0` and `b₀ ≥ 0`, the ratio diverges to `+∞`. -/
theorem dd_tendsto_atTop {b : ℕ → ℝ} {d r γ : ℝ} (hγ : -1 < γ) (hrg : γ < r) (hd : 0 < d)
    (hb0 : 0 ≤ b 0) (hb : ∀ t, b (t + 1) = b t * ((1 + r) / (1 + γ)) + d) :
    Tendsto b atTop atTop := by
  have hγ' : 0 < 1 + γ := by linarith
  have h1 : 1 < (1 + r) / (1 + γ) := (one_lt_div hγ').mpr (by linarith)
  have hs : ddStationary d r γ < 0 := by
    unfold ddStationary
    exact div_neg_of_pos_of_neg (by positivity) (by linarith)
  have hgap : 0 < b 0 - ddStationary d r γ := by linarith
  have hp := (tendsto_pow_atTop_atTop_of_one_lt h1).atTop_mul_const hgap
  have hfun : b = fun t => ((1 + r) / (1 + γ)) ^ t * (b 0 - ddStationary d r γ) +
      ddStationary d r γ := by
    funext t
    rw [← dd_sub_stationary hγ'.ne' (ne_of_lt hrg) hb t]
    ring
  rw [hfun]
  exact tendsto_atTop_add_const_right _ _ hp

/-- AKMM, p. 444 (box): at `b_{t−1} = 1`, `γ = 0.03`, `r = 0.02`, the largest primary deficit
consistent with debt not rising, `(γ − r)/(1 + γ) = 0.01/1.03`, is "approximately 1 percent":
it lies in `(0.0097, 0.0098)`. -/
theorem dd_box_threshold :
    (0.0097 : ℝ) < (0.03 - 0.02) / (1 + 0.03) * 1 ∧
      (0.03 - 0.02) / (1 + 0.03) * 1 < (0.0098 : ℝ) := by
  constructor <;> norm_num

/-- AKMM, p. 444 (box): with `r = 0.02`, `γ = 0.03`, a 3 percent primary deficit is consistent
with the stable ratio `b* = 3.09`, and `0.03 = (0.01/1.03) × 3.09`. -/
theorem dd_box_309 :
    ddStationary 0.03 0.02 0.03 = 3.09 ∧ (0.03 : ℝ) = (0.03 - 0.02) / (1 + 0.03) * 3.09 := by
  unfold ddStationary
  constructor <;> norm_num

end AKMM.FiscalPolicy
