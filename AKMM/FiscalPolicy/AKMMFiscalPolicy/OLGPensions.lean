/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Debt and pensions with overlapping generations

AKMM, §15.6, (15.19)–(15.24), pp. 462–463, footnote 10.

A small open two-period OLG economy with exogenous `r`: cohorts `N_t = (1 + n)^t`, only the
young work, earning `y_t = (1 + γ)^tω`; PAYG pensions financed by the tax `τ_p`, public goods
`G_t = gY_t`, a flat tax `τ_t` and one-period debt.

* The young share `N_t/(N_t + N_{t−1}) = (1 + n)/(2 + n)` (`olg_young_share`); the balanced PAYG
  pension `p_t = (1 + n)τ_py_t` (`olg_pension`); the budget in ratios
  `g + (1 + r)b_{t−1}/((1 + n)(1 + γ)) = τ_t + b_t` (`olg_budget_ratio`).
* (15.21): the flow budgets (15.19)–(15.20) hold for some saving iff the lifetime budget holds
  (`eq_15_21`); (15.22): the Euler equation at an interior optimum (`eq_15_22`); with log utility
  `c_y = W/(1 + β)`, `c_o = β(1 + r)W/(1 + β)` (`olg_log_consumption`).
* **PAYG is implicit debt** (15.23)–(15.24): with `b_{p,t} = τ_py_t` and
  `1 + r_p = (1 + n)(1 + γ)` the two budget sets coincide (`olg_payg_eq_debt`).
* The present value of the young's income rises with `τ_p` iff `(1 + n)(1 + γ) > 1 + r`
  (`olg_pv_hasDerivAt`, `olg_pv_increasing_iff`). The book's "iff `γ + n > r`" uses
  `(1 + n)(1 + γ) ≈ 1 + n + γ` and is not exact (`olg_pv_approx_false`).
* **Pareto improvement under dynamic inefficiency**: if `(1 + n)(1 + γ) > 1 + r`, introducing
  `τ_p > 0` gives the initial old a positive pension and strictly enlarges every young cohort's
  budget set (`olg_payg_pareto`); if `(1 + n)(1 + γ) < 1 + r` it strictly shrinks it
  (`olg_payg_tax_on_young`).
* **The tax holiday** (zero initial debt, `τ_t = 0`, `B_t = gY_t`, repaid at `t + 1`): debt ratio
  `b_t = g` and `τ_{t+1} = g(1 + (1 + r)/((1 + n)(1 + γ)))` (`olg_holiday_taxes`); with log
  utility generation `t` consumes more in both periods and generation `t + 1` less; so aggregate
  consumption rises at `t` and falls at `t + 2` (`olg_holiday_aggregate`).

Departures: §15.6 is a small open economy; the closed-economy dynamic-inefficiency results of the
`OverlappingGenerations` dependency (Miao Ch. 16) have a different model and are not used. The
aggregate-consumption claims are proved for log utility (consumption proportional to lifetime
income); the book argues for general utility.
-/

namespace AKMM.FiscalPolicy

/-- AKMM, p. 462: with `N_t = (1 + n)^t`, the young share is `N_t/(N_t + N_{t−1}) = (1 + n)/(2 + n)`
(`n > −1`). -/
theorem olg_young_share {n : ℝ} (hn : -1 < n) (t : ℕ) :
    (1 + n) ^ (t + 1) / ((1 + n) ^ (t + 1) + (1 + n) ^ t) = (1 + n) / (2 + n) := by
  have h1 : 0 < 1 + n := by linarith
  have hp : 0 < (1 + n) ^ t := pow_pos h1 t
  rw [div_eq_div_iff (by positivity) (by linarith), pow_succ]
  ring

/-- AKMM, p. 462: a balanced PAYG system `p_tN_{t−1} = τ_py_tN_t` with `N_t = (1 + n)N_{t−1}` pays
`p_t = (1 + n)τ_py_t`. -/
theorem olg_pension {n τp yt Nm pt : ℝ} (hN : Nm ≠ 0) (h : pt * Nm = τp * yt * ((1 + n) * Nm)) :
    pt = (1 + n) * τp * yt := by
  have := mul_right_cancel₀ hN (show pt * Nm = (1 + n) * τp * yt * Nm by rw [h]; ring)
  exact this

/-- AKMM, p. 462: dividing the budget `G_t + p_tN_{t−1} + (1 + r)B_{t−1} = (τ_p + τ_t)Y_t + B_t` by
`Y_t = (1 + n)(1 + γ)Y_{t−1}`, with `G_t = gY_t` and the pension self-financing
(`p_tN_{t−1} = τ_pY_t`), gives `g + (1 + r)b_{t−1}/((1 + n)(1 + γ)) = τ_t + b_t`. -/
theorem olg_budget_ratio {g r n γ τp τt Ym Bm B P : ℝ} (hY : Ym ≠ 0)
    (hng : (1 + n) * (1 + γ) ≠ 0) (hP : P = τp * ((1 + n) * (1 + γ) * Ym))
    (h : g * ((1 + n) * (1 + γ) * Ym) + P + (1 + r) * Bm =
      (τp + τt) * ((1 + n) * (1 + γ) * Ym) + B) :
    g + (1 + r) / ((1 + n) * (1 + γ)) * (Bm / Ym) = τt + B / ((1 + n) * (1 + γ) * Ym) := by
  rw [hP] at h
  have hn1 : 1 + n ≠ 0 := left_ne_zero_of_mul hng
  have hγ1 : 1 + γ ≠ 0 := right_ne_zero_of_mul hng
  have key : g * ((1 + n) * (1 + γ) * Ym) + (1 + r) * Bm =
      τt * ((1 + n) * (1 + γ) * Ym) + B := by linarith
  have e1 : g + (1 + r) / ((1 + n) * (1 + γ)) * (Bm / Ym) =
      (g * ((1 + n) * (1 + γ) * Ym) + (1 + r) * Bm) / ((1 + n) * (1 + γ) * Ym) := by
    field_simp
  have e2 : τt + B / ((1 + n) * (1 + γ) * Ym) =
      (τt * ((1 + n) * (1 + γ) * Ym) + B) / ((1 + n) * (1 + γ) * Ym) := by
    field_simp
  rw [e1, e2, key]

/-- **(15.21)** (AKMM, p. 462): the budgets (15.19) `c_y + a = (1 − τ_t − τ_p)y_t` and (15.20)
`c_o = (1 + r)a + p_{t+1}` with `p_{t+1} = (1 + n)(1 + γ)τ_py_t` hold for some saving `a` iff
`c_y + c_o/(1 + r) = (1 − τ_t − τ_p + (1 + n)(1 + γ)τ_p/(1 + r))y_t`. -/
theorem eq_15_21 {r n γ τt τp yt cy co : ℝ} (hr : 1 + r ≠ 0) :
    (∃ a, cy + a = (1 - τt - τp) * yt ∧ co = (1 + r) * a + (1 + n) * (1 + γ) * τp * yt) ↔
      cy + co / (1 + r) = (1 - τt - τp + (1 + n) * (1 + γ) / (1 + r) * τp) * yt := by
  constructor
  · rintro ⟨a, h1, h2⟩
    rw [h2]
    field_simp
    linear_combination (1 + r) * h1
  · intro h
    refine ⟨(1 - τt - τp) * yt - cy, by ring, ?_⟩
    field_simp at h
    linear_combination h

/-- **(15.22)** (AKMM, p. 463): if `c_y` maximises `u(c_y) + βu((1 + r)(W − c_y))` (the lifetime
budget (15.21) with wealth `W`) and `u` is differentiable at `c_y` and `c_o = (1 + r)(W − c_y)` with
`u′(c_y) ≠ 0`, then `1 = (1 + r)βu′(c_o)/u′(c_y)`. -/
theorem eq_15_22 {u : ℝ → ℝ} {β r W cy u'y u'o : ℝ} (hu'y : u'y ≠ 0)
    (hmax : ∀ c, u c + β * u ((1 + r) * (W - c)) ≤ u cy + β * u ((1 + r) * (W - cy)))
    (hy : HasDerivAt u u'y cy) (ho : HasDerivAt u u'o ((1 + r) * (W - cy))) :
    1 = (1 + r) * β * u'o / u'y := by
  have hin : HasDerivAt (fun c => (1 + r) * (W - c)) ((1 + r) * (0 - 1)) cy :=
    ((hasDerivAt_const cy W).sub (hasDerivAt_id cy)).const_mul (1 + r)
  have hd := hy.add ((ho.comp cy hin).const_mul β)
  have hloc : IsLocalMax (fun c => u c + β * u ((1 + r) * (W - c))) cy :=
    Filter.Eventually.of_forall hmax
  have := hloc.hasDerivAt_eq_zero hd
  field_simp
  linear_combination this

/-- AKMM, p. 463, with log utility: the Euler equation (15.22) and the lifetime budget give
`c_y = W/(1 + β)` and `c_o = β(1 + r)W/(1 + β)` (`β > 0`, `c_y > 0`). -/
theorem olg_log_consumption {β r W cy co : ℝ} (hβ : 0 < β) (hcy : cy ≠ 0) (hco : co ≠ 0)
    (hr : 1 + r ≠ 0) (hE : 1 = (1 + r) * β * (1 / co) / (1 / cy)) (hW : cy + co / (1 + r) = W) :
    cy = W / (1 + β) ∧ co = β * (1 + r) * W / (1 + β) := by
  have hco' : co = β * (1 + r) * cy := by
    field_simp at hE
    linarith
  have h1β : (1 + β) ≠ 0 := by linarith
  rw [hco'] at hW
  field_simp at hW
  constructor
  · rw [← hW]
    field_simp
  · rw [hco', ← hW]
    field_simp

/-- **PAYG is implicit debt** (AKMM, p. 463): with forced bond purchases `b_{p,t} = τ_py_t` at
`1 + r_p = (1 + n)(1 + γ)`, the budgets (15.23)–(15.24) are equivalent to (15.19)–(15.20). -/
theorem olg_payg_eq_debt {r n γ τt τp yt cy a co : ℝ} :
    (cy + a = (1 - τt - τp) * yt ∧ co = (1 + r) * a + (1 + n) * (1 + γ) * τp * yt) ↔
      (cy + a + τp * yt = (1 - τt) * yt ∧ co = (1 + r) * a + (1 + n) * (1 + γ) * (τp * yt)) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨by linarith, by rw [h2]; ring⟩

/-- The present value of the young's lifetime income (the right side of (15.21)). -/
noncomputable def olgPV (r n γ τt yt τp : ℝ) : ℝ :=
  (1 - τt - τp + (1 + n) * (1 + γ) / (1 + r) * τp) * yt

/-- AKMM, p. 463: `∂/∂τ_p` of the right side of (15.21) is `((1 + n)(1 + γ)/(1 + r) − 1)y_t`. -/
theorem olg_pv_hasDerivAt {r n γ τt yt τp : ℝ} :
    HasDerivAt (olgPV r n γ τt yt) (((1 + n) * (1 + γ) / (1 + r) - 1) * yt) τp := by
  have h := ((hasDerivAt_id τp).mul_const (((1 + n) * (1 + γ) / (1 + r) - 1) * yt)).const_add
    ((1 - τt) * yt)
  refine (h.congr_deriv (one_mul _)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [olgPV, id]
  ring

/-- AKMM, p. 463: "the pension system increases the present value of household income for the
young if and only if wage growth exceeds the interest rate": for `y_t > 0`, `1 + r > 0`, the
derivative is positive iff `(1 + n)(1 + γ) > 1 + r`. -/
theorem olg_pv_increasing_iff {r n γ yt : ℝ} (hy : 0 < yt) (hr : 0 < 1 + r) :
    0 < ((1 + n) * (1 + γ) / (1 + r) - 1) * yt ↔ 1 + r < (1 + n) * (1 + γ) := by
  rw [mul_pos_iff_of_pos_right hy, sub_pos, one_lt_div hr]

/-- AKMM, p. 463: the printed criterion "iff `γ + n > r`" is the approximation
`(1 + n)(1 + γ) ≈ 1 + n + γ`; it is not exact: at `n = γ = 1/10`, `r = 41/200`, the pension raises
the young's present value (`(1 + n)(1 + γ) = 1.21 > 1.205`) although `γ + n = 0.2 < r`. -/
theorem olg_pv_approx_false :
    (1 + (41 / 200 : ℝ)) < (1 + 1 / 10) * (1 + 1 / 10) ∧ (1 / 10 + 1 / 10 : ℝ) < 41 / 200 := by
  constructor <;> norm_num

/-- The young's budget set at pension tax `τ_p`: `c_y + c_o/(1 + r) ≤ PV(τ_p)`. -/
def olgBudgetSet (r n γ τt yt τp : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 + x.2 / (1 + r) ≤ olgPV r n γ τt yt τp}

/-- **Pareto improvement** (AKMM, p. 463): "if the interest rate is lower than the wage growth
rate … introducing a PAYG pension system is Pareto improving": with `(1 + n)(1 + γ) > 1 + r`,
`τ_p > 0`, `y > 0`, the initial old receive a positive pension `(1 + n)τ_py₀` and every young
cohort's budget set strictly grows. -/
theorem olg_payg_pareto {r n γ τt τp y0 : ℝ} (hr : 0 < 1 + r) (hn : -1 < n)
    (hdi : 1 + r < (1 + n) * (1 + γ)) (hτ : 0 < τp) (hy0 : 0 < y0) :
    0 < (1 + n) * τp * y0 ∧
      ∀ yt, 0 < yt → olgBudgetSet r n γ τt yt 0 ⊂ olgBudgetSet r n γ τt yt τp := by
  refine ⟨mul_pos (mul_pos (by linarith) hτ) hy0, fun yt hyt => ?_⟩
  have hgt : olgPV r n γ τt yt 0 < olgPV r n γ τt yt τp := by
    unfold olgPV
    have : 0 < ((1 + n) * (1 + γ) / (1 + r) - 1) * τp * yt :=
      mul_pos (mul_pos (by rw [sub_pos, one_lt_div hr]; exact hdi) hτ) hyt
    nlinarith
  refine ⟨fun x hx => le_trans hx hgt.le, fun hsub => ?_⟩
  have hmem : (olgPV r n γ τt yt τp, (0 : ℝ)) ∈ olgBudgetSet r n γ τt yt τp := by
    simp [olgBudgetSet]
  have := hsub hmem
  simp only [olgBudgetSet, Set.mem_ofPred_eq, zero_div, add_zero] at this
  linarith

/-- AKMM, p. 463: "if the interest rate is larger than the growth rate of output … the pension
system is effectively a tax on the young generation": with `(1 + n)(1 + γ) < 1 + r`, `τ_p > 0`,
`y_t > 0`, the young's budget set strictly shrinks. -/
theorem olg_payg_tax_on_young {r n γ τt τp yt : ℝ} (hr : 0 < 1 + r)
    (hde : (1 + n) * (1 + γ) < 1 + r) (hτ : 0 < τp) (hyt : 0 < yt) :
    olgBudgetSet r n γ τt yt τp ⊂ olgBudgetSet r n γ τt yt 0 := by
  have hlt : olgPV r n γ τt yt τp < olgPV r n γ τt yt 0 := by
    unfold olgPV
    have : ((1 + n) * (1 + γ) / (1 + r) - 1) * τp * yt < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (by rw [sub_neg, div_lt_one hr]; exact hde) hτ) hyt
    nlinarith
  refine ⟨fun x hx => le_trans hx hlt.le, fun hsub => ?_⟩
  have hmem : (olgPV r n γ τt yt 0, (0 : ℝ)) ∈ olgBudgetSet r n γ τt yt 0 := by
    simp [olgBudgetSet]
  have := hsub hmem
  simp only [olgBudgetSet, Set.mem_ofPred_eq, zero_div, add_zero] at this
  linarith

/-- AKMM, p. 463, **the tax holiday**: with zero initial debt, `τ_t = 0` and the deficit financed
by `b_t`, the budget in ratios gives `b_t = g`; repaying at `t + 1` (`b_{t+1} = 0`) requires
`τ_{t+1} = g(1 + (1 + r)/((1 + n)(1 + γ)))`, against `τ = g` without the holiday. -/
theorem olg_holiday_taxes {g r n γ bt τ1 : ℝ}
    (h0 : g + (1 + r) / ((1 + n) * (1 + γ)) * 0 = 0 + bt)
    (h1 : g + (1 + r) / ((1 + n) * (1 + γ)) * bt = τ1 + 0) :
    bt = g ∧ τ1 = g * (1 + (1 + r) / ((1 + n) * (1 + γ))) := by
  have hb : bt = g := by linarith
  refine ⟨hb, ?_⟩
  rw [hb] at h1
  linarith

/-- AKMM, p. 463, **aggregate consumption after the tax holiday** (log utility, consumption
`κ_yW`, `κ_oW` proportional to lifetime income with `κ_y, κ_o > 0`, cohorts `N > 0`): generation
`t` gains lifetime income (its tax falls from `g > 0` to `0`) and generation `t + 1` loses (its tax
rises by `g(1 + r)/((1 + n)(1 + γ)) > 0`); the old at `t` and the young at `t + 2` are unaffected.
Hence `C_t = c_{y,t}N_t + c_{o,t}N_{t−1}` rises and `C_{t+2} = c_{y,t+2}N_{t+2} + c_{o,t+2}N_{t+1}`
falls. -/
theorem olg_holiday_aggregate {κy κo W0 Wt Wt1 W2 g d yt yt1 Nm Nt Nt1 Nt2 : ℝ}
    (hκy : 0 < κy) (hκo : 0 < κo) (hg : 0 < g) (hd : 0 < d) (hyt : 0 < yt) (hyt1 : 0 < yt1)
    (hNt : 0 < Nt) (hNt1 : 0 < Nt1) :
    κy * Wt * Nt + κo * W0 * Nm < κy * (Wt + g * yt) * Nt + κo * W0 * Nm ∧
      κy * W2 * Nt2 + κo * (Wt1 - d * yt1) * Nt1 < κy * W2 * Nt2 + κo * Wt1 * Nt1 := by
  constructor
  · nlinarith [mul_pos (mul_pos (mul_pos hκy hg) hyt) hNt]
  · nlinarith [mul_pos (mul_pos (mul_pos hκo hd) hyt1) hNt1]

end AKMM.FiscalPolicy
