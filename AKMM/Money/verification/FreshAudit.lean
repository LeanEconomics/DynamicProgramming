import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import OverlappingGenerations.OXExamples
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ClassicalMonetaryModel.MIUNonseparable
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.ContinuousOn
import Mathlib.Algebra.Order.Archimedean.Basic
import Monetarism.UnpleasantArithmetic
import TwoPeriodModel.TwoPeriod
import Mathlib.Topology.Order.Compact
import IncompleteMarkets.BWMoney
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The young's saving problem with fiat money

AKMM, §17.2.1, pp. 496–498 (Hornstein and Krusell). A young agent with endowment `a = ω_y`
and old-age income `b` (in the book `b = ω_o`) saves `s = p_{m,t}M′ ≥ 0` in money with gross
real return `R = p_{m,t+1}/p_{m,t}`, and maximises `log c_y + log c_o`,
`c_y = a − s`, `c_o = b + Rs`.

* `olgUtil`, `olgFeasible`, `olgOptimal`: the problem (17.1) in terms of real saving.
* `eq_17_2`: the budget set (17.2) in consumption, `c_y + c_o/R = ω_y + ω_o/R`, `c_y ≤ ω_y`.
* `olgDemand`, `eq_17_3`: the demand (17.3) is the **unique** optimum, for every `R ≥ 0`
  (for `R > 0` it is `max{(ω_y − ω_o/R)/2, 0}`, `olg_demand_eq_max`).
* `olg_interior_cons`, `olg_interior_iff`: the interior consumption formulas and their validity
  iff `R ≥ ω_o/ω_y` (strictly positive saving iff `R > ω_o/ω_y`).

The proofs use only the inequality `log x ≤ x − 1` (strict for `x ≠ 1`).
-/

namespace AKMM.Money

/-- AKMM, (17.1), p. 497: lifetime utility `log(a − s) + log(b + Rs)` of real saving `s`. -/
noncomputable def olgUtil (a b R s : ℝ) : ℝ := Real.log (a - s) + Real.log (b + R * s)

/-- AKMM, (17.1), p. 497: feasible real saving, `s ≥ 0` (`M′ ≥ 0`) and `c_y = a − s > 0`. -/
def olgFeasible (a s : ℝ) : Prop := 0 ≤ s ∧ s < a

/-- AKMM, (17.1), p. 497: optimal saving. -/
def olgOptimal (a b R s : ℝ) : Prop :=
  olgFeasible a s ∧ ∀ s', olgFeasible a s' → olgUtil a b R s' ≤ olgUtil a b R s

/-- AKMM, (17.3), p. 498: the demand for real balances, `0` when `Ra ≤ b`, otherwise
`(a − b/R)/2`. -/
noncomputable def olgDemand (a b R : ℝ) : ℝ := if R * a ≤ b then 0 else (a - b / R) / 2

/-- AKMM, (17.2), p. 497: with `R > 0`, `(c_y, c_o)` is attained by some `M′ ≥ 0` iff
`c_y + c_o/R = ω_y + ω_o/R` and `ω_y − c_y ≥ 0`. -/
theorem eq_17_2 {a b R cy co : ℝ} (hR : 0 < R) :
    (∃ s, 0 ≤ s ∧ cy = a - s ∧ co = b + R * s) ↔ cy + co / R = a + b / R ∧ 0 ≤ a - cy := by
  constructor
  · rintro ⟨s, hs, rfl, rfl⟩
    refine ⟨?_, by linarith⟩
    field_simp
    ring
  · rintro ⟨h1, h2⟩
    refine ⟨a - cy, h2, by ring, ?_⟩
    field_simp at h1
    linarith

/-- The key inequality: for feasible `s′, s` (with `b + Rs′, b + Rs > 0`),
`U(s′) − U(s) ≤ (s′ − s)(R/(b + Rs) − 1/(a − s))`, strictly if `s′ ≠ s`. -/
theorem olg_util_sub_le {a b R s s' : ℝ} (hs : s < a) (hs' : s' < a) (hb : 0 < b + R * s)
    (hb' : 0 < b + R * s') :
    olgUtil a b R s' - olgUtil a b R s ≤ (s' - s) * (R / (b + R * s) - 1 / (a - s)) ∧
      (s' ≠ s → olgUtil a b R s' - olgUtil a b R s <
        (s' - s) * (R / (b + R * s) - 1 / (a - s))) := by
  have ha : 0 < a - s := by linarith
  have ha' : 0 < a - s' := by linarith
  have e1 : Real.log (a - s') - Real.log (a - s) = Real.log ((a - s') / (a - s)) :=
    (Real.log_div ha'.ne' ha.ne').symm
  have e2 : Real.log (b + R * s') - Real.log (b + R * s) =
      Real.log ((b + R * s') / (b + R * s)) := (Real.log_div hb'.ne' hb.ne').symm
  have q1 : (a - s') / (a - s) - 1 = (s - s') / (a - s) := by field_simp; ring
  have q2 : (b + R * s') / (b + R * s) - 1 = R * (s' - s) / (b + R * s) := by field_simp; ring
  have hsplit : olgUtil a b R s' - olgUtil a b R s =
      Real.log ((a - s') / (a - s)) + Real.log ((b + R * s') / (b + R * s)) := by
    unfold olgUtil; rw [← e1, ← e2]; ring
  have hrhs : (s' - s) * (R / (b + R * s) - 1 / (a - s)) =
      ((a - s') / (a - s) - 1) + ((b + R * s') / (b + R * s) - 1) := by
    rw [q1, q2]; field_simp; ring
  have l1 := Real.log_le_sub_one_of_pos (div_pos ha' ha)
  have l2 := Real.log_le_sub_one_of_pos (div_pos hb' hb)
  refine ⟨by rw [hsplit, hrhs]; linarith, fun hne => ?_⟩
  have hne1 : (a - s') / (a - s) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq ha.ne'] at h
    exact hne (by linarith)
  have l1' := Real.log_lt_sub_one_of_pos (div_pos ha' ha) hne1
  rw [hsplit, hrhs]
  linarith

/-- AKMM, (17.3), p. 498: the demand is feasible. -/
theorem olg_demand_feasible {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 ≤ R) :
    olgFeasible a (olgDemand a b R) := by
  unfold olgDemand olgFeasible
  split_ifs with h
  · exact ⟨le_rfl, ha⟩
  · have hR' : 0 < R := by
      rcases hR.lt_or_eq with h' | h'
      · exact h'
      · subst h'; simp at h; linarith
    have : b / R < a := by rw [div_lt_iff₀ hR']; linarith
    have : 0 < b / R := div_pos hb hR'
    constructor <;> linarith

/-- The marginal condition at the demand: `(s′ − s*)(R/(b + Rs*) − 1/(a − s*)) ≤ 0` for every
`s′ ≥ 0`. -/
theorem olg_demand_marginal {a b R s' : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 ≤ R)
    (hs' : 0 ≤ s') :
    (s' - olgDemand a b R) * (R / (b + R * olgDemand a b R) - 1 / (a - olgDemand a b R))
      ≤ 0 := by
  unfold olgDemand
  split_ifs with h
  · simp only [sub_zero, mul_zero, add_zero]
    apply mul_nonpos_of_nonneg_of_nonpos hs'
    rw [sub_nonpos, div_le_div_iff₀ hb ha]
    linarith
  · have hR' : 0 < R := by
      rcases hR.lt_or_eq with h' | h'
      · exact h'
      · subst h'; simp at h; linarith
    have hz : R / (b + R * ((a - b / R) / 2)) - 1 / (a - (a - b / R) / 2) = 0 := by
      have h1 : b + R * ((a - b / R) / 2) = (R * a + b) / 2 := by field_simp; ring
      have h2 : a - (a - b / R) / 2 = (R * a + b) / (2 * R) := by field_simp; ring
      have h3 : 0 < R * a + b := by positivity
      rw [h1, h2]
      field_simp
      ring
    rw [hz, mul_zero]

/-- **AKMM, (17.3)**, p. 498: the demand `olgDemand` is optimal, and it is the unique optimum. -/
theorem eq_17_3 {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR : 0 ≤ R) :
    olgOptimal a b R (olgDemand a b R) ∧ ∀ s, olgOptimal a b R s → s = olgDemand a b R := by
  have hf := olg_demand_feasible ha hb hR
  have hpos : ∀ s, 0 ≤ s → 0 < b + R * s := fun s hs => by positivity
  refine ⟨⟨hf, fun s' hs' => ?_⟩, fun s hs => ?_⟩
  · have := (olg_util_sub_le hf.2 hs'.2 (hpos _ hf.1) (hpos _ hs'.1)).1
    have := olg_demand_marginal ha hb hR hs'.1
    linarith
  · by_contra hne
    have h1 := (olg_util_sub_le hf.2 hs.1.2 (hpos _ hf.1) (hpos _ hs.1.1)).2 hne
    have h2 := olg_demand_marginal ha hb hR hs.1.1
    have h3 := hs.2 _ hf
    linarith

/-- AKMM, (17.3), p. 498: for `R > 0` the demand is `max{(ω_y − ω_o/R)/2, 0}`. -/
theorem olg_demand_eq_max {a b R : ℝ} (hR : 0 < R) :
    olgDemand a b R = max ((a - b / R) / 2) 0 := by
  unfold olgDemand
  split_ifs with h
  · have : a ≤ b / R := by rw [le_div_iff₀ hR]; linarith
    rw [max_eq_right (by linarith)]
  · have : b / R < a := by rw [div_lt_iff₀ hR]; linarith
    rw [max_eq_left (by linarith)]

/-- AKMM, p. 498: the interior solution `c_y = (ω_y + ω_o/R)/2`, `c_o = (ω_yR + ω_o)/2`
(`= R c_y`). -/
theorem olg_interior_cons (a b R : ℝ) (hR : 0 < R) :
    a - (a - b / R) / 2 = (a + b / R) / 2 ∧ b + R * ((a - b / R) / 2) = (a * R + b) / 2 ∧
      (a * R + b) / 2 = R * ((a + b / R) / 2) := by
  refine ⟨by ring, by field_simp; ring, by field_simp⟩

/-- AKMM, p. 498: the interior solution is valid (`c_y ≤ ω_y`) iff `R ≥ ω_o/ω_y`; saving is
strictly positive iff `R > ω_o/ω_y`, and zero (`c_y = ω_y`, `c_o = ω_o`) otherwise. -/
theorem olg_interior_iff {a b R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    ((a + b / R) / 2 ≤ a ↔ b / a ≤ R) ∧ (0 < olgDemand a b R ↔ b / a < R) ∧
      (olgDemand a b R = 0 ↔ R ≤ b / a) := by
  have k1 : (a + b / R) / 2 ≤ a ↔ b / R ≤ a := by constructor <;> intro h <;> linarith
  have k2 : b / R ≤ a ↔ b / a ≤ R := by
    rw [div_le_iff₀ hR, div_le_iff₀ ha, mul_comm]
  refine ⟨k1.trans k2, ?_, ?_⟩
  · unfold olgDemand
    split_ifs with h
    · simp only [lt_self_iff_false, false_iff, not_lt]
      rw [le_div_iff₀ ha]; linarith
    · have hlt : b < R * a := lt_of_not_ge h
      have : b / R < a := by rw [div_lt_iff₀ hR]; linarith
      have : b / a < R := by rw [div_lt_iff₀ ha]; linarith
      constructor <;> intro _ <;> linarith
  · unfold olgDemand
    split_ifs with h
    · simp only [true_iff]; rw [le_div_iff₀ ha]; linarith
    · have hlt : b < R * a := lt_of_not_ge h
      have : b / R < a := by rw [div_lt_iff₀ hR]; linarith
      have : b / a < R := by rw [div_lt_iff₀ ha]; linarith
      constructor <;> intro h' <;> linarith

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiat money in the Samuelson endowment economy: the classification of equilibria

AKMM, §17.2.1, pp. 496–499. Every cohort has endowment `(ω_y, ω_o)` and utility
`log c_y + log c_o`; the initial old own the money stock `M`. A sequence of money prices
`p_{m,t} ≥ 0` is an equilibrium if at every date holding the whole stock `M` is optimal for the
young (the market-clearing condition (17.4)).

* `olgIsEquilibrium`; the young's problem in money units (`olg_moneyOptimal_iff_pos`, and the
  cases `p_{m,t} = 0`: `olg_moneyOptimal_zero_pos`, `olg_moneyOptimal_zero_zero`).
* `eq_17_5`: an equilibrium is either `p ≡ 0` or a positive solution of (17.5); `eq_17_5_div`
  gives the printed form `p_{m,t+1} = ω_o p_{m,t}/(ω_y − 2Mp_{m,t})`.
* `olg_classification`: the positive solutions are exactly
  `p_{m,t} = 1/(M(2/(ω_y − ω_o) + c(ω_y/ω_o)ᵗ))`, `c ≥ 0`, and exist only when `ω_y > ω_o`.
* `olg_continuum`: for `ω_y > ω_o` the equilibrium initial prices are exactly `[0, p̄_m]`,
  `p̄_m = (ω_y − ω_o)/(2M)`; `olg_unique_given_p0`: each one determines the equilibrium;
  `olg_no_monetary`: for `ω_y ≤ ω_o` the only equilibrium is `p ≡ 0`.
* `olg_stationary`, `olg_decreasing_to_zero`: `p̄_m` gives the stationary equilibrium; every
  `p_{m,0} ∈ (0, p̄_m)` gives a strictly decreasing path converging to zero.
* The map of Figure 17.2: fixed points (`olg_map_fixed_iff`), monotonicity on `[0, p̃_m)`
  (`olg_map_strictMonoOn`), slopes `ω_o/ω_y` and `ω_y/ω_o` (`olg_map_hasDerivAt`,
  `olg_map_slopes`), and the domain restriction `p < p̃_m = ω_y/(2M)` (`olg_map_domain`).
* The real form `m_{t+1} = ω_o m_t/(ω_y − 2m_t)` and nominal neutrality (`eq_17_5_real`,
  `olg_nominal_neutral`).
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, (17.1), p. 497: lifetime utility of a young agent holding `M′` units of money at money
prices `p_{m,t}, p_{m,t+1}`. -/
noncomputable def olgMoneyUtil (ωy ωo pt pt1 M' : ℝ) : ℝ :=
  Real.log (ωy - pt * M') + Real.log (ωo + pt1 * M')

/-- AKMM, (17.1), p. 497: feasible money holdings, `M′ ≥ 0` and `c_y > 0`. -/
def olgMoneyFeasible (ωy pt M' : ℝ) : Prop := 0 ≤ M' ∧ pt * M' < ωy

/-- AKMM, (17.1), p. 497: optimal money holdings of the young. -/
def olgMoneyOptimal (ωy ωo pt pt1 M' : ℝ) : Prop :=
  olgMoneyFeasible ωy pt M' ∧
    ∀ M'', olgMoneyFeasible ωy pt M'' → olgMoneyUtil ωy ωo pt pt1 M'' ≤ olgMoneyUtil ωy ωo pt pt1 M'

/-- AKMM, (17.4), p. 498: an equilibrium of the endowment economy with money stock `M`: money
prices are nonnegative and at every date the young optimally buy the whole stock. -/
def olgIsEquilibrium (ωy ωo M : ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ p t) ∧ ∀ t, olgMoneyOptimal ωy ωo (p t) (p (t + 1)) M

/-- The money-unit utility is the real-saving utility at `s = p_{m,t}M′`,
`R = p_{m,t+1}/p_{m,t}`. -/
theorem olg_moneyUtil_eq {ωy ωo pt pt1 : ℝ} (hpt : pt ≠ 0) (M' : ℝ) :
    olgMoneyUtil ωy ωo pt pt1 M' = olgUtil ωy ωo (pt1 / pt) (pt * M') := by
  unfold olgMoneyUtil olgUtil
  congr 2
  field_simp

/-- AKMM, (17.3), p. 498: with `p_{m,t} > 0`, `M′` is optimal iff `p_{m,t}M′` equals the demand
at the return `p_{m,t+1}/p_{m,t}`. -/
theorem olg_moneyOptimal_iff_pos {ωy ωo pt pt1 M' : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo)
    (hpt : 0 < pt) (hpt1 : 0 ≤ pt1) :
    olgMoneyOptimal ωy ωo pt pt1 M' ↔ 0 ≤ M' ∧ pt * M' = olgDemand ωy ωo (pt1 / pt) := by
  have hR : 0 ≤ pt1 / pt := div_nonneg hpt1 hpt.le
  obtain ⟨hopt, huniq⟩ := eq_17_3 hωy hωo hR
  constructor
  · rintro ⟨⟨h0, h1⟩, h⟩
    refine ⟨h0, huniq _ ⟨⟨mul_nonneg hpt.le h0, h1⟩, fun s' hs' => ?_⟩⟩
    have := h (s' / pt) ⟨div_nonneg hs'.1 hpt.le, by rw [mul_div_cancel₀ _ hpt.ne']; exact hs'.2⟩
    rwa [olg_moneyUtil_eq hpt.ne', olg_moneyUtil_eq hpt.ne', mul_div_cancel₀ _ hpt.ne'] at this
  · rintro ⟨h0, h⟩
    refine ⟨⟨h0, by rw [h]; exact hopt.1.2⟩, fun M'' hM'' => ?_⟩
    rw [olg_moneyUtil_eq hpt.ne', olg_moneyUtil_eq hpt.ne', h]
    exact hopt.2 _ ⟨mul_nonneg hpt.le hM''.1, hM''.2⟩

/-- AKMM, p. 498: if money is free today but valued tomorrow there is no optimal choice. -/
theorem olg_moneyOptimal_zero_pos {ωy ωo pt1 M' : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo)
    (hpt1 : 0 < pt1) : ¬ olgMoneyOptimal ωy ωo 0 pt1 M' := by
  rintro ⟨⟨h0, -⟩, h⟩
  have := h (M' + 1) ⟨by linarith, by simpa using hωy⟩
  unfold olgMoneyUtil at this
  have hlt : Real.log (ωo + pt1 * M') < Real.log (ωo + pt1 * (M' + 1)) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  simp only [zero_mul, sub_zero] at this
  linarith

/-- AKMM, p. 498 and footnote 4: if money is worthless today and tomorrow, any holding is
optimal (the money stock can be passed on). -/
theorem olg_moneyOptimal_zero_zero {ωy ωo M' : ℝ} (hωy : 0 < ωy) :
    olgMoneyOptimal ωy ωo 0 0 M' ↔ 0 ≤ M' := by
  constructor
  · exact fun h => h.1.1
  · intro h
    refine ⟨⟨h, by simpa using hωy⟩, fun M'' _ => ?_⟩
    simp [olgMoneyUtil]

/-- One step of an equilibrium: holding `M > 0` is optimal at `(p_{m,t}, p_{m,t+1})` iff both
prices are zero, or both are positive and `p_{m,t+1}(ω_y − 2Mp_{m,t}) = ω_o p_{m,t}`. -/
theorem olg_step_iff {ωy ωo M pt pt1 : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hpt : 0 ≤ pt) (hpt1 : 0 ≤ pt1) :
    olgMoneyOptimal ωy ωo pt pt1 M ↔
      (pt = 0 ∧ pt1 = 0) ∨ (0 < pt ∧ 0 < pt1 ∧ pt1 * (ωy - 2 * M * pt) = ωo * pt) := by
  constructor
  · intro h
    rcases hpt.lt_or_eq with hp | hp
    · right
      obtain ⟨-, hd⟩ := (olg_moneyOptimal_iff_pos hωy hωo hp hpt1).1 h
      have hdpos : 0 < olgDemand ωy ωo (pt1 / pt) := by rw [← hd]; positivity
      unfold olgDemand at hd hdpos
      split_ifs at hd hdpos with hc
      · exact absurd hdpos (lt_irrefl 0)
      · have hR : 0 < pt1 / pt := by
          by_contra hn
          have : pt1 / pt = 0 := le_antisymm (not_lt.1 hn) (div_nonneg hpt1 hp.le)
          rw [this] at hc
          exact hc (by simp; linarith)
        have h1 : 0 < pt1 := by
          rcases hpt1.lt_or_eq with h' | h'
          · exact h'
          · rw [← h', zero_div] at hR; exact absurd hR (lt_irrefl 0)
        refine ⟨hp, h1, ?_⟩
        field_simp at hd
        linear_combination -hd
    · left
      subst hp
      refine ⟨rfl, ?_⟩
      by_contra hn
      exact olg_moneyOptimal_zero_pos hωy hωo (lt_of_le_of_ne hpt1 (Ne.symm hn)) h
  · rintro (⟨rfl, rfl⟩ | ⟨hp, hp1, he⟩)
    · exact (olg_moneyOptimal_zero_zero hωy).2 hM.le
    · refine (olg_moneyOptimal_iff_pos hωy hωo hp hpt1).2 ⟨hM.le, ?_⟩
      unfold olgDemand
      have hlt : ωo * pt < pt1 * ωy := by nlinarith [mul_pos (mul_pos hM hp) hp1]
      have hc : ¬ (pt1 / pt * ωy ≤ ωo) := by
        rw [not_le, div_mul_eq_mul_div, lt_div_iff₀ hp]; linarith
      simp only [hc, ↓reduceIte]
      field_simp
      linear_combination -he

/-- **AKMM, (17.5)**, p. 498: an equilibrium is either `p ≡ 0` (money never valued) or a
positive solution of `p_{m,t+1}(ω_y − 2Mp_{m,t}) = ω_o p_{m,t}`; conversely each is an
equilibrium. -/
theorem eq_17_5 {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) (p : ℕ → ℝ) :
    olgIsEquilibrium ωy ωo M p ↔ (∀ t, p t = 0) ∨
      ∀ t, 0 < p t ∧ p (t + 1) * (ωy - 2 * M * p t) = ωo * p t := by
  constructor
  · rintro ⟨hnn, hopt⟩
    have hstep := fun t => (olg_step_iff hωy hωo hM (hnn t) (hnn (t + 1))).1 (hopt t)
    rcases (hnn 0).lt_or_eq with h0 | h0
    · right
      have hpos : ∀ t, 0 < p t := by
        intro t
        induction t with
        | zero => exact h0
        | succ n ih =>
          rcases hstep n with ⟨h, -⟩ | ⟨-, h, -⟩
          · exact absurd h ih.ne'
          · exact h
      intro t
      rcases hstep t with ⟨h, -⟩ | ⟨-, -, h⟩
      · exact absurd h (hpos t).ne'
      · exact ⟨hpos t, h⟩
    · left
      intro t
      induction t with
      | zero => exact h0.symm
      | succ n ih =>
        rcases hstep n with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd ih h.ne'
  · rintro (h | h)
    · refine ⟨fun t => (h t).ge, fun t => ?_⟩
      rw [h t, h (t + 1)]
      exact (olg_moneyOptimal_zero_zero hωy).2 hM.le
    · refine ⟨fun t => (h t).1.le, fun t => ?_⟩
      exact (olg_step_iff hωy hωo hM (h t).1.le (h (t + 1)).1.le).2
        (Or.inr ⟨(h t).1, (h (t + 1)).1, (h t).2⟩)

/-- AKMM, (17.5) and p. 499: along a monetary equilibrium `p_{m,t} < p̃_m = ω_y/(2M)` and
`p_{m,t+1} = ω_o p_{m,t}/(ω_y − 2Mp_{m,t})`. -/
theorem eq_17_5_div {ωy ωo M pt pt1 : ℝ} (hωo : 0 < ωo) (hpt : 0 < pt) (hpt1 : 0 < pt1)
    (h : pt1 * (ωy - 2 * M * pt) = ωo * pt) :
    2 * M * pt < ωy ∧ pt1 = ωo * pt / (ωy - 2 * M * pt) := by
  have hpos : 0 < ωy - 2 * M * pt := by
    by_contra hn
    have : pt1 * (ωy - 2 * M * pt) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpt1.le (not_lt.1 hn)
    nlinarith
  refine ⟨by linarith, ?_⟩
  rw [eq_div_iff hpos.ne', h]

/-- AKMM, p. 499: in real balances `m_t = p_{m,t}M` the equilibrium condition reads
`m_{t+1}(ω_y − 2m_t) = ω_o m_t`, i.e. `m_{t+1} = ω_o m_t/(ω_y − 2m_t)`. -/
theorem eq_17_5_real {ωy ωo M pt pt1 : ℝ} (hM : M ≠ 0) :
    pt1 * (ωy - 2 * M * pt) = ωo * pt ↔ M * pt1 * (ωy - 2 * (M * pt)) = ωo * (M * pt) := by
  constructor
  · intro h; linear_combination M * h
  · intro h
    have : M * (pt1 * (ωy - 2 * M * pt) - ωo * pt) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hM
    · linarith

/-- The closed form of the positive solutions: `Y_t = 2/(ω_y − ω_o) + c(ω_y/ω_o)ᵗ` satisfies
`ω_o Y_{t+1} = ω_y Y_t − 2`. -/
theorem olg_closed_form_step {ωy ωo : ℝ} (hωo : 0 < ωo) (hgap : ωo < ωy) (c : ℝ) (t : ℕ) :
    ωo * (2 / (ωy - ωo) + c * (ωy / ωo) ^ (t + 1)) =
      ωy * (2 / (ωy - ωo) + c * (ωy / ωo) ^ t) - 2 := by
  have h1 : ωy - ωo ≠ 0 := by linarith
  rw [pow_succ]
  field_simp
  ring

/-- **AKMM, pp. 498–499: the classification of equilibria.** With `ω_y, ω_o, M > 0`, `p` is an
equilibrium iff `p ≡ 0`, or `ω_y > ω_o` and for some `c ≥ 0`,
`p_{m,t} = 1/(M(2/(ω_y − ω_o) + c(ω_y/ω_o)ᵗ))` for all `t`. -/
theorem olg_classification {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (p : ℕ → ℝ) :
    olgIsEquilibrium ωy ωo M p ↔ (∀ t, p t = 0) ∨ (ωo < ωy ∧ ∃ c, 0 ≤ c ∧
      ∀ t, p t = (M * (2 / (ωy - ωo) + c * (ωy / ωo) ^ t))⁻¹) := by
  rw [eq_17_5 hωy hωo hM]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨hgap, c, hc, hp⟩ t => ?_⟩
  · set y : ℕ → ℝ := fun t => (M * p t)⁻¹ with hy
    have hypos : ∀ t, 0 < y t := fun t => inv_pos.2 (mul_pos hM (h t).1)
    have hrec : ∀ t, ωo * y (t + 1) = ωy * y t - 2 := fun t => by
      obtain ⟨hp, he⟩ := h t
      have hp1 := (h (t + 1)).1
      simp only [hy]
      field_simp
      linear_combination -he
    have hgap : ωo < ωy := by
      by_contra hn
      have hle : ωy ≤ ωo := not_lt.1 hn
      have hdec : ∀ t, y (t + 1) ≤ y t - 2 / ωo := fun t => by
        have := hrec t
        rw [le_sub_iff_add_le, ← mul_le_mul_iff_of_pos_left hωo, mul_add,
          mul_div_cancel₀ _ hωo.ne']
        nlinarith [hypos t]
      have hlin : ∀ t : ℕ, y t ≤ y 0 - t * (2 / ωo) := by
        intro t
        induction t with
        | zero => simp
        | succ n ih => have := hdec n; push_cast; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (y 0 / (2 / ωo))
      have h2 : 0 < 2 / ωo := by positivity
      have := hlin n
      have := hypos n
      rw [div_lt_iff₀ h2] at hn
      linarith
    refine ⟨hgap, y 0 - 2 / (ωy - ωo), ?_, ?_⟩
    · set lam := ωy / ωo with hlam
      set yb := 2 / (ωy - ωo) with hyb
      have hl1 : 1 < lam := (one_lt_div hωo).2 hgap
      have hfix : ωo * yb = ωy * yb - 2 := by
        simp only [hyb]; field_simp [(by linarith : ωy - ωo ≠ 0)]; ring
      have hd : ∀ t, y t - yb = (y 0 - yb) * lam ^ t := by
        intro t
        induction t with
        | zero => simp
        | succ n ih =>
          have e : y (n + 1) - yb = lam * (y n - yb) := by
            have := hrec n
            simp only [hlam]
            field_simp
            linear_combination this - hfix
          rw [e, ih, pow_succ]; ring
      by_contra hneg
      have hd0 : y 0 - yb < 0 := not_le.1 hneg
      have hyb0 : 0 < yb := div_pos two_pos (by linarith)
      obtain ⟨n, hn⟩ := exists_nat_gt (yb / (-(y 0 - yb)) / (lam - 1))
      have hb : 1 + (n : ℝ) * (lam - 1) ≤ lam ^ n := by
        have := one_add_mul_le_pow (show (-2 : ℝ) ≤ lam - 1 by linarith) n
        simpa using this
      have hk : (y 0 - yb) * lam ^ n ≤ (y 0 - yb) * (1 + n * (lam - 1)) :=
        mul_le_mul_of_nonpos_left hb hd0.le
      have hn' : yb < (-(y 0 - yb)) * (n * (lam - 1)) := by
        rw [div_lt_iff₀ (by linarith), div_lt_iff₀ (by linarith)] at hn
        nlinarith
      have := hd n
      have := hypos n
      nlinarith
    · intro t
      have hd : ∀ t, y t = 2 / (ωy - ωo) + (y 0 - 2 / (ωy - ωo)) * (ωy / ωo) ^ t := by
        intro t
        induction t with
        | zero => simp
        | succ n ih =>
          have h1 := hrec n
          have h2 := olg_closed_form_step hωo hgap (y 0 - 2 / (ωy - ωo)) n
          apply mul_left_cancel₀ hωo.ne'
          rw [h1, h2, ih]
      rw [← hd t]
      simp only [hy]
      have := (h t).1
      field_simp
  · have hpos : ∀ t, 0 < 2 / (ωy - ωo) + c * (ωy / ωo) ^ t := fun t => by
      have : 0 < 2 / (ωy - ωo) := div_pos two_pos (by linarith)
      have : 0 ≤ c * (ωy / ωo) ^ t := mul_nonneg hc (pow_nonneg (by positivity) t)
      linarith
    have hstep := olg_closed_form_step hωo hgap c t
    refine ⟨by rw [hp t]; exact inv_pos.2 (mul_pos hM (hpos t)), ?_⟩
    rw [hp t, hp (t + 1)]
    set A := 2 / (ωy - ωo) + c * (ωy / ωo) ^ t with hA
    set B := 2 / (ωy - ωo) + c * (ωy / ωo) ^ (t + 1) with hB
    have hA0 : A ≠ 0 := (hpos t).ne'
    have hB0 : B ≠ 0 := (hpos (t + 1)).ne'
    have hM0 := hM.ne'
    calc (M * B)⁻¹ * (ωy - 2 * M * (M * A)⁻¹) = (ωy * A - 2) / (M * B * A) := by
          field_simp
      _ = ωo * B / (M * B * A) := by rw [← hstep]
      _ = ωo * (M * A)⁻¹ := by field_simp

/-- AKMM, p. 499: if `ω_y ≤ ω_o` the only equilibrium is the nonmonetary one, `p ≡ 0`. -/
theorem olg_no_monetary {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hle : ωy ≤ ωo) (p : ℕ → ℝ) : olgIsEquilibrium ωy ωo M p ↔ ∀ t, p t = 0 := by
  rw [olg_classification hωy hωo hM]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (not_lt.2 hle)
  · exact Or.inl

/-- AKMM, p. 499: the nonmonetary equilibrium `p ≡ 0` always exists. -/
theorem olg_nonmonetary_exists {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) :
    olgIsEquilibrium ωy ωo M (fun _ => 0) :=
  (eq_17_5 hωy hωo hM _).2 (Or.inl fun _ => rfl)

/-- **AKMM, p. 499: the continuum of equilibria.** If `ω_y > ω_o`, `p_{m,0}` is the initial price
of an equilibrium iff `p_{m,0} ∈ [0, p̄_m]`, `p̄_m = (ω_y − ω_o)/(2M)`. -/
theorem olg_continuum {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) (p0 : ℝ) :
    (∃ p, olgIsEquilibrium ωy ωo M p ∧ p 0 = p0) ↔ 0 ≤ p0 ∧ p0 ≤ (ωy - ωo) / (2 * M) := by
  have hd : 0 < ωy - ωo := by linarith
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases (olg_classification hωy hωo hM p).1 hp with h | ⟨-, c, hc, h⟩
    · rw [h 0]; exact ⟨le_rfl, by positivity⟩
    · rw [h 0, pow_zero, mul_one]
      have hy : 0 < 2 / (ωy - ωo) := div_pos two_pos hd
      refine ⟨(inv_pos.2 (by positivity)).le, ?_⟩
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      have : 2 * M / (ωy - ωo) = M * (2 / (ωy - ωo)) := by ring
      rw [this]
      nlinarith
  · rintro ⟨h0, h1⟩
    rcases h0.lt_or_eq with hp | hp
    · refine ⟨fun t => (M * (2 / (ωy - ωo) + ((M * p0)⁻¹ - 2 / (ωy - ωo)) *
        (ωy / ωo) ^ t))⁻¹, (olg_classification hωy hωo hM _).2 (Or.inr ⟨hgap, _, ?_,
          fun _ => rfl⟩), ?_⟩
      · rw [sub_nonneg, le_inv_comm₀ (div_pos two_pos hd) (by positivity), inv_div]
        rw [le_div_iff₀ (by positivity)] at h1
        rw [le_div_iff₀ two_pos]; linarith
      · simp only [pow_zero, mul_one, add_sub_cancel]
        field_simp
    · exact ⟨fun _ => 0, olg_nonmonetary_exists hωy hωo hM, hp⟩

/-- AKMM, p. 499: an equilibrium is determined by its initial price `p_{m,0}`. -/
theorem olg_unique_given_p0 {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p p' : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (hp' : olgIsEquilibrium ωy ωo M p')
    (h0 : p 0 = p' 0) : p = p' := by
  rcases (eq_17_5 hωy hωo hM p).1 hp with h | h <;>
    rcases (eq_17_5 hωy hωo hM p').1 hp' with h' | h'
  · funext t; rw [h, h']
  · exact absurd (h 0 ▸ h0) (h' 0).1.ne
  · exact absurd (h' 0 ▸ h0) (h 0).1.ne'
  · funext t
    induction t with
    | zero => exact h0
    | succ n ih =>
      rw [(eq_17_5_div hωo (h n).1 (h (n + 1)).1 (h n).2).2,
        (eq_17_5_div hωo (h' n).1 (h' (n + 1)).1 (h' n).2).2, ih]

/-- AKMM, p. 498: for `ω_y > ω_o` the constant price `p̄_m = (ω_y − ω_o)/(2M) > 0` is an
equilibrium (the stationary monetary equilibrium). -/
theorem olg_stationary {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) :
    0 < (ωy - ωo) / (2 * M) ∧ olgIsEquilibrium ωy ωo M (fun _ => (ωy - ωo) / (2 * M)) := by
  have hd : 0 < ωy - ωo := by linarith
  refine ⟨by positivity, (eq_17_5 hωy hωo hM _).2 (Or.inr fun _ => ⟨by positivity, ?_⟩)⟩
  field_simp
  ring

/-- AKMM, p. 499: every equilibrium with `0 < p_{m,0} < p̄_m` has strictly decreasing prices
converging to zero: money loses its value in the limit. -/
theorem olg_decreasing_to_zero {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (h0 : 0 < p 0)
    (h1 : p 0 < (ωy - ωo) / (2 * M)) : StrictAnti p ∧ Tendsto p atTop (𝓝 0) := by
  rcases (olg_classification hωy hωo hM p).1 hp with h | ⟨hgap, c, hc, h⟩
  · exact absurd (h 0) h0.ne'
  have hd : 0 < ωy - ωo := by linarith
  have hl : 1 < ωy / ωo := (one_lt_div hωo).2 hgap
  have hcpos : 0 < c := by
    rcases hc.lt_or_eq with hc' | hc'
    · exact hc'
    · subst hc'
      rw [h 0] at h1
      simp only [zero_mul, add_zero] at h1
      rw [show (M * (2 / (ωy - ωo)))⁻¹ = (ωy - ωo) / (2 * M) by field_simp] at h1
      exact absurd h1 (lt_irrefl _)
  have hY : ∀ t, 0 < 2 / (ωy - ωo) + c * (ωy / ωo) ^ t := fun t => by
    have : 0 < 2 / (ωy - ωo) := div_pos two_pos hd
    positivity
  refine ⟨strictAnti_nat_of_succ_lt fun n => ?_, ?_⟩
  · rw [h n, h (n + 1)]
    apply inv_strictAnti₀ (mul_pos hM (hY n))
    apply mul_lt_mul_of_pos_left _ hM
    have : (ωy / ωo) ^ n < (ωy / ωo) ^ (n + 1) := pow_lt_pow_right₀ hl (Nat.lt_succ_self n)
    nlinarith
  · have hT : Tendsto (fun t : ℕ => M * (2 / (ωy - ωo) + c * (ωy / ωo) ^ t)) atTop atTop :=
      Tendsto.const_mul_atTop hM (tendsto_atTop_add_const_left _ _
        ((tendsto_pow_atTop_atTop_of_one_lt hl).const_mul_atTop hcpos))
    have := tendsto_inv_atTop_zero.comp hT
    exact this.congr fun t => (h t).symm

/-! ### The map of Figure 17.2 in real balances -/

/-- AKMM, p. 499: the equilibrium map in real balances, `f(m) = ω_o m/(ω_y − 2m)`. -/
noncomputable def olgMap (ωy ωo m : ℝ) : ℝ := ωo * m / (ωy - 2 * m)

/-- AKMM, p. 498: on `[0, ω_y/2)` the fixed points of the map are `0` and
`m̄ = (ω_y − ω_o)/2` (the latter a positive fixed point only when `ω_y > ω_o`). -/
theorem olg_map_fixed_iff {ωy ωo m : ℝ} (hm0 : 0 ≤ m) (hm : 2 * m < ωy) :
    olgMap ωy ωo m = m ↔ m = 0 ∨ m = (ωy - ωo) / 2 := by
  unfold olgMap
  have hp : 0 < ωy - 2 * m := by linarith
  rw [div_eq_iff hp.ne']
  constructor
  · intro h
    have : m * (2 * m - (ωy - ωo)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact Or.inl h'
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-- AKMM, p. 499: the map is strictly increasing on `[0, ω_y/2)`. -/
theorem olg_map_strictMonoOn {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    StrictMonoOn (olgMap ωy ωo) (Set.Ico 0 (ωy / 2)) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨-, hy1⟩ := hy
  unfold olgMap
  have h1 : 0 < ωy - 2 * x := by linarith
  have h2 : 0 < ωy - 2 * y := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_lt_mul_of_pos_left hxy (mul_pos hωo hωy)]

/-- AKMM, p. 499: the slope of the map is `f′(m) = ω_oω_y/(ω_y − 2m)²` for `2m ≠ ω_y`. -/
theorem olg_map_hasDerivAt {ωy ωo m : ℝ} (hm : ωy - 2 * m ≠ 0) :
    HasDerivAt (olgMap ωy ωo) (ωo * ωy / (ωy - 2 * m) ^ 2) m := by
  have h1 : HasDerivAt (fun x => ωo * x) ωo m :=
    ((hasDerivAt_id' m).const_mul ωo).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x => ωy - 2 * x) (-2) m :=
    (HasDerivAt.const_sub ωy ((hasDerivAt_id' m).const_mul 2)).congr_deriv (by ring)
  have := h1.div h2 hm
  refine this.congr_deriv ?_
  field_simp
  ring

/-- AKMM, p. 499: the slope is `ω_o/ω_y` at `0` (below one in case (i)) and `ω_y/ω_o` at the
monetary steady state `m̄ = (ω_y − ω_o)/2` (above one in case (i)); in case (ii) the slope at
the origin is at least one. -/
theorem olg_map_slopes {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    HasDerivAt (olgMap ωy ωo) (ωo / ωy) 0 ∧
      HasDerivAt (olgMap ωy ωo) (ωy / ωo) ((ωy - ωo) / 2) ∧
      (ωo < ωy → ωo / ωy < 1 ∧ 1 < ωy / ωo) ∧ (ωy ≤ ωo → 1 ≤ ωo / ωy) := by
  refine ⟨?_, ?_, fun h => ⟨(div_lt_one hωy).2 h, (one_lt_div hωo).2 h⟩,
    fun h => (one_le_div hωy).2 h⟩
  · have := olg_map_hasDerivAt (ωo := ωo) (m := 0) (by simpa using hωy.ne')
    refine this.congr_deriv ?_
    rw [mul_zero, sub_zero, sq]
    field_simp
  · have := olg_map_hasDerivAt (ωy := ωy) (ωo := ωo) (m := (ωy - ωo) / 2)
      (by ring_nf; exact hωo.ne')
    refine this.congr_deriv ?_
    have : ωy - 2 * ((ωy - ωo) / 2) = ωo := by ring
    rw [this]
    field_simp

/-- AKMM, p. 499: for `p_{m,t} ≥ p̃_m = ω_y/(2M)` no positive `p_{m,t+1}` solves (17.5): next
period's price would be "infinite or negative". -/
theorem olg_map_domain {ωy ωo M pt pt1 : ℝ} (hωo : 0 < ωo) (hpt : 0 < pt) (hpt1 : 0 < pt1)
    (hge : ωy ≤ 2 * M * pt) : pt1 * (ωy - 2 * M * pt) ≠ ωo * pt := by
  intro h
  have : pt1 * (ωy - 2 * M * pt) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpt1.le (by linarith)
  nlinarith

/-- AKMM, p. 499: the equilibrium determines only the real value of the money stock: `p` is an
equilibrium with stock `M` iff `p_{m,t}M/M′` is one with stock `M′`. -/
theorem olg_nominal_neutral {ωy ωo M M' : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hM' : 0 < M') (p : ℕ → ℝ) :
    olgIsEquilibrium ωy ωo M p ↔ olgIsEquilibrium ωy ωo M' (fun t => p t * M / M') := by
  rw [eq_17_5 hωy hωo hM, eq_17_5 hωy hωo hM']
  have hk : 0 < M / M' := div_pos hM hM'
  have e : ∀ t, 2 * M' * (p t * M / M') = 2 * M * p t := fun t => by field_simp
  have e2 : ∀ t, p (t + 1) * M / M' * (ωy - 2 * M * p t) =
      M / M' * (p (t + 1) * (ωy - 2 * M * p t)) := fun t => by ring
  refine or_congr ⟨fun h t => by rw [h t]; ring, fun h t => ?_⟩
    ⟨fun h t => ⟨by have := (h t).1; positivity, ?_⟩, fun h t => ⟨?_, ?_⟩⟩
  · rcases div_eq_zero_iff.1 (h t) with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' hM.ne'
    · exact absurd h' hM'.ne'
  · rw [e t, e2 t, (h t).2]; ring
  · have h1 := (h t).1
    rw [mul_div_assoc] at h1
    exact (mul_pos_iff_of_pos_right hk).1 h1
  · have h1 := (h t).2
    rw [e t, e2 t, show ωo * (p t * M / M') = M / M' * (ωo * p t) by ring] at h1
    exact mul_left_cancel₀ hk.ne' h1

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Welfare across the equilibria of the fiat-money endowment economy

AKMM, §17.2.2, p. 500 (the comparisons the text "leave[s] as an exercise"), with the link to
Miao, Chapter 16 (the `OverlappingGenerations` dependency).

* `olgIndirect`: utility at the optimum as a function of the return, `log((Rω_y + ω_o)²/(4R))`;
  it is strictly increasing on `R ≥ ω_o/ω_y` (`olg_indirect_strictMonoOn`), the "key insight":
  a higher return on saving is better.
* `olg_cohort_util_eq`: in every equilibrium the utility of cohort `t` is
  `olgIndirect (ω_o/(ω_y − 2m_t))`, `m_t = p_{m,t}M` (autarky included).
* `olg_ranking`: equilibria are ranked by `p_{m,0}`: a larger `p_{m,0} ≤ p̄_m` gives strictly
  higher utility to every cohort and to the initial old. Hence every monetary equilibrium
  Pareto-improves on autarky (`olg_monetary_improves_autarky`) and every equilibrium other than
  the stationary monetary one is Pareto-dominated by it (`olg_stationary_dominates`).
* `olg_stationary_welfare`: the stationary utility `2 log((ω_y + ω_o)/2) > log ω_y + log ω_o`;
  `olg_smoothing_hurts_old`: for `ω_y < ω_o` the smoothed allocation would hurt the initial old.
* `olg_return_limit`: the long-run gross return is `ω_o/ω_y < 1` along non-stationary
  equilibria and `1` in the stationary one.
* The Miao link: the book's economy is Miao's Samuelson economy with log utility, `β = 1` and
  `g_n = g_m = 1` (`olgMiao`); its monetary equilibria are exactly the paths of
  `olg_classification` (`olg_miao_paths`); the stationary monetary equilibrium is Pareto optimal
  and autarky is Pareto optimal iff `ω_y ≤ ω_o` (`olg_miao_stationary_pareto`,
  `olg_miao_autarky_pareto_iff`, from Miao's Propositions 16.1.2–16.1.3).
-/

open Filter Topology Miao.OverlappingGenerations

namespace AKMM.Money

/-- AKMM, p. 500: utility at the interior optimum as a function of the gross return `R`,
`log c_y + log c_o = log((Rω_y + ω_o)²/(4R))`. -/
noncomputable def olgIndirect (ωy ωo R : ℝ) : ℝ := Real.log ((R * ωy + ωo) ^ 2 / (4 * R))

/-- At the interior optimum `olgUtil` equals `olgIndirect`; at the corner return
`R = ω_o/ω_y`, `olgIndirect` is the autarky utility `log ω_y + log ω_o`. -/
theorem olg_indirect_eq {ωy ωo R : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hR : 0 < R) :
    olgUtil ωy ωo R ((ωy - ωo / R) / 2) = olgIndirect ωy ωo R ∧
      olgIndirect ωy ωo (ωo / ωy) = Real.log ωy + Real.log ωo := by
  constructor
  · unfold olgUtil olgIndirect
    have h1 : ωy - (ωy - ωo / R) / 2 = (R * ωy + ωo) / (2 * R) := by field_simp; ring
    have h2 : ωo + R * ((ωy - ωo / R) / 2) = (R * ωy + ωo) / 2 := by field_simp; ring
    have h3 : 0 < R * ωy + ωo := by positivity
    rw [h1, h2, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  · unfold olgIndirect
    rw [← Real.log_mul hωy.ne' hωo.ne']
    congr 1
    field_simp
    ring

/-- **AKMM, p. 500** ("a higher return on saving is better for the consumer"): the indirect
utility is strictly increasing in the return on `[ω_o/ω_y, ∞)`. -/
theorem olg_indirect_strictMonoOn {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    StrictMonoOn (olgIndirect ωy ωo) (Set.Ici (ωo / ωy)) := by
  intro R1 h1 R2 h2 hlt
  have h1' : ωo / ωy ≤ R1 := h1
  have hR1 : 0 < R1 := lt_of_lt_of_le (div_pos hωo hωy) h1'
  have hR2 : 0 < R2 := hR1.trans hlt
  have hk : ωo ≤ R1 * ωy := by rwa [div_le_iff₀ hωy] at h1'
  unfold olgIndirect
  apply Real.log_lt_log (by positivity)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hk2 : ωo * ωo < (R1 * ωy) * (R2 * ωy) := by
    have : R1 * ωy < R2 * ωy := mul_lt_mul_of_pos_right hlt hωy
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hk2 (sub_pos.2 hlt)]

/-- AKMM, p. 500: the lifetime utility of cohort `t` along a price path. -/
noncomputable def olgCohortUtil (ωy ωo M : ℝ) (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.log (ωy - M * p t) + Real.log (ωo + M * p (t + 1))

/-- AKMM, p. 500: in every equilibrium the utility of cohort `t` is the indirect utility at the
return `ω_o/(ω_y − 2m_t)`, `m_t = p_{m,t}M` (in autarky `m_t = 0`, return `ω_o/ω_y`). -/
theorem olg_cohort_util_eq {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (t : ℕ) :
    olgCohortUtil ωy ωo M p t = olgIndirect ωy ωo (ωo / (ωy - 2 * (M * p t))) ∧
      2 * (M * p t) < ωy := by
  rcases (eq_17_5 hωy hωo hM p).1 hp with h | h
  · simp only [olgCohortUtil, h, mul_zero, sub_zero, add_zero]
    exact ⟨(olg_indirect_eq hωy hωo (div_pos hωo hωy)).2.symm, hωy⟩
  · obtain ⟨hlt, heq⟩ := eq_17_5_div hωo (h t).1 (h (t + 1)).1 (h t).2
    have hx := mul_pos hM (h t).1
    have hd : 0 < ωy - 2 * (M * p t) := by linarith
    refine ⟨?_, by linarith⟩
    unfold olgCohortUtil olgIndirect
    have hc1 : 0 < ωy - M * p t := by linarith
    have hc2 : 0 < ωo + M * p (t + 1) := by have := (h (t + 1)).1; positivity
    have hMp1 : M * p (t + 1) = ωo * (M * p t) / (ωy - 2 * (M * p t)) := by
      rw [heq, mul_div_assoc', show 2 * M * p t = 2 * (M * p t) by ring]; ring
    rw [← Real.log_mul hc1.ne' hc2.ne', hMp1]
    congr 1
    generalize M * p t = x at *
    have hd' := hd.ne'
    have hd2 : ωy - x * 2 ≠ 0 := by rw [mul_comm]; exact hd'
    have hωo' := hωo.ne'
    field_simp
    ring

/-- The equilibrium return `ω_o/(ω_y − 2m)` is strictly increasing in real balances
`m ∈ [0, ω_y/2)` and at least `ω_o/ω_y`. -/
theorem olg_return_strictMonoOn {ωy ωo : ℝ} (hωo : 0 < ωo) :
    StrictMonoOn (fun m => ωo / (ωy - 2 * m)) (Set.Ico 0 (ωy / 2)) ∧
      ∀ m ∈ Set.Ico 0 (ωy / 2), ωo / ωy ≤ ωo / (ωy - 2 * m) := by
  refine ⟨fun x hx y hy hxy => ?_, fun m hm => ?_⟩
  · obtain ⟨-, hy1⟩ := hy
    exact div_lt_div_of_pos_left hωo (by linarith) (by linarith)
  · obtain ⟨hm0, hm1⟩ := hm
    exact div_le_div_of_nonneg_left hωo.le (by linarith) (by linarith)

/-- **AKMM, p. 500: equilibria are ranked by the initial value of money.** If `p, p′` are
equilibria with `p_{m,0} < p′_{m,0}`, then real balances are higher under `p′` at every date,
every cohort `t ≥ 0` is strictly better off under `p′`, and so are the initial old. -/
theorem olg_ranking {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p p' : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (hp' : olgIsEquilibrium ωy ωo M p')
    (h0 : p 0 < p' 0) :
    (∀ t, p t < p' t) ∧ (∀ t, olgCohortUtil ωy ωo M p t < olgCohortUtil ωy ωo M p' t) ∧
      ωo + M * p 0 < ωo + M * p' 0 := by
  have hlt : ∀ t, p t < p' t := by
    rcases (eq_17_5 hωy hωo hM p').1 hp' with h' | h'
    · exact absurd (h' 0 ▸ h0) (not_lt.2 (hp.1 0))
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      rcases (eq_17_5 hωy hωo hM p).1 hp with h | h
      · rw [h]; exact (h' (n + 1)).1
      · rw [(eq_17_5_div hωo (h n).1 (h (n + 1)).1 (h n).2).2,
          (eq_17_5_div hωo (h' n).1 (h' (n + 1)).1 (h' n).2).2]
        have hm := olg_map_strictMonoOn hωy hωo
          (a := M * p n) (b := M * p' n)
          ⟨(mul_pos hM (h n).1).le, by linarith [(eq_17_5_div hωo (h n).1 (h (n + 1)).1 (h n).2).1]⟩
          ⟨(mul_pos hM (h' n).1).le,
            by linarith [(eq_17_5_div hωo (h' n).1 (h' (n + 1)).1 (h' n).2).1]⟩
          (mul_lt_mul_of_pos_left ih hM)
        unfold olgMap at hm
        have e : ∀ x, ωo * x / (ωy - 2 * M * x) = (ωo * (M * x) / (ωy - 2 * (M * x))) / M :=
          fun x => by field_simp
        rw [e, e]
        exact div_lt_div_of_pos_right hm hM
  refine ⟨hlt, fun t => ?_, by nlinarith [hlt 0]⟩
  obtain ⟨e1, l1⟩ := olg_cohort_util_eq hωy hωo hM hp t
  obtain ⟨e2, l2⟩ := olg_cohort_util_eq hωy hωo hM hp' t
  obtain ⟨hmono, hge⟩ := olg_return_strictMonoOn hωo
  have m1 : M * p t ∈ Set.Ico 0 (ωy / 2) := ⟨mul_nonneg hM.le (hp.1 t), by linarith⟩
  have m2 : M * p' t ∈ Set.Ico 0 (ωy / 2) := ⟨mul_nonneg hM.le (hp'.1 t), by linarith⟩
  rw [e1, e2]
  exact olg_indirect_strictMonoOn hωy hωo (hge _ m1) (hge _ m2)
    (hmono m1 m2 (mul_lt_mul_of_pos_left (hlt t) hM))

/-- AKMM, p. 500: every monetary equilibrium (stationary or not) is a strict Pareto improvement
on autarky: every cohort and the initial old are strictly better off. -/
theorem olg_monetary_improves_autarky {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (h0 : 0 < p 0) :
    (∀ t, Real.log ωy + Real.log ωo < olgCohortUtil ωy ωo M p t) ∧ ωo < ωo + M * p 0 := by
  have h := olg_ranking hωy hωo hM (olg_nonmonetary_exists hωy hωo hM) hp h0
  refine ⟨fun t => ?_, by simpa using h.2.2⟩
  have := h.2.1 t
  simpa [olgCohortUtil] using this

/-- AKMM, p. 500: every equilibrium with `p_{m,0} < p̄_m` (autarky and the non-stationary
monetary equilibria) is Pareto-dominated by the stationary monetary equilibrium, which is a
feasible allocation; these equilibria are therefore Pareto inefficient. -/
theorem olg_stationary_dominates {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p)
    (h0 : p 0 < (ωy - ωo) / (2 * M)) :
    (∀ t, olgCohortUtil ωy ωo M p t <
      olgCohortUtil ωy ωo M (fun _ => (ωy - ωo) / (2 * M)) t) ∧
      ωo + M * p 0 < ωo + M * ((ωy - ωo) / (2 * M)) :=
  let h := olg_ranking hωy hωo hM hp (olg_stationary hωy hωo hM hgap).2 h0
  ⟨h.2.1, h.2.2⟩

/-- AKMM, p. 500: in the stationary monetary equilibrium every cohort obtains
`2 log((ω_y + ω_o)/2)`, which exceeds autarky utility `log ω_y + log ω_o` when `ω_y ≠ ω_o`. -/
theorem olg_stationary_welfare {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hne : ωy ≠ ωo) (t : ℕ) :
    olgCohortUtil ωy ωo M (fun _ => (ωy - ωo) / (2 * M)) t = 2 * Real.log ((ωy + ωo) / 2) ∧
      Real.log ωy + Real.log ωo < 2 * Real.log ((ωy + ωo) / 2) := by
  constructor
  · unfold olgCohortUtil
    have e1 : ωy - M * ((ωy - ωo) / (2 * M)) = (ωy + ωo) / 2 := by field_simp; ring
    have e2 : ωo + M * ((ωy - ωo) / (2 * M)) = (ωy + ωo) / 2 := by field_simp; ring
    rw [e1, e2]; ring
  · rw [← Real.log_mul hωy.ne' hωo.ne', two_mul, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_lt_log (by positivity)
    have : 0 < (ωy - ωo) ^ 2 := by positivity
    nlinarith

/-- AKMM, p. 500: when `ω_y < ω_o` the smoothed allocation `((ω_y + ω_o)/2, (ω_y + ω_o)/2)`
would make the initial old (consumption `ω_o` in autarky) worse off. -/
theorem olg_smoothing_hurts_old {ωy ωo : ℝ} (hlt : ωy < ωo) : (ωy + ωo) / 2 < ωo := by linarith

/-- AKMM, p. 500: the gross return on saving `p_{m,t+1}/p_{m,t}` tends to `ω_o/ω_y < 1` along
every equilibrium with `0 < p_{m,0} < p̄_m`, and equals `1` in the stationary one. -/
theorem olg_return_limit {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {p : ℕ → ℝ} (hp : olgIsEquilibrium ωy ωo M p) (h0 : 0 < p 0)
    (h1 : p 0 < (ωy - ωo) / (2 * M)) :
    Tendsto (fun t => p (t + 1) / p t) atTop (𝓝 (ωo / ωy)) ∧
      (ωo < ωy → (ωy - ωo) / (2 * M) / ((ωy - ωo) / (2 * M)) = 1) := by
  refine ⟨?_, fun hgap => div_self (by have h : 0 < ωy - ωo := (by linarith); positivity)⟩
  rcases (eq_17_5 hωy hωo hM p).1 hp with h | h
  · exact absurd (h 0) h0.ne'
  have hr : ∀ t, p (t + 1) / p t = ωo / (ωy - 2 * M * p t) := fun t => by
    rw [(eq_17_5_div hωo (h t).1 (h (t + 1)).1 (h t).2).2]
    field_simp [(h t).1.ne']
  simp only [hr]
  have hlim := (olg_decreasing_to_zero hωy hωo hM hp h0 h1).2
  have : Tendsto (fun t => ωy - 2 * M * p t) atTop (𝓝 (ωy - 2 * M * 0)) :=
    tendsto_const_nhds.sub (hlim.const_mul (2 * M))
  rw [mul_zero, sub_zero] at this
  exact (tendsto_const_nhds.div this hωy.ne')

/-! ### The link with Miao, Chapter 16 -/

/-- AKMM, §17.2.1 as Miao's Samuelson economy (Miao, §16.1): log utility with `β = 1`,
endowments `(ω_y, ω_o)`, no population or money growth, one agent per cohort, stock `M`. -/
noncomputable def olgMiao (ωy ωo M : ℝ) (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) :
    OXEconomy where
  ox_P := ox_logPrefs 1 one_pos le_rfl
  ox_e1 := ωy
  ox_e2 := ωo
  ox_gn := 1
  ox_gm := 1
  ox_N0 := 1
  ox_M0 := M
  ox_e1_pos := hωy
  ox_e2_pos := hωo
  ox_gn_pos := one_pos
  ox_gm_pos := one_pos
  ox_N0_pos := one_pos
  ox_M0_pos := hM

/-- The book's model matches Miao's: every monetary equilibrium of `olgMiao` (Miao's notion,
dates `t ≥ 1`) has real balances `m̂_{n+1} = 1/(2/(ω_y − ω_o) + c(ω_y/ω_o)ⁿ)`, `c ≥ 0`, and
`ω_y > ω_o` — the paths of `olg_classification`. -/
theorem olg_miao_paths {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    {q cy co m : ℕ → ℝ} (h : (olgMiao ωy ωo M hωy hωo hM).ox_IsMonetary q cy co m) :
    ωo < ωy ∧ ∃ c, 0 ≤ c ∧ ∀ n : ℕ, ((olgMiao ωy ωo M hωy hωo hM).ox_mhat q (n + 1))⁻¹ =
      2 / (ωy - ωo) + c * (ωy / ωo) ^ n := by
  have := (olgMiao ωy ωo M hωy hωo hM).ox_log_paths rfl rfl rfl h
  simpa [olgMiao] using this

/-- AKMM, p. 500 (via Miao's Proposition 16.1.3): for `ω_y > ω_o` the stationary monetary
equilibrium allocation `c_y = (ω_y + ω_o)/2 = c_o` is Pareto optimal. -/
theorem olg_miao_stationary_pareto {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M)
    (hgap : ωo < ωy) :
    (olgMiao ωy ωo M hωy hωo hM).ox_ParetoOptimal (fun _ => (ωy + ωo) / 2)
      (fun _ => (ωy + ωo) / 2) := by
  set E := olgMiao ωy ωo M hωy hωo hM
  have hgap' : E.ox_e2 < E.ox_gn * E.ox_e1 := by simp [E, olgMiao, hgap]
  have hc := E.ox_log_construct rfl rfl rfl hgap' le_rfl
  have hd : ωy - ωo ≠ 0 := by linarith
  have e1 : ∀ t : ℕ, E.ox_e1 - (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
      0 * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹ = (ωy + ωo) / 2 := fun t => by
    simp only [E, olgMiao, zero_mul, add_zero, one_mul, mul_one]
    field_simp; ring
  have e2 : ∀ t : ℕ, E.ox_e2 + E.ox_gn * (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
      0 * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t + 1 - 1))⁻¹ = (ωy + ωo) / 2 := fun t => by
    simp only [E, olgMiao, zero_mul, add_zero, one_mul, mul_one]
    field_simp; ring
  simp only [e1, e2] at hc
  have hR : E.ox_Raut * E.ox_gm < E.ox_gn := by
    rw [E.ox_log_Raut rfl rfl]
    simp only [E, olgMiao, mul_one]
    exact (div_lt_one hωy).2 hgap
  exact (E.proposition_16_1_3 hR hc (fun _ _ => ⟨rfl, rfl⟩)).2 le_rfl

/-- AKMM, p. 500 (via Miao's Proposition 16.1.2): the autarky allocation is Pareto optimal iff
`ω_y ≤ ω_o`; in particular it is inefficient whenever money can be valued. -/
theorem olg_miao_autarky_pareto_iff {ωy ωo M : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hM : 0 < M) :
    (olgMiao ωy ωo M hωy hωo hM).ox_ParetoOptimal (fun _ => ωy) (fun _ => ωo) ↔ ωy ≤ ωo := by
  set E := olgMiao ωy ωo M hωy hωo hM
  refine (E.proposition_16_1_2 E.ox_autarky_isEquilibrium).trans ?_
  rw [E.ox_log_Raut rfl rfl]
  exact one_le_div hωy

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money growth in the overlapping-generations endowment economy

AKMM, §17.2.3, p. 501, and the remark on p. 514. The money stock grows at the gross rate
`1 + μ`, `μ ≥ 0`, `M_t = M₀(1 + μ)ᵗ`; the new money `μM_t` is handed to the old of date `t + 1` as
a lump-sum transfer, so cohort `t` has old-age income `ω_o + p_{m,t+1}μM_t` besides its money.

* `mgIsEquilibrium`; `mg_step_iff`: with `p_{m,t} > 0` the young hold the stock iff
  `p_{m,t+1} > 0` and `m_{t+1}(ω_y − (2 + μ)m_t) = (1 + μ)ω_o m_t`, `m_t = p_{m,t}M_t`.
* `mg_stationary_iff`: a stationary monetary equilibrium (constant real balances `m̄`) exists iff
  `ω_y > (1 + μ)ω_o`, and then `m̄ = (ω_y − (1 + μ)ω_o)/(2 + μ)`.
* `mg_return`: in it the real return on money is `1/(1 + μ)` (below one for `μ > 0`) and the
  price level `P = 1/p_m` grows at the money growth rate, `P_{t+1}/P_t = 1 + μ`.
* `mg_value_strictAntiOn`: the total real value of money `m̄` is strictly decreasing in `μ`, so
  it is lower than without money growth.

**Departure.** On p. 514 the book says the stationary equilibrium has "the rate of inflation
equal[ling] the inverse of the money growth rate". Inflation equals the money growth rate
(`mg_return`); it is the price of money that changes at the inverse rate.
-/

namespace AKMM.Money

/-- AKMM, p. 501: the money stock `M_t = M₀(1 + μ)ᵗ`. -/
noncomputable def mgStock (M0 μ : ℝ) (t : ℕ) : ℝ := M0 * (1 + μ) ^ t

/-- AKMM, p. 501: an equilibrium with money growth: at every date the young optimally buy the
whole stock `M_t`, given the transfer `p_{m,t+1}μM_t` they receive when old. -/
def mgIsEquilibrium (ωy ωo μ M0 : ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ p t) ∧ ∀ t, olgMoneyOptimal ωy (ωo + p (t + 1) * μ * mgStock M0 μ t) (p t) (p (t + 1))
    (mgStock M0 μ t)

/-- The money stock is positive. -/
theorem mgStock_pos {M0 μ : ℝ} (hM : 0 < M0) (hμ : 0 ≤ μ) (t : ℕ) : 0 < mgStock M0 μ t := by
  unfold mgStock; positivity

/-- AKMM, p. 501: `M_{t+1} = (1 + μ)M_t`. -/
theorem mgStock_succ (M0 μ : ℝ) (t : ℕ) : mgStock M0 μ (t + 1) = (1 + μ) * mgStock M0 μ t := by
  unfold mgStock; ring

/-- AKMM, p. 501: one step of an equilibrium with money growth. With `p_{m,t} > 0` the young buy
the stock iff `p_{m,t+1} > 0` and, in real balances `m_t = p_{m,t}M_t`,
`m_{t+1}(ω_y − (2 + μ)m_t) = (1 + μ)ω_o m_t`. -/
theorem mg_step_iff {ωy ωo μ M0 : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hμ : 0 ≤ μ) (hM : 0 < M0)
    {p : ℕ → ℝ} (t : ℕ) (hpt : 0 < p t) (hpt1 : 0 ≤ p (t + 1)) :
    olgMoneyOptimal ωy (ωo + p (t + 1) * μ * mgStock M0 μ t) (p t) (p (t + 1)) (mgStock M0 μ t)
      ↔ 0 < p (t + 1) ∧ p (t + 1) * mgStock M0 μ (t + 1) *
        (ωy - (2 + μ) * (p t * mgStock M0 μ t)) = (1 + μ) * ωo * (p t * mgStock M0 μ t) := by
  have hMt := mgStock_pos hM hμ t
  have hb : 0 < ωo + p (t + 1) * μ * mgStock M0 μ t := by positivity
  rw [olg_moneyOptimal_iff_pos hωy hb hpt hpt1, mgStock_succ]
  set Mt := mgStock M0 μ t
  constructor
  · rintro ⟨-, hd⟩
    have hdpos : 0 < olgDemand ωy (ωo + p (t + 1) * μ * Mt) (p (t + 1) / p t) := by
      rw [← hd]; positivity
    unfold olgDemand at hd hdpos
    split_ifs at hd hdpos with hc
    · exact absurd hdpos (lt_irrefl 0)
    · have h1 : 0 < p (t + 1) := by
        rcases hpt1.lt_or_eq with h' | h'
        · exact h'
        · rw [← h', zero_div, zero_mul] at hc
          exact absurd (by rw [zero_mul, zero_mul, add_zero]; exact hωo.le) hc
      refine ⟨h1, ?_⟩
      field_simp at hd
      linear_combination (-(1 + μ) * Mt) * hd
  · rintro ⟨h1, he⟩
    refine ⟨hMt.le, ?_⟩
    have hcore : p (t + 1) * ωy - (2 + μ) * (p t * p (t + 1) * Mt) - ωo * p t = 0 := by
      have h0 : ((1 + μ) * Mt) * (p (t + 1) * ωy - (2 + μ) * (p t * p (t + 1) * Mt) -
          ωo * p t) = 0 := by linear_combination he
      rcases mul_eq_zero.1 h0 with h' | h'
      · exact absurd h' (by positivity)
      · exact h'
    unfold olgDemand
    have hlt : (ωo + p (t + 1) * μ * Mt) * p t < p (t + 1) * ωy := by
      nlinarith [mul_pos (mul_pos h1 hMt) hpt, mul_pos hpt hMt]
    have hc : ¬ (p (t + 1) / p t * ωy ≤ ωo + p (t + 1) * μ * Mt) := by
      rw [not_le, div_mul_eq_mul_div, lt_div_iff₀ hpt]; linarith
    simp only [hc, ↓reduceIte]
    field_simp
    linear_combination -hcore

/-- **AKMM, p. 501: the stationary monetary equilibrium with money growth.** Prices with constant
real balances `p_{m,t}M_t = m̄ > 0` form an equilibrium iff `ω_y > (1 + μ)ω_o` and
`m̄ = (ω_y − (1 + μ)ω_o)/(2 + μ)`. -/
theorem mg_stationary_iff {ωy ωo μ M0 mb : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hμ : 0 ≤ μ)
    (hM : 0 < M0) (hmb : 0 < mb) :
    mgIsEquilibrium ωy ωo μ M0 (fun t => mb / mgStock M0 μ t) ↔
      (1 + μ) * ωo < ωy ∧ mb = (ωy - (1 + μ) * ωo) / (2 + μ) := by
  have hpos : ∀ t, 0 < mb / mgStock M0 μ t := fun t => div_pos hmb (mgStock_pos hM hμ t)
  have hreal : ∀ t, mb / mgStock M0 μ t * mgStock M0 μ t = mb := fun t =>
    div_mul_cancel₀ _ (mgStock_pos hM hμ t).ne'
  have key : ∀ t, olgMoneyOptimal ωy (ωo + mb / mgStock M0 μ (t + 1) * μ * mgStock M0 μ t)
      (mb / mgStock M0 μ t) (mb / mgStock M0 μ (t + 1)) (mgStock M0 μ t) ↔
      mb * (ωy - (2 + μ) * mb) = (1 + μ) * ωo * mb := fun t => by
    rw [mg_step_iff (p := fun t => mb / mgStock M0 μ t) hωy hωo hμ hM t (hpos t) (hpos _).le]
    simp only [hreal]
    exact ⟨fun h => h.2, fun h => ⟨hpos _, h⟩⟩
  have h2 : (0 : ℝ) < 2 + μ := by linarith
  unfold mgIsEquilibrium
  simp only [key]
  constructor
  · rintro ⟨-, h⟩
    have e := h 0
    have e' : ωy - (2 + μ) * mb = (1 + μ) * ωo := by
      apply mul_left_cancel₀ hmb.ne'; linear_combination e
    refine ⟨?_, ?_⟩
    · nlinarith
    · rw [eq_div_iff h2.ne']; linarith
  · rintro ⟨-, h⟩
    refine ⟨fun t => (hpos t).le, fun _ => ?_⟩
    rw [h]; field_simp; ring

/-- AKMM, p. 501 and p. 522: along a stationary equilibrium with money growth the gross real
return on money is `1/(1 + μ)` and the price level `P_t = 1/p_{m,t}` grows at the money growth
rate: `P_{t+1}/P_t = 1 + μ` (inflation equals money growth, not its inverse as printed on
p. 514). -/
theorem mg_return {μ M0 mb : ℝ} (hμ : 0 ≤ μ) (hM : 0 < M0) (hmb : 0 < mb) (t : ℕ) :
    (mb / mgStock M0 μ (t + 1)) / (mb / mgStock M0 μ t) = 1 / (1 + μ) ∧
      (mb / mgStock M0 μ (t + 1))⁻¹ / (mb / mgStock M0 μ t)⁻¹ = 1 + μ ∧
      (0 < μ → 1 / (1 + μ) < 1) := by
  have hMt := mgStock_pos hM hμ t
  rw [mgStock_succ]
  refine ⟨?_, ?_, fun h => by rw [div_lt_one (by linarith)]; linarith⟩
  · field_simp
  · field_simp

/-- AKMM, p. 501: the real value of the money stock in the stationary equilibrium,
`m̄(μ) = (ω_y − (1 + μ)ω_o)/(2 + μ)`, is strictly decreasing in `μ ≥ 0`; in particular it is
lower than without money growth. -/
theorem mg_value_strictAntiOn {ωy ωo : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) :
    StrictAntiOn (fun μ : ℝ => (ωy - (1 + μ) * ωo) / (2 + μ)) (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiat money has no value in dynastic models

AKMM, §17.3.1, pp. 501–503. A dynastic household holds a real asset `a` (price `q_t = 1/(1+r_t)`),
money `M ≥ 0` and nominal bonds `B` (interest `i_t`); `p_{m,t}` is the price of money.

* `eq_17_11`: the budget (17.8) is the budget (17.11) in total real wealth
  `â_t = a_t + m_t + b_t(1 + i_{t−1})`.
* `eq_17_12`: if a finite optimum holds money in positive amount, the two "static" coefficients
  vanish, `q_t = p_{m,t}/p_{m,t+1} = p_{m,t}/(p_{m,t+1}(1 + i_t))`; `dyn_unbounded` is the
  unbounded-consumption argument; `eq_17_13`: the compact budget.
* `dyn_no_value_of_pos_rate`: with `i_t > 0` (17.12) cannot hold with valued money.
* `eq_17_14`: the discounted value of money telescopes, `q₀⋯q_{T−1}m_T = p_{m,0}M_T`; hence the
  transversality condition forces `p_{m,0} lim M_T ≤ 0` (`dyn_tvc_money_vanishes`), and money
  cannot be valued unless the stock vanishes (`dyn_no_valued_money`).
* `eq_17_15`: the Fisher equation `1 + i_t = (1 + r_t)(1 + π_t)`.

**Departure.** (17.14) is printed `q₀q₁⋯q_T m_T`, but its expansion stops at
`p_{m,T−1}/p_{m,T}`: the discount factor of `m_T` is `q₀⋯q_{T−1}` (`eq_17_14`;
`dyn_printed_product` shows the printed product is `p_{m,0}M_T q_T`). The conclusion is
unaffected. The transversality condition, which the book takes from Chapter 4, is a hypothesis.
-/

open Filter Topology

namespace AKMM.Money

/-- **AKMM, (17.11)**, p. 502: with `m = p_{m,t}M`, `b = p_{m,t}B`, `m′ = p_{m,t+1}M′`,
`b′ = p_{m,t+1}B′`, `â = a + m + b(1 + i_{t−1})` and `â′ = a′ + m′ + b′(1 + i_t)`, the budget
(17.8) is equivalent to (17.11). -/
theorem eq_17_11 {c q a a' pt pt1 M M' B B' i im1 w l τ : ℝ} (hpt1 : pt1 ≠ 0) :
    c + q * a' + pt * M' + pt * B' = w * (1 - l) + a + pt * M + pt * (1 + im1) * B - τ ↔
      c + q * (a' + pt1 * M' + pt1 * B' * (1 + i)) + (pt / pt1 - q) * (pt1 * M') +
        (pt / pt1 - q * (1 + i)) * (pt1 * B') =
          w * (1 - l) - τ + (a + pt * M + pt * B * (1 + im1)) := by
  have e : q * (a' + pt1 * M' + pt1 * B' * (1 + i)) + (pt / pt1 - q) * (pt1 * M') +
      (pt / pt1 - q * (1 + i)) * (pt1 * B') = q * a' + pt * M' + pt * B' := by
    field_simp; ring
  rw [show c + q * (a' + pt1 * M' + pt1 * B' * (1 + i)) + (pt / pt1 - q) * (pt1 * M') +
      (pt / pt1 - q * (1 + i)) * (pt1 * B') = c + (q * (a' + pt1 * M' + pt1 * B' * (1 + i)) +
      (pt / pt1 - q) * (pt1 * M') + (pt / pt1 - q * (1 + i)) * (pt1 * B')) by ring, e]
  constructor <;> intro h <;> linarith

/-- AKMM, p. 502: if the return on bonds differs from the real interest rate, the coefficient
`k = p_{m,t}/p_{m,t+1} − q_t(1 + i_t)` is nonzero and consumption `Y − kb′` is unbounded in the
bond position `b′`. -/
theorem dyn_unbounded {k Y : ℝ} (hk : k ≠ 0) (C : ℝ) : ∃ b, C ≤ Y - k * b :=
  ⟨(Y - C) / k, by rw [mul_div_cancel₀ _ hk]; linarith⟩

/-- **AKMM, (17.12)**, p. 503: suppose `(m*, b*)` (`m* ≥ 0`) maximises consumption
`Y − k_m m − k_b b` over `m ≥ 0` and all `b`, with `k_m = p_{m,t}/p_{m,t+1} − q_t` and
`k_b = p_{m,t}/p_{m,t+1} − q_t(1 + i_t)`. If money is held, `m* > 0`, then `k_m = k_b = 0`. -/
theorem eq_17_12 {km kb Y ms bs : ℝ} (hms : 0 < ms)
    (hopt : ∀ m b, 0 ≤ m → Y - km * m - kb * b ≤ Y - km * ms - kb * bs) : km = 0 ∧ kb = 0 := by
  constructor
  · have h1 := hopt 0 bs le_rfl
    have h2 := hopt (2 * ms) bs (by linarith)
    nlinarith
  · by_contra hk
    obtain ⟨b, hb⟩ := dyn_unbounded (Y := Y - km * ms) hk (Y - km * ms - kb * bs + 1)
    have := hopt ms b hms.le
    linarith

/-- AKMM, (17.12), p. 503: in the book's notation `q_t = p_{m,t}/p_{m,t+1} =
p_{m,t}/(p_{m,t+1}(1 + i_t))`. -/
theorem eq_17_12_prices {q pt pt1 i : ℝ} (hi : 1 + i ≠ 0) (hm : pt / pt1 - q = 0)
    (hb : pt / pt1 - q * (1 + i) = 0) : q = pt / pt1 ∧ q = pt / pt1 / (1 + i) := by
  refine ⟨by linarith, ?_⟩
  rw [eq_div_iff hi]; linarith

/-- **AKMM, (17.13)**, p. 503: under the no-arbitrage conditions the budget (17.11) becomes
`c_t + q_tâ_{t+1} = w_t(1 − l_t) − τ_t + â_t`. -/
theorem eq_17_13 {c q ahat ahat' pt pt1 i m' b' w l τ : ℝ} (hm : pt / pt1 - q = 0)
    (hb : pt / pt1 - q * (1 + i) = 0) :
    c + q * ahat' + (pt / pt1 - q) * m' + (pt / pt1 - q * (1 + i)) * b' = w * (1 - l) - τ + ahat
      ↔ c + q * ahat' = w * (1 - l) - τ + ahat := by
  rw [hm, hb, zero_mul, zero_mul, add_zero, add_zero]

/-- AKMM, p. 503: with a positive nominal rate `i_t > 0` the two no-arbitrage conditions (17.12)
cannot both hold at a positive price of money: money is dominated by bonds. -/
theorem dyn_no_value_of_pos_rate {q pt pt1 i : ℝ} (hpt : 0 < pt) (hpt1 : 0 < pt1) (hi : 0 < i)
    (hm : pt / pt1 - q = 0) : pt / pt1 - q * (1 + i) ≠ 0 := by
  have : q = pt / pt1 := by linarith
  rw [this]
  have : 0 < pt / pt1 := div_pos hpt hpt1
  nlinarith

/-- **AKMM, (17.14)**, p. 503: with `q_s = p_{m,s}/p_{m,s+1}` the discounted real value of money
telescopes, `(∏_{s<T} q_s) p_{m,T}M_T = p_{m,0}M_T`. -/
theorem eq_17_14 {pm : ℕ → ℝ} (hpm : ∀ t, 0 < pm t) (M : ℕ → ℝ) (T : ℕ) :
    (∏ s ∈ Finset.range T, pm s / pm (s + 1)) * (pm T * M T) = pm 0 * M T := by
  have h : ∀ T, (∏ s ∈ Finset.range T, pm s / pm (s + 1)) = pm 0 / pm T := by
    intro T
    induction T with
    | zero => simp [div_self (hpm 0).ne']
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      field_simp [(hpm n).ne', (hpm (n + 1)).ne']
  rw [h, div_mul_eq_mul_div, mul_comm (pm 0), mul_assoc, mul_div_assoc]
  field_simp [(hpm T).ne']

/-- AKMM, (17.14) as printed: the product `q₀⋯q_T` multiplying `m_T` equals `p_{m,0}M_T q_T`, not
`p_{m,0}M_T`. -/
theorem dyn_printed_product {pm : ℕ → ℝ} (hpm : ∀ t, 0 < pm t) (M : ℕ → ℝ) (T : ℕ) :
    (∏ s ∈ Finset.range (T + 1), pm s / pm (s + 1)) * (pm T * M T) =
      pm 0 * M T * (pm T / pm (T + 1)) := by
  rw [Finset.prod_range_succ, mul_comm _ (pm T / pm (T + 1)), mul_assoc, eq_17_14 hpm]
  ring

/-- AKMM, (17.14), p. 503: if the transversality condition holds,
`(∏_{s<T} q_s) m_T → L ≤ 0`, and the price of money is positive, then `p_{m,0} lim M_T ≤ 0`:
`M_T → L/p_{m,0}` with `L ≤ 0`, so (as `M_T ≥ 0`) the money stock vanishes. -/
theorem dyn_tvc_money_vanishes {pm M : ℕ → ℝ} (hpm : ∀ t, 0 < pm t) (hM : ∀ t, 0 ≤ M t)
    {L : ℝ} (hL : L ≤ 0)
    (htvc : Tendsto (fun T => (∏ s ∈ Finset.range T, pm s / pm (s + 1)) * (pm T * M T)) atTop
      (𝓝 L)) : Tendsto M atTop (𝓝 0) := by
  simp only [eq_17_14 hpm] at htvc
  have hl : Tendsto M atTop (𝓝 (L / pm 0)) := by
    have := htvc.div_const (pm 0)
    refine this.congr fun T => ?_
    field_simp [(hpm 0).ne']
  have hge : 0 ≤ L / pm 0 := ge_of_tendsto hl (Eventually.of_forall hM)
  have hle : L / pm 0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hL (hpm 0).le
  rwa [le_antisymm hle hge] at hl

/-- AKMM, p. 503: "if fiat money is not vanishing … money cannot have value". If the money stock
is bounded below by `M̲ > 0`, no path of positive money prices satisfies the no-arbitrage
condition `q_s = p_{m,s}/p_{m,s+1}` together with the transversality condition. -/
theorem dyn_no_valued_money {pm M : ℕ → ℝ} {Mlow L : ℝ} (hMlow : 0 < Mlow)
    (hM : ∀ t, Mlow ≤ M t) (hpm : ∀ t, 0 < pm t) (hL : L ≤ 0)
    (htvc : Tendsto (fun T => (∏ s ∈ Finset.range T, pm s / pm (s + 1)) * (pm T * M T)) atTop
      (𝓝 L)) : False := by
  have h := dyn_tvc_money_vanishes hpm (fun t => hMlow.le.trans (hM t)) hL htvc
  have : Mlow ≤ 0 := ge_of_tendsto' h hM
  linarith

/-- **AKMM, (17.15)**, p. 503: with `q_t = 1/(1 + r_t)`, `1 + π_t = p_{m,t}/p_{m,t+1}` and the
no-arbitrage condition `q_t(1 + i_t) = p_{m,t}/p_{m,t+1}`, `1 + i_t = (1 + r_t)(1 + π_t)`. -/
theorem eq_17_15 {r i infl q : ℝ} (hr : 1 + r ≠ 0) (hq : q = 1 / (1 + r))
    (hna : q * (1 + i) = 1 + infl) : 1 + i = (1 + r) * (1 + infl) := by
  rw [← hna, hq]; field_simp

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cash-in-advance model and the Friedman rule

AKMM, §17.3.2, pp. 504–505, and "The Friedman rule", p. 512. The household maximises
`∑ βᵗu(c_t, l_t)` subject to the cash-in-advance constraint `c_t ≤ m_t` (17.18) and the budget
(17.19); `βᵗλ_t` and `βᵗµ_t` are the multipliers on the budget and the CIA constraint, and the
first-order conditions are (17.20)–(17.23). In a stationary equilibrium `w = z`, `a = 0`,
`c = z(1 − l)`, and the multipliers are constant.

* `eq_17_19`: (17.17) in real balances is (17.19).
* `cia_stationary_growth`: with the money stock growing at the gross rate `γ` and a binding CIA,
  `p_{m,t}/p_{m,t+1} = γ`, `µ = λ(γ − β)/β`, an equilibrium needs `γ ≥ β`, and
  `u₂/u₁ = βz/γ`.
* `eq_17_24`: with a constant stock (`γ = 1`): `p_m = c/M`, `q = β`, `µ = λ(1 − β)/β > 0`,
  `q(1 + i) = 1`, and `u₂/u₁ = βz` (17.24).
* `cia_must_bind`: if the CIA never binds (`µ = 0`) the price of money grows at `1/β` and the
  transversality condition `βᵗλm_t → 0` fails.
* `cia_mrs_lt_mrt`: `βz < z`; with `u = log c + θ log l` CIA consumption `βz/(θ + β)` is below the
  frictionless `z/(θ + 1)` and leisure is higher (`cia_log_consumption`, `cia_log_compare`).
* `cia_friedman_rule`: with `γ = β` (money withdrawn at the rate of discount, taxes
  `τ_t = (1 − β)p_{m,t}M_t`), `µ = 0`, the frictionless condition `u₂/u₁ = z` holds, the nominal
  rate is zero, the transversality condition holds and the nominal stock vanishes.

The first-order conditions are taken as given, as in the book.
-/

open Filter Topology

namespace AKMM.Money

/-- **AKMM, (17.19)**, p. 504: with `m = p_{m,t}M`, `m′ = p_{m,t+1}M′`, the budget (17.17)
`q_ta_{t+1} + p_{m,t}M_{t+1} = a_t + p_{m,t}M_t − c_t + w_t(1 − l_t) − τ_t` is (17.19). -/
theorem eq_17_19 {c q a a' pt pt1 M M' w l τ : ℝ} (hpt1 : pt1 ≠ 0) :
    q * a' + pt * M' = a + pt * M - c + w * (1 - l) - τ ↔
      c + q * a' + pt / pt1 * (pt1 * M') = a + pt * M + w * (1 - l) - τ := by
  have : pt / pt1 * (pt1 * M') = pt * M' := by field_simp
  rw [this]
  constructor <;> intro h <;> linarith

/-- AKMM, pp. 505 and 512: a stationary CIA equilibrium with money growing at the gross rate `γ`
(`M_t = M₀γᵗ`), constant consumption `c > 0`, constant multipliers `λ > 0`, `µ ≥ 0` and a binding
constraint `c = p_{m,t}M_t`. Then `p_{m,t}/p_{m,t+1} = γ`, `µ = λ(γ − β)/β`, so `γ ≥ β`, and
(17.20)–(17.21) give `u₂/u₁ = βz/γ`. -/
theorem cia_stationary_growth {β γ z c M0 lam mu U1 U2 : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β)
    (hγ : 0 < γ) (hc : 0 < c) (hM0 : 0 < M0) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (h20 : U1 = lam + mu) (h21 : U2 = lam * z)
    (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + mu))
    (hbind : ∀ t, c = pm t * (M0 * γ ^ t)) :
    (∀ t, pm t / pm (t + 1) = γ) ∧ mu = lam * (γ - β) / β ∧ β ≤ γ ∧ U2 / U1 = β * z / γ := by
  have hpm : ∀ t, pm t = c / (M0 * γ ^ t) := fun t => by
    rw [hbind t]; field_simp
  have hret : ∀ t, pm t / pm (t + 1) = γ := fun t => by
    rw [hpm, hpm, pow_succ]; field_simp
  have hmu' : mu = lam * (γ - β) / β := by
    have := h23 0; rw [hret] at this
    field_simp; linarith
  refine ⟨hret, hmu', ?_, ?_⟩
  · have : 0 ≤ lam * (γ - β) / β := hmu'.symm ▸ hmu
    have := (div_nonneg_iff.1 this)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · nlinarith [(mul_nonneg_iff_of_pos_left hlam).1 h1]
    · linarith
  · rw [h20, h21, hmu']
    have : lam + lam * (γ - β) / β = lam * γ / β := by field_simp; ring
    rw [this]
    field_simp

/-- **AKMM, (17.24)**, p. 505: in the stationary equilibrium with a constant money stock `M`, a
constant consumption `c > 0` and a binding CIA: `p_m = c/M` is constant, `q = β` (from (17.22)),
the nominal rate satisfies `q(1 + i) = 1`, the CIA multiplier is `µ = λ(1 − β)/β > 0`, and
`u₂(c, 1 − c/z)/u₁(c, 1 − c/z) = zλ/(λ + µ) = βz`. -/
theorem eq_17_24 {β z c M lam mu q i U1 U2 : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hc : 0 < c) (hM : 0 < M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (h20 : U1 = lam + mu) (h21 : U2 = lam * z) (h22 : lam * q = β * lam)
    (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + mu)) (hbind : ∀ t, c = pm t * M)
    (hfisher : q * (1 + i) = pm 0 / pm 1) :
    (∀ t, pm t = c / M) ∧ q = β ∧ q * (1 + i) = 1 ∧ mu = lam * (1 - β) / β ∧ 0 < mu ∧
      U2 / U1 = z * (lam / (lam + mu)) ∧ U2 / U1 = β * z := by
  have hb : ∀ t, c = pm t * (M * 1 ^ t) := fun t => by rw [one_pow, mul_one]; exact hbind t
  obtain ⟨hret, hmu', -, hmrs⟩ :=
    cia_stationary_growth hβ one_pos hc hM hlam hmu h20 h21 h23 hb
  have hq : q = β := by
    have := mul_left_cancel₀ hlam.ne' (h22.trans (mul_comm β lam))
    exact this
  refine ⟨fun t => by rw [hbind t]; field_simp, hq, by rw [hfisher, hret], hmu', ?_, ?_, ?_⟩
  · rw [hmu']; exact div_pos (mul_pos hlam (by linarith)) hβ
  · rw [h20, h21]; field_simp
  · rw [hmrs]; ring

/-- AKMM, p. 505: the CIA must bind in a stationary equilibrium. If it never binds (`µ_t = 0`)
with a constant `λ > 0`, (17.23) makes the price of money grow at `1/β`,
`p_{m,t} = p_{m,0}β^{−t}`, and with a constant stock `M > 0` the transversality condition
`βᵗλ_t m_t → 0` fails. -/
theorem cia_must_bind {β lam M : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hM : 0 < M)
    (hpm : ∀ t, 0 < pm t) (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + 0)) :
    (∀ t, pm t = pm 0 / β ^ t) ∧
      ¬ Tendsto (fun t : ℕ => β ^ t * lam * (pm t * M)) atTop (𝓝 0) := by
  have hstep : ∀ t, pm (t + 1) = pm t / β := fun t => by
    have := h23 t
    rw [add_zero] at this
    have h1 : pm t / pm (t + 1) = β := mul_left_cancel₀ hlam.ne' (this.trans (mul_comm β lam))
    have := (hpm (t + 1)).ne'
    field_simp at h1 ⊢
    linarith
  have hform : ∀ t, pm t = pm 0 / β ^ t := fun t => by
    induction t with
    | zero => simp
    | succ n ih => rw [hstep, ih, pow_succ]; field_simp
  refine ⟨hform, fun h => ?_⟩
  have hc : (fun t : ℕ => β ^ t * lam * (pm t * M)) = fun _ => lam * (pm 0 * M) := by
    funext t; rw [hform]; field_simp
  rw [hc] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  have : 0 < lam * (pm 0 * M) := by have := hpm 0; positivity
  linarith

/-- AKMM, p. 505: in the CIA economy the marginal rate of substitution between leisure and
consumption, `βz`, is below the marginal rate of transformation `z`. -/
theorem cia_mrs_lt_mrt {β z : ℝ} (hβ1 : β < 1) (hz : 0 < z) : β * z < z := by nlinarith

/-- AKMM, p. 505 (an instance): with `u(c, l) = log c + θ log l` and `l = 1 − c/z`, the condition
`u₂/u₁ = θc/l = κz` holds at `c ∈ (0, z)` iff `c = κz/(θ + κ)`. -/
theorem cia_log_consumption {θ κ z c : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) (hz : 0 < z) (hcz : c < z) :
    θ * c / (1 - c / z) = κ * z ↔ c = κ * z / (θ + κ) := by
  have hl : 0 < 1 - c / z := by rw [sub_pos, div_lt_one hz]; exact hcz
  rw [div_eq_iff hl.ne', eq_div_iff (by linarith)]
  constructor <;> intro h <;> field_simp at h ⊢ <;> linarith

/-- AKMM, p. 505: "in the CIA economy leisure is higher and consumption is lower": with
`u = log c + θ log l`, CIA consumption `βz/(θ + β)` is below the frictionless `z/(θ + 1)`. -/
theorem cia_log_compare {θ β z : ℝ} (hθ : 0 < θ) (hβ : 0 < β) (hβ1 : β < 1) (hz : 0 < z) :
    β * z / (θ + β) < 1 * z / (θ + 1) ∧ 1 - (1 * z / (θ + 1)) / z < 1 - (β * z / (θ + β)) / z := by
  have h1 : β * z / (θ + β) < 1 * z / (θ + 1) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_pos hθ hz]
  refine ⟨h1, ?_⟩
  have := div_lt_div_of_pos_right h1 hz
  linarith

/-- **AKMM, p. 505: the Friedman rule.** Withdraw money at the rate of discount, `M_t = M₀βᵗ`,
through the lump-sum tax `τ_t = (1 − β)p_{m,t}M_t`. In the stationary CIA equilibrium with
constant consumption the CIA multiplier is zero, the frictionless condition `u₂/u₁ = z` holds,
the return on money equals the real interest rate (`q = β`, nominal rate `i = 0`), the tax equals
`(1 − β)c`, the transversality condition `βᵗλm_t → 0` holds and the nominal stock vanishes. -/
theorem cia_friedman_rule {β z c M0 lam mu q i U1 U2 : ℝ} {pm : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hc : 0 < c) (hM0 : 0 < M0) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (h20 : U1 = lam + mu) (h21 : U2 = lam * z) (h22 : lam * q = β * lam)
    (h23 : ∀ t, lam * (pm t / pm (t + 1)) = β * (lam + mu))
    (hbind : ∀ t, c = pm t * (M0 * β ^ t)) (hfisher : q * (1 + i) = pm 0 / pm 1) :
    mu = 0 ∧ U2 / U1 = z ∧ i = 0 ∧
      (∀ t, (1 - β) * (pm t * (M0 * β ^ t)) = (1 - β) * c) ∧
      Tendsto (fun t : ℕ => β ^ t * lam * (pm t * (M0 * β ^ t))) atTop (𝓝 0) ∧
      Tendsto (fun t : ℕ => M0 * β ^ t) atTop (𝓝 0) := by
  obtain ⟨hret, hmu', -, hmrs⟩ :=
    cia_stationary_growth hβ hβ hc hM0 hlam hmu h20 h21 h23 hbind
  have hq : q = β := mul_left_cancel₀ hlam.ne' (h22.trans (mul_comm β lam))
  have hpow : Tendsto (fun t : ℕ => β ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1
  refine ⟨by rw [hmu', sub_self, mul_zero, zero_div], by rw [hmrs]; field_simp, ?_,
    fun t => by rw [← hbind t], ?_, by simpa using hpow.const_mul M0⟩
  · rw [hret, hq] at hfisher
    have : β * i = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ.ne'
    · exact h
  · have : (fun t : ℕ => β ^ t * lam * (pm t * (M0 * β ^ t))) = fun t => β ^ t * (lam * c) := by
      funext t; rw [← hbind t]; ring
    rw [this]
    simpa using hpow.mul_const (lam * c)

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money reduces transactions costs

AKMM, §17.3.2, "Money reduces transactions costs", pp. 509–510. Purchases cost `ψ(x)c` with
`x = c/(M_{t+1}/P_t)` (consumption over real balances chosen at `t`) and `ψ(x) = κx^η`,
`κ, η > 0`.

* `tc_cost_homogeneous`: the cost `ψ(c/m)c` is homogeneous of degree one in `(c, m)`;
  `tc_psi_hasDerivAt`: `ψ′(x) = κηx^{η−1}`.
* `eq_17_28`: (17.26) and (17.27) give `1 − q_t/(p_{m,t}/p_{m,t+1}) = ψ′(x)x²`;
  `tc_fisher_lhs`: with the Fisher equation the left side is `i/(1 + i)`.
* `eq_17_29`: `M_{t+1}/P_t = c_t((1/(κη)) i_t/(1 + i_t))^{−1/(1+η)}`.
* `tc_demand_homogeneous`, `tc_demand_elasticity`, `tc_log_demand`: money demand is
  proportional to consumption and has the constant elasticity `−1/(1 + η)` with respect to the
  opportunity cost `i/(1 + i)`; `tc_demand_strictAntiOn`: it is decreasing in `i`.

The first-order conditions are taken as given, as in the book.
-/

namespace AKMM.Money

/-- AKMM, p. 510: the transaction-cost function `ψ(x) = κx^η`. -/
noncomputable def tcPsi (κ η x : ℝ) : ℝ := κ * x ^ η

/-- AKMM, p. 510: transactions costs `ψ(c/m)c` are homogeneous of degree one in consumption and
real balances jointly. -/
theorem tc_cost_homogeneous (κ η c m : ℝ) {k : ℝ} (hk : k ≠ 0) :
    tcPsi κ η (k * c / (k * m)) * (k * c) = k * (tcPsi κ η (c / m) * c) := by
  rw [mul_div_mul_left _ _ hk]; ring

/-- AKMM, p. 510: `ψ′(x) = κηx^{η−1}` for `x > 0`. -/
theorem tc_psi_hasDerivAt (κ η : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (tcPsi κ η) (κ * η * x ^ (η - 1)) x := by
  have := (Real.hasDerivAt_rpow_const (p := η) (Or.inl hx.ne')).const_mul κ
  refine this.congr_deriv ?_
  ring

/-- **AKMM, (17.28)**, p. 510: from the asset condition (17.26) `λ_tq_t = βλ_{t+1}` and the
money condition (17.27) `λ_t(p_{m,t}/p_{m,t+1})(1 − ψ′x²) = βλ_{t+1}`,
`1 − q_t/(p_{m,t}/p_{m,t+1}) = ψ′x²`. -/
theorem eq_17_28 {lam lam' q R D β : ℝ} (hlam : lam ≠ 0) (hR : R ≠ 0)
    (h26 : lam * q = β * lam') (h27 : lam * R * (1 - D) = β * lam') : 1 - q / R = D := by
  have : R * (1 - D) = q := mul_left_cancel₀ hlam (by rw [← mul_assoc, h27, h26])
  rw [← this]; field_simp; ring

/-- AKMM, p. 510: with the Fisher equation `q_t(1 + i_t) = p_{m,t}/p_{m,t+1}`, the left side of
(17.28) is the opportunity cost `i_t/(1 + i_t)`. -/
theorem tc_fisher_lhs {q i R : ℝ} (hi : 1 + i ≠ 0) (hq : q ≠ 0) (hF : q * (1 + i) = R) :
    1 - q / R = i / (1 + i) := by
  rw [← hF]; field_simp; ring

/-- AKMM, (17.29), p. 510: the money demand `M_{t+1}/P_t = c((1/(κη)) s)^{−1/(1+η)}` as a
function of consumption `c` and the opportunity cost `s = i/(1 + i)`. -/
noncomputable def tcDemand (κ η c s : ℝ) : ℝ := c * (1 / (κ * η) * s) ^ (-(1 / (1 + η)))

/-- **AKMM, (17.29)**, p. 510: with `ψ(x) = κx^η` and `x = c/m` (`m = M_{t+1}/P_t > 0`), the
condition (17.28) `i/(1 + i) = ψ′(x)x²` holds iff `m = c((1/(κη)) i/(1 + i))^{−1/(1+η)}`. -/
theorem eq_17_29 {κ η c m i : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hc : 0 < c) (hm : 0 < m)
    (hi : 0 < i) :
    i / (1 + i) = κ * η * (c / m) ^ (η - 1) * (c / m) ^ 2 ↔ m = tcDemand κ η c (i / (1 + i)) := by
  set x := c / m with hx
  have hx0 : 0 < x := div_pos hc hm
  set s := i / (1 + i) with hs
  have hs0 : 0 < s := div_pos hi (by linarith)
  have hA : 0 < 1 / (κ * η) * s := by positivity
  have hpow : x ^ (η - 1) * x ^ 2 = x ^ (1 + η) := by
    rw [show (x ^ 2 : ℝ) = x ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hx0]; ring_nf
  have h1η : (1 + η) ≠ 0 := by linarith
  rw [mul_assoc, hpow]
  unfold tcDemand
  constructor
  · intro h
    have hxA : x ^ (1 + η) = 1 / (κ * η) * s := by rw [h]; field_simp
    have hx' : x = (1 / (κ * η) * s) ^ (1 / (1 + η)) := by
      rw [← hxA, one_div, Real.rpow_rpow_inv hx0.le h1η]
    rw [Real.rpow_neg hA.le, ← hx', hx]
    field_simp
  · intro h
    have hx' : x = (1 / (κ * η) * s) ^ (1 / (1 + η)) := by
      rw [hx, h, Real.rpow_neg hA.le]
      have := Real.rpow_pos_of_pos hA (1 / (1 + η))
      field_simp
    rw [hx', ← Real.rpow_mul hA.le, one_div_mul_cancel h1η, Real.rpow_one]
    field_simp

/-- AKMM, p. 510: money demand is proportional to consumption (unit consumption elasticity). -/
theorem tc_demand_homogeneous (κ η c s k : ℝ) : tcDemand κ η (k * c) s = k * tcDemand κ η c s := by
  unfold tcDemand; ring

/-- AKMM, p. 510: the elasticity of money demand with respect to the opportunity cost
`s = i/(1 + i)` is the constant `−1/(1 + η)`: scaling `s` by `k > 0` scales demand by
`k^{−1/(1+η)}`. -/
theorem tc_demand_elasticity {κ η c s k : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hs : 0 < s)
    (hk : 0 < k) : tcDemand κ η c (k * s) = k ^ (-(1 / (1 + η))) * tcDemand κ η c s := by
  unfold tcDemand
  rw [show 1 / (κ * η) * (k * s) = k * (1 / (κ * η) * s) by ring,
    Real.mul_rpow hk.le (by positivity)]
  ring

/-- AKMM, p. 510: in logarithms, `log m = log c − (1/(1 + η)) log(s/(κη))`, linear in `log s`
with slope `−1/(1 + η)`. -/
theorem tc_log_demand {κ η c s : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hc : 0 < c) (hs : 0 < s) :
    Real.log (tcDemand κ η c s) =
      Real.log c - 1 / (1 + η) * (Real.log s - Real.log (κ * η)) := by
  unfold tcDemand
  have hA : 0 < 1 / (κ * η) * s := by positivity
  rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos hA _).ne', Real.log_rpow hA,
    Real.log_mul (by positivity) hs.ne', one_div (κ * η), Real.log_inv]
  ring

/-- AKMM, p. 510: real money demand is strictly decreasing in the nominal interest rate. -/
theorem tc_demand_strictAntiOn {κ η c : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hc : 0 < c) :
    StrictAntiOn (fun i => tcDemand κ η c (i / (1 + i))) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  simp only [tcDemand]
  apply mul_lt_mul_of_pos_left _ hc
  apply Real.rpow_lt_rpow_of_neg (by positivity) _ (by
    have : 0 < 1 / (1 + η) := by positivity
    linarith)
  apply mul_lt_mul_of_pos_left _ (by positivity)
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Money in the utility function

AKMM, §17.3.2, "Money in the utility function", p. 511. Preferences
`∑ βᵗ[u(c_t, m_{t+1}p_{m,t}/p_{m,t+1}) + v(l_t)]` (17.30), budget (17.19), first-order conditions
(17.31)–(17.34).

* `eq_17_35`: (17.31), (17.33), (17.34) and the Fisher equation give `u₂/u₁ = i/(1 + i)`.
* `miu_homothetic_partials`, `miu_homothetic_mrs`: for a constant-returns index
  `h(c, m) = cφ(m/c)` (every constant-returns function on `c > 0` has this form) and
  `u = F ∘ h`, `u₂/u₁ = φ′(x)/(φ(x) − xφ′(x))` depends only on `x = m/c`.
* `miu_homothetic_demand`: if this ratio is injective in `x`, the money demand `m/c` is a
  function of `i/(1 + i)` alone.
* `miu_ces_crs`: the CES composite of Galí (2015, p. 35), imported from the
  `ClassicalMonetaryModel` dependency, is of this form (it is AKMM's `h` of p. 518).
-/

namespace AKMM.Money

/-- **AKMM, (17.35)**, p. 511: from `u₁ = λ_t` (17.31), `λ_tq_t = βλ_{t+1}` (17.33),
`λ_tR = u₂R + βλ_{t+1}` (17.34), `R = p_{m,t}/p_{m,t+1}`, and the Fisher equation
`q_t(1 + i_t) = R`: `1 = u₂/u₁ + 1/(1 + i)`, i.e. `u₂/u₁ = i/(1 + i)`. -/
theorem eq_17_35 {U1 U2 lam lam' q R i β : ℝ} (hlam : 0 < lam) (hR : R ≠ 0) (hi : 1 + i ≠ 0)
    (h31 : U1 = lam) (h33 : lam * q = β * lam') (h34 : lam * R = U2 * R + β * lam')
    (hF : q * (1 + i) = R) : 1 = U2 / U1 + 1 / (1 + i) ∧ U2 / U1 = i / (1 + i) := by
  have hq : q = R / (1 + i) := by rw [← hF]; field_simp
  have h : lam = U2 + lam / (1 + i) := by
    have : lam * R = U2 * R + lam * q := by rw [h34, h33]
    rw [hq] at this
    apply mul_right_cancel₀ hR
    rw [this]; field_simp
  have h1 : 1 = U2 / U1 + 1 / (1 + i) := by
    have hU2 : U2 = lam - lam / (1 + i) := by linarith
    rw [h31, hU2]; field_simp; ring
  refine ⟨h1, ?_⟩
  have : U2 / U1 = 1 - 1 / (1 + i) := by linarith
  rw [this]; field_simp; ring

/-- AKMM, p. 511: partial derivatives of a constant-returns index `h(c, m) = cφ(m/c)`:
`h_c = φ(x) − xφ′(x)` and `h_m = φ′(x)`, `x = m/c`. -/
theorem miu_homothetic_partials {φ : ℝ → ℝ} {φ' c m : ℝ} (hc : c ≠ 0)
    (hφ : HasDerivAt φ φ' (m / c)) :
    HasDerivAt (fun c' => c' * φ (m / c')) (φ (m / c) - m / c * φ') c ∧
      HasDerivAt (fun m' => c * φ (m' / c)) φ' m := by
  constructor
  · have hd : HasDerivAt (fun c' => m / c') (-(m / c ^ 2)) c := by
      have := (hasDerivAt_inv hc).const_mul m
      refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun x => by simp [div_eq_mul_inv]
    have := (hasDerivAt_id' c).mul (hφ.comp c hd)
    refine this.congr_deriv ?_
    have e : c * (φ' * -(m / c ^ 2)) = -(m / c * φ') := by field_simp
    rw [Function.comp_apply, e]
    ring
  · have hd : HasDerivAt (fun m' => m' / c) (1 / c) m := by
      simpa using (hasDerivAt_id' m).div_const c
    have := (hφ.comp m hd).const_mul c
    refine this.congr_deriv ?_
    field_simp

/-- AKMM, p. 511: with `u = F ∘ h`, `F′(h) ≠ 0`, `h(c, m) = cφ(m/c)`, the marginal rate of
substitution `u₂/u₁ = F′h_m/(F′h_c) = φ′(x)/(φ(x) − xφ′(x))` depends only on `x = m/c`. -/
theorem miu_homothetic_mrs {F φ : ℝ → ℝ} {F' φ' c m : ℝ} (hc : c ≠ 0)
    (hF : HasDerivAt F F' (c * φ (m / c))) (hφ : HasDerivAt φ φ' (m / c)) (hF0 : F' ≠ 0) :
    ∃ U1 U2, HasDerivAt (fun c' => F (c' * φ (m / c'))) U1 c ∧
      HasDerivAt (fun m' => F (c * φ (m' / c))) U2 m ∧
      U2 / U1 = φ' / (φ (m / c) - m / c * φ') := by
  obtain ⟨h1, h2⟩ := miu_homothetic_partials hc hφ
  refine ⟨F' * (φ (m / c) - m / c * φ'), F' * φ', hF.comp c h1, hF.comp m h2, ?_⟩
  rw [mul_div_mul_left _ _ hF0]

/-- AKMM, p. 511: if the marginal rate of substitution `g(x) = φ′(x)/(φ(x) − xφ′(x))` is
injective on the positive ratios, then any two consumers facing the same opportunity cost
`i/(1 + i)` (so `g(m/c) = g(m′/c′) = i/(1 + i)` by (17.35)) hold the same ratio of real
balances to consumption: money demand is `m/c = g⁻¹(i/(1 + i))`. -/
theorem miu_homothetic_demand {g : ℝ → ℝ} (hg : Set.InjOn g (Set.Ioi 0)) {c m c' m' i : ℝ}
    (hx : 0 < m / c) (hx' : 0 < m' / c') (h : g (m / c) = i / (1 + i))
    (h' : g (m' / c') = i / (1 + i)) : m / c = m' / c' :=
  hg hx hx' (h.trans h'.symm)

/-- AKMM, p. 518 (with Galí 2015, p. 35): the CES index
`h(c, m) = ((1 − ω)c^ρ + ωm^ρ)^{1/ρ}` (Galí's `composite ω (1 − ρ)`) has constant returns,
`h(c, m) = c h(1, m/c)`, so it is homothetic in the sense above. -/
theorem miu_ces_crs {ω ρ c m : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m) :
    Gali.ClassicalMonetaryModel.MIUNonseparable.composite ω (1 - ρ) c m =
      c * Gali.ClassicalMonetaryModel.MIUNonseparable.composite ω (1 - ρ) 1 (m / c) := by
  have := Gali.ClassicalMonetaryModel.MIUNonseparable.composite_homogeneous (ν := 1 - ρ)
    hω0 hω1 one_pos (div_pos hm hc) hc
  rw [mul_one, mul_div_cancel₀ _ hc.ne'] at this
  exact this

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hyperinflations in the cash-in-advance model

AKMM, §17.3.3, "Hyperinflation", pp. 512–513, with footnotes 11–12. In the CIA model with a
binding constraint, `z = 1`, money growth `M_{t+1} = γM_t` (`γ > 1`) and `u(c, l) = u(c) + l`, real
balances satisfy (17.38) `γm_t = βm_{t+1}u′(m_{t+1})`, with no initial condition.

* `eq_17_36`, `eq_17_37`, `eq_17_38`: the derivation from (17.20)–(17.23).
* `hypIsPath`; `hyp_steady_iff`: the positive steady state `u′(m̄) = γ/β`.
* `hyp_exists_path`: if `u′` is positive, continuous and strictly decreasing and
  `lim_{m→0} m u′(m) = 0`, then from every `m₀ ∈ (0, m̄)` there is a path of (17.38), strictly
  decreasing, converging to `0`.
* `hyp_all_paths`: if moreover `m u′(m)` is strictly increasing, the path from `m₀` is unique
  and every path with `m₀ ∈ (0, m̄)` decreases to `0`; paths with `m₀ > m̄` increase
  (`hyp_above_increasing`), so `m̄` is unstable (footnote 11).
* `hyp_return_lt`: along such paths the real return on money is below the stationary `1/γ`, so
  the CIA binds (footnote 11).
* `hyp_local_stable`, `hyp_local_unstable`: local stability at `0` when `u′ > γ/β` near `0`,
  instability when `u′ < γ/β` near `0` (footnote 11, `u′(0) ≷ γ/β`).
* `hyp_log_unique`: with `u = log`, `m_t = β/γ` is the unique path (footnote 12).

**Departure.** The book says that "for any initial real balances `0 < m₀ < m̄` the path of real
balances defined by (17.38) converges" to zero. Equation (17.38) defines `m_{t+1}` only
implicitly; without monotonicity of `m u′(m)` it may have several solutions, and we prove
existence of a convergent path (`hyp_exists_path`). Convergence of every path, and uniqueness,
are proved under the added hypothesis that `m u′(m)` is strictly increasing (`hyp_all_paths`).
-/

open Filter Topology

namespace AKMM.Money

/-- **AKMM, (17.36)**, p. 513: with a binding CIA, `z = w = 1`, (17.20) `u₁ = λ + µ`, (17.21)
`u₂ = λ` and (17.23) `λ_tR_t = β(λ_{t+1} + µ_{t+1})`, `R_t = p_{m,t}/p_{m,t+1}`, give
`u₂(t)R_t = βu₁(t + 1)`. -/
theorem eq_17_36 {β : ℝ} {U1 U2 lam mu R : ℕ → ℝ} (h20 : ∀ t, U1 t = lam t + mu t)
    (h21 : ∀ t, U2 t = lam t) (h23 : ∀ t, lam t * R t = β * (lam (t + 1) + mu (t + 1)))
    (t : ℕ) : U2 t * R t = β * U1 (t + 1) := by
  rw [h21, h23, h20]

/-- **AKMM, (17.37)**, p. 513: with `M_{t+1} = γM_t` and `m_t = p_{m,t}M_t`,
`p_{m,t}/p_{m,t+1} = γm_t/m_{t+1}`. -/
theorem eq_17_37 {γ pt pt1 Mt : ℝ} (hγ : γ ≠ 0) (hpt1 : pt1 ≠ 0) (hM : Mt ≠ 0) :
    pt / pt1 = γ * (pt * Mt) / (pt1 * (γ * Mt)) := by
  field_simp

/-- **AKMM, (17.38)**, p. 513: with `u(c, l) = u(c) + l` (`u₂ = 1`, `u₁ = u′(c)`, `c = m`),
(17.37) `γu₂m_t/m_{t+1} = βu₁(t + 1)` is `γm_t = βm_{t+1}u′(m_{t+1})`. -/
theorem eq_17_38 {β γ mt mt1 du1 : ℝ} (hmt1 : mt1 ≠ 0) :
    γ * 1 * mt / mt1 = β * du1 ↔ γ * mt = β * (mt1 * du1) := by
  rw [mul_one, div_eq_iff hmt1]
  constructor <;> intro h <;> linarith

/-- AKMM, (17.38): a path of positive real balances. -/
def hypIsPath (β γ : ℝ) (du : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ γ * m t = β * (m (t + 1) * du (m (t + 1)))

/-- AKMM, p. 513: a constant `m̄ > 0` is a path iff `u′(m̄) = γ/β`. -/
theorem hyp_steady_iff {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hmb : 0 < mb) :
    hypIsPath β γ du (fun _ => mb) ↔ du mb = γ / β := by
  unfold hypIsPath
  constructor
  · intro h
    have := (h 0).2
    field_simp
    nlinarith [this]
  · intro h t
    refine ⟨hmb, ?_⟩
    rw [h]; field_simp

/-- One step of (17.38) downward: if `u′` is continuous and strictly decreasing on `(0, ∞)`,
`m u′(m) → 0` as `m → 0⁺`, `u′(m̄) = γ/β` and `0 < x < m̄`, there is `y ∈ (0, x)` with
`γx = βyu′(y)`. -/
theorem hyp_step_exists {β γ mb x : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hlim : Tendsto (fun m => m * du m) (𝓝[>] 0) (𝓝 0)) (hmb : du mb = γ / β)
    (hx : 0 < x) (hxm : x < mb) : ∃ y, 0 < y ∧ y < x ∧ γ * x = β * (y * du y) := by
  have htar : 0 < γ * x / β := by positivity
  have hgx : γ * x / β < x * du x := by
    have : γ / β < du x := hmb ▸ hanti hx (hx.trans hxm) hxm
    calc γ * x / β = x * (γ / β) := by ring
      _ < x * du x := mul_lt_mul_of_pos_left this hx
  obtain ⟨ε, hε, hε0, hεx⟩ : ∃ ε, ε * du ε < γ * x / β ∧ 0 < ε ∧ ε < x := by
    have h1 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m * du m < γ * x / β := hlim (gt_mem_nhds htar)
    have h2 : ∀ᶠ m in 𝓝[>] (0 : ℝ), m ∈ Set.Ioo 0 x := Ioo_mem_nhdsGT hx
    obtain ⟨ε, h1', h2'⟩ := (h1.and h2).exists
    exact ⟨ε, h1', h2'⟩
  have hgc : ContinuousOn (fun m => m * du m) (Set.Icc ε x) :=
    continuousOn_id.mul (hcont.mono fun m hm => lt_of_lt_of_le hε0 hm.1)
  obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc hεx.le hgc ⟨hε.le, hgx.le⟩
  refine ⟨y, lt_of_lt_of_le hε0 hy.1, lt_of_le_of_ne hy.2 ?_, ?_⟩
  · rintro rfl; simp only at hyv; linarith
  · simp only at hyv; rw [hyv]; field_simp

/-- A strictly decreasing path of (17.38) starting below `m̄` converges to `0` (`u′` continuous
and strictly decreasing, so `m̄` is the only positive steady state). -/
theorem hyp_tendsto_zero {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hmb : du mb = γ / β) (hmb0 : 0 < mb) {m : ℕ → ℝ} (hm : hypIsPath β γ du m)
    (hdec : Antitone m) (h0 : m 0 < mb) : Tendsto m atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range m) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hm t).1.le⟩
  have hL := tendsto_atTop_ciInf hdec hbdd
  set L := ⨅ t, m t
  have hL0 : 0 ≤ L := le_ciInf fun t => (hm t).1.le
  rcases hL0.lt_or_eq with hLpos | hLz
  · exfalso
    have hshift : Tendsto (fun t => m (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
    have hcL : ContinuousAt du L := hcont.continuousAt (Ioi_mem_nhds hLpos)
    have hlhs : Tendsto (fun t => γ * m t) atTop (𝓝 (γ * L)) := hL.const_mul γ
    have hrhs : Tendsto (fun t => β * (m (t + 1) * du (m (t + 1)))) atTop
        (𝓝 (β * (L * du L))) := (hshift.mul (hcL.tendsto.comp hshift)).const_mul β
    have heq : γ * L = β * (L * du L) :=
      tendsto_nhds_unique hlhs (hrhs.congr fun t => ((hm t).2).symm)
    have hduL : du L = γ / β := by field_simp; nlinarith [heq]
    have hLle : L ≤ m 0 := ciInf_le hbdd 0
    have : L = mb := hanti.injOn hLpos hmb0 (hduL.trans hmb.symm)
    linarith
  · rw [← hLz] at hL; exact hL

/-- **AKMM, p. 513: hyperinflation paths.** If `u′` is continuous and strictly
decreasing on `(0, ∞)`, `lim_{m→0} m u′(m) = 0` and `u′(m̄) = γ/β`, `m̄ > 0`, then for every
`m₀ ∈ (0, m̄)` there is a path of (17.38) from `m₀` that is strictly decreasing and converges to
zero: the value of real balances vanishes in the limit. -/
theorem hyp_exists_path {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hlim : Tendsto (fun m => m * du m) (𝓝[>] 0) (𝓝 0)) (hmb : du mb = γ / β) (hmb0 : 0 < mb)
    {m0 : ℝ} (h0 : 0 < m0) (h1 : m0 < mb) :
    ∃ m : ℕ → ℝ, m 0 = m0 ∧ hypIsPath β γ du m ∧ StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  classical
  have hex : ∀ x, 0 < x ∧ x < mb → ∃ y, 0 < y ∧ y < x ∧ γ * x = β * (y * du y) :=
    fun x hx => hyp_step_exists hβ hγ hcont hanti hlim hmb hx.1 hx.2
  let step : ℝ → ℝ := fun x => if h : 0 < x ∧ x < mb then Classical.choose (hex x h) else 0
  have hstep : ∀ x, 0 < x → x < mb →
      0 < step x ∧ step x < x ∧ γ * x = β * (step x * du (step x)) := fun x hx hxm => by
    have h : 0 < x ∧ x < mb := ⟨hx, hxm⟩
    simp only [step, h, and_self, ↓reduceDIte]
    exact Classical.choose_spec (hex x h)
  let m : ℕ → ℝ := fun t => step^[t] m0
  have hsucc : ∀ t, m (t + 1) = step (m t) := fun t => Function.iterate_succ_apply' _ _ _
  have hinv : ∀ t, 0 < m t ∧ m t < mb := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      rw [hsucc]
      obtain ⟨a, b, -⟩ := hstep _ ih.1 ih.2
      exact ⟨a, b.trans ih.2⟩
  have hpath : hypIsPath β γ du m := fun t => by
    refine ⟨(hinv t).1, ?_⟩
    rw [hsucc]; exact (hstep _ (hinv t).1 (hinv t).2).2.2
  have hanti' : StrictAnti m := strictAnti_nat_of_succ_lt fun t => by
    rw [hsucc]; exact (hstep _ (hinv t).1 (hinv t).2).2.1
  exact ⟨m, rfl, hpath, hanti', hyp_tendsto_zero hβ hcont hanti hmb hmb0 hpath
    hanti'.antitone h1⟩

/-- **AKMM, p. 513**, under the added hypothesis that `m u′(m)` is strictly increasing: every
path of (17.38) with `m₀ ∈ (0, m̄)` is strictly decreasing and converges to `0`, and the path is
determined by `m₀`. -/
theorem hyp_all_paths {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hcont : ContinuousOn du (Set.Ioi 0)) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hg : StrictMonoOn (fun m => m * du m) (Set.Ioi 0)) (hmb : du mb = γ / β) (hmb0 : 0 < mb)
    {m : ℕ → ℝ} (hm : hypIsPath β γ du m) (h1 : m 0 < mb) :
    StrictAnti m ∧ Tendsto m atTop (𝓝 0) ∧
      ∀ m' : ℕ → ℝ, hypIsPath β γ du m' → m' 0 = m 0 → m' = m := by
  have hdec : ∀ t, m t < mb → m (t + 1) < m t := fun t ht => by
    have hlt : γ / β < du (m t) := hmb ▸ hanti (hm t).1 hmb0 ht
    have : m (t + 1) * du (m (t + 1)) < m t * du (m t) := by
      have e := (hm t).2
      have : γ * m t < β * (m t * du (m t)) := by
        have := mul_lt_mul_of_pos_left hlt (mul_pos hβ (hm t).1)
        rw [show β * (m t) * (γ / β) = γ * m t by field_simp] at this
        linarith
      nlinarith
    by_contra hn
    have := hg.le_iff_le (hm t).1 (hm (t + 1)).1 |>.2 (not_lt.1 hn)
    linarith
  have hbelow : ∀ t, m t < mb := fun t => by
    induction t with
    | zero => exact h1
    | succ n ih => exact (hdec n ih).trans ih
  have hsa : StrictAnti m := strictAnti_nat_of_succ_lt fun t => hdec t (hbelow t)
  refine ⟨hsa, hyp_tendsto_zero hβ hcont hanti hmb hmb0 hm hsa.antitone h1,
    fun m' hm' h0 => funext fun t => ?_⟩
  induction t with
  | zero => exact h0
  | succ n ih =>
    have e1 := (hm' n).2
    have e2 := (hm n).2
    rw [ih] at e1
    exact hg.injOn (hm' (n + 1)).1 (hm (n + 1)).1
      (mul_left_cancel₀ hβ.ne' (e1.symm.trans e2))

/-- AKMM, footnote 11, p. 513: with `m u′(m)` strictly increasing, a path starting above `m̄`
is strictly increasing: the monetary steady state is unstable. -/
theorem hyp_above_increasing {β γ mb : ℝ} {du : ℝ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hg : StrictMonoOn (fun m => m * du m) (Set.Ioi 0))
    (hmb : du mb = γ / β) (hmb0 : 0 < mb) {m : ℕ → ℝ} (hm : hypIsPath β γ du m)
    (h1 : mb < m 0) : StrictMono m := by
  have hinc : ∀ t, mb < m t → m t < m (t + 1) := fun t ht => by
    have hlt : du (m t) < γ / β := hmb ▸ hanti hmb0 (hm t).1 ht
    have : m t * du (m t) < m (t + 1) * du (m (t + 1)) := by
      have e := (hm t).2
      have : β * (m t * du (m t)) < γ * m t := by
        have := mul_lt_mul_of_pos_left hlt (mul_pos hβ (hm t).1)
        rw [show β * (m t) * (γ / β) = γ * m t by field_simp] at this
        linarith
      nlinarith
    by_contra hn
    have := hg.le_iff_le (hm (t + 1)).1 (hm t).1 |>.2 (not_lt.1 hn)
    linarith
  have habove : ∀ t, mb < m t := fun t => by
    induction t with
    | zero => exact h1
    | succ n ih => exact ih.trans (hinc n ih)
  exact strictMono_nat_of_lt_succ fun t => hinc t (habove t)

/-- AKMM, footnote 11, p. 513: along a decreasing path the gross real return on money
`p_{m,t+1}/p_{m,t} = m_{t+1}/(γm_t)` is below its stationary value `1/γ`, so the CIA binds. -/
theorem hyp_return_lt {γ mt mt1 : ℝ} (hγ : 0 < γ) (hmt : 0 < mt) (hlt : mt1 < mt) :
    mt1 / (γ * mt) < 1 / γ := by
  rw [div_lt_div_iff₀ (by positivity) hγ]; nlinarith

/-- AKMM, footnote 11, p. 513 (local stability at zero): if `u′ ≥ k > γ/β` on `(0, δ)`, every
path staying in `(0, δ)` satisfies `m_t ≤ (γ/(βk))ᵗ m₀` and converges to zero. -/
theorem hyp_local_stable {β γ k δ : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hk : γ / β < k) (hδ : ∀ m, 0 < m → m < δ → k ≤ du m) {m : ℕ → ℝ} (hm : hypIsPath β γ du m)
    (hin : ∀ t, m t < δ) : (∀ t, m t ≤ (γ / (β * k)) ^ t * m 0) ∧ Tendsto m atTop (𝓝 0) := by
  have hk0 : 0 < k := lt_trans (by positivity) hk
  have hstep : ∀ t, m (t + 1) ≤ γ / (β * k) * m t := fun t => by
    have hdu := hδ _ (hm (t + 1)).1 (hin (t + 1))
    have e := (hm t).2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hdu (mul_nonneg hβ.le (hm (t + 1)).1.le)
    nlinarith
  have hbound : ∀ t, m t ≤ (γ / (β * k)) ^ t * m 0 := fun t => by
    induction t with
    | zero => simp
    | succ n ih =>
      calc m (n + 1) ≤ γ / (β * k) * m n := hstep n
        _ ≤ γ / (β * k) * ((γ / (β * k)) ^ n * m 0) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (γ / (β * k)) ^ (n + 1) * m 0 := by ring
  refine ⟨hbound, ?_⟩
  have hr : γ / (β * k) < 1 := by
    rw [div_lt_one (by positivity)]
    rwa [div_lt_iff₀ hβ, mul_comm] at hk
  have hlim : Tendsto (fun t => (γ / (β * k)) ^ t * m 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr).mul_const (m 0)
  exact squeeze_zero (fun t => (hm t).1.le) hbound hlim

/-- AKMM, footnote 11, p. 513 (instability at zero): if `0 < u′ ≤ k < γ/β` on `(0, δ)`, a path
in `(0, δ)` moves away from zero, `m_{t+1} ≥ (γ/(βk))m_t > m_t`. -/
theorem hyp_local_unstable {β γ k δ : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (hk0 : 0 < k)
    (hk : k < γ / β) (hδ : ∀ m, 0 < m → m < δ → du m ≤ k) {m : ℕ → ℝ}
    (hm : hypIsPath β γ du m) (t : ℕ) (hin : m (t + 1) < δ) :
    γ / (β * k) * m t ≤ m (t + 1) ∧ m t < m (t + 1) := by
  have hdu := hδ _ (hm (t + 1)).1 hin
  have e := (hm t).2
  have h1 : γ / (β * k) * m t ≤ m (t + 1) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hdu (mul_nonneg hβ.le (hm (t + 1)).1.le)
    nlinarith
  refine ⟨h1, lt_of_lt_of_le ?_ h1⟩
  have : 1 < γ / (β * k) := by
    rw [one_lt_div (by positivity)]
    rwa [lt_div_iff₀ hβ, mul_comm] at hk
  nlinarith [(hm t).1]

/-- AKMM, footnote 12, p. 513: with `u = log` (`u′(m) = 1/m`), (17.38) reads `γm_t = β`: the
unique path is `m_t = β/γ`. -/
theorem hyp_log_unique {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (m : ℕ → ℝ) :
    hypIsPath β γ (fun x => x⁻¹) m ↔ ∀ t, m t = β / γ := by
  constructor
  · intro h t
    have e := (h t).2
    rw [mul_inv_cancel₀ (h (t + 1)).1.ne', mul_one] at e
    rw [eq_div_iff hγ.ne']; linarith
  · intro h t
    refine ⟨by rw [h]; positivity, ?_⟩
    rw [h, h, mul_inv_cancel₀ (by positivity), mul_one]; field_simp

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Interest-rate pegs and interest-rate rules

AKMM, §17.3.3, "Price level indeterminacy under pure interest rate rules" and "Interest rate rules
with a target", pp. 515–516, with footnotes 14–15.

**The CIA peg** (`u(c) + l`, `z = 1`). `pegIsEquilibrium` collects the conditions of p. 515.
* `peg_pins`: every equilibrium has `q_t = β`, `p_{m,t}/p_{m,t+1} = β(1 + i_t)` and
  `u′(c_{t+1}) = 1 + i_t`: the peg determines inflation and consumption from `t = 1` on.
* `peg_c0`: initial consumption is `c₀ = min(p_{m,0}M₀, c₀*)`, `u′(c₀*) = 1`.
* `peg_exists`: every `p_{m,0} > 0` indexes an equilibrium; `peg_real_indeterminacy`: distinct
  `p_{m,0} ≤ c₀*/M₀` give distinct `c₀` (real, not just nominal, indeterminacy).

**Rules `i_t = φ(P_t/P̃_t)`** (17.39) with a constant real rate.
* `eq_17_40`: `x_{t+1} = x_t(1 + φ(x_t))/(1 + ĩ)`, `x = P/P̃`, `ĩ = φ(1)`; `rule_target`.
* `rule_map_hasDerivAt`: the slope at `1` is `1 + φ′(1)/(1 + ĩ)`.
* `rule_determinate`: if the slope has modulus `> 1` the only solution staying near `1` is
  `x ≡ 1`; `rule_indeterminate`: if it has modulus `< 1`, every start near `1` gives a solution
  converging to `1`.
* `rule_phi_pos_determinate`: `φ′(1) > 0` gives determinacy (the book's claim);
  `rule_phi_neg_indeterminate`: `−2(1 + ĩ) < φ′(1) < 0` gives indeterminacy;
  `rule_phi_very_neg_determinate` and `rule_printed_counterexample`: for `φ′(1) < −2(1 + ĩ)` the
  solution is again unique, so the printed "if `φ′(1) < 0` there is indeterminacy" is false.
* `rule_knife_edge`: footnote 15 for an affine rule with `φ′(1) = 0`: every constant ratio solves
  (17.40).
-/

open Filter Topology

namespace AKMM.Money

/-! ### The cash-in-advance interest-rate peg -/

/-- AKMM, p. 515: the equilibrium conditions of the CIA model with `u(c) + l`, `z = 1` and a
peg `i_t`: `c_t ≤ p_{m,t}M_t`, `u′(c_t) = λ_t + µ_t`, `1 = λ_t`, `q_tλ_t = βλ_{t+1}`,
`λ_tp_{m,t}/p_{m,t+1} = β(λ_{t+1} + µ_{t+1})`, the Fisher equation
`q_t(1 + i_t) = p_{m,t}/p_{m,t+1}`, and `µ_t ≥ 0` with complementary slackness. -/
def pegIsEquilibrium (β : ℝ) (du : ℝ → ℝ) (i pm M c lam mu q : ℕ → ℝ) : Prop :=
  ∀ t, 0 < pm t ∧ 0 < c t ∧ c t ≤ pm t * M t ∧ du (c t) = lam t + mu t ∧ lam t = 1 ∧
    q t * lam t = β * lam (t + 1) ∧ lam t * (pm t / pm (t + 1)) = β * (lam (t + 1) + mu (t + 1)) ∧
    q t * (1 + i t) = pm t / pm (t + 1) ∧ 0 ≤ mu t ∧ mu t * (pm t * M t - c t) = 0

/-- **AKMM, p. 515: the peg determines inflation.** In every equilibrium `q_t = β`,
`p_{m,t}/p_{m,t+1} = β(1 + i_t)` and `u′(c_{t+1}) = 1 + i_t`. -/
theorem peg_pins {β : ℝ} {du : ℝ → ℝ} {i pm M c lam mu q : ℕ → ℝ}
    (h : pegIsEquilibrium β du i pm M c lam mu q) (t : ℕ) :
    q t = β ∧ pm t / pm (t + 1) = β * (1 + i t) ∧ du (c (t + 1)) = 1 + i t := by
  obtain ⟨hp, -, -, -, hl, h22, h23, hF, -, -⟩ := h t
  obtain ⟨hp1, -, -, h20', hl', -⟩ := h (t + 1)
  have hq : q t = β := by rw [hl, hl'] at h22; linarith
  have hR : pm t / pm (t + 1) = β * (1 + i t) := by rw [← hF, hq]
  refine ⟨hq, hR, ?_⟩
  have hb : β ≠ 0 := by
    rintro rfl; rw [zero_mul] at hR; exact (div_pos hp hp1).ne' hR
  rw [hl, hl', hR, one_mul] at h23
  rw [h20', hl']
  exact (mul_left_cancel₀ hb h23).symm

/-- AKMM, p. 515: initial consumption is `c₀ = min(p_{m,0}M₀, c₀*)` where `u′(c₀*) = 1`: if the
CIA does not bind, `µ₀ = 0` and `c₀ = c₀*`; otherwise `c₀ = p_{m,0}M₀ < c₀*`. -/
theorem peg_c0 {β cs : ℝ} {du : ℝ → ℝ} {i pm M c lam mu q : ℕ → ℝ}
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hcs : 0 < cs) (hdu : du cs = 1)
    (h : pegIsEquilibrium β du i pm M c lam mu q) : c 0 = min (pm 0 * M 0) cs := by
  obtain ⟨-, hc, hcia, h20, hl, -, -, -, hmu, hcs'⟩ := h 0
  rw [hl] at h20
  rcases hmu.lt_or_eq with hpos | hzero
  · have hb : c 0 = pm 0 * M 0 := by
      rcases mul_eq_zero.1 hcs' with h' | h'
      · exact absurd h' hpos.ne'
      · linarith
    have hlt : c 0 < cs := by
      by_contra hn
      rcases (not_lt.1 hn).lt_or_eq with h' | h'
      · have := hanti hcs hc h'; linarith
      · rw [← h', hdu] at h20; linarith
    rw [← hb, min_eq_left hlt.le]
  · rw [← hzero, add_zero] at h20
    have hc0 : c 0 = cs := hanti.injOn hc hcs (h20.trans hdu.symm)
    rw [hc0, min_eq_right (hc0 ▸ hcia)]

/-- **AKMM, p. 515: every initial price of money indexes an equilibrium.** Suppose `u′` is
strictly decreasing on `(0, ∞)`, `u′(c₀*) = 1`, and `cinv` inverts `u′` on `[1, ∞)` with
positive values. For a peg `i_t > 0`, an initial stock `M₀ > 0` and every `p₀ > 0` there is an
equilibrium with `p_{m,0} = p₀`, `M_0 = M₀` (the later money stock is endogenous). -/
theorem peg_exists {β cs M0 p0 : ℝ} {du cinv : ℝ → ℝ} {i : ℕ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hcs : 0 < cs) (hdu : du cs = 1)
    (hcinv : ∀ x, 1 ≤ x → 0 < cinv x ∧ du (cinv x) = x) (hi : ∀ t, 0 < i t) (hM0 : 0 < M0)
    (hp0 : 0 < p0) :
    ∃ pm M c lam mu q : ℕ → ℝ, pegIsEquilibrium β du i pm M c lam mu q ∧ pm 0 = p0 ∧
      M 0 = M0 := by
  let pm : ℕ → ℝ := fun t => p0 / ∏ s ∈ Finset.range t, (β * (1 + i s))
  have hprod : ∀ t, 0 < ∏ s ∈ Finset.range t, (β * (1 + i s)) := fun t =>
    Finset.prod_pos fun s _ => mul_pos hβ (by linarith [hi s])
  have hpm : ∀ t, 0 < pm t := fun t => div_pos hp0 (hprod t)
  have hratio : ∀ t, pm t / pm (t + 1) = β * (1 + i t) := fun t => by
    simp only [pm, Finset.prod_range_succ]
    have := (hprod t).ne'
    have : β * (1 + i t) ≠ 0 := (mul_pos hβ (by linarith [hi t])).ne'
    field_simp
  let c : ℕ → ℝ := fun t => if t = 0 then min (p0 * M0) cs else cinv (1 + i (t - 1))
  let M : ℕ → ℝ := fun t => if t = 0 then M0 else c t / pm t
  let mu : ℕ → ℝ := fun t => du (c t) - 1
  have hc0 : c 0 = min (p0 * M0) cs := rfl
  have hcs1 : ∀ t, c (t + 1) = cinv (1 + i t) := fun t => by simp [c]
  have hdu1 : ∀ t, du (c (t + 1)) = 1 + i t := fun t => by
    rw [hcs1]; exact (hcinv _ (by linarith [hi t])).2
  refine ⟨pm, M, c, fun _ => 1, mu, fun _ => β, fun t => ?_, by simp [pm], rfl⟩
  cases t with
  | zero =>
    have hpm0 : pm 0 = p0 := by simp [pm]
    have hM0' : M 0 = M0 := rfl
    have hc0pos : 0 < c 0 := lt_min (mul_pos hp0 hM0) hcs
    have hmu1 : mu 1 = i 0 := by simp only [mu]; rw [hdu1 0]; ring
    refine ⟨hpm 0, hc0pos, ?_, by simp [mu], rfl, by ring, ?_, ?_, ?_, ?_⟩
    · rw [hpm0, hM0', hc0]; exact min_le_left _ _
    · rw [hratio, hmu1]; ring
    · rw [hratio]
    · rcases le_or_gt cs (p0 * M0) with hle | hlt
      · simp only [mu]; rw [show c 0 = cs by rw [hc0, min_eq_right hle], hdu, sub_self]
      · have : c 0 = p0 * M0 := by rw [hc0, min_eq_left hlt.le]
        have h1 : 1 < du (c 0) := hdu ▸ hanti (by rw [this]; exact mul_pos hp0 hM0) hcs
          (by rw [this]; exact hlt)
        simp only [mu]; linarith
    · rcases le_or_gt cs (p0 * M0) with hle | hlt
      · simp only [mu]; rw [show c 0 = cs by rw [hc0, min_eq_right hle], hdu, sub_self, zero_mul]
      · have : c 0 = p0 * M0 := by rw [hc0, min_eq_left hlt.le]
        rw [hpm0, hM0', this]; ring
  | succ s =>
    have hcpos : 0 < c (s + 1) := by rw [hcs1]; exact (hcinv _ (by linarith [hi s])).1
    have hMs : M (s + 1) = c (s + 1) / pm (s + 1) := by simp [M]
    have hbind : pm (s + 1) * M (s + 1) = c (s + 1) := by
      rw [hMs]; field_simp [(hpm (s + 1)).ne']
    have hmu1 : mu (s + 1 + 1) = i (s + 1) := by simp only [mu]; rw [hdu1 (s + 1)]; ring
    refine ⟨hpm _, hcpos, hbind.ge, by simp [mu], rfl, by ring, ?_, ?_, ?_, ?_⟩
    · rw [hratio, hmu1]; ring
    · rw [hratio]
    · simp only [mu]; rw [hdu1 s]; linarith [hi s]
    · rw [hbind, sub_self, mul_zero]

/-- **AKMM, p. 515: real indeterminacy.** Two equilibria with initial prices
`p_{m,0} < p′_{m,0} ≤ c₀*/M₀` (same `M₀`) have different initial consumption. -/
theorem peg_real_indeterminacy {β cs : ℝ} {du : ℝ → ℝ}
    {i pm M c lam mu q pm' M' c' lam' mu' q' : ℕ → ℝ} (hanti : StrictAntiOn du (Set.Ioi 0))
    (hcs : 0 < cs) (hdu : du cs = 1) (h : pegIsEquilibrium β du i pm M c lam mu q)
    (h' : pegIsEquilibrium β du i pm' M' c' lam' mu' q') (hM : M 0 = M' 0) (hM0 : 0 < M 0)
    (hlt : pm 0 < pm' 0) (hle : pm' 0 * M' 0 ≤ cs) : c 0 < c' 0 := by
  rw [peg_c0 hanti hcs hdu h, peg_c0 hanti hcs hdu h', min_eq_left hle,
    min_eq_left (by rw [hM]; nlinarith [hM ▸ hM0])]
  rw [hM]; exact mul_lt_mul_of_pos_right hlt (hM ▸ hM0)

/-! ### Interest-rate rules with a target -/

/-- AKMM, (17.40), p. 516: the map `x ↦ x(1 + φ(x))/(1 + ĩ)` of the price level relative to
target. -/
noncomputable def ruleMap (φ : ℝ → ℝ) (it x : ℝ) : ℝ := x * (1 + φ x) / (1 + it)

/-- **AKMM, (17.40)**, p. 516: with the Fisher equation `1 + i_t = (1 + r)P_{t+1}/P_t`, the rule
`i_t = φ(P_t/P̃_t)` (17.39) and the target `P̃_{t+1} = (1 + π̃)P̃_t`, `1 + ĩ = (1 + r)(1 + π̃)`:
`P_{t+1}/P̃_{t+1} = ((1 + φ(P_t/P̃_t))/(1 + ĩ)) P_t/P̃_t`. -/
theorem eq_17_40 {φ : ℝ → ℝ} {r it pit Pt Pt1 Qt Qt1 i : ℝ} (hr : 1 + r ≠ 0)
    (hpit : 1 + pit ≠ 0) (hPt : Pt ≠ 0) (hQt : Qt ≠ 0) (hF : 1 + i = (1 + r) * (Pt1 / Pt))
    (hrule : i = φ (Pt / Qt)) (htarget : Qt1 = (1 + pit) * Qt)
    (hit : 1 + it = (1 + r) * (1 + pit)) : Pt1 / Qt1 = ruleMap φ it (Pt / Qt) := by
  unfold ruleMap
  rw [← hrule, hF, hit, htarget]
  field_simp

/-- AKMM, p. 515: if the policy attains its target at every date, the interest rate is
`ĩ = φ(1)` and the target inflation rate is `(1 + ĩ)/(1 + r)`. -/
theorem rule_target {φ : ℝ → ℝ} {r Pt Pt1 i : ℝ} (hr : 1 + r ≠ 0) (hPt : Pt ≠ 0)
    (hF : 1 + i = (1 + r) * (Pt1 / Pt)) (hrule : i = φ 1) :
    i = φ 1 ∧ Pt1 / Pt = (1 + φ 1) / (1 + r) := by
  refine ⟨hrule, ?_⟩
  rw [← hrule, hF]; field_simp

/-- AKMM, p. 516: `x = 1` is a fixed point of (17.40) and the slope there is
`1 + φ′(1)/(1 + ĩ)`. -/
theorem rule_map_hasDerivAt {φ : ℝ → ℝ} {it d : ℝ} (hit : 1 + it ≠ 0) (hφ1 : φ 1 = it)
    (hφ : HasDerivAt φ d 1) :
    ruleMap φ it 1 = 1 ∧ HasDerivAt (ruleMap φ it) (1 + d / (1 + it)) 1 := by
  refine ⟨by unfold ruleMap; rw [hφ1, one_mul, div_self hit], ?_⟩
  have h := ((hasDerivAt_id' 1).mul ((hasDerivAt_const 1 (1 : ℝ)).add hφ)).div_const (1 + it)
  unfold ruleMap
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, hφ1]
  field_simp
  ring

/-- The local bound behind the linearisation: if `F(1) = 1` and `F′(1) = s`, for every `ε > 0`
there is `δ > 0` with `|F(x) − 1 − s(x − 1)| ≤ ε|x − 1|` for `|x − 1| < δ`. -/
theorem rule_local_bound {F : ℝ → ℝ} {s : ℝ} (hF : HasDerivAt F s 1) (h1 : F 1 = 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ x, |x - 1| < δ → |F x - 1 - s * (x - 1)| ≤ ε * |x - 1| := by
  have h := (hasDerivAt_iff_isLittleO.1 hF).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := hball (by rwa [Real.dist_eq])
  simpa [h1, Real.norm_eq_abs, smul_eq_mul, mul_comm] using this

/-- **AKMM, p. 516 (determinacy).** If `F(1) = 1` and `|F′(1)| > 1`, there is `δ > 0` such that
the only solution of `x_{t+1} = F(x_t)` with `|x_t − 1| < δ` for all `t` is `x ≡ 1`. -/
theorem rule_determinate {F : ℝ → ℝ} {s : ℝ} (hF : HasDerivAt F s 1) (h1 : F 1 = 1)
    (hs : 1 < |s|) : ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = F (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  obtain ⟨δ, hδ, hb⟩ := rule_local_bound hF h1 (ε := (|s| - 1) / 2) (by linarith)
  set K := (|s| + 1) / 2 with hK
  have hK1 : 1 < K := by rw [hK]; linarith
  have hgrow : ∀ y, |y - 1| < δ → K * |y - 1| ≤ |F y - 1| := fun y hy => by
    have h := hb y hy
    have : |s * (y - 1)| ≤ |F y - 1| + |F y - 1 - s * (y - 1)| := by
      have h2 := abs_sub_abs_le_abs_sub (s * (y - 1)) (F y - 1)
      rw [abs_sub_comm (s * (y - 1)) (F y - 1)] at h2
      linarith
    rw [abs_mul] at this
    rw [hK]; nlinarith [abs_nonneg (y - 1)]
  refine ⟨δ, hδ, fun x hx hin t => ?_⟩
  have hpow : ∀ n, K ^ n * |x t - 1| ≤ |x (t + n) - 1| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hgrow _ (hin (t + n))
      rw [← hx] at this
      calc K ^ (n + 1) * |x t - 1| = K * (K ^ n * |x t - 1|) := by ring
        _ ≤ K * |x (t + n) - 1| := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ |x (t + (n + 1)) - 1| := by rw [← add_assoc]; exact this
  by_contra hne
  have hpos : 0 < |x t - 1| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (δ / |x t - 1|) hK1
  have := hpow n
  have := hin (t + n)
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- **AKMM, p. 516 (indeterminacy).** If `F(1) = 1` and `|F′(1)| < 1`, there is `δ > 0` such that
every start `|x₀ − 1| < δ` generates a solution staying within `δ` of `1` and converging to `1`:
a continuum of bounded solutions. -/
theorem rule_indeterminate {F : ℝ → ℝ} {s : ℝ} (hF : HasDerivAt F s 1) (h1 : F 1 = 1)
    (hs : |s| < 1) : ∃ δ > 0, ∀ x0, |x0 - 1| < δ →
      (∀ t, |F^[t] x0 - 1| < δ) ∧ Tendsto (fun t => F^[t] x0) atTop (𝓝 1) := by
  obtain ⟨δ, hδ, hb⟩ := rule_local_bound hF h1 (ε := (1 - |s|) / 2) (by linarith)
  set K := (1 + |s|) / 2 with hK
  have hK1 : K < 1 := by rw [hK]; linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hshrink : ∀ y, |y - 1| < δ → |F y - 1| ≤ K * |y - 1| := fun y hy => by
    have h := hb y hy
    have : |F y - 1| ≤ |s * (y - 1)| + |F y - 1 - s * (y - 1)| := by
      have := abs_add_le (s * (y - 1)) (F y - 1 - s * (y - 1))
      rwa [add_sub_cancel] at this
    rw [abs_mul] at this
    rw [hK]; nlinarith [abs_nonneg (y - 1)]
  refine ⟨δ, hδ, fun x0 hx0 => ?_⟩
  have hall : ∀ t, |F^[t] x0 - 1| ≤ K ^ t * |x0 - 1| := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      have hin : |F^[n] x0 - 1| < δ :=
        lt_of_le_of_lt (ih.trans (mul_le_of_le_one_left (abs_nonneg _)
          (pow_le_one₀ hK0 hK1.le))) hx0
      rw [Function.iterate_succ_apply']
      calc |F (F^[n] x0) - 1| ≤ K * |F^[n] x0 - 1| := hshrink _ hin
        _ ≤ K * (K ^ n * |x0 - 1|) := mul_le_mul_of_nonneg_left ih hK0
        _ = K ^ (n + 1) * |x0 - 1| := by ring
  refine ⟨fun t => lt_of_le_of_lt ((hall t).trans (mul_le_of_le_one_left (abs_nonneg _)
    (pow_le_one₀ hK0 hK1.le))) hx0, ?_⟩
  have hlim : Tendsto (fun t => K ^ t * |x0 - 1|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hK0 hK1).mul_const |x0 - 1|
  have : Tendsto (fun t => F^[t] x0 - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact hall t) hlim
  simpa using this.add_const 1

/-- **AKMM, p. 516**: if `φ′(1) > 0` the bounded solution near `1` is unique, `P_t = P̃_t`. -/
theorem rule_phi_pos_determinate {φ : ℝ → ℝ} {it d : ℝ} (hit : 0 < 1 + it) (hφ1 : φ 1 = it)
    (hφ : HasDerivAt φ d 1) (hd : 0 < d) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = ruleMap φ it (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  obtain ⟨h1, hD⟩ := rule_map_hasDerivAt hit.ne' hφ1 hφ
  refine rule_determinate hD h1 ?_
  have : 0 < d / (1 + it) := div_pos hd hit
  rw [abs_of_pos (by linarith)]; linarith

/-- AKMM, p. 516, corrected: if `−2(1 + ĩ) < φ′(1) < 0` there is a continuum of solutions near
`1`, all converging to `1`. -/
theorem rule_phi_neg_indeterminate {φ : ℝ → ℝ} {it d : ℝ} (hit : 0 < 1 + it) (hφ1 : φ 1 = it)
    (hφ : HasDerivAt φ d 1) (hd : d < 0) (hd2 : -2 * (1 + it) < d) :
    ∃ δ > 0, ∀ x0, |x0 - 1| < δ → (∀ t, |(ruleMap φ it)^[t] x0 - 1| < δ) ∧
      Tendsto (fun t => (ruleMap φ it)^[t] x0) atTop (𝓝 1) := by
  obtain ⟨h1, hD⟩ := rule_map_hasDerivAt hit.ne' hφ1 hφ
  refine rule_indeterminate hD h1 ?_
  have a1 : d / (1 + it) < 0 := div_neg_of_neg_of_pos hd hit
  have a2 : -2 < d / (1 + it) := by rw [lt_div_iff₀ hit]; linarith
  rw [abs_lt]; constructor <;> linarith

/-- AKMM, p. 516, corrected: if `φ′(1) < −2(1 + ĩ)` the deviation is again explosive
(oscillating), and the bounded solution near `1` is unique. -/
theorem rule_phi_very_neg_determinate {φ : ℝ → ℝ} {it d : ℝ} (hit : 0 < 1 + it)
    (hφ1 : φ 1 = it) (hφ : HasDerivAt φ d 1) (hd : d < -2 * (1 + it)) :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = ruleMap φ it (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  obtain ⟨h1, hD⟩ := rule_map_hasDerivAt hit.ne' hφ1 hφ
  refine rule_determinate hD h1 ?_
  have : d / (1 + it) < -2 := by rw [div_lt_iff₀ hit]; linarith
  rw [abs_of_neg (by linarith)]; linarith

/-- AKMM, p. 516: counterexample to the printed "if `φ′(1) < 0`, then there is indeterminacy".
The rule `φ(x) = −3(x − 1)` (`ĩ = 0`, `φ′(1) = −3 < 0`) has a unique solution near `1`. -/
theorem rule_printed_counterexample :
    ∃ δ > 0, ∀ x : ℕ → ℝ, (∀ t, x (t + 1) = ruleMap (fun y => -3 * (y - 1)) 0 (x t)) →
      (∀ t, |x t - 1| < δ) → ∀ t, x t = 1 := by
  have hφ : HasDerivAt (fun y : ℝ => -3 * (y - 1)) (-3) 1 := by
    simpa using ((hasDerivAt_id' (1 : ℝ)).sub_const 1).const_mul (-3 : ℝ)
  exact rule_phi_very_neg_determinate (by norm_num) (by norm_num) hφ (by norm_num)

/-- AKMM, footnote 15, p. 516: for an affine rule with `φ′(1) = 0` (`φ ≡ ĩ`), every constant
ratio `P_t/P̃_t = x̄` solves (17.40): a continuum of non-diverging solutions. -/
theorem rule_knife_edge {it xb : ℝ} (hit : 1 + it ≠ 0) :
    ruleMap (fun _ => it) it xb = xb := by
  unfold ruleMap; field_simp

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The cashless limit

AKMM, §17.3.3, "The cashless limit", pp. 517–519, with footnotes 17–18. Utility is
`u(c, m₁) = f(h(c, m₁))` with `f` increasing and strictly concave and the CES index
`h(c, m₁) = ((1 − ω)c^ρ + ωm₁^ρ)^{1/ρ}`, `ρ < 1`, `ρ ≠ 0` (Galí's `composite ω (1 − ρ)`).

* `clH`, `clh`, `clh1`, `clh2`, `clTheta`: the index, its partial derivatives and the money
  share `θ = ωm₁^ρ/H`; `cl_h_eq_composite` identifies `h` with Galí's composite;
  `cl_h_hasDerivAt_c`, `cl_h_hasDerivAt_m`: `h_c = h₁`, `h_m = h₂`.
* `eq_17_41`: `h₂/h₁ = i/(1 + i)` iff `M_{t+1}/P_t = c((1 − ω)/ω · i/(1 + i))^{1/(ρ−1)}`;
  `cl_demand_homogeneous`, `cl_demand_elasticity`, `cl_demand_strictAnti`: unit consumption
  elasticity, constant elasticity `1/(ρ − 1)` in `i/(1 + i)`, decreasing in the opportunity cost;
  `cl_demand_tendsto_zero`: real balances vanish as `ω → 0`.
* `cl_footnote_17`: `(i/(1 + i))m₁/c = (u₁₂m₁/u₁)/(u₂₁c/u₂)`.
* `cl_h1_hasDerivAt_c`, `cl_h1_hasDerivAt_m`: `h₁₁c/h₁ = (ρ − 1)θ`, `h₁₂m₁/h₁ = (1 − ρ)θ`;
  `cl_footnote_18_identities`: `u₁₁c/u₁ = (f″/f′)h₁c + h₁₁c/h₁` and
  `u₁₂m₁/u₁ = (f″/f′)h₂m₁ + h₁₂m₁/h₁` (the latter corrected: printed with `h_{2,2}` for `h₂m₁`).
* `cl_footnote_18_limits`: along the money-demand curve, as `ω → 0`, `θ → 0`, `h → c`, `h₁ → 1`,
  `h₂m₁ → 0`, hence `η_{u₁,c} → −f″(c)c/f′(c) > 0` and `η_{u₁,m₁} → 0`.
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, p. 518: the CES aggregator inside the index, `H = (1 − ω)c^ρ + ωm^ρ`. -/
noncomputable def clH (ω ρ c m : ℝ) : ℝ := (1 - ω) * c ^ ρ + ω * m ^ ρ

/-- AKMM, p. 518: the CES index `h = H^{1/ρ}`. -/
noncomputable def clh (ω ρ c m : ℝ) : ℝ := clH ω ρ c m ^ (1 / ρ)

/-- AKMM, p. 518: `h₁ = ∂h/∂c = (1 − ω)c^{ρ−1}H^{1/ρ−1}`. -/
noncomputable def clh1 (ω ρ c m : ℝ) : ℝ := (1 - ω) * c ^ (ρ - 1) * clH ω ρ c m ^ (1 / ρ - 1)

/-- AKMM, p. 518: `h₂ = ∂h/∂m₁ = ωm₁^{ρ−1}H^{1/ρ−1}`. -/
noncomputable def clh2 (ω ρ c m : ℝ) : ℝ := ω * m ^ (ρ - 1) * clH ω ρ c m ^ (1 / ρ - 1)

/-- The money share `θ = ωm₁^ρ/H`. -/
noncomputable def clTheta (ω ρ c m : ℝ) : ℝ := ω * m ^ ρ / clH ω ρ c m

/-- The aggregator is positive. -/
theorem clH_pos {ω ρ c m : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m) :
    0 < clH ω ρ c m := by
  unfold clH
  have := Real.rpow_pos_of_pos hc ρ
  have := Real.rpow_pos_of_pos hm ρ
  have : 0 < 1 - ω := by linarith
  positivity

/-- The book's index is Galí's composite `composite ω (1 − ρ)` (Galí 2015, p. 35). -/
theorem cl_h_eq_composite {ω ρ c m : ℝ} (hρ : ρ ≠ 0) :
    clh ω ρ c m = Gali.ClassicalMonetaryModel.MIUNonseparable.composite ω (1 - ρ) c m := by
  unfold clh clH Gali.ClassicalMonetaryModel.MIUNonseparable.composite
  have h1 : (1 - ρ) ≠ 1 := by intro h; exact hρ (by linarith)
  simp only [h1, ↓reduceIte, show (1 : ℝ) - (1 - ρ) = ρ by ring]

/-- AKMM, p. 518: `∂h/∂c = h₁`. -/
theorem cl_h_hasDerivAt_c {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun c' => clh ω ρ c' m) (clh1 ω ρ c m) c := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun c' => clH ω ρ c' m) ((1 - ω) * (ρ * c ^ (ρ - 1))) c := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul (1 - ω)).add_const _
  have := hd.rpow_const (p := 1 / ρ) (Or.inl hH.ne')
  unfold clh clh1
  refine this.congr_deriv ?_
  field_simp

/-- AKMM, p. 518: `∂h/∂m₁ = h₂`. -/
theorem cl_h_hasDerivAt_m {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun m' => clh ω ρ c m') (clh2 ω ρ c m) m := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun m' => clH ω ρ c m') (ω * (ρ * m ^ (ρ - 1))) m := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul ω).const_add _
  have := hd.rpow_const (p := 1 / ρ) (Or.inl hH.ne')
  unfold clh clh2
  refine this.congr_deriv ?_
  field_simp

/-- AKMM, (17.41), p. 518: money demand `m₁ = c((1 − ω)/ω · s)^{1/(ρ−1)}`, `s = i/(1 + i)`. -/
noncomputable def clDemand (ω ρ c s : ℝ) : ℝ := c * ((1 - ω) / ω * s) ^ (1 / (ρ - 1))

/-- **AKMM, (17.41)**, p. 518: `h_{m₁}/h_c = s` iff `m₁ = c((1 − ω)/ω · s)^{1/(ρ−1)}`. -/
theorem eq_17_41 {ω ρ c m s : ℝ} (hρ1 : ρ < 1) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) (hs : 0 < s) : clh2 ω ρ c m / clh1 ω ρ c m = s ↔ m = clDemand ω ρ c s := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have h1ω : 0 < 1 - ω := by linarith
  have hρ' : ρ - 1 ≠ 0 := by linarith
  have hratio : clh2 ω ρ c m / clh1 ω ρ c m = ω / (1 - ω) * (m / c) ^ (ρ - 1) := by
    unfold clh1 clh2
    rw [Real.div_rpow hm.le hc.le]
    have := (Real.rpow_pos_of_pos hH (1 / ρ - 1)).ne'
    have := (Real.rpow_pos_of_pos hc (ρ - 1)).ne'
    field_simp
  rw [hratio]
  have hB : 0 < (1 - ω) / ω * s := by positivity
  have hx : 0 < m / c := div_pos hm hc
  unfold clDemand
  constructor
  · intro h
    have h' : (m / c) ^ (ρ - 1) = (1 - ω) / ω * s := by
      field_simp at h ⊢; linarith
    have : m / c = ((1 - ω) / ω * s) ^ (1 / (ρ - 1)) := by
      rw [← h', one_div, Real.rpow_rpow_inv hx.le hρ']
    rw [← this]; field_simp
  · intro h
    have : m / c = ((1 - ω) / ω * s) ^ (1 / (ρ - 1)) := by rw [h]; field_simp
    rw [this, ← Real.rpow_mul hB.le, one_div, inv_mul_cancel₀ hρ', Real.rpow_one]
    field_simp

/-- AKMM, p. 518: money demand has unitary elasticity with respect to consumption. -/
theorem cl_demand_homogeneous (ω ρ c s k : ℝ) : clDemand ω ρ (k * c) s = k * clDemand ω ρ c s := by
  unfold clDemand; ring

/-- AKMM, p. 518: constant elasticity `1/(ρ − 1)` with respect to `i/(1 + i)`. -/
theorem cl_demand_elasticity {ω ρ c s k : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hs : 0 < s)
    (hk : 0 < k) : clDemand ω ρ c (k * s) = k ^ (1 / (ρ - 1)) * clDemand ω ρ c s := by
  unfold clDemand
  have h1ω : 0 < 1 - ω := by linarith
  have : 0 < (1 - ω) / ω * s := by positivity
  rw [show (1 - ω) / ω * (k * s) = k * ((1 - ω) / ω * s) by ring,
    Real.mul_rpow hk.le this.le]
  ring

/-- AKMM, p. 518: since `ρ < 1`, real balances are strictly decreasing in the opportunity cost. -/
theorem cl_demand_strictAnti {ω ρ c : ℝ} (hρ1 : ρ < 1) (hω0 : 0 < ω) (hω1 : ω < 1)
    (hc : 0 < c) : StrictAntiOn (clDemand ω ρ c) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  unfold clDemand
  apply mul_lt_mul_of_pos_left _ hc
  have h1ω : 0 < (1 - ω) / ω := div_pos (by linarith) hω0
  exact Real.rpow_lt_rpow_of_neg (by positivity) (mul_lt_mul_of_pos_left hab h1ω)
    (by rw [one_div_neg]; linarith)

/-- AKMM, p. 519: as `ω → 0` real balances vanish, `M_{t+1}/P_t → 0`, for fixed `c` and `i`. -/
theorem cl_demand_tendsto_zero {ρ c s : ℝ} (hρ1 : ρ < 1) (hs : 0 < s) :
    Tendsto (fun ω => clDemand ω ρ c s) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ω : ℝ => (1 - ω) / ω * s) (𝓝[>] 0) atTop := by
    have : Tendsto (fun ω : ℝ => (ω⁻¹ - 1) * s) (𝓝[>] 0) atTop :=
      (tendsto_atTop_add_const_right _ (-1) tendsto_inv_nhdsGT_zero).atTop_mul_const hs
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ω hω
    have : (0 : ℝ) < ω := hω
    field_simp
  have h2 : Tendsto (fun x : ℝ => x ^ (1 / (ρ - 1))) atTop (𝓝 0) := by
    have hρ' : 0 < 1 - ρ := by linarith
    have := tendsto_rpow_neg_atTop (y := 1 / (1 - ρ)) (by positivity)
    refine this.congr fun x => ?_
    congr 1
    have : (1 : ℝ) - ρ ≠ 0 := by linarith
    have : ρ - 1 ≠ 0 := by linarith
    field_simp
    ring
  have h3 := (h2.comp h1).const_mul c
  rw [mul_zero] at h3
  exact h3

/-- AKMM, footnote 17, p. 519: with `u₂/u₁ = i/(1 + i)` and symmetric cross partials,
`(i/(1 + i))m₁/c = (u₁₂m₁/u₁)/(u₂₁c/u₂)`. -/
theorem cl_footnote_17 {u1 u2 u12 c m s : ℝ} (hu1 : u1 ≠ 0) (hu2 : u2 ≠ 0) (hu12 : u12 ≠ 0)
    (hc : c ≠ 0) (hs : u2 / u1 = s) : s * m / c = (u12 * m / u1) / (u12 * c / u2) := by
  rw [← hs]; field_simp

/-- AKMM, footnote 18, p. 519: `h₁₁c/h₁ = (ρ − 1)θ`: the derivative of `h₁` in `c` is
`h₁(ρ − 1)θ/c`. -/
theorem cl_h1_hasDerivAt_c {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun c' => clh1 ω ρ c' m)
      (clh1 ω ρ c m * ((ρ - 1) * clTheta ω ρ c m / c)) c := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun c' => clH ω ρ c' m) ((1 - ω) * (ρ * c ^ (ρ - 1))) c := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hc.ne')).const_mul (1 - ω)).add_const _
  have h1 := (Real.hasDerivAt_rpow_const (p := ρ - 1) (Or.inl hc.ne')).const_mul (1 - ω)
  have h2 := hd.rpow_const (p := 1 / ρ - 1) (Or.inl hH.ne')
  have := h1.mul h2
  unfold clh1 clTheta
  refine this.congr_deriv ?_
  unfold clH at hH ⊢
  have hcρ := Real.rpow_pos_of_pos hc ρ
  simp only [Real.rpow_sub_one hc.ne', Real.rpow_sub_one hH.ne']
  field_simp
  ring

/-- AKMM, footnote 18, p. 519: `h₁₂m₁/h₁ = (1 − ρ)θ`: the derivative of `h₁` in `m₁` is
`h₁(1 − ρ)θ/m₁`. -/
theorem cl_h1_hasDerivAt_m {ω ρ c m : ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c)
    (hm : 0 < m) : HasDerivAt (fun m' => clh1 ω ρ c m')
      (clh1 ω ρ c m * ((1 - ρ) * clTheta ω ρ c m / m)) m := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hd : HasDerivAt (fun m' => clH ω ρ c m') (ω * (ρ * m ^ (ρ - 1))) m := by
    unfold clH
    exact ((Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul ω).const_add _
  have := (hd.rpow_const (p := 1 / ρ - 1) (Or.inl hH.ne')).const_mul ((1 - ω) * c ^ (ρ - 1))
  unfold clh1 clTheta
  refine this.congr_deriv ?_
  unfold clH at hH ⊢
  have hmρ := Real.rpow_pos_of_pos hm ρ
  simp only [Real.rpow_sub_one hm.ne', Real.rpow_sub_one hH.ne']
  field_simp

/-- AKMM, footnote 18, p. 519: with `u₁ = f′(h)h₁` and `f″` the derivative of `f′`,
`u₁₁c/u₁ = (f″/f′)h₁c + h₁₁c/h₁` and `u₁₂m₁/u₁ = (f″/f′)h₂m₁ + h₁₂m₁/h₁`. (The book prints
the second as `(f″/f′)h_{2,2} + h_{1,2}m₁/h₁`; the first term is `(f″/f′)h₂m₁`.) -/
theorem cl_footnote_18_identities {ω ρ c m : ℝ} {df d2f : ℝ → ℝ} (hρ : ρ ≠ 0) (hω0 : 0 < ω)
    (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m)
    (hdf : HasDerivAt df (d2f (clh ω ρ c m)) (clh ω ρ c m)) (hdf0 : df (clh ω ρ c m) ≠ 0) :
    (∃ u11, HasDerivAt (fun c' => df (clh ω ρ c' m) * clh1 ω ρ c' m) u11 c ∧
      u11 * c / (df (clh ω ρ c m) * clh1 ω ρ c m) =
        d2f (clh ω ρ c m) / df (clh ω ρ c m) * clh1 ω ρ c m * c + (ρ - 1) * clTheta ω ρ c m) ∧
    (∃ u12, HasDerivAt (fun m' => df (clh ω ρ c m') * clh1 ω ρ c m') u12 m ∧
      u12 * m / (df (clh ω ρ c m) * clh1 ω ρ c m) =
        d2f (clh ω ρ c m) / df (clh ω ρ c m) * (clh2 ω ρ c m * m) +
          (1 - ρ) * clTheta ω ρ c m) := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  have hh1 : 0 < clh1 ω ρ c m := by
    unfold clh1
    have := Real.rpow_pos_of_pos hc (ρ - 1)
    have := Real.rpow_pos_of_pos hH (1 / ρ - 1)
    have : 0 < 1 - ω := by linarith
    positivity
  constructor
  · refine ⟨_, (hdf.comp c (cl_h_hasDerivAt_c hρ hω0 hω1 hc hm)).mul
      (cl_h1_hasDerivAt_c hρ hω0 hω1 hc hm), ?_⟩
    simp only [Function.comp_apply]
    field_simp
  · refine ⟨_, (hdf.comp m (cl_h_hasDerivAt_m hρ hω0 hω1 hc hm)).mul
      (cl_h1_hasDerivAt_m hρ hω0 hω1 hc hm), ?_⟩
    simp only [Function.comp_apply]
    field_simp

/-- The identity `h₂m₁ = θh`. -/
theorem cl_h2_mul {ω ρ c m : ℝ} (hω0 : 0 < ω) (hω1 : ω < 1) (hc : 0 < c) (hm : 0 < m) :
    clh2 ω ρ c m * m = clTheta ω ρ c m * clh ω ρ c m := by
  have hH := clH_pos (ρ := ρ) hω0 hω1 hc hm
  unfold clh2 clTheta clh
  rw [Real.rpow_sub_one hm.ne', Real.rpow_sub_one hH.ne']
  field_simp

/-- Along the money-demand curve the scaled money weight `W(ω) = ω(m₁/c)^ρ` tends to zero as
`ω → 0`: `W = ω^{1/(1−ρ)}((1 − ω)s)^{ρ/(ρ−1)}`. -/
theorem cl_weight_tendsto {ρ c s : ℝ} (hρ1 : ρ < 1) (hc : 0 < c) (hs : 0 < s) :
    Tendsto (fun ω => ω * (clDemand ω ρ c s / c) ^ ρ) (𝓝[>] 0) (𝓝 0) := by
  have hρ' : ρ - 1 ≠ 0 := by linarith
  have hρ'' : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h1ρ : 0 < 1 / (1 - ρ) := by have : 0 < 1 - ρ := by linarith
                                   positivity
  set k := ρ / (ρ - 1) with hk
  have hform : ∀ ω, 0 < ω → ω < 1 →
      ω * (clDemand ω ρ c s / c) ^ ρ = ω ^ (1 / (1 - ρ)) * ((1 - ω) * s) ^ k := by
    intro ω hω0 hω1
    have hB : 0 < (1 - ω) * s := mul_pos (by linarith) hs
    unfold clDemand
    rw [mul_div_cancel_left₀ _ hc.ne', ← Real.rpow_mul (by positivity),
      show (1 - ω) / ω * s = (1 - ω) * s * ω⁻¹ by ring, Real.mul_rpow hB.le (by positivity),
      Real.inv_rpow hω0.le, show 1 / (ρ - 1) * ρ = k by rw [hk]; ring]
    have : ω ^ (1 / (1 - ρ)) = ω * (ω ^ k)⁻¹ := by
      rw [← Real.rpow_neg hω0.le, ← Real.rpow_one_add' hω0.le]
      · congr 1; rw [hk]; field_simp; ring
      · rw [hk]; have : 1 + -(ρ / (ρ - 1)) = 1 / (1 - ρ) := by field_simp; ring
        rw [this]; exact h1ρ.ne'
    rw [this]; ring
  have hlim : Tendsto (fun ω : ℝ => ω ^ (1 / (1 - ρ)) * ((1 - ω) * s) ^ k) (𝓝[>] 0)
      (𝓝 (0 ^ (1 / (1 - ρ)) * ((1 - 0) * s) ^ k)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    apply ContinuousAt.mul (Real.continuousAt_rpow_const 0 _ (Or.inr h1ρ.le))
    apply ContinuousAt.rpow_const _ (Or.inl (by simp only [sub_zero, one_mul, ne_eq]; exact hs.ne'))
    exact ((continuousAt_const.sub continuousAt_id).mul continuousAt_const)
  rw [Real.zero_rpow h1ρ.ne', zero_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ω hω
  exact (hform ω hω.1 hω.2).symm

/-- **AKMM, footnote 18, p. 519: the cashless limit.** Fix `c > 0` and the opportunity cost
`s = i/(1 + i) > 0`, and let real balances follow the money demand (17.41). As `ω → 0`:
the money share `θ → 0`, `h → c`, `h₁ → 1`, `h₂m₁ → 0`. If `f′`, `f″` are continuous at `c` and
`f′(c) ≠ 0`, then `η_{u₁,c} = −((f″/f′)h₁c + (ρ − 1)θ) → −f″(c)c/f′(c)` and
`η_{u₁,m₁} = −((f″/f′)h₂m₁ + (1 − ρ)θ) → 0`. -/
theorem cl_footnote_18_limits {ρ c s : ℝ} {df d2f : ℝ → ℝ} (hρ : ρ ≠ 0) (hρ1 : ρ < 1)
    (hc : 0 < c) (hs : 0 < s) (hdfc : ContinuousAt df c) (hd2fc : ContinuousAt d2f c)
    (hdf0 : df c ≠ 0) :
    let m := fun ω => clDemand ω ρ c s
    Tendsto (fun ω => clTheta ω ρ c (m ω)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ω => clh ω ρ c (m ω)) (𝓝[>] 0) (𝓝 c) ∧
      Tendsto (fun ω => clh1 ω ρ c (m ω)) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun ω => clh2 ω ρ c (m ω) * m ω) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ω => -(d2f (clh ω ρ c (m ω)) / df (clh ω ρ c (m ω)) * clh1 ω ρ c (m ω) * c +
        (ρ - 1) * clTheta ω ρ c (m ω))) (𝓝[>] 0) (𝓝 (-(d2f c * c / df c))) ∧
      Tendsto (fun ω => -(d2f (clh ω ρ c (m ω)) / df (clh ω ρ c (m ω)) *
        (clh2 ω ρ c (m ω) * m ω) + (1 - ρ) * clTheta ω ρ c (m ω))) (𝓝[>] 0) (𝓝 0) := by
  intro m
  have hW := cl_weight_tendsto hρ1 hc hs
  set W := fun ω => ω * (clDemand ω ρ c s / c) ^ ρ with hWdef
  have hmpos : ∀ ω, 0 < ω → ω < 1 → 0 < m ω := fun ω h0 h1 => by
    simp only [m, clDemand]
    have : 0 < (1 - ω) / ω * s := by have : 0 < 1 - ω := by linarith
                                     positivity
    positivity
  have hmρ : ∀ ω, 0 < ω → ω < 1 → m ω ^ ρ = c ^ ρ * (m ω / c) ^ ρ := fun ω h0 h1 => by
    rw [← Real.mul_rpow hc.le (div_pos (hmpos ω h0 h1) hc).le, mul_div_cancel₀ _ hc.ne']
  have ev : ∀ᶠ ω in 𝓝[>] (0 : ℝ), 0 < ω ∧ ω < 1 := Ioo_mem_nhdsGT one_pos
  have hcρ := Real.rpow_pos_of_pos hc ρ
  -- H = c^ρ((1 − ω) + W)
  have hHform : ∀ᶠ ω in 𝓝[>] (0 : ℝ), clH ω ρ c (m ω) = c ^ ρ * ((1 - ω) + W ω) := by
    filter_upwards [ev] with ω hω
    simp only [clH, hWdef]
    rw [hmρ ω hω.1 hω.2]; ring
  have hden : Tendsto (fun ω : ℝ => (1 - ω) + W ω) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun ω : ℝ => 1 - ω) (𝓝[>] 0) (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    simpa using this.add hW
  have hH : Tendsto (fun ω => clH ω ρ c (m ω)) (𝓝[>] 0) (𝓝 (c ^ ρ)) := by
    have := hden.const_mul (c ^ ρ)
    rw [mul_one] at this
    exact this.congr' (hHform.mono fun ω h => h.symm)
  have hθ : Tendsto (fun ω => clTheta ω ρ c (m ω)) (𝓝[>] 0) (𝓝 0) := by
    have hq := hW.div hden one_ne_zero
    rw [zero_div] at hq
    refine hq.congr' ?_
    filter_upwards [ev, hHform] with ω hω hHω
    simp only [clTheta, hHω, hWdef]
    rw [hmρ ω hω.1 hω.2]
    field_simp
    rfl
  have hh : Tendsto (fun ω => clh ω ρ c (m ω)) (𝓝[>] 0) (𝓝 c) := by
    have := ((Real.continuousAt_rpow_const (c ^ ρ) (1 / ρ) (Or.inl hcρ.ne')).tendsto).comp hH
    rwa [← Real.rpow_mul hc.le, mul_one_div_cancel hρ, Real.rpow_one] at this
  have hh1 : Tendsto (fun ω => clh1 ω ρ c (m ω)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun ω : ℝ => (1 - ω) * c ^ (ρ - 1)) (𝓝[>] 0) (𝓝 (c ^ (ρ - 1))) := by
      have := (((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_id (x := 𝓝 (0 : ℝ)))).mul (tendsto_const_nhds (x := c ^ (ρ - 1)))).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have h2 := ((Real.continuousAt_rpow_const (c ^ ρ) (1 / ρ - 1)
      (Or.inl hcρ.ne')).tendsto).comp hH
    have := h1.mul h2
    rw [← Real.rpow_mul hc.le, ← Real.rpow_add hc,
      show ρ - 1 + ρ * (1 / ρ - 1) = 0 by field_simp; ring, Real.rpow_zero] at this
    exact this
  have hh2 : Tendsto (fun ω => clh2 ω ρ c (m ω) * m ω) (𝓝[>] 0) (𝓝 0) := by
    have := hθ.mul hh
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [ev] with ω hω
    exact (cl_h2_mul hω.1 hω.2 hc (hmpos ω hω.1 hω.2)).symm
  have hdf : Tendsto (fun ω => df (clh ω ρ c (m ω))) (𝓝[>] 0) (𝓝 (df c)) := hdfc.tendsto.comp hh
  have hd2f : Tendsto (fun ω => d2f (clh ω ρ c (m ω))) (𝓝[>] 0) (𝓝 (d2f c)) :=
    hd2fc.tendsto.comp hh
  have hratio := hd2f.div hdf hdf0
  refine ⟨hθ, hh, hh1, hh2, ?_, ?_⟩
  · have := ((hratio.mul hh1).mul_const c).add (hθ.const_mul (ρ - 1))
    have := this.neg
    convert this using 2
    ring
  · have := (hratio.mul hh2).add (hθ.const_mul (1 - ρ))
    have := this.neg
    convert this using 2
    ring

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The consolidated government budget

AKMM, §17.3.3, "Monetary-fiscal interactions", pp. 519–522. Real spending `g_t`, taxes `τ_t`,
nominal debt `B_t` (interest `i_{t−1}`), money `M_t`, price level `P_t`, real rate `r_t`,
`q_t = 1/(1 + r_t)` and the Fisher equation `1 + i_t = (1 + r_t)P_{t+1}/P_t`.

* `gb_flow_real`: (17.42) in real liabilities `b̂_t = (1 + i_{t−1})B_t/P_t`:
  `g_t + b̂_t = τ_t + q_tb̂_{t+1} + s_t`, `s_t = (M_{t+1} − M_t)/P_t`.
* `gb_iterate`: `b̂₀ = ∑_{t<T} Q_t(τ_t − g_t + s_t) + Q_Tb̂_T`, `Q_t = ∏_{s<t} q_s`.
* `eq_17_43`: if `Q_Tb̂_T → 0` (from the household's transversality condition and market
  clearing) and the sums converge, `∑ Q_t(g_t − τ_t) + b̂₀ = ∑ Q_ts_t`.
* `gb_printed_discount`: with the printed `q_{0,t} = ∏_{s=0}^{t} q_s` (17.43) fails.
* `eq_17_44`: in total liabilities `d_t = ((1 + i_{t−1})B_t + M_t)/P_t`,
  `d_t = τ_t − g_t + (M_{t+1}/P_t)i_t/(1 + i_t) + d_{t+1}/(1 + r_t)`.
* `gb_zero_rate`, `gb_zero_rate_printed`: with `i = 0` the discount factor is `1/(1 + r_t)`, not
  the printed `1/r_t`.
* `gb_stationary`: the stationary budget `ḡ + (r̄/(1 + r̄))d̄ = τ̄ + c̄f(ī)ī/(1 + ī)`.
* `gb_omo_irrelevance`: at `i = 0` any `(M̂, B̂)` with `M̂_t + B̂_t = M_t + B_t` satisfies the
  budget whenever `(M, B)` does (Wallace's irrelevance of open-market operations).
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, (17.42), p. 519: with the Fisher equation, `B_{t+1}/P_t = q_tb̂_{t+1}`, so (17.42) is
`g_t + b̂_t = τ_t + q_tb̂_{t+1} + s_t`, `b̂_t = (1 + i_{t−1})B_t/P_t`. -/
theorem gb_flow_real {g τ Bt Bt1 Mt Mt1 Pt Pt1 im1 i r : ℝ} (hPt : Pt ≠ 0) (hPt1 : Pt1 ≠ 0)
    (hr : 1 + r ≠ 0) (hF : 1 + i = (1 + r) * (Pt1 / Pt)) :
    g + (1 + im1) * Bt / Pt = τ + Bt1 / Pt + (Mt1 - Mt) / Pt ↔
      g + (1 + im1) * Bt / Pt =
        τ + 1 / (1 + r) * ((1 + i) * Bt1 / Pt1) + (Mt1 - Mt) / Pt := by
  have : 1 / (1 + r) * ((1 + i) * Bt1 / Pt1) = Bt1 / Pt := by rw [hF]; field_simp
  rw [this]

/-- AKMM, p. 520: iterating the real flow budget `b̂_t = τ_t − g_t + s_t + q_tb̂_{t+1}`
`T` times: `b̂₀ = ∑_{t<T} Q_t(τ_t − g_t + s_t) + Q_Tb̂_T`, `Q_t = ∏_{s<t} q_s`. -/
theorem gb_iterate {q x bh : ℕ → ℝ} (h : ∀ t, bh t = x t + q t * bh (t + 1)) (T : ℕ) :
    bh 0 = ∑ t ∈ Finset.range T, (∏ s ∈ Finset.range t, q s) * x t +
      (∏ s ∈ Finset.range T, q s) * bh T := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, Finset.prod_range_succ, h n]
    ring

/-- **AKMM, (17.43)**, p. 520: if the real flow budget holds at every date, the discounted
terminal liabilities vanish, `Q_Tb̂_T → 0`, and the present values converge,
`∑ Q_t(g_t − τ_t) = D` and `∑ Q_ts_t = S`, then `D + b̂₀ = S`. -/
theorem eq_17_43 {q g τ s bh : ℕ → ℝ} {D S : ℝ}
    (h : ∀ t, bh t = (τ t - g t + s t) + q t * bh (t + 1))
    (htvc : Tendsto (fun T => (∏ s ∈ Finset.range T, q s) * bh T) atTop (𝓝 0))
    (hD : HasSum (fun t => (∏ s ∈ Finset.range t, q s) * (g t - τ t)) D)
    (hS : HasSum (fun t => (∏ s ∈ Finset.range t, q s) * s t) S) : D + bh 0 = S := by
  have hsum := hS.sub hD
  have hlim : Tendsto (fun T => ∑ t ∈ Finset.range T, (∏ s ∈ Finset.range t, q s) *
      (τ t - g t + s t)) atTop (𝓝 (S - D)) := by
    refine hsum.tendsto_sum_nat.congr fun T => ?_
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have h2 : Tendsto (fun T => ∑ t ∈ Finset.range T, (∏ s ∈ Finset.range t, q s) *
      (τ t - g t + s t) + (∏ s ∈ Finset.range T, q s) * bh T) atTop (𝓝 (S - D + 0)) :=
    hlim.add htvc
  have h3 : Tendsto (fun _ : ℕ => bh 0) atTop (𝓝 (S - D + 0)) :=
    h2.congr fun T => (gb_iterate h T).symm
  have := tendsto_nhds_unique tendsto_const_nhds h3
  linarith

/-- AKMM, p. 520: the printed discount factor `q_{0,t} = ∏_{s=0}^{t} q_s` is wrong. With
`q ≡ 1/2`, `b̂₀ = 1`, `s₀ = 1` and all other terms zero the flow budget holds at every date and
(17.43) holds with `∏_{s<t}`, but the printed weights give `∑ q_{0,t}s_t = 1/2 ≠ b̂₀`. -/
theorem gb_printed_discount :
    let q : ℕ → ℝ := fun _ => 1 / 2
    let s : ℕ → ℝ := fun t => if t = 0 then 1 else 0
    let bh : ℕ → ℝ := fun t => if t = 0 then 1 else 0
    (∀ t, bh t = (0 - 0 + s t) + q t * bh (t + 1)) ∧
      HasSum (fun t => (∏ u ∈ Finset.range t, q u) * s t) 1 ∧
      HasSum (fun t => (∏ u ∈ Finset.range (t + 1), q u) * s t) (1 / 2) := by
  intro q s bh
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [bh, s]
    · simp [bh, s, ht.ne']
  · have := hasSum_ite_eq (0 : ℕ) (1 : ℝ)
    refine this.congr_fun fun t => ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [s]
    · simp [s, ht.ne']
  · have := hasSum_ite_eq (0 : ℕ) (1 / 2 : ℝ)
    refine this.congr_fun fun t => ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [s, q]
    · simp [s, ht.ne']

/-- **AKMM, (17.44)**, p. 520: with `D_t = (1 + i_{t−1})B_t + M_t`, `d_t = D_t/P_t` and the Fisher
equation, the flow budget (17.42) is
`d_t = τ_t − g_t + (M_{t+1}/P_t)(i_t/(1 + i_t)) + d_{t+1}/(1 + r_t)`. -/
theorem eq_17_44 {g τ Bt Bt1 Mt Mt1 Pt Pt1 im1 i r : ℝ} (hPt : Pt ≠ 0) (hPt1 : Pt1 ≠ 0)
    (hr : 1 + r ≠ 0) (hi : 1 + i ≠ 0) (hF : 1 + i = (1 + r) * (Pt1 / Pt)) :
    g + (1 + im1) * Bt / Pt = τ + Bt1 / Pt + (Mt1 - Mt) / Pt ↔
      ((1 + im1) * Bt + Mt) / Pt = τ - g + Mt1 / Pt * (i / (1 + i)) +
        1 / (1 + r) * (((1 + i) * Bt1 + Mt1) / Pt1) := by
  have e : 1 / (1 + r) * (((1 + i) * Bt1 + Mt1) / Pt1) + Mt1 / Pt * (i / (1 + i)) =
      Bt1 / Pt + Mt1 / Pt := by
    have hP : Pt1 / Pt = (1 + i) / (1 + r) := by rw [hF]; field_simp
    have hP' : Pt1 = Pt * ((1 + i) / (1 + r)) := by
      rw [← hP]; field_simp
    rw [hP']
    field_simp
    ring
  constructor
  · intro h
    have : ((1 + im1) * Bt + Mt) / Pt = (1 + im1) * Bt / Pt + Mt / Pt := by ring
    rw [this]
    have h' : (1 + im1) * Bt / Pt = τ - g + Bt1 / Pt + (Mt1 - Mt) / Pt := by linarith
    rw [h']
    have : (Mt1 - Mt) / Pt = Mt1 / Pt - Mt / Pt := by ring
    linarith
  · intro h
    have : ((1 + im1) * Bt + Mt) / Pt = (1 + im1) * Bt / Pt + Mt / Pt := by ring
    rw [this] at h
    have : (Mt1 - Mt) / Pt = Mt1 / Pt - Mt / Pt := by ring
    linarith

/-- AKMM, p. 522: with `i_t = i_{t−1} = 0` (17.44) reads
`(M_t + B_t)/P_t = τ_t − g_t + (1/(1 + r_t))(M_{t+1} + B_{t+1})/P_{t+1}`. -/
theorem gb_zero_rate {g τ Bt Bt1 Mt Mt1 Pt Pt1 r : ℝ} (hPt : Pt ≠ 0) (hPt1 : Pt1 ≠ 0)
    (hr : 1 + r ≠ 0) (hF : 1 + 0 = (1 + r) * (Pt1 / Pt)) :
    g + (1 + 0) * Bt / Pt = τ + Bt1 / Pt + (Mt1 - Mt) / Pt ↔
      (Mt + Bt) / Pt = τ - g + 1 / (1 + r) * ((Mt1 + Bt1) / Pt1) := by
  rw [eq_17_44 hPt hPt1 hr (by norm_num) hF]
  simp only [zero_div, mul_zero, add_zero, one_mul]
  rw [add_comm Bt Mt, add_comm Bt1 Mt1]

/-- AKMM, p. 522: the printed discount factor `1/r_t` is wrong: for `r_t > 0` and nonzero
next-period liabilities `X = (M_{t+1} + B_{t+1})/P_{t+1}`, `X/(1 + r_t) ≠ X/r_t`, so the printed
equation contradicts (17.44). -/
theorem gb_zero_rate_printed {r X : ℝ} (hr : 0 < r) (hX : X ≠ 0) :
    1 / (1 + r) * X ≠ 1 / r * X := by
  intro h
  have := mul_right_cancel₀ hX h
  rw [div_eq_div_iff (by linarith) hr.ne'] at this
  linarith

/-- AKMM, p. 521: the stationary budget. With constant `τ̄, ḡ, ī, r̄`, real liabilities `d̄` and
money demand `M_{t+1}/P_t = c̄f(ī)`, (17.44) reads `ḡ + (r̄/(1 + r̄))d̄ = τ̄ + c̄f(ī)ī/(1 + ī)`. -/
theorem gb_stationary {gb τb db rb ib cf : ℝ} (hr : 1 + rb ≠ 0) :
    db = τb - gb + cf * (ib / (1 + ib)) + 1 / (1 + rb) * db ↔
      gb + rb / (1 + rb) * db = τb + cf * (ib / (1 + ib)) := by
  have : db - 1 / (1 + rb) * db = rb / (1 + rb) * db := by field_simp; ring
  constructor <;> intro h <;> linarith

/-- AKMM, p. 522 (the irrelevance of open-market operations, Wallace 1981): at `i = 0` the
budget depends on money and bonds only through `M_t + B_t`; any sequences `(M̂, B̂)` with
`M̂_t + B̂_t = M_t + B_t` satisfy it iff `(M, B)` do. -/
theorem gb_omo_irrelevance {M B M' B' τ g r P : ℕ → ℝ} (hsum : ∀ t, M' t + B' t = M t + B t) :
    (∀ t, (M t + B t) / P t = τ t - g t + 1 / (1 + r t) * ((M (t + 1) + B (t + 1)) / P (t + 1)))
      ↔ ∀ t, (M' t + B' t) / P t =
        τ t - g t + 1 / (1 + r t) * ((M' (t + 1) + B' (t + 1)) / P (t + 1)) := by
  simp only [hsum]

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Seigniorage, unpleasant arithmetic, fiscal backstops and the fiscal theory of the price level

AKMM, §17.3.3, pp. 520–523.

* **The seigniorage Laffer curve** (p. 521). `lf_interior_max`: if the money demand `f` is
  continuous and positive and `f(i)i → 0` as `i → ∞`, arbitrage seigniorage `f(i)i/(1 + i)` has
  a maximum at some `i* > 0`. `lf_counterexample`: "`f` strictly decreasing" alone is not enough
  (`f(i) = 1 + 1/(1 + i)` gives strictly increasing revenue with no maximum);
  `lf_tc_no_max`: neither does the chapter's own transactions-cost demand (17.29).
* **Unpleasant arithmetic** (p. 521). `ua_stationary`: on the benign side of the Laffer curve a
  higher `d̄` requires a higher `ī` and higher inflation. `ua_dynamic`: with fixed surpluses,
  lower seigniorage now means higher seigniorage later (Cochrane's `unpleasant_tradeoff`).
* **A fiscal backstop** (p. 522). `fb_backstop`: every path along which real balances vanish
  eventually breaches the ceiling `P̃₀γᵗ`; `fb_stationary`: the stationary path never does.
* **The fiscal theory** (pp. 523). `eq_17_45`, `eq_17_46`, `ftpl_price_level`: under the tax rule
  (17.45) the present-value budget pins `(1 + i_{−1})B₀/P₀ = (τ̃ − g̃)/(1 − β)`;
  `ftpl_unique` (Cochrane's `lastDay_existsUnique`): with `B₀ > 0` and `τ̃ > g̃`, `P₀` exists and
  is unique; `ftpl_none` (Cochrane's `lastDay_none`): with `τ̃ ≤ g̃` there is no positive `P₀`.

**Departures.** The Laffer maximum needs a hypothesis such as `f(i)i → 0`; the FTPL needs
`τ̃ > g̃` besides `B₀ > 0`.
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, p. 521: the increasing part `i/(1 + i)` of seigniorage starts at `0`, is strictly
increasing and bounded above by `1`. -/
theorem lf_increasing_part :
    (0 : ℝ) / (1 + 0) = 0 ∧ StrictMonoOn (fun i : ℝ => i / (1 + i)) (Set.Ici 0) ∧
      ∀ i : ℝ, 0 ≤ i → i / (1 + i) < 1 := by
  refine ⟨by norm_num, fun a ha b hb hab => ?_, fun i hi => by
    rw [div_lt_one (by linarith)]; linarith⟩
  have ha' : (0 : ℝ) ≤ a := ha
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- **AKMM, p. 521: the seigniorage Laffer curve.** If `f` is continuous on `[0, ∞)`, positive on
`(0, ∞)` and `f(i)i → 0` as `i → ∞`, then seigniorage `f(i)i/(1 + i)` attains its maximum over
`i ≥ 0` at some `i* > 0`. -/
theorem lf_interior_max {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0))
    (hpos : ∀ i, 0 < i → 0 < f i) (hlim : Tendsto (fun i => f i * i) atTop (𝓝 0)) :
    ∃ i0, 0 < i0 ∧ IsMaxOn (fun i => f i * (i / (1 + i))) (Set.Ici 0) i0 := by
  set S := fun i : ℝ => f i * (i / (1 + i)) with hSdef
  have hv : 0 < S 1 := by simp only [hSdef]; have := hpos 1 one_pos; positivity
  have hSle : ∀ i, 0 < i → S i ≤ f i * i := fun i hi => by
    simp only [hSdef]
    apply mul_le_mul_of_nonneg_left _ (hpos i hi).le
    rw [div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨R, hR⟩ := (eventually_atTop.1 (hlim (gt_mem_nhds hv)))
  set R' := max R 1
  have hScont : ContinuousOn S (Set.Icc 0 R') := by
    apply (hcont.mono Set.Icc_subset_Ici_self).mul
    exact (continuousOn_id.div (continuousOn_const.add continuousOn_id) fun x hx => by
      have : (0 : ℝ) ≤ x := hx.1; positivity)
  obtain ⟨i0, hi0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (le_trans zero_le_one (le_max_right R 1))) hScont
  have h1 : S 1 ≤ S i0 := hmax ⟨zero_le_one, le_max_right R 1⟩
  have hi0pos : 0 < i0 := by
    rcases hi0.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at h1; simp [hSdef] at h1; nlinarith [hpos 1 one_pos]
  refine ⟨i0, hi0pos, fun i hi => ?_⟩
  have hi' : (0 : ℝ) ≤ i := hi
  by_cases hiR : i ≤ R'
  · exact hmax ⟨hi', hiR⟩
  · have hiR' : R ≤ i := le_trans (le_max_left R 1) (le_of_not_ge hiR)
    have hipos : 0 < i := lt_of_lt_of_le one_pos (le_trans (le_max_right R 1) (le_of_not_ge hiR))
    have := hR i hiR'
    exact le_trans (hSle i hipos) (le_trans this.le h1)

/-- AKMM, p. 521: "`f` strictly decreasing" is not enough. With `f(i) = 1 + 1/(1 + i)`
(positive, strictly decreasing) seigniorage equals `1 − 1/(1 + i)²`, which is strictly
increasing on `[0, ∞)`: there is no maximum. -/
theorem lf_counterexample :
    StrictAntiOn (fun i : ℝ => 1 + 1 / (1 + i)) (Set.Ici 0) ∧
      (∀ i : ℝ, 0 ≤ i → 0 < 1 + 1 / (1 + i)) ∧
      StrictMonoOn (fun i : ℝ => (1 + 1 / (1 + i)) * (i / (1 + i))) (Set.Ici 0) ∧
      ¬ ∃ i0 : ℝ, 0 ≤ i0 ∧
        IsMaxOn (fun i : ℝ => (1 + 1 / (1 + i)) * (i / (1 + i))) (Set.Ici 0) i0 := by
  have hform : ∀ i : ℝ, 0 ≤ i → (1 + 1 / (1 + i)) * (i / (1 + i)) = 1 - 1 / (1 + i) ^ 2 :=
    fun i hi => by have : (1 + i) ≠ 0 := by linarith
                   field_simp; ring
  have hmono : StrictMonoOn (fun i : ℝ => (1 + 1 / (1 + i)) * (i / (1 + i))) (Set.Ici 0) := by
    intro a ha b hb hab
    have ha' : (0 : ℝ) ≤ a := ha
    have hb' : (0 : ℝ) ≤ b := hb
    simp only
    rw [hform a ha', hform b hb']
    have : 1 / (1 + b) ^ 2 < 1 / (1 + a) ^ 2 := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    linarith
  refine ⟨fun a ha b hb hab => ?_, fun i hi => by positivity, hmono, ?_⟩
  · have ha' : (0 : ℝ) ≤ a := ha
    simp only
    have : 1 / (1 + b) < 1 / (1 + a) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
    linarith
  · rintro ⟨i0, h, hi0⟩
    have hle := isMaxOn_iff.1 hi0
    have h1 := hle (i0 + 1) (show i0 + 1 ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith)
    have h2 := hmono (show i0 ∈ Set.Ici (0 : ℝ) from h)
      (show i0 + 1 ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) (by linarith)
    linarith

/-- AKMM, p. 521, with (17.29): for the chapter's transactions-cost demand
`m/c = ((1/(κη))s)^{−1/(1+η)}`, `s = i/(1 + i)`, seigniorage per unit of consumption
`(m/c)s` is strictly increasing in `s ∈ (0, 1)`: it has no interior Laffer maximum. -/
theorem lf_tc_no_max {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    StrictMonoOn (fun s => tcDemand κ η 1 s * s) (Set.Ioi 0) := by
  have hform : ∀ s : ℝ, 0 < s →
      tcDemand κ η 1 s * s = (1 / (κ * η)) ^ (-(1 / (1 + η))) * s ^ (η / (1 + η)) := by
    intro s hs
    unfold tcDemand
    rw [one_mul, Real.mul_rpow (by positivity) hs.le, mul_assoc]
    congr 1
    rw [show η / (1 + η) = -(1 / (1 + η)) + 1 by field_simp; ring,
      Real.rpow_add hs, Real.rpow_one]
  intro a ha b hb hab
  dsimp only
  rw [hform a ha, hform b hb]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  exact Real.rpow_lt_rpow (le_of_lt ha) hab (by positivity)

/-- **AKMM, p. 521: unpleasant arithmetic (stationary version).** Fix `ḡ, τ̄, r̄ > 0, c̄ > 0`. If
seigniorage `S` is strictly increasing on a set `I` (the benign side of the Laffer curve) and
`(d̄₁, ī₁)`, `(d̄₂, ī₂)` both satisfy the stationary budget with `ī₁, ī₂ ∈ I`, then `d̄₁ < d̄₂`
forces `ī₁ < ī₂` and, by the Fisher equation, higher inflation. -/
theorem ua_stationary {S : ℝ → ℝ} {I : Set ℝ} (hS : StrictMonoOn S I)
    {gb τb rb cb d1 d2 i1 i2 : ℝ} (hr : 0 < rb) (hc : 0 < cb) (hi1 : i1 ∈ I) (hi2 : i2 ∈ I)
    (h1 : gb + rb / (1 + rb) * d1 = τb + cb * S i1)
    (h2 : gb + rb / (1 + rb) * d2 = τb + cb * S i2) (hd : d1 < d2) :
    i1 < i2 ∧ (1 + i1) / (1 + rb) < (1 + i2) / (1 + rb) := by
  have hk : 0 < rb / (1 + rb) := by positivity
  have : cb * S i1 < cb * S i2 := by nlinarith
  have hS12 : S i1 < S i2 := lt_of_mul_lt_mul_left this hc.le
  have hi : i1 < i2 := (hS.lt_iff_lt hi1 hi2).1 hS12
  exact ⟨hi, div_lt_div_of_pos_right (by linarith) (by linarith)⟩

/-- AKMM, p. 521 (Sargent–Wallace, dynamic version, via Cochrane's `unpleasant_tradeoff`): with
`q ≡ β`, (17.43) reads `∑ βᵗ(s_t + σ_t) = b̂₀` (primary surpluses `s`, seigniorage `σ`). If the
surpluses are fixed with present value `S` and the date-0 seigniorage is cut, `σ′₀ < σ₀`, then
seigniorage must be higher at some later date. -/
theorem ua_dynamic {β b0 S : ℝ} (hβ : 0 < β) {s σ σ' : ℕ → ℝ}
    (hs : HasSum (fun j => β ^ j * s j) S) (hb : HasSum (fun j => β ^ j * (s j + σ j)) b0)
    (hb' : HasSum (fun j => β ^ j * (s j + σ' j)) b0) (h0 : σ' 0 < σ 0) :
    ∃ j, 0 < j ∧ σ j < σ' j :=
  Cochrane.Monetarism.UnpleasantArithmetic.unpleasant_tradeoff hβ hs hb hb' h0

/-- AKMM, p. 522: a fiscal backstop. With money growth `M_t = M₀γᵗ` and real balances `m_t → 0`
(the hyperinflation paths), the price level `P_t = M_t/m_t` eventually exceeds any ceiling
`P̃₀γᵗ`: the promise to buy money at that ceiling rules these paths out. -/
theorem fb_backstop {M0 γ Pt0 : ℝ} {m : ℕ → ℝ} (hM0 : 0 < M0) (hγ : 0 < γ) (hP : 0 < Pt0)
    (hm : ∀ t, 0 < m t) (hlim : Tendsto m atTop (𝓝 0)) :
    ∃ t, Pt0 * γ ^ t < M0 * γ ^ t / m t := by
  obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds (div_pos hM0 hP))).exists
  refine ⟨t, ?_⟩
  rw [lt_div_iff₀ (hm t)]
  have hg : 0 < γ ^ t := pow_pos hγ t
  rw [lt_div_iff₀ hP] at ht
  nlinarith

/-- AKMM, p. 522: the stationary path `m_t = m̄` respects every ceiling `P̃₀ ≥ M₀/m̄`: the
critical value grows at the money growth rate, as the stationary price level does. -/
theorem fb_stationary {M0 γ Pt0 mb : ℝ} (hγ : 0 < γ) (hP : M0 / mb ≤ Pt0)
    (t : ℕ) : M0 * γ ^ t / mb ≤ Pt0 * γ ^ t := by
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right hP (pow_pos hγ t).le

/-- **AKMM, (17.45)**, p. 523: under the tax rule `τ_t − τ̃ = −(M_{t+1} − M_t)/P_t` and
`g_t = g̃` the primary surplus plus seigniorage is constant, `τ̃ − g̃`. -/
theorem eq_17_45 {τt τtil gt gtil st : ℝ} (hrule : τt - τtil = -st) (hg : gt = gtil) :
    τt - gt + st = τtil - gtil := by
  rw [hg]; linarith

/-- **AKMM, (17.46)**, p. 523: with `q_{0,t} = βᵗ`, `0 ≤ β < 1`, the present value of the
constant `τ̃ − g̃` is `(τ̃ − g̃)/(1 − β)`. -/
theorem eq_17_46 {β τtil gtil : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => β ^ t * (τtil - gtil)) ((τtil - gtil) / (1 - β)) := by
  have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (τtil - gtil)
  simpa [div_eq_inv_mul, mul_comm] using this

/-- AKMM, (17.43) with (17.45)–(17.46), p. 523: if the real flow budget holds at every date with
`q_t = β` (the CIA peg), the discounted terminal liabilities vanish and taxes follow (17.45),
then the initial real liabilities equal the present value of surpluses:
`(1 + i_{−1})B₀/P₀ = (τ̃ − g̃)/(1 − β)`. -/
theorem ftpl_price_level {β τtil gtil : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {g τ s bh : ℕ → ℝ}
    (h : ∀ t, bh t = (τ t - g t + s t) + β * bh (t + 1))
    (htvc : Tendsto (fun T => β ^ T * bh T) atTop (𝓝 0))
    (hrule : ∀ t, τ t - τtil = -s t) (hg : ∀ t, g t = gtil) :
    bh 0 = (τtil - gtil) / (1 - β) := by
  have hcomb : ∀ t, τ t - g t + s t = τtil - gtil := fun t => eq_17_45 (hrule t) (hg t)
  have hx : ∀ t, bh t = (τtil - gtil) + β * bh (t + 1) := fun t => by rw [h t, hcomb t]
  have hit := fun T => gb_iterate (q := fun _ => β) (x := fun _ => τtil - gtil) hx T
  simp only [Finset.prod_const, Finset.card_range] at hit
  have h2 := (eq_17_46 hβ0 hβ1 (τtil := τtil) (gtil := gtil)).tendsto_sum_nat.add htvc
  rw [add_zero] at h2
  have h3 : Tendsto (fun _ : ℕ => bh 0) atTop (𝓝 ((τtil - gtil) / (1 - β))) :=
    h2.congr fun T => (hit T).symm
  exact tendsto_nhds_unique tendsto_const_nhds h3

/-- AKMM, p. 523 (via Cochrane's `lastDay_existsUnique`): with `B₀ > 0`, `1 + i_{−1} > 0`,
`0 < β < 1` and `τ̃ > g̃`, there is exactly one positive `P₀` with
`(1 + i_{−1})B₀/P₀ = (τ̃ − g̃)/(1 − β)`. -/
theorem ftpl_unique {β τtil gtil B0 im1 : ℝ} (hβ1 : β < 1) (hB : 0 < B0) (hi : 0 < 1 + im1)
    (hτ : gtil < τtil) :
    ∃! P0 : ℝ, 0 < P0 ∧ (1 + im1) * B0 / P0 = (τtil - gtil) / (1 - β) :=
  Cochrane.TwoPeriodModel.TwoPeriod.lastDay_existsUnique (mul_pos hi hB)
    (div_pos (by linarith) (by linarith))

/-- AKMM, p. 523 (added hypothesis, via Cochrane's `lastDay_none`): with `B₀ > 0` but
`τ̃ ≤ g̃` no positive price level satisfies (17.46). -/
theorem ftpl_none {β τtil gtil B0 im1 : ℝ} (hβ1 : β < 1) (hB : 0 < B0) (hi : 0 < 1 + im1)
    (hτ : τtil ≤ gtil) :
    ¬ ∃ P0 : ℝ, 0 < P0 ∧ (1 + im1) * B0 / P0 = (τtil - gtil) / (1 - β) :=
  Cochrane.TwoPeriodModel.TwoPeriod.lastDay_none (mul_pos hi hB)
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Two fiat currencies: Kareken–Wallace exchange-rate indeterminacy

AKMM, §17.4.1, pp. 524–526. In the endowment OLG economy of §17.2 the young can save in two
currencies `a, b` with prices `p_{a,t}, p_{b,t}` (no short sales), stocks `M_a, M_b > 0`.

* `kwOptimal`, `kwIsEquilibrium`: the young's problem and equilibrium.
* `kw_dominated`: a currency with a strictly lower return is not held.
* `kw_equal_returns_util`, `kw_optimal_iff`: with equal returns only total real saving matters
  and the problem is the one-currency problem (17.3).
* `kw_structure`: in every equilibrium each currency is valued at all dates or at none, and if
  both are valued their returns are equal at all dates; `kw_e_constant`: then the exchange rate
  `e_t = p_{a,t}/p_{b,t}` is constant.
* `kw_indeterminate`: every `e > 0` (and every one-currency equilibrium path for total real
  balances) gives an equilibrium: the exchange rate is not determined; `kw_unvalued`: so is the
  equilibrium in which one currency is never valued.
* Growing stocks: `kw_gresham` (`eM_{a,t}/M_t → 1` and `γ_t → γ_a` for `γ_a > γ_b`, Gresham's
  law), `kw_limit_formula` (the steady state of the modified demand is
  `p_bM = (ω_y − γω_o)/(1 + γ)`), `kw_limit_lower` (it is lower for faster money growth, so the
  `e = 0` equilibrium has the higher limit), `kw_limit_eq_mg` (it is the money-growth stationary
  value of §17.2.3).

**Not formalised.** That an equilibrium path with growing stocks exists and converges to the
limit; the book defers the proof to the appendix of Kareken and Wallace (1981).
-/

open Filter Topology

namespace AKMM.Money

/-- AKMM, p. 524: utility of a young agent holding `(M_a′, M_b′)`. -/
noncomputable def kwUtil (ωy ωo pa pb pa1 pb1 Ma Mb : ℝ) : ℝ :=
  Real.log (ωy - pa * Ma - pb * Mb) + Real.log (ωo + pa1 * Ma + pb1 * Mb)

/-- AKMM, p. 524: feasible holdings, `M_a′, M_b′ ≥ 0` and `c_y > 0`. -/
def kwFeasible (ωy pa pb Ma Mb : ℝ) : Prop := 0 ≤ Ma ∧ 0 ≤ Mb ∧ pa * Ma + pb * Mb < ωy

/-- AKMM, p. 524: optimal holdings. -/
def kwOptimal (ωy ωo pa pb pa1 pb1 Ma Mb : ℝ) : Prop :=
  kwFeasible ωy pa pb Ma Mb ∧ ∀ Ma' Mb', kwFeasible ωy pa pb Ma' Mb' →
    kwUtil ωy ωo pa pb pa1 pb1 Ma' Mb' ≤ kwUtil ωy ωo pa pb pa1 pb1 Ma Mb

/-- AKMM, p. 525: an equilibrium with constant stocks `M_a, M_b`: prices are nonnegative and the
young hold both stocks at every date. -/
def kwIsEquilibrium (ωy ωo Ma Mb : ℝ) (pa pb : ℕ → ℝ) : Prop :=
  (∀ t, 0 ≤ pa t ∧ 0 ≤ pb t) ∧ ∀ t, kwOptimal ωy ωo (pa t) (pb t) (pa (t + 1)) (pb (t + 1)) Ma Mb

/-- AKMM, p. 524: if currency `a` has a strictly lower return than `b`
(`p_{a,t+1}/p_{a,t} < p_{b,t+1}/p_{b,t}`), holding `M_a′ > 0` is not optimal. -/
theorem kw_dominated {ωy ωo pa pb pa1 pb1 Ma Mb : ℝ} (hωo : 0 < ωo) (hpa : 0 < pa) (hpb : 0 < pb)
    (hpa1 : 0 ≤ pa1) (hpb1 : 0 ≤ pb1) (hret : pa1 / pa < pb1 / pb) (hMa : 0 < Ma) :
    ¬ kwOptimal ωy ωo pa pb pa1 pb1 Ma Mb := by
  rintro ⟨⟨-, hMb, hc⟩, h⟩
  have hfeas : kwFeasible ωy pa pb 0 (Mb + pa * Ma / pb) := by
    refine ⟨le_rfl, by positivity, ?_⟩
    have : pa * 0 + pb * (Mb + pa * Ma / pb) = pa * Ma + pb * Mb := by field_simp; ring
    rw [this]; exact hc
  have := h _ _ hfeas
  unfold kwUtil at this
  have e1 : ωy - pa * 0 - pb * (Mb + pa * Ma / pb) = ωy - pa * Ma - pb * Mb := by
    field_simp; ring
  have hgain : pa1 * Ma < pb1 * (pa * Ma / pb) := by
    rw [div_lt_div_iff₀ hpa hpb] at hret
    rw [mul_div_assoc', lt_div_iff₀ hpb]
    nlinarith
  have hlt : Real.log (ωo + pa1 * Ma + pb1 * Mb) <
      Real.log (ωo + pa1 * 0 + pb1 * (Mb + pa * Ma / pb)) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  rw [e1] at this
  linarith

/-- AKMM, p. 525: with equal returns `R` only total real saving `s = p_aM_a′ + p_bM_b′` matters:
the two-currency utility is the one-currency utility `log(ω_y − s) + log(ω_o + Rs)`. -/
theorem kw_equal_returns_util {ωy ωo pa pb pa1 pb1 R : ℝ} (hpa : pa ≠ 0) (hpb : pb ≠ 0)
    (ha : pa1 / pa = R) (hb : pb1 / pb = R) (Ma Mb : ℝ) :
    kwUtil ωy ωo pa pb pa1 pb1 Ma Mb = olgUtil ωy ωo R (pa * Ma + pb * Mb) := by
  unfold kwUtil olgUtil
  have h1 : pa1 = R * pa := by rw [← ha]; field_simp
  have h2 : pb1 = R * pb := by rw [← hb]; field_simp
  rw [h1, h2]
  ring_nf

/-- AKMM, p. 525: with equal returns `R` and positive prices, `(M_a′, M_b′) ≥ 0` is optimal iff
total real saving equals the one-currency demand (17.3); the split is indeterminate. -/
theorem kw_optimal_iff {ωy ωo pa pb pa1 pb1 R Ma Mb : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo)
    (hpa : 0 < pa) (hpb : 0 < pb) (hR : 0 ≤ R) (ha : pa1 / pa = R) (hb : pb1 / pb = R)
    (hMa : 0 ≤ Ma) (hMb : 0 ≤ Mb) :
    kwOptimal ωy ωo pa pb pa1 pb1 Ma Mb ↔ pa * Ma + pb * Mb = olgDemand ωy ωo R := by
  obtain ⟨hopt, huniq⟩ := eq_17_3 hωy hωo hR
  constructor
  · rintro ⟨⟨-, -, hc⟩, h⟩
    refine huniq _ ⟨⟨by positivity, hc⟩, fun s' hs' => ?_⟩
    have := h (s' / pa) 0 ⟨div_nonneg hs'.1 hpa.le, le_rfl, by
      rw [mul_div_cancel₀ _ hpa.ne', mul_zero, add_zero]; exact hs'.2⟩
    rwa [kw_equal_returns_util hpa.ne' hpb.ne' ha hb, kw_equal_returns_util hpa.ne' hpb.ne' ha hb,
      mul_div_cancel₀ _ hpa.ne', mul_zero, add_zero] at this
  · intro h
    refine ⟨⟨hMa, hMb, by rw [h]; exact hopt.1.2⟩, fun Ma' Mb' hf => ?_⟩
    rw [kw_equal_returns_util hpa.ne' hpb.ne' ha hb, kw_equal_returns_util hpa.ne' hpb.ne' ha hb, h]
    exact hopt.2 _ ⟨by have := hf.1; have := hf.2.1; positivity, hf.2.2⟩

/-- The problem is symmetric in the two currencies. -/
theorem kw_optimal_comm {ωy ωo pa pb pa1 pb1 Ma Mb : ℝ} :
    kwOptimal ωy ωo pa pb pa1 pb1 Ma Mb ↔ kwOptimal ωy ωo pb pa pb1 pa1 Mb Ma := by
  have hu : ∀ x y, kwUtil ωy ωo pa pb pa1 pb1 x y = kwUtil ωy ωo pb pa pb1 pa1 y x := fun x y => by
    unfold kwUtil; ring_nf
  have hf : ∀ x y, kwFeasible ωy pa pb x y ↔ kwFeasible ωy pb pa y x := fun x y => by
    unfold kwFeasible; constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, by linarith⟩
  unfold kwOptimal
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hf _ _).1 h1, fun x y hxy => by rw [← hu, ← hu]; exact h2 y x ((hf _ _).2 hxy)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hf _ _).2 h1, fun x y hxy => by rw [hu, hu]; exact h2 y x ((hf _ _).1 hxy)⟩

/-- AKMM, p. 524: if currency `a` is free today but valued tomorrow there is no optimum. -/
theorem kw_zero_pos {ωy ωo pb pa1 pb1 Ma Mb : ℝ} (hωo : 0 < ωo) (hpa1 : 0 < pa1)
    (hpb1 : 0 ≤ pb1) : ¬ kwOptimal ωy ωo 0 pb pa1 pb1 Ma Mb := by
  rintro ⟨⟨hMa, hMb, hc⟩, h⟩
  have := h (Ma + 1) Mb ⟨by linarith, hMb, by simpa using hc⟩
  unfold kwUtil at this
  have hlt : Real.log (ωo + pa1 * Ma + pb1 * Mb) < Real.log (ωo + pa1 * (Ma + 1) + pb1 * Mb) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  simp only [zero_mul, sub_zero] at this
  linarith

/-- AKMM, p. 524: if currency `a` is valued today but worthless tomorrow, holding it is not
optimal. -/
theorem kw_pos_zero {ωy ωo pa pb pb1 Ma Mb : ℝ} (hpa : 0 < pa) (hMa : 0 < Ma) :
    ¬ kwOptimal ωy ωo pa pb 0 pb1 Ma Mb := by
  rintro ⟨⟨-, hMb, hc⟩, h⟩
  have := h 0 Mb ⟨le_rfl, hMb, by nlinarith⟩
  unfold kwUtil at this
  have hlt : Real.log (ωy - pa * Ma - pb * Mb) < Real.log (ωy - pa * 0 - pb * Mb) :=
    Real.log_lt_log (by nlinarith) (by nlinarith)
  simp only [zero_mul, add_zero, mul_zero, sub_zero] at this hlt
  linarith

/-- **AKMM, pp. 524–525: the structure of equilibria.** With `M_a, M_b > 0`, in every
equilibrium each currency is valued at all dates or at none, and if both are valued their
returns are equal at every date. -/
theorem kw_structure {ωy ωo Ma Mb : ℝ} (hωo : 0 < ωo) (hMa : 0 < Ma) (hMb : 0 < Mb)
    {pa pb : ℕ → ℝ} (h : kwIsEquilibrium ωy ωo Ma Mb pa pb) :
    ((∀ t, pa t = 0) ∨ ∀ t, 0 < pa t) ∧ ((∀ t, pb t = 0) ∨ ∀ t, 0 < pb t) ∧
      ((∀ t, 0 < pa t) → (∀ t, 0 < pb t) → ∀ t, pa (t + 1) / pa t = pb (t + 1) / pb t) := by
  obtain ⟨hnn, hopt⟩ := h
  have hopt' : ∀ t, kwOptimal ωy ωo (pb t) (pa t) (pb (t + 1)) (pa (t + 1)) Mb Ma :=
    fun t => kw_optimal_comm.1 (hopt t)
  have dich : ∀ (p q : ℕ → ℝ) (M M' : ℝ), 0 < M → (∀ t, 0 ≤ p t) → (∀ t, 0 ≤ q t) →
      (∀ t, kwOptimal ωy ωo (p t) (q t) (p (t + 1)) (q (t + 1)) M M') →
      (∀ t, p t = 0) ∨ ∀ t, 0 < p t := by
    intro p q M M' hM hp hq ho
    have up : ∀ t, p t = 0 → p (t + 1) = 0 := fun t ht => by
      by_contra hn
      have := ho t
      rw [ht] at this
      exact kw_zero_pos hωo (lt_of_le_of_ne (hp _) (Ne.symm hn)) (hq _) this
    have up' : ∀ t, 0 < p t → 0 < p (t + 1) := fun t ht => by
      by_contra hn
      have h0 : p (t + 1) = 0 := le_antisymm (not_lt.1 hn) (hp _)
      have := ho t
      rw [h0] at this
      exact kw_pos_zero ht hM this
    rcases (hp 0).lt_or_eq with h0 | h0
    · right; intro t; induction t with
        | zero => exact h0
        | succ n ih => exact up' n ih
    · left; intro t; induction t with
        | zero => exact h0.symm
        | succ n ih => exact up n ih
  refine ⟨dich pa pb Ma Mb hMa (fun t => (hnn t).1) (fun t => (hnn t).2) hopt,
    dich pb pa Mb Ma hMb (fun t => (hnn t).2) (fun t => (hnn t).1) hopt', fun ha hb t => ?_⟩
  rcases lt_trichotomy (pa (t + 1) / pa t) (pb (t + 1) / pb t) with hlt | heq | hgt
  · exact absurd (hopt t) (kw_dominated hωo (ha t) (hb t) (hnn _).1 (hnn _).2 hlt hMa)
  · exact heq
  · exact absurd (hopt' t) (kw_dominated hωo (hb t) (ha t) (hnn _).2 (hnn _).1 hgt hMb)

/-- AKMM, p. 525: with equal returns at all dates the exchange rate `e_t = p_{a,t}/p_{b,t}` is
constant. -/
theorem kw_e_constant {pa pb : ℕ → ℝ} (ha : ∀ t, 0 < pa t) (hb : ∀ t, 0 < pb t)
    (h : ∀ t, pa (t + 1) / pa t = pb (t + 1) / pb t) (t : ℕ) : pa t / pb t = pa 0 / pb 0 := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    have h' := h n
    rw [div_eq_div_iff (ha n).ne' (hb n).ne'] at h'
    rw [div_eq_div_iff (hb (n + 1)).ne' (hb n).ne']
    linear_combination h'

/-- **AKMM, p. 525: the exchange rate is indeterminate.** Let `x` be a positive equilibrium path
of total real balances in the one-currency economy ((17.5) with stock `1`). For every `e > 0`
the prices `p_{b,t} = x_t/(eM_a + M_b)`, `p_{a,t} = ep_{b,t}` form an equilibrium with both
stocks held. -/
theorem kw_indeterminate {ωy ωo Ma Mb e : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hMa : 0 < Ma)
    (hMb : 0 < Mb) (he : 0 < e) {x : ℕ → ℝ} (hx : olgIsEquilibrium ωy ωo 1 x) (hx0 : 0 < x 0) :
    kwIsEquilibrium ωy ωo Ma Mb (fun t => e * (x t / (e * Ma + Mb)))
      (fun t => x t / (e * Ma + Mb)) := by
  have hK : 0 < e * Ma + Mb := by positivity
  have hpos : ∀ t, 0 < x t := by
    rcases (eq_17_5 hωy hωo one_pos x).1 hx with h | h
    · exact absurd (h 0) hx0.ne'
    · exact fun t => (h t).1
  refine ⟨fun t => ⟨by have := hpos t; positivity, by have := hpos t; positivity⟩, fun t => ?_⟩
  have hR : 0 ≤ x (t + 1) / x t := div_nonneg (hpos _).le (hpos t).le
  have hd := ((olg_moneyOptimal_iff_pos hωy hωo (hpos t) (hpos (t + 1)).le).1 (hx.2 t)).2
  rw [mul_one] at hd
  have hxt := (hpos t).ne'
  rw [kw_optimal_iff hωy hωo (by have := hpos t; positivity) (by have := hpos t; positivity) hR
    (by field_simp) (by field_simp) hMa.le hMb.le]
  rw [← hd]
  field_simp

/-- AKMM, p. 525: the equilibria in which currency `a` is never valued are the one-currency
equilibria for `b` (for instance `e = 0`). -/
theorem kw_unvalued {ωy ωo Ma Mb : ℝ} (hMa : 0 ≤ Ma) {pb : ℕ → ℝ}
    (h : olgIsEquilibrium ωy ωo Mb pb) : kwIsEquilibrium ωy ωo Ma Mb (fun _ => 0) pb := by
  have hu : ∀ t x y, kwUtil ωy ωo 0 (pb t) 0 (pb (t + 1)) x y =
      olgMoneyUtil ωy ωo (pb t) (pb (t + 1)) y := fun t x y => by
    unfold kwUtil olgMoneyUtil; ring_nf
  refine ⟨fun t => ⟨le_rfl, h.1 t⟩, fun t => ⟨⟨hMa, (h.2 t).1.1, by simpa using (h.2 t).1.2⟩,
    fun x y hxy => ?_⟩⟩
  rw [hu, hu]
  exact (h.2 t).2 y ⟨hxy.2.1, by simpa using hxy.2.2⟩

/-- AKMM, p. 525: the modified demand with transfers `p_{b,t+1}(γ_t − 1)M_t` to the old is the
one-currency demand with old-age income `ω_o + p_{b,t+1}(γ_t − 1)M_t`; at an interior solution
`p_{b,t}M_t = (ω_y − (ω_o + p_{b,t+1}(γ_t − 1)M_t)/(p_{b,t+1}/p_{b,t}))/2`. -/
theorem kw_modified_demand {ωy W R : ℝ} (hint : W < R * ωy) :
    olgDemand ωy W R = (ωy - W / R) / 2 := by
  unfold olgDemand
  simp only [not_le.2 hint, ↓reduceIte]

/-- **AKMM, p. 526: the long-run real value of total money.** With constant growth `γ > 0`, a
stationary solution of the modified demand (`p_{b,t+1}/p_{b,t} = 1/γ`, transfer value
`(γ − 1)x/γ`) is `x = (ω_y − γω_o)/(1 + γ)`. -/
theorem kw_limit_formula {ωy ωo γ x : ℝ} (hγ : 0 < γ) :
    x = (ωy - (ωo + (γ - 1) * x / γ) / (1 / γ)) / 2 ↔ x = (ωy - γ * ωo) / (1 + γ) := by
  have e : (ωo + (γ - 1) * x / γ) / (1 / γ) = γ * ωo + (γ - 1) * x := by field_simp
  rw [e, eq_div_iff (two_ne_zero), eq_div_iff (by linarith : (1 : ℝ) + γ ≠ 0)]
  constructor <;> intro h <;> linear_combination h

/-- AKMM, p. 526: the limit `(ω_y − γω_o)/(1 + γ)` is strictly decreasing in `γ`: the value of
the money stock when only the slower-growing currency is valued (`e = 0`) is higher. -/
theorem kw_limit_lower {ωy ωo γa γb : ℝ} (hωy : 0 < ωy) (hωo : 0 < ωo) (hγb : 0 < γb)
    (hγ : γb < γa) : (ωy - γa * ωo) / (1 + γa) < (ωy - γb * ωo) / (1 + γb) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The Kareken–Wallace limit is the stationary value of §17.2.3 with `γ = 1 + μ`
(`mg_stationary_iff`). -/
theorem kw_limit_eq_mg (ωy ωo μ : ℝ) :
    (ωy - (1 + μ) * ωo) / (1 + (1 + μ)) = (ωy - (1 + μ) * ωo) / (2 + μ) := by ring_nf

/-- **AKMM, p. 526: Gresham's law.** With `M_{a,t} = M_{a,0}γ_aᵗ`, `M_{b,t} = M_{b,0}γ_bᵗ`,
`γ_a > γ_b > 0` and `e > 0`, the share of currency `a` in the total stock
`M_t = eM_{a,t} + M_{b,t}` tends to one and the growth factor `γ_t = M_{t+1}/M_t` tends to
`γ_a`. -/
theorem kw_gresham {e Ma0 Mb0 γa γb : ℝ} (he : 0 < e) (hMa : 0 < Ma0) (hMb : 0 < Mb0)
    (hγb : 0 < γb) (hγ : γb < γa) :
    Tendsto (fun t : ℕ => e * Ma0 * γa ^ t / (e * Ma0 * γa ^ t + Mb0 * γb ^ t)) atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ => (e * Ma0 * γa ^ (t + 1) + Mb0 * γb ^ (t + 1)) /
        (e * Ma0 * γa ^ t + Mb0 * γb ^ t)) atTop (𝓝 γa) := by
  have hγa : 0 < γa := hγb.trans hγ
  set k := Mb0 / (e * Ma0) with hk
  have hk0 : 0 < k := by positivity
  have hr : Tendsto (fun t : ℕ => (γb / γa) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hγa).2 hγ)
  have hden : Tendsto (fun t : ℕ => 1 + k * (γb / γa) ^ t) atTop (𝓝 1) := by
    simpa using (hr.const_mul k).const_add 1
  have e1 : ∀ t : ℕ, e * Ma0 * γa ^ t / (e * Ma0 * γa ^ t + Mb0 * γb ^ t) =
      1 / (1 + k * (γb / γa) ^ t) := fun t => by
    have := pow_pos hγa t
    rw [hk, div_pow]
    field_simp
  have e2 : ∀ t : ℕ, (e * Ma0 * γa ^ (t + 1) + Mb0 * γb ^ (t + 1)) /
      (e * Ma0 * γa ^ t + Mb0 * γb ^ t) =
        (γa + k * γb * (γb / γa) ^ t) / (1 + k * (γb / γa) ^ t) := fun t => by
    have := pow_pos hγa t
    have := pow_pos hγb t
    rw [hk, div_pow, pow_succ, pow_succ]
    field_simp
  constructor
  · simp only [e1]
    simpa using hden.inv₀ one_ne_zero
  · simp only [e2]
    have hnum : Tendsto (fun t : ℕ => γa + k * γb * (γb / γa) ^ t) atTop (𝓝 γa) := by
      simpa using (hr.const_mul (k * γb)).const_add γa
    have := hnum.div hden one_ne_zero
    rw [div_one] at this
    exact this

end AKMM.Money

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Missing assets: fiat money in the Huggett economy

AKMM, §17.5, pp. 528–529. The Huggett economy with the borrowing limit `a′ ≥ 0`, two income
states `ω_lo < ω_hi` with transition probabilities `π_{·|·}`, utility `u` with `u′` strictly
decreasing. In the autarky equilibrium nobody trades and the bond price is set by the agent who
values the bond most.

* `ma_valuation_high_gt_low`: the high-income agent values the bond strictly more than the
  low-income agent, `π_{hi|hi} + π_{lo|hi}R > π_{lo|lo} + π_{hi|lo}/R`, `R = u′(ω_lo)/u′(ω_hi)`;
  hence at the autarky price the low-income agent would like to borrow (`ma_low_constrained`).
* `ma_autarky_price`: `qu′(ω_hi) = β(π_{hi|hi}u′(ω_hi) + π_{lo|hi}u′(ω_lo))` gives
  `1/q = (1/β)/(π_{hi|hi} + π_{lo|hi}u′(ω_lo)/u′(ω_hi)) < 1/β`.
* `ma_negative_rate_iff`: the autarky net rate is negative iff
  `β(π_{hi|hi} + π_{lo|hi}R) > 1`; an instance with log utility (`ma_negative_rate_example`).
* `ma_price_level`: with a constant price level money has gross return one; if aggregate saving
  in the `q = 1` economy is `m > 0`, the price level is `P = M/m` (Miao's
  `bw_fiat_quantity_theory`, from the `IncompleteMarkets` dependency).
-/

namespace AKMM.Money

/-- AKMM, p. 528: the bond valuations of the two agents at autarky. With `R > 1`
(`u′(ω_lo) > u′(ω_hi)`), `π_{lo|hi} > 0` and rows summing to one,
`π_{hi|hi} + π_{lo|hi}R > 1 ≥ π_{lo|lo} + π_{hi|lo}/R`. -/
theorem ma_valuation_high_gt_low {phh plh pll phl R : ℝ} (hR : 1 < R) (hplh : 0 < plh)
    (hphl : 0 ≤ phl) (hrow1 : phh + plh = 1) (hrow2 : pll + phl = 1) :
    1 < phh + plh * R ∧ pll + phl / R ≤ 1 ∧ pll + phl / R < phh + plh * R := by
  have h1 : 1 < phh + plh * R := by nlinarith
  have h2 : pll + phl / R ≤ 1 := by
    have : phl / R ≤ phl := div_le_self hphl hR.le
    linarith
  exact ⟨h1, h2, lt_of_le_of_lt h2 h1⟩

/-- AKMM, p. 528: at the autarky price set by the high-income agent the low-income agent is
borrowing constrained: `qu′(ω_lo) > β(π_{lo|lo}u′(ω_lo) + π_{hi|lo}u′(ω_hi))`. -/
theorem ma_low_constrained {β q phh plh pll phl uhi ulo : ℝ} (hβ : 0 < β) (huhi : 0 < uhi)
    (hlt : uhi < ulo) (hplh : 0 < plh) (hphl : 0 ≤ phl) (hrow1 : phh + plh = 1)
    (hrow2 : pll + phl = 1) (hq : q * uhi = β * (phh * uhi + plh * ulo)) :
    β * (pll * ulo + phl * uhi) < q * ulo := by
  have hulo : 0 < ulo := huhi.trans hlt
  have hR : 1 < ulo / uhi := (one_lt_div huhi).2 hlt
  obtain ⟨-, -, h3⟩ := ma_valuation_high_gt_low hR hplh hphl hrow1 hrow2
  have hqv : q = β * (phh + plh * (ulo / uhi)) := by
    field_simp
    linear_combination hq
  rw [hqv]
  have : pll * ulo + phl * uhi = ulo * (pll + phl / (ulo / uhi)) := by field_simp
  rw [this]
  nlinarith [mul_lt_mul_of_pos_left h3 (mul_pos hβ hulo)]

/-- **AKMM, p. 529: the autarky interest rate.** From the high agent's Euler equation
`qu′(ω_hi) = β(π_{hi|hi}u′(ω_hi) + π_{lo|hi}u′(ω_lo))`:
`1/q = (1/β)·1/(π_{hi|hi} + π_{lo|hi}u′(ω_lo)/u′(ω_hi)) < 1/β`. -/
theorem ma_autarky_price {β q phh plh uhi ulo : ℝ} (hβ : 0 < β) (huhi : 0 < uhi)
    (hlt : uhi < ulo) (hplh : 0 < plh) (hrow1 : phh + plh = 1)
    (hq : q * uhi = β * (phh * uhi + plh * ulo)) :
    1 / q = 1 / β * (1 / (phh + plh * (ulo / uhi))) ∧ 1 / q < 1 / β := by
  have hR : 1 < ulo / uhi := (one_lt_div huhi).2 hlt
  have hv : 1 < phh + plh * (ulo / uhi) := by nlinarith
  have hqv : q = β * (phh + plh * (ulo / uhi)) := by
    field_simp
    linear_combination hq
  refine ⟨by rw [hqv]; field_simp, ?_⟩
  rw [hqv, div_lt_div_iff₀ (by positivity) hβ]
  nlinarith

/-- AKMM, p. 529: the autarky net real rate is negative (`1/q < 1`) iff
`β(π_{hi|hi} + π_{lo|hi}u′(ω_lo)/u′(ω_hi)) > 1`. -/
theorem ma_negative_rate_iff {β V : ℝ} (hβ : 0 < β) (hV : 0 < V) :
    1 / (β * V) < 1 ↔ 1 < β * V := by
  rw [div_lt_one (by positivity)]

/-- AKMM, p. 529 (an instance): with `u = log`, `ω_hi = 2`, `ω_lo = 1/2` (`R = 4`),
`π_{hi|hi} = π_{lo|hi} = 1/2` and `β = 1/2`, the autarky gross rate is `1/q = 4/5 < 1`. -/
theorem ma_negative_rate_example :
    1 / ((1 / 2 : ℝ) * (1 / 2 + 1 / 2 * ((1 / 2 : ℝ)⁻¹ / (2 : ℝ)⁻¹))) = 4 / 5 := by norm_num

/-- AKMM, p. 529 (via Miao's `bw_fiat_quantity_theory`): with a constant price level, money has
gross return one and the economy is the `q = 1` saving economy; if aggregate saving there is
`m > 0` and the money stock is `M > 0`, the money market clears at a positive price level iff
`P = M/m`. -/
theorem ma_price_level {M m P : ℝ} (hM : 0 < M) (hm : 0 < m) :
    (0 < P ∧ m = M / P) ↔ P = M / m :=
  Miao.IncompleteMarkets.bw_fiat_quantity_theory hM hm

end AKMM.Money

set_option linter.style.longLine false
#print axioms AKMM.Money.olgUtil
#print axioms AKMM.Money.olgFeasible
#print axioms AKMM.Money.olgOptimal
#print axioms AKMM.Money.olgDemand
#print axioms AKMM.Money.eq_17_2
#print axioms AKMM.Money.olg_util_sub_le
#print axioms AKMM.Money.olg_demand_feasible
#print axioms AKMM.Money.olg_demand_marginal
#print axioms AKMM.Money.eq_17_3
#print axioms AKMM.Money.olg_demand_eq_max
#print axioms AKMM.Money.olg_interior_cons
#print axioms AKMM.Money.olg_interior_iff
#print axioms AKMM.Money.olgMoneyUtil
#print axioms AKMM.Money.olgMoneyFeasible
#print axioms AKMM.Money.olgMoneyOptimal
#print axioms AKMM.Money.olgIsEquilibrium
#print axioms AKMM.Money.olg_moneyUtil_eq
#print axioms AKMM.Money.olg_moneyOptimal_iff_pos
#print axioms AKMM.Money.olg_moneyOptimal_zero_pos
#print axioms AKMM.Money.olg_moneyOptimal_zero_zero
#print axioms AKMM.Money.olg_step_iff
#print axioms AKMM.Money.eq_17_5
#print axioms AKMM.Money.eq_17_5_div
#print axioms AKMM.Money.eq_17_5_real
#print axioms AKMM.Money.olg_closed_form_step
#print axioms AKMM.Money.olg_classification
#print axioms AKMM.Money.olg_no_monetary
#print axioms AKMM.Money.olg_nonmonetary_exists
#print axioms AKMM.Money.olg_continuum
#print axioms AKMM.Money.olg_unique_given_p0
#print axioms AKMM.Money.olg_stationary
#print axioms AKMM.Money.olg_decreasing_to_zero
#print axioms AKMM.Money.olgMap
#print axioms AKMM.Money.olg_map_fixed_iff
#print axioms AKMM.Money.olg_map_strictMonoOn
#print axioms AKMM.Money.olg_map_hasDerivAt
#print axioms AKMM.Money.olg_map_slopes
#print axioms AKMM.Money.olg_map_domain
#print axioms AKMM.Money.olg_nominal_neutral
#print axioms AKMM.Money.olgIndirect
#print axioms AKMM.Money.olg_indirect_eq
#print axioms AKMM.Money.olg_indirect_strictMonoOn
#print axioms AKMM.Money.olgCohortUtil
#print axioms AKMM.Money.olg_cohort_util_eq
#print axioms AKMM.Money.olg_return_strictMonoOn
#print axioms AKMM.Money.olg_ranking
#print axioms AKMM.Money.olg_monetary_improves_autarky
#print axioms AKMM.Money.olg_stationary_dominates
#print axioms AKMM.Money.olg_stationary_welfare
#print axioms AKMM.Money.olg_smoothing_hurts_old
#print axioms AKMM.Money.olg_return_limit
#print axioms AKMM.Money.olgMiao
#print axioms AKMM.Money.olg_miao_paths
#print axioms AKMM.Money.olg_miao_stationary_pareto
#print axioms AKMM.Money.olg_miao_autarky_pareto_iff
#print axioms AKMM.Money.mgStock
#print axioms AKMM.Money.mgIsEquilibrium
#print axioms AKMM.Money.mgStock_pos
#print axioms AKMM.Money.mgStock_succ
#print axioms AKMM.Money.mg_step_iff
#print axioms AKMM.Money.mg_stationary_iff
#print axioms AKMM.Money.mg_return
#print axioms AKMM.Money.mg_value_strictAntiOn
#print axioms AKMM.Money.eq_17_11
#print axioms AKMM.Money.dyn_unbounded
#print axioms AKMM.Money.eq_17_12
#print axioms AKMM.Money.eq_17_12_prices
#print axioms AKMM.Money.eq_17_13
#print axioms AKMM.Money.dyn_no_value_of_pos_rate
#print axioms AKMM.Money.eq_17_14
#print axioms AKMM.Money.dyn_printed_product
#print axioms AKMM.Money.dyn_tvc_money_vanishes
#print axioms AKMM.Money.dyn_no_valued_money
#print axioms AKMM.Money.eq_17_15
#print axioms AKMM.Money.eq_17_19
#print axioms AKMM.Money.cia_stationary_growth
#print axioms AKMM.Money.eq_17_24
#print axioms AKMM.Money.cia_must_bind
#print axioms AKMM.Money.cia_mrs_lt_mrt
#print axioms AKMM.Money.cia_log_consumption
#print axioms AKMM.Money.cia_log_compare
#print axioms AKMM.Money.cia_friedman_rule
#print axioms AKMM.Money.tcPsi
#print axioms AKMM.Money.tc_cost_homogeneous
#print axioms AKMM.Money.tc_psi_hasDerivAt
#print axioms AKMM.Money.eq_17_28
#print axioms AKMM.Money.tc_fisher_lhs
#print axioms AKMM.Money.tcDemand
#print axioms AKMM.Money.eq_17_29
#print axioms AKMM.Money.tc_demand_homogeneous
#print axioms AKMM.Money.tc_demand_elasticity
#print axioms AKMM.Money.tc_log_demand
#print axioms AKMM.Money.tc_demand_strictAntiOn
#print axioms AKMM.Money.eq_17_35
#print axioms AKMM.Money.miu_homothetic_partials
#print axioms AKMM.Money.miu_homothetic_mrs
#print axioms AKMM.Money.miu_homothetic_demand
#print axioms AKMM.Money.miu_ces_crs
#print axioms AKMM.Money.eq_17_36
#print axioms AKMM.Money.eq_17_37
#print axioms AKMM.Money.eq_17_38
#print axioms AKMM.Money.hypIsPath
#print axioms AKMM.Money.hyp_steady_iff
#print axioms AKMM.Money.hyp_step_exists
#print axioms AKMM.Money.hyp_tendsto_zero
#print axioms AKMM.Money.hyp_exists_path
#print axioms AKMM.Money.hyp_all_paths
#print axioms AKMM.Money.hyp_above_increasing
#print axioms AKMM.Money.hyp_return_lt
#print axioms AKMM.Money.hyp_local_stable
#print axioms AKMM.Money.hyp_local_unstable
#print axioms AKMM.Money.hyp_log_unique
#print axioms AKMM.Money.pegIsEquilibrium
#print axioms AKMM.Money.peg_pins
#print axioms AKMM.Money.peg_c0
#print axioms AKMM.Money.peg_exists
#print axioms AKMM.Money.peg_real_indeterminacy
#print axioms AKMM.Money.ruleMap
#print axioms AKMM.Money.eq_17_40
#print axioms AKMM.Money.rule_target
#print axioms AKMM.Money.rule_map_hasDerivAt
#print axioms AKMM.Money.rule_local_bound
#print axioms AKMM.Money.rule_determinate
#print axioms AKMM.Money.rule_indeterminate
#print axioms AKMM.Money.rule_phi_pos_determinate
#print axioms AKMM.Money.rule_phi_neg_indeterminate
#print axioms AKMM.Money.rule_phi_very_neg_determinate
#print axioms AKMM.Money.rule_printed_counterexample
#print axioms AKMM.Money.rule_knife_edge
#print axioms AKMM.Money.clH
#print axioms AKMM.Money.clh
#print axioms AKMM.Money.clh1
#print axioms AKMM.Money.clh2
#print axioms AKMM.Money.clTheta
#print axioms AKMM.Money.clH_pos
#print axioms AKMM.Money.cl_h_eq_composite
#print axioms AKMM.Money.cl_h_hasDerivAt_c
#print axioms AKMM.Money.cl_h_hasDerivAt_m
#print axioms AKMM.Money.clDemand
#print axioms AKMM.Money.eq_17_41
#print axioms AKMM.Money.cl_demand_homogeneous
#print axioms AKMM.Money.cl_demand_elasticity
#print axioms AKMM.Money.cl_demand_strictAnti
#print axioms AKMM.Money.cl_demand_tendsto_zero
#print axioms AKMM.Money.cl_footnote_17
#print axioms AKMM.Money.cl_h1_hasDerivAt_c
#print axioms AKMM.Money.cl_h1_hasDerivAt_m
#print axioms AKMM.Money.cl_footnote_18_identities
#print axioms AKMM.Money.cl_h2_mul
#print axioms AKMM.Money.cl_weight_tendsto
#print axioms AKMM.Money.cl_footnote_18_limits
#print axioms AKMM.Money.gb_flow_real
#print axioms AKMM.Money.gb_iterate
#print axioms AKMM.Money.eq_17_43
#print axioms AKMM.Money.gb_printed_discount
#print axioms AKMM.Money.eq_17_44
#print axioms AKMM.Money.gb_zero_rate
#print axioms AKMM.Money.gb_zero_rate_printed
#print axioms AKMM.Money.gb_stationary
#print axioms AKMM.Money.gb_omo_irrelevance
#print axioms AKMM.Money.lf_increasing_part
#print axioms AKMM.Money.lf_interior_max
#print axioms AKMM.Money.lf_counterexample
#print axioms AKMM.Money.lf_tc_no_max
#print axioms AKMM.Money.ua_stationary
#print axioms AKMM.Money.ua_dynamic
#print axioms AKMM.Money.fb_backstop
#print axioms AKMM.Money.fb_stationary
#print axioms AKMM.Money.eq_17_45
#print axioms AKMM.Money.eq_17_46
#print axioms AKMM.Money.ftpl_price_level
#print axioms AKMM.Money.ftpl_unique
#print axioms AKMM.Money.ftpl_none
#print axioms AKMM.Money.kwUtil
#print axioms AKMM.Money.kwFeasible
#print axioms AKMM.Money.kwOptimal
#print axioms AKMM.Money.kwIsEquilibrium
#print axioms AKMM.Money.kw_dominated
#print axioms AKMM.Money.kw_equal_returns_util
#print axioms AKMM.Money.kw_optimal_iff
#print axioms AKMM.Money.kw_optimal_comm
#print axioms AKMM.Money.kw_zero_pos
#print axioms AKMM.Money.kw_pos_zero
#print axioms AKMM.Money.kw_structure
#print axioms AKMM.Money.kw_e_constant
#print axioms AKMM.Money.kw_indeterminate
#print axioms AKMM.Money.kw_unvalued
#print axioms AKMM.Money.kw_modified_demand
#print axioms AKMM.Money.kw_limit_formula
#print axioms AKMM.Money.kw_limit_lower
#print axioms AKMM.Money.kw_limit_eq_mg
#print axioms AKMM.Money.kw_gresham
#print axioms AKMM.Money.ma_valuation_high_gt_low
#print axioms AKMM.Money.ma_low_constrained
#print axioms AKMM.Money.ma_autarky_price
#print axioms AKMM.Money.ma_negative_rate_iff
#print axioms AKMM.Money.ma_negative_rate_example
#print axioms AKMM.Money.ma_price_level
