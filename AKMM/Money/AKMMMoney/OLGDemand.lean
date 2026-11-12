/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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
