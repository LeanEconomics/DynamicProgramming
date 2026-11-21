/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LifeCycleFiscalPolicy.RicardianEquivalence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Ricardian equivalence in two periods

AKMM, §15.4, pp. 455–456.

The household chooses `(c₀, ℓ₀, c₁, ℓ₁)` and bonds `b₀` subject to `c₀ + b₀ = w₀ℓ₀ + T₀` and
`c₁ = w₁ℓ₁ + (1 + r₁)b₀ − τ₁` (`ricFlow`). The government issues `B₀ = T₀` and repays with
`τ₁ = (1 + r₁)B₀` (`ricGov`).

* The flow constraints hold for some `b₀` iff the present-value constraint
  `c₀ + c₁/(1 + r₁) = w₀ℓ₀ + w₁ℓ₁/(1 + r₁) + T₀ − τ₁/(1 + r₁)` holds (`ric_pv_iff`); `b₀` drops out.
* With `τ₁ = (1 + r₁)T₀` the tax and transfer terms sum to zero (`ric_taxes_cancel`), so the
  budget set equals the one with `T₀ = τ₁ = B₀ = 0` (`ric_budgetSet_eq`): **for any preferences**
  a plan is optimal with the transfer iff it is optimal without (`ric_optimal_iff`), and the
  household finances an unchanged allocation by saving exactly `T₀` more (`ric_saving`), which
  matches the extra bonds and pays the tax (`ric_market_clears`).
* With labour fixed, this is Obstfeld–Rogoff's two-period timing neutrality, imported from
  `LifeCycleFiscalPolicy` (`ric_obstfeld_rogoff`).

Correction: p. 456 writes "zero taxes and transfers (`T₀ = τ₁ = B₁ = 0`)"; the debt in the
two-period model is `B₀` (`ricGov`).
-/

namespace AKMM.FiscalPolicy

/-- The household's flow budget constraints (AKMM, p. 455) for plan
`x = (c₀, ℓ₀, c₁, ℓ₁)` and bond purchases `b₀`. -/
def ricFlow (w0 w1 r1 T0 τ1 : ℝ) (x : ℝ × ℝ × ℝ × ℝ) (b0 : ℝ) : Prop :=
  x.1 + b0 = w0 * x.2.1 + T0 ∧ x.2.2.1 = w1 * x.2.2.2 + (1 + r1) * b0 - τ1

/-- The household's budget set: plans financed by some bond position. -/
def ricBudgetSet (w0 w1 r1 T0 τ1 : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  {x | ∃ b0, ricFlow w0 w1 r1 T0 τ1 x b0}

/-- The government's policy (AKMM, p. 455): the transfer `T₀` is financed by debt `B₀ = T₀`,
repaid by the lump-sum tax `τ₁ = (1 + r₁)B₀`. -/
def ricGov (r1 T0 B0 τ1 : ℝ) : Prop := B0 = T0 ∧ τ1 = (1 + r1) * B0

/-- AKMM, p. 455: the flow constraints hold for some `b₀` iff the present-value constraint holds;
"the value for debt purchases, `b₀`, drops out". -/
theorem ric_pv_iff {w0 w1 r1 T0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (x : ℝ × ℝ × ℝ × ℝ) :
    x ∈ ricBudgetSet w0 w1 r1 T0 τ1 ↔
      x.1 + x.2.2.1 / (1 + r1) = w0 * x.2.1 + w1 * x.2.2.2 / (1 + r1) + T0 - τ1 / (1 + r1) := by
  constructor
  · rintro ⟨b0, h0, h1⟩
    rw [h1]
    field_simp
    linear_combination (1 + r1) * h0
  · intro h
    refine ⟨w0 * x.2.1 + T0 - x.1, by ring, ?_⟩
    field_simp at h
    linear_combination h

/-- AKMM, p. 455: with `τ₁ = (1 + r₁)B₀ = (1 + r₁)T₀`, "the tax and transfer terms in the present
value budget constraint must sum to zero, regardless of the size of the initial transfer". -/
theorem ric_taxes_cancel {r1 T0 B0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (hg : ricGov r1 T0 B0 τ1) :
    T0 - τ1 / (1 + r1) = 0 := by
  obtain ⟨hB, hτ⟩ := hg
  rw [hτ, hB]
  field_simp
  ring

/-- AKMM, p. 456: the budget set with the debt-financed transfer equals the budget set with
`T₀ = τ₁ = B₀ = 0`. -/
theorem ric_budgetSet_eq {w0 w1 r1 T0 B0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (hg : ricGov r1 T0 B0 τ1) :
    ricBudgetSet w0 w1 r1 T0 τ1 = ricBudgetSet w0 w1 r1 0 0 := by
  ext x
  rw [ric_pv_iff hr, ric_pv_iff hr]
  have h := ric_taxes_cancel hr hg
  constructor <;> intro h' <;> simp only [zero_div, sub_zero, add_zero] at h' ⊢ <;> linarith

/-- **Ricardian equivalence** (AKMM, p. 456): "the household's optimal allocation of consumption
and hours must be identical to that in the case of zero taxes and transfers", for any utility
`U` over `(c₀, ℓ₀, c₁, ℓ₁)`. -/
theorem ric_optimal_iff {w0 w1 r1 T0 B0 τ1 : ℝ} (hr : 1 + r1 ≠ 0) (hg : ricGov r1 T0 B0 τ1)
    (U : ℝ × ℝ × ℝ × ℝ → ℝ) (x : ℝ × ℝ × ℝ × ℝ) :
    (x ∈ ricBudgetSet w0 w1 r1 T0 τ1 ∧ ∀ y ∈ ricBudgetSet w0 w1 r1 T0 τ1, U y ≤ U x) ↔
      (x ∈ ricBudgetSet w0 w1 r1 0 0 ∧ ∀ y ∈ ricBudgetSet w0 w1 r1 0 0, U y ≤ U x) := by
  rw [ric_budgetSet_eq hr hg]

/-- AKMM, p. 456: "The household must therefore respond to the initial transfer `T₀` by increasing
savings by exactly `T₀`": a plan financed by `b₀` without the policy is financed by `b₀ + T₀` with
it. -/
theorem ric_saving {w0 w1 r1 T0 B0 τ1 b0 : ℝ} (hg : ricGov r1 T0 B0 τ1) (x : ℝ × ℝ × ℝ × ℝ)
    (h : ricFlow w0 w1 r1 0 0 x b0) : ricFlow w0 w1 r1 T0 τ1 x (b0 + T0) := by
  obtain ⟨hB, hτ⟩ := hg
  obtain ⟨h0, h1⟩ := h
  constructor
  · linarith
  · rw [hτ, hB, h1]
    ring

/-- AKMM, p. 456: the extra saving "(i) exactly match[es] the additional supply of government
bonds issued, and (ii) provide[s] exactly enough second period income to pay the expected
lump-sum tax". -/
theorem ric_market_clears {r1 T0 B0 τ1 b0 : ℝ} (hg : ricGov r1 T0 B0 τ1) :
    (b0 + T0) - b0 = B0 ∧ (1 + r1) * ((b0 + T0) - b0) = τ1 := by
  obtain ⟨hB, hτ⟩ := hg
  constructor
  · rw [hB]
    ring
  · rw [hτ, hB]
    ring

/-- With hours fixed, AKMM's neutrality is Obstfeld–Rogoff's (O&R (3.1), p. 130): the private
budget set with taxes `(−T₀, (1 + r₁)T₀)` on endowments `(w₀ℓ₀, w₁ℓ₁)` equals the one without
taxes (`ObstfeldRogoff…two_period_budgetSet_eq_of_pv_eq`). -/
theorem ric_obstfeld_rogoff {w0 w1 l0 l1 r1 T0 : ℝ} (hr : 1 + r1 ≠ 0) :
    ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.twoPeriodBudgetSet r1
        (w0 * l0) (w1 * l1) (-T0) ((1 + r1) * T0) =
      ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.twoPeriodBudgetSet r1
        (w0 * l0) (w1 * l1) 0 0 := by
  apply ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.two_period_budgetSet_eq_of_pv_eq
  field_simp
  ring

end AKMM.FiscalPolicy
