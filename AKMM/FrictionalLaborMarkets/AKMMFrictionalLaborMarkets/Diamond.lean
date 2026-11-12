/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Diamond paradox

AKMM, §20.9, p. 621 (stated verbally, after Diamond 1971). `n ≥ 1` identical firms post wages
`w : Fin n → ℝ`; a worker produces `p` and has reservation value `b < p`; searching again costs
`s > 0`. A firm meets the worker with probability `1/n` and earns `p − w_i` if the worker accepts.

The worker side is described by the two properties of optimal sequential search with cost `s`
used in the book's argument (`DiamondWorker`): offers below `b` are rejected, and an offer
`w_i ≥ b` within `s` of the best offer `max_j w_j` is accepted (one more search costs `s` and can
raise the wage by less than `s`). `diamondAccept` is a concrete such rule.

* `diamond_ne`: everyone offering the reservation wage `b` is a Nash equilibrium ("no firm would
  want to deviate as offering a higher wage does not make it more likely that the firm will hire
  a worker").
* `diamond_unique`: it is the only Nash equilibrium: in any other profile the highest-wage firm
  gains by cutting its wage slightly without losing the worker, or a firm whose offer is rejected
  gains by offering `b`.
* `diamond_paradox`: hence for every search cost `s > 0`, however small, the unique equilibrium
  wage is `b`.

Departure: the book's argument is verbal; the formalisation makes the game explicit, with the
worker's behaviour summarised by the two properties above.
-/

namespace AKMM.FrictionalLaborMarkets

/-- AKMM, p. 621: a worker's acceptance rule with reservation value `b` and search cost `s`:
offers below `b` are rejected, and an offer `w_i ≥ b` with `w_j − s < w_i` for every `j` is
accepted. -/
structure DiamondWorker (n : ℕ) (b s : ℝ) where
  /-- whether the worker accepts firm `i`'s offer under the wage profile `w` -/
  acc : (Fin n → ℝ) → Fin n → Prop
  /-- offers below the reservation value are rejected -/
  reject_low : ∀ w i, w i < b → ¬ acc w i
  /-- offers that searching again (at cost `s`) cannot beat are accepted -/
  accept_high : ∀ w i, b ≤ w i → (∀ j, w j - s < w i) → acc w i

/-- A concrete acceptance rule: accept `w_i` iff `w_i ≥ b` and `w_i > w_j − s` for all `j`. -/
def diamondAccept (n : ℕ) (b s : ℝ) : DiamondWorker n b s where
  acc w i := b ≤ w i ∧ ∀ j, w j - s < w i
  reject_low _ _ h h' := absurd h'.1 (not_le.mpr h)
  accept_high _ _ h h' := ⟨h, h'⟩

/-- Firm `i`'s expected profit `(p − w_i)/n` if the worker accepts its offer, `0` otherwise. -/
noncomputable def diamondProfit {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ)
    (w : Fin n → ℝ) (i : Fin n) : ℝ := by
  classical exact if A.acc w i then (p - w i) / n else 0

/-- A wage profile is a Nash equilibrium if no firm gains by changing its own wage. -/
def DiamondNE {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ i (w' : ℝ), diamondProfit A p (Function.update w i w') i ≤ diamondProfit A p w i

/-- When the worker accepts firm `i`'s offer, its profit is `(p − w_i)/n`. -/
theorem diamond_profit_acc {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ) {w : Fin n → ℝ}
    {i : Fin n} (h : A.acc w i) : diamondProfit A p w i = (p - w i) / n := by
  classical
  unfold diamondProfit
  simp [h]

/-- Profit is zero when the offer is rejected. -/
theorem diamond_profit_rej {n : ℕ} {b s : ℝ} (A : DiamondWorker n b s) (p : ℝ) {w : Fin n → ℝ}
    {i : Fin n} (h : ¬ A.acc w i) : diamondProfit A p w i = 0 := by
  classical
  unfold diamondProfit
  simp [h]

/-- AKMM, p. 621: when all firms offer the reservation wage `b`, no firm gains by deviating. -/
theorem diamond_ne {n : ℕ} {b s p : ℝ} (A : DiamondWorker n b s) (hs : 0 < s) (hbp : b < p) :
    DiamondNE A p (fun _ ↦ b) := by
  intro i w'
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hacc : A.acc (fun _ ↦ b) i := A.accept_high _ _ le_rfl fun _ ↦ by linarith
  rw [diamond_profit_acc A p hacc]
  by_cases h : A.acc (Function.update (fun _ ↦ b) i w') i
  · rw [diamond_profit_acc A p h, Function.update_self]
    have hw' : b ≤ w' := by
      by_contra hc
      exact A.reject_low _ i (by rw [Function.update_self]; exact not_le.mp hc) h
    exact div_le_div_of_nonneg_right (by linarith) hn
  · rw [diamond_profit_rej A p h]
    exact div_nonneg (by linarith) hn

/-- AKMM, p. 621: the equilibrium is unique: in every Nash equilibrium every firm offers the
reservation wage `b`. -/
theorem diamond_unique {n : ℕ} {b s p : ℝ} (A : DiamondWorker n b s) (hs : 0 < s) (hbp : b < p)
    {w : Fin n → ℝ} (hNE : DiamondNE A p w) (i : Fin n) : w i = b := by
  classical
  have hn0 : 0 < n := Fin.pos i
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ w ⟨i, Finset.mem_univ i⟩
  have hk' : ∀ j, w j ≤ w k := fun j ↦ hk j (Finset.mem_univ j)
  -- step 1: the highest wage is at most `b`
  have hmax : w k ≤ b := by
    by_contra hc
    have hc : b < w k := not_le.mp hc
    set ε := min s (w k - b) / 2 with hε
    have hε0 : 0 < ε := by
      have : 0 < min s (w k - b) := lt_min hs (by linarith)
      positivity
    have hεs : ε < s := by
      have := min_le_left s (w k - b); linarith
    have hεb : ε ≤ w k - b := by
      have := min_le_right s (w k - b)
      have : 0 ≤ min s (w k - b) := by positivity
      linarith
    have hacc : A.acc w k := A.accept_high w k hc.le fun j ↦ by have := hk' j; linarith
    have hacc' : A.acc (Function.update w k (w k - ε)) k := by
      refine A.accept_high _ k (by rw [Function.update_self]; linarith) fun j ↦ ?_
      rw [Function.update_self]
      by_cases hj : j = k
      · subst hj; rw [Function.update_self]; linarith
      · rw [Function.update_of_ne hj]; have := hk' j; linarith
    have := hNE k (w k - ε)
    rw [diamond_profit_acc A p hacc', diamond_profit_acc A p hacc, Function.update_self] at this
    have := (div_le_div_iff_of_pos_right hn).mp this
    linarith
  -- step 2: every wage is at least `b`
  have hge : b ≤ w i := by
    by_contra hc
    have hc : w i < b := not_le.mp hc
    have hrej : ¬ A.acc w i := A.reject_low w i hc
    have hacc' : A.acc (Function.update w i b) i := by
      refine A.accept_high _ i (by rw [Function.update_self]) fun j ↦ ?_
      rw [Function.update_self]
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; linarith
      · rw [Function.update_of_ne hj]; have := hk' j; linarith
    have := hNE i b
    rw [diamond_profit_acc A p hacc', diamond_profit_rej A p hrej, Function.update_self] at this
    have : 0 < (p - b) / n := div_pos (by linarith) hn
    linarith
  have := hk' i
  linarith

/-- AKMM, p. 621 (**the Diamond paradox**): for every search cost `s > 0`, however small, the
wage profiles that are Nash equilibria are exactly the one where every firm offers the
reservation wage `b`. -/
theorem diamond_paradox {n : ℕ} {b p : ℝ} (hbp : b < p) (s : ℝ) (hs : 0 < s)
    (A : DiamondWorker n b s) (w : Fin n → ℝ) : DiamondNE A p w ↔ w = fun _ ↦ b := by
  constructor
  · intro h; funext i; exact diamond_unique A hs hbp h i
  · rintro rfl; exact diamond_ne A hs hbp

/-- The concrete acceptance rule `diamondAccept` instantiates `diamond_paradox`. -/
theorem diamond_paradox_example {n : ℕ} {b p s : ℝ} (hbp : b < p) (hs : 0 < s)
    (w : Fin n → ℝ) : DiamondNE (diamondAccept n b s) p w ↔ w = fun _ ↦ b :=
  diamond_paradox hbp s hs _ w

end AKMM.FrictionalLaborMarkets
