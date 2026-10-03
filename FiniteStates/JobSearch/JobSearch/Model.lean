/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# The McCall job search model

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.1.1.1 (pp. 3–4)
and Assumption 1.1.1 (p. 11). An unemployed worker draws a wage offer each
period from a finite set `W ⊂ ℝ₊` with distribution `φ`; accepting means
working at that wage forever, rejecting means receiving compensation `c` and
drawing again. The discount factor is `β ∈ (0, 1)`.

`Model W` packages these primitives: the wage outcomes are the values of
`wage : W → ℝ` on a finite index type `W`, so that value functions are
functions `W → ℝ`. The expectation `E h = ∑ h(w) φ(w)` of §1.2.4.3 (p. 31) is
defined here with the facts the chapter uses about it: it preserves constants,
it is monotone, and it is 1-Lipschitz in the supremum norm.
-/

open Finset

namespace SargentStachurski.JobSearch

/-- The job search primitives (Assumption 1.1.1, p. 11): a finite set of nonnegative wage
offers with a probability distribution `φ`, compensation `c > 0`, and `β ∈ (0, 1)`. -/
structure Model (W : Type*) [Fintype W] where
  wage : W → ℝ
  wage_nonneg : ∀ w, 0 ≤ wage w
  φ : W → ℝ
  φ_nonneg : ∀ w, 0 ≤ φ w
  φ_sum : ∑ w, φ w = 1
  c : ℝ
  c_pos : 0 < c
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

theorem one_sub_β_pos : 0 < 1 - m.β := by linarith [m.β_lt_one]

theorem β_nonneg : 0 ≤ m.β := m.β_pos.le

/-- The expectation of `h(W)` under `φ`, `E h(W) = ∑ h(w) φ(w) = ⟨h, φ⟩` (p. 31). -/
def E (h : W → ℝ) : ℝ := ∑ w, h w * m.φ w

/-- The expectation of a constant is the constant. -/
theorem E_const (a : ℝ) : m.E (fun _ => a) = a := by
  simp only [E, ← mul_sum, m.φ_sum, mul_one]

/-- Expectation is monotone. -/
theorem E_mono {f g : W → ℝ} (h : ∀ w, f w ≤ g w) : m.E f ≤ m.E g :=
  sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (h w) (m.φ_nonneg w)

/-- A pointwise upper bound bounds the expectation. -/
theorem E_le_of_le {f : W → ℝ} {a : ℝ} (h : ∀ w, f w ≤ a) : m.E f ≤ a := by
  calc m.E f ≤ m.E (fun _ => a) := m.E_mono h
    _ = a := m.E_const a

/-- A pointwise lower bound bounds the expectation. -/
theorem le_E_of_le {f : W → ℝ} {a : ℝ} (h : ∀ w, a ≤ f w) : a ≤ m.E f := by
  calc a = m.E (fun _ => a) := (m.E_const a).symm
    _ ≤ m.E f := m.E_mono h

/-- The expectation of a nonnegative function is nonnegative. -/
theorem E_nonneg {f : W → ℝ} (h : ∀ w, 0 ≤ f w) : 0 ≤ m.E f := m.le_E_of_le h

/-- Expectation is additive. -/
theorem E_add (f g : W → ℝ) : m.E (f + g) = m.E f + m.E g := by
  simp only [E, Pi.add_apply, add_mul, sum_add_distrib]

/-- Expectation commutes with scaling. -/
theorem E_mul (a : ℝ) (f : W → ℝ) : m.E (fun w => a * f w) = a * m.E f := by
  simp only [E, mul_assoc, ← mul_sum]

/-- Expectation is 1-Lipschitz in the supremum norm: `|E f − E g| ≤ ‖f − g‖_∞`. This is the
triangle-inequality step in the proof of Proposition 1.3.1 (p. 34). -/
theorem abs_E_sub_E_le (f g : W → ℝ) : |m.E f - m.E g| ≤ ‖f - g‖ := by
  have hle : ∀ w, |f w - g w| ≤ ‖f - g‖ := fun w => by
    have := norm_le_pi_norm (f - g) w
    simpa [Real.norm_eq_abs] using this
  calc |m.E f - m.E g| = |∑ w, (f w - g w) * m.φ w| := by
        simp only [E, ← sum_sub_distrib, sub_mul]
    _ ≤ ∑ w, |(f w - g w) * m.φ w| := abs_sum_le_sum_abs _ _
    _ = ∑ w, |f w - g w| * m.φ w := by
        refine sum_congr rfl fun w _ => ?_
        rw [abs_mul, abs_of_nonneg (m.φ_nonneg w)]
    _ ≤ ∑ w, ‖f - g‖ * m.φ w :=
        sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (hle w) (m.φ_nonneg w)
    _ = ‖f - g‖ := by rw [← mul_sum, m.φ_sum, mul_one]

end Model

end SargentStachurski.JobSearch
