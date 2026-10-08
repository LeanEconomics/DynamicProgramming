/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Max, min and pointwise operations on functions

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.1.1 (p. 12),
Exercise 1.2.1 (p. 13), §1.2.4.1 (pp. 29–30), and the bound (1.28) with
Exercise 1.3.1 (p. 34) that the contraction proof for job search rests on.

The book writes `a ∨ b` for `max a b` and `a ∧ b` for `min a b`, and defines
`|a| := a ∨ (−a)`. Functions in `ℝ^X` are combined pointwise, (1.20)–(1.22).
In Lean these are Mathlib's `Pi` instances; the lemmas here record that they
compute as the book says.
-/

namespace SargentStachurski.JobSearch

/-- The book's definition of the absolute value, `|a| = a ∨ (−a)` (p. 12). -/
theorem abs_eq_max_neg' (a : ℝ) : |a| = max a (-a) := abs_eq_max_neg

/-- Exercise 1.2.1 (p. 13): `α ∨ (s + t) ≤ s + α ∨ t` whenever `s ≥ 0`. -/
theorem max_add_le_add_max {α s t : ℝ} (hs : 0 ≤ s) : max α (s + t) ≤ s + max α t := by
  rcases le_total α (s + t) with h | h
  · rw [max_eq_right h]
    linarith [le_max_right α t]
  · rw [max_eq_left h]
    calc α ≤ max α t := le_max_left _ _
      _ ≤ s + max α t := le_add_of_nonneg_left hs

/-- One half of (1.28), derived from Exercise 1.2.1 as the book's solution to
Exercise 1.3.1 does: `α ∨ x ≤ |x − y| + α ∨ y`. -/
theorem max_le_abs_sub_add_max (α x y : ℝ) : max α x ≤ |x - y| + max α y := by
  have hx : x ≤ |x - y| + y := by
    have := le_abs_self (x - y)
    linarith
  calc max α x ≤ max α (|x - y| + y) := max_le_max_left α hx
    _ ≤ |x - y| + max α y := max_add_le_add_max (abs_nonneg _)

/-- The bound (1.28), Exercise 1.3.1 (p. 34): `|α ∨ x − α ∨ y| ≤ |x − y|`. -/
theorem abs_max_sub_max_le (α x y : ℝ) : |max α x - max α y| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  constructor
  · have := max_le_abs_sub_add_max α x y
    linarith
  · have := max_le_abs_sub_add_max α y x
    rw [abs_sub_comm y x] at this
    linarith

/-- The `min` twin of (1.28): `|α ∧ x − α ∧ y| ≤ |x − y|`, used when the book takes a
minimum rather than a maximum (p. 12, `a ∧ b := min{a, b}`). -/
theorem abs_min_sub_min_le (α x y : ℝ) : |min α x - min α y| ≤ |x - y| := by
  have h := abs_max_sub_max_le (-α) (-x) (-y)
  rw [max_neg_neg, max_neg_neg, neg_sub_neg, neg_sub_neg, abs_sub_comm (min α y),
    abs_sub_comm y] at h
  exact h

/-- `x ↦ α ∨ x` is order preserving, the fact behind the greedy comparison in (1.29). -/
theorem max_le_max_of_le (α : ℝ) {x y : ℝ} (h : x ≤ y) : max α x ≤ max α y :=
  max_le_max_left α h

variable {X : Type*} (u v : X → ℝ) (α β : ℝ) (x : X)

/-- (1.20), p. 29: `(αu + βv)(x) = αu(x) + βv(x)`. -/
theorem smul_add_smul_apply : (α • u + β • v) x = α * u x + β * v x := by
  simp

/-- (1.20), p. 29: `(uv)(x) = u(x)v(x)`. -/
theorem mul_apply' : (u * v) x = u x * v x := rfl

/-- (1.21), p. 29: `|u|(x) = |u(x)|`. -/
theorem abs_apply' : |u| x = |u x| := rfl

/-- (1.21), p. 29: `(u ∨ v)(x) = u(x) ∨ v(x)`. -/
theorem sup_apply' : (u ⊔ v) x = max (u x) (v x) := rfl

/-- (1.21), p. 29: `(u ∧ v)(x) = u(x) ∧ v(x)`. -/
theorem inf_apply' : (u ⊓ v) x = min (u x) (v x) := rfl

end SargentStachurski.JobSearch
