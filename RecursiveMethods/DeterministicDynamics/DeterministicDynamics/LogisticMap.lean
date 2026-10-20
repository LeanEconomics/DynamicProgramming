/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Cycles of the logistic map

SLP Exercise 6.3, p. 139: `x_{t+1} = g(x_t) = 4x_t − 4x_t²`.

* **Exercise 6.3a** (`ex_6_3a`): `g` maps `[0, 1]` into itself, and its stationary points are
  `0` and `3/4`.
* **Exercise 6.3b**: `g²` at `0, 1/4, 1/2, 3/4, 1` (`ex_6_3b_values`). There is a two-cycle,
  `(5 − √5)/8 ↔ (5 + √5)/8` (`ex_6_3b_two_cycle`). There is a three-cycle,
  `sin²(π/7) → sin²(2π/7) → sin²(4π/7)` (`ex_6_3b_three_cycle`), because
  `g(sin²θ) = sin²(2θ)` (`logistic_sin_sq`).
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Set Real

/-- The logistic map `g(x) = 4x − 4x²`. -/
def logistic (x : ℝ) : ℝ := 4 * x - 4 * x ^ 2

/-- **Exercise 6.3a.** `g : [0, 1] → [0, 1]`, with stationary points `0` and `3/4`. -/
theorem ex_6_3a :
    MapsTo logistic (Icc 0 1) (Icc 0 1) ∧
      ∀ x, logistic x = x ↔ x = 0 ∨ x = 3 / 4 := by
  refine ⟨fun x hx => ⟨?_, ?_⟩, fun x => ?_⟩
  · simp only [logistic]; nlinarith [hx.1, hx.2]
  · simp only [logistic]; nlinarith [sq_nonneg (2 * x - 1)]
  · simp only [logistic]
    constructor
    · intro h
      have : x * (3 - 4 * x) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num

/-- **Exercise 6.3b.** `g²` at `x = 0, 1/4, 1/2, 3/4, 1`. -/
theorem ex_6_3b_values :
    logistic^[2] 0 = 0 ∧ logistic^[2] (1 / 4) = 3 / 4 ∧ logistic^[2] (1 / 2) = 0 ∧
      logistic^[2] (3 / 4) = 3 / 4 ∧ logistic^[2] 1 = 0 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, logistic]
  norm_num

/-- **Exercise 6.3b.** A two-cycle: `(5 − √5)/8 ↔ (5 + √5)/8`. -/
theorem ex_6_3b_two_cycle :
    ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ x ≠ y ∧ logistic x = y ∧ logistic y = x := by
  have h5 : sqrt 5 ^ 2 = 5 := sq_sqrt (by norm_num)
  have hs0 : 0 < sqrt 5 := sqrt_pos.2 (by norm_num)
  have hs3 : sqrt 5 < 3 := by nlinarith
  refine ⟨(5 - sqrt 5) / 8, (5 + sqrt 5) / 8, ⟨by linarith, by linarith⟩, ⟨by linarith,
    by linarith⟩, by intro h; linarith, ?_, ?_⟩ <;> simp only [logistic] <;> nlinarith

/-- `g(sin²θ) = sin²(2θ)`. -/
theorem logistic_sin_sq (θ : ℝ) : logistic (sin θ ^ 2) = sin (2 * θ) ^ 2 := by
  simp only [logistic, sin_two_mul]
  have := sin_sq_add_cos_sq θ
  nlinarith [this]

/-- **Exercise 6.3b.** A three-cycle: `sin²(π/7) → sin²(2π/7) → sin²(4π/7) → sin²(π/7)`, with
three distinct points. -/
theorem ex_6_3b_three_cycle :
    ∃ x y z : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ z ∈ Icc 0 1 ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      logistic x = y ∧ logistic y = z ∧ logistic z = x := by
  have hpi := pi_pos
  set x := sin (π / 7) ^ 2
  set y := sin (2 * (π / 7)) ^ 2
  set z := sin (2 * (2 * (π / 7))) ^ 2
  have hsq : ∀ θ : ℝ, sin θ ^ 2 ∈ Icc (0 : ℝ) 1 := fun θ =>
    ⟨sq_nonneg _, by rw [sin_sq]; linarith [sq_nonneg (cos θ)]⟩
  -- `sin(8π/7)² = sin(π/7)²`
  have h8 : sin (2 * (2 * (2 * (π / 7)))) ^ 2 = x := by
    have : 2 * (2 * (2 * (π / 7))) = π / 7 + π := by ring
    rw [this, sin_add_pi, neg_sq]
  -- `sin(4π/7) = sin(3π/7)`
  have h4 : sin (2 * (2 * (π / 7))) = sin (3 * (π / 7)) := by
    rw [← sin_pi_sub]; congr 1; ring
  -- `sin` rises on `(0, π/2)`
  have hlt : ∀ a b : ℝ, 0 < a → a < b → b ≤ π / 2 → sin a ^ 2 < sin b ^ 2 := fun a b ha hab hb =>
    by
      have h1 := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hb hab
      have h2 : 0 < sin a := sin_pos_of_pos_of_lt_pi ha (by linarith)
      nlinarith
  have hxy : x < y := hlt _ _ (by positivity) (by linarith) (by linarith)
  have hyz : y < z := by
    simp only [y, z, h4]
    exact hlt _ _ (by positivity) (by linarith) (by linarith)
  refine ⟨x, y, z, hsq _, hsq _, hsq _, hxy.ne, hyz.ne, (hxy.trans hyz).ne, logistic_sin_sq _,
    logistic_sin_sq _, ?_⟩
  rw [logistic_sin_sq, h8]

end StokeyLucasPrescott.DeterministicDynamics
