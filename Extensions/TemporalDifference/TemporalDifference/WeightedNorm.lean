/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The stationary-distribution norm

Tsitsiklis and Van Roy (1997).

For a Markov matrix `P` on a finite state space with stationary distribution `d`, the weighted
norm `‖v‖_d² = ∑_x d(x)v(x)²` makes `P` nonexpansive (`dsq_applyP_le`), by Jensen's inequality
row by row (`jensen_sq`) and stationarity. So the Bellman operator `Tv = r + βPv` of a Markov
reward process is a `β`-contraction for `‖·‖_d` (`dsq_bellman_sub_le`), and
`⟨v, Pv⟩_d ≤ ‖v‖_d²` (`dinner_applyP_le`), the inequality behind the convergence of TD learning.
-/

open Finset

namespace DPExtensions.TemporalDifference

variable {X : Type*} [Fintype X]

/-- The squared weighted norm `‖v‖_d² = ∑_x d(x)v(x)²`. -/
def dsq (d v : X → ℝ) : ℝ := ∑ x, d x * v x ^ 2

/-- The weighted inner product `⟨v, w⟩_d = ∑_x d(x)v(x)w(x)`. -/
def dinner (d v w : X → ℝ) : ℝ := ∑ x, d x * v x * w x

/-- `(Pv)(x) = ∑_y P(x, y)v(y)`. -/
def applyP (P : X → X → ℝ) (v : X → ℝ) (x : X) : ℝ := ∑ y, P x y * v y

theorem dsq_nonneg {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (v : X → ℝ) : 0 ≤ dsq d v :=
  sum_nonneg fun x _ => mul_nonneg (hd x) (sq_nonneg _)

theorem dinner_self (d v : X → ℝ) : dinner d v v = dsq d v :=
  sum_congr rfl fun x _ => by ring

theorem dinner_comm (d v w : X → ℝ) : dinner d v w = dinner d w v :=
  sum_congr rfl fun x _ => by ring

theorem dsq_add (d v w : X → ℝ) :
    dsq d (fun x => v x + w x) = dsq d v + 2 * dinner d v w + dsq d w := by
  simp only [dsq, dinner, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => by ring

theorem dsq_smul (d v : X → ℝ) (c : ℝ) : dsq d (fun x => c * v x) = c ^ 2 * dsq d v := by
  simp only [dsq, mul_sum]
  exact sum_congr rfl fun x _ => by ring

theorem dinner_le {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (v w : X → ℝ) :
    2 * dinner d v w ≤ dsq d v + dsq d w := by
  simp only [dsq, dinner, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun x _ => ?_
  nlinarith [mul_nonneg (hd x) (sq_nonneg (v x - w x))]

/-- **Jensen's inequality for a probability row**: `(∑ p_y v_y)² ≤ ∑ p_y v_y²`. -/
theorem jensen_sq {p v : X → ℝ} (hp : ∀ y, 0 ≤ p y) (h1 : ∑ y, p y = 1) :
    (∑ y, p y * v y) ^ 2 ≤ ∑ y, p y * v y ^ 2 := by
  set m := ∑ y, p y * v y
  have h : 0 ≤ ∑ y, p y * (v y - m) ^ 2 := sum_nonneg fun y _ => mul_nonneg (hp y) (sq_nonneg _)
  have e : ∑ y, p y * (v y - m) ^ 2 = ∑ y, p y * v y ^ 2 - 2 * m * m + m ^ 2 * ∑ y, p y := by
    have hy : ∀ y, p y * (v y - m) ^ 2 = p y * v y ^ 2 - 2 * m * (p y * v y) + m ^ 2 * p y :=
      fun y => by ring
    simp only [hy, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rfl
  rw [e, h1] at h
  nlinarith

/-- **`P` is nonexpansive for `‖·‖_d`** when `d` is stationary. -/
theorem dsq_applyP_le {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (hstat : ∀ y, ∑ x, d x * P x y = d y) (v : X → ℝ) :
    dsq d (applyP P v) ≤ dsq d v := by
  calc dsq d (applyP P v) ≤ ∑ x, d x * ∑ y, P x y * v y ^ 2 :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (jensen_sq (hP0 x) (hP1 x)) (hd x)
    _ = dsq d v := by
        simp only [mul_sum, dsq]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => ?_
        rw [← hstat y, sum_mul]
        exact sum_congr rfl fun x _ => by ring

/-- `⟨v, Pv⟩_d ≤ ‖v‖_d²`. -/
theorem dinner_applyP_le {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y) (hP1 : ∀ x, ∑ y, P x y = 1)
    {d : X → ℝ} (hd : ∀ x, 0 ≤ d x) (hstat : ∀ y, ∑ x, d x * P x y = d y) (v : X → ℝ) :
    dinner d v (applyP P v) ≤ dsq d v := by
  linarith [dinner_le hd v (applyP P v), dsq_applyP_le hP0 hP1 hd hstat v]

/-- **The Bellman operator is a `β`-contraction for `‖·‖_d`**: with `Tv = r + βPv`,
`‖Tv − Tw‖_d² ≤ β²‖v − w‖_d²`. -/
theorem dsq_bellman_sub_le {P : X → X → ℝ} (hP0 : ∀ x y, 0 ≤ P x y)
    (hP1 : ∀ x, ∑ y, P x y = 1) {d : X → ℝ} (hd : ∀ x, 0 ≤ d x)
    (hstat : ∀ y, ∑ x, d x * P x y = d y) (r : X → ℝ) (β : ℝ) (v w : X → ℝ) :
    dsq d (fun x => (r x + β * applyP P v x) - (r x + β * applyP P w x)) ≤
      β ^ 2 * dsq d (fun x => v x - w x) := by
  have e : (fun x => (r x + β * applyP P v x) - (r x + β * applyP P w x)) =
      fun x => β * applyP P (fun y => v y - w y) x := by
    funext x
    simp only [applyP, mul_sub, sum_sub_distrib]
    ring
  rw [e, dsq_smul]
  exact mul_le_mul_of_nonneg_left (dsq_applyP_le hP0 hP1 hd hstat _) (sq_nonneg β)

end DPExtensions.TemporalDifference
