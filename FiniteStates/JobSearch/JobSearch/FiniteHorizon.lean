/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import JobSearch.Model

/-!
# Finite-horizon job search by backward induction

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.1.1 (pp. 3–10):
the two-period problem (1.2)–(1.4), the three-period problem (1.5), and
Exercises 1.1.2–1.1.3.

Backward induction is organised by the number `j` of periods remaining after
the current one. With `j = 0` the worker takes `max{c, w}`, (1.2); with
`j + 1` remaining the stopping value is `w(1 + β + ⋯ + β^{j+1})` and the
continuation value is `c + β E v_j(W')`, so `v_{j+1}(w)` is their maximum,
(1.3) and (1.5). The reservation wage `w*_{j+1}` is the continuation value
divided by `1 + β + ⋯ + β^{j+1}`, (1.4) and Exercise 1.1.2, and the worker
accepts iff the offer is at least the reservation wage. Exercise 1.1.3's
`T`-period extension is the general `j`.

The two-period model's `v₂, v₁, h₁, w₁*` are `value 0`, `value 1`,
`contValue 0`, `resWage 1`; the three-period `v₀, w₀*` are `value 2`,
`resWage 2`. The comparative static of p. 7, that higher compensation raises
the continuation value and the reservation wage, is proved for every horizon.
-/

open Finset

namespace SargentStachurski.JobSearch

namespace Model

variable {W : Type*} [Fintype W] (m : Model W)

/-- The discounted sum `1 + β + ⋯ + βʲ` of `j + 1` wage payments. -/
def annuity (j : ℕ) : ℝ := ∑ s ∈ range (j + 1), m.β ^ s

/-- The stopping value with `j` periods remaining after this one: the offer `w` paid now and
in each of the `j` remaining periods, `w(1 + β + ⋯ + βʲ)` (p. 4, p. 7). -/
def stopValue (j : ℕ) (w : W) : ℝ := m.wage w * m.annuity j

/-- The value functions by backward induction: `v` with `0` periods remaining is `max{c, w}`
(1.2); with `j + 1` remaining it is the larger of stopping and continuing, (1.3), (1.5). -/
noncomputable def value : ℕ → W → ℝ
  | 0 => fun w => max m.c (m.wage w)
  | j + 1 => fun w => max (m.stopValue (j + 1) w) (m.c + m.β * m.E (value j))

/-- The continuation value when `j + 1` periods remain: reject, receive `c`, and behave
optimally with `j` remaining: `c + β ∑ v_j(w') φ(w')`, (1.2). -/
noncomputable def contValue (j : ℕ) : ℝ := m.c + m.β * m.E (m.value j)

/-- The reservation wage: with no periods remaining it is `c`; with `j + 1` remaining it is the
continuation value divided by the annuity factor, (1.4) and Exercise 1.1.2. -/
noncomputable def resWage : ℕ → ℝ
  | 0 => m.c
  | j + 1 => m.contValue j / m.annuity (j + 1)

theorem annuity_pos (j : ℕ) : 0 < m.annuity j := by
  unfold annuity
  rw [sum_range_succ']
  have : 0 ≤ ∑ s ∈ range j, m.β ^ (s + 1) := sum_nonneg fun s _ => pow_nonneg m.β_nonneg _
  simp only [pow_zero]
  linarith

theorem annuity_zero : m.annuity 0 = 1 := by simp [annuity]

theorem annuity_one : m.annuity 1 = 1 + m.β := by simp [annuity, sum_range_succ]

theorem annuity_two : m.annuity 2 = 1 + m.β + m.β ^ 2 := by
  simp [annuity, sum_range_succ]

/-- (1.2), p. 4: the last-period value is `v₂(w) = max{c, w}`. -/
theorem value_zero (w : W) : m.value 0 w = max m.c (m.wage w) := rfl

/-- (1.2), p. 4: `h₁ = c + β ∑ v₂(w') φ(w')`. -/
theorem contValue_zero : m.contValue 0 = m.c + m.β * m.E (fun w => max m.c (m.wage w)) := rfl

/-- (1.3), p. 6: `v₁(w) = max{w + βw, h₁}`. -/
theorem value_one (w : W) : m.value 1 w = max (m.wage w + m.β * m.wage w) (m.contValue 0) := by
  change max (m.stopValue 1 w) (m.contValue 0) = _
  rw [stopValue, annuity_one]
  ring_nf

/-- (1.4), p. 6: the two-period reservation wage `w₁* = h₁/(1 + β)`. -/
theorem resWage_one : m.resWage 1 = m.contValue 0 / (1 + m.β) := by
  change m.contValue 0 / m.annuity 1 = _
  rw [annuity_one]

/-- (1.5), p. 7: `v₀(w) = max{w + βw + β²w, c + β ∑ v₁(w') φ(w')}`. -/
theorem value_two (w : W) :
    m.value 2 w = max (m.wage w + m.β * m.wage w + m.β ^ 2 * m.wage w) (m.contValue 1) := by
  change max (m.stopValue 2 w) (m.contValue 1) = _
  rw [stopValue, annuity_two]
  ring_nf

/-- Exercise 1.1.2, p. 10: the time-zero reservation wage `w₀* = h₀/(1 + β + β²)`. -/
theorem resWage_two : m.resWage 2 = m.contValue 1 / (1 + m.β + m.β ^ 2) := by
  change m.contValue 1 / m.annuity 2 = _
  rw [annuity_two]

/-- With `j + 1` periods remaining the value is the larger of stopping and continuing. -/
theorem value_succ (j : ℕ) (w : W) :
    m.value (j + 1) w = max (m.stopValue (j + 1) w) (m.contValue j) := rfl

/-- The optimal choice (p. 7, Exercise 1.1.3): stopping is at least as good as continuing iff the
offer is at least the reservation wage. -/
theorem contValue_le_stopValue_iff (j : ℕ) (w : W) :
    m.contValue j ≤ m.stopValue (j + 1) w ↔ m.resWage (j + 1) ≤ m.wage w := by
  change m.contValue j ≤ m.wage w * m.annuity (j + 1) ↔ m.contValue j / m.annuity (j + 1) ≤ _
  rw [div_le_iff₀ (m.annuity_pos (j + 1))]

/-- The value equals the stopping value iff the offer is at least the reservation wage: the
worker accepts. -/
theorem value_succ_eq_stopValue_iff (j : ℕ) (w : W) :
    m.value (j + 1) w = m.stopValue (j + 1) w ↔ m.resWage (j + 1) ≤ m.wage w := by
  rw [value_succ, max_eq_left_iff, contValue_le_stopValue_iff]

/-- The value equals the continuation value iff the offer is at most the reservation wage: the
worker rejects. -/
theorem value_succ_eq_contValue_iff (j : ℕ) (w : W) :
    m.value (j + 1) w = m.contValue j ↔ m.wage w ≤ m.resWage (j + 1) := by
  rw [value_succ, max_eq_right_iff]
  change m.wage w * m.annuity (j + 1) ≤ m.contValue j ↔ _ ≤ m.contValue j / m.annuity (j + 1)
  rw [le_div_iff₀ (m.annuity_pos (j + 1))]

/-- In the last period the worker accepts iff `w ≥ c = w*₀`. -/
theorem value_zero_eq_wage_iff (w : W) : m.value 0 w = m.wage w ↔ m.resWage 0 ≤ m.wage w := by
  change max m.c (m.wage w) = m.wage w ↔ m.c ≤ m.wage w
  exact max_eq_right_iff

/-- Values are bounded below by the compensation `c`. -/
theorem c_le_value (j : ℕ) (w : W) : m.c ≤ m.value j w := by
  induction j generalizing w with
  | zero => exact le_max_left _ _
  | succ j ih =>
    rw [value_succ]
    refine le_trans ?_ (le_max_right _ _)
    unfold contValue
    have : 0 ≤ m.E (m.value j) := m.E_nonneg fun w => m.c_pos.le.trans (ih w)
    nlinarith [m.β_pos]

/-- Values are nonnegative. -/
theorem value_nonneg (j : ℕ) (w : W) : 0 ≤ m.value j w := m.c_pos.le.trans (m.c_le_value j w)

/-- Reservation wages are positive. -/
theorem resWage_pos (j : ℕ) : 0 < m.resWage j := by
  cases j with
  | zero => exact m.c_pos
  | succ j =>
    change 0 < m.contValue j / m.annuity (j + 1)
    refine div_pos ?_ (m.annuity_pos _)
    unfold contValue
    have : 0 ≤ m.E (m.value j) := m.E_nonneg (m.value_nonneg j)
    nlinarith [m.β_pos, m.c_pos]

/-! ### Higher compensation raises the reservation wage (p. 7)

Two models that share wages, distribution and discount factor but differ in compensation.
-/

/-- Values are increasing in the compensation `c`, horizon by horizon. -/
theorem value_le_value_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) (j : ℕ) (w : W) : m.value j w ≤ m'.value j w := by
  induction j generalizing w with
  | zero =>
    change max m.c (m.wage w) ≤ max m'.c (m'.wage w)
    rw [hw]
    exact max_le_max_right _ hc
  | succ j ih =>
    rw [value_succ, value_succ]
    have hs : m.stopValue (j + 1) w = m'.stopValue (j + 1) w := by
      simp only [stopValue, annuity, hw, hβ]
    have hE : m.E (m.value j) ≤ m'.E (m'.value j) := by
      calc m.E (m.value j) ≤ m.E (m'.value j) := m.E_mono (ih)
        _ = m'.E (m'.value j) := by simp only [E, hφ]
    have hcont : m.contValue j ≤ m'.contValue j := by
      unfold contValue
      rw [hβ]
      nlinarith [m'.β_pos]
    rw [hs]
    exact max_le_max_left _ hcont

/-- The continuation value is increasing in `c` (p. 7: "higher unemployment compensation `c`
shifts up the continuation value `h₁`"). -/
theorem contValue_le_contValue_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) (j : ℕ) : m.contValue j ≤ m'.contValue j := by
  unfold contValue
  have hE : m.E (m.value j) ≤ m'.E (m'.value j) := by
    calc m.E (m.value j) ≤ m.E (m'.value j) :=
          m.E_mono (m.value_le_value_of_c_le m' hw hφ hβ hc j)
      _ = m'.E (m'.value j) := by simp only [E, hφ]
  rw [hβ]
  nlinarith [m'.β_pos]

/-- The reservation wage is increasing in `c` at every horizon (p. 7: "... and increases the
reservation wage"). -/
theorem resWage_le_resWage_of_c_le (m' : Model W) (hw : m.wage = m'.wage) (hφ : m.φ = m'.φ)
    (hβ : m.β = m'.β) (hc : m.c ≤ m'.c) (j : ℕ) : m.resWage j ≤ m'.resWage j := by
  cases j with
  | zero => exact hc
  | succ j =>
    change m.contValue j / m.annuity (j + 1) ≤ m'.contValue j / m'.annuity (j + 1)
    have ha : m.annuity (j + 1) = m'.annuity (j + 1) := by simp only [annuity, hβ]
    rw [ha]
    exact div_le_div_of_nonneg_right (m.contValue_le_contValue_of_c_le m' hw hφ hβ hc j)
      (m'.annuity_pos _).le

end Model

end SargentStachurski.JobSearch
