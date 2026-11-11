/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.InfiniteNGM
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Solving for the value function and the functional Euler equation

AKMM, §4.4.4–4.4.5, Examples 4.7–4.8, pp. 120–123. `u = log`, `f(k) = Ak^α`, `δ = 1`; choices
`k' ∈ (0, Ak^α)` (consumption and next capital positive, as the logarithm requires).

* `vfe_log_max`: `log(Y − k') + B log k'` is maximized over `(0, Y)` at `k' = BY/(1 + B)`.
* (4.23): `V₁(k) = log A + α log k`, attained at `k' = 0` (`eq_4_23`).
* `V₂(k) = a₂ + b₂ log k` with the book's `a₂`, `b₂ = α + α²β`, attained at
  `k' = αβAk^α/(1 + αβ)` (`example_4_7_V2`); in general `T` maps `a' + b' log k` to
  `a'' + α(1 + βb') log k` (`example_4_7_iterate`), so `b_n = α(1 − (αβ)ⁿ)/(1 − αβ) → b`
  (`example_4_7_coefficients`).
* Guess and verify: `V = a + b log k` with `b = α/(1 − αβ)` and the printed `a` solves the
  Bellman equation, with policy `k' = αβAk^α` (`example_4_7`).
* (4.25): the first-order condition and the envelope condition give the functional Euler
  equation (`eq_4_25`); Example 4.8: `g(k) = sAk^α` solves it iff `s = αβ` (`example_4_8`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- AKMM, p. 121: for `Y > 0`, `B > 0`, `log(Y − k') + B log k'` is maximized over `(0, Y)` at
`k' = BY/(1 + B)` (the first-order condition `1/(Y − k') = B/k'`). -/
theorem vfe_log_max {Y B : ℝ} (hY : 0 < Y) (hB : 0 < B) {k' : ℝ} (hk0 : 0 < k') (hk1 : k' < Y) :
    Real.log (Y - k') + B * Real.log k' ≤
      Real.log (Y - B * Y / (1 + B)) + B * Real.log (B * Y / (1 + B)) := by
  set ks := B * Y / (1 + B)
  have hks : 0 < ks := by positivity
  have hY' : Y - ks = Y / (1 + B) := by simp only [ks]; field_simp; ring
  have hYks : 0 < Y - ks := by rw [hY']; positivity
  have h1 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.2 hk1) hYks)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hk0 hks)
  rw [Real.log_div (sub_pos.2 hk1).ne' hYks.ne'] at h1
  rw [Real.log_div hk0.ne' hks.ne'] at h2
  have e : (Y - k') / (Y - ks) - 1 + B * (k' / ks - 1) = 0 := by
    rw [hY']; simp only [ks]; field_simp; ring
  nlinarith

/-- **AKMM, (4.23), p. 121.** `V₁(k) = max_{k' ≥ 0} log(Ak^α − k') = log A + α log k`, attained at
`k' = 0`. -/
theorem eq_4_23 {A α k : ℝ} (hA : 0 < A) (hk : 0 < k) :
    (∀ k' ∈ Set.Ico 0 (A * k ^ α), Real.log (A * k ^ α - k') ≤ Real.log (A * k ^ α - 0)) ∧
      Real.log (A * k ^ α - 0) = Real.log A + α * Real.log k := by
  have hP : 0 < A * k ^ α := mul_pos hA (rpow_pos_of_pos hk α)
  refine ⟨fun k' hk' => Real.log_le_log (by linarith [hk'.2]) (by linarith [hk'.1]), ?_⟩
  rw [sub_zero, Real.log_mul hA.ne' (rpow_pos_of_pos hk α).ne', Real.log_rpow hk]

/-- **AKMM, Example 4.7, p. 121: one Bellman step on `a' + b' log k`.** For `b' > 0`,
`max_{0<k'<Ak^α} {log(Ak^α − k') + β(a' + b' log k')}` is attained at
`k' = βb'Ak^α/(1 + βb')`, with value `a'' + α(1 + βb') log k`, where
`a'' = log(A − βb'A/(1 + βb')) + βa' + βb' log(βb'A/(1 + βb'))`. -/
theorem example_4_7_iterate {A α β a' b' k : ℝ} (hA : 0 < A) (hβ : 0 < β) (hb : 0 < b')
    (hk : 0 < k) :
    (∀ k' ∈ Set.Ioo 0 (A * k ^ α), Real.log (A * k ^ α - k') + β * (a' + b' * Real.log k') ≤
      Real.log (A * k ^ α - β * b' * (A * k ^ α) / (1 + β * b')) +
        β * (a' + b' * Real.log (β * b' * (A * k ^ α) / (1 + β * b')))) ∧
    Real.log (A * k ^ α - β * b' * (A * k ^ α) / (1 + β * b')) +
        β * (a' + b' * Real.log (β * b' * (A * k ^ α) / (1 + β * b'))) =
      (Real.log (A - β * b' * A / (1 + β * b')) + β * a' +
        β * b' * Real.log (β * b' * A / (1 + β * b'))) + α * (1 + β * b') * Real.log k := by
  have hB : 0 < β * b' := mul_pos hβ hb
  have hP : 0 < k ^ α := rpow_pos_of_pos hk α
  have hY : 0 < A * k ^ α := mul_pos hA hP
  refine ⟨fun k' hk' => ?_, ?_⟩
  · have := vfe_log_max hY hB hk'.1 hk'.2
    nlinarith
  · have hc : 0 < A - β * b' * A / (1 + β * b') := by
      rw [show A - β * b' * A / (1 + β * b') = A / (1 + β * b') by field_simp; ring]
      positivity
    have hd : 0 < β * b' * A / (1 + β * b') := by positivity
    rw [show A * k ^ α - β * b' * (A * k ^ α) / (1 + β * b') =
        (A - β * b' * A / (1 + β * b')) * k ^ α by ring,
      show β * b' * (A * k ^ α) / (1 + β * b') = β * b' * A / (1 + β * b') * k ^ α by ring,
      Real.log_mul hc.ne' hP.ne', Real.log_mul hd.ne' hP.ne', Real.log_rpow hk]
    ring

/-- **AKMM, Example 4.7, p. 121: `V₂`.** With `V₁ = log A + α log k`, the second iterate is
`V₂(k) = a₂ + b₂ log k`, `a₂ = log(A − αβA/(1 + αβ)) + β log A + αβ log(αβA/(1 + αβ))`,
`b₂ = α + α²β`, attained at `k' = αβAk^α/(1 + αβ)`. -/
theorem example_4_7_V2 {A α β k : ℝ} (hA : 0 < A) (hα : 0 < α) (hβ : 0 < β) (hk : 0 < k) :
    (∀ k' ∈ Set.Ioo 0 (A * k ^ α), Real.log (A * k ^ α - k') + β * (Real.log A + α * Real.log k') ≤
      Real.log (A * k ^ α - α * β * A * k ^ α / (1 + α * β)) +
        β * (Real.log A + α * Real.log (α * β * A * k ^ α / (1 + α * β)))) ∧
    Real.log (A * k ^ α - α * β * A * k ^ α / (1 + α * β)) +
        β * (Real.log A + α * Real.log (α * β * A * k ^ α / (1 + α * β))) =
      (Real.log (A - α * β * A / (1 + α * β)) + β * Real.log A +
        α * β * Real.log (α * β * A / (1 + α * β))) + (α + α ^ 2 * β) * Real.log k := by
  obtain ⟨h1, h2⟩ := example_4_7_iterate (a' := Real.log A) hA hβ hα hk
  have e1 : β * α * (A * k ^ α) / (1 + β * α) = α * β * A * k ^ α / (1 + α * β) := by ring
  have e2 : β * α * A / (1 + β * α) = α * β * A / (1 + α * β) := by ring
  rw [e1] at h1 h2
  rw [e2] at h2
  refine ⟨h1, ?_⟩
  rw [h2]
  ring

/-- AKMM, Example 4.7, p. 121: the coefficients `b_n = α(1 − (αβ)ⁿ)/(1 − αβ)` of
`V_n = a_n + b_n log k` start at `b₁ = α`, `b₂ = α + α²β`, satisfy `b_{n+1} = α(1 + βb_n)`, and
converge to `b = α/(1 − αβ)`. -/
theorem example_4_7_coefficients {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (α * (1 - (α * β) ^ 1) / (1 - α * β) = α) ∧
    (α * (1 - (α * β) ^ 2) / (1 - α * β) = α + α ^ 2 * β) ∧
    (∀ n : ℕ, α * (1 - (α * β) ^ (n + 1)) / (1 - α * β) =
      α * (1 + β * (α * (1 - (α * β) ^ n) / (1 - α * β)))) ∧
    Filter.Tendsto (fun n : ℕ => α * (1 - (α * β) ^ n) / (1 - α * β)) Filter.atTop
      (nhds (α / (1 - α * β))) := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  have hne : (1 - α * β) ≠ 0 := by linarith
  refine ⟨by rw [div_eq_iff hne]; ring, by rw [div_eq_iff hne]; ring, fun n => ?_, ?_⟩
  · have hne' : 1 - β * α ≠ 0 := by rw [mul_comm]; exact hne
    field_simp
    ring
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_sub 1).const_mul α
  simpa using this.div_const (1 - α * β)

/-- **Example 4.7** (AKMM, p. 121): guess and verify. With `b = α/(1 − αβ)` and
`a = (1/(1 − β))(1/(1 − αβ))(log A + (1 − αβ) log(1 − αβ) + αβ log(αβ))`, `V(k) = a + b log k`
solves the Bellman equation `V(k) = max_{0<k'<Ak^α} {log(Ak^α − k') + βV(k')}`, and the maximum is
attained at `k' = αβAk^α`, the policy of the sequential approach. -/
theorem example_4_7 {A α β k : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hk : 0 < k) :
    (∀ k' ∈ Set.Ioo 0 (A * k ^ α), Real.log (A * k ^ α - k') +
        β * ((1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) *
          Real.log (1 - α * β) + α * β * Real.log (α * β)) +
          α / (1 - α * β) * Real.log k') ≤
      (1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) * Real.log (1 - α * β) +
        α * β * Real.log (α * β)) + α / (1 - α * β) * Real.log k) ∧
    Real.log (A * k ^ α - α * β * A * k ^ α) +
        β * ((1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) *
          Real.log (1 - α * β) + α * β * Real.log (α * β)) +
          α / (1 - α * β) * Real.log (α * β * A * k ^ α)) =
      (1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) * Real.log (1 - α * β) +
        α * β * Real.log (α * β)) + α / (1 - α * β) * Real.log k := by
  have hq0 : 0 < α * β := mul_pos hα0 hβ0
  have hq1 : α * β < 1 := by nlinarith
  have h1q : 0 < 1 - α * β := by linarith
  set a := (1 / (1 - β)) * (1 / (1 - α * β)) * (Real.log A + (1 - α * β) *
    Real.log (1 - α * β) + α * β * Real.log (α * β))
  set b := α / (1 - α * β)
  have hb : 0 < b := div_pos hα0 h1q
  have hβb : β * b / (1 + β * b) = α * β := by
    have hne' : 1 - β * α ≠ 0 := by nlinarith
    rw [div_eq_iff (by positivity)]
    simp only [b]
    field_simp
    ring
  have hP : 0 < k ^ α := rpow_pos_of_pos hk α
  have hpol : β * b * (A * k ^ α) / (1 + β * b) = α * β * A * k ^ α := by
    rw [show β * b * (A * k ^ α) / (1 + β * b) = β * b / (1 + β * b) * (A * k ^ α) by ring,
      hβb]; ring
  have hval : Real.log (A * k ^ α - α * β * A * k ^ α) +
      β * (a + b * Real.log (α * β * A * k ^ α)) = a + b * Real.log k := by
    rw [show A * k ^ α - α * β * A * k ^ α = (1 - α * β) * A * k ^ α by ring,
      Real.log_mul (mul_pos h1q hA).ne' hP.ne', Real.log_mul h1q.ne' hA.ne',
      show α * β * A * k ^ α = (α * β) * A * k ^ α by ring,
      Real.log_mul (mul_pos hq0 hA).ne' hP.ne', Real.log_mul hq0.ne' hA.ne', Real.log_rpow hk]
    simp only [a, b]
    have h1β : (1 - β) ≠ 0 := by linarith
    field_simp
    ring
  obtain ⟨h1, -⟩ := example_4_7_iterate (a' := a) hA hβ0 hb hk
  rw [hpol] at h1
  exact ⟨fun k' hk' => (h1 k' hk').trans_eq hval, hval⟩

/-- **AKMM, (4.25), p. 122: the functional Euler equation.** If the policy satisfies the
first-order condition `F₂(x, g(x)) + βV'(g(x)) = 0` and the envelope condition
`V'(x) = F₁(x, g(x))` (`property_4`) for all `x`, then
`F₂(x, g(x)) + βF₁(g(x), g(g(x))) = 0` for all `x`. -/
theorem eq_4_25 {g V' : ℝ → ℝ} {F1 F2 : ℝ → ℝ → ℝ} {β : ℝ}
    (hfoc : ∀ x, F2 x (g x) + β * V' (g x) = 0) (henv : ∀ x, V' x = F1 x (g x)) (x : ℝ) :
    F2 x (g x) + β * F1 (g x) (g (g x)) = 0 := by
  rw [← henv]; exact hfoc x

/-- **Example 4.8** (AKMM, p. 123). With `F(k, k') = log(Ak^α − k')`,
`F₁ = αAk^{α−1}/(Ak^α − k')` and `F₂ = −1/(Ak^α − k')`, the guess `g(k) = sAk^α`, `0 < s < 1`,
solves the functional Euler equation (4.25) at `k > 0` iff `s = αβ` (Example 4.6, with
`g(g(k)) = sA(sAk^α)^α`). -/
theorem example_4_8 {A α β s k : ℝ} (hA : 0 < A) (hα0 : 0 < α) (hβ0 : 0 < β) (hs0 : 0 < s)
    (hs1 : s < 1) (hk : 0 < k) :
    -(1 / (A * k ^ α - s * A * k ^ α)) +
        β * (α * A * (s * A * k ^ α) ^ (α - 1) /
          (A * (s * A * k ^ α) ^ α - s * A * (s * A * k ^ α) ^ α)) = 0 ↔ s = α * β := by
  rw [← example_4_6 hA hα0 hβ0 hs0 hs1 hk]
  constructor <;> intro h
  · rw [mul_div_assoc] at *; linarith
  · rw [h]; ring

end AKMM.DynamicOptimization
