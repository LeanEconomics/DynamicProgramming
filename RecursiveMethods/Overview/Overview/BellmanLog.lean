/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.FiniteHorizon
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The infinite-horizon log/Cobb–Douglas economy

SLP Exercise 2.3, p. 14, and equations (8)–(11), pp. 12–14.

With `f(k) = k^α`, `U(c) = ln c`, the conjectured optimal policy is `k_{t+1} = αβ k_t^α` (8).

* `logCapital` (Ex 2.3a): along (8), `ln k_t = αᵗ ln k₀ + ln(αβ)(1 − αᵗ)/(1 − α)`.
* `hasSum_value` (Ex 2.3a): the lifetime utility of (8) from `k₀` is
  `v(k₀) = A + B ln k₀`, `B = α/(1 − αβ)`,
  `A = [ln(1 − αβ) + αβ ln(αβ)/(1 − αβ)]/(1 − β)`.
* `bellman_le`, `bellman_attained`, `bellman_isGreatest`, `bellman_argmax_unique` (Ex 2.3b): `v`
  satisfies the functional equation (11), `v(k) = max_{0 < y < k^α} {ln(k^α − y) + βv(y)}`, and
  `y = αβk^α` is the unique maximizer, recovering (8).
-/

open Finset Set Filter Topology Real

namespace StokeyLucasPrescott.Overview

/-- The coefficient `B = α/(1 − αβ)`. -/
noncomputable def coefB (α β : ℝ) : ℝ := α / (1 - α * β)

/-- The constant `A = [ln(1 − αβ) + αβ ln(αβ)/(1 − αβ)]/(1 − β)`. -/
noncomputable def coefA (α β : ℝ) : ℝ :=
  (log (1 - α * β) + α * β / (1 - α * β) * log (α * β)) / (1 - β)

/-- The value function `v(k) = A + B ln k`. -/
noncomputable def logValue (α β k : ℝ) : ℝ := coefA α β + coefB α β * log k

/-- The capital path (8): `k_{t+1} = αβ k_t^α`. -/
noncomputable def cdPath (α β k₀ : ℝ) : ℕ → ℝ
  | 0 => k₀
  | t + 1 => α * β * cdPath α β k₀ t ^ α

theorem cdPath_pos {α β k₀ : ℝ} (h0 : 0 < α * β) (hk₀ : 0 < k₀) (t : ℕ) : 0 < cdPath α β k₀ t := by
  induction t with
  | zero => exact hk₀
  | succ t ih => exact mul_pos h0 (rpow_pos_of_pos ih α)

/-- **Ex 2.3a.** Along (8), `ln k_t = αᵗ ln k₀ + ln(αβ)(1 − αᵗ)/(1 − α)`. -/
theorem logCapital {α β k₀ : ℝ} (hα1 : α < 1) (h0 : 0 < α * β) (hk₀ : 0 < k₀) (t : ℕ) :
    log (cdPath α β k₀ t) = α ^ t * log k₀ + log (α * β) * (1 - α ^ t) / (1 - α) := by
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  induction t with
  | zero => simp [cdPath]
  | succ t ih =>
    simp only [cdPath]
    rw [log_mul h0.ne' (rpow_pos_of_pos (cdPath_pos h0 hk₀ t) α).ne',
      log_rpow (cdPath_pos h0 hk₀ t), ih]
    field_simp
    ring

/-- Consumption along (8) is `(1 − αβ) k_t^α`. -/
theorem cdPath_consumption (α β k₀ : ℝ) (t : ℕ) :
    cdPath α β k₀ t ^ α - cdPath α β k₀ (t + 1) = (1 - α * β) * cdPath α β k₀ t ^ α := by
  simp only [cdPath]
  ring

/-- **Ex 2.3a.** The lifetime utility `∑ βᵗ ln c_t` of the path (8) from `k₀` is `v(k₀)`. -/
theorem hasSum_value {α β k₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hk₀ : 0 < k₀) :
    HasSum (fun t => β ^ t * log (cdPath α β k₀ t ^ α - cdPath α β k₀ (t + 1)))
      (logValue α β k₀) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1 : α * β < 1 := by nlinarith
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  have h1ab : (1 - α * β) ≠ 0 := (sub_pos.2 h1).ne'
  -- per-period utility as a combination of geometric terms
  have hterm : ∀ t, β ^ t * log (cdPath α β k₀ t ^ α - cdPath α β k₀ (t + 1)) =
      (log (1 - α * β) + α * log (α * β) / (1 - α)) * β ^ t +
        (α * log k₀ - α * log (α * β) / (1 - α)) * (α * β) ^ t := fun t => by
    rw [cdPath_consumption, log_mul (sub_pos.2 h1).ne'
      (rpow_pos_of_pos (cdPath_pos h0 hk₀ t) α).ne', log_rpow (cdPath_pos h0 hk₀ t),
      logCapital hα1 h0 hk₀ t, mul_pow]
    field_simp
    ring
  have hg1 := hasSum_geometric_of_lt_one hβ.le hβ1
  have hg2 := hasSum_geometric_of_lt_one h0.le h1
  have hs := (hg1.mul_left (log (1 - α * β) + α * log (α * β) / (1 - α))).add
    (hg2.mul_left (α * log k₀ - α * log (α * β) / (1 - α)))
  convert hs using 1
  · funext t
    exact hterm t
  · simp only [logValue, coefA, coefB]
    field_simp
    ring

/-- The objective on the right of (11): `ln(k^α − y) + β v(y)`. -/
noncomputable def bellmanRHS (α β k y : ℝ) : ℝ := log (k ^ α - y) + β * logValue α β y

/-- **Ex 2.3b (upper bound).** For every feasible `y ∈ (0, k^α)`,
`ln(k^α − y) + βv(y) ≤ v(k)`. -/
theorem bellman_le {α β k y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1)
    (hk : 0 < k) (hy : 0 < y) (hyk : y < k ^ α) :
    bellmanRHS α β k y ≤ logValue α β k := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  set cs := (1 - α * β) * k ^ α
  set ys := α * β * k ^ α
  have hcs : 0 < cs := mul_pos h1ab hK
  have hys : 0 < ys := mul_pos h0 hK
  -- tangent lines of ln at `cs` and `ys`
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyk)) (hasDerivAt_log hcs.ne')
  have t2 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (hasDerivAt_log hys.ne')
  have hB : 0 ≤ β * coefB α β := mul_nonneg hβ.le (div_nonneg hα.le h1ab.le)
  -- the value at the maximizer
  have hval : log cs + β * logValue α β ys = logValue α β k := by
    simp only [cs, ys, logValue, coefA, coefB]
    rw [log_mul h1ab.ne' hK.ne', log_mul h0.ne' hK.ne', log_rpow hk]
    have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
    field_simp
    ring
  -- the linear terms cancel by the first-order condition
  have hfoc : cs⁻¹ * (k ^ α - y - cs) + β * coefB α β * (ys⁻¹ * (y - ys)) = 0 := by
    simp only [cs, ys, coefB]
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left t2 hB
  unfold bellmanRHS
  rw [← hval]
  simp only [logValue] at this ⊢
  nlinarith

/-- **Ex 2.3b (attainment).** The policy `y = αβk^α` attains `v(k)`. -/
theorem bellman_attained {α β k : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1)
    (hk : 0 < k) : bellmanRHS α β k (α * β * k ^ α) = logValue α β k := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  unfold bellmanRHS
  rw [show k ^ α - α * β * k ^ α = (1 - α * β) * k ^ α by ring]
  simp only [logValue, coefA, coefB]
  rw [log_mul h1ab.ne' hK.ne', log_mul h0.ne' hK.ne', log_rpow hk]
  field_simp
  ring

/-- **Ex 2.3b.** `v` satisfies the functional equation (11):
`v(k) = max_{0 < y < k^α} {ln(k^α − y) + βv(y)}`. -/
theorem bellman_isGreatest {α β k : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1)
    (hk : 0 < k) :
    IsGreatest (bellmanRHS α β k '' Ioo 0 (k ^ α)) (logValue α β k) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  refine ⟨⟨α * β * k ^ α, ⟨mul_pos h0 hK, by nlinarith⟩,
    bellman_attained hα hβ hβ1 h1 hk⟩, ?_⟩
  rintro _ ⟨y, ⟨hy0, hyk⟩, rfl⟩
  exact bellman_le hα hβ hβ1 h1 hk hy0 hyk

/-- **The maximizer is unique**: any `y` attaining `v(k)` is `αβk^α`, so (11) generates the
policy (8). -/
theorem bellman_argmax_unique {α β k y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (h1 : α * β < 1) (hk : 0 < k) (hy : 0 < y) (hyk : y < k ^ α)
    (hmax : logValue α β k ≤ bellmanRHS α β k y) : y = α * β * k ^ α := by
  by_contra hne
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  set cs := (1 - α * β) * k ^ α
  set ys := α * β * k ^ α
  have hcs : 0 < cs := mul_pos h1ab hK
  have hys : 0 < ys := mul_pos h0 hK
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyk)) (hasDerivAt_log hcs.ne')
  have t2 := strictConcave_lt_tangent strictConcaveOn_log_Ioi (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (fun h => hne h.symm) (hasDerivAt_log hys.ne')
  have hB : 0 < β * coefB α β := mul_pos hβ (div_pos hα h1ab)
  have hval : log cs + β * logValue α β ys = logValue α β k := by
    simp only [cs, ys, logValue, coefA, coefB]
    rw [log_mul h1ab.ne' hK.ne', log_mul h0.ne' hK.ne', log_rpow hk]
    have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
    field_simp
    ring
  have hfoc : cs⁻¹ * (k ^ α - y - cs) + β * coefB α β * (ys⁻¹ * (y - ys)) = 0 := by
    simp only [cs, ys, coefB]
    field_simp
    ring
  have := mul_lt_mul_of_pos_left t2 hB
  unfold bellmanRHS at hmax
  rw [← hval] at hmax
  simp only [logValue] at this hmax
  nlinarith

end StokeyLucasPrescott.Overview
