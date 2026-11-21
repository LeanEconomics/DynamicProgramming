/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.PriceDuration

/-!
# The expected time between price changes

AKMM, §18.2, p. 534. Suppose a price changes with probability `1 − θ` each month,
independently of its history. The book writes the expected time between price adjustments as
`∑_{t ≥ 1} (1 − θ) θᵗ t = θ/(1 − θ)`.

The sum is computed correctly (`dur_printed_sum`), but its weights `(1 − θ) θᵗ` (`t ≥ 1`) add up
to `θ`, not to one (`dur_printed_weights_sum`), so it is not an expectation unless `θ = 1`. The
duration of a price (the number of months until the next change, counting the current one) is
`t ≥ 1` with probability `(1 − θ) θ^{t−1}`; its mean is `1/(1 − θ)` (`dur_mean`, from Galí's
`mean_duration`). The printed value `θ/(1 − θ)` is the expected number of months *without* a
change before the change, one less than the duration (`dur_printed_eq_mean_sub_one`), and it
differs from the mean duration (`dur_printed_ne_mean`).
-/

namespace AKMM.NominalFrictions

open Gali.BasicNewKeynesianModel

/-- AKMM, p. 534: the printed weights `(1 − θ)θᵗ`, `t ≥ 1`, sum to `θ` (not to one) for
`θ ∈ [0, 1)`. -/
theorem dur_printed_weights_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (1 - θ) * θ ^ (t + 1) = θ := by
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  simp_rw [pow_succ, ← mul_assoc, mul_comm _ θ]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp

/-- AKMM, p. 534: the printed weights do not form a probability distribution on `t ≥ 1`. -/
theorem dur_printed_weights_ne_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (1 - θ) * θ ^ (t + 1) ≠ 1 := by
  rw [dur_printed_weights_sum h0 h1]; exact ne_of_lt h1

/-- AKMM, p. 534: the printed sum itself is correct,
`∑_{t ≥ 1} (1 − θ) θᵗ t = θ/(1 − θ)` (indexing from `t = 0`, where the term vanishes). -/
theorem dur_printed_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (1 - θ) * θ ^ t * (t : ℝ) = θ / (1 - θ) := by
  have hn : ‖θ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  have hs : ∀ t : ℕ, (1 - θ) * θ ^ t * (t : ℝ) = (1 - θ) * ((t : ℝ) * θ ^ t) := by
    intro t; ring
  simp_rw [hs]
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hn]
  field_simp

/-- AKMM, p. 534 (corrected): with reset probability `1 − θ`, a price lasts `t + 1 ≥ 1`
periods with probability `(1 − θ)θᵗ`; these probabilities sum to one (Galí's
`survival_sum`). -/
theorem dur_pmf_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) : ∑' t, durationProb θ t = 1 :=
  survival_sum h0 h1

/-- AKMM, p. 534 (corrected): the expected duration of a price is `1/(1 − θ)` (Galí's
`mean_duration`). -/
theorem dur_mean {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, ((t : ℝ) + 1) * durationProb θ t = 1 / (1 - θ) :=
  mean_duration h0 h1

/-- AKMM, p. 534: the printed value `θ/(1 − θ)` is the expected number of periods without a
change, `∑ₜ t (1 − θ) θᵗ`, one less than the mean duration `1/(1 − θ)`. -/
theorem dur_printed_eq_mean_sub_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' t : ℕ, (t : ℝ) * durationProb θ t = θ / (1 - θ) ∧ θ / (1 - θ) = 1 / (1 - θ) - 1 := by
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  refine ⟨?_, by field_simp; ring⟩
  rw [← dur_printed_sum h0 h1]
  congr 1
  funext t
  unfold durationProb
  ring

/-- AKMM, p. 534: the printed value is not the mean duration. -/
theorem dur_printed_ne_mean {θ : ℝ} (h1 : θ < 1) : θ / (1 - θ) ≠ 1 / (1 - θ) := by
  have h : (0 : ℝ) < 1 - θ := by linarith
  intro he
  rw [div_left_inj' h.ne'] at he
  linarith

end AKMM.NominalFrictions
