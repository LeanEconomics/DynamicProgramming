/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The discrete-time lifetime budget and the no-Ponzi-game condition

AKMM, §9.2 (pp. 245–246, (9.15)) and Appendix 9.A.3, discrete part (p. 844).

With `a_{t+1} = w_t + (1 + r_t)a_t − c_t` and the discount factor `D_s = ∏_{t=1}^s (1 + r_t)`:

* the telescoped lifetime budget
  `a_{T+1}/D_T = Σ_{s≤T} w_s/D_s + (1 + r_0)a_0 − Σ_{s≤T} c_s/D_s`
  (`appendix_9A3_discrete_budget`);
* the no-Ponzi-game condition `a_{T+1}/D_T ≥ 0` gives the lifetime budget constraint, finite
  and infinite horizon, and in the limit the two are equivalent (`appendix_9A3_discrete_lbc`,
  `appendix_9A3_discrete_lbc_infinite`, `appendix_9A3_discrete_npg_iff_lbc`);
* with a constant rate `D_s = (1 + r)^s` (`discreteBudget_const_discount`);
* p. 246: in the finite horizon `a_{T+1}/(1 + r)^T ≥ 0 ⇔ a_{T+1} ≥ 0`, but in the infinite
  horizon `lim a_{T+1}/(1 + r)^T ≥ 0` does not imply `lim a_{T+1} ≥ 0`. The book's example
  `a_t = a > 0` satisfies both conditions; the counterexample is `a_t = a < 0` with `r > 0`,
  debt rolled over forever (`discreteBudget_npg_printed_example`,
  `discreteBudget_npg_counterexample`).
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, Appendix 9.A.3, p. 844: the discount factor `D_s = ∏_{t=1}^s (1 + r_t)`. -/
noncomputable def discreteDiscount (r : ℕ → ℝ) (s : ℕ) : ℝ :=
  ∏ i ∈ Finset.range s, (1 + r (i + 1))

/-- The discount factor is positive when every gross rate is positive. -/
theorem discreteBudget_discount_pos {r : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) (s : ℕ) :
    0 < discreteDiscount r s :=
  Finset.prod_pos fun i _ => hr (i + 1)

/-- AKMM, Appendix 9.A.3, p. 844: with a constant rate, `D_s = (1 + r)^s`. -/
theorem discreteBudget_const_discount (r : ℝ) (s : ℕ) :
    discreteDiscount (fun _ => r) s = (1 + r) ^ s := by
  simp [discreteDiscount]

/-- AKMM, Appendix 9.A.3, p. 844: dividing `a_{t+1} = w_t + (1 + r_t)a_t − c_t` by `D_t` and
summing from `0` to `T` gives
`a_{T+1}/D_T = Σ_{s≤T} w_s/D_s + (1 + r_0)a_0 − Σ_{s≤T} c_s/D_s`. -/
theorem appendix_9A3_discrete_budget {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t) (T : ℕ) :
    a (T + 1) / discreteDiscount r T =
      ∑ s ∈ Finset.range (T + 1), w s / discreteDiscount r s + (1 + r 0) * a 0 -
        ∑ s ∈ Finset.range (T + 1), c s / discreteDiscount r s := by
  induction T with
  | zero => simp [discreteDiscount, hb 0]
  | succ T ih =>
    have hD := discreteBudget_discount_pos hr T
    have hsucc : discreteDiscount r (T + 1) = discreteDiscount r T * (1 + r (T + 1)) :=
      Finset.prod_range_succ _ _
    rw [Finset.sum_range_succ (fun s => w s / discreteDiscount r s) (T + 1),
      Finset.sum_range_succ (fun s => c s / discreteDiscount r s) (T + 1), hsucc, hb (T + 1)]
    have h1 := hr (T + 1)
    have key : (w (T + 1) + (1 + r (T + 1)) * a (T + 1) - c (T + 1)) /
        (discreteDiscount r T * (1 + r (T + 1))) =
        a (T + 1) / discreteDiscount r T + w (T + 1) / (discreteDiscount r T * (1 + r (T + 1)))
          - c (T + 1) / (discreteDiscount r T * (1 + r (T + 1))) := by
      field_simp
      ring
    rw [key, ih]
    ring

/-- AKMM, Appendix 9.A.3, p. 844: the finite-horizon no-Ponzi condition `a_{T+1}/D_T ≥ 0`
guarantees the lifetime budget constraint
`Σ_{s≤T} c_s/D_s ≤ Σ_{s≤T} w_s/D_s + (1 + r_0)a_0`, and conversely. -/
theorem appendix_9A3_discrete_lbc {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t) (T : ℕ) :
    0 ≤ a (T + 1) / discreteDiscount r T ↔
      ∑ s ∈ Finset.range (T + 1), c s / discreteDiscount r s ≤
        ∑ s ∈ Finset.range (T + 1), w s / discreteDiscount r s + (1 + r 0) * a 0 := by
  rw [appendix_9A3_discrete_budget hr hb T]
  constructor <;> intro h <;> linarith

/-- AKMM, Appendix 9.A.3, p. 844, the limit `T → ∞`: if the discounted wage and consumption
series converge, the discounted terminal asset converges to
`Σ w_s/D_s + (1 + r_0)a_0 − Σ c_s/D_s`. -/
theorem appendix_9A3_discrete_limit {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t)
    (hw : Summable fun s => w s / discreteDiscount r s)
    (hc : Summable fun s => c s / discreteDiscount r s) :
    Tendsto (fun T => a (T + 1) / discreteDiscount r T) atTop
      (𝓝 (∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0 -
        ∑' s, c s / discreteDiscount r s)) := by
  have hW := (hw.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hC := (hc.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h := (hW.add_const ((1 + r 0) * a 0)).sub hC
  refine h.congr fun T => ?_
  simp only [Function.comp]
  rw [appendix_9A3_discrete_budget hr hb T]

/-- AKMM, Appendix 9.A.3, p. 844: the infinite-horizon no-Ponzi condition
`lim a_{T+1}/D_T ≥ 0` guarantees the lifetime budget constraint
`Σ c_s/D_s ≤ Σ w_s/D_s + (1 + r_0)a_0`. -/
theorem appendix_9A3_discrete_lbc_infinite {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t)
    (hw : Summable fun s => w s / discreteDiscount r s)
    (hc : Summable fun s => c s / discreteDiscount r s) {L : ℝ}
    (hL : Tendsto (fun T => a (T + 1) / discreteDiscount r T) atTop (𝓝 L)) (hnpg : 0 ≤ L) :
    ∑' s, c s / discreteDiscount r s ≤ ∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0 := by
  have h := tendsto_nhds_unique hL (appendix_9A3_discrete_limit hr hb hw hc)
  linarith

/-- AKMM, Appendix 9.A.3, p. 844: in the limit the no-Ponzi condition and the lifetime budget
constraint are equivalent, and the lifetime budget holds with equality iff the discounted
terminal asset tends to zero. -/
theorem appendix_9A3_discrete_npg_iff_lbc {r w c a : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hb : ∀ t, a (t + 1) = w t + (1 + r t) * a t - c t)
    (hw : Summable fun s => w s / discreteDiscount r s)
    (hc : Summable fun s => c s / discreteDiscount r s) :
    ∃ L, Tendsto (fun T => a (T + 1) / discreteDiscount r T) atTop (𝓝 L) ∧
      (0 ≤ L ↔ ∑' s, c s / discreteDiscount r s ≤
        ∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0) ∧
      (L = 0 ↔ ∑' s, c s / discreteDiscount r s =
        ∑' s, w s / discreteDiscount r s + (1 + r 0) * a 0) := by
  refine ⟨_, appendix_9A3_discrete_limit hr hb hw hc, ?_, ?_⟩ <;>
    constructor <;> intro h <;> linarith

/-- AKMM, p. 246: in the finite horizon `a_{T+1}/(1 + r)^T ≥ 0` is equivalent to `a_{T+1} ≥ 0`,
because `(1 + r)^T > 0`. -/
theorem discreteBudget_finite_npg_iff {r x : ℝ} (hr : 0 < 1 + r) (T : ℕ) :
    0 ≤ x / (1 + r) ^ T ↔ 0 ≤ x :=
  div_nonneg_iff.trans ⟨fun h => h.elim (fun h => h.1) fun h => absurd h.2
    (not_le.mpr (pow_pos hr T)), fun h => Or.inl ⟨h, (pow_pos hr T).le⟩⟩

/-- AKMM, p. 246, the printed example: a constant positive asset `a_t = a > 0` satisfies both
`lim a_{T+1}/(1 + r)^T ≥ 0` and `lim a_{T+1} ≥ 0` (for `r > 0`), so it does not separate them,
contrary to the text. -/
theorem discreteBudget_npg_printed_example {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    Tendsto (fun T : ℕ => a / (1 + r) ^ T) atTop (𝓝 0) ∧
      Tendsto (fun _ : ℕ => a) atTop (𝓝 a) ∧ 0 ≤ (0 : ℝ) ∧ 0 ≤ a := by
  refine ⟨?_, tendsto_const_nhds, le_rfl, ha.le⟩
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 + r)⁻¹) (by positivity)
    (inv_lt_one_of_one_lt₀ (by linarith))).const_mul a
  simpa [div_eq_mul_inv, inv_pow] using h

/-- AKMM, p. 246, the corrected counterexample: with `r > 0`, the constant debt `a_t = a < 0`
(consumption `c_t = w + ra`, so the budget holds) satisfies the no-Ponzi condition
`lim a_{T+1}/(1 + r)^T = 0 ≥ 0` but violates `lim a_{T+1} ≥ 0`. -/
theorem discreteBudget_npg_counterexample {r a w : ℝ} (hr : 0 < r) (ha : a < 0) :
    (∀ t : ℕ, (fun _ : ℕ => a) (t + 1) =
      w + (1 + r) * (fun _ : ℕ => a) t - (fun _ : ℕ => w + r * a) t) ∧
      Tendsto (fun T : ℕ => a / (1 + r) ^ T) atTop (𝓝 0) ∧
      Tendsto (fun _ : ℕ => a) atTop (𝓝 a) ∧ ¬ 0 ≤ a := by
  refine ⟨fun t => by ring, ?_, tendsto_const_nhds, not_le.mpr ha⟩
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 + r)⁻¹) (by positivity)
    (inv_lt_one_of_one_lt₀ (by linarith))).const_mul a
  simpa [div_eq_mul_inv, inv_pow] using h

end AKMM.ContinuousTime
