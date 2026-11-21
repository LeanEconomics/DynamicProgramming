/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.SecretaryBellman
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The secretary problem for many candidates: `τ(N)/N → 1/e`

Miao, p. 186: "for `N` sufficiently large, `1 ≃ 1/τ(N) + ⋯ + 1/(N − 1) ≃ ∫_{τ(N)}^N dx/x`, thus
`τ(N)/N ≃ 1/e ≃ 0.368`." Made precise:

* `sec_log_le_H`, `sec_H_le_log`: `ln(N/t) ≤ 1/t + ⋯ + 1/(N − 1) ≤ ln((N − 1)/(t − 1))`
  (the integral comparison, via `ln(1 + x) ≤ x`).
* `sec_tau_bounds`: `1/e < τ(N)/N ≤ 1/e + 2/N` for every `N ≥ 1`, with τ as in (6.43).
* `sec_tau_limit`: **`τ(N)/N → 1/e`** as `N → ∞`; and `0.3678 < 1/e < 0.3679`
  (`sec_inv_e_approx`), the book's 36.8%.
-/

namespace Miao.FiniteHorizonDP

open Filter Topology

theorem sec_H_succ_top {N t : ℕ} (h : t ≤ N) : sec_H (N + 1) t = sec_H N t + 1 / (N : ℝ) := by
  unfold sec_H
  rw [Finset.sum_Ico_succ_top h]

/-- `ln(N/t) ≤ 1/t + ⋯ + 1/(N − 1)` for `1 ≤ t ≤ N`. -/
theorem sec_log_le_H {t : ℕ} (ht : 1 ≤ t) : ∀ N, t ≤ N → Real.log ((N : ℝ) / t) ≤ sec_H N t := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le hN with h | h
    · rw [← h, sec_H_self, div_self ht0.ne', Real.log_one]
    · have hN' : t ≤ N := by omega
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      rw [sec_H_succ_top hN']
      have hsplit : Real.log (((N + 1 : ℕ) : ℝ) / t) =
          Real.log ((N : ℝ) / t) + Real.log (((N : ℝ) + 1) / N) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        push_cast
        field_simp
      have hstep : Real.log (((N : ℝ) + 1) / N) ≤ 1 / N := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
        have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
        linarith
      rw [hsplit]
      linarith [ih hN']

/-- `1/t + ⋯ + 1/(N − 1) ≤ ln((N − 1)/(t − 1))` for `2 ≤ t ≤ N`. -/
theorem sec_H_le_log {t : ℕ} (ht : 2 ≤ t) :
    ∀ N, t ≤ N → sec_H N t ≤ Real.log (((N : ℝ) - 1) / ((t : ℝ) - 1)) := by
  have ht1 : (0 : ℝ) < (t : ℝ) - 1 := by
    have : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le hN with h | h
    · rw [← h, sec_H_self, div_self ht1.ne', Real.log_one]
    · have hN' : t ≤ N := by omega
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
        linarith
      have hNpos : (0 : ℝ) < N := by linarith
      rw [sec_H_succ_top hN']
      have hsplit : Real.log ((((N + 1 : ℕ) : ℝ) - 1) / ((t : ℝ) - 1)) =
          Real.log (((N : ℝ) - 1) / ((t : ℝ) - 1)) + Real.log ((N : ℝ) / ((N : ℝ) - 1)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        push_cast
        field_simp
        ring
      have hstep : 1 / (N : ℝ) ≤ Real.log ((N : ℝ) / ((N : ℝ) - 1)) := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) - 1) / N by positivity)
        have e : ((N : ℝ) - 1) / N - 1 = -(1 / N) := by field_simp; ring
        have e2 : Real.log ((N : ℝ) / ((N : ℝ) - 1)) = -Real.log (((N : ℝ) - 1) / N) := by
          rw [← Real.log_inv, inv_div]
        rw [e2]
        linarith
      rw [hsplit]
      linarith [ih hN']

/-- **Bounds on τ(N)/N**: `1/e < τ(N)/N ≤ 1/e + 2/N` for `N ≥ 1`, with τ as in (6.43). -/
theorem sec_tau_bounds {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (-1) < (sec_tau N : ℝ) / N ∧ (sec_tau N : ℝ) / N ≤ Real.exp (-1) + 2 / N := by
  obtain ⟨hτ1, hτH, hτN⟩ := sec_tau_spec hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hτpos : (0 : ℝ) < sec_tau N := by exact_mod_cast hτ1
  refine ⟨?_, ?_⟩
  · have h1 := sec_log_le_H hτ1 N hτN
    have h2 : Real.log ((N : ℝ) / sec_tau N) < 1 := lt_of_le_of_lt h1 hτH
    have h3 : (N : ℝ) / sec_tau N < Real.exp 1 :=
      (Real.log_lt_iff_lt_exp (by positivity)).1 h2
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by positivity), inv_div]
    exact h3
  · have he := Real.exp_pos (-1)
    rcases Nat.lt_or_ge (sec_tau N) 3 with h | h
    · have : (sec_tau N : ℝ) ≤ 2 := by exact_mod_cast (show sec_tau N ≤ 2 by omega)
      have : (sec_tau N : ℝ) / N ≤ 2 / N := div_le_div_of_nonneg_right this hNpos.le
      linarith
    · set m := sec_tau N - 1 with hm
      have hm2 : 2 ≤ m := by omega
      have hHm : 1 ≤ sec_H N m := sec_tau_min (by omega) (by omega)
      have hlog := sec_H_le_log hm2 N (by omega)
      have hmr : (m : ℝ) - 1 = (sec_tau N : ℝ) - 2 := by
        rw [hm]
        push_cast [show 1 ≤ sec_tau N by omega]
        ring
      rw [hmr] at hlog
      have hτ2 : (0 : ℝ) < (sec_tau N : ℝ) - 2 := by
        have : (3 : ℝ) ≤ sec_tau N := by exact_mod_cast h
        linarith
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have : (sec_tau N : ℝ) ≤ N := by exact_mod_cast hτN
        linarith
      have h1 : 1 ≤ Real.log (((N : ℝ) - 1) / ((sec_tau N : ℝ) - 2)) := le_trans hHm hlog
      have h2 : Real.exp 1 ≤ ((N : ℝ) - 1) / ((sec_tau N : ℝ) - 2) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < ((N : ℝ) - 1) / ((sec_tau N : ℝ) - 2))]
        exact Real.exp_le_exp.2 h1
      have h3 : (sec_tau N : ℝ) - 2 ≤ ((N : ℝ) - 1) * Real.exp (-1) := by
        rw [le_div_iff₀ hτ2] at h2
        have he1 : Real.exp 1 * Real.exp (-1) = 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos 1]
      rw [div_le_iff₀ hNpos, add_mul, div_mul_cancel₀ _ hNpos.ne']
      nlinarith

/-- **`τ(N)/N → 1/e`** (Miao, p. 186), with τ as in (6.43): with many candidates the employer
should interview about `N/e` of them before accepting the best so far. -/
theorem sec_tau_limit :
    Tendsto (fun N : ℕ => (sec_tau N : ℝ) / N) atTop (𝓝 (Real.exp (-1))) := by
  have hup : Tendsto (fun N : ℕ => Real.exp (-1) + 2 / (N : ℝ)) atTop (𝓝 (Real.exp (-1))) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
    simpa using tendsto_const_nhds.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (sec_tau_bounds hN).1.le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (sec_tau_bounds hN).2

/-- Miao, p. 186: `1/e ≃ 0.368`; precisely `0.3678 < 1/e < 0.3679`. -/
theorem sec_inv_e_approx : 0.3678 < Real.exp (-1) ∧ Real.exp (-1) < 0.3679 := by
  rw [Real.exp_neg]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  constructor
  · rw [lt_inv_comm₀ (by norm_num) hpos]
    linarith
  · rw [inv_lt_comm₀ hpos (by norm_num)]
    linarith

end Miao.FiniteHorizonDP
