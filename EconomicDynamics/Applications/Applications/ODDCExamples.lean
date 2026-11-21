/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.ODDCSolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Discrete choice: two concrete replacement problems

Miao, §8.2, pp. 235–236. The cost `c(s) = K arctan s` is bounded, continuously differentiable
(`c′(s) = K/(1 + s²)`) and, for `K > 0`, strictly increasing: it satisfies all of the book's
assumptions (`od_dcArctan`, `od_dcArctan_props`). Take `P_b − P_s = 1` (`P_b = 1`, `P_s = 0`).

* `od_dc_example_misprint` (`K = 2`): the cost rises by `2 arctan 1 = π/2 > 1`, so a trigger
  `s* ∈ (0, 1)` exists, and the printed solution formula of p. 236 is wrong at `s = 0`: it lies
  strictly above `V(0)`.
* `od_dc_example_no_trigger` (`K = (1 − β)/2`): the cost rises by less than `(1 − β)π/4 < 1 − β`,
  so maintaining is strictly optimal at every `s ≥ 0`: the trigger `s*` the book assumes does not
  exist.
-/

namespace Miao.Applications

open Real BoundedContinuousFunction

/-- The cost function `c(s) = K arctan s`. -/
noncomputable def od_dcArctan (K : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun s => K * arctan s)
    (continuous_const.mul continuous_arctan) (|K| * (π / 2)) fun s => by
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact abs_le.2 ⟨(neg_pi_div_two_lt_arctan s).le, (arctan_lt_pi_div_two s).le⟩

theorem od_dcArctan_apply (K s : ℝ) : od_dcArctan K s = K * arctan s := rfl

/-- `K arctan` is strictly increasing (for `K > 0`), differentiable with derivative
`K/(1 + s²)`, and the derivative is continuous. -/
theorem od_dcArctan_props {K : ℝ} (hK : 0 < K) :
    StrictMonoOn (od_dcArctan K) (Set.Ici 0) ∧
      (∀ s, HasDerivAt (od_dcArctan K) (K * (1 / (1 + s ^ 2))) s) ∧
      Continuous fun s : ℝ => K * (1 / (1 + s ^ 2)) := by
  refine ⟨fun x _ y _ hxy => ?_, fun s => ?_, ?_⟩
  · rw [od_dcArctan_apply, od_dcArctan_apply]
    exact mul_lt_mul_of_pos_left (arctan_strictMono hxy) hK
  · exact (hasDerivAt_arctan s).const_mul K
  · exact continuous_const.mul (continuous_const.div (by fun_prop) fun s => by positivity)

/-- Miao, p. 236, a concrete counterexample to the printed solution formula: with
`c(s) = 2 arctan s`, `P_b = 1`, `P_s = 0`, the Bellman equation has a solution `V`, there is a
trigger `s* ∈ (0, 1)`, and the printed `max{−c(s*)/(1 − β), P(0)}` exceeds `V(0)`. -/
theorem od_dc_example_misprint {lam β : ℝ} (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ V : ℝ →ᵇ ℝ, od_DCBellman (od_dcArctan 2) lam β 1 0 V ∧
      ∃ ss ∈ Set.Ioo (0 : ℝ) 1,
        od_dcM (od_dcArctan 2) lam β V ss = od_dcR (od_dcArctan 2) lam β 1 0 V ∧
        V 0 < max (-od_dcArctan 2 ss / (1 - β))
          (-od_dcArctan 2 0 / (1 - β) + ∫ y in (0 : ℝ)..ss, 2 * (1 / (1 + y ^ 2)) / (1 - β) *
            (1 - β * exp (-(lam * (1 - β) * (y - 0))))) := by
  obtain ⟨hmono, hder, hcont⟩ := od_dcArctan_props (K := 2) two_pos
  obtain ⟨V, -, hV⟩ := od_dc_exists hlam (od_dcArctan 2) hβ0 hβ1 1 0
  have hjump : (1 : ℝ) - 0 < od_dcArctan 2 1 - od_dcArctan 2 0 := by
    rw [od_dcArctan_apply, od_dcArctan_apply, arctan_one, arctan_zero]
    linarith [pi_gt_three]
  obtain ⟨ss, hss, hind⟩ := od_dc_trigger_exists hlam hβ0 hβ1 (by norm_num) hmono.monotoneOn hV
    zero_le_one hjump
  refine ⟨V, hV, ss, hss, hind, ?_⟩
  exact (od_dc_solution_misprint hlam hβ0 hβ1 (by norm_num) hmono hder hcont hV hss.1.le hind 0
    ⟨le_rfl, hss.1⟩).2

/-- Miao, p. 235, a concrete counterexample to the existence of the trigger: with
`c(s) = ((1 − β)/2) arctan s`, `P_b = 1`, `P_s = 0`, maintaining is strictly better than replacing
at every `s ≥ 0` for every solution `V`, so no indifference point exists. -/
theorem od_dc_example_no_trigger {lam β : ℝ} (hlam : 0 < lam) (hβ0 : 0 < β) (hβ1 : β < 1)
    {V : ℝ →ᵇ ℝ} (hV : od_DCBellman (od_dcArctan ((1 - β) / 2)) lam β 1 0 V) :
    ∀ s, 0 ≤ s → od_dcR (od_dcArctan ((1 - β) / 2)) lam β 1 0 V <
      od_dcM (od_dcArctan ((1 - β) / 2)) lam β V s := by
  have hK : 0 < (1 - β) / 2 := by linarith
  obtain ⟨hmono, -, -⟩ := od_dcArctan_props hK
  refine od_dc_no_trigger hlam hβ0 hβ1 (by norm_num) hmono.monotoneOn hV
    (D := (1 - β) / 2 * (π / 2)) (fun s _ => ?_) ?_
  · rw [od_dcArctan_apply, od_dcArctan_apply, arctan_zero, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left (arctan_lt_pi_div_two s).le hK.le
  · nlinarith [pi_lt_four]

end Miao.Applications
