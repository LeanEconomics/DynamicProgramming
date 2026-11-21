/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.SecretaryBellman
import FiniteHorizonDP.POVerification
import FiniteHorizonDP.MDPStoppingExamples
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The secretary problem as a Markov decision process: Proposition 6.6.1

Miao, §6.6.1, pp. 185–186, in Chapter 5's formulation `secretary N` (`MDPStoppingExamples`): the
optimal stopping problem recast as the Markov decision process `(secretary N).toMDP` on
`{0, 1} ∪ {ŝ}` (`Sum.inl z`, `Sum.inr ()`) with actions `1` = continue, `0` = stop, `β = 1`,
**dates shifted by one** (MDP date `t` is the book's date `t + 1`), and horizon `T = N − 1`.

* `sec_integral_cont`, `sec_integral_stop`, `sec_integral_hat`: the integrals against the
  kernels; `sec_bellmanVal_*`: the right-hand side of (6.19).
* `sec_mdp_values`: by Theorem 6.3.2, the recursion of `SecretaryBellman` gives the value
  functions of the Markov decision problem, `V_{t+1}^{MDP}(z) = sec_V N (t + 1) z`; so the Bellman
  equations (6.41)–(6.42) are those of the problem's values.
* **Proposition 6.6.1** (`prop_6_6_1`), corrected: the plan "accept the first best-so-far candidate
  at a date `≥ τ`" (`sec_rule N τ`), i.e. reject the first `τ − 1` candidates, is optimal, with
  value `V_1(1)`; it is optimal from every history (`prop_6_6_1_from`).
* `prop_6_6_1_misprint`: the printed rule "interview `τ` candidates and subsequently choose the
  first candidate better than those" (`sec_rule N (τ + 1)`) is not optimal: for `N = 4` it wins
  with probability `5/12 < 11/24 = V_1(1)`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

theorem po_fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  fin_cases a <;> simp

/-- Every function on `{0, 1} ∪ {ŝ}` is measurable (the space has no `MeasurableSingletonClass`
instance in Mathlib, so this is proved from the two summands). -/
theorem sec_measurable {β : Type*} [MeasurableSpace β] (f : Fin 2 ⊕ Unit → β) : Measurable f := by
  rw [← Sum.elim_comp_inl_inr f]
  exact (measurable_of_countable _).sumElim (measurable_of_countable _)

theorem sec_integrable (μ : Measure (Fin 2 ⊕ Unit)) [IsFiniteMeasure μ]
    (w : Fin 2 ⊕ Unit → ℝ) : Integrable w μ :=
  Integrable.of_bound (sec_measurable w).aestronglyMeasurable (∑ x, |w x|)
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun x _ => abs_nonneg (w x)) (Finset.mem_univ s))

theorem sec_isMarkov (N : ℕ) : (secretary N).toMDP.IsMarkov := (secretary_assumptions N).1

theorem sec_P_cont (N t : ℕ) (z : Fin 2) :
    (secretary N).toMDP.P t (Sum.inl z, 1) = (bern (1 / ((t : ℝ) + 2))).map Sum.inl := by
  change stopKernel ((secretary N).Q t) (Sum.inl z, 1) = _
  rw [stopKernel, famKernel_apply]
  simp only [ite_true]
  rw [contKernel_inl]
  rfl

theorem sec_P_stop (N t : ℕ) (s : Fin 2 ⊕ Unit) :
    (secretary N).toMDP.P t (s, 0) = Measure.dirac sHat := by
  change stopKernel ((secretary N).Q t) (s, 0) = _
  rw [stopKernel, famKernel_apply]
  simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, Kernel.const_apply]

theorem sec_P_hat (N t : ℕ) (u : Unit) (a : Fin 2) :
    (secretary N).toMDP.P t (Sum.inr u, a) = Measure.dirac sHat := by
  change stopKernel ((secretary N).Q t) (Sum.inr u, a) = _
  rw [stopKernel, famKernel_apply]
  split_ifs
  · exact contKernel_inr _ u
  · rfl

/-- The integral after continuing at a candidate:
`∫ w dP = w(1)/(t + 2) + (t + 1)w(0)/(t + 2)` (MDP date `t`, book date `t + 1`). -/
theorem sec_integral_cont (N t : ℕ) (z : Fin 2) (w : Fin 2 ⊕ Unit → ℝ) :
    ∫ s, w s ∂(secretary N).toMDP.P t (Sum.inl z, 1) =
      1 / ((t : ℝ) + 2) * w (Sum.inl 1) + ((t : ℝ) + 1) / ((t : ℝ) + 2) * w (Sum.inl 0) := by
  have h0 : (0 : ℝ) ≤ 1 / ((t : ℝ) + 2) := by positivity
  have h1 : 1 / ((t : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have := isProbabilityMeasure_bern h0 h1
  rw [sec_P_cont, integral_map measurable_inl.aemeasurable
    (sec_measurable _).aestronglyMeasurable, integral_fintype Integrable.of_finite,
    Fin.sum_univ_two]
  obtain ⟨e1, e0⟩ := bern_one (1 / ((t : ℝ) + 2))
  simp only [measureReal_def, e1, e0, smul_eq_mul]
  rw [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]
  have : 1 - 1 / ((t : ℝ) + 2) = ((t : ℝ) + 1) / ((t : ℝ) + 2) := by field_simp; ring
  rw [this]
  ring

theorem sec_integral_stop (N t : ℕ) (s : Fin 2 ⊕ Unit) (w : Fin 2 ⊕ Unit → ℝ) :
    ∫ s', w s' ∂(secretary N).toMDP.P t (s, 0) = w sHat := by
  rw [sec_P_stop, integral_dirac' _ _ (sec_measurable w).stronglyMeasurable]

theorem sec_integral_hat (N t : ℕ) (u : Unit) (a : Fin 2) (w : Fin 2 ⊕ Unit → ℝ) :
    ∫ s', w s' ∂(secretary N).toMDP.P t (Sum.inr u, a) = w sHat := by
  rw [sec_P_hat, integral_dirac' _ _ (sec_measurable w).stronglyMeasurable]

theorem sec_u_inl (N t : ℕ) (z a : Fin 2) :
    (secretary N).toMDP.u t (Sum.inl z, a) =
      if a = 1 then 0 else if z = 1 then ((min (t + 1) N : ℕ) : ℝ) / N else 0 := by
  simp [StoppingProblem.toMDP, secretary]

theorem sec_u_inr (N t : ℕ) (u : Unit) (a : Fin 2) :
    (secretary N).toMDP.u t (Sum.inr u, a) = 0 := rfl

/-- The value functions of the Markov decision problem, in MDP dates: `w_t(z) = V_{t+1}(z)` and
`w_t(ŝ) = 0`. -/
noncomputable def sec_w (N t : ℕ) : Fin 2 ⊕ Unit → ℝ :=
  Sum.elim (fun z => sec_V N (t + 1) z) fun _ => 0

/-- The threshold rule: at MDP date `t` (the `(t + 1)`-th candidate), stop at a best-so-far
candidate if `t + 1 ≥ r`, otherwise continue. -/
def sec_rule (r : ℕ) (t : ℕ) : Fin 2 ⊕ Unit → Fin 2 :=
  Sum.elim (fun z => if z = 1 ∧ r ≤ t + 1 then 0 else 1) fun _ => 1

theorem sec_bv_cont {N t : ℕ} (z : Fin 2) :
    po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inl z) 1 = sec_C N (t + 1) := by
  unfold po_bellmanVal
  rw [sec_integral_cont, sec_u_inl]
  simp only [ite_true, zero_add, sec_w, Sum.elim_inl, sec_C]
  have : (secretary N).toMDP.β = 1 := rfl
  rw [this, one_mul]
  push_cast
  ring_nf

theorem sec_bv_stop {N t : ℕ} (ht : t + 1 ≤ N) (z : Fin 2) :
    po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inl z) 0 =
      if z = 1 then ((t : ℝ) + 1) / N else 0 := by
  unfold po_bellmanVal
  rw [sec_integral_stop, sec_u_inl, min_eq_left ht]
  have : (secretary N).toMDP.β = 1 := rfl
  simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, sec_w, sHat, Sum.elim_inr, this,
    mul_zero, add_zero]
  push_cast
  rfl

theorem sec_bv_hat {N t : ℕ} (u : Unit) (a : Fin 2) :
    po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inr u) a = 0 := by
  unfold po_bellmanVal
  rw [sec_integral_hat, sec_u_inr]
  simp [sec_w, sHat]

theorem sec_bounded (N : ℕ) : BoundedRewards (secretary N).toMDP 1 := by
  refine ⟨fun t x => ?_, fun s => ?_⟩
  · obtain ⟨s, a⟩ := x
    cases s with
    | inl z =>
      rw [sec_u_inl]
      split_ifs
      · simp
      · rcases Nat.eq_zero_or_pos N with hN | hN
        · simp [hN]
        · rw [abs_of_nonneg (by positivity), div_le_one (by exact_mod_cast hN)]
          exact_mod_cast min_le_right _ _
      · simp
    | inr u => rw [sec_u_inr]; simp
  · cases s with
    | inl z => simp only [StoppingProblem.toMDP, Sum.elim_inl, secretary]; split_ifs <;> simp
    | inr u => simp [StoppingProblem.toMDP]

theorem sec_assumption (N T : ℕ) : po_Assumption513 (secretary N).toMDP T :=
  po_assumption513_of_bounded (sec_isMarkov N) (sec_bounded N)
    (fun _ => measurable_toMDP_u _ measurable_const (measurable_of_countable _))
    (measurable_toMDP_uT _ (measurable_of_countable _)) T

/-- The Bellman equation of the Markov decision problem is solved by `sec_w`, and the threshold
rule with `r = τ` selects maximisers, at every MDP date `t < N − 1`. -/
theorem sec_solves {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t < N - 1) (s : Fin 2 ⊕ Unit) :
    po_SolvesAt (secretary N).toMDP (sec_w N) t s ∧
      sec_rule (sec_tau N) t s ∈ po_G (secretary N).toMDP (sec_w N) t s := by
  have hk : t + 1 < N := by omega
  obtain ⟨hV1, hV0⟩ := sec_bellman N hk
  have hC := sec_C_nonneg N (t + 1)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hstop, hcont⟩ := sec_threshold (show 1 ≤ N by omega)
  push_cast at hV1
  cases s with
  | inr u =>
    refine po_solvesAt_of_max (fun a _ => ?_) (Set.mem_univ _) ?_ <;>
      simp only [sec_bv_hat, sec_w, Sum.elim_inr, le_refl]
  | inl z =>
    have hle : ∀ a ∈ (secretary N).toMDP.Γ (Sum.inl z),
        po_bellmanVal (secretary N).toMDP (sec_w N) t (Sum.inl z) a ≤ sec_w N t (Sum.inl z) := by
      intro a _
      simp only [sec_w, Sum.elim_inl]
      rcases po_fin2_cases a with rfl | rfl
      · rw [sec_bv_stop hk.le]
        rcases po_fin2_cases z with rfl | rfl
        · simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false]
          rw [hV0]
          exact le_max_left _ _
        · simp only [ite_true]
          rw [hV1]
          exact le_max_left _ _
      · rw [sec_bv_cont]
        rcases po_fin2_cases z with rfl | rfl
        · rw [hV0]
          exact le_max_right _ _
        · rw [hV1]
          exact le_max_right _ _
    refine po_solvesAt_of_max hle (Set.mem_univ _) ?_
    simp only [sec_w, Sum.elim_inl, sec_rule]
    rcases po_fin2_cases z with rfl | rfl
    · simp only [show (0 : Fin 2) ≠ 1 by decide, false_and, ite_false]
      rw [sec_bv_cont, hV0, max_eq_right hC]
    · simp only [true_and]
      split_ifs with hτ
      · rw [sec_bv_stop hk.le]
        simp only [ite_true]
        have h1 := hstop (t + 1) hτ hk.le
        rw [hV0] at h1
        push_cast at h1
        rw [hV1, max_eq_left (le_trans (le_max_right _ _) h1)]
      · rw [sec_bv_cont]
        have h1 := hcont (t + 1) (by omega) (by omega)
        rw [hV0, max_eq_right hC] at h1
        push_cast at h1
        rw [hV1, max_eq_right h1]

theorem sec_wT {N : ℕ} (hN : 1 ≤ N) (s : Fin 2 ⊕ Unit) :
    sec_w N (N - 1) s = (secretary N).toMDP.uT s := by
  cases s with
  | inl z =>
    simp only [sec_w, Sum.elim_inl, Nat.sub_add_cancel hN, StoppingProblem.toMDP, secretary]
    rcases po_fin2_cases z with rfl | rfl
    · simp [(sec_V_terminal N).2]
    · simp [(sec_V_terminal N).1]
  | inr u => rfl

/-- **The secretary problem's value functions** (Miao, pp. 185–186). By Theorem 6.3.2, for every
MDP date `t ≤ N − 1` and history `sᵗ`, the value of the sequence problem (6.14) is `sec_w N t`
(the book's `V_{t+1}`), and the threshold plan with `r = τ` attains it. -/
theorem sec_mdp_values {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t ≤ N - 1)
    (h : Fin (t + 1) → Fin 2 ⊕ Unit) :
    po_genFrom (sec_rule (sec_tau N)) t (h (Fin.last t)) ∈
        po_plansFrom (secretary N).toMDP (N - 1) t h ∧
      po_JFrom (secretary N).toMDP (N - 1) t h
        (po_genFrom (sec_rule (sec_tau N)) t (h (Fin.last t))) = sec_w N t (h (Fin.last t)) ∧
      po_VFrom (secretary N).toMDP (N - 1) t h = sec_w N t (h (Fin.last t)) :=
  theorem_6_3_2 (sec_isMarkov N) zero_le_one (sec_assumption N (N - 1))
    (fun t _ s a _ => by
      have := sec_isMarkov N t
      exact sec_integrable _ _)
    (fun t ht s => (sec_solves hN ht s).1) (fun _ _ => sec_measurable _)
    (fun t ht s => (sec_solves hN ht s).2) (sec_wT (by omega)) t ht h

/-- **Proposition 6.6.1** (Miao, p. 185), corrected. For `N ≥ 2`, with τ as in (6.43), the plan
"reject the first `τ − 1` candidates, then accept the first candidate who is the best so far"
(stop at a best-so-far candidate at a date `≥ τ`) is optimal from the first candidate
(`s₀ = 1`: the first candidate is the best so far), and its probability of choosing the best is
`V_1(1)`. -/
theorem prop_6_6_1 {N : ℕ} (hN : 2 ≤ N) :
    po_genPlan (sec_rule (sec_tau N)) (Sum.inl 1) ∈
        feasiblePlans (secretary N).toMDP ((N - 1 : ℕ) : ℕ∞) (Sum.inl 1) ∧
      J0T (secretary N).toMDP (N - 1) (Sum.inl 1) (po_genPlan (sec_rule (sec_tau N))
        (Sum.inl 1)) = sec_V N 1 1 ∧
      V0 (secretary N).toMDP (N - 1) (Sum.inl 1) = sec_V N 1 1 := by
  have := sec_mdp_values hN (Nat.zero_le _) fun _ => Sum.inl 1
  exact this

/-- Proposition 6.6.1 from every history: the threshold plan is optimal at every date `t` from
every history (Theorem 6.3.2), in particular after any history reached by following it. -/
theorem prop_6_6_1_from {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t ≤ N - 1)
    (h : Fin (t + 1) → Fin 2 ⊕ Unit) :
    (po_JFrom (secretary N).toMDP (N - 1) t h
      (po_genFrom (sec_rule (sec_tau N)) t (h (Fin.last t))) : EReal) =
      po_VFrom (secretary N).toMDP (N - 1) t h := by
  obtain ⟨-, h1, h2⟩ := sec_mdp_values hN ht h
  rw [h1, h2]

/-- The probabilities of winning under the rule `sec_rule 3` for `N = 4`, by date. -/
noncomputable def sec4_w : ℕ → Fin 2 ⊕ Unit → ℝ := fun t =>
  Sum.elim (fun z => if t = 3 then (if z = 1 then 1 else 0)
    else if t = 2 then (if z = 1 then 3 / 4 else 1 / 4) else 5 / 12) fun _ => 0

/-- **The printed Proposition 6.6.1 is off by one** (Miao, p. 185): for `N = 4`, `τ = 2` by
(6.43), and the rule "interview `τ` candidates and subsequently choose the first candidate that is
better than those `τ`" (`sec_rule (τ + 1)`) wins with probability `5/12`, less than the optimal
`V_1(1) = 11/24`. -/
theorem prop_6_6_1_misprint :
    J0T (secretary 4).toMDP 3 (Sum.inl 1) (po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1)) =
        5 / 12 ∧ sec_V 4 1 1 = 11 / 24 ∧
      J0T (secretary 4).toMDP 3 (Sum.inl 1) (po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1)) <
        V0 (secretary 4).toMDP 3 (Sum.inl 1) := by
  have hτ := sec_tau_four.1
  have hV : sec_V 4 1 1 = 11 / 24 := by
    obtain ⟨h0, h1⟩ := eq_6_41_6_42 4 (t := 1) (by norm_num)
    have h20 := sec_threshold_misprint.1
    have h21 := (eq_6_41_6_42 4 (t := 2) (by norm_num)).2
    rw [h20] at h21
    norm_num at h21
    rw [h1, h0, h21, h20]
    norm_num
  have hF : po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1) ∈
      feasiblePlans (secretary 4).toMDP ((3 : ℕ) : ℕ∞) (Sum.inl 1) :=
    po_genPlan_feasible (fun _ _ => sec_measurable _) (fun _ _ _ => Set.mem_univ _) _
  have hJ : J0T (secretary 4).toMDP 3 (Sum.inl 1)
      (po_genPlan (sec_rule (sec_tau 4 + 1)) (Sum.inl 1)) = 5 / 12 := by
    have := po_policy_value 3 (secretary 4).toMDP sec4_w (sec_rule (sec_tau 4 + 1))
      (sec_isMarkov 4) (fun _ _ => sec_measurable _) (fun j hj s => ?_) (fun s => ?_)
      (Sum.inl 1) (po_intPlan_of_assumption513 (sec_assumption 4 3 0 (Nat.zero_le 3)) hF)
    · rw [this]
      simp [sec4_w]
    · have hβ : (secretary 4).toMDP.β = 1 := rfl
      rw [hτ, hβ, one_mul]
      cases s with
      | inr u =>
        rw [sec_u_inr, sec_rule, Sum.elim_inr, sec_integral_hat]
        simp [sec4_w, sHat]
      | inl z =>
        interval_cases j <;> rcases po_fin2_cases z with rfl | rfl <;>
          simp [sec_rule, sec_u_inl, sec_integral_cont, sec_integral_stop, sec4_w, sHat] <;>
          norm_num
    · cases s with
      | inr u => rfl
      | inl z =>
        rcases po_fin2_cases z with rfl | rfl <;> simp [sec4_w, StoppingProblem.toMDP, secretary]
  refine ⟨hJ, hV, ?_⟩
  rw [hJ, (prop_6_6_1 (N := 4) (by norm_num)).2.2, hV]
  norm_num

end Miao.FiniteHorizonDP
