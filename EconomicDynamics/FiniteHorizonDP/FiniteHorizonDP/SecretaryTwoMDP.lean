/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiniteHorizonDP.SecretaryExercises
import FiniteHorizonDP.SecretaryMDP

/-!
# Exercise 6.3 as a Markov decision process

The best-two secretary problem in Chapter 5's formulation `secretaryTwo N` (Exercise 5.3,
`MDPStoppingExamples`), recast as the Markov decision process `(secretaryTwo N).toMDP` with
dates shifted by one (MDP date `t` is the book's date `t + 1`) and horizon `T = N − 1`.

* `two_integral_cont`: after continuing, `∫ w dP = (w(1) + w(2))/(t + 2) + t w(0)/(t + 2)`.
* `ex_6_3_mdp` (with Theorem 6.3.2): the recursion `two_V` of `SecretaryExercises` gives the value
  functions of the Markov decision problem, and the rule "stop at relative rank `r` at date `k`
  iff `g_k(r) ≥ W_k`" (`two_rule`) is optimal from every history. With `ex_6_3_threshold` and
  `ex_6_3_rank2` this is the solution of Exercise 6.3: two thresholds `τ_1 ≤ τ_2`, with
  `τ_2 = ⌈(2N + 1)/3⌉`.
-/

namespace Miao.FiniteHorizonDP

open MeasureTheory ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z]

theorem po_stopP_cont (sp : StoppingProblem Z) (t : ℕ) (z : Z) :
    sp.toMDP.P t (Sum.inl z, 1) = (sp.Q t z).map Sum.inl := by
  change stopKernel (sp.Q t) (Sum.inl z, 1) = _
  rw [stopKernel, famKernel_apply]
  simp only [ite_true]
  rw [contKernel_inl]

theorem po_stopP_stop (sp : StoppingProblem Z) (t : ℕ) (s : Z ⊕ Unit) :
    sp.toMDP.P t (s, 0) = Measure.dirac sHat := by
  change stopKernel (sp.Q t) (s, 0) = _
  rw [stopKernel, famKernel_apply]
  simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, Kernel.const_apply]

theorem po_stopP_hat (sp : StoppingProblem Z) (t : ℕ) (u : Unit) (a : Fin 2) :
    sp.toMDP.P t (Sum.inr u, a) = Measure.dirac sHat := by
  change stopKernel (sp.Q t) (Sum.inr u, a) = _
  rw [stopKernel, famKernel_apply]
  split_ifs
  · exact contKernel_inr _ u
  · rfl

/-- Bounded payoffs give bounded rewards of the stopping MDP. -/
theorem po_toMDP_bounded (sp : StoppingProblem Z) {B : ℝ} (hB : sp.Bounded B) :
    BoundedRewards sp.toMDP B := by
  refine ⟨fun t x => ?_, fun s => ?_⟩
  · obtain ⟨s, a⟩ := x
    cases s with
    | inl z =>
      simp only [StoppingProblem.toMDP, Sum.elim_inl]
      split_ifs
      · exact hB.2.1 t z
      · exact hB.2.2.1 t z
    | inr _ => simpa [StoppingProblem.toMDP] using hB.1
  · cases s with
    | inl z => exact hB.2.2.2 z
    | inr _ => simpa [StoppingProblem.toMDP] using hB.1

theorem two_measurable {β : Type*} [MeasurableSpace β] (f : Fin 3 ⊕ Unit → β) : Measurable f := by
  rw [← Sum.elim_comp_inl_inr f]
  exact (measurable_of_countable _).sumElim (measurable_of_countable _)

theorem two_integrable (μ : Measure (Fin 3 ⊕ Unit)) [IsFiniteMeasure μ]
    (w : Fin 3 ⊕ Unit → ℝ) : Integrable w μ :=
  Integrable.of_bound (two_measurable w).aestronglyMeasurable (∑ x, |w x|)
    (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun x _ => abs_nonneg (w x)) (Finset.mem_univ s))

theorem po_fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  fin_cases a <;> simp

theorem two_isMarkov {N : ℕ} (hN : 2 ≤ N) : (secretaryTwo N).toMDP.IsMarkov := (ex_5_3 hN).1

theorem two_bounded {N : ℕ} (hN : 2 ≤ N) : (secretaryTwo N).Bounded 1 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) * (N - 1) := by nlinarith
  refine ⟨zero_le_one, fun t z => by simp [secretaryTwo], fun t z => ?_, fun z => ?_⟩
  · set k : ℕ := min (t + 1) N with hk
    have hk1 : 1 ≤ k := le_min (by omega) (by omega)
    have hkN : k ≤ N := min_le_right _ _
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkN' : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have hcase : (k : ℝ) = N ∨ (k : ℝ) + 1 ≤ N := by
      rcases Nat.lt_or_ge k N with h | h
      · exact Or.inr (by exact_mod_cast h)
      · exact Or.inl (by exact_mod_cast le_antisymm hkN h)
    simp only [secretaryTwo, ← hk]
    split_ifs
    · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
      rcases hcase with h | h
      · rw [h]
        linarith
      · nlinarith
    · rw [abs_of_nonneg (div_nonneg (by nlinarith) hden.le), div_le_one hden]
      nlinarith
    · simp
  · simp only [secretaryTwo]
    split_ifs <;> simp

theorem two_assumption {N : ℕ} (hN : 2 ≤ N) (T : ℕ) :
    po_Assumption513 (secretaryTwo N).toMDP T :=
  po_assumption513_of_bounded (two_isMarkov hN) (po_toMDP_bounded _ (two_bounded hN))
    (fun _ => measurable_toMDP_u _ measurable_const (measurable_of_countable _))
    (measurable_toMDP_uT _ (measurable_of_countable _)) T

/-- The integral after continuing (MDP date `t`, book date `t + 1`):
`∫ w dP = w(1)/(t + 2) + w(2)/(t + 2) + t w(0)/(t + 2)`. -/
theorem two_integral_cont (N t : ℕ) (z : Fin 3) (w : Fin 3 ⊕ Unit → ℝ) :
    ∫ s, w s ∂(secretaryTwo N).toMDP.P t (Sum.inl z, 1) =
      1 / ((t : ℝ) + 2) * w (Sum.inl 1) + 1 / ((t : ℝ) + 2) * w (Sum.inl 2) +
        (t : ℝ) / ((t : ℝ) + 2) * w (Sum.inl 0) := by
  have := isProbabilityMeasure_rank3 t
  rw [po_stopP_cont]
  change ∫ s, w s ∂(rank3 t).map Sum.inl = _
  rw [integral_map measurable_inl.aemeasurable (two_measurable _).aestronglyMeasurable,
    integral_fintype Integrable.of_finite, Fin.sum_univ_three]
  have h0 : (0 : ℝ) ≤ 1 / ((t : ℝ) + 2) := by positivity
  have h1 : (0 : ℝ) ≤ (t : ℝ) / ((t : ℝ) + 2) := by positivity
  have r0 : (rank3 t).real {0} = (t : ℝ) / ((t : ℝ) + 2) := by
    simp [measureReal_def, rank3, Measure.dirac_apply', ENNReal.toReal_ofReal h1]
  have ht2 : (0 : ℝ) ≤ (t : ℝ) + 2 := by positivity
  have r1 : (rank3 t).real {1} = 1 / ((t : ℝ) + 2) := by
    simp [measureReal_def, rank3, Measure.dirac_apply', ht2]
  have r2 : (rank3 t).real {2} = 1 / ((t : ℝ) + 2) := by
    simp [measureReal_def, rank3, Measure.dirac_apply', ht2]
  simp only [r0, r1, r2, smul_eq_mul]
  ring

theorem two_u_inl (N t : ℕ) (z : Fin 3) (b : Fin 2) :
    (secretaryTwo N).toMDP.u t (Sum.inl z, b) =
      if b = 1 then 0 else (secretaryTwo N).g t z := by
  simp [StoppingProblem.toMDP, secretaryTwo]

/-- The value functions in MDP dates: `w_t(r) = V_{t+1}(r)`, `w_t(ŝ) = 0`. -/
noncomputable def two_w (N t : ℕ) : Fin 3 ⊕ Unit → ℝ :=
  Sum.elim (fun z => two_V N (t + 1) z) fun _ => 0

open Classical in
/-- The optimal rule: at MDP date `t` (book date `k = t + 1`), stop at relative rank `r` iff
`g_k(r) ≥ W_k`. -/
noncomputable def two_rule (N t : ℕ) : Fin 3 ⊕ Unit → Fin 2 :=
  Sum.elim (fun z => if two_W N (t + 1) ≤ two_g N (t + 1) z then 0 else 1) fun _ => 1

theorem two_g_eq {N t : ℕ} (ht : t + 1 ≤ N) (z : Fin 3) :
    (secretaryTwo N).g t z = two_g N (t + 1) z := by
  simp only [secretaryTwo, two_g, min_eq_left ht]

theorem two_bv {N t : ℕ} (ht : t + 1 < N) (z : Fin 3) (b : Fin 2) :
    po_bellmanVal (secretaryTwo N).toMDP (two_w N) t (Sum.inl z) b =
      if b = 1 then two_W N (t + 1) else two_g N (t + 1) z := by
  have hβ : (secretaryTwo N).toMDP.β = 1 := rfl
  unfold po_bellmanVal
  rw [two_u_inl N t z b, hβ, one_mul]
  rcases po_fin2_cases b with rfl | rfl
  · rw [po_stopP_stop, integral_dirac' _ _ (two_measurable _).stronglyMeasurable]
    simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false, two_w, sHat, Sum.elim_inr, add_zero,
      two_g_eq ht.le]
  · rw [two_integral_cont]
    simp only [ite_true, zero_add, two_w, Sum.elim_inl, two_W]
    push_cast
    ring_nf

theorem two_bv_hat {N t : ℕ} (u : Unit) (b : Fin 2) :
    po_bellmanVal (secretaryTwo N).toMDP (two_w N) t (Sum.inr u) b = 0 := by
  unfold po_bellmanVal
  rw [po_stopP_hat, integral_dirac' _ _ (two_measurable _).stronglyMeasurable]
  simp [two_w, sHat, StoppingProblem.toMDP]

theorem two_solves {N : ℕ} {t : ℕ} (ht : t < N - 1) (s : Fin 3 ⊕ Unit) :
    po_SolvesAt (secretaryTwo N).toMDP (two_w N) t s ∧
      two_rule N t s ∈ po_G (secretaryTwo N).toMDP (two_w N) t s := by
  have hk : t + 1 < N := by omega
  cases s with
  | inr u =>
    refine po_solvesAt_of_max (fun a _ => ?_) (Set.mem_univ _) ?_ <;>
      simp only [two_bv_hat, two_w, Sum.elim_inr, le_refl]
  | inl z =>
    have hV := (ex_6_3_bellman N).2 (t + 1) hk z
    refine po_solvesAt_of_max (fun b _ => ?_) (Set.mem_univ _) ?_
    · simp only [two_w, Sum.elim_inl]
      rw [two_bv hk, hV]
      split_ifs
      · exact le_max_right _ _
      · exact le_max_left _ _
    · simp only [two_w, Sum.elim_inl, two_rule]
      rw [hV]
      split_ifs with h
      · rw [two_bv hk]
        simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false]
        exact (max_eq_left h).symm
      · rw [two_bv hk]
        simp only [ite_true]
        exact (max_eq_right (le_of_lt (lt_of_not_ge h))).symm

theorem two_wT {N : ℕ} (hN : 1 ≤ N) (s : Fin 3 ⊕ Unit) :
    two_w N (N - 1) s = (secretaryTwo N).toMDP.uT s := by
  obtain ⟨h0, h1, h2⟩ := (ex_6_3_bellman N).1
  cases s with
  | inl z =>
    simp only [two_w, Sum.elim_inl, Nat.sub_add_cancel hN, StoppingProblem.toMDP, secretaryTwo]
    rcases po_fin3_cases z with rfl | rfl | rfl
    · simp [h0]
    · simp [h1]
    · simp [h2, show (2 : Fin 3) ≠ 0 by decide]
  | inr u => rfl

/-- **Exercise 6.3, solved as a Markov decision problem** (Miao, p. 189). For `N ≥ 2`, every MDP
date `t ≤ N − 1` and every history `sᵗ`: the value of the sequence problem (6.14) of
`(secretaryTwo N).toMDP` is `two_w N t` (the book's `V_{t+1}` of `ex_6_3_bellman`), and the rule
"stop at relative rank `r` iff `g_k(r) ≥ W_k`" attains it. -/
theorem ex_6_3_mdp {N : ℕ} (hN : 2 ≤ N) {t : ℕ} (ht : t ≤ N - 1)
    (h : Fin (t + 1) → Fin 3 ⊕ Unit) :
    po_genFrom (two_rule N) t (h (Fin.last t)) ∈
        po_plansFrom (secretaryTwo N).toMDP (N - 1) t h ∧
      po_JFrom (secretaryTwo N).toMDP (N - 1) t h
        (po_genFrom (two_rule N) t (h (Fin.last t))) = two_w N t (h (Fin.last t)) ∧
      po_VFrom (secretaryTwo N).toMDP (N - 1) t h = two_w N t (h (Fin.last t)) :=
  theorem_6_3_2 (two_isMarkov hN) zero_le_one (two_assumption hN (N - 1))
    (fun t _ s a _ => by
      have := two_isMarkov hN t
      exact two_integrable _ _)
    (fun t ht s => (two_solves ht s).1) (fun _ _ => two_measurable _)
    (fun t ht s => (two_solves ht s).2) (two_wT (by omega)) t ht h

end Miao.FiniteHorizonDP
