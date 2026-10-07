/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ApproximationAndLearning.QFactorFDP

/-!
# Q-learning

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §9.2.1 (pp. 310–313).

For a finite MDP, the Q-factor Bellman operator is
`(Sq)(x, a) = r(x, a) + β ∑_{x'} max_{a' ∈ Γ(x')} q(x', a') P(x, a, x')` (9.17), (3.7).

* §9.2.1.1: `S` has a unique fixed point `q*`, the Q-factor value function; with
  Proposition 5.3.1, `v*(x) = max_a q*(x, a)` and any `σ(x) ∈ argmax_a q*(x, a)` is optimal.
* §9.2.1.3: `S` is a contraction of modulus `β` for the supremum norm.
* The Q-learning update (9.18) moves only the visited entry, and there it is the Robbins–Monro
  step `q + α(Ŝq − q)` with the single-sample estimate `(Ŝq)(x, a) = r(x, a) + β max_{a'}
  q(X', a')`, whose mean under `X' ∼ P(x, a, ·)` is `(Sq)(x, a)`: the noise has mean zero.

Theorem 9.2.1 (almost sure convergence of Q-learning, Watkins–Dayan and Tsitsiklis) is cited in
the book and not formalised.
-/

open Set Function Filter Topology

namespace SargentStachurski.ApproximationAndLearning

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- `max_{a ∈ Γ(x)} q(x, a)`. -/
noncomputable def qmax (q : M.G → ℝ) (x : X) : ℝ :=
  (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach) fun a => q ⟨(x, a.1), a.2⟩

theorem le_qmax (q : M.G → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : q ⟨(x, a), ha⟩ ≤ M.qmax q x :=
  Finset.le_sup' (fun a : M.Γ x => q ⟨(x, a.1), a.2⟩) (Finset.mem_attach _ ⟨a, ha⟩)

theorem abs_qmax_sub_le {q q' : M.G → ℝ} {c : ℝ} (h : ∀ p, |q p - q' p| ≤ c) (x : X) :
    |M.qmax q x - M.qmax q' x| ≤ c := by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun a _ => ?_)
    have := (abs_sub_le_iff.1 (h ⟨(x, a.1), a.2⟩)).1
    linarith [M.le_qmax q' a.2]
  · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun a _ => ?_)
    have := (abs_sub_le_iff.1 (h ⟨(x, a.1), a.2⟩)).2
    linarith [M.le_qmax q a.2]

/-- The Q-factor Bellman operator `S` of (9.17). -/
noncomputable def S (q : M.G → ℝ) (p : M.G) : ℝ :=
  M.r p.1.1 p.1.2 + M.β * ∑ x', M.qmax q x' * M.P p.1.1 p.1.2 x'

/-- `S` is the Bellman operator of the Q-factor ADP (Exercise 3.2.4). -/
theorem bellman_qadp (q : M.G → ℝ) : M.qadp.bellman q = M.S q :=
  funext fun p => M.exercise_3_2_4 q p

/-- §9.2.1.3 (p. 311): `S` is a contraction of modulus `β` for the supremum norm. -/
theorem S_contraction {q q' : M.G → ℝ} {c : ℝ} (h : ∀ p, |q p - q' p| ≤ c) (p : M.G) :
    |M.S q p - M.S q' p| ≤ M.β * c := by
  simp only [S, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  exact mul_le_mul_of_nonneg_left (M.abs_sum_sub_le p.2 fun y => M.abs_qmax_sub_le h y)
    M.β_nonneg

/-- §9.2.1.1 (p. 310) with Proposition 5.3.1: `S` has a unique fixed point `q*`, the Q-factor
value function; `v*(x) = max_a q*(x, a)`; and a policy maximizing `q*(x, ·)` at every state is
optimal for the MDP. -/
theorem section_9_2_1 :
    ∃ qstar, M.qadp.IsValueFunction qstar ∧ M.S qstar = qstar ∧
      (∀ q, M.S q = q → q = qstar) ∧
      (∀ v, M.adp.IsValueFunction v → ∀ x, v x = M.qmax qstar x) ∧
      ∀ σ : M.Policy, (∀ x a (ha : a ∈ M.Γ x), qstar ⟨(x, a), ha⟩ ≤ qstar (M.pairOf σ x)) →
        M.adp.IsOptimal M.adp_wellPosed σ := by
  obtain ⟨⟨-, ⟨q, hq, -, hqs, huniq⟩, -⟩, -, -⟩ := M.exercise_3_2_6
  obtain ⟨h1, -, h3⟩ := M.proposition_5_3_1
  refine ⟨q, hq, ?_, fun w hw => ?_, fun v hv x => ((h1 v q hv hq).1 x), fun σ hσ =>
    h3 q σ hq hσ⟩
  · rw [← M.bellman_qadp]
    exact (M.qadp.solvesBellman_iff (M.qadp_regular q)).1 hqs
  · refine huniq w (M.qadp_regular w) ((M.qadp.solvesBellman_iff (M.qadp_regular w)).2 ?_)
    rw [M.bellman_qadp]
    exact hw

/-- The single-sample estimate `(Ŝq)(x, a) = r(x, a) + β max_{a'} q(x', a')` after observing
the next state `x'`. -/
noncomputable def Shat (q : M.G → ℝ) (p : M.G) (x' : X) : ℝ :=
  M.r p.1.1 p.1.2 + M.β * M.qmax q x'

/-- The sample is unbiased: `∑_{x'} (Ŝq)(x, a; x') P(x, a, x') = (Sq)(x, a)`. -/
theorem Shat_unbiased (q : M.G → ℝ) (p : M.G) :
    ∑ x', M.Shat q p x' * M.P p.1.1 p.1.2 x' = M.S q p := by
  simp only [Shat, S, add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, M.P_sum _ _ p.2, mul_one, Finset.mul_sum]
  exact congrArg _ (Finset.sum_congr rfl fun x' _ => by ring)

/-- The noise `W = Ŝq − Sq` has mean zero under `P(x, a, ·)`. -/
theorem noise_mean_zero (q : M.G → ℝ) (p : M.G) :
    ∑ x', (M.Shat q p x' - M.S q p) * M.P p.1.1 p.1.2 x' = 0 := by
  simp only [sub_mul, Finset.sum_sub_distrib, M.Shat_unbiased, ← Finset.mul_sum,
    M.P_sum _ _ p.2, mul_one, sub_self]

/-- The Q-learning update (9.18) at the visited pair `p = (X_t, A_t)` with next state `x'`. -/
noncomputable def qUpdate [DecidableEq M.G] (q : M.G → ℝ) (p : M.G) (x' : X) (α : ℝ) :
    M.G → ℝ :=
  update q p ((1 - α) * q p + α * M.Shat q p x')

/-- (9.18) is the Robbins–Monro step `q + α(Ŝq − q)` at the visited pair (as (9.16)), and it
leaves every other entry unchanged. -/
theorem qUpdate_apply [DecidableEq M.G] (q : M.G → ℝ) (p : M.G) (x' : X) (α : ℝ) (p' : M.G) :
    M.qUpdate q p x' α p' = if p' = p then q p + α * (M.Shat q p x' - q p) else q p' := by
  unfold qUpdate
  by_cases h : p' = p
  · subst h
    simp only [update_self, ↓reduceIte]
    ring
  · simp only [update_of_ne h, h, ↓reduceIte]

end FiniteMDP

end SargentStachurski.ApproximationAndLearning
