/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.Span
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Order.Field

/-!
# Finite MDPs, constant shifts and the span contraction

White (1963); Morton and Wecker (1977); Bray (2019, *Quantitative Economics*).

A finite MDP with feasible actions `Γ(s)`, reward `r`, transitions `P` and discount
`β ∈ [0, 1]` (`β = 1` is the average-reward case). With `Tv(s) = max_{a ∈ Γ(s)} Q_v(s, a)`:

* `T_add_const`, `T_iterate_add_const`: `T(v + c) = Tv + βc`.
* `isGreedy_add_const_iff` (**White**): greedy policies ignore constant shifts of `v`.
* `rel`, `relT_iterate` (**relative value iteration**): with `rel(v) = v − v(s₀)`, iterating
  `v ↦ rel(Tv)` gives `rel(Tⁿv)` (Bray's Lemma 4): relative value iteration tracks value
  iteration up to a constant, at no cost.
* `sp_T_sub_le` (**the span contraction**): if `α` bounds the Dobrushin coefficient
  `1 − ∑_t min(P(s, a, t), P(s', a', t))` over all feasible state–action pairs, then
  `sp(Tv − Tw) ≤ βα·sp(v − w)`.
* For `β < 1`: `T` and the policy operators are sup-norm contractions with fixed points `v*`
  and `v_σ`, ordered by monotonicity (`vstar_le_of_T_le`, `le_vσ_of_le`, `vσ_le_vstar`).
-/

open Finset Filter Topology

namespace DPExtensions.RelativeValueIteration

variable (S A : Type*) [Fintype S] in
/-- A finite Markov decision process with discount factor `β ∈ [0, 1]`. -/
structure MDP where
  /-- feasible actions -/
  Γ : S → Finset A
  Γ_nonempty : ∀ s, (Γ s).Nonempty
  /-- rewards -/
  r : S → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_le_one : β ≤ 1
  /-- transition probabilities -/
  P : S → A → S → ℝ
  P_nonneg : ∀ s a t, 0 ≤ P s a t
  P_sum : ∀ s a, ∑ t, P s a t = 1

namespace MDP

variable {S A : Type*} [Fintype S] (M : MDP S A)

/-- The action value `Q_v(s, a) = r(s, a) + β∑_t P(s, a, t)v(t)`. -/
def Q (v : S → ℝ) (s : S) (a : A) : ℝ := M.r s a + M.β * ∑ t, M.P s a t * v t

/-- The Bellman operator. -/
noncomputable def T (v : S → ℝ) (s : S) : ℝ := (M.Γ s).sup' (M.Γ_nonempty s) (M.Q v s)

/-- The policy operator of a decision rule `σ`. -/
def Tσ (σ : S → A) (v : S → ℝ) (s : S) : ℝ := M.Q v s (σ s)

/-- `σ` is greedy for `v`. -/
def IsGreedy (σ : S → A) (v : S → ℝ) : Prop :=
  ∀ s, σ s ∈ M.Γ s ∧ ∀ a ∈ M.Γ s, M.Q v s a ≤ M.Q v s (σ s)

/-- `σ` is feasible. -/
def IsPolicy (σ : S → A) : Prop := ∀ s, σ s ∈ M.Γ s

theorem exists_greedyAct (v : S → ℝ) (s : S) :
    ∃ a ∈ M.Γ s, M.T v s = M.Q v s a ∧ ∀ b ∈ M.Γ s, M.Q v s b ≤ M.Q v s a := by
  obtain ⟨a, ha, hmax⟩ := exists_max_image (M.Γ s) (M.Q v s) (M.Γ_nonempty s)
  exact ⟨a, ha, le_antisymm (sup'_le _ _ hmax) (le_sup' (M.Q v s) ha), hmax⟩

theorem exists_greedy (v : S → ℝ) : ∃ σ, M.IsGreedy σ v := by
  choose σ hσ using M.exists_greedyAct v
  exact ⟨σ, fun s => ⟨(hσ s).1, (hσ s).2.2⟩⟩

theorem Q_le_T (v : S → ℝ) {s : S} {a : A} (ha : a ∈ M.Γ s) : M.Q v s a ≤ M.T v s :=
  le_sup' (M.Q v s) ha

theorem Tσ_eq_T_of_greedy {σ : S → A} {v : S → ℝ} (h : M.IsGreedy σ v) : M.Tσ σ v = M.T v :=
  funext fun s => le_antisymm (M.Q_le_T v (h s).1) (sup'_le _ _ (h s).2)

theorem Tσ_le_T {σ : S → A} (hσ : M.IsPolicy σ) (v : S → ℝ) : M.Tσ σ v ≤ M.T v := fun s =>
  M.Q_le_T v (hσ s)

theorem Q_add_const (v : S → ℝ) (c : ℝ) (s : S) (a : A) :
    M.Q (fun t => v t + c) s a = M.Q v s a + M.β * c := by
  simp only [Q, mul_add, sum_add_distrib, ← sum_mul, M.P_sum, one_mul]
  ring

theorem T_add_const (v : S → ℝ) (c : ℝ) : M.T (fun t => v t + c) = fun s => M.T v s + M.β * c := by
  funext s
  simp only [T, Q_add_const]
  exact (sup'_add _ _ _ _).symm

theorem Tσ_add_const (σ : S → A) (v : S → ℝ) (c : ℝ) :
    M.Tσ σ (fun t => v t + c) = fun s => M.Tσ σ v s + M.β * c :=
  funext fun s => M.Q_add_const v c s (σ s)

/-- **White (1963)**: greedy policies are invariant to constant shifts of the value function. -/
theorem isGreedy_add_const_iff (σ : S → A) (v : S → ℝ) (c : ℝ) :
    M.IsGreedy σ (fun t => v t + c) ↔ M.IsGreedy σ v := by
  simp only [IsGreedy, Q_add_const, add_le_add_iff_right]

theorem T_iterate_add_const (v : S → ℝ) (c : ℝ) (n : ℕ) :
    M.T^[n] (fun t => v t + c) = fun s => M.T^[n] v s + M.β ^ n * c := by
  induction n generalizing v c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_add_const, ih, pow_succ']
    funext s
    ring

/-- The relative value function, normalized to `0` at the reference state `s₀`. -/
def rel (s₀ : S) (v : S → ℝ) (s : S) : ℝ := v s - v s₀

omit [Fintype S] in
theorem rel_add_const (s₀ : S) (v : S → ℝ) (c : ℝ) : rel s₀ (fun t => v t + c) = rel s₀ v := by
  funext s
  simp only [rel]
  ring

/-- **Relative value iteration is value iteration up to a constant** (Bray, 2019, Lemma 4):
iterating `v ↦ rel(Tv)` from `rel(v)` gives `rel(Tⁿv)`. -/
theorem relT_iterate (s₀ : S) (v : S → ℝ) (n : ℕ) :
    (fun w => rel s₀ (M.T w))^[n] (rel s₀ v) = rel s₀ (M.T^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    have e : rel s₀ (M.T^[n] v) = fun t => M.T^[n] v t + -M.T^[n] v s₀ := by
      funext t
      simp only [rel]
      ring
    rw [e, T_add_const, rel_add_const]

theorem Q_sub_Q (v w : S → ℝ) (s : S) (a : A) :
    M.Q v s a - M.Q w s a = M.β * ∑ t, M.P s a t * (v t - w t) := by
  simp only [Q, mul_sub, sum_sub_distrib]
  ring

variable [Nonempty S]

/-- **The span contraction**: if `α` bounds `1 − ∑_t min(P(s, a, t), P(s', a', t))` over all
feasible pairs, then `sp(Tv − Tw) ≤ βα·sp(v − w)`. -/
theorem sp_T_sub_le {α : ℝ}
    (hα : ∀ s a s' a', a ∈ M.Γ s → a' ∈ M.Γ s' → 1 - ∑ t, min (M.P s a t) (M.P s' a' t) ≤ α)
    (v w : S → ℝ) :
    sp (fun s => M.T v s - M.T w s) ≤ M.β * α * sp (fun s => v s - w s) := by
  refine sp_le fun s s' => ?_
  obtain ⟨a, ha, hva, -⟩ := M.exists_greedyAct v s
  obtain ⟨a', ha', hwa', -⟩ := M.exists_greedyAct w s'
  have h1 : M.Q w s a ≤ M.T w s := M.Q_le_T w ha
  have h2 : M.Q v s' a' ≤ M.T v s' := M.Q_le_T v ha'
  have hd := dobrushin (M.P_sum s a) (M.P_sum s' a') (fun t => v t - w t)
  have hsp := sp_nonneg (fun t => v t - w t)
  have hc : (1 - ∑ t, min (M.P s a t) (M.P s' a' t)) * sp (fun t => v t - w t) ≤
      α * sp (fun t => v t - w t) := mul_le_mul_of_nonneg_right (hα s a s' a' ha ha') hsp
  have e1 := M.Q_sub_Q v w s a
  have e2 := M.Q_sub_Q v w s' a'
  have h3 := mul_le_mul_of_nonneg_left (hd.trans hc) M.β_nonneg
  nlinarith

end MDP

end DPExtensions.RelativeValueIteration
