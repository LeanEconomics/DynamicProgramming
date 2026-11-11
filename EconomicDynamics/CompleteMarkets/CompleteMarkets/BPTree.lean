/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The event tree of §§13.6–13.8

Miao, §13.1 (the event tree) as used in §13.6 (asset price bubbles, pp. 439–444), §13.7
(recursive formulation, p. 444) and Exercise 13.7 (p. 454).

A history `s^t = (s_1, …, s_t)` is a list `h : List S` of shocks over a finite shock set `S`,
the most recent shock first: the successors of `h` are the lists `s :: h`, the root `[]` is the
date-0 node and a date-`t` node is a list of length `t`. Probabilities `pr h = Pr(s^t)` are
strictly positive, `pr [] = 1` and `∑ₛ pr (s :: h) = pr h` (`BPTree`).

* `bp_nodeSum t g`: the sum of `g` over all date-`t` nodes (defined by recursion on `t`).
* `bp_condExp T j x h`: the conditional expectation `E_t[x_{t+j}]` at the date-`t` node `h`,
  `E_t[x_{t+j}] = ∑ₛ Pr(s | s^t) E_{t+1}[x_{t+j}]`.
* `bp_pv T δ t x = E[δ_t x_t]`: the date-0 value of a date-`t` payoff under the deflator `δ`.
* The tower property (`bp_condExp_add`), linearity and positivity of `bp_condExp`, and the law
  of iterated expectations `pr · E_t[x_{t+j}]` summed over date-`t` nodes `= E[x_{t+j}]`
  (`bp_nodeSum_condExp`).
* §13.7, p. 444: a Markov chain `P` with initial state `s₀` gives the probabilities
  `Pr(s^t) = Pr(s_t | s_{t−1}) ⋯ Pr(s_1 | s_0)` (`bp_markovPr`, `bp_markovTree`), and the
  conditional probability of `s_{t+1}` given `s^t` depends only on `s_t` (`eq_13_7_markov`).
-/

namespace Miao.CompleteMarkets

/-- The event tree (Miao, §13.1, p. 415): histories are lists over the finite shock set `S`
(most recent shock first), with strictly positive, consistent probabilities. -/
structure BPTree (S : Type*) [Fintype S] where
  /-- `pr h = Pr(s^t)`. -/
  pr : List S → ℝ
  pr_pos : ∀ h, 0 < pr h
  pr_nil : pr [] = 1
  pr_cons : ∀ h, ∑ s, pr (s :: h) = pr h

/-- The sum of `g` over the date-`t` nodes of the tree. -/
def bp_nodeSum {S : Type*} [Fintype S] : ℕ → (List S → ℝ) → ℝ
  | 0, g => g []
  | t + 1, g => bp_nodeSum t (fun h => ∑ s, g (s :: h))

/-- The conditional expectation `E_t[x_{t+j}]` at the node `h` (Miao, §13.1). -/
noncomputable def bp_condExp {S : Type*} [Fintype S] (T : BPTree S) : ℕ → (List S → ℝ) → List S → ℝ
  | 0, x, h => x h
  | j + 1, x, h => ∑ s, T.pr (s :: h) / T.pr h * bp_condExp T j x (s :: h)

/-- The date-0 value `E[δ_t x_t]` of the date-`t` payoff `x` under the deflator `δ`. -/
def bp_pv {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ) (t : ℕ)
    (x : List S → ℝ) : ℝ :=
  bp_nodeSum t (fun h => T.pr h * δ h * x h)

theorem bp_nodeSum_zero {S : Type*} [Fintype S] (g : List S → ℝ) :
    bp_nodeSum 0 g = g [] := rfl

theorem bp_nodeSum_succ {S : Type*} [Fintype S] (t : ℕ) (g : List S → ℝ) :
    bp_nodeSum (t + 1) g = bp_nodeSum t (fun h => ∑ s, g (s :: h)) := rfl

/-- Only the values at date-`t` nodes matter. -/
theorem bp_nodeSum_congr {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ)
    (hfg : ∀ h : List S, h.length = t → f h = g h) : bp_nodeSum t f = bp_nodeSum t g := by
  induction t generalizing f g with
  | zero =>
    exact hfg [] rfl
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ]
    refine ih _ _ (fun h hh => Finset.sum_congr rfl (fun s _ => hfg _ ?_))
    simp [hh]

theorem bp_nodeSum_add {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ) :
    bp_nodeSum t (fun h => f h + g h) = bp_nodeSum t f + bp_nodeSum t g := by
  induction t generalizing f g with
  | zero => rfl
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ, bp_nodeSum_succ, ← ih]
    simp only [Finset.sum_add_distrib]

theorem bp_nodeSum_smul {S : Type*} [Fintype S] (t : ℕ) (a : ℝ) (f : List S → ℝ) :
    bp_nodeSum t (fun h => a * f h) = a * bp_nodeSum t f := by
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ, ← ih]
    simp only [Finset.mul_sum]

theorem bp_nodeSum_neg {S : Type*} [Fintype S] (t : ℕ) (f : List S → ℝ) :
    bp_nodeSum t (fun h => -f h) = -bp_nodeSum t f := by
  have := bp_nodeSum_smul t (-1) f
  simpa using this

theorem bp_nodeSum_sub {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ) :
    bp_nodeSum t (fun h => f h - g h) = bp_nodeSum t f - bp_nodeSum t g := by
  have h1 := bp_nodeSum_add t f (fun h => -g h)
  rw [bp_nodeSum_neg] at h1
  simpa [sub_eq_add_neg] using h1

theorem bp_nodeSum_finsetSum {S : Type*} [Fintype S] {ι : Type*} (A : Finset ι) (t : ℕ)
    (f : ι → List S → ℝ) :
    bp_nodeSum t (fun h => ∑ i ∈ A, f i h) = ∑ i ∈ A, bp_nodeSum t (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simpa using bp_nodeSum_smul t 0 (fun _ => (0 : ℝ))
  | insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    rw [bp_nodeSum_add, ih]

theorem bp_nodeSum_const {S : Type*} [Fintype S] (T : BPTree S) (t : ℕ) (a : ℝ) :
    bp_nodeSum t (fun h => T.pr h * a) = a := by
  induction t generalizing a with
  | zero => simp [bp_nodeSum_zero, T.pr_nil]
  | succ t ih =>
    rw [bp_nodeSum_succ]
    simp only [← Finset.sum_mul, T.pr_cons]
    exact ih a

theorem bp_nodeSum_mono {S : Type*} [Fintype S] (t : ℕ) (f g : List S → ℝ)
    (hfg : ∀ h, f h ≤ g h) : bp_nodeSum t f ≤ bp_nodeSum t g := by
  induction t generalizing f g with
  | zero => exact hfg []
  | succ t ih =>
    rw [bp_nodeSum_succ, bp_nodeSum_succ]
    exact ih _ _ (fun h => Finset.sum_le_sum (fun s _ => hfg _))

theorem bp_nodeSum_nonneg {S : Type*} [Fintype S] (t : ℕ) (f : List S → ℝ)
    (hf : ∀ h, 0 ≤ f h) : 0 ≤ bp_nodeSum t f := by
  have := bp_nodeSum_mono t (fun _ => (0 : ℝ)) f hf
  have h0 : bp_nodeSum t (fun _ : List S => (0 : ℝ)) = 0 := by
    simpa using bp_nodeSum_smul t 0 (fun _ : List S => (0 : ℝ))
  linarith

/-- A sum of nonnegative terms over the date-`t` nodes vanishes only if every term does. -/
theorem bp_nodeSum_eq_zero_iff {S : Type*} [Fintype S] (t : ℕ) (f : List S → ℝ)
    (hf : ∀ h, 0 ≤ f h) (h0 : bp_nodeSum t f = 0) : ∀ h : List S, h.length = t → f h = 0 := by
  induction t generalizing f with
  | zero =>
    intro h hh
    rw [List.length_eq_zero_iff] at hh
    subst hh
    exact h0
  | succ t ih =>
    intro h hh
    obtain ⟨s, h', rfl⟩ : ∃ s h', h = s :: h' := by
      cases h with
      | nil => simp at hh
      | cons s h' => exact ⟨s, h', rfl⟩
    have hh' : h'.length = t := by simpa using hh
    have key := ih (fun g => ∑ s, f (s :: g))
      (fun g => Finset.sum_nonneg (fun s _ => hf _)) h0 h' hh'
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => hf _)).1 key s (Finset.mem_univ s)

/-- A single date-`t` node contributes its value. -/
theorem bp_nodeSum_single {S : Type*} [Fintype S] [DecidableEq S] (t : ℕ) (h₀ : List S)
    (hh₀ : h₀.length = t) (v : ℝ) :
    bp_nodeSum t (fun h => if h = h₀ then v else 0) = v := by
  induction t generalizing h₀ v with
  | zero =>
    rw [List.length_eq_zero_iff] at hh₀
    subst hh₀
    simp [bp_nodeSum_zero]
  | succ t ih =>
    obtain ⟨s₀, g₀, rfl⟩ : ∃ s g, h₀ = s :: g := by
      cases h₀ with
      | nil => simp at hh₀
      | cons s g => exact ⟨s, g, rfl⟩
    have hg : g₀.length = t := by simpa using hh₀
    rw [bp_nodeSum_succ]
    have : (fun h : List S => ∑ s, (if s :: h = s₀ :: g₀ then v else 0)) =
        fun h => if h = g₀ then v else 0 := by
      funext h
      by_cases hh : h = g₀
      · subst hh
        simp
      · simp [hh]
    rw [this]
    exact ih g₀ hg v

theorem bp_condExp_zero {S : Type*} [Fintype S] (T : BPTree S) (x : List S → ℝ)
    (h : List S) : bp_condExp T 0 x h = x h := rfl

theorem bp_condExp_succ {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x : List S → ℝ)
    (h : List S) :
    bp_condExp T (j + 1) x h = ∑ s, T.pr (s :: h) / T.pr h * bp_condExp T j x (s :: h) := rfl

/-- The tower property: `E_t[E_{t+j}[x_{t+j+k}]] = E_t[x_{t+j+k}]`. -/
theorem bp_condExp_add {S : Type*} [Fintype S] (T : BPTree S) (j k : ℕ) (x : List S → ℝ)
    (h : List S) : bp_condExp T (j + k) x h = bp_condExp T j (bp_condExp T k x) h := by
  induction j generalizing h with
  | zero => simp [bp_condExp_zero]
  | succ j ih =>
    rw [show j + 1 + k = (j + k) + 1 by omega, bp_condExp_succ, bp_condExp_succ]
    exact Finset.sum_congr rfl (fun s _ => by rw [ih])

theorem bp_condExp_congr {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x y : List S → ℝ)
    (hxy : ∀ g, x g = y g) (h : List S) : bp_condExp T j x h = bp_condExp T j y h := by
  rw [show x = y from funext hxy]

theorem bp_condExp_add_fun {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ)
    (x y : List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => x g + y g) h = bp_condExp T j x h + bp_condExp T j y h := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    simp only [bp_condExp_succ, ih, mul_add, Finset.sum_add_distrib]

theorem bp_condExp_smul {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (a : ℝ)
    (x : List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => a * x g) h = a * bp_condExp T j x h := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    simp only [bp_condExp_succ, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)

theorem bp_condExp_sub_fun {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ)
    (x y : List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => x g - y g) h = bp_condExp T j x h - bp_condExp T j y h := by
  have h1 := bp_condExp_add_fun T j x (fun g => (-1) * y g) h
  rw [bp_condExp_smul] at h1
  simpa [sub_eq_add_neg] using h1

theorem bp_condExp_const {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (a : ℝ)
    (h : List S) : bp_condExp T j (fun _ => a) h = a := by
  induction j generalizing h with
  | zero => rfl
  | succ j ih =>
    simp only [bp_condExp_succ, ih]
    rw [← Finset.sum_mul, ← Finset.sum_div, T.pr_cons, div_self (T.pr_pos h).ne', one_mul]

theorem bp_condExp_mono {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x y : List S → ℝ)
    (hxy : ∀ g, x g ≤ y g) (h : List S) : bp_condExp T j x h ≤ bp_condExp T j y h := by
  induction j generalizing h with
  | zero => exact hxy h
  | succ j ih =>
    simp only [bp_condExp_succ]
    refine Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (ih _) ?_)
    exact div_nonneg (T.pr_pos _).le (T.pr_pos _).le

theorem bp_condExp_nonneg {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x : List S → ℝ)
    (hx : ∀ g, 0 ≤ x g) (h : List S) : 0 ≤ bp_condExp T j x h := by
  have := bp_condExp_mono T j (fun _ => 0) x hx h
  rwa [bp_condExp_const] at this

theorem bp_condExp_finsetSum {S : Type*} [Fintype S] (T : BPTree S) {ι : Type*}
    (A : Finset ι) (j : ℕ) (x : ι → List S → ℝ) (h : List S) :
    bp_condExp T j (fun g => ∑ i ∈ A, x i g) h = ∑ i ∈ A, bp_condExp T j (x i) h := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using bp_condExp_const T j 0 h
  | insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    rw [bp_condExp_add_fun, ih]

/-- The law of iterated expectations on the tree: summing `Pr(s^t) E_t[x_{t+j}]` over the
date-`t` nodes gives `E[x_{t+j}]`. -/
theorem bp_nodeSum_condExp {S : Type*} [Fintype S] (T : BPTree S) (t j : ℕ)
    (x : List S → ℝ) :
    bp_nodeSum t (fun h => T.pr h * bp_condExp T j x h) =
      bp_nodeSum (t + j) (fun h => T.pr h * x h) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    have hstep : (fun h => T.pr h * bp_condExp T (j + 1) x h) =
        fun h => ∑ s, T.pr (s :: h) * bp_condExp T j x (s :: h) := by
      funext h
      rw [bp_condExp_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      field_simp [(T.pr_pos h).ne']
    rw [hstep, ← bp_nodeSum_succ t (fun g => T.pr g * bp_condExp T j x g), ih (t + 1)]
    rw [show t + 1 + j = t + (j + 1) by omega]

/-- At the root, `E_0[x_j] = E[x_j]`. -/
theorem bp_condExp_root {S : Type*} [Fintype S] (T : BPTree S) (j : ℕ) (x : List S → ℝ) :
    bp_condExp T j x [] = bp_nodeSum j (fun h => T.pr h * x h) := by
  have := bp_nodeSum_condExp T 0 j x
  rw [bp_nodeSum_zero, T.pr_nil, one_mul, zero_add] at this
  exact this

theorem bp_pv_add {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ) (t : ℕ)
    (x y : List S → ℝ) :
    bp_pv T δ t (fun h => x h + y h) = bp_pv T δ t x + bp_pv T δ t y := by
  unfold bp_pv
  rw [← bp_nodeSum_add]
  congr 1
  funext h
  ring

theorem bp_pv_mono {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ)
    (hδ : ∀ h, 0 ≤ δ h) (t : ℕ) (x y : List S → ℝ) (hxy : ∀ h, x h ≤ y h) :
    bp_pv T δ t x ≤ bp_pv T δ t y := by
  unfold bp_pv
  refine bp_nodeSum_mono t _ _ (fun h => ?_)
  exact mul_le_mul_of_nonneg_left (hxy h) (mul_nonneg (T.pr_pos h).le (hδ h))

theorem bp_pv_nonneg {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ)
    (hδ : ∀ h, 0 ≤ δ h) (t : ℕ) (x : List S → ℝ) (hx : ∀ h, 0 ≤ x h) :
    0 ≤ bp_pv T δ t x :=
  bp_nodeSum_nonneg t _ (fun h => mul_nonneg (mul_nonneg (T.pr_pos h).le (hδ h)) (hx h))

theorem bp_pv_finsetSum {S : Type*} [Fintype S] (T : BPTree S) (δ : List S → ℝ)
    {ι : Type*} (A : Finset ι) (t : ℕ) (x : ι → List S → ℝ) :
    bp_pv T δ t (fun h => ∑ i ∈ A, x i h) = ∑ i ∈ A, bp_pv T δ t (x i) := by
  unfold bp_pv
  rw [← bp_nodeSum_finsetSum]
  congr 1
  funext h
  rw [Finset.mul_sum]

/-- The probabilities generated by a Markov chain `P` with initial state `s₀` (Miao, §13.7,
p. 444): `Pr(s_{t+1}, s^t) = Pr(s_{t+1} | s_t) Pr(s^t)`. -/
def bp_markovPr {S : Type*} (P : S → S → ℝ) (s₀ : S) : List S → ℝ
  | [] => 1
  | s :: h => P (h.headD s₀) s * bp_markovPr P s₀ h

/-- A strictly positive stochastic matrix generates an event tree. -/
def bp_markovTree {S : Type*} [Fintype S] (P : S → S → ℝ) (s₀ : S)
    (hP : ∀ a b, 0 < P a b) (hrow : ∀ a, ∑ b, P a b = 1) : BPTree S where
  pr := bp_markovPr P s₀
  pr_pos := by
    intro h
    induction h with
    | nil => simp [bp_markovPr]
    | cons s h ih => exact mul_pos (hP _ _) ih
  pr_nil := rfl
  pr_cons := by
    intro h
    simp only [bp_markovPr, ← Finset.sum_mul, hrow, one_mul]

/-- Miao, §13.7, p. 444: `Pr(s^t) = Pr(s_t | s_{t−1}) Pr(s_{t−1} | s_{t−2}) ⋯ Pr(s_1 | s_0)`,
written recursively, and the conditional probability `Pr(s_{t+1} | s^t)` of the next shock
equals the transition probability `Pr(s_{t+1} | s_t)`. -/
theorem eq_13_7_markov {S : Type*} [Fintype S] (P : S → S → ℝ) (s₀ : S)
    (hP : ∀ a b, 0 < P a b) (hrow : ∀ a, ∑ b, P a b = 1) (s : S) (h : List S) :
    (bp_markovTree P s₀ hP hrow).pr (s :: h) =
        P (h.headD s₀) s * (bp_markovTree P s₀ hP hrow).pr h ∧
      (bp_markovTree P s₀ hP hrow).pr (s :: h) / (bp_markovTree P s₀ hP hrow).pr h =
        P (h.headD s₀) s := by
  refine ⟨rfl, ?_⟩
  have hpos := (bp_markovTree P s₀ hP hrow).pr_pos h
  rw [show (bp_markovTree P s₀ hP hrow).pr (s :: h) =
    P (h.headD s₀) s * (bp_markovTree P s₀ hP hrow).pr h from rfl]
  field_simp

/-- The deterministic tree: one shock, probability one at every node. -/
def bp_detTree : BPTree Unit where
  pr := fun _ => 1
  pr_pos := fun _ => one_pos
  pr_nil := rfl
  pr_cons := fun _ => by simp

end Miao.CompleteMarkets
