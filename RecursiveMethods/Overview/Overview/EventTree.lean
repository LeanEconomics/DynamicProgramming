/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Overview.Basics
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The finite-horizon stochastic planner on an event tree

SLP Exercise 2.5, p. 18.

Shocks `z_1, …, z_T` are i.i.d., taking the values `a_1, …, a_n` with probabilities
`π_1, …, π_n`; `z_0` is known. In period `t` the planner has seen the history
`h = (z_1, …, z_t)`, coded as `h : Fin t → Fin n`, and chooses `c_t(h)` and `k_{t+1}(h)` subject
to `c_t + k_{t+1} ≤ z_t f(k_t)`.

* `finrank_plan` (Ex 2.5): a contingency plan lists `(c_t(h), k_{t+1}(h))` for every history, so
  the planner's feasible set lies in a Euclidean space of dimension `2(1 + n + n² + ⋯ + nᵀ)`.
* `sum_snoc`: summing over histories of length `t + 1` is summing over a history of length `t`
  and the next shock.
* `tree_euler_optimal` (Ex 2.5): the first-order conditions
  `U′(c_t(h)) = β ∑_j π_j a_j f′(k_{t+1}(h)) U′(c_{t+1}(h, j))` with `k_{T+1} = 0` are sufficient
  for an optimum over all feasible contingency plans.
-/

open Finset Set

namespace StokeyLucasPrescott.Overview

/-- **Ex 2.5.** The space of contingency plans `t ↦ (h ↦ (c_t(h), k_{t+1}(h)))`, `t = 0, …, T`, has
dimension `2 ∑_{t=0}^T nᵗ`. -/
theorem finrank_plan (n T : ℕ) :
    Module.finrank ℝ ((t : Fin (T + 1)) → (Fin t → Fin n) → ℝ × ℝ) =
      2 * ∑ t ∈ range (T + 1), n ^ t := by
  rw [Module.finrank_pi_fintype, mul_sum, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun t _ => ?_
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_prod, mul_comm]

/-- Histories of length `t + 1` are histories of length `t` followed by one more shock. -/
theorem sum_snoc {n t : ℕ} (φ : (Fin (t + 1) → Fin n) → ℝ) :
    ∑ g, φ g = ∑ h : Fin t → Fin n, ∑ j : Fin n, φ (Fin.snoc h j) := by
  rw [← (Fin.snocEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type, sum_comm]
  rfl

variable {n : ℕ}

/-- The probability of a history, `∏ π_{h_i}`. -/
def histProb (pr : Fin n → ℝ) {t : ℕ} (h : Fin t → Fin n) : ℝ := ∏ i, pr (h i)

theorem histProb_snoc (pr : Fin n → ℝ) {t : ℕ} (h : Fin t → Fin n) (j : Fin n) :
    histProb pr (Fin.snoc h j : Fin (t + 1) → Fin n) = histProb pr h * pr j := by
  simp [histProb, Fin.prod_univ_castSucc]

/-- The productivity shock after history `h`: `z₀` in period `0`, `a_{h_t}` afterwards. -/
def zOf (a : Fin n → ℝ) (z₀ : ℝ) : (t : ℕ) → (Fin t → Fin n) → ℝ
  | 0, _ => z₀
  | t + 1, g => a (g (Fin.last t))

/-- Capital entering period `t` after history `h`: `k₀`, then the choice `K_{t−1}` made at the
history's initial segment. -/
def kIn (k₀ : ℝ) (K : (t : ℕ) → (Fin t → Fin n) → ℝ) : (t : ℕ) → (Fin t → Fin n) → ℝ
  | 0, _ => k₀
  | t + 1, g => K t (Fin.init g)

/-- Consumption `c_t(h) = z_t f(k_t) − k_{t+1}(h)`. -/
def treeCons (a : Fin n → ℝ) (z₀ k₀ : ℝ) (f : ℝ → ℝ) (K : (t : ℕ) → (Fin t → Fin n) → ℝ)
    (t : ℕ) (h : Fin t → Fin n) : ℝ :=
  zOf a z₀ t h * f (kIn k₀ K t h) - K t h

/-- The marginal product of the capital entering period `t`: `0` in period `0` (capital is given)
and `f′(k_t(h))` afterwards. -/
def fdIn (f' : ℝ → ℝ) (Ks : (t : ℕ) → (Fin t → Fin n) → ℝ) : (t : ℕ) → (Fin t → Fin n) → ℝ
  | 0, _ => 0
  | t + 1, g => f' (Ks t (Fin.init g))

/-- Expected discounted utility `∑_{t=0}^T βᵗ ∑_h P(h) U(c_t(h))`. -/
def treeValue (pr a : Fin n → ℝ) (z₀ k₀ β : ℝ) (U f : ℝ → ℝ) (T : ℕ)
    (K : (t : ℕ) → (Fin t → Fin n) → ℝ) : ℝ :=
  ∑ t ∈ range (T + 1), β ^ t * ∑ h : Fin t → Fin n, histProb pr h * U (treeCons a z₀ k₀ f K t h)

/-- A contingency plan is feasible when every `k_{t+1}(h) ≥ 0` and every consumption lies in `D`. -/
def TreeFeasible (D : Set ℝ) (a : Fin n → ℝ) (z₀ k₀ : ℝ) (f : ℝ → ℝ) (T : ℕ)
    (K : (t : ℕ) → (Fin t → Fin n) → ℝ) : Prop :=
  ∀ t ≤ T, ∀ h : Fin t → Fin n, 0 ≤ K t h ∧ treeCons a z₀ k₀ f K t h ∈ D

/-- `∑_{t=0}^T (A_t − B_t) = A_0 − B_T` when `A_{t+1} = B_t`. -/
theorem sum_shift_telescope {A B : ℕ → ℝ} (T : ℕ) (h : ∀ t < T, A (t + 1) = B t) :
    ∑ t ∈ range (T + 1), (A t - B t) = A 0 - B T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih fun t ht => h t (by omega), h T (by omega)]
    ring

/-- **Ex 2.5 (sufficiency of the first-order conditions).** If `U` is concave on `D`, `f` concave
on `[0, ∞)`, probabilities and shocks are nonnegative, the plan `K*` is feasible with positive
capital, satisfies the stochastic Euler equations
`β ∑_j π_j a_j f′(k*_{t+1}(h)) U′(c*_{t+1}(h, j)) = U′(c*_t(h))` for `t < T` and `k*_{T+1} = 0`,
then it maximizes expected discounted utility over all feasible plans. -/
theorem tree_euler_optimal {D : Set ℝ} {U U' f f' : ℝ → ℝ} {pr a : Fin n → ℝ} {z₀ k₀ β : ℝ}
    {T : ℕ} {Ks : (t : ℕ) → (Fin t → Fin n) → ℝ}
    (hβ : 0 ≤ β) (hpr : ∀ j, 0 ≤ pr j) (ha : ∀ j, 0 ≤ a j) (hz₀ : 0 ≤ z₀)
    (hU : ConcaveOn ℝ D U) (hf : ConcaveOn ℝ (Ici 0) f)
    (hKs : TreeFeasible D a z₀ k₀ f T Ks) (hpos : ∀ t < T, ∀ h, 0 < Ks t h)
    (hUd : ∀ t ≤ T, ∀ h, HasDerivAt U (U' (treeCons a z₀ k₀ f Ks t h))
      (treeCons a z₀ k₀ f Ks t h))
    (hU'0 : ∀ t ≤ T, ∀ h, 0 ≤ U' (treeCons a z₀ k₀ f Ks t h))
    (hfd : ∀ t < T, ∀ h, HasDerivAt f (f' (Ks t h)) (Ks t h))
    (heuler : ∀ t < T, ∀ h : Fin t → Fin n,
      β * ∑ j, pr j * a j * f' (Ks t h) * U' (treeCons a z₀ k₀ f Ks (t + 1) (Fin.snoc h j)) =
        U' (treeCons a z₀ k₀ f Ks t h))
    (hT : ∀ h, Ks T h = 0) {K : (t : ℕ) → (Fin t → Fin n) → ℝ}
    (hK : TreeFeasible D a z₀ k₀ f T K) :
    treeValue pr a z₀ k₀ β U f T K ≤ treeValue pr a z₀ k₀ β U f T Ks := by
  set cs := treeCons a z₀ k₀ f Ks
  set c := treeCons a z₀ k₀ f K
  have hprob : ∀ t (h : Fin t → Fin n), 0 ≤ histProb pr h := fun t h =>
    prod_nonneg fun i _ => hpr (h i)
  have hzOf : ∀ t (h : Fin t → Fin n), 0 ≤ zOf a z₀ t h := fun t h => by
    rcases t with _ | t
    · exact hz₀
    · exact ha _
  -- weight of node `(t, h)`
  set w : (t : ℕ) → (Fin t → Fin n) → ℝ := fun t h => β ^ t * histProb pr h * U' (cs t h)
  have hw : ∀ t ≤ T, ∀ h, 0 ≤ w t h := fun t ht h =>
    mul_nonneg (mul_nonneg (pow_nonneg hβ t) (hprob t h)) (hU'0 t ht h)
  -- `A_t`: the value of the capital entering `t`; `B_t`: the value of the capital chosen at `t`
  set A : ℕ → ℝ := fun t => ∑ h : Fin t → Fin n, w t h *
    (zOf a z₀ t h * fdIn f' Ks t h * (kIn k₀ K t h - kIn k₀ Ks t h))
  set B : ℕ → ℝ := fun t => ∑ h : Fin t → Fin n, w t h * (K t h - Ks t h)
  -- each node's utility gain is bounded by `A_t − B_t`
  have hnode : ∀ t ≤ T, β ^ t * ∑ h : Fin t → Fin n, histProb pr h * U (c t h) -
      β ^ t * ∑ h : Fin t → Fin n, histProb pr h * U (cs t h) ≤ A t - B t := by
    intro t ht
    simp only [A, B, ← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun h _ => ?_
    have h1 := concave_le_tangent hU (hKs t ht h).2 (hK t ht h).2 (hUd t ht h)
    -- the output term
    have hout : zOf a z₀ t h * (f (kIn k₀ K t h) - f (kIn k₀ Ks t h)) ≤
        zOf a z₀ t h * fdIn f' Ks t h * (kIn k₀ K t h - kIn k₀ Ks t h) := by
      rcases t with _ | t
      · simp [kIn, fdIn]
      · simp only [kIn, fdIn]
        have hKs0 := hKs t (by omega) (Fin.init h)
        have hK0 := hK t (by omega) (Fin.init h)
        have := concave_le_tangent hf (Set.mem_Ici.2 (hpos t (by omega) (Fin.init h)).le)
          (Set.mem_Ici.2 hK0.1) (hfd t (by omega) (Fin.init h))
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) (hzOf _ h)
    have hcdiff : c t h - cs t h = zOf a z₀ t h * (f (kIn k₀ K t h) - f (kIn k₀ Ks t h)) -
        (K t h - Ks t h) := by simp only [c, cs, treeCons]; ring
    have h2 : U (c t h) - U (cs t h) ≤ U' (cs t h) *
        ((zOf a z₀ t h * fdIn f' Ks t h * (kIn k₀ K t h - kIn k₀ Ks t h)) - (K t h - Ks t h)) := by
      have := mul_le_mul_of_nonneg_left (show c t h - cs t h ≤
        zOf a z₀ t h * fdIn f' Ks t h * (kIn k₀ K t h - kIn k₀ Ks t h) - (K t h - Ks t h) by
          linarith) (hU'0 t ht h)
      simp only [c, cs] at h1 this ⊢
      linarith
    have hpw : 0 ≤ β ^ t * histProb pr h := mul_nonneg (pow_nonneg hβ t) (hprob t h)
    have := mul_le_mul_of_nonneg_left h2 hpw
    simp only [w]
    nlinarith
  -- the Euler equations make `A_{t+1} = B_t`
  have hAB : ∀ t < T, A (t + 1) = B t := by
    intro t ht
    simp only [A, B]
    rw [sum_snoc]
    refine sum_congr rfl fun h _ => ?_
    simp only [w, zOf, kIn, fdIn, Fin.init_snoc, Fin.snoc_last, histProb_snoc]
    have he := heuler t ht h
    calc ∑ j, β ^ (t + 1) * (histProb pr h * pr j) * U' (cs (t + 1) (Fin.snoc h j)) *
          (a j * f' (Ks t h) * (K t h - Ks t h))
        = β ^ t * histProb pr h * (K t h - Ks t h) *
            (β * ∑ j, pr j * a j * f' (Ks t h) * U' (cs (t + 1) (Fin.snoc h j))) := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun j _ => ?_
          ring
      _ = β ^ t * histProb pr h * U' (cs t h) * (K t h - Ks t h) := by rw [he]; ring
  have hA0 : A 0 = 0 := by simp [A, kIn, fdIn]
  have hBT : 0 ≤ B T := sum_nonneg fun h _ => by
    rw [hT h, sub_zero]
    exact mul_nonneg (hw T le_rfl h) (hK T le_rfl h).1
  have htel := sum_shift_telescope T hAB
  have hsum := sum_le_sum fun t (ht : t ∈ range (T + 1)) =>
    hnode t (Nat.lt_succ_iff.1 (mem_range.1 ht))
  rw [sum_sub_distrib, htel, hA0] at hsum
  unfold treeValue
  linarith

end StokeyLucasPrescott.Overview
