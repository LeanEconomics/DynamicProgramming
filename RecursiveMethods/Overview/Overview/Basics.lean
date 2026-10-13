/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The finite-horizon planning problem

SLP §2.1, pp. 10–11.

The planner chooses capital `k₁, …, k_{T+1}` given `k₀`, consuming `c_t = f(k_t) − k_{t+1}` and
maximizing `∑_{t=0}^T β^t U(c_t)` (problem (3)–(4)). The book observes that with a finite horizon
this is a standard concave program, solved exactly by the first-order and boundary conditions
(5)–(6). We prove the sufficiency half for any concave `U` and `f`:

* `concave_le_tangent`, `strictConcave_lt_tangent`: the tangent-line inequalities.
* `sum_telescope`: the telescoping identity behind every Euler-equation argument in Chapter 2.
* `euler_optimal`: a feasible path satisfying the Euler equation (5) and `k_{T+1} = 0` (6) is
  optimal; `euler_unique`: with `U` strictly concave it is the only optimum.
-/

open Finset Set

namespace StokeyLucasPrescott.Overview

/-- **The tangent-line inequality** for a concave function differentiable at `x`. -/
theorem concave_le_tangent {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ} (hf : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f f' x) : f y ≤ f x + f' * (y - x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    linarith
  · simp
  · have := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    linarith

/-- **The strict tangent-line inequality** for a strictly concave function. -/
theorem strictConcave_lt_tangent {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ} (hf : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hd : HasDerivAt f f' x) :
    f y < f x + f' * (y - x) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have := hf.slope_lt_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_lt_iff₀ (sub_pos.2 h)] at this
    linarith
  · have := hf.lt_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, lt_div_iff₀ (sub_pos.2 h)] at this
    linarith

/-- **Telescoping.** If `d₀ = 0` and `a_t g_t = a_{t−1}` for `1 ≤ t ≤ n`, then
`∑_{t=0}^n a_t (g_t d_t − d_{t+1}) = −a_n d_{n+1}`. -/
theorem sum_telescope {a g d : ℕ → ℝ} (hd0 : d 0 = 0) (n : ℕ)
    (hag : ∀ t, 1 ≤ t → t ≤ n → a t * g t = a (t - 1)) :
    ∑ t ∈ range (n + 1), a t * (g t * d t - d (t + 1)) = -(a n * d (n + 1)) := by
  induction n with
  | zero => simp [hd0]
  | succ n ih =>
    rw [sum_range_succ, ih fun t h1 h2 => hag t h1 (by omega)]
    have h := hag (n + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at h
    linear_combination d (n + 1) * h

/-- The planner's objective `∑_{t=0}^T β^t U(f(k_t) − k_{t+1})`. -/
def planValue (β : ℝ) (U f : ℝ → ℝ) (T : ℕ) (k : ℕ → ℝ) : ℝ :=
  ∑ t ∈ range (T + 1), β ^ t * U (f (k t) - k (t + 1))

/-- A capital path is feasible from `k₀` when `k_{t+1} ≥ 0` and consumption lies in the domain `D`
of `U`, for `t = 0, …, T` (constraint (4) with no waste). -/
def Feasible (D : Set ℝ) (f : ℝ → ℝ) (T : ℕ) (k₀ : ℝ) (k : ℕ → ℝ) : Prop :=
  k 0 = k₀ ∧ ∀ t ≤ T, 0 ≤ k (t + 1) ∧ f (k t) - k (t + 1) ∈ D

/-- **The Euler equation and boundary condition are sufficient** (SLP (5)–(6), p. 11): if `U` is
concave on `D`, `f` concave on `[0, ∞)`, `k*` is feasible, and
`β f'(k*_t) U'(c*_t) = U'(c*_{t−1})` for `t = 1, …, T` with `k*_{T+1} = 0`, then `k*` is optimal. -/
theorem euler_optimal {D : Set ℝ} {U U' f f' : ℝ → ℝ} {β k₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ}
    (hβ : 0 ≤ β) (hU : ConcaveOn ℝ D U) (hf : ConcaveOn ℝ (Ici 0) f)
    (hks : Feasible D f T k₀ ks) (hk₀ : 0 ≤ k₀)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (f (ks t) - ks (t + 1))) (f (ks t) - ks (t + 1)))
    (hU'0 : ∀ t ≤ T, 0 ≤ U' (f (ks t) - ks (t + 1)))
    (hfd : ∀ t, 1 ≤ t → t ≤ T → HasDerivAt f (f' (ks t)) (ks t))
    (heuler : ∀ t, 1 ≤ t → t ≤ T →
      β * f' (ks t) * U' (f (ks t) - ks (t + 1)) = U' (f (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) {k : ℕ → ℝ} (hk : Feasible D f T k₀ k) :
    planValue β U f T k ≤ planValue β U f T ks := by
  set a : ℕ → ℝ := fun t => β ^ t * U' (f (ks t) - ks (t + 1))
  set d : ℕ → ℝ := fun t => k t - ks t
  have hd0 : d 0 = 0 := by simp only [d, hk.1, hks.1, sub_self]
  have hks0 : ∀ t ≤ T + 1, 0 ≤ ks t := fun t ht => by
    rcases t with _ | t
    · rw [hks.1]; exact hk₀
    · exact (hks.2 t (by omega)).1
  have hk0 : ∀ t ≤ T + 1, 0 ≤ k t := fun t ht => by
    rcases t with _ | t
    · rw [hk.1]; exact hk₀
    · exact (hk.2 t (by omega)).1
  -- term-by-term bound
  have hterm : ∀ t ∈ range (T + 1),
      β ^ t * U (f (k t) - k (t + 1)) - β ^ t * U (f (ks t) - ks (t + 1)) ≤
        a t * (f' (ks t) * d t - d (t + 1)) := fun t ht => by
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have hU1 := concave_le_tangent hU (hks.2 t htT).2 (hk.2 t htT).2 (hUd t htT)
    have hβt : 0 ≤ β ^ t := pow_nonneg hβ t
    have hfb : f (k t) - f (ks t) ≤ f' (ks t) * d t := by
      rcases t with _ | t
      · simp [d, hk.1, hks.1]
      · have := concave_le_tangent hf (Set.mem_Ici.2 (hks0 (t + 1) (by omega)))
          (Set.mem_Ici.2 (hk0 (t + 1) (by omega))) (hfd (t + 1) (by omega) htT)
        simp only [d]
        linarith
    have hstep : U (f (k t) - k (t + 1)) - U (f (ks t) - ks (t + 1)) ≤
        U' (f (ks t) - ks (t + 1)) * (f' (ks t) * d t - d (t + 1)) := by
      have h2 := mul_le_mul_of_nonneg_left
        (show (f (k t) - k (t + 1)) - (f (ks t) - ks (t + 1)) ≤ f' (ks t) * d t - d (t + 1) by
          simp only [d]; linarith) (hU'0 t htT)
      linarith
    have := mul_le_mul_of_nonneg_left hstep hβt
    simp only [a]
    nlinarith
  have htel := sum_telescope (a := a) (g := fun t => f' (ks t)) (d := d) hd0 T fun t h1 h2 => by
    simp only [a]
    have he := heuler t h1 h2
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at he ⊢
    rw [pow_succ]
    linear_combination β ^ s * he
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, htel] at hsum
  have hlast : 0 ≤ a T * d (T + 1) := by
    have hdT : d (T + 1) = k (T + 1) := by simp only [d, hT, sub_zero]
    rw [hdT]
    exact mul_nonneg (mul_nonneg (pow_nonneg hβ T) (hU'0 T le_rfl)) (hk0 _ le_rfl)
  unfold planValue
  linarith

/-- **The optimum is unique** (SLP p. 11): with `U` strictly concave and `β > 0`, a feasible path
attaining the value of an Euler path `k*` coincides with it. -/
theorem euler_unique {D : Set ℝ} {U U' f f' : ℝ → ℝ} {β k₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ}
    (hβ : 0 < β) (hU : StrictConcaveOn ℝ D U) (hf : ConcaveOn ℝ (Ici 0) f)
    (hks : Feasible D f T k₀ ks) (hk₀ : 0 ≤ k₀)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (f (ks t) - ks (t + 1))) (f (ks t) - ks (t + 1)))
    (hU'0 : ∀ t ≤ T, 0 ≤ U' (f (ks t) - ks (t + 1)))
    (hfd : ∀ t, 1 ≤ t → t ≤ T → HasDerivAt f (f' (ks t)) (ks t))
    (heuler : ∀ t, 1 ≤ t → t ≤ T →
      β * f' (ks t) * U' (f (ks t) - ks (t + 1)) = U' (f (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) {k : ℕ → ℝ} (hk : Feasible D f T k₀ k)
    (heq : planValue β U f T ks ≤ planValue β U f T k) :
    ∀ t ≤ T + 1, k t = ks t := by
  -- first, all consumptions coincide
  set a : ℕ → ℝ := fun t => β ^ t * U' (f (ks t) - ks (t + 1))
  set d : ℕ → ℝ := fun t => k t - ks t
  have hd0 : d 0 = 0 := by simp only [d, hk.1, hks.1, sub_self]
  have hks0 : ∀ t ≤ T + 1, 0 ≤ ks t := fun t ht => by
    rcases t with _ | t
    · rw [hks.1]; exact hk₀
    · exact (hks.2 t (by omega)).1
  have hk0 : ∀ t ≤ T + 1, 0 ≤ k t := fun t ht => by
    rcases t with _ | t
    · rw [hk.1]; exact hk₀
    · exact (hk.2 t (by omega)).1
  -- the gap on each term, with the strict inequality where consumptions differ
  have hgap : ∀ t ∈ range (T + 1),
      β ^ t * U (f (k t) - k (t + 1)) - β ^ t * U (f (ks t) - ks (t + 1)) ≤
        a t * (f' (ks t) * d t - d (t + 1)) := fun t ht => by
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have hU1 := concave_le_tangent hU.concaveOn (hks.2 t htT).2 (hk.2 t htT).2 (hUd t htT)
    have hβt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have hfb : f (k t) - f (ks t) ≤ f' (ks t) * d t := by
      rcases t with _ | t
      · simp [d, hk.1, hks.1]
      · have := concave_le_tangent hf (Set.mem_Ici.2 (hks0 (t + 1) (by omega)))
          (Set.mem_Ici.2 (hk0 (t + 1) (by omega))) (hfd (t + 1) (by omega) htT)
        simp only [d]
        linarith
    have h2 := mul_le_mul_of_nonneg_left
      (show (f (k t) - k (t + 1)) - (f (ks t) - ks (t + 1)) ≤ f' (ks t) * d t - d (t + 1) by
        simp only [d]; linarith) (hU'0 t htT)
    have := mul_le_mul_of_nonneg_left
      (show U (f (k t) - k (t + 1)) - U (f (ks t) - ks (t + 1)) ≤
        U' (f (ks t) - ks (t + 1)) * (f' (ks t) * d t - d (t + 1)) by linarith) hβt
    simp only [a]
    nlinarith
  have htel := sum_telescope (a := a) (g := fun t => f' (ks t)) (d := d) hd0 T fun t h1 h2 => by
    simp only [a]
    have he := heuler t h1 h2
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at he ⊢
    rw [pow_succ]
    linear_combination β ^ s * he
  have hlast : 0 ≤ a T * d (T + 1) := by
    have hdT : d (T + 1) = k (T + 1) := by simp only [d, hT, sub_zero]
    rw [hdT]
    exact mul_nonneg (mul_nonneg (pow_nonneg hβ.le T) (hU'0 T le_rfl)) (hk0 _ le_rfl)
  -- every term's gap is zero, so every consumption coincides
  have hc : ∀ t ≤ T, f (k t) - k (t + 1) = f (ks t) - ks (t + 1) := by
    by_contra hne
    push Not at hne
    obtain ⟨t₀, ht₀, hne⟩ := hne
    have hstrict : β ^ t₀ * U (f (k t₀) - k (t₀ + 1)) - β ^ t₀ * U (f (ks t₀) - ks (t₀ + 1)) <
        a t₀ * (f' (ks t₀) * d t₀ - d (t₀ + 1)) := by
      have hU1 := strictConcave_lt_tangent hU (hks.2 t₀ ht₀).2 (hk.2 t₀ ht₀).2 (Ne.symm hne)
        (hUd t₀ ht₀)
      have hβt : 0 < β ^ t₀ := pow_pos hβ t₀
      have hfb : f (k t₀) - f (ks t₀) ≤ f' (ks t₀) * d t₀ := by
        rcases t₀ with _ | t
        · simp [d, hk.1, hks.1]
        · have := concave_le_tangent hf (Set.mem_Ici.2 (hks0 (t + 1) (by omega)))
            (Set.mem_Ici.2 (hk0 (t + 1) (by omega))) (hfd (t + 1) (by omega) ht₀)
          simp only [d]
          linarith
      have h2 := mul_le_mul_of_nonneg_left
        (show (f (k t₀) - k (t₀ + 1)) - (f (ks t₀) - ks (t₀ + 1)) ≤
          f' (ks t₀) * d t₀ - d (t₀ + 1) by simp only [d]; linarith) (hU'0 t₀ ht₀)
      have := mul_lt_mul_of_pos_left
        (show U (f (k t₀) - k (t₀ + 1)) - U (f (ks t₀) - ks (t₀ + 1)) <
          U' (f (ks t₀) - ks (t₀ + 1)) * (f' (ks t₀) * d t₀ - d (t₀ + 1)) by linarith) hβt
      simp only [a]
      nlinarith
    have hsum := sum_lt_sum hgap ⟨t₀, mem_range.2 (Nat.lt_succ_of_le ht₀), hstrict⟩
    rw [sum_sub_distrib, htel] at hsum
    unfold planValue at heq
    linarith
  -- consumptions coincide, so capital coincides by induction
  intro t ht
  induction t with
  | zero => rw [hk.1, hks.1]
  | succ t ih =>
    have h := hc t (by omega)
    rw [ih (by omega)] at h
    linarith

end StokeyLucasPrescott.Overview
