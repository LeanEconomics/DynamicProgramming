import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.Order.MonotoneConvergence
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The finite-horizon log/Cobb–Douglas economy

SLP Exercise 2.2, p. 12: `f(k) = k^α`, `0 < α < 1`, `U(c) = ln c`.

* `euler_iff_z` (Ex 2.2a): with `z_t = k_t / k_{t−1}^α`, the Euler equation (5) becomes the
  first-order difference equation `αβ(1 − z_t) = z_t(1 − z_{t+1})`.
* `savingRate`, `savingRate_succ`, `z_unique` (Ex 2.2b): with `n` periods remaining,
  `s_n = αβ(1 − (αβ)ⁿ)/(1 − (αβ)ⁿ⁺¹)`; it is the unique solution with `s₀ = 0` (the boundary
  condition `z_{T+1} = 0`).
* `path`, `path_feasible`, `path_euler`, `path_optimal`, `path_unique` (Ex 2.2c): the path
  `k_{t+1} = s_{T−t} k_t^α` of (7) satisfies (5)–(6), and is therefore the unique optimum.
* `savingRate_tendsto` (equation (8), p. 12): `s_n → αβ`.
-/

open Finset Set Filter Topology Real

namespace StokeyLucasPrescott.Overview

/-- **Ex 2.2a.** With `A = k_{t−1}^α`, `B = k_t^α` and `z_t = k_t / A`, `z_{t+1} = k_{t+1} / B`,
the Euler equation `β α k_t^{α−1} / (k_t^α − k_{t+1}) = 1/(k_{t−1}^α − k_t)` is equivalent to
`αβ(1 − z_t) = z_t (1 − z_{t+1})`. -/
theorem euler_iff_z {α β a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a ^ α)
    (hbc : c < b ^ α) :
    β * (α * b ^ (α - 1)) * (b ^ α - c)⁻¹ = (a ^ α - b)⁻¹ ↔
      α * β * (1 - b / a ^ α) = b / a ^ α * (1 - c / b ^ α) := by
  have hA : 0 < a ^ α := rpow_pos_of_pos ha α
  have hB : 0 < b ^ α := rpow_pos_of_pos hb α
  have hb1 : b ^ (α - 1) = b ^ α / b := rpow_sub_one hb.ne' α
  rw [hb1]
  have h1 : (b ^ α - c) ≠ 0 := (sub_pos.2 hbc).ne'
  have h2 : (a ^ α - b) ≠ 0 := (sub_pos.2 hab).ne'
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination h
  · intro h
    field_simp at h ⊢
    linear_combination h

/-- The saving rate with `n` periods remaining, `s_n = αβ(1 − (αβ)ⁿ)/(1 − (αβ)ⁿ⁺¹)`. -/
noncomputable def savingRate (α β : ℝ) (n : ℕ) : ℝ :=
  α * β * (1 - (α * β) ^ n) / (1 - (α * β) ^ (n + 1))

theorem savingRate_zero (α β : ℝ) : savingRate α β 0 = 0 := by simp [savingRate]

/-- The backward recursion `s_{n+1} (1 + αβ − s_n) = αβ`. -/
theorem savingRate_succ {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (n : ℕ) :
    savingRate α β (n + 1) * (1 + α * β - savingRate α β n) = α * β := by
  have hp : ∀ m : ℕ, (α * β) ^ m < 1 → 1 - (α * β) ^ m ≠ 0 := fun m h => (sub_pos.2 h).ne'
  have hlt : ∀ m : ℕ, 0 < m → (α * β) ^ m < 1 := fun m hm => pow_lt_one₀ h0.le h1 hm.ne'
  have e1 := hp (n + 1) (hlt _ (by omega))
  have e2 := hp (n + 2) (hlt _ (by omega))
  simp only [savingRate]
  field_simp
  ring

theorem savingRate_pos {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {n : ℕ} (hn : 0 < n) :
    0 < savingRate α β n := by
  have := pow_lt_one₀ h0.le h1 hn.ne'
  have := pow_lt_one₀ h0.le h1 (n := n + 1) (by omega)
  unfold savingRate
  positivity

theorem savingRate_nonneg {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (n : ℕ) :
    0 ≤ savingRate α β n := by
  rcases n with _ | n
  · simp [savingRate_zero]
  · exact (savingRate_pos h0 h1 (Nat.succ_pos n)).le

theorem savingRate_lt_one {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (n : ℕ) :
    savingRate α β n < 1 := by
  have hn1 : (α * β) ^ (n + 1) < 1 := pow_lt_one₀ h0.le h1 (by omega)
  unfold savingRate
  rw [div_lt_one (sub_pos.2 hn1), pow_succ]
  have := pow_le_one₀ h0.le h1.le (n := n)
  nlinarith [pow_nonneg h0.le n]

/-- **Ex 2.2b.** The difference equation `αβ(1 − z_t) = z_t(1 − z_{t+1})` with the boundary
condition `z_{T+1} = 0` has the unique solution `z_t = s_{T+1−t}`. -/
theorem z_unique {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {z : ℕ → ℝ}
    (hT : z (T + 1) = 0) (hz : ∀ t, 1 ≤ t → t ≤ T → α * β * (1 - z t) = z t * (1 - z (t + 1))) :
    ∀ t, 1 ≤ t → t ≤ T + 1 → z t = savingRate α β (T + 1 - t) := by
  have key : ∀ n ≤ T, z (T + 1 - n) = savingRate α β n := by
    intro n hn
    induction n with
    | zero => simp [hT, savingRate_zero]
    | succ n ih =>
      have hih := ih (by omega)
      have hrec := hz (T - n) (by omega) (by omega)
      have heq : T - n + 1 = T + 1 - n := by omega
      rw [heq, hih] at hrec
      have hs := savingRate_succ h0 h1 n
      have hd : 1 + α * β - savingRate α β n ≠ 0 := by
        have := savingRate_lt_one h0 h1 n
        intro h; linarith
      have hidx : T + 1 - (n + 1) = T - n := by omega
      rw [hidx]
      have hprod : (z (T - n) - savingRate α β (n + 1)) * (1 + α * β - savingRate α β n) = 0 := by
        linear_combination -hrec - hs
      exact sub_eq_zero.1 ((mul_eq_zero.1 hprod).resolve_right hd)
  intro t ht1 htT
  have := key (T + 1 - t) (by omega)
  rwa [show T + 1 - (T + 1 - t) = t by omega] at this

/-- The path (7): `k₀` given, `k_{t+1} = s_{T−t} k_t^α`. -/
noncomputable def path (α β : ℝ) (T : ℕ) (k₀ : ℝ) : ℕ → ℝ
  | 0 => k₀
  | t + 1 => savingRate α β (T - t) * path α β T k₀ t ^ α

theorem path_pos {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {k₀ : ℝ} (hk₀ : 0 < k₀) :
    ∀ t ≤ T, 0 < path α β T k₀ t := by
  intro t ht
  induction t with
  | zero => exact hk₀
  | succ t ih =>
    have := ih (by omega)
    simp only [path]
    exact mul_pos (savingRate_pos h0 h1 (by omega)) (rpow_pos_of_pos this α)

theorem path_terminal {α β : ℝ} (T : ℕ) (k₀ : ℝ) : path α β T k₀ (T + 1) = 0 := by
  simp [path, savingRate_zero]

/-- Consumption along the path, `c_t = (1 − s_{T−t}) k_t^α`. -/
theorem path_consumption {α β : ℝ} (T : ℕ) (k₀ : ℝ) (t : ℕ) :
    path α β T k₀ t ^ α - path α β T k₀ (t + 1) =
      (1 - savingRate α β (T - t)) * path α β T k₀ t ^ α := by
  simp only [path]
  ring

/-- **Ex 2.2c (feasibility).** The path (7) is feasible with strictly positive consumption. -/
theorem path_feasible {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {k₀ : ℝ}
    (hk₀ : 0 < k₀) :
    Feasible (Ioi 0) (fun k => k ^ α) T k₀ (path α β T k₀) := by
  refine ⟨rfl, fun t ht => ⟨?_, ?_⟩⟩
  · simp only [path]
    exact mul_nonneg (savingRate_nonneg h0 h1 _) (rpow_nonneg (path_pos h0 h1 hk₀ t ht).le α)
  · rw [Set.mem_Ioi, path_consumption]
    exact mul_pos (sub_pos.2 (savingRate_lt_one h0 h1 _))
      (rpow_pos_of_pos (path_pos h0 h1 hk₀ t ht) α)

/-- **Ex 2.2c (Euler).** The path (7) satisfies the Euler equation (5) for `t = 1, …, T`. -/
theorem path_euler {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) {T : ℕ} {k₀ : ℝ}
    (hk₀ : 0 < k₀) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ T) :
    β * (α * path α β T k₀ t ^ (α - 1)) *
        (path α β T k₀ t ^ α - path α β T k₀ (t + 1))⁻¹ =
      (path α β T k₀ (t - 1) ^ α - path α β T k₀ t)⁻¹ := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hks := path_pos h0 h1 hk₀ (T := T) s (by omega)
  have hkt := path_pos h0 h1 hk₀ (s + 1) htT
  have hfe := path_feasible h0 h1 hk₀ (T := T)
  have hc1 := (hfe.2 s (by omega)).2
  have hc2 := (hfe.2 (s + 1) htT).2
  rw [Set.mem_Ioi] at hc1 hc2
  rw [euler_iff_z hks hkt (by linarith) (by linarith)]
  -- the ratios are saving rates
  have hz1 : path α β T k₀ (s + 1) / path α β T k₀ s ^ α = savingRate α β (T - s) := by
    simp only [path]
    field_simp [(rpow_pos_of_pos hks α).ne']
  have hz2 : path α β T k₀ (s + 1 + 1) / path α β T k₀ (s + 1) ^ α =
      savingRate α β (T - (s + 1)) := by
    conv_lhs => rw [path]
    field_simp [(rpow_pos_of_pos hkt α).ne']
  rw [hz1, hz2]
  have hrec := savingRate_succ h0 h1 (T - (s + 1))
  have hidx : T - (s + 1) + 1 = T - s := by omega
  rw [hidx] at hrec
  linarith

/-- **Ex 2.2c.** The path (7) is optimal: it maximizes `∑_{t=0}^T β^t ln(k_t^α − k_{t+1})` over
all feasible paths. -/
theorem path_optimal {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (h1 : α * β < 1)
    {T : ℕ} {k₀ : ℝ} (hk₀ : 0 < k₀) {k : ℕ → ℝ} (hk : Feasible (Ioi 0) (fun k => k ^ α) T k₀ k) :
    planValue β log (fun k => k ^ α) T k ≤ planValue β log (fun k => k ^ α) T (path α β T k₀) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hfe := path_feasible h0 h1 hk₀ (T := T)
  refine euler_optimal (U' := fun c => c⁻¹) (f' := fun k => α * k ^ (α - 1)) hβ.le
    strictConcaveOn_log_Ioi.concaveOn (strictConcaveOn_rpow hα hα1).concaveOn hfe hk₀.le
    (fun t ht => hasDerivAt_log (Set.mem_Ioi.1 (hfe.2 t ht).2).ne')
    (fun t ht => (inv_pos.2 (Set.mem_Ioi.1 (hfe.2 t ht).2)).le)
    (fun t _ ht2 => hasDerivAt_rpow_const (Or.inl (path_pos h0 h1 hk₀ t ht2).ne'))
    (fun t ht1 ht2 => by
      have := path_euler h0 h1 hk₀ t ht1 ht2
      simpa [mul_assoc] using this)
    (path_terminal T k₀) hk

/-- **Uniqueness** (SLP p. 11): the path (7) is the only optimum. -/
theorem path_unique {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (h1 : α * β < 1)
    {T : ℕ} {k₀ : ℝ} (hk₀ : 0 < k₀) {k : ℕ → ℝ} (hk : Feasible (Ioi 0) (fun k => k ^ α) T k₀ k)
    (hopt : planValue β log (fun k => k ^ α) T (path α β T k₀) ≤
      planValue β log (fun k => k ^ α) T k) :
    ∀ t ≤ T + 1, k t = path α β T k₀ t := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hfe := path_feasible h0 h1 hk₀ (T := T)
  exact euler_unique (U' := fun c => c⁻¹) (f' := fun k => α * k ^ (α - 1)) hβ
    strictConcaveOn_log_Ioi (strictConcaveOn_rpow hα hα1).concaveOn hfe hk₀.le
    (fun t ht => hasDerivAt_log (Set.mem_Ioi.1 (hfe.2 t ht).2).ne')
    (fun t ht => (inv_pos.2 (Set.mem_Ioi.1 (hfe.2 t ht).2)).le)
    (fun t _ ht2 => hasDerivAt_rpow_const (Or.inl (path_pos h0 h1 hk₀ t ht2).ne'))
    (fun t ht1 ht2 => by
      have := path_euler h0 h1 hk₀ t ht1 ht2
      simpa [mul_assoc] using this)
    (path_terminal T k₀) hk hopt

/-- **Equation (8).** As the horizon recedes the saving rate converges to `αβ`. -/
theorem savingRate_tendsto {α β : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) :
    Tendsto (savingRate α β) atTop (𝓝 (α * β)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  have hp1 : Tendsto (fun n : ℕ => (α * β) ^ (n + 1)) atTop (𝓝 0) :=
    hp.comp (tendsto_add_atTop_nat 1)
  have := ((tendsto_const_nhds (x := α * β)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp1) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  rw [show α * β * (1 - 0) / (1 - 0) = α * β by ring] at this
  exact this

end StokeyLucasPrescott.Overview

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The infinite-horizon log/Cobb–Douglas economy

SLP Exercise 2.3, p. 14, and equations (8)–(11), pp. 12–14.

With `f(k) = k^α`, `U(c) = ln c`, the conjectured optimal policy is `k_{t+1} = αβ k_t^α` (8).

* `logCapital` (Ex 2.3a): along (8), `ln k_t = αᵗ ln k₀ + ln(αβ)(1 − αᵗ)/(1 − α)`.
* `hasSum_value` (Ex 2.3a): the lifetime utility of (8) from `k₀` is
  `v(k₀) = A + B ln k₀`, `B = α/(1 − αβ)`,
  `A = [ln(1 − αβ) + αβ ln(αβ)/(1 − αβ)]/(1 − β)`.
* `bellman_le`, `bellman_attained`, `bellman_isGreatest`, `bellman_argmax_unique` (Ex 2.3b): `v`
  satisfies the functional equation (11), `v(k) = max_{0 < y < k^α} {ln(k^α − y) + βv(y)}`, and
  `y = αβk^α` is the unique maximizer, recovering (8).
-/

open Finset Set Filter Topology Real

namespace StokeyLucasPrescott.Overview

/-- The coefficient `B = α/(1 − αβ)`. -/
noncomputable def coefB (α β : ℝ) : ℝ := α / (1 - α * β)

/-- The constant `A = [ln(1 − αβ) + αβ ln(αβ)/(1 − αβ)]/(1 − β)`. -/
noncomputable def coefA (α β : ℝ) : ℝ :=
  (log (1 - α * β) + α * β / (1 - α * β) * log (α * β)) / (1 - β)

/-- The value function `v(k) = A + B ln k`. -/
noncomputable def logValue (α β k : ℝ) : ℝ := coefA α β + coefB α β * log k

/-- The capital path (8): `k_{t+1} = αβ k_t^α`. -/
noncomputable def cdPath (α β k₀ : ℝ) : ℕ → ℝ
  | 0 => k₀
  | t + 1 => α * β * cdPath α β k₀ t ^ α

theorem cdPath_pos {α β k₀ : ℝ} (h0 : 0 < α * β) (hk₀ : 0 < k₀) (t : ℕ) : 0 < cdPath α β k₀ t := by
  induction t with
  | zero => exact hk₀
  | succ t ih => exact mul_pos h0 (rpow_pos_of_pos ih α)

/-- **Ex 2.3a.** Along (8), `ln k_t = αᵗ ln k₀ + ln(αβ)(1 − αᵗ)/(1 − α)`. -/
theorem logCapital {α β k₀ : ℝ} (hα1 : α < 1) (h0 : 0 < α * β) (hk₀ : 0 < k₀) (t : ℕ) :
    log (cdPath α β k₀ t) = α ^ t * log k₀ + log (α * β) * (1 - α ^ t) / (1 - α) := by
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  induction t with
  | zero => simp [cdPath]
  | succ t ih =>
    simp only [cdPath]
    rw [log_mul h0.ne' (rpow_pos_of_pos (cdPath_pos h0 hk₀ t) α).ne',
      log_rpow (cdPath_pos h0 hk₀ t), ih]
    field_simp
    ring

/-- Consumption along (8) is `(1 − αβ) k_t^α`. -/
theorem cdPath_consumption (α β k₀ : ℝ) (t : ℕ) :
    cdPath α β k₀ t ^ α - cdPath α β k₀ (t + 1) = (1 - α * β) * cdPath α β k₀ t ^ α := by
  simp only [cdPath]
  ring

/-- **Ex 2.3a.** The lifetime utility `∑ βᵗ ln c_t` of the path (8) from `k₀` is `v(k₀)`. -/
theorem hasSum_value {α β k₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hk₀ : 0 < k₀) :
    HasSum (fun t => β ^ t * log (cdPath α β k₀ t ^ α - cdPath α β k₀ (t + 1)))
      (logValue α β k₀) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1 : α * β < 1 := by nlinarith
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  have h1ab : (1 - α * β) ≠ 0 := (sub_pos.2 h1).ne'
  -- per-period utility as a combination of geometric terms
  have hterm : ∀ t, β ^ t * log (cdPath α β k₀ t ^ α - cdPath α β k₀ (t + 1)) =
      (log (1 - α * β) + α * log (α * β) / (1 - α)) * β ^ t +
        (α * log k₀ - α * log (α * β) / (1 - α)) * (α * β) ^ t := fun t => by
    rw [cdPath_consumption, log_mul (sub_pos.2 h1).ne'
      (rpow_pos_of_pos (cdPath_pos h0 hk₀ t) α).ne', log_rpow (cdPath_pos h0 hk₀ t),
      logCapital hα1 h0 hk₀ t, mul_pow]
    field_simp
    ring
  have hg1 := hasSum_geometric_of_lt_one hβ.le hβ1
  have hg2 := hasSum_geometric_of_lt_one h0.le h1
  have hs := (hg1.mul_left (log (1 - α * β) + α * log (α * β) / (1 - α))).add
    (hg2.mul_left (α * log k₀ - α * log (α * β) / (1 - α)))
  convert hs using 1
  · funext t
    exact hterm t
  · simp only [logValue, coefA, coefB]
    field_simp
    ring

/-- The objective on the right of (11): `ln(k^α − y) + β v(y)`. -/
noncomputable def bellmanRHS (α β k y : ℝ) : ℝ := log (k ^ α - y) + β * logValue α β y

/-- **Ex 2.3b (upper bound).** For every feasible `y ∈ (0, k^α)`,
`ln(k^α − y) + βv(y) ≤ v(k)`. -/
theorem bellman_le {α β k y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1)
    (hk : 0 < k) (hy : 0 < y) (hyk : y < k ^ α) :
    bellmanRHS α β k y ≤ logValue α β k := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  set cs := (1 - α * β) * k ^ α
  set ys := α * β * k ^ α
  have hcs : 0 < cs := mul_pos h1ab hK
  have hys : 0 < ys := mul_pos h0 hK
  -- tangent lines of ln at `cs` and `ys`
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyk)) (hasDerivAt_log hcs.ne')
  have t2 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (hasDerivAt_log hys.ne')
  have hB : 0 ≤ β * coefB α β := mul_nonneg hβ.le (div_nonneg hα.le h1ab.le)
  -- the value at the maximizer
  have hval : log cs + β * logValue α β ys = logValue α β k := by
    simp only [cs, ys, logValue, coefA, coefB]
    rw [log_mul h1ab.ne' hK.ne', log_mul h0.ne' hK.ne', log_rpow hk]
    have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
    field_simp
    ring
  -- the linear terms cancel by the first-order condition
  have hfoc : cs⁻¹ * (k ^ α - y - cs) + β * coefB α β * (ys⁻¹ * (y - ys)) = 0 := by
    simp only [cs, ys, coefB]
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left t2 hB
  unfold bellmanRHS
  rw [← hval]
  simp only [logValue] at this ⊢
  nlinarith

/-- **Ex 2.3b (attainment).** The policy `y = αβk^α` attains `v(k)`. -/
theorem bellman_attained {α β k : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1)
    (hk : 0 < k) : bellmanRHS α β k (α * β * k ^ α) = logValue α β k := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  unfold bellmanRHS
  rw [show k ^ α - α * β * k ^ α = (1 - α * β) * k ^ α by ring]
  simp only [logValue, coefA, coefB]
  rw [log_mul h1ab.ne' hK.ne', log_mul h0.ne' hK.ne', log_rpow hk]
  field_simp
  ring

/-- **Ex 2.3b.** `v` satisfies the functional equation (11):
`v(k) = max_{0 < y < k^α} {ln(k^α − y) + βv(y)}`. -/
theorem bellman_isGreatest {α β k : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1)
    (hk : 0 < k) :
    IsGreatest (bellmanRHS α β k '' Ioo 0 (k ^ α)) (logValue α β k) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  refine ⟨⟨α * β * k ^ α, ⟨mul_pos h0 hK, by nlinarith⟩,
    bellman_attained hα hβ hβ1 h1 hk⟩, ?_⟩
  rintro _ ⟨y, ⟨hy0, hyk⟩, rfl⟩
  exact bellman_le hα hβ hβ1 h1 hk hy0 hyk

/-- **The maximizer is unique**: any `y` attaining `v(k)` is `αβk^α`, so (11) generates the
policy (8). -/
theorem bellman_argmax_unique {α β k y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hβ1 : β < 1)
    (h1 : α * β < 1) (hk : 0 < k) (hy : 0 < y) (hyk : y < k ^ α)
    (hmax : logValue α β k ≤ bellmanRHS α β k y) : y = α * β * k ^ α := by
  by_contra hne
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  set cs := (1 - α * β) * k ^ α
  set ys := α * β * k ^ α
  have hcs : 0 < cs := mul_pos h1ab hK
  have hys : 0 < ys := mul_pos h0 hK
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyk)) (hasDerivAt_log hcs.ne')
  have t2 := strictConcave_lt_tangent strictConcaveOn_log_Ioi (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (fun h => hne h.symm) (hasDerivAt_log hys.ne')
  have hB : 0 < β * coefB α β := mul_pos hβ (div_pos hα h1ab)
  have hval : log cs + β * logValue α β ys = logValue α β k := by
    simp only [cs, ys, logValue, coefA, coefB]
    rw [log_mul h1ab.ne' hK.ne', log_mul h0.ne' hK.ne', log_rpow hk]
    have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
    field_simp
    ring
  have hfoc : cs⁻¹ * (k ^ α - y - cs) + β * coefB α β * (ys⁻¹ * (y - ys)) = 0 := by
    simp only [cs, ys, coefB]
    field_simp
    ring
  have := mul_lt_mul_of_pos_left t2 hB
  unfold bellmanRHS at hmax
  rw [← hval] at hmax
  simp only [logValue] at this hmax
  nlinarith

end StokeyLucasPrescott.Overview

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The neoclassical technology

SLP §2.1, pp. 9–10, and Exercise 2.1, pp. 10–11.

Output is `F(k, n)` with `F` homogeneous of degree one, `F(0, n) = 0`, strictly increasing in
each input, strictly quasi-concave, and satisfying the Inada conditions in `k`. With depreciation
`0 < δ ≤ 1` and labour normalized to one, the total supply of goods is
`f(k) = F(k, 1) + (1 − δ)k`.

* `Neoclassical`: the book's assumptions on `F` (with strict quasi-concavity on the open
  quadrant; see `docs/corrections.md`).
* `strictConcaveOn_F` and Ex 2.1: `f` is continuously differentiable, strictly increasing and
  strictly concave, with `f(0) = 0`, `f′ > 0`, `f′(0+) = ∞` and `f′(∞) = 1 − δ`
  (`f_zero`, `hasDerivAt_f`, `continuousOn_f'`, `f'_pos`, `strictMonoOn_f`, `strictConcaveOn_f`,
  `f'_tendsto_zero`, `f'_tendsto_atTop`).
* `cobbDouglas_neoclassical`: `F(k, n) = k^α n^{1−α}` satisfies the assumptions, so they are
  consistent.
-/

open Set Filter Topology Real

namespace StokeyLucasPrescott.Overview

/-- The book's assumptions on the production function `F`, with `Fk` the marginal product of
capital at `n = 1`. Strict quasi-concavity is assumed on the open quadrant: on `ℝ²₊` it would
contradict `F(0, n) = 0`. -/
structure Neoclassical (F : ℝ → ℝ → ℝ) (Fk : ℝ → ℝ) : Prop where
  hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n
  zero_left : F 0 1 = 0
  deriv_k : ∀ k, 0 < k → HasDerivAt (fun k => F k 1) (Fk k) k
  cont_Fk : ContinuousOn Fk (Ioi 0)
  cont_F : ContinuousOn (fun k => F k 1) (Ici 0)
  Fk_pos : ∀ k, 0 < k → 0 < Fk k
  mono_n : ∀ k, 0 < k → StrictMonoOn (F k) (Ioi 0)
  quasi : ∀ x₁ x₂ y₁ y₂ θ : ℝ, 0 < x₁ → 0 < x₂ → 0 < y₁ → 0 < y₂ → (x₁, x₂) ≠ (y₁, y₂) →
    0 < θ → θ < 1 → min (F x₁ x₂) (F y₁ y₂) < F (θ * x₁ + (1 - θ) * y₁) (θ * x₂ + (1 - θ) * y₂)
  inada_zero : Tendsto Fk (𝓝[>] 0) atTop
  inada_top : Tendsto Fk atTop (𝓝 0)

/-- Total supply of goods `f(k) = F(k, 1) + (1 − δ)k`. -/
def goods (F : ℝ → ℝ → ℝ) (δ k : ℝ) : ℝ := F k 1 + (1 - δ) * k

namespace Neoclassical

variable {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} (hF : Neoclassical F Fk)
include hF

/-- `k ↦ F(k, 1)` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_F : StrictMonoOn (fun k => F k 1) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) hF.cont_F fun x hx => ?_
  rw [interior_Ici] at hx
  rw [(hF.deriv_k x hx).deriv]
  exact hF.Fk_pos x hx

theorem F_pos {k : ℝ} (hk : 0 < k) : 0 < F k 1 := by
  have := hF.strictMonoOn_F (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hk.le) hk
  simpa [hF.zero_left] using this

/-- **`k ↦ F(k, 1)` is strictly concave on `[0, ∞)`**: homogeneity turns strict quasi-concavity
into strict concavity along `n = 1`, and strict monotonicity in `n` handles the endpoint `k = 0`. -/
theorem strictConcaveOn_F : StrictConcaveOn ℝ (Ici 0) (fun k => F k 1) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [Set.mem_Ici] at hx hy
  -- the endpoint case `x = 0` (and symmetrically `y = 0`)
  have hend : ∀ {y b : ℝ}, 0 < y → 0 < b → b < 1 → b * F y 1 < F (b * y) 1 := by
    intro y b hy hb hb1
    have h := hF.hom b y 1 hb hy.le zero_le_one
    rw [mul_one] at h
    rw [← h]
    exact hF.mono_n (b * y) (mul_pos hb hy) (Set.mem_Ioi.2 hb) (Set.mem_Ioi.2 one_pos) hb1
  rcases hx.eq_or_lt with rfl | hx0
  · have hy0 : 0 < y := lt_of_le_of_ne hy hxy
    simpa [hF.zero_left] using hend hy0 hb (by linarith)
  rcases hy.eq_or_lt with rfl | hy0
  · simpa [hF.zero_left] using hend hx0 ha (by linarith)
  -- the interior case, by normalizing both points to the unit isoquant
  set p := F x 1
  set q := F y 1
  have hp : 0 < p := hF.F_pos hx0
  have hq : 0 < q := hF.F_pos hy0
  set S := a * p + b * q
  have hS : 0 < S := by positivity
  set θ := a * p / S
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [div_lt_one hS]; simp only [S]; nlinarith
  have hX : F (x / p) (1 / p) = 1 := by
    have h := hF.hom (1 / p) x 1 (by positivity) hx0.le zero_le_one
    rw [show 1 / p * x = x / p by ring, mul_one] at h
    rw [h]
    field_simp
    rfl
  have hY : F (y / q) (1 / q) = 1 := by
    have h := hF.hom (1 / q) y 1 (by positivity) hy0.le zero_le_one
    rw [show 1 / q * y = y / q by ring, mul_one] at h
    rw [h]
    field_simp
    rfl
  have hne : (x / p, 1 / p) ≠ (y / q, 1 / q) := by
    intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hpq : p = q := by
      have := h2
      field_simp at this
      linarith
    rw [hpq] at h1
    exact hxy (by field_simp at h1; linarith)
  have hq' := hF.quasi (x / p) (1 / p) (y / q) (1 / q) θ (by positivity) (by positivity)
    (by positivity) (by positivity) hne hθ0 hθ1
  rw [hX, hY, min_self] at hq'
  have h1θ : 1 - θ = b * q / S := by simp only [θ, S]; field_simp; ring
  have e1 : θ * (x / p) + (1 - θ) * (y / q) = 1 / S * (a * x + b * y) := by
    rw [h1θ]; simp only [θ]; field_simp
  have e2 : θ * (1 / p) + (1 - θ) * (1 / q) = 1 / S * 1 := by
    rw [h1θ]; simp only [θ, S]; field_simp; linarith
  rw [e1, e2, hF.hom (1 / S) _ 1 (by positivity) (by positivity) zero_le_one] at hq'
  rw [one_div, inv_mul_eq_div, one_lt_div hS] at hq'
  simpa [S] using hq'

theorem f_zero (δ : ℝ) : goods F δ 0 = 0 := by simp [goods, hF.zero_left]

/-- **Ex 2.1.** `f′(k) = F_k(k, 1) + 1 − δ`. -/
theorem hasDerivAt_f (δ : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (goods F δ) (Fk k + (1 - δ)) k := by
  exact ((hF.deriv_k k hk).add ((hasDerivAt_id k).const_mul (1 - δ))).congr_deriv (by ring)

/-- **Ex 2.1.** `f` is continuously differentiable on `(0, ∞)`. -/
theorem continuousOn_f' (δ : ℝ) : ContinuousOn (fun k => Fk k + (1 - δ)) (Ioi 0) :=
  hF.cont_Fk.add continuousOn_const

/-- **Ex 2.1.** `f′ > 0`. -/
theorem f'_pos {δ : ℝ} (hδ1 : δ ≤ 1) {k : ℝ} (hk : 0 < k) : 0 < Fk k + (1 - δ) := by
  have := hF.Fk_pos k hk
  linarith

/-- **Ex 2.1.** `f` is strictly increasing. -/
theorem strictMonoOn_f {δ : ℝ} (hδ1 : δ ≤ 1) : StrictMonoOn (goods F δ) (Ici 0) := by
  intro x hx y hy hxy
  have h := hF.strictMonoOn_F hx hy hxy
  simp only [goods]
  rw [Set.mem_Ici] at hx
  nlinarith

/-- **Ex 2.1.** `f` is strictly concave. -/
theorem strictConcaveOn_f (δ : ℝ) : StrictConcaveOn ℝ (Ici 0) (goods F δ) := by
  have hlin : ConcaveOn ℝ (Ici 0) (fun k : ℝ => (1 - δ) * k) :=
    ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; exact le_of_eq (by ring)⟩
  exact hF.strictConcaveOn_F.add_concaveOn hlin

/-- **Ex 2.1.** `f′(k) → ∞` as `k → 0+`. -/
theorem f'_tendsto_zero (δ : ℝ) : Tendsto (fun k => Fk k + (1 - δ)) (𝓝[>] 0) atTop :=
  tendsto_atTop_add_const_right _ _ hF.inada_zero

/-- **Ex 2.1.** `f′(k) → 1 − δ` as `k → ∞`. -/
theorem f'_tendsto_atTop (δ : ℝ) : Tendsto (fun k => Fk k + (1 - δ)) atTop (𝓝 (1 - δ)) := by
  simpa using hF.inada_top.add_const (1 - δ)

end Neoclassical

/-- The Cobb–Douglas technology `F(k, n) = k^α n^{1−α}`. -/
noncomputable def cobbDouglas (α : ℝ) (k n : ℝ) : ℝ := k ^ α * n ^ (1 - α)

/-- **The assumptions are consistent**: Cobb–Douglas with `0 < α < 1` is neoclassical, with
`F_k(k, 1) = αk^{α−1}`. -/
theorem cobbDouglas_neoclassical {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Neoclassical (cobbDouglas α) (fun k => α * k ^ (α - 1)) := by
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  have hlogF : ∀ a b : ℝ, 0 < a → 0 < b →
      log (cobbDouglas α a b) = α * log a + (1 - α) * log b := fun a b ha hb => by
    unfold cobbDouglas
    rw [log_mul (rpow_pos_of_pos ha α).ne' (rpow_pos_of_pos hb _).ne', log_rpow ha, log_rpow hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l k n hl hk hn
    unfold cobbDouglas
    rw [mul_rpow hl.le hk, mul_rpow hl.le hn]
    have : l ^ α * l ^ (1 - α) = l := by
      rw [← rpow_add hl]; simp
    calc l ^ α * k ^ α * (l ^ (1 - α) * n ^ (1 - α))
        = (l ^ α * l ^ (1 - α)) * (k ^ α * n ^ (1 - α)) := by ring
      _ = l * (k ^ α * n ^ (1 - α)) := by rw [this]
  · simp [cobbDouglas, zero_rpow hα.ne']
  · intro k hk
    have := (hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).mul_const ((1 : ℝ) ^ (1 - α))
    simpa [cobbDouglas] using this
  · exact continuousOn_const.mul fun x hx =>
      (continuousAt_rpow_const x _ (Or.inl (Set.mem_Ioi.1 hx).ne')).continuousWithinAt
  · have : (fun k => cobbDouglas α k 1) = fun k => k ^ α := by
      funext k; simp [cobbDouglas]
    rw [this]
    exact (continuous_rpow_const hα.le).continuousOn
  · intro k hk
    exact mul_pos hα (rpow_pos_of_pos hk _)
  · intro k hk n hn m hm hnm
    unfold cobbDouglas
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow (Set.mem_Ioi.1 hn).le hnm h1α) (rpow_pos_of_pos hk α)
  · intro x₁ x₂ y₁ y₂ θ hx₁ hx₂ hy₁ hy₂ hne hθ0 hθ1
    have hm₁ : 0 < θ * x₁ + (1 - θ) * y₁ := by nlinarith
    have hm₂ : 0 < θ * x₂ + (1 - θ) * y₂ := by nlinarith
    -- concavity of the logarithm in each coordinate, strictly in one of them
    have c₁ : θ * log x₁ + (1 - θ) * log y₁ ≤ log (θ * x₁ + (1 - θ) * y₁) := by
      have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx₁) (Set.mem_Ioi.2 hy₁) hθ0.le
        (by linarith : 0 ≤ 1 - θ) (by ring)
      simpa [smul_eq_mul] using this
    have c₂ : θ * log x₂ + (1 - θ) * log y₂ ≤ log (θ * x₂ + (1 - θ) * y₂) := by
      have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hx₂) (Set.mem_Ioi.2 hy₂) hθ0.le
        (by linarith : 0 ≤ 1 - θ) (by ring)
      simpa [smul_eq_mul] using this
    have hstrict : α * (θ * log x₁ + (1 - θ) * log y₁) + (1 - α) * (θ * log x₂ + (1 - θ) * log y₂)
        < α * log (θ * x₁ + (1 - θ) * y₁) + (1 - α) * log (θ * x₂ + (1 - θ) * y₂) := by
      by_cases h₁ : x₁ = y₁
      · have h₂ : x₂ ≠ y₂ := fun h => hne (by rw [h₁, h])
        have s₂ : θ * log x₂ + (1 - θ) * log y₂ < log (θ * x₂ + (1 - θ) * y₂) := by
          have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 hx₂) (Set.mem_Ioi.2 hy₂) h₂ hθ0
            (by linarith : 0 < 1 - θ) (by ring)
          simpa [smul_eq_mul] using this
        nlinarith
      · have s₁ : θ * log x₁ + (1 - θ) * log y₁ < log (θ * x₁ + (1 - θ) * y₁) := by
          have := strictConcaveOn_log_Ioi.2 (Set.mem_Ioi.2 hx₁) (Set.mem_Ioi.2 hy₁) h₁ hθ0
            (by linarith : 0 < 1 - θ) (by ring)
          simpa [smul_eq_mul] using this
        nlinarith
    have hFx := hlogF x₁ x₂ hx₁ hx₂
    have hFy := hlogF y₁ y₂ hy₁ hy₂
    have hFm := hlogF _ _ hm₁ hm₂
    have hposx : 0 < cobbDouglas α x₁ x₂ :=
      mul_pos (rpow_pos_of_pos hx₁ _) (rpow_pos_of_pos hx₂ _)
    have hposy : 0 < cobbDouglas α y₁ y₂ :=
      mul_pos (rpow_pos_of_pos hy₁ _) (rpow_pos_of_pos hy₂ _)
    have hposm : 0 < cobbDouglas α (θ * x₁ + (1 - θ) * y₁) (θ * x₂ + (1 - θ) * y₂) :=
      mul_pos (rpow_pos_of_pos hm₁ _) (rpow_pos_of_pos hm₂ _)
    rw [← log_lt_log_iff (lt_min hposx hposy) hposm]
    have hmin : log (min (cobbDouglas α x₁ x₂) (cobbDouglas α y₁ y₂)) ≤
        θ * log (cobbDouglas α x₁ x₂) + (1 - θ) * log (cobbDouglas α y₁ y₂) := by
      have h1 := log_le_log (lt_min hposx hposy) (min_le_left _ _)
      have h2 := log_le_log (lt_min hposx hposy) (min_le_right _ _)
      nlinarith
    rw [hFx, hFy] at hmin
    rw [hFm]
    nlinarith
  · exact (tendsto_rpow_neg_nhdsGT_zero (by linarith : α - 1 < 0)).const_mul_atTop hα
  · have := (tendsto_rpow_neg_atTop h1α).const_mul α
    simpa [neg_sub] using this

end StokeyLucasPrescott.Overview

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Competitive equilibrium in the finite-horizon growth economy

SLP §2.3, pp. 22–29, and Exercises 2.8–2.10.

Households own capital and labour, rent them to firms, and trade in one market in period 0 at
prices `p_t` (goods), `r_t` (capital rental) and `w_t` (labour), in units of period-`t` goods.

* `firm_profit_le`: at `r = F_k(k*, 1)` and `w = F(k*, 1) − k* F_k(k*, 1)` every input pair earns at
  most zero profit, which `(k*, 1)` attains: the firm's problem (8) is solved and `π = 0`.
* `first_welfare` (SLP pp. 26–27): a competitive equilibrium allocation solves the planner's
  problem.
* `household_optimal`, `second_welfare` (Ex 2.8): the planner's Euler path with the prices
  (20)–(22) is a competitive equilibrium.
* `firmOwned_firm_optimal`, `firmOwned_household_optimal` (Ex 2.9): the same quantities and prices
  form an equilibrium when firms own the capital and households own shares.
* `sequential_budget`, `sequential_household_optimal` (Ex 2.10): with sequential spot markets,
  one-period bonds at `q_t = 1/f′(k*_{t+1})` and perfect foresight, the same allocation with zero
  bond holdings is optimal for the household.
-/

open Finset Set Filter Topology

namespace StokeyLucasPrescott.Overview

/-! ### The firm -/

/-- **The firm's problem (8).** If `F` is homogeneous of degree one with `k ↦ F(k, 1)` concave, then
at `r = F_k(k*, 1)`, `w = F(k*, 1) − k* F_k(k*, 1)`, every `(k, n) ≥ 0` has
`F(k, n) − rk − wn ≤ 0`. -/
theorem firm_profit_le {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    (hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1)
    (hcont0 : ∀ k, 0 ≤ k → Tendsto (fun n => F k n) (𝓝[>] 0) (𝓝 (F k 0)))
    {ks : ℝ} (hks : 0 < ks) (hd : HasDerivAt (fun k => F k 1) (Fk ks) ks)
    {k n : ℝ} (hk : 0 ≤ k) (hn : 0 ≤ n) :
    F k n - Fk ks * k - (F ks 1 - ks * Fk ks) * n ≤ 0 := by
  -- for `n > 0`, homogeneity and the tangent line at `k*`
  have hpos : ∀ n, 0 < n → F k n - Fk ks * k - (F ks 1 - ks * Fk ks) * n ≤ 0 := fun n hn => by
    have h1 := hom n (k / n) 1 hn (by positivity) zero_le_one
    rw [show n * (k / n) = k by field_simp, mul_one] at h1
    have h2 := concave_le_tangent hconc (Set.mem_Ici.2 hks.le)
      (Set.mem_Ici.2 (by positivity : 0 ≤ k / n))
      hd
    have h3 := mul_le_mul_of_nonneg_left h2 hn.le
    rw [h1]
    have e : n * (F ks 1 + Fk ks * (k / n - ks)) = Fk ks * k + (F ks 1 - ks * Fk ks) * n := by
      field_simp
      ring
    linarith
  rcases hn.eq_or_lt with rfl | hn
  · -- at `n = 0`, pass to the limit
    have hlim : Tendsto (fun n => F k n - Fk ks * k - (F ks 1 - ks * Fk ks) * n) (𝓝[>] 0)
        (𝓝 (F k 0 - Fk ks * k - (F ks 1 - ks * Fk ks) * 0)) :=
      ((hcont0 k hk).sub tendsto_const_nhds).sub
        (tendsto_const_nhds.mul (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id))
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun n hn => hpos n hn)
  · exact hpos n hn

/-- **Zero profit.** `(k*, 1)` earns zero profit at these prices. -/
theorem firm_profit_zero (F : ℝ → ℝ → ℝ) (Fk : ℝ → ℝ) (ks : ℝ) :
    F ks 1 - Fk ks * ks - (F ks 1 - ks * Fk ks) * 1 = 0 := by ring

/-! ### Households and equilibrium -/

/-- Lifetime utility `∑_{t=0}^T βᵗ U(c_t)`. -/
def utility (β : ℝ) (U : ℝ → ℝ) (T : ℕ) (c : ℕ → ℝ) : ℝ := ∑ t ∈ range (T + 1), β ^ t * U (c t)

/-- The household's feasible set (13): consumption in the domain of `U`, `k_{t+1} ≥ 0` and
`k₀ = x₀`. -/
def HHFeasible (D : Set ℝ) (x₀ : ℝ) (T : ℕ) (c k : ℕ → ℝ) : Prop :=
  k 0 = x₀ ∧ ∀ t ≤ T, c t ∈ D ∧ 0 ≤ k (t + 1)

/-- The household's budget constraint (12), with profit income `prof`. -/
def HHBudget (p r w : ℕ → ℝ) (δ prof : ℝ) (T : ℕ) (c k : ℕ → ℝ) : Prop :=
  ∑ t ∈ range (T + 1), p t * (c t + k (t + 1) - (r t + 1 - δ) * k t - w t) ≤ prof

variable (D : Set ℝ) (β : ℝ) (U : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (δ x₀ : ℝ) (T : ℕ)
  (p r w c k : ℕ → ℝ) in
/-- A competitive equilibrium (SLP p. 25): firms maximize profit each period, households maximize
utility over their budget set given equilibrium profits, and goods markets clear. -/
structure IsEquilibrium : Prop where
  firm : ∀ t ≤ T, ∀ k' n', 0 ≤ k' → 0 ≤ n' →
    F k' n' - r t * k' - w t * n' ≤ F (k t) 1 - r t * k t - w t
  feasible : HHFeasible D x₀ T c k
  budget : HHBudget p r w δ (∑ t ∈ range (T + 1), p t * (F (k t) 1 - r t * k t - w t)) T c k
  household : ∀ c' k', HHFeasible D x₀ T c' k' →
    HHBudget p r w δ (∑ t ∈ range (T + 1), p t * (F (k t) 1 - r t * k t - w t)) T c' k' →
    utility β U T c' ≤ utility β U T c
  clear : ∀ t ≤ T, c t + k (t + 1) - (1 - δ) * k t = F (k t) 1

/-- **The first welfare theorem** (SLP pp. 26–27): with nonnegative goods prices, a competitive
equilibrium allocation maximizes the planner's objective over all allocations with
`c_t + k_{t+1} ≤ f(k_t)`. -/
theorem first_welfare {D : Set ℝ} {β : ℝ} {U : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {δ x₀ : ℝ} {T : ℕ}
    {p r w c k : ℕ → ℝ} (he : IsEquilibrium D β U F δ x₀ T p r w c k) (hp : ∀ t, 0 ≤ p t)
    (hx₀ : 0 ≤ x₀) {c' k' : ℕ → ℝ} (hf : HHFeasible D x₀ T c' k')
    (hres : ∀ t ≤ T, c' t + k' (t + 1) ≤ goods F δ (k' t)) :
    utility β U T c' ≤ utility β U T c := by
  refine he.household c' k' hf ?_
  unfold HHBudget
  refine sum_le_sum fun t ht => ?_
  have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
  have hk't : 0 ≤ k' t := by
    rcases t with _ | t
    · rw [hf.1]; exact hx₀
    · exact (hf.2 t (by omega)).2
  have hfirm := he.firm t htT (k' t) 1 hk't zero_le_one
  have hr := hres t htT
  simp only [goods] at hr
  apply mul_le_mul_of_nonneg_left _ (hp t)
  linarith

/-! ### Exercise 2.8: the planner's allocation is an equilibrium -/

/-- The goods prices (20): `p₀` given, `p_t = p_{t−1}/f′(k*_t)`. -/
noncomputable def priceP (p₀ : ℝ) (fd : ℝ → ℝ) (ks : ℕ → ℝ) : ℕ → ℝ
  | 0 => p₀
  | t + 1 => priceP p₀ fd ks t / fd (ks (t + 1))

theorem priceP_pos {p₀ : ℝ} {fd : ℝ → ℝ} {ks : ℕ → ℝ} (hp₀ : 0 < p₀)
    (hfd : ∀ t, 0 < fd (ks t)) (t : ℕ) : 0 < priceP p₀ fd ks t := by
  induction t with
  | zero => exact hp₀
  | succ t ih => exact div_pos ih (hfd (t + 1))

/-- **Ex 2.8 (household).** At the prices (20)–(22), the planner's consumption maximizes the
household's utility over its budget set (11)–(13) (with zero profits). -/
theorem household_optimal {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ x₀ p₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hp₀ : 0 < p₀) (hU : ConcaveOn ℝ D U)
    (hks0 : ks 0 = x₀)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) {c k : ℕ → ℝ} (hf : HHFeasible D x₀ T c k)
    (hb : HHBudget (priceP p₀ (fun k => Fk k + (1 - δ)) ks) (fun t => Fk (ks t))
      (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ 0 T c k) :
    utility β U T c ≤ utility β U T fun t => goods F δ (ks t) - ks (t + 1) := by
  set p := priceP p₀ (fun k => Fk k + (1 - δ)) ks
  set cs : ℕ → ℝ := fun t => goods F δ (ks t) - ks (t + 1)
  set d : ℕ → ℝ := fun t => k t - ks t
  set lam := U' (cs 0) / p₀
  have hp : ∀ t, 0 < p t := priceP_pos hp₀ hfd
  -- marginal utilities are proportional to prices: `βᵗ U′(c*_t) = λ p_t`
  have hprop : ∀ t ≤ T, β ^ t * U' (cs t) = lam * p t := by
    intro t ht
    induction t with
    | zero => simp [lam, p, priceP, hp₀.ne']
    | succ t ih =>
      have he := heuler (t + 1) (by omega) ht
      simp only [Nat.add_sub_cancel] at he
      have ih' := ih (by omega)
      simp only [p, priceP]
      have hne := (hfd (t + 1)).ne'
      field_simp
      simp only [p] at ih'
      rw [pow_succ]
      calc β ^ t * β * U' (cs (t + 1)) * (Fk (ks (t + 1)) + (1 - δ))
          = β ^ t * (β * (Fk (ks (t + 1)) + (1 - δ)) * U' (cs (t + 1))) := by ring
        _ = β ^ t * U' (cs t) := by rw [he]
        _ = lam * priceP p₀ (fun k => Fk k + (1 - δ)) ks t := ih'
  have hlam : 0 ≤ lam := div_nonneg hU'0 hp₀.le
  -- concavity of `U`
  have hconc : utility β U T c - utility β U T cs ≤
      lam * ∑ t ∈ range (T + 1), p t * (c t - cs t) := by
    unfold utility
    rw [← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun t ht => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have h1 := concave_le_tangent hU (hcs t htT) (hf.2 t htT).1 (hUd t htT)
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ t)
    have h3 := hprop t htT
    calc β ^ t * U (c t) - β ^ t * U (cs t) ≤ β ^ t * U' (cs t) * (c t - cs t) := by
          simp only [cs] at h2 ⊢; nlinarith
      _ = lam * (p t * (c t - cs t)) := by rw [h3]; ring
  -- the budget, against the planner's allocation which exhausts it
  have hzero : ∀ t, cs t + ks (t + 1) - (Fk (ks t) + 1 - δ) * ks t -
      (F (ks t) 1 - ks t * Fk (ks t)) = 0 := fun t => by simp only [cs, goods]; ring
  have hbud : ∑ t ∈ range (T + 1), p t * (c t - cs t) ≤
      ∑ t ∈ range (T + 1), p t * ((Fk (ks t) + (1 - δ)) * d t - d (t + 1)) := by
    unfold HHBudget at hb
    have : ∑ t ∈ range (T + 1), p t * (c t - cs t) -
        ∑ t ∈ range (T + 1), p t * ((Fk (ks t) + (1 - δ)) * d t - d (t + 1)) =
        ∑ t ∈ range (T + 1), p t * (c t + k (t + 1) - (Fk (ks t) + 1 - δ) * k t -
          (F (ks t) 1 - ks t * Fk (ks t))) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      have := hzero t
      simp only [d]
      linear_combination (-p t) * this
    beta_reduce at hb
    linarith
  -- telescoping
  have hd0 : d 0 = 0 := by simp only [d, hf.1, hks0, sub_self]
  have htel := sum_telescope (a := p) (g := fun t => Fk (ks t) + (1 - δ)) (d := d) hd0 T
    fun t h1 _ => by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [p, priceP, Nat.add_sub_cancel]
      field_simp [(hfd (s + 1)).ne']
  have hlast : 0 ≤ p T * d (T + 1) := by
    simp only [d, hT, sub_zero]
    exact mul_nonneg (hp T).le (hf.2 T le_rfl).2
  have := mul_le_mul_of_nonneg_left (hbud.trans (htel.le.trans
    (show -(p T * d (T + 1)) ≤ 0 by linarith))) hlam
  linarith

/-- **Ex 2.8 (second welfare theorem).** The planner's Euler path, with the prices (20)–(22), is a
competitive equilibrium. -/
theorem second_welfare {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ x₀ p₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hp₀ : 0 < p₀) (hU : ConcaveOn ℝ D U)
    (hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1)
    (hcont0 : ∀ k, 0 ≤ k → Tendsto (fun n => F k n) (𝓝[>] 0) (𝓝 (F k 0)))
    (hderiv : ∀ t ≤ T, HasDerivAt (fun k => F k 1) (Fk (ks t)) (ks t))
    (hks : ∀ t ≤ T, 0 < ks t) (hks0 : ks 0 = x₀)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) :
    IsEquilibrium D β U F δ x₀ T (priceP p₀ (fun k => Fk k + (1 - δ)) ks) (fun t => Fk (ks t))
      (fun t => F (ks t) 1 - ks t * Fk (ks t)) (fun t => goods F δ (ks t) - ks (t + 1)) ks := by
  have hprofit : ∑ t ∈ range (T + 1), priceP p₀ (fun k => Fk k + (1 - δ)) ks t *
      (F (ks t) 1 - Fk (ks t) * ks t - (F (ks t) 1 - ks t * Fk (ks t))) = 0 :=
    sum_eq_zero fun t _ => by ring
  have hfeas : HHFeasible D x₀ T (fun t => goods F δ (ks t) - ks (t + 1)) ks :=
    ⟨hks0, fun t ht => ⟨hcs t ht, by
      rcases (Nat.lt_or_ge t T) with h | h
      · exact (hks (t + 1) (by omega)).le
      · rw [show t = T by omega, hT]⟩⟩
  refine ⟨fun t ht k' n' hk' hn' => ?_, hfeas, ?_, fun c' k' hf hb => ?_, fun t _ => ?_⟩
  · have := firm_profit_le hom hconc hcont0 (hks t ht) (hderiv t ht) hk' hn'
    linarith
  · rw [hprofit]
    unfold HHBudget
    exact (sum_eq_zero fun t _ => by simp only [goods]; ring).le
  · rw [hprofit] at hb
    exact household_optimal hβ hp₀ hU hks0 hcs hUd hU'0 hfd heuler hT hf hb
  · simp only [goods]; ring

/-! ### Exercise 2.9: firms own the capital -/

/-- The firm's discounted profit when it owns the capital, invests `k_{t+1} − (1 − δ)k_t` and hires
labour `n_t`. -/
def firmValue (F : ℝ → ℝ → ℝ) (p w : ℕ → ℝ) (δ : ℝ) (T : ℕ) (k n : ℕ → ℝ) : ℝ :=
  ∑ t ∈ range (T + 1), p t * (F (k t) (n t) - w t * n t - (k (t + 1) - (1 - δ) * k t))

/-- **Ex 2.9 (firm).** At the prices (20) and (22), the planner's capital path with `n = 1`
maximizes the value of a firm that owns the capital, over all `k ≥ 0`, `n ≥ 0` with `k₀ = x₀`. -/
theorem firmOwned_firm_optimal {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} {δ x₀ p₀ : ℝ} {T : ℕ}
    {ks : ℕ → ℝ} (hp₀ : 0 < p₀)
    (hom : ∀ l k n : ℝ, 0 < l → 0 ≤ k → 0 ≤ n → F (l * k) (l * n) = l * F k n)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1)
    (hcont0 : ∀ k, 0 ≤ k → Tendsto (fun n => F k n) (𝓝[>] 0) (𝓝 (F k 0)))
    (hderiv : ∀ t ≤ T, HasDerivAt (fun k => F k 1) (Fk (ks t)) (ks t))
    (hks : ∀ t ≤ T, 0 < ks t) (hks0 : ks 0 = x₀) (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (hT : ks (T + 1) = 0) {k n : ℕ → ℝ} (hk0 : k 0 = x₀) (hk : ∀ t ≤ T + 1, 0 ≤ k t)
    (hn : ∀ t ≤ T, 0 ≤ n t) :
    firmValue F (priceP p₀ (fun k => Fk k + (1 - δ)) ks)
        (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T k n ≤
      firmValue F (priceP p₀ (fun k => Fk k + (1 - δ)) ks)
        (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks fun _ => 1 := by
  set p := priceP p₀ (fun k => Fk k + (1 - δ)) ks
  set d : ℕ → ℝ := fun t => k t - ks t
  have hp : ∀ t, 0 < p t := priceP_pos hp₀ hfd
  -- each period, output is bounded by factor payments at the equilibrium prices
  have hbound : firmValue F p (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T k n -
      firmValue F p (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks (fun _ => 1) ≤
      ∑ t ∈ range (T + 1), p t * ((Fk (ks t) + (1 - δ)) * d t - d (t + 1)) := by
    unfold firmValue
    rw [← sum_sub_distrib]
    refine sum_le_sum fun t ht => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have hfirm := firm_profit_le hom hconc hcont0 (hks t htT) (hderiv t htT) (hk t (by omega))
      (hn t htT)
    have := mul_le_mul_of_nonneg_left hfirm (hp t).le
    simp only [d]
    nlinarith
  have hd0 : d 0 = 0 := by simp only [d, hk0, hks0, sub_self]
  have htel := sum_telescope (a := p) (g := fun t => Fk (ks t) + (1 - δ)) (d := d) hd0 T
    fun t h1 _ => by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [p, priceP, Nat.add_sub_cancel]
      field_simp [(hfd (s + 1)).ne']
  have hlast : 0 ≤ p T * d (T + 1) := by
    simp only [d, hT, sub_zero]
    exact mul_nonneg (hp T).le (hk (T + 1) le_rfl)
  linarith

/-- **Ex 2.9 (household).** With firms owning the capital, the household chooses consumption and
labour `n_t ≤ 1` subject to `∑ p_t (c_t − w_t n_t) ≤ V`, where `V` is the firm's value; the
planner's consumption is optimal. -/
theorem firmOwned_household_optimal {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ p₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hp₀ : 0 < p₀) (hU : ConcaveOn ℝ D U)
    (hconc : ConcaveOn ℝ (Ici 0) fun k => F k 1) (hF0 : 0 ≤ F 0 1)
    (hderiv : ∀ t ≤ T, HasDerivAt (fun k => F k 1) (Fk (ks t)) (ks t))
    (hks : ∀ t ≤ T, 0 < ks t)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    {c n : ℕ → ℝ} (hc : ∀ t ≤ T, c t ∈ D) (hn : ∀ t ≤ T, n t ≤ 1)
    (hb : ∑ t ∈ range (T + 1), priceP p₀ (fun k => Fk k + (1 - δ)) ks t *
      (c t - (F (ks t) 1 - ks t * Fk (ks t)) * n t) ≤
      firmValue F (priceP p₀ (fun k => Fk k + (1 - δ)) ks)
        (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks fun _ => 1) :
    utility β U T c ≤ utility β U T fun t => goods F δ (ks t) - ks (t + 1) := by
  set p := priceP p₀ (fun k => Fk k + (1 - δ)) ks
  set cs : ℕ → ℝ := fun t => goods F δ (ks t) - ks (t + 1)
  set lam := U' (cs 0) / p₀
  have hp : ∀ t, 0 < p t := priceP_pos hp₀ hfd
  have hprop : ∀ t ≤ T, β ^ t * U' (cs t) = lam * p t := by
    intro t ht
    induction t with
    | zero => simp [lam, p, priceP, hp₀.ne']
    | succ t ih =>
      have he := heuler (t + 1) (by omega) ht
      simp only [Nat.add_sub_cancel] at he
      have ih' := ih (by omega)
      simp only [p, priceP]
      have hne := (hfd (t + 1)).ne'
      field_simp
      simp only [p] at ih'
      rw [pow_succ]
      calc β ^ t * β * U' (cs (t + 1)) * (Fk (ks (t + 1)) + (1 - δ))
          = β ^ t * (β * (Fk (ks (t + 1)) + (1 - δ)) * U' (cs (t + 1))) := by ring
        _ = β ^ t * U' (cs t) := by rw [he]
        _ = lam * priceP p₀ (fun k => Fk k + (1 - δ)) ks t := ih'
  have hlam : 0 ≤ lam := div_nonneg hU'0 hp₀.le
  -- wages are nonnegative: `F(k*, 1) − k* F_k ≥ F(0, 1) ≥ 0` by concavity
  have hw : ∀ t ≤ T, 0 ≤ F (ks t) 1 - ks t * Fk (ks t) := fun t ht => by
    have := concave_le_tangent hconc (Set.mem_Ici.2 (hks t ht).le) (Set.mem_Ici.2 le_rfl)
      (hderiv t ht)
    linarith
  have hconcU : utility β U T c - utility β U T cs ≤
      lam * ∑ t ∈ range (T + 1), p t * (c t - cs t) := by
    unfold utility
    rw [← sum_sub_distrib, mul_sum]
    refine sum_le_sum fun t ht => ?_
    have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have h1 := concave_le_tangent hU (hcs t htT) (hc t htT) (hUd t htT)
    have h2 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ t)
    have h3 := hprop t htT
    calc β ^ t * U (c t) - β ^ t * U (cs t) ≤ β ^ t * U' (cs t) * (c t - cs t) := by
          simp only [cs] at h2 ⊢; nlinarith
      _ = lam * (p t * (c t - cs t)) := by rw [h3]; ring
  -- the planner's consumption exhausts the budget at `n = 1`
  have hspend : ∑ t ∈ range (T + 1), p t * (c t - cs t) ≤ 0 := by
    have hfv : firmValue F p (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ T ks (fun _ => 1) =
        ∑ t ∈ range (T + 1), p t * (cs t - (F (ks t) 1 - ks t * Fk (ks t))) := by
      unfold firmValue
      refine sum_congr rfl fun t _ => ?_
      simp only [cs, goods]
      ring
    have hlab : ∀ t ∈ range (T + 1), p t * (c t - (F (ks t) 1 - ks t * Fk (ks t))) ≤
        p t * (c t - (F (ks t) 1 - ks t * Fk (ks t)) * n t) := fun t ht => by
      have htT : t ≤ T := Nat.lt_succ_iff.1 (mem_range.1 ht)
      have := mul_le_mul_of_nonneg_left (hn t htT) (hw t htT)
      exact mul_le_mul_of_nonneg_left (by linarith) (hp t).le
    have h1 := (sum_le_sum hlab).trans hb
    rw [hfv] at h1
    rw [← sub_nonpos, ← sum_sub_distrib] at h1
    have : ∑ t ∈ range (T + 1), p t * (c t - cs t) =
        ∑ t ∈ range (T + 1), (p t * (c t - (F (ks t) 1 - ks t * Fk (ks t))) -
          p t * (cs t - (F (ks t) 1 - ks t * Fk (ks t)))) :=
      sum_congr rfl fun t _ => by ring
    linarith
  have := mul_le_mul_of_nonneg_left hspend hlam
  linarith

/-! ### Exercise 2.10: sequential markets -/

/-- The present-value price of period-`t` goods implied by bond prices: `P₀ = 1`,
`P_{t+1} = P_t q_t`. -/
def pvPrice (q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => pvPrice q t * q t

/-- The household's period-`t` budget constraint in sequential markets: goods, capital and
one-period bonds `b`, with `b₀ = 0`. -/
def SeqBudget (q r w : ℕ → ℝ) (δ : ℝ) (t : ℕ) (c k b : ℕ → ℝ) : Prop :=
  c t + k (t + 1) - (1 - δ) * k t + q t * b (t + 1) ≤ r t * k t + w t + b t

/-- **Sequential budgets imply the Arrow–Debreu budget.** If each period's budget holds, `b₀ = 0`
and `b_{T+1} = 0`, then `∑ P_t (c_t + k_{t+1} − (r_t + 1 − δ)k_t − w_t) ≤ 0` with
`P_t = ∏_{s<t} q_s`, `q ≥ 0`. -/
theorem sequential_budget {q r w : ℕ → ℝ} {δ : ℝ} {T : ℕ} {c k b : ℕ → ℝ} (hq : ∀ t, 0 ≤ q t)
    (hb : ∀ t ≤ T, SeqBudget q r w δ t c k b) (hb0 : b 0 = 0) (hbT : b (T + 1) = 0) :
    HHBudget (pvPrice q) r w δ 0 T c k := by
  have hP : ∀ t, 0 ≤ pvPrice q t := fun t => by
    induction t with
    | zero => simp [pvPrice]
    | succ t ih => exact mul_nonneg ih (hq t)
  -- weight each period's budget by `P_t`; the bond terms telescope
  have hsum : ∀ n ≤ T, ∑ t ∈ range (n + 1), pvPrice q t *
      (c t + k (t + 1) - (r t + 1 - δ) * k t - w t) ≤ -(pvPrice q (n + 1) * b (n + 1)) := by
    intro n hn
    induction n with
    | zero =>
      have h := mul_le_mul_of_nonneg_left (hb 0 (by omega)) (hP 0)
      simp only [sum_range_one, pvPrice, hb0, zero_add] at h ⊢
      linarith
    | succ n ih =>
      rw [sum_range_succ]
      have h := mul_le_mul_of_nonneg_left (hb (n + 1) hn) (hP (n + 1))
      have ih' := ih (by omega)
      simp only [pvPrice] at h ih' ⊢
      linear_combination ih' + h
  have := hsum T le_rfl
  rw [hbT, mul_zero, neg_zero] at this
  exact this

/-- **Ex 2.10.** In sequential markets with bond prices `q_t = 1/f′(k*_{t+1})` and the factor prices
(21)–(22), the planner's consumption is optimal for the household among all plans satisfying
the period budgets with `b₀ = b_{T+1} = 0`; the planner's allocation with `b ≡ 0` satisfies them,
so bond markets clear. -/
theorem sequential_household_optimal {D : Set ℝ} {U U' : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ}
    {β δ x₀ : ℝ} {T : ℕ} {ks : ℕ → ℝ} (hβ : 0 ≤ β) (hU : ConcaveOn ℝ D U) (hks0 : ks 0 = x₀)
    (hcs : ∀ t ≤ T, goods F δ (ks t) - ks (t + 1) ∈ D)
    (hUd : ∀ t ≤ T, HasDerivAt U (U' (goods F δ (ks t) - ks (t + 1)))
      (goods F δ (ks t) - ks (t + 1)))
    (hU'0 : 0 ≤ U' (goods F δ (ks 0) - ks 1))
    (hfd : ∀ t, 0 < Fk (ks t) + (1 - δ))
    (heuler : ∀ t, 1 ≤ t → t ≤ T → β * (Fk (ks t) + (1 - δ)) * U' (goods F δ (ks t) - ks (t + 1)) =
      U' (goods F δ (ks (t - 1)) - ks t))
    (hT : ks (T + 1) = 0) {c k b : ℕ → ℝ} (hf : HHFeasible D x₀ T c k)
    (hb : ∀ t ≤ T, SeqBudget (fun t => 1 / (Fk (ks (t + 1)) + (1 - δ))) (fun t => Fk (ks t))
      (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ t c k b)
    (hb0 : b 0 = 0) (hbT : b (T + 1) = 0) :
    utility β U T c ≤ utility β U T fun t => goods F δ (ks t) - ks (t + 1) := by
  have hq : ∀ t, 0 ≤ 1 / (Fk (ks (t + 1)) + (1 - δ)) := fun t => (one_div_pos.2 (hfd _)).le
  have hAD := sequential_budget hq hb hb0 hbT
  -- the present-value prices are the prices (20) with `p₀ = 1`
  have hPeq : pvPrice (fun t => 1 / (Fk (ks (t + 1)) + (1 - δ))) =
      priceP 1 (fun k => Fk k + (1 - δ)) ks := by
    funext t
    induction t with
    | zero => rfl
    | succ t ih => simp only [pvPrice, priceP, ih]; ring
  rw [hPeq] at hAD
  exact household_optimal hβ one_pos hU hks0 hcs hUd hU'0 hfd heuler hT hf hAD

/-- **Ex 2.10 (bond-market clearing).** The planner's allocation with zero bond holdings satisfies
every period's budget with equality. -/
theorem sequential_planner_feasible {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} {δ : ℝ} {ks : ℕ → ℝ}
    (q : ℕ → ℝ) (t : ℕ) :
    SeqBudget q (fun t => Fk (ks t)) (fun t => F (ks t) 1 - ks t * Fk (ks t)) δ t
      (fun t => goods F δ (ks t) - ks (t + 1)) ks fun _ => 0 := by
  unfold SeqBudget goods
  ring_nf
  exact le_rfl

end StokeyLucasPrescott.Overview

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stochastic log/Cobb–Douglas economy

SLP §2.2, pp. 16–19, and Exercise 2.6, p. 19.

Output is `z f(k) = z k^α` with i.i.d. shocks `z ∼ μ`, `z > 0`, `ln z` integrable, `U = ln`.

* `log_tradeoff`, `log_tradeoff_unique`: for `Y > 0`, `ln(Y − y) + (αβ/(1 − αβ)) ln y` is
  maximized over `y ∈ (0, Y)` exactly at `y = αβY`.
* `stochValue`: `v(k, z) = A + B ln k + C ln z`, `B = α/(1 − αβ)`, `C = 1/(1 − αβ)`.
* `integral_stochValue`: `E[v(y, z′)] = A + B ln y + C E[ln z]`.
* `stoch_bellman_isGreatest`, `stoch_argmax_unique` (Ex 2.6): `v` satisfies the functional
  equation (3) and `y = αβ z k^α` (policy (5)) is the unique maximizer.
* `hasSum_expected_utility` (Ex 2.6): along policy (5), with the shocks after period 0 i.i.d. under
  the product measure, `∑ βᵗ E[ln c_t] = v(k, z)`.
-/

open Finset Set Filter Topology Real MeasureTheory ProbabilityTheory

namespace StokeyLucasPrescott.Overview

/-- **The log trade-off.** For `Y > 0` and `0 < αβ < 1`, every `y ∈ (0, Y)` has
`ln(Y − y) + (αβ/(1 − αβ)) ln y ≤ ln((1 − αβ)Y) + (αβ/(1 − αβ)) ln(αβY)`. -/
theorem log_tradeoff {α β Y y : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (hY : 0 < Y) (hy : 0 < y)
    (hyY : y < Y) :
    log (Y - y) + α * β / (1 - α * β) * log y ≤
      log ((1 - α * β) * Y) + α * β / (1 - α * β) * log (α * β * Y) := by
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have hcs : 0 < (1 - α * β) * Y := mul_pos h1ab hY
  have hys : 0 < α * β * Y := mul_pos h0 hY
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyY)) (hasDerivAt_log hcs.ne')
  have t2 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (hasDerivAt_log hys.ne')
  have hw : 0 ≤ α * β / (1 - α * β) := div_nonneg h0.le h1ab.le
  have hfoc : ((1 - α * β) * Y)⁻¹ * (Y - y - (1 - α * β) * Y) +
      α * β / (1 - α * β) * ((α * β * Y)⁻¹ * (y - α * β * Y)) = 0 := by
    have hα0 : α ≠ 0 := left_ne_zero_of_mul h0.ne'
    have hβ0 : β ≠ 0 := right_ne_zero_of_mul h0.ne'
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left t2 hw
  nlinarith

/-- **The maximizer is unique.** -/
theorem log_tradeoff_unique {α β Y y : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1) (hY : 0 < Y)
    (hy : 0 < y) (hyY : y < Y)
    (hmax : log ((1 - α * β) * Y) + α * β / (1 - α * β) * log (α * β * Y) ≤
      log (Y - y) + α * β / (1 - α * β) * log y) : y = α * β * Y := by
  by_contra hne
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have hcs : 0 < (1 - α * β) * Y := mul_pos h1ab hY
  have hys : 0 < α * β * Y := mul_pos h0 hY
  have t1 := concave_le_tangent strictConcaveOn_log_Ioi.concaveOn (Set.mem_Ioi.2 hcs)
    (Set.mem_Ioi.2 (sub_pos.2 hyY)) (hasDerivAt_log hcs.ne')
  have t2 := strictConcave_lt_tangent strictConcaveOn_log_Ioi (Set.mem_Ioi.2 hys)
    (Set.mem_Ioi.2 hy) (fun h => hne h.symm) (hasDerivAt_log hys.ne')
  have hw : 0 < α * β / (1 - α * β) := div_pos h0 h1ab
  have hfoc : ((1 - α * β) * Y)⁻¹ * (Y - y - (1 - α * β) * Y) +
      α * β / (1 - α * β) * ((α * β * Y)⁻¹ * (y - α * β * Y)) = 0 := by
    have hα0 : α ≠ 0 := left_ne_zero_of_mul h0.ne'
    have hβ0 : β ≠ 0 := right_ne_zero_of_mul h0.ne'
    field_simp
    ring
  have := mul_lt_mul_of_pos_left t2 hw
  nlinarith

/-- The coefficient `C = 1/(1 − αβ)` on `ln z`. -/
noncomputable def coefC (α β : ℝ) : ℝ := 1 / (1 - α * β)

/-- The constant `A = [ln(1 − αβ) + βB ln(αβ) + βC m]/(1 − β)`, `m = E[ln z]`. -/
noncomputable def coefAs (α β m : ℝ) : ℝ :=
  (log (1 - α * β) + β * coefB α β * log (α * β) + β * coefC α β * m) / (1 - β)

/-- The value function `v(k, z) = A + B ln k + C ln z`. -/
noncomputable def stochValue (α β m k z : ℝ) : ℝ :=
  coefAs α β m + coefB α β * log k + coefC α β * log z

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- `E[v(y, z′)] = A + B ln y + C E[ln z]`. -/
theorem integral_stochValue (hint : Integrable log μ) (α β y : ℝ) :
    ∫ z', stochValue α β (∫ z, log z ∂μ) y z' ∂μ =
      coefAs α β (∫ z, log z ∂μ) + coefB α β * log y + coefC α β * ∫ z, log z ∂μ := by
  unfold stochValue
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul]
  simp

/-- The right side of (3): `ln(z k^α − y) + β E[v(y, z′)]`. -/
noncomputable def stochRHS (μ : Measure ℝ) (α β k z y : ℝ) : ℝ :=
  log (z * k ^ α - y) + β * ∫ z', stochValue α β (∫ z, log z ∂μ) y z' ∂μ

/-- The value at the maximizer `y = αβ z k^α` is `v(k, z)`. -/
theorem stochRHS_attained (hint : Integrable log μ) {α β k z : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hβ1 : β < 1) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) :
    stochRHS μ α β k z (α * β * (z * k ^ α)) = stochValue α β (∫ z, log z ∂μ) k z := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hK : 0 < k ^ α := rpow_pos_of_pos hk α
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  unfold stochRHS
  rw [integral_stochValue hint]
  rw [show z * k ^ α - α * β * (z * k ^ α) = (1 - α * β) * (z * k ^ α) by ring]
  simp only [stochValue, coefAs, coefB, coefC]
  rw [log_mul h1ab.ne' (mul_pos hz hK).ne', log_mul h0.ne' (mul_pos hz hK).ne',
    log_mul hz.ne' hK.ne', log_rpow hk]
  field_simp
  ring

/-- The objective in (3) equals the log trade-off plus terms independent of `y`. -/
theorem stochRHS_eq (hint : Integrable log μ) (α β k z y : ℝ) :
    stochRHS μ α β k z y = (log (z * k ^ α - y) + α * β / (1 - α * β) * log y) +
      β * (coefAs α β (∫ z, log z ∂μ) + coefC α β * ∫ z, log z ∂μ) := by
  unfold stochRHS
  rw [integral_stochValue hint]
  simp only [coefB]
  ring

/-- **Ex 2.6.** `v` satisfies the stochastic functional equation (3):
`v(k, z) = max_{0 < y < z k^α} {ln(z k^α − y) + β E[v(y, z′)]}`. -/
theorem stoch_bellman_isGreatest (hint : Integrable log μ) {α β k z : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (hβ1 : β < 1) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) :
    IsGreatest (stochRHS μ α β k z '' Ioo 0 (z * k ^ α)) (stochValue α β (∫ z, log z ∂μ) k z) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hY : 0 < z * k ^ α := mul_pos hz (rpow_pos_of_pos hk α)
  refine ⟨⟨α * β * (z * k ^ α), ⟨mul_pos h0 hY, by nlinarith⟩,
    stochRHS_attained hint hα hβ hβ1 h1 hk hz⟩, ?_⟩
  rintro _ ⟨y, ⟨hy0, hyY⟩, rfl⟩
  rw [← stochRHS_attained hint hα hβ hβ1 h1 hk hz, stochRHS_eq hint, stochRHS_eq hint]
  have := log_tradeoff h0 h1 hY hy0 hyY
  rw [show z * k ^ α - α * β * (z * k ^ α) = (1 - α * β) * (z * k ^ α) by ring]
  linarith

/-- **Ex 2.6.** The policy (5), `y = αβ z k^α`, is the unique maximizer in (3). -/
theorem stoch_argmax_unique (hint : Integrable log μ) {α β k z y : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hβ1 : β < 1) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) (hy : 0 < y) (hyY : y < z * k ^ α)
    (hmax : stochValue α β (∫ z, log z ∂μ) k z ≤ stochRHS μ α β k z y) :
    y = α * β * (z * k ^ α) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have hY : 0 < z * k ^ α := mul_pos hz (rpow_pos_of_pos hk α)
  rw [← stochRHS_attained hint hα hβ hβ1 h1 hk hz, stochRHS_eq hint, stochRHS_eq hint] at hmax
  rw [show z * k ^ α - α * β * (z * k ^ α) = (1 - α * β) * (z * k ^ α) by ring] at hmax
  exact log_tradeoff_unique h0 h1 hY hy hyY (by linarith)

/-! ### Expected utility along the policy -/

/-- The shock in period `t`: the known `z` in period `0`, the coordinate `ω t` afterwards. -/
def shock (z : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℝ := if t = 0 then z else ω t

/-- Capital along policy (5): `k_{t+1} = αβ z_t k_t^α`. -/
noncomputable def stochPath (α β k z : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => k
  | t + 1 => α * β * shock z ω t * stochPath α β k z ω t ^ α

/-- Consumption along (5): `c_t = (1 − αβ) z_t k_t^α`. -/
noncomputable def stochCons (α β k z : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℝ :=
  shock z ω t * stochPath α β k z ω t ^ α - stochPath α β k z ω (t + 1)

/-- The product measure of i.i.d. shocks. -/
noncomputable abbrev shockMeasure (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => μ

theorem ae_shock_pos (hpos : ∀ᵐ z ∂μ, 0 < z) : ∀ᵐ ω ∂shockMeasure μ, ∀ t, 0 < ω t := by
  rw [ae_all_iff]
  intro t
  have h : ∀ᵐ x ∂(shockMeasure μ).map (fun ω => ω t), 0 < x := by
    rwa [Measure.infinitePi_map_eval]
  exact ae_of_ae_map (measurable_pi_apply t).aemeasurable h

theorem integrable_log_coord (hint : Integrable log μ) (t : ℕ) :
    Integrable (fun ω : ℕ → ℝ => log (ω t)) (shockMeasure μ) := by
  have h : Integrable log ((shockMeasure μ).map (fun ω => ω t)) := by
    rwa [Measure.infinitePi_map_eval]
  exact h.comp_aemeasurable (measurable_pi_apply t).aemeasurable

theorem integral_log_coord (t : ℕ) :
    ∫ ω, log (ω t) ∂shockMeasure μ = ∫ z, log z ∂μ := by
  rw [← integral_map (measurable_pi_apply t).aemeasurable
    measurable_log.aestronglyMeasurable, Measure.infinitePi_map_eval]

/-- The expected log shock: `ln z` in period `0`, `E[ln z]` afterwards. -/
noncomputable def meanShock (μ : Measure ℝ) (z : ℝ) (t : ℕ) : ℝ :=
  if t = 0 then log z else ∫ z, log z ∂μ

theorem integrable_log_shock (hint : Integrable log μ) (z : ℝ) (t : ℕ) :
    Integrable (fun ω => log (shock z ω t)) (shockMeasure μ) := by
  rcases t with _ | t
  · simp [shock]
  · simpa [shock] using integrable_log_coord hint (t + 1)

theorem integral_log_shock (z : ℝ) (t : ℕ) :
    ∫ ω, log (shock z ω t) ∂shockMeasure μ = meanShock μ z t := by
  rcases t with _ | t
  · simp [shock, meanShock]
  · simpa [shock, meanShock] using integral_log_coord (μ := μ) (t + 1)

/-- Almost surely, along (5), `ln k_{t+1} = ln(αβ) + ln z_t + α ln k_t` and capital is positive. -/
theorem ae_log_path (hpos : ∀ᵐ z ∂μ, 0 < z) {α β k z : ℝ} (h0 : 0 < α * β) (hk : 0 < k)
    (hz : 0 < z) :
    ∀ᵐ ω ∂shockMeasure μ, ∀ t, 0 < shock z ω t ∧ 0 < stochPath α β k z ω t ∧
      log (stochPath α β k z ω (t + 1)) =
        log (α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
  filter_upwards [ae_shock_pos hpos] with ω hω t
  have hsh : ∀ s, 0 < shock z ω s := fun s => by
    unfold shock; split_ifs
    · exact hz
    · exact hω s
  have hkp : ∀ s, 0 < stochPath α β k z ω s := fun s => by
    induction s with
    | zero => exact hk
    | succ s ih => exact mul_pos (mul_pos h0 (hsh s)) (rpow_pos_of_pos ih α)
  refine ⟨hsh t, hkp t, ?_⟩
  simp only [stochPath]
  rw [log_mul (mul_pos h0 (hsh t)).ne' (rpow_pos_of_pos (hkp t) α).ne', log_mul h0.ne' (hsh t).ne',
    log_rpow (hkp t)]

/-- The expected log capital, by the recursion `M_{t+1} = ln(αβ) + αM_t + E[ln z_t]`. -/
noncomputable def meanLogK (μ : Measure ℝ) (α β k z : ℝ) : ℕ → ℝ
  | 0 => log k
  | t + 1 => log (α * β) + α * meanLogK μ α β k z t + meanShock μ z t

/-- `ln k_t` is integrable with mean `M_t`. -/
theorem integral_log_path (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ) {α β k z : ℝ}
    (h0 : 0 < α * β) (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    Integrable (fun ω => log (stochPath α β k z ω t)) (shockMeasure μ) ∧
      ∫ ω, log (stochPath α β k z ω t) ∂shockMeasure μ = meanLogK μ α β k z t := by
  have hae := ae_log_path hpos h0 hk hz
  induction t with
  | zero => simp [stochPath, meanLogK]
  | succ t ih =>
    have heq : (fun ω => log (stochPath α β k z ω (t + 1))) =ᵐ[shockMeasure μ]
        fun ω => log (α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
      filter_upwards [hae] with ω hω
      exact (hω t).2.2
    have hint' : Integrable (fun ω => log (α * β) + log (shock z ω t) +
        α * log (stochPath α β k z ω t)) (shockMeasure μ) :=
      ((integrable_const _).add (integrable_log_shock hint z t)).add (ih.1.const_mul α)
    refine ⟨hint'.congr heq.symm, ?_⟩
    have hA : Integrable (fun ω => log (α * β) + log (shock z ω t)) (shockMeasure μ) :=
      (integrable_const _).add (integrable_log_shock hint z t)
    have e1 := integral_add hA (ih.1.const_mul α)
    have e2 := integral_add (integrable_const (log (α * β))) (integrable_log_shock hint z t)
    beta_reduce at e1 e2
    rw [integral_congr_ae heq, e1, e2, integral_const, integral_const_mul, ih.2,
      integral_log_shock]
    simp [meanLogK]
    ring

/-- Expected log consumption: `E[ln c_t] = ln(1 − αβ) + E[ln z_t] + αM_t`. -/
theorem integral_log_cons (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ) {α β k z : ℝ}
    (h0 : 0 < α * β) (h1 : α * β < 1) (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ =
      log (1 - α * β) + meanShock μ z t + α * meanLogK μ α β k z t := by
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  have heq : (fun ω => log (stochCons α β k z ω t)) =ᵐ[shockMeasure μ]
      fun ω => log (1 - α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
    filter_upwards [ae_log_path hpos h0 hk hz] with ω hω
    obtain ⟨hs, hp, -⟩ := hω t
    unfold stochCons
    rw [show shock z ω t * stochPath α β k z ω t ^ α - stochPath α β k z ω (t + 1) =
      (1 - α * β) * shock z ω t * stochPath α β k z ω t ^ α by simp only [stochPath]; ring,
      log_mul (mul_pos h1ab hs).ne' (rpow_pos_of_pos hp α).ne', log_mul h1ab.ne' hs.ne',
      log_rpow hp]
  have hi := (integral_log_path hpos hint h0 hk hz t).1
  have hA : Integrable (fun ω => log (1 - α * β) + log (shock z ω t)) (shockMeasure μ) :=
    (integrable_const _).add (integrable_log_shock hint z t)
  have e1 := integral_add hA (hi.const_mul α)
  have e2 := integral_add (integrable_const (log (1 - α * β))) (integrable_log_shock hint z t)
  beta_reduce at e1 e2
  rw [integral_congr_ae heq, e1, e2, integral_const, integral_const_mul,
    (integral_log_path hpos hint h0 hk hz t).2, integral_log_shock]
  simp

omit [IsProbabilityMeasure μ] in
/-- After period `0`, `M_{s+1} = αˢ M_1 + (ln(αβ) + m)(1 − αˢ)/(1 − α)`. -/
theorem meanLogK_succ {α β k z : ℝ} (hα1 : α < 1) (s : ℕ) :
    meanLogK μ α β k z (s + 1) = α ^ s * meanLogK μ α β k z 1 +
      (log (α * β) + ∫ z, log z ∂μ) * (1 - α ^ s) / (1 - α) := by
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + 1 = (s + 1) + 1 by rfl]
    conv_lhs => rw [meanLogK]
    rw [ih]
    simp only [meanShock, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    field_simp
    ring

/-- **Ex 2.6.** Along policy (5), the expected discounted utility `∑ βᵗ E[ln c_t]` from `(k, z)`
is `v(k, z)`. -/
theorem hasSum_expected_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ) {α β k z : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k) (hz : 0 < z) :
    HasSum (fun t => β ^ t * ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ)
      (stochValue α β (∫ z, log z ∂μ) k z) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1 : α * β < 1 := by nlinarith
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  have h1β : (1 - β) ≠ 0 := (sub_pos.2 hβ1).ne'
  have h1ab : (1 - α * β) ≠ 0 := (sub_pos.2 h1).ne'
  set m := ∫ z, log z ∂μ
  set M1 := meanLogK μ α β k z 1
  -- the terms after period 0, as geometric series
  have hterm : ∀ s, β ^ (s + 1) * ∫ ω, log (stochCons α β k z ω (s + 1)) ∂shockMeasure μ =
      β * (log (1 - α * β) + m + α * (log (α * β) + m) / (1 - α)) * β ^ s +
        β * (α * M1 - α * (log (α * β) + m) / (1 - α)) * (α * β) ^ s := fun s => by
    rw [integral_log_cons hpos hint h0 h1 hk hz, meanLogK_succ hα1 s]
    simp only [meanShock, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, mul_pow,
      pow_succ]
    field_simp
    ring
  have hg1 := hasSum_geometric_of_lt_one hβ.le hβ1
  have hg2 := hasSum_geometric_of_lt_one h0.le h1
  have htail := (hg1.mul_left (β * (log (1 - α * β) + m + α * (log (α * β) + m) / (1 - α)))).add
    (hg2.mul_left (β * (α * M1 - α * (log (α * β) + m) / (1 - α))))
  rw [← hasSum_nat_add_iff' 1]
  convert htail using 1
  · funext s
    exact hterm s
  · rw [sum_range_one, pow_zero, one_mul, integral_log_cons hpos hint h0 h1 hk hz]
    simp only [M1, meanLogK, meanShock, ↓reduceIte, stochValue, coefAs, coefB, coefC, m]
    field_simp
    ring

end StokeyLucasPrescott.Overview

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Log-normal capital

SLP Exercise 2.7, p. 20.

Under policy (5), `k_{t+1} = αβ z_t k_t^α`, so `ln k_{t+1} = ln(αβ) + α ln k_t + ln z_t`. If the
`ln z_t` are i.i.d. `N(m, σ²)`, each `ln k_t` is normal.

* `capPath`, `log_capPath`: the capital path in levels has logarithm `logPath`.
* `logPath_eq`: `ln k_t = c_t + ∑_{s<t} α^{t−1−s} ln z_s`, a function of past shocks only.
* `indepFun_logPath`: `ln k_t` is independent of the current shock `ln z_t`.
* `hasLaw_logPath` (Ex 2.7): `ln k_t ∼ N(μ_t, σ_t²)` with `μ_{t+1} = αμ_t + ln(αβ) + m`,
  `σ²_{t+1} = α²σ_t² + σ²`; `meanN_eq`, `varN_eq`: `μ_t = αᵗ ln k₀ + (ln(αβ) + m)(1 − αᵗ)/(1 − α)`,
  `σ_t² = σ²(1 − α^{2t})/(1 − α²)`.
* `meanN_tendsto`, `varN_tendsto` (Ex 2.7): `μ_t → (ln(αβ) + m)/(1 − α)`,
  `σ_t² → σ²/(1 − α²)`.
-/

open Finset Filter Topology Real MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StokeyLucasPrescott.Overview

/-- The capital path `k_{t+1} = αβ e^{ω_t} k_t^α`, with `ω_t = ln z_t`. -/
noncomputable def capPath (α β k₀ : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => k₀
  | t + 1 => α * β * exp (ω t) * capPath α β k₀ ω t ^ α

/-- `ln k_t`: `ℓ₀` given, `ℓ_{t+1} = ln(αβ) + αℓ_t + ω_t`. -/
noncomputable def logPath (α β ℓ₀ : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => ℓ₀
  | t + 1 => log (α * β) + α * logPath α β ℓ₀ ω t + ω t

/-- The capital path in levels has logarithm `logPath`, and stays positive. -/
theorem log_capPath {α β k₀ : ℝ} (h0 : 0 < α * β) (hk₀ : 0 < k₀) (ω : ℕ → ℝ) (t : ℕ) :
    0 < capPath α β k₀ ω t ∧ log (capPath α β k₀ ω t) = logPath α β (log k₀) ω t := by
  induction t with
  | zero => exact ⟨hk₀, rfl⟩
  | succ t ih =>
    obtain ⟨hp, hl⟩ := ih
    refine ⟨mul_pos (mul_pos h0 (exp_pos _)) (rpow_pos_of_pos hp α), ?_⟩
    simp only [capPath, logPath]
    rw [log_mul (mul_pos h0 (exp_pos _)).ne' (rpow_pos_of_pos hp α).ne',
      log_mul h0.ne' (exp_pos _).ne', log_exp, log_rpow hp, hl]
    ring

/-- The deterministic part of `ln k_t`: `c₀ = ℓ₀`, `c_{t+1} = ln(αβ) + αc_t`. -/
noncomputable def constPath (α β ℓ₀ : ℝ) : ℕ → ℝ
  | 0 => ℓ₀
  | t + 1 => log (α * β) + α * constPath α β ℓ₀ t

/-- `ln k_t = c_t + ∑_{s<t} α^{t−1−s} ω_s`. -/
theorem logPath_eq (α β ℓ₀ : ℝ) (ω : ℕ → ℝ) (t : ℕ) :
    logPath α β ℓ₀ ω t = constPath α β ℓ₀ t + ∑ s ∈ range t, α ^ (t - 1 - s) * ω s := by
  induction t with
  | zero => simp [logPath, constPath]
  | succ t ih =>
    simp only [logPath, constPath, ih, sum_range_succ, Nat.add_sub_cancel, Nat.sub_self,
      pow_zero, one_mul, mul_add, mul_sum]
    have : ∀ s ∈ range t, α * (α ^ (t - 1 - s) * ω s) = α ^ (t - s) * ω s := fun s hs => by
      have hs := mem_range.1 hs
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [sum_congr rfl this]
    ring

theorem measurable_logPath (α β ℓ₀ : ℝ) (t : ℕ) :
    Measurable fun ω : ℕ → ℝ => logPath α β ℓ₀ ω t := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (measurable_const.add (ih.const_mul α)).add (measurable_pi_apply t)

/-- **`ln k_t` is independent of the current shock** under any product probability measure. -/
theorem indepFun_logPath {ν : Measure ℝ} [IsProbabilityMeasure ν] (α β ℓ₀ : ℝ) (t : ℕ) :
    IndepFun (fun ω => logPath α β ℓ₀ ω t) (fun ω => ω t)
      (Measure.infinitePi fun _ : ℕ => ν) := by
  set c : ℕ → ℝ := fun s => if s < t then α ^ (t - 1 - s) else 1
  have hind : iIndepFun (fun s (ω : ℕ → ℝ) => c s * ω s) (Measure.infinitePi fun _ : ℕ => ν) :=
    iIndepFun_infinitePi (X := fun s x => c s * x) fun s => measurable_const.mul measurable_id
  have hmeas : ∀ s, Measurable fun ω : ℕ → ℝ => c s * ω s :=
    fun s => measurable_const.mul (measurable_pi_apply s)
  have hsum := hind.indepFun_finsetSum_of_notMem hmeas (s := range t) (i := t) (by simp)
  have h := hsum.comp (measurable_const_add (constPath α β ℓ₀ t)) measurable_id
  convert h using 1
  · funext ω
    simp only [Function.comp_apply, Finset.sum_apply, logPath_eq]
    congr 1
    refine sum_congr rfl fun s hs => ?_
    simp [c, mem_range.1 hs]
  · funext ω
    simp [c]

/-- The means `μ₀ = ℓ₀`, `μ_{t+1} = αμ_t + ln(αβ) + m`. -/
noncomputable def meanN (α β ℓ₀ m : ℝ) : ℕ → ℝ
  | 0 => ℓ₀
  | t + 1 => α * meanN α β ℓ₀ m t + log (α * β) + m

/-- `α²` as a nonnegative real. -/
noncomputable def sqNN (α : ℝ) : ℝ≥0 := ⟨α ^ 2, sq_nonneg α⟩

theorem coe_sqNN (α : ℝ) : (sqNN α : ℝ) = α ^ 2 := rfl

/-- The variances `σ₀² = 0`, `σ²_{t+1} = α²σ_t² + σ²`. -/
noncomputable def varN (α : ℝ) (v : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 0
  | t + 1 => sqNN α * varN α v t + v

/-- **Ex 2.7.** If the log shocks are i.i.d. `N(m, σ²)`, then `ln k_t ∼ N(μ_t, σ_t²)`. -/
theorem hasLaw_logPath (α β ℓ₀ m : ℝ) (v : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω => logPath α β ℓ₀ ω t) (gaussianReal (meanN α β ℓ₀ m t) (varN α v t))
      (Measure.infinitePi fun _ : ℕ => gaussianReal m v) := by
  set P := Measure.infinitePi fun _ : ℕ => gaussianReal m v
  induction t with
  | zero =>
    refine ⟨measurable_const.aemeasurable, ?_⟩
    simp only [logPath, meanN, varN, gaussianReal_zero_var]
    rw [Measure.map_const, measure_univ, one_smul]
  | succ t ih =>
    -- the two summands and their laws
    set X : (ℕ → ℝ) → ℝ := fun ω => log (α * β) + α * logPath α β ℓ₀ ω t
    set Y : (ℕ → ℝ) → ℝ := fun ω => ω t
    have hφ : Measurable fun x : ℝ => log (α * β) + α * x := measurable_const.add
      (measurable_const.mul measurable_id)
    have hX : HasLaw X (gaussianReal (α * meanN α β ℓ₀ m t + log (α * β))
        (sqNN α * varN α v t)) P := by
      refine ⟨(hφ.comp (measurable_logPath α β ℓ₀ t)).aemeasurable, ?_⟩
      have hmul : (P.map fun ω => logPath α β ℓ₀ ω t).map (fun x => α * x) =
          gaussianReal (α * meanN α β ℓ₀ m t) (sqNN α * varN α v t) := by
        rw [ih.map_eq, gaussianReal_map_const_mul]
        rfl
      have hmap' : P.map X = ((P.map fun ω => logPath α β ℓ₀ ω t).map (fun x => α * x)).map
          (fun x => x + log (α * β)) := by
        rw [Measure.map_map (measurable_add_const _) (measurable_const_mul α),
          Measure.map_map ((measurable_add_const _).comp (measurable_const_mul α))
            (measurable_logPath α β ℓ₀ t)]
        congr 1
        funext ω
        simp [X, add_comm]
      rw [hmap', hmul, gaussianReal_map_add_const]
    have hY : HasLaw Y (gaussianReal m v) P :=
      ⟨(measurable_pi_apply t).aemeasurable, Measure.infinitePi_map_eval _ t⟩
    have hXY : IndepFun X Y P := (indepFun_logPath (ν := gaussianReal m v) α β ℓ₀ t).comp hφ
      measurable_id
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hXY hX hY
    have hfun : (fun ω => logPath α β ℓ₀ ω (t + 1)) = X + Y := by
      funext ω
      simp [X, Y, logPath]
    refine ⟨(measurable_logPath α β ℓ₀ (t + 1)).aemeasurable, ?_⟩
    rw [hfun, hsum]
    rfl

/-- **Ex 2.7.** `μ_t = αᵗ ln k₀ + (ln(αβ) + m)(1 − αᵗ)/(1 − α)`. -/
theorem meanN_eq {α β ℓ₀ m : ℝ} (hα1 : α < 1) (t : ℕ) :
    meanN α β ℓ₀ m t = α ^ t * ℓ₀ + (log (α * β) + m) * (1 - α ^ t) / (1 - α) := by
  have h1α : (1 - α) ≠ 0 := (sub_pos.2 hα1).ne'
  induction t with
  | zero => simp [meanN]
  | succ t ih =>
    simp only [meanN, ih]
    field_simp
    ring

/-- **Ex 2.7.** `σ_t² = σ²(1 − α^{2t})/(1 − α²)`. -/
theorem varN_eq {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (v : ℝ≥0) (t : ℕ) :
    (varN α v t : ℝ) = v * (1 - (α ^ 2) ^ t) / (1 - α ^ 2) := by
  have h2 : (1 - α ^ 2) ≠ 0 := by nlinarith
  induction t with
  | zero => simp [varN]
  | succ t ih =>
    rw [varN, NNReal.coe_add, NNReal.coe_mul, coe_sqNN, ih]
    field_simp
    ring

/-- **Ex 2.7.** `μ_t → (ln(αβ) + m)/(1 − α)`. -/
theorem meanN_tendsto {α β ℓ₀ m : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (meanN α β ℓ₀ m) atTop (𝓝 ((log (α * β) + m) / (1 - α))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
  have := ((hp.mul_const ℓ₀).add (((tendsto_const_nhds (x := log (α * β) + m)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).div_const (1 - α)))
  simp only [zero_mul, zero_add, sub_zero, mul_one] at this
  refine this.congr fun t => ?_
  rw [meanN_eq hα1]

/-- **Ex 2.7.** `σ_t² → σ²/(1 − α²)`. -/
theorem varN_tendsto {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (v : ℝ≥0) :
    Tendsto (fun t => (varN α v t : ℝ)) atTop (𝓝 (v / (1 - α ^ 2))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg α) (by nlinarith : α ^ 2 < 1)
  have := ((tendsto_const_nhds (x := (v : ℝ))).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp)).div_const (1 - α ^ 2)
  simp only [sub_zero, mul_one] at this
  refine this.congr fun t => ?_
  rw [varN_eq hα0 hα1]

end StokeyLucasPrescott.Overview

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A constant savings rate

SLP Exercise 2.4, p. 15: `g(k) = s f(k)` with `f` as in Exercise 2.1.

For any `g` on `[0, ∞)` that is continuous, strictly increasing and strictly concave with
`g(0) = 0`, lying above the 45° line somewhere and below it somewhere:

* `exists_unique_fixedPoint` (Ex 2.4a): there is exactly one positive stationary point `k*`;
  `lt_of_lt_fixed`, `gt_of_gt_fixed`: `g(k) > k` below it and `g(k) < k` above it.
* `tendsto_fixedPoint`, `monotone_of_le`, `antitone_of_ge` (Ex 2.4b): from every `k₀ > 0` the
  sequence `k_{t+1} = g(k_t)` converges monotonically to `k*`; `iterate_eq_fixed_iff`: it reaches
  `k*` in finitely many periods only if it starts there.
* `savings_crossings`, `savings_unique_steady_state`: for `f` neoclassical, `s > 0` and
  `s(1 − δ) < 1` give the two crossings. The book states only `s > 0`; see
  `docs/corrections.md`.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.Overview

/-- The assumptions on a savings function `g` on `[0, ∞)`. -/
structure SavingsMap (g : ℝ → ℝ) : Prop where
  zero : g 0 = 0
  cont : ContinuousOn g (Ici 0)
  mono : StrictMonoOn g (Ici 0)
  conc : StrictConcaveOn ℝ (Ici 0) g
  above : ∃ a, 0 < a ∧ a < g a
  below : ∃ b, 0 < b ∧ g b < b

namespace SavingsMap

variable {g : ℝ → ℝ} (hg : SavingsMap g)
include hg

/-- `g(k) − k` is strictly concave and vanishes at `0`, so it changes sign at most once on
`(0, ∞)`: if it is `≥ 0` at `y > 0` it is `> 0` on `(0, y)`. -/
theorem pos_of_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y ≤ g y) : x < g x := by
  have hy0 : 0 < y := hx.trans hxy
  have hA : 0 < 1 - x / y := by rw [sub_pos, div_lt_one hy0]; exact hxy
  have hB : 0 < x / y := by positivity
  have h := hg.conc.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy0.le) hy0.ne hA hB (by ring)
  simp only [smul_eq_mul, hg.zero, mul_zero, zero_add] at h
  rw [show x / y * y = x by field_simp] at h
  have : x / y * y ≤ x / y * g y := mul_le_mul_of_nonneg_left hy (by positivity)
  rw [show x / y * y = x by field_simp] at this
  linarith

/-- **Ex 2.4a.** There is exactly one positive stationary point. -/
theorem exists_unique_fixedPoint : ∃! k, 0 < k ∧ g k = k := by
  obtain ⟨a, ha, hga⟩ := hg.above
  obtain ⟨b, hb, hgb⟩ := hg.below
  have hab : a < b := by
    by_contra h
    push Not at h
    rcases h.eq_or_lt with rfl | h
    · linarith
    · have := hg.pos_of_lt hb h hga.le
      linarith
  -- existence by the intermediate value theorem for `g(k) − k`
  have hcont : ContinuousOn (fun k => g k - k) (Icc a b) :=
    (hg.cont.mono fun x hx => Set.mem_Ici.2 (ha.le.trans hx.1)).sub continuousOn_id
  obtain ⟨k, hk, hk0⟩ := intermediate_value_Icc' hab.le hcont
    (show (0 : ℝ) ∈ Icc (g b - b) (g a - a) from ⟨by linarith, by linarith⟩)
  refine ⟨k, ⟨ha.trans_le hk.1, by linarith⟩, fun j ⟨hj, hgj⟩ => ?_⟩
  -- uniqueness: two positive fixed points contradict strict concavity
  have hk0' : 0 < k := ha.trans_le hk.1
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hg.pos_of_lt hj h (by linarith)
    linarith
  · have := hg.pos_of_lt hk0' h hgj.ge
    linarith

/-- The positive stationary point `k*`. -/
noncomputable def kstar : ℝ := Classical.choose hg.exists_unique_fixedPoint

theorem kstar_pos : 0 < hg.kstar := (Classical.choose_spec hg.exists_unique_fixedPoint).1.1

theorem g_kstar : g hg.kstar = hg.kstar := (Classical.choose_spec hg.exists_unique_fixedPoint).1.2

theorem eq_kstar {k : ℝ} (hk : 0 < k) (hgk : g k = k) : k = hg.kstar :=
  (Classical.choose_spec hg.exists_unique_fixedPoint).2 k ⟨hk, hgk⟩

/-- Below `k*` the map lies above the 45° line. -/
theorem lt_of_lt_fixed {k : ℝ} (hk : 0 < k) (hks : k < hg.kstar) : k < g k :=
  hg.pos_of_lt hk hks hg.g_kstar.ge

/-- Above `k*` the map lies below the 45° line. -/
theorem gt_of_gt_fixed {k : ℝ} (hks : hg.kstar < k) : g k < k := by
  by_contra h
  push Not at h
  have := hg.pos_of_lt hg.kstar_pos hks h
  rw [hg.g_kstar] at this
  exact lt_irrefl _ this

theorem g_pos {k : ℝ} (hk : 0 < k) : 0 < g k := by
  have := hg.mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hk.le) hk
  rwa [hg.zero] at this

/-- Iterates from `k₀ ∈ (0, k*]` stay in `(0, k*]` and increase. -/
theorem iterate_mem_below {k₀ : ℝ} (hk₀ : 0 < k₀) (hle : k₀ ≤ hg.kstar) (t : ℕ) :
    0 < g^[t] k₀ ∧ g^[t] k₀ ≤ hg.kstar ∧ g^[t] k₀ ≤ g^[t + 1] k₀ := by
  induction t with
  | zero =>
    refine ⟨hk₀, hle, ?_⟩
    rcases hle.eq_or_lt with h | h
    · simp [h, hg.g_kstar]
    · exact (hg.lt_of_lt_fixed hk₀ h).le
  | succ t ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hpos : 0 < g^[t + 1] k₀ := by
      rw [Function.iterate_succ_apply']; exact hg.g_pos h0
    have hle' : g^[t + 1] k₀ ≤ hg.kstar := by
      rw [Function.iterate_succ_apply', ← hg.g_kstar]
      exact hg.mono.monotoneOn (Set.mem_Ici.2 h0.le) (Set.mem_Ici.2 hg.kstar_pos.le) h1
    refine ⟨hpos, hle', ?_⟩
    rw [Function.iterate_succ_apply' g (t + 1)]
    rcases hle'.eq_or_lt with h | h
    · rw [h, hg.g_kstar]
    · exact (hg.lt_of_lt_fixed hpos h).le

/-- Iterates from `k₀ ≥ k*` stay above `k*` and decrease. -/
theorem iterate_mem_above {k₀ : ℝ} (hge : hg.kstar ≤ k₀) (t : ℕ) :
    hg.kstar ≤ g^[t] k₀ ∧ g^[t + 1] k₀ ≤ g^[t] k₀ := by
  induction t with
  | zero =>
    refine ⟨hge, ?_⟩
    rcases hge.eq_or_lt with h | h
    · simp [← h, hg.g_kstar]
    · exact (hg.gt_of_gt_fixed h).le
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    have hge' : hg.kstar ≤ g^[t + 1] k₀ := by
      rw [Function.iterate_succ_apply', ← hg.g_kstar]
      exact hg.mono.monotoneOn (Set.mem_Ici.2 hg.kstar_pos.le)
        (Set.mem_Ici.2 (hg.kstar_pos.le.trans h1)) h1
    refine ⟨hge', ?_⟩
    rw [Function.iterate_succ_apply' g (t + 1)]
    rcases hge'.eq_or_lt with h | h
    · rw [← h, hg.g_kstar]
    · exact (hg.gt_of_gt_fixed h).le

/-- **Ex 2.4b (monotonicity).** From `k₀ ∈ (0, k*]` the sequence rises. -/
theorem monotone_of_le {k₀ : ℝ} (hk₀ : 0 < k₀) (hle : k₀ ≤ hg.kstar) :
    Monotone fun t => g^[t] k₀ :=
  monotone_nat_of_le_succ fun t => (hg.iterate_mem_below hk₀ hle t).2.2

/-- **Ex 2.4b (monotonicity).** From `k₀ ≥ k*` the sequence falls. -/
theorem antitone_of_ge {k₀ : ℝ} (hge : hg.kstar ≤ k₀) : Antitone fun t => g^[t] k₀ :=
  antitone_nat_of_succ_le fun t => (hg.iterate_mem_above hge t).2

/-- A limit of the iterates in `(0, ∞)` is a fixed point, hence `k*`. -/
theorem limit_eq_kstar {k₀ L : ℝ} (hL : 0 < L) (hlim : Tendsto (fun t => g^[t] k₀) atTop (𝓝 L))
    (hpos : ∀ t, 0 ≤ g^[t] k₀) : L = hg.kstar := by
  have hcontL : ContinuousWithinAt g (Ici 0) L := hg.cont L (Set.mem_Ici.2 hL.le)
  have h1 : Tendsto (fun t => g (g^[t] k₀)) atTop (𝓝 (g L)) :=
    hcontL.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hpos⟩)
  have h2 : Tendsto (fun t => g (g^[t] k₀)) atTop (𝓝 L) := by
    have := hlim.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Function.iterate_succ_apply'] using this
  exact hg.eq_kstar hL (tendsto_nhds_unique h1 h2)

/-- **Ex 2.4b.** From every `k₀ > 0` the sequence `k_{t+1} = g(k_t)` converges to `k*`. -/
theorem tendsto_fixedPoint {k₀ : ℝ} (hk₀ : 0 < k₀) :
    Tendsto (fun t => g^[t] k₀) atTop (𝓝 hg.kstar) := by
  rcases le_total k₀ hg.kstar with hle | hge
  · have hb := hg.iterate_mem_below hk₀ hle
    have hmono := hg.monotone_of_le hk₀ hle
    have hbdd : BddAbove (range fun t => g^[t] k₀) :=
      ⟨hg.kstar, by rintro _ ⟨t, rfl⟩; exact (hb t).2.1⟩
    have hlim := tendsto_atTop_ciSup hmono hbdd
    have hLpos : 0 < ⨆ t, g^[t] k₀ := hk₀.trans_le (le_ciSup hbdd 0)
    rwa [← hg.limit_eq_kstar hLpos hlim fun t => (hb t).1.le]
  · have ha := hg.iterate_mem_above hge
    have hanti := hg.antitone_of_ge hge
    have hbdd : BddBelow (range fun t => g^[t] k₀) :=
      ⟨hg.kstar, by rintro _ ⟨t, rfl⟩; exact (ha t).1⟩
    have hlim := tendsto_atTop_ciInf hanti hbdd
    have hLpos : 0 < ⨅ t, g^[t] k₀ :=
      hg.kstar_pos.trans_le (le_ciInf fun t => (ha t).1)
    rwa [← hg.limit_eq_kstar hLpos hlim fun t => (hg.kstar_pos.le.trans (ha t).1)]

/-- **Ex 2.4b (no finite-time arrival).** The sequence reaches `k*` in finitely many periods only
if `k₀ = k*`. -/
theorem iterate_eq_fixed_iff {k₀ : ℝ} (hk₀ : 0 < k₀) (t : ℕ) :
    g^[t] k₀ = hg.kstar ↔ k₀ = hg.kstar := by
  constructor
  · intro h
    induction t generalizing k₀ with
    | zero => exact h
    | succ t ih =>
      rw [Function.iterate_succ_apply] at h
      have := ih (hg.g_pos hk₀) h
      rw [← hg.g_kstar] at this
      exact hg.mono.injOn (Set.mem_Ici.2 hk₀.le) (Set.mem_Ici.2 hg.kstar_pos.le) this
  · intro h
    rw [h]
    exact Function.iterate_fixed hg.g_kstar t

end SavingsMap

namespace Neoclassical

variable {F : ℝ → ℝ → ℝ} {Fk : ℝ → ℝ} (hF : Neoclassical F Fk)
include hF

/-- Near zero `s f(k) > k`: the mean value theorem and `f′(0+) = ∞`. -/
theorem savings_above {δ s : ℝ} (hs : 0 < s) :
    ∃ a, 0 < a ∧ a < s * goods F δ a := by
  have hev : ∀ᶠ k in 𝓝[>] (0 : ℝ), 1 / s < Fk k + (1 - δ) :=
    (hF.f'_tendsto_zero δ).eventually (eventually_gt_atTop (1 / s))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set a := ε / 2
  have ha : 0 < a := by positivity
  refine ⟨a, ha, ?_⟩
  have hcont : ContinuousOn (goods F δ) (Icc 0 a) :=
    ((hF.cont_F).add (continuousOn_const.mul continuousOn_id)).mono Icc_subset_Ici_self
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (goods F δ) (fun k => Fk k + (1 - δ)) ha
    hcont (fun x hx => hF.hasDerivAt_f δ hx.1)
  have hξε : ξ ∈ Metric.ball (0 : ℝ) ε ∩ Ioi 0 :=
    ⟨by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hξ.1]
      have : ξ < ε / 2 := hξ.2
      linarith,
      hξ.1⟩
  have hbig : 1 / s < Fk ξ + (1 - δ) := hball hξε
  rw [hslope, hF.f_zero δ, sub_zero, sub_zero, lt_div_iff₀ ha] at hbig
  have e : s * (1 / s * a) = a := by field_simp
  nlinarith

/-- For large `k`, `s f(k) < k`: concavity and `s f′(∞) = s(1 − δ) < 1`. -/
theorem savings_below {δ s : ℝ} (hs : 0 < s) (hsδ : s * (1 - δ) < 1) :
    ∃ b, 0 < b ∧ s * goods F δ b < b := by
  -- a point `K` where `s f′(K) < 1`
  have hev : ∀ᶠ k in atTop, s * (Fk k + (1 - δ)) < 1 := by
    have := ((hF.f'_tendsto_atTop δ).const_mul s).eventually (gt_mem_nhds hsδ)
    exact this
  obtain ⟨K, hK⟩ := (hev.and (eventually_gt_atTop 0)).exists
  set m := Fk K + (1 - δ)
  have hm : s * m < 1 := hK.1
  -- the tangent line at `K` bounds `f`
  have htan : ∀ k, 0 ≤ k → goods F δ k ≤ goods F δ K + m * (k - K) := fun k hk =>
    concave_le_tangent (hF.strictConcaveOn_f δ).concaveOn (Set.mem_Ici.2 hK.2.le) (Set.mem_Ici.2 hk)
      (hF.hasDerivAt_f δ hK.2)
  set b := max K ((s * |goods F δ K| + s * |m| * K + 1) / (1 - s * m)) + 1
  have h1 : 0 < 1 - s * m := sub_pos.2 hm
  have hbK : K < b := by simp only [b]; linarith [le_max_left K ((s * |goods F δ K| +
    s * |m| * K + 1) / (1 - s * m))]
  have hbig : (s * |goods F δ K| + s * |m| * K + 1) / (1 - s * m) < b := by
    simp only [b]; linarith [le_max_right K ((s * |goods F δ K| + s * |m| * K + 1) / (1 - s * m))]
  have hb0 : 0 < b := hK.2.trans hbK
  refine ⟨b, hb0, ?_⟩
  have ht := mul_le_mul_of_nonneg_left (htan b hb0.le) hs.le
  rw [div_lt_iff₀ h1] at hbig
  have e1 : s * goods F δ K ≤ s * |goods F δ K| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.le
  have e2 : -(s * m * K) ≤ s * |m| * K := by
    have : -(m * K) ≤ |m| * K := by
      have := neg_abs_le m
      nlinarith [hK.2]
    nlinarith
  nlinarith

/-- **Ex 2.4 (crossings).** With `s > 0` and `s(1 − δ) < 1`, `g = s f` is a savings map. -/
theorem savings_crossings {δ s : ℝ} (hδ1 : δ ≤ 1) (hs : 0 < s) (hsδ : s * (1 - δ) < 1) :
    SavingsMap fun k => s * goods F δ k where
  zero := by simp [hF.f_zero δ]
  cont := continuousOn_const.mul ((hF.cont_F).add (continuousOn_const.mul continuousOn_id))
  mono := fun x hx y hy hxy => mul_lt_mul_of_pos_left (hF.strictMonoOn_f hδ1 hx hy hxy) hs
  conc := ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => by
    have := (hF.strictConcaveOn_f δ).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at this ⊢
    nlinarith⟩
  above := hF.savings_above hs
  below := hF.savings_below hs hsδ

/-- **Ex 2.4a for the neoclassical model.** There is exactly one positive stationary point of
`k ↦ s f(k)`, and every path from `k₀ > 0` converges monotonically to it. -/
theorem savings_unique_steady_state {δ s : ℝ} (hδ1 : δ ≤ 1) (hs : 0 < s)
    (hsδ : s * (1 - δ) < 1) : ∃! k, 0 < k ∧ s * goods F δ k = k :=
  (hF.savings_crossings hδ1 hs hsδ).exists_unique_fixedPoint

end Neoclassical

end StokeyLucasPrescott.Overview

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The objective (2) along policy (5)

SLP §2.2, (2), p. 17, and Exercise 2.6, p. 19.

Exercise 2.6 asks for "the value of the objective function (2)", `E[∑ βᵗ U(c_t)]`, along policy
(5) from `k₀ = k`, `z₀ = z`, and calls it `v(k, z)`. `hasSum_expected_utility` computes
`∑ βᵗ E[ln c_t] = v(k, z)`; here the expectation is taken outside the sum, as in (2).

The bound is `E|ln c_t| ≤ D` uniformly in `t` (with `α < 1`, `E|ln k_t|` stays bounded), so
`∑ βᵗ E|ln c_t| < ∞` and expectation and sum can be exchanged (Fubini–Tonelli for series).

* `ae_summable_norm_of_summable_integral_norm`, `integrable_tsum_of_summable_integral_norm`:
  if `∑ₙ E|fₙ| < ∞` then `∑ₙ |fₙ|` is a.e. finite and `∑ₙ fₙ` is integrable.
* `integral_abs_log_shock_le`, `integral_abs_log_path_le`, `integral_abs_log_cons_le`:
  `E|ln z_t| ≤ Z`, `E|ln k_t| ≤ K`, `E|ln c_t| ≤ D` for all `t`.
* `ae_summable_utility`: almost surely `∑ βᵗ ln c_t(ω)` converges absolutely.
* `integrable_utility`: `ω ↦ ∑ βᵗ ln c_t(ω)` is integrable.
* `hasSum_integral_utility`, `integral_tsum_utility`: `E[∑ βᵗ ln c_t] = ∑ βᵗ E[ln c_t]`.
* `integral_utility_eq_stochValue` (Ex 2.6): `E[∑ βᵗ ln c_t] = v(k, z) = A + B ln k + C ln z`,
  the function of `StochasticLog` that satisfies (3).
-/

namespace StokeyLucasPrescott.Overview

open Finset Set Filter Topology Real MeasureTheory ProbabilityTheory

/-- If the integrable `fₙ` have `∑ₙ E|fₙ| < ∞`, then `∫⁻ ∑ₙ ‖fₙ‖ₑ < ∞` and almost surely
`∑ₙ |fₙ(ω)|` converges. -/
theorem ae_summable_norm_of_summable_integral_norm {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} (hf : ∀ n, Integrable (f n) P)
    (hs : Summable fun n => ∫ ω, ‖f n ω‖ ∂P) :
    (∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂P ≠ ⊤) ∧ ∀ᵐ ω ∂P, Summable fun n => ‖f n ω‖ := by
  have htop : ∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hf n).1.enorm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hf _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun ω => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨htop, ?_⟩
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun n => (hf n).1.enorm) htop] with ω hω
  exact tsum_enorm_ne_top_iff_summable_norm.1 hω.ne

/-- If the integrable `fₙ` have `∑ₙ E|fₙ| < ∞`, then `ω ↦ ∑ₙ fₙ(ω)` is integrable. -/
theorem integrable_tsum_of_summable_integral_norm {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : ℕ → Ω → ℝ} (hf : ∀ n, Integrable (f n) P)
    (hs : Summable fun n => ∫ ω, ‖f n ω‖ ∂P) :
    Integrable (fun ω => ∑' n, f n ω) P := by
  obtain ⟨htop, hae⟩ := ae_summable_norm_of_summable_integral_norm hf hs
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ n ∈ range N, f n ω)
    (fun N => (integrable_finsetSum (range N) fun n _ => hf n).1) ?_, ?_⟩
  · filter_upwards [hae] with ω hω
    exact hω.of_norm.hasSum.tendsto_sum_nat
  · rw [hasFiniteIntegral_iff_enorm]
    exact (lintegral_mono fun ω => enorm_tsum_le_tsum_enorm).trans_lt htop.lt_top

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- `|ln z_t|` is integrable and `E|ln z_t| ≤ |ln z| + E_μ|ln z′|` for every `t`. -/
theorem integral_abs_log_shock_le (hint : Integrable log μ) (z : ℝ) (t : ℕ) :
    Integrable (fun ω => |log (shock z ω t)|) (shockMeasure μ) ∧
      ∫ ω, |log (shock z ω t)| ∂shockMeasure μ ≤ |log z| + ∫ x, |log x| ∂μ := by
  refine ⟨(integrable_log_shock hint z t).abs, ?_⟩
  have h0 : 0 ≤ ∫ x, |log x| ∂μ := integral_nonneg fun x => abs_nonneg _
  rcases t with _ | t
  · simp [shock, h0]
  · have e : ∫ ω, |log (ω (t + 1))| ∂shockMeasure μ = ∫ x, |log x| ∂μ := by
      rw [← integral_map (φ := fun ω : ℕ → ℝ => ω (t + 1)) (f := fun x => |log x|)
        (measurable_pi_apply (t + 1)).aemeasurable
        (continuous_abs.measurable.comp measurable_log).aestronglyMeasurable,
        Measure.infinitePi_map_eval]
    simp only [shock, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rw [e]
    linarith [abs_nonneg (log z)]

/-- Along policy (5), `E|ln k_t| ≤ K = |ln k| + (|ln(αβ)| + Z)/(1 − α)` for every `t`, where
`Z = |ln z| + E_μ|ln z′|`: `E|ln k_{t+1}| ≤ |ln(αβ)| + Z + αE|ln k_t|` and `K` is a fixed point
bound for this recursion. -/
theorem integral_abs_log_path_le (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    ∫ ω, |log (stochPath α β k z ω t)| ∂shockMeasure μ ≤
      |log k| + (|log (α * β)| + (|log z| + ∫ x, |log x| ∂μ)) / (1 - α) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1α : 0 < 1 - α := sub_pos.2 hα1
  set Z := |log z| + ∫ x, |log x| ∂μ
  set K := |log k| + (|log (α * β)| + Z) / (1 - α)
  have hK : |log (α * β)| + Z + α * K ≤ K := by
    have : (1 - α) * K = (1 - α) * |log k| + (|log (α * β)| + Z) := by
      simp only [K]; field_simp
    nlinarith [abs_nonneg (log k)]
  induction t with
  | zero =>
    simp only [stochPath, integral_const, probReal_univ, smul_eq_mul, one_mul, K]
    have : 0 ≤ (|log (α * β)| + Z) / (1 - α) := by
      apply div_nonneg _ h1α.le
      have : 0 ≤ ∫ x, |log x| ∂μ := integral_nonneg fun x => abs_nonneg _
      positivity
    linarith
  | succ t ih =>
    have hi := (integral_log_path hpos hint h0 hk hz t).1
    have hi' := (integral_log_path hpos hint h0 hk hz (t + 1)).1
    have hs := integral_abs_log_shock_le hint z t
    have hle : (fun ω => |log (stochPath α β k z ω (t + 1))|) ≤ᵐ[shockMeasure μ]
        fun ω => |log (α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)| := by
      filter_upwards [ae_log_path hpos h0 hk hz] with ω hω
      rw [(hω t).2.2]
      calc |log (α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t)|
          ≤ |log (α * β) + log (shock z ω t)| + |α * log (stochPath α β k z ω t)| :=
            abs_add_le _ _
        _ ≤ _ := by
            rw [abs_mul, abs_of_pos hα]
            linarith [abs_add_le (log (α * β)) (log (shock z ω t))]
    have hA : Integrable (fun ω => |log (α * β)| + |log (shock z ω t)|) (shockMeasure μ) :=
      (integrable_const _).add hs.1
    have hB := hi.abs.const_mul α
    calc ∫ ω, |log (stochPath α β k z ω (t + 1))| ∂shockMeasure μ
        ≤ ∫ ω, |log (α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)|
            ∂shockMeasure μ := integral_mono_ae hi'.abs (hA.add hB) hle
      _ = |log (α * β)| + ∫ ω, |log (shock z ω t)| ∂shockMeasure μ +
            α * ∫ ω, |log (stochPath α β k z ω t)| ∂shockMeasure μ := by
          rw [integral_add hA hB, integral_add (integrable_const _) hs.1, integral_const,
            integral_const_mul]
          simp
      _ ≤ |log (α * β)| + Z + α * K := by
          have := mul_le_mul_of_nonneg_left ih hα.le
          linarith [hs.2]
      _ ≤ K := hK


/-- Almost surely `ln c_t = ln(1 − αβ) + ln z_t + α ln k_t` along policy (5). -/
theorem ae_log_cons (hpos : ∀ᵐ z ∂μ, 0 < z) {α β k z : ℝ} (h0 : 0 < α * β) (h1 : α * β < 1)
    (hk : 0 < k) (hz : 0 < z) (t : ℕ) :
    (fun ω => log (stochCons α β k z ω t)) =ᵐ[shockMeasure μ]
      fun ω => log (1 - α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t) := by
  have h1ab : 0 < 1 - α * β := sub_pos.2 h1
  filter_upwards [ae_log_path hpos h0 hk hz] with ω hω
  obtain ⟨hs, hp, -⟩ := hω t
  unfold stochCons
  rw [show shock z ω t * stochPath α β k z ω t ^ α - stochPath α β k z ω (t + 1) =
    (1 - α * β) * shock z ω t * stochPath α β k z ω t ^ α by simp only [stochPath]; ring,
    log_mul (mul_pos h1ab hs).ne' (rpow_pos_of_pos hp α).ne', log_mul h1ab.ne' hs.ne',
    log_rpow hp]

/-- Along policy (5), `ln c_t` is integrable and `E|ln c_t| ≤ |ln(1 − αβ)| + Z + αK` for every
`t`. -/
theorem integral_abs_log_cons_le (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) (t : ℕ) :
    Integrable (fun ω => log (stochCons α β k z ω t)) (shockMeasure μ) ∧
      ∫ ω, |log (stochCons α β k z ω t)| ∂shockMeasure μ ≤
        |log (1 - α * β)| + (|log z| + ∫ x, |log x| ∂μ) +
          α * (|log k| + (|log (α * β)| + (|log z| + ∫ x, |log x| ∂μ)) / (1 - α)) := by
  have h0 : 0 < α * β := mul_pos hα hβ
  have h1 : α * β < 1 := by nlinarith
  have heq := ae_log_cons hpos h0 h1 hk hz t (μ := μ)
  have hi := (integral_log_path hpos hint h0 hk hz t).1
  have hs := integral_abs_log_shock_le hint z t
  have hc : Integrable (fun ω => log (stochCons α β k z ω t)) (shockMeasure μ) :=
    (((integrable_const _).add (integrable_log_shock hint z t)).add (hi.const_mul α)).congr
      heq.symm
  refine ⟨hc, ?_⟩
  have hle : (fun ω => |log (stochCons α β k z ω t)|) ≤ᵐ[shockMeasure μ]
      fun ω => |log (1 - α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)| := by
    filter_upwards [heq] with ω hω
    rw [hω]
    calc |log (1 - α * β) + log (shock z ω t) + α * log (stochPath α β k z ω t)|
        ≤ |log (1 - α * β) + log (shock z ω t)| + |α * log (stochPath α β k z ω t)| :=
          abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_pos hα]
          linarith [abs_add_le (log (1 - α * β)) (log (shock z ω t))]
  have hA : Integrable (fun ω => |log (1 - α * β)| + |log (shock z ω t)|) (shockMeasure μ) :=
    (integrable_const _).add hs.1
  have hB := hi.abs.const_mul α
  calc ∫ ω, |log (stochCons α β k z ω t)| ∂shockMeasure μ
      ≤ ∫ ω, |log (1 - α * β)| + |log (shock z ω t)| + α * |log (stochPath α β k z ω t)|
          ∂shockMeasure μ := integral_mono_ae hc.abs (hA.add hB) hle
    _ = |log (1 - α * β)| + ∫ ω, |log (shock z ω t)| ∂shockMeasure μ +
          α * ∫ ω, |log (stochPath α β k z ω t)| ∂shockMeasure μ := by
        rw [integral_add hA hB, integral_add (integrable_const _) hs.1, integral_const,
          integral_const_mul]
        simp
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left
          (integral_abs_log_path_le hpos hint hα hα1 hβ hk hz t) hα.le
        linarith [hs.2]

/-- Each `βᵗ ln c_t` is integrable and `∑ₜ E|βᵗ ln c_t| < ∞`. -/
theorem summable_integral_norm_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    (∀ t, Integrable (fun ω => β ^ t * log (stochCons α β k z ω t)) (shockMeasure μ)) ∧
      Summable fun t => ∫ ω, ‖β ^ t * log (stochCons α β k z ω t)‖ ∂shockMeasure μ := by
  set Dc := |log (1 - α * β)| + (|log z| + ∫ x, |log x| ∂μ) +
    α * (|log k| + (|log (α * β)| + (|log z| + ∫ x, |log x| ∂μ)) / (1 - α))
  have hb := fun t => integral_abs_log_cons_le hpos hint hα hα1 hβ hβ1 hk hz t (μ := μ)
  refine ⟨fun t => (hb t).1.const_mul _, ?_⟩
  refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun ω => norm_nonneg _)
    (fun t => ?_) ((summable_geometric_of_lt_one hβ.le hβ1).mul_right Dc)
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hβ]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hb t).2 (pow_nonneg hβ.le t)


/-- **Ex 2.6.** Almost surely the discounted utility series `∑ βᵗ ln c_t(ω)` along policy (5)
converges absolutely. -/
theorem ae_summable_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    ∀ᵐ ω ∂shockMeasure μ, Summable fun t => |β ^ t * log (stochCons α β k z ω t)| := by
  obtain ⟨hi, hs⟩ := summable_integral_norm_utility hpos hint hα hα1 hβ hβ1 hk hz (μ := μ)
  simpa only [Real.norm_eq_abs] using (ae_summable_norm_of_summable_integral_norm hi hs).2

/-- **Ex 2.6.** The realized discounted utility `ω ↦ ∑ βᵗ ln c_t(ω)` along policy (5) is
integrable, so the objective (2) is a well-defined real number. -/
theorem integrable_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    Integrable (fun ω => ∑' t, β ^ t * log (stochCons α β k z ω t)) (shockMeasure μ) := by
  obtain ⟨hi, hs⟩ := summable_integral_norm_utility hpos hint hα hα1 hβ hβ1 hk hz (μ := μ)
  exact integrable_tsum_of_summable_integral_norm hi hs

/-- **Ex 2.6.** `∑ βᵗ E[ln c_t]` converges to `E[∑ βᵗ ln c_t]` along policy (5). -/
theorem hasSum_integral_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    HasSum (fun t => β ^ t * ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ)
      (∫ ω, ∑' t, β ^ t * log (stochCons α β k z ω t) ∂shockMeasure μ) := by
  obtain ⟨hi, hs⟩ := summable_integral_norm_utility hpos hint hα hα1 hβ hβ1 hk hz (μ := μ)
  simpa only [integral_const_mul] using hasSum_integral_of_summable_integral_norm hi hs

/-- **Ex 2.6.** `E[∑ βᵗ ln c_t] = ∑ βᵗ E[ln c_t]` along policy (5). -/
theorem integral_tsum_utility (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    ∫ ω, ∑' t, β ^ t * log (stochCons α β k z ω t) ∂shockMeasure μ =
      ∑' t, β ^ t * ∫ ω, log (stochCons α β k z ω t) ∂shockMeasure μ :=
  (hasSum_integral_utility hpos hint hα hα1 hβ hβ1 hk hz).tsum_eq.symm

/-- **Ex 2.6.** The objective (2), `E[∑ βᵗ ln c_t]`, under policy (5) from `(k, z)` is
`v(k, z) = A + B ln k + C ln z`. -/
theorem integral_utility_eq_stochValue (hpos : ∀ᵐ z ∂μ, 0 < z) (hint : Integrable log μ)
    {α β k z : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) (hk : 0 < k)
    (hz : 0 < z) :
    ∫ ω, ∑' t, β ^ t * log (stochCons α β k z ω t) ∂shockMeasure μ =
      stochValue α β (∫ z, log z ∂μ) k z :=
  (hasSum_integral_utility hpos hint hα hα1 hβ hβ1 hk hz).unique
    (hasSum_expected_utility hpos hint hα hα1 hβ hβ1 hk hz)

end StokeyLucasPrescott.Overview

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.Overview.concave_le_tangent
#print axioms StokeyLucasPrescott.Overview.strictConcave_lt_tangent
#print axioms StokeyLucasPrescott.Overview.sum_telescope
#print axioms StokeyLucasPrescott.Overview.planValue
#print axioms StokeyLucasPrescott.Overview.Feasible
#print axioms StokeyLucasPrescott.Overview.euler_optimal
#print axioms StokeyLucasPrescott.Overview.euler_unique
#print axioms StokeyLucasPrescott.Overview.euler_iff_z
#print axioms StokeyLucasPrescott.Overview.savingRate
#print axioms StokeyLucasPrescott.Overview.savingRate_zero
#print axioms StokeyLucasPrescott.Overview.savingRate_succ
#print axioms StokeyLucasPrescott.Overview.savingRate_pos
#print axioms StokeyLucasPrescott.Overview.savingRate_nonneg
#print axioms StokeyLucasPrescott.Overview.savingRate_lt_one
#print axioms StokeyLucasPrescott.Overview.z_unique
#print axioms StokeyLucasPrescott.Overview.path
#print axioms StokeyLucasPrescott.Overview.path_pos
#print axioms StokeyLucasPrescott.Overview.path_terminal
#print axioms StokeyLucasPrescott.Overview.path_consumption
#print axioms StokeyLucasPrescott.Overview.path_feasible
#print axioms StokeyLucasPrescott.Overview.path_euler
#print axioms StokeyLucasPrescott.Overview.path_optimal
#print axioms StokeyLucasPrescott.Overview.path_unique
#print axioms StokeyLucasPrescott.Overview.savingRate_tendsto
#print axioms StokeyLucasPrescott.Overview.coefB
#print axioms StokeyLucasPrescott.Overview.coefA
#print axioms StokeyLucasPrescott.Overview.logValue
#print axioms StokeyLucasPrescott.Overview.cdPath
#print axioms StokeyLucasPrescott.Overview.cdPath_pos
#print axioms StokeyLucasPrescott.Overview.logCapital
#print axioms StokeyLucasPrescott.Overview.cdPath_consumption
#print axioms StokeyLucasPrescott.Overview.hasSum_value
#print axioms StokeyLucasPrescott.Overview.bellmanRHS
#print axioms StokeyLucasPrescott.Overview.bellman_le
#print axioms StokeyLucasPrescott.Overview.bellman_attained
#print axioms StokeyLucasPrescott.Overview.bellman_isGreatest
#print axioms StokeyLucasPrescott.Overview.bellman_argmax_unique
#print axioms StokeyLucasPrescott.Overview.Neoclassical
#print axioms StokeyLucasPrescott.Overview.Neoclassical.mk
#print axioms StokeyLucasPrescott.Overview.Neoclassical.hom
#print axioms StokeyLucasPrescott.Overview.Neoclassical.zero_left
#print axioms StokeyLucasPrescott.Overview.Neoclassical.deriv_k
#print axioms StokeyLucasPrescott.Overview.Neoclassical.cont_Fk
#print axioms StokeyLucasPrescott.Overview.Neoclassical.cont_F
#print axioms StokeyLucasPrescott.Overview.Neoclassical.Fk_pos
#print axioms StokeyLucasPrescott.Overview.Neoclassical.mono_n
#print axioms StokeyLucasPrescott.Overview.Neoclassical.quasi
#print axioms StokeyLucasPrescott.Overview.Neoclassical.inada_zero
#print axioms StokeyLucasPrescott.Overview.Neoclassical.inada_top
#print axioms StokeyLucasPrescott.Overview.goods
#print axioms StokeyLucasPrescott.Overview.Neoclassical.strictMonoOn_F
#print axioms StokeyLucasPrescott.Overview.Neoclassical.F_pos
#print axioms StokeyLucasPrescott.Overview.Neoclassical.strictConcaveOn_F
#print axioms StokeyLucasPrescott.Overview.Neoclassical.f_zero
#print axioms StokeyLucasPrescott.Overview.Neoclassical.hasDerivAt_f
#print axioms StokeyLucasPrescott.Overview.Neoclassical.continuousOn_f'
#print axioms StokeyLucasPrescott.Overview.Neoclassical.f'_pos
#print axioms StokeyLucasPrescott.Overview.Neoclassical.strictMonoOn_f
#print axioms StokeyLucasPrescott.Overview.Neoclassical.strictConcaveOn_f
#print axioms StokeyLucasPrescott.Overview.Neoclassical.f'_tendsto_zero
#print axioms StokeyLucasPrescott.Overview.Neoclassical.f'_tendsto_atTop
#print axioms StokeyLucasPrescott.Overview.cobbDouglas
#print axioms StokeyLucasPrescott.Overview.cobbDouglas_neoclassical
#print axioms StokeyLucasPrescott.Overview.firm_profit_le
#print axioms StokeyLucasPrescott.Overview.firm_profit_zero
#print axioms StokeyLucasPrescott.Overview.utility
#print axioms StokeyLucasPrescott.Overview.HHFeasible
#print axioms StokeyLucasPrescott.Overview.HHBudget
#print axioms StokeyLucasPrescott.Overview.IsEquilibrium
#print axioms StokeyLucasPrescott.Overview.IsEquilibrium.mk
#print axioms StokeyLucasPrescott.Overview.IsEquilibrium.firm
#print axioms StokeyLucasPrescott.Overview.IsEquilibrium.feasible
#print axioms StokeyLucasPrescott.Overview.IsEquilibrium.budget
#print axioms StokeyLucasPrescott.Overview.IsEquilibrium.household
#print axioms StokeyLucasPrescott.Overview.IsEquilibrium.clear
#print axioms StokeyLucasPrescott.Overview.first_welfare
#print axioms StokeyLucasPrescott.Overview.priceP
#print axioms StokeyLucasPrescott.Overview.priceP_pos
#print axioms StokeyLucasPrescott.Overview.household_optimal
#print axioms StokeyLucasPrescott.Overview.second_welfare
#print axioms StokeyLucasPrescott.Overview.firmValue
#print axioms StokeyLucasPrescott.Overview.firmOwned_firm_optimal
#print axioms StokeyLucasPrescott.Overview.firmOwned_household_optimal
#print axioms StokeyLucasPrescott.Overview.pvPrice
#print axioms StokeyLucasPrescott.Overview.SeqBudget
#print axioms StokeyLucasPrescott.Overview.sequential_budget
#print axioms StokeyLucasPrescott.Overview.sequential_household_optimal
#print axioms StokeyLucasPrescott.Overview.sequential_planner_feasible
#print axioms StokeyLucasPrescott.Overview.finrank_plan
#print axioms StokeyLucasPrescott.Overview.sum_snoc
#print axioms StokeyLucasPrescott.Overview.histProb
#print axioms StokeyLucasPrescott.Overview.histProb_snoc
#print axioms StokeyLucasPrescott.Overview.zOf
#print axioms StokeyLucasPrescott.Overview.kIn
#print axioms StokeyLucasPrescott.Overview.treeCons
#print axioms StokeyLucasPrescott.Overview.fdIn
#print axioms StokeyLucasPrescott.Overview.treeValue
#print axioms StokeyLucasPrescott.Overview.TreeFeasible
#print axioms StokeyLucasPrescott.Overview.sum_shift_telescope
#print axioms StokeyLucasPrescott.Overview.tree_euler_optimal
#print axioms StokeyLucasPrescott.Overview.log_tradeoff
#print axioms StokeyLucasPrescott.Overview.log_tradeoff_unique
#print axioms StokeyLucasPrescott.Overview.coefC
#print axioms StokeyLucasPrescott.Overview.coefAs
#print axioms StokeyLucasPrescott.Overview.stochValue
#print axioms StokeyLucasPrescott.Overview.integral_stochValue
#print axioms StokeyLucasPrescott.Overview.stochRHS
#print axioms StokeyLucasPrescott.Overview.stochRHS_attained
#print axioms StokeyLucasPrescott.Overview.stochRHS_eq
#print axioms StokeyLucasPrescott.Overview.stoch_bellman_isGreatest
#print axioms StokeyLucasPrescott.Overview.stoch_argmax_unique
#print axioms StokeyLucasPrescott.Overview.shock
#print axioms StokeyLucasPrescott.Overview.stochPath
#print axioms StokeyLucasPrescott.Overview.stochCons
#print axioms StokeyLucasPrescott.Overview.shockMeasure
#print axioms StokeyLucasPrescott.Overview.ae_shock_pos
#print axioms StokeyLucasPrescott.Overview.integrable_log_coord
#print axioms StokeyLucasPrescott.Overview.integral_log_coord
#print axioms StokeyLucasPrescott.Overview.meanShock
#print axioms StokeyLucasPrescott.Overview.integrable_log_shock
#print axioms StokeyLucasPrescott.Overview.integral_log_shock
#print axioms StokeyLucasPrescott.Overview.ae_log_path
#print axioms StokeyLucasPrescott.Overview.meanLogK
#print axioms StokeyLucasPrescott.Overview.integral_log_path
#print axioms StokeyLucasPrescott.Overview.integral_log_cons
#print axioms StokeyLucasPrescott.Overview.meanLogK_succ
#print axioms StokeyLucasPrescott.Overview.hasSum_expected_utility
#print axioms StokeyLucasPrescott.Overview.capPath
#print axioms StokeyLucasPrescott.Overview.logPath
#print axioms StokeyLucasPrescott.Overview.log_capPath
#print axioms StokeyLucasPrescott.Overview.constPath
#print axioms StokeyLucasPrescott.Overview.logPath_eq
#print axioms StokeyLucasPrescott.Overview.measurable_logPath
#print axioms StokeyLucasPrescott.Overview.indepFun_logPath
#print axioms StokeyLucasPrescott.Overview.meanN
#print axioms StokeyLucasPrescott.Overview.sqNN
#print axioms StokeyLucasPrescott.Overview.coe_sqNN
#print axioms StokeyLucasPrescott.Overview.varN
#print axioms StokeyLucasPrescott.Overview.hasLaw_logPath
#print axioms StokeyLucasPrescott.Overview.meanN_eq
#print axioms StokeyLucasPrescott.Overview.varN_eq
#print axioms StokeyLucasPrescott.Overview.meanN_tendsto
#print axioms StokeyLucasPrescott.Overview.varN_tendsto
#print axioms StokeyLucasPrescott.Overview.SavingsMap
#print axioms StokeyLucasPrescott.Overview.SavingsMap.mk
#print axioms StokeyLucasPrescott.Overview.SavingsMap.zero
#print axioms StokeyLucasPrescott.Overview.SavingsMap.cont
#print axioms StokeyLucasPrescott.Overview.SavingsMap.mono
#print axioms StokeyLucasPrescott.Overview.SavingsMap.conc
#print axioms StokeyLucasPrescott.Overview.SavingsMap.above
#print axioms StokeyLucasPrescott.Overview.SavingsMap.below
#print axioms StokeyLucasPrescott.Overview.SavingsMap.pos_of_lt
#print axioms StokeyLucasPrescott.Overview.SavingsMap.exists_unique_fixedPoint
#print axioms StokeyLucasPrescott.Overview.SavingsMap.kstar
#print axioms StokeyLucasPrescott.Overview.SavingsMap.kstar_pos
#print axioms StokeyLucasPrescott.Overview.SavingsMap.g_kstar
#print axioms StokeyLucasPrescott.Overview.SavingsMap.eq_kstar
#print axioms StokeyLucasPrescott.Overview.SavingsMap.lt_of_lt_fixed
#print axioms StokeyLucasPrescott.Overview.SavingsMap.gt_of_gt_fixed
#print axioms StokeyLucasPrescott.Overview.SavingsMap.g_pos
#print axioms StokeyLucasPrescott.Overview.SavingsMap.iterate_mem_below
#print axioms StokeyLucasPrescott.Overview.SavingsMap.iterate_mem_above
#print axioms StokeyLucasPrescott.Overview.SavingsMap.monotone_of_le
#print axioms StokeyLucasPrescott.Overview.SavingsMap.antitone_of_ge
#print axioms StokeyLucasPrescott.Overview.SavingsMap.limit_eq_kstar
#print axioms StokeyLucasPrescott.Overview.SavingsMap.tendsto_fixedPoint
#print axioms StokeyLucasPrescott.Overview.SavingsMap.iterate_eq_fixed_iff
#print axioms StokeyLucasPrescott.Overview.Neoclassical.savings_above
#print axioms StokeyLucasPrescott.Overview.Neoclassical.savings_below
#print axioms StokeyLucasPrescott.Overview.Neoclassical.savings_crossings
#print axioms StokeyLucasPrescott.Overview.Neoclassical.savings_unique_steady_state
#print axioms StokeyLucasPrescott.Overview.ae_summable_norm_of_summable_integral_norm
#print axioms StokeyLucasPrescott.Overview.integrable_tsum_of_summable_integral_norm
#print axioms StokeyLucasPrescott.Overview.integral_abs_log_shock_le
#print axioms StokeyLucasPrescott.Overview.integral_abs_log_path_le
#print axioms StokeyLucasPrescott.Overview.ae_log_cons
#print axioms StokeyLucasPrescott.Overview.integral_abs_log_cons_le
#print axioms StokeyLucasPrescott.Overview.summable_integral_norm_utility
#print axioms StokeyLucasPrescott.Overview.ae_summable_utility
#print axioms StokeyLucasPrescott.Overview.integrable_utility
#print axioms StokeyLucasPrescott.Overview.hasSum_integral_utility
#print axioms StokeyLucasPrescott.Overview.integral_tsum_utility
#print axioms StokeyLucasPrescott.Overview.integral_utility_eq_stochValue
