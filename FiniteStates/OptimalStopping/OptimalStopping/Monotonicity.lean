/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.ContinuationValue
import Mathlib.Data.Finset.Max
import Mathlib.Order.Monotone.Basic

/-!
# Monotone values and monotone actions

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §4.1.3 (pp. 114–116).

Lemma 4.1.4: if `e` and `c` are increasing and `P` is monotone increasing then
`h*` and `v*` are increasing. The proof is the book's: `T` maps the closed set
of increasing functions into itself, so the fixed point lies in it
(Vol. 1, Ex 1.2.18).

Exercises 4.1.9–4.1.11: the optimal policy `σ* = 1{e ≥ h*}` is decreasing when
`e` is decreasing and `h*` increasing, which holds when `e` is constant, `c`
increasing and `P` monotone increasing; and increasing when `e` is increasing
and `h*` decreasing, as in IID job search (Example 4.1.5), where `h*` is
constant. On a totally ordered state space a monotone binary policy is a
threshold policy (p. 116).
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.OptimalStopping

namespace StoppingProblem

variable {X : Type*} [Fintype X] [DecidableEq X] (S : StoppingProblem X)

/-! ### Monotone values (§4.1.3.1) -/

variable [PartialOrder X]

omit [DecidableEq X] in
/-- `T` maps increasing functions to increasing functions when `e`, `c` are increasing and `P` is
monotone increasing (the step in the proof of Lemma 4.1.4). -/
theorem monotone_T_of_monotone (he : Monotone S.e) (hc : Monotone S.c)
    (hP : MonotoneIncreasing S.P) {v : X → ℝ} (hv : Monotone v) : Monotone (S.T v) := by
  intro x y hxy
  have h := (monotoneIncreasing_iff S.P).1 hP v hv hxy
  exact max_le_max (he hxy) (add_le_add (hc hxy) (mul_le_mul_of_nonneg_left h S.β_pos.le))

/-- **Lemma 4.1.4** (p. 114): if `e, c ∈ iℝ^X` and `P` is monotone increasing, then `v*` is
increasing. -/
theorem monotone_vstar (he : Monotone S.e) (hc : Monotone S.c) (hP : MonotoneIncreasing S.P) :
    Monotone S.vstar := by
  have hiter : ∀ k : ℕ, Monotone (S.T^[k] 0) := by
    intro k
    induction k with
    | zero => exact fun _ _ _ => le_rfl
    | succ k ih => rw [iterate_succ_apply']; exact S.monotone_T_of_monotone he hc hP ih
  exact (isClosed_monotone X).mem_of_tendsto (S.tendsto_iterate_T 0) (Eventually.of_forall hiter)

/-- Lemma 4.1.4 (p. 114): under the same hypotheses `h* = c + βPv*` is increasing. -/
theorem monotone_hstar (he : Monotone S.e) (hc : Monotone S.c) (hP : MonotoneIncreasing S.P) :
    Monotone S.hstar := by
  intro x y hxy
  have h := (monotoneIncreasing_iff S.P).1 hP S.vstar (S.monotone_vstar he hc hP) hxy
  exact add_le_add (hc hxy) (mul_le_mul_of_nonneg_left h S.β_pos.le)

/-! ### Monotone actions (§4.1.3.2) -/

/-- Exercise 4.1.9 (p. 115): `σ*` is decreasing whenever `e` is decreasing and `h*` is
increasing. Policies are ordered pointwise with `false < true`. -/
theorem antitone_sigmaStar (he : Antitone S.e) (hh : Monotone S.hstar) : Antitone S.sigmaStar := by
  intro x y hxy
  simp only [sigmaStar]
  by_cases hy : S.hstar y ≤ S.e y
  · have hx : S.hstar x ≤ S.e x := (hh hxy).trans (hy.trans (he hxy))
    simp [hx, hy]
  · simp [hy]

/-- Exercise 4.1.10 (p. 115): the conditions of Exercise 4.1.9 hold when `e` is constant, `c` is
increasing and `P` is monotone increasing; so `σ*` is decreasing. -/
theorem antitone_sigmaStar_of_const (he : ∀ x y, S.e x = S.e y) (hc : Monotone S.c)
    (hP : MonotoneIncreasing S.P) : Antitone S.sigmaStar :=
  S.antitone_sigmaStar (fun x y _ => (he y x).le)
    (S.monotone_hstar (fun x y _ => (he x y).le) hc hP)

/-- Exercise 4.1.11 (p. 115): `σ*` is increasing whenever `e` is increasing and `h*` is
decreasing. -/
theorem monotone_sigmaStar (he : Monotone S.e) (hh : Antitone S.hstar) : Monotone S.sigmaStar := by
  intro x y hxy
  simp only [sigmaStar]
  by_cases hx : S.hstar x ≤ S.e x
  · have hy : S.hstar y ≤ S.e y := (hh hxy).trans (hx.trans (he hxy))
    simp [hx, hy]
  · simp [hx]

omit [PartialOrder X] in
/-- When every row of `P` is the same distribution (IID transitions) and `c` is constant, the
continuation value `h*` is constant. -/
theorem hstar_const_of_iid (hP : ∀ x y, S.P x = S.P y) (hc : ∀ x y, S.c x = S.c y) (x y : X) :
    S.hstar x = S.hstar y := by
  simp only [hstar_apply]
  rw [hc x y, hP x y]

/-- Example 4.1.5 (p. 116): in IID job search, `e(w) = w/(1 − β)` is increasing and `h*` is
constant, so `σ*` is increasing: the agent accepts all sufficiently large offers. -/
theorem monotone_sigmaStar_of_iid (he : Monotone S.e) (hP : ∀ x y, S.P x = S.P y)
    (hc : ∀ x y, S.c x = S.c y) : Monotone S.sigmaStar :=
  S.monotone_sigmaStar he fun x y _ => (S.hstar_const_of_iid hP hc y x).le

end StoppingProblem

/-! ### Threshold policies (p. 116) -/

variable {Y : Type*} [Finite Y] [LinearOrder Y]

/-- On a totally ordered finite set, an increasing binary policy that stops somewhere is a
threshold policy: there is `x*` with `σ(x) = 1 ⟺ x ≥ x*` (p. 116). -/
theorem exists_threshold_of_monotone {σ : Policy Y} (hσ : Monotone σ) (hne : ∃ x, σ x = true) :
    ∃ xs : Y, ∀ x, σ x = true ↔ xs ≤ x := by
  classical
  cases nonempty_fintype Y
  have hne' : (univ.filter fun x => σ x = true).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [hx]⟩
  refine ⟨(univ.filter fun x => σ x = true).min' hne', fun x => ?_⟩
  constructor
  · intro hx
    exact Finset.min'_le _ _ (by simp [hx])
  · intro hx
    have hmin : σ ((univ.filter fun x => σ x = true).min' hne') = true := by
      have := Finset.min'_mem _ hne'
      simpa using this
    have := hσ hx
    rw [hmin] at this
    rcases Bool.eq_false_or_eq_true (σ x) with h | h
    · exact h
    · rw [h] at this
      exact absurd this (by decide)

/-- A decreasing binary policy that stops somewhere is a threshold policy from below:
`σ(x) = 1 ⟺ x ≤ x*`. -/
theorem exists_threshold_of_antitone {σ : Policy Y} (hσ : Antitone σ) (hne : ∃ x, σ x = true) :
    ∃ xs : Y, ∀ x, σ x = true ↔ x ≤ xs := by
  classical
  cases nonempty_fintype Y
  have hne' : (univ.filter fun x => σ x = true).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [hx]⟩
  refine ⟨(univ.filter fun x => σ x = true).max' hne', fun x => ?_⟩
  constructor
  · intro hx
    exact Finset.le_max' _ _ (by simp [hx])
  · intro hx
    have hmax : σ ((univ.filter fun x => σ x = true).max' hne') = true := by
      have := Finset.max'_mem _ hne'
      simpa using this
    have := hσ hx
    rw [hmax] at this
    rcases Bool.eq_false_or_eq_true (σ x) with h | h
    · exact h
    · rw [h] at this
      exact absurd this (by decide)

end SargentStachurski.OptimalStopping
