/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Distributions on a finite grid and first-order stochastic dominance

States are the grid points `0, 1, …, n`, in increasing order. A distribution is `ψ : ℕ → ℝ`,
nonnegative with `∑_{i ≤ n} ψ(i) = 1` (values beyond `n` are never used), and a Markov kernel
`P : ℕ → ℕ → ℝ` has a distribution `P(i, ·)` in each row `i ≤ n`.

* `abel`: summation by parts, `∑_{i ≤ m} D_iG_i = ∑_{i < m} F_D(i)(G_i − G_{i+1}) + F_D(m)G_m`,
  the workhorse of the chapter.
* `Dominated ψ φ`: `ψ` is below `φ` in first-order stochastic dominance (`F_ψ ≥ F_φ`), and
  `sum_mul_antitone_le`: then `∑ φG ≤ ∑ ψG` for every decreasing `G` (and the reverse for
  increasing functions, `sum_mul_monotone_le`).
* `IsMonotone P`: the rows of `P` increase in FOSD; `push_mono`: such a kernel preserves FOSD.
* `abs_cdf_push_sub_le`: a monotone kernel shrinks the Kolmogorov distance
  `max_k |F_ψ(k) − F_φ(k)|` by the factor `F_{P(0,·)}(y) − F_{P(n,·)}(y)` at each `y`.
-/

open Finset

namespace DPExtensions.StationaryDistributions

/-- The cumulative distribution function `F_ψ(k) = ∑_{i ≤ k} ψ(i)`. -/
def cdf (ψ : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range (k + 1), ψ i

theorem cdf_zero (ψ : ℕ → ℝ) : cdf ψ 0 = ψ 0 := by simp [cdf]

theorem cdf_succ (ψ : ℕ → ℝ) (k : ℕ) : cdf ψ (k + 1) = cdf ψ k + ψ (k + 1) :=
  sum_range_succ _ _

theorem cdf_sub (ψ φ : ℕ → ℝ) (k : ℕ) : cdf (fun i => ψ i - φ i) k = cdf ψ k - cdf φ k :=
  sum_sub_distrib _ _

/-- **Summation by parts.** -/
theorem abel (D G : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), D i * G i =
      ∑ i ∈ range m, cdf D i * (G i - G (i + 1)) + cdf D m * G m := by
  induction m with
  | zero => simp [cdf]
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ, cdf_succ]
    ring

/-- `ψ` is a distribution on `{0, …, n}`. -/
def IsDist (n : ℕ) (ψ : ℕ → ℝ) : Prop := (∀ i, 0 ≤ ψ i) ∧ cdf ψ n = 1

/-- `P` is a Markov kernel on `{0, …, n}`. -/
def IsKernel (n : ℕ) (P : ℕ → ℕ → ℝ) : Prop := (∀ i j, 0 ≤ P i j) ∧ ∀ i ≤ n, cdf (P i) n = 1

/-- The distribution of the next state, `(ψP)(j) = ∑_{i ≤ n} ψ(i)P(i, j)`. -/
def push (n : ℕ) (ψ : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range (n + 1), ψ i * P i j

/-- The rows of `P` increase in first-order stochastic dominance. -/
def IsMonotone (n : ℕ) (P : ℕ → ℕ → ℝ) : Prop :=
  ∀ i i', i ≤ i' → i' ≤ n → ∀ y ≤ n, cdf (P i') y ≤ cdf (P i) y

/-- `ψ` is below `φ` in first-order stochastic dominance: `F_φ ≤ F_ψ` on the grid. -/
def Dominated (n : ℕ) (ψ φ : ℕ → ℝ) : Prop := ∀ k ≤ n, cdf φ k ≤ cdf ψ k

theorem cdf_nonneg {ψ : ℕ → ℝ} (h : ∀ i, 0 ≤ ψ i) (k : ℕ) : 0 ≤ cdf ψ k :=
  sum_nonneg fun i _ => h i

theorem cdf_mono {ψ : ℕ → ℝ} (h : ∀ i, 0 ≤ ψ i) {k k' : ℕ} (hk : k ≤ k') : cdf ψ k ≤ cdf ψ k' :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun i _ _ => h i

theorem cdf_le_one {n : ℕ} {ψ : ℕ → ℝ} (h : IsDist n ψ) {k : ℕ} (hk : k ≤ n) : cdf ψ k ≤ 1 :=
  h.2 ▸ cdf_mono h.1 hk

/-- `F_{ψP}(y) = ∑_{i ≤ n} ψ(i)F_{P(i, ·)}(y)`. -/
theorem cdf_push (n : ℕ) (ψ : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (y : ℕ) :
    cdf (push n ψ P) y = ∑ i ∈ range (n + 1), ψ i * cdf (P i) y := by
  simp only [cdf, push, mul_sum]
  rw [sum_comm]

theorem push_isDist {n : ℕ} {ψ : ℕ → ℝ} {P : ℕ → ℕ → ℝ} (hψ : IsDist n ψ) (hP : IsKernel n P) :
    IsDist n (push n ψ P) := by
  refine ⟨fun j => sum_nonneg fun i _ => mul_nonneg (hψ.1 i) (hP.1 i j), ?_⟩
  rw [cdf_push, ← hψ.2, cdf]
  exact sum_congr rfl fun i hi => by rw [hP.2 i (by simp at hi; omega), mul_one]

/-- **FOSD and decreasing functions**: if `ψ` is below `φ`, then `∑ φG ≤ ∑ ψG` for every `G`
decreasing on the grid. -/
theorem sum_mul_antitone_le {n : ℕ} {ψ φ : ℕ → ℝ} (hψ : IsDist n ψ) (hφ : IsDist n φ)
    (h : Dominated n ψ φ) {G : ℕ → ℝ} (hG : ∀ i < n, G (i + 1) ≤ G i) :
    ∑ i ∈ range (n + 1), φ i * G i ≤ ∑ i ∈ range (n + 1), ψ i * G i := by
  have e := abel (fun i => ψ i - φ i) G n
  rw [cdf_sub, hψ.2, hφ.2, sub_self, zero_mul, add_zero] at e
  have hnn : 0 ≤ ∑ i ∈ range n, cdf (fun i => ψ i - φ i) i * (G i - G (i + 1)) := by
    refine sum_nonneg fun i hi => mul_nonneg ?_ (sub_nonneg.2 (hG i (mem_range.1 hi)))
    rw [cdf_sub]
    exact sub_nonneg.2 (h i (by simp at hi; omega))
  have e2 : ∑ i ∈ range (n + 1), (ψ i - φ i) * G i =
      ∑ i ∈ range (n + 1), ψ i * G i - ∑ i ∈ range (n + 1), φ i * G i := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  linarith

/-- **FOSD and increasing functions**: if `ψ` is below `φ`, then `∑ ψf ≤ ∑ φf` for every `f`
increasing on the grid — for instance mean wealth. -/
theorem sum_mul_monotone_le {n : ℕ} {ψ φ : ℕ → ℝ} (hψ : IsDist n ψ) (hφ : IsDist n φ)
    (h : Dominated n ψ φ) {f : ℕ → ℝ} (hf : ∀ i < n, f i ≤ f (i + 1)) :
    ∑ i ∈ range (n + 1), ψ i * f i ≤ ∑ i ∈ range (n + 1), φ i * f i := by
  have := sum_mul_antitone_le hψ hφ h (G := fun i => -f i) fun i hi => neg_le_neg (hf i hi)
  simp only [mul_neg, sum_neg_distrib] at this
  linarith

/-- **A monotone kernel preserves first-order stochastic dominance.** -/
theorem push_mono {n : ℕ} {P : ℕ → ℕ → ℝ} (hP : IsMonotone n P) {ψ φ : ℕ → ℝ}
    (hψ : IsDist n ψ) (hφ : IsDist n φ) (h : Dominated n ψ φ) :
    Dominated n (push n ψ P) (push n φ P) := by
  intro y hy
  rw [cdf_push, cdf_push]
  exact sum_mul_antitone_le hψ hφ h fun i hi => hP i (i + 1) (Nat.le_succ i) (by omega) y hy

/-- A kernel whose rows are below another's pushes every distribution below. -/
theorem push_le_of_le {n : ℕ} {P Q : ℕ → ℕ → ℝ}
    (hPQ : ∀ i ≤ n, ∀ y ≤ n, cdf (Q i) y ≤ cdf (P i) y) {ψ : ℕ → ℝ} (hψ : ∀ i, 0 ≤ ψ i) :
    Dominated n (push n ψ P) (push n ψ Q) := by
  intro y hy
  rw [cdf_push, cdf_push]
  exact sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (hPQ i (by simp at hi; omega) y hy) (hψ i)

/-- **The Kolmogorov distance under a monotone kernel**: if `|F_ψ(k) − F_φ(k)| ≤ δ` on the
grid, then `|F_{ψP}(y) − F_{φP}(y)| ≤ δ(F_{P(0,·)}(y) − F_{P(n,·)}(y))`. -/
theorem abs_cdf_push_sub_le {n : ℕ} {P : ℕ → ℕ → ℝ} (hP : IsMonotone n P) {ψ φ : ℕ → ℝ}
    (hψ : IsDist n ψ) (hφ : IsDist n φ) {δ : ℝ} (hδ : ∀ k ≤ n, |cdf ψ k - cdf φ k| ≤ δ)
    {y : ℕ} (hy : y ≤ n) :
    |cdf (push n ψ P) y - cdf (push n φ P) y| ≤ δ * (cdf (P 0) y - cdf (P n) y) := by
  set G : ℕ → ℝ := fun i => cdf (P i) y
  have e := abel (fun i => ψ i - φ i) G n
  rw [cdf_sub, hψ.2, hφ.2, sub_self, zero_mul, add_zero] at e
  have e2 : cdf (push n ψ P) y - cdf (push n φ P) y =
      ∑ i ∈ range (n + 1), (ψ i - φ i) * G i := by
    rw [cdf_push, cdf_push, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e2, e]
  have hG : ∀ i ∈ range n, 0 ≤ G i - G (i + 1) := fun i hi =>
    sub_nonneg.2 (hP i (i + 1) (Nat.le_succ i) (by simp at hi; omega) y hy)
  calc |∑ i ∈ range n, cdf (fun i => ψ i - φ i) i * (G i - G (i + 1))|
      ≤ ∑ i ∈ range n, |cdf (fun i => ψ i - φ i) i * (G i - G (i + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, δ * (G i - G (i + 1)) := by
        refine sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (hG i hi), cdf_sub]
        exact mul_le_mul_of_nonneg_right (hδ i (by simp at hi; omega)) (hG i hi)
    _ = δ * (G 0 - G n) := by rw [← mul_sum, sum_range_sub']

end DPExtensions.StationaryDistributions
