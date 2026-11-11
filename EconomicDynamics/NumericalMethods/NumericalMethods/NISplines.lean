/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Splines and linear splines (Miao, §11.3.2, pp. 360–361)

A function `φ` on `[a, b]` is a spline of order `k` if it is `C^{k−2}` on `[a, b]` and there are
nodes `a = x₀ < x₁ < ⋯ < xₙ = b` such that `φ` is a polynomial of degree at most `k − 1` on each
`[xᵢ, xᵢ₊₁]`.

* `ni_IsSpline k n x φ` (the definition, Miao, p. 361).
* `ni_spline_two_piecewise_linear`: a spline of order 2 is a continuous piecewise linear
  function.
* `ni_node_interval`: every point of `[x₀, xₙ]` lies in some `[xᵢ, xᵢ₊₁]`.
* `ni_linear_spline_exists`, `ni_linear_spline_unique`: for every data `y₀, …, yₙ` there is a
  linear spline (order 2) interpolating them, and any two agree on `[x₀, xₙ]`.

The book says "a polynomial of order at most `k − 1`"; the intended meaning (as the examples of
order 2 = linear and order 4 = cubic show) is degree at most `k − 1`, which is what is used.
-/

open Polynomial

namespace Miao.NumericalMethods

/-- **Spline of order `k`** (Miao, p. 361): nodes `x₀ < ⋯ < xₙ`, `φ` is `C^{k−2}` on `[x₀, xₙ]`
and a polynomial of degree at most `k − 1` on each `[xᵢ, xᵢ₊₁]`. -/
def ni_IsSpline (k n : ℕ) (x : ℕ → ℝ) (φ : ℝ → ℝ) : Prop :=
  StrictMono x ∧ ContDiffOn ℝ ((k - 2 : ℕ) : WithTop ℕ∞) φ (Set.Icc (x 0) (x n)) ∧
    ∀ i < n, ∃ p : ℝ[X], p.natDegree ≤ k - 1 ∧ ∀ t ∈ Set.Icc (x i) (x (i + 1)), φ t = p.eval t

/-- Miao, p. 361: a spline of order 2 (a linear spline) is a continuous piecewise linear
function. -/
theorem ni_spline_two_piecewise_linear {n : ℕ} {x : ℕ → ℝ} {φ : ℝ → ℝ}
    (h : ni_IsSpline 2 n x φ) :
    ContinuousOn φ (Set.Icc (x 0) (x n)) ∧
      ∀ i < n, ∃ a b : ℝ, ∀ t ∈ Set.Icc (x i) (x (i + 1)), φ t = a + b * t := by
  refine ⟨?_, fun i hi => ?_⟩
  · have := h.2.1
    simpa using this.continuousOn
  · obtain ⟨p, hp, hφ⟩ := h.2.2 i hi
    refine ⟨p.coeff 0, p.coeff 1, fun t ht => ?_⟩
    rw [hφ t ht, eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ]

/-- Every point of `[x₀, xₙ]` (`n ≥ 1`) lies in some subinterval `[xᵢ, xᵢ₊₁]`, `i < n`. -/
theorem ni_node_interval {x : ℕ → ℝ} :
    ∀ n, 0 < n → ∀ t ∈ Set.Icc (x 0) (x n), ∃ i < n, t ∈ Set.Icc (x i) (x (i + 1)) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ t ht
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by omega, ht⟩
    · by_cases htn : t ≤ x n
      · obtain ⟨i, hi, hti⟩ := ih hn t ⟨ht.1, htn⟩
        exact ⟨i, by omega, hti⟩
      · exact ⟨n, by omega, ⟨(not_le.mp htn).le, ht.2⟩⟩

/-- Two affine functions agreeing at two distinct points agree everywhere. -/
theorem ni_affine_eq {a₁ b₁ a₂ b₂ u v : ℝ} (huv : u ≠ v) (hu : a₁ + b₁ * u = a₂ + b₂ * u)
    (hv : a₁ + b₁ * v = a₂ + b₂ * v) (t : ℝ) : a₁ + b₁ * t = a₂ + b₂ * t := by
  have hb : b₁ = b₂ := by
    have : (b₁ - b₂) * (u - v) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd (sub_eq_zero.mp h) huv
  subst hb
  linarith

/-- Miao, p. 361 (linear spline, uniqueness): two linear splines with the same nodes
interpolating the same data agree on `[x₀, xₙ]`. -/
theorem ni_linear_spline_unique {n : ℕ} (hn : 0 < n) {x : ℕ → ℝ} {φ ψ : ℝ → ℝ}
    (hφ : ni_IsSpline 2 n x φ) (hψ : ni_IsSpline 2 n x ψ) (heq : ∀ i ≤ n, φ (x i) = ψ (x i))
    (t : ℝ) (ht : t ∈ Set.Icc (x 0) (x n)) : φ t = ψ t := by
  obtain ⟨i, hi, hti⟩ := ni_node_interval n hn t ht
  obtain ⟨a₁, b₁, h₁⟩ := (ni_spline_two_piecewise_linear hφ).2 i hi
  obtain ⟨a₂, b₂, h₂⟩ := (ni_spline_two_piecewise_linear hψ).2 i hi
  have hlt : x i < x (i + 1) := hφ.1 (Nat.lt_succ_self i)
  have hu := heq i hi.le
  have hv := heq (i + 1) hi
  rw [h₁ _ ⟨le_rfl, hlt.le⟩, h₂ _ ⟨le_rfl, hlt.le⟩] at hu
  rw [h₁ _ ⟨hlt.le, le_rfl⟩, h₂ _ ⟨hlt.le, le_rfl⟩] at hv
  rw [h₁ t hti, h₂ t hti]
  exact ni_affine_eq hlt.ne hu hv t

/-- The slopes `sᵢ = (yᵢ₊₁ − yᵢ)/(xᵢ₊₁ − xᵢ)`. -/
noncomputable def ni_slope (x y : ℕ → ℝ) (i : ℕ) : ℝ := (y (i + 1) - y i) / (x (i + 1) - x i)

/-- The interpolating linear spline in closed form,
`φ(t) = y₀ + ∑ᵢ sᵢ (max(xᵢ, min(t, xᵢ₊₁)) − xᵢ)`. -/
noncomputable def ni_linSpline (n : ℕ) (x y : ℕ → ℝ) (t : ℝ) : ℝ :=
  y 0 + ∑ i ∈ Finset.range n, ni_slope x y i * (max (x i) (min t (x (i + 1))) - x i)

/-- On `[xⱼ, xⱼ₊₁]` the closed form is `yⱼ + sⱼ (t − xⱼ)`. -/
theorem ni_linSpline_piece {n : ℕ} {x : ℕ → ℝ} (hx : StrictMono x) (y : ℕ → ℝ) {j : ℕ}
    (hj : j < n) {t : ℝ} (ht : t ∈ Set.Icc (x j) (x (j + 1))) :
    ni_linSpline n x y t = y j + ni_slope x y j * (t - x j) := by
  unfold ni_linSpline
  rw [← Finset.sum_range_add_sum_Ico _ hj.le, Finset.sum_eq_sum_Ico_succ_bot hj]
  have hlow : ∀ i ∈ Finset.range j,
      ni_slope x y i * (max (x i) (min t (x (i + 1))) - x i) = y (i + 1) - y i := by
    intro i hi
    have hi' : i + 1 ≤ j := Finset.mem_range.mp hi
    have h1 : x (i + 1) ≤ t := (hx.monotone hi').trans ht.1
    have h2 : x i < x (i + 1) := hx (Nat.lt_succ_self i)
    rw [min_eq_right h1, max_eq_right h2.le, ni_slope]
    field_simp [(sub_pos.mpr h2).ne']
  have hhigh : ∀ i ∈ Finset.Ico (j + 1) n,
      ni_slope x y i * (max (x i) (min t (x (i + 1))) - x i) = 0 := by
    intro i hi
    have hi' : j + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have h1 : t ≤ x i := ht.2.trans (hx.monotone hi')
    have h2 : min t (x (i + 1)) ≤ x i := (min_le_left _ _).trans h1
    rw [max_eq_left h2, sub_self, mul_zero]
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, Finset.sum_const_zero,
    Finset.sum_range_sub (fun i => y i), min_eq_left ht.2, max_eq_right ht.1]
  ring

/-- Miao, p. 361 (linear spline, existence): for strictly increasing nodes and any data there is
a linear spline (order 2) interpolating the data. -/
theorem ni_linear_spline_exists {n : ℕ} (hn : 0 < n) {x : ℕ → ℝ} (hx : StrictMono x)
    (y : ℕ → ℝ) : ni_IsSpline 2 n x (ni_linSpline n x y) ∧
      ∀ i ≤ n, ni_linSpline n x y (x i) = y i := by
  refine ⟨⟨hx, ?_, fun j hj => ?_⟩, fun i hi => ?_⟩
  · have hc : Continuous (ni_linSpline n x y) := by
      unfold ni_linSpline
      fun_prop
    simpa using hc.continuousOn
  · refine ⟨C (ni_slope x y j) * X + C (y j - ni_slope x y j * x j), natDegree_linear_le,
      fun t ht => ?_⟩
    · rw [ni_linSpline_piece hx y hj ht]
      simp
      ring
  · rcases lt_or_eq_of_le hi with hi | rfl
    · rw [ni_linSpline_piece hx y hi ⟨le_rfl, (hx (Nat.lt_succ_self i)).le⟩]
      ring
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [ni_linSpline_piece hx y (Nat.lt_succ_self m) ⟨(hx (Nat.lt_succ_self m)).le, le_rfl⟩,
        ni_slope]
      field_simp [(sub_pos.mpr (hx (Nat.lt_succ_self m))).ne']
      ring

end Miao.NumericalMethods
