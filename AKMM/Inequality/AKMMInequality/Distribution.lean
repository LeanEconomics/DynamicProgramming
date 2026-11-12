/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IncompleteMarkets.AYComputation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §21.1: Lorenz curves, Gini coefficients and Pareto tails

AKMM, §21.1, pp. 629–631, with footnote 1. The Lorenz curve and the Gini coefficient of a
sorted sample `y₀ ≤ … ≤ y_{n−1}` are Miao's (`Miao.IncompleteMarkets.ay_lorenz`, `ay_gini`,
Chapter 17), whose Gini is twice the area between the diagonal and the Lorenz curve.

* `gi_gini_eq_ratio`: the Gini coefficient is `A/(A + B)` (p. 630).
* `gi_lorenz_le_diag`, `gi_lorenz_convex`: the Lorenz curve lies below the 45-degree line and is
  convex; `gi_lorenz_concentrated`: under complete concentration it is flat at zero up to the last
  point.
* `gi_gini_mem_Icc`, `gi_gini_equal`, `gi_gini_eq_zero_iff`: the Gini lies in `[0, 1]`, is zero
  under perfect equality, and only then; `gi_gini_concentrated_tendsto`: it tends to one when one
  agent holds all income.
* `pa_ccdf`, `pa_log_ccdf`, `pa_log_ccdf_strictAnti`: for the Pareto distribution
  `F(x) = 1 − (x̲/x)^α` of footnote 1, `log(1 − F(x))` is linear in `log x` with slope `−α`.
-/

namespace AKMM.Inequality

open Filter Topology Miao.IncompleteMarkets

/-- **AKMM, p. 630: "The Gini coefficient is computed as the area `A` divided by the area
`A + B`".** With `B` the area under the piecewise-linear Lorenz curve and `A = 1/2 − B` the area
between it and the diagonal, `G = A/(A + B)`. -/
theorem gi_gini_eq_ratio (y : ℕ → ℝ) (n : ℕ) :
    ay_gini y n = (1 / 2 - ∑ i ∈ Finset.range n,
        (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) /
      ((1 / 2 - ∑ i ∈ Finset.range n,
        (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) +
        ∑ i ∈ Finset.range n, (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) := by
  rw [ay_gini_eq_area, sub_add_cancel]
  ring

/-- **AKMM, p. 630: "The Lorenz curve is always below the 45-degree line"** (Miao's
`ay_lorenz_le_diag`). -/
theorem gi_lorenz_le_diag {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) {i : ℕ} (hi : i ≤ n) : ay_lorenz y n i ≤ i / n :=
  ay_lorenz_le_diag hsort hT hi

/-- **AKMM, p. 630: the Lorenz curve is convex**: for sorted data its increments
`z_{i+1} − z_i = y_i/Σy` are nondecreasing. -/
theorem gi_lorenz_convex {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) {i : ℕ} (hi : i + 1 < n) :
    ay_lorenz y n (i + 1) - ay_lorenz y n i ≤ ay_lorenz y n (i + 2) - ay_lorenz y n (i + 1) := by
  simp only [ay_lorenz, Finset.sum_range_succ]
  rw [← sub_div, ← sub_div, div_le_div_iff_of_pos_right hT]
  have := hsort i (i + 1) (Nat.le_succ i) hi
  linarith

/-- **AKMM, p. 630: "The most extreme income inequality would be a Lorenz curve that is a flat
line … up until 100, where it jumps to 100".** If only the last of `m + 1` agents has income, the
Lorenz curve is `0` at `i ≤ m` and `1` at `m + 1`. -/
theorem gi_lorenz_concentrated {y : ℕ → ℝ} {m : ℕ} (hy : ∀ j, j < m → y j = 0) (hm : 0 < y m) :
    (∀ i, i ≤ m → ay_lorenz y (m + 1) i = 0) ∧ ay_lorenz y (m + 1) (m + 1) = 1 := by
  have hpre : ∀ i, i ≤ m → ∑ j ∈ Finset.range i, y j = 0 := fun i hi =>
    Finset.sum_eq_zero fun j hj => hy j ((Finset.mem_range.1 hj).trans_le hi)
  have hT : 0 < ∑ j ∈ Finset.range (m + 1), y j := by
    rw [Finset.sum_range_succ, hpre m le_rfl, zero_add]; exact hm
  refine ⟨fun i hi => ?_, ay_lorenz_n hT⟩
  rw [ay_lorenz, hpre i hi, zero_div]

/-- **AKMM, p. 630: the Gini coefficient lies in `[0, 1]`** (Miao's `ay_gini_nonneg`,
`ay_gini_le`) for sorted nonnegative data with positive total. -/
theorem gi_gini_mem_Icc {y : ℕ → ℝ} {n : ℕ} (hy : ∀ j, 0 ≤ y j)
    (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k) (hT : 0 < ∑ j ∈ Finset.range n, y j) :
    ay_gini y n ∈ Set.Icc 0 1 :=
  ⟨ay_gini_nonneg hsort hT, (ay_gini_le hy hT).2⟩

/-- **AKMM, p. 630: "When there is perfect equality, the Gini coefficient is therefore 0"**
(Miao's `ay_gini_equal`). -/
theorem gi_gini_equal {y : ℕ → ℝ} {n : ℕ} {c : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hy : ∀ j, j < n → y j = c) : ay_gini y n = 0 :=
  ay_gini_equal hc hn hy

/-- AKMM, p. 630, the converse: a zero Gini coefficient means perfect equality. For sorted data
with positive total, `G = 0` iff `y_j = (Σy)/n` for every `j < n`. -/
theorem gi_gini_eq_zero_iff {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) :
    ay_gini y n = 0 ↔ ∀ j, j < n → y j = (∑ k ∈ Finset.range n, y k) / n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set T := ∑ k ∈ Finset.range n, y k with hTd
  constructor
  · intro h0
    have hS : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) =
        ∑ i ∈ Finset.range n, (((2 * i + 1 : ℕ) : ℝ) / n) := by
      have h1 : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) = n := by
        rw [ay_gini] at h0
        field_simp at h0
        linarith
      rw [h1]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ay_sum_odd]
      field_simp
    have hle : ∀ i ∈ Finset.range n, ay_lorenz y n i + ay_lorenz y n (i + 1) ≤
        ((2 * i + 1 : ℕ) : ℝ) / n := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have h1 := ay_lorenz_le_diag hsort hT hi'.le
      have h2 := ay_lorenz_le_diag hsort hT (Nat.succ_le_of_lt hi')
      have e : (((2 * i + 1 : ℕ) : ℝ)) / n = i / n + ((i : ℝ) + 1) / n := by
        push_cast; ring
      rw [e]
      push_cast at h2
      linarith
    have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hS
    have hz : ∀ i, i ≤ n → ay_lorenz y n i = i / n := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp [ay_lorenz]
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k < n := by omega
        have h1 := ay_lorenz_le_diag hsort hT hk.le
        have h2 := ay_lorenz_le_diag hsort hT hi
        have h3 := heq k (Finset.mem_range.2 hk)
        have e : (((2 * k + 1 : ℕ) : ℝ)) / n = k / n + ((k : ℝ) + 1) / n := by
          push_cast; ring
        rw [e] at h3
        push_cast at h2 ⊢
        linarith
    intro j hj
    have h1 := hz (j + 1) hj
    have h2 := hz j hj.le
    simp only [ay_lorenz, Finset.sum_range_succ] at h1 h2
    have e : y j =
        T * ((∑ k ∈ Finset.range j, y k + y j) / T - (∑ k ∈ Finset.range j, y k) / T) := by
      field_simp
      ring
    rw [e, h1, h2]
    push_cast
    field_simp
    ring
  · intro h
    have hc : 0 < T / n := div_pos hT hnpos
    exact ay_gini_equal hc hn h

/-- **AKMM, p. 630: "the Gini coefficient tends to 1 in the extreme case where one agent holds all
income".** With `m + 1` agents of whom one holds everything, `G = 1 − 1/(m + 1)` (Miao's
`ay_gini_concentrated`), which tends to `1`. -/
theorem gi_gini_concentrated_tendsto {y : ℕ → ℕ → ℝ} (hy : ∀ m j, j < m → y m j = 0)
    (hm : ∀ m, 0 < y m m) :
    Tendsto (fun m => ay_gini (y m) (m + 1)) atTop (𝓝 1) := by
  have h : ∀ m, ay_gini (y m) (m + 1) = 1 - 1 / ((m + 1 : ℕ) : ℝ) := fun m =>
    ay_gini_concentrated (hm m) (hy m) rfl
  simp_rw [h]
  exact ay_gini_concentrated_tendsto

/-- AKMM, fn 1, p. 631: the Pareto complementary distribution `1 − F(x) = (x̲/x)^α`. -/
noncomputable def pa_ccdf (α xm x : ℝ) : ℝ := (xm / x) ^ α

/-- **AKMM, p. 631 and fn 1: "a linear relation between the logarithm of `x` and the logarithm
of one minus the cumulative distribution at `x`".** For `x ≥ x̲ > 0`,
`log(1 − F(x)) = α log x̲ − α log x`, with slope `−α` in `log x`. -/
theorem pa_log_ccdf {α xm x : ℝ} (hxm : 0 < xm) (hx : 0 < x) :
    Real.log (pa_ccdf α xm x) = α * Real.log xm - α * Real.log x := by
  unfold pa_ccdf
  rw [Real.log_rpow (div_pos hxm hx), Real.log_div hxm.ne' hx.ne']
  ring

/-- **AKMM, fn 1: "the slope … is negative".** For `α > 0`, `log(1 − F)` is strictly decreasing
in `x > 0`. -/
theorem pa_log_ccdf_strictAnti {α xm : ℝ} (hα : 0 < α) (hxm : 0 < xm) :
    StrictAntiOn (fun x => Real.log (pa_ccdf α xm x)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  simp only
  rw [pa_log_ccdf hxm hx', pa_log_ccdf hxm hy']
  have := Real.log_lt_log hx' hxy
  nlinarith

end AKMM.Inequality
