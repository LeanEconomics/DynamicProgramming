/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Discounted values of deterministic sequences

Miao, *Economic Dynamics in Discrete Time*, Chapter 22, §22.1 and Exercise 22.1, pp. 775–798. In
the deterministic version of the limited-commitment model (Exercise 22.1, after Zhang 2012)
endowments and consumption are sequences, and the agent's continuation value at `t` is
`V_t(x) = Σ_{j ≥ 0} β^j x_{t+j}` (`lc_detValue`). This module collects the facts about these
discounted sums used in `LCLagrangian` and `LCZhang`: convergence for bounded sequences, bounds,
linearity, monotonicity, the split `V_t = Σ_{j<τ} β^j x_{t+j} + β^τ V_{t+τ}`, and the value of
a constant sequence.
-/

namespace Miao.RecursiveContracts

open Filter Topology

/-- The continuation value `V_t(x) = Σ_j β^j x_{t+j}` (Miao, p. 797). -/
noncomputable def lc_detValue (β : ℝ) (x : ℕ → ℝ) (t : ℕ) : ℝ := ∑' j : ℕ, β ^ j * x (t + j)

/-- Discounted bounded sequences are summable. -/
theorem lc_summable_geom {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) : Summable fun j : ℕ => β ^ j * x j := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) ?_
  intro t
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hx t) (pow_nonneg hβ0 t)

/-- The bound `|V_t(x)| ≤ M/(1 − β)`. -/
theorem lc_detValue_abs_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) : |lc_detValue β x t| ≤ M / (1 - β) := by
  have hs := lc_summable_geom hβ0 hβ1 (x := fun j => x (t + j)) (fun j => hx (t + j))
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hgeo : ∑' j : ℕ, M * β ^ j = M / (1 - β) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]
  rw [abs_le]
  constructor
  · have := Summable.tsum_le_tsum (f := fun j : ℕ => -(M * β ^ j))
      (g := fun j => β ^ j * x (t + j)) (fun j => by
        have := (abs_le.mp (hx (t + j))).1
        nlinarith [pow_nonneg hβ0 j]) (hg.mul_left M).neg hs
    rw [tsum_neg, hgeo] at this
    exact this
  · have := Summable.tsum_le_tsum (g := fun j : ℕ => M * β ^ j)
      (f := fun j => β ^ j * x (t + j)) (fun j => by
        have := (abs_le.mp (hx (t + j))).2
        nlinarith [pow_nonneg hβ0 j]) hs (hg.mul_left M)
    rw [hgeo] at this
    exact this

/-- The split `V_t = Σ_{j<τ} β^j x_{t+j} + β^τ V_{t+τ}`. -/
theorem lc_detValue_split {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t τ : ℕ) :
    lc_detValue β x t = ∑ j ∈ Finset.range τ, β ^ j * x (t + j) +
      β ^ τ * lc_detValue β x (t + τ) := by
  have hs := lc_summable_geom hβ0 hβ1 (x := fun j => x (t + j)) (fun j => hx (t + j))
  unfold lc_detValue
  rw [← hs.sum_add_tsum_nat_add τ, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun i => ?_
  rw [pow_add, show t + (i + τ) = t + τ + i by ring]
  ring

/-- The recursion `V_t = x_t + β V_{t+1}`. -/
theorem lc_detValue_succ {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (t : ℕ) :
    lc_detValue β x t = x t + β * lc_detValue β x (t + 1) := by
  rw [lc_detValue_split hβ0 hβ1 hx t 1]
  simp

/-- `V_0(x) = Σ_{s<T} β^s x_s + β^T V_T(x)`. -/
theorem lc_detValue_split0 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ t, |x t| ≤ M) (T : ℕ) :
    lc_detValue β x 0 = ∑ s ∈ Finset.range T, β ^ s * x s + β ^ T * lc_detValue β x T := by
  rw [lc_detValue_split hβ0 hβ1 hx 0 T]
  simp

/-- Linearity: `V_t(a − b) = V_t(a) − V_t(b)`. -/
theorem lc_detValue_sub {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a b : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) (hb : ∀ t, |b t| ≤ M) (t : ℕ) :
    lc_detValue β (fun s => a s - b s) t = lc_detValue β a t - lc_detValue β b t := by
  unfold lc_detValue
  rw [← (lc_summable_geom hβ0 hβ1 (x := fun j => a (t + j)) (fun _ => ha _)).tsum_sub
    (lc_summable_geom hβ0 hβ1 (x := fun j => b (t + j)) (fun _ => hb _))]
  exact tsum_congr fun j => by ring

/-- Monotonicity: `a ≤ b` pointwise gives `V_t(a) ≤ V_t(b)`. -/
theorem lc_detValue_mono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a b : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) (hb : ∀ t, |b t| ≤ M) (hab : ∀ t, a t ≤ b t) (t : ℕ) :
    lc_detValue β a t ≤ lc_detValue β b t :=
  Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hab _) (pow_nonneg hβ0 j))
    (lc_summable_geom hβ0 hβ1 (x := fun j => a (t + j)) (fun _ => ha _))
    (lc_summable_geom hβ0 hβ1 (x := fun j => b (t + j)) (fun _ => hb _))

/-- The value of a constant sequence: `V_t(k) = k/(1 − β)`. -/
theorem lc_detValue_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (k : ℝ) (t : ℕ) :
    lc_detValue β (fun _ => k) t = k / (1 - β) := by
  unfold lc_detValue
  rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
  ring

end Miao.RecursiveContracts
