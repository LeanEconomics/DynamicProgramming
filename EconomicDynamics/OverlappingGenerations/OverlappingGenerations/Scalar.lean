/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OverlappingGenerations.Basics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Scalar first-order linear equations

Copied from `EconomicDynamics/DifferenceEquations` (module `Scalar`), namespace renamed.

Miao, §1.1, pp. 5–10: `x_{t+1} = b x_t + c z_t` (1.1).

* Shared vocabulary: `IsScalarSol b c z x` (the sequence `x` solves (1.1)) and `BddSeq x`
  (`|x_t| ≤ M` for all `t`; equivalent to `IsStableSeq`, `bddSeq_iff_isStableSeq`).
* The autonomous case (1.2)–(1.3): the steady state `c/(1−b)` (`eq_1_2_steady_state`), the
  general solution (`eq_1_3`), global stability for `|b| < 1` (`eq_1_3_globallyStable`),
  divergence for `|b| > 1` (`eq_1_3_diverges`) and the constant as the only bounded solution
  (`eq_1_3_bdd_iff`).
* The backward solution (1.4) (`eq_1_4`).
* **Correction to (1.5).** The book says the limit `lim c Σ_{j<t} bʲ z_{t−1−j}` exists for every
  bounded `{z_t}` when `|b| < 1`. This is false: for `z_t = (−1)ᵗ` and `c ≠ 0` no solution
  converges, whatever `b` (`eq_1_5_counterexample`). What is true: if `z_t → z̄` then
  `x_t → c z̄/(1−b)` (`eq_1_5_tendsto`); bounded `z` gives bounded `x` (`eq_1_5_bdd`); and any
  two solutions approach each other (`eq_1_5_sub_tendsto`), so the long-run path does not depend
  on `x₀`.
* `|b| = 1`. For `b = 1`, `c ≠ 0` the solution converges iff `Σ z_j` converges
  (`eq_1_5_b_one_tendsto_iff`), and the limit moves one-for-one with `x₀`
  (`eq_1_5_b_one_limit_sub`). For `b = −1` the book's claim fails: `z_t = 1` has a convergent
  (constant) solution though `Σ z_j = ∞` (`eq_1_5_b_neg_one_counterexample`), and at most one
  initial value gives a convergent solution (`eq_1_5_b_neg_one_unique`).
* **Correction (|b| > 1).** The book says (1.4) shows that `{x_t}` diverges. Not every solution
  diverges: the forward solution (1.8) is bounded; every other solution has `|x_t| → ∞`
  (`eq_1_8_others_diverge`).
* The forward identity (1.6) (`eq_1_6`), the transversality condition (1.7), the forward
  solution (1.8) (`fwdSol`, `eq_1_8_isScalarSol`, `eq_1_8_bdd`, `eq_1_8_transversality`,
  `eq_1_8_unique_of_transversality`, `eq_1_8_unique_bdd`), bubbles (1.9) (`eq_1_9`,
  `eq_1_9_every_solution`, `eq_1_9_bubble_stable`) and the divergence of the forward sum for
  `|b| < 1` (`eq_1_8_not_summable`).
* Example 1.1.1: the adaptive-expectations recursion (`example_1_1_1_recursion`), the backward
  solution (`example_1_1_1_backward`, the printed formula is right), convergence iff
  `p₀ = p̄ ∨ |a| < 1` (`example_1_1_1_tendsto_iff`); for `R > λ` one has `|a| < 1 ⟺ R > 1`
  (`example_1_1_1_abs_a_lt_one_iff`), so the assumption `|a| < 1` is automatic for a gross
  return `R > 1`. Perfect foresight: the forward identity (`example_1_1_1_forward`), the limit
  form (`example_1_1_1_forward_limit`) and the unique bounded solution `d/(R−1)`
  (`example_1_1_1_unique_bdd`).
* Example 1.1.2 (dividend taxes, `taxPath`): every bounded solution has the printed `p_T` and
  `p₀` (`example_1_1_2_pT`, `example_1_1_2_p0`), `taxPath` is the unique bounded solution
  (`example_1_1_2_solves`, `example_1_1_2_unique`), the price drops at time 0
  (`example_1_1_2_drop`), falls strictly until `T` (`example_1_1_2_decreasing`) and is constant
  from `T` on (`example_1_1_2_const`).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- The sequence `x` solves `x_{t+1} = b x_t + c z_t` (Miao, (1.1), p. 5). -/
def IsScalarSol (b c : ℝ) (z x : ℕ → ℝ) : Prop :=
  ∀ t, x (t + 1) = b * x t + c * z t

/-- A real sequence is bounded: `|x_t| ≤ M` for all `t`. -/
def BddSeq (x : ℕ → ℝ) : Prop :=
  ∃ M, ∀ t, |x t| ≤ M

/-- `BddSeq` is the book's stability (Definition 1.4.2, p. 17) for real sequences. -/
theorem bddSeq_iff_isStableSeq (x : ℕ → ℝ) : BddSeq x ↔ IsStableSeq x := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨|M| + 1, by positivity, fun t => ?_⟩
    rw [Real.norm_eq_abs]
    linarith [hM t, le_abs_self M]
  · rintro ⟨M, -, hM⟩
    refine ⟨M, fun t => ?_⟩
    have := hM t
    rw [Real.norm_eq_abs] at this
    exact this.le

/-- A convergent real sequence is bounded. -/
theorem bddSeq_of_tendsto {x : ℕ → ℝ} {L : ℝ} (h : Tendsto x atTop (𝓝 L)) : BddSeq x := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto x h).subset_closedBall 0
  refine ⟨C, fun t => ?_⟩
  have := hC ⟨t, rfl⟩
  rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this

/-- The bound of a bounded sequence is nonnegative. -/
theorem BddSeq.exists_nonneg {x : ℕ → ℝ} (h : BddSeq x) : ∃ M, 0 ≤ M ∧ ∀ t, |x t| ≤ M := by
  obtain ⟨M, hM⟩ := h
  exact ⟨M, (abs_nonneg _).trans (hM 0), hM⟩

/-- A geometric sequence: `x_{t+1} = b x_t` gives `x_t = bᵗ x₀`. -/
theorem geom_eq {b : ℝ} {x : ℕ → ℝ} (h : ∀ t, x (t + 1) = b * x t) (t : ℕ) :
    x t = b ^ t * x 0 := by
  induction t with
  | zero => simp
  | succ n ih => rw [h, ih, pow_succ]; ring

/-- `|bᵗ k| → ∞` when `|b| > 1` and `k ≠ 0`. -/
theorem abs_pow_mul_tendsto_atTop {b k : ℝ} (hb : 1 < |b|) (hk : k ≠ 0) :
    Tendsto (fun t : ℕ => |b ^ t * k|) atTop atTop := by
  simp only [abs_mul, abs_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt hb).atTop_mul_const (abs_pos.2 hk)

/-- `bᵗ k → 0` with `k ≠ 0` iff `|b| < 1`. -/
theorem pow_mul_tendsto_zero_iff {b k : ℝ} (hk : k ≠ 0) :
    Tendsto (fun t : ℕ => b ^ t * k) atTop (𝓝 0) ↔ |b| < 1 := by
  constructor
  · intro h
    by_contra hb
    push Not at hb
    have hk' : 0 < |k| := abs_pos.2 hk
    have h1 : ∀ t : ℕ, |k| ≤ |b ^ t * k| := fun t => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hb)
    have h3 : Tendsto (fun t : ℕ => |b ^ t * k|) atTop (𝓝 0) := by simpa using h.abs
    obtain ⟨t, ht⟩ := ((tendsto_order.1 h3).2 |k| hk').exists
    linarith [h1 t]
  · intro hb
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hb).mul_const k

/-- A geometric sequence with `|b| > 1` is bounded iff it is zero. -/
theorem geom_bdd_iff {b : ℝ} (hb : 1 < |b|) {x : ℕ → ℝ} (h : ∀ t, x (t + 1) = b * x t) :
    BddSeq x ↔ x 0 = 0 := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra h0
    obtain ⟨t, ht⟩ := ((abs_pow_mul_tendsto_atTop hb h0).eventually_gt_atTop M).exists
    have := hM t
    rw [geom_eq h t] at this
    linarith
  · intro h0
    exact ⟨0, fun t => by rw [geom_eq h t, h0]; simp⟩

/-- A bounded sequence discounted geometrically at `|r| < 1` goes to zero. -/
theorem pow_mul_tendsto_zero_of_bdd {r : ℝ} (hr : |r| < 1) {x : ℕ → ℝ} (hx : BddSeq x)
    (t : ℕ) : Tendsto (fun T : ℕ => r ^ T * x (t + T)) atTop (𝓝 0) := by
  obtain ⟨M, -, hM⟩ := hx.exists_nonneg
  refine squeeze_zero_norm (a := fun T => |r| ^ T * M) (fun T => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg r) hr).mul_const M

/-- A forced recursion `y_{t+1} = b y_t + w_t` with `|b| < 1` and bounded `w` is bounded. -/
theorem bddSeq_of_forced {b : ℝ} (hb : |b| < 1) {y w : ℕ → ℝ}
    (h : ∀ t, y (t + 1) = b * y t + w t) (hw : BddSeq w) : BddSeq y := by
  obtain ⟨M, hM0, hM⟩ := hw.exists_nonneg
  have h1 : 0 < 1 - |b| := by linarith
  set K := max |y 0| (M / (1 - |b|)) with hK
  have hKM : M ≤ (1 - |b|) * K := by
    have : M / (1 - |b|) ≤ K := le_max_right _ _
    rw [div_le_iff₀ h1] at this
    linarith
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact le_max_left _ _
  | succ n ih =>
    rw [h]
    calc |b * y n + w n| ≤ |b| * |y n| + |w n| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |b| * K + M := add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg b)) (hM n)
      _ ≤ K := by linarith

/-- A forced recursion `y_{t+1} = b y_t + e_t` with `|b| < 1` and `e_t → 0` has `y_t → 0`. -/
theorem tendsto_zero_of_forced {b : ℝ} (hb : |b| < 1) {y e : ℕ → ℝ}
    (h : ∀ t, y (t + 1) = b * y t + e t) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto y atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : 0 < 1 - |b| := by linarith
  have hη : 0 < ε / 2 * (1 - |b|) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 he _ hη
  have key : ∀ k, |y (N + k)| ≤ |b| ^ k * |y N| + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have hek : |e (N + k)| < ε / 2 * (1 - |b|) := by
        simpa [Real.dist_eq] using hN (N + k) (by omega)
      rw [← add_assoc, h]
      calc |b * y (N + k) + e (N + k)| ≤ |b| * |y (N + k)| + |e (N + k)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |b| * (|b| ^ k * |y N| + ε / 2) + ε / 2 * (1 - |b|) :=
            add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg b)) hek.le
        _ = |b| ^ (k + 1) * |y N| + ε / 2 := by ring
  have hg : Tendsto (fun k : ℕ => |b| ^ k * |y N|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg b) hb).mul_const |y N|
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hg (ε / 2) (by positivity)
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  have hk := hK k (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hk
  rw [Real.dist_eq, sub_zero]
  linarith [key k]

/-! ### The autonomous equation (1.2) -/

/-- Miao, (1.2), p. 6: for `b ≠ 1` the constant `x̄` solves `x_{t+1} = b x_t + c` iff
`x̄ = c/(1 − b)`. -/
theorem eq_1_2_steady_state {b c : ℝ} (hb : b ≠ 1) (xbar : ℝ) :
    IsScalarSol b c (fun _ => 1) (fun _ => xbar) ↔ xbar = c / (1 - b) := by
  have h : (1 - b) ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  simp only [IsScalarSol, mul_one]
  constructor
  · intro hx
    rw [eq_div_iff h]
    linarith [hx 0]
  · intro hx _
    rw [hx]
    field_simp
    ring

/-- Miao, (1.2), p. 6: for `b = 1` and `c ≠ 0` there is no steady state (which is why the book
requires `b ≠ 1`). -/
theorem eq_1_2_no_steady_state_of_b_one {c : ℝ} (hc : c ≠ 0) (xbar : ℝ) :
    ¬ IsScalarSol 1 c (fun _ => 1) (fun _ => xbar) := by
  intro h
  have := h 0
  simp only [one_mul, mul_one] at this
  exact hc (by linarith)

/-- Miao, (1.3), p. 6: for `b ≠ 1` every solution of (1.2) is `x_t = (x₀ − x̄)bᵗ + x̄`, and
conversely this formula solves (1.2) for every `x₀`. -/
theorem eq_1_3 {b c : ℝ} (hb : b ≠ 1) (x : ℕ → ℝ) :
    IsScalarSol b c (fun _ => 1) x ↔
      ∀ t, x t = (x 0 - c / (1 - b)) * b ^ t + c / (1 - b) := by
  have h : (1 - b) ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  have hbar : c / (1 - b) = b * (c / (1 - b)) + c := by field_simp; ring
  constructor
  · intro hx t
    have hy : ∀ t, x (t + 1) - c / (1 - b) = b * (x t - c / (1 - b)) := fun t => by
      rw [hx t, mul_one]
      linarith
    have := geom_eq (x := fun t => x t - c / (1 - b)) hy t
    linarith
  · intro hx t
    rw [hx (t + 1), hx t, mul_one, pow_succ]
    linarith

/-- Miao, (1.3), p. 6: for `|b| < 1` the steady state is globally asymptotically stable: the
solution family `x₀ ↦ (x₀ − x̄)bᵗ + x̄` converges to `x̄` from every `x₀`. -/
theorem eq_1_3_globallyStable {b c : ℝ} (hb : |b| < 1) :
    IsGloballyStable (fun x0 (t : ℕ) => (x0 - c / (1 - b)) * b ^ t + c / (1 - b))
      (c / (1 - b)) := by
  intro x0
  have := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hb).const_mul (x0 - c / (1 - b))).add_const
    (c / (1 - b))
  simpa using this

/-- Miao, (1.3), p. 6: for `|b| < 1` every solution of (1.2) converges to `x̄ = c/(1 − b)`. -/
theorem eq_1_3_tendsto {b c : ℝ} (hb : |b| < 1) {x : ℕ → ℝ}
    (hx : IsScalarSol b c (fun _ => 1) x) : Tendsto x atTop (𝓝 (c / (1 - b))) := by
  have hb1 : b ≠ 1 := fun h => by rw [h] at hb; norm_num at hb
  have := eq_1_3_globallyStable (c := c) hb (x 0)
  refine this.congr (fun t => ?_)
  exact ((eq_1_3 hb1 x).1 hx t).symm

/-- Miao, (1.3), p. 6: for `|b| > 1` and `x₀ ≠ x̄` the solution explodes, `|x_t| → ∞`. -/
theorem eq_1_3_diverges {b c : ℝ} (hb : 1 < |b|) {x : ℕ → ℝ}
    (hx : IsScalarSol b c (fun _ => 1) x) (h0 : x 0 ≠ c / (1 - b)) :
    Tendsto (fun t => |x t|) atTop atTop := by
  have hb1 : b ≠ 1 := fun h => by rw [h] at hb; norm_num at hb
  have hk : x 0 - c / (1 - b) ≠ 0 := sub_ne_zero.2 h0
  have h1 := (tendsto_atTop_add_const_right _ (-|c / (1 - b)|)
    (abs_pow_mul_tendsto_atTop hb hk))
  refine tendsto_atTop_mono (fun t => ?_) h1
  rw [(eq_1_3 hb1 x).1 hx t, mul_comm (x 0 - c / (1 - b)) (b ^ t)]
  have := abs_sub_abs_le_abs_sub (b ^ t * (x 0 - c / (1 - b))) (-(c / (1 - b)))
  rw [abs_neg, sub_neg_eq_add] at this
  linarith

/-- Miao, (1.3), p. 6: for `|b| > 1` the only stable (bounded) solution of (1.2) is the steady
state `x_t = x̄`. -/
theorem eq_1_3_bdd_iff {b c : ℝ} (hb : 1 < |b|) {x : ℕ → ℝ}
    (hx : IsScalarSol b c (fun _ => 1) x) : BddSeq x ↔ ∀ t, x t = c / (1 - b) := by
  constructor
  · intro hB
    by_contra hne
    have h0 : x 0 ≠ c / (1 - b) := by
      intro h0
      have hb1 : b ≠ 1 := fun h => by rw [h] at hb; norm_num at hb
      exact hne fun t => by rw [(eq_1_3 hb1 x).1 hx t, h0]; ring
    obtain ⟨M, hM⟩ := hB
    obtain ⟨t, ht⟩ := ((eq_1_3_diverges hb hx h0).eventually_gt_atTop M).exists
    linarith [hM t]
  · intro h
    exact ⟨|c / (1 - b)|, fun t => by rw [h t]⟩

/-! ### The backward solution (1.4) and the limit (1.5) -/

/-- Miao, (1.4), p. 6: the backward-looking solution
`x_t = c Σ_{j<t} bʲ z_{t−1−j} + bᵗ x₀`. -/
theorem eq_1_4 {b c : ℝ} {z x : ℕ → ℝ} (hx : IsScalarSol b c z x) (t : ℕ) :
    x t = c * ∑ j ∈ Finset.range t, b ^ j * z (t - 1 - j) + b ^ t * x 0 := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hx n, ih, Finset.sum_range_succ', pow_succ]
    have : ∀ j ∈ Finset.range n, b ^ (j + 1) * z (n + 1 - 1 - (j + 1)) =
        b * (b ^ j * z (n - 1 - j)) := fun j _ => by
      rw [pow_succ]
      have : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
      rw [this]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    simp
    ring

/-- `(−1)ᵗ`, scaled by `c ≠ 0`, does not converge. -/
theorem not_tendsto_neg_one_pow {c : ℝ} (hc : c ≠ 0) (l : ℝ) :
    ¬ Tendsto (fun t : ℕ => c * (-1) ^ t) atTop (𝓝 l) := by
  intro h
  have h1 : Tendsto (fun t : ℕ => c * (-1) ^ (t + 1)) atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).2 h
  have h2 : Tendsto (fun t : ℕ => c * (-1) ^ (t + 1)) atTop (𝓝 (-l)) := by
    have := h.neg
    refine this.congr (fun t => ?_)
    rw [pow_succ]; ring
  have hl : l = 0 := by linarith [tendsto_nhds_unique h1 h2]
  have h3 : Tendsto (fun t : ℕ => |c * (-1) ^ t|) atTop (𝓝 0) := by
    simpa [hl] using h.abs
  have h4 : (fun t : ℕ => |c * (-1) ^ t|) = fun _ => |c| := by
    ext t; simp [abs_mul]
  rw [h4] at h3
  exact hc (abs_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds h3))

/-- **Counterexample to (1.5)** (Miao, p. 7). The book asserts that for `|b| < 1` and bounded
`{z_t}` the limit `lim_t c Σ_{j<t} bʲ z_{t−1−j}` exists. For the bounded `z_t = (−1)ᵗ` and
any `c ≠ 0` no solution of (1.1) converges, for every `b` (in particular `|b| < 1`). -/
theorem eq_1_5_counterexample {b c : ℝ} (hc : c ≠ 0) {x : ℕ → ℝ}
    (hx : IsScalarSol b c (fun t => (-1) ^ t) x) : BddSeq (fun t : ℕ => (-1 : ℝ) ^ t) ∧
      ¬ ∃ L, Tendsto x atTop (𝓝 L) := by
  refine ⟨⟨1, fun t => by simp⟩, ?_⟩
  rintro ⟨L, hL⟩
  have h1 : Tendsto (fun t => x (t + 1) - b * x t) atTop (𝓝 (L - b * L)) :=
    ((tendsto_add_atTop_iff_nat 1).2 hL).sub (hL.const_mul b)
  refine not_tendsto_neg_one_pow hc (L - b * L) (h1.congr (fun t => ?_))
  rw [hx t]; ring

/-- Miao, (1.5), p. 7, corrected: for `|b| < 1` and `z_t → z̄`, every solution of (1.1)
converges to the generalized steady state `c z̄/(1 − b)`, whatever `x₀`. -/
theorem eq_1_5_tendsto {b c zbar : ℝ} (hb : |b| < 1) {z x : ℕ → ℝ}
    (hz : Tendsto z atTop (𝓝 zbar)) (hx : IsScalarSol b c z x) :
    Tendsto x atTop (𝓝 (c * zbar / (1 - b))) := by
  have h1 : 1 - b ≠ 0 := by
    intro h; have : b = 1 := by linarith
    rw [this] at hb; norm_num at hb
  have hy : ∀ t, x (t + 1) - c * zbar / (1 - b) =
      b * (x t - c * zbar / (1 - b)) + c * (z t - zbar) := fun t => by
    rw [hx t]; field_simp; ring
  have he : Tendsto (fun t => c * (z t - zbar)) atTop (𝓝 0) := by
    simpa using (hz.sub_const zbar).const_mul c
  have := tendsto_zero_of_forced hb (y := fun t => x t - c * zbar / (1 - b)) hy he
  simpa using this.add_const (c * zbar / (1 - b))

/-- Miao, (1.5), p. 7, corrected: for `|b| < 1` and bounded `z`, every solution is bounded. -/
theorem eq_1_5_bdd {b c : ℝ} (hb : |b| < 1) {z x : ℕ → ℝ} (hz : BddSeq z)
    (hx : IsScalarSol b c z x) : BddSeq x := by
  refine bddSeq_of_forced hb hx ?_
  obtain ⟨M, hM⟩ := hz
  exact ⟨|c| * M, fun t => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg c)⟩

/-- Miao, (1.5), p. 7, corrected: for `|b| < 1` any two solutions of (1.1) approach each other,
`x_t − x'_t = bᵗ(x₀ − x'₀) → 0`, so the long-run behaviour does not depend on `x₀`. -/
theorem eq_1_5_sub_tendsto {b c : ℝ} (hb : |b| < 1) {z x x' : ℕ → ℝ}
    (hx : IsScalarSol b c z x) (hx' : IsScalarSol b c z x') :
    Tendsto (fun t => x t - x' t) atTop (𝓝 0) := by
  have hd : ∀ t, x (t + 1) - x' (t + 1) = b * (x t - x' t) := fun t => by
    rw [hx t, hx' t]; ring
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hb).mul_const (x 0 - x' 0)
  rw [zero_mul] at this
  exact this.congr (fun t => (geom_eq (x := fun t => x t - x' t) hd t).symm)

/-- Miao, p. 7, `b = 1`: the solution is `x_t = x₀ + c Σ_{j<t} z_j`. -/
theorem eq_1_5_b_one_formula {c : ℝ} {z x : ℕ → ℝ} (hx : IsScalarSol 1 c z x) (t : ℕ) :
    x t = x 0 + c * ∑ j ∈ Finset.range t, z j := by
  induction t with
  | zero => simp
  | succ n ih => rw [hx n, ih, Finset.sum_range_succ]; ring

/-- Miao, p. 7, `b = 1`, `c ≠ 0`: the solution converges iff `Σ_j z_j` converges, as the book
says. -/
theorem eq_1_5_b_one_tendsto_iff {c : ℝ} (hc : c ≠ 0) {z x : ℕ → ℝ}
    (hx : IsScalarSol 1 c z x) :
    (∃ L, Tendsto x atTop (𝓝 L)) ↔
      ∃ S, Tendsto (fun t => ∑ j ∈ Finset.range t, z j) atTop (𝓝 S) := by
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨(L - x 0) / c, ?_⟩
    have := (hL.sub_const (x 0)).div_const c
    refine this.congr (fun t => ?_)
    rw [eq_1_5_b_one_formula hx t]; field_simp; ring
  · rintro ⟨S, hS⟩
    refine ⟨x 0 + c * S, ?_⟩
    exact ((hS.const_mul c).const_add (x 0)).congr (fun t => (eq_1_5_b_one_formula hx t).symm)

/-- Miao, p. 7, `b = 1`: the limit depends on the initial condition: if two solutions converge
to `L` and `L'`, then `L − L' = x₀ − x'₀`. So the solution is not globally stable. -/
theorem eq_1_5_b_one_limit_sub {c : ℝ} {z x x' : ℕ → ℝ} (hx : IsScalarSol 1 c z x)
    (hx' : IsScalarSol 1 c z x') {L L' : ℝ} (hL : Tendsto x atTop (𝓝 L))
    (hL' : Tendsto x' atTop (𝓝 L')) : L - L' = x 0 - x' 0 := by
  have h := hL.sub hL'
  have hc : (fun t => x t - x' t) = fun _ => x 0 - x' 0 := by
    ext t; rw [eq_1_5_b_one_formula hx t, eq_1_5_b_one_formula hx' t]; ring
  rw [hc] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **Counterexample** (Miao, p. 7, `b = −1`). The book says that for `|b| = 1` the solution
does not converge unless `Σ z_j` is finite. For `b = −1`, `c = 1`, `z_t = 1` the constant
`x_t = 1/2` is a convergent solution although the partial sums `Σ_{j<t} z_j = t` diverge. -/
theorem eq_1_5_b_neg_one_counterexample :
    IsScalarSol (-1) 1 (fun _ => 1) (fun _ => 1 / 2) ∧
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) ∧
      Tendsto (fun t => ∑ _j ∈ Finset.range t, (1 : ℝ)) atTop atTop := by
  refine ⟨fun t => by norm_num, tendsto_const_nhds, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact tendsto_natCast_atTop_atTop

/-- Miao, p. 7, `b = −1`, corrected: at most one initial value gives a convergent solution (two
convergent solutions coincide), so the limit, when it exists, does not "depend on `x₀`" in the
book's sense: all other initial values diverge. -/
theorem eq_1_5_b_neg_one_unique {c : ℝ} {z x x' : ℕ → ℝ} (hx : IsScalarSol (-1) c z x)
    (hx' : IsScalarSol (-1) c z x') {L L' : ℝ} (hL : Tendsto x atTop (𝓝 L))
    (hL' : Tendsto x' atTop (𝓝 L')) : x = x' := by
  have hd : ∀ t, x (t + 1) - x' (t + 1) = -1 * (x t - x' t) := fun t => by
    rw [hx t, hx' t]; ring
  have h0 : x 0 - x' 0 = 0 := by
    by_contra h0
    have := not_tendsto_neg_one_pow h0 (L - L')
    exact this ((hL.sub hL').congr (fun t => by
      rw [geom_eq (x := fun t => x t - x' t) hd t]; ring))
  ext t
  have := geom_eq (x := fun t => x t - x' t) hd t
  simp only [h0, mul_zero] at this
  linarith

/-! ### The forward solution (1.6)–(1.8) and bubbles (1.9) -/

/-- Miao, (1.6), p. 7: for `b ≠ 0` and every `T`,
`x_t = (1/b)ᵀ x_{t+T} − (c/b) Σ_{j<T} (1/b)ʲ z_{t+j}`. -/
theorem eq_1_6 {b c : ℝ} (hb : b ≠ 0) {z x : ℕ → ℝ} (hx : IsScalarSol b c z x) (t T : ℕ) :
    x t = (1 / b) ^ T * x (t + T) - c / b * ∑ j ∈ Finset.range T, (1 / b) ^ j * z (t + j) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, ← add_assoc, hx (t + n), pow_succ]
    field_simp
    ring

/-- The forward-looking solution `x*_t = −(c/b) Σ_{j≥0} (1/b)ʲ z_{t+j}` (Miao, (1.8), p. 7). -/
noncomputable def fwdSol (b c : ℝ) (z : ℕ → ℝ) (t : ℕ) : ℝ :=
  -(c / b) * ∑' j : ℕ, (1 / b) ^ j * z (t + j)

theorem abs_one_div_lt_one {b : ℝ} (hb : 1 < |b|) : |1 / b| < 1 := by
  rw [abs_div, abs_one, div_lt_one (by linarith)]
  exact hb

/-- Miao, p. 7: for `|b| > 1` and bounded `z` the series in (1.8) converges (absolutely). -/
theorem eq_1_8_summable {b : ℝ} (hb : 1 < |b|) {z : ℕ → ℝ} (hz : BddSeq z) (t : ℕ) :
    Summable (fun j : ℕ => |(1 / b) ^ j * z (t + j)|) := by
  obtain ⟨M, -, hM⟩ := hz.exists_nonneg
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => ?_)
    ((summable_geometric_of_lt_one (abs_nonneg _) (abs_one_div_lt_one hb)).mul_right M)
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

/-- Miao, (1.8), p. 7: for `|b| > 1` and bounded `z`, the forward solution solves (1.1). -/
theorem eq_1_8_isScalarSol {b c : ℝ} (hb : 1 < |b|) {z : ℕ → ℝ} (hz : BddSeq z) :
    IsScalarSol b c z (fwdSol b c z) := by
  intro t
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; norm_num at hb
  have hs : Summable (fun j : ℕ => (1 / b) ^ j * z (t + j)) :=
    (eq_1_8_summable hb hz t).of_abs
  have hsplit := hs.tsum_eq_zero_add
  have hshift : ∑' j : ℕ, (1 / b) ^ (j + 1) * z (t + (j + 1)) =
      1 / b * ∑' j : ℕ, (1 / b) ^ j * z (t + 1 + j) := by
    rw [← tsum_mul_left]
    congr 1; ext j
    rw [pow_succ, show t + (j + 1) = t + 1 + j by omega]; ring
  simp only [fwdSol]
  rw [hsplit, hshift]
  generalize ∑' j : ℕ, (1 / b) ^ j * z (t + 1 + j) = S
  field_simp
  ring_nf

/-- Miao, p. 7: for `|b| > 1` and bounded `z` the forward solution is stable (bounded). -/
theorem eq_1_8_bdd {b c : ℝ} (hb : 1 < |b|) {z : ℕ → ℝ} (hz : BddSeq z) :
    BddSeq (fwdSol b c z) := by
  obtain ⟨M, -, hM⟩ := hz.exists_nonneg
  have hr := abs_one_div_lt_one hb
  refine ⟨|c / b| * (M * (1 - |1 / b|)⁻¹), fun t => ?_⟩
  simp only [fwdSol, abs_mul, abs_neg]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hs := eq_1_8_summable hb hz t
  have hg := (summable_geometric_of_lt_one (abs_nonneg _) hr).mul_left M
  calc |∑' j : ℕ, (1 / b) ^ j * z (t + j)| ≤ ∑' j : ℕ, |(1 / b) ^ j * z (t + j)| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun j : ℕ =>
          (1 / b) ^ j * z (t + j)) (by simpa [Real.norm_eq_abs] using hs)
    _ ≤ ∑' j : ℕ, M * |1 / b| ^ j := by
        refine hs.tsum_le_tsum (fun j => ?_) hg
        rw [abs_mul, abs_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
    _ = M * (1 - |1 / b|)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg _) hr]

/-- Miao, (1.7), p. 7: a bounded sequence satisfies the transversality condition
`(1/b)ᵀ x_{t+T} → 0` when `|b| > 1`. -/
theorem eq_1_7_of_bdd {b : ℝ} (hb : 1 < |b|) {x : ℕ → ℝ} (hx : BddSeq x) (t : ℕ) :
    Tendsto (fun T : ℕ => (1 / b) ^ T * x (t + T)) atTop (𝓝 0) :=
  pow_mul_tendsto_zero_of_bdd (abs_one_div_lt_one hb) hx t

/-- Miao, p. 7: the forward solution (1.8) satisfies the transversality condition (1.7). -/
theorem eq_1_8_transversality {b c : ℝ} (hb : 1 < |b|) {z : ℕ → ℝ} (hz : BddSeq z) (t : ℕ) :
    Tendsto (fun T : ℕ => (1 / b) ^ T * fwdSol b c z (t + T)) atTop (𝓝 0) :=
  eq_1_7_of_bdd hb (eq_1_8_bdd hb hz) t

/-- Miao, (1.6)–(1.8), p. 7: a solution of (1.1) satisfying the transversality condition (1.7)
at `t` equals the forward solution at `t` (letting `T → ∞` in (1.6)). -/
theorem eq_1_8_unique_of_transversality {b c : ℝ} (hb : 1 < |b|) {z x : ℕ → ℝ}
    (hz : BddSeq z) (hx : IsScalarSol b c z x) (t : ℕ)
    (htv : Tendsto (fun T : ℕ => (1 / b) ^ T * x (t + T)) atTop (𝓝 0)) :
    x t = fwdSol b c z t := by
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; norm_num at hb
  have hs : Summable (fun j : ℕ => (1 / b) ^ j * z (t + j)) :=
    (eq_1_8_summable hb hz t).of_abs
  have h1 : Tendsto (fun T : ℕ => x t + c / b * ∑ j ∈ Finset.range T, (1 / b) ^ j * z (t + j))
      atTop (𝓝 (x t + c / b * ∑' j : ℕ, (1 / b) ^ j * z (t + j))) :=
    (hs.hasSum.tendsto_sum_nat.const_mul (c / b)).const_add (x t)
  have h2 : (fun T : ℕ => x t + c / b * ∑ j ∈ Finset.range T, (1 / b) ^ j * z (t + j)) =
      fun T : ℕ => (1 / b) ^ T * x (t + T) := by
    ext T; rw [eq_1_6 hb0 hx t T]; ring
  rw [h2] at h1
  have := tendsto_nhds_unique h1 htv
  simp only [fwdSol]
  linarith

/-- Miao, (1.8), p. 7: for `|b| > 1` and bounded `z`, the forward solution is the unique
bounded solution of (1.1). -/
theorem eq_1_8_unique_bdd {b c : ℝ} (hb : 1 < |b|) {z x : ℕ → ℝ} (hz : BddSeq z)
    (hx : IsScalarSol b c z x) (hB : BddSeq x) : x = fwdSol b c z :=
  funext fun t => eq_1_8_unique_of_transversality hb hz hx t (eq_1_7_of_bdd hb hB t)

/-- Miao, (1.8), p. 7, summary: for `|b| > 1` and bounded `z` the forward solution solves
(1.1), is bounded, satisfies (1.7), and is the only bounded solution. -/
theorem eq_1_8 {b c : ℝ} (hb : 1 < |b|) {z : ℕ → ℝ} (hz : BddSeq z) :
    IsScalarSol b c z (fwdSol b c z) ∧ BddSeq (fwdSol b c z) ∧
      (∀ t, Tendsto (fun T : ℕ => (1 / b) ^ T * fwdSol b c z (t + T)) atTop (𝓝 0)) ∧
      ∀ x, IsScalarSol b c z x → BddSeq x → x = fwdSol b c z :=
  ⟨eq_1_8_isScalarSol hb hz, eq_1_8_bdd hb hz, eq_1_8_transversality hb hz,
    fun _ hx hB => eq_1_8_unique_bdd hb hz hx hB⟩

/-- Miao, (1.9), p. 8: if `x*` solves (1.1), then `x* + B` solves (1.1) iff `B` is a bubble,
`B_{t+1} = b B_t`. -/
theorem eq_1_9 {b c : ℝ} {z xstar B : ℕ → ℝ} (hx : IsScalarSol b c z xstar) :
    IsScalarSol b c z (fun t => xstar t + B t) ↔ ∀ t, B (t + 1) = b * B t := by
  constructor
  · intro h t
    have := h t
    simp only at this
    rw [hx t] at this
    linarith
  · intro h t
    simp only
    rw [hx t, h t]
    ring

/-- Miao, (1.9), p. 8: every solution is the fundamental solution plus a bubble
`B_t = bᵗ B₀`. -/
theorem eq_1_9_every_solution {b c : ℝ} {z xstar x : ℕ → ℝ} (hxs : IsScalarSol b c z xstar)
    (hx : IsScalarSol b c z x) : ∀ t, x t = xstar t + b ^ t * (x 0 - xstar 0) := by
  have hd : ∀ t, x (t + 1) - xstar (t + 1) = b * (x t - xstar t) := fun t => by
    rw [hx t, hxs t]; ring
  intro t
  have := geom_eq (x := fun t => x t - xstar t) hd t
  linarith

/-- **Correction** (Miao, p. 7, "if `|b| > 1`, (1.4) shows that `{x_t}` diverges"). For `|b| > 1`
and bounded `z`, the forward solution is bounded, and every other solution explodes:
`x₀ ≠ x*₀ ⇒ |x_t| → ∞`. -/
theorem eq_1_8_others_diverge {b c : ℝ} (hb : 1 < |b|) {z x : ℕ → ℝ} (hz : BddSeq z)
    (hx : IsScalarSol b c z x) (h0 : x 0 ≠ fwdSol b c z 0) :
    Tendsto (fun t => |x t|) atTop atTop := by
  obtain ⟨M, hM⟩ := eq_1_8_bdd (c := c) hb hz
  have hk : x 0 - fwdSol b c z 0 ≠ 0 := sub_ne_zero.2 h0
  have h1 := tendsto_atTop_add_const_right _ (-M) (abs_pow_mul_tendsto_atTop hb hk)
  refine tendsto_atTop_mono (fun t => ?_) h1
  rw [eq_1_9_every_solution (eq_1_8_isScalarSol hb hz) hx t]
  have := abs_sub_abs_le_abs_sub (b ^ t * (x 0 - fwdSol b c z 0)) (-fwdSol b c z t)
  rw [abs_neg, sub_neg_eq_add, add_comm] at this
  linarith [hM t]

/-- Miao, p. 8: for `0 < |b| < 1` the infinite sum in (1.8) need not converge: with `z_t = 1`
the series `Σ (1/b)ʲ` diverges. -/
theorem eq_1_8_not_summable {b : ℝ} (hb0 : b ≠ 0) (hb : |b| < 1) :
    ¬ Summable (fun j : ℕ => (1 / b) ^ j * (fun _ : ℕ => (1 : ℝ)) j) := by
  simp only [mul_one]
  rw [summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, abs_div, abs_one,
    div_lt_one (abs_pos.2 hb0)]
  linarith

/-- Miao, p. 8: for `|b| < 1` and `z_t = 1`, every bubble solution `c/(1−b) + B_t`
(`B_{t+1} = b B_t`, any `B₀`) solves (1.1) and converges to `c/(1 − b)`: the bubbles are
globally stable rather than exploding. -/
theorem eq_1_9_bubble_stable {b c : ℝ} (hb : |b| < 1) {B : ℕ → ℝ}
    (hB : ∀ t, B (t + 1) = b * B t) :
    IsScalarSol b c (fun _ => 1) (fun t => c / (1 - b) + B t) ∧
      Tendsto (fun t => c / (1 - b) + B t) atTop (𝓝 (c / (1 - b))) := by
  have hb1 : b ≠ 1 := fun h => by rw [h] at hb; norm_num at hb
  have hconst : IsScalarSol b c (fun _ => 1) (fun _ => c / (1 - b)) :=
    (eq_1_2_steady_state hb1 _).2 rfl
  have hsol := (eq_1_9 (B := B) hconst).2 hB
  exact ⟨hsol, eq_1_3_tendsto hb hsol⟩

/-! ### Example 1.1.1: adaptive versus rational expectations -/

/-- **Example 1.1.1** (Miao, pp. 8–9). From the pricing equation (1.10)
`p_t = (ₜpᵉₜ₊₁ + d)/R` and adaptive expectations (1.11)
`ₜ₊₁pᵉₜ₊₂ = (1 − λ) ₜpᵉₜ₊₁ + λ p_{t+1}` (here `e t` is the period-`t` forecast `ₜpᵉₜ₊₁`):
`R p_{t+1} − d = (1 − λ)(R p_t − d) + λ p_{t+1}`, i.e.
`(R − λ) p_{t+1} = (1 − λ) R p_t + λ d`. -/
theorem example_1_1_1_recursion {R d lam : ℝ} (hR : R ≠ 0) {p e : ℕ → ℝ}
    (h110 : ∀ t, p t = (e t + d) / R)
    (h111 : ∀ t, e (t + 1) = (1 - lam) * e t + lam * p (t + 1)) (t : ℕ) :
    R * p (t + 1) - d = (1 - lam) * (R * p t - d) + lam * p (t + 1) ∧
      (R - lam) * p (t + 1) = (1 - lam) * R * p t + lam * d := by
  have he : ∀ t, e t = R * p t - d := fun t => by rw [h110 t]; field_simp; ring
  have h := h111 t
  rw [he, he] at h
  constructor <;> linarith

/-- **Example 1.1.1** (Miao, p. 9): the backward-looking solution
`p_t = aᵗ p₀ + (1 − aᵗ) d/(R − 1)`, `a = R(1 − λ)/(R − λ)` (the printed formula is correct;
it needs `R ≠ λ`, `R ≠ 1` and `λ ≠ 0`). -/
theorem example_1_1_1_backward {R d lam : ℝ} (hRl : R ≠ lam) (hR1 : R ≠ 1) (hl : lam ≠ 0)
    {p : ℕ → ℝ} (hp : ∀ t, (R - lam) * p (t + 1) = (1 - lam) * R * p t + lam * d) (t : ℕ) :
    p t = (R * (1 - lam) / (R - lam)) ^ t * p 0 +
      (1 - (R * (1 - lam) / (R - lam)) ^ t) * (d / (R - 1)) := by
  have hRl' : R - lam ≠ 0 := sub_ne_zero.2 hRl
  have hR1' : R - 1 ≠ 0 := sub_ne_zero.2 hR1
  have ha1 : R * (1 - lam) / (R - lam) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hRl']
    intro h
    have : lam * (R - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hl h1
    · exact hR1' h1
  have hsol : IsScalarSol (R * (1 - lam) / (R - lam)) (lam * d / (R - lam)) (fun _ => 1) p := by
    intro t
    have := hp t
    field_simp
    linarith
  have hbar : lam * d / (R - lam) / (1 - R * (1 - lam) / (R - lam)) = d / (R - 1) := by
    have h1 : R - lam - R * (1 - lam) ≠ 0 := by
      have : R - lam - R * (1 - lam) = lam * (R - 1) := by ring
      rw [this]; exact mul_ne_zero hl hR1'
    rw [one_sub_div hRl', div_div_div_cancel_right₀ hRl', div_eq_div_iff h1 hR1']
    ring
  have := (eq_1_3 ha1 p).1 hsol t
  rw [hbar] at this
  rw [this]
  ring

/-- **Example 1.1.1** (Miao, p. 9), stated precisely: the adaptive-expectations price converges
to `p̄ = d/(R − 1)` iff `p₀ = p̄` or `|a| < 1`. -/
theorem example_1_1_1_tendsto_iff {R d lam : ℝ} (hRl : R ≠ lam) (hR1 : R ≠ 1) (hl : lam ≠ 0)
    {p : ℕ → ℝ} (hp : ∀ t, (R - lam) * p (t + 1) = (1 - lam) * R * p t + lam * d) :
    Tendsto p atTop (𝓝 (d / (R - 1))) ↔
      p 0 = d / (R - 1) ∨ |R * (1 - lam) / (R - lam)| < 1 := by
  set a := R * (1 - lam) / (R - lam)
  have hform : ∀ t, p t - d / (R - 1) = a ^ t * (p 0 - d / (R - 1)) := fun t => by
    rw [example_1_1_1_backward hRl hR1 hl hp t]; ring
  rw [← tendsto_sub_nhds_zero_iff]
  have hfun : (fun t => p t - d / (R - 1)) = fun t => a ^ t * (p 0 - d / (R - 1)) :=
    funext hform
  rw [hfun]
  by_cases h0 : p 0 = d / (R - 1)
  · simp [h0]
  · rw [pow_mul_tendsto_zero_iff (sub_ne_zero.2 h0)]
    simp [h0]

/-- **Example 1.1.1** (Miao, p. 9): for `λ ∈ (0, 1)` and `R > λ` one has `0 < a` and
`|a| < 1 ⟺ R > 1`. So for a gross return `R > 1` the book's stability assumption `|a| < 1`
always holds. -/
theorem example_1_1_1_abs_a_lt_one_iff {R lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (hRl : lam < R) :
    0 < R * (1 - lam) / (R - lam) ∧ (|R * (1 - lam) / (R - lam)| < 1 ↔ 1 < R) := by
  have hpos : 0 < R - lam := by linarith
  have ha : 0 < R * (1 - lam) / (R - lam) :=
    div_pos (mul_pos (by linarith) (by linarith)) hpos
  refine ⟨ha, ?_⟩
  rw [abs_of_pos ha, div_lt_one hpos]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Example 1.1.1** (Miao, p. 9), perfect foresight (1.12) `p_t = (p_{t+1} + d)/R`: for every
`T`, `p_t = d/(R − 1) + p_{t+T}/Rᵀ − d/((R − 1)Rᵀ)`. -/
theorem example_1_1_1_forward {R d : ℝ} (hR0 : R ≠ 0) (hR1 : R ≠ 1) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + d) / R) (t T : ℕ) :
    p t = d / (R - 1) + p (t + T) / R ^ T - d / ((R - 1) * R ^ T) := by
  have hR1' : R - 1 ≠ 0 := sub_ne_zero.2 hR1
  induction T with
  | zero => simp
  | succ n ih =>
    rw [ih, h (t + n), pow_succ, ← add_assoc]
    field_simp
    ring

/-- **Example 1.1.1** (Miao, p. 9): for `R > 1`, `p_t = d/(R − 1) + lim_T p_{t+T}/Rᵀ`; the limit
exists for every solution of (1.12). -/
theorem example_1_1_1_forward_limit {R d : ℝ} (hR : 1 < R) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + d) / R) (t : ℕ) :
    Tendsto (fun T : ℕ => p (t + T) / R ^ T) atTop (𝓝 (p t - d / (R - 1))) := by
  have hR0 : R ≠ 0 := by positivity
  have hR1 : R - 1 ≠ 0 := by linarith
  have hlim : Tendsto (fun T : ℕ => p t - d / (R - 1) + d / (R - 1) * (R ^ T)⁻¹) atTop
      (𝓝 (p t - d / (R - 1))) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt hR)).const_mul (d / (R - 1)) |>.const_add
      (p t - d / (R - 1))
  refine hlim.congr (fun T => ?_)
  have := example_1_1_1_forward hR0 (by linarith) h t T
  have hRT : R ^ T ≠ 0 := pow_ne_zero _ hR0
  field_simp
  field_simp at this
  linarith

/-- The perfect-foresight equation `p_t = (p_{t+1} + d)/R` is (1.1) with `b = R`, `c = −d`,
`z_t = 1`. -/
theorem example_1_1_1_isScalarSol {R d : ℝ} (hR0 : R ≠ 0) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + d) / R) : IsScalarSol R (-d) (fun _ => 1) p := by
  intro t
  have := h t
  field_simp at this
  linarith

/-- **Example 1.1.1** (Miao, p. 9): for `R > 1` every perfect-foresight solution is the
fundamental value plus a bubble, `p_t = d/(R − 1) + Rᵗ(p₀ − d/(R − 1))`. -/
theorem example_1_1_1_bubbles {R d : ℝ} (hR : 1 < R) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + d) / R) (t : ℕ) :
    p t = d / (R - 1) + R ^ t * (p 0 - d / (R - 1)) := by
  have hR0 : R ≠ 0 := by positivity
  have hbar : -d / (1 - R) = d / (R - 1) := by
    rw [← neg_div_neg_eq, neg_neg, neg_sub]
  have := (eq_1_3 (b := R) (by linarith) p).1 (example_1_1_1_isScalarSol hR0 h) t
  rw [hbar] at this
  rw [this]; ring

/-- **Example 1.1.1** (Miao, p. 9): for `R > 1`, ruling out bubbles, the unique bounded
solution of (1.12) is the fundamental value `p_t = d/(R − 1)`. -/
theorem example_1_1_1_unique_bdd {R d : ℝ} (hR : 1 < R) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + d) / R) : BddSeq p ↔ ∀ t, p t = d / (R - 1) := by
  have hR0 : R ≠ 0 := by positivity
  have hbar : -d / (1 - R) = d / (R - 1) := by
    rw [← neg_div_neg_eq, neg_neg, neg_sub]
  have := eq_1_3_bdd_iff (b := R) (by rw [abs_of_pos (by linarith)]; exact hR)
    (example_1_1_1_isScalarSol hR0 h)
  rwa [hbar] at this

/-! ### Example 1.1.2: dividend taxes -/

/-- The dividend tax rate in Example 1.1.2 (Miao, p. 10): `τ₁` on dividends paid at
`s ≤ T`, `τ₂` from `T + 1` on. -/
def divTax (τ₁ τ₂ : ℝ) (T s : ℕ) : ℝ :=
  if s ≤ T then τ₁ else τ₂

/-- The price path of Example 1.1.2 (Miao, p. 10): for `t ≤ T`,
`p_t = (1 − τ₁)d/(R − 1) + R^{−(T−t)} (τ₁ − τ₂)d/(R − 1)`; for `t ≥ T`,
`p_t = (1 − τ₂)d/(R − 1)`. -/
noncomputable def taxPath (R d τ₁ τ₂ : ℝ) (T t : ℕ) : ℝ :=
  if t ≤ T then (1 - τ₁) * d / (R - 1) + (τ₁ - τ₂) * d / (R - 1) / R ^ (T - t)
  else (1 - τ₂) * d / (R - 1)

/-- `(1/R) Σ_{j<k} A/Rʲ = A/(R − 1) (1 − 1/Rᵏ)`. -/
theorem sum_div_pow_eq {R A : ℝ} (hR0 : R ≠ 0) (hR1 : R ≠ 1) (k : ℕ) :
    1 / R * ∑ j ∈ Finset.range k, A / R ^ j = A / (R - 1) * (1 - 1 / R ^ k) := by
  have hR1' : R - 1 ≠ 0 := sub_ne_zero.2 hR1
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    field_simp
    ring

/-- **Example 1.1.2** (Miao, p. 10): for every solution of
`p_t = (p_{t+1} + (1 − τ_{t+1})d)/R`, `p₀ = p_T/Rᵀ + (1/R) Σ_{j<T} (1 − τ₁)d/Rʲ`
(the forward identity (1.6) over the low-tax years). -/
theorem example_1_1_2_p0_forward {R d τ₁ τ₂ : ℝ} {T : ℕ} (hR0 : R ≠ 0) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + (1 - divTax τ₁ τ₂ T (t + 1)) * d) / R) :
    p 0 = 1 / R ^ T * p T + 1 / R * ∑ j ∈ Finset.range T, (1 - τ₁) * d / R ^ j := by
  have key : ∀ k, k ≤ T →
      p 0 = 1 / R ^ k * p k + 1 / R * ∑ j ∈ Finset.range k, (1 - τ₁) * d / R ^ j := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [ih (by omega), h n, Finset.sum_range_succ]
      have : divTax τ₁ τ₂ T (n + 1) = τ₁ := by simp only [divTax, hn, ↓reduceIte]
      rw [this, pow_succ]
      field_simp
      ring
  exact key T le_rfl

/-- **Example 1.1.2** (Miao, p. 10): for `R > 1` every bounded solution has
`p_T = (1 − τ₂)d/(R − 1)` (after `T` the price is the new fundamental value). -/
theorem example_1_1_2_pT {R d τ₁ τ₂ : ℝ} {T : ℕ} (hR : 1 < R) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + (1 - divTax τ₁ τ₂ T (t + 1)) * d) / R) (hB : BddSeq p) :
    ∀ s, p (T + s) = (1 - τ₂) * d / (R - 1) := by
  have hq : ∀ s, p (T + s) = (p (T + s + 1) + (1 - τ₂) * d) / R := fun s => by
    rw [h (T + s)]
    have : divTax τ₁ τ₂ T (T + s + 1) = τ₂ := by
      simp only [divTax, show ¬ T + s + 1 ≤ T by omega, ↓reduceIte]
    rw [this]
  have hqB : BddSeq (fun s => p (T + s)) := by
    obtain ⟨M, hM⟩ := hB; exact ⟨M, fun s => hM _⟩
  have := (example_1_1_1_unique_bdd hR (p := fun s => p (T + s)) hq).1 hqB
  intro s
  rw [this s, mul_div_assoc]

/-- **Example 1.1.2** (Miao, p. 10): for `R > 1` every bounded solution has the printed
`p₀ = (1 − τ₁)d/(R − 1) + (1/Rᵀ)[(1 − τ₂)d/(R − 1) − (1 − τ₁)d/(R − 1)]`. -/
theorem example_1_1_2_p0 {R d τ₁ τ₂ : ℝ} {T : ℕ} (hR : 1 < R) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + (1 - divTax τ₁ τ₂ T (t + 1)) * d) / R) (hB : BddSeq p) :
    p 0 = 1 / R ^ T * ((1 - τ₂) * d / (R - 1)) +
        1 / R * ∑ j ∈ Finset.range T, (1 - τ₁) * d / R ^ j ∧
      p 0 = (1 - τ₁) * d / (R - 1) +
        1 / R ^ T * ((1 - τ₂) * d / (R - 1) - (1 - τ₁) * d / (R - 1)) := by
  have hR0 : R ≠ 0 := by positivity
  have hpT := example_1_1_2_pT hR h hB 0
  rw [add_zero] at hpT
  have h1 := example_1_1_2_p0_forward hR0 h
  rw [hpT] at h1
  refine ⟨h1, ?_⟩
  rw [h1, sum_div_pow_eq hR0 (by linarith)]
  ring

/-- **Example 1.1.2** (Miao, p. 10): `taxPath` solves the pricing equation with the announced
tax schedule. -/
theorem example_1_1_2_solves {R d τ₁ τ₂ : ℝ} {T : ℕ} (hR : 1 < R) (t : ℕ) :
    taxPath R d τ₁ τ₂ T t =
      (taxPath R d τ₁ τ₂ T (t + 1) + (1 - divTax τ₁ τ₂ T (t + 1)) * d) / R := by
  have hR0 : R ≠ 0 := by positivity
  have hR1 : R - 1 ≠ 0 := by linarith
  rcases lt_trichotomy (t + 1) (T + 1) with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, T = t + 1 + k := ⟨T - (t + 1), by omega⟩
    simp only [taxPath, divTax, show t ≤ t + 1 + k by omega, show t + 1 ≤ t + 1 + k by omega,
      ↓reduceIte, show t + 1 + k - t = k + 1 by omega, show t + 1 + k - (t + 1) = k by omega,
      pow_succ]
    field_simp
    ring
  · have ht : t = T := by omega
    subst ht
    simp only [taxPath, divTax, le_refl, show ¬ t + 1 ≤ t by omega, ↓reduceIte, Nat.sub_self,
      pow_zero, div_one]
    field_simp
    ring
  · simp only [taxPath, divTax, show ¬ t ≤ T by omega, show ¬ t + 1 ≤ T by omega, ↓reduceIte]
    field_simp
    ring

/-- **Example 1.1.2** (Miao, p. 10): `taxPath` is constant, equal to the new fundamental value
`(1 − τ₂)d/(R − 1)`, from `T` on. -/
theorem example_1_1_2_const {R d τ₁ τ₂ : ℝ} {T t : ℕ} (ht : T ≤ t) :
    taxPath R d τ₁ τ₂ T t = (1 - τ₂) * d / (R - 1) := by
  rcases ht.lt_or_eq with h | h
  · simp only [taxPath, show ¬ t ≤ T by omega, ↓reduceIte]
  · subst h
    simp only [taxPath, le_refl, ↓reduceIte, Nat.sub_self, pow_zero, div_one]
    ring

/-- **Example 1.1.2** (Miao, p. 10): for `R > 1`, `taxPath` is the unique bounded solution. -/
theorem example_1_1_2_unique {R d τ₁ τ₂ : ℝ} {T : ℕ} (hR : 1 < R) {p : ℕ → ℝ}
    (h : ∀ t, p t = (p (t + 1) + (1 - divTax τ₁ τ₂ T (t + 1)) * d) / R) :
    BddSeq p ↔ p = taxPath R d τ₁ τ₂ T := by
  have hR0 : R ≠ 0 := by positivity
  have htB : BddSeq (taxPath R d τ₁ τ₂ T) := by
    refine bddSeq_of_tendsto (L := (1 - τ₂) * d / (R - 1)) (tendsto_const_nhds.congr' ?_)
    exact eventually_atTop.2 ⟨T, fun t ht => (example_1_1_2_const ht).symm⟩
  constructor
  · intro hB
    have hd : ∀ t, p (t + 1) - taxPath R d τ₁ τ₂ T (t + 1) =
        R * (p t - taxPath R d τ₁ τ₂ T t) := fun t => by
      have h1 := h t
      have h2 := example_1_1_2_solves (d := d) (τ₁ := τ₁) (τ₂ := τ₂) (T := T) hR t
      field_simp at h1 h2
      linarith
    have hdB : BddSeq (fun t => p t - taxPath R d τ₁ τ₂ T t) := by
      obtain ⟨M, hM⟩ := hB
      obtain ⟨M', hM'⟩ := htB
      exact ⟨M + M', fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))⟩
    have h0 := (geom_bdd_iff (by rw [abs_of_pos (by linarith)]; exact hR) hd).1 hdB
    ext t
    have := geom_eq (x := fun t => p t - taxPath R d τ₁ τ₂ T t) hd t
    simp only [h0, mul_zero] at this
    linarith
  · rintro rfl
    exact htB

/-- **Example 1.1.2** (Miao, p. 10): for `τ₂ > τ₁`, `d > 0`, `R > 1` the price drops at time 0
below the old fundamental value `(1 − τ₁)d/(R − 1)` (the price before the announcement). -/
theorem example_1_1_2_drop {R d τ₁ τ₂ : ℝ} {T : ℕ} (hR : 1 < R) (hd : 0 < d) (hτ : τ₁ < τ₂) :
    taxPath R d τ₁ τ₂ T 0 < (1 - τ₁) * d / (R - 1) := by
  simp only [taxPath, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  have : (τ₁ - τ₂) * d / (R - 1) / R ^ T < 0 :=
    div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hd)
      (by linarith)) (by positivity)
  linarith

/-- **Example 1.1.2** (Miao, p. 10): for `τ₂ > τ₁`, `d > 0`, `R > 1` the price declines
strictly from `0` to `T`. -/
theorem example_1_1_2_decreasing {R d τ₁ τ₂ : ℝ} {T : ℕ} (hR : 1 < R) (hd : 0 < d)
    (hτ : τ₁ < τ₂) {t : ℕ} (ht : t < T) :
    taxPath R d τ₁ τ₂ T (t + 1) < taxPath R d τ₁ τ₂ T t := by
  obtain ⟨k, rfl⟩ : ∃ k, T = t + 1 + k := ⟨T - (t + 1), by omega⟩
  simp only [taxPath, show t ≤ t + 1 + k by omega, show t + 1 ≤ t + 1 + k by omega,
    ↓reduceIte, show t + 1 + k - t = k + 1 by omega, show t + 1 + k - (t + 1) = k by omega]
  have hR0 : (0 : ℝ) < R := by linarith
  have hy : (τ₁ - τ₂) * d / (R - 1) / R ^ (k + 1) < 0 :=
    div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hd)
      (by linarith)) (by positivity)
  have heq : (τ₁ - τ₂) * d / (R - 1) / R ^ k = R * ((τ₁ - τ₂) * d / (R - 1) / R ^ (k + 1)) := by
    rw [pow_succ]; field_simp
  rw [heq]
  nlinarith

end Miao.OverlappingGenerations
