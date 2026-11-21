import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Definitions of Chapter 1

Copied from `EconomicDynamics/DifferenceEquations` (module `Basics`), namespace renamed.

Miao, §1.4, pp. 15–18: the first-order linear system `Ax_{t+1} = Bx_t + Cz_t` (1.20) and the
vocabulary used throughout the chapter.

* `IsSolution A B C z x`: `x` solves (1.20) for the forcing sequence `z`.
* `IsRegular A B` (Assumption 1.4.1): `det(Aα − B) ≠ 0` for some `α`.
* `EventuallyConst z zbar` (Assumption 1.4.2): `z_t = z̄` for all `t ≥ T`.
* `IsStableSeq x` (Definition 1.4.2): `‖x_t‖ < M` for all `t`, for some `M > 0`. On `ι → ℝ` the
  norm is the max norm `‖X‖ = maxⱼ |Xⱼ|` of the book.
* `IsSteadyStateOf x xbar` (Definition 1.4.1): once the sequence reaches `x̄` it stays there.
* `IsAsympStable`, `basin`, `IsGloballyStable` (Definitions 1.4.3–1.4.4), for a family of
  sequences `sol X₀` indexed by the initial value.
* `IsStableMatrix M` (Definition 1.4.5): every eigenvalue of the complex matrix `M` has modulus
  less than one; a real matrix `A` is stable when `A.map Complex.ofRealHom` is.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

open scoped Matrix

/-- `x` solves `Ax_{t+1} = Bx_t + Cz_t` (Miao, (1.20), p. 15). -/
def IsSolution {K n m : Type*} [CommRing K] [Fintype n] [Fintype m]
    (A B : Matrix n n K) (C : Matrix n m K) (z : ℕ → m → K) (x : ℕ → n → K) : Prop :=
  ∀ t, A *ᵥ x (t + 1) = B *ᵥ x t + C *ᵥ z t

/-- **Assumption 1.4.1** (regularity, Miao, p. 15): `det(Aα − B) ≠ 0` for some `α`. -/
def IsRegular {K n : Type*} [CommRing K] [Fintype n] [DecidableEq n] (A B : Matrix n n K) :
    Prop :=
  ∃ α : K, Matrix.det (α • A - B) ≠ 0

/-- **Assumption 1.4.2** (Miao, p. 16): `z_t = z̄` for all `t ≥ T`, for some `T`. -/
def EventuallyConst {α : Type*} (z : ℕ → α) (zbar : α) : Prop :=
  ∃ T, ∀ t, T ≤ t → z t = zbar

/-- **Definition 1.4.2** (Miao, p. 17): a sequence is stable if it is bounded, `‖x_t‖ < M` for
some `M > 0` and all `t`. -/
def IsStableSeq {E : Type*} [Norm E] (x : ℕ → E) : Prop :=
  ∃ M, 0 < M ∧ ∀ t, ‖x t‖ < M

/-- **Definition 1.4.1** (Miao, p. 16): `x̄` is a steady state of the sequence `x` if `x_t = x̄`
implies `x_s = x̄` for every `s > t`. -/
def IsSteadyStateOf {α : Type*} (x : ℕ → α) (xbar : α) : Prop :=
  ∀ t, x t = xbar → ∀ s, t < s → x s = xbar

/-- **Definition 1.4.3** (Miao, p. 17): `x̄` is asymptotically stable for the family of sequences
`sol X₀` (indexed by the initial value) if `sol X₀ t → x̄` for some `X₀`. -/
def IsAsympStable {α : Type*} [TopologicalSpace α] (sol : α → ℕ → α) (xbar : α) : Prop :=
  ∃ X₀, Tendsto (sol X₀) atTop (𝓝 xbar)

/-- The basin of attraction of `x̄` (Definition 1.4.3): the initial values from which the
sequence converges to `x̄`. -/
def basin {α : Type*} [TopologicalSpace α] (sol : α → ℕ → α) (xbar : α) : Set α :=
  {X₀ | Tendsto (sol X₀) atTop (𝓝 xbar)}

/-- **Definition 1.4.4** (Miao, p. 17): `x̄` is globally (asymptotically) stable if
`sol X₀ t → x̄` for every initial value `X₀`. -/
def IsGloballyStable {α : Type*} [TopologicalSpace α] (sol : α → ℕ → α) (xbar : α) : Prop :=
  ∀ X₀, Tendsto (sol X₀) atTop (𝓝 xbar)

/-- **Definition 1.4.5** (Miao, p. 18): a complex matrix is stable if all its eigenvalues have
modulus less than one. -/
def IsStableMatrix {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → ‖μ‖ < 1

theorem isGloballyStable_iff_basin {α : Type*} [TopologicalSpace α] (sol : α → ℕ → α)
    (xbar : α) : IsGloballyStable sol xbar ↔ basin sol xbar = Set.univ := by
  simp [IsGloballyStable, basin, Set.eq_univ_iff_forall]

theorem isAsympStable_iff_basin {α : Type*} [TopologicalSpace α] (sol : α → ℕ → α)
    (xbar : α) : IsAsympStable sol xbar ↔ (basin sol xbar).Nonempty := by
  simp [IsAsympStable, basin, Set.Nonempty]

theorem isStableSeq_iff_bddAbove {E : Type*} [Norm E] (x : ℕ → E) :
    IsStableSeq x ↔ BddAbove (Set.range fun t => ‖x t‖) := by
  constructor
  · rintro ⟨M, -, hM⟩
    exact ⟨M, by rintro _ ⟨t, rfl⟩; exact (hM t).le⟩
  · rintro ⟨M, hM⟩
    refine ⟨max M 0 + 1, by positivity, fun t => ?_⟩
    have := hM ⟨t, rfl⟩
    linarith [le_max_left M 0]

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Phase diagrams

Copied from `EconomicDynamics/DifferenceEquations` (module `PhaseDiagram`), namespace renamed.

Miao, §1.5, pp. 27–28: the linear system
`x_{t+1} = ã x_t + b y_t − e`, `y_{t+1} = c x_t − d̃ y_t + f` with `a = ã − 1`, `d = d̃ + 1`
and `a, b, c, d, e, f > 0`; `x₀` is given.

**A 2×2 saddle toolkit** (used again in `Exercises.lean`). For the homogeneous system
`X_{t+1} = m₁₁X_t + m₁₂Y_t`, `Y_{t+1} = m₂₁X_t + m₂₂Y_t` (`IsSol22`) with characteristic
polynomial `p(μ) = μ² − (m₁₁ + m₂₂)μ + (m₁₁m₂₂ − m₁₂m₂₁)` (`cp22`) and `p(1) < 0`: the roots
`λ_lo < 1 < λ_hi` are real (`roots22_lt`); `λ_lo > −1 ⟺ p(−1) > 0` (`lamLo_gt_neg_one_iff`);
`s_t = m₂₁X_t + (λ − m₁₁)Y_t` is geometric at rate `λ` for each root (`sVar_succ`); a bounded
solution has `s^hi = 0` (`sHi_zero_of_bdd`); and, when `m₁₂m₂₁ > 0`, for `X₀` predetermined the
saddle path `Y₀ = kX₀`, `k = (λ_lo − m₁₁)/m₁₂` (`saddle22`) is the unique bounded solution and
converges iff `p(−1) > 0` (`saddle22_unique`, `saddle22_tendsto`, `saddle22_unbounded`,
`saddle22_iff`, `saddle22_only_zero`).

**The book's system.** The Δ-form (`phase_delta`), the isocline equivalences
(`phase_isocline_x`, `phase_isocline_y`), the unique steady state (`phase_steady_state`), and
the roots of `[[1 + a, b], [c, 1 − d]]`: real, one below and one above `1` (`phase_roots`).

**Correction.** The book says the phase diagram shows a convergent saddle path with all other
paths diverging. The second root lies in `(−1, 1)` only when `(2 + a)(2 − d) > bc`
(`phase_lamLo_iff`). Under that condition each `x₀` has exactly one convergent path, on the
downward-sloping saddle line, and every other path is unbounded (`phase_saddle`,
`phase_saddle_slope`); and "every `x₀` has a convergent path" is equivalent to the condition
(`phase_saddle_iff`). For `a = b = c = e = f = 1`, `d = 3` both roots are unstable and the
steady state is the only bounded path (`phase_counterexample`).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-! ### A 2×2 saddle toolkit -/

/-- `(X, Y)` solves `X_{t+1} = m₁₁X_t + m₁₂Y_t`, `Y_{t+1} = m₂₁X_t + m₂₂Y_t`. -/
def IsSol22 (m11 m12 m21 m22 : ℝ) (X Y : ℕ → ℝ) : Prop :=
  ∀ t, X (t + 1) = m11 * X t + m12 * Y t ∧ Y (t + 1) = m21 * X t + m22 * Y t

/-- The characteristic polynomial `p(μ) = μ² − tr μ + det` of `[[m₁₁, m₁₂], [m₂₁, m₂₂]]`. -/
def cp22 (m11 m12 m21 m22 μ : ℝ) : ℝ :=
  μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21)

/-- The discriminant `tr² − 4 det`. -/
def disc22 (m11 m12 m21 m22 : ℝ) : ℝ :=
  (m11 + m22) ^ 2 - 4 * (m11 * m22 - m12 * m21)

/-- The smaller root `(tr − √disc)/2`. -/
noncomputable def lamLo (m11 m12 m21 m22 : ℝ) : ℝ :=
  ((m11 + m22) - Real.sqrt (disc22 m11 m12 m21 m22)) / 2

/-- The larger root `(tr + √disc)/2`. -/
noncomputable def lamHi (m11 m12 m21 m22 : ℝ) : ℝ :=
  ((m11 + m22) + Real.sqrt (disc22 m11 m12 m21 m22)) / 2

/-- The variable `s_t = m₂₁X_t + (λ − m₁₁)Y_t` attached to the root `λ` (a left eigenvector). -/
def sVar (m11 m21 l : ℝ) (X Y : ℕ → ℝ) (t : ℕ) : ℝ :=
  m21 * X t + (l - m11) * Y t

variable {m11 m12 m21 m22 : ℝ}

theorem disc22_pos (h1 : cp22 m11 m12 m21 m22 1 < 0) : 0 < disc22 m11 m12 m21 m22 := by
  simp only [cp22, disc22] at *
  nlinarith [sq_nonneg (m11 + m22 - 2)]

theorem cp22_factor (h1 : cp22 m11 m12 m21 m22 1 < 0) (μ : ℝ) :
    cp22 m11 m12 m21 m22 μ = (μ - lamLo m11 m12 m21 m22) * (μ - lamHi m11 m12 m21 m22) := by
  have hs := Real.sq_sqrt (disc22_pos h1).le
  simp only [cp22, lamLo, lamHi, disc22] at *
  linear_combination (1 / 4) * hs

theorem cp22_lamLo (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    cp22 m11 m12 m21 m22 (lamLo m11 m12 m21 m22) = 0 := by
  rw [cp22_factor h1]; ring

theorem cp22_lamHi (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    cp22 m11 m12 m21 m22 (lamHi m11 m12 m21 m22) = 0 := by
  rw [cp22_factor h1]; ring

theorem lamLo_lt_lamHi (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    lamLo m11 m12 m21 m22 < lamHi m11 m12 m21 m22 := by
  have := Real.sqrt_pos.2 (disc22_pos h1)
  simp only [lamLo, lamHi]
  linarith

/-- With `p(1) < 0` the two roots are real with `λ_lo < 1 < λ_hi`. -/
theorem roots22_lt (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    lamLo m11 m12 m21 m22 < 1 ∧ 1 < lamHi m11 m12 m21 m22 := by
  have hf := cp22_factor h1 1
  have hlt := lamLo_lt_lamHi h1
  rw [hf] at h1
  constructor <;> nlinarith

/-- With `p(1) < 0`: `λ_lo > −1 ⟺ p(−1) > 0`. -/
theorem lamLo_gt_neg_one_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    -1 < lamLo m11 m12 m21 m22 ↔ 0 < cp22 m11 m12 m21 m22 (-1) := by
  have hf := cp22_factor h1 (-1)
  have hhi := (roots22_lt h1).2
  rw [hf]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- With `p(1) < 0`: `|λ_lo| < 1 ⟺ p(−1) > 0`. -/
theorem abs_lamLo_lt_one_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) :
    |lamLo m11 m12 m21 m22| < 1 ↔ 0 < cp22 m11 m12 m21 m22 (-1) := by
  rw [abs_lt, ← lamLo_gt_neg_one_iff h1]
  exact ⟨fun h => h.1, fun h => ⟨h, (roots22_lt h1).1⟩⟩

/-- `p(m₁₁) = −m₁₂m₂₁`, so `m₁₂m₂₁ > 0` puts `m₁₁` strictly between the roots. -/
theorem lamLo_lt_m11 (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21) :
    lamLo m11 m12 m21 m22 < m11 ∧ m11 < lamHi m11 m12 m21 m22 := by
  have hf := cp22_factor h1 m11
  have hlt := lamLo_lt_lamHi h1
  have : cp22 m11 m12 m21 m22 m11 = -(m12 * m21) := by simp only [cp22]; ring
  rw [this] at hf
  constructor <;> nlinarith

/-- For a root `λ` of `p`, one step of the system multiplies `s` by `λ`. -/
theorem sVar_step {l : ℝ} (hl : cp22 m11 m12 m21 m22 l = 0) {X Y : ℕ → ℝ} {t : ℕ}
    (hX : X (t + 1) = m11 * X t + m12 * Y t) (hY : Y (t + 1) = m21 * X t + m22 * Y t) :
    sVar m11 m21 l X Y (t + 1) = l * sVar m11 m21 l X Y t := by
  simp only [sVar, cp22] at *
  rw [hX, hY]
  linear_combination (-Y t) * hl

/-- For a root `λ` and a solution, `s_t = λᵗ s₀`. -/
theorem sVar_succ {l : ℝ} (hl : cp22 m11 m12 m21 m22 l = 0) {X Y : ℕ → ℝ}
    (h : IsSol22 m11 m12 m21 m22 X Y) (t : ℕ) :
    sVar m11 m21 l X Y t = l ^ t * sVar m11 m21 l X Y 0 :=
  geom_eq (fun t => sVar_step hl (h t).1 (h t).2) t

/-- Recovering `(X, Y)` from the two `s` variables. -/
theorem recover22 {l1 l2 : ℝ} (hne : l1 ≠ l2) (hm21 : m21 ≠ 0) (X Y : ℕ → ℝ) (t : ℕ) :
    X t = ((l2 - m11) * sVar m11 m21 l1 X Y t - (l1 - m11) * sVar m11 m21 l2 X Y t) /
        (m21 * (l2 - l1)) ∧
      Y t = (sVar m11 m21 l2 X Y t - sVar m11 m21 l1 X Y t) / (l2 - l1) := by
  have hd : l2 - l1 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  simp only [sVar]
  constructor <;> field_simp <;> ring

/-- Solutions with the same initial values coincide. -/
theorem IsSol22.ext {X Y X' Y' : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y)
    (h' : IsSol22 m11 m12 m21 m22 X' Y') (hX : X 0 = X' 0) (hY : Y 0 = Y' 0) :
    X = X' ∧ Y = Y' := by
  have key : ∀ t, X t = X' t ∧ Y t = Y' t := by
    intro t
    induction t with
    | zero => exact ⟨hX, hY⟩
    | succ n ih => exact ⟨by rw [(h n).1, (h' n).1, ih.1, ih.2],
        by rw [(h n).2, (h' n).2, ih.1, ih.2]⟩
  exact ⟨funext fun t => (key t).1, funext fun t => (key t).2⟩

theorem bddSeq_lin {X Y : ℕ → ℝ} (hX : BddSeq X) (hY : BddSeq Y) (p q : ℝ) :
    BddSeq (fun t => p * X t + q * Y t) := by
  obtain ⟨M, hM⟩ := hX
  obtain ⟨M', hM'⟩ := hY
  refine ⟨|p| * M + |q| * M', fun t => (abs_add_le _ _).trans (add_le_add ?_ ?_)⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM' t) (abs_nonneg _)

/-- A bounded solution has `s^hi₀ = 0` (the unstable component vanishes). -/
theorem sHi_zero_of_bdd (h1 : cp22 m11 m12 m21 m22 1 < 0) {X Y : ℕ → ℝ}
    (h : IsSol22 m11 m12 m21 m22 X Y) (hX : BddSeq X) (hY : BddSeq Y) :
    sVar m11 m21 (lamHi m11 m12 m21 m22) X Y 0 = 0 := by
  have hhi := (roots22_lt h1).2
  exact (geom_bdd_iff (by rw [abs_of_pos (by linarith)]; exact hhi)
    (fun t => sVar_step (cp22_lamHi h1) (h t).1 (h t).2)).1
    (bddSeq_lin hX hY m21 (lamHi m11 m12 m21 m22 - m11))

/-- The slope of the saddle path, `k = (λ_lo − m₁₁)/m₁₂`. -/
noncomputable def kSaddle (m11 m12 m21 m22 : ℝ) : ℝ :=
  (lamLo m11 m12 m21 m22 - m11) / m12

/-- `s^hi₀ = 0 ⟺ Y₀ = kX₀`: the saddle line. -/
theorem sHi_zero_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21) (X Y : ℕ → ℝ)
    (t : ℕ) : sVar m11 m21 (lamHi m11 m12 m21 m22) X Y t = 0 ↔
      Y t = kSaddle m11 m12 m21 m22 * X t := by
  have hm12 : m12 ≠ 0 := by rintro h; simp [h] at hm
  have hb := lamLo_lt_m11 h1 hm
  have hhi : lamHi m11 m12 m21 m22 - m11 ≠ 0 := by linarith
  have hprod : (lamLo m11 m12 m21 m22 - m11) * (lamHi m11 m12 m21 m22 - m11) = -(m12 * m21) := by
    have := cp22_factor h1 m11
    simp only [cp22] at this
    linarith
  simp only [sVar, kSaddle]
  constructor
  · intro h
    rw [div_mul_eq_mul_div, eq_div_iff hm12]
    have : (lamHi m11 m12 m21 m22 - m11) * (Y t * m12) =
        (lamHi m11 m12 m21 m22 - m11) * ((lamLo m11 m12 m21 m22 - m11) * X t) := by
      linear_combination m12 * h - X t * hprod
    exact mul_left_cancel₀ hhi this
  · intro h
    rw [h]
    field_simp
    linear_combination X t * hprod

/-- The saddle path `X_t = λ_loᵗX₀`, `Y_t = λ_loᵗ k X₀` solves the system. -/
theorem saddle22 (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm12 : m12 ≠ 0) (X0 : ℝ) :
    IsSol22 m11 m12 m21 m22 (fun t => lamLo m11 m12 m21 m22 ^ t * X0)
      (fun t => lamLo m11 m12 m21 m22 ^ t * (kSaddle m11 m12 m21 m22 * X0)) := by
  have hc := cp22_lamLo h1
  intro t
  simp only [kSaddle, cp22, pow_succ] at *
  constructor
  · field_simp; ring
  · field_simp
    linear_combination (lamLo m11 m12 m21 m22 ^ t * X0) * hc

/-- With `|λ_lo| < 1` the saddle path converges to `0`. -/
theorem saddle22_tendsto (h1 : cp22 m11 m12 m21 m22 1 < 0) (hc : 0 < cp22 m11 m12 m21 m22 (-1))
    (X0 : ℝ) : Tendsto (fun t => lamLo m11 m12 m21 m22 ^ t * X0) atTop (𝓝 0) ∧
      Tendsto (fun t => lamLo m11 m12 m21 m22 ^ t * (kSaddle m11 m12 m21 m22 * X0)) atTop
        (𝓝 0) := by
  have hl := (abs_lamLo_lt_one_iff h1).2 hc
  have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl
  exact ⟨by simpa using h.mul_const X0, by simpa using h.mul_const _⟩

/-- A bounded solution lies on the saddle line, so it is the saddle path through its `X₀`. -/
theorem saddle22_unique (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21)
    {X Y : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y) (hX : BddSeq X) (hY : BddSeq Y) :
    X = (fun t => lamLo m11 m12 m21 m22 ^ t * X 0) ∧
      Y = (fun t => lamLo m11 m12 m21 m22 ^ t * (kSaddle m11 m12 m21 m22 * X 0)) := by
  have hm12 : m12 ≠ 0 := by rintro h; simp [h] at hm
  have hY0 := (sHi_zero_iff h1 hm X Y 0).1 (sHi_zero_of_bdd h1 h hX hY)
  exact h.ext (saddle22 h1 hm12 (X 0)) (by simp) (by simp [hY0])

/-- Off the saddle line every solution is unbounded. -/
theorem saddle22_unbounded (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21)
    {X Y : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y) (hoff : Y 0 ≠ kSaddle m11 m12 m21 m22 * X 0) :
    ¬ (BddSeq X ∧ BddSeq Y) := fun ⟨hX, hY⟩ =>
  hoff ((sHi_zero_iff h1 hm X Y 0).1 (sHi_zero_of_bdd h1 h hX hY))

/-- `s` of a solution converging to `0` converges to `0`. -/
theorem sVar_tendsto {X Y : ℕ → ℝ} (l : ℝ) (hX : Tendsto X atTop (𝓝 0))
    (hY : Tendsto Y atTop (𝓝 0)) : Tendsto (sVar m11 m21 l X Y) atTop (𝓝 0) := by
  have := (hX.const_mul m21).add (hY.const_mul (l - m11))
  simp only [mul_zero, add_zero] at this
  exact this

/-- Every `X₀` has a solution converging to the steady state iff `p(−1) > 0` (given `p(1) < 0`
and `m₁₂m₂₁ > 0`). -/
theorem saddle22_iff (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21) :
    (∀ X0, ∃ X Y : ℕ → ℝ, IsSol22 m11 m12 m21 m22 X Y ∧ X 0 = X0 ∧
      Tendsto X atTop (𝓝 0) ∧ Tendsto Y atTop (𝓝 0)) ↔ 0 < cp22 m11 m12 m21 m22 (-1) := by
  have hm12 : m12 ≠ 0 := by rintro h; simp [h] at hm
  have hm21 : m21 ≠ 0 := by rintro h; simp [h] at hm
  constructor
  · intro H
    obtain ⟨X, Y, h, hX0, hX, hY⟩ := H 1
    have hhi0 := sHi_zero_of_bdd h1 h (bddSeq_of_tendsto hX) (bddSeq_of_tendsto hY)
    have hlo0 : sVar m11 m21 (lamLo m11 m12 m21 m22) X Y 0 ≠ 0 := by
      intro h0
      have hlt := lamLo_lt_lamHi h1
      simp only [sVar] at h0 hhi0
      have hY0 : Y 0 = 0 := by
        have : (lamHi m11 m12 m21 m22 - lamLo m11 m12 m21 m22) * Y 0 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left (by linarith)
      rw [hY0, hX0] at h0
      simp only [mul_one, mul_zero, add_zero] at h0
      exact hm21 h0
    have hs := sVar_tendsto (m11 := m11) (m21 := m21) (lamLo m11 m12 m21 m22) hX hY
    have : Tendsto (fun t => lamLo m11 m12 m21 m22 ^ t *
        sVar m11 m21 (lamLo m11 m12 m21 m22) X Y 0) atTop (𝓝 0) :=
      hs.congr (fun t => sVar_succ (cp22_lamLo h1) h t)
    exact (abs_lamLo_lt_one_iff h1).1 ((pow_mul_tendsto_zero_iff hlo0).1 this)
  · intro hc X0
    exact ⟨_, _, saddle22 h1 hm12 X0, by simp, saddle22_tendsto h1 hc X0⟩

/-- If `p(−1) < 0` both roots are unstable and the only bounded solution is `0`. -/
theorem saddle22_only_zero (h1 : cp22 m11 m12 m21 m22 1 < 0) (hm : 0 < m12 * m21)
    (hc : cp22 m11 m12 m21 m22 (-1) < 0) {X Y : ℕ → ℝ} (h : IsSol22 m11 m12 m21 m22 X Y)
    (hX : BddSeq X) (hY : BddSeq Y) : X = 0 ∧ Y = 0 := by
  have hm21 : m21 ≠ 0 := by rintro h; simp [h] at hm
  have hlo : lamLo m11 m12 m21 m22 < -1 := by
    rcases lt_trichotomy (lamLo m11 m12 m21 m22) (-1) with h' | h' | h'
    · exact h'
    · have := cp22_factor h1 (-1)
      rw [h'] at this
      simp at this
      linarith
    · linarith [(lamLo_gt_neg_one_iff h1).1 h']
  have hlo0 : sVar m11 m21 (lamLo m11 m12 m21 m22) X Y 0 = 0 :=
    (geom_bdd_iff (by rw [abs_of_neg (by linarith)]; linarith)
      (fun t => sVar_step (cp22_lamLo h1) (h t).1 (h t).2)).1
      (bddSeq_lin hX hY m21 (lamLo m11 m12 m21 m22 - m11))
  have hhi0 := sHi_zero_of_bdd h1 h hX hY
  have hne := (lamLo_lt_lamHi h1).ne
  have hr := recover22 (m11 := m11) hne hm21 X Y 0
  rw [hlo0, hhi0] at hr
  simp only [mul_zero, zero_div, sub_self] at hr
  exact (h.ext (X' := fun _ => 0) (Y' := fun _ => 0) (fun t => by simp) hr.1 hr.2)

/-! ### The book's phase diagram -/

/-- The system of Miao, p. 27, in terms of `a = ã − 1` and `d = d̃ + 1`:
`x_{t+1} = (1 + a)x_t + b y_t − e`, `y_{t+1} = c x_t + (1 − d)y_t + f`. -/
def IsPhaseSol (a b c d e f : ℝ) (x y : ℕ → ℝ) : Prop :=
  ∀ t, x (t + 1) = (1 + a) * x t + b * y t - e ∧ y (t + 1) = c * x t + (1 - d) * y t + f

/-- Forward iteration of the system from `(x₀, y₀)`. -/
def phaseIter (a b c d e f x0 y0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x0, y0)
  | t + 1 => ((1 + a) * (phaseIter a b c d e f x0 y0 t).1 + b * (phaseIter a b c d e f x0 y0 t).2
      - e, c * (phaseIter a b c d e f x0 y0 t).1 + (1 - d) * (phaseIter a b c d e f x0 y0 t).2 + f)

theorem phaseIter_sol {a b c d e f x0 y0 : ℝ} :
    IsPhaseSol a b c d e f (fun t => (phaseIter a b c d e f x0 y0 t).1)
      (fun t => (phaseIter a b c d e f x0 y0 t).2) := fun _ => ⟨rfl, rfl⟩

/-- Miao, p. 27: the system `x_{t+1} = ãx_t + by_t − e`, `y_{t+1} = cx_t − d̃y_t + f` is
`IsPhaseSol` with `a = ã − 1`, `d = d̃ + 1`. -/
theorem phase_tilde (at' b c dt e f : ℝ) (x y : ℕ → ℝ) :
    (∀ t, x (t + 1) = at' * x t + b * y t - e ∧ y (t + 1) = c * x t - dt * y t + f) ↔
      IsPhaseSol (at' - 1) b c (dt + 1) e f x y := by
  simp only [IsPhaseSol]
  constructor <;> intro h t <;> constructor <;> linarith [(h t).1, (h t).2]

/-- Miao, p. 27: `Δx_t = ax_t + by_t − e` and `Δy_t = cx_t − dy_t + f`. -/
theorem phase_delta {a b c d e f : ℝ} {x y : ℕ → ℝ} (h : IsPhaseSol a b c d e f x y) (t : ℕ) :
    x (t + 1) - x t = a * x t + b * y t - e ∧ y (t + 1) - y t = c * x t - d * y t + f := by
  rw [(h t).1, (h t).2]
  constructor <;> ring

/-- Miao, p. 28: for `b > 0`, `Δx ≥ 0 ⟺ y ≥ −(a/b)x + e/b` (and strictly). -/
theorem phase_isocline_x {a b e : ℝ} (hb : 0 < b) (x y : ℝ) :
    (0 ≤ a * x + b * y - e ↔ -(a / b) * x + e / b ≤ y) ∧
      (0 < a * x + b * y - e ↔ -(a / b) * x + e / b < y) := by
  have : -(a / b) * x + e / b = (e - a * x) / b := by field_simp; ring
  rw [this, div_le_iff₀ hb, div_lt_iff₀ hb]
  constructor <;> constructor <;> intro h <;> linarith

/-- Miao, p. 28: for `d > 0`, `Δy ≥ 0 ⟺ y ≤ (c/d)x + f/d` (and strictly). -/
theorem phase_isocline_y {c d f : ℝ} (hd : 0 < d) (x y : ℝ) :
    (0 ≤ c * x - d * y + f ↔ y ≤ c / d * x + f / d) ∧
      (0 < c * x - d * y + f ↔ y < c / d * x + f / d) := by
  have : c / d * x + f / d = (c * x + f) / d := by field_simp
  rw [this, le_div_iff₀ hd, lt_div_iff₀ hd]
  constructor <;> constructor <;> intro h <;> linarith

/-- Miao, p. 28: for `a, b, c, d > 0` the steady state is unique:
`x̄ = (ed − bf)/(ad + bc)`, `ȳ = (af + ce)/(ad + bc)`. -/
theorem phase_steady_state {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (xb yb : ℝ) :
    IsPhaseSol a b c d e f (fun _ => xb) (fun _ => yb) ↔
      xb = (e * d - b * f) / (a * d + b * c) ∧ yb = (a * f + c * e) / (a * d + b * c) := by
  have hD : 0 < a * d + b * c := by positivity
  simp only [IsPhaseSol]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h 0
    constructor <;> rw [eq_div_iff hD.ne'] <;> nlinarith
  · rintro ⟨rfl, rfl⟩ _
    constructor <;> field_simp <;> ring

theorem bddSeq_sub_const {x : ℕ → ℝ} (hx : BddSeq x) (k : ℝ) : BddSeq (fun t => x t - k) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨M + |k|, fun t => (abs_sub _ _).trans (add_le_add (hM t) le_rfl)⟩

/-- Deviations from a steady state `(x̄, ȳ)` solve the homogeneous system with matrix
`[[1 + a, b], [c, 1 − d]]`. -/
theorem phase_dev {a b c d e f xb yb : ℝ} {x y : ℕ → ℝ}
    (hss : IsPhaseSol a b c d e f (fun _ => xb) (fun _ => yb)) (h : IsPhaseSol a b c d e f x y) :
    IsSol22 (1 + a) b c (1 - d) (fun t => x t - xb) (fun t => y t - yb) := by
  intro t
  obtain ⟨h1, h2⟩ := h t
  obtain ⟨s1, s2⟩ := hss 0
  constructor
  · simp only; rw [h1]; linear_combination (-1 : ℝ) * s1
  · simp only; rw [h2]; linear_combination (-1 : ℝ) * s2

theorem phase_cp_one {a b c d : ℝ} : cp22 (1 + a) b c (1 - d) 1 = -(a * d) - b * c := by
  simp only [cp22]; ring

theorem phase_cp_neg_one {a b c d : ℝ} :
    cp22 (1 + a) b c (1 - d) (-1) = (2 + a) * (2 - d) - b * c := by
  simp only [cp22]; ring

/-- Miao, p. 28: the coefficient matrix `[[1 + a, b], [c, 1 − d]]` has two real roots, one
below and one above `1`. -/
theorem phase_roots {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    cp22 (1 + a) b c (1 - d) 1 < 0 ∧ lamLo (1 + a) b c (1 - d) < 1 ∧
      1 < lamHi (1 + a) b c (1 - d) := by
  have h1 : cp22 (1 + a) b c (1 - d) 1 < 0 := by rw [phase_cp_one]; nlinarith [mul_pos ha hd]
  exact ⟨h1, roots22_lt h1⟩

/-- **Correction** (Miao, p. 28): the smaller root lies in `(−1, 1)` iff
`(2 + a)(2 − d) > bc`. -/
theorem phase_lamLo_iff {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    |lamLo (1 + a) b c (1 - d)| < 1 ↔ b * c < (2 + a) * (2 - d) := by
  rw [abs_lamLo_lt_one_iff (phase_roots ha hb hc hd).1, phase_cp_neg_one, sub_pos]

/-- **Saddle path** (Miao, p. 28, corrected): if `(2 + a)(2 − d) > bc`, for every `x₀` the path
starting at `y₀ = ȳ + k(x₀ − x̄)`, `k = (λ_lo − 1 − a)/b`, converges to the steady state; every
bounded path is of this form; every other path is unbounded. -/
theorem phase_saddle {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcond : b * c < (2 + a) * (2 - d)) (x0 : ℝ) :
    (∃ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y ∧ x 0 = x0 ∧
      Tendsto x atTop (𝓝 ((e * d - b * f) / (a * d + b * c))) ∧
      Tendsto y atTop (𝓝 ((a * f + c * e) / (a * d + b * c)))) ∧
    ∀ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y →
      ((BddSeq x ∧ BddSeq y) ↔ y 0 - (a * f + c * e) / (a * d + b * c) =
        kSaddle (1 + a) b c (1 - d) * (x 0 - (e * d - b * f) / (a * d + b * c))) := by
  set xb := (e * d - b * f) / (a * d + b * c)
  set yb := (a * f + c * e) / (a * d + b * c)
  have h1 := (phase_roots ha hb hc hd).1
  have hm : 0 < b * c := mul_pos hb hc
  have hc1 : 0 < cp22 (1 + a) b c (1 - d) (-1) := by rw [phase_cp_neg_one]; linarith
  have hss : IsPhaseSol a b c d e f (fun _ => xb) (fun _ => yb) :=
    (phase_steady_state ha hb hc hd _ _).2 ⟨rfl, rfl⟩
  have hdevB : ∀ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y →
      y 0 - yb = kSaddle (1 + a) b c (1 - d) * (x 0 - xb) →
      Tendsto x atTop (𝓝 xb) ∧ Tendsto y atTop (𝓝 yb) := by
    intro x y h hk
    have hdev := phase_dev hss h
    obtain ⟨hX, hY⟩ := hdev.ext (saddle22 h1 hb.ne' (x 0 - xb)) (by simp) (by simpa using hk)
    obtain ⟨t1, t2⟩ := saddle22_tendsto h1 hc1 (x 0 - xb)
    rw [← hX] at t1
    rw [← hY] at t2
    exact ⟨by simpa using t1.add_const xb, by simpa using t2.add_const yb⟩
  refine ⟨?_, fun x y h => ⟨fun ⟨hx, hy⟩ => ?_, fun hk => ?_⟩⟩
  · obtain ⟨x, y, hxy⟩ : ∃ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y ∧ x 0 = x0 ∧
        y 0 = yb + kSaddle (1 + a) b c (1 - d) * (x0 - xb) :=
      ⟨fun t => (phaseIter a b c d e f x0 (yb + kSaddle (1 + a) b c (1 - d) * (x0 - xb)) t).1,
        fun t => (phaseIter a b c d e f x0 (yb + kSaddle (1 + a) b c (1 - d) * (x0 - xb)) t).2,
        phaseIter_sol, rfl, rfl⟩
    obtain ⟨h, hx0, hy0⟩ := hxy
    refine ⟨x, y, h, hx0, hdevB x y h (by rw [hy0, hx0]; ring)⟩
  · have h0 := sHi_zero_of_bdd h1 (phase_dev hss h) (bddSeq_sub_const hx xb)
      (bddSeq_sub_const hy yb)
    exact (sHi_zero_iff h1 hm _ _ 0).1 h0
  · obtain ⟨t1, t2⟩ := hdevB x y h hk
    exact ⟨bddSeq_of_tendsto t1, bddSeq_of_tendsto t2⟩

/-- Miao, p. 28 (Figure 1.4): the saddle path `y − ȳ = k(x − x̄)` slopes down, more steeply
than the isocline `Δx = 0` (slope `−a/b`): `k < −a/b < 0`. -/
theorem phase_saddle_slope {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    kSaddle (1 + a) b c (1 - d) < -(a / b) ∧ -(a / b) < 0 := by
  have hlo := (phase_roots ha hb hc hd).2.1
  simp only [kSaddle]
  refine ⟨?_, by have := div_pos ha hb; linarith⟩
  rw [div_lt_iff₀ hb]
  have : -(a / b) * b = -a := by field_simp
  linarith

/-- **Correction** (Miao, p. 28): every `x₀` has a path converging to the steady state iff
`(2 + a)(2 − d) > bc`. -/
theorem phase_saddle_iff {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    (∀ x0, ∃ x y : ℕ → ℝ, IsPhaseSol a b c d e f x y ∧ x 0 = x0 ∧
      Tendsto x atTop (𝓝 ((e * d - b * f) / (a * d + b * c))) ∧
      Tendsto y atTop (𝓝 ((a * f + c * e) / (a * d + b * c)))) ↔
      b * c < (2 + a) * (2 - d) := by
  constructor
  · intro H
    have h1 := (phase_roots ha hb hc hd).1
    have hss : IsPhaseSol a b c d e f (fun _ => (e * d - b * f) / (a * d + b * c))
        (fun _ => (a * f + c * e) / (a * d + b * c)) :=
      (phase_steady_state ha hb hc hd _ _).2 ⟨rfl, rfl⟩
    have := (saddle22_iff h1 (mul_pos hb hc)).1 (fun X0 => by
      obtain ⟨x, y, h, hx0, hx, hy⟩ := H (X0 + (e * d - b * f) / (a * d + b * c))
      exact ⟨_, _, phase_dev hss h, by simp [hx0],
        by simpa using hx.sub_const ((e * d - b * f) / (a * d + b * c)),
        by simpa using hy.sub_const ((a * f + c * e) / (a * d + b * c))⟩)
    rwa [phase_cp_neg_one, sub_pos] at this
  · intro hcond x0
    exact (phase_saddle (e := e) (f := f) ha hb hc hd hcond x0).1

/-- **Counterexample** (Miao, p. 28): for `a = b = c = e = f = 1`, `d = 3` one has
`(2 + a)(2 − d) = −3 < 1 = bc`; both roots are unstable (`λ_lo < −1`, `λ_hi > 1`), and the
steady state `(1/2, 1/2)` is the only bounded path: no convergent saddle path exists. -/
theorem phase_counterexample :
    lamLo (1 + 1) 1 1 (1 - 3) < -1 ∧ 1 < lamHi (1 + 1) 1 1 (1 - 3) ∧
      ∀ x y : ℕ → ℝ, IsPhaseSol 1 1 1 3 1 1 x y → BddSeq x → BddSeq y →
        x = (fun _ => 1 / 2) ∧ y = (fun _ => 1 / 2) := by
  have h1 : cp22 (1 + 1) 1 1 (1 - 3) 1 < 0 := by rw [phase_cp_one]; norm_num
  have hc : cp22 (1 + 1) 1 1 (1 - 3) (-1) < 0 := by rw [phase_cp_neg_one]; norm_num
  refine ⟨?_, (roots22_lt h1).2, fun x y h hx hy => ?_⟩
  · by_contra hlo
    push Not at hlo
    rcases hlo.lt_or_eq with hlt | heq
    · linarith [(lamLo_gt_neg_one_iff h1).1 hlt]
    · have := cp22_factor h1 (-1)
      rw [← heq] at this
      simp at this
      linarith
  · have hss : IsPhaseSol 1 1 1 3 1 1 (fun _ => 1 / 2) (fun _ => 1 / 2) := by
      intro t; constructor <;> norm_num
    obtain ⟨hX, hY⟩ := saddle22_only_zero h1 (by norm_num) hc (phase_dev hss h)
      (bddSeq_sub_const hx _) (bddSeq_sub_const hy _)
    constructor
    · ext t; have := congrFun hX t; simp only [Pi.zero_apply] at this; linarith
    · ext t; have := congrFun hY t; simp only [Pi.zero_apply] at this; linarith

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Preferences of the Samuelson (1958) exchange economy

Miao, §16.1, p. 530: a generation-`t` agent has utility `u(c_t^t) + βu(c_{t+1}^t)` with
`β ∈ (0, 1]`, `u' > 0`, `u'' < 0` and `lim_{c→0} u'(c) = ∞`.

* `OXPrefs`: the period utility `u` and its derivative `u'` (field `ox_du`) on `(0, ∞)`,
  `u' > 0`, `u'` strictly decreasing (the content of `u'' < 0` used in §16.1), `u'`
  continuous, and the Inada condition. The concrete instance `ox_logPrefs` (`u = ln`) shows the
  hypotheses are satisfiable.
* Concavity consequences used throughout the section: the (strict) tangent-line inequality
  (`ox_tangent`, `ox_tangent_strict`), strict monotonicity of `u` (`ox_u_strictMonoOn`), a
  uniform chord bound (`ox_chord`), the first-order condition at a local maximum along a budget
  line (`ox_foc`), and sufficiency of the Euler equation on a budget line (`ox_line_optimal`,
  `ox_line_optimal_strict`).

**Departure.** Utility is defined on `(0, ∞)`: consumption is required to be positive
throughout the chapter (with the Inada condition zero consumption is never chosen).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, §16.1, p. 530: period utility `u` with derivative `u'` on `(0, ∞)`, `u' > 0`, `u'`
strictly decreasing (from `u'' < 0`), `u'` continuous, `lim_{c → 0} u'(c) = ∞`, and the discount
factor `β ∈ (0, 1]`. -/
structure OXPrefs where
  /-- The period utility `u`. -/
  ox_u : ℝ → ℝ
  /-- Its derivative `u'`. -/
  ox_du : ℝ → ℝ
  /-- The discount factor. -/
  ox_β : ℝ
  ox_β_pos : 0 < ox_β
  ox_β_le : ox_β ≤ 1
  ox_hasDeriv : ∀ c, 0 < c → HasDerivAt ox_u (ox_du c) c
  ox_du_pos : ∀ c, 0 < c → 0 < ox_du c
  ox_du_anti : StrictAntiOn ox_du (Set.Ioi 0)
  ox_du_cont : ContinuousOn ox_du (Set.Ioi 0)
  ox_inada : Tendsto ox_du (𝓝[>] 0) atTop

/-- Logarithmic utility `u = ln`, `u'(c) = 1/c`: a concrete instance of `OXPrefs`. -/
noncomputable def ox_logPrefs (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) : OXPrefs where
  ox_u := Real.log
  ox_du := fun c => c⁻¹
  ox_β := β
  ox_β_pos := hβ
  ox_β_le := hβ1
  ox_hasDeriv := fun _ hc => Real.hasDerivAt_log hc.ne'
  ox_du_pos := fun _ hc => inv_pos.2 hc
  ox_du_anti := fun _ hx _ _ hxy => inv_strictAnti₀ (Set.mem_Ioi.1 hx) hxy
  ox_du_cont := continuousOn_inv₀.mono fun _ hx => (Set.mem_Ioi.1 hx).ne'
  ox_inada := tendsto_inv_nhdsGT_zero

/-- Miao, p. 530: the logarithmic instance has `u = ln` and `u'(c) = 1/c`. -/
theorem ox_logPrefs_spec (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (ox_logPrefs β hβ hβ1).ox_u = Real.log ∧ (ox_logPrefs β hβ hβ1).ox_du = (fun c => c⁻¹) ∧
      (ox_logPrefs β hβ hβ1).ox_β = β :=
  ⟨rfl, rfl, rfl⟩

namespace OXPrefs

variable (P : OXPrefs)

/-- Lifetime utility `u(c₁) + βu(c₂)` of a two-period-lived agent (Miao, p. 530). -/
def ox_U (c1 c2 : ℝ) : ℝ := P.ox_u c1 + P.ox_β * P.ox_u c2

/-- Strict concavity of `u` (Miao, p. 530, `u'' < 0`): for `x, y > 0`, `y ≠ x`,
`u(y) < u(x) + u'(x)(y − x)`. -/
theorem ox_tangent_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : y ≠ x) :
    P.ox_u y < P.ox_u x + P.ox_du x * (y - x) := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope P.ox_u P.ox_du hlt
      (fun z hz => (P.ox_hasDeriv z (by linarith [hz.1])).continuousAt.continuousWithinAt)
      (fun z hz => P.ox_hasDeriv z (by linarith [hz.1]))
    have hc0 : 0 < c := by linarith [hc.1]
    have hdu : P.ox_du x < P.ox_du c := P.ox_du_anti hc0 hx hc.2
    have hxy : 0 < x - y := by linarith
    rw [eq_div_iff hxy.ne'] at hcd
    nlinarith
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope P.ox_u P.ox_du hlt
      (fun z hz => (P.ox_hasDeriv z (by linarith [hz.1])).continuousAt.continuousWithinAt)
      (fun z hz => P.ox_hasDeriv z (by linarith [hz.1]))
    have hc0 : 0 < c := by linarith [hc.1]
    have hdu : P.ox_du c < P.ox_du x := P.ox_du_anti hx hc0 hc.1
    have hxy : 0 < y - x := by linarith
    rw [eq_div_iff hxy.ne'] at hcd
    nlinarith

/-- Concavity of `u`: `u(y) ≤ u(x) + u'(x)(y − x)` for `x, y > 0`. -/
theorem ox_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    P.ox_u y ≤ P.ox_u x + P.ox_du x * (y - x) := by
  rcases eq_or_ne y x with h | h
  · subst h; simp
  · exact (P.ox_tangent_strict hx hy h).le

/-- `u' > 0`: `u` is strictly increasing on `(0, ∞)`. -/
theorem ox_u_strictMonoOn : StrictMonoOn P.ox_u (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h := P.ox_tangent_strict (Set.mem_Ioi.1 hy) (Set.mem_Ioi.1 hx) hxy.ne
  have hd := P.ox_du_pos y (Set.mem_Ioi.1 hy)
  nlinarith

/-- `u` strictly increasing, in the form used for consumption comparisons. -/
theorem ox_u_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) : P.ox_u x < P.ox_u y :=
  P.ox_u_strictMonoOn hx (show (0 : ℝ) < y by linarith) hxy

/-- `u'` strictly decreasing, in the form used for marginal-utility comparisons. -/
theorem ox_du_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) : P.ox_du y < P.ox_du x :=
  P.ox_du_anti hx (show (0 : ℝ) < y by linarith) hxy

/-- A uniform chord bound from strict concavity: for `0 < ε₀ < c` there is `κ > u'(c)` with
`u(c) − u(c − ε) ≥ κε` for every `ε ∈ [ε₀, c)`. -/
theorem ox_chord {c ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀c : ε₀ < c) :
    ∃ κ, P.ox_du c < κ ∧ ∀ ε, ε₀ ≤ ε → ε < c → κ * ε ≤ P.ox_u c - P.ox_u (c - ε) := by
  have hc : 0 < c := by linarith
  have hc0 : 0 < c - ε₀ := by linarith
  set a := P.ox_du (c - ε₀)
  set D := P.ox_u c - P.ox_u (c - ε₀)
  have ha : P.ox_du c < a := P.ox_du_lt hc0 (by linarith)
  have hD : P.ox_du c * ε₀ < D := by
    have := P.ox_tangent_strict hc hc0 (by linarith)
    simp only [D]; nlinarith
  refine ⟨min (D / ε₀) a, lt_min ((lt_div_iff₀ hε₀).2 hD) ha, fun ε hε hεc => ?_⟩
  have hce : 0 < c - ε := by linarith
  have ht := P.ox_tangent hc0 hce
  have h1 : min (D / ε₀) a * ε₀ ≤ D := by
    have := min_le_left (D / ε₀) a
    calc min (D / ε₀) a * ε₀ ≤ D / ε₀ * ε₀ := mul_le_mul_of_nonneg_right this hε₀.le
      _ = D := div_mul_cancel₀ D hε₀.ne'
  have h2 : min (D / ε₀) a * (ε - ε₀) ≤ a * (ε - ε₀) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
  have : P.ox_u (c - ε) ≤ P.ox_u (c - ε₀) - a * (ε - ε₀) := by
    have : c - ε - (c - ε₀) = -(ε - ε₀) := by ring
    rw [this] at ht; linarith
  nlinarith

/-- Positivity of an affine function near `0`: if `0 < a` then `0 < a + bs` for `s` near `0`. -/
theorem ox_eventually_pos (a b : ℝ) (ha : 0 < a) : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < a + b * s := by
  have : Tendsto (fun s : ℝ => a + b * s) (𝓝 0) (𝓝 (a + b * 0)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).tendsto 0)
  rw [mul_zero, add_zero] at this
  exact this.eventually (lt_mem_nhds ha)

/-- The first-order condition along a budget line: if moving `s` units along the line
`(c₁ − as, c₂ + bs)` never raises utility for `s` near `0`, then `a u'(c₁) = βb u'(c₂)`. -/
theorem ox_foc {c1 c2 a b : ℝ} (h1 : 0 < c1) (h2 : 0 < c2)
    (hmax : ∀ᶠ s in 𝓝 (0 : ℝ), P.ox_U (c1 - a * s) (c2 + b * s) ≤ P.ox_U c1 c2) :
    a * P.ox_du c1 = P.ox_β * b * P.ox_du c2 := by
  have hl1 : HasDerivAt (fun s : ℝ => c1 - a * s) (-a) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a |>.const_sub c1
  have hl2 : HasDerivAt (fun s : ℝ => c2 + b * s) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul b).const_add c2
  have hu1 : HasDerivAt P.ox_u (P.ox_du c1) ((fun s : ℝ => c1 - a * s) 0) := by
    simpa using P.ox_hasDeriv c1 h1
  have hu2 : HasDerivAt P.ox_u (P.ox_du c2) ((fun s : ℝ => c2 + b * s) 0) := by
    simpa using P.ox_hasDeriv c2 h2
  have hphi : HasDerivAt (fun s => P.ox_U (c1 - a * s) (c2 + b * s))
      (P.ox_du c1 * -a + P.ox_β * (P.ox_du c2 * b)) 0 :=
    (hu1.comp 0 hl1).add ((hu2.comp 0 hl2).const_mul P.ox_β)
  have hloc : IsLocalMax (fun s => P.ox_U (c1 - a * s) (c2 + b * s)) 0 := by
    filter_upwards [hmax] with s hs
    simpa using hs
  have := hloc.hasDerivAt_eq_zero hphi
  linarith

/-- Sufficiency of the Euler equation (Miao, (16.4)): if `u'(c₁) = βRu'(c₂)` then `(c₁, c₂)`
maximises `u(c₁') + βu(c₂')` over the budget line `c₁' + c₂'/R ≤ c₁ + c₂/R`. -/
theorem ox_line_optimal {c1 c2 R c1' c2' : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (hR : 0 < R)
    (heul : P.ox_du c1 = P.ox_β * R * P.ox_du c2) (h1' : 0 < c1') (h2' : 0 < c2')
    (hline : c1' + c2' / R ≤ c1 + c2 / R) : P.ox_U c1' c2' ≤ P.ox_U c1 c2 := by
  have t1 := P.ox_tangent h1 h1'
  have t2 := mul_le_mul_of_nonneg_left (P.ox_tangent h2 h2') P.ox_β_pos.le
  have hK : R * ((c1' + c2' / R) - (c1 + c2 / R)) = R * (c1' - c1) + (c2' - c2) := by
    field_simp; ring
  have hpos : 0 ≤ P.ox_β * P.ox_du c2 := (mul_pos P.ox_β_pos (P.ox_du_pos c2 h2)).le
  have hneg : P.ox_β * P.ox_du c2 * (R * (c1' - c1) + (c2' - c2)) ≤ 0 := by
    rw [← hK]
    exact mul_nonpos_of_nonneg_of_nonpos hpos
      (mul_nonpos_of_nonneg_of_nonpos hR.le (by linarith))
  rw [heul] at t1
  unfold ox_U
  nlinarith

/-- The strict version of `ox_line_optimal`: any other point of the budget set is strictly
worse. -/
theorem ox_line_optimal_strict {c1 c2 R c1' c2' : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (hR : 0 < R)
    (heul : P.ox_du c1 = P.ox_β * R * P.ox_du c2) (h1' : 0 < c1') (h2' : 0 < c2')
    (hline : c1' + c2' / R ≤ c1 + c2 / R) (hne : c1' ≠ c1 ∨ c2' ≠ c2) :
    P.ox_U c1' c2' < P.ox_U c1 c2 := by
  have hK : R * ((c1' + c2' / R) - (c1 + c2 / R)) = R * (c1' - c1) + (c2' - c2) := by
    field_simp; ring
  have hpos : 0 < P.ox_β * P.ox_du c2 := mul_pos P.ox_β_pos (P.ox_du_pos c2 h2)
  have hneg : P.ox_β * P.ox_du c2 * (R * (c1' - c1) + (c2' - c2)) ≤ 0 := by
    rw [← hK]
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le
      (mul_nonpos_of_nonneg_of_nonpos hR.le (by linarith))
  unfold ox_U
  rcases hne with hne | hne
  · have t1 := P.ox_tangent_strict h1 h1' hne
    have t2 := mul_le_mul_of_nonneg_left (P.ox_tangent h2 h2') P.ox_β_pos.le
    rw [heul] at t1
    nlinarith
  · have t1 := P.ox_tangent h1 h1'
    have t2 := mul_lt_mul_of_pos_left (P.ox_tangent_strict h2 h2' hne) P.ox_β_pos
    rw [heul] at t1
    nlinarith

end OXPrefs

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Samuelson (1958) exchange economy with fiat money

Miao, §16.1, pp. 530–532: two-period-lived agents, `N_t = g_n N_{t−1}` young at `t`, endowments
`(e₁, e₂)`, money supply `M_t = g_m M_{t−1}` distributed as lump-sum transfers to the old.

* `OXEconomy`: the primitives (`OXPrefs`, `e₁, e₂, g_n, g_m, N₀, M₀ > 0`); `ox_N`, `ox_M`.
* The value of money `q_t = 1/p_t ≥ 0` (`q_t = 0` is the book's `p_t = ∞`). Budget sets
  (16.1)–(16.2) (`ox_Budget`, `eq_16_1_16_2` in the book's price form), optimal choices
  (`ox_Optimal`), the initial old (`ox_OldOptimal`, `ox_oldOptimal_iff`), equilibrium with the
  market-clearing conditions (16.3) (`ox_IsEquilibrium`), monetary and nonmonetary equilibria.
* Autarky is the unique nonmonetary equilibrium (`ox_autarky_isEquilibrium`,
  `ox_nonmonetary_autarky`).
* The Euler equation (16.4) (`eq_16_4`), the autarky interest rate (16.5) (`ox_Raut`,
  `eq_16_5`: the unique gross rate at which `(e₁, e₂)` is optimal), equilibrium consumption
  `c_t^t = e₁ − m̂_t`, `c_{t+1}^t = e₂ + g_n m̂_{t+1}` and (16.6) (`ox_monetary_alloc`,
  `eq_16_6`), (16.7) (`eq_16_7`).
* The equilibrium difference equation in saving: every sequence `m̂_t ∈ (0, e₁)` solving
  `u'(e₁ − m̂_t) = β(g_n m̂_{t+1}/(g_m m̂_t))u'(e₂ + g_n m̂_{t+1})` is a monetary equilibrium
  (`ox_ofSaving_isMonetary`), and every monetary equilibrium arises this way.

**Departures.** (i) The initial old's budget is printed with `y₂`; it is `e₂`. (ii) In a
nonmonetary equilibrium money holdings are indeterminate (money has no value); we let the young
hold the money stock so that `M_t = N_t m_t^t` still holds, where the book writes `m_t^t = 0`.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, §16.1, pp. 530–531: the primitives of the Samuelson exchange economy. -/
structure OXEconomy where
  /-- Preferences. -/
  ox_P : OXPrefs
  /-- Endowment of the young. -/
  ox_e1 : ℝ
  /-- Endowment of the old. -/
  ox_e2 : ℝ
  /-- Population growth factor `g_n`. -/
  ox_gn : ℝ
  /-- Money growth factor `g_m`. -/
  ox_gm : ℝ
  /-- Initial old population `N₀`. -/
  ox_N0 : ℝ
  /-- Initial money stock `M₀ = N₀ m₀⁰`. -/
  ox_M0 : ℝ
  ox_e1_pos : 0 < ox_e1
  ox_e2_pos : 0 < ox_e2
  ox_gn_pos : 0 < ox_gn
  ox_gm_pos : 0 < ox_gm
  ox_N0_pos : 0 < ox_N0
  ox_M0_pos : 0 < ox_M0

/-- A concrete economy (log utility, `β = 1`, `e = (2, 1)`, `g_n = g_m = N₀ = M₀ = 1`): the
hypotheses of `OXEconomy` are satisfiable. -/
noncomputable def ox_exampleEconomy : OXEconomy where
  ox_P := ox_logPrefs 1 one_pos le_rfl
  ox_e1 := 2
  ox_e2 := 1
  ox_gn := 1
  ox_gm := 1
  ox_N0 := 1
  ox_M0 := 1
  ox_e1_pos := two_pos
  ox_e2_pos := one_pos
  ox_gn_pos := one_pos
  ox_gm_pos := one_pos
  ox_N0_pos := one_pos
  ox_M0_pos := one_pos

/-- The example economy has `e₁ = 2`, `e₂ = 1`. -/
theorem ox_exampleEconomy_spec : ox_exampleEconomy.ox_e1 = 2 ∧ ox_exampleEconomy.ox_e2 = 1 :=
  ⟨rfl, rfl⟩

namespace OXEconomy

variable (E : OXEconomy)

/-- Population of generation `t`: `N_t = N₀ g_nᵗ`. -/
def ox_N (t : ℕ) : ℝ := E.ox_N0 * E.ox_gn ^ t

/-- Money stock after the date-`t` transfer: `M_t = M₀ g_mᵗ`. -/
def ox_M (t : ℕ) : ℝ := E.ox_M0 * E.ox_gm ^ t

/-- The per-capita transfer to an old agent of generation `t` (in money): `(g_m − 1)M_t/N_t`. -/
noncomputable def ox_τ (t : ℕ) : ℝ := (E.ox_gm - 1) * E.ox_M t / E.ox_N t

/-- Lifetime utility. -/
def ox_EU (c1 c2 : ℝ) : ℝ := E.ox_P.ox_U c1 c2

/-- Miao, (16.5), p. 531: the autarky interest rate `R_aut = u'(e₁)/(βu'(e₂))`. -/
noncomputable def ox_Raut : ℝ := E.ox_P.ox_du E.ox_e1 / (E.ox_P.ox_β * E.ox_P.ox_du E.ox_e2)

/-- Miao, (16.1)–(16.2), p. 531, with `q_t = 1/p_t` the value of money: the budget set of a
young agent of generation `t ≥ 1` (consumption positive). -/
def ox_Budget (q : ℕ → ℝ) (t : ℕ) (c1 c2 m : ℝ) : Prop :=
  0 ≤ m ∧ 0 < c1 ∧ 0 < c2 ∧ c1 + q t * m ≤ E.ox_e1 ∧
    c2 ≤ E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t

/-- Optimal choice of generation `t`: in the budget set and utility-maximal there. -/
def ox_Optimal (q : ℕ → ℝ) (t : ℕ) (c1 c2 m : ℝ) : Prop :=
  E.ox_Budget q t c1 c2 m ∧
    ∀ c1' c2' m', E.ox_Budget q t c1' c2' m' → E.ox_EU c1' c2' ≤ E.ox_EU c1 c2

/-- Miao, p. 531: the initial old's resources `e₂ + m₀⁰/p₁ + (g_m − 1)M₀/(N₀p₁)`. -/
noncomputable def ox_oldBudget (q : ℕ → ℝ) : ℝ :=
  E.ox_e2 + q 1 * (E.ox_M0 / E.ox_N0) + q 1 * ((E.ox_gm - 1) * E.ox_M0 / E.ox_N0)

/-- The initial old maximise `u(c₁⁰)` subject to their budget. -/
def ox_OldOptimal (q : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ c ≤ E.ox_oldBudget q ∧
    ∀ c', 0 < c' → c' ≤ E.ox_oldBudget q → E.ox_P.ox_u c' ≤ E.ox_P.ox_u c

/-- Miao, p. 531: an equilibrium. `q_t ≥ 0` is the value of money at `t ≥ 1`, `cy t = c_t^t`,
`co t = c_{t+1}^t` (so `co 0 = c₁⁰` is the initial old's consumption), `m t = m_t^t`. Every
generation optimises, money and goods markets clear (16.3). -/
def ox_IsEquilibrium (q cy co m : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 ≤ q t) ∧ (∀ t, 1 ≤ t → E.ox_Optimal q t (cy t) (co t) (m t)) ∧
    E.ox_OldOptimal q (co 0) ∧ (∀ t, 1 ≤ t → E.ox_M t = E.ox_N t * m t) ∧
    ∀ t, 1 ≤ t → E.ox_N t * cy t + E.ox_N (t - 1) * co (t - 1) =
      E.ox_N t * E.ox_e1 + E.ox_N (t - 1) * E.ox_e2

/-- Miao, p. 531: a monetary equilibrium (finite positive prices: `q_t > 0` for all `t ≥ 1`). -/
def ox_IsMonetary (q cy co m : ℕ → ℝ) : Prop :=
  E.ox_IsEquilibrium q cy co m ∧ ∀ t, 1 ≤ t → 0 < q t

/-- Miao, p. 531: a nonmonetary equilibrium (`p_t = ∞`, i.e. `q_t = 0`). -/
def ox_IsNonmonetary (q cy co m : ℕ → ℝ) : Prop :=
  E.ox_IsEquilibrium q cy co m ∧ ∀ t, 1 ≤ t → q t = 0

/-- Miao, p. 532: real balances per young `m̂_t = M_t/(N_t p_t) = q_t M_t/N_t`. -/
noncomputable def ox_mhat (q : ℕ → ℝ) (t : ℕ) : ℝ := q t * E.ox_M t / E.ox_N t

theorem ox_N_pos (t : ℕ) : 0 < E.ox_N t := mul_pos E.ox_N0_pos (pow_pos E.ox_gn_pos t)

theorem ox_M_pos (t : ℕ) : 0 < E.ox_M t := mul_pos E.ox_M0_pos (pow_pos E.ox_gm_pos t)

theorem ox_N_succ (t : ℕ) : E.ox_N (t + 1) = E.ox_N t * E.ox_gn := by
  simp only [ox_N, pow_succ]; ring

theorem ox_M_succ (t : ℕ) : E.ox_M (t + 1) = E.ox_M t * E.ox_gm := by
  simp only [ox_M, pow_succ]; ring

/-- Miao, (16.1)–(16.2), p. 531: in the book's price notation `p_t = 1/q_t > 0`, the budget set
is `c_t^t + m_t^t/p_t ≤ e₁`, `c_{t+1}^t ≤ e₂ + m_t^t/p_{t+1} + (g_m − 1)M_t/(N_t p_{t+1})`. -/
theorem eq_16_1_16_2 (p : ℕ → ℝ) (t : ℕ) (c1 c2 m : ℝ) :
    E.ox_Budget (fun s => 1 / p s) t c1 c2 m ↔
      0 ≤ m ∧ 0 < c1 ∧ 0 < c2 ∧ c1 + m / p t ≤ E.ox_e1 ∧
        c2 ≤ E.ox_e2 + m / p (t + 1) + (E.ox_gm - 1) * E.ox_M t / (E.ox_N t * p (t + 1)) := by
  unfold ox_Budget ox_τ
  have h1 : 1 / p t * m = m / p t := by ring
  have h2 : 1 / p (t + 1) * m = m / p (t + 1) := by ring
  have h3 : 1 / p (t + 1) * ((E.ox_gm - 1) * E.ox_M t / E.ox_N t) =
      (E.ox_gm - 1) * E.ox_M t / (E.ox_N t * p (t + 1)) := by
    rw [div_mul_div_comm, one_mul, mul_comm (p (t + 1))]
  rw [h1, h2, h3]

/-- Miao, p. 531: since `u` is strictly increasing, the initial old consume their resources:
`c₁⁰ = e₂ + m₀⁰/p₁ + (g_m − 1)M₀/(N₀p₁)`. -/
theorem ox_oldOptimal_iff (q : ℕ → ℝ) (hb : 0 < E.ox_oldBudget q) (c : ℝ) :
    E.ox_OldOptimal q c ↔ c = E.ox_oldBudget q := by
  constructor
  · rintro ⟨hc, hcb, hmax⟩
    by_contra hne
    have hlt : c < E.ox_oldBudget q := lt_of_le_of_ne hcb hne
    exact absurd (hmax _ hb le_rfl) (not_le.2 (E.ox_P.ox_u_lt hc hlt))
  · rintro rfl
    exact ⟨hb, le_rfl, fun c' hc' hcb => E.ox_P.ox_u_strictMonoOn.monotoneOn hc' hb hcb⟩

/-- An optimal choice exhausts both budget constraints (`u` is strictly increasing). -/
theorem ox_optimal_binds {q : ℕ → ℝ} {t : ℕ} {c1 c2 m : ℝ} (h : E.ox_Optimal q t c1 c2 m) :
    c1 = E.ox_e1 - q t * m ∧ c2 = E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t := by
  obtain ⟨⟨hm, h1, h2, hb1, hb2⟩, hmax⟩ := h
  constructor
  · by_contra hne
    have hlt : c1 < E.ox_e1 - q t * m := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax (E.ox_e1 - q t * m) c2 m ⟨hm, by linarith, h2, by linarith, hb2⟩
    have hu := E.ox_P.ox_u_lt h1 hlt
    unfold ox_EU OXPrefs.ox_U at this
    linarith
  · by_contra hne
    have hlt : c2 < E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax c1 _ m ⟨hm, h1, by linarith, hb1, le_rfl⟩
    have hu := mul_lt_mul_of_pos_left (E.ox_P.ox_u_lt h2 hlt) E.ox_P.ox_β_pos
    unfold ox_EU OXPrefs.ox_U at this
    linarith

/-- Miao, p. 531: autarky with valueless money (`p_t = ∞`) is an equilibrium, the nonmonetary
equilibrium. -/
theorem ox_autarky_isEquilibrium :
    E.ox_IsNonmonetary (fun _ => 0) (fun _ => E.ox_e1) (fun _ => E.ox_e2)
      (fun t => E.ox_M t / E.ox_N t) := by
  have hb : E.ox_oldBudget (fun _ => 0) = E.ox_e2 := by simp [ox_oldBudget]
  refine ⟨⟨fun _ _ => le_rfl, fun t _ => ⟨⟨?_, E.ox_e1_pos, E.ox_e2_pos, by simp, by simp⟩, ?_⟩,
    (E.ox_oldOptimal_iff _ (by rw [hb]; exact E.ox_e2_pos) _).2 hb.symm, fun t _ => ?_,
    fun t _ => rfl⟩, fun _ _ => rfl⟩
  · exact (div_pos (E.ox_M_pos t) (E.ox_N_pos t)).le
  · rintro c1' c2' m' ⟨_, h1, h2, hb1, hb2⟩
    simp only [zero_mul, add_zero] at hb1 hb2
    have u1 := E.ox_P.ox_u_strictMonoOn.monotoneOn h1 E.ox_e1_pos hb1
    have u2 := E.ox_P.ox_u_strictMonoOn.monotoneOn h2 E.ox_e2_pos hb2
    unfold ox_EU OXPrefs.ox_U
    nlinarith [E.ox_P.ox_β_pos]
  · field_simp [(E.ox_N_pos t).ne']

/-- Miao, p. 531: in every nonmonetary equilibrium the allocation is autarky,
`c_t^t = e₁`, `c_{t+1}^t = e₂` (`t ≥ 1`) and `c₁⁰ = e₂`. -/
theorem ox_nonmonetary_autarky {q cy co m : ℕ → ℝ} (h : E.ox_IsNonmonetary q cy co m) :
    (∀ t, 1 ≤ t → cy t = E.ox_e1 ∧ co t = E.ox_e2) ∧ co 0 = E.ox_e2 := by
  obtain ⟨⟨_, hopt, hold, _, _⟩, hq⟩ := h
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := E.ox_optimal_binds (hopt t ht)
    simp only [hq t ht, hq (t + 1) (by omega), zero_mul, sub_zero, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  · have hb : E.ox_oldBudget q = E.ox_e2 := by simp [ox_oldBudget, hq 1 le_rfl]
    rw [E.ox_oldOptimal_iff q (by rw [hb]; exact E.ox_e2_pos)] at hold
    rw [hold, hb]

/-- Real balances per young in terms of individual holdings: `m̂_t = q_t m_t^t` when the money
market clears. -/
theorem ox_mhat_eq {q m : ℕ → ℝ} {t : ℕ} (hclear : E.ox_M t = E.ox_N t * m t) :
    E.ox_mhat q t = q t * m t := by
  unfold ox_mhat; rw [hclear]; field_simp [(E.ox_N_pos t).ne']

/-- The old's resources in terms of next period's real balances: with `m_t^t = M_t/N_t`,
`e₂ + q_{t+1}m_t^t + q_{t+1}(g_m − 1)M_t/N_t = e₂ + g_n m̂_{t+1}`. -/
theorem ox_old_resources (q : ℕ → ℝ) (t : ℕ) :
    E.ox_e2 + q (t + 1) * (E.ox_M t / E.ox_N t) + q (t + 1) * E.ox_τ t =
      E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1) := by
  unfold ox_mhat ox_τ
  rw [E.ox_M_succ, E.ox_N_succ]
  have := (E.ox_N_pos t).ne'
  have := E.ox_gn_pos.ne'
  field_simp
  ring

/-- The initial old's resources: `c₁⁰ = e₂ + g_n m̂₁`. -/
theorem ox_oldBudget_eq (q : ℕ → ℝ) : E.ox_oldBudget q = E.ox_e2 + E.ox_gn * E.ox_mhat q 1 := by
  have h := E.ox_old_resources q 0
  simp only [ox_N, ox_M, ox_τ, pow_zero, mul_one, zero_add] at h
  rw [← h]; unfold ox_oldBudget; ring

/-- Miao, p. 532: in a monetary equilibrium `m_t^t = M_t/N_t > 0`, `m̂_t ∈ (0, e₁)`,
`c_t^t = e₁ − m̂_t`, `c_{t+1}^t = e₂ + g_n m̂_{t+1}` (`t ≥ 1`) and `c₁⁰ = e₂ + g_n m̂₁`. -/
theorem ox_monetary_alloc {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    (∀ t, 1 ≤ t → m t = E.ox_M t / E.ox_N t ∧ 0 < E.ox_mhat q t ∧ E.ox_mhat q t < E.ox_e1 ∧
      cy t = E.ox_e1 - E.ox_mhat q t ∧ co t = E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1)) ∧
      co 0 = E.ox_e2 + E.ox_gn * E.ox_mhat q 1 := by
  obtain ⟨⟨_, hopt, hold, hclear, _⟩, hq⟩ := h
  refine ⟨fun t ht => ?_, ?_⟩
  · have hm : m t = E.ox_M t / E.ox_N t := by
      rw [hclear t ht]; field_simp [(E.ox_N_pos t).ne']
    have hmh := E.ox_mhat_eq (q := q) (hclear t ht)
    obtain ⟨h1, h2⟩ := E.ox_optimal_binds (hopt t ht)
    have hc1 := (hopt t ht).1.2.1
    have hpos : 0 < E.ox_mhat q t := by
      unfold ox_mhat; exact div_pos (mul_pos (hq t ht) (E.ox_M_pos t)) (E.ox_N_pos t)
    refine ⟨hm, hpos, by linarith, by rw [h1, hmh], ?_⟩
    rw [h2, hm, E.ox_old_resources]
  · have hb : 0 < E.ox_oldBudget q := by
      rw [E.ox_oldBudget_eq]
      have : 0 < E.ox_mhat q 1 := by
        unfold ox_mhat; exact div_pos (mul_pos (hq 1 le_rfl) (E.ox_M_pos 1)) (E.ox_N_pos 1)
      nlinarith [E.ox_e2_pos, E.ox_gn_pos]
    rw [(E.ox_oldOptimal_iff q hb _).1 hold, E.ox_oldBudget_eq]

/-- Miao, (16.4), p. 531: in a monetary equilibrium the Euler equation
`u'(c_t^t)/(βu'(c_{t+1}^t)) = p_t/p_{t+1} = R_{t+1}` holds, with `p_t/p_{t+1} = q_{t+1}/q_t`. -/
theorem eq_16_4 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_P.ox_du (cy t) / (E.ox_P.ox_β * E.ox_P.ox_du (co t)) = q (t + 1) / q t := by
  have hopt := h.1.2.1 t ht
  have hqt := h.2 t ht
  have hqt1 := h.2 (t + 1) (by omega)
  obtain ⟨hm, hmpos, -, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  obtain ⟨b1, b2⟩ := E.ox_optimal_binds hopt
  obtain ⟨⟨_, h1, h2, _, _⟩, hmax⟩ := hopt
  have hmt : 0 < m t := by rw [hm]; exact div_pos (E.ox_M_pos t) (E.ox_N_pos t)
  have hfoc := E.ox_P.ox_foc (a := q t) (b := q (t + 1)) h1 h2 (by
    filter_upwards [OXPrefs.ox_eventually_pos (cy t) (-q t) h1,
      OXPrefs.ox_eventually_pos (co t) (q (t + 1)) h2,
      OXPrefs.ox_eventually_pos (m t) 1 hmt] with s hs1 hs2 hs3
    refine hmax _ _ (m t + s) ⟨by linarith, by linarith, hs2, ?_, ?_⟩
    · linarith
    · linarith)
  have hd1 := E.ox_P.ox_du_pos _ h1
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hβ := E.ox_P.ox_β_pos
  rw [div_eq_div_iff (by positivity) hqt.ne']
  linarith

/-- Miao, (16.5), p. 531: `R_aut = u'(e₁)/(βu'(e₂))` is the implicit interest rate of the
nonmonetary equilibrium: for a gross rate `R > 0`, autarky `(e₁, e₂)` maximises utility on the
budget line `c₁ + c₂/R ≤ e₁ + e₂/R` iff `R = R_aut`. -/
theorem eq_16_5 {R : ℝ} (hR : 0 < R) :
    (∀ c1 c2, 0 < c1 → 0 < c2 → c1 + c2 / R ≤ E.ox_e1 + E.ox_e2 / R →
      E.ox_EU c1 c2 ≤ E.ox_EU E.ox_e1 E.ox_e2) ↔ R = E.ox_Raut := by
  have hd1 := E.ox_P.ox_du_pos _ E.ox_e1_pos
  have hd2 := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  constructor
  · intro hmax
    have hfoc := E.ox_P.ox_foc (a := 1) (b := R) E.ox_e1_pos E.ox_e2_pos (by
      filter_upwards [OXPrefs.ox_eventually_pos E.ox_e1 (-1) E.ox_e1_pos,
        OXPrefs.ox_eventually_pos E.ox_e2 R E.ox_e2_pos] with s hs1 hs2
      refine hmax _ _ (by linarith) hs2 (le_of_eq ?_)
      field_simp; ring)
    unfold ox_Raut
    rw [eq_div_iff (by positivity)]
    linarith
  · intro hRe c1 c2 h1 h2 hline
    refine E.ox_P.ox_line_optimal E.ox_e1_pos E.ox_e2_pos hR ?_ h1 h2 hline
    rw [hRe]; unfold ox_Raut; field_simp

/-- Miao, (16.7), p. 538: `R_{t+1} = p_t/p_{t+1} = g_n m̂_{t+1}/(g_m m̂_t)` whenever `q_t > 0`. -/
theorem eq_16_7 (q : ℕ → ℝ) {t : ℕ} (hq : 0 < q t) :
    q (t + 1) / q t = E.ox_gn * E.ox_mhat q (t + 1) / (E.ox_gm * E.ox_mhat q t) := by
  unfold ox_mhat
  rw [E.ox_M_succ, E.ox_N_succ]
  have := (E.ox_N_pos t).ne'
  have := (E.ox_M_pos t).ne'
  have := E.ox_gn_pos.ne'
  have := E.ox_gm_pos.ne'
  have := hq.ne'
  field_simp

/-- Ratio bound used in (16.6): `u'(e₁ − a)/(βu'(e₂ + b)) > R_aut` for `0 < a < e₁`, `b > 0`. -/
theorem ox_Raut_lt {a b : ℝ} (ha : 0 < a) (hae : a < E.ox_e1) (hb : 0 < b) :
    E.ox_Raut < E.ox_P.ox_du (E.ox_e1 - a) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + b)) := by
  have hd1 := E.ox_P.ox_du_lt (x := E.ox_e1 - a) (y := E.ox_e1) (by linarith) (by linarith)
  have hd2 := E.ox_P.ox_du_lt (x := E.ox_e2) (y := E.ox_e2 + b) E.ox_e2_pos (by linarith)
  have p1 := E.ox_P.ox_du_pos _ E.ox_e1_pos
  have p2 := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + b by linarith [E.ox_e2_pos])
  have p3 := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  unfold ox_Raut
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : E.ox_P.ox_du E.ox_e1 * E.ox_P.ox_du (E.ox_e2 + b) <
      E.ox_P.ox_du (E.ox_e1 - a) * E.ox_P.ox_du E.ox_e2 := by nlinarith
  nlinarith

/-- Miao, (16.6), p. 532: in a monetary equilibrium,
`u'(e₁ − m̂_t)/(βu'(e₂ + g_n m̂_{t+1})) = R_{t+1} > R_aut` for all `t ≥ 1`. -/
theorem eq_16_6 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_P.ox_du (E.ox_e1 - E.ox_mhat q t) /
        (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1))) = q (t + 1) / q t ∧
      E.ox_Raut < q (t + 1) / q t := by
  obtain ⟨-, hpos, hlt, hcy, hco⟩ := (E.ox_monetary_alloc h).1 t ht
  obtain ⟨-, hpos1, -, -, -⟩ := (E.ox_monetary_alloc h).1 (t + 1) (by omega)
  have he := E.eq_16_4 h ht
  rw [hcy, hco] at he
  exact ⟨he, he ▸ E.ox_Raut_lt hpos hlt (mul_pos E.ox_gn_pos hpos1)⟩

/-- The Euler relation of the saving difference equation: `a, b ∈ (0, e₁)` and
`u'(e₁ − a) = β(g_n b/(g_m a))u'(e₂ + g_n b)`. -/
def ox_EulerRel (a b : ℝ) : Prop :=
  0 < a ∧ a < E.ox_e1 ∧ 0 < b ∧ b < E.ox_e1 ∧
    E.ox_P.ox_du (E.ox_e1 - a) =
      E.ox_P.ox_β * (E.ox_gn * b / (E.ox_gm * a)) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * b)

/-- The value of money implied by a saving path: `q_t = m̂_t N_t/M_t`. -/
noncomputable def ox_qOf (mh : ℕ → ℝ) (t : ℕ) : ℝ := mh t * E.ox_N t / E.ox_M t

theorem ox_mhat_qOf (mh : ℕ → ℝ) (t : ℕ) : E.ox_mhat (E.ox_qOf mh) t = mh t := by
  unfold ox_mhat ox_qOf
  field_simp [(E.ox_N_pos t).ne', (E.ox_M_pos t).ne']

/-- The young's budget line at positive money values: every choice in the budget set satisfies
`c₁ + c₂/R ≤ e₁ + (e₂ + q_{t+1}τ_t)/R`, `R = q_{t+1}/q_t`. -/
theorem ox_budget_line {q : ℕ → ℝ} {t : ℕ} (hq : 0 < q t) (hq1 : 0 < q (t + 1)) {c1 c2 m : ℝ}
    (hb : E.ox_Budget q t c1 c2 m) :
    c1 + c2 / (q (t + 1) / q t) ≤
      E.ox_e1 + (E.ox_e2 + q (t + 1) * E.ox_τ t) / (q (t + 1) / q t) := by
  obtain ⟨_, _, _, hb1, hb2⟩ := hb
  have hR : 0 < q (t + 1) / q t := div_pos hq1 hq
  have : c2 / (q (t + 1) / q t) ≤ (E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t) /
      (q (t + 1) / q t) := div_le_div_of_nonneg_right hb2 hR.le
  have he : (E.ox_e2 + q (t + 1) * m + q (t + 1) * E.ox_τ t) / (q (t + 1) / q t) =
      (E.ox_e2 + q (t + 1) * E.ox_τ t) / (q (t + 1) / q t) + q t * m := by
    field_simp; ring
  linarith

/-- Miao, pp. 531–532 (the equilibrium difference equation in saving): every sequence `m̂_t` with
`ox_EulerRel (m̂_t) (m̂_{t+1})` for all `t ≥ 1` is a monetary equilibrium, with
`q_t = m̂_t N_t/M_t`,
`c_t^t = e₁ − m̂_t`, `c_{t+1}^t = e₂ + g_n m̂_{t+1}`, `m_t^t = M_t/N_t`. -/
theorem ox_ofSaving_isMonetary {mh : ℕ → ℝ}
    (hrel : ∀ t, 1 ≤ t → E.ox_EulerRel (mh t) (mh (t + 1))) :
    E.ox_IsMonetary (E.ox_qOf mh) (fun t => E.ox_e1 - mh t)
      (fun t => E.ox_e2 + E.ox_gn * mh (t + 1)) (fun t => E.ox_M t / E.ox_N t) := by
  have hq : ∀ t, 1 ≤ t → 0 < E.ox_qOf mh t := fun t ht =>
    div_pos (mul_pos (hrel t ht).1 (E.ox_N_pos t)) (E.ox_M_pos t)
  have hco : ∀ t, 0 < E.ox_e2 + E.ox_gn * mh (t + 1) := fun t => by
    have := (hrel (t + 1) (by omega)).1
    nlinarith [E.ox_e2_pos, E.ox_gn_pos]
  have hres : ∀ t, E.ox_e2 + E.ox_qOf mh (t + 1) * (E.ox_M t / E.ox_N t) +
      E.ox_qOf mh (t + 1) * E.ox_τ t = E.ox_e2 + E.ox_gn * mh (t + 1) := fun t => by
    rw [E.ox_old_resources, E.ox_mhat_qOf]
  have hyoung : ∀ t, E.ox_qOf mh t * (E.ox_M t / E.ox_N t) = mh t := fun t => by
    rw [← E.ox_mhat_qOf mh t]; unfold ox_mhat; ring
  refine ⟨⟨fun t ht => (hq t ht).le, fun t ht => ?_, ?_, fun t _ => ?_, fun t ht => ?_⟩, hq⟩
  · obtain ⟨h0, he, -, -, heul⟩ := hrel t ht
    have hb : E.ox_Budget (E.ox_qOf mh) t (E.ox_e1 - mh t) (E.ox_e2 + E.ox_gn * mh (t + 1))
        (E.ox_M t / E.ox_N t) :=
      ⟨(div_pos (E.ox_M_pos t) (E.ox_N_pos t)).le, by linarith, hco t,
        by rw [hyoung]; linarith, by rw [hres]⟩
    refine ⟨hb, fun c1' c2' m' hb' => ?_⟩
    have hqt := hq t ht
    have hqt1 := hq (t + 1) (by omega)
    have hR : 0 < E.ox_qOf mh (t + 1) / E.ox_qOf mh t := div_pos hqt1 hqt
    have hReq := E.eq_16_7 (E.ox_qOf mh) hqt
    rw [E.ox_mhat_qOf, E.ox_mhat_qOf] at hReq
    refine E.ox_P.ox_line_optimal (by linarith) (hco t) hR ?_ hb'.2.1 hb'.2.2.1 ?_
    · rw [hReq]; exact heul
    · have hl := E.ox_budget_line hqt hqt1 hb'
      have he2 : E.ox_e1 + (E.ox_e2 + E.ox_qOf mh (t + 1) * E.ox_τ t) /
          (E.ox_qOf mh (t + 1) / E.ox_qOf mh t) = (E.ox_e1 - mh t) +
          (E.ox_e2 + E.ox_gn * mh (t + 1)) / (E.ox_qOf mh (t + 1) / E.ox_qOf mh t) := by
        rw [← hres t, ← hyoung t]
        field_simp
        ring
      linarith
  · have hpos : 0 < E.ox_oldBudget (E.ox_qOf mh) := by
      rw [E.ox_oldBudget_eq, E.ox_mhat_qOf]; exact hco 0
    refine (E.ox_oldOptimal_iff _ hpos _).2 ?_
    rw [E.ox_oldBudget_eq, E.ox_mhat_qOf]
  · field_simp [(E.ox_N_pos t).ne']
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [E.ox_N_succ]
    ring

/-- Conversely, every monetary equilibrium satisfies the saving difference equation:
`ox_EulerRel (m̂_t) (m̂_{t+1})` for all `t ≥ 1`. -/
theorem ox_monetary_eulerRel {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ}
    (ht : 1 ≤ t) : E.ox_EulerRel (E.ox_mhat q t) (E.ox_mhat q (t + 1)) := by
  obtain ⟨-, hpos, hlt, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  obtain ⟨-, hpos1, hlt1, -, -⟩ := (E.ox_monetary_alloc h).1 (t + 1) (by omega)
  refine ⟨hpos, hlt, hpos1, hlt1, ?_⟩
  have he := (E.eq_16_6 h ht).1
  rw [E.eq_16_7 q (h.2 t ht)] at he
  have hd := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1) by
    nlinarith [E.ox_e2_pos, E.ox_gn_pos])
  have hβ := E.ox_P.ox_β_pos
  rw [div_eq_iff (by positivity)] at he
  rw [he]; ring

end OXEconomy

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence of monetary equilibrium (Proposition 16.1.1)

Miao, §16.1, pp. 537–538.

* (16.8): in a monetary equilibrium `m̂_{t+1}/m̂_t = R_{t+1}g_m/g_n > R_aut g_m/g_n`
  (`eq_16_8`).
* **Proposition 16.1.1**: a monetary equilibrium exists iff `R_aut g_m < g_n`
  (`proposition_16_1_1`). Necessity (`proposition_16_1_1_necessity`), the book's limiting step
  (`proposition_16_1_1_limit`), the stationary monetary equilibrium: existence and uniqueness of
  `m̂ ∈ (0, e₁)` with `u'(e₁ − m̂)/(βu'(e₂ + g_n m̂)) = g_n/g_m` (`proposition_16_1_1_root`), the
  constant path is a monetary equilibrium (`proposition_16_1_1_sufficiency`) and is the unique
  monetary equilibrium with constant real balances (`proposition_16_1_1_unique_stationary`); its
  interest rate is `g_n/g_m`, the golden rule `R = g_n` when `g_m = 1` (`ox_stationary_R`).

**Correction (necessity proof).** The book splits on `R_aut g_m/g_n > 1` and `= 1` and in the
second case takes limits in (16.6)–(16.7). The limit `m̂_∞` is always finite (`m̂_t < e₁`); what
the limiting argument needs is `m̂_∞ < e₁` (so that `u'` is continuous at `e₁ − m̂_∞`), which the
book does not check. `proposition_16_1_1_limit` proves the limit equation for `0 < m̂_∞ < e₁`.
The necessity proof given here avoids limits: since `m̂_t ≥ m̂₁`, `R_{t+1} ≥ u'(e₁ − m̂₁)/(βu'(e₂))
> R_aut`, so `m̂_t` grows at a rate bounded above one in both cases.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, (16.8), p. 538: in a monetary equilibrium
`m̂_{t+1}/m̂_t = R_{t+1} g_m/g_n > R_aut g_m/g_n`. -/
theorem eq_16_8 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_mhat q (t + 1) / E.ox_mhat q t = q (t + 1) / q t * E.ox_gm / E.ox_gn ∧
      E.ox_Raut * E.ox_gm / E.ox_gn < E.ox_mhat q (t + 1) / E.ox_mhat q t := by
  have h7 := E.eq_16_7 q (h.2 t ht)
  obtain ⟨-, hpos, -, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have he : E.ox_mhat q (t + 1) / E.ox_mhat q t = q (t + 1) / q t * E.ox_gm / E.ox_gn := by
    rw [h7]; field_simp
  refine ⟨he, ?_⟩
  rw [he]
  have := (E.eq_16_6 h ht).2
  have : E.ox_Raut * E.ox_gm < q (t + 1) / q t * E.ox_gm := mul_lt_mul_of_pos_right this hgm
  exact div_lt_div_of_pos_right this hgn

/-- **Proposition 16.1.1**, necessity (Miao, pp. 537–538): if a monetary equilibrium exists then
`R_aut g_m < g_n`. -/
theorem proposition_16_1_1_necessity {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    E.ox_Raut * E.ox_gm < E.ox_gn := by
  by_contra hcon
  have hge : E.ox_gn ≤ E.ox_Raut * E.ox_gm := not_lt.1 hcon
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have hβ := E.ox_P.ox_β_pos
  have alloc := (E.ox_monetary_alloc h).1
  set x := E.ox_mhat q
  have hx : ∀ t, 1 ≤ t → 0 < x t ∧ x t < E.ox_e1 := fun t ht =>
    ⟨(alloc t ht).2.1, (alloc t ht).2.2.1⟩
  -- real balances increase
  have hinc : ∀ t, 1 ≤ t → x t < x (t + 1) := fun t ht => by
    have h8 := (E.eq_16_8 h ht).2
    have h1 : 1 ≤ E.ox_Raut * E.ox_gm / E.ox_gn := (le_div_iff₀ hgn).2 (by linarith)
    have := (hx t ht).1
    have : 1 < x (t + 1) / x t := lt_of_le_of_lt h1 h8
    rwa [lt_div_iff₀ (hx t ht).1, one_mul] at this
  have hmono : ∀ n, x 1 ≤ x (n + 1) := fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact ih.trans (hinc (n + 1) (by omega)).le
  -- uniform lower bound on the interest rate
  set Rb := E.ox_P.ox_du (E.ox_e1 - x 1) / (E.ox_P.ox_β * E.ox_P.ox_du E.ox_e2)
  have hRb : E.ox_Raut < Rb := by
    have := E.ox_P.ox_du_lt (x := E.ox_e1 - x 1) (y := E.ox_e1) (by linarith [hx 1 le_rfl])
      (by linarith [(hx 1 le_rfl).1])
    have := E.ox_P.ox_du_pos _ E.ox_e2_pos
    unfold ox_Raut; simp only [Rb]
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  have hRt : ∀ n, Rb ≤ q (n + 2) / q (n + 1) := fun n => by
    have he := (E.eq_16_6 h (t := n + 1) (by omega)).1
    rw [← he]
    have hxn := hmono n
    have hxn1 := hx (n + 1) (by omega)
    have hxn2 := hx (n + 2) (by omega)
    have d1 : E.ox_P.ox_du (E.ox_e1 - x 1) ≤ E.ox_P.ox_du (E.ox_e1 - x (n + 1)) :=
      E.ox_P.ox_du_anti.antitoneOn (show (0 : ℝ) < E.ox_e1 - x (n + 1) by linarith)
        (show (0 : ℝ) < E.ox_e1 - x 1 by linarith [hx 1 le_rfl]) (by linarith)
    have d2 : E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (n + 2)) ≤ E.ox_P.ox_du E.ox_e2 :=
      E.ox_P.ox_du_anti.antitoneOn E.ox_e2_pos
        (show (0 : ℝ) < E.ox_e2 + E.ox_gn * x (n + 2) by nlinarith [E.ox_e2_pos])
        (by nlinarith)
    have p1 := E.ox_P.ox_du_pos _ (show (0 : ℝ) < E.ox_e1 - x 1 by linarith [hx 1 le_rfl])
    have p2 := E.ox_P.ox_du_pos _
      (show (0 : ℝ) < E.ox_e2 + E.ox_gn * x (n + 2) by nlinarith [E.ox_e2_pos])
    simp only [Rb]
    exact div_le_div₀ (by linarith) d1 (by positivity) (mul_le_mul_of_nonneg_left d2 hβ.le)
  set k := Rb * E.ox_gm / E.ox_gn
  have hk : 1 < k := by
    have : E.ox_Raut * E.ox_gm < Rb * E.ox_gm := mul_lt_mul_of_pos_right hRb hgm
    exact (lt_div_iff₀ hgn).2 (by linarith)
  have hgrow : ∀ n, k ^ n * x 1 ≤ x (n + 1) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have h8 := (E.eq_16_8 h (t := n + 1) (by omega)).1
      have hxn := (hx (n + 1) (by omega)).1
      have hr : k ≤ x (n + 2) / x (n + 1) := by
        rw [h8]
        have := mul_le_mul_of_nonneg_right (hRt n) hgm.le
        exact div_le_div_of_nonneg_right this hgn.le
      rw [le_div_iff₀ hxn] at hr
      calc k ^ (n + 1) * x 1 = k * (k ^ n * x 1) := by ring
        _ ≤ k * x (n + 1) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ x (n + 2) := by linarith
  have hx1 := (hx 1 le_rfl).1
  have htend : Tendsto (fun n => k ^ n * x 1) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const hx1
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop E.ox_e1).exists
  linarith [hgrow n, (hx (n + 1) (by omega)).2]

/-- Miao, p. 538 (the limiting step of the necessity proof): if along a monetary equilibrium
`m̂_t → m̂_∞` with `0 < m̂_∞ < e₁`, then `u'(e₁ − m̂_∞)/(βu'(e₂ + g_n m̂_∞)) = R_∞ = g_n/g_m`;
since the left side exceeds `R_aut`, `R_aut g_m = g_n` is impossible. -/
theorem proposition_16_1_1_limit {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {L : ℝ}
    (hL : Tendsto (E.ox_mhat q) atTop (𝓝 L)) (hL0 : 0 < L) (hLe : L < E.ox_e1) :
    E.ox_P.ox_du (E.ox_e1 - L) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * L)) =
      E.ox_gn / E.ox_gm ∧ E.ox_Raut < E.ox_gn / E.ox_gm := by
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  set x := E.ox_mhat q
  have hL1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  -- the right side of (16.7) converges to g_n/g_m
  have hR : Tendsto (fun t => E.ox_gn * x (t + 1) / (E.ox_gm * x t)) atTop
      (𝓝 (E.ox_gn * L / (E.ox_gm * L))) :=
    (hL1.const_mul _).div (hL.const_mul _) (by positivity)
  have hRe : E.ox_gn * L / (E.ox_gm * L) = E.ox_gn / E.ox_gm := by field_simp
  rw [hRe] at hR
  -- the left side of (16.6) converges by continuity of `u'`
  have hc1 : ContinuousAt E.ox_P.ox_du (E.ox_e1 - L) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by linarith))
  have hc2 : ContinuousAt E.ox_P.ox_du (E.ox_e2 + E.ox_gn * L) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by nlinarith [E.ox_e2_pos]))
  have hp2 := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + E.ox_gn * L by nlinarith [E.ox_e2_pos])
  have hβ := E.ox_P.ox_β_pos
  have hlhs : Tendsto (fun t => E.ox_P.ox_du (E.ox_e1 - x t) /
      (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (t + 1)))) atTop
      (𝓝 (E.ox_P.ox_du (E.ox_e1 - L) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * L)))) :=
    (hc1.tendsto.comp (hL.const_sub _)).div
      ((hc2.tendsto.comp ((hL1.const_mul _).const_add _)).const_mul _) (by positivity)
  have heq : ∀ᶠ t in atTop, E.ox_P.ox_du (E.ox_e1 - x t) /
      (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (t + 1))) =
        E.ox_gn * x (t + 1) / (E.ox_gm * x t) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [(E.eq_16_6 h ht).1, E.eq_16_7 q (h.2 t ht)]
  have hlim := tendsto_nhds_unique (hlhs.congr' heq) hR
  refine ⟨hlim, ?_⟩
  rw [← hlim]
  exact E.ox_Raut_lt hL0 hLe (mul_pos hgn hL0)

/-- **Proposition 16.1.1**, the stationary root (Miao, p. 538): if `R_aut g_m < g_n` there is a
unique `m̂ ∈ (0, e₁)` with `u'(e₁ − m̂) = β(g_n/g_m)u'(e₂ + g_n m̂)`. -/
theorem proposition_16_1_1_root (hR : E.ox_Raut * E.ox_gm < E.ox_gn) :
    ∃! mh, 0 < mh ∧ mh < E.ox_e1 ∧ E.ox_P.ox_du (E.ox_e1 - mh) =
      E.ox_P.ox_β * (E.ox_gn / E.ox_gm) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * mh) := by
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have hβ := E.ox_P.ox_β_pos
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hd2 := E.ox_P.ox_du_pos _ he2
  set K := E.ox_P.ox_β * (E.ox_gn / E.ox_gm)
  have hK : 0 < K := by positivity
  set F : ℝ → ℝ := fun x => E.ox_P.ox_du (E.ox_e1 - x) - K * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x)
  have hF0 : F 0 < 0 := by
    simp only [F, sub_zero, mul_zero, add_zero]
    have : E.ox_Raut < E.ox_gn / E.ox_gm := (lt_div_iff₀ hgm).2 hR
    unfold ox_Raut at this
    rw [div_lt_iff₀ (by positivity)] at this
    simp only [K]; linarith
  -- an interior point where `F > 0`, from the Inada condition
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), K * E.ox_P.ox_du E.ox_e2 < E.ox_P.ox_du y ∧ y < E.ox_e1 ∧
      0 < y :=
    (E.ox_P.ox_inada.eventually_gt_atTop _).and
      ((show ∀ᶠ y in 𝓝[>] (0 : ℝ), y < E.ox_e1 from
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds he1)).and self_mem_nhdsWithin)
  obtain ⟨δ, hδK, hδe, hδ0⟩ := hev.exists
  set b := E.ox_e1 - δ
  have hb0 : 0 < b := by simp only [b]; linarith
  have hFb : 0 < F b := by
    simp only [F, b, sub_sub_cancel]
    have : E.ox_P.ox_du (E.ox_e2 + E.ox_gn * (E.ox_e1 - δ)) ≤ E.ox_P.ox_du E.ox_e2 :=
      E.ox_P.ox_du_anti.antitoneOn he2 (show (0 : ℝ) < _ by nlinarith) (by nlinarith)
    nlinarith
  have hcont : ContinuousOn F (Set.Icc 0 b) := by
    refine ContinuousOn.sub ?_ (ContinuousOn.mul continuousOn_const ?_)
    · refine E.ox_P.ox_du_cont.comp (continuousOn_const.sub continuousOn_id) fun x hx => ?_
      simp only [Set.mem_Ioi]; linarith [hx.2]
    · refine E.ox_P.ox_du_cont.comp (continuousOn_const.add
        (continuousOn_const.mul continuousOn_id)) fun x hx => ?_
      simp only [Set.mem_Ioi]; nlinarith [hx.1]
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc hb0.le hcont ⟨hF0.le, hFb.le⟩
  have hx0 : 0 < x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h] at hFx; linarith
    · exact h
  have hxe : x < E.ox_e1 := by linarith [hx.2]
  -- `F` is strictly increasing
  have hFmono : ∀ y z, 0 < y → y < z → z < E.ox_e1 → F y < F z := fun y z hy hyz hz => by
    have d1 := E.ox_P.ox_du_lt (x := E.ox_e1 - z) (y := E.ox_e1 - y) (by linarith) (by linarith)
    have d2 := E.ox_P.ox_du_lt (x := E.ox_e2 + E.ox_gn * y) (y := E.ox_e2 + E.ox_gn * z)
      (by nlinarith) (by nlinarith)
    simp only [F]; nlinarith
  refine ⟨x, ⟨hx0, hxe, by simp only [F] at hFx; linarith⟩, ?_⟩
  rintro y ⟨hy0, hye, hy⟩
  have hFy : F y = 0 := by simp only [F]; linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · linarith [hFmono y x hy0 hlt hxe]
  · linarith [hFmono x y hx0 hlt hye]

/-- The constant saving path `m̂` satisfies the saving difference equation iff `m̂` is the
stationary root. -/
theorem ox_eulerRel_const_iff {mh : ℝ} (h0 : 0 < mh) (he : mh < E.ox_e1) :
    E.ox_EulerRel mh mh ↔ E.ox_P.ox_du (E.ox_e1 - mh) =
      E.ox_P.ox_β * (E.ox_gn / E.ox_gm) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * mh) := by
  have : E.ox_gn * mh / (E.ox_gm * mh) = E.ox_gn / E.ox_gm := by
    have := E.ox_gm_pos.ne'; field_simp
  unfold ox_EulerRel
  rw [this]
  exact ⟨fun h => h.2.2.2.2, fun h => ⟨h0, he, h0, he, h⟩⟩

/-- **Proposition 16.1.1**, sufficiency (Miao, p. 538): if `R_aut g_m < g_n`, the constant path
`m̂_t = m̂` (the stationary root) is a monetary equilibrium. -/
theorem proposition_16_1_1_sufficiency (hR : E.ox_Raut * E.ox_gm < E.ox_gn) :
    ∃ mh : ℝ, 0 < mh ∧ mh < E.ox_e1 ∧ E.ox_IsMonetary (E.ox_qOf fun _ => mh)
      (fun _ => E.ox_e1 - mh) (fun _ => E.ox_e2 + E.ox_gn * mh)
      (fun t => E.ox_M t / E.ox_N t) := by
  obtain ⟨mh, ⟨h0, he, hroot⟩, -⟩ := E.proposition_16_1_1_root hR
  exact ⟨mh, h0, he, E.ox_ofSaving_isMonetary (mh := fun _ => mh)
    fun _ _ => (E.ox_eulerRel_const_iff h0 he).2 hroot⟩

/-- **Proposition 16.1.1** (Miao, p. 537): `R_aut g_m < g_n` is necessary and sufficient for the
existence of at least one monetary equilibrium. -/
theorem proposition_16_1_1 :
    (∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m) ↔ E.ox_Raut * E.ox_gm < E.ox_gn := by
  constructor
  · rintro ⟨q, cy, co, m, h⟩
    exact E.proposition_16_1_1_necessity h
  · intro hR
    obtain ⟨mh, -, -, h⟩ := E.proposition_16_1_1_sufficiency hR
    exact ⟨_, _, _, _, h⟩

/-- Miao, p. 538: the equilibrium with constant per-capita real balances is unique: in every
monetary equilibrium with `m̂_t = m̂` for all `t ≥ 1`, `m̂` is the stationary root. -/
theorem proposition_16_1_1_unique_stationary {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m)
    {mh : ℝ} (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) :
    0 < mh ∧ mh < E.ox_e1 ∧ E.ox_P.ox_du (E.ox_e1 - mh) =
      E.ox_P.ox_β * (E.ox_gn / E.ox_gm) * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * mh) := by
  have hrel := E.ox_monetary_eulerRel h (t := 1) le_rfl
  rw [hc 1 le_rfl, hc 2 (by omega)] at hrel
  exact ⟨hrel.1, hrel.2.1, (E.ox_eulerRel_const_iff hrel.1 hrel.2.1).1 hrel⟩

/-- Miao, p. 538 (the golden rule): in a monetary equilibrium with constant real balances the
gross interest rate is `R_{t+1} = g_n/g_m`; with `g_m = 1` it is the population growth factor. -/
theorem ox_stationary_R {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {mh : ℝ}
    (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) {t : ℕ} (ht : 1 ≤ t) :
    q (t + 1) / q t = E.ox_gn / E.ox_gm := by
  rw [E.eq_16_7 q (h.2 t ht), hc t ht, hc (t + 1) (by omega)]
  have := (E.proposition_16_1_1_unique_stationary h hc).1
  have := E.ox_gm_pos.ne'
  field_simp

end OXEconomy

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The offer curve and the dynamics of the special case

Miao, §16.1, "A Special Case and Multiple Equilibria", pp. 532–536 (Figures 16.1–16.4).

* Saving `m_t = m_t^t/p_t = e₁ − c_t^t` and excess demand `z_t = m_t^t/p_{t+1} = m_t R_{t+1}`:
  the ray to a point of the offer curve has slope `R_{t+1}` (`ox_offer_z`), the offer curve lies
  left of `e₁` (`ox_offer_lt_e1`); in equilibrium with `g_n = g_m = 1`, `z_t = m_{t+1}` and the
  Euler equation is `u'(e₁ − m_t) = βu'(m_tR_{t+1} + e₂)R_{t+1}` (`ox_offer_equilibrium`).
* The slopes `dm_t/dR_{t+1}` and `dz_t/dR_{t+1} > 0` by implicit differentiation of the Euler
  equation (`ox_offer_slope_m`, `ox_offer_slope_z`, `ox_offer_slope_z_pos`); backward bending
  iff `βu'(c)(γ(c)z/c − 1) > 0` (`ox_offer_backward_iff`), which needs `γ(c_{t+1}^t) > 1`
  (`ox_offer_backward_necessary`); `γ ≤ 1` gives an upward-sloping curve (`ox_offer_upward`).
* The nonmonetary steady state at the origin: zero saving is optimal exactly at `R = R_aut`
  (`ox_offer_origin`), and the slope of the offer curve at the origin is `R_aut`
  (`ox_offer_slope_origin`); monetary steady states lie on the 45° line with `R = 1`
  (`ox_offer_steady_iff`) and exist iff `R_aut < 1` (`ox_offer_steady_exists_iff`).
* Along paths with real balances vanishing, `R_{t+1} → R_aut` and inflation
  `p_{t+1}/p_t → 1/R_aut`, the inverse of the slope at the origin (`ox_R_tendsto_Raut`).
* Stability of a steady state of `m_{t+1} = f(m_t)`: `|f'| < 1` gives local stability
  (`ox_fixed_stable`), `|f'| > 1` instability (`ox_fixed_unstable`); the locally stable case
  is indeterminate, a continuum of monetary equilibria converging to `m*`
  (`ox_indeterminacy`); two-period cycles (`ox_two_cycle`).

**Correction.** "A monetary steady state is unstable iff `|dm_{t+1}/dm_t| > 1`" fails at
`|f'| = 1`: `f(x) = x + x³` has `f'(0) = 1` and an unstable fixed point
(`ox_unstable_counterexample`). What is true is the two sufficient conditions above.
Figures 16.1–16.4 are not formalised beyond these statements; the convergence claims of
Figure 16.2 are proved for the logarithmic economy (`OXExamples`, Example 16.1.1).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, p. 532: with real saving `m = q_t m_t^t` and `z = q_{t+1} m_t^t`, `z = mR_{t+1}`: the
slope of the ray from the origin to a point of the offer curve is `p_t/p_{t+1}`. -/
theorem ox_offer_z (q : ℕ → ℝ) (t : ℕ) (hq : q t ≠ 0) (mm : ℝ) :
    q (t + 1) * mm = q t * mm * (q (t + 1) / q t) := by
  field_simp

/-- Miao, p. 532: the offer curve lies to the left of `e₁`: optimal saving is below `e₁`. -/
theorem ox_offer_lt_e1 {q : ℕ → ℝ} {t : ℕ} {c1 c2 m : ℝ} (h : E.ox_Optimal q t c1 c2 m) :
    q t * m < E.ox_e1 := by
  obtain ⟨⟨_, h1, _, hb1, _⟩, _⟩ := h
  linarith

/-- Miao, pp. 532–534: in a monetary equilibrium of the special case `g_n = g_m = 1`, demand
equals supply, `z_t = m_tR_{t+1} = m_{t+1}`, and the Euler equation reads
`u'(e₁ − m_t) = βu'(m_tR_{t+1} + e₂)R_{t+1}`. -/
theorem ox_offer_equilibrium (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    E.ox_mhat q t * (q (t + 1) / q t) = E.ox_mhat q (t + 1) ∧
      E.ox_P.ox_du (E.ox_e1 - E.ox_mhat q t) = E.ox_P.ox_β *
        E.ox_P.ox_du (E.ox_mhat q t * (q (t + 1) / q t) + E.ox_e2) * (q (t + 1) / q t) := by
  obtain ⟨-, hpos, -, -, -⟩ := (E.ox_monetary_alloc h).1 t ht
  have h7 := E.eq_16_7 q (h.2 t ht)
  rw [hgn, hgm, one_mul, one_mul] at h7
  have hz : E.ox_mhat q t * (q (t + 1) / q t) = E.ox_mhat q (t + 1) := by
    rw [h7]; field_simp
  refine ⟨hz, ?_⟩
  have h6 := (E.eq_16_6 h ht).1
  rw [hgn, one_mul] at h6
  have hd := E.ox_P.ox_du_pos _ (show 0 < E.ox_e2 + E.ox_mhat q (t + 1) by
    have := ((E.ox_monetary_alloc h).1 (t + 1) (by omega)).2.1
    linarith [E.ox_e2_pos])
  have hβ := E.ox_P.ox_β_pos
  rw [div_eq_iff (by positivity)] at h6
  rw [hz, add_comm, h6]; ring

end OXEconomy

namespace OXPrefs

variable (P : OXPrefs)

/-- Miao, p. 533: implicit differentiation of the Euler equation
`u'(e₁ − m(R)) = βu'(m(R)R + e₂)R` gives
`m'(u''(c₁) + βR²u''(c₂)) = −(Rmβu''(c₂) + βu'(c₂))`. -/
theorem ox_offer_slope_m {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R') :
    m' * (d1 + P.ox_β * R ^ 2 * d2) =
      -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) := by
  have hL : HasDerivAt (fun R' => P.ox_du (e1 - mf R')) (d1 * -m') R :=
    hd1.comp R (hm.const_sub e1)
  have hin : HasDerivAt (fun R' => mf R' * R' + e2) (m' * R + mf R * 1) R :=
    ((hm.mul (hasDerivAt_id R)).add_const e2)
  have hR : HasDerivAt (fun R' => P.ox_β * P.ox_du (mf R' * R' + e2) * R')
      (P.ox_β * (d2 * (m' * R + mf R * 1)) * R + P.ox_β * P.ox_du (mf R * R + e2) * 1) R :=
    ((hd2.comp R hin).const_mul P.ox_β).mul (hasDerivAt_id R)
  have := hL.unique (hR.congr_of_eventuallyEq (by
    filter_upwards [heul] with R' hR' using hR'))
  linear_combination (-1 : ℝ) * this

/-- Miao, p. 533: `dm_t/dR_{t+1} = −(R mβu''(c₂) + βu'(c₂))/(u''(c₁) + βR²u''(c₂))`. -/
theorem ox_offer_slope_m_eq {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 ≠ 0) :
    m' = -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) /
      (d1 + P.ox_β * R ^ 2 * d2) := by
  rw [eq_div_iff hD]; exact P.ox_offer_slope_m hm hd1 hd2 heul

/-- Miao, p. 533: with `z(R) = m(R)R`,
`dz_t/dR_{t+1} = (m u''(c₁) − βu'(c₂)R)/(u''(c₁) + βR²u''(c₂))`. -/
theorem ox_offer_slope_z {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 ≠ 0) :
    HasDerivAt (fun R' => mf R' * R')
      ((mf R * d1 - P.ox_β * P.ox_du (mf R * R + e2) * R) / (d1 + P.ox_β * R ^ 2 * d2)) R := by
  have h : HasDerivAt (fun R' => mf R' * R') (m' * R + mf R * 1) R := hm.mul (hasDerivAt_id' R)
  convert h using 1
  have hs := P.ox_offer_slope_m hm hd1 hd2 heul
  rw [div_eq_iff hD]
  linear_combination (-R) * hs

/-- Miao, p. 533: `dz_t/dR_{t+1} > 0` (with `u'' < 0` at both consumptions, `m ≥ 0`, `R > 0`). -/
theorem ox_offer_slope_z_pos {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hd1n : d1 < 0) (hd2n : d2 < 0) (hR : 0 < R) (hm0 : 0 ≤ mf R) (hc2 : 0 < mf R * R + e2) :
    ∃ z', HasDerivAt (fun R' => mf R' * R') z' R ∧ 0 < z' := by
  have hβ := P.ox_β_pos
  have hD : d1 + P.ox_β * R ^ 2 * d2 < 0 := by
    have : 0 ≤ P.ox_β * R ^ 2 := by positivity
    have := mul_nonpos_of_nonneg_of_nonpos this hd2n.le
    linarith
  refine ⟨_, P.ox_offer_slope_z hm hd1 hd2 heul hD.ne, div_pos_of_neg_of_neg ?_ hD⟩
  have := P.ox_du_pos _ hc2
  have : 0 < P.ox_β * P.ox_du (mf R * R + e2) * R := by positivity
  have := mul_nonpos_of_nonneg_of_nonpos hm0 hd1n.le
  linarith

/-- Miao, p. 533: the coefficient of relative risk aversion `γ(c) = −cu''(c)/u'(c)` enters
through the identity `−(Rmβu''(c₂) + βu'(c₂)) = βu'(c₂)(γ(c₂)z/c₂ − 1)`, `z = mR`; hence, as the
denominator is negative, `dm_t/dR_{t+1} < 0` iff `0 < βu'(c₂)(γ(c₂)z/c₂ − 1)`. -/
theorem ox_offer_backward_iff {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 < 0) (hc2 : 0 < mf R * R + e2) :
    -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) =
        P.ox_β * P.ox_du (mf R * R + e2) *
          ((-(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)) * (mf R * R / (mf R * R + e2)) - 1) ∧
      (m' < 0 ↔ 0 < P.ox_β * P.ox_du (mf R * R + e2) *
          ((-(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)) * (mf R * R / (mf R * R + e2)) - 1))
    := by
  have hdu := P.ox_du_pos _ hc2
  have hid : -(R * mf R * P.ox_β * d2 + P.ox_β * P.ox_du (mf R * R + e2)) =
      P.ox_β * P.ox_du (mf R * R + e2) *
        ((-(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)) * (mf R * R / (mf R * R + e2)) - 1) := by
    set w := P.ox_du (mf R * R + e2)
    set c := mf R * R + e2
    have hw : w ≠ 0 := hdu.ne'
    have hc : c ≠ 0 := hc2.ne'
    field_simp
    ring
  refine ⟨hid, ?_⟩
  rw [← hid]
  have hs := P.ox_offer_slope_m hm hd1 hd2 heul
  constructor
  · intro hm'; nlinarith
  · intro hpos
    by_contra hge
    have : 0 ≤ m' := not_lt.1 hge
    nlinarith [mul_nonpos_of_nonneg_of_nonpos this hD.le]

/-- Miao, p. 534: since `z < c_{t+1}^t` (`e₂ > 0`), a backward-bending offer curve
(`dm_t/dR_{t+1} < 0`) needs `γ(c_{t+1}^t) > 1`. -/
theorem ox_offer_backward_necessary {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ}
    (hm : HasDerivAt mf m' R) (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R))
    (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 < 0) (he2 : 0 < e2) (hz : 0 ≤ mf R * R) (hm' : m' < 0) :
    1 < -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2) := by
  have hc2 : 0 < mf R * R + e2 := by linarith
  obtain ⟨-, hiff⟩ := P.ox_offer_backward_iff hm hd1 hd2 heul hD hc2
  have hpos := hiff.1 hm'
  have hβ := P.ox_β_pos
  have hdu := P.ox_du_pos _ hc2
  set γ := -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)
  have h1 : 0 < γ * (mf R * R / (mf R * R + e2)) - 1 := by
    by_contra hle
    have : P.ox_β * P.ox_du (mf R * R + e2) *
        (γ * (mf R * R / (mf R * R + e2)) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hle)
    linarith
  have hfrac : mf R * R / (mf R * R + e2) < 1 := (div_lt_one hc2).2 (by linarith)
  have hfrac0 : 0 ≤ mf R * R / (mf R * R + e2) := div_nonneg hz hc2.le
  by_contra hγ
  have hγ' : γ ≤ 1 := not_lt.1 hγ
  rcases le_or_gt γ 0 with hγ0 | hγ0
  · nlinarith
  · nlinarith

/-- Miao, p. 534: if `γ(c_{t+1}^t) ≤ 1` the offer curve is upward sloping: `dm_t/dR_{t+1} > 0`. -/
theorem ox_offer_upward {e1 e2 R m' d1 d2 : ℝ} {mf : ℝ → ℝ} (hm : HasDerivAt mf m' R)
    (hd1 : HasDerivAt P.ox_du d1 (e1 - mf R)) (hd2 : HasDerivAt P.ox_du d2 (mf R * R + e2))
    (heul : ∀ᶠ R' in 𝓝 R, P.ox_du (e1 - mf R') = P.ox_β * P.ox_du (mf R' * R' + e2) * R')
    (hD : d1 + P.ox_β * R ^ 2 * d2 < 0) (he2 : 0 < e2) (hz : 0 ≤ mf R * R)
    (hγ : -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2) ≤ 1) : 0 < m' := by
  have hc2 : 0 < mf R * R + e2 := by linarith
  obtain ⟨hid, -⟩ := P.ox_offer_backward_iff hm hd1 hd2 heul hD hc2
  have hs := P.ox_offer_slope_m hm hd1 hd2 heul
  have hβ := P.ox_β_pos
  have hdu := P.ox_du_pos _ hc2
  set γ := -(mf R * R + e2) * d2 / P.ox_du (mf R * R + e2)
  have hfrac : mf R * R / (mf R * R + e2) < 1 := (div_lt_one hc2).2 (by linarith)
  have hfrac0 : 0 ≤ mf R * R / (mf R * R + e2) := div_nonneg hz hc2.le
  have hneg : γ * (mf R * R / (mf R * R + e2)) - 1 < 0 := by
    rcases le_or_gt γ 0 with hγ0 | hγ0
    · nlinarith
    · nlinarith
  have : P.ox_β * P.ox_du (mf R * R + e2) * (γ * (mf R * R / (mf R * R + e2)) - 1) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hneg
  rw [← hid] at this
  by_contra hle
  nlinarith [mul_nonneg_of_nonpos_of_nonpos (not_lt.1 hle) hD.le]

end OXPrefs

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, pp. 532–534 (the nonmonetary steady state at the origin): zero saving solves the
Euler equation `u'(e₁ − m) = βu'(mR + e₂)R` iff `R = R_aut`. -/
theorem ox_offer_origin {R : ℝ} :
    E.ox_P.ox_du (E.ox_e1 - 0) = E.ox_P.ox_β * E.ox_P.ox_du (0 * R + E.ox_e2) * R ↔
      R = E.ox_Raut := by
  have hd := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  simp only [sub_zero, zero_mul, zero_add]
  unfold ox_Raut
  rw [eq_div_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- Miao, p. 534: the slope of the offer curve `z = m(R)R` at the origin (`m(R_aut) = 0`) is
`dz/dm = R_aut`. -/
theorem ox_offer_slope_origin {mf : ℝ → ℝ} {m' : ℝ} (hm : HasDerivAt mf m' E.ox_Raut)
    (h0 : mf E.ox_Raut = 0) (hm' : m' ≠ 0) :
    HasDerivAt (fun R => mf R * R) (m' * E.ox_Raut) E.ox_Raut ∧
      m' * E.ox_Raut / m' = E.ox_Raut := by
  refine ⟨?_, by field_simp⟩
  have : HasDerivAt (fun R => mf R * R) (m' * E.ox_Raut + mf E.ox_Raut * 1) E.ox_Raut :=
    hm.mul (hasDerivAt_id' E.ox_Raut)
  simpa [h0] using this

/-- Miao, p. 534 (monetary steady states of the special case): with `g_n = g_m = 1`, the
constant path `m` is a monetary equilibrium iff `m ∈ (0, e₁)` and `u'(e₁ − m) = βu'(e₂ + m)`,
i.e. it lies on the 45° line with `R = 1`. -/
theorem ox_offer_steady_iff (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) {mh : ℝ} :
    E.ox_EulerRel mh mh ↔ 0 < mh ∧ mh < E.ox_e1 ∧
      E.ox_P.ox_du (E.ox_e1 - mh) = E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + mh) := by
  constructor
  · intro h
    have := (E.ox_eulerRel_const_iff h.1 h.2.1).1 h
    rw [hgn, hgm, div_one, mul_one, one_mul] at this
    exact ⟨h.1, h.2.1, this⟩
  · rintro ⟨h0, he, h⟩
    refine (E.ox_eulerRel_const_iff h0 he).2 ?_
    rw [hgn, hgm, div_one, mul_one, one_mul]; exact h

/-- Miao, p. 534: with `g_n = g_m = 1` there is a monetary steady state iff the slope of the
offer curve at the origin is below one, `R_aut < 1` (Proposition 16.1.1). -/
theorem ox_offer_steady_exists_iff (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) :
    (∃ mh, E.ox_EulerRel mh mh) ↔ E.ox_Raut < 1 := by
  constructor
  · rintro ⟨mh, h⟩
    have := E.proposition_16_1_1_necessity (E.ox_ofSaving_isMonetary (mh := fun _ => mh)
      fun _ _ => h)
    rwa [hgn, hgm, mul_one] at this
  · intro hR
    obtain ⟨mh, ⟨h0, he, hroot⟩, -⟩ :=
      E.proposition_16_1_1_root (by rw [hgn, hgm, mul_one]; exact hR)
    exact ⟨mh, (E.ox_eulerRel_const_iff h0 he).2 hroot⟩

/-- Miao, p. 535: along a monetary equilibrium whose real balances vanish, `m̂_t → 0`, the
interest rate tends to `R_aut` and the gross inflation rate `p_{t+1}/p_t = q_t/q_{t+1}` tends to
`1/R_aut`, the inverse of the slope of the offer curve at the origin. -/
theorem ox_R_tendsto_Raut {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m)
    (h0 : Tendsto (E.ox_mhat q) atTop (𝓝 0)) :
    Tendsto (fun t => q (t + 1) / q t) atTop (𝓝 E.ox_Raut) ∧
      Tendsto (fun t => q t / q (t + 1)) atTop (𝓝 E.ox_Raut⁻¹) := by
  set x := E.ox_mhat q
  have hx1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 0) := h0.comp (tendsto_add_atTop_nat 1)
  have hc1 : ContinuousAt E.ox_P.ox_du (E.ox_e1 - 0) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by simpa using E.ox_e1_pos))
  have hc2 : ContinuousAt E.ox_P.ox_du (E.ox_e2 + E.ox_gn * 0) :=
    E.ox_P.ox_du_cont.continuousAt (Ioi_mem_nhds (by simpa using E.ox_e2_pos))
  have hp2 := E.ox_P.ox_du_pos _ E.ox_e2_pos
  have hβ := E.ox_P.ox_β_pos
  have hlhs : Tendsto (fun t => E.ox_P.ox_du (E.ox_e1 - x t) /
      (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * x (t + 1)))) atTop
      (𝓝 (E.ox_P.ox_du (E.ox_e1 - 0) / (E.ox_P.ox_β * E.ox_P.ox_du (E.ox_e2 + E.ox_gn * 0)))) :=
    (hc1.tendsto.comp (h0.const_sub _)).div
      ((hc2.tendsto.comp ((hx1.const_mul _).const_add _)).const_mul _) (by simpa using
        (mul_pos hβ hp2).ne')
  simp only [sub_zero, mul_zero, add_zero] at hlhs
  have hR : Tendsto (fun t => q (t + 1) / q t) atTop (𝓝 E.ox_Raut) := by
    refine hlhs.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact (E.eq_16_6 h ht).1
  refine ⟨hR, ?_⟩
  have hRa : E.ox_Raut ≠ 0 := by
    unfold ox_Raut; have := E.ox_P.ox_du_pos _ E.ox_e1_pos; positivity
  refine (hR.inv₀ hRa).congr' ?_
  filter_upwards with t
  rw [inv_div]

end OXEconomy

/-- Local stability of a steady state (Miao, p. 535, Figure 16.3): if `f(x*) = x*` and
`|f'(x*)| < 1`, every path `x_{n+1} = f(x_n)` starting close to `x*` stays at least as close
and converges to `x*`. -/
theorem ox_fixed_stable {f : ℝ → ℝ} {xs f' : ℝ} (hfix : f xs = xs) (hf : HasDerivAt f f' xs)
    (hlt : |f'| < 1) : ∃ δ > 0, ∀ x0, |x0 - xs| < δ →
      (∀ n, |f^[n] x0 - xs| ≤ |x0 - xs|) ∧ Tendsto (fun n => f^[n] x0) atTop (𝓝 xs) := by
  set k := (|f'| + 1) / 2
  have hk1 : k < 1 := by simp only [k]; linarith
  have hk0 : 0 ≤ k := by simp only [k]; positivity
  have hε : 0 < k - |f'| := by simp only [k]; linarith
  have ho := (hasDerivAt_iff_isLittleO.1 hf).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ho
  have hstep : ∀ x, |x - xs| < δ → |f x - xs| ≤ k * |x - xs| := fun x hx => by
    have h := hball (show dist x xs < δ by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |f x - xs| ≤ |f x - xs - (x - xs) * f'| + |(x - xs) * f'| := by
      have := abs_add_le (f x - xs - (x - xs) * f') ((x - xs) * f')
      simpa using this
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (x - xs)]
  refine ⟨δ, hδ, fun x0 hx0 => ?_⟩
  have hiter : ∀ n, |f^[n] x0 - xs| ≤ k ^ n * |x0 - xs| := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have hlt' : |f^[n] x0 - xs| < δ :=
        lt_of_le_of_lt (ih.trans (mul_le_of_le_one_left (abs_nonneg _)
          (pow_le_one₀ hk0 hk1.le))) hx0
      rw [Function.iterate_succ_apply']
      calc |f (f^[n] x0) - xs| ≤ k * |f^[n] x0 - xs| := hstep _ hlt'
        _ ≤ k * (k ^ n * |x0 - xs|) := mul_le_mul_of_nonneg_left ih hk0
        _ = k ^ (n + 1) * |x0 - xs| := by ring
  refine ⟨fun n => (hiter n).trans (mul_le_of_le_one_left (abs_nonneg _)
    (pow_le_one₀ hk0 hk1.le)), ?_⟩
  have hk : Tendsto (fun n => k ^ n * |x0 - xs|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk1).mul_const |x0 - xs|
  have : Tendsto (fun n => f^[n] x0 - xs) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by simpa [Real.norm_eq_abs] using hiter n) hk
  simpa using this.add_const xs

/-- Instability of a steady state (Miao, p. 534, Figure 16.2): if `f(x*) = x*` and
`|f'(x*)| > 1`, every path starting at `x₀ ≠ x*` eventually leaves a fixed neighbourhood. -/
theorem ox_fixed_unstable {f : ℝ → ℝ} {xs f' : ℝ} (hfix : f xs = xs) (hf : HasDerivAt f f' xs)
    (hgt : 1 < |f'|) : ∃ δ > 0, ∀ x0, x0 ≠ xs → ∃ n, δ ≤ |f^[n] x0 - xs| := by
  set k := (|f'| + 1) / 2
  have hk1 : 1 < k := by simp only [k]; linarith
  have hε : 0 < |f'| - k := by simp only [k]; linarith
  have ho := (hasDerivAt_iff_isLittleO.1 hf).def hε
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ho
  have hstep : ∀ x, |x - xs| < δ → k * |x - xs| ≤ |f x - xs| := fun x hx => by
    have h := hball (show dist x xs < δ by rwa [Real.dist_eq])
    simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
    have h2 : |(x - xs) * f'| ≤ |f x - xs| + |f x - xs - (x - xs) * f'| := by
      have := abs_add_le (f x - xs) ((x - xs) * f' - (f x - xs))
      have e : (f x - xs) + ((x - xs) * f' - (f x - xs)) = (x - xs) * f' := by ring
      rwa [e, abs_sub_comm ((x - xs) * f')] at this
    rw [abs_mul] at h2
    nlinarith [abs_nonneg (x - xs)]
  refine ⟨δ, hδ, fun x0 hx0 => ?_⟩
  by_contra hall
  push Not at hall
  have hiter : ∀ n, k ^ n * |x0 - xs| ≤ |f^[n] x0 - xs| := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc k ^ (n + 1) * |x0 - xs| = k * (k ^ n * |x0 - xs|) := by ring
        _ ≤ k * |f^[n] x0 - xs| := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ |f (f^[n] x0) - xs| := hstep _ (hall n)
  have hpos : 0 < |x0 - xs| := abs_pos.2 (sub_ne_zero.2 hx0)
  have htend : Tendsto (fun n => k ^ n * |x0 - xs|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hk1).atTop_mul_const hpos
  obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop δ).exists
  linarith [hiter n, hall n]

/-- **Correction** (Miao, p. 534: "unstable iff `|dm_{t+1}/dm_t| > 1`"): `f(x) = x + x³` has the
fixed point `0` with `f'(0) = 1`, yet every path from `x₀ > 0` leaves every bounded set, so `0`
is unstable without `|f'(0)| > 1`. -/
theorem ox_unstable_counterexample :
    HasDerivAt (fun x : ℝ => x + x ^ 3) 1 0 ∧ ∀ x0 : ℝ, 0 < x0 → ∀ B : ℝ, ∃ n,
      B < (fun x : ℝ => x + x ^ 3)^[n] x0 := by
  refine ⟨?_, ?_⟩
  · have h : HasDerivAt (fun x : ℝ => x + x ^ 3) (1 + (3 : ℕ) * (0 : ℝ) ^ (3 - 1)) 0 :=
      (hasDerivAt_id' (0 : ℝ)).add (hasDerivAt_pow 3 (0 : ℝ))
    convert h using 1
    norm_num
  intro x0 hx0 B
  set f := fun x : ℝ => x + x ^ 3
  have hiter : ∀ n : ℕ, x0 + n * x0 ^ 3 ≤ f^[n] x0 := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hge : x0 ≤ f^[n] x0 := by
        have : (0 : ℝ) ≤ n * x0 ^ 3 := by positivity
        linarith
      have : x0 ^ 3 ≤ (f^[n] x0) ^ 3 := pow_le_pow_left₀ hx0.le hge 3
      simp only [f]; push_cast; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - x0) / x0 ^ 3)
  refine ⟨n, ?_⟩
  have h3 : 0 < x0 ^ 3 := by positivity
  rw [div_lt_iff₀ h3] at hn
  linarith [hiter n]

namespace OXEconomy

variable (E : OXEconomy)

/-- Miao, p. 535 (indeterminacy): if the equilibrium relation is given near a monetary steady
state `m*` by a map `f` (every `(a, f a)` with `a` near `m*` solves the saving difference
equation) with `|f'(m*)| < 1`, then for every `m₁` close to `m*` the path `m̂_t = f^{t−1}(m₁)` is a
monetary equilibrium converging to `m*`: a continuum of equilibria. -/
theorem ox_indeterminacy {f : ℝ → ℝ} {ms f' r : ℝ} (hr : 0 < r) (hfix : f ms = ms)
    (hf : HasDerivAt f f' ms) (hlt : |f'| < 1)
    (hrel : ∀ a, |a - ms| < r → E.ox_EulerRel a (f a)) :
    ∃ δ > 0, ∀ m1, |m1 - ms| < δ →
      E.ox_IsMonetary (E.ox_qOf fun t => f^[t - 1] m1) (fun t => E.ox_e1 - f^[t - 1] m1)
        (fun t => E.ox_e2 + E.ox_gn * f^[t + 1 - 1] m1) (fun t => E.ox_M t / E.ox_N t) ∧
      Tendsto (fun n => f^[n] m1) atTop (𝓝 ms) := by
  obtain ⟨δ, hδ, hst⟩ := ox_fixed_stable hfix hf hlt
  refine ⟨min δ r, lt_min hδ hr, fun m1 hm1 => ?_⟩
  obtain ⟨hstay, htend⟩ := hst m1 (lt_of_lt_of_le hm1 (min_le_left _ _))
  refine ⟨E.ox_ofSaving_isMonetary (mh := fun t => f^[t - 1] m1) fun t ht => ?_, htend⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Function.iterate_succ_apply']
  exact hrel _ (lt_of_le_of_lt (hstay s) (lt_of_lt_of_le hm1 (min_le_right _ _)))

/-- Miao, pp. 535–536 (Figure 16.4, a two-period cycle): if `(m_a, m_b)` and `(m_b, m_a)` both
solve the saving difference equation, real balances alternating `m_a, m_b, m_a, …` form a
monetary equilibrium. -/
theorem ox_two_cycle {ma mb : ℝ} (hab : E.ox_EulerRel ma mb) (hba : E.ox_EulerRel mb ma) :
    E.ox_IsMonetary (E.ox_qOf fun t => if Even t then mb else ma)
      (fun t => E.ox_e1 - if Even t then mb else ma)
      (fun t => E.ox_e2 + E.ox_gn * if Even (t + 1) then mb else ma)
      (fun t => E.ox_M t / E.ox_N t) := by
  refine E.ox_ofSaving_isMonetary (mh := fun t => if Even t then mb else ma) fun t _ => ?_
  rcases Nat.even_or_odd t with he | ho
  · have : ¬ Even (t + 1) := Nat.not_even_iff_odd.2 he.add_one
    simp only [he, this, ↓reduceIte]; exact hba
  · have : Even (t + 1) := ho.add_one
    have hne : ¬ Even t := Nat.not_even_iff_odd.2 ho
    simp only [hne, this, ↓reduceIte]; exact hab

end OXEconomy

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pareto optimality in the exchange economy

Miao, §16.1, pp. 538–544.

* **Definition 16.1.1** (feasibility (16.9), equivalent to (16.3): `definition_16_1_1`),
  **Definition 16.1.2** (`ox_ParetoOptimal`), **Definition 16.1.3** (`ox_IsStationary`).
* The general stationary criterion behind Propositions 16.1.2–16.1.3: a feasible stationary
  allocation `(c₁, c₂)` with `R = u'(c₁)/(βu'(c₂))` is Pareto optimal iff `R ≥ g_n`
  (`ox_stationary_optimal`, `ox_stationary_not_optimal`, `ox_stationary_optimal_iff`). The
  steps of the book's proof: the perturbations `ε_t = c₁ − c̃_t^t` satisfy `ε_t ≥ 0` (16.10)
  (`eq_16_10`), `g_nε_{t+1} ≥ Rε_t` with strict inequality when `ε_t ≠ 0` (the content of
  `c̄ − e₂ = ε(R_aut + f(ε))`, `f(ε) > 0`: `eq_16_11`), and grow geometrically
  (`ox_eps_geometric`); the transfer scheme `f(ε) = u(e₁ − ε) + βu(e₂ + g_nε)` with
  `f'(0) = −u'(e₁) + βg_nu'(e₂)` (`proposition_16_1_2_transfer`).
* **Proposition 16.1.2**: autarky is optimal iff `R_aut ≥ g_n` (`proposition_16_1_2`).
* (16.12) (`eq_16_12`), (16.13) (`eq_16_13`), **Proposition 16.1.3** (`proposition_16_1_3`),
  and the steps of the book's necessity proof (`proposition_16_1_3_steps`).
* Balasko–Shell (Miao, pp. 542–544): `∏_{s=1}^t R_{s+1} = 1/p_{t+1}` when `p₁ = 1`, so the two
  forms of the criterion agree (`ox_balasko_shell_prod`, `ox_balasko_shell_equiv`); the
  compensating transfers `δ_t = δ₀∏R_{s+1}` (`ox_balasko_shell_transfers`); and the criterion
  for stationary allocations with constant population (`ox_balasko_shell_stationary`). The
  general Balasko–Shell theorem is cited, not proved, by the book; it is not formalised.

**Departures.** (i) Feasible allocations have positive consumption. (ii) The book's
sufficiency proof for Proposition 16.1.2 starts from the first date at which the alternative
allocation differs and represents the indifference curve as `h(c₁) = h(e₁) + (e₁ − c₁)(−h'(e₁) +
f(e₁ − c₁))` (16.11). Here the same estimate is obtained from strict concavity directly: the
tangent-line inequality gives `g_nε_{t+1} ≥ R_autε_t` (strict for `ε_t ≠ 0`) and a uniform chord
bound (`OXPrefs.ox_chord`) replaces `f(ε_{t+j}) ≥ f(ε_{t+1})`. (iii) The necessity half of
Proposition 16.1.3 is proved by the `ε`-transfer of Proposition 16.1.2 rather than by revealed
preference (Figure 16.5); the book's steps (the budget line is flatter, the initial old gain)
are recorded in `proposition_16_1_3_steps`.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- **Definition 16.1.1** (Miao, p. 538): an allocation (`cy t = c_t^t`, `co t = c_{t+1}^t`,
`co 0 = c₁⁰`) is feasible if consumption is positive and (16.9) holds:
`g_n c_t^t + c_t^{t−1} = g_n e₁ + e₂`, `t ≥ 1`. -/
def ox_Feasible (cy co : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 < cy t) ∧ (∀ t, 0 < co t) ∧
    ∀ t, 1 ≤ t → E.ox_gn * cy t + co (t - 1) = E.ox_gn * E.ox_e1 + E.ox_e2

/-- **Definition 16.1.1** (Miao, p. 538): (16.3) is equivalent to (16.9). -/
theorem definition_16_1_1 (cy co : ℕ → ℝ) :
    (∀ t, 1 ≤ t → E.ox_N t * cy t + E.ox_N (t - 1) * co (t - 1) =
      E.ox_N t * E.ox_e1 + E.ox_N (t - 1) * E.ox_e2) ↔
    ∀ t, 1 ≤ t → E.ox_gn * cy t + co (t - 1) = E.ox_gn * E.ox_e1 + E.ox_e2 := by
  refine forall_congr' fun t => imp_congr_right fun ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel, E.ox_N_succ]
  have hN := E.ox_N_pos s
  constructor
  · intro h
    have : E.ox_N s * (E.ox_gn * cy (s + 1) + co s) =
        E.ox_N s * (E.ox_gn * E.ox_e1 + E.ox_e2) := by linarith
    exact mul_left_cancel₀ hN.ne' this
  · intro h
    linear_combination E.ox_N s * h

/-- **Definition 16.1.2** (Miao, p. 539): a feasible allocation is Pareto optimal if no feasible
allocation gives the initial old at least as much consumption and every generation `t ≥ 1` at
least as much utility, with one strict inequality. -/
def ox_ParetoOptimal (cy co : ℕ → ℝ) : Prop :=
  E.ox_Feasible cy co ∧ ¬ ∃ cy' co' : ℕ → ℝ, E.ox_Feasible cy' co' ∧ co 0 ≤ co' 0 ∧
    (∀ t, 1 ≤ t → E.ox_EU (cy t) (co t) ≤ E.ox_EU (cy' t) (co' t)) ∧
    (co 0 < co' 0 ∨ ∃ t, 1 ≤ t ∧ E.ox_EU (cy t) (co t) < E.ox_EU (cy' t) (co' t))

/-- **Definition 16.1.3** (Miao, p. 539): an allocation is stationary, `c_t^t = c_y` and
`c_{t+1}^t = c_o` for all `t ≥ 1` (`c₁⁰` unrestricted). -/
def ox_IsStationary (cy co : ℕ → ℝ) (c1 c2 : ℝ) : Prop :=
  ∀ t, 1 ≤ t → cy t = c1 ∧ co t = c2

/-- Miao, (16.12), p. 541: a stationary allocation with positive consumption is feasible iff
`c₁ + c₂/g_n = e₁ + e₂/g_n` and `c₁⁰ = c₂`. -/
theorem eq_16_12 {cy co : ℕ → ℝ} {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2)
    (h1 : 0 < c1) (h2 : 0 < c2) :
    E.ox_Feasible cy co ↔ c1 + c2 / E.ox_gn = E.ox_e1 + E.ox_e2 / E.ox_gn ∧ co 0 = c2 := by
  have hgn := E.ox_gn_pos
  constructor
  · rintro ⟨-, -, hf⟩
    have hf1 := hf 1 le_rfl
    have hf2 := hf 2 (by omega)
    simp only [Nat.sub_self, Nat.add_one_sub_one] at hf1 hf2
    rw [(hs 1 le_rfl).1] at hf1
    rw [(hs 2 (by omega)).1, (hs 1 le_rfl).2] at hf2
    refine ⟨?_, by linarith⟩
    field_simp
    linarith
  · rintro ⟨hl, h0⟩
    have hl' : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2 := by
      field_simp at hl; linarith
    refine ⟨fun t ht => (hs t ht).1 ▸ h1, fun t => ?_, fun t ht => ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, h0]; exact h2
      · rw [(hs t h).2]; exact h2
    · rw [(hs t ht).1]
      rcases Nat.eq_zero_or_pos (t - 1) with h | h
      · rw [h, h0]; exact hl'
      · rw [(hs (t - 1) h).2]; exact hl'

/-- Feasibility relative to a feasible stationary `(c₁, c₂)`: the old's consumption is
`c̃_{t+1}^t = c₂ + g_n(c₁ − c̃_{t+1}^{t+1})` (Miao, p. 540, "since `C̃` is feasible"). -/
theorem ox_feasible_old {c1 c2 : ℝ}
    (hl : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2)
    {cy' co' : ℕ → ℝ} (hF : E.ox_Feasible cy' co') (t : ℕ) :
    co' t = c2 + E.ox_gn * (c1 - cy' (t + 1)) := by
  have := hF.2.2 (t + 1) (by omega)
  simp only [Nat.add_sub_cancel] at this
  linarith

/-- Miao, (16.11), p. 540 (the content of (16.11) and of
`c̃_{t+2}^{t+1} − e₂ ≥ ε_{t+1}[R_aut + f(ε_{t+1})]`): if a generation is not worse off than at the
stationary `(c₁, c₂)`, then with `R = u'(c₁)/(βu'(c₂))`, `ε = c₁ − c̃₁`:
`c̃₂ − c₂ ≥ Rε`, strictly if `ε ≠ 0`. -/
theorem eq_16_11 {c1 c2 x y : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (hx : 0 < x) (hy : 0 < y)
    (hU : E.ox_EU c1 c2 ≤ E.ox_EU x y) :
    E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) * (c1 - x) ≤ y - c2 ∧
      (x ≠ c1 → E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) * (c1 - x) < y - c2) := by
  have hβ := E.ox_P.ox_β_pos
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hk : 0 < E.ox_P.ox_β * E.ox_P.ox_du c2 := mul_pos hβ hd2
  have t2 := mul_le_mul_of_nonneg_left (E.ox_P.ox_tangent h2 hy) hβ.le
  unfold ox_EU OXPrefs.ox_U at hU
  have key : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) * (c1 - x) =
      E.ox_P.ox_du c1 * (c1 - x) / (E.ox_P.ox_β * E.ox_P.ox_du c2) := by ring
  rw [key]
  constructor
  · rw [div_le_iff₀ hk]
    have t1 := E.ox_P.ox_tangent h1 hx
    nlinarith
  · intro hne
    rw [div_lt_iff₀ hk]
    have t1 := E.ox_P.ox_tangent_strict h1 hx hne
    nlinarith

/-- Miao, p. 540 (geometric growth of the perturbations): given `0 < ε₀ < c₁`, there is
`ρ > u'(c₁)/(βu'(c₂))` such that whenever a generation is not worse off than at `(c₁, c₂)` with
`ε = c₁ − c̃₁ ≥ ε₀`, `c̃₂ − c₂ ≥ ρε`. -/
theorem ox_eps_geometric {c1 c2 ε₀ : ℝ} (h2 : 0 < c2) (hε₀ : 0 < ε₀) (hε₀c : ε₀ < c1) :
    ∃ ρ, E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) < ρ ∧ ∀ x y, 0 < x → 0 < y →
      ε₀ ≤ c1 - x → E.ox_EU c1 c2 ≤ E.ox_EU x y → ρ * (c1 - x) ≤ y - c2 := by
  obtain ⟨κ, hκ, hch⟩ := E.ox_P.ox_chord hε₀ hε₀c
  have hβ := E.ox_P.ox_β_pos
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hk : 0 < E.ox_P.ox_β * E.ox_P.ox_du c2 := mul_pos hβ hd2
  refine ⟨κ / (E.ox_P.ox_β * E.ox_P.ox_du c2), div_lt_div_of_pos_right hκ hk,
    fun x y hx hy hε hU => ?_⟩
  have hc := hch (c1 - x) hε (by linarith)
  rw [sub_sub_cancel] at hc
  have t2 := mul_le_mul_of_nonneg_left (E.ox_P.ox_tangent h2 hy) hβ.le
  unfold ox_EU OXPrefs.ox_U at hU
  rw [div_mul_eq_mul_div, div_le_iff₀ hk]
  nlinarith

/-- The perturbations in the sufficiency proof of Proposition 16.1.2: with `R ≥ g_n`, the
sequence `ε_t = c₁ − c̃_t^t` is nonnegative and nondecreasing (Miao, (16.10), p. 539). -/
theorem eq_16_10 {cy co : ℕ → ℝ} {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2)
    (h1 : 0 < c1) (h2 : 0 < c2) (h0 : co 0 = c2)
    (hl : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2)
    (hR : E.ox_gn ≤ E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2))
    {cy' co' : ℕ → ℝ} (hF : E.ox_Feasible cy' co') (h0' : co 0 ≤ co' 0)
    (hU : ∀ t, 1 ≤ t → E.ox_EU (cy t) (co t) ≤ E.ox_EU (cy' t) (co' t)) (n : ℕ) :
    0 ≤ c1 - cy' (n + 1) ∧ c1 - cy' (n + 1) ≤ c1 - cy' (n + 2) := by
  have hgn := E.ox_gn_pos
  have hco := E.ox_feasible_old hl hF
  have hstep : ∀ n, 0 ≤ c1 - cy' (n + 1) → c1 - cy' (n + 1) ≤ c1 - cy' (n + 2) := fun n hn => by
    have hUn := hU (n + 1) (by omega)
    rw [(hs (n + 1) (by omega)).1, (hs (n + 1) (by omega)).2] at hUn
    have := (E.eq_16_11 h1 h2 (hF.1 (n + 1) (by omega)) (hF.2.1 (n + 1)) hUn).1
    rw [hco (n + 1)] at this
    have : E.ox_gn * (c1 - cy' (n + 1)) ≤ E.ox_gn * (c1 - cy' (n + 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hR hn]
    exact le_of_mul_le_mul_left this hgn
  have hnn : ∀ n, 0 ≤ c1 - cy' (n + 1) := fun n => by
    induction n with
    | zero =>
      have := hco 0
      rw [h0] at h0'
      nlinarith
    | succ n ih => exact ih.trans (hstep n ih)
  exact ⟨hnn n, hstep n (hnn n)⟩

/-- Miao, pp. 539–540 (the sufficiency argument of Proposition 16.1.2, for any feasible stationary
allocation): if `(c₁, c₂)` is feasible and `R = u'(c₁)/(βu'(c₂)) ≥ g_n`, it is Pareto optimal. -/
theorem ox_stationary_optimal {cy co : ℕ → ℝ} {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2)
    (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co)
    (hR : E.ox_gn ≤ E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2)) :
    E.ox_ParetoOptimal cy co := by
  obtain ⟨hl0, h0⟩ := (E.eq_16_12 hs h1 h2).1 hF
  have hgn := E.ox_gn_pos
  have hl : E.ox_gn * c1 + c2 = E.ox_gn * E.ox_e1 + E.ox_e2 := by
    field_simp at hl0; linarith
  refine ⟨hF, ?_⟩
  rintro ⟨cy', co', hF', h0', hU, hstrict⟩
  have hco := E.ox_feasible_old hl hF'
  set ε := fun n : ℕ => c1 - cy' (n + 1)
  have hε := E.eq_16_10 hs h1 h2 h0 hl hR hF' h0' hU
  have hεlt : ∀ n, ε n < c1 := fun n => by
    simp only [ε]; linarith [hF'.1 (n + 1) (by omega)]
  -- all perturbations vanish
  have hzero : ∀ n, ε n = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs0⟩ := hcon
    have hpos : 0 < ε s := lt_of_le_of_ne (hε s).1 (Ne.symm hs0)
    have hmono : ∀ j, ε s ≤ ε (s + j) := fun j => by
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact ih.trans (by simpa [ε, add_assoc] using (hε (s + j)).2)
    obtain ⟨ρ, hρ, hgeo⟩ := E.ox_eps_geometric h2 hpos (hεlt s)
    set k := ρ / E.ox_gn
    have hk : 1 < k := (lt_div_iff₀ hgn).2 (by linarith)
    have hgrow : ∀ j, k ^ j * ε s ≤ ε (s + j) := fun j => by
      induction j with
      | zero => simp
      | succ j ih =>
        have hUj := hU (s + j + 1) (by omega)
        rw [(hs (s + j + 1) (by omega)).1, (hs (s + j + 1) (by omega)).2] at hUj
        have := hgeo _ _ (hF'.1 (s + j + 1) (by omega)) (hF'.2.1 (s + j + 1)) (hmono j) hUj
        rw [hco (s + j + 1)] at this
        have h3 : k * ε (s + j) ≤ ε (s + (j + 1)) := by
          simp only [k, ε, ← add_assoc]
          rw [div_mul_eq_mul_div, div_le_iff₀ hgn]
          linarith
        calc k ^ (j + 1) * ε s = k * (k ^ j * ε s) := by ring
          _ ≤ k * ε (s + j) := mul_le_mul_of_nonneg_left ih (by linarith)
          _ ≤ ε (s + (j + 1)) := h3
    have htend : Tendsto (fun j => k ^ j * ε s) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const hpos
    obtain ⟨j, hj⟩ := (htend.eventually_gt_atTop c1).exists
    linarith [hgrow j, hεlt (s + j)]
  have hcy : ∀ t, 1 ≤ t → cy' t = c1 := fun t ht => by
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    have := hzero n; simp only [ε] at this; linarith
  have hco' : ∀ t, co' t = c2 := fun t => by
    rw [hco t, hcy (t + 1) (by omega), sub_self, mul_zero, add_zero]
  rcases hstrict with h | ⟨t, ht, h⟩
  · rw [hco' 0, h0] at h; exact lt_irrefl _ h
  · rw [hcy t ht, hco' t, (hs t ht).1, (hs t ht).2] at h; exact lt_irrefl _ h

/-- Miao, p. 541 (the transfer scheme): `f(ε) = u(c₁ − ε) + βu(c₂ + g_nε)` has
`f'(0) = −u'(c₁) + βg_nu'(c₂)`, positive when `g_n > u'(c₁)/(βu'(c₂))`; hence some small `ε > 0`
makes every generation better off. -/
theorem proposition_16_1_2_transfer {c1 c2 : ℝ} (h1 : 0 < c1) (h2 : 0 < c2)
    (hR : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) < E.ox_gn) :
    HasDerivAt (fun ε => E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε))
        (-E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2) 0 ∧
      0 < -E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2 ∧
      ∃ ε, 0 < ε ∧ ε < c1 ∧ E.ox_EU c1 c2 < E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε) := by
  have hβ := E.ox_P.ox_β_pos
  have hd2 := E.ox_P.ox_du_pos _ h2
  have hl1 : HasDerivAt (fun s : ℝ => c1 - s) (-1) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_sub c1
  have hl2 : HasDerivAt (fun s : ℝ => c2 + E.ox_gn * s) E.ox_gn 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul E.ox_gn).const_add c2
  have hu1 : HasDerivAt E.ox_P.ox_u (E.ox_P.ox_du c1) ((fun s : ℝ => c1 - s) 0) := by
    simpa using E.ox_P.ox_hasDeriv c1 h1
  have hu2 : HasDerivAt E.ox_P.ox_u (E.ox_P.ox_du c2) ((fun s : ℝ => c2 + E.ox_gn * s) 0) := by
    simpa using E.ox_P.ox_hasDeriv c2 h2
  have hd : HasDerivAt (fun ε => E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε))
      (-E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2) 0 := by
    have h0 : HasDerivAt (fun ε => E.ox_EU (c1 - ε) (c2 + E.ox_gn * ε))
        (E.ox_P.ox_du c1 * -1 + E.ox_P.ox_β * (E.ox_P.ox_du c2 * E.ox_gn)) 0 :=
      (hu1.comp 0 hl1).add ((hu2.comp 0 hl2).const_mul E.ox_P.ox_β)
    exact h0.congr_deriv (by ring)
  have hpos : 0 < -E.ox_P.ox_du c1 + E.ox_P.ox_β * E.ox_gn * E.ox_P.ox_du c2 := by
    rw [div_lt_iff₀ (mul_pos hβ hd2)] at hR; linarith
  refine ⟨hd, hpos, ?_⟩
  have hev := (hd.tendsto_slope_zero_right.eventually (lt_mem_nhds hpos)).and
    ((show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < c1 from mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h1)).and
      self_mem_nhdsWithin)
  obtain ⟨ε, hsl, hεc, hε0⟩ := hev.exists
  refine ⟨ε, hε0, hεc, ?_⟩
  simp only [zero_add, smul_eq_mul, sub_zero, mul_zero, add_zero] at hsl
  have := (mul_pos_iff_of_pos_left (inv_pos.2 (Set.mem_Ioi.1 hε0))).1 hsl
  linarith

/-- Miao, pp. 540–541 (necessity in Proposition 16.1.2, for any feasible stationary allocation):
if `R = u'(c₁)/(βu'(c₂)) < g_n` the transfer of `ε` from each young to the old is a Pareto
improvement. -/
theorem ox_stationary_not_optimal {cy co : ℕ → ℝ} {c1 c2 : ℝ}
    (hs : ox_IsStationary cy co c1 c2) (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co)
    (hR : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) < E.ox_gn) :
    ¬ E.ox_ParetoOptimal cy co := by
  obtain ⟨-, h0⟩ := (E.eq_16_12 hs h1 h2).1 hF
  obtain ⟨-, -, ε, hε0, hεc, hU⟩ := E.proposition_16_1_2_transfer h1 h2 hR
  have hgn := E.ox_gn_pos
  rintro ⟨-, hno⟩
  refine hno ⟨fun _ => c1 - ε, fun _ => c2 + E.ox_gn * ε, ⟨fun _ _ => by linarith,
    fun _ => by nlinarith, fun t _ => ?_⟩, ?_, fun t ht => ?_, Or.inl ?_⟩
  · have := (E.eq_16_12 hs h1 h2).1 hF
    field_simp at this; linarith [this.1]
  · rw [h0]; nlinarith
  · rw [(hs t ht).1, (hs t ht).2]; exact hU.le
  · rw [h0]; nlinarith

/-- Miao, pp. 539–541: a feasible stationary allocation is Pareto optimal iff
`u'(c₁)/(βu'(c₂)) ≥ g_n`. -/
theorem ox_stationary_optimal_iff {cy co : ℕ → ℝ} {c1 c2 : ℝ}
    (hs : ox_IsStationary cy co c1 c2) (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co) :
    E.ox_ParetoOptimal cy co ↔ E.ox_gn ≤ E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) :=
  ⟨fun h => not_lt.1 fun hlt => E.ox_stationary_not_optimal hs h1 h2 hF hlt h,
    E.ox_stationary_optimal hs h1 h2 hF⟩

/-- **Proposition 16.1.2** (Miao, p. 539): the nonmonetary equilibrium (autarky) is Pareto optimal
iff `R_aut ≥ g_n`. -/
theorem proposition_16_1_2 {q cy co m : ℕ → ℝ} (h : E.ox_IsNonmonetary q cy co m) :
    E.ox_ParetoOptimal cy co ↔ E.ox_gn ≤ E.ox_Raut := by
  obtain ⟨hy, h0⟩ := E.ox_nonmonetary_autarky h
  have hs : ox_IsStationary cy co E.ox_e1 E.ox_e2 := hy
  have hF : E.ox_Feasible cy co := by
    refine (E.eq_16_12 hs E.ox_e1_pos E.ox_e2_pos).2 ⟨rfl, h0⟩
  exact E.ox_stationary_optimal_iff hs E.ox_e1_pos E.ox_e2_pos hF

/-- Miao, (16.13), p. 542: in a stationary monetary equilibrium with real balances `m̂`
(`R = g_n/g_m`), every choice in a young agent's budget set satisfies
`c₁ + (g_m/g_n)c₂ ≤ e₁ + (g_m/g_n)e₂ + (g_m − 1)m̂`, with equality at the equilibrium allocation. -/
theorem eq_16_13 {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) {mh : ℝ}
    (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) {t : ℕ} (ht : 1 ≤ t) :
    (∀ c1 c2 m', E.ox_Budget q t c1 c2 m' → c1 + E.ox_gm / E.ox_gn * c2 ≤
      E.ox_e1 + E.ox_gm / E.ox_gn * E.ox_e2 + (E.ox_gm - 1) * mh) ∧
      cy t + E.ox_gm / E.ox_gn * co t =
        E.ox_e1 + E.ox_gm / E.ox_gn * E.ox_e2 + (E.ox_gm - 1) * mh := by
  have hR := E.ox_stationary_R h hc ht
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  have hqt := h.2 t ht
  have hqt1 := h.2 (t + 1) (by omega)
  have hinv : 1 / (q (t + 1) / q t) = E.ox_gm / E.ox_gn := by rw [hR]; field_simp
  have hτ : q (t + 1) * E.ox_τ t / (q (t + 1) / q t) = (E.ox_gm - 1) * mh := by
    have hm1 := hc (t + 1) (by omega)
    unfold ox_mhat at hm1
    rw [E.ox_M_succ, E.ox_N_succ] at hm1
    rw [div_eq_mul_one_div, hinv]
    unfold ox_τ
    rw [← hm1]
    have := (E.ox_N_pos t).ne'
    field_simp
  obtain ⟨-, -, -, hcy, hco⟩ := (E.ox_monetary_alloc h).1 t ht
  refine ⟨fun c1 c2 m' hb => ?_, ?_⟩
  · have hl := E.ox_budget_line hqt hqt1 hb
    rw [div_eq_mul_one_div c2, hinv, add_div, hτ, div_eq_mul_one_div E.ox_e2, hinv] at hl
    linarith
  · rw [hcy, hco, hc t ht, hc (t + 1) (by omega)]
    field_simp
    ring

/-- Miao, p. 542 (the steps of the necessity proof of Proposition 16.1.3): with `g_m > 1` the
budget line (16.13), slope `−g_n/g_m`, is flatter than the feasibility line (16.12), slope `−g_n`;
and if `c̄₁ < ĉ₁` the initial old can be given strictly more, `e₂ + g_n(e₁ − c̄₁) > e₂ +
g_n(e₁ − ĉ₁)`. -/
theorem proposition_16_1_3_steps (hgm : 1 < E.ox_gm) {cb ch : ℝ} (hlt : cb < ch) :
    E.ox_gn / E.ox_gm < E.ox_gn ∧
      E.ox_e2 + E.ox_gn * (E.ox_e1 - ch) < E.ox_e2 + E.ox_gn * (E.ox_e1 - cb) := by
  have hgn := E.ox_gn_pos
  exact ⟨(div_lt_iff₀ (by linarith)).2 (by nlinarith), by nlinarith⟩

/-- **Proposition 16.1.3** (Miao, p. 541): given `R_aut g_m < g_n`, the stationary monetary
equilibrium is Pareto optimal iff `g_m ≤ 1`. Stated for every monetary equilibrium with a
stationary allocation (by `proposition_16_1_1` one exists exactly when `R_aut g_m < g_n`). -/
theorem proposition_16_1_3 (_hR : E.ox_Raut * E.ox_gm < E.ox_gn) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {c1 c2 : ℝ} (hs : ox_IsStationary cy co c1 c2) :
    E.ox_ParetoOptimal cy co ↔ E.ox_gm ≤ 1 := by
  have hgn := E.ox_gn_pos
  have hgm := E.ox_gm_pos
  obtain ⟨halloc, h0⟩ := E.ox_monetary_alloc h
  have hc : ∀ t, 1 ≤ t → E.ox_mhat q t = E.ox_e1 - c1 := fun t ht => by
    have := (halloc t ht).2.2.2.1; rw [(hs t ht).1] at this; linarith
  have h1 : 0 < c1 := (hs 1 le_rfl).1 ▸ h.1.2.1 1 le_rfl |>.1.2.1
  have h2 : 0 < c2 := (hs 1 le_rfl).2 ▸ h.1.2.1 1 le_rfl |>.1.2.2.1
  have hF : E.ox_Feasible cy co := by
    refine ⟨fun t ht => (h.1.2.1 t ht).1.2.1, fun t => ?_,
      (E.definition_16_1_1 cy co).1 h.1.2.2.2.2⟩
    rcases Nat.eq_zero_or_pos t with ht | ht
    · rw [ht, h0]
      have := (halloc 1 le_rfl).2.1
      nlinarith [E.ox_e2_pos]
    · exact (h.1.2.1 t ht).1.2.2.1
  have hRe : E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) = E.ox_gn / E.ox_gm := by
    have := E.eq_16_4 h (t := 1) le_rfl
    rw [(hs 1 le_rfl).1, (hs 1 le_rfl).2] at this
    rw [this, E.ox_stationary_R h hc le_rfl]
  rw [E.ox_stationary_optimal_iff hs h1 h2 hF, hRe, le_div_iff₀ hgm]
  constructor
  · intro hle; nlinarith
  · intro hle; nlinarith

/-- Miao, p. 543 (Balasko–Shell): with `p₁ = 1` and `R_{s+1} = p_s/p_{s+1}`,
`∏_{s=1}^t R_{s+1} = 1/p_{t+1}`. -/
theorem ox_balasko_shell_prod {p : ℕ → ℝ} (hp : ∀ t, 0 < p t) (h1 : p 1 = 1) (t : ℕ) :
    ∏ s ∈ Finset.Icc 1 t, p s / p (s + 1) = 1 / p (t + 1) := by
  induction t with
  | zero => simp [h1]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    have := (hp (n + 1)).ne'
    have := (hp (n + 1 + 1)).ne'
    field_simp

/-- Miao, p. 543 (Balasko–Shell): with `p₁ = 1`, `∑_t ∏_{s=1}^t R_{s+1} = ∞` iff
`∑_t 1/p_t = ∞` (for positive terms, divergence is failure of summability). -/
theorem ox_balasko_shell_equiv {p : ℕ → ℝ} (hp : ∀ t, 0 < p t) (h1 : p 1 = 1) :
    (¬ Summable fun t : ℕ => ∏ s ∈ Finset.Icc 1 (t + 1), p s / p (s + 1)) ↔
      ¬ Summable fun t : ℕ => 1 / p (t + 1) := by
  simp only [ox_balasko_shell_prod hp h1]
  rw [summable_nat_add_iff (f := fun t : ℕ => 1 / p (t + 1)) 1]

/-- Miao, pp. 543–544 (Balasko–Shell intuition): the transfer `δ_t` to generation `t` when old that
compensates for giving up `δ_{t−1}` when young, `δ_{t−1}u'(c_t^t) = δ_tβu'(c_{t+1}^t)`, is
`δ_t = δ₀∏_{s=1}^t R_{s+1}` with `R_{s+1} = u'(c_s^s)/(βu'(c_{s+1}^s))`. -/
theorem ox_balasko_shell_transfers {cy co δ : ℕ → ℝ} (hco : ∀ t, 0 < co t)
    (hδ : ∀ t, 1 ≤ t → δ (t - 1) * E.ox_P.ox_du (cy t) = δ t * E.ox_P.ox_β * E.ox_P.ox_du (co t))
    (t : ℕ) : δ t = δ 0 * ∏ s ∈ Finset.Icc 1 t,
      E.ox_P.ox_du (cy s) / (E.ox_P.ox_β * E.ox_P.ox_du (co s)) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc, ← ih]
    have h := hδ (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h
    have := (mul_pos E.ox_P.ox_β_pos (E.ox_P.ox_du_pos _ (hco (n + 1)))).ne'
    rw [mul_div_assoc', eq_div_iff this, h]
    ring

/-- Miao, p. 543 (Balasko–Shell for stationary allocations, `g_n = 1`): a feasible stationary
allocation is Pareto optimal iff `∑_t ∏_{s=1}^t R_{s+1} = ∑_t Rᵗ = ∞`. -/
theorem ox_balasko_shell_stationary (hgn : E.ox_gn = 1) {cy co : ℕ → ℝ} {c1 c2 : ℝ}
    (hs : ox_IsStationary cy co c1 c2) (h1 : 0 < c1) (h2 : 0 < c2) (hF : E.ox_Feasible cy co) :
    E.ox_ParetoOptimal cy co ↔
      ¬ Summable fun t : ℕ => (E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2)) ^ (t + 1) := by
  rw [E.ox_stationary_optimal_iff hs h1 h2 hF, hgn]
  have hR : 0 < E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2) :=
    div_pos (E.ox_P.ox_du_pos _ h1) (mul_pos E.ox_P.ox_β_pos (E.ox_P.ox_du_pos _ h2))
  rw [summable_nat_add_iff (f := fun t : ℕ =>
    (E.ox_P.ox_du c1 / (E.ox_P.ox_β * E.ox_P.ox_du c2)) ^ t) 1, summable_geometric_iff_norm_lt_one,
    Real.norm_eq_abs, abs_of_pos hR, not_lt]

end OXEconomy

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples 16.1.1 and 16.1.2

Miao, §16.1, pp. 536–537.

* The logarithmic economy (`u = ln`, `β = 1`, `g_m = 1`, any `g_n`): the saving difference
  equation is linear in `x_t = 1/m̂_t`, `x_{t+1} = (g_ne₁/e₂)x_t − 2g_n/e₂` (`ox_log_eulerRel`);
  every monetary equilibrium is `x_t = x* + cλ^{t−1}` with `c ≥ 0` (`ox_log_paths`), every such
  path is one (`ox_log_construct`), and paths with `c > 0` have `m̂_t → 0` (`ox_log_tendsto`).
  This is used again in Exercise 16.1.
* **Example 16.1.1** (`g_n = 1`, `N₀ = 1`): the price difference equation
  `p_te₁ − M = p_{t+1}e₂ + M` (`example_16_1_1_diffeq`), its general solution
  `p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` with `c ≥ 0` (`example_16_1_1_general`), every `c ≥ 0` gives a
  monetary equilibrium (`example_16_1_1_construct`); `c = 0` is the stationary monetary
  equilibrium; for `c > 0` the price level explodes, the allocation tends to autarky and gross
  inflation tends to `e₁/e₂ = 1/R_aut` (`example_16_1_1_explosive`). Figure 16.2 in this
  economy: no equilibrium starts to the right of `m* = (e₁ − e₂)/2`, a path of the difference
  equation that does leaves `(0, e₁)` (`example_16_1_1_right`), and equilibria starting to the
  left decrease to the nonmonetary steady state (`example_16_1_1_left`).
* **Example 16.1.2**: the high-interest-rate equilibrium `p_t = 1`, `c = 1/2`, `R = 1`
  (`example_16_1_2_high`); the low-interest-rate (autarky) equilibrium: `R_aut < 1`, the price
  system `p_t/p_{t+1} = R_aut` makes autarky optimal for every generation, prices explode, the
  present value of the aggregate endowment is infinite and autarky is not Pareto optimal
  (`example_16_1_2_low`).

**Corrections.** (i) Example 16.1.2 says the initial old have no money but money `M = 0.5 − ε`
is supplied for `t ≥ 1`; in the model of §16.1 (`M_t = g_mM_{t−1}`) this is the economy with
`M₀ = 0.5 − ε` held by the initial old and `g_m = 1`, which is what is formalised. (ii) In the
low-interest-rate equilibrium the price sequence `p₁ = 1`, `p_t/p_{t+1} = R_aut` with valued money
is not an equilibrium: the initial old would consume `ε + (0.5 − ε) = 0.5`, and (16.6) forces
`R_{t+1} > R_aut` in every monetary equilibrium (`example_16_1_2_not_monetary`). The
low-interest-rate equilibrium is the nonmonetary one (`p_t = ∞`); at the prices `p_t/p_{t+1} =
R_aut` every generation's optimal choice is autarky with zero money demand.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- The example economy is logarithmic with `β = 1` and `g_n = g_m = N₀ = 1`, `e₁ > e₂`: it
satisfies the hypotheses of Example 16.1.1. -/
theorem ox_exampleEconomy_log :
    ox_exampleEconomy.ox_P.ox_du = (fun c => c⁻¹) ∧ ox_exampleEconomy.ox_P.ox_β = 1 ∧
      ox_exampleEconomy.ox_gn = 1 ∧ ox_exampleEconomy.ox_gm = 1 ∧ ox_exampleEconomy.ox_N0 = 1 ∧
      ox_exampleEconomy.ox_e2 < ox_exampleEconomy.ox_e1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [ox_exampleEconomy]; norm_num

/-- With `u = ln`, `β = 1`: `R_aut = e₂/e₁`. -/
theorem ox_log_Raut (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1) :
    E.ox_Raut = E.ox_e2 / E.ox_e1 := by
  unfold ox_Raut; simp only [hdu, hβ, one_mul]
  have := E.ox_e1_pos.ne'; have := E.ox_e2_pos.ne'
  field_simp

/-- The logarithmic saving difference equation (Miao, p. 536): with `u = ln`, `β = 1`, `g_m = 1`
and `a, b ∈ (0, e₁)`, `(a, b)` solves the Euler relation iff
`1/b = (g_ne₁/e₂)(1/a) − 2g_n/e₂`. -/
theorem ox_log_eulerRel (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) {a b : ℝ} (ha : 0 < a) (hae : a < E.ox_e1) (hb : 0 < b)
    (hbe : b < E.ox_e1) :
    E.ox_EulerRel a b ↔ b⁻¹ = E.ox_gn * E.ox_e1 / E.ox_e2 * a⁻¹ - 2 * E.ox_gn / E.ox_e2 := by
  have he2 := E.ox_e2_pos
  have hgn := E.ox_gn_pos
  have h1 : E.ox_e1 - a ≠ 0 := by linarith
  have h2 : E.ox_e2 + E.ox_gn * b ≠ 0 := by nlinarith
  unfold ox_EulerRel
  simp only [hdu, hβ, hgm, one_mul]
  constructor
  · rintro ⟨-, -, -, -, h⟩
    field_simp at h ⊢
    linear_combination h
  · intro h
    refine ⟨ha, hae, hb, hbe, ?_⟩
    field_simp at h ⊢
    linear_combination h

/-- The fixed point `x* = 2g_n/(g_ne₁ − e₂)` and the root `λ = g_ne₁/e₂` of the logarithmic
difference equation satisfy `λx* − 2g_n/e₂ = x*`. -/
theorem ox_log_fixed (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) :
    E.ox_gn * E.ox_e1 / E.ox_e2 * (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2)) -
      2 * E.ox_gn / E.ox_e2 = 2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) := by
  have := E.ox_e2_pos.ne'
  have : E.ox_gn * E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
  field_simp
  ring

/-- Miao, pp. 536–537 and Exercise 16.1(c): in the logarithmic economy every monetary equilibrium
has `1/m̂_{n+1} = x* + cλⁿ` with `c ≥ 0`, `x* = 2g_n/(g_ne₁ − e₂)`, `λ = g_ne₁/e₂ > 1`. -/
theorem ox_log_paths (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    E.ox_e2 < E.ox_gn * E.ox_e1 ∧ ∃ c, 0 ≤ c ∧ ∀ n : ℕ, (E.ox_mhat q (n + 1))⁻¹ =
      2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) + c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n := by
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hgap : E.ox_e2 < E.ox_gn * E.ox_e1 := by
    have := E.proposition_16_1_1_necessity h
    rw [E.ox_log_Raut hdu hβ, hgm, mul_one, div_lt_iff₀ he1] at this
    linarith
  refine ⟨hgap, ?_⟩
  set lam := E.ox_gn * E.ox_e1 / E.ox_e2
  set xs := 2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2)
  have hlam : 1 < lam := (one_lt_div he2).2 hgap
  set y := fun n : ℕ => (E.ox_mhat q (n + 1))⁻¹
  have hsol : IsScalarSol lam (-(2 * E.ox_gn / E.ox_e2)) (fun _ => 1) y := fun n => by
    have hr := E.ox_monetary_eulerRel h (t := n + 1) (by omega)
    have := (E.ox_log_eulerRel hdu hβ hgm hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1).1 hr
    simp only [y, mul_one]; rw [this]; ring
  have hgen := (eq_1_3 hlam.ne' y).1 hsol
  have hxs : -(2 * E.ox_gn / E.ox_e2) / (1 - lam) = xs := by
    simp only [lam, xs]
    have : E.ox_gn * E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
    have : E.ox_e2 - E.ox_gn * E.ox_e1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hxs] at hgen
  refine ⟨y 0 - xs, ?_, fun n => (hgen n).trans (by ring)⟩
  by_contra hneg
  have hc : y 0 - xs < 0 := not_le.1 hneg
  have hpos : ∀ n, 0 < y n := fun n => by
    have := ((E.ox_monetary_alloc h).1 (n + 1) (by omega)).2.1
    exact inv_pos.2 this
  have ht : Tendsto (fun n : ℕ => (y 0 - xs) * lam ^ n) atTop atBot :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop_of_neg hc
  obtain ⟨n, hn⟩ := (ht.eventually_lt_atBot (-xs)).exists
  have := hpos n
  rw [hgen n] at this
  linarith

/-- Miao, p. 536 and Exercise 16.1(c): in the logarithmic economy with `e₂ < g_ne₁`, for every
`c ≥ 0` the path `m̂_t = 1/(x* + cλ^{t−1})` is a monetary equilibrium. -/
theorem ox_log_construct (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) {c : ℝ} (hc : 0 ≤ c) :
    E.ox_IsMonetary (E.ox_qOf fun t => (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
        c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹)
      (fun t => E.ox_e1 - (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
        c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹)
      (fun t => E.ox_e2 + E.ox_gn * (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
        c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t + 1 - 1))⁻¹)
      (fun t => E.ox_M t / E.ox_N t) := by
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hgn := E.ox_gn_pos
  have hfix := E.ox_log_fixed hgap
  set lam := E.ox_gn * E.ox_e1 / E.ox_e2
  set xs := 2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2)
  have hlam : 1 < lam := (one_lt_div he2).2 hgap
  have hxs : E.ox_e1⁻¹ < xs := by
    simp only [xs]
    rw [inv_lt_iff_one_lt_mul₀ he1, div_mul_eq_mul_div, one_lt_div (by linarith)]
    nlinarith
  have hbig : ∀ k : ℕ, E.ox_e1⁻¹ < xs + c * lam ^ k := fun k => by
    have : 0 ≤ c * lam ^ k := mul_nonneg hc (pow_nonneg (by linarith) k)
    linarith
  have hpos : ∀ k : ℕ, 0 < xs + c * lam ^ k := fun k =>
    lt_trans (inv_pos.2 he1) (hbig k)
  have hlt : ∀ k : ℕ, (xs + c * lam ^ k)⁻¹ < E.ox_e1 := fun k => by
    rw [inv_lt_comm₀ (hpos k) he1]; exact hbig k
  refine E.ox_ofSaving_isMonetary fun t ht => ?_
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine (E.ox_log_eulerRel hdu hβ hgm (inv_pos.2 (hpos s)) (hlt s) (inv_pos.2 (hpos (s + 1)))
    (hlt (s + 1))).2 ?_
  rw [inv_inv, inv_inv, pow_succ]
  linear_combination -hfix

/-- Paths with `c > 0` have real balances `m̂_t → 0`. -/
theorem ox_log_tendsto (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℕ => (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
      c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ (t - 1))⁻¹) atTop (𝓝 0) := by
  have hlam : 1 < E.ox_gn * E.ox_e1 / E.ox_e2 := (one_lt_div E.ox_e2_pos).2 hgap
  refine tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ ?_)
  exact ((tendsto_pow_atTop_atTop_of_one_lt hlam).comp (tendsto_sub_atTop_nat 1)).const_mul_atTop hc

/-- **Example 16.1.1** (Miao, p. 536): with `u = ln`, `β = 1`, `g_n = g_m = 1`, `N₀ = 1`,
`M = M₀`, every monetary equilibrium satisfies `p_te₁ − M = p_{t+1}e₂ + M` (`p_t = 1/q_t`). -/
theorem example_16_1_1_diffeq (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {t : ℕ} (ht : 1 ≤ t) :
    1 / q t * E.ox_e1 - E.ox_M0 = 1 / q (t + 1) * E.ox_e2 + E.ox_M0 := by
  have hr := E.ox_monetary_eulerRel h ht
  have hrel := (E.ox_log_eulerRel hdu hβ hgm hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1).1 hr
  have hmh : ∀ s, E.ox_mhat q s = q s * E.ox_M0 := fun s => by
    unfold ox_mhat ox_M ox_N; rw [hgm, hgn, hN]; simp
  rw [hmh, hmh, hgn, one_mul] at hrel
  have hq := h.2 t ht
  have hq1 := h.2 (t + 1) (by omega)
  have hM := E.ox_M0_pos
  have he2 := E.ox_e2_pos
  rw [mul_inv, mul_inv] at hrel
  have : 1 / q (t + 1) =
      E.ox_M0 * (E.ox_e1 / E.ox_e2 * ((q t)⁻¹ * E.ox_M0⁻¹) - 2 * 1 / E.ox_e2) := by
    rw [← hrel]; field_simp
  rw [this]
  field_simp
  ring

/-- **Example 16.1.1** (Miao, p. 536): the general solution. Every monetary equilibrium has
`p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` for `t ≥ 1`, with `c ≥ 0`. -/
theorem example_16_1_1_general (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) :
    E.ox_e2 < E.ox_e1 ∧ ∃ c, 0 ≤ c ∧ ∀ t, 1 ≤ t →
      1 / q t = 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t := by
  obtain ⟨hgap, c, hc, hx⟩ := E.ox_log_paths hdu hβ hgm h
  rw [hgn, one_mul] at hgap hx
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hM := E.ox_M0_pos
  refine ⟨hgap, E.ox_M0 * c * (E.ox_e2 / E.ox_e1), by positivity, fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hmh : E.ox_mhat q (n + 1) = q (n + 1) * E.ox_M0 := by
    unfold ox_mhat ox_M ox_N; rw [hgm, hgn, hN]; simp
  have hxn := hx n
  rw [hmh, mul_inv] at hxn
  have hq := (h.2 (n + 1) (by omega)).ne'
  have : 1 / q (n + 1) = E.ox_M0 * ((q (n + 1))⁻¹ * E.ox_M0⁻¹) := by field_simp
  rw [this, hxn, pow_succ]
  have : E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
  field_simp

/-- **Example 16.1.1** (Miao, p. 536): conversely every `c ≥ 0` gives a monetary equilibrium with
`p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` for `t ≥ 1`; `c = 0` is the stationary monetary equilibrium with
constant prices. -/
theorem example_16_1_1_construct (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) (he : E.ox_e2 < E.ox_e1)
    {c : ℝ} (hc : 0 ≤ c) : ∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m ∧ ∀ t, 1 ≤ t →
      1 / q t = 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t := by
  have he1 := E.ox_e1_pos
  have he2 := E.ox_e2_pos
  have hM := E.ox_M0_pos
  have hgap : E.ox_e2 < E.ox_gn * E.ox_e1 := by rw [hgn, one_mul]; exact he
  set c' := c * (E.ox_e1 / E.ox_e2) / E.ox_M0
  have hc' : 0 ≤ c' := by positivity
  refine ⟨_, _, _, _, E.ox_log_construct hdu hβ hgm hgap hc', fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  unfold ox_qOf ox_M ox_N
  simp only [hgn, hgm, hN, one_pow, mul_one, one_mul, Nat.add_sub_cancel, c']
  have : E.ox_e1 - E.ox_e2 ≠ 0 := by linarith
  rw [pow_succ]
  field_simp

/-- **Example 16.1.1** (Miao, pp. 536–537; Figure 16.2): along a monetary equilibrium with
`c > 0` the price level explodes, `p_t → ∞`, money becomes worthless (`m̂_t → 0`), the allocation
tends to autarky, and gross inflation `p_{t+1}/p_t` tends to `e₁/e₂ = 1/R_aut`, the inverse of the
slope of the offer curve at the origin. -/
theorem example_16_1_1_explosive (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) (hN : E.ox_N0 = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {c : ℝ} (hc : 0 < c)
    (hp : ∀ t, 1 ≤ t → 1 / q t = 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t) :
    Tendsto (fun t => 1 / q t) atTop atTop ∧ Tendsto (E.ox_mhat q) atTop (𝓝 0) ∧
      Tendsto cy atTop (𝓝 E.ox_e1) ∧ Tendsto co atTop (𝓝 E.ox_e2) ∧
      Tendsto (fun t => q t / q (t + 1)) atTop (𝓝 (E.ox_e1 / E.ox_e2)) := by
  have he := (E.example_16_1_1_general hdu hβ hgn hgm hN h).1
  have he2 := E.ox_e2_pos
  have hlam : 1 < E.ox_e1 / E.ox_e2 := (one_lt_div he2).2 he
  have hev : (fun t => 2 * E.ox_M0 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ t) =ᶠ[atTop]
      fun t => 1 / q t := by
    filter_upwards [eventually_ge_atTop 1] with t ht using (hp t ht).symm
  have hP : Tendsto (fun t => 1 / q t) atTop atTop :=
    (tendsto_atTop_add_const_left _ _
      ((tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hc)).congr' hev
  have hmh : ∀ t, E.ox_mhat q t = E.ox_M0 * (1 / q t)⁻¹ := fun t => by
    unfold ox_mhat ox_M ox_N; rw [hgm, hgn, hN]; simp; ring
  have h0 : Tendsto (E.ox_mhat q) atTop (𝓝 0) := by
    rw [show E.ox_mhat q = fun t => E.ox_M0 * (1 / q t)⁻¹ from funext hmh]
    simpa using (tendsto_inv_atTop_zero.comp hP).const_mul E.ox_M0
  have halloc := (E.ox_monetary_alloc h).1
  have h01 : Tendsto (fun t => E.ox_mhat q (t + 1)) atTop (𝓝 0) :=
    h0.comp (tendsto_add_atTop_nat 1)
  refine ⟨hP, h0, ?_, ?_, ?_⟩
  · have : Tendsto (fun t => E.ox_e1 - E.ox_mhat q t) atTop (𝓝 (E.ox_e1 - 0)) :=
      h0.const_sub _
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht using (halloc t ht).2.2.2.1.symm
  · have : Tendsto (fun t => E.ox_e2 + E.ox_gn * E.ox_mhat q (t + 1)) atTop
        (𝓝 (E.ox_e2 + E.ox_gn * 0)) := (h01.const_mul _).const_add _
    rw [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht using (halloc t ht).2.2.2.2.symm
  · have := (E.ox_R_tendsto_Raut h h0).2
    rwa [E.ox_log_Raut hdu hβ, inv_div] at this

/-- Example 16.1.1, Figure 16.2 (Miao, pp. 534–535): no monetary equilibrium starts to the right
of the monetary steady state `m* = (e₁ − e₂)/2`, and every one starting to its left has real
balances strictly decreasing to the nonmonetary steady state `0`. -/
theorem example_16_1_1_left (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) :
    E.ox_mhat q 1 ≤ (E.ox_e1 - E.ox_e2) / 2 ∧ (E.ox_mhat q 1 < (E.ox_e1 - E.ox_e2) / 2 →
      StrictAnti (fun n => E.ox_mhat q (n + 1)) ∧ Tendsto (E.ox_mhat q) atTop (𝓝 0)) := by
  obtain ⟨hgap, c, hc, hx⟩ := E.ox_log_paths hdu hβ hgm h
  rw [hgn, one_mul] at hgap hx
  simp only [mul_one] at hx
  have he2 := E.ox_e2_pos
  have hd : 0 < E.ox_e1 - E.ox_e2 := by linarith
  have hlam : 1 < E.ox_e1 / E.ox_e2 := (one_lt_div he2).2 hgap
  have hpos : ∀ n : ℕ, 0 < 2 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ n := fun n => by
    have : 0 ≤ c * (E.ox_e1 / E.ox_e2) ^ n := mul_nonneg hc (pow_nonneg (by linarith) n)
    have : 0 < 2 / (E.ox_e1 - E.ox_e2) := by positivity
    linarith
  have hmh : ∀ n : ℕ, E.ox_mhat q (n + 1) =
      (2 / (E.ox_e1 - E.ox_e2) + c * (E.ox_e1 / E.ox_e2) ^ n)⁻¹ := fun n => by
    rw [← hx n, inv_inv]
  have hstar : (2 / (E.ox_e1 - E.ox_e2))⁻¹ = (E.ox_e1 - E.ox_e2) / 2 := by rw [inv_div]
  refine ⟨?_, fun hlt => ?_⟩
  · rw [hmh 0, ← hstar, pow_zero, mul_one]
    exact inv_anti₀ (by positivity) (by linarith)
  · have hc0 : 0 < c := by
      rcases eq_or_lt_of_le hc with h0 | h0
      · rw [hmh 0, ← h0, zero_mul, add_zero, hstar] at hlt; exact absurd hlt (lt_irrefl _)
      · exact h0
    refine ⟨fun a b hab => ?_, ?_⟩
    · simp only [hmh]
      refine inv_strictAnti₀ (hpos a) ?_
      have := pow_lt_pow_right₀ hlam hab
      nlinarith
    · have ht : Tendsto (fun n => E.ox_mhat q (n + 1)) atTop (𝓝 0) := by
        simp only [hmh]
        exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _
          ((tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hc0))
      exact (tendsto_add_atTop_iff_nat 1).1 ht

/-- Example 16.1.1, Figure 16.2 (Miao, p. 535): a solution of the difference equation
`x_{t+1} = (e₁/e₂)x_t − 2/e₂` in `x_t = 1/m_t` that starts to the right of `m*` (`x₀ < x*`)
eventually has `x_t < 1/e₁`, i.e. real balances leave `(0, e₁)`: it is not an equilibrium. -/
theorem example_16_1_1_right {e1 e2 : ℝ} (he2 : 0 < e2) (he : e2 < e1) {x : ℕ → ℝ}
    (hx : ∀ n, x (n + 1) = e1 / e2 * x n - 2 / e2) (h0 : x 0 < 2 / (e1 - e2)) :
    ∃ n, x n < e1⁻¹ := by
  have hlam : 1 < e1 / e2 := (one_lt_div he2).2 he
  have hsol : IsScalarSol (e1 / e2) (-(2 / e2)) (fun _ => 1) x := fun n => by
    rw [hx n]; ring
  have hgen := (eq_1_3 hlam.ne' x).1 hsol
  have hxs : -(2 / e2) / (1 - e1 / e2) = 2 / (e1 - e2) := by
    have : e1 - e2 ≠ 0 := by linarith
    have : e2 - e1 ≠ 0 := by linarith
    field_simp; ring
  rw [hxs] at hgen
  have hc : x 0 - 2 / (e1 - e2) < 0 := by linarith
  have ht : Tendsto (fun n : ℕ => (x 0 - 2 / (e1 - e2)) * (e1 / e2) ^ n) atTop atBot :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop_of_neg hc
  obtain ⟨n, hn⟩ := (ht.eventually_lt_atBot (e1⁻¹ - 2 / (e1 - e2))).exists
  exact ⟨n, by rw [hgen n]; linarith⟩

/-- **Example 16.1.2** (Miao, p. 537), the high-interest-rate equilibrium: with `β = 1`,
`e₁ = 1 − ε`, `e₂ = ε`, `ε ∈ (0, 1/2)`, `g_n = g_m = N₀ = 1`, `M = 1/2 − ε`, the prices `p_t = 1`
with `c_t^t = c_{t+1}^t = c₁⁰ = 1/2` and `m_t^t = 1/2 − ε` form a monetary equilibrium with
`R_{t+1} = 1`. -/
theorem example_16_1_2_high {ε : ℝ} (hβ : E.ox_P.ox_β = 1) (he1 : E.ox_e1 = 1 - ε)
    (he2 : E.ox_e2 = ε) (hε : ε < 1 / 2) (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1)
    (hN : E.ox_N0 = 1) (hM : E.ox_M0 = 1 / 2 - ε) :
    E.ox_IsMonetary (fun _ => 1) (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => 1 / 2 - ε) ∧
      ∀ t : ℕ, (fun _ : ℕ => (1 : ℝ)) (t + 1) / (fun _ : ℕ => (1 : ℝ)) t = 1 := by
  have hε0 : 0 < 1 / 2 - ε := by linarith
  have hNt : ∀ t, E.ox_N t = 1 := fun t => by unfold ox_N; rw [hN, hgn, one_pow, one_mul]
  have hMt : ∀ t, E.ox_M t = 1 / 2 - ε := fun t => by unfold ox_M; rw [hM, hgm, one_pow, mul_one]
  have hrel : ∀ t, 1 ≤ t → E.ox_EulerRel ((fun _ => 1 / 2 - ε) t) ((fun _ => 1 / 2 - ε) (t + 1)) :=
    fun _ _ => by
      refine ⟨hε0, by rw [he1]; linarith, hε0, by rw [he1]; linarith, ?_⟩
      dsimp only
      rw [hβ, hgn, hgm, he1, he2]
      have a1 : 1 - ε - (1 / 2 - ε) = (1 : ℝ) / 2 := by ring
      have a2 : ε + 1 * (1 / 2 - ε) = (1 : ℝ) / 2 := by ring
      have a3 : 1 * (1 / 2 - ε) / (1 * (1 / 2 - ε)) = (1 : ℝ) := div_self (by linarith)
      rw [a1, a2, a3]; ring
  have h := E.ox_ofSaving_isMonetary hrel
  have hq : E.ox_qOf (fun _ => 1 / 2 - ε) = fun _ => 1 := funext fun t => by
    unfold ox_qOf; rw [hNt, hMt, mul_one]; exact div_self hε0.ne'
  have hcy : (fun _ : ℕ => E.ox_e1 - (1 / 2 - ε)) = fun _ => 1 / 2 := funext fun _ => by
    rw [he1]; ring
  have hco : (fun _ : ℕ => E.ox_e2 + E.ox_gn * (1 / 2 - ε)) = fun _ => 1 / 2 := funext fun _ => by
    rw [he2, hgn]; ring
  have hm : (fun t => E.ox_M t / E.ox_N t) = fun _ => 1 / 2 - ε := funext fun t => by
    rw [hNt, hMt, div_one]
  rw [hq, hcy, hco, hm] at h
  exact ⟨h, fun _ => div_one 1⟩

/-- **Example 16.1.2** (Miao, p. 537), the low-interest-rate equilibrium: `R_aut < 1`; at the prices
`p₁ = 1`, `p_t/p_{t+1} = R_aut` (so `p_t = R_aut^{−(t−1)} → ∞`) every generation's optimal choice is
autarky with zero money demand; autarky with valueless money is an equilibrium, the present value
`∑ p_t(e₁ + e₂)` of the aggregate endowment is infinite, and autarky is not Pareto optimal. -/
theorem example_16_1_2_low {ε : ℝ} (hβ : E.ox_P.ox_β = 1) (he1 : E.ox_e1 = 1 - ε)
    (he2 : E.ox_e2 = ε) (hε : ε < 1 / 2) (hgn : E.ox_gn = 1) (hgm : E.ox_gm = 1) :
    E.ox_Raut < 1 ∧
      (∀ t, 1 ≤ t → E.ox_Optimal (fun s => E.ox_Raut ^ (s - 1)) t E.ox_e1 E.ox_e2 0) ∧
      Tendsto (fun t : ℕ => 1 / E.ox_Raut ^ (t - 1)) atTop atTop ∧
      (¬ Summable fun t : ℕ => 1 / E.ox_Raut ^ t * (E.ox_e1 + E.ox_e2)) ∧
      E.ox_IsNonmonetary (fun _ => 0) (fun _ => E.ox_e1) (fun _ => E.ox_e2)
        (fun t => E.ox_M t / E.ox_N t) ∧
      ¬ E.ox_ParetoOptimal (fun _ => E.ox_e1) (fun _ => E.ox_e2) := by
  have hε0 : 0 < ε := he2 ▸ E.ox_e2_pos
  have hR0 : 0 < E.ox_Raut := by
    unfold ox_Raut
    have := E.ox_P.ox_du_pos _ E.ox_e1_pos
    have := E.ox_P.ox_du_pos _ E.ox_e2_pos
    have := E.ox_P.ox_β_pos
    positivity
  have hR1 : E.ox_Raut < 1 := by
    unfold ox_Raut
    rw [hβ, one_mul, div_lt_one (E.ox_P.ox_du_pos _ E.ox_e2_pos)]
    exact E.ox_P.ox_du_lt E.ox_e2_pos (by rw [he1, he2]; linarith)
  have hauto := E.ox_autarky_isEquilibrium
  refine ⟨hR1, fun t ht => ?_, ?_, ?_, hauto, ?_⟩
  · have hq : 0 < E.ox_Raut ^ (t - 1) := pow_pos hR0 _
    have hq1 : 0 < E.ox_Raut ^ (t + 1 - 1) := pow_pos hR0 _
    have hτ : E.ox_τ t = 0 := by unfold ox_τ; rw [hgm]; ring
    have hratio : E.ox_Raut ^ (t + 1 - 1) / E.ox_Raut ^ (t - 1) = E.ox_Raut := by
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
    refine ⟨⟨le_rfl, E.ox_e1_pos, E.ox_e2_pos, by simp, by simp [hτ]⟩,
      fun c1' c2' m' hb => ?_⟩
    have hl := E.ox_budget_line (q := fun s => E.ox_Raut ^ (s - 1)) hq hq1 hb
    simp only [hτ, mul_zero, add_zero, hratio] at hl
    exact (E.eq_16_5 hR0).2 rfl c1' c2' hb.2.1 hb.2.2.1 hl
  · have : Tendsto (fun t : ℕ => (1 / E.ox_Raut) ^ (t - 1)) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hR0).2 hR1)).comp (tendsto_sub_atTop_nat 1)
    refine this.congr fun t => ?_
    rw [div_pow, one_pow]
  · intro hs
    have h0 := hs.tendsto_atTop_zero
    have hge : ∀ t : ℕ, E.ox_e1 + E.ox_e2 ≤ 1 / E.ox_Raut ^ t * (E.ox_e1 + E.ox_e2) := fun t => by
      have : 1 ≤ 1 / E.ox_Raut ^ t := by
        rw [le_div_iff₀ (pow_pos hR0 t), one_mul]; exact pow_le_one₀ hR0.le hR1.le
      nlinarith [E.ox_e1_pos, E.ox_e2_pos]
    have hpos : 0 < E.ox_e1 + E.ox_e2 := by linarith [E.ox_e1_pos, E.ox_e2_pos]
    obtain ⟨t, ht⟩ := (h0.eventually (gt_mem_nhds hpos)).exists
    linarith [hge t]
  · rw [E.proposition_16_1_2 hauto, hgn, not_le]; exact hR1

/-- **Correction to Example 16.1.2** (Miao, p. 537): no monetary equilibrium has
`p_t/p_{t+1} = R_aut`; by (16.6), `R_{t+1} > R_aut` in every monetary equilibrium. -/
theorem example_16_1_2_not_monetary {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    ¬ ∀ t, 1 ≤ t → q (t + 1) / q t = E.ox_Raut := fun hR =>
  absurd (hR 1 le_rfl) (E.eq_16_6 h le_rfl).2.ne'

end OXEconomy

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 16.1 and 16.2

Miao, §16.4, p. 556.

* **Exercise 16.1** (`u = ln`, `β = 1`, `N_t = g_nN_{t−1}`, `e₁ > e₂`, one unit of money per
  initial old, constant money stock). (a) The nonmonetary equilibrium is autarky, with
  `R_aut = e₂/e₁` (`ex_16_1_a`). (b) A stationary monetary equilibrium exists iff `e₂ < g_ne₁`
  (`ex_16_1_b_exists`); it is unique, with `m̂ = (g_ne₁ − e₂)/(2g_n)`,
  `c₁ = (g_ne₁ + e₂)/(2g_n)`, `c₂ = (g_ne₁ + e₂)/2`, `R = g_n`, `p_t = 1/(g_nᵗm̂)`
  (`ex_16_1_b_values`); it is Pareto optimal, autarky is not, and it Pareto dominates autarky
  (`ex_16_1_b_rank`); when `e₂ ≥ g_ne₁` autarky is the only equilibrium and it is Pareto
  optimal (`ex_16_1_b_autarky`). (c) Every monetary equilibrium is `1/m̂_{n+1} = x* + cλⁿ`,
  `c ≥ 0`; the rate of return on money is `g_n` for `c = 0` and tends to `R_aut = e₂/e₁` for
  `c > 0` (`ex_16_1_c`); both kinds exist (`ex_16_1_c_exist`).
* **Exercise 16.2** (the initial old also own a tree paying `d > 0` each period; constant
  population). The two-asset budget sets and equilibrium (`ox_TreeBudget`, `ox_TreeOptimal`,
  `ox_TreeEquilibrium`). (a) There is no equilibrium with valued fiat money, for any preferences
  (`ex_16_2_a`). (b) With the preferences of Exercise 16.1 the nonmonetary equilibrium is unique:
  the tree price is constant at `a* = (e₁ − e₂ − 2d + √((e₁ − e₂ − 2d)² + 8de₁))/4`
  (`ex_16_2_b_exists`, `ex_16_2_b_unique`).

**Departures (Exercise 16.2).** The exercise keeps the population growth of Exercise 16.1; with
`g_n ≠ 1` the dividend per young `dN₀/N_t` varies with `t` and the equilibria have no closed
form. We formalise constant population (`g_n = 1`), per capita: each initial old owns one tree
and one unit of money, the young hold one of each in equilibrium. The initial old consume their
resources `e₂ + q₁ + a₁ + d` (their utility maximisation, as in `OXEconomy.ox_oldOptimal_iff`).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

namespace OXEconomy

variable (E : OXEconomy)

/-- **Exercise 16.1(a)** (Miao, p. 556): autarky with valueless money is the nonmonetary
equilibrium, every nonmonetary equilibrium is autarky, and the implicit interest rate is
`R_aut = e₂/e₁`. -/
theorem ex_16_1_a (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1) :
    E.ox_IsNonmonetary (fun _ => 0) (fun _ => E.ox_e1) (fun _ => E.ox_e2)
      (fun t => E.ox_M t / E.ox_N t) ∧
    (∀ q cy co m : ℕ → ℝ, E.ox_IsNonmonetary q cy co m →
      (∀ t, 1 ≤ t → cy t = E.ox_e1 ∧ co t = E.ox_e2) ∧ co 0 = E.ox_e2) ∧
    E.ox_Raut = E.ox_e2 / E.ox_e1 :=
  ⟨E.ox_autarky_isEquilibrium, fun _ _ _ _ h => E.ox_nonmonetary_autarky h, E.ox_log_Raut hdu hβ⟩

/-- **Exercise 16.1(b)** (Miao, p. 556): with `g_m = 1`, a stationary monetary equilibrium exists
iff `e₂ < g_ne₁`. -/
theorem ex_16_1_b_exists (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) :
    (∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m ∧ ∃ mh, ∀ t, 1 ≤ t → E.ox_mhat q t = mh) ↔
      E.ox_e2 < E.ox_gn * E.ox_e1 := by
  have he1 := E.ox_e1_pos
  have hiff : E.ox_Raut * E.ox_gm < E.ox_gn ↔ E.ox_e2 < E.ox_gn * E.ox_e1 := by
    rw [E.ox_log_Raut hdu hβ, hgm, mul_one, div_lt_iff₀ he1]
  constructor
  · rintro ⟨q, cy, co, m, h, -⟩
    exact hiff.1 (E.proposition_16_1_1_necessity h)
  · intro hgap
    obtain ⟨mh, -, -, h⟩ := E.proposition_16_1_1_sufficiency (hiff.2 hgap)
    exact ⟨_, _, _, _, h, mh, fun t _ => E.ox_mhat_qOf _ t⟩

/-- **Exercise 16.1(b)** (Miao, p. 556): in every stationary monetary equilibrium (with
`M₀ = N₀`, `g_m = 1`), `m̂ = (g_ne₁ − e₂)/(2g_n)`, `c_t^t = (g_ne₁ + e₂)/(2g_n)`,
`c_{t+1}^t = c₁⁰ = (g_ne₁ + e₂)/2`, `R_{t+1} = g_n` and `p_t = 1/q_t = 1/(g_nᵗm̂)`. -/
theorem ex_16_1_b_values (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hM : E.ox_M0 = E.ox_N0) {q cy co m : ℕ → ℝ}
    (h : E.ox_IsMonetary q cy co m) {mh : ℝ} (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) :
    mh = (E.ox_gn * E.ox_e1 - E.ox_e2) / (2 * E.ox_gn) ∧
      (∀ t, 1 ≤ t → cy t = (E.ox_gn * E.ox_e1 + E.ox_e2) / (2 * E.ox_gn) ∧
        co t = (E.ox_gn * E.ox_e1 + E.ox_e2) / 2 ∧ q (t + 1) / q t = E.ox_gn ∧
        1 / q t = 1 / (E.ox_gn ^ t * mh)) ∧
      co 0 = (E.ox_gn * E.ox_e1 + E.ox_e2) / 2 := by
  have hgn := E.ox_gn_pos
  obtain ⟨h0, he, hroot⟩ := E.proposition_16_1_1_unique_stationary h hc
  simp only [hdu, hβ, hgm, one_mul, div_one] at hroot
  have h1 : E.ox_e1 - mh ≠ 0 := by linarith
  have h2 : E.ox_e2 + E.ox_gn * mh ≠ 0 := by nlinarith [E.ox_e2_pos]
  have hmh : mh = (E.ox_gn * E.ox_e1 - E.ox_e2) / (2 * E.ox_gn) := by
    field_simp at hroot
    rw [eq_div_iff (by nlinarith [E.ox_e2_pos])] at hroot
    rw [eq_div_iff (by positivity)]
    linarith
  obtain ⟨halloc, hco0⟩ := E.ox_monetary_alloc h
  refine ⟨hmh, fun t ht => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [(halloc t ht).2.2.2.1, hc t ht, hmh]; field_simp; ring
  · rw [(halloc t ht).2.2.2.2, hc (t + 1) (by omega), hmh]; field_simp; ring
  · rw [E.ox_stationary_R h hc ht, hgm, div_one]
  · have := hc t ht
    unfold ox_mhat ox_M ox_N at this
    rw [hM, hgm, one_pow, mul_one] at this
    rw [← this]
    have := E.ox_N0_pos.ne'
    have := (pow_pos hgn t).ne'
    field_simp
  · rw [hco0, hc 1 le_rfl, hmh]; field_simp; ring

/-- **Exercise 16.1(b)** (Miao, p. 556), the Pareto ranking: with `g_m = 1` (for any preferences,
in particular those of the exercise), the stationary monetary equilibrium is Pareto optimal,
autarky is not, and the monetary allocation makes the initial old and every generation strictly
better off than autarky. -/
theorem ex_16_1_b_rank (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m)
    {mh : ℝ}
    (hc : ∀ t, 1 ≤ t → E.ox_mhat q t = mh) :
    E.ox_ParetoOptimal cy co ∧ ¬ E.ox_ParetoOptimal (fun _ => E.ox_e1) (fun _ => E.ox_e2) ∧
      E.ox_e2 < co 0 ∧ ∀ t, 1 ≤ t → E.ox_EU E.ox_e1 E.ox_e2 < E.ox_EU (cy t) (co t) := by
  have hgn := E.ox_gn_pos
  have hR := E.proposition_16_1_1_necessity h
  obtain ⟨halloc, hco0⟩ := E.ox_monetary_alloc h
  obtain ⟨h0, -, -⟩ := E.proposition_16_1_1_unique_stationary h hc
  have hs : ox_IsStationary cy co (E.ox_e1 - mh) (E.ox_e2 + E.ox_gn * mh) := fun t ht =>
    ⟨by rw [(halloc t ht).2.2.2.1, hc t ht], by rw [(halloc t ht).2.2.2.2, hc (t + 1) (by omega)]⟩
  refine ⟨(E.proposition_16_1_3 hR h hs).2 hgm.le, ?_, ?_, fun t ht => ?_⟩
  · rw [E.proposition_16_1_2 E.ox_autarky_isEquilibrium, not_le]
    rw [hgm, mul_one] at hR; exact hR
  · rw [hco0, hc 1 le_rfl]; nlinarith
  · have hc1 := (h.1.2.1 t ht).1.2.1
    have hc2 := (h.1.2.1 t ht).1.2.2.1
    have heul := E.eq_16_4 h ht
    rw [E.ox_stationary_R h hc ht, hgm, div_one] at heul
    have hd2 := E.ox_P.ox_du_pos _ hc2
    have hβ0 := E.ox_P.ox_β_pos
    rw [div_eq_iff (by positivity)] at heul
    refine E.ox_P.ox_line_optimal_strict hc1 hc2 hgn (by rw [heul]; ring) E.ox_e1_pos
      E.ox_e2_pos ?_ (Or.inl ?_)
    · rw [(hs t ht).1, (hs t ht).2]; field_simp; ring_nf; rfl
    · rw [(hs t ht).1]; linarith

/-- **Exercise 16.1(b)** (Miao, p. 556): when `e₂ ≥ g_ne₁` there is no monetary equilibrium and
autarky, the only equilibrium, is Pareto optimal. -/
theorem ex_16_1_b_autarky (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hge : E.ox_gn * E.ox_e1 ≤ E.ox_e2) :
    (¬ ∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m) ∧
      E.ox_ParetoOptimal (fun _ => E.ox_e1) (fun _ => E.ox_e2) := by
  have he1 := E.ox_e1_pos
  refine ⟨fun ⟨q, cy, co, m, h⟩ => ?_, ?_⟩
  · have := E.proposition_16_1_1_necessity h
    rw [E.ox_log_Raut hdu hβ, hgm, mul_one, div_lt_iff₀ he1] at this
    linarith
  · rw [E.proposition_16_1_2 E.ox_autarky_isEquilibrium, E.ox_log_Raut hdu hβ, le_div_iff₀ he1]
    exact hge

/-- **Exercise 16.1(c)** (Miao, p. 556): every monetary equilibrium (with `g_m = 1`) has
`1/m̂_{n+1} = x* + cλⁿ` with `c ≥ 0`; if `c = 0` the rate of return on money is `R_{t+1} = g_n`
for all `t`, and if `c > 0` it tends to `R_aut = e₂/e₁`. -/
theorem ex_16_1_c (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) {q cy co m : ℕ → ℝ} (h : E.ox_IsMonetary q cy co m) :
    ∃ c, 0 ≤ c ∧ (∀ n : ℕ, (E.ox_mhat q (n + 1))⁻¹ =
      2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) + c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n) ∧
      (c = 0 → ∀ t, 1 ≤ t → q (t + 1) / q t = E.ox_gn) ∧
      (0 < c → Tendsto (fun t => q (t + 1) / q t) atTop (𝓝 (E.ox_e2 / E.ox_e1))) := by
  obtain ⟨hgap, c, hc, hx⟩ := E.ox_log_paths hdu hβ hgm h
  refine ⟨c, hc, hx, fun h0 t ht => ?_, fun hc0 => ?_⟩
  · have hconst : ∀ t, 1 ≤ t → E.ox_mhat q t = (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2))⁻¹ :=
      fun t ht => by
        obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
        have := hx n
        rw [h0, zero_mul, add_zero] at this
        rw [← this, inv_inv]
    rw [E.ox_stationary_R h hconst ht, hgm, div_one]
  · have hlam : 1 < E.ox_gn * E.ox_e1 / E.ox_e2 := (one_lt_div E.ox_e2_pos).2 hgap
    have ht : Tendsto (fun n => E.ox_mhat q (n + 1)) atTop (𝓝 0) := by
      have : (fun n => E.ox_mhat q (n + 1)) = fun n =>
          (2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) +
            c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n)⁻¹ := funext fun n => by rw [← hx n, inv_inv]
      rw [this]
      exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _
        ((tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hc0))
    have := (E.ox_R_tendsto_Raut h ((tendsto_add_atTop_iff_nat 1).1 ht)).1
    rwa [E.ox_log_Raut hdu hβ] at this

/-- **Exercise 16.1(c)** (Miao, p. 556): when `e₂ < g_ne₁` both kinds of monetary equilibrium
exist: the stationary one (`c = 0`) and, for every `c > 0`, one whose real balances vanish. -/
theorem ex_16_1_c_exist (hdu : E.ox_P.ox_du = fun c => c⁻¹) (hβ : E.ox_P.ox_β = 1)
    (hgm : E.ox_gm = 1) (hgap : E.ox_e2 < E.ox_gn * E.ox_e1) {c : ℝ} (hc : 0 ≤ c) :
    ∃ q cy co m : ℕ → ℝ, E.ox_IsMonetary q cy co m ∧ ∀ n : ℕ, (E.ox_mhat q (n + 1))⁻¹ =
      2 * E.ox_gn / (E.ox_gn * E.ox_e1 - E.ox_e2) + c * (E.ox_gn * E.ox_e1 / E.ox_e2) ^ n :=
  ⟨_, _, _, _, E.ox_log_construct hdu hβ hgm hgap hc, fun n => by
    rw [E.ox_mhat_qOf, inv_inv, Nat.add_sub_cancel]⟩

end OXEconomy

namespace OXPrefs

variable (P : OXPrefs)

/-- Exercise 16.2 (Miao, p. 556): the budget set of a young agent at `t` who can hold money (value
`q_t`) and trees (price `a_t`, dividend `d`), per capita with constant population. -/
def ox_TreeBudget (e1 e2 d : ℝ) (q a : ℕ → ℝ) (t : ℕ) (c1 c2 m x : ℝ) : Prop :=
  0 ≤ m ∧ 0 ≤ x ∧ 0 < c1 ∧ 0 < c2 ∧ c1 + q t * m + a t * x ≤ e1 ∧
    c2 ≤ e2 + q (t + 1) * m + (a (t + 1) + d) * x

/-- Exercise 16.2: an optimal choice of the young at `t`. -/
def ox_TreeOptimal (e1 e2 d : ℝ) (q a : ℕ → ℝ) (t : ℕ) (c1 c2 m x : ℝ) : Prop :=
  ox_TreeBudget e1 e2 d q a t c1 c2 m x ∧
    ∀ c1' c2' m' x', ox_TreeBudget e1 e2 d q a t c1' c2' m' x' → P.ox_U c1' c2' ≤ P.ox_U c1 c2

/-- Exercise 16.2: an equilibrium of the economy with money and trees: nonnegative prices, the
young optimise holding one unit of money and one tree each (market clearing), the initial old
consume their resources, and the goods market clears. -/
def ox_TreeEquilibrium (e1 e2 d : ℝ) (q a cy co : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 ≤ q t ∧ 0 ≤ a t) ∧
    (∀ t, 1 ≤ t → P.ox_TreeOptimal e1 e2 d q a t (cy t) (co t) 1 1) ∧
    co 0 = e2 + q 1 + a 1 + d ∧ ∀ t, 1 ≤ t → cy t + co (t - 1) = e1 + e2 + d

/-- In the tree economy optimal choices exhaust both budget constraints. -/
theorem ox_tree_binds {e1 e2 d : ℝ} {q a : ℕ → ℝ} {t : ℕ} {c1 c2 m x : ℝ}
    (h : P.ox_TreeOptimal e1 e2 d q a t c1 c2 m x) :
    c1 = e1 - q t * m - a t * x ∧ c2 = e2 + q (t + 1) * m + (a (t + 1) + d) * x := by
  obtain ⟨⟨hm, hx, h1, h2, hb1, hb2⟩, hmax⟩ := h
  constructor
  · by_contra hne
    have hlt : c1 < e1 - q t * m - a t * x := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax (e1 - q t * m - a t * x) c2 m x ⟨hm, hx, by linarith, h2, by linarith, hb2⟩
    have hu := P.ox_u_lt h1 hlt
    unfold ox_U at this
    linarith
  · by_contra hne
    have hlt : c2 < e2 + q (t + 1) * m + (a (t + 1) + d) * x := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact h
      · linarith
    have := hmax c1 _ m x ⟨hm, hx, h1, by linarith, hb1, le_rfl⟩
    have hu := mul_lt_mul_of_pos_left (P.ox_u_lt h2 hlt) P.ox_β_pos
    unfold ox_U at this
    linarith

/-- In the tree economy, with `d > 0` and nonnegative next-period prices, the tree price is
positive (a free tree would be demanded without bound). -/
theorem ox_tree_price_pos {e1 e2 d : ℝ} (hd : 0 < d) {q a : ℕ → ℝ} {t : ℕ} {c1 c2 m x : ℝ}
    (h : P.ox_TreeOptimal e1 e2 d q a t c1 c2 m x) (ha : 0 ≤ a t) (ha1 : 0 ≤ a (t + 1)) :
    0 < a t := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · exfalso
    obtain ⟨⟨hm, hx, h1, h2, hb1, hb2⟩, hmax⟩ := h
    have := hmax c1 (c2 + d) m (x + 1) ⟨hm, by linarith, h1, by linarith,
      by rw [← h0] at hb1 ⊢; linarith, by nlinarith⟩
    have hu := mul_lt_mul_of_pos_left (P.ox_u_lt h2 (show c2 < c2 + d by linarith)) P.ox_β_pos
    unfold ox_U at this
    linarith
  · exact h0

/-- Exercise 16.2: the first-order conditions of the tree economy at a choice with positive
holdings of an asset: for trees `a_tu'(c₁) = β(a_{t+1} + d)u'(c₂)`, for money
`q_tu'(c₁) = βq_{t+1}u'(c₂)`. -/
theorem ox_tree_foc {e1 e2 d : ℝ} {q a : ℕ → ℝ} {t : ℕ} {c1 c2 m x : ℝ}
    (h : P.ox_TreeOptimal e1 e2 d q a t c1 c2 m x) :
    (0 < x → a t * P.ox_du c1 = P.ox_β * (a (t + 1) + d) * P.ox_du c2) ∧
      (0 < m → q t * P.ox_du c1 = P.ox_β * q (t + 1) * P.ox_du c2) := by
  obtain ⟨b1, b2⟩ := P.ox_tree_binds h
  obtain ⟨⟨hm, hx, h1, h2, _, _⟩, hmax⟩ := h
  refine ⟨fun hx0 => P.ox_foc h1 h2 ?_, fun hm0 => P.ox_foc h1 h2 ?_⟩
  · filter_upwards [ox_eventually_pos c1 (-a t) h1, ox_eventually_pos c2 (a (t + 1) + d) h2,
      ox_eventually_pos x 1 hx0] with s hs1 hs2 hs3
    exact hmax _ _ m (x + s) ⟨hm, by linarith, by linarith, hs2, by rw [b1]; linarith,
      by rw [b2]; linarith⟩
  · filter_upwards [ox_eventually_pos c1 (-q t) h1, ox_eventually_pos c2 (q (t + 1)) h2,
      ox_eventually_pos m 1 hm0] with s hs1 hs2 hs3
    exact hmax _ _ (m + s) x ⟨by linarith, hx, by linarith, hs2, by rw [b1]; linarith,
      by rw [b2]; linarith⟩

/-- **Exercise 16.2(a)** (Miao, p. 556): with a tree paying `d > 0`, there is no equilibrium with
valued fiat money (for any preferences). Money and trees must earn the same return,
`q_{t+1}/q_t = (a_{t+1} + d)/a_t`, so `a_t/q_t` falls by `d/q_{t+1} > d/e₁` every period. -/
theorem ex_16_2_a {e1 e2 d : ℝ} (hd : 0 < d) :
    ¬ ∃ q a cy co : ℕ → ℝ, P.ox_TreeEquilibrium e1 e2 d q a cy co ∧ ∀ t, 1 ≤ t → 0 < q t := by
  rintro ⟨q, a, cy, co, ⟨hprice, hopt, -, -⟩, hq⟩
  have hβ := P.ox_β_pos
  have hapos : ∀ t, 1 ≤ t → 0 < a t := fun t ht =>
    P.ox_tree_price_pos hd (hopt t ht) (hprice t ht).2 (hprice (t + 1) (by omega)).2
  have he1 : ∀ t, 1 ≤ t → q t < e1 := fun t ht => by
    obtain ⟨⟨-, -, h1, -, hb1, -⟩, -⟩ := hopt t ht
    have := (hprice t ht).2
    linarith
  set b := fun t => a t / q t
  have hstep : ∀ t, 1 ≤ t → b (t + 1) = b t - d / q (t + 1) := fun t ht => by
    obtain ⟨hx, hm⟩ := P.ox_tree_foc (hopt t ht)
    have hx1 := hx one_pos
    have hm1 := hm one_pos
    obtain ⟨⟨-, -, h1, h2, -, -⟩, -⟩ := hopt t ht
    have hd1 := P.ox_du_pos _ h1
    have hd2 := P.ox_du_pos _ h2
    have hqt := hq t ht
    have hqt1 := hq (t + 1) (by omega)
    have harb : a t * q (t + 1) = q t * (a (t + 1) + d) := by
      have key : (a t * q (t + 1) - q t * (a (t + 1) + d)) * (P.ox_β * P.ox_du (co t)) = 0 := by
        linear_combination q t * hx1 - a t * hm1
      have hne : P.ox_β * P.ox_du (co t) ≠ 0 := by positivity
      have := (mul_eq_zero.1 key).resolve_right hne
      linarith
    simp only [b]
    field_simp
    linear_combination -harb
  have hdec : ∀ n : ℕ, b (n + 1) ≤ b 1 - n * (d / e1) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep (n + 1) (by omega)
      have hqn := hq (n + 2) (by omega)
      have hlt := he1 (n + 2) (by omega)
      have : d / e1 ≤ d / q (n + 1 + 1) := div_le_div_of_nonneg_left hd.le hqn hlt.le
      rw [hs]; push_cast; linarith
  have he1pos : 0 < e1 := lt_trans (hq 1 le_rfl) (he1 1 le_rfl)
  obtain ⟨n, hn⟩ := exists_nat_gt (b 1 / (d / e1))
  have hpos : 0 < b (n + 1) := div_pos (hapos (n + 1) (by omega)) (hq (n + 1) (by omega))
  have := hdec n
  rw [div_lt_iff₀ (by positivity)] at hn
  linarith

/-- The constant tree price of Exercise 16.2(b):
`a* = (e₁ − e₂ − 2d + √((e₁ − e₂ − 2d)² + 8de₁))/4`. -/
noncomputable def ox_astar (e1 e2 d : ℝ) : ℝ :=
  (e1 - e2 - 2 * d + Real.sqrt ((e1 - e2 - 2 * d) ^ 2 + 8 * d * e1)) / 4

/-- Exercise 16.2(b): `a* > 0`, `e₁ − 2a* > 0` and `(a* + d)(e₁ − 2a*) = a*e₂`, the steady state
of the tree-price equation `(a_{t+1} + d)(e₁ − 2a_t) = a_te₂`. -/
theorem ox_astar_spec {e1 e2 d : ℝ} (he1 : 0 < e1) (he2 : 0 < e2) (hd : 0 < d) :
    0 < ox_astar e1 e2 d ∧ 0 < e1 - 2 * ox_astar e1 e2 d ∧
      (ox_astar e1 e2 d + d) * (e1 - 2 * ox_astar e1 e2 d) = ox_astar e1 e2 d * e2 := by
  have hD : 0 ≤ (e1 - e2 - 2 * d) ^ 2 + 8 * d * e1 := by positivity
  have hS := Real.sq_sqrt hD
  have hS0 := Real.sqrt_nonneg ((e1 - e2 - 2 * d) ^ 2 + 8 * d * e1)
  have hSB : |e1 - e2 - 2 * d| < Real.sqrt ((e1 - e2 - 2 * d) ^ 2 + 8 * d * e1) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hpos : 0 < ox_astar e1 e2 d := by
    unfold ox_astar
    have := neg_abs_le (e1 - e2 - 2 * d)
    exact div_pos (by linarith) (by norm_num)
  have hrel : (ox_astar e1 e2 d + d) * (e1 - 2 * ox_astar e1 e2 d) = ox_astar e1 e2 d * e2 := by
    unfold ox_astar
    linear_combination (-1 / 8 : ℝ) * hS
  refine ⟨hpos, ?_, hrel⟩
  by_contra hle
  have : (ox_astar e1 e2 d + d) * (e1 - 2 * ox_astar e1 e2 d) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hle)
  nlinarith

/-- **Exercise 16.2(b)** (Miao, p. 556): with the preferences of Exercise 16.1 (`u = ln`, `β = 1`)
the constant tree price `a*` with valueless money is a nonmonetary equilibrium:
`c_t^t = e₁ − a*`, `c_{t+1}^t = e₂ + a* + d`. -/
theorem ex_16_2_b_exists (hdu : P.ox_du = fun c => c⁻¹) (hβ : P.ox_β = 1) {e1 e2 d : ℝ}
    (he1 : 0 < e1) (he2 : 0 < e2) (hd : 0 < d) :
    P.ox_TreeEquilibrium e1 e2 d (fun _ => 0) (fun _ => ox_astar e1 e2 d)
      (fun _ => e1 - ox_astar e1 e2 d) (fun _ => e2 + ox_astar e1 e2 d + d) := by
  obtain ⟨ha, hea, hrel⟩ := ox_astar_spec he1 he2 hd
  set A := ox_astar e1 e2 d
  have hc1 : 0 < e1 - A := by linarith
  have hc2 : 0 < e2 + A + d := by linarith
  refine ⟨fun _ _ => ⟨le_rfl, ha.le⟩, fun t _ => ⟨⟨zero_le_one, zero_le_one, hc1, hc2,
    by linarith, by linarith⟩, fun c1' c2' m' x' hb => ?_⟩, by ring, fun _ _ => by ring⟩
  obtain ⟨-, hx', h1', h2', hb1, hb2⟩ := hb
  have hR : 0 < (A + d) / A := by positivity
  refine P.ox_line_optimal hc1 hc2 hR ?_ h1' h2' ?_
  · simp only [hdu, hβ, one_mul]
    field_simp
    linear_combination (-1 : ℝ) * hrel
  · simp only [zero_mul, add_zero] at hb1 hb2
    have : c2' / ((A + d) / A) ≤ (e2 + (A + d) * x') / ((A + d) / A) :=
      div_le_div_of_nonneg_right hb2 hR.le
    have e1' : (e2 + (A + d) * x') / ((A + d) / A) = e2 / ((A + d) / A) + A * x' := by
      field_simp
    have e2' : (e2 + A + d) / ((A + d) / A) = e2 / ((A + d) / A) + A := by
      field_simp; ring
    rw [e2']; linarith

/-- **Exercise 16.2(b)** (Miao, p. 556): with the preferences of Exercise 16.1 every nonmonetary
equilibrium has the constant tree price `a_t = a*`: deviations from `a*` grow by at least
`e₂/(e₁ − 2a*) > 1` per period and would leave `(0, e₁)`. -/
theorem ex_16_2_b_unique (hdu : P.ox_du = fun c => c⁻¹) (hβ : P.ox_β = 1) {e1 e2 d : ℝ}
    (he1 : 0 < e1) (he2 : 0 < e2) (hd : 0 < d) {q a cy co : ℕ → ℝ}
    (h : P.ox_TreeEquilibrium e1 e2 d q a cy co) (hq : ∀ t, 1 ≤ t → q t = 0) :
    ∀ t, 1 ≤ t → a t = ox_astar e1 e2 d := by
  obtain ⟨hA, hea, hrelA⟩ := ox_astar_spec he1 he2 hd
  set A := ox_astar e1 e2 d
  obtain ⟨hprice, hopt, -, -⟩ := h
  have hapos : ∀ t, 1 ≤ t → 0 < a t := fun t ht =>
    P.ox_tree_price_pos hd (hopt t ht) (hprice t ht).2 (hprice (t + 1) (by omega)).2
  -- the tree-price difference equation
  have hrel : ∀ t, 1 ≤ t → (a (t + 1) + d) * (e1 - 2 * a t) = a t * e2 := fun t ht => by
    have hfoc := (P.ox_tree_foc (hopt t ht)).1 one_pos
    obtain ⟨b1, b2⟩ := P.ox_tree_binds (hopt t ht)
    obtain ⟨⟨-, -, h1, h2, -, -⟩, -⟩ := hopt t ht
    rw [b1, hq t ht] at h1 hfoc
    rw [b2, hq (t + 1) (by omega)] at h2 hfoc
    simp only [hdu, hβ, one_mul, sub_zero, add_zero, mul_one] at hfoc h1 h2
    field_simp at hfoc
    linear_combination (-1 : ℝ) * hfoc
  have hlt : ∀ t, 1 ≤ t → a t < e1 := fun t ht => by
    obtain ⟨⟨-, -, h1, -, hb1, -⟩, -⟩ := hopt t ht
    have := (hprice t ht).1
    nlinarith [hq t ht]
  have hgap : ∀ t, 1 ≤ t → 0 < e1 - 2 * a t := fun t ht => by
    have h1 := hrel t ht
    have := hapos (t + 1) (by omega)
    by_contra hle
    have : (a (t + 1) + d) * (e1 - 2 * a t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.1 hle)
    nlinarith [hapos t ht]
  set k := e2 / (e1 - 2 * A)
  have hk : 1 < k := by
    rw [one_lt_div hea]
    nlinarith
  -- deviations grow geometrically
  have hdev : ∀ t, 1 ≤ t → k * |a t - A| ≤ |a (t + 1) - A| := fun t ht => by
    have hid : (a (t + 1) - A) * (e1 - 2 * a t) * (e1 - 2 * A) = e1 * e2 * (a t - A) := by
      linear_combination (e1 - 2 * A) * hrel t ht - (e1 - 2 * a t) * hrelA
    have hg := hgap t ht
    have hle : e1 - 2 * a t ≤ e1 := by linarith [hapos t ht]
    have habs := congrArg abs hid
    simp only [abs_mul, abs_of_pos hg, abs_of_pos hea, abs_of_pos he1, abs_of_pos he2] at habs
    simp only [k]
    rw [div_mul_eq_mul_div, div_le_iff₀ hea]
    have h0 := abs_nonneg (a (t + 1) - A)
    have h1 : e1 * (e2 * |a t - A|) ≤ e1 * (|a (t + 1) - A| * (e1 - 2 * A)) := by
      calc e1 * (e2 * |a t - A|) = |a (t + 1) - A| * (e1 - 2 * a t) * (e1 - 2 * A) := by
            linarith
        _ ≤ |a (t + 1) - A| * e1 * (e1 - 2 * A) := by
            apply mul_le_mul_of_nonneg_right _ hea.le
            exact mul_le_mul_of_nonneg_left hle h0
        _ = e1 * (|a (t + 1) - A| * (e1 - 2 * A)) := by ring
    exact le_of_mul_le_mul_left h1 he1
  intro t ht
  by_contra hne
  have hpos : 0 < |a t - A| := abs_pos.2 (sub_ne_zero.2 hne)
  have hgrow : ∀ j, k ^ j * |a t - A| ≤ |a (t + j) - A| := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      calc k ^ (j + 1) * |a t - A| = k * (k ^ j * |a t - A|) := by ring
        _ ≤ k * |a (t + j) - A| := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ |a (t + j + 1) - A| := hdev (t + j) (by omega)
  have hbdd : ∀ j, |a (t + j) - A| ≤ e1 + A := fun j => by
    have h1 := hapos (t + j) (by omega)
    have h2 := hlt (t + j) (by omega)
    rw [abs_le]; constructor <;> linarith
  have htend : Tendsto (fun j => k ^ j * |a t - A|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const hpos
  obtain ⟨j, hj⟩ := (htend.eventually_gt_atTop (e1 + A)).exists
  linarith [hgrow j, hbdd j]

end OXPrefs

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The young agent's saving problem in the Diamond model

Miao, §16.2, p. 545. A young agent with wage `w` solves
`max u(c_t^t) + βu(c_{t+1}^t)` subject to `c_t^t + s_t = w_t`, `c_{t+1}^t = R_{t+1}s_t`.

* Tangent-line inequalities for (strictly) concave differentiable functions
  (`op_concave_tangent`, `op_strictConcave_tangent`).
* The Euler equation `u′(w − s) = βu′(Rs)R`: necessary at an interior maximum
  (`op_euler_necessary`), sufficient for concave `u` (`op_euler_sufficient`), and for strictly
  concave `u` the maximum is unique (`op_euler_sufficient_strict`).
* The saving function `s = s(w, R)`: with a continuous, strictly decreasing marginal utility
  satisfying the Inada condition at `0`, the Euler equation has exactly one solution in `(0, w)`
  (`op_saving_exists`, `op_saving_unique`).
* `0 < s_w < 1`: saving and first-period consumption both rise strictly with the wage
  (`op_saving_wage_mono`); with a differentiable saving function the implicit derivative is
  `s_w = u″(c_y)/(u″(c_y) + βR²u″(c_o)) ∈ (0, 1)` (`op_saving_sw`).
* Log utility with second-period income `y₂` (used for Exercises 16.4–16.8): the optimal saving
  is `s = (βy₁ − y₂/R)/(1 + β)` (`opLogSaving`, `op_log_saving`).

Departure: the book states `0 < s_w < 1` as a property of the derivative of the saving
function; the derivative-free monotonicity statement `op_saving_wage_mono` needs no
differentiability, and `op_saving_sw` is the derivative statement.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- The tangent line of a concave function lies above its graph. -/
theorem op_concave_tangent {u : ℝ → ℝ} {S : Set ℝ} (hu : ConcaveOn ℝ S u) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt u d x) : u y ≤ u x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hu.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    nlinarith
  · simp
  · have h := hu.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    nlinarith

/-- The tangent line of a strictly concave function lies strictly above its graph off `x`. -/
theorem op_strictConcave_tangent {u : ℝ → ℝ} {S : Set ℝ} (hu : StrictConcaveOn ℝ S u)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hne : y ≠ x) (hd : HasDerivAt u d x) :
    u y < u x + d * (y - x) := by
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · have h := hu.lt_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at h
    nlinarith
  · have h := hu.slope_lt_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at h
    nlinarith

/-- The derivative of the lifetime utility `s ↦ u(w − s) + βu(Rs)`. -/
theorem op_lifetime_hasDerivAt {u up : ℝ → ℝ} {β w R s : ℝ}
    (hy : HasDerivAt u (up (w - s)) (w - s)) (ho : HasDerivAt u (up (R * s)) (R * s)) :
    HasDerivAt (fun x => u (w - x) + β * u (R * x))
      (-up (w - s) + β * (up (R * s) * R)) s := by
  have h1 : HasDerivAt (fun x => u (w - x)) (up (w - s) * (-1)) s := by
    have := (hasDerivAt_id s).const_sub w
    exact hy.comp s this
  have h2 : HasDerivAt (fun x => u (R * x)) (up (R * s) * R) s := by
    have := (hasDerivAt_id s).const_mul R
    simp only [mul_one] at this
    exact ho.comp s this
  convert h1.add (h2.const_mul β) using 1
  ring

/-- Miao, p. 545: the consumption Euler equation `u′(w − s) = βu′(Rs)R` is necessary at an
interior maximum of the young agent's problem. -/
theorem op_euler_necessary {u up : ℝ → ℝ} {β w R s : ℝ} (hs0 : 0 < s) (hsw : s < w)
    (hmax : ∀ s' ∈ Set.Ioo 0 w, u (w - s') + β * u (R * s') ≤ u (w - s) + β * u (R * s))
    (hy : HasDerivAt u (up (w - s)) (w - s)) (ho : HasDerivAt u (up (R * s)) (R * s)) :
    up (w - s) = β * up (R * s) * R := by
  have hloc : IsLocalMax (fun x => u (w - x) + β * u (R * x)) s :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs0 hsw) hmax
  have := hloc.hasDerivAt_eq_zero (op_lifetime_hasDerivAt hy ho)
  linarith

/-- Miao, p. 545: for concave `u` the Euler equation is sufficient: a saving level `s ∈ (0, w)`
satisfying it maximises lifetime utility over `(0, w)`. -/
theorem op_euler_sufficient {u up : ℝ → ℝ} {β w R s : ℝ} (hu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hβ : 0 ≤ β) (hR : 0 < R) (hs0 : 0 < s) (hsw : s < w)
    (hy : HasDerivAt u (up (w - s)) (w - s)) (ho : HasDerivAt u (up (R * s)) (R * s))
    (heul : up (w - s) = β * up (R * s) * R) :
    ∀ s' ∈ Set.Ioo 0 w, u (w - s') + β * u (R * s') ≤ u (w - s) + β * u (R * s) := by
  intro s' hs'
  have h1 := op_concave_tangent hu (show w - s ∈ Set.Ioi 0 from by simp; linarith)
    (show w - s' ∈ Set.Ioi 0 from by simp; linarith [hs'.2]) hy
  have h2 := op_concave_tangent hu (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
    (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs'.1) ho
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  have : up (w - s) * (w - s' - (w - s)) + β * (up (R * s) * (R * s' - R * s)) = 0 := by
    rw [heul]; ring
  nlinarith

/-- Miao, p. 545: for strictly concave `u` the saving level satisfying the Euler equation is the
unique maximiser over `(0, w)`. -/
theorem op_euler_sufficient_strict {u up : ℝ → ℝ} {β w R s : ℝ}
    (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) (hβ : 0 ≤ β) (hR : 0 < R) (hs0 : 0 < s)
    (hsw : s < w) (hy : HasDerivAt u (up (w - s)) (w - s))
    (ho : HasDerivAt u (up (R * s)) (R * s)) (heul : up (w - s) = β * up (R * s) * R) :
    ∀ s' ∈ Set.Ioo 0 w, s' ≠ s →
      u (w - s') + β * u (R * s') < u (w - s) + β * u (R * s) := by
  intro s' hs' hne
  have h1 := op_strictConcave_tangent hu (show w - s ∈ Set.Ioi 0 from by simp; linarith)
    (show w - s' ∈ Set.Ioi 0 from by simp; linarith [hs'.2])
    (fun h => hne (by linarith)) hy
  have h2 := op_concave_tangent hu.concaveOn (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
    (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs'.1) ho
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  have : up (w - s) * (w - s' - (w - s)) + β * (up (R * s) * (R * s' - R * s)) = 0 := by
    rw [heul]; ring
  nlinarith

/-- The Inada condition `u′(0) = ∞`, in the form used below. -/
theorem op_inada_small {up : ℝ → ℝ} (hinada : Tendsto up (𝓝[>] 0) atTop) (M : ℝ) :
    ∃ ε > 0, ∀ c, 0 < c → c < ε → M < up c := by
  obtain ⟨ε, hε, hsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 (hinada.eventually_gt_atTop M)
  exact ⟨ε, hε, fun c hc hcε => hsub ⟨hc, hcε⟩⟩

/-- Miao, p. 545: "solving yields a saving function `s_t = s(w_t, R_{t+1})`". With a
continuous, strictly decreasing marginal utility `u′ > 0` satisfying the Inada condition at `0`,
the Euler equation has a solution `s ∈ (0, w)` for every `w > 0`, `R > 0`. -/
theorem op_saving_exists {up : ℝ → ℝ} {β w R : ℝ} (hβ : 0 < β) (hw : 0 < w) (hR : 0 < R)
    (hcont : ContinuousOn up (Set.Ioi 0)) (hanti : StrictAntiOn up (Set.Ioi 0))
    (hinada : Tendsto up (𝓝[>] 0) atTop) :
    ∃ s, 0 < s ∧ s < w ∧ up (w - s) = β * up (R * s) * R := by
  have hβR : 0 < β * R := mul_pos hβ hR
  obtain ⟨ε1, hε1, h1⟩ := op_inada_small hinada (up (w / 2) / (β * R))
  obtain ⟨ε2, hε2, h2⟩ := op_inada_small hinada (β * R * up (R * w / 2))
  set c1 := min (ε1 / 2) (R * w / 4) with hc1
  have hc1pos : 0 < c1 := lt_min (by linarith) (by positivity)
  have hc1le : c1 ≤ R * w / 4 := min_le_right _ _
  have hc1lt : c1 < ε1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set s1 := c1 / R with hs1
  have hs1pos : 0 < s1 := div_pos hc1pos hR
  have hRs1 : R * s1 = c1 := by rw [hs1]; field_simp
  have hs1le : s1 ≤ w / 4 := by
    rw [hs1, div_le_iff₀ hR]; linarith
  set c2 := min (ε2 / 2) (w / 4) with hc2
  have hc2pos : 0 < c2 := lt_min (by linarith) (by positivity)
  have hc2le : c2 ≤ w / 4 := min_le_right _ _
  have hc2lt : c2 < ε2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set s2 := w - c2 with hs2
  set g : ℝ → ℝ := fun s => up (w - s) - β * up (R * s) * R with hg
  have hg1 : g s1 < 0 := by
    have ha := h1 c1 hc1pos hc1lt
    have hb : up (w - s1) < up (w / 2) :=
      hanti (show w / 2 ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s1 ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    rw [div_lt_iff₀ hβR] at ha
    simp only [hg, hRs1]
    nlinarith
  have hg2 : 0 < g s2 := by
    have ha : β * R * up (R * w / 2) < up c2 := h2 c2 hc2pos hc2lt
    have hb : up (R * s2) < up (R * w / 2) :=
      hanti (show R * w / 2 ∈ Set.Ioi 0 from by rw [Set.mem_Ioi]; positivity)
        (show R * s2 ∈ Set.Ioi 0 from mul_pos hR (by simp [hs2]; linarith))
        (by rw [hs2]; nlinarith)
    have hc : w - s2 = c2 := by rw [hs2]; ring
    simp only [hg, hc]
    nlinarith
  have hle : s1 ≤ s2 := by rw [hs2]; linarith
  have hsub : Set.Icc s1 s2 ⊆ Set.Ioo 0 w := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hgc : ContinuousOn g (Set.Icc s1 s2) := by
    apply ContinuousOn.sub
    · exact hcont.comp (continuousOn_const.sub continuousOn_id)
        (fun x hx => by simp; linarith [(hsub hx).2])
    · apply ContinuousOn.mul _ continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact hcont.comp (continuousOn_const.mul continuousOn_id)
        (fun x hx => by simp only [Set.mem_Ioi]; exact mul_pos hR (hsub hx).1)
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc hle hgc ⟨hg1.le, hg2.le⟩
  refine ⟨s, (hsub hs).1, (hsub hs).2, ?_⟩
  simp only [hg] at hgs
  linarith

/-- Miao, p. 545: the saving function is well defined: with strictly decreasing marginal
utility the Euler equation has at most one solution in `(0, w)`. -/
theorem op_saving_unique {up : ℝ → ℝ} {β w R s s' : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hanti : StrictAntiOn up (Set.Ioi 0)) (hs0 : 0 < s) (hsw : s < w) (hs0' : 0 < s')
    (hsw' : s' < w) (he : up (w - s) = β * up (R * s) * R)
    (he' : up (w - s') = β * up (R * s') * R) : s = s' := by
  have hβR : 0 < β * R := mul_pos hβ hR
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have ha : up (w - s) < up (w - s') :=
      hanti (show w - s' ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    have hb : up (R * s') < up (R * s) :=
      hanti (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
        (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0') (by nlinarith)
    nlinarith
  · have ha : up (w - s') < up (w - s) :=
      hanti (show w - s ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s' ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    have hb : up (R * s) < up (R * s') :=
      hanti (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0')
        (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0) (by nlinarith)
    nlinarith

/-- Miao, p. 545: "`0 < s_w < 1`; saving is an increasing function of the wage rate by the
concavity of `u`". If `s` solves the Euler equation at the wage `w` and `s′` at `w′ > w` (same
`R`), then saving rises strictly, `s < s′`, and so does first-period consumption,
`w − s < w′ − s′` (so `0 < s′ − s < w′ − w`). -/
theorem op_saving_wage_mono {up : ℝ → ℝ} {β w w' R s s' : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hanti : StrictAntiOn up (Set.Ioi 0)) (hww : w < w') (hs0 : 0 < s) (hsw : s < w)
    (hs0' : 0 < s') (hsw' : s' < w') (he : up (w - s) = β * up (R * s) * R)
    (he' : up (w' - s') = β * up (R * s') * R) : s < s' ∧ w - s < w' - s' := by
  have hβR : 0 < β * R := mul_pos hβ hR
  constructor
  · by_contra h
    push Not at h
    have ha : up (w' - s') < up (w - s) :=
      hanti (show w - s ∈ Set.Ioi 0 from by simp; linarith)
        (show w' - s' ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    have hb : up (R * s) ≤ up (R * s') :=
      hanti.antitoneOn (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0')
        (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0) (by nlinarith)
    nlinarith
  · by_contra h
    push Not at h
    have ha : up (w - s) ≤ up (w' - s') :=
      hanti.antitoneOn (show w' - s' ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s ∈ Set.Ioi 0 from by simp; linarith) h
    have hb : up (R * s') < up (R * s) :=
      hanti (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
        (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0') (by nlinarith)
    nlinarith

/-- Miao, p. 545: the implicit derivative of the saving function. If `sf` is a saving function
(it solves the Euler equation for all wages near `w`), differentiable at `w` with derivative
`s_w`, and `u′` has derivative `u″` at both consumptions, then
`u″(c_y)(1 − s_w) = βR²u″(c_o)s_w`; with `u″ < 0` this gives `0 < s_w < 1`. -/
theorem op_saving_sw {up upp sf : ℝ → ℝ} {β w R sw : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hsf : ∀ᶠ w' in 𝓝 w, up (w' - sf w') = β * up (R * sf w') * R)
    (hd : HasDerivAt sf sw w) (hy : HasDerivAt up (upp (w - sf w)) (w - sf w))
    (ho : HasDerivAt up (upp (R * sf w)) (R * sf w)) :
    upp (w - sf w) * (1 - sw) = β * R ^ 2 * upp (R * sf w) * sw ∧
      (upp (w - sf w) < 0 → upp (R * sf w) < 0 → 0 < sw ∧ sw < 1) := by
  have h1 : HasDerivAt (fun x => up (x - sf x)) (upp (w - sf w) * (1 - sw)) w :=
    hy.comp w ((hasDerivAt_id w).sub hd)
  have h2 : HasDerivAt (fun x => β * up (R * sf x) * R)
      (β * (upp (R * sf w) * (R * sw)) * R) w :=
    ((ho.comp w (hd.const_mul R)).const_mul β).mul_const R
  have h1' : HasDerivAt (fun x => β * up (R * sf x) * R) (upp (w - sf w) * (1 - sw)) w :=
    h1.congr_of_eventuallyEq (hsf.mono fun x hx => hx.symm)
  have heq := h1'.unique h2
  refine ⟨by rw [heq]; ring, fun hny hno => ?_⟩
  have hk : 0 < β * R ^ 2 := by positivity
  have hpos : 0 < -upp (R * sf w) * (β * R ^ 2) := mul_pos (by linarith) hk
  constructor
  · by_contra h
    push Not at h
    have : upp (w - sf w) * (1 - sw) < 0 := mul_neg_of_neg_of_pos hny (by linarith)
    have : 0 ≤ β * R ^ 2 * upp (R * sf w) * sw := by nlinarith
    linarith
  · by_contra h
    push Not at h
    have : 0 ≤ upp (w - sf w) * (1 - sw) := mul_nonneg_of_nonpos_of_nonpos hny.le (by linarith)
    have : β * R ^ 2 * upp (R * sf w) * sw < 0 := by nlinarith
    linarith

/-- Optimal saving with log utility, wage `y₁` and second-period income `y₂`:
`s = (βy₁ − y₂/R)/(1 + β)`. -/
noncomputable def opLogSaving (β y1 y2 R : ℝ) : ℝ :=
  (β * y1 - y2 / R) / (1 + β)

/-- Log utility `ln c_y + β ln c_o` with budget `c_y = y₁ − s`, `c_o = Rs + y₂`: the saving
`opLogSaving` gives `c_y = W/(1 + β)`, `c_o = βRW/(1 + β)` with `W = y₁ + y₂/R`, and maximises
lifetime utility over every `s` with both consumptions positive. -/
theorem op_log_saving {β y1 y2 R : ℝ} (hβ : 0 < β) (hR : 0 < R) (hW : 0 < y1 + y2 / R) :
    y1 - opLogSaving β y1 y2 R = (y1 + y2 / R) / (1 + β) ∧
      R * opLogSaving β y1 y2 R + y2 = β * R * (y1 + y2 / R) / (1 + β) ∧
      ∀ s, 0 < y1 - s → 0 < R * s + y2 →
        Real.log (y1 - s) + β * Real.log (R * s + y2) ≤
          Real.log (y1 - opLogSaving β y1 y2 R) +
            β * Real.log (R * opLogSaving β y1 y2 R + y2) := by
  have hcy : y1 - opLogSaving β y1 y2 R = (y1 + y2 / R) / (1 + β) := by
    unfold opLogSaving; field_simp; ring
  have hco : R * opLogSaving β y1 y2 R + y2 = β * R * (y1 + y2 / R) / (1 + β) := by
    unfold opLogSaving; field_simp; ring
  refine ⟨hcy, hco, fun s hs1 hs2 => ?_⟩
  set W := y1 + y2 / R
  have hcyp : 0 < W / (1 + β) := by positivity
  have hcop : 0 < β * R * W / (1 + β) := by positivity
  have key : ∀ x c : ℝ, 0 < x → 0 < c → Real.log x ≤ Real.log c + x / c - 1 := by
    intro x c hx hc
    have := Real.log_le_sub_one_of_pos (div_pos hx hc)
    rw [Real.log_div hx.ne' hc.ne'] at this
    linarith
  have k1 := key (y1 - s) _ hs1 hcyp
  have k2 := key (R * s + y2) _ hs2 hcop
  rw [hcy, hco]
  have h3 := mul_le_mul_of_nonneg_left k2 hβ.le
  have : (y1 - s) / (W / (1 + β)) - 1 + β * ((R * s + y2) / (β * R * W / (1 + β)) - 1) = 0 := by
    have hW' : W ≠ 0 := hW.ne'
    have hWR : W * R = y1 * R + y2 := by simp only [W]; field_simp
    field_simp
    linear_combination (-(1 + β)) * hWR
  nlinarith

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Diamond (1965) model: equilibrium law of motion and steady states

Miao, §16.2, pp. 544–549. Technology `f(k) = F(k, 1)` with `f(0) = 0`, `f′ > 0`, `f` strictly
concave, `f′(∞) = 0`; no depreciation; population `N_{t+1} = g_n N_t`.

* Firms: (16.14) `w = f(k) − kf′(k)` and (16.15) `R = 1 + f′(k)` are the first-order conditions
  of profit maximisation with `F(K, N) = Nf(K/N)` (`eq_16_14`, `eq_16_15`, `op_F_hasDerivAt_K`,
  `op_F_hasDerivAt_N`), and factor payments exhaust output (`op_euler_identity`).
* Capital-market clearing `K_{t+1} = N_t s_t` gives `g_n k_{t+1} = s_t`
  (`op_capital_market`), and the equilibrium law (16.16) (`OPIsDiamondEqm`, `eq_16_16`).
* The wage: positive, strictly increasing, `w(0+) = 0`, `w(k)/k = f(k)/k − f′(k) → 0`
  (`op_wage_pos`, `op_wage_strictMono`, `op_wage_tendsto_zero`, `op_f_div_tendsto_zero`,
  `op_wage_div_tendsto_zero`).
* With `s_R ≥ 0`, (16.16) has a unique solution `k_{t+1} = G(k_t)` (`op_temporary_eqm`,
  `op_G_exists`); `G` is increasing (`op_G_strictMono`), `G(0+) = 0` (`op_G_tendsto_zero`),
  `G(k)/k → 0` (`op_G_div_tendsto_zero`), so `G` eventually lies below the diagonal
  (`op_G_eventually_below`).
* The slope `dk_{t+1}/dk_t = −s_w kf″(k)/(g_n − s_R f″(k_{t+1}))` by implicit differentiation
  (`op_G_slope`, `op_G_slope_pos`, `op_G_slope_steady`).
* Steady states: `G′(0) > 1` gives at least one positive steady state (`op_exists_fixed`,
  `op_above_diag_of_deriv`). **Correction:** "odd" and "even" numbers of positive steady states
  are false in general: functions with all the listed properties and `G′(0) = 2` resp. `1/2`
  have exactly two resp. one positive steady states (`op_odd_counterexample`,
  `op_even_counterexample`).
* The Diamond conditions: **correction** — condition (ii) must read `G′(0) > 1`; with the
  printed `G′(0) < 1` together with (iii) there is no positive steady state at all
  (`op_diamond_conditions_printed`). With `G′(0) > 1` and `G′(k*) < 1` at every positive steady
  state there is exactly one positive steady state `k_D` (`op_diamond_conditions`), it is
  globally stable for increasing `G` (`op_fixed_signs`, `op_global_convergence`), and
  `|G′(k*)| < 1` gives local stability (`op_local_stability`).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- The competitive wage (16.14): `w(k) = f(k) − kf′(k)`. -/
def opWage (f fp : ℝ → ℝ) (k : ℝ) : ℝ := f k - k * fp k

/-- The gross interest rate (16.15): `R(k) = 1 + f′(k)` (no depreciation). -/
def opRate (fp : ℝ → ℝ) (k : ℝ) : ℝ := 1 + fp k

/-! ### Firms -/

/-- `∂F/∂K = f′(K/N)` for `F(K, N) = Nf(K/N)`. -/
theorem op_F_hasDerivAt_K {f fp : ℝ → ℝ} {K N : ℝ} (hN : N ≠ 0)
    (hf : HasDerivAt f (fp (K / N)) (K / N)) :
    HasDerivAt (fun K' => N * f (K' / N)) (fp (K / N)) K := by
  have h1 : HasDerivAt (fun K' => K' / N) (1 / N) K := (hasDerivAt_id K).div_const N
  have := (hf.comp K h1).const_mul N
  simp only [Function.comp_def] at this
  convert this using 1
  field_simp

/-- `∂F/∂N = f(k) − kf′(k)` with `k = K/N`, for `F(K, N) = Nf(K/N)`. -/
theorem op_F_hasDerivAt_N {f fp : ℝ → ℝ} {K N : ℝ} (hN : N ≠ 0)
    (hf : HasDerivAt f (fp (K / N)) (K / N)) :
    HasDerivAt (fun N' => N' * f (K / N')) (opWage f fp (K / N)) N := by
  have h1 : HasDerivAt (fun N' => K / N') (-(K / N ^ 2)) N := by
    have := (hasDerivAt_inv hN).const_mul K
    convert this using 1
    · ext x; simp [div_eq_mul_inv]
    · ring
  have := (hasDerivAt_id' N).mul (hf.comp N h1)
  simp only [Function.comp_def] at this
  convert this using 1
  simp only [opWage]
  field_simp
  ring

/-- Miao, (16.15), p. 545: if the capital input `K` maximises profit
`Nf(K′/N) − (R − 1)K′` over `K′ > 0`, then `R = 1 + f′(k)`. -/
theorem eq_16_15 {f fp : ℝ → ℝ} {K N R : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hf : HasDerivAt f (fp (K / N)) (K / N))
    (hmax : ∀ K' > 0, N * f (K' / N) - (R - 1) * K' ≤ N * f (K / N) - (R - 1) * K) :
    R = opRate fp (K / N) := by
  have hloc : IsLocalMax (fun K' => N * f (K' / N) - (R - 1) * K') K :=
    Filter.eventually_of_mem (Ioi_mem_nhds hK) hmax
  have hd := (op_F_hasDerivAt_K hN.ne' hf).sub ((hasDerivAt_id K).const_mul (R - 1))
  have := hloc.hasDerivAt_eq_zero hd
  simp only [opRate]
  simp only [mul_one] at this
  linarith

/-- Miao, (16.14), p. 545: if the labour input `N` maximises profit `N′f(K/N′) − wN′` over
`N′ > 0`, then `w = f(k) − kf′(k)`. -/
theorem eq_16_14 {f fp : ℝ → ℝ} {K N w : ℝ} (hN : 0 < N)
    (hf : HasDerivAt f (fp (K / N)) (K / N))
    (hmax : ∀ N' > 0, N' * f (K / N') - w * N' ≤ N * f (K / N) - w * N) :
    w = opWage f fp (K / N) := by
  have hloc : IsLocalMax (fun N' => N' * f (K / N') - w * N') N :=
    Filter.eventually_of_mem (Ioi_mem_nhds hN) hmax
  have hd := (op_F_hasDerivAt_N hN.ne' hf).sub ((hasDerivAt_id N).const_mul w)
  have := hloc.hasDerivAt_eq_zero hd
  simp only [mul_one] at this
  linarith

/-- Factor payments exhaust output: `Nf(K/N) = f′(k)K + w(k)N` (constant returns). -/
theorem op_euler_identity (f fp : ℝ → ℝ) {K N : ℝ} (hN : N ≠ 0) :
    N * f (K / N) = fp (K / N) * K + opWage f fp (K / N) * N := by
  simp only [opWage]; field_simp; ring

/-! ### Capital-market equilibrium and (16.16) -/

/-- Miao, p. 546: `K_{t+1} = N_t s_t`, `K_t = k_tN_t` and `N_{t+1} = g_nN_t` give
`g_nk_{t+1} = s_t`. -/
theorem op_capital_market {K k N s : ℕ → ℝ} {gn : ℝ} (t : ℕ) (hKs : K (t + 1) = N t * s t)
    (hk : ∀ t, K t = k t * N t) (hN : N (t + 1) = gn * N t) (hN0 : N t ≠ 0) :
    gn * k (t + 1) = s t := by
  have h := hk (t + 1)
  rw [hKs, hN] at h
  have : N t * (gn * k (t + 1) - s t) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hN0
  linarith

/-- The Diamond equilibrium (16.16): `k_t > 0` and
`k_{t+1} = s(f(k_t) − k_tf′(k_t), 1 + f′(k_{t+1}))/g_n` for all `t`. -/
def OPIsDiamondEqm (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn : ℝ) (k : ℕ → ℝ) : Prop :=
  ∀ t, 0 < k t ∧ k (t + 1) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) / gn

/-- Miao, (16.16), p. 546: optimal saving `s_t = s(w_t, R_{t+1})`, the factor prices
(16.14)–(16.15) and capital-market clearing `g_nk_{t+1} = s_t` characterise the Diamond
equilibrium. -/
theorem eq_16_16 {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn) {k w R sv : ℕ → ℝ}
    (hk : ∀ t, 0 < k t) (hw : ∀ t, w t = opWage f fp (k t)) (hR : ∀ t, R t = opRate fp (k t))
    (hsv : ∀ t, sv t = s (w t) (R (t + 1))) (hcm : ∀ t, gn * k (t + 1) = sv t) :
    OPIsDiamondEqm s f fp gn k := by
  intro t
  refine ⟨hk t, ?_⟩
  rw [eq_div_iff hgn.ne', mul_comm, hcm t, hsv t, hw t, hR (t + 1)]

/-- Conversely, a Diamond equilibrium satisfies capital-market clearing with optimal saving. -/
theorem op_diamondEqm_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    {k : ℕ → ℝ} : OPIsDiamondEqm s f fp gn k ↔
      ∀ t, 0 < k t ∧ gn * k (t + 1) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) := by
  refine forall_congr' fun t => and_congr_right fun _ => ?_
  rw [eq_div_iff hgn.ne', mul_comm]

/-! ### Properties of the technology and the wage -/

/-- Strict concavity makes `f′` strictly decreasing. -/
theorem op_fp_strictAnti {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) : StrictAntiOn fp (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (le_of_lt hx)
  have hy' : y ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 (le_of_lt hy)
  have h1 := hconc.slope_lt_of_hasDerivAt hx' hy' hxy (hfd x hx)
  have h2 := hconc.lt_slope_of_hasDerivAt hx' hy' hxy (hfd y hy)
  linarith

/-- The wage is positive: `f(k) − kf′(k) > 0` for `k > 0` (strict concavity, `f(0) = 0`). -/
theorem op_wage_pos {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    {k : ℝ} (hk : 0 < k) (hd : HasDerivAt f (fp k) k) : 0 < opWage f fp k := by
  have := op_strictConcave_tangent hconc (Set.mem_Ici.2 hk.le) (Set.mem_Ici.2 le_rfl)
    hk.ne hd
  rw [hf0] at this
  simp only [opWage]
  linarith

/-- The wage is strictly increasing in `k` (Miao, p. 546: "an increase in the capital stock in
period `t` increases the wage"). -/
theorem op_wage_strictMono {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) : StrictMonoOn (opWage f fp) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have h1 := op_strictConcave_tangent hconc (Set.mem_Ici.2 hy'.le) (Set.mem_Ici.2 hx'.le)
    hxy.ne (hfd y hy')
  have h2 := op_fp_strictAnti hconc hfd hx hy hxy
  simp only [opWage]
  nlinarith

/-- `w(k) < f(k)` when `f′(k) > 0`. -/
theorem op_wage_lt {f fp : ℝ → ℝ} {k : ℝ} (hk : 0 < k) (hfp : 0 < fp k) :
    opWage f fp k < f k := by
  simp only [opWage]; nlinarith

/-- `w(0+) = 0`: the wage tends to `0` as `k → 0`. -/
theorem op_wage_tendsto_zero {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : f 0 = 0) (hfc : ContinuousWithinAt f (Set.Ioi 0) 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k) :
    Tendsto (opWage f fp) (𝓝[>] 0) (𝓝 0) := by
  have hf : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have := hfc.tendsto; rwa [hf0] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hf ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (op_wage_pos hconc hf0 hk (hfd k hk)).le
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (op_wage_lt hk (hfp k hk)).le

/-- `w(k)/k = f(k)/k − f′(k)`. -/
theorem op_wage_div_eq (f fp : ℝ → ℝ) {k : ℝ} (hk : k ≠ 0) :
    opWage f fp k / k = f k / k - fp k := by
  simp only [opWage]; field_simp

/-- `f(k)/k → 0` as `k → ∞`, from `f′(∞) = 0` and concavity. -/
theorem op_f_div_tendsto_zero {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : f 0 = 0) (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k)
    (hfp : ∀ k, 0 < k → 0 < fp k) (hinf : Tendsto fp atTop (𝓝 0)) :
    Tendsto (fun k => f k / k) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K1, hK1⟩ := eventually_atTop.1 (hinf.eventually (eventually_lt_nhds (half_pos hε)))
  set K := max K1 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfK : fp K < ε / 2 := hK1 K (le_max_left _ _)
  refine ⟨max (K + 1) (2 * |f K| / ε + 1), fun n hn => ?_⟩
  have hn1 : K + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 * |f K| / ε + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : 0 < n := by linarith
  have htan := op_concave_tangent hconc.concaveOn (Set.mem_Ici.2 hK.le)
    (Set.mem_Ici.2 hn0.le) (hfd K hK)
  have hfn : 0 < f n := by
    have := op_wage_pos hconc hf0 hn0 (hfd n hn0)
    have := hfp n hn0
    simp only [opWage] at *
    nlinarith
  have hfKp := hfp K hK
  have hb : f n < |f K| + ε / 2 * n := by
    have : fp K * (n - K) ≤ fp K * n := by nlinarith
    have : fp K * n < ε / 2 * n := by nlinarith
    linarith [le_abs_self (f K)]
  have h2 : 2 * |f K| / ε < n := by linarith
  rw [div_lt_iff₀ hε] at h2
  rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hfn hn0), div_lt_iff₀ hn0]
  nlinarith

/-- `w(k)/k → 0` as `k → ∞`. -/
theorem op_wage_div_tendsto_zero {f fp : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hf0 : f 0 = 0) (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k)
    (hfp : ∀ k, 0 < k → 0 < fp k) (hinf : Tendsto fp atTop (𝓝 0)) :
    Tendsto (fun k => opWage f fp k / k) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (op_f_div_tendsto_zero hconc hf0 hfd hfp hinf) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (div_pos (op_wage_pos hconc hf0 hk (hfd k hk)) hk).le
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact div_le_div_of_nonneg_right (op_wage_lt hk (hfp k hk)).le hk.le

/-! ### The temporary equilibrium `k_{t+1} = G(k_t)` -/

/-- Miao, p. 546: "If `s_R > 0` ... we can solve for `k_{t+1}` as a function of `k_t`". Given
the wage `w > 0`, if `x ↦ S(x) = s(w, R(x))` is continuous, nonincreasing (`s_R ≥ 0` and `R`
decreasing) and `0 < S < w`, then `g_n x = S(x)` has exactly one solution `x > 0`. -/
theorem op_temporary_eqm {S : ℝ → ℝ} {gn w : ℝ} (hgn : 0 < gn)
    (hpos : ∀ x, 0 < x → 0 < S x) (hlt : ∀ x, 0 < x → S x < w)
    (hanti : AntitoneOn S (Set.Ioi 0)) (hcont : ContinuousOn S (Set.Ioi 0)) :
    ∃! x, 0 < x ∧ gn * x = S x := by
  have hw : 0 < w := lt_trans (hpos 1 one_pos) (hlt 1 one_pos)
  set xb := w / gn with hxb
  have hxb0 : 0 < xb := div_pos hw hgn
  have hgxb : gn * xb = w := by rw [hxb]; field_simp
  set x0 := S xb / gn with hx0
  have hx00 : 0 < x0 := div_pos (hpos xb hxb0) hgn
  have hgx0 : gn * x0 = S xb := by rw [hx0]; field_simp
  have hx0xb : x0 < xb := by
    have := hlt xb hxb0
    nlinarith
  set h : ℝ → ℝ := fun x => gn * x - S x with hh
  have hcont' : ContinuousOn h (Set.Icc x0 xb) :=
    (continuousOn_const.mul continuousOn_id).sub
      (hcont.mono fun x hx => lt_of_lt_of_le hx00 hx.1)
  have h0 : h x0 ≤ 0 := by
    simp only [hh]
    have := hanti hx00 hxb0 hx0xb.le
    linarith
  have h1 : 0 ≤ h xb := by
    simp only [hh]
    linarith [hlt xb hxb0]
  obtain ⟨x, hx, hx'⟩ := intermediate_value_Icc hx0xb.le hcont' ⟨h0, h1⟩
  refine ⟨x, ⟨lt_of_lt_of_le hx00 hx.1, by simp only [hh] at hx'; linarith⟩, ?_⟩
  rintro y ⟨hy0, hy⟩
  have hx0' : 0 < x := lt_of_lt_of_le hx00 hx.1
  have hxe : gn * x = S x := by simp only [hh] at hx'; linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt' | hlt'
  · have := hanti hy0 hx0' hlt'.le
    nlinarith
  · have := hanti hx0' hy0 hlt'.le
    nlinarith

/-- `s_R ≥ 0` and `f′` decreasing make `x ↦ s(w, R(x))` nonincreasing. -/
theorem op_S_antitone {s : ℝ → ℝ → ℝ} {fp : ℝ → ℝ} {w : ℝ}
    (hmonoR : MonotoneOn (s w) (Set.Ioi 1)) (hfanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) :
    AntitoneOn (fun x => s w (opRate fp x)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have h1 : fp y ≤ fp x := hfanti.antitoneOn hx hy hxy
  exact hmonoR (show opRate fp y ∈ Set.Ioi 1 by simp [opRate, hfp y hy'])
    (show opRate fp x ∈ Set.Ioi 1 by simp [opRate, hfp x hx']) (by simp [opRate]; linarith)

/-- Miao, p. 546: with `s_R ≥ 0` the equilibrium law (16.16) defines a function
`k_{t+1} = G(k_t)` on `k > 0`. -/
theorem op_G_exists {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hfpc : ContinuousOn fp (Set.Ioi 0))
    (hpos : ∀ w, 0 < w → ∀ R, 1 < R → 0 < s w R) (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hmonoR : ∀ w, 0 < w → MonotoneOn (s w) (Set.Ioi 1))
    (hcontR : ∀ w, 0 < w → ContinuousOn (s w) (Set.Ioi 1)) :
    ∃ G : ℝ → ℝ, ∀ k, 0 < k →
      0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k)) := by
  have hfanti := op_fp_strictAnti hconc hfd
  have H : ∀ k, 0 < k → ∃ x, 0 < x ∧ gn * x = s (opWage f fp k) (opRate fp x) := by
    intro k hk
    have hw := op_wage_pos hconc hf0 hk (hfd k hk)
    have hR : ∀ x, 0 < x → 1 < opRate fp x := fun x hx => by simp [opRate, hfp x hx]
    obtain ⟨x, hx, -⟩ := op_temporary_eqm (S := fun x => s (opWage f fp k) (opRate fp x))
      (w := opWage f fp k) hgn (fun x hx => hpos _ hw _ (hR x hx))
      (fun x hx => hlt _ hw _ (hR x hx)) (op_S_antitone (hmonoR _ hw) hfanti hfp)
      ((hcontR _ hw).comp (continuousOn_const.add hfpc) fun x hx => hR x hx)
    exact ⟨x, hx⟩
  choose! G hG using H
  exact ⟨G, hG⟩

/-- Miao, p. 546: "`G` is an increasing function". If saving rises strictly with the wage and
`s_R ≥ 0`, any solution `G` of (16.16) is strictly increasing. -/
theorem op_G_strictMono {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hsw : ∀ w w' R, 0 < w → w < w' → 1 < R → s w R < s w' R)
    (hmonoR : ∀ w, 0 < w → MonotoneOn (s w) (Set.Ioi 1))
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    StrictMonoOn G (Set.Ioi 0) := by
  intro k hk k' hk' hkk
  have hk0 : (0 : ℝ) < k := hk
  have hk0' : (0 : ℝ) < k' := hk'
  obtain ⟨hG1, hE1⟩ := hG k hk0
  obtain ⟨hG2, hE2⟩ := hG k' hk0'
  have hw := op_wage_pos hconc hf0 hk0 (hfd k hk0)
  have hww := op_wage_strictMono hconc hfd hk hk' hkk
  have hanti := op_S_antitone (hmonoR _ (lt_trans hw hww)) (op_fp_strictAnti hconc hfd) hfp
  by_contra h
  push Not at h
  have h1 : s (opWage f fp k) (opRate fp (G k)) < s (opWage f fp k') (opRate fp (G k)) :=
    hsw _ _ _ hw hww (by simp [opRate, hfp _ hG1])
  have h2 := hanti (show G k' ∈ Set.Ioi 0 from hG2) (show G k ∈ Set.Ioi 0 from hG1) h
  nlinarith

/-- `G(k) < w(k)/g_n`: the capital stock is bounded by the wage bill (Miao, p. 546,
`g_nk_{t+1}/k_t ≤ w_t/k_t`). -/
theorem op_G_lt_wage {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k)))
    {k : ℝ} (hk : 0 < k) : gn * G k < opWage f fp k := by
  obtain ⟨hG1, hE⟩ := hG k hk
  rw [hE]
  exact hlt _ (op_wage_pos hconc hf0 hk (hfd k hk)) _ (by simp [opRate, hfp _ hG1])

/-- Miao, p. 546: `G(0) = 0`, as the limit `G(k) → 0` as `k → 0+`. -/
theorem op_G_tendsto_zero {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfc : ContinuousWithinAt f (Set.Ioi 0) 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    Tendsto G (𝓝[>] 0) (𝓝 0) := by
  have hw := (op_wage_tendsto_zero hconc hf0 hfc hfd hfp).div_const gn
  rw [zero_div] at hw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with k hk
    exact (hG k hk).1.le
  · filter_upwards [self_mem_nhdsWithin] with k hk
    rw [le_div_iff₀ hgn, mul_comm]
    exact (op_G_lt_wage hconc hf0 hfd hfp hlt hG hk).le

/-- Miao, p. 546: `lim_{k→∞} G(k)/k = 0`. -/
theorem op_G_div_tendsto_zero {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k) (hfp : ∀ k, 0 < k → 0 < fp k)
    (hinf : Tendsto fp atTop (𝓝 0)) (hlt : ∀ w, 0 < w → ∀ R, 1 < R → s w R < w)
    (hG : ∀ k, 0 < k → 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    Tendsto (fun k => G k / k) atTop (𝓝 0) := by
  have hw := (op_wage_div_tendsto_zero hconc hf0 hfd hfp hinf).div_const gn
  rw [zero_div] at hw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hw ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with k hk
    exact (div_pos (hG k hk).1 hk).le
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have := op_G_lt_wage hconc hf0 hfd hfp hlt hG hk
    rw [div_div, le_div_iff₀ (mul_pos hk hgn)]
    have : G k / k * (k * gn) = gn * G k := by field_simp
    linarith

/-- Miao, p. 547: "`k_{t+1}/k_t = G(k_t)/k_t < 1` for `k_t` sufficiently large": the graph of `G`
eventually falls below the diagonal. -/
theorem op_G_eventually_below {G : ℝ → ℝ} (hG : Tendsto (fun k => G k / k) atTop (𝓝 0)) :
    ∃ M, ∀ k, M < k → G k < k := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((hG.eventually (eventually_lt_nhds one_pos)).and
    (eventually_gt_atTop 0))
  refine ⟨M, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hM k hk.le
  rwa [div_lt_one h2] at h1

/-! ### The slope of `G` -/

/-- The derivative of the wage: `w′(k) = −kf″(k)`. -/
theorem op_wage_hasDerivAt {f fp fpp : ℝ → ℝ} {k : ℝ} (hf : HasDerivAt f (fp k) k)
    (hfp : HasDerivAt fp (fpp k) k) : HasDerivAt (opWage f fp) (-k * fpp k) k := by
  have := hf.sub ((hasDerivAt_id' k).mul hfp)
  unfold opWage
  convert this using 1
  ring

/-- Miao, p. 546: implicit differentiation of (16.16). If `G` solves
`g_nG(k) = s(w(k), R(G(k)))` near `k`, with `s` differentiable at `(w(k), R(G(k)))` with partial
derivatives `s_w, s_R`, then `G′(k)(g_n − s_R f″(G(k))) = −s_w kf″(k)`. -/
theorem op_G_slope {s : ℝ → ℝ → ℝ} {f fp fpp G : ℝ → ℝ} {gn k G' sw sR : ℝ}
    (hG : ∀ᶠ x in 𝓝 k, gn * G x = s (opWage f fp x) (opRate fp (G x)))
    (hGd : HasDerivAt G G' k)
    (hs : HasFDerivAt (fun p : ℝ × ℝ => s p.1 p.2)
      (sw • ContinuousLinearMap.fst ℝ ℝ ℝ + sR • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (opWage f fp k, opRate fp (G k)))
    (hf : HasDerivAt f (fp k) k) (hfpk : HasDerivAt fp (fpp k) k)
    (hfpG : HasDerivAt fp (fpp (G k)) (G k)) :
    G' * (gn - sR * fpp (G k)) = -sw * k * fpp k := by
  have hw := op_wage_hasDerivAt hf hfpk
  have hR : HasDerivAt (fun x => opRate fp (G x)) (fpp (G k) * G') k := by
    have := (hfpG.comp k hGd).const_add 1
    unfold opRate
    exact this
  have hg := hs.comp_hasDerivAt k (hw.prodMk hR)
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at hg
  have hl : HasDerivAt (fun x => gn * G x) (gn * G') k := hGd.const_mul gn
  have hl' : HasDerivAt (fun x => s (opWage f fp x) (opRate fp (G x))) (gn * G') k :=
    hl.congr_of_eventuallyEq (hG.mono fun x hx => hx.symm)
  have := hl'.unique hg
  linarith

/-- Miao, p. 546: "if `s_R > 0`, then the denominator is positive", and the numerator
`−s_wkf″(k)` is positive, so `G′(k) = −s_wkf″(k)/(g_n − s_Rf″(G(k))) > 0`. -/
theorem op_G_slope_pos {gn k G' sw sR fppk fppG : ℝ} (hgn : 0 < gn) (hk : 0 < k)
    (hsw : 0 < sw) (hsR : 0 ≤ sR) (hk2 : fppk < 0) (hG2 : fppG < 0)
    (h : G' * (gn - sR * fppG) = -sw * k * fppk) :
    0 < gn - sR * fppG ∧ 0 < -sw * k * fppk ∧ G' = -sw * k * fppk / (gn - sR * fppG) ∧
      0 < G' := by
  have hd : 0 < gn - sR * fppG := by nlinarith
  have hn : 0 < -sw * k * fppk := by
    have : 0 < sw * k := mul_pos hsw hk
    nlinarith
  have hG' : G' = -sw * k * fppk / (gn - sR * fppG) := by
    rw [eq_div_iff hd.ne']; exact h
  exact ⟨hd, hn, hG', by rw [hG']; exact div_pos hn hd⟩

/-- Miao, p. 549: at a positive steady state `G(k*) = k*` the slope is
`G′(k*) = −s_wk*f″(k*)/(g_n − s_Rf″(k*))`. -/
theorem op_G_slope_steady {gn kstar G' sw sR fpp : ℝ} (hden : gn - sR * fpp ≠ 0)
    (h : G' * (gn - sR * fpp) = -sw * kstar * fpp) :
    G' = -sw * kstar * fpp / (gn - sR * fpp) := by
  rw [eq_div_iff hden]; exact h

/-! ### Steady states of `k_{t+1} = G(k_t)` -/

/-- Intermediate values for `G − id`, upward crossing. -/
theorem op_ivt_up {G : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn G (Set.Ioi 0)) (ha : 0 < a)
    (hab : a < b) (hA : G a < a) (hB : b < G b) : ∃ z, a < z ∧ z < b ∧ G z = z := by
  have hcont : ContinuousOn (fun x => G x - x) (Set.Icc a b) :=
    (hc.mono fun x hx => lt_of_lt_of_le ha hx.1).sub continuousOn_id
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hab.le hcont
    (show (0 : ℝ) ∈ Set.Ioo (G a - a) (G b - b) from ⟨by linarith, by linarith⟩)
  exact ⟨z, hz.1, hz.2, by simp only at hz0; linarith⟩

/-- Intermediate values for `G − id`, downward crossing. -/
theorem op_ivt_down {G : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn G (Set.Ioi 0)) (ha : 0 < a)
    (hab : a < b) (hA : a < G a) (hB : G b < b) : ∃ z, a < z ∧ z < b ∧ G z = z := by
  have hcont : ContinuousOn (fun x => G x - x) (Set.Icc a b) :=
    (hc.mono fun x hx => lt_of_lt_of_le ha hx.1).sub continuousOn_id
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hab.le hcont
    (show (0 : ℝ) ∈ Set.Ioo (G b - b) (G a - a) from ⟨by linarith, by linarith⟩)
  exact ⟨z, hz.1, hz.2, by simp only at hz0; linarith⟩

/-- A steady state with `G′(k*) < 1` is crossed from above: `G > id` just left of `k*` and
`G < id` just right of it. -/
theorem op_slope_lt_one {G : ℝ → ℝ} {c d : ℝ} (hd : HasDerivAt G d c) (hfix : G c = c)
    (hd1 : d < 1) :
    ∃ δ > 0, ∀ y, c - δ < y → y < c + δ → (c < y → G y < y) ∧ (y < c → y < G y) := by
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  have hev := h.eventually (eventually_lt_nhds hd1)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨δ, hδ, fun y hy1 hy2 => ⟨fun hcy => ?_, fun hyc => ?_⟩⟩
  · have hdist : dist y c < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hdist (show y ∈ ({c} : Set ℝ)ᶜ from by simp; linarith)
    rw [slope_def_field, hfix, div_lt_iff₀ (by linarith)] at this
    linarith
  · have hdist : dist y c < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball hdist (show y ∈ ({c} : Set ℝ)ᶜ from by simp; linarith)
    rw [slope_def_field, hfix, div_lt_iff_of_neg (by linarith)] at this
    linarith

/-- The least steady state in `[a, b]`, when `b` is one. -/
theorem op_least_fixed {G : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn G (Set.Ioi 0)) (ha : 0 < a)
    (hab : a ≤ b) (hb : G b = b) :
    ∃ c, a ≤ c ∧ c ≤ b ∧ G c = c ∧ ∀ z, a ≤ z → z < c → G z ≠ z := by
  set A := Set.Icc a b ∩ (fun x => G x - x) ⁻¹' {0} with hA
  have hcl : IsClosed A :=
    ((hc.mono fun x hx => lt_of_lt_of_le ha hx.1).sub continuousOn_id).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hbA : b ∈ A := ⟨⟨hab, le_rfl⟩, by simp [hb]⟩
  have hbdd : BddBelow A := ⟨a, fun x hx => hx.1.1⟩
  have hcA := hcl.csInf_mem ⟨b, hbA⟩ hbdd
  refine ⟨sInf A, hcA.1.1, hcA.1.2, by have := hcA.2; simp at this; linarith, ?_⟩
  intro z hz hzc hGz
  have hzA : z ∈ A := ⟨⟨hz, by linarith [hcA.1.2]⟩, by simp [hGz]⟩
  exact absurd (csInf_le hbdd hzA) (not_le.2 hzc)

/-- If `G < id` at `y₁ < c` and `c` is a steady state with `G′(c) < 1`, there is a steady state
strictly between them. -/
theorem op_fixed_below {G : ℝ → ℝ} {y1 c d : ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hy1 : 0 < y1) (hlt : y1 < c) (hG1 : G y1 < y1) (hfix : G c = c) (hd : HasDerivAt G d c)
    (hd1 : d < 1) : ∃ z, y1 < z ∧ z < c ∧ G z = z := by
  obtain ⟨δ, hδ, hloc⟩ := op_slope_lt_one hd hfix hd1
  set y2 := max (c - δ / 2) ((y1 + c) / 2)
  have hy2c : y2 < c := max_lt (by linarith) (by linarith)
  have hy2a : c - δ < y2 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hy2b : y1 < y2 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hG2 : y2 < G y2 := (hloc y2 hy2a (by linarith)).2 hy2c
  obtain ⟨z, hz1, hz2, hz⟩ := op_ivt_up hc hy1 hy2b hG1 hG2
  exact ⟨z, hz1, by linarith, hz⟩

/-- `G′(0) > 1` in the sense of a right derivative at `0` with `G(0) = 0`: then `G(k) > k` for
small `k > 0`. -/
theorem op_above_diag_of_deriv {G : ℝ → ℝ} {d : ℝ} (hG0 : G 0 = 0)
    (hd : HasDerivWithinAt G d (Set.Ioi 0) 0) (hd1 : 1 < d) :
    ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hd
  obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (h.eventually (eventually_gt_nhds hd1))
  refine ⟨ε, hε, fun k hk hkε => ?_⟩
  have := hsub ⟨hk, hkε⟩
  simp only [Set.mem_ofPred_eq, slope_def_field, hG0, sub_zero] at this
  rwa [lt_div_iff₀ hk, one_mul] at this

/-- `G′(0) < 1`: then `G(k) < k` for small `k > 0`. -/
theorem op_below_diag_of_deriv {G : ℝ → ℝ} {d : ℝ} (hG0 : G 0 = 0)
    (hd : HasDerivWithinAt G d (Set.Ioi 0) 0) (hd1 : d < 1) :
    ∃ ε > 0, ∀ k, 0 < k → k < ε → G k < k := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hd
  obtain ⟨ε, hε, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (h.eventually (eventually_lt_nhds hd1))
  refine ⟨ε, hε, fun k hk hkε => ?_⟩
  have := hsub ⟨hk, hkε⟩
  simp only [Set.mem_ofPred_eq, slope_def_field, hG0, sub_zero] at this
  rwa [div_lt_iff₀ hk, one_mul] at this

/-- Miao, p. 547: "If `G′(0) > 1`, then [there are] positive steady states": `G` continuous on
`(0, ∞)`, above the diagonal near `0` and below it for large `k` has a positive steady
state. -/
theorem op_exists_fixed {G : ℝ → ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k) (hhigh : ∃ M, ∀ k, M < k → G k < k) :
    ∃ k, 0 < k ∧ G k = k := by
  obtain ⟨ε, hε, hl⟩ := hlow
  obtain ⟨M, hM⟩ := hhigh
  set b := max (M + 1) ε
  have hb : ε / 2 < b := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨z, hz, -, hfz⟩ := op_ivt_down hc (by linarith) hb (hl _ (by linarith) (by linarith))
    (hM b (lt_of_lt_of_le (by linarith) (le_max_left _ _)))
  exact ⟨z, by linarith, hfz⟩

/-- Miao, p. 549, the Diamond conditions, corrected: with `G′(0) > 1` (`G > id` near `0`), `G`
below the diagonal for large `k`, and `G′(k*) < 1` at every positive steady state, there is
exactly one positive steady state `k_D` (the Diamond steady state). -/
theorem op_diamond_conditions {G : ℝ → ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k) (hhigh : ∃ M, ∀ k, M < k → G k < k)
    (hslope : ∀ k, 0 < k → G k = k → ∃ d, HasDerivAt G d k ∧ d < 1) :
    ∃! k, 0 < k ∧ G k = k := by
  obtain ⟨k0, hk0, hfix0⟩ := op_exists_fixed hc hlow hhigh
  refine ⟨k0, ⟨hk0, hfix0⟩, ?_⟩
  have key : ∀ k1 k2, 0 < k1 → G k1 = k1 → k1 < k2 → G k2 = k2 → False := by
    intro k1 k2 hk1 hf1 h12 hf2
    obtain ⟨d1, hd1, hd11⟩ := hslope k1 hk1 hf1
    obtain ⟨δ, hδ, hloc⟩ := op_slope_lt_one hd1 hf1 hd11
    have hk2δ : k1 + δ ≤ k2 := by
      by_contra h
      push Not at h
      have := (hloc k2 (by linarith) h).1 h12
      linarith
    obtain ⟨c, hac, hcb, hfc, hleast⟩ :=
      op_least_fixed hc (a := k1 + δ / 2) (b := k2) (by linarith) (by linarith) hf2
    have hy1 : G (k1 + δ / 4) < k1 + δ / 4 := (hloc _ (by linarith) (by linarith)).1 (by linarith)
    obtain ⟨dc, hdc, hdc1⟩ := hslope c (by linarith) hfc
    obtain ⟨z, hz1, hz2, hz⟩ :=
      op_fixed_below hc (by linarith) (by linarith) hy1 hfc hdc hdc1
    by_cases hzδ : z < k1 + δ
    · have := (hloc z (by linarith) hzδ).1 (by linarith)
      linarith
    · exact hleast z (by push Not at hzδ; linarith) hz2 hz
  rintro k ⟨hk, hfk⟩
  rcases lt_trichotomy k k0 with h | h | h
  · exact (key k k0 hk hfk h hfix0).elim
  · exact h
  · exact (key k0 k hk0 hfix0 h hfk).elim

/-- **Correction to the Diamond conditions** (Miao, p. 549). As printed, condition (ii) is
`G′(0) < 1`, i.e. `G < id` near `0`. Together with (iii), `G′(k*) < 1` at every positive steady
state, this leaves NO positive steady state, so there is no Diamond steady state `k_D`; the
condition must be `G′(0) > 1` (`op_diamond_conditions`). -/
theorem op_diamond_conditions_printed {G : ℝ → ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → G k < k)
    (hslope : ∀ k, 0 < k → G k = k → ∃ d, HasDerivAt G d k ∧ d < 1) :
    ¬ ∃ k, 0 < k ∧ G k = k := by
  rintro ⟨k2, hk2, hf2⟩
  obtain ⟨ε, hε, hl⟩ := hlow
  set a := min (ε / 2) k2
  have ha : 0 < a := lt_min (by linarith) hk2
  have haε : a < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨c, hac, hcb, hfc, hleast⟩ := op_least_fixed hc ha (min_le_right _ _) hf2
  have hy1 : G (a / 2) < a / 2 := hl _ (by linarith) (by linarith)
  obtain ⟨dc, hdc, hdc1⟩ := hslope c (by linarith) hfc
  obtain ⟨z, hz1, hz2, hz⟩ := op_fixed_below hc (by linarith) (by linarith) hy1 hfc hdc hdc1
  by_cases hzε : z < ε
  · have := hl z (by linarith) hzε
    linarith
  · exact hleast z (by push Not at hzε; linarith) hz2 hz

/-- With a unique positive steady state `k*`, `G > id` near `0` and `G < id` for large `k`:
`G(k) > k` on `(0, k*)` and `G(k) < k` on `(k*, ∞)` (the configuration of Figure 16.10). -/
theorem op_fixed_signs {G : ℝ → ℝ} {kstar : ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hks : 0 < kstar) (hlow : ∃ ε > 0, ∀ k, 0 < k → k < ε → k < G k)
    (hhigh : ∃ M, ∀ k, M < k → G k < k) (huniq : ∀ k, 0 < k → G k = k → k = kstar) :
    (∀ k, 0 < k → k < kstar → k < G k) ∧ (∀ k, kstar < k → G k < k) := by
  obtain ⟨ε, hε, hl⟩ := hlow
  obtain ⟨M, hM⟩ := hhigh
  constructor
  · intro k hk hkk
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · set y := min (ε / 2) (k / 2)
      have hy : 0 < y := lt_min (by linarith) (by linarith)
      have hyk : y < k := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hyε : y < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      obtain ⟨z, hz1, hz2, hz⟩ := op_ivt_down hc hy hyk (hl y hy hyε) h
      have := huniq z (by linarith) hz
      linarith
    · have := huniq k hk h
      linarith
  · intro k hk
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · set b := max (M + 1) (k + 1)
      have hb : k < b := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      obtain ⟨z, hz1, hz2, hz⟩ := op_ivt_down hc (by linarith) hb h
        (hM b (lt_of_lt_of_le (by linarith) (le_max_left _ _)))
      have := huniq z (by linarith) hz
      linarith
    · have := huniq k (by linarith) h.symm
      linarith

/-- Miao, p. 549 and Figure 16.10: under the Diamond conditions the unique positive steady state
is globally stable: for increasing `G` with `G > id` on `(0, k*)` and `G < id` on `(k*, ∞)`,
`k_t → k*` from every `k₁ > 0`. -/
theorem op_global_convergence {G : ℝ → ℝ} {kstar k1 : ℝ} (hc : ContinuousOn G (Set.Ioi 0))
    (hmono : MonotoneOn G (Set.Ioi 0)) (hks : 0 < kstar) (hfix : G kstar = kstar)
    (hbelow : ∀ k, 0 < k → k < kstar → k < G k) (habove : ∀ k, kstar < k → G k < k)
    (hk1 : 0 < k1) : Tendsto (fun t => G^[t] k1) atTop (𝓝 kstar) := by
  set x : ℕ → ℝ := fun t => G^[t] k1 with hx
  have hxs : ∀ t, x (t + 1) = G (x t) := fun t => by
    simp only [hx]; rw [Function.iterate_succ_apply']
  have hlim : ∀ L, 0 < L → Tendsto x atTop (𝓝 L) → G L = L := by
    intro L hL hxL
    have h1 : Tendsto (fun t => G (x t)) atTop (𝓝 (G L)) :=
      ((hc.continuousAt (Ioi_mem_nhds hL)).tendsto).comp hxL
    have h2 : Tendsto (fun t => G (x t)) atTop (𝓝 L) := by
      have := hxL.comp (tendsto_add_atTop_nat 1)
      refine this.congr fun t => ?_
      simp only [Function.comp_apply, hxs]
    exact tendsto_nhds_unique h1 h2
  rcases le_or_gt k1 kstar with hle | hgt
  · have hb : ∀ t, 0 < x t ∧ x t ≤ kstar := by
      intro t
      induction t with
      | zero => exact ⟨hk1, hle⟩
      | succ t ih =>
        rw [hxs]
        rcases ih.2.lt_or_eq with h | h
        · exact ⟨lt_trans ih.1 (hbelow _ ih.1 h), by
            have := hmono ih.1 (show kstar ∈ Set.Ioi 0 from hks) ih.2; rwa [hfix] at this⟩
        · rw [h, hfix]; exact ⟨hks, le_rfl⟩
    have hm : Monotone x := by
      refine monotone_nat_of_le_succ fun t => ?_
      rw [hxs]
      rcases (hb t).2.lt_or_eq with h | h
      · exact (hbelow _ (hb t).1 h).le
      · rw [h, hfix]
    have hbdd : BddAbove (Set.range x) := ⟨kstar, by rintro _ ⟨t, rfl⟩; exact (hb t).2⟩
    have hT := tendsto_atTop_ciSup hm hbdd
    set L := ⨆ t, x t
    have hL0 : 0 < L := lt_of_lt_of_le (hb 0).1 (le_ciSup hbdd 0)
    have hLk : L ≤ kstar := ciSup_le fun t => (hb t).2
    have hGL := hlim L hL0 hT
    rcases hLk.lt_or_eq with h | h
    · have := hbelow L hL0 h; linarith
    · rwa [h] at hT
  · have hb : ∀ t, kstar ≤ x t := by
      intro t
      induction t with
      | zero => exact hgt.le
      | succ t ih =>
        rw [hxs]
        have := hmono (show kstar ∈ Set.Ioi 0 from hks)
          (show x t ∈ Set.Ioi 0 from lt_of_lt_of_le hks ih) ih
        rwa [hfix] at this
    have hm : Antitone x := by
      refine antitone_nat_of_succ_le fun t => ?_
      rw [hxs]
      rcases (hb t).lt_or_eq with h | h
      · exact (habove _ h).le
      · rw [← h, hfix]
    have hbdd : BddBelow (Set.range x) := ⟨kstar, by rintro _ ⟨t, rfl⟩; exact hb t⟩
    have hT := tendsto_atTop_ciInf hm hbdd
    set L := ⨅ t, x t
    have hLk : kstar ≤ L := le_ciInf hb
    have hGL := hlim L (lt_of_lt_of_le hks hLk) hT
    rcases hLk.lt_or_eq with h | h
    · have := habove L h; linarith
    · rwa [← h] at hT

/-- Miao, p. 549: "the condition for the stability of a positive steady state is `G′(k*) < 1`".
A steady state with `|G′(k*)| < 1` is locally asymptotically stable (for increasing `G`,
`G′ ≥ 0`, so this is `G′(k*) < 1`). -/
theorem op_local_stability {G : ℝ → ℝ} {c d : ℝ} (hd : HasDerivAt G d c) (hfix : G c = c)
    (hd1 : |d| < 1) :
    ∃ δ > 0, ∀ k1, |k1 - c| < δ → Tendsto (fun t => G^[t] k1) atTop (𝓝 c) := by
  set q := (|d| + 1) / 2 with hq
  have hq0 : 0 < q := by have := abs_nonneg d; rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hdq : |d| < q := by rw [hq]; linarith
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  have hev : ∀ᶠ z in 𝓝[≠] c, |slope G c z| < q := by
    have hb : ∀ᶠ z in 𝓝 d, |z| < q := by
      filter_upwards [Metric.ball_mem_nhds d (show 0 < q - |d| by linarith)] with z hz
      rw [Metric.mem_ball, Real.dist_eq] at hz
      have := abs_sub_abs_le_abs_sub z d
      linarith
    exact h.eventually hb
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  have hcontr : ∀ y, |y - c| < δ → |G y - c| ≤ q * |y - c| := by
    intro y hy
    by_cases hyc : y = c
    · rw [hyc, hfix]; simp
    · have := hball (by rwa [Real.dist_eq]) hyc
      rw [slope_def_field, hfix, abs_div, div_lt_iff₀ (abs_pos.2 (sub_ne_zero.2 hyc))] at this
      linarith
  refine ⟨δ, hδ, fun k1 hk1 => ?_⟩
  have hbound : ∀ t, |G^[t] k1 - c| ≤ q ^ t * |k1 - c| := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      have hlt : |G^[t] k1 - c| < δ := by
        have : q ^ t ≤ 1 := pow_le_one₀ hq0.le hq1.le
        have : q ^ t * |k1 - c| ≤ |k1 - c| := by
          have := abs_nonneg (k1 - c); nlinarith
        linarith
      calc |G (G^[t] k1) - c| ≤ q * |G^[t] k1 - c| := hcontr _ hlt
        _ ≤ q * (q ^ t * |k1 - c|) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = q ^ (t + 1) * |k1 - c| := by ring
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).mul_const |k1 - c|
  rw [zero_mul] at hz
  exact squeeze_zero (fun t => abs_nonneg _) hbound hz

/-! ### The number of steady states: counterexamples to "odd" and "even" -/

/-- A continuous, strictly increasing map with `G(0) = 0`, `G′(0) = 2 > 1` and `G(k)/k → 0`:
`G(k) = max(min(2k, 2 + √k), min(2k − 9, 3√k))`. -/
noncomputable def opOddG (k : ℝ) : ℝ :=
  max (min (2 * k) (2 + Real.sqrt k)) (min (2 * k - 9) (3 * Real.sqrt k))

/-- The analogue with `G′(0) = 1/2 < 1`: `G(k) = max(min(k/2, √k), min(2k − 9, 3√k))`. -/
noncomputable def opEvenG (k : ℝ) : ℝ :=
  max (min (k / 2) (Real.sqrt k)) (min (2 * k - 9) (3 * Real.sqrt k))

/-- `max` of strictly increasing functions is strictly increasing. -/
theorem op_strictMonoOn_max {f g : ℝ → ℝ} {S : Set ℝ} (hf : StrictMonoOn f S)
    (hg : StrictMonoOn g S) : StrictMonoOn (fun x => max (f x) (g x)) S :=
  fun _ ha _ hb hab => max_lt (lt_max_of_lt_left (hf ha hb hab))
    (lt_max_of_lt_right (hg ha hb hab))

/-- `min` of strictly increasing functions is strictly increasing. -/
theorem op_strictMonoOn_min {f g : ℝ → ℝ} {S : Set ℝ} (hf : StrictMonoOn f S)
    (hg : StrictMonoOn g S) : StrictMonoOn (fun x => min (f x) (g x)) S :=
  fun _ ha _ hb hab => lt_min (lt_of_le_of_lt (min_le_left _ _) (hf ha hb hab))
    (lt_of_le_of_lt (min_le_right _ _) (hg ha hb hab))

/-- `√` is strictly increasing on `[0, ∞)`. -/
theorem op_sqrt_strictMonoOn : StrictMonoOn Real.sqrt (Set.Ici 0) :=
  fun _ ha _ _ hab => Real.sqrt_lt_sqrt ha hab

/-- `3√k/k → 0`. -/
theorem op_three_sqrt_div_tendsto : Tendsto (fun k => 3 * Real.sqrt k / k) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul 3
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hs := Real.sqrt_pos.2 hk
  have hss := Real.mul_self_sqrt hk.le
  simp only [Function.comp_apply]
  field_simp
  linarith

theorem op_sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem op_sqrt_nine : Real.sqrt 9 = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The properties of `opOddG` listed by the text: continuous, strictly increasing on
`[0, ∞)`, `G(0) = 0`, `G(k) = 2k` on `(0, 1]` (so `G′(0) = 2 > 1`), `G(k)/k → 0`. -/
theorem op_oddG_props : Continuous opOddG ∧ StrictMonoOn opOddG (Set.Ici 0) ∧ opOddG 0 = 0 ∧
    (∀ k, 0 < k → k ≤ 1 → opOddG k = 2 * k) ∧
    HasDerivWithinAt opOddG 2 (Set.Ioi 0) 0 ∧
    Tendsto (fun k => opOddG k / k) atTop (𝓝 0) := by
  have hsmall : ∀ k, 0 < k → k ≤ 1 → opOddG k = 2 * k := by
    intro k hk hk1
    have hs := Real.sqrt_nonneg k
    unfold opOddG
    rw [min_eq_left (by linarith), max_eq_left (le_trans (min_le_left _ _) (by linarith))]
  refine ⟨?_, ?_, ?_, hsmall, ?_, ?_⟩
  · unfold opOddG; fun_prop
  · have h1 : StrictMonoOn (fun k : ℝ => 2 * k) (Set.Ici 0) := fun _ _ _ _ h => by linarith
    have h2 : StrictMonoOn (fun k => 2 + Real.sqrt k) (Set.Ici 0) := fun _ ha _ hb h => by
      have := op_sqrt_strictMonoOn ha hb h; simp only; linarith
    have h3 : StrictMonoOn (fun k : ℝ => 2 * k - 9) (Set.Ici 0) := fun _ _ _ _ h => by linarith
    have h4 : StrictMonoOn (fun k => 3 * Real.sqrt k) (Set.Ici 0) := fun _ ha _ hb h => by
      have := op_sqrt_strictMonoOn ha hb h; simp only; linarith
    exact op_strictMonoOn_max (op_strictMonoOn_min h1 h2) (op_strictMonoOn_min h3 h4)
  · unfold opOddG; norm_num
  · have hd : HasDerivWithinAt (fun k : ℝ => 2 * k) 2 (Set.Ioi 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).hasDerivWithinAt
    refine hd.congr_of_eventuallyEq ?_ (by unfold opOddG; norm_num)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact hsmall k hk.1 hk.2.le
  · refine op_three_sqrt_div_tendsto.congr' ?_
    filter_upwards [eventually_ge_atTop 9] with k hk
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt (show (0 : ℝ) ≤ k by linarith)
    have hs3 : 3 ≤ Real.sqrt k := by rw [← op_sqrt_nine]; exact Real.sqrt_le_sqrt hk
    unfold opOddG
    rw [min_eq_right (show 3 * Real.sqrt k ≤ 2 * k - 9 by nlinarith),
      max_eq_right (le_trans (min_le_right _ _) (by linarith))]

/-- The positive steady states of `opOddG` are exactly `4` and `9`. -/
theorem op_oddG_fixed : {k : ℝ | 0 < k ∧ opOddG k = k} = {4, 9} := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hk, hG⟩
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt hk.le
    set t := Real.sqrt k
    unfold opOddG at hG
    rcases le_total (min (2 * k) (2 + t)) (min (2 * k - 9) (3 * t)) with hm | hm
    · rw [max_eq_right hm] at hG
      rcases le_total (2 * k - 9) (3 * t) with hn | hn
      · rw [min_eq_left hn] at hG; right; linarith
      · rw [min_eq_right hn] at hG
        have : t * (t - 3) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · rw [h] at hss; linarith
        · right; have : t = 3 := by linarith
          rw [this] at hss; linarith
    · rw [max_eq_left hm] at hG
      rcases le_total (2 * k) (2 + t) with hn | hn
      · rw [min_eq_left hn] at hG; linarith
      · rw [min_eq_right hn] at hG
        have : (t - 2) * (t + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; have : t = 2 := by linarith
          rw [this] at hss; linarith
        · linarith
  · rintro (rfl | rfl)
    · refine ⟨by norm_num, ?_⟩
      unfold opOddG; rw [op_sqrt_four]; norm_num
    · refine ⟨by norm_num, ?_⟩
      unfold opOddG; rw [op_sqrt_nine]; norm_num

/-- **Correction** (Miao, p. 547): "If `G′(0) > 1`, then an odd number of positive steady states
exist" is false. `opOddG` has every property the text derives for `G` (`op_oddG_props`) and
`G′(0) = 2`, but exactly two positive steady states. -/
theorem op_odd_counterexample :
    Set.ncard {k : ℝ | 0 < k ∧ opOddG k = k} = 2 ∧
      ¬ Odd (Set.ncard {k : ℝ | 0 < k ∧ opOddG k = k}) := by
  rw [op_oddG_fixed, Set.ncard_pair (by norm_num)]
  exact ⟨rfl, by decide⟩

/-- The properties of `opEvenG`: continuous, strictly increasing on `[0, ∞)`, `G(0) = 0`,
`G(k) = k/2` on `(0, 1]` (so `G′(0) = 1/2 < 1`), `G(k)/k → 0`. -/
theorem op_evenG_props : Continuous opEvenG ∧ StrictMonoOn opEvenG (Set.Ici 0) ∧
    opEvenG 0 = 0 ∧ (∀ k, 0 < k → k ≤ 1 → opEvenG k = k / 2) ∧
    HasDerivWithinAt opEvenG (1 / 2) (Set.Ioi 0) 0 ∧
    Tendsto (fun k => opEvenG k / k) atTop (𝓝 0) := by
  have hsmall : ∀ k, 0 < k → k ≤ 1 → opEvenG k = k / 2 := by
    intro k hk hk1
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt hk.le
    have hsk : k / 2 ≤ Real.sqrt k := by nlinarith
    unfold opEvenG
    rw [min_eq_left hsk, max_eq_left (le_trans (min_le_left _ _) (by linarith))]
  refine ⟨?_, ?_, ?_, hsmall, ?_, ?_⟩
  · unfold opEvenG; fun_prop
  · have h1 : StrictMonoOn (fun k : ℝ => k / 2) (Set.Ici 0) := fun _ _ _ _ h => by
      simp only; linarith
    have h3 : StrictMonoOn (fun k : ℝ => 2 * k - 9) (Set.Ici 0) := fun _ _ _ _ h => by linarith
    have h4 : StrictMonoOn (fun k => 3 * Real.sqrt k) (Set.Ici 0) := fun _ ha _ hb h => by
      have := op_sqrt_strictMonoOn ha hb h; simp only; linarith
    exact op_strictMonoOn_max (op_strictMonoOn_min h1 op_sqrt_strictMonoOn)
      (op_strictMonoOn_min h3 h4)
  · unfold opEvenG; norm_num
  · have hd : HasDerivWithinAt (fun k : ℝ => k / 2) (1 / 2) (Set.Ioi 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).hasDerivWithinAt
    refine hd.congr_of_eventuallyEq ?_ (by unfold opEvenG; norm_num)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with k hk
    exact hsmall k hk.1 hk.2.le
  · refine op_three_sqrt_div_tendsto.congr' ?_
    filter_upwards [eventually_ge_atTop 9] with k hk
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt (show (0 : ℝ) ≤ k by linarith)
    have hs3 : 3 ≤ Real.sqrt k := by rw [← op_sqrt_nine]; exact Real.sqrt_le_sqrt hk
    unfold opEvenG
    rw [min_eq_right (show 3 * Real.sqrt k ≤ 2 * k - 9 by nlinarith),
      max_eq_right (le_trans (min_le_right _ _) (by linarith))]

/-- The only positive steady state of `opEvenG` is `9`. -/
theorem op_evenG_fixed : {k : ℝ | 0 < k ∧ opEvenG k = k} = {9} := by
  ext k
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hk, hG⟩
    have hs := Real.sqrt_nonneg k
    have hss := Real.mul_self_sqrt hk.le
    set t := Real.sqrt k
    unfold opEvenG at hG
    rcases le_total (min (k / 2) t) (min (2 * k - 9) (3 * t)) with hm | hm
    · rw [max_eq_right hm] at hG
      rcases le_total (2 * k - 9) (3 * t) with hn | hn
      · rw [min_eq_left hn] at hG; linarith
      · rw [min_eq_right hn] at hG
        have : t * (t - 3) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · rw [h] at hss; linarith
        · have : t = 3 := by linarith
          rw [this] at hss; linarith
    · rw [max_eq_left hm] at hG
      rcases le_total (k / 2) t with hn | hn
      · rw [min_eq_left hn] at hG; linarith
      · rw [min_eq_right hn] at hG
        nlinarith
  · rintro rfl
    refine ⟨by norm_num, ?_⟩
    unfold opEvenG; rw [op_sqrt_nine]; norm_num

/-- **Correction** (Miao, p. 547): "If `G′(0) < 1`, then an even number of positive steady states
exist" is false. `opEvenG` has the listed properties and `G′(0) = 1/2`, but exactly one positive
steady state (a tangency at `k = 9`). -/
theorem op_even_counterexample :
    Set.ncard {k : ℝ | 0 < k ∧ opEvenG k = k} = 1 ∧
      ¬ Even (Set.ncard {k : ℝ | 0 < k ∧ opEvenG k = k}) := by
  rw [op_evenG_fixed, Set.ncard_singleton]
  exact ⟨rfl, by decide⟩

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamic efficiency in the Diamond model

Miao, §16.2, pp. 549–551.

* The aggregate resource constraint per worker, `k_t + f(k_t) = g_nk_{t+1} + c_t^t + g_n⁻¹c_t^{t−1}`
  (`op_resource_per_worker`), and in a steady state (16.17)
  `c_y + g_n⁻¹c_o = f(k) − (g_n − 1)k` (`eq_16_17`).
* The golden rule `f′(k_G) = g_n − 1` maximises steady-state consumption per worker
  (`op_golden_rule_max`, strictly: `op_golden_rule_strict`); `k_G` exists and is unique
  (`op_golden_rule_exists`, `op_golden_rule_unique`).
* The planner's steady-state problem: the partial derivatives of the Lagrangian
  (`op_planner_lagrangian`) and the first-order conditions (`op_planner_foc`); with `λ₀ = 0`,
  `θ = 0` and the golden rule (`op_planner_golden_rule`). **Correction:** the printed conditions
  `u′(c_y)/(βu′(c_o)) = g_n` and `f′(k) = g_n − 1 + θ/µ` hold only for `θ = 0`; in general
  `u′(c_y)/(βu′(c_o)) = g_n(1 + θ/µ)` and `f′(k) = g_n − 1 + g_nθ/µ`
  (`op_planner_foc_printed`). The conclusion `f′(k) ≥ g_n − 1` stands.
* Dynamic inefficiency: a steady state with `k* > k_G` is Pareto dominated: lowering capital to
  `k_G` makes every generation strictly better off and leaves the initial old as well off
  (`OPFeasible`, `OPParetoDominates`, `op_dynamic_inefficiency`).
* A competitive steady state with `k* < k_G` (`f′(k*) > g_n − 1`) is Pareto optimal
  (`op_pareto_optimal_of_lt_golden`), by a present-value argument at the prices `(g_n/R)ᵗ`.
* The Cass–Balasko–Shell criterion at a steady state: `Σ g_n⁻ᵗ ∏_{s ≤ t} R_{s+1} = ∞` iff
  `R ≥ g_n` iff `k* ≤ k_G` (`op_cass_steady_state`, `op_cass_corollary`).

Not formalised: the general Cass (1972) / Balasko–Shell (1980) theorem (cited, not proved, in
the text), and Pareto optimality of the golden-rule steady state `k* = k_G` itself.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, p. 550: dividing the aggregate resource constraint
`K_t + F(K_t, N_t) = K_{t+1} + N_tc_t^t + N_{t−1}c_t^{t−1}` (with `F(K, N) = Nf(K/N)`) by `N_t`
gives `k_t + f(k_t) = g_nk_{t+1} + c_t^t + g_n⁻¹c_t^{t−1}`. -/
theorem op_resource_per_worker {f : ℝ → ℝ} {K K' N Nm N' gn cy co : ℝ} (hgn : 0 < gn)
    (hNm : 0 < Nm) (hN : N = gn * Nm) (hN' : N' = gn * N)
    (h : K + N * f (K / N) = K' + N * cy + Nm * co) :
    K / N + f (K / N) = gn * (K' / N') + cy + co / gn := by
  have hN0 : 0 < N := by rw [hN]; positivity
  rw [hN'] at *
  rw [hN] at h hN0 ⊢
  field_simp
  field_simp at h
  linarith

/-- Miao, (16.17), p. 550: in a steady state the resource constraint is
`c_y + g_n⁻¹c_o = f(k) − (g_n − 1)k`. -/
theorem eq_16_17 {f : ℝ → ℝ} {gn k cy co : ℝ} :
    k + f k = gn * k + cy + co / gn ↔ cy + co / gn = f k - (gn - 1) * k := by
  constructor <;> intro h <;> linarith

/-- Miao, p. 551: the golden rule `f′(k_G) = g_n − 1` maximises steady-state consumption per
worker `f(k) − (g_n − 1)k`. -/
theorem op_golden_rule_max {f : ℝ → ℝ} {gn kG : ℝ} (hconc : ConcaveOn ℝ (Set.Ici 0) f)
    (hkG : 0 ≤ kG) (hfG : HasDerivAt f (gn - 1) kG) {k : ℝ} (hk : 0 ≤ k) :
    f k - (gn - 1) * k ≤ f kG - (gn - 1) * kG := by
  have := op_concave_tangent hconc (Set.mem_Ici.2 hkG) (Set.mem_Ici.2 hk) hfG
  linarith

/-- The golden rule is the unique maximiser for strictly concave `f`. -/
theorem op_golden_rule_strict {f : ℝ → ℝ} {gn kG : ℝ} (hconc : StrictConcaveOn ℝ (Set.Ici 0) f)
    (hkG : 0 ≤ kG) (hfG : HasDerivAt f (gn - 1) kG) {k : ℝ} (hk : 0 ≤ k) (hne : k ≠ kG) :
    f k - (gn - 1) * k < f kG - (gn - 1) * kG := by
  have := op_strictConcave_tangent hconc (Set.mem_Ici.2 hkG) (Set.mem_Ici.2 hk) hne hfG
  linarith

/-- The golden rule capital stock is unique (`f′` strictly decreasing). -/
theorem op_golden_rule_unique {fp : ℝ → ℝ} {gn k1 k2 : ℝ} (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hk1 : 0 < k1) (hk2 : 0 < k2) (h1 : fp k1 = gn - 1) (h2 : fp k2 = gn - 1) : k1 = k2 :=
  hanti.injOn hk1 hk2 (by rw [h1, h2])

/-- The golden rule exists when `g_n > 1`, `f′` is continuous, `f′(0+) = ∞` and `f′(∞) = 0`. -/
theorem op_golden_rule_exists {fp : ℝ → ℝ} {gn : ℝ} (hgn : 1 < gn)
    (hfpc : ContinuousOn fp (Set.Ioi 0)) (hinada : Tendsto fp (𝓝[>] 0) atTop)
    (hinf : Tendsto fp atTop (𝓝 0)) : ∃ kG, 0 < kG ∧ fp kG = gn - 1 := by
  obtain ⟨ε, hε, hl⟩ := op_inada_small hinada (gn - 1)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hinf.eventually (eventually_lt_nhds
    (show (0 : ℝ) < gn - 1 by linarith)))
  set a := ε / 2 with ha_def
  set b := max M (a + 1)
  have hab : a ≤ b := le_trans (by linarith) (le_max_right _ _)
  have ha : 0 < a := by positivity
  obtain ⟨k, hk, hfk⟩ := intermediate_value_Icc' hab
    (hfpc.mono fun x hx => lt_of_lt_of_le ha hx.1)
    ⟨(hM b (le_max_left _ _)).le, (hl a ha (by linarith)).le⟩
  exact ⟨k, lt_of_lt_of_le ha hk.1, hfk⟩

/-! ### The planner's steady-state problem -/

/-- Miao, pp. 550–551: the Lagrangian of the planner's steady-state problem,
`λ₀u(c₁⁰) + λ₁[u(c_y) + βu(c_o)] + µ[f(k) − (g_n − 1)k − c_y − g_n⁻¹c_o]
 + θ[f(k₁) + k₁ − g_nk − c_y − g_n⁻¹c₁⁰]`. -/
noncomputable def opLagrangian (u f : ℝ → ℝ) (lam0 lam1 β gn μ θ k1 cy co c01 k : ℝ) : ℝ :=
  lam0 * u c01 + lam1 * (u cy + β * u co) + μ * (f k - (gn - 1) * k - cy - co / gn) +
    θ * (f k1 + k1 - gn * k - cy - c01 / gn)

/-- The partial derivatives of the planner's Lagrangian in `c_y`, `c_o`, `c₁⁰` and `k`. -/
theorem op_planner_lagrangian {u up f fp : ℝ → ℝ} {lam0 lam1 β gn μ θ k1 cy co c01 k : ℝ}
    (hcy : HasDerivAt u (up cy) cy) (hco : HasDerivAt u (up co) co)
    (hc01 : HasDerivAt u (up c01) c01) (hk : HasDerivAt f (fp k) k) :
    HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 x co c01 k)
        (lam1 * up cy - μ - θ) cy ∧
      HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 cy x c01 k)
        (lam1 * β * up co - μ / gn) co ∧
      HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 cy co x k)
        (lam0 * up c01 - θ / gn) c01 ∧
      HasDerivAt (fun x => opLagrangian u f lam0 lam1 β gn μ θ k1 cy co c01 x)
        (μ * (fp k - (gn - 1)) - θ * gn) k := by
  unfold opLagrangian
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((((hcy.add_const (β * u co)).const_mul lam1).const_add (lam0 * u c01)).add
      ((((hasDerivAt_id' cy).const_sub (f k - (gn - 1) * k)).sub_const (co / gn)).const_mul
        μ)).add ((((hasDerivAt_id' cy).const_sub (f k1 + k1 - gn * k)).sub_const
        (c01 / gn)).const_mul θ)
    convert h using 1
    ring
  · have h := (((((hco.const_mul β).const_add (u cy)).const_mul lam1).const_add
      (lam0 * u c01)).add ((((hasDerivAt_id' co).div_const gn).const_sub
        (f k - (gn - 1) * k - cy)).const_mul μ)).add_const
      (θ * (f k1 + k1 - gn * k - cy - c01 / gn))
    convert h using 1
    ring
  · have h := (((hc01.const_mul lam0).add_const (lam1 * (u cy + β * u co))).add
      ((((hasDerivAt_id' c01).div_const gn).const_sub (f k1 + k1 - gn * k - cy)).const_mul
        θ)).add_const (μ * (f k - (gn - 1) * k - cy - co / gn))
    convert h using 1
    · ext x; simp only [Pi.add_apply]; ring
    · ring
  · have h := ((((hk.sub ((hasDerivAt_id' k).const_mul (gn - 1))).sub_const
      (cy + co / gn)).const_mul μ).add (((((hasDerivAt_id' k).const_mul gn).const_sub
        (f k1 + k1)).sub_const (cy + c01 / gn)).const_mul θ)).const_add
      (lam0 * u c01 + lam1 * (u cy + β * u co))
    convert h using 1
    · ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · ring

/-- Miao, p. 551: the first-order conditions of the planner's problem. From the stationarity
of the Lagrangian with `µ > 0`, `θ ≥ 0`: `u′(c_y)/(βu′(c_o)) = g_n(1 + θ/µ)`,
`λ₀u′(c₁⁰) = θ/g_n`, and `f′(k) = g_n − 1 + g_nθ/µ ≥ g_n − 1`. -/
theorem op_planner_foc {up : ℝ → ℝ} {lam0 lam1 β gn μ θ cy co c01 fpk : ℝ} (hgn : 0 < gn)
    (hβ : 0 < β) (hμ : 0 < μ) (hθ : 0 ≤ θ) (hup : 0 < up co)
    (h1 : lam1 * up cy - μ - θ = 0) (h2 : lam1 * β * up co - μ / gn = 0)
    (h3 : lam0 * up c01 - θ / gn = 0) (h4 : μ * (fpk - (gn - 1)) - θ * gn = 0) :
    up cy / (β * up co) = gn * (1 + θ / μ) ∧ lam0 * up c01 = θ / gn ∧
      fpk = gn - 1 + gn * θ / μ ∧ gn - 1 ≤ fpk := by
  have hlam1 : lam1 * (β * up co) = μ / gn := by linarith
  have hlam1pos : 0 < lam1 := by
    by_contra h
    push Not at h
    have : lam1 * (β * up co) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    have : 0 < μ / gn := div_pos hμ hgn
    linarith
  have hfpk : fpk = gn - 1 + gn * θ / μ := by
    field_simp
    linarith
  refine ⟨?_, by linarith, hfpk, ?_⟩
  · rw [div_eq_iff (by positivity)]
    have hcy : lam1 * up cy = μ + θ := by linarith
    have : lam1 * (up cy - gn * (1 + θ / μ) * (β * up co)) = 0 := by
      have e : lam1 * (gn * (1 + θ / μ) * (β * up co)) = gn * (1 + θ / μ) * (μ / gn) := by
        rw [← hlam1]; ring
      have e2 : gn * (1 + θ / μ) * (μ / gn) = μ + θ := by field_simp
      linarith [mul_sub lam1 (up cy) (gn * (1 + θ / μ) * (β * up co))]
    have := (mul_eq_zero.1 this).resolve_left hlam1pos.ne'
    linarith
  · rw [hfpk]
    have : 0 ≤ gn * θ / μ := by positivity
    linarith

/-- Miao, p. 551: "When the planner does not consider the initial old, `λ₀ = 0`, so that
`θ = 0`": then `u′(c_y)/(βu′(c_o)) = g_n` and `f′(k) = g_n − 1`, the golden rule. -/
theorem op_planner_golden_rule {up : ℝ → ℝ} {lam1 β gn μ θ cy co c01 fpk : ℝ} (hgn : 0 < gn)
    (hβ : 0 < β) (hμ : 0 < μ) (hθ : 0 ≤ θ) (hup : 0 < up co)
    (h1 : lam1 * up cy - μ - θ = 0) (h2 : lam1 * β * up co - μ / gn = 0)
    (h3 : 0 * up c01 - θ / gn = 0) (h4 : μ * (fpk - (gn - 1)) - θ * gn = 0) :
    θ = 0 ∧ up cy / (β * up co) = gn ∧ fpk = gn - 1 := by
  obtain ⟨ha, -, hc, -⟩ := op_planner_foc hgn hβ hμ hθ hup h1 h2 h3 h4
  have hθ0 : θ = 0 := by
    have : θ / gn = 0 := by linarith
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h hgn.ne'
  rw [hθ0] at ha hc
  refine ⟨hθ0, by simpa using ha, by simpa using hc⟩

/-- **Correction** (Miao, p. 551): with `θ > 0` the printed first-order conditions fail:
`u′(c_y)/(βu′(c_o)) ≠ g_n`, and `f′(k) ≠ g_n − 1 + θ/µ` unless `g_n = 1`. -/
theorem op_planner_foc_printed {up : ℝ → ℝ} {lam0 lam1 β gn μ θ cy co c01 fpk : ℝ}
    (hgn : 0 < gn) (hβ : 0 < β) (hμ : 0 < μ) (hθ : 0 < θ) (hup : 0 < up co)
    (h1 : lam1 * up cy - μ - θ = 0) (h2 : lam1 * β * up co - μ / gn = 0)
    (h3 : lam0 * up c01 - θ / gn = 0) (h4 : μ * (fpk - (gn - 1)) - θ * gn = 0) :
    up cy / (β * up co) ≠ gn ∧ (gn ≠ 1 → fpk ≠ gn - 1 + θ / μ) := by
  obtain ⟨ha, -, hc, -⟩ := op_planner_foc hgn hβ hμ hθ.le hup h1 h2 h3 h4
  have hθμ : 0 < θ / μ := div_pos hθ hμ
  refine ⟨fun h => ?_, fun hg h => ?_⟩
  · rw [ha] at h
    have : gn * (θ / μ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · rw [hc] at h
    have : (gn - 1) * (θ / μ) = 0 := by
      have e : gn * θ / μ = gn * (θ / μ) := by ring
      linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact hg (by linarith)
    · linarith

/-! ### Feasible allocations and Pareto dominance -/

/-- A feasible allocation (Miao, p. 550), indexed from the book's `t = 1` as `t = 0`: capital
`k_t ≥ 0`, consumption of the young `y_t > 0` and of the old `o_t > 0` (`o₀ = c₁⁰`, the
initial old), with `k_t + f(k_t) = g_nk_{t+1} + y_t + o_t/g_n`. -/
def OPFeasible (f : ℝ → ℝ) (gn : ℝ) (k y o : ℕ → ℝ) : Prop :=
  ∀ t, 0 ≤ k t ∧ 0 < y t ∧ 0 < o t ∧ k t + f (k t) = gn * k (t + 1) + y t + o t / gn

/-- The allocation `(k, y, o)` starting from `k₀ = k*` Pareto dominates the steady state
`(k*, c_y, c_o)`: the initial old and every generation `t` (utility `u(y_t) + βu(o_{t+1})`) are
at least as well off, and someone is strictly better off. -/
def OPParetoDominates (u : ℝ → ℝ) (β : ℝ) (f : ℝ → ℝ) (gn kstar cy co : ℝ)
    (k y o : ℕ → ℝ) : Prop :=
  OPFeasible f gn k y o ∧ k 0 = kstar ∧ u co ≤ u (o 0) ∧
    (∀ t, u cy + β * u co ≤ u (y t) + β * u (o (t + 1))) ∧
    (u co < u (o 0) ∨ ∃ t, u cy + β * u co < u (y t) + β * u (o (t + 1)))

/-- The steady-state allocation is feasible. -/
theorem op_steady_feasible {f : ℝ → ℝ} {gn kstar cy co : ℝ} (hks : 0 ≤ kstar) (hcy : 0 < cy)
    (hco : 0 < co) (hss : kstar + f kstar = gn * kstar + cy + co / gn) :
    OPFeasible f gn (fun _ => kstar) (fun _ => cy) (fun _ => co) :=
  fun _ => ⟨hks, hcy, hco, hss⟩

/-- Miao, p. 551: "When the marginal product of capital is smaller than the population growth
rate, the economy accumulates too much capital `k* > k_G` and hence it is dynamically
inefficient. A planner can reduce saving from `k*` to `k_G` and makes everyone better off."
The allocation `k₀ = k*`, `k_t = k_G` (`t ≥ 1`), `y₀ = c_y + g_n(k* − k_G)`,
`y_t = c_y + Δ` with `Δ = [f(k_G) − (g_n − 1)k_G] − [f(k*) − (g_n − 1)k*] > 0`, `o_t = c_o`
Pareto dominates the steady state: every generation is strictly better off. -/
theorem op_dynamic_inefficiency {u f : ℝ → ℝ} {β gn kstar kG cy co : ℝ} (hgn : 0 < gn)
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hkG : 0 ≤ kG) (hfG : HasDerivAt f (gn - 1) kG)
    (hks : kG < kstar) (hcy : 0 < cy) (hco : 0 < co)
    (hss : kstar + f kstar = gn * kstar + cy + co / gn) (hu : StrictMonoOn u (Set.Ioi 0)) :
    ∃ k y o : ℕ → ℝ, OPParetoDominates u β f gn kstar cy co k y o ∧
      ∀ t, cy < y t ∧ o t = co := by
  set Δ := (f kG - (gn - 1) * kG) - (f kstar - (gn - 1) * kstar) with hΔ
  have hΔpos : 0 < Δ := by
    have := op_golden_rule_strict hconc hkG hfG (by linarith : (0 : ℝ) ≤ kstar) hks.ne'
    rw [hΔ]; linarith
  set k : ℕ → ℝ := fun t => if t = 0 then kstar else kG
  set y : ℕ → ℝ := fun t => if t = 0 then cy + gn * (kstar - kG) else cy + Δ
  set o : ℕ → ℝ := fun _ => co
  have hy : ∀ t, cy < y t := by
    intro t
    rcases t with _ | t
    · simp only [y, ↓reduceIte]; nlinarith
    · simp only [y, Nat.add_one_ne_zero, ↓reduceIte]; linarith
  have hgain : ∀ t, u cy + β * u co < u (y t) + β * u (o (t + 1)) := by
    intro t
    have := hu (show cy ∈ Set.Ioi 0 from hcy) (show y t ∈ Set.Ioi 0 from
      lt_trans hcy (hy t)) (hy t)
    simp only [o]
    linarith
  refine ⟨k, y, o, ⟨?_, by simp [k], le_rfl, fun t => (hgain t).le, Or.inr ⟨0, hgain 0⟩⟩,
    fun t => ⟨hy t, rfl⟩⟩
  intro t
  refine ⟨?_, lt_trans hcy (hy t), hco, ?_⟩
  · rcases t with _ | t
    · simp only [k, ↓reduceIte]; linarith
    · simp only [k, Nat.add_one_ne_zero, ↓reduceIte]; exact hkG
  · rcases t with _ | t
    · simp only [k, y, o, ↓reduceIte, zero_add, one_ne_zero]
      linarith
    · simp only [k, y, o, Nat.add_one_ne_zero, ↓reduceIte]
      rw [hΔ]
      linarith

/-- Miao, p. 551 (the efficient half of the steady-state corollary): a competitive steady state
with `f′(k*) > g_n − 1` (`k* < k_G`) is Pareto optimal. Here `c_y, c_o` satisfy the Euler
equation `u′(c_y) = βRu′(c_o)`, `R = 1 + f′(k*)`, with `u` concave and strictly increasing and
`f` concave. No feasible allocation from `k₀ = k*` Pareto dominates it. -/
theorem op_pareto_optimal_of_lt_golden {u up f : ℝ → ℝ} {β gn kstar cy co fps : ℝ}
    (hgn : 0 < gn) (hβ : 0 < β) (huc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hum : StrictMonoOn u (Set.Ioi 0)) (hucy : HasDerivAt u (up cy) cy)
    (huco : HasDerivAt u (up co) co) (hupco : 0 < up co)
    (heul : up cy = β * (1 + fps) * up co) (hfc : ConcaveOn ℝ (Set.Ici 0) f)
    (hks : 0 < kstar) (hfd : HasDerivAt f fps kstar) (heff : gn - 1 < fps) (hcy : 0 < cy)
    (hco : 0 < co) (hss : kstar + f kstar = gn * kstar + cy + co / gn) :
    ¬ ∃ k y o : ℕ → ℝ, OPParetoDominates u β f gn kstar cy co k y o := by
  rintro ⟨k, y, o, hfeas, hk0, hold, hgen, hstrict⟩
  set R := 1 + fps with hR
  have hRgn : gn < R := by rw [hR]; linarith
  have hR0 : 0 < R := lt_trans hgn hRgn
  set ρ := gn / R with hρ
  have hρ0 : 0 < ρ := div_pos hgn hR0
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hR0]; exact hRgn
  have hρR : ρ * R = gn := by rw [hρ]; field_simp
  -- the one-period resource inequality
  have hres : ∀ t, gn * (k (t + 1) - kstar) + (y t - cy) + (o t - co) / gn ≤
      R * (k t - kstar) := by
    intro t
    obtain ⟨hkt, -, -, he⟩ := hfeas t
    have := op_concave_tangent hfc (Set.mem_Ici.2 hks.le) (Set.mem_Ici.2 hkt) hfd
    have e : (o t - co) / gn = o t / gn - co / gn := by ring
    rw [e, hR]
    nlinarith
  -- the value gain of each generation at the prices `(1, 1/R)`
  have hD : ∀ t, u cy + β * u co ≤ u (y t) + β * u (o (t + 1)) →
      β * up co * (R * (y t - cy) + (o (t + 1) - co)) ≥
        u (y t) + β * u (o (t + 1)) - (u cy + β * u co) := by
    intro t _
    have h1 := op_concave_tangent huc (show cy ∈ Set.Ioi 0 from hcy)
      (show y t ∈ Set.Ioi 0 from (hfeas t).2.1) hucy
    have h2 := op_concave_tangent huc (show co ∈ Set.Ioi 0 from hco)
      (show o (t + 1) ∈ Set.Ioi 0 from (hfeas (t + 1)).2.2.1) huco
    have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
    rw [heul] at h1
    nlinarith
  have hβu : 0 < β * up co := mul_pos hβ hupco
  set D : ℕ → ℝ := fun t => (y t - cy) + (o (t + 1) - co) / R with hDdef
  have hDnn : ∀ t, 0 ≤ D t := by
    intro t
    have := hD t (hgen t)
    have h0 : 0 ≤ R * (y t - cy) + (o (t + 1) - co) := by
      by_contra h
      push Not at h
      have := mul_neg_of_pos_of_neg hβu h
      linarith [hgen t]
    simp only [hDdef]
    have : (y t - cy) + (o (t + 1) - co) / R = (R * (y t - cy) + (o (t + 1) - co)) / R := by
      field_simp
    rw [this]
    exact div_nonneg h0 hR0.le
  have ho0 : co ≤ o 0 := by
    by_contra h
    push Not at h
    have := hum (show o 0 ∈ Set.Ioi 0 from (hfeas 0).2.2.1) (show co ∈ Set.Ioi 0 from hco) h
    linarith
  -- the telescoped present-value inequality
  have hP : ∀ T, (o 0 - co) / gn + (∑ t ∈ Finset.range T, ρ ^ t * D t) + ρ ^ T * (y T - cy) +
      ρ ^ (T + 1) * R * (k (T + 1) - kstar) ≤ 0 := by
    intro T
    induction T with
    | zero =>
      have := hres 0
      rw [hk0, sub_self, mul_zero] at this
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add, pow_one]
      rw [hρR]
      linarith
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have hstep := hres (T + 1)
      have hpow : 0 ≤ ρ ^ (T + 1) := pow_nonneg hρ0.le _
      have hm := mul_le_mul_of_nonneg_left hstep hpow
      have e : ρ ^ T * D T + ρ ^ (T + 1) * (y (T + 1) - cy) +
          ρ ^ (T + 1 + 1) * R * (k (T + 1 + 1) - kstar) - ρ ^ T * (y T - cy) -
          ρ ^ (T + 1) * R * (k (T + 1) - kstar) =
          ρ ^ (T + 1) * (gn * (k (T + 1 + 1) - kstar) + (y (T + 1) - cy) +
            (o (T + 1) - co) / gn - R * (k (T + 1) - kstar)) := by
        simp only [hDdef, pow_succ]
        field_simp
        rw [← hρR]
        ring
      linarith
  -- the right-hand side vanishes
  have hbound : ∀ T, (o 0 - co) / gn + (∑ t ∈ Finset.range T, ρ ^ t * D t) ≤
      ρ ^ T * (cy + gn * kstar) := by
    intro T
    have h := hP T
    have hy : -cy ≤ y T - cy := by linarith [(hfeas T).2.1]
    have hk : -kstar ≤ k (T + 1) - kstar := by linarith [(hfeas (T + 1)).1]
    have hpT : 0 ≤ ρ ^ T := pow_nonneg hρ0.le _
    have h1 := mul_le_mul_of_nonneg_left hy hpT
    have h2 := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ ρ ^ (T + 1) * R)
    have e : ρ ^ (T + 1) * R * -kstar = -(ρ ^ T * gn * kstar) := by
      rw [pow_succ]; linear_combination (-(ρ ^ T) * kstar) * hρR
    nlinarith
  -- someone gains strictly
  obtain ⟨c, hc, m, hlow⟩ : ∃ c > 0, ∃ m : ℕ, ∀ T, m < T →
      c ≤ (o 0 - co) / gn + ∑ t ∈ Finset.range T, ρ ^ t * D t := by
    have hsum : ∀ T, 0 ≤ ∑ t ∈ Finset.range T, ρ ^ t * D t := fun T =>
      Finset.sum_nonneg fun t _ => mul_nonneg (pow_nonneg hρ0.le _) (hDnn t)
    rcases hstrict with h | ⟨m, hm⟩
    · have ho : co < o 0 := by
        by_contra h'
        push Not at h'
        rcases h'.lt_or_eq with h'' | h''
        · have := hum (show o 0 ∈ Set.Ioi 0 from (hfeas 0).2.2.1)
            (show co ∈ Set.Ioi 0 from hco) h''
          linarith
        · rw [h''] at h; linarith
      refine ⟨(o 0 - co) / gn, div_pos (by linarith) hgn, 0, fun T _ => ?_⟩
      linarith [hsum T]
    · have hDm : 0 < D m := by
        have := hD m (hgen m)
        have h0 : 0 < R * (y m - cy) + (o (m + 1) - co) := by
          by_contra h
          push Not at h
          have := mul_nonpos_of_nonneg_of_nonpos hβu.le h
          linarith
        simp only [hDdef]
        have : (y m - cy) + (o (m + 1) - co) / R = (R * (y m - cy) + (o (m + 1) - co)) / R := by
          field_simp
        rw [this]
        exact div_pos h0 hR0
      refine ⟨ρ ^ m * D m, mul_pos (pow_pos hρ0 _) hDm, m, fun T hT => ?_⟩
      have := Finset.single_le_sum (f := fun t => ρ ^ t * D t)
        (fun t _ => mul_nonneg (pow_nonneg hρ0.le _) (hDnn t)) (Finset.mem_range.2 hT)
      have : 0 ≤ (o 0 - co) / gn := div_nonneg (by linarith) hgn.le
      linarith
  have hlim : Tendsto (fun T => ρ ^ T * (cy + gn * kstar)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const (cy + gn * kstar)
    rwa [zero_mul] at this
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hc))
  have h1 := hlow (max T0 (m + 1)) (lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _))
  have h2 := hbound (max T0 (m + 1))
  have h3 := hT0 (max T0 (m + 1)) (le_max_left _ _)
  linarith

/-! ### The Cass–Balasko–Shell criterion at a steady state -/

/-- Miao, p. 551: at a steady state `R_t = R`, the Cass–Balasko–Shell sum
`Σ_t g_n⁻ᵗ ∏_{s=1}^t R_{s+1}` diverges iff `R ≥ g_n`. -/
theorem op_cass_steady_state {gn R : ℝ} {Rs : ℕ → ℝ} (hgn : 0 < gn) (hR : 0 < R)
    (hRs : ∀ s, Rs s = R) :
    ¬ Summable (fun t : ℕ => gn⁻¹ ^ t * ∏ s ∈ Finset.range t, Rs (s + 1)) ↔ gn ≤ R := by
  have e : (fun t : ℕ => gn⁻¹ ^ t * ∏ s ∈ Finset.range t, Rs (s + 1)) =
      fun t : ℕ => (R / gn) ^ t := by
    ext t
    simp only [hRs, Finset.prod_const, Finset.card_range]
    rw [div_eq_mul_inv, mul_pow, mul_comm]
  rw [e, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_pos (div_pos hR hgn), div_lt_one hgn, not_lt]

/-- Miao, p. 551: "a steady state equilibrium is Pareto optimal (or dynamically efficient) if
and only if `k* ≤ k_G` or `f′(k*) ≥ g_n − 1`": the Cass–Balasko–Shell sum at the steady state
with `R = 1 + f′(k*)` diverges iff `f′(k*) ≥ g_n − 1` iff `k* ≤ k_G`. (The Pareto optimality
halves are `op_pareto_optimal_of_lt_golden` and `op_dynamic_inefficiency`.) -/
theorem op_cass_corollary {fp : ℝ → ℝ} {gn kstar kG : ℝ} {Rs : ℕ → ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hfp : 0 < fp kstar) (hks : 0 < kstar) (hkG : 0 < kG)
    (hG : fp kG = gn - 1) (hRs : ∀ s, Rs s = 1 + fp kstar) :
    (¬ Summable (fun t : ℕ => gn⁻¹ ^ t * ∏ s ∈ Finset.range t, Rs (s + 1)) ↔
      gn - 1 ≤ fp kstar) ∧ (gn - 1 ≤ fp kstar ↔ kstar ≤ kG) := by
  refine ⟨?_, ?_⟩
  · rw [op_cass_steady_state hgn (by linarith) hRs]
    constructor <;> intro h <;> linarith
  · rw [← hG]
    exact hanti.le_iff_ge hkG hks

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asset price bubbles in the Diamond model

Miao, §16.3, pp. 551–555 (Tirole 1985). The initial old hold an unbacked government debt `B₁`
that is rolled over forever; `b_t = B_t/N_t`.

* Capital-market clearing (16.18) `g_n(k_{t+1} + b_{t+1}) = s(w_t, R_{t+1})` and no arbitrage
  (16.19) `g_nb_{t+1} = R_tb_t` (`eq_16_18`, `eq_16_19`); the bubble equilibrium
  (`OPIsBubbleEqm`); with `b = 0` it is the Diamond equilibrium (`op_bubble_zero`); a positive
  initial bubble stays positive (`op_bubble_pos`); combining the two equations,
  `g_nk_{t+1} = s(w_t, R_{t+1}) − R_tb_t` (`op_bubble_k_law`).
* The bubbly steady state has `R(k) = g_n`: the golden rule `k = k_G`, with
  `b* = s(w(k_G), g_n)/g_n − k_G` (`op_bubbly_steady`, `op_bubbly_steady_golden`).
  (The text's `g_b(b + k)` is a misprint for `g_n(b + k)`.)
* The locus `Δk_t = 0`: `b = [s(w(k), R(k)) − g_nk]/R(k)` (`opKLocus`, `op_k_locus`); it
  vanishes exactly at the Diamond steady states (`op_kLocus_zero_iff`); it is positive where
  `G(k) > k` and negative where `G(k) < k` (`op_kLocus_pos`, `op_kLocus_neg`), so (with the
  corrected Diamond conditions) positive on `(0, k_D)`, negative beyond.
* Its slope at a zero: `db/dk = (−s_wkf″ + s_Rf″ − g_n)/R(k)` (`op_kLocus_hasDerivAt`).
  **Correction:** the text divides by `R²(k)` (`op_kLocus_slope_printed`). Under the Diamond
  conditions `db/dk(k_D) < 0` (`op_kLocus_slope_neg`).
* The vector fields: with `s_R ≥ 0`, `k_{t+1} > k_t ⟺ b_t < b(k_t)` (`op_k_increase_iff`,
  `op_k_decrease_iff`, `op_k_stationary_iff`); `b_{t+1} − b_t = (R_t/g_n − 1)b_t`
  (`op_b_diff`), `b_{t+1} > b_t ⟺ k_t < k_G` (`op_b_increase_iff`), and `Δb = 0` is the line
  `k = k_G` (`op_b_stationary_iff`). The text's middle step replaces `R(k_{t+1})` by `R(k_t)`;
  this is valid as an equivalence when `s_R ≥ 0`, which the proof uses.
* A bubbly steady state exists iff `k_G < k_D` iff `R_D < g_n`: the bubbleless economy is
  dynamically inefficient (`op_bubbly_exists_iff`).

The saddle-point property of the bubbly steady state is proved for the linearised system in
Exercise 16.9 (`ex_16_9_saddle`). Not formalised: the global claims read off Figure 16.13 (the
nonlinear saddle path `b₁ = b(k₁)` and convergence to `k_D` for `b₁ < b(k₁)`), and the
literature survey on p. 555.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, (16.18), p. 552: `N_ts_t = B_{t+1} + K_{t+1}` in per capita terms is
`g_n(k_{t+1} + b_{t+1}) = s_t`. -/
theorem eq_16_18 {N N' sv B' K' b' k' gn : ℝ} (hN : N ≠ 0) (hcm : N * sv = B' + K')
    (hB' : B' = b' * N') (hK' : K' = k' * N') (hN' : N' = gn * N) :
    gn * (k' + b') = sv := by
  rw [hB', hK', hN'] at hcm
  have : N * (gn * (k' + b') - sv) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hN
  linarith

/-- Miao, (16.19), p. 552: no arbitrage `B_{t+1} = R_tB_t` in per capita terms is
`g_nb_{t+1} = R_tb_t`. -/
theorem eq_16_19 {N N' B B' b b' R gn : ℝ} (hN : N ≠ 0) (h : B' = R * B) (hB : B = b * N)
    (hB' : B' = b' * N') (hN' : N' = gn * N) : gn * b' = R * b := by
  rw [hB', hB, hN'] at h
  have : N * (gn * b' - R * b) = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_left hN
  linarith

/-- An equilibrium with a bubble (Miao, p. 552): `(k_t, b_t)` with `k_t > 0` satisfying (16.18)
and (16.19), where `w_t = w(k_t)`, `R_t = R(k_t)`. -/
def OPIsBubbleEqm (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn : ℝ) (k b : ℕ → ℝ) : Prop :=
  ∀ t, 0 < k t ∧ gn * (k (t + 1) + b (t + 1)) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) ∧
    gn * b (t + 1) = opRate fp (k t) * b t

/-- Miao, p. 552: "if `b_t = 0`, then (16.19) is redundant and (16.18) reduces to (16.16)": a
bubble equilibrium with `b₁ = 0` has `b_t = 0` for all `t` and is a Diamond equilibrium. -/
theorem op_bubble_zero {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k b : ℕ → ℝ} (hgn : 0 < gn)
    (h : OPIsBubbleEqm s f fp gn k b) (hb0 : b 0 = 0) :
    (∀ t, b t = 0) ∧ OPIsDiamondEqm s f fp gn k := by
  have hb : ∀ t, b t = 0 := by
    intro t
    induction t with
    | zero => exact hb0
    | succ t ih =>
      have := (h t).2.2
      rw [ih, mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hgn.ne'
  refine ⟨hb, (op_diamondEqm_iff hgn).2 fun t => ⟨(h t).1, ?_⟩⟩
  have := (h t).2.1
  rwa [hb (t + 1), add_zero] at this

/-- A positive initial bubble stays positive (`R_t > 0`). -/
theorem op_bubble_pos {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k b : ℕ → ℝ} (hgn : 0 < gn)
    (hfp : ∀ k, 0 < k → 0 < fp k) (h : OPIsBubbleEqm s f fp gn k b) (hb0 : 0 < b 0) :
    ∀ t, 0 < b t := by
  intro t
  induction t with
  | zero => exact hb0
  | succ t ih =>
    have he := (h t).2.2
    have hR : 0 < opRate fp (k t) := by simp only [opRate]; linarith [hfp _ (h t).1]
    have : 0 < gn * b (t + 1) := by rw [he]; exact mul_pos hR ih
    exact pos_of_mul_pos_right this hgn.le

/-- Combining (16.18) and (16.19): `g_nk_{t+1} = s(w_t, R_{t+1}) − R_tb_t`. -/
theorem op_bubble_k_law {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k b : ℕ → ℝ}
    (h : OPIsBubbleEqm s f fp gn k b) (t : ℕ) :
    gn * k (t + 1) = s (opWage f fp (k t)) (opRate fp (k (t + 1))) - opRate fp (k t) * b t := by
  have h1 := (h t).2.1
  have h2 := (h t).2.2
  linarith

/-- Miao, pp. 552–553: in a steady state with `b ≠ 0`, `g_n = R(k) = f′(k) + 1` and
`b* = s(w(k), g_n)/g_n − k`. -/
theorem op_bubbly_steady {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k b : ℝ} (hgn : 0 < gn)
    (h1 : gn * (k + b) = s (opWage f fp k) (opRate fp k)) (h2 : gn * b = opRate fp k * b)
    (hb : b ≠ 0) : opRate fp k = gn ∧ fp k = gn - 1 ∧ b = s (opWage f fp k) gn / gn - k := by
  have hR : opRate fp k = gn := by
    have : (gn - opRate fp k) * b = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_right hb
    linarith
  refine ⟨hR, by simp only [opRate] at hR; linarith, ?_⟩
  rw [← hR] at h1 ⊢
  rw [eq_sub_iff_add_eq, eq_div_iff (by rw [hR]; exact hgn.ne'), add_comm, mul_comm]
  rw [hR] at h1 ⊢
  exact h1

/-- Miao, p. 553: "the bubbly steady state capital stock is equal to the Golden Rule capital
stock". -/
theorem op_bubbly_steady_golden {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k b kG : ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hk : 0 < k) (hkG : 0 < kG) (hG : fp kG = gn - 1)
    (h1 : gn * (k + b) = s (opWage f fp k) (opRate fp k)) (h2 : gn * b = opRate fp k * b)
    (hb : b ≠ 0) : k = kG ∧ b = s (opWage f fp kG) gn / gn - kG := by
  obtain ⟨-, hfk, hbk⟩ := op_bubbly_steady hgn h1 h2 hb
  have hkk : k = kG := op_golden_rule_unique hanti hk hkG hfk hG
  subst hkk
  exact ⟨rfl, hbk⟩

/-! ### The locus `Δk_t = 0` -/

/-- The locus `Δk_t = 0` of Figure 16.11: `b(k) = [s(w(k), R(k)) − g_nk]/R(k)`. -/
noncomputable def opKLocus (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn k : ℝ) : ℝ :=
  (s (opWage f fp k) (opRate fp k) - gn * k) / opRate fp k

/-- Miao, p. 553: on the locus `k_{t+1} = k_t`,
`0 = [s(w(k_t), R(k_t)) − R(k_t)b_t]/g_n − k_t`, i.e. `b_t = b(k_t)`. -/
theorem op_k_locus {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k b : ℝ} (hgn : 0 < gn)
    (hR : 0 < opRate fp k) :
    (s (opWage f fp k) (opRate fp k) - opRate fp k * b) / gn - k = 0 ↔
      b = opKLocus s f fp gn k := by
  unfold opKLocus
  rw [sub_eq_zero, div_eq_iff hgn.ne', eq_div_iff hR.ne']
  constructor <;> intro h <;> linarith

/-- Miao, p. 553: "this curve crosses the horizontal axis at ... the Diamond steady state":
`b(k) = 0` iff `g_nk = s(w(k), R(k))`, the steady-state condition of (16.16). -/
theorem op_kLocus_zero_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k : ℝ}
    (hR : 0 < opRate fp k) :
    opKLocus s f fp gn k = 0 ↔ gn * k = s (opWage f fp k) (opRate fp k) := by
  unfold opKLocus
  rw [div_eq_zero_iff, or_iff_left hR.ne']
  constructor <;> intro h <;> linarith

/-- With `s_R ≥ 0`: where `G(k) > k`, `s(w(k), R(k)) > g_nk`; where `G(k) < k`, `<`. -/
theorem op_S_vs_G {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn k : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k)
    (hG : 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) :
    (k < G k → gn * k < s (opWage f fp k) (opRate fp k)) ∧
      (G k < k → s (opWage f fp k) (opRate fp k) < gn * k) := by
  have hR1 : ∀ x, 0 < x → opRate fp x ∈ Set.Ioi 1 := fun x hx => by
    simp [opRate, hfp x hx]
  constructor
  · intro h
    have hfa := hanti (show k ∈ Set.Ioi 0 from hk)
      (show G k ∈ Set.Ioi 0 from hG.1) h
    have := hmono (hR1 _ hG.1) (hR1 _ hk) (by simp only [opRate]; linarith)
    nlinarith [hG.2]
  · intro h
    have hfa := hanti (show G k ∈ Set.Ioi 0 from hG.1)
      (show k ∈ Set.Ioi 0 from hk) h
    have := hmono (hR1 _ hk) (hR1 _ hG.1) (by simp only [opRate]; linarith)
    nlinarith [hG.2]

/-- The locus `b(k)` is positive where `G(k) > k` (e.g. on `(0, k_D)`), the substance of
"`db/dk(0) > 0`" (Miao, p. 553). -/
theorem op_kLocus_pos {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn k : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k)
    (hG : 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) (h : k < G k) :
    0 < opKLocus s f fp gn k := by
  have := (op_S_vs_G hgn hmono hanti hfp hk hG).1 h
  unfold opKLocus
  exact div_pos (by linarith) (by simp only [opRate]; linarith [hfp k hk])

/-- The locus `b(k)` is negative where `G(k) < k` (e.g. on `(k_D, ∞)`). -/
theorem op_kLocus_neg {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn k : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k)
    (hG : 0 < G k ∧ gn * G k = s (opWage f fp k) (opRate fp (G k))) (h : G k < k) :
    opKLocus s f fp gn k < 0 := by
  have := (op_S_vs_G hgn hmono hanti hfp hk hG).2 h
  unfold opKLocus
  exact div_neg_of_neg_of_pos (by linarith) (by simp only [opRate]; linarith [hfp k hk])

/-- Miao, p. 553: at a zero of the locus (`k = k_D`),
`db/dk = (−s_wkf″(k) + s_Rf″(k) − g_n)/R(k)`. -/
theorem op_kLocus_hasDerivAt {s : ℝ → ℝ → ℝ} {f fp fpp : ℝ → ℝ} {gn k sw sR : ℝ}
    (hs : HasFDerivAt (fun p : ℝ × ℝ => s p.1 p.2)
      (sw • ContinuousLinearMap.fst ℝ ℝ ℝ + sR • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (opWage f fp k, opRate fp k))
    (hf : HasDerivAt f (fp k) k) (hfpk : HasDerivAt fp (fpp k) k) (hR : opRate fp k ≠ 0)
    (hzero : s (opWage f fp k) (opRate fp k) = gn * k) :
    HasDerivAt (opKLocus s f fp gn) ((-sw * k * fpp k + sR * fpp k - gn) / opRate fp k) k := by
  have hw := op_wage_hasDerivAt hf hfpk
  have hRd : HasDerivAt (opRate fp) (fpp k) k := by
    unfold opRate; exact hfpk.const_add 1
  have hg := hs.comp_hasDerivAt k (hw.prodMk hRd)
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul] at hg
  have hN := hg.sub ((hasDerivAt_id' k).const_mul gn)
  have hq := hN.div hRd hR
  unfold opKLocus
  convert hq using 1
  · rfl
  · simp only [Pi.sub_apply, Function.comp_apply]
    rw [hzero]
    field_simp
    ring

/-- **Correction** (Miao, p. 553): the printed slope has denominator `R²(k)`; the slope is
`(−s_wkf″ + s_Rf″ − g_n)/R(k)`, which differs from the printed value whenever the numerator is
nonzero (since `R > 1`). -/
theorem op_kLocus_slope_printed {num R : ℝ} (hnum : num ≠ 0) (hR : 1 < R) :
    num / R ≠ num / R ^ 2 := by
  intro h
  have hR0 : R ≠ 0 := by linarith
  field_simp at h
  have : num * (R - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact hnum h'
  · linarith

/-- Miao, p. 553: "Under the Diamond conditions ... `db/dk(k_D) < 0`": with `s_R ≥ 0`, `f″ < 0`
and `0 < G′(k_D) = −s_wk_Df″/(g_n − s_Rf″) < 1`, the numerator `−s_wk_Df″ + s_Rf″ − g_n` is
negative. -/
theorem op_kLocus_slope_neg {gn kD sw sR fpp : ℝ} (hgn : 0 < gn) (hsR : 0 ≤ sR) (hfpp : fpp < 0)
    (hG1 : -sw * kD * fpp / (gn - sR * fpp) < 1) : -sw * kD * fpp + sR * fpp - gn < 0 := by
  have hd : 0 < gn - sR * fpp := by nlinarith
  rw [div_lt_one hd] at hG1
  linarith

/-! ### Vector fields -/

/-- Miao, p. 554: with `s_R ≥ 0`, `k_{t+1} > k_t ⟺ b_t < b(k_t)` (the arrows of
Figure 16.11), where `g_nk_{t+1} = s(w(k_t), R(k_{t+1})) − R(k_t)b_t`. -/
theorem op_k_increase_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k k' b : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k) (hk' : 0 < k')
    (heq : gn * k' = s (opWage f fp k) (opRate fp k') - opRate fp k * b) :
    k < k' ↔ b < opKLocus s f fp gn k := by
  have hR1 : ∀ x, 0 < x → opRate fp x ∈ Set.Ioi 1 := fun x hx => by
    simp [opRate, hfp x hx]
  have hR0 : 0 < opRate fp k := lt_trans one_pos (hR1 k hk)
  unfold opKLocus
  rw [lt_div_iff₀ hR0]
  constructor
  · intro h
    have hfa := hanti (show k ∈ Set.Ioi 0 from hk) (show k' ∈ Set.Ioi 0 from hk') h
    have := hmono (hR1 _ hk') (hR1 _ hk) (by simp only [opRate]; linarith)
    nlinarith
  · intro h
    by_contra h'
    push Not at h'
    have hfa := hanti.antitoneOn (show k' ∈ Set.Ioi 0 from hk')
      (show k ∈ Set.Ioi 0 from hk) h'
    have := hmono (hR1 _ hk) (hR1 _ hk') (by simp only [opRate]; linarith)
    nlinarith

/-- With `s_R ≥ 0`, `k_{t+1} < k_t ⟺ b_t > b(k_t)`. -/
theorem op_k_decrease_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k k' b : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k) (hk' : 0 < k')
    (heq : gn * k' = s (opWage f fp k) (opRate fp k') - opRate fp k * b) :
    k' < k ↔ opKLocus s f fp gn k < b := by
  have hR1 : ∀ x, 0 < x → opRate fp x ∈ Set.Ioi 1 := fun x hx => by
    simp [opRate, hfp x hx]
  have hR0 : 0 < opRate fp k := lt_trans one_pos (hR1 k hk)
  unfold opKLocus
  rw [div_lt_iff₀ hR0]
  constructor
  · intro h
    have hfa := hanti (show k' ∈ Set.Ioi 0 from hk') (show k ∈ Set.Ioi 0 from hk) h
    have := hmono (hR1 _ hk) (hR1 _ hk') (by simp only [opRate]; linarith)
    nlinarith
  · intro h
    by_contra h'
    push Not at h'
    have hfa := hanti.antitoneOn (show k ∈ Set.Ioi 0 from hk)
      (show k' ∈ Set.Ioi 0 from hk') h'
    have := hmono (hR1 _ hk') (hR1 _ hk) (by simp only [opRate]; linarith)
    nlinarith

/-- With `s_R ≥ 0`, `k_{t+1} = k_t ⟺ b_t = b(k_t)`: the locus `Δk = 0`. -/
theorem op_k_stationary_iff {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn k k' b : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp k)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hk : 0 < k) (hk' : 0 < k')
    (heq : gn * k' = s (opWage f fp k) (opRate fp k') - opRate fp k * b) :
    k' = k ↔ b = opKLocus s f fp gn k := by
  have h1 := op_k_increase_iff hgn hmono hanti hfp hk hk' heq
  have h2 := op_k_decrease_iff hgn hmono hanti hfp hk hk' heq
  constructor
  · intro h
    rcases lt_trichotomy b (opKLocus s f fp gn k) with hb | hb | hb
    · exact absurd (h1.2 hb) (by rw [h]; exact lt_irrefl k)
    · exact hb
    · exact absurd (h2.2 hb) (by rw [h]; exact lt_irrefl k)
  · intro h
    rcases lt_trichotomy k' k with hk2 | hk2 | hk2
    · exact absurd (h2.1 hk2) (by rw [h]; exact lt_irrefl _)
    · exact hk2
    · exact absurd (h1.1 hk2) (by rw [h]; exact lt_irrefl _)

/-- Miao, p. 554: `b_{t+1} − b_t = (R_t/g_n − 1)b_t`. -/
theorem op_b_diff {gn R b b' : ℝ} (hgn : 0 < gn) (heq : gn * b' = R * b) :
    b' - b = (R / gn - 1) * b := by
  field_simp
  linarith

/-- Miao, p. 554: `b_{t+1} > b_t ⟺ R_t/g_n − 1 > 0 ⟺ k_t < k_G` (for `b_t > 0`). -/
theorem op_b_increase_iff {fp : ℝ → ℝ} {gn k kG b b' : ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hk : 0 < k) (hkG : 0 < kG) (hG : fp kG = gn - 1)
    (hb : 0 < b) (heq : gn * b' = opRate fp k * b) :
    (b < b' ↔ 0 < opRate fp k / gn - 1) ∧ (b < b' ↔ k < kG) := by
  have hd := op_b_diff hgn heq
  have h1 : b < b' ↔ 0 < opRate fp k / gn - 1 := by
    constructor
    · intro h
      have : 0 < (opRate fp k / gn - 1) * b := by linarith
      exact pos_of_mul_pos_left this hb.le
    · intro h
      have := mul_pos h hb
      linarith
  refine ⟨h1, h1.trans ?_⟩
  rw [sub_pos, one_lt_div hgn]
  simp only [opRate]
  rw [show gn < 1 + fp k ↔ fp kG < fp k by rw [hG]; constructor <;> intro h <;> linarith]
  exact hanti.lt_iff_gt hkG hk

/-- Miao, p. 554: the locus `Δb_t = 0` (for `b_t > 0`) is the vertical line `k = k_G`. -/
theorem op_b_stationary_iff {fp : ℝ → ℝ} {gn k kG b b' : ℝ} (hgn : 0 < gn)
    (hanti : StrictAntiOn fp (Set.Ioi 0)) (hk : 0 < k) (hkG : 0 < kG) (hG : fp kG = gn - 1)
    (hb : 0 < b) (heq : gn * b' = opRate fp k * b) : b' = b ↔ k = kG := by
  have hd := op_b_diff hgn heq
  constructor
  · intro h
    rw [h, sub_self] at hd
    have h0 := (mul_eq_zero.1 hd.symm).resolve_right hb.ne'
    rw [sub_eq_zero, div_eq_one_iff_eq hgn.ne'] at h0
    simp only [opRate] at h0
    exact op_golden_rule_unique hanti hk hkG (by linarith) hG
  · intro h
    rw [h] at heq
    simp only [opRate, hG] at heq
    have : gn * (b' - b) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hgn.ne'
    linarith

/-- Miao, p. 554: "for a bubbly steady state to exist, we must have `k_G < k_D` or `R_D < g_n`.
That is, the bubbleless equilibrium must be dynamically inefficient." With `s_R ≥ 0`, `G` the
Diamond law with unique positive steady state `k_D` (`G > id` below, `G < id` above), a
steady-state bubble `b > 0` at `k_G` exists iff `k_G < k_D`, iff `R(k_D) < g_n`. -/
theorem op_bubbly_exists_iff {s : ℝ → ℝ → ℝ} {f fp G : ℝ → ℝ} {gn kG kD : ℝ} (hgn : 0 < gn)
    (hmono : MonotoneOn (s (opWage f fp kG)) (Set.Ioi 1)) (hanti : StrictAntiOn fp (Set.Ioi 0))
    (hfp : ∀ k, 0 < k → 0 < fp k) (hkG : 0 < kG) (hkD : 0 < kD) (hGR : fp kG = gn - 1)
    (hG : 0 < G kG ∧ gn * G kG = s (opWage f fp kG) (opRate fp (G kG)))
    (hfixD : G kD = kD) (hbelow : ∀ k, 0 < k → k < kD → k < G k)
    (habove : ∀ k, kD < k → G k < k) :
    ((∃ b, 0 < b ∧ gn * (kG + b) = s (opWage f fp kG) (opRate fp kG)) ↔ kG < kD) ∧
      (kG < kD ↔ opRate fp kD < gn) := by
  have hSG := op_S_vs_G hgn hmono hanti hfp hkG hG
  have hRG : opRate fp kG = gn := by simp only [opRate, hGR]; ring
  refine ⟨⟨?_, fun h => ?_⟩, ?_⟩
  · rintro ⟨b, hb, hbe⟩
    by_contra h
    push Not at h
    have hle : G kG ≤ kG := by
      rcases h.lt_or_eq with h' | h'
      · exact (habove kG h').le
      · rw [← h', hfixD]
    rcases hle.lt_or_eq with h' | h'
    · have := hSG.2 h'
      nlinarith
    · have : s (opWage f fp kG) (opRate fp kG) = gn * kG := by
        have e := hG.2
        rw [h'] at e
        linarith
      nlinarith
  · have := hSG.1 (hbelow kG hkG h)
    refine ⟨s (opWage f fp kG) (opRate fp kG) / gn - kG, ?_, ?_⟩
    · rw [sub_pos, lt_div_iff₀ hgn]; linarith
    · field_simp; ring
  · simp only [opRate]
    rw [show 1 + fp kD < gn ↔ fp kD < fp kG by rw [hGR]; constructor <;> intro h <;> linarith]
    exact (hanti.lt_iff_gt hkD hkG).symm

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 16.3, 16.4 and 16.6–16.9

Miao, §16.4, pp. 556–558 (Exercise 16.5 is in `OPExercisesCES`).

* Cobb–Douglas technology `f(k) = Ak^α`: derivative and wage `w(k) = (1 − α)Ak^α`
  (`opCD`, `opCDfp`, `op_cd_hasDerivAt`, `op_cd_wage`); the steady state of `k = ck^α`
  (`opKstarCD`, `op_cd_steady_iff`) and global convergence of `k_{t+1} = ck_t^α`
  (`op_cd_converge`).
* **Exercise 16.3** (CRRA `u(c) = c^{1−γ}/(1 − γ)`, `f = k^α`): the saving function
  `s = w/(1 + β^{−1/γ}R^{1−1/γ})` (`opCRRASaving`) solves the Euler equation and is the optimum
  (`ex_16_3_euler`, `ex_16_3_optimal`); it increases in `R` for `γ < 1`, decreases for `γ > 1`
  and is `βw/(1 + β)` for `γ = 1` (`ex_16_3_mono_lt`, `ex_16_3_anti_gt`, `ex_16_3_gamma_one`);
  the law of motion (`ex_16_3_law`).
* **Exercise 16.4** (log, `f = k^α`): `k_{t+1} = β(1 − α)k_t^α/((1 + β)g_n)` (`ex_16_4_law`), the
  unique positive steady state (`ex_16_4_steady`), global convergence (`ex_16_4_converge`), the
  marginal product at the steady state and dynamic (in)efficiency, both of which occur
  (`ex_16_4_mpk`, `ex_16_4_inefficient`, `ex_16_4_efficient`).
* **Exercise 16.6** (depreciation `δ`): `R = 1 + f′(k) − δ` (`ex_16_6_rate`), the law of motion
  (`OPIsDiamondEqmDep`) and its `δ = 1` form (`ex_16_6_full`); with log utility the law does
  not depend on `δ` (`ex_16_6_log`).
* **Exercise 16.7** (spending `G_t` financed by lump-sum taxes on the young, log, `k^α`): the law
  `k_{t+1} = β((1 − α)k_t^α − G_t)/((1 + β)g_n)` (`ex_16_7_a`); a permanent increase lowers the
  stable steady state (`ex_16_7_b`); higher spending at any dates (permanent or temporary)
  lowers the whole capital path, strictly after the first higher date (`ex_16_7_bc_path`).
* **Exercise 16.8** (social security, log, `k^α`): pay-as-you-go saving and the law of motion
  (`ex_16_8_a_i`), less capital in steady state (`ex_16_8_a_ii`), the welfare effect at given
  prices (lifetime wealth falls iff `R > g_n`) and the steady-state consumption trade-off
  (`ex_16_8_a_iii`, `ex_16_8_a_iii_resources`); fully funded social security is neutral
  (`ex_16_8_b`).
* **Exercise 16.9**: the linearisation of the §16.3 system at the bubbly steady state
  (`ex_16_9_linearization`) has roots `0 < λ₁ < 1 < λ₂`: a saddle, with a unique convergent
  path for each initial capital (`ex_16_9_roots`, `ex_16_9_saddle`).

Not formalised: the drawings asked for in Exercise 16.7(b)–(c) (their content is
`ex_16_7_bc_path`) and the "explain the intuition" parts.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-! ### Cobb–Douglas technology -/

/-- Cobb–Douglas `f(k) = Ak^α`. -/
noncomputable def opCD (A α k : ℝ) : ℝ := A * k ^ α

/-- Its derivative `f′(k) = Aαk^{α−1}`. -/
noncomputable def opCDfp (A α k : ℝ) : ℝ := A * α * k ^ (α - 1)

theorem op_cd_hasDerivAt {A α k : ℝ} (hk : 0 < k) :
    HasDerivAt (opCD A α) (opCDfp A α k) k := by
  have := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).const_mul A
  unfold opCD opCDfp
  convert this using 1
  ring

/-- The Cobb–Douglas wage `w(k) = (1 − α)Ak^α`. -/
theorem op_cd_wage {A α k : ℝ} (hk : 0 < k) :
    opWage (opCD A α) (opCDfp A α) k = (1 - α) * A * k ^ α := by
  unfold opWage opCD opCDfp
  rw [Real.rpow_sub_one hk.ne']
  field_simp

/-- `k^α = k · k^{α−1}`. -/
theorem op_rpow_eq_mul {k α : ℝ} (hk : 0 < k) : k ^ α = k * k ^ (α - 1) := by
  rw [Real.rpow_sub_one hk.ne']; field_simp

/-- The positive steady state of `k = ck^α` (`0 < α < 1`, `c > 0`): `k* = c^{1/(1−α)}`. -/
noncomputable def opKstarCD (c α : ℝ) : ℝ := c ^ (1 - α)⁻¹

theorem op_kstarCD_pos {c α : ℝ} (hc : 0 < c) : 0 < opKstarCD c α :=
  Real.rpow_pos_of_pos hc _

/-- `k = ck^α` with `k > 0` iff `k = c^{1/(1−α)}`. -/
theorem op_cd_steady_iff {c α k : ℝ} (hc : 0 < c) (hα1 : α < 1) (hk : 0 < k) :
    k = c * k ^ α ↔ k = opKstarCD c α := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have hka : 0 < k ^ α := Real.rpow_pos_of_pos hk α
  have hsub : k ^ (1 - α) = k / k ^ α := by
    rw [Real.rpow_sub hk, Real.rpow_one]
  constructor
  · intro h
    have : k ^ (1 - α) = c := by
      rw [hsub, div_eq_iff hka.ne']; exact h
    unfold opKstarCD
    rw [← this, Real.rpow_rpow_inv hk.le h1]
  · intro h
    have : k ^ (1 - α) = c := by
      rw [h]; unfold opKstarCD
      rw [Real.rpow_inv_rpow hc.le h1]
    rw [hsub, div_eq_iff hka.ne'] at this
    exact this

/-- Global convergence of `k_{t+1} = ck_t^α` from every `k₀ > 0` to `c^{1/(1−α)}`, via
`ln k_{t+1} − ln k* = α(ln k_t − ln k*)`. -/
theorem op_cd_converge {c α : ℝ} {k : ℕ → ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    (hk0 : 0 < k 0) (hlaw : ∀ t, k (t + 1) = c * k t ^ α) :
    (∀ t, 0 < k t) ∧ Tendsto k atTop (𝓝 (opKstarCD c α)) := by
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih => rw [hlaw]; exact mul_pos hc (Real.rpow_pos_of_pos ih _)
  refine ⟨hpos, ?_⟩
  set L := Real.log c / (1 - α) with hL
  have h1 : (1 - α) ≠ 0 := by linarith
  have hlog : ∀ t, Real.log (k t) - L = α ^ t * (Real.log (k 0) - L) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hlaw, Real.log_mul hc.ne' (Real.rpow_pos_of_pos (hpos t) _).ne',
        Real.log_rpow (hpos t), pow_succ]
      have : Real.log c + α * Real.log (k t) - L = α * (Real.log (k t) - L) := by
        rw [hL]; field_simp; ring
      rw [this, ih]; ring
  have hT : Tendsto (fun t => Real.log (k t)) atTop (𝓝 L) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0.le hα1).mul_const (Real.log (k 0) - L)
    rw [zero_mul] at this
    have := this.add_const L
    rw [zero_add] at this
    refine this.congr fun t => ?_
    rw [← hlog t]; ring
  have hE := (Real.continuous_exp.tendsto L).comp hT
  have hk : (Real.exp ∘ fun t => Real.log (k t)) = k := by
    ext t; simp [Real.exp_log (hpos t)]
  rw [hk] at hE
  have hstar : Real.exp L = opKstarCD c α := by
    unfold opKstarCD
    rw [Real.rpow_def_of_pos hc, hL]
    congr 1
  rwa [hstar] at hE

/-! ### Exercise 16.3: CRRA utility -/

/-- The CRRA saving function `s(w, R) = w/(1 + β^{−1/γ}R^{1−1/γ})`. -/
noncomputable def opCRRASaving (β γ w R : ℝ) : ℝ :=
  w / (1 + β ^ (-1 / γ) * R ^ (1 - 1 / γ))

/-- CRRA utility `u(c) = c^{1−γ}/(1 − γ)` has `u′(c) = c^{−γ}`. -/
theorem op_crra_hasDerivAt {γ c : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun x => x ^ (1 - γ) / (1 - γ)) (c ^ (-γ)) c := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := (Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).div_const (1 - γ)
  convert this using 1
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- CRRA utility is strictly concave on `(0, ∞)` (`γ > 0`, `γ ≠ 1`). -/
theorem op_crra_strictConcave {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≠ 1) :
    StrictConcaveOn ℝ (Set.Ioi 0) (fun x => x ^ (1 - γ) / (1 - γ)) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0)
    (fun c hc => (op_crra_hasDerivAt hγ hc).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(op_crra_hasDerivAt hγ ha).deriv, (op_crra_hasDerivAt hγ hb).deriv]
  exact Real.rpow_lt_rpow_of_neg ha hab (by linarith)

/-- **Exercise 16.3** (Miao, p. 556): the CRRA saving `s = w/(1 + β^{−1/γ}R^{1−1/γ})` lies in
`(0, w)` and solves the Euler equation `(w − s)^{−γ} = β(Rs)^{−γ}R`. -/
theorem ex_16_3_euler {β γ w R : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hw : 0 < w) (hR : 0 < R) :
    0 < opCRRASaving β γ w R ∧ opCRRASaving β γ w R < w ∧
      (w - opCRRASaving β γ w R) ^ (-γ) =
        β * (R * opCRRASaving β γ w R) ^ (-γ) * R := by
  set q := β ^ (-1 / γ) * R ^ (1 - 1 / γ) with hq
  have hq0 : 0 < q := mul_pos (Real.rpow_pos_of_pos hβ _) (Real.rpow_pos_of_pos hR _)
  have hs : opCRRASaving β γ w R = w / (1 + q) := rfl
  have hs0 : 0 < w / (1 + q) := div_pos hw (by linarith)
  have hws : w - w / (1 + q) = q * (w / (1 + q)) := by field_simp; ring
  refine ⟨by rw [hs]; exact hs0, by rw [hs, div_lt_iff₀ (by linarith)]; nlinarith, ?_⟩
  rw [hs, hws, Real.mul_rpow hq0.le hs0.le, Real.mul_rpow hR.le hs0.le, hq,
    Real.mul_rpow (Real.rpow_pos_of_pos hβ _).le (Real.rpow_pos_of_pos hR _).le,
    ← Real.rpow_mul hβ.le, ← Real.rpow_mul hR.le]
  have e1 : -1 / γ * -γ = 1 := by field_simp
  have e2 : (1 - 1 / γ) * -γ = -γ + 1 := by field_simp; ring
  rw [e1, e2, Real.rpow_one, Real.rpow_add hR, Real.rpow_one]
  ring

/-- **Exercise 16.3**: the CRRA saving maximises `u(w − s) + βu(Rs)` over `s ∈ (0, w)`. -/
theorem ex_16_3_optimal {β γ w R : ℝ} (hβ : 0 < β) (hγ0 : 0 < γ) (hγ : γ ≠ 1) (hw : 0 < w)
    (hR : 0 < R) : ∀ s ∈ Set.Ioo 0 w,
      (w - s) ^ (1 - γ) / (1 - γ) + β * ((R * s) ^ (1 - γ) / (1 - γ)) ≤
        (w - opCRRASaving β γ w R) ^ (1 - γ) / (1 - γ) +
          β * ((R * opCRRASaving β γ w R) ^ (1 - γ) / (1 - γ)) := by
  obtain ⟨hs0, hsw, heul⟩ := ex_16_3_euler hβ hγ0 hw hR
  exact op_euler_sufficient (u := fun x => x ^ (1 - γ) / (1 - γ)) (up := fun c => c ^ (-γ))
    (op_crra_strictConcave hγ0 hγ).concaveOn hβ.le hR hs0 hsw
    (op_crra_hasDerivAt hγ (by linarith)) (op_crra_hasDerivAt hγ (mul_pos hR hs0)) heul

/-- **Exercise 16.3**: for `γ < 1` (substitution effect dominates) saving increases strictly
with the interest rate. -/
theorem ex_16_3_mono_lt {β γ w : ℝ} (hβ : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hw : 0 < w) :
    StrictMonoOn (opCRRASaving β γ w) (Set.Ioi 0) := by
  intro R hR R' hR' h
  have he : 1 - 1 / γ < 0 := by
    have : 1 < 1 / γ := by rw [lt_div_iff₀ hγ0]; linarith
    linarith
  have hb := Real.rpow_pos_of_pos hβ (-1 / γ)
  have := Real.rpow_lt_rpow_of_neg hR h he
  unfold opCRRASaving
  apply div_lt_div_of_pos_left hw
  · have := Real.rpow_pos_of_pos (show (0 : ℝ) < R' from hR') (1 - 1 / γ); positivity
  · nlinarith

/-- **Exercise 16.3**: for `γ > 1` (income effect dominates) saving decreases strictly with the
interest rate. -/
theorem ex_16_3_anti_gt {β γ w : ℝ} (hβ : 0 < β) (hγ1 : 1 < γ) (hw : 0 < w) :
    StrictAntiOn (opCRRASaving β γ w) (Set.Ioi 0) := by
  intro R hR R' hR' h
  have hγ0 : 0 < γ := by linarith
  have he : 0 < 1 - 1 / γ := by
    have : 1 / γ < 1 := by rw [div_lt_iff₀ hγ0]; linarith
    linarith
  have hb := Real.rpow_pos_of_pos hβ (-1 / γ)
  have := Real.rpow_lt_rpow (le_of_lt hR) h he
  unfold opCRRASaving
  apply div_lt_div_of_pos_left hw
  · have := Real.rpow_pos_of_pos (show (0 : ℝ) < R from hR) (1 - 1 / γ); positivity
  · nlinarith

/-- **Exercise 16.3**: for `γ = 1` (log utility) saving `βw/(1 + β)` does not depend on `R`; it
is the log saving `opLogSaving` with no second-period income. -/
theorem ex_16_3_gamma_one {β w R : ℝ} (hβ : 0 < β) :
    opCRRASaving β 1 w R = β * w / (1 + β) ∧ opLogSaving β w 0 R = β * w / (1 + β) := by
  constructor
  · unfold opCRRASaving
    rw [show (-1 : ℝ) / 1 = -1 by norm_num, show (1 : ℝ) - 1 / 1 = 0 by norm_num,
      Real.rpow_zero, Real.rpow_neg_one]
    field_simp
    ring
  · unfold opLogSaving; ring

/-- **Exercise 16.3**: the equilibrium law of motion with CRRA utility and `f(k) = k^α`:
`k_{t+1} = (1 − α)k_t^α/(g_n[1 + β^{−1/γ}(1 + αk_{t+1}^{α−1})^{1−1/γ}])`. -/
theorem ex_16_3_law {β γ α gn : ℝ} {k : ℕ → ℝ} :
    OPIsDiamondEqm (opCRRASaving β γ) (opCD 1 α) (opCDfp 1 α) gn k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = (1 - α) * k t ^ α /
        (1 + β ^ (-1 / γ) * (1 + α * k (t + 1) ^ (α - 1)) ^ (1 - 1 / γ)) / gn := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [op_cd_wage h1] at h2
    exact h2.trans (by unfold opCRRASaving opRate opCDfp; ring_nf)
  · rw [op_cd_wage h1]
    exact h2.trans (by unfold opCRRASaving opRate opCDfp; ring_nf)

/-! ### Exercise 16.4: log utility and Cobb–Douglas -/

/-- **Exercise 16.4** (Miao, p. 556): with `u = ln c` and `f = k^α` the law of motion is
`k_{t+1} = β(1 − α)k_t^α/((1 + β)g_n)`. -/
theorem ex_16_4_law {β α gn : ℝ} {k : ℕ → ℝ} :
    OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCD 1 α) (opCDfp 1 α) gn k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = β * (1 - α) / ((1 + β) * gn) * k t ^ α := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [op_cd_wage h1] at h2
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)
  · rw [op_cd_wage h1]
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)

/-- **Exercise 16.4**: the unique positive steady state
`k* = [β(1 − α)/((1 + β)g_n)]^{1/(1−α)}`. -/
theorem ex_16_4_steady {β α gn k : ℝ} (hβ : 0 < β) (hα1 : α < 1) (hgn : 0 < gn) (hk : 0 < k) :
    k = β * (1 - α) / ((1 + β) * gn) * k ^ α ↔
      k = opKstarCD (β * (1 - α) / ((1 + β) * gn)) α :=
  op_cd_steady_iff (by have : 0 < 1 - α := by linarith
                       positivity) hα1 hk

/-- **Exercise 16.4**: every equilibrium path converges to `k*`. -/
theorem ex_16_4_converge {β α gn : ℝ} {k : ℕ → ℝ} (hβ : 0 < β) (hα0 : 0 < α) (hα1 : α < 1)
    (hgn : 0 < gn)
    (h : OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCD 1 α) (opCDfp 1 α) gn k) :
    Tendsto k atTop (𝓝 (opKstarCD (β * (1 - α) / ((1 + β) * gn)) α)) := by
  have hl := ex_16_4_law.1 h
  have hc : 0 < β * (1 - α) / ((1 + β) * gn) := by
    have : 0 < 1 - α := by linarith
    positivity
  exact (op_cd_converge hc hα0 hα1 (hl 0).1 fun t => (hl t).2).2

/-- **Exercise 16.4**: at the steady state `f′(k*) = α(1 + β)g_n/(β(1 − α))`, so the economy is
dynamically inefficient (`k* > k_G`) iff `α(1 + β)g_n/(β(1 − α)) < g_n − 1`. -/
theorem ex_16_4_mpk {β α gn : ℝ} (hβ : 0 < β) (hα1 : α < 1) (hgn : 0 < gn) :
    opCDfp 1 α (opKstarCD (β * (1 - α) / ((1 + β) * gn)) α) =
      α * (1 + β) * gn / (β * (1 - α)) := by
  have h1 : (1 - α) ≠ 0 := by linarith
  have h1' : 0 < 1 - α := by linarith
  set c := β * (1 - α) / ((1 + β) * gn) with hc
  have hc0 : 0 < c := by positivity
  have hk := op_kstarCD_pos (α := α) hc0
  have hkk : opKstarCD c α ^ (1 - α) = c := by
    unfold opKstarCD; rw [Real.rpow_inv_rpow hc0.le h1]
  have hneg : opKstarCD c α ^ (α - 1) = c⁻¹ := by
    rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg hk.le, hkk]
  unfold opCDfp
  rw [hneg, hc]
  field_simp

/-- **Exercise 16.4**: dynamic inefficiency occurs: `α = 1/10`, `β = 1`, `g_n = 2` give
`f′(k*) = 4/9 < g_n − 1`. -/
theorem ex_16_4_inefficient :
    opCDfp 1 (1 / 10) (opKstarCD (1 * (1 - 1 / 10) / ((1 + 1) * 2)) (1 / 10)) < 2 - 1 := by
  rw [ex_16_4_mpk (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-- **Exercise 16.4**: and so does dynamic efficiency: `α = 1/3`, `β = 1`, `g_n = 2` give
`f′(k*) = 2 > g_n − 1`. -/
theorem ex_16_4_efficient :
    2 - 1 < opCDfp 1 (1 / 3) (opKstarCD (1 * (1 - 1 / 3) / ((1 + 1) * 2)) (1 / 3)) := by
  rw [ex_16_4_mpk (by norm_num) (by norm_num) (by norm_num)]; norm_num

/-! ### Exercise 16.6: depreciation -/

/-- The Diamond equilibrium with depreciation `δ`:
`k_{t+1} = s(w(k_t), 1 + f′(k_{t+1}) − δ)/g_n`. -/
def OPIsDiamondEqmDep (s : ℝ → ℝ → ℝ) (f fp : ℝ → ℝ) (gn δ : ℝ) (k : ℕ → ℝ) : Prop :=
  ∀ t, 0 < k t ∧ k (t + 1) = s (opWage f fp (k t)) (1 + fp (k (t + 1)) - δ) / gn

/-- **Exercise 16.6** (Miao, p. 557): firms rent capital at `r`; profit maximisation gives
`r = f′(k)` (as in (16.15)), and a unit saved returns `R = 1 − δ + r = 1 + f′(k) − δ`. -/
theorem ex_16_6_rate {f fp : ℝ → ℝ} {K N r δ : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hf : HasDerivAt f (fp (K / N)) (K / N))
    (hmax : ∀ K' > 0, N * f (K' / N) - r * K' ≤ N * f (K / N) - r * K) :
    r = fp (K / N) ∧ 1 - δ + r = 1 + fp (K / N) - δ := by
  have h := eq_16_15 (R := r + 1) hK hN hf (by simpa using hmax)
  simp only [opRate] at h
  exact ⟨by linarith, by linarith⟩

/-- **Exercise 16.6**: with full depreciation `δ = 1`, `R = f′(k)` and
`k_{t+1} = s(w(k_t), f′(k_{t+1}))/g_n`; with `δ = 0` it is (16.16). -/
theorem ex_16_6_full {s : ℝ → ℝ → ℝ} {f fp : ℝ → ℝ} {gn : ℝ} {k : ℕ → ℝ} :
    (OPIsDiamondEqmDep s f fp gn 1 k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = s (opWage f fp (k t)) (fp (k (t + 1))) / gn) ∧
      (OPIsDiamondEqmDep s f fp gn 0 k ↔ OPIsDiamondEqm s f fp gn k) := by
  constructor
  · refine forall_congr' fun t => and_congr_right fun _ => ?_
    rw [show 1 + fp (k (t + 1)) - 1 = fp (k (t + 1)) by ring]
  · refine forall_congr' fun t => and_congr_right fun _ => ?_
    rw [show 1 + fp (k (t + 1)) - 0 = opRate fp (k (t + 1)) by simp [opRate]]

/-- **Exercise 16.6**: with log utility and `f = k^α` the law
`k_{t+1} = β(1 − α)k_t^α/((1 + β)g_n)` holds for every depreciation rate. -/
theorem ex_16_6_log {β α gn δ : ℝ} {k : ℕ → ℝ} :
    OPIsDiamondEqmDep (fun w R => opLogSaving β w 0 R) (opCD 1 α) (opCDfp 1 α) gn δ k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = β * (1 - α) / ((1 + β) * gn) * k t ^ α := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [op_cd_wage h1] at h2
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)
  · rw [op_cd_wage h1]
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)

/-! ### Exercise 16.7: government spending -/

/-- **Exercise 16.7(a)** (Miao, p. 557): with lump-sum taxes `G_t` on the young, log utility and
`f = k^α`, optimal saving is `β(w_t − G_t)/(1 + β)` (`op_log_saving` with income `w_t − G_t`),
and capital-market clearing gives `k_{t+1} = β((1 − α)k_t^α − G_t)/((1 + β)g_n)`. -/
theorem ex_16_7_a {β α gn : ℝ} {k Gs : ℕ → ℝ} (hβ : 0 < β) (hgn : 0 < gn)
    (hk : ∀ t, 0 < k t) :
    (∀ t, gn * k (t + 1) = opLogSaving β (opWage (opCD 1 α) (opCDfp 1 α) (k t) - Gs t) 0
      (opRate (opCDfp 1 α) (k (t + 1)))) ↔
      ∀ t, k (t + 1) = β * ((1 - α) * k t ^ α - Gs t) / ((1 + β) * gn) := by
  refine forall_congr' fun t => ?_
  rw [op_cd_wage (hk t)]
  unfold opLogSaving
  simp only [zero_div, sub_zero]
  have hb : (1 + β) ≠ 0 := by linarith
  constructor
  · intro h
    rw [eq_div_iff (mul_ne_zero hb hgn.ne')]
    field_simp at h
    linarith
  · intro h
    rw [h]; field_simp

/-- **Exercise 16.7(b)**: a permanent increase in spending from `G_L` to `G_H` lowers the stable
steady state. Steady states solve `(1 − α)k^α − dk = G` with `d = (1 + β)g_n/β`; on the stable
branch, where the slope of the law `α(1 − α)k^{α−1}/d` is at most `1`, `k_H < k_L`. -/
theorem ex_16_7_b {α d Glow Ghigh kL kH : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hkL : 0 < kL)
    (hkH : 0 < kH) (hGlh : Glow < Ghigh) (hL : (1 - α) * kL ^ α - d * kL = Glow)
    (hH : (1 - α) * kH ^ α - d * kH = Ghigh) (hstab : α * (1 - α) * kL ^ (α - 1) ≤ d) :
    kH < kL := by
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have ht := op_strictConcave_tangent (Real.strictConcaveOn_rpow hα0 hα1)
      (Set.mem_Ici.2 hkL.le) (Set.mem_Ici.2 hkH.le) h.ne' (Real.hasDerivAt_rpow_const
        (p := α) (Or.inl hkL.ne'))
    have h1 : 0 < 1 - α := by linarith
    have : (1 - α) * kH ^ α < (1 - α) * kL ^ α + α * (1 - α) * kL ^ (α - 1) * (kH - kL) := by
      nlinarith
    nlinarith
  · rw [h] at hL; linarith

/-- **Exercise 16.7(b)–(c)**: the capital path under any spending path `G′ ≥ G` (a permanent or a
temporary increase) lies below the path under `G` from the same `k₀`, strictly below after the
first date `T` with `G′_T > G_T`. -/
theorem ex_16_7_bc_path {β α gn : ℝ} {k k' Gs Gs' : ℕ → ℝ} (hβ : 0 < β) (hα0 : 0 < α)
    (hα1 : α < 1) (hgn : 0 < gn) (hk' : ∀ t, 0 < k' t) (h0 : k' 0 = k 0)
    (hlaw : ∀ t, k (t + 1) = β * ((1 - α) * k t ^ α - Gs t) / ((1 + β) * gn))
    (hlaw' : ∀ t, k' (t + 1) = β * ((1 - α) * k' t ^ α - Gs' t) / ((1 + β) * gn))
    (hG : ∀ t, Gs t ≤ Gs' t) :
    (∀ t, k' t ≤ k t) ∧ ∀ T, Gs T < Gs' T → ∀ t, T < t → k' t < k t := by
  have hc : 0 < β / ((1 + β) * gn) := by positivity
  have h1 : 0 < 1 - α := by linarith
  have hstep : ∀ t, k' t ≤ k t → k' (t + 1) ≤ k (t + 1) ∧
      (Gs t < Gs' t ∨ k' t < k t → k' (t + 1) < k (t + 1)) := by
    intro t ht
    have hp := Real.rpow_le_rpow (hk' t).le ht hα0.le
    rw [hlaw, hlaw']
    have e : ∀ x G, β * ((1 - α) * x - G) / ((1 + β) * gn) =
        β / ((1 + β) * gn) * ((1 - α) * x - G) := fun x G => by ring
    rw [e, e]
    refine ⟨mul_le_mul_of_nonneg_left (by nlinarith [hG t]) hc.le, fun hor => ?_⟩
    apply mul_lt_mul_of_pos_left _ hc
    rcases hor with hor | hor
    · nlinarith
    · have := Real.rpow_lt_rpow (hk' t).le hor hα0
      nlinarith [hG t]
  have hle : ∀ t, k' t ≤ k t := by
    intro t
    induction t with
    | zero => rw [h0]
    | succ t ih => exact (hstep t ih).1
  refine ⟨hle, fun T hT t ht => ?_⟩
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | h
    · exact (hstep t (hle t)).2 (Or.inr (ih h))
    · rw [h] at hT; exact (hstep t (hle t)).2 (Or.inl hT)

/-! ### Exercise 16.8: social security -/

/-- **Exercise 16.8(a)(i)** (Miao, p. 558): pay-as-you-go social security. The young pay `d_t`
and the old receive `g_nd_{t+1}`; optimal saving is `s = (β(w − d) − g_nd′/R)/(1 + β)`
(`op_log_saving` with incomes `w − d`, `g_nd′`), so the law of motion is
`g_nk_{t+1} = [β((1 − α)k_t^α − d_t) − g_nd_{t+1}/(1 + αk_{t+1}^{α−1})]/(1 + β)`. -/
theorem ex_16_8_a_i {β α gn : ℝ} {k ds : ℕ → ℝ} (hk : ∀ t, 0 < k t) :
    (∀ t, gn * k (t + 1) = opLogSaving β (opWage (opCD 1 α) (opCDfp 1 α) (k t) - ds t)
      (gn * ds (t + 1)) (opRate (opCDfp 1 α) (k (t + 1)))) ↔
      ∀ t, gn * k (t + 1) = (β * ((1 - α) * k t ^ α - ds t) -
        gn * ds (t + 1) / (1 + α * k (t + 1) ^ (α - 1))) / (1 + β) := by
  refine forall_congr' fun t => ?_
  rw [op_cd_wage (hk t)]
  unfold opLogSaving opRate opCDfp
  simp only [mul_one, one_mul]

/-- **Exercise 16.8(a)(ii)**: introducing social security lowers the steady-state capital stock:
a steady state with `d > 0` has less capital than the steady state `k₀` without. -/
theorem ex_16_8_a_ii {β α gn d k k0 : ℝ} (hβ : 0 < β) (hα0 : 0 < α) (hα1 : α < 1)
    (hgn : 0 < gn) (hd : 0 < d) (hk : 0 < k) (hk0 : 0 < k0)
    (hss : gn * k = (β * ((1 - α) * k ^ α - d) - gn * d / (1 + α * k ^ (α - 1))) / (1 + β))
    (hss0 : gn * k0 = β * ((1 - α) * k0 ^ α) / (1 + β)) : k < k0 := by
  have hR : 0 < 1 + α * k ^ (α - 1) := by
    have := Real.rpow_pos_of_pos hk (α - 1); positivity
  have hpd : 0 < gn * d / (1 + α * k ^ (α - 1)) := by positivity
  have h1 : (1 + β) * gn * k < β * (1 - α) * k ^ α := by
    rw [eq_div_iff (by linarith)] at hss
    nlinarith
  have h2 : (1 + β) * gn * k0 = β * (1 - α) * k0 ^ α := by
    rw [eq_div_iff (by linarith)] at hss0
    linarith
  rw [op_rpow_eq_mul hk] at h1
  rw [op_rpow_eq_mul hk0] at h2
  have hc : 0 < β * (1 - α) := mul_pos hβ (by linarith)
  have h1' : (1 + β) * gn < β * (1 - α) * k ^ (α - 1) := by nlinarith
  have h2' : (1 + β) * gn = β * (1 - α) * k0 ^ (α - 1) := by
    have : k0 * ((1 + β) * gn - β * (1 - α) * k0 ^ (α - 1)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hk0.ne'
    linarith
  by_contra h
  push Not at h
  have := Real.rpow_le_rpow_of_nonpos hk0 h (by linarith : α - 1 ≤ 0)
  nlinarith

/-- Lifetime utility of a generation at prices `(w, R)` under a constant pay-as-you-go
contribution `d`, at the optimal log saving: `ln c_y + β ln c_o` with lifetime wealth
`W = w − d + g_nd/R`. -/
noncomputable def opPAYGWelfare (β gn w R d : ℝ) : ℝ :=
  Real.log ((w - d + gn * d / R) / (1 + β)) +
    β * Real.log (β * R * (w - d + gn * d / R) / (1 + β))

/-- **Exercise 16.8(a)(iii)**: at given prices a larger contribution changes lifetime wealth by
`−(1 − g_n/R)` per unit: welfare of a generation falls iff `R > g_n` (dynamically efficient)
and rises iff `R < g_n` (dynamically inefficient). The optimal consumptions are those of
`op_log_saving`. -/
theorem ex_16_8_a_iii {β gn w R d1 d2 : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hd : d1 < d2) (hW1 : 0 < w - d1 + gn * d1 / R) (hW2 : 0 < w - d2 + gn * d2 / R) :
    (gn < R → opPAYGWelfare β gn w R d2 < opPAYGWelfare β gn w R d1) ∧
      (R < gn → opPAYGWelfare β gn w R d1 < opPAYGWelfare β gn w R d2) := by
  have hW : ∀ d, w - d + gn * d / R = w - d * (1 - gn / R) := fun d => by ring
  have hmono : ∀ W1 W2, 0 < W1 → W1 < W2 →
      Real.log (W1 / (1 + β)) + β * Real.log (β * R * W1 / (1 + β)) <
        Real.log (W2 / (1 + β)) + β * Real.log (β * R * W2 / (1 + β)) := by
    intro W1 W2 h1 h12
    have a : Real.log (W1 / (1 + β)) < Real.log (W2 / (1 + β)) :=
      Real.log_lt_log (by positivity) (div_lt_div_of_pos_right h12 (by linarith))
    have b : Real.log (β * R * W1 / (1 + β)) < Real.log (β * R * W2 / (1 + β)) :=
      Real.log_lt_log (by positivity)
        (div_lt_div_of_pos_right (mul_lt_mul_of_pos_left h12 (by positivity)) (by linarith))
    nlinarith
  refine ⟨fun h => ?_, fun h => ?_⟩
  · apply hmono _ _ hW2
    rw [hW, hW]
    have : 0 < 1 - gn / R := by rw [sub_pos, div_lt_one hR]; exact h
    nlinarith
  · apply hmono _ _ hW1
    rw [hW, hW]
    have : 1 - gn / R < 0 := by rw [sub_neg, one_lt_div hR]; exact h
    nlinarith

/-- **Exercise 16.8(a)(iii)**: steady-state consumption per worker `f(k) − (g_n − 1)k` rises with
`k` below the golden rule and falls above it; since social security lowers `k`
(`ex_16_8_a_ii`), it lowers steady-state consumption when the economy is dynamically efficient
and raises it when it is dynamically inefficient. -/
theorem ex_16_8_a_iii_resources {f fp : ℝ → ℝ} {gn kG : ℝ}
    (hconc : StrictConcaveOn ℝ (Set.Ici 0) f) (hfd : ∀ k, 0 < k → HasDerivAt f (fp k) k)
    (hkG : 0 < kG) (hG : fp kG = gn - 1) :
    (∀ x y, 0 < x → x < y → y ≤ kG → f x - (gn - 1) * x < f y - (gn - 1) * y) ∧
      (∀ x y, kG ≤ x → x < y → f y - (gn - 1) * y < f x - (gn - 1) * x) := by
  have hanti := op_fp_strictAnti hconc hfd
  constructor
  · intro x y hx hxy hy
    have hy0 : 0 < y := by linarith
    have ht := op_strictConcave_tangent hconc (Set.mem_Ici.2 hy0.le) (Set.mem_Ici.2 hx.le)
      hxy.ne (hfd y hy0)
    have : gn - 1 ≤ fp y := by
      rw [← hG]; exact hanti.antitoneOn (show y ∈ Set.Ioi 0 from hy0)
        (show kG ∈ Set.Ioi 0 from hkG) hy
    nlinarith
  · intro x y hx hxy
    have hx0 : 0 < x := by linarith
    have ht := op_strictConcave_tangent hconc (Set.mem_Ici.2 hx0.le)
      (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ y)) hxy.ne' (hfd x hx0)
    have : fp x ≤ gn - 1 := by
      rw [← hG]; exact hanti.antitoneOn (show kG ∈ Set.Ioi 0 from hkG)
        (show x ∈ Set.Ioi 0 from hx0) hx
    nlinarith

/-- **Exercise 16.8(b)** (Miao, p. 558): fully funded social security. The young contribute `d`,
the old receive `Rd`. Optimal private saving is `s = βw/(1 + β) − d` (`op_log_saving` with
incomes `w − d`, `Rd`), so total saving `s + d = βw/(1 + β)` and consumption are unchanged;
with `g_nk_{t+1} = s_t + d_t` the law of motion is that of Exercise 16.4: social security has no
effect on capital or welfare. (Private saving may be negative when `d > βw/(1 + β)`.) -/
theorem ex_16_8_b {β w R d : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    opLogSaving β (w - d) (R * d) R + d = opLogSaving β w 0 R ∧
      w - d - opLogSaving β (w - d) (R * d) R = w - opLogSaving β w 0 R ∧
      R * opLogSaving β (w - d) (R * d) R + R * d = R * opLogSaving β w 0 R := by
  unfold opLogSaving
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-! ### Exercise 16.9: linearisation of the bubble economy -/

/-- The coefficients of the linearised system at the bubbly steady state `(k_G, b*)`, with
`D = g_n − s_Rf″`: `dk′ = m₁₁dk + m₁₂db`, `db′ = m₂₁dk + db`. -/
noncomputable def opLinM11 (gn sw sR fpp kG bs : ℝ) : ℝ := -fpp * (sw * kG + bs) / (gn - sR * fpp)

noncomputable def opLinM12 (gn sR fpp : ℝ) : ℝ := -gn / (gn - sR * fpp)

noncomputable def opLinM21 (gn fpp bs : ℝ) : ℝ := fpp * bs / gn

/-- **Exercise 16.9** (Miao, p. 558): the linearisation. Taking total differentials of
`g_nk_{t+1} = s(w(k_t), R(k_{t+1})) − R(k_t)b_t` and `g_nb_{t+1} = R(k_t)b_t` at `(k_G, b*)`
(`R = g_n`, `w′ = −k_Gf″`, `R′ = f″`):
`g_ndk′ = −s_wk_Gf″dk + s_Rf″dk′ − f″b*dk − g_ndb` and `g_ndb′ = f″b*dk + g_ndb`. With
`D = g_n − s_Rf″ ≠ 0` these are equivalent to `dk′ = m₁₁dk + m₁₂db`, `db′ = m₂₁dk + db`. -/
theorem ex_16_9_linearization {gn sw sR fpp kG bs dk db dk' db' : ℝ} (hgn : 0 < gn)
    (hD : gn - sR * fpp ≠ 0) :
    (gn * dk' = sw * (-kG * fpp) * dk + sR * fpp * dk' - (fpp * bs * dk + gn * db) ∧
      gn * db' = fpp * bs * dk + gn * db) ↔
      (dk' = opLinM11 gn sw sR fpp kG bs * dk + opLinM12 gn sR fpp * db ∧
        db' = opLinM21 gn fpp bs * dk + 1 * db) := by
  have hD' : gn - fpp * sR ≠ 0 := by rwa [mul_comm]
  have e : opLinM11 gn sw sR fpp kG bs * dk + opLinM12 gn sR fpp * db =
      (-fpp * (sw * kG + bs) * dk - gn * db) / (gn - sR * fpp) := by
    unfold opLinM11 opLinM12; field_simp; ring
  have e2 : opLinM21 gn fpp bs * dk + 1 * db = (fpp * bs * dk + gn * db) / gn := by
    unfold opLinM21; field_simp
  rw [e, e2, eq_div_iff hD, eq_div_iff hgn.ne']
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **Exercise 16.9**: with `s_w > 0`, `s_R ≥ 0`, `f″ < 0`, `b* > 0` the characteristic roots
satisfy `0 < λ₁ < 1 < λ₂`: the bubbly steady state is a saddle point (Miao, p. 555). -/
theorem ex_16_9_roots {gn sw sR fpp kG bs : ℝ} (hgn : 0 < gn) (hsw : 0 < sw) (hsR : 0 ≤ sR)
    (hfpp : fpp < 0) (hkG : 0 < kG) (hbs : 0 < bs) :
    cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 1 < 0 ∧
      0 < opLinM12 gn sR fpp * opLinM21 gn fpp bs ∧
      0 < cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 (-1) ∧
      0 < lamLo (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 ∧
      lamLo (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 < 1 ∧
      1 < lamHi (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 := by
  have hD : 0 < gn - sR * fpp := by nlinarith
  have hm : 0 < opLinM12 gn sR fpp * opLinM21 gn fpp bs := by
    unfold opLinM12 opLinM21
    rw [show -gn / (gn - sR * fpp) * (fpp * bs / gn) = (-fpp) * bs / (gn - sR * fpp) by
      field_simp]
    have : 0 < -fpp := by linarith
    positivity
  have hm11 : 0 < opLinM11 gn sw sR fpp kG bs := by
    unfold opLinM11
    have : 0 < -fpp := by linarith
    have : 0 < sw * kG + bs := by positivity
    positivity
  have h1 : cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp) (opLinM21 gn fpp bs) 1 1
      < 0 := by
    simp only [cp22]; nlinarith
  have hdet : 0 < cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
      (opLinM21 gn fpp bs) 1 0 := by
    simp only [cp22]
    unfold opLinM11 opLinM12 opLinM21
    rw [show (0 : ℝ) ^ 2 - (-fpp * (sw * kG + bs) / (gn - sR * fpp) + 1) * 0 +
      (-fpp * (sw * kG + bs) / (gn - sR * fpp) * 1 -
        -gn / (gn - sR * fpp) * (fpp * bs / gn)) = (-fpp) * sw * kG / (gn - sR * fpp) by
      field_simp; ring]
    have : 0 < -fpp := by linarith
    positivity
  have hm1 : 0 < cp22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
      (opLinM21 gn fpp bs) 1 (-1) := by
    simp only [cp22] at hdet ⊢
    nlinarith
  obtain ⟨hlo, hhi⟩ := roots22_lt h1
  have hf := cp22_factor h1 0
  have hlo0 : 0 < lamLo (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
      (opLinM21 gn fpp bs) 1 := by
    rw [hf] at hdet
    nlinarith
  exact ⟨h1, hm, hm1, hlo0, hlo, hhi⟩

/-- **Exercise 16.9** and Miao, p. 555 ("this steady state is a saddle point. For any given
initial value `k₁`, there is a unique `b₁` on the saddle path"), for the linearised system: for
every initial deviation `dk₀` there is a solution converging to the steady state, and every
bounded solution starts on the saddle line `db₀ = κ dk₀`. -/
theorem ex_16_9_saddle {gn sw sR fpp kG bs : ℝ} (hgn : 0 < gn) (hsw : 0 < sw) (hsR : 0 ≤ sR)
    (hfpp : fpp < 0) (hkG : 0 < kG) (hbs : 0 < bs) (dk0 : ℝ) :
    (∃ dk db : ℕ → ℝ, IsSol22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
        (opLinM21 gn fpp bs) 1 dk db ∧ dk 0 = dk0 ∧
        Tendsto dk atTop (𝓝 0) ∧ Tendsto db atTop (𝓝 0)) ∧
      ∀ dk db : ℕ → ℝ, IsSol22 (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
        (opLinM21 gn fpp bs) 1 dk db → BddSeq dk → BddSeq db →
        db 0 = kSaddle (opLinM11 gn sw sR fpp kG bs) (opLinM12 gn sR fpp)
          (opLinM21 gn fpp bs) 1 * dk 0 := by
  obtain ⟨h1, hm, hc, -, -, -⟩ := ex_16_9_roots hgn hsw hsR hfpp hkG hbs
  refine ⟨(saddle22_iff h1 hm).2 hc dk0, fun dk db h hK hB => ?_⟩
  exact (sHi_zero_iff h1 hm dk db 0).1 (sHi_zero_of_bdd h1 h hK hB)

end Miao.OverlappingGenerations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 16.5: the Diamond model with CES technology

Miao, §16.4, Exercise 16.5, pp. 556–557: `u = ln c` and
`f(k) = A[ak^ρ + 1 − a]^{1/ρ}` with `ρ = (σ − 1)/σ`, `σ` the elasticity of substitution.

* The derivative of `f`, the wage `w(k) = A(1 − a)[ak^ρ + 1 − a]^{1/ρ − 1}` and the law of
  motion `k_{t+1} = βw(k_t)/((1 + β)g_n)` (`opCES`, `ex_16_5_hasDerivAt`, `ex_16_5_wage`,
  `ex_16_5_law`).
* (a) `σ > 1` (`0 < ρ < 1`): a positive steady state exists (`ex_16_5_a`); `σ = 1` is
  Cobb–Douglas `Ak^a`, which has the positive steady state of Exercise 16.4
  (`ex_16_5_a_cobbDouglas`).
* (b) `σ < 1` (`ρ < 0`): `w(k) ≤ AMk` with `M` independent of `A` (`ex_16_5_b_bound`); for `A`
  small (`βAM < (1 + β)g_n`) there is no positive steady state (`ex_16_5_b_none`) and every
  path converges to `0` geometrically (`ex_16_5_b_collapse`); for `A` large
  (`βA(1 − a) > (1 + β)g_n`) there are at least two positive steady states, so uniqueness fails
  (`ex_16_5_b_two`).

Departure: the printed formula is undefined at `σ = 1` (exponent `σ/(σ − 1)`); "`σ = 1`
corresponds to Cobb–Douglas" is the limit `σ → 1`, so `σ = 1` is treated with `f = Ak^a`.
Not formalised: the stability of each steady state for `σ < 1` and an upper bound (two) on
their number.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- The CES aggregate `ak^ρ + 1 − a`. -/
noncomputable def opCESbase (a ρ k : ℝ) : ℝ := a * k ^ ρ + (1 - a)

/-- CES technology `f(k) = A[ak^ρ + 1 − a]^{1/ρ}`. -/
noncomputable def opCES (A a ρ k : ℝ) : ℝ := A * opCESbase a ρ k ^ (1 / ρ)

/-- Its derivative `f′(k) = Aak^{ρ−1}[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
noncomputable def opCESfp (A a ρ k : ℝ) : ℝ :=
  A * a * k ^ (ρ - 1) * opCESbase a ρ k ^ (1 / ρ - 1)

/-- The CES wage `A(1 − a)[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
noncomputable def opCESwage (A a ρ k : ℝ) : ℝ := A * (1 - a) * opCESbase a ρ k ^ (1 / ρ - 1)

theorem op_ces_base_pos {a ρ k : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hk : 0 < k) :
    0 < opCESbase a ρ k ∧ 1 - a ≤ opCESbase a ρ k ∧ a * k ^ ρ ≤ opCESbase a ρ k := by
  have := Real.rpow_pos_of_pos hk ρ
  unfold opCESbase
  refine ⟨by nlinarith, by nlinarith, by linarith⟩

/-- **Exercise 16.5**: `f′(k) = Aak^{ρ−1}[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
theorem ex_16_5_hasDerivAt {A a ρ k : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hρ : ρ ≠ 0)
    (hk : 0 < k) : HasDerivAt (opCES A a ρ) (opCESfp A a ρ k) k := by
  have hb : HasDerivAt (opCESbase a ρ) (a * (ρ * k ^ (ρ - 1))) k := by
    unfold opCESbase
    exact ((Real.hasDerivAt_rpow_const (p := ρ) (Or.inl hk.ne')).const_mul a).add_const _
  have hr := (hb.rpow_const (p := 1 / ρ)
    (Or.inl (op_ces_base_pos ha0 ha1 hk).1.ne')).const_mul A
  unfold opCES opCESfp
  convert hr using 1
  field_simp

/-- **Exercise 16.5**: the CES wage `w(k) = f(k) − kf′(k) = A(1 − a)[ak^ρ + 1 − a]^{1/ρ − 1}`. -/
theorem ex_16_5_wage {A a ρ k : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hk : 0 < k) :
    opWage (opCES A a ρ) (opCESfp A a ρ) k = opCESwage A a ρ k := by
  have hb := (op_ces_base_pos (ρ := ρ) ha0 ha1 hk).1
  have e1 : opCESbase a ρ k ^ (1 / ρ) = opCESbase a ρ k ^ (1 / ρ - 1) * opCESbase a ρ k := by
    rw [Real.rpow_sub_one hb.ne']; field_simp
  unfold opWage opCES opCESfp opCESwage
  rw [e1, show k * (A * a * k ^ (ρ - 1) * opCESbase a ρ k ^ (1 / ρ - 1)) =
    A * a * (k * k ^ (ρ - 1)) * opCESbase a ρ k ^ (1 / ρ - 1) by ring, ← op_rpow_eq_mul hk]
  unfold opCESbase
  ring

/-- **Exercise 16.5**: with log utility the law of motion is `k_{t+1} = βw(k_t)/((1 + β)g_n)`. -/
theorem ex_16_5_law {β A a ρ gn : ℝ} {k : ℕ → ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCES A a ρ) (opCESfp A a ρ) gn k ↔
      ∀ t, 0 < k t ∧ k (t + 1) = β / ((1 + β) * gn) * opCESwage A a ρ (k t) := by
  refine forall_congr' fun t => ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · rw [ex_16_5_wage ha0 ha1 h1] at h2
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)
  · rw [ex_16_5_wage ha0 ha1 h1]
    exact h2.trans (by unfold opLogSaving; simp only [zero_div, sub_zero]; field_simp)

/-- The CES wage is continuous on `(0, ∞)`. -/
theorem op_ces_wage_continuousOn {A a ρ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ContinuousOn (opCESwage A a ρ) (Set.Ioi 0) := by
  have hb : ContinuousOn (opCESbase a ρ) (Set.Ioi 0) := by
    unfold opCESbase
    exact (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx =>
      Or.inl (ne_of_gt hx))).add continuousOn_const
  unfold opCESwage
  exact continuousOn_const.mul (hb.rpow_const fun x hx =>
    Or.inl (op_ces_base_pos ha0 ha1 hx).1.ne')

/-- **Exercise 16.5(a)** (Miao, p. 557): for `σ > 1` (`0 < ρ < 1`) there is a positive steady
state `k = βw(k)/((1 + β)g_n)`. -/
theorem ex_16_5_a {β A a ρ gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hgn : 0 < gn) :
    ∃ k, 0 < k ∧ k = β / ((1 + β) * gn) * opCESwage A a ρ k := by
  set c := β / ((1 + β) * gn) with hc
  have hc0 : 0 < c := by positivity
  have he : 0 < 1 / ρ - 1 := by
    have : 1 < 1 / ρ := by rw [lt_div_iff₀ hρ0]; linarith
    linarith
  have h1a : 0 < 1 - a := by linarith
  set W0 := A * (1 - a) * (1 - a) ^ (1 / ρ - 1) with hW0
  have hW00 : 0 < W0 := by have := Real.rpow_pos_of_pos h1a (1 / ρ - 1); positivity
  have hlow : ∀ k, 0 < k → W0 ≤ opCESwage A a ρ k := by
    intro k hk
    have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk
    have := Real.rpow_le_rpow h1a.le hb.2.1 he.le
    unfold opCESwage
    rw [hW0]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hup : ∀ k, 1 ≤ k → opCESwage A a ρ k ≤ A * (1 - a) * (k / k ^ ρ) := by
    intro k hk
    have hk0 : 0 < k := by linarith
    have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk0
    have hkρ : 1 ≤ k ^ ρ := Real.one_le_rpow hk hρ0.le
    have hbase : opCESbase a ρ k ≤ k ^ ρ := by unfold opCESbase; nlinarith
    have h1 := Real.rpow_le_rpow hb.1.le hbase he.le
    rw [← Real.rpow_mul hk0.le, show ρ * (1 / ρ - 1) = 1 - ρ by field_simp,
      Real.rpow_sub hk0, Real.rpow_one] at h1
    unfold opCESwage
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  set C := c * (A * (1 - a)) with hC
  have hC0 : 0 < C := by positivity
  set khi := max 1 ((C + 1) ^ ρ⁻¹) with hkhi
  have hkhi1 : 1 ≤ khi := le_max_left _ _
  have hkhi0 : 0 < khi := by linarith
  have hkhiρ : C + 1 ≤ khi ^ ρ := by
    have := Real.rpow_le_rpow (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < C + 1) _).le
      (le_max_right 1 ((C + 1) ^ ρ⁻¹)) hρ0.le
    rwa [Real.rpow_inv_rpow (by linarith) hρ0.ne'] at this
  have hφhi : c * opCESwage A a ρ khi < khi := by
    have h := mul_le_mul_of_nonneg_left (hup khi hkhi1) hc0.le
    have hkp : 0 < khi ^ ρ := by linarith
    have : C * (khi / khi ^ ρ) < khi := by
      rw [mul_div_assoc', div_lt_iff₀ hkp]; nlinarith
    rw [hC] at this
    linarith
  set klo := c * W0 / 2 with hklo
  have hklo0 : 0 < klo := by positivity
  have hφlo : klo < c * opCESwage A a ρ klo := by
    have := mul_le_mul_of_nonneg_left (hlow klo hklo0) hc0.le
    rw [hklo]; linarith
  set φ : ℝ → ℝ := fun k => c * opCESwage A a ρ k - k with hφ
  have hsub : Set.uIcc klo khi ⊆ Set.Ioi 0 := by
    intro x hx
    rcases Set.mem_uIcc.1 hx with h | h
    · exact lt_of_lt_of_le hklo0 h.1
    · exact lt_of_lt_of_le hkhi0 h.1
  have hcont : ContinuousOn φ (Set.uIcc klo khi) :=
    ((continuousOn_const.mul (op_ces_wage_continuousOn ha0 ha1)).sub continuousOn_id).mono hsub
  have h0 : (0 : ℝ) ∈ Set.uIcc (φ klo) (φ khi) :=
    Set.mem_uIcc.2 (Or.inr ⟨by simp only [hφ]; linarith, by simp only [hφ]; linarith⟩)
  obtain ⟨k, hk, hk0⟩ := intermediate_value_uIcc hcont h0
  refine ⟨k, hsub hk, ?_⟩
  simp only [hφ] at hk0
  linarith

/-- **Exercise 16.5(a)**, `σ = 1`: with Cobb–Douglas `f = Ak^a` the positive steady state is
`k* = [βA(1 − a)/((1 + β)g_n)]^{1/(1−a)}`. -/
theorem ex_16_5_a_cobbDouglas {β A a gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha1 : a < 1)
    (hgn : 0 < gn) :
    ∃ k, 0 < k ∧ k = β / ((1 + β) * gn) * opWage (opCD A a) (opCDfp A a) k := by
  have hc : 0 < β / ((1 + β) * gn) * ((1 - a) * A) := by
    have : 0 < 1 - a := by linarith
    positivity
  set k := opKstarCD (β / ((1 + β) * gn) * ((1 - a) * A)) a
  have hk : 0 < k := op_kstarCD_pos hc
  refine ⟨k, hk, ?_⟩
  rw [op_cd_wage hk]
  have := (op_cd_steady_iff hc ha1 hk).2 rfl
  linear_combination this

/-- The constant `M = (1 − a)·max(a^e, (1 − a)^e)`, `e = 1/ρ − 1`, of the bound for `σ < 1`. -/
noncomputable def opCESM (a ρ : ℝ) : ℝ :=
  (1 - a) * max (a ^ (1 / ρ - 1)) ((1 - a) ^ (1 / ρ - 1))

/-- For `ρ < 0`: `w(k) ≤ A(1 − a)a^e k^{1−ρ}` with `e = 1/ρ − 1`. -/
theorem op_ces_wage_le_small {A a ρ k : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hk : 0 < k) :
    opCESwage A a ρ k ≤ A * (1 - a) * a ^ (1 / ρ - 1) * (k * k ^ (-ρ)) := by
  have he : 1 / ρ - 1 ≤ 0 := by
    have : 1 / ρ < 0 := by rw [one_div]; exact inv_lt_zero.2 hρ
    linarith
  have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk
  have hakp : 0 < a * k ^ ρ := mul_pos ha0 (Real.rpow_pos_of_pos hk ρ)
  have hρne : ρ ≠ 0 := hρ.ne
  have h1 := Real.rpow_le_rpow_of_nonpos hakp hb.2.2 he
  rw [Real.mul_rpow ha0.le (Real.rpow_pos_of_pos hk ρ).le, ← Real.rpow_mul hk.le,
    show ρ * (1 / ρ - 1) = 1 + -ρ by field_simp; ring, Real.rpow_add hk, Real.rpow_one] at h1
  unfold opCESwage
  have h1a : 0 < 1 - a := by linarith
  calc A * (1 - a) * opCESbase a ρ k ^ (1 / ρ - 1)
      ≤ A * (1 - a) * (a ^ (1 / ρ - 1) * (k * k ^ (-ρ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = A * (1 - a) * a ^ (1 / ρ - 1) * (k * k ^ (-ρ)) := by ring

/-- For `ρ < 0`: `w(k) ≤ A(1 − a)^{1/ρ}`, a bound uniform in `k`. -/
theorem op_ces_wage_le_large {A a ρ k : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hk : 0 < k) :
    opCESwage A a ρ k ≤ A * (1 - a) * (1 - a) ^ (1 / ρ - 1) := by
  have he : 1 / ρ - 1 ≤ 0 := by
    have : 1 / ρ < 0 := by rw [one_div]; exact inv_lt_zero.2 hρ
    linarith
  have hb := op_ces_base_pos (ρ := ρ) ha0 ha1 hk
  have h1a : 0 < 1 - a := by linarith
  have h1 := Real.rpow_le_rpow_of_nonpos h1a hb.2.1 he
  unfold opCESwage
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Exercise 16.5(b)**: for `σ < 1` (`ρ < 0`), `w(k) ≤ AMk` for all `k > 0`, with
`M = opCESM a ρ > 0` independent of `A`. -/
theorem ex_16_5_b_bound {A a ρ : ℝ} (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1) (hρ : ρ < 0) :
    0 < opCESM a ρ ∧ ∀ k, 0 < k → opCESwage A a ρ k ≤ A * opCESM a ρ * k := by
  have h1a : 0 < 1 - a := by linarith
  have hM : 0 < opCESM a ρ := by
    unfold opCESM
    exact mul_pos h1a (lt_of_lt_of_le (Real.rpow_pos_of_pos ha0 _) (le_max_left _ _))
  refine ⟨hM, fun k hk => ?_⟩
  rcases le_total k 1 with hk1 | hk1
  · have h := op_ces_wage_le_small hA ha0 ha1 hρ hk
    have hkr : k ^ (-ρ) ≤ 1 := Real.rpow_le_one hk.le hk1 (by linarith)
    have hae : 0 < a ^ (1 / ρ - 1) := Real.rpow_pos_of_pos ha0 _
    have : A * (1 - a) * a ^ (1 / ρ - 1) * (k * k ^ (-ρ)) ≤
        A * (1 - a) * a ^ (1 / ρ - 1) * k := by
      have : k * k ^ (-ρ) ≤ k := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hmax : A * (1 - a) * a ^ (1 / ρ - 1) * k ≤ A * opCESM a ρ * k := by
      unfold opCESM
      have := le_max_left (a ^ (1 / ρ - 1)) ((1 - a) ^ (1 / ρ - 1))
      have : 0 ≤ A * (1 - a) * k := by positivity
      nlinarith
    linarith
  · have h := op_ces_wage_le_large hA ha0 ha1 hρ hk
    have hae : 0 < (1 - a) ^ (1 / ρ - 1) := Real.rpow_pos_of_pos h1a _
    have : A * (1 - a) * (1 - a) ^ (1 / ρ - 1) ≤ A * (1 - a) * (1 - a) ^ (1 / ρ - 1) * k := by
      have : 0 ≤ A * (1 - a) * (1 - a) ^ (1 / ρ - 1) := by positivity
      nlinarith
    have hmax : A * (1 - a) * (1 - a) ^ (1 / ρ - 1) * k ≤ A * opCESM a ρ * k := by
      unfold opCESM
      have := le_max_right (a ^ (1 / ρ - 1)) ((1 - a) ^ (1 / ρ - 1))
      have : 0 ≤ A * (1 - a) * k := by positivity
      nlinarith
    linarith

/-- **Exercise 16.5(b)** (Miao, p. 557): "for `A` sufficiently small, there is no positive steady
state": if `βAM < (1 + β)g_n` then `βw(k)/((1 + β)g_n) < k` for every `k > 0`. -/
theorem ex_16_5_b_none {β A a ρ gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hgn : 0 < gn) (hsmall : β / ((1 + β) * gn) * A * opCESM a ρ < 1) :
    ∀ k, 0 < k → β / ((1 + β) * gn) * opCESwage A a ρ k < k := by
  intro k hk
  have h := (ex_16_5_b_bound hA ha0 ha1 hρ).2 k hk
  have hc : 0 < β / ((1 + β) * gn) := by positivity
  have := mul_le_mul_of_nonneg_left h hc.le
  nlinarith

/-- **Exercise 16.5(b)**: with `A` small every equilibrium path collapses to `0`:
`k_t ≤ qᵗk₀` with `q = βAM/((1 + β)g_n) < 1`, so the zero steady state is globally stable. -/
theorem ex_16_5_b_collapse {β A a ρ gn : ℝ} {k : ℕ → ℝ} (hβ : 0 < β) (hA : 0 < A)
    (ha0 : 0 < a) (ha1 : a < 1) (hρ : ρ < 0) (hgn : 0 < gn)
    (hsmall : β / ((1 + β) * gn) * A * opCESM a ρ < 1)
    (h : OPIsDiamondEqm (fun w R => opLogSaving β w 0 R) (opCES A a ρ) (opCESfp A a ρ) gn k) :
    (∀ t, k t ≤ (β / ((1 + β) * gn) * A * opCESM a ρ) ^ t * k 0) ∧ Tendsto k atTop (𝓝 0) := by
  have hl := (ex_16_5_law ha0 ha1).1 h
  set q := β / ((1 + β) * gn) * A * opCESM a ρ with hq
  have hc : 0 < β / ((1 + β) * gn) := by positivity
  have hq0 : 0 < q := mul_pos (mul_pos hc hA) (ex_16_5_b_bound hA ha0 ha1 hρ).1
  have hstep : ∀ t, k (t + 1) ≤ q * k t := by
    intro t
    rw [(hl t).2]
    have := mul_le_mul_of_nonneg_left ((ex_16_5_b_bound hA ha0 ha1 hρ).2 _ (hl t).1) hc.le
    rw [hq]; linarith
  have hb : ∀ t, k t ≤ q ^ t * k 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc k (t + 1) ≤ q * k t := hstep t
        _ ≤ q * (q ^ t * k 0) := mul_le_mul_of_nonneg_left ih hq0.le
        _ = q ^ (t + 1) * k 0 := by ring
  refine ⟨hb, ?_⟩
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hsmall).mul_const (k 0)
  rw [zero_mul] at hz
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun t => (hl t).1.le) hb

/-- **Exercise 16.5(b)**: for `A` large (`βA(1 − a) > (1 + β)g_n`) there are at least two
positive steady states `k₁ < 1 < k₂`, so the steady state is not unique. -/
theorem ex_16_5_b_two {β A a ρ gn : ℝ} (hβ : 0 < β) (hA : 0 < A) (ha0 : 0 < a) (ha1 : a < 1)
    (hρ : ρ < 0) (hgn : 0 < gn) (hlarge : 1 < β / ((1 + β) * gn) * (A * (1 - a))) :
    ∃ k1 k2, 0 < k1 ∧ k1 < 1 ∧ 1 < k2 ∧
      k1 = β / ((1 + β) * gn) * opCESwage A a ρ k1 ∧
      k2 = β / ((1 + β) * gn) * opCESwage A a ρ k2 := by
  set c := β / ((1 + β) * gn) with hc
  have hc0 : 0 < c := by positivity
  have h1a : 0 < 1 - a := by linarith
  set φ : ℝ → ℝ := fun k => c * opCESwage A a ρ k - k with hφ
  have hcont : ContinuousOn φ (Set.Ioi 0) :=
    (continuousOn_const.mul (op_ces_wage_continuousOn ha0 ha1)).sub continuousOn_id
  -- `φ(1) > 0`
  have hφ1 : 0 < φ 1 := by
    simp only [hφ, opCESwage, opCESbase, Real.one_rpow, mul_one]
    rw [show a + (1 - a) = 1 by ring, Real.one_rpow, mul_one]
    linarith
  -- small `k`
  set B := c * (A * (1 - a) * a ^ (1 / ρ - 1)) with hB
  have hB0 : 0 < B := by have := Real.rpow_pos_of_pos ha0 (1 / ρ - 1); positivity
  have hnρ : 0 < -ρ := by linarith
  set klo := min (1 / 2) ((1 / (2 * B)) ^ (-ρ)⁻¹) with hklo
  have hklo0 : 0 < klo := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hklo1 : klo < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hkr : klo ^ (-ρ) ≤ 1 / (2 * B) := by
    have := Real.rpow_le_rpow hklo0.le (min_le_right (1 / 2) ((1 / (2 * B)) ^ (-ρ)⁻¹))
      hnρ.le
    rwa [Real.rpow_inv_rpow (by positivity) hnρ.ne'] at this
  have hφlo : φ klo < 0 := by
    have h := mul_le_mul_of_nonneg_left (op_ces_wage_le_small hA ha0 ha1 hρ hklo0) hc0.le
    have : c * (A * (1 - a) * a ^ (1 / ρ - 1) * (klo * klo ^ (-ρ))) = B * klo * klo ^ (-ρ) := by
      rw [hB]; ring
    have hk2 : B * klo * klo ^ (-ρ) ≤ klo / 2 := by
      have := mul_le_mul_of_nonneg_left hkr (by positivity : 0 ≤ B * klo)
      have e : B * klo * (1 / (2 * B)) = klo / 2 := by field_simp
      linarith
    simp only [hφ]
    linarith
  -- large `k`
  set W1 := A * (1 - a) * (1 - a) ^ (1 / ρ - 1) with hW1
  set khi := max 2 (c * W1 + 1) with hkhi
  have hkhi1 : 1 < khi := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hφhi : φ khi < 0 := by
    have h := mul_le_mul_of_nonneg_left (op_ces_wage_le_large hA ha0 ha1 hρ
      (by linarith : (0 : ℝ) < khi)) hc0.le
    have : c * W1 + 1 ≤ khi := le_max_right _ _
    simp only [hφ]
    rw [hW1] at this
    linarith
  obtain ⟨k1, hk1, hk1e⟩ := intermediate_value_Ioo hklo1.le
    (hcont.mono fun x hx => lt_of_lt_of_le hklo0 hx.1) ⟨hφlo, hφ1⟩
  obtain ⟨k2, hk2, hk2e⟩ := intermediate_value_Ioo' hkhi1.le
    (hcont.mono fun x hx => lt_of_lt_of_le one_pos hx.1) ⟨hφhi, hφ1⟩
  refine ⟨k1, k2, lt_trans hklo0 hk1.1, hk1.2, hk2.1, ?_, ?_⟩
  · simp only [hφ] at hk1e; linarith
  · simp only [hφ] at hk2e; linarith

end Miao.OverlappingGenerations

set_option linter.style.longLine false
#print axioms Miao.OverlappingGenerations.IsSolution
#print axioms Miao.OverlappingGenerations.IsRegular
#print axioms Miao.OverlappingGenerations.EventuallyConst
#print axioms Miao.OverlappingGenerations.IsStableSeq
#print axioms Miao.OverlappingGenerations.IsSteadyStateOf
#print axioms Miao.OverlappingGenerations.IsAsympStable
#print axioms Miao.OverlappingGenerations.basin
#print axioms Miao.OverlappingGenerations.IsGloballyStable
#print axioms Miao.OverlappingGenerations.IsStableMatrix
#print axioms Miao.OverlappingGenerations.isGloballyStable_iff_basin
#print axioms Miao.OverlappingGenerations.isAsympStable_iff_basin
#print axioms Miao.OverlappingGenerations.isStableSeq_iff_bddAbove
#print axioms Miao.OverlappingGenerations.IsScalarSol
#print axioms Miao.OverlappingGenerations.BddSeq
#print axioms Miao.OverlappingGenerations.bddSeq_iff_isStableSeq
#print axioms Miao.OverlappingGenerations.bddSeq_of_tendsto
#print axioms Miao.OverlappingGenerations.BddSeq.exists_nonneg
#print axioms Miao.OverlappingGenerations.geom_eq
#print axioms Miao.OverlappingGenerations.abs_pow_mul_tendsto_atTop
#print axioms Miao.OverlappingGenerations.pow_mul_tendsto_zero_iff
#print axioms Miao.OverlappingGenerations.geom_bdd_iff
#print axioms Miao.OverlappingGenerations.pow_mul_tendsto_zero_of_bdd
#print axioms Miao.OverlappingGenerations.bddSeq_of_forced
#print axioms Miao.OverlappingGenerations.tendsto_zero_of_forced
#print axioms Miao.OverlappingGenerations.eq_1_2_steady_state
#print axioms Miao.OverlappingGenerations.eq_1_2_no_steady_state_of_b_one
#print axioms Miao.OverlappingGenerations.eq_1_3
#print axioms Miao.OverlappingGenerations.eq_1_3_globallyStable
#print axioms Miao.OverlappingGenerations.eq_1_3_tendsto
#print axioms Miao.OverlappingGenerations.eq_1_3_diverges
#print axioms Miao.OverlappingGenerations.eq_1_3_bdd_iff
#print axioms Miao.OverlappingGenerations.eq_1_4
#print axioms Miao.OverlappingGenerations.not_tendsto_neg_one_pow
#print axioms Miao.OverlappingGenerations.eq_1_5_counterexample
#print axioms Miao.OverlappingGenerations.eq_1_5_tendsto
#print axioms Miao.OverlappingGenerations.eq_1_5_bdd
#print axioms Miao.OverlappingGenerations.eq_1_5_sub_tendsto
#print axioms Miao.OverlappingGenerations.eq_1_5_b_one_formula
#print axioms Miao.OverlappingGenerations.eq_1_5_b_one_tendsto_iff
#print axioms Miao.OverlappingGenerations.eq_1_5_b_one_limit_sub
#print axioms Miao.OverlappingGenerations.eq_1_5_b_neg_one_counterexample
#print axioms Miao.OverlappingGenerations.eq_1_5_b_neg_one_unique
#print axioms Miao.OverlappingGenerations.eq_1_6
#print axioms Miao.OverlappingGenerations.fwdSol
#print axioms Miao.OverlappingGenerations.abs_one_div_lt_one
#print axioms Miao.OverlappingGenerations.eq_1_8_summable
#print axioms Miao.OverlappingGenerations.eq_1_8_isScalarSol
#print axioms Miao.OverlappingGenerations.eq_1_8_bdd
#print axioms Miao.OverlappingGenerations.eq_1_7_of_bdd
#print axioms Miao.OverlappingGenerations.eq_1_8_transversality
#print axioms Miao.OverlappingGenerations.eq_1_8_unique_of_transversality
#print axioms Miao.OverlappingGenerations.eq_1_8_unique_bdd
#print axioms Miao.OverlappingGenerations.eq_1_8
#print axioms Miao.OverlappingGenerations.eq_1_9
#print axioms Miao.OverlappingGenerations.eq_1_9_every_solution
#print axioms Miao.OverlappingGenerations.eq_1_8_others_diverge
#print axioms Miao.OverlappingGenerations.eq_1_8_not_summable
#print axioms Miao.OverlappingGenerations.eq_1_9_bubble_stable
#print axioms Miao.OverlappingGenerations.example_1_1_1_recursion
#print axioms Miao.OverlappingGenerations.example_1_1_1_backward
#print axioms Miao.OverlappingGenerations.example_1_1_1_tendsto_iff
#print axioms Miao.OverlappingGenerations.example_1_1_1_abs_a_lt_one_iff
#print axioms Miao.OverlappingGenerations.example_1_1_1_forward
#print axioms Miao.OverlappingGenerations.example_1_1_1_forward_limit
#print axioms Miao.OverlappingGenerations.example_1_1_1_isScalarSol
#print axioms Miao.OverlappingGenerations.example_1_1_1_bubbles
#print axioms Miao.OverlappingGenerations.example_1_1_1_unique_bdd
#print axioms Miao.OverlappingGenerations.divTax
#print axioms Miao.OverlappingGenerations.taxPath
#print axioms Miao.OverlappingGenerations.sum_div_pow_eq
#print axioms Miao.OverlappingGenerations.example_1_1_2_p0_forward
#print axioms Miao.OverlappingGenerations.example_1_1_2_pT
#print axioms Miao.OverlappingGenerations.example_1_1_2_p0
#print axioms Miao.OverlappingGenerations.example_1_1_2_solves
#print axioms Miao.OverlappingGenerations.example_1_1_2_const
#print axioms Miao.OverlappingGenerations.example_1_1_2_unique
#print axioms Miao.OverlappingGenerations.example_1_1_2_drop
#print axioms Miao.OverlappingGenerations.example_1_1_2_decreasing
#print axioms Miao.OverlappingGenerations.IsSol22
#print axioms Miao.OverlappingGenerations.cp22
#print axioms Miao.OverlappingGenerations.disc22
#print axioms Miao.OverlappingGenerations.lamLo
#print axioms Miao.OverlappingGenerations.lamHi
#print axioms Miao.OverlappingGenerations.sVar
#print axioms Miao.OverlappingGenerations.disc22_pos
#print axioms Miao.OverlappingGenerations.cp22_factor
#print axioms Miao.OverlappingGenerations.cp22_lamLo
#print axioms Miao.OverlappingGenerations.cp22_lamHi
#print axioms Miao.OverlappingGenerations.lamLo_lt_lamHi
#print axioms Miao.OverlappingGenerations.roots22_lt
#print axioms Miao.OverlappingGenerations.lamLo_gt_neg_one_iff
#print axioms Miao.OverlappingGenerations.abs_lamLo_lt_one_iff
#print axioms Miao.OverlappingGenerations.lamLo_lt_m11
#print axioms Miao.OverlappingGenerations.sVar_step
#print axioms Miao.OverlappingGenerations.sVar_succ
#print axioms Miao.OverlappingGenerations.recover22
#print axioms Miao.OverlappingGenerations.IsSol22.ext
#print axioms Miao.OverlappingGenerations.bddSeq_lin
#print axioms Miao.OverlappingGenerations.sHi_zero_of_bdd
#print axioms Miao.OverlappingGenerations.kSaddle
#print axioms Miao.OverlappingGenerations.sHi_zero_iff
#print axioms Miao.OverlappingGenerations.saddle22
#print axioms Miao.OverlappingGenerations.saddle22_tendsto
#print axioms Miao.OverlappingGenerations.saddle22_unique
#print axioms Miao.OverlappingGenerations.saddle22_unbounded
#print axioms Miao.OverlappingGenerations.sVar_tendsto
#print axioms Miao.OverlappingGenerations.saddle22_iff
#print axioms Miao.OverlappingGenerations.saddle22_only_zero
#print axioms Miao.OverlappingGenerations.IsPhaseSol
#print axioms Miao.OverlappingGenerations.phaseIter
#print axioms Miao.OverlappingGenerations.phaseIter_sol
#print axioms Miao.OverlappingGenerations.phase_tilde
#print axioms Miao.OverlappingGenerations.phase_delta
#print axioms Miao.OverlappingGenerations.phase_isocline_x
#print axioms Miao.OverlappingGenerations.phase_isocline_y
#print axioms Miao.OverlappingGenerations.phase_steady_state
#print axioms Miao.OverlappingGenerations.bddSeq_sub_const
#print axioms Miao.OverlappingGenerations.phase_dev
#print axioms Miao.OverlappingGenerations.phase_cp_one
#print axioms Miao.OverlappingGenerations.phase_cp_neg_one
#print axioms Miao.OverlappingGenerations.phase_roots
#print axioms Miao.OverlappingGenerations.phase_lamLo_iff
#print axioms Miao.OverlappingGenerations.phase_saddle
#print axioms Miao.OverlappingGenerations.phase_saddle_slope
#print axioms Miao.OverlappingGenerations.phase_saddle_iff
#print axioms Miao.OverlappingGenerations.phase_counterexample
#print axioms Miao.OverlappingGenerations.OXPrefs
#print axioms Miao.OverlappingGenerations.OXPrefs.mk
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_u
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_du
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_β
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_β_pos
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_β_le
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_hasDeriv
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_du_pos
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_du_anti
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_du_cont
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_inada
#print axioms Miao.OverlappingGenerations.ox_logPrefs
#print axioms Miao.OverlappingGenerations.ox_logPrefs_spec
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_U
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_tangent_strict
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_tangent
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_u_strictMonoOn
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_u_lt
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_du_lt
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_chord
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_eventually_pos
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_foc
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_line_optimal
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_line_optimal_strict
#print axioms Miao.OverlappingGenerations.OXEconomy
#print axioms Miao.OverlappingGenerations.OXEconomy.mk
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_P
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_e1
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_e2
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_gn
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_gm
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_N0
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_M0
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_e1_pos
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_e2_pos
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_gn_pos
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_gm_pos
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_N0_pos
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_M0_pos
#print axioms Miao.OverlappingGenerations.ox_exampleEconomy
#print axioms Miao.OverlappingGenerations.ox_exampleEconomy_spec
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_N
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_M
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_τ
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_EU
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_Raut
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_Budget
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_Optimal
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_oldBudget
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_OldOptimal
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_IsEquilibrium
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_IsMonetary
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_IsNonmonetary
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_mhat
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_N_pos
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_M_pos
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_N_succ
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_M_succ
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_1_16_2
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_oldOptimal_iff
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_optimal_binds
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_autarky_isEquilibrium
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_nonmonetary_autarky
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_mhat_eq
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_old_resources
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_oldBudget_eq
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_monetary_alloc
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_4
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_5
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_7
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_Raut_lt
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_6
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_EulerRel
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_qOf
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_mhat_qOf
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_budget_line
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_ofSaving_isMonetary
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_monetary_eulerRel
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_8
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_1_necessity
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_1_limit
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_1_root
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_eulerRel_const_iff
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_1_sufficiency
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_1
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_1_unique_stationary
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_stationary_R
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_offer_z
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_offer_lt_e1
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_offer_equilibrium
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_offer_slope_m
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_offer_slope_m_eq
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_offer_slope_z
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_offer_slope_z_pos
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_offer_backward_iff
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_offer_backward_necessary
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_offer_upward
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_offer_origin
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_offer_slope_origin
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_offer_steady_iff
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_offer_steady_exists_iff
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_R_tendsto_Raut
#print axioms Miao.OverlappingGenerations.ox_fixed_stable
#print axioms Miao.OverlappingGenerations.ox_fixed_unstable
#print axioms Miao.OverlappingGenerations.ox_unstable_counterexample
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_indeterminacy
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_two_cycle
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_Feasible
#print axioms Miao.OverlappingGenerations.OXEconomy.definition_16_1_1
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_ParetoOptimal
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_IsStationary
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_12
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_feasible_old
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_11
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_eps_geometric
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_10
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_stationary_optimal
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_2_transfer
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_stationary_not_optimal
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_stationary_optimal_iff
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_2
#print axioms Miao.OverlappingGenerations.OXEconomy.eq_16_13
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_3_steps
#print axioms Miao.OverlappingGenerations.OXEconomy.proposition_16_1_3
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_balasko_shell_prod
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_balasko_shell_equiv
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_balasko_shell_transfers
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_balasko_shell_stationary
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_exampleEconomy_log
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_log_Raut
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_log_eulerRel
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_log_fixed
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_log_paths
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_log_construct
#print axioms Miao.OverlappingGenerations.OXEconomy.ox_log_tendsto
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_1_diffeq
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_1_general
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_1_construct
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_1_explosive
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_1_left
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_1_right
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_2_high
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_2_low
#print axioms Miao.OverlappingGenerations.OXEconomy.example_16_1_2_not_monetary
#print axioms Miao.OverlappingGenerations.OXEconomy.ex_16_1_a
#print axioms Miao.OverlappingGenerations.OXEconomy.ex_16_1_b_exists
#print axioms Miao.OverlappingGenerations.OXEconomy.ex_16_1_b_values
#print axioms Miao.OverlappingGenerations.OXEconomy.ex_16_1_b_rank
#print axioms Miao.OverlappingGenerations.OXEconomy.ex_16_1_b_autarky
#print axioms Miao.OverlappingGenerations.OXEconomy.ex_16_1_c
#print axioms Miao.OverlappingGenerations.OXEconomy.ex_16_1_c_exist
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_TreeBudget
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_TreeOptimal
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_TreeEquilibrium
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_tree_binds
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_tree_price_pos
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_tree_foc
#print axioms Miao.OverlappingGenerations.OXPrefs.ex_16_2_a
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_astar
#print axioms Miao.OverlappingGenerations.OXPrefs.ox_astar_spec
#print axioms Miao.OverlappingGenerations.OXPrefs.ex_16_2_b_exists
#print axioms Miao.OverlappingGenerations.OXPrefs.ex_16_2_b_unique
#print axioms Miao.OverlappingGenerations.op_concave_tangent
#print axioms Miao.OverlappingGenerations.op_strictConcave_tangent
#print axioms Miao.OverlappingGenerations.op_lifetime_hasDerivAt
#print axioms Miao.OverlappingGenerations.op_euler_necessary
#print axioms Miao.OverlappingGenerations.op_euler_sufficient
#print axioms Miao.OverlappingGenerations.op_euler_sufficient_strict
#print axioms Miao.OverlappingGenerations.op_inada_small
#print axioms Miao.OverlappingGenerations.op_saving_exists
#print axioms Miao.OverlappingGenerations.op_saving_unique
#print axioms Miao.OverlappingGenerations.op_saving_wage_mono
#print axioms Miao.OverlappingGenerations.op_saving_sw
#print axioms Miao.OverlappingGenerations.opLogSaving
#print axioms Miao.OverlappingGenerations.op_log_saving
#print axioms Miao.OverlappingGenerations.opWage
#print axioms Miao.OverlappingGenerations.opRate
#print axioms Miao.OverlappingGenerations.op_F_hasDerivAt_K
#print axioms Miao.OverlappingGenerations.op_F_hasDerivAt_N
#print axioms Miao.OverlappingGenerations.eq_16_15
#print axioms Miao.OverlappingGenerations.eq_16_14
#print axioms Miao.OverlappingGenerations.op_euler_identity
#print axioms Miao.OverlappingGenerations.op_capital_market
#print axioms Miao.OverlappingGenerations.OPIsDiamondEqm
#print axioms Miao.OverlappingGenerations.eq_16_16
#print axioms Miao.OverlappingGenerations.op_diamondEqm_iff
#print axioms Miao.OverlappingGenerations.op_fp_strictAnti
#print axioms Miao.OverlappingGenerations.op_wage_pos
#print axioms Miao.OverlappingGenerations.op_wage_strictMono
#print axioms Miao.OverlappingGenerations.op_wage_lt
#print axioms Miao.OverlappingGenerations.op_wage_tendsto_zero
#print axioms Miao.OverlappingGenerations.op_wage_div_eq
#print axioms Miao.OverlappingGenerations.op_f_div_tendsto_zero
#print axioms Miao.OverlappingGenerations.op_wage_div_tendsto_zero
#print axioms Miao.OverlappingGenerations.op_temporary_eqm
#print axioms Miao.OverlappingGenerations.op_S_antitone
#print axioms Miao.OverlappingGenerations.op_G_exists
#print axioms Miao.OverlappingGenerations.op_G_strictMono
#print axioms Miao.OverlappingGenerations.op_G_lt_wage
#print axioms Miao.OverlappingGenerations.op_G_tendsto_zero
#print axioms Miao.OverlappingGenerations.op_G_div_tendsto_zero
#print axioms Miao.OverlappingGenerations.op_G_eventually_below
#print axioms Miao.OverlappingGenerations.op_wage_hasDerivAt
#print axioms Miao.OverlappingGenerations.op_G_slope
#print axioms Miao.OverlappingGenerations.op_G_slope_pos
#print axioms Miao.OverlappingGenerations.op_G_slope_steady
#print axioms Miao.OverlappingGenerations.op_ivt_up
#print axioms Miao.OverlappingGenerations.op_ivt_down
#print axioms Miao.OverlappingGenerations.op_slope_lt_one
#print axioms Miao.OverlappingGenerations.op_least_fixed
#print axioms Miao.OverlappingGenerations.op_fixed_below
#print axioms Miao.OverlappingGenerations.op_above_diag_of_deriv
#print axioms Miao.OverlappingGenerations.op_below_diag_of_deriv
#print axioms Miao.OverlappingGenerations.op_exists_fixed
#print axioms Miao.OverlappingGenerations.op_diamond_conditions
#print axioms Miao.OverlappingGenerations.op_diamond_conditions_printed
#print axioms Miao.OverlappingGenerations.op_fixed_signs
#print axioms Miao.OverlappingGenerations.op_global_convergence
#print axioms Miao.OverlappingGenerations.op_local_stability
#print axioms Miao.OverlappingGenerations.opOddG
#print axioms Miao.OverlappingGenerations.opEvenG
#print axioms Miao.OverlappingGenerations.op_strictMonoOn_max
#print axioms Miao.OverlappingGenerations.op_strictMonoOn_min
#print axioms Miao.OverlappingGenerations.op_sqrt_strictMonoOn
#print axioms Miao.OverlappingGenerations.op_three_sqrt_div_tendsto
#print axioms Miao.OverlappingGenerations.op_sqrt_four
#print axioms Miao.OverlappingGenerations.op_sqrt_nine
#print axioms Miao.OverlappingGenerations.op_oddG_props
#print axioms Miao.OverlappingGenerations.op_oddG_fixed
#print axioms Miao.OverlappingGenerations.op_odd_counterexample
#print axioms Miao.OverlappingGenerations.op_evenG_props
#print axioms Miao.OverlappingGenerations.op_evenG_fixed
#print axioms Miao.OverlappingGenerations.op_even_counterexample
#print axioms Miao.OverlappingGenerations.op_resource_per_worker
#print axioms Miao.OverlappingGenerations.eq_16_17
#print axioms Miao.OverlappingGenerations.op_golden_rule_max
#print axioms Miao.OverlappingGenerations.op_golden_rule_strict
#print axioms Miao.OverlappingGenerations.op_golden_rule_unique
#print axioms Miao.OverlappingGenerations.op_golden_rule_exists
#print axioms Miao.OverlappingGenerations.opLagrangian
#print axioms Miao.OverlappingGenerations.op_planner_lagrangian
#print axioms Miao.OverlappingGenerations.op_planner_foc
#print axioms Miao.OverlappingGenerations.op_planner_golden_rule
#print axioms Miao.OverlappingGenerations.op_planner_foc_printed
#print axioms Miao.OverlappingGenerations.OPFeasible
#print axioms Miao.OverlappingGenerations.OPParetoDominates
#print axioms Miao.OverlappingGenerations.op_steady_feasible
#print axioms Miao.OverlappingGenerations.op_dynamic_inefficiency
#print axioms Miao.OverlappingGenerations.op_pareto_optimal_of_lt_golden
#print axioms Miao.OverlappingGenerations.op_cass_steady_state
#print axioms Miao.OverlappingGenerations.op_cass_corollary
#print axioms Miao.OverlappingGenerations.eq_16_18
#print axioms Miao.OverlappingGenerations.eq_16_19
#print axioms Miao.OverlappingGenerations.OPIsBubbleEqm
#print axioms Miao.OverlappingGenerations.op_bubble_zero
#print axioms Miao.OverlappingGenerations.op_bubble_pos
#print axioms Miao.OverlappingGenerations.op_bubble_k_law
#print axioms Miao.OverlappingGenerations.op_bubbly_steady
#print axioms Miao.OverlappingGenerations.op_bubbly_steady_golden
#print axioms Miao.OverlappingGenerations.opKLocus
#print axioms Miao.OverlappingGenerations.op_k_locus
#print axioms Miao.OverlappingGenerations.op_kLocus_zero_iff
#print axioms Miao.OverlappingGenerations.op_S_vs_G
#print axioms Miao.OverlappingGenerations.op_kLocus_pos
#print axioms Miao.OverlappingGenerations.op_kLocus_neg
#print axioms Miao.OverlappingGenerations.op_kLocus_hasDerivAt
#print axioms Miao.OverlappingGenerations.op_kLocus_slope_printed
#print axioms Miao.OverlappingGenerations.op_kLocus_slope_neg
#print axioms Miao.OverlappingGenerations.op_k_increase_iff
#print axioms Miao.OverlappingGenerations.op_k_decrease_iff
#print axioms Miao.OverlappingGenerations.op_k_stationary_iff
#print axioms Miao.OverlappingGenerations.op_b_diff
#print axioms Miao.OverlappingGenerations.op_b_increase_iff
#print axioms Miao.OverlappingGenerations.op_b_stationary_iff
#print axioms Miao.OverlappingGenerations.op_bubbly_exists_iff
#print axioms Miao.OverlappingGenerations.opCD
#print axioms Miao.OverlappingGenerations.opCDfp
#print axioms Miao.OverlappingGenerations.op_cd_hasDerivAt
#print axioms Miao.OverlappingGenerations.op_cd_wage
#print axioms Miao.OverlappingGenerations.op_rpow_eq_mul
#print axioms Miao.OverlappingGenerations.opKstarCD
#print axioms Miao.OverlappingGenerations.op_kstarCD_pos
#print axioms Miao.OverlappingGenerations.op_cd_steady_iff
#print axioms Miao.OverlappingGenerations.op_cd_converge
#print axioms Miao.OverlappingGenerations.opCRRASaving
#print axioms Miao.OverlappingGenerations.op_crra_hasDerivAt
#print axioms Miao.OverlappingGenerations.op_crra_strictConcave
#print axioms Miao.OverlappingGenerations.ex_16_3_euler
#print axioms Miao.OverlappingGenerations.ex_16_3_optimal
#print axioms Miao.OverlappingGenerations.ex_16_3_mono_lt
#print axioms Miao.OverlappingGenerations.ex_16_3_anti_gt
#print axioms Miao.OverlappingGenerations.ex_16_3_gamma_one
#print axioms Miao.OverlappingGenerations.ex_16_3_law
#print axioms Miao.OverlappingGenerations.ex_16_4_law
#print axioms Miao.OverlappingGenerations.ex_16_4_steady
#print axioms Miao.OverlappingGenerations.ex_16_4_converge
#print axioms Miao.OverlappingGenerations.ex_16_4_mpk
#print axioms Miao.OverlappingGenerations.ex_16_4_inefficient
#print axioms Miao.OverlappingGenerations.ex_16_4_efficient
#print axioms Miao.OverlappingGenerations.OPIsDiamondEqmDep
#print axioms Miao.OverlappingGenerations.ex_16_6_rate
#print axioms Miao.OverlappingGenerations.ex_16_6_full
#print axioms Miao.OverlappingGenerations.ex_16_6_log
#print axioms Miao.OverlappingGenerations.ex_16_7_a
#print axioms Miao.OverlappingGenerations.ex_16_7_b
#print axioms Miao.OverlappingGenerations.ex_16_7_bc_path
#print axioms Miao.OverlappingGenerations.ex_16_8_a_i
#print axioms Miao.OverlappingGenerations.ex_16_8_a_ii
#print axioms Miao.OverlappingGenerations.opPAYGWelfare
#print axioms Miao.OverlappingGenerations.ex_16_8_a_iii
#print axioms Miao.OverlappingGenerations.ex_16_8_a_iii_resources
#print axioms Miao.OverlappingGenerations.ex_16_8_b
#print axioms Miao.OverlappingGenerations.opLinM11
#print axioms Miao.OverlappingGenerations.opLinM12
#print axioms Miao.OverlappingGenerations.opLinM21
#print axioms Miao.OverlappingGenerations.ex_16_9_linearization
#print axioms Miao.OverlappingGenerations.ex_16_9_roots
#print axioms Miao.OverlappingGenerations.ex_16_9_saddle
#print axioms Miao.OverlappingGenerations.opCESbase
#print axioms Miao.OverlappingGenerations.opCES
#print axioms Miao.OverlappingGenerations.opCESfp
#print axioms Miao.OverlappingGenerations.opCESwage
#print axioms Miao.OverlappingGenerations.op_ces_base_pos
#print axioms Miao.OverlappingGenerations.ex_16_5_hasDerivAt
#print axioms Miao.OverlappingGenerations.ex_16_5_wage
#print axioms Miao.OverlappingGenerations.ex_16_5_law
#print axioms Miao.OverlappingGenerations.op_ces_wage_continuousOn
#print axioms Miao.OverlappingGenerations.ex_16_5_a
#print axioms Miao.OverlappingGenerations.ex_16_5_a_cobbDouglas
#print axioms Miao.OverlappingGenerations.opCESM
#print axioms Miao.OverlappingGenerations.op_ces_wage_le_small
#print axioms Miao.OverlappingGenerations.op_ces_wage_le_large
#print axioms Miao.OverlappingGenerations.ex_16_5_b_bound
#print axioms Miao.OverlappingGenerations.ex_16_5_b_none
#print axioms Miao.OverlappingGenerations.ex_16_5_b_collapse
#print axioms Miao.OverlappingGenerations.ex_16_5_b_two
