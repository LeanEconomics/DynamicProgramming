import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Dynamics.PeriodicPts.Defs
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Definitions of Chapter 1

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

namespace Miao.DifferenceEquations

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

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Scalar first-order linear equations

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

namespace Miao.DifferenceEquations

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

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Lag operators (scalar case)

Miao, §1.2, pp. 10–12, for two-sided real sequences `X : ℤ → ℝ`.

* The lag operator `lagOp n X = Lⁿ X`, `(LⁿX)_t = X_{t−n}` for every integer `n`, with
  `Lᵐ Lⁿ = L^{m+n}` (`lagOp_lagOp`), `L⁰ = id` (`lagOp_zero`), `Lⁿ = (L¹)ⁿ` for `n ∈ ℕ`
  (`lagOp_iterate`), `L⁻ⁿLⁿ = id` (`lagOp_neg_lagOp`) and `Lⁿ c = c` (`lagOp_const`).
* `1/(1 − λLⁿ) = Σ λʲ L^{nj}` (`lag_inverse_geom`): for `|λ| < 1` and bounded `X`,
  `Y_t = Σ_j λʲ X_{t−nj}` (`geomLagSum`) is bounded, solves `Y − λLⁿY = X`, and is the unique
  bounded solution.
* `1/(1 − λLⁿ)² = Σ (j + 1)λʲ L^{nj}` (`lag_inverse_geom_sq`): `Y_t = Σ_j (j+1)λʲ X_{t−nj}`
  (`geomLagSum2`) is the unique bounded solution of `(1 − λLⁿ)²Y = X`.
* The scalar identities `1/(1 − λ) = Σ λʲ` and `1/(1 − λ)² = Σ (j + 1)λʲ`
  (`lag_scalar_geom`, `lag_scalar_geom_sq`).

The book states the operator identities formally; here they are made precise as statements
about the unique bounded solution, which is how they are used. The integer `n` is arbitrary
(`n < 0` gives lead operators, `n = 0` gives `Y = X/(1 − λ)`).
The matrix version `(I − ALⁿ)⁻¹ = Σ Aʲ L^{nj}` is not in this module.
-/

open Filter Topology

namespace Miao.DifferenceEquations

/-- The lag operator `Lⁿ` (Miao, p. 11): `(LⁿX)_t = X_{t−n}` for `n ∈ ℤ`. -/
def lagOp (n : ℤ) (X : ℤ → ℝ) : ℤ → ℝ :=
  fun t => X (t - n)

/-- A two-sided real sequence is bounded. -/
def BddZSeq (X : ℤ → ℝ) : Prop :=
  ∃ M, ∀ t, |X t| ≤ M

/-- Miao, p. 11: `Lᵐ(LⁿX) = L^{m+n}X`. -/
theorem lagOp_lagOp (m n : ℤ) (X : ℤ → ℝ) : lagOp m (lagOp n X) = lagOp (m + n) X := by
  ext t; simp only [lagOp]; congr 1; ring

/-- Miao, p. 11: `L⁰X = X`. -/
theorem lagOp_zero (X : ℤ → ℝ) : lagOp 0 X = X := by
  ext t; simp [lagOp]

/-- Miao, p. 11: `Lⁿ` is the `n`-th power of `L = L¹` for `n ∈ ℕ`. -/
theorem lagOp_iterate (n : ℕ) (X : ℤ → ℝ) : (lagOp 1)^[n] X = lagOp n X := by
  induction n with
  | zero => simp [lagOp_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, lagOp_lagOp]
    push_cast; ring_nf

/-- Miao, p. 11: `L⁻ⁿ` inverts `Lⁿ`. -/
theorem lagOp_neg_lagOp (n : ℤ) (X : ℤ → ℝ) : lagOp (-n) (lagOp n X) = X := by
  rw [lagOp_lagOp, neg_add_cancel, lagOp_zero]

/-- Miao, p. 11: `Lⁿ c = c` for a constant sequence. -/
theorem lagOp_const (n : ℤ) (c : ℝ) : lagOp n (fun _ => c) = fun _ => c := rfl

/-- The operator `1 − λLⁿ`: `((1 − λLⁿ)Y)_t = Y_t − λ Y_{t−n}`. -/
def oneSubLag (lam : ℝ) (n : ℤ) (Y : ℤ → ℝ) : ℤ → ℝ :=
  fun t => Y t - lam * lagOp n Y t

/-- `Y_t = Σ_j λʲ (L^{nj}X)_t = Σ_j λʲ X_{t−nj}`, the right side of `1/(1 − λLⁿ) = Σ λʲL^{nj}`
(Miao, p. 11). -/
noncomputable def geomLagSum (lam : ℝ) (n : ℤ) (X : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑' j : ℕ, lam ^ j * lagOp (n * j) X t

/-- `Y_t = Σ_j (j + 1)λʲ X_{t−nj}`, the right side of `1/(1 − λLⁿ)² = Σ (j+1)λʲL^{nj}`
(Miao, p. 11). -/
noncomputable def geomLagSum2 (lam : ℝ) (n : ℤ) (X : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑' j : ℕ, ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X t

theorem summable_of_abs_le {f g : ℕ → ℝ} {M : ℝ} (hg : Summable g) (h : ∀ j, |f j| ≤ M * g j) :
    Summable f :=
  Summable.of_norm_bounded (hg.mul_left M) (fun j => by rw [Real.norm_eq_abs]; exact h j)

theorem abs_tsum_le_of_abs_le {f g : ℕ → ℝ} {M : ℝ} (hg : Summable g)
    (h : ∀ j, |f j| ≤ M * g j) : |∑' j, f j| ≤ M * ∑' j, g j := by
  have hs : Summable (fun j => |f j|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) h (hg.mul_left M)
  calc |∑' j, f j| ≤ ∑' j, |f j| := by
        simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := f)
          (by simpa [Real.norm_eq_abs] using hs)
    _ ≤ ∑' j, M * g j := hs.tsum_le_tsum h (hg.mul_left M)
    _ = M * ∑' j, g j := tsum_mul_left

theorem summable_succ_mul_geom {r : ℝ} (hr : |r| < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) * r ^ j) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by rwa [Real.norm_eq_abs])
  have h2 := summable_geometric_of_abs_lt_one hr
  refine (h1.add h2).congr (fun j => ?_)
  simp only [pow_one]; ring

theorem abs_lagOp_le {X : ℤ → ℝ} {M : ℝ} (hX : ∀ t, |X t| ≤ M) (n t : ℤ) :
    |lagOp n X t| ≤ M := hX _

/-- Summability of the series in `geomLagSum`. -/
theorem geomLagSum_summable {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n t : ℤ) :
    Summable (fun j : ℕ => lam ^ j * lagOp (n * j) X t) := by
  obtain ⟨M, hM⟩ := hX
  refine summable_of_abs_le (M := M) (summable_geometric_of_lt_one (abs_nonneg _) hl)
    (fun j => ?_)
  rw [abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

/-- Summability of the series in `geomLagSum2`. -/
theorem geomLagSum2_summable {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X)
    (n t : ℤ) : Summable (fun j : ℕ => ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X t) := by
  obtain ⟨M, hM⟩ := hX
  refine summable_of_abs_le (M := M) (summable_succ_mul_geom (r := |lam|) (by simpa using hl))
    (fun j => ?_)
  rw [abs_mul, abs_mul, abs_pow, mul_comm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1)]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

theorem geomLagSum_bdd {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n : ℤ) :
    BddZSeq (geomLagSum lam n X) := by
  obtain ⟨M, hM⟩ := hX
  refine ⟨M * ∑' j : ℕ, |lam| ^ j, fun t => ?_⟩
  refine abs_tsum_le_of_abs_le (summable_geometric_of_lt_one (abs_nonneg _) hl) (fun j => ?_)
  rw [abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

theorem geomLagSum2_bdd {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n : ℤ) :
    BddZSeq (geomLagSum2 lam n X) := by
  obtain ⟨M, hM⟩ := hX
  refine ⟨M * ∑' j : ℕ, ((j : ℝ) + 1) * |lam| ^ j, fun t => ?_⟩
  refine abs_tsum_le_of_abs_le (summable_succ_mul_geom (r := |lam|) (by simpa using hl))
    (fun j => ?_)
  rw [abs_mul, abs_mul, abs_pow, mul_comm, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j + 1)]
  exact mul_le_mul_of_nonneg_right (abs_lagOp_le hM _ _) (by positivity)

/-- The first term and the shifted tail of `geomLagSum`:
`Y_t = X_t + λ Y_{t−n}`. -/
theorem geomLagSum_eq {lam : ℝ} (hl : |lam| < 1) {X : ℤ → ℝ} (hX : BddZSeq X) (n t : ℤ) :
    geomLagSum lam n X t = X t + lam * geomLagSum lam n X (t - n) := by
  simp only [geomLagSum]
  rw [(geomLagSum_summable hl hX n t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [lagOp, pow_zero, one_mul, Nat.cast_zero, mul_zero, sub_zero]
  congr 1
  congr 1; ext j
  rw [pow_succ]
  push_cast
  rw [show t - n * ((j : ℤ) + 1) = t - n - n * j by ring]
  ring

/-- Uniqueness: a bounded `D` with `D_t = λ D_{t−n}`, `|λ| < 1`, is zero. -/
theorem eq_zero_of_bdd_of_lag {lam : ℝ} (hl : |lam| < 1) {n : ℤ} {D : ℤ → ℝ} (hD : BddZSeq D)
    (h : ∀ t, D t = lam * D (t - n)) : D = 0 := by
  obtain ⟨M, hM⟩ := hD
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have key : ∀ (k : ℕ) t, D t = lam ^ k * D (t - n * k) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [ih t, h (t - n * k), pow_succ]
      push_cast
      rw [show t - n * k - n = t - n * (k + 1) by ring]
      ring
  ext t
  have hle : ∀ k : ℕ, |D t| ≤ |lam| ^ k * M := fun k => by
    rw [key k t, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _) (by positivity)
  have hlim : Tendsto (fun k : ℕ => |lam| ^ k * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg lam) hl).mul_const M
  have := ge_of_tendsto' hlim hle
  simpa using abs_nonpos_iff.1 this

/-- **Lag-operator expansion** (Miao, p. 11): `1/(1 − λLⁿ) = Σ_{j≥0} λʲ L^{nj}` for `|λ| < 1`.
For bounded `X`, `Y = Σ λʲ L^{nj} X` is bounded, solves `(1 − λLⁿ)Y = X`, and is the unique
bounded solution. -/
theorem lag_inverse_geom {lam : ℝ} (hl : |lam| < 1) (n : ℤ) {X : ℤ → ℝ} (hX : BddZSeq X) :
    oneSubLag lam n (geomLagSum lam n X) = X ∧ BddZSeq (geomLagSum lam n X) ∧
      ∀ Y, BddZSeq Y → oneSubLag lam n Y = X → Y = geomLagSum lam n X := by
  have hsol : oneSubLag lam n (geomLagSum lam n X) = X := by
    ext t
    simp only [oneSubLag, lagOp]
    rw [geomLagSum_eq hl hX n t]
    ring
  refine ⟨hsol, geomLagSum_bdd hl hX n, fun Y hY hYX => ?_⟩
  have hD : BddZSeq (fun t => Y t - geomLagSum lam n X t) := by
    obtain ⟨M, hM⟩ := hY
    obtain ⟨M', hM'⟩ := geomLagSum_bdd hl hX n
    exact ⟨M + M', fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))⟩
  have h0 := eq_zero_of_bdd_of_lag hl hD (n := n) (fun t => by
    have h1 := congrFun hYX t
    have h2 := congrFun hsol t
    simp only [oneSubLag, lagOp] at h1 h2
    linarith)
  ext t
  have := congrFun h0 t
  simp only [Pi.zero_apply] at this
  linarith

/-- `(1 − λLⁿ)` applied to `Σ (j+1)λʲ L^{nj}X` gives `Σ λʲ L^{nj}X`. -/
theorem oneSubLag_geomLagSum2 {lam : ℝ} (hl : |lam| < 1) (n : ℤ) {X : ℤ → ℝ}
    (hX : BddZSeq X) : oneSubLag lam n (geomLagSum2 lam n X) = geomLagSum lam n X := by
  ext t
  simp only [oneSubLag]
  rw [show lagOp n (geomLagSum2 lam n X) t = geomLagSum2 lam n X (t - n) from rfl]
  simp only [geomLagSum2, geomLagSum]
  set A : ℕ → ℝ := fun j => ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X t with hAdef
  set B : ℕ → ℝ := fun j => ((j : ℝ) + 1) * lam ^ j * lagOp (n * j) X (t - n) with hBdef
  set C : ℕ → ℝ := fun j => lam ^ j * lagOp (n * j) X t with hCdef
  have hA : Summable A := geomLagSum2_summable hl hX n t
  have hB : Summable (fun j => lam * B j) := (geomLagSum2_summable hl hX n (t - n)).mul_left lam
  have hC : Summable C := geomLagSum_summable hl hX n t
  have hA' : Summable (fun j => A (j + 1)) := (summable_nat_add_iff 1).2 hA
  have e1 : ∑' j, A j = A 0 + ∑' j, A (j + 1) := hA.tsum_eq_zero_add
  have e2 : ∑' j, C j = C 0 + ∑' j, C (j + 1) := hC.tsum_eq_zero_add
  have e3 : ∑' j, (A (j + 1) - lam * B j) = ∑' j, A (j + 1) - ∑' j, lam * B j :=
    hA'.tsum_sub hB
  have e4 : ∑' j, (A (j + 1) - lam * B j) = ∑' j, C (j + 1) := by
    refine tsum_congr (fun j => ?_)
    simp only [hAdef, hBdef, hCdef, lagOp]
    push_cast
    rw [show t - n * ((j : ℤ) + 1) = t - n - n * j by ring, pow_succ]
    ring
  have e5 : ∑' j, lam * B j = lam * ∑' j, B j := tsum_mul_left
  have e6 : A 0 = C 0 := by simp [hAdef, hCdef]
  linarith

/-- **Lag-operator expansion** (Miao, p. 11): `1/(1 − λLⁿ)² = Σ_{j≥0} (j + 1)λʲ L^{nj}` for
`|λ| < 1`. For bounded `X`, `Y = Σ (j+1)λʲ L^{nj} X` is bounded, solves `(1 − λLⁿ)²Y = X`, and
is the unique bounded solution. -/
theorem lag_inverse_geom_sq {lam : ℝ} (hl : |lam| < 1) (n : ℤ) {X : ℤ → ℝ} (hX : BddZSeq X) :
    oneSubLag lam n (oneSubLag lam n (geomLagSum2 lam n X)) = X ∧
      BddZSeq (geomLagSum2 lam n X) ∧
      ∀ Y, BddZSeq Y → oneSubLag lam n (oneSubLag lam n Y) = X → Y = geomLagSum2 lam n X := by
  obtain ⟨h1, h1B, h1U⟩ := lag_inverse_geom hl n hX
  have h2 := oneSubLag_geomLagSum2 hl n hX
  refine ⟨by rw [h2, h1], geomLagSum2_bdd hl hX n, fun Y hY hYX => ?_⟩
  have hVB : BddZSeq (oneSubLag lam n Y) := by
    obtain ⟨M, hM⟩ := hY
    refine ⟨M + |lam| * M, fun t => ?_⟩
    simp only [oneSubLag, lagOp]
    refine (abs_sub _ _).trans (add_le_add (hM t) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
  have hV := h1U _ hVB hYX
  obtain ⟨-, -, hU⟩ := lag_inverse_geom hl n h1B
  rw [hU Y hY hV, hU _ (geomLagSum2_bdd hl hX n) h2]

/-- Miao, p. 11, scalar form: `1/(1 − λ) = Σ_{j≥0} λʲ` for `|λ| < 1`. -/
theorem lag_scalar_geom {lam : ℝ} (hl : |lam| < 1) : 1 / (1 - lam) = ∑' j : ℕ, lam ^ j := by
  rw [tsum_geometric_of_abs_lt_one hl, one_div]

/-- Miao, p. 11, scalar form: `1/(1 − λ)² = Σ_{j≥0} (j + 1)λʲ` for `|λ| < 1`. -/
theorem lag_scalar_geom_sq {lam : ℝ} (hl : |lam| < 1) :
    1 / (1 - lam) ^ 2 = ∑' j : ℕ, ((j : ℝ) + 1) * lam ^ j := by
  have hl1 : 1 - lam ≠ 0 := by
    intro h; have : lam = 1 := by linarith
    rw [this] at hl; norm_num at hl
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := lam) (by rwa [Real.norm_eq_abs])
  have h2 := summable_geometric_of_abs_lt_one hl
  have : (fun j : ℕ => ((j : ℝ) + 1) * lam ^ j) = fun j : ℕ => (j : ℝ) * lam ^ j + lam ^ j := by
    ext j; ring
  rw [this, (by simpa using h1 : Summable (fun j : ℕ => (j : ℝ) * lam ^ j)).tsum_add h2,
    tsum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs]),
    tsum_geometric_of_abs_lt_one hl]
  field_simp
  ring

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Scalar second-order linear equations

Miao, §1.3, pp. 12–15, and (1.19), p. 15: `x_{t+2} = a x_{t+1} + b x_t + c z_t` (1.13).

* Characteristic roots: `λ₁ + λ₂ = a`, `λ₁λ₂ = −b` iff `μ² − aμ − b = (μ − λ₁)(μ − λ₂)`
  (`char_roots_iff`); complex roots always exist (`char_roots_exist`); the factorisation (1.15)
  (`eq_1_15`); superposition (`superposition`, `sub_isHomSol`).
* Case 1 (distinct real roots): `c₁λ₁ᵗ + c₂λ₂ᵗ` solves (1.16) (`eq_1_17`) and every solution has
  this form (`eq_1_17_general`); sink (`case1_sink`, also with bounded forcing,
  `case1_sink_bdd`) and indeterminacy (`case1_sink_indeterminate`); source
  (`case1_source`). **Correction:** "explodes" means unbounded, not `|x_t| → ∞`: for roots `±2`
  the solution `2ᵗ + (−2)ᵗ` vanishes at every odd `t` (`case1_source_not_tendsto`). The
  saddle-path solution `x_{t+1} = λ₁x_t − (c/λ₂) Σ λ₂^{−j} z_{t+j}` (`saddlePath`,
  `case1_saddle_eq`) solves (1.13) (`case1_saddle_isSol`), is bounded (`case1_saddle_bdd`), and
  is the unique bounded solution with the given `x₀` (`case1_saddle_unique`, `case1_saddle`).
* Case 2 (repeated root `λ`): `(c₁ + tc₂)λᵗ` solves (1.16) (`case2_solution`), with the book's
  verification (`case2_verification`). **Correction:** it is the general solution only for
  `λ ≠ 0` (`case2_general`); for `λ = 0` the solution `0, 1, 0, 0, …` is not of this form
  (`case2_general_counterexample`). Stability: all solutions converge to 0 iff `|λ| < 1`
  (`case2_stable_iff`).
* Case 3 (complex roots `re^{±iθ}`): the roots (`case3_roots`), the book's complex computation
  (`case3_complex_form`, `case3_conj_real`), real solutions `rᵗ(A cos θt + B sin θt)`
  (`case3_solution`), which are all real solutions when `sin θ ≠ 0` (`case3_general`); damped
  for `r < 1` (`case3_damped`) and explosive (unbounded) for `r > 1` (`case3_explosive`).
* (1.19): `x` solves (1.13) iff `(x_t, x_{t+1})` solves the first-order system (`eq_1_19`,
  `eq_1_19_of_system`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

/-- `x` solves `x_{t+2} = a x_{t+1} + b x_t + c z_t` (Miao, (1.13), p. 12). -/
def IsSecondOrderSol (a b c : ℝ) (z x : ℕ → ℝ) : Prop :=
  ∀ t, x (t + 2) = a * x (t + 1) + b * x t + c * z t

/-- `x` solves the homogeneous equation `x_{t+2} = a x_{t+1} + b x_t` (Miao, (1.16), p. 12). -/
def IsHomSol (a b : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ t, x (t + 2) = a * x (t + 1) + b * x t

/-- Miao, p. 12: `λ₁ + λ₂ = a` and `λ₁λ₂ = −b` iff `μ² − aμ − b = (μ − λ₁)(μ − λ₂)` for all
`μ`; in particular `λ₁`, `λ₂` are the characteristic roots. -/
theorem char_roots_iff {K : Type*} [Field K] [CharZero K] (a b l1 l2 : K) :
    (l1 + l2 = a ∧ l1 * l2 = -b) ↔ ∀ μ : K, μ ^ 2 - a * μ - b = (μ - l1) * (μ - l2) := by
  constructor
  · rintro ⟨h1, h2⟩ μ
    rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]
    ring
  · intro h
    have h0 := h 0
    have h1 := h 1
    exact ⟨by linear_combination h1 - h0, by linear_combination -h0⟩

/-- Miao, p. 12: the two (possibly complex) characteristic roots exist for all real `a`, `b`. -/
theorem char_roots_exist (a b : ℝ) : ∃ l1 l2 : ℂ, l1 + l2 = a ∧ l1 * l2 = -b := by
  set s : ℂ := ((a : ℂ) ^ 2 + 4 * b) ^ ((2 : ℂ)⁻¹)
  have hs : s ^ 2 = (a : ℂ) ^ 2 + 4 * b := by
    have := Complex.cpow_nat_inv_pow ((a : ℂ) ^ 2 + 4 * b) (n := 2) (by norm_num)
    simp only [Nat.cast_ofNat] at this
    exact this
  refine ⟨(a + s) / 2, (a - s) / 2, by ring, ?_⟩
  linear_combination (-1 / 4 : ℂ) * hs

/-- Miao, (1.15), p. 12: with `λ₁ + λ₂ = a`, `λ₁λ₂ = −b`,
`(L⁻¹ − λ₁)(L⁻¹ − λ₂)x_t = x_{t+2} − a x_{t+1} − b x_t`. -/
theorem eq_1_15 {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (x : ℕ → ℝ) (t : ℕ) :
    (x (t + 2) - l2 * x (t + 1)) - l1 * (x (t + 1) - l2 * x t) =
      x (t + 2) - a * x (t + 1) - b * x t := by
  rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]
  ring

/-- Miao, p. 13 (superposition): a homogeneous solution plus a particular solution solves
(1.13). -/
theorem superposition {a b c : ℝ} {z xh xp : ℕ → ℝ} (hh : IsHomSol a b xh)
    (hp : IsSecondOrderSol a b c z xp) : IsSecondOrderSol a b c z (fun t => xh t + xp t) := by
  intro t
  simp only
  rw [hh t, hp t]
  ring

/-- Miao, p. 13: the difference of two solutions of (1.13) solves (1.16), so every solution is
`xᵖ + xʰ`. -/
theorem sub_isHomSol {a b c : ℝ} {z x xp : ℕ → ℝ} (hx : IsSecondOrderSol a b c z x)
    (hp : IsSecondOrderSol a b c z xp) : IsHomSol a b (fun t => x t - xp t) := by
  intro t
  simp only
  rw [hx t, hp t]
  ring

/-- Solutions of (1.16) agreeing at `t = 0, 1` agree everywhere. -/
theorem IsHomSol.ext {a b : ℝ} {x y : ℕ → ℝ} (hx : IsHomSol a b x) (hy : IsHomSol a b y)
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  have key : ∀ t, x t = y t ∧ x (t + 1) = y (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1⟩
    | succ n ih => exact ⟨ih.2, by rw [hx n, hy n, ih.1, ih.2]⟩
  exact funext fun t => (key t).1

/-- For a solution of (1.16), `u_t = x_{t+1} − λ₂x_t` satisfies `u_{t+1} = λ₁u_t`. -/
theorem hom_factor {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) {x : ℕ → ℝ}
    (hx : IsHomSol a b x) (t : ℕ) :
    x (t + 1 + 1) - l2 * x (t + 1) = l1 * (x (t + 1) - l2 * x t) := by
  rw [show t + 1 + 1 = t + 2 from rfl, hx t]
  linear_combination (-x (t + 1)) * h1 + x t * h2

/-- For a solution of (1.13), `u_t = x_{t+1} − λ₂x_t` satisfies `u_{t+1} = λ₁u_t + c z_t`. -/
theorem sol_factor {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    {z x : ℕ → ℝ} (hx : IsSecondOrderSol a b c z x) (t : ℕ) :
    x (t + 1 + 1) - l2 * x (t + 1) = l1 * (x (t + 1) - l2 * x t) + c * z t := by
  rw [show t + 1 + 1 = t + 2 from rfl, hx t]
  linear_combination (-x (t + 1)) * h1 + x t * h2

/-! ### Case 1: distinct real roots -/

/-- **Case 1** (Miao, (1.17), p. 13): `c₁λ₁ᵗ + c₂λ₂ᵗ` solves (1.16). -/
theorem eq_1_17 {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (c1 c2 : ℝ) :
    IsHomSol a b (fun t => c1 * l1 ^ t + c2 * l2 ^ t) := by
  intro t
  have hr1 : l1 ^ 2 = a * l1 + b := by rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]; ring
  have hr2 : l2 ^ 2 = a * l2 + b := by rw [← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]; ring
  simp only [pow_add, pow_one]
  linear_combination c1 * l1 ^ t * hr1 + c2 * l2 ^ t * hr2

/-- **Case 1** (Miao, (1.17), p. 13): for distinct roots every solution of (1.16) is
`c₁λ₁ᵗ + c₂λ₂ᵗ`, with `c₁ = (x₁ − λ₂x₀)/(λ₁ − λ₂)`, `c₂ = (λ₁x₀ − x₁)/(λ₁ − λ₂)`. -/
theorem eq_1_17_general {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (hne : l1 ≠ l2)
    {x : ℕ → ℝ} (hx : IsHomSol a b x) :
    x = fun t => (x 1 - l2 * x 0) / (l1 - l2) * l1 ^ t + (l1 * x 0 - x 1) / (l1 - l2) * l2 ^ t := by
  have hd : l1 - l2 ≠ 0 := sub_ne_zero.2 hne
  refine hx.ext (eq_1_17 h1 h2 _ _) ?_ ?_
  · simp only [pow_zero, mul_one]; field_simp; ring
  · simp only [pow_one]; field_simp; ring

/-- **Case 1, sink** (Miao, p. 13): if `|λ₁| < 1` and `|λ₂| < 1`, every solution of (1.16)
converges to the steady state `0`. -/
theorem case1_sink {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (hl1 : |l1| < 1)
    (hl2 : |l2| < 1) {x : ℕ → ℝ} (hx : IsHomSol a b x) : Tendsto x atTop (𝓝 0) := by
  have hu : ∀ t, x (t + 1 + 1) - l2 * x (t + 1) = l1 * (x (t + 1) - l2 * x t) :=
    hom_factor h1 h2 hx
  have hu0 : Tendsto (fun t => x (t + 1) - l2 * x t) atTop (𝓝 0) := by
    have := (pow_mul_tendsto_zero_iff (b := l1) (k := 1) one_ne_zero).2 hl1
    have h := this.mul_const (x 1 - l2 * x 0)
    simp only [mul_one, zero_mul] at h
    exact h.congr (fun t => (geom_eq (x := fun t => x (t + 1) - l2 * x t) hu t).symm)
  exact tendsto_zero_of_forced hl2 (fun t => by ring) hu0

/-- **Case 1, sink** (Miao, p. 13): with bounded forcing and `|λ₁|, |λ₂| < 1`, every solution
of (1.13) is bounded, whatever `x₀` and `x₁`. -/
theorem case1_sink_bdd {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl1 : |l1| < 1) (hl2 : |l2| < 1) {z x : ℕ → ℝ} (hz : BddSeq z)
    (hx : IsSecondOrderSol a b c z x) : BddSeq x := by
  have hu : BddSeq (fun t => x (t + 1) - l2 * x t) := by
    refine bddSeq_of_forced hl1 (w := fun t => c * z t) (fun t => sol_factor h1 h2 hx t) ?_
    obtain ⟨M, hM⟩ := hz
    exact ⟨|c| * M, fun t => by
      change |c * z t| ≤ _
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg c)⟩
  exact bddSeq_of_forced hl2 (fun t => by ring) hu

/-- **Case 1, sink: indeterminacy** (Miao, p. 13): the initial value `x₀` does not pin down the
solution: `λ₁ᵗ` and `λ₂ᵗ` are distinct convergent solutions with `x₀ = 1`. -/
theorem case1_sink_indeterminate {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hne : l1 ≠ l2) (hl1 : |l1| < 1) (hl2 : |l2| < 1) :
    ∃ x y : ℕ → ℝ, IsHomSol a b x ∧ IsHomSol a b y ∧ x 0 = y 0 ∧ x ≠ y ∧
      Tendsto x atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) := by
  have hx := eq_1_17 h1 h2 1 0
  have hy := eq_1_17 h1 h2 0 1
  refine ⟨_, _, hx, hy, by simp, fun h => hne ?_, case1_sink h1 h2 hl1 hl2 hx,
    case1_sink h1 h2 hl1 hl2 hy⟩
  simpa using congrFun h 1

/-- **Case 1, source** (Miao, p. 13): if `|λ₁| > 1` and `|λ₂| > 1` (distinct), every solution
of (1.16) other than `0` explodes (is unbounded). -/
theorem case1_source {a b l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b) (hne : l1 ≠ l2)
    (hl1 : 1 < |l1|) (hl2 : 1 < |l2|) {x : ℕ → ℝ} (hx : IsHomSol a b x)
    (h0 : x 0 ≠ 0 ∨ x 1 ≠ 0) : ¬ BddSeq x := by
  rintro ⟨M, hM⟩
  have hbu : ∀ l : ℝ, BddSeq (fun t => x (t + 1) - l * x t) := fun l =>
    ⟨M + |l| * M, fun t => (abs_sub _ _).trans (add_le_add (hM _)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)))⟩
  have hu := (geom_bdd_iff hl1 (x := fun t => x (t + 1) - l2 * x t)
    (hom_factor h1 h2 hx)).1 (hbu l2)
  have hv := (geom_bdd_iff hl2 (x := fun t => x (t + 1) - l1 * x t)
    (hom_factor (by linarith) (by linarith) hx)).1 (hbu l1)
  simp only [zero_add] at hu hv
  have hd : (l1 - l2) * x 0 = 0 := by linarith
  have hx0 : x 0 = 0 := (mul_eq_zero.1 hd).resolve_left (sub_ne_zero.2 hne)
  rw [hx0, mul_zero, sub_zero] at hu
  rcases h0 with h | h
  · exact h hx0
  · exact h hu

/-- **Correction** (Miao, p. 13, "this solution explodes"): in a source the solution need not
satisfy `|x_t| → ∞`. For `x_{t+2} = 4x_t` (roots `±2`), `x_t = 2ᵗ + (−2)ᵗ` is a solution that
vanishes at every odd `t`. -/
theorem case1_source_not_tendsto :
    IsHomSol 0 4 (fun t => 2 ^ t + (-2) ^ t) ∧ (∀ k, (2 : ℝ) ^ (2 * k + 1) + (-2) ^ (2 * k + 1) = 0)
      ∧ ¬ Tendsto (fun t => |(2 : ℝ) ^ t + (-2) ^ t|) atTop atTop := by
  have hodd : ∀ k, (2 : ℝ) ^ (2 * k + 1) + (-2) ^ (2 * k + 1) = 0 := fun k => by
    rw [pow_succ, pow_succ, pow_mul, pow_mul]; norm_num
  refine ⟨fun t => by simp only [pow_add]; ring, hodd, fun h => ?_⟩
  obtain ⟨N, hN⟩ := (tendsto_atTop.1 h 1).exists_forall_of_atTop
  have := hN (2 * N + 1) (by omega)
  rw [hodd N, abs_zero] at this
  norm_num at this

/-- The saddle path of Case 1 (Miao, p. 13): `x₀` given and
`x_{t+1} = λ₁x_t + w_t`, `w_t = −(c/λ₂) Σ_j (1/λ₂)ʲ z_{t+j}` (the forward solution (1.8)). -/
noncomputable def saddlePath (l1 l2 c : ℝ) (z : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | t + 1 => l1 * saddlePath l1 l2 c z x0 t + fwdSol l2 c z t

/-- **Case 1, saddle path** (Miao, p. 13): the saddle path satisfies the displayed equation
`x_{t+1} = λ₁x_t − (c/λ₂) Σ_{j≥0} λ₂^{−j} z_{t+j}`. -/
theorem case1_saddle_eq (l1 l2 c : ℝ) (z : ℕ → ℝ) (x0 : ℝ) (t : ℕ) :
    saddlePath l1 l2 c z x0 (t + 1) = l1 * saddlePath l1 l2 c z x0 t -
      c / l2 * ∑' j : ℕ, l2 ^ (-(j : ℤ)) * z (t + j) := by
  simp only [saddlePath, fwdSol, zpow_neg, zpow_natCast, inv_pow, one_div]
  ring

/-- **Case 1, saddle path** (Miao, pp. 13–14): for `|λ₂| > 1` and bounded `z` the saddle path
solves (1.13). -/
theorem case1_saddle_isSol {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl2 : 1 < |l2|) {z : ℕ → ℝ} (hz : BddSeq z) (x0 : ℝ) :
    IsSecondOrderSol a b c z (saddlePath l1 l2 c z x0) := by
  intro t
  have hw := eq_1_8_isScalarSol (c := c) hl2 hz t
  have e1 : saddlePath l1 l2 c z x0 (t + 2) =
      l1 * saddlePath l1 l2 c z x0 (t + 1) + fwdSol l2 c z (t + 1) := rfl
  have e2 : saddlePath l1 l2 c z x0 (t + 1) =
      l1 * saddlePath l1 l2 c z x0 t + fwdSol l2 c z t := rfl
  rw [e1, hw, ← h1, show b = -(l1 * l2) by rw [h2, neg_neg]]
  linear_combination (-l2) * e2

/-- **Case 1, saddle path** (Miao, p. 14): for `|λ₁| < 1 < |λ₂|` and bounded `z` the saddle path
is bounded. -/
theorem case1_saddle_bdd {l1 l2 c : ℝ} (hl1 : |l1| < 1) (hl2 : 1 < |l2|) {z : ℕ → ℝ}
    (hz : BddSeq z) (x0 : ℝ) : BddSeq (saddlePath l1 l2 c z x0) :=
  bddSeq_of_forced hl1 (fun _ => rfl) (eq_1_8_bdd hl2 hz)

/-- **Case 1, saddle path** (Miao, p. 14): for `|λ₁| < 1 < |λ₂|` and bounded `z`, any bounded
solution of (1.13) with initial value `x₀` is the saddle path. -/
theorem case1_saddle_unique {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl1 : |l1| < 1) (hl2 : 1 < |l2|) {z x : ℕ → ℝ} (hz : BddSeq z)
    (hx : IsSecondOrderSol a b c z x) (hB : BddSeq x) : x = saddlePath l1 l2 c z (x 0) := by
  set y := saddlePath l1 l2 c z (x 0)
  have hD := sub_isHomSol hx (case1_saddle_isSol h1 h2 hl2 hz (x 0))
  have hDB : BddSeq (fun t => x t - y t) := by
    obtain ⟨M, hM⟩ := hB
    obtain ⟨M', hM'⟩ := case1_saddle_bdd (c := c) hl1 hl2 hz (x 0)
    exact ⟨M + M', fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))⟩
  set v : ℕ → ℝ := fun t => (x (t + 1) - y (t + 1)) - l1 * (x t - y t) with hvdef
  have hv : ∀ t, v (t + 1) = l2 * v t := fun t => by
    have := hom_factor (l1 := l2) (l2 := l1) (by linarith) (by linarith) hD t
    simp only [hvdef]
    linarith
  have hvB : BddSeq v := by
    obtain ⟨M, hM⟩ := hDB
    exact ⟨M + |l1| * M, fun t => (abs_sub _ _).trans (add_le_add (hM _)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)))⟩
  have hv0 := (geom_bdd_iff hl2 hv).1 hvB
  have hvall : ∀ t, v t = 0 := fun t => by
    rw [geom_eq hv t, hv0, mul_zero]
  have hD0 : x 0 - y 0 = 0 := by simp [y, saddlePath]
  have hg : ∀ t, x (t + 1) - y (t + 1) = l1 * (x t - y t) := fun t => by
    have := hvall t
    simp only [hvdef] at this
    linarith
  ext t
  have := geom_eq (x := fun t => x t - y t) hg t
  simp only [hD0, mul_zero] at this
  linarith

/-- **Case 1, saddle path** (Miao, pp. 13–14): for `|λ₁| < 1 < |λ₂|` and bounded `z`, for each
`x₀` there is exactly one bounded solution of (1.13) starting at `x₀`: the saddle path. -/
theorem case1_saddle {a b c l1 l2 : ℝ} (h1 : l1 + l2 = a) (h2 : l1 * l2 = -b)
    (hl1 : |l1| < 1) (hl2 : 1 < |l2|) {z : ℕ → ℝ} (hz : BddSeq z) (x0 : ℝ) :
    ∃! x : ℕ → ℝ, x 0 = x0 ∧ IsSecondOrderSol a b c z x ∧ BddSeq x := by
  refine ⟨saddlePath l1 l2 c z x0, ⟨rfl, case1_saddle_isSol h1 h2 hl2 hz x0,
    case1_saddle_bdd hl1 hl2 hz x0⟩, fun x ⟨hx0, hx, hB⟩ => ?_⟩
  rw [case1_saddle_unique h1 h2 hl1 hl2 hz hx hB, hx0]

/-! ### Case 2: a repeated root -/

/-- **Case 2** (Miao, p. 14): with the repeated root `λ` (`a = 2λ`, `b = −λ²`), `(c₁ + tc₂)λᵗ`
solves (1.16). -/
theorem case2_solution (l c1 c2 : ℝ) :
    IsHomSol (2 * l) (-l ^ 2) (fun t => (c1 + t * c2) * l ^ t) := by
  intro t
  push_cast
  simp only [pow_add]
  ring

/-- **Case 2** (Miao, p. 14): the book's verification. With `(L⁻¹ − λ)y_t = y_{t+1} − λy_t`,
`(L⁻¹ − λ)²x_t = x_{t+2} − 2λx_{t+1} + λ²x_t`, `(L⁻¹ − λ)[(c₁ + tc₂)λᵗ] = c₂λ^{t+1}` and
`(L⁻¹ − λ)[c₂λ^{t+1}] = 0`. -/
theorem case2_verification (l c1 c2 : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    ((x (t + 2) - l * x (t + 1)) - l * (x (t + 1) - l * x t) =
        x (t + 2) - 2 * l * x (t + 1) - (-l ^ 2) * x t) ∧
      ((c1 + ((t + 1 : ℕ) : ℝ) * c2) * l ^ (t + 1) - l * ((c1 + t * c2) * l ^ t) =
        c2 * l ^ (t + 1)) ∧
      c2 * l ^ (t + 1 + 1) - l * (c2 * l ^ (t + 1)) = 0 := by
  refine ⟨by ring, ?_, by rw [pow_succ _ (t + 1)]; ring⟩
  push_cast
  rw [pow_succ]
  ring

/-- **Case 2, corrected** (Miao, p. 14): for `λ ≠ 0` every solution of (1.16) is
`(c₁ + tc₂)λᵗ` with `c₁ = x₀`, `c₂ = (x₁ − λx₀)/λ`. -/
theorem case2_general {l : ℝ} (hl : l ≠ 0) {x : ℕ → ℝ} (hx : IsHomSol (2 * l) (-l ^ 2) x) :
    x = fun t : ℕ => (x 0 + (t : ℝ) * ((x 1 - l * x 0) / l)) * l ^ t := by
  refine hx.ext (case2_solution _ _ _) ?_ ?_
  · simp
  · simp only [Nat.cast_one, one_mul, pow_one]; field_simp; ring

/-- **Counterexample to Case 2 as printed** (Miao, p. 14): for the repeated root `λ = 0`
(`a = b = 0`), `x = (0, 1, 0, 0, …)` solves (1.16) but is not `(c₁ + tc₂)0ᵗ` for any
`c₁, c₂`. -/
theorem case2_general_counterexample :
    IsHomSol (2 * 0) (-0 ^ 2) (fun t => if t = 1 then 1 else 0) ∧
      ¬ ∃ c1 c2 : ℝ, ∀ t : ℕ, (if t = 1 then (1 : ℝ) else 0) = (c1 + t * c2) * 0 ^ t := by
  refine ⟨fun t => by simp, ?_⟩
  rintro ⟨c1, c2, h⟩
  have := h 1
  simp at this

/-- **Case 2, stability** (Miao, p. 14): with a repeated root `λ`, every solution of (1.16)
converges to `0` iff `|λ| < 1`. -/
theorem case2_stable_iff (l : ℝ) :
    (∀ x, IsHomSol (2 * l) (-l ^ 2) x → Tendsto x atTop (𝓝 0)) ↔ |l| < 1 := by
  constructor
  · intro h
    have := h _ (case2_solution l 1 0)
    simp only [mul_zero, add_zero, one_mul] at this
    exact (pow_mul_tendsto_zero_iff (b := l) one_ne_zero).1 (by simpa using this)
  · intro hl x hx
    exact case1_sink (l1 := l) (l2 := l) (by ring) (by ring) hl hl hx

/-! ### Case 3: complex roots -/

/-- **Case 3** (Miao, p. 14): `λ₁ = re^{iθ}`, `λ₂ = re^{−iθ}` are the characteristic roots of
`μ² − aμ − b` for `a = 2r cos θ`, `b = −r²`. -/
theorem case3_roots (r θ : ℝ) :
    (r * Complex.exp (θ * Complex.I)) + (r * Complex.exp (-θ * Complex.I)) =
        ((2 * r * Real.cos θ : ℝ) : ℂ) ∧
      (r * Complex.exp (θ * Complex.I)) * (r * Complex.exp (-θ * Complex.I)) =
        -((-r ^ 2 : ℝ) : ℂ) := by
  constructor
  · rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    push_cast
    ring
  · rw [mul_mul_mul_comm, ← Complex.exp_add]
    push_cast
    ring_nf
    simp

/-- **Case 3** (Miao, p. 14): the book's computation
`c₁λ₁ᵗ + c₂λ₂ᵗ = rᵗ[(c₁ + c₂) cos θt + (c₁ − c₂) i sin θt]` for `λ₁,₂ = re^{±iθ}`. -/
theorem case3_complex_form (r θ : ℝ) (c1 c2 : ℂ) (t : ℕ) :
    c1 * (r * Complex.exp (θ * Complex.I)) ^ t + c2 * (r * Complex.exp (-θ * Complex.I)) ^ t =
      (r : ℂ) ^ t * ((c1 + c2) * (Real.cos (θ * t) : ℂ) +
        (c1 - c2) * (Real.sin (θ * t) : ℂ) * Complex.I) := by
  rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    show (t : ℂ) * (θ * Complex.I) = ((θ * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    show (t : ℂ) * (-θ * Complex.I) = ((-(θ * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- **Case 3** (Miao, p. 15): if `c₂ = c̄₁` then `c₁ + c₂` and `(c₁ − c₂)i` are real. -/
theorem case3_conj_real (c : ℂ) :
    (c + (starRingEnd ℂ) c).im = 0 ∧ ((c - (starRingEnd ℂ) c) * Complex.I).im = 0 := by
  simp

/-- **Case 3** (Miao, p. 15): with conjugate constants `c₂ = c̄₁` the complex solution is the
real `rᵗ[A cos θt + B sin θt]`, `A = 2 Re c₁`, `B = −2 Im c₁`. -/
theorem case3_real_form (r θ : ℝ) (c : ℂ) (t : ℕ) :
    c * (r * Complex.exp (θ * Complex.I)) ^ t +
        (starRingEnd ℂ) c * (r * Complex.exp (-θ * Complex.I)) ^ t =
      ((r ^ t * (2 * c.re * Real.cos (θ * t) + (-2 * c.im) * Real.sin (θ * t)) : ℝ) : ℂ) := by
  rw [case3_complex_form]
  apply Complex.ext <;> simp <;> ring

/-- **Case 3** (Miao, p. 15): `rᵗ[A cos θt + B sin θt]` solves (1.16) for the complex roots
`re^{±iθ}`, i.e. `a = 2r cos θ`, `b = −r²`. -/
theorem case3_solution (r θ A B : ℝ) :
    IsHomSol (2 * r * Real.cos θ) (-r ^ 2)
      (fun t : ℕ => r ^ t * (A * Real.cos (θ * t) + B * Real.sin (θ * t))) := by
  intro t
  have hc : Real.cos (θ * ((t + 2 : ℕ) : ℝ)) =
      2 * Real.cos θ * Real.cos (θ * ((t + 1 : ℕ) : ℝ)) - Real.cos (θ * t) := by
    push_cast
    rw [show θ * ((t : ℝ) + 2) = θ * (t + 1) + θ by ring,
      show θ * (t : ℝ) = θ * (t + 1) - θ by ring, Real.cos_add, Real.cos_sub]
    ring
  have hs : Real.sin (θ * ((t + 2 : ℕ) : ℝ)) =
      2 * Real.cos θ * Real.sin (θ * ((t + 1 : ℕ) : ℝ)) - Real.sin (θ * t) := by
    push_cast
    rw [show θ * ((t : ℝ) + 2) = θ * (t + 1) + θ by ring,
      show θ * (t : ℝ) = θ * (t + 1) - θ by ring, Real.sin_add, Real.sin_sub]
    ring
  simp only
  rw [hc, hs, pow_add, pow_add]
  ring

/-- **Case 3** (Miao, p. 15): for genuinely complex roots (`r ≠ 0`, `sin θ ≠ 0`) every real
solution of (1.16) is `rᵗ[A cos θt + B sin θt]`, with `A = x₀`,
`B = (x₁ − r cos θ x₀)/(r sin θ)`. -/
theorem case3_general {r θ : ℝ} (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) {x : ℕ → ℝ}
    (hx : IsHomSol (2 * r * Real.cos θ) (-r ^ 2) x) :
    x = fun t : ℕ => r ^ t * (x 0 * Real.cos (θ * t) +
      (x 1 - r * Real.cos θ * x 0) / (r * Real.sin θ) * Real.sin (θ * t)) := by
  refine hx.ext (case3_solution _ _ _ _) ?_ ?_
  · simp
  · simp only [pow_one, Nat.cast_one, mul_one]
    field_simp
    ring

/-- **Case 3** (Miao, p. 15): for `0 ≤ r < 1` the oscillations are damped:
`rᵗ[A cos θt + B sin θt] → 0`. -/
theorem case3_damped_form {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ A B : ℝ) :
    Tendsto (fun t : ℕ => r ^ t * (A * Real.cos (θ * t) + B * Real.sin (θ * t))) atTop
      (𝓝 0) := by
  refine squeeze_zero_norm (a := fun t => r ^ t * (|A| + |B|)) (fun t => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr0 t)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const (|A| + |B|)

/-- **Case 3** (Miao, p. 15): for `0 < r < 1` and `sin θ ≠ 0` every solution of (1.16)
converges to `0`. -/
theorem case3_damped {r θ : ℝ} (hr0 : 0 < r) (hr : r < 1) (hs : Real.sin θ ≠ 0) {x : ℕ → ℝ}
    (hx : IsHomSol (2 * r * Real.cos θ) (-r ^ 2) x) : Tendsto x atTop (𝓝 0) := by
  rw [case3_general hr0.ne' hs hx]
  exact case3_damped_form hr0.le hr θ _ _

/-- **Case 3** (Miao, p. 15): for `r > 1` and `sin θ ≠ 0` the oscillations are explosive: every
nonzero solution of (1.16) is unbounded. The proof uses the invariant
`Q_t = x_{t+1}² − a x_t x_{t+1} + r² x_t² = |x_{t+1} − λ₂x_t|²`, which grows like `r^{2t}`. -/
theorem case3_explosive {r θ : ℝ} (hr : 1 < r) (hs : Real.sin θ ≠ 0) {x : ℕ → ℝ}
    (hx : IsHomSol (2 * r * Real.cos θ) (-r ^ 2) x) (h0 : x 0 ≠ 0 ∨ x 1 ≠ 0) : ¬ BddSeq x := by
  set a := 2 * r * Real.cos θ
  set Q : ℕ → ℝ := fun t => x (t + 1) ^ 2 - a * x t * x (t + 1) + r ^ 2 * x t ^ 2 with hQdef
  have hQ : ∀ t, Q (t + 1) = r ^ 2 * Q t := fun t => by
    simp only [hQdef]
    rw [show t + 1 + 1 = t + 2 from rfl, hx t]
    ring
  have hQ0 : 0 < Q 0 := by
    have hcs := Real.sin_sq_add_cos_sq θ
    have heq : Q 0 = (x 1 - r * Real.cos θ * x 0) ^ 2 + r ^ 2 * Real.sin θ ^ 2 * x 0 ^ 2 := by
      simp only [hQdef, a]
      linear_combination (-(r ^ 2 * x 0 ^ 2)) * hcs
    rw [heq]
    rcases h0 with h | h
    · have : 0 < r ^ 2 * Real.sin θ ^ 2 * x 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (x 1 - r * Real.cos θ * x 0)]
    · by_cases hx0 : x 0 = 0
      · rw [hx0]; simp only [mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, add_zero]; positivity
      · have : 0 < r ^ 2 * Real.sin θ ^ 2 * x 0 ^ 2 := by positivity
        nlinarith [sq_nonneg (x 1 - r * Real.cos θ * x 0)]
  rintro ⟨M, hM⟩
  have hsq : ∀ t, x t ^ 2 ≤ M ^ 2 := fun t => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM t) 2
  have hxy : ∀ t, |a * x t * x (t + 1)| ≤ |a| * (M * M) := fun t => by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hM t) (hM _) (abs_nonneg _)
      ((abs_nonneg _).trans (hM t))) (abs_nonneg _)
  have hbound : ∀ t, Q t ≤ M ^ 2 + |a| * (M * M) + r ^ 2 * M ^ 2 := fun t => by
    simp only [hQdef]
    have := neg_abs_le (a * x t * x (t + 1))
    nlinarith [hsq t, hsq (t + 1), hxy t, sq_nonneg r]
  have hr2 : 1 < |r ^ 2| := by rw [abs_of_pos (by positivity)]; nlinarith
  obtain ⟨t, ht⟩ := ((abs_pow_mul_tendsto_atTop hr2 hQ0.ne').eventually_gt_atTop
    (M ^ 2 + |a| * (M * M) + r ^ 2 * M ^ 2)).exists
  have hQt : Q t = (r ^ 2) ^ t * Q 0 := geom_eq hQ t
  have hpos : 0 < Q t := by rw [hQt]; positivity
  rw [← hQt, abs_of_pos hpos] at ht
  linarith [hbound t]

/-! ### The first-order form (1.19) -/

/-- Miao, (1.19), p. 15: `x` solves (1.13) iff `X_t = (x_t, x_{t+1})` solves the first-order
system `X_{t+1} = [[0, 1], [b, a]] X_t + [0; c] z_t`, written as (1.20) with `A = I`. -/
theorem eq_1_19 (a b c : ℝ) (z x : ℕ → ℝ) :
    IsSecondOrderSol a b c z x ↔
      IsSolution (1 : Matrix (Fin 2) (Fin 2) ℝ) !![0, 1; b, a] !![0; c] (fun t => ![z t])
        (fun t => ![x t, x (t + 1)]) := by
  simp only [IsSolution, Matrix.one_mulVec]
  constructor
  · intro h t
    ext i
    fin_cases i
    · simp
    · simp [h t]
      ring
  · intro h t
    have := congrFun (h t) 1
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_empty, add_zero,
      Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.head_cons, smul_eq_mul,
      Matrix.tail_cons] at this
    rw [show t + 2 = t + 1 + 1 from rfl, this]
    ring

/-- Miao, (1.19), p. 15: conversely, a solution `X` of the first-order system has
`X_t = (x_t, x_{t+1})` with `x_t = X_t(0)` a solution of (1.13). -/
theorem eq_1_19_of_system {a b c : ℝ} {z : ℕ → ℝ} {X : ℕ → Fin 2 → ℝ}
    (h : IsSolution (1 : Matrix (Fin 2) (Fin 2) ℝ) !![0, 1; b, a] !![0; c] (fun t => ![z t]) X) :
    IsSecondOrderSol a b c z (fun t => X t 0) ∧ ∀ t, X t = ![X t 0, X (t + 1) 0] := by
  simp only [IsSolution, Matrix.one_mulVec] at h
  have h0 : ∀ t, X (t + 1) 0 = X t 1 := fun t => by
    have := congrFun (h t) 0
    rw [show X t = ![X t 0, X t 1] by ext i; fin_cases i <;> rfl] at this
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_cons,
      Matrix.mulVec_empty, add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul, mul_zero, Matrix.tail_cons, mul_one,
      zero_add] at this
    linarith
  have h1 : ∀ t, X (t + 1) 1 = b * X t 0 + a * X t 1 + c * z t := fun t => by
    have := congrFun (h t) 1
    rw [show X t = ![X t 0, X t 1] by ext i; fin_cases i <;> rfl] at this
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.mulVec_cons,
      Matrix.mulVec_empty, add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, smul_eq_mul,
      Matrix.tail_cons] at this
    linarith
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only
    rw [show t + 2 = t + 1 + 1 from rfl, h0, h1, h0]
    ring
  · ext i
    fin_cases i
    · simp
    · simp [h0]

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Upper triangular matrices and geometric decay

Tools for Miao, §1.4.2, pp. 24–27 (the proof of Theorem 1.4.5): if `Λ` is an upper triangular
complex matrix whose diagonal entries all have modulus less than one, then the operator norms
`‖Λᵗ‖` are summable (`summable_norm_pow_of_triangular`), so `Λᵗ → 0` geometrically fast in the
sense needed for forward and backward solutions.

* The first block (`tendsto_zero_of_le_rec`, `tendsto_zero_of_rec`, `triangular_step`,
  `triangular_invariant`, `triangular_tendsto_iff`) is copied from
  `RecursiveMethods/DeterministicDynamics` (`LinearSystems.lean`).
* `mclm M` is the matrix `M` as a continuous linear map on `Fin m → ℂ` with the max norm;
  `‖mclm M‖` is the matrix norm used throughout.
* `summable_of_tendsto_zero`: if `‖Mᵗ‖ → 0` then `∑ₜ ‖Mᵗ‖ < ∞` (choose `K` with
  `‖Mᴷ‖ ≤ 1/2` and compare block sums).
* `diag_mul_of_upper`, `upper_inv`, `diag_inv_of_upper`: products and inverses of upper
  triangular matrices are upper triangular, with the products/inverses of the diagonals.
-/

open Filter Topology

namespace Miao.DifferenceEquations

open scoped Matrix

/-! ### A perturbed geometric recursion (copied from `LinearSystems.lean`) -/

/-- If `b_{t+1} ≤ rb_t + c_t` with `0 ≤ r < 1`, `b ≥ 0` and `c_t → 0`, then `b_t → 0`. -/
theorem tendsto_zero_of_le_rec {b c : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb0 : ∀ t, 0 ≤ b t) (hc : Tendsto c atTop (𝓝 0)) (hrec : ∀ t, b (t + 1) ≤ r * b t + c t) :
    Tendsto b atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hc) (ε / 2 * (1 - r)) (by
    have : 0 < 1 - r := by linarith
    positivity)
  -- `b_t ≤ r^{t − T}b_T + ε/2` for `t ≥ T`
  have hbound : ∀ k, b (T + k) ≤ r ^ k * b T + ε / 2 := by
    intro k
    induction k with
    | zero => simp; linarith
    | succ k ih =>
      have hcT : c (T + k) ≤ ε / 2 * (1 - r) := by
        have := hT (T + k) (by omega)
        rw [Real.dist_eq, sub_zero] at this
        exact (le_abs_self _).trans this.le
      have := hrec (T + k)
      rw [show T + (k + 1) = T + k + 1 by ring]
      calc b (T + k + 1) ≤ r * b (T + k) + c (T + k) := this
        _ ≤ r * (r ^ k * b T + ε / 2) + ε / 2 * (1 - r) := by
          have := mul_le_mul_of_nonneg_left ih hr0
          linarith
        _ = r ^ (k + 1) * b T + ε / 2 := by ring
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 / (b T + 1) by
    have := hb0 T; positivity) hr1
  refine ⟨T + K, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = T + k := ⟨t - T, by omega⟩
  have hk : r ^ k ≤ r ^ K := pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have h1 : r ^ k * b T < ε / 2 := by
    have hbT := hb0 T
    have : r ^ k * b T ≤ r ^ K * (b T + 1) := by
      have := pow_nonneg hr0 k
      nlinarith
    calc r ^ k * b T ≤ r ^ K * (b T + 1) := this
      _ < ε / 2 / (b T + 1) * (b T + 1) := mul_lt_mul_of_pos_right hK (by linarith)
      _ = ε / 2 := by field_simp
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hb0 _)]
  linarith [hbound k]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- If `a_{t+1} = μa_t + e_t` with `|μ| < 1` and `e_t → 0`, then `a_t → 0`. -/
theorem tendsto_zero_of_rec {a e : ℕ → V} {μ : ℂ} (hμ : ‖μ‖ < 1) (he : Tendsto e atTop (𝓝 0))
    (hrec : ∀ t, a (t + 1) = μ • a t + e t) : Tendsto a atTop (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_zero_of_le_rec (norm_nonneg μ) hμ
    (fun t => norm_nonneg _) (tendsto_zero_iff_norm_tendsto_zero.1 he) fun t => ?_)
  rw [hrec, ← norm_smul]
  exact norm_add_le _ _


variable {n : ℕ}

/-! ### Triangular systems (copied from `LinearSystems.lean`) -/

/-- One step of an upper triangular system, coordinate by coordinate. -/
theorem triangular_step (Λ : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (Λ *ᵥ v) i = Λ i i * v i + ∑ j ∈ Finset.univ.erase i, Λ i j * v j := by
  simp only [Matrix.mulVec, dotProduct]
  exact (Finset.add_sum_erase _ (fun j => Λ i j * v j) (Finset.mem_univ i)).symm

/-- Coordinates beyond `k` stay zero. -/
theorem triangular_invariant (Λ : Matrix (Fin n) (Fin n) ℂ) (hΛ : ∀ i j, j < i → Λ i j = 0)
    {k : ℕ} {w : Fin n → ℂ} (hw : ∀ j : Fin n, k ≤ j.val → w j = 0) (t : ℕ) :
    ∀ j : Fin n, k ≤ j.val → ((Λ ^ t) *ᵥ w) j = 0 := by
  induction t with
  | zero => intro j hj; simpa using hw j hj
  | succ t ih =>
    intro j hj
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l j with hlj | hjl
    · rw [hΛ j l hlj, zero_mul]
    · have := ih l (hj.trans (Fin.le_def.1 hjl))
      simp only [Matrix.mulVec, dotProduct] at this
      rw [this, mul_zero]

/-- **The triangular case.** If `Λ` is upper triangular, with `|Λᵢᵢ| < 1` for `i < m` and
`|Λᵢᵢ| ≥ 1` otherwise, then `Λᵗw → 0` iff `wᵢ = 0` for every `i ≥ m`. -/
theorem triangular_tendsto_iff (Λ : Matrix (Fin n) (Fin n) ℂ) (hΛ : ∀ i j, j < i → Λ i j = 0)
    (m : ℕ) (hs : ∀ i : Fin n, i.val < m → ‖Λ i i‖ < 1)
    (hu : ∀ i : Fin n, m ≤ i.val → 1 ≤ ‖Λ i i‖) (w : Fin n → ℂ) :
    Tendsto (fun t => (Λ ^ t) *ᵥ w) atTop (𝓝 0) ↔ ∀ i : Fin n, m ≤ i.val → w i = 0 := by
  set W : ℕ → Fin n → ℂ := fun t => (Λ ^ t) *ᵥ w
  have hrec : ∀ t i, W (t + 1) i = Λ i i * W t i + ∑ j ∈ Finset.univ.erase i, Λ i j * W t j :=
    fun t i => by
      simp only [W]
      rw [pow_succ', ← Matrix.mulVec_mulVec, triangular_step]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hjm, hj⟩ := hcon
    set S := Finset.univ.filter fun l : Fin n => w l ≠ 0
    have hS : S.Nonempty := ⟨j, by simp [S, hj]⟩
    set J := S.max' hS
    have hJS : J ∈ S := S.max'_mem hS
    have hwJ : w J ≠ 0 := (Finset.mem_filter.1 hJS).2
    have hjJ : j ≤ J := S.le_max' j (by simp [S, hj])
    have hbeyond : ∀ l : Fin n, J.val + 1 ≤ l.val → w l = 0 := fun l hl => by
      by_contra hl0
      have := S.le_max' l (by simp [S, hl0])
      have : l.val ≤ J.val := this
      omega
    have hinv := triangular_invariant Λ hΛ hbeyond
    -- the `J`-th coordinate is `Λ_JJᵗ w_J`
    have hJ : ∀ t, W t J = Λ J J ^ t * w J := by
      intro t
      induction t with
      | zero => simp [W]
      | succ t ih =>
        rw [hrec, ih, Finset.sum_eq_zero, add_zero, pow_succ]
        · ring
        · intro l hl
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hlJ | hJl
          · rw [hΛ J l hlJ, zero_mul]
          · rw [show W t l = 0 from hinv t l hJl, mul_zero]
    have hcoord : Tendsto (fun t => W t J) atTop (𝓝 0) := by
      have := ((continuous_apply J).tendsto 0).comp h
      simpa [Function.comp_def] using this
    have hpos : 0 < ‖w J‖ := norm_pos_iff.2 hwJ
    have hge : ∀ t, ‖w J‖ ≤ ‖W t J‖ := fun t => by
      rw [hJ, norm_mul, norm_pow]
      exact le_mul_of_one_le_left (norm_nonneg _)
        (one_le_pow₀ (hu J (hjm.trans (Fin.le_def.1 hjJ))))
    have := ge_of_tendsto' (tendsto_zero_iff_norm_tendsto_zero.1 hcoord) hge
    linarith
  · intro hw
    have hinv := triangular_invariant Λ hΛ hw
    -- downward induction on the coordinates
    have key : ∀ d : ℕ, ∀ i : Fin n, n ≤ i.val + d → Tendsto (fun t => W t i) atTop (𝓝 0) := by
      intro d
      induction d with
      | zero => intro i hi; exact absurd i.2 (by omega)
      | succ d ih =>
        intro i hi
        rcases le_or_gt m i.val with hmi | him
        · simp only [show ∀ t, W t i = 0 from fun t => hinv t i hmi]
          exact tendsto_const_nhds
        · refine tendsto_zero_of_rec (hs i him) ?_ fun t => by rw [hrec, smul_eq_mul]
          rw [show (0 : ℂ) = ∑ j ∈ Finset.univ.erase i, 0 by simp]
          refine tendsto_finsetSum _ fun j hj => ?_
          rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hij
          · simp only [hΛ i j hji, zero_mul]
            exact tendsto_const_nhds
          · have := (ih j (by have : i.val < j.val := hij; omega)).const_mul (Λ i j)
            rwa [mul_zero] at this
    exact tendsto_pi_nhds.2 fun i => key n i (by omega)


/-! ### Matrix norms through continuous linear maps -/

/-- The complex matrix `M` as a continuous linear map on `Fin m → ℂ` (max norm). -/
noncomputable def mclm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

theorem mclm_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    mclm M v = M *ᵥ v := rfl

theorem norm_mulVec_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    ‖M *ᵥ v‖ ≤ ‖mclm M‖ * ‖v‖ :=
  (mclm M).le_opNorm v

theorem norm_mclm_mul_le {m : ℕ} (M N : Matrix (Fin m) (Fin m) ℂ) :
    ‖mclm (M * N)‖ ≤ ‖mclm M‖ * ‖mclm N‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [mclm_apply, ← Matrix.mulVec_mulVec, mul_assoc]
  exact (norm_mulVec_le M _).trans (mul_le_mul_of_nonneg_left (norm_mulVec_le N v)
    (norm_nonneg _))

/-- Pointwise convergence to zero of powers gives convergence of operator norms (adapted from
`tendsto_opNorm_pow` in `RecursiveMethods/DeterministicDynamics`, `LocalStability.lean`). -/
theorem tendsto_norm_mclm_pow {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ w, Tendsto (fun t => (M ^ t) *ᵥ w) atTop (𝓝 0)) :
    Tendsto (fun t => ‖mclm (M ^ t)‖) atTop (𝓝 0) := by
  set e : Fin m → Fin m → ℂ := fun i => Pi.single i 1
  have hsum : Tendsto (fun t => ∑ i, ‖(M ^ t) *ᵥ e i‖) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ i : Fin m, ‖(0 : Fin m → ℂ)‖ by simp]
    exact tendsto_finsetSum _ fun i _ => (h (e i)).norm
  have hbound : ∀ t, ‖mclm (M ^ t)‖ ≤ ∑ i, ‖(M ^ t) *ᵥ e i‖ := fun t => by
    refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      fun z => ?_
    have hz : z = ∑ i, z i • e i := by
      funext j; simp [e, Pi.single_apply]
    calc ‖mclm (M ^ t) z‖ = ‖∑ i, z i • (M ^ t) *ᵥ e i‖ := by
          conv_lhs => rw [hz]
          rw [map_sum]; simp only [map_smul, mclm_apply]
      _ ≤ ∑ i, ‖z i • (M ^ t) *ᵥ e i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖z‖ * ‖(M ^ t) *ᵥ e i‖ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z i) (norm_nonneg _)
      _ = (∑ i, ‖(M ^ t) *ᵥ e i‖) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]
  exact squeeze_zero (fun t => norm_nonneg _) hbound hsum

/-- If `‖Mᵗ‖ → 0` then `∑ₜ ‖Mᵗ‖ < ∞`: with `‖Mᴷ‖ ≤ 1/2`, the sums over `K q` terms stay below
twice the sum of the first `K`. -/
theorem summable_of_tendsto_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (h : Tendsto (fun t => ‖mclm (M ^ t)‖) atTop (𝓝 0)) :
    Summable fun t => ‖mclm (M ^ t)‖ := by
  set a : ℕ → ℝ := fun t => ‖mclm (M ^ t)‖
  obtain ⟨N, hN⟩ :=
    (h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists_forall_of_atTop
  set K := N + 1
  have hK : a K ≤ 1 / 2 := hN K (by omega)
  set c₀ := ∑ i ∈ Finset.range K, a i
  have ha0 : ∀ t, 0 ≤ a t := fun t => norm_nonneg _
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun i _ => ha0 i
  have hblock : ∀ q, ∑ i ∈ Finset.range (K * q), a i ≤ 2 * c₀ := by
    intro q
    induction q with
    | zero => simp; linarith
    | succ q ih =>
      rw [show K * (q + 1) = K + K * q by ring, Finset.sum_range_add]
      have hshift : ∑ i ∈ Finset.range (K * q), a (K + i) ≤
          ∑ i ∈ Finset.range (K * q), 1 / 2 * a i := Finset.sum_le_sum fun i _ => by
        have : a (K + i) ≤ a K * a i := by
          simp only [a, pow_add]
          exact norm_mclm_mul_le _ _
        exact this.trans (mul_le_mul_of_nonneg_right hK (ha0 i))
      rw [← Finset.mul_sum] at hshift
      linarith
  refine summable_of_sum_range_le (c := 2 * c₀) ha0 fun t => ?_
  calc ∑ i ∈ Finset.range t, a i ≤ ∑ i ∈ Finset.range (K * t), a i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by simp only [K]; nlinarith))
          fun i _ _ => ha0 i
    _ ≤ 2 * c₀ := hblock t

/-! ### Products and inverses of upper triangular matrices -/

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
theorem diag_mul_of_upper {m : ℕ} {M N : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) (i : Fin m) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hki => ?_) (by simp)
  rcases lt_or_gt_of_ne hki with h | h
  · rw [hM h, zero_mul]
  · rw [hN h, mul_zero]

/-- The inverse of an upper triangular matrix is upper triangular. -/
theorem upper_inv {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsUpperTriangular)
    (hdet : M.det ≠ 0) : M⁻¹.IsUpperTriangular := by
  let : Invertible M := Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.2 hdet)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

/-- The diagonal of the inverse of an invertible upper triangular matrix. -/
theorem diag_inv_of_upper {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsUpperTriangular)
    (hdet : M.det ≠ 0) (i : Fin m) : M⁻¹ i i = (M i i)⁻¹ := by
  have h1 : (M⁻¹ * M) i i = 1 := by
    rw [Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.2 hdet), Matrix.one_apply_eq]
  rw [diag_mul_of_upper (upper_inv hM hdet) hM] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- If `Λ` is upper triangular with every diagonal entry of modulus less than one, the operator
norms of its powers are summable. -/
theorem summable_norm_pow_of_triangular {m : ℕ} (Λ : Matrix (Fin m) (Fin m) ℂ)
    (hΛ : Λ.IsUpperTriangular) (hd : ∀ i, ‖Λ i i‖ < 1) :
    Summable fun t => ‖mclm (Λ ^ t)‖ := by
  refine summable_of_tendsto_zero Λ (tendsto_norm_mclm_pow Λ fun w => ?_)
  exact (triangular_tendsto_iff Λ (fun i j h => hΛ h) m (fun i _ => hd i)
    (fun i hi => absurd i.2 (by omega)) w).2 fun i hi => absurd i.2 (by omega)

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stable and unstable subspaces

Copied from `RecursiveMethods/DeterministicDynamics` (`LinearSystems.lean`, and
`finrank_stableSubspace` from `LQStability.lean`), the spectral layer used in Miao, §1.4.1,
pp. 17–23, in place of the Jordan form.

For an operator `f` on a finite-dimensional complex normed space, the **stable subspace** is the
sum of the generalized eigenspaces of the eigenvalues `|μ| < 1`, the **unstable subspace** that
of the eigenvalues `|μ| ≥ 1`.

* `tendsto_iff_mem_stable`: `fᵗz → 0` iff `z` lies in the stable subspace.
* `stable_eq_top`: if every eigenvalue lies inside the unit disc, the stable subspace is all.
* `cplx`, `cplxEnd A`: a real vector as a complex vector, a real matrix acting on `ℂⁿ`;
  `hasEigenvalue_cplxEnd_iff`: its eigenvalues are the characteristic roots of `A`.
* `finrank_stableSubspace`: the stable subspace has dimension the number of characteristic
  roots, with multiplicity, inside the unit circle.
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The stable subspace -/

/-- The **stable subspace**: the generalized eigenspaces of the eigenvalues with `|μ| < 1`. -/
noncomputable def stableSubspace (f : End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ {μ : ℂ | ‖μ‖ < 1}, f.maxGenEigenspace μ

/-- The **unstable subspace**: the generalized eigenspaces of the eigenvalues with `|μ| ≥ 1`. -/
noncomputable def unstableSubspace (f : End ℂ V) : Submodule ℂ V :=
  ⨆ μ ∈ {μ : ℂ | 1 ≤ ‖μ‖}, f.maxGenEigenspace μ

/-- The vectors whose orbits converge to zero. -/
noncomputable def convSubspace (f : End ℂ V) : Submodule ℂ V where
  carrier := {z | Tendsto (fun t => (f ^ t) z) atTop (𝓝 0)}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
    simpa using hx.add hy
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, map_smul] at hx ⊢
    simpa using hx.const_smul c

theorem mem_convSubspace {f : End ℂ V} {z : V} :
    z ∈ convSubspace f ↔ Tendsto (fun t => (f ^ t) z) atTop (𝓝 0) := Iff.rfl

/-- On the generalized eigenspace of `|μ| < 1`, orbits converge to zero. -/
theorem tendsto_of_mem_maxGenEigenspace {f : End ℂ V} {μ : ℂ} (hμ : ‖μ‖ < 1) {v : V}
    (hv : v ∈ f.maxGenEigenspace μ) : Tendsto (fun t => (f ^ t) v) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ v).1 hv
  set N := f - μ • (1 : End ℂ V)
  have hcomm : ∀ t, N * f ^ t = f ^ t * N := fun t =>
    ((Commute.sub_left (Commute.refl f) (Commute.smul_left (Commute.one_left f) μ)).pow_right t).eq
  induction k generalizing v with
  | zero => simp only [pow_zero, Module.End.one_apply] at hk; subst hk; simp
  | succ k ih =>
    have hNv : (N ^ k) (N v) = 0 := by rw [← Module.End.mul_apply, ← pow_succ]; exact hk
    have hNv' := ih (Module.End.mem_maxGenEigenspace f μ (N v) |>.2 ⟨k, hNv⟩) hNv
    refine tendsto_zero_of_rec hμ hNv' fun t => ?_
    have h1 : ∀ w, f w = μ • w + N w := fun w => by simp [N]
    calc (f ^ (t + 1)) v = f ((f ^ t) v) := by rw [pow_succ', Module.End.mul_apply]
      _ = μ • (f ^ t) v + N ((f ^ t) v) := h1 _
      _ = μ • (f ^ t) v + (f ^ t) (N v) := by
        rw [← Module.End.mul_apply, hcomm t, Module.End.mul_apply]

/-- Along an eigenvector of `|μ| ≥ 1`, the orbit does not converge to zero. -/
theorem not_tendsto_of_eigen {f : End ℂ V} {μ : ℂ} (hμ : 1 ≤ ‖μ‖) {v : V} (hv : f v = μ • v)
    (hv0 : v ≠ 0) : ¬ Tendsto (fun t => (f ^ t) v) atTop (𝓝 0) := by
  intro h
  have hpow : ∀ t, (f ^ t) v = μ ^ t • v := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  have hn := (tendsto_zero_iff_norm_tendsto_zero.1 h)
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have : ∀ t, ‖v‖ ≤ ‖(f ^ t) v‖ := fun t => by
    rw [hpow, norm_smul, norm_pow]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hμ)
  have := ge_of_tendsto' hn this
  linarith

theorem stable_le_conv (f : End ℂ V) : stableSubspace f ≤ convSubspace f :=
  iSup₂_le fun _ hμ _ hv => tendsto_of_mem_maxGenEigenspace hμ hv

theorem stable_sup_unstable [FiniteDimensional ℂ V] (f : End ℂ V) :
    stableSubspace f ⊔ unstableSubspace f = ⊤ := by
  refine eq_top_iff.2 ((Module.End.iSup_maxGenEigenspace_eq_top f).symm.le.trans
    (iSup_le fun μ => ?_))
  rcases lt_or_ge ‖μ‖ 1 with h | h
  · exact le_sup_of_le_left (le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from h))
  · exact le_sup_of_le_right (le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | 1 ≤ ‖μ‖} from h))

theorem disjoint_stable_unstable (f : End ℂ V) :
    Disjoint (stableSubspace f) (unstableSubspace f) :=
  (Module.End.independent_maxGenEigenspace f).disjoint_biSup_biSup
    (Set.disjoint_left.2 fun μ h1 h2 => by
      simp only [Set.mem_ofPred_eq] at h1 h2; linarith)

theorem unstable_invariant (f : End ℂ V) {z : V} (hz : z ∈ unstableSubspace f) :
    f z ∈ unstableSubspace f := by
  have : unstableSubspace f ≤ (unstableSubspace f).comap f := iSup₂_le fun μ hμ v hv =>
    (le_biSup (fun μ => f.maxGenEigenspace μ) hμ)
      (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hv)
  exact this hz

/-- **Orbits converge to zero exactly on the stable subspace.** -/
theorem tendsto_iff_mem_stable [FiniteDimensional ℂ V] (f : End ℂ V) (z : V) :
    Tendsto (fun t => (f ^ t) z) atTop (𝓝 0) ↔ z ∈ stableSubspace f := by
  refine ⟨fun hz => ?_, fun hz => stable_le_conv f hz⟩
  -- the convergent vectors meet the unstable subspace only in zero
  set W := convSubspace f ⊓ unstableSubspace f
  have hWinv : ∀ w ∈ W, f w ∈ W := fun w hw => ⟨by
    change Tendsto _ _ _
    have := (mem_convSubspace.1 hw.1).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, pow_succ, Module.End.mul_apply] using this,
    unstable_invariant f hw.2⟩
  have hW : W = ⊥ := by
    by_contra hne
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hWinv)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hfw : f w = μ • (w : V) := by
      have := Module.End.mem_eigenspace_iff.1 hw.1
      rw [Subtype.ext_iff] at this
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hstab : ‖μ‖ < 1 := by
      by_contra hge
      exact not_tendsto_of_eigen (not_lt.1 hge) hfw hw0 (mem_convSubspace.1 w.2.1)
    have hs : (w : V) ∈ stableSubspace f := le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hstab)
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hfw))
    exact hw0 ((Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs w.2.2)
  -- split `z` along stable ⊕ unstable
  have hztop : z ∈ stableSubspace f ⊔ unstableSubspace f := by
    rw [stable_sup_unstable]; exact Submodule.mem_top
  obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.1 hztop
  have huc : u ∈ convSubspace f := by
    have := (convSubspace f).sub_mem hz (stable_le_conv f hs)
    simpa using this
  have hu0 : u = 0 := by
    have : u ∈ W := ⟨huc, hu⟩
    rw [hW] at this
    exact (Submodule.mem_bot ℂ).1 this
  simpa [hu0] using hs

/-- If every eigenvalue lies inside the unit disc, the stable subspace is everything. -/
theorem stable_eq_top [FiniteDimensional ℂ V] (f : End ℂ V)
    (h : ∀ μ, f.HasEigenvalue μ → ‖μ‖ < 1) : stableSubspace f = ⊤ := by
  have hu : unstableSubspace f = ⊥ := by
    by_contra hne
    have : Nontrivial (unstableSubspace f) := Submodule.nontrivial_iff_ne_bot.2 hne
    have hinv : ∀ w ∈ unstableSubspace f, f w ∈ unstableSubspace f := fun w hw =>
      unstable_invariant f hw
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict hinv)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hfw : f w = μ • (w : V) := by
      have := Module.End.mem_eigenspace_iff.1 hw.1
      rw [Subtype.ext_iff] at this
      simpa [LinearMap.restrict_apply] using this
    have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
    have hstab := h μ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hfw, hw0⟩)
    have hs : (w : V) ∈ stableSubspace f := le_biSup (fun μ => f.maxGenEigenspace μ)
      (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hstab)
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hfw))
    exact hw0 ((Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs w.2)
  have := stable_sup_unstable f
  rwa [hu, sup_bot_eq] at this

/-! ### Matrices -/

variable {ι : Type*}

/-- A real vector as a complex vector. -/
def cplx (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

theorem cplx_sub (x y : ι → ℝ) : cplx (x - y) = cplx x - cplx y := by
  funext i; simp [cplx]

theorem cplx_add (x y : ι → ℝ) : cplx (x + y) = cplx x + cplx y := by
  funext i; simp [cplx]

theorem tendsto_cplx_iff {y : ℕ → ι → ℝ} :
    Tendsto (fun t => cplx (y t)) atTop (𝓝 0) ↔ Tendsto y atTop (𝓝 0) := by
  simp only [tendsto_pi_nhds, cplx, Pi.zero_apply]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h => ?_⟩
  · have := (Complex.continuous_re.tendsto 0).comp h
    simpa [Function.comp_def] using this
  · have := (Complex.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using this

variable [Fintype ι] [DecidableEq ι]

/-- `A` acting on `ℂⁿ`. -/
noncomputable def cplxEnd (A : Matrix (ι) (ι) ℝ) : End ℂ (ι → ℂ) :=
  Matrix.toLin' (A.map Complex.ofRealHom)

theorem cplxEnd_pow_cplx (A : Matrix (ι) (ι) ℝ) (t : ℕ) (z : ι → ℝ) :
    (cplxEnd A ^ t) (cplx z) = cplx ((A ^ t) *ᵥ z) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← Matrix.mulVec_mulVec]
    funext i
    simp only [cplxEnd, Matrix.toLin'_apply, cplx]
    exact (RingHom.map_mulVec Complex.ofRealHom A _ i).symm

/-- The characteristic roots of `A` are the eigenvalues of `A` on `ℂⁿ`. -/
theorem hasEigenvalue_cplxEnd_iff (A : Matrix (ι) (ι) ℝ) (μ : ℂ) :
    (cplxEnd A).HasEigenvalue μ ↔ (A.charpoly.map Complex.ofRealHom).IsRoot μ := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, cplxEnd, Matrix.charpoly_toLin',
    Matrix.charpoly_map]

/-! ### The dimension of the stable subspace -/

variable [FiniteDimensional ℂ V]

/-- The generalized eigenspaces are independent, so their dimensions add. -/
theorem finrank_biSup_maxGenEigenspace (f : Module.End ℂ V) (T : Finset ℂ) :
    finrank ℂ ↥(⨆ μ ∈ T, f.maxGenEigenspace μ) = ∑ μ ∈ T, finrank ℂ (f.maxGenEigenspace μ) := by
  refine Finset.induction_on T (by simp) ?_
  intro a T ha ih
  rw [Finset.sum_insert ha, ← ih, Finset.iSup_insert]
  have hdis : Disjoint (f.maxGenEigenspace a) (⨆ μ ∈ T, f.maxGenEigenspace μ) := by
    have := (Module.End.independent_maxGenEigenspace f).disjoint_biSup (y := (T : Set ℂ))
      (by simpa using ha)
    simpa using this
  have := Submodule.finrank_sup_add_finrank_inf_eq (f.maxGenEigenspace a)
    (⨆ μ ∈ T, f.maxGenEigenspace μ)
  rw [hdis.eq_bot, finrank_bot, add_zero] at this
  exact this

/-- **The dimension of the stable subspace** is the number of characteristic roots, with
multiplicity, inside the unit circle. -/
theorem finrank_stableSubspace (f : Module.End ℂ V) :
    finrank ℂ (stableSubspace f) = (f.charpoly.roots.filter fun μ => ‖μ‖ < 1).card := by
  set T := (f.charpoly.roots.filter fun μ => ‖μ‖ < 1).toFinset
  have hT : ∀ μ, μ ∈ T ↔ μ ∈ f.charpoly.roots ∧ ‖μ‖ < 1 := fun μ => by
    simp [T]
  have hbot : ∀ μ, μ ∉ f.charpoly.roots → f.maxGenEigenspace μ = ⊥ := fun μ hμ => by
    rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq]
    exact Polynomial.rootMultiplicity_eq_zero fun h =>
      hμ ((Polynomial.mem_roots f.charpoly_monic.ne_zero).2 h)
  have heq : stableSubspace f = ⨆ μ ∈ T, f.maxGenEigenspace μ := by
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => ?_)
    · by_cases hr : μ ∈ f.charpoly.roots
      · exact le_biSup (fun μ => f.maxGenEigenspace μ) ((hT μ).2 ⟨hr, hμ⟩)
      · rw [hbot μ hr]; exact bot_le
    · exact le_biSup (fun μ => f.maxGenEigenspace μ) (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from
        ((hT μ).1 hμ).2)
  rw [heq, finrank_biSup_maxGenEigenspace, ← Multiset.toFinset_sum_count_eq]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [LinearMap.finrank_maxGenEigenspace_eq,
    Multiset.count_filter_of_pos (p := fun μ : ℂ => ‖μ‖ < 1) ((hT μ).1 hμ).2,
    Polynomial.count_roots]

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The real stable and unstable subspaces of a real matrix

Copied from `RecursiveMethods/DeterministicDynamics` (`RealSplitting.lean`); used for Miao,
§1.4.1, pp. 19–23 (the split `x* = (s, u)`). For a real matrix `A`, the complex stable and
unstable subspaces of `A` acting on `ℂⁿ` (`Spectral`) are closed under complex conjugation,
because conjugation maps the generalized eigenspace of `μ` onto that of `μ̄`
(`conjV_mem_maxGenEigenspace`). Hence the real vectors split.

* `stableR A`: the real vectors with `Aᵗz → 0`; `unstableR A`: the real vectors lying in the
  complex unstable subspace. Both are `A`-invariant (`stableR_invariant`,
  `unstableR_invariant`).
* `isCompl_stableR_unstableR`: `ℝⁿ = E_s ⊕ E_u`. A real `z` splits in `ℂⁿ` as `s + u`; taking
  conjugates and using uniqueness of the splitting, `s` and `u` are real.
* `finrank_stableR`: `dim E_s` is the number of characteristic roots (with multiplicity) inside
  the unit circle. A real basis of `E_s` stays independent over `ℂ` (`linearIndependent_cplx`),
  so `dim_ℝ E_s ≤ dim_ℂ S` and `dim_ℝ E_u ≤ dim_ℂ U`, and both sides add up to `n`.
* `unstableR_ker`: `A` is injective on `E_u` (an eigenvalue `0` would be stable).
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix ComplexConjugate

variable {ι : Type*}

/-- Componentwise complex conjugation. -/
def conjV (w : ι → ℂ) : ι → ℂ := fun i => conj (w i)

theorem conjV_conjV (w : ι → ℂ) : conjV (conjV w) = w := by
  funext i; simp [conjV]

theorem conjV_add (w w' : ι → ℂ) : conjV (w + w') = conjV w + conjV w' := by
  funext i; simp [conjV]

theorem conjV_sub (w w' : ι → ℂ) : conjV (w - w') = conjV w - conjV w' := by
  funext i; simp [conjV]

theorem conjV_smul (c : ℂ) (w : ι → ℂ) : conjV (c • w) = conj c • conjV w := by
  funext i; simp [conjV]

theorem conjV_zero : conjV (0 : ι → ℂ) = 0 := by funext i; simp [conjV]

theorem conjV_cplx (z : ι → ℝ) : conjV (cplx z) = cplx z := by
  funext i; simp [conjV, cplx]

/-- A conjugation-fixed complex vector is real. -/
theorem eq_cplx_re {w : ι → ℂ} (hw : conjV w = w) : w = cplx fun i => (w i).re := by
  funext i
  have := congrFun hw i
  simp only [conjV] at this
  exact (Complex.conj_eq_iff_re.1 this).symm

variable [Fintype ι] [DecidableEq ι]

theorem cplxEnd_conjV (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    cplxEnd A (conjV w) = conjV (cplxEnd A w) := by
  funext i
  simp [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, conjV, map_sum]

theorem pow_sub_conjV (A : Matrix ι ι ℝ) (μ : ℂ) (k : ℕ) (w : ι → ℂ) :
    ((cplxEnd A - conj μ • (1 : Module.End ℂ (ι → ℂ))) ^ k) (conjV w) =
      conjV (((cplxEnd A - μ • (1 : Module.End ℂ (ι → ℂ))) ^ k) w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, cplxEnd_conjV,
      conjV_sub, conjV_smul]

/-- Conjugation maps the generalized eigenspace of `μ` into that of `μ̄`. -/
theorem conjV_mem_maxGenEigenspace (A : Matrix ι ι ℝ) {μ : ℂ} {w : ι → ℂ}
    (hw : w ∈ (cplxEnd A).maxGenEigenspace μ) :
    conjV w ∈ (cplxEnd A).maxGenEigenspace (conj μ) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
  exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [pow_sub_conjV, hk, conjV_zero]⟩

/-- A union of generalized eigenspaces over a conjugation-closed set of eigenvalues is closed
under conjugation. -/
theorem conjV_mem_biSup (A : Matrix ι ι ℝ) {s : Set ℂ} (hs : ∀ μ ∈ s, conj μ ∈ s) {w : ι → ℂ}
    (hw : w ∈ ⨆ μ ∈ s, (cplxEnd A).maxGenEigenspace μ) :
    conjV w ∈ ⨆ μ ∈ s, (cplxEnd A).maxGenEigenspace μ := by
  refine Submodule.iSup_induction _ (motive := fun x => conjV x ∈ _) hw (fun μ x hx => ?_)
    (by rw [conjV_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by rw [conjV_add]; exact Submodule.add_mem _ hx hy)
  refine Submodule.iSup_induction _ (motive := fun x => conjV x ∈ _) hx (fun hμ y hy => ?_)
    (by rw [conjV_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by rw [conjV_add]; exact Submodule.add_mem _ hx hy)
  exact (le_biSup (fun μ => (cplxEnd A).maxGenEigenspace μ) (hs μ hμ))
    (conjV_mem_maxGenEigenspace A hy)

theorem conjV_mem_stable (A : Matrix ι ι ℝ) {w : ι → ℂ}
    (hw : w ∈ stableSubspace (cplxEnd A)) : conjV w ∈ stableSubspace (cplxEnd A) :=
  conjV_mem_biSup A (fun μ hμ => by simpa using hμ) hw

theorem conjV_mem_unstable (A : Matrix ι ι ℝ) {w : ι → ℂ}
    (hw : w ∈ unstableSubspace (cplxEnd A)) : conjV w ∈ unstableSubspace (cplxEnd A) :=
  conjV_mem_biSup A (fun μ hμ => by simpa using hμ) hw

/-! ### The real subspaces -/

/-- `ℝⁿ → ℂⁿ` as a real-linear map. -/
def cplxL : (ι → ℝ) →ₗ[ℝ] (ι → ℂ) where
  toFun := cplx
  map_add' := cplx_add
  map_smul' c z := by funext i; simp [cplx, Complex.real_smul]

/-- The real stable subspace `E_s = {z : Aᵗz → 0}`. -/
noncomputable def stableR (A : Matrix ι ι ℝ) : Submodule ℝ (ι → ℝ) :=
  ((stableSubspace (cplxEnd A)).restrictScalars ℝ).comap cplxL

/-- The real unstable subspace `E_u`. -/
noncomputable def unstableR (A : Matrix ι ι ℝ) : Submodule ℝ (ι → ℝ) :=
  ((unstableSubspace (cplxEnd A)).restrictScalars ℝ).comap cplxL

theorem mem_stableR {A : Matrix ι ι ℝ} {z : ι → ℝ} :
    z ∈ stableR A ↔ cplx z ∈ stableSubspace (cplxEnd A) := Iff.rfl

theorem mem_unstableR {A : Matrix ι ι ℝ} {z : ι → ℝ} :
    z ∈ unstableR A ↔ cplx z ∈ unstableSubspace (cplxEnd A) := Iff.rfl

/-- `z ∈ E_s` iff `Aᵗz → 0`. -/
theorem mem_stableR_iff (A : Matrix ι ι ℝ) (z : ι → ℝ) :
    z ∈ stableR A ↔ Tendsto (fun t => (A ^ t) *ᵥ z) atTop (𝓝 0) := by
  rw [mem_stableR, ← tendsto_iff_mem_stable, ← tendsto_cplx_iff]
  simp only [cplxEnd_pow_cplx]

theorem cplx_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) : cplx (A *ᵥ z) = cplxEnd A (cplx z) := by
  have := cplxEnd_pow_cplx A 1 z
  simpa using this.symm

theorem stableR_invariant (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ stableR A) :
    A *ᵥ z ∈ stableR A := by
  rw [mem_stableR_iff] at hz ⊢
  have := hz.comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def, pow_succ, Matrix.mulVec_mulVec] using this

theorem unstableR_invariant (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A) :
    A *ᵥ z ∈ unstableR A := by
  rw [mem_unstableR, cplx_mulVec]
  exact unstable_invariant _ hz

/-- **`ℝⁿ = E_s ⊕ E_u`.** -/
theorem isCompl_stableR_unstableR (A : Matrix ι ι ℝ) : IsCompl (stableR A) (unstableR A) := by
  set f := cplxEnd A
  refine ⟨Submodule.disjoint_def.2 fun z hs hu => ?_, codisjoint_iff.2 ?_⟩
  · have h0 := (Submodule.disjoint_def.1 (disjoint_stable_unstable f)) _ hs hu
    funext i
    have := congrFun h0 i
    simpa [cplxL, cplx] using this
  · refine eq_top_iff.2 fun z _ => ?_
    have hz : cplx z ∈ stableSubspace f ⊔ unstableSubspace f := by
      rw [stable_sup_unstable]; exact Submodule.mem_top
    obtain ⟨s, hs, u, hu, hsu⟩ := Submodule.mem_sup.1 hz
    -- conjugating the splitting gives another splitting, so `s` and `u` are real
    have hcs := conjV_mem_stable A hs
    have hcu := conjV_mem_unstable A hu
    have hsplit : conjV s + conjV u = s + u := by rw [← conjV_add, hsu, conjV_cplx]
    have hd : s - conjV s = conjV u - u := by
      rw [sub_eq_sub_iff_add_eq_add, ← hsplit, add_comm]
    have hmem : s - conjV s ∈ stableSubspace f ⊓ unstableSubspace f :=
      ⟨Submodule.sub_mem _ hs hcs, hd ▸ Submodule.sub_mem _ hcu hu⟩
    rw [(disjoint_stable_unstable f).eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
    have hs' := eq_cplx_re hmem.symm
    have hu' : conjV u = u := by
      have := hsplit; rw [← hmem] at this; exact add_left_cancel this
    have hu'' := eq_cplx_re hu'
    refine Submodule.mem_sup.2 ⟨fun i => (s i).re, ?_, fun i => (u i).re, ?_, ?_⟩
    · rw [mem_stableR, ← hs']; exact hs
    · rw [mem_unstableR, ← hu'']; exact hu
    · funext i
      have := congrFun hsu i
      simp only [Pi.add_apply, cplx] at this
      have := congrArg Complex.re this
      simpa using this

omit [Fintype ι] [DecidableEq ι] in
/-- Real vectors independent over `ℝ` are independent over `ℂ`. -/
theorem linearIndependent_cplx {κ : Type*} [Finite κ] {v : κ → ι → ℝ}
    (hv : LinearIndependent ℝ v) : LinearIndependent ℂ fun k => cplx (v k) := by
  have : Fintype κ := Fintype.ofFinite κ
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc k
  have hre : ∀ i, ∑ k, (c k).re * v k i = 0 := fun i => by
    have := congrArg Complex.re (congrFun hc i)
    simpa [cplx, Finset.sum_apply, Complex.re_sum, Complex.mul_re] using this
  have him : ∀ i, ∑ k, (c k).im * v k i = 0 := fun i => by
    have := congrArg Complex.im (congrFun hc i)
    simpa [cplx, Finset.sum_apply, Complex.im_sum, Complex.mul_im] using this
  have h1 := hv (fun k => (c k).re) (by funext i; simpa [Finset.sum_apply] using hre i) k
  have h2 := hv (fun k => (c k).im) (by funext i; simpa [Finset.sum_apply] using him i) k
  exact Complex.ext h1 h2

omit [Fintype ι] [DecidableEq ι] in
/-- `dim_ℝ` of a real subspace is at most `dim_ℂ` of a complex subspace containing its
complexification. -/
theorem finrank_le_of_cplx [Finite ι] {E : Submodule ℝ (ι → ℝ)} {S : Submodule ℂ (ι → ℂ)}
    (h : ∀ z ∈ E, cplx z ∈ S) : finrank ℝ E ≤ finrank ℂ S := by
  set b := Module.finBasis ℝ E
  have hli : LinearIndependent ℂ fun k => (⟨cplx (b k), h _ (b k).2⟩ : S) := by
    refine LinearIndependent.of_comp S.subtype ?_
    exact linearIndependent_cplx (v := fun k => ((b k : E) : ι → ℝ))
      (b.linearIndependent.map' E.subtype (Submodule.ker_subtype E))
  simpa using hli.fintype_card_le_finrank

/-- **`dim E_s` is the number of characteristic roots inside the unit circle.** -/
theorem finrank_stableR (A : Matrix ι ι ℝ) :
    finrank ℝ (stableR A) =
      ((A.charpoly.map Complex.ofRealHom).roots.filter fun μ => ‖μ‖ < 1).card := by
  set f := cplxEnd A
  have hcp : LinearMap.charpoly f = A.charpoly.map Complex.ofRealHom := by
    simp only [f, cplxEnd]
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  have h1 := finrank_le_of_cplx (E := stableR A) (S := stableSubspace f) fun z hz => hz
  have h2 := finrank_le_of_cplx (E := unstableR A) (S := unstableSubspace f) fun z hz => hz
  have hR := Submodule.finrank_add_eq_of_isCompl (isCompl_stableR_unstableR A)
  have hC : finrank ℂ (stableSubspace f) + finrank ℂ (unstableSubspace f) = Fintype.card ι := by
    rw [Submodule.finrank_add_eq_of_isCompl
      ⟨disjoint_stable_unstable f, codisjoint_iff.2 (stable_sup_unstable f)⟩]
    simp
  simp only [Module.finrank_fintype_fun_eq_card] at hR
  rw [← hcp, ← finrank_stableSubspace]
  omega

/-- `A` is injective on `E_u`: an eigenvector of `0` lies in the stable subspace. -/
theorem unstableR_ker (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A)
    (h0 : A *ᵥ z = 0) : z = 0 := by
  set f := cplxEnd A
  have hf : f (cplx z) = 0 := by rw [← cplx_mulVec, h0]; funext i; simp [cplx]
  have hs : cplx z ∈ stableSubspace f := by
    refine le_biSup (fun μ => f.maxGenEigenspace μ) (show (0 : ℂ) ∈ {μ : ℂ | ‖μ‖ < 1} by simp) ?_
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simpa using hf⟩
  exact (Submodule.disjoint_def.1 (isCompl_stableR_unstableR A).disjoint) z hs hz

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stable estimate

Copied from `RecursiveMethods/DeterministicDynamics` (`Dichotomy.lean`, the part up to the
stable estimate). Used for the geometric bounds in Miao, §1.2, pp. 11–12 and §1.4.1,
pp. 17–23. With `ℝⁿ = E_s ⊕ E_u` (`RealSplitting`) and the projections `P_s`, `Q_u` (`projS`,
`projU`), which commute with `A`:

* `stable_bound`: there is `a < 1` with `‖AᵏP_s z‖ ≤ K aᵏ‖z‖`. Take `a` between the largest
  characteristic root inside the unit circle and `1`; the generalized eigenspaces of `A` and of
  `a⁻¹A` agree (`mem_maxGen_smul`), so `a⁻ᵏAᵏP_s z → 0`, and a bound on a basis is uniform
  (`uniform_bound_of_basis`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bounds on a basis are uniform bounds. -/
theorem uniform_bound_of_basis (T : ℕ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (h : ∀ i, ∃ C, ∀ k, ‖T k (Pi.single i 1)‖ ≤ C) :
    ∃ K, 0 ≤ K ∧ ∀ k z, ‖T k z‖ ≤ K * ‖z‖ := by
  choose C hC using h
  refine ⟨∑ i, max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _, fun k z => ?_⟩
  have hz : z = ∑ i, z i • (Pi.single i 1 : ι → ℝ) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  calc ‖T k z‖ = ‖∑ i, z i • T k (Pi.single i 1)‖ := by
        conv_lhs => rw [hz]
        rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i, ‖z i • T k (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖z‖ * max (C i) 0 := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm z i) ((hC i k).trans (le_max_left _ _))
          (norm_nonneg _) (norm_nonneg _)
    _ = (∑ i, max (C i) 0) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]

omit [DecidableEq ι] in
/-- A convergent sequence of vectors is bounded. -/
theorem exists_bound_of_tendsto {u : ℕ → ι → ℝ} {L : ι → ℝ} (h : Tendsto u atTop (𝓝 L)) :
    ∃ C, ∀ k, ‖u k‖ ≤ C := by
  obtain ⟨C, hC⟩ := h.norm.bddAbove_range
  exact ⟨C, fun k => hC ⟨k, rfl⟩⟩

/-- Scaling an operator scales its generalized eigenvalues. -/
theorem mem_maxGen_smul {V : Type*} [AddCommGroup V] [Module ℂ V] (g : Module.End ℂ V)
    {c ν : ℂ} {w : V} (hw : w ∈ g.maxGenEigenspace ν) :
    w ∈ (c • g).maxGenEigenspace (c * ν) := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hw
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
  have e : c • g - (c * ν) • (1 : Module.End ℂ V) = c • (g - ν • 1) := by
    rw [smul_sub, smul_smul]
  rw [e, smul_pow, LinearMap.smul_apply, hk, smul_zero]

/-! ### The projections -/

/-- The projection onto `E_s` along `E_u`. -/
noncomputable def projS (A : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (stableR A).projection (unstableR A) (isCompl_stableR_unstableR A)

/-- The projection onto `E_u` along `E_s`. -/
noncomputable def projU (A : Matrix ι ι ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (unstableR A).projection (stableR A) (isCompl_stableR_unstableR A).symm

theorem projS_add_projU (A : Matrix ι ι ℝ) (z : ι → ℝ) : projS A z + projU A z = z :=
  Submodule.projection_add_projection_eq_self _ z

theorem projS_mem (A : Matrix ι ι ℝ) (z : ι → ℝ) : projS A z ∈ stableR A :=
  Submodule.projection_apply_mem _ z

theorem projU_mem (A : Matrix ι ι ℝ) (z : ι → ℝ) : projU A z ∈ unstableR A :=
  Submodule.projection_apply_mem _ z

theorem projS_of_mem (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ stableR A) : projS A z = z :=
  Submodule.projection_apply_left _ ⟨z, hz⟩

theorem projS_of_mem_unstable (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A) :
    projS A z = 0 :=
  Submodule.projection_apply_right _ ⟨z, hz⟩

theorem projU_of_mem (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ unstableR A) : projU A z = z :=
  Submodule.projection_apply_left _ ⟨z, hz⟩

theorem projU_of_mem_stable (A : Matrix ι ι ℝ) {z : ι → ℝ} (hz : z ∈ stableR A) :
    projU A z = 0 :=
  Submodule.projection_apply_right _ ⟨z, hz⟩

theorem projS_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) : projS A (A *ᵥ z) = A *ᵥ projS A z := by
  conv_lhs => rw [← projS_add_projU A z, Matrix.mulVec_add, map_add]
  rw [projS_of_mem A (stableR_invariant A (projS_mem A z)),
    projS_of_mem_unstable A (unstableR_invariant A (projU_mem A z)), add_zero]

theorem projU_mulVec (A : Matrix ι ι ℝ) (z : ι → ℝ) : projU A (A *ᵥ z) = A *ᵥ projU A z := by
  conv_lhs => rw [← projS_add_projU A z, Matrix.mulVec_add, map_add]
  rw [projU_of_mem_stable A (stableR_invariant A (projS_mem A z)),
    projU_of_mem A (unstableR_invariant A (projU_mem A z)), zero_add]

theorem pow_mulVec_mem_stableR (A : Matrix ι ι ℝ) (k : ℕ) {z : ι → ℝ} (hz : z ∈ stableR A) :
    (A ^ k) *ᵥ z ∈ stableR A := by
  induction k with
  | zero => simpa using hz
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact stableR_invariant A ih

/-! ### The stable estimate -/

/-- A complex vector in `S` whose `a⁻¹`-scaled orbit decays, when `a` exceeds every root inside
the unit circle. -/
theorem tendsto_scaled_of_stable (A : Matrix ι ι ℝ) {a : ℝ} (ha : 0 < a)
    (hroot : ∀ μ ∈ (A.charpoly.map Complex.ofRealHom).roots, ‖μ‖ < 1 → ‖μ‖ < a)
    {w : ι → ℂ} (hw : w ∈ stableSubspace (cplxEnd A)) :
    Tendsto (fun t => ((((a⁻¹ : ℝ) : ℂ) • cplxEnd A) ^ t) w) atTop (𝓝 0) := by
  set f := cplxEnd A
  have hcp : LinearMap.charpoly f = A.charpoly.map Complex.ofRealHom := by
    simp only [f, cplxEnd]
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map]
  suffices hle : stableSubspace f ≤ convSubspace ((((a⁻¹ : ℝ) : ℂ)) • f) from hle hw
  refine iSup₂_le fun μ hμ => ?_
  by_cases hr : μ ∈ (LinearMap.charpoly f).roots
  · intro v hv
    have hμa : ‖((a⁻¹ : ℝ) : ℂ) * μ‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ha),
        inv_mul_lt_iff₀ ha, mul_one]
      exact hroot μ (hcp ▸ hr) hμ
    exact tendsto_of_mem_maxGenEigenspace hμa (mem_maxGen_smul f hv)
  · have : f.maxGenEigenspace μ = ⊥ := by
      rw [← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_eq_zero fun h =>
        hr ((Polynomial.mem_roots f.charpoly_monic.ne_zero).2 h)
    rw [this]; exact bot_le

theorem scaled_pow_cplx (A : Matrix ι ι ℝ) (s : ℝ) (t : ℕ) (z : ι → ℝ) :
    ((((s : ℂ)) • cplxEnd A) ^ t) (cplx z) = cplx (s ^ t • (A ^ t) *ᵥ z) := by
  rw [smul_pow, LinearMap.smul_apply, cplxEnd_pow_cplx]
  funext i; simp [cplx, Matrix.mulVec, dotProduct]

/-- **The stable estimate.** -/
theorem stable_bound (A : Matrix ι ι ℝ) :
    ∃ a, 0 < a ∧ a < 1 ∧ ∃ K, 0 ≤ K ∧ ∀ k z, ‖(A ^ k) *ᵥ projS A z‖ ≤ K * a ^ k * ‖z‖ := by
  set T := ((A.charpoly.map Complex.ofRealHom).roots.filter fun μ => ‖μ‖ < 1).toFinset
  set ρ : ℝ := ((T.sup fun μ => ‖μ‖₊ : NNReal) : ℝ)
  have hρ0 : 0 ≤ ρ := NNReal.coe_nonneg _
  have hρ1 : ρ < 1 := by
    have : (T.sup fun μ => ‖μ‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by norm_num)]
      intro μ hμ
      have := (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hμ)).2
      exact_mod_cast this
    exact_mod_cast this
  set a := (ρ + 1) / 2
  have ha0 : 0 < a := by simp only [a]; linarith
  have ha1 : a < 1 := by simp only [a]; linarith
  have hroot : ∀ μ ∈ (A.charpoly.map Complex.ofRealHom).roots, ‖μ‖ < 1 → ‖μ‖ < a :=
    fun μ hμ h1 => by
      have hT : μ ∈ T := Multiset.mem_toFinset.2 (Multiset.mem_filter.2 ⟨hμ, h1⟩)
      have : ‖μ‖₊ ≤ T.sup fun μ => ‖μ‖₊ := Finset.le_sup (f := fun μ => ‖μ‖₊) hT
      have : ‖μ‖ ≤ ρ := by exact_mod_cast this
      simp only [a]; linarith
  set L : ℕ → (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := fun k =>
    (a⁻¹) ^ k • (Matrix.toLin' (A ^ k) ∘ₗ projS A)
  have hL : ∀ k z, L k z = (a⁻¹) ^ k • (A ^ k) *ᵥ projS A z := fun k z => by
    simp only [L, LinearMap.smul_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
  obtain ⟨K, hK0, hK⟩ := uniform_bound_of_basis L fun i => by
    have hs : cplx (projS A (Pi.single i 1)) ∈ stableSubspace (cplxEnd A) := projS_mem A _
    have h := tendsto_scaled_of_stable A ha0 hroot hs
    simp only [scaled_pow_cplx] at h
    obtain ⟨C, hC⟩ := exists_bound_of_tendsto (tendsto_cplx_iff.1 h)
    exact ⟨C, fun k => by rw [hL]; exact hC k⟩
  refine ⟨a, ha0, ha1, K, hK0, fun k z => ?_⟩
  have h1 := hK k z
  rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (inv_pos.2 ha0) k), inv_pow,
    inv_mul_le_iff₀ (pow_pos ha0 k)] at h1
  linarith

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# First-order linear systems: regularity, steady state, stable matrices

Miao, §1.4, pp. 15–18, for the system `Ax_{t+1} = Bx_t + Cz_t` (1.20). (The companion form
(1.19) is treated elsewhere.)

* **Stable matrices** (Definition 1.4.5): for a real matrix `A`, `IsStableMatrix (A.map ofReal)`
  is the root condition on the characteristic polynomial (`isStableMatrix_iff_roots`), and
  holds iff `Aᵗv → 0` for every real `v` (`isStableMatrix_iff_tendsto`); then the decay is
  geometric, `‖Aᵏv‖ ≤ K aᵏ‖v‖` with `a < 1` (`hasGeomDecay_of_isStableMatrix`).
* **Footnote 2** (`footnote_2`, `isRegular_of_isUnit_det`): if `A` is nonsingular,
  `det(Az − B) ≠ 0` whenever `z` is not an eigenvalue of `A⁻¹B`, so the pair is regular.
* **The scalar example** (p. 16): `a = b = 0` is not regular, and `0 = 0·x_t + cz_t` has no
  solution once `cz_t ≠ 0` (`example_scalar_not_regular`, `example_scalar_no_solution`).
* **Non-regular pairs** (p. 16). The book argues that if `det(Aα − B) = 0` for all `α` then
  (1.20) has no solution for generic `z`. As stated this is false: for `A = B = diag(1, 0)` and
  `C = (1, 0)'` the pair is singular for every `α`, yet (1.20) has a solution for every `z`
  (`remark_nonregular_counterexample`). The argument (a polynomial `ψ` with
  `ψ(α)(Aα − B) = 0`, so `ψ(L⁻¹)Cz_t = 0`) needs `ψ(α)C ≠ 0`. Proved here
  (`remark_nonregular_no_solution`): if the pair is singular for every `α` and `C` has a right
  inverse (full row rank), there is a forcing sequence, zero from some date on, for which
  (1.20) has no solution. The polynomial `ψ` is a left null vector of `XA − B` over `ℝ[X]`.
* **The steady state (1.21)** (Assumption 1.4.2): if `A − B` is invertible, `x̄ = (A − B)⁻¹Cz̄`
  is the unique point with `Ax̄ = Bx̄ + Cz̄` (`eq_1_21`); the constant sequence solves the
  stationary system (`eq_1_21_solution`); and, for nonsingular `A`, a solution that reaches `x̄`
  after `T` stays there (`eq_1_21_steadyState`). Definition 1.4.1 alone does not single out
  `x̄`: every point a sequence never visits is vacuously a steady state of it
  (`isSteadyStateOf_of_not_mem_range`), so "unique" refers to the stationary equation.

General tools for later modules: `HasGeomDecay`, bounds for matrices acting on vectors, the
backward solution of `x_{t+1} = Wx_t + g_t` (`backward_sol_eq`) and its boundedness, geometric
series of matrix powers (`summable_geom_series`, `tsum_geom_series_succ`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix

/-! ### Stable matrices -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Definition 1.4.5** (Miao, p. 18) for real matrices: `A.map ofReal` is stable iff every root
of the characteristic polynomial of `A` has modulus less than one. -/
theorem isStableMatrix_iff_roots (A : Matrix ι ι ℝ) :
    IsStableMatrix (A.map Complex.ofRealHom) ↔
      ∀ μ : ℂ, (A.charpoly.map Complex.ofRealHom).IsRoot μ → ‖μ‖ < 1 :=
  forall_congr' fun μ => by rw [← hasEigenvalue_cplxEnd_iff]; rfl

/-- A stable real matrix drives every orbit to zero. -/
theorem tendsto_of_isStableMatrix (A : Matrix ι ι ℝ) (h : IsStableMatrix (A.map Complex.ofRealHom))
    (v : ι → ℝ) : Tendsto (fun t => (A ^ t) *ᵥ v) atTop (𝓝 0) := by
  have htop := stable_eq_top (cplxEnd A) h
  have := (tendsto_iff_mem_stable (cplxEnd A) (cplx v)).2 (by rw [htop]; exact Submodule.mem_top)
  simp only [cplxEnd_pow_cplx] at this
  exact tendsto_cplx_iff.1 this

/-- If every real orbit converges to zero, the matrix is stable. -/
theorem isStableMatrix_of_tendsto (A : Matrix ι ι ℝ)
    (h : ∀ v : ι → ℝ, Tendsto (fun t => (A ^ t) *ᵥ v) atTop (𝓝 0)) :
    IsStableMatrix (A.map Complex.ofRealHom) := by
  intro μ hμ
  by_contra hge
  push Not at hge
  obtain ⟨w, hw⟩ := (show (cplxEnd A).HasEigenvalue μ from hμ).exists_hasEigenvector
  have hfw : cplxEnd A w = μ • w := Module.End.mem_eigenspace_iff.1 hw.1
  set r : ι → ℝ := fun i => (w i).re
  set q : ι → ℝ := fun i => (w i).im
  have hwrq : w = cplx r + Complex.I • cplx q := by
    funext i
    simp only [r, q, cplx, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hc : Tendsto (fun t => (cplxEnd A ^ t) w) atTop (𝓝 0) := by
    have h1 := tendsto_cplx_iff.2 (h r)
    have h2 := (tendsto_cplx_iff.2 (h q)).const_smul Complex.I
    rw [smul_zero] at h2
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr fun t => ?_
    rw [hwrq, map_add, map_smul, cplxEnd_pow_cplx, cplxEnd_pow_cplx]
  exact not_tendsto_of_eigen hge hfw hw.2 hc

/-- A real matrix is stable iff all its orbits converge to zero. -/
theorem isStableMatrix_iff_tendsto (A : Matrix ι ι ℝ) :
    IsStableMatrix (A.map Complex.ofRealHom) ↔
      ∀ v : ι → ℝ, Tendsto (fun t => (A ^ t) *ᵥ v) atTop (𝓝 0) :=
  ⟨tendsto_of_isStableMatrix A, isStableMatrix_of_tendsto A⟩

/-- Geometric decay of the powers of `M` acting on vectors: `‖Mᵏz‖ ≤ K aᵏ‖z‖`, `0 ≤ a < 1`. -/
def HasGeomDecay (M : Matrix ι ι ℝ) (K a : ℝ) : Prop :=
  0 ≤ a ∧ a < 1 ∧ 0 ≤ K ∧ ∀ k z, ‖(M ^ k) *ᵥ z‖ ≤ K * a ^ k * ‖z‖

/-- A stable real matrix has geometrically decaying powers. -/
theorem hasGeomDecay_of_isStableMatrix (A : Matrix ι ι ℝ)
    (h : IsStableMatrix (A.map Complex.ofRealHom)) : ∃ K a, HasGeomDecay A K a := by
  obtain ⟨a, ha0, ha1, K, hK0, hK⟩ := stable_bound A
  have hS : ∀ z, projS A z = z := fun z => projS_of_mem A (by
    rw [mem_stableR, stable_eq_top (cplxEnd A) h]; exact Submodule.mem_top)
  exact ⟨K, a, ha0.le, ha1, hK0, fun k z => by simpa [hS] using hK k z⟩

/-- If every eigenvalue of `M` has modulus greater than one, `M` is invertible and `M⁻¹` is
stable. -/
theorem isStableMatrix_inv (M : Matrix ι ι ℝ)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (M.map Complex.ofRealHom)) μ →
      1 < ‖μ‖) :
    IsUnit M.det ∧ IsStableMatrix (M⁻¹.map Complex.ofRealHom) := by
  set f := Complex.ofRealHom
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h0' : (M.map f).det = 0 := by
      rw [show M.map f = f.mapMatrix M from rfl, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    have := h 0 (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMv), hv⟩)
    norm_num at this
  refine ⟨hdet, fun ν hν => ?_⟩
  obtain ⟨w, hw⟩ := hν.exists_hasEigenvector
  have hw1 : M⁻¹.map f *ᵥ w = ν • w := by
    simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hw.1
  have hMM : M.map f * M⁻¹.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have hw2 : w = ν • (M.map f *ᵥ w) := by
    have := congrArg (fun v => M.map f *ᵥ v) hw1
    simp only [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec, Matrix.mulVec_smul] at this
    exact this
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hw2
    exact hw.2 hw2
  have hMw : M.map f *ᵥ w = ν⁻¹ • w := by
    conv_rhs => rw [hw2]
    rw [smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have := h ν⁻¹ (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMw), hw.2⟩)
  rw [norm_inv] at this
  have hpos : 0 < ‖ν‖ := norm_pos_iff.2 hν0
  rwa [one_lt_inv₀ hpos] at this

/-! ### Footnote 2 and the scalar example -/

/-- **Footnote 2** (Miao, p. 17): if `A` is nonsingular and `z` is not an eigenvalue of
`A⁻¹B`, then `det(Az − B) = det(A) det(Iz − A⁻¹B) ≠ 0`. -/
theorem footnote_2 {K n : Type*} [Field K] [Fintype n] [DecidableEq n] (A B : Matrix n n K)
    (hA : IsUnit A.det) (z : K)
    (hz : ¬ Module.End.HasEigenvalue (Matrix.toLin' (A⁻¹ * B)) z) : (z • A - B).det ≠ 0 := by
  have hfac : z • A - B = A * (z • 1 - A⁻¹ * B) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
  rw [hfac, Matrix.det_mul]
  refine mul_ne_zero hA.ne_zero fun h0 => hz ?_
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hv⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
  rw [Matrix.toLin'_apply]
  exact hMv.symm

/-- Miao, p. 17: a pair with `A` nonsingular is regular (Assumption 1.4.1), over any infinite
field: `A⁻¹B` has finitely many eigenvalues. -/
theorem isRegular_of_isUnit_det {K n : Type*} [Field K] [Infinite K] [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (hA : IsUnit A.det) : IsRegular A B := by
  classical
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (A⁻¹ * B).charpoly.roots.toFinset
  refine ⟨z, footnote_2 A B hA z fun he => hz ?_⟩
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin'] at he
  exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).2 he)

/-- Miao, p. 16: the scalar pair `a = b = 0` violates Assumption 1.4.1. -/
theorem example_scalar_not_regular : ¬ IsRegular (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 := by
  rintro ⟨α, hα⟩
  simp at hα

/-- Miao, p. 16: with `a = b = 0`, `ax_{t+1} = bx_t + cz_t` has no solution once `cz_t ≠ 0`. -/
theorem example_scalar_no_solution (c : ℝ) (z : ℕ → Fin 1 → ℝ) (t : ℕ) (hcz : c * z t 0 ≠ 0)
    (x : ℕ → Fin 1 → ℝ) :
    ¬ IsSolution (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 (Matrix.of fun _ _ => c) z x := by
  intro hx
  have h1 : c * z t 0 = 0 := by simpa [Matrix.mulVec, dotProduct] using (congrFun (hx t) 0).symm
  exact hcz h1

/-! ### Non-regular pairs -/

/-- Miao, p. 16, corrected: if `det(αA − B) = 0` for every `α` and `C` has full row rank
(`CD = I`), then there is a forcing sequence, zero from some date on, for which (1.20) has no
solution. The book's `ψ` is a nonzero `v` with `v(XA − B) = 0` over `ℝ[X]`; its coefficients
`ψ_k` satisfy `ψ_kA = ψ_{k+1}B` and `ψ_0B = 0`, so `∑_k ψ_k ⬝ Cz_k = 0` along any solution. -/
theorem remark_nonregular_no_solution {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (hreg : ¬ IsRegular A B) (D : Matrix m n ℝ)
    (hCD : C * D = 1) :
    ∃ z : ℕ → m → ℝ, (∃ T, ∀ t, T ≤ t → z t = 0) ∧ ∀ x, ¬ IsSolution A B C z x := by
  classical
  set M : Matrix n n (Polynomial ℝ) :=
    Matrix.of fun i j => Polynomial.X * Polynomial.C (A i j) - Polynomial.C (B i j)
  have hdet : M.det = 0 := by
    refine Polynomial.funext fun α => ?_
    rw [Polynomial.eval_zero, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    have hα : ¬ (α • A - B).det ≠ 0 := fun h => hreg ⟨α, h⟩
    push Not at hα
    convert hα using 2
    ext i j
    simp [M]
    ring
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  set ψ : ℕ → n → ℝ := fun k i => (v i).coeff k
  -- the coefficient relations
  have hrel : ∀ k, ψ k ᵥ* A = ψ (k + 1) ᵥ* B := fun k => by
    funext j
    have := congrArg (fun p => Polynomial.coeff p (k + 1)) (congrFun hvM j)
    simp only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply,
      Polynomial.coeff_zero, Polynomial.finsetSum_coeff, mul_sub, ← mul_assoc,
      Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X,
      Finset.sum_sub_distrib] at this
    simp only [Matrix.vecMul, dotProduct, ψ]
    linarith
  have h0 : ψ 0 ᵥ* B = 0 := by
    funext j
    have := congrArg (fun p => Polynomial.coeff p 0) (congrFun hvM j)
    simp only [Matrix.vecMul, dotProduct, M, Matrix.of_apply, Pi.zero_apply,
      Polynomial.coeff_zero, Polynomial.finsetSum_coeff, mul_sub, ← mul_assoc,
      Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_zero, zero_mul,
      Finset.sum_sub_distrib, Finset.sum_const_zero, zero_sub, neg_eq_zero] at this
    simpa [Matrix.vecMul, dotProduct, ψ] using this
  -- a degree bound
  set N := Finset.univ.sup (fun i => (v i).natDegree) + 1
  have hN : ∀ k, N ≤ k → ψ k = 0 := fun k hk => by
    funext i
    refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
    have : (v i).natDegree ≤ _ := Finset.le_sup (f := fun i => (v i).natDegree)
      (Finset.mem_univ i)
    omega
  -- a nonzero coefficient
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hv
  set k₁ := (v i₁).natDegree
  have hk₁ : k₁ < N := by
    have : (v i₁).natDegree ≤ _ := Finset.le_sup (f := fun i => (v i).natDegree)
      (Finset.mem_univ i₁)
    omega
  have hψ₁ : ψ k₁ ≠ 0 := fun h => by
    have := congrFun h i₁
    simp only [ψ, k₁, Pi.zero_apply] at this
    exact Polynomial.leadingCoeff_ne_zero.2 hi₁ this
  set w := ψ k₁ ᵥ* C
  have hw : w ≠ 0 := fun h => hψ₁ (by
    rw [← Matrix.vecMul_one (ψ k₁), ← hCD, ← Matrix.vecMul_vecMul]
    simp only [w] at h
    rw [h, Matrix.zero_vecMul])
  refine ⟨fun t => if t = k₁ then w else 0, ⟨k₁ + 1, fun t ht => by
    simp only [show t ≠ k₁ by omega, ↓reduceIte]⟩, fun x hx => ?_⟩
  -- along a solution the weighted sum telescopes to zero
  set a : ℕ → ℝ := fun k => (ψ k ᵥ* A) ⬝ᵥ x (k + 1)
  set b : ℕ → ℝ := fun k => (ψ k ᵥ* B) ⬝ᵥ x k
  have hb0 : b 0 = 0 := by simp [b, h0]
  have hba : ∀ k, b (k + 1) = a k := fun k => by simp only [a, b, hrel]
  have htel : ∀ K, ∑ k ∈ Finset.range (K + 1), (a k - b k) = a K := fun K => by
    induction K with
    | zero => simp [hb0]
    | succ K ih => rw [Finset.sum_range_succ, ih, hba]; ring
  have hsum : ∑ k ∈ Finset.range (N + 1),
      ψ k ⬝ᵥ (C *ᵥ (if k = k₁ then w else 0)) = 0 := by
    have hterm : ∀ k, ψ k ⬝ᵥ (C *ᵥ (if k = k₁ then w else 0)) = a k - b k := fun k => by
      have := hx k
      rw [← sub_eq_iff_eq_add'] at this
      simp only at this
      rw [← this, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    simp only [hterm, htel, a, hN N le_rfl, Matrix.zero_vecMul, zero_dotProduct]
  rw [Finset.sum_eq_single k₁ (fun k _ hk => by simp [hk])
    (fun h => absurd (Finset.mem_range.2 (by omega)) h)] at hsum
  simp only [↓reduceIte, Matrix.dotProduct_mulVec] at hsum
  exact hw (dotProduct_self_eq_zero.1 hsum)

/-- Miao, p. 16: the book's claim that a non-regular pair has no solution for generic `z` is
false without a rank condition on `C`. For `A = B = diag(1, 0)` and `C = (1, 0)'`,
`det(αA − B) = 0` for every `α`, yet (1.20) has a solution for every forcing sequence. -/
theorem remark_nonregular_counterexample :
    ¬ IsRegular !![(1 : ℝ), 0; 0, 0] !![1, 0; 0, 0] ∧
      ∀ z : ℕ → Fin 1 → ℝ, ∃ x : ℕ → Fin 2 → ℝ,
        IsSolution !![(1 : ℝ), 0; 0, 0] !![1, 0; 0, 0] !![1; 0] z x := by
  refine ⟨fun ⟨α, hα⟩ => hα ?_, fun z => ⟨fun t => ![∑ s ∈ Finset.range t, z s 0, 0],
    fun t => ?_⟩⟩
  · simp [Matrix.det_fin_two]
  · funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Finset.sum_range_succ]

/-! ### The steady state (1.21) -/

/-- Miao, (1.21), p. 16: if `A − B` is invertible, `x̄ = (A − B)⁻¹Cz̄` is the unique solution of
the stationary equation `Ax̄ = Bx̄ + Cz̄`. -/
theorem eq_1_21 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (zbar : m → ℝ) (hAB : IsUnit (A - B).det) (xb : n → ℝ) :
    A *ᵥ xb = B *ᵥ xb + C *ᵥ zbar ↔ xb = (A - B)⁻¹ *ᵥ (C *ᵥ zbar) := by
  constructor
  · intro h
    have h1 : (A - B) *ᵥ xb = C *ᵥ zbar := by rw [Matrix.sub_mulVec, h]; abel
    rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAB, Matrix.one_mulVec]
  · intro h
    have h1 : (A - B) *ᵥ xb = C *ᵥ zbar := by
      rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAB, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec] at h1
    rw [← h1]; abel

/-- Miao, (1.21), p. 16: the constant sequence `x̄` solves (1.20) with constant forcing `z̄`. -/
theorem eq_1_21_solution {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (zbar : m → ℝ) (hAB : IsUnit (A - B).det) :
    IsSolution A B C (fun _ => zbar) (fun _ => (A - B)⁻¹ *ᵥ (C *ᵥ zbar)) := fun _ =>
  (eq_1_21 A B C zbar hAB _).2 rfl

/-- Miao, p. 16 (Definition 1.4.1 and (1.21)): under Assumption 1.4.2 with `z_t = z̄` for
`t ≥ T`, `A` and `A − B` nonsingular, `x̄` is a steady state of the solution from date `T` on:
once `x_t = x̄` with `t ≥ T`, `x_s = x̄` for all `s > t`. -/
theorem eq_1_21_steadyState {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (zbar : m → ℝ) (hA : IsUnit A.det)
    (hAB : IsUnit (A - B).det) (z : ℕ → m → ℝ) (T : ℕ) (hz : ∀ t, T ≤ t → z t = zbar)
    (x : ℕ → n → ℝ) (hx : IsSolution A B C z x) :
    IsSteadyStateOf (fun s => x (T + s)) ((A - B)⁻¹ *ᵥ (C *ᵥ zbar)) := by
  set xb := (A - B)⁻¹ *ᵥ (C *ᵥ zbar)
  have hbar := (eq_1_21 A B C zbar hAB xb).2 rfl
  have hstep : ∀ t, T ≤ t → x t = xb → x (t + 1) = xb := fun t ht h => by
    have h1 := hx t
    rw [h, hz t ht, ← hbar] at h1
    exact (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 hA)) h1
  intro t ht s hs
  obtain ⟨k, rfl⟩ : ∃ k, s = t + 1 + k := ⟨s - (t + 1), by omega⟩
  induction k with
  | zero => exact hstep (T + t) (by omega) ht
  | succ k ih =>
    change x (T + (t + 1 + (k + 1))) = xb
    rw [show T + (t + 1 + (k + 1)) = T + (t + 1 + k) + 1 by ring]
    exact hstep _ (by omega) (ih (by omega))

/-- Remark on Definition 1.4.1 (Miao, p. 16): a point that the sequence never visits is
vacuously a steady state of it, so a sequence can have many steady states in the sense of the
definition. -/
theorem isSteadyStateOf_of_not_mem_range {α : Type*} (x : ℕ → α) (xb : α)
    (h : xb ∉ Set.range x) : IsSteadyStateOf x xb := fun t ht => absurd ⟨t, ht⟩ h

/-! ### Tools: bounds, backward and forward solutions -/

/-- Stable sequences (Definition 1.4.2) are the bounded ones. -/
theorem isStableSeq_iff_exists_le {E : Type*} [Norm E] (x : ℕ → E) :
    IsStableSeq x ↔ ∃ C, ∀ t, ‖x t‖ ≤ C := by
  rw [isStableSeq_iff_bddAbove]
  exact ⟨fun ⟨C, hC⟩ => ⟨C, fun t => hC ⟨t, rfl⟩⟩,
    fun ⟨C, hC⟩ => ⟨C, by rintro _ ⟨t, rfl⟩; exact hC t⟩⟩

omit [DecidableEq ι] in
/-- A matrix is a bounded operator for the max norms. -/
theorem exists_mulVec_bound {κ : Type*} [Fintype κ] (M : Matrix κ ι ℝ) :
    ∃ c, 0 ≤ c ∧ ∀ v, ‖M *ᵥ v‖ ≤ c * ‖v‖ := by
  classical
  set f := LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  exact ⟨‖f‖, norm_nonneg _, fun v => by simpa [f, Matrix.toLin'_apply] using f.le_opNorm v⟩

omit [DecidableEq ι] in
/-- A matrix maps bounded sequences to bounded sequences. -/
theorem bounded_mulVec {κ : Type*} [Fintype κ] (M : Matrix κ ι ℝ) {v : ℕ → ι → ℝ} {C : ℝ}
    (hv : ∀ t, ‖v t‖ ≤ C) : ∃ C', ∀ t, ‖M *ᵥ v t‖ ≤ C' := by
  obtain ⟨c, hc0, hc⟩ := exists_mulVec_bound M
  exact ⟨c * C, fun t => (hc _).trans (mul_le_mul_of_nonneg_left (hv t) hc0)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- A vector on `κ ⊕ υ` is bounded by the sum of the norms of its two parts. -/
theorem norm_sum_type_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → ℝ) :
    ‖v‖ ≤ ‖v ∘ Sum.inl‖ + ‖v ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rcases i with i | i
  · exact (norm_le_pi_norm (v ∘ Sum.inl) i).trans (le_add_of_nonneg_right (norm_nonneg _))
  · exact (norm_le_pi_norm (v ∘ Sum.inr) i).trans (le_add_of_nonneg_left (norm_nonneg _))

omit [Fintype ι] [DecidableEq ι] in
/-- The parts of a vector on `κ ⊕ υ` are no larger than the vector. -/
theorem norm_comp_inl_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → ℝ) :
    ‖v ∘ Sum.inl‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm v _

omit [Fintype ι] [DecidableEq ι] in
theorem norm_comp_inr_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → ℝ) :
    ‖v ∘ Sum.inr‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm v _

/-- The backward solution of `x_{t+1} = Wx_t + g_t`:
`x_t = Wᵗx₀ + ∑_{j<t} Wʲg_{t−1−j}`. -/
theorem backward_sol_eq (W : Matrix ι ι ℝ) {x g : ℕ → ι → ℝ}
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + g t) (t : ℕ) :
    x t = (W ^ t) *ᵥ x 0 + ∑ j ∈ Finset.range t, (W ^ j) *ᵥ g (t - 1 - j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hx t, ih, Matrix.mulVec_add, Matrix.mulVec_sum, Finset.sum_range_succ',
      Matrix.mulVec_mulVec, ← pow_succ']
    simp only [Matrix.mulVec_mulVec, ← pow_succ', pow_zero, Matrix.one_mulVec]
    rw [show t + 1 - 1 - 0 = t by omega, add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega]

/-- With geometric decay of `W` and bounded `g`, the backward solution is bounded. -/
theorem bounded_backward (W : Matrix ι ι ℝ) {K a : ℝ} (hW : HasGeomDecay W K a)
    {x g : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + g t) {C : ℝ} (hg : ∀ t, ‖g t‖ ≤ C) :
    ∀ t, ‖x t‖ ≤ K * ‖x 0‖ + K * C / (1 - a) := by
  obtain ⟨ha0, ha1, hK0, hK⟩ := hW
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg 0)
  intro t
  rw [backward_sol_eq W hx t]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖(W ^ t) *ᵥ x 0‖ ≤ K * a ^ t * ‖x 0‖ := hK t _
      _ ≤ K * 1 * ‖x 0‖ := by
          gcongr
          exact pow_le_one₀ ha0 ha1.le
      _ = K * ‖x 0‖ := by ring
  · calc ‖∑ j ∈ Finset.range t, (W ^ j) *ᵥ g (t - 1 - j)‖
        ≤ ∑ j ∈ Finset.range t, K * C * a ^ j := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          calc ‖(W ^ j) *ᵥ g (t - 1 - j)‖ ≤ K * a ^ j * ‖g (t - 1 - j)‖ := hK j _
            _ ≤ K * a ^ j * C := by gcongr; exact hg _
            _ = K * C * a ^ j := by ring
      _ = K * C * ∑ j ∈ Finset.range t, a ^ j := by rw [Finset.mul_sum]
      _ ≤ K * C * (1 - a)⁻¹ := by
          gcongr
          rw [← tsum_geometric_of_lt_one ha0 ha1]
          exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg ha0 j)
            (summable_geometric_of_lt_one ha0 ha1)
      _ = K * C / (1 - a) := by ring

/-- Geometric series of matrix powers applied to a bounded sequence converge, with
`‖∑ⱼ Mʲvⱼ‖ ≤ KC/(1 − a)`. -/
theorem summable_geom_series (M : Matrix ι ι ℝ) {K a : ℝ} (hM : HasGeomDecay M K a)
    {v : ℕ → ι → ℝ} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) :
    Summable (fun j => (M ^ j) *ᵥ v j) ∧ ‖∑' j, (M ^ j) *ᵥ v j‖ ≤ K * C / (1 - a) := by
  obtain ⟨ha0, ha1, hK0, hK⟩ := hM
  have hb : ∀ j, ‖(M ^ j) *ᵥ v j‖ ≤ K * C * a ^ j := fun j =>
    calc ‖(M ^ j) *ᵥ v j‖ ≤ K * a ^ j * ‖v j‖ := hK j _
      _ ≤ K * a ^ j * C := by gcongr; exact hv j
      _ = K * C * a ^ j := by ring
  have hg := (hasSum_geometric_of_lt_one ha0 ha1).mul_left (K * C)
  refine ⟨Summable.of_norm_bounded hg.summable hb, ?_⟩
  have := tsum_of_norm_bounded hg hb
  simpa [div_eq_mul_inv] using this

omit [DecidableEq ι] in
/-- A matrix commutes with a convergent sum. -/
theorem mulVec_tsum_rs {κ : Type*} (M : Matrix κ ι ℝ) {f : ℕ → ι → ℝ}
    (hf : Summable f) : M *ᵥ (∑' j, f j) = ∑' j, M *ᵥ f j :=
  ((hf.hasSum.map M.mulVecLin (Continuous.matrix_mulVec continuous_const
    continuous_id)).tsum_eq).symm

/-- Peeling off the first term: `∑ⱼ Mʲvⱼ = v₀ + M ∑ⱼ Mʲv_{j+1}`. -/
theorem tsum_geom_series_succ (M : Matrix ι ι ℝ) {K a : ℝ} (hM : HasGeomDecay M K a)
    {v : ℕ → ι → ℝ} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) :
    ∑' j, (M ^ j) *ᵥ v j = v 0 + M *ᵥ ∑' j, (M ^ j) *ᵥ v (j + 1) := by
  rw [(summable_geom_series M hM hv).1.tsum_eq_zero_add,
    mulVec_tsum_rs M (summable_geom_series M hM fun j => hv (j + 1)).1]
  simp only [pow_zero, Matrix.one_mulVec, pow_succ', Matrix.mulVec_mulVec]

/-- If `M` decays geometrically and `MN = 1`, a vector whose `N`-orbit is bounded is zero. -/
theorem eq_zero_of_bounded_orbit (M N : Matrix ι ι ℝ) {K a : ℝ} (hM : HasGeomDecay M K a)
    (hMN : M * N = 1) {v : ι → ℝ} {C : ℝ} (hv : ∀ k, ‖(N ^ k) *ᵥ v‖ ≤ C) : v = 0 := by
  obtain ⟨ha0, ha1, hK0, hK⟩ := hM
  have hpow : ∀ k, M ^ k * N ^ k = 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ', Matrix.mul_assoc, ← Matrix.mul_assoc M, hMN, Matrix.one_mul, ih]
  have hle : ∀ k, ‖v‖ ≤ K * C * a ^ k := fun k => by
    have : v = (M ^ k) *ᵥ ((N ^ k) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, hpow, Matrix.one_mulVec]
    calc ‖v‖ = ‖(M ^ k) *ᵥ ((N ^ k) *ᵥ v)‖ := by rw [← this]
      _ ≤ K * a ^ k * ‖(N ^ k) *ᵥ v‖ := hK k _
      _ ≤ K * a ^ k * C := by gcongr; exact hv k
      _ = K * C * a ^ k := by ring
  have hlim : Tendsto (fun k => K * C * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul (K * C)
  have := ge_of_tendsto' hlim hle
  exact norm_le_zero_iff.1 this

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The matrix lag-operator formula

Miao, §1.2, pp. 11–12: `(I − ALⁿ)⁻¹ = ∑_{j ≥ 0} AʲLⁿʲ` when all eigenvalues of `A` lie inside
the unit circle, where `LⁿX_t = X_{t−n}` on two-sided sequences `{X_t}_{t ∈ ℤ}`.

The operator identity is made precise on bounded sequences `X : ℤ → (ι → ℝ)`
(`lag_matrix_formula`): the series `Y_t = ∑ⱼ AʲX_{t−nj}` (`lagSeries`) converges for every `t`,
`Y` is bounded, `Y_t − AY_{t−n} = X_t` (that is, `(I − ALⁿ)Y = X`), and `Y` is the only bounded
sequence with this property. So `∑ⱼ AʲLⁿʲ` is the inverse of `I − ALⁿ` on bounded sequences.

The book says "here `n` is any integer". For two-sided sequences this is right: the proof uses
only `t − n(j + 1) = (t − n) − nj`, and works for `n ≤ 0` too (`n = 0` gives
`Y_t = ∑ⱼ AʲX_t = (I − A)⁻¹X_t`, `n < 0` a sum of leads). The geometric decay
`‖Aʲv‖ ≤ K aʲ‖v‖`, `a < 1`, comes from `hasGeomDecay_of_isStableMatrix`.
-/

open Filter Topology

namespace Miao.DifferenceEquations

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑ⱼ AʲLⁿʲX` at date `t`: `∑ⱼ AʲX_{t−nj}`. -/
noncomputable def lagSeries (A : Matrix ι ι ℝ) (n : ℤ) (X : ℤ → ι → ℝ) (t : ℤ) : ι → ℝ :=
  ∑' j : ℕ, (A ^ j) *ᵥ X (t - n * j)

/-- The lag series converges and is bounded by `KC/(1 − a)`. -/
theorem lagSeries_summable (A : Matrix ι ι ℝ) {K a : ℝ} (hA : HasGeomDecay A K a) (n : ℤ)
    {X : ℤ → ι → ℝ} {C : ℝ} (hX : ∀ t, ‖X t‖ ≤ C) (t : ℤ) :
    Summable (fun j : ℕ => (A ^ j) *ᵥ X (t - n * j)) ∧
      ‖lagSeries A n X t‖ ≤ K * C / (1 - a) :=
  summable_geom_series A hA (v := fun j : ℕ => X (t - n * j)) fun _ => hX _

/-- `(I − ALⁿ)Y = X`: `Y_t = X_t + AY_{t−n}`. -/
theorem lagSeries_rec (A : Matrix ι ι ℝ) {K a : ℝ} (hA : HasGeomDecay A K a) (n : ℤ)
    {X : ℤ → ι → ℝ} {C : ℝ} (hX : ∀ t, ‖X t‖ ≤ C) (t : ℤ) :
    lagSeries A n X t = X t + A *ᵥ lagSeries A n X (t - n) := by
  unfold lagSeries
  rw [tsum_geom_series_succ A hA (v := fun j : ℕ => X (t - n * j)) fun _ => hX _]
  simp only [Nat.cast_zero, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  congr 3
  funext j
  congr 2
  ring

/-- Uniqueness: a bounded `Y` with `Y_t = X_t + AY_{t−n}` is the lag series. -/
theorem lagSeries_unique (A : Matrix ι ι ℝ) {K a : ℝ} (hA : HasGeomDecay A K a) (n : ℤ)
    {X Y : ℤ → ι → ℝ} {C D : ℝ} (hX : ∀ t, ‖X t‖ ≤ C) (hY : ∀ t, ‖Y t‖ ≤ D)
    (hrec : ∀ t, Y t = X t + A *ᵥ Y (t - n)) : Y = lagSeries A n X := by
  obtain ⟨ha0, ha1, hK0, hK⟩ := hA
  set E := fun t => Y t - lagSeries A n X t
  have hE : ∀ t, E t = A *ᵥ E (t - n) := fun t => by
    simp only [E, Matrix.mulVec_sub]
    rw [hrec t, lagSeries_rec A ⟨ha0, ha1, hK0, hK⟩ n hX t]
    abel
  have hEk : ∀ (k : ℕ) t, E t = (A ^ k) *ᵥ E (t - n * k) := fun k => by
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [ih t, hE (t - n * k), Matrix.mulVec_mulVec, ← pow_succ]
      congr 2
      push_cast
      ring
  set B := D + K * C / (1 - a)
  have hEB : ∀ t, ‖E t‖ ≤ B := fun t =>
    (norm_sub_le _ _).trans (add_le_add (hY t)
      (lagSeries_summable A ⟨ha0, ha1, hK0, hK⟩ n hX t).2)
  funext t
  rw [← sub_eq_zero]
  have hle : ∀ k : ℕ, ‖E t‖ ≤ K * B * a ^ k := fun k => by
    calc ‖E t‖ = ‖(A ^ k) *ᵥ E (t - n * k)‖ := by rw [← hEk]
      _ ≤ K * a ^ k * ‖E (t - n * k)‖ := hK k _
      _ ≤ K * a ^ k * B := by gcongr; exact hEB _
      _ = K * B * a ^ k := by ring
  have hlim : Tendsto (fun k : ℕ => K * B * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul (K * B)
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)

/-- **The matrix lag formula** (Miao, §1.2, pp. 11–12): `(I − ALⁿ)⁻¹ = ∑_{j ≥ 0} AʲLⁿʲ` if all
eigenvalues of `A` are inside the unit circle, for every integer `n`. On bounded sequences
`X`: the series `Y_t = ∑ⱼ AʲX_{t−nj}` converges, `Y` is bounded, `Y − ALⁿY = X`, and every
bounded solution of `Y' − ALⁿY' = X` equals `Y`. -/
theorem lag_matrix_formula (A : Matrix ι ι ℝ) (hA : IsStableMatrix (A.map Complex.ofRealHom))
    (n : ℤ) (X : ℤ → ι → ℝ) (hX : ∃ C, ∀ t, ‖X t‖ ≤ C) :
    (∀ t, Summable (fun j : ℕ => (A ^ j) *ᵥ X (t - n * j))) ∧
      (∃ D, ∀ t, ‖lagSeries A n X t‖ ≤ D) ∧
      (∀ t, lagSeries A n X t - A *ᵥ lagSeries A n X (t - n) = X t) ∧
      ∀ Y : ℤ → ι → ℝ, (∃ D, ∀ t, ‖Y t‖ ≤ D) → (∀ t, Y t - A *ᵥ Y (t - n) = X t) →
        Y = lagSeries A n X := by
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix A hA
  obtain ⟨C, hC⟩ := hX
  refine ⟨fun t => (lagSeries_summable A hKa n hC t).1,
    ⟨_, fun t => (lagSeries_summable A hKa n hC t).2⟩,
    fun t => by rw [lagSeries_rec A hKa n hC t]; abel, fun Y ⟨D, hD⟩ hY => ?_⟩
  exact lagSeries_unique A hKa n hC hD fun t => by rw [← hY t]; abel

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A real block diagonalisation `W = P⁻¹ diag(J_s, J_u) P`

Miao, §1.4.1, pp. 17–20. The book takes the complex Jordan form `W = P⁻¹JP` and orders the
Jordan blocks as `J = diag(J_s, J_u)`, stable roots first. Only the split into a stable and an
unstable block is used in the proofs of Theorem 1.4.2, Corollary 1.4.1 and Theorem 1.4.3, so
here a **real** invertible `P` is used (`IsRealBlockSplit W P R J_s J_u`):

* `PR = I`, `RP = I` (`R = P⁻¹`, (1.28)), `PW = diag(J_s, J_u)P`;
* all eigenvalues of `J_s` have modulus `< 1`, all eigenvalues of `J_u` modulus `> 1`.

`exists_real_block_split`: such a real `P` exists whenever `W` has no eigenvalue on the unit
circle, with `J_s` of size `n_s = dim E_s`, the number of stable characteristic roots counted
with multiplicity (`finrank_stableR`). The columns of `R` are a basis of `E_s` followed by a
basis of `E_u` (`RealSplitting`); `J = PWR` is block diagonal because `E_s` and `E_u` are
`W`-invariant. An eigenvector `w` of a block gives the eigenvector `R(w, 0)` (or `R(0, w)`) of
`W` in the complex stable (unstable) subspace, which fixes the modulus of its eigenvalue.

Consequences used later: `WR = RJ` (`mul_R`), `n_s + n_u = n` (`card_add_card`),
`I − W` is invertible (`isUnit_one_sub`), and the block formulas for `P x` and `R x*`.
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix

variable {ι σ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
  [DecidableEq τ]

/-- A real block diagonalisation of `W` (Miao, pp. 18–20, with a real `P` in place of the
Jordan form): `R = P⁻¹`, `PW = diag(J_s, J_u)P`, `J_s` stable, every eigenvalue of `J_u` of
modulus greater than one. -/
def IsRealBlockSplit (W : Matrix ι ι ℝ) (P : Matrix (σ ⊕ τ) ι ℝ) (R : Matrix ι (σ ⊕ τ) ℝ)
    (Js : Matrix σ σ ℝ) (Ju : Matrix τ τ ℝ) : Prop :=
  P * R = 1 ∧ R * P = 1 ∧ P * W = Matrix.fromBlocks Js 0 0 Ju * P ∧
    IsStableMatrix (Js.map Complex.ofRealHom) ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (Ju.map Complex.ofRealHom)) μ → 1 < ‖μ‖

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] [DecidableEq τ] in
/-- `diag(J_s, J_u)` acts blockwise: the `s` part. -/
theorem blockDiag_mulVec_inl (Js : Matrix σ σ ℝ) (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → ℝ) :
    (Matrix.fromBlocks Js 0 0 Ju *ᵥ v) ∘ Sum.inl = Js *ᵥ (v ∘ Sum.inl) := by
  rw [Matrix.fromBlocks_mulVec]
  simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] [DecidableEq τ] in
/-- `diag(J_s, J_u)` acts blockwise: the `u` part. -/
theorem blockDiag_mulVec_inr (Js : Matrix σ σ ℝ) (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → ℝ) :
    (Matrix.fromBlocks Js 0 0 Ju *ᵥ v) ∘ Sum.inr = Ju *ᵥ (v ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]
  simp

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
/-- The first block row of a matrix with block columns. -/
theorem mulVec_comp_inl {κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inl = P.toBlocks₁₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₁₂ *ᵥ (x ∘ Sum.inr) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
/-- The second block row of a matrix with block columns. -/
theorem mulVec_comp_inr {κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inr = P.toBlocks₂₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₂₂ *ᵥ (x ∘ Sum.inr) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

/-- `WR = RJ`. -/
theorem IsRealBlockSplit.mul_R {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ}
    {R : Matrix ι (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (h : IsRealBlockSplit W P R Js Ju) : W * R = R * Matrix.fromBlocks Js 0 0 Ju := by
  obtain ⟨hPR, hRP, hPW, -, -⟩ := h
  calc W * R = R * P * W * R := by rw [hRP, Matrix.one_mul]
    _ = R * (P * W) * R := by rw [Matrix.mul_assoc R P W]
    _ = R * Matrix.fromBlocks Js 0 0 Ju * (P * R) := by
        rw [hPW, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = R * Matrix.fromBlocks Js 0 0 Ju := by rw [hPR, Matrix.mul_one]

/-- `n_s + n_u = n`: `P` is invertible. -/
theorem card_add_card_of_inv {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) : Fintype.card σ + Fintype.card τ = Fintype.card ι := by
  classical
  have e : (σ ⊕ τ → ℝ) ≃ₗ[ℝ] (ι → ℝ) := LinearEquiv.ofLinearMap (Matrix.toLin' R)
    (Matrix.toLin' P) (by rw [← Matrix.toLin'_mul, hRP, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hPR, Matrix.toLin'_one])
  have := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at this
  exact this

/-- `I − W` is invertible under a block split: `1` is not an eigenvalue. -/
theorem IsRealBlockSplit.isUnit_one_sub {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ}
    {R : Matrix ι (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (h : IsRealBlockSplit W P R Js Ju) : IsUnit (1 - W).det := by
  obtain ⟨hPR, hRP, hPW, hJs, hJu⟩ := h
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v v' hvv
  rw [← sub_eq_zero]
  set d := v - v'
  have hd : W *ᵥ d = d := by
    have : (1 - W) *ᵥ d = 0 := by simp only [d, Matrix.mulVec_sub, hvv, sub_self]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this.symm
  have hJ : Matrix.fromBlocks Js 0 0 Ju *ᵥ (P *ᵥ d) = P *ᵥ d := by
    rw [Matrix.mulVec_mulVec, ← hPW, ← Matrix.mulVec_mulVec, hd]
  -- the stable part: `J_sᵗs = s → 0`
  have hs : (P *ᵥ d) ∘ Sum.inl = 0 := by
    have h1 : Js *ᵥ ((P *ᵥ d) ∘ Sum.inl) = (P *ᵥ d) ∘ Sum.inl := by
      rw [← blockDiag_mulVec_inl Js Ju, hJ]
    have hpow : ∀ k, (Js ^ k) *ᵥ ((P *ᵥ d) ∘ Sum.inl) = (P *ᵥ d) ∘ Sum.inl := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h1, ih]
    have := tendsto_of_isStableMatrix Js hJs ((P *ᵥ d) ∘ Sum.inl)
    simp only [hpow] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  -- the unstable part: a bounded `J_u`-orbit is zero
  have hu : (P *ᵥ d) ∘ Sum.inr = 0 := by
    have h1 : Ju *ᵥ ((P *ᵥ d) ∘ Sum.inr) = (P *ᵥ d) ∘ Sum.inr := by
      rw [← blockDiag_mulVec_inr Js Ju, hJ]
    have hpow : ∀ k, (Ju ^ k) *ᵥ ((P *ᵥ d) ∘ Sum.inr) = (P *ᵥ d) ∘ Sum.inr := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h1, ih]
    obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
    obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
    exact eq_zero_of_bounded_orbit Ju⁻¹ Ju hKa (Matrix.nonsing_inv_mul _ hdet)
      (fun k => by rw [hpow k])
  have hP0 : P *ᵥ d = 0 := by
    funext i
    rcases i with i | i
    · exact congrFun hs i
    · exact congrFun hu i
  have : d = R *ᵥ (P *ᵥ d) := by rw [Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
  rw [this, hP0, Matrix.mulVec_zero]

/-! ### Existence of a real block split -/

/-- An eigenvector of `J` transported by `R` is an eigenvector of `W`. -/
theorem eigen_transport {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    {J : Matrix (σ ⊕ τ) (σ ⊕ τ) ℝ} (hPR : P * R = 1) (hWR : W * R = R * J) {μ : ℂ}
    {w : σ ⊕ τ → ℂ} (hw : w ≠ 0) (hJw : J.map Complex.ofRealHom *ᵥ w = μ • w) :
    cplxEnd W (R.map Complex.ofRealHom *ᵥ w) = μ • (R.map Complex.ofRealHom *ᵥ w) ∧
      R.map Complex.ofRealHom *ᵥ w ≠ 0 := by
  classical
  set f := Complex.ofRealHom
  refine ⟨?_, fun h0 => hw ?_⟩
  · rw [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hWR,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, hJw, Matrix.mulVec_smul]
  · have : P.map f *ᵥ (R.map f *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPR,
        Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_mulVec]
    rw [← this, h0, Matrix.mulVec_zero]

/-- **A real block split exists** (Miao, pp. 18–20) when `W` has no eigenvalue on the unit
circle: with `n_s = dim E_s` (the number of stable characteristic roots with multiplicity,
`finrank_stableR`) and `n_u = dim E_u`, there are a real invertible `P` and blocks `J_s`
(`n_s × n_s`, stable) and `J_u` (`n_u × n_u`, all eigenvalues of modulus `> 1`) with
`PWP⁻¹ = diag(J_s, J_u)`. -/
theorem exists_real_block_split (W : Matrix ι ι ℝ)
    (hW : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (W.map Complex.ofRealHom)) μ →
      ‖μ‖ ≠ 1) :
    ∃ (P : Matrix (Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W))) ι ℝ)
      (R : Matrix ι (Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W))) ℝ)
      (Js : Matrix (Fin (finrank ℝ (stableR W))) (Fin (finrank ℝ (stableR W))) ℝ)
      (Ju : Matrix (Fin (finrank ℝ (unstableR W))) (Fin (finrank ℝ (unstableR W))) ℝ),
      IsRealBlockSplit W P R Js Ju := by
  set f := Complex.ofRealHom
  have hc := isCompl_stableR_unstableR W
  set bs := Module.finBasis ℝ (stableR W)
  set bu := Module.finBasis ℝ (unstableR W)
  set bb := (bs.prod bu).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hbl : ∀ a, bb (Sum.inl a) = (bs a : ι → ℝ) := fun a => by
    simp [bb, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  have hbr : ∀ b, bb (Sum.inr b) = (bu b : ι → ℝ) := fun b => by
    simp [bb, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  set P := LinearMap.toMatrix' bb.equivFun.toLinearMap
  set R := LinearMap.toMatrix' bb.equivFun.symm.toLinearMap
  have hPv : ∀ v, P *ᵥ v = bb.equivFun v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hRv : ∀ c, R *ᵥ c = bb.equivFun.symm c := fun c => LinearMap.toMatrix'_mulVec _ c
  have hPR : P * R = 1 := Matrix.toLin'.injective (LinearMap.ext fun c => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, hRv, hPv, Matrix.one_mulVec, LinearEquiv.apply_symm_apply])
  have hRP : R * P = 1 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, hPv, hRv, Matrix.one_mulVec, LinearEquiv.symm_apply_apply])
  have hRcol : ∀ j, R *ᵥ Pi.single j 1 = bb j := fun j => by
    rw [hRv, LinearEquiv.symm_apply_eq]
    funext i
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  set J := P * W * R
  -- `E_s` has no `u`-coordinates, `E_u` no `s`-coordinates
  have hPs : ∀ v ∈ stableR W, ∀ b, (P *ᵥ v) (Sum.inr b) = 0 := fun v hv b => by
    rw [hPv, Basis.equivFun_apply]
    simp only [bb, Basis.map_repr, LinearEquiv.trans_apply]
    have := Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hc (⟨v, hv⟩ : stableR W)
    simp only at this
    rw [this, Basis.prod_repr_inr, map_zero, Finsupp.zero_apply]
  have hPu : ∀ v ∈ unstableR W, ∀ a, (P *ᵥ v) (Sum.inl a) = 0 := fun v hv a => by
    rw [hPv, Basis.equivFun_apply]
    simp only [bb, Basis.map_repr, LinearEquiv.trans_apply]
    have := Submodule.prodEquivOfIsCompl_symm_apply_right _ _ hc (⟨v, hv⟩ : unstableR W)
    simp only at this
    rw [this, Basis.prod_repr_inl, map_zero, Finsupp.zero_apply]
  have hJcol : ∀ j, J *ᵥ Pi.single j 1 = P *ᵥ (W *ᵥ bb j) := fun j => by
    rw [← hRcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hJ12 : J.toBlocks₁₂ = 0 := by
    ext a b
    have := congrFun (hJcol (Sum.inr b)) (Sum.inl a)
    rw [Matrix.mulVec_single_one, hbr] at this
    simp only [Matrix.col_apply] at this
    rw [Matrix.toBlocks₁₂, Matrix.of_apply, this, Matrix.zero_apply]
    exact hPu _ (unstableR_invariant W (bu b).2) a
  have hJ21 : J.toBlocks₂₁ = 0 := by
    ext b a
    have := congrFun (hJcol (Sum.inl a)) (Sum.inr b)
    rw [Matrix.mulVec_single_one, hbl] at this
    simp only [Matrix.col_apply] at this
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, this, Matrix.zero_apply]
    exact hPs _ (stableR_invariant W (bs a).2) b
  have hJ : J = Matrix.fromBlocks J.toBlocks₁₁ 0 0 J.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks J, hJ12, hJ21]
  have hPW : P * W = J * P := by
    simp only [J]; rw [Matrix.mul_assoc, hRP, Matrix.mul_one]
  have hWR : W * R = R * J := by
    simp only [J]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRP, Matrix.one_mul]
  -- the column `j` of `R` is `bb j`
  have hRmem : ∀ (w : _ → ℂ) (S : Submodule ℂ (ι → ℂ)), (∀ j, w j ≠ 0 → cplx (bb j) ∈ S) →
      R.map f *ᵥ w ∈ S := fun w S hS => by
    have hsum : R.map f *ᵥ w = ∑ j, w j • cplx (bb j) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, cplx]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hRcol, Matrix.mulVec_single_one, Matrix.col_apply, mul_comm]
      rfl
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : w j = 0
    · rw [hj, zero_smul]; exact S.zero_mem
    · exact S.smul_mem _ (hS j hj)
  have hJmap : J.map f = Matrix.fromBlocks (J.toBlocks₁₁.map f) 0 0 (J.toBlocks₂₂.map f) := by
    conv_lhs => rw [hJ]
    simp only [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  refine ⟨P, R, J.toBlocks₁₁, J.toBlocks₂₂, hPR, hRP, hJ ▸ hPW, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · -- the stable block
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : J.toBlocks₁₁.map f *ᵥ w = μ • w := by
      simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hw.1
    set w' : Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W)) → ℂ := Sum.elim w 0
    have hw' : w' ≠ 0 := fun h => hw.2 (by funext a; exact congrFun h (Sum.inl a))
    have hJw : J.map f *ᵥ w' = μ • w' := by
      rw [hJmap, Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i <;> simp [w', hw1]
    obtain ⟨hev, hne⟩ := eigen_transport hPR hWR hw' hJw
    have hmem : R.map f *ᵥ w' ∈ stableSubspace (cplxEnd W) :=
      hRmem w' _ fun j hj => by
        rcases j with a | b
        · rw [hbl]; exact (bs a).2
        · exact absurd rfl hj
    by_contra hge
    push Not at hge
    have hU : R.map f *ᵥ w' ∈ unstableSubspace (cplxEnd W) :=
      le_biSup (fun μ => (cplxEnd W).maxGenEigenspace μ) (show μ ∈ {μ : ℂ | 1 ≤ ‖μ‖} from hge)
        (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hev))
    exact hne ((Submodule.disjoint_def.1 (disjoint_stable_unstable _)) _ hmem hU)
  · -- the unstable block
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : J.toBlocks₂₂.map f *ᵥ w = μ • w := by
      simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hw.1
    set w' : Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W)) → ℂ := Sum.elim 0 w
    have hw' : w' ≠ 0 := fun h => hw.2 (by funext a; exact congrFun h (Sum.inr a))
    have hJw : J.map f *ᵥ w' = μ • w' := by
      rw [hJmap, Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i <;> simp [w', hw1]
    obtain ⟨hev, hne⟩ := eigen_transport hPR hWR hw' hJw
    have hmem : R.map f *ᵥ w' ∈ unstableSubspace (cplxEnd W) :=
      hRmem w' _ fun j hj => by
        rcases j with a | b
        · exact absurd rfl hj
        · rw [hbr]; exact (bu b).2
    have h1 := hW μ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hev, hne⟩)
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hS : R.map f *ᵥ w' ∈ stableSubspace (cplxEnd W) :=
        le_biSup (fun μ => (cplxEnd W).maxGenEigenspace μ) (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hlt)
          (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hev))
      exact absurd ((Submodule.disjoint_def.1 (disjoint_stable_unstable _)) _ hS hmem) hne
    · exact hgt

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonsingular systems: Theorems 1.4.1 and 1.4.2, Corollary 1.4.1

Miao, §1.4.1, pp. 17–23: `x_{t+1} = Wx_t + A⁻¹Cz_t` (1.22) with `W = A⁻¹B`.

* (1.22) `eq_1_22`; the backward solution (1.25) in the form
  `x_t = Wᵗx₀ + ∑_{j<t} WʲA⁻¹Cz_{t−1−j}` (`eq_1_25`), and (1.24) for `x* = Px` (`eq_1_24`).
* **Theorem 1.4.1** (`theorem_1_4_1`): with `A`, `I − W` nonsingular and `z_t = z̄` eventually,
  every solution converges to `x̄ = (A − B)⁻¹Cz̄` iff all eigenvalues of `W` are stable. Both
  directions are proved; the book asserts the converse without proof. For the converse, the
  difference of two solutions is `Wᵗ(x₀ − x₀')`, so every orbit of `W` converges to zero.
  `xbar_eq`: the two formulas for `x̄`, `(A − B)⁻¹Cz̄ = (I − W)⁻¹A⁻¹Cz̄`, agree.
* **Theorem 1.4.2** (Blanchard–Kahn, `theorem_1_4_2`), with a real block split
  `PWP⁻¹ = diag(J_s, J_u)` (`IsRealBlockSplit`, which exists under (iii):
  `exists_real_block_split`), `x = (k, y)`, `n_k` predetermined and `n_y` jump coordinates:
  if `n_u = n_y` and `P_uy` is nonsingular, then for every `k₀` and every stable `z` there is a
  unique stable solution. The proof follows the book: the forward solution (1.29) for `u`
  (`forwardU`, `eq_1_29`; the printed formula `u_t = −∑ⱼ J_u^{−j−1}C_u*z_{t+j}` is correct),
  (1.30)–(1.32) (`eq_1_30`, `eq_1_31`, `eq_1_32`), then `y₀` from (1.32) and the backward
  solution. Existence needs only a right inverse of `P_uy` (`bk_exists`), uniqueness only a
  left inverse (`bk_unique`). (1.33) is checked (`eq_1_33`, the printed coefficients are
  correct), and `R_ks` is nonsingular with `R_ks⁻¹ = P_sk − P_syP_uy⁻¹P_uk` (`rks_inv`); the
  converse (`puy_inv_of_rks`) and the order condition `n_s = n_k ⇔ n_u = n_y` (`bk_order_iff`)
  give the book's reformulation of the Blanchard–Kahn conditions.
* **Corollary 1.4.1** (`corollary_1_4_1`): under Assumption 1.4.2 the stable solution converges
  to `x̄` (here `I − W` and `A − B` are automatically invertible).
* **The stable manifold (1.34)** (`eq_1_34`, `stable_initial_iff`): the initial values of
  stable solutions are the `(k₀, y₀)` with `y₀ = P_uy⁻¹u₀ − P_uy⁻¹P_ukk₀`. The book calls this an
  `n_k`-dimensional subspace. For `z = 0` it is the linear subspace `stableArm P`
  (`{x : (Px)_u = 0}`, `stableArm_iff`) of dimension `n_k` (`finrank_stableArm`); in general
  it is the affine translate `x̂ + stableArm P` with `x̂ = (0, P_uy⁻¹u₀)`
  (`stable_initial_translate`), a linear subspace only when `u₀ = 0`.
* **Unit roots** (p. 23, `remark_unit_root`): for `x_{t+1} = x_t + 1` (`n_k = 1`,
  `n_u = n_y = 0`, eigenvalue `1`) no solution is stable.
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix

/-! ### (1.22), (1.24), (1.25) -/

/-- Miao, (1.22), p. 17: for nonsingular `A`, (1.20) is `x_{t+1} = A⁻¹Bx_t + A⁻¹Cz_t`. -/
theorem eq_1_22 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → ℝ) (x : ℕ → n → ℝ) :
    IsSolution A B C z x ↔ ∀ t, x (t + 1) = (A⁻¹ * B) *ᵥ x t + (A⁻¹ * C) *ᵥ z t := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← h,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
  · rw [h, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.one_mul]

/-- The recursion `x_{t+1} = Wx_t + Gz_t` has a solution from every `x₀`. -/
theorem exists_sol_rec {n m : Type*} [Fintype n] [Fintype m] (W : Matrix n n ℝ)
    (G : Matrix n m ℝ) (z : ℕ → m → ℝ) (x₀ : n → ℝ) :
    ∃ x : ℕ → n → ℝ, x 0 = x₀ ∧ ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t :=
  ⟨fun t => Nat.rec x₀ (fun t xt => W *ᵥ xt + G *ᵥ z t) t, rfl, fun _ => rfl⟩

/-- Solutions of `x_{t+1} = Wx_t + Gz_t` are determined by `x₀`. -/
theorem sol_rec_unique {n m : Type*} [Fintype n] [Fintype m] (W : Matrix n n ℝ)
    (G : Matrix n m ℝ) (z : ℕ → m → ℝ) {x y : ℕ → n → ℝ}
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (hy : ∀ t, y (t + 1) = W *ᵥ y t + G *ᵥ z t)
    (h0 : x 0 = y 0) : x = y := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih => rw [hx, hy, ih]

/-- Miao, p. 18: with `A` nonsingular, (1.22) has a solution for every `x₀` (the backward
solution), and it is unique. -/
theorem exists_unique_solution {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → ℝ)
    (x₀ : n → ℝ) : ∃! x : ℕ → n → ℝ, IsSolution A B C z x ∧ x 0 = x₀ := by
  obtain ⟨x, hx0, hx⟩ := exists_sol_rec (A⁻¹ * B) (A⁻¹ * C) z x₀
  refine ⟨x, ⟨(eq_1_22 A B C hA z x).2 hx, hx0⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  exact sol_rec_unique _ _ z ((eq_1_22 A B C hA z y).1 hy) hx (hy0.trans hx0.symm)

/-- Miao, (1.24), p. 18: if `PW = JP`, then `x* = Px` solves `x*_{t+1} = Jx*_t + C*z_t`
with `C* = PA⁻¹C`. -/
theorem eq_1_24 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (hA : IsUnit A.det) (P J : Matrix n n ℝ) (hPW : P * (A⁻¹ * B) = J * P)
    (z : ℕ → m → ℝ) (x : ℕ → n → ℝ) (hx : IsSolution A B C z x) (t : ℕ) :
    P *ᵥ x (t + 1) = J *ᵥ (P *ᵥ x t) + (P * A⁻¹ * C) *ᵥ z t := by
  rw [(eq_1_22 A B C hA z x).1 hx t, Matrix.mulVec_add, Matrix.mulVec_mulVec, hPW]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Miao, (1.25), p. 18, the backward-looking solution in the original coordinates:
`x_t = Wᵗx₀ + ∑_{j<t} WʲA⁻¹Cz_{t−1−j}`. -/
theorem eq_1_25 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → ℝ) (x : ℕ → n → ℝ)
    (hx : IsSolution A B C z x) (t : ℕ) :
    x t = ((A⁻¹ * B) ^ t) *ᵥ x 0 +
      ∑ j ∈ Finset.range t, ((A⁻¹ * B) ^ j) *ᵥ ((A⁻¹ * C) *ᵥ z (t - 1 - j)) :=
  backward_sol_eq _ ((eq_1_22 A B C hA z x).1 hx) t

/-! ### Theorem 1.4.1 -/

/-- `A − B = A(I − W)` is invertible when `A` and `I − W` are. -/
theorem isUnit_sub_det {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hA : IsUnit A.det) (hIW : IsUnit (1 - A⁻¹ * B).det) : IsUnit (A - B).det := by
  have : A - B = A * (1 - A⁻¹ * B) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [this, Matrix.det_mul]
  exact hA.mul hIW

/-- Miao, p. 19 (proof of Theorem 1.4.1): `(I − W)⁻¹A⁻¹Cz̄` is the steady state `x̄` of (1.21). -/
theorem xbar_eq {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] (A B : Matrix n n ℝ)
    (C : Matrix n m ℝ) (zbar : m → ℝ) (hA : IsUnit A.det) :
    (A - B)⁻¹ *ᵥ (C *ᵥ zbar) = (1 - A⁻¹ * B)⁻¹ *ᵥ ((A⁻¹ * C) *ᵥ zbar) := by
  have : A - B = A * (1 - A⁻¹ * B) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
  rw [this, Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **Theorem 1.4.1** (Miao, p. 18). Let `A` and `I − W` be nonsingular, `W = A⁻¹B`, and
`z_t = z̄` for `t ≥ T` (Assumption 1.4.2). Every solution of (1.22) converges to
`x̄ = (A − B)⁻¹Cz̄`, whatever `x₀`, if and only if all eigenvalues of `W` are stable. -/
theorem theorem_1_4_1 {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (hA : IsUnit A.det)
    (hIW : IsUnit (1 - A⁻¹ * B).det) (z : ℕ → m → ℝ) (zbar : m → ℝ)
    (hz : EventuallyConst z zbar) :
    (∀ x, IsSolution A B C z x → Tendsto x atTop (𝓝 ((A - B)⁻¹ *ᵥ (C *ᵥ zbar)))) ↔
      IsStableMatrix ((A⁻¹ * B).map Complex.ofRealHom) := by
  set W := A⁻¹ * B
  set G := A⁻¹ * C
  have hAB := isUnit_sub_det A B hA hIW
  set xb := (A - B)⁻¹ *ᵥ (C *ᵥ zbar)
  have hbar : xb = W *ᵥ xb + G *ᵥ zbar :=
    (eq_1_22 A B C hA (fun _ => zbar) (fun _ => xb)).1 (eq_1_21_solution A B C zbar hAB) 0
  have hdiff : ∀ x y, IsSolution A B C z x → IsSolution A B C z y →
      ∀ t, x t - y t = (W ^ t) *ᵥ (x 0 - y 0) := by
    intro x y hx hy t
    have hx' := (eq_1_22 A B C hA z x).1 hx
    have hy' := (eq_1_22 A B C hA z y).1 hy
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, hx' t, hy' t, Matrix.mulVec_sub]
      abel
  constructor
  · intro h
    refine isStableMatrix_of_tendsto W fun v => ?_
    obtain ⟨x, hx0, hx⟩ := exists_sol_rec W G z 0
    obtain ⟨y, hy0, hy⟩ := exists_sol_rec W G z v
    have hxs : IsSolution A B C z x := (eq_1_22 A B C hA z x).2 hx
    have hys : IsSolution A B C z y := (eq_1_22 A B C hA z y).2 hy
    have := (h y hys).sub (h x hxs)
    rw [sub_self] at this
    refine this.congr fun t => ?_
    rw [hdiff y x hys hxs t, hy0, hx0, sub_zero]
  · intro hW x hx
    obtain ⟨T, hT⟩ := hz
    have hx' := (eq_1_22 A B C hA z x).1 hx
    have hd : ∀ k, x (k + T) - xb = (W ^ k) *ᵥ (x T - xb) := fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, show k + 1 + T = k + T + 1 by ring,
          hx' (k + T), hT (k + T) (by omega), Matrix.mulVec_sub]
        conv_lhs => rw [hbar]
        abel
    have h1 : Tendsto (fun k => x (k + T) - xb) atTop (𝓝 0) := by
      simp_rw [hd]
      exact tendsto_of_isStableMatrix W hW _
    have h2 := h1.add_const xb
    simp only [sub_add_cancel, zero_add] at h2
    exact (tendsto_add_atTop_iff_nat T).1 h2

/-! ### The forward solution (1.29) -/

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- Miao, (1.29), p. 21: the forward-looking solution `u_t = −∑_{j ≥ 0} J_u^{−j−1}c_{t+j}` of
`u_{t+1} = J_uu_t + c_t`. -/
noncomputable def forwardU (Ju : Matrix τ τ ℝ) (c : ℕ → τ → ℝ) (t : ℕ) : τ → ℝ :=
  -(Ju⁻¹ *ᵥ ∑' j, (Ju⁻¹ ^ j) *ᵥ c (t + j))

/-- The forward solution solves `u_{t+1} = J_uu_t + c_t`. -/
theorem forwardU_rec (Ju : Matrix τ τ ℝ) (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → ℝ} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) (t : ℕ) :
    forwardU Ju c (t + 1) = Ju *ᵥ forwardU Ju c t + c t := by
  have hS := tsum_geom_series_succ Ju⁻¹ hM (v := fun j => c (t + j)) fun _ => hc _
  have e : (fun j => (Ju⁻¹ ^ j) *ᵥ c (t + (j + 1))) = fun j => (Ju⁻¹ ^ j) *ᵥ c (t + 1 + j) := by
    funext j; rw [show t + (j + 1) = t + 1 + j by ring]
  unfold forwardU
  rw [hS, e, add_zero, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  abel

/-- The forward solution is bounded. -/
theorem forwardU_bounded (Ju : Matrix τ τ ℝ) {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    {c : ℕ → τ → ℝ} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) : ∃ D, ∀ t, ‖forwardU Ju c t‖ ≤ D := by
  obtain ⟨c₀, hc₀, hb⟩ := exists_mulVec_bound Ju⁻¹
  refine ⟨c₀ * (K * C / (1 - a)), fun t => ?_⟩
  rw [forwardU, norm_neg]
  exact (hb _).trans (mul_le_mul_of_nonneg_left
    (summable_geom_series Ju⁻¹ hM (v := fun j => c (t + j)) fun _ => hc _).2 hc₀)

/-- The forward solution is the only bounded solution of `u_{t+1} = J_uu_t + c_t`. -/
theorem forwardU_unique (Ju : Matrix τ τ ℝ) (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → ℝ} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C)
    {u : ℕ → τ → ℝ} {D : ℝ} (hu : ∀ t, ‖u t‖ ≤ D) (hrec : ∀ t, u (t + 1) = Ju *ᵥ u t + c t) :
    ∀ t, u t = forwardU Ju c t := by
  obtain ⟨D', hD'⟩ := forwardU_bounded Ju hM hc
  set e := fun t => u t - forwardU Ju c t
  have he : ∀ t, e (t + 1) = Ju *ᵥ e t := fun t => by
    simp only [e, hrec t, forwardU_rec Ju hdet hM hc t, Matrix.mulVec_sub]
    abel
  have hek : ∀ t k, (Ju ^ k) *ᵥ e t = e (t + k) := fun t k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, ← add_assoc, he]
  intro t
  rw [← sub_eq_zero]
  refine eq_zero_of_bounded_orbit Ju⁻¹ Ju hM (Matrix.nonsing_inv_mul _ hdet)
    (C := D + D') fun k => ?_
  rw [hek]
  exact (norm_sub_le _ _).trans (add_le_add (hu _) (hD' _))

/-! ### Blanchard–Kahn -/

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] {m : Type*}
  [Fintype m]

omit [DecidableEq τ] [DecidableEq ι] [DecidableEq σ] in
/-- (1.26), p. 20: the stable part `s_t = (Px_t)_s` of a solution solves
`s_{t+1} = J_ss_t + C_s*z_t`. -/
theorem split_rec_inl {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (G : Matrix ι m ℝ)
    (z : ℕ → m → ℝ) {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (t : ℕ) :
    (P *ᵥ x (t + 1)) ∘ Sum.inl =
      Js *ᵥ ((P *ᵥ x t) ∘ Sum.inl) + (P *ᵥ (G *ᵥ z t)) ∘ Sum.inl := by
  rw [hx t, Matrix.mulVec_add, Matrix.mulVec_mulVec, hPW, ← Matrix.mulVec_mulVec,
    ← blockDiag_mulVec_inl Js Ju]
  rfl

omit [DecidableEq τ] [DecidableEq ι] [DecidableEq σ] in
/-- (1.26), p. 20: the unstable part `u_t = (Px_t)_u` solves `u_{t+1} = J_uu_t + C_u*z_t`. -/
theorem split_rec_inr {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (G : Matrix ι m ℝ)
    (z : ℕ → m → ℝ) {x : ℕ → ι → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (t : ℕ) :
    (P *ᵥ x (t + 1)) ∘ Sum.inr =
      Ju *ᵥ ((P *ᵥ x t) ∘ Sum.inr) + (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr := by
  rw [hx t, Matrix.mulVec_add, Matrix.mulVec_mulVec, hPW, ← Matrix.mulVec_mulVec,
    ← blockDiag_mulVec_inr Js Ju]
  rfl

/-- A solution whose unstable part is bounded is bounded: the stable part always is
(backward solution of a stable system). -/
theorem bounded_of_split {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju)
    (G : Matrix ι m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) {x : ℕ → ι → ℝ}
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) {D : ℝ}
    (hu : ∀ t, ‖(P *ᵥ x t) ∘ Sum.inr‖ ≤ D) : ∃ D', ∀ t, ‖x t‖ ≤ D' := by
  obtain ⟨hPR, hRP, hPW, hJs, -⟩ := hS
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix Js hJs
  obtain ⟨Cc, hCc⟩ := bounded_mulVec P (bounded_mulVec G hz).choose_spec
  have hcs : ∀ t, ‖(P *ᵥ (G *ᵥ z t)) ∘ Sum.inl‖ ≤ Cc := fun t =>
    (norm_comp_inl_le _).trans (hCc t)
  have hs := bounded_backward Js hKa (x := fun t => (P *ᵥ x t) ∘ Sum.inl)
    (split_rec_inl hPW G z hx) hcs
  obtain ⟨r, hr0, hr⟩ := exists_mulVec_bound R
  refine ⟨r * (K * ‖(P *ᵥ x 0) ∘ Sum.inl‖ + K * Cc / (1 - a) + D), fun t => ?_⟩
  have hxt : x t = R *ᵥ (P *ᵥ x t) := by rw [Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
  rw [hxt]
  exact (hr _).trans (mul_le_mul_of_nonneg_left ((norm_sum_type_le _).trans
    (add_le_add (hs t) (hu t))) hr0)

/-- Miao, (1.29), p. 21: along any stable solution, `u_t = (Px_t)_u` is the forward solution
`−∑ⱼ J_u^{−j−1}C_u*z_{t+j}`. -/
theorem eq_1_29 {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju)
    (G : Matrix ι m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) {x : ℕ → ι → ℝ}
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) {D : ℝ} (hxb : ∀ t, ‖x t‖ ≤ D) (t : ℕ) :
    (P *ᵥ x t) ∘ Sum.inr = forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) t := by
  obtain ⟨-, -, hPW, -, hJu⟩ := hS
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  obtain ⟨Cc, hCc⟩ := bounded_mulVec P (bounded_mulVec G hz).choose_spec
  obtain ⟨Dx, hDx⟩ := bounded_mulVec P hxb
  exact forwardU_unique Ju hdet hKa (fun t => (norm_comp_inr_le _).trans (hCc t))
    (fun t => (norm_comp_inr_le _).trans (hDx t)) (split_rec_inr hPW G z hx) t

variable {κ υ : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ]

omit [Fintype τ] [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] [DecidableEq υ] in
/-- Miao, (1.30), p. 21: `s_t = P_skk_t + P_syy_t`. -/
theorem eq_1_30 (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inl = P.toBlocks₁₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₁₂ *ᵥ (x ∘ Sum.inr) :=
  mulVec_comp_inl P x

omit [Fintype τ] [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] [DecidableEq υ] in
/-- Miao, (1.31), p. 21: `u_t = P_ukk_t + P_uyy_t`. -/
theorem eq_1_31 (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inr = P.toBlocks₂₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₂₂ *ᵥ (x ∘ Sum.inr) :=
  mulVec_comp_inr P x

omit [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] in
/-- Miao, (1.32), p. 21: if `QP_uy = I`, `y_t = Qu_t − QP_ukk_t`. -/
theorem eq_1_32 (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (Q : Matrix υ τ ℝ) (hQ : Q * P.toBlocks₂₂ = 1)
    (x : κ ⊕ υ → ℝ) :
    x ∘ Sum.inr = Q *ᵥ ((P *ᵥ x) ∘ Sum.inr) - Q *ᵥ (P.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) := by
  rw [eq_1_31, Matrix.mulVec_add, add_sub_cancel_left, Matrix.mulVec_mulVec, hQ,
    Matrix.one_mulVec]

/-- **Existence** in Theorem 1.4.2 (Miao, pp. 20–22): if `P_uy` has a right inverse `Q`, then
for every `k₀` and every bounded `z` there is a bounded solution with `k`-part `k₀`, namely the
one with `y₀ = Q(u₀ − P_ukk₀)`, `u₀` the forward solution (1.29). -/
theorem bk_exists {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ) (hQ : P.toBlocks₂₂ * Q = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (k₀ : κ → ℝ) :
    ∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 = Sum.elim k₀ (Q *ᵥ (forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0 -
        P.toBlocks₂₁ *ᵥ k₀)) ∧ ∃ D, ∀ t, ‖x t‖ ≤ D := by
  have hS' := hS
  obtain ⟨-, -, hPW, -, hJu⟩ := hS'
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  set c := fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr
  obtain ⟨Cc, hCc⟩ := bounded_mulVec P (bounded_mulVec G hz).choose_spec
  have hc : ∀ t, ‖c t‖ ≤ Cc := fun t => (norm_comp_inr_le _).trans (hCc t)
  obtain ⟨x, hx0, hx⟩ := exists_sol_rec W G z
    (Sum.elim k₀ (Q *ᵥ (forwardU Ju c 0 - P.toBlocks₂₁ *ᵥ k₀)))
  have hu : ∀ t, (P *ᵥ x t) ∘ Sum.inr = forwardU Ju c t := fun t => by
    induction t with
    | zero =>
      rw [mulVec_comp_inr, hx0, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_mulVec, hQ,
        Matrix.one_mulVec]
      abel
    | succ t ih => rw [split_rec_inr hPW G z hx, ih, forwardU_rec Ju hdet hKa hc]
  obtain ⟨D, hD⟩ := forwardU_bounded Ju hKa hc
  exact ⟨x, hx, hx0, bounded_of_split hS G hz hx (D := D) fun t => by rw [hu]; exact hD t⟩

/-- **Uniqueness** in Theorem 1.4.2 (Miao, pp. 20–22): if `P_uy` has a left inverse, two
bounded solutions with the same `k₀` coincide. -/
theorem bk_unique {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ) (hQ : Q * P.toBlocks₂₂ = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C)
    {x y : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t)
    (hy : ∀ t, y (t + 1) = W *ᵥ y t + G *ᵥ z t) {D D' : ℝ} (hxb : ∀ t, ‖x t‖ ≤ D)
    (hyb : ∀ t, ‖y t‖ ≤ D') (h0 : x 0 ∘ Sum.inl = y 0 ∘ Sum.inl) : x = y := by
  refine sol_rec_unique W G z hx hy ?_
  have hux := eq_1_29 hS G hz hx hxb 0
  have huy := eq_1_29 hS G hz hy hyb 0
  have hx2 := eq_1_32 P Q hQ (x 0)
  have hy2 := eq_1_32 P Q hQ (y 0)
  rw [hux, h0] at hx2
  rw [huy] at hy2
  funext i
  rcases i with i | i
  · exact congrFun h0 i
  · exact congrFun (hx2.trans hy2.symm) i

/-- **Theorem 1.4.2** (Blanchard–Kahn, Miao, p. 20). Let `A` be nonsingular and `W = A⁻¹B`
have a real block split `PWP⁻¹ = diag(J_s, J_u)` (`IsRealBlockSplit`; by
`exists_real_block_split` one exists when (iii) `W` has no eigenvalue on the unit circle).
Order `x = (k, y)` with `k` predetermined. If (i) `n_u = n_y` and (ii) `P_uy` is nonsingular,
then for every `k₀` and every stable `z` the system (1.22) has a unique stable solution with
`k`-part `k₀`. -/
theorem theorem_1_4_2 (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (hA : IsUnit A.det) {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (_hi : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (k₀ : κ → ℝ) (z : ℕ → m → ℝ)
    (hz : IsStableSeq z) :
    ∃! x : ℕ → κ ⊕ υ → ℝ, IsSolution A B Cm z x ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableSeq x := by
  obtain ⟨C, hC⟩ := (isStableSeq_iff_exists_le z).1 hz
  obtain ⟨x, hx, hx0, hxb⟩ := bk_exists hS Q hii.1 (A⁻¹ * Cm) hC k₀
  refine ⟨x, ⟨(eq_1_22 A B Cm hA z x).2 hx, by rw [hx0, Sum.elim_comp_inl],
    (isStableSeq_iff_exists_le x).2 hxb⟩, fun y ⟨hy, hy0, hyb⟩ => ?_⟩
  obtain ⟨D, hD⟩ := hxb
  obtain ⟨D', hD'⟩ := (isStableSeq_iff_exists_le y).1 hyb
  exact bk_unique hS Q hii.2 (A⁻¹ * Cm) hC ((eq_1_22 A B Cm hA z y).1 hy) hx hD' hD
    (by rw [hy0, hx0, Sum.elim_comp_inl])

/-! ### (1.33) and the matrix `R_ks` -/

/-- The block equations of `PR = I` and `RP = I`. -/
theorem blocks_of_inv {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) :
    (R.toBlocks₁₁ * P.toBlocks₁₁ + R.toBlocks₁₂ * P.toBlocks₂₁ = 1 ∧
      R.toBlocks₁₁ * P.toBlocks₁₂ + R.toBlocks₁₂ * P.toBlocks₂₂ = 0) ∧
    (P.toBlocks₁₁ * R.toBlocks₁₁ + P.toBlocks₁₂ * R.toBlocks₂₁ = 1 ∧
      P.toBlocks₂₁ * R.toBlocks₁₁ + P.toBlocks₂₂ * R.toBlocks₂₁ = 0) := by
  classical
  have h1 := congrArg Matrix.toBlocks₁₁ hRP
  have h2 := congrArg Matrix.toBlocks₁₂ hRP
  have h3 := congrArg Matrix.toBlocks₁₁ hPR
  have h4 := congrArg Matrix.toBlocks₂₁ hPR
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁] at h1
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂] at h2
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁] at h3
  rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
    Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁] at h4
  refine ⟨⟨h1.trans ?_, h2.trans ?_⟩, ⟨h3.trans ?_, h4.trans ?_⟩⟩ <;>
    ext i j <;> simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.one_apply]

/-- Miao, p. 22: `R_ks` is nonsingular, with `R_ks⁻¹ = P_sk − P_syP_uy⁻¹P_uk`. -/
theorem rks_inv {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) :
    R.toBlocks₁₁ * (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁) = 1 ∧
      (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁) * R.toBlocks₁₁ = 1 := by
  classical
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := blocks_of_inv hPR hRP
  -- `R_ku = −R_ksP_syQ` and `R_ys = −QP_ukR_ks`
  have hku : R.toBlocks₁₂ = -(R.toBlocks₁₁ * P.toBlocks₁₂ * Q) := by
    have := congrArg (· * Q) h2
    simp only [Matrix.add_mul, Matrix.mul_assoc, hQ.1, Matrix.mul_one, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc] at this
    exact eq_neg_of_add_eq_zero_right this
  have hys : R.toBlocks₂₁ = -(Q * P.toBlocks₂₁ * R.toBlocks₁₁) := by
    have := congrArg (Q * ·) h4
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hQ.2, Matrix.one_mul, Matrix.mul_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  constructor
  · rw [hku] at h1
    rw [← h1, Matrix.mul_sub]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    abel
  · rw [hys] at h3
    rw [← h3, Matrix.sub_mul]
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
    abel

/-- Miao, p. 22, the converse: if `R_ks` is nonsingular, so is `P_uy`, with
`P_uy⁻¹ = R_yu − R_ysR_ks⁻¹R_ku`. -/
theorem puy_inv_of_rks {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) (S : Matrix σ κ ℝ)
    (hS : R.toBlocks₁₁ * S = 1 ∧ S * R.toBlocks₁₁ = 1) :
    P.toBlocks₂₂ * (R.toBlocks₂₂ - R.toBlocks₂₁ * S * R.toBlocks₁₂) = 1 ∧
      (R.toBlocks₂₂ - R.toBlocks₂₁ * S * R.toBlocks₁₂) * P.toBlocks₂₂ = 1 := by
  classical
  -- the same argument with the roles of `P` and `R` exchanged
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := blocks_of_inv hRP hPR
  have hR := (blocks_of_inv hPR hRP)
  have e1 : P.toBlocks₂₂ * R.toBlocks₂₂ + P.toBlocks₂₁ * R.toBlocks₁₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hPR
    rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂] at this
    rw [add_comm, this]
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  have e2 : R.toBlocks₂₂ * P.toBlocks₂₂ + R.toBlocks₂₁ * P.toBlocks₁₂ = 1 := by
    have := congrArg Matrix.toBlocks₂₂ hRP
    rw [← Matrix.fromBlocks_toBlocks R, ← Matrix.fromBlocks_toBlocks P,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂] at this
    rw [add_comm, this]
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  clear h1 h3 hR
  -- `P_uk = −P_uyR_ysS` and `P_sy = −SR_kuP_uy`
  have h4' : P.toBlocks₂₁ * R.toBlocks₁₁ + P.toBlocks₂₂ * R.toBlocks₂₁ = 0 := by
    have := (blocks_of_inv hPR hRP).2.2
    exact this
  have h2' : R.toBlocks₁₁ * P.toBlocks₁₂ + R.toBlocks₁₂ * P.toBlocks₂₂ = 0 :=
    (blocks_of_inv hPR hRP).1.2
  have huk : P.toBlocks₂₁ = -(P.toBlocks₂₂ * R.toBlocks₂₁ * S) := by
    have := congrArg (· * S) h4'
    simp only [Matrix.add_mul, Matrix.mul_assoc, hS.1, Matrix.mul_one, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc] at this
    exact eq_neg_of_add_eq_zero_left this
  have hsy : P.toBlocks₁₂ = -(S * R.toBlocks₁₂ * P.toBlocks₂₂) := by
    have := congrArg (S * ·) h2'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hS.2, Matrix.one_mul, Matrix.mul_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  constructor
  · rw [huk] at e1
    rw [← e1, Matrix.mul_sub]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    abel
  · rw [hsy] at e2
    rw [← e2, Matrix.sub_mul]
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
    abel

omit [DecidableEq τ] [DecidableEq σ] in
/-- Miao, p. 22: given `n_s + n_u = n_k + n_y`, the order condition `n_u = n_y` is `n_s = n_k`. -/
theorem bk_order_iff {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    [DecidableEq σ] [DecidableEq τ] (hPR : P * R = 1) (hRP : R * P = 1) :
    Fintype.card τ = Fintype.card υ ↔ Fintype.card σ = Fintype.card κ := by
  have := card_add_card_of_inv hPR hRP
  rw [Fintype.card_sum] at this
  omega

/-- Miao, (1.33), p. 21, checked: along any solution, with `Q = P_uy⁻¹` and
`R_ks⁻¹ = P_sk − P_syQP_uk` (`rks_inv`),
`k_{t+1} = R_ksJ_sR_ks⁻¹k_t + (R_kuC_u* + R_ksC_s*)z_t + (R_kuJ_uP_uy + R_ksJ_sP_sy)P_uy⁻¹u_t`.
The forcing term is written as `R_ku(C*z_t)_u + R_ks(C*z_t)_s` with `C* = PG`. -/
theorem eq_1_33 {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ)
    (z : ℕ → m → ℝ) {x : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (t : ℕ) :
    x (t + 1) ∘ Sum.inl =
      (R.toBlocks₁₁ * Js * (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁)) *ᵥ
          (x t ∘ Sum.inl) +
        (R.toBlocks₁₂ *ᵥ ((P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) +
          R.toBlocks₁₁ *ᵥ ((P *ᵥ (G *ᵥ z t)) ∘ Sum.inl)) +
        ((R.toBlocks₁₂ * Ju * P.toBlocks₂₂ + R.toBlocks₁₁ * Js * P.toBlocks₁₂) * Q) *ᵥ
          ((P *ᵥ x t) ∘ Sum.inr) := by
  obtain ⟨-, hRP, hPW, -, -⟩ := hS
  have hk : x (t + 1) ∘ Sum.inl = R.toBlocks₁₁ *ᵥ ((P *ᵥ x (t + 1)) ∘ Sum.inl) +
      R.toBlocks₁₂ *ᵥ ((P *ᵥ x (t + 1)) ∘ Sum.inr) := by
    rw [← mulVec_comp_inl, Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
  have hs : (P *ᵥ x t) ∘ Sum.inl = (P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁) *ᵥ
      (x t ∘ Sum.inl) + (P.toBlocks₁₂ * Q) *ᵥ ((P *ᵥ x t) ∘ Sum.inr) := by
    rw [mulVec_comp_inl, eq_1_32 P Q hQ.2 (x t)]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]
    abel
  rw [hk, split_rec_inl hPW G z hx, split_rec_inr hPW G z hx, hs]
  simp only [Matrix.mulVec_add, Matrix.add_mul, Matrix.add_mulVec, Matrix.mul_assoc, hQ.1,
    Matrix.mul_one, ← Matrix.mulVec_mulVec]
  abel

/-! ### Corollary 1.4.1 and the stable manifold -/

/-- **Corollary 1.4.1** (Miao, p. 22). Under the conditions of Theorem 1.4.2 and
Assumption 1.4.2 (`z_t = z̄` for `t ≥ T`), the stable solution converges to the steady state
`x̄ = (A − B)⁻¹Cz̄` of (1.21). (`I − W` is invertible because `W` has no eigenvalue `1`
(`IsRealBlockSplit.isUnit_one_sub`), so `A − B` is.) -/
theorem corollary_1_4_1 (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (hA : IsUnit A.det) {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (z : ℕ → m → ℝ) (zbar : m → ℝ) (hz : EventuallyConst z zbar) (x : ℕ → κ ⊕ υ → ℝ)
    (hx : IsSolution A B Cm z x) (hxs : IsStableSeq x) :
    IsUnit (A - B).det ∧ Tendsto x atTop (𝓝 ((A - B)⁻¹ *ᵥ (Cm *ᵥ zbar))) := by
  have hAB := isUnit_sub_det A B hA hS.isUnit_one_sub
  refine ⟨hAB, ?_⟩
  obtain ⟨hPR, hRP, hPW, hJs, hJu⟩ := hS
  set W := A⁻¹ * B
  set G := A⁻¹ * Cm
  set xb := (A - B)⁻¹ *ᵥ (Cm *ᵥ zbar)
  have hbar : xb = W *ᵥ xb + G *ᵥ zbar :=
    (eq_1_22 A B Cm hA (fun _ => zbar) (fun _ => xb)).1 (eq_1_21_solution A B Cm zbar hAB) 0
  obtain ⟨T, hT⟩ := hz
  have hx' := (eq_1_22 A B Cm hA z x).1 hx
  -- deviations from `x̄` after `T` solve the homogeneous system
  set d := fun k => x (k + T) - xb
  have hd : ∀ k, d (k + 1) = W *ᵥ d k + (0 : Matrix (κ ⊕ υ) m ℝ) *ᵥ z k := fun k => by
    simp only [d, Matrix.zero_mulVec, add_zero]
    rw [show k + 1 + T = k + T + 1 by ring, hx' (k + T), hT (k + T) (by omega),
      Matrix.mulVec_sub]
    conv_lhs => rw [hbar]
    abel
  obtain ⟨Dx, hDx⟩ := (isStableSeq_iff_exists_le x).1 hxs
  have hdb : ∀ k, ‖d k‖ ≤ Dx + ‖xb‖ := fun k => (norm_sub_le _ _).trans (add_le_add (hDx _) le_rfl)
  have hz0 : ∀ k, ‖z k‖ ≤ ‖z 0‖ + ‖z (0 + T)‖ + ∑ j ∈ Finset.range T, ‖z j‖ := fun k => by
    rcases lt_or_ge k T with hk | hk
    · have := Finset.single_le_sum (f := fun j => ‖z j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_range.2 hk)
      linarith [norm_nonneg (z 0), norm_nonneg (z (0 + T))]
    · rw [hT k hk, ← hT (0 + T) (by omega)]
      linarith [norm_nonneg (z 0), Finset.sum_nonneg fun j (_ : j ∈ Finset.range T) =>
        norm_nonneg (z j)]
  -- the unstable part vanishes, the stable part decays
  have hu := eq_1_29 ⟨hPR, hRP, hPW, hJs, hJu⟩ 0 hz0 hd hdb
  have hu0 : ∀ k, (P *ᵥ d k) ∘ Sum.inr = 0 := fun k => by
    rw [hu k]
    simp [forwardU]
  have hs : ∀ k, (P *ᵥ d k) ∘ Sum.inl = (Js ^ k) *ᵥ ((P *ᵥ d 0) ∘ Sum.inl) := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [split_rec_inl hPW 0 z hd, ih, pow_succ', ← Matrix.mulVec_mulVec]
      simp
  have hPd : Tendsto (fun k => P *ᵥ d k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_sum_type_le _) ?_
    have e : (fun k => ‖(P *ᵥ d k) ∘ Sum.inl‖ + ‖(P *ᵥ d k) ∘ Sum.inr‖) =
        fun k => ‖(Js ^ k) *ᵥ ((P *ᵥ d 0) ∘ Sum.inl)‖ :=
      funext fun k => by rw [hu0, norm_zero, add_zero, hs k]
    rw [e]
    exact (tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_of_isStableMatrix Js hJs _))
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have h := ((Matrix.mulVecLin R).continuous_of_finiteDimensional.tendsto 0).comp hPd
    simp only [map_zero] at h
    refine h.congr fun k => ?_
    simp only [Function.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hRP,
      Matrix.one_mulVec]
  have h2 := hdlim.add_const xb
  simp only [d, sub_add_cancel, zero_add] at h2
  exact (tendsto_add_atTop_iff_nat T).1 h2

/-- Miao, (1.34), p. 22: the initial value of the stable solution satisfies
`y₀ = P_uy⁻¹u₀ − P_uy⁻¹P_ukk₀`, `u₀` the forward solution (1.29). -/
theorem eq_1_34 {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ) (hQ : Q * P.toBlocks₂₂ = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C)
    {x : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) {D : ℝ}
    (hxb : ∀ t, ‖x t‖ ≤ D) :
    x 0 ∘ Sum.inr = Q *ᵥ forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0 -
      Q *ᵥ (P.toBlocks₂₁ *ᵥ (x 0 ∘ Sum.inl)) := by
  rw [eq_1_32 P Q hQ (x 0), eq_1_29 hS G hz hx hxb 0]

/-- The stable manifold, Miao, p. 22–23: under the conditions of Theorem 1.4.2, `x₀` is the
initial value of a stable solution iff `y₀ = P_uy⁻¹u₀ − P_uy⁻¹P_ukk₀`. -/
theorem stable_initial_iff {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ)
    {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (x₀ : κ ⊕ υ → ℝ) :
    (∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧ x 0 = x₀ ∧
        ∃ D, ∀ t, ‖x t‖ ≤ D) ↔
      x₀ ∘ Sum.inr = Q *ᵥ forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0 -
        Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) := by
  constructor
  · rintro ⟨x, hx, rfl, D, hD⟩
    exact eq_1_34 hS Q hQ.2 G hz hx hD
  · intro h
    obtain ⟨x, hx, hx0, hxb⟩ := bk_exists hS Q hQ.1 G hz (x₀ ∘ Sum.inl)
    refine ⟨x, hx, ?_, hxb⟩
    rw [hx0]
    funext i
    rcases i with i | i
    · rfl
    · have := congrFun h i
      simp only [Function.comp_apply] at this
      rw [this, Matrix.mulVec_sub]
      rfl

/-- The stable arm of the homogeneous system: `{x : (Px)_u = 0}`. -/
noncomputable def stableArm (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) : Submodule ℝ (κ ⊕ υ → ℝ) :=
  LinearMap.ker (LinearMap.funLeft ℝ ℝ Sum.inr ∘ₗ P.mulVecLin)

omit [Fintype τ] [DecidableEq τ] [Fintype σ] [DecidableEq σ] [DecidableEq κ] [DecidableEq υ] in
theorem mem_stableArm (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (x : κ ⊕ υ → ℝ) :
    x ∈ stableArm P ↔ (P *ᵥ x) ∘ Sum.inr = 0 := by
  simp [stableArm, LinearMap.funLeft]

/-- The stable manifold (1.34) of the homogeneous system `x_{t+1} = Wx_t` (Miao, p. 23): the
initial values of stable solutions form the linear subspace `stableArm P`. -/
theorem stableArm_iff {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (x₀ : κ ⊕ υ → ℝ) :
    (∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t) ∧ x 0 = x₀ ∧ ∃ D, ∀ t, ‖x t‖ ≤ D) ↔
      x₀ ∈ stableArm P := by
  rw [mem_stableArm]
  have hS' := hS
  obtain ⟨-, -, hPW, -, -⟩ := hS'
  have hz : ∀ t : ℕ, ‖(fun _ => (0 : Fin 0 → ℝ)) t‖ ≤ 0 := fun _ => by simp
  have hrec : ∀ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t) →
      ∀ t, x (t + 1) = W *ᵥ x t + (0 : Matrix (κ ⊕ υ) (Fin 0) ℝ) *ᵥ (fun _ => 0) t :=
    fun x hx t => by rw [hx t, Matrix.zero_mulVec, add_zero]
  constructor
  · rintro ⟨x, hx, rfl, D, hD⟩
    rw [eq_1_29 hS 0 hz (hrec x hx) hD 0]
    simp [forwardU]
  · intro h0
    obtain ⟨x, hx0, hx⟩ := exists_sol_rec W (0 : Matrix (κ ⊕ υ) (Fin 0) ℝ) (fun _ => 0) x₀
    have hu : ∀ t, (P *ᵥ x t) ∘ Sum.inr = 0 := fun t => by
      induction t with
      | zero => rw [hx0, h0]
      | succ t ih => rw [split_rec_inr hPW 0 _ hx, ih]; simp
    refine ⟨x, fun t => by rw [hx t, Matrix.zero_mulVec, add_zero], hx0,
      bounded_of_split hS 0 hz hx (D := 0) fun t => by rw [hu]; simp⟩

omit [Fintype σ] [DecidableEq σ] [DecidableEq κ] in
/-- Miao, p. 23: the stable arm is `n_k`-dimensional when `P_uy` is nonsingular. -/
theorem finrank_stableArm (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) :
    finrank ℝ (stableArm P) = Fintype.card κ := by
  classical
  set N : Matrix (κ ⊕ υ) κ ℝ :=
    Matrix.of fun i j => Sum.elim (fun a => (1 : Matrix κ κ ℝ) a j)
      (fun b => (-(Q * P.toBlocks₂₁)) b j) i
  have hNl : ∀ k, (N *ᵥ k) ∘ Sum.inl = k := fun k => by
    funext a; simp [N, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hNr : ∀ k, (N *ᵥ k) ∘ Sum.inr = -(Q * P.toBlocks₂₁) *ᵥ k := fun k => by
    funext b; simp [N, Matrix.mulVec, dotProduct]
  have hrange : LinearMap.range (Matrix.toLin' N) = stableArm P := by
    ext x
    rw [LinearMap.mem_range, mem_stableArm, mulVec_comp_inr]
    constructor
    · rintro ⟨k, rfl⟩
      rw [Matrix.toLin'_apply, hNl, hNr, Matrix.neg_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQ.1, Matrix.one_mul, add_neg_cancel]
    · intro h
      refine ⟨x ∘ Sum.inl, ?_⟩
      rw [Matrix.toLin'_apply]
      funext i
      rcases i with a | b
      · exact congrFun (hNl _) a
      · have h2 := congrArg (fun v => Q *ᵥ v) h
        simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, hQ.2, Matrix.one_mulVec,
          Matrix.mulVec_zero] at h2
        have := congrFun (hNr (x ∘ Sum.inl)) b
        change ((N *ᵥ x ∘ Sum.inl) ∘ Sum.inr) b = _
        rw [this, Matrix.neg_mulVec]
        have h3 := congrFun h2 b
        simp only [Pi.add_apply, Function.comp_apply, Pi.zero_apply] at h3 ⊢
        rw [Pi.neg_apply]
        linarith
  have hinj : Function.Injective (Matrix.toLin' N) := fun k k' h => by
    have := congrArg (fun v => v ∘ Sum.inl) h
    simpa [Matrix.toLin'_apply, hNl] using this
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]

/-- Miao, p. 23, corrected: for a nonzero forcing the stable manifold is an affine subspace, the
translate of the `n_k`-dimensional `stableArm P` by `x̂ = (0, P_uy⁻¹u₀)`; it is a linear subspace
only when `u₀ = 0`. -/
theorem stable_initial_translate {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ)
    {z : ℕ → m → ℝ} {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (x₀ : κ ⊕ υ → ℝ) :
    (∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧ x 0 = x₀ ∧
        ∃ D, ∀ t, ‖x t‖ ≤ D) ↔
      x₀ - Sum.elim (0 : κ → ℝ) (Q *ᵥ forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0) ∈
        stableArm P := by
  rw [stable_initial_iff hS Q hQ G hz, mem_stableArm, mulVec_comp_inr]
  set u₀ := forwardU Ju (fun t => (P *ᵥ (G *ᵥ z t)) ∘ Sum.inr) 0
  have hl : (x₀ - Sum.elim (0 : κ → ℝ) (Q *ᵥ u₀)) ∘ Sum.inl = x₀ ∘ Sum.inl := by funext a; simp
  have hr : (x₀ - Sum.elim (0 : κ → ℝ) (Q *ᵥ u₀)) ∘ Sum.inr = x₀ ∘ Sum.inr - Q *ᵥ u₀ := by
    funext a; simp
  rw [hl, hr]
  constructor
  · intro h
    rw [h, show Q *ᵥ u₀ - Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) - Q *ᵥ u₀ =
        -(Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl))) by abel, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec, add_neg_cancel]
  · intro h
    have h2 : Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) + (x₀ ∘ Sum.inr - Q *ᵥ u₀) = 0 := by
      have := congrArg (fun v => Q *ᵥ v) h
      simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at this
      rwa [Matrix.mulVec_mulVec _ Q P.toBlocks₂₂, hQ.2, Matrix.one_mulVec] at this
    calc x₀ ∘ Sum.inr = (Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl)) + (x₀ ∘ Sum.inr - Q *ᵥ u₀)) +
          (Q *ᵥ u₀ - Q *ᵥ (P.toBlocks₂₁ *ᵥ (x₀ ∘ Sum.inl))) := by abel
      _ = _ := by rw [h2, zero_add]

/-- Miao, p. 23 (eigenvalues on the unit circle): for `x_{t+1} = x_t + z_t` with `z_t = 1`
(`n_k = 1`, `n_u = n_y = 0`, the eigenvalue `1` violates (iii)) no solution is stable: `k_t`
drifts like a random walk with drift, `x_t = x₀ + t`. -/
theorem remark_unit_root (x : ℕ → Fin 1 → ℝ)
    (hx : ∀ t, x (t + 1) = (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x t +
      (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ => 1)) :
    Module.End.HasEigenvalue
      (Matrix.toLin' ((1 : Matrix (Fin 1) (Fin 1) ℝ).map Complex.ofRealHom)) 1 ∧
      ¬ IsStableSeq x := by
  have hev : Module.End.HasEigenvalue
      (Matrix.toLin' ((1 : Matrix (Fin 1) (Fin 1) ℝ).map Complex.ofRealHom)) 1 := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ => (1 : ℂ))
      ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · rw [Matrix.toLin'_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec,
        one_smul]
    · intro h
      simpa using congrFun h 0
  refine ⟨hev, fun hs => ?_⟩
  have hxt : ∀ t : ℕ, x t 0 = x 0 0 + t := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hx t]
      simp [ih]
      ring
  obtain ⟨M, -, hM⟩ := hs
  obtain ⟨t, ht⟩ := exists_nat_gt (M - x 0 0)
  have h1 := (norm_le_pi_norm (x t) 0).trans_lt (hM t)
  rw [hxt, Real.norm_eq_abs] at h1
  linarith [le_abs_self (x 0 0 + t)]

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# When the Blanchard–Kahn conditions fail: Theorem 1.4.3

Miao, §1.4.1, p. 23. The book states: "If `n_u > n_y`, then there is no solution to (1.22). If
`n_u < n_y`, then there are infinitely many solutions to (1.22)."

**As printed, the first claim is false**: with `A` nonsingular, (1.22) has a (unique) solution
from every `x₀ = (k₀, y₀)` (`exists_unique_solution`); `theorem_1_4_3_printed_gt_false` gives a
block split with `n_u = 1 > n_y = 0` and a solution. The second claim is true but empty: as soon
as `n_y ≥ 1` there are infinitely many solutions with a given `k₀`, whatever `n_u`
(`theorem_1_4_3_printed_lt`). The intended statements concern **stable** solutions:

* `theorem_1_4_3_gt`: if `n_u > n_y`, then for every `z` there is a `k₀` from which no
  stable solution starts (the admissible `k₀` lie in a translate of the range of `R_ks`, of
  dimension at most `n_s < n_k`).
* `theorem_1_4_3_lt`: if `n_u < n_y` and one stable solution with initial `k₀` exists, there
  are infinitely many (add multiples of a stable homogeneous solution `R(J_sᵗs, 0)` with
  `R_kss = 0`, `s ≠ 0`, which exists since `n_s > n_k`).
* `theorem_1_4_3_lt_exists`: if moreover `P_uy` has full row rank (a right inverse), a stable
  solution exists for every `k₀` and every bounded `z`, hence infinitely many.
* Without the rank condition, `n_u < n_y` does not give any stable solution:
  `theorem_1_4_3_lt_counterexample` (`n_k = 1`, `n_y = 2`, `n_u = 1`, the unstable root sits on
  the predetermined variable, and `k₀ = 1` has no stable solution).
-/

open Filter Topology

namespace Miao.DifferenceEquations

open Module
open scoped Matrix

variable {κ υ σ τ : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ]
  [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] {m : Type*} [Fintype m]

/-- The predetermined part of the initial value of a stable homogeneous solution lies in the
range of `R_ks`. -/
theorem homog_stable_mem_range {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) {x : ℕ → κ ⊕ υ → ℝ} (hx : ∀ t, x (t + 1) = W *ᵥ x t)
    {D : ℝ} (hD : ∀ t, ‖x t‖ ≤ D) :
    x 0 ∘ Sum.inl ∈ LinearMap.range (Matrix.toLin' R.toBlocks₁₁) := by
  have h0 := (mem_stableArm P (x 0)).1 ((stableArm_iff hS (x 0)).1 ⟨x, hx, rfl, D, hD⟩)
  refine ⟨(P *ᵥ x 0) ∘ Sum.inl, ?_⟩
  have : x 0 = R *ᵥ (P *ᵥ x 0) := by rw [Matrix.mulVec_mulVec, hS.2.1, Matrix.one_mulVec]
  conv_rhs => rw [this, mulVec_comp_inl, h0, Matrix.mulVec_zero, add_zero]
  rw [Matrix.toLin'_apply]

/-- **Theorem 1.4.3, first part, corrected** (Miao, p. 23): if `n_u > n_y`, then for every
forcing sequence (bounded or not) there is an initial `k₀` from which (1.22) has no stable
solution. -/
theorem theorem_1_4_3_gt {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card υ < Fintype.card τ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) :
    ∃ k₀ : κ → ℝ, ¬ ∃ x : ℕ → κ ⊕ υ → ℝ, (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 ∘ Sum.inl = k₀ ∧ ∃ D, ∀ t, ‖x t‖ ≤ D := by
  by_contra h
  push Not at h
  choose x hx hx0 D hD using h
  have hcard := card_add_card_of_inv hS.1 hS.2.1
  rw [Fintype.card_sum] at hcard
  have htop : LinearMap.range (Matrix.toLin' R.toBlocks₁₁) = ⊤ := by
    refine eq_top_iff.2 fun k _ => ?_
    set d := fun t => x k t - x 0 t
    have hd : ∀ t, d (t + 1) = W *ᵥ d t := fun t => by
      simp only [d, hx k t, hx 0 t, Matrix.mulVec_sub]
      abel
    have := homog_stable_mem_range hS hd (D := D k + D 0) fun t =>
      (norm_sub_le _ _).trans (add_le_add (hD k t) (hD 0 t))
    have e : d 0 ∘ Sum.inl = k := by
      funext i
      have h1 := congrFun (hx0 k) i
      have h2 := congrFun (hx0 0) i
      simp only [Function.comp_apply, Pi.zero_apply] at h1 h2
      simp [d, h1, h2]
    rwa [e] at this
  have hle := LinearMap.finrank_range_le (Matrix.toLin' R.toBlocks₁₁)
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card] at hle
  omega

/-- **Theorem 1.4.3, second part, corrected** (Miao, p. 23): if `n_u < n_y` and (1.22) has one
stable solution with initial `k₀`, it has infinitely many. -/
theorem theorem_1_4_3_lt {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card τ < Fintype.card υ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) (x : ℕ → κ ⊕ υ → ℝ)
    (hx : ∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) (hxb : ∃ D, ∀ t, ‖x t‖ ≤ D) :
    {x' : ℕ → κ ⊕ υ → ℝ | (∀ t, x' (t + 1) = W *ᵥ x' t + G *ᵥ z t) ∧
      x' 0 ∘ Sum.inl = x 0 ∘ Sum.inl ∧ ∃ D, ∀ t, ‖x' t‖ ≤ D}.Infinite := by
  have hcard := card_add_card_of_inv hS.1 hS.2.1
  rw [Fintype.card_sum] at hcard
  have hker : LinearMap.ker (Matrix.toLin' R.toBlocks₁₁) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]; omega)
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hs
  set d₀ := R *ᵥ Sum.elim s 0
  have hPd : P *ᵥ d₀ = Sum.elim s 0 := by
    rw [Matrix.mulVec_mulVec, hS.1, Matrix.one_mulVec]
  have hd₀ : d₀ ∈ stableArm P := by
    rw [mem_stableArm, hPd, Sum.elim_comp_inr]
  obtain ⟨d, hd, hd0, Dd, hDd⟩ := (stableArm_iff hS d₀).2 hd₀
  have hdk : d 0 ∘ Sum.inl = 0 := by
    rw [hd0, mulVec_comp_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, hs, Matrix.mulVec_zero,
      add_zero]
  have hdne : d 0 ≠ 0 := fun h => hs0 (by
    have := congrArg (fun v => (P *ᵥ v) ∘ Sum.inl) h
    simpa [hd0, hPd] using this)
  obtain ⟨Dx, hDx⟩ := hxb
  refine Set.infinite_of_injective_forall_mem (f := fun c : ℝ => x + c • d) (fun c c' h => ?_)
    fun c => ⟨fun t => ?_, ?_, ⟨Dx + |c| * Dd, fun t => ?_⟩⟩
  · have h1 := congrFun h 0
    simp only [Pi.add_apply, Pi.smul_apply, add_right_inj] at h1
    exact smul_left_injective ℝ hdne h1
  · simp only [Pi.add_apply, Pi.smul_apply, hx t, hd t, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel
  · funext i
    have := congrFun hdk i
    simp only [Function.comp_apply, Pi.zero_apply] at this
    simp [this]
  · simp only [Pi.add_apply, Pi.smul_apply]
    refine (norm_add_le _ _).trans (add_le_add (hDx t) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hDd t) (abs_nonneg c)

/-- Miao, p. 23, corrected: if `n_u < n_y` and `P_uy` has full row rank (a right inverse), then
for every `k₀` and every bounded `z` there are infinitely many stable solutions. -/
theorem theorem_1_4_3_lt_exists {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju)
    (hlt : Fintype.card τ < Fintype.card υ) (Q : Matrix υ τ ℝ) (hQ : P.toBlocks₂₂ * Q = 1)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) (hz : ∃ C, ∀ t, ‖z t‖ ≤ C) (k₀ : κ → ℝ) :
    {x : ℕ → κ ⊕ υ → ℝ | (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 ∘ Sum.inl = k₀ ∧ ∃ D, ∀ t, ‖x t‖ ≤ D}.Infinite := by
  obtain ⟨C, hC⟩ := hz
  obtain ⟨x, hx, hx0, hxb⟩ := bk_exists hS Q hQ G hC k₀
  have := theorem_1_4_3_lt hS hlt G z x hx hxb
  rwa [hx0, Sum.elim_comp_inl] at this

omit [DecidableEq κ] [DecidableEq υ] in
/-- Miao, p. 23: the second claim of Theorem 1.4.3 as printed ("infinitely many solutions") holds
whenever there is a jump variable, whatever `n_u`: every `y₀` starts a solution. -/
theorem theorem_1_4_3_printed_lt [Nonempty υ] (W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → ℝ) (k₀ : κ → ℝ) :
    {x : ℕ → κ ⊕ υ → ℝ | (∀ t, x (t + 1) = W *ᵥ x t + G *ᵥ z t) ∧
      x 0 ∘ Sum.inl = k₀}.Infinite := by
  obtain ⟨i₀⟩ := ‹Nonempty υ›
  refine Set.infinite_of_injective_forall_mem
    (f := fun c : ℝ => fun t => Nat.rec (Sum.elim k₀ fun _ => c)
      (fun t xt => W *ᵥ xt + G *ᵥ z t) t) (fun c c' h => ?_) fun c => ⟨fun _ => rfl, rfl⟩
  have := congrFun (congrFun h 0) (Sum.inr i₀)
  simpa using this

/-! ### Counterexamples -/

/-- The eigenvalues of `cI` are `c`. -/
theorem hasEigenvalue_smul_one {c : ℝ} {μ : ℂ}
    (h : Module.End.HasEigenvalue
      (Matrix.toLin' ((c • (1 : Matrix σ σ ℝ)).map Complex.ofRealHom)) μ) : μ = c := by
  classical
  obtain ⟨w, hw⟩ := h.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw.2
  have := congrFun h1 i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.one_apply,
    apply_ite (fun r : ℝ => (r : ℂ)), ite_mul] at this
  exact (this.resolve_right hi).symm

/-- Miao, p. 23: the first claim of Theorem 1.4.3 as printed is false. For `k_{t+1} = 2k_t` with
`k` predetermined and no jump variable, the real block split has `n_u = 1 > n_y = 0`, yet
(1.22) has a solution from `k₀ = 1` (the backward solution `k_t = 2ᵗ`, which is not stable). -/
theorem theorem_1_4_3_printed_gt_false :
    IsRealBlockSplit
      (Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
        (0 : Matrix (Fin 0) (Fin 0) ℝ))
      (Matrix.fromBlocks (0 : Matrix (Fin 0) (Fin 1) ℝ) 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) 0)
      (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 0) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0)
      (0 : Matrix (Fin 0) (Fin 0) ℝ) ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
      Fintype.card (Fin 0) < Fintype.card (Fin 1) ∧
      ∃ x : ℕ → Fin 1 ⊕ Fin 0 → ℝ,
        (∀ t, x (t + 1) = Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
          (0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ x t) ∧ x 0 ∘ Sum.inl = fun _ => 1 := by
  refine ⟨⟨?_, ?_, ?_, fun μ hμ => ?_, fun μ hμ => ?_⟩, by simp, ?_⟩
  · ext (i | i) (j | j) <;>
      first | exact i.elim0 | simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;>
      first | exact i.elim0 | simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;>
      first | exact i.elim0 | simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    exact absurd (funext fun i => i.elim0) hw.2
  · rw [hasEigenvalue_smul_one hμ]; norm_num
  · obtain ⟨x, hx0, hx⟩ := exists_sol_rec (Matrix.fromBlocks
      ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 (0 : Matrix (Fin 0) (Fin 0) ℝ))
      (0 : Matrix (Fin 1 ⊕ Fin 0) (Fin 0) ℝ) (fun _ => 0) (Sum.elim (fun _ => 1) 0)
    exact ⟨x, fun t => by rw [hx t, Matrix.zero_mulVec, add_zero], by rw [hx0]; rfl⟩

/-- Miao, p. 23: with `n_u < n_y` but `P_uy` without full row rank, a stable solution need not
exist. Here `n_k = 1`, `n_y = 2`, `W = diag(2, ½, ½)`, the unstable root belongs to the
predetermined variable (`P_uy = 0`), and from `k₀ = 1` no solution is stable. -/
theorem theorem_1_4_3_lt_counterexample :
    IsRealBlockSplit
      (Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 1) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) 0)
      (Matrix.fromBlocks (0 : Matrix (Fin 1) (Fin 2) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)
        (1 : Matrix (Fin 2) (Fin 2) ℝ) 0)
      ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
      Fintype.card (Fin 1) < Fintype.card (Fin 2) ∧
      ∀ x : ℕ → Fin 1 ⊕ Fin 2 → ℝ,
        (∀ t, x (t + 1) = Matrix.fromBlocks ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) 0 0
          ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ x t) →
        x 0 ∘ Sum.inl = (fun _ => 1) → ¬ IsStableSeq x := by
  refine ⟨⟨?_, ?_, ?_, fun μ hμ => ?_, fun μ hμ => ?_⟩, by simp, fun x hx hx0 hs => ?_⟩
  · ext (i | i) (j | j) <;> simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;> simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · ext (i | i) (j | j) <;> simp [Matrix.fromBlocks_multiply, Matrix.one_apply]
  · rw [hasEigenvalue_smul_one hμ]; norm_num
  · rw [hasEigenvalue_smul_one hμ]; norm_num
  · have hk : ∀ t : ℕ, x t (Sum.inl 0) = 2 ^ t := fun t => by
      induction t with
      | zero => simpa using congrFun hx0 0
      | succ t ih =>
        rw [hx t, Matrix.fromBlocks_mulVec]
        simp [Matrix.mulVec, dotProduct, ih, pow_succ, mul_comm]
    obtain ⟨M, -, hM⟩ := hs
    obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
    have h1 := (norm_le_pi_norm (x t) (Sum.inl 0)).trans_lt (hM t)
    rw [hk, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    linarith

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Generalized eigenvalues and the complex generalized Schur (QZ) form

Miao, §1.4.2, pp. 24–25: Definition 1.4.6 and Theorem 1.4.4. The book omits the proof (it cites
Golub and van Loan); Mathlib has no Schur or QZ decomposition, so it is built here.

* `IsGenEigenvector`, `IsGenEigenvalue`, `genEigenvalues` (Definition 1.4.6): `Bx = λAx` with
  `x ≠ 0`; `isGenEigenvalue_iff_det`: `λ ∈ λ(A, B)` iff `det(B − λA) = 0`.
* `theorem_1_4_4`: for a regular pair `(A, B)` (Assumption 1.4.1) there are unitary `Q`, `Z`
  with `S = QAZ` and `T = QBZ` upper triangular (items 1–2), `sᵢᵢ, tᵢᵢ` never both zero (item 3),
  `λ(A, B) = {tᵢᵢ/sᵢᵢ : sᵢᵢ ≠ 0}` (item 4), and the diagonal pairs ordered by any prescribed
  scale-invariant predicate `P`: the pairs satisfying `P` come first (item 5, see below).
* `theorem_1_4_4_stable`: the case used in Theorem 1.4.5, `P(s, t) := |t| < |s|`, so that the
  stable generalized eigenvalues come first (a pair with `sᵢᵢ = 0` is an infinite, unstable,
  eigenvalue).
* `diag_ne_zero_of_regular` and `genEigenvalues_eq_diag` give items 3 and 4 for *any* unitary
  `Q`, `Z` triangularising the pencil.

Proof: induction on `n`. A generalized eigenvector `z` exists (an eigenvector of `D⁻¹A` with
`D = αA − B` invertible); `Az` and `Bz` are multiples of one unit vector `q`. Completing `z` and
`q` to unitary matrices `W` and `V*` (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`)
makes the first column of `V*AW` and `V*BW` vanish below the diagonal; the lower right blocks form a
regular pencil, which is triangularised by induction. For the ordering, an eigenvector of a pair
satisfying `P` is used whenever one exists; the diagonal pairs of the deflated pencil are
generalized eigenpairs of the original one (determinant identity), so once no pair satisfies `P`
none appears later.

**Departure.** Item 5 ("the pairs can be arranged in any order") is proved in the weaker form
needed by the book: for every predicate `P` on pairs with `P(cs, ct) ↔ P(s, t)` for `c ≠ 0`
there is `m` with `i < m ↔ P(sᵢᵢ, tᵢᵢ)`. An arbitrary permutation of the diagonal pairs is not
formalised.
-/

namespace Miao.DifferenceEquations

open scoped Matrix

/-! ### Definition 1.4.6 -/

/-- **Definition 1.4.6** (Miao, p. 24): `x` is a right generalized eigenvector of `(A, B)` for
`λ` if `x ≠ 0` and `Bx = λAx`. -/
def IsGenEigenvector {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (lam : ℂ) (x : ι → ℂ) :
    Prop :=
  x ≠ 0 ∧ B *ᵥ x = lam • (A *ᵥ x)

/-- **Definition 1.4.6** (Miao, p. 24): `λ ∈ ℂ` is a generalized eigenvalue of `(A, B)`. -/
def IsGenEigenvalue {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (lam : ℂ) : Prop :=
  ∃ x, IsGenEigenvector A B lam x

/-- The set `λ(A, B)` of generalized eigenvalues (Miao, p. 24). -/
def genEigenvalues {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) : Set ℂ :=
  {lam | IsGenEigenvalue A B lam}

/-- Miao, p. 24: `λ` is a generalized eigenvalue iff `det(B − λA) = 0`. -/
theorem isGenEigenvalue_iff_det {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (lam : ℂ) : IsGenEigenvalue A B lam ↔ (B - lam • A).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  simp only [IsGenEigenvalue, IsGenEigenvector, Matrix.sub_mulVec, Matrix.smul_mulVec,
    sub_eq_zero]

/-! ### Unitary equivalence -/

theorem det_ne_zero_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : U.det ≠ 0 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.1 hU)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact left_ne_zero_of_mul_eq_one h

theorem conj_lincomb {ι : Type*} [Fintype ι] (Q Z X Y : Matrix ι ι ℂ) (a b : ℂ) :
    a • (Q * X * Z) - b • (Q * Y * Z) = Q * (a • X - b • Y) * Z := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The pencil determinant is multiplied by `det Q · det Z` under `(A, B) ↦ (QAZ, QBZ)`. -/
theorem det_conj_lincomb {ι : Type*} [Fintype ι] [DecidableEq ι] (Q Z X Y : Matrix ι ι ℂ)
    (a b : ℂ) : (a • (Q * X * Z) - b • (Q * Y * Z)).det = Q.det * (a • X - b • Y).det * Z.det := by
  rw [conj_lincomb, Matrix.det_mul, Matrix.det_mul]

/-- The pencil `a • T − b • S` of two upper triangular matrices is upper triangular. -/
theorem upper_lincomb {n : ℕ} {S T : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (a b : ℂ) : (a • T - b • S).IsUpperTriangular := by
  intro i j h
  simp [hS h, hT h]

theorem det_upper_lincomb {n : ℕ} {S T : Matrix (Fin n) (Fin n) ℂ} (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (a b : ℂ) :
    (a • T - b • S).det = ∏ i, (a * T i i - b * S i i) := by
  rw [Matrix.det_of_isUpperTriangular (upper_lincomb hS hT a b)]
  simp

/-- **Theorem 1.4.4(3)** (Miao, p. 25): for a regular pencil, `sᵢᵢ` and `tᵢᵢ` are not both zero,
for any unitary `Q`, `Z` making `QAZ` and `QBZ` upper triangular. -/
theorem diag_ne_zero_of_regular {n : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hreg : IsRegular A B) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (hS : (Q * A * Z).IsUpperTriangular)
    (hT : (Q * B * Z).IsUpperTriangular) (i : Fin n) :
    (Q * A * Z) i i ≠ 0 ∨ (Q * B * Z) i i ≠ 0 := by
  obtain ⟨α, hα⟩ := hreg
  by_contra h
  push Not at h
  have h0 : (α • (Q * A * Z) - (1 : ℂ) • (Q * B * Z)).det = 0 := by
    rw [det_upper_lincomb hT hS]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h.1, h.2])
  rw [det_conj_lincomb, one_smul] at h0
  simp [det_ne_zero_of_unitary hQ, det_ne_zero_of_unitary hZ, hα] at h0

/-- **Theorem 1.4.4(4)** (Miao, p. 25): `λ(A, B) = {tᵢᵢ/sᵢᵢ : sᵢᵢ ≠ 0}`, for any unitary `Q`, `Z`
making `S = QAZ` and `T = QBZ` upper triangular. -/
theorem genEigenvalues_eq_diag {n : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hreg : IsRegular A B) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (hS : (Q * A * Z).IsUpperTriangular)
    (hT : (Q * B * Z).IsUpperTriangular) :
    genEigenvalues A B =
      {lam | ∃ i, (Q * A * Z) i i ≠ 0 ∧ lam = (Q * B * Z) i i / (Q * A * Z) i i} := by
  ext lam
  have hdet : (B - lam • A).det = 0 ↔ ∃ i, (Q * B * Z) i i - lam * (Q * A * Z) i i = 0 := by
    have h := det_conj_lincomb Q Z B A 1 lam
    rw [det_upper_lincomb hS hT, one_smul] at h
    simp only [one_mul] at h
    have hp : (∃ i, (Q * B * Z) i i - lam * (Q * A * Z) i i = 0) ↔
        ∏ i, ((Q * B * Z) i i - lam * (Q * A * Z) i i) = 0 := by
      simp [Finset.prod_eq_zero_iff]
    rw [hp, h]
    simp [det_ne_zero_of_unitary hQ, det_ne_zero_of_unitary hZ]
  change IsGenEigenvalue A B lam ↔ _
  rw [isGenEigenvalue_iff_det, hdet]
  constructor
  · rintro ⟨i, hi⟩
    have hs : (Q * A * Z) i i ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero] at hi
      rcases diag_ne_zero_of_regular hreg hQ hZ hS hT i with h | h
      · exact h h0
      · exact h hi
    exact ⟨i, hs, by rw [eq_div_iff hs]; linear_combination -hi⟩
  · rintro ⟨i, hs, rfl⟩
    exact ⟨i, by field_simp; ring⟩

/-! ### Generalized eigenpairs and deflation -/

/-- A regular pencil of positive size has a generalized eigenvector: `z ≠ 0` and
`(s, t) ≠ (0, 0)` with `sBz = tAz`. -/
theorem exists_eigenPair {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hreg : IsRegular A B) :
    ∃ z : Fin (n + 1) → ℂ, z ≠ 0 ∧ ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ s • (B *ᵥ z) = t • (A *ᵥ z) := by
  obtain ⟨α, hα⟩ := hreg
  set D := α • A - B
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (D⁻¹ * A))
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have h1 : D⁻¹ *ᵥ (A *ᵥ z) = μ • z := by
    have := hz.apply_eq_smul
    rwa [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec] at this
  have hAz : A *ᵥ z = μ • (α • (A *ᵥ z) - B *ᵥ z) := by
    have h2 := congrArg (D *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h2
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv D (isUnit_iff_ne_zero.2 hα),
      Matrix.one_mul] at h2
    conv_lhs => rw [h2]
    simp [D, Matrix.sub_mulVec, Matrix.smul_mulVec]
  refine ⟨z, hz.2, μ, μ * α - 1, ?_, by linear_combination (norm := module) hAz⟩
  by_cases hμ0 : μ = 0
  · right; simp [hμ0]
  · left; exact hμ0

/-- A nonzero vector is a nonzero multiple of the `i₀`-th column of a unitary matrix. -/
theorem exists_unitary_col {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) {w : ι → ℂ}
    (hw : w ≠ 0) : ∃ U ∈ Matrix.unitaryGroup ι ℂ, ∃ r : ℂ, r ≠ 0 ∧
      w = r • (U *ᵥ Pi.single i₀ 1) := by
  set r : ℂ := (‖WithLp.toLp 2 w‖ : ℂ)
  have hr : r ≠ 0 := by
    simp only [r, ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
    intro h
    exact hw (congrArg WithLp.ofLp h)
  set z : ι → ℂ := r⁻¹ • w
  have hz : z ⬝ᵥ star z = 1 := by
    have h1 : ‖WithLp.toLp 2 z‖ = 1 := by
      simp only [z, WithLp.toLp_smul, norm_smul, norm_inv, r, Complex.norm_real, norm_norm]
      exact inv_mul_cancel₀ (by simpa [r] using hr)
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 z)
    rw [h1, EuclideanSpace.inner_toLp_toLp] at h2
    simpa using h2
  set v : ι → EuclideanSpace ℂ ι := fun _ => WithLp.toLp 2 z
  have hv : Orthonormal ℂ (({i₀} : Set ι).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rw [Set.mem_singleton_iff] at hi hj
    subst hi hj
    simp only [↓reduceIte]
    exact (EuclideanSpace.inner_toLp_toLp z z).trans hz
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b, r, hr, ?_⟩
  have hcol : (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b *ᵥ Pi.single i₀ 1 = z := by
    rw [Matrix.mulVec_single_one]
    funext i
    rw [Matrix.col_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, hb i₀ rfl]
  rw [hcol, smul_smul, mul_inv_cancel₀ hr, one_smul]

/-- **Deflation.** From a generalized eigenvector `z` of a regular pencil, unitary `V`, `W` such
that the first columns of `VAW` and `VBW` vanish below the diagonal, with leading pair
proportional to `(s, t)` and not `(0, 0)`. -/
theorem deflate {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hreg : IsRegular A B)
    {z : Fin (n + 1) → ℂ} (hz : z ≠ 0) {s t : ℂ} (hst : s ≠ 0 ∨ t ≠ 0)
    (he : s • (B *ᵥ z) = t • (A *ᵥ z)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ, ∃ W ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ,
      (∀ i : Fin n, (V * A * W) i.succ 0 = 0) ∧ (∀ i : Fin n, (V * B * W) i.succ 0 = 0) ∧
      s * (V * B * W) 0 0 = t * (V * A * W) 0 0 ∧
      ((V * A * W) 0 0 ≠ 0 ∨ (V * B * W) 0 0 ≠ 0) := by
  -- `Az = a w`, `Bz = b w` for one nonzero `w`
  have hw : ∃ w : Fin (n + 1) → ℂ, w ≠ 0 ∧ ∃ a b : ℂ, A *ᵥ z = a • w ∧ B *ᵥ z = b • w ∧
      (a ≠ 0 ∨ b ≠ 0) ∧ s * b = t * a := by
    by_cases hA : A *ᵥ z = 0
    · have hB : B *ᵥ z ≠ 0 := by
        intro hB
        obtain ⟨α, hα⟩ := hreg
        exact hα (Matrix.exists_mulVec_eq_zero_iff.1
          ⟨z, hz, by simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hA, hB]⟩)
      have hs : s = 0 := by
        rw [hA, smul_zero, smul_eq_zero] at he
        exact he.resolve_right hB
      exact ⟨B *ᵥ z, hB, 0, 1, by simp [hA], by simp, by simp, by simp [hs]⟩
    · have hs : s ≠ 0 := by
        rintro rfl
        have ht : t ≠ 0 := hst.resolve_left (not_not.2 rfl)
        rw [zero_smul, eq_comm, smul_eq_zero] at he
        exact he.elim ht hA
      refine ⟨A *ᵥ z, hA, 1, t / s, by simp, ?_, by simp, by field_simp⟩
      rw [div_eq_inv_mul, mul_smul, ← he, smul_smul, inv_mul_cancel₀ hs, one_smul]
  obtain ⟨w, hw0, a, b, hAz, hBz, hab, hsb⟩ := hw
  obtain ⟨U, hU, r, hr, hzr⟩ := exists_unitary_col (0 : Fin (n + 1)) hz
  obtain ⟨W, hW, ρ, hρ, hwρ⟩ := exists_unitary_col (0 : Fin (n + 1)) hw0
  have hUe : U *ᵥ Pi.single 0 1 = r⁻¹ • z := by
    rw [hzr, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have key : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ), M *ᵥ z = c • w →
      ∀ i, (star W * M * U) i 0 =
        r⁻¹ * c * ρ * (Pi.single (0 : Fin (n + 1)) (1 : ℂ) : Fin (n + 1) → ℂ) i := by
    intro M c hM i
    have hcol : (star W * M * U) *ᵥ Pi.single 0 1 =
        (r⁻¹ * c * ρ) • Pi.single (0 : Fin (n + 1)) (1 : ℂ) := by
      rw [← Matrix.mulVec_mulVec, hUe, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hM,
        hwρ, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mem_unitaryGroup_iff'.1 hW, Matrix.one_mulVec, smul_smul, smul_smul]
    have := congrFun hcol i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this, Pi.smul_apply, smul_eq_mul]
  refine ⟨star W, Unitary.star_mem hW, U, hU, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · rw [key A a hAz]; simp
  · rw [key B b hBz]; simp
  · rw [key A a hAz, key B b hBz, Pi.single_eq_same]
    linear_combination (r⁻¹ * ρ) * hsb
  · rw [key A a hAz, key B b hBz]
    simp only [Pi.single_eq_same, mul_one, ne_eq, mul_eq_zero, inv_eq_zero, hr, hρ, false_or,
      or_false]
    tauto

/-- Laplace expansion when the first column vanishes below the diagonal. -/
theorem det_of_col_zero {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h : ∀ i : Fin n, P i.succ 0 = 0) : P.det = P 0 0 * (P.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

/-! ### Block diagonal `diag(1, Q)` -/

/-- The block diagonal matrix `diag(1, Q)` of size `n + 1`. -/
def blockOne {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of (Fin.cons (Fin.cons 1 0 : Fin (n + 1) → ℂ) fun i => Fin.cons 0 (Q i))

theorem blockOne_mul_zero {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    (blockOne Q * M) 0 j = M 0 j := by
  simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockOne_mul_succ {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin n) (j : Fin (n + 1)) :
    (blockOne Q * M) i.succ j = ∑ k, Q i k * M k.succ j := by
  simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mul_blockOne_zero {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    (M * blockOne Z) i 0 = M i 0 := by
  simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem mul_blockOne_succ {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (j : Fin n) :
    (M * blockOne Z) i j.succ = ∑ k, M i k.succ * Z k j := by
  simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockOne_mul_blockOne {n : ℕ} (P R : Matrix (Fin n) (Fin n) ℂ) :
    blockOne P * blockOne R = blockOne (P * R) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]

theorem star_blockOne {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) :
    star (blockOne P) = blockOne (star P) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blockOne, Matrix.star_apply]

theorem blockOne_one {n : ℕ} : blockOne (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blockOne, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem blockOne_mem {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    blockOne P ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_blockOne, blockOne_mul_blockOne,
    Matrix.mem_unitaryGroup_iff.1 hP, blockOne_one]

/-- Entries of `diag(1, Q) · M · diag(1, Z)` when the first column of `M` vanishes below the
diagonal. -/
theorem assemble_apply {n : ℕ} (Q Z : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hM : ∀ i : Fin n, M i.succ 0 = 0) :
    (blockOne Q * M * blockOne Z) 0 0 = M 0 0 ∧
      (∀ i : Fin n, (blockOne Q * M * blockOne Z) i.succ 0 = 0) ∧
      ∀ i j : Fin n, (blockOne Q * M * blockOne Z) i.succ j.succ =
        (Q * M.submatrix Fin.succ Fin.succ * Z) i j := by
  refine ⟨by rw [mul_blockOne_zero, blockOne_mul_zero], fun i => ?_, fun i j => ?_⟩
  · rw [mul_blockOne_zero, blockOne_mul_succ]
    simp [hM]
  · rw [mul_blockOne_succ]
    simp only [blockOne_mul_succ]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]

theorem assemble_upper {n : ℕ} (Q Z : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hM : ∀ i : Fin n, M i.succ 0 = 0)
    (h : (Q * M.submatrix Fin.succ Fin.succ * Z).IsUpperTriangular) :
    (blockOne Q * M * blockOne Z).IsUpperTriangular := by
  obtain ⟨-, h1, h2⟩ := assemble_apply Q Z M hM
  intro i j hij
  induction i using Fin.cases with
  | zero => exact absurd hij (Fin.not_lt_zero _)
  | succ i =>
    induction j using Fin.cases with
    | zero => exact h1 i
    | succ j => rw [h2]; exact h (Fin.succ_lt_succ_iff.1 hij)

/-- Two nonzero pairs with `sb = ta` are proportional. -/
theorem proportional_of_cross {s t a b : ℂ} (hst : s ≠ 0 ∨ t ≠ 0) (hab : a ≠ 0 ∨ b ≠ 0)
    (h : s * b = t * a) : ∃ c : ℂ, c ≠ 0 ∧ a = c * s ∧ b = c * t := by
  by_cases hs : s = 0
  · have ht : t ≠ 0 := hst.resolve_left (not_not.2 hs)
    have ha : a = 0 := by
      rw [hs, zero_mul, eq_comm, mul_eq_zero] at h
      exact h.resolve_left ht
    have hb : b ≠ 0 := hab.resolve_left (not_not.2 ha)
    exact ⟨b / t, div_ne_zero hb ht, by simp [ha, hs], by field_simp⟩
  · have ha : a ≠ 0 := by
      intro ha
      rw [ha, mul_zero, mul_eq_zero] at h
      exact hab.elim (fun h' => h' ha) fun hb => (h.resolve_left hs) ▸ hb <| rfl
    refine ⟨a / s, div_ne_zero ha hs, by field_simp, ?_⟩
    field_simp
    linear_combination h

/-! ### Theorem 1.4.4 -/

/-- A predicate on pairs `(s, t)` that depends only on the ratio, i.e. on the generalized
eigenvalue `t/s` (possibly infinite). -/
def ScaleInvariant (P : ℂ → ℂ → Prop) : Prop :=
  ∀ c s t : ℂ, c ≠ 0 → (P (c * s) (c * t) ↔ P s t)

/-- Existence of an ordered QZ form, by induction on the size. -/
theorem exists_qz_ordered (P : ℂ → ℂ → Prop) (hP : ScaleInvariant P) :
    ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), IsRegular A B →
      ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ Z ∈ Matrix.unitaryGroup (Fin n) ℂ,
        (Q * A * Z).IsUpperTriangular ∧ (Q * B * Z).IsUpperTriangular ∧
        ∃ m : ℕ, ∀ i : Fin n, i.val < m ↔ P ((Q * A * Z) i i) ((Q * B * Z) i i) := by
  intro n
  induction n with
  | zero =>
    intro A B _
    exact ⟨1, one_mem _, 1, one_mem _, fun i => i.elim0, fun i => i.elim0, 0, fun i => i.elim0⟩
  | succ n ih =>
    intro A B hreg
    -- an eigenpair satisfying `P` if there is one
    have hchoice : ∃ z : Fin (n + 1) → ℂ, z ≠ 0 ∧ ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧
        s • (B *ᵥ z) = t • (A *ᵥ z) ∧
        ((∃ s' t' : ℂ, (s' ≠ 0 ∨ t' ≠ 0) ∧ (s' • B - t' • A).det = 0 ∧ P s' t') → P s t) := by
      by_cases hex : ∃ s' t' : ℂ, (s' ≠ 0 ∨ t' ≠ 0) ∧ (s' • B - t' • A).det = 0 ∧ P s' t'
      · obtain ⟨s, t, hst, hdet, hPst⟩ := hex
        obtain ⟨z, hz, hz0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
        refine ⟨z, hz, s, t, hst, ?_, fun _ => hPst⟩
        rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hz0
      · obtain ⟨z, hz, s, t, hst, he⟩ := exists_eigenPair hreg
        exact ⟨z, hz, s, t, hst, he, fun h => absurd h hex⟩
    obtain ⟨z, hz, s, t, hst, he, hPst⟩ := hchoice
    obtain ⟨V, hV, W, hW, hMc, hNc, hprop, hnz⟩ := deflate hreg hz hst he
    set M := V * A * W with hMdef
    set N := V * B * W with hNdef
    set A' := M.submatrix Fin.succ Fin.succ
    set B' := N.submatrix Fin.succ Fin.succ
    have hdefl : ∀ a b : ℂ,
        (a • N - b • M).det = (a * N 0 0 - b * M 0 0) * (a • B' - b • A').det := by
      intro a b
      rw [det_of_col_zero _ (fun i => by simp [hMc i, hNc i])]
      rfl
    have hreg' : IsRegular A' B' := by
      obtain ⟨α, hα⟩ := hreg
      refine ⟨α, fun h0 => hα ?_⟩
      have h1 : (α • M - N).det = (α * M 0 0 - N 0 0) * (α • A' - B').det := by
        rw [det_of_col_zero _ (fun i => by simp [hMc i, hNc i])]
        rfl
      have h2 := det_conj_lincomb V W A B α 1
      rw [one_smul, one_smul, ← hMdef, ← hNdef, h1, h0, mul_zero] at h2
      simpa [det_ne_zero_of_unitary hV, det_ne_zero_of_unitary hW] using h2.symm
    obtain ⟨Q', hQ', Z', hZ', hS', hT', m', hm'⟩ := ih A' B' hreg'
    have hS := assemble_apply Q' Z' M hMc
    have hT := assemble_apply Q' Z' N hNc
    have hassoc : ∀ X, blockOne Q' * V * X * (W * blockOne Z') =
        blockOne Q' * (V * X * W) * blockOne Z' := fun X => by simp only [Matrix.mul_assoc]
    refine ⟨blockOne Q' * V, mul_mem (blockOne_mem hQ') hV, W * blockOne Z',
      mul_mem hW (blockOne_mem hZ'), ?_⟩
    rw [hassoc A, hassoc B, ← hMdef, ← hNdef]
    refine ⟨assemble_upper Q' Z' M hMc hS', assemble_upper Q' Z' N hNc hT', ?_⟩
    by_cases hp : P (M 0 0) (N 0 0)
    · refine ⟨m' + 1, fun i => ?_⟩
      induction i using Fin.cases with
      | zero => rw [hS.1, hT.1]; exact iff_of_true (by simp) hp
      | succ i => rw [Fin.val_succ, hS.2.2, hT.2.2, ← hm' i]; omega
    · refine ⟨0, fun i => ?_⟩
      simp only [Nat.not_lt_zero, false_iff]
      induction i using Fin.cases with
      | zero => rw [hS.1, hT.1]; exact hp
      | succ i =>
        rw [hS.2.2, hT.2.2]
        intro hPi
        apply hp
        set σ := (Q' * A' * Z') i i with hσ
        set τ := (Q' * B' * Z') i i with hτ
        have hne : σ ≠ 0 ∨ τ ≠ 0 := diag_ne_zero_of_regular hreg' hQ' hZ' hS' hT' i
        have hdet' : (σ • B' - τ • A').det = 0 := by
          have h1 := det_conj_lincomb Q' Z' B' A' σ τ
          rw [det_upper_lincomb hS' hT',
            Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hσ, ← hτ]; ring)] at h1
          simpa [det_ne_zero_of_unitary hQ', det_ne_zero_of_unitary hZ'] using h1.symm
        have hdetMN : (σ • N - τ • M).det = 0 := by rw [hdefl, hdet', mul_zero]
        have hdetAB : (σ • B - τ • A).det = 0 := by
          have h1 := det_conj_lincomb V W B A σ τ
          rw [← hMdef, ← hNdef, hdetMN] at h1
          simpa [det_ne_zero_of_unitary hV, det_ne_zero_of_unitary hW] using h1.symm
        obtain ⟨c, hc, hM0, hN0⟩ := proportional_of_cross hst hnz hprop
        rw [hM0, hN0, hP c s t hc]
        exact hPst ⟨σ, τ, hne, hdetAB, hPi⟩

/-- **Theorem 1.4.4** (complex generalized Schur form, Miao, pp. 24–25). Let `(A, B)` be regular
(Assumption 1.4.1). Then there are unitary `Q`, `Z` such that (1) `S = QAZ` and (2) `T = QBZ`
are upper triangular, (3) `sᵢᵢ` and `tᵢᵢ` are never both zero, (4)
`λ(A, B) = {tᵢᵢ/sᵢᵢ : sᵢᵢ ≠ 0}`, and (5, in the form proved here) for any prescribed
scale-invariant property `P` of the pairs `(sᵢᵢ, tᵢᵢ)`, the pairs with `P` come first. -/
theorem theorem_1_4_4 {n : ℕ} (P : ℂ → ℂ → Prop) (hP : ScaleInvariant P)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hreg : IsRegular A B) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ Z ∈ Matrix.unitaryGroup (Fin n) ℂ,
      (Q * A * Z).IsUpperTriangular ∧ (Q * B * Z).IsUpperTriangular ∧
      (∀ i, (Q * A * Z) i i ≠ 0 ∨ (Q * B * Z) i i ≠ 0) ∧
      genEigenvalues A B =
        {lam | ∃ i, (Q * A * Z) i i ≠ 0 ∧ lam = (Q * B * Z) i i / (Q * A * Z) i i} ∧
      ∃ m : ℕ, ∀ i : Fin n, i.val < m ↔ P ((Q * A * Z) i i) ((Q * B * Z) i i) := by
  obtain ⟨Q, hQ, Z, hZ, hS, hT, hm⟩ := exists_qz_ordered P hP n A B hreg
  exact ⟨Q, hQ, Z, hZ, hS, hT, diag_ne_zero_of_regular hreg hQ hZ hS hT,
    genEigenvalues_eq_diag hreg hQ hZ hS hT, hm⟩

/-- The stability predicate `|t| < |s|` on diagonal pairs (a stable generalized eigenvalue
`t/s`; a pair with `s = 0` is an infinite, unstable, eigenvalue) is scale invariant. -/
theorem scaleInvariant_stable : ScaleInvariant fun s t => ‖t‖ < ‖s‖ := by
  intro c s t hc
  simp only [norm_mul]
  exact mul_lt_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- **Theorem 1.4.4** with the ordering used in Theorem 1.4.5 (Miao, p. 25): the stable
generalized eigenvalues (`|tᵢᵢ| < |sᵢᵢ|`) come first. -/
theorem theorem_1_4_4_stable {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hreg : IsRegular A B) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ Z ∈ Matrix.unitaryGroup (Fin n) ℂ,
      (Q * A * Z).IsUpperTriangular ∧ (Q * B * Z).IsUpperTriangular ∧
      (∀ i, (Q * A * Z) i i ≠ 0 ∨ (Q * B * Z) i i ≠ 0) ∧
      genEigenvalues A B =
        {lam | ∃ i, (Q * A * Z) i i ≠ 0 ∧ lam = (Q * B * Z) i i / (Q * A * Z) i i} ∧
      ∃ m : ℕ, ∀ i : Fin n, i.val < m ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖ :=
  theorem_1_4_4 _ scaleInvariant_stable A B hreg

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Singular systems: Klein's method

Miao, §1.4.2, pp. 24–27: the system `Ax_{t+1} = Bx_t + Cz_t` (1.20) with `A` possibly singular,
solved through the ordered QZ form `S = QAZ`, `T = QBZ` of `QZ.lean`.

**Representation.** `x_t ∈ ℂ^{n_k + n_y}` is indexed by `Fin (nk + ny)`; the predetermined block
`k_t` is the coordinates `Fin.castAdd ny i` (`i < n_k`) and `y_t` the coordinates
`Fin.natAdd nk j`. The blocks `S₁₁, S₁₂, S₂₂, …, Z₁₁, Z₁₂` are `Matrix.submatrix` along these
embeddings, and `s_t`, `u_t` are `x*_t ∘ Fin.castAdd ny`, `x*_t ∘ Fin.natAdd nk` with
`x*_t = Zᴴx_t`. Conditions (i) `n_s = n_k` and the stable-first ordering are the one hypothesis
`i < n_k ↔ |tᵢᵢ| < |sᵢᵢ|`.

* `theorem_1_4_5` (Klein): under (i)–(iii), for every `k₀` and stable `z` there is a unique stable
  solution with initial predetermined block `k₀`. The proof follows the book: (1.36)
  (`eq_1_36`), the forward solution for `u_t` (`eq_1_37`, `fwdSum`), the backward recursion
  (1.38) (`eq_1_38`), `s₀ = Z₁₁⁻¹(k₀ − Z₁₂u₀)` (`eq_s0`) and (1.39)–(1.40) (`eq_1_39_40`);
  uniqueness because `T₂₂⁻¹S₂₂` has norm-summable powers, so a bounded `u` is the forward sum.
  `S₁₁⁻¹T₁₁` and `T₂₂⁻¹S₂₂` are upper triangular with diagonal entries of modulus `< 1`
  (`summable_Ms`, `summable_Mu`).
* `theorem_1_4_5_real`: for real `A, B, C, z, k₀` the unique stable solution is real.
* `corollary_1_4_1_singular` (p. 27, "a corollary similar to Corollary 1.4.1"): `A − B` is
  invertible (1 is not a generalized eigenvalue) and every stable solution tends to
  `x̄ = (A − B)⁻¹Cz̄` when `z` is eventually constant.
* `remark_augmented`, `remark_u_eq_zero`: the augmented system for `(z_t, x_t)` (p. 27), whose
  stable solutions have `u_t = 0`.
* The Cagan example (p. 24): `example_cagan_iff`, `example_cagan_det` (`A` singular),
  `example_cagan_regular`, `example_cagan_genEigenvalues` (`λ(A, B) = {1 + 1/α}` for `α ≠ 0`,
  empty for `α = 0`).

**Corrections.**
* (1.37) is printed as `u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ Q₂Cz_{t+j}`; the correct forward solution is
  `u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ Q₂Cz_{t+j}` (`eq_1_37`); the printed one fails in general
  (`eq_1_37_printed_false`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

open scoped Matrix

/-! ### Bounded sequences under matrices -/

/-- `‖Mv‖ ≤ (∑ᵢⱼ |Mᵢⱼ|) ‖v‖` in the max norm, for rectangular `M`. -/
theorem norm_mulVec_le_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ)
    (v : κ → ℂ) : ‖M *ᵥ v‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ = ‖∑ j, M i j * v j‖ := rfl
    _ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j, ‖M i j‖) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
        (norm_nonneg _)

theorem isStableSeq_of_le {E : Type*} [SeminormedAddCommGroup E] {x : ℕ → E} {K : ℝ}
    (h : ∀ t, ‖x t‖ ≤ K) : IsStableSeq x :=
  ⟨max K 0 + 1, by positivity, fun t => (h t).trans_lt (by linarith [le_max_left K 0])⟩

theorem IsStableSeq.bound {E : Type*} [SeminormedAddCommGroup E] {x : ℕ → E}
    (h : IsStableSeq x) : ∃ K, 0 ≤ K ∧ ∀ t, ‖x t‖ ≤ K := by
  obtain ⟨M, hM, hx⟩ := h
  exact ⟨M, hM.le, fun t => (hx t).le⟩

/-- A stable sequence stays stable under a fixed matrix. -/
theorem IsStableSeq.mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] {x : ℕ → κ → ℂ}
    (h : IsStableSeq x) (M : Matrix ι κ ℂ) : IsStableSeq fun t => M *ᵥ x t := by
  obtain ⟨K, -, hK⟩ := h.bound
  exact isStableSeq_of_le fun t => (norm_mulVec_le_sum M (x t)).trans
    (mul_le_mul_of_nonneg_left (hK t) (by positivity))

/-! ### The forward solution and the backward recursion -/

/-- The forward sum `∑ⱼ Nʲ w_{t+j}`. -/
noncomputable def fwdSum {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (w : ℕ → Fin m → ℂ) (t : ℕ) :
    Fin m → ℂ :=
  ∑' j, (N ^ j) *ᵥ w (t + j)

theorem summable_fwd {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    (t : ℕ) : Summable fun j => (N ^ j) *ᵥ w (t + j) :=
  Summable.of_norm_bounded (hN.mul_right W) fun _ =>
    (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (hw _) (norm_nonneg _))

theorem norm_fwdSum_le {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    (t : ℕ) : ‖fwdSum N w t‖ ≤ (∑' j, ‖mclm (N ^ j)‖) * W := by
  have hb : ∀ j, ‖(N ^ j) *ᵥ w (t + j)‖ ≤ ‖mclm (N ^ j)‖ * W := fun j =>
    (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (hw _) (norm_nonneg _))
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded (hN.mul_right W).hasSum hb

/-- The forward sum solves `u_t = N u_{t+1} + w_t`. -/
theorem fwdSum_rec {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    (t : ℕ) : fwdSum N w t = N *ᵥ fwdSum N w (t + 1) + w t := by
  unfold fwdSum
  have hmap := (mclm N).map_tsum (summable_fwd hN hw (t + 1))
  simp only [mclm_apply] at hmap
  rw [(summable_fwd hN hw t).tsum_eq_zero_add, hmap]
  simp only [pow_zero, Matrix.one_mulVec, add_zero, Matrix.mulVec_mulVec]
  rw [add_comm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [← pow_succ', show t + (j + 1) = t + 1 + j by ring]

/-- Any bounded solution of `u_t = N u_{t+1} + w_t` is the forward sum, when the powers of `N`
are summable in norm. -/
theorem eq_fwdSum {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (hN : Summable fun j => ‖mclm (N ^ j)‖) {w : ℕ → Fin m → ℂ} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W)
    {u : ℕ → Fin m → ℂ} (hu : IsStableSeq u) (hrec : ∀ t, u t = N *ᵥ u (t + 1) + w t) (t : ℕ) :
    u t = fwdSum N w t := by
  have hiter : ∀ J, u t = (N ^ J) *ᵥ u (t + J) +
      ∑ j ∈ Finset.range J, (N ^ j) *ᵥ w (t + j) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [ih, hrec (t + J), Finset.sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_mulVec,
        ← pow_succ, show t + J + 1 = t + (J + 1) by ring]
      abel
  obtain ⟨U₀, -, hU₀⟩ := hu.bound
  have h1 : Tendsto (fun J => (N ^ J) *ᵥ u (t + J)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun J => (norm_mulVec_le _ _).trans
      (mul_le_mul_of_nonneg_left (hU₀ _) (norm_nonneg _))) ?_
    simpa using hN.tendsto_atTop_zero.mul_const U₀
  have h2 := (summable_fwd hN hw t).hasSum.tendsto_sum_nat
  have h3 := h1.add h2
  rw [zero_add] at h3
  exact tendsto_nhds_unique (tendsto_const_nhds.congr hiter) h3

/-- The backward recursion `s_{t+1} = M s_t + v_t` with bounded `v` and norm-summable powers of
`M` has bounded solutions. -/
theorem isStableSeq_of_rec {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : Summable fun j => ‖mclm (M ^ j)‖) {v s : ℕ → Fin m → ℂ} (hv : IsStableSeq v)
    (hrec : ∀ t, s (t + 1) = M *ᵥ s t + v t) : IsStableSeq s := by
  have hform : ∀ t, s t = (M ^ t) *ᵥ s 0 + ∑ j ∈ Finset.range t, (M ^ j) *ᵥ v (t - 1 - j) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hrec, ih, Finset.sum_range_succ', Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ',
        Matrix.mulVec_sum]
      simp only [Matrix.mulVec_mulVec, ← pow_succ', pow_zero, Matrix.one_mulVec]
      rw [add_assoc]
      congr 2
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega]
  obtain ⟨V, hV0, hV⟩ := hv.bound
  set σ := ∑' j, ‖mclm (M ^ j)‖
  have hσ : ∀ t, ‖mclm (M ^ t)‖ ≤ σ := fun t => hM.le_tsum t fun j _ => norm_nonneg _
  refine isStableSeq_of_le (K := σ * ‖s 0‖ + σ * V) fun t => ?_
  rw [hform t]
  refine (norm_add_le _ _).trans (add_le_add ((norm_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_right (hσ t) (norm_nonneg _))) ?_)
  calc ‖∑ j ∈ Finset.range t, (M ^ j) *ᵥ v (t - 1 - j)‖
      ≤ ∑ j ∈ Finset.range t, ‖mclm (M ^ j)‖ * V := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => (norm_mulVec_le _ _).trans
          (mul_le_mul_of_nonneg_left (hV _) (norm_nonneg _)))
    _ = (∑ j ∈ Finset.range t, ‖mclm (M ^ j)‖) * V := by rw [Finset.sum_mul]
    _ ≤ σ * V := mul_le_mul_of_nonneg_right
        (hM.sum_le_tsum _ fun j _ => norm_nonneg _) hV0

theorem IsStableSeq.add {E : Type*} [SeminormedAddCommGroup E] {x y : ℕ → E}
    (hx : IsStableSeq x) (hy : IsStableSeq y) : IsStableSeq fun t => x t + y t := by
  obtain ⟨K, -, hK⟩ := hx.bound
  obtain ⟨L, -, hL⟩ := hy.bound
  exact isStableSeq_of_le fun t => (norm_add_le _ _).trans (add_le_add (hK t) (hL t))

theorem IsStableSeq.sub {E : Type*} [SeminormedAddCommGroup E] {x y : ℕ → E}
    (hx : IsStableSeq x) (hy : IsStableSeq y) : IsStableSeq fun t => x t - y t := by
  obtain ⟨K, -, hK⟩ := hx.bound
  obtain ⟨L, -, hL⟩ := hy.bound
  exact isStableSeq_of_le fun t => (norm_sub_le _ _).trans (add_le_add (hK t) (hL t))

theorem IsStableSeq.shift {E : Type*} [Norm E] {x : ℕ → E} (hx : IsStableSeq x) (k : ℕ) :
    IsStableSeq fun t => x (t + k) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t => h _⟩

theorem norm_comp_le {m p : ℕ} (v : Fin p → ℂ) (f : Fin m → Fin p) : ‖v ∘ f‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm v (f i)

theorem IsStableSeq.comp {m p : ℕ} {x : ℕ → Fin p → ℂ} (hx : IsStableSeq x) (f : Fin m → Fin p) :
    IsStableSeq fun t => x t ∘ f := by
  obtain ⟨K, -, hK⟩ := hx.bound
  exact isStableSeq_of_le fun t => (norm_comp_le _ f).trans (hK t)

theorem isStableSeq_append {a b : ℕ} {s : ℕ → Fin a → ℂ} {u : ℕ → Fin b → ℂ}
    (hs : IsStableSeq s) (hu : IsStableSeq u) : IsStableSeq fun t => Fin.append (s t) (u t) := by
  obtain ⟨K, hK0, hK⟩ := hs.bound
  obtain ⟨L, hL0, hL⟩ := hu.bound
  refine isStableSeq_of_le (K := K + L) fun t => (pi_norm_le_iff_of_nonneg (by positivity)).2
    fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    exact (norm_le_pi_norm _ i).trans ((hK t).trans (by linarith))
  · rw [Fin.append_right]
    exact (norm_le_pi_norm _ i).trans ((hL t).trans (by linarith))

/-! ### Block form (1.36) -/

theorem upper_castAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) : (M.submatrix (Fin.castAdd b) (Fin.castAdd b)).IsUpperTriangular :=
  fun _ _ h => hM (Fin.lt_def.2 (Fin.lt_def.1 h))

theorem upper_natAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) : (M.submatrix (Fin.natAdd a) (Fin.natAdd a)).IsUpperTriangular :=
  fun _ _ h => hM ((Fin.natAdd_lt_natAdd_iff a).2 h)

theorem mulVec_castAdd {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ)
    (v : Fin (a + b) → ℂ) (i : Fin a) :
    (M *ᵥ v) (Fin.castAdd b i) =
      (M.submatrix (Fin.castAdd b) (Fin.castAdd b) *ᵥ (v ∘ Fin.castAdd b)) i +
      (M.submatrix (Fin.castAdd b) (Fin.natAdd a) *ᵥ (v ∘ Fin.natAdd a)) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.submatrix_apply,
    Function.comp_apply]

theorem mulVec_natAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) (v : Fin (a + b) → ℂ) (i : Fin b) :
    (M *ᵥ v) (Fin.natAdd a i) =
      (M.submatrix (Fin.natAdd a) (Fin.natAdd a) *ᵥ (v ∘ Fin.natAdd a)) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.submatrix_apply,
    Function.comp_apply]
  rw [Finset.sum_eq_zero fun j _ => by
    rw [hM (Fin.lt_def.2 (by simp only [id, Fin.val_castAdd, Fin.val_natAdd]; omega)),
      zero_mul], zero_add]

/-- Miao, (1.36), p. 26: with `S`, `T` upper triangular, `Sx*_{t+1} = Tx*_t + c_t` splits into
`S₁₁s_{t+1} + S₁₂u_{t+1} = T₁₁s_t + T₁₂u_t + c¹_t` and `S₂₂u_{t+1} = T₂₂u_t + c²_t`, where `s`
(resp. `u`) is the first `a` (resp. last `b`) coordinates. -/
theorem eq_1_36 {a b : ℕ} {S T : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) (y y' c : Fin (a + b) → ℂ) :
    S *ᵥ y' = T *ᵥ y + c ↔
      (S.submatrix (Fin.castAdd b) (Fin.castAdd b) *ᵥ (y' ∘ Fin.castAdd b) +
          S.submatrix (Fin.castAdd b) (Fin.natAdd a) *ᵥ (y' ∘ Fin.natAdd a) =
        T.submatrix (Fin.castAdd b) (Fin.castAdd b) *ᵥ (y ∘ Fin.castAdd b) +
          T.submatrix (Fin.castAdd b) (Fin.natAdd a) *ᵥ (y ∘ Fin.natAdd a) + c ∘ Fin.castAdd b) ∧
      S.submatrix (Fin.natAdd a) (Fin.natAdd a) *ᵥ (y' ∘ Fin.natAdd a) =
        T.submatrix (Fin.natAdd a) (Fin.natAdd a) *ᵥ (y ∘ Fin.natAdd a) + c ∘ Fin.natAdd a := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have := congrFun h (Fin.castAdd b i)
      simp only [Pi.add_apply, mulVec_castAdd] at this
      simp only [Pi.add_apply, Function.comp_apply, this]
    · have := congrFun h (Fin.natAdd a i)
      simp only [Pi.add_apply, mulVec_natAdd hS, mulVec_natAdd hT] at this
      simp only [Pi.add_apply, Function.comp_apply, this]
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have := congrFun h1 i
      simp only [Pi.add_apply, Function.comp_apply] at this
      simp only [Pi.add_apply, mulVec_castAdd, this]
    · have := congrFun h2 i
      simp only [Pi.add_apply, Function.comp_apply] at this
      simp only [Pi.add_apply, mulVec_natAdd hS, mulVec_natAdd hT, this]

/-- Solving the second block of (1.36) for `u_t` (Miao, p. 26): with `T₂₂` invertible,
`S₂₂u' = T₂₂u + c` iff `u = T₂₂⁻¹S₂₂u' − T₂₂⁻¹c`. -/
theorem solve_fwd {m : ℕ} {S22 T22 : Matrix (Fin m) (Fin m) ℂ} (h : T22.det ≠ 0)
    (u u' c : Fin m → ℂ) :
    S22 *ᵥ u' = T22 *ᵥ u + c ↔ u = (T22⁻¹ * S22) *ᵥ u' + -(T22⁻¹ *ᵥ c) := by
  have h1 : T22⁻¹ * T22 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)
  have h2 : T22 * T22⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)
  constructor
  · intro e
    rw [← Matrix.mulVec_mulVec, e, Matrix.mulVec_add, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec]
    abel
  · intro e
    rw [e, Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      Matrix.mulVec_neg, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    abel

/-- Miao, (1.38), p. 26: solving the first block of (1.36) for `s_{t+1}`:
`s_{t+1} = S₁₁⁻¹T₁₁s_t + S₁₁⁻¹T₁₂u_t − S₁₁⁻¹S₁₂u_{t+1} + S₁₁⁻¹c¹_t`. -/
theorem eq_1_38 {m p : ℕ} {S11 T11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 : Matrix (Fin m) (Fin p) ℂ} (h : S11.det ≠ 0) (s s' c : Fin m → ℂ)
    (u u' : Fin p → ℂ) :
    S11 *ᵥ s' + S12 *ᵥ u' = T11 *ᵥ s + T12 *ᵥ u + c ↔
      s' = (S11⁻¹ * T11) *ᵥ s + S11⁻¹ *ᵥ (T12 *ᵥ u - S12 *ᵥ u' + c) := by
  have h1 : S11⁻¹ * S11 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)
  have h2 : S11 * S11⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)
  constructor
  · intro e
    have e' : S11 *ᵥ s' = T11 *ᵥ s + (T12 *ᵥ u - S12 *ᵥ u' + c) := by
      rw [← sub_eq_of_eq_add' e.symm]
      abel
    calc s' = S11⁻¹ *ᵥ (S11 *ᵥ s') := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      _ = _ := by rw [e', Matrix.mulVec_add, Matrix.mulVec_mulVec]
  · intro e
    rw [e, Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    abel

/-! ### The blocks of an ordered QZ form -/

/-- Miao, p. 26: `S₁₁` is invertible, since its diagonal entries are the `sᵢᵢ` of the stable
pairs, `|tᵢᵢ| < |sᵢᵢ|`. -/
theorem det_S11_ne_zero {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖) :
    (S.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular (upper_castAdd hS)]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have h := (hord (Fin.castAdd ny i)).1 i.2
  rw [Matrix.submatrix_apply]
  exact norm_pos_iff.1 ((norm_nonneg _).trans_lt h)

/-- Miao, p. 26: `T₂₂` is invertible, since its diagonal entries are the `tᵢᵢ` of the unstable
pairs, `|tᵢᵢ| > |sᵢᵢ|` (no pair on the unit circle). -/
theorem det_T22_ne_zero {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hT : T.IsUpperTriangular) (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) :
    (T.submatrix (Fin.natAdd nk) (Fin.natAdd nk)).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular (upper_natAdd hT)]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have h1 : ¬ ‖T (Fin.natAdd nk i) (Fin.natAdd nk i)‖ < ‖S (Fin.natAdd nk i) (Fin.natAdd nk i)‖ :=
    fun h => by have := (hord _).2 h; simp at this
  have h2 := lt_of_le_of_ne (not_lt.1 h1) (hdiag _).symm
  rw [Matrix.submatrix_apply]
  exact norm_pos_iff.1 ((norm_nonneg _).trans_lt h2)

/-- `S₁₁⁻¹T₁₁` is upper triangular with diagonal entries `tᵢᵢ/sᵢᵢ` of modulus less than one, so
the norms of its powers are summable. -/
theorem summable_Ms {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖) :
    Summable fun j => ‖mclm (((S.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
      T.submatrix (Fin.castAdd ny) (Fin.castAdd ny)) ^ j)‖ := by
  have hdet := det_S11_ne_zero hS hord
  have hinv := upper_inv (upper_castAdd hS) hdet
  refine summable_norm_pow_of_triangular _ (hinv.mul (upper_castAdd hT)) fun i => ?_
  rw [diag_mul_of_upper hinv (upper_castAdd hT), diag_inv_of_upper (upper_castAdd hS) hdet]
  simp only [Matrix.submatrix_apply, norm_mul, norm_inv]
  have h := (hord (Fin.castAdd ny i)).1 i.2
  have hpos : 0 < ‖S (Fin.castAdd ny i) (Fin.castAdd ny i)‖ := (norm_nonneg _).trans_lt h
  rw [inv_mul_lt_iff₀ hpos, mul_one]
  exact h

/-- `T₂₂⁻¹S₂₂` is upper triangular with diagonal entries `sᵢᵢ/tᵢᵢ` of modulus less than one. -/
theorem summable_Mu {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) :
    Summable fun j => ‖mclm (((T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
      S.submatrix (Fin.natAdd nk) (Fin.natAdd nk)) ^ j)‖ := by
  have hdet := det_T22_ne_zero hT hord hdiag
  have hinv := upper_inv (upper_natAdd hT) hdet
  refine summable_norm_pow_of_triangular _ (hinv.mul (upper_natAdd hS)) fun i => ?_
  rw [diag_mul_of_upper hinv (upper_natAdd hS), diag_inv_of_upper (upper_natAdd hT) hdet]
  simp only [Matrix.submatrix_apply, norm_mul, norm_inv]
  have h1 : ¬ ‖T (Fin.natAdd nk i) (Fin.natAdd nk i)‖ < ‖S (Fin.natAdd nk i) (Fin.natAdd nk i)‖ :=
    fun h => by have := (hord _).2 h; simp at this
  have h2 := lt_of_le_of_ne (not_lt.1 h1) (hdiag _).symm
  have hpos : 0 < ‖T (Fin.natAdd nk i) (Fin.natAdd nk i)‖ := (norm_nonneg _).trans_lt h2
  rw [inv_mul_lt_iff₀ hpos, mul_one]
  exact h2

/-! ### The transformed system -/

/-- Klein's construction in the transformed coordinates `x* = Zᴴx` (Miao, proof of Theorem 1.4.5,
pp. 25–26). With `S`, `T` upper triangular, the first `n_k` pairs stable and the rest unstable
(none on the unit circle), `Z₁₁` invertible and `c` stable, there is exactly one stable `y`
with `Sy_{t+1} = Ty_t + c_t` and `(Zy₀)ₖ = k₀`. -/
theorem klein_core {nk ny : ℕ} {S T Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    {c : ℕ → Fin (nk + ny) → ℂ} (hc : IsStableSeq c) (k₀ : Fin nk → ℂ) :
    ∃! y : ℕ → Fin (nk + ny) → ℂ, (∀ t, S *ᵥ y (t + 1) = T *ᵥ y t + c t) ∧ IsStableSeq y ∧
      ∀ i, (Z *ᵥ y 0) (Fin.castAdd ny i) = k₀ i := by
  set K := Fin.castAdd (n := nk) ny
  set U := Fin.natAdd (m := ny) nk
  have hS11 := det_S11_ne_zero hS hord
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hMs := summable_Ms hS hT hord
  have hN := summable_Mu hS hT hord hdiag
  set N := (T.submatrix U U)⁻¹ * S.submatrix U U
  set Ms := (S.submatrix K K)⁻¹ * T.submatrix K K
  -- Step 1: the forward solution for `u`
  set w : ℕ → Fin ny → ℂ := fun t => -((T.submatrix U U)⁻¹ *ᵥ (c t ∘ U))
  obtain ⟨W, -, hW⟩ := ((hc.comp U).mulVec (T.submatrix U U)⁻¹).bound
  have hW' : ∀ t, ‖w t‖ ≤ W := fun t => by
    simp only [w, norm_neg]
    exact hW t
  set uF := fwdSum N w
  have huF : ∀ t, uF t = N *ᵥ uF (t + 1) + w t := fwdSum_rec hN hW'
  have huFs : IsStableSeq uF := isStableSeq_of_le (norm_fwdSum_le hN hW')
  -- Step 2: the backward recursion for `s`
  set v : ℕ → Fin nk → ℂ := fun t => (S.submatrix K K)⁻¹ *ᵥ
    (T.submatrix K U *ᵥ uF t - S.submatrix K U *ᵥ uF (t + 1) + c t ∘ K)
  have hv : IsStableSeq v := ((((huFs.mulVec _).sub ((huFs.shift 1).mulVec _)).add
    (hc.comp K)).mulVec _)
  set s₀ := (Z.submatrix K K)⁻¹ *ᵥ (k₀ - Z.submatrix K U *ᵥ uF 0)
  set sF : ℕ → Fin nk → ℂ := fun t => Nat.rec s₀ (fun t st => Ms *ᵥ st + v t) t
  have hsF : ∀ t, sF (t + 1) = Ms *ᵥ sF t + v t := fun t => rfl
  have hsFs : IsStableSeq sF := isStableSeq_of_rec hMs hv hsF
  have hZ1 : Z.submatrix K K * (Z.submatrix K K)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hZ11)
  have hZ2 : (Z.submatrix K K)⁻¹ * Z.submatrix K K = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hZ11)
  have hK : ∀ (a : Fin nk → ℂ) (b : Fin ny → ℂ), Fin.append a b ∘ K = a :=
    fun a b => funext fun i => Fin.append_left a b i
  have hU : ∀ (a : Fin nk → ℂ) (b : Fin ny → ℂ), Fin.append a b ∘ U = b :=
    fun a b => funext fun i => Fin.append_right a b i
  refine ⟨fun t => Fin.append (sF t) (uF t), ⟨fun t => ?_, isStableSeq_append hsFs huFs,
    fun i => ?_⟩, ?_⟩
  · -- Step 3: the constructed sequence solves the system
    rw [eq_1_36 hS hT, hK, hK, hU, hU, eq_1_38 hS11, solve_fwd hT22]
    exact ⟨hsF t, huF t⟩
  · rw [mulVec_castAdd, hK, hU]
    change (Z.submatrix K K *ᵥ s₀ + Z.submatrix K U *ᵥ uF 0) i = k₀ i
    rw [Matrix.mulVec_mulVec, hZ1, Matrix.one_mulVec, sub_add_cancel]
  · rintro y ⟨hy, hys, hy0⟩
    have hblk := fun t => (eq_1_36 hS hT (y t) (y (t + 1)) (c t)).1 (hy t)
    -- `u` is the forward sum
    have hu : ∀ t, y t ∘ U = uF t :=
      eq_fwdSum hN hW' (hys.comp U) fun t => (solve_fwd hT22 _ _ _).1 (hblk t).2
    -- `s₀` is pinned down by `k₀`
    have hs0 : y 0 ∘ K = s₀ := by
      have h1 : Z.submatrix K K *ᵥ (y 0 ∘ K) + Z.submatrix K U *ᵥ (y 0 ∘ U) = k₀ :=
        funext fun i => by rw [← hy0 i, mulVec_castAdd]; rfl
      rw [hu 0] at h1
      calc y 0 ∘ K = (Z.submatrix K K)⁻¹ *ᵥ (Z.submatrix K K *ᵥ (y 0 ∘ K)) := by
            rw [Matrix.mulVec_mulVec, hZ2, Matrix.one_mulVec]
        _ = s₀ := by
            rw [show s₀ = (Z.submatrix K K)⁻¹ *ᵥ (k₀ - Z.submatrix K U *ᵥ uF 0) from rfl, ← h1,
              add_sub_cancel_right]
    have hs : ∀ t, y t ∘ K = sF t := by
      intro t
      induction t with
      | zero => exact hs0
      | succ t ih =>
        have := (eq_1_38 hS11 _ _ _ _ _).1 (hblk t).1
        rw [this, ih, hu, hu, hsF]
    funext t
    have hy' : y t = Fin.append (y t ∘ K) (y t ∘ U) := funext fun i =>
      Fin.addCases (fun i => (Fin.append_left (y t ∘ K) (y t ∘ U) i).symm)
        (fun i => (Fin.append_right (y t ∘ K) (y t ∘ U) i).symm) i
    rw [hy', hs, hu]

/-- Without forcing, a stable solution of the transformed system has `u_t = 0` and tends to zero
(the backward part is `s_t = (S₁₁⁻¹T₁₁)ᵗs₀`). -/
theorem klein_homog {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) {d : ℕ → Fin (nk + ny) → ℂ} (hd : IsStableSeq d)
    (h : ∀ t, S *ᵥ d (t + 1) = T *ᵥ d t) :
    (∀ t, d t ∘ Fin.natAdd nk = 0) ∧ Tendsto d atTop (𝓝 0) := by
  set K := Fin.castAdd (n := nk) ny
  set U := Fin.natAdd (m := ny) nk
  have hS11 := det_S11_ne_zero hS hord
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hMs := summable_Ms hS hT hord
  have hN := summable_Mu hS hT hord hdiag
  have hblk := fun t => (eq_1_36 hS hT (d t) (d (t + 1)) 0).1 (by rw [add_zero]; exact h t)
  have hu : ∀ t, d t ∘ U = 0 := by
    intro t
    have := eq_fwdSum hN (w := fun _ => 0) (W := 0) (fun _ => by simp) (hd.comp U)
      (fun t => by
        have := (solve_fwd hT22 _ _ _).1 (hblk t).2
        simpa using this) t
    rw [this]
    simp [fwdSum]
  set Ms := (S.submatrix K K)⁻¹ * T.submatrix K K
  have hs : ∀ t, d t ∘ K = (Ms ^ t) *ᵥ (d 0 ∘ K) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := (eq_1_38 hS11 _ _ _ _ _).1 (hblk t).1
      rw [this, hu, hu, ih, pow_succ', ← Matrix.mulVec_mulVec]
      simp [Ms, Matrix.mul_assoc]
      rfl
  refine ⟨hu, squeeze_zero_norm (a := fun t => ‖mclm (Ms ^ t)‖ * ‖d 0 ∘ K‖) (fun t => ?_) ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have h1 : d t (K i) = (d t ∘ K) i := rfl
      rw [h1, hs]
      exact (norm_le_pi_norm _ i).trans (norm_mulVec_le _ _)
    · have h1 : d t (U i) = (d t ∘ U) i := rfl
      rw [h1, hu]
      simp only [Pi.zero_apply, norm_zero]
      positivity
  · simpa using hMs.tendsto_atTop_zero.mul_const ‖d 0 ∘ K‖

/-- Miao, (1.37) as corrected: in a stable solution of the transformed system,
`u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ c²_{t+j}`. The book prints `−T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ c²_{t+j}`, which
is wrong unless `T₂₂⁻¹` commutes with `S₂₂` (`eq_1_37_printed_false`). -/
theorem eq_1_37 {nk ny : ℕ} {S T : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖) {c : ℕ → Fin (nk + ny) → ℂ} (hc : IsStableSeq c)
    {y : ℕ → Fin (nk + ny) → ℂ} (hy : IsStableSeq y) (h : ∀ t, S *ᵥ y (t + 1) = T *ᵥ y t + c t)
    (t : ℕ) :
    y t ∘ Fin.natAdd nk = -∑' j, (((T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
      S.submatrix (Fin.natAdd nk) (Fin.natAdd nk)) ^ j *
        (T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹) *ᵥ (c (t + j) ∘ Fin.natAdd nk) := by
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hN := summable_Mu hS hT hord hdiag
  obtain ⟨W, -, hW⟩ := ((hc.comp (Fin.natAdd nk)).mulVec
    (T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹).bound
  have hW' : ∀ t, ‖-((T.submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *ᵥ
      (c t ∘ Fin.natAdd nk))‖ ≤ W := fun t => by rw [norm_neg]; exact hW t
  rw [eq_fwdSum hN hW' (hy.comp _) (fun t => (solve_fwd hT22 _ _ _).1
    ((eq_1_36 hS hT _ _ _).1 (h t)).2) t, fwdSum, ← tsum_neg]
  simp only [Matrix.mulVec_neg, Matrix.mulVec_mulVec]

/-- Miao, (1.39)–(1.40), p. 26: with `x_t = Zx*_t`, `k_t = Z₁₁s_t + Z₁₂u_t` and
`y_t = Z₂₁s_t + Z₂₂u_t`. -/
theorem eq_1_39_40 {nk ny : ℕ} (Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ)
    (xs : Fin (nk + ny) → ℂ) :
    (Z *ᵥ xs) ∘ Fin.castAdd ny =
        Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *ᵥ (xs ∘ Fin.castAdd ny) +
          Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) *ᵥ (xs ∘ Fin.natAdd nk) ∧
      (Z *ᵥ xs) ∘ Fin.natAdd nk =
        Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny) *ᵥ (xs ∘ Fin.castAdd ny) +
          Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk) *ᵥ (xs ∘ Fin.natAdd nk) := by
  refine ⟨funext fun i => mulVec_castAdd Z xs i, funext fun i => ?_⟩
  simp only [Function.comp_apply, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
    Matrix.submatrix_apply]

/-! ### Theorem 1.4.5 -/

/-- The unitary change of variables `x* = Zᴴx` (Miao, p. 25): `x` solves (1.20) iff
`Sx*_{t+1} = Tx*_t + QCz_t` with `S = QAZ`, `T = QBZ`. -/
theorem isSolution_iff_transformed {n nz : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    {C : Matrix (Fin n) (Fin nz) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (z : ℕ → Fin nz → ℂ) (x : ℕ → Fin n → ℂ) :
    IsSolution A B C z x ↔ ∀ t, (Q * A * Z) *ᵥ (star Z *ᵥ x (t + 1)) =
      (Q * B * Z) *ᵥ (star Z *ᵥ x t) + Q *ᵥ (C *ᵥ z t) := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hQQ : star Q * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ),
      (Q * M * Z) *ᵥ (star Z *ᵥ v) = Q *ᵥ (M *ᵥ v) := fun M v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZZ, Matrix.mul_one,
      Matrix.mulVec_mulVec]
  simp only [IsSolution, key, ← Matrix.mulVec_add]
  refine forall_congr' fun t => ⟨fun h => by rw [h], fun h => ?_⟩
  have := congrArg (star Q *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hQQ, Matrix.one_mul,
    Matrix.one_mulVec] using this

/-- Condition (iii) of Theorem 1.4.5 on the diagonal of a QZ form: no generalized eigenvalue on
the unit circle gives `|tᵢᵢ| ≠ |sᵢᵢ|` for every `i`. -/
theorem diag_off_circle {n : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ} (hreg : IsRegular A B)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) (i : Fin n) :
    ‖(Q * B * Z) i i‖ ≠ ‖(Q * A * Z) i i‖ := by
  intro h
  by_cases hs : (Q * A * Z) i i = 0
  · rw [hs, norm_zero, norm_eq_zero] at h
    rcases diag_ne_zero_of_regular hreg hQ hZ hS hT i with h' | h'
    · exact h' hs
    · exact h' h
  · have hmem : (Q * B * Z) i i / (Q * A * Z) i i ∈ genEigenvalues A B := by
      rw [genEigenvalues_eq_diag hreg hQ hZ hS hT]
      exact ⟨i, hs, rfl⟩
    refine hcirc _ hmem ?_
    rw [norm_div, h, div_self (norm_ne_zero_iff.2 hs)]

/-- **Theorem 1.4.5** (Klein, Miao, p. 25). Let `(A, B)` be regular, with QZ form `S = QAZ`,
`T = QBZ` whose stable generalized eigenvalues come first, and partition `x_t = (k_t, y_t)` with
`k_t` the first `n_k` (predetermined) coordinates. Suppose (i) `n_s = n_k`, i.e. pair `i` is
stable iff `i < n_k` (`hord`, which also records the ordering); (ii) `Z₁₁` is invertible; (iii)
`(A, B)` has no generalized eigenvalue on the unit circle. Then for every `k₀` and every stable
`{z_t}`, (1.20) has a unique stable solution with initial predetermined block `k₀`. -/
theorem theorem_1_4_5 {nk ny nz : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ} (hreg : IsRegular A B)
    {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) (k₀ : Fin nk → ℂ)
    {z : ℕ → Fin nz → ℂ} (hz : IsStableSeq z) :
    ∃! x : ℕ → Fin (nk + ny) → ℂ,
      IsSolution A B C z x ∧ IsStableSeq x ∧ ∀ i, x 0 (Fin.castAdd ny i) = k₀ i := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hZ
  obtain ⟨y, ⟨hy1, hy2, hy3⟩, hyu⟩ := klein_core hS hT hord
    (diag_off_circle hreg hQ hZ hS hT hcirc) hZ11 ((hz.mulVec C).mulVec Q) k₀
  refine ⟨fun t => Z *ᵥ y t, ⟨(isSolution_iff_transformed hQ hZ z _).2 fun t => ?_,
    hy2.mulVec Z, hy3⟩, ?_⟩
  · simpa only [Matrix.mulVec_mulVec, hZZ', Matrix.one_mulVec] using hy1 t
  · rintro x ⟨hx1, hx2, hx3⟩
    have hback : ∀ t, Z *ᵥ (star Z *ᵥ x t) = x t := fun t => by
      rw [Matrix.mulVec_mulVec, hZZ, Matrix.one_mulVec]
    have := hyu (fun t => star Z *ᵥ x t) ⟨(isSolution_iff_transformed hQ hZ z x).1 hx1,
      hx2.mulVec _, fun i => by rw [hback]; exact hx3 i⟩
    funext t
    rw [← this, hback]

/-! ### Steady state (the analogue of Corollary 1.4.1) -/

/-- Under condition (iii) of Theorem 1.4.5, `1` is not a generalized eigenvalue, so `A − B` is
invertible and the steady state `x̄ = (A − B)⁻¹Cz̄` of (1.21) is defined. -/
theorem det_sub_ne_zero {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) : (A - B).det ≠ 0 := by
  intro h
  have h1 : IsGenEigenvalue A B 1 := by
    rw [isGenEigenvalue_iff_det, one_smul, ← neg_sub, Matrix.det_neg, h, mul_zero]
  exact hcirc 1 h1 (by simp)

/-- **Corollary 1.4.1 for singular systems** (Miao, p. 27, stated but not written out in the
book). Under the conditions of Theorem 1.4.5 and Assumption 1.4.2 (`z_t = z̄` eventually),
`A − B` is invertible and every stable solution of (1.20) converges to the steady state
`x̄ = (A − B)⁻¹Cz̄`. Condition (ii) (`Z₁₁` invertible) is not needed for the convergence. -/
theorem corollary_1_4_1_singular {nk ny nz : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ} (hreg : IsRegular A B)
    {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) {z : ℕ → Fin nz → ℂ} {zbar : Fin nz → ℂ}
    (hzc : EventuallyConst z zbar) {x : ℕ → Fin (nk + ny) → ℂ} (hx : IsSolution A B C z x)
    (hxs : IsStableSeq x) :
    (A - B).det ≠ 0 ∧ Tendsto x atTop (𝓝 ((A - B)⁻¹ *ᵥ (C *ᵥ zbar))) := by
  have hdet := det_sub_ne_zero hcirc
  refine ⟨hdet, ?_⟩
  set xbar := (A - B)⁻¹ *ᵥ (C *ᵥ zbar)
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hxbar : IsSolution A B C (fun _ => zbar) (fun _ => xbar) := fun _ => by
    have h1 : (A - B) *ᵥ xbar = C *ᵥ zbar := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
        Matrix.one_mulVec]
    rw [Matrix.sub_mulVec] at h1
    rw [← h1]
    abel
  obtain ⟨T₀, hT₀⟩ := hzc
  set d : ℕ → Fin (nk + ny) → ℂ := fun t => star Z *ᵥ (x (t + T₀) - xbar)
  have hd : IsStableSeq d :=
    ((hxs.shift T₀).sub (isStableSeq_of_le (x := fun _ => xbar) fun _ => le_rfl)).mulVec _
  have e2 := (isSolution_iff_transformed hQ hZ _ _).1 hxbar 0
  have hdeq : ∀ t, (Q * A * Z) *ᵥ d (t + 1) = (Q * B * Z) *ᵥ d t := by
    intro t
    have e1 := (isSolution_iff_transformed hQ hZ z x).1 hx (t + T₀)
    rw [hT₀ (t + T₀) (by omega)] at e1
    simp only [d, Matrix.mulVec_sub, show t + 1 + T₀ = t + T₀ + 1 by ring, e1, e2]
    abel
  obtain ⟨-, hlim⟩ := klein_homog hS hT hord (diag_off_circle hreg hQ hZ hS hT hcirc) hd hdeq
  have h3 : ∀ t, Z *ᵥ d t = x (t + T₀) - xbar := fun t => by
    simp only [d, Matrix.mulVec_mulVec, hZZ, Matrix.one_mulVec]
  have h4 : Tendsto (fun t => x (t + T₀) - xbar) atTop (𝓝 0) := by
    have h2 := ((mclm Z).continuous.tendsto 0).comp hlim
    simpa [Function.comp_def, mclm_apply, h3] using h2
  have h5 := h4.add_const xbar
  simp only [sub_add_cancel, zero_add] at h5
  exact (tendsto_add_atTop_iff_nat T₀).1 h5

/-! ### Real data -/

theorem map_ofReal_mulVec {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (v : κ → ℝ) :
    M.map Complex.ofRealHom *ᵥ (fun j => (v j : ℂ)) = fun i => ((M *ᵥ v) i : ℂ) :=
  funext fun i => (RingHom.map_mulVec Complex.ofRealHom M v i).symm

theorem norm_ofReal_vec {m : ℕ} (v : Fin m → ℝ) : ‖(fun i => (v i : ℂ))‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [Complex.norm_real]
    exact norm_le_pi_norm v i
  · rw [← Complex.norm_real]
    exact norm_le_pi_norm (fun i => (v i : ℂ)) i

/-- A real sequence solves the real system iff its complexification solves the complexified one. -/
theorem isSolution_ofReal_iff {n nz : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin n) (Fin nz) ℝ} (z : ℕ → Fin nz → ℝ) (x : ℕ → Fin n → ℝ) :
    IsSolution A B C z x ↔ IsSolution (A.map Complex.ofRealHom) (B.map Complex.ofRealHom)
      (C.map Complex.ofRealHom) (fun t i => (z t i : ℂ)) (fun t i => (x t i : ℂ)) := by
  simp only [IsSolution, map_ofReal_mulVec]
  refine forall_congr' fun t => ⟨fun h => by rw [h]; funext i; simp, fun h => funext fun i => ?_⟩
  have := congrFun h i
  simp only [Pi.add_apply] at this
  exact_mod_cast this

/-- **Theorem 1.4.5, real data** (Miao, p. 25, where `A`, `B`, `C`, `z`, `k₀` are real): the QZ
form is complex, but the unique stable solution is real, because its complex conjugate is
another stable solution with the same `k₀`. -/
theorem theorem_1_4_5_real {nk ny nz : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℝ}
    {C : Matrix (Fin (nk + ny)) (Fin nz) ℝ}
    (hreg : IsRegular (A.map Complex.ofRealHom) (B.map Complex.ofRealHom))
    {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A.map Complex.ofRealHom * Z).IsUpperTriangular)
    (hT : (Q * B.map Complex.ofRealHom * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔
      ‖(Q * B.map Complex.ofRealHom * Z) i i‖ < ‖(Q * A.map Complex.ofRealHom * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues (A.map Complex.ofRealHom) (B.map Complex.ofRealHom),
      ‖lam‖ ≠ 1) (k₀ : Fin nk → ℝ) {z : ℕ → Fin nz → ℝ} (hz : IsStableSeq z) :
    ∃! x : ℕ → Fin (nk + ny) → ℝ,
      IsSolution A B C z x ∧ IsStableSeq x ∧ ∀ i, x 0 (Fin.castAdd ny i) = k₀ i := by
  have hzc : IsStableSeq fun t i => (z t i : ℂ) := by
    obtain ⟨M, hM, h⟩ := hz
    exact ⟨M, hM, fun t => by rw [norm_ofReal_vec]; exact h t⟩
  obtain ⟨xc, ⟨h1, h2, h3⟩, hu⟩ := theorem_1_4_5 (C := C.map Complex.ofRealHom) hreg hQ hZ hS hT
    hord hZ11 hcirc (fun i => (k₀ i : ℂ)) hzc
  -- the conjugate is another stable solution
  have hconj : (fun t i => (starRingEnd ℂ) (xc t i)) = xc := by
    refine hu _ ⟨fun t => ?_, ?_, fun i => by simp [h3 i]⟩
    · have hmap : ∀ {κ : Type} [Fintype κ] (M : Matrix (Fin (nk + ny)) κ ℝ) (v : κ → ℂ),
          M.map Complex.ofRealHom *ᵥ (fun j => (starRingEnd ℂ) (v j)) =
            fun i => (starRingEnd ℂ) ((M.map Complex.ofRealHom *ᵥ v) i) := by
        intro κ _ M v
        funext i
        rw [RingHom.map_mulVec]
        congr 1
        ext a b
        simp
      have hz' : (fun j => (z t j : ℂ)) = fun j => (starRingEnd ℂ) ((z t j : ℂ)) :=
        funext fun j => (Complex.conj_ofReal _).symm
      change _ = _ + C.map Complex.ofRealHom *ᵥ (fun j => (z t j : ℂ))
      rw [hz', hmap, hmap, hmap, h1 t]
      funext i
      simp only [Pi.add_apply, map_add]
    · obtain ⟨M, hM, h⟩ := h2
      refine ⟨M, hM, fun t => ?_⟩
      have : ‖fun i => (starRingEnd ℂ) (xc t i)‖ = ‖xc t‖ := by
        refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
          ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
        · rw [Complex.norm_conj]
          exact norm_le_pi_norm (xc t) i
        · rw [← Complex.norm_conj]
          exact norm_le_pi_norm (fun i => (starRingEnd ℂ) (xc t i)) i
      rw [this]
      exact h t
  have hreal : ∀ t i, ((xc t i).re : ℂ) = xc t i := fun t i =>
    Complex.conj_eq_iff_re.1 (congrFun (congrFun hconj t) i)
  refine ⟨fun t i => (xc t i).re, ⟨?_, ?_, fun i => ?_⟩, ?_⟩
  · rw [isSolution_ofReal_iff]
    simpa only [hreal] using h1
  · obtain ⟨M, hM, h⟩ := h2
    exact ⟨M, hM, fun t => by
      rw [← norm_ofReal_vec]
      simpa only [hreal] using h t⟩
  · have := congrArg Complex.re (h3 i)
    simpa using this
  · rintro x ⟨hx1, hx2, hx3⟩
    have hxc : (fun t i => (x t i : ℂ)) = xc := hu _ ⟨(isSolution_ofReal_iff z x).1 hx1, by
      obtain ⟨M, hM, h⟩ := hx2
      exact ⟨M, hM, fun t => by rw [norm_ofReal_vec]; exact h t⟩,
      fun i => by simp [hx3 i]⟩
    funext t i
    have := congrArg Complex.re (congrFun (congrFun hxc t) i)
    simpa using this

/-- Miao, p. 26: in any solution with initial predetermined block `k₀`,
`s₀ = Z₁₁⁻¹(k₀ − Z₁₂u₀)`. -/
theorem eq_s0 {nk ny : ℕ} {Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0) (xs : Fin (nk + ny) → ℂ)
    (k₀ : Fin nk → ℂ) (h : (Z *ᵥ xs) ∘ Fin.castAdd ny = k₀) :
    xs ∘ Fin.castAdd ny = (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *ᵥ
      (k₀ - Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) *ᵥ (xs ∘ Fin.natAdd nk)) := by
  rw [← h, (eq_1_39_40 Z xs).1, add_sub_cancel_right, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hZ11), Matrix.one_mulVec]

/-! ### Remarks on p. 27 -/

/-- Miao, p. 27: with `z_{t+1} = Φz_t`, the system for `(z_t, x_t)` with matrices
`[[I, 0], [0, A]]` and `[[Φ, 0], [C, B]]` and no forcing is equivalent to (1.20) together with
the law of motion of `z`. -/
theorem remark_augmented {K : Type*} [CommRing K] {n nz : ℕ} (A B : Matrix (Fin n) (Fin n) K)
    (C : Matrix (Fin n) (Fin nz) K) (Φ : Matrix (Fin nz) (Fin nz) K) (z : ℕ → Fin nz → K)
    (x : ℕ → Fin n → K) :
    IsSolution (Matrix.fromBlocks 1 0 0 A) (Matrix.fromBlocks Φ 0 C B)
        (0 : Matrix (Fin nz ⊕ Fin n) (Fin 0) K) (fun _ => 0) (fun t => Sum.elim (z t) (x t)) ↔
      (∀ t, z (t + 1) = Φ *ᵥ z t) ∧ IsSolution A B C z x := by
  simp only [IsSolution, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add, Matrix.mulVec_zero]
  rw [← forall_and]
  refine forall_congr' fun t => ?_
  rw [Sum.elim_eq_iff, add_comm (C *ᵥ z t)]

/-- Miao, p. 27 ("we have `u_t = 0`"): without forcing (as in the augmented system), every
stable solution has `u_t = 0`, where `x*_t = Zᴴx_t = (s_t, u_t)`. -/
theorem remark_u_eq_zero {nk ny : ℕ} {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) {x : ℕ → Fin (nk + ny) → ℂ}
    (hx : ∀ t, A *ᵥ x (t + 1) = B *ᵥ x t) (hxs : IsStableSeq x) (t : ℕ) :
    (star Z *ᵥ x t) ∘ Fin.natAdd nk = 0 := by
  have hsol : IsSolution A B (0 : Matrix (Fin (nk + ny)) (Fin 0) ℂ) (fun _ => 0) x :=
    fun t => by rw [hx t, Matrix.zero_mulVec, add_zero]
  have h := (isSolution_iff_transformed hQ hZ _ x).1 hsol
  simp only [Matrix.mulVec_zero, add_zero] at h
  exact (klein_homog hS hT hord (diag_off_circle hreg hQ hZ hS hT hcirc) (hxs.mulVec _) h).1 t

/-! ### The printed form of (1.37) is wrong -/

/-- **Counterexample to (1.37) as printed** (Miao, p. 26). The book's
`u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ c²_{t+j}` need not solve `S₂₂u_{t+1} = T₂₂u_t + c²_t`: take
`S₂₂ = [[0, 1], [0, 0]]`, `T₂₂ = diag(1, 2)` (both pairs unstable: infinite eigenvalues) and
`c²_t = e₂` at `t = 1`, zero otherwise. The correct formula is `eq_1_37`. -/
theorem eq_1_37_printed_false :
    ∃ (S₂₂ T₂₂ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℕ → Fin 2 → ℂ),
      S₂₂.IsUpperTriangular ∧ T₂₂.IsUpperTriangular ∧ (∀ i, ‖S₂₂ i i‖ < ‖T₂₂ i i‖) ∧
      IsStableSeq c ∧
      ¬ ∀ t, S₂₂ *ᵥ (-(T₂₂⁻¹ *ᵥ ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (t + 1 + j))) =
        T₂₂ *ᵥ (-(T₂₂⁻¹ *ᵥ ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (t + j))) + c t := by
  set S₂₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  set T₂₂ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 2]
  set c : ℕ → Fin 2 → ℂ := fun t => if t = 1 then ![0, 1] else 0
  have hTinv : T₂₂⁻¹ = !![1, 0; 0, 1 / 2] := Matrix.inv_eq_right_inv (by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [T₂₂, Matrix.mul_apply, Fin.sum_univ_two])
  have hN : T₂₂⁻¹ * S₂₂ = !![0, 1; 0, 0] := by
    rw [hTinv]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [S₂₂, Matrix.mul_apply, Fin.sum_univ_two]
  have hc1 : ∀ j, j ≠ 1 → c j = 0 := fun j hj => by simp [c, hj]
  have hsum0 : ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (0 + j) = ![1, 0] := by
    rw [tsum_eq_single 1 fun j hj => by rw [zero_add, hc1 j hj, Matrix.mulVec_zero]]
    rw [hN]
    ext i; fin_cases i <;> simp [c, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hsum1 : ∑' j, ((T₂₂⁻¹ * S₂₂) ^ j) *ᵥ c (0 + 1 + j) = ![0, 1] := by
    rw [tsum_eq_single 0 fun j hj => by rw [hc1 _ (by omega), Matrix.mulVec_zero]]
    simp [c]
  refine ⟨S₂₂, T₂₂, c, ?_, ?_, ?_, ?_, fun h => ?_⟩
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [S₂₂]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [T₂₂]
  · intro i; fin_cases i <;> norm_num [S₂₂, T₂₂]
  · refine isStableSeq_of_le (K := 1) fun t => ?_
    by_cases ht : t = 1
    · simp only [c, ht, ↓reduceIte]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      fin_cases i <;> simp
    · simp [c, ht]
  · have h0 := congrFun (h 0) 0
    rw [hsum0, hsum1, hTinv] at h0
    norm_num [S₂₂, T₂₂, c, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0

/-! ### The Cagan example (p. 24) -/

/-- The matrix `A` of the Cagan model (Miao, p. 24). -/
def caganA {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

/-- The matrix `B` of the Cagan model, with interest semi-elasticity `α`. -/
def caganB {K : Type*} [CommRing K] (α : K) : Matrix (Fin 2) (Fin 2) K := !![1, 1; α, -1]

/-- The matrix `C` of the Cagan model (one forcing variable, the money stock `m_t`). -/
def caganC {K : Type*} [CommRing K] : Matrix (Fin 2) (Fin 1) K := !![0; 1]

/-- **Cagan model** (Miao, p. 24): with `x_t = (R_t, p_t)` and `z_t = m_t`, (1.20) with the
matrices above is the Fisher equation `R_t = p_{t+1} − p_t` together with money market
equilibrium `m_t − p_t = −αR_t`. -/
theorem example_cagan_iff (α : ℝ) (R p m : ℕ → ℝ) :
    IsSolution caganA (caganB α) caganC (fun t => ![m t]) (fun t => ![R t, p t]) ↔
      ∀ t, R t = p (t + 1) - p t ∧ m t - p t = -α * R t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, Fin.forall_fin_two]
  have e1 : (caganA *ᵥ ![R (t + 1), p (t + 1)]) 0 = p (t + 1) := by
    simp [caganA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e2 : (caganA *ᵥ ![R (t + 1), p (t + 1)]) 1 = 0 := by
    simp [caganA, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e3 : (caganB α *ᵥ ![R t, p t] + caganC *ᵥ ![m t]) 0 = R t + p t := by
    simp [caganB, caganC]
  have e4 : (caganB α *ᵥ ![R t, p t] + caganC *ᵥ ![m t]) 1 = α * R t - p t + m t := by
    simp [caganB, caganC]
    ring
  rw [e1, e2, e3, e4]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- Miao, p. 24: in the Cagan model `A` is singular. -/
theorem example_cagan_det {K : Type*} [CommRing K] :
    (caganA : Matrix (Fin 2) (Fin 2) K).det = 0 := by
  simp [caganA, Matrix.det_fin_two]

/-- The Cagan pencil is regular for every `α`: `det(A − B) = −1`. -/
theorem example_cagan_regular {K : Type*} [Field K] (α : K) : IsRegular caganA (caganB α) :=
  ⟨1, by simp [caganA, caganB, Matrix.det_fin_two]⟩

/-- The generalized eigenvalues of the Cagan pencil: `det(B − λA) = −1 − α(1 − λ)`, so for
`α ≠ 0` the only generalized eigenvalue is `1 + 1/α` (the second is infinite). -/
theorem example_cagan_genEigenvalues {α : ℂ} (hα : α ≠ 0) :
    genEigenvalues caganA (caganB α) = {1 + α⁻¹} := by
  ext lam
  change IsGenEigenvalue _ _ lam ↔ lam = 1 + α⁻¹
  have hdet : (caganB α - lam • caganA).det = -1 - α * (1 - lam) := by
    simp [caganA, caganB, Matrix.det_fin_two]
    ring
  rw [isGenEigenvalue_iff_det, hdet]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- For `α = 0` the Cagan pencil has no finite generalized eigenvalue (both are infinite). -/
theorem example_cagan_genEigenvalues_zero : genEigenvalues caganA (caganB (0 : ℂ)) = ∅ := by
  ext lam
  change IsGenEigenvalue _ _ lam ↔ False
  rw [isGenEigenvalue_iff_det]
  simp [caganA, caganB, Matrix.det_fin_two]

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Phase diagrams

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

namespace Miao.DifferenceEquations

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

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonlinear systems

Miao, §1.6, pp. 28–32.

* **Example 1.6.1** (optimal growth). The steady-state equations `C̄ = f(K̄) − δK̄`,
  `1 = β(f'(K̄) + 1 − δ)` (`example_1_6_1_steady`); the first-order Taylor coefficients of the
  Euler equation and the resource constraint (`example_1_6_1_linearization`); the linearised
  equations are equivalent to the printed matrix system (`example_1_6_1_matrix`) and to the
  reduced system with matrix `[[1/β, −1], [f''/A, 1 − βf''/A]]`, `A = −u''/u'`
  (`example_1_6_1_reduced`; the printed entries are correct); trace
  `T = 1 + 1/β − βf''/A > 1 + 1/β > 2` and determinant `1/β > 1` (`example_1_6_1_trace_det`);
  the roots satisfy `0 < λ₁ < 1 < λ₂` (`example_1_6_1_roots`), so the steady state is a saddle:
  for every `dK₀` there is exactly one bounded linearised path, and it converges
  (`example_1_6_1_saddle`).
* **Definition 1.6.1** (periodic points): `Function.minimalPeriod f x = p` iff `fᵖ(x) = x` and
  `p` is the least such positive integer (`definition_1_6_1`); the `p`-cycle has `p` distinct
  points (`definition_1_6_1_cycle`).
* The logistic map `f(x) = 4x − 4x²` (definition copied from
  `RecursiveMethods/DeterministicDynamics/LogisticMap.lean`): the second iterate
  `16x − 80x² + 128x³ − 64x⁴` (`logistic_two`), the fixed points of `f` are exactly `0, 3/4`
  (`logistic_fixed_iff`), those of `f²` exactly `0, 3/4, (5 ± √5)/8` (`logistic_two_fixed_iff`),
  `(5 ± √5)/8` form a two-cycle of minimal period 2 (`logistic_two_cycle`), and the printed
  decimals `0.3455`, `0.9045` are correct to four places (`logistic_two_cycle_decimals`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

open scoped Matrix

/-! ### Example 1.6.1: optimal growth -/

/-- **Example 1.6.1** (Miao, p. 31): a constant path `(K̄, C̄)` satisfies the resource constraint
(1.43) and the Euler equation `u'(C) = βu'(C)(f'(K) + 1 − δ)` iff `C̄ = f(K̄) − δK̄` and
`1 = β(f'(K̄) + 1 − δ)` (given `u'(C̄) ≠ 0`). -/
theorem example_1_6_1_steady {f fp up : ℝ → ℝ} {β δ K C : ℝ} (hu : up C ≠ 0) :
    (C + K - (1 - δ) * K = f K ∧ up C = β * up C * (fp K + 1 - δ)) ↔
      (C = f K - δ * K ∧ 1 = β * (fp K + 1 - δ)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    have : up C * 1 = up C * (β * (fp K + 1 - δ)) := by linarith
    exact mul_left_cancel₀ hu this
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    linear_combination (up C) * h2

/-- **Example 1.6.1** (Miao, p. 31): the first-order Taylor coefficients at the steady state.
For the Euler residual `u'(C_t) − βu'(C_{t+1})(f'(K_{t+1}) + 1 − δ)` the partial derivatives in
`C_t`, `C_{t+1}`, `K_{t+1}` are `u''`, `−βu''(f' + 1 − δ)`, `−βu'f''`; for the resource residual
`C_t + K_{t+1} − (1 − δ)K_t − f(K_t)` they are `1`, `1`, `−(1 − δ) − f'` in `C_t`, `K_{t+1}`,
`K_t`. Setting the linear terms to zero gives the two linearised equations of the book. -/
theorem example_1_6_1_linearization {f fp up : ℝ → ℝ} {β δ Kb Cb upp fpp : ℝ}
    (hf : HasDerivAt f (fp Kb) Kb) (hfp : HasDerivAt fp fpp Kb) (hup : HasDerivAt up upp Cb) :
    HasDerivAt (fun C => up C - β * up Cb * (fp Kb + 1 - δ)) upp Cb ∧
      HasDerivAt (fun C' => up Cb - β * up C' * (fp Kb + 1 - δ))
        (-(β * upp * (fp Kb + 1 - δ))) Cb ∧
      HasDerivAt (fun K' => up Cb - β * up Cb * (fp K' + 1 - δ)) (-(β * up Cb * fpp)) Kb ∧
      HasDerivAt (fun C => C + Kb - (1 - δ) * Kb - f Kb) 1 Cb ∧
      HasDerivAt (fun K' => Cb + K' - (1 - δ) * Kb - f Kb) 1 Kb ∧
      HasDerivAt (fun K => Cb + Kb - (1 - δ) * K - f K) (-(1 - δ) - fp Kb) Kb := by
  refine ⟨HasDerivAt.sub_const _ hup, ?_, ?_, ?_, ?_, ?_⟩
  · have := HasDerivAt.const_sub (up Cb)
      (HasDerivAt.mul_const (HasDerivAt.const_mul β hup) (fp Kb + 1 - δ))
    convert this using 1
  · have := HasDerivAt.const_sub (up Cb)
      (HasDerivAt.const_mul (β * up Cb) (HasDerivAt.add_const (1 - δ) hfp))
    convert this using 1
    ext K; ring
  · have := HasDerivAt.sub_const (f Kb) (HasDerivAt.sub_const ((1 - δ) * Kb)
      (HasDerivAt.add_const Kb (hasDerivAt_id Cb)))
    simpa using this
  · have := HasDerivAt.sub_const (f Kb) (HasDerivAt.sub_const ((1 - δ) * Kb)
      (HasDerivAt.const_add Cb (hasDerivAt_id Kb)))
    simpa using this
  · have := HasDerivAt.sub (HasDerivAt.const_sub (Cb + Kb)
      (HasDerivAt.const_mul (1 - δ) (hasDerivAt_id Kb))) hf
    convert this using 1
    · ext K; simp only [Pi.sub_apply, id]
    · ring

theorem vec2_eq_iff (a b c d : ℝ) : (![a, b] : Fin 2 → ℝ) = ![c, d] ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mulVec22 (a b c d x y : ℝ) :
    !![a, b; c, d] *ᵥ ![x, y] = ![a * x + b * y, c * x + d * y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Example 1.6.1** (Miao, p. 31): at the steady state (`β(f' + 1 − δ) = 1`, `u'' ≠ 0`) the
two linearised equations
`u''dC_t = βu''(f' + 1 − δ)dC_{t+1} + βu'f''dK_{t+1}` and
`dC_t + dK_{t+1} − (1 − δ)dK_t = f'dK_t` are equivalent to the printed system
`[[βu'f''/u'', 1], [1, 0]] (dK_{t+1}, dC_{t+1}) = [[0, 1], [f' + 1 − δ, −1]] (dK_t, dC_t)`. -/
theorem example_1_6_1_matrix {β δ up upp fp fpp : ℝ} (hupp : upp ≠ 0)
    (hss : β * (fp + 1 - δ) = 1) (dK dC : ℕ → ℝ) (t : ℕ) :
    (upp * dC t = β * upp * (fp + 1 - δ) * dC (t + 1) + β * up * fpp * dK (t + 1) ∧
        dC t + dK (t + 1) - (1 - δ) * dK t = fp * dK t) ↔
      !![β * up * fpp / upp, 1; 1, 0] *ᵥ ![dK (t + 1), dC (t + 1)] =
        !![0, 1; fp + 1 - δ, -1] *ᵥ ![dK t, dC t] := by
  rw [mulVec22, mulVec22, vec2_eq_iff]
  have h1 : β * upp * (fp + 1 - δ) = upp := by rw [mul_comm β, mul_assoc, hss, mul_one]
  rw [h1]
  constructor
  · rintro ⟨e1, e2⟩
    refine ⟨?_, by linarith⟩
    field_simp
    linarith
  · rintro ⟨e1, e2⟩
    refine ⟨?_, by linarith⟩
    field_simp at e1
    linarith

/-- **Example 1.6.1** (Miao, p. 31): with `A = −u''/u'` (`u' > 0`, `u'' ≠ 0`) and
`β(f' + 1 − δ) = 1`, the linearised equations are equivalent to
`(dK_{t+1}, dC_{t+1}) = [[1/β, −1], [f''/A, 1 − βf''/A]] (dK_t, dC_t)`, as printed. -/
theorem example_1_6_1_reduced {β δ up upp fp fpp : ℝ} (hβ : β ≠ 0) (hup : 0 < up)
    (hupp : upp ≠ 0) (hss : β * (fp + 1 - δ) = 1) (dK dC : ℕ → ℝ) (t : ℕ) :
    (upp * dC t = β * upp * (fp + 1 - δ) * dC (t + 1) + β * up * fpp * dK (t + 1) ∧
        dC t + dK (t + 1) - (1 - δ) * dK t = fp * dK t) ↔
      ![dK (t + 1), dC (t + 1)] =
        !![1 / β, -1; fpp / (-upp / up), 1 - β * fpp / (-upp / up)] *ᵥ ![dK t, dC t] := by
  rw [mulVec22, vec2_eq_iff]
  have hfp : fp + 1 - δ = 1 / β := by field_simp; linarith
  have h1 : β * upp * (fp + 1 - δ) = upp := by rw [mul_comm β, mul_assoc, hss, mul_one]
  rw [h1]
  have hup' : up ≠ 0 := hup.ne'
  constructor
  · rintro ⟨e1, e2⟩
    have eK : dK (t + 1) = 1 / β * dK t + -1 * dC t := by rw [← hfp]; linarith
    refine ⟨eK, ?_⟩
    rw [eK] at e1
    field_simp
    field_simp at e1
    linarith
  · rintro ⟨e1, e2⟩
    refine ⟨?_, ?_⟩
    · rw [e2, e1]
      field_simp
      ring
    · rw [e1, ← hfp]; ring

/-- **Example 1.6.1** (Miao, p. 31): for `0 < β < 1`, `f'' < 0`, `A > 0`, the coefficient matrix
has trace `T = 1 + 1/β − βf''/A > 1 + 1/β > 2` and determinant `D = 1/β > 1`. -/
theorem example_1_6_1_trace_det {β fpp A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hf : fpp < 0)
    (hA : 0 < A) :
    1 / β + (1 - β * fpp / A) = 1 + 1 / β - β * fpp / A ∧
      1 / β * (1 - β * fpp / A) - (-1) * (fpp / A) = 1 / β ∧
      1 + 1 / β < 1 + 1 / β - β * fpp / A ∧ 2 < 1 + 1 / β ∧ 1 < 1 / β := by
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have h2 : β * fpp / A < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hβ0 hf) hA
  refine ⟨by ring, by field_simp; ring, by linarith, by linarith, h1⟩

/-- **Example 1.6.1** (Miao, p. 31): the characteristic roots satisfy `0 < λ₁ < 1 < λ₂`, so
the steady state is a saddle point. -/
theorem example_1_6_1_roots {β fpp A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hf : fpp < 0)
    (hA : 0 < A) :
    cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) 1 < 0 ∧
      0 < lamLo (1 / β) (-1) (fpp / A) (1 - β * fpp / A) ∧
      lamLo (1 / β) (-1) (fpp / A) (1 - β * fpp / A) < 1 ∧
      1 < lamHi (1 / β) (-1) (fpp / A) (1 - β * fpp / A) := by
  have h2 : β * fpp / A < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hβ0 hf) hA
  have hcp : ∀ μ, cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) μ =
      μ ^ 2 - (1 + 1 / β - β * fpp / A) * μ + 1 / β := fun μ => by
    simp only [cp22]; field_simp; ring
  have h1 : cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) 1 < 0 := by
    rw [hcp]; linarith
  obtain ⟨hlo, hhi⟩ := roots22_lt h1
  refine ⟨h1, ?_, hlo, hhi⟩
  have h0 := cp22_factor h1 0
  rw [hcp] at h0
  have hb : 0 < 1 / β := by positivity
  nlinarith

/-- **Example 1.6.1** (Miao, p. 31): the saddle property of the linearised system. For every
`dK₀` (capital is predetermined) there is exactly one bounded solution, it starts at
`dC₀ = k dK₀` on the saddle line, and it converges to the steady state. -/
theorem example_1_6_1_saddle {β fpp A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hf : fpp < 0)
    (hA : 0 < A) (dK0 : ℝ) :
    (∃ dK dC : ℕ → ℝ, IsSol22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) dK dC ∧ dK 0 = dK0 ∧
      Tendsto dK atTop (𝓝 0) ∧ Tendsto dC atTop (𝓝 0)) ∧
    ∀ dK dC : ℕ → ℝ, IsSol22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) dK dC → BddSeq dK →
      BddSeq dC → dC 0 = kSaddle (1 / β) (-1) (fpp / A) (1 - β * fpp / A) * dK 0 := by
  obtain ⟨h1, hlo0, -, -⟩ := example_1_6_1_roots hβ0 hβ1 hf hA
  have hm : 0 < -1 * (fpp / A) := by
    have := div_neg_of_neg_of_pos hf hA; linarith
  have hc : 0 < cp22 (1 / β) (-1) (fpp / A) (1 - β * fpp / A) (-1) := by
    rw [cp22_factor h1 (-1)]
    have := (roots22_lt h1).2
    nlinarith
  refine ⟨(saddle22_iff h1 hm).2 hc dK0, fun dK dC h hK hC => ?_⟩
  exact (sHi_zero_iff h1 hm dK dC 0).1 (sHi_zero_of_bdd h1 h hK hC)

/-! ### Definition 1.6.1: periodic points -/

/-- **Definition 1.6.1** (Miao, pp. 31–32): `x*` is a periodic point of period `p > 0` (`p` is
the smallest positive integer with `fᵖ(x*) = x*`) iff `Function.minimalPeriod f x* = p`. -/
theorem definition_1_6_1 {α : Type*} (f : α → α) (x : α) {p : ℕ} (hp : 0 < p) :
    Function.minimalPeriod f x = p ↔ f^[p] x = x ∧ ∀ q, 0 < q → q < p → f^[q] x ≠ x := by
  constructor
  · rintro rfl
    exact ⟨Function.iterate_minimalPeriod, fun q hq hlt =>
      Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hq.ne' hlt⟩
  · rintro ⟨h, hmin⟩
    have hle := Function.IsPeriodicPt.minimalPeriod_le hp h
    have hpos := Function.IsPeriodicPt.minimalPeriod_pos hp h
    by_contra hne
    exact hmin _ hpos (lt_of_le_of_ne hle hne) Function.iterate_minimalPeriod

/-- **Definition 1.6.1** (Miao, p. 32): the `p`-cycle `{x*, f(x*), …, f^{p−1}(x*)}` of a point of
minimal period `p` has exactly `p` distinct points. -/
theorem definition_1_6_1_cycle {α : Type*} [DecidableEq α] (f : α → α) (x : α) :
    ((Finset.range (Function.minimalPeriod f x)).image (fun k => f^[k] x)).card =
      Function.minimalPeriod f x := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro m hm n hn hmn
  exact Function.iterate_injOn_Iio_minimalPeriod (by simpa using hm) (by simpa using hn) hmn

/-! ### The logistic map -/

/-- The logistic map `f(x) = 4x − 4x²` (Miao, p. 32). Copied from
`RecursiveMethods/DeterministicDynamics/LogisticMap.lean` (`logistic`). -/
def logistic (x : ℝ) : ℝ := 4 * x - 4 * x ^ 2

/-- Miao, p. 32: `f²(x) = 16x − 80x² + 128x³ − 64x⁴`. -/
theorem logistic_two (x : ℝ) :
    logistic^[2] x = 16 * x - 80 * x ^ 2 + 128 * x ^ 3 - 64 * x ^ 4 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, logistic]
  ring

/-- Miao, p. 32: the fixed points of `f` are exactly `0` and `0.75`. Copied (restated) from
`RecursiveMethods/DeterministicDynamics/LogisticMap.lean` (`ex_6_3a`). -/
theorem logistic_fixed_iff (x : ℝ) : logistic x = x ↔ x = 0 ∨ x = 3 / 4 := by
  simp only [logistic]
  constructor
  · intro h
    have : x * (3 - 4 * x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Miao, p. 32: the fixed points of `f²` are exactly `0`, `3/4` and `(5 ± √5)/8`. -/
theorem logistic_two_fixed_iff (x : ℝ) :
    logistic^[2] x = x ↔
      x = 0 ∨ x = 3 / 4 ∨ x = (5 - Real.sqrt 5) / 8 ∨ x = (5 + Real.sqrt 5) / 8 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have key : logistic^[2] x - x =
      -(x * (4 * x - 3) * (16 * ((x - (5 - Real.sqrt 5) / 8) * (x - (5 + Real.sqrt 5) / 8)))) := by
    rw [logistic_two]
    linear_combination (-(x * (4 * x - 3)) / 4) * h5
  constructor
  · intro h
    have : x * (4 * x - 3) * (16 * ((x - (5 - Real.sqrt 5) / 8) *
        (x - (5 + Real.sqrt 5) / 8))) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl (by linarith))
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · norm_num at h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact Or.inr (Or.inr (Or.inl (by linarith)))
        · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · intro h
    have : logistic^[2] x - x = 0 := by
      rw [key]
      rcases h with rfl | rfl | rfl | rfl <;> ring
    linarith

/-- Miao, p. 32: `(5 − √5)/8` and `(5 + √5)/8` form a two-cycle: `f` swaps them, and each has
minimal period `2` (Definition 1.6.1). -/
theorem logistic_two_cycle :
    logistic ((5 - Real.sqrt 5) / 8) = (5 + Real.sqrt 5) / 8 ∧
      logistic ((5 + Real.sqrt 5) / 8) = (5 - Real.sqrt 5) / 8 ∧
      Function.minimalPeriod logistic ((5 - Real.sqrt 5) / 8) = 2 ∧
      Function.minimalPeriod logistic ((5 + Real.sqrt 5) / 8) = 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have e1 : logistic ((5 - Real.sqrt 5) / 8) = (5 + Real.sqrt 5) / 8 := by
    simp only [logistic]; linear_combination (-1 / 16 : ℝ) * h5
  have e2 : logistic ((5 + Real.sqrt 5) / 8) = (5 - Real.sqrt 5) / 8 := by
    simp only [logistic]; linear_combination (-1 / 16 : ℝ) * h5
  have hper : ∀ y, logistic^[2] y = y → logistic y ≠ y →
      Function.minimalPeriod logistic y = 2 := fun y h2 h1 => by
    refine (definition_1_6_1 logistic y (by norm_num)).2 ⟨h2, fun q hq hlt => ?_⟩
    obtain rfl : q = 1 := by omega
    simpa using h1
  refine ⟨e1, e2, hper _ ?_ ?_, hper _ ?_ ?_⟩
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [e1, e2]
  · rw [e1]; intro h; linarith
  · simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [e2, e1]
  · rw [e2]; intro h; linarith

/-- Miao, p. 32: the printed decimals are correct to four places:
`|(5 − √5)/8 − 0.3455| < 0.00005` and `|(5 + √5)/8 − 0.9045| < 0.00005`. -/
theorem logistic_two_cycle_decimals :
    |(5 - Real.sqrt 5) / 8 - 0.3455| < 0.00005 ∧ |(5 + Real.sqrt 5) / 8 - 0.9045| < 0.00005 := by
  have hlo : (2.236 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hhi : Real.sqrt 5 < 2.2361 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> rw [abs_lt] <;> constructor <;> linarith

end Miao.DifferenceEquations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises of Chapter 1

Miao, §1.8, pp. 41–43. Exercises 3 and 4 are Dynare exercises and are not formalised.

**Exercise 1 (Cagan).** `m_t − p_t = −α(p_{t+1} − p_t)`, `α > 0` (`IsCagan`), which is (1.1)
with `b = (1 + α)/α > 1` (`cagan_isScalarSol`).
* (a), `ρ ∈ [0, 1)`: for every `μ` and `m₀` there is a unique bounded solution,
  `p_t = m̄ + (m_t − m̄)/(1 + α(1 − ρ))`, `m̄ = μ/(1 − ρ)` (`ex_1_1a`), equal to the forward sum
  `(1/(1 + α)) Σ (α/(1 + α))ʲ m_{t+j}` (`ex_1_1a_forward`).
* (a), `ρ = 1`: a bounded solution exists iff `μ = 0` (`ex_1_1a_rho_one_bdd_iff`); for every `μ`
  the unique solution with `p_t − m_t` bounded is `p_t = m_t + αμ` (`ex_1_1a_rho_one`).
* (b): the announced increase `m_t = m̄` (`t < T`), `m̄'` (`t ≥ T`): the unique bounded path is
  `p_t = m̄ + (α/(1 + α))^{T−t}(m̄' − m̄)` for `t ≤ T` and `m̄'` after (`cagan_path`,
  `ex_1_1b_solves`, `ex_1_1b_unique`); the price jumps at the announcement and rises strictly
  to `m̄'` at `T`, staying above money before `T` (`ex_1_1b_shape`).

**Exercise 2 (Dornbusch).** The four equations (`IsDornbusch`) reduce to a forward recursion in
`(e_t, p_t)` (`ex_1_2_reduce`, `IsDorn2`).
* (a) The steady state `r = r*`, `y^d = y`, `p̄ = m̄ − αy + βr*`,
  `ē = p̄ − p* + ((1 − φ)y + γr* − g)/δ` (`ex_1_2a`).
* (b) Deviations solve the 2×2 system `[[1 − θ(δ + γ/β), θδ], [1/β, 1]]` (`ex_1_2_dev`) with
  `p(1) = −θδ/β < 0` and `p(−1) = 4 − θ(2δ + (2γ + δ)/β)`. With `p` predetermined and `e` a jump
  variable, every `p₀` has a (unique) convergent path iff `θ(2δ + (2γ + δ)/β) < 4`
  (`ex_1_2b_iff`); under this condition the bounded path through `p₀` is unique and all others
  are unbounded (`ex_1_2b_unique`). The condition is not automatic in discrete time
  (`ex_1_2b_counterexample`).
* (c) Isoclines: `Δe ≥ 0 ⟺ p ≥ p̄` and `Δp ≥ 0 ⟺ (δ + γ/β)(p − p̄) ≤ δ(e − ē)` (`ex_1_2c`).
* (d) The unexpected permanent increase `m̄ → m̄'` at date 0 from the old steady state: the
  unique bounded path is `p_t = p̄' − λᵗΔm`, `e_t = ē' − kλᵗΔm` (`ex_1_2d_path`,
  `ex_1_2d_unique`); the exchange rate overshoots, `e₀ − ē = (1 − k)Δm > Δm` (`ex_1_2d_overshoot`),
  and for `λ > 0` the price rises and the exchange rate falls monotonically (`ex_1_2d_monotone`).
* (e) The announced increase at `T`: any bounded path from the old steady state has
  `e₀ = ē + λ_hi^{−T}(1 + (1/β)/(λ_hi − m₁₁))Δm` (`ex_1_2e_jump`); this path exists, is bounded
  and converges to the new steady state (`ex_1_2e_exists`); the jump is positive and strictly
  decreasing in `T`, and equals the jump in (d) at `T = 0` (`ex_1_2e_jump_shape`).
-/

open Filter Topology

namespace Miao.DifferenceEquations

/-! ### Exercise 1: the Cagan model -/

/-- The Cagan model under perfect foresight (Miao, Exercise 1, p. 41):
`m_t − p_t = −α(p_{t+1} − p_t)`. -/
def IsCagan (α : ℝ) (m p : ℕ → ℝ) : Prop :=
  ∀ t, m t - p t = -α * (p (t + 1) - p t)

/-- The Cagan model is (1.1) with `b = (1 + α)/α`, `c = −1/α`, `z = m`. -/
theorem cagan_isScalarSol {α : ℝ} (hα : 0 < α) {m p : ℕ → ℝ} :
    IsCagan α m p ↔ IsScalarSol ((1 + α) / α) (-1 / α) m p := by
  simp only [IsCagan, IsScalarSol]
  refine forall_congr' fun t => ?_
  constructor
  · intro h; field_simp; linarith
  · intro h; field_simp at h; linarith

theorem cagan_b_gt_one {α : ℝ} (hα : 0 < α) : 1 < |(1 + α) / α| := by
  rw [abs_of_pos (by positivity), lt_div_iff₀ hα]
  linarith

/-- **Exercise 1(a)** (Miao, p. 41), `ρ ∈ [0, 1)`: for `α > 0`, every `μ` and every `m₀`, the
Cagan model has a unique stable (bounded) solution,
`p_t = m̄ + (m_t − m̄)/(1 + α(1 − ρ))` with `m̄ = μ/(1 − ρ)`. -/
theorem ex_1_1a {α ρ μ : ℝ} (hα : 0 < α) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {m : ℕ → ℝ}
    (hm : ∀ t, m (t + 1) = ρ * m t + μ) :
    IsCagan α m (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) ∧
      BddSeq (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) ∧
      ∀ p, IsCagan α m p → BddSeq p →
        p = fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ)) := by
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 + α * (1 - ρ) := by positivity
  have hmB : BddSeq m :=
    eq_1_5_bdd (b := ρ) (c := μ) (z := fun _ => 1) (by rw [abs_of_nonneg hρ0]; exact hρ1)
      ⟨1, fun _ => by simp⟩ (fun t => by rw [hm t, mul_one])
  have hsol : IsCagan α m (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) := by
    intro t
    simp only
    rw [hm t]
    field_simp
    ring
  have hB : BddSeq (fun t => μ / (1 - ρ) + (m t - μ / (1 - ρ)) / (1 + α * (1 - ρ))) := by
    obtain ⟨M, hM⟩ := hmB
    refine ⟨|μ / (1 - ρ)| + (M + |μ / (1 - ρ)|) / (1 + α * (1 - ρ)), fun t => ?_⟩
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_div, abs_of_pos h2]
    exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hM t) le_rfl)) h2.le
  refine ⟨hsol, hB, fun p hp hpB => ?_⟩
  have hb := cagan_b_gt_one hα
  rw [eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 hp) hpB,
    eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 hsol) hB]

/-- **Exercise 1(a)** (Miao, p. 41): the stable solution is the forward solution
`p_t = (1/(1 + α)) Σ_{j≥0} (α/(1 + α))ʲ m_{t+j}` (this is (1.8) for the Cagan model). -/
theorem ex_1_1a_forward {α : ℝ} (hα : 0 < α) (m : ℕ → ℝ) (t : ℕ) :
    fwdSol ((1 + α) / α) (-1 / α) m t =
      1 / (1 + α) * ∑' j : ℕ, (α / (1 + α)) ^ j * m (t + j) := by
  have : (1 : ℝ) / ((1 + α) / α) = α / (1 + α) := by rw [one_div_div]
  simp only [fwdSol, this]
  congr 1
  field_simp

/-- **Exercise 1(a)** (Miao, p. 41), `ρ = 1`: with `m_{t+1} = m_t + μ` a stable (bounded)
solution exists iff `μ = 0`; money grows without bound otherwise. -/
theorem ex_1_1a_rho_one_bdd_iff {α μ : ℝ} (hα : 0 < α) {m : ℕ → ℝ}
    (hm : ∀ t, m (t + 1) = m t + μ) :
    (∃ p, IsCagan α m p ∧ BddSeq p) ↔ μ = 0 := by
  have hform : ∀ t, m t = m 0 + μ * t := fun t => by
    induction t with
    | zero => simp
    | succ n ih => rw [hm n, ih]; push_cast; ring
  constructor
  · rintro ⟨p, hp, ⟨M, hM⟩⟩
    by_contra hμ
    have hmB : ∀ t, |m t| ≤ M + α * (M + M) := fun t => by
      have := hp t
      have e : m t = p t - α * (p (t + 1) - p t) := by linarith
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hM t) ?_)
      rw [abs_mul, abs_of_pos hα]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM _) (hM t))) hα.le
    have hlim : Tendsto (fun t : ℕ => |m 0 + μ * t|) atTop atTop := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (abs_pos.2 hμ)
      refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-|m 0|) h)
      have := abs_sub_abs_le_abs_sub (μ * t) (-m 0)
      rw [abs_neg, sub_neg_eq_add, abs_mul, Nat.abs_cast, add_comm (μ * t)] at this
      linarith
    obtain ⟨t, ht⟩ := (hlim.eventually_gt_atTop (M + α * (M + M))).exists
    rw [← hform t] at ht
    linarith [hmB t]
  · rintro rfl
    refine ⟨m, fun t => by rw [hm t]; ring, ⟨|m 0|, fun t => by rw [hform t]; simp⟩⟩

/-- **Exercise 1(a)** (Miao, p. 41), `ρ = 1`, corrected statement: for every `μ` the unique
solution with `p_t − m_t` bounded (no bubble in real balances) is `p_t = m_t + αμ`. -/
theorem ex_1_1a_rho_one {α μ : ℝ} (hα : 0 < α) {m : ℕ → ℝ} (hm : ∀ t, m (t + 1) = m t + μ) :
    IsCagan α m (fun t => m t + α * μ) ∧
      ∀ p, IsCagan α m p → BddSeq (fun t => p t - m t) → p = fun t => m t + α * μ := by
  refine ⟨fun t => by simp only; rw [hm t]; ring, fun p hp hB => ?_⟩
  have hq : IsScalarSol ((1 + α) / α) (-μ) (fun _ => 1) (fun t => p t - m t) := by
    intro t
    have := hp t
    simp only
    rw [hm t]
    field_simp
    linarith
  have := (eq_1_3_bdd_iff (cagan_b_gt_one hα) hq).1 hB
  have hbar : -μ / (1 - (1 + α) / α) = α * μ := by field_simp; ring
  ext t
  have := this t
  rw [hbar] at this
  linarith

/-- The announced money path of Exercise 1(b): `m̄` before `T`, `m̄'` from `T` on. -/
def cagan_money (mb mb' : ℝ) (T t : ℕ) : ℝ :=
  if t < T then mb else mb'

/-- The price path of Exercise 1(b): `p_t = m̄ + (α/(1 + α))^{T−t}(m̄' − m̄)` for `t ≤ T`,
`p_t = m̄'` for `t ≥ T`. -/
noncomputable def cagan_path (α mb mb' : ℝ) (T t : ℕ) : ℝ :=
  if t ≤ T then mb + (α / (1 + α)) ^ (T - t) * (mb' - mb) else mb'

/-- **Exercise 1(b)** (Miao, p. 41): the price path solves the Cagan model with the announced
money path. -/
theorem ex_1_1b_solves {α mb mb' : ℝ} (hα : 0 < α) (T : ℕ) :
    IsCagan α (cagan_money mb mb' T) (cagan_path α mb mb' T) := by
  intro t
  have h1 : (1 + α) ≠ 0 := by positivity
  rcases lt_trichotomy (t + 1) (T + 1) with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, T = t + 1 + k := ⟨T - (t + 1), by omega⟩
    simp only [cagan_money, cagan_path, show t < t + 1 + k by omega, show t ≤ t + 1 + k by omega,
      show t + 1 ≤ t + 1 + k by omega, ↓reduceIte, show t + 1 + k - t = k + 1 by omega,
      show t + 1 + k - (t + 1) = k by omega, pow_succ]
    field_simp
    ring
  · obtain rfl : t = T := by omega
    simp only [cagan_money, cagan_path, lt_irrefl, le_refl, show ¬ t + 1 ≤ t by omega,
      ↓reduceIte, Nat.sub_self, pow_zero, one_mul]
    ring
  · simp only [cagan_money, cagan_path, show ¬ t < T by omega, show ¬ t ≤ T by omega,
      show ¬ t + 1 ≤ T by omega, ↓reduceIte]
    ring

theorem cagan_path_const {α mb mb' : ℝ} {T t : ℕ} (ht : T ≤ t) :
    cagan_path α mb mb' T t = mb' := by
  rcases ht.lt_or_eq with h | rfl
  · simp only [cagan_path, show ¬ t ≤ T by omega, ↓reduceIte]
  · simp only [cagan_path, le_refl, ↓reduceIte, Nat.sub_self, pow_zero, one_mul]
    ring

/-- **Exercise 1(b)** (Miao, p. 41): the price path is the unique bounded solution. -/
theorem ex_1_1b_unique {α mb mb' : ℝ} (hα : 0 < α) (T : ℕ) {p : ℕ → ℝ}
    (hp : IsCagan α (cagan_money mb mb' T) p) (hB : BddSeq p) : p = cagan_path α mb mb' T := by
  have hb := cagan_b_gt_one hα
  have hmB : BddSeq (cagan_money mb mb' T) :=
    ⟨|mb| + |mb'|, fun t => by
      simp only [cagan_money]; split_ifs
      · linarith [abs_nonneg mb']
      · linarith [abs_nonneg mb]⟩
  have hpathB : BddSeq (cagan_path α mb mb' T) :=
    bddSeq_of_tendsto (L := mb') (tendsto_const_nhds.congr'
      (eventually_atTop.2 ⟨T, fun t ht => (cagan_path_const ht).symm⟩))
  rw [eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 hp) hB,
    eq_1_8_unique_bdd hb hmB ((cagan_isScalarSol hα).1 (ex_1_1b_solves hα T)) hpathB]

/-- **Exercise 1(b)** (Miao, p. 41): for `m̄' > m̄` the price jumps at the announcement
(`p₀ > m̄` when `T > 0`, i.e. above the pre-announcement price `m̄`), rises strictly until `T`,
stays above the money supply before `T`, and equals `m̄'` from `T` on. -/
theorem ex_1_1b_shape {α mb mb' : ℝ} (hα : 0 < α) (hm : mb < mb') (T : ℕ) :
    mb < cagan_path α mb mb' T 0 ∧
      (∀ t, t < T → cagan_path α mb mb' T t < cagan_path α mb mb' T (t + 1)) ∧
      (∀ t, t < T → cagan_money mb mb' T t < cagan_path α mb mb' T t) ∧
      ∀ t, T ≤ t → cagan_path α mb mb' T t = mb' := by
  have hq0 : 0 < α / (1 + α) := by positivity
  have hq1 : α / (1 + α) < 1 := by rw [div_lt_one (by positivity)]; linarith
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_, fun t ht => cagan_path_const ht⟩
  · simp only [cagan_path, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
    have : 0 < (α / (1 + α)) ^ T * (mb' - mb) := mul_pos (pow_pos hq0 T) (by linarith)
    linarith
  · obtain ⟨k, rfl⟩ : ∃ k, T = t + 1 + k := ⟨T - (t + 1), by omega⟩
    simp only [cagan_path, show t ≤ t + 1 + k by omega, show t + 1 ≤ t + 1 + k by omega,
      ↓reduceIte, show t + 1 + k - t = k + 1 by omega, show t + 1 + k - (t + 1) = k by omega,
      pow_succ]
    have hk := pow_pos hq0 k
    have : (α / (1 + α)) ^ k * (α / (1 + α)) < (α / (1 + α)) ^ k := by
      nlinarith
    nlinarith
  · simp only [cagan_money, cagan_path, ht, ↓reduceIte, ht.le]
    have : 0 < (α / (1 + α)) ^ (T - t) * (mb' - mb) := mul_pos (pow_pos hq0 _) (by linarith)
    linarith

/-! ### Exercise 2: the Dornbusch model -/

/-- The Dornbusch model (Miao, Exercise 2, p. 42):
`y^d_t = δ(e_t + p* − p_t) − γr_t + φy + g`, `p_{t+1} − p_t = θ(y^d_t − y)`,
`m_t − p_t = αy − βr_t`, `r_t = r* + e_{t+1} − e_t`. -/
def IsDornbusch (δ γ φ θ α β y g ps rs : ℝ) (m yd e p r : ℕ → ℝ) : Prop :=
  ∀ t, yd t = δ * (e t + ps - p t) - γ * r t + φ * y + g ∧ p (t + 1) - p t = θ * (yd t - y) ∧
    m t - p t = α * y - β * r t ∧ r t = rs + e (t + 1) - e t

/-- The reduced forward recursion of the Dornbusch model in `(e_t, p_t)`. -/
def IsDorn2 (δ γ φ θ α β y g ps rs : ℝ) (m e p : ℕ → ℝ) : Prop :=
  ∀ t, e (t + 1) = e t + (α * y - m t + p t) / β - rs ∧
    p (t + 1) = p t + θ * (δ * (e t + ps - p t) - γ * ((α * y - m t + p t) / β) + φ * y + g - y)

/-- The steady-state price `p̄ = m̄ − αy + βr*`. -/
def pbarD (α β y rs mb : ℝ) : ℝ := mb - α * y + β * rs

/-- The steady-state exchange rate `ē = p̄ − p* + ((1 − φ)y + γr* − g)/δ`. -/
noncomputable def ebarD (δ γ φ α β y g ps rs mb : ℝ) : ℝ :=
  pbarD α β y rs mb - ps + ((1 - φ) * y + γ * rs - g) / δ

/-- The `(p, p)` entry `1 − θ(δ + γ/β)` of the Dornbusch coefficient matrix. -/
noncomputable def dM11 (θ δ γ β : ℝ) : ℝ := 1 - θ * (δ + γ / β)

/-- The stable root of the Dornbusch matrix `[[1 − θ(δ + γ/β), θδ], [1/β, 1]]`. -/
noncomputable abbrev dLo (θ δ γ β : ℝ) : ℝ := lamLo (dM11 θ δ γ β) (θ * δ) (1 / β) 1

/-- The unstable root of the Dornbusch matrix. -/
noncomputable abbrev dHi (θ δ γ β : ℝ) : ℝ := lamHi (dM11 θ δ γ β) (θ * δ) (1 / β) 1

/-- The slope `k = (λ_lo − m₁₁)/(θδ)` of the Dornbusch saddle path in `(p − p̄, e − ē)`. -/
noncomputable abbrev dK (θ δ γ β : ℝ) : ℝ := kSaddle (dM11 θ δ γ β) (θ * δ) (1 / β) 1

/-- Forward iteration of the reduced Dornbusch recursion from `(e₀, p₀)`. -/
noncomputable def dornIter (δ γ φ θ α β y g ps rs : ℝ) (m : ℕ → ℝ) (e0 p0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (e0, p0)
  | t + 1 => ((dornIter δ γ φ θ α β y g ps rs m e0 p0 t).1 +
      (α * y - m t + (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) / β - rs,
    (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2 + θ * (δ * ((dornIter δ γ φ θ α β y g ps rs m e0
      p0 t).1 + ps - (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) - γ * ((α * y - m t +
      (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) / β) + φ * y + g - y))

variable {δ γ φ θ α β y g ps rs : ℝ}

theorem dornIter_sol (m : ℕ → ℝ) (e0 p0 : ℝ) :
    IsDorn2 δ γ φ θ α β y g ps rs m (fun t => (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).1)
      (fun t => (dornIter δ γ φ θ α β y g ps rs m e0 p0 t).2) := fun _ => ⟨rfl, rfl⟩

/-- **Exercise 2** (Miao, p. 42): the four equations are equivalent to `r_t`, `y^d_t` given by
the money market and demand equations plus the forward recursion `IsDorn2` in `(e, p)`. -/
theorem ex_1_2_reduce (hβ : β ≠ 0) (m yd e p r : ℕ → ℝ) :
    IsDornbusch δ γ φ θ α β y g ps rs m yd e p r ↔
      (∀ t, r t = (α * y - m t + p t) / β ∧ yd t = δ * (e t + ps - p t) - γ * r t + φ * y + g) ∧
        IsDorn2 δ γ φ θ α β y g ps rs m e p := by
  constructor
  · intro h
    have hr : ∀ t, r t = (α * y - m t + p t) / β := fun t => by
      rw [eq_div_iff hβ]; linarith [(h t).2.2.1]
    refine ⟨fun t => ⟨hr t, (h t).1⟩, fun t => ⟨?_, ?_⟩⟩
    · rw [← hr t]; linarith [(h t).2.2.2]
    · rw [← hr t]; have := (h t).2.1; rw [(h t).1] at this; linarith
  · rintro ⟨h1, h2⟩ t
    refine ⟨(h1 t).2, ?_, ?_, ?_⟩
    · rw [(h2 t).2, (h1 t).2, (h1 t).1]; ring
    · rw [(h1 t).1]; field_simp; ring
    · rw [(h2 t).1, (h1 t).1]; ring

/-- **Exercise 2(a)** (Miao, p. 43): with constant money `m̄`, a constant `(y^d, e, p, r)` solves
the model iff `r = r*`, `y^d = y`, `p = p̄ = m̄ − αy + βr*` and
`e = ē = p̄ − p* + ((1 − φ)y + γr* − g)/δ`. -/
theorem ex_1_2a (hδ : δ ≠ 0) (hθ : θ ≠ 0) (mb ydb eb pb rb : ℝ) :
    IsDornbusch δ γ φ θ α β y g ps rs (fun _ => mb) (fun _ => ydb) (fun _ => eb) (fun _ => pb)
        (fun _ => rb) ↔
      rb = rs ∧ ydb = y ∧ pb = pbarD α β y rs mb ∧ eb = ebarD δ γ φ α β y g ps rs mb := by
  simp only [IsDornbusch, pbarD, ebarD]
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h 0
    have hr : rb = rs := by linarith
    have hyd : ydb = y := by
      have : θ * (ydb - y) = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hθ
      linarith
    have hp : pb = mb - α * y + β * rs := by rw [← hr]; linarith
    refine ⟨hr, hyd, hp, ?_⟩
    rw [hr, hyd, hp] at h1
    field_simp
    linarith
  · rintro ⟨rfl, rfl, rfl, rfl⟩ _
    refine ⟨?_, by ring, by ring, by ring⟩
    field_simp
    ring

/-- **Exercise 2** (Miao, p. 43): when `m_t = m_c`, the deviations from the steady state
`(p̄(m_c), ē(m_c))` move one step by the matrix `[[1 − θ(δ + γ/β), θδ], [1/β, 1]]`. -/
theorem ex_1_2_dev_step (hδ : δ ≠ 0) (hβ : β ≠ 0) {m e p : ℕ → ℝ} {mc : ℝ} {t : ℕ}
    (hm : m t = mc) :
    (e (t + 1) = e t + (α * y - m t + p t) / β - rs ∧
      p (t + 1) = p t + θ * (δ * (e t + ps - p t) - γ * ((α * y - m t + p t) / β) + φ * y + g
        - y)) ↔
    (p (t + 1) - pbarD α β y rs mc = dM11 θ δ γ β * (p t - pbarD α β y rs mc) +
        θ * δ * (e t - ebarD δ γ φ α β y g ps rs mc) ∧
      e (t + 1) - ebarD δ γ φ α β y g ps rs mc = 1 / β * (p t - pbarD α β y rs mc) +
        1 * (e t - ebarD δ γ φ α β y g ps rs mc)) := by
  rw [hm]
  have i1 : θ * (δ * (e t + ps - p t) - γ * ((α * y - mc + p t) / β) + φ * y + g - y) =
      (dM11 θ δ γ β - 1) * (p t - pbarD α β y rs mc) +
        θ * δ * (e t - ebarD δ γ φ α β y g ps rs mc) := by
    simp only [dM11, ebarD, pbarD]; field_simp; ring
  have i2 : e t + (α * y - mc + p t) / β - rs = e t + 1 / β * (p t - pbarD α β y rs mc) := by
    simp only [pbarD]; field_simp; ring
  rw [i1, i2]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [h2]; ring
    · rw [h1]; ring
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- **Exercise 2(b)** (Miao, p. 43): with constant money the deviations solve the 2×2 system. -/
theorem ex_1_2_dev (hδ : δ ≠ 0) (hβ : β ≠ 0) (mb : ℝ) (e p : ℕ → ℝ) :
    IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p ↔
      IsSol22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (fun t => p t - pbarD α β y rs mb)
        (fun t => e t - ebarD δ γ φ α β y g ps rs mb) :=
  forall_congr' fun _ => ex_1_2_dev_step (m := fun _ => mb) hδ hβ rfl

theorem dorn_cp_one (hβ : β ≠ 0) :
    cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 1 = -(θ * δ / β) := by
  simp only [cp22, dM11]; field_simp; ring

/-- **Exercise 2(b)** (Miao, p. 43): `p(−1) = 4 − θ(2δ + (2γ + δ)/β)`. -/
theorem dorn_cp_neg_one (hβ : β ≠ 0) :
    cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (-1) = 4 - θ * (2 * δ + (2 * γ + δ) / β) := by
  simp only [cp22, dM11]; field_simp; ring

theorem dorn_h1 (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) :
    cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 1 < 0 := by
  rw [dorn_cp_one hβ.ne']
  have : 0 < θ * δ / β := by positivity
  linarith

theorem dorn_hm (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) : 0 < θ * δ * (1 / β) := by positivity

/-- Under `θ(2δ + (2γ + δ)/β) < 4`, a path on the saddle line converges to the steady state. -/
theorem dorn_tendsto (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p)
    (hk : e 0 - ebarD δ γ φ α β y g ps rs mb = dK θ δ γ β * (p 0 - pbarD α β y rs mb)) :
    Tendsto p atTop (𝓝 (pbarD α β y rs mb)) ∧
      Tendsto e atTop (𝓝 (ebarD δ γ φ α β y g ps rs mb)) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hc : 0 < cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (-1) := by
    rw [dorn_cp_neg_one hβ.ne']; linarith
  have hdev := (ex_1_2_dev hδ.ne' hβ.ne' mb e p).1 h
  obtain ⟨hX, hY⟩ := hdev.ext (saddle22 h1 (by positivity) (p 0 - pbarD α β y rs mb))
    (by simp) (by simp only [pow_zero, one_mul]; exact hk)
  obtain ⟨t1, t2⟩ := saddle22_tendsto h1 hc (p 0 - pbarD α β y rs mb)
  rw [← hX] at t1
  rw [← hY] at t2
  exact ⟨by simpa using t1.add_const (pbarD α β y rs mb),
    by simpa using t2.add_const (ebarD δ γ φ α β y g ps rs mb)⟩

/-- **Exercise 2(b)** (Miao, p. 43): with `p` predetermined and `e` a jump variable, every `p₀`
has a path converging to the steady state iff `θ(2δ + (2γ + δ)/β) < 4` (equivalently the stable
root lies in `(−1, 1)`; the other root always exceeds `1`). -/
theorem ex_1_2b_iff (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) (mb : ℝ) :
    (∀ p0, ∃ e p : ℕ → ℝ, IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p ∧ p 0 = p0 ∧
      Tendsto p atTop (𝓝 (pbarD α β y rs mb)) ∧
      Tendsto e atTop (𝓝 (ebarD δ γ φ α β y g ps rs mb))) ↔
      θ * (2 * δ + (2 * γ + δ) / β) < 4 := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  constructor
  · intro H
    have := (saddle22_iff h1 (dorn_hm hδ hθ hβ)).1 (fun X0 => by
      obtain ⟨e, p, h, hp0, hp, he⟩ := H (X0 + pbarD α β y rs mb)
      exact ⟨_, _, (ex_1_2_dev hδ.ne' hβ.ne' mb e p).1 h, by simp [hp0],
        by simpa using hp.sub_const (pbarD α β y rs mb),
        by simpa using he.sub_const (ebarD δ γ φ α β y g ps rs mb)⟩)
    rw [dorn_cp_neg_one hβ.ne'] at this
    linarith
  · intro hcond p0
    set e0 := ebarD δ γ φ α β y g ps rs mb + dK θ δ γ β * (p0 - pbarD α β y rs mb)
    have hsol := dornIter_sol (δ := δ) (γ := γ) (φ := φ) (θ := θ) (α := α) (β := β) (y := y)
      (g := g) (ps := ps) (rs := rs) (fun _ => mb) e0 p0
    refine ⟨_, _, hsol, rfl, dorn_tendsto hδ hθ hβ hcond hsol ?_⟩
    simp only [dornIter, e0]
    ring

/-- **Exercise 2(b)** (Miao, p. 43): under `θ(2δ + (2γ + δ)/β) < 4` a path is bounded iff it
starts on the saddle line `e₀ − ē = k(p₀ − p̄)`; so for given `p₀` the stable solution is unique
(`e₀` jumps onto the line) and every other path is unbounded. -/
theorem ex_1_2b_unique (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p) :
    (BddSeq p ∧ BddSeq e) ↔
      e 0 - ebarD δ γ φ α β y g ps rs mb = dK θ δ γ β * (p 0 - pbarD α β y rs mb) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hm := dorn_hm hδ hθ hβ
  have hdev := (ex_1_2_dev hδ.ne' hβ.ne' mb e p).1 h
  constructor
  · rintro ⟨hp, he⟩
    exact (sHi_zero_iff h1 hm _ _ 0).1 (sHi_zero_of_bdd h1 hdev
      (bddSeq_sub_const hp _) (bddSeq_sub_const he _))
  · intro hk
    obtain ⟨t1, t2⟩ := dorn_tendsto hδ hθ hβ hcond h hk
    exact ⟨bddSeq_of_tendsto t1, bddSeq_of_tendsto t2⟩

/-- **Exercise 2(b)** (Miao, p. 43): the stability condition is not automatic in discrete time.
For `δ = γ = β = θ = 1`, `θ(2δ + (2γ + δ)/β) = 5 > 4`, both roots are unstable, and the steady
state is the only bounded path. -/
theorem ex_1_2b_counterexample {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 1 1 φ 1 α 1 y g ps rs (fun _ => mb) e p) (hp : BddSeq p) (he : BddSeq e) :
    (1 : ℝ) * (2 * 1 + (2 * 1 + 1) / 1) = 5 ∧
      p = (fun _ => pbarD α 1 y rs mb) ∧ e = (fun _ => ebarD 1 1 φ α 1 y g ps rs mb) := by
  have h1 := dorn_h1 (δ := 1) (θ := 1) (β := 1) (γ := 1) one_pos one_pos one_pos
  have hc : cp22 (dM11 1 1 1 1) (1 * 1) (1 / 1) 1 (-1) < 0 := by
    rw [dorn_cp_neg_one one_ne_zero]; norm_num
  obtain ⟨hX, hY⟩ := saddle22_only_zero h1 (dorn_hm one_pos one_pos one_pos) hc
    ((ex_1_2_dev one_ne_zero one_ne_zero mb e p).1 h) (bddSeq_sub_const hp _)
    (bddSeq_sub_const he _)
  refine ⟨by norm_num, ?_, ?_⟩
  · ext t; have := congrFun hX t; simp only [Pi.zero_apply] at this; linarith
  · ext t; have := congrFun hY t; simp only [Pi.zero_apply] at this; linarith

/-- **Exercise 2(c)** (Miao, p. 43), the phase-diagram isoclines: with constant money,
`Δe_t ≥ 0 ⟺ p_t ≥ p̄` and `Δp_t ≥ 0 ⟺ (δ + γ/β)(p_t − p̄) ≤ δ(e_t − ē)`. -/
theorem ex_1_2c (hδ : δ ≠ 0) (hθ : 0 < θ) (hβ : 0 < β) {mb : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb) e p) (t : ℕ) :
    (0 ≤ e (t + 1) - e t ↔ pbarD α β y rs mb ≤ p t) ∧
      (0 ≤ p (t + 1) - p t ↔
        (δ + γ / β) * (p t - pbarD α β y rs mb) ≤ δ * (e t - ebarD δ γ φ α β y g ps rs mb)) := by
  obtain ⟨h1, h2⟩ := ((ex_1_2_dev hδ hβ.ne' mb e p).1 h) t
  simp only at h1 h2
  have he : e (t + 1) - e t = 1 / β * (p t - pbarD α β y rs mb) := by linarith
  have hp : p (t + 1) - p t = θ * (δ * (e t - ebarD δ γ φ α β y g ps rs mb) -
      (δ + γ / β) * (p t - pbarD α β y rs mb)) := by
    simp only [dM11] at h1; linarith
  rw [he, hp]
  constructor
  · rw [mul_nonneg_iff_of_pos_left (one_div_pos.2 hβ), sub_nonneg]
  · rw [mul_nonneg_iff_of_pos_left hθ, sub_nonneg]

theorem pbarD_sub (mb mb' : ℝ) : pbarD α β y rs mb' = pbarD α β y rs mb + (mb' - mb) := by
  simp only [pbarD]; ring

theorem ebarD_sub (mb mb' : ℝ) :
    ebarD δ γ φ α β y g ps rs mb' = ebarD δ γ φ α β y g ps rs mb + (mb' - mb) := by
  simp only [ebarD, pbarD]; ring

/-- The saddle slope of the Dornbusch model is negative: `k < 0`. -/
theorem dK_neg (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) : dK θ δ γ β < 0 := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have := (lamLo_lt_m11 h1 (dorn_hm hδ hθ hβ)).1
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- **Exercise 2(d)** (Miao, p. 43): after an unexpected permanent increase `m̄ → m̄'` at date 0,
starting from the old steady state `p₀ = p̄(m̄)`, the path `p_t = p̄' − λᵗΔm`,
`e_t = ē' − kλᵗΔm` (`Δm = m̄' − m̄`, `λ = λ_lo`) solves the model and converges to the new
steady state. -/
theorem ex_1_2d_path (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) (mb mb' : ℝ) :
    IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb')
        (fun t => ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)))
        (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) ∧
      pbarD α β y rs mb' - dLo θ δ γ β ^ 0 * (mb' - mb) = pbarD α β y rs mb ∧
      Tendsto (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) atTop
        (𝓝 (pbarD α β y rs mb')) ∧
      Tendsto (fun t => ebarD δ γ φ α β y g ps rs mb' -
        dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb))) atTop
        (𝓝 (ebarD δ γ φ α β y g ps rs mb')) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hS := saddle22 h1 (by positivity : θ * δ ≠ 0) (-(mb' - mb))
  have hsol : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb')
      (fun t => ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)))
      (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) := by
    rw [ex_1_2_dev hδ.ne' hβ.ne']
    have e1 : (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb) - pbarD α β y rs mb') =
        fun t => dLo θ δ γ β ^ t * (-(mb' - mb)) := by ext t; ring
    have e2 : (fun t => ebarD δ γ φ α β y g ps rs mb' -
        dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)) - ebarD δ γ φ α β y g ps rs mb') =
        fun t => dLo θ δ γ β ^ t * (dK θ δ γ β * -(mb' - mb)) := by ext t; ring
    rw [e1, e2]
    exact hS
  have hp0 : pbarD α β y rs mb' - dLo θ δ γ β ^ 0 * (mb' - mb) = pbarD α β y rs mb := by
    rw [pbarD_sub mb mb']; ring
  obtain ⟨t1, t2⟩ := dorn_tendsto hδ hθ hβ hcond hsol (by simp only [pow_zero]; ring)
  exact ⟨hsol, hp0, t1, t2⟩

/-- **Exercise 2(d)** (Miao, p. 43): this is the only bounded path from `p₀ = p̄(m̄)`. -/
theorem ex_1_2d_unique (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) {mb mb' : ℝ} {e p : ℕ → ℝ}
    (h : IsDorn2 δ γ φ θ α β y g ps rs (fun _ => mb') e p) (hp0 : p 0 = pbarD α β y rs mb)
    (hp : BddSeq p) (he : BddSeq e) :
    p = (fun t => pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb)) ∧
      e = (fun t => ebarD δ γ φ α β y g ps rs mb' -
        dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb))) := by
  have hk := (ex_1_2b_unique hδ hθ hβ hcond h).1 ⟨hp, he⟩
  obtain ⟨hsol, -, -, -⟩ := ex_1_2d_path (φ := φ) (α := α) (y := y) (g := g) (ps := ps)
    (rs := rs) hδ hθ hβ hcond mb mb'
  have hd := (ex_1_2_dev hδ.ne' hβ.ne' mb' e p).1 h
  have hd' := (ex_1_2_dev hδ.ne' hβ.ne' mb' _ _).1 hsol
  have hP0 : p 0 - pbarD α β y rs mb' = -(mb' - mb) := by rw [hp0, pbarD_sub mb mb']; ring
  obtain ⟨hX, hY⟩ := hd.ext hd' (by simp only [pow_zero]; rw [hP0]; ring)
    (by simp only [pow_zero]; rw [hk, hP0]; ring)
  constructor
  · ext t; have := congrFun hX t; linarith
  · ext t; have := congrFun hY t; linarith

/-- **Exercise 2(d)** (Miao, p. 43), overshooting: for `m̄' > m̄` the exchange rate jumps at date
0 to `e₀ = ē' − kΔm` above its new steady state `ē'`, and depreciates by `(1 − k)Δm > Δm`. -/
theorem ex_1_2d_overshoot (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ}
    (hm : mb < mb') :
    ebarD δ γ φ α β y g ps rs mb' <
        ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ 0 * (mb' - mb)) ∧
      ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ 0 * (mb' - mb)) -
          ebarD δ γ φ α β y g ps rs mb = (1 - dK θ δ γ β) * (mb' - mb) ∧
      mb' - mb < (1 - dK θ δ γ β) * (mb' - mb) := by
  have hk := dK_neg (γ := γ) hδ hθ hβ
  have hΔ : 0 < mb' - mb := by linarith
  refine ⟨?_, by rw [ebarD_sub mb mb']; ring, by nlinarith⟩
  simp only [pow_zero, one_mul]
  nlinarith

/-- **Exercise 2(d)** (Miao, p. 43): if the stable root is positive (`0 < λ < 1`), the price
rises and the exchange rate falls monotonically towards the new steady state. -/
theorem ex_1_2d_monotone (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ}
    (hm : mb < mb') (hl : 0 < dLo θ δ γ β) (t : ℕ) :
    pbarD α β y rs mb' - dLo θ δ γ β ^ t * (mb' - mb) <
        pbarD α β y rs mb' - dLo θ δ γ β ^ (t + 1) * (mb' - mb) ∧
      ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ (t + 1) * (mb' - mb)) <
        ebarD δ γ φ α β y g ps rs mb' - dK θ δ γ β * (dLo θ δ γ β ^ t * (mb' - mb)) := by
  have hk := dK_neg (γ := γ) hδ hθ hβ
  have hl1 := (roots22_lt (dorn_h1 (γ := γ) hδ hθ hβ)).1
  have hΔ : 0 < mb' - mb := by linarith
  have hpt := pow_pos hl t
  have hd : 0 < dLo θ δ γ β ^ t * (mb' - mb) * (1 - dLo θ δ γ β) :=
    mul_pos (mul_pos hpt hΔ) (by linarith)
  rw [pow_succ]
  constructor
  · nlinarith
  · nlinarith

/-- One-step dynamics of the announced-increase economy (Exercise 2(e)): before `T` the
deviations from the old steady state move by the matrix, and from `T` on the deviations from the
new steady state solve the 2×2 system. -/
theorem dorn_announce_core (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ} {T : ℕ}
    {e p : ℕ → ℝ} (h : IsDorn2 δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e p) :
    IsSol22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (fun t => p (T + t) - pbarD α β y rs mb')
        (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') ∧
      sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β) (fun t => p (T + t) - pbarD α β y rs mb')
          (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') 0 =
        dHi θ δ γ β ^ T * sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β)
          (fun t => p t - pbarD α β y rs mb) (fun t => e t - ebarD δ γ φ α β y g ps rs mb) 0 -
          (1 / β + dHi θ δ γ β - dM11 θ δ γ β) * (mb' - mb) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hnew : IsSol22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (fun t => p (T + t) - pbarD α β y rs mb')
      (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') := fun t =>
    (ex_1_2_dev_step (m := cagan_money mb mb' T) (t := T + t) (mc := mb') hδ.ne' hβ.ne'
      (by simp only [cagan_money, show ¬ T + t < T by omega, ↓reduceIte])).1 (h (T + t))
  have hold : ∀ k, k ≤ T → sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β)
      (fun t => p t - pbarD α β y rs mb) (fun t => e t - ebarD δ γ φ α β y g ps rs mb) k =
      dHi θ δ γ β ^ k * sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β)
      (fun t => p t - pbarD α β y rs mb) (fun t => e t - ebarD δ γ φ α β y g ps rs mb) 0 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hstep := (ex_1_2_dev_step (m := cagan_money mb mb' T) (t := n) (mc := mb) hδ.ne'
        hβ.ne'
        (by simp only [cagan_money, show n < T by omega, ↓reduceIte])).1 (h n)
      rw [sVar_step (cp22_lamHi h1) hstep.1 hstep.2, ih (by omega), pow_succ]
      ring
  refine ⟨hnew, ?_⟩
  rw [← hold T le_rfl]
  simp only [sVar, add_zero]
  rw [pbarD_sub mb mb', ebarD_sub mb mb']
  ring

/-- The exchange-rate jump of Exercise 2(e):
`J(T) = λ_hi^{−T}(1 + (1/β)/(λ_hi − m₁₁))Δm`. -/
noncomputable def dornJump (θ δ γ β mb mb' : ℝ) (T : ℕ) : ℝ :=
  (dHi θ δ γ β ^ T)⁻¹ * (1 + 1 / β / (dHi θ δ γ β - dM11 θ δ γ β)) * (mb' - mb)

/-- **Exercise 2(e)** (Miao, p. 43): with the increase to `m̄'` announced for date `T` and the
economy at the old steady state (`p₀ = p̄(m̄)`), every bounded path has the exchange rate jump
`e₀ = ē(m̄) + λ_hi^{−T}(1 + (1/β)/(λ_hi − m₁₁))Δm` at the announcement. -/
theorem ex_1_2e_jump (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ} {T : ℕ}
    {e p : ℕ → ℝ} (h : IsDorn2 δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e p)
    (hp0 : p 0 = pbarD α β y rs mb) (hp : BddSeq p) (he : BddSeq e) :
    e 0 = ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  obtain ⟨hnew, hs⟩ := dorn_announce_core hδ hθ hβ h
  have hpT : BddSeq (fun t => p (T + t)) := by obtain ⟨M, hM⟩ := hp; exact ⟨M, fun t => hM _⟩
  have heT : BddSeq (fun t => e (T + t)) := by obtain ⟨M, hM⟩ := he; exact ⟨M, fun t => hM _⟩
  have hz := sHi_zero_of_bdd h1 hnew (bddSeq_sub_const hpT _) (bddSeq_sub_const heT _)
  rw [hz] at hs
  have hgap : 0 < dHi θ δ γ β - dM11 θ δ γ β := by
    linarith [(lamLo_lt_m11 h1 (dorn_hm hδ hθ hβ)).2]
  have hhi : 0 < dHi θ δ γ β := by linarith [(roots22_lt h1).2]
  have hT : dHi θ δ γ β ^ T ≠ 0 := (pow_pos hhi T).ne'
  simp only [sVar, hp0, sub_self, mul_zero, zero_add] at hs
  have key : e 0 - ebarD δ γ φ α β y g ps rs mb = ((1 / β + (dHi θ δ γ β - dM11 θ δ γ β)) *
      (mb' - mb)) / (dHi θ δ γ β ^ T * (dHi θ δ γ β - dM11 θ δ γ β)) := by
    rw [eq_div_iff (mul_ne_zero hT hgap.ne')]
    linear_combination (-1 : ℝ) * hs
  rw [show e 0 = ebarD δ γ φ α β y g ps rs mb + (e 0 - ebarD δ γ φ α β y g ps rs mb) by ring, key]
  simp only [dornJump]
  field_simp
  ring

/-- **Exercise 2(e)** (Miao, p. 43): the path starting at `p₀ = p̄(m̄)`, `e₀ = ē(m̄) + J(T)`
exists, and (under the stability condition) converges to the new steady state, so it is the
unique bounded path. -/
theorem ex_1_2e_exists (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β)
    (hcond : θ * (2 * δ + (2 * γ + δ) / β) < 4) (mb mb' : ℝ) (T : ℕ) :
    Tendsto (fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T)
        (ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T) (pbarD α β y rs mb) t).2)
        atTop (𝓝 (pbarD α β y rs mb')) ∧
      Tendsto (fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T)
        (ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T) (pbarD α β y rs mb) t).1)
        atTop (𝓝 (ebarD δ γ φ α β y g ps rs mb')) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hm := dorn_hm hδ hθ hβ
  have hc : 0 < cp22 (dM11 θ δ γ β) (θ * δ) (1 / β) 1 (-1) := by
    rw [dorn_cp_neg_one hβ.ne']; linarith
  set e0 := ebarD δ γ φ α β y g ps rs mb + dornJump θ δ γ β mb mb' T
  set p := fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e0
    (pbarD α β y rs mb) t).2 with hpdef
  set e := fun t => (dornIter δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e0
    (pbarD α β y rs mb) t).1 with hedef
  have hsol : IsDorn2 δ γ φ θ α β y g ps rs (cagan_money mb mb' T) e p := dornIter_sol _ _ _
  obtain ⟨hnew, hs⟩ := dorn_announce_core hδ hθ hβ hsol
  have hgap : 0 < dHi θ δ γ β - dM11 θ δ γ β := by
    linarith [(lamLo_lt_m11 h1 hm).2]
  have hhi : 0 < dHi θ δ γ β := by linarith [(roots22_lt h1).2]
  have hT : dHi θ δ γ β ^ T ≠ 0 := (pow_pos hhi T).ne'
  have hz : sVar (dM11 θ δ γ β) (1 / β) (dHi θ δ γ β) (fun t => p (T + t) - pbarD α β y rs mb')
      (fun t => e (T + t) - ebarD δ γ φ α β y g ps rs mb') 0 = 0 := by
    rw [hs]
    have hp0 : p 0 = pbarD α β y rs mb := rfl
    have he0 : e 0 = e0 := rfl
    simp only [sVar, hp0, he0, e0, dornJump, sub_self, mul_zero, zero_add, add_sub_cancel_left]
    field_simp
    ring
  have hk := (sHi_zero_iff h1 hm _ _ 0).1 hz
  obtain ⟨hX, hY⟩ := hnew.ext (saddle22 h1 (by positivity) (p (T + 0) - pbarD α β y rs mb'))
    (by simp) (by simpa using hk)
  obtain ⟨t1, t2⟩ := saddle22_tendsto h1 hc (p (T + 0) - pbarD α β y rs mb')
  rw [← hX] at t1
  rw [← hY] at t2
  have t1' := t1.add_const (pbarD α β y rs mb')
  have t2' := t2.add_const (ebarD δ γ φ α β y g ps rs mb')
  simp only [sub_add_cancel, zero_add] at t1' t2'
  constructor
  · rw [← tendsto_add_atTop_iff_nat T]
    exact t1'.congr (fun t => by rw [add_comm])
  · rw [← tendsto_add_atTop_iff_nat T]
    exact t2'.congr (fun t => by rw [add_comm])

/-- **Exercise 2(e)** (Miao, p. 43): for `m̄' > m̄` the exchange rate depreciates on the
announcement (`J(T) > 0`), by less the further away the increase (`J(T + 1) < J(T)`), and for
`T = 0` the jump is the overshooting jump `(1 − k)Δm` of part (d). -/
theorem ex_1_2e_jump_shape (hδ : 0 < δ) (hθ : 0 < θ) (hβ : 0 < β) {mb mb' : ℝ}
    (hm : mb < mb') (T : ℕ) :
    0 < dornJump θ δ γ β mb mb' T ∧ dornJump θ δ γ β mb mb' (T + 1) < dornJump θ δ γ β mb mb' T ∧
      dornJump θ δ γ β mb mb' 0 = (1 - dK θ δ γ β) * (mb' - mb) := by
  have h1 := dorn_h1 (γ := γ) hδ hθ hβ
  have hm12 := dorn_hm hδ hθ hβ
  have hgap : 0 < dHi θ δ γ β - dM11 θ δ γ β := by
    linarith [(lamLo_lt_m11 h1 hm12).2]
  have hhi : 1 < dHi θ δ γ β := (roots22_lt h1).2
  have hΔ : 0 < mb' - mb := by linarith
  have hc : 0 < 1 + 1 / β / (dHi θ δ γ β - dM11 θ δ γ β) := by positivity
  have hpos : ∀ n : ℕ, 0 < (dHi θ δ γ β ^ n)⁻¹ := fun n => inv_pos.2 (pow_pos (by linarith) n)
  refine ⟨mul_pos (mul_pos (hpos T) hc) hΔ, ?_, ?_⟩
  · simp only [dornJump]
    have : (dHi θ δ γ β ^ (T + 1))⁻¹ < (dHi θ δ γ β ^ T)⁻¹ := by
      rw [pow_succ, mul_inv]
      have := hpos T
      have : (dHi θ δ γ β)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hhi
      nlinarith
    have := mul_pos hc hΔ
    nlinarith
  · have hprod : (dLo θ δ γ β - dM11 θ δ γ β) * (dHi θ δ γ β - dM11 θ δ γ β) =
        -(θ * δ * (1 / β)) := by
      have := cp22_factor h1 (dM11 θ δ γ β)
      simp only [cp22] at this
      linarith
    have hm0 : θ * δ ≠ 0 := by positivity
    have hq : 1 / β / (dHi θ δ γ β - dM11 θ δ γ β) = -(dLo θ δ γ β - dM11 θ δ γ β) / (θ * δ) := by
      rw [div_eq_div_iff hgap.ne' hm0]
      linear_combination hprod
    simp only [dornJump, dK, kSaddle, pow_zero, inv_one, one_mul]
    rw [hq]
    ring

end Miao.DifferenceEquations

set_option linter.style.longLine false
#print axioms Miao.DifferenceEquations.IsSolution
#print axioms Miao.DifferenceEquations.IsRegular
#print axioms Miao.DifferenceEquations.EventuallyConst
#print axioms Miao.DifferenceEquations.IsStableSeq
#print axioms Miao.DifferenceEquations.IsSteadyStateOf
#print axioms Miao.DifferenceEquations.IsAsympStable
#print axioms Miao.DifferenceEquations.basin
#print axioms Miao.DifferenceEquations.IsGloballyStable
#print axioms Miao.DifferenceEquations.IsStableMatrix
#print axioms Miao.DifferenceEquations.isGloballyStable_iff_basin
#print axioms Miao.DifferenceEquations.isAsympStable_iff_basin
#print axioms Miao.DifferenceEquations.isStableSeq_iff_bddAbove
#print axioms Miao.DifferenceEquations.IsScalarSol
#print axioms Miao.DifferenceEquations.BddSeq
#print axioms Miao.DifferenceEquations.bddSeq_iff_isStableSeq
#print axioms Miao.DifferenceEquations.bddSeq_of_tendsto
#print axioms Miao.DifferenceEquations.BddSeq.exists_nonneg
#print axioms Miao.DifferenceEquations.geom_eq
#print axioms Miao.DifferenceEquations.abs_pow_mul_tendsto_atTop
#print axioms Miao.DifferenceEquations.pow_mul_tendsto_zero_iff
#print axioms Miao.DifferenceEquations.geom_bdd_iff
#print axioms Miao.DifferenceEquations.pow_mul_tendsto_zero_of_bdd
#print axioms Miao.DifferenceEquations.bddSeq_of_forced
#print axioms Miao.DifferenceEquations.tendsto_zero_of_forced
#print axioms Miao.DifferenceEquations.eq_1_2_steady_state
#print axioms Miao.DifferenceEquations.eq_1_2_no_steady_state_of_b_one
#print axioms Miao.DifferenceEquations.eq_1_3
#print axioms Miao.DifferenceEquations.eq_1_3_globallyStable
#print axioms Miao.DifferenceEquations.eq_1_3_tendsto
#print axioms Miao.DifferenceEquations.eq_1_3_diverges
#print axioms Miao.DifferenceEquations.eq_1_3_bdd_iff
#print axioms Miao.DifferenceEquations.eq_1_4
#print axioms Miao.DifferenceEquations.not_tendsto_neg_one_pow
#print axioms Miao.DifferenceEquations.eq_1_5_counterexample
#print axioms Miao.DifferenceEquations.eq_1_5_tendsto
#print axioms Miao.DifferenceEquations.eq_1_5_bdd
#print axioms Miao.DifferenceEquations.eq_1_5_sub_tendsto
#print axioms Miao.DifferenceEquations.eq_1_5_b_one_formula
#print axioms Miao.DifferenceEquations.eq_1_5_b_one_tendsto_iff
#print axioms Miao.DifferenceEquations.eq_1_5_b_one_limit_sub
#print axioms Miao.DifferenceEquations.eq_1_5_b_neg_one_counterexample
#print axioms Miao.DifferenceEquations.eq_1_5_b_neg_one_unique
#print axioms Miao.DifferenceEquations.eq_1_6
#print axioms Miao.DifferenceEquations.fwdSol
#print axioms Miao.DifferenceEquations.abs_one_div_lt_one
#print axioms Miao.DifferenceEquations.eq_1_8_summable
#print axioms Miao.DifferenceEquations.eq_1_8_isScalarSol
#print axioms Miao.DifferenceEquations.eq_1_8_bdd
#print axioms Miao.DifferenceEquations.eq_1_7_of_bdd
#print axioms Miao.DifferenceEquations.eq_1_8_transversality
#print axioms Miao.DifferenceEquations.eq_1_8_unique_of_transversality
#print axioms Miao.DifferenceEquations.eq_1_8_unique_bdd
#print axioms Miao.DifferenceEquations.eq_1_8
#print axioms Miao.DifferenceEquations.eq_1_9
#print axioms Miao.DifferenceEquations.eq_1_9_every_solution
#print axioms Miao.DifferenceEquations.eq_1_8_others_diverge
#print axioms Miao.DifferenceEquations.eq_1_8_not_summable
#print axioms Miao.DifferenceEquations.eq_1_9_bubble_stable
#print axioms Miao.DifferenceEquations.example_1_1_1_recursion
#print axioms Miao.DifferenceEquations.example_1_1_1_backward
#print axioms Miao.DifferenceEquations.example_1_1_1_tendsto_iff
#print axioms Miao.DifferenceEquations.example_1_1_1_abs_a_lt_one_iff
#print axioms Miao.DifferenceEquations.example_1_1_1_forward
#print axioms Miao.DifferenceEquations.example_1_1_1_forward_limit
#print axioms Miao.DifferenceEquations.example_1_1_1_isScalarSol
#print axioms Miao.DifferenceEquations.example_1_1_1_bubbles
#print axioms Miao.DifferenceEquations.example_1_1_1_unique_bdd
#print axioms Miao.DifferenceEquations.divTax
#print axioms Miao.DifferenceEquations.taxPath
#print axioms Miao.DifferenceEquations.sum_div_pow_eq
#print axioms Miao.DifferenceEquations.example_1_1_2_p0_forward
#print axioms Miao.DifferenceEquations.example_1_1_2_pT
#print axioms Miao.DifferenceEquations.example_1_1_2_p0
#print axioms Miao.DifferenceEquations.example_1_1_2_solves
#print axioms Miao.DifferenceEquations.example_1_1_2_const
#print axioms Miao.DifferenceEquations.example_1_1_2_unique
#print axioms Miao.DifferenceEquations.example_1_1_2_drop
#print axioms Miao.DifferenceEquations.example_1_1_2_decreasing
#print axioms Miao.DifferenceEquations.lagOp
#print axioms Miao.DifferenceEquations.BddZSeq
#print axioms Miao.DifferenceEquations.lagOp_lagOp
#print axioms Miao.DifferenceEquations.lagOp_zero
#print axioms Miao.DifferenceEquations.lagOp_iterate
#print axioms Miao.DifferenceEquations.lagOp_neg_lagOp
#print axioms Miao.DifferenceEquations.lagOp_const
#print axioms Miao.DifferenceEquations.oneSubLag
#print axioms Miao.DifferenceEquations.geomLagSum
#print axioms Miao.DifferenceEquations.geomLagSum2
#print axioms Miao.DifferenceEquations.summable_of_abs_le
#print axioms Miao.DifferenceEquations.abs_tsum_le_of_abs_le
#print axioms Miao.DifferenceEquations.summable_succ_mul_geom
#print axioms Miao.DifferenceEquations.abs_lagOp_le
#print axioms Miao.DifferenceEquations.geomLagSum_summable
#print axioms Miao.DifferenceEquations.geomLagSum2_summable
#print axioms Miao.DifferenceEquations.geomLagSum_bdd
#print axioms Miao.DifferenceEquations.geomLagSum2_bdd
#print axioms Miao.DifferenceEquations.geomLagSum_eq
#print axioms Miao.DifferenceEquations.eq_zero_of_bdd_of_lag
#print axioms Miao.DifferenceEquations.lag_inverse_geom
#print axioms Miao.DifferenceEquations.oneSubLag_geomLagSum2
#print axioms Miao.DifferenceEquations.lag_inverse_geom_sq
#print axioms Miao.DifferenceEquations.lag_scalar_geom
#print axioms Miao.DifferenceEquations.lag_scalar_geom_sq
#print axioms Miao.DifferenceEquations.IsSecondOrderSol
#print axioms Miao.DifferenceEquations.IsHomSol
#print axioms Miao.DifferenceEquations.char_roots_iff
#print axioms Miao.DifferenceEquations.char_roots_exist
#print axioms Miao.DifferenceEquations.eq_1_15
#print axioms Miao.DifferenceEquations.superposition
#print axioms Miao.DifferenceEquations.sub_isHomSol
#print axioms Miao.DifferenceEquations.IsHomSol.ext
#print axioms Miao.DifferenceEquations.hom_factor
#print axioms Miao.DifferenceEquations.sol_factor
#print axioms Miao.DifferenceEquations.eq_1_17
#print axioms Miao.DifferenceEquations.eq_1_17_general
#print axioms Miao.DifferenceEquations.case1_sink
#print axioms Miao.DifferenceEquations.case1_sink_bdd
#print axioms Miao.DifferenceEquations.case1_sink_indeterminate
#print axioms Miao.DifferenceEquations.case1_source
#print axioms Miao.DifferenceEquations.case1_source_not_tendsto
#print axioms Miao.DifferenceEquations.saddlePath
#print axioms Miao.DifferenceEquations.case1_saddle_eq
#print axioms Miao.DifferenceEquations.case1_saddle_isSol
#print axioms Miao.DifferenceEquations.case1_saddle_bdd
#print axioms Miao.DifferenceEquations.case1_saddle_unique
#print axioms Miao.DifferenceEquations.case1_saddle
#print axioms Miao.DifferenceEquations.case2_solution
#print axioms Miao.DifferenceEquations.case2_verification
#print axioms Miao.DifferenceEquations.case2_general
#print axioms Miao.DifferenceEquations.case2_general_counterexample
#print axioms Miao.DifferenceEquations.case2_stable_iff
#print axioms Miao.DifferenceEquations.case3_roots
#print axioms Miao.DifferenceEquations.case3_complex_form
#print axioms Miao.DifferenceEquations.case3_conj_real
#print axioms Miao.DifferenceEquations.case3_real_form
#print axioms Miao.DifferenceEquations.case3_solution
#print axioms Miao.DifferenceEquations.case3_general
#print axioms Miao.DifferenceEquations.case3_damped_form
#print axioms Miao.DifferenceEquations.case3_damped
#print axioms Miao.DifferenceEquations.case3_explosive
#print axioms Miao.DifferenceEquations.eq_1_19
#print axioms Miao.DifferenceEquations.eq_1_19_of_system
#print axioms Miao.DifferenceEquations.tendsto_zero_of_le_rec
#print axioms Miao.DifferenceEquations.tendsto_zero_of_rec
#print axioms Miao.DifferenceEquations.triangular_step
#print axioms Miao.DifferenceEquations.triangular_invariant
#print axioms Miao.DifferenceEquations.triangular_tendsto_iff
#print axioms Miao.DifferenceEquations.mclm
#print axioms Miao.DifferenceEquations.mclm_apply
#print axioms Miao.DifferenceEquations.norm_mulVec_le
#print axioms Miao.DifferenceEquations.norm_mclm_mul_le
#print axioms Miao.DifferenceEquations.tendsto_norm_mclm_pow
#print axioms Miao.DifferenceEquations.summable_of_tendsto_zero
#print axioms Miao.DifferenceEquations.diag_mul_of_upper
#print axioms Miao.DifferenceEquations.upper_inv
#print axioms Miao.DifferenceEquations.diag_inv_of_upper
#print axioms Miao.DifferenceEquations.summable_norm_pow_of_triangular
#print axioms Miao.DifferenceEquations.stableSubspace
#print axioms Miao.DifferenceEquations.unstableSubspace
#print axioms Miao.DifferenceEquations.convSubspace
#print axioms Miao.DifferenceEquations.mem_convSubspace
#print axioms Miao.DifferenceEquations.tendsto_of_mem_maxGenEigenspace
#print axioms Miao.DifferenceEquations.not_tendsto_of_eigen
#print axioms Miao.DifferenceEquations.stable_le_conv
#print axioms Miao.DifferenceEquations.stable_sup_unstable
#print axioms Miao.DifferenceEquations.disjoint_stable_unstable
#print axioms Miao.DifferenceEquations.unstable_invariant
#print axioms Miao.DifferenceEquations.tendsto_iff_mem_stable
#print axioms Miao.DifferenceEquations.stable_eq_top
#print axioms Miao.DifferenceEquations.cplx
#print axioms Miao.DifferenceEquations.cplx_sub
#print axioms Miao.DifferenceEquations.cplx_add
#print axioms Miao.DifferenceEquations.tendsto_cplx_iff
#print axioms Miao.DifferenceEquations.cplxEnd
#print axioms Miao.DifferenceEquations.cplxEnd_pow_cplx
#print axioms Miao.DifferenceEquations.hasEigenvalue_cplxEnd_iff
#print axioms Miao.DifferenceEquations.finrank_biSup_maxGenEigenspace
#print axioms Miao.DifferenceEquations.finrank_stableSubspace
#print axioms Miao.DifferenceEquations.conjV
#print axioms Miao.DifferenceEquations.conjV_conjV
#print axioms Miao.DifferenceEquations.conjV_add
#print axioms Miao.DifferenceEquations.conjV_sub
#print axioms Miao.DifferenceEquations.conjV_smul
#print axioms Miao.DifferenceEquations.conjV_zero
#print axioms Miao.DifferenceEquations.conjV_cplx
#print axioms Miao.DifferenceEquations.eq_cplx_re
#print axioms Miao.DifferenceEquations.cplxEnd_conjV
#print axioms Miao.DifferenceEquations.pow_sub_conjV
#print axioms Miao.DifferenceEquations.conjV_mem_maxGenEigenspace
#print axioms Miao.DifferenceEquations.conjV_mem_biSup
#print axioms Miao.DifferenceEquations.conjV_mem_stable
#print axioms Miao.DifferenceEquations.conjV_mem_unstable
#print axioms Miao.DifferenceEquations.cplxL
#print axioms Miao.DifferenceEquations.stableR
#print axioms Miao.DifferenceEquations.unstableR
#print axioms Miao.DifferenceEquations.mem_stableR
#print axioms Miao.DifferenceEquations.mem_unstableR
#print axioms Miao.DifferenceEquations.mem_stableR_iff
#print axioms Miao.DifferenceEquations.cplx_mulVec
#print axioms Miao.DifferenceEquations.stableR_invariant
#print axioms Miao.DifferenceEquations.unstableR_invariant
#print axioms Miao.DifferenceEquations.isCompl_stableR_unstableR
#print axioms Miao.DifferenceEquations.linearIndependent_cplx
#print axioms Miao.DifferenceEquations.finrank_le_of_cplx
#print axioms Miao.DifferenceEquations.finrank_stableR
#print axioms Miao.DifferenceEquations.unstableR_ker
#print axioms Miao.DifferenceEquations.uniform_bound_of_basis
#print axioms Miao.DifferenceEquations.exists_bound_of_tendsto
#print axioms Miao.DifferenceEquations.mem_maxGen_smul
#print axioms Miao.DifferenceEquations.projS
#print axioms Miao.DifferenceEquations.projU
#print axioms Miao.DifferenceEquations.projS_add_projU
#print axioms Miao.DifferenceEquations.projS_mem
#print axioms Miao.DifferenceEquations.projU_mem
#print axioms Miao.DifferenceEquations.projS_of_mem
#print axioms Miao.DifferenceEquations.projS_of_mem_unstable
#print axioms Miao.DifferenceEquations.projU_of_mem
#print axioms Miao.DifferenceEquations.projU_of_mem_stable
#print axioms Miao.DifferenceEquations.projS_mulVec
#print axioms Miao.DifferenceEquations.projU_mulVec
#print axioms Miao.DifferenceEquations.pow_mulVec_mem_stableR
#print axioms Miao.DifferenceEquations.tendsto_scaled_of_stable
#print axioms Miao.DifferenceEquations.scaled_pow_cplx
#print axioms Miao.DifferenceEquations.stable_bound
#print axioms Miao.DifferenceEquations.isStableMatrix_iff_roots
#print axioms Miao.DifferenceEquations.tendsto_of_isStableMatrix
#print axioms Miao.DifferenceEquations.isStableMatrix_of_tendsto
#print axioms Miao.DifferenceEquations.isStableMatrix_iff_tendsto
#print axioms Miao.DifferenceEquations.HasGeomDecay
#print axioms Miao.DifferenceEquations.hasGeomDecay_of_isStableMatrix
#print axioms Miao.DifferenceEquations.isStableMatrix_inv
#print axioms Miao.DifferenceEquations.footnote_2
#print axioms Miao.DifferenceEquations.isRegular_of_isUnit_det
#print axioms Miao.DifferenceEquations.example_scalar_not_regular
#print axioms Miao.DifferenceEquations.example_scalar_no_solution
#print axioms Miao.DifferenceEquations.remark_nonregular_no_solution
#print axioms Miao.DifferenceEquations.remark_nonregular_counterexample
#print axioms Miao.DifferenceEquations.eq_1_21
#print axioms Miao.DifferenceEquations.eq_1_21_solution
#print axioms Miao.DifferenceEquations.eq_1_21_steadyState
#print axioms Miao.DifferenceEquations.isSteadyStateOf_of_not_mem_range
#print axioms Miao.DifferenceEquations.isStableSeq_iff_exists_le
#print axioms Miao.DifferenceEquations.exists_mulVec_bound
#print axioms Miao.DifferenceEquations.bounded_mulVec
#print axioms Miao.DifferenceEquations.norm_sum_type_le
#print axioms Miao.DifferenceEquations.norm_comp_inl_le
#print axioms Miao.DifferenceEquations.norm_comp_inr_le
#print axioms Miao.DifferenceEquations.backward_sol_eq
#print axioms Miao.DifferenceEquations.bounded_backward
#print axioms Miao.DifferenceEquations.summable_geom_series
#print axioms Miao.DifferenceEquations.mulVec_tsum_rs
#print axioms Miao.DifferenceEquations.tsum_geom_series_succ
#print axioms Miao.DifferenceEquations.eq_zero_of_bounded_orbit
#print axioms Miao.DifferenceEquations.lagSeries
#print axioms Miao.DifferenceEquations.lagSeries_summable
#print axioms Miao.DifferenceEquations.lagSeries_rec
#print axioms Miao.DifferenceEquations.lagSeries_unique
#print axioms Miao.DifferenceEquations.lag_matrix_formula
#print axioms Miao.DifferenceEquations.IsRealBlockSplit
#print axioms Miao.DifferenceEquations.blockDiag_mulVec_inl
#print axioms Miao.DifferenceEquations.blockDiag_mulVec_inr
#print axioms Miao.DifferenceEquations.mulVec_comp_inl
#print axioms Miao.DifferenceEquations.mulVec_comp_inr
#print axioms Miao.DifferenceEquations.IsRealBlockSplit.mul_R
#print axioms Miao.DifferenceEquations.card_add_card_of_inv
#print axioms Miao.DifferenceEquations.IsRealBlockSplit.isUnit_one_sub
#print axioms Miao.DifferenceEquations.eigen_transport
#print axioms Miao.DifferenceEquations.exists_real_block_split
#print axioms Miao.DifferenceEquations.eq_1_22
#print axioms Miao.DifferenceEquations.exists_sol_rec
#print axioms Miao.DifferenceEquations.sol_rec_unique
#print axioms Miao.DifferenceEquations.exists_unique_solution
#print axioms Miao.DifferenceEquations.eq_1_24
#print axioms Miao.DifferenceEquations.eq_1_25
#print axioms Miao.DifferenceEquations.isUnit_sub_det
#print axioms Miao.DifferenceEquations.xbar_eq
#print axioms Miao.DifferenceEquations.theorem_1_4_1
#print axioms Miao.DifferenceEquations.forwardU
#print axioms Miao.DifferenceEquations.forwardU_rec
#print axioms Miao.DifferenceEquations.forwardU_bounded
#print axioms Miao.DifferenceEquations.forwardU_unique
#print axioms Miao.DifferenceEquations.split_rec_inl
#print axioms Miao.DifferenceEquations.split_rec_inr
#print axioms Miao.DifferenceEquations.bounded_of_split
#print axioms Miao.DifferenceEquations.eq_1_29
#print axioms Miao.DifferenceEquations.eq_1_30
#print axioms Miao.DifferenceEquations.eq_1_31
#print axioms Miao.DifferenceEquations.eq_1_32
#print axioms Miao.DifferenceEquations.bk_exists
#print axioms Miao.DifferenceEquations.bk_unique
#print axioms Miao.DifferenceEquations.theorem_1_4_2
#print axioms Miao.DifferenceEquations.blocks_of_inv
#print axioms Miao.DifferenceEquations.rks_inv
#print axioms Miao.DifferenceEquations.puy_inv_of_rks
#print axioms Miao.DifferenceEquations.bk_order_iff
#print axioms Miao.DifferenceEquations.eq_1_33
#print axioms Miao.DifferenceEquations.corollary_1_4_1
#print axioms Miao.DifferenceEquations.eq_1_34
#print axioms Miao.DifferenceEquations.stable_initial_iff
#print axioms Miao.DifferenceEquations.stableArm
#print axioms Miao.DifferenceEquations.mem_stableArm
#print axioms Miao.DifferenceEquations.stableArm_iff
#print axioms Miao.DifferenceEquations.finrank_stableArm
#print axioms Miao.DifferenceEquations.stable_initial_translate
#print axioms Miao.DifferenceEquations.remark_unit_root
#print axioms Miao.DifferenceEquations.homog_stable_mem_range
#print axioms Miao.DifferenceEquations.theorem_1_4_3_gt
#print axioms Miao.DifferenceEquations.theorem_1_4_3_lt
#print axioms Miao.DifferenceEquations.theorem_1_4_3_lt_exists
#print axioms Miao.DifferenceEquations.theorem_1_4_3_printed_lt
#print axioms Miao.DifferenceEquations.hasEigenvalue_smul_one
#print axioms Miao.DifferenceEquations.theorem_1_4_3_printed_gt_false
#print axioms Miao.DifferenceEquations.theorem_1_4_3_lt_counterexample
#print axioms Miao.DifferenceEquations.IsGenEigenvector
#print axioms Miao.DifferenceEquations.IsGenEigenvalue
#print axioms Miao.DifferenceEquations.genEigenvalues
#print axioms Miao.DifferenceEquations.isGenEigenvalue_iff_det
#print axioms Miao.DifferenceEquations.det_ne_zero_of_unitary
#print axioms Miao.DifferenceEquations.conj_lincomb
#print axioms Miao.DifferenceEquations.det_conj_lincomb
#print axioms Miao.DifferenceEquations.upper_lincomb
#print axioms Miao.DifferenceEquations.det_upper_lincomb
#print axioms Miao.DifferenceEquations.diag_ne_zero_of_regular
#print axioms Miao.DifferenceEquations.genEigenvalues_eq_diag
#print axioms Miao.DifferenceEquations.exists_eigenPair
#print axioms Miao.DifferenceEquations.exists_unitary_col
#print axioms Miao.DifferenceEquations.deflate
#print axioms Miao.DifferenceEquations.det_of_col_zero
#print axioms Miao.DifferenceEquations.blockOne
#print axioms Miao.DifferenceEquations.blockOne_mul_zero
#print axioms Miao.DifferenceEquations.blockOne_mul_succ
#print axioms Miao.DifferenceEquations.mul_blockOne_zero
#print axioms Miao.DifferenceEquations.mul_blockOne_succ
#print axioms Miao.DifferenceEquations.blockOne_mul_blockOne
#print axioms Miao.DifferenceEquations.star_blockOne
#print axioms Miao.DifferenceEquations.blockOne_one
#print axioms Miao.DifferenceEquations.blockOne_mem
#print axioms Miao.DifferenceEquations.assemble_apply
#print axioms Miao.DifferenceEquations.assemble_upper
#print axioms Miao.DifferenceEquations.proportional_of_cross
#print axioms Miao.DifferenceEquations.ScaleInvariant
#print axioms Miao.DifferenceEquations.exists_qz_ordered
#print axioms Miao.DifferenceEquations.theorem_1_4_4
#print axioms Miao.DifferenceEquations.scaleInvariant_stable
#print axioms Miao.DifferenceEquations.theorem_1_4_4_stable
#print axioms Miao.DifferenceEquations.norm_mulVec_le_sum
#print axioms Miao.DifferenceEquations.isStableSeq_of_le
#print axioms Miao.DifferenceEquations.IsStableSeq.bound
#print axioms Miao.DifferenceEquations.IsStableSeq.mulVec
#print axioms Miao.DifferenceEquations.fwdSum
#print axioms Miao.DifferenceEquations.summable_fwd
#print axioms Miao.DifferenceEquations.norm_fwdSum_le
#print axioms Miao.DifferenceEquations.fwdSum_rec
#print axioms Miao.DifferenceEquations.eq_fwdSum
#print axioms Miao.DifferenceEquations.isStableSeq_of_rec
#print axioms Miao.DifferenceEquations.IsStableSeq.add
#print axioms Miao.DifferenceEquations.IsStableSeq.sub
#print axioms Miao.DifferenceEquations.IsStableSeq.shift
#print axioms Miao.DifferenceEquations.norm_comp_le
#print axioms Miao.DifferenceEquations.IsStableSeq.comp
#print axioms Miao.DifferenceEquations.isStableSeq_append
#print axioms Miao.DifferenceEquations.upper_castAdd
#print axioms Miao.DifferenceEquations.upper_natAdd
#print axioms Miao.DifferenceEquations.mulVec_castAdd
#print axioms Miao.DifferenceEquations.mulVec_natAdd
#print axioms Miao.DifferenceEquations.eq_1_36
#print axioms Miao.DifferenceEquations.solve_fwd
#print axioms Miao.DifferenceEquations.eq_1_38
#print axioms Miao.DifferenceEquations.det_S11_ne_zero
#print axioms Miao.DifferenceEquations.det_T22_ne_zero
#print axioms Miao.DifferenceEquations.summable_Ms
#print axioms Miao.DifferenceEquations.summable_Mu
#print axioms Miao.DifferenceEquations.klein_core
#print axioms Miao.DifferenceEquations.klein_homog
#print axioms Miao.DifferenceEquations.eq_1_37
#print axioms Miao.DifferenceEquations.eq_1_39_40
#print axioms Miao.DifferenceEquations.isSolution_iff_transformed
#print axioms Miao.DifferenceEquations.diag_off_circle
#print axioms Miao.DifferenceEquations.theorem_1_4_5
#print axioms Miao.DifferenceEquations.det_sub_ne_zero
#print axioms Miao.DifferenceEquations.corollary_1_4_1_singular
#print axioms Miao.DifferenceEquations.map_ofReal_mulVec
#print axioms Miao.DifferenceEquations.norm_ofReal_vec
#print axioms Miao.DifferenceEquations.isSolution_ofReal_iff
#print axioms Miao.DifferenceEquations.theorem_1_4_5_real
#print axioms Miao.DifferenceEquations.eq_s0
#print axioms Miao.DifferenceEquations.remark_augmented
#print axioms Miao.DifferenceEquations.remark_u_eq_zero
#print axioms Miao.DifferenceEquations.eq_1_37_printed_false
#print axioms Miao.DifferenceEquations.caganA
#print axioms Miao.DifferenceEquations.caganB
#print axioms Miao.DifferenceEquations.caganC
#print axioms Miao.DifferenceEquations.example_cagan_iff
#print axioms Miao.DifferenceEquations.example_cagan_det
#print axioms Miao.DifferenceEquations.example_cagan_regular
#print axioms Miao.DifferenceEquations.example_cagan_genEigenvalues
#print axioms Miao.DifferenceEquations.example_cagan_genEigenvalues_zero
#print axioms Miao.DifferenceEquations.IsSol22
#print axioms Miao.DifferenceEquations.cp22
#print axioms Miao.DifferenceEquations.disc22
#print axioms Miao.DifferenceEquations.lamLo
#print axioms Miao.DifferenceEquations.lamHi
#print axioms Miao.DifferenceEquations.sVar
#print axioms Miao.DifferenceEquations.disc22_pos
#print axioms Miao.DifferenceEquations.cp22_factor
#print axioms Miao.DifferenceEquations.cp22_lamLo
#print axioms Miao.DifferenceEquations.cp22_lamHi
#print axioms Miao.DifferenceEquations.lamLo_lt_lamHi
#print axioms Miao.DifferenceEquations.roots22_lt
#print axioms Miao.DifferenceEquations.lamLo_gt_neg_one_iff
#print axioms Miao.DifferenceEquations.abs_lamLo_lt_one_iff
#print axioms Miao.DifferenceEquations.lamLo_lt_m11
#print axioms Miao.DifferenceEquations.sVar_step
#print axioms Miao.DifferenceEquations.sVar_succ
#print axioms Miao.DifferenceEquations.recover22
#print axioms Miao.DifferenceEquations.IsSol22.ext
#print axioms Miao.DifferenceEquations.bddSeq_lin
#print axioms Miao.DifferenceEquations.sHi_zero_of_bdd
#print axioms Miao.DifferenceEquations.kSaddle
#print axioms Miao.DifferenceEquations.sHi_zero_iff
#print axioms Miao.DifferenceEquations.saddle22
#print axioms Miao.DifferenceEquations.saddle22_tendsto
#print axioms Miao.DifferenceEquations.saddle22_unique
#print axioms Miao.DifferenceEquations.saddle22_unbounded
#print axioms Miao.DifferenceEquations.sVar_tendsto
#print axioms Miao.DifferenceEquations.saddle22_iff
#print axioms Miao.DifferenceEquations.saddle22_only_zero
#print axioms Miao.DifferenceEquations.IsPhaseSol
#print axioms Miao.DifferenceEquations.phaseIter
#print axioms Miao.DifferenceEquations.phaseIter_sol
#print axioms Miao.DifferenceEquations.phase_tilde
#print axioms Miao.DifferenceEquations.phase_delta
#print axioms Miao.DifferenceEquations.phase_isocline_x
#print axioms Miao.DifferenceEquations.phase_isocline_y
#print axioms Miao.DifferenceEquations.phase_steady_state
#print axioms Miao.DifferenceEquations.bddSeq_sub_const
#print axioms Miao.DifferenceEquations.phase_dev
#print axioms Miao.DifferenceEquations.phase_cp_one
#print axioms Miao.DifferenceEquations.phase_cp_neg_one
#print axioms Miao.DifferenceEquations.phase_roots
#print axioms Miao.DifferenceEquations.phase_lamLo_iff
#print axioms Miao.DifferenceEquations.phase_saddle
#print axioms Miao.DifferenceEquations.phase_saddle_slope
#print axioms Miao.DifferenceEquations.phase_saddle_iff
#print axioms Miao.DifferenceEquations.phase_counterexample
#print axioms Miao.DifferenceEquations.example_1_6_1_steady
#print axioms Miao.DifferenceEquations.example_1_6_1_linearization
#print axioms Miao.DifferenceEquations.vec2_eq_iff
#print axioms Miao.DifferenceEquations.mulVec22
#print axioms Miao.DifferenceEquations.example_1_6_1_matrix
#print axioms Miao.DifferenceEquations.example_1_6_1_reduced
#print axioms Miao.DifferenceEquations.example_1_6_1_trace_det
#print axioms Miao.DifferenceEquations.example_1_6_1_roots
#print axioms Miao.DifferenceEquations.example_1_6_1_saddle
#print axioms Miao.DifferenceEquations.definition_1_6_1
#print axioms Miao.DifferenceEquations.definition_1_6_1_cycle
#print axioms Miao.DifferenceEquations.logistic
#print axioms Miao.DifferenceEquations.logistic_two
#print axioms Miao.DifferenceEquations.logistic_fixed_iff
#print axioms Miao.DifferenceEquations.logistic_two_fixed_iff
#print axioms Miao.DifferenceEquations.logistic_two_cycle
#print axioms Miao.DifferenceEquations.logistic_two_cycle_decimals
#print axioms Miao.DifferenceEquations.IsCagan
#print axioms Miao.DifferenceEquations.cagan_isScalarSol
#print axioms Miao.DifferenceEquations.cagan_b_gt_one
#print axioms Miao.DifferenceEquations.ex_1_1a
#print axioms Miao.DifferenceEquations.ex_1_1a_forward
#print axioms Miao.DifferenceEquations.ex_1_1a_rho_one_bdd_iff
#print axioms Miao.DifferenceEquations.ex_1_1a_rho_one
#print axioms Miao.DifferenceEquations.cagan_money
#print axioms Miao.DifferenceEquations.cagan_path
#print axioms Miao.DifferenceEquations.ex_1_1b_solves
#print axioms Miao.DifferenceEquations.cagan_path_const
#print axioms Miao.DifferenceEquations.ex_1_1b_unique
#print axioms Miao.DifferenceEquations.ex_1_1b_shape
#print axioms Miao.DifferenceEquations.IsDornbusch
#print axioms Miao.DifferenceEquations.IsDorn2
#print axioms Miao.DifferenceEquations.pbarD
#print axioms Miao.DifferenceEquations.ebarD
#print axioms Miao.DifferenceEquations.dM11
#print axioms Miao.DifferenceEquations.dLo
#print axioms Miao.DifferenceEquations.dHi
#print axioms Miao.DifferenceEquations.dK
#print axioms Miao.DifferenceEquations.dornIter
#print axioms Miao.DifferenceEquations.dornIter_sol
#print axioms Miao.DifferenceEquations.ex_1_2_reduce
#print axioms Miao.DifferenceEquations.ex_1_2a
#print axioms Miao.DifferenceEquations.ex_1_2_dev_step
#print axioms Miao.DifferenceEquations.ex_1_2_dev
#print axioms Miao.DifferenceEquations.dorn_cp_one
#print axioms Miao.DifferenceEquations.dorn_cp_neg_one
#print axioms Miao.DifferenceEquations.dorn_h1
#print axioms Miao.DifferenceEquations.dorn_hm
#print axioms Miao.DifferenceEquations.dorn_tendsto
#print axioms Miao.DifferenceEquations.ex_1_2b_iff
#print axioms Miao.DifferenceEquations.ex_1_2b_unique
#print axioms Miao.DifferenceEquations.ex_1_2b_counterexample
#print axioms Miao.DifferenceEquations.ex_1_2c
#print axioms Miao.DifferenceEquations.pbarD_sub
#print axioms Miao.DifferenceEquations.ebarD_sub
#print axioms Miao.DifferenceEquations.dK_neg
#print axioms Miao.DifferenceEquations.ex_1_2d_path
#print axioms Miao.DifferenceEquations.ex_1_2d_unique
#print axioms Miao.DifferenceEquations.ex_1_2d_overshoot
#print axioms Miao.DifferenceEquations.ex_1_2d_monotone
#print axioms Miao.DifferenceEquations.dorn_announce_core
#print axioms Miao.DifferenceEquations.dornJump
#print axioms Miao.DifferenceEquations.ex_1_2e_jump
#print axioms Miao.DifferenceEquations.ex_1_2e_exists
#print axioms Miao.DifferenceEquations.ex_1_2e_jump_shape
