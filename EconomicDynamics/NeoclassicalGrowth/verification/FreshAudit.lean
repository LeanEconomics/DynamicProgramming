import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Basic.Real.Pointwise
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Definitions of Chapter 1

Copied from `EconomicDynamics/RationalExpectations` (module `DeterministicBasics`), namespace
renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Upper triangular matrices and geometric decay

Copied from `EconomicDynamics/RationalExpectations` (module `Triangular`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stable and unstable subspaces

Copied from `EconomicDynamics/RationalExpectations` (module `Spectral`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The real stable and unstable subspaces of a real matrix

Copied from `EconomicDynamics/RationalExpectations` (module `RealSplitting`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stable estimate

Copied from `EconomicDynamics/RationalExpectations` (module `Dichotomy`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# First-order linear systems: regularity, steady state, stable matrices

Copied from `EconomicDynamics/RationalExpectations` (module `LinearSystems`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A real block diagonalisation `W = P⁻¹ diag(J_s, J_u) P`

Copied from `EconomicDynamics/RationalExpectations` (module `BlockSplit`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonsingular systems: Theorems 1.4.1 and 1.4.2, Corollary 1.4.1

Copied from `EconomicDynamics/RationalExpectations` (module `Nonsingular`), namespace renamed.

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditional expectations and linear rational expectations systems

Copied from `EconomicDynamics/RationalExpectations` (module `Basics`), namespace renamed.

Miao, Chapter 2, pp. 45, 52–53, 55. The chapter fixes a probability space `(Ω, F, Pr)` and a
filtration `{F_t}`, and writes `E_t` for the conditional expectation given `F_t`. Every linear
solution method of the chapter uses only three properties of `E_t`: it is linear, it does not
increase the `L¹` norm, and it satisfies the law of iterated expectations. Those properties are
collected here as a `CondExpSystem` on a normed space `V` of scalar random variables; the
conditional expectations of `L¹(Ω, F, Pr)` given a filtration form one (`condExpSystemL1`, in
`CondExpL1`). A vector random variable is a family `ι → V`, so `max_j E|x_j|`, the norm of
Definition 2.3.1, is `maxⱼ ‖xⱼ‖`.

* `CondExpSystem 𝕜 V`: continuous linear maps `E_t` with `‖E_t‖ ≤ 1` and
  `E_s ∘ E_t = E_t ∘ E_s = E_s` for `s ≤ t`.
* `IsAdaptedV E x`: `E_t x_t = x_t` for every `t` (adapted to `{F_t}`).
* `IsStableProc x` (Definition 2.3.1): `‖x_t j‖ < M` for all `t`, `j`.
* `matAct M x`: a matrix acting on a vector of random variables.
* `IsRESolution E A B C z x` (2.11): `A E_t x_{t+1} = Bx_t + Cz_t`.
* `IsPredeterminedBK E k` (Blanchard–Kahn, p. 53): `E_t k_{t+1} = k_{t+1}`.
-/

namespace Miao.NeoclassicalGrowth

/-- A family of conditional expectation operators `E_t` on a normed space `V` of random
variables: linear, contractive, with the law of iterated expectations
`E_s E_t = E_t E_s = E_s` for `s ≤ t` (Miao, p. 45). -/
structure CondExpSystem (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] where
  /-- `E_t`, the conditional expectation given `F_t`. -/
  E : ℕ → V →L[𝕜] V
  /-- `‖E_t X‖ ≤ ‖X‖`. -/
  norm_le : ∀ t, ‖E t‖ ≤ 1
  /-- `E_s E_t = E_s` for `s ≤ t`. -/
  tower_le : ∀ s t, s ≤ t → (E s).comp (E t) = E s
  /-- `E_t E_s = E_s` for `s ≤ t`. -/
  tower_ge : ∀ s t, s ≤ t → (E t).comp (E s) = E s

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

namespace CondExpSystem

variable (E : CondExpSystem 𝕜 V)

theorem tower_le_apply {s t : ℕ} (h : s ≤ t) (X : V) : E.E s (E.E t X) = E.E s X := by
  simpa using congrArg (fun L => L X) (E.tower_le s t h)

theorem tower_ge_apply {s t : ℕ} (h : s ≤ t) (X : V) : E.E t (E.E s X) = E.E s X := by
  simpa using congrArg (fun L => L X) (E.tower_ge s t h)

theorem idem (t : ℕ) (X : V) : E.E t (E.E t X) = E.E t X :=
  E.tower_le_apply le_rfl X

theorem norm_apply_le (t : ℕ) (X : V) : ‖E.E t X‖ ≤ ‖X‖ := by
  calc ‖E.E t X‖ ≤ ‖E.E t‖ * ‖X‖ := (E.E t).le_opNorm X
    _ ≤ 1 * ‖X‖ := by gcongr; exact E.norm_le t
    _ = ‖X‖ := one_mul _

end CondExpSystem

/-- `x` is adapted: `E_t x_t = x_t` for every `t` and component (Miao, p. 45). -/
def IsAdaptedV {ι : Type*} (E : CondExpSystem 𝕜 V) (x : ℕ → ι → V) : Prop :=
  ∀ t i, E.E t (x t i) = x t i

/-- **Definition 2.3.1** (Miao, p. 52): `{X_t}` is stable if `max_j E|X_{t,j}| < M` for all `t`,
for some `M > 0`. With `V = L¹`, `‖X_{t,j}‖ = E|X_{t,j}|`. -/
def IsStableProc {ι : Type*} (x : ℕ → ι → V) : Prop :=
  ∃ M, 0 < M ∧ ∀ t i, ‖x t i‖ < M

/-- A matrix acting on a vector of random variables: `(Mx)ᵢ = ∑ⱼ Mᵢⱼ xⱼ`. -/
def matAct {ι κ : Type*} [Fintype κ] (M : Matrix ι κ 𝕜) (x : κ → V) : ι → V :=
  fun i => ∑ j, M i j • x j

/-- `E_t` applied to each component. -/
def Evec {ι : Type*} (E : CondExpSystem 𝕜 V) (t : ℕ) (x : ι → V) : ι → V :=
  fun i => E.E t (x i)

/-- `x` solves the linear rational expectations system `A E_t x_{t+1} = Bx_t + Cz_t`
(Miao, (2.11), p. 52). -/
def IsRESolution {n m : Type*} [Fintype n] [Fintype m] (E : CondExpSystem 𝕜 V)
    (A B : Matrix n n 𝕜) (C : Matrix n m 𝕜) (z : ℕ → m → V) (x : ℕ → n → V) : Prop :=
  ∀ t, matAct A (Evec E t (x (t + 1))) = matAct B (x t) + matAct C (z t)

/-- Blanchard and Kahn's predetermined process (Miao, p. 53): `X_{t+1}` is `F_t`-measurable,
`E_t X_{t+1} = X_{t+1}`. -/
def IsPredeterminedBK {ι : Type*} (E : CondExpSystem 𝕜 V) (k : ℕ → ι → V) : Prop :=
  ∀ t i, E.E t (k (t + 1) i) = k (t + 1) i

theorem Evec_matAct {ι κ : Type*} [Fintype κ] (E : CondExpSystem 𝕜 V) (t : ℕ)
    (M : Matrix ι κ 𝕜) (x : κ → V) : Evec E t (matAct M x) = matAct M (Evec E t x) := by
  funext i
  simp [Evec, matAct, map_sum, map_smul]

theorem matAct_add {ι κ : Type*} [Fintype κ] (M : Matrix ι κ 𝕜) (x y : κ → V) :
    matAct M (x + y) = matAct M x + matAct M y := by
  funext i
  simp [matAct, smul_add, Finset.sum_add_distrib]

theorem matAct_mul {ι κ ρ : Type*} [Fintype κ] [Fintype ρ] (M : Matrix ι κ 𝕜)
    (N : Matrix κ ρ 𝕜) (x : ρ → V) : matAct M (matAct N x) = matAct (M * N) x := by
  funext i
  simp only [matAct, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem matAct_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → V) :
    matAct (1 : Matrix ι ι 𝕜) x = x := by
  funext i
  simp [matAct, Matrix.one_apply]

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stable processes and the forward solution (2.12)

Copied from `EconomicDynamics/RationalExpectations` (module `BKStable`), namespace renamed.

Miao, §2.3, pp. 52–54. The system (2.11) `AE_tx_{t+1} = Bx_t + Cz_t` is `IsRESolution`
(Basics); the regularity Assumption 1.4.1 that the book maintains is automatic once `A` is
nonsingular, which is the Blanchard–Kahn case treated here (`isRegular_of_isUnit_det`).
Processes are vectors `ι → V` of elements of a normed space `V` carrying a `CondExpSystem`;
their norm is the max norm `maxⱼ ‖xⱼ‖` of Definition 2.3.1.

* Tools: matrices acting on `ι → V` (`matAct`) are linear, continuous and commute with
  convergent sums (`bkS_matAct_hasSum`); a bound `‖Nv‖ ≤ c‖v‖` on real vectors gives the same
  bound on random vectors (`bkS_norm_matAct_le`), so geometric decay `HasGeomDecay` transfers
  (`bkS_geom_decay`).
* **Definition 2.3.1**: stable processes are the bounded ones (`bkS_isStableProc_iff`); they
  stay stable under `E_t`, at any dates (`bkS_stable_Evec`), under shifts, matrices and sums.
* Summability: for a stable `z` and `M` with geometric decay, `∑ⱼ MʲE_tz_{t+j}` converges, with
  the bound `KC/(1 − a)` (`bkS_summable_geom`).
* **The forward solution (2.12)**: `bkS_fwd`, in the printed form
  `u_t = −∑ⱼ J_u^{−j−1}C_u*E_tz_{t+j}` (`eq_2_12`; the printed formula is right). It is adapted,
  bounded, solves `E_tu_{t+1} = J_uu_t + c_t` (`bkS_fwd_rec`), and is the only bounded adapted
  solution (`bkS_fwd_unique`): the difference `e` of two solutions satisfies
  `e_t = J_u^{−k}E_te_{t+k}` for every `k` (law of iterated expectations), and
  `‖J_u^{−k}‖ → 0`, `‖E_t‖ ≤ 1`.
* **Jump-only systems** (`bkS_jump_unique`): if `W` is invertible and `W⁻¹` decays
  geometrically, `E_tx_{t+1} = Wx_t + c_t` has exactly one stable adapted solution,
  `x_t = −∑ⱼ W^{−j−1}E_tc_{t+j}`.
* (2.11) with `A` nonsingular is `E_tx_{t+1} = Wx_t + A⁻¹Cz_t`, `W = A⁻¹B` (`eq_2_11_iff`).

Departure: the book requires solutions (and `z`) to be adapted without saying so in (2.11);
here adaptedness is an explicit hypothesis or conclusion (`IsAdaptedV`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Matrices acting on random vectors -/

theorem bkS_matAct_sub {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x y : κ → V) :
    matAct M (x - y) = matAct M x - matAct M y := by
  funext i
  simp [matAct, smul_sub, Finset.sum_sub_distrib]

theorem bkS_matAct_neg {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → V) :
    matAct M (-x) = -matAct M x := by
  funext i
  simp [matAct, Finset.sum_neg_distrib]

theorem bkS_matAct_zero {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) :
    matAct M (0 : κ → V) = 0 := by
  funext i
  simp [matAct]

theorem bkS_matAct_zero_left {ι κ : Type*} [Fintype κ] (x : κ → V) :
    matAct (0 : Matrix ι κ ℝ) x = 0 := by
  funext i
  simp [matAct]

theorem bkS_matAct_smul {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (c : ℝ) (x : κ → V) :
    matAct M (c • x) = c • matAct M x := by
  funext i
  simp [matAct, Finset.smul_sum, smul_comm c]

theorem bkS_matAct_sum {ι κ α : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (s : Finset α)
    (f : α → κ → V) : matAct M (∑ a ∈ s, f a) = ∑ a ∈ s, matAct M (f a) := by
  funext i
  simp only [matAct, Finset.sum_apply, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem bkS_matAct_add_left {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℝ) (x : κ → V) :
    matAct (M + N) x = matAct M x + matAct N x := by
  funext i
  simp [matAct, add_smul, Finset.sum_add_distrib]

theorem bkS_matAct_sub_left {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℝ) (x : κ → V) :
    matAct (M - N) x = matAct M x - matAct N x := by
  funext i
  simp [matAct, sub_smul, Finset.sum_sub_distrib]

theorem bkS_matAct_pow_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (k : ℕ)
    (x : ι → V) : matAct (M ^ (k + 1)) x = matAct M (matAct (M ^ k) x) := by
  rw [matAct_mul, pow_succ']

/-- `matAct M` as a continuous linear map. -/
noncomputable def bkS_matCLM {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) :
    (κ → V) →L[ℝ] (ι → V) :=
  ContinuousLinearMap.pi fun i => ∑ j, M i j • ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : κ => V) j

theorem bkS_matCLM_apply {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → V) :
    bkS_matCLM M x = matAct M x := by
  funext i
  simp [bkS_matCLM, matAct]

/-- A matrix commutes with convergent sums of random vectors. -/
theorem bkS_matAct_hasSum {ι κ α : Type*} [Fintype κ] (M : Matrix ι κ ℝ) {f : α → κ → V}
    {s : κ → V} (h : HasSum f s) : HasSum (fun j => matAct M (f j)) (matAct M s) := by
  simpa [bkS_matCLM_apply] using (bkS_matCLM M).hasSum h

/-- `matAct` on real vectors is `*ᵥ`. -/
theorem bkS_matAct_real {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (x : κ → ℝ) :
    matAct M x = M *ᵥ x := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

/-- A bound `‖Nv‖ ≤ c‖v‖` on real vectors gives `‖Nx‖ ≤ c‖x‖` on random vectors: the row sums
`∑ⱼ |Nᵢⱼ|` are values `(Ns)ᵢ` at sign vectors `s`. -/
theorem bkS_norm_matAct_le {ι κ : Type*} [Fintype ι] [Fintype κ] (N : Matrix ι κ ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hN : ∀ v : κ → ℝ, ‖N *ᵥ v‖ ≤ c * ‖v‖) (x : κ → V) :
    ‖matAct N x‖ ≤ c * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).2 fun i => ?_
  set s : κ → ℝ := fun j => if 0 ≤ N i j then 1 else -1
  have hs : ‖s‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
    simp only [s]
    split_ifs <;> simp
  have hrow : ∑ j, |N i j| ≤ c := by
    have h1 : ∑ j, |N i j| = (N *ᵥ s) i := by
      simp only [Matrix.mulVec, dotProduct, s]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h
      · rw [abs_of_nonneg h, mul_one]
      · rw [abs_of_neg (not_le.1 h), mul_neg_one]
    rw [h1]
    calc (N *ᵥ s) i ≤ |(N *ᵥ s) i| := le_abs_self _
      _ = ‖(N *ᵥ s) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖N *ᵥ s‖ := norm_le_pi_norm _ i
      _ ≤ c * ‖s‖ := hN s
      _ ≤ c * 1 := by gcongr
      _ = c := mul_one c
  calc ‖matAct N x i‖ = ‖∑ j, N i j • x j‖ := rfl
    _ ≤ ∑ j, ‖N i j • x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |N i j| * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j, |N i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ c * ‖x‖ := by gcongr

/-- Every matrix is a bounded operator on random vectors. -/
theorem bkS_matAct_bound {ι κ : Type*} [Fintype ι] [Fintype κ] (N : Matrix ι κ ℝ) :
    ∃ c, 0 ≤ c ∧ ∀ x : κ → V, ‖matAct N x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_mulVec_bound N
  exact ⟨c, hc0, bkS_norm_matAct_le N hc0 hc⟩

/-- Geometric decay transfers to random vectors: `‖Mᵏx‖ ≤ Kaᵏ‖x‖`. -/
theorem bkS_geom_decay {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} {K a : ℝ}
    (hM : HasGeomDecay M K a) (k : ℕ) (x : ι → V) :
    ‖matAct (M ^ k) x‖ ≤ K * a ^ k * ‖x‖ :=
  bkS_norm_matAct_le _ (mul_nonneg hM.2.2.1 (pow_nonneg hM.1 k)) (hM.2.2.2 k) x

/-! ### Conditional expectations of random vectors -/

/-- `E_t` on random vectors as a continuous linear map. -/
noncomputable def bkS_ECLM (E : CondExpSystem ℝ V) (ι : Type*) (t : ℕ) :
    (ι → V) →L[ℝ] (ι → V) :=
  ContinuousLinearMap.pi fun i => (E.E t).comp (ContinuousLinearMap.proj i)

theorem bkS_ECLM_apply (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x : ι → V) :
    bkS_ECLM E ι t x = Evec E t x := by
  funext i
  simp [bkS_ECLM, Evec]

theorem bkS_Evec_hasSum (E : CondExpSystem ℝ V) {ι α : Type*} (t : ℕ) {f : α → ι → V}
    {s : ι → V} (h : HasSum f s) : HasSum (fun j => Evec E t (f j)) (Evec E t s) := by
  simpa [bkS_ECLM_apply] using (bkS_ECLM E ι t).hasSum h

theorem bkS_Evec_add (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x y : ι → V) :
    Evec E t (x + y) = Evec E t x + Evec E t y := by
  funext i
  simp [Evec]

theorem bkS_Evec_sub (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x y : ι → V) :
    Evec E t (x - y) = Evec E t x - Evec E t y := by
  funext i
  simp [Evec]

theorem bkS_Evec_neg (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x : ι → V) :
    Evec E t (-x) = -Evec E t x := by
  funext i
  simp [Evec]

theorem bkS_Evec_zero (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) :
    Evec E t (0 : ι → V) = 0 := by
  funext i
  simp [Evec]

theorem bkS_Evec_smul (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (c : ℝ) (x : ι → V) :
    Evec E t (c • x) = c • Evec E t x := by
  funext i
  simp [Evec]

theorem bkS_Evec_sumElim (E : CondExpSystem ℝ V) {κ υ : Type*} (t : ℕ) (a : κ → V)
    (b : υ → V) : Evec E t (Sum.elim a b) = Sum.elim (Evec E t a) (Evec E t b) := by
  funext i
  rcases i with i | i <;> rfl

/-- The law of iterated expectations on random vectors: `E_sE_t = E_s` for `s ≤ t`. -/
theorem bkS_Evec_tower_le (E : CondExpSystem ℝ V) {ι : Type*} {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E s (Evec E t x) = Evec E s x := by
  funext i
  exact E.tower_le_apply h _

/-- `E_tE_s = E_s` for `s ≤ t`. -/
theorem bkS_Evec_tower_ge (E : CondExpSystem ℝ V) {ι : Type*} {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E t (Evec E s x) = Evec E s x := by
  funext i
  exact E.tower_ge_apply h _

theorem bkS_Evec_idem (E : CondExpSystem ℝ V) {ι : Type*} (t : ℕ) (x : ι → V) :
    Evec E t (Evec E t x) = Evec E t x :=
  bkS_Evec_tower_le E le_rfl x

/-- An `F_s`-measurable random vector is `F_t`-measurable for `t ≥ s`. -/
theorem bkS_Evec_of_le (E : CondExpSystem ℝ V) {ι : Type*} {s t : ℕ} (h : s ≤ t) {x : ι → V}
    (hx : Evec E s x = x) : Evec E t x = x := by
  rw [← hx, bkS_Evec_tower_ge E h]

theorem bkS_norm_Evec_le (E : CondExpSystem ℝ V) {ι : Type*} [Fintype ι] (t : ℕ) (x : ι → V) :
    ‖Evec E t x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (E.norm_apply_le t _).trans (norm_le_pi_norm x i)

theorem bkS_isAdaptedV_iff (E : CondExpSystem ℝ V) {ι : Type*} (x : ℕ → ι → V) :
    IsAdaptedV E x ↔ ∀ t, Evec E t (x t) = x t :=
  ⟨fun h t => funext fun i => h t i, fun h t i => congrFun (h t) i⟩

/-! ### Definition 2.3.1: stable processes -/

omit [NormedSpace ℝ V] in
/-- **Definition 2.3.1** (Miao, p. 52): a process is stable iff it is bounded in the max norm
`maxⱼ ‖xⱼ‖`. -/
theorem bkS_isStableProc_iff {ι : Type*} [Fintype ι] (x : ℕ → ι → V) :
    IsStableProc x ↔ ∃ C, ∀ t, ‖x t‖ ≤ C := by
  constructor
  · rintro ⟨M, hM, h⟩
    exact ⟨M, fun t => (pi_norm_le_iff_of_nonneg hM.le).2 fun i => (h t i).le⟩
  · rintro ⟨C, h⟩
    refine ⟨max C 0 + 1, by positivity, fun t i => ?_⟩
    exact (norm_le_pi_norm (x t) i).trans_lt ((h t).trans_lt (by linarith [le_max_left C 0]))

/-- Miao, p. 52: a stable process stays stable under conditional expectations, at any dates:
`t ↦ E_{f(t)}x_{g(t)}` is stable (e.g. `E_tx_{t+j}`, `E_0x_t`). -/
theorem bkS_stable_Evec (E : CondExpSystem ℝ V) {ι : Type*} {x : ℕ → ι → V}
    (hx : IsStableProc x) (f g : ℕ → ℕ) : IsStableProc fun t => Evec E (f t) (x (g t)) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t i => (E.norm_apply_le _ _).trans_lt (h _ i)⟩

omit [NormedSpace ℝ V] in
/-- Miao, p. 52: shifts of a stable process are stable. -/
theorem bkS_stable_shift {ι : Type*} {x : ℕ → ι → V} (hx : IsStableProc x) (j : ℕ) :
    IsStableProc fun t => x (t + j) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t i => h _ i⟩

/-- Miao, p. 52: a matrix maps stable processes to stable processes. -/
theorem bkS_stable_matAct {ι κ : Type*} [Finite ι] [Fintype κ] (M : Matrix ι κ ℝ)
    {x : ℕ → κ → V} (hx : IsStableProc x) : IsStableProc fun t => matAct M (x t) := by
  have := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff x).1 hx
  obtain ⟨c, hc0, hc⟩ := bkS_matAct_bound (V := V) M
  exact (bkS_isStableProc_iff _).2 ⟨c * C, fun t => (hc _).trans (by gcongr; exact hC t)⟩

omit [NormedSpace ℝ V] in
/-- Sums of stable processes are stable. -/
theorem bkS_stable_add {ι : Type*} {x y : ℕ → ι → V} (hx : IsStableProc x)
    (hy : IsStableProc y) : IsStableProc fun t => x t + y t := by
  obtain ⟨M, hM, h⟩ := hx
  obtain ⟨N, hN, h'⟩ := hy
  exact ⟨M + N, by positivity, fun t i => (norm_add_le _ _).trans_lt (add_lt_add (h t i) (h' t i))⟩

/-- Miao, p. 52: for a stable `z` (`‖z_t‖ ≤ C`) and `M` with geometric decay, `∑ⱼ MʲE_tz_{t+j}`
converges, with norm at most `KC/(1 − a)`. -/
theorem bkS_summable_geom [CompleteSpace V] (E : CondExpSystem ℝ V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} {K a : ℝ} (hM : HasGeomDecay M K a) {z : ℕ → ι → V}
    {C : ℝ} (hz : ∀ t, ‖z t‖ ≤ C) (t : ℕ) :
    Summable (fun j => matAct (M ^ j) (Evec E t (z (t + j)))) ∧
      ‖∑' j, matAct (M ^ j) (Evec E t (z (t + j)))‖ ≤ K * C / (1 - a) := by
  have ha0 := hM.1
  have ha1 := hM.2.1
  have hb : ∀ j, ‖matAct (M ^ j) (Evec E t (z (t + j)))‖ ≤ K * C * a ^ j := fun j =>
    calc ‖matAct (M ^ j) (Evec E t (z (t + j)))‖ ≤ K * a ^ j * ‖Evec E t (z (t + j))‖ :=
          bkS_geom_decay hM j _
      _ ≤ K * a ^ j * C := mul_le_mul_of_nonneg_left ((bkS_norm_Evec_le E t _).trans (hz _))
          (mul_nonneg hM.2.2.1 (pow_nonneg ha0 j))
      _ = K * C * a ^ j := by ring
  have hg := (hasSum_geometric_of_lt_one ha0 ha1).mul_left (K * C)
  refine ⟨Summable.of_norm_bounded hg.summable hb, ?_⟩
  have := tsum_of_norm_bounded hg hb
  simpa [div_eq_mul_inv] using this

/-! ### The forward solution (2.12) -/

/-- Miao, (2.12), p. 54: the forward-looking solution
`u_t = −J_u⁻¹∑_{j ≥ 0} J_u^{−j}E_tc_{t+j}` of `E_tu_{t+1} = J_uu_t + c_t`. -/
noncomputable def bkS_fwd {τ : Type*} [Fintype τ] [DecidableEq τ] (E : CondExpSystem ℝ V)
    (Ju : Matrix τ τ ℝ) (c : ℕ → τ → V) (t : ℕ) : τ → V :=
  -matAct Ju⁻¹ (∑' j, matAct (Ju⁻¹ ^ j) (Evec E t (c (t + j))))

/-- Miao, (2.12), p. 54, in the printed form: with `c_t = C_u*z_t`,
`u_t = −∑_{j ≥ 0} J_u^{−j−1}C_u*E_tz_{t+j}`. -/
theorem eq_2_12 [CompleteSpace V] (E : CondExpSystem ℝ V) {τ m : Type*} [Fintype τ]
    [DecidableEq τ] [Fintype m] {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    (Cu : Matrix τ m ℝ) {z : ℕ → m → V} (hz : IsStableProc z) (t : ℕ) :
    bkS_fwd E Ju (fun t => matAct Cu (z t)) t =
      -∑' j, matAct (Ju⁻¹ ^ (j + 1) * Cu) (Evec E t (z (t + j))) := by
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct Cu hz)
  have hs := (bkS_summable_geom E hM hC t).1
  unfold bkS_fwd
  rw [((bkS_matAct_hasSum Ju⁻¹ hs.hasSum).tsum_eq).symm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [Evec_matAct, matAct_mul, matAct_mul, ← pow_succ']

/-- The forward solution is adapted: `E_tu_t = u_t`. -/
theorem bkS_fwd_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) (t : ℕ) :
    Evec E t (bkS_fwd E Ju c t) = bkS_fwd E Ju c t := by
  have hs := (bkS_summable_geom E hM hc t).1
  unfold bkS_fwd
  rw [bkS_Evec_neg, Evec_matAct, ((bkS_Evec_hasSum E t hs.hasSum).tsum_eq).symm]
  congr 2
  refine tsum_congr fun j => ?_
  rw [Evec_matAct, bkS_Evec_idem]

/-- The forward solution is bounded. -/
theorem bkS_fwd_bound [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a)
    {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C) :
    ∃ D, ∀ t, ‖bkS_fwd E Ju c t‖ ≤ D := by
  obtain ⟨b, hb0, hb⟩ := bkS_matAct_bound (V := V) Ju⁻¹
  refine ⟨b * (K * C / (1 - a)), fun t => ?_⟩
  rw [bkS_fwd, norm_neg]
  exact (hb _).trans (mul_le_mul_of_nonneg_left (bkS_summable_geom E hM hc t).2 hb0)

/-- The forward solution solves `E_tu_{t+1} = J_uu_t + c_t` when `c` is adapted. -/
theorem bkS_fwd_rec [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C)
    (hca : ∀ t, Evec E t (c t) = c t) (t : ℕ) :
    Evec E t (bkS_fwd E Ju c (t + 1)) = matAct Ju (bkS_fwd E Ju c t) + c t := by
  set M := Ju⁻¹
  have hs := (bkS_summable_geom E hM hc t).1
  have hs1 := (bkS_summable_geom E hM hc (t + 1)).1
  -- `S_t = E_tc_t + M S'_t`
  set S' := ∑' j, matAct (M ^ j) (Evec E t (c (t + 1 + j)))
  have hs' : Summable fun j => matAct (M ^ j) (Evec E t (c (t + 1 + j))) := by
    have := (bkS_summable_geom E hM (z := fun s => c (s + 1)) (fun s => hc _) t).1
    refine this.congr fun j => ?_
    rw [show t + j + 1 = t + 1 + j by ring]
  have hS : ∑' j, matAct (M ^ j) (Evec E t (c (t + j))) = c t + matAct M S' := by
    rw [hs.tsum_eq_zero_add, ((bkS_matAct_hasSum M hs'.hasSum).tsum_eq).symm]
    simp only [pow_zero, matAct_one, add_zero, hca t]
    congr 1
    refine tsum_congr fun j => ?_
    rw [matAct_mul, ← pow_succ', show t + (j + 1) = t + 1 + j by ring]
  -- `E_tS_{t+1} = S'_t`
  have hES : Evec E t (∑' j, matAct (M ^ j) (Evec E (t + 1) (c (t + 1 + j)))) = S' := by
    rw [((bkS_Evec_hasSum E t hs1.hasSum).tsum_eq).symm]
    refine tsum_congr fun j => ?_
    rw [Evec_matAct, bkS_Evec_tower_le E (Nat.le_succ t)]
  unfold bkS_fwd
  rw [bkS_Evec_neg, Evec_matAct, hES, hS, bkS_matAct_neg, matAct_mul,
    Matrix.mul_nonsing_inv _ hdet, matAct_one]
  abel

/-- The forward solution is the only bounded adapted solution of `E_tu_{t+1} = J_uu_t + c_t`
(Miao, p. 54): the difference `e` of two solutions satisfies `e_t = J_u^{−k}E_te_{t+k}`. -/
theorem bkS_fwd_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {τ : Type*} [Fintype τ]
    [DecidableEq τ] {Ju : Matrix τ τ ℝ} (hdet : IsUnit Ju.det) {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) {c : ℕ → τ → V} {C : ℝ} (hc : ∀ t, ‖c t‖ ≤ C)
    (hca : ∀ t, Evec E t (c t) = c t) {u : ℕ → τ → V} (hua : ∀ t, Evec E t (u t) = u t)
    {D : ℝ} (hu : ∀ t, ‖u t‖ ≤ D) (hrec : ∀ t, Evec E t (u (t + 1)) = matAct Ju (u t) + c t)
    (t : ℕ) : u t = bkS_fwd E Ju c t := by
  set M := Ju⁻¹
  obtain ⟨D', hD'⟩ := bkS_fwd_bound E hM hc
  set e := fun s => u s - bkS_fwd E Ju c s
  have he : ∀ s, e s = matAct M (Evec E s (e (s + 1))) := fun s => by
    simp only [e, bkS_Evec_sub, hrec s, bkS_fwd_rec E hdet hM hc hca s]
    rw [show matAct Ju (u s) + c s - (matAct Ju (bkS_fwd E Ju c s) + c s) =
      matAct Ju (u s - bkS_fwd E Ju c s) by rw [bkS_matAct_sub]; abel, matAct_mul,
      Matrix.nonsing_inv_mul _ hdet, matAct_one]
  have hea : ∀ s, Evec E s (e s) = e s := fun s => by
    simp only [e, bkS_Evec_sub, hua s, bkS_fwd_adapted E hM hc s]
  have hk : ∀ k, e t = matAct (M ^ k) (Evec E t (e (t + k))) := fun k => by
    induction k with
    | zero => simp [hea t, matAct_one]
    | succ k ih =>
      rw [ih]
      conv_lhs => rw [he (t + k)]
      rw [Evec_matAct, bkS_Evec_tower_le E (by omega), matAct_mul, ← pow_succ,
        show t + k + 1 = t + (k + 1) by ring]
  have ha0 := hM.1
  have ha1 := hM.2.1
  have hle : ∀ k, ‖e t‖ ≤ K * (D + D') * a ^ k := fun k => by
    rw [hk k]
    calc ‖matAct (M ^ k) (Evec E t (e (t + k)))‖ ≤ K * a ^ k * ‖Evec E t (e (t + k))‖ :=
          bkS_geom_decay hM k _
      _ ≤ K * a ^ k * (D + D') := mul_le_mul_of_nonneg_left ((bkS_norm_Evec_le E t _).trans
          ((norm_sub_le _ _).trans (add_le_add (hu _) (hD' _))))
          (mul_nonneg hM.2.2.1 (pow_nonneg ha0 k))
      _ = K * (D + D') * a ^ k := by ring
  have hlim : Tendsto (fun k => K * (D + D') * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul (K * (D + D'))
  have h0 : e t = 0 := norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)
  exact sub_eq_zero.1 h0

/-- **Jump-only systems** (Miao, pp. 53–54, with `n_k = 0`): if `W` is invertible and `W⁻¹`
decays geometrically (all eigenvalues of `W` outside the unit circle), then for every stable
adapted `c` the system `E_tx_{t+1} = Wx_t + c_t` has exactly one stable adapted solution, the
forward solution `x_t = −∑ⱼ W^{−j−1}E_tc_{t+j}`. -/
theorem bkS_jump_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {W : Matrix ι ι ℝ} (hdet : IsUnit W.det) {K a : ℝ}
    (hM : HasGeomDecay W⁻¹ K a) {c : ℕ → ι → V} (hc : IsStableProc c) (hca : IsAdaptedV E c) :
    ∃! x : ℕ → ι → V, (∀ t, Evec E t (x (t + 1)) = matAct W (x t) + c t) ∧
      IsAdaptedV E x ∧ IsStableProc x := by
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff c).1 hc
  have hca' := (bkS_isAdaptedV_iff E c).1 hca
  obtain ⟨D, hD⟩ := bkS_fwd_bound E hM hC
  refine ⟨bkS_fwd E W c, ⟨bkS_fwd_rec E hdet hM hC hca',
    (bkS_isAdaptedV_iff E _).2 (bkS_fwd_adapted E hM hC), (bkS_isStableProc_iff _).2 ⟨D, hD⟩⟩,
    fun x ⟨hx, hxa, hxs⟩ => funext fun t => ?_⟩
  obtain ⟨D', hD'⟩ := (bkS_isStableProc_iff x).1 hxs
  exact bkS_fwd_unique E hdet hM hC hca' ((bkS_isAdaptedV_iff E x).1 hxa) hD' hx t

/-- Miao, (2.11), p. 52, with `A` nonsingular: `AE_tx_{t+1} = Bx_t + Cz_t` iff
`E_tx_{t+1} = Wx_t + A⁻¹Cz_t` with `W = A⁻¹B`. -/
theorem eq_2_11_iff (E : CondExpSystem ℝ V) {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] (A B : Matrix n n ℝ) (C : Matrix n m ℝ) (hA : IsUnit A.det) (z : ℕ → m → V)
    (x : ℕ → n → V) :
    IsRESolution E A B C z x ↔
      ∀ t, Evec E t (x (t + 1)) = matAct (A⁻¹ * B) (x t) + matAct (A⁻¹ * C) (z t) := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · rw [← matAct_mul, ← matAct_mul, ← matAct_add, ← h, matAct_mul,
      Matrix.nonsing_inv_mul _ hA, matAct_one]
  · rw [h, matAct_add, matAct_mul, matAct_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.one_mul]

/-- Miao, p. 52: with `A` nonsingular the regularity Assumption 1.4.1 that the book maintains
holds automatically. -/
theorem bkS_regular_of_det {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hA : IsUnit A.det) : IsRegular A B :=
  isRegular_of_isUnit_det A B hA

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Blanchard–Kahn method for stochastic systems

Copied from `EconomicDynamics/RationalExpectations` (module `StochasticBK`), namespace renamed.

Miao, §2.3.1, pp. 53–54. `A` is nonsingular, `W = A⁻¹B` has a real block split
`PWP⁻¹ = diag(J_s, J_u)` (`IsRealBlockSplit`, which exists when no eigenvalue of `W` lies on the
unit circle: `exists_real_block_split`), and `x = (k, y)` with `k` predetermined in the sense of
Blanchard and Kahn (`IsPredeterminedBK`: `E_tk_{t+1} = k_{t+1}`). A stable solution
(`bkS_IsStableSol`) is a stable adapted process solving `E_tx_{t+1} = Wx_t + Gz_t` with `k`
predetermined.

* **Theorem 1.4.2 in the stochastic case** (`theorem_1_4_2_stoch`): if `n_u = n_y` and `P_uy` is
  nonsingular, then for every `k₀` with `E_0k₀ = k₀` and every stable adapted `z` there is a
  unique stable solution of (2.11) with `k`-part `k₀`. The hypothesis `E_0k₀ = k₀` is necessary
  (`bkS_k0_adapted`). Existence (`bkS_exists`) needs only a right inverse of `P_uy`, uniqueness
  (`bkS_unique`) only a left inverse. Along any stable solution `u_t = (Px_t)_u` is the forward
  solution (2.12) (`bkS_u_eq_fwd`), `y_t = P_uy⁻¹(u_t − P_ukk_t)` and
  `k_{t+1} = (Wx_t + Gz_t)_k` (`bkS_policy`).
  **Corollary 1.4.1 in the stochastic case** (`corollary_1_4_1_stoch`): if `z_t = z̄` from some
  date on, the stable solution converges in norm to `x̄ = (A − B)⁻¹Cz̄`.
  The construction differs from the deterministic one: `x_{t+1} = Wx_t + Gz_t + (0, η_{t+1})`,
  where the expectational error `η_{t+1} = Q(u_{t+1} − E_tu_{t+1})` of the jump variables keeps
  `u` on the forward solution.
* **Certainty equivalence** (p. 54): for the trivial system `E_t = id` (`bkS_trivial`) on `ℝ`,
  stable stochastic solutions are exactly the stable deterministic solutions of Chapter 1
  (`certainty_equivalence`), the forward solutions agree (`certainty_equivalence_fwd`), and
  Theorem 1.4.2 follows from its stochastic version (`theorem_1_4_2_of_stoch`). In general the
  formulas are the deterministic ones with `z_{t+j}` replaced by `E_tz_{t+j}` (`eq_2_12`,
  `bkS_policy`). If `E_tz_{t+1} = Φz_t` (as for (2.1)), `E_tz_{t+j} = Φʲz_t` and
  `u_t = −∑ⱼ J_u^{−j−1}C_u*Φʲz_t`, the same expression as in the deterministic case `Σ = 0`
  (`certainty_equivalence_ar`).
* **Theorem 1.4.3 in the stochastic case** (p. 54, "also applies here"). As printed (Chapter 1)
  it is false; the corrected versions about stable solutions hold. Given `w ≠ 0` with
  `E_0w = w` (a nonzero `F_0`-measurable random variable, e.g. a constant): if `n_u > n_y`, for
  every `z` some `F_0`-measurable `k₀` has no stable solution (`theorem_1_4_3_gt_stoch`); if
  `n_u < n_y`, one stable solution gives infinitely many (`theorem_1_4_3_lt_stoch`), and if
  `P_uy` has a right inverse they exist for every `k₀` (`theorem_1_4_3_lt_exists_stoch`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Blocks -/

omit [NormedSpace ℝ V] in
theorem bkS_add_comp {α β : Type*} (a b : α → V) (f : β → α) : (a + b) ∘ f = a ∘ f + b ∘ f :=
  rfl

omit [NormedSpace ℝ V] in
theorem bkS_sub_comp {α β : Type*} (a b : α → V) (f : β → α) : (a - b) ∘ f = a ∘ f - b ∘ f :=
  rfl

theorem bkS_Evec_comp (E : CondExpSystem ℝ V) {α β : Type*} (t : ℕ) (a : α → V) (f : β → α) :
    Evec E t (a ∘ f) = Evec E t a ∘ f :=
  rfl

/-- `(Px)_s = P_skk + P_syy`. -/
theorem bkS_comp_inl {σ τ κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → V) :
    matAct P x ∘ Sum.inl = matAct P.toBlocks₁₁ (x ∘ Sum.inl) + matAct P.toBlocks₁₂ (x ∘ Sum.inr) :=
  by
  funext i
  simp [matAct, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

/-- `(Px)_u = P_ukk + P_uyy`. -/
theorem bkS_comp_inr {σ τ κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → V) :
    matAct P x ∘ Sum.inr = matAct P.toBlocks₂₁ (x ∘ Sum.inl) + matAct P.toBlocks₂₂ (x ∘ Sum.inr) :=
  by
  funext i
  simp [matAct, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem bkS_blockDiag_inl {σ τ : Type*} [Fintype σ] [Fintype τ] (Js : Matrix σ σ ℝ)
    (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → V) :
    matAct (Matrix.fromBlocks Js 0 0 Ju) v ∘ Sum.inl = matAct Js (v ∘ Sum.inl) := by
  funext i
  simp [matAct, Fintype.sum_sum_type]

theorem bkS_blockDiag_inr {σ τ : Type*} [Fintype σ] [Fintype τ] (Js : Matrix σ σ ℝ)
    (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → V) :
    matAct (Matrix.fromBlocks Js 0 0 Ju) v ∘ Sum.inr = matAct Ju (v ∘ Sum.inr) := by
  funext i
  simp [matAct, Fintype.sum_sum_type]

/-- (1.26) for random vectors, stable part: `(PWx)_s = J_s(Px)_s`. -/
theorem bkS_split_inl {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ] {W : Matrix ι ι ℝ}
    {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (x : ι → V) :
    matAct P (matAct W x) ∘ Sum.inl = matAct Js (matAct P x ∘ Sum.inl) := by
  rw [matAct_mul, hPW, ← matAct_mul, bkS_blockDiag_inl]

/-- (1.26) for random vectors, unstable part: `(PWx)_u = J_u(Px)_u`. -/
theorem bkS_split_inr {ι σ τ : Type*} [Fintype ι] [Fintype σ] [Fintype τ] {W : Matrix ι ι ℝ}
    {P : Matrix (σ ⊕ τ) ι ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (x : ι → V) :
    matAct P (matAct W x) ∘ Sum.inr = matAct Ju (matAct P x ∘ Sum.inr) := by
  rw [matAct_mul, hPW, ← matAct_mul, bkS_blockDiag_inr]

omit [NormedSpace ℝ V] in
theorem bkS_norm_comp_inl_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → V) :
    ‖v ∘ Sum.inl‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm v _

omit [NormedSpace ℝ V] in
theorem bkS_norm_comp_inr_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → V) :
    ‖v ∘ Sum.inr‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm v _

omit [NormedSpace ℝ V] in
theorem bkS_norm_sum_type_le {κ υ : Type*} [Fintype κ] [Fintype υ] (v : κ ⊕ υ → V) :
    ‖v‖ ≤ ‖v ∘ Sum.inl‖ + ‖v ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rcases i with i | i
  · exact (norm_le_pi_norm (v ∘ Sum.inl) i).trans (le_add_of_nonneg_right (norm_nonneg _))
  · exact (norm_le_pi_norm (v ∘ Sum.inr) i).trans (le_add_of_nonneg_left (norm_nonneg _))

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem bkS_sumElim_eta {κ υ : Type*} (v : κ ⊕ υ → V) :
    v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  funext i
  rcases i with i | i <;> rfl

/-- The backward solution of `s_{t+1} = Ms_t + g_t` for random vectors:
`s_t = Mᵗs₀ + ∑_{j<t} Mʲg_{t−1−j}`. -/
theorem bkS_backward_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    {s g : ℕ → ι → V} (hs : ∀ t, s (t + 1) = matAct M (s t) + g t) (t : ℕ) :
    s t = matAct (M ^ t) (s 0) + ∑ j ∈ Finset.range t, matAct (M ^ j) (g (t - 1 - j)) := by
  induction t with
  | zero => simp [matAct_one]
  | succ t ih =>
    rw [hs t, ih, matAct_add, bkS_matAct_sum, Finset.sum_range_succ', matAct_mul, ← pow_succ']
    simp only [matAct_mul, ← pow_succ', pow_zero, matAct_one]
    rw [show t + 1 - 1 - 0 = t by omega, add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega]

/-- With geometric decay of `M` and bounded `g`, the backward solution is bounded. -/
theorem bkS_bounded_backward {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ} {K a : ℝ}
    (hM : HasGeomDecay M K a) {s g : ℕ → ι → V} (hs : ∀ t, s (t + 1) = matAct M (s t) + g t)
    {C : ℝ} (hg : ∀ t, ‖g t‖ ≤ C) : ∀ t, ‖s t‖ ≤ K * ‖s 0‖ + K * C / (1 - a) := by
  have ha0 := hM.1
  have ha1 := hM.2.1
  have hK0 := hM.2.2.1
  have hC : 0 ≤ C := (norm_nonneg _).trans (hg 0)
  intro t
  rw [bkS_backward_eq M hs t]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖matAct (M ^ t) (s 0)‖ ≤ K * a ^ t * ‖s 0‖ := bkS_geom_decay hM t _
      _ ≤ K * 1 * ‖s 0‖ := by
          gcongr
          exact pow_le_one₀ ha0 ha1.le
      _ = K * ‖s 0‖ := by ring
  · calc ‖∑ j ∈ Finset.range t, matAct (M ^ j) (g (t - 1 - j))‖
        ≤ ∑ j ∈ Finset.range t, K * C * a ^ j := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          calc ‖matAct (M ^ j) (g (t - 1 - j))‖ ≤ K * a ^ j * ‖g (t - 1 - j)‖ :=
                bkS_geom_decay hM j _
            _ ≤ K * a ^ j * C := by gcongr; exact hg _
            _ = K * C * a ^ j := by ring
      _ = K * C * ∑ j ∈ Finset.range t, a ^ j := by rw [Finset.mul_sum]
      _ ≤ K * C * (1 - a)⁻¹ := by
          gcongr
          rw [← tsum_geometric_of_lt_one ha0 ha1]
          exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg ha0 j)
            (summable_geometric_of_lt_one ha0 ha1)
      _ = K * C / (1 - a) := by ring

/-! ### Stable solutions -/

/-- A stable solution of `E_tx_{t+1} = Wx_t + Gz_t` (Miao, pp. 52–53): adapted, stable, with
the `k`-part predetermined in the sense of Blanchard and Kahn. -/
def bkS_IsStableSol (E : CondExpSystem ℝ V) {κ υ m : Type*} [Fintype κ] [Fintype υ] [Fintype m]
    (W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V)
    (x : ℕ → κ ⊕ υ → V) : Prop :=
  (∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t)) ∧ IsAdaptedV E x ∧
    IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ IsStableProc x

variable {κ υ σ τ m : Type*} [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ]
  [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] [Fintype m]

omit [DecidableEq κ] [DecidableEq υ] [DecidableEq σ] [DecidableEq τ] in
/-- (2.11) in the transformed variables, unstable part: `E_tu_{t+1} = J_uu_t + C_u*z_t`. -/
theorem bkS_u_rec (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hPW : P * W = Matrix.fromBlocks Js 0 0 Ju * P) (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V)
    {x : ℕ → κ ⊕ υ → V} (hx : ∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t))
    (t : ℕ) :
    Evec E t (matAct P (x (t + 1)) ∘ Sum.inr) =
      matAct Ju (matAct P (x t) ∘ Sum.inr) + matAct P (matAct G (z t)) ∘ Sum.inr := by
  rw [bkS_Evec_comp, Evec_matAct, hx t, matAct_add, bkS_add_comp, bkS_split_inr hPW]

/-- Miao, (2.12), p. 54: along any stable solution, `u_t = (Px_t)_u` is the forward solution
`−∑ⱼ J_u^{−j−1}C_u*E_tz_{t+j}` (`eq_2_12`). -/
theorem bkS_u_eq_fwd [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (G : Matrix (κ ⊕ υ) m ℝ)
    {z : ℕ → m → V} (hz : IsStableProc z) (hza : IsAdaptedV E z) {x : ℕ → κ ⊕ υ → V}
    (hx : ∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t)) (hxa : IsAdaptedV E x)
    (hxs : IsStableProc x) (t : ℕ) :
    matAct P (x t) ∘ Sum.inr = bkS_fwd E Ju (fun t => matAct P (matAct G (z t)) ∘ Sum.inr) t := by
  obtain ⟨-, -, hPW, -, hJu⟩ := hS
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct P (bkS_stable_matAct G hz))
  obtain ⟨D, hD⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct P hxs)
  have hza' := (bkS_isAdaptedV_iff E z).1 hza
  have hxa' := (bkS_isAdaptedV_iff E x).1 hxa
  refine bkS_fwd_unique E hdet hKa (C := C) (fun t => (bkS_norm_comp_inr_le _).trans (hC t))
    (fun t => ?_) (fun t => ?_) (D := D) (fun t => (bkS_norm_comp_inr_le _).trans (hD t))
    (bkS_u_rec E hPW G z hx) t
  · rw [bkS_Evec_comp, Evec_matAct, Evec_matAct, hza' t]
  · rw [bkS_Evec_comp, Evec_matAct, hxa' t]

/-- The policy of a stable solution (Miao, pp. 53–54, with (1.32)): if `QP_uy = I`, then
`y_t = Q(u_t − P_ukk_t)` with `u_t` the forward solution (2.12), and
`k_{t+1} = (Wx_t + Gz_t)_k`. These are the deterministic formulas with `E_t` applied to the
forcing terms. -/
theorem bkS_policy [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V} (hz : IsStableProc z)
    (hza : IsAdaptedV E z) {x : ℕ → κ ⊕ υ → V} (hx : bkS_IsStableSol E W G z x) (t : ℕ) :
    x t ∘ Sum.inr = matAct Q (bkS_fwd E Ju (fun t => matAct P (matAct G (z t)) ∘ Sum.inr) t -
      matAct P.toBlocks₂₁ (x t ∘ Sum.inl)) ∧
      x (t + 1) ∘ Sum.inl = (matAct W (x t) + matAct G (z t)) ∘ Sum.inl := by
  obtain ⟨hx, hxa, hxp, hxs⟩ := hx
  constructor
  · rw [← bkS_u_eq_fwd E hS G hz hza hx hxa hxs t, bkS_comp_inr, add_sub_cancel_left,
      matAct_mul, hQ, matAct_one]
  · funext i
    have := congrFun (hx t) (Sum.inl i)
    simp only [Evec] at this
    simp only [Function.comp_apply]
    rw [← this]
    exact (hxp t i).symm

/-- **Uniqueness** in the stochastic Theorem 1.4.2 (Miao, pp. 53–54): if `P_uy` has a left
inverse, two stable solutions with the same `k₀` coincide. -/
theorem bkS_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : Q * P.toBlocks₂₂ = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V} (hz : IsStableProc z)
    (hza : IsAdaptedV E z) {x x' : ℕ → κ ⊕ υ → V} (hx : bkS_IsStableSol E W G z x)
    (hx' : bkS_IsStableSol E W G z x') (h0 : x 0 ∘ Sum.inl = x' 0 ∘ Sum.inl) : x = x' := by
  have hk : ∀ t, x t ∘ Sum.inl = x' t ∘ Sum.inl ∧ x t = x' t := fun t => by
    have key : ∀ t, x t ∘ Sum.inl = x' t ∘ Sum.inl → x t = x' t := fun t ht => by
      rw [bkS_sumElim_eta (x t), bkS_sumElim_eta (x' t), (bkS_policy E hS Q hQ G hz hza hx t).1,
        (bkS_policy E hS Q hQ G hz hza hx' t).1, ht]
    induction t with
    | zero => exact ⟨h0, key 0 h0⟩
    | succ t ih =>
      have h1 : x (t + 1) ∘ Sum.inl = x' (t + 1) ∘ Sum.inl := by
        rw [(bkS_policy E hS Q hQ G hz hza hx t).2, (bkS_policy E hS Q hQ G hz hza hx' t).2,
          ih.2]
      exact ⟨h1, key _ h1⟩
  exact funext fun t => (hk t).2

/-- **Existence** in the stochastic Theorem 1.4.2 (Miao, pp. 53–54): if `P_uy` has a right
inverse `Q`, then for every `F_0`-measurable `k₀` and every stable adapted `z` there is a stable
solution with `k`-part `k₀`: `x₀ = (k₀, Q(u₀ − P_ukk₀))` and
`x_{t+1} = Wx_t + Gz_t + (0, Q(u_{t+1} − E_tu_{t+1}))`, `u` the forward solution (2.12). -/
theorem bkS_exists [CompleteSpace V] (E : CondExpSystem ℝ V) {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ}
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit W P R Js Ju) (Q : Matrix υ τ ℝ)
    (hQ : P.toBlocks₂₂ * Q = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V} (hz : IsStableProc z)
    (hza : IsAdaptedV E z) (k₀ : κ → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) :
    ∃ x, bkS_IsStableSol E W G z x ∧ x 0 ∘ Sum.inl = k₀ := by
  have hS' := hS
  obtain ⟨-, hRP, hPW, hJs, hJu⟩ := hS'
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  set c := fun t => matAct P (matAct G (z t)) ∘ Sum.inr
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff _).1 (bkS_stable_matAct P (bkS_stable_matAct G hz))
  have hc : ∀ t, ‖c t‖ ≤ C := fun t => (bkS_norm_comp_inr_le _).trans (hC t)
  have hza' := (bkS_isAdaptedV_iff E z).1 hza
  have hca : ∀ t, Evec E t (c t) = c t := fun t => by
    simp only [c]
    rw [bkS_Evec_comp, Evec_matAct, Evec_matAct, hza' t]
  set f := bkS_fwd E Ju c
  have hfa : ∀ t, Evec E t (f t) = f t := bkS_fwd_adapted E hKa hc
  have hfr : ∀ t, Evec E t (f (t + 1)) = matAct Ju (f t) + c t := bkS_fwd_rec E hdet hKa hc hca
  set η : ℕ → υ → V := fun t => matAct Q (f (t + 1) - Evec E t (f (t + 1)))
  set x₀ : κ ⊕ υ → V := Sum.elim k₀ (matAct Q (f 0 - matAct P.toBlocks₂₁ k₀))
  obtain ⟨x, hx0, hx⟩ : ∃ x : ℕ → κ ⊕ υ → V, x 0 = x₀ ∧
      ∀ t, x (t + 1) = matAct W (x t) + matAct G (z t) + Sum.elim (0 : κ → V) (η t) :=
    ⟨fun t => Nat.rec x₀ (fun t xt => matAct W xt + matAct G (z t) + Sum.elim (0 : κ → V) (η t))
      t, rfl,
      fun _ => rfl⟩
  -- the unstable part follows the forward solution
  have hu : ∀ t, matAct P (x t) ∘ Sum.inr = f t := fun t => by
    induction t with
    | zero =>
      rw [hx0, bkS_comp_inr, Sum.elim_comp_inl, Sum.elim_comp_inr, matAct_mul, hQ, matAct_one]
      abel
    | succ t ih =>
      rw [hx t, matAct_add, matAct_add, bkS_add_comp, bkS_add_comp, bkS_split_inr hPW, ih,
        bkS_comp_inr P (Sum.elim (0 : κ → V) (η t)), Sum.elim_comp_inl, Sum.elim_comp_inr,
        bkS_matAct_zero, zero_add]
      simp only [η]
      rw [matAct_mul P.toBlocks₂₂ Q, hQ, matAct_one]
      have := hfr t
      simp only [c] at this ⊢
      rw [this]
      abel
  -- adaptedness
  have hxa : ∀ t, Evec E t (x t) = x t := fun t => by
    induction t with
    | zero =>
      rw [hx0, bkS_Evec_sumElim, Evec_matAct, bkS_Evec_sub, Evec_matAct, hfa 0,
        show Evec E 0 k₀ = k₀ from funext hk₀]
    | succ t ih =>
      rw [hx t, bkS_Evec_add, bkS_Evec_add, Evec_matAct, Evec_matAct,
        bkS_Evec_of_le E (Nat.le_succ t) ih, bkS_Evec_of_le E (Nat.le_succ t) (hza' t),
        bkS_Evec_sumElim, bkS_Evec_zero]
      simp only [η]
      rw [Evec_matAct, bkS_Evec_sub, hfa (t + 1), bkS_Evec_tower_ge E (Nat.le_succ t)]
  have hEη : ∀ t, Evec E t (Sum.elim (0 : κ → V) (η t)) = 0 := fun t => by
    rw [bkS_Evec_sumElim, bkS_Evec_zero]
    simp only [η]
    rw [Evec_matAct, bkS_Evec_sub, bkS_Evec_idem, sub_self, bkS_matAct_zero, Sum.elim_zero_zero]
  have heq : ∀ t, Evec E t (x (t + 1)) = matAct W (x t) + matAct G (z t) := fun t => by
    rw [hx t, bkS_Evec_add, bkS_Evec_add, Evec_matAct, Evec_matAct, hxa t, hza' t, hEη t,
      add_zero]
  -- stability: the stable part solves a backward equation driven by bounded terms
  obtain ⟨D, hD⟩ := bkS_fwd_bound E hKa hc
  obtain ⟨cQ, hcQ0, hcQ⟩ := bkS_matAct_bound (V := V) Q
  obtain ⟨cP, hcP0, hcP⟩ := bkS_matAct_bound (V := V) P
  obtain ⟨cR, hcR0, hcR⟩ := bkS_matAct_bound (V := V) R
  obtain ⟨Ks, as, hKas⟩ := hasGeomDecay_of_isStableMatrix Js hJs
  have hη : ∀ t, ‖Sum.elim (0 : κ → V) (η t)‖ ≤ cQ * (D + D) := fun t => by
    refine (bkS_norm_sum_type_le _).trans ?_
    rw [Sum.elim_comp_inl, Sum.elim_comp_inr, norm_zero, zero_add]
    exact (hcQ _).trans (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
      (add_le_add (hD _) ((bkS_norm_Evec_le E t _).trans (hD _)))) hcQ0)
  set g := fun t => matAct P (matAct G (z t)) ∘ Sum.inl +
    matAct P (Sum.elim (0 : κ → V) (η t)) ∘ Sum.inl
  have hsr : ∀ t, matAct P (x (t + 1)) ∘ Sum.inl =
      matAct Js (matAct P (x t) ∘ Sum.inl) + g t := fun t => by
    rw [hx t, matAct_add, matAct_add, bkS_add_comp, bkS_add_comp, bkS_split_inl hPW, add_assoc]
  have hg : ∀ t, ‖g t‖ ≤ C + cP * (cQ * (D + D)) := fun t =>
    (norm_add_le _ _).trans (add_le_add ((bkS_norm_comp_inl_le _).trans (hC t))
      ((bkS_norm_comp_inl_le _).trans ((hcP _).trans (mul_le_mul_of_nonneg_left (hη t) hcP0))))
  have hsb := bkS_bounded_backward hKas (s := fun t => matAct P (x t) ∘ Sum.inl) hsr hg
  refine ⟨x, ⟨heq, (bkS_isAdaptedV_iff E x).2 hxa, fun t i => ?_, (bkS_isStableProc_iff x).2
    ⟨cR * (Ks * ‖matAct P (x 0) ∘ Sum.inl‖ + Ks * (C + cP * (cQ * (D + D))) / (1 - as) + D),
      fun t => ?_⟩⟩, by rw [hx0, Sum.elim_comp_inl]⟩
  · have h1 : E.E t (x (t + 1) (Sum.inl i)) =
        (matAct W (x t) + matAct G (z t)) (Sum.inl i) := congrFun (heq t) (Sum.inl i)
    have h2 : x (t + 1) (Sum.inl i) = (matAct W (x t) + matAct G (z t)) (Sum.inl i) := by
      rw [hx t]
      simp
    simp only [Function.comp_apply]
    rw [h1, h2]
  · have hxt : x t = matAct R (matAct P (x t)) := by rw [matAct_mul, hRP, matAct_one]
    rw [hxt]
    refine (hcR _).trans (mul_le_mul_of_nonneg_left ((bkS_norm_sum_type_le _).trans
      (add_le_add (hsb t) ?_)) hcR0)
    rw [hu t]
    exact hD t

/-- **Theorem 1.4.2 in the stochastic case** (Blanchard–Kahn, Miao, pp. 53–54). Let `A` be
nonsingular and `W = A⁻¹B` have a real block split `PWP⁻¹ = diag(J_s, J_u)` (no eigenvalue on
the unit circle, condition (iii)). Order `x = (k, y)` with `k` predetermined. If (i)
`n_u = n_y` and (ii) `P_uy` is nonsingular, then for every `F_0`-measurable `k₀` and every
stable adapted `z` the system (2.11) has a unique stable adapted solution with `k`
predetermined and `k`-part `k₀`. -/
theorem theorem_1_4_2_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ) (hA : IsUnit A.det)
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (_hi : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (k₀ : κ → V)
    (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) (z : ℕ → m → V) (hz : IsStableProc z)
    (hza : IsAdaptedV E z) :
    ∃! x : ℕ → κ ⊕ υ → V, IsRESolution E A B Cm z x ∧ IsAdaptedV E x ∧
      IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableProc x := by
  have hiff : ∀ x, (IsRESolution E A B Cm z x ∧ IsAdaptedV E x ∧
      IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableProc x) ↔
      bkS_IsStableSol E (A⁻¹ * B) (A⁻¹ * Cm) z x ∧ x 0 ∘ Sum.inl = k₀ := fun x => by
    rw [eq_2_11_iff E A B Cm hA z x, bkS_IsStableSol]
    tauto
  obtain ⟨x, hx, hx0⟩ := bkS_exists E hS Q hii.1 _ hz hza k₀ hk₀
  refine ⟨x, (hiff x).2 ⟨hx, hx0⟩, fun y hy => ?_⟩
  obtain ⟨hy, hy0⟩ := (hiff y).1 hy
  exact bkS_unique E hS Q hii.2 _ hz hza hy hx (hy0.trans hx0.symm)

omit [Fintype κ] [DecidableEq κ] [Fintype υ] [DecidableEq υ] in
/-- Miao, p. 53: the hypothesis `E_0k₀ = k₀` of `theorem_1_4_2_stoch` is necessary: the initial
value of an adapted solution is `F_0`-measurable. -/
theorem bkS_k0_adapted (E : CondExpSystem ℝ V) {x : ℕ → κ ⊕ υ → V} (hxa : IsAdaptedV E x)
    (i : κ) : E.E 0 (x 0 (Sum.inl i)) = x 0 (Sum.inl i) :=
  hxa 0 (Sum.inl i)

/-! ### Certainty equivalence -/

/-- The trivial system `E_t = id` (no uncertainty): the deterministic case (Miao, p. 54). -/
noncomputable def bkS_trivial (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    CondExpSystem ℝ V where
  E := fun _ => ContinuousLinearMap.id ℝ V
  norm_le := fun _ => ContinuousLinearMap.norm_id_le
  tower_le := fun _ _ _ => ContinuousLinearMap.id_comp _
  tower_ge := fun _ _ _ => ContinuousLinearMap.id_comp _

theorem bkS_Evec_trivial {ι : Type*} (t : ℕ) (x : ι → V) : Evec (bkS_trivial V) t x = x :=
  rfl

omit [DecidableEq κ] [DecidableEq υ] in
/-- **Certainty equivalence** (Miao, p. 54), the deterministic case: for `E_t = id` on `ℝ`, the
stable adapted solutions of (2.11) with `k` predetermined are exactly the stable solutions of the
deterministic system (1.20) of Chapter 1. -/
theorem certainty_equivalence (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (z : ℕ → m → ℝ) (x : ℕ → κ ⊕ υ → ℝ) :
    (IsRESolution (bkS_trivial ℝ) A B Cm z x ∧ IsAdaptedV (bkS_trivial ℝ) x ∧
        IsPredeterminedBK (bkS_trivial ℝ) (fun t => x t ∘ Sum.inl) ∧ IsStableProc x) ↔
      IsSolution A B Cm z x ∧ IsStableSeq x := by
  have h1 : IsRESolution (bkS_trivial ℝ) A B Cm z x ↔ IsSolution A B Cm z x := by
    simp only [IsRESolution, IsSolution, bkS_Evec_trivial, bkS_matAct_real]
  have h2 : IsStableProc x ↔ IsStableSeq x := by
    rw [bkS_isStableProc_iff, isStableSeq_iff_exists_le]
  rw [h1, h2]
  exact ⟨fun h => ⟨h.1, h.2.2.2⟩, fun h => ⟨h.1, fun _ _ => rfl, fun _ _ => rfl, h.2⟩⟩

/-- **Certainty equivalence** (Miao, p. 54), the forward solution: for `E_t = id` on `ℝ` the
stochastic forward solution (2.12) is the deterministic one (1.29). -/
theorem certainty_equivalence_fwd (Ju : Matrix τ τ ℝ) (c : ℕ → τ → ℝ) (t : ℕ) :
    bkS_fwd (bkS_trivial ℝ) Ju c t = forwardU Ju c t := by
  simp only [bkS_fwd, forwardU, bkS_Evec_trivial, bkS_matAct_real]

/-- Theorem 1.4.2 (Miao, p. 20) recovered from its stochastic version with `E_t = id`
(certainty equivalence, p. 54). -/
theorem theorem_1_4_2_of_stoch (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ)
    (hA : IsUnit A.det) {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ}
    {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju)
    (hi : Fintype.card τ = Fintype.card υ) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) (k₀ : κ → ℝ) (z : ℕ → m → ℝ)
    (hz : IsStableSeq z) :
    ∃! x : ℕ → κ ⊕ υ → ℝ, IsSolution A B Cm z x ∧ x 0 ∘ Sum.inl = k₀ ∧ IsStableSeq x := by
  have hz' : IsStableProc z := by
    rw [bkS_isStableProc_iff, ← isStableSeq_iff_exists_le]
    exact hz
  have h := theorem_1_4_2_stoch (bkS_trivial ℝ) A B Cm hA hS hi Q hii k₀ (fun _ => rfl) z hz'
    (fun _ _ => rfl)
  refine (existsUnique_congr fun x => ?_).1 h
  have := certainty_equivalence A B Cm z x
  tauto

omit [Fintype τ] [DecidableEq τ] in
/-- Miao, p. 54: if `E_tz_{t+1} = Φz_t` (as for (2.1)), then `E_tz_{t+j} = Φʲz_t`. -/
theorem bkS_Evec_ar (E : CondExpSystem ℝ V) [DecidableEq m] {Φ : Matrix m m ℝ}
    {z : ℕ → m → V} (hza : IsAdaptedV E z) (hΦ : ∀ t, Evec E t (z (t + 1)) = matAct Φ (z t))
    (t j : ℕ) : Evec E t (z (t + j)) = matAct (Φ ^ j) (z t) := by
  induction j with
  | zero => rw [add_zero, pow_zero, matAct_one]; exact (bkS_isAdaptedV_iff E z).1 hza t
  | succ j ih =>
    rw [← add_assoc, ← bkS_Evec_tower_le E (Nat.le_add_right t j), hΦ, Evec_matAct, ih,
      matAct_mul, ← pow_succ']

/-- **Certainty equivalence** (Miao, p. 54): if `E_tz_{t+1} = Φz_t` (as for (2.1)), the forward
solution (2.12) is `u_t = −∑ⱼ J_u^{−j−1}C_u*Φʲz_t`, the same expression as in the deterministic
case `z_{t+1} = Φz_t` (`Σ = 0`, `certainty_equivalence_ar_det`). -/
theorem certainty_equivalence_ar [CompleteSpace V] (E : CondExpSystem ℝ V) [DecidableEq m]
    {Ju : Matrix τ τ ℝ} {K a : ℝ} (hM : HasGeomDecay Ju⁻¹ K a) (Cu : Matrix τ m ℝ)
    {Φ : Matrix m m ℝ} {z : ℕ → m → V} (hz : IsStableProc z) (hza : IsAdaptedV E z)
    (hΦ : ∀ t, Evec E t (z (t + 1)) = matAct Φ (z t)) (t : ℕ) :
    bkS_fwd E Ju (fun t => matAct Cu (z t)) t =
      -∑' j, matAct (Ju⁻¹ ^ (j + 1) * Cu * Φ ^ j) (z t) := by
  rw [eq_2_12 E hM Cu hz t]
  congr 1
  refine tsum_congr fun j => ?_
  rw [bkS_Evec_ar E hza hΦ, matAct_mul]

/-- **Certainty equivalence** (Miao, p. 54), deterministic side: for `z_{t+1} = Φz_t` the
deterministic forward solution (1.29) is `−∑ⱼ J_u^{−j−1}C_u*Φʲz_t`, the expression of
`certainty_equivalence_ar`. -/
theorem certainty_equivalence_ar_det [DecidableEq m] {Ju : Matrix τ τ ℝ} {K a : ℝ}
    (hM : HasGeomDecay Ju⁻¹ K a) (Cu : Matrix τ m ℝ) {Φ : Matrix m m ℝ} {z : ℕ → m → ℝ}
    (hz : IsStableSeq z) (hΦ : ∀ t, z (t + 1) = Φ *ᵥ z t) (t : ℕ) :
    forwardU Ju (fun t => Cu *ᵥ z t) t = -∑' j, (Ju⁻¹ ^ (j + 1) * Cu * Φ ^ j) *ᵥ z t := by
  have hz' : IsStableProc z := by
    rw [bkS_isStableProc_iff, ← isStableSeq_iff_exists_le]
    exact hz
  have h := certainty_equivalence_ar (bkS_trivial ℝ) hM Cu hz' (fun _ _ => rfl)
    (fun t => by rw [bkS_Evec_trivial, bkS_matAct_real, hΦ]) t
  simp only [bkS_matAct_real] at h
  rw [← certainty_equivalence_fwd, h]

/-! ### Theorem 1.4.3 in the stochastic case -/

/-- The forward solution with zero forcing is zero. -/
theorem bkS_fwd_zero (E : CondExpSystem ℝ V) (Ju : Matrix τ τ ℝ) (t : ℕ) :
    bkS_fwd E Ju (fun _ => (0 : τ → V)) t = 0 := by
  simp [bkS_fwd, bkS_Evec_zero, bkS_matAct_zero]

/-- A stable adapted solution of the homogeneous system `E_td_{t+1} = Wd_t` has `u = 0`. -/
theorem bkS_homog_u_zero [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) {d : ℕ → κ ⊕ υ → V}
    (hd : ∀ t, Evec E t (d (t + 1)) = matAct W (d t)) (hda : ∀ t, Evec E t (d t) = d t)
    {D : ℝ} (hdb : ∀ t, ‖d t‖ ≤ D) (t : ℕ) : matAct P (d t) ∘ Sum.inr = 0 := by
  obtain ⟨-, -, hPW, -, hJu⟩ := hS
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  obtain ⟨cP, hcP0, hcP⟩ := bkS_matAct_bound (V := V) P
  rw [bkS_fwd_unique E hdet hKa (c := fun _ => 0) (C := 0) (fun _ => by simp)
    (fun t => bkS_Evec_zero E t) (u := fun t => matAct P (d t) ∘ Sum.inr) (D := cP * D)
    (fun t => by rw [bkS_Evec_comp, Evec_matAct, hda t])
    (fun t => (bkS_norm_comp_inr_le _).trans ((hcP _).trans
      (mul_le_mul_of_nonneg_left (hdb t) hcP0)))
    (fun t => by rw [bkS_Evec_comp, Evec_matAct, hd t, add_zero, bkS_split_inr hPW]) t,
    bkS_fwd_zero]

/-- **Theorem 1.4.3, first part, corrected, stochastic case** (Miao, pp. 23, 54): if
`n_u > n_y`, then for every forcing process there is an `F_0`-measurable `k₀` from which no
stable solution starts. (`w ≠ 0` is any `F_0`-measurable random variable, e.g. a constant.) -/
theorem theorem_1_4_3_gt_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card υ < Fintype.card τ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V) {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    ∃ k₀ : κ → V, (∀ i, E.E 0 (k₀ i) = k₀ i) ∧
      ¬ ∃ x, bkS_IsStableSol E W G z x ∧ x 0 ∘ Sum.inl = k₀ := by
  have hcard := card_add_card_of_inv hS.1 hS.2.1
  rw [Fintype.card_sum] at hcard
  have hker : LinearMap.ker (Matrix.toLin' R.toBlocks₁₁ᵀ) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]; omega)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hy
  by_contra h
  push Not at h
  obtain ⟨x, hx, hx0⟩ := h 0 (fun i => by simp)
  obtain ⟨x', hx', hx0'⟩ := h (fun i => y i • w) (fun i => by rw [map_smul, hw0])
  set d := fun t => x' t - x t
  have hd : ∀ t, Evec E t (d (t + 1)) = matAct W (d t) := fun t => by
    simp only [d, bkS_Evec_sub, hx.1 t, hx'.1 t, bkS_matAct_sub]
    abel
  have hda : ∀ t, Evec E t (d t) = d t := fun t => by
    simp only [d, bkS_Evec_sub, (bkS_isAdaptedV_iff E _).1 hx.2.1 t,
      (bkS_isAdaptedV_iff E _).1 hx'.2.1 t]
  obtain ⟨Dx, hDx⟩ := (bkS_isStableProc_iff _).1 hx.2.2.2
  obtain ⟨Dx', hDx'⟩ := (bkS_isStableProc_iff _).1 hx'.2.2.2
  have hu := bkS_homog_u_zero E hS hd hda (D := Dx' + Dx)
    (fun t => (norm_sub_le _ _).trans (add_le_add (hDx' t) (hDx t))) 0
  have hd0 : d 0 ∘ Sum.inl = matAct R.toBlocks₁₁ (matAct P (d 0) ∘ Sum.inl) := by
    have e : d 0 = matAct R (matAct P (d 0)) := by rw [matAct_mul, hS.2.1, matAct_one]
    conv_lhs => rw [e]
    rw [bkS_comp_inl R, hu, bkS_matAct_zero, add_zero]
  have hdy : d 0 ∘ Sum.inl = fun i => y i • w := by
    simp only [d]
    rw [bkS_sub_comp, hx0', hx0, sub_zero]
  set s := matAct P (d 0) ∘ Sum.inl
  have key : ∑ i, y i • (d 0 ∘ Sum.inl) i = 0 := by
    rw [hd0]
    simp only [matAct, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have hj := congrFun hy j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hj
    have hj' : ∑ i, y i * R.toBlocks₁₁ i j = 0 := by
      rw [← hj]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hj', zero_smul]
  rw [hdy] at key
  simp only [smul_smul, ← Finset.sum_smul] at key
  have hpos : ∑ i, y i * y i ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
    exact (Finset.sum_pos' (fun i _ => mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩).ne'
  exact hw ((smul_eq_zero.1 key).resolve_left hpos)

/-- **Theorem 1.4.3, second part, corrected, stochastic case** (Miao, pp. 23, 54): if
`n_u < n_y` and there is one stable solution, there are infinitely many with the same `k₀`
(add multiples of `λᵗ`-type stable homogeneous solutions `R(J_sᵗs, 0)w` with `R_kss = 0`, where
`w ≠ 0` is `F_0`-measurable). -/
theorem theorem_1_4_3_lt_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card τ < Fintype.card υ)
    (G : Matrix (κ ⊕ υ) m ℝ) (z : ℕ → m → V) {x : ℕ → κ ⊕ υ → V}
    (hx : bkS_IsStableSol E W G z x) {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    {x' | bkS_IsStableSol E W G z x' ∧ x' 0 ∘ Sum.inl = x 0 ∘ Sum.inl}.Infinite := by
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
  have hwt : ∀ t, E.E t w = w := fun t => by rw [← hw0, E.tower_ge_apply (Nat.zero_le t)]
  set D : ℕ → κ ⊕ υ → V := fun t i => d t i • w
  have hDa : ∀ t s, Evec E s (D t) = D t := fun t s => funext fun i => by
    simp only [D, Evec, map_smul, hwt]
  have hDrec : ∀ t, matAct W (D t) = D (t + 1) := fun t => by
    funext i
    simp only [D, matAct, hd t, Matrix.mulVec, dotProduct, smul_smul, Finset.sum_smul]
  have hDb : ∀ t, ‖D t‖ ≤ Dd * ‖w‖ := fun t =>
    (pi_norm_le_iff_of_nonneg (mul_nonneg ((norm_nonneg _).trans (hDd 0)) (norm_nonneg _))).2
      fun i => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm (d t) i).trans (hDd t))
          (norm_nonneg _)
  have hD0 : D 0 ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hdne
    exact Function.ne_iff.2 ⟨i, smul_ne_zero hi hw⟩
  obtain ⟨hxe, hxa, hxp, hxs⟩ := hx
  obtain ⟨Dx, hDx⟩ := (bkS_isStableProc_iff _).1 hxs
  refine Set.infinite_of_injective_forall_mem (f := fun c : ℝ => x + c • D)
    (fun c c' h => ?_) fun c => ⟨⟨fun t => ?_, fun t i => ?_, fun t i => ?_, ?_⟩, ?_⟩
  · have h1 := congrFun h 0
    simp only [Pi.add_apply, Pi.smul_apply, add_right_inj] at h1
    exact smul_left_injective ℝ hD0 h1
  · simp only [Pi.add_apply, Pi.smul_apply]
    rw [bkS_Evec_add, bkS_Evec_smul, hxe t, hDa, matAct_add, bkS_matAct_smul, hDrec]
    abel
  · simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul, hxa t i]
    rw [show E.E t (D t i) = D t i from congrFun (hDa t t) i]
  · simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, map_add, map_smul]
    rw [show E.E t (x (t + 1) (Sum.inl i)) = x (t + 1) (Sum.inl i) from hxp t i]
    rw [show E.E t (D (t + 1) (Sum.inl i)) = D (t + 1) (Sum.inl i) from
      congrFun (hDa (t + 1) t) _]
  · refine (bkS_isStableProc_iff _).2 ⟨Dx + |c| * (Dd * ‖w‖), fun t => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply]
    refine (norm_add_le _ _).trans (add_le_add (hDx t) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hDb t) (abs_nonneg c)
  · funext i
    have := congrFun hdk i
    simp only [Function.comp_apply, Pi.zero_apply] at this
    simp [D, this]

/-- Miao, pp. 23, 54, corrected: if `n_u < n_y` and `P_uy` has a right inverse (full row
rank), then for every `F_0`-measurable `k₀` and every stable adapted `z` there are infinitely
many stable solutions with `k`-part `k₀`. -/
theorem theorem_1_4_3_lt_exists_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    {W : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ} {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ}
    {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (hS : IsRealBlockSplit W P R Js Ju) (hlt : Fintype.card τ < Fintype.card υ)
    (Q : Matrix υ τ ℝ) (hQ : P.toBlocks₂₂ * Q = 1) (G : Matrix (κ ⊕ υ) m ℝ) {z : ℕ → m → V}
    (hz : IsStableProc z) (hza : IsAdaptedV E z) (k₀ : κ → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i)
    {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    {x | bkS_IsStableSol E W G z x ∧ x 0 ∘ Sum.inl = k₀}.Infinite := by
  obtain ⟨x, hx, hx0⟩ := bkS_exists E hS Q hQ G hz hza k₀ hk₀
  have := theorem_1_4_3_lt_stoch E hS hlt G z hx hw hw0
  rwa [hx0] at this

/-- The conditional expectations from date `T` on: `E'_t = E_{t+T}`. -/
def bkS_shift (E : CondExpSystem ℝ V) (T : ℕ) : CondExpSystem ℝ V where
  E := fun t => E.E (t + T)
  norm_le := fun t => E.norm_le (t + T)
  tower_le := fun s t h => E.tower_le (s + T) (t + T) (by omega)
  tower_ge := fun s t h => E.tower_ge (s + T) (t + T) (by omega)

/-- **Corollary 1.4.1 in the stochastic case** (Miao, pp. 22, 53): under the conditions of the
stochastic Theorem 1.4.2, if `z_t = z̄` for `t ≥ T`, the stable solution converges (in norm) to
`x̄ = (A − B)⁻¹Cz̄`. After `T` the deviation `d` from `x̄` solves the homogeneous system, its
`u`-part vanishes, and since `R_ks` is invertible the predetermined `k` makes the stable part
predetermined too, so `s_{t+1} = J_ss_t` exactly. -/
theorem corollary_1_4_1_stoch [CompleteSpace V] (E : CondExpSystem ℝ V)
    (A B : Matrix (κ ⊕ υ) (κ ⊕ υ) ℝ) (Cm : Matrix (κ ⊕ υ) m ℝ) (hA : IsUnit A.det)
    {P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ} {R : Matrix (κ ⊕ υ) (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ}
    {Ju : Matrix τ τ ℝ} (hS : IsRealBlockSplit (A⁻¹ * B) P R Js Ju) (Q : Matrix υ τ ℝ)
    (hii : P.toBlocks₂₂ * Q = 1 ∧ Q * P.toBlocks₂₂ = 1) {z : ℕ → m → V}
    (hza : IsAdaptedV E z) (zbar : m → V) (T : ℕ) (hzT : ∀ t, T ≤ t → z t = zbar)
    {x : ℕ → κ ⊕ υ → V} (hx : IsRESolution E A B Cm z x) (hxa : IsAdaptedV E x)
    (hxp : IsPredeterminedBK E (fun t => x t ∘ Sum.inl)) (hxs : IsStableProc x) :
    Tendsto x atTop (𝓝 (matAct ((A - B)⁻¹ * Cm) zbar)) := by
  have hS' := hS
  obtain ⟨hPR, hRP, hPW, hJs, -⟩ := hS'
  have hx' := (eq_2_11_iff E A B Cm hA z x).1 hx
  set W := A⁻¹ * B
  set G := A⁻¹ * Cm
  have hAB := isUnit_sub_det A B hA hS.isUnit_one_sub
  set xb := matAct ((A - B)⁻¹ * Cm) zbar
  have hzb : ∀ t, T ≤ t → Evec E t zbar = zbar := fun t ht => by
    rw [← hzT t ht]; exact (bkS_isAdaptedV_iff E z).1 hza t
  have hxb : ∀ t, T ≤ t → Evec E t xb = xb := fun t ht => by
    simp only [xb]; rw [Evec_matAct, hzb t ht]
  have hbar : xb = matAct W xb + matAct G zbar := by
    have h1 : (A - B) * ((A - B)⁻¹ * Cm) = Cm := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAB, Matrix.one_mul]
    have h2 : W * ((A - B)⁻¹ * Cm) + G = (A - B)⁻¹ * Cm := by
      simp only [W, G]
      rw [Matrix.mul_assoc, ← Matrix.mul_add]
      nth_rewrite 2 [← h1]
      rw [Matrix.sub_mul, add_sub_cancel, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
        Matrix.one_mul]
    simp only [xb]
    rw [matAct_mul, ← bkS_matAct_add_left, h2]
  set E' := bkS_shift E T
  set d : ℕ → κ ⊕ υ → V := fun k => x (k + T) - xb
  have hd : ∀ k, Evec E' k (d (k + 1)) = matAct W (d k) := fun k => by
    change Evec E (k + T) (x (k + 1 + T) - xb) = matAct W (x (k + T) - xb)
    rw [bkS_Evec_sub, hxb _ (by omega), show k + 1 + T = k + T + 1 by ring, hx' (k + T),
      hzT _ (by omega), bkS_matAct_sub]
    conv_lhs => rw [hbar]
    abel
  have hda : ∀ k, Evec E' k (d k) = d k := fun k => by
    change Evec E (k + T) (x (k + T) - xb) = x (k + T) - xb
    rw [bkS_Evec_sub, (bkS_isAdaptedV_iff E x).1 hxa, hxb _ (by omega)]
  obtain ⟨Dx, hDx⟩ := (bkS_isStableProc_iff x).1 hxs
  have hu := bkS_homog_u_zero E' hS hd hda (D := Dx + ‖xb‖)
    (fun k => (norm_sub_le _ _).trans (add_le_add (hDx _) le_rfl))
  obtain ⟨hRS, hSR⟩ := rks_inv hPR hRP Q hii
  set S := P.toBlocks₁₁ - P.toBlocks₁₂ * Q * P.toBlocks₂₁
  set s : ℕ → σ → V := fun k => matAct P (d k) ∘ Sum.inl
  have hdk : ∀ k, d k ∘ Sum.inl = matAct R.toBlocks₁₁ (s k) := fun k => by
    have e : d k = matAct R (matAct P (d k)) := by rw [matAct_mul, hRP, matAct_one]
    conv_lhs => rw [e]
    rw [bkS_comp_inl R, hu k, bkS_matAct_zero, add_zero]
  have hsk : ∀ k, s k = matAct S (d k ∘ Sum.inl) := fun k => by
    rw [hdk, matAct_mul, hSR, matAct_one]
  -- the stable part is predetermined, hence `s_{k+1} = J_ss_k`
  have hpre : ∀ k, Evec E' k (d (k + 1) ∘ Sum.inl) = d (k + 1) ∘ Sum.inl := fun k => by
    change Evec E (k + T) ((x (k + 1 + T) - xb) ∘ Sum.inl) = (x (k + 1 + T) - xb) ∘ Sum.inl
    rw [bkS_sub_comp, bkS_Evec_sub, bkS_Evec_comp, bkS_Evec_comp, hxb _ (by omega)]
    congr 1
    funext i
    rw [show k + 1 + T = k + T + 1 by ring]
    exact hxp (k + T) i
  have hsr : ∀ k, s (k + 1) = matAct Js (s k) := fun k => by
    have h1 : Evec E' k (s (k + 1)) = s (k + 1) := by
      rw [hsk, Evec_matAct, hpre]
    have h2 : Evec E' k (s (k + 1)) = matAct Js (s k) := by
      simp only [s]
      rw [bkS_Evec_comp, Evec_matAct, hd k, bkS_split_inl hPW]
    rw [← h1, h2]
  have hs : ∀ k, s k = matAct (Js ^ k) (s 0) := fun k => by
    induction k with
    | zero => rw [pow_zero, matAct_one]
    | succ k ih => rw [hsr, ih, bkS_matAct_pow_succ]
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix Js hJs
  obtain ⟨cR, hcR0, hcR⟩ := bkS_matAct_bound (V := V) R
  have hle : ∀ k, ‖d k‖ ≤ cR * (K * ‖s 0‖) * a ^ k := fun k => by
    have e : d k = matAct R (matAct P (d k)) := by rw [matAct_mul, hRP, matAct_one]
    rw [e]
    refine (hcR _).trans ?_
    have h1 : ‖matAct P (d k)‖ ≤ ‖s k‖ := by
      refine (bkS_norm_sum_type_le _).trans ?_
      rw [hu k, norm_zero, add_zero]
    calc cR * ‖matAct P (d k)‖ ≤ cR * ‖s k‖ := mul_le_mul_of_nonneg_left h1 hcR0
      _ ≤ cR * (K * a ^ k * ‖s 0‖) :=
          mul_le_mul_of_nonneg_left (by rw [hs k]; exact bkS_geom_decay hKa k _) hcR0
      _ = cR * (K * ‖s 0‖) * a ^ k := by ring
  have hlim : Tendsto (fun k => cR * (K * ‖s 0‖) * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hKa.1 hKa.2.1).const_mul
      (cR * (K * ‖s 0‖))
  have hdlim : Tendsto d atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) hle hlim)
  have h2 := hdlim.add_const xb
  simp only [d, sub_add_cancel, zero_add] at h2
  exact (tendsto_add_atTop_iff_nat T).1 h2

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian model: Example 2.3.1 and Exercise 2.2

Copied from `EconomicDynamics/RationalExpectations` (module `NewKeynesian`), namespace renamed.

Miao, Example 2.3.1, pp. 54–55, and Exercise 2 of §2.6, pp. 82–83. The model is the Phillips
curve (2.13) `π_t = κx_t + βE_tπ_{t+1}` and the IS curve (2.14)
`x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1}) + ε^x_t`, with `κ, β, γ > 0`.

**Example 2.3.1** (exogenous rule (2.15) `i_t = ρ_ri_{t−1} + ε_t`, state `(i_{t−1}, x_t, π_t)`):
* (2.16) is derived from (2.13)–(2.15) (`eq_2_16`, an equivalence, given that `i_t` is
  `F_t`-measurable). `A⁻¹`, `W = A⁻¹B` and `A⁻¹C` are computed (`eq_2_16_W`): the printed `W`
  (whose typesetting is garbled) has the right entries
  `[[ρ_r, 0, 0], [ρ_r/γ, 1 + κ/(βγ), −1/(βγ)], [0, −κ/β, 1/β]]`.
* The eigenvalues of `W` are `ρ_r` and the roots `λ₂ ∈ (0, 1)`, `λ₁ > 1` of
  `λ² − (1 + 1/β + κ/(βγ))λ + 1/β` (`nk_lam`, `example_2_3_1_eigen`); exactly one lies outside
  the unit circle. Only `κ, β, γ > 0` and `|ρ_r| < 1` are used (`β < 1` is not needed).
* An explicit real block split with `n_s = 2`, `n_u = 1` (`example_2_3_1_split`, from the general
  saddle lemma `nk_saddle_split`); with two jump variables the Blanchard–Kahn order condition
  fails, and the stochastic Theorem 1.4.3 (`theorem_1_4_3_lt_exists_stoch`) gives
  indeterminacy: for every `F_0`-measurable `i_{−1}` and stable adapted shocks there are
  infinitely many stable solutions (`example_2_3_1_indeterminate`; in general this needs one
  nonzero `F_0`-measurable random variable `w`, e.g. a constant), in particular in the
  deterministic case (`example_2_3_1_indeterminate_det`).

**Exercise 2.2** (`i_t = δ_ππ_t + δ_xx_t + ε_t`, state `(x_t, π_t)`, both jump variables): the model
is the jump-only system `E_tX_{t+1} = WX_t + c_t` (`nk_taylor_iff`), and it has a unique stable
equilibrium for all stable adapted shocks (`nkDeterminate`) iff both eigenvalues of `W` lie
outside the unit circle (`nk_jump2_unique` via `bkS_jump_unique`; `nk_jump2_nonunique` for the
converse). With `κ, γ > 0`, `0 < β < 1`:
* **(b), exact** (`ex_2_2_b_exact`, `δ_x ≥ 0`): determinacy iff `κ(δ_π − 1) + (1 − β)δ_x > 0` or
  `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`; for `δ_π, δ_x ≥ 0` the second branch is impossible and
  the condition is Bullard–Mitra's `κ(δ_π − 1) + (1 − β)δ_x > 0` (`ex_2_2_b`).
* **(a), corrected** (`ex_2_2_a`, `δ_x = 0`): determinacy iff `δ > 1` or
  `δ < −1 − 2(1 + β)γ/κ`. The printed claim "`δ > 1` is necessary and sufficient" is false:
  `κ = γ = 1`, `β = 1/2`, `δ = −5` is determinate (`ex_2_2_a_printed_false`); both roots leave
  the unit circle through `−1`. The Taylor principle holds for `δ ≥ 0`
  (`ex_2_2_a_taylor_principle`).

General tools: `nk_eig2` (eigenvalues of `2 × 2` matrices), `nkBothOut` and
`nk_out_of_bothOut`/`nk_root_of_not_bothOut` (both roots of `λ² − Tλ + D` outside the unit
circle iff `D > 1, 1 ∓ T + D > 0` or `D < −1, 1 ∓ T + D < 0`, given `T² ≥ 4`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Example 2.3.1: the system (2.16) -/

/-- The matrix `A` of (2.16), Miao, p. 55; the state is `(i_{t−1}, x_t, π_t)`. -/
noncomputable def nkA (β γ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1] 0 !![-1 / γ; 0] !![1, 1 / γ; 0, β]

/-- The matrix `B` of (2.16), Miao, p. 55. -/
noncomputable def nkB (κ ρ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![ρ] 0 0 !![1, 0; -κ, 1]

/-- The forcing matrix of (2.16): `(ε_t, −ε^x_t, 0)' = C(ε_t, ε^x_t)'`. -/
noncomputable def nkC : Matrix (Fin 1 ⊕ Fin 2) (Fin 2) ℝ :=
  Matrix.fromRows !![1, 0] !![0, -1; 0, 0]

/-- `A⁻¹` for (2.16). -/
noncomputable def nkAinv (β γ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1] 0 !![1 / γ; 0] !![1, -1 / (β * γ); 0, 1 / β]

/-- A `3 × 3` matrix with a predetermined first coordinate:
`[[ρ, 0, 0], [q, m₁₁, m₁₂], [0, m₂₁, m₂₂]]`. -/
noncomputable def nkSaddleW (ρ q m11 m12 m21 m22 : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![ρ] 0 !![q; 0] !![m11, m12; m21, m22]

/-- The matrix `W = A⁻¹B` of Example 2.3.1 (Miao, p. 55):
`[[ρ_r, 0, 0], [ρ_r/γ, 1 + κ/(βγ), −1/(βγ)], [0, −κ/β, 1/β]]`. -/
noncomputable def nkW (κ β γ ρ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  nkSaddleW ρ (ρ / γ) (1 + κ / (β * γ)) (-1 / (β * γ)) (-κ / β) (1 / β)

/-- The forcing matrix `A⁻¹C` of the reduced form of (2.16). -/
noncomputable def nkG (γ : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 2) ℝ :=
  Matrix.fromRows !![1, 0] !![1 / γ, -1; 0, 0]

/-- The state `(i_{t−1}, x_t, π_t)` of (2.16), with `ii t = i_{t−1}`. -/
def nkState (ii x π : ℕ → V) : ℕ → Fin 1 ⊕ Fin 2 → V :=
  fun t => Sum.elim (fun _ => ii t) ![x t, π t]

/-- The shocks `(ε_t, ε^x_t)`. -/
def nkShock (ε εx : ℕ → V) : ℕ → Fin 2 → V :=
  fun t => ![ε t, εx t]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem nk_sumElim_eq_iff {a a' b b' c c' : V} :
    Sum.elim (fun _ : Fin 1 => a) ![b, c] = Sum.elim (fun _ : Fin 1 => a') ![b', c'] ↔
      a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨congrFun h (Sum.inl 0), congrFun h (Sum.inr 0), congrFun h (Sum.inr 1)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem nk_matAct_A (β γ : ℝ) (a b c : V) :
    matAct (nkA β γ) (Sum.elim (fun _ : Fin 1 => a) ![b, c]) =
      Sum.elim (fun _ : Fin 1 => a) ![-(γ⁻¹ • a) + (b + γ⁻¹ • c), β • c] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [matAct, nkA, Fintype.sum_sum_type, Fin.sum_univ_two, neg_div, neg_smul]

theorem nk_matAct_B (κ ρ : ℝ) (a b c : V) :
    matAct (nkB κ ρ) (Sum.elim (fun _ : Fin 1 => a) ![b, c]) =
      Sum.elim (fun _ : Fin 1 => ρ • a) ![b, -(κ • b) + c] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [matAct, nkB, Fintype.sum_sum_type, Fin.sum_univ_two, neg_smul]

theorem nk_matAct_C (e ex : V) :
    matAct nkC ![e, ex] = Sum.elim (fun _ : Fin 1 => e) ![-ex, 0] := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [matAct, nkC, Fin.sum_univ_two]

/-- Miao, (2.16), p. 55: given that `i_t` is `F_t`-measurable, the Phillips curve (2.13)
`π_t = κx_t + βE_tπ_{t+1}`, the IS curve (2.14) `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1}) + ε^x_t`
and the rule (2.15) `i_t = ρ_ri_{t−1} + ε_t` hold iff `(i_{t−1}, x_t, π_t)` solves (2.16),
`AE_t(i_t, x_{t+1}, π_{t+1})' = B(i_{t−1}, x_t, π_t)' + (ε_t, −ε^x_t, 0)'`. -/
theorem eq_2_16 (E : CondExpSystem ℝ V) (κ β γ ρ : ℝ) (ii x π ε εx : ℕ → V)
    (hia : ∀ t, E.E t (ii (t + 1)) = ii (t + 1)) :
    ((∀ t, π t = κ • x t + β • E.E t (π (t + 1))) ∧
        (∀ t, x t = E.E t (x (t + 1)) - γ⁻¹ • (ii (t + 1) - E.E t (π (t + 1))) + εx t) ∧
        (∀ t, ii (t + 1) = ρ • ii t + ε t)) ↔
      IsRESolution E (nkA β γ) (nkB κ ρ) nkC (nkShock ε εx) (nkState ii x π) := by
  have hE : ∀ t, Evec E t (nkState ii x π (t + 1)) =
      Sum.elim (fun _ : Fin 1 => ii (t + 1)) ![E.E t (x (t + 1)), E.E t (π (t + 1))] := fun t => by
    funext i
    rcases i with i | i <;> fin_cases i
    · exact hia t
    · rfl
    · rfl
  have hS : ∀ (a b c : V) (a' b' c' : V), Sum.elim (fun _ : Fin 1 => a) ![b, c] +
      Sum.elim (fun _ : Fin 1 => a') ![b', c'] = Sum.elim (fun _ : Fin 1 => a + a') ![b + b',
        c + c'] := fun a b c a' b' c' => by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl
  have key : ∀ t, (π t = κ • x t + β • E.E t (π (t + 1)) ∧
      x t = E.E t (x (t + 1)) - γ⁻¹ • (ii (t + 1) - E.E t (π (t + 1))) + εx t ∧
      ii (t + 1) = ρ • ii t + ε t) ↔
      matAct (nkA β γ) (Evec E t (nkState ii x π (t + 1))) =
        matAct (nkB κ ρ) (nkState ii x π t) + matAct nkC (nkShock ε εx t) := fun t => by
    rw [hE t]
    simp only [nkState, nkShock]
    rw [nk_matAct_A, nk_matAct_B, nk_matAct_C, hS, nk_sumElim_eq_iff]
    constructor
    · rintro ⟨h13, h14, h15⟩
      refine ⟨h15, ?_, ?_⟩
      · linear_combination (norm := module) -h14
      · linear_combination (norm := module) -h13
    · rintro ⟨h15, h14, h13⟩
      refine ⟨?_, ?_, h15⟩
      · linear_combination (norm := module) -h13
      · linear_combination (norm := module) -h14
  unfold IsRESolution
  simp only [← key, forall_and]

/-- Miao, p. 55: the inverse of `A` in (2.16). -/
theorem nkA_mul_inv {β γ : ℝ} (hβ : β ≠ 0) (hγ : γ ≠ 0) : nkA β γ * nkAinv β γ = 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [nkA, nkAinv, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    field_simp <;> ring1

/-- Miao, p. 55, checked: `A⁻¹ = [[1, 0, 0], [1/γ, 1, −1/(βγ)], [0, 0, 1/β]]`,
`W = A⁻¹B = [[ρ_r, 0, 0], [ρ_r/γ, 1 + κ/(βγ), −1/(βγ)], [0, −κ/β, 1/β]]` (the printed `W`,
whose typesetting is garbled, has exactly these entries) and the reduced-form forcing is
`A⁻¹(ε_t, −ε^x_t, 0)' = (ε_t, ε_t/γ − ε^x_t, 0)'`. -/
theorem eq_2_16_W {κ β γ ρ : ℝ} (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    IsUnit (nkA β γ).det ∧ (nkA β γ)⁻¹ = nkAinv β γ ∧ (nkA β γ)⁻¹ * nkB κ ρ = nkW κ β γ ρ ∧
      (nkA β γ)⁻¹ * nkC = nkG γ := by
  have h1 := nkA_mul_inv hβ hγ
  have hinv : (nkA β γ)⁻¹ = nkAinv β γ := Matrix.inv_eq_right_inv h1
  refine ⟨Matrix.isUnit_det_of_right_inverse h1, hinv, ?_, ?_⟩ <;> rw [hinv]
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkAinv, nkB, nkW, nkSaddleW, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two] <;>
      field_simp
  · ext (i | i) j <;> fin_cases i <;> fin_cases j <;>
      simp [nkAinv, nkC, nkG, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

/-! ### Example 2.3.1: eigenvalues and a real block split of `W` -/

/-- The `s`-rows `(1, 0, 0)`, `(0, m₂₁, λ₂ − m₁₁)` and the `u`-row `(ℓ₀, m₂₁, λ₁ − m₁₁)`,
`ℓ₀ = m₂₁q/(λ₁ − ρ)` (left eigenvector for `λ₁`), of a real block split of `nkSaddleW`. -/
noncomputable def nkSaddleP (ρ q m11 m21 l1 l2 : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 1 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1; 0] !![0, 0; m21, l2 - m11] !![m21 * q / (l1 - ρ)] !![m21, l1 - m11]

/-- The inverse of `nkSaddleP`. -/
noncomputable def nkSaddleR (ρ q m11 m21 l1 l2 : ℝ) : Matrix (Fin 1 ⊕ Fin 2) (Fin 2 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![1, 0] !![0]
    !![(l2 - m11) * (m21 * q / (l1 - ρ)) / (m21 * (l1 - l2)), (l1 - m11) / (m21 * (l1 - l2));
      -(m21 * q / (l1 - ρ)) / (l1 - l2), -1 / (l1 - l2)]
    !![-(l2 - m11) / (m21 * (l1 - l2)); 1 / (l1 - l2)]

/-- A lower triangular real `2 × 2` matrix with diagonal entries inside the unit circle is
stable. -/
theorem nk_tri_stable {a b c : ℝ} (ha : |a| < 1) (hc : |c| < 1) :
    IsStableMatrix ((!![a, 0; b, c] : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofRealHom) := by
  intro μ hμ
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (a : ℂ) * w 0 = μ * w 0 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 0
  have e1 : (b : ℂ) * w 0 + c * w 1 = μ * w 1 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 1
  by_cases h0 : w 0 = 0
  · have h1' : w 1 ≠ 0 := fun h => hw.2 (funext fun i => by fin_cases i <;> simp [h0, h])
    rw [h0, mul_zero, zero_add] at e1
    rw [← mul_right_cancel₀ h1' e1, Complex.norm_real, Real.norm_eq_abs]
    exact hc
  · rw [← mul_right_cancel₀ h0 e0, Complex.norm_real, Real.norm_eq_abs]
    exact ha

/-- The eigenvalue of a `1 × 1` matrix `(l)` is `l`. -/
theorem nk_scalar_eig {l : ℝ} {μ : ℂ}
    (hμ : Module.End.HasEigenvalue
      (Matrix.toLin' ((!![l] : Matrix (Fin 1) (Fin 1) ℝ).map Complex.ofRealHom)) μ) :
    μ = l := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (l : ℂ) * w 0 = μ * w 0 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using congrFun h1 0
  have h0 : w 0 ≠ 0 := fun h => hw.2 (funext fun i => by fin_cases i; exact h)
  exact (mul_right_cancel₀ h0 e0).symm

/-- A real block split of the saddle matrix `nkSaddleW` (Miao, pp. 54–55): if `|ρ| < 1` and the
lower block has eigenvalues `λ₁ > 1` and `|λ₂| < 1` (`λ₁ + λ₂ = m₁₁ + m₂₂`,
`λ₁λ₂ = m₁₁m₂₂ − m₁₂m₂₁`) with `m₂₁ ≠ 0`, then `PWP⁻¹ = diag(J_s, J_u)` with
`J_s = [[ρ, 0], [m₂₁q, λ₂]]` (stable) and `J_u = (λ₁)`: `n_s = 2`, `n_u = 1`. -/
theorem nk_saddle_split {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (hρ : |ρ| < 1) (hl1 : 1 < l1)
    (hl2 : |l2| < 1) (ha : m21 ≠ 0) (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) :
    IsRealBlockSplit (nkSaddleW ρ q m11 m12 m21 m22) (nkSaddleP ρ q m11 m21 l1 l2)
      (nkSaddleR ρ q m11 m21 l1 l2) !![ρ, 0; m21 * q, l2] !![l1] := by
  have hd : l1 - l2 ≠ 0 := by
    have := (abs_lt.1 hl2).2
    linarith
  have hr : l1 - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  obtain rfl : m22 = l1 + l2 - m11 := by linarith
  obtain rfl : m12 = (m11 * (l1 + l2 - m11) - l1 * l2) / m21 := by
    field_simp
    linarith
  refine ⟨?_, ?_, ?_, nk_tri_stable hρ hl2, fun μ hμ => ?_⟩
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkSaddleP, nkSaddleR, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
      field_simp <;> ring1
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkSaddleP, nkSaddleR, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
      field_simp <;> ring1
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [nkSaddleP, nkSaddleW, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
      field_simp <;> ring1
  · rw [nk_scalar_eig hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hl1

/-- The eigenvalues of the saddle matrix `nkSaddleW` are `ρ`, `λ₁` and `λ₂` (Miao, p. 55). -/
theorem nk_saddle_eig {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue
      (Matrix.toLin' ((nkSaddleW ρ q m11 m12 m21 m22).map Complex.ofRealHom)) μ) :
    μ = ρ ∨ μ = l1 ∨ μ = l2 := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (ρ : ℂ) * w (Sum.inl 0) = μ * w (Sum.inl 0) := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, nkSaddleW] using congrFun h1 (Sum.inl 0)
  have e1 : (q : ℂ) * w (Sum.inl 0) + (m11 * w (Sum.inr 0) + m12 * w (Sum.inr 1)) =
      μ * w (Sum.inr 0) := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, nkSaddleW] using congrFun h1 (Sum.inr 0)
  have e2 : (m21 : ℂ) * w (Sum.inr 0) + m22 * w (Sum.inr 1) = μ * w (Sum.inr 1) := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, nkSaddleW] using congrFun h1 (Sum.inr 1)
  by_cases h0 : w (Sum.inl 0) = 0
  · right
    rw [h0, mul_zero, zero_add] at e1
    have hc : (μ - l1) * (μ - l2) = μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21) := by
      have hs : ((l1 : ℂ) + l2) = (m11 : ℂ) + m22 := by exact_mod_cast hsum
      have hp : ((l1 : ℂ) * l2) = (m11 : ℂ) * m22 - m12 * m21 := by exact_mod_cast hprod
      linear_combination (-μ) * hs + hp
    have hx : (μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21)) * w (Sum.inr 0) = 0 := by
      linear_combination (m22 - μ) * e1 - m12 * e2
    have hy : (μ ^ 2 - (m11 + m22) * μ + (m11 * m22 - m12 * m21)) * w (Sum.inr 1) = 0 := by
      linear_combination (m11 - μ) * e2 - m21 * e1
    have hne : w (Sum.inr 0) ≠ 0 ∨ w (Sum.inr 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hw.2
      funext i
      rcases i with i | i <;> fin_cases i
      · exact h0
      · exact hcon.1
      · exact hcon.2
    have hchar : (μ - l1) * (μ - l2) = 0 := by
      rw [hc]
      rcases hne with h | h
      · exact (mul_eq_zero.1 hx).resolve_right h
      · exact (mul_eq_zero.1 hy).resolve_right h
    rcases mul_eq_zero.1 hchar with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  · exact Or.inl (mul_right_cancel₀ h0 e0).symm

/-- `λ₁` is an eigenvalue of the saddle matrix, with eigenvector `(0, λ₁ − m₂₂, m₂₁)`. -/
theorem nk_saddle_eig_l1 {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (ha : m21 ≠ 0)
    (hsum : l1 + l2 = m11 + m22) (hprod : l1 * l2 = m11 * m22 - m12 * m21) :
    Module.End.HasEigenvalue
      (Matrix.toLin' ((nkSaddleW ρ q m11 m12 m21 m22).map Complex.ofRealHom)) l1 := by
  have h1 : l1 ^ 2 - (m11 + m22) * l1 + (m11 * m22 - m12 * m21) = 0 := by
    rw [← hsum, ← hprod]; ring
  have h1c : (l1 : ℂ) ^ 2 - (m11 + m22) * l1 + (m11 * m22 - m12 * m21) = 0 := by
    exact_mod_cast h1
  set v : Fin 1 ⊕ Fin 2 → ℂ := Sum.elim 0 ![(l1 : ℂ) - m22, m21]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h => ha ?_⟩
  · funext i
    rcases i with i | i <;> fin_cases i
    · simp [v, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, nkSaddleW]
    · have e : (m11 : ℂ) * (l1 - m22) + m12 * m21 = l1 * (l1 - m22) := by
        linear_combination -h1c
      simpa [v, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fin.sum_univ_two, nkSaddleW] using e
    · have e : (m21 : ℂ) * (l1 - m22) + m22 * m21 = l1 * m21 := by ring
      simpa [v, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fin.sum_univ_two, nkSaddleW] using e
  · have := congrFun h (Sum.inr 1)
    simpa [v] using this

/-- Miao, p. 55: exactly one eigenvalue of the saddle matrix lies outside the unit circle. -/
theorem nk_saddle_unstable {ρ q m11 m12 m21 m22 l1 l2 : ℝ} (hρ : |ρ| < 1) (hl1 : 1 < l1)
    (hl2 : |l2| < 1) (ha : m21 ≠ 0) (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) :
    {μ : ℂ | Module.End.HasEigenvalue
      (Matrix.toLin' ((nkSaddleW ρ q m11 m12 m21 m22).map Complex.ofRealHom)) μ ∧ 1 < ‖μ‖} =
      {(l1 : ℂ)} := by
  ext μ
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hμ, h1⟩
    rcases nk_saddle_eig hsum hprod hμ with h | h | h
    · rw [h, Complex.norm_real, Real.norm_eq_abs] at h1
      linarith
    · exact h
    · rw [h, Complex.norm_real, Real.norm_eq_abs] at h1
      linarith
  · rintro rfl
    refine ⟨nk_saddle_eig_l1 ha hsum hprod, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hl1

/-! ### Example 2.3.1: the New Keynesian model is indeterminate -/

/-- The trace `1 + 1/β + κ/(βγ)` of the jump block of `W` in Example 2.3.1. -/
noncomputable def nkTr (κ β γ : ℝ) : ℝ := 1 + κ / (β * γ) + 1 / β

/-- The unstable root `λ₁ = (T + √(T² − 4/β))/2` of `λ² − Tλ + 1/β` (Example 2.3.1). -/
noncomputable def nkLam1 (κ β γ : ℝ) : ℝ := (nkTr κ β γ + √(nkTr κ β γ ^ 2 - 4 / β)) / 2

/-- The stable root `λ₂ = (T − √(T² − 4/β))/2` of `λ² − Tλ + 1/β` (Example 2.3.1). -/
noncomputable def nkLam2 (κ β γ : ℝ) : ℝ := (nkTr κ β γ - √(nkTr κ β γ ^ 2 - 4 / β)) / 2

/-- Miao, p. 55: for `κ, β, γ > 0` the jump block of `W` has eigenvalues `λ₁ > 1` and
`0 < λ₂ < 1` (`β < 1` is not needed): its characteristic polynomial `λ² − Tλ + 1/β` is
negative at `λ = 1`. -/
theorem nk_lam {κ β γ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ) :
    nkLam1 κ β γ + nkLam2 κ β γ = (1 + κ / (β * γ)) + 1 / β ∧
      nkLam1 κ β γ * nkLam2 κ β γ = (1 + κ / (β * γ)) * (1 / β) - (-1 / (β * γ)) * (-κ / β) ∧
      0 < nkLam2 κ β γ ∧ nkLam2 κ β γ < 1 ∧ 1 < nkLam1 κ β γ := by
  have hk : 0 < κ / (β * γ) := by positivity
  have hib : 0 < 1 / β := by positivity
  have hD : 0 < nkTr κ β γ ^ 2 - 4 / β := by
    have e : nkTr κ β γ ^ 2 - 4 / β = (1 - 1 / β) ^ 2 + 2 * (1 + 1 / β) * (κ / (β * γ)) +
        (κ / (β * γ)) ^ 2 := by
      simp only [nkTr]; ring
    rw [e]
    positivity
  set s := √(nkTr κ β γ ^ 2 - 4 / β) with hs_def
  have hs : s ^ 2 = nkTr κ β γ ^ 2 - 4 / β := Real.sq_sqrt hD.le
  have hs0 : 0 < s := Real.sqrt_pos.2 hD
  have hsum : nkLam1 κ β γ + nkLam2 κ β γ = nkTr κ β γ := by
    simp only [nkLam1, nkLam2, ← hs_def]; ring
  have hprod : nkLam1 κ β γ * nkLam2 κ β γ = 1 / β := by
    simp only [nkLam1, nkLam2, ← hs_def]
    linear_combination (-1 / 4 : ℝ) * hs
  have hlt : nkLam2 κ β γ < nkLam1 κ β γ := by
    simp only [nkLam1, nkLam2, ← hs_def]; linarith
  have hT : nkTr κ β γ = 1 + κ / (β * γ) + 1 / β := rfl
  have hp1 : (1 - nkLam1 κ β γ) * (1 - nkLam2 κ β γ) = -(κ / (β * γ)) := by
    linear_combination -hsum + hprod - hT
  have h1 : 1 < nkLam1 κ β γ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 (hlt.trans_le h).le)]
  have h2 : nkLam2 κ β γ < 1 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (sub_nonneg.2 h1.le) (sub_nonneg.2 h)]
  have h3 : 0 < nkLam2 κ β γ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (zero_le_one.trans h1.le) h]
  refine ⟨hsum, ?_, h3, h2, h1⟩
  rw [hprod]
  field_simp
  ring

/-- **Example 2.3.1** (Miao, p. 55): a real block split of `W` with `n_s = 2` and `n_u = 1`
(stable block `[[ρ_r, 0], [−κρ_r/(βγ), λ₂]]`, unstable block `(λ₁)`). There are two jump
variables (`x_t`, `π_t`), so the order condition `n_u = n_y` of Blanchard and Kahn fails. -/
theorem example_2_3_1_split {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ)
    (hρ : |ρ| < 1) :
    IsRealBlockSplit (nkW κ β γ ρ)
      (nkSaddleP ρ (ρ / γ) (1 + κ / (β * γ)) (-κ / β) (nkLam1 κ β γ) (nkLam2 κ β γ))
      (nkSaddleR ρ (ρ / γ) (1 + κ / (β * γ)) (-κ / β) (nkLam1 κ β γ) (nkLam2 κ β γ))
      !![ρ, 0; -κ / β * (ρ / γ), nkLam2 κ β γ] !![nkLam1 κ β γ] ∧
      Fintype.card (Fin 1) < Fintype.card (Fin 2) := by
  obtain ⟨hsum, hprod, h3, h2, h1⟩ := nk_lam hκ hβ hγ
  refine ⟨nk_saddle_split hρ h1 (abs_lt.2 ⟨by linarith, h2⟩)
    (div_ne_zero (neg_ne_zero.2 hκ.ne') hβ.ne') hsum hprod,
    by simp⟩

/-- **Example 2.3.1** (Miao, p. 55): for `κ, β, γ > 0` and `|ρ_r| < 1`, exactly one eigenvalue of
`W` lies outside the unit circle, namely `λ₁`; the others are `ρ_r` and `λ₂ ∈ (0, 1)`. -/
theorem example_2_3_1_eigen {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ)
    (hρ : |ρ| < 1) :
    {μ : ℂ | Module.End.HasEigenvalue
      (Matrix.toLin' ((nkW κ β γ ρ).map Complex.ofRealHom)) μ ∧ 1 < ‖μ‖} =
      {(nkLam1 κ β γ : ℂ)} ∧
    (∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' ((nkW κ β γ ρ).map Complex.ofRealHom)) μ →
        μ = ρ ∨ μ = nkLam1 κ β γ ∨ μ = nkLam2 κ β γ) ∧
    1 < nkLam1 κ β γ ∧ 0 < nkLam2 κ β γ ∧ nkLam2 κ β γ < 1 := by
  obtain ⟨hsum, hprod, h3, h2, h1⟩ := nk_lam hκ hβ hγ
  exact ⟨nk_saddle_unstable hρ h1 (abs_lt.2 ⟨by linarith, h2⟩)
    (div_ne_zero (neg_ne_zero.2 hκ.ne') hβ.ne') hsum hprod,
    fun μ hμ => nk_saddle_eig hsum hprod hμ, h1, h3, h2⟩

/-- **Example 2.3.1** (Miao, pp. 54–55): the exogenous rule `i_t = ρ_ri_{t−1} + ε_t` makes the
equilibrium indeterminate. For `κ, β, γ > 0`, `|ρ_r| < 1`, every `F_0`-measurable `i_{−1}` and
every stable adapted shock process `(ε_t, ε^x_t)`, the system (2.16) has infinitely many stable
adapted solutions with `i` predetermined and initial value `i_{−1}` (provided `V` contains a
nonzero `F_0`-measurable `w`; the extra solutions add `cλ₂ᵗw` along the stable eigenvector). -/
theorem example_2_3_1_indeterminate [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ ρ : ℝ}
    (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ) (hρ : |ρ| < 1) (i₀ : V) (hi₀ : E.E 0 i₀ = i₀)
    {z : ℕ → Fin 2 → V} (hz : IsStableProc z) (hza : IsAdaptedV E z) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    {X : ℕ → Fin 1 ⊕ Fin 2 → V | IsRESolution E (nkA β γ) (nkB κ ρ) nkC z X ∧
      IsAdaptedV E X ∧ IsPredeterminedBK E (fun t => X t ∘ Sum.inl) ∧ IsStableProc X ∧
      X 0 (Sum.inl 0) = i₀}.Infinite := by
  obtain ⟨hdetA, -, hW, hG⟩ := eq_2_16_W (κ := κ) (ρ := ρ) hβ.ne' hγ.ne'
  obtain ⟨hS, hcard⟩ := example_2_3_1_split hκ hβ hγ hρ
  have hQ : (nkSaddleP ρ (ρ / γ) (1 + κ / (β * γ)) (-κ / β) (nkLam1 κ β γ)
      (nkLam2 κ β γ)).toBlocks₂₂ * !![1 / (-κ / β); 0] = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [nkSaddleP, Matrix.toBlocks_fromBlocks₂₂]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  have hinf := theorem_1_4_3_lt_exists_stoch E hS hcard _ hQ (nkG γ) hz hza (fun _ => i₀)
    (fun _ => hi₀) hw hw0
  refine hinf.mono ?_
  rintro X ⟨⟨he, ha, hp, hs⟩, hX0⟩
  refine ⟨?_, ha, hp, hs, congrFun hX0 0⟩
  rw [eq_2_11_iff E _ _ _ hdetA z X, hW, hG]
  exact he

/-- **Example 2.3.1**, deterministic case (Miao, p. 55): with `E_t = id` on `ℝ` (no
uncertainty), for every `i_{−1}` and every bounded shock sequence there are infinitely many
bounded solutions of (2.16) with initial value `i_{−1}`. -/
theorem example_2_3_1_indeterminate_det {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hγ : 0 < γ)
    (hρ : |ρ| < 1) (i₀ : ℝ) {z : ℕ → Fin 2 → ℝ} (hz : IsStableSeq z) :
    {X : ℕ → Fin 1 ⊕ Fin 2 → ℝ | IsSolution (nkA β γ) (nkB κ ρ) nkC z X ∧ IsStableSeq X ∧
      X 0 (Sum.inl 0) = i₀}.Infinite := by
  have hz' : IsStableProc z := by
    rw [bkS_isStableProc_iff, ← isStableSeq_iff_exists_le]
    exact hz
  refine (example_2_3_1_indeterminate (bkS_trivial ℝ) hκ hβ hγ hρ i₀ rfl hz' (fun _ _ => rfl)
    one_ne_zero rfl).mono ?_
  rintro X ⟨he, ha, hp, hs, h0⟩
  have := (certainty_equivalence _ _ _ z X).1 ⟨he, ha, hp, hs⟩
  exact ⟨this.1, this.2, h0⟩

/-! ### Exercise 2.2: interest rate rules and determinacy -/

/-- Both roots of `λ² − Tλ + D` lie outside the unit circle (the Schur–Cohn conditions for the
reciprocal polynomial): `D > 1, 1 − T + D > 0, 1 + T + D > 0`, or
`D < −1, 1 − T + D < 0, 1 + T + D < 0`. -/
def nkBothOut (T D : ℝ) : Prop :=
  (1 < D ∧ 0 < 1 - T + D ∧ 0 < 1 + T + D) ∨ (D < -1 ∧ 1 - T + D < 0 ∧ 1 + T + D < 0)

/-- The eigenvalues of a real `2 × 2` matrix are roots of `μ² − (tr M)μ + det M`. -/
theorem nk_eig2 (M : Matrix (Fin 2) (Fin 2) ℝ) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (M.map Complex.ofRealHom)) μ) :
    μ ^ 2 - ((M 0 0 + M 1 1 : ℝ) : ℂ) * μ + ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ) = 0 := by
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have h1 := Module.End.mem_eigenspace_iff.1 hw.1
  have e0 : (M 0 0 : ℂ) * w 0 + M 0 1 * w 1 = μ * w 0 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 0
  have e1 : (M 1 0 : ℂ) * w 0 + M 1 1 * w 1 = μ * w 1 := by
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 1
  have hx : (μ ^ 2 - ((M 0 0 + M 1 1 : ℝ) : ℂ) * μ + ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ))
      * w 0 = 0 := by
    push_cast
    linear_combination (M 1 1 - μ) * e0 - M 0 1 * e1
  have hy : (μ ^ 2 - ((M 0 0 + M 1 1 : ℝ) : ℂ) * μ + ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ))
      * w 1 = 0 := by
    push_cast
    linear_combination (M 0 0 - μ) * e1 - M 1 0 * e0
  by_cases h0 : w 0 = 0
  · have h1' : w 1 ≠ 0 := fun h => hw.2 (funext fun i => by fin_cases i <;> simp [h0, h])
    exact (mul_eq_zero.1 hy).resolve_right h1'
  · exact (mul_eq_zero.1 hx).resolve_right h0

/-- Under `nkBothOut T D`, every complex root of `μ² − Tμ + D` has modulus greater than one. -/
theorem nk_out_of_bothOut {T D : ℝ} (h : nkBothOut T D) {μ : ℂ}
    (hμ : μ ^ 2 - (T : ℂ) * μ + (D : ℂ) = 0) : 1 < ‖μ‖ := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, μ = a + b * Complex.I := ⟨μ.re, μ.im, (Complex.re_add_im μ).symm⟩
  have hc : (((a ^ 2 - b ^ 2 - T * a + D : ℝ) : ℂ) + ((2 * a * b - T * b : ℝ) : ℂ) * Complex.I)
      = 0 := by
    push_cast
    linear_combination hμ - b ^ 2 * Complex.I_sq
  have hr : a ^ 2 - b ^ 2 - T * a + D = 0 := by
    have := congrArg Complex.re hc
    rwa [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
  have hi : 2 * a * b - T * b = 0 := by
    have := congrArg Complex.im hc
    rwa [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, zero_add, Complex.zero_im] at this
  have hn : ‖(a : ℂ) + b * Complex.I‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  suffices hs : 1 < a ^ 2 + b ^ 2 by
    by_contra hle
    push Not at hle
    have : ‖(a : ℂ) + b * Complex.I‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hle
    linarith
  by_cases hb : b = 0
  · subst hb
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, add_zero]
      at hr ⊢
    by_contra hle
    push Not at hle
    have ha1 : a ≤ 1 := by nlinarith
    have ha2 : -1 ≤ a := by nlinarith
    rcases h with ⟨hD, h1, h2⟩ | ⟨hD, h1, h2⟩
    · -- the other root `b' = T − a` satisfies `ab' = D`, `(1 − a)(1 − b') = 1 − T + D`
      have hp1 : (1 - a) * (1 - (T - a)) = 1 - T + D := by linear_combination -hr
      have hp2 : (1 + a) * (1 + (T - a)) = 1 + T + D := by linear_combination -hr
      have hab : a * (T - a) = D := by linear_combination -hr
      have hb1 : T - a < 1 := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 ha1) (sub_nonpos.2 hc)]
      have hb2 : -1 < T - a := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (neg_le_iff_add_nonneg.1 ha2)
          (by linarith : 1 + (T - a) ≤ 0)]
      nlinarith [mul_le_mul_of_nonneg_left (abs_le.2 ⟨ha2, ha1⟩) (abs_nonneg (T - a)),
        abs_mul a (T - a), le_abs_self (a * (T - a)), abs_lt.2 ⟨hb2, hb1⟩, abs_nonneg a]
    · have hp1 : (1 - a) * (1 - (T - a)) = 1 - T + D := by linear_combination -hr
      have hp2 : (1 + a) * (1 + (T - a)) = 1 + T + D := by linear_combination -hr
      have ha1' : a < 1 := by
        rcases ha1.lt_or_eq with h | h
        · exact h
        · subst h; linarith
      have hb1 : 1 < T - a := by
        by_contra hc
        push Not at hc
        nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hc)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a) (by linarith : (0 : ℝ) ≤ 1 + (T - a))]
  · have ha : a = T / 2 := by
      have : b * (2 * a - T) = 0 := by linear_combination hi
      have := (mul_eq_zero.1 this).resolve_left hb
      linarith
    have hbb : b ^ 2 = D - T ^ 2 / 4 := by rw [ha] at hr; linear_combination -hr
    have hb2 : 0 < b ^ 2 := by positivity
    rcases h with ⟨hD, -, -⟩ | ⟨hD, -, -⟩
    · nlinarith
    · nlinarith

/-- If `T² ≥ 4` and the roots of `λ² − Tλ + D` are not both outside the unit circle, one of them
is real and lies in `[−1, 1]`. -/
theorem nk_root_of_not_bothOut {T D : ℝ} (hT : 4 ≤ T ^ 2) (h : ¬ nkBothOut T D) :
    ∃ r : ℝ, |r| ≤ 1 ∧ r ^ 2 - T * r + D = 0 := by
  by_cases hd : T ^ 2 - 4 * D < 0
  · exact absurd (Or.inl ⟨by nlinarith, by nlinarith [sq_nonneg (2 - T)],
      by nlinarith [sq_nonneg (2 + T)]⟩) h
  push Not at hd
  set s := √(T ^ 2 - 4 * D)
  have hs : s ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hd
  have hr1 : ((T - s) / 2) ^ 2 - T * ((T - s) / 2) + D = 0 := by linear_combination hs / 4
  have hr2 : ((T + s) / 2) ^ 2 - T * ((T + s) / 2) + D = 0 := by linear_combination hs / 4
  by_contra hall
  push Not at hall
  have h1 : 1 < |(T - s) / 2| := by
    by_contra hc; push Not at hc; exact hall _ hc hr1
  have h2 : 1 < |(T + s) / 2| := by
    by_contra hc; push Not at hc; exact hall _ hc hr2
  have hD : D = ((T - s) / 2) * ((T + s) / 2) := by linear_combination hs / 4
  have hp1 : 1 - T + D = (1 - (T - s) / 2) * (1 - (T + s) / 2) := by rw [hD]; ring
  have hp2 : 1 + T + D = (1 + (T - s) / 2) * (1 + (T + s) / 2) := by rw [hD]; ring
  apply h
  rcases lt_abs.1 h1 with h1 | h1 <;> rcases lt_abs.1 h2 with h2 | h2
  · exact Or.inl ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩
  · exact Or.inr ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩
  · exact Or.inr ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩
  · exact Or.inl ⟨by rw [hD]; nlinarith, by rw [hp1]; nlinarith, by rw [hp2]; nlinarith⟩

/-- An eigenvector of a real `2 × 2` matrix for a real root `r` of its characteristic
polynomial: `(r − M₁₁, M₁₀)`. -/
theorem nk_eigvec2 (M : Matrix (Fin 2) (Fin 2) ℝ) {r : ℝ}
    (hr : r ^ 2 - (M 0 0 + M 1 1) * r + (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0) :
    M *ᵥ ![r - M 1 1, M 1 0] = r • ![r - M 1 1, M 1 0] := by
  funext i
  fin_cases i
  · have e : M 0 0 * (r - M 1 1) + M 0 1 * M 1 0 = r * (r - M 1 1) := by
      linear_combination -hr
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using e
  · have e : M 1 0 * (r - M 1 1) + M 1 1 * M 1 0 = r * M 1 0 := by ring
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using e

/-- **Jump-only `2 × 2` systems, determinacy** (Miao, pp. 53–54 with `n_k = 0`): if both roots
of the characteristic polynomial of `M` lie outside the unit circle, then for every stable
adapted `c`, `E_tX_{t+1} = MX_t + c_t` has exactly one stable adapted solution. -/
theorem nk_jump2_unique [CompleteSpace V] (E : CondExpSystem ℝ V) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (h : nkBothOut (M 0 0 + M 1 1) (M 0 0 * M 1 1 - M 0 1 * M 1 0)) {c : ℕ → Fin 2 → V}
    (hc : IsStableProc c) (hca : IsAdaptedV E c) :
    ∃! X : ℕ → Fin 2 → V, (∀ t, Evec E t (X (t + 1)) = matAct M (X t) + c t) ∧
      IsAdaptedV E X ∧ IsStableProc X := by
  have hev : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' (M.map Complex.ofRealHom)) μ → 1 < ‖μ‖ :=
    fun μ hμ => nk_out_of_bothOut h (nk_eig2 M hμ)
  obtain ⟨hdet, hinv⟩ := isStableMatrix_inv M hev
  obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
  exact bkS_jump_unique E hdet hKa hc hca

/-- **Jump-only `2 × 2` systems, indeterminacy**: if `M₁₀ ≠ 0`, `(tr M)² ≥ 4` and the roots are
not both outside the unit circle, the homogeneous system `E_tX_{t+1} = MX_t` has a nonzero
stable adapted solution `rᵗvw` (`|r| ≤ 1` a real root, `v` its eigenvector, `w ≠ 0`
`F_0`-measurable). -/
theorem nk_jump2_nonunique (E : CondExpSystem ℝ V) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM10 : M 1 0 ≠ 0) (hT : 4 ≤ (M 0 0 + M 1 1) ^ 2)
    (h : ¬ nkBothOut (M 0 0 + M 1 1) (M 0 0 * M 1 1 - M 0 1 * M 1 0)) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    ∃ X : ℕ → Fin 2 → V, X ≠ 0 ∧ (∀ t, Evec E t (X (t + 1)) = matAct M (X t)) ∧
      IsAdaptedV E X ∧ IsStableProc X := by
  obtain ⟨r, hr1, hr⟩ := nk_root_of_not_bothOut hT h
  set v : Fin 2 → ℝ := ![r - M 1 1, M 1 0]
  have hv := nk_eigvec2 M (r := r) (by linear_combination hr)
  have hwt : ∀ t, E.E t w = w := fun t => by rw [← hw0, E.tower_ge_apply (Nat.zero_le t)]
  set X : ℕ → Fin 2 → V := fun t i => (r ^ t * v i) • w
  have hXa : ∀ s t, Evec E s (X t) = X t := fun s t => funext fun i => by
    simp only [X, Evec, map_smul, hwt]
  have hrec : ∀ t, matAct M (X t) = X (t + 1) := fun t => by
    funext i
    have hvi := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hvi
    simp only [matAct, X, smul_smul, ← Finset.sum_smul]
    congr 1
    calc ∑ j, M i j * (r ^ t * v j) = r ^ t * ∑ j, M i j * v j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = r ^ (t + 1) * v i := by rw [hvi, pow_succ]; ring
  refine ⟨X, fun h0 => ?_, fun t => by rw [hXa, hrec], (bkS_isAdaptedV_iff E X).2 fun t =>
    hXa t t, ⟨‖v‖ * ‖w‖ + 1, by positivity, fun t i => ?_⟩⟩
  · have := congrFun (congrFun h0 0) 1
    simp only [X, v, pow_zero, one_mul, Pi.zero_apply] at this
    exact smul_ne_zero hM10 hw this
  · simp only [X]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr1
    have h2 : |v i| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
    nlinarith [abs_nonneg (v i), norm_nonneg w, pow_nonneg (abs_nonneg r) t,
      mul_le_mul h1 h2 (abs_nonneg _) zero_le_one]

/-- The jump matrix `W` of the Taylor-rule model of Exercise 2.2 with state `(x_t, π_t)`:
`W = [[1 + δ_x/γ + κ/(βγ), δ_π/γ − 1/(βγ)], [−κ/β, 1/β]]`. -/
noncomputable def nkWT (κ β γ δπ δx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + δx / γ + κ / (β * γ), δπ / γ - 1 / (β * γ); -κ / β, 1 / β]

/-- Exercise 2.2: the model (2.13)–(2.14) with the Taylor rule `i_t = δ_ππ_t + δ_xx_t + ε_t`,
for the state `X_t = (x_t, π_t)`. -/
def nkTaylorEqm (E : CondExpSystem ℝ V) (κ β γ δπ δx : ℝ) (ε εx : ℕ → V)
    (X : ℕ → Fin 2 → V) : Prop :=
  ∀ t, X t 1 = κ • X t 0 + β • E.E t (X (t + 1) 1) ∧
    X t 0 = E.E t (X (t + 1) 0) - γ⁻¹ • ((δπ • X t 1 + δx • X t 0 + ε t) - E.E t (X (t + 1) 1))
      + εx t

/-- Exercise 2.2: the Taylor-rule model has a unique stable equilibrium for every stable adapted
pair of shocks `(ε_t, ε^x_t)`. -/
def nkDeterminate (E : CondExpSystem ℝ V) (κ β γ δπ δx : ℝ) : Prop :=
  ∀ ε εx : ℕ → V, (∃ C, ∀ t, ‖ε t‖ ≤ C) → (∃ C, ∀ t, ‖εx t‖ ≤ C) →
    (∀ t, E.E t (ε t) = ε t) → (∀ t, E.E t (εx t) = εx t) →
    ∃! X, nkTaylorEqm E κ β γ δπ δx ε εx X ∧ IsAdaptedV E X ∧ IsStableProc X

/-- Exercise 2.2 (Miao, pp. 82–83): substituting the Taylor rule, (2.13)–(2.14) are the
jump-only system `E_tX_{t+1} = WX_t + (γ⁻¹ε_t − ε^x_t, 0)'`, `W = nkWT`. -/
theorem nk_taylor_iff (E : CondExpSystem ℝ V) {κ β γ : ℝ} (δπ δx : ℝ) (hβ : β ≠ 0)
    (ε εx : ℕ → V) (X : ℕ → Fin 2 → V) :
    nkTaylorEqm E κ β γ δπ δx ε εx X ↔
      ∀ t, Evec E t (X (t + 1)) = matAct (nkWT κ β γ δπ δx) (X t) + ![γ⁻¹ • ε t - εx t, 0] := by
  refine forall_congr' fun t => ?_
  set a := E.E t (X (t + 1) 0)
  set b := E.E t (X (t + 1) 1)
  set x := X t 0
  set p := X t 1
  have hv : Evec E t (X (t + 1)) = ![a, b] := funext fun i => by fin_cases i <;> rfl
  have hm : matAct (nkWT κ β γ δπ δx) (X t) = ![(1 + δx / γ + κ / (β * γ)) • x +
      (δπ / γ - 1 / (β * γ)) • p, (-κ / β) • x + (1 / β) • p] := funext fun i => by
    fin_cases i <;> simp [matAct, nkWT, Fin.sum_univ_two, x, p]
  have hvec : ∀ u u' v' v'' : V, ![u, u'] = ![v', v''] ↔ u = v' ∧ u' = v'' := fun u u' v' v'' =>
    ⟨fun h => ⟨congrFun h 0, congrFun h 1⟩, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
  have hadd : ∀ u u' v' v'' : V, ![u, u'] + ![v', v''] = ![u + v', u' + v''] :=
    fun u u' v' v'' => funext fun i => by fin_cases i <;> rfl
  rw [hv, hm, hadd, hvec]
  have e1 : β * (-κ / β) = -κ := by field_simp
  have e2 : β * (1 / β) = 1 := by field_simp
  constructor
  · rintro ⟨h1, h2⟩
    have hb : b = β⁻¹ • (p - κ • x) := by
      rw [h1, add_sub_cancel_left, inv_smul_smul₀ hβ]
    have ha : a = x + γ⁻¹ • ((δπ • p + δx • x + ε t) - b) - εx t := by
      linear_combination (norm := module) -h2
    refine ⟨?_, ?_⟩
    · rw [ha, hb]
      module
    · rw [hb, add_zero]
      module
  · rintro ⟨h1, h2⟩
    rw [add_zero] at h2
    refine ⟨?_, ?_⟩
    · rw [h2, smul_add, smul_smul, smul_smul, e1, e2]
      module
    · rw [h1, h2]
      module

/-- Exercise 2.2: the determinacy conditions for `nkWT`. With `κ, γ > 0`, `0 < β < 1` and
`δ_x ≥ 0`, both eigenvalues of `W` lie outside the unit circle iff
`κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`. -/
theorem nk_bothOut_WT {κ β γ δπ δx : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hδx : 0 ≤ δx) :
    nkBothOut (nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1)
        (nkWT κ β γ δπ δx 0 0 * nkWT κ β γ δπ δx 1 1 -
          nkWT κ β γ δπ δx 0 1 * nkWT κ β γ δπ δx 1 0) ↔
      (0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0) := by
  have hP : 0 < β * γ := mul_pos hβ0 hγ
  have eT : nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1 =
      1 + δx / γ + κ / (β * γ) + 1 / β := by simp [nkWT]
  have eD : nkWT κ β γ δπ δx 0 0 * nkWT κ β γ δπ δx 1 1 -
      nkWT κ β γ δπ δx 0 1 * nkWT κ β γ δπ δx 1 0 = (γ + δx + κ * δπ) / (β * γ) := by
    simp only [nkWT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  have k1 : 1 - (1 + δx / γ + κ / (β * γ) + 1 / β) + (γ + δx + κ * δπ) / (β * γ) =
      (κ * (δπ - 1) + (1 - β) * δx) / (β * γ) := by
    field_simp
    ring
  have k2 : 1 + (1 + δx / γ + κ / (β * γ) + 1 / β) + (γ + δx + κ * δπ) / (β * γ) =
      (κ * (1 + δπ) + (1 + β) * (2 * γ + δx)) / (β * γ) := by
    field_simp
    ring
  rw [eT, eD, nkBothOut, k1, k2]
  simp only [lt_div_iff₀ hP, div_lt_iff₀ hP, one_mul, zero_mul, neg_one_mul]
  have hbd : 0 ≤ β * δx := mul_nonneg hβ0.le hδx
  constructor
  · rintro (⟨-, h, -⟩ | ⟨-, -, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨by nlinarith, h, by nlinarith⟩
    · exact Or.inr ⟨by nlinarith, by nlinarith, h⟩

/-- The trace of `nkWT` exceeds `2` (so `T² ≥ 4`) when `0 < β < 1`, `κ, γ > 0`, `δ_x ≥ 0`. -/
theorem nk_WT_trace {κ β γ δπ δx : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (hδx : 0 ≤ δx) : 4 ≤ (nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1) ^ 2 := by
  have eT : nkWT κ β γ δπ δx 0 0 + nkWT κ β γ δπ δx 1 1 =
      1 + δx / γ + κ / (β * γ) + 1 / β := by simp [nkWT]
  have h1 : 1 < 1 / β := one_lt_one_div hβ0 hβ1
  have h2 : 0 ≤ δx / γ := div_nonneg hδx hγ.le
  have h3 : 0 < κ / (β * γ) := by positivity
  rw [eT]
  nlinarith

/-- **Exercise 2.2, sufficiency** (Miao, pp. 82–83): with `κ, γ > 0`, `0 < β < 1`, `δ_x ≥ 0`, if
`κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`, the Taylor-rule model has a
unique stable equilibrium for every stable adapted pair of shocks. -/
theorem ex_2_2_suff [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδx : 0 ≤ δx)
    (hc : 0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0) :
    nkDeterminate E κ β γ δπ δx := by
  rintro ε εx ⟨C1, h1⟩ ⟨C2, h2⟩ ha1 ha2
  set c : ℕ → Fin 2 → V := fun t => ![γ⁻¹ • ε t - εx t, 0]
  have hC1 : 0 ≤ C1 := (norm_nonneg _).trans (h1 0)
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (h2 0)
  have hcs : IsStableProc c := by
    refine ⟨|γ⁻¹| * C1 + C2 + 1, by positivity, fun t i => ?_⟩
    fin_cases i
    · simp only [c]
      calc ‖γ⁻¹ • ε t - εx t‖ ≤ ‖γ⁻¹ • ε t‖ + ‖εx t‖ := norm_sub_le _ _
        _ = |γ⁻¹| * ‖ε t‖ + ‖εx t‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ |γ⁻¹| * C1 + C2 := add_le_add (mul_le_mul_of_nonneg_left (h1 t) (abs_nonneg _)) (h2 t)
        _ < |γ⁻¹| * C1 + C2 + 1 := lt_add_one _
    · simp only [c]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_zero]
      positivity
  have hca : IsAdaptedV E c := fun t i => by
    fin_cases i
    · simp only [c]
      simp only [Fin.zero_eta, Matrix.cons_val_zero, map_sub, map_smul, ha1, ha2]
    · simp only [c]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_zero]
  obtain h := nk_jump2_unique E (nkWT κ β γ δπ δx) ((nk_bothOut_WT hκ hβ0 hβ1 hγ hδx).2 hc)
    hcs hca
  refine (existsUnique_congr fun X => ?_).2 h
  rw [nk_taylor_iff E δπ δx hβ0.ne' ε εx X]

/-- **Exercise 2.2, necessity** (Miao, pp. 82–83): with `κ, γ > 0`, `0 < β < 1`, `δ_x ≥ 0`, if the
Taylor-rule model has a unique stable equilibrium for all stable adapted shocks, then
`κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`. Otherwise a root `r` of
the jump matrix with `|r| ≤ 1` gives, for zero shocks, the second stable equilibrium `rᵗvw`
(`w ≠ 0` `F_0`-measurable). -/
theorem ex_2_2_nec (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hγ : 0 < γ) (hδx : 0 ≤ δx) {w : V} (hw : w ≠ 0) (hw0 : E.E 0 w = w)
    (hdet : nkDeterminate E κ β γ δπ δx) :
    0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0 := by
  by_contra hc
  have hnb := fun hb => hc ((nk_bothOut_WT (δπ := δπ) hκ hβ0 hβ1 hγ hδx).1 hb)
  have hM10 : nkWT κ β γ δπ δx 1 0 ≠ 0 := by
    have e : nkWT κ β γ δπ δx 1 0 = -κ / β := by simp [nkWT]
    rw [e]
    exact div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  obtain ⟨X, hX0, hXe, hXa, hXs⟩ := nk_jump2_nonunique E (nkWT κ β γ δπ δx) hM10
    (nk_WT_trace hκ hβ0 hβ1 hγ hδx) hnb hw hw0
  obtain ⟨Y, -, hYu⟩ := hdet (fun _ => 0) (fun _ => 0) ⟨0, fun _ => by simp⟩
    ⟨0, fun _ => by simp⟩ (fun _ => map_zero _) (fun _ => map_zero _)
  have hz : (![γ⁻¹ • (0 : V) - 0, 0] : Fin 2 → V) = 0 := by
    funext i
    fin_cases i <;> simp
  have h1 := hYu X ⟨(nk_taylor_iff E δπ δx hβ0.ne' _ _ X).2 fun t => by
    rw [hXe t, hz, add_zero], hXa, hXs⟩
  have h2 := hYu 0 ⟨(nk_taylor_iff E δπ δx hβ0.ne' _ _ 0).2 fun t => by
    rw [Pi.zero_apply, Pi.zero_apply, bkS_Evec_zero, bkS_matAct_zero, hz, add_zero],
    fun _ _ => map_zero _, ⟨1, one_pos, fun _ _ => by simp⟩⟩
  exact hX0 (h1.trans h2.symm)

/-- **Exercise 2.2(b)**, exact conditions (Miao, p. 83): for the Taylor rule
`i_t = δ_ππ_t + δ_xx_t + ε_t` with `κ, γ > 0`, `0 < β < 1` and `δ_x ≥ 0` (and `V` containing a
nonzero `F_0`-measurable `w`), there is a unique stable equilibrium for all stable adapted shocks
iff `κ(δ_π − 1) + (1 − β)δ_x > 0` or `κ(1 + δ_π) + (1 + β)(2γ + δ_x) < 0`. The second branch (both
roots below `−1`, for a strongly negative `δ_π`) is missing from the usual statement. -/
theorem ex_2_2_b_exact [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδx : 0 ≤ δx) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    nkDeterminate E κ β γ δπ δx ↔
      (0 < κ * (δπ - 1) + (1 - β) * δx ∨ κ * (1 + δπ) + (1 + β) * (2 * γ + δx) < 0) :=
  ⟨ex_2_2_nec E hκ hβ0 hβ1 hγ hδx hw hw0, ex_2_2_suff E hκ hβ0 hβ1 hγ hδx⟩

/-- **Exercise 2.2(b)** (Miao, p. 83), the Bullard–Mitra condition: for `δ_π, δ_x ≥ 0` (with
`κ, γ > 0`, `0 < β < 1`), there is a unique stable equilibrium iff
`κ(δ_π − 1) + (1 − β)δ_x > 0`. -/
theorem ex_2_2_b [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δπ δx : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδπ : 0 ≤ δπ) (hδx : 0 ≤ δx) {w : V}
    (hw : w ≠ 0) (hw0 : E.E 0 w = w) :
    nkDeterminate E κ β γ δπ δx ↔ 0 < κ * (δπ - 1) + (1 - β) * δx := by
  rw [ex_2_2_b_exact E hκ hβ0 hβ1 hγ hδx hw hw0]
  refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
  nlinarith [mul_nonneg hκ.le hδπ, mul_nonneg hβ0.le hδx]

/-- **Exercise 2.2(a)**, corrected (Miao, p. 82): for the rule `i_t = δπ_t + ε_t` (with
`κ, γ > 0`, `0 < β < 1`), there is a unique stable equilibrium iff `δ > 1` or
`δ < −1 − 2(1 + β)γ/κ`. The book's claim that `δ > 1` is necessary is false
(`ex_2_2_a_printed_false`): for very negative `δ` both roots leave the unit circle through `−1`. -/
theorem ex_2_2_a [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (δ : ℝ) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) :
    nkDeterminate E κ β γ δ 0 ↔ (1 < δ ∨ δ < -1 - 2 * (1 + β) * γ / κ) := by
  rw [ex_2_2_b_exact E hκ hβ0 hβ1 hγ le_rfl hw hw0]
  have e : -1 - 2 * (1 + β) * γ / κ = (-κ - 2 * (1 + β) * γ) / κ := by
    rw [eq_div_iff hκ.ne']
    field_simp
  rw [e, lt_div_iff₀ hκ]
  constructor
  · rintro (h | h)
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)
  · rintro (h | h)
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by nlinarith)

/-- **Exercise 2.2(a)**, the Taylor principle (Miao, p. 82), proved for `δ ≥ 0`: with `κ, γ > 0`
and `0 < β < 1`, there is a unique stable equilibrium iff `δ > 1`. -/
theorem ex_2_2_a_taylor_principle [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ δ : ℝ}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hδ : 0 ≤ δ) {w : V} (hw : w ≠ 0)
    (hw0 : E.E 0 w = w) : nkDeterminate E κ β γ δ 0 ↔ 1 < δ := by
  rw [ex_2_2_a E hκ hβ0 hβ1 hγ δ hw hw0]
  refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
  have : 0 < 2 * (1 + β) * γ / κ := by positivity
  linarith

/-- **Exercise 2.2(a)** as printed is false (Miao, p. 82): "`δ > 1` is necessary". For
`κ = γ = 1`, `β = 1/2` and `δ = −5` the equilibrium is unique (the roots of `λ² − 5λ − 8` are
`(5 ± √57)/2`, both outside the unit circle). -/
theorem ex_2_2_a_printed_false [CompleteSpace V] (E : CondExpSystem ℝ V) :
    nkDeterminate E 1 (1 / 2) 1 (-5) 0 ∧ ¬ (1 < (-5 : ℝ)) :=
  ⟨ex_2_2_suff E one_pos (by norm_num) (by norm_num) one_pos le_rfl (Or.inr (by norm_num)),
    by norm_num⟩

end Miao.NeoclassicalGrowth

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonlinear systems

Copied from `EconomicDynamics/DifferenceEquations` (module `Nonlinear`), namespace renamed.

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

namespace Miao.NeoclassicalGrowth

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

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Primitives of the basic Ramsey model

Miao, §14.1.1, pp. 456–459: the assumptions on the production function `F` and the utility
function `u`, the zero-profit property of a constant-returns firm, and the King–Plosser–Rebelo
(KPR) utility functions (14.5)–(14.6) that are consistent with balanced growth.

* **Zero profits** (p. 459). Euler's theorem for a function homogeneous of degree one and
  Fréchet differentiable at `(K, L)`: `F(K, L) = F_K K + F_L L` (`rm_euler_homogeneous`).
  Hence, with the firm's first-order conditions (14.3), profits `F − R^k K − wN` are zero
  (`rm_zero_profit`). The partial derivatives are homogeneous of degree zero
  (`rm_partial1_homog_zero`, `rm_partial2_homog_zero`), so `F_K(K, AN)` depends only on
  `K/(AN)` (used for detrending).
* **KPR utility** (14.5): `u(c, n) = c^{1−σ}v(n)/(1 − σ)` has `u_c = c^{−σ}v(n)`,
  `u_n = c^{1−σ}v'(n)/(1 − σ)` (`rm_kpr_hasDerivAt_c`, `rm_kpr_hasDerivAt_n`);
  `u_c(λc, n) = λ^{−σ}u_c(c, n)` and `u_n(λc, n) = λ^{1−σ}u_n(c, n)`
  (`rm_kpr_uc_scale`, `rm_kpr_un_scale`), so the marginal rate of substitution `−u_n/u_c` is
  homogeneous of degree one in `c` (`rm_kpr_mrs_scale`). For (14.6), `u = ln c + v(n)`, the same
  holds with `σ = 1` (`rm_log_hasDerivAt_c`, `rm_log_uc_scale`, `rm_log_mrs_scale`).

**Corrections.** The printed limit conditions `lim_{c→0} u(c, ·) = ∞` and
`lim_{K→∞} F(K, 1) = 0` cannot hold: a function increasing in `c` is bounded above near
`c = 0` (`rm_inada_u_misprint`), and `F(·, 1)` strictly increasing with `F(0, 1) = 0` is
bounded below by `F(1, 1) > 0` for `K ≥ 1` (`rm_inada_F_misprint`). The intended conditions are
`lim_{c→0} u_c = ∞` and `lim_{K→∞} F_1(K, 1) = 0`; they hold for log utility
(`rm_log_inada`) and for Cobb–Douglas (`rm_cd_inada_zero`, `rm_cd_inada_top`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### Constant returns to scale -/

/-- Miao, p. 459 (Euler's theorem behind "the firm makes zero profit"): if `F` is homogeneous of
degree one along the ray through `(K, L)` and Fréchet differentiable at `(K, L)` with partial
derivatives `F_K, F_L`, then `F(K, L) = F_K K + F_L L`. -/
theorem rm_euler_homogeneous {F : ℝ → ℝ → ℝ} {FK FL K L : ℝ}
    (hhom : ∀ s, 0 < s → F (s * K) (s * L) = s * F K L)
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ) (K, L)) :
    F K L = FK * K + FL * L := by
  have hγ : HasDerivAt (fun s : ℝ => (s * K, s * L)) (K, L) 1 :=
    (hasDerivAt_mul_const K).prodMk (hasDerivAt_mul_const L)
  have h1 : HasDerivAt (fun s : ℝ => F (s * K) (s * L)) (FK * K + FL * L) 1 := by
    have := hF.comp_hasDerivAt_of_eq (x := (1 : ℝ)) hγ (by simp)
    convert this using 1
    · rfl
    · simp
  have h2 : HasDerivAt (fun s : ℝ => F (s * K) (s * L)) (F K L) 1 := by
    have h3 : HasDerivAt (fun s : ℝ => s * F K L) (F K L) 1 := hasDerivAt_mul_const _
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with s hs
    exact hhom s hs
  exact h2.unique h1

/-- Miao, p. 459: with the first-order conditions (14.3) `R^k = F_K`, `w = F_N` (here `A = 1` is
absorbed into effective labour `L = AN`), a constant-returns firm makes zero profit. -/
theorem rm_zero_profit {F : ℝ → ℝ → ℝ} {FK FL K L Rk w : ℝ}
    (hhom : ∀ s, 0 < s → F (s * K) (s * L) = s * F K L)
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ) (K, L))
    (hR : Rk = FK) (hw : w = FL) : F K L - Rk * K - w * L = 0 := by
  rw [rm_euler_homogeneous hhom hF, hR, hw]; ring

/-- Miao, p. 459 (used for detrending): if `F` is homogeneous of degree one on the positive
quadrant and has partial derivative `F₁` in its first argument there, then `F₁` is homogeneous of
degree zero: `F₁(sK, sL) = F₁(K, L)`. -/
theorem rm_partial1_homog_zero {F F1 : ℝ → ℝ → ℝ}
    (hhom : ∀ s x y, 0 < s → 0 < x → 0 < y → F (s * x) (s * y) = s * F x y)
    (hF1 : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F z y) (F1 x y) x)
    {s K L : ℝ} (hs : 0 < s) (hK : 0 < K) (hL : 0 < L) : F1 (s * K) (s * L) = F1 K L := by
  have hA : HasDerivAt (fun z => F (s * z) (s * L)) (F1 (s * K) (s * L) * s) K := by
    have hl : HasDerivAt (fun z => s * z) s K := by simpa using (hasDerivAt_id K).const_mul s
    exact (hF1 (s * K) (s * L) (mul_pos hs hK) (mul_pos hs hL)).comp K hl
  have hB : HasDerivAt (fun z => F (s * z) (s * L)) (s * F1 K L) K := by
    refine ((hF1 K L hK hL).const_mul s).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hK] with z hz
    exact hhom s z L hs hz hL
  have := hA.unique hB
  have hs' : s ≠ 0 := hs.ne'
  have : (F1 (s * K) (s * L) - F1 K L) * s = 0 := by linarith
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs')

/-- Miao, p. 459: the partial derivative in the second argument is homogeneous of degree zero
too. -/
theorem rm_partial2_homog_zero {F F2 : ℝ → ℝ → ℝ}
    (hhom : ∀ s x y, 0 < s → 0 < x → 0 < y → F (s * x) (s * y) = s * F x y)
    (hF2 : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F x z) (F2 x y) y)
    {s K L : ℝ} (hs : 0 < s) (hK : 0 < K) (hL : 0 < L) : F2 (s * K) (s * L) = F2 K L := by
  have hA : HasDerivAt (fun z => F (s * K) (s * z)) (F2 (s * K) (s * L) * s) L := by
    have hl : HasDerivAt (fun z => s * z) s L := by simpa using (hasDerivAt_id L).const_mul s
    exact (hF2 (s * K) (s * L) (mul_pos hs hK) (mul_pos hs hL)).comp L hl
  have hB : HasDerivAt (fun z => F (s * K) (s * z)) (s * F2 K L) L := by
    refine ((hF2 K L hK hL).const_mul s).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hL] with z hz
    exact hhom s K z hs hK hz
  have := hA.unique hB
  have : (F2 (s * K) (s * L) - F2 K L) * s = 0 := by linarith
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs.ne')

/-! ### KPR utility (14.5)–(14.6) -/

/-- The KPR utility (14.5), `u(c, n) = c^{1−σ}v(n)/(1 − σ)`. -/
noncomputable def rmKprU (σ : ℝ) (v : ℝ → ℝ) (c n : ℝ) : ℝ :=
  c ^ (1 - σ) * v n / (1 - σ)

/-- The marginal utility of consumption for (14.5), `u_c = c^{−σ}v(n)`. -/
noncomputable def rmKprUc (σ : ℝ) (v : ℝ → ℝ) (c n : ℝ) : ℝ :=
  c ^ (-σ) * v n

/-- The marginal (dis)utility of labour for (14.5), `u_n = c^{1−σ}v'(n)/(1 − σ)`. -/
noncomputable def rmKprUn (σ : ℝ) (v' : ℝ → ℝ) (c n : ℝ) : ℝ :=
  c ^ (1 - σ) * v' n / (1 - σ)

/-- Miao, (14.5), p. 459: `∂u/∂c = c^{−σ}v(n)` for `c > 0`, `σ ≠ 1`. -/
theorem rm_kpr_hasDerivAt_c {σ : ℝ} (hσ : σ ≠ 1) (v : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (n : ℝ) :
    HasDerivAt (fun x => rmKprU σ v x n) (rmKprUc σ v c n) c := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).mul_const (v n)
    |>.div_const (1 - σ)
  have h1 : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have he : (1 - σ) * c ^ (1 - σ - 1) * v n / (1 - σ) = rmKprUc σ v c n := by
    simp only [rmKprUc, show 1 - σ - 1 = -σ by ring]
    field_simp
  exact he ▸ h

/-- Miao, (14.5), p. 459: `∂u/∂n = c^{1−σ}v'(n)/(1 − σ)` when `v'` is the derivative of `v`. -/
theorem rm_kpr_hasDerivAt_n (σ : ℝ) {v v' : ℝ → ℝ} (c : ℝ) {n : ℝ}
    (hv : HasDerivAt v (v' n) n) :
    HasDerivAt (fun x => rmKprU σ v c x) (rmKprUn σ v' c n) n := by
  have h := (hv.const_mul (c ^ (1 - σ))).div_const (1 - σ)
  exact h

/-- Miao, p. 459: `u_c(λc, n) = λ^{−σ}u_c(c, n)` for (14.5). -/
theorem rm_kpr_uc_scale (σ : ℝ) (v : ℝ → ℝ) {l c : ℝ} (hl : 0 < l) (hc : 0 < c) (n : ℝ) :
    rmKprUc σ v (l * c) n = l ^ (-σ) * rmKprUc σ v c n := by
  simp only [rmKprUc, Real.mul_rpow hl.le hc.le]; ring

/-- Miao, p. 459: `u_n(λc, n) = λ^{1−σ}u_n(c, n)` for (14.5). -/
theorem rm_kpr_un_scale (σ : ℝ) (v' : ℝ → ℝ) {l c : ℝ} (hl : 0 < l) (hc : 0 < c) (n : ℝ) :
    rmKprUn σ v' (l * c) n = l ^ (1 - σ) * rmKprUn σ v' c n := by
  simp only [rmKprUn, Real.mul_rpow hl.le hc.le]; ring

/-- Miao, p. 459: for (14.5) the marginal rate of substitution `−u_n/u_c` is homogeneous of
degree one in consumption, which is why the wage grows at the rate of technology. -/
theorem rm_kpr_mrs_scale (σ : ℝ) {v v' : ℝ → ℝ} {l c : ℝ} (hl : 0 < l) (hc : 0 < c) (n : ℝ)
    (hv : v n ≠ 0) :
    -rmKprUn σ v' (l * c) n / rmKprUc σ v (l * c) n =
      l * (-rmKprUn σ v' c n / rmKprUc σ v c n) := by
  rw [rm_kpr_un_scale σ v' hl hc, rm_kpr_uc_scale σ v hl hc]
  have h1 : l ^ (1 - σ) = l * l ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hl, Real.rpow_one]
  have h2 : 0 < l ^ (-σ) := Real.rpow_pos_of_pos hl _
  have h3 : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  rw [h1]
  simp only [rmKprUc] at *
  field_simp

/-- Miao, (14.6), p. 459: for `u = ln c + v(n)`, `∂u/∂c = 1/c`. -/
theorem rm_log_hasDerivAt_c (v : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (n : ℝ) :
    HasDerivAt (fun x => Real.log x + v n) (1 / c) c := by
  simpa [one_div] using (Real.hasDerivAt_log hc.ne').add_const (v n)

/-- Miao, (14.6), p. 459: `u_c(λc) = λ^{−1}u_c(c)` for log utility. -/
theorem rm_log_uc_scale {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    1 / (l * c) = l⁻¹ * (1 / c) := by
  field_simp

/-- Miao, (14.6), p. 459: for log utility `−u_n/u_c = −c v'(n)` is homogeneous of degree one in
`c`. -/
theorem rm_log_mrs_scale (vn l c : ℝ) (hl : 0 < l) (hc : 0 < c) :
    -vn / (1 / (l * c)) = l * (-vn / (1 / c)) := by
  field_simp

/-! ### The limit conditions on p. 456–457 -/

/-- Correction to Miao, p. 456: `lim_{c→0} u(c, n) = ∞` is impossible when `u(·, n)` is
increasing on `(0, ∞)` (as `u_c > 0` requires). -/
theorem rm_inada_u_misprint {u : ℝ → ℝ} (hu : MonotoneOn u (Set.Ioi 0)) :
    ¬ Tendsto u (𝓝[>] 0) atTop := by
  intro h
  have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), u 1 + 1 ≤ u c := h.eventually (eventually_ge_atTop _)
  have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨c, hc1, hc2⟩ := (h1.and h2).exists
  have := hu hc2.1 (Set.mem_Ioi.2 zero_lt_one) hc2.2.le
  linarith

/-- Correction to Miao, p. 457: `lim_{K→∞} F(K, 1) = 0` is impossible when `F(·, 1)` is strictly
increasing on `[0, ∞)` (as `F₁ > 0` requires) and `F(0, 1) = 0`. -/
theorem rm_inada_F_misprint {f : ℝ → ℝ} (hf : StrictMonoOn f (Set.Ici 0)) (h0 : f 0 = 0) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro h
  have h1 : 0 < f 1 := by
    have := hf (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_lt_one
    linarith
  have h2 : ∀ᶠ K in atTop, f 1 ≤ f K := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    exact hf.monotoneOn (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 (by linarith)) hK
  have := ge_of_tendsto h h2
  linarith

/-- Miao, p. 456 (the intended condition): for log utility `u_c = 1/c → ∞` as `c → 0⁺`. -/
theorem rm_log_inada : Tendsto (fun c : ℝ => 1 / c) (𝓝[>] 0) atTop := by
  simpa [one_div] using tendsto_inv_nhdsGT_zero

/-- Miao, p. 457 (the intended condition): for Cobb–Douglas `F(K, 1) = K^α`, `0 < α < 1`, the
marginal product `F₁(K, 1) = αK^{α−1} → ∞` as `K → 0⁺`. -/
theorem rm_cd_inada_zero {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun K : ℝ => α * K ^ (α - 1)) (𝓝[>] 0) atTop := by
  exact (tendsto_rpow_neg_nhdsGT_zero (show α - 1 < 0 by linarith)).const_mul_atTop hα0

/-- Miao, p. 457 (the intended condition): `F₁(K, 1) = αK^{α−1} → 0` as `K → ∞`. -/
theorem rm_cd_inada_top {α : ℝ} (hα1 : α < 1) :
    Tendsto (fun K : ℝ => α * K ^ (α - 1)) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (show 0 < 1 - α by linarith)
  have h' : Tendsto (fun K : ℝ => K ^ (α - 1)) atTop (𝓝 0) := by
    simpa [show -(1 - α) = α - 1 by ring] using h
  simpa using h'.const_mul α

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The social planner's problem of the basic Ramsey model

Miao, §14.1.1, "Social Planner's Problem", pp. 464–465. The planner maximises
`∑ βᵗ gₙᵗ u(c_t, n_t)` subject to `gₙᵗc_t + gₙᵗi_t = F(gₙᵗk_t, A_tgₙᵗn_t)` and
`gₙk_{t+1} = (1 − δ)k_t + i_t`, with `A_t = g_aᵗ`. Since `F` is homogeneous of degree one the
per-capita resource constraint is `c_t + i_t = F(k_t, A_tn_t)` (`rm_planner_resource`), and
eliminating `i_t` gives `c_t = F(k_t, A_tn_t) + (1 − δ)k_t − gₙk_{t+1}` (`rmPlanC`).

Optimality is used in the weakest form the first-order conditions need: no feasible plan that
agrees with the plan from some date `T` on gives a higher discounted utility over dates `< T`
(`RMPlanNFI`). A plan that maximises the infinite sum among feasible plans with summable utility
has this property (`rm_planner_nfi_of_optimal`).

* The Euler equation `u_c(c_t, n_t) = βu_c(c_{t+1}, n_{t+1})[F_K(k_{t+1}, A_{t+1}n_{t+1}) + 1 − δ]`
  is necessary (`rm_planner_euler`), by the variation of `k_{t+1}` alone.
* The intratemporal condition is necessary in the form
  `−u_n(c_t, n_t)/u_c(c_t, n_t) = A_tF_N(k_t, A_tn_t)` (`rm_planner_intratemporal`), by the
  variation of `n_t` alone.

**Correction.** The book prints `−u_n/u_c = F_N(k_t, A_tn_t)`, without the factor `A_t` (the
detrended version on p. 465 is right). With `F_N ≠ 0` the printed equation and the true one
together force `A_t = 1` (`rm_planner_intratemporal_misprint`), so the printed one fails at every
date `t ≥ 1` when `g_a ≠ 1`.
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- Miao, p. 464: the aggregate resource constraint `gₙᵗc_t + gₙᵗi_t = F(gₙᵗk_t, A_tgₙᵗn_t)` is
equivalent to the per-capita one `c_t + i_t = F(k_t, A_tn_t)` when `F` is homogeneous of degree
one. -/
theorem rm_planner_resource {F : ℝ → ℝ → ℝ} (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    {gn A c i k n : ℝ} (hgn : 0 < gn) (t : ℕ) :
    gn ^ t * c + gn ^ t * i = F (gn ^ t * k) (A * (gn ^ t * n)) ↔ c + i = F k (A * n) := by
  have hs : (0 : ℝ) < gn ^ t := pow_pos hgn t
  rw [show A * (gn ^ t * n) = gn ^ t * (A * n) by ring, hhom _ _ _ hs]
  constructor
  · intro h
    have : gn ^ t * (c + i) = gn ^ t * F k (A * n) := by linarith
    exact mul_left_cancel₀ hs.ne' this
  · intro h; rw [← h]; ring

/-- Per-capita consumption from the resource constraint and (14.2):
`c_t = F(k_t, g_aᵗn_t) + (1 − δ)k_t − gₙk_{t+1}`. -/
def rmPlanC (F : ℝ → ℝ → ℝ) (ga gn δ : ℝ) (k n : ℕ → ℝ) (t : ℕ) : ℝ :=
  F (k t) (ga ^ t * n t) + (1 - δ) * k t - gn * k (t + 1)

/-- The gain in discounted utility over dates `< T` from switching from `(k, n)` to `(k', n')`. -/
def rmPlanGain (U F : ℝ → ℝ → ℝ) (β ga gn δ : ℝ) (k n k' n' : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * gn ^ t *
    (U (rmPlanC F ga gn δ k' n' t) (n' t) - U (rmPlanC F ga gn δ k n t) (n t))

/-- A feasible plan from `k₀`: positive capital, labour and consumption at every date. -/
def RMPlanFeasible (F : ℝ → ℝ → ℝ) (ga gn δ k0 : ℝ) (k n : ℕ → ℝ) : Prop :=
  k 0 = k0 ∧ ∀ t, 0 < k t ∧ 0 < n t ∧ 0 < rmPlanC F ga gn δ k n t

/-- No finite improvement: no feasible plan agreeing with `(k, n)` from some date `T` on does
better over the dates `< T`. -/
def RMPlanNFI (U F : ℝ → ℝ → ℝ) (β ga gn δ : ℝ) (k n : ℕ → ℝ) : Prop :=
  ∀ (T : ℕ) (k' n' : ℕ → ℝ), RMPlanFeasible F ga gn δ (k 0) k' n' →
    (∀ t, T ≤ t → k' t = k t ∧ n' t = n t) → rmPlanGain U F β ga gn δ k n k' n' T ≤ 0

/-- Miao, p. 464: a plan maximising `∑ βᵗgₙᵗu(c_t, n_t)` among feasible plans (all of which have
summable discounted utility) admits no finite improvement. -/
theorem rm_planner_nfi_of_optimal {U F : ℝ → ℝ → ℝ} {β ga gn δ : ℝ} {k n : ℕ → ℝ}
    (hsum : ∀ k' n', RMPlanFeasible F ga gn δ (k 0) k' n' →
      Summable (fun t => β ^ t * gn ^ t * U (rmPlanC F ga gn δ k' n' t) (n' t)))
    (hk : RMPlanFeasible F ga gn δ (k 0) k n)
    (hopt : ∀ k' n', RMPlanFeasible F ga gn δ (k 0) k' n' →
      ∑' t, β ^ t * gn ^ t * U (rmPlanC F ga gn δ k' n' t) (n' t) ≤
        ∑' t, β ^ t * gn ^ t * U (rmPlanC F ga gn δ k n t) (n t)) :
    RMPlanNFI U F β ga gn δ k n := by
  intro T k' n' hf hagree
  have hc : ∀ t, T ≤ t → rmPlanC F ga gn δ k' n' t = rmPlanC F ga gn δ k n t := by
    intro t ht
    simp only [rmPlanC, (hagree t ht).1, (hagree t ht).2, (hagree (t + 1) (by omega)).1]
  have h1 := (hsum k' n' hf).sum_add_tsum_nat_add T
  have h2 := (hsum k n hk).sum_add_tsum_nat_add T
  have htail : (∑' t, β ^ (t + T) * gn ^ (t + T) *
      U (rmPlanC F ga gn δ k' n' (t + T)) (n' (t + T))) =
      ∑' t, β ^ (t + T) * gn ^ (t + T) * U (rmPlanC F ga gn δ k n (t + T)) (n (t + T)) := by
    congr 1; ext t
    rw [hc (t + T) (by omega), (hagree (t + T) (by omega)).2]
  have := hopt k' n' hf
  simp only [rmPlanGain, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- Evaluation of the derivative `u_c • fst + u_n • snd` at `(x, y)`. -/
theorem rm_clm_apply (a b x y : ℝ) :
    (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) =
      a * x + b * y := by
  simp

/-- The capital stock with `k_{t+1}` replaced by `x`. -/
theorem rm_planC_update_k_ne {F : ℝ → ℝ → ℝ} {ga gn δ : ℝ} (k n : ℕ → ℝ) {t s : ℕ} (x : ℝ)
    (h1 : s ≠ t) (h2 : s ≠ t + 1) :
    rmPlanC F ga gn δ (Function.update k (t + 1) x) n s = rmPlanC F ga gn δ k n s := by
  simp only [rmPlanC, Function.update_of_ne h2, Function.update_of_ne (show s + 1 ≠ t + 1 by omega)]

theorem rm_planC_update_k_t {F : ℝ → ℝ → ℝ} {ga gn δ : ℝ} (k n : ℕ → ℝ) (t : ℕ) (x : ℝ) :
    rmPlanC F ga gn δ (Function.update k (t + 1) x) n t =
      F (k t) (ga ^ t * n t) + (1 - δ) * k t - gn * x := by
  simp only [rmPlanC, Function.update_of_ne (show t ≠ t + 1 by omega), Function.update_self]

theorem rm_planC_update_k_succ {F : ℝ → ℝ → ℝ} {ga gn δ : ℝ} (k n : ℕ → ℝ) (t : ℕ) (x : ℝ) :
    rmPlanC F ga gn δ (Function.update k (t + 1) x) n (t + 1) =
      F x (ga ^ (t + 1) * n (t + 1)) + (1 - δ) * x - gn * k (t + 2) := by
  simp only [rmPlanC, Function.update_of_ne (show t + 1 + 1 ≠ t + 1 by omega), Function.update_self]

/-- **The planner's Euler equation** (Miao, p. 464): a feasible plan with no finite improvement
satisfies `u_c(c_t, n_t) = βu_c(c_{t+1}, n_{t+1})[F_K(k_{t+1}, A_{t+1}n_{t+1}) + 1 − δ]`,
`A_t = g_aᵗ`. Here `U` is Fréchet differentiable at each `(c_t, n_t)` with partials `u_c, u_n`
and `F` has partial derivative `F_K` in capital on the positive quadrant. -/
theorem rm_planner_euler {U F uc un FK : ℝ → ℝ → ℝ} {β ga gn δ : ℝ} {k n : ℕ → ℝ}
    (hβ : 0 < β) (hgn : 0 < gn) (hga : 0 < ga)
    (hU : ∀ t, HasFDerivAt (fun p : ℝ × ℝ => U p.1 p.2)
      (uc (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        un (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (rmPlanC F ga gn δ k n t, n t))
    (hFK : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F z y) (FK x y) x)
    (hfeas : RMPlanFeasible F ga gn δ (k 0) k n) (hnfi : RMPlanNFI U F β ga gn δ k n) (t : ℕ) :
    uc (rmPlanC F ga gn δ k n t) (n t) = β * uc (rmPlanC F ga gn δ k n (t + 1)) (n (t + 1)) *
      (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + 1 - δ) := by
  set c0 := rmPlanC F ga gn δ k n t with hc0
  set c1 := rmPlanC F ga gn δ k n (t + 1) with hc1
  have hy : 0 < ga ^ (t + 1) * n (t + 1) := mul_pos (pow_pos hga _) (hfeas.2 (t + 1)).2.1
  -- consumption at dates `t` and `t + 1` as functions of `k_{t+1} = x`
  set f0 : ℝ → ℝ := fun x => F (k t) (ga ^ t * n t) + (1 - δ) * k t - gn * x with hf0
  set f1 : ℝ → ℝ := fun x => F x (ga ^ (t + 1) * n (t + 1)) + (1 - δ) * x - gn * k (t + 1 + 1)
    with hf1
  have hd0 : HasDerivAt f0 (-gn) (k (t + 1)) := by
    have := ((hasDerivAt_id (k (t + 1))).const_mul gn).const_sub
      (F (k t) (ga ^ t * n t) + (1 - δ) * k t)
    simpa [hf0] using this
  have hd1 : HasDerivAt f1 (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ)) (k (t + 1)) := by
    have := (((hFK (k (t + 1)) _ (hfeas.2 (t + 1)).1 hy).add
      ((hasDerivAt_id (k (t + 1))).const_mul (1 - δ))).sub_const (gn * k (t + 1 + 1)))
    simpa [hf1] using this
  have hf0x : f0 (k (t + 1)) = c0 := rfl
  have hf1x : f1 (k (t + 1)) = c1 := rfl
  -- the objective
  set φ : ℝ → ℝ := fun x => β ^ t * gn ^ t * (U (f0 x) (n t) - U c0 (n t)) +
    β ^ (t + 1) * gn ^ (t + 1) * (U (f1 x) (n (t + 1)) - U c1 (n (t + 1))) with hφ
  have hg0 : HasDerivAt (fun x => U (f0 x) (n t)) (uc c0 (n t) * (-gn)) (k (t + 1)) := by
    have hγ : HasDerivAt (fun x => (f0 x, n t)) ((-gn), (0 : ℝ)) (k (t + 1)) :=
      hd0.prodMk (hasDerivAt_const _ _)
    have := HasFDerivAt.comp_hasDerivAt (x := k (t + 1)) (hU t) hγ
    convert this using 1
    · rfl
    · rw [rm_clm_apply, hc0]; ring
  have hg1 : HasDerivAt (fun x => U (f1 x) (n (t + 1)))
      (uc c1 (n (t + 1)) * (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ))) (k (t + 1)) := by
    have hγ : HasDerivAt (fun x => (f1 x, n (t + 1)))
        ((FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ)), (0 : ℝ)) (k (t + 1)) :=
      hd1.prodMk (hasDerivAt_const _ _)
    have := HasFDerivAt.comp_hasDerivAt (x := k (t + 1)) (hU (t + 1)) hγ
    convert this using 1
    · rfl
    · rw [rm_clm_apply, hc1]; ring
  have hφd : HasDerivAt φ (β ^ t * gn ^ t * (uc c0 (n t) * (-gn)) + β ^ (t + 1) * gn ^ (t + 1) *
      (uc c1 (n (t + 1)) * (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + (1 - δ)))) (k (t + 1)) := by
    have := ((hg0.sub_const (U c0 (n t))).const_mul (β ^ t * gn ^ t)).add
      ((hg1.sub_const (U c1 (n (t + 1)))).const_mul (β ^ (t + 1) * gn ^ (t + 1)))
    exact this.congr_deriv (by ring)
  -- local maximum
  have hmax : IsLocalMax φ (k (t + 1)) := by
    have e1 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < x := lt_mem_nhds (hfeas.2 (t + 1)).1
    have e2 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < f0 x :=
      continuousAt_const.eventually_lt hd0.continuousAt (by rw [hf0x]; exact (hfeas.2 t).2.2)
    have e3 : ∀ᶠ x in 𝓝 (k (t + 1)), 0 < f1 x :=
      continuousAt_const.eventually_lt hd1.continuousAt
        (by rw [hf1x]; exact (hfeas.2 (t + 1)).2.2)
    filter_upwards [e1, e2, e3] with x h1 h2 h3
    have hφ0 : φ (k (t + 1)) = 0 := by simp [hφ, hf0x, hf1x]
    rw [hφ0]
    have hfe : RMPlanFeasible F ga gn δ (k 0) (Function.update k (t + 1) x) n := by
      refine ⟨Function.update_of_ne (by omega) _ _, fun s => ?_⟩
      by_cases hs1 : s = t
      · subst hs1
        refine ⟨?_, (hfeas.2 s).2.1, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact (hfeas.2 s).1
        · rw [rm_planC_update_k_t]; exact h2
      by_cases hs2 : s = t + 1
      · subst hs2
        refine ⟨by rw [Function.update_self]; exact h1, (hfeas.2 _).2.1, ?_⟩
        rw [rm_planC_update_k_succ]; exact h3
      refine ⟨?_, (hfeas.2 s).2.1, ?_⟩
      · rw [Function.update_of_ne hs2]; exact (hfeas.2 s).1
      · rw [rm_planC_update_k_ne k n x hs1 hs2]; exact (hfeas.2 s).2.2
    have hg := hnfi (t + 2) (Function.update k (t + 1) x) n hfe (fun s hs =>
      ⟨Function.update_of_ne (by omega) _ _, rfl⟩)
    have hsum : rmPlanGain U F β ga gn δ k n (Function.update k (t + 1) x) n (t + 2) = φ x := by
      simp only [rmPlanGain, Finset.sum_range_succ]
      rw [Finset.sum_eq_zero (fun s hs => by
        rw [rm_planC_update_k_ne k n x (by simp at hs; omega) (by simp at hs; omega)]; ring)]
      rw [rm_planC_update_k_t, rm_planC_update_k_succ]
      simp only [hφ, hf0, hf1, hc0, hc1]
      ring
    linarith
  have h0 := hmax.hasDerivAt_eq_zero hφd
  have hpos : 0 < β ^ t * gn ^ t * gn := by positivity
  have : β ^ t * gn ^ t * gn * (uc c0 (n t) - β * uc c1 (n (t + 1)) *
      (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + 1 - δ)) = 0 := by
    linear_combination -h0
  have := (mul_eq_zero.1 this).resolve_left hpos.ne'
  linarith

/-- **The planner's intratemporal condition** (Miao, p. 464, corrected): a feasible plan with no
finite improvement satisfies `u_n(c_t, n_t) + u_c(c_t, n_t)A_tF_N(k_t, A_tn_t) = 0`, i.e.
`−u_n/u_c = A_tF_N(k_t, A_tn_t)`. -/
theorem rm_planner_intratemporal {U F uc un FN : ℝ → ℝ → ℝ} {β ga gn δ : ℝ} {k n : ℕ → ℝ}
    (hβ : 0 < β) (hgn : 0 < gn) (hga : 0 < ga)
    (hU : ∀ t, HasFDerivAt (fun p : ℝ × ℝ => U p.1 p.2)
      (uc (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        un (rmPlanC F ga gn δ k n t) (n t) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (rmPlanC F ga gn δ k n t, n t))
    (hFN : ∀ x y, 0 < x → 0 < y → HasDerivAt (fun z => F x z) (FN x y) y)
    (hfeas : RMPlanFeasible F ga gn δ (k 0) k n) (hnfi : RMPlanNFI U F β ga gn δ k n) (t : ℕ) :
    un (rmPlanC F ga gn δ k n t) (n t) +
      uc (rmPlanC F ga gn δ k n t) (n t) * (ga ^ t * FN (k t) (ga ^ t * n t)) = 0 := by
  set c0 := rmPlanC F ga gn δ k n t with hc0
  set x0 := n t with hx0
  have hA : 0 < ga ^ t := pow_pos hga t
  set f0 : ℝ → ℝ := fun x => F (k t) (ga ^ t * x) + (1 - δ) * k t - gn * k (t + 1) with hf0
  have hd0 : HasDerivAt f0 (FN (k t) (ga ^ t * x0) * ga ^ t) x0 := by
    have hl : HasDerivAt (fun x => ga ^ t * x) (ga ^ t) x0 := by
      simpa using (hasDerivAt_id x0).const_mul (ga ^ t)
    have := (((hFN (k t) (ga ^ t * x0) (hfeas.2 t).1 (mul_pos hA (hfeas.2 t).2.1)).comp x0
      hl).add_const ((1 - δ) * k t)).sub_const (gn * k (t + 1))
    exact this
  have hf0x : f0 x0 = c0 := rfl
  set φ : ℝ → ℝ := fun x => β ^ t * gn ^ t * (U (f0 x) x - U c0 x0) with hφ
  have hg : HasDerivAt (fun x => U (f0 x) x)
      (uc c0 x0 * (FN (k t) (ga ^ t * x0) * ga ^ t) + un c0 x0) x0 := by
    have hγ : HasDerivAt (fun x => (f0 x, x)) ((FN (k t) (ga ^ t * x0) * ga ^ t), (1 : ℝ)) x0 :=
      hd0.prodMk (hasDerivAt_id x0)
    have := HasFDerivAt.comp_hasDerivAt (f := fun x => (f0 x, x)) (x := x0) (hU t) hγ
    convert this using 1
    · rfl
    · rw [rm_clm_apply, hc0, hx0]; ring
  have hφd : HasDerivAt φ (β ^ t * gn ^ t *
      (uc c0 x0 * (FN (k t) (ga ^ t * x0) * ga ^ t) + un c0 x0)) x0 := by
    simpa [hφ] using (hg.sub_const (U c0 x0)).const_mul (β ^ t * gn ^ t)
  have hmax : IsLocalMax φ x0 := by
    have e1 : ∀ᶠ x in 𝓝 x0, 0 < x := lt_mem_nhds (hfeas.2 t).2.1
    have e2 : ∀ᶠ x in 𝓝 x0, 0 < f0 x :=
      continuousAt_const.eventually_lt hd0.continuousAt (by rw [hf0x]; exact (hfeas.2 t).2.2)
    filter_upwards [e1, e2] with x h1 h2
    have hφ0 : φ x0 = 0 := by simp [hφ, hf0x]
    rw [hφ0]
    have hcs : ∀ s, s ≠ t → rmPlanC F ga gn δ k (Function.update n t x) s =
        rmPlanC F ga gn δ k n s := fun s hs => by
      simp only [rmPlanC, Function.update_of_ne hs]
    have hct : rmPlanC F ga gn δ k (Function.update n t x) t = f0 x := by
      simp only [rmPlanC, Function.update_self, hf0]
    have hfe : RMPlanFeasible F ga gn δ (k 0) k (Function.update n t x) := by
      refine ⟨rfl, fun s => ?_⟩
      by_cases hs : s = t
      · subst hs
        exact ⟨(hfeas.2 s).1, by rw [Function.update_self]; exact h1, by rw [hct]; exact h2⟩
      · refine ⟨(hfeas.2 s).1, by rw [Function.update_of_ne hs]; exact (hfeas.2 s).2.1, ?_⟩
        rw [hcs s hs]; exact (hfeas.2 s).2.2
    have hgain := hnfi (t + 1) k (Function.update n t x) hfe (fun s hs =>
      ⟨rfl, Function.update_of_ne (by omega) _ _⟩)
    have hsum : rmPlanGain U F β ga gn δ k n k (Function.update n t x) (t + 1) = φ x := by
      simp only [rmPlanGain, Finset.sum_range_succ]
      rw [Finset.sum_eq_zero (fun s hs => by
        have hs' : s ≠ t := by simp at hs; omega
        rw [hcs s hs', Function.update_of_ne hs']; ring)]
      rw [hct, Function.update_self]
      simp only [hφ, hc0, hx0]
      ring
    linarith
  have h0 := hmax.hasDerivAt_eq_zero hφd
  have hpos : 0 < β ^ t * gn ^ t := by positivity
  have := (mul_eq_zero.1 h0).resolve_left hpos.ne'
  linarith

/-- Correction to Miao, p. 464: the printed intratemporal condition `−u_n/u_c = F_N(k_t, A_tn_t)`
and the true one `−u_n/u_c = A_tF_N(k_t, A_tn_t)` together force `A_t = 1` when `F_N ≠ 0`. -/
theorem rm_planner_intratemporal_misprint {ucv unv FNv A : ℝ} (huc : ucv ≠ 0) (hFN : FNv ≠ 0)
    (htrue : unv + ucv * (A * FNv) = 0) (hprinted : -unv / ucv = FNv) : A = 1 := by
  have h1 : -unv = FNv * ucv := by field_simp at hprinted; linarith
  have : ucv * FNv * (A - 1) = 0 := by linear_combination htrue + h1
  have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero huc hFN)
  linarith

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Decentralisations of the basic Ramsey model

Miao, §14.1.1, pp. 456–467. Per-capita sequences `c, i, n, k`, aggregates `C, I, N, K`,
technology `A_t = g_aᵗ`, population `gₙᵗ`. Partial derivatives of `F` are `F_K, F_N` (in capital
and in effective labour). Equilibria are described by the first-order conditions the text
derives; the necessity of the planner's conditions is proved in `RMPlanner`.

**Arrow–Debreu equilibrium** (pp. 457–460). The household's first-order conditions
`βᵗu_c = λq_t⁰`, `−βᵗu_n = λq_t⁰w_t`, `q_t⁰ = q_{t+1}⁰(R^k_{t+1} + 1 − δ)` (`RMADFOC`) imply the
Euler equation (14.7) and (14.8) (`rm_ad_euler`); conversely (14.7)–(14.8) give Arrow–Debreu
prices `q_t⁰ = βᵗu_c(c_t, n_t)/λ` (`rm_ad_of_hh`), and the two transversality conditions
`lim q_t⁰k_{t+1} = 0` and (14.9) are then equivalent (`rm_ad_tvc_iff`). The firm's first-order
conditions (14.3) follow from profit maximisation (`eq_14_3`), and firms make zero profit
(`rm_zero_profit` in `RMBasics`), so `Π = 0`.

**Households own capital** (pp. 460–461): the system (14.7), (14.8), (14.3), (14.4)
(`RMHHFOC`, `RMFirmFOC`, `RMClear`). Market clearing implies the per-capita accumulation
equation (14.2) and resource constraint (`rm_clear_percapita`).

**Firms own capital** (pp. 461–464): the asset-pricing equation (14.11) (`eq_14_11`), its forward
solution (14.12) under the no-bubble condition (14.13) (`eq_14_12`), the derivation of (14.13)
from the household's transversality condition (`eq_14_13`), the pricing kernel
`M_{t,t+j} = βʲu_c(c_{t+j}, n_{t+j})/u_c(c_t, n_t)` (`rmKernel`, `rm_kernel_zero`,
`rm_kernel_mul`), the firm's first-order condition for capital (`rm_firm_capital_foc`), the
equivalence of (14.14) with `Q ≡ 1` and (14.7) (`eq_14_14_iff_eq_14_7`, so the two sequential
arrangements have the same allocations), and the stock return `V_{t+1}/(V_t − D_t) =
u_c(c_t)/(βu_c(c_{t+1})) = R^k_{t+1} + 1 − δ` (`rm_stock_return`).

**Social planner** (pp. 464–465): competitive allocations satisfy the planner's first-order
conditions (`rm_ce_planner`: they are Pareto optimal in the first-order sense), and the planner's
allocation is supported by the prices `R^k_t = F_K`, `w_t = A_tF_N`, `q_t⁰ = βᵗu_c/u_c(c₀)`
(`rm_planner_ce`). With KPR utility the planner's conditions are equivalent to the detrended
system of p. 465, `g_a^σu_c(c̃_t, n_t) = βu_c(c̃_{t+1}, n_{t+1})[F_K(k̃_{t+1}, n_{t+1}) + 1 − δ]`
etc. (`rm_detrend_planner`), and the detrended prices are `R^k_t = F_K(k̃_t, n_t)`,
`w̃_t = F_N(k̃_t, n_t)` (`rm_detrend_prices`).

**Recursive competitive equilibrium** (pp. 465–467): with `g_a = gₙ = 1`, the household's
first-order and envelope conditions and the consistency conditions generate sequences that
satisfy the sequential equilibrium conditions (`rm_rce_sequential`).

**Correction.** The detrended competitive system printed on pp. 459–460 has
`u_c(c̃_t, n_t) = βu_c(c̃_{t+1}, n_{t+1})(R^k_{t+1} + 1 − δ)`; detrending (14.7) with KPR utility
gives the factor `g_a^σ` on the left, as in the planner's detrended system on p. 465. With the
true equation the printed one forces `g_a^σ = 1` (`rm_detrend_euler_misprint`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### Arrow–Debreu and sequential household conditions -/

/-- The household's sequential first-order conditions (14.7)–(14.8). -/
def RMHHFOC (uc un : ℝ → ℝ → ℝ) (β δ : ℝ) (c n Rk w : ℕ → ℝ) : Prop :=
  ∀ t, uc (c t) (n t) = β * uc (c (t + 1)) (n (t + 1)) * (Rk (t + 1) + 1 - δ) ∧
    -un (c t) (n t) / uc (c t) (n t) = w t

/-- The Arrow–Debreu household's first-order conditions (Miao, p. 458). -/
def RMADFOC (uc un : ℝ → ℝ → ℝ) (β δ lam : ℝ) (c n q Rk w : ℕ → ℝ) : Prop :=
  ∀ t, β ^ t * uc (c t) (n t) = lam * q t ∧ -(β ^ t * un (c t) (n t)) = lam * q t * w t ∧
    q t = q (t + 1) * (Rk (t + 1) + 1 - δ)

/-- Miao, p. 459–461: the Arrow–Debreu first-order conditions imply (14.7) and (14.8). -/
theorem rm_ad_euler {uc un : ℝ → ℝ → ℝ} {β δ lam : ℝ} {c n q Rk w : ℕ → ℝ} (hβ : 0 < β)
    (huc : ∀ t, uc (c t) (n t) ≠ 0) (h : RMADFOC uc un β δ lam c n q Rk w) :
    RMHHFOC uc un β δ c n Rk w := by
  intro t
  obtain ⟨h1, h2, h3⟩ := h t
  obtain ⟨h1', -, -⟩ := h (t + 1)
  have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
  refine ⟨?_, ?_⟩
  · have : β ^ t * uc (c t) (n t) =
        β ^ t * (β * uc (c (t + 1)) (n (t + 1)) * (Rk (t + 1) + 1 - δ)) := by
      rw [pow_succ] at h1'
      linear_combination h1 + lam * h3 - (Rk (t + 1) + 1 - δ) * h1'
    exact mul_left_cancel₀ hb this
  · rw [div_eq_iff (huc t)]
    have : β ^ t * (-un (c t) (n t)) = β ^ t * (w t * uc (c t) (n t)) := by
      linear_combination h2 - w t * h1
    exact mul_left_cancel₀ hb this

/-- Miao, p. 461 ("the equilibrium system is identical"): conversely, (14.7)–(14.8) and any
`λ ≠ 0` give Arrow–Debreu prices `q_t⁰ = βᵗu_c(c_t, n_t)/λ` satisfying the Arrow–Debreu
first-order conditions. -/
theorem rm_ad_of_hh {uc un : ℝ → ℝ → ℝ} {β δ lam : ℝ} {c n Rk w : ℕ → ℝ} (hlam : lam ≠ 0)
    (huc : ∀ t, uc (c t) (n t) ≠ 0) (h : RMHHFOC uc un β δ c n Rk w) :
    RMADFOC uc un β δ lam c n (fun t => β ^ t * uc (c t) (n t) / lam) Rk w := by
  intro t
  obtain ⟨h1, h2⟩ := h t
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [div_eq_iff (huc t)] at h2
    field_simp
    linear_combination β ^ t * h2
  · simp only [pow_succ]
    rw [h1]
    field_simp

/-- Miao, pp. 458, 461: with `q_t⁰ = βᵗu_c/λ`, the Arrow–Debreu transversality condition
`lim q_t⁰k_{t+1} = 0` is equivalent to (14.9). -/
theorem rm_ad_tvc_iff {uc : ℝ → ℝ → ℝ} {β lam : ℝ} {c n k : ℕ → ℝ} (hlam : lam ≠ 0) :
    Tendsto (fun t => β ^ t * uc (c t) (n t) / lam * k (t + 1)) atTop (𝓝 0) ↔
      Tendsto (fun t => β ^ t * uc (c t) (n t) * k (t + 1)) atTop (𝓝 0) := by
  constructor
  · intro h
    have := h.const_mul lam
    simp only [mul_zero] at this
    refine this.congr (fun t => ?_)
    field_simp
  · intro h
    have := h.div_const lam
    simp only [zero_div] at this
    refine this.congr (fun t => ?_)
    ring

/-! ### Firms and market clearing -/

/-- The firm's first-order conditions (14.3) on aggregates, `A_t = g_aᵗ`. -/
def RMFirmFOC (FK FN : ℝ → ℝ → ℝ) (ga : ℝ) (K N Rk w : ℕ → ℝ) : Prop :=
  ∀ t, FK (K t) (ga ^ t * N t) = Rk t ∧ ga ^ t * FN (K t) (ga ^ t * N t) = w t

/-- **(14.3)** (Miao, p. 458): if the firm's profit `F(K, AN) − R^kK − wN` is at a local maximum
in `K` and in `N` at `(K, N)`, and `F` has partial derivatives `F_K`, `F_N` there, then
`F_K(K, AN) = R^k` and `AF_N(K, AN) = w`. -/
theorem eq_14_3 {F FK FN : ℝ → ℝ → ℝ} {A K N Rk w : ℝ}
    (hK : HasDerivAt (fun x => F x (A * N)) (FK K (A * N)) K)
    (hN : HasDerivAt (fun y => F K y) (FN K (A * N)) (A * N))
    (hmaxK : IsLocalMax (fun x => F x (A * N) - Rk * x - w * N) K)
    (hmaxN : IsLocalMax (fun y => F K (A * y) - Rk * K - w * y) N) :
    FK K (A * N) = Rk ∧ A * FN K (A * N) = w := by
  have dK : HasDerivAt (fun x => F x (A * N) - Rk * x - w * N) (FK K (A * N) - Rk * 1) K :=
    (hK.sub ((hasDerivAt_id K).const_mul Rk)).sub_const _
  have hl : HasDerivAt (fun y => A * y) A N := by simpa using (hasDerivAt_id N).const_mul A
  have dN : HasDerivAt (fun y => F K (A * y) - Rk * K - w * y)
      (FN K (A * N) * A - w * 1) N :=
    ((hN.comp N hl).sub_const _).sub ((hasDerivAt_id N).const_mul w)
  have e1 := hmaxK.hasDerivAt_eq_zero dK
  have e2 := hmaxN.hasDerivAt_eq_zero dN
  constructor <;> linarith

/-- Market clearing (14.4a)–(14.4d). -/
def RMClear (F : ℝ → ℝ → ℝ) (ga gn δ : ℝ) (c i n k C I N K : ℕ → ℝ) : Prop :=
  ∀ t, C t = gn ^ t * c t ∧ K t = gn ^ t * k t ∧ I t = gn ^ t * i t ∧ N t = gn ^ t * n t ∧
    K (t + 1) = (1 - δ) * K t + I t ∧ C t + I t = F (K t) (ga ^ t * N t)

/-- Miao, (14.2) and (14.4): market clearing implies the per-capita accumulation equation
`gₙk_{t+1} = (1 − δ)k_t + i_t` and resource constraint `c_t + i_t = F(k_t, A_tn_t)`. -/
theorem rm_clear_percapita {F : ℝ → ℝ → ℝ} (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    {ga gn δ : ℝ} (hgn : 0 < gn) {c i n k C I N K : ℕ → ℝ}
    (h : RMClear F ga gn δ c i n k C I N K) (t : ℕ) :
    gn * k (t + 1) = (1 - δ) * k t + i t ∧ c t + i t = F (k t) (ga ^ t * n t) := by
  obtain ⟨hC, hK, hI, hN, hacc, hres⟩ := h t
  have hK1 := (h (t + 1)).2.1
  have hs : (0 : ℝ) < gn ^ t := pow_pos hgn t
  refine ⟨?_, ?_⟩
  · rw [hK1, hK, hI, pow_succ] at hacc
    have : gn ^ t * (gn * k (t + 1)) = gn ^ t * ((1 - δ) * k t + i t) := by linarith
    exact mul_left_cancel₀ hs.ne' this
  · rw [hC, hI, hK, hN] at hres
    exact (rm_planner_resource (fun s x y hs => hhom s x y hs) hgn t).1 hres

/-! ### The planner's conditions and the welfare theorems -/

/-- The planner's first-order conditions in per-capita terms (Miao, p. 464, with the
intratemporal condition corrected to `−u_n/u_c = A_tF_N`), the resource constraint and (14.2). -/
def RMPlannerFOC (uc un F FK FN : ℝ → ℝ → ℝ) (β ga gn δ : ℝ) (c i n k : ℕ → ℝ) : Prop :=
  ∀ t, uc (c t) (n t) =
      β * uc (c (t + 1)) (n (t + 1)) * (FK (k (t + 1)) (ga ^ (t + 1) * n (t + 1)) + 1 - δ) ∧
    -un (c t) (n t) / uc (c t) (n t) = ga ^ t * FN (k t) (ga ^ t * n t) ∧
    c t + i t = F (k t) (ga ^ t * n t) ∧ gn * k (t + 1) = (1 - δ) * k t + i t

/-- **Competitive allocations are Pareto optimal** (Miao, p. 465): an allocation satisfying the
sequential equilibrium conditions (14.7), (14.8), (14.3), (14.4) satisfies the planner's
first-order conditions (`F_K`, `F_N` are homogeneous of degree zero, `k, n > 0`). -/
theorem rm_ce_planner {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ : ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (hgn : 0 < gn) (hga : 0 < ga) {c i n k C I N K Rk w : ℕ → ℝ}
    (hk : ∀ t, 0 < k t) (hn : ∀ t, 0 < n t)
    (hhh : RMHHFOC uc un β δ c n Rk w) (hfirm : RMFirmFOC FK FN ga K N Rk w)
    (hcl : RMClear F ga gn δ c i n k C I N K) : RMPlannerFOC uc un F FK FN β ga gn δ c i n k := by
  have hpr : ∀ t, FK (K t) (ga ^ t * N t) = FK (k t) (ga ^ t * n t) ∧
      FN (K t) (ga ^ t * N t) = FN (k t) (ga ^ t * n t) := by
    intro t
    obtain ⟨-, hK, -, hN, -, -⟩ := hcl t
    have he : ga ^ t * N t = gn ^ t * (ga ^ t * n t) := by rw [hN]; ring
    have hs := pow_pos hgn t
    have hy := mul_pos (pow_pos hga t) (hn t)
    rw [he, hK]
    exact ⟨hFK _ _ _ hs (hk t) hy, hFN _ _ _ hs (hk t) hy⟩
  intro t
  obtain ⟨hacc, hres⟩ := rm_clear_percapita hhom hgn hcl t
  refine ⟨?_, ?_, hres, hacc⟩
  · rw [(hhh t).1, ← (hfirm (t + 1)).1, (hpr (t + 1)).1]
  · rw [(hhh t).2, ← (hfirm t).2, (hpr t).2]

/-- **The planner's allocation is an equilibrium** (Miao, p. 465, "conversely, we can also find
equilibrium prices"): an allocation satisfying the planner's conditions, with
`R^k_t = F_K(k_t, A_tn_t)`, `w_t = A_tF_N(k_t, A_tn_t)` and the aggregates `gₙᵗ ×` per capita,
satisfies (14.7), (14.8), (14.3), (14.4), and the Arrow–Debreu conditions with
`q_t⁰ = βᵗu_c(c_t, n_t)/u_c(c₀, n₀)`. -/
theorem rm_planner_ce {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ : ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (hgn : 0 < gn) (hga : 0 < ga) {c i n k : ℕ → ℝ} (hk : ∀ t, 0 < k t) (hn : ∀ t, 0 < n t)
    (huc : ∀ t, uc (c t) (n t) ≠ 0) (h : RMPlannerFOC uc un F FK FN β ga gn δ c i n k) :
    let Rk := fun t => FK (k t) (ga ^ t * n t)
    let w := fun t => ga ^ t * FN (k t) (ga ^ t * n t)
    RMHHFOC uc un β δ c n Rk w ∧
      RMFirmFOC FK FN ga (fun t => gn ^ t * k t) (fun t => gn ^ t * n t) Rk w ∧
      RMClear F ga gn δ c i n k (fun t => gn ^ t * c t) (fun t => gn ^ t * i t)
        (fun t => gn ^ t * n t) (fun t => gn ^ t * k t) ∧
      RMADFOC uc un β δ (uc (c 0) (n 0)) c n
        (fun t => β ^ t * uc (c t) (n t) / uc (c 0) (n 0)) Rk w := by
  intro Rk w
  have hhh : RMHHFOC uc un β δ c n Rk w := fun t => ⟨(h t).1, (h t).2.1⟩
  refine ⟨hhh, fun t => ?_, fun t => ?_, rm_ad_of_hh (huc 0) huc hhh⟩
  · have he : ga ^ t * (gn ^ t * n t) = gn ^ t * (ga ^ t * n t) := by ring
    have hs := pow_pos hgn t
    have hy := mul_pos (pow_pos hga t) (hn t)
    rw [he]
    exact ⟨hFK _ _ _ hs (hk t) hy, by rw [hFN _ _ _ hs (hk t) hy]⟩
  · obtain ⟨-, -, hres, hacc⟩ := h t
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · change gn ^ (t + 1) * k (t + 1) = (1 - δ) * (gn ^ t * k t) + gn ^ t * i t
      rw [pow_succ, mul_assoc, hacc]; ring
    · rw [show ga ^ t * (gn ^ t * n t) = gn ^ t * (ga ^ t * n t) by ring,
        hhom _ _ _ (pow_pos hgn t), ← hres]
      ring

/-! ### Detrending with KPR utility -/

/-- The detrended planner's system (Miao, p. 465): `g_a^σu_c(c̃_t, n_t) =
βu_c(c̃_{t+1}, n_{t+1})[F_K(k̃_{t+1}, n_{t+1}) + 1 − δ]`, `−u_n/u_c = F_N(k̃_t, n_t)`,
`c̃_t + ı̃_t = F(k̃_t, n_t)`, `gₙg_ak̃_{t+1} = (1 − δ)k̃_t + ı̃_t`. -/
def RMDetrendedFOC (uc un F FK FN : ℝ → ℝ → ℝ) (β ga gn δ σ : ℝ) (c i n k : ℕ → ℝ) : Prop :=
  ∀ t, ga ^ σ * uc (c t) (n t) =
      β * uc (c (t + 1)) (n (t + 1)) * (FK (k (t + 1)) (n (t + 1)) + 1 - δ) ∧
    -un (c t) (n t) / uc (c t) (n t) = FN (k t) (n t) ∧
    c t + i t = F (k t) (n t) ∧ gn * ga * k (t + 1) = (1 - δ) * k t + i t

/-- Miao, p. 465: with the KPR scaling `u_c(λc, n) = λ^{−σ}u_c(c, n)`, `u_n(λc, n) =
λ^{1−σ}u_n(c, n)` (true for (14.5), `rm_kpr_uc_scale`, `rm_kpr_un_scale`, and for (14.6) with
`σ = 1`) and constant returns, the planner's conditions for `x_t = g_aᵗx̃_t` (`x = c, i, k`) are
equivalent to the detrended system. -/
theorem rm_detrend_planner {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ σ : ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    (huc : ∀ l x y, 0 < l → 0 < x → uc (l * x) y = l ^ (-σ) * uc x y)
    (hun : ∀ l x y, 0 < l → 0 < x → un (l * x) y = l ^ (1 - σ) * un x y)
    (hga : 0 < ga) {c i n k : ℕ → ℝ} (hc : ∀ t, 0 < c t) (hk : ∀ t, 0 < k t)
    (hn : ∀ t, 0 < n t) (hucp : ∀ t, uc (c t) (n t) ≠ 0) :
    RMPlannerFOC uc un F FK FN β ga gn δ (fun t => ga ^ t * c t) (fun t => ga ^ t * i t) n
        (fun t => ga ^ t * k t) ↔ RMDetrendedFOC uc un F FK FN β ga gn δ σ c i n k := by
  have hA : ∀ t, (0 : ℝ) < ga ^ t := fun t => pow_pos hga t
  have hp : ∀ t : ℕ, (ga ^ t) ^ (-σ) ≠ 0 := fun t => (Real.rpow_pos_of_pos (hA t) _).ne'
  have hsucc : ∀ t : ℕ, (ga ^ (t + 1)) ^ (-σ) = (ga ^ t) ^ (-σ) * ga ^ (-σ) := fun t => by
    rw [pow_succ, Real.mul_rpow (hA t).le hga.le]
  have hgs : ga ^ σ * ga ^ (-σ) = 1 := by
    rw [← Real.rpow_add hga]; simp
  have hrat : ∀ t : ℕ, (ga ^ t) ^ (1 - σ) = ga ^ t * (ga ^ t) ^ (-σ) := fun t => by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add (hA t), Real.rpow_one]
  have hK : ∀ t, FK (ga ^ t * k t) (ga ^ t * n t) = FK (k t) (n t) :=
    fun t => hFK _ _ _ (hA t) (hk t) (hn t)
  have hN : ∀ t, FN (ga ^ t * k t) (ga ^ t * n t) = FN (k t) (n t) :=
    fun t => hFN _ _ _ (hA t) (hk t) (hn t)
  have hF : ∀ t, F (ga ^ t * k t) (ga ^ t * n t) = ga ^ t * F (k t) (n t) :=
    fun t => hhom _ _ _ (hA t)
  have hu : ∀ t, uc (ga ^ t * c t) (n t) = (ga ^ t) ^ (-σ) * uc (c t) (n t) :=
    fun t => huc _ _ _ (hA t) (hc t)
  have hv : ∀ t, un (ga ^ t * c t) (n t) = (ga ^ t) ^ (1 - σ) * un (c t) (n t) :=
    fun t => hun _ _ _ (hA t) (hc t)
  have hmrs : ∀ t, -un (ga ^ t * c t) (n t) / uc (ga ^ t * c t) (n t) =
      ga ^ t * (-un (c t) (n t) / uc (c t) (n t)) := fun t => by
    rw [hu, hv, hrat]
    have := hp t
    have := hucp t
    field_simp
  apply forall_congr'
  intro t
  beta_reduce
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [hu, hu, hK, hsucc]
    constructor
    · intro h
      have : (ga ^ t) ^ (-σ) * (ga ^ σ * uc (c t) (n t)) = (ga ^ t) ^ (-σ) *
          (β * uc (c (t + 1)) (n (t + 1)) * (FK (k (t + 1)) (n (t + 1)) + 1 - δ)) := by
        linear_combination ga ^ σ * h + (ga ^ t) ^ (-σ) * β * uc (c (t + 1)) (n (t + 1)) *
          (FK (k (t + 1)) (n (t + 1)) + 1 - δ) * hgs
      exact mul_left_cancel₀ (hp t) this
    · intro h
      linear_combination (ga ^ t) ^ (-σ) * ga ^ (-σ) * h - (ga ^ t) ^ (-σ) * uc (c t) (n t) * hgs
  · rw [hmrs, hN]
    constructor
    · intro h; exact mul_left_cancel₀ (hA t).ne' h
    · intro h; rw [h]
  · rw [hF]
    constructor
    · intro h
      have : ga ^ t * (c t + i t) = ga ^ t * F (k t) (n t) := by linarith
      exact mul_left_cancel₀ (hA t).ne' this
    · intro h; rw [← h]; ring
  · rw [pow_succ]
    constructor
    · intro h
      have : ga ^ t * (gn * ga * k (t + 1)) = ga ^ t * ((1 - δ) * k t + i t) := by linarith
      exact mul_left_cancel₀ (hA t).ne' this
    · intro h
      linear_combination ga ^ t * h

/-- Miao, p. 460: detrended prices. With `K_t = gₙᵗg_aᵗk̃_t`, `N_t = gₙᵗn_t`, (14.3) gives
`R^k_t = F_K(k̃_t, n_t)` and `w̃_t = w_t/g_aᵗ = F_N(k̃_t, n_t)`. -/
theorem rm_detrend_prices {FK FN : ℝ → ℝ → ℝ}
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    {ga gn : ℝ} (hga : 0 < ga) (hgn : 0 < gn) {kt n : ℝ} (hk : 0 < kt) (hn : 0 < n) (t : ℕ) :
    FK (gn ^ t * ga ^ t * kt) (ga ^ t * (gn ^ t * n)) = FK kt n ∧
      ga ^ t * FN (gn ^ t * ga ^ t * kt) (ga ^ t * (gn ^ t * n)) / ga ^ t = FN kt n := by
  have hs : (0 : ℝ) < gn ^ t * ga ^ t := mul_pos (pow_pos hgn t) (pow_pos hga t)
  have he : ga ^ t * (gn ^ t * n) = (gn ^ t * ga ^ t) * n := by ring
  rw [he, hFK _ _ _ hs hk hn, hFN _ _ _ hs hk hn]
  exact ⟨rfl, by field_simp [(pow_pos hga t).ne']⟩

/-- Correction to Miao, pp. 459–460: the printed detrended Euler equation
`u_c(c̃_t) = βu_c(c̃_{t+1})(R^k_{t+1} + 1 − δ)` and the true one
`g_a^σu_c(c̃_t) = βu_c(c̃_{t+1})(R^k_{t+1} + 1 − δ)` hold together only if `g_a^σ = 1`. -/
theorem rm_detrend_euler_misprint {u0 u1 β R δ gs : ℝ} (hu : u0 ≠ 0)
    (htrue : gs * u0 = β * u1 * (R + 1 - δ)) (hprinted : u0 = β * u1 * (R + 1 - δ)) : gs = 1 := by
  have : (gs - 1) * u0 = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_right hu
  linarith

/-! ### Firms own capital -/

/-- **(14.11)** (Miao, p. 462): the first-order condition for share holdings
`u_c(c_t)(V_t − D_t) = βu_c(c_{t+1})V_{t+1}` gives `V_t = D_t + βu_c(c_{t+1})/u_c(c_t) V_{t+1}`. -/
theorem eq_14_11 {m0 m1 V0 V1 D0 β : ℝ} (hm : m0 ≠ 0) (h : m0 * (V0 - D0) = β * m1 * V1) :
    V0 = D0 + β * m1 / m0 * V1 := by
  field_simp
  linarith

/-- The partial-sum identity behind (14.12): iterating (14.11) `T` times,
`u_c(c_t)V_t = ∑_{j<T} βʲu_c(c_{t+j})D_{t+j} + β^Tu_c(c_{t+T})V_{t+T}`. -/
theorem rm_value_partial {m V D : ℕ → ℝ} {β : ℝ}
    (h : ∀ s, m s * (V s - D s) = β * m (s + 1) * V (s + 1)) (t T : ℕ) :
    m t * V t = ∑ j ∈ Finset.range T, β ^ j * m (t + j) * D (t + j) +
      β ^ T * m (t + T) * V (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have := h (t + T)
    rw [show t + (T + 1) = t + T + 1 by ring, pow_succ]
    linear_combination β ^ T * this

/-- **(14.12)** (Miao, p. 462): if (14.11) holds at every date and the no-bubble condition
(14.13) holds, then `V_t = ∑_{j≥0} βʲu_c(c_{t+j})/u_c(c_t) D_{t+j}` (as the limit of partial
sums). -/
theorem eq_14_12 {m V D : ℕ → ℝ} {β : ℝ} (hm : ∀ s, m s ≠ 0)
    (h : ∀ s, m s * (V s - D s) = β * m (s + 1) * V (s + 1)) (t : ℕ)
    (hnb : Tendsto (fun j => β ^ j * m (t + j) * V (t + j)) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * m (t + j) / m t * D (t + j)) atTop
      (𝓝 (V t)) := by
  have hT : ∀ T, ∑ j ∈ Finset.range T, β ^ j * m (t + j) / m t * D (t + j) =
      V t - β ^ T * m (t + T) * V (t + T) / m t := by
    intro T
    have := rm_value_partial h t T
    have hsum : ∑ j ∈ Finset.range T, β ^ j * m (t + j) / m t * D (t + j) =
        (∑ j ∈ Finset.range T, β ^ j * m (t + j) * D (t + j)) / m t := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum]
    field_simp [hm t]
    linarith
  simp only [hT]
  have := (hnb.div_const (m t)).const_sub (V t)
  simpa using this

/-- **(14.13)** (Miao, pp. 462–463): the household's transversality condition
`lim βᵗu_c(c_t)ψ_{t+1}(V_t − D_t) = 0`, `ψ ≡ 1` and the share first-order condition give the
no-bubble condition `lim_j βʲu_c(c_{t+j})V_{t+j} = 0` at every date `t`. -/
theorem eq_14_13 {m V D ψ : ℕ → ℝ} {β : ℝ} (hβ : 0 < β) (hψ : ∀ s, ψ s = 1)
    (h : ∀ s, m s * (V s - D s) = β * m (s + 1) * V (s + 1))
    (htvc : Tendsto (fun s => β ^ s * m s * ψ (s + 1) * (V s - D s)) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun j => β ^ j * m (t + j) * V (t + j)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s => β ^ (s + 1) * m (s + 1) * V (s + 1)) atTop (𝓝 0) := by
    refine htvc.congr (fun s => ?_)
    rw [hψ, mul_one, mul_assoc, h s, pow_succ]; ring
  have h2 : Tendsto (fun s => β ^ s * m s * V s) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).1 h1
  have h3 := ((tendsto_add_atTop_iff_nat t).2 h2).const_mul (β ^ t)⁻¹
  simp only [mul_zero] at h3
  refine h3.congr (fun j => ?_)
  rw [show j + t = t + j by ring, pow_add]
  field_simp [(pow_pos hβ t).ne']

/-- The pricing kernel `M_{t,t+j} = βʲu_c(c_{t+j})/u_c(c_t)` (Miao, p. 463). -/
noncomputable def rmKernel (β : ℝ) (m : ℕ → ℝ) (t j : ℕ) : ℝ :=
  β ^ j * m (t + j) / m t

/-- Miao, p. 462: `M_{t,t} = 1`. -/
theorem rm_kernel_zero (β : ℝ) {m : ℕ → ℝ} (t : ℕ) (hm : m t ≠ 0) : rmKernel β m t 0 = 1 := by
  simp [rmKernel, hm]

/-- The kernel is consistent across dates: `M_{t,t+j}M_{t+j,t+j+l} = M_{t,t+j+l}`. -/
theorem rm_kernel_mul (β : ℝ) {m : ℕ → ℝ} (hm : ∀ s, m s ≠ 0) (t j l : ℕ) :
    rmKernel β m t j * rmKernel β m (t + j) l = rmKernel β m t (j + l) := by
  simp only [rmKernel, pow_add, add_assoc]
  field_simp [hm (t + j)]

/-- Miao, (14.14), p. 463: the firm's first-order condition for `K_{t+1}`. If raising `K_{t+1}`
to `x` (financed by date-`t` dividends, paid back in date-`t+1` dividends
`F(x, A_{t+1}N_{t+1}) + (1 − δ)x`) leaves the value `−x + M_{t,t+1}[F(x, AN) + (1 − δ)x]` at a
local maximum at `K_{t+1}`, then `1 = M_{t,t+1}[F_K(K_{t+1}, A_{t+1}N_{t+1}) + 1 − δ]`, i.e.
(14.14) with `Q_t = Q_{t+1} = 1`. -/
theorem rm_firm_capital_foc {F FK : ℝ → ℝ → ℝ} {M δ K1 L1 : ℝ}
    (hF : HasDerivAt (fun x => F x L1) (FK K1 L1) K1)
    (hmax : IsLocalMax (fun x => -x + M * (F x L1 + (1 - δ) * x)) K1) :
    1 = M * (FK K1 L1 + (1 - δ) * 1) := by
  have hd : HasDerivAt (fun x => -x + M * (F x L1 + (1 - δ) * x))
      (-1 + M * (FK K1 L1 + (1 - δ) * 1)) K1 :=
    (hasDerivAt_id K1).neg.add ((hF.add ((hasDerivAt_id K1).const_mul (1 - δ))).const_mul M)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-- Miao, p. 463: with `Q ≡ 1`, `M_{t,t+1} = βu_c(c_{t+1})/u_c(c_t)` and `R^k = F_K`, the firm's
condition (14.14) is equivalent to the household's Euler equation (14.7); so the arrangements
"households own capital" and "firms own capital" have the same equilibrium allocations. -/
theorem eq_14_14_iff_eq_14_7 {m0 m1 β FK δ : ℝ} (hm : m0 ≠ 0) :
    (1 = β * m1 / m0 * (FK + (1 - δ) * 1)) ↔ m0 = β * m1 * (FK + 1 - δ) := by
  constructor
  · intro h; field_simp at h; linarith
  · intro h; field_simp; linarith

/-- Miao, pp. 463–464: the stock return `V_{t+1}/(V_t − D_t) = u_c(c_t)/(βu_c(c_{t+1}))
= R^k_{t+1} + 1 − δ`, from the share first-order condition and (14.7). -/
theorem rm_stock_return {m0 m1 V0 V1 D0 β R δ : ℝ} (hβ : β ≠ 0) (hm1 : m1 ≠ 0)
    (hex : V0 - D0 ≠ 0) (h : m0 * (V0 - D0) = β * m1 * V1) (heul : m0 = β * m1 * (R + 1 - δ)) :
    V1 / (V0 - D0) = m0 / (β * m1) ∧ m0 / (β * m1) = R + 1 - δ := by
  refine ⟨?_, ?_⟩
  · rw [div_eq_div_iff hex (mul_ne_zero hβ hm1)]; linarith
  · rw [heul]; field_simp

/-! ### Recursive competitive equilibrium -/

/-- **Recursive competitive equilibrium generates a sequential equilibrium** (Miao, pp. 466–467,
`g_a = gₙ = 1`). Suppose the decision rules `g^c, g^n, g` and the law of motion `G` satisfy the
household's first-order conditions `u_c = βV_k(g(k, K), G(K))`, `−u_n = u_cW(K)`, the envelope
condition `V_k(k, K) = u_c(R^k(K) + 1 − δ)`, the price equations (14.15), and the consistency and
market-clearing conditions `g(K, K) = G(K)`, `G(K) − (1 − δ)K + C = F(K, N)`. Then the sequences
`K_{t+1} = G(K_t)`, `C_t = g^c(K_t, K_t)`, `N_t = g^n(K_t, K_t)` with prices `R^k(K_t)`, `W(K_t)`
satisfy (14.7), (14.8), (14.3) and the resource constraint. -/
theorem rm_rce_sequential {uc un F FK FN : ℝ → ℝ → ℝ} {Vk gc gnl g : ℝ → ℝ → ℝ}
    {G Rk W : ℝ → ℝ} {β δ : ℝ}
    (hfoc : ∀ k K, uc (gc k K) (gnl k K) = β * Vk (g k K) (G K))
    (hlab : ∀ k K, -un (gc k K) (gnl k K) = uc (gc k K) (gnl k K) * W K)
    (henv : ∀ k K, Vk k K = uc (gc k K) (gnl k K) * (Rk K + 1 - δ))
    (hprice : ∀ K, FK K (gnl K K) = Rk K ∧ FN K (gnl K K) = W K)
    (hcons : ∀ K, g K K = G K) (hres : ∀ K, G K - (1 - δ) * K + gc K K = F K (gnl K K))
    (huc : ∀ k K, uc (gc k K) (gnl k K) ≠ 0) (K : ℕ → ℝ) (hK : ∀ t, K (t + 1) = G (K t)) :
    let C := fun t => gc (K t) (K t)
    let N := fun t => gnl (K t) (K t)
    RMHHFOC uc un β δ C N (fun t => Rk (K t)) (fun t => W (K t)) ∧
      RMFirmFOC FK FN 1 K N (fun t => Rk (K t)) (fun t => W (K t)) ∧
      ∀ t, K (t + 1) - (1 - δ) * K t + C t = F (K t) (N t) := by
  intro C N
  refine ⟨fun t => ⟨?_, ?_⟩, fun t => ?_, fun t => ?_⟩
  · simp only [C, N]
    rw [hfoc, hcons, ← hK, henv]
    ring
  · simp only [C, N]
    rw [div_eq_iff (huc _ _), hlab]; ring
  · simp only [one_pow, one_mul, N]
    exact ⟨(hprice _).1, (hprice _).2⟩
  · simp only [C, N]
    rw [hK, hres]

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The steady state of the basic Ramsey model

Miao, §14.1.1, pp. 459 and 465: the steady state of the detrended system (balanced growth).

* A constant detrended path solves the detrended planner's system iff
  `F_K(k̃, n) = g_a^σ/β − 1 + δ` (the **modified golden rule**), `−u_n/u_c = F_N(k̃, n)`,
  `ı̃ = (gₙg_a − 1 + δ)k̃` and `c̃ = F(k̃, n) − ı̃` (`rm_steady_state_iff`).
* With `f(x) = F_K(x, 1)` continuous and strictly decreasing on `(0, ∞)`, `f(0⁺) = ∞`,
  `f(∞) = 0`, the capital–labour ratio solving `f(x) = r` exists and is unique for every `r > 0`
  (`rm_steady_ratio_exists_unique`); the target `r = g_a^σ/β − 1 + δ` is positive when
  `g_a ≥ 1` (`rm_mgr_pos`). By homogeneity `F_K(k̃, n) = F_K(k̃/n, 1)` (`rm_FK_ratio`).
* **Comparative statics**: the ratio is decreasing in `r` (`rm_steady_ratio_anti`), so it rises
  with `β` (`rm_cs_beta`) and falls with `δ` (`rm_cs_delta`), with `g_a` when `σ > 0`
  (`rm_cs_ga`), and with `σ` when `g_a > 1` (`rm_cs_sigma`).
* **Balanced growth** (p. 459): at a steady state of the detrended system `C, I, K, Y` grow at
  the gross rate `gₙg_a`, the wage at `g_a`, and the rental rate is constant
  (`rm_balanced_growth`).
* **A worked example**: log utility `ln c + θ ln(1 − n)` and Cobb–Douglas
  `F = k^αn^{1−α}`. The partial derivatives (`rm_cd_FK_hasDerivAt`, `rm_cd_FN_hasDerivAt`),
  homogeneity (`rm_cd_homog`), the hypotheses of the existence theorem (`rm_cd_FK_strictAnti`),
  and the closed-form steady state `x* = (α/r)^{1/(1−α)}`,
  `n* = (1 − α)x*^α/((1 − α)x*^α + θχ)`, `χ = x*^α − (gₙg_a − 1 + δ)x*`, which solves the
  detrended system when `βgₙ < 1` (`rm_cd_log_steady`, `rm_cd_chi_pos`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- **The steady state** (Miao, pp. 459, 465): a constant path `(c̃, ı̃, n, k̃)` solves the
detrended system iff the modified golden rule `F_K(k̃, n) = g_a^σ/β − 1 + δ`, the labour condition
`−u_n/u_c = F_N(k̃, n)`, `ı̃ = (gₙg_a − 1 + δ)k̃` and `c̃ = F(k̃, n) − ı̃` hold. -/
theorem rm_steady_state_iff {uc un F FK FN : ℝ → ℝ → ℝ} {β ga gn δ σ cs is ns ks : ℝ}
    (hβ : 0 < β) (huc : uc cs ns ≠ 0) :
    RMDetrendedFOC uc un F FK FN β ga gn δ σ (fun _ => cs) (fun _ => is) (fun _ => ns)
        (fun _ => ks) ↔
      FK ks ns = ga ^ σ / β - 1 + δ ∧ -un cs ns / uc cs ns = FN ks ns ∧
        is = (gn * ga - 1 + δ) * ks ∧ cs = F ks ns - is := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4⟩ := h 0
    refine ⟨?_, h2, by linarith, by linarith⟩
    have : β * uc cs ns * (FK ks ns - (ga ^ σ / β - 1 + δ)) = 0 := by
      field_simp
      linear_combination -h1
    have := (mul_eq_zero.1 this).resolve_left (mul_ne_zero hβ.ne' huc)
    linarith
  · rintro ⟨h1, h2, h3, h4⟩ t
    refine ⟨?_, h2, by linarith, by rw [h3]; ring⟩
    rw [h1]
    field_simp
    ring

/-- Miao, p. 465: by homogeneity of degree zero, `F_K(k̃, n) = F_K(k̃/n, 1)`. -/
theorem rm_FK_ratio {FK : ℝ → ℝ → ℝ}
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y) {k n : ℝ}
    (hk : 0 < k) (hn : 0 < n) : FK k n = FK (k / n) 1 := by
  have := hFK n (k / n) 1 hn (div_pos hk hn) one_pos
  rw [mul_div_cancel₀ k hn.ne', mul_one] at this
  exact this

/-- The modified-golden-rule target `g_a^σ/β − 1 + δ` is positive for `g_a ≥ 1`, `σ ≥ 0`,
`0 < β < 1`, `δ ≥ 0`. -/
theorem rm_mgr_pos {β ga δ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hga : 1 ≤ ga) (hσ : 0 ≤ σ)
    (hδ : 0 ≤ δ) : 0 < ga ^ σ / β - 1 + δ := by
  have h1 : 1 ≤ ga ^ σ := Real.one_le_rpow hga hσ
  have h2 : 1 < ga ^ σ / β := by rw [lt_div_iff₀ hβ0]; linarith
  linarith

/-- **Existence and uniqueness of the steady-state capital–labour ratio** (Miao, p. 465, using
the conditions of p. 457): if `f = F_K(·, 1)` is continuous and strictly decreasing on
`(0, ∞)` with `f(0⁺) = ∞` and `f(∞) = 0`, then `f(x) = r` has exactly one solution `x > 0` for
each `r > 0`. -/
theorem rm_steady_ratio_exists_unique {f : ℝ → ℝ} (hc : ContinuousOn f (Set.Ioi 0))
    (hanti : StrictAntiOn f (Set.Ioi 0)) (h0 : Tendsto f (𝓝[>] 0) atTop)
    (htop : Tendsto f atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) : ∃! x, 0 < x ∧ f x = r := by
  obtain ⟨a, ha0, har⟩ : ∃ a, 0 < a ∧ r < f a := by
    have e1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), r + 1 ≤ f x := h0.eventually (eventually_ge_atTop _)
    have e2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
    obtain ⟨a, h1, h2⟩ := (e1.and e2).exists
    exact ⟨a, h2, by linarith⟩
  obtain ⟨b, hab, hbr⟩ : ∃ b, a ≤ b ∧ f b < r := by
    have e1 : ∀ᶠ x in atTop, f x < r := htop.eventually (gt_mem_nhds hr)
    obtain ⟨b, hb⟩ := (e1.and (eventually_ge_atTop a)).exists
    exact ⟨b, hb.2, hb.1⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha0 hx.1
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab (hc.mono hsub) ⟨hbr.le, har.le⟩
  refine ⟨x, ⟨hsub hx, hfx⟩, fun y ⟨hy, hfy⟩ => ?_⟩
  exact hanti.injOn hy (hsub hx) (hfy.trans hfx.symm)

/-- **Comparative statics** (Miao, §14.1.1): the steady-state ratio is decreasing in the target
`r`: if `f(x₁) = r₁ < r₂ = f(x₂)` then `x₂ < x₁`. -/
theorem rm_steady_ratio_anti {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 r1 r2 : ℝ}
    (hx1 : 0 < x1) (hx2 : 0 < x2) (h1 : f x1 = r1) (h2 : f x2 = r2) (hr : r1 < r2) : x2 < x1 := by
  by_contra hc
  rcases (not_lt.1 hc).eq_or_lt with h | h
  · subst h; linarith
  · have := hanti hx1 hx2 h; linarith

/-- Comparative statics: a more patient economy (`β₁ < β₂`) has a higher capital–labour ratio. -/
theorem rm_cs_beta {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β1 β2 ga δ σ : ℝ}
    (hβ1 : 0 < β1) (hβ : β1 < β2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = ga ^ σ / β1 - 1 + δ) (h2 : f x2 = ga ^ σ / β2 - 1 + δ) (hga : 0 < ga) :
    x1 < x2 := by
  refine rm_steady_ratio_anti hanti hx2 hx1 h2 h1 ?_
  have : ga ^ σ / β2 < ga ^ σ / β1 :=
    div_lt_div_of_pos_left (Real.rpow_pos_of_pos hga σ) hβ1 hβ
  linarith

/-- Comparative statics: faster depreciation lowers the capital–labour ratio. -/
theorem rm_cs_delta {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β ga δ1 δ2 σ : ℝ}
    (hδ : δ1 < δ2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = ga ^ σ / β - 1 + δ1) (h2 : f x2 = ga ^ σ / β - 1 + δ2) : x2 < x1 :=
  rm_steady_ratio_anti hanti hx1 hx2 h1 h2 (by linarith)

/-- Comparative statics: faster technical progress lowers the detrended capital–labour ratio
when `σ > 0`. -/
theorem rm_cs_ga {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β g1 g2 δ σ : ℝ}
    (hβ : 0 < β) (hσ : 0 < σ) (hg1 : 0 < g1) (hg : g1 < g2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = g1 ^ σ / β - 1 + δ) (h2 : f x2 = g2 ^ σ / β - 1 + δ) : x2 < x1 := by
  refine rm_steady_ratio_anti hanti hx1 hx2 h1 h2 ?_
  have : g1 ^ σ < g2 ^ σ := Real.rpow_lt_rpow hg1.le hg hσ
  have := div_lt_div_of_pos_right this hβ
  linarith

/-- Comparative statics: with `g_a > 1`, a higher `σ` (lower intertemporal elasticity) lowers the
detrended capital–labour ratio. -/
theorem rm_cs_sigma {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0)) {x1 x2 β ga δ σ1 σ2 : ℝ}
    (hβ : 0 < β) (hga : 1 < ga) (hσ : σ1 < σ2) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h1 : f x1 = ga ^ σ1 / β - 1 + δ) (h2 : f x2 = ga ^ σ2 / β - 1 + δ) : x2 < x1 := by
  refine rm_steady_ratio_anti hanti hx1 hx2 h1 h2 ?_
  have : ga ^ σ1 < ga ^ σ2 := Real.rpow_lt_rpow_of_exponent_lt hga hσ
  have := div_lt_div_of_pos_right this hβ
  linarith

/-- **Balanced growth** (Miao, p. 459): at a steady state `(c̃, ı̃, k̃, n)` of the detrended
system, the aggregates `X_t = gₙᵗg_aᵗx̃` (`X = C, I, K`) and `Y_t = F(K_t, A_tN_t)` grow at the
gross rate `gₙg_a`, the wage `w_t = A_tF_N(K_t, A_tN_t)` grows at `g_a` and the rental rate
`F_K(K_t, A_tN_t)` is constant. -/
theorem rm_balanced_growth {F FK FN : ℝ → ℝ → ℝ}
    (hhom : ∀ s x y, 0 < s → F (s * x) (s * y) = s * F x y)
    (hFK : ∀ s x y, 0 < s → 0 < x → 0 < y → FK (s * x) (s * y) = FK x y)
    (hFN : ∀ s x y, 0 < s → 0 < x → 0 < y → FN (s * x) (s * y) = FN x y)
    {ga gn x ks ns : ℝ} (hga : 0 < ga) (hgn : 0 < gn) (hk : 0 < ks) (hn : 0 < ns) (t : ℕ) :
    let X := fun s : ℕ => gn ^ s * ga ^ s * x
    let K := fun s : ℕ => gn ^ s * ga ^ s * ks
    let L := fun s : ℕ => ga ^ s * (gn ^ s * ns)
    X (t + 1) = gn * ga * X t ∧ F (K (t + 1)) (L (t + 1)) = gn * ga * F (K t) (L t) ∧
      F (K t) (L t) = gn ^ t * ga ^ t * F ks ns ∧
      ga ^ (t + 1) * FN (K (t + 1)) (L (t + 1)) = ga * (ga ^ t * FN (K t) (L t)) ∧
      FK (K (t + 1)) (L (t + 1)) = FK (K t) (L t) := by
  intro X K L
  have hL : ∀ s, L s = (gn ^ s * ga ^ s) * ns := fun s => by simp only [L]; ring
  have hs : ∀ s : ℕ, (0 : ℝ) < gn ^ s * ga ^ s := fun s => mul_pos (pow_pos hgn s) (pow_pos hga s)
  have hY : ∀ s, F (K s) (L s) = gn ^ s * ga ^ s * F ks ns := fun s => by
    rw [hL]; exact hhom _ _ _ (hs s)
  have hR : ∀ s, FK (K s) (L s) = FK ks ns := fun s => by
    rw [hL]; exact hFK _ _ _ (hs s) hk hn
  have hW : ∀ s, FN (K s) (L s) = FN ks ns := fun s => by
    rw [hL]; exact hFN _ _ _ (hs s) hk hn
  refine ⟨by simp only [X, pow_succ]; ring, by rw [hY, hY, pow_succ, pow_succ]; ring, hY t,
    by rw [hW, hW, pow_succ]; ring, by rw [hR, hR]⟩

/-! ### Worked example: log utility and Cobb–Douglas -/

/-- Cobb–Douglas `F(k, n) = k^αn^{1−α}`. -/
noncomputable def rmCD (α k n : ℝ) : ℝ := k ^ α * n ^ (1 - α)

/-- `F_K = αk^{α−1}n^{1−α}`. -/
noncomputable def rmCDK (α k n : ℝ) : ℝ := α * k ^ (α - 1) * n ^ (1 - α)

/-- `F_N = (1 − α)k^αn^{−α}`. -/
noncomputable def rmCDN (α k n : ℝ) : ℝ := (1 - α) * k ^ α * n ^ (-α)

/-- The Cobb–Douglas partial derivative in capital. -/
theorem rm_cd_FK_hasDerivAt (α : ℝ) {k : ℝ} (hk : 0 < k) (n : ℝ) :
    HasDerivAt (fun z => rmCD α z n) (rmCDK α k n) k := by
  have := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).mul_const (n ^ (1 - α))
  simpa [rmCD, rmCDK] using this

/-- The Cobb–Douglas partial derivative in labour. -/
theorem rm_cd_FN_hasDerivAt (α k : ℝ) {n : ℝ} (hn : 0 < n) :
    HasDerivAt (fun z => rmCD α k z) (rmCDN α k n) n := by
  have := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hn.ne')).const_mul (k ^ α)
  convert this using 1
  · rfl
  · simp only [rmCDN, show 1 - α - 1 = -α by ring]
    ring

/-- Cobb–Douglas is homogeneous of degree one and its partials of degree zero. -/
theorem rm_cd_homog (α : ℝ) {s x y : ℝ} (hs : 0 < s) (hx : 0 < x) (hy : 0 < y) :
    rmCD α (s * x) (s * y) = s * rmCD α x y ∧ rmCDK α (s * x) (s * y) = rmCDK α x y ∧
      rmCDN α (s * x) (s * y) = rmCDN α x y := by
  simp only [rmCD, rmCDK, rmCDN, Real.mul_rpow hs.le hx.le, Real.mul_rpow hs.le hy.le]
  have e1 : s ^ α * s ^ (1 - α) = s := by
    rw [← Real.rpow_add hs]; simp
  have e2 : s ^ (α - 1) * s ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hs]; simp
  have e3 : s ^ α * s ^ (-α) = 1 := by
    rw [← Real.rpow_add hs]; simp
  refine ⟨?_, ?_, ?_⟩
  · linear_combination x ^ α * y ^ (1 - α) * e1
  · linear_combination α * x ^ (α - 1) * y ^ (1 - α) * e2
  · linear_combination (1 - α) * x ^ α * y ^ (-α) * e3

/-- The marginal product `F_K(x, 1) = αx^{α−1}` is continuous and strictly decreasing on
`(0, ∞)`, so (with `rm_cd_inada_zero`, `rm_cd_inada_top`) the existence theorem applies. -/
theorem rm_cd_FK_strictAnti {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    StrictAntiOn (fun x => rmCDK α x 1) (Set.Ioi 0) ∧
      ContinuousOn (fun x => rmCDK α x 1) (Set.Ioi 0) := by
  refine ⟨fun x hx y _ hxy => ?_, ?_⟩
  · simp only [rmCDK, Real.one_rpow, mul_one]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx hxy (by linarith)) hα0
  · intro x hx
    simp only [rmCDK, Real.one_rpow, mul_one]
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx))).const_mul α).continuousWithinAt

/-- In the worked example the steady-state consumption–labour ratio `χ = x^α − (gₙg_a − 1 + δ)x`
at `x = (α/r)^{1/(1−α)}`, `r = g_a/β − 1 + δ`, is positive when `βgₙ < 1`. -/
theorem rm_cd_chi_pos {α β ga gn δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hga : 0 < ga) (hr : 0 < ga / β - 1 + δ) (hβgn : β * gn < 1) :
    let r := ga / β - 1 + δ
    let x := (α / r) ^ (1 / (1 - α))
    0 < x ^ α - (gn * ga - 1 + δ) * x := by
  intro r x
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hα0 hr) _
  have hxa : x ^ (α - 1) = r / α := by
    simp only [x]
    rw [← Real.rpow_mul (div_pos hα0 hr).le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show 1 - α ≠ 0 by linarith]; ring, Real.rpow_neg_one, inv_div]
  have hxα : x ^ α = x * (r / α) := by
    rw [← hxa, ← Real.rpow_one_add' hx.le (by linarith)]; ring_nf
  rw [hxα]
  have h1 : r ≤ r / α := by rw [le_div_iff₀ hα0]; nlinarith
  have h2 : gn * ga - 1 + δ < r := by
    have : gn * ga < ga / β := by
      rw [lt_div_iff₀ hβ]; nlinarith
    simp only [r]; linarith
  nlinarith

/-- **Worked steady state** (Miao, §14.1.1, log utility (14.6) with `v(n) = θ ln(1 − n)`,
Cobb–Douglas): with `r = g_a/β − 1 + δ > 0`, `x = (α/r)^{1/(1−α)}`,
`χ = x^α − (gₙg_a − 1 + δ)x > 0`, `n = (1 − α)x^α/((1 − α)x^α + θχ)`, `k̃ = xn`,
`ı̃ = (gₙg_a − 1 + δ)k̃`, `c̃ = χn`, the constant path
solves the detrended system (`σ = 1`, `u_c = 1/c`, `u_n = −θ/(1 − n)`). -/
theorem rm_cd_log_steady {α β ga gn δ θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hθ : 0 < θ) (hr : 0 < ga / β - 1 + δ)
    (hχ : 0 < ((α / (ga / β - 1 + δ)) ^ (1 / (1 - α))) ^ α -
      (gn * ga - 1 + δ) * (α / (ga / β - 1 + δ)) ^ (1 / (1 - α))) :
    let r := ga / β - 1 + δ
    let x := (α / r) ^ (1 / (1 - α))
    let χ := x ^ α - (gn * ga - 1 + δ) * x
    let ns := (1 - α) * x ^ α / ((1 - α) * x ^ α + θ * χ)
    RMDetrendedFOC (fun c _ => 1 / c) (fun _ n => -θ / (1 - n)) (rmCD α) (rmCDK α) (rmCDN α)
      β ga gn δ 1 (fun _ => χ * ns) (fun _ => (gn * ga - 1 + δ) * (x * ns)) (fun _ => ns)
      (fun _ => x * ns) := by
  intro r x χ ns
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hα0 hr) _
  have hxa : x ^ (α - 1) = r / α := by
    simp only [x]
    rw [← Real.rpow_mul (div_pos hα0 hr).le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show 1 - α ≠ 0 by linarith]; ring, Real.rpow_neg_one, inv_div]
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hden : 0 < (1 - α) * x ^ α + θ * χ := by
    have : 0 < 1 - α := by linarith
    positivity
  have hns : 0 < ns := div_pos (mul_pos (by linarith) hxα) hden
  have hns1 : ns < 1 := by
    rw [div_lt_one hden]; nlinarith
  have hc : 0 < χ * ns := mul_pos hχ hns
  -- the Cobb–Douglas functions at `(xn, n)`
  have hK : rmCDK α (x * ns) ns = r := by
    have := (rm_cd_homog α hns hx one_pos).2.1
    rw [show ns * x = x * ns by ring, mul_one] at this
    rw [this]; simp only [rmCDK, Real.one_rpow, mul_one, hxa]; field_simp
  have hN : rmCDN α (x * ns) ns = (1 - α) * x ^ α := by
    have := (rm_cd_homog α hns hx one_pos).2.2
    rw [show ns * x = x * ns by ring, mul_one] at this
    rw [this]; simp [rmCDN]
  have hY : rmCD α (x * ns) ns = x ^ α * ns := by
    have := (rm_cd_homog α hns hx one_pos).1
    rw [show ns * x = x * ns by ring, mul_one] at this
    rw [this]; simp [rmCD]; ring
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Real.rpow_one, hK, r]
    field_simp
    ring
  · simp only [hN]
    have h1 : 1 - ns ≠ 0 := by linarith
    have hnum : θ * χ * ns = (1 - α) * x ^ α * (1 - ns) := by
      simp only [ns]; field_simp; ring
    field_simp
    linear_combination hnum
  · simp only [hY, χ]; ring
  · ring

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dynamics of the detrended Ramsey model: phase diagram and saddle path

Miao, §14.1.1 (with the tools of §1.5–1.6). The text of §14.1 states the detrended equilibrium
system and leaves its dynamics to Chapter 1 (Example 1.6.1 treats `g_a = gₙ = 1`). Here the
detrended system with inelastic labour (`n ≡ 1`, `f(k) = F(k, 1)`) is
`g_a^σu'(c̃_t) = βu'(c̃_{t+1})(f'(k̃_{t+1}) + 1 − δ)`,
`gₙg_ak̃_{t+1} = f(k̃_t) + (1 − δ)k̃_t − c̃_t`. Write `b = β/g_a^σ`, `γ = gₙg_a`, `A = −u''/u'`.

* **Phase diagram.** Consumption rises iff next period's capital is below the steady state:
  `c̃_{t+1} > c̃_t ⟺ k̃_{t+1} < k̃*` (`rm_phase_c`); capital rises iff consumption is below the
  `Δk̃ = 0` locus: `k̃_{t+1} > k̃_t ⟺ c̃_t < f(k̃_t) − (γ − 1 + δ)k̃_t` (`rm_phase_k`).
* **Linearisation.** The partial derivatives of the two residuals at the steady state
  (`rm_lin_taylor`); the linearised equations are equivalent to
  `(dk_{t+1}, dc_{t+1}) = M(dk_t, dc_t)`,
  `M = [[1/(bγ), −1/γ], [f''/(Aγ), 1 − bf''/(Aγ)]]` (`rm_lin_reduced`).
* **Eigenvalues.** `det M = 1/(bγ)`, `tr M = 1 + 1/(bγ) − bf''/(Aγ)` (`rm_lin_trace_det`);
  the characteristic polynomial is negative at `1` and the roots satisfy `0 < λ₁ < 1 < λ₂`
  (`rm_lin_roots`): the steady state is a saddle.
* **Saddle path.** For every `dk₀` there is exactly one bounded solution of the linearised
  system; it starts on the saddle line `dc₀ = κdk₀` with slope `κ > 0`, converges monotonically
  to the steady state, and every other solution is unbounded (`rm_lin_saddle`,
  `rm_lin_saddle_monotone`).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- **Phase diagram, `Δc̃ = 0` locus** (Miao, §14.1.1 with §1.5): if `u'` and `f'` are strictly
decreasing, `u'(c̃_{t+1}) > 0`, `β(f'(k̃*) + 1 − δ) = g_a^σ > 0`, and the Euler equation holds, then
consumption rises from `t` to `t + 1` iff `k̃_{t+1} < k̃*`. -/
theorem rm_phase_c {up fp : ℝ → ℝ} {β gs δ c0 c1 k1 kstar : ℝ}
    (hup : StrictAntiOn up (Set.Ioi 0)) (hfp : StrictAntiOn fp (Set.Ioi 0))
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hk1 : 0 < k1) (hks : 0 < kstar) (hβ : 0 < β)
    (hup0 : 0 < up c1) (hgs : 0 < gs) (hss : β * (fp kstar + 1 - δ) = gs)
    (heul : gs * up c0 = β * up c1 * (fp k1 + 1 - δ)) : c0 < c1 ↔ k1 < kstar := by
  have key : c0 < c1 ↔ up c1 < up c0 :=
    ⟨fun h => hup hc0 hc1 h, fun h => by
      by_contra hn
      rcases (not_lt.1 hn).eq_or_lt with he | he
      · rw [he] at h; exact lt_irrefl _ h
      · exact lt_asymm h (hup hc1 hc0 he)⟩
  have key2 : k1 < kstar ↔ fp kstar < fp k1 :=
    ⟨fun h => hfp hk1 hks h, fun h => by
      by_contra hn
      rcases (not_lt.1 hn).eq_or_lt with he | he
      · rw [he] at h; exact lt_irrefl _ h
      · exact lt_asymm h (hfp hks hk1 he)⟩
  rw [key, key2]
  -- `gs·u'(c₀) = βu'(c₁)(f'(k₁) + 1 − δ)` and `gs = β(f'(k*) + 1 − δ)`
  rw [← hss] at heul
  have hpos : 0 < β * (fp kstar + 1 - δ) := hss ▸ hgs
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have h1 : β * up c1 * (fp k1 + 1 - δ) ≤ β * up c1 * (fp kstar + 1 - δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_pos hβ hup0).le
    have : (β * (fp kstar + 1 - δ)) * up c0 ≤ (β * (fp kstar + 1 - δ)) * up c1 := by
      linarith
    have := le_of_mul_le_mul_left this hpos
    linarith
  · intro h
    by_contra hn
    push Not at hn
    have h1 : β * up c1 * (fp kstar + 1 - δ) < β * up c1 * (fp k1 + 1 - δ) :=
      mul_lt_mul_of_pos_left (by linarith) (mul_pos hβ hup0)
    have : (β * (fp kstar + 1 - δ)) * up c0 ≤ (β * (fp kstar + 1 - δ)) * up c1 :=
      mul_le_mul_of_nonneg_left hn hpos.le
    linarith

/-- **Phase diagram, `Δk̃ = 0` locus** (Miao, §14.1.1 with §1.5): with
`γk̃_{t+1} = f(k̃_t) + (1 − δ)k̃_t − c̃_t` and `γ > 0`, capital rises iff
`c̃_t < f(k̃_t) − (γ − 1 + δ)k̃_t`. -/
theorem rm_phase_k {γ δ k0 k1 c0 fk0 : ℝ} (hγ : 0 < γ)
    (hres : γ * k1 = fk0 + (1 - δ) * k0 - c0) : k0 < k1 ↔ c0 < fk0 - (γ - 1 + δ) * k0 := by
  constructor
  · intro h; nlinarith
  · intro h
    have : γ * k0 < γ * k1 := by linarith
    exact lt_of_mul_lt_mul_left this hγ.le

/-- **Linearisation** (Miao, §14.1.1 with Example 1.6.1): the partial derivatives at the steady
state `(k̄, c̄)` of the Euler residual `g_a^σu'(c_t) − βu'(c_{t+1})(f'(k_{t+1}) + 1 − δ)` in
`c_t, c_{t+1}, k_{t+1}` and of the resource residual `γk_{t+1} − f(k_t) − (1 − δ)k_t + c_t` in
`k_{t+1}, k_t, c_t`. -/
theorem rm_lin_taylor {f fp up : ℝ → ℝ} {β gs γ δ kb cb upp fpp : ℝ}
    (hf : HasDerivAt f (fp kb) kb) (hfp : HasDerivAt fp fpp kb) (hup : HasDerivAt up upp cb) :
    HasDerivAt (fun c => gs * up c - β * up cb * (fp kb + 1 - δ)) (gs * upp) cb ∧
      HasDerivAt (fun c' => gs * up cb - β * up c' * (fp kb + 1 - δ))
        (-(β * upp * (fp kb + 1 - δ))) cb ∧
      HasDerivAt (fun k' => gs * up cb - β * up cb * (fp k' + 1 - δ)) (-(β * up cb * fpp)) kb ∧
      HasDerivAt (fun k' => γ * k' - f kb - (1 - δ) * kb + cb) γ kb ∧
      HasDerivAt (fun k => γ * kb - f k - (1 - δ) * k + cb) (-(fp kb) - (1 - δ)) kb ∧
      HasDerivAt (fun c => γ * kb - f kb - (1 - δ) * kb + c) 1 cb := by
  refine ⟨(hup.const_mul gs).sub_const _, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((hup.const_mul β).mul_const (fp kb + 1 - δ)).const_sub (gs * up cb)
    convert this using 1
  · have := ((hfp.add_const (1 - δ)).const_mul (β * up cb)).const_sub (gs * up cb)
    convert this using 1
    ext k; ring
  · have := ((((hasDerivAt_id kb).const_mul γ).sub_const (f kb)).sub_const
      ((1 - δ) * kb)).add_const cb
    simpa using this
  · have := (((hf.const_sub (γ * kb)).sub ((hasDerivAt_id kb).const_mul (1 - δ))).add_const cb)
    exact this.congr_deriv (by ring)
  · simpa using (hasDerivAt_id cb).const_add (γ * kb - f kb - (1 - δ) * kb)

/-- **The linearised system** (Miao, §14.1.1): at a steady state `b(f' + 1 − δ) = 1` with
`u' > 0`, `u'' ≠ 0`, `b, γ ≠ 0`, the linearised Euler and resource equations
`u''dc_t = bu''(f' + 1 − δ)dc_{t+1} + bu'f''dk_{t+1}`,
`γdk_{t+1} = (f' + 1 − δ)dk_t − dc_t` are equivalent to `(dk_{t+1}, dc_{t+1}) = M(dk_t, dc_t)`. -/
theorem rm_lin_reduced {b γ δ up upp fp fpp : ℝ} (hb : b ≠ 0) (hγ : γ ≠ 0) (hup : 0 < up)
    (hupp : upp ≠ 0) (hss : b * (fp + 1 - δ) = 1) (dk dc : ℕ → ℝ) (t : ℕ) :
    (upp * dc t = b * upp * (fp + 1 - δ) * dc (t + 1) + b * up * fpp * dk (t + 1) ∧
        γ * dk (t + 1) = (fp + 1 - δ) * dk t - dc t) ↔
      (dk (t + 1) = 1 / (b * γ) * dk t + -1 / γ * dc t ∧
        dc (t + 1) = fpp / (-upp / up * γ) * dk t +
          (1 - b * fpp / (-upp / up * γ)) * dc t) := by
  have hfp : fp + 1 - δ = 1 / b := by field_simp; linarith
  have h1 : b * upp * (fp + 1 - δ) = upp := by rw [mul_comm b, mul_assoc, hss, mul_one]
  rw [h1]
  have hup' : up ≠ 0 := hup.ne'
  constructor
  · rintro ⟨e1, e2⟩
    have eK : dk (t + 1) = 1 / (b * γ) * dk t + -1 / γ * dc t := by
      rw [hfp] at e2; field_simp; field_simp at e2; linarith
    refine ⟨eK, ?_⟩
    rw [eK] at e1
    field_simp
    field_simp at e1
    linear_combination (-1) * e1
  · rintro ⟨e1, e2⟩
    refine ⟨?_, ?_⟩
    · rw [e2, e1]
      field_simp
      ring
    · rw [e1, hfp]; field_simp; ring

/-- **Trace and determinant** (Miao, §14.1.1): `det M = 1/(bγ)` and
`tr M = 1 + 1/(bγ) − bf''/(Aγ)`. -/
theorem rm_lin_trace_det {b γ fpp A : ℝ} (hb : b ≠ 0) (hγ : γ ≠ 0) (hA : A ≠ 0) :
    1 / (b * γ) + (1 - b * fpp / (A * γ)) = 1 + 1 / (b * γ) - b * fpp / (A * γ) ∧
      1 / (b * γ) * (1 - b * fpp / (A * γ)) - (-1 / γ) * (fpp / (A * γ)) = 1 / (b * γ) := by
  refine ⟨by ring, by field_simp; ring⟩

/-- **Eigenvalues** (Miao, §14.1.1): for `b, γ, A > 0` and `f'' < 0`, the characteristic
polynomial of `M` is negative at `1`, and its roots satisfy `0 < λ₁ < 1 < λ₂`. -/
theorem rm_lin_roots {b γ fpp A : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hf : fpp < 0) (hA : 0 < A) :
    cp22 (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) 1 < 0 ∧
      0 < lamLo (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) ∧
      lamLo (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) < 1 ∧
      1 < lamHi (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) := by
  have hcp : ∀ μ, cp22 (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) μ =
      μ ^ 2 - (1 + 1 / (b * γ) - b * fpp / (A * γ)) * μ + 1 / (b * γ) := fun μ => by
    simp only [cp22]; field_simp; ring
  have h2 : b * fpp / (A * γ) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hb hf) (mul_pos hA hγ)
  have h1 : cp22 (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ)) 1 < 0 := by
    rw [hcp]; linarith
  obtain ⟨hlo, hhi⟩ := roots22_lt h1
  refine ⟨h1, ?_, hlo, hhi⟩
  have h0 := cp22_factor h1 0
  rw [hcp] at h0
  have hd : 0 < 1 / (b * γ) := by positivity
  nlinarith

/-- **The saddle path** (Miao, §14.1.1): for every `dk₀` the linearised system has a solution
starting at `dk₀` converging to the steady state, every bounded solution starts on the saddle
line `dc₀ = κdk₀`, the slope `κ` is positive (consumption is increasing in capital along the
saddle path), and every solution off the line is unbounded. -/
theorem rm_lin_saddle {b γ fpp A : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hf : fpp < 0) (hA : 0 < A)
    (dk0 : ℝ) :
    let m11 := 1 / (b * γ)
    let m12 := -1 / γ
    let m21 := fpp / (A * γ)
    let m22 := 1 - b * fpp / (A * γ)
    (∃ dk dc : ℕ → ℝ, IsSol22 m11 m12 m21 m22 dk dc ∧ dk 0 = dk0 ∧
      Tendsto dk atTop (𝓝 0) ∧ Tendsto dc atTop (𝓝 0)) ∧
    (∀ dk dc : ℕ → ℝ, IsSol22 m11 m12 m21 m22 dk dc → BddSeq dk → BddSeq dc →
      dc 0 = kSaddle m11 m12 m21 m22 * dk 0) ∧
    0 < kSaddle m11 m12 m21 m22 ∧
    (∀ dk dc : ℕ → ℝ, IsSol22 m11 m12 m21 m22 dk dc →
      dc 0 ≠ kSaddle m11 m12 m21 m22 * dk 0 → ¬ (BddSeq dk ∧ BddSeq dc)) := by
  intro m11 m12 m21 m22
  obtain ⟨h1, hlo0, -, -⟩ := rm_lin_roots hb hγ hf hA
  have hm : 0 < m12 * m21 := by
    have h21 : fpp / (A * γ) < 0 := div_neg_of_neg_of_pos hf (mul_pos hA hγ)
    have h12 : -1 / γ < 0 := div_neg_of_neg_of_pos (by norm_num) hγ
    exact mul_pos_of_neg_of_neg h12 h21
  have hc : 0 < cp22 m11 m12 m21 m22 (-1) := by
    rw [cp22_factor h1 (-1)]
    have := (roots22_lt h1).2
    nlinarith
  refine ⟨(saddle22_iff h1 hm).2 hc dk0, fun dk dc h hK hC => ?_, ?_,
    fun dk dc h hoff => saddle22_unbounded h1 hm h hoff⟩
  · exact (sHi_zero_iff h1 hm dk dc 0).1 (sHi_zero_of_bdd h1 h hK hC)
  · have hlt := lamLo_lt_m11 h1 hm
    have hm12 : m12 < 0 := div_neg_of_neg_of_pos (by norm_num) hγ
    simp only [kSaddle]
    exact div_pos_of_neg_of_neg (by linarith) hm12

/-- **Monotone convergence along the saddle path** (Miao, §14.1.1): since the stable root lies in
`(0, 1)`, capital on the saddle path `dk_t = λ₁ᵗdk₀` moves monotonically towards the steady
state: `|dk_{t+1}| < |dk_t|` and `dk_t` keeps the sign of `dk₀`, for `dk₀ ≠ 0`. -/
theorem rm_lin_saddle_monotone {b γ fpp A : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hf : fpp < 0)
    (hA : 0 < A) {dk0 : ℝ} (hdk : dk0 ≠ 0) (t : ℕ) :
    let l := lamLo (1 / (b * γ)) (-1 / γ) (fpp / (A * γ)) (1 - b * fpp / (A * γ))
    |l ^ (t + 1) * dk0| < |l ^ t * dk0| ∧ 0 < l ^ t * dk0 * dk0 := by
  intro l
  obtain ⟨-, hl0', hl1', -⟩ := rm_lin_roots hb hγ hf hA
  have hl0 : 0 < l := hl0'
  have hl1 : l < 1 := hl1'
  have hlt : 0 < l ^ t := pow_pos hl0 t
  refine ⟨?_, ?_⟩
  · rw [pow_succ, abs_mul, abs_mul, abs_mul, abs_of_pos hlt, abs_of_pos hl0]
    have : 0 < |dk0| := abs_pos.2 hdk
    nlinarith [mul_lt_mul_of_pos_left hl1 (mul_pos hlt this)]
  · have : 0 < dk0 * dk0 := mul_self_pos.2 hdk
    nlinarith

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Incorporating fiscal policy

Miao, §14.1.2, pp. 467–471. No long-run growth; firms own capital; consumption, distribution,
labour income and corporate income taxes `τˢ, τᵈ, τⁿ, τᶜ`, lump-sum taxes `T`, one-period
government bonds `B` with gross return `R`.

* The household's first-order conditions (p. 468) give the consumption Euler equation
  `u_C(t)/(1 + τˢ_t) = βR_tu_C(t + 1)/(1 + τˢ_{t+1})` and the labour condition
  `−u_N/u_C = (1 − τⁿ)w/(1 + τˢ)` (`rm_fiscal_euler`, `rm_fiscal_labour`); the share condition is
  the firm's value recursion `V_t = (1 − τᵈ_t)D_t + βΛ_{t+1}/Λ_t V_{t+1}`
  (`rm_fiscal_value_recursion`).
* The firm's first-order condition for capital (14.20), with `Q = 1 − τᵈ` (14.19), from the
  variation of `K_{t+1}` (`eq_14_20`).
* **Proposition 14.1.1**: the one-step identity
  `Q_tK_{t+1} = βΛ_{t+1}/Λ_t[(1 − τᵈ_{t+1})D_{t+1} + Q_{t+1}K_{t+2}]` (`rm_prop_14_1_1_step`),
  the forward solution `Q_tK_{t+1} = ∑_{j≥1} βʲΛ_{t+j}/Λ_t (1 − τᵈ_{t+j})D_{t+j}` under the
  transversality condition (`rm_prop_14_1_1_sum`), the equality of the ex-dividend value with
  `Q_tK_{t+1}` (`rm_prop_14_1_1_exdiv`), and the proposition
  `V_t − (1 − τᵈ_t)D_t = (1 − τᵈ_t)K_{t+1}` (`proposition_14_1_1`).
* **(14.21)**: with constant `τᵈ ≠ 1` and `τᶜ`, (14.19)–(14.20) are equivalent to
  `1 = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]` (`eq_14_21`).
* **Permanent changes in `τᵈ`** (p. 470) with lump-sum taxes balancing the budget do not affect
  the allocation: any equilibrium for `τᵈ` gives an equilibrium for any other constant `τᵈ' ≠ 1`
  with the same allocation, the same `Λ, w, R, D, B`, price of capital `Q' = 1 − τᵈ'`, equity
  value `V' = (1 − τᵈ')(D + K_{+1})` and lump-sum taxes `T' = T + (τᵈ − τᵈ')D`
  (`rm_distribution_tax_neutral`).
* **Temporary changes in `τᵈ`**: with a time-varying distribution tax, (14.19)–(14.20) become
  `(1 − τᵈ_t)/(1 − τᵈ_{t+1}) = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`
  (`rm_temporary_distribution_tax`), which agrees with (14.21) only when `τᵈ_t = τᵈ_{t+1}`
  (`rm_temporary_distribution_tax_distorts`): an anticipated change distorts investment.
* **Walras' law and Ricardian equivalence**: with the government budget constraint, the resource
  constraint and `ψ ≡ 1`, the household's budget constraint holds (`rm_walras`); so the
  equilibrium conditions involve `(B, T)` only through the government budget constraint, and any
  other debt and lump-sum tax path satisfying it supports the same equilibrium
  (`rm_ricardian`).

**Corrections.**
1. The proof of Proposition 14.1.1 drops the factor `1 − τᵈ_{t+1}` on `D_{t+1}`: the printed
   step `Q_tK_{t+1} = βΛ_{t+1}/Λ_t(D_{t+1} + Q_{t+1}K_{t+2})` contradicts the true one unless
   `τᵈ_{t+1}D_{t+1} = 0` (`rm_prop_14_1_1_misprint`), and the printed sum
   `∑ βʲΛ_{t+j}/Λ_t D_{t+j}` must be `∑ βʲΛ_{t+j}/Λ_t (1 − τᵈ_{t+j})D_{t+j}`. The
   proposition itself is correct. (The proof also writes `w_tN_{t+1}` for `w_{t+1}N_{t+1}`.)
2. The government budget constraint prints corporate revenue `τᶜ(F − wN)`, but the dividend
   definition gives the firm a depreciation allowance, so corporate revenue is
   `τᶜ(F − wN − δK)`. With the printed constraint, Walras' law fails: the household budget,
   the printed government budget and the resource constraint together force `τᶜδK = 0`
   (`rm_gov_budget_misprint`). `RMFiscalEq` uses the corrected constraint.
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- The tax rates of §14.1.2: consumption `τs`, distribution `τd`, labour `τn`, corporate `τc`. -/
structure RMTaxes where
  τs : ℕ → ℝ
  τd : ℕ → ℝ
  τn : ℕ → ℝ
  τc : ℕ → ℝ

/-- Quantities and prices of §14.1.2. `lam` is the household's multiplier `Λ`. -/
structure RMFiscalPath where
  C : ℕ → ℝ
  N : ℕ → ℝ
  K : ℕ → ℝ
  I : ℕ → ℝ
  G : ℕ → ℝ
  w : ℕ → ℝ
  R : ℕ → ℝ
  lam : ℕ → ℝ
  V : ℕ → ℝ
  D : ℕ → ℝ
  Q : ℕ → ℝ
  B : ℕ → ℝ
  T : ℕ → ℝ

/-- The government budget constraint (Miao, p. 469, corporate revenue corrected to
`τᶜ(F − wN − δK)`). -/
def rmGovBudget (F : ℝ → ℝ → ℝ) (δ : ℝ) (τ : RMTaxes) (p : RMFiscalPath) (t : ℕ) : Prop :=
  p.G t + p.B t = p.B (t + 1) / p.R t + τ.τs t * p.C t + τ.τd t * p.D t +
    τ.τc t * (F (p.K t) (p.N t) - p.w t * p.N t - δ * p.K t) + τ.τn t * p.w t * p.N t + p.T t

/-- The equilibrium system of §14.1.2 (Miao, pp. 468–469): the household's first-order
conditions, the dividend definition, (14.18), the firm's labour condition `w = F_N`, (14.19),
(14.20), the government budget constraint (corrected) and the resource constraint. -/
def RMFiscalEq (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τ : RMTaxes) (p : RMFiscalPath) :
    Prop :=
  ∀ t, uC (p.C t) (p.N t) = (1 + τ.τs t) * p.lam t ∧
    -uN (p.C t) (p.N t) = (1 - τ.τn t) * p.lam t * p.w t ∧
    p.lam t * (p.V t - (1 - τ.τd t) * p.D t) = β * p.lam (t + 1) * p.V (t + 1) ∧
    p.lam t = β * p.lam (t + 1) * p.R t ∧
    p.D t = (1 - τ.τc t) * (F (p.K t) (p.N t) - p.w t * p.N t) - p.I t +
      τ.τc t * δ * p.K t ∧
    p.K (t + 1) = (1 - δ) * p.K t + p.I t ∧
    p.w t = FN (p.K t) (p.N t) ∧
    p.Q t = 1 - τ.τd t ∧
    p.Q t = β * p.lam (t + 1) / p.lam t * ((1 - δ) * p.Q (t + 1) +
      (1 - τ.τd (t + 1)) * τ.τc (t + 1) * δ +
      (1 - τ.τd (t + 1)) * (1 - τ.τc (t + 1)) * FK (p.K (t + 1)) (p.N (t + 1))) ∧
    rmGovBudget F δ τ p t ∧
    p.C t + p.I t + p.G t = F (p.K t) (p.N t)

/-! ### Household and firm first-order conditions -/

/-- Miao, p. 468: the `C` and `B` conditions give
`u_C(t)/(1 + τˢ_t) = βR_tu_C(t + 1)/(1 + τˢ_{t+1})`. -/
theorem rm_fiscal_euler {uc0 uc1 τs0 τs1 l0 l1 β R : ℝ} (h0 : 1 + τs0 ≠ 0) (h1 : 1 + τs1 ≠ 0)
    (hc0 : uc0 = (1 + τs0) * l0) (hc1 : uc1 = (1 + τs1) * l1) (hb : l0 = β * l1 * R) :
    uc0 / (1 + τs0) = β * R * (uc1 / (1 + τs1)) := by
  rw [hc0, hc1]; field_simp; rw [hb]; ring

/-- Miao, p. 468: the `C` and `N` conditions give `−u_N/u_C = (1 − τⁿ)w/(1 + τˢ)`. -/
theorem rm_fiscal_labour {uc un τs τn l w : ℝ} (hs : 1 + τs ≠ 0) (hl : l ≠ 0)
    (hc : uc = (1 + τs) * l) (hn : -un = (1 - τn) * l * w) :
    -un / uc = (1 - τn) * w / (1 + τs) := by
  rw [hn, hc]; field_simp

/-- Miao, p. 468: the share condition is the firm's value recursion
`V_t = (1 − τᵈ_t)D_t + βΛ_{t+1}/Λ_t V_{t+1}` (the firm's objective). -/
theorem rm_fiscal_value_recursion {l0 l1 V0 V1 D0 τd0 β : ℝ} (hl : l0 ≠ 0)
    (h : l0 * (V0 - (1 - τd0) * D0) = β * l1 * V1) :
    V0 = (1 - τd0) * D0 + β * l1 / l0 * V1 := by
  field_simp; linarith

/-- **(14.19)–(14.20)** (Miao, p. 469): if raising `K_{t+1}` to `x` (cutting date-`t` dividends
one-for-one and raising date-`t+1` dividends by `(1 − τᶜ)F(x, N) + (1 − δ + τᶜδ)x`) leaves the
after-tax value `−(1 − τᵈ_t)x + m(1 − τᵈ_{t+1})[(1 − τᶜ)F(x, N) + (1 − δ + τᶜδ)x]` at a local
maximum at `K_{t+1}`, with `m = βΛ_{t+1}/Λ_t`, then (14.20) holds with `Q = 1 − τᵈ`. -/
theorem eq_14_20 {F FK : ℝ → ℝ → ℝ} {m δ K1 N1 τd0 τd1 τc1 : ℝ}
    (hF : HasDerivAt (fun x => F x N1) (FK K1 N1) K1)
    (hmax : IsLocalMax (fun x => -(1 - τd0) * x +
      m * (1 - τd1) * ((1 - τc1) * F x N1 + (1 - δ + τc1 * δ) * x)) K1) :
    1 - τd0 = m * ((1 - δ) * (1 - τd1) + (1 - τd1) * τc1 * δ +
      (1 - τd1) * (1 - τc1) * FK K1 N1) := by
  have hd : HasDerivAt (fun x => -(1 - τd0) * x +
      m * (1 - τd1) * ((1 - τc1) * F x N1 + (1 - δ + τc1 * δ) * x))
      (-(1 - τd0) * 1 + m * (1 - τd1) * ((1 - τc1) * FK K1 N1 + (1 - δ + τc1 * δ) * 1)) K1 :=
    ((hasDerivAt_id K1).const_mul _).add
      (((hF.const_mul (1 - τc1)).add ((hasDerivAt_id K1).const_mul _)).const_mul _)
  have := hmax.hasDerivAt_eq_zero hd
  linear_combination -this

/-! ### Proposition 14.1.1 -/

/-- Miao, p. 469 (proof of Proposition 14.1.1, corrected): multiplying (14.20) by `K_{t+1}` and
using `F = F_KK + F_NN`, `w = F_N`, (14.18), (14.19) and the dividend definition,
`Q_tK_{t+1} = βΛ_{t+1}/Λ_t[(1 − τᵈ_{t+1})D_{t+1} + Q_{t+1}K_{t+2}]`. -/
theorem rm_prop_14_1_1_step {F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath}
    (t : ℕ)
    (h20 : p.Q t = β * p.lam (t + 1) / p.lam t * ((1 - δ) * p.Q (t + 1) +
      (1 - τ.τd (t + 1)) * τ.τc (t + 1) * δ +
      (1 - τ.τd (t + 1)) * (1 - τ.τc (t + 1)) * FK (p.K (t + 1)) (p.N (t + 1))))
    (h19 : p.Q (t + 1) = 1 - τ.τd (t + 1)) (hw : p.w (t + 1) = FN (p.K (t + 1)) (p.N (t + 1)))
    (hE : F (p.K (t + 1)) (p.N (t + 1)) = FK (p.K (t + 1)) (p.N (t + 1)) * p.K (t + 1) +
      FN (p.K (t + 1)) (p.N (t + 1)) * p.N (t + 1))
    (hacc : p.K (t + 1 + 1) = (1 - δ) * p.K (t + 1) + p.I (t + 1))
    (hD : p.D (t + 1) = (1 - τ.τc (t + 1)) * (F (p.K (t + 1)) (p.N (t + 1)) -
      p.w (t + 1) * p.N (t + 1)) - p.I (t + 1) + τ.τc (t + 1) * δ * p.K (t + 1)) :
    p.Q t * p.K (t + 1) = β * p.lam (t + 1) / p.lam t *
      ((1 - τ.τd (t + 1)) * p.D (t + 1) + p.Q (t + 1) * p.K (t + 2)) := by
  rw [show t + 2 = t + 1 + 1 by ring, hacc, hD, h20, h19, hw, hE]
  ring

/-- Correction to Miao, p. 469: the printed step `Q_tK_{t+1} = βΛ_{t+1}/Λ_t(D_{t+1} +
Q_{t+1}K_{t+2})` and the true one hold together only if `τᵈ_{t+1}D_{t+1} = 0`. -/
theorem rm_prop_14_1_1_misprint {m D1 Q1K2 τd1 QK : ℝ} (hm : m ≠ 0)
    (htrue : QK = m * ((1 - τd1) * D1 + Q1K2)) (hprinted : QK = m * (D1 + Q1K2)) :
    τd1 * D1 = 0 := by
  have : m * (τd1 * D1) = 0 := by linear_combination htrue - hprinted
  exact (mul_eq_zero.1 this).resolve_left hm

/-- Miao, p. 470 (Proposition 14.1.1, the forward solution, corrected): if the one-step identity
holds at every date and the transversality condition `lim β^TΛ_TQ_TK_{T+1} = 0` holds, then
`Q_tK_{t+1} = ∑_{j≥1} βʲΛ_{t+j}/Λ_t (1 − τᵈ_{t+j})D_{t+j}` (limit of partial sums). -/
theorem rm_prop_14_1_1_sum {β : ℝ} {lam Y D τd : ℕ → ℝ} (hβ : 0 < β) (hl : ∀ s, lam s ≠ 0)
    (hstep : ∀ s, Y s = β * lam (s + 1) / lam s * ((1 - τd (s + 1)) * D (s + 1) + Y (s + 1)))
    (htvc : Tendsto (fun s => β ^ s * lam s * Y s) atTop (𝓝 0)) (t : ℕ) :
    Tendsto (fun T => ∑ j ∈ Finset.range T,
      β ^ (j + 1) * lam (t + j + 1) / lam t * ((1 - τd (t + j + 1)) * D (t + j + 1))) atTop
      (𝓝 (Y t)) := by
  have hstep' : ∀ s, lam s * Y s =
      β * lam (s + 1) * ((1 - τd (s + 1)) * D (s + 1)) + β * lam (s + 1) * Y (s + 1) := by
    intro s; rw [hstep s]; field_simp [hl s]
  have hpart : ∀ T, lam t * Y t = ∑ j ∈ Finset.range T,
      β ^ (j + 1) * lam (t + j + 1) * ((1 - τd (t + j + 1)) * D (t + j + 1)) +
      β ^ T * lam (t + T) * Y (t + T) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, show t + (T + 1) = t + T + 1 by ring]
      have := hstep' (t + T)
      linear_combination β ^ T * this
  have hT : ∀ T, ∑ j ∈ Finset.range T,
      β ^ (j + 1) * lam (t + j + 1) / lam t * ((1 - τd (t + j + 1)) * D (t + j + 1)) =
      Y t - (β ^ t)⁻¹ * (β ^ (t + T) * lam (t + T) * Y (t + T)) / lam t := by
    intro T
    have h := hpart T
    have hsum : ∑ j ∈ Finset.range T,
        β ^ (j + 1) * lam (t + j + 1) / lam t * ((1 - τd (t + j + 1)) * D (t + j + 1)) =
        (∑ j ∈ Finset.range T,
          β ^ (j + 1) * lam (t + j + 1) * ((1 - τd (t + j + 1)) * D (t + j + 1))) / lam t := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hS : (∑ j ∈ Finset.range T,
        β ^ (j + 1) * lam (t + j + 1) * ((1 - τd (t + j + 1)) * D (t + j + 1))) =
        lam t * Y t - β ^ T * lam (t + T) * Y (t + T) := by linarith [h]
    rw [hsum, hS, pow_add]
    field_simp [hl t, (pow_pos hβ t).ne']
  simp only [hT]
  have h1 : Tendsto (fun T => β ^ (t + T) * lam (t + T) * Y (t + T)) atTop (𝓝 0) := by
    have := (tendsto_add_atTop_iff_nat t).2 htvc
    exact this.congr (fun T => by rw [add_comm T t])
  have := ((h1.const_mul (β ^ t)⁻¹).div_const (lam t)).const_sub (Y t)
  simpa using this

/-- Miao, p. 470 (Proposition 14.1.1, "`Q_tK_{t+1}` is the ex-dividend equity value"): if the
ex-dividend value `X_t = V_t − (1 − τᵈ_t)D_t` satisfies the share condition, `Y_t = Q_tK_{t+1}`
satisfies the one-step identity, and both `β^TΛ_TV_T` and `β^TΛ_TQ_TK_{T+1}` tend to zero, then
`V_t − (1 − τᵈ_t)D_t = Q_tK_{t+1}`. -/
theorem rm_prop_14_1_1_exdiv {β : ℝ} {lam V D Y τd : ℕ → ℝ} (hβ : 0 < β)
    (hl : ∀ s, lam s ≠ 0)
    (hψ : ∀ s, lam s * (V s - (1 - τd s) * D s) = β * lam (s + 1) * V (s + 1))
    (hstep : ∀ s, Y s = β * lam (s + 1) / lam s * ((1 - τd (s + 1)) * D (s + 1) + Y (s + 1)))
    (hnb : Tendsto (fun s => β ^ s * lam s * V s) atTop (𝓝 0))
    (htvc : Tendsto (fun s => β ^ s * lam s * Y s) atTop (𝓝 0)) (t : ℕ) :
    V t - (1 - τd t) * D t = Y t := by
  set e : ℕ → ℝ := fun s => β ^ s * lam s * (V s - (1 - τd s) * D s - Y s) with he
  have hsucc : ∀ s, e (s + 1) = e s := by
    intro s
    have h1 := hψ s
    have h2 : lam s * Y s = β * lam (s + 1) * ((1 - τd (s + 1)) * D (s + 1) + Y (s + 1)) := by
      rw [hstep s]; field_simp [hl s]
    simp only [he, pow_succ]
    linear_combination (-(β ^ s)) * h1 + β ^ s * h2
  have hconst : ∀ s, e s = e 0 := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [hsucc, ih]
  have hlim : Tendsto e atTop (𝓝 0) := by
    have hX : Tendsto (fun s => β ^ s * lam s * (V s - (1 - τd s) * D s)) atTop (𝓝 0) := by
      have := (tendsto_add_atTop_iff_nat 1).2 hnb
      refine this.congr (fun s => ?_)
      rw [mul_assoc (β ^ s), hψ s, pow_succ]; ring
    have := hX.sub htvc
    simp only [sub_zero] at this
    exact this.congr (fun s => by simp only [he]; ring)
  have h0 : e 0 = 0 := by
    have : Tendsto e atTop (𝓝 (e 0)) := by
      rw [show e = fun _ => e 0 from funext hconst]; exact tendsto_const_nhds
    exact tendsto_nhds_unique this hlim
  have := hconst t
  rw [h0] at this
  simp only [he] at this
  have hne : β ^ t * lam t ≠ 0 := mul_ne_zero (pow_pos hβ t).ne' (hl t)
  have := (mul_eq_zero.1 this).resolve_left hne
  linarith

/-- **Proposition 14.1.1** (Miao, p. 469, McGrattan and Prescott 2005): in an equilibrium of
§14.1.2 in which `F = F_KK + F_NN` along the path, `Λ_t ≠ 0`, and the transversality conditions
`lim β^TΛ_TQ_TK_{T+1} = 0` and `lim β^TΛ_TV_T = 0` hold, the ex-dividend equity value is
`V_t − (1 − τᵈ_t)D_t = (1 − τᵈ_t)K_{t+1}`. -/
theorem proposition_14_1_1 {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τ : RMTaxes}
    {p : RMFiscalPath} (hβ : 0 < β) (heq : RMFiscalEq uC uN F FK FN β δ τ p)
    (hl : ∀ s, p.lam s ≠ 0)
    (hE : ∀ s, F (p.K s) (p.N s) = FK (p.K s) (p.N s) * p.K s + FN (p.K s) (p.N s) * p.N s)
    (hnb : Tendsto (fun s => β ^ s * p.lam s * p.V s) atTop (𝓝 0))
    (htvc : Tendsto (fun s => β ^ s * p.lam s * (p.Q s * p.K (s + 1))) atTop (𝓝 0)) (t : ℕ) :
    p.V t - (1 - τ.τd t) * p.D t = (1 - τ.τd t) * p.K (t + 1) := by
  have hstep : ∀ s, p.Q s * p.K (s + 1) = β * p.lam (s + 1) / p.lam s *
      ((1 - τ.τd (s + 1)) * p.D (s + 1) + p.Q (s + 1) * p.K (s + 1 + 1)) := fun s =>
    rm_prop_14_1_1_step s (heq s).2.2.2.2.2.2.2.2.1 (heq (s + 1)).2.2.2.2.2.2.2.1
      (heq (s + 1)).2.2.2.2.2.2.1 (hE (s + 1)) (heq (s + 1)).2.2.2.2.2.1
      (heq (s + 1)).2.2.2.2.1
  have := rm_prop_14_1_1_exdiv (Y := fun s => p.Q s * p.K (s + 1)) hβ hl
    (fun s => (heq s).2.2.1) hstep hnb htvc t
  rw [this, (heq t).2.2.2.2.2.2.2.1]

/-! ### Distribution taxes -/

/-- **(14.21)** (Miao, p. 470): with constant `τᵈ ≠ 1` and `τᶜ`, (14.19) and (14.20) are
equivalent to `1 = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K(K_{t+1}, N_{t+1})]`. -/
theorem eq_14_21 {m δ τd τc FK1 : ℝ} (hτ : 1 - τd ≠ 0) :
    (1 - τd = m * ((1 - δ) * (1 - τd) + (1 - τd) * τc * δ + (1 - τd) * (1 - τc) * FK1)) ↔
      1 = m * ((1 - δ) + τc * δ + (1 - τc) * FK1) := by
  constructor
  · intro h
    have : (1 - τd) * 1 = (1 - τd) * (m * ((1 - δ) + τc * δ + (1 - τc) * FK1)) := by
      linear_combination h
    exact mul_left_cancel₀ hτ this
  · intro h; linear_combination (1 - τd) * h

/-- Miao, pp. 470–471 (temporary changes): with a time-varying distribution tax (14.19)–(14.20)
are equivalent to `(1 − τᵈ_t)/(1 − τᵈ_{t+1}) = βΛ_{t+1}/Λ_t[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`. -/
theorem rm_temporary_distribution_tax {m δ τd0 τd1 τc FK1 : ℝ} (hτ : 1 - τd1 ≠ 0) :
    (1 - τd0 = m * ((1 - δ) * (1 - τd1) + (1 - τd1) * τc * δ + (1 - τd1) * (1 - τc) * FK1)) ↔
      (1 - τd0) / (1 - τd1) = m * ((1 - δ) + τc * δ + (1 - τc) * FK1) := by
  rw [div_eq_iff hτ]
  constructor <;> intro h <;> linear_combination h

/-- Miao, pp. 470–471: a temporary (anticipated) change in the distribution tax distorts the
investment decision: the time-varying condition agrees with (14.21) only if `τᵈ_t = τᵈ_{t+1}`. -/
theorem rm_temporary_distribution_tax_distorts {m δ τd0 τd1 τc FK1 : ℝ} (hτ : 1 - τd1 ≠ 0)
    (htv : (1 - τd0) / (1 - τd1) = m * ((1 - δ) + τc * δ + (1 - τc) * FK1))
    (h21 : 1 = m * ((1 - δ) + τc * δ + (1 - τc) * FK1)) : τd0 = τd1 := by
  rw [← h21, div_eq_one_iff_eq hτ] at htv
  linarith

/-- **A permanent change in the distribution tax is neutral** (Miao, p. 470): take an
equilibrium with constant `τᵈ ≠ 1`, constant `τᶜ`, and lump-sum taxes balancing the budget.
For any constant `τᵈ' ≠ 1`, the same allocation with the same `Λ, w, R, D, B`, the price of
capital `Q' = 1 − τᵈ'`, equity value `V'_t = (1 − τᵈ')(D_t + K_{t+1})` and lump-sum taxes
`T'_t = T_t + (τᵈ − τᵈ')D_t` is an equilibrium for `τᵈ'`. (Requires `F = F_KK + F_NN`.) -/
theorem rm_distribution_tax_neutral {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ td td' tc : ℝ}
    {τs τn : ℕ → ℝ} {p : RMFiscalPath}
    (heq : RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td, τn, fun _ => tc⟩ p)
    (hτ : 1 - td ≠ 0) (hl : ∀ s, p.lam s ≠ 0)
    (hE : ∀ s, F (p.K s) (p.N s) = FK (p.K s) (p.N s) * p.K s + FN (p.K s) (p.N s) * p.N s) :
    RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td', τn, fun _ => tc⟩
      { p with V := fun s => (1 - td') * (p.D s + p.K (s + 1)), Q := fun _ => 1 - td',
               T := fun s => p.T s + (td - td') * p.D s } := by
  -- the τᵈ-free capital condition `Λ_tK_{t+1} = βΛ_{t+1}(D_{t+1} + K_{t+2})`
  have hkey : ∀ s, p.lam s * p.K (s + 1) =
      β * p.lam (s + 1) * (p.D (s + 1) + p.K (s + 1 + 1)) := by
    intro s
    have h := rm_prop_14_1_1_step (F := F) (FK := FK) (FN := FN) (β := β) (δ := δ)
      (τ := ⟨τs, fun _ => td, τn, fun _ => tc⟩) (p := p) s (heq s).2.2.2.2.2.2.2.2.1
      (heq (s + 1)).2.2.2.2.2.2.2.1 (heq (s + 1)).2.2.2.2.2.2.1 (hE (s + 1))
      (heq (s + 1)).2.2.2.2.2.1 (heq (s + 1)).2.2.2.2.1
    rw [(heq s).2.2.2.2.2.2.2.1, (heq (s + 1)).2.2.2.2.2.2.2.1] at h
    simp only at h
    rw [show s + 2 = s + 1 + 1 by ring] at h
    field_simp [hl s] at h
    linear_combination h
  intro t
  obtain ⟨h1, h2, -, h4, h5, h6, h7, -, h9, h10, h11⟩ := heq t
  simp only at h1 h2 h4 h5 h6 h7 h9 h10 h11 ⊢
  refine ⟨h1, h2, ?_, h4, h5, h6, h7, trivial, ?_, ?_, h11⟩
  · have := hkey t
    linear_combination (1 - td') * this
  · -- (14.20) for `τᵈ'` from (14.20) for `τᵈ`
    have h9' := h9
    rw [(heq t).2.2.2.2.2.2.2.1, (heq (t + 1)).2.2.2.2.2.2.2.1] at h9'
    simp only at h9'
    have h21 := (eq_14_21 hτ).1 h9'
    linear_combination (1 - td') * h21
  · simp only [rmGovBudget] at h10 ⊢
    linear_combination h10

/-! ### Government budget, Walras' law and Ricardian equivalence -/

/-- **Walras' law** (Miao, pp. 468–469): with the (corrected) government budget constraint, the
dividend definition and the resource constraint, the household's budget constraint with
`ψ_t = ψ_{t+1} = 1` holds:
`(1 + τˢ)C + (V − (1 − τᵈ)D) + B_{t+1}/R = V + (1 − τⁿ)wN + B − T`. -/
theorem rm_walras {F : ℝ → ℝ → ℝ} {δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath} (t : ℕ)
    (hgov : rmGovBudget F δ τ p t)
    (hD : p.D t = (1 - τ.τc t) * (F (p.K t) (p.N t) - p.w t * p.N t) - p.I t +
      τ.τc t * δ * p.K t)
    (hres : p.C t + p.I t + p.G t = F (p.K t) (p.N t)) :
    (1 + τ.τs t) * p.C t + 1 * (p.V t - (1 - τ.τd t) * p.D t) + p.B (t + 1) / p.R t =
      1 * p.V t + (1 - τ.τn t) * p.w t * p.N t + p.B t - p.T t := by
  simp only [rmGovBudget] at hgov
  linear_combination -hgov + hres - hD

/-- Correction to Miao, p. 469: with the printed government budget constraint (corporate revenue
`τᶜ(F − wN)`), the household's budget constraint, the dividend definition and the resource
constraint together force `τᶜ_tδK_t = 0`. -/
theorem rm_gov_budget_misprint {F : ℝ → ℝ → ℝ} {δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath}
    (t : ℕ)
    (hgov : p.G t + p.B t = p.B (t + 1) / p.R t + τ.τs t * p.C t + τ.τd t * p.D t +
      τ.τc t * (F (p.K t) (p.N t) - p.w t * p.N t) + τ.τn t * p.w t * p.N t + p.T t)
    (hhh : (1 + τ.τs t) * p.C t + (p.V t - (1 - τ.τd t) * p.D t) + p.B (t + 1) / p.R t =
      p.V t + (1 - τ.τn t) * p.w t * p.N t + p.B t - p.T t)
    (hD : p.D t = (1 - τ.τc t) * (F (p.K t) (p.N t) - p.w t * p.N t) - p.I t +
      τ.τc t * δ * p.K t)
    (hres : p.C t + p.I t + p.G t = F (p.K t) (p.N t)) : τ.τc t * δ * p.K t = 0 := by
  linear_combination -hgov - hhh - hD + hres

/-- **Ricardian equivalence** (Miao, §14.1.2): the equilibrium conditions involve the debt and
lump-sum tax paths only through the government budget constraint. Hence if `p` is an
equilibrium and `(B', T')` is any other path satisfying the government budget constraint with
the same allocation, prices and distortionary taxes, then `p` with `(B', T')` is an equilibrium,
and the household's budget constraint holds along it. -/
theorem rm_ricardian {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τ : RMTaxes} {p : RMFiscalPath}
    (heq : RMFiscalEq uC uN F FK FN β δ τ p) {B' T' : ℕ → ℝ}
    (hgov : ∀ t, rmGovBudget F δ τ { p with B := B', T := T' } t) :
    RMFiscalEq uC uN F FK FN β δ τ { p with B := B', T := T' } ∧
      ∀ t, (1 + τ.τs t) * p.C t + 1 * (p.V t - (1 - τ.τd t) * p.D t) + B' (t + 1) / p.R t =
        1 * p.V t + (1 - τ.τn t) * p.w t * p.N t + B' t - T' t := by
  have h : RMFiscalEq uC uN F FK FN β δ τ { p with B := B', T := T' } := by
    intro t
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11⟩ := heq t
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hgov t, h11⟩
  refine ⟨h, fun t => ?_⟩
  exact rm_walras (p := { p with B := B', T := T' }) t (hgov t) (h t).2.2.2.2.1
    (h t).2.2.2.2.2.2.2.2.2.2

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 14.1 and 14.2

Miao, §14.4, p. 507.

**Exercise 14.1.** The model of §14.1.2 in two further market arrangements in which households
own capital, rent it to firms at `R^k` and pay a capital income tax `τᵏ` on `(R^k − δ)K`
(the counterpart of the corporate tax with its depreciation allowance):

* sequential markets with one-period bonds (`RMHKPath`, `RMHKEq`); the household's
  first-order condition for `K_{t+1}` is `Λ_t = βΛ_{t+1}[(1 − δ) + R^k_{t+1} − τᵏ_{t+1}(R^k_{t+1} −
  δ)]`;
* an Arrow–Debreu market at date 0 (`RMADPath`, `RMADEq`), with date-0 prices `q_t`, the
  first-order conditions `βᵗu_C = λq_t(1 + τˢ_t)`, `−βᵗu_N = λq_t(1 − τⁿ_t)w_t`,
  `q_t = q_{t+1}[(1 − δ) + R^k_{t+1} − τᵏ_{t+1}(R^k_{t+1} − δ)]`.

With `τᵏ = τᶜ` and a constant distribution tax, the three arrangements (with the one of §14.1.2,
`RMFiscalEq`) have exactly the same equilibrium allocations: each is equivalent to the
allocation system `RMFiscalAlloc` (`ex_14_1_firm`, `ex_14_1_hk`, `ex_14_1_ad`), hence to each
other (`ex_14_1`).

**Exercise 14.2.** The steady state of §14.1.2 (`ex_14_2`): `R = 1/β`, the modified golden rule
with taxes `1 = β[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`, i.e. `F_K = (1/β − 1)/(1 − τᶜ) + δ`
(`ex_14_2_mgr`), `−u_N/u_C = (1 − τⁿ)F_N/(1 + τˢ)`, `I = δK`, `C + δK + G = F`, `Q = 1 − τᵈ`,
`V = (1 − τᵈ)D/(1 − β)`, and the government budget `G + (1 − β)B = revenue + T`. With constant
returns the dividends are `D = (1/β − 1)K` and the equity value `V = (1 − τᵈ)K/β`
(`ex_14_2_value`). The capital–labour ratio is unique (`rm_steady_ratio_exists_unique` applies),
independent of `τᵈ, τˢ, τⁿ`, and decreasing in `τᶜ` (`ex_14_2_corporate_tax`). For Cobb–Douglas
the ratio is `((α/r))^{1/(1−α)}` with `r = (1/β − 1)/(1 − τᶜ) + δ` (`ex_14_2_cd`). A concrete
steady state shows that the equilibrium system is satisfiable (`rm_fiscal_eq_example`).

**Departures.** Equilibria are described by their first-order conditions (as in the text). In
the Arrow–Debreu arrangement the government balances its budget date by date with lump-sum
taxes (by Ricardian equivalence, `rm_ricardian`, the timing of lump-sum taxes does not matter).
The equivalence uses a constant distribution tax: with a time-varying `τᵈ` the firm-ownership
arrangement has the distorted condition of `rm_temporary_distribution_tax`.
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-- The allocation system common to the three arrangements: the consumption Euler equation with
the after-tax return on capital, the labour condition, (14.18) and the resource constraint. -/
def RMFiscalAlloc (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τs τn τc : ℕ → ℝ)
    (C N K I G : ℕ → ℝ) : Prop :=
  ∀ t, uC (C t) (N t) / (1 + τs t) = β * (uC (C (t + 1)) (N (t + 1)) / (1 + τs (t + 1))) *
      ((1 - δ) + τc (t + 1) * δ + (1 - τc (t + 1)) * FK (K (t + 1)) (N (t + 1))) ∧
    -uN (C t) (N t) / uC (C t) (N t) = (1 - τn t) / (1 + τs t) * FN (K t) (N t) ∧
    K (t + 1) = (1 - δ) * K t + I t ∧ C t + I t + G t = F (K t) (N t)

/-! ### The arrangement of §14.1.2 -/

/-- **Exercise 14.1** (Miao, p. 507), the arrangement of §14.1.2 (firms own capital): with a
constant distribution tax `τᵈ ≠ 1`, an allocation is an equilibrium allocation iff it satisfies
`RMFiscalAlloc`. (`u_C ≠ 0`, `1 + τˢ ≠ 0`, `β > 0`, and `F = F_KK + F_NN` along the allocation.) -/
theorem ex_14_1_firm {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ td : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (htd : 1 - td ≠ 0) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0)
    (hE : ∀ t, F (K t) (N t) = FK (K t) (N t) * K t + FN (K t) (N t) * N t) :
    (∃ p : RMFiscalPath, RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td, τn, τc⟩ p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      RMFiscalAlloc uC uN F FK FN β δ τs τn τc C N K I G := by
  constructor
  · rintro ⟨p, heq, rfl, rfl, rfl, rfl, rfl⟩ t
    obtain ⟨h1, h2, -, -, -, h6, h7, h8, h9, -, h11⟩ := heq t
    obtain ⟨h1', -⟩ := heq (t + 1)
    have h8' := (heq (t + 1)).2.2.2.2.2.2.2.1
    simp only at h1 h2 h6 h7 h8 h9 h11 h1' h8'
    have hl : p.lam t ≠ 0 := fun h => huc t (by rw [h1, h, mul_zero])
    rw [h8, h8'] at h9
    have h21 := (eq_14_21 htd).1 h9
    refine ⟨?_, ?_, h6, h11⟩
    · rw [h1, h1', mul_div_cancel_left₀ _ (hs t), mul_div_cancel_left₀ _ (hs (t + 1))]
      field_simp at h21
      linear_combination h21
    · rw [rm_fiscal_labour (hs t) hl h1 h2, h7]; ring
  · intro h
    set lam : ℕ → ℝ := fun t => uC (C t) (N t) / (1 + τs t) with hlam
    have hl : ∀ t, lam t ≠ 0 := fun t => div_ne_zero (huc t) (hs t)
    set w : ℕ → ℝ := fun t => FN (K t) (N t) with hw
    set D : ℕ → ℝ := fun t => (1 - τc t) * (F (K t) (N t) - w t * N t) - I t + τc t * δ * K t
      with hD
    refine ⟨⟨C, N, K, I, G, w, fun t => lam t / (β * lam (t + 1)), lam,
      fun t => (1 - td) * (D t + K (t + 1)), D, fun _ => 1 - td, fun _ => 0,
      fun t => G t - τs t * C t - td * D t -
        τc t * (F (K t) (N t) - w t * N t - δ * K t) - τn t * w t * N t⟩,
      fun t => ?_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := h t
    obtain ⟨-, -, e3', -⟩ := h (t + 1)
    have heul : lam t = β * lam (t + 1) *
        ((1 - δ) + τc (t + 1) * δ + (1 - τc (t + 1)) * FK (K (t + 1)) (N (t + 1))) := by
      simp only [hlam]; rw [e1]
    have hkey : lam t * K (t + 1) = β * lam (t + 1) * (D (t + 1) + K (t + 1 + 1)) := by
      simp only [hD, hw]
      rw [e3', hE (t + 1), heul]; ring
    refine ⟨?_, ?_, ?_, ?_, rfl, e3, rfl, rfl, ?_, ?_, e4⟩
    · simp only [hlam]; field_simp [hs t]
    · simp only [hlam, hw]
      rw [div_eq_iff (huc t)] at e2
      linear_combination e2
    · simp only
      linear_combination (1 - td) * hkey
    · simp only
      field_simp [hl (t + 1), hβ.ne']
    · simp only
      have := (eq_14_21 (m := β * lam (t + 1) / lam t) (δ := δ) (τc := τc (t + 1))
        (FK1 := FK (K (t + 1)) (N (t + 1))) htd).2 (by field_simp [hl t]; linear_combination heul)
      exact this
    · simp only [rmGovBudget, zero_div]; ring

/-! ### Households own capital -/

/-- Quantities and prices when households own capital: rental rate `Rk`, bond return `R`. -/
structure RMHKPath where
  C : ℕ → ℝ
  N : ℕ → ℝ
  K : ℕ → ℝ
  I : ℕ → ℝ
  G : ℕ → ℝ
  w : ℕ → ℝ
  Rk : ℕ → ℝ
  R : ℕ → ℝ
  lam : ℕ → ℝ
  B : ℕ → ℝ
  T : ℕ → ℝ

/-- **Exercise 14.1**, households own capital: the household's first-order conditions for
`C, N, K_{t+1}, B_{t+1}` (budget `(1 + τˢ)C + I + B_{t+1}/R = (1 − τⁿ)wN + R^kK − τᵏ(R^k − δ)K +
B − T`), the firm's static conditions `R^k = F_K`, `w = F_N`, (14.18), the government budget
constraint and the resource constraint. -/
def RMHKEq (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τs τn τk : ℕ → ℝ) (p : RMHKPath) : Prop :=
  ∀ t, uC (p.C t) (p.N t) = (1 + τs t) * p.lam t ∧
    -uN (p.C t) (p.N t) = (1 - τn t) * p.lam t * p.w t ∧
    p.lam t = β * p.lam (t + 1) *
      ((1 - δ) + p.Rk (t + 1) - τk (t + 1) * (p.Rk (t + 1) - δ)) ∧
    p.lam t = β * p.lam (t + 1) * p.R t ∧
    p.Rk t = FK (p.K t) (p.N t) ∧ p.w t = FN (p.K t) (p.N t) ∧
    p.K (t + 1) = (1 - δ) * p.K t + p.I t ∧
    p.G t + p.B t = p.B (t + 1) / p.R t + τs t * p.C t + τk t * (p.Rk t - δ) * p.K t +
      τn t * p.w t * p.N t + p.T t ∧
    p.C t + p.I t + p.G t = F (p.K t) (p.N t)

/-- **Exercise 14.1** (Miao, p. 507), households own capital: with `τᵏ = τᶜ`, an allocation is an
equilibrium allocation iff it satisfies `RMFiscalAlloc`. -/
theorem ex_14_1_hk {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0) :
    (∃ p : RMHKPath, RMHKEq uC uN F FK FN β δ τs τn τc p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      RMFiscalAlloc uC uN F FK FN β δ τs τn τc C N K I G := by
  constructor
  · rintro ⟨p, heq, rfl, rfl, rfl, rfl, rfl⟩ t
    obtain ⟨h1, h2, h3, -, -, h6, h7, -, h9⟩ := heq t
    obtain ⟨h1', -, -, -, h5', -⟩ := heq (t + 1)
    have hl : p.lam t ≠ 0 := fun h => huc t (by rw [h1, h, mul_zero])
    refine ⟨?_, ?_, h7, h9⟩
    · rw [h1, h1', ← h5']
      field_simp [hs t, hs (t + 1)]
      linear_combination h3
    · rw [rm_fiscal_labour (hs t) hl h1 h2, h6]; ring
  · intro h
    set lam : ℕ → ℝ := fun t => uC (C t) (N t) / (1 + τs t) with hlam
    have hl : ∀ t, lam t ≠ 0 := fun t => div_ne_zero (huc t) (hs t)
    refine ⟨⟨C, N, K, I, G, fun t => FN (K t) (N t), fun t => FK (K t) (N t),
      fun t => lam t / (β * lam (t + 1)), lam, fun _ => 0,
      fun t => G t - τs t * C t - τc t * (FK (K t) (N t) - δ) * K t -
        τn t * FN (K t) (N t) * N t⟩, fun t => ?_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := h t
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, e3, ?_, e4⟩
    · simp only [hlam]; field_simp [hs t]
    · simp only [hlam]
      rw [div_eq_iff (huc t)] at e2
      linear_combination e2
    · simp only [hlam]; rw [e1]; ring
    · simp only
      field_simp [hl (t + 1), hβ.ne']
    · simp only [zero_div]; ring

/-! ### Arrow–Debreu -/

/-- Quantities and prices of the Arrow–Debreu arrangement: date-0 prices `q`, multiplier `lam0`.
-/
structure RMADPath where
  C : ℕ → ℝ
  N : ℕ → ℝ
  K : ℕ → ℝ
  I : ℕ → ℝ
  G : ℕ → ℝ
  w : ℕ → ℝ
  Rk : ℕ → ℝ
  q : ℕ → ℝ
  lam0 : ℝ
  T : ℕ → ℝ

/-- **Exercise 14.1**, Arrow–Debreu (households own capital, date-0 market): the household's
first-order conditions, the firm's conditions, (14.18), date-by-date government budget balance
and the resource constraint. -/
def RMADEq (uC uN F FK FN : ℝ → ℝ → ℝ) (β δ : ℝ) (τs τn τk : ℕ → ℝ) (p : RMADPath) : Prop :=
  ∀ t, β ^ t * uC (p.C t) (p.N t) = p.lam0 * p.q t * (1 + τs t) ∧
    -(β ^ t * uN (p.C t) (p.N t)) = p.lam0 * p.q t * (1 - τn t) * p.w t ∧
    p.q t = p.q (t + 1) * ((1 - δ) + p.Rk (t + 1) - τk (t + 1) * (p.Rk (t + 1) - δ)) ∧
    p.Rk t = FK (p.K t) (p.N t) ∧ p.w t = FN (p.K t) (p.N t) ∧
    p.K (t + 1) = (1 - δ) * p.K t + p.I t ∧
    p.G t = τs t * p.C t + τk t * (p.Rk t - δ) * p.K t + τn t * p.w t * p.N t + p.T t ∧
    p.C t + p.I t + p.G t = F (p.K t) (p.N t)

/-- **Exercise 14.1** (Miao, p. 507), Arrow–Debreu: with `τᵏ = τᶜ`, an allocation is an
equilibrium allocation iff it satisfies `RMFiscalAlloc`. -/
theorem ex_14_1_ad {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0) :
    (∃ p : RMADPath, RMADEq uC uN F FK FN β δ τs τn τc p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      RMFiscalAlloc uC uN F FK FN β δ τs τn τc C N K I G := by
  constructor
  · rintro ⟨p, heq, rfl, rfl, rfl, rfl, rfl⟩ t
    obtain ⟨h1, h2, h3, -, h5, h6, -, h8⟩ := heq t
    obtain ⟨h1', -, -, h4', -⟩ := heq (t + 1)
    have hb : β ^ t ≠ 0 := (pow_pos hβ t).ne'
    refine ⟨?_, ?_, h6, h8⟩
    · rw [← h4']
      have hu0 : uC (p.C t) (p.N t) = p.lam0 * p.q t * (1 + τs t) / β ^ t := by
        field_simp; linear_combination h1
      have hu1 : uC (p.C (t + 1)) (p.N (t + 1)) =
          p.lam0 * p.q (t + 1) * (1 + τs (t + 1)) / β ^ (t + 1) := by
        field_simp; linear_combination h1'
      rw [hu0, hu1, h3, pow_succ]
      field_simp [hs t, hs (t + 1)]
      ring
    · rw [← h5, div_eq_iff (huc t)]
      have hd : (1 + τs t) * (1 + τs t)⁻¹ = 1 := mul_inv_cancel₀ (hs t)
      have : β ^ t * (-uN (p.C t) (p.N t)) =
          β ^ t * ((1 - τn t) / (1 + τs t) * p.w t * uC (p.C t) (p.N t)) := by
        linear_combination h2 - ((1 - τn t) / (1 + τs t) * p.w t) * h1 -
          (p.lam0 * p.q t * p.w t * (1 - τn t)) * hd
      exact mul_left_cancel₀ hb this
  · intro h
    refine ⟨⟨C, N, K, I, G, fun t => FN (K t) (N t), fun t => FK (K t) (N t),
      fun t => β ^ t * uC (C t) (N t) / (1 + τs t), 1,
      fun t => G t - τs t * C t - τc t * (FK (K t) (N t) - δ) * K t -
        τn t * FN (K t) (N t) * N t⟩, fun t => ?_, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := h t
    refine ⟨?_, ?_, ?_, rfl, rfl, e3, ?_, e4⟩
    · simp only; field_simp [hs t]
    · simp only
      rw [div_eq_iff (huc t)] at e2
      linear_combination β ^ t * e2
    · simp only
      linear_combination β ^ t * e1
    · simp only; ring

/-- **Exercise 14.1** (Miao, p. 507): the three arrangements (firms own capital with a constant
distribution tax; households own capital with sequential markets; Arrow–Debreu), with
`τᵏ = τᶜ`, have the same equilibrium allocations. -/
theorem ex_14_1 {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ td : ℝ} {τs τn τc : ℕ → ℝ}
    {C N K I G : ℕ → ℝ} (hβ : 0 < β) (htd : 1 - td ≠ 0) (hs : ∀ t, 1 + τs t ≠ 0)
    (huc : ∀ t, uC (C t) (N t) ≠ 0)
    (hE : ∀ t, F (K t) (N t) = FK (K t) (N t) * K t + FN (K t) (N t) * N t) :
    ((∃ p : RMFiscalPath, RMFiscalEq uC uN F FK FN β δ ⟨τs, fun _ => td, τn, τc⟩ p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      (∃ p : RMHKPath, RMHKEq uC uN F FK FN β δ τs τn τc p ∧
        p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G)) ∧
    ((∃ p : RMHKPath, RMHKEq uC uN F FK FN β δ τs τn τc p ∧
      p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G) ↔
      (∃ p : RMADPath, RMADEq uC uN F FK FN β δ τs τn τc p ∧
        p.C = C ∧ p.N = N ∧ p.K = K ∧ p.I = I ∧ p.G = G)) := by
  rw [ex_14_1_firm hβ htd hs huc hE, ex_14_1_hk hβ hs huc, ex_14_1_ad hβ hs huc]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-! ### Exercise 14.2: the steady state -/

/-- The constant path with the given values. -/
def rmConstPath (C N K I G w R lam V D Q B T : ℝ) : RMFiscalPath :=
  ⟨fun _ => C, fun _ => N, fun _ => K, fun _ => I, fun _ => G, fun _ => w, fun _ => R,
    fun _ => lam, fun _ => V, fun _ => D, fun _ => Q, fun _ => B, fun _ => T⟩

/-- **Exercise 14.2** (Miao, p. 507): the steady state of §14.1.2. With constant taxes, `β ∈
(0, 1)`, `1 + τˢ ≠ 0`, `τᵈ ≠ 1` and `u_C ≠ 0`, a constant path is an equilibrium iff
`Λ = u_C/(1 + τˢ)`, `w = F_N`, `−u_N/u_C = (1 − τⁿ)F_N/(1 + τˢ)`, `R = 1/β`,
`1 = β[(1 − δ) + τᶜδ + (1 − τᶜ)F_K]`, `Q = 1 − τᵈ`, `I = δK`, the dividend definition,
`V = (1 − τᵈ)D/(1 − β)`, `C + δK + G = F` and the government budget
`G + (1 − β)B = τˢC + τᵈD + τᶜ(F − wN − δK) + τⁿwN + T`. -/
theorem ex_14_2 {uC uN F FK FN : ℝ → ℝ → ℝ} {β δ ts td tn tc : ℝ}
    {C N K I G w R lam V D Q B T : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs : 1 + ts ≠ 0)
    (htd : 1 - td ≠ 0) (huc : uC C N ≠ 0) :
    RMFiscalEq uC uN F FK FN β δ ⟨fun _ => ts, fun _ => td, fun _ => tn, fun _ => tc⟩
        (rmConstPath C N K I G w R lam V D Q B T) ↔
      lam = uC C N / (1 + ts) ∧ w = FN K N ∧
        -uN C N / uC C N = (1 - tn) * FN K N / (1 + ts) ∧ R = 1 / β ∧
        1 = β * ((1 - δ) + tc * δ + (1 - tc) * FK K N) ∧ Q = 1 - td ∧ I = δ * K ∧
        D = (1 - tc) * (F K N - w * N) - I + tc * δ * K ∧ V = (1 - td) * D / (1 - β) ∧
        C + δ * K + G = F K N ∧
        G + (1 - β) * B = ts * C + td * D + tc * (F K N - w * N - δ * K) + tn * w * N + T := by
  have hb1 : 1 - β ≠ 0 := by linarith
  constructor
  · intro h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h 0
    simp only [rmConstPath, rmGovBudget] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    have hl : lam ≠ 0 := fun h => huc (by rw [h1, h, mul_zero])
    have hR : R = 1 / β := by
      field_simp
      have : lam * 1 = lam * (β * R) := by linear_combination h4
      linarith [mul_left_cancel₀ hl this]
    have hI : I = δ * K := by linarith
    refine ⟨by field_simp; linarith, h7, ?_, hR, ?_, h8, hI, h5, ?_, by linarith, ?_⟩
    · rw [rm_fiscal_labour hs hl h1 h2, h7]
    · rw [h8] at h9
      have hβl : β * lam / lam = β := by field_simp
      rw [hβl] at h9
      exact (eq_14_21 (m := β) htd).1 h9
    · field_simp
      have : lam * (V - (1 - td) * D) = lam * (β * V) := by linear_combination h3
      have := mul_left_cancel₀ hl this
      linarith
    · rw [hR] at h10
      field_simp at h10
      linear_combination h10
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ t
    have hl : lam ≠ 0 := by rw [h1]; exact div_ne_zero huc hs
    simp only [rmConstPath, rmGovBudget]
    refine ⟨by rw [h1]; field_simp, ?_, ?_, by rw [h4]; field_simp, h8, by linarith, h2, h6,
      ?_, ?_, by linarith⟩
    · rw [div_eq_iff huc] at h3
      rw [h3, h1, h2]; field_simp
    · rw [h9]; field_simp; ring
    · rw [h6]
      have hβl : β * lam / lam = β := by field_simp
      rw [hβl]
      linear_combination (1 - td) * h5
    · rw [h4]; field_simp; linear_combination h11

/-- **Exercise 14.2**, a concrete steady state (so `RMFiscalEq` is satisfiable): linear utility
`u = C − N`, `F(K, N) = (1/β − 1 + δ)K + N`, zero distortionary taxes, `I = δK`,
`C = (1/β − 1)K + N`, `w = 1`, `R = 1/β`, `Λ = Q = 1`, `D = (1/β − 1)K`,
`V = D/(1 − β)`, `B = T = G = 0`. -/
theorem rm_fiscal_eq_example {β δ K N : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    RMFiscalEq (fun _ _ => 1) (fun _ _ => -1) (fun k n => (1 / β - 1 + δ) * k + n)
      (fun _ _ => 1 / β - 1 + δ) (fun _ _ => 1) β δ
      ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
      (rmConstPath ((1 / β - 1) * K + N) N K (δ * K) 0 1 (1 / β) 1
        ((1 / β - 1) * K / (1 - β)) ((1 / β - 1) * K) 1 0 0) := by
  refine (ex_14_2 (uC := fun _ _ => 1) hβ0 hβ1 (by norm_num) (by norm_num)
    (by norm_num)).2 ⟨by norm_num, rfl, by norm_num, rfl, ?_, by norm_num, rfl, by ring,
      by ring, by ring, by ring⟩
  field_simp
  ring

/-- **Exercise 14.2**: the steady-state modified golden rule with a corporate tax,
`F_K = (1/β − 1)/(1 − τᶜ) + δ` (for `τᶜ ≠ 1`). -/
theorem ex_14_2_mgr {β δ tc FK : ℝ} (hβ : 0 < β) (htc : 1 - tc ≠ 0) :
    1 = β * ((1 - δ) + tc * δ + (1 - tc) * FK) ↔ FK = (1 / β - 1) / (1 - tc) + δ := by
  constructor
  · intro h; field_simp; linear_combination -h
  · intro h; rw [h]; field_simp; ring

/-- **Exercise 14.2**: with constant returns (`F = F_KK + F_NN`, `w = F_N`) dividends are
`D = (1/β − 1)K` and the equity value `V = (1 − τᵈ)D/(1 − β) = (1 − τᵈ)K/β`, the steady-state
form of Proposition 14.1.1 (`V − (1 − τᵈ)D = (1 − τᵈ)K`). -/
theorem ex_14_2_value {β δ td tc K N F FK FN w I D V : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hE : F = FK * K + FN * N) (hw : w = FN) (hI : I = δ * K)
    (hmgr : 1 = β * ((1 - δ) + tc * δ + (1 - tc) * FK))
    (hD : D = (1 - tc) * (F - w * N) - I + tc * δ * K) (hV : V = (1 - td) * D / (1 - β)) :
    D = (1 / β - 1) * K ∧ V = (1 - td) * K / β ∧ V - (1 - td) * D = (1 - td) * K := by
  have hb1 : 1 - β ≠ 0 := by linarith
  have hD' : D = (1 / β - 1) * K := by
    rw [hD, hE, hw, hI]; field_simp; linear_combination (-K) * hmgr
  refine ⟨hD', ?_, ?_⟩
  · rw [hV, hD']; field_simp
  · rw [hV, hD']; field_simp; ring

/-- **Exercise 14.2**, comparative statics: the steady-state target
`r(τᶜ) = (1/β − 1)/(1 − τᶜ) + δ` does not involve `τᵈ, τˢ, τⁿ` and is increasing in `τᶜ < 1`, so
a higher corporate tax lowers the capital–labour ratio when `F_K(·, 1)` is strictly
decreasing. -/
theorem ex_14_2_corporate_tax {f : ℝ → ℝ} (hanti : StrictAntiOn f (Set.Ioi 0))
    {β δ tc1 tc2 x1 x2 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (htc : tc1 < tc2) (htc2 : tc2 < 1)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (h1 : f x1 = (1 / β - 1) / (1 - tc1) + δ)
    (h2 : f x2 = (1 / β - 1) / (1 - tc2) + δ) : x2 < x1 := by
  refine rm_steady_ratio_anti hanti hx1 hx2 h1 h2 ?_
  have hb : 0 < 1 / β - 1 := by rw [sub_pos, lt_div_iff₀ hβ0]; linarith
  have : (1 / β - 1) / (1 - tc1) < (1 / β - 1) / (1 - tc2) :=
    div_lt_div_of_pos_left hb (by linarith) (by linarith)
  linarith

/-- **Exercise 14.2**, Cobb–Douglas: with `r = (1/β − 1)/(1 − τᶜ) + δ > 0`, the ratio
`x = (α/r)^{1/(1−α)}` solves the modified golden rule `F_K(xN, N) = r` for every `N > 0`. -/
theorem ex_14_2_cd {α r N : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hN : 0 < N) :
    rmCDK α ((α / r) ^ (1 / (1 - α)) * N) N = r := by
  have hx : 0 < (α / r) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos (div_pos hα0 hr) _
  have hxa : ((α / r) ^ (1 / (1 - α))) ^ (α - 1) = r / α := by
    rw [← Real.rpow_mul (div_pos hα0 hr).le, show 1 / (1 - α) * (α - 1) = -1 by
      field_simp [show 1 - α ≠ 0 by linarith]; ring, Real.rpow_neg_one, inv_div]
  have := (rm_cd_homog α hN hx one_pos).2.1
  rw [show N * (α / r) ^ (1 / (1 - α)) = (α / r) ^ (1 / (1 - α)) * N by ring, mul_one] at this
  rw [this]
  simp only [rmCDK, Real.one_rpow, mul_one, hxa]
  field_simp

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic RBC model: technology, preferences and the static first-order conditions

Miao, §14.2, pp. 471–473. The planner maximises `E ∑ βᵗ[ln C_t + χ ln(1 − N_t)]` (14.22)
subject to `C_t + I_t = z_tK_t^αN_t^{1−α} = Y_t` (14.23), `K_{t+1} = (1 − δ)K_t + I_t` (14.24),
`ln z_t = ρ ln z_{t−1} + σε_t` (14.25).

* Cobb–Douglas technology: output `rb_Y`, marginal products `rb_MPK`, `rb_MPL`, the identities
  `R_k = αY/K`, `w = (1 − α)Y/N` (`rb_MPK_eq`, `rb_MPL_eq`), Euler's theorem (`rb_euler_thm`),
  the tangent (concavity) inequality (`rb_cd_tangent`), and the firm's problem: marginal-product
  prices give a profit maximum with zero profit (`rb_firm_optimal`), and conversely a profit
  maximum with positive inputs has marginal-product prices (`rb_firm_foc`).
* The intratemporal condition (14.27): given `K_t`, `K_{t+1}` (hence `I_t`), `N_t` maximises
  `ln(zK^αN^{1−α} − I) + χ ln(1 − N)` iff `χC/(1 − N) = (1 − α)zK^αN^{−α}`
  (`eq_14_27`, `rb_labour_suff`, `rb_labour_nec`).
* The Euler equation (14.26) derived from the one-step variation in `K_{t+1}` with a finite
  conditional distribution of the next-period state (`eq_14_26_node`, `rb_euler_node_suff`,
  `rb_euler_node_nec`); the general measure-theoretic statement is in `RBPlanner`.
* The shock (14.25) iterated (`eq_14_25_iter`), and the Solow residual `SR_t = ln z_t`
  (`rb_solow_residual`).

**Departures.** The book's (14.26) is stated for a general distribution of `ε`; here the
derivation by the one-step variation is carried out for a finite conditional distribution
(weights `p i ≥ 0`, `∑ p i = 1`), while `RBPlanner` proves the sufficiency of (14.26), (14.27) and
transversality with a general conditional expectation.
-/

namespace Miao.NeoclassicalGrowth

open Real

/-! ### Technology -/

/-- Cobb–Douglas output `Y = zK^αN^{1−α}` (Miao, (14.23), p. 472). -/
noncomputable def rb_Y (α z K N : ℝ) : ℝ := z * K ^ α * N ^ (1 - α)

/-- The marginal product of capital `αzK^{α−1}N^{1−α}`, the rental rate `R_k` (Miao, p. 472). -/
noncomputable def rb_MPK (α z K N : ℝ) : ℝ := α * z * K ^ (α - 1) * N ^ (1 - α)

/-- The marginal product of labour `(1 − α)zK^αN^{−α}`, the wage `w` (Miao, p. 472). -/
noncomputable def rb_MPL (α z K N : ℝ) : ℝ := (1 - α) * z * K ^ α * N ^ (-α)

theorem rb_rpow_sub_one' {x : ℝ} (hx : 0 < x) (a : ℝ) : x ^ (a - 1) = x ^ a / x := by
  rw [Real.rpow_sub_one hx.ne']

theorem rb_rpow_neg' {x : ℝ} (hx : 0 < x) (α : ℝ) : x ^ (-α) = x ^ (1 - α) / x := by
  rw [← rb_rpow_sub_one' hx]
  ring_nf

/-- Miao, p. 473: `R_k = αY/K`. -/
theorem rb_MPK_eq (α z : ℝ) {K N : ℝ} (hK : 0 < K) :
    rb_MPK α z K N = α * rb_Y α z K N / K := by
  rw [rb_MPK, rb_Y, rb_rpow_sub_one' hK]
  ring

/-- Miao, p. 473: `w = (1 − α)Y/N`. -/
theorem rb_MPL_eq (α z K : ℝ) {N : ℝ} (hN : 0 < N) :
    rb_MPL α z K N = (1 - α) * rb_Y α z K N / N := by
  rw [rb_MPL, rb_Y, rb_rpow_neg' hN]
  ring

/-- Euler's theorem for the constant-returns technology: `R_kK + wN = Y`. -/
theorem rb_euler_thm (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPK α z K N * K + rb_MPL α z K N * N = rb_Y α z K N := by
  rw [rb_MPK_eq α z hK, rb_MPL_eq α z K hN]
  field_simp
  ring

theorem rb_Y_pos {α z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    0 < rb_Y α z K N := by
  unfold rb_Y
  have := Real.rpow_pos_of_pos hK α
  have := Real.rpow_pos_of_pos hN (1 - α)
  positivity

theorem rb_MPK_pos {α z K N : ℝ} (hα : 0 < α) (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    0 < rb_MPK α z K N := by
  rw [rb_MPK_eq α z hK]
  have := rb_Y_pos (α := α) hz hK hN
  positivity

theorem rb_MPL_pos {α z K N : ℝ} (hα : α < 1) (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    0 < rb_MPL α z K N := by
  rw [rb_MPL_eq α z K hN]
  have := rb_Y_pos (α := α) hz hK hN
  have : 0 < 1 - α := by linarith
  positivity

/-- The Cobb–Douglas tangent inequality: for `0 < α < 1`, `z ≥ 0`, `K, N > 0` and
`K', N' ≥ 0`, `zK'^αN'^{1−α} ≤ R_kK' + wN'` with `R_k`, `w` the marginal products at `(K, N)`.
This is the joint concavity of the technology. -/
theorem rb_cd_tangent {α z K N K' N' : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 ≤ z)
    (hK : 0 < K) (hN : 0 < N) (hK' : 0 ≤ K') (hN' : 0 ≤ N') :
    rb_Y α z K' N' ≤ rb_MPK α z K N * K' + rb_MPL α z K N * N' := by
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hα0.le (by linarith : 0 ≤ 1 - α)
    (div_nonneg hK' hK.le) (div_nonneg hN' hN.le) (by ring)
  rw [Real.div_rpow hK' hK.le, Real.div_rpow hN' hN.le] at hamgm
  have hKa := Real.rpow_pos_of_pos hK α
  have hNa := Real.rpow_pos_of_pos hN (1 - α)
  have hA : 0 < z * K ^ α * N ^ (1 - α) + 1 := by positivity
  have key : K' ^ α * N' ^ (1 - α) ≤
      (α * (K' / K) + (1 - α) * (N' / N)) * (K ^ α * N ^ (1 - α)) := by
    have h := mul_le_mul_of_nonneg_right hamgm (le_of_lt (mul_pos hKa hNa))
    calc K' ^ α * N' ^ (1 - α)
        = K' ^ α / K ^ α * (N' ^ (1 - α) / N ^ (1 - α)) * (K ^ α * N ^ (1 - α)) := by
          field_simp
      _ ≤ _ := h
  rw [rb_MPK, rb_MPL, rb_Y, rb_rpow_sub_one' hK, rb_rpow_neg' hN]
  have := mul_le_mul_of_nonneg_left key hz
  clear hA
  calc z * K' ^ α * N' ^ (1 - α) = z * (K' ^ α * N' ^ (1 - α)) := by ring
    _ ≤ z * ((α * (K' / K) + (1 - α) * (N' / N)) * (K ^ α * N ^ (1 - α))) := this
    _ = _ := by field_simp

/-- The tangent inequality in the form `Y(K', N') ≤ Y(K, N) + R_k(K' − K) + w(N' − N)`. -/
theorem rb_cd_tangent' {α z K N K' N' : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 ≤ z)
    (hK : 0 < K) (hN : 0 < N) (hK' : 0 ≤ K') (hN' : 0 ≤ N') :
    rb_Y α z K' N' ≤
      rb_Y α z K N + rb_MPK α z K N * (K' - K) + rb_MPL α z K N * (N' - N) := by
  have h1 := rb_cd_tangent hα0 hα1 hz hK hN hK' hN'
  have h2 := rb_euler_thm α z hK hN
  linarith

/-! ### The firm's problem -/

/-- Profit `zK^αN^{1−α} − R_kK − wN` of the firm (Miao, p. 460 and p. 472). -/
noncomputable def rb_profit (α z Rk w K N : ℝ) : ℝ := rb_Y α z K N - Rk * K - w * N

/-- Miao, p. 472: with the marginal-product prices `R_k = αzK^{α−1}N^{1−α}`,
`w = (1 − α)zK^αN^{−α}`, `(K, N)` maximises the firm's profit over all `K', N' ≥ 0`, and the
maximal profit is zero. -/
theorem rb_firm_optimal {α z K N : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 ≤ z) (hK : 0 < K)
    (hN : 0 < N) :
    rb_profit α z (rb_MPK α z K N) (rb_MPL α z K N) K N = 0 ∧
      ∀ K' N', 0 ≤ K' → 0 ≤ N' →
        rb_profit α z (rb_MPK α z K N) (rb_MPL α z K N) K' N' ≤ 0 := by
  refine ⟨?_, fun K' N' hK' hN' => ?_⟩
  · rw [rb_profit, ← rb_euler_thm α z hK hN]
    ring
  · rw [rb_profit]
    linarith [rb_cd_tangent hα0 hα1 hz hK hN hK' hN']

theorem rb_hasDerivAt_Y_K (α z N : ℝ) {K : ℝ} (hK : 0 < K) :
    HasDerivAt (fun k => rb_Y α z k N) (rb_MPK α z K N) K := by
  have h := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul z
  have h2 := h.mul_const (N ^ (1 - α))
  convert h2 using 1
  · rfl
  · rw [rb_MPK]; ring

theorem rb_hasDerivAt_Y_N (α z K : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => rb_Y α z K n) (rb_MPL α z K N) N := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul (z * K ^ α)
  convert h using 1
  · rfl
  · rw [rb_MPL]; ring_nf

/-- Miao, p. 472, the converse: if `(K, N)` with `K, N > 0` maximises profit given `(R_k, w)`,
then `R_k` and `w` are the marginal products. -/
theorem rb_firm_foc {α z Rk w K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (hmax : ∀ K' N', 0 ≤ K' → 0 ≤ N' → rb_profit α z Rk w K' N' ≤ rb_profit α z Rk w K N) :
    Rk = rb_MPK α z K N ∧ w = rb_MPL α z K N := by
  constructor
  · have hloc : IsLocalMax (fun k => rb_profit α z Rk w k N) K := by
      filter_upwards [lt_mem_nhds hK] with k hk using hmax k N hk.le hN.le
    have hd : HasDerivAt (fun k => rb_profit α z Rk w k N) (rb_MPK α z K N - Rk) K := by
      have := ((rb_hasDerivAt_Y_K α z N hK).sub ((hasDerivAt_id K).const_mul Rk)).sub_const
        (w * N)
      convert this using 1
      · funext k; simp [rb_profit]
      · ring
    linarith [hloc.hasDerivAt_eq_zero hd]
  · have hloc : IsLocalMax (fun n => rb_profit α z Rk w K n) N := by
      filter_upwards [lt_mem_nhds hN] with n hn using hmax K n hK.le hn.le
    have hd : HasDerivAt (fun n => rb_profit α z Rk w K n) (rb_MPL α z K N - w) N := by
      have := ((rb_hasDerivAt_Y_N α z K hN).sub_const (Rk * K)).sub
        ((hasDerivAt_id N).const_mul w)
      convert this using 1
      · funext n; simp [rb_profit]
      · ring
    linarith [hloc.hasDerivAt_eq_zero hd]

/-! ### Preferences and the intratemporal condition (14.27) -/

/-- Period utility `ln C + χ ln(1 − N)` (Miao, (14.22), p. 472). -/
noncomputable def rb_u (χ C N : ℝ) : ℝ := Real.log C + χ * Real.log (1 - N)

/-- Concavity of `ln`: `ln c' ≤ ln c + (c' − c)/c` for `c, c' > 0`. -/
theorem rb_log_tangent {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    Real.log c' ≤ Real.log c + (c' - c) / c := by
  have h := Real.log_le_sub_one_of_pos (div_pos hc' hc)
  rw [Real.log_div hc'.ne' hc.ne'] at h
  have : c' / c - 1 = (c' - c) / c := by field_simp
  linarith

/-- The utility tangent inequality: `u(c', n') ≤ u(c, n) + (c' − c)/c − χ(n' − n)/(1 − n)`. -/
theorem rb_u_tangent {χ c n c' n' : ℝ} (hχ : 0 ≤ χ) (hc : 0 < c) (hn : n < 1) (hc' : 0 < c')
    (hn' : n' < 1) :
    rb_u χ c' n' ≤ rb_u χ c n + (c' - c) / c - χ * ((n' - n) / (1 - n)) := by
  have h1 := rb_log_tangent hc hc'
  have h2 := rb_log_tangent (by linarith : 0 < 1 - n) (by linarith : 0 < 1 - n')
  have h3 := mul_le_mul_of_nonneg_left h2 hχ
  rw [rb_u, rb_u]
  have : (1 - n' - (1 - n)) / (1 - n) = -((n' - n) / (1 - n)) := by ring
  rw [this] at h3
  linarith

/-- The objective of the static labour choice given `(z, K)` and investment `I`:
`ln(zK^αN^{1−α} − I) + χ ln(1 − N)`. -/
noncomputable def rb_static (α χ z K I N : ℝ) : ℝ := rb_u χ (rb_Y α z K N - I) N

/-- Miao, (14.27), p. 472: the intratemporal condition `χC/(1 − N) = (1 − α)zK^αN^{−α}`. -/
def eq_14_27 (α χ z K C N : ℝ) : Prop := χ * C / (1 - N) = rb_MPL α z K N

/-- Miao, (14.27), sufficiency: if `N ∈ (0, 1)`, `C = zK^αN^{1−α} − I > 0` and (14.27) holds,
then `N` maximises the static objective over every `N' ∈ [0, 1)` with positive consumption. -/
theorem rb_labour_suff {α χ z K I N : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hχ : 0 ≤ χ)
    (hz : 0 ≤ z) (hK : 0 < K) (hN0 : 0 < N) (hN1 : N < 1) (hC : 0 < rb_Y α z K N - I)
    (hfoc : eq_14_27 α χ z K (rb_Y α z K N - I) N) {N' : ℝ} (hN0' : 0 ≤ N') (hN1' : N' < 1)
    (hC' : 0 < rb_Y α z K N' - I) :
    rb_static α χ z K I N' ≤ rb_static α χ z K I N := by
  have ht := rb_u_tangent hχ hC hN1 hC' hN1'
  have hY := rb_cd_tangent' (K' := K) hα0 hα1 hz hK hN0 hK.le hN0'
  set C := rb_Y α z K N - I
  have h1N : 0 < 1 - N := by linarith
  have hw : rb_MPL α z K N / C = χ / (1 - N) := by
    rw [eq_14_27] at hfoc
    rw [← hfoc]
    field_simp
  have hgap : (rb_Y α z K N' - I - C) / C ≤ rb_MPL α z K N * (N' - N) / C := by
    apply div_le_div_of_nonneg_right _ hC.le
    simp only [C]
    linarith
  have : rb_MPL α z K N * (N' - N) / C = χ * ((N' - N) / (1 - N)) := by
    rw [mul_comm, mul_div_assoc, mul_comm, hw]
    ring
  unfold rb_static
  linarith

theorem rb_hasDerivAt_static (α χ z K I : ℝ) {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1)
    (hC : 0 < rb_Y α z K N - I) :
    HasDerivAt (rb_static α χ z K I)
      (rb_MPL α z K N / (rb_Y α z K N - I) - χ / (1 - N)) N := by
  have h1 := ((rb_hasDerivAt_Y_N α z K hN0).sub_const I).log hC.ne'
  have h2 := (((hasDerivAt_id N).const_sub 1).log (by simp; linarith)).const_mul χ
  convert h1.add h2 using 1
  · funext n; simp [rb_static, rb_u]
  · simp only [id]
    field_simp
    ring

/-- Miao, (14.27), necessity: if `N ∈ (0, 1)` with positive consumption maximises the static
objective over `N' ∈ [0, 1)` with positive consumption, then (14.27) holds. -/
theorem rb_labour_nec {α χ z K I N : ℝ} (hN0 : 0 < N) (hN1 : N < 1)
    (hC : 0 < rb_Y α z K N - I)
    (hmax : ∀ N', 0 ≤ N' → N' < 1 → 0 < rb_Y α z K N' - I →
      rb_static α χ z K I N' ≤ rb_static α χ z K I N) :
    eq_14_27 α χ z K (rb_Y α z K N - I) N := by
  have hcont : ContinuousAt (fun n => rb_Y α z K n - I) N :=
    ((rb_hasDerivAt_Y_N α z K hN0).sub_const I).continuousAt
  have hloc : IsLocalMax (rb_static α χ z K I) N := by
    filter_upwards [lt_mem_nhds hN0, gt_mem_nhds hN1, hcont.eventually (lt_mem_nhds hC)]
      with n h0 h1 h2 using hmax n h0.le h1 h2
  have h0 := hloc.hasDerivAt_eq_zero (rb_hasDerivAt_static α χ z K I hN0 hN1 hC)
  rw [eq_14_27]
  have h1N : 0 < 1 - N := by linarith
  field_simp at h0 ⊢
  linarith

/-! ### The Euler equation (14.26) from the one-step variation -/

/-- The two-period objective of the variation in `K_{t+1} = k`: date-`t` consumption
`W − k` (`W = Y_t + (1 − δ)K_t`) and date-`t+1` consumption
`z_iK^αN_i^{1−α} + (1 − δ)k − K₂ᵢ` in state `i` with probability `p i`. -/
noncomputable def rb_node {ι : Type*} [Fintype ι] (α β δ W : ℝ) (p z N K₂ : ι → ℝ)
    (k : ℝ) : ℝ :=
  Real.log (W - k) + β * ∑ i, p i * Real.log (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)

/-- Miao, (14.26), p. 472, at a node with finitely many successor states:
`1/C_t = E_t[β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}]`. -/
def eq_14_26_node {ι : Type*} [Fintype ι] (α β δ W : ℝ) (p z N K₂ : ι → ℝ) (k : ℝ) : Prop :=
  1 / (W - k) =
    ∑ i, p i * (β * (rb_MPK α (z i) k (N i) + 1 - δ) /
      (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))

/-- Miao, (14.26), sufficiency of the Euler equation for the one-step variation: if
consumption is positive at `k > 0` in every state and (14.26) holds, `k` maximises the
two-period objective among all `k' ≥ 0` with positive consumption. -/
theorem rb_euler_node_suff {ι : Type*} [Fintype ι] {α β δ W : ℝ} {p z N K₂ : ι → ℝ} {k : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, 0 ≤ z i)
    (hN : ∀ i, 0 < N i) (hk : 0 < k) (hc0 : 0 < W - k)
    (hc1 : ∀ i, 0 < rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)
    (heul : eq_14_26_node α β δ W p z N K₂ k) {k' : ℝ} (hk' : 0 ≤ k') (hc0' : 0 < W - k')
    (hc1' : ∀ i, 0 < rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i) :
    rb_node α β δ W p z N K₂ k' ≤ rb_node α β δ W p z N K₂ k := by
  have h0 := rb_log_tangent hc0 hc0'
  have hi : ∀ i, p i * Real.log (rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i) ≤
      p i * Real.log (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i) +
        p i * ((rb_MPK α (z i) k (N i) + 1 - δ) /
          (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)) * (k' - k) := fun i => by
    have ht := rb_log_tangent (hc1 i) (hc1' i)
    have hY := rb_cd_tangent' hα0 hα1 (hz i) hk (hN i) hk' (hN i).le
    have hq : (rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i -
        (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)) /
          (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i) ≤
        (rb_MPK α (z i) k (N i) + 1 - δ) * (k' - k) /
          (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i) := by
      apply div_le_div_of_nonneg_right _ (hc1 i).le
      simp only [sub_self, mul_zero, add_zero] at hY
      nlinarith
    have := mul_le_mul_of_nonneg_left (ht.trans (add_le_add_right hq _)) (hp i)
    calc _ ≤ _ := this
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  have hs := mul_le_mul_of_nonneg_left hsum hβ
  unfold rb_node
  rw [eq_14_26_node] at heul
  have hE : β * ((∑ i, p i * ((rb_MPK α (z i) k (N i) + 1 - δ) /
      (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))) * (k' - k)) = (k' - k) / (W - k) := by
    rw [div_eq_mul_one_div (k' - k), heul, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have : (W - k' - (W - k)) / (W - k) = -((k' - k) / (W - k)) := by ring
  rw [this] at h0
  nlinarith

/-- Miao, (14.26), necessity: if `k > 0` with positive consumption maximises the two-period
objective among all `k' > 0` with positive consumption, the Euler equation holds. -/
theorem rb_euler_node_nec {ι : Type*} [Fintype ι] {α β δ W : ℝ} {p z N K₂ : ι → ℝ} {k : ℝ}
    (hk : 0 < k) (hc0 : 0 < W - k)
    (hc1 : ∀ i, 0 < rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)
    (hmax : ∀ k', 0 < k' → 0 < W - k' →
      (∀ i, 0 < rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i) →
        rb_node α β δ W p z N K₂ k' ≤ rb_node α β δ W p z N K₂ k) :
    eq_14_26_node α β δ W p z N K₂ k := by
  have hdi : ∀ i, HasDerivAt (fun k => rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i)
      (rb_MPK α (z i) k (N i) + (1 - δ)) k := fun i =>
    (((rb_hasDerivAt_Y_K α (z i) (N i) hk).add
      ((hasDerivAt_id k).const_mul (1 - δ))).sub_const (K₂ i)).congr_deriv (by simp)
  have hd : HasDerivAt (rb_node α β δ W p z N K₂)
      (-(1 / (W - k)) + β * ∑ i, p i * ((rb_MPK α (z i) k (N i) + (1 - δ)) /
        (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))) k := by
    have h0 : HasDerivAt (fun k => Real.log (W - k)) (-(1 / (W - k))) k := by
      have := ((hasDerivAt_id k).const_sub W).log hc0.ne'
      convert this using 1
      · rfl
      · exact (neg_div _ _).symm
    have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      ((hdi i).log (hc1 i).ne').const_mul (p i))
    convert h0.add (hs.const_mul β) using 1
    · funext k'
      simp [rb_node]
  have hev : ∀ᶠ k' in nhds k, ∀ i, 0 < rb_Y α (z i) k' (N i) + (1 - δ) * k' - K₂ i :=
    Filter.eventually_all.2 fun i => (hdi i).continuousAt.eventually (lt_mem_nhds (hc1 i))
  have hcW : ∀ᶠ k' in nhds k, 0 < W - k' :=
    ((continuous_const.sub continuous_id).continuousAt (x := k)).eventually (lt_mem_nhds hc0)
  have hloc : IsLocalMax (rb_node α β δ W p z N K₂) k := by
    filter_upwards [lt_mem_nhds hk, hcW, hev] with k' h1 h2 h3 using hmax k' h1 h2 h3
  have h0 := hloc.hasDerivAt_eq_zero hd
  rw [eq_14_26_node]
  rw [Finset.mul_sum] at h0
  rw [show (1 / (W - k)) = ∑ i, β * (p i * ((rb_MPK α (z i) k (N i) + (1 - δ)) /
      (rb_Y α (z i) k (N i) + (1 - δ) * k - K₂ i))) by linarith]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The shock process (14.25) and the Solow residual -/

/-- Miao, (14.25), p. 472: `ln z_t = ρ ln z_{t−1} + σε_t`, started from `ln z_0`. -/
noncomputable def rb_lnz (ρ σ lnz0 : ℝ) (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => lnz0
  | t + 1 => ρ * rb_lnz ρ σ lnz0 ε t + σ * ε (t + 1)

/-- Miao, (14.25) iterated: `ln z_t = ρᵗ ln z_0 + σ∑_{s<t} ρ^{t−1−s}ε_{s+1}`. -/
theorem eq_14_25_iter (ρ σ lnz0 : ℝ) (ε : ℕ → ℝ) (t : ℕ) :
    rb_lnz ρ σ lnz0 ε t =
      ρ ^ t * lnz0 + σ * ∑ s ∈ Finset.range t, ρ ^ (t - 1 - s) * ε (s + 1) := by
  induction t with
  | zero => simp [rb_lnz]
  | succ t ih =>
    rw [rb_lnz, ih, Finset.sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have : ∀ s ∈ Finset.range t, ρ ^ (t - s) * ε (s + 1) =
        ρ * (ρ ^ (t - 1 - s) * ε (s + 1)) := fun s hs => by
      have hs' := Finset.mem_range.1 hs
      obtain ⟨j, rfl⟩ : ∃ j, t = s + 1 + j := ⟨t - (s + 1), by omega⟩
      rw [show s + 1 + j - 1 - s = j by omega, show s + 1 + j - s = j + 1 by omega]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring

/-- Miao, p. 482: in the model the Solow residual `SR_t = ln Y_t − α ln K_t − (1 − α) ln N_t`
equals `ln z_t`. -/
theorem rb_solow_residual {α z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) :
    Real.log (rb_Y α z K N) - α * Real.log K - (1 - α) * Real.log N = Real.log z := by
  have hKa := Real.rpow_pos_of_pos hK α
  have hNa := Real.rpow_pos_of_pos hN (1 - α)
  rw [rb_Y, Real.log_mul (by positivity) hNa.ne', Real.log_mul hz.ne' hKa.ne',
    Real.log_rpow hK, Real.log_rpow hN]
  ring

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stochastic planner's problem of the basic RBC model

Miao, §14.2, p. 472: the planner's problem (14.22)–(14.25), its Euler equation (14.26), the
intratemporal condition (14.27) and "the usual transversality condition", on a probability
space `(Ω, μ)` with a filtration `ℱ`; `E_t` is Mathlib's conditional expectation `μ[·|ℱ t]`.

* `rb_IsFeasible`: positive consumption, `N_t ∈ [0, 1)`, `K_t ≥ 0`, and the resource constraint
  (14.23) with (14.24), `C_t + K_{t+1} = z_tK_t^αN_t^{1−α} + (1 − δ)K_t`.
* `eq_14_26`: `1/C_t = E_t[β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}]` a.e.;
  `rb_TVC`: `βᵀE[K_{T+1}/C_T] → 0`.
* **Sufficiency** (`rb_planner_suff`, `rb_planner_optimal`): an interior feasible plan
  satisfying (14.26), (14.27) and transversality is optimal: for every feasible adapted
  alternative with the same `K_0`, `∑_{t≤T} βᵗE[u'_t] ≤ ∑_{t≤T} βᵗE[u_t] + βᵀE[K_{T+1}/C_T]`, so
  the expected discounted utility of the alternative is at most that of the plan. The proof
  is the concavity argument (`rb_cd_tangent`, `rb_u_tangent`) with the Euler equation used
  through the pull-out property of `E_t` and a telescoping sum (`rb_suff_core`), which
  `RBEquilibrium` reuses for the household.
* **Non-vacuity** (`rb_bm_solution`): with full depreciation `δ = 1` and a deterministic TFP
  path, `K_{t+1} = αβY_t`, `C_t = (1 − αβ)Y_t`, `N_t = (1 − α)/(1 − α + χ(1 − αβ))` is feasible
  and satisfies (14.26), (14.27), transversality and the integrability hypotheses of
  `rb_planner_suff`, on every probability space.

**Departures.** The book asserts the first-order conditions are satisfied by the optimum; here
the converse (sufficiency, with transversality) is proved in the stochastic setting, and the
necessity of (14.26)–(14.27) is proved for the one-step variations in `RBModel`
(`rb_labour_nec`, `rb_euler_node_nec`). Integrability of the terms involved is assumed
explicitly. The expected discounted utility is the limit of the expected partial sums.
-/

open MeasureTheory Filter Topology

namespace Miao.NeoclassicalGrowth

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The telescoping identity: if `a₀ = 0` and `βa_{t+1} = b_t`, then
`∑_{t≤T} βᵗ(a_t − b_t) = −βᵀb_T`. -/
theorem rb_telescope (β : ℝ) (a b : ℕ → ℝ) (h0 : a 0 = 0) (h : ∀ t, β * a (t + 1) = b t)
    (T : ℕ) : ∑ t ∈ Finset.range (T + 1), β ^ t * (a t - b t) = -β ^ T * b T := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, ← h T]
    ring

/-- The Euler equation through the pull-out property: if `B = E_m[βA]` a.e. and `X` is
`m`-measurable, then `βE[XA] = E[XB]`. -/
theorem rb_integral_euler (μ : Measure Ω) [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {A B X : Ω → ℝ} (β : ℝ) (hX : StronglyMeasurable[m] X)
    (hXA : Integrable (fun ω => X ω * A ω) μ) (hA : Integrable A μ)
    (heul : B =ᵐ[μ] μ[fun ω => β * A ω | m]) :
    β * ∫ ω, X ω * A ω ∂μ = ∫ ω, X ω * B ω ∂μ := by
  have hg : Integrable (fun ω => β * A ω) μ := hA.const_mul β
  have hfg : Integrable (X * fun ω => β * A ω) μ := by
    have := hXA.const_mul β
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hX hfg hg
  have h1 : ∫ ω, X ω * B ω ∂μ = ∫ ω, (X * μ[fun ω => β * A ω | m]) ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [heul] with ω hω
    simp only [Pi.mul_apply, hω]
  rw [h1, ← integral_congr_ae hpull, integral_condExp hm, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply]
  ring

/-- The core of the sufficiency argument (Miao, p. 472, "the usual transversality condition";
cf. Theorem 7.5.2). If the one-period gains satisfy `d_t ≤ A_tΔ_t − B_tΔ_{t+1}`, `Δ₀ = 0`,
`Δ_{t+1}` is `ℱ_t`-measurable and `B_t = E_t[βA_{t+1}]` (the Euler equation), then
`∑_{t≤T} βᵗE[d_t] ≤ −βᵀE[B_TΔ_{T+1}]`. -/
theorem rb_suff_core (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {β : ℝ}
    (hβ : 0 ≤ β) (d A B Δ : ℕ → Ω → ℝ)
    (hd : ∀ t ω, d t ω ≤ A t ω * Δ t ω - B t ω * Δ (t + 1) ω) (hΔ0 : ∀ ω, Δ 0 ω = 0)
    (hΔm : ∀ t, StronglyMeasurable[ℱ t] (Δ (t + 1)))
    (heul : ∀ t, B t =ᵐ[μ] μ[fun ω => β * A (t + 1) ω | ℱ t])
    (hdi : ∀ t, Integrable (d t) μ) (hAΔ : ∀ t, Integrable (fun ω => A t ω * Δ t ω) μ)
    (hBΔ : ∀ t, Integrable (fun ω => B t ω * Δ (t + 1) ω) μ) (hAi : ∀ t, Integrable (A t) μ)
    (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, d t ω ∂μ ≤
      -β ^ T * ∫ ω, B T ω * Δ (T + 1) ω ∂μ := by
  set a : ℕ → ℝ := fun t => ∫ ω, A t ω * Δ t ω ∂μ
  set b : ℕ → ℝ := fun t => ∫ ω, B t ω * Δ (t + 1) ω ∂μ
  have ha0 : a 0 = 0 := by simp [a, hΔ0]
  have hab : ∀ t, β * a (t + 1) = b t := fun t => by
    have h := rb_integral_euler μ (ℱ.le t) β (hΔm t)
      ((hAΔ (t + 1)).congr (Eventually.of_forall fun ω => mul_comm _ _)) (hAi (t + 1)) (heul t)
    simp only [a, b]
    rw [integral_congr_ae (Eventually.of_forall fun ω => mul_comm (A (t + 1) ω) _), h]
    exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have hle : ∀ t, ∫ ω, d t ω ∂μ ≤ a t - b t := fun t => by
    simp only [a, b]
    rw [← integral_sub (hAΔ t) (hBΔ t)]
    exact integral_mono (hdi t) ((hAΔ t).sub (hBΔ t)) fun ω => hd t ω
  calc ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, d t ω ∂μ
      ≤ ∑ t ∈ Finset.range (T + 1), β ^ t * (a t - b t) :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hβ t)
    _ = -β ^ T * b T := rb_telescope β a b ha0 hab T

/-! ### The planner's problem -/

/-- A feasible allocation of the planner (Miao, (14.23)–(14.24), p. 472), with investment
eliminated: `C_t > 0`, `0 ≤ N_t < 1`, `K_t ≥ 0` and
`C_t + K_{t+1} = z_tK_t^αN_t^{1−α} + (1 − δ)K_t`. -/
def rb_IsFeasible (α δ : ℝ) (z C N K : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, 0 < C t ω ∧ 0 ≤ N t ω ∧ N t ω < 1 ∧ 0 ≤ K t ω ∧
    C t ω + K (t + 1) ω = rb_Y α (z t ω) (K t ω) (N t ω) + (1 - δ) * K t ω

/-- The gross return on capital `R_{t} = αz_tK_t^{α−1}N_t^{1−α} + 1 − δ` divided by `C_t`. -/
noncomputable def rb_A (α δ : ℝ) (z C N K : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (rb_MPK α (z t ω) (K t ω) (N t ω) + 1 - δ) / C t ω

/-- Miao, (14.26), p. 472: the Euler equation
`1/C_t = E_t[β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}]` (a.e.). -/
def eq_14_26 (μ : Measure Ω) (ℱ : Filtration ℕ m0) (α β δ : ℝ) (z C N K : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, (fun ω => 1 / C t ω) =ᵐ[μ] μ[fun ω => β * rb_A α δ z C N K (t + 1) ω | ℱ t]

/-- The transversality condition `lim βᵀE[K_{T+1}/C_T] = 0` (Miao, p. 472). -/
def rb_TVC (μ : Measure Ω) (β : ℝ) (C K : ℕ → Ω → ℝ) : Prop :=
  Tendsto (fun T : ℕ => β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ) atTop (𝓝 0)

/-- Expected discounted utility up to date `T` (Miao, (14.22)). -/
noncomputable def rb_value (μ : Measure Ω) (β χ : ℝ) (C N : ℕ → Ω → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ

/-- The pointwise one-period inequality of the planner: if (14.27) holds for the plan,
`u(C'_t, N'_t) − u(C_t, N_t) ≤ A_t(K'_t − K_t) − (K'_{t+1} − K_{t+1})/C_t`. -/
theorem rb_planner_pointwise {α δ χ z C N K C' N' K' K₁ K₁' : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hχ : 0 ≤ χ) (hz : 0 ≤ z) (hC : 0 < C) (hN0 : 0 < N) (hN1 : N < 1) (hK : 0 < K)
    (hC' : 0 < C') (hN0' : 0 ≤ N') (hN1' : N' < 1) (hK' : 0 ≤ K')
    (hres : C + K₁ = rb_Y α z K N + (1 - δ) * K)
    (hres' : C' + K₁' = rb_Y α z K' N' + (1 - δ) * K') (hfoc : eq_14_27 α χ z K C N) :
    rb_u χ C' N' - rb_u χ C N ≤
      (rb_MPK α z K N + 1 - δ) / C * (K' - K) - 1 / C * (K₁' - K₁) := by
  have ht := rb_u_tangent hχ hC hN1 hC' hN1'
  have hY := rb_cd_tangent' hα0 hα1 hz hK hN0 hK' hN0'
  have h1N : 0 < 1 - N := by linarith
  have hw : χ * ((N' - N) / (1 - N)) = rb_MPL α z K N * (N' - N) / C := by
    rw [eq_14_27] at hfoc
    rw [← hfoc]
    field_simp
  have hq : (C' - C) / C ≤ ((rb_MPK α z K N + 1 - δ) * (K' - K) +
      rb_MPL α z K N * (N' - N) - (K₁' - K₁)) / C := by
    apply div_le_div_of_nonneg_right _ hC.le
    linarith
  have : ((rb_MPK α z K N + 1 - δ) * (K' - K) + rb_MPL α z K N * (N' - N) - (K₁' - K₁)) / C =
      (rb_MPK α z K N + 1 - δ) / C * (K' - K) + rb_MPL α z K N * (N' - N) / C -
        1 / C * (K₁' - K₁) := by
    field_simp
  linarith

/-- **Sufficiency of (14.26), (14.27)** (Miao, §14.2, p. 472). Let `(C, N, K)` be feasible with
`K_t > 0`, `N_t ∈ (0, 1)`, adapted (`K_{t+1}` is `ℱ_t`-measurable), satisfying (14.27) at every
date and state and the Euler equation (14.26). Then for every feasible alternative
`(C', N', K')` with `K'_0 = K_0` and `K'_{t+1}` `ℱ_t`-measurable, and every `T`,
`∑_{t≤T} βᵗE[u(C'_t, N'_t)] ≤ ∑_{t≤T} βᵗE[u(C_t, N_t)] + βᵀE[K_{T+1}/C_T]`
(integrability of the terms involved is assumed). -/
theorem rb_planner_suff (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {α β δ χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hχ : 0 ≤ χ)
    {z C N K C' N' K' : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω) (hF : rb_IsFeasible α δ z C N K)
    (hK : ∀ t ω, 0 < K t ω) (hN : ∀ t ω, 0 < N t ω)
    (hfoc : ∀ t ω, eq_14_27 α χ (z t ω) (K t ω) (C t ω) (N t ω))
    (heul : eq_14_26 μ ℱ α β δ z C N K)
    (hKm : ∀ t, StronglyMeasurable[ℱ t] (K (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (C t ω) (N t ω)) μ)
    (hAi : ∀ t, Integrable (rb_A α δ z C N K t) μ)
    (hAK : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K t ω) μ)
    (hBK : ∀ t, Integrable (fun ω => K (t + 1) ω / C t ω) μ)
    (hF' : rb_IsFeasible α δ z C' N' K') (h0 : ∀ ω, K' 0 ω = K 0 ω)
    (hKm' : ∀ t, StronglyMeasurable[ℱ t] (K' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (C' t ω) (N' t ω)) μ)
    (hAK' : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K' t ω) μ)
    (hBK' : ∀ t, Integrable (fun ω => K' (t + 1) ω / C t ω) μ) (T : ℕ) :
    rb_value μ β χ C' N' T ≤
      rb_value μ β χ C N T + β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ := by
  set d : ℕ → Ω → ℝ := fun t ω => rb_u χ (C' t ω) (N' t ω) - rb_u χ (C t ω) (N t ω)
  set Δ : ℕ → Ω → ℝ := fun t ω => K' t ω - K t ω
  set B : ℕ → Ω → ℝ := fun t ω => 1 / C t ω
  have hBΔ : ∀ t, Integrable (fun ω => B t ω * Δ (t + 1) ω) μ := fun t =>
    ((hBK' t).sub (hBK t)).congr (Eventually.of_forall fun ω => by
      simp only [B, Δ, Pi.sub_apply]; ring)
  have hcore := rb_suff_core μ ℱ hβ d (rb_A α δ z C N K) B Δ
    (fun t ω => by
      obtain ⟨hC, hN0, hN1, -, hres⟩ := hF t ω
      obtain ⟨hC', hN0', hN1', hK', hres'⟩ := hF' t ω
      exact rb_planner_pointwise hα0 hα1 hχ (hz t ω) hC (hN t ω) hN1 (hK t ω) hC' hN0'
        hN1' hK' hres hres' (hfoc t ω))
    (fun ω => by simp [Δ, h0]) (fun t => (hKm' t).sub (hKm t))
    (fun t => heul t) (fun t => (hui' t).sub (hui t))
    (fun t => ((hAK' t).sub (hAK t)).congr (Eventually.of_forall fun ω => by
      simp only [Δ, Pi.sub_apply]; ring)) hBΔ hAi T
  have hsplit : ∀ t, ∫ ω, d t ω ∂μ =
      ∫ ω, rb_u χ (C' t ω) (N' t ω) ∂μ - ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ :=
    fun t => integral_sub (hui' t) (hui t)
  have hlast : -β ^ T * ∫ ω, B T ω * Δ (T + 1) ω ∂μ ≤
      β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ := by
    have hint : ∫ ω, B T ω * Δ (T + 1) ω ∂μ =
        ∫ ω, K' (T + 1) ω / C T ω ∂μ - ∫ ω, K (T + 1) ω / C T ω ∂μ := by
      rw [← integral_sub (hBK' T) (hBK T)]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [B, Δ]; ring)
    have hpos : 0 ≤ ∫ ω, K' (T + 1) ω / C T ω ∂μ :=
      integral_nonneg fun ω => div_nonneg (hF' (T + 1) ω).2.2.2.1 (hF T ω).1.le
    rw [hint]
    have := pow_nonneg hβ T
    nlinarith
  simp only [hsplit] at hcore
  unfold rb_value
  have hs : ∑ t ∈ Finset.range (T + 1), β ^ t * (∫ ω, rb_u χ (C' t ω) (N' t ω) ∂μ -
      ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ) =
      ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (C' t ω) (N' t ω) ∂μ -
        ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (C t ω) (N t ω) ∂μ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hs] at hcore
  linarith

/-- **Optimality** (Miao, §14.2, p. 472): under the hypotheses of `rb_planner_suff` and the
transversality condition, if the expected discounted utilities of the plan and of the
alternative converge (to `V` and `V'`), then `V' ≤ V`. -/
theorem rb_planner_optimal (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {α β δ χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hχ : 0 ≤ χ)
    {z C N K C' N' K' : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω) (hF : rb_IsFeasible α δ z C N K)
    (hK : ∀ t ω, 0 < K t ω) (hN : ∀ t ω, 0 < N t ω)
    (hfoc : ∀ t ω, eq_14_27 α χ (z t ω) (K t ω) (C t ω) (N t ω))
    (heul : eq_14_26 μ ℱ α β δ z C N K) (htvc : rb_TVC μ β C K)
    (hKm : ∀ t, StronglyMeasurable[ℱ t] (K (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (C t ω) (N t ω)) μ)
    (hAi : ∀ t, Integrable (rb_A α δ z C N K t) μ)
    (hAK : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K t ω) μ)
    (hBK : ∀ t, Integrable (fun ω => K (t + 1) ω / C t ω) μ)
    (hF' : rb_IsFeasible α δ z C' N' K') (h0 : ∀ ω, K' 0 ω = K 0 ω)
    (hKm' : ∀ t, StronglyMeasurable[ℱ t] (K' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (C' t ω) (N' t ω)) μ)
    (hAK' : ∀ t, Integrable (fun ω => rb_A α δ z C N K t ω * K' t ω) μ)
    (hBK' : ∀ t, Integrable (fun ω => K' (t + 1) ω / C t ω) μ) {V V' : ℝ}
    (hV : Tendsto (rb_value μ β χ C N) atTop (𝓝 V))
    (hV' : Tendsto (rb_value μ β χ C' N') atTop (𝓝 V')) : V' ≤ V := by
  have hlim : Tendsto (fun T => rb_value μ β χ C N T + β ^ T * ∫ ω, K (T + 1) ω / C T ω ∂μ)
      atTop (𝓝 (V + 0)) := hV.add htvc
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' hV' hlim fun T =>
    rb_planner_suff μ ℱ hα0 hα1 hβ hχ hz hF hK hN hfoc heul hKm hui hAi hAK hBK hF' h0 hKm'
      hui' hAK' hBK' T

/-! ### A concrete solution: full depreciation -/

/-- Hours in the full-depreciation solution, `N = (1 − α)/(1 − α + χ(1 − αβ))`. -/
noncomputable def rb_bmN (α β χ : ℝ) : ℝ := (1 - α) / (1 - α + χ * (1 - α * β))

/-- Capital in the full-depreciation solution: `K_{t+1} = αβz_tK_t^αN^{1−α}`. -/
noncomputable def rb_bmK (α β χ : ℝ) (zs : ℕ → ℝ) (k0 : ℝ) : ℕ → ℝ
  | 0 => k0
  | t + 1 => α * β * rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)

/-- Consumption in the full-depreciation solution: `C_t = (1 − αβ)z_tK_t^αN^{1−α}`. -/
noncomputable def rb_bmC (α β χ : ℝ) (zs : ℕ → ℝ) (k0 : ℝ) (t : ℕ) : ℝ :=
  (1 - α * β) * rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)

theorem rb_bmN_mem {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hχ : 0 < χ) : 0 < rb_bmN α β χ ∧ rb_bmN α β χ < 1 := by
  have h1 : 0 < 1 - α * β := by nlinarith
  have h2 : 0 < χ * (1 - α * β) := mul_pos hχ h1
  unfold rb_bmN
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]
    linarith

theorem rb_bmK_pos {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hχ : 0 < χ) {zs : ℕ → ℝ} (hzs : ∀ t, 0 < zs t) {k0 : ℝ} (hk0 : 0 < k0) (t : ℕ) :
    0 < rb_bmK α β χ zs k0 t := by
  induction t with
  | zero => exact hk0
  | succ t ih =>
    have := rb_Y_pos (α := α) (hzs t) ih (rb_bmN_mem hα0 hα1 hβ1 hχ).1
    simp only [rb_bmK]
    positivity

/-- **The full-depreciation solution** (Miao, §14.2 with `δ = 1`; Long and Plosser (1983)).
With `δ = 1` and a deterministic TFP path `z_t > 0`, the allocation `K_{t+1} = αβY_t`,
`C_t = (1 − αβ)Y_t`, `N_t = (1 − α)/(1 − α + χ(1 − αβ))` (constant random variables on any
probability space) is feasible, interior, adapted, satisfies (14.27) and (14.26), the
transversality condition, and all the integrability hypotheses of `rb_planner_suff`. In
particular those hypotheses are satisfiable, and by `rb_planner_optimal` this allocation is
optimal. -/
theorem rb_bm_solution (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hχ : 0 < χ)
    {zs : ℕ → ℝ} (hzs : ∀ t, 0 < zs t) {k0 : ℝ} (hk0 : 0 < k0) :
    let z : ℕ → Ω → ℝ := fun t _ => zs t
    let C : ℕ → Ω → ℝ := fun t _ => rb_bmC α β χ zs k0 t
    let N : ℕ → Ω → ℝ := fun _ _ => rb_bmN α β χ
    let K : ℕ → Ω → ℝ := fun t _ => rb_bmK α β χ zs k0 t
    rb_IsFeasible α 1 z C N K ∧ (∀ t ω, 0 < K t ω) ∧ (∀ t ω, 0 < N t ω) ∧
      (∀ t ω, eq_14_27 α χ (z t ω) (K t ω) (C t ω) (N t ω)) ∧ eq_14_26 μ ℱ α β 1 z C N K ∧
      rb_TVC μ β C K ∧ (∀ t, StronglyMeasurable[ℱ t] (K (t + 1))) ∧
      (∀ t, Integrable (fun ω => rb_u χ (C t ω) (N t ω)) μ) ∧
      (∀ t, Integrable (rb_A α 1 z C N K t) μ) ∧
      (∀ t, Integrable (fun ω => rb_A α 1 z C N K t ω * K t ω) μ) ∧
      (∀ t, Integrable (fun ω => K (t + 1) ω / C t ω) μ) := by
  intro z C N K
  obtain ⟨hn0, hn1⟩ := rb_bmN_mem hα0 hα1 hβ1 hχ
  have hab : 0 < 1 - α * β := by nlinarith
  have hKp := rb_bmK_pos hα0 hα1 hβ0 hβ1 hχ hzs hk0
  have hY : ∀ t, 0 < rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ) := fun t =>
    rb_Y_pos (hzs t) (hKp t) hn0
  have hCp : ∀ t, 0 < rb_bmC α β χ zs k0 t := fun t => mul_pos hab (hY t)
  refine ⟨fun t ω => ⟨hCp t, hn0.le, hn1, (hKp t).le, ?_⟩, fun t ω => hKp t, fun t ω => hn0,
    fun t ω => ?_, fun t => ?_, ?_, fun t => stronglyMeasurable_const,
    fun t => by simp only [C, N]; exact integrable_const _,
    fun t => by simp only [C, N, K, z]; exact integrable_const _,
    fun t => by simp only [rb_A, C, N, K, z]; exact integrable_const _,
    fun t => by simp only [C, K]; exact integrable_const _⟩
  · simp only [C, K, z, N, rb_bmC, rb_bmK]
    ring
  · simp only [eq_14_27, C, K, z, N]
    rw [rb_MPL_eq _ _ _ hn0, rb_bmC]
    have h1n : 0 < 1 - rb_bmN α β χ := by linarith
    rw [div_eq_div_iff h1n.ne' hn0.ne']
    have hden : 0 < 1 - α + χ * (1 - α * β) := by nlinarith
    simp only [rb_bmN]
    field_simp
    ring
  · have hc : (fun ω : Ω => β * rb_A α 1 z C N K (t + 1) ω) =
        fun _ => 1 / rb_bmC α β χ zs k0 t := by
      funext ω
      simp only [rb_A, C, K, z, N]
      rw [rb_MPK_eq _ _ (hKp (t + 1)), rb_bmC, rb_bmC]
      have hY1 := hY (t + 1)
      have := hY t
      set Y1 := rb_Y α (zs (t + 1)) (rb_bmK α β χ zs k0 (t + 1)) (rb_bmN α β χ)
      set Y0 := rb_Y α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)
      have hK1 : rb_bmK α β χ zs k0 (t + 1) = α * β * Y0 := rfl
      rw [hK1]
      field_simp
      ring
    rw [hc, condExp_const (ℱ.le t)]
  · simp only [rb_TVC, K, C, integral_const, smul_eq_mul, probReal_univ, one_mul]
    have hr : ∀ T : ℕ, β ^ T * (rb_bmK α β χ zs k0 (T + 1) / rb_bmC α β χ zs k0 T) =
        β ^ T * (α * β / (1 - α * β)) := fun T => by
      congr 1
      rw [rb_bmC]
      simp only [rb_bmK]
      have := hY T
      field_simp
    simp only [hr]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (α * β / (1 - α * β))
    simpa using this

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The decentralised equilibrium of the basic RBC model

Miao, §14.2, p. 472: "In a decentralized equilibrium in which households own capital and make
real investment, the rental rate and the wage rate are given by
`R_kt = αz_tK_t^{α−1}N_t^{1−α}` and `w_t = (1 − α)z_tK_t^αN_t^{−α}`", and "our previous analysis
regarding Pareto optimality and decentralized competitive equilibrium still applies to the
stochastic case" (the sequential equilibrium of §14.1, pp. 460–461, with population and
technology growth switched off).

* The household's budget `c_t + k_{t+1} = (R_kt + 1 − δ)k_t + w_tn_t + Π_t`
  (`rb_IsHHFeasible`), its Euler equation `1/c_t = E_t[β(R_{k,t+1} + 1 − δ)/c_{t+1}]`
  (`rb_HHEuler`) and labour supply (14.36) `χc_t/(1 − n_t) = w_t`.
* **Household sufficiency** (`rb_household_suff`, `rb_household_optimal`): with transversality,
  these conditions make the plan optimal for the household at the given prices.
* A sequential competitive equilibrium (`rb_IsSCE`): the household conditions, the firm's
  profit maximisation at every date and state, and profits paid to the household; markets clear
  with a unit population, so the firm's inputs are `(k_t, n_t)`.
* **Equivalence** (`rb_sce_iff`): a positive allocation with prices `(R_k, w, Π)` is a sequential
  competitive equilibrium iff the prices are the marginal products with zero profits and the
  allocation satisfies the planner's conditions: feasibility, (14.26) and (14.27). Hence an
  equilibrium allocation satisfying transversality is optimal for the planner
  (`rb_sce_optimal`, first welfare theorem), and the planner's allocation decentralises
  (second welfare theorem, the `←` direction).
* Non-vacuity: the full-depreciation solution with marginal-product prices is an equilibrium
  (`rb_bm_sce`).
-/

open MeasureTheory Filter Topology

namespace Miao.NeoclassicalGrowth

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The household's feasible plans (Miao, p. 460): `c_t > 0`, `0 ≤ n_t < 1`, `k_t ≥ 0` and the
budget `c_t + k_{t+1} = (R_kt + 1 − δ)k_t + w_tn_t + Π_t` (investment eliminated). -/
def rb_IsHHFeasible (δ : ℝ) (Rk w Pr c n k : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, 0 < c t ω ∧ 0 ≤ n t ω ∧ n t ω < 1 ∧ 0 ≤ k t ω ∧
    c t ω + k (t + 1) ω = (Rk t ω + 1 - δ) * k t ω + w t ω * n t ω + Pr t ω

/-- The household's Euler equation `1/c_t = E_t[β(R_{k,t+1} + 1 − δ)/c_{t+1}]` (a.e.). -/
def rb_HHEuler (μ : Measure Ω) (ℱ : Filtration ℕ m0) (β δ : ℝ) (Rk c : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun ω => 1 / c t ω) =ᵐ[μ] μ[fun ω => β * ((Rk (t + 1) ω + 1 - δ) / c (t + 1) ω) | ℱ t]

/-- The household's one-period inequality: with labour supply `χc/(1 − n) = w`,
`u(c', n') − u(c, n) ≤ (R_k + 1 − δ)/c·(k' − k) − (k'_1 − k_1)/c`. -/
theorem rb_household_pointwise {δ χ Rk w Pr c n k c' n' k' k₁ k₁' : ℝ} (hχ : 0 ≤ χ)
    (hc : 0 < c) (hn1 : n < 1) (hc' : 0 < c') (hn1' : n' < 1)
    (hb : c + k₁ = (Rk + 1 - δ) * k + w * n + Pr)
    (hb' : c' + k₁' = (Rk + 1 - δ) * k' + w * n' + Pr) (hls : χ * c / (1 - n) = w) :
    rb_u χ c' n' - rb_u χ c n ≤ (Rk + 1 - δ) / c * (k' - k) - 1 / c * (k₁' - k₁) := by
  have ht := rb_u_tangent hχ hc hn1 hc' hn1'
  have h1n : 0 < 1 - n := by linarith
  have hw : χ * ((n' - n) / (1 - n)) = w * (n' - n) / c := by
    rw [← hls]
    field_simp
  have : (c' - c) / c = (Rk + 1 - δ) / c * (k' - k) + w * (n' - n) / c - 1 / c * (k₁' - k₁) := by
    have hcc : c' - c = (Rk + 1 - δ) * (k' - k) + w * (n' - n) - (k₁' - k₁) := by linarith
    rw [hcc]
    field_simp
  linarith

/-- **Household sufficiency** (Miao, p. 460 and p. 472): a feasible plan with `n_t > 0`,
`k_{t+1}` `ℱ_t`-measurable, labour supply (14.36) and the household Euler equation satisfies,
against every feasible adapted alternative with the same `k_0`,
`∑_{t≤T} βᵗE[u'_t] ≤ ∑_{t≤T} βᵗE[u_t] + βᵀE[k_{T+1}/c_T]`. -/
theorem rb_household_suff (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {β δ χ : ℝ} (hβ : 0 ≤ β) (hχ : 0 ≤ χ) {Rk w Pr c n k c' n' k' : ℕ → Ω → ℝ}
    (hF : rb_IsHHFeasible δ Rk w Pr c n k)
    (hls : ∀ t ω, χ * c t ω / (1 - n t ω) = w t ω) (heul : rb_HHEuler μ ℱ β δ Rk c)
    (hkm : ∀ t, StronglyMeasurable[ℱ t] (k (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (c t ω) (n t ω)) μ)
    (hAi : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω) μ)
    (hAk : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k t ω) μ)
    (hBk : ∀ t, Integrable (fun ω => k (t + 1) ω / c t ω) μ)
    (hF' : rb_IsHHFeasible δ Rk w Pr c' n' k') (h0 : ∀ ω, k' 0 ω = k 0 ω)
    (hkm' : ∀ t, StronglyMeasurable[ℱ t] (k' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (c' t ω) (n' t ω)) μ)
    (hAk' : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k' t ω) μ)
    (hBk' : ∀ t, Integrable (fun ω => k' (t + 1) ω / c t ω) μ) (T : ℕ) :
    rb_value μ β χ c' n' T ≤
      rb_value μ β χ c n T + β ^ T * ∫ ω, k (T + 1) ω / c T ω ∂μ := by
  set d : ℕ → Ω → ℝ := fun t ω => rb_u χ (c' t ω) (n' t ω) - rb_u χ (c t ω) (n t ω)
  set Δ : ℕ → Ω → ℝ := fun t ω => k' t ω - k t ω
  set A : ℕ → Ω → ℝ := fun t ω => (Rk t ω + 1 - δ) / c t ω
  set B : ℕ → Ω → ℝ := fun t ω => 1 / c t ω
  have hBΔ : ∀ t, Integrable (fun ω => B t ω * Δ (t + 1) ω) μ := fun t =>
    ((hBk' t).sub (hBk t)).congr (Eventually.of_forall fun ω => by
      simp only [B, Δ, Pi.sub_apply]; ring)
  have hcore := rb_suff_core μ ℱ hβ d A B Δ
    (fun t ω => by
      obtain ⟨hc, -, hn1, -, hb⟩ := hF t ω
      obtain ⟨hc', -, hn1', -, hb'⟩ := hF' t ω
      exact rb_household_pointwise hχ hc hn1 hc' hn1' hb hb' (hls t ω))
    (fun ω => by simp [Δ, h0]) (fun t => (hkm' t).sub (hkm t))
    (fun t => heul t) (fun t => (hui' t).sub (hui t))
    (fun t => ((hAk' t).sub (hAk t)).congr (Eventually.of_forall fun ω => by
      simp only [A, Δ, Pi.sub_apply]; ring)) hBΔ hAi T
  have hsplit : ∀ t, ∫ ω, d t ω ∂μ =
      ∫ ω, rb_u χ (c' t ω) (n' t ω) ∂μ - ∫ ω, rb_u χ (c t ω) (n t ω) ∂μ :=
    fun t => integral_sub (hui' t) (hui t)
  have hlast : -β ^ T * ∫ ω, B T ω * Δ (T + 1) ω ∂μ ≤
      β ^ T * ∫ ω, k (T + 1) ω / c T ω ∂μ := by
    have hint : ∫ ω, B T ω * Δ (T + 1) ω ∂μ =
        ∫ ω, k' (T + 1) ω / c T ω ∂μ - ∫ ω, k (T + 1) ω / c T ω ∂μ := by
      rw [← integral_sub (hBk' T) (hBk T)]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [B, Δ]; ring)
    have hpos : 0 ≤ ∫ ω, k' (T + 1) ω / c T ω ∂μ :=
      integral_nonneg fun ω => div_nonneg (hF' (T + 1) ω).2.2.2.1 (hF T ω).1.le
    rw [hint]
    have := pow_nonneg hβ T
    nlinarith
  simp only [hsplit] at hcore
  unfold rb_value
  have hs : ∑ t ∈ Finset.range (T + 1), β ^ t * (∫ ω, rb_u χ (c' t ω) (n' t ω) ∂μ -
      ∫ ω, rb_u χ (c t ω) (n t ω) ∂μ) =
      ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (c' t ω) (n' t ω) ∂μ -
        ∑ t ∈ Finset.range (T + 1), β ^ t * ∫ ω, rb_u χ (c t ω) (n t ω) ∂μ := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hs] at hcore
  linarith

/-- **Household optimality**: under the hypotheses of `rb_household_suff` and the
transversality condition `βᵀE[k_{T+1}/c_T] → 0`, if the expected discounted utilities converge
(to `V`, `V'`), then `V' ≤ V`. -/
theorem rb_household_optimal (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {β δ χ : ℝ} (hβ : 0 ≤ β) (hχ : 0 ≤ χ) {Rk w Pr c n k c' n' k' : ℕ → Ω → ℝ}
    (hF : rb_IsHHFeasible δ Rk w Pr c n k)
    (hls : ∀ t ω, χ * c t ω / (1 - n t ω) = w t ω) (heul : rb_HHEuler μ ℱ β δ Rk c)
    (htvc : rb_TVC μ β c k) (hkm : ∀ t, StronglyMeasurable[ℱ t] (k (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (c t ω) (n t ω)) μ)
    (hAi : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω) μ)
    (hAk : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k t ω) μ)
    (hBk : ∀ t, Integrable (fun ω => k (t + 1) ω / c t ω) μ)
    (hF' : rb_IsHHFeasible δ Rk w Pr c' n' k') (h0 : ∀ ω, k' 0 ω = k 0 ω)
    (hkm' : ∀ t, StronglyMeasurable[ℱ t] (k' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (c' t ω) (n' t ω)) μ)
    (hAk' : ∀ t, Integrable (fun ω => (Rk t ω + 1 - δ) / c t ω * k' t ω) μ)
    (hBk' : ∀ t, Integrable (fun ω => k' (t + 1) ω / c t ω) μ) {V V' : ℝ}
    (hV : Tendsto (rb_value μ β χ c n) atTop (𝓝 V))
    (hV' : Tendsto (rb_value μ β χ c' n') atTop (𝓝 V')) : V' ≤ V := by
  have hlim : Tendsto (fun T => rb_value μ β χ c n T + β ^ T * ∫ ω, k (T + 1) ω / c T ω ∂μ)
      atTop (𝓝 (V + 0)) := hV.add htvc
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' hV' hlim fun T =>
    rb_household_suff μ ℱ hβ hχ hF hls heul hkm hui hAi hAk hBk hF' h0 hkm' hui' hAk' hBk' T

/-- A sequential competitive equilibrium of the basic RBC model (Miao, pp. 460–461 and
p. 472): the household's budget, labour supply (14.36) and Euler equation hold, the firm
maximises profit `z_tK^αN^{1−α} − R_ktK − w_tN` at `(k_t, n_t)` over all `K, N ≥ 0`, and the
household receives the profit `Π_t`. -/
def rb_IsSCE (μ : Measure Ω) (ℱ : Filtration ℕ m0) (α β δ χ : ℝ)
    (z c n k Rk w Pr : ℕ → Ω → ℝ) : Prop :=
  rb_IsHHFeasible δ Rk w Pr c n k ∧ (∀ t ω, χ * c t ω / (1 - n t ω) = w t ω) ∧
    rb_HHEuler μ ℱ β δ Rk c ∧
    (∀ t ω K' N', 0 ≤ K' → 0 ≤ N' → rb_profit α (z t ω) (Rk t ω) (w t ω) K' N' ≤
      rb_profit α (z t ω) (Rk t ω) (w t ω) (k t ω) (n t ω)) ∧
    (∀ t ω, Pr t ω = rb_profit α (z t ω) (Rk t ω) (w t ω) (k t ω) (n t ω))

/-- **Equivalence of the decentralised equilibrium and the planner's conditions** (Miao,
p. 472). For a positive allocation (`k_t, n_t > 0`), `(c, n, k)` with prices `(R_k, w, Π)` is a
sequential competitive equilibrium iff `R_kt = αz_tk_t^{α−1}n_t^{1−α}`,
`w_t = (1 − α)z_tk_t^αn_t^{−α}`, `Π_t = 0`, and the allocation is feasible for the planner and
satisfies (14.26) and (14.27). -/
theorem rb_sce_iff (μ : Measure Ω) (ℱ : Filtration ℕ m0) {α β δ χ : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {z c n k Rk w Pr : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω)
    (hk : ∀ t ω, 0 < k t ω) (hn : ∀ t ω, 0 < n t ω) :
    rb_IsSCE μ ℱ α β δ χ z c n k Rk w Pr ↔
      ((∀ t ω, Rk t ω = rb_MPK α (z t ω) (k t ω) (n t ω)) ∧
        (∀ t ω, w t ω = rb_MPL α (z t ω) (k t ω) (n t ω)) ∧ (∀ t ω, Pr t ω = 0)) ∧
      rb_IsFeasible α δ z c n k ∧ (∀ t ω, eq_14_27 α χ (z t ω) (k t ω) (c t ω) (n t ω)) ∧
      eq_14_26 μ ℱ α β δ z c n k := by
  constructor
  · rintro ⟨hb, hls, heul, hfirm, hpr⟩
    have hp : ∀ t ω, Rk t ω = rb_MPK α (z t ω) (k t ω) (n t ω) ∧
        w t ω = rb_MPL α (z t ω) (k t ω) (n t ω) := fun t ω =>
      rb_firm_foc (hk t ω) (hn t ω) (hfirm t ω)
    have hRk : Rk = fun t ω => rb_MPK α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => (hp t ω).1
    have hw : w = fun t ω => rb_MPL α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => (hp t ω).2
    subst hRk hw
    have hPr : ∀ t ω, Pr t ω = 0 := fun t ω => by
      rw [hpr t ω]
      exact (rb_firm_optimal hα0 hα1 (hz t ω) (hk t ω) (hn t ω)).1
    refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl, hPr⟩, fun t ω => ?_, fun t ω => hls t ω,
      fun t => heul t⟩
    obtain ⟨hc, hn0, hn1, hk0, hbud⟩ := hb t ω
    refine ⟨hc, hn0, hn1, hk0, ?_⟩
    rw [hbud, hPr t ω, ← rb_euler_thm α (z t ω) (hk t ω) (hn t ω)]
    ring
  · rintro ⟨⟨hRk, hw, hPr⟩, hF, hfoc, heul⟩
    have hRk' : Rk = fun t ω => rb_MPK α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => hRk t ω
    have hw' : w = fun t ω => rb_MPL α (z t ω) (k t ω) (n t ω) :=
      funext fun t => funext fun ω => hw t ω
    subst hRk' hw'
    refine ⟨fun t ω => ?_, fun t ω => hfoc t ω, fun t => heul t, fun t ω K' N' hK' hN' => ?_,
      fun t ω => ?_⟩
    · obtain ⟨hc, hn0, hn1, hk0, hres⟩ := hF t ω
      refine ⟨hc, hn0, hn1, hk0, ?_⟩
      rw [hres, hPr t ω, ← rb_euler_thm α (z t ω) (hk t ω) (hn t ω)]
      ring
    · obtain ⟨h1, h2⟩ := rb_firm_optimal hα0 hα1 (hz t ω) (hk t ω) (hn t ω)
      rw [h1]
      exact h2 K' N' hK' hN'
    · rw [hPr t ω, (rb_firm_optimal hα0 hα1 (hz t ω) (hk t ω) (hn t ω)).1]

/-- **First welfare theorem** (Miao, p. 472): an equilibrium allocation with positive capital
and hours satisfying transversality (and the integrability hypotheses) is optimal for the
planner. -/
theorem rb_sce_optimal (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0)
    {α β δ χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β) (hχ : 0 ≤ χ)
    {z c n k Rk w Pr C' N' K' : ℕ → Ω → ℝ} (hz : ∀ t ω, 0 ≤ z t ω)
    (hk : ∀ t ω, 0 < k t ω) (hn : ∀ t ω, 0 < n t ω)
    (hE : rb_IsSCE μ ℱ α β δ χ z c n k Rk w Pr) (htvc : rb_TVC μ β c k)
    (hkm : ∀ t, StronglyMeasurable[ℱ t] (k (t + 1)))
    (hui : ∀ t, Integrable (fun ω => rb_u χ (c t ω) (n t ω)) μ)
    (hAi : ∀ t, Integrable (rb_A α δ z c n k t) μ)
    (hAK : ∀ t, Integrable (fun ω => rb_A α δ z c n k t ω * k t ω) μ)
    (hBK : ∀ t, Integrable (fun ω => k (t + 1) ω / c t ω) μ)
    (hF' : rb_IsFeasible α δ z C' N' K') (h0 : ∀ ω, K' 0 ω = k 0 ω)
    (hKm' : ∀ t, StronglyMeasurable[ℱ t] (K' (t + 1)))
    (hui' : ∀ t, Integrable (fun ω => rb_u χ (C' t ω) (N' t ω)) μ)
    (hAK' : ∀ t, Integrable (fun ω => rb_A α δ z c n k t ω * K' t ω) μ)
    (hBK' : ∀ t, Integrable (fun ω => K' (t + 1) ω / c t ω) μ) {V V' : ℝ}
    (hV : Tendsto (rb_value μ β χ c n) atTop (𝓝 V))
    (hV' : Tendsto (rb_value μ β χ C' N') atTop (𝓝 V')) : V' ≤ V := by
  obtain ⟨-, hF, hfoc, heul⟩ := (rb_sce_iff μ ℱ hα0 hα1 hz hk hn).1 hE
  exact rb_planner_optimal μ ℱ hα0 hα1 hβ hχ hz hF hk hn hfoc heul htvc hkm hui hAi hAK hBK
    hF' h0 hKm' hui' hAK' hBK' hV hV'

/-- Non-vacuity of `rb_IsSCE`: the full-depreciation solution of `rb_bm_solution` with the
marginal-product prices and zero profit is a sequential competitive equilibrium. -/
theorem rb_bm_sce (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {α β χ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hχ : 0 < χ)
    {zs : ℕ → ℝ} (hzs : ∀ t, 0 < zs t) {k0 : ℝ} (hk0 : 0 < k0) :
    rb_IsSCE μ ℱ α β 1 χ (fun t _ => zs t) (fun t _ => rb_bmC α β χ zs k0 t)
      (fun _ _ => rb_bmN α β χ) (fun t _ => rb_bmK α β χ zs k0 t)
      (fun t _ => rb_MPK α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ))
      (fun t _ => rb_MPL α (zs t) (rb_bmK α β χ zs k0 t) (rb_bmN α β χ)) (fun _ _ => 0) := by
  obtain ⟨hF, hK, hN, hfoc, heul, -⟩ :=
    rb_bm_solution (Ω := Ω) μ ℱ hα0 hα1 hβ0 hβ1 hχ hzs hk0
  exact (rb_sce_iff μ ℱ hα0 hα1 (fun t _ => (hzs t).le) hK hN).2
    ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, hF, hfoc, heul⟩

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The nonstochastic steady state of the basic RBC model

Miao, §14.2, pp. 473–474, "Steady State" and "Calibration". With `z_t = z̄` constant
(the book takes `z̄ = 1`; a general `z̄ > 0` is used for the permanent TFP shock, p. 484) and
`ρ_k = 1/β − (1 − δ) > 0`:

* The steady-state Euler equation `1 = β(αK^{α−1}N^{1−α} + 1 − δ)` holds iff
  `K/N = (z̄α/ρ_k)^{1/(1−α)}` (`rb_ss_euler`; the book's display with `z̄ = 1`, `rb_ss_KN`).
* Factor prices `R_k = αY/K = α(K/N)^{α−1}`, `w = (1 − α)(K/N)^α` (`rb_ss_prices`);
  `I = δK = δ(K/N)N`, `Y = (K/N)^αN` (`rb_ss_IY_levels`); the ratios `Y/K = ρ_k/α`,
  `I/Y = δα/ρ_k`, `C/Y = 1 − δα/ρ_k` (`rb_ss_ratios`).
* (14.28) `χ = (1 − α)(K/N)^α(1 − N)/C` (`eq_14_28`), in closed form
  `χ = (1 − α)(1 − N)/(N(1 − δα/ρ_k))` (`rb_ss_chi`); the map `N ↦ χ` is a strictly decreasing
  bijection of `(0, 1)` onto `(0, ∞)` with inverse `N = (1 − α)/(1 − α + χs_c)`
  (`rb_ss_N_iff`, `rb_ss_N_mem`, `rb_ss_chi_strictAnti`): "there is a one-to-one mapping between
  `χ` and `N`". For given `χ` the steady state exists and is unique (`rb_ss_exists_unique`).
* Calibration (p. 474): with `α = 0.33`, `β = 0.99`, `δ = 0.025`, `N = 0.33`, the exact value
  is `χ = 623971/350889 ≈ 1.778` (`rb_calib_chi`); the printed `χ = 1.75` is not what (14.28)
  gives for these parameters (`rb_calib_chi_ne`).
* A permanent TFP change: hours do not depend on `z̄`, and `K`, `Y`, `I`, `C`, `w` scale with
  `z̄^{1/(1−α)}` (`rb_ss_permanent`), so their log changes are `ln z̄/(1 − α)`.
-/

namespace Miao.NeoclassicalGrowth

open Real

/-- `ρ_k = 1/β − (1 − δ)`, the steady-state rental rate. -/
noncomputable def rb_rk (β δ : ℝ) : ℝ := 1 / β - (1 - δ)

/-- The steady-state capital–labour ratio `(z̄α/ρ_k)^{1/(1−α)}` (Miao, p. 473 with `z̄ = 1`). -/
noncomputable def rb_kn (α β δ z : ℝ) : ℝ := (z * α / rb_rk β δ) ^ (1 - α)⁻¹

/-- The steady-state consumption share `s_c = C/Y = 1 − δα/ρ_k`. -/
noncomputable def rb_sc (α β δ : ℝ) : ℝ := 1 - δ * α / rb_rk β δ

theorem rb_rk_pos {β δ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ) : 0 < rb_rk β δ := by
  have : 1 < 1 / β := by rw [lt_one_div (by norm_num) hβ0]; simpa using hβ1
  unfold rb_rk
  linarith

theorem rb_sc_pos {α β δ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 ≤ δ) :
    0 < rb_sc α β δ := by
  have hr := rb_rk_pos hβ0 hβ1 hδ0
  have : 1 < 1 / β := by rw [lt_one_div (by norm_num) hβ0]; simpa using hβ1
  unfold rb_sc
  rw [sub_pos, div_lt_one hr]
  unfold rb_rk
  nlinarith

theorem rb_sc_lt_one {α β δ : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ) :
    rb_sc α β δ < 1 := by
  have hr := rb_rk_pos hβ0 hβ1 hδ0.le
  unfold rb_sc
  have : 0 < δ * α / rb_rk β δ := by positivity
  linarith

theorem rb_kn_pos {α β δ z : ℝ} (hα0 : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hz : 0 < z) : 0 < rb_kn α β δ z := by
  have := rb_rk_pos hβ0 hβ1 hδ
  unfold rb_kn
  positivity

theorem rb_kn_pow {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) : rb_kn α β δ z ^ (1 - α) = z * α / rb_rk β δ := by
  have := rb_rk_pos hβ0 hβ1 hδ
  unfold rb_kn
  exact Real.rpow_inv_rpow (by positivity) (by linarith)

/-- Output and marginal products in terms of `K/N`: `MPK = αz(K/N)^{α−1}`. -/
theorem rb_MPK_ratio (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPK α z K N = α * z * (K / N) ^ (α - 1) := by
  rw [rb_MPK, Real.div_rpow hK.le hN.le, show 1 - α = -(α - 1) by ring,
    Real.rpow_neg hN.le]
  field_simp

theorem rb_MPL_ratio (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPL α z K N = (1 - α) * z * (K / N) ^ α := by
  rw [rb_MPL, Real.div_rpow hK.le hN.le, Real.rpow_neg hN.le]
  field_simp

theorem rb_Y_ratio (α z : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_Y α z K N = z * (K / N) ^ α * N := by
  rw [rb_Y, Real.div_rpow hK.le hN.le, Real.rpow_sub hN, Real.rpow_one]
  have := Real.rpow_pos_of_pos hN α
  field_simp

/-- At the steady-state ratio the marginal product of capital is `ρ_k`. -/
theorem rb_MPK_kn {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN : 0 < N) :
    rb_MPK α z (rb_kn α β δ z * N) N = rb_rk β δ := by
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hr := rb_rk_pos hβ0 hβ1 hδ
  rw [rb_MPK_ratio α z (by positivity) hN, mul_div_cancel_right₀ _ hN.ne',
    show α - 1 = -(1 - α) by ring, Real.rpow_neg hk.le, rb_kn_pow hα0 hα1 hβ0 hβ1 hδ hz]
  field_simp

/-- **The steady-state Euler equation** (Miao, p. 473): for `K, N, z̄ > 0`,
`1 = β(αz̄K^{α−1}N^{1−α} + 1 − δ)` iff `K/N = (z̄α/(1/β − (1 − δ)))^{1/(1−α)}`. -/
theorem rb_ss_euler {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    1 = β * (rb_MPK α z K N + 1 - δ) ↔ K / N = rb_kn α β δ z := by
  have hr := rb_rk_pos hβ0 hβ1 hδ
  have hiff : 1 = β * (rb_MPK α z K N + 1 - δ) ↔ rb_MPK α z K N = rb_rk β δ := by
    unfold rb_rk
    constructor
    · intro h
      field_simp
      linarith
    · intro h
      rw [h]
      field_simp
      ring
  rw [hiff]
  constructor
  · intro h
    rw [rb_MPK_ratio α z hK hN, show α - 1 = -(1 - α) by ring,
      Real.rpow_neg (div_pos hK hN).le] at h
    have hp : (K / N) ^ (1 - α) = z * α / rb_rk β δ := by
      have := Real.rpow_pos_of_pos (div_pos hK hN) (1 - α)
      field_simp at h ⊢
      linarith
    unfold rb_kn
    rw [← hp, Real.rpow_rpow_inv (div_pos hK hN).le (by linarith)]
  · intro h
    have hK' : K = rb_kn α β δ z * N := by
      rw [← h]
      field_simp
    rw [hK']
    exact rb_MPK_kn hα0 hα1 hβ0 hβ1 hδ hz hN

/-- Miao, p. 473 (`z̄ = 1`): `K/N = (α/(1/β − (1 − δ)))^{1/(1−α)}`. -/
theorem rb_ss_KN {α β δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N)
    (h : 1 = β * (rb_MPK α 1 K N + 1 - δ)) :
    K / N = (α / (1 / β - (1 - δ))) ^ (1 / (1 - α)) := by
  rw [(rb_ss_euler hα0 hα1 hβ0 hβ1 hδ one_pos hK hN).1 h, rb_kn, rb_rk, one_mul]
  simp only [one_div]

/-- Miao, p. 473: the steady-state factor prices `R_k = αY/K = α(K/N)^{α−1}` and
`w = (1 − α)(K/N)^α` (with `z̄ = 1`). -/
theorem rb_ss_prices (α : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    rb_MPK α 1 K N = α * rb_Y α 1 K N / K ∧ rb_MPK α 1 K N = α * (K / N) ^ (α - 1) ∧
      rb_MPL α 1 K N = (1 - α) * (K / N) ^ α := by
  refine ⟨rb_MPK_eq α 1 hK, ?_, ?_⟩
  · rw [rb_MPK_ratio α 1 hK hN, mul_one]
  · rw [rb_MPL_ratio α 1 hK hN, mul_one]

/-- Miao, p. 473: `I = δK = δ(K/N)N` (from (14.24)) and `Y = (K/N)^αN` (with `z̄ = 1`). -/
theorem rb_ss_IY_levels (α δ : ℝ) {K N : ℝ} (hK : 0 < K) (hN : 0 < N) :
    K = (1 - δ) * K + δ * K ∧ δ * K = δ * (K / N) * N ∧ rb_Y α 1 K N = (K / N) ^ α * N := by
  refine ⟨by ring, by field_simp, ?_⟩
  rw [rb_Y_ratio α 1 hK hN, one_mul]

/-- Miao, pp. 473–475: the steady-state great ratios. With `K = (K/N)N` at the steady-state
ratio, `I = δK` and `C = Y − I`: `Y/K = ρ_k/α`, `I/Y = δα/ρ_k`, `C/Y = 1 − δα/ρ_k`, and
`αY/K + 1 − δ = 1/β` (used in the log-linearisation). -/
theorem rb_ss_ratios {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN : 0 < N) :
    let K := rb_kn α β δ z * N
    let Y := rb_Y α z K N
    Y / K = rb_rk β δ / α ∧ δ * K / Y = δ * α / rb_rk β δ ∧
      (Y - δ * K) / Y = rb_sc α β δ ∧ α * (Y / K) + 1 - δ = 1 / β := by
  intro K Y
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hr := rb_rk_pos hβ0 hβ1 hδ
  have hK : 0 < K := mul_pos hk hN
  have hY : 0 < Y := rb_Y_pos hz hK hN
  have hYK : Y / K = rb_rk β δ / α := by
    have h := rb_MPK_kn hα0 hα1 hβ0 hβ1 hδ hz hN
    rw [rb_MPK_eq α z hK] at h
    rw [eq_div_iff hα0.ne', ← h]
    simp only [Y, K]
    ring
  have hKY : K / Y = α / rb_rk β δ := by
    rw [← inv_div, hYK, inv_div]
  refine ⟨hYK, ?_, ?_, ?_⟩
  · rw [mul_div_assoc, hKY]
    ring
  · rw [sub_div, div_self hY.ne', mul_div_assoc, hKY, rb_sc]
    ring
  · rw [hYK, rb_rk]
    field_simp
    ring

/-- Miao, (14.28), p. 473: at the steady state (`z̄ = 1`), (14.27) `χC/(1 − N) = (1 − α)K^αN^{−α}`
is `χ = (1 − α)(K/N)^α(1 − N)/C`. -/
theorem eq_14_28 {α χ : ℝ} {K N C : ℝ} (hK : 0 < K) (hN0 : 0 < N) (hN1 : N < 1) (hC : 0 < C) :
    eq_14_27 α χ 1 K C N ↔ χ = (1 - α) * (K / N) ^ α * (1 - N) / C := by
  rw [eq_14_27, rb_MPL_ratio α 1 hK hN0, mul_one]
  have h1 : 0 < 1 - N := by linarith
  constructor
  · intro h
    field_simp
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- (14.28) in closed form: at the steady state, (14.27) holds iff
`χ = (1 − α)(1 − N)/(N(1 − δα/ρ_k))`. -/
theorem rb_ss_chi {α β δ χ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN0 : 0 < N) (hN1 : N < 1) :
    eq_14_27 α χ z (rb_kn α β δ z * N) (rb_Y α z (rb_kn α β δ z * N) N -
        δ * (rb_kn α β δ z * N)) N ↔
      χ = (1 - α) * (1 - N) / (N * rb_sc α β δ) := by
  obtain ⟨-, -, hC, -⟩ := rb_ss_ratios hα0 hα1 hβ0 hβ1 hδ hz hN0
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hK : 0 < rb_kn α β δ z * N := mul_pos hk hN0
  have hY : 0 < rb_Y α z (rb_kn α β δ z * N) N := rb_Y_pos hz hK hN0
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  set Y := rb_Y α z (rb_kn α β δ z * N) N
  have hCe : Y - δ * (rb_kn α β δ z * N) = rb_sc α β δ * Y := by
    rw [← hC]
    field_simp
  rw [eq_14_27, hCe, rb_MPL_eq α z _ hN0]
  have h1 : 0 < 1 - N := by linarith
  rw [div_eq_div_iff h1.ne' hN0.ne', eq_div_iff (mul_pos hN0 hs).ne']
  constructor
  · intro h
    have : (χ * (N * rb_sc α β δ) - (1 - α) * (1 - N)) * Y = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact absurd h' hY.ne'
  · intro h
    linear_combination Y * h

/-- Hours as a function of `χ`: `N(χ) = (1 − α)/(1 − α + χs_c)`. -/
noncomputable def rb_ssN (α β δ χ : ℝ) : ℝ := (1 - α) / (1 - α + χ * rb_sc α β δ)

/-- "A one-to-one mapping between `χ` and `N`" (Miao, p. 473): for `N ∈ (0, 1)`,
`χ = (1 − α)(1 − N)/(Ns_c)` iff `N = (1 − α)/(1 − α + χs_c)`. -/
theorem rb_ss_N_iff {α β δ χ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hχ : 0 ≤ χ) {N : ℝ} (hN0 : 0 < N) :
    χ = (1 - α) * (1 - N) / (N * rb_sc α β δ) ↔ N = rb_ssN α β δ χ := by
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  have hd : 0 < 1 - α + χ * rb_sc α β δ := by nlinarith
  have h1α : 0 < 1 - α := by linarith
  unfold rb_ssN
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [h]
    field_simp
    ring

theorem rb_ss_N_mem {α β δ χ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hδ : 0 ≤ δ)
    (hχ : 0 < χ) : 0 < rb_ssN α β δ χ ∧ rb_ssN α β δ χ < 1 := by
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  have hcs := mul_pos hχ hs
  unfold rb_ssN
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

/-- The map `N ↦ χ = (1 − α)(1 − N)/(Ns_c)` is strictly decreasing on `(0, 1)`. -/
theorem rb_ss_chi_strictAnti {α β δ : ℝ} (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hδ : 0 ≤ δ) :
    StrictAntiOn (fun N => (1 - α) * (1 - N) / (N * rb_sc α β δ)) (Set.Ioo 0 1) := by
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  intro a ha b hb hab
  simp only
  rw [div_lt_div_iff₀ (mul_pos hb.1 hs) (mul_pos ha.1 hs)]
  have h1 : 0 < 1 - α := by linarith
  have : (1 - b) * a < (1 - a) * b := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left this (mul_pos h1 hs)]

/-- **Existence and uniqueness of the steady state** (Miao, p. 473): for every `χ > 0`
there is exactly one `(K, N)` with `K > 0`, `N ∈ (0, 1)`, satisfying the steady-state Euler
equation and (14.27) with `C = Y − δK > 0`; it is `N = (1 − α)/(1 − α + χs_c)`,
`K = (K/N)N`. -/
theorem rb_ss_exists_unique {α β δ χ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hz : 0 < z) (hχ : 0 < χ) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ p.2 < 1 ∧ 0 < rb_Y α z p.1 p.2 - δ * p.1 ∧
      1 = β * (rb_MPK α z p.1 p.2 + 1 - δ) ∧
      eq_14_27 α χ z p.1 (rb_Y α z p.1 p.2 - δ * p.1) p.2 := by
  obtain ⟨hN0, hN1⟩ := rb_ss_N_mem hα1 hβ0 hβ1 hδ hχ
  set N := rb_ssN α β δ χ
  have hk := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hK : 0 < rb_kn α β δ z * N := mul_pos hk hN0
  have hs := rb_sc_pos hα1 hβ0 hβ1 hδ
  have hCpos : ∀ M, 0 < M → 0 < rb_Y α z (rb_kn α β δ z * M) M - δ * (rb_kn α β δ z * M) :=
    fun M hM => by
      obtain ⟨-, -, hC, -⟩ := rb_ss_ratios hα0 hα1 hβ0 hβ1 hδ hz hM
      have hY : 0 < rb_Y α z (rb_kn α β δ z * M) M := rb_Y_pos hz (mul_pos hk hM) hM
      have : rb_Y α z (rb_kn α β δ z * M) M - δ * (rb_kn α β δ z * M) =
          rb_sc α β δ * rb_Y α z (rb_kn α β δ z * M) M := by
        rw [← hC]; field_simp
      rw [this]
      positivity
  refine ⟨(rb_kn α β δ z * N, N), ⟨hK, hN0, hN1, hCpos N hN0, ?_, ?_⟩, ?_⟩
  · exact (rb_ss_euler hα0 hα1 hβ0 hβ1 hδ hz hK hN0).2 (by field_simp)
  · exact (rb_ss_chi hα0 hα1 hβ0 hβ1 hδ hz hN0 hN1).2
      ((rb_ss_N_iff hα1 hβ0 hβ1 hδ hχ.le hN0).2 rfl)
  · rintro ⟨K', N'⟩ ⟨hK', hN0', hN1', -, he, hf⟩
    simp only at hK' hN0' hN1' he hf
    have hKN := (rb_ss_euler hα0 hα1 hβ0 hβ1 hδ hz hK' hN0').1 he
    have hK'' : K' = rb_kn α β δ z * N' := by rw [← hKN]; field_simp
    subst hK''
    have hNN := (rb_ss_N_iff hα1 hβ0 hβ1 hδ hχ.le hN0').1
      ((rb_ss_chi hα0 hα1 hβ0 hβ1 hδ hz hN0' hN1').1 hf)
    rw [hNN]

/-- **Calibration** (Miao, p. 474): with `α = 0.33`, `β = 0.99`, `δ = 0.025` and `N = 0.33`,
(14.28) gives `χ = (1 − α)(1 − N)/(Ns_c) = 623971/350889`, with `1.77 < χ < 1.78`. -/
theorem rb_calib_chi :
    (1 - 33 / 100) * (1 - 33 / 100) / (33 / 100 * rb_sc (33 / 100) (99 / 100) (1 / 40)) =
      (623971 / 350889 : ℝ) ∧ (1.77 : ℝ) < 623971 / 350889 ∧ (623971 / 350889 : ℝ) < 1.78 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  simp only [rb_sc, rb_rk]
  norm_num

/-- Correction to Miao, p. 474: the printed calibrated value `χ = 1.75` is not the value of
(14.28) at the stated parameters `α = 0.33`, `β = 0.99`, `δ = 0.025`, `N = 0.33`. -/
theorem rb_calib_chi_ne :
    (1 - 33 / 100) * (1 - 33 / 100) / (33 / 100 * rb_sc (33 / 100) (99 / 100) (1 / 40)) ≠
      (1.75 : ℝ) := by
  rw [rb_calib_chi.1]
  norm_num

/-- **A permanent TFP change** (Miao, p. 484): hours in the steady state do not depend on
`z̄` (`rb_ssN` does not involve `z̄`), and the capital–labour ratio scales as
`(K/N)(z̄) = z̄^{1/(1−α)}(K/N)(1)`; hence `K`, `Y`, `I = δK`, `C = s_cY` and `w` all scale with
`z̄^{1/(1−α)}`: their log changes are `ln z̄/(1 − α)`. -/
theorem rb_ss_permanent {α β δ z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ : 0 ≤ δ) (hz : 0 < z) {N : ℝ} (hN : 0 < N) :
    rb_kn α β δ z = z ^ (1 - α)⁻¹ * rb_kn α β δ 1 ∧
      rb_Y α z (rb_kn α β δ z * N) N = z ^ (1 - α)⁻¹ * rb_Y α 1 (rb_kn α β δ 1 * N) N ∧
      rb_MPL α z (rb_kn α β δ z * N) N = z ^ (1 - α)⁻¹ * rb_MPL α 1 (rb_kn α β δ 1 * N) N ∧
      Real.log (rb_kn α β δ z * N) = Real.log (rb_kn α β δ 1 * N) + Real.log z / (1 - α) := by
  have hr := rb_rk_pos hβ0 hβ1 hδ
  have h1 : 0 < 1 - α := by linarith
  have hk1 := rb_kn_pos hα0 hβ0 hβ1 hδ one_pos
  have hkz := rb_kn_pos hα0 hβ0 hβ1 hδ hz
  have hkn : rb_kn α β δ z = z ^ (1 - α)⁻¹ * rb_kn α β δ 1 := by
    unfold rb_kn
    rw [one_mul, ← Real.mul_rpow hz.le (by positivity), mul_div_assoc]
  have hzp : 0 < z ^ (1 - α)⁻¹ := Real.rpow_pos_of_pos hz _
  -- `z (z^{1/(1−α)})^α = z^{1/(1−α)}`
  have hza : z * (z ^ (1 - α)⁻¹) ^ α = z ^ (1 - α)⁻¹ := by
    rw [← Real.rpow_mul hz.le]
    conv_lhs => lhs; rw [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    field_simp
    ring
  refine ⟨hkn, ?_, ?_, ?_⟩
  · rw [rb_Y_ratio α z (mul_pos hkz hN) hN, rb_Y_ratio α 1 (mul_pos hk1 hN) hN,
      mul_div_cancel_right₀ _ hN.ne', mul_div_cancel_right₀ _ hN.ne', hkn,
      Real.mul_rpow hzp.le hk1.le]
    linear_combination (rb_kn α β δ 1 ^ α * N) * hza
  · rw [rb_MPL_ratio α z (mul_pos hkz hN) hN, rb_MPL_ratio α 1 (mul_pos hk1 hN) hN,
      mul_div_cancel_right₀ _ hN.ne', mul_div_cancel_right₀ _ hN.ne', hkn,
      Real.mul_rpow hzp.le hk1.le]
    linear_combination ((1 - α) * rb_kn α β δ 1 ^ α) * hza
  · rw [hkn, mul_assoc, Real.log_mul hzp.ne' (mul_pos hk1 hN).ne', Real.log_rpow hz]
    ring

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The log-linearised basic RBC model

Miao, §14.2, pp. 474–480, "Log-linearized System". `X̂` is the log deviation of `X_t` from its
steady-state value `X` (z̄ = 1). "Taking logarithms and total differentiation" is made precise as
the derivative at `s = 0` along the curve `X(s) = Xe^{sX̂}` (whose log deviation is `sX̂`); the
log-linearised equation is the vanishing of that derivative.

* (14.27) in logs: the derivative is `Ĉ + ζN̂ − (ẑ + αK̂ − αN̂)`, `ζ = N/(1 − N)`
  (`eq_14_27_loglin`), solved as (14.31) (`eq_14_31`).
* The resource constraint (14.23)–(14.24): the derivative is
  `CĈ + KK̂' − (1 − δ)KK̂ − Y(ẑ + αK̂ + (1 − α)N̂)` (`rb_resource_loglin`), solved for `K̂'`
  with the steady-state Euler equation `1 = β(αY/K + 1 − δ)` (`rb_resource_solved`), and with
  (14.31) substituted, (14.32) (`eq_14_32`).
* The Euler equation (14.26): the derivative of the integrand (`rb_euler_loglin`), the
  linearised equation `−Ĉ_t = −Ĉ_{t+1} + βα(Y/K)[ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1}]`
  (`rb_euler_loglin_eq`), and with (14.31) substituted, (14.33), deterministically
  (`eq_14_33_det`) and with a conditional expectation operator `E_t` (`eq_14_33`).
* The labour market: log-linearised supply (14.36) `ζN̂ = −Ĉ + ŵ` (`eq_14_36_loglin`) and demand
  (14.37) `ŵ = ẑ + αK̂ − αN̂` (`eq_14_37`); their intersection (`rb_labour_market`); the supply
  curve slopes up and the demand curve down (`rb_labour_slopes`).
* Output `Ŷ = αK̂ + (1 − α)N̂ + ẑ` (`rb_output_loglin`), the rental rate `R̂_k = Ŷ − K̂`
  (`rb_rental_loglin`), investment from the resource constraint and from (14.24)
  (`rb_investment_loglin`).
* The stock return (p. 479): with `R^s = R_k + 1 − δ`, the log deviation is
  `R̂^s = (R_k/R^s)R̂_k = (1 − β(1 − δ))R̂_k` (`rb_stock_return_loglin`); the printed
  `R̂^s = R̂_k` is false for `δ < 1` (`rb_stock_return_printed_false`).
* The risk-free rate (p. 480): `r̂^f_{t+1} = E_tĈ_{t+1} − Ĉ_t` (`rb_riskfree_loglin`,
  `rb_riskfree_eq`, and with `E_t`, `rb_riskfree_E`).

The coefficients of (14.32)–(14.33) are `rb_p`, `rb_g`, `rb_q`, `rb_a`, `rb_b`, `rb_c`, written in
terms of `α`, `β`, `ζ` and the steady-state ratios `Y/K`, `C/K`.
-/

namespace Miao.NeoclassicalGrowth

open Real

/-- `ζ = N/(1 − N)` (Miao, p. 475). -/
noncomputable def rb_zeta (N : ℝ) : ℝ := N / (1 - N)

/-- The coefficient of `K̂_t` in (14.32): `1/β + (1 − α)/(α + ζ)·αY/K`. -/
noncomputable def rb_p (α β ζ yk : ℝ) : ℝ := 1 / β + (1 - α) / (α + ζ) * α * yk

/-- The coefficient of `ẑ_t` in (14.32): `(Y/K)(1 + ζ)/(ζ + α)`. -/
noncomputable def rb_g (α ζ yk : ℝ) : ℝ := yk * (1 + ζ) / (ζ + α)

/-- Minus the coefficient of `Ĉ_t` in (14.32): `C/K + (1 − α)/(α + ζ)·Y/K`. -/
noncomputable def rb_q (α ζ yk ck : ℝ) : ℝ := ck + (1 - α) / (α + ζ) * yk

/-- `(1 − α)βα(Y/K)/(α + ζ)`, (14.33). -/
noncomputable def rb_a (α β ζ yk : ℝ) : ℝ := (1 - α) * β * α * yk / (α + ζ)

/-- `βα(Y/K)(1 + ζ)/(α + ζ)`, (14.33). -/
noncomputable def rb_b (α β ζ yk : ℝ) : ℝ := β * α * yk * (1 + ζ) / (α + ζ)

/-- `βα(1 − α)(Y/K)ζ/(α + ζ)`, (14.33). -/
noncomputable def rb_c (α β ζ yk : ℝ) : ℝ := β * α * (1 - α) * yk * ζ / (α + ζ)

/-! ### Exponential curves -/

theorem rb_hasDerivAt_exp_mul (x : ℝ) : HasDerivAt (fun s => Real.exp (s * x)) x 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x).exp

theorem rb_Y_exp (α : ℝ) {z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) (a b c : ℝ) :
    rb_Y α (z * Real.exp a) (K * Real.exp b) (N * Real.exp c) =
      rb_Y α z K N * Real.exp (a + α * b + (1 - α) * c) := by
  unfold rb_Y
  rw [Real.mul_rpow hK.le (Real.exp_pos b).le, Real.mul_rpow hN.le (Real.exp_pos c).le,
    ← Real.exp_mul, ← Real.exp_mul, Real.exp_add, Real.exp_add]
  have := hz
  ring_nf

theorem rb_MPK_exp (α : ℝ) {z K N : ℝ} (hz : 0 < z) (hK : 0 < K) (hN : 0 < N) (a b c : ℝ) :
    rb_MPK α (z * Real.exp a) (K * Real.exp b) (N * Real.exp c) =
      rb_MPK α z K N * Real.exp (a + (α - 1) * b + (1 - α) * c) := by
  unfold rb_MPK
  rw [Real.mul_rpow hK.le (Real.exp_pos b).le, Real.mul_rpow hN.le (Real.exp_pos c).le,
    ← Real.exp_mul, ← Real.exp_mul, Real.exp_add, Real.exp_add]
  have := hz
  ring_nf

theorem rb_MPL_exp (α : ℝ) {z K N : ℝ} (hK : 0 < K) (hN : 0 < N) (a b c : ℝ) :
    rb_MPL α (z * Real.exp a) (K * Real.exp b) (N * Real.exp c) =
      rb_MPL α z K N * Real.exp (a + α * b - α * c) := by
  unfold rb_MPL
  rw [Real.mul_rpow hK.le (Real.exp_pos b).le, Real.mul_rpow hN.le (Real.exp_pos c).le,
    ← Real.exp_mul, ← Real.exp_mul, show a + α * b - α * c = a + b * α + c * -α by ring,
    Real.exp_add, Real.exp_add]
  ring

theorem rb_hasDerivAt_log_one_sub {N n : ℝ} (hN : N < 1) :
    HasDerivAt (fun s => Real.log (1 - N * Real.exp (s * n))) (-(N * n) / (1 - N)) 0 := by
  have h := (((rb_hasDerivAt_exp_mul n).const_mul N).const_sub 1).log (by simp; linarith)
  simpa using h

/-! ### (14.27) and (14.31) -/

/-- Miao, p. 475: "taking logarithms and total differentiation" of (14.27): the derivative at
`s = 0` of `ln(χC_t) − ln(1 − N_t) − ln((1 − α)z_tK_t^αN_t^{−α})` along `X(s) = Xe^{sX̂}` is
`Ĉ + ζN̂ − (ẑ + αK̂ − αN̂)`, `ζ = N/(1 − N)`. -/
theorem eq_14_27_loglin {α χ C K N : ℝ} (hα1 : α < 1) (hχ : 0 < χ) (hC : 0 < C) (hK : 0 < K)
    (hN0 : 0 < N) (hN1 : N < 1) (c z k n : ℝ) :
    HasDerivAt (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) -
        Real.log (rb_MPL α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))))
      (c + rb_zeta N * n - (z + α * k - α * n)) 0 := by
  have hM := rb_MPL_pos hα1 one_pos hK hN0 (α := α)
  have hf : (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) -
        Real.log (rb_MPL α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n)))) =
      fun s => Real.log (χ * C) + s * c - Real.log (1 - N * Real.exp (s * n)) -
        (Real.log (rb_MPL α 1 K N) + s * (z + α * k - α * n)) := by
    funext s
    have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
    rw [e, rb_MPL_exp α hK hN0, ← mul_assoc, Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_mul hM.ne' (by positivity), Real.log_exp]
    ring_nf
  rw [hf]
  have h1 := (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (Real.log (χ * C))).sub
    (rb_hasDerivAt_log_one_sub (n := n) hN1)
  have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const (z + α * k - α * n)).const_add
    (Real.log (rb_MPL α 1 K N))
  convert h1.sub h2 using 1
  · funext s
    simp only [Pi.sub_apply, id]
  · rw [rb_zeta]
    ring

/-- Miao, (14.31), p. 475: `Ĉ + ζN̂ = ẑ + αK̂ − αN̂` iff
`N̂ = ẑ/(α + ζ) + αK̂/(α + ζ) − Ĉ/(α + ζ)`. -/
theorem eq_14_31 {α ζ : ℝ} (h : α + ζ ≠ 0) (c z k n : ℝ) :
    c + ζ * n = z + α * k - α * n ↔
      n = 1 / (α + ζ) * z + α / (α + ζ) * k - 1 / (α + ζ) * c := by
  constructor
  · intro h1
    field_simp
    linarith
  · intro h1
    rw [h1]
    field_simp
    ring

/-! ### The resource constraint and (14.32) -/

/-- Miao, p. 475: total differentiation of the resource constraint
`C_t + K_{t+1} − (1 − δ)K_t = z_tK_t^αN_t^{1−α}` along `X(s) = Xe^{sX̂}`: the derivative is
`CĈ + KK̂' − (1 − δ)KK̂ − Y(ẑ + αK̂ + (1 − α)N̂)` with `Y = K^αN^{1−α}`. -/
theorem rb_resource_loglin (α δ : ℝ) {C K N : ℝ} (hK : 0 < K) (hN : 0 < N) (c k' z k n : ℝ) :
    HasDerivAt (fun s => C * Real.exp (s * c) + K * Real.exp (s * k') -
        (1 - δ) * (K * Real.exp (s * k)) -
        rb_Y α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n)))
      (C * c + K * k' - (1 - δ) * K * k -
        rb_Y α 1 K N * (z + α * k + (1 - α) * n)) 0 := by
  have hf : (fun s => C * Real.exp (s * c) + K * Real.exp (s * k') -
        (1 - δ) * (K * Real.exp (s * k)) -
        rb_Y α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      fun s => C * Real.exp (s * c) + K * Real.exp (s * k') -
        (1 - δ) * (K * Real.exp (s * k)) -
        rb_Y α 1 K N * Real.exp (s * (z + α * k + (1 - α) * n)) := by
    funext s
    have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
    rw [e, rb_Y_exp α one_pos hK hN]
    ring_nf
  rw [hf]
  have := (((rb_hasDerivAt_exp_mul c).const_mul C).add ((rb_hasDerivAt_exp_mul k').const_mul K)).sub
    (((rb_hasDerivAt_exp_mul k).const_mul K).const_mul (1 - δ)) |>.sub
    ((rb_hasDerivAt_exp_mul (z + α * k + (1 - α) * n)).const_mul (rb_Y α 1 K N))
  convert this using 1
  ring

/-- Miao, p. 475: solving the linearised resource constraint for `K̂_{t+1}`:
`K̂' = (Y/K)[ẑ + αK̂ + (1 − α)N̂] − (C/K)Ĉ + (1 − δ)K̂ = K̂/β + (Y/K)[ẑ + (1 − α)N̂] − (C/K)Ĉ`,
using the steady-state Euler equation `1 = β(αY/K + 1 − δ)`. -/
theorem rb_resource_solved {α β δ C K Y : ℝ} (hK : 0 < K) (hss : α * (Y / K) + 1 - δ = 1 / β)
    {c k' z k n : ℝ} (h : C * c + K * k' - (1 - δ) * K * k - Y * (z + α * k + (1 - α) * n) = 0) :
    k' = Y / K * (z + α * k + (1 - α) * n) - C / K * c + (1 - δ) * k ∧
      k' = 1 / β * k + Y / K * (z + (1 - α) * n) - C / K * c := by
  have h1 : k' = Y / K * (z + α * k + (1 - α) * n) - C / K * c + (1 - δ) * k := by
    field_simp
    linarith
  refine ⟨h1, ?_⟩
  rw [h1, ← hss]
  ring

/-- Miao, (14.32), p. 475: substituting (14.31) for `N̂_t` into the solved resource constraint
gives `K̂_{t+1} = (1/β + (1 − α)/(α + ζ)·αY/K)K̂_t + (Y/K)(1 + ζ)/(ζ + α)·ẑ_t
− (C/K + (1 − α)/(α + ζ)·Y/K)Ĉ_t`. -/
theorem eq_14_32 {α β ζ yk ck : ℝ} (hαζ : α + ζ ≠ 0) {c k' z k n : ℝ}
    (hk : k' = 1 / β * k + yk * (z + (1 - α) * n) - ck * c)
    (hn : n = 1 / (α + ζ) * z + α / (α + ζ) * k - 1 / (α + ζ) * c) :
    k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c := by
  have h' : ζ + α ≠ 0 := by rwa [add_comm]
  rw [hk, hn, rb_p, rb_g, rb_q]
  field_simp
  ring

/-! ### The Euler equation and (14.33) -/

/-- Miao, p. 476: total differentiation of the Euler equation (14.26): the derivative at `s = 0`
of the integrand `1/C_t − β(αz_{t+1}K_{t+1}^{α−1}N_{t+1}^{1−α} + 1 − δ)/C_{t+1}` along
`X(s) = Xe^{sX̂}` is
`(−Ĉ_t + β(R_k + 1 − δ)Ĉ_{t+1} − βR_k(ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1}))/C`. -/
theorem rb_euler_loglin (α β δ : ℝ) {C K N : ℝ} (hC : 0 < C) (hK : 0 < K) (hN : 0 < N)
    (c c' z' k' n' : ℝ) :
    HasDerivAt (fun s => 1 / (C * Real.exp (s * c)) -
        β * (rb_MPK α (Real.exp (s * z')) (K * Real.exp (s * k')) (N * Real.exp (s * n')) +
          1 - δ) / (C * Real.exp (s * c')))
      ((-c + β * (rb_MPK α 1 K N + 1 - δ) * c' -
        β * rb_MPK α 1 K N * (z' + (α - 1) * k' + (1 - α) * n')) / C) 0 := by
  set e := z' + (α - 1) * k' + (1 - α) * n'
  have hf : (fun s => 1 / (C * Real.exp (s * c)) -
        β * (rb_MPK α (Real.exp (s * z')) (K * Real.exp (s * k')) (N * Real.exp (s * n')) +
          1 - δ) / (C * Real.exp (s * c'))) =
      fun s => 1 / C * Real.exp (s * (-c)) -
        β / C * (rb_MPK α 1 K N * Real.exp (s * (e - c')) + (1 - δ) * Real.exp (s * (-c'))) := by
    funext s
    have ez : Real.exp (s * z') = 1 * Real.exp (s * z') := (one_mul _).symm
    rw [ez, rb_MPK_exp α one_pos hK hN]
    have h1 : Real.exp (s * (-c)) = 1 / Real.exp (s * c) := by
      rw [mul_neg, Real.exp_neg, one_div]
    have h2 : Real.exp (s * (-c')) = 1 / Real.exp (s * c') := by
      rw [mul_neg, Real.exp_neg, one_div]
    have h3 : Real.exp (s * (e - c')) = Real.exp (s * e) / Real.exp (s * c') := by
      rw [mul_sub, Real.exp_sub]
    rw [h1, h2, h3]
    simp only [e]
    field_simp
    ring_nf
  rw [hf]
  have := ((rb_hasDerivAt_exp_mul (-c)).const_mul (1 / C)).sub
    ((((rb_hasDerivAt_exp_mul (e - c')).const_mul (rb_MPK α 1 K N)).add
      ((rb_hasDerivAt_exp_mul (-c')).const_mul (1 - δ))).const_mul (β / C))
  convert this using 1
  field_simp
  ring

/-- Miao, p. 476: with the steady-state Euler equation `β(αY/K + 1 − δ) = 1` and
`R_k = αY/K`, the linearised Euler equation (the derivative of `rb_euler_loglin` set to zero) is
`−Ĉ_t = −Ĉ_{t+1} + βα(Y/K)[ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1}]`. -/
theorem rb_euler_loglin_eq {α β δ C yk Rk : ℝ} (hC : 0 < C) (hRk : Rk = α * yk)
    (hss : β * (Rk + 1 - δ) = 1) (c c' z' k' n' : ℝ) :
    (-c + β * (Rk + 1 - δ) * c' - β * Rk * (z' + (α - 1) * k' + (1 - α) * n')) / C = 0 ↔
      -c = -c' + β * α * yk * (z' + (α - 1) * k' + (1 - α) * n') := by
  rw [div_eq_zero_iff, hss, hRk]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hC.ne'
  · intro h
    left
    linarith

/-- Miao, (14.33), p. 476, deterministic form: substituting (14.31) at `t + 1` into the
linearised Euler equation gives
`−Ĉ_t = −(1 + (1 − α)βα(Y/K)/(α + ζ))Ĉ_{t+1} + βα(Y/K)(1 + ζ)/(α + ζ)·ẑ_{t+1}
− βα(1 − α)(Y/K)ζ/(α + ζ)·K̂_{t+1}`. -/
theorem eq_14_33_det {α β ζ yk : ℝ} (hαζ : α + ζ ≠ 0) {c c' z' k' n' : ℝ}
    (he : -c = -c' + β * α * yk * (z' + (α - 1) * k' + (1 - α) * n'))
    (hn : n' = 1 / (α + ζ) * z' + α / (α + ζ) * k' - 1 / (α + ζ) * c') :
    -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k' := by
  rw [he, hn, rb_a, rb_b, rb_c]
  field_simp
  ring

/-- Miao, (14.33), p. 476, with the conditional expectation: let `E_t` be a conditional
expectation operator (a continuous linear map, as in Chapter 2). If
`−Ĉ_t = E_t[−Ĉ_{t+1} + βα(Y/K)(ẑ_{t+1} + (α − 1)K̂_{t+1} + (1 − α)N̂_{t+1})]` and (14.31) holds at
`t + 1`, then `−Ĉ_t = −(1 + a)E_tĈ_{t+1} + bE_tẑ_{t+1} − cE_tK̂_{t+1}`. -/
theorem eq_14_33 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (E : CondExpSystem ℝ V)
    {α β ζ yk : ℝ} (hαζ : α + ζ ≠ 0) {C Z Kh Nh : ℕ → V} (t : ℕ)
    (he : -C t = E.E t (-C (t + 1) + (β * α * yk) • (Z (t + 1) + (α - 1) • Kh (t + 1) +
      (1 - α) • Nh (t + 1))))
    (hn : Nh (t + 1) = (1 / (α + ζ)) • Z (t + 1) + (α / (α + ζ)) • Kh (t + 1) -
      (1 / (α + ζ)) • C (t + 1)) :
    -C t = -(1 + rb_a α β ζ yk) • E.E t (C (t + 1)) + rb_b α β ζ yk • E.E t (Z (t + 1)) -
      rb_c α β ζ yk • E.E t (Kh (t + 1)) := by
  rw [he, hn]
  simp only [map_add, map_sub, map_neg, map_smul]
  rw [rb_a, rb_b, rb_c]
  match_scalars <;> field_simp <;> ring

/-! ### The labour market (14.36)–(14.37), output, rental rate, investment -/

/-- Miao, p. 478: the log-linearised labour supply (14.36) `χC_t/(1 − N_t) = w_t`: the derivative
of `ln(χC) − ln(1 − N) − ln w` along `X(s) = Xe^{sX̂}` is `Ĉ + ζN̂ − ŵ`, so the linearised supply
curve is `ζN̂ = −Ĉ + ŵ`. -/
theorem eq_14_36_loglin {χ C N w : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hN1 : N < 1) (hw : 0 < w)
    (c n wh : ℝ) :
    HasDerivAt (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) - Real.log (w * Real.exp (s * wh)))
      (c + rb_zeta N * n - wh) 0 := by
  have hf : (fun s => Real.log (χ * (C * Real.exp (s * c))) -
        Real.log (1 - N * Real.exp (s * n)) - Real.log (w * Real.exp (s * wh))) =
      fun s => Real.log (χ * C) + s * c - Real.log (1 - N * Real.exp (s * n)) -
        (Real.log w + s * wh) := by
    funext s
    rw [← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul hw.ne' (by positivity), Real.log_exp]
  rw [hf]
  have h1 := (((hasDerivAt_id (0 : ℝ)).mul_const c).const_add (Real.log (χ * C))).sub
    (rb_hasDerivAt_log_one_sub (n := n) hN1)
  have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const wh).const_add (Real.log w)
  convert h1.sub h2 using 1
  · funext s
    simp only [Pi.sub_apply, id]
  · rw [rb_zeta]
    ring

/-- Miao, (14.37), p. 478: the log-linearised labour demand `w = (1 − α)zK^αN^{−α}`: the log of
the wage along `X(s) = Xe^{sX̂}` is `ln w + s(ẑ + αK̂ − αN̂)`, so `ŵ = ẑ + αK̂ − αN̂`. -/
theorem eq_14_37 {α K N : ℝ} (hα1 : α < 1) (hK : 0 < K) (hN : 0 < N) (z k n s : ℝ) :
    Real.log (rb_MPL α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      Real.log (rb_MPL α 1 K N) + s * (z + α * k - α * n) := by
  have hM := rb_MPL_pos hα1 one_pos hK hN (α := α)
  have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
  rw [e, rb_MPL_exp α hK hN, Real.log_mul hM.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 478 (Figure 14.2): the log-linearised labour supply `ζN̂ = −Ĉ + ŵ` and demand
`ŵ = ẑ + αK̂ − αN̂` intersect at `N̂ = (ẑ + αK̂ − Ĉ)/(α + ζ)` (this is (14.31)) and
`ŵ = (ζ(ẑ + αK̂) + αĈ)/(α + ζ)`. -/
theorem rb_labour_market {α ζ : ℝ} (hαζ : α + ζ ≠ 0) {c z k n wh : ℝ} :
    (ζ * n = -c + wh ∧ wh = z + α * k - α * n) ↔
      (n = (z + α * k - c) / (α + ζ) ∧ wh = (ζ * (z + α * k) + α * c) / (α + ζ)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hn : n = (z + α * k - c) / (α + ζ) := by
      field_simp
      linarith
    refine ⟨hn, ?_⟩
    rw [h2, hn]
    field_simp
    ring
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    constructor <;> field_simp <;> ring

/-- Miao, p. 478: the labour supply curve `ŵ = ζN̂ + Ĉ` is upward sloping in `N̂` (`ζ > 0`) and
shifts up with `Ĉ` (the wealth effect); the demand curve `ŵ = ẑ + αK̂ − αN̂` is downward sloping and
shifts up with `ẑ`. In equilibrium `∂N̂/∂Ĉ = −1/(α + ζ) < 0`, `∂ŵ/∂Ĉ = α/(α + ζ) > 0`,
`∂N̂/∂ẑ = 1/(α + ζ) > 0` and `∂ŵ/∂ẑ = ζ/(α + ζ) > 0`. -/
theorem rb_labour_slopes {α ζ : ℝ} (hα : 0 < α) (hζ : 0 < ζ) :
    StrictMono (fun n : ℝ => ζ * n) ∧ StrictAnti (fun n : ℝ => -(α * n)) ∧
      -1 / (α + ζ) < 0 ∧ 0 < α / (α + ζ) ∧ 0 < 1 / (α + ζ) ∧ 0 < ζ / (α + ζ) := by
  have h : 0 < α + ζ := by linarith
  refine ⟨fun a b hab => by simp only; nlinarith, fun a b hab => by simp only; nlinarith,
    by rw [neg_div]; exact neg_neg_of_pos (by positivity), by positivity, by positivity,
    by positivity⟩

/-- Miao, p. 478: the log-linearised production function. Along `X(s) = Xe^{sX̂}`,
`ln Y = ln Y + s(ẑ + αK̂ + (1 − α)N̂)`, so `Ŷ = αK̂ + (1 − α)N̂ + ẑ`. -/
theorem rb_output_loglin {α K N : ℝ} (hK : 0 < K) (hN : 0 < N) (z k n s : ℝ) :
    Real.log (rb_Y α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      Real.log (rb_Y α 1 K N) + s * (α * k + (1 - α) * n + z) := by
  have hY := rb_Y_pos (α := α) one_pos hK hN
  have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
  rw [e, rb_Y_exp α one_pos hK hN, Real.log_mul hY.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 478: the rental rate `R_k = αY/K`; along `X(s) = Xe^{sX̂}`,
`ln R_k = ln R_k + s(Ŷ − K̂)`, so `R̂_k = Ŷ − K̂`. -/
theorem rb_rental_loglin {α K N : ℝ} (hα : 0 < α) (hK : 0 < K) (hN : 0 < N) (z k n s : ℝ) :
    Real.log (rb_MPK α (Real.exp (s * z)) (K * Real.exp (s * k)) (N * Real.exp (s * n))) =
      Real.log (rb_MPK α 1 K N) + s * ((α * k + (1 - α) * n + z) - k) := by
  have hR := rb_MPK_pos hα one_pos hK hN
  have e : Real.exp (s * z) = 1 * Real.exp (s * z) := (one_mul _).symm
  rw [e, rb_MPK_exp α one_pos hK hN, Real.log_mul hR.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 480 ("we can derive investment simply from the resource constraint"): the
linearised resource constraint `CĈ + IÎ = YŶ` gives `Î = (YŶ − CĈ)/I`, and the linearised
(14.24) `KK̂' = (1 − δ)KK̂ + IÎ` with `I = δK` gives `Î = (K̂' − (1 − δ)K̂)/δ`. -/
theorem rb_investment_loglin {δ C I Y K : ℝ} (hI : 0 < I) (hδ : 0 < δ) (hIK : I = δ * K)
    {c i y k k' : ℝ} :
    (C * c + I * i = Y * y → i = (Y * y - C * c) / I) ∧
      (K * k' = (1 - δ) * K * k + I * i → i = (k' - (1 - δ) * k) / δ) := by
  have hK : K ≠ 0 := by rintro rfl; simp at hIK; linarith
  refine ⟨fun h => ?_, fun h => ?_⟩
  · field_simp
    linarith
  · rw [hIK] at h
    rw [eq_div_iff hδ.ne']
    apply mul_left_cancel₀ hK
    linarith

/-! ### Returns -/

/-- Miao, p. 479, corrected: with `R^s = R_k + 1 − δ`, along `R_k(s) = R_ke^{sR̂_k}` the log
deviation of `R^s` is `(R_k/R^s)R̂_k`: `d/ds ln(R_ke^{sR̂_k} + 1 − δ)|₀ = R_kR̂_k/(R_k + 1 − δ)`;
at the steady state `R^s = 1/β`, so `R̂^s = (1 − β(1 − δ))R̂_k`. -/
theorem rb_stock_return_loglin {β δ Rk : ℝ} (hRs : β * (Rk + 1 - δ) = 1) (hβ : 0 < β)
    (r : ℝ) :
    HasDerivAt (fun s => Real.log (Rk * Real.exp (s * r) + 1 - δ)) ((1 - β * (1 - δ)) * r) 0 := by
  have hpos : Rk + 1 - δ ≠ 0 := by
    intro h; rw [h, mul_zero] at hRs; exact zero_ne_one hRs
  have h := (((rb_hasDerivAt_exp_mul r).const_mul Rk).add_const (1 - δ)).log
    (by simpa [add_sub_assoc] using hpos)
  convert h using 1
  · funext s; ring_nf
  · simp only [zero_mul, Real.exp_zero, mul_one]
    have hR : Rk = 1 / β - (1 - δ) := by field_simp; linarith
    rw [show Rk + (1 - δ) = Rk + 1 - δ by ring]
    field_simp
    rw [hR]
    field_simp
    ring

/-- Correction to Miao, p. 479: the printed `R̂^s_t = R̂_kt` fails whenever `δ < 1` and
`R̂_k ≠ 0` (here `β = 1/2`, `δ = 0`, `R_k = 1`, `R̂_k = 1`: the log deviation of `R^s` is `1/2`). -/
theorem rb_stock_return_printed_false :
    ¬ HasDerivAt (fun s => Real.log (1 * Real.exp (s * 1) + 1 - 0)) 1 0 := by
  intro h
  have h2 := rb_stock_return_loglin (β := 1 / 2) (δ := 0) (Rk := 1) (by norm_num) (by norm_num) 1
  have := h.unique h2
  norm_num at this

/-- Miao, p. 480: total differentiation of the risk-free Euler equation
`1/C_t = βE_t[(1 + r^f_{t+1})/C_{t+1}]`: the derivative at `s = 0` of the integrand
`1/C_t − βR^f_{t+1}/C_{t+1}` along `X(s) = Xe^{sX̂}` (with `R̂^f = dR^f/R^f`) is
`(−Ĉ_t − βR^f(R̂^f − Ĉ_{t+1}))/C`. -/
theorem rb_riskfree_loglin (β : ℝ) {C Rf : ℝ} (hC : 0 < C) (c c' r : ℝ) :
    HasDerivAt (fun s => 1 / (C * Real.exp (s * c)) -
        β * (Rf * Real.exp (s * r)) / (C * Real.exp (s * c')))
      ((-c - β * Rf * (r - c')) / C) 0 := by
  have hf : (fun s => 1 / (C * Real.exp (s * c)) -
        β * (Rf * Real.exp (s * r)) / (C * Real.exp (s * c'))) =
      fun s => 1 / C * Real.exp (s * (-c)) - β * Rf / C * Real.exp (s * (r - c')) := by
    funext s
    rw [mul_neg, Real.exp_neg, mul_sub, Real.exp_sub]
    field_simp
  rw [hf]
  have := ((rb_hasDerivAt_exp_mul (-c)).const_mul (1 / C)).sub
    ((rb_hasDerivAt_exp_mul (r - c')).const_mul (β * Rf / C))
  convert this using 1
  field_simp

/-- Miao, p. 480: with `βR^f = 1` at the steady state, the linearised risk-free Euler equation
is `r̂^f_{t+1} = Ĉ_{t+1} − Ĉ_t`. -/
theorem rb_riskfree_eq {β C Rf : ℝ} (hC : 0 < C) (hss : β * Rf = 1) (c c' r : ℝ) :
    (-c - β * Rf * (r - c')) / C = 0 ↔ r = c' - c := by
  rw [div_eq_zero_iff, hss]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hC.ne'
  · intro h
    left
    linarith

/-- Miao, p. 480: since `r^f_{t+1}` is known at date `t` (`E_tr̂^f_{t+1} = r̂^f_{t+1}`), applying
`E_t` to the linearised equation gives `r̂^f_{t+1} = E_tĈ_{t+1} − Ĉ_t` (`Ĉ_t` adapted). -/
theorem rb_riskfree_E {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : CondExpSystem ℝ V) {C R : ℕ → V} (t : ℕ) (hC : E.E t (C t) = C t)
    (hR : E.E t (R (t + 1)) = R (t + 1)) (h : E.E t (R (t + 1) - (C (t + 1) - C t)) = 0) :
    R (t + 1) = E.E t (C (t + 1)) - C t := by
  rw [map_sub, map_sub, hC, hR, sub_eq_zero] at h
  exact h

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The phase diagram and the saddle path of the log-linearised RBC model

Miao, §14.2, pp. 476–478 (Figure 14.1) and p. 484 (Figure 14.3). Throughout,
`0 < α < 1`, `0 < β < 1`, `ζ > 0`, `Y/K > 0`, `C/K > 0`.

* (14.34): `K̂_{t+1} − K̂_t = (p − 1)K̂_t + gẑ_t − qĈ_t` (`eq_14_34_K`). The second line of
  (14.34) is printed with `+(1 − α)βα(Y/K)/(α + ζ)·Ĉ_{t+1}`; (14.33) gives `−aĈ_{t+1}`
  (`eq_14_34_C`); the printed sign is wrong (`eq_14_34_printed_false`).
* The isocline `ΔĈ = 0` is `Ĉ_{t+1} = (1 + ζ)/(1 − α)·ẑ_{t+1} − ζK̂_{t+1}`, downward sloping
  (`rb_isocline_C`), and `Ĉ` falls exactly to the right of it (`rb_isocline_C_sign`). The
  isocline `ΔK̂ = 0` is (14.35), upward sloping (`eq_14_35`), and `K̂` falls exactly above it
  (`eq_14_35_sign`).
* With `ẑ = 0` the system is `x_{t+1} = Mx_t` (`rb_det_system`) with `det M = p/(1 + a)` and
  characteristic polynomial negative at `1` (`rb_char_one_neg`); hence its eigenvalues are real
  with `0 < λ₁ < 1 < λ₂` (`rb_saddle_roots`, `rb_saddle_eigen`): a saddle.
* The saddle path (`rb_saddle_det`): for every `K̂₀`, `K̂_t = λ₁ᵗK̂₀`, `Ĉ_t = φK̂_t` with
  `φ = (λ₂ − m₂₂)/q > 0` (upward sloping) solves the system and converges monotonically to the
  steady state, and it is the only bounded solution with that `K̂₀`: "given any initial state
  `K̂₀` there is a unique solution `Ĉ₀`, which must lie on the saddle".
* A permanent TFP shock (p. 484): with `ẑ_t = ẑ` for all `t`, the new steady state is
  `K̂* = Ĉ* = ẑ/(1 − α)` (`rb_permanent_ss`; both isoclines shift up, `rb_permanent_shift`);
  from `K̂₀ = 0` the unique bounded path rises monotonically to it, the interest rate
  `r̂^f_{t+1} = Ĉ_{t+1} − Ĉ_t` is positive and investment rises (`rb_permanent_path`). Initial
  consumption `Ĉ₀ = (1 − φ)ẑ/(1 − α)` may be of either sign (as the book says).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### Signs of the coefficients -/

theorem rb_coeff_pos {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    1 < rb_p α β ζ yk ∧ 0 < rb_q α ζ yk ck ∧ 0 < rb_a α β ζ yk ∧ 0 < rb_b α β ζ yk ∧
      0 < rb_c α β ζ yk ∧ 0 < rb_g α ζ yk := by
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < α + ζ := by linarith
  have hb : 1 < 1 / β := by rw [lt_one_div (by norm_num) hβ0]; simpa using hβ1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rb_p
    have : 0 < (1 - α) / (α + ζ) * α * yk := by positivity
    linarith
  · unfold rb_q; positivity
  · unfold rb_a; positivity
  · unfold rb_b; positivity
  · unfold rb_c; positivity
  · unfold rb_g; positivity

theorem rb_b_eq {α β ζ yk : ℝ} (hα1 : α < 1) :
    rb_b α β ζ yk = rb_a α β ζ yk * ((1 + ζ) / (1 - α)) := by
  have h1 : 1 - α ≠ 0 := by linarith
  unfold rb_a rb_b
  field_simp

theorem rb_c_eq (α β ζ yk : ℝ) : rb_c α β ζ yk = rb_a α β ζ yk * ζ := by
  unfold rb_a rb_c
  ring

/-! ### The phase diagram (14.34)–(14.35) -/

/-- Miao, (14.34), first line, p. 476: `K̂_{t+1} − K̂_t = (1/β − 1 + (1 − α)/(α + ζ)·αY/K)K̂_t
+ (Y/K)(1 + ζ)/(ζ + α)·ẑ_t − (C/K + (1 − α)/(α + ζ)·Y/K)Ĉ_t`. -/
theorem eq_14_34_K {α β ζ yk ck c k k' z : ℝ}
    (h : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c) :
    k' - k = (1 / β - 1 + (1 - α) / (α + ζ) * α * yk) * k + rb_g α ζ yk * z -
      rb_q α ζ yk ck * c := by
  rw [h, rb_p]
  ring

/-- Miao, (14.34), second line, corrected: (14.33) gives
`Ĉ_{t+1} − Ĉ_t = −(1 − α)βα(Y/K)/(α + ζ)·Ĉ_{t+1} + βα(Y/K)(1 + ζ)/(α + ζ)·ẑ_{t+1}
− βα(1 − α)(Y/K)ζ/(α + ζ)·K̂_{t+1}`. -/
theorem eq_14_34_C {α β ζ yk c c' k' z' : ℝ}
    (h : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' - c = -rb_a α β ζ yk * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k' := by
  linarith

/-- Correction to Miao, (14.34), p. 476: the printed second line
`Ĉ_{t+1} − Ĉ_t = +aĈ_{t+1} + bẑ_{t+1} − cK̂_{t+1}` is inconsistent with (14.33): whenever `a ≠ 0`,
the point `Ĉ_{t+1} = 1`, `Ĉ_t = 1 + a`, `ẑ_{t+1} = K̂_{t+1} = 0` satisfies (14.33) but not the
printed equation. -/
theorem eq_14_34_printed_false {α β ζ yk : ℝ} (ha : rb_a α β ζ yk ≠ 0) :
    let c' : ℝ := 1
    let c : ℝ := 1 + rb_a α β ζ yk
    (-c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * 0 - rb_c α β ζ yk * 0) ∧
      c' - c ≠ rb_a α β ζ yk * c' + rb_b α β ζ yk * 0 - rb_c α β ζ yk * 0 := by
  intro c' c
  refine ⟨by simp [c, c'], fun h => ha ?_⟩
  simp only [c, c'] at h
  linarith

/-- Miao, p. 477: the isocline `ΔĈ_t = 0`. Along (14.33),
`Ĉ_{t+1} − Ĉ_t = −a(Ĉ_{t+1} − (1 + ζ)/(1 − α)·ẑ_{t+1} + ζK̂_{t+1})`, so `Ĉ_{t+1} = Ĉ_t` iff
`Ĉ_{t+1} = (1 + ζ)/(1 − α)·ẑ_{t+1} − ζK̂_{t+1}`, a downward-sloping line (slope `−ζ < 0`). -/
theorem rb_isocline_C {α β ζ yk c c' k' z' : ℝ} (hα1 : α < 1) (ha : rb_a α β ζ yk ≠ 0)
    (h : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' - c = -rb_a α β ζ yk * (c' - (1 + ζ) / (1 - α) * z' + ζ * k') ∧
      (c' = c ↔ c' = (1 + ζ) / (1 - α) * z' - ζ * k') := by
  have hd : c' - c = -rb_a α β ζ yk * (c' - (1 + ζ) / (1 - α) * z' + ζ * k') := by
    rw [eq_14_34_C h, rb_b_eq hα1, rb_c_eq]
    ring
  refine ⟨hd, ⟨fun he => ?_, fun he => ?_⟩⟩
  · have : rb_a α β ζ yk * (c' - (1 + ζ) / (1 - α) * z' + ζ * k') = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 ha
    · linarith
  · have : c' - c = 0 := by rw [hd, he]; ring
    linarith

/-- Miao, p. 477: "when `K̂` is above the isocline `Ĉ_t = Ĉ_{t+1}`, `Ĉ_t` is expected to fall":
with `a > 0`, `Ĉ_{t+1} < Ĉ_t` iff `ζK̂_{t+1} > (1 + ζ)/(1 − α)·ẑ_{t+1} − Ĉ_{t+1}`. -/
theorem rb_isocline_C_sign {α β ζ yk c c' k' z' : ℝ} (hα1 : α < 1) (ha : 0 < rb_a α β ζ yk)
    (h : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' < c ↔ (1 + ζ) / (1 - α) * z' - c' < ζ * k' := by
  have hd := (rb_isocline_C hα1 ha.ne' h).1
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    have : 0 ≤ c' - c := by
      rw [hd]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    linarith
  · intro hlt
    have : c' - c < 0 := by
      rw [hd]
      exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith

/-- Miao, (14.35), p. 477: the isocline `ΔK̂_t = 0`: `K̂_{t+1} = K̂_t` iff
`Ĉ_t = (C/K + (1 − α)/(α + ζ)·Y/K)⁻¹[(1/β − 1 + (1 − α)/(α + ζ)·αY/K)K̂_t
+ (Y/K)(1 + ζ)/(ζ + α)·ẑ_t]`, an upward-sloping line. -/
theorem eq_14_35 {α β ζ yk ck c k k' z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck)
    (h : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c) :
    (k' = k ↔ c = (rb_q α ζ yk ck)⁻¹ * ((1 / β - 1 + (1 - α) / (α + ζ) * α * yk) * k +
        rb_g α ζ yk * z)) ∧
      0 < (rb_q α ζ yk ck)⁻¹ * (1 / β - 1 + (1 - α) / (α + ζ) * α * yk) := by
  obtain ⟨hp, hq, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hd := eq_14_34_K h
  have hp' : 1 / β - 1 + (1 - α) / (α + ζ) * α * yk = rb_p α β ζ yk - 1 := by
    rw [rb_p]; ring
  refine ⟨⟨fun he => ?_, fun he => ?_⟩, ?_⟩
  · rw [he, sub_self, hp'] at hd
    rw [hp', eq_inv_mul_iff_mul_eq₀ hq.ne']
    linarith
  · rw [hp'] at he hd
    rw [he, mul_inv_cancel_left₀ hq.ne'] at hd
    linarith
  · rw [hp']
    have : 0 < rb_p α β ζ yk - 1 := by linarith
    positivity

/-- Miao, pp. 477–478: "when `Ĉ_t` is above the isocline `K̂_{t+1} = K̂_t`, `K̂_t` is expected to
fall because households save less": `K̂_{t+1} < K̂_t` iff `Ĉ_t` exceeds the right side of
(14.35). -/
theorem eq_14_35_sign {α β ζ yk ck c k k' z : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck)
    (h : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c) :
    k' < k ↔ (rb_q α ζ yk ck)⁻¹ * ((1 / β - 1 + (1 - α) / (α + ζ) * α * yk) * k +
        rb_g α ζ yk * z) < c := by
  obtain ⟨-, hq, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hd := eq_14_34_K h
  rw [inv_mul_lt_iff₀ hq]
  constructor <;> intro h' <;> nlinarith

/-! ### The deterministic system as `x_{t+1} = Mx_t` -/

/-- The entries of the matrix `M` of the deterministic log-linearised system in `(K̂, Ĉ)`. -/
noncomputable def rb_m21 (α β ζ yk : ℝ) : ℝ :=
  -(rb_c α β ζ yk * rb_p α β ζ yk) / (1 + rb_a α β ζ yk)

/-- `m₂₂ = (1 + cq)/(1 + a)`. -/
noncomputable def rb_m22 (α β ζ yk ck : ℝ) : ℝ :=
  (1 + rb_c α β ζ yk * rb_q α ζ yk ck) / (1 + rb_a α β ζ yk)

/-- Miao, pp. 476–477: the deterministic system (14.32)–(14.33) is
`K̂_{t+1} = pK̂_t − qĈ_t + gẑ_t`,
`Ĉ_{t+1} = m₂₁K̂_t + m₂₂Ĉ_t + (bẑ_{t+1} − cgẑ_t)/(1 + a)`. -/
theorem rb_det_system {α β ζ yk ck c c' k k' z z' : ℝ} (ha : 1 + rb_a α β ζ yk ≠ 0)
    (h1 : k' = rb_p α β ζ yk * k + rb_g α ζ yk * z - rb_q α ζ yk ck * c)
    (h2 : -c = -(1 + rb_a α β ζ yk) * c' + rb_b α β ζ yk * z' - rb_c α β ζ yk * k') :
    c' = rb_m21 α β ζ yk * k + rb_m22 α β ζ yk ck * c +
      (rb_b α β ζ yk * z' - rb_c α β ζ yk * rb_g α ζ yk * z) / (1 + rb_a α β ζ yk) := by
  rw [rb_m21, rb_m22]
  field_simp
  rw [h1] at h2
  linarith

/-- `det M = m₁₁m₂₂ − m₁₂m₂₁ = p/(1 + a)`. -/
theorem rb_det_M {α β ζ yk ck : ℝ} (ha : 1 + rb_a α β ζ yk ≠ 0) :
    rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk =
      rb_p α β ζ yk / (1 + rb_a α β ζ yk) := by
  rw [rb_m21, rb_m22]
  field_simp
  ring

/-- The characteristic polynomial `λ² − (m₁₁ + m₂₂)λ + det M` is negative at `λ = 1`:
`1 − tr M + det M = (a(1 − p) − cq)/(1 + a) < 0`; also `det M > 0` and `m₁₂m₂₁ > 0`. -/
theorem rb_char_one_neg {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    1 - (rb_p α β ζ yk + rb_m22 α β ζ yk ck) +
        (rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk) < 0 ∧
      0 < rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk ∧
      0 < (-rb_q α ζ yk ck) * rb_m21 α β ζ yk := by
  obtain ⟨hp, hq, ha, -, hc, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have ha' : 1 + rb_a α β ζ yk ≠ 0 := by linarith
  rw [rb_det_M ha']
  refine ⟨?_, by positivity, ?_⟩
  · have : 1 - (rb_p α β ζ yk + rb_m22 α β ζ yk ck) + rb_p α β ζ yk / (1 + rb_a α β ζ yk) =
        (rb_a α β ζ yk * (1 - rb_p α β ζ yk) - rb_c α β ζ yk * rb_q α ζ yk ck) /
          (1 + rb_a α β ζ yk) := by
      rw [rb_m22]
      field_simp
      ring
    rw [this]
    apply div_neg_of_neg_of_pos _ (by linarith)
    nlinarith [mul_pos hc hq]
  · rw [rb_m21]
    have : 0 < rb_c α β ζ yk * rb_p α β ζ yk := by nlinarith
    rw [neg_mul, neg_div, mul_neg, neg_neg]
    positivity

/-- The two roots of `λ² − Tλ + D`. -/
noncomputable def rb_lam1 (T D : ℝ) : ℝ := (T - √(T ^ 2 - 4 * D)) / 2

/-- The larger root of `λ² − Tλ + D`. -/
noncomputable def rb_lam2 (T D : ℝ) : ℝ := (T + √(T ^ 2 - 4 * D)) / 2

/-- If `1 − T + D < 0` and `D > 0`, the roots of `λ² − Tλ + D` are real and
`0 < λ₁ < 1 < λ₂`, with `λ₁ + λ₂ = T` and `λ₁λ₂ = D`. -/
theorem rb_saddle_roots {T D : ℝ} (h1 : 1 - T + D < 0) (hD : 0 < D) :
    rb_lam1 T D + rb_lam2 T D = T ∧ rb_lam1 T D * rb_lam2 T D = D ∧
      0 < rb_lam1 T D ∧ rb_lam1 T D < 1 ∧ 1 < rb_lam2 T D ∧
      (∀ x, x ^ 2 - T * x + D = (x - rb_lam1 T D) * (x - rb_lam2 T D)) := by
  have hdisc : (T - 2) ^ 2 < T ^ 2 - 4 * D := by nlinarith
  have hd0 : 0 ≤ T ^ 2 - 4 * D := le_trans (sq_nonneg _) hdisc.le
  set r := √(T ^ 2 - 4 * D)
  have hr2 : r ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hd0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have habs : |T - 2| < r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hdisc
  have hsum : rb_lam1 T D + rb_lam2 T D = T := by unfold rb_lam1 rb_lam2; ring
  have hprod : rb_lam1 T D * rb_lam2 T D = D := by
    unfold rb_lam1 rb_lam2
    nlinarith
  have hl2 : 1 < rb_lam2 T D := by
    unfold rb_lam2
    have := neg_abs_le (T - 2)
    linarith
  have hl1 : rb_lam1 T D < 1 := by
    unfold rb_lam1
    have := le_abs_self (T - 2)
    linarith
  refine ⟨hsum, hprod, ?_, hl1, hl2, fun x => ?_⟩
  · by_contra hn
    push Not at hn
    nlinarith
  · have : (x - rb_lam1 T D) * (x - rb_lam2 T D) =
        x ^ 2 - (rb_lam1 T D + rb_lam2 T D) * x + rb_lam1 T D * rb_lam2 T D := by ring
    rw [this, hsum, hprod]

/-- **The saddle property** (Miao, pp. 477–478): the matrix `M` of the deterministic system has
real eigenvalues `0 < λ₁ < 1 < λ₂` (roots of `λ² − tr M·λ + det M`), and `λ₁ < m₂₂ < λ₂`. -/
theorem rb_saddle_eigen {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    let T := rb_p α β ζ yk + rb_m22 α β ζ yk ck
    let D := rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk
    rb_lam1 T D + rb_lam2 T D = T ∧ rb_lam1 T D * rb_lam2 T D = D ∧ 0 < rb_lam1 T D ∧
      rb_lam1 T D < 1 ∧ 1 < rb_lam2 T D ∧ rb_lam1 T D < rb_m22 α β ζ yk ck ∧
      rb_m22 α β ζ yk ck < rb_lam2 T D := by
  intro T D
  obtain ⟨h1, hD, hm⟩ := rb_char_one_neg hα0 hα1 hβ0 hβ1 hζ hyk hck
  obtain ⟨hs, hp, hl0, hl1, hl2, hfac⟩ := rb_saddle_roots h1 hD
  have hneg : (rb_m22 α β ζ yk ck - rb_lam1 T D) * (rb_m22 α β ζ yk ck - rb_lam2 T D) < 0 := by
    rw [← hfac]
    nlinarith
  have hle : rb_lam1 T D ≤ rb_lam2 T D := by linarith
  refine ⟨hs, hp, hl0, hl1, hl2, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    nlinarith
  · by_contra hn
    push Not at hn
    nlinarith

/-! ### The saddle path of a `2 × 2` system -/

/-- The left eigenvector identity: if `l² − (m₁₁ + m₂₂)l + (m₁₁m₂₂ − m₁₂m₂₁) = 0`, then
`w = (l − m₂₂)k + m₁₂c` satisfies `w' = lw` along `x' = Mx`. -/
theorem rb_left_eig {m11 m12 m21 m22 l : ℝ}
    (hl : l ^ 2 - (m11 + m22) * l + (m11 * m22 - m12 * m21) = 0) (k c : ℝ) :
    (l - m22) * (m11 * k + m12 * c) + m12 * (m21 * k + m22 * c) =
      l * ((l - m22) * k + m12 * c) := by
  linear_combination (-k) * hl

/-- **The saddle path** of `x_{t+1} = Mx_t` (Miao, pp. 477–478). Let `λ₁ + λ₂ = m₁₁ + m₂₂`,
`λ₁λ₂ = m₁₁m₂₂ − m₁₂m₂₁`, `m₁₂ ≠ 0`, `|λ₁| < 1 < λ₂`, and `φ = (m₂₂ − λ₂)/m₁₂`. Then for
every `k₀`: (i) `k_t = λ₁ᵗk₀`, `c_t = φk_t` solves the system and tends to `0`; (ii) every
bounded solution with `k_0 = k₀` is this one. -/
theorem rb_saddle_det {m11 m12 m21 m22 l1 l2 : ℝ} (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) (hm12 : m12 ≠ 0) (hl1 : |l1| < 1)
    (hl2 : 1 < l2) (k0 : ℝ) :
    let φ := (m22 - l2) / m12
    ((∀ t : ℕ, l1 ^ (t + 1) * k0 = m11 * (l1 ^ t * k0) + m12 * (φ * (l1 ^ t * k0)) ∧
        φ * (l1 ^ (t + 1) * k0) = m21 * (l1 ^ t * k0) + m22 * (φ * (l1 ^ t * k0))) ∧
      Tendsto (fun t : ℕ => l1 ^ t * k0) atTop (𝓝 0)) ∧
      ∀ k c : ℕ → ℝ, k 0 = k0 →
        (∀ t, k (t + 1) = m11 * k t + m12 * c t ∧ c (t + 1) = m21 * k t + m22 * c t) →
        (∃ B, ∀ t, |k t| ≤ B ∧ |c t| ≤ B) → ∀ t, k t = l1 ^ t * k0 ∧ c t = φ * k t := by
  intro φ
  have hl2' : l2 ^ 2 - (m11 + m22) * l2 + (m11 * m22 - m12 * m21) = 0 := by
    rw [← hsum, ← hprod]; ring
  have hφ1 : m11 + m12 * φ = l1 := by
    simp only [φ]
    field_simp
    linarith
  have hφ2 : m21 + m22 * φ = φ * l1 := by
    simp only [φ]
    field_simp
    have : l1 = m11 + m22 - l2 := by linarith
    rw [this]
    linear_combination (-1) * hl2'
  refine ⟨⟨fun t => ⟨?_, ?_⟩, ?_⟩, fun k c hk0 hsys hB => ?_⟩
  · rw [pow_succ]
    linear_combination (-(l1 ^ t * k0)) * hφ1
  · rw [pow_succ]
    linear_combination (-(l1 ^ t * k0)) * hφ2
  · simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl1).mul_const k0
  · -- the unstable combination `w_t = (λ₂ − m₂₂)k_t + m₁₂c_t` grows like `λ₂ᵗ`
    set w : ℕ → ℝ := fun t => (l2 - m22) * k t + m12 * c t
    have hw : ∀ t, w t = l2 ^ t * w 0 := fun t => by
      induction t with
      | zero => simp
      | succ t ih =>
        have h := rb_left_eig hl2' (k t) (c t)
        simp only [w] at ih ⊢
        rw [(hsys t).1, (hsys t).2, h, ih, pow_succ]
        ring
    obtain ⟨B, hBt⟩ := hB
    have hw0 : w 0 = 0 := by
      by_contra hne
      have hbd : ∀ t, |w t| ≤ (|l2 - m22| + |m12|) * B := fun t => by
        simp only [w]
        calc |(l2 - m22) * k t + m12 * c t| ≤ |l2 - m22| * |k t| + |m12| * |c t| := by
              rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ |l2 - m22| * B + |m12| * B := by
              gcongr
              · exact (hBt t).1
              · exact (hBt t).2
          _ = _ := by ring
      have htend : Tendsto (fun t : ℕ => l2 ^ t * |w 0|) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt hl2).atTop_mul_const (abs_pos.2 hne)
      obtain ⟨t, ht⟩ := (htend.eventually_gt_atTop ((|l2 - m22| + |m12|) * B)).exists
      have := hbd t
      rw [hw t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
      linarith
    have hc : ∀ t, c t = φ * k t := fun t => by
      have h0 : w t = 0 := by rw [hw t, hw0, mul_zero]
      simp only [w, φ] at h0 ⊢
      field_simp
      linarith
    have hk : ∀ t, k t = l1 ^ t * k0 := fun t => by
      induction t with
      | zero => simp [hk0]
      | succ t ih =>
        rw [(hsys t).1, hc t, ih, pow_succ]
        linear_combination (l1 ^ t * k0) * hφ1
    exact fun t => ⟨hk t, hc t⟩

/-! ### A permanent TFP shock (p. 484) -/

/-- Miao, p. 484: with a permanent shock `ẑ_t = ẑ` and the steady-state relations
`1/β = αY/K + 1 − δ`, `C/K = Y/K − δ`, the point `K̂* = Ĉ* = ẑ/(1 − α)` is a steady state of
(14.32)–(14.33). -/
theorem rb_permanent_ss {α β δ ζ yk ck : ℝ} (hα1 : α < 1) (hαζ : α + ζ ≠ 0)
    (hβ : 1 / β = α * yk + 1 - δ) (hck : ck = yk - δ) (z : ℝ) :
    z / (1 - α) = rb_p α β ζ yk * (z / (1 - α)) + rb_g α ζ yk * z -
        rb_q α ζ yk ck * (z / (1 - α)) ∧
      -(z / (1 - α)) = -(1 + rb_a α β ζ yk) * (z / (1 - α)) + rb_b α β ζ yk * z -
        rb_c α β ζ yk * (z / (1 - α)) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have h2 : ζ + α ≠ 0 := by rwa [add_comm]
  constructor
  · rw [rb_p, hβ, rb_g, rb_q, hck]
    field_simp
    ring
  · rw [rb_a, rb_b, rb_c]
    field_simp
    ring

/-- Miao, p. 484: "both isoclines `ΔĈ_t = 0` and `ΔK̂_t = 0` shift up" with a permanent rise in
`ẑ`: the intercepts `(1 + ζ)/(1 − α)·ẑ` and `q⁻¹gẑ` increase with `ẑ`. -/
theorem rb_permanent_shift {α β ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck) :
    StrictMono (fun z : ℝ => (1 + ζ) / (1 - α) * z) ∧
      StrictMono (fun z : ℝ => (rb_q α ζ yk ck)⁻¹ * (rb_g α ζ yk * z)) := by
  obtain ⟨-, hq, -, -, -, hg⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have h1 : 0 < (1 + ζ) / (1 - α) := div_pos (by linarith) (by linarith)
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · simp only
    exact mul_lt_mul_of_pos_left hab h1
  · simp only
    exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hab hg) (inv_pos.2 hq)

/-- **The response to a permanent TFP shock** (Miao, p. 484, Figure 14.3). Let `ẑ_t = ẑ > 0`
for all `t`, `K̂₀ = 0`, with the steady-state relations of `rb_permanent_ss`. Write
`λ₁ < 1 < λ₂` for the eigenvalues of `M` and `φ = (λ₂ − m₂₂)/q > 0` for the slope of the saddle
path. Then `K̂_t = (1 − λ₁ᵗ)ẑ/(1 − α)`, `Ĉ_t = ẑ/(1 − α) − φλ₁ᵗẑ/(1 − α)` solves
(14.32)–(14.33); it is the unique bounded solution with `K̂₀ = 0`; capital and consumption rise
strictly along it (so the interest rate `r̂^f_{t+1} = Ĉ_{t+1} − Ĉ_t > 0`), and investment
`Î_t = (K̂_{t+1} − (1 − δ)K̂_t)/δ` is positive for `0 < δ ≤ 1`. -/
theorem rb_permanent_path {α β δ ζ yk ck : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 < ζ) (hyk : 0 < yk) (hck : 0 < ck)
    (hβ : 1 / β = α * yk + 1 - δ) (hck' : ck = yk - δ) {z : ℝ} (hz : 0 < z) :
    let T := rb_p α β ζ yk + rb_m22 α β ζ yk ck
    let D := rb_p α β ζ yk * rb_m22 α β ζ yk ck - (-rb_q α ζ yk ck) * rb_m21 α β ζ yk
    let l1 := rb_lam1 T D
    let φ := (rb_lam2 T D - rb_m22 α β ζ yk ck) / rb_q α ζ yk ck
    let K : ℕ → ℝ := fun t => (1 - l1 ^ t) * (z / (1 - α))
    let C : ℕ → ℝ := fun t => z / (1 - α) - φ * (l1 ^ t * (z / (1 - α)))
    0 < φ ∧
      (∀ t, K (t + 1) = rb_p α β ζ yk * K t + rb_g α ζ yk * z - rb_q α ζ yk ck * C t ∧
        -C t = -(1 + rb_a α β ζ yk) * C (t + 1) + rb_b α β ζ yk * z -
          rb_c α β ζ yk * K (t + 1)) ∧
      (∀ K' C' : ℕ → ℝ, K' 0 = 0 →
        (∀ t, K' (t + 1) = rb_p α β ζ yk * K' t + rb_g α ζ yk * z - rb_q α ζ yk ck * C' t ∧
          -C' t = -(1 + rb_a α β ζ yk) * C' (t + 1) + rb_b α β ζ yk * z -
            rb_c α β ζ yk * K' (t + 1)) →
        (∃ B, ∀ t, |K' t| ≤ B ∧ |C' t| ≤ B) → K' = K ∧ C' = C) ∧
      StrictMono K ∧ StrictMono C ∧ (∀ t, 0 < C (t + 1) - C t) ∧
      (∀ t, 0 < (K (t + 1) - (1 - δ) * K t) / δ) := by
  intro T D l1 φ K C
  obtain ⟨hp, hq, ha, -, hc, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have ha' : 1 + rb_a α β ζ yk ≠ 0 := by linarith
  obtain ⟨hs, hpr, hl0, hl1, hl2, hlm, hml⟩ := rb_saddle_eigen hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hαζ : α + ζ ≠ 0 := by linarith
  obtain ⟨hss1, hss2⟩ := rb_permanent_ss (z := z) (yk := yk) (ck := ck) hα1 hαζ hβ hck'
  have hz1 : 0 < z / (1 - α) := div_pos hz (by linarith)
  have hφ : 0 < φ := div_pos (by linarith) hq
  -- the deviations from the new steady state solve the homogeneous system
  have hM := rb_saddle_det (m11 := rb_p α β ζ yk) (m12 := -rb_q α ζ yk ck)
    (m21 := rb_m21 α β ζ yk) (m22 := rb_m22 α β ζ yk ck) hs hpr (neg_ne_zero.2 hq.ne')
    (by rw [abs_of_pos hl0]; exact hl1) hl2 (-(z / (1 - α)))
  have hφ' : (rb_m22 α β ζ yk ck - rb_lam2 T D) / -rb_q α ζ yk ck = φ := by
    simp only [φ]
    rw [div_neg, ← neg_div, neg_sub]
  obtain ⟨⟨hsol, -⟩, huniq⟩ := hM
  -- from the matrix form back to (14.32)–(14.33)
  have hback : ∀ k c k' c' : ℝ, k' = rb_p α β ζ yk * k + (-rb_q α ζ yk ck) * c →
      c' = rb_m21 α β ζ yk * k + rb_m22 α β ζ yk ck * c →
      k' = rb_p α β ζ yk * k - rb_q α ζ yk ck * c ∧
        -c = -(1 + rb_a α β ζ yk) * c' - rb_c α β ζ yk * k' := fun k c k' c' h1 h2 => by
    refine ⟨by linarith, ?_⟩
    rw [h2, h1, rb_m21, rb_m22]
    field_simp
    ring
  have hfwd : ∀ k c k' c' : ℝ, k' = rb_p α β ζ yk * k - rb_q α ζ yk ck * c →
      -c = -(1 + rb_a α β ζ yk) * c' - rb_c α β ζ yk * k' →
      k' = rb_p α β ζ yk * k + (-rb_q α ζ yk ck) * c ∧
        c' = rb_m21 α β ζ yk * k + rb_m22 α β ζ yk ck * c := fun k c k' c' h1 h2 => by
    refine ⟨by linarith, ?_⟩
    have := rb_det_system (c := c) (c' := c') (k := k) (k' := k') (z := 0) (z' := 0) ha'
      (by rw [h1]; ring) (by linarith)
    simpa using this
  have hKd : ∀ t, K t = z / (1 - α) + l1 ^ t * (-(z / (1 - α))) := fun t => by
    simp only [K]; ring
  have hCd : ∀ t, C t = z / (1 - α) + φ * (l1 ^ t * (-(z / (1 - α)))) := fun t => by
    simp only [C]; ring
  have hsys : ∀ t, K (t + 1) = rb_p α β ζ yk * K t + rb_g α ζ yk * z -
      rb_q α ζ yk ck * C t ∧ -C t = -(1 + rb_a α β ζ yk) * C (t + 1) + rb_b α β ζ yk * z -
        rb_c α β ζ yk * K (t + 1) := fun t => by
    obtain ⟨e1, e2⟩ := hback _ _ _ _ (hsol t).1 (hsol t).2
    rw [hKd, hKd, hCd, hCd]
    constructor
    · linear_combination e1 + hss1
    · linear_combination e2 + hss2
  refine ⟨hφ, hsys, fun K' C' hK0 hsys' hB => ?_, ?_, ?_, ?_, ?_⟩
  · -- uniqueness: the deviations are a bounded solution of the homogeneous system
    obtain ⟨B, hB⟩ := hB
    have hu := huniq (fun t => K' t - z / (1 - α)) (fun t => C' t - z / (1 - α))
      (by simp [hK0]) (fun t => by
        obtain ⟨e1, e2⟩ := hsys' t
        have e1' : K' (t + 1) - z / (1 - α) = rb_p α β ζ yk * (K' t - z / (1 - α)) -
            rb_q α ζ yk ck * (C' t - z / (1 - α)) := by linear_combination e1 - hss1
        have e2' : -(C' t - z / (1 - α)) = -(1 + rb_a α β ζ yk) * (C' (t + 1) - z / (1 - α)) -
            rb_c α β ζ yk * (K' (t + 1) - z / (1 - α)) := by linear_combination e2 - hss2
        exact hfwd _ _ _ _ e1' e2')
      ⟨B + |z / (1 - α)|, fun t => ⟨(abs_sub _ _).trans (by linarith [(hB t).1]),
        (abs_sub _ _).trans (by linarith [(hB t).2])⟩⟩
    refine ⟨funext fun t => ?_, funext fun t => ?_⟩
    · have := (hu t).1
      rw [hKd]
      linarith
    · have h1 := (hu t).1
      have e : C' t - z / (1 - α) = φ * (K' t - z / (1 - α)) := by rw [(hu t).2, ← hφ']
      rw [hCd, ← h1]
      linarith
  · refine strictMono_nat_of_lt_succ fun t => ?_
    simp only [K]
    have : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    nlinarith
  · refine strictMono_nat_of_lt_succ fun t => ?_
    simp only [C]
    have : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    have : 0 < φ * ((l1 ^ t - l1 ^ (t + 1)) * (z / (1 - α))) := by
      apply mul_pos hφ (mul_pos (by linarith) hz1)
    nlinarith
  · intro t
    simp only [C]
    have : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    have : 0 < φ * ((l1 ^ t - l1 ^ (t + 1)) * (z / (1 - α))) := by
      apply mul_pos hφ (mul_pos (by linarith) hz1)
    nlinarith
  · intro t
    apply div_pos _ hδ0
    simp only [K]
    have h1 : l1 ^ (t + 1) < l1 ^ t := pow_lt_pow_right_of_lt_one₀ hl0 hl1 (Nat.lt_succ_self t)
    have h2 : l1 ^ t ≤ 1 := pow_le_one₀ hl0.le hl1.le
    have h3 : 0 ≤ 1 - δ := by linarith
    have : (1 - δ) * ((1 - l1 ^ t) * (z / (1 - α))) ≤ (1 - l1 ^ t) * (z / (1 - α)) := by
      have : 0 ≤ (1 - l1 ^ t) * (z / (1 - α)) := mul_nonneg (by linarith) hz1.le
      nlinarith
    nlinarith

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stochastic saddle path of the log-linearised RBC model (Blanchard–Kahn)

Miao, §14.2, pp. 476–478: "Equations (14.32) and (14.33) combined with the shock process in
(14.25) constitute a linear system of difference equations for `{Ĉ_t, K̂_{t+1}}` ... Given any
initial state for `K̂₀` and `ẑ₀`, there is a unique solution `Ĉ₀`, which must lie on the saddle."
Here this is the stochastic Theorem 1.4.2 of Chapter 2 (`bkS_exists`, `bkS_unique`) applied to
the RBC system, with `E_t` a conditional expectation system (`CondExpSystem`) on a real Banach
space `V` (e.g. `L¹`).

* `rb_split2`: an explicit real block split of a `2 × 2` saddle matrix `[[m₁₁, m₁₂], [m₂₁, m₂₂]]`
  with eigenvalues `|λ₁| < 1 < λ₂` (left eigenvectors `(λᵢ − m₂₂, m₁₂)`).
* `rb_bk_iff`: with `K̂` predetermined and `E_tẑ_{t+1} = ρẑ_t` (from (14.25)), (14.32)–(14.33)
  are equivalent to `E_tx_{t+1} = Wx_t + Gẑ_t` for `x = (K̂, Ĉ)`, `W` the matrix of
  `RBSaddle` and `G = (g, (bρ − cg)/(1 + a))`.
* **`rb_saddle_stoch`**: for every `F₀`-measurable `K̂₀` and every stable adapted `ẑ` with
  `E_tẑ_{t+1} = ρẑ_t`, there is exactly one stable adapted solution `(K̂, Ĉ)` of (14.32)–(14.33)
  with `K̂` predetermined and the given `K̂₀`.
-/

namespace Miao.NeoclassicalGrowth

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A `2 × 2` matrix in the block form of Chapter 2 (`k = Fin 1`, `y = Fin 1`). -/
noncomputable def rb_W2 (m11 m12 m21 m22 : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![m11] !![m12] !![m21] !![m22]

/-- The rows `(λ₁ − m₂₂, m₁₂)` (stable) and `(λ₂ − m₂₂, m₁₂)` (unstable): left eigenvectors. -/
noncomputable def rb_P2 (m12 m22 l1 l2 : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![l1 - m22] !![m12] !![l2 - m22] !![m12]

/-- The inverse of `rb_P2`. -/
noncomputable def rb_R2 (m12 m22 l1 l2 : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks !![m12 / (m12 * (l1 - l2))] !![-m12 / (m12 * (l1 - l2))]
    !![-(l2 - m22) / (m12 * (l1 - l2))] !![(l1 - m22) / (m12 * (l1 - l2))]

/-- A real block split of a `2 × 2` saddle matrix (Miao, pp. 53–54 applied on p. 478): if
`λ₁ + λ₂ = m₁₁ + m₂₂`, `λ₁λ₂ = m₁₁m₂₂ − m₁₂m₂₁`, `m₁₂ ≠ 0`, `|λ₁| < 1 < λ₂`, then
`PWP⁻¹ = diag(λ₁, λ₂)` with `n_s = n_u = 1`. -/
theorem rb_split2 {m11 m12 m21 m22 l1 l2 : ℝ} (hsum : l1 + l2 = m11 + m22)
    (hprod : l1 * l2 = m11 * m22 - m12 * m21) (hm12 : m12 ≠ 0) (hl1 : |l1| < 1)
    (hl2 : 1 < l2) :
    IsRealBlockSplit (rb_W2 m11 m12 m21 m22) (rb_P2 m12 m22 l1 l2) (rb_R2 m12 m22 l1 l2)
      !![l1] !![l2] := by
  have hd : l1 - l2 ≠ 0 := by
    have := (abs_lt.1 hl1).2
    linarith
  obtain rfl : m22 = l1 + l2 - m11 := by linarith
  obtain rfl : m21 = (m11 * (l1 + l2 - m11) - l1 * l2) / m12 := by
    field_simp
    linarith
  refine ⟨?_, ?_, ?_, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [rb_P2, rb_R2, Matrix.mul_apply, Fintype.sum_sum_type] <;>
      field_simp <;> ring
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [rb_P2, rb_R2, Matrix.mul_apply, Fintype.sum_sum_type] <;>
      field_simp <;> ring
  · ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [rb_P2, rb_W2, Matrix.mul_apply, Fintype.sum_sum_type] <;>
      field_simp <;> ring
  · rw [nk_scalar_eig hμ, Complex.norm_real, Real.norm_eq_abs]
    exact hl1
  · rw [nk_scalar_eig hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hl2

/-- The forcing matrix `G = (g, h)` of the shock `ẑ_t`. -/
noncomputable def rb_G2 (g h : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ :=
  Matrix.of fun i _ => Sum.elim (fun _ => g) (fun _ => h) i

/-- The log-linearised RBC system (14.32)–(14.33) at date `t` for `V`-valued `x = (K̂, Ĉ)` and
shock `ẑ`. -/
def rb_IsLinRBC (E : CondExpSystem ℝ V) (α β ζ yk ck : ℝ) (z : ℕ → Fin 1 → V)
    (x : ℕ → Fin 1 ⊕ Fin 1 → V) (t : ℕ) : Prop :=
  x (t + 1) (Sum.inl 0) = rb_p α β ζ yk • x t (Sum.inl 0) + rb_g α ζ yk • z t 0 -
      rb_q α ζ yk ck • x t (Sum.inr 0) ∧
    -x t (Sum.inr 0) = -(1 + rb_a α β ζ yk) • E.E t (x (t + 1) (Sum.inr 0)) +
      rb_b α β ζ yk • E.E t (z (t + 1) 0) - rb_c α β ζ yk • E.E t (x (t + 1) (Sum.inl 0))

/-- The matrices `W`, `G` of the RBC system in the form `E_tx_{t+1} = Wx_t + Gẑ_t`. -/
noncomputable def rb_Wrbc (α β ζ yk ck : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  rb_W2 (rb_p α β ζ yk) (-rb_q α ζ yk ck) (rb_m21 α β ζ yk) (rb_m22 α β ζ yk ck)

/-- `G = (g, (bρ − cg)/(1 + a))`. -/
noncomputable def rb_Grbc (α β ζ yk ρ : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ :=
  rb_G2 (rb_g α ζ yk)
    ((rb_b α β ζ yk * ρ - rb_c α β ζ yk * rb_g α ζ yk) / (1 + rb_a α β ζ yk))

theorem rb_matAct_W2 (m11 m12 m21 m22 : ℝ) (x : Fin 1 ⊕ Fin 1 → V) :
    matAct (rb_W2 m11 m12 m21 m22) x (Sum.inl 0) = m11 • x (Sum.inl 0) + m12 • x (Sum.inr 0) ∧
      matAct (rb_W2 m11 m12 m21 m22) x (Sum.inr 0) =
        m21 • x (Sum.inl 0) + m22 • x (Sum.inr 0) := by
  simp [matAct, rb_W2, Fintype.sum_sum_type]

theorem rb_matAct_G2 (g h : ℝ) (z : Fin 1 → V) :
    matAct (rb_G2 g h) z (Sum.inl 0) = g • z 0 ∧ matAct (rb_G2 g h) z (Sum.inr 0) = h • z 0 := by
  simp [matAct, rb_G2]

/-- Miao, pp. 476–477: with `K̂_{t+1}` known at `t` and `E_tẑ_{t+1} = ρẑ_t`, (14.32)–(14.33)
at date `t` are equivalent to `E_tx_{t+1} = Wx_t + Gẑ_t`. -/
theorem rb_bk_iff (E : CondExpSystem ℝ V) {α β ζ yk ck ρ : ℝ} (ha : 1 + rb_a α β ζ yk ≠ 0)
    {z : ℕ → Fin 1 → V} {x : ℕ → Fin 1 ⊕ Fin 1 → V} (t : ℕ)
    (hz : E.E t (z (t + 1) 0) = ρ • z t 0)
    (hk : E.E t (x (t + 1) (Sum.inl 0)) = x (t + 1) (Sum.inl 0)) :
    Evec E t (x (t + 1)) = matAct (rb_Wrbc α β ζ yk ck) (x t) +
        matAct (rb_Grbc α β ζ yk ρ) (z t) ↔ rb_IsLinRBC E α β ζ yk ck z x t := by
  obtain ⟨hW1, hW2⟩ := rb_matAct_W2 (rb_p α β ζ yk) (-rb_q α ζ yk ck) (rb_m21 α β ζ yk)
    (rb_m22 α β ζ yk ck) (x t)
  obtain ⟨hG1, hG2⟩ := rb_matAct_G2 (V := V) (rb_g α ζ yk)
    ((rb_b α β ζ yk * ρ - rb_c α β ζ yk * rb_g α ζ yk) / (1 + rb_a α β ζ yk)) (z t)
  have hfun : ∀ u v : Fin 1 ⊕ Fin 1 → V, u = v ↔ u (Sum.inl 0) = v (Sum.inl 0) ∧
      u (Sum.inr 0) = v (Sum.inr 0) := fun u v => by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      funext i
      rcases i with i | i <;> fin_cases i
      · exact h1
      · exact h2
  rw [hfun]
  simp only [Evec, Pi.add_apply, rb_Wrbc, rb_Grbc, hW1, hW2, hG1, hG2, hk, rb_IsLinRBC, hz]
  set K := x t (Sum.inl 0)
  set C := x t (Sum.inr 0)
  set K' := x (t + 1) (Sum.inl 0)
  set EC := E.E t (x (t + 1) (Sum.inr 0))
  set Z := z t 0
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : K' = rb_p α β ζ yk • K + rb_g α ζ yk • Z - rb_q α ζ yk ck • C := by
      rw [h1]; module
    refine ⟨h1', ?_⟩
    rw [h2, h1', rb_m21, rb_m22]
    match_scalars <;> field_simp <;> ring
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1]; module, ?_⟩
    rw [h1] at h2
    have h3 : EC = (1 + rb_a α β ζ yk)⁻¹ • ((1 + rb_a α β ζ yk) • EC) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    have h4 : (1 + rb_a α β ζ yk) • EC = C + rb_b α β ζ yk • ρ • Z -
        rb_c α β ζ yk • (rb_p α β ζ yk • K + rb_g α ζ yk • Z - rb_q α ζ yk ck • C) := by
      have : (1 + rb_a α β ζ yk) • EC = -(-(1 + rb_a α β ζ yk) • EC) := by module
      rw [this]
      have h5 : -(1 + rb_a α β ζ yk) • EC = -C - rb_b α β ζ yk • ρ • Z +
          rb_c α β ζ yk • (rb_p α β ζ yk • K + rb_g α ζ yk • Z - rb_q α ζ yk ck • C) := by
        rw [h2]; module
      rw [h5]
      module
    rw [h3, h4, rb_m21, rb_m22]
    match_scalars <;> field_simp
    ring

/-- **The stochastic saddle path** (Miao, pp. 476–478, via the stochastic Blanchard–Kahn
Theorem 1.4.2 of Chapter 2). Let `0 < α < 1`, `0 < β < 1`, `ζ, Y/K, C/K > 0`. For every
`F₀`-measurable `K̂₀` and every stable adapted shock `ẑ` with `E_tẑ_{t+1} = ρẑ_t`, there is exactly
one stable adapted process `x = (K̂, Ĉ)` with `K̂` predetermined and `K̂_0 = K̂₀` satisfying
(14.32)–(14.33) at every date. -/
theorem rb_saddle_stoch [CompleteSpace V] (E : CondExpSystem ℝ V) {α β ζ yk ck ρ : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hζ : 0 < ζ) (hyk : 0 < yk)
    (hck : 0 < ck) {z : ℕ → Fin 1 → V} (hzs : IsStableProc z) (hza : IsAdaptedV E z)
    (hz : ∀ t, E.E t (z (t + 1) 0) = ρ • z t 0) (k₀ : V) (hk₀ : E.E 0 k₀ = k₀) :
    ∃! x : ℕ → Fin 1 ⊕ Fin 1 → V, (∀ t, rb_IsLinRBC E α β ζ yk ck z x t) ∧
      IsAdaptedV E x ∧ IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ IsStableProc x ∧
      x 0 (Sum.inl 0) = k₀ := by
  obtain ⟨-, -, ha, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have ha' : 1 + rb_a α β ζ yk ≠ 0 := by linarith
  obtain ⟨hs, hpr, hl0, hl1, hl2, -, -⟩ := rb_saddle_eigen hα0 hα1 hβ0 hβ1 hζ hyk hck
  obtain ⟨-, hq, -⟩ := rb_coeff_pos hα0 hα1 hβ0 hβ1 hζ hyk hck
  have hm12 : -rb_q α ζ yk ck ≠ 0 := neg_ne_zero.2 hq.ne'
  have hS := rb_split2 hs hpr hm12 (by rw [abs_of_pos hl0]; exact hl1) hl2
  set P := rb_P2 (-rb_q α ζ yk ck) (rb_m22 α β ζ yk ck) _ _
  have hP22 : P.toBlocks₂₂ = !![-rb_q α ζ yk ck] := by
    simp [P, rb_P2]
  set Q : Matrix (Fin 1) (Fin 1) ℝ := !![(-rb_q α ζ yk ck)⁻¹]
  have hQ1 : P.toBlocks₂₂ * Q = 1 := by
    rw [hP22]
    ext i j
    fin_cases i; fin_cases j
    simp [Q, hq.ne']
  have hQ2 : Q * P.toBlocks₂₂ = 1 := by
    rw [hP22]
    ext i j
    fin_cases i; fin_cases j
    simp [Q, hq.ne']
  -- the set of solutions coincides with the stable solutions of the Blanchard–Kahn system
  have hiff : ∀ x : ℕ → Fin 1 ⊕ Fin 1 → V,
      ((∀ t, rb_IsLinRBC E α β ζ yk ck z x t) ∧ IsAdaptedV E x ∧
        IsPredeterminedBK E (fun t => x t ∘ Sum.inl) ∧ IsStableProc x ∧
        x 0 (Sum.inl 0) = k₀) ↔
      (bkS_IsStableSol E (rb_Wrbc α β ζ yk ck) (rb_Grbc α β ζ yk ρ) z x ∧
        x 0 ∘ Sum.inl = fun _ => k₀) := fun x => by
    have h0 : x 0 ∘ Sum.inl = (fun _ : Fin 1 => k₀) ↔ x 0 (Sum.inl 0) = k₀ := by
      constructor
      · intro h; exact congrFun h 0
      · intro h; funext i; fin_cases i; exact h
    rw [h0, bkS_IsStableSol]
    constructor
    · rintro ⟨hsys, hxa, hxp, hxs, hx0⟩
      exact ⟨⟨fun t => (rb_bk_iff E ha' t (hz t) (hxp t 0)).2 (hsys t), hxa, hxp, hxs⟩, hx0⟩
    · rintro ⟨⟨hsys, hxa, hxp, hxs⟩, hx0⟩
      exact ⟨fun t => (rb_bk_iff E ha' t (hz t) (hxp t 0)).1 (hsys t), hxa, hxp, hxs, hx0⟩
  obtain ⟨x, hx, hx0⟩ := bkS_exists E hS Q hQ1 (rb_Grbc α β ζ yk ρ) hzs hza
    (fun _ : Fin 1 => k₀) (fun _ => hk₀)
  refine ⟨x, (hiff x).2 ⟨hx, hx0⟩, fun y hy => ?_⟩
  obtain ⟨hy, hy0⟩ := (hiff y).1 hy
  exact bkS_unique E hS Q hQ2 (rb_Grbc α β ζ yk ρ) hzs hza hy hx (hy0.trans hx0.symm)

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Various utility functions in the RBC model

Miao, §14.3.1, pp. 487–493.

* **KPR utility** (14.38) `u(c, n) = (c(1 − n)^χ)^{1−γ}/(1 − γ)` (`rb_u38`) is of the King–Plosser–
  Rebelo form (14.5) `c^{1−γ}v(n)/(1 − γ)` with `v(n) = (1 − n)^{χ(1−γ)}` (`rb_u38_kpr`), and
  (14.39) `ln c − χn^{1+ν}/(1 + ν)` (`rb_u39`) is of the form (14.6) (`rb_u39_kpr`).
* "When `γ = 1`, (14.38) reduces to (14.22)": corrected, `((c(1 − n)^χ)^{1−γ} − 1)/(1 − γ)`
  (which differs from (14.38) by the constant `1/(1 − γ)`, hence represents the same preferences)
  tends to `ln c + χ ln(1 − n)` as `γ → 1` (`rb_u38_limit`); (14.38) as printed has no limit at
  `γ = 1` (`rb_u38_printed_no_limit`).
* Marginal utilities and the marginal rate of substitution of (14.38):
  `u_c = c^{−γ}(1 − n)^{χ(1−γ)}`, `u_n = −χc^{1−γ}(1 − n)^{χ(1−γ)−1}`, `−u_n/u_c = χc/(1 − n)`
  for every `γ` (`rb_u38_uc`, `rb_u38_un`, `rb_u38_mrs`), so the intratemporal condition is
  (14.27) and the steady state and the calibrated `χ` do not depend on `γ` ("we still obtain
  `χ = 1.75`", `rb_u38_intratemporal`).
* Balanced growth (the KPR class): `u_c(gc, n) = g^{−γ}u_c(c, n)` and the MRS is homogeneous of
  degree one in `c` (`rb_u38_homog`); along `c_t = gᵗc₀`, `w_t = gᵗw₀`, `n` constant, the
  intratemporal condition holds at all dates iff at date 0, and the Euler equation holds with
  the constant gross return `R = g^γ/β` (`rb_u38_bgp`). For (14.39), `u_c = 1/c` and the MRS is
  `χn^νc` (`rb_u39_mrs`), also homogeneous of degree one in `c`.
* The Frisch elasticity of (14.39) is `1/ν` (`rb_u39_frisch`): with marginal utility `λ` held
  fixed, `χn^ν = λw` gives `n = (λw/χ)^{1/ν}` and `d ln n/d ln w = 1/ν`.
* **Indivisible labour** (`ν = 0`; Hansen (1985), Rogerson (1988)): with lotteries over working
  `n̄` hours or not, full insurance is optimal and the representative household's expected
  utility is `ln c − BN`, `N = pn̄`, `B = −χ ln(1 − n̄)/n̄ > 0`: (14.39) with `ν = 0`
  (`rb_lottery`).
* Labour-market comparative statics: with (14.39) the log-linearised supply is `νN̂ = ŵ − Ĉ`
  (`rb_u39_supply_loglin`); at given `Ĉ`, `K̂` the hours response to `ẑ` is `1/(α + ν)` (largest
  for indivisible labour) and the wage response is `ν/(α + ν)` (zero for `ν = 0`)
  (`rb_nu_responses`); a larger consumption response lowers hours and output and raises the
  wage (`rb_consumption_channel`, the intuition for Figure 14.7).
* **GHH utility** (14.40) `U(c − G(n))`: `−u_n/u_c = G′(n)` (`rb_ghh_mrs`), independent of `c`
  (no wealth effect), so hours solve `G′(n) = (1 − α)zK^αn^{−α}`, uniquely if `G′` is increasing
  (`rb_ghh_hours`); GHH preferences are outside the KPR class: the MRS is not homogeneous of
  degree one in `c` (`rb_ghh_not_kpr`).
* **Habit formation**: marginal utility `Λ_t = 1/(C_t − bC_{t−1}) − βbE_t[1/(C_{t+1} − bC_t)]`
  is the derivative of lifetime utility in `C_t` (`rb_habit_mu`, finitely many successor states).
-/

open Filter Topology

namespace Miao.NeoclassicalGrowth

/-! ### KPR utility (14.38)–(14.39) -/

/-- Miao, (14.38), p. 488: `u(c, n) = (c(1 − n)^χ)^{1−γ}/(1 − γ)`. -/
noncomputable def rb_u38 (γ χ c n : ℝ) : ℝ := (c * (1 - n) ^ χ) ^ (1 - γ) / (1 - γ)

/-- Miao, (14.39), p. 488: `u(c, n) = ln c − χn^{1+ν}/(1 + ν)`. -/
noncomputable def rb_u39 (ν χ c n : ℝ) : ℝ := Real.log c - χ * n ^ (1 + ν) / (1 + ν)

/-- Miao, p. 488: (14.38) is of the KPR form (14.5) `c^{1−γ}v(n)/(1 − γ)` with
`v(n) = (1 − n)^{χ(1−γ)}`. -/
theorem rb_u38_kpr (γ χ : ℝ) {c n : ℝ} (hc : 0 ≤ c) (hn : n ≤ 1) :
    rb_u38 γ χ c n = c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ)) / (1 - γ) := by
  rw [rb_u38, Real.mul_rpow hc (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith)]

/-- Miao, p. 488: (14.39) is of the KPR form (14.6) `ln c + v(n)` with
`v(n) = −χn^{1+ν}/(1 + ν)`. -/
theorem rb_u39_kpr (ν χ c n : ℝ) :
    rb_u39 ν χ c n = Real.log c + (fun m => -(χ * m ^ (1 + ν) / (1 + ν))) n := by
  simp only [rb_u39]
  ring

/-- Miao, p. 489, corrected: as `γ → 1`, `((c(1 − n)^χ)^{1−γ} − 1)/(1 − γ)`, which differs from
(14.38) by the constant `1/(1 − γ)`, tends to `ln c + χ ln(1 − n)`, the period utility of
(14.22). -/
theorem rb_u38_limit (χ : ℝ) {c n : ℝ} (hc : 0 < c) (hn : n < 1) :
    Tendsto (fun γ => (rb_u38 γ χ c n - 1 / (1 - γ))) (𝓝[≠] 1)
      (𝓝 (Real.log c + χ * Real.log (1 - n))) := by
  set x := c * (1 - n) ^ χ
  have hx : 0 < x := mul_pos hc (Real.rpow_pos_of_pos (by linarith) _)
  have hlog : Real.log x = Real.log c + χ * Real.log (1 - n) := by
    rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)]
  -- the derivative of `h ↦ x^h = exp(h ln x)` at `0` is `ln x`
  have hd : HasDerivAt (fun h => Real.exp (h * Real.log x)) (Real.log x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log x)).exp
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  have hmap : Tendsto (fun γ : ℝ => 1 - γ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun γ : ℝ => 1 - γ) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with γ hγ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hγ ⊢
      intro h
      exact hγ (by linarith)
  rw [← hlog]
  refine (hs.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with γ hγ
  simp only [Function.comp_apply, slope_def_field, zero_mul, Real.exp_zero, sub_zero, rb_u38]
  rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
  ring

/-- Miao, p. 489: the printed claim that (14.38) "reduces to" (14.22) at `γ = 1` cannot be read
as a limit: at `c = 1`, `n = 0`, (14.38) equals `1/(1 − γ)`, which has no finite limit as
`γ → 1`. -/
theorem rb_u38_printed_no_limit (χ L : ℝ) :
    ¬ Tendsto (fun γ => rb_u38 γ χ 1 0) (𝓝[≠] 1) (𝓝 L) := by
  intro h
  have h1 : Tendsto (fun γ => rb_u38 γ χ 1 0) (𝓝[>] 1) (𝓝 L) :=
    h.mono_left (nhdsWithin_mono _ fun γ hγ => ne_of_gt hγ)
  have hbot : Tendsto (fun γ : ℝ => rb_u38 γ χ 1 0) (𝓝[>] 1) atBot := by
    have hm : Tendsto (fun γ : ℝ => 1 - γ) (𝓝[>] 1) (𝓝[<] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun γ : ℝ => 1 - γ) (𝓝 1) (𝓝 (1 - 1)) :=
          (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with γ hγ
        simp only [Set.mem_Ioi] at hγ
        simp only [Set.mem_Iio]
        linarith
    refine (tendsto_inv_nhdsLT_zero.comp hm).congr' (Eventually.of_forall fun γ => ?_)
    simp [rb_u38]
  exact not_tendsto_nhds_of_tendsto_atBot hbot L h1

/-- The marginal utility of consumption under (14.38): `u_c = c^{−γ}(1 − n)^{χ(1−γ)}`. -/
theorem rb_u38_uc {γ χ c n : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) (hn : n < 1) :
    HasDerivAt (fun c' => rb_u38 γ χ c' n) (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) c := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hd := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hc.ne')).mul_const
    ((1 - n) ^ (χ * (1 - γ)))).div_const (1 - γ)
  have heq : (fun c' => rb_u38 γ χ c' n) =ᶠ[𝓝 c]
      fun c' => c' ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ)) / (1 - γ) := by
    filter_upwards [lt_mem_nhds hc] with c' hc'
    exact rb_u38_kpr γ χ hc'.le hn.le
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- The marginal (dis)utility of labour under (14.38):
`u_n = −χc^{1−γ}(1 − n)^{χ(1−γ)−1}`. -/
theorem rb_u38_un {γ χ c n : ℝ} (hγ : γ ≠ 1) (hc : 0 ≤ c) (hn : n < 1) :
    HasDerivAt (fun n' => rb_u38 γ χ c n')
      (-(χ * c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ) - 1))) n := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have hd := ((((hasDerivAt_id n).const_sub 1).rpow_const (p := χ * (1 - γ))
    (Or.inl (by simp; linarith))).const_mul (c ^ (1 - γ))).div_const (1 - γ)
  have heq : (fun n' => rb_u38 γ χ c n') =ᶠ[𝓝 n]
      fun n' => c ^ (1 - γ) * (1 - id n') ^ (χ * (1 - γ)) / (1 - γ) := by
    filter_upwards [gt_mem_nhds hn] with n' hn'
    exact rb_u38_kpr γ χ hc hn'.le
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [id]
  field_simp

/-- Miao, p. 489: under (14.38) the marginal rate of substitution is `−u_n/u_c = χc/(1 − n)` for
every `γ ≠ 1`, the same as under (14.22). -/
theorem rb_u38_mrs {γ χ c n : ℝ} (hc : 0 < c) (hn : n < 1) :
    χ * c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ) - 1) / (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) =
      χ * c / (1 - n) := by
  have h1n : 0 < 1 - n := by linarith
  rw [Real.rpow_sub h1n, Real.rpow_one, show 1 - γ = 1 + -γ by ring, Real.rpow_add hc,
    Real.rpow_one]
  have := Real.rpow_pos_of_pos hc (-γ)
  have := Real.rpow_pos_of_pos h1n (χ * (1 + -γ))
  field_simp

/-- Miao, p. 489 ("using the previous calibration strategy, we still obtain `χ = 1.75` in
(14.38)"): under (14.38) the intratemporal condition `−u_n/u_c = w` with `w` the marginal
product of labour is exactly (14.27), whatever `γ`; the steady-state Euler equation
`u_c = βu_c(R_k + 1 − δ)` at constant `(c, n)` is `1 = β(R_k + 1 − δ)`. Hence the steady state
and the calibrated `χ` (`RBSteadyState`) do not depend on `γ`. -/
theorem rb_u38_intratemporal {α β δ γ χ z K c n Rk : ℝ} (hc : 0 < c) (hn : n < 1) :
    (χ * c ^ (1 - γ) * (1 - n) ^ (χ * (1 - γ) - 1) / (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) =
        rb_MPL α z K n ↔ eq_14_27 α χ z K c n) ∧
      (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) =
          β * (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) * (Rk + 1 - δ) ↔ 1 = β * (Rk + 1 - δ)) := by
  refine ⟨by rw [rb_u38_mrs hc hn, eq_14_27], ?_⟩
  have hu : 0 < c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) :=
    mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos (by linarith) _)
  constructor
  · intro h
    have : c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * 1 =
        c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * (β * (Rk + 1 - δ)) := by linarith
    exact mul_left_cancel₀ hu.ne' this
  · intro h
    calc c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) = c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * 1 :=
          (mul_one _).symm
      _ = c ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * (β * (Rk + 1 - δ)) := by rw [← h]
      _ = _ := by ring

/-- Balanced growth (Miao, pp. 459 and 488, the KPR class): under (14.38),
`u_c(gc, n) = g^{−γ}u_c(c, n)` and `MRS(gc, n) = g·MRS(c, n)`. -/
theorem rb_u38_homog {γ χ g c n : ℝ} (hg : 0 < g) (hc : 0 < c) :
    (g * c) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) = g ^ (-γ) * (c ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) ∧
      χ * (g * c) / (1 - n) = g * (χ * c / (1 - n)) := by
  refine ⟨?_, by ring⟩
  rw [Real.mul_rpow hg.le hc.le]
  ring

/-- Balanced growth path under (14.38): with `n` constant, `c_t = gᵗc₀` and `w_t = gᵗw₀`
(`g > 0`), the intratemporal condition `χc_t/(1 − n) = w_t` holds at every date iff it holds at
date `0`, and the Euler equation `u_c(c_t, n) = βu_c(c_{t+1}, n)R` holds at every date iff
`R = g^γ/β`. -/
theorem rb_u38_bgp {β γ χ g c0 w0 n R : ℝ} (hβ : 0 < β) (hg : 0 < g) (hc : 0 < c0)
    (hn : n < 1) :
    ((∀ t : ℕ, χ * (g ^ t * c0) / (1 - n) = g ^ t * w0) ↔ χ * c0 / (1 - n) = w0) ∧
      ((∀ t : ℕ, (g ^ t * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) =
          β * ((g ^ (t + 1) * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) * R) ↔
        R = g ^ γ / β) := by
  have hv : 0 < (1 - n) ^ (χ * (1 - γ)) := Real.rpow_pos_of_pos (by linarith) _
  constructor
  · constructor
    · intro h; simpa using h 0
    · intro h t
      rw [← h]
      ring
  · have key : ∀ t : ℕ, (g ^ (t + 1) * c0) ^ (-γ) = g ^ (-γ) * (g ^ t * c0) ^ (-γ) := fun t => by
      rw [pow_succ, mul_comm (g ^ t) g, mul_assoc, Real.mul_rpow hg.le (by positivity)]
    have hgg : g ^ (-γ) * g ^ γ = 1 := by
      rw [← Real.rpow_add hg, neg_add_cancel, Real.rpow_zero]
    constructor
    · intro h
      have h0 := h 0
      rw [key 0] at h0
      have hp : 0 < (g ^ 0 * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) :=
        mul_pos (Real.rpow_pos_of_pos (by simpa using hc) _) hv
      have h1 : 1 = β * g ^ (-γ) * R := by
        have : (g ^ 0 * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * 1 =
            (g ^ 0 * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ)) * (β * g ^ (-γ) * R) := by
          rw [mul_one]; nth_rewrite 1 [h0]; ring
        exact mul_left_cancel₀ hp.ne' this
      rw [eq_div_iff hβ.ne']
      linear_combination (-(g ^ γ)) * h1 + (-(β * R)) * hgg
    · intro h t
      rw [key t, h]
      have hb : β ≠ 0 := hβ.ne'
      have : β * (g ^ (-γ) * (g ^ t * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) * (g ^ γ / β) =
          (g ^ (-γ) * g ^ γ) * ((g ^ t * c0) ^ (-γ) * (1 - n) ^ (χ * (1 - γ))) := by
        field_simp
      rw [this, hgg, one_mul]

/-- Under (14.39), `u_c = 1/c`, `u_n = −χn^ν`, and `−u_n/u_c = χn^νc`, homogeneous of degree one
in `c` (balanced growth). -/
theorem rb_u39_mrs {ν χ c n : ℝ} (hc : 0 < c) (hn : 0 < n) (hν : 1 + ν ≠ 0) :
    HasDerivAt (fun c' => rb_u39 ν χ c' n) (1 / c) c ∧
      HasDerivAt (fun n' => rb_u39 ν χ c n') (-(χ * n ^ ν)) n ∧
      χ * n ^ ν / (1 / c) = χ * n ^ ν * c ∧
      ∀ g : ℝ, χ * n ^ ν * (g * c) = g * (χ * n ^ ν * c) := by
  refine ⟨?_, ?_, by field_simp, fun g => by ring⟩
  · have := (Real.hasDerivAt_log hc.ne').sub_const (χ * n ^ (1 + ν) / (1 + ν))
    simpa [rb_u39, one_div] using this
  · have h := (((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hn.ne')).const_mul χ).div_const
      (1 + ν)).const_sub (Real.log c)
    refine h.congr_deriv ?_
    rw [show 1 + ν - 1 = ν by ring]
    field_simp

/-- **The Frisch elasticity** of (14.39) is `1/ν` (Miao, p. 488): holding the marginal utility
of consumption `λ > 0` fixed, the first-order condition `χn^ν = λw` holds iff
`n = (λw/χ)^{1/ν}`, and along `w(s) = we^s`, `ln n(s) = ln n + s/ν`. -/
theorem rb_u39_frisch {ν χ lam w n : ℝ} (hν : 0 < ν) (hχ : 0 < χ) (hlam : 0 < lam)
    (hw : 0 < w) (hn : 0 < n) :
    (χ * n ^ ν = lam * w ↔ n = (lam * w / χ) ^ ν⁻¹) ∧
      ∀ s : ℝ, Real.log ((lam * (w * Real.exp s) / χ) ^ ν⁻¹) =
        Real.log ((lam * w / χ) ^ ν⁻¹) + s / ν := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun s => ?_⟩
  · rw [← h, mul_div_cancel_left₀ _ hχ.ne', Real.rpow_rpow_inv hn.le hν.ne']
  · rw [h, Real.rpow_inv_rpow (by positivity) hν.ne']
    field_simp
  · rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity),
      show lam * (w * Real.exp s) / χ = lam * w / χ * Real.exp s by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
    field_simp

/-- The log-linearised labour supply under (14.39): the derivative of
`ln(χn^νc) − ln w` along `X(s) = Xe^{sX̂}` is `νN̂ + Ĉ − ŵ`, so supply is `νN̂ = ŵ − Ĉ`. -/
theorem rb_u39_supply_loglin {ν χ c n w : ℝ} (hχ : 0 < χ) (hc : 0 < c) (hn : 0 < n)
    (hw : 0 < w) (ch nh wh : ℝ) :
    ∀ s : ℝ, Real.log (χ * (n * Real.exp (s * nh)) ^ ν * (c * Real.exp (s * ch))) -
        Real.log (w * Real.exp (s * wh)) =
      Real.log (χ * n ^ ν * c) - Real.log w + s * (ν * nh + ch - wh) := by
  intro s
  rw [Real.mul_rpow hn.le (Real.exp_pos _).le, ← Real.exp_mul,
    show χ * (n ^ ν * Real.exp (s * nh * ν)) * (c * Real.exp (s * ch)) =
      χ * n ^ ν * c * Real.exp (s * nh * ν + s * ch) by rw [Real.exp_add]; ring,
    Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_mul hw.ne' (by positivity), Real.log_exp]
  ring

/-- Miao, p. 489 (Figure 14.8): with the supply `νN̂ = ŵ − Ĉ` and demand `ŵ = ẑ + αK̂ − αN̂`,
`N̂ = (ẑ + αK̂ − Ĉ)/(α + ν)` and `ŵ = (ν(ẑ + αK̂) + αĈ)/(α + ν)`; at given `Ĉ`, `K̂`, the hours
response `1/(α + ν)` to `ẑ` is decreasing in `ν` (largest for indivisible labour, `ν = 0`) and
the wage response `ν/(α + ν)` is increasing in `ν` (zero for `ν = 0`). -/
theorem rb_nu_responses {α : ℝ} (hα : 0 < α) :
    (∀ {ν c z k n wh : ℝ}, 0 ≤ ν → (ν * n = wh - c ∧ wh = z + α * k - α * n) →
      n = (z + α * k - c) / (α + ν) ∧ wh = (ν * (z + α * k) + α * c) / (α + ν)) ∧
      StrictAntiOn (fun ν : ℝ => 1 / (α + ν)) (Set.Ici 0) ∧
      StrictMonoOn (fun ν : ℝ => ν / (α + ν)) (Set.Ici 0) ∧ (0 : ℝ) / (α + 0) = 0 := by
  refine ⟨fun {ν c z k n wh} hν ⟨h1, h2⟩ => ?_, fun a ha b hb hab => ?_,
    fun a ha b hb hab => ?_, by simp⟩
  · have hd : 0 < α + ν := by linarith
    have hn : n = (z + α * k - c) / (α + ν) := by
      field_simp
      linarith
    refine ⟨hn, ?_⟩
    rw [h2, hn]
    field_simp
    ring
  · simp only [Set.mem_Ici] at ha hb
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · simp only [Set.mem_Ici] at ha hb
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- Miao, p. 489 (Figure 14.7): "the bigger is the consumption increase, the bigger is this
inward shift in labour supply, and therefore the smaller is the hours response in equilibrium and
the larger is the wage response. As a result, the initial jump in output is smaller." With the
supply `ζN̂ = ŵ − Ĉ` and demand `ŵ = ẑ + αK̂ − αN̂`, a larger `Ĉ` (at the same `ẑ`, `K̂`) gives
lower `N̂`, higher `ŵ` and lower `Ŷ = αK̂ + (1 − α)N̂ + ẑ`. -/
theorem rb_consumption_channel {α ζ z k c₁ c₂ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hζ : 0 < ζ)
    (hc : c₁ < c₂) :
    (z + α * k - c₂) / (α + ζ) < (z + α * k - c₁) / (α + ζ) ∧
      (ζ * (z + α * k) + α * c₁) / (α + ζ) < (ζ * (z + α * k) + α * c₂) / (α + ζ) ∧
      α * k + (1 - α) * ((z + α * k - c₂) / (α + ζ)) + z <
        α * k + (1 - α) * ((z + α * k - c₁) / (α + ζ)) + z := by
  have hd : 0 < α + ζ := by linarith
  have h1 : (z + α * k - c₂) / (α + ζ) < (z + α * k - c₁) / (α + ζ) :=
    div_lt_div_of_pos_right (by linarith) hd
  refine ⟨h1, div_lt_div_of_pos_right (by nlinarith) hd, ?_⟩
  have : 0 < 1 - α := by linarith
  nlinarith

/-! ### Indivisible labour: the Hansen–Rogerson lottery -/

/-- **Indivisible labour** (Miao, p. 489; Hansen (1985), Rogerson (1988)). Each household works
`n̄ ∈ (0, 1)` hours or none; it works with probability `p ∈ [0, 1]` and consumes `c₁` if it works
and `c₀` if not, with `pc₁ + (1 − p)c₀ = c`. Its expected utility
`p(ln c₁ + χ ln(1 − n̄)) + (1 − p)(ln c₀ + χ ln 1)` is at most `ln c + pχ ln(1 − n̄)`, with
equality under full insurance `c₁ = c₀ = c`; and `ln c + pχ ln(1 − n̄) = ln c − BN` with
`N = pn̄` and `B = −χ ln(1 − n̄)/n̄ > 0`: (14.39) with `ν = 0`. -/
theorem rb_lottery {χ nbar p c c₁ c₀ : ℝ} (hχ : 0 < χ) (hn0 : 0 < nbar) (hn1 : nbar < 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hc₁ : 0 < c₁) (hc₀ : 0 < c₀)
    (hres : p * c₁ + (1 - p) * c₀ = c) :
    p * (Real.log c₁ + χ * Real.log (1 - nbar)) + (1 - p) * (Real.log c₀ + χ * Real.log 1) ≤
        Real.log c + p * (χ * Real.log (1 - nbar)) ∧
      (0 < c → p * (Real.log c + χ * Real.log (1 - nbar)) +
        (1 - p) * (Real.log c + χ * Real.log 1) = Real.log c + p * (χ * Real.log (1 - nbar))) ∧
      Real.log c + p * (χ * Real.log (1 - nbar)) =
        rb_u39 0 (-(χ * Real.log (1 - nbar)) / nbar) c (p * nbar) ∧
      0 < -(χ * Real.log (1 - nbar)) / nbar := by
  have hcpos : 0 < c := by
    rw [← hres]
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h]; simpa using hc₀
    · have : 0 ≤ (1 - p) * c₀ := mul_nonneg (by linarith) hc₀.le
      nlinarith
  have hlog1 : Real.log (1 - nbar) < 0 := Real.log_neg (by linarith) (by linarith)
  refine ⟨?_, fun _ => by simp only [Real.log_one, mul_zero, add_zero]; ring, ?_, ?_⟩
  · -- Jensen for `ln` via the weighted AM–GM inequality
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hp0 (by linarith : 0 ≤ 1 - p)
      hc₁.le hc₀.le (by ring)
    have hpos : 0 < c₁ ^ p * c₀ ^ (1 - p) :=
      mul_pos (Real.rpow_pos_of_pos hc₁ _) (Real.rpow_pos_of_pos hc₀ _)
    have hl := Real.log_le_log hpos (hamgm.trans_eq hres)
    rw [Real.log_mul (Real.rpow_pos_of_pos hc₁ _).ne' (Real.rpow_pos_of_pos hc₀ _).ne',
      Real.log_rpow hc₁, Real.log_rpow hc₀] at hl
    simp only [Real.log_one, mul_zero, add_zero]
    nlinarith
  · simp only [rb_u39, add_zero, Real.rpow_one, div_one]
    field_simp
    ring
  · have : 0 < -(χ * Real.log (1 - nbar)) := by nlinarith
    positivity

/-! ### GHH utility (14.40) -/

/-- Miao, (14.40), p. 489: under GHH utility `u(c, n) = U(c − G(n))`, `u_c = U′(c − G(n))` and
`u_n = −U′(c − G(n))G′(n)`, so with `U′ > 0` the labour supply condition `−u_n/u_c = w` is
`G′(n) = w`, which does not involve `c`. -/
theorem rb_ghh_mrs {U G : ℝ → ℝ} {U' G' c n w : ℝ} (hU : HasDerivAt U U' (c - G n))
    (hG : HasDerivAt G G' n) (hU' : 0 < U') :
    HasDerivAt (fun c' => U (c' - G n)) U' c ∧
      HasDerivAt (fun n' => U (c - G n')) (-(U' * G')) n ∧ (U' * G' / U' = w ↔ G' = w) := by
  refine ⟨?_, ?_, ?_⟩
  · convert hU.comp c ((hasDerivAt_id c).sub_const (G n)) using 1
    · funext x
      simp only [Function.comp_apply, id]
    · ring
  · convert hU.comp n (hG.const_sub c) using 1
    · rfl
    · ring
  · rw [mul_div_cancel_left₀ _ hU'.ne']

/-- Miao, p. 490: "consumption does not affect labour supply ... the shift in labour demand
determines the change in hours and wage." With GHH preferences and `G′` monotone increasing,
the labour-market equilibrium `G′(n) = (1 − α)zK^αn^{−α}` has at most one solution `n > 0`, and
it does not depend on consumption. -/
theorem rb_ghh_hours {α z K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hz : 0 < z) (hK : 0 < K)
    {G' : ℝ → ℝ} (hG : Monotone G') {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (h₁ : G' n₁ = rb_MPL α z K n₁) (h₂ : G' n₂ = rb_MPL α z K n₂) : n₁ = n₂ := by
  have hanti : ∀ a b, 0 < a → a < b → rb_MPL α z K b < rb_MPL α z K a := fun a b ha hab => by
    unfold rb_MPL
    have := Real.rpow_lt_rpow_of_neg ha hab (by linarith : -α < 0)
    have hc : 0 < (1 - α) * z * K ^ α :=
      mul_pos (mul_pos (by linarith) hz) (Real.rpow_pos_of_pos hK _)
    nlinarith
  rcases lt_trichotomy n₁ n₂ with h | h | h
  · have := hG h.le
    have := hanti n₁ n₂ hn₁ h
    linarith
  · exact h
  · have := hG h.le
    have := hanti n₂ n₁ hn₂ h
    linarith

/-- Miao, p. 488 ("other utility models outside the KPR class"): GHH utility is not of the KPR
class: with `G(n) = n²/2` the MRS `G′(n) = n` is not homogeneous of degree one in `c`
(`MRS(2c, 1) ≠ 2·MRS(c, 1)`), so it is not compatible with balanced growth with constant hours. -/
theorem rb_ghh_not_kpr : ¬ ∀ g c : ℝ, (fun (_ : ℝ) (n : ℝ) => n) (g * c) 1 =
    g * (fun (_ : ℝ) (n : ℝ) => n) c 1 := by
  intro h
  have := h 2 1
  norm_num at this

/-! ### Habit formation -/

/-- Miao, p. 492, habit formation: with lifetime utility `E∑βᵗ[ln(C_t − bC_{t−1}) + …]`, the
date-`t` consumption `C_t` enters `ln(C_t − bC_{t−1})` and `β ln(C_{t+1} − bC_t)`; with finitely
many successor states (`C_{t+1} = C₁ i` with probability `p i`), the derivative of these terms
in `C_t` is the marginal utility `Λ_t = 1/(C_t − bC_{t−1}) − βbE_t[1/(C_{t+1} − bC_t)]`. -/
theorem rb_habit_mu {ι : Type*} [Fintype ι] {β b Cm C : ℝ} {p C₁ : ι → ℝ} (hC : 0 < C - b * Cm)
    (hC₁ : ∀ i, 0 < C₁ i - b * C) :
    HasDerivAt (fun x => Real.log (x - b * Cm) + β * ∑ i, p i * Real.log (C₁ i - b * x))
      (1 / (C - b * Cm) - β * b * ∑ i, p i * (1 / (C₁ i - b * C))) C := by
  have h0 := ((hasDerivAt_id C).sub_const (b * Cm)).log hC.ne'
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((((hasDerivAt_id C).const_mul b).const_sub (C₁ i)).log (hC₁ i).ne').const_mul (p i))
  convert h0.add (hs.const_mul β) using 1
  · funext x
    simp
  · simp only [id, mul_one, Finset.mul_sum]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Partial derivatives and Euler's theorem (copied)

Copied from `EconomicDynamics/Applications` (module `IVQTheory`, Miao §8.6.2, pp. 278–280),
names `iv_*` renamed to `rx_*`, namespace renamed.

* `rx_HasPartials Ψ a b p`: `Ψ : ℝ × ℝ → ℝ` is differentiable at `p` with partial derivatives
  `Ψ₁(p) = a`, `Ψ₂(p) = b`; `rx_HasPartials.comp` is the chain rule along a path.
* `rx_euler_homog`: Euler's theorem `Ψ(I, K) = IΨ₁ + KΨ₂` for a linearly homogeneous `Ψ`.
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- `Ψ : ℝ × ℝ → ℝ` is differentiable at `p` with partial derivatives `Ψ₁(p) = a` and
`Ψ₂(p) = b`. -/
def rx_HasPartials (Ψ : ℝ × ℝ → ℝ) (a b : ℝ) (p : ℝ × ℝ) : Prop :=
  HasFDerivAt Ψ (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) p

/-- The derivative of `Ψ` along a differentiable path `k ↦ (x k, y k)`. -/
theorem rx_HasPartials.comp {Ψ : ℝ × ℝ → ℝ} {a b : ℝ} {x y : ℝ → ℝ} {x' y' k : ℝ}
    (hΨ : rx_HasPartials Ψ a b (x k, y k)) (hx : HasDerivAt x x' k) (hy : HasDerivAt y y' k) :
    HasDerivAt (fun s => Ψ (x s, y s)) (a * x' + b * y') k := by
  unfold rx_HasPartials at hΨ
  have := HasFDerivAt.comp_hasDerivAt (l := Ψ) (f := fun s => (x s, y s)) k hΨ
    (HasDerivAt.prodMk hx hy)
  simpa [Function.comp_def, smul_eq_mul] using this

/-- Miao, p. 280 (Euler's theorem for linearly homogeneous functions): if
`Ψ(λI, λK) = λΨ(I, K)` for all `λ > 0` and `Ψ` has partial derivatives `Ψ₁ = a`, `Ψ₂ = b` at
`(I, K)`, then `Ψ(I, K) = IΨ₁ + KΨ₂`. -/
theorem rx_euler_homog {Ψ : ℝ × ℝ → ℝ} {I K a b : ℝ}
    (hhom : ∀ l : ℝ, 0 < l → Ψ (l * I, l * K) = l * Ψ (I, K))
    (hd : rx_HasPartials Ψ a b (I, K)) : Ψ (I, K) = I * a + K * b := by
  have hd' : rx_HasPartials Ψ a b ((fun l : ℝ => l * I) 1, (fun l : ℝ => l * K) 1) := by
    simpa using hd
  have d1 : HasDerivAt (fun l : ℝ => Ψ (l * I, l * K)) (a * I + b * K) 1 := by
    have := hd'.comp ((hasDerivAt_id (1 : ℝ)).mul_const I) ((hasDerivAt_id (1 : ℝ)).mul_const K)
    simpa using this
  have d2 : HasDerivAt (fun l : ℝ => Ψ (l * I, l * K)) (Ψ (I, K)) 1 := by
    have h0 : HasDerivAt (fun l : ℝ => l * Ψ (I, K)) (1 * Ψ (I, K)) 1 :=
      (hasDerivAt_id (1 : ℝ)).mul_const _
    rw [one_mul] at h0
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with l hl
    exact hhom l hl
  have := d1.unique d2
  linarith

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The event tree of §14.3

Miao, §14.3, pp. 493–508: the stochastic models of §14.3 are written with conditional
expectations `E_t`. We write them on an event tree, as in Chapter 13: a node is a history
`h : List S` of shocks from a finite set `S`, most recent first; its successors are the lists
`s :: h`, and `cp h s` is the conditional probability of `s` given `h`. A process is a function
`List S → ℝ` (its value at a date-`t` node is its date-`t` value); a variable chosen at date
`t`, such as `K_{t+1}`, is a function of the date-`t` node at which it is chosen.

* `RXTree S`: conditional probabilities `cp h s ≥ 0`, `∑ₛ cp h s = 1`; concrete instances
  `rx_detTree` (deterministic, perfect foresight) and `rx_coinTree` (a fair coin each period).
* `rx_E T x h = E_t[x_{t+1}]` at the node `h` (`rx_Es T h f` for a successor-indexed
  `f`), its linearity, and "taking out what is known"
  (`rx_E_mul_left`).
* `rx_pv T m n x h = E_t[M_{t,t+n} x_{t+n}]`, the value at `h` of a payoff `n` periods ahead
  under the one-period stochastic discount factor `m` (`M_{t,t+n}` is the product of `m` along
  the path), and the forward iteration of a pricing recursion `y = E[m(d + y)]`
  (`rx_pv_iterate`, `rx_pv_limit`).
* `rx_node_foc`: the first-order condition of a node problem in which a variable chosen at `h`
  enters the objective at `h` and at all successors of `h`.
* `rx_homog_hasDerivAt`: a positively homogeneous function of one variable is linear on
  `(0, ∞)`, so its derivative equals its average (used for `∂P/∂K = P/K`).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- An event tree (Miao, §13.1, used in §14.3): conditional probabilities of the next shock
given the history. -/
structure RXTree (S : Type*) [Fintype S] where
  /-- `cp h s = Pr(s | h)`. -/
  cp : List S → S → ℝ
  cp_nonneg : ∀ h s, 0 ≤ cp h s
  cp_sum : ∀ h, ∑ s, cp h s = 1

/-- The deterministic tree: one shock, conditional probability one. -/
def rx_detTree : RXTree Unit where
  cp := fun _ _ => 1
  cp_nonneg := fun _ _ => zero_le_one
  cp_sum := fun _ => by simp

/-- The coin tree: two equally likely shocks each period. -/
noncomputable def rx_coinTree : RXTree Bool where
  cp := fun _ _ => 1 / 2
  cp_nonneg := fun _ _ => by norm_num
  cp_sum := fun _ => by simp

/-- The conditional expectation `E_t[x_{t+1}]` at the node `h`. -/
def rx_E {S : Type*} [Fintype S] (T : RXTree S) (x : List S → ℝ) (h : List S) : ℝ :=
  ∑ s, T.cp h s * x (s :: h)

/-- The conditional expectation `Eₜ[f]` of a successor-indexed date-`t+1` quantity `f s` at
the node `h`. -/
def rx_Es {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (f : S → ℝ) : ℝ :=
  ∑ s, T.cp h s * f s

/-- `rx_Es` is `rx_E` of the process whose value at `s :: h` is `f s`. -/
theorem rx_E_eq_Es {S : Type*} [Fintype S] (T : RXTree S) (x : List S → ℝ) (h : List S) :
    rx_E T x h = rx_Es T h (fun s => x (s :: h)) := rfl

theorem rx_Es_add {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (f g : S → ℝ) :
    rx_Es T h (fun s => f s + g s) = rx_Es T h f + rx_Es T h g := by
  simp only [rx_Es, mul_add, Finset.sum_add_distrib]

theorem rx_Es_mul_left {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (a : ℝ)
    (f : S → ℝ) : rx_Es T h (fun s => a * f s) = a * rx_Es T h f := by
  simp only [rx_Es, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem rx_Es_const {S : Type*} [Fintype S] (T : RXTree S) (h : List S) (a : ℝ) :
    rx_Es T h (fun _ => a) = a := by
  simp only [rx_Es, ← Finset.sum_mul, T.cp_sum, one_mul]

/-- In the deterministic tree the expectation is the value at the unique successor. -/
theorem rx_E_det (x : List Unit → ℝ) (h : List Unit) : rx_E rx_detTree x h = x (() :: h) := by
  simp [rx_E, rx_detTree]

/-- In the coin tree the expectation is the average over the two successors. -/
theorem rx_E_coin (x : List Bool → ℝ) (h : List Bool) :
    rx_E rx_coinTree x h = (x (true :: h) + x (false :: h)) / 2 := by
  simp [rx_E, rx_coinTree]
  ring

theorem rx_E_add {S : Type*} [Fintype S] (T : RXTree S) (x y : List S → ℝ) (h : List S) :
    rx_E T (fun g => x g + y g) h = rx_E T x h + rx_E T y h := by
  simp only [rx_E, mul_add, Finset.sum_add_distrib]

/-- Expectation of a constant. -/
theorem rx_E_const {S : Type*} [Fintype S] (T : RXTree S) (a : ℝ) (h : List S) :
    rx_E T (fun _ => a) h = a := by
  simp only [rx_E, ← Finset.sum_mul, T.cp_sum, one_mul]

/-- Taking out what is known: a factor fixed at the date-`t` node leaves the expectation. -/
theorem rx_E_mul_left {S : Type*} [Fintype S] (T : RXTree S) (a : ℝ) (x : List S → ℝ)
    (h : List S) : rx_E T (fun g => a * x g) h = a * rx_E T x h := by
  simp only [rx_E, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `rx_pv T m n x h = E_t[M_{t,t+n} x_{t+n}]` at the node `h`, with `M` the product of the
one-period discount factors `m` along the path. -/
def rx_pv {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) :
    ℕ → (List S → ℝ) → List S → ℝ
  | 0, x, h => x h
  | n + 1, x, h => ∑ s, T.cp h s * (m (s :: h) * rx_pv T m n x (s :: h))

theorem rx_pv_one {S : Type*} [Fintype S] (T : RXTree S) (m x : List S → ℝ) (h : List S) :
    rx_pv T m 1 x h = rx_E T (fun g => m g * x g) h := rfl

theorem rx_pv_add {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (n : ℕ)
    (x y : List S → ℝ) (h : List S) :
    rx_pv T m n (fun g => x g + y g) h = rx_pv T m n x h + rx_pv T m n y h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [rx_pv, ih, mul_add, Finset.sum_add_distrib]

theorem rx_pv_sum {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (N : ℕ)
    (x : List S → ℝ) (h : List S) :
    ∑ j ∈ Finset.range N, rx_pv T m (j + 1 + 1) x h =
      ∑ s, T.cp h s * (m (s :: h) * ∑ j ∈ Finset.range N, rx_pv T m (j + 1) x (s :: h)) := by
  simp only [rx_pv, Finset.mul_sum]
  exact Finset.sum_comm

/-- Forward iteration of the pricing recursion `yₜ = Eₜ[m_{t+1}(d_{t+1} + y_{t+1})]`:
`yₜ = Σ_{j<n} Eₜ[M_{t,t+j+1} d_{t+j+1}] + Eₜ[M_{t,t+n} y_{t+n}]`. -/
theorem rx_pv_iterate {S : Type*} [Fintype S] (T : RXTree S) {m d y : List S → ℝ}
    (hy : ∀ h, y h = rx_E T (fun g => m g * (d g + y g)) h) (n : ℕ) (h : List S) :
    y h = ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d h + rx_pv T m n y h := by
  induction n generalizing h with
  | zero => simp [rx_pv]
  | succ n ih =>
    rw [Finset.sum_range_succ', rx_pv_sum, hy h]
    rw [show rx_pv T m (0 + 1) d h = ∑ s, T.cp h s * (m (s :: h) * d (s :: h)) from rfl,
      show rx_pv T m (n + 1) y h = ∑ s, T.cp h s * (m (s :: h) * rx_pv T m n y (s :: h))
        from rfl]
    simp only [rx_E]
    rw [add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ih (s :: h)]
    ring

/-- The present-value formula: if the residual `Eₜ[M_{t,t+n} y_{t+n}]` vanishes as `n → ∞`
(transversality), then `yₜ = Σ_{j ≥ 1} Eₜ[M_{t,t+j} d_{t+j}]` (limit of partial sums). -/
theorem rx_pv_limit {S : Type*} [Fintype S] (T : RXTree S) {m d y : List S → ℝ}
    (hy : ∀ h, y h = rx_E T (fun g => m g * (d g + y g)) h) (h : List S)
    (htvc : Tendsto (fun n => rx_pv T m n y h) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d h) atTop (𝓝 (y h)) := by
  have h3 := (tendsto_const_nhds (x := y h)).sub htvc
  rw [sub_zero] at h3
  refine h3.congr fun n => ?_
  rw [rx_pv_iterate T hy n h]
  ring

/-- The first-order condition of a node problem. A variable `k` chosen at a node enters the
objective through `c₀(k)` at that node (felicity `U₀`) and through `c₁ₛ(k)` at each successor
`s` (felicity `U₁ₛ`, conditional probability `pₛ`, discount factor `β`). At a local maximum,
`U₀′ c₀′ + β Σₛ pₛ U₁ₛ′ c₁ₛ′ = 0`. -/
theorem rx_node_foc {S : Type*} [Fintype S] {U0 c0 : ℝ → ℝ} {U1 c1 : S → ℝ → ℝ} {p : S → ℝ}
    {β k l0 d0 : ℝ} {l1 d1 : S → ℝ} (hU0 : HasDerivAt U0 l0 (c0 k)) (hc0 : HasDerivAt c0 d0 k)
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (c1 s k)) (hc1 : ∀ s, HasDerivAt (c1 s) (d1 s) k)
    (hmax : IsLocalMax (fun x => U0 (c0 x) + β * ∑ s, p s * U1 s (c1 s x)) k) :
    l0 * d0 + β * ∑ s, p s * (l1 s * d1 s) = 0 := by
  have hs : HasDerivAt (fun x => ∑ s, p s * U1 s (c1 s x)) (∑ s, p s * (l1 s * d1 s)) k :=
    HasDerivAt.fun_sum fun s _ => ((hU1 s).comp k (hc1 s)).const_mul (p s)
  exact hmax.hasDerivAt_eq_zero (((hU0.comp k hc0).add (hs.const_mul β)))

/-- A function homogeneous of degree one on `(0, ∞)` (`P(λk) = λP(k)`) has derivative
`P(k)/k` at every `k > 0`: marginal equals average. -/
theorem rx_homog_hasDerivAt {P : ℝ → ℝ} (hP : ∀ l k : ℝ, 0 < l → 0 < k → P (l * k) = l * P k)
    {k : ℝ} (hk : 0 < k) : HasDerivAt P (P k / k) k := by
  have h0 : HasDerivAt (fun x => x * (P k / k)) (1 * (P k / k)) k :=
    (hasDerivAt_id k).mul_const _
  rw [one_mul] at h0
  refine h0.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hk] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have := hP (x / k) k (div_pos hx0 hk) hk
  rw [div_mul_cancel₀ x hk.ne'] at this
  rw [this]
  field_simp

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §14.3.2 Capacity utilization and Exercise 14.3

Miao, §14.3 (introduction, p. 493) and §14.3.2, pp. 493–494; Exercise 14.3, p. 507.

Capital depreciates at the rate `δ(u) = δ₀u^{δ₁}` (`rx_dep`, `δ₀ > 0`, `δ₁ > 1`), increasing and
strictly convex in the utilization rate `u > 0` (`rx_dep_strictMonoOn`, `rx_dep_strictConvexOn`),
`K_{t+1} = (1 − δ(uₜ))Kₜ + Iₜ` and `Yₜ = zₜ(Kₜuₜ)^α Nₜ^{1−α}` (`rx_cuY`). The model lives on
the event tree of `RXTree`.

* The planner's first-order conditions, derived by perturbing `K_{t+1}` at a node and `uₜ`:
  `u′(Cₜ) = βEₜ u′(C_{t+1})(1 − δ(u_{t+1}) + αY_{t+1}/K_{t+1})` (`rx_cu_planner_euler`) and
  `δ′(uₜ) = αYₜ/(Kₜuₜ)` (`rx_cu_planner_util`).
* The decentralisation: the firm's conditions `R_{kt} = αYₜ/(Kₜuₜ)` and the wage
  (`rx_cu_firm_foc`); the household's utilization condition `δ′(uₜ) = R_{kt}` (14.41)
  (`eq_14_41`) and its Euler equation (`rx_cu_household_euler`); with the firm's prices the
  household's conditions are the planner's (`rx_cu_decentralised_eq_planner`).
* Calibration (p. 494): in a steady state with `u = 1`, `δ₀δ₁ = 1/β − 1 + δ₀`, so
  `δ₁ = 1 + (1/β − 1)/δ₀ > 1` (`rx_cu_calibration`); with `β = 0.99`, `δ₀ = 0.025`,
  `δ₁ = 139/99` (`rx_cu_calibration_value`).
* Exercise 14.3 (its mathematical content: the steady state): the steady-state utilization
  rate is unique, `u^{δ₁} = (1/β − 1)/(δ₀(δ₁ − 1))` (`ex_14_3_utilization`), it equals one iff
  `δ₀(δ₁ − 1) = 1/β − 1` (`ex_14_3_u_eq_one`), and the steady-state capital–labour ratio solves
  `αzu^α(K/N)^{α−1} = δ₀δ₁u^{δ₁}` (`ex_14_3_capital_labour`). The calibration and the Dynare
  impulse responses of Exercise 14.3 are not formalised (computational).
* "The idea of capacity utilization is to allow the intensity of the use of capital to vary in
  response to TFP shocks" (p. 493): given `K`, `N`, the optimal utilization rate is strictly
  increasing in `z` (`rx_cu_util_increasing`), so output rises proportionally more than TFP
  (`rx_cu_amplification`).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- The depreciation rate `δ(u) = δ₀u^{δ₁}` (Miao, p. 493). -/
noncomputable def rx_dep (δ0 δ1 u : ℝ) : ℝ := δ0 * u ^ δ1

/-- Output with capacity utilization `Y = z(Ku)^α N^{1−α}` (Miao, p. 493). -/
noncomputable def rx_cuY (α z K u N : ℝ) : ℝ := z * (K * u) ^ α * N ^ (1 - α)

/-- Miao, p. 493: `δ′(u) = δ₀δ₁u^{δ₁−1}` for `u > 0`. -/
theorem rx_dep_hasDerivAt (δ0 δ1 : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (rx_dep δ0 δ1) (δ0 * δ1 * u ^ (δ1 - 1)) u := by
  have := (Real.hasDerivAt_rpow_const (p := δ1) (Or.inl hu.ne')).const_mul δ0
  unfold rx_dep
  convert this using 1
  ring

/-- Miao, p. 493: higher utilization makes capital depreciate faster. -/
theorem rx_dep_strictMonoOn {δ0 δ1 : ℝ} (h0 : 0 < δ0) (h1 : 1 < δ1) :
    StrictMonoOn (rx_dep δ0 δ1) (Set.Ioi 0) := by
  intro x hx y _ hxy
  unfold rx_dep
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hx) hxy (by linarith)) h0

/-- Miao, p. 493: `δ₁ > 1` makes `δ(·)` strictly convex (the curvature parameter). -/
theorem rx_dep_strictConvexOn {δ0 δ1 : ℝ} (h0 : 0 < δ0) (h1 : 1 < δ1) :
    StrictConvexOn ℝ (Set.Ici 0) (rx_dep δ0 δ1) := by
  have hc := strictConvexOn_rpow h1
  refine ⟨hc.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := hc.2 hx hy hxy ha hb hab
  simp only [rx_dep, smul_eq_mul] at this ⊢
  nlinarith [mul_lt_mul_of_pos_left this h0]

/-- `k ↦ z(ku)^α N^{1−α}` has derivative `αY/k` at `k > 0` (for `u > 0`). -/
theorem rx_cuY_hasDerivAt_K (α z u N : ℝ) {k : ℝ} (hk : 0 < k) (hu : 0 < u) :
    HasDerivAt (fun x => rx_cuY α z x u N) (α * rx_cuY α z k u N / k) k := by
  have hku : 0 < k * u := mul_pos hk hu
  have h1 : HasDerivAt (fun x => x * u) u k := by simpa using (hasDerivAt_id k).mul_const u
  have h2 := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hku.ne')).comp k h1
  have h3 := (h2.const_mul z).mul_const (N ^ (1 - α))
  unfold rx_cuY
  refine h3.congr_deriv ?_
  rw [Real.rpow_sub_one hku.ne']
  field_simp

/-- `v ↦ z(Kv)^α N^{1−α}` has derivative `αY/u` at `u > 0` (for `K > 0`). -/
theorem rx_cuY_hasDerivAt_u (α z K N : ℝ) {u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    HasDerivAt (fun v => rx_cuY α z K v N) (α * rx_cuY α z K u N / u) u := by
  have hku : 0 < K * u := mul_pos hK hu
  have h1 : HasDerivAt (fun v => K * v) K u := by simpa using (hasDerivAt_id u).const_mul K
  have h2 := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hku.ne')).comp u h1
  have h3 := (h2.const_mul z).mul_const (N ^ (1 - α))
  unfold rx_cuY
  refine h3.congr_deriv ?_
  rw [Real.rpow_sub_one hku.ne']
  field_simp

/-- Miao, p. 493, the planner's Euler equation with capacity utilization. At the node `h`
the planner chooses `K_{t+1} = k`; it enters `Cₜ = Yₜ − k + (1 − δ(uₜ))Kₜ` and, at each
successor `s`, `C_{t+1}(s) = Y_{t+1}(s) − K_{t+2}(s) + (1 − δ(u_{t+1}(s)))k` with
`Y_{t+1}(s) = z(s)(ku(s))^α N(s)^{1−α}`. If `K_{t+1}` is a local maximum of
`u(Cₜ) + βEₜu(C_{t+1})` (felicities `U₀`, `U₁ₛ` with derivatives `u′(Cₜ) = Λ₀`,
`u′(C_{t+1}(s)) = Λ₁(s)`), then
`u′(Cₜ) = βEₜ[u′(C_{t+1})(1 − δ(u_{t+1}) + αY_{t+1}/K_{t+1})]`. -/
theorem rx_cu_planner_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {α β δ0 δ1 Yt ut Kt K1 l0 : ℝ} {z u N K2 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hK1 : 0 < K1) (hu : ∀ s, 0 < u s)
    (hU0 : HasDerivAt U0 l0 (Yt - K1 + (1 - rx_dep δ0 δ1 ut) * Kt))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s)
      (rx_cuY α (z s) K1 (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * K1))
    (hmax : IsLocalMax (fun k => U0 (Yt - k + (1 - rx_dep δ0 δ1 ut) * Kt) + β * ∑ s,
      T.cp h s * U1 s (rx_cuY α (z s) k (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)) K1) :
    l0 = β * rx_Es T h (fun s => l1 s *
      (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1)) := by
  have hc0 : HasDerivAt (fun k => Yt - k + (1 - rx_dep δ0 δ1 ut) * Kt) (0 - 1 + 0) K1 :=
    ((hasDerivAt_const K1 Yt).sub (hasDerivAt_id K1)).add (hasDerivAt_const K1 _)
  have hc1 : ∀ s, HasDerivAt
      (fun k => rx_cuY α (z s) k (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
      (α * rx_cuY α (z s) K1 (u s) (N s) / K1 - 0 + (1 - rx_dep δ0 δ1 (u s)) * 1) K1 :=
    fun s => ((rx_cuY_hasDerivAt_K α (z s) (u s) (N s) hK1 (hu s)).sub
      (hasDerivAt_const K1 _)).add ((hasDerivAt_id K1).const_mul _)
  have e := rx_node_foc (c0 := fun k => Yt - k + (1 - rx_dep δ0 δ1 ut) * Kt)
    (c1 := fun s k => rx_cuY α (z s) k (u s) (N s) - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
    hU0 hc0 hU1 hc1 hmax
  simp only [rx_Es]
  have hs : ∀ s, T.cp h s * (l1 s * (α * rx_cuY α (z s) K1 (u s) (N s) / K1 - 0
      + (1 - rx_dep δ0 δ1 (u s)) * 1)) = T.cp h s * (l1 s *
      (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1)) := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => hs s] at e
  linarith

/-- Miao, p. 493, the planner's utilization condition `δ′(uₜ) = αYₜ/(Kₜuₜ)`. The rate `uₜ`
enters only `Cₜ = z(Kₜuₜ)^α Nₜ^{1−α} − K_{t+1} + (1 − δ(uₜ))Kₜ`; at a local maximum of
`u(Cₜ)` with `u′(Cₜ) ≠ 0` the marginal product of utilization equals the marginal cost
`δ′(uₜ)Kₜ`. -/
theorem rx_cu_planner_util {α δ0 δ1 z K N K1 u l0 : ℝ} {U0 : ℝ → ℝ} (hK : 0 < K) (hu : 0 < u)
    (hl0 : l0 ≠ 0) (hU0 : HasDerivAt U0 l0 (rx_cuY α z K u N - K1 + (1 - rx_dep δ0 δ1 u) * K))
    (hmax : IsLocalMax (fun v => U0 (rx_cuY α z K v N - K1 + (1 - rx_dep δ0 δ1 v) * K)) u) :
    δ0 * δ1 * u ^ (δ1 - 1) = α * rx_cuY α z K u N / (K * u) := by
  have hc : HasDerivAt (fun v => rx_cuY α z K v N - K1 + (1 - rx_dep δ0 δ1 v) * K)
      (α * rx_cuY α z K u N / u - 0 + (0 - δ0 * δ1 * u ^ (δ1 - 1)) * K) u :=
    ((rx_cuY_hasDerivAt_u α z K N hK hu).sub (hasDerivAt_const u K1)).add
      (((hasDerivAt_const u 1).sub (rx_dep_hasDerivAt δ0 δ1 hu)).mul_const K)
  have e := hmax.hasDerivAt_eq_zero (hU0.comp u hc)
  rcases mul_eq_zero.1 e with h0 | h0
  · exact absurd h0 hl0
  · field_simp
    field_simp at h0
    linarith

/-- Miao, p. 494, the firm's problem `max zk^α n^{1−α} − R_k k − wn`: at an interior maximum
`R_k = αzk^α n^{1−α}/k` and `w = (1 − α)zk^α n^{1−α}/n`; in equilibrium `k = Ku`, `n = N`, so
`R_{kt} = αYₜ/(Kₜuₜ)`. -/
theorem rx_cu_firm_foc {α z K u N R w : ℝ} (hK : 0 < K) (hu : 0 < u) (hN : 0 < N)
    (hk : IsLocalMax (fun k => z * k ^ α * N ^ (1 - α) - R * k - w * N) (K * u))
    (hn : IsLocalMax (fun n => z * (K * u) ^ α * n ^ (1 - α) - R * (K * u) - w * n) N) :
    R = α * rx_cuY α z K u N / (K * u) ∧ w = (1 - α) * rx_cuY α z K u N / N := by
  have hku : 0 < K * u := mul_pos hK hu
  constructor
  · have d : HasDerivAt (fun k => z * k ^ α * N ^ (1 - α) - R * k - w * N)
        (z * (α * (K * u) ^ (α - 1)) * N ^ (1 - α) - R * 1 - 0) (K * u) :=
      ((((Real.hasDerivAt_rpow_const (p := α) (Or.inl hku.ne')).const_mul z).mul_const _).sub
        ((hasDerivAt_id _).const_mul R)).sub (hasDerivAt_const _ _)
    have e := hk.hasDerivAt_eq_zero d
    rw [Real.rpow_sub_one hku.ne'] at e
    unfold rx_cuY
    field_simp at e ⊢
    linarith
  · have d : HasDerivAt (fun n => z * (K * u) ^ α * n ^ (1 - α) - R * (K * u) - w * n)
        (z * (K * u) ^ α * ((1 - α) * N ^ (1 - α - 1)) - 0 - w * 1) N :=
      (((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul _).sub
        (hasDerivAt_const _ _)).sub ((hasDerivAt_id _).const_mul w)
    have e := hn.hasDerivAt_eq_zero d
    rw [Real.rpow_sub_one hN.ne'] at e
    unfold rx_cuY
    field_simp at e ⊢
    linarith

/-- Miao, (14.41), p. 494. The household owns capital and rents the services `uₜKₜ` at the rate
`R_{kt}`; its budget gives `Cₜ = R_{kt}uₜKₜ + wₜNₜ − K_{t+1} + (1 − δ(uₜ))Kₜ`. At a local
maximum in `uₜ` with `u′(Cₜ) ≠ 0`: `δ′(uₜ) = R_{kt}`. -/
theorem eq_14_41 {δ0 δ1 R w K N K1 u l0 : ℝ} {U0 : ℝ → ℝ} (hK : 0 < K) (hu : 0 < u)
    (hl0 : l0 ≠ 0) (hU0 : HasDerivAt U0 l0 (R * (u * K) + w * N - K1 + (1 - rx_dep δ0 δ1 u) * K))
    (hmax : IsLocalMax (fun v => U0 (R * (v * K) + w * N - K1 + (1 - rx_dep δ0 δ1 v) * K)) u) :
    δ0 * δ1 * u ^ (δ1 - 1) = R := by
  have hc : HasDerivAt (fun v => R * (v * K) + w * N - K1 + (1 - rx_dep δ0 δ1 v) * K)
      (R * (1 * K) + 0 - 0 + (0 - δ0 * δ1 * u ^ (δ1 - 1)) * K) u :=
    ((((hasDerivAt_id u).mul_const K).const_mul R).add (hasDerivAt_const u _)).sub
      (hasDerivAt_const u K1) |>.add
      (((hasDerivAt_const u 1).sub (rx_dep_hasDerivAt δ0 δ1 hu)).mul_const K)
  have e := hmax.hasDerivAt_eq_zero (hU0.comp u hc)
  rcases mul_eq_zero.1 e with h0 | h0
  · exact absurd h0 hl0
  · have : (R - δ0 * δ1 * u ^ (δ1 - 1)) * K = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hK.ne'

/-- Miao, p. 494, the household's Euler equation with utilization: perturbing `K_{t+1} = k` in
`Cₜ = R_{kt}uₜKₜ + wₜNₜ − k + (1 − δ(uₜ))Kₜ` and
`C_{t+1}(s) = R_k(s)u(s)k + w(s)N(s) − K_{t+2}(s) + (1 − δ(u(s)))k` gives
`u′(Cₜ) = βEₜ[u′(C_{t+1})(R_{k,t+1}u_{t+1} + 1 − δ(u_{t+1}))]`. -/
theorem rx_cu_household_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β δ0 δ1 Wt K1 l0 : ℝ} {R u wN K2 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (Wt - K1))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s)
      (R s * u s * K1 + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * K1))
    (hmax : IsLocalMax (fun k => U0 (Wt - k) + β * ∑ s,
      T.cp h s * U1 s (R s * u s * k + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)) K1) :
    l0 = β * rx_Es T h (fun s => l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s))) := by
  have hc0 : HasDerivAt (fun k => Wt - k) (0 - 1) K1 := (hasDerivAt_const K1 Wt).sub
    (hasDerivAt_id K1)
  have hc1 : ∀ s, HasDerivAt
      (fun k => R s * u s * k + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
      (R s * u s * 1 + 0 - 0 + (1 - rx_dep δ0 δ1 (u s)) * 1) K1 :=
    fun s => ((((hasDerivAt_id K1).const_mul _).add (hasDerivAt_const K1 _)).sub
      (hasDerivAt_const K1 _)).add ((hasDerivAt_id K1).const_mul _)
  have e := rx_node_foc (c0 := fun k => Wt - k)
    (c1 := fun s k => R s * u s * k + wN s - K2 s + (1 - rx_dep δ0 δ1 (u s)) * k)
    hU0 hc0 hU1 hc1 hmax
  simp only [rx_Es]
  have hs : ∀ s, T.cp h s * (l1 s * (R s * u s * 1 + 0 - 0 + (1 - rx_dep δ0 δ1 (u s)) * 1)) =
      T.cp h s * (l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s))) := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => hs s] at e
  linarith

/-- Miao, pp. 493–494: the decentralised equilibrium and the planner's problem give the same
conditions. With the firm's rental rate `R_k = αY/(Ku)` (`rx_cu_firm_foc`), the household's
Euler equation is the planner's (`rx_cu_household_euler` vs `rx_cu_planner_euler`), (14.41) is
the planner's utilization condition (`rx_cu_planner_util`), and the household's income
`R_kuK + wN` with `w = (1 − α)Y/N` is output `Y`, so its budget is the resource constraint. -/
theorem rx_cu_decentralised_eq_planner {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {α β δ0 δ1 K1 l0 : ℝ} {R u z N l1 : S → ℝ} (hK1 : 0 < K1) (hu : ∀ s, 0 < u s)
    (hR : ∀ s, R s = α * rx_cuY α (z s) K1 (u s) (N s) / (K1 * u s)) :
    (l0 = β * rx_Es T h (fun s => l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s))) ↔
      l0 = β * rx_Es T h (fun s => l1 s *
        (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1))) ∧
    (∀ {Rt ut Kt zt Nt : ℝ}, 0 < Kt → 0 < ut → Rt = α * rx_cuY α zt Kt ut Nt / (Kt * ut) →
      (δ0 * δ1 * ut ^ (δ1 - 1) = Rt ↔
        δ0 * δ1 * ut ^ (δ1 - 1) = α * rx_cuY α zt Kt ut Nt / (Kt * ut))) ∧
    (∀ {Rt wt ut Kt zt Nt : ℝ}, 0 < Kt → 0 < ut → 0 < Nt →
      Rt = α * rx_cuY α zt Kt ut Nt / (Kt * ut) → wt = (1 - α) * rx_cuY α zt Kt ut Nt / Nt →
      Rt * (ut * Kt) + wt * Nt = rx_cuY α zt Kt ut Nt) := by
  refine ⟨?_, fun _ _ hRt => by rw [hRt], fun hKt hut hNt hRt hwt => ?_⟩
  · have : ∀ s, l1 s * (R s * u s + 1 - rx_dep δ0 δ1 (u s)) =
        l1 s * (1 - rx_dep δ0 δ1 (u s) + α * rx_cuY α (z s) K1 (u s) (N s) / K1) := by
      intro s
      rw [hR s]
      have := hu s
      field_simp
      ring
    simp only [this]
  · rw [hRt, hwt]
    field_simp
    ring

/-- Miao, p. 494, calibration. In a steady state with `u = 1`, the Euler equation gives
`1 = β(1 − δ(1) + αY/K)` and (14.41) with `R_k = αY/K` gives `δ′(1) = δ₀δ₁ = αY/K`; hence
`δ₀δ₁ = 1/β − 1 + δ₀` pins down `δ₀δ₁`, `δ₁ = 1 + (1/β − 1)/δ₀`, and `δ₁ > 1` when `β < 1`. -/
theorem rx_cu_calibration {β δ0 δ1 ay : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0)
    (heuler : 1 = β * (1 - rx_dep δ0 δ1 1 + ay)) (hutil : δ0 * δ1 * (1 : ℝ) ^ (δ1 - 1) = ay) :
    δ0 * δ1 = 1 / β - 1 + δ0 ∧ δ1 = 1 + (1 / β - 1) / δ0 ∧ (β < 1 → 1 < δ1) := by
  simp only [rx_dep, Real.one_rpow, mul_one] at heuler hutil
  have h1 : δ0 * δ1 = 1 / β - 1 + δ0 := by
    rw [hutil]
    field_simp
    linarith
  have h2 : δ1 = 1 + (1 / β - 1) / δ0 := by
    have : (1 / β - 1) / δ0 = δ1 - 1 := by
      rw [div_eq_iff hδ0.ne']
      linear_combination -h1
    linarith
  refine ⟨h1, h2, fun hβ1 => ?_⟩
  rw [h2]
  have : 0 < 1 / β - 1 := by
    rw [lt_sub_iff_add_lt, zero_add, lt_div_iff₀ hβ]
    linarith
  have := div_pos this hδ0
  linarith

/-- Miao, p. 494, calibration: with `β = 0.99` (§14.2) and `δ₀ = 0.025`, `δ₁ = 139/99`. -/
theorem rx_cu_calibration_value {δ1 ay : ℝ}
    (heuler : 1 = 99 / 100 * (1 - rx_dep (1 / 40) δ1 1 + ay))
    (hutil : 1 / 40 * δ1 * (1 : ℝ) ^ (δ1 - 1) = ay) : δ1 = 139 / 99 := by
  have := (rx_cu_calibration (by norm_num) (by norm_num) heuler hutil).2.1
  rw [this]
  norm_num

/-- **Exercise 14.3** (Miao, p. 507), the steady-state utilization rate. In a nonstochastic
steady state the Euler equation is `1 = β(1 − δ(u) + αY/K)` and the utilization condition is
`δ′(u) = αY/(Ku)`. Then `u^{δ₁} = (1/β − 1)/(δ₀(δ₁ − 1))`, so the steady-state utilization
rate is unique: `u = ((1/β − 1)/(δ₀(δ₁ − 1)))^{1/δ₁}`. -/
theorem ex_14_3_utilization {β δ0 δ1 ay u : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0) (hδ1 : 1 < δ1)
    (hu : 0 < u) (heuler : 1 = β * (1 - rx_dep δ0 δ1 u + ay))
    (hutil : δ0 * δ1 * u ^ (δ1 - 1) = ay / u) :
    u ^ δ1 = (1 / β - 1) / (δ0 * (δ1 - 1)) ∧
      u = ((1 / β - 1) / (δ0 * (δ1 - 1))) ^ δ1⁻¹ := by
  have hay : ay = δ0 * δ1 * u ^ δ1 := by
    rw [Real.rpow_sub_one hu.ne'] at hutil
    field_simp at hutil
    linarith
  have h1 : u ^ δ1 = (1 / β - 1) / (δ0 * (δ1 - 1)) := by
    rw [hay] at heuler
    unfold rx_dep at heuler
    have : δ0 * (δ1 - 1) ≠ 0 := mul_ne_zero hδ0.ne' (by linarith)
    have hb : 1 / β = 1 - δ0 * u ^ δ1 + δ0 * δ1 * u ^ δ1 := by
      rw [div_eq_iff hβ.ne']
      linear_combination heuler
    rw [eq_div_iff this, hb]
    ring
  refine ⟨h1, ?_⟩
  rw [← h1, Real.rpow_rpow_inv hu.le (by linarith)]

/-- **Exercise 14.3** (Miao, p. 507), existence of the steady-state utilization rate: for
`0 < β < 1`, `u* = ((1/β − 1)/(δ₀(δ₁ − 1)))^{1/δ₁} > 0` together with `αY/K = δ₀δ₁u*^{δ₁}`
satisfies both steady-state conditions. -/
theorem ex_14_3_utilization_exists {β δ0 δ1 : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ0)
    (hδ1 : 1 < δ1) :
    let u := ((1 / β - 1) / (δ0 * (δ1 - 1))) ^ δ1⁻¹
    0 < u ∧ 1 = β * (1 - rx_dep δ0 δ1 u + δ0 * δ1 * u ^ δ1) ∧
      δ0 * δ1 * u ^ (δ1 - 1) = δ0 * δ1 * u ^ δ1 / u := by
  intro u
  have hc : 0 < (1 / β - 1) / (δ0 * (δ1 - 1)) := by
    apply div_pos
    · rw [lt_sub_iff_add_lt, zero_add, lt_div_iff₀ hβ]
      linarith
    · exact mul_pos hδ0 (by linarith)
  have hu : 0 < u := Real.rpow_pos_of_pos hc _
  have hpow : u ^ δ1 = (1 / β - 1) / (δ0 * (δ1 - 1)) :=
    Real.rpow_inv_rpow hc.le (by linarith)
  refine ⟨hu, ?_, ?_⟩
  · unfold rx_dep
    rw [hpow]
    have : δ0 * (δ1 - 1) ≠ 0 := mul_ne_zero hδ0.ne' (by linarith)
    have hc' : δ0 * (δ1 - 1) * ((1 / β - 1) / (δ0 * (δ1 - 1))) = 1 / β - 1 :=
      mul_div_cancel₀ _ this
    have hb : β * (1 / β) = 1 := by field_simp
    linear_combination (-β) * hc' - hb
  · rw [Real.rpow_sub_one hu.ne']
    ring

/-- **Exercise 14.3** (Miao, p. 507) and p. 494: the steady-state utilization rate equals one
iff `δ₀(δ₁ − 1) = 1/β − 1` (equivalently `δ₀δ₁ = 1/β − 1 + δ₀`, `rx_cu_calibration`). -/
theorem ex_14_3_u_eq_one {β δ0 δ1 ay u : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0) (hδ1 : 1 < δ1)
    (hu : 0 < u) (heuler : 1 = β * (1 - rx_dep δ0 δ1 u + ay))
    (hutil : δ0 * δ1 * u ^ (δ1 - 1) = ay / u) :
    u = 1 ↔ δ0 * (δ1 - 1) = 1 / β - 1 := by
  obtain ⟨h1, h2⟩ := ex_14_3_utilization hβ hδ0 hδ1 hu heuler hutil
  have hne : δ0 * (δ1 - 1) ≠ 0 := mul_ne_zero hδ0.ne' (by linarith)
  constructor
  · intro hu1
    rw [hu1, Real.one_rpow, eq_div_iff hne, one_mul] at h1
    exact h1
  · intro hc
    rw [h2, ← hc, div_self hne, Real.one_rpow]

/-- **Exercise 14.3** (Miao, p. 507), the steady-state capital–labour ratio: with
`Y = z(Ku)^α N^{1−α}`, the condition `αY/K = r` (with `r = δ₀δ₁u^{δ₁}` from
`ex_14_3_utilization`) reads `αzu^α(K/N)^{α−1} = r`. -/
theorem ex_14_3_capital_labour {α z K u N : ℝ} (hK : 0 < K) (hu : 0 < u) (hN : 0 < N) :
    α * rx_cuY α z K u N / K = α * z * u ^ α * (K / N) ^ (α - 1) := by
  unfold rx_cuY
  rw [Real.mul_rpow hK.le hu.le, Real.div_rpow hK.le hN.le, Real.rpow_sub_one hK.ne',
    Real.rpow_sub_one hN.ne', show (1 : ℝ) - α = -(α - 1) by ring, Real.rpow_neg hN.le,
    Real.rpow_sub_one hN.ne']
  have : 0 < N ^ α := Real.rpow_pos_of_pos hN α
  field_simp

/-- The utilization condition `δ₀δ₁u^{δ₁−1} = αz(Ku)^α N^{1−α}/(Ku)` is equivalent to
`u^{δ₁−α} = (α/(δ₀δ₁)) K^{α−1}N^{1−α} z`. -/
theorem rx_cu_util_closed {α δ0 δ1 z K u N : ℝ} (hδ0 : 0 < δ0) (hδ1 : 0 < δ1) (hK : 0 < K)
    (hu : 0 < u) (hfoc : δ0 * δ1 * u ^ (δ1 - 1) = α * rx_cuY α z K u N / (K * u)) :
    u ^ (δ1 - α) = α / (δ0 * δ1) * (K ^ (α - 1) * N ^ (1 - α)) * z := by
  unfold rx_cuY at hfoc
  rw [Real.mul_rpow hK.le hu.le, Real.rpow_sub_one hu.ne'] at hfoc
  rw [Real.rpow_sub hu, Real.rpow_sub_one hK.ne']
  have hua : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  field_simp at hfoc ⊢
  linarith

/-- Miao, p. 493: utilization responds to TFP. Given `K` and `N`, if `u` and `u′` satisfy the
planner's utilization condition at TFP levels `z < z′` (with `δ₀ > 0`, `δ₁ > 1 > α`), then
`u < u′`. -/
theorem rx_cu_util_increasing {α δ0 δ1 z z' K N u u' : ℝ} (hδ0 : 0 < δ0) (hδ1 : 1 < δ1)
    (hα0 : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hN : 0 < N) (hu : 0 < u) (hu' : 0 < u')
    (hz : z < z')
    (hfoc : δ0 * δ1 * u ^ (δ1 - 1) = α * rx_cuY α z K u N / (K * u))
    (hfoc' : δ0 * δ1 * u' ^ (δ1 - 1) = α * rx_cuY α z' K u' N / (K * u')) : u < u' := by
  have e := rx_cu_util_closed hδ0 (by linarith) hK hu hfoc
  have e' := rx_cu_util_closed hδ0 (by linarith) hK hu' hfoc'
  have hc : 0 < α / (δ0 * δ1) * (K ^ (α - 1) * N ^ (1 - α)) :=
    mul_pos (div_pos hα0 (mul_pos hδ0 (by linarith)))
      (mul_pos (Real.rpow_pos_of_pos hK _) (Real.rpow_pos_of_pos hN _))
  by_contra hle
  have := Real.rpow_le_rpow hu'.le (not_lt.1 hle) (show 0 ≤ δ1 - α by linarith)
  rw [e, e'] at this
  nlinarith

/-- Miao, p. 493, amplification: given `K` and `N`, if utilization rises with TFP (`u < u′`,
`rx_cu_util_increasing`), output rises proportionally more than TFP:
`z′/z < Y(z′, u′)/Y(z, u)`. -/
theorem rx_cu_amplification {α z z' K N u u' : ℝ} (hα0 : 0 < α) (hz : 0 < z) (hz' : 0 < z')
    (hK : 0 < K) (hN : 0 < N) (hu : 0 < u) (huu : u < u') :
    z' / z < rx_cuY α z' K u' N / rx_cuY α z K u N := by
  unfold rx_cuY
  have hu' : 0 < u' := hu.trans huu
  rw [Real.mul_rpow hK.le hu.le, Real.mul_rpow hK.le hu'.le]
  have h1 : u ^ α < u' ^ α := Real.rpow_lt_rpow hu.le huu hα0
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hNa : 0 < N ^ (1 - α) := Real.rpow_pos_of_pos hN _
  have hua : 0 < u ^ α := Real.rpow_pos_of_pos hu α
  rw [div_lt_div_iff₀ hz (by positivity)]
  have : z' * (z * (K ^ α * u ^ α) * N ^ (1 - α)) < z' * (z * (K ^ α * u' ^ α) * N ^ (1 - α)) := by
    gcongr
  linarith

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §14.3.3 Capital adjustment costs: the planner and the three decentralisations

Miao, §14.3.3, pp. 494–500, and Exercise 14.5, p. 508. Capital accumulates as
`K_{t+1} = (1 − δ)Kₜ + Φ(Iₜ, Kₜ)` (14.42), with `Φ_I > 0`, `Φ_II < 0`, often
`Φ(I, K) = ϕ(I/K)K` (14.43) with `ϕ″ < 0`, `ϕ(δ) = δ`, `ϕ′(δ) = 1`, `ϕ″(δ) = κ`.

* (14.43): linear homogeneity, partial derivatives `Φ_I = ϕ′(I/K)`,
  `Φ_K = ϕ(I/K) − (I/K)ϕ′(I/K)`, `Φ_II = ϕ″(I/K)/K < 0` (`rx_Phi`, `rx_Phi_homog`,
  `rx_Phi_partials`, `rx_Phi_II`); the steady state `I/K = δ`, `Q = 1`, `Φ_K = 0`
  (`rx_Phi_steady`, `eq_14_43_steady`), and the normalisation forces `κ < 0` (`rx_kappa_neg`).
  The concrete `ϕ(i) = i + κ(i − δ)²/2` (`rx_phiQuad`) satisfies all the normalisations
  (`rx_phiQuad_normalised`).
* The first-order conditions are derived by perturbing `K_{t+1}` at a node, the investment
  changes being given by the inverse `G(·, K)` of `Φ(·, K)` (`rx_inverse_partials`): the
  generic node Euler equation `rx_uzawa_euler`, with `Q = 1/Φ_I` (the `Iₜ` condition
  `QΦ_I = 1`, also the stationarity of the Lagrangian in `Iₜ`, `rx_invest_foc`).
* The planner (14.44)–(14.45): `eq_14_45_N` (labour), `eq_14_45_K` (capital).
* Decentralisation 1 (households own capital), (14.46)–(14.47): the household's labour and
  capital conditions (`rx_dec1_labour`, `rx_dec1_euler`), the firm's
  `R_k = zF_K`, `w = zF_N` (`eq_14_47_foc`).
* Decentralisation 2 (stock market): the household's share and bond conditions
  (`rx_dec2_shares`, `rx_dec2_bonds`), the firm's (14.48)–(14.49) (`eq_14_48`, `eq_14_49`).
* Decentralisation 3 (capital goods producers): the producer's `QΦ_I = 1`
  (`rx_dec3_producer`) and the household's Euler equation (`rx_dec3_euler`).
* **Exercise 14.5**: decentralisations 1 and 2 have the planner's equilibrium conditions
  (`ex_14_5_dec1`, `ex_14_5_dec2`, budgets ⇒ resource constraint `ex_14_5_budgets`).
  **Correction**: decentralisation 3 as printed does not: the household does not internalise
  `Φ_K`, so its Euler equation lacks the term `Q_{t+1}Φ_K` (`ex_14_5_dec3_iff`); the two
  Euler equations are incompatible whenever `Φ_K` has a strict sign at all successors
  (`ex_14_5_dec3_counterexample`), which happens for (14.43) off the steady state
  (`rx_Phi_K_pos`, `rx_phiQuad_K`). They agree when `Φ_K ≡ 0` and when the household's capital
  also earns the producers' rent `QΦ_KK` (`ex_14_5_dec3_corrected`).
* "In the case without capital adjustment costs (`Φ = I`), `Qₜ = 1`" (`rx_no_adjustment_Q`).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- The adjustment cost function (14.43), `Φ(I, K) = ϕ(I/K)K` (Miao, p. 495). -/
noncomputable def rx_Phi (ϕ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := ϕ (p.1 / p.2) * p.2

/-- Miao, p. 495: (14.43) is linearly homogeneous. -/
theorem rx_Phi_homog (ϕ : ℝ → ℝ) {l : ℝ} (hl : l ≠ 0) (I K : ℝ) :
    rx_Phi ϕ (l * I, l * K) = l * rx_Phi ϕ (I, K) := by
  simp only [rx_Phi]
  rw [mul_div_mul_left I K hl]
  ring

/-- Miao, p. 495: the partial derivatives of (14.43), `Φ_I = ϕ′(I/K)` and
`Φ_K = ϕ(I/K) − (I/K)ϕ′(I/K)`, at `K > 0`. -/
theorem rx_Phi_partials {ϕ : ℝ → ℝ} {d : ℝ} {I K : ℝ} (hK : K ≠ 0)
    (hϕ : HasDerivAt ϕ d (I / K)) : rx_HasPartials (rx_Phi ϕ) d (ϕ (I / K) - I / K * d) (I, K) := by
  have hinv : HasFDerivAt (fun p : ℝ × ℝ => p.2⁻¹)
      (-((K ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) (I, K) := by
    have h0 : HasDerivAt (fun x : ℝ => x⁻¹) (-(K ^ 2)⁻¹) ((I, K).2) := hasDerivAt_inv hK
    have := h0.comp_hasFDerivAt (𝕜 := ℝ) (f := Prod.snd) (I, K)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (I, K)))
    simpa [Function.comp_def] using this
  have hdiv : HasFDerivAt (fun p : ℝ × ℝ => p.1 * p.2⁻¹)
      (I • (-((K ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) +
        K⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ) (I, K) :=
    (hasFDerivAt_fst (p := (I, K))).mul hinv
  have hϕ' : HasDerivAt ϕ d ((fun p : ℝ × ℝ => p.1 * p.2⁻¹) (I, K)) := by
    simpa [div_eq_mul_inv] using hϕ
  have hcomp := hϕ'.comp_hasFDerivAt (I, K) hdiv
  have hfull := hcomp.mul (hasFDerivAt_snd (p := (I, K)))
  unfold rx_HasPartials
  have heq : rx_Phi ϕ = (fun p : ℝ × ℝ => (ϕ ∘ fun p : ℝ × ℝ => p.1 * p.2⁻¹) p * p.2) := by
    funext p
    simp [rx_Phi, div_eq_mul_inv]
  rw [heq]
  refine hfull.congr_fderiv ?_
  ext
  · simp [div_eq_mul_inv]
    field_simp
  · simp [div_eq_mul_inv]
    field_simp
    ring

/-- The partial derivative in the first argument, as a one-variable derivative. -/
theorem rx_HasPartials.fst {Ψ : ℝ × ℝ → ℝ} {a b I K : ℝ} (h : rx_HasPartials Ψ a b (I, K)) :
    HasDerivAt (fun x => Ψ (x, K)) a I := by
  have := h.comp (x := fun x => x) (y := fun _ => K) (k := I) (hasDerivAt_id I)
    (hasDerivAt_const I K)
  simpa using this

/-- The partial derivative in the second argument, as a one-variable derivative. -/
theorem rx_HasPartials.snd {Ψ : ℝ × ℝ → ℝ} {a b I K : ℝ} (h : rx_HasPartials Ψ a b (I, K)) :
    HasDerivAt (fun y => Ψ (I, y)) b K := by
  have := h.comp (x := fun _ => I) (y := fun y => y) (k := K) (hasDerivAt_const K I)
    (hasDerivAt_id K)
  simpa using this

/-- Miao, p. 495: `Φ_II = ϕ″(I/K)/K`, negative when `ϕ″ < 0` and `K > 0` (the book's
`Φ_II < 0`). -/
theorem rx_Phi_II {dϕ : ℝ → ℝ} {d2 I K : ℝ} (hd2 : HasDerivAt dϕ d2 (I / K)) :
    HasDerivAt (fun x => dϕ (x / K)) (d2 / K) I ∧ (d2 < 0 → 0 < K → d2 / K < 0) := by
  have := hd2.comp I ((hasDerivAt_id' I).div_const K)
  exact ⟨this.congr_deriv (by ring), fun h1 h2 => div_neg_of_neg_of_pos h1 h2⟩

/-- Miao, p. 495: at `I = δK` the normalisations `ϕ(δ) = δ`, `ϕ′(δ) = 1` give `Φ = δK`,
`Φ_I = 1` and `Φ_K = 0`. -/
theorem rx_Phi_steady {ϕ dϕ : ℝ → ℝ} {δ K : ℝ} (hK : K ≠ 0) (h0 : ϕ δ = δ) (h1 : dϕ δ = 1) :
    rx_Phi ϕ (δ * K, K) = δ * K ∧ dϕ (δ * K / K) = 1 ∧
      ϕ (δ * K / K) - δ * K / K * dϕ (δ * K / K) = 0 := by
  have e : δ * K / K = δ := by field_simp
  simp [rx_Phi, e, h0, h1]

/-- Miao, p. 495, (14.43): "this assumption ensures that the investment rate is `I/K = δ` and
`Q = 1` in the nonstochastic steady state". If `ϕ` is strictly increasing (`Φ_I > 0`),
`ϕ(δ) = δ`, `ϕ′(δ) = 1`, and a steady state satisfies `K = (1 − δ)K + Φ(I, K)` with `K > 0`,
`QΦ_I = 1` and the Euler equation `1 = β(zF_K + Q(1 − δ + Φ_K))`, then `I/K = δ`, `Q = 1` and
`zF_K = 1/β − 1 + δ`: the steady state is that of the model without adjustment costs, whatever
`κ = ϕ″(δ)`. -/
theorem eq_14_43_steady {ϕ dϕ : ℝ → ℝ} {δ β K I Q zFK : ℝ} (hβ : 0 < β) (hK : 0 < K)
    (hmono : StrictMono ϕ) (h0 : ϕ δ = δ) (h1 : dϕ δ = 1)
    (hacc : K = (1 - δ) * K + rx_Phi ϕ (I, K)) (hQ : Q * dϕ (I / K) = 1)
    (heuler : 1 = β * (zFK + Q * (1 - δ + (ϕ (I / K) - I / K * dϕ (I / K))))) :
    I / K = δ ∧ Q = 1 ∧ zFK = 1 / β - 1 + δ := by
  have hϕ : ϕ (I / K) = δ := by
    simp only [rx_Phi] at hacc
    have : (ϕ (I / K) - δ) * K = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hK.ne'
  have hi : I / K = δ := hmono.injective (hϕ.trans h0.symm)
  rw [hi, h1, mul_one] at hQ
  refine ⟨hi, hQ, ?_⟩
  rw [hi, h0, h1, hQ] at heuler
  field_simp
  linarith

/-- Miao, p. 495: with `ϕ″ < 0` everywhere, the parameter `κ = ϕ″(δ)` is negative. -/
theorem rx_kappa_neg {d2 : ℝ → ℝ} {δ κ : ℝ} (h : ∀ i, d2 i < 0) (hκ : d2 δ = κ) : κ < 0 :=
  hκ ▸ h δ

/-- A concrete adjustment function for (14.43): `ϕ(i) = i + κ(i − δ)²/2`. -/
noncomputable def rx_phiQuad (δ κ i : ℝ) : ℝ := i + κ * (i - δ) ^ 2 / 2

/-- `rx_phiQuad` satisfies the normalisations of (14.43): `ϕ(δ) = δ`, `ϕ′(i) = 1 + κ(i − δ)`
(so `ϕ′(δ) = 1`) and `ϕ″ = κ` (so `ϕ″ < 0` for `κ < 0`). -/
theorem rx_phiQuad_normalised (δ κ : ℝ) :
    rx_phiQuad δ κ δ = δ ∧ (∀ i, HasDerivAt (rx_phiQuad δ κ) (1 + κ * (i - δ)) i) ∧
      (1 + κ * (δ - δ) = 1) ∧ (∀ i, HasDerivAt (fun j => 1 + κ * (j - δ)) κ i) := by
  refine ⟨by simp [rx_phiQuad], fun i => ?_, by ring, fun i => ?_⟩
  · have h0 := (hasDerivAt_id' i).sub_const δ
    have h := ((h0.mul h0).const_mul κ).div_const 2
    have := (hasDerivAt_id' i).add h
    unfold rx_phiQuad
    simp only [sq]
    exact this.congr_deriv (by ring)
  · have := (((hasDerivAt_id i).sub_const δ).const_mul κ).const_add 1
    simpa using this

/-- For `rx_phiQuad`, `Φ_K = ϕ(i) − iϕ′(i) = −κ(i² − δ²)/2`, positive when `κ < 0` and
`0 ≤ δ < i` (investment above its steady-state rate). -/
theorem rx_phiQuad_K (δ κ i : ℝ) :
    rx_phiQuad δ κ i - i * (1 + κ * (i - δ)) = -κ * (i ^ 2 - δ ^ 2) / 2 ∧
      (κ < 0 → 0 ≤ δ → δ < i → 0 < -κ * (i ^ 2 - δ ^ 2) / 2) := by
  refine ⟨by unfold rx_phiQuad; ring, fun hκ hδ hi => ?_⟩
  have : 0 < i ^ 2 - δ ^ 2 := by nlinarith
  have : 0 < -κ * (i ^ 2 - δ ^ 2) := mul_pos (by linarith) this
  linarith

/-- Miao, p. 495, (14.43): `Φ_K = ϕ(i) − iϕ′(i)` is strictly positive for `i > δ > 0` when
`ϕ″ < 0`, `ϕ(δ) = δ`, `ϕ′(δ) = 1`: its derivative is `−iϕ″(i) > 0` and it vanishes at
`i = δ`. -/
theorem rx_Phi_K_pos {ϕ dϕ d2 : ℝ → ℝ} {δ i : ℝ} (hϕ : ∀ x, HasDerivAt ϕ (dϕ x) x)
    (hdϕ : ∀ x, HasDerivAt dϕ (d2 x) x) (hneg : ∀ x, d2 x < 0) (h0 : ϕ δ = δ) (h1 : dϕ δ = 1)
    (hδ : 0 < δ) (hi : δ < i) : 0 < ϕ i - i * dϕ i := by
  have hg : ∀ x, HasDerivAt (fun y => ϕ y - y * dϕ y) (-(x * d2 x)) x := by
    intro x
    have := (hϕ x).sub ((hasDerivAt_id' x).mul (hdϕ x))
    exact this.congr_deriv (by ring)
  have hmono : StrictMonoOn (fun y => ϕ y - y * dϕ y) (Set.Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x _ => (hg x).continuousAt.continuousWithinAt) (fun x hx => ?_)
    rw [interior_Ioi] at hx
    rw [(hg x).deriv]
    have : 0 < x := hx
    nlinarith [hneg x]
  have := hmono (show δ ∈ Set.Ioi 0 from hδ) (show i ∈ Set.Ioi 0 from hδ.trans hi) hi
  simp only [h0, h1, mul_one, sub_self] at this
  exact this

/-- The partial derivatives of the inverse `G(·, K)` of `Φ(·, K)`: differentiating
`Φ(G(X, K), K) = X` gives `Φ_I G_X = 1` and `Φ_I G_K + Φ_K = 0`. -/
theorem rx_inverse_partials {Φ G : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {X K gX gK a b : ℝ} (hG : rx_HasPartials G gX gK (X, K))
    (hΦ : rx_HasPartials Φ a b (G (X, K), K)) : a * gX = 1 ∧ a * gK + b = 0 := by
  constructor
  · have hp : HasDerivAt (fun x => G (x, K)) gX X := hG.fst
    have d := hΦ.comp (x := fun x => G (x, K)) (y := fun _ => K) (k := X) hp
      (hasDerivAt_const X K)
    have d' : HasDerivAt (fun x => Φ (G (x, K), K)) 1 X := by
      simpa [hΦG] using hasDerivAt_id' X
    have := d.unique d'
    linarith
  · have hp : HasDerivAt (fun y => G (X, y)) gK K := hG.snd
    have d := hΦ.comp (x := fun y => G (X, y)) (y := fun y => y) (k := K) hp (hasDerivAt_id K)
    have d' : HasDerivAt (fun y => Φ (G (X, y), y)) 0 K := by
      simpa [hΦG] using hasDerivAt_const K X
    have := d.unique d'
    linarith

/-- The node Euler equation with adjustment costs in the accumulation equation (14.42).
At the node `h`, `K_{t+1} = k` is financed by `Iₜ = G(k − (1 − δ)Kₜ, Kₜ)` out of income `y₀`,
and at each successor `s` the investment `I_{t+1}(s) = G(K_{t+2}(s) − (1 − δ)k, k)` keeps
`K_{t+2}(s)` fixed, out of income `y₁ₛ(k)` with `y₁ₛ′(K_{t+1}) = r₁ₛ`. With `QₜΦ_I(Iₜ, Kₜ) = 1`,
`Q_{t+1}Φ_I(I_{t+1}, K_{t+1}) = 1` and `Φ_K(I_{t+1}, K_{t+1}) = b₁`, a local maximum of
`U₀(cₜ) + βEₜU₁(c_{t+1})` gives `ΛₜQₜ = βEₜ[Λ_{t+1}(r_{t+1} + Q_{t+1}(1 − δ + Φ_K))]`. -/
theorem rx_uzawa_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 y0 l0 a0 b0 gX0 gK0 Q0 : ℝ} {K2 l1 r1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    {U0 : ℝ → ℝ} {U1 y1 : S → ℝ → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hy1 : ∀ s, HasDerivAt (y1 s) (r1 s) K1)
    (hU0 : HasDerivAt U0 l0 (y0 - G (K1 - (1 - δ) * Kt, Kt)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s K1 - G (K2 s - (1 - δ) * K1, K1)))
    (hmax : IsLocalMax (fun k => U0 (y0 - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * U1 s (y1 s k - G (K2 s - (1 - δ) * k, k))) K1) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (r1 s + Q1 s * (1 - δ + b1 s))) := by
  obtain ⟨e0, -⟩ := rx_inverse_partials hΦG hG0 hΦ0
  have hgX0 : gX0 = Q0 := by
    calc gX0 = gX0 * (Q0 * a0) := by rw [hQ0, mul_one]
      _ = Q0 * (a0 * gX0) := by ring
      _ = Q0 := by rw [e0, mul_one]
  have hgX1 : ∀ s, gX1 s = Q1 s ∧ gK1 s = -(Q1 s * b1 s) := by
    intro s
    obtain ⟨e1, e2⟩ := rx_inverse_partials hΦG (hG1 s) (hΦ1 s)
    have hq := hQ1 s
    constructor
    · calc gX1 s = gX1 s * (Q1 s * a1 s) := by rw [hq, mul_one]
        _ = Q1 s * (a1 s * gX1 s) := by ring
        _ = Q1 s := by rw [e1, mul_one]
    · calc gK1 s = gK1 s * (Q1 s * a1 s) := by rw [hq, mul_one]
        _ = Q1 s * (a1 s * gK1 s + b1 s) - Q1 s * b1 s := by ring
        _ = -(Q1 s * b1 s) := by rw [e2]; ring
  have hc0 : HasDerivAt (fun k => y0 - G (k - (1 - δ) * Kt, Kt)) (0 - (gX0 * 1 + gK0 * 0)) K1 :=
    (hasDerivAt_const K1 y0).sub (hG0.comp (x := fun k => k - (1 - δ) * Kt) (y := fun _ => Kt)
      ((hasDerivAt_id K1).sub_const _) (hasDerivAt_const K1 Kt))
  have hc1 : ∀ s, HasDerivAt (fun k => y1 s k - G (K2 s - (1 - δ) * k, k))
      (r1 s - (gX1 s * (0 - (1 - δ) * 1) + gK1 s * 1)) K1 := fun s =>
    (hy1 s).sub ((hG1 s).comp (x := fun k => K2 s - (1 - δ) * k) (y := fun k => k)
      ((hasDerivAt_const K1 _).sub ((hasDerivAt_id K1).const_mul _)) (hasDerivAt_id K1))
  have e := rx_node_foc (c0 := fun k => y0 - G (k - (1 - δ) * Kt, Kt))
    (c1 := fun s k => y1 s k - G (K2 s - (1 - δ) * k, k)) hU0 hc0 hU1 hc1 hmax
  have hs : ∀ s, T.cp h s * (l1 s * (r1 s - (gX1 s * (0 - (1 - δ) * 1) + gK1 s * 1))) =
      T.cp h s * (l1 s * (r1 s + Q1 s * (1 - δ + b1 s))) := by
    intro s
    rw [(hgX1 s).1, (hgX1 s).2]
    ring
  rw [Finset.sum_congr rfl fun s _ => hs s, hgX0] at e
  simp only [rx_Es]
  linarith

/-- Miao, (14.45), p. 496, and (14.48), p. 498: the `Iₜ` condition `QₜΦ_I(Iₜ, Kₜ) = 1`. The
terms of the Lagrangian in `Iₜ` are `Λ(−Iₜ) + ΛQΦ(Iₜ, Kₜ)` (multiplier `Λ` on the resource or
dividend constraint, `ΛQ` on (14.42)); their derivative is `Λ(QΦ_I − 1)`, which vanishes iff
`QΦ_I = 1` when `Λ ≠ 0`. -/
theorem rx_invest_foc {Φ : ℝ × ℝ → ℝ} {Λ Q I K a : ℝ} (hΦ : HasDerivAt (fun x => Φ (x, K)) a I) :
    HasDerivAt (fun x => Λ * -x + Λ * Q * Φ (x, K)) (Λ * (Q * a - 1)) I ∧
      (Λ ≠ 0 → (Λ * (Q * a - 1) = 0 ↔ Q * a = 1)) := by
  refine ⟨?_, fun hΛ => ?_⟩
  · have := ((hasDerivAt_id' I).neg.const_mul Λ).add (hΦ.const_mul (Λ * Q))
    exact this.congr_deriv (by ring)
  · constructor
    · intro h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hΛ
      · linarith
    · intro h0
      rw [h0, sub_self, mul_zero]

/-- Miao, p. 498: "In the case without capital adjustment costs (i.e., `Φ(I, K) = I`),
`Qₜ = 1`". -/
theorem rx_no_adjustment_Q {Q I K : ℝ} {a : ℝ} (hΦ : HasDerivAt (fun x => (fun p : ℝ × ℝ => p.1)
    (x, K)) a I) (hQ : Q * a = 1) : Q = 1 := by
  have : a = 1 := hΦ.unique (hasDerivAt_id' I)
  rw [this, mul_one] at hQ
  exact hQ

/-- A labour first-order condition: if `n ↦ U(c(n), n)` has a local maximum at `N`, with
`c′(N) = c_N`, `U_C = Λ`, `U_N = u_N`, then `Λc_N + u_N = 0`. -/
theorem rx_labour_foc {U : ℝ × ℝ → ℝ} {c : ℝ → ℝ} {N cn l uN : ℝ}
    (hU : rx_HasPartials U l uN (c N, N)) (hc : HasDerivAt c cn N)
    (hmax : IsLocalMax (fun n => U (c n, n)) N) : l * cn + uN = 0 := by
  have := hU.comp (x := c) (y := fun n => n) (k := N) hc (hasDerivAt_id N)
  have e := hmax.hasDerivAt_eq_zero this
  linarith

/-- Miao, (14.45), p. 496, the planner's `Nₜ` condition `−u_N(Cₜ, Nₜ) = ΛₜzₜF_N(Kₜ, Nₜ)`
with `Λₜ = u_C(Cₜ, Nₜ)`, from perturbing `Nₜ` in `Cₜ = zₜF(Kₜ, Nₜ) − Iₜ`. -/
theorem eq_14_45_N {U F : ℝ × ℝ → ℝ} {z K I N FN l uN : ℝ}
    (hU : rx_HasPartials U l uN (z * F (K, N) - I, N)) (hF : HasDerivAt (fun n => F (K, n)) FN N)
    (hmax : IsLocalMax (fun n => U (z * F (K, n) - I, n)) N) : -uN = l * (z * FN) := by
  have hc : HasDerivAt (fun n => z * F (K, n) - I) (z * FN - 0) N :=
    (hF.const_mul z).sub (hasDerivAt_const N I)
  have := rx_labour_foc (c := fun n => z * F (K, n) - I) hU hc hmax
  linarith

/-- Miao, (14.45), p. 496, the planner's `K_{t+1}` condition
`ΛₜQₜ = βEₜΛ_{t+1}(z_{t+1}F_K(K_{t+1}, N_{t+1}) + Q_{t+1}(1 − δ + Φ_K(I_{t+1}, K_{t+1})))`,
from perturbing `K_{t+1}` in the resource constraint (14.44)
`Cₜ = zₜF(Kₜ, Nₜ) − Iₜ` with (14.42), `Λ = u_C`, `QΦ_I = 1`. -/
theorem eq_14_45_K {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G F : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 zt Nt l0 a0 b0 gX0 gK0 Q0 : ℝ} {z N FK K2 l1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hF : ∀ s, HasDerivAt (fun k => F (k, N s)) (FK s) K1)
    (hU0 : HasDerivAt U0 l0 (zt * F (Kt, Nt) - G (K1 - (1 - δ) * Kt, Kt)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (z s * F (K1, N s) - G (K2 s - (1 - δ) * K1, K1)))
    (hmax : IsLocalMax (fun k => U0 (zt * F (Kt, Nt) - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * U1 s (z s * F (k, N s) - G (K2 s - (1 - δ) * k, k))) K1) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (z s * FK s + Q1 s * (1 - δ + b1 s))) :=
  rx_uzawa_euler T h hΦG (y1 := fun s k => z s * F (k, N s)) hG0 hΦ0 hG1 hΦ1 hQ0 hQ1
    (fun s => (hF s).const_mul (z s)) hU0 hU1 hmax

/-- Miao, p. 496, decentralisation 1: the household's `Nₜ` condition `−u_N = Λₜwₜ`, from
perturbing `Nₜ` in the budget (14.46) `Cₜ = R_{kt}Kₜ + wₜNₜ − Iₜ`. -/
theorem rx_dec1_labour {U : ℝ × ℝ → ℝ} {y w N l uN : ℝ}
    (hU : rx_HasPartials U l uN (y + w * N, N)) (hmax : IsLocalMax (fun n => U (y + w * n, n)) N) :
    -uN = l * w := by
  have hc : HasDerivAt (fun n => y + w * n) (w * 1) N :=
    ((hasDerivAt_id N).const_mul w).const_add y
  have := rx_labour_foc (c := fun n => y + w * n) hU hc hmax
  linarith

/-- Miao, p. 496, decentralisation 1: the household's `K_{t+1}` condition
`ΛₜQₜ = βEₜΛ_{t+1}[R_{k,t+1} + Q_{t+1}(1 − δ + Φ_K(I_{t+1}, K_{t+1}))]`, from perturbing
`K_{t+1}` in (14.46) with (14.42). -/
theorem rx_dec1_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 yt l0 a0 b0 gX0 gK0 Q0 : ℝ} {R wN K2 l1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hU0 : HasDerivAt U0 l0 (yt - G (K1 - (1 - δ) * Kt, Kt)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (R s * K1 + wN s - G (K2 s - (1 - δ) * K1, K1)))
    (hmax : IsLocalMax (fun k => U0 (yt - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * U1 s (R s * k + wN s - G (K2 s - (1 - δ) * k, k))) K1) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) :=
  rx_uzawa_euler T h hΦG (y1 := fun s k => R s * k + wN s) hG0 hΦ0 hG1 hΦ1 hQ0 hQ1
    (fun s => by simpa using ((hasDerivAt_id K1).const_mul (R s)).add_const (wN s)) hU0 hU1 hmax

/-- Miao, (14.47), p. 497: the firm's static problem `max zF(K, N) − R_kK − wN`; at an
interior maximum `R_k = zF_K(K, N)` and `w = zF_N(K, N)`. -/
theorem eq_14_47_foc {F : ℝ × ℝ → ℝ} {z K N R w FK FN : ℝ} (hF : rx_HasPartials F FK FN (K, N))
    (hK : IsLocalMax (fun k => z * F (k, N) - R * k - w * N) K)
    (hN : IsLocalMax (fun n => z * F (K, n) - R * K - w * n) N) : R = z * FK ∧ w = z * FN := by
  constructor
  · have d : HasDerivAt (fun k => z * F (k, N) - R * k - w * N) (z * FK - R * 1 - 0) K :=
      (((hF.fst).const_mul z).sub ((hasDerivAt_id K).const_mul R)).sub (hasDerivAt_const K _)
    have := hK.hasDerivAt_eq_zero d
    linarith
  · have d : HasDerivAt (fun n => z * F (K, n) - R * K - w * n) (z * FN - 0 - w * 1) N :=
      (((hF.snd).const_mul z).sub (hasDerivAt_const N _)).sub ((hasDerivAt_id N).const_mul w)
    have := hN.hasDerivAt_eq_zero d
    linarith

/-- Miao, p. 497, decentralisation 2: the household's `ψ_{t+1}` condition
`Λₜ(Vₜ − Dₜ) = βEₜΛ_{t+1}V_{t+1}`, from perturbing the share holding `ψ_{t+1} = x` in
`Cₜ = yₜ − x(Vₜ − Dₜ)` and `C_{t+1}(s) = y_{t+1}(s) + xV_{t+1}(s)`. -/
theorem rx_dec2_shares {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β y0 V D ψ l0 : ℝ} {y1 V1 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - ψ * (V - D)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + ψ * V1 s))
    (hmax : IsLocalMax (fun x => U0 (y0 - x * (V - D)) + β * ∑ s,
      T.cp h s * U1 s (y1 s + x * V1 s)) ψ) :
    l0 * (V - D) = β * rx_Es T h (fun s => l1 s * V1 s) := by
  have hc0 : HasDerivAt (fun x => y0 - x * (V - D)) (0 - 1 * (V - D)) ψ :=
    (hasDerivAt_const ψ y0).sub ((hasDerivAt_id ψ).mul_const _)
  have hc1 : ∀ s, HasDerivAt (fun x => y1 s + x * V1 s) (1 * V1 s) ψ :=
    fun s => ((hasDerivAt_id ψ).mul_const _).const_add _
  have e := rx_node_foc (c0 := fun x => y0 - x * (V - D)) (c1 := fun s x => y1 s + x * V1 s)
    hU0 hc0 hU1 hc1 hmax
  simp only [one_mul] at e
  simp only [rx_Es]
  linarith

/-- Miao, p. 497, decentralisation 2: the household's `B_{t+1}` condition
`Λₜ = βEₜΛ_{t+1}R_{f,t+1}`, from perturbing the bond holding `B_{t+1} = x` in `Cₜ = yₜ − x`
and `C_{t+1}(s) = y_{t+1}(s) + xR_f(s)`. -/
theorem rx_dec2_bonds {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β y0 B l0 : ℝ} {y1 Rf l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - B)) (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + B * Rf s))
    (hmax : IsLocalMax (fun x => U0 (y0 - x) + β * ∑ s, T.cp h s * U1 s (y1 s + x * Rf s)) B) :
    l0 = β * rx_Es T h (fun s => l1 s * Rf s) := by
  have hc0 : HasDerivAt (fun x => y0 - x) (0 - 1) B := (hasDerivAt_const B y0).sub
    (hasDerivAt_id B)
  have hc1 : ∀ s, HasDerivAt (fun x => y1 s + x * Rf s) (1 * Rf s) B :=
    fun s => ((hasDerivAt_id B).mul_const _).const_add _
  have e := rx_node_foc (c0 := fun x => y0 - x) (c1 := fun s x => y1 s + x * Rf s)
    hU0 hc0 hU1 hc1 hmax
  simp only [one_mul] at e
  simp only [rx_Es]
  linarith

/-- Miao, (14.48), p. 498: the firm's `Iₜ` condition `QₜΦ_I(Iₜ, Kₜ) = 1`. The firm's
Lagrangian has the terms `(βᵗΛₜ/Λ₀)(−Iₜ + QₜΦ(Iₜ, Kₜ))` in `Iₜ` (the multiplier on (14.42)
being `Qₜβᵗ Λₜ/Λ₀`); with `βᵗΛₜ/Λ₀ ≠ 0` stationarity is (14.48). -/
theorem eq_14_48 {Φ : ℝ × ℝ → ℝ} {β Λt Λ0 Q I K a : ℝ} {t : ℕ} (hβ : β ≠ 0) (hΛt : Λt ≠ 0)
    (hΛ0 : Λ0 ≠ 0) (hΦ : HasDerivAt (fun x => Φ (x, K)) a I) :
    HasDerivAt (fun x => β ^ t * Λt / Λ0 * -x + β ^ t * Λt / Λ0 * Q * Φ (x, K))
      (β ^ t * Λt / Λ0 * (Q * a - 1)) I ∧
    (β ^ t * Λt / Λ0 * (Q * a - 1) = 0 ↔ Q * a = 1) :=
  rx_invest_foc (Λ := β ^ t * Λt / Λ0) hΦ |>.imp id fun h =>
    h (div_ne_zero (mul_ne_zero (pow_ne_zero t hβ) hΛt) hΛ0)

/-- Miao, (14.49), p. 498: the firm's `K_{t+1}` condition
`ΛₜQₜ = βEₜΛ_{t+1}[z_{t+1}F_K(K_{t+1}, N_{t+1}) + Q_{t+1}(1 − δ + Φ_K(I_{t+1}, K_{t+1}))]`.
The firm maximises `E Σ βᵗ(Λₜ/Λ₀)Dₜ` with `Dₜ = zₜF(Kₜ, Nₜ) − wₜNₜ − Iₜ`; the terms in
`K_{t+1} = k` are, after division by `βᵗ/Λ₀ > 0`, `ΛₜDₜ(k) + βEₜΛ_{t+1}D_{t+1}(k)`. -/
theorem eq_14_49 {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G F : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 yt Λt a0 b0 gX0 gK0 Q0 : ℝ} {z N wN FK K2 Λ1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hF : ∀ s, HasDerivAt (fun k => F (k, N s)) (FK s) K1)
    (hmax : IsLocalMax (fun k => Λt * (yt - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * (Λ1 s * (z s * F (k, N s) - wN s - G (K2 s - (1 - δ) * k, k)))) K1) :
    Λt * Q0 = β * rx_Es T h (fun s => Λ1 s * (z s * FK s + Q1 s * (1 - δ + b1 s))) :=
  rx_uzawa_euler T h hΦG (U0 := fun d => Λt * d) (U1 := fun s d => Λ1 s * d)
    (y1 := fun s k => z s * F (k, N s) - wN s) hG0 hΦ0 hG1 hΦ1 hQ0 hQ1
    (fun s => by simpa using ((hF s).const_mul (z s)).sub_const (wN s))
    (by simpa using (hasDerivAt_id _).const_mul Λt)
    (fun s => by simpa using (hasDerivAt_id _).const_mul (Λ1 s)) hmax

/-- Miao, p. 499, decentralisation 3: the capital goods producer maximises
`QₜK_{t+1} − Qₜ(1 − δ)Kₜ − Iₜ` subject to (14.42), i.e. `QₜΦ(Iₜ, Kₜ) − Iₜ`; at an interior
maximum `QₜΦ_I(Iₜ, Kₜ) = 1`. -/
theorem rx_dec3_producer {Φ : ℝ × ℝ → ℝ} {δ Q I K a : ℝ}
    (hΦ : HasDerivAt (fun x => Φ (x, K)) a I)
    (hmax : IsLocalMax (fun x => Q * ((1 - δ) * K + Φ (x, K)) - Q * (1 - δ) * K - x) I) :
    Q * a = 1 := by
  have d : HasDerivAt (fun x => Q * ((1 - δ) * K + Φ (x, K)) - Q * (1 - δ) * K - x)
      (Q * (0 + a) - 0 - 1) I :=
    ((((hasDerivAt_const I _).add hΦ).const_mul Q).sub (hasDerivAt_const I _)).sub
      (hasDerivAt_id I)
  have := hmax.hasDerivAt_eq_zero d
  linarith

/-- Miao, p. 500, decentralisation 3: the household's `K_{t+1}` condition. The household buys
`K_{t+1} = k` at the price `Qₜ` and next period earns `ρ_{t+1}k`; perturbing `k` in
`Cₜ = yₜ − Qₜk`, `C_{t+1}(s) = y_{t+1}(s) + ρ(s)k` gives `ΛₜQₜ = βEₜΛ_{t+1}ρ_{t+1}`. In the
book's budget `Cₜ + QₜK_{t+1} = Qₜ(1 − δ)Kₜ + R_{kt}Kₜ + wₜNₜ + Πₜ`,
`ρ = R_k + (1 − δ)Q`. -/
theorem rx_dec3_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β y0 Q K1 l0 : ℝ} {y1 ρ l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - Q * K1)) (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + ρ s * K1))
    (hmax : IsLocalMax (fun k => U0 (y0 - Q * k) + β * ∑ s, T.cp h s * U1 s (y1 s + ρ s * k))
      K1) :
    l0 * Q = β * rx_Es T h (fun s => l1 s * ρ s) := by
  have hc0 : HasDerivAt (fun k => y0 - Q * k) (0 - Q * 1) K1 :=
    (hasDerivAt_const K1 y0).sub ((hasDerivAt_id K1).const_mul Q)
  have hc1 : ∀ s, HasDerivAt (fun k => y1 s + ρ s * k) (ρ s * 1) K1 :=
    fun s => ((hasDerivAt_id K1).const_mul _).const_add _
  have e := rx_node_foc (c0 := fun k => y0 - Q * k) (c1 := fun s k => y1 s + ρ s * k)
    hU0 hc0 hU1 hc1 hmax
  simp only [mul_one] at e
  simp only [rx_Es]
  linarith

/-- **Exercise 14.5** (Miao, p. 508), decentralisation 1. With the firm's prices
`R_k = zF_K`, `w = zF_N` (`eq_14_47_foc`) and `Λ = u_C`, the household's conditions
(`rx_dec1_labour`, `rx_dec1_euler`, `rx_invest_foc`) are the planner's (14.45). -/
theorem ex_14_5_dec1 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {δ β l0 Q0 : ℝ}
    {R z FK l1 Q1 b1 : S → ℝ} (hR : ∀ s, R s = z s * FK s) {uN w zt FNt : ℝ}
    (hw : w = zt * FNt) :
    (l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) ↔
      l0 * Q0 = β * rx_Es T h (fun s => l1 s * (z s * FK s + Q1 s * (1 - δ + b1 s)))) ∧
    (-uN = l0 * w ↔ -uN = l0 * (zt * FNt)) := by
  exact ⟨by simp only [hR], by rw [hw]⟩

/-- **Exercise 14.5** (Miao, p. 508), decentralisation 2. The firm discounts with the
household's `Λ = u_C`; the firm's (14.48)–(14.49) and the household's labour condition with the
firm's wage `w = zF_N` are the planner's (14.45), so the planner's allocation satisfies them
with the same `Q`. The household's share condition then prices the firm,
`Pₜ = Vₜ − Dₜ = EₜβΛ_{t+1}V_{t+1}/Λₜ`. -/
theorem ex_14_5_dec2 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {β l0 V D : ℝ}
    {l1 V1 : S → ℝ} (hl0 : 0 < l0)
    (hshare : l0 * (V - D) = β * rx_Es T h (fun s => l1 s * V1 s)) :
    V - D = rx_Es T h (fun s => β * l1 s / l0 * V1 s) := by
  have : rx_Es T h (fun s => β * l1 s / l0 * V1 s) =
      β / l0 * rx_Es T h (fun s => l1 s * V1 s) := by
    rw [← rx_Es_mul_left]
    congr 1
    funext s
    ring
  rw [this]
  field_simp
  linarith

/-- **Exercise 14.5** (Miao, p. 508): in each decentralisation the household's budget is the
resource constraint (14.44) `Cₜ + Iₜ = zₜF(Kₜ, Nₜ)`, when `F` is linearly homogeneous and
`R_k = zF_K`, `w = zF_N`. (1) `C + I = R_kK + wN` (14.46); (2) `C + ψ'(V − D) + B' =
ψV + BR_f + wN` with `ψ = ψ' = 1`, `B = B' = 0` and `D = zF − wN − I`; (3)
`C + QK' = Q(1 − δ)K + R_kK + wN + Π` with the producers' profit
`Π = QK' − Q(1 − δ)K − I`. -/
theorem ex_14_5_budgets {F : ℝ × ℝ → ℝ} {z K N FK FN R w C I V Rf Q K' δ : ℝ}
    (hhom : ∀ l : ℝ, 0 < l → F (l * K, l * N) = l * F (K, N))
    (hF : rx_HasPartials F FK FN (K, N)) (hR : R = z * FK) (hw : w = z * FN) :
    (C + I = R * K + w * N → C + I = z * F (K, N)) ∧
    (C + 1 * (V - (z * F (K, N) - w * N - I)) + 0 = 1 * V + 0 * Rf + w * N →
      C + I = z * F (K, N)) ∧
    (C + Q * K' = Q * (1 - δ) * K + R * K + w * N + (Q * K' - Q * (1 - δ) * K - I) →
      C + I = z * F (K, N)) := by
  have he := rx_euler_homog hhom hF
  have hinc : R * K + w * N = z * F (K, N) := by rw [hR, hw, he]; ring
  refine ⟨fun h1 => by rw [h1, hinc], fun h2 => by linarith, fun h3 => by linarith⟩

/-- **Exercise 14.5** (Miao, p. 508), **correction** for decentralisation 3. With the book's
budget the household's return on capital is `ρ = R_k + (1 − δ)Q` (`rx_dec3_euler`): the
household does not internalise that its capital `K_{t+1}` raises the capital producers' output
`Φ(I_{t+1}, K_{t+1})`. Given its Euler equation and `β ≠ 0`, the planner's (14.45) holds iff
`Eₜ[Λ_{t+1}Q_{t+1}Φ_K(I_{t+1}, K_{t+1})] = 0`. -/
theorem ex_14_5_dec3_iff {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {δ β l0 Q0 : ℝ}
    {R l1 Q1 b1 : S → ℝ} (hβ : β ≠ 0)
    (hdec3 : l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + (1 - δ) * Q1 s))) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) ↔
      rx_Es T h (fun s => l1 s * Q1 s * b1 s) = 0 := by
  have e : rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) =
      rx_Es T h (fun s => l1 s * (R s + (1 - δ) * Q1 s)) +
        rx_Es T h (fun s => l1 s * Q1 s * b1 s) := by
    rw [← rx_Es_add]
    congr 1
    funext s
    ring
  rw [e, hdec3]
  constructor
  · intro h1
    have : β * rx_Es T h (fun s => l1 s * Q1 s * b1 s) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hβ
  · intro h1
    rw [h1]
    ring

/-- The conditional expectation of a strictly positive quantity is strictly positive. -/
theorem rx_Es_pos {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {f : S → ℝ}
    (hf : ∀ s, 0 < f s) : 0 < rx_Es T h f := by
  unfold rx_Es
  obtain ⟨s, hs⟩ : ∃ s, 0 < T.cp h s := by
    by_contra hc
    push Not at hc
    have : ∑ s, T.cp h s ≤ 0 := Finset.sum_nonpos fun s _ => hc s
    rw [T.cp_sum] at this
    linarith
  exact Finset.sum_pos' (fun s _ => mul_nonneg (T.cp_nonneg h s) (hf s).le)
    ⟨s, Finset.mem_univ _, mul_pos hs (hf s)⟩

/-- **Exercise 14.5** (Miao, p. 508), **counterexample** for decentralisation 3: if
`Λ_{t+1}Q_{t+1}Φ_K(I_{t+1}, K_{t+1}) > 0` at every successor (e.g. (14.43) with investment
above its steady-state rate, `rx_Phi_K_pos`, `rx_phiQuad_K`) and `β > 0`, the household's
Euler equation of decentralisation 3 and the planner's (14.45) cannot both hold at the same
allocation and prices: the third decentralisation does not yield the planner's allocation. -/
theorem ex_14_5_dec3_counterexample {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ β l0 Q0 : ℝ} {R l1 Q1 b1 : S → ℝ} (hβ : 0 < β) (hpos : ∀ s, 0 < l1 s * Q1 s * b1 s)
    (hdec3 : l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + (1 - δ) * Q1 s)))
    (hplan : l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s)))) :
    False := by
  have := (ex_14_5_dec3_iff T h hβ.ne' hdec3).1 hplan
  linarith [rx_Es_pos T h hpos]

/-- **Exercise 14.5** (Miao, p. 508), corrected decentralisation 3: if the household's capital
also earns the capital producers' rent `Q_{t+1}Φ_K(I_{t+1}, K_{t+1})K_{t+1}` (so its return is
`ρ = R_k + Q(1 − δ + Φ_K)`; when `Φ` is linearly homogeneous and `QΦ_I = 1` this rent is the
producers' whole profit, `rx_producer_profit`), its Euler equation is the planner's (14.45); in
particular the book's version is right when `Φ_K ≡ 0`, e.g. `Φ(I, K) = vI`. -/
theorem ex_14_5_dec3_corrected {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ β y0 Q K1 l0 : ℝ} {y1 R Q1 b1 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - Q * K1))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + (R s + Q1 s * (1 - δ + b1 s)) * K1))
    (hmax : IsLocalMax (fun k => U0 (y0 - Q * k) + β * ∑ s,
      T.cp h s * U1 s (y1 s + (R s + Q1 s * (1 - δ + b1 s)) * k)) K1) :
    l0 * Q = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) ∧
      ((∀ s, b1 s = 0) → ∀ s, R s + Q1 s * (1 - δ + b1 s) = R s + (1 - δ) * Q1 s) :=
  ⟨rx_dec3_euler T h hU0 hU1 hmax, fun hb s => by rw [hb s]; ring⟩

/-- The rent of the capital producers: with `Φ` linearly homogeneous and `QΦ_I = 1`, the
profit `QΦ(I, K) − I` equals `QΦ_K K`. -/
theorem rx_producer_profit {Φ : ℝ × ℝ → ℝ} {Q I K a b : ℝ}
    (hhom : ∀ l : ℝ, 0 < l → Φ (l * I, l * K) = l * Φ (I, K))
    (hd : rx_HasPartials Φ a b (I, K)) (hQ : Q * a = 1) : Q * Φ (I, K) - I = Q * b * K := by
  rw [rx_euler_homog hhom hd]
  linear_combination I * hQ

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Proposition 14.3.1 (Exercise 14.4): marginal Q equals average Q

Miao, §14.3.3, pp. 498–499, and Exercise 14.4, p. 508, on the event tree of `RXTree`. A
variable chosen at a node `h` (date `t`) is `K_{t+1} = Kn h`; at a successor `g = s :: h` the
capital in place is `Kn g.tail`, the firm hires `N g`, invests `I g` and pays the dividend
`D g = z g F(Kn g.tail, N g) − w g N g − I g` (`rx_div`). The firm discounts with the
household's stochastic discount factor `m g = βΛ_g/Λ_{g.tail}` (`rx_sdf`).

* **Proposition 14.3.1**: if `F` and `Φ` are linearly homogeneous, then under (14.42), (14.48),
  (14.49), `w = zF_N` and the transversality condition `Eₜ[M_{t,t+n}Q_{t+n}K_{t+n+1}] → 0`,
  `QₜK_{t+1} = Pₜ`, the ex-dividend value `Pₜ = Σ_{j ≥ 1} Eₜ[M_{t,t+j}D_{t+j}]`, so
  `Qₜ = Pₜ/K_{t+1}` (`proposition_14_3_1`; the one-step identity is `rx_hayashi_step`).
  This `Pₜ` satisfies the book's definition `Pₜ = Eₜ[βΛ_{t+1}V_{t+1}/Λₜ]` with
  `V_{t+1} = D_{t+1} + P_{t+1}` (`rx_P_recursion`).
* `Qₜ = ∂Pₜ/∂K_{t+1}`: the firm's value `W(k)` (the supremum over plans feasible from `k` of a
  positively homogeneous valuation of their dividends, `rx_firmValue`) is homogeneous of degree
  one (`rx_firmValue_homog`, by scaling plans, `rx_scale_feasible`, `rx_div_scale`); so is
  `P(k) = Eₜ[m W(k)]`, whose derivative is therefore `P/K = Q` (`proposition_14_3_1_marginal`).
  A concrete valuation: the truncated present value (`rx_truncValue_homog`).
* The stock return equals the investment return,
  `R_{s,t+1} = (P_{t+1} + D_{t+1})/Pₜ = (Q_{t+1}(1 − δ + Φ_K) + R_{k,t+1})/Qₜ`
  (`rx_stock_return`), using `D = R_kK − I` (`rx_dividend_eq`). The book's displayed chain
  drops `K_{t+1}` from `R_{k,t+1}` in its second line (a misprint; the result is right).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- The firm's dividend at a non-root node `g`: `D = zF(K, N) − wN − I`, with `K = Kn g.tail`
the capital chosen at the parent node. -/
def rx_div {S : Type*} (F : ℝ × ℝ → ℝ) (z w N I Kn : List S → ℝ) (g : List S) : ℝ :=
  z g * F (Kn g.tail, N g) - w g * N g - I g

/-- The household's stochastic discount factor `m g = βΛ_g/Λ_{g.tail}`. -/
noncomputable def rx_sdf {S : Type*} (β : ℝ) (Λ : List S → ℝ) (g : List S) : ℝ :=
  β * Λ g / Λ g.tail

/-- The one-step identity behind Proposition 14.3.1 (Miao, p. 498): with `F`, `Φ` linearly
homogeneous, `w = zF_N`, `QΦ_I = 1` and (14.42),
`D_{t+1} + Q_{t+1}K_{t+2} = K_{t+1}(z_{t+1}F_K + Q_{t+1}(1 − δ + Φ_K))`. -/
theorem rx_hayashi_step {Φ F : ℝ × ℝ → ℝ} {δ z w N I K1 K2 Q a b FK FN : ℝ}
    (hΦhom : ∀ l : ℝ, 0 < l → Φ (l * I, l * K1) = l * Φ (I, K1))
    (hFhom : ∀ l : ℝ, 0 < l → F (l * K1, l * N) = l * F (K1, N))
    (hΦd : rx_HasPartials Φ a b (I, K1)) (hFd : rx_HasPartials F FK FN (K1, N))
    (hacc : K2 = (1 - δ) * K1 + Φ (I, K1)) (h48 : Q * a = 1) (hw : w = z * FN) :
    z * F (K1, N) - w * N - I + Q * K2 = K1 * (z * FK + Q * (1 - δ + b)) := by
  rw [hacc, rx_euler_homog hFhom hFd, rx_euler_homog hΦhom hΦd, hw]
  linear_combination I * h48

/-- **Proposition 14.3.1** (Miao, p. 498) = **Exercise 14.4** (p. 508). If `F` and `Φ` are
linearly homogeneous, `Λ > 0`, and the plan satisfies (14.42), (14.48), (14.49), `w = zF_N`,
and the transversality condition at `h`, then `QₕK_{t+1} = Pₕ`, where `Pₕ` is the ex-dividend
value of the firm, the limit of `Σ_{j<n} Eₜ[M_{t,t+j+1}D_{t+j+1}]`; hence `Qₕ = Pₕ/K_{t+1}`
(marginal Q equals average Q). -/
theorem proposition_14_3_1 {S : Type*} [Fintype S] (T : RXTree S) {Φ F : ℝ × ℝ → ℝ}
    {δ β : ℝ} {Kn I N z w Λ Q a b FK FN P : List S → ℝ}
    (hΦhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Φ (l * p.1, l * p.2) = l * Φ p)
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p)
    (hΦd : ∀ h s, rx_HasPartials Φ (a (s :: h)) (b (s :: h)) (I (s :: h), Kn h))
    (hFd : ∀ h s, rx_HasPartials F (FK (s :: h)) (FN (s :: h)) (Kn h, N (s :: h)))
    (hacc : ∀ h s, Kn (s :: h) = (1 - δ) * Kn h + Φ (I (s :: h), Kn h))
    (h48 : ∀ h s, Q (s :: h) * a (s :: h) = 1)
    (hw : ∀ h s, w (s :: h) = z (s :: h) * FN (s :: h))
    (h49 : ∀ h, Λ h * Q h = β * rx_E T (fun g => Λ g * (z g * FK g + Q g * (1 - δ + b g))) h)
    (hΛ : ∀ h, 0 < Λ h) (h : List S)
    (hP : Tendsto (fun n => ∑ j ∈ Finset.range n,
      rx_pv T (rx_sdf β Λ) (j + 1) (rx_div F z w N I Kn) h) atTop (𝓝 (P h)))
    (htvc : Tendsto (fun n => rx_pv T (rx_sdf β Λ) n (fun g => Q g * Kn g) h) atTop (𝓝 0)) :
    Q h * Kn h = P h ∧ (0 < Kn h → Q h = P h / Kn h) := by
  have hrec : ∀ h', Q h' * Kn h' = rx_E T (fun g => rx_sdf β Λ g *
      (rx_div F z w N I Kn g + Q g * Kn g)) h' := by
    intro h'
    have hs : ∀ s, rx_sdf β Λ (s :: h') * (rx_div F z w N I Kn (s :: h') + Q (s :: h') *
        Kn (s :: h')) = Kn h' / Λ h' * (β * (Λ (s :: h') * (z (s :: h') * FK (s :: h') +
          Q (s :: h') * (1 - δ + b (s :: h'))))) := by
      intro s
      have e := rx_hayashi_step (fun l hl => hΦhom l (I (s :: h'), Kn h') hl)
        (fun l hl => hFhom l (Kn h', N (s :: h')) hl) (hΦd h' s) (hFd h' s) (hacc h' s)
        (h48 h' s) (hw h' s)
      simp only [rx_div, rx_sdf, List.tail_cons]
      rw [e]
      field_simp
    simp only [rx_E]
    rw [Finset.sum_congr rfl fun s _ => by rw [hs s]]
    have : ∑ s, T.cp h' s * (Kn h' / Λ h' * (β * (Λ (s :: h') * (z (s :: h') * FK (s :: h') +
        Q (s :: h') * (1 - δ + b (s :: h')))))) = Kn h' / Λ h' * (β * rx_E T (fun g => Λ g *
          (z g * FK g + Q g * (1 - δ + b g))) h') := by
      simp only [rx_E, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, ← h49 h']
    have := hΛ h'
    field_simp
  have hlim := rx_pv_limit T hrec h htvc
  have heq : Q h * Kn h = P h := tendsto_nhds_unique hlim hP
  exact ⟨heq, fun hK => by rw [← heq]; field_simp⟩

/-- Miao, p. 498: the ex-dividend value defined as the present value of future dividends
satisfies the book's definition `Pₜ = Eₜ[βΛ_{t+1}V_{t+1}/Λₜ]` with the cum-dividend value
`V_{t+1} = D_{t+1} + P_{t+1}`. -/
theorem rx_P_recursion {S : Type*} [Fintype S] (T : RXTree S) {m d P : List S → ℝ}
    (hP : ∀ h, Tendsto (fun n => ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d h) atTop (𝓝 (P h)))
    (h : List S) : P h = rx_E T (fun g => m g * (d g + P g)) h := by
  have h1 : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), rx_pv T m (j + 1) d h) atTop
      (𝓝 (P h)) := (hP h).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => ∑ j ∈ Finset.range (n + 1), rx_pv T m (j + 1) d h) atTop
      (𝓝 (rx_E T (fun g => m g * (d g + P g)) h)) := by
    have e : ∀ n, ∑ j ∈ Finset.range (n + 1), rx_pv T m (j + 1) d h =
        ∑ s, T.cp h s * (m (s :: h) * (d (s :: h) +
          ∑ j ∈ Finset.range n, rx_pv T m (j + 1) d (s :: h))) := by
      intro n
      rw [Finset.sum_range_succ', rx_pv_sum,
        show rx_pv T m (0 + 1) d h = ∑ s, T.cp h s * (m (s :: h) * d (s :: h)) from rfl,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp only [e, rx_E]
    refine tendsto_finsetSum _ fun s _ => ?_
    exact ((tendsto_const_nhds.add (hP (s :: h))).const_mul _).const_mul _
  exact tendsto_nhds_unique h1 h2

/-- Miao, p. 499: `D_{t+1} = R_{k,t+1}K_{t+1} − I_{t+1}` when `F` is linearly homogeneous and
`R_k = zF_K`, `w = zF_N`. -/
theorem rx_dividend_eq {F : ℝ × ℝ → ℝ} {z w R N I K FK FN : ℝ}
    (hFhom : ∀ l : ℝ, 0 < l → F (l * K, l * N) = l * F (K, N))
    (hFd : rx_HasPartials F FK FN (K, N)) (hR : R = z * FK) (hw : w = z * FN) :
    z * F (K, N) - w * N - I = R * K - I := by
  rw [rx_euler_homog hFhom hFd, hR, hw]
  ring

/-- Miao, pp. 498–499: the stock return equals the investment return. With `Pₜ = QₜK_{t+1}`,
`P_{t+1} = Q_{t+1}K_{t+2}` (Proposition 14.3.1), `D_{t+1} = R_{k,t+1}K_{t+1} − I_{t+1}`,
(14.42), Euler's identity `Φ = Φ_I I + Φ_K K` and `Q_{t+1}Φ_I = 1`:
`(P_{t+1} + D_{t+1})/Pₜ = (Q_{t+1}(1 − δ + Φ_K) + R_{k,t+1})/Qₜ`. -/
theorem rx_stock_return {δ P P' D' Q Q' K1 K2 R' I' Φv a' b' : ℝ} (hP : P = Q * K1)
    (hP' : P' = Q' * K2) (hD : D' = R' * K1 - I') (hK2 : K2 = (1 - δ) * K1 + Φv)
    (hΦ : Φv = I' * a' + K1 * b') (hQ' : Q' * a' = 1) (hQ : Q ≠ 0) (hK1 : K1 ≠ 0) :
    (P' + D') / P = (Q' * (1 - δ + b') + R') / Q := by
  rw [hP, hP', hD, hK2, hΦ]
  have : Q' * ((1 - δ) * K1 + (I' * a' + K1 * b')) + (R' * K1 - I') =
      K1 * (Q' * (1 - δ + b') + R') := by linear_combination I' * hQ'
  rw [this]
  field_simp

/-- The plans feasible for the firm from initial capital `k`: `p = (I, K, N)` with `K` the
capital in place at each node, `K_root = k` and (14.42). -/
def rx_firmFeasible {S : Type*} (δ : ℝ) (Φ : ℝ × ℝ → ℝ) (k : ℝ) :
    Set ((List S → ℝ) × (List S → ℝ) × (List S → ℝ)) :=
  {p | p.2.1 [] = k ∧ ∀ h s, p.2.1 (s :: h) = (1 - δ) * p.2.1 h + Φ (p.1 h, p.2.1 h)}

/-- The dividends of a plan `p = (I, K, N)`. -/
def rx_divPlan {S : Type*} (F : ℝ × ℝ → ℝ) (z w : List S → ℝ)
    (p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)) (g : List S) : ℝ :=
  z g * F (p.2.1 g, p.2.2 g) - w g * p.2.2 g - p.1 g

/-- The firm's value from capital `k`: the supremum, over feasible plans, of a valuation `val`
of their dividends. -/
noncomputable def rx_firmValue {S : Type*} (val : (List S → ℝ) → ℝ) (δ : ℝ)
    (Φ F : ℝ × ℝ → ℝ) (z w : List S → ℝ) (k : ℝ) : ℝ :=
  sSup ((fun p => val (rx_divPlan F z w p)) '' rx_firmFeasible δ Φ k)

/-- Scaling a plan: `(λI, λK, λN)`. -/
def rx_scale {S : Type*} (l : ℝ) (p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)) :
    (List S → ℝ) × (List S → ℝ) × (List S → ℝ) :=
  (fun g => l * p.1 g, fun g => l * p.2.1 g, fun g => l * p.2.2 g)

/-- With `Φ` linearly homogeneous, a plan feasible from `k` scales to a plan feasible from
`λk`. -/
theorem rx_scale_feasible {S : Type*} {δ : ℝ} {Φ : ℝ × ℝ → ℝ}
    (hΦhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Φ (l * p.1, l * p.2) = l * Φ p) {l k : ℝ}
    (hl : 0 < l) {p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)}
    (hp : p ∈ rx_firmFeasible δ Φ k) : rx_scale l p ∈ rx_firmFeasible δ Φ (l * k) := by
  refine ⟨by simp [rx_scale, hp.1], fun h s => ?_⟩
  simp only [rx_scale]
  rw [hp.2 h s, hΦhom l (p.1 h, p.2.1 h) hl]
  ring

/-- With `F` linearly homogeneous, the dividends of the scaled plan are `λ` times the
dividends. -/
theorem rx_div_scale {S : Type*} {F : ℝ × ℝ → ℝ} {z w : List S → ℝ}
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p) {l : ℝ}
    (hl : 0 < l) (p : (List S → ℝ) × (List S → ℝ) × (List S → ℝ)) :
    rx_divPlan F z w (rx_scale l p) = fun g => l * rx_divPlan F z w p g := by
  funext g
  simp only [rx_divPlan, rx_scale]
  rw [hFhom l (p.2.1 g, p.2.2 g) hl]
  ring

open Pointwise in
/-- Miao, p. 498 (Proposition 14.3.1, `∂Pₜ/∂K_{t+1}`): with `F`, `Φ` linearly homogeneous and a
positively homogeneous valuation, the firm's value is homogeneous of degree one in capital. -/
theorem rx_firmValue_homog {S : Type*} {val : (List S → ℝ) → ℝ} {δ : ℝ} {Φ F : ℝ × ℝ → ℝ}
    {z w : List S → ℝ}
    (hval : ∀ (l : ℝ) (D : List S → ℝ), 0 < l → val (fun g => l * D g) = l * val D)
    (hΦhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → Φ (l * p.1, l * p.2) = l * Φ p)
    (hFhom : ∀ (l : ℝ) (p : ℝ × ℝ), 0 < l → F (l * p.1, l * p.2) = l * F p) {l k : ℝ}
    (hl : 0 < l) : rx_firmValue val δ Φ F z w (l * k) = l * rx_firmValue val δ Φ F z w k := by
  unfold rx_firmValue
  have hset : (fun p => val (rx_divPlan F z w p)) '' rx_firmFeasible δ Φ (l * k) =
      l • ((fun p => val (rx_divPlan F z w p)) '' rx_firmFeasible δ Φ k) := by
    ext x
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨val (rx_divPlan F z w (rx_scale l⁻¹ p)), ⟨rx_scale l⁻¹ p, ?_, rfl⟩, ?_⟩
      · have := rx_scale_feasible hΦhom (inv_pos.2 hl) hp
        rwa [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] at this
      · rw [rx_div_scale hFhom (inv_pos.2 hl), hval _ _ (inv_pos.2 hl), ← mul_assoc,
          mul_inv_cancel₀ hl.ne', one_mul]
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨rx_scale l p, rx_scale_feasible hΦhom hl hp,
        by rw [rx_div_scale hFhom hl, hval _ _ hl]⟩
  rw [hset, Real.sSup_smul_of_nonneg hl.le, smul_eq_mul]

/-- `rx_pv` is linear in the payoff. -/
theorem rx_pv_smul {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (n : ℕ) (l : ℝ)
    (x : List S → ℝ) (h : List S) : rx_pv T m n (fun g => l * x g) h = l * rx_pv T m n x h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [rx_pv, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- A concrete positively homogeneous valuation: the present value of dividends over the first
`N` periods, `Σ_{j<N} E₀[M_{0,j}D_j]`. -/
theorem rx_truncValue_homog {S : Type*} [Fintype S] (T : RXTree S) (m : List S → ℝ) (N : ℕ)
    (l : ℝ) (D : List S → ℝ) :
    ∑ j ∈ Finset.range N, rx_pv T m j (fun g => l * D g) [] =
      l * ∑ j ∈ Finset.range N, rx_pv T m j D [] := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => rx_pv_smul T m j l D []

/-- **Proposition 14.3.1** (Miao, p. 498), `Qₜ = ∂Pₜ/∂K_{t+1}`. Let the ex-dividend value as a
function of `K_{t+1} = k` be `P(k) = Eₜ[m_{t+1}W_{t+1}(k)]`, each continuation value
`W_{t+1}(s)` homogeneous of degree one (`rx_firmValue_homog`). Then `P` is homogeneous of
degree one, and if `P(K_{t+1}) = QₜK_{t+1}` (`proposition_14_3_1`) with `K_{t+1} > 0`, then
`P′(K_{t+1}) = Qₜ`. -/
theorem proposition_14_3_1_marginal {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {m : S → ℝ} {W : S → ℝ → ℝ} (hW : ∀ s (l k : ℝ), 0 < l → W s (l * k) = l * W s k)
    {Q K1 : ℝ} (hK1 : 0 < K1) (hPQ : rx_Es T h (fun s => m s * W s K1) = Q * K1) :
    (∀ l k : ℝ, 0 < l → rx_Es T h (fun s => m s * W s (l * k)) =
      l * rx_Es T h (fun s => m s * W s k)) ∧
    HasDerivAt (fun k => rx_Es T h (fun s => m s * W s k)) Q K1 := by
  have hhom : ∀ l k : ℝ, 0 < l → rx_Es T h (fun s => m s * W s (l * k)) =
      l * rx_Es T h (fun s => m s * W s k) := by
    intro l k hl
    rw [← rx_Es_mul_left]
    congr 1
    funext s
    rw [hW s l k hl]
    ring
  refine ⟨hhom, ?_⟩
  have := rx_homog_hasDerivAt (P := fun k => rx_Es T h (fun s => m s * W s k))
    (fun l k hl _ => hhom l k hl) hK1
  simp only [hPQ] at this
  rwa [mul_div_cancel_right₀ Q hK1.ne'] at this

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Investment adjustment costs (14.50)–(14.52) and Exercise 14.6

Miao, §14.3.3, pp. 500–501, and Exercise 14.6, p. 508, on the event tree of `RXTree`.

* With `K_{t+1} = (1 − δ)Kₜ + G(Iₜ, I_{t−1})`, the firm's first-order conditions (14.50) and
  (14.51) are the stationarity of its Lagrangian in `Iₜ` and in `K_{t+1}` (`eq_14_50`,
  `eq_14_51`); `Iₜ` enters `G(Iₜ, I_{t−1})` at `t` and `G(I_{t+1}, Iₜ)` at every successor.
* (14.52) `G(I, I₋) = (1 − S(I/I₋))I`: partial derivatives `G₁ = 1 − S(x) − xS′(x)`,
  `G₂ = S′(x)x²`, `x = I/I₋` (`rx_G52`, `rx_G52_d1`, `rx_G52_d2`); with `S(1) = S′(1) = 0`,
  `G(I, I) = I`, `G₁ = 1`, `G₂ = 0` at `x = 1` (`rx_G52_steady`); the steady state has
  `I/K = δ`, `Q = 1`, `zF_K = 1/β − 1 + δ`, independently of `κ` (`eq_14_52_steady`).
* **Exercise 14.6** (risk neutrality: `Λ` constant, so the discount factor is `β`). Each
  log-linearised equation is the derivative at `ε = 0` of the equation along the path
  `X = X̄e^{εx̂}` of every variable (log-deviations `x̂`), at the steady state `I/K = δ`,
  `Q = 1`, `R̄_k = 1/β − 1 + δ`:
  - (14.43): `q̂ₜ + κδ(îₜ − k̂ₜ) = 0` (`ex_14_6_invest_43`, solved
    `îₜ − k̂ₜ = −q̂ₜ/(κδ)` in `ex_14_6_invest_43_solved`), `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ`
    (`ex_14_6_capital_43`) and `q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + (1 − δ)q̂_{t+1} − κδ²(î_{t+1} −
    k̂_{t+1})]` (`ex_14_6_Q_43`), which with the investment equation is
    `q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + q̂_{t+1}]` (`ex_14_6_Q_43_solved`);
  - (14.52): `q̂ₜ − κ(îₜ − î_{t−1}) + βκ(Eₜî_{t+1} − îₜ) = 0` (`ex_14_6_invest_52`), i.e.
    `îₜ = î_{t−1}/(1 + β) + βEₜî_{t+1}/(1 + β) + q̂ₜ/(κ(1 + β))` (`ex_14_6_invest_52_solved`),
    `q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + (1 − δ)q̂_{t+1}]` (`ex_14_6_Q_52`) and
    `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ` (`ex_14_6_capital_52`).
  - The differences (`ex_14_6_differences`): under (14.43) the investment rate depends only on
    current `q̂`; under (14.52) investment depends on lagged investment with weight
    `1/(1 + β) ∈ (0, 1)` (inertia), and the `q̂` equations differ by the term `δq̂_{t+1}`.
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- Miao, (14.50), p. 500. The terms of the firm's Lagrangian (multiplier `ΛQ` on
`K_{t+1} = (1 − δ)Kₜ + G(Iₜ, I_{t−1})`) in `Iₜ = x` at the node `h` are
`Λₜ(−x + QₜG(x, I_{t−1})) + βEₜΛ_{t+1}Q_{t+1}G(I_{t+1}, x)`. Their derivative is
`Λₜ(QₜG₁ + Eₜ[βΛ_{t+1}Q_{t+1}G₂/Λₜ] − 1)`; for `Λₜ ≠ 0` stationarity is (14.50):
`QₜG₁(Iₜ, I_{t−1}) + Eₜ[βΛ_{t+1}Q_{t+1}G₂(I_{t+1}, Iₜ)/Λₜ] = 1`. -/
theorem eq_14_50 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {G : ℝ × ℝ → ℝ}
    {β Λt Qt It Ip G1 : ℝ} {Λ Q I G2 : S → ℝ} (hΛ : Λt ≠ 0)
    (hG1 : HasDerivAt (fun x => G (x, Ip)) G1 It)
    (hG2 : ∀ s, HasDerivAt (fun x => G (I s, x)) (G2 s) It) :
    HasDerivAt (fun x => Λt * (-x + Qt * G (x, Ip)) + β * ∑ s, T.cp h s * (Λ s * Q s *
        G (I s, x)))
      (Λt * (Qt * G1 + rx_Es T h (fun s => β * Λ s / Λt * Q s * G2 s) - 1)) It ∧
    (Λt * (Qt * G1 + rx_Es T h (fun s => β * Λ s / Λt * Q s * G2 s) - 1) = 0 ↔
      Qt * G1 + rx_Es T h (fun s => β * Λ s / Λt * Q s * G2 s) = 1) := by
  refine ⟨?_, ?_⟩
  · have hs : HasDerivAt (fun x => ∑ s, T.cp h s * (Λ s * Q s * G (I s, x)))
        (∑ s, T.cp h s * (Λ s * Q s * G2 s)) It :=
      HasDerivAt.fun_sum fun s _ => ((hG2 s).const_mul _).const_mul _
    have := (((hasDerivAt_id' It).neg.add (hG1.const_mul Qt)).const_mul Λt).add
      (hs.const_mul β)
    refine this.congr_deriv ?_
    have e : Λt * ∑ s, T.cp h s * (β * Λ s / Λt * Q s * G2 s) =
        β * ∑ s, T.cp h s * (Λ s * Q s * G2 s) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by field_simp
    simp only [rx_Es]
    linear_combination -e
  · constructor
    · intro h0
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 hΛ
      · linarith
    · intro h0
      rw [h0, sub_self, mul_zero]

/-- Miao, (14.51), p. 500. The terms of the Lagrangian in `K_{t+1} = k` are
`−ΛₜQₜk + βEₜΛ_{t+1}[z_{t+1}F(k, N_{t+1}) + Q_{t+1}(1 − δ)k]` (with investment adjustment costs
`K_{t+1}` does not enter `G`); stationarity is (14.51)
`ΛₜQₜ = βEₜΛ_{t+1}[z_{t+1}F_K(K_{t+1}, N_{t+1}) + Q_{t+1}(1 − δ)]`. -/
theorem eq_14_51 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {F : ℝ × ℝ → ℝ}
    {β δ Λt Qt K1 : ℝ} {Λ Q z N FK : S → ℝ}
    (hF : ∀ s, HasDerivAt (fun k => F (k, N s)) (FK s) K1) :
    HasDerivAt (fun k => Λt * (-(Qt * k)) + β * ∑ s, T.cp h s * (Λ s * (z s * F (k, N s) +
        Q s * (1 - δ) * k)))
      (β * rx_Es T h (fun s => Λ s * (z s * FK s + Q s * (1 - δ))) - Λt * Qt) K1 ∧
    (β * rx_Es T h (fun s => Λ s * (z s * FK s + Q s * (1 - δ))) - Λt * Qt = 0 ↔
      Λt * Qt = β * rx_Es T h (fun s => Λ s * (z s * FK s + Q s * (1 - δ)))) := by
  refine ⟨?_, by constructor <;> intro h0 <;> linarith⟩
  have hs : HasDerivAt (fun k => ∑ s, T.cp h s * (Λ s * (z s * F (k, N s) + Q s * (1 - δ) * k)))
      (∑ s, T.cp h s * (Λ s * (z s * FK s + Q s * (1 - δ) * 1))) K1 :=
    HasDerivAt.fun_sum fun s _ => ((((hF s).const_mul (z s)).add
      ((hasDerivAt_id' K1).const_mul _)).const_mul _).const_mul _
  have := ((((hasDerivAt_id' K1).const_mul Qt).neg).const_mul Λt).add (hs.const_mul β)
  refine this.congr_deriv ?_
  simp only [rx_Es, mul_one]
  ring

/-- The investment adjustment cost function (14.52), `G(I, I₋) = (1 − S(I/I₋))I`. -/
noncomputable def rx_G52 (S : ℝ → ℝ) (I Ip : ℝ) : ℝ := (1 - S (I / Ip)) * I

/-- Miao, (14.52), p. 500: `G₁ = 1 − S(x) − xS′(x)` with `x = I/I₋`. -/
theorem rx_G52_d1 {S : ℝ → ℝ} {dS I Ip : ℝ} (hS : HasDerivAt S dS (I / Ip)) :
    HasDerivAt (fun y => rx_G52 S y Ip) (1 - S (I / Ip) - I / Ip * dS) I := by
  have h1 := hS.comp I ((hasDerivAt_id' I).div_const Ip)
  have := ((hasDerivAt_const I (1 : ℝ)).sub h1).mul (hasDerivAt_id' I)
  unfold rx_G52
  refine this.congr_deriv ?_
  simp only [Function.comp_def, Pi.sub_apply]
  ring

/-- Miao, (14.52), p. 500: `G₂ = S′(x)x²` with `x = I/I₋`, `I₋ ≠ 0`. -/
theorem rx_G52_d2 {S : ℝ → ℝ} {dS I Ip : ℝ} (hIp : Ip ≠ 0) (hS : HasDerivAt S dS (I / Ip)) :
    HasDerivAt (fun y => rx_G52 S I y) (dS * (I / Ip) ^ 2) Ip := by
  have hd : HasDerivAt (fun y => I / y) (-(I / Ip ^ 2)) Ip := by
    have := (hasDerivAt_inv hIp).const_mul I
    simpa [div_eq_mul_inv] using this
  have h1 := hS.comp Ip hd
  have := ((hasDerivAt_const Ip (1 : ℝ)).sub h1).mul_const I
  unfold rx_G52
  refine this.congr_deriv ?_
  field_simp
  ring

/-- Miao, p. 500: with `S(1) = S′(1) = 0`, `G(I, I) = I` (for every `I`), and at `I = I₋ ≠ 0`
the partial derivatives are `G₁ = 1`, `G₂ = 0`. -/
theorem rx_G52_steady {S : ℝ → ℝ} {dS1 I : ℝ} (hS0 : S 1 = 0) (hdS : dS1 = 0) (hI : I ≠ 0) :
    rx_G52 S I I = I ∧ 1 - S (I / I) - I / I * dS1 = 1 ∧ dS1 * (I / I) ^ 2 = 0 := by
  simp [rx_G52, div_self hI, hS0, hdS]

/-- `G(I, I) = I` also at `I = 0`. -/
theorem rx_G52_diag {S : ℝ → ℝ} (hS0 : S 1 = 0) (I : ℝ) : rx_G52 S I I = I := by
  rcases eq_or_ne I 0 with h | h
  · simp [rx_G52, h]
  · exact (rx_G52_steady hS0 rfl h).1

/-- Miao, p. 500: "these assumptions ensure that the steady-state investment rate `I/K` is
equal to `δ` and `Q = 1`" and `κ` does not affect the nonstochastic steady state. In a steady
state with constant `Λ`, constant investment `I ≠ 0` and `K > 0`: `K = (1 − δ)K + G(I, I)`,
(14.50) `QG₁ + βQG₂ = 1` and (14.51) `Q = β(zF_K + Q(1 − δ))` give `I/K = δ`, `Q = 1` and
`zF_K = 1/β − 1 + δ`. -/
theorem eq_14_52_steady {S : ℝ → ℝ} {dS1 δ β K I Q zFK : ℝ} (hS0 : S 1 = 0) (hdS : dS1 = 0)
    (hβ : 0 < β) (hK : 0 < K) (hI : I ≠ 0) (hacc : K = (1 - δ) * K + rx_G52 S I I)
    (h50 : Q * (1 - S (I / I) - I / I * dS1) + β * Q * (dS1 * (I / I) ^ 2) = 1)
    (h51 : Q = β * (zFK + Q * (1 - δ))) : I / K = δ ∧ Q = 1 ∧ zFK = 1 / β - 1 + δ := by
  obtain ⟨e0, e1, e2⟩ := rx_G52_steady hS0 hdS hI
  rw [e0] at hacc
  rw [e1, e2] at h50
  have hQ : Q = 1 := by linarith
  refine ⟨?_, hQ, ?_⟩
  · field_simp
    linarith
  · rw [hQ] at h51
    field_simp
    linarith

/-- `ε ↦ c·e^{εa}` has derivative `ca` at `0`. -/
theorem rx_hasDerivAt_exp (c a : ℝ) : HasDerivAt (fun ε => c * Real.exp (ε * a)) (c * a) 0 := by
  have := (((hasDerivAt_id' (0 : ℝ)).mul_const a).exp).const_mul c
  refine this.congr_deriv ?_
  simp

/-- `ε ↦ e^{εa}` has derivative `a` at `0`. -/
theorem rx_hasDerivAt_exp1 (a : ℝ) : HasDerivAt (fun ε => Real.exp (ε * a)) a 0 := by
  have := ((hasDerivAt_id' (0 : ℝ)).mul_const a).exp
  refine this.congr_deriv ?_
  simp

/-- Along the path `I = Īe^{εî}`, `K = K̄e^{εk̂}` with `Ī = δK̄`, the investment rate is
`I/K = δe^{ε(î − k̂)}`. -/
theorem rx_ratio_path {δ Kb ι k ε : ℝ} (hK : Kb ≠ 0) :
    δ * Kb * Real.exp (ε * ι) / (Kb * Real.exp (ε * k)) = δ * Real.exp (ε * (ι - k)) := by
  rw [mul_sub, Real.exp_sub]
  have := Real.exp_pos (ε * k)
  field_simp

/-- The rate path `ε ↦ δe^{ε(î − k̂)}` composed with a function differentiable at `δ`. -/
theorem rx_hasDerivAt_rate {f : ℝ → ℝ} {df δ ι k : ℝ} (hf : HasDerivAt f df δ) :
    HasDerivAt (fun ε => f (δ * Real.exp (ε * (ι - k)))) (df * (δ * (ι - k))) 0 := by
  have hp := rx_hasDerivAt_exp δ (ι - k)
  have hf' : HasDerivAt f df (δ * Real.exp (0 * (ι - k))) := by simpa using hf
  exact hf'.comp 0 hp

/-- **Exercise 14.6** (Miao, p. 508), (14.43), the investment equation `Qϕ′(I/K) = 1`. Along
`Q = e^{εq̂}`, `I/K = δe^{ε(î − k̂)}`, with `ϕ′(δ) = 1` and `ϕ″(δ) = κ`, the derivative at
`ε = 0` is `q̂ + κδ(î − k̂)`: the log-linearised equation is `q̂ₜ + κδ(îₜ − k̂ₜ) = 0`. -/
theorem ex_14_6_invest_43 {dϕ : ℝ → ℝ} {δ κ q ι k : ℝ} (h1 : dϕ δ = 1)
    (hκ : HasDerivAt dϕ κ δ) :
    HasDerivAt (fun ε => Real.exp (ε * q) * dϕ (δ * Real.exp (ε * (ι - k))) - 1)
      (q + κ * δ * (ι - k)) 0 := by
  have h := ((rx_hasDerivAt_exp 1 q).mul (rx_hasDerivAt_rate (ι := ι) (k := k) hκ)).sub_const 1
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun ε => by simp)
  simp [h1]
  ring

/-- **Exercise 14.6**, (14.43): solving the linearised investment equation, the investment
rate is proportional to the current `q̂`: `îₜ − k̂ₜ = −q̂ₜ/(κδ)` (`κ < 0`, so `î − k̂` rises
with `q̂`). -/
theorem ex_14_6_invest_43_solved {δ κ q ι k : ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 0) :
    q + κ * δ * (ι - k) = 0 ↔ ι - k = -q / (κ * δ) := by
  constructor
  · intro h0
    field_simp
    linarith
  · intro h0
    rw [h0]
    field_simp
    ring

/-- **Exercise 14.6**, (14.43), capital accumulation `K_{t+1} = (1 − δ)Kₜ + ϕ(Iₜ/Kₜ)Kₜ`. Along
`K_{t+1} = K̄e^{εk̂′}`, `Kₜ = K̄e^{εk̂}`, `Iₜ/Kₜ = δe^{ε(î − k̂)}`, with `ϕ(δ) = δ`, `ϕ′(δ) = 1`,
the derivative is `K̄(k̂′ − (1 − δ)k̂ − δî)`: `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ`. -/
theorem ex_14_6_capital_43 {ϕ : ℝ → ℝ} {δ Kb k' k ι : ℝ} (h0 : ϕ δ = δ)
    (h1 : HasDerivAt ϕ 1 δ) :
    HasDerivAt (fun ε => Kb * Real.exp (ε * k') - (1 - δ) * (Kb * Real.exp (ε * k))
        - ϕ (δ * Real.exp (ε * (ι - k))) * (Kb * Real.exp (ε * k)))
      (Kb * (k' - (1 - δ) * k - δ * ι)) 0 := by
  have h := ((rx_hasDerivAt_exp Kb k').sub ((rx_hasDerivAt_exp Kb k).const_mul (1 - δ))).sub
    ((rx_hasDerivAt_rate (ι := ι) (k := k) h1).mul (rx_hasDerivAt_exp Kb k))
  refine h.congr_deriv ?_
  simp [h0]
  ring

/-- **Exercise 14.6**, (14.43), the Q equation under risk neutrality,
`Qₜ = βEₜ[R_{k,t+1} + Q_{t+1}(1 − δ + Φ_K)]` with `Φ_K = ϕ(i) − iϕ′(i)`. Along
`Qₜ = e^{εq̂}`, `R_k(s) = R̄e^{εr̂(s)}`, `Q(s) = e^{εq̂(s)}`, `i(s) = δe^{ε(î(s) − k̂(s))}`, with
`ϕ(δ) = δ`, `ϕ′(δ) = 1`, `ϕ″(δ) = κ`, the derivative at `0` is
`q̂ − βEₜ[R̄r̂ + (1 − δ)q̂′ − κδ²(î′ − k̂′)]`. -/
theorem ex_14_6_Q_43 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {ϕ dϕ : ℝ → ℝ}
    {δ κ β Rb q : ℝ} {r q1 ι1 k1 : S → ℝ} (h0 : ϕ δ = δ) (h1 : dϕ δ = 1)
    (hϕ : HasDerivAt ϕ 1 δ) (hκ : HasDerivAt dϕ κ δ) :
    HasDerivAt (fun ε => Real.exp (ε * q) - β * ∑ s, T.cp h s * (Rb * Real.exp (ε * r s) +
        Real.exp (ε * q1 s) * (1 - δ + (ϕ (δ * Real.exp (ε * (ι1 s - k1 s))) -
          δ * Real.exp (ε * (ι1 s - k1 s)) * dϕ (δ * Real.exp (ε * (ι1 s - k1 s)))))))
      (q - β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s
        - κ * δ ^ 2 * (ι1 s - k1 s))) 0 := by
  have hs : ∀ s, HasDerivAt (fun ε => T.cp h s * (Rb * Real.exp (ε * r s) +
      Real.exp (ε * q1 s) * (1 - δ + (ϕ (δ * Real.exp (ε * (ι1 s - k1 s))) -
        δ * Real.exp (ε * (ι1 s - k1 s)) * dϕ (δ * Real.exp (ε * (ι1 s - k1 s)))))))
      (T.cp h s * (Rb * r s + (1 - δ) * q1 s - κ * δ ^ 2 * (ι1 s - k1 s))) 0 := by
    intro s
    have hA := rx_hasDerivAt_rate (ι := ι1 s) (k := k1 s) hϕ
    have hB := rx_hasDerivAt_exp δ (ι1 s - k1 s)
    have hC := rx_hasDerivAt_rate (ι := ι1 s) (k := k1 s) hκ
    have hK := (hA.sub (hB.mul hC)).const_add (1 - δ)
    have := ((rx_hasDerivAt_exp Rb (r s)).add ((rx_hasDerivAt_exp1 (q1 s)).mul hK)).const_mul
      (T.cp h s)
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply, zero_mul, Real.exp_zero, mul_one, h0, h1]
    ring
  exact (rx_hasDerivAt_exp1 q).sub
    ((HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hs s).const_mul β)

/-- **Exercise 14.6**, (14.43): substituting the linearised investment equation at `t + 1`
(`κδ(î′ − k̂′) = −q̂′`) into `ex_14_6_Q_43`, the Q equation is
`q̂ₜ = βEₜ[R̄_k r̂_{k,t+1} + q̂_{t+1}]`. -/
theorem ex_14_6_Q_43_solved {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ κ β Rb q : ℝ} {r q1 ι1 k1 : S → ℝ} (hinv : ∀ s, q1 s + κ * δ * (ι1 s - k1 s) = 0) :
    q - β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s - κ * δ ^ 2 * (ι1 s - k1 s)) = 0 ↔
      q = β * rx_Es T h (fun s => Rb * r s + q1 s) := by
  have e : ∀ s, Rb * r s + (1 - δ) * q1 s - κ * δ ^ 2 * (ι1 s - k1 s) = Rb * r s + q1 s := by
    intro s
    linear_combination (-δ) * hinv s
  simp only [e]
  constructor <;> intro h0 <;> linarith

/-- The functions `g₁(x) = 1 − S(x) − xS′(x)` and `g₂(x) = S′(x)x²` of (14.52) have, with
`S(1) = S′(1) = 0` and `S″(1) = κ`, the values `g₁(1) = 1`, `g₂(1) = 0` and derivatives
`g₁′(1) = −κ`, `g₂′(1) = κ`. -/
theorem rx_g52_derivs {S dS : ℝ → ℝ} {κ : ℝ} (hS0 : S 1 = 0) (hdS0 : dS 1 = 0)
    (hS : HasDerivAt S (dS 1) 1) (hκ : HasDerivAt dS κ 1) :
    (1 - S 1 - 1 * dS 1 = 1) ∧ dS 1 * 1 ^ 2 = 0 ∧
      HasDerivAt (fun x => 1 - S x - x * dS x) (-κ) 1 ∧
      HasDerivAt (fun x => dS x * x ^ 2) κ 1 := by
  refine ⟨by simp [hS0, hdS0], by simp [hdS0], ?_, ?_⟩
  · have := ((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub hS).sub ((hasDerivAt_id' 1).mul hκ)
    refine this.congr_deriv ?_
    simp [hdS0]
  · have := hκ.mul ((hasDerivAt_id' (1 : ℝ)).pow 2)
    refine this.congr_deriv ?_
    simp [hdS0]

/-- `g₁(x) = 1 − S(x) − xS′(x)`, so that `G₁(I, I₋) = g₁(I/I₋)` for (14.52) (`rx_G52_d1`). -/
noncomputable def rx_g1 (S dS : ℝ → ℝ) (x : ℝ) : ℝ := 1 - S x - x * dS x

/-- `g₂(x) = S′(x)x²`, so that `G₂(I, I₋) = g₂(I/I₋)` for (14.52) (`rx_G52_d2`). -/
noncomputable def rx_g2 (dS : ℝ → ℝ) (x : ℝ) : ℝ := dS x * x ^ 2

/-- **Exercise 14.6** (Miao, p. 508), (14.52), the investment equation (14.50) under risk
neutrality, `QₜG₁(Iₜ, I_{t−1}) + βEₜQ_{t+1}G₂(I_{t+1}, Iₜ) = 1`, with `G₁ = g₁(Iₜ/I_{t−1})`,
`G₂ = g₂(I_{t+1}/Iₜ)`. Along `Q = e^{εq̂}`, `Iₜ/I_{t−1} = e^{ε(îₜ − î_{t−1})}`,
`I_{t+1}/Iₜ = e^{ε(î_{t+1} − îₜ)}`, with `S(1) = S′(1) = 0`, `S″(1) = κ`, the derivative at `0`
is `q̂ₜ − κ(îₜ − î_{t−1}) + βκ(Eₜî_{t+1} − îₜ)`. -/
theorem ex_14_6_invest_52 {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Sf dS : ℝ → ℝ} {κ β q ι ιm : ℝ} {q1 ι1 : S → ℝ} (hS0 : Sf 1 = 0) (hdS0 : dS 1 = 0)
    (hS : HasDerivAt Sf (dS 1) 1) (hκ : HasDerivAt dS κ 1) :
    HasDerivAt (fun ε => Real.exp (ε * q) * rx_g1 Sf dS (Real.exp (ε * (ι - ιm))) + β * ∑ s,
        T.cp h s * (Real.exp (ε * q1 s) * rx_g2 dS (Real.exp (ε * (ι1 s - ι)))) - 1)
      (q - κ * (ι - ιm) + β * κ * (rx_Es T h ι1 - ι)) 0 := by
  obtain ⟨e1, e2, d1, d2⟩ := rx_g52_derivs hS0 hdS0 hS hκ
  have d1' : HasDerivAt (rx_g1 Sf dS) (-κ) (Real.exp (0 * (ι - ιm))) := by
    rw [zero_mul, Real.exp_zero]
    exact d1
  have hA := (rx_hasDerivAt_exp1 q).mul (d1'.comp 0 (rx_hasDerivAt_exp1 (ι - ιm)))
  have hs : ∀ s, HasDerivAt (fun ε => T.cp h s * (Real.exp (ε * q1 s) *
      rx_g2 dS (Real.exp (ε * (ι1 s - ι))))) (T.cp h s * (κ * (ι1 s - ι))) 0 := by
    intro s
    have d2' : HasDerivAt (rx_g2 dS) κ (Real.exp (0 * (ι1 s - ι))) := by
      rw [zero_mul, Real.exp_zero]
      exact d2
    have := ((rx_hasDerivAt_exp1 (q1 s)).mul (d2'.comp 0 (rx_hasDerivAt_exp1 (ι1 s - ι)))).const_mul
      (T.cp h s)
    refine this.congr_deriv ?_
    simp only [zero_mul, Real.exp_zero, Function.comp_apply]
    have : rx_g2 dS 1 = 0 := e2
    rw [this]
    ring
  have hsum := (HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hs s).const_mul β
  refine ((hA.add hsum).sub_const 1).congr_deriv ?_
  have : rx_g1 Sf dS 1 = 1 := e1
  simp only [zero_mul, Real.exp_zero, Function.comp_apply, this, rx_Es]
  have hc : ∑ s, T.cp h s * (κ * (ι1 s - ι)) = κ * (∑ s, T.cp h s * ι1 s - ι) := by
    have : ∑ s, T.cp h s * (κ * (ι1 s - ι)) = κ * ∑ s, T.cp h s * ι1 s -
        κ * ι * ∑ s, T.cp h s := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, T.cp_sum]
    ring
  rw [hc]
  ring

/-- **Exercise 14.6**, (14.52): solving the linearised investment equation,
`îₜ = î_{t−1}/(1 + β) + βEₜî_{t+1}/(1 + β) + q̂ₜ/(κ(1 + β))`. -/
theorem ex_14_6_invest_52_solved {κ β q ι ιm Eι : ℝ} (hκ : κ ≠ 0) (hβ : 0 < β) :
    q - κ * (ι - ιm) + β * κ * (Eι - ι) = 0 ↔
      ι = ιm / (1 + β) + β / (1 + β) * Eι + q / (κ * (1 + β)) := by
  have h1 : (1 + β) ≠ 0 := by linarith
  constructor
  · intro h0
    field_simp
    linear_combination -h0
  · intro h0
    rw [h0]
    field_simp
    ring

/-- **Exercise 14.6**, (14.52), the Q equation (14.51) under risk neutrality,
`Qₜ = βEₜ[R_{k,t+1} + Q_{t+1}(1 − δ)]`: along `Qₜ = e^{εq̂}`, `R_k(s) = R̄e^{εr̂(s)}`,
`Q(s) = e^{εq̂(s)}` the derivative is `q̂ − βEₜ[R̄r̂ + (1 − δ)q̂′]`. -/
theorem ex_14_6_Q_52 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {δ β Rb q : ℝ}
    {r q1 : S → ℝ} :
    HasDerivAt (fun ε => Real.exp (ε * q) - β * ∑ s, T.cp h s * (Rb * Real.exp (ε * r s) +
        Real.exp (ε * q1 s) * (1 - δ)))
      (q - β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s)) 0 := by
  have hs : ∀ s, HasDerivAt (fun ε => T.cp h s * (Rb * Real.exp (ε * r s) +
      Real.exp (ε * q1 s) * (1 - δ))) (T.cp h s * (Rb * r s + (1 - δ) * q1 s)) 0 := by
    intro s
    have := ((rx_hasDerivAt_exp Rb (r s)).add ((rx_hasDerivAt_exp1 (q1 s)).mul_const
      (1 - δ))).const_mul (T.cp h s)
    exact this.congr_deriv (by ring)
  exact (rx_hasDerivAt_exp1 q).sub
    ((HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hs s).const_mul β)

/-- **Exercise 14.6**, (14.52), capital accumulation
`K_{t+1} = (1 − δ)Kₜ + (1 − S(Iₜ/I_{t−1}))Iₜ`: along `K_{t+1} = K̄e^{εk̂′}`, `Kₜ = K̄e^{εk̂}`,
`Iₜ = δK̄e^{εî}`, `Iₜ/I_{t−1} = e^{ε(î − î₋)}`, with `S(1) = S′(1) = 0`, the derivative is
`K̄(k̂′ − (1 − δ)k̂ − δî)`: `k̂_{t+1} = (1 − δ)k̂ₜ + δîₜ`. -/
theorem ex_14_6_capital_52 {Sf : ℝ → ℝ} {dS1 δ Kb k' k ι ιm : ℝ} (hS0 : Sf 1 = 0)
    (hdS0 : dS1 = 0) (hS : HasDerivAt Sf dS1 1) :
    HasDerivAt (fun ε => Kb * Real.exp (ε * k') - (1 - δ) * (Kb * Real.exp (ε * k))
        - (1 - Sf (Real.exp (ε * (ι - ιm)))) * (δ * Kb * Real.exp (ε * ι)))
      (Kb * (k' - (1 - δ) * k - δ * ι)) 0 := by
  have hS' : HasDerivAt Sf dS1 (Real.exp (0 * (ι - ιm))) := by simpa using hS
  have hc := hS'.comp 0 (rx_hasDerivAt_exp1 (ι - ιm))
  have h := ((rx_hasDerivAt_exp Kb k').sub ((rx_hasDerivAt_exp Kb k).const_mul (1 - δ))).sub
    (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hc).mul (rx_hasDerivAt_exp (δ * Kb) ι))
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, Function.comp_apply, zero_mul, Real.exp_zero, hS0, hdS0]
  ring

/-- **Exercise 14.6** (Miao, p. 508), "discuss the differences". (1) Under (14.43) the
linearised investment rate is pinned down by the current `q̂` alone: two solutions with the same
`q̂ₜ` and `k̂ₜ` have the same `îₜ`, whatever past investment was. (2) Under (14.52) current
investment puts the weight `1/(1 + β) ∈ (0, 1)` on lagged investment (inertia) and
`β/(1 + β)` on expected future investment, the weights summing to one. (3) The two `q̂`
equations differ by `βδEₜq̂_{t+1}`. -/
theorem ex_14_6_differences {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ κ β Rb : ℝ} {r q1 : S → ℝ} (hκ : κ ≠ 0) (hδ : δ ≠ 0) (hβ : 0 < β) :
    (∀ q ι ι' k : ℝ, q + κ * δ * (ι - k) = 0 → q + κ * δ * (ι' - k) = 0 → ι = ι') ∧
    (0 < 1 / (1 + β) ∧ 1 / (1 + β) < 1 ∧ 1 / (1 + β) + β / (1 + β) = 1) ∧
    β * rx_Es T h (fun s => Rb * r s + q1 s) -
      β * rx_Es T h (fun s => Rb * r s + (1 - δ) * q1 s) = β * δ * rx_Es T h q1 := by
  refine ⟨fun q ι ι' k h1 h2 => ?_, ⟨by positivity, ?_, ?_⟩, ?_⟩
  · have : κ * δ * (ι - ι') = 0 := by linarith
    have hkd : κ * δ ≠ 0 := mul_ne_zero hκ hδ
    have := (mul_eq_zero.1 this).resolve_left hkd
    linarith
  · rw [div_lt_one (by linarith)]
    linarith
  · field_simp
  · simp only [rx_Es, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring

end Miao.NeoclassicalGrowth

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §14.3.4 Stochastic trends

Miao, §14.3.4, pp. 501–503: the basic RBC model (log utility `ln C + χ ln(1 − N)`,
`Y = zK^α N^{1−α}`) with a unit-root technology shock `ln zₜ = μ_z + ln z_{t−1} + σεₜ`,
`z_{−1} = 1`.

* The random walk with drift: `ln zₜ = (t + 1)μ_z + σΣ_{j≤t} εⱼ` (`rx_lnz_walk`).
* Detrending: `X̃ₜ = Xₜ/zₜ^{1/(1−α)}` for `C, I, Y, w`, `K̃_{t+1} = K_{t+1}/zₜ^{1/(1−α)}`; with
  `zₜ = z_{t−1}e^{μ_z + σεₜ}` (`e = μ_z + σεₜ`), each equilibrium condition is equivalent to its
  detrended form displayed on p. 501: the Euler equation (`rx_detrend_euler`, on the event
  tree), labour supply (`rx_detrend_labour`), the resource constraint (`rx_detrend_resource`),
  output (`rx_detrend_output`), capital accumulation (`rx_detrend_capital`), the rental rate
  (`rx_detrend_rental`) and the wage (`rx_detrend_wage`). The key scaling identity is
  `zₜ^{1/(1−α)} = z_{t−1}^{1/(1−α)}e^{e/(1−α)}` (`rx_trend_scale`).
* Transforming back (p. 502): `ln xₜ = ln x̃ₜ + ln zₜ/(1 − α)`, and
  `ln xₜ − ln x̃_ss = (ln x̃ₜ − ln x̃_ss) + ln zₜ/(1 − α)` (`rx_detrend_back`).
* The steady state of the detrended system (`εₜ = 0`, `G = e^{μ_z/(1−α)}`,
  `rx_trend_exp_G`): the rental rate is `R = G/β − 1 + δ`, the capital–labour ratio solves
  `αG^{1−α}k^{α−1} = R`, `I/K = 1 − (1 − δ)/G`, and hours are `N = w/(w + χc)`; the steady
  state is unique (`rx_trend_steady_unique`) and exists, with `0 < N < 1` and positive
  consumption, when `R > 0` and `β ≤ 1` (`rx_trend_steady_exists`).
* Other sources of shocks (pp. 503–505): with investment-specific technology
  `K_{t+1} = (1 − δ)Kₜ + vₜIₜ`, `Qₜ = 1/vₜ` and `ΛₜQₜ = βEₜΛ_{t+1}[R_{k,t+1} + (1 − δ)Q_{t+1}]`
  (`rx_ist_foc`, an instance of `rx_dec1_euler` with `Φ(I, K) = vI`, `G(X, K) = X/v`); the
  capital price falls when `v` rises (`rx_ist_price`). With lump-sum government spending the
  steady-state capital–labour ratio does not depend on `Ḡ` (`rx_gov_kn`).
* Not formalised (computational/numerical): the calibration and the Dynare impulse responses
  (Figures 14.10–14.13) and the qualitative statements read off them.
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- Miao, p. 501: the random walk with drift `ln zₜ = μ_z + ln z_{t−1} + σεₜ`, `ln z_{−1} = 0`,
gives `ln zₜ = (t + 1)μ_z + σΣ_{j≤t} εⱼ`. -/
theorem rx_lnz_walk {μ σ : ℝ} {lz ε : ℕ → ℝ} (h0 : lz 0 = μ + 0 + σ * ε 0)
    (h : ∀ t, lz (t + 1) = μ + lz t + σ * ε (t + 1)) (t : ℕ) :
    lz t = (t + 1) * μ + σ * ∑ j ∈ Finset.range (t + 1), ε j := by
  induction t with
  | zero => simp [h0]
  | succ n ih =>
    rw [h n, ih, Finset.sum_range_succ _ (n + 1)]
    push_cast
    ring

/-- The scaling identity: if `zₜ = z_{t−1}e^{e}` with `z_{t−1} > 0`, then
`zₜ^{1/(1−α)} = z_{t−1}^{1/(1−α)}e^{e/(1−α)}`. -/
theorem rx_trend_scale {α zp e : ℝ} (hzp : 0 < zp) :
    (zp * Real.exp e) ^ (1 / (1 - α)) = zp ^ (1 / (1 - α)) * Real.exp (e / (1 - α)) := by
  rw [Real.mul_rpow hzp.le (Real.exp_pos e).le, ← Real.exp_mul]
  ring_nf

/-- Miao, p. 501, the detrended output equation. With `Ỹ = Y/zₜ^{1/(1−α)}`,
`K̃ = K/z_{t−1}^{1/(1−α)}` and `zₜ = z_{t−1}e^{e}`:
`Y = zₜKₜ^α Nₜ^{1−α}` iff `Ỹ = e^{αe/(α−1)}K̃^α Nₜ^{1−α}`. -/
theorem rx_detrend_output {α zp e Y K N : ℝ} (hα : α ≠ 1) (hzp : 0 < zp) (hK : 0 < K) :
    Y = zp * Real.exp e * K ^ α * N ^ (1 - α) ↔
      Y / (zp * Real.exp e) ^ (1 / (1 - α)) =
        Real.exp (α / (α - 1) * e) * (K / zp ^ (1 / (1 - α))) ^ α * N ^ (1 - α) := by
  have h1 : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hA : 0 < zp ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzp _
  have key : Real.exp (α / (α - 1) * e) * (K / zp ^ (1 / (1 - α))) ^ α *
      (zp * Real.exp e) ^ (1 / (1 - α)) = zp * Real.exp e * K ^ α := by
    rw [Real.rpow_def_of_pos (div_pos hK hA), Real.rpow_def_of_pos (mul_pos hzp (Real.exp_pos e)),
      Real.rpow_def_of_pos hK, Real.log_div hK.ne' hA.ne', Real.log_rpow hzp,
      Real.log_mul hzp.ne' (Real.exp_pos e).ne', Real.log_exp]
    conv_rhs => rw [← Real.exp_log hzp]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have : α - 1 ≠ 0 := sub_ne_zero.2 hα
    field_simp
    ring
  have hz : 0 < (zp * Real.exp e) ^ (1 / (1 - α)) :=
    Real.rpow_pos_of_pos (mul_pos hzp (Real.exp_pos e)) _
  rw [div_eq_iff hz.ne', ← key]
  constructor <;> intro h <;> rw [h] <;> ring

/-- Miao, p. 501, detrended capital accumulation. With `K̃_{t+1} = K_{t+1}/zₜ^{1/(1−α)}`,
`K̃ₜ = Kₜ/z_{t−1}^{1/(1−α)}`, `Ĩ = I/zₜ^{1/(1−α)}`, `zₜ = z_{t−1}e^{e}`:
`K_{t+1} = (1 − δ)Kₜ + Iₜ` iff `K̃_{t+1} = e^{e/(α−1)}(1 − δ)K̃ₜ + Ĩₜ`. -/
theorem rx_detrend_capital {α δ zp e K' K I : ℝ} (hα : α ≠ 1) (hzp : 0 < zp) :
    K' = (1 - δ) * K + I ↔
      K' / (zp * Real.exp e) ^ (1 / (1 - α)) =
        Real.exp (e / (α - 1)) * (1 - δ) * (K / zp ^ (1 / (1 - α))) +
          I / (zp * Real.exp e) ^ (1 / (1 - α)) := by
  rw [rx_trend_scale hzp]
  have hA : 0 < zp ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzp _
  have hB := Real.exp_pos (e / (1 - α))
  have hBB : Real.exp (e / (α - 1)) * Real.exp (e / (1 - α)) = 1 := by
    have : α - 1 ≠ 0 := sub_ne_zero.2 hα
    have : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
    rw [← Real.exp_add, show e / (α - 1) + e / (1 - α) = 0 by field_simp; ring, Real.exp_zero]
  have e1 : Real.exp (e / (α - 1)) * (1 - δ) * (K / zp ^ (1 / (1 - α))) =
      (1 - δ) * K / (zp ^ (1 / (1 - α)) * Real.exp (e / (1 - α))) := by
    field_simp
    linear_combination (1 - δ) * K * hBB
  rw [e1, ← add_div, div_left_inj' (mul_pos hA hB).ne']

/-- Miao, p. 501, the detrended rental rate: `R_k = αY/K` iff
`R_k = (αỸ/K̃)e^{e/(1−α)}`. -/
theorem rx_detrend_rental {α zp e R Y K : ℝ} (hzp : 0 < zp) :
    R = α * Y / K ↔
      R = α * (Y / (zp * Real.exp e) ^ (1 / (1 - α))) / (K / zp ^ (1 / (1 - α))) *
        Real.exp (e / (1 - α)) := by
  rw [rx_trend_scale hzp]
  have hA : 0 < zp ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzp _
  have hB := Real.exp_pos (e / (1 - α))
  have : α * (Y / (zp ^ (1 / (1 - α)) * Real.exp (e / (1 - α)))) / (K / zp ^ (1 / (1 - α))) *
      Real.exp (e / (1 - α)) = α * Y / K := by
    rcases eq_or_ne K 0 with hK | hK
    · simp [hK]
    · field_simp
  rw [this]

/-- Miao, p. 501, detrended labour supply: `χCₜ/(1 − Nₜ) = wₜ` iff `χC̃ₜ/(1 − Nₜ) = w̃ₜ`. -/
theorem rx_detrend_labour {χ C N w a : ℝ} (ha : 0 < a) :
    χ * C / (1 - N) = w ↔ χ * (C / a) / (1 - N) = w / a := by
  rw [show χ * (C / a) / (1 - N) = χ * C / (1 - N) / a by ring, div_left_inj' ha.ne']

/-- Miao, p. 501, the detrended resource constraint: `C + I = Y` iff `C̃ + Ĩ = Ỹ`. -/
theorem rx_detrend_resource {C I Y a : ℝ} (ha : 0 < a) : C + I = Y ↔ C / a + I / a = Y / a := by
  rw [← add_div, div_left_inj' ha.ne']

/-- Miao, p. 501, the detrended wage: if `w = (1 − α)Y/N` (the firm's condition) and
`Y = zₜKₜ^α Nₜ^{1−α}`, then `w̃ = (1 − α)e^{αe/(α−1)}K̃^α N^{−α}`. -/
theorem rx_detrend_wage {α zp e Y K N w : ℝ} (hα : α ≠ 1) (hzp : 0 < zp) (hK : 0 < K)
    (hN : 0 < N) (hw : w = (1 - α) * Y / N) (hY : Y = zp * Real.exp e * K ^ α * N ^ (1 - α)) :
    w / (zp * Real.exp e) ^ (1 / (1 - α)) =
      (1 - α) * Real.exp (α / (α - 1) * e) * (K / zp ^ (1 / (1 - α))) ^ α * N ^ (-α) := by
  have hYt := (rx_detrend_output hα hzp hK).1 hY
  rw [hw, show (1 - α) * Y / N / (zp * Real.exp e) ^ (1 / (1 - α)) =
    (1 - α) * (Y / (zp * Real.exp e) ^ (1 / (1 - α))) / N by ring, hYt,
    show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add_one hN.ne']
  field_simp

/-- Miao, p. 501, the detrended Euler equation, on the event tree. At the node `h` with TFP
`zₜ > 0`, successors with `z_{t+1}(s) = zₜe^{e(s)}`: `1/Cₜ = βEₜ[(R_{k,t+1} + 1 − δ)/C_{t+1}]`
iff `1/C̃ₜ = βEₜ[e^{e_{t+1}/(α−1)}(R_{k,t+1} + 1 − δ)/C̃_{t+1}]`, where
`C̃ₜ = Cₜ/zₜ^{1/(1−α)}`, `C̃_{t+1}(s) = C_{t+1}(s)/z_{t+1}(s)^{1/(1−α)}`. -/
theorem rx_detrend_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {α β δ zt Ct : ℝ} {C1 R1 e1 : S → ℝ} (hα : α ≠ 1) (hzt : 0 < zt) :
    1 / Ct = β * rx_Es T h (fun s => 1 / C1 s * (R1 s + 1 - δ)) ↔
      1 / (Ct / zt ^ (1 / (1 - α))) = β * rx_Es T h (fun s =>
        1 / (C1 s / (zt * Real.exp (e1 s)) ^ (1 / (1 - α))) * Real.exp (e1 s / (α - 1)) *
          (R1 s + 1 - δ)) := by
  have hA : 0 < zt ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hzt _
  have hs : ∀ s, 1 / (C1 s / (zt * Real.exp (e1 s)) ^ (1 / (1 - α))) *
      Real.exp (e1 s / (α - 1)) * (R1 s + 1 - δ) =
        zt ^ (1 / (1 - α)) * (1 / C1 s * (R1 s + 1 - δ)) := by
    intro s
    rw [rx_trend_scale hzt, one_div_div]
    have hBB : Real.exp (e1 s / (1 - α)) * Real.exp (e1 s / (α - 1)) = 1 := by
      have : α - 1 ≠ 0 := sub_ne_zero.2 hα
      have : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
      rw [← Real.exp_add, show e1 s / (1 - α) + e1 s / (α - 1) = 0 by field_simp; ring,
        Real.exp_zero]
    rw [div_eq_mul_one_div (zt ^ (1 / (1 - α)) * _)]
    linear_combination zt ^ (1 / (1 - α)) * (1 / C1 s) * (R1 s + 1 - δ) * hBB
  simp only [hs]
  rw [rx_Es_mul_left, one_div_div, div_eq_mul_one_div (zt ^ _), mul_left_comm β]
  constructor
  · intro h0
    rw [h0]
  · intro h0
    exact mul_left_cancel₀ hA.ne' h0

/-- Miao, p. 502, transforming back: `ln xₜ = ln x̃ₜ + ln zₜ/(1 − α)` for
`x̃ₜ = xₜ/zₜ^{1/(1−α)}`, and the impulse responses
`ln xₜ − ln x̃_ss = (ln x̃ₜ − ln x̃_ss) + ln zₜ/(1 − α)`. -/
theorem rx_detrend_back {α x z xss : ℝ} (hx : 0 < x) (hz : 0 < z) :
    Real.log x = Real.log (x / z ^ (1 / (1 - α))) + Real.log z / (1 - α) ∧
      Real.log x - Real.log xss = (Real.log (x / z ^ (1 / (1 - α))) - Real.log xss) +
        Real.log z / (1 - α) := by
  have h1 : Real.log x = Real.log (x / z ^ (1 / (1 - α))) + Real.log z / (1 - α) := by
    rw [Real.log_div hx.ne' (Real.rpow_pos_of_pos hz _).ne', Real.log_rpow hz]
    ring
  exact ⟨h1, by rw [h1]; ring⟩

/-- Miao, p. 501: at `εₜ = 0` the exponential factors of the detrended system are powers of
the steady-state gross growth rate `G = e^{μ_z/(1−α)}` of the trend:
`e^{αμ_z/(α−1)} = G^{−α}`, `e^{μ_z/(α−1)} = G⁻¹`. -/
theorem rx_trend_exp_G {α μ : ℝ} (hα : α ≠ 1) :
    Real.exp (α / (α - 1) * μ) = Real.exp (μ / (1 - α)) ^ (-α) ∧
      Real.exp (μ / (α - 1)) = (Real.exp (μ / (1 - α)))⁻¹ := by
  have : α - 1 ≠ 0 := sub_ne_zero.2 hα
  have : 1 - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  refine ⟨?_, ?_⟩
  · rw [← Real.exp_mul]
    congr 1
    field_simp
    ring
  · rw [← Real.exp_neg]
    congr 1
    field_simp
    ring

/-- The steady state of the detrended system of p. 501 at `εₜ = 0`, written with
`G = e^{μ_z/(1−α)}` (`rx_trend_exp_G`): Euler equation, labour supply, resource constraint,
output, capital accumulation, rental rate and wage. -/
def rx_trendSS (α β δ χ G C I Y K N Rk w : ℝ) : Prop :=
  1 = β / G * (Rk + 1 - δ) ∧ χ * C / (1 - N) = w ∧ C + I = Y ∧
    Y = G ^ (-α) * K ^ α * N ^ (1 - α) ∧ K = G⁻¹ * (1 - δ) * K + I ∧ Rk = α * Y / K * G ∧
    w = (1 - α) * G ^ (-α) * K ^ α * N ^ (-α)

/-- The steady-state rental rate `R = G/β − 1 + δ`. -/
noncomputable def rx_trR (β δ G : ℝ) : ℝ := G / β - 1 + δ

/-- The steady-state capital–labour ratio `k = (R/(αG^{1−α}))^{1/(α−1)}`. -/
noncomputable def rx_trk (α β δ G : ℝ) : ℝ := (rx_trR β δ G / (α * G ^ (1 - α))) ^ (α - 1)⁻¹

/-- Output per hour `y = G^{−α}k^α`. -/
noncomputable def rx_try (α β δ G : ℝ) : ℝ := G ^ (-α) * rx_trk α β δ G ^ α

/-- Investment per hour `i = (1 − (1 − δ)/G)k`. -/
noncomputable def rx_tri (α β δ G : ℝ) : ℝ := (1 - (1 - δ) / G) * rx_trk α β δ G

/-- Consumption per hour `c = y − i`. -/
noncomputable def rx_trc (α β δ G : ℝ) : ℝ := rx_try α β δ G - rx_tri α β δ G

/-- Hours `N = w/(w + χc)` with `w = (1 − α)y`. -/
noncomputable def rx_trN (α β δ χ G : ℝ) : ℝ :=
  (1 - α) * rx_try α β δ G / ((1 - α) * rx_try α β δ G + χ * rx_trc α β δ G)

theorem rx_rpow_kN {α k N : ℝ} (hk : 0 < k) (hN : 0 < N) :
    (k * N) ^ α * N ^ (1 - α) = k ^ α * N ∧ (k * N) ^ α * N ^ (-α) = k ^ α := by
  rw [Real.mul_rpow hk.le hN.le]
  constructor
  · rw [mul_assoc, ← Real.rpow_add hN, show α + (1 - α) = 1 by ring, Real.rpow_one]
  · rw [mul_assoc, ← Real.rpow_add hN, show α + -α = 0 by ring, Real.rpow_zero, mul_one]

/-- `k^{α−1} = R/(αG^{1−α})` for the closed-form `k`, when `R > 0`. -/
theorem rx_trk_pow {α β δ G : ℝ} (hα : α ≠ 1) (hα0 : 0 < α) (hG : 0 < G)
    (hR : 0 < rx_trR β δ G) :
    0 < rx_trk α β δ G ∧ rx_trk α β δ G ^ (α - 1) = rx_trR β δ G / (α * G ^ (1 - α)) := by
  have hc : 0 < rx_trR β δ G / (α * G ^ (1 - α)) :=
    div_pos hR (mul_pos hα0 (Real.rpow_pos_of_pos hG _))
  exact ⟨Real.rpow_pos_of_pos hc _, Real.rpow_inv_rpow hc.le (sub_ne_zero.2 hα)⟩

/-- Miao, p. 501: uniqueness of the steady state of the detrended system. Any steady state
with `K > 0`, `0 < N < 1` has the rental rate `R = G/β − 1 + δ`, the capital–labour ratio
`K/N = k`, investment `I = (1 − (1 − δ)/G)K` and hours `N = w/(w + χc)` of `rx_trN`. -/
theorem rx_trend_steady_unique {α β δ χ G C I Y K N Rk w : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : 0 < β) (hG : 0 < G) (hK : 0 < K) (hN : 0 < N) (hN1 : N < 1)
    (hss : rx_trendSS α β δ χ G C I Y K N Rk w) :
    Rk = rx_trR β δ G ∧ K / N = rx_trk α β δ G ∧ I = (1 - (1 - δ) / G) * K ∧
      N = rx_trN α β δ χ G := by
  obtain ⟨hE, hL, hRes, hY, hKa, hRk, hw⟩ := hss
  have hα : α ≠ 1 := ne_of_lt hα1
  have hR : Rk = rx_trR β δ G := by
    unfold rx_trR
    field_simp at hE ⊢
    linarith
  have hk : 0 < K / N := div_pos hK hN
  have hKkN : K = K / N * N := by field_simp
  obtain ⟨e1, e2⟩ := rx_rpow_kN (α := α) hk hN
  rw [← hKkN] at e1 e2
  have hYk : Y = N * (G ^ (-α) * (K / N) ^ α) := by rw [hY, mul_assoc, e1]; ring
  have hwk : w = (1 - α) * (G ^ (-α) * (K / N) ^ α) := by rw [hw, mul_assoc, e2]; ring
  have hpow : (K / N) ^ (α - 1) = rx_trR β δ G / (α * G ^ (1 - α)) := by
    rw [← hR, hRk, hYk, Real.rpow_sub_one hk.ne', show (1 : ℝ) - α = -α + 1 by ring,
      Real.rpow_add_one hG.ne']
    have : 0 < G ^ (-α) := Real.rpow_pos_of_pos hG _
    field_simp
  have hkeq : K / N = rx_trk α β δ G := by
    unfold rx_trk
    rw [← hpow, Real.rpow_rpow_inv hk.le (sub_ne_zero.2 hα)]
  have hI : I = (1 - (1 - δ) / G) * K := by
    field_simp
    field_simp at hKa
    linarith
  refine ⟨hR, hkeq, hI, ?_⟩
  have hC : C = N * rx_trc α β δ G := by
    have : C = Y - I := by linarith
    have hKN : K = N * rx_trk α β δ G := by rw [← hkeq]; field_simp
    rw [this, hYk, hI, hkeq, hKN]
    unfold rx_trc rx_try rx_tri
    ring
  have hwe : w = (1 - α) * rx_try α β δ G := by rw [hwk, hkeq]; rfl
  have hlab : χ * C = w * (1 - N) := by
    have : 1 - N ≠ 0 := by linarith
    field_simp at hL
    linarith
  have hy : 0 < rx_try α β δ G := by
    unfold rx_try
    rw [← hkeq]
    exact mul_pos (Real.rpow_pos_of_pos hG _) (Real.rpow_pos_of_pos hk _)
  have hsum : N * ((1 - α) * rx_try α β δ G + χ * rx_trc α β δ G) =
      (1 - α) * rx_try α β δ G := by
    rw [hC, hwe] at hlab
    linarith
  have hpos : 0 < (1 - α) * rx_try α β δ G := mul_pos (by linarith) hy
  have hden : (1 - α) * rx_try α β δ G + χ * rx_trc α β δ G ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsum
    linarith
  unfold rx_trN
  field_simp
  linarith

/-- Miao, p. 501: existence of the steady state of the detrended system. If `0 < α < 1`,
`0 < β ≤ 1`, `χ > 0`, `G > 0` and `R = G/β − 1 + δ > 0`, then consumption per hour
`c = y − i` is positive, hours `N = w/(w + χc)` lie in `(0, 1)`, and
`(C, I, Y, K) = (cN, iN, yN, kN)`, `R_k = R`, `w = (1 − α)y` is a steady state. -/
theorem rx_trend_steady_exists {α β δ χ G : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hχ : 0 < χ) (hG : 0 < G) (hR : 0 < rx_trR β δ G) :
    0 < rx_trc α β δ G ∧ 0 < rx_trN α β δ χ G ∧ rx_trN α β δ χ G < 1 ∧
      rx_trendSS α β δ χ G (rx_trc α β δ G * rx_trN α β δ χ G)
        (rx_tri α β δ G * rx_trN α β δ χ G) (rx_try α β δ G * rx_trN α β δ χ G)
        (rx_trk α β δ G * rx_trN α β δ χ G) (rx_trN α β δ χ G) (rx_trR β δ G)
        ((1 - α) * rx_try α β δ G) := by
  have hα : α ≠ 1 := ne_of_lt hα1
  obtain ⟨hk, hkp⟩ := rx_trk_pow hα hα0 hG hR
  have hGa : 0 < G ^ (-α) := Real.rpow_pos_of_pos hG _
  have hy : 0 < rx_try α β δ G := mul_pos hGa (Real.rpow_pos_of_pos hk _)
  have hyk : rx_try α β δ G = rx_trR β δ G / (α * G) * rx_trk α β δ G := by
    unfold rx_try
    have e : rx_trk α β δ G ^ α = rx_trk α β δ G ^ (α - 1) * rx_trk α β δ G := by
      rw [Real.rpow_sub_one hk.ne']
      field_simp
    rw [e, hkp, show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add_one hG.ne']
    field_simp
  have hRD : α * (G - 1 + δ) < rx_trR β δ G := by
    have hGb : G ≤ G / β := by rw [le_div_iff₀ hβ]; nlinarith
    unfold rx_trR at hR ⊢
    rcases le_or_gt (G - 1 + δ) 0 with hD | hD
    · nlinarith
    · nlinarith
  have hc : 0 < rx_trc α β δ G := by
    have e : rx_trc α β δ G = rx_trk α β δ G * ((rx_trR β δ G - α * (G - 1 + δ)) / (α * G)) := by
      unfold rx_trc rx_tri
      rw [hyk]
      field_simp
      ring
    rw [e]
    exact mul_pos hk (div_pos (by linarith) (mul_pos hα0 hG))
  have hw : 0 < (1 - α) * rx_try α β δ G := mul_pos (by linarith) hy
  have hden : 0 < (1 - α) * rx_try α β δ G + χ * rx_trc α β δ G := by positivity
  have hN : 0 < rx_trN α β δ χ G := div_pos hw hden
  have hN1 : rx_trN α β δ χ G < 1 := by
    unfold rx_trN
    rw [div_lt_one hden]
    nlinarith [mul_pos hχ hc]
  have hNd : rx_trN α β δ χ G * ((1 - α) * rx_try α β δ G + χ * rx_trc α β δ G) =
      (1 - α) * rx_try α β δ G := by
    unfold rx_trN
    field_simp
  obtain ⟨e1, e2⟩ := rx_rpow_kN (α := α) hk hN
  refine ⟨hc, hN, hN1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rx_trR
    field_simp
    ring
  · have : 1 - rx_trN α β δ χ G ≠ 0 := by linarith
    field_simp
    linarith
  · unfold rx_trc
    ring
  · rw [mul_assoc, e1]
    unfold rx_try
    ring
  · unfold rx_tri
    field_simp
    ring
  · rw [hyk]
    field_simp
  · rw [mul_assoc, e2]
    unfold rx_try
    ring

/-- Investment-specific technology `Φ(I, K) = vI` (Miao, p. 503) has partial derivatives
`Φ_I = v`, `Φ_K = 0`; its inverse `G(X, K) = X/v` (for `v ≠ 0`) has `G_X = 1/v`, `G_K = 0`.
(A concrete instance of the hypotheses of `rx_uzawa_euler` and `rx_inverse_partials`.) -/
theorem rx_linear_partials {v : ℝ} (hv : v ≠ 0) (p : ℝ × ℝ) :
    rx_HasPartials (fun q : ℝ × ℝ => v * q.1) v 0 p ∧
      rx_HasPartials (fun q : ℝ × ℝ => q.1 / v) (1 / v) 0 p ∧
      ∀ X K : ℝ, (fun q : ℝ × ℝ => v * q.1) ((fun q : ℝ × ℝ => q.1 / v) (X, K), K) = X := by
  refine ⟨?_, ?_, fun X K => by simp only; field_simp⟩
  · unfold rx_HasPartials
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul v
    refine this.congr_fderiv ?_
    ext <;> simp
  · unfold rx_HasPartials
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul_const (1 / v)
    refine (this.congr_fderiv ?_).congr_of_eventuallyEq
      (Eventually.of_forall fun q => div_eq_mul_one_div q.1 v)
    ext <;> simp

/-- Miao, p. 503, investment-specific shocks, decentralisation 1: with
`K_{t+1} = (1 − δ)Kₜ + vₜIₜ` the `Iₜ` condition is `Qₜvₜ = 1`, i.e. `Qₜ = 1/vₜ`
(`rx_invest_foc`), and perturbing `K_{t+1} = k` (financed by `Iₜ = (k − (1 − δ)Kₜ)/vₜ`, with
`I_{t+1}(s) = (K_{t+2}(s) − (1 − δ)k)/v(s)`) gives
`ΛₜQₜ = βEₜΛ_{t+1}[R_{k,t+1} + (1 − δ)Q_{t+1}]`. -/
theorem rx_ist_foc {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ β Kt K1 yt vt l0 : ℝ} {R wN K2 v l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (yt - (K1 - (1 - δ) * Kt) / vt))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (R s * K1 + wN s - (K2 s - (1 - δ) * K1) / v s))
    (hmax : IsLocalMax (fun k => U0 (yt - (k - (1 - δ) * Kt) / vt) + β * ∑ s,
      T.cp h s * U1 s (R s * k + wN s - (K2 s - (1 - δ) * k) / v s)) K1) :
    l0 * (1 / vt) = β * rx_Es T h (fun s => l1 s * (R s + (1 - δ) * (1 / v s))) := by
  have hc0 : HasDerivAt (fun k => yt - (k - (1 - δ) * Kt) / vt) (0 - (1 - 0) / vt) K1 :=
    (hasDerivAt_const K1 yt).sub (((hasDerivAt_id' K1).sub (hasDerivAt_const K1 _)).div_const vt)
  have hc1 : ∀ s, HasDerivAt (fun k => R s * k + wN s - (K2 s - (1 - δ) * k) / v s)
      (R s * 1 + 0 - (0 - (1 - δ) * 1) / v s) K1 := fun s =>
    ((((hasDerivAt_id' K1).const_mul (R s)).add (hasDerivAt_const K1 _)).sub
      (((hasDerivAt_const K1 _).sub ((hasDerivAt_id' K1).const_mul _)).div_const (v s)))
  have e := rx_node_foc (c0 := fun k => yt - (k - (1 - δ) * Kt) / vt)
    (c1 := fun s k => R s * k + wN s - (K2 s - (1 - δ) * k) / v s) hU0 hc0 hU1 hc1 hmax
  have hs : ∀ s, T.cp h s * (l1 s * (R s * 1 + 0 - (0 - (1 - δ) * 1) / v s)) =
      T.cp h s * (l1 s * (R s + (1 - δ) * (1 / v s))) := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => hs s] at e
  simp only [rx_Es]
  linarith

/-- Miao, p. 503: "the capital price is equal to `1/vₜ`"; a positive investment-specific
technology shock lowers it: `0 < v < v′ ⇒ 1/v′ < 1/v`. -/
theorem rx_ist_price {v v' : ℝ} (hv : 0 < v) (hvv : v < v') : 1 / v' < 1 / v :=
  one_div_lt_one_div_of_lt hv hvv

/-- Miao, p. 505, government spending financed by lump-sum taxes: the resource constraint
`C + I + G = zK^α N^{1−α}` does not enter the steady-state Euler equation
`1 = β(R_k + 1 − δ)` or the rental rate `R_k = α(K/N)^{α−1}` (with `z = 1`), so the
steady-state capital–labour ratio `((1/β − 1 + δ)/α)^{1/(α−1)}` does not depend on `Ḡ`. -/
theorem rx_gov_kn {α β δ Rk k : ℝ} (hα : α ≠ 1) (hβ : 0 < β) (hα0 : 0 < α) (hk : 0 < k)
    (hE : 1 = β * (Rk + 1 - δ)) (hR : Rk = α * k ^ (α - 1)) :
    k = ((1 / β - 1 + δ) / α) ^ (α - 1)⁻¹ := by
  have : (1 / β - 1 + δ) / α = k ^ (α - 1) := by
    rw [div_eq_iff hα0.ne', mul_comm, ← hR]
    field_simp
    linarith
  rw [this, Real.rpow_rpow_inv hk.le (sub_ne_zero.2 hα)]

end Miao.NeoclassicalGrowth

set_option linter.style.longLine false
#print axioms Miao.NeoclassicalGrowth.IsSolution
#print axioms Miao.NeoclassicalGrowth.IsRegular
#print axioms Miao.NeoclassicalGrowth.EventuallyConst
#print axioms Miao.NeoclassicalGrowth.IsStableSeq
#print axioms Miao.NeoclassicalGrowth.IsSteadyStateOf
#print axioms Miao.NeoclassicalGrowth.IsAsympStable
#print axioms Miao.NeoclassicalGrowth.basin
#print axioms Miao.NeoclassicalGrowth.IsGloballyStable
#print axioms Miao.NeoclassicalGrowth.IsStableMatrix
#print axioms Miao.NeoclassicalGrowth.isGloballyStable_iff_basin
#print axioms Miao.NeoclassicalGrowth.isAsympStable_iff_basin
#print axioms Miao.NeoclassicalGrowth.isStableSeq_iff_bddAbove
#print axioms Miao.NeoclassicalGrowth.tendsto_zero_of_le_rec
#print axioms Miao.NeoclassicalGrowth.tendsto_zero_of_rec
#print axioms Miao.NeoclassicalGrowth.triangular_step
#print axioms Miao.NeoclassicalGrowth.triangular_invariant
#print axioms Miao.NeoclassicalGrowth.triangular_tendsto_iff
#print axioms Miao.NeoclassicalGrowth.mclm
#print axioms Miao.NeoclassicalGrowth.mclm_apply
#print axioms Miao.NeoclassicalGrowth.norm_mulVec_le
#print axioms Miao.NeoclassicalGrowth.norm_mclm_mul_le
#print axioms Miao.NeoclassicalGrowth.tendsto_norm_mclm_pow
#print axioms Miao.NeoclassicalGrowth.summable_of_tendsto_zero
#print axioms Miao.NeoclassicalGrowth.diag_mul_of_upper
#print axioms Miao.NeoclassicalGrowth.upper_inv
#print axioms Miao.NeoclassicalGrowth.diag_inv_of_upper
#print axioms Miao.NeoclassicalGrowth.summable_norm_pow_of_triangular
#print axioms Miao.NeoclassicalGrowth.stableSubspace
#print axioms Miao.NeoclassicalGrowth.unstableSubspace
#print axioms Miao.NeoclassicalGrowth.convSubspace
#print axioms Miao.NeoclassicalGrowth.mem_convSubspace
#print axioms Miao.NeoclassicalGrowth.tendsto_of_mem_maxGenEigenspace
#print axioms Miao.NeoclassicalGrowth.not_tendsto_of_eigen
#print axioms Miao.NeoclassicalGrowth.stable_le_conv
#print axioms Miao.NeoclassicalGrowth.stable_sup_unstable
#print axioms Miao.NeoclassicalGrowth.disjoint_stable_unstable
#print axioms Miao.NeoclassicalGrowth.unstable_invariant
#print axioms Miao.NeoclassicalGrowth.tendsto_iff_mem_stable
#print axioms Miao.NeoclassicalGrowth.stable_eq_top
#print axioms Miao.NeoclassicalGrowth.cplx
#print axioms Miao.NeoclassicalGrowth.cplx_sub
#print axioms Miao.NeoclassicalGrowth.cplx_add
#print axioms Miao.NeoclassicalGrowth.tendsto_cplx_iff
#print axioms Miao.NeoclassicalGrowth.cplxEnd
#print axioms Miao.NeoclassicalGrowth.cplxEnd_pow_cplx
#print axioms Miao.NeoclassicalGrowth.hasEigenvalue_cplxEnd_iff
#print axioms Miao.NeoclassicalGrowth.finrank_biSup_maxGenEigenspace
#print axioms Miao.NeoclassicalGrowth.finrank_stableSubspace
#print axioms Miao.NeoclassicalGrowth.conjV
#print axioms Miao.NeoclassicalGrowth.conjV_conjV
#print axioms Miao.NeoclassicalGrowth.conjV_add
#print axioms Miao.NeoclassicalGrowth.conjV_sub
#print axioms Miao.NeoclassicalGrowth.conjV_smul
#print axioms Miao.NeoclassicalGrowth.conjV_zero
#print axioms Miao.NeoclassicalGrowth.conjV_cplx
#print axioms Miao.NeoclassicalGrowth.eq_cplx_re
#print axioms Miao.NeoclassicalGrowth.cplxEnd_conjV
#print axioms Miao.NeoclassicalGrowth.pow_sub_conjV
#print axioms Miao.NeoclassicalGrowth.conjV_mem_maxGenEigenspace
#print axioms Miao.NeoclassicalGrowth.conjV_mem_biSup
#print axioms Miao.NeoclassicalGrowth.conjV_mem_stable
#print axioms Miao.NeoclassicalGrowth.conjV_mem_unstable
#print axioms Miao.NeoclassicalGrowth.cplxL
#print axioms Miao.NeoclassicalGrowth.stableR
#print axioms Miao.NeoclassicalGrowth.unstableR
#print axioms Miao.NeoclassicalGrowth.mem_stableR
#print axioms Miao.NeoclassicalGrowth.mem_unstableR
#print axioms Miao.NeoclassicalGrowth.mem_stableR_iff
#print axioms Miao.NeoclassicalGrowth.cplx_mulVec
#print axioms Miao.NeoclassicalGrowth.stableR_invariant
#print axioms Miao.NeoclassicalGrowth.unstableR_invariant
#print axioms Miao.NeoclassicalGrowth.isCompl_stableR_unstableR
#print axioms Miao.NeoclassicalGrowth.linearIndependent_cplx
#print axioms Miao.NeoclassicalGrowth.finrank_le_of_cplx
#print axioms Miao.NeoclassicalGrowth.finrank_stableR
#print axioms Miao.NeoclassicalGrowth.unstableR_ker
#print axioms Miao.NeoclassicalGrowth.uniform_bound_of_basis
#print axioms Miao.NeoclassicalGrowth.exists_bound_of_tendsto
#print axioms Miao.NeoclassicalGrowth.mem_maxGen_smul
#print axioms Miao.NeoclassicalGrowth.projS
#print axioms Miao.NeoclassicalGrowth.projU
#print axioms Miao.NeoclassicalGrowth.projS_add_projU
#print axioms Miao.NeoclassicalGrowth.projS_mem
#print axioms Miao.NeoclassicalGrowth.projU_mem
#print axioms Miao.NeoclassicalGrowth.projS_of_mem
#print axioms Miao.NeoclassicalGrowth.projS_of_mem_unstable
#print axioms Miao.NeoclassicalGrowth.projU_of_mem
#print axioms Miao.NeoclassicalGrowth.projU_of_mem_stable
#print axioms Miao.NeoclassicalGrowth.projS_mulVec
#print axioms Miao.NeoclassicalGrowth.projU_mulVec
#print axioms Miao.NeoclassicalGrowth.pow_mulVec_mem_stableR
#print axioms Miao.NeoclassicalGrowth.tendsto_scaled_of_stable
#print axioms Miao.NeoclassicalGrowth.scaled_pow_cplx
#print axioms Miao.NeoclassicalGrowth.stable_bound
#print axioms Miao.NeoclassicalGrowth.isStableMatrix_iff_roots
#print axioms Miao.NeoclassicalGrowth.tendsto_of_isStableMatrix
#print axioms Miao.NeoclassicalGrowth.isStableMatrix_of_tendsto
#print axioms Miao.NeoclassicalGrowth.isStableMatrix_iff_tendsto
#print axioms Miao.NeoclassicalGrowth.HasGeomDecay
#print axioms Miao.NeoclassicalGrowth.hasGeomDecay_of_isStableMatrix
#print axioms Miao.NeoclassicalGrowth.isStableMatrix_inv
#print axioms Miao.NeoclassicalGrowth.footnote_2
#print axioms Miao.NeoclassicalGrowth.isRegular_of_isUnit_det
#print axioms Miao.NeoclassicalGrowth.example_scalar_not_regular
#print axioms Miao.NeoclassicalGrowth.example_scalar_no_solution
#print axioms Miao.NeoclassicalGrowth.remark_nonregular_no_solution
#print axioms Miao.NeoclassicalGrowth.remark_nonregular_counterexample
#print axioms Miao.NeoclassicalGrowth.eq_1_21
#print axioms Miao.NeoclassicalGrowth.eq_1_21_solution
#print axioms Miao.NeoclassicalGrowth.eq_1_21_steadyState
#print axioms Miao.NeoclassicalGrowth.isSteadyStateOf_of_not_mem_range
#print axioms Miao.NeoclassicalGrowth.isStableSeq_iff_exists_le
#print axioms Miao.NeoclassicalGrowth.exists_mulVec_bound
#print axioms Miao.NeoclassicalGrowth.bounded_mulVec
#print axioms Miao.NeoclassicalGrowth.norm_sum_type_le
#print axioms Miao.NeoclassicalGrowth.norm_comp_inl_le
#print axioms Miao.NeoclassicalGrowth.norm_comp_inr_le
#print axioms Miao.NeoclassicalGrowth.backward_sol_eq
#print axioms Miao.NeoclassicalGrowth.bounded_backward
#print axioms Miao.NeoclassicalGrowth.summable_geom_series
#print axioms Miao.NeoclassicalGrowth.mulVec_tsum_rs
#print axioms Miao.NeoclassicalGrowth.tsum_geom_series_succ
#print axioms Miao.NeoclassicalGrowth.eq_zero_of_bounded_orbit
#print axioms Miao.NeoclassicalGrowth.IsRealBlockSplit
#print axioms Miao.NeoclassicalGrowth.blockDiag_mulVec_inl
#print axioms Miao.NeoclassicalGrowth.blockDiag_mulVec_inr
#print axioms Miao.NeoclassicalGrowth.mulVec_comp_inl
#print axioms Miao.NeoclassicalGrowth.mulVec_comp_inr
#print axioms Miao.NeoclassicalGrowth.IsRealBlockSplit.mul_R
#print axioms Miao.NeoclassicalGrowth.card_add_card_of_inv
#print axioms Miao.NeoclassicalGrowth.IsRealBlockSplit.isUnit_one_sub
#print axioms Miao.NeoclassicalGrowth.eigen_transport
#print axioms Miao.NeoclassicalGrowth.exists_real_block_split
#print axioms Miao.NeoclassicalGrowth.eq_1_22
#print axioms Miao.NeoclassicalGrowth.exists_sol_rec
#print axioms Miao.NeoclassicalGrowth.sol_rec_unique
#print axioms Miao.NeoclassicalGrowth.exists_unique_solution
#print axioms Miao.NeoclassicalGrowth.eq_1_24
#print axioms Miao.NeoclassicalGrowth.eq_1_25
#print axioms Miao.NeoclassicalGrowth.isUnit_sub_det
#print axioms Miao.NeoclassicalGrowth.xbar_eq
#print axioms Miao.NeoclassicalGrowth.theorem_1_4_1
#print axioms Miao.NeoclassicalGrowth.forwardU
#print axioms Miao.NeoclassicalGrowth.forwardU_rec
#print axioms Miao.NeoclassicalGrowth.forwardU_bounded
#print axioms Miao.NeoclassicalGrowth.forwardU_unique
#print axioms Miao.NeoclassicalGrowth.split_rec_inl
#print axioms Miao.NeoclassicalGrowth.split_rec_inr
#print axioms Miao.NeoclassicalGrowth.bounded_of_split
#print axioms Miao.NeoclassicalGrowth.eq_1_29
#print axioms Miao.NeoclassicalGrowth.eq_1_30
#print axioms Miao.NeoclassicalGrowth.eq_1_31
#print axioms Miao.NeoclassicalGrowth.eq_1_32
#print axioms Miao.NeoclassicalGrowth.bk_exists
#print axioms Miao.NeoclassicalGrowth.bk_unique
#print axioms Miao.NeoclassicalGrowth.theorem_1_4_2
#print axioms Miao.NeoclassicalGrowth.blocks_of_inv
#print axioms Miao.NeoclassicalGrowth.rks_inv
#print axioms Miao.NeoclassicalGrowth.puy_inv_of_rks
#print axioms Miao.NeoclassicalGrowth.bk_order_iff
#print axioms Miao.NeoclassicalGrowth.eq_1_33
#print axioms Miao.NeoclassicalGrowth.corollary_1_4_1
#print axioms Miao.NeoclassicalGrowth.eq_1_34
#print axioms Miao.NeoclassicalGrowth.stable_initial_iff
#print axioms Miao.NeoclassicalGrowth.stableArm
#print axioms Miao.NeoclassicalGrowth.mem_stableArm
#print axioms Miao.NeoclassicalGrowth.stableArm_iff
#print axioms Miao.NeoclassicalGrowth.finrank_stableArm
#print axioms Miao.NeoclassicalGrowth.stable_initial_translate
#print axioms Miao.NeoclassicalGrowth.remark_unit_root
#print axioms Miao.NeoclassicalGrowth.CondExpSystem
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.mk
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.E
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.norm_le
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.tower_le
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.tower_ge
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.tower_le_apply
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.tower_ge_apply
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.idem
#print axioms Miao.NeoclassicalGrowth.CondExpSystem.norm_apply_le
#print axioms Miao.NeoclassicalGrowth.IsAdaptedV
#print axioms Miao.NeoclassicalGrowth.IsStableProc
#print axioms Miao.NeoclassicalGrowth.matAct
#print axioms Miao.NeoclassicalGrowth.Evec
#print axioms Miao.NeoclassicalGrowth.IsRESolution
#print axioms Miao.NeoclassicalGrowth.IsPredeterminedBK
#print axioms Miao.NeoclassicalGrowth.Evec_matAct
#print axioms Miao.NeoclassicalGrowth.matAct_add
#print axioms Miao.NeoclassicalGrowth.matAct_mul
#print axioms Miao.NeoclassicalGrowth.matAct_one
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_sub
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_neg
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_zero
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_zero_left
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_smul
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_sum
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_add_left
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_sub_left
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_pow_succ
#print axioms Miao.NeoclassicalGrowth.bkS_matCLM
#print axioms Miao.NeoclassicalGrowth.bkS_matCLM_apply
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_hasSum
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_real
#print axioms Miao.NeoclassicalGrowth.bkS_norm_matAct_le
#print axioms Miao.NeoclassicalGrowth.bkS_matAct_bound
#print axioms Miao.NeoclassicalGrowth.bkS_geom_decay
#print axioms Miao.NeoclassicalGrowth.bkS_ECLM
#print axioms Miao.NeoclassicalGrowth.bkS_ECLM_apply
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_hasSum
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_add
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_sub
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_neg
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_zero
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_smul
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_sumElim
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_tower_le
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_tower_ge
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_idem
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_of_le
#print axioms Miao.NeoclassicalGrowth.bkS_norm_Evec_le
#print axioms Miao.NeoclassicalGrowth.bkS_isAdaptedV_iff
#print axioms Miao.NeoclassicalGrowth.bkS_isStableProc_iff
#print axioms Miao.NeoclassicalGrowth.bkS_stable_Evec
#print axioms Miao.NeoclassicalGrowth.bkS_stable_shift
#print axioms Miao.NeoclassicalGrowth.bkS_stable_matAct
#print axioms Miao.NeoclassicalGrowth.bkS_stable_add
#print axioms Miao.NeoclassicalGrowth.bkS_summable_geom
#print axioms Miao.NeoclassicalGrowth.bkS_fwd
#print axioms Miao.NeoclassicalGrowth.eq_2_12
#print axioms Miao.NeoclassicalGrowth.bkS_fwd_adapted
#print axioms Miao.NeoclassicalGrowth.bkS_fwd_bound
#print axioms Miao.NeoclassicalGrowth.bkS_fwd_rec
#print axioms Miao.NeoclassicalGrowth.bkS_fwd_unique
#print axioms Miao.NeoclassicalGrowth.bkS_jump_unique
#print axioms Miao.NeoclassicalGrowth.eq_2_11_iff
#print axioms Miao.NeoclassicalGrowth.bkS_regular_of_det
#print axioms Miao.NeoclassicalGrowth.bkS_add_comp
#print axioms Miao.NeoclassicalGrowth.bkS_sub_comp
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_comp
#print axioms Miao.NeoclassicalGrowth.bkS_comp_inl
#print axioms Miao.NeoclassicalGrowth.bkS_comp_inr
#print axioms Miao.NeoclassicalGrowth.bkS_blockDiag_inl
#print axioms Miao.NeoclassicalGrowth.bkS_blockDiag_inr
#print axioms Miao.NeoclassicalGrowth.bkS_split_inl
#print axioms Miao.NeoclassicalGrowth.bkS_split_inr
#print axioms Miao.NeoclassicalGrowth.bkS_norm_comp_inl_le
#print axioms Miao.NeoclassicalGrowth.bkS_norm_comp_inr_le
#print axioms Miao.NeoclassicalGrowth.bkS_norm_sum_type_le
#print axioms Miao.NeoclassicalGrowth.bkS_sumElim_eta
#print axioms Miao.NeoclassicalGrowth.bkS_backward_eq
#print axioms Miao.NeoclassicalGrowth.bkS_bounded_backward
#print axioms Miao.NeoclassicalGrowth.bkS_IsStableSol
#print axioms Miao.NeoclassicalGrowth.bkS_u_rec
#print axioms Miao.NeoclassicalGrowth.bkS_u_eq_fwd
#print axioms Miao.NeoclassicalGrowth.bkS_policy
#print axioms Miao.NeoclassicalGrowth.bkS_unique
#print axioms Miao.NeoclassicalGrowth.bkS_exists
#print axioms Miao.NeoclassicalGrowth.theorem_1_4_2_stoch
#print axioms Miao.NeoclassicalGrowth.bkS_k0_adapted
#print axioms Miao.NeoclassicalGrowth.bkS_trivial
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_trivial
#print axioms Miao.NeoclassicalGrowth.certainty_equivalence
#print axioms Miao.NeoclassicalGrowth.certainty_equivalence_fwd
#print axioms Miao.NeoclassicalGrowth.theorem_1_4_2_of_stoch
#print axioms Miao.NeoclassicalGrowth.bkS_Evec_ar
#print axioms Miao.NeoclassicalGrowth.certainty_equivalence_ar
#print axioms Miao.NeoclassicalGrowth.certainty_equivalence_ar_det
#print axioms Miao.NeoclassicalGrowth.bkS_fwd_zero
#print axioms Miao.NeoclassicalGrowth.bkS_homog_u_zero
#print axioms Miao.NeoclassicalGrowth.theorem_1_4_3_gt_stoch
#print axioms Miao.NeoclassicalGrowth.theorem_1_4_3_lt_stoch
#print axioms Miao.NeoclassicalGrowth.theorem_1_4_3_lt_exists_stoch
#print axioms Miao.NeoclassicalGrowth.bkS_shift
#print axioms Miao.NeoclassicalGrowth.corollary_1_4_1_stoch
#print axioms Miao.NeoclassicalGrowth.nkA
#print axioms Miao.NeoclassicalGrowth.nkB
#print axioms Miao.NeoclassicalGrowth.nkC
#print axioms Miao.NeoclassicalGrowth.nkAinv
#print axioms Miao.NeoclassicalGrowth.nkSaddleW
#print axioms Miao.NeoclassicalGrowth.nkW
#print axioms Miao.NeoclassicalGrowth.nkG
#print axioms Miao.NeoclassicalGrowth.nkState
#print axioms Miao.NeoclassicalGrowth.nkShock
#print axioms Miao.NeoclassicalGrowth.nk_sumElim_eq_iff
#print axioms Miao.NeoclassicalGrowth.nk_matAct_A
#print axioms Miao.NeoclassicalGrowth.nk_matAct_B
#print axioms Miao.NeoclassicalGrowth.nk_matAct_C
#print axioms Miao.NeoclassicalGrowth.eq_2_16
#print axioms Miao.NeoclassicalGrowth.nkA_mul_inv
#print axioms Miao.NeoclassicalGrowth.eq_2_16_W
#print axioms Miao.NeoclassicalGrowth.nkSaddleP
#print axioms Miao.NeoclassicalGrowth.nkSaddleR
#print axioms Miao.NeoclassicalGrowth.nk_tri_stable
#print axioms Miao.NeoclassicalGrowth.nk_scalar_eig
#print axioms Miao.NeoclassicalGrowth.nk_saddle_split
#print axioms Miao.NeoclassicalGrowth.nk_saddle_eig
#print axioms Miao.NeoclassicalGrowth.nk_saddle_eig_l1
#print axioms Miao.NeoclassicalGrowth.nk_saddle_unstable
#print axioms Miao.NeoclassicalGrowth.nkTr
#print axioms Miao.NeoclassicalGrowth.nkLam1
#print axioms Miao.NeoclassicalGrowth.nkLam2
#print axioms Miao.NeoclassicalGrowth.nk_lam
#print axioms Miao.NeoclassicalGrowth.example_2_3_1_split
#print axioms Miao.NeoclassicalGrowth.example_2_3_1_eigen
#print axioms Miao.NeoclassicalGrowth.example_2_3_1_indeterminate
#print axioms Miao.NeoclassicalGrowth.example_2_3_1_indeterminate_det
#print axioms Miao.NeoclassicalGrowth.nkBothOut
#print axioms Miao.NeoclassicalGrowth.nk_eig2
#print axioms Miao.NeoclassicalGrowth.nk_out_of_bothOut
#print axioms Miao.NeoclassicalGrowth.nk_root_of_not_bothOut
#print axioms Miao.NeoclassicalGrowth.nk_eigvec2
#print axioms Miao.NeoclassicalGrowth.nk_jump2_unique
#print axioms Miao.NeoclassicalGrowth.nk_jump2_nonunique
#print axioms Miao.NeoclassicalGrowth.nkWT
#print axioms Miao.NeoclassicalGrowth.nkTaylorEqm
#print axioms Miao.NeoclassicalGrowth.nkDeterminate
#print axioms Miao.NeoclassicalGrowth.nk_taylor_iff
#print axioms Miao.NeoclassicalGrowth.nk_bothOut_WT
#print axioms Miao.NeoclassicalGrowth.nk_WT_trace
#print axioms Miao.NeoclassicalGrowth.ex_2_2_suff
#print axioms Miao.NeoclassicalGrowth.ex_2_2_nec
#print axioms Miao.NeoclassicalGrowth.ex_2_2_b_exact
#print axioms Miao.NeoclassicalGrowth.ex_2_2_b
#print axioms Miao.NeoclassicalGrowth.ex_2_2_a
#print axioms Miao.NeoclassicalGrowth.ex_2_2_a_taylor_principle
#print axioms Miao.NeoclassicalGrowth.ex_2_2_a_printed_false
#print axioms Miao.NeoclassicalGrowth.IsScalarSol
#print axioms Miao.NeoclassicalGrowth.BddSeq
#print axioms Miao.NeoclassicalGrowth.bddSeq_iff_isStableSeq
#print axioms Miao.NeoclassicalGrowth.bddSeq_of_tendsto
#print axioms Miao.NeoclassicalGrowth.BddSeq.exists_nonneg
#print axioms Miao.NeoclassicalGrowth.geom_eq
#print axioms Miao.NeoclassicalGrowth.abs_pow_mul_tendsto_atTop
#print axioms Miao.NeoclassicalGrowth.pow_mul_tendsto_zero_iff
#print axioms Miao.NeoclassicalGrowth.geom_bdd_iff
#print axioms Miao.NeoclassicalGrowth.pow_mul_tendsto_zero_of_bdd
#print axioms Miao.NeoclassicalGrowth.bddSeq_of_forced
#print axioms Miao.NeoclassicalGrowth.tendsto_zero_of_forced
#print axioms Miao.NeoclassicalGrowth.eq_1_2_steady_state
#print axioms Miao.NeoclassicalGrowth.eq_1_2_no_steady_state_of_b_one
#print axioms Miao.NeoclassicalGrowth.eq_1_3
#print axioms Miao.NeoclassicalGrowth.eq_1_3_globallyStable
#print axioms Miao.NeoclassicalGrowth.eq_1_3_tendsto
#print axioms Miao.NeoclassicalGrowth.eq_1_3_diverges
#print axioms Miao.NeoclassicalGrowth.eq_1_3_bdd_iff
#print axioms Miao.NeoclassicalGrowth.eq_1_4
#print axioms Miao.NeoclassicalGrowth.not_tendsto_neg_one_pow
#print axioms Miao.NeoclassicalGrowth.eq_1_5_counterexample
#print axioms Miao.NeoclassicalGrowth.eq_1_5_tendsto
#print axioms Miao.NeoclassicalGrowth.eq_1_5_bdd
#print axioms Miao.NeoclassicalGrowth.eq_1_5_sub_tendsto
#print axioms Miao.NeoclassicalGrowth.eq_1_5_b_one_formula
#print axioms Miao.NeoclassicalGrowth.eq_1_5_b_one_tendsto_iff
#print axioms Miao.NeoclassicalGrowth.eq_1_5_b_one_limit_sub
#print axioms Miao.NeoclassicalGrowth.eq_1_5_b_neg_one_counterexample
#print axioms Miao.NeoclassicalGrowth.eq_1_5_b_neg_one_unique
#print axioms Miao.NeoclassicalGrowth.eq_1_6
#print axioms Miao.NeoclassicalGrowth.fwdSol
#print axioms Miao.NeoclassicalGrowth.abs_one_div_lt_one
#print axioms Miao.NeoclassicalGrowth.eq_1_8_summable
#print axioms Miao.NeoclassicalGrowth.eq_1_8_isScalarSol
#print axioms Miao.NeoclassicalGrowth.eq_1_8_bdd
#print axioms Miao.NeoclassicalGrowth.eq_1_7_of_bdd
#print axioms Miao.NeoclassicalGrowth.eq_1_8_transversality
#print axioms Miao.NeoclassicalGrowth.eq_1_8_unique_of_transversality
#print axioms Miao.NeoclassicalGrowth.eq_1_8_unique_bdd
#print axioms Miao.NeoclassicalGrowth.eq_1_8
#print axioms Miao.NeoclassicalGrowth.eq_1_9
#print axioms Miao.NeoclassicalGrowth.eq_1_9_every_solution
#print axioms Miao.NeoclassicalGrowth.eq_1_8_others_diverge
#print axioms Miao.NeoclassicalGrowth.eq_1_8_not_summable
#print axioms Miao.NeoclassicalGrowth.eq_1_9_bubble_stable
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_recursion
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_backward
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_tendsto_iff
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_abs_a_lt_one_iff
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_forward
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_forward_limit
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_isScalarSol
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_bubbles
#print axioms Miao.NeoclassicalGrowth.example_1_1_1_unique_bdd
#print axioms Miao.NeoclassicalGrowth.divTax
#print axioms Miao.NeoclassicalGrowth.taxPath
#print axioms Miao.NeoclassicalGrowth.sum_div_pow_eq
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_p0_forward
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_pT
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_p0
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_solves
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_const
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_unique
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_drop
#print axioms Miao.NeoclassicalGrowth.example_1_1_2_decreasing
#print axioms Miao.NeoclassicalGrowth.IsSol22
#print axioms Miao.NeoclassicalGrowth.cp22
#print axioms Miao.NeoclassicalGrowth.disc22
#print axioms Miao.NeoclassicalGrowth.lamLo
#print axioms Miao.NeoclassicalGrowth.lamHi
#print axioms Miao.NeoclassicalGrowth.sVar
#print axioms Miao.NeoclassicalGrowth.disc22_pos
#print axioms Miao.NeoclassicalGrowth.cp22_factor
#print axioms Miao.NeoclassicalGrowth.cp22_lamLo
#print axioms Miao.NeoclassicalGrowth.cp22_lamHi
#print axioms Miao.NeoclassicalGrowth.lamLo_lt_lamHi
#print axioms Miao.NeoclassicalGrowth.roots22_lt
#print axioms Miao.NeoclassicalGrowth.lamLo_gt_neg_one_iff
#print axioms Miao.NeoclassicalGrowth.abs_lamLo_lt_one_iff
#print axioms Miao.NeoclassicalGrowth.lamLo_lt_m11
#print axioms Miao.NeoclassicalGrowth.sVar_step
#print axioms Miao.NeoclassicalGrowth.sVar_succ
#print axioms Miao.NeoclassicalGrowth.recover22
#print axioms Miao.NeoclassicalGrowth.IsSol22.ext
#print axioms Miao.NeoclassicalGrowth.bddSeq_lin
#print axioms Miao.NeoclassicalGrowth.sHi_zero_of_bdd
#print axioms Miao.NeoclassicalGrowth.kSaddle
#print axioms Miao.NeoclassicalGrowth.sHi_zero_iff
#print axioms Miao.NeoclassicalGrowth.saddle22
#print axioms Miao.NeoclassicalGrowth.saddle22_tendsto
#print axioms Miao.NeoclassicalGrowth.saddle22_unique
#print axioms Miao.NeoclassicalGrowth.saddle22_unbounded
#print axioms Miao.NeoclassicalGrowth.sVar_tendsto
#print axioms Miao.NeoclassicalGrowth.saddle22_iff
#print axioms Miao.NeoclassicalGrowth.saddle22_only_zero
#print axioms Miao.NeoclassicalGrowth.IsPhaseSol
#print axioms Miao.NeoclassicalGrowth.phaseIter
#print axioms Miao.NeoclassicalGrowth.phaseIter_sol
#print axioms Miao.NeoclassicalGrowth.phase_tilde
#print axioms Miao.NeoclassicalGrowth.phase_delta
#print axioms Miao.NeoclassicalGrowth.phase_isocline_x
#print axioms Miao.NeoclassicalGrowth.phase_isocline_y
#print axioms Miao.NeoclassicalGrowth.phase_steady_state
#print axioms Miao.NeoclassicalGrowth.bddSeq_sub_const
#print axioms Miao.NeoclassicalGrowth.phase_dev
#print axioms Miao.NeoclassicalGrowth.phase_cp_one
#print axioms Miao.NeoclassicalGrowth.phase_cp_neg_one
#print axioms Miao.NeoclassicalGrowth.phase_roots
#print axioms Miao.NeoclassicalGrowth.phase_lamLo_iff
#print axioms Miao.NeoclassicalGrowth.phase_saddle
#print axioms Miao.NeoclassicalGrowth.phase_saddle_slope
#print axioms Miao.NeoclassicalGrowth.phase_saddle_iff
#print axioms Miao.NeoclassicalGrowth.phase_counterexample
#print axioms Miao.NeoclassicalGrowth.example_1_6_1_steady
#print axioms Miao.NeoclassicalGrowth.example_1_6_1_linearization
#print axioms Miao.NeoclassicalGrowth.vec2_eq_iff
#print axioms Miao.NeoclassicalGrowth.mulVec22
#print axioms Miao.NeoclassicalGrowth.example_1_6_1_matrix
#print axioms Miao.NeoclassicalGrowth.example_1_6_1_reduced
#print axioms Miao.NeoclassicalGrowth.example_1_6_1_trace_det
#print axioms Miao.NeoclassicalGrowth.example_1_6_1_roots
#print axioms Miao.NeoclassicalGrowth.example_1_6_1_saddle
#print axioms Miao.NeoclassicalGrowth.definition_1_6_1
#print axioms Miao.NeoclassicalGrowth.definition_1_6_1_cycle
#print axioms Miao.NeoclassicalGrowth.logistic
#print axioms Miao.NeoclassicalGrowth.logistic_two
#print axioms Miao.NeoclassicalGrowth.logistic_fixed_iff
#print axioms Miao.NeoclassicalGrowth.logistic_two_fixed_iff
#print axioms Miao.NeoclassicalGrowth.logistic_two_cycle
#print axioms Miao.NeoclassicalGrowth.logistic_two_cycle_decimals
#print axioms Miao.NeoclassicalGrowth.rm_euler_homogeneous
#print axioms Miao.NeoclassicalGrowth.rm_zero_profit
#print axioms Miao.NeoclassicalGrowth.rm_partial1_homog_zero
#print axioms Miao.NeoclassicalGrowth.rm_partial2_homog_zero
#print axioms Miao.NeoclassicalGrowth.rmKprU
#print axioms Miao.NeoclassicalGrowth.rmKprUc
#print axioms Miao.NeoclassicalGrowth.rmKprUn
#print axioms Miao.NeoclassicalGrowth.rm_kpr_hasDerivAt_c
#print axioms Miao.NeoclassicalGrowth.rm_kpr_hasDerivAt_n
#print axioms Miao.NeoclassicalGrowth.rm_kpr_uc_scale
#print axioms Miao.NeoclassicalGrowth.rm_kpr_un_scale
#print axioms Miao.NeoclassicalGrowth.rm_kpr_mrs_scale
#print axioms Miao.NeoclassicalGrowth.rm_log_hasDerivAt_c
#print axioms Miao.NeoclassicalGrowth.rm_log_uc_scale
#print axioms Miao.NeoclassicalGrowth.rm_log_mrs_scale
#print axioms Miao.NeoclassicalGrowth.rm_inada_u_misprint
#print axioms Miao.NeoclassicalGrowth.rm_inada_F_misprint
#print axioms Miao.NeoclassicalGrowth.rm_log_inada
#print axioms Miao.NeoclassicalGrowth.rm_cd_inada_zero
#print axioms Miao.NeoclassicalGrowth.rm_cd_inada_top
#print axioms Miao.NeoclassicalGrowth.rm_planner_resource
#print axioms Miao.NeoclassicalGrowth.rmPlanC
#print axioms Miao.NeoclassicalGrowth.rmPlanGain
#print axioms Miao.NeoclassicalGrowth.RMPlanFeasible
#print axioms Miao.NeoclassicalGrowth.RMPlanNFI
#print axioms Miao.NeoclassicalGrowth.rm_planner_nfi_of_optimal
#print axioms Miao.NeoclassicalGrowth.rm_clm_apply
#print axioms Miao.NeoclassicalGrowth.rm_planC_update_k_ne
#print axioms Miao.NeoclassicalGrowth.rm_planC_update_k_t
#print axioms Miao.NeoclassicalGrowth.rm_planC_update_k_succ
#print axioms Miao.NeoclassicalGrowth.rm_planner_euler
#print axioms Miao.NeoclassicalGrowth.rm_planner_intratemporal
#print axioms Miao.NeoclassicalGrowth.rm_planner_intratemporal_misprint
#print axioms Miao.NeoclassicalGrowth.RMHHFOC
#print axioms Miao.NeoclassicalGrowth.RMADFOC
#print axioms Miao.NeoclassicalGrowth.rm_ad_euler
#print axioms Miao.NeoclassicalGrowth.rm_ad_of_hh
#print axioms Miao.NeoclassicalGrowth.rm_ad_tvc_iff
#print axioms Miao.NeoclassicalGrowth.RMFirmFOC
#print axioms Miao.NeoclassicalGrowth.eq_14_3
#print axioms Miao.NeoclassicalGrowth.RMClear
#print axioms Miao.NeoclassicalGrowth.rm_clear_percapita
#print axioms Miao.NeoclassicalGrowth.RMPlannerFOC
#print axioms Miao.NeoclassicalGrowth.rm_ce_planner
#print axioms Miao.NeoclassicalGrowth.rm_planner_ce
#print axioms Miao.NeoclassicalGrowth.RMDetrendedFOC
#print axioms Miao.NeoclassicalGrowth.rm_detrend_planner
#print axioms Miao.NeoclassicalGrowth.rm_detrend_prices
#print axioms Miao.NeoclassicalGrowth.rm_detrend_euler_misprint
#print axioms Miao.NeoclassicalGrowth.eq_14_11
#print axioms Miao.NeoclassicalGrowth.rm_value_partial
#print axioms Miao.NeoclassicalGrowth.eq_14_12
#print axioms Miao.NeoclassicalGrowth.eq_14_13
#print axioms Miao.NeoclassicalGrowth.rmKernel
#print axioms Miao.NeoclassicalGrowth.rm_kernel_zero
#print axioms Miao.NeoclassicalGrowth.rm_kernel_mul
#print axioms Miao.NeoclassicalGrowth.rm_firm_capital_foc
#print axioms Miao.NeoclassicalGrowth.eq_14_14_iff_eq_14_7
#print axioms Miao.NeoclassicalGrowth.rm_stock_return
#print axioms Miao.NeoclassicalGrowth.rm_rce_sequential
#print axioms Miao.NeoclassicalGrowth.rm_steady_state_iff
#print axioms Miao.NeoclassicalGrowth.rm_FK_ratio
#print axioms Miao.NeoclassicalGrowth.rm_mgr_pos
#print axioms Miao.NeoclassicalGrowth.rm_steady_ratio_exists_unique
#print axioms Miao.NeoclassicalGrowth.rm_steady_ratio_anti
#print axioms Miao.NeoclassicalGrowth.rm_cs_beta
#print axioms Miao.NeoclassicalGrowth.rm_cs_delta
#print axioms Miao.NeoclassicalGrowth.rm_cs_ga
#print axioms Miao.NeoclassicalGrowth.rm_cs_sigma
#print axioms Miao.NeoclassicalGrowth.rm_balanced_growth
#print axioms Miao.NeoclassicalGrowth.rmCD
#print axioms Miao.NeoclassicalGrowth.rmCDK
#print axioms Miao.NeoclassicalGrowth.rmCDN
#print axioms Miao.NeoclassicalGrowth.rm_cd_FK_hasDerivAt
#print axioms Miao.NeoclassicalGrowth.rm_cd_FN_hasDerivAt
#print axioms Miao.NeoclassicalGrowth.rm_cd_homog
#print axioms Miao.NeoclassicalGrowth.rm_cd_FK_strictAnti
#print axioms Miao.NeoclassicalGrowth.rm_cd_chi_pos
#print axioms Miao.NeoclassicalGrowth.rm_cd_log_steady
#print axioms Miao.NeoclassicalGrowth.rm_phase_c
#print axioms Miao.NeoclassicalGrowth.rm_phase_k
#print axioms Miao.NeoclassicalGrowth.rm_lin_taylor
#print axioms Miao.NeoclassicalGrowth.rm_lin_reduced
#print axioms Miao.NeoclassicalGrowth.rm_lin_trace_det
#print axioms Miao.NeoclassicalGrowth.rm_lin_roots
#print axioms Miao.NeoclassicalGrowth.rm_lin_saddle
#print axioms Miao.NeoclassicalGrowth.rm_lin_saddle_monotone
#print axioms Miao.NeoclassicalGrowth.RMTaxes
#print axioms Miao.NeoclassicalGrowth.RMTaxes.mk
#print axioms Miao.NeoclassicalGrowth.RMTaxes.τs
#print axioms Miao.NeoclassicalGrowth.RMTaxes.τd
#print axioms Miao.NeoclassicalGrowth.RMTaxes.τn
#print axioms Miao.NeoclassicalGrowth.RMTaxes.τc
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.mk
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.C
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.N
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.K
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.I
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.G
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.w
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.R
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.lam
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.V
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.D
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.Q
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.B
#print axioms Miao.NeoclassicalGrowth.RMFiscalPath.T
#print axioms Miao.NeoclassicalGrowth.rmGovBudget
#print axioms Miao.NeoclassicalGrowth.RMFiscalEq
#print axioms Miao.NeoclassicalGrowth.rm_fiscal_euler
#print axioms Miao.NeoclassicalGrowth.rm_fiscal_labour
#print axioms Miao.NeoclassicalGrowth.rm_fiscal_value_recursion
#print axioms Miao.NeoclassicalGrowth.eq_14_20
#print axioms Miao.NeoclassicalGrowth.rm_prop_14_1_1_step
#print axioms Miao.NeoclassicalGrowth.rm_prop_14_1_1_misprint
#print axioms Miao.NeoclassicalGrowth.rm_prop_14_1_1_sum
#print axioms Miao.NeoclassicalGrowth.rm_prop_14_1_1_exdiv
#print axioms Miao.NeoclassicalGrowth.proposition_14_1_1
#print axioms Miao.NeoclassicalGrowth.eq_14_21
#print axioms Miao.NeoclassicalGrowth.rm_temporary_distribution_tax
#print axioms Miao.NeoclassicalGrowth.rm_temporary_distribution_tax_distorts
#print axioms Miao.NeoclassicalGrowth.rm_distribution_tax_neutral
#print axioms Miao.NeoclassicalGrowth.rm_walras
#print axioms Miao.NeoclassicalGrowth.rm_gov_budget_misprint
#print axioms Miao.NeoclassicalGrowth.rm_ricardian
#print axioms Miao.NeoclassicalGrowth.RMFiscalAlloc
#print axioms Miao.NeoclassicalGrowth.ex_14_1_firm
#print axioms Miao.NeoclassicalGrowth.RMHKPath
#print axioms Miao.NeoclassicalGrowth.RMHKPath.mk
#print axioms Miao.NeoclassicalGrowth.RMHKPath.C
#print axioms Miao.NeoclassicalGrowth.RMHKPath.N
#print axioms Miao.NeoclassicalGrowth.RMHKPath.K
#print axioms Miao.NeoclassicalGrowth.RMHKPath.I
#print axioms Miao.NeoclassicalGrowth.RMHKPath.G
#print axioms Miao.NeoclassicalGrowth.RMHKPath.w
#print axioms Miao.NeoclassicalGrowth.RMHKPath.Rk
#print axioms Miao.NeoclassicalGrowth.RMHKPath.R
#print axioms Miao.NeoclassicalGrowth.RMHKPath.lam
#print axioms Miao.NeoclassicalGrowth.RMHKPath.B
#print axioms Miao.NeoclassicalGrowth.RMHKPath.T
#print axioms Miao.NeoclassicalGrowth.RMHKEq
#print axioms Miao.NeoclassicalGrowth.ex_14_1_hk
#print axioms Miao.NeoclassicalGrowth.RMADPath
#print axioms Miao.NeoclassicalGrowth.RMADPath.mk
#print axioms Miao.NeoclassicalGrowth.RMADPath.C
#print axioms Miao.NeoclassicalGrowth.RMADPath.N
#print axioms Miao.NeoclassicalGrowth.RMADPath.K
#print axioms Miao.NeoclassicalGrowth.RMADPath.I
#print axioms Miao.NeoclassicalGrowth.RMADPath.G
#print axioms Miao.NeoclassicalGrowth.RMADPath.w
#print axioms Miao.NeoclassicalGrowth.RMADPath.Rk
#print axioms Miao.NeoclassicalGrowth.RMADPath.q
#print axioms Miao.NeoclassicalGrowth.RMADPath.lam0
#print axioms Miao.NeoclassicalGrowth.RMADPath.T
#print axioms Miao.NeoclassicalGrowth.RMADEq
#print axioms Miao.NeoclassicalGrowth.ex_14_1_ad
#print axioms Miao.NeoclassicalGrowth.ex_14_1
#print axioms Miao.NeoclassicalGrowth.rmConstPath
#print axioms Miao.NeoclassicalGrowth.ex_14_2
#print axioms Miao.NeoclassicalGrowth.rm_fiscal_eq_example
#print axioms Miao.NeoclassicalGrowth.ex_14_2_mgr
#print axioms Miao.NeoclassicalGrowth.ex_14_2_value
#print axioms Miao.NeoclassicalGrowth.ex_14_2_corporate_tax
#print axioms Miao.NeoclassicalGrowth.ex_14_2_cd
#print axioms Miao.NeoclassicalGrowth.rb_Y
#print axioms Miao.NeoclassicalGrowth.rb_MPK
#print axioms Miao.NeoclassicalGrowth.rb_MPL
#print axioms Miao.NeoclassicalGrowth.rb_rpow_sub_one'
#print axioms Miao.NeoclassicalGrowth.rb_rpow_neg'
#print axioms Miao.NeoclassicalGrowth.rb_MPK_eq
#print axioms Miao.NeoclassicalGrowth.rb_MPL_eq
#print axioms Miao.NeoclassicalGrowth.rb_euler_thm
#print axioms Miao.NeoclassicalGrowth.rb_Y_pos
#print axioms Miao.NeoclassicalGrowth.rb_MPK_pos
#print axioms Miao.NeoclassicalGrowth.rb_MPL_pos
#print axioms Miao.NeoclassicalGrowth.rb_cd_tangent
#print axioms Miao.NeoclassicalGrowth.rb_cd_tangent'
#print axioms Miao.NeoclassicalGrowth.rb_profit
#print axioms Miao.NeoclassicalGrowth.rb_firm_optimal
#print axioms Miao.NeoclassicalGrowth.rb_hasDerivAt_Y_K
#print axioms Miao.NeoclassicalGrowth.rb_hasDerivAt_Y_N
#print axioms Miao.NeoclassicalGrowth.rb_firm_foc
#print axioms Miao.NeoclassicalGrowth.rb_u
#print axioms Miao.NeoclassicalGrowth.rb_log_tangent
#print axioms Miao.NeoclassicalGrowth.rb_u_tangent
#print axioms Miao.NeoclassicalGrowth.rb_static
#print axioms Miao.NeoclassicalGrowth.eq_14_27
#print axioms Miao.NeoclassicalGrowth.rb_labour_suff
#print axioms Miao.NeoclassicalGrowth.rb_hasDerivAt_static
#print axioms Miao.NeoclassicalGrowth.rb_labour_nec
#print axioms Miao.NeoclassicalGrowth.rb_node
#print axioms Miao.NeoclassicalGrowth.eq_14_26_node
#print axioms Miao.NeoclassicalGrowth.rb_euler_node_suff
#print axioms Miao.NeoclassicalGrowth.rb_euler_node_nec
#print axioms Miao.NeoclassicalGrowth.rb_lnz
#print axioms Miao.NeoclassicalGrowth.eq_14_25_iter
#print axioms Miao.NeoclassicalGrowth.rb_solow_residual
#print axioms Miao.NeoclassicalGrowth.rb_telescope
#print axioms Miao.NeoclassicalGrowth.rb_integral_euler
#print axioms Miao.NeoclassicalGrowth.rb_suff_core
#print axioms Miao.NeoclassicalGrowth.rb_IsFeasible
#print axioms Miao.NeoclassicalGrowth.rb_A
#print axioms Miao.NeoclassicalGrowth.eq_14_26
#print axioms Miao.NeoclassicalGrowth.rb_TVC
#print axioms Miao.NeoclassicalGrowth.rb_value
#print axioms Miao.NeoclassicalGrowth.rb_planner_pointwise
#print axioms Miao.NeoclassicalGrowth.rb_planner_suff
#print axioms Miao.NeoclassicalGrowth.rb_planner_optimal
#print axioms Miao.NeoclassicalGrowth.rb_bmN
#print axioms Miao.NeoclassicalGrowth.rb_bmK
#print axioms Miao.NeoclassicalGrowth.rb_bmC
#print axioms Miao.NeoclassicalGrowth.rb_bmN_mem
#print axioms Miao.NeoclassicalGrowth.rb_bmK_pos
#print axioms Miao.NeoclassicalGrowth.rb_bm_solution
#print axioms Miao.NeoclassicalGrowth.rb_IsHHFeasible
#print axioms Miao.NeoclassicalGrowth.rb_HHEuler
#print axioms Miao.NeoclassicalGrowth.rb_household_pointwise
#print axioms Miao.NeoclassicalGrowth.rb_household_suff
#print axioms Miao.NeoclassicalGrowth.rb_household_optimal
#print axioms Miao.NeoclassicalGrowth.rb_IsSCE
#print axioms Miao.NeoclassicalGrowth.rb_sce_iff
#print axioms Miao.NeoclassicalGrowth.rb_sce_optimal
#print axioms Miao.NeoclassicalGrowth.rb_bm_sce
#print axioms Miao.NeoclassicalGrowth.rb_rk
#print axioms Miao.NeoclassicalGrowth.rb_kn
#print axioms Miao.NeoclassicalGrowth.rb_sc
#print axioms Miao.NeoclassicalGrowth.rb_rk_pos
#print axioms Miao.NeoclassicalGrowth.rb_sc_pos
#print axioms Miao.NeoclassicalGrowth.rb_sc_lt_one
#print axioms Miao.NeoclassicalGrowth.rb_kn_pos
#print axioms Miao.NeoclassicalGrowth.rb_kn_pow
#print axioms Miao.NeoclassicalGrowth.rb_MPK_ratio
#print axioms Miao.NeoclassicalGrowth.rb_MPL_ratio
#print axioms Miao.NeoclassicalGrowth.rb_Y_ratio
#print axioms Miao.NeoclassicalGrowth.rb_MPK_kn
#print axioms Miao.NeoclassicalGrowth.rb_ss_euler
#print axioms Miao.NeoclassicalGrowth.rb_ss_KN
#print axioms Miao.NeoclassicalGrowth.rb_ss_prices
#print axioms Miao.NeoclassicalGrowth.rb_ss_IY_levels
#print axioms Miao.NeoclassicalGrowth.rb_ss_ratios
#print axioms Miao.NeoclassicalGrowth.eq_14_28
#print axioms Miao.NeoclassicalGrowth.rb_ss_chi
#print axioms Miao.NeoclassicalGrowth.rb_ssN
#print axioms Miao.NeoclassicalGrowth.rb_ss_N_iff
#print axioms Miao.NeoclassicalGrowth.rb_ss_N_mem
#print axioms Miao.NeoclassicalGrowth.rb_ss_chi_strictAnti
#print axioms Miao.NeoclassicalGrowth.rb_ss_exists_unique
#print axioms Miao.NeoclassicalGrowth.rb_calib_chi
#print axioms Miao.NeoclassicalGrowth.rb_calib_chi_ne
#print axioms Miao.NeoclassicalGrowth.rb_ss_permanent
#print axioms Miao.NeoclassicalGrowth.rb_zeta
#print axioms Miao.NeoclassicalGrowth.rb_p
#print axioms Miao.NeoclassicalGrowth.rb_g
#print axioms Miao.NeoclassicalGrowth.rb_q
#print axioms Miao.NeoclassicalGrowth.rb_a
#print axioms Miao.NeoclassicalGrowth.rb_b
#print axioms Miao.NeoclassicalGrowth.rb_c
#print axioms Miao.NeoclassicalGrowth.rb_hasDerivAt_exp_mul
#print axioms Miao.NeoclassicalGrowth.rb_Y_exp
#print axioms Miao.NeoclassicalGrowth.rb_MPK_exp
#print axioms Miao.NeoclassicalGrowth.rb_MPL_exp
#print axioms Miao.NeoclassicalGrowth.rb_hasDerivAt_log_one_sub
#print axioms Miao.NeoclassicalGrowth.eq_14_27_loglin
#print axioms Miao.NeoclassicalGrowth.eq_14_31
#print axioms Miao.NeoclassicalGrowth.rb_resource_loglin
#print axioms Miao.NeoclassicalGrowth.rb_resource_solved
#print axioms Miao.NeoclassicalGrowth.eq_14_32
#print axioms Miao.NeoclassicalGrowth.rb_euler_loglin
#print axioms Miao.NeoclassicalGrowth.rb_euler_loglin_eq
#print axioms Miao.NeoclassicalGrowth.eq_14_33_det
#print axioms Miao.NeoclassicalGrowth.eq_14_33
#print axioms Miao.NeoclassicalGrowth.eq_14_36_loglin
#print axioms Miao.NeoclassicalGrowth.eq_14_37
#print axioms Miao.NeoclassicalGrowth.rb_labour_market
#print axioms Miao.NeoclassicalGrowth.rb_labour_slopes
#print axioms Miao.NeoclassicalGrowth.rb_output_loglin
#print axioms Miao.NeoclassicalGrowth.rb_rental_loglin
#print axioms Miao.NeoclassicalGrowth.rb_investment_loglin
#print axioms Miao.NeoclassicalGrowth.rb_stock_return_loglin
#print axioms Miao.NeoclassicalGrowth.rb_stock_return_printed_false
#print axioms Miao.NeoclassicalGrowth.rb_riskfree_loglin
#print axioms Miao.NeoclassicalGrowth.rb_riskfree_eq
#print axioms Miao.NeoclassicalGrowth.rb_riskfree_E
#print axioms Miao.NeoclassicalGrowth.rb_coeff_pos
#print axioms Miao.NeoclassicalGrowth.rb_b_eq
#print axioms Miao.NeoclassicalGrowth.rb_c_eq
#print axioms Miao.NeoclassicalGrowth.eq_14_34_K
#print axioms Miao.NeoclassicalGrowth.eq_14_34_C
#print axioms Miao.NeoclassicalGrowth.eq_14_34_printed_false
#print axioms Miao.NeoclassicalGrowth.rb_isocline_C
#print axioms Miao.NeoclassicalGrowth.rb_isocline_C_sign
#print axioms Miao.NeoclassicalGrowth.eq_14_35
#print axioms Miao.NeoclassicalGrowth.eq_14_35_sign
#print axioms Miao.NeoclassicalGrowth.rb_m21
#print axioms Miao.NeoclassicalGrowth.rb_m22
#print axioms Miao.NeoclassicalGrowth.rb_det_system
#print axioms Miao.NeoclassicalGrowth.rb_det_M
#print axioms Miao.NeoclassicalGrowth.rb_char_one_neg
#print axioms Miao.NeoclassicalGrowth.rb_lam1
#print axioms Miao.NeoclassicalGrowth.rb_lam2
#print axioms Miao.NeoclassicalGrowth.rb_saddle_roots
#print axioms Miao.NeoclassicalGrowth.rb_saddle_eigen
#print axioms Miao.NeoclassicalGrowth.rb_left_eig
#print axioms Miao.NeoclassicalGrowth.rb_saddle_det
#print axioms Miao.NeoclassicalGrowth.rb_permanent_ss
#print axioms Miao.NeoclassicalGrowth.rb_permanent_shift
#print axioms Miao.NeoclassicalGrowth.rb_permanent_path
#print axioms Miao.NeoclassicalGrowth.rb_W2
#print axioms Miao.NeoclassicalGrowth.rb_P2
#print axioms Miao.NeoclassicalGrowth.rb_R2
#print axioms Miao.NeoclassicalGrowth.rb_split2
#print axioms Miao.NeoclassicalGrowth.rb_G2
#print axioms Miao.NeoclassicalGrowth.rb_IsLinRBC
#print axioms Miao.NeoclassicalGrowth.rb_Wrbc
#print axioms Miao.NeoclassicalGrowth.rb_Grbc
#print axioms Miao.NeoclassicalGrowth.rb_matAct_W2
#print axioms Miao.NeoclassicalGrowth.rb_matAct_G2
#print axioms Miao.NeoclassicalGrowth.rb_bk_iff
#print axioms Miao.NeoclassicalGrowth.rb_saddle_stoch
#print axioms Miao.NeoclassicalGrowth.rb_u38
#print axioms Miao.NeoclassicalGrowth.rb_u39
#print axioms Miao.NeoclassicalGrowth.rb_u38_kpr
#print axioms Miao.NeoclassicalGrowth.rb_u39_kpr
#print axioms Miao.NeoclassicalGrowth.rb_u38_limit
#print axioms Miao.NeoclassicalGrowth.rb_u38_printed_no_limit
#print axioms Miao.NeoclassicalGrowth.rb_u38_uc
#print axioms Miao.NeoclassicalGrowth.rb_u38_un
#print axioms Miao.NeoclassicalGrowth.rb_u38_mrs
#print axioms Miao.NeoclassicalGrowth.rb_u38_intratemporal
#print axioms Miao.NeoclassicalGrowth.rb_u38_homog
#print axioms Miao.NeoclassicalGrowth.rb_u38_bgp
#print axioms Miao.NeoclassicalGrowth.rb_u39_mrs
#print axioms Miao.NeoclassicalGrowth.rb_u39_frisch
#print axioms Miao.NeoclassicalGrowth.rb_u39_supply_loglin
#print axioms Miao.NeoclassicalGrowth.rb_nu_responses
#print axioms Miao.NeoclassicalGrowth.rb_consumption_channel
#print axioms Miao.NeoclassicalGrowth.rb_lottery
#print axioms Miao.NeoclassicalGrowth.rb_ghh_mrs
#print axioms Miao.NeoclassicalGrowth.rb_ghh_hours
#print axioms Miao.NeoclassicalGrowth.rb_ghh_not_kpr
#print axioms Miao.NeoclassicalGrowth.rb_habit_mu
#print axioms Miao.NeoclassicalGrowth.rx_HasPartials
#print axioms Miao.NeoclassicalGrowth.rx_HasPartials.comp
#print axioms Miao.NeoclassicalGrowth.rx_euler_homog
#print axioms Miao.NeoclassicalGrowth.RXTree
#print axioms Miao.NeoclassicalGrowth.RXTree.mk
#print axioms Miao.NeoclassicalGrowth.RXTree.cp
#print axioms Miao.NeoclassicalGrowth.RXTree.cp_nonneg
#print axioms Miao.NeoclassicalGrowth.RXTree.cp_sum
#print axioms Miao.NeoclassicalGrowth.rx_detTree
#print axioms Miao.NeoclassicalGrowth.rx_coinTree
#print axioms Miao.NeoclassicalGrowth.rx_E
#print axioms Miao.NeoclassicalGrowth.rx_Es
#print axioms Miao.NeoclassicalGrowth.rx_E_eq_Es
#print axioms Miao.NeoclassicalGrowth.rx_Es_add
#print axioms Miao.NeoclassicalGrowth.rx_Es_mul_left
#print axioms Miao.NeoclassicalGrowth.rx_Es_const
#print axioms Miao.NeoclassicalGrowth.rx_E_det
#print axioms Miao.NeoclassicalGrowth.rx_E_coin
#print axioms Miao.NeoclassicalGrowth.rx_E_add
#print axioms Miao.NeoclassicalGrowth.rx_E_const
#print axioms Miao.NeoclassicalGrowth.rx_E_mul_left
#print axioms Miao.NeoclassicalGrowth.rx_pv
#print axioms Miao.NeoclassicalGrowth.rx_pv_one
#print axioms Miao.NeoclassicalGrowth.rx_pv_add
#print axioms Miao.NeoclassicalGrowth.rx_pv_sum
#print axioms Miao.NeoclassicalGrowth.rx_pv_iterate
#print axioms Miao.NeoclassicalGrowth.rx_pv_limit
#print axioms Miao.NeoclassicalGrowth.rx_node_foc
#print axioms Miao.NeoclassicalGrowth.rx_homog_hasDerivAt
#print axioms Miao.NeoclassicalGrowth.rx_dep
#print axioms Miao.NeoclassicalGrowth.rx_cuY
#print axioms Miao.NeoclassicalGrowth.rx_dep_hasDerivAt
#print axioms Miao.NeoclassicalGrowth.rx_dep_strictMonoOn
#print axioms Miao.NeoclassicalGrowth.rx_dep_strictConvexOn
#print axioms Miao.NeoclassicalGrowth.rx_cuY_hasDerivAt_K
#print axioms Miao.NeoclassicalGrowth.rx_cuY_hasDerivAt_u
#print axioms Miao.NeoclassicalGrowth.rx_cu_planner_euler
#print axioms Miao.NeoclassicalGrowth.rx_cu_planner_util
#print axioms Miao.NeoclassicalGrowth.rx_cu_firm_foc
#print axioms Miao.NeoclassicalGrowth.eq_14_41
#print axioms Miao.NeoclassicalGrowth.rx_cu_household_euler
#print axioms Miao.NeoclassicalGrowth.rx_cu_decentralised_eq_planner
#print axioms Miao.NeoclassicalGrowth.rx_cu_calibration
#print axioms Miao.NeoclassicalGrowth.rx_cu_calibration_value
#print axioms Miao.NeoclassicalGrowth.ex_14_3_utilization
#print axioms Miao.NeoclassicalGrowth.ex_14_3_utilization_exists
#print axioms Miao.NeoclassicalGrowth.ex_14_3_u_eq_one
#print axioms Miao.NeoclassicalGrowth.ex_14_3_capital_labour
#print axioms Miao.NeoclassicalGrowth.rx_cu_util_closed
#print axioms Miao.NeoclassicalGrowth.rx_cu_util_increasing
#print axioms Miao.NeoclassicalGrowth.rx_cu_amplification
#print axioms Miao.NeoclassicalGrowth.rx_Phi
#print axioms Miao.NeoclassicalGrowth.rx_Phi_homog
#print axioms Miao.NeoclassicalGrowth.rx_Phi_partials
#print axioms Miao.NeoclassicalGrowth.rx_HasPartials.fst
#print axioms Miao.NeoclassicalGrowth.rx_HasPartials.snd
#print axioms Miao.NeoclassicalGrowth.rx_Phi_II
#print axioms Miao.NeoclassicalGrowth.rx_Phi_steady
#print axioms Miao.NeoclassicalGrowth.eq_14_43_steady
#print axioms Miao.NeoclassicalGrowth.rx_kappa_neg
#print axioms Miao.NeoclassicalGrowth.rx_phiQuad
#print axioms Miao.NeoclassicalGrowth.rx_phiQuad_normalised
#print axioms Miao.NeoclassicalGrowth.rx_phiQuad_K
#print axioms Miao.NeoclassicalGrowth.rx_Phi_K_pos
#print axioms Miao.NeoclassicalGrowth.rx_inverse_partials
#print axioms Miao.NeoclassicalGrowth.rx_uzawa_euler
#print axioms Miao.NeoclassicalGrowth.rx_invest_foc
#print axioms Miao.NeoclassicalGrowth.rx_no_adjustment_Q
#print axioms Miao.NeoclassicalGrowth.rx_labour_foc
#print axioms Miao.NeoclassicalGrowth.eq_14_45_N
#print axioms Miao.NeoclassicalGrowth.eq_14_45_K
#print axioms Miao.NeoclassicalGrowth.rx_dec1_labour
#print axioms Miao.NeoclassicalGrowth.rx_dec1_euler
#print axioms Miao.NeoclassicalGrowth.eq_14_47_foc
#print axioms Miao.NeoclassicalGrowth.rx_dec2_shares
#print axioms Miao.NeoclassicalGrowth.rx_dec2_bonds
#print axioms Miao.NeoclassicalGrowth.eq_14_48
#print axioms Miao.NeoclassicalGrowth.eq_14_49
#print axioms Miao.NeoclassicalGrowth.rx_dec3_producer
#print axioms Miao.NeoclassicalGrowth.rx_dec3_euler
#print axioms Miao.NeoclassicalGrowth.ex_14_5_dec1
#print axioms Miao.NeoclassicalGrowth.ex_14_5_dec2
#print axioms Miao.NeoclassicalGrowth.ex_14_5_budgets
#print axioms Miao.NeoclassicalGrowth.ex_14_5_dec3_iff
#print axioms Miao.NeoclassicalGrowth.rx_Es_pos
#print axioms Miao.NeoclassicalGrowth.ex_14_5_dec3_counterexample
#print axioms Miao.NeoclassicalGrowth.ex_14_5_dec3_corrected
#print axioms Miao.NeoclassicalGrowth.rx_producer_profit
#print axioms Miao.NeoclassicalGrowth.rx_div
#print axioms Miao.NeoclassicalGrowth.rx_sdf
#print axioms Miao.NeoclassicalGrowth.rx_hayashi_step
#print axioms Miao.NeoclassicalGrowth.proposition_14_3_1
#print axioms Miao.NeoclassicalGrowth.rx_P_recursion
#print axioms Miao.NeoclassicalGrowth.rx_dividend_eq
#print axioms Miao.NeoclassicalGrowth.rx_stock_return
#print axioms Miao.NeoclassicalGrowth.rx_firmFeasible
#print axioms Miao.NeoclassicalGrowth.rx_divPlan
#print axioms Miao.NeoclassicalGrowth.rx_firmValue
#print axioms Miao.NeoclassicalGrowth.rx_scale
#print axioms Miao.NeoclassicalGrowth.rx_scale_feasible
#print axioms Miao.NeoclassicalGrowth.rx_div_scale
#print axioms Miao.NeoclassicalGrowth.rx_firmValue_homog
#print axioms Miao.NeoclassicalGrowth.rx_pv_smul
#print axioms Miao.NeoclassicalGrowth.rx_truncValue_homog
#print axioms Miao.NeoclassicalGrowth.proposition_14_3_1_marginal
#print axioms Miao.NeoclassicalGrowth.eq_14_50
#print axioms Miao.NeoclassicalGrowth.eq_14_51
#print axioms Miao.NeoclassicalGrowth.rx_G52
#print axioms Miao.NeoclassicalGrowth.rx_G52_d1
#print axioms Miao.NeoclassicalGrowth.rx_G52_d2
#print axioms Miao.NeoclassicalGrowth.rx_G52_steady
#print axioms Miao.NeoclassicalGrowth.rx_G52_diag
#print axioms Miao.NeoclassicalGrowth.eq_14_52_steady
#print axioms Miao.NeoclassicalGrowth.rx_hasDerivAt_exp
#print axioms Miao.NeoclassicalGrowth.rx_hasDerivAt_exp1
#print axioms Miao.NeoclassicalGrowth.rx_ratio_path
#print axioms Miao.NeoclassicalGrowth.rx_hasDerivAt_rate
#print axioms Miao.NeoclassicalGrowth.ex_14_6_invest_43
#print axioms Miao.NeoclassicalGrowth.ex_14_6_invest_43_solved
#print axioms Miao.NeoclassicalGrowth.ex_14_6_capital_43
#print axioms Miao.NeoclassicalGrowth.ex_14_6_Q_43
#print axioms Miao.NeoclassicalGrowth.ex_14_6_Q_43_solved
#print axioms Miao.NeoclassicalGrowth.rx_g52_derivs
#print axioms Miao.NeoclassicalGrowth.rx_g1
#print axioms Miao.NeoclassicalGrowth.rx_g2
#print axioms Miao.NeoclassicalGrowth.ex_14_6_invest_52
#print axioms Miao.NeoclassicalGrowth.ex_14_6_invest_52_solved
#print axioms Miao.NeoclassicalGrowth.ex_14_6_Q_52
#print axioms Miao.NeoclassicalGrowth.ex_14_6_capital_52
#print axioms Miao.NeoclassicalGrowth.ex_14_6_differences
#print axioms Miao.NeoclassicalGrowth.rx_lnz_walk
#print axioms Miao.NeoclassicalGrowth.rx_trend_scale
#print axioms Miao.NeoclassicalGrowth.rx_detrend_output
#print axioms Miao.NeoclassicalGrowth.rx_detrend_capital
#print axioms Miao.NeoclassicalGrowth.rx_detrend_rental
#print axioms Miao.NeoclassicalGrowth.rx_detrend_labour
#print axioms Miao.NeoclassicalGrowth.rx_detrend_resource
#print axioms Miao.NeoclassicalGrowth.rx_detrend_wage
#print axioms Miao.NeoclassicalGrowth.rx_detrend_euler
#print axioms Miao.NeoclassicalGrowth.rx_detrend_back
#print axioms Miao.NeoclassicalGrowth.rx_trend_exp_G
#print axioms Miao.NeoclassicalGrowth.rx_trendSS
#print axioms Miao.NeoclassicalGrowth.rx_trR
#print axioms Miao.NeoclassicalGrowth.rx_trk
#print axioms Miao.NeoclassicalGrowth.rx_try
#print axioms Miao.NeoclassicalGrowth.rx_tri
#print axioms Miao.NeoclassicalGrowth.rx_trc
#print axioms Miao.NeoclassicalGrowth.rx_trN
#print axioms Miao.NeoclassicalGrowth.rx_rpow_kN
#print axioms Miao.NeoclassicalGrowth.rx_trk_pow
#print axioms Miao.NeoclassicalGrowth.rx_trend_steady_unique
#print axioms Miao.NeoclassicalGrowth.rx_trend_steady_exists
#print axioms Miao.NeoclassicalGrowth.rx_linear_partials
#print axioms Miao.NeoclassicalGrowth.rx_ist_foc
#print axioms Miao.NeoclassicalGrowth.rx_ist_price
#print axioms Miao.NeoclassicalGrowth.rx_gov_kn
