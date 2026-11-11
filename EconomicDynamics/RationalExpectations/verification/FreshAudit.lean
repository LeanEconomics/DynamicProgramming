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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ConditionalExpectation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.Deriv.Pow
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Definitions of Chapter 1

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Upper triangular matrices and geometric decay

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stable and unstable subspaces

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The real stable and unstable subspaces of a real matrix

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stable estimate

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# First-order linear systems: regularity, steady state, stable matrices

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A real block diagonalisation `W = P⁻¹ diag(J_s, J_u) P`

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonsingular systems: Theorems 1.4.1 and 1.4.2, Corollary 1.4.1

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Generalized eigenvalues and the complex generalized Schur (QZ) form

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Singular systems: Klein's method

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Conditional expectations and linear rational expectations systems

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The conditional expectations of `L¹(Ω, F, Pr)` given a filtration

Miao, Chapter 2, p. 45 (the probability space `(Ω, F, Pr)`, the filtration `{F_t}` and `E_t`)
and Definition 2.3.1, p. 52. For a finite measure `μ` on `(Ω, m0)` and a filtration
`ℱ : Filtration ℕ m0`, Mathlib's `L¹` conditional expectation `condExpL1CLM` given `ℱ t` is a
`CondExpSystem` on `Ω →₁[μ] 𝕜`, for any `RCLike` scalar field `𝕜`:

* `condExpSystemL1 𝕜 ℱ μ : CondExpSystem 𝕜 (Ω →₁[μ] 𝕜)`, in particular for `𝕜 = ℝ`
  (`condExpSystemL1_real`) and for `𝕜 = ℂ` (`condExpSystemL1_complex`, the field used in the
  Klein and Sims theorems). `E_t` is `𝕜`-linear (`condExpL1CLM_smul`), `‖E_t‖ ≤ 1`
  (`condExpL1_norm_apply_le`, from `integral_norm_condExp_le`) and the tower property holds
  both ways (`condExpL1_tower_le`, `condExpL1_tower_ge`).
* Interpretation: `E_t X` agrees a.e. with `μ[X | ℱ t]` (`condExpL1_ae_eq_condExp`);
  `E_t X = X` iff `X` is a.e. equal to an `ℱ t`-strongly measurable function
  (`condExpL1_eq_self_iff`, `condExpL1_eq_self_iff_exists`), so `IsAdaptedV` is adaptedness;
  `‖X‖ = ∫|X|` (`l1_norm_eq_integral_abs`), so `IsStableProc` on `L¹` is exactly
  Definition 2.3.1's `max_j E|X_j| < M` (`l1_isStableProc_iff`).

Departure: the book's processes are measurable functions; here (as for any `L¹` theory) they
are classes of functions up to `Pr`-null sets.
-/

open MeasureTheory

namespace Miao.RationalExpectations

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- `‖E X‖ ≤ ‖X‖` for Mathlib's `L¹` conditional expectation (Miao, p. 45). -/
theorem condExpL1_norm_apply_le {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (X : Ω →₁[μ] 𝕜) :
    ‖condExpL1CLM 𝕜 hm μ X‖ ≤ ‖X‖ := by
  have hX : Integrable (⇑X) μ := L1.integrable_coeFn X
  have hae := condExp_ae_eq_condExpL1CLM hm hX
  rw [Integrable.toL1_coeFn X hX] at hae
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  calc ∫ ω, ‖condExpL1CLM 𝕜 hm μ X ω‖ ∂μ = ∫ ω, ‖(μ[⇑X | m]) ω‖ ∂μ :=
        integral_congr_ae (hae.mono fun ω h => by simp only [h])
    _ ≤ ∫ ω, ‖X ω‖ ∂μ := integral_norm_condExp_le _

/-- `E_t X` agrees a.e. with `μ[X | m]` (Miao, p. 45). -/
theorem condExpL1_ae_eq_condExp {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLM 𝕜 hm μ X =ᵐ[μ] μ[⇑X | m] := by
  have hX : Integrable (⇑X) μ := L1.integrable_coeFn X
  have hae := condExp_ae_eq_condExpL1CLM hm hX
  rw [Integrable.toL1_coeFn X hX] at hae
  exact hae.symm

/-- `E_s E_t = E_s` for `m₁ ≤ m₂` (law of iterated expectations, Miao, p. 45). -/
theorem condExpL1_tower_le {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm₂)]
    [SigmaFinite (μ.trim (h12.trans hm₂))] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLM 𝕜 (h12.trans hm₂) μ (condExpL1CLM 𝕜 hm₂ μ X) =
      condExpL1CLM 𝕜 (h12.trans hm₂) μ X := by
  apply Lp.ext_iff.mpr
  have h1 := condExpL1_ae_eq_condExp μ (h12.trans hm₂) (condExpL1CLM 𝕜 hm₂ μ X)
  have h2 : μ[⇑(condExpL1CLM 𝕜 hm₂ μ X) | m₁] =ᵐ[μ] μ[μ[⇑X | m₂] | m₁] :=
    condExp_congr_ae (condExpL1_ae_eq_condExp μ hm₂ X)
  have h3 : μ[μ[⇑X | m₂] | m₁] =ᵐ[μ] μ[⇑X | m₁] := condExp_condExp_of_le h12 hm₂
  have h4 := condExpL1_ae_eq_condExp μ (h12.trans hm₂) X
  exact h1.trans (h2.trans (h3.trans h4.symm))

/-- `E_t E_s = E_s` for `m₁ ≤ m₂`: `E_s X` is already `m₂`-measurable (Miao, p. 45). -/
theorem condExpL1_tower_ge {𝕜 : Type*} [RCLike 𝕜] (μ : Measure Ω)
    {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm₂)]
    [SigmaFinite (μ.trim (h12.trans hm₂))] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLM 𝕜 hm₂ μ (condExpL1CLM 𝕜 (h12.trans hm₂) μ X) =
      condExpL1CLM 𝕜 (h12.trans hm₂) μ X :=
  condExpL1CLM_of_aestronglyMeasurable' _
    ((aestronglyMeasurable_condExpL1CLM (hm := h12.trans hm₂) X).mono h12)

/-- `E_t` as a `𝕜`-linear map (`condExpL1CLM` is `𝕜`-homogeneous, `condExpL1CLM_smul`). -/
noncomputable def condExpL1CLMK (𝕜 : Type*) [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] :
    (Ω →₁[μ] 𝕜) →L[𝕜] Ω →₁[μ] 𝕜 where
  toFun := condExpL1CLM 𝕜 hm μ
  map_add' := (condExpL1CLM 𝕜 hm μ).map_add
  map_smul' c X := condExpL1CLM_smul c X
  cont := (condExpL1CLM 𝕜 hm μ).continuous

theorem condExpL1CLMK_apply (𝕜 : Type*) [RCLike 𝕜] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (X : Ω →₁[μ] 𝕜) :
    condExpL1CLMK 𝕜 μ hm X = condExpL1CLM 𝕜 hm μ X := rfl

/-- **The concrete instance** (Miao, p. 45): for a finite measure `μ` and a filtration
`ℱ`, `E_t = ` Mathlib's `L¹` conditional expectation given `ℱ t` is a `CondExpSystem` on
`L¹(Ω, F, μ; 𝕜)`. -/
noncomputable def condExpSystemL1 (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] : CondExpSystem 𝕜 (Ω →₁[μ] 𝕜) where
  E t := condExpL1CLMK 𝕜 μ (ℱ.le t)
  norm_le t := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => by
    rw [one_mul]
    exact condExpL1_norm_apply_le μ (ℱ.le t) X
  tower_le s t hst := by
    ext1 X
    exact condExpL1_tower_le μ (ℱ.mono hst) (ℱ.le t) X
  tower_ge s t hst := by
    ext1 X
    exact condExpL1_tower_ge μ (ℱ.mono hst) (ℱ.le t) X

theorem condExpSystemL1_E_apply (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X = condExpL1CLM 𝕜 (ℱ.le t) μ X := rfl

/-- The real instance `CondExpSystem ℝ (Ω →₁[μ] ℝ)` (Miao, p. 45). -/
noncomputable def condExpSystemL1_real (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    [IsFiniteMeasure μ] : CondExpSystem ℝ (Ω →₁[μ] ℝ) :=
  condExpSystemL1 ℝ ℱ μ

/-- The complex instance `CondExpSystem ℂ (Ω →₁[μ] ℂ)`, the setting of the Klein and Sims
theorems (Miao, pp. 55–64). -/
noncomputable def condExpSystemL1_complex (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    [IsFiniteMeasure μ] : CondExpSystem ℂ (Ω →₁[μ] ℂ) :=
  condExpSystemL1 ℂ ℱ μ

/-- Miao, p. 45: `E_t X` agrees a.e. with the conditional expectation `μ[X | ℱ t]`. -/
theorem condExpSystemL1_ae_eq (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X =ᵐ[μ] μ[⇑X | ℱ t] :=
  condExpL1_ae_eq_condExp μ (ℱ.le t) X

/-- Miao, p. 45 (adaptedness): `E_t X = X` iff `X` is a.e. strongly `ℱ t`-measurable. -/
theorem condExpL1_eq_self_iff (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X = X ↔ AEStronglyMeasurable[ℱ t] (⇑X) μ := by
  constructor
  · intro h
    have hm := aestronglyMeasurable_condExpL1CLM (hm := ℱ.le t) X
    rw [← condExpSystemL1_E_apply, h] at hm
    exact hm
  · intro h
    exact condExpL1CLM_of_aestronglyMeasurable' X h

/-- Miao, p. 45: `E_t X = X` iff `X` has an `ℱ t`-strongly measurable representative. -/
theorem condExpL1_eq_self_iff_exists (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] (t : ℕ) (X : Ω →₁[μ] 𝕜) :
    (condExpSystemL1 𝕜 ℱ μ).E t X = X ↔
      ∃ g : Ω → 𝕜, StronglyMeasurable[ℱ t] g ∧ ⇑X =ᵐ[μ] g := by
  rw [condExpL1_eq_self_iff]
  exact ⟨fun h => ⟨h.mk _, h.stronglyMeasurable_mk, h.ae_eq_mk⟩,
    fun ⟨g, hg, hXg⟩ => ⟨g, hg, hXg⟩⟩

/-- Miao, p. 45: a process of `L¹` vectors is adapted (`IsAdaptedV`) iff every component has an
`ℱ t`-strongly measurable representative. -/
theorem condExpL1_isAdaptedV_iff (𝕜 : Type*) [RCLike 𝕜] (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) [IsFiniteMeasure μ] {ι : Type*} (x : ℕ → ι → Ω →₁[μ] 𝕜) :
    IsAdaptedV (condExpSystemL1 𝕜 ℱ μ) x ↔
      ∀ t i, ∃ g : Ω → 𝕜, StronglyMeasurable[ℱ t] g ∧ ⇑(x t i) =ᵐ[μ] g := by
  simp only [IsAdaptedV, condExpL1_eq_self_iff_exists]

/-- Definition 2.3.1 (Miao, p. 52): the `L¹` norm is `E|X|`. -/
theorem l1_norm_eq_integral_abs {μ : Measure Ω} (X : Ω →₁[μ] ℝ) :
    ‖X‖ = ∫ ω, |X ω| ∂μ := by
  rw [L1.norm_eq_integral_norm]
  rfl

/-- **Definition 2.3.1** (Miao, p. 52) on `L¹`: `IsStableProc x` is exactly
`max_j E|x_{t,j}| < M` for all `t`, some `M > 0`. -/
theorem l1_isStableProc_iff {μ : Measure Ω} {ι : Type*} (x : ℕ → ι → Ω →₁[μ] ℝ) :
    IsStableProc x ↔ ∃ M, 0 < M ∧ ∀ t i, ∫ ω, |x t i ω| ∂μ < M := by
  simp only [IsStableProc, l1_norm_eq_integral_abs]

/-- The complex form of Definition 2.3.1 (Miao, p. 52): `‖X‖ = E|X|` on `L¹(Ω; ℂ)`. -/
theorem l1_norm_eq_integral_norm_complex {μ : Measure Ω} (X : Ω →₁[μ] ℂ) :
    ‖X‖ = ∫ ω, ‖X ω‖ ∂μ :=
  L1.norm_eq_integral_norm X

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# First-order linear stochastic systems: moments

Miao, §2.1, pp. 45–48, and the white-noise claims of p. 56. Concrete probability: a probability
measure `μ` on `(Ω, m0)`, a filtration `ℱ`, processes `z : ℕ → Ω → n → ℝ`, `ε : ℕ → Ω → k → ℝ`,
conditional expectations `μ[·|ℱ t]`, moments as integrals.

* (2.1) `z_{t+1} = Φz_t + Σε_{t+1}` and (2.2) `E_tε_{t+1} = 0`, `E_tε_{t+1}ε'_{t+1} = I` are the
  fields of `var_Model` (with `ε` adapted and square integrable, `z₀` `ℱ₀`-measurable and square
  integrable); `var_Model.z_memLp`, `var_Model.z_meas`: every `z_t` is square integrable and
  `ℱ_t`-measurable.
* Examples 2.1.1–2.1.3 as pathwise equivalences (`example_2_1_1`, `example_2_1_2`,
  `example_2_1_3`).
* Definition 2.1.1 (`var_IsCovStationary`). The book's "covariance depends only on `|t − s|`" is
  stated for the lag `t − s ≥ 0`: for vector processes `E(X_t − m)(X_s − m)'` with `t < s` is the
  transpose `Γ(s − t)'`, and `Γ(j)` need not be symmetric (`definition_2_1_1_not_symmetric`).
* Means: `μ_{t+1} = Φμ_t` (`var_mean_rec`), `μ_t = Φᵗμ₀ → 0` for stable `Φ`
  (`var_mean_tendsto_zero`), `μ_t = 0` if `μ₀ = 0`.
* The Lyapunov equation `C = ΦCΦ' + ΣΣ'`: for stable `Φ` its unique solution is
  `∑ⱼΦʲΣΣ'Φ'ʲ` (`var_lyapSol`, `lyap_fixed`, `lyap_unique`) and successive iteration converges to
  it from any start (`lyap_iterate_tendsto`); the second moments of every solution of (2.1)–(2.2)
  satisfy `E z_{t+1}z'_{t+1} = Φ E z_tz'_t Φ' + ΣΣ'` (`var_mom_rec`) and converge to it
  (`var_mom_tendsto`); a covariance-stationary solution has mean `0`, `C_z(0) = ∑ⱼΦʲΣΣ'Φ'ʲ` and
  `C_z(j) = ΦʲC_z(0)` (`var_stationary_moments`), and conversely `z₀` with these moments makes `z`
  covariance stationary (`var_stationary_of_initial`): the stationary first and second moments
  are unique. `C_z(j) = ΦʲC_z(0)` (`var_autocov`).
* Impulse responses: `z_{t+j} = Φʲz_t + ∑_{i<j}ΦⁱΣε_{t+j−i}` (`var_ma_shift`), the
  finite-horizon MA representation `z_{t+1} = Φ^{t+1}z₀ + ∑_{j≤t}ΦʲΣε_{t+1−j}` (`var_ma`), the
  initial-condition term vanishes for stable `Φ` (`var_ma_initial_tendsto`), and `ΦʲΣ` is the
  response of `z_{t+1+j}` to a shock to `ε_{t+1}` (`var_impulse_response`).
* White noise (Definition 2.3.3, `var_IsWhiteNoise`): it is stable since
  `E|X| ≤ (EX²)^{1/2}` (`whiteNoise_stable`, `whiteNoise_stable_L1`); `{ε_{t+1}}` satisfying
  (2.2) is a white noise with `Σ = I` (`mds_whiteNoise`). (A white noise that violates (2.2), and
  the failure of "unique stationary distribution", are in `VARExamples`.)

Departure: "unique stationary distribution" (p. 47) is not implied by (2.1)–(2.2), which pin down
only the first two conditional moments of `ε`; what is proved is uniqueness of the stationary
first and second moments (a counterexample to the distributional claim is in `VARExamples`).
-/

open MeasureTheory Filter Topology

namespace Miao.RationalExpectations

open scoped Matrix

/-! ### Examples 2.1.1–2.1.3 (pathwise) -/

/-- **Example 2.1.1** (Miao, p. 46): with `b ≠ 1` and `z_t = y_t − d/(1 − b)`,
`y_{t+1} = by_t + d + σε_{t+1}` iff `z_{t+1} = bz_t + σε_{t+1}`. -/
theorem example_2_1_1 {b d σ : ℝ} (hb : 1 - b ≠ 0) (y e : ℕ → ℝ) :
    (∀ t, y (t + 1) = b * y t + d + σ * e (t + 1)) ↔
      ∀ t, y (t + 1) - d / (1 - b) = b * (y t - d / (1 - b)) + σ * e (t + 1) := by
  refine forall_congr' fun t => ?_
  have h : d = (1 - b) * (d / (1 - b)) := by field_simp
  constructor
  · intro h1
    linear_combination h1 + h
  · intro h1
    linear_combination h1 - h

/-- **Example 2.1.2** (Miao, p. 46): `y_{t+1} = by_t + ε_{t+1} + cε_t` iff the state
`(y_t, ε_t)` follows `(y_{t+1}, ε_{t+1})' = [b c; 0 0](y_t, ε_t)' + (1, 1)'ε_{t+1}`. -/
theorem example_2_1_2 {b c : ℝ} (y e : ℕ → ℝ) :
    (∀ t, y (t + 1) = b * y t + e (t + 1) + c * e t) ↔
      ∀ t, ![y (t + 1), e (t + 1)] =
        !![b, c; 0, 0] *ᵥ ![y t, e t] + e (t + 1) • (![1, 1] : Fin 2 → ℝ) := by
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    ext i
    fin_cases i
    · simp [h]
      ring
    · simp
  · intro h
    have := congrFun h 0
    simp at this
    linarith
/-- **Example 2.1.3** (Miao, p. 46): the VAR(2) `y_{t+1} = A₁y_t + A₂y_{t−1} + Cε_{t+1}` (dates
`t ≥ 1`) iff the stacked state `(y_t, y_{t−1})` follows the first-order system with
`[A₁ A₂; I 0]` and `[C; 0]`. -/
theorem example_2_1_3 {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
    (A₁ A₂ : Matrix n n ℝ) (C : Matrix n k ℝ) (y : ℕ → n → ℝ) (e : ℕ → k → ℝ) :
    (∀ t, y (t + 2) = A₁ *ᵥ y (t + 1) + A₂ *ᵥ y t + C *ᵥ e (t + 2)) ↔
      ∀ t, Sum.elim (y (t + 2)) (y (t + 1)) =
        Matrix.fromBlocks A₁ A₂ 1 0 *ᵥ Sum.elim (y (t + 1)) (y t) +
          Matrix.fromRows C 0 *ᵥ e (t + 2) := by
  refine forall_congr' fun t => ?_
  rw [Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Sum.elim_comp_inl,
    Sum.elim_comp_inr]
  rw [← Sum.elim_add_add, add_zero]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg (fun v : n ⊕ n → ℝ => v ∘ Sum.inl) h
    simpa only [Sum.elim_comp_inl] using this

/-! ### Matrix lemmas: powers with geometric decay -/

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem var_pow_entry_le {Φ : Matrix n n ℝ} {K a : ℝ} (hΦ : HasGeomDecay Φ K a) (k : ℕ)
    (i j : n) : |(Φ ^ k) i j| ≤ K * a ^ k := by
  have h := hΦ.2.2.2 k (Pi.single j 1)
  have e : ((Φ ^ k) *ᵥ Pi.single j 1) i = (Φ ^ k) i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hs : ‖(Pi.single j 1 : n → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hK : 0 ≤ K * a ^ k := mul_nonneg hΦ.2.2.1 (pow_nonneg hΦ.1 k)
  calc |(Φ ^ k) i j| = ‖((Φ ^ k) *ᵥ Pi.single j 1) i‖ := by rw [e, Real.norm_eq_abs]
    _ ≤ ‖(Φ ^ k) *ᵥ Pi.single j 1‖ := norm_le_pi_norm _ i
    _ ≤ K * a ^ k * ‖(Pi.single j 1 : n → ℝ)‖ := h
    _ ≤ K * a ^ k * 1 := by gcongr
    _ = K * a ^ k := mul_one _

/-- The `ℓ¹` size of a matrix, `∑ᵢⱼ|Yᵢⱼ|`. -/
def var_l1 (Y : Matrix n n ℝ) : ℝ := ∑ c, ∑ d, |Y c d|

omit [DecidableEq n] in
theorem var_l1_nonneg (Y : Matrix n n ℝ) : 0 ≤ var_l1 Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq n] in
theorem var_sandwich_apply (A Y B : Matrix n n ℝ) (i j : n) :
    (A * Y * Bᵀ) i j = ∑ c, ∑ d, A i c * Y c d * B j d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `|(ΦᵏYΦ'ᵏ)ᵢⱼ| ≤ (Kaᵏ)²∑|Y|`. -/
theorem var_sandwich_le {Φ : Matrix n n ℝ} {K a : ℝ} (hΦ : HasGeomDecay Φ K a) (k : ℕ)
    (Y : Matrix n n ℝ) (i j : n) :
    |(Φ ^ k * Y * (Φ ^ k)ᵀ) i j| ≤ (K * a ^ k) ^ 2 * var_l1 Y := by
  rw [var_sandwich_apply, var_l1, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := var_pow_entry_le hΦ k i c
  have h2 := var_pow_entry_le hΦ k j d
  have hK : 0 ≤ K * a ^ k := mul_nonneg hΦ.2.2.1 (pow_nonneg hΦ.1 k)
  calc |(Φ ^ k) i c| * |Y c d| * |(Φ ^ k) j d| ≤ (K * a ^ k) * |Y c d| * (K * a ^ k) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2 (abs_nonneg _)
          (mul_nonneg hK (abs_nonneg _))
    _ = (K * a ^ k) ^ 2 * |Y c d| := by ring

/-! ### The Lyapunov equation -/

/-- The Lyapunov map `C ↦ ΦCΦ' + Q` (Miao, p. 47). -/
def var_lyapMap (Φ Q : Matrix n n ℝ) (X : Matrix n n ℝ) : Matrix n n ℝ := Φ * X * Φᵀ + Q

/-- The candidate solution `∑ⱼΦʲQΦ'ʲ` of the Lyapunov equation, entrywise. -/
noncomputable def var_lyapSol (Φ Q : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => ∑' k : ℕ, (Φ ^ k * Q * (Φ ^ k)ᵀ) i j

theorem var_lyap_summable {Φ : Matrix n n ℝ} {K a : ℝ} (hΦ : HasGeomDecay Φ K a)
    (Q : Matrix n n ℝ) (i j : n) : Summable fun k : ℕ => (Φ ^ k * Q * (Φ ^ k)ᵀ) i j := by
  have ha : a ^ 2 < 1 := by nlinarith [hΦ.1, hΦ.2.1]
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg a) ha).mul_left (K ^ 2 * var_l1 Q)) fun k => ?_
  rw [Real.norm_eq_abs]
  refine (var_sandwich_le hΦ k Q i j).trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
  ring

/-- Iterating the Lyapunov map: `Lᵏ(X₀) = ΦᵏX₀Φ'ᵏ + ∑_{j<k}ΦʲQΦ'ʲ`. -/
theorem var_lyap_iterate (Φ Q X0 : Matrix n n ℝ) (k : ℕ) :
    (var_lyapMap Φ Q)^[k] X0 =
      Φ ^ k * X0 * (Φ ^ k)ᵀ + ∑ j ∈ Finset.range k, Φ ^ j * Q * (Φ ^ j)ᵀ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, var_lyapMap, Finset.sum_range_succ']
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul, pow_succ',
      Matrix.transpose_mul, pow_zero, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one,
      Matrix.mul_assoc]
    abel

/-- Miao, p. 47: "It can be solved numerically by successive iteration": for stable `Φ` the
iterates of `C ↦ ΦCΦ' + Q` converge (entrywise) to `∑ⱼΦʲQΦ'ʲ` from any start. -/
theorem lyap_iterate_tendsto (Φ : Matrix n n ℝ) (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom))
    (Q X0 : Matrix n n ℝ) (i j : n) :
    Tendsto (fun k => ((var_lyapMap Φ Q)^[k] X0) i j) atTop (𝓝 (var_lyapSol Φ Q i j)) := by
  obtain ⟨K, a, hd⟩ := hasGeomDecay_of_isStableMatrix Φ hΦ
  simp only [var_lyap_iterate, Matrix.add_apply, Matrix.sum_apply]
  rw [← zero_add (var_lyapSol Φ Q i j)]
  refine Tendsto.add ?_ ?_
  · have ha : (fun k : ℕ => (K * a ^ k) ^ 2 * var_l1 X0) = fun k => K ^ 2 * var_l1 X0 * (a ^ 2) ^ k
      := by funext k; rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; ring
    have hlim : Tendsto (fun k : ℕ => (K * a ^ k) ^ 2 * var_l1 X0) atTop (𝓝 0) := by
      rw [ha]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg a)
        (by nlinarith [hd.1, hd.2.1])).const_mul (K ^ 2 * var_l1 X0)
    refine squeeze_zero_norm (fun k => ?_) hlim
    rw [Real.norm_eq_abs]
    exact var_sandwich_le hd k X0 i j
  · exact (var_lyap_summable hd Q i j).hasSum.tendsto_sum_nat

omit [DecidableEq n] in
theorem var_lyapMap_apply (Φ Q X : Matrix n n ℝ) (i j : n) :
    var_lyapMap Φ Q X i j = ∑ c, ∑ d, Φ i c * X c d * Φ j d + Q i j := by
  rw [var_lyapMap, Matrix.add_apply, var_sandwich_apply]

omit [DecidableEq n] in
theorem var_lyapMap_continuous (Φ Q : Matrix n n ℝ) {X : ℕ → Matrix n n ℝ}
    {Y : Matrix n n ℝ} (h : ∀ i j, Tendsto (fun k => X k i j) atTop (𝓝 (Y i j))) (i j : n) :
    Tendsto (fun k => var_lyapMap Φ Q (X k) i j) atTop (𝓝 (var_lyapMap Φ Q Y i j)) := by
  simp only [var_lyapMap_apply]
  refine Tendsto.add ?_ tendsto_const_nhds
  refine tendsto_finsetSum _ fun c _ => tendsto_finsetSum _ fun d _ => ?_
  exact ((h c d).const_mul _).mul_const _

/-- Miao, p. 47 (the discrete Lyapunov equation): for stable `Φ`, `∑ⱼΦʲQΦ'ʲ` solves
`C = ΦCΦ' + Q`. -/
theorem lyap_fixed (Φ : Matrix n n ℝ) (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom))
    (Q : Matrix n n ℝ) : var_lyapMap Φ Q (var_lyapSol Φ Q) = var_lyapSol Φ Q := by
  ext i j
  have h1 := lyap_iterate_tendsto Φ hΦ Q 0
  have h2 := var_lyapMap_continuous Φ Q h1 i j
  have h3 : Tendsto (fun k => ((var_lyapMap Φ Q)^[k + 1] 0) i j) atTop
      (𝓝 (var_lyapSol Φ Q i j)) := (tendsto_add_atTop_iff_nat 1).2 (h1 i j)
  simp only [Function.iterate_succ_apply'] at h3
  exact tendsto_nhds_unique h2 h3

/-- Miao, p. 47: for stable `Φ` the Lyapunov equation `C = ΦCΦ' + Q` has exactly one solution. -/
theorem lyap_unique (Φ : Matrix n n ℝ) (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom))
    (Q C : Matrix n n ℝ) (hC : var_lyapMap Φ Q C = C) : C = var_lyapSol Φ Q := by
  ext i j
  have hfix : ∀ k, (var_lyapMap Φ Q)^[k] C = C := fun k =>
    Function.iterate_fixed hC k
  have h := lyap_iterate_tendsto Φ hΦ Q C i j
  simp only [hfix] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

/-! ### The model (2.1)–(2.2) -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {k : Type*} [DecidableEq k]

/-- The shock conditions (2.2) (Miao, p. 46), with `ε` adapted and square integrable:
`E_tε_{t+1} = 0`, `E_tε_{t+1}ε'_{t+1} = I`. -/
structure var_ShockMDS (μ : Measure Ω) (ℱ : Filtration ℕ m0) (ε : ℕ → Ω → k → ℝ) : Prop where
  /-- `ε_t` is square integrable. -/
  memLp : ∀ t i, MemLp (fun ω => ε t ω i) 2 μ
  /-- `ε_t` is `ℱ_t`-measurable. -/
  meas : ∀ t i, Measurable[ℱ t] fun ω => ε t ω i
  /-- `E_tε_{t+1} = 0`. -/
  mds : ∀ t i, μ[fun ω => ε (t + 1) ω i | ℱ t] =ᵐ[μ] 0
  /-- `E_tε_{t+1}ε'_{t+1} = I`. -/
  cvar : ∀ t i j, μ[fun ω => ε (t + 1) ω i * ε (t + 1) ω j | ℱ t] =ᵐ[μ]
    fun _ => if i = j then 1 else 0

variable [Fintype k]

variable (n) (μ : Measure Ω) (ℱ : Filtration ℕ m0) (Φ : Matrix n n ℝ) (Sg : Matrix n k ℝ)
  (z : ℕ → Ω → n → ℝ) (ε : ℕ → Ω → k → ℝ) in
/-- The model (2.1)–(2.2) (Miao, pp. 45–46): `z_{t+1} = Φz_t + Σε_{t+1}`, `z₀` given
(`ℱ₀`-measurable, square integrable), `ε` satisfying (2.2). -/
structure var_Model : Prop where
  /-- (2.1). -/
  eq21 : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω
  /-- `z₀` is square integrable. -/
  z0_memLp : ∀ i, MemLp (fun ω => z 0 ω i) 2 μ
  /-- `z₀` is `ℱ₀`-measurable. -/
  z0_meas : ∀ i, Measurable[ℱ 0] fun ω => z 0 ω i
  /-- (2.2). -/
  shock : var_ShockMDS μ ℱ ε

/-- The mean vector `Ez`. -/
noncomputable def var_mean (μ : Measure Ω) (X : Ω → n → ℝ) : n → ℝ :=
  fun i => ∫ ω, X ω i ∂μ

/-- The second-moment matrix `EXY'`. -/
noncomputable def var_mom {p q : Type*} (μ : Measure Ω) (X : Ω → p → ℝ) (Y : Ω → q → ℝ) :
    Matrix p q ℝ :=
  Matrix.of fun i j => ∫ ω, X ω i * Y ω j ∂μ

omit [DecidableEq n] [DecidableEq k] in
theorem var_rec_apply {Φ : Matrix n n ℝ} {Sg : Matrix n k ℝ} {z : ℕ → Ω → n → ℝ}
    {ε : ℕ → Ω → k → ℝ} (hrec : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω)
    (t : ℕ) (i : n) :
    (fun ω => z (t + 1) ω i) =
      fun ω => ∑ c, Φ i c * z t ω c + ∑ l, Sg i l * ε (t + 1) ω l := by
  funext ω
  rw [hrec]
  simp [Matrix.mulVec, dotProduct]

namespace var_Model

variable {μ : Measure Ω} {ℱ : Filtration ℕ m0} {Φ : Matrix n n ℝ} {Sg : Matrix n k ℝ}
  {z : ℕ → Ω → n → ℝ} {ε : ℕ → Ω → k → ℝ}

omit [DecidableEq n] in
theorem z_memLp (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) (i : n) :
    MemLp (fun ω => z t ω i) 2 μ := by
  induction t generalizing i with
  | zero => exact h.z0_memLp i
  | succ t ih =>
    rw [var_rec_apply h.eq21]
    refine MemLp.add ?_ ?_
    · exact memLp_finsetSum _ fun c _ => (ih c).const_mul _
    · exact memLp_finsetSum _ fun l _ => (h.shock.memLp (t + 1) l).const_mul _

omit [DecidableEq n] in
theorem z_meas (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) (i : n) :
    Measurable[ℱ t] fun ω => z t ω i := by
  induction t generalizing i with
  | zero => exact h.z0_meas i
  | succ t ih =>
    rw [var_rec_apply h.eq21]
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ fun c _ => ?_
      exact ((ih c).mono (ℱ.mono (Nat.le_succ t)) le_rfl).const_mul _
    · exact Finset.measurable_sum _ fun l _ => (h.shock.meas (t + 1) l).const_mul _

end var_Model

/-! ### Moments of the shocks -/

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

omit [Fintype k] in
/-- `E[Xε_{t+1}] = 0` for `ℱ_t`-measurable square-integrable `X` (tower property). -/
theorem var_cross_zero {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) {t : ℕ} {X : Ω → ℝ}
    (hX : Measurable[ℱ t] X) (hX2 : MemLp X 2 μ) (i : k) :
    ∫ ω, X ω * ε (t + 1) ω i ∂μ = 0 := by
  have hεi : MemLp (fun ω => ε (t + 1) ω i) 2 μ := hε.memLp (t + 1) i
  have hprod : Integrable (X * fun ω => ε (t + 1) ω i) μ := hX2.integrable_mul hεi
  have h1 := condExp_mul_of_stronglyMeasurable_left hX.stronglyMeasurable hprod
    (hεi.integrable one_le_two)
  have h2 : ∫ ω, X ω * ε (t + 1) ω i ∂μ = ∫ ω, (μ[X * fun ω => ε (t + 1) ω i | ℱ t]) ω ∂μ :=
    (integral_condExp (ℱ.le t)).symm
  have h3 : X * μ[fun ω => ε (t + 1) ω i | ℱ t] =ᵐ[μ] 0 := by
    filter_upwards [hε.mds t i] with ω hω
    simp [hω]
  rw [h2, integral_congr_ae (h1.trans h3)]
  simp

omit [Fintype k] in
/-- `Eε_{t+1} = 0`. -/
theorem var_mean_eps_zero {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) (t : ℕ) (i : k) :
    ∫ ω, ε (t + 1) ω i ∂μ = 0 := by
  rw [← integral_condExp (ℱ.le t), integral_congr_ae (hε.mds t i)]
  simp

omit [Fintype k] in
/-- `Eε_{t+1}ε'_{t+1} = I`. -/
theorem var_mom_eps {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) (t : ℕ) (i j : k) :
    ∫ ω, ε (t + 1) ω i * ε (t + 1) ω j ∂μ = if i = j then 1 else 0 := by
  rw [← integral_condExp (ℱ.le t), integral_congr_ae (hε.cvar t i j)]
  simp

omit [IsProbabilityMeasure μ] in
/-- `∫(∑ₛ wₛfₛ)g = ∑ₛ wₛ∫fₛg` for square-integrable `fₛ, g`. -/
theorem var_integral_sum_mul {ι : Type*} [Fintype ι] (w : ι → ℝ) {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ s, MemLp (f s) 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, (∑ s, w s * f s ω) * g ω ∂μ = ∑ s, w s * ∫ ω, f s ω * g ω ∂μ := by
  simp only [Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext ω
    ring
  · intro s _
    have := ((hf s).integrable_mul hg).const_mul (w s)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring

omit [IsProbabilityMeasure μ] in
/-- `∫g(∑ₛ wₛfₛ) = ∑ₛ wₛ∫gfₛ`. -/
theorem var_integral_mul_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ s, MemLp (f s) 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, g ω * (∑ s, w s * f s ω) ∂μ = ∑ s, w s * ∫ ω, g ω * f s ω ∂μ := by
  have := var_integral_sum_mul w hf hg
  simp only [mul_comm (g _)] at this ⊢
  rw [← this]

/-! ### Means -/

variable {Φ : Matrix n n ℝ} {Sg : Matrix n k ℝ} {z : ℕ → Ω → n → ℝ} {ε : ℕ → Ω → k → ℝ}

omit [DecidableEq n] in
/-- Miao, p. 47: taking expectations of (2.1), `μ_{t+1} = Φμ_t`. -/
theorem var_mean_rec (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mean μ (z (t + 1)) = Φ *ᵥ var_mean μ (z t) := by
  funext i
  have hz := h.z_memLp t
  simp only [var_mean]
  rw [var_rec_apply h.eq21, integral_add, integral_finsetSum, integral_finsetSum]
  · simp only [integral_const_mul, var_mean_eps_zero h.shock, mul_zero, Finset.sum_const_zero,
      add_zero, Matrix.mulVec, dotProduct]
    rfl
  · exact fun l _ => ((h.shock.memLp (t + 1) l).integrable one_le_two).const_mul _
  · exact fun c _ => ((hz c).integrable one_le_two).const_mul _
  · exact integrable_finsetSum _ fun c _ => ((hz c).integrable one_le_two).const_mul _
  · exact integrable_finsetSum _ fun l _ =>
      ((h.shock.memLp (t + 1) l).integrable one_le_two).const_mul _

/-- Miao, p. 47: `μ_t = Φᵗμ₀`. -/
theorem var_mean_eq (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mean μ (z t) = (Φ ^ t) *ᵥ var_mean μ (z 0) := by
  induction t with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ t ih => rw [var_mean_rec h, ih, Matrix.mulVec_mulVec, pow_succ']

/-- Miao, p. 47: if all eigenvalues of `Φ` are inside the unit circle, `μ_t → 0`; with
`μ₀ = 0`, `μ_t = 0` for all `t`. -/
theorem var_mean_tendsto_zero (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) :
    Tendsto (fun t => var_mean μ (z t)) atTop (𝓝 0) ∧
      (var_mean μ (z 0) = 0 → ∀ t, var_mean μ (z t) = 0) := by
  refine ⟨?_, fun h0 t => by rw [var_mean_eq h, h0, Matrix.mulVec_zero]⟩
  rw [show (fun t => var_mean μ (z t)) = fun t => (Φ ^ t) *ᵥ var_mean μ (z 0) from
    funext (var_mean_eq h)]
  exact tendsto_of_isStableMatrix Φ hΦ _

/-! ### Second moments -/

/-- The state and shock of date `t + 1` as one family indexed by `n ⊕ k`. -/
def var_stack (z : ℕ → Ω → n → ℝ) (ε : ℕ → Ω → k → ℝ) (t : ℕ) : n ⊕ k → Ω → ℝ :=
  Sum.elim (fun c ω => z t ω c) (fun l ω => ε (t + 1) ω l)

omit [DecidableEq n] [DecidableEq k] in
theorem var_rec_stack (hrec : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω)
    (t : ℕ) (i : n) :
    (fun ω => z (t + 1) ω i) = fun ω => ∑ s, Sum.elim (Φ i) (Sg i) s * var_stack z ε t s ω := by
  rw [var_rec_apply hrec]
  funext ω
  simp [var_stack, Fintype.sum_sum_type]

omit [DecidableEq n] [DecidableEq k] in
theorem var_rec_stack_apply (hrec : ∀ t ω, z (t + 1) ω = Φ *ᵥ z t ω + Sg *ᵥ ε (t + 1) ω)
    (t : ℕ) (i : n) (ω : Ω) :
    z (t + 1) ω i = ∑ s, Sum.elim (Φ i) (Sg i) s * var_stack z ε t s ω :=
  congrFun (var_rec_stack hrec t i) ω

omit [DecidableEq n] [IsProbabilityMeasure μ] in
theorem var_stack_memLp (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) (s : n ⊕ k) :
    MemLp (var_stack z ε t s) 2 μ := by
  rcases s with c | l
  · exact h.z_memLp t c
  · exact h.shock.memLp (t + 1) l

omit [DecidableEq n] in
/-- Miao, p. 47: the second moments satisfy `Ez_{t+1}z'_{t+1} = Φ(Ez_tz'_t)Φ' + ΣΣ'`. -/
theorem var_mom_rec (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mom μ (z (t + 1)) (z (t + 1)) = var_lyapMap Φ (Sg * Sgᵀ) (var_mom μ (z t) (z t)) := by
  ext i j
  have hst := var_stack_memLp h t
  have hzj : MemLp (fun ω => z (t + 1) ω j) 2 μ := h.z_memLp (t + 1) j
  have e1 : var_mom μ (z (t + 1)) (z (t + 1)) i j =
      ∑ s, Sum.elim (Φ i) (Sg i) s *
        ∫ ω, var_stack z ε t s ω * z (t + 1) ω j ∂μ := by
    simp only [var_mom, Matrix.of_apply]
    rw [show (fun ω => z (t + 1) ω i * z (t + 1) ω j) =
      fun ω => (∑ s, Sum.elim (Φ i) (Sg i) s * var_stack z ε t s ω) * z (t + 1) ω j from
        funext fun ω => by rw [var_rec_stack_apply h.eq21 t i ω]]
    exact var_integral_sum_mul _ hst hzj
  have e2 : ∀ s, ∫ ω, var_stack z ε t s ω * z (t + 1) ω j ∂μ =
      ∑ r, Sum.elim (Φ j) (Sg j) r * ∫ ω, var_stack z ε t s ω * var_stack z ε t r ω ∂μ := by
    intro s
    rw [show (fun ω => var_stack z ε t s ω * z (t + 1) ω j) =
      fun ω => var_stack z ε t s ω * ∑ r, Sum.elim (Φ j) (Sg j) r * var_stack z ε t r ω from
        funext fun ω => by rw [var_rec_stack_apply h.eq21 t j ω]]
    exact var_integral_mul_sum _ hst (hst s)
  have hzε : ∀ c l, ∫ ω, z t ω c * ε (t + 1) ω l ∂μ = 0 := fun c l =>
    var_cross_zero h.shock (h.z_meas t c) (h.z_memLp t c) l
  have hεz : ∀ l c, ∫ ω, ε (t + 1) ω l * z t ω c ∂μ = 0 := fun l c => by
    simp only [mul_comm (ε _ _ _)]; exact hzε c l
  rw [e1]
  simp only [e2]
  simp only [Fintype.sum_sum_type, var_stack, Sum.elim_inl, Sum.elim_inr]
  simp only [hzε, hεz, var_mom_eps h.shock, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [var_lyapMap_apply]
  simp only [var_mom, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

omit [DecidableEq n] in
/-- The second moments are the Lyapunov iterates: `Ez_tz'_t = Lᵗ(Ez₀z'₀)`. -/
theorem var_mom_iterate (h : var_Model n μ ℱ Φ Sg z ε) (t : ℕ) :
    var_mom μ (z t) (z t) = (var_lyapMap Φ (Sg * Sgᵀ))^[t] (var_mom μ (z 0) (z 0)) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [var_mom_rec h, ih, Function.iterate_succ_apply']

/-- Miao, p. 47: for stable `Φ` the second moments of every solution converge to the solution
`∑ⱼΦʲΣΣ'Φ'ʲ` of the Lyapunov equation. -/
theorem var_mom_tendsto (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (i j : n) :
    Tendsto (fun t => var_mom μ (z t) (z t) i j) atTop
      (𝓝 (var_lyapSol Φ (Sg * Sgᵀ) i j)) := by
  rw [show (fun t => var_mom μ (z t) (z t) i j) =
    fun t => ((var_lyapMap Φ (Sg * Sgᵀ))^[t] (var_mom μ (z 0) (z 0))) i j from
      funext fun t => by rw [var_mom_iterate h]]
  exact lyap_iterate_tendsto Φ hΦ _ _ i j

/-- Miao, p. 47: `C_z(j) = Ez_{t+j}z'_t = ΦʲEz_tz'_t` (the autocovariogram). -/
theorem var_autocov (h : var_Model n μ ℱ Φ Sg z ε) (t j : ℕ) :
    var_mom μ (z (t + j)) (z t) = Φ ^ j * var_mom μ (z t) (z t) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Matrix.mul_assoc, ← ih]
    ext a b
    have hst := var_stack_memLp h (t + j)
    have hzb : MemLp (fun ω => z t ω b) 2 μ := h.z_memLp t b
    have hmb : Measurable[ℱ (t + j)] fun ω => z t ω b :=
      (h.z_meas t b).mono (ℱ.mono (Nat.le_add_right t j)) le_rfl
    simp only [var_mom, Matrix.of_apply, Matrix.mul_apply]
    rw [show (fun ω => z (t + (j + 1)) ω a * z t ω b) =
      fun ω => (∑ s, Sum.elim (Φ a) (Sg a) s * var_stack z ε (t + j) s ω) * z t ω b from
        funext fun ω => by rw [← var_rec_stack_apply h.eq21 (t + j) a ω, Nat.add_assoc],
      var_integral_sum_mul _ hst hzb]
    simp only [Fintype.sum_sum_type, var_stack, Sum.elim_inl, Sum.elim_inr]
    have hz : ∀ l, ∫ ω, ε (t + j + 1) ω l * z t ω b ∂μ = 0 := fun l => by
      simp only [mul_comm (ε _ _ _)]; exact var_cross_zero h.shock hmb hzb l
    simp only [hz, mul_zero, Finset.sum_const_zero, add_zero]

/-- **Definition 2.1.1** (Miao, p. 47): `X` is covariance stationary: square integrable, constant
mean `m`, and `E(X_{t+j} − m)(X_t − m)'` depends only on the lag `j ≥ 0`. -/
def var_IsCovStationary (μ : Measure Ω) (X : ℕ → Ω → n → ℝ) : Prop :=
  (∀ t i, MemLp (fun ω => X t ω i) 2 μ) ∧ ∃ m : n → ℝ, ∃ Γ : ℕ → Matrix n n ℝ,
    (∀ t, var_mean μ (X t) = m) ∧
      ∀ t j, var_mom μ (fun ω => X (t + j) ω - m) (fun ω => X t ω - m) = Γ j

/-- **Definition 2.1.1** (Miao, p. 47), as printed ("depends only on `|t − s|`"), would force
`Γ(j)` to be symmetric, since `E(X_s − m)(X_t − m)' = (E(X_t − m)(X_s − m)')'`. For a vector
process that is false: for `Φ = [0 1/2; 0 0]`, `Σ = I`, the stationary `C(0) = I + ΦΦ'` solves
the Lyapunov equation but `C(1) = ΦC(0)` is not symmetric. -/
theorem definition_2_1_1_not_symmetric :
    let Φ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 2; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) ℝ := !![5 / 4, 0; 0, 1]
    var_lyapMap Φ 1 C = C ∧ (Φ * C)ᵀ ≠ Φ * C := by
  intro Φ C
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Φ, C, var_lyapMap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
        dotProduct, Matrix.one_apply]
  · intro hs
    have := congrFun (congrFun hs 1) 0
    simp [Φ, C, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- Miao, p. 47 (corrected): for stable `Φ`, a covariance-stationary solution of (2.1)–(2.2) has
mean `0`, `C_z(0) = ∑ⱼΦʲΣΣ'Φ'ʲ` (the unique solution of the Lyapunov equation) and
`C_z(j) = ΦʲC_z(0)`: its stationary first and second moments are uniquely determined. -/
theorem var_stationary_moments (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (hs : var_IsCovStationary μ z) :
    ∃ Γ : ℕ → Matrix n n ℝ, (∀ t, var_mean μ (z t) = 0) ∧
      (∀ t j, var_mom μ (z (t + j)) (z t) = Γ j) ∧
      Γ 0 = var_lyapSol Φ (Sg * Sgᵀ) ∧ ∀ j, Γ j = Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ) := by
  obtain ⟨-, m, Γ, hm, hΓ⟩ := hs
  have hm0 : m = 0 := by
    have hfix : ∀ t, m = (Φ ^ t) *ᵥ m := fun t => by
      have := var_mean_eq h t
      rw [hm t, hm 0] at this
      exact this
    have hlim := tendsto_of_isStableMatrix Φ hΦ m
    simp only [← hfix] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  subst hm0
  have hΓ' : ∀ t j, var_mom μ (z (t + j)) (z t) = Γ j := fun t j => by
    have := hΓ t j
    simpa only [sub_zero] using this
  have e1 : var_mom μ (z 1) (z 1) = Γ 0 := by simpa using hΓ' 1 0
  have e0 : var_mom μ (z 0) (z 0) = Γ 0 := by simpa using hΓ' 0 0
  have hC : var_lyapMap Φ (Sg * Sgᵀ) (Γ 0) = Γ 0 := by
    rw [← e0, ← var_mom_rec h 0]
    simpa using e1.trans e0.symm
  have h0 := lyap_unique Φ hΦ _ _ hC
  refine ⟨Γ, hm, hΓ', h0, fun j => ?_⟩
  rw [← hΓ' 0 j, var_autocov h 0 j, ← h0, e0]

/-- Miao, p. 47, existence: "assume `z₀` is drawn from the stationary distribution": if `Ez₀ = 0`
and `Ez₀z'₀ = ∑ⱼΦʲΣΣ'Φ'ʲ`, then `z` is covariance stationary with `C_z(j) = ΦʲC_z(0)`. -/
theorem var_stationary_of_initial (h : var_Model n μ ℱ Φ Sg z ε)
    (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (h0 : var_mean μ (z 0) = 0)
    (hC : var_mom μ (z 0) (z 0) = var_lyapSol Φ (Sg * Sgᵀ)) :
    var_IsCovStationary μ z ∧ ∀ t j,
      var_mom μ (z (t + j)) (z t) = Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ) := by
  have hS : ∀ t, var_mom μ (z t) (z t) = var_lyapSol Φ (Sg * Sgᵀ) := fun t => by
    rw [var_mom_iterate h, hC]
    exact Function.iterate_fixed (lyap_fixed Φ hΦ _) t
  have hauto : ∀ t j, var_mom μ (z (t + j)) (z t) = Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ) :=
    fun t j => by rw [var_autocov h, hS]
  refine ⟨⟨h.z_memLp, 0, fun j => Φ ^ j * var_lyapSol Φ (Sg * Sgᵀ),
    (var_mean_tendsto_zero h hΦ).2 h0, fun t j => ?_⟩, hauto⟩
  simpa only [sub_zero] using hauto t j

/-! ### Impulse responses -/

omit [DecidableEq k] in
/-- Miao, p. 47: `z_{t+j} = Φʲz_t + Σε_{t+j} + ΦΣε_{t+j−1} + ⋯ + Φ^{j−1}Σε_{t+1}`. -/
theorem var_ma_shift {x : ℕ → n → ℝ} {e : ℕ → k → ℝ}
    (hrec : ∀ t, x (t + 1) = Φ *ᵥ x t + Sg *ᵥ e (t + 1)) (t j : ℕ) :
    x (t + j) = (Φ ^ j) *ᵥ x t + ∑ i ∈ Finset.range j, (Φ ^ i * Sg) *ᵥ e (t + j - i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, hrec, ih, Finset.sum_range_succ', Matrix.mulVec_add,
      Matrix.mulVec_mulVec, ← pow_succ', Matrix.mulVec_sum]
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ', pow_zero, Matrix.one_mul]
    rw [Nat.sub_zero]
    have : ∀ i ∈ Finset.range j, (Φ ^ (i + 1) * Sg) *ᵥ e (t + j + 1 - (i + 1)) =
        (Φ ^ (i + 1) * Sg) *ᵥ e (t + j - i) := fun i _ => by
      rw [show t + j + 1 - (i + 1) = t + j - i by omega]
    rw [Finset.sum_congr rfl this]
    abel

omit [DecidableEq k] in
/-- Miao, p. 48: the finite-horizon moving-average representation
`z_{t+1} = Φ^{t+1}z₀ + ∑_{j≤t}ΦʲΣε_{t+1−j}`. -/
theorem var_ma {x : ℕ → n → ℝ} {e : ℕ → k → ℝ}
    (hrec : ∀ t, x (t + 1) = Φ *ᵥ x t + Sg *ᵥ e (t + 1)) (t : ℕ) :
    x (t + 1) = (Φ ^ (t + 1)) *ᵥ x 0 + ∑ j ∈ Finset.range (t + 1), (Φ ^ j * Sg) *ᵥ e (t + 1 - j)
    := by
  simpa using var_ma_shift hrec 0 (t + 1)

omit [DecidableEq k] in
/-- Miao, p. 48: for stable `Φ` the initial condition washes out, `Φ^{t+1}z₀ → 0`, so `z_{t+1}`
is asymptotically `∑ⱼΦʲΣε_{t+1−j}`. -/
theorem var_ma_initial_tendsto (hΦ : IsStableMatrix (Φ.map Complex.ofRealHom)) (x0 : n → ℝ) :
    Tendsto (fun t => (Φ ^ (t + 1)) *ᵥ x0) atTop (𝓝 0) :=
  (tendsto_add_atTop_iff_nat 1).2 (tendsto_of_isStableMatrix Φ hΦ x0)

omit [DecidableEq k] in
/-- Miao, p. 48, the impulse response: if `ε'` differs from `ε` only by a shock `v` at date
`s + 1`, and `z, z'` solve (2.1) from the same `z₀`, then `z'_{s+1+j} − z_{s+1+j} = ΦʲΣv`; and
`z' = z` before date `s + 1`. -/
theorem var_impulse_response {x x' : ℕ → n → ℝ} {e e' : ℕ → k → ℝ}
    (hrec : ∀ t, x (t + 1) = Φ *ᵥ x t + Sg *ᵥ e (t + 1))
    (hrec' : ∀ t, x' (t + 1) = Φ *ᵥ x' t + Sg *ᵥ e' (t + 1)) (h0 : x' 0 = x 0) (s : ℕ)
    (v : k → ℝ) (he : ∀ t, e' t = if t = s + 1 then e t + v else e t) :
    (∀ t ≤ s, x' t = x t) ∧ ∀ j, x' (s + 1 + j) - x (s + 1 + j) = (Φ ^ j * Sg) *ᵥ v := by
  have hbefore : ∀ t ≤ s, x' t = x t := by
    intro t ht
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [hrec, hrec', ih (by omega), he]
      simp only [show t + 1 ≠ s + 1 by omega, ↓reduceIte]
  refine ⟨hbefore, fun j => ?_⟩
  induction j with
  | zero =>
    rw [add_zero, hrec, hrec', hbefore s le_rfl, he]
    simp [Matrix.mulVec_add]
  | succ j ih =>
    rw [← Nat.add_assoc, hrec, hrec', he]
    simp only [show s + 1 + j + 1 ≠ s + 1 by omega, ↓reduceIte]
    rw [show Φ *ᵥ x' (s + 1 + j) + Sg *ᵥ e (s + 1 + j + 1) -
        (Φ *ᵥ x (s + 1 + j) + Sg *ᵥ e (s + 1 + j + 1)) =
        Φ *ᵥ (x' (s + 1 + j) - x (s + 1 + j)) by rw [Matrix.mulVec_sub]; abel, ih,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']

/-! ### White noise (Definition 2.3.3, p. 56) -/

/-- **Definition 2.3.3** (Miao, p. 56): `X` is a white noise with variance `Σ_w`: square
integrable, `EX_t = 0`, `EX_tX'_s = 0` for `s ≠ t` and `= Σ_w` for `s = t`. -/
def var_IsWhiteNoise (μ : Measure Ω) (X : ℕ → Ω → k → ℝ) (Sw : Matrix k k ℝ) : Prop :=
  (∀ t i, MemLp (fun ω => X t ω i) 2 μ) ∧ (∀ t i, ∫ ω, X t ω i ∂μ = 0) ∧
    ∀ t s, var_mom μ (X t) (X s) = if t = s then Sw else 0

omit [Fintype k] [DecidableEq k] in
/-- `E|X| ≤ (EX²)^{1/2}` on a probability space. -/
theorem var_integral_abs_le_sqrt {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ ω, |X ω| ∂μ ≤ Real.sqrt (∫ ω, X ω * X ω ∂μ) := by
  have habs : MemLp (fun ω => |X ω|) 2 μ := hX.abs
  have hv := ProbabilityTheory.variance_nonneg (fun ω => |X ω|) μ
  rw [ProbabilityTheory.variance_eq_sub habs] at hv
  have hsq : ∫ ω, ((fun ω => |X ω|) ^ 2) ω ∂μ = ∫ ω, X ω * X ω ∂μ := by
    congr 1
    funext ω
    simp [sq]
  rw [hsq] at hv
  exact Real.le_sqrt_of_sq_le (by linarith)

omit [Fintype k] [DecidableEq k] in
/-- Miao, p. 56: "a white noise process is stable" (Definition 2.3.1): `E|X_{t,i}| ≤ (Σ_w)ᵢᵢ^{1/2}`,
so `max_i E|X_{t,i}| < M` for all `t`. -/
theorem whiteNoise_stable [Finite k] {X : ℕ → Ω → k → ℝ} {Sw : Matrix k k ℝ}
    (hX : var_IsWhiteNoise μ X Sw) :
    ∃ M, 0 < M ∧ ∀ t i, ∫ ω, |X t ω i| ∂μ < M := by
  cases nonempty_fintype k
  refine ⟨∑ i, Real.sqrt (Sw i i) + 1, by positivity, fun t i => ?_⟩
  have hd : ∫ ω, X t ω i * X t ω i ∂μ = Sw i i := by
    have := congrFun (congrFun (hX.2.2 t t) i) i
    simpa [var_mom] using this
  have h1 := var_integral_abs_le_sqrt (hX.1 t i)
  rw [hd] at h1
  have h2 : Real.sqrt (Sw i i) ≤ ∑ j, Real.sqrt (Sw j j) :=
    Finset.single_le_sum (f := fun j => Real.sqrt (Sw j j)) (fun j _ => Real.sqrt_nonneg _)
      (Finset.mem_univ i)
  linarith

omit [Fintype k] [DecidableEq k] in
/-- Miao, p. 56, in the `L¹` setting: the classes of a white noise form a stable process
(`IsStableProc`, Definition 2.3.1). -/
theorem whiteNoise_stable_L1 [Finite k] {X : ℕ → Ω → k → ℝ} {Sw : Matrix k k ℝ}
    (hX : var_IsWhiteNoise μ X Sw) :
    IsStableProc fun t i => ((hX.1 t i).integrable one_le_two).toL1 (fun ω => X t ω i) := by
  obtain ⟨M, hM, hb⟩ := whiteNoise_stable hX
  refine ⟨M, hM, fun t i => ?_⟩
  rw [l1_norm_eq_integral_abs]
  refine lt_of_eq_of_lt (integral_congr_ae ?_) (hb t i)
  filter_upwards [Integrable.coeFn_toL1 ((hX.1 t i).integrable one_le_two)] with ω hω
  rw [hω]

omit [Fintype k] in
/-- Miao, p. 56: "the process `{ε_{t+1}}` satisfying (2.2) is a white noise" (with `Σ = I`):
`Eε_{t+1} = 0`, `Eε_{t+1}ε'_{s+1} = 0` for `s ≠ t` (tower property), `Eε_{t+1}ε'_{t+1} = I`. -/
theorem mds_whiteNoise {ε : ℕ → Ω → k → ℝ} (hε : var_ShockMDS μ ℱ ε) :
    var_IsWhiteNoise μ (fun t => ε (t + 1)) 1 := by
  refine ⟨fun t i => hε.memLp (t + 1) i, fun t i => var_mean_eps_zero hε t i, fun t s => ?_⟩
  ext i j
  simp only [var_mom, Matrix.of_apply]
  rcases lt_trichotomy t s with hts | hts | hts
  · have hm : Measurable[ℱ s] fun ω => ε (t + 1) ω i :=
      (hε.meas (t + 1) i).mono (ℱ.mono (by omega)) le_rfl
    rw [var_cross_zero hε hm (hε.memLp (t + 1) i) j]
    simp [hts.ne]
  · subst hts
    rw [var_mom_eps hε t i j]
    simp [Matrix.one_apply]
  · have hm : Measurable[ℱ t] fun ω => ε (s + 1) ω j :=
      (hε.meas (s + 1) j).mono (ℱ.mono (by omega)) le_rfl
    rw [show (fun ω => ε (t + 1) ω i * ε (s + 1) ω j) =
      fun ω => ε (s + 1) ω j * ε (t + 1) ω i by funext ω; ring,
      var_cross_zero hε hm (hε.memLp (s + 1) j) i]
    simp [hts.ne']

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Counterexamples for §2.1 and p. 56

Miao, p. 47 and p. 56. The probability space is the infinite product `Ω = ℕ → Fin N` of uniform
laws on `Fin N` (`vex_P N`, `Measure.infinitePi`), whose coordinates are independent
(`iIndepFun_infinitePi`); the filtration is `Filtration.piLE`, `F_t = σ(ω₀, …, ω_t)`.

* **A white noise need not satisfy (2.2)** (p. 56): on `ℕ → Fin 8`, `ε_{2j} = f(ω_j)` with `f`
  taking the values `−1, 0, 1` with probabilities `3/8, 1/4, 3/8`, and
  `ε_{2j+1} = 2(ε_{2j}² − 3/4)`. Then `{ε_t}` is a white noise with variance `3/4`
  (`whiteNoise_example`), but `ε₁` is a function of `ε₀`, so for every filtration to which `ε` is
  adapted (for instance `piLE`) `E₀ε₁ = ε₁ ≠ 0` (`whiteNoise_not_mds`).
* **(2.1)–(2.2) do not determine the law of `z`** (p. 47, "unique stationary distribution"): on
  `ℕ → Fin 4`, with `Φ = 0`, `Σ = 1`, the shocks `ε_t = a(ω_t)`, `a` uniform on
  `{−√2, 0, 0, √2}`, and `ε_t = b(ω_t)`, `b` uniform on `{−1, 1, 1, −1}`, both satisfy (2.2) for
  `piLE` and both `z_t = ε_t` are covariance-stationary solutions of (2.1)–(2.2) with the same
  first and second moments, but `Ez_t⁴ = 2` in the first and `1` in the second
  (`stationary_law_not_unique`). What (2.1)–(2.2) do determine for stable `Φ` is the stationary
  mean and autocovariances (`var_stationary_moments`).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Miao.RationalExpectations

open scoped Matrix

/-- The uniform law on `Fin N`. -/
noncomputable abbrev vex_unif (N : ℕ) [NeZero N] : Measure (Fin N) :=
  (PMF.uniformOfFintype (Fin N)).toMeasure

/-- The product of independent uniform coordinates on `ℕ → Fin N`. -/
noncomputable abbrev vex_P (N : ℕ) [NeZero N] : Measure (ℕ → Fin N) :=
  Measure.infinitePi fun _ => vex_unif N

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem vex_coord_measurable (F : Fin N → ℝ) (j : ℕ) :
    Measurable fun ω : ℕ → Fin N => F (ω j) :=
  (measurable_of_finite F).comp (measurable_pi_apply j)

/-- `E F(ω_j) = (∑ᵢF(i))/N`. -/
theorem vex_integral_coord (F : Fin N → ℝ) (j : ℕ) :
    ∫ ω, F (ω j) ∂vex_P N = (∑ i, F i) / N := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => vex_unif N) j
  rw [show (∫ ω, F (ω j) ∂vex_P N) = ∫ x, F x ∂(Measure.map (Function.eval j) (vex_P N)) from
    (integral_map hmp.measurable.aemeasurable
      (measurable_of_finite F).aestronglyMeasurable).symm, hmp.map_eq, PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply, div_eq_inv_mul, Finset.mul_sum]

/-- Independent coordinates: `E F(ω_j)G(ω_{j'}) = EF(ω_j) EG(ω_{j'})` for `j ≠ j'`. -/
theorem vex_integral_coord2 (F G : Fin N → ℝ) {j j' : ℕ} (hne : j ≠ j') :
    ∫ ω, F (ω j) * G (ω j') ∂vex_P N = (∑ i, F i) / N * ((∑ i, G i) / N) := by
  have hind : IndepFun (fun ω : ℕ → Fin N => ω j) (fun ω => ω j') (vex_P N) :=
    (iIndepFun_infinitePi (P := fun _ => vex_unif N) (X := fun _ x => x)
      (fun _ => measurable_id)).indepFun hne
  have h2 := hind.comp (measurable_of_finite F) (measurable_of_finite G)
  have h3 := h2.integral_fun_mul_eq_mul_integral
    (vex_coord_measurable F j).aestronglyMeasurable
    (vex_coord_measurable G j').aestronglyMeasurable
  simp only [Function.comp_apply] at h3
  rw [h3, vex_integral_coord, vex_integral_coord]

theorem vex_memLp (F : Fin N → ℝ) (j : ℕ) : MemLp (fun ω : ℕ → Fin N => F (ω j)) 2 (vex_P N) :=
  MemLp.of_bound (vex_coord_measurable F j).aestronglyMeasurable (∑ i, |F i|)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i => |F i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ _))

omit [NeZero N] in
/-- The coordinate `ω_j` is `F_t`-measurable for `j ≤ t`. -/
theorem vex_coord_meas_piLE (F : Fin N → ℝ) {j t : ℕ} (h : j ≤ t) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => Fin N) t] fun ω => F (ω j) := by
  have h1 : Measurable[Filtration.piLE (X := fun _ : ℕ => Fin N) t]
      (Preorder.restrictLe (π := fun _ : ℕ => Fin N) t) := Measurable.of_comap_le le_rfl
  exact (measurable_of_finite F).comp
    ((measurable_pi_apply (⟨j, Set.mem_Iic.2 h⟩ : Set.Iic t)).comp h1)

/-- The coordinate `ω_{t+1}` is independent of `F_t = σ(ω₀, …, ω_t)`. -/
theorem vex_indep (F : Fin N → ℝ) (t : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → Fin N => F (ω (t + 1))) inferInstance)
      (Filtration.piLE (X := fun _ : ℕ => Fin N) t) (vex_P N) := by
  have hi : iIndepFun (fun (i : ℕ) (ω : ℕ → Fin N) => ω i) (vex_P N) :=
    iIndepFun_infinitePi (P := fun _ => vex_unif N) (X := fun _ x => x) (fun _ => measurable_id)
  have h := hi.indepFun_finset {t + 1} (Finset.Iic t) (by simp)
    (fun i => measurable_pi_apply i)
  have hm : Measurable fun v : (({t + 1} : Finset ℕ) → Fin N) => F (v ⟨t + 1, by simp⟩) :=
    (measurable_of_finite F).comp (measurable_pi_apply _)
  have h2 := h.comp hm measurable_id
  rw [IndepFun_iff_Indep] at h2
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact h2

/-- `E_tF(ω_{t+1}) = EF(ω_{t+1})` for the filtration `piLE`. -/
theorem vex_condExp (F : Fin N → ℝ) (t : ℕ) :
    (vex_P N)[fun ω => F (ω (t + 1)) | Filtration.piLE (X := fun _ : ℕ => Fin N) t] =ᵐ[vex_P N]
      fun _ => (∑ i, F i) / N := by
  have h := condExp_indep_eq (vex_coord_measurable F (t + 1)).comap_le
    (Filtration.le _ t) (Measurable.of_comap_le le_rfl).stronglyMeasurable (vex_indep F t)
  rw [vex_integral_coord] at h
  exact h

/-! ### A white noise that does not satisfy (2.2) -/

/-- `f` takes the values `−1, 0, 1` with probabilities `3/8, 1/4, 3/8`. -/
def vex_f : Fin 8 → ℝ := ![-1, -1, -1, 0, 0, 1, 1, 1]

/-- `g = 2(f² − 3/4)`. -/
noncomputable def vex_g : Fin 8 → ℝ := fun i => 2 * (vex_f i ^ 2 - 3 / 4)

/-- `ε_{2j} = f(ω_j)`, `ε_{2j+1} = g(ω_j)`. -/
noncomputable def vex_F (t : ℕ) : Fin 8 → ℝ := if t % 2 = 0 then vex_f else vex_g

/-- The white noise of the counterexample (Miao, p. 56). -/
noncomputable def vex_wn (t : ℕ) (ω : ℕ → Fin 8) (_ : Unit) : ℝ := vex_F t (ω (t / 2))

theorem vex_sum_F (t : ℕ) : ∑ i, vex_F t i = 0 := by
  unfold vex_F
  split_ifs
  · simp [Fin.sum_univ_eight, vex_f]
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
    norm_num

theorem vex_sum_FF (t : ℕ) : ∑ i, vex_F t i * vex_F t i = 6 := by
  unfold vex_F
  split_ifs
  · simp [Fin.sum_univ_eight, vex_f]
    norm_num
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
    norm_num

theorem vex_sum_FG {t s : ℕ} (hts : t ≠ s) (hj : t / 2 = s / 2) :
    ∑ i, vex_F t i * vex_F s i = 0 := by
  have h2 : t % 2 ≠ s % 2 := by omega
  unfold vex_F
  split_ifs with h1 h3 h3
  · omega
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
  · simp [Fin.sum_univ_eight, vex_g, vex_f]
  · omega

theorem vex_g_ne_zero (i : Fin 8) : vex_g i ≠ 0 := by
  fin_cases i <;> norm_num [vex_g, vex_f]

/-- Definition 2.3.3 (Miao, p. 56): `vex_wn` is a white noise with variance `3/4`. -/
theorem whiteNoise_example :
    var_IsWhiteNoise (vex_P 8) vex_wn (Matrix.of fun _ _ => (3 / 4 : ℝ)) := by
  refine ⟨fun t _ => vex_memLp (vex_F t) (t / 2), fun t _ => ?_, fun t s => ?_⟩
  · simp only [vex_wn]
    rw [vex_integral_coord, vex_sum_F, zero_div]
  · split_ifs with hts
    · subst hts
      ext i j
      change ∫ ω, vex_F t (ω (t / 2)) * vex_F t (ω (t / 2)) ∂vex_P 8 = (3 / 4 : ℝ)
      have := vex_integral_coord (N := 8) (fun x => vex_F t x * vex_F t x) (t / 2)
      rw [this, vex_sum_FF]
      norm_num
    · ext i j
      change ∫ ω, vex_F t (ω (t / 2)) * vex_F s (ω (s / 2)) ∂vex_P 8 = (0 : ℝ)
      by_cases hj : t / 2 = s / 2
      · have := vex_integral_coord (N := 8) (fun x => vex_F t x * vex_F s x) (t / 2)
        rw [← hj, this, vex_sum_FG hts hj, zero_div]
      · rw [vex_integral_coord2 _ _ hj, vex_sum_F, zero_div, zero_mul]

/-- Miao, p. 56: "a white noise may not satisfy (2.2)": for every filtration to which the white
noise `vex_wn` is adapted, `E₀ε₁ ≠ 0`, because `ε₁ = 2(ε₀² − 3/4)` is `F₀`-measurable and never
zero. Adapted filtrations exist, e.g. `piLE` (`vex_wn_adapted`). -/
theorem whiteNoise_not_mds (ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → Fin 8)))
    (hℱ : ∀ t, Measurable[ℱ t] fun ω => vex_wn t ω ()) :
    ¬ (vex_P 8)[fun ω => vex_wn 1 ω () | ℱ 0] =ᵐ[vex_P 8] 0 := by
  intro h
  have he : (fun ω : ℕ → Fin 8 => vex_wn 1 ω ()) =
      fun ω => 2 * ((vex_wn 0 ω ()) ^ 2 - 3 / 4) := by
    funext ω
    simp [vex_wn, vex_F, vex_g]
  have hm : Measurable[ℱ 0] fun ω => vex_wn 1 ω () := by
    rw [he]
    exact (((hℱ 0).pow_const 2).sub_const _).const_mul _
  have hint : Integrable (fun ω => vex_wn 1 ω ()) (vex_P 8) :=
    (vex_memLp (vex_F 1) 0).integrable one_le_two
  rw [condExp_of_stronglyMeasurable (ℱ.le 0) hm.stronglyMeasurable hint] at h
  obtain ⟨ω, hω⟩ := h.exists
  exact vex_g_ne_zero (ω 0) (by simpa [vex_wn, vex_F] using hω)

/-- The white noise `vex_wn` is adapted to `piLE`. -/
theorem vex_wn_adapted (t : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => Fin 8) t] fun ω => vex_wn t ω () :=
  vex_coord_meas_piLE (vex_F t) (Nat.div_le_self t 2)

/-! ### (2.1)–(2.2) do not pin down the stationary law -/

/-- The shock `ε_t = F(ω_t)`. -/
def vex_sh (F : Fin 4 → ℝ) (t : ℕ) (ω : ℕ → Fin 4) (_ : Unit) : ℝ := F (ω t)

/-- With `∑F = 0` and `∑F² = 4`, `ε_t = F(ω_t)` satisfies (2.2) for `piLE`. -/
theorem vex_sh_mds {F : Fin 4 → ℝ} (h1 : ∑ i, F i = 0) (h2 : ∑ i, F i * F i = 4) :
    var_ShockMDS (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) (vex_sh F) := by
  refine ⟨fun t _ => vex_memLp F t, fun t _ => vex_coord_meas_piLE F le_rfl, fun t _ => ?_,
    fun t _ _ => ?_⟩
  · refine (vex_condExp F t).trans (Eventually.of_forall fun ω => ?_)
    simp [h1]
  · refine (vex_condExp (N := 4) (fun x => F x * F x) t).trans
      (Eventually.of_forall fun ω => ?_)
    simp only [h2]
    norm_num

theorem vex_zero_stable :
    IsStableMatrix ((0 : Matrix Unit Unit ℝ).map Complex.ofRealHom) := by
  refine isStableMatrix_of_tendsto 0 fun v => tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [zero_pow (by omega), Matrix.zero_mulVec]

/-- With `Φ = 0`, `z_t = ε_t` solves (2.1) with `Σ = 1`. -/
theorem vex_model {F : Fin 4 → ℝ} (h1 : ∑ i, F i = 0) (h2 : ∑ i, F i * F i = 4) :
    var_Model Unit (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) 0 1 (vex_sh F)
      (vex_sh F) := by
  refine ⟨fun t ω => ?_, fun _ => vex_memLp F 0, fun _ => vex_coord_meas_piLE F le_rfl,
    vex_sh_mds h1 h2⟩
  simp [Matrix.zero_mulVec, Matrix.one_mulVec]

theorem vex_lyapSol_zero : var_lyapSol (0 : Matrix Unit Unit ℝ) (1 * 1ᵀ) = 1 := by
  ext i j
  simp only [var_lyapSol, Matrix.of_apply]
  rw [tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
  simp

/-- The two shock laws. -/
noncomputable def vex_a : Fin 4 → ℝ := ![-Real.sqrt 2, 0, 0, Real.sqrt 2]

/-- The second shock law. -/
def vex_b : Fin 4 → ℝ := ![-1, 1, 1, -1]

theorem vex_a_sums :
    ∑ i, vex_a i = 0 ∧ ∑ i, vex_a i * vex_a i = 4 ∧ ∑ i, vex_a i ^ 4 = 8 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  refine ⟨by simp [Fin.sum_univ_four, vex_a], ?_, ?_⟩
  · simp [Fin.sum_univ_four, vex_a, h2]
    norm_num
  · have h4' : (-Real.sqrt 2) ^ 4 = 4 := by rw [Even.neg_pow (by decide), h4]
    simp [Fin.sum_univ_four, vex_a, h4, h4']
    norm_num

theorem vex_b_sums :
    ∑ i, vex_b i = 0 ∧ ∑ i, vex_b i * vex_b i = 4 ∧ ∑ i, vex_b i ^ 4 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_four, vex_b] <;> norm_num

/-- Miao, p. 47 (corrected): "if all eigenvalues of `Φ` are inside the unit circle then `{z_t}`
has a unique stationary distribution" fails under (2.1)–(2.2) alone. On one probability space
with one filtration, `Φ = 0` (stable), `Σ = 1`, the shocks `vex_sh vex_a` and `vex_sh vex_b`
both satisfy (2.2); both `z_t = ε_t` are covariance-stationary solutions with the same mean `0`
and autocovariances, yet `Ez_t⁴ = 2` for the first and `Ez_t⁴ = 1` for the second, so the laws of
`z_t` differ. -/
theorem stationary_law_not_unique :
    IsStableMatrix ((0 : Matrix Unit Unit ℝ).map Complex.ofRealHom) ∧
      var_Model Unit (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) 0 1 (vex_sh vex_a)
        (vex_sh vex_a) ∧
      var_Model Unit (vex_P 4) (Filtration.piLE (X := fun _ : ℕ => Fin 4)) 0 1 (vex_sh vex_b)
        (vex_sh vex_b) ∧
      var_IsCovStationary (vex_P 4) (vex_sh vex_a) ∧
      var_IsCovStationary (vex_P 4) (vex_sh vex_b) ∧
      ∀ t, ∫ ω, vex_sh vex_a t ω () ^ 4 ∂vex_P 4 = 2 ∧ ∫ ω, vex_sh vex_b t ω () ^ 4 ∂vex_P 4 = 1
    := by
  obtain ⟨a1, a2, a4⟩ := vex_a_sums
  obtain ⟨b1, b2, b4⟩ := vex_b_sums
  have ha := vex_model a1 a2
  have hb := vex_model b1 b2
  have hcov : ∀ {F : Fin 4 → ℝ}, ∑ i, F i = 0 → ∑ i, F i * F i = 4 →
      var_IsCovStationary (vex_P 4) (vex_sh F) := fun {F} h1 h2 => by
    refine (var_stationary_of_initial (vex_model h1 h2) vex_zero_stable ?_ ?_).1
    · funext i
      simp only [var_mean, vex_sh]
      rw [vex_integral_coord, h1]
      simp
    · rw [vex_lyapSol_zero]
      ext i j
      obtain rfl : i = j := Subsingleton.elim _ _
      rw [Matrix.one_apply_eq]
      change ∫ ω, F (ω 0) * F (ω 0) ∂vex_P 4 = (1 : ℝ)
      have := vex_integral_coord (N := 4) (fun x => F x * F x) 0
      rw [this, h2]
      norm_num
  refine ⟨vex_zero_stable, ha, hb, hcov a1 a2, hcov b1 b2, fun t => ⟨?_, ?_⟩⟩
  · have := vex_integral_coord (N := 4) (fun x => vex_a x ^ 4) t
    simp only [vex_sh]
    rw [this, a4]
    norm_num
  · have := vex_integral_coord (N := 4) (fun x => vex_b x ^ 4) t
    simp only [vex_sh]
    rw [this, b4]
    norm_num

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Scalar linear rational expectations models

Miao, §2.2, pp. 48–52. Abstract setting: a `CondExpSystem ℝ V` on a complete normed space `V`
of scalar random variables (for instance `condExpSystemL1_real`); a process is `x : ℕ → V`,
adapted if `E_t x_t = x_t` (`sre_IsAdapted`), stable if bounded (`sre_IsBounded`, which is
Definition 2.3.1 for one variable, `sre_isStableProc_iff`).

* Lag operators (p. 48): `L^{-j}X_t = E_tX_{t+j}` (`sre_lagInv`), the rule
  `LʲE_tX_{t+i} = E_tX_{t+i−j}` (`sre_lagE`), `LʲE_tX_{t+j} = X_t` (`sre_lagE_self`),
  `L^{-i}L^{-j} = L^{-(i+j)}` (`sre_lagInv_lagInv`, law of iterated expectations).
* `E_tx_{t+1} = bx_t + f_t`, `|b| > 1`, `f` bounded adapted: the forward solution
  `x*_t = −∑ⱼ b^{−j−1}E_tf_{t+j}` (`sre_fwd`) converges, is adapted, bounded and solves
  (`sre_fwd_adapted`, `sre_fwd_bound`, `sre_fwd_rec`); with `f = cz` this is (2.3) (`eq_2_3`).
  It is the only stable adapted solution (`eq_2_3_unique`). Bubbles (2.4): `x* + B` solves iff
  `E_tB_{t+1} = bB_t`, and every adapted solution is of this form (`eq_2_4`,
  `eq_2_4_every`). The transversality condition (2.5) holds for every stable process
  (`eq_2_5_of_bounded`), forces `x = x*` (`eq_2_5_rules_out_bubbles`) and fails for every
  nonzero adapted bubble (`eq_2_5_bubble_fails`).
* Example 2.2.1 (Blanchard–Watson): `E_td_{t+j} = ρʲd_t` (`example_2_2_1_Ed`), the fundamental
  price `d_t/(R − ρ)` (`example_2_2_1_fundamental`, `example_2_2_1_general`); the bursting
  bubble satisfies (2.4) (`example_2_2_1_bubble`, concrete: functions on `Ω` with `μ[·|ℱ t]`;
  `example_2_2_1_bubble_L1` in `L¹`), and the coin's conditional mean is `q` when it is
  independent of `ℱ_t` (`example_2_2_1_coin`).
* (2.6)–(2.9): with `a = λ₁ + λ₂`, `b = −λ₁λ₂`, `|λ₁| < 1 < |λ₂|`, the process
  `x_t = λ₁x_{t−1} − (c/λ₂)∑ⱼλ₂^{−j}E_tz_{t+j}` (`sre_second`, `eq_2_9`) is the unique stable
  adapted solution of (2.6) on the dates `t ≥ 1` with the given `x₀` (`eq_2_6_solution`,
  `eq_2_6_unique`).
* (2.10): the reduction (`eq_2_10_reduce`), and the book's recipe made precise: if `λ₁, λ₂` are
  the roots of `λ² = (a₀ + a₁)λ + a₂` with `|λ₁| < 1 < |λ₂|`, and `a₀ ≠ λ₁`, there is exactly
  one stable adapted solution with the given `x₀` (`eq_2_10_solution`, `eq_2_10_unique`); for
  `a₀ = λ₁` uniqueness fails (`eq_2_10_indeterminate`).
* §2.2.2 (p. 51): the guess `x_t = Gx_{t−1} + Hz_t` solves (2.6) iff a coefficient identity
  holds (`uc_iff`); matching coefficients is sufficient (`uc_sufficient`) and necessary when
  the guess works for two initial values and `z ≢ 0` (`uc_necessary`); with `G = λ₁`,
  `H = c/(G + ρ − a)` is well defined (`uc_denominator_ne_zero`) and the guess is the
  lag-operator solution (`uc_eq_lag_solution`).

Departures from the book (see the docstrings):
* "Bounded" in the book means Definition 2.3.1 (`sup_t E|z_t| < ∞`); all processes are
  explicitly adapted.
* (2.6) and (2.10) involve `x_{t−1}`, so they are imposed for `t ≥ 1` with `x₀` given.
* Example 2.2.1 and §2.2.2 assume `ε` IID with mean zero; what is used is only the
  martingale-difference property `E_tε_{t+1} = 0` (hence `E_td_{t+1} = ρd_t`).
* (2.10): the book says the reduced equation "is similar to (2.7)", but it contains `x_{t−1}`,
  not `E_{t−1}x_{t−1}`; the book's final step solves for `x_t` from (2.10), whose coefficient
  on `x_t` is `a₀ − λ₁` once `E_tx_{t+1} = λ₁x_t + ω_t` is substituted, so the condition is
  `a₀ ≠ λ₁` (not `a₀ ≠ 0`); for `a₀ = λ₁` there are sunspot solutions.
-/

open Filter Topology MeasureTheory

namespace Miao.RationalExpectations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Scalar processes -/

/-- A scalar process `x` is adapted: `E_tx_t = x_t` (Miao, p. 45). -/
def sre_IsAdapted (E : CondExpSystem ℝ V) (x : ℕ → V) : Prop :=
  ∀ t, E.E t (x t) = x t

/-- A scalar process is bounded (stable, Definition 2.3.1). -/
def sre_IsBounded (x : ℕ → V) : Prop :=
  ∃ M, ∀ t, ‖x t‖ ≤ M

omit [NormedSpace ℝ V] in
/-- **Definition 2.3.1** (Miao, p. 52) for one variable: stable iff bounded. -/
theorem sre_isStableProc_iff (x : ℕ → V) :
    IsStableProc (fun t (_ : Unit) => x t) ↔ sre_IsBounded x := by
  constructor
  · rintro ⟨M, -, hM⟩
    exact ⟨M, fun t => (hM t ()).le⟩
  · rintro ⟨M, hM⟩
    refine ⟨|M| + 1, by positivity, fun t _ => ?_⟩
    linarith [hM t, le_abs_self M]

theorem sre_isAdaptedV_iff (E : CondExpSystem ℝ V) (x : ℕ → V) :
    IsAdaptedV E (fun t (_ : Unit) => x t) ↔ sre_IsAdapted E x :=
  ⟨fun h t => h t (), fun h t _ => h t⟩

theorem sre_adapted_succ (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x)
    (t : ℕ) : E.E (t + 1) (x t) = x t := by
  rw [← hx t, E.tower_ge_apply (Nat.le_succ t), hx t]

theorem sre_adapted_le (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x)
    {s t : ℕ} (h : s ≤ t) : E.E t (x s) = x s := by
  rw [← hx s, E.tower_ge_apply h, hx s]

/-- The conditional expectations from date `k` on: `E'_t = E_{t+k}`. -/
def sre_shiftSys (E : CondExpSystem ℝ V) (k : ℕ) : CondExpSystem ℝ V where
  E t := E.E (t + k)
  norm_le t := E.norm_le (t + k)
  tower_le s t h := E.tower_le _ _ (by omega)
  tower_ge s t h := E.tower_ge _ _ (by omega)

theorem sre_shiftSys_E (E : CondExpSystem ℝ V) (k t : ℕ) :
    (sre_shiftSys E k).E t = E.E (t + k) := rfl

/-! ### Lag operators -/

/-- The inverse lag operator (Miao, p. 48): `L^{-j}X_t = E_tX_{t+j}`. -/
def sre_lagInv (E : CondExpSystem ℝ V) (j : ℕ) (x : ℕ → V) : ℕ → V :=
  fun t => E.E t (x (t + j))

/-- The lag operator (Miao, p. 48): `LʲX_t = X_{t−j}` (for `t ≥ j`). -/
def sre_lag (j : ℕ) (x : ℕ → V) : ℕ → V :=
  fun t => x (t - j)

/-- The rule of Miao, p. 48: `Lʲ` applied to `E_tX_{t+i}` is `E_tX_{t+i−j}` (for `j ≤ i`): the
lag shifts the date of the variable, not the date of the expectation. -/
def sre_lagE (E : CondExpSystem ℝ V) (j i : ℕ) (x : ℕ → V) : ℕ → V :=
  fun t => E.E t (x (t + i - j))

/-- Miao, p. 48: `LʲE_tX_{t+j} = E_tX_t = X_t` for an adapted `X`, which is why
`L^{-j}X_t = E_tX_{t+j}` is the inverse of `Lʲ`. -/
theorem sre_lagE_self (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x) (j : ℕ) :
    sre_lagE E j j x = x := by
  funext t
  simp only [sre_lagE, Nat.add_sub_cancel]
  exact hx t

/-- Miao, p. 48: `L⁰X = X` for adapted `X`. -/
theorem sre_lagInv_zero (E : CondExpSystem ℝ V) {x : ℕ → V} (hx : sre_IsAdapted E x) :
    sre_lagInv E 0 x = x := by
  funext t
  exact hx t

/-- Miao, p. 48: `L^{-i}L^{-j}X_t = E_tE_{t+i}X_{t+i+j} = L^{-(i+j)}X_t`. -/
theorem sre_lagInv_lagInv (E : CondExpSystem ℝ V) (i j : ℕ) (x : ℕ → V) :
    sre_lagInv E i (sre_lagInv E j x) = sre_lagInv E (i + j) x := by
  funext t
  simp only [sre_lagInv, Nat.add_assoc]
  exact E.tower_le_apply (Nat.le_add_right t i) _

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Miao, p. 48: lags compose additively, `Lⁱ(LʲX)_t = X_{t−i−j}`. -/
theorem sre_lag_lag (i j : ℕ) (x : ℕ → V) : sre_lag i (sre_lag j x) = sre_lag (i + j) x := by
  funext t
  simp only [sre_lag]
  congr 1
  omega

/-- Miao, p. 48: `E_tx_{t+1} = bx_t + cz_t` is `(L^{-1} − b)x_t = cz_t`. -/
theorem sre_lag_form (E : CondExpSystem ℝ V) (b c : ℝ) (x z : ℕ → V) :
    (∀ t, E.E t (x (t + 1)) = b • x t + c • z t) ↔
      sre_lagInv E 1 x - b • x = c • z := by
  constructor
  · intro h
    funext t
    simp only [Pi.sub_apply, Pi.smul_apply, sre_lagInv, h t]
    abel
  · intro h t
    have := congrFun h t
    simp only [Pi.sub_apply, Pi.smul_apply, sre_lagInv] at this
    rw [← this]
    abel

/-! ### The first-order equation `E_tx_{t+1} = bx_t + f_t` -/

/-- Iterating `E_te_{t+1} = be_t` with the law of iterated expectations:
`E_te_{t+k} = bᵏe_t`. -/
theorem sre_iter (E : CondExpSystem ℝ V) {b : ℝ} {e : ℕ → V} (he : sre_IsAdapted E e)
    (hrec : ∀ t, E.E t (e (t + 1)) = b • e t) (k t : ℕ) :
    E.E t (e (t + k)) = b ^ k • e t := by
  induction k with
  | zero => simpa using he t
  | succ k ih =>
    rw [← Nat.add_assoc, ← E.tower_le_apply (Nat.le_add_right t k), hrec, map_smul, ih,
      smul_smul, pow_succ, mul_comm]

/-- A bounded adapted solution of `E_te_{t+1} = be_t` with `|b| > 1` is zero. -/
theorem sre_bubble_bounded_zero (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {e : ℕ → V}
    (he : sre_IsAdapted E e) (hrec : ∀ t, E.E t (e (t + 1)) = b • e t)
    (hbd : sre_IsBounded e) : e = 0 := by
  obtain ⟨M, hM⟩ := hbd
  funext t
  by_contra hne
  have hpos : 0 < ‖e t‖ := norm_pos_iff.2 hne
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / ‖e t‖) hb
  have h1 : |b| ^ k * ‖e t‖ ≤ M := by
    calc |b| ^ k * ‖e t‖ = ‖E.E t (e (t + k))‖ := by
          rw [sre_iter E he hrec, norm_smul, norm_pow, Real.norm_eq_abs]
      _ ≤ ‖e (t + k)‖ := E.norm_apply_le _ _
      _ ≤ M := hM _
  rw [div_lt_iff₀ hpos] at hk
  linarith

/-- Two bounded adapted solutions of `E_tx_{t+1} = bx_t + f_t`, `|b| > 1`, coincide. -/
theorem sre_unique_of_bounded (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f x y : ℕ → V}
    (hx : sre_IsAdapted E x) (hy : sre_IsAdapted E y) (hxb : sre_IsBounded x)
    (hyb : sre_IsBounded y) (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t)
    (hys : ∀ t, E.E t (y (t + 1)) = b • y t + f t) : x = y := by
  have h := sre_bubble_bounded_zero E hb (e := x - y)
    (fun t => by simp only [Pi.sub_apply, map_sub, hx t, hy t])
    (fun t => by simp only [Pi.sub_apply, map_sub, hxs, hys, smul_sub]; abel)
    (by
      obtain ⟨M, hM⟩ := hxb
      obtain ⟨N, hN⟩ := hyb
      exact ⟨M + N, fun t => (norm_sub_le _ _).trans (add_le_add (hM t) (hN t))⟩)
  exact funext fun t => sub_eq_zero.1 (congrFun h t)

/-- The forward (fundamental) solution `x*_t = −∑ⱼ b^{−j−1}E_tf_{t+j}` of
`E_tx_{t+1} = bx_t + f_t`. -/
noncomputable def sre_fwd (E : CondExpSystem ℝ V) (b : ℝ) (f : ℕ → V) : ℕ → V :=
  fun t => -∑' j : ℕ, (b⁻¹) ^ (j + 1) • E.E t (f (t + j))

theorem sre_inv_abs_lt_one {b : ℝ} (hb : 1 < |b|) : |b⁻¹| < 1 := by
  rw [abs_inv]
  exact inv_lt_one_of_one_lt₀ hb

/-- The terms of the forward sum are dominated by a geometric series. -/
theorem sre_fwd_term_le (E : CondExpSystem ℝ V) (b : ℝ) {f : ℕ → V} {M : ℝ}
    (hM : ∀ t, ‖f t‖ ≤ M) (t j : ℕ) :
    ‖(b⁻¹) ^ (j + 1) • E.E t (f (t + j))‖ ≤ M * |b⁻¹| * |b⁻¹| ^ j := by
  rw [norm_smul, norm_pow, Real.norm_eq_abs, pow_succ]
  calc |b⁻¹| ^ j * |b⁻¹| * ‖E.E t (f (t + j))‖ ≤ |b⁻¹| ^ j * |b⁻¹| * M := by
        gcongr
        exact (E.norm_apply_le _ _).trans (hM _)
    _ = M * |b⁻¹| * |b⁻¹| ^ j := by ring

theorem sre_fwd_summable [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f : ℕ → V} {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M) (t : ℕ) :
    Summable fun j : ℕ => (b⁻¹) ^ (j + 1) • E.E t (f (t + j)) :=
  Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg _) (sre_inv_abs_lt_one hb)).mul_left _)
    (sre_fwd_term_le E b hM t)

/-- The forward solution is bounded: `‖x*_t‖ ≤ M|b|^{-1}/(1 − |b|^{-1})`. -/
theorem sre_fwd_bound (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f : ℕ → V} {M : ℝ}
    (hM : ∀ t, ‖f t‖ ≤ M) (t : ℕ) :
    ‖sre_fwd E b f t‖ ≤ M * |b⁻¹| * (1 - |b⁻¹|)⁻¹ := by
  rw [sre_fwd, norm_neg]
  exact tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (abs_nonneg _) (sre_inv_abs_lt_one hb)).mul_left _)
    (sre_fwd_term_le E b hM t)

theorem sre_fwd_isBounded (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f : ℕ → V}
    (hf : sre_IsBounded f) : sre_IsBounded (sre_fwd E b f) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨_, sre_fwd_bound E hb hM⟩

/-- The forward solution is adapted. -/
theorem sre_fwd_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f : ℕ → V} (hf : sre_IsBounded f) : sre_IsAdapted E (sre_fwd E b f) := by
  obtain ⟨M, hM⟩ := hf
  intro t
  simp only [sre_fwd, map_neg]
  rw [(E.E t).map_tsum (sre_fwd_summable E hb hM t)]
  simp only [map_smul, E.idem]

/-- The forward solution solves `E_tx_{t+1} = bx_t + f_t`. -/
theorem sre_fwd_rec [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) (t : ℕ) :
    E.E t (sre_fwd E b f (t + 1)) = b • sre_fwd E b f t + f t := by
  obtain ⟨M, hM⟩ := hf
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, abs_zero] at hb
    linarith
  have hs := sre_fwd_summable E hb hM t
  have hs1 := sre_fwd_summable E hb hM (t + 1)
  simp only [sre_fwd, map_neg]
  rw [(E.E t).map_tsum hs1, hs.tsum_eq_zero_add]
  simp only [map_smul, E.tower_le_apply (Nat.le_succ t), smul_neg, smul_add, Nat.add_zero,
    hfa t, zero_add, pow_one, smul_smul, mul_inv_cancel₀ hb0, one_smul]
  have hs2 : Summable fun j : ℕ => (b⁻¹) ^ (j + 1 + 1) • E.E t (f (t + (j + 1))) :=
    (summable_nat_add_iff 1).2 hs
  have h2 : (∑' j : ℕ, (b⁻¹) ^ (j + 1) • E.E t (f (t + 1 + j))) =
      b • ∑' j : ℕ, (b⁻¹) ^ (j + 1 + 1) • E.E t (f (t + (j + 1))) := by
    rw [← hs2.tsum_const_smul b]
    congr 1
    funext j
    simp only [smul_smul, pow_succ (b⁻¹) (j + 1)]
    rw [show t + 1 + j = t + (j + 1) by omega]
    congr 1
    field_simp
  rw [h2]
  abel

/-- **(2.3)** (Miao, p. 49): for `|b| > 1` and a stable adapted `z`, the fundamental solution
`x_t = −c∑ⱼ b^{−j−1}E_tz_{t+j}` of `E_tx_{t+1} = bx_t + cz_t` is a stable adapted solution. -/
theorem eq_2_3 [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) (c : ℝ)
    {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) :
    (∀ t, sre_fwd E b (c • z) t = -(c • ∑' j : ℕ, (b⁻¹) ^ (j + 1) • E.E t (z (t + j)))) ∧
    sre_IsAdapted E (sre_fwd E b (c • z)) ∧ sre_IsBounded (sre_fwd E b (c • z)) ∧
    ∀ t, E.E t (sre_fwd E b (c • z) (t + 1)) = b • sre_fwd E b (c • z) t + c • z t := by
  have hcza : sre_IsAdapted E (c • z) := fun t => by simp [hza t]
  have hczb : sre_IsBounded (c • z) := by
    obtain ⟨M, hM⟩ := hz
    exact ⟨|c| * M, fun t => by
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]; gcongr; exact hM t⟩
  obtain ⟨M, hM⟩ := hz
  refine ⟨fun t => ?_, sre_fwd_adapted E hb hczb, sre_fwd_isBounded E hb hczb,
    sre_fwd_rec E hb hcza hczb⟩
  simp only [sre_fwd, Pi.smul_apply, map_smul]
  rw [← (sre_fwd_summable E hb hM t).tsum_const_smul c]
  congr 2
  funext j
  rw [smul_comm]

/-- **(2.3)** (Miao, p. 49), uniqueness: the fundamental solution is the only stable adapted
solution. -/
theorem eq_2_3_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f x : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) (hx : sre_IsAdapted E x)
    (hxb : sre_IsBounded x) (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t) :
    x = sre_fwd E b f :=
  sre_unique_of_bounded E hb hx (sre_fwd_adapted E hb hf) hxb (sre_fwd_isBounded E hb hf) hxs
    (sre_fwd_rec E hb hfa hf)

/-- **(2.4)** (Miao, p. 49), with any particular solution `p`: `p + B` solves
`E_tx_{t+1} = bx_t + f_t` iff the bubble satisfies `E_tB_{t+1} = bB_t`. -/
theorem eq_2_4_of_particular (E : CondExpSystem ℝ V) (b : ℝ) {f p B : ℕ → V}
    (hp : ∀ t, E.E t (p (t + 1)) = b • p t + f t) :
    (∀ t, E.E t ((p + B) (t + 1)) = b • (p + B) t + f t) ↔
      ∀ t, E.E t (B (t + 1)) = b • B t := by
  constructor
  · intro h t
    have := h t
    simp only [Pi.add_apply, map_add, hp t, smul_add] at this
    calc E.E t (B (t + 1)) = (b • p t + f t + E.E t (B (t + 1))) - (b • p t + f t) := by abel
      _ = b • B t := by rw [this]; abel
  · intro h t
    simp only [Pi.add_apply, map_add, hp t, h t, smul_add]
    abel

/-- **(2.4)** (Miao, p. 49): `x* + B` solves iff `E_tB_{t+1} = bB_t`. -/
theorem eq_2_4 [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {f B : ℕ → V}
    (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) :
    (∀ t, E.E t ((sre_fwd E b f + B) (t + 1)) = b • (sre_fwd E b f + B) t + f t) ↔
      ∀ t, E.E t (B (t + 1)) = b • B t :=
  eq_2_4_of_particular E b (sre_fwd_rec E hb hfa hf)

/-- Miao, p. 49: every adapted solution is `x* + B` with an adapted bubble `B`
(`E_tB_{t+1} = bB_t`). -/
theorem eq_2_4_every [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|)
    {f x : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f) (hx : sre_IsAdapted E x)
    (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t) :
    ∃ B, x = sre_fwd E b f + B ∧ sre_IsAdapted E B ∧ ∀ t, E.E t (B (t + 1)) = b • B t := by
  refine ⟨x - sre_fwd E b f, by abel, fun t => ?_, ?_⟩
  · simp only [Pi.sub_apply, map_sub, hx t, sre_fwd_adapted E hb hf t]
  · refine (eq_2_4 E hb hfa hf).1 ?_
    simpa using hxs

/-- The transversality (no-bubble) condition **(2.5)** (Miao, p. 49):
`lim_{T→∞} b^{−T}E_tx_{t+T} = 0` for every `t`. -/
def sre_Transversality (E : CondExpSystem ℝ V) (b : ℝ) (x : ℕ → V) : Prop :=
  ∀ t, Tendsto (fun T : ℕ => (b⁻¹) ^ T • E.E t (x (t + T))) atTop (𝓝 0)

/-- Miao, p. 49: every stable process satisfies (2.5) when `|b| > 1`. -/
theorem eq_2_5_of_bounded (E : CondExpSystem ℝ V) {b : ℝ} (hb : 1 < |b|) {x : ℕ → V}
    (hx : sre_IsBounded x) : sre_Transversality E b x := by
  obtain ⟨M, hM⟩ := hx
  intro t
  have hlim : Tendsto (fun T : ℕ => M * |b⁻¹| ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _)
      (sre_inv_abs_lt_one hb)).const_mul M
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [norm_smul, norm_pow, Real.norm_eq_abs, mul_comm]
  gcongr
  exact (E.norm_apply_le _ _).trans (hM _)

/-- An adapted bubble satisfying (2.5) is zero. -/
theorem sre_bubble_tvc_zero (E : CondExpSystem ℝ V) {b : ℝ} (hb0 : b ≠ 0) {e : ℕ → V}
    (he : sre_IsAdapted E e) (hrec : ∀ t, E.E t (e (t + 1)) = b • e t)
    (htv : sre_Transversality E b e) : e = 0 := by
  funext t
  have hconst : (fun T : ℕ => (b⁻¹) ^ T • E.E t (e (t + T))) = fun _ => e t := by
    funext T
    rw [sre_iter E he hrec, smul_smul, ← mul_pow, inv_mul_cancel₀ hb0, one_pow, one_smul]
  have := htv t
  rw [hconst] at this
  exact tendsto_nhds_unique tendsto_const_nhds this

/-- Miao, p. 49: a nonzero adapted bubble violates (2.5): `b^{−T}E_tB_{t+T} = B_t`. -/
theorem eq_2_5_bubble_fails (E : CondExpSystem ℝ V) {b : ℝ} (hb0 : b ≠ 0) {B : ℕ → V}
    (hB : sre_IsAdapted E B) (hrec : ∀ t, E.E t (B (t + 1)) = b • B t) (hne : B ≠ 0) :
    ¬ sre_Transversality E b B :=
  fun h => hne (sre_bubble_tvc_zero E hb0 hB hrec h)

/-- Two adapted solutions of `E_tx_{t+1} = bx_t + f_t` that satisfy (2.5) coincide. -/
theorem sre_unique_of_tvc (E : CondExpSystem ℝ V) {b : ℝ} (hb0 : b ≠ 0) {f x y : ℕ → V}
    (hx : sre_IsAdapted E x) (hy : sre_IsAdapted E y) (hxt : sre_Transversality E b x)
    (hyt : sre_Transversality E b y) (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t)
    (hys : ∀ t, E.E t (y (t + 1)) = b • y t + f t) : x = y := by
  have h := sre_bubble_tvc_zero E hb0 (e := x - y)
    (fun t => by simp only [Pi.sub_apply, map_sub, hx t, hy t])
    (fun t => by simp only [Pi.sub_apply, map_sub, hxs, hys, smul_sub]; abel)
    (fun t => by
      have := (hxt t).sub (hyt t)
      simpa only [Pi.sub_apply, map_sub, smul_sub, sub_zero] using this)
  exact funext fun t => sub_eq_zero.1 (congrFun h t)

/-- **(2.5)** (Miao, p. 49): "if we impose the transversality condition, bubbles cannot
exist": an adapted solution satisfying (2.5) is the fundamental solution. -/
theorem eq_2_5_rules_out_bubbles [CompleteSpace V] (E : CondExpSystem ℝ V) {b : ℝ}
    (hb : 1 < |b|) {f x : ℕ → V} (hfa : sre_IsAdapted E f) (hf : sre_IsBounded f)
    (hx : sre_IsAdapted E x) (hxt : sre_Transversality E b x)
    (hxs : ∀ t, E.E t (x (t + 1)) = b • x t + f t) : x = sre_fwd E b f := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, abs_zero] at hb
    linarith
  exact sre_unique_of_tvc E hb0 hx (sre_fwd_adapted E hb hf) hxt
    (eq_2_5_of_bounded E hb (sre_fwd_isBounded E hb hf)) hxs (sre_fwd_rec E hb hfa hf)

/-- The forward sum when `E_tf_{t+1} = ρf_t` with `|ρ| < |b|`: `x*_t = (ρ − b)^{−1}f_t`
(no boundedness needed: the terms are `b^{−j−1}ρʲf_t`). -/
theorem sre_fwd_ar1 (E : CondExpSystem ℝ V) {b ρ : ℝ} (hρb : |ρ| < |b|) {f : ℕ → V}
    (hfa : sre_IsAdapted E f) (hf : ∀ t, E.E t (f (t + 1)) = ρ • f t) (t : ℕ) :
    sre_fwd E b f t = (ρ - b)⁻¹ • f t := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, abs_zero] at hρb
    linarith [abs_nonneg ρ]
  have hr : |ρ * b⁻¹| < 1 := by
    rw [abs_mul, abs_inv]
    have hpos : 0 < |b| := by linarith [abs_nonneg ρ]
    rw [mul_inv_lt_iff₀ hpos, one_mul]
    exact hρb
  have hterm : (fun j : ℕ => (b⁻¹) ^ (j + 1) • E.E t (f (t + j))) =
      fun j => (b⁻¹ * (ρ * b⁻¹) ^ j) • f t := by
    funext j
    rw [sre_iter E hfa hf, smul_smul, mul_pow, pow_succ]
    congr 1
    ring
  have hsum : HasSum (fun j : ℕ => b⁻¹ * (ρ * b⁻¹) ^ j) (b⁻¹ * (1 - ρ * b⁻¹)⁻¹) :=
    (hasSum_geometric_of_abs_lt_one hr).mul_left _
  simp only [sre_fwd, hterm]
  rw [(hsum.smul_const (f t)).tsum_eq, ← neg_smul]
  congr 1
  have h1 : (1 - ρ * b⁻¹) ≠ 0 := by
    intro h
    have : ρ * b⁻¹ = 1 := by linarith
    rw [this, abs_one] at hr
    exact lt_irrefl _ hr
  have h2 : ρ - b ≠ 0 := by
    intro h
    have : ρ = b := by linarith
    rw [this] at hρb
    exact lt_irrefl _ hρb
  have h3 : b - ρ ≠ 0 := by
    intro h
    apply h2
    linarith
  field_simp
  ring

/-! ### Example 2.2.1 (Blanchard and Watson): abstract part -/

/-- Example 2.2.1 (Miao, p. 49): `d_t = ρd_{t−1} + ε_t` with `E_tε_{t+1} = 0` gives
`E_td_{t+j} = ρʲd_t`. The book assumes `ε` IID with mean zero; only the martingale-difference
property `E_tε_{t+1} = 0` is used. -/
theorem example_2_2_1_Ed (E : CondExpSystem ℝ V) {ρ : ℝ} {d ε : ℕ → V}
    (hd : sre_IsAdapted E d) (hrec : ∀ t, d (t + 1) = ρ • d t + ε (t + 1))
    (hε : ∀ t, E.E t (ε (t + 1)) = 0) (j t : ℕ) : E.E t (d (t + j)) = ρ ^ j • d t :=
  sre_iter E hd (fun t => by rw [hrec, map_add, hε, add_zero, map_smul, hd]) j t

/-- Example 2.2.1 (Miao, p. 49): the fundamental price `p_t = d_t/(R − ρ)` solves
`p_t = (E_tp_{t+1} + d_t)/R` and is the fundamental solution `∑ⱼ R^{−j−1}E_td_{t+j}`
(written as `sre_fwd E R (−d)`). -/
theorem example_2_2_1_fundamental (E : CondExpSystem ℝ V) {R ρ : ℝ} (hR : 1 < R)
    (hρ : |ρ| < 1) {d ε : ℕ → V} (hd : sre_IsAdapted E d)
    (hrec : ∀ t, d (t + 1) = ρ • d t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0) :
    (∀ t, (R - ρ)⁻¹ • d t = R⁻¹ • (E.E t ((R - ρ)⁻¹ • d (t + 1)) + d t)) ∧
    ∀ t, sre_fwd E R (-d) t = (R - ρ)⁻¹ • d t := by
  have hEd : ∀ t, E.E t (d (t + 1)) = ρ • d t := fun t => by
    simpa using example_2_2_1_Ed E hd hrec hε 1 t
  have hRρ : R - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    intro h; linarith
  constructor
  · intro t
    rw [map_smul, hEd, smul_smul]
    have hR0 : R ≠ 0 := by positivity
    have hk : R⁻¹ * ((R - ρ)⁻¹ * ρ + 1) = (R - ρ)⁻¹ := by
      field_simp
      ring
    calc (R - ρ)⁻¹ • d t = (R⁻¹ * ((R - ρ)⁻¹ * ρ + 1)) • d t := by rw [hk]
      _ = R⁻¹ • (((R - ρ)⁻¹ * ρ) • d t + d t) := by rw [mul_smul, add_smul, one_smul]
  · intro t
    have hρR : |ρ| < |R| := by rw [abs_of_pos (show (0 : ℝ) < R by linarith)]; linarith
    rw [sre_fwd_ar1 E hρR (f := -d) (fun t => by simp [hd t]) (fun t => by
      simp [hEd t]) t]
    simp only [Pi.neg_apply, smul_neg, ← neg_smul]
    congr 1
    rw [← inv_neg, neg_sub]

/-- Example 2.2.1 (Miao, pp. 49–50): the general adapted solution of `p_t = (E_tp_{t+1} + d_t)/R`
is `p_t = d_t/(R − ρ) + B_t` with `E_tB_{t+1} = RB_t`, and with `d` stable the fundamental price
is the only stable adapted one; a transversality condition like (2.5) rules out bubbles. -/
theorem example_2_2_1_general [CompleteSpace V] (E : CondExpSystem ℝ V) {R ρ : ℝ} (hR : 1 < R)
    (hρ : |ρ| < 1) {d ε p : ℕ → V} (hd : sre_IsAdapted E d)
    (hrec : ∀ t, d (t + 1) = ρ • d t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0)
    (hp : sre_IsAdapted E p) (hps : ∀ t, p t = R⁻¹ • (E.E t (p (t + 1)) + d t)) :
    (∃ B, p = (fun t => (R - ρ)⁻¹ • d t) + B ∧ ∀ t, E.E t (B (t + 1)) = R • B t) ∧
    (sre_IsBounded d → sre_Transversality E R p → p = fun t => (R - ρ)⁻¹ • d t) ∧
    (sre_IsBounded d → sre_IsBounded p → p = fun t => (R - ρ)⁻¹ • d t) := by
  have hR0 : R ≠ 0 := by positivity
  have hRabs : 1 < |R| := by rw [abs_of_pos (by linarith)]; exact hR
  have hsol : ∀ t, E.E t (p (t + 1)) = R • p t + (-d) t := fun t => by
    rw [hps t, smul_smul, mul_inv_cancel₀ hR0, one_smul, Pi.neg_apply]; abel
  obtain ⟨hfund, hfwd⟩ := example_2_2_1_fundamental E hR hρ hd hrec hε
  have hpart : ∀ t, E.E t ((fun t => (R - ρ)⁻¹ • d t) (t + 1)) =
      R • (fun t => (R - ρ)⁻¹ • d t) t + (-d) t := fun t => by
    have h := hfund t
    simp only [Pi.neg_apply]
    conv_rhs => rw [h, smul_smul, mul_inv_cancel₀ hR0, one_smul]
    abel
  have hda : sre_IsAdapted E (-d) := fun t => by simp [hd t]
  refine ⟨⟨p - fun t => (R - ρ)⁻¹ • d t, by abel, ?_⟩, fun hdb htv => ?_, fun hdb hpb => ?_⟩
  · refine (eq_2_4_of_particular E R (p := fun s => (R - ρ)⁻¹ • d s) hpart).1 ?_
    simpa using hsol
  · have hnb : sre_IsBounded (-d) := by
      obtain ⟨M, hM⟩ := hdb; exact ⟨M, fun t => by simpa using hM t⟩
    rw [eq_2_5_rules_out_bubbles E hRabs hda hnb hp htv hsol]
    funext t; exact hfwd t
  · have hnb : sre_IsBounded (-d) := by
      obtain ⟨M, hM⟩ := hdb; exact ⟨M, fun t => by simpa using hM t⟩
    rw [eq_2_3_unique E hRabs hda hnb hp hpb hsol]
    funext t; exact hfwd t

/-! ### Boundedness of a stable backward recursion -/

omit [NormedSpace ℝ V] in
/-- If `‖x_{t+1}‖ ≤ |λ|‖x_t‖ + U` with `|λ| < 1`, then `‖x_t‖ ≤ ‖x₀‖ + U/(1 − |λ|)`. -/
theorem sre_bounded_of_rec {x : ℕ → V} {lam U : ℝ} (hl : |lam| < 1) (hU : 0 ≤ U)
    (h : ∀ t, ‖x (t + 1)‖ ≤ |lam| * ‖x t‖ + U) (t : ℕ) :
    ‖x t‖ ≤ ‖x 0‖ + U / (1 - |lam|) := by
  have h1 : 0 < 1 - |lam| := by linarith
  have hq : 0 ≤ U / (1 - |lam|) := div_nonneg hU h1.le
  induction t with
  | zero => linarith
  | succ t ih =>
    have hk : |lam| * (U / (1 - |lam|)) + U = U / (1 - |lam|) := by
      field_simp
      ring
    calc ‖x (t + 1)‖ ≤ |lam| * ‖x t‖ + U := h t
      _ ≤ |lam| * (‖x 0‖ + U / (1 - |lam|)) + U := by gcongr
      _ = |lam| * ‖x 0‖ + (|lam| * (U / (1 - |lam|)) + U) := by ring
      _ ≤ 1 * ‖x 0‖ + U / (1 - |lam|) := by
          rw [hk]; gcongr
      _ = ‖x 0‖ + U / (1 - |lam|) := by ring

theorem sre_smul_isBounded {x : ℕ → V} (c : ℝ) (hx : sre_IsBounded x) :
    sre_IsBounded (c • x) := by
  obtain ⟨M, hM⟩ := hx
  exact ⟨|c| * M, fun t => by
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs]; gcongr; exact hM t⟩

theorem sre_smul_isAdapted (E : CondExpSystem ℝ V) {x : ℕ → V} (c : ℝ)
    (hx : sre_IsAdapted E x) : sre_IsAdapted E (c • x) := fun t => by simp [hx t]

/-! ### The second-order equation (2.6) -/

/-- **(2.6)** (Miao, p. 50): `E_tx_{t+1} = ax_t + bx_{t−1} + cz_t`, imposed for `t ≥ 1` (it involves
`x_{t−1}`; `x₀` is given), written at date `t + 1`. -/
def sre_IsSol26 (E : CondExpSystem ℝ V) (a b c : ℝ) (z x : ℕ → V) : Prop :=
  ∀ t, E.E (t + 1) (x (t + 2)) = a • x (t + 1) + b • x t + c • z (t + 1)

/-- The lag-operator solution of (2.6) (Miao, p. 50): `x_t = λ₁x_{t−1} + u_t` with
`u = −c∑ⱼλ₂^{−j−1}E_tz_{t+j}`, the forward solution of `E_tu_{t+1} = λ₂u_t + cz_t`. -/
noncomputable def sre_second (E : CondExpSystem ℝ V) (lam1 lam2 c : ℝ) (z : ℕ → V) (x0 : V) :
    ℕ → V
  | 0 => x0
  | t + 1 => lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1)

/-- **(2.9)** (Miao, p. 50): the forward part is `−(c/λ₂)∑ⱼλ₂^{−j}E_tz_{t+j}`, so
`x_t = λ₁x_{t−1} − (c/λ₂)∑ⱼλ₂^{−j}E_tz_{t+j}`. -/
theorem eq_2_9 [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 : ℝ} (hl2 : 1 < |lam2|)
    (c : ℝ) {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) (x0 : V) (t : ℕ) :
    sre_second E lam1 lam2 c z x0 (t + 1) = lam1 • sre_second E lam1 lam2 c z x0 t -
      (c / lam2) • ∑' j : ℕ, (lam2⁻¹) ^ j • E.E (t + 1) (z (t + 1 + j)) := by
  obtain ⟨M, hM⟩ := hz
  have hs := sre_fwd_summable E hl2 hM (t + 1)
  have hs0 : Summable fun j : ℕ => (lam2⁻¹) ^ j • E.E (t + 1) (z (t + 1 + j)) := by
    have := hs.const_smul lam2
    refine this.congr fun j => ?_
    have h0 : lam2 ≠ 0 := by
      intro h; rw [h, abs_zero] at hl2; linarith
    rw [smul_smul, pow_succ, ← mul_assoc, mul_comm lam2, mul_assoc, mul_inv_cancel₀ h0,
      mul_one]
  rw [sre_second, (eq_2_3 E hl2 c hza ⟨M, hM⟩).1, sub_eq_add_neg]
  congr 1
  congr 1
  rw [← hs0.tsum_const_smul, ← hs.tsum_const_smul]
  congr 1
  funext j
  rw [smul_smul, smul_smul, pow_succ, div_eq_mul_inv]
  congr 1
  ring

theorem sre_second_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 : ℝ}
    (hl2 : 1 < |lam2|) (c : ℝ) {z : ℕ → V} (hz : sre_IsBounded z) {x0 : V}
    (hx0 : E.E 0 x0 = x0) : sre_IsAdapted E (sre_second E lam1 lam2 c z x0) := by
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    simp only [sre_second, map_add, map_smul]
    rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih,
      sre_fwd_adapted E hl2 (sre_smul_isBounded c hz) (t + 1)]

/-- Miao, (2.6)–(2.9), p. 50: with `a = λ₁ + λ₂`, `b = −λ₁λ₂` (the characteristic roots of
Section 1.3), `|λ₁| < 1 < |λ₂|` and `z` stable and adapted, the lag-operator process is a stable
adapted solution of (2.6) on the dates `t ≥ 1` with the given `x₀`. -/
theorem eq_2_6_solution [CompleteSpace V] (E : CondExpSystem ℝ V) {a b c lam1 lam2 : ℝ}
    (ha : a = lam1 + lam2) (hb : b = -(lam1 * lam2)) (hl1 : |lam1| < 1) (hl2 : 1 < |lam2|)
    {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x0 : V}
    (hx0 : E.E 0 x0 = x0) :
    sre_second E lam1 lam2 c z x0 0 = x0 ∧ sre_IsAdapted E (sre_second E lam1 lam2 c z x0) ∧
      sre_IsBounded (sre_second E lam1 lam2 c z x0) ∧
      sre_IsSol26 E a b c z (sre_second E lam1 lam2 c z x0) := by
  have hczb := sre_smul_isBounded c hz
  have hXa := sre_second_adapted E hl2 c hz (lam1 := lam1) hx0
  refine ⟨rfl, hXa, ?_, fun t => ?_⟩
  · obtain ⟨U, hU⟩ := sre_fwd_isBounded E hl2 hczb
    have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
    refine ⟨_, sre_bounded_of_rec hl1 hU0 (fun t => ?_)⟩
    calc ‖sre_second E lam1 lam2 c z x0 (t + 1)‖
        = ‖lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1)‖ := rfl
      _ ≤ ‖lam1 • sre_second E lam1 lam2 c z x0 t‖ + ‖sre_fwd E lam2 (c • z) (t + 1)‖ :=
          norm_add_le _ _
      _ ≤ |lam1| * ‖sre_second E lam1 lam2 c z x0 t‖ + U := by
          rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hU _
  · have h1 : sre_second E lam1 lam2 c z x0 (t + 2) =
        lam1 • sre_second E lam1 lam2 c z x0 (t + 1) + sre_fwd E lam2 (c • z) (t + 1 + 1) := rfl
    have h2 : sre_second E lam1 lam2 c z x0 (t + 1) =
        lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1) := rfl
    have hrec := sre_fwd_rec E hl2 (sre_smul_isAdapted E c hza) hczb (t + 1)
    rw [h1, map_add, map_smul, hXa (t + 1), hrec, Pi.smul_apply, h2, ha, hb]
    module

/-- Miao, (2.6)–(2.9), p. 50, uniqueness: the lag-operator process is the only stable adapted
solution of (2.6) (dates `t ≥ 1`) with the given `x₀`. -/
theorem eq_2_6_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {a b c lam1 lam2 : ℝ}
    (ha : a = lam1 + lam2) (hb : b = -(lam1 * lam2)) (hl2 : 1 < |lam2|) {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x : ℕ → V} (hxa : sre_IsAdapted E x)
    (hxb : sre_IsBounded x) (hxs : sre_IsSol26 E a b c z x) :
    x = sre_second E lam1 lam2 c z (x 0) := by
  set u := sre_fwd E lam2 (c • z) with hu
  have hczb := sre_smul_isBounded c hz
  have hcza := sre_smul_isAdapted E c hza
  set E' := sre_shiftSys E 1
  have hv : (fun t => x (t + 1) - lam1 • x t) = fun t => u (t + 1) := by
    refine sre_unique_of_bounded E' hl2 (f := fun t => c • z (t + 1)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro t
      change E.E (t + 1) _ = _
      rw [map_sub, map_smul, hxa (t + 1), sre_adapted_succ E hxa t]
    · intro t
      exact sre_fwd_adapted E hl2 hczb (t + 1)
    · obtain ⟨M, hM⟩ := hxb
      exact ⟨M + |lam1| * M, fun t => (norm_sub_le _ _).trans (add_le_add (hM _)
        (by rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hM t))⟩
    · obtain ⟨M, hM⟩ := sre_fwd_isBounded E hl2 hczb
      exact ⟨M, fun t => hM _⟩
    · intro t
      change E.E (t + 1) _ = _
      rw [map_sub, map_smul, hxs t, hxa (t + 1), ha, hb]
      module
    · intro t
      change E.E (t + 1) _ = _
      exact sre_fwd_rec E hl2 hcza hczb (t + 1)
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    have := congrFun hv t
    change x (t + 1) = lam1 • sre_second E lam1 lam2 c z (x 0) t + u (t + 1)
    rw [← ih, ← this]
    abel

/-! ### The equation (2.10) -/

/-- **(2.10)** (Miao, p. 51): `E_tx_{t+1} = a₀x_t + a₁E_{t−1}x_t + a₂x_{t−1} + cz_t`, for `t ≥ 1`,
written at date `t + 1`. -/
def sre_IsSol210 (E : CondExpSystem ℝ V) (a0 a1 a2 c : ℝ) (z x : ℕ → V) : Prop :=
  ∀ t, E.E (t + 1) (x (t + 2)) =
    a0 • x (t + 1) + a1 • E.E t (x (t + 1)) + a2 • x t + c • z (t + 1)

/-- Miao, p. 51: taking `E_{t−1}` of (2.10) gives
`E_{t−1}x_{t+1} = (a₀ + a₁)E_{t−1}x_t + a₂x_{t−1} + cE_{t−1}z_t`. -/
theorem eq_2_10_reduce (E : CondExpSystem ℝ V) {a0 a1 a2 c : ℝ} {z x : ℕ → V}
    (hxa : sre_IsAdapted E x) (hxs : sre_IsSol210 E a0 a1 a2 c z x) (t : ℕ) :
    E.E t (x (t + 2)) = (a0 + a1) • E.E t (x (t + 1)) + a2 • x t + c • E.E t (z (t + 1)) := by
  have := congrArg (E.E t) (hxs t)
  rw [E.tower_le_apply (Nat.le_succ t)] at this
  rw [this]
  simp only [map_add, map_smul, E.idem, hxa t, add_smul]

/-- The forcing `c E_tz_{t+1}` of the reduced forward equation. -/
noncomputable def sre_force210 (E : CondExpSystem ℝ V) (c : ℝ) (z : ℕ → V) : ℕ → V :=
  fun s => c • E.E s (z (s + 1))

theorem sre_force210_adapted (E : CondExpSystem ℝ V) (c : ℝ) (z : ℕ → V) :
    sre_IsAdapted E (sre_force210 E c z) := fun s => by simp [sre_force210, E.idem]

theorem sre_force210_bounded (E : CondExpSystem ℝ V) (c : ℝ) {z : ℕ → V}
    (hz : sre_IsBounded z) : sre_IsBounded (sre_force210 E c z) := by
  obtain ⟨M, hM⟩ := hz
  exact ⟨|c| * M, fun s => by
    rw [sre_force210, norm_smul, Real.norm_eq_abs]
    gcongr
    exact (E.norm_apply_le _ _).trans (hM _)⟩

/-- The solution of (2.10) built as the book describes (Miao, p. 51): `ω = E_tx_{t+1} − λ₁x_t`
is the forward solution of `E_tω_{t+1} = λ₂ω_t + cE_tz_{t+1}`, and (2.10) is then solved for
`x_t`: `x_{t+1} = λ₁x_t + (a₀ − λ₁)^{−1}(ω_{t+1} − a₁ω_t − cz_{t+1})`. -/
noncomputable def sre_sol210 (E : CondExpSystem ℝ V) (lam1 lam2 a0 a1 c : ℝ) (z : ℕ → V)
    (x0 : V) : ℕ → V
  | 0 => x0
  | t + 1 => lam1 • sre_sol210 E lam1 lam2 a0 a1 c z x0 t +
      (a0 - lam1)⁻¹ • (sre_fwd E lam2 (sre_force210 E c z) (t + 1) -
        a1 • sre_fwd E lam2 (sre_force210 E c z) t - c • z (t + 1))

theorem sre_sol210_adapted [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 c : ℝ}
    (hl2 : 1 < |lam2|) {z : ℕ → V} (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x0 : V}
    (hx0 : E.E 0 x0 = x0) : sre_IsAdapted E (sre_sol210 E lam1 lam2 a0 a1 c z x0) := by
  have hω := sre_fwd_adapted E hl2 (sre_force210_bounded E c hz)
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    simp only [sre_sol210, map_add, map_smul, map_sub]
    rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih, hω (t + 1), hza (t + 1),
      sre_adapted_succ E hω t]

/-- The key identity: `E_tx_{t+1} = λ₁x_t + ω_t` along the constructed solution. -/
theorem sre_sol210_E [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 c : ℝ}
    (hsum : lam1 + lam2 = a0 + a1) (hne : a0 ≠ lam1) (hl2 : 1 < |lam2|) {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : sre_IsBounded z) {x0 : V} (hx0 : E.E 0 x0 = x0) (t : ℕ) :
    E.E t (sre_sol210 E lam1 lam2 a0 a1 c z x0 (t + 1)) =
      lam1 • sre_sol210 E lam1 lam2 a0 a1 c z x0 t + sre_fwd E lam2 (sre_force210 E c z) t := by
  have hfb := sre_force210_bounded E c hz
  have hω := sre_fwd_adapted E hl2 hfb
  have hrec := sre_fwd_rec E hl2 (sre_force210_adapted E c z) hfb t
  have hXa := sre_sol210_adapted E (lam1 := lam1) (a0 := a0) (a1 := a1) (c := c) hl2 hza hz hx0
  have hk : (a0 - lam1)⁻¹ * (a0 - lam1) = 1 := inv_mul_cancel₀ (sub_ne_zero.2 hne)
  simp only [sre_sol210, map_add, map_smul, map_sub]
  rw [hXa t, hrec, hω t, sre_force210]
  have ha1 : a1 = lam1 + lam2 - a0 := by linarith
  subst ha1
  linear_combination (norm := module) hk • sre_fwd E lam2 (sre_force210 E c z) t

/-- Miao, (2.10), p. 51, existence (the book's recipe, made precise): let `λ₁, λ₂` be the roots
of `λ² = (a₀ + a₁)λ + a₂` (`λ₁ + λ₂ = a₀ + a₁`, `λ₁λ₂ = −a₂`) with `|λ₁| < 1 < |λ₂|`, and
`a₀ ≠ λ₁`. For stable adapted `z`, `sre_sol210` is a stable adapted solution of (2.10) with the
given `x₀`. -/
theorem eq_2_10_solution [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 a2 c : ℝ}
    (hsum : lam1 + lam2 = a0 + a1) (hprod : a2 = -(lam1 * lam2)) (hne : a0 ≠ lam1)
    (hl1 : |lam1| < 1) (hl2 : 1 < |lam2|) {z : ℕ → V} (hza : sre_IsAdapted E z)
    (hz : sre_IsBounded z) {x0 : V} (hx0 : E.E 0 x0 = x0) :
    sre_sol210 E lam1 lam2 a0 a1 c z x0 0 = x0 ∧
      sre_IsAdapted E (sre_sol210 E lam1 lam2 a0 a1 c z x0) ∧
      sre_IsBounded (sre_sol210 E lam1 lam2 a0 a1 c z x0) ∧
      sre_IsSol210 E a0 a1 a2 c z (sre_sol210 E lam1 lam2 a0 a1 c z x0) := by
  set X := sre_sol210 E lam1 lam2 a0 a1 c z x0 with hX
  set ω := sre_fwd E lam2 (sre_force210 E c z) with hωdef
  have hfb := sre_force210_bounded E c hz
  have hXa : sre_IsAdapted E X := sre_sol210_adapted E hl2 hza hz hx0
  have hk : (a0 - lam1) * (a0 - lam1)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.2 hne)
  refine ⟨rfl, hXa, ?_, fun t => ?_⟩
  · obtain ⟨W, hW⟩ := sre_fwd_isBounded E hl2 hfb
    obtain ⟨Z, hZ⟩ := hz
    have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
    have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
    have hU0 : 0 ≤ |(a0 - lam1)⁻¹| * (W + |a1| * W + |c| * Z) := by positivity
    refine ⟨_, sre_bounded_of_rec hl1 hU0 (fun t => ?_)⟩
    have hinner : ‖ω (t + 1) - a1 • ω t - c • z (t + 1)‖ ≤ W + |a1| * W + |c| * Z := by
      calc ‖ω (t + 1) - a1 • ω t - c • z (t + 1)‖
          ≤ ‖ω (t + 1) - a1 • ω t‖ + ‖c • z (t + 1)‖ := norm_sub_le _ _
        _ ≤ ‖ω (t + 1)‖ + ‖a1 • ω t‖ + ‖c • z (t + 1)‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ W + |a1| * W + |c| * Z := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
            gcongr
            · exact hW _
            · exact hW _
            · exact hZ _
    calc ‖X (t + 1)‖
        = ‖lam1 • X t + (a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1))‖ := rfl
      _ ≤ ‖lam1 • X t‖ + ‖(a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1))‖ :=
          norm_add_le _ _
      _ ≤ |lam1| * ‖X t‖ + |(a0 - lam1)⁻¹| * (W + |a1| * W + |c| * Z) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
  · have h1 := sre_sol210_E E hsum hne hl2 hza hz hx0 (c := c) (t + 1)
    have h0 := sre_sol210_E E hsum hne hl2 hza hz hx0 (c := c) t
    rw [h1, h0]
    have hdef : X (t + 1) =
        lam1 • X t + (a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1)) := rfl
    have hDX : (a0 - lam1) • X (t + 1) =
        ((a0 - lam1) * lam1) • X t + (ω (t + 1) - a1 • ω t - c • z (t + 1)) := by
      rw [hdef]
      linear_combination (norm := module) hk • (ω (t + 1) - a1 • ω t - c • z (t + 1))
    have ha1 : a1 = lam1 + lam2 - a0 := by linarith
    subst ha1 hprod
    linear_combination (norm := module) -hDX

/-- Miao, (2.10), p. 51, uniqueness: under the hypotheses of `eq_2_10_solution`, every stable
adapted solution of (2.10) is `sre_sol210` with its own `x₀`. -/
theorem eq_2_10_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {lam1 lam2 a0 a1 a2 c : ℝ}
    (hsum : lam1 + lam2 = a0 + a1) (hprod : a2 = -(lam1 * lam2)) (hne : a0 ≠ lam1)
    (hl2 : 1 < |lam2|) {z : ℕ → V} (hz : sre_IsBounded z)
    {x : ℕ → V} (hxa : sre_IsAdapted E x) (hxb : sre_IsBounded x)
    (hxs : sre_IsSol210 E a0 a1 a2 c z x) :
    x = sre_sol210 E lam1 lam2 a0 a1 c z (x 0) := by
  set ω := sre_fwd E lam2 (sre_force210 E c z) with hωdef
  have hfb := sre_force210_bounded E c hz
  have hw : (fun t => E.E t (x (t + 1)) - lam1 • x t) = ω := by
    refine sre_unique_of_bounded E hl2 (f := sre_force210 E c z) ?_
      (sre_fwd_adapted E hl2 hfb) ?_ (sre_fwd_isBounded E hl2 hfb) ?_
      (sre_fwd_rec E hl2 (sre_force210_adapted E c z) hfb)
    · intro t
      simp only [map_sub, map_smul, E.idem, hxa t]
    · obtain ⟨M, hM⟩ := hxb
      exact ⟨M + |lam1| * M, fun t => (norm_sub_le _ _).trans (add_le_add
        ((E.norm_apply_le _ _).trans (hM _))
        (by rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hM t))⟩
    · intro t
      simp only [map_sub, map_smul]
      rw [E.tower_le_apply (Nat.le_succ t), eq_2_10_reduce E hxa hxs t, sre_force210]
      have ha1 : a1 = lam1 + lam2 - a0 := by linarith
      subst ha1 hprod
      module
  have hk : (a0 - lam1)⁻¹ * (a0 - lam1) = 1 := inv_mul_cancel₀ (sub_ne_zero.2 hne)
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    have e1 : E.E (t + 1) (x (t + 2)) = lam1 • x (t + 1) + ω (t + 1) := by
      have := congrFun hw (t + 1)
      rw [← this]; abel
    have e0 : E.E t (x (t + 1)) = lam1 • x t + ω t := by
      have := congrFun hw t
      rw [← this]; abel
    have heq := hxs t
    rw [e1, e0] at heq
    change x (t + 1) = lam1 • sre_sol210 E lam1 lam2 a0 a1 c z (x 0) t +
      (a0 - lam1)⁻¹ • (ω (t + 1) - a1 • ω t - c • z (t + 1))
    rw [← ih]
    have ha1 : a1 = lam1 + lam2 - a0 := by linarith
    subst ha1 hprod
    linear_combination (norm := module) -(a0 - lam1)⁻¹ • heq - hk • (x (t + 1) - lam1 • x t)

/-- The sunspot process `x_{t+1} = λ₁x_t + η_{t+1}`. -/
def sre_sunspot (lam1 : ℝ) (η : ℕ → V) (x0 : V) : ℕ → V
  | 0 => x0
  | t + 1 => lam1 • sre_sunspot lam1 η x0 t + η (t + 1)

/-- Miao, (2.10), p. 51, the condition `a₀ ≠ λ₁` cannot be dropped: if `a₀ = λ₁` (so
`a₁ = λ₂`, `a₂ = −λ₁λ₂`) and `c = 0`, then for every adapted `η` with `E_tη_{t+1} = 0`,
`x_{t+1} = λ₁x_t + η_{t+1}` solves (2.10); it is stable when `η` is bounded and `|λ₁| < 1`.
Taking `η = 0` and any nonzero bounded martingale difference gives two different stable solutions
with the same `x₀`. -/
theorem eq_2_10_indeterminate (E : CondExpSystem ℝ V) {lam1 lam2 : ℝ} (hl1 : |lam1| < 1)
    {z η : ℕ → V} (hηa : sre_IsAdapted E η) (hη : ∀ t, E.E t (η (t + 1)) = 0) {x0 : V}
    (hx0 : E.E 0 x0 = x0) :
    sre_IsAdapted E (sre_sunspot lam1 η x0) ∧
      sre_IsSol210 E lam1 lam2 (-(lam1 * lam2)) 0 z (sre_sunspot lam1 η x0) ∧
      (sre_IsBounded η → sre_IsBounded (sre_sunspot lam1 η x0)) := by
  have hXa : sre_IsAdapted E (sre_sunspot lam1 η x0) := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      simp only [sre_sunspot, map_add, map_smul]
      rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih, hηa]
  refine ⟨hXa, fun t => ?_, fun ⟨U, hU⟩ => ?_⟩
  · have h1 : sre_sunspot lam1 η x0 (t + 2) = lam1 • sre_sunspot lam1 η x0 (t + 1) + η (t + 2) :=
      rfl
    have h0 : sre_sunspot lam1 η x0 (t + 1) = lam1 • sre_sunspot lam1 η x0 t + η (t + 1) := rfl
    rw [h1, map_add, map_smul, hXa (t + 1), hη (t + 1)]
    conv_rhs => rw [h0, map_add, map_smul, hXa t, hη t]
    rw [h0]
    module
  · have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
    refine ⟨_, sre_bounded_of_rec hl1 hU0 (fun t => ?_)⟩
    calc ‖sre_sunspot lam1 η x0 (t + 1)‖ = ‖lam1 • sre_sunspot lam1 η x0 t + η (t + 1)‖ := rfl
      _ ≤ |lam1| * ‖sre_sunspot lam1 η x0 t‖ + U := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hU _

/-! ### §2.2.2: the method of undetermined coefficients -/

/-- The guess of §2.2.2 (Miao, p. 51): `x_t = Gx_{t−1} + Hz_t`. -/
def sre_uc (G H : ℝ) (z : ℕ → V) (x0 : V) : ℕ → V
  | 0 => x0
  | t + 1 => G • sre_uc G H z x0 t + H • z (t + 1)

theorem sre_uc_adapted (E : CondExpSystem ℝ V) (G H : ℝ) {z : ℕ → V} (hza : sre_IsAdapted E z)
    {x0 : V} (hx0 : E.E 0 x0 = x0) : sre_IsAdapted E (sre_uc G H z x0) := by
  intro t
  induction t with
  | zero => exact hx0
  | succ t ih =>
    simp only [sre_uc, map_add, map_smul]
    rw [← ih, E.tower_ge_apply (Nat.le_succ t), ih, hza]

/-- §2.2.2 (Miao, pp. 51–52): with `z_t = ρz_{t−1} + ε_t`, `E_{t−1}ε_t = 0` (so
`E_tz_{t+1} = ρz_t`; the book assumes `ε` IID with mean zero), the guess solves (2.6) iff
`(G² − aG − b)x_{t−1} + (GH + ρH − aH − c)z_t = 0` for all `t ≥ 1`. (The book's display
`E_t(Gx_t + Hz_{t+1}) = a(Gx_{t−1} + Hz_t) + bx_{t−1} + cz_t = G²x_{t−1} + GHz_t + ρHz_t` chains
the equation and the evaluation of its left side; the matching conditions are as printed.) -/
theorem uc_iff (E : CondExpSystem ℝ V) {a b c ρ G H : ℝ} {z : ℕ → V} (hza : sre_IsAdapted E z)
    (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) {x0 : V} (hx0 : E.E 0 x0 = x0) :
    sre_IsSol26 E a b c z (sre_uc G H z x0) ↔
      ∀ t, (G ^ 2 - a * G - b) • sre_uc G H z x0 t +
        (G * H + ρ * H - a * H - c) • z (t + 1) = 0 := by
  have hXa := sre_uc_adapted E G H hza hx0
  refine forall_congr' fun t => ?_
  have h1 : sre_uc G H z x0 (t + 2) = G • sre_uc G H z x0 (t + 1) + H • z (t + 2) := rfl
  have h0 : sre_uc G H z x0 (t + 1) = G • sre_uc G H z x0 t + H • z (t + 1) := rfl
  rw [h1, map_add, map_smul, map_smul, hXa (t + 1), hz (t + 1), h0, ← sub_eq_zero]
  constructor
  · intro h
    rw [← h]
    module
  · intro h
    rw [← h]
    module

/-- §2.2.2 (Miao, p. 52): matching coefficients, `G² = aG + b` and `GH + ρH = aH + c`, is
sufficient for the guess to solve (2.6). -/
theorem uc_sufficient (E : CondExpSystem ℝ V) {a b c ρ G H : ℝ} {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) {x0 : V}
    (hx0 : E.E 0 x0 = x0) (hG : G ^ 2 = a * G + b) (hH : G * H + ρ * H = a * H + c) :
    sre_IsSol26 E a b c z (sre_uc G H z x0) := by
  refine (uc_iff E hza hz hx0).2 fun t => ?_
  rw [show G ^ 2 - a * G - b = 0 by linarith, show G * H + ρ * H - a * H - c = 0 by linarith,
    zero_smul, zero_smul, add_zero]

/-- §2.2.2 (Miao, p. 52): matching coefficients is necessary as soon as the guess solves (2.6)
for two different initial values and `z` is not identically zero. -/
theorem uc_necessary (E : CondExpSystem ℝ V) {a b c ρ G H : ℝ} {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) {x0 x0' : V}
    (hx0 : E.E 0 x0 = x0) (hx0' : E.E 0 x0' = x0') (hne : x0 ≠ x0')
    (hs : sre_IsSol26 E a b c z (sre_uc G H z x0))
    (hs' : sre_IsSol26 E a b c z (sre_uc G H z x0')) {t : ℕ} (hzt : z (t + 1) ≠ 0) :
    G ^ 2 = a * G + b ∧ G * H + ρ * H = a * H + c := by
  have h := (uc_iff E hza hz hx0).1 hs
  have h' := (uc_iff E hza hz hx0').1 hs'
  have hG : G ^ 2 - a * G - b = 0 := by
    have h0 := h 0
    have h0' := h' 0
    have : (G ^ 2 - a * G - b) • (x0 - x0') = 0 := by
      have e : sre_uc G H z x0 0 = x0 := rfl
      have e' : sre_uc G H z x0' 0 = x0' := rfl
      rw [e] at h0
      rw [e'] at h0'
      rw [smul_sub]
      linear_combination (norm := module) h0 - h0'
    exact (smul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have ht := h t
  rw [hG, zero_smul, zero_add] at ht
  have hH := (smul_eq_zero.1 ht).resolve_right hzt
  constructor <;> linarith

/-- §2.2.2 (Miao, p. 52): with `a = λ₁ + λ₂`, `|ρ| < 1 < |λ₂|`, the denominator of
`H = c/(G + ρ − a)` at the stable root `G = λ₁` is `ρ − λ₂ ≠ 0`. -/
theorem uc_denominator_ne_zero {a lam1 lam2 ρ : ℝ} (ha : a = lam1 + lam2) (hρ : |ρ| < 1)
    (hl2 : 1 < |lam2|) : lam1 + ρ - a ≠ 0 := by
  rw [ha]
  intro h
  have : ρ = lam2 := by linarith
  rw [this] at hρ
  linarith

/-- §2.2.2 (Miao, p. 52): the stable root `G = λ₁` and `H = c/(G + ρ − a)` satisfy both
matching conditions. -/
theorem uc_stable_root {a b c lam1 lam2 ρ : ℝ} (ha : a = lam1 + lam2) (hb : b = -(lam1 * lam2))
    (hρ : |ρ| < 1) (hl2 : 1 < |lam2|) :
    lam1 ^ 2 = a * lam1 + b ∧
      lam1 * (c / (lam1 + ρ - a)) + ρ * (c / (lam1 + ρ - a)) =
        a * (c / (lam1 + ρ - a)) + c := by
  have hd := uc_denominator_ne_zero ha hρ hl2
  refine ⟨by rw [ha, hb]; ring, ?_⟩
  field_simp
  ring

/-- §2.2.2 (Miao, p. 52): the undetermined-coefficients solution with `G = λ₁`,
`H = c/(G + ρ − a)` is the lag-operator solution of (2.6)–(2.9). -/
theorem uc_eq_lag_solution (E : CondExpSystem ℝ V) {a c lam1 lam2 ρ : ℝ}
    (ha : a = lam1 + lam2) (hρ : |ρ| < 1) (hl2 : 1 < |lam2|) {z : ℕ → V}
    (hza : sre_IsAdapted E z) (hz : ∀ t, E.E t (z (t + 1)) = ρ • z t) (x0 : V) :
    sre_second E lam1 lam2 c z x0 = sre_uc lam1 (c / (lam1 + ρ - a)) z x0 := by
  have hd := uc_denominator_ne_zero ha hρ hl2
  have hρl : |ρ| < |lam2| := by linarith
  have hu : ∀ t, sre_fwd E lam2 (c • z) t = (c / (lam1 + ρ - a)) • z t := by
    intro t
    rw [sre_fwd_ar1 E hρl (sre_smul_isAdapted E c hza) (fun t => by
      simp only [Pi.smul_apply, map_smul, hz t, smul_comm c ρ]) t, Pi.smul_apply, smul_smul]
    congr 1
    rw [ha, show lam1 + ρ - (lam1 + lam2) = ρ - lam2 by ring]
    field_simp
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change lam1 • sre_second E lam1 lam2 c z x0 t + sre_fwd E lam2 (c • z) (t + 1) =
      lam1 • sre_uc lam1 (c / (lam1 + ρ - a)) z x0 t + (c / (lam1 + ρ - a)) • z (t + 1)
    rw [ih, hu]

/-! ### Example 2.2.1: the bursting bubble, concretely -/

/-- Example 2.2.1 (Miao, p. 50): a coin `θ_{t+1}` independent of `F_t` with mean `q` (for a
0–1 coin, `Pr(θ_{t+1} = 1) = q`) has conditional mean `E_tθ_{t+1} = q`. -/
theorem example_2_2_1_coin {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (t : ℕ) {θ : Ω → ℝ} {q : ℝ}
    (hθ : Measurable θ) (hind : ProbabilityTheory.Indep (MeasurableSpace.comap θ inferInstance)
      (ℱ t) μ) (hq : ∫ ω, θ ω ∂μ = q) :
    μ[θ | ℱ t] =ᵐ[μ] fun _ => q := by
  have h := condExp_indep_eq hθ.comap_le (ℱ.le t)
    (Measurable.of_comap_le le_rfl).stronglyMeasurable hind
  rw [hq] at h
  exact h

/-- **Example 2.2.1** (Miao, p. 50): the bursting bubble
`B_{t+1} = (R/q)B_tθ_{t+1} + e_{t+1}` with a 0–1 coin `θ_{t+1}` of conditional mean `q` and
`E_te_{t+1} = 0` satisfies (2.4): `E_tB_{t+1} = RB_t`. -/
theorem example_2_2_1_bubble {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {R q : ℝ} (hq : q ≠ 0) {B θ e : ℕ → Ω → ℝ}
    (t : ℕ) (hB : StronglyMeasurable[ℱ t] (B t)) (hBi : Integrable (B t) μ)
    (hθm : StronglyMeasurable (θ (t + 1))) (hθ01 : ∀ ω, θ (t + 1) ω = 0 ∨ θ (t + 1) ω = 1)
    (hθ : μ[θ (t + 1) | ℱ t] =ᵐ[μ] fun _ => q) (hei : Integrable (e (t + 1)) μ)
    (he : μ[e (t + 1) | ℱ t] =ᵐ[μ] 0)
    (hrec : ∀ ω, B (t + 1) ω = R / q * B t ω * θ (t + 1) ω + e (t + 1) ω) :
    μ[B (t + 1) | ℱ t] =ᵐ[μ] fun ω => R * B t ω := by
  have hθb : ∀ ω, ‖θ (t + 1) ω‖ ≤ 1 := fun ω => by
    rcases hθ01 ω with h | h <;> simp [h]
  have hθi : Integrable (θ (t + 1)) μ :=
    Integrable.of_bound hθm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hθb)
  have hfm : StronglyMeasurable[ℱ t] (fun ω => R / q * B t ω) := hB.const_mul _
  have hfi : Integrable (fun ω => R / q * B t ω) μ := hBi.const_mul _
  have hprod : Integrable ((fun ω => R / q * B t ω) * θ (t + 1)) μ :=
    hfi.mul_bdd hθm.aestronglyMeasurable (Filter.Eventually.of_forall hθb)
  have hsplit : B (t + 1) = (fun ω => R / q * B t ω) * θ (t + 1) + e (t + 1) := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, hrec ω]
  rw [hsplit]
  have h1 := condExp_add hprod hei (ℱ t)
  have h2 := condExp_mul_of_stronglyMeasurable_left hfm hprod hθi
  filter_upwards [h1, h2, hθ, he] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.mul_apply, h3, h4, Pi.zero_apply, add_zero]
  field_simp

/-- **Example 2.2.1** in `L¹` (Miao, p. 50): the classes of the bursting bubble satisfy (2.4)
for the conditional expectations `condExpSystemL1_real`, so the abstract results above apply
(a nonzero such bubble violates (2.5), `eq_2_5_bubble_fails`). -/
theorem example_2_2_1_bubble_L1 {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {R : ℝ} {B : ℕ → Ω → ℝ} (t : ℕ)
    (hBi : ∀ s, Integrable (B s) μ) (hB : μ[B (t + 1) | ℱ t] =ᵐ[μ] fun ω => R * B t ω) :
    (condExpSystemL1_real ℱ μ).E t ((hBi (t + 1)).toL1 _) = R • (hBi t).toL1 _ := by
  apply Lp.ext
  have h1 := condExpSystemL1_ae_eq ℝ ℱ μ t ((hBi (t + 1)).toL1 _)
  have h2 : μ[⇑((hBi (t + 1)).toL1 (B (t + 1))) | ℱ t] =ᵐ[μ] μ[B (t + 1) | ℱ t] :=
    condExp_congr_ae (Integrable.coeFn_toL1 _)
  have h3 := Lp.coeFn_smul R ((hBi t).toL1 (B t))
  have h4 := Integrable.coeFn_toL1 (hBi t)
  change _ =ᵐ[μ] _
  filter_upwards [h1, h2, hB, h3, h4] with ω e1 e2 e3 e4 e5
  rw [condExpSystemL1_real, e1, e2, e3, e4, Pi.smul_apply, e5, smul_eq_mul]

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 1: the stochastic Cagan model

Miao, §2.6, Exercise 1, p. 82: `m_t − p_t = −αE_t(p_{t+1} − p_t)`, `α > 0`,
`m_{t+1} = ρm_t + ε_{t+1}`, `ρ ∈ [0, 1]`, `m₀` given. Setting: a `CondExpSystem ℝ V`
(`ScalarRE`).

* For adapted `p` the model is `E_tp_{t+1} = ((1 + α)/α)p_t − α^{−1}m_t` (`ex_1_iff`), a
  first-order equation with `b = (1 + α)/α > 1` (`ex_1_b_gt_one`).
* Condition and uniqueness: for every `α > 0` and every stable adapted `m` there is exactly one
  stable adapted solution, the forward solution `p_t = α^{−1}∑ⱼ b^{−j−1}E_tm_{t+j}`
  (`ex_1_unique`).
* The solution: if `E_tε_{t+1} = 0`, then `E_tm_{t+j} = ρʲm_t` and
  `p_t = m_t/(1 + α(1 − ρ))` (`ex_1_solution`); it is the forward solution for every
  `ρ ∈ [0, 1]` (`ex_1_solution_eq_fwd`), and for `ρ ∈ [0, 1)` with `ε` stable, `m` is stable
  and this is the unique stable solution (`ex_1`).
* What the shock must satisfy: the book takes `ε` a white noise; the formula solves the model iff
  `E_tε_{t+1} = 0` for all `t` (`ex_1_solution_iff`), which a white noise need not satisfy
  (`whiteNoise_not_mds` in `VARMoments`).
* `ρ = 1`: `m` is a martingale (`ex_1_rho_one_martingale`) whose norm grows at most linearly
  (`ex_1_rho_one_growth`); `p = m` solves the model and is the unique adapted solution satisfying
  the transversality condition (2.5) (`ex_1_rho_one`), whether or not `m` is stable; it is stable
  exactly when `m` is. (That a random walk with stable white-noise increments is not stable in
  `L¹`, e.g. `E|m_t| ~ √(2t/π)` for ±1 steps, is not formalised.)
-/

namespace Miao.RationalExpectations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exercise 1 (Miao, p. 82): the Cagan model `m_t − p_t = −αE_t(p_{t+1} − p_t)`. -/
def ex1_IsSol (E : CondExpSystem ℝ V) (α : ℝ) (m p : ℕ → V) : Prop :=
  ∀ t, m t - p t = -α • E.E t (p (t + 1) - p t)

/-- **Exercise 1** (Miao, p. 82): for adapted `p` and `α ≠ 0`, the Cagan model is
`E_tp_{t+1} = ((1 + α)/α)p_t − α^{−1}m_t`. -/
theorem ex_1_iff (E : CondExpSystem ℝ V) {α : ℝ} (hα : α ≠ 0) {m p : ℕ → V}
    (hp : sre_IsAdapted E p) :
    ex1_IsSol E α m p ↔ ∀ t, E.E t (p (t + 1)) = ((1 + α) / α) • p t + (-α⁻¹ • m) t := by
  refine forall_congr' fun t => ?_
  rw [map_sub, hp t, Pi.smul_apply]
  constructor
  · intro h
    have h2 : E.E t (p (t + 1)) = α⁻¹ • (α • E.E t (p (t + 1))) := by
      rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
    rw [h2]
    have h3 : α • E.E t (p (t + 1)) = α • p t + p t - m t := by
      rw [smul_sub] at h
      linear_combination (norm := module) h
    rw [h3]
    have : (1 + α) / α = α⁻¹ * (1 + α) := by ring
    rw [this, mul_smul]
    module
  · intro h
    rw [h]
    have : (1 + α) / α = α⁻¹ * (1 + α) := by ring
    rw [this, mul_smul]
    have h4 : α • α⁻¹ • ((1 + α) • p t) = (1 + α) • p t := by
      rw [smul_smul, mul_inv_cancel₀ hα, one_smul]
    have h5 : α • α⁻¹ • m t = m t := by rw [smul_smul, mul_inv_cancel₀ hα, one_smul]
    linear_combination (norm := module) h4 - h5

/-- Exercise 1: `b = (1 + α)/α > 1` for `α > 0`. -/
theorem ex_1_b_gt_one {α : ℝ} (hα : 0 < α) : 1 < |(1 + α) / α| := by
  rw [abs_of_pos (by positivity), lt_div_iff₀ hα]
  linarith

/-- **Exercise 1** (Miao, p. 82), existence and uniqueness: for `α > 0` and a stable adapted
money supply, the forward solution `p_t = α^{−1}∑ⱼ b^{−j−1}E_tm_{t+j}`, `b = (1 + α)/α`, is a
stable adapted solution, and it is the only one. -/
theorem ex_1_unique [CompleteSpace V] (E : CondExpSystem ℝ V) {α : ℝ} (hα : 0 < α)
    {m : ℕ → V} (hma : sre_IsAdapted E m) (hm : sre_IsBounded m) :
    (sre_IsAdapted E (sre_fwd E ((1 + α) / α) (-α⁻¹ • m)) ∧
      sre_IsBounded (sre_fwd E ((1 + α) / α) (-α⁻¹ • m)) ∧
      ex1_IsSol E α m (sre_fwd E ((1 + α) / α) (-α⁻¹ • m))) ∧
    ∀ p, sre_IsAdapted E p → sre_IsBounded p → ex1_IsSol E α m p →
      p = sre_fwd E ((1 + α) / α) (-α⁻¹ • m) := by
  have hb := ex_1_b_gt_one hα
  have hfa := sre_smul_isAdapted E (-α⁻¹) hma
  have hfb := sre_smul_isBounded (-α⁻¹) hm
  have hpa := sre_fwd_adapted E hb hfb
  refine ⟨⟨hpa, sre_fwd_isBounded E hb hfb,
    (ex_1_iff E hα.ne' hpa).2 (sre_fwd_rec E hb hfa hfb)⟩, fun p hp hpb hps => ?_⟩
  exact eq_2_3_unique E hb hfa hfb hp hpb ((ex_1_iff E hα.ne' hp).1 hps)

/-- Exercise 1: `m_{t+1} = ρm_t + ε_{t+1}` with `E_tε_{t+1} = 0` gives `E_tm_{t+1} = ρm_t`. -/
theorem ex_1_Em (E : CondExpSystem ℝ V) {ρ : ℝ} {m ε : ℕ → V} (hma : sre_IsAdapted E m)
    (hrec : ∀ t, m (t + 1) = ρ • m t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0) (t : ℕ) :
    E.E t (m (t + 1)) = ρ • m t := by
  rw [hrec, map_add, hε, add_zero, map_smul, hma]

/-- **Exercise 1** (Miao, p. 82): if `E_tm_{t+1} = ρm_t` (e.g. `E_tε_{t+1} = 0`, `ex_1_Em`) and
`1 + α(1 − ρ) ≠ 0`, then `p_t = m_t/(1 + α(1 − ρ))` solves the Cagan model. -/
theorem ex_1_solution (E : CondExpSystem ℝ V) {α ρ : ℝ} {m : ℕ → V}
    (hma : sre_IsAdapted E m) (hm : ∀ t, E.E t (m (t + 1)) = ρ • m t)
    (hd : 1 + α * (1 - ρ) ≠ 0) :
    ex1_IsSol E α m (fun t => (1 + α * (1 - ρ))⁻¹ • m t) := by
  intro t
  rw [map_sub, map_smul, map_smul, hm, hma]
  have hk : (1 + α * (1 - ρ))⁻¹ * (1 + α * (1 - ρ)) = 1 := inv_mul_cancel₀ hd
  linear_combination (norm := module) -(hk • m t)

/-- **Exercise 1** (Miao, p. 82): the solution `m_t/(1 + α(1 − ρ))` is the forward solution
for every `ρ ∈ [0, 1]` (the forward sum converges since `ρ ≤ 1 < b`, even if `m` is not stable). -/
theorem ex_1_solution_eq_fwd (E : CondExpSystem ℝ V) {α ρ : ℝ} (hα : 0 < α) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) {m : ℕ → V} (hma : sre_IsAdapted E m)
    (hm : ∀ t, E.E t (m (t + 1)) = ρ • m t) (t : ℕ) :
    sre_fwd E ((1 + α) / α) (-α⁻¹ • m) t = (1 + α * (1 - ρ))⁻¹ • m t := by
  have hb := ex_1_b_gt_one hα
  have hρb : |ρ| < |(1 + α) / α| := by
    rw [abs_of_nonneg hρ0]
    exact lt_of_le_of_lt hρ1 hb
  rw [sre_fwd_ar1 E hρb (sre_smul_isAdapted E _ hma) (fun t => by
    simp only [Pi.smul_apply, map_smul, hm t, smul_comm (-α⁻¹) ρ]) t, Pi.smul_apply, smul_smul]
  congr 1
  have h1 : ρ - (1 + α) / α ≠ 0 := by
    intro h
    have : ρ = (1 + α) / α := by linarith
    rw [this, abs_of_pos (by positivity)] at hρb
    exact lt_irrefl _ hρb
  have h2 : 1 + α * (1 - ρ) ≠ 0 := by nlinarith
  rw [show ρ - (1 + α) / α = -(1 + α * (1 - ρ)) / α by field_simp; ring, inv_div]
  field_simp

/-- **Exercise 1** (Miao, p. 82), the answer: for `α > 0`, `ρ ∈ [0, 1)`, `m₀` adapted and a
stable shock with `E_tε_{t+1} = 0`, the money supply is stable and `p_t = m_t/(1 + α(1 − ρ))` is
the unique stable adapted solution. -/
theorem ex_1 [CompleteSpace V] (E : CondExpSystem ℝ V) {α ρ : ℝ} (hα : 0 < α) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {m ε : ℕ → V} (hma : sre_IsAdapted E m)
    (hrec : ∀ t, m (t + 1) = ρ • m t + ε (t + 1)) (hε : ∀ t, E.E t (ε (t + 1)) = 0)
    (hεb : sre_IsBounded ε) :
    sre_IsBounded m ∧ ex1_IsSol E α m (fun t => (1 + α * (1 - ρ))⁻¹ • m t) ∧
      sre_IsBounded (fun t => (1 + α * (1 - ρ))⁻¹ • m t) ∧
      ∀ p, sre_IsAdapted E p → sre_IsBounded p → ex1_IsSol E α m p →
        p = fun t => (1 + α * (1 - ρ))⁻¹ • m t := by
  have hEm := ex_1_Em E hma hrec hε
  have hd : 1 + α * (1 - ρ) ≠ 0 := by nlinarith
  have hmb : sre_IsBounded m := by
    obtain ⟨U, hU⟩ := hεb
    have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
    have hl : |ρ| < 1 := by rw [abs_of_nonneg hρ0]; exact hρ1
    refine ⟨_, sre_bounded_of_rec hl hU0 (fun t => ?_)⟩
    rw [hrec]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact hU _
  refine ⟨hmb, ex_1_solution E hma hEm hd, ?_, fun p hp hpb hps => ?_⟩
  · have := sre_smul_isBounded (1 + α * (1 - ρ))⁻¹ hmb
    exact this
  · rw [(ex_1_unique E hα hma hmb).2 p hp hpb hps]
    funext t
    exact ex_1_solution_eq_fwd E hα hρ0 hρ1.le hma hEm t

/-- **Exercise 1** (Miao, p. 82), what the shock must satisfy: with `m` adapted,
`m_{t+1} = ρm_t + ε_{t+1}` and `1 + α(1 − ρ) ≠ 0`, the price `m_t/(1 + α(1 − ρ))` solves the
model iff `E_tε_{t+1} = 0` for all `t`. A white noise (the book's assumption) need not satisfy this
(`whiteNoise_not_mds`). -/
theorem ex_1_solution_iff (E : CondExpSystem ℝ V) {α ρ : ℝ} {m ε : ℕ → V}
    (hma : sre_IsAdapted E m) (hrec : ∀ t, m (t + 1) = ρ • m t + ε (t + 1))
    (hd : 1 + α * (1 - ρ) ≠ 0) (hα : α ≠ 0) :
    ex1_IsSol E α m (fun t => (1 + α * (1 - ρ))⁻¹ • m t) ↔ ∀ t, E.E t (ε (t + 1)) = 0 := by
  refine ⟨fun h t => ?_, fun h => ex_1_solution E hma (ex_1_Em E hma hrec h) hd⟩
  have ht := h t
  rw [map_sub, map_smul, map_smul, hma, hrec, map_add, map_smul, hma] at ht
  have hk : (1 + α * (1 - ρ))⁻¹ * (1 + α * (1 - ρ)) = 1 := inv_mul_cancel₀ hd
  have h2 : (α * (1 + α * (1 - ρ))⁻¹) • E.E t (ε (t + 1)) = 0 := by
    linear_combination (norm := module) ht + hk • m t
  exact (smul_eq_zero.1 h2).resolve_left (mul_ne_zero hα (inv_ne_zero hd))

/-- Exercise 1 with `ρ = 1`: `m` is a martingale, `E_tm_{t+j} = m_t`. -/
theorem ex_1_rho_one_martingale (E : CondExpSystem ℝ V) {m ε : ℕ → V}
    (hma : sre_IsAdapted E m) (hrec : ∀ t, m (t + 1) = m t + ε (t + 1))
    (hε : ∀ t, E.E t (ε (t + 1)) = 0) (j t : ℕ) : E.E t (m (t + j)) = m t := by
  have := sre_iter E hma (b := 1) (fun t => by
    rw [one_smul]; simpa using ex_1_Em E hma (ρ := 1) (fun t => by rw [one_smul, hrec]) hε t) j t
  rwa [one_pow, one_smul] at this

omit [NormedSpace ℝ V] in
/-- Exercise 1 with `ρ = 1`: `‖m_t‖ ≤ ‖m₀‖ + tU` when `‖ε_t‖ ≤ U`; the norm grows at most
linearly (and need not stay bounded). -/
theorem ex_1_rho_one_growth {m ε : ℕ → V} {U : ℝ} (hrec : ∀ t, m (t + 1) = m t + ε (t + 1))
    (hU : ∀ t, ‖ε t‖ ≤ U) (t : ℕ) : ‖m t‖ ≤ ‖m 0‖ + t * U := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hrec]
    calc ‖m t + ε (t + 1)‖ ≤ ‖m t‖ + ‖ε (t + 1)‖ := norm_add_le _ _
      _ ≤ ‖m 0‖ + t * U + U := add_le_add ih (hU _)
      _ = ‖m 0‖ + ((t + 1 : ℕ) : ℝ) * U := by push_cast; ring

/-- **Exercise 1** with `ρ = 1` (Miao, p. 82): `p = m` solves the Cagan model and is the unique
adapted solution satisfying the transversality condition (2.5) `b^{−T}E_tp_{t+T} → 0`
(`b = (1 + α)/α`), with no stability assumption on `m`; `p` is stable iff `m` is. -/
theorem ex_1_rho_one (E : CondExpSystem ℝ V) {α : ℝ} (hα : 0 < α) {m ε : ℕ → V}
    (hma : sre_IsAdapted E m) (hrec : ∀ t, m (t + 1) = m t + ε (t + 1))
    (hε : ∀ t, E.E t (ε (t + 1)) = 0) :
    ex1_IsSol E α m m ∧ sre_Transversality E ((1 + α) / α) m ∧
      ∀ p, sre_IsAdapted E p → sre_Transversality E ((1 + α) / α) p → ex1_IsSol E α m p →
        p = m := by
  have hb := ex_1_b_gt_one hα
  have hEm : ∀ t, E.E t (m (t + 1)) = (1 : ℝ) • m t := fun t => by
    rw [one_smul]; exact (by simpa using ex_1_rho_one_martingale E hma hrec hε 1 t)
  have hsol : ex1_IsSol E α m m := by
    have := ex_1_solution E hma hEm (α := α) (by simp)
    simpa using this
  have htv : sre_Transversality E ((1 + α) / α) m := by
    intro t
    have hr : |((1 + α) / α)⁻¹| < 1 := sre_inv_abs_lt_one hb
    have hl := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).smul_const (m t)
    rw [zero_smul] at hl
    refine hl.congr fun T => ?_
    rw [ex_1_rho_one_martingale E hma hrec hε T t]
  have hb0 : (1 + α) / α ≠ 0 := by positivity
  refine ⟨hsol, htv, fun p hp hpt hps => ?_⟩
  exact sre_unique_of_tvc E hb0 hp hma hpt htv ((ex_1_iff E hα.ne' hp).1 hps)
    ((ex_1_iff E hα.ne' hma).1 hsol)

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stable processes and the forward solution (2.12)

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Blanchard–Kahn method for stochastic systems

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian model: Example 2.3.1 and Exercise 2.2

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Martingales and Klein's predetermined processes

Miao, §2.3.2, pp. 55–56, in the abstract setting of `Basics` (a `CondExpSystem 𝕜 V`).

* `IsMartingaleProc` (Definition 2.3.2): `E_t X_{t+1} = X_t`.
* `IsMartingaleDiffProc` (Definition 2.3.2): `E_t X_{t+1} = 0`.
* `IsPredeterminedKlein E ξ X` (Definition 2.3.4): the prediction error
  `X_{t+1} − E_t X_{t+1}` is the given process `ξ_{t+1}`, `ξ` is a martingale difference, and
  `X₀` is `F₀`-measurable (`E₀X₀ = X₀`). "Exogenously given" is modelled by `ξ` being a parameter.
* `predError_isMartingaleDiff`: the prediction error of any process is automatically a martingale
  difference, so clause (a) of Definition 2.3.4 only says that `ξ` is given in advance.
* `isPredeterminedKlein_zero_iff` (p. 56): with `ξ = 0` the definition is Blanchard and Kahn's
  (`IsPredeterminedBK`) together with `E₀X₀ = X₀`.
* `isStableProc_of_uniformly_bounded` (p. 56, "it is stable if it is uniformly bounded"); in the
  abstract setting stability means bounded norms (`E|X|` for `V = L¹`), so a uniform bound on the
  norms is stability itself. The `L¹` reading (`|X_t| ≤ M` a.s. gives `E|X_t| ≤ M`) belongs to the
  concrete `L¹` instance and is not formalised here.
* `example_mdiff_not_stable` (p. 56, "a martingale difference process may not be stable"): an
  abstract `CondExpSystem` on `ℓ^∞(ℕ)`, `E_t` = truncation to the coordinates `≤ t` (a
  filtration in which coordinate `t` is revealed at date `t`), with the adapted martingale
  difference `X_t = t·e_t`, `‖X_t‖ = t`. In a finite-dimensional `V` such an example is
  impossible for adapted processes, so an infinite-dimensional space is needed; this one is
  abstract and is not `L¹` of a probability space.

The white-noise claims of p. 56 (Definition 2.3.3, "a white noise process is stable", "(2.2) gives
a white noise", "a white noise may not satisfy (2.2)") are second-moment statements and are not
formalised in this module.
-/

namespace Miao.RationalExpectations

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Definition 2.3.2** (Miao, p. 55): `{X_t}` is a martingale if `E_t X_{t+1} = X_t`. -/
def IsMartingaleProc {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) : Prop :=
  ∀ t i, E.E t (X (t + 1) i) = X t i

/-- **Definition 2.3.2** (Miao, p. 55): `{X_t}` is a martingale difference process if
`E_t X_{t+1} = 0`. -/
def IsMartingaleDiffProc {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) : Prop :=
  ∀ t i, E.E t (X (t + 1) i) = 0

/-- **Definition 2.3.4** (Miao, p. 56): `{X_t}` is predetermined (backward-looking) with the
exogenously given prediction error `{ξ_t}` if (a) `ξ_{t+1} = X_{t+1} − E_t X_{t+1}` and `ξ` is a
martingale difference process, and (b) `X₀` is `F₀`-measurable. -/
def IsPredeterminedKlein {ι : Type*} (E : CondExpSystem 𝕜 V) (ξ X : ℕ → ι → V) : Prop :=
  (∀ t i, X (t + 1) i - E.E t (X (t + 1) i) = ξ (t + 1) i) ∧ IsMartingaleDiffProc E ξ ∧
    ∀ i, E.E 0 (X 0 i) = X 0 i

/-- Miao, Definition 2.3.4 (p. 56): the prediction error `X_{t+1} − E_t X_{t+1}` of any process is
a martingale difference (law of iterated expectations), so in clause (a) the content is that the
prediction error is given exogenously. -/
theorem predError_isMartingaleDiff {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) :
    IsMartingaleDiffProc E (fun t i => X t i - E.E (t - 1) (X t i)) := by
  intro t i
  simp only [Nat.add_sub_cancel, map_sub, E.idem, sub_self]

/-- Miao, p. 56 ("When `ξ_{t+1} = 0`, we obtain the Blanchard and Kahn (1980) definition"):
predetermined with zero prediction error is `E_t X_{t+1} = X_{t+1}` (`IsPredeterminedBK`) with an
`F₀`-measurable `X₀`. -/
theorem isPredeterminedKlein_zero_iff {ι : Type*} (E : CondExpSystem 𝕜 V) (X : ℕ → ι → V) :
    IsPredeterminedKlein E 0 X ↔ IsPredeterminedBK E X ∧ ∀ i, E.E 0 (X 0 i) = X 0 i := by
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨fun t i => (sub_eq_zero.1 (h1 t i)).symm, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨fun t i => by rw [h1 t i, sub_self]; rfl, fun t i => map_zero _, h3⟩

/-- A martingale is a martingale difference after subtracting its lag (Miao, p. 55):
`E_t (X_{t+1} − X_t) = 0` for an adapted martingale. -/
theorem IsMartingaleProc.diff {ι : Type*} {E : CondExpSystem 𝕜 V} {X : ℕ → ι → V}
    (hX : IsMartingaleProc E X) (had : IsAdaptedV E X) :
    IsMartingaleDiffProc E (fun t i => X t i - X (t - 1) i) := by
  intro t i
  simp only [Nat.add_sub_cancel, map_sub, hX t i, had t i, sub_self]

/-- Miao, p. 56: "A martingale difference process … is stable if it is uniformly bounded." In the
abstract setting stability (Definition 2.3.1) is a bound on the norms, so a uniform bound on the
norms gives stability (no martingale property is needed). -/
theorem isStableProc_of_uniformly_bounded {ι : Type*} {X : ℕ → ι → V} {M : ℝ}
    (h : ∀ t i, ‖X t i‖ ≤ M) : IsStableProc X :=
  ⟨max M 0 + 1, by positivity, fun t i => (h t i).trans_lt (by linarith [le_max_left M 0])⟩

/-! ### A martingale difference that is not stable -/

/-- The truncation `f ↦ f·1_{[0,t]}` on `ℓ^∞(ℕ)`, the conditional expectation of the example. -/
noncomputable def klM_trunc (t : ℕ) : lp (fun _ : ℕ => ℂ) ⊤ →L[ℂ] lp (fun _ : ℕ => ℂ) ⊤ :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun n => if n ≤ t then f n else 0, memℓp_infty_iff.2 ⟨‖f‖, by
        rintro _ ⟨n, rfl⟩
        change ‖(if n ≤ t then f n else 0)‖ ≤ ‖f‖
        split_ifs
        · exact lp.norm_apply_le_norm ENNReal.top_ne_zero f n
        · simp⟩⟩
      map_add' := fun f g => by
        refine lp.ext (funext fun n => ?_)
        simp only [lp.coeFn_add, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c f => by
        refine lp.ext (funext fun n => ?_)
        simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
    1 fun f => by
      rw [one_mul]
      refine lp.norm_le_of_forall_le (norm_nonneg f) fun n => ?_
      change ‖(if n ≤ t then f n else 0)‖ ≤ ‖f‖
      split_ifs
      · exact lp.norm_apply_le_norm ENNReal.top_ne_zero f n
      · simp

theorem klM_trunc_apply (t : ℕ) (f : lp (fun _ : ℕ => ℂ) ⊤) (n : ℕ) :
    klM_trunc t f n = if n ≤ t then f n else 0 := rfl

/-- The truncations form a `CondExpSystem` on `ℓ^∞(ℕ)` (coordinate `t` revealed at date `t`). -/
noncomputable def klM_truncSystem : CondExpSystem ℂ (lp (fun _ : ℕ => ℂ) ⊤) where
  E := klM_trunc
  norm_le t := LinearMap.mkContinuous_norm_le _ zero_le_one _
  tower_le s t h := by
    refine ContinuousLinearMap.ext fun f => lp.ext (funext fun n => ?_)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, klM_trunc_apply]
    split_ifs <;> first | rfl | omega
  tower_ge s t h := by
    refine ContinuousLinearMap.ext fun f => lp.ext (funext fun n => ?_)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, klM_trunc_apply]
    split_ifs <;> first | rfl | omega

/-- Miao, p. 56: "A martingale difference process may not be stable." In the `CondExpSystem` of
truncations on `ℓ^∞(ℕ)`, `X_t = t·e_t` is adapted and a martingale difference
(`E_t X_{t+1} = 0`), but `‖X_t‖ = t`, so it is not stable. -/
theorem example_mdiff_not_stable :
    ∃ X : ℕ → Fin 1 → lp (fun _ : ℕ => ℂ) ⊤, IsAdaptedV klM_truncSystem X ∧
      IsMartingaleDiffProc klM_truncSystem X ∧ ¬ IsStableProc X := by
  refine ⟨fun t _ => lp.single ⊤ t (t : ℂ), fun t i => ?_, fun t i => ?_, ?_⟩
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rfl
    · rw [lp.single_apply_ne ⊤ t _ (by omega)]
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rw [lp.single_apply_ne ⊤ (t + 1) _ (by omega)]
      rfl
    · rfl
  · rintro ⟨M, -, hM⟩
    obtain ⟨t, ht⟩ := exists_nat_gt M
    have h := hM t 0
    rw [lp.norm_single ENNReal.zero_lt_top, Complex.norm_natCast] at h
    linarith

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Klein method for linear rational expectations models

Miao, §2.3.2, pp. 56–57: the system `A E_t x_{t+1} = Bx_t + Cz_t` (2.11) with `A` possibly
singular, in the abstract setting of `Basics` with `𝕜 = ℂ` (the QZ form is complex): `V` is a
complete complex normed space of random variables with conditional expectations
`E : CondExpSystem ℂ V`, a vector random variable is `Fin m → V` with the max norm.

**Representation.** As in the deterministic `Singular`, `x_t = (k_t, y_t)` is indexed by
`Fin (nk + ny)`, the blocks are `Matrix.submatrix` along `Fin.castAdd ny` and `Fin.natAdd nk`, and
`x*_t = Zᴴx_t = (s_t, u_t)`.

* `klein_stochastic`: under the hypotheses of Theorem 1.4.5 (regular pencil, ordered QZ form with
  (i) `n_s = n_k`, (ii) `Z₁₁` invertible, (iii) no generalized eigenvalue on the unit circle), for
  every stable adapted `{z_t}`, every stable martingale-difference prediction error `{ξ_t}` and
  every `F₀`-measurable `k₀`, there is exactly one stable adapted solution of (2.11) whose
  predetermined block `k_t` is predetermined with prediction error `ξ` (Definition 2.3.4) and
  starts at `k₀`. The proof follows the book's modified steps: the forward solution (2.17)
  (`eq_2_17`, `klS_fwd`, `klS_eq_fwd`), the replacement of (1.38) (`eq_klein_Es`), the prediction
  error identity (`eq_klein_xi`), the formula for `s_{t+1}` (`eq_klein_s`) and
  `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}` (`eq_klein_k`).
* `klein_stochastic_real`: real data. `V` carries a conjugation `cj` (conjugate-linear, isometric,
  commuting with every `E_t`; for complex `L¹` it is pointwise conjugation); if `A`, `B`, `C` are
  real and `z`, `ξ`, `k₀` are fixed by `cj`, the unique solution is fixed by `cj` (real).

**Corrections.**
* (2.17) repeats the misprint of (1.37): it reads `u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ Q₂CE_t z_{t+j}`;
  the correct forward solution is `u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ Q₂CE_t z_{t+j}` (`eq_2_17`). The
  printed one fails already for the deterministic system `E_t = id` (`eq_2_17_printed_false`).
* The formulas for `E_t s_{t+1}`, the prediction error `ξ_{t+1}` and `s_{t+1}` on pp. 56–57 are
  correct as printed (every term and sign checked).
* The book's hypotheses leave implicit that `ξ_{t+1}` must be `F_{t+1}`-measurable (needed for
  the solution to be adapted) and that `ξ` must be stable (otherwise `k` is not); both are
  assumed.
-/

open Filter Topology

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Matrices acting on vectors of random variables -/

theorem klS_matAct_sub {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x y : κ → V) :
    matAct M (x - y) = matAct M x - matAct M y := by
  funext i
  simp [matAct, smul_sub, Finset.sum_sub_distrib]

theorem klS_matAct_neg {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x : κ → V) :
    matAct M (-x) = -matAct M x := by
  funext i
  simp [matAct, Finset.sum_neg_distrib]

theorem klS_matAct_zero {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) :
    matAct M (0 : κ → V) = 0 := by
  funext i
  simp [matAct]

theorem klS_zero_matAct {ι κ : Type*} [Fintype κ] (x : κ → V) :
    matAct (0 : Matrix ι κ ℂ) x = 0 := by
  funext i
  simp [matAct]

theorem klS_add_matAct {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℂ) (x : κ → V) :
    matAct (M + N) x = matAct M x + matAct N x := by
  funext i
  simp [matAct, add_smul, Finset.sum_add_distrib]

theorem klS_sub_matAct {ι κ : Type*} [Fintype κ] (M N : Matrix ι κ ℂ) (x : κ → V) :
    matAct (M - N) x = matAct M x - matAct N x := by
  funext i
  simp [matAct, sub_smul, Finset.sum_sub_distrib]

theorem klS_neg_matAct {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x : κ → V) :
    matAct (-M) x = -matAct M x := by
  funext i
  simp [matAct, neg_smul, Finset.sum_neg_distrib]

/-- Rows `f` of `Mv`: `(Mv)∘f = M_{f,·}v`. -/
theorem klS_matAct_comp {ι ι' κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (f : ι' → ι)
    (x : κ → V) : matAct M x ∘ f = matAct (M.submatrix f id) x := rfl

/-- `M` as a continuous linear map on vectors of random variables. -/
noncomputable def klS_matCLM {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) :
    (κ → V) →L[ℂ] (ι → V) :=
  ContinuousLinearMap.pi fun i => ∑ j, M i j • ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : κ => V) j

theorem klS_matCLM_apply {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (x : κ → V) :
    klS_matCLM M x = matAct M x := by
  funext i
  simp [klS_matCLM, matAct]

theorem klS_matAct_sum {ι κ α : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (s : Finset α)
    (f : α → κ → V) : matAct M (∑ a ∈ s, f a) = ∑ a ∈ s, matAct M (f a) := by
  rw [← klS_matCLM_apply, map_sum]
  simp only [klS_matCLM_apply]

theorem klS_matAct_inv_mul {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.det ≠ 0)
    (x : Fin m → V) : matAct M⁻¹ (matAct M x) = x := by
  rw [matAct_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h), matAct_one]

theorem klS_matAct_mul_inv {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.det ≠ 0)
    (x : Fin m → V) : matAct M (matAct M⁻¹ x) = x := by
  rw [matAct_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h), matAct_one]

/-- Column blocks: `Mv = M_{·,K}v_K + M_{·,U}v_U`, restricted to rows `f`. -/
theorem klS_matAct_blocks {ι κ : Type*} {a b : ℕ} (M : Matrix ι (Fin (a + b)) ℂ) (f : κ → ι)
    (v : Fin (a + b) → V) :
    matAct M v ∘ f = matAct (M.submatrix f (Fin.castAdd b)) (v ∘ Fin.castAdd b) +
      matAct (M.submatrix f (Fin.natAdd a)) (v ∘ Fin.natAdd a) := by
  funext i
  simp only [matAct, Function.comp_apply, Pi.add_apply, Fin.sum_univ_add, Matrix.submatrix_apply]

/-- For upper triangular `M`, the lower block row is `(Mv)_U = M_{UU}v_U`. -/
theorem klS_matAct_natAdd {a b : ℕ} {M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hM : M.IsUpperTriangular) (v : Fin (a + b) → V) :
    matAct M v ∘ Fin.natAdd a = matAct (M.submatrix (Fin.natAdd a) (Fin.natAdd a))
      (v ∘ Fin.natAdd a) := by
  rw [klS_matAct_blocks]
  have h0 : M.submatrix (Fin.natAdd a) (Fin.castAdd b) = 0 := by
    ext i j
    apply hM
    rw [Fin.lt_def]
    change (j : ℕ) < a + (i : ℕ)
    omega
  rw [h0, klS_zero_matAct, zero_add]

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem klS_ext_blocks {a b : ℕ} {f g : Fin (a + b) → V}
    (h1 : f ∘ Fin.castAdd b = g ∘ Fin.castAdd b) (h2 : f ∘ Fin.natAdd a = g ∘ Fin.natAdd a) :
    f = g := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · exact congrFun h1 i
  · exact congrFun h2 i

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem klS_append_castAdd {a b : ℕ} (x : Fin a → V) (y : Fin b → V) :
    Fin.append x y ∘ Fin.castAdd b = x :=
  funext fun i => Fin.append_left x y i

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem klS_append_natAdd {a b : ℕ} (x : Fin a → V) (y : Fin b → V) :
    Fin.append x y ∘ Fin.natAdd a = y :=
  funext fun i => Fin.append_right x y i

/-! ### Conditional expectations of vectors -/

theorem klS_Evec_add {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x y : ι → V) :
    Evec E t (x + y) = Evec E t x + Evec E t y := by
  funext i
  simp [Evec]

theorem klS_Evec_sub {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x y : ι → V) :
    Evec E t (x - y) = Evec E t x - Evec E t y := by
  funext i
  simp [Evec]

theorem klS_Evec_neg {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x : ι → V) :
    Evec E t (-x) = -Evec E t x := by
  funext i
  simp [Evec]

theorem klS_Evec_zero {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) :
    Evec E t (0 : ι → V) = 0 := by
  funext i
  simp [Evec]

theorem klS_Evec_idem {ι : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x : ι → V) :
    Evec E t (Evec E t x) = Evec E t x :=
  funext fun i => E.idem t (x i)

theorem klS_Evec_tower_le {ι : Type*} (E : CondExpSystem ℂ V) {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E s (Evec E t x) = Evec E s x :=
  funext fun i => E.tower_le_apply h (x i)

theorem klS_Evec_tower_ge {ι : Type*} (E : CondExpSystem ℂ V) {s t : ℕ} (h : s ≤ t)
    (x : ι → V) : Evec E t (Evec E s x) = Evec E s x :=
  funext fun i => E.tower_ge_apply h (x i)

theorem klS_Evec_comp {ι κ : Type*} (E : CondExpSystem ℂ V) (t : ℕ) (x : ι → V) (f : κ → ι) :
    Evec E t (x ∘ f) = Evec E t x ∘ f := rfl

theorem klS_Evec_append {a b : ℕ} (E : CondExpSystem ℂ V) (t : ℕ) (x : Fin a → V)
    (y : Fin b → V) : Evec E t (Fin.append x y) = Fin.append (Evec E t x) (Evec E t y) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [Evec]

/-- `F_t`-measurable variables are `F_{t+1}`-measurable. -/
theorem klS_adapted_succ {ι : Type*} (E : CondExpSystem ℂ V) {t : ℕ} {x : ι → V}
    (h : Evec E t x = x) : Evec E (t + 1) x = x := by
  rw [← h, klS_Evec_tower_ge E (Nat.le_succ t)]

/-- `E_t` as a continuous linear map on vectors. -/
noncomputable def klS_EvecCLM (E : CondExpSystem ℂ V) (t : ℕ) (ι : Type*) :
    (ι → V) →L[ℂ] (ι → V) :=
  ContinuousLinearMap.pi fun i => (E.E t).comp (ContinuousLinearMap.proj i)

theorem klS_EvecCLM_apply (E : CondExpSystem ℂ V) (t : ℕ) {ι : Type*} (x : ι → V) :
    klS_EvecCLM E t ι x = Evec E t x := rfl

/-! ### Norms and stability -/

/-- The entry sum `∑ᵢⱼ |Mᵢⱼ|`, which bounds the action of `M` on vectors of random variables. -/
noncomputable def klS_ent {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖M i j‖

theorem klS_ent_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) :
    0 ≤ klS_ent M := by
  unfold klS_ent
  positivity

theorem klS_norm_matAct_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ)
    (v : κ → V) : ‖matAct M v‖ ≤ klS_ent M * ‖v‖ := by
  unfold klS_ent
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖matAct M v i‖ = ‖∑ j, M i j • v j‖ := rfl
    _ ≤ ∑ j, ‖M i j • v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _)
    _ = (∑ j, ‖M i j‖) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
        (norm_nonneg _)

theorem klS_norm_Evec_le {ι : Type*} [Fintype ι] (E : CondExpSystem ℂ V) (t : ℕ) (v : ι → V) :
    ‖Evec E t v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
    (E.norm_apply_le t (v i)).trans (norm_le_pi_norm v i)

omit [NormedSpace ℂ V] in
theorem klS_stable_bound {ι : Type*} [Fintype ι] {x : ℕ → ι → V} (h : IsStableProc x) :
    ∃ K, 0 ≤ K ∧ ∀ t, ‖x t‖ ≤ K := by
  obtain ⟨M, hM, hx⟩ := h
  exact ⟨M, hM.le, fun t => (pi_norm_le_iff_of_nonneg hM.le).2 fun i => (hx t i).le⟩

omit [NormedSpace ℂ V] in
theorem klS_stable_of_le {ι : Type*} [Fintype ι] {x : ℕ → ι → V} {K : ℝ}
    (h : ∀ t, ‖x t‖ ≤ K) : IsStableProc x :=
  isStableProc_of_uniformly_bounded fun t i => (norm_le_pi_norm (x t) i).trans (h t)

omit [NormedSpace ℂ V] in
theorem klS_stable_add {ι : Type*} [Finite ι] {x y : ℕ → ι → V} (hx : IsStableProc x)
    (hy : IsStableProc y) : IsStableProc fun t => x t + y t := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  obtain ⟨L, -, hL⟩ := klS_stable_bound hy
  exact klS_stable_of_le fun t => (norm_add_le _ _).trans (add_le_add (hK t) (hL t))

omit [NormedSpace ℂ V] in
theorem klS_stable_sub {ι : Type*} [Finite ι] {x y : ℕ → ι → V} (hx : IsStableProc x)
    (hy : IsStableProc y) : IsStableProc fun t => x t - y t := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  obtain ⟨L, -, hL⟩ := klS_stable_bound hy
  exact klS_stable_of_le fun t => (norm_sub_le _ _).trans (add_le_add (hK t) (hL t))

theorem klS_stable_matAct {ι κ : Type*} [Finite ι] [Fintype κ] {x : ℕ → κ → V}
    (hx : IsStableProc x) (M : Matrix ι κ ℂ) : IsStableProc fun t => matAct M (x t) := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  exact klS_stable_of_le fun t => (klS_norm_matAct_le M (x t)).trans
    (mul_le_mul_of_nonneg_left (hK t) (klS_ent_nonneg M))

theorem klS_stable_Evec {ι : Type*} [Finite ι] (E : CondExpSystem ℂ V) {x : ℕ → ι → V}
    (hx : IsStableProc x) (k : ℕ) : IsStableProc fun t => Evec E t (x (t + k)) := by
  have := Fintype.ofFinite ι
  obtain ⟨K, -, hK⟩ := klS_stable_bound hx
  exact klS_stable_of_le fun t => (klS_norm_Evec_le E t _).trans (hK _)

omit [NormedSpace ℂ V] in
theorem klS_stable_shift {ι : Type*} {x : ℕ → ι → V} (hx : IsStableProc x) (k : ℕ) :
    IsStableProc fun t => x (t + k) := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t => h _⟩

omit [NormedSpace ℂ V] in
theorem klS_stable_comp {ι κ : Type*} {x : ℕ → ι → V} (hx : IsStableProc x) (f : κ → ι) :
    IsStableProc fun t => x t ∘ f := by
  obtain ⟨M, hM, h⟩ := hx
  exact ⟨M, hM, fun t i => h t (f i)⟩

omit [NormedSpace ℂ V] in
theorem klS_stable_append {a b : ℕ} {s : ℕ → Fin a → V} {u : ℕ → Fin b → V}
    (hs : IsStableProc s) (hu : IsStableProc u) :
    IsStableProc fun t => Fin.append (s t) (u t) := by
  obtain ⟨K, hK, hs⟩ := hs
  obtain ⟨L, hL, hu⟩ := hu
  refine ⟨K + L, by positivity, fun t i => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change ‖Fin.append (s t) (u t) (Fin.castAdd b i)‖ < K + L
    rw [Fin.append_left]
    linarith [hs t i]
  · change ‖Fin.append (s t) (u t) (Fin.natAdd a i)‖ < K + L
    rw [Fin.append_right]
    linarith [hu t i]

/-! ### Matrix norms -/

theorem klS_entry_le_mclm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i k : Fin m) :
    ‖M i k‖ ≤ ‖mclm M‖ := by
  have h1 : (M *ᵥ Pi.single k 1) i = M i k := by simp [Matrix.mulVec_single]
  have h2 : ‖(Pi.single k (1 : ℂ) : Fin m → ℂ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
      by_cases hj : j = k
      · subst hj
        simp
      · simp [hj]
  calc ‖M i k‖ = ‖(M *ᵥ Pi.single k 1) i‖ := by rw [h1]
    _ ≤ ‖M *ᵥ Pi.single k 1‖ := norm_le_pi_norm _ i
    _ ≤ ‖mclm M‖ * ‖(Pi.single k (1 : ℂ) : Fin m → ℂ)‖ := norm_mulVec_le _ _
    _ ≤ ‖mclm M‖ := mul_le_of_le_one_right (norm_nonneg _) h2

theorem klS_ent_le_mclm {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    klS_ent M ≤ (m * m : ℝ) * ‖mclm M‖ := by
  calc klS_ent M ≤ ∑ _i : Fin m, ∑ _j : Fin m, ‖mclm M‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => klS_entry_le_mclm M i j
    _ = (m * m : ℝ) * ‖mclm M‖ := by simp [Finset.sum_const, mul_assoc]

theorem klS_summable_ent {m : ℕ} {N : Matrix (Fin m) (Fin m) ℂ}
    (h : Summable fun j => ‖mclm (N ^ j)‖) : Summable fun j => klS_ent (N ^ j) :=
  Summable.of_nonneg_of_le (fun _ => klS_ent_nonneg _) (fun _ => klS_ent_le_mclm _)
    (h.mul_left _)

/-! ### The forward solution -/

/-- The forward sum `∑ⱼ Nʲ E_t w_{t+j}`. -/
noncomputable def klS_fwd (E : CondExpSystem ℂ V) {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ)
    (w : ℕ → Fin m → V) (t : ℕ) : Fin m → V :=
  ∑' j, matAct (N ^ j) (Evec E t (w (t + j)))

theorem klS_fwd_summable [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (t : ℕ) :
    Summable fun j => matAct (N ^ j) (Evec E t (w (t + j))) :=
  Summable.of_norm_bounded (hN.mul_right W) fun _ => (klS_norm_matAct_le _ _).trans
    (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hw _)) (klS_ent_nonneg _))

theorem klS_norm_fwd_le [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (t : ℕ) :
    ‖klS_fwd E N w t‖ ≤ (∑' j, klS_ent (N ^ j)) * W := by
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded (hN.mul_right W).hasSum fun j => (klS_norm_matAct_le _ _).trans
    (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hw _)) (klS_ent_nonneg _))

/-- The forward sum is adapted: `E_t u_t = u_t`. -/
theorem klS_fwd_adapted [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (t : ℕ) :
    Evec E t (klS_fwd E N w t) = klS_fwd E N w t := by
  unfold klS_fwd
  rw [← klS_EvecCLM_apply, (klS_EvecCLM E t (Fin m)).map_tsum (klS_fwd_summable E hN hw t)]
  simp only [klS_EvecCLM_apply, Evec_matAct, klS_Evec_idem]

/-- The forward sum solves `u_t = N E_t u_{t+1} + w_t` for adapted `w`. -/
theorem klS_fwd_rec [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) (hwa : ∀ t, Evec E t (w t) = w t)
    (t : ℕ) : klS_fwd E N w t = matAct N (Evec E t (klS_fwd E N w (t + 1))) + w t := by
  have h1 : Evec E t (klS_fwd E N w (t + 1)) =
      ∑' j, matAct (N ^ j) (Evec E t (w (t + 1 + j))) := by
    unfold klS_fwd
    rw [← klS_EvecCLM_apply, (klS_EvecCLM E t (Fin m)).map_tsum
      (klS_fwd_summable E hN hw (t + 1))]
    simp only [klS_EvecCLM_apply, Evec_matAct, klS_Evec_tower_le E (Nat.le_succ t)]
  have hs : Summable fun j => matAct (N ^ j) (Evec E t (w (t + 1 + j))) :=
    Summable.of_norm_bounded (hN.mul_right W) fun _ => (klS_norm_matAct_le _ _).trans
      (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hw _)) (klS_ent_nonneg _))
  rw [h1, ← klS_matCLM_apply, (klS_matCLM N).map_tsum hs]
  unfold klS_fwd
  rw [(klS_fwd_summable E hN hw t).tsum_eq_zero_add]
  simp only [klS_matCLM_apply, matAct_mul, pow_zero, matAct_one, add_zero, hwa]
  rw [add_comm]
  congr 1
  refine tsum_congr fun j => ?_
  rw [← pow_succ', show t + (j + 1) = t + 1 + j by ring]

/-- Any stable adapted solution of `u_t = N E_t u_{t+1} + w_t` is the forward sum, when the powers
of `N` are summable. -/
theorem klS_eq_fwd [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {N : Matrix (Fin m) (Fin m) ℂ} (hN : Summable fun j => klS_ent (N ^ j))
    {w : ℕ → Fin m → V} {W : ℝ} (hw : ∀ t, ‖w t‖ ≤ W) {u : ℕ → Fin m → V}
    (hu : IsStableProc u) (hua : ∀ t, Evec E t (u t) = u t)
    (hrec : ∀ t, u t = matAct N (Evec E t (u (t + 1))) + w t) (t : ℕ) :
    u t = klS_fwd E N w t := by
  have hiter : ∀ J, u t = matAct (N ^ J) (Evec E t (u (t + J))) +
      ∑ j ∈ Finset.range J, matAct (N ^ j) (Evec E t (w (t + j))) := by
    intro J
    induction J with
    | zero => simp [hua, matAct_one]
    | succ J ih =>
      have e : Evec E t (u (t + J)) = matAct N (Evec E t (u (t + J + 1))) +
          Evec E t (w (t + J)) := by
        rw [hrec (t + J), klS_Evec_add, Evec_matAct, klS_Evec_tower_le E (by omega)]
      rw [ih, e, matAct_add, matAct_mul, ← pow_succ, Finset.sum_range_succ,
        show t + J + 1 = t + (J + 1) by ring]
      abel
  obtain ⟨U₀, -, hU₀⟩ := klS_stable_bound hu
  have h1 : Tendsto (fun J => matAct (N ^ J) (Evec E t (u (t + J)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun J => (klS_norm_matAct_le _ _).trans
      (mul_le_mul_of_nonneg_left ((klS_norm_Evec_le E t _).trans (hU₀ _))
        (klS_ent_nonneg _))) ?_
    simpa using hN.tendsto_atTop_zero.mul_const U₀
  have h2 := (klS_fwd_summable E hN hw t).hasSum.tendsto_sum_nat
  have h3 := h1.add h2
  rw [zero_add] at h3
  exact tendsto_nhds_unique (tendsto_const_nhds.congr hiter) h3

/-- The backward recursion `s_{t+1} = Ms_t + v_t` with stable `v` and summable powers of `M` has
stable solutions. -/
theorem klS_stable_of_rec {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : Summable fun j => klS_ent (M ^ j)) {v s : ℕ → Fin m → V} (hv : IsStableProc v)
    (hrec : ∀ t, s (t + 1) = matAct M (s t) + v t) : IsStableProc s := by
  have hform : ∀ t, s t = matAct (M ^ t) (s 0) +
      ∑ j ∈ Finset.range t, matAct (M ^ j) (v (t - 1 - j)) := by
    intro t
    induction t with
    | zero => simp [matAct_one]
    | succ t ih =>
      rw [hrec, ih, matAct_add, matAct_mul, ← pow_succ', klS_matAct_sum,
        Finset.sum_range_succ' _ t]
      simp only [matAct_mul, ← pow_succ', pow_zero, matAct_one]
      rw [add_assoc]
      congr 2
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega]
  obtain ⟨Vb, hV0, hV⟩ := klS_stable_bound hv
  set σ := ∑' j, klS_ent (M ^ j)
  have hσ : ∀ t, klS_ent (M ^ t) ≤ σ := fun t =>
    hM.le_tsum t fun j _ => klS_ent_nonneg _
  refine klS_stable_of_le (K := σ * ‖s 0‖ + σ * Vb) fun t => ?_
  rw [hform t]
  refine (norm_add_le _ _).trans (add_le_add ((klS_norm_matAct_le _ _).trans
    (mul_le_mul_of_nonneg_right (hσ t) (norm_nonneg _))) ?_)
  calc ‖∑ j ∈ Finset.range t, matAct (M ^ j) (v (t - 1 - j))‖
      ≤ ∑ j ∈ Finset.range t, klS_ent (M ^ j) * Vb := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => (klS_norm_matAct_le _ _).trans
          (mul_le_mul_of_nonneg_left (hV _) (klS_ent_nonneg _)))
    _ = (∑ j ∈ Finset.range t, klS_ent (M ^ j)) * Vb := by rw [Finset.sum_mul]
    _ ≤ σ * Vb := mul_le_mul_of_nonneg_right
        (hM.sum_le_tsum _ fun j _ => klS_ent_nonneg _) hV0

/-! ### The transformed system in blocks -/

omit [NormedSpace ℂ V] in
theorem klS_norm_comp_le {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → V) (f : κ → ι) :
    ‖v ∘ f‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm v (f i)

/-- Miao, p. 56 (the analogue of (1.36) for (2.11)): with `S`, `T` upper triangular,
`S E_t x*_{t+1} = T x*_t + c_t` splits into the `s`-block
`S₁₁E_t s_{t+1} + S₁₂E_t u_{t+1} = T₁₁s_t + T₁₂u_t + c¹_t` and the `u`-block
`S₂₂E_t u_{t+1} = T₂₂u_t + c²_t` (here `y' = E_t x*_{t+1}`). -/
theorem klS_blocks_iff {a b : ℕ} {S T : Matrix (Fin (a + b)) (Fin (a + b)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular) (y y' c : Fin (a + b) → V) :
    matAct S y' = matAct T y + c ↔
      (matAct (S.submatrix (Fin.castAdd b) (Fin.castAdd b)) (y' ∘ Fin.castAdd b) +
          matAct (S.submatrix (Fin.castAdd b) (Fin.natAdd a)) (y' ∘ Fin.natAdd a) =
        matAct (T.submatrix (Fin.castAdd b) (Fin.castAdd b)) (y ∘ Fin.castAdd b) +
          matAct (T.submatrix (Fin.castAdd b) (Fin.natAdd a)) (y ∘ Fin.natAdd a) +
            c ∘ Fin.castAdd b) ∧
      matAct (S.submatrix (Fin.natAdd a) (Fin.natAdd a)) (y' ∘ Fin.natAdd a) =
        matAct (T.submatrix (Fin.natAdd a) (Fin.natAdd a)) (y ∘ Fin.natAdd a) +
          c ∘ Fin.natAdd a := by
  have e1 : (matAct T y + c) ∘ Fin.castAdd b = matAct T y ∘ Fin.castAdd b + c ∘ Fin.castAdd b :=
    rfl
  have e2 : (matAct T y + c) ∘ Fin.natAdd a = matAct T y ∘ Fin.natAdd a + c ∘ Fin.natAdd a :=
    rfl
  constructor
  · intro h
    have h1 : matAct S y' ∘ Fin.castAdd b = (matAct T y + c) ∘ Fin.castAdd b := by rw [h]
    have h2 : matAct S y' ∘ Fin.natAdd a = (matAct T y + c) ∘ Fin.natAdd a := by rw [h]
    rw [e1, klS_matAct_blocks, klS_matAct_blocks] at h1
    rw [e2, klS_matAct_natAdd hS, klS_matAct_natAdd hT] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine klS_ext_blocks ?_ ?_
    · rw [e1, klS_matAct_blocks, klS_matAct_blocks]
      exact h1
    · rw [e2, klS_matAct_natAdd hS, klS_matAct_natAdd hT]
      exact h2

/-- Solving the `u`-block for `u_t` (Miao, p. 56): with `T₂₂` invertible,
`S₂₂a = T₂₂u + d` iff `u = T₂₂⁻¹S₂₂a − T₂₂⁻¹d` (with `a = E_t u_{t+1}`, `d = c²_t`). -/
theorem klS_solve_fwd {m : ℕ} {S22 T22 : Matrix (Fin m) (Fin m) ℂ} (h : T22.det ≠ 0)
    (u a d : Fin m → V) :
    matAct S22 a = matAct T22 u + d ↔ u = matAct (T22⁻¹ * S22) a + -matAct T22⁻¹ d := by
  constructor
  · intro e
    rw [← matAct_mul, e, matAct_add, klS_matAct_inv_mul h]
    abel
  · intro e
    rw [e, matAct_add, klS_matAct_neg, ← matAct_mul, klS_matAct_mul_inv h, klS_matAct_mul_inv h]
    abel

/-- Miao, p. 56 ("We replace equation (1.38) with"): solving the `s`-block for `E_t s_{t+1}`,
`E_t s_{t+1} = S₁₁⁻¹T₁₁s_t + S₁₁⁻¹T₁₂u_t − S₁₁⁻¹S₁₂E_t u_{t+1} + S₁₁⁻¹Q₁Cz_t`. Here `Es'`, `Eu'`
stand for `E_t s_{t+1}`, `E_t u_{t+1}` and `c` for `Q₁Cz_t`. The printed formula is correct. -/
theorem eq_klein_Es {m p : ℕ} {S11 T11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 : Matrix (Fin m) (Fin p) ℂ} (h : S11.det ≠ 0) (s Es' c : Fin m → V)
    (u Eu' : Fin p → V) :
    matAct S11 Es' + matAct S12 Eu' = matAct T11 s + matAct T12 u + c ↔
      Es' = matAct (S11⁻¹ * T11) s + matAct (S11⁻¹ * T12) u - matAct (S11⁻¹ * S12) Eu' +
        matAct S11⁻¹ c := by
  have hI : S11 * S11⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)
  constructor
  · intro e
    have e' : matAct S11 Es' = matAct T11 s + matAct T12 u + c - matAct S12 Eu' := by
      rw [← e]
      abel
    calc Es' = matAct S11⁻¹ (matAct S11 Es') := (klS_matAct_inv_mul h Es').symm
      _ = _ := by
        rw [e']
        simp only [klS_matAct_sub, matAct_add, matAct_mul]
        abel
  · intro e
    rw [e]
    simp only [klS_matAct_sub, matAct_add, matAct_mul, ← Matrix.mul_assoc, hI, Matrix.one_mul,
      matAct_one]
    abel

/-- Miao, p. 57: since `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}`, its prediction error is
`ξ_{t+1} = k_{t+1} − E_t k_{t+1} = Z₁₁(s_{t+1} − E_t s_{t+1}) + Z₁₂(u_{t+1} − E_t u_{t+1})`. -/
theorem eq_klein_xi (E : CondExpSystem ℂ V) (t : ℕ) {m p : ℕ} (Z11 : Matrix (Fin m) (Fin m) ℂ)
    (Z12 : Matrix (Fin m) (Fin p) ℂ) (s' : Fin m → V) (u' : Fin p → V) :
    matAct Z11 s' + matAct Z12 u' - Evec E t (matAct Z11 s' + matAct Z12 u') =
      matAct Z11 (s' - Evec E t s') + matAct Z12 (u' - Evec E t u') := by
  rw [klS_Evec_add, Evec_matAct, Evec_matAct, klS_matAct_sub, klS_matAct_sub]
  abel

/-- Miao, p. 56, `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}` (and `y_{t+1} = Z₂₁s_{t+1} + Z₂₂u_{t+1}`),
from `x = Zx*` with `x* = (s, u)`. -/
theorem eq_klein_k {nk ny : ℕ} (Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ)
    (xs : Fin (nk + ny) → V) :
    matAct Z xs ∘ Fin.castAdd ny =
        matAct (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)) (xs ∘ Fin.castAdd ny) +
          matAct (Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk)) (xs ∘ Fin.natAdd nk) ∧
      matAct Z xs ∘ Fin.natAdd nk =
        matAct (Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny)) (xs ∘ Fin.castAdd ny) +
          matAct (Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk)) (xs ∘ Fin.natAdd nk) :=
  ⟨klS_matAct_blocks Z _ xs, klS_matAct_blocks Z _ xs⟩

/-- Miao, p. 57: in a solution, the predetermined block gives
`s_{t+1} = S₁₁⁻¹T₁₁s_t + S₁₁⁻¹T₁₂u_t − S₁₁⁻¹S₁₂E_t u_{t+1} + S₁₁⁻¹Q₁Cz_t
  − Z₁₁⁻¹Z₁₂(u_{t+1} − E_t u_{t+1}) + Z₁₁⁻¹ξ_{t+1}`
from the `s`-block `h1` and the prediction error `h2` of `k_{t+1} = Z₁₁s_{t+1} + Z₁₂u_{t+1}`
(`Es'`, `Eu'` stand for `E_t s_{t+1}`, `E_t u_{t+1}`). The printed formula is correct, every term
and sign included. -/
theorem eq_klein_s {m p : ℕ} {S11 T11 Z11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 Z12 : Matrix (Fin m) (Fin p) ℂ} (hS11 : S11.det ≠ 0) (hZ11 : Z11.det ≠ 0)
    {s s' Es' c ξ' : Fin m → V} {u u' Eu' : Fin p → V}
    (h1 : matAct S11 Es' + matAct S12 Eu' = matAct T11 s + matAct T12 u + c)
    (h2 : matAct Z11 s' + matAct Z12 u' - (matAct Z11 Es' + matAct Z12 Eu') = ξ') :
    s' = matAct (S11⁻¹ * T11) s + (matAct (S11⁻¹ * T12) u - matAct (S11⁻¹ * S12) Eu' +
      matAct S11⁻¹ c - matAct (Z11⁻¹ * Z12) (u' - Eu') + matAct Z11⁻¹ ξ') := by
  have hEs := (eq_klein_Es hS11 s Es' c u Eu').1 h1
  have h3 : matAct Z11 (s' - Es') = ξ' - matAct Z12 (u' - Eu') := by
    rw [klS_matAct_sub, klS_matAct_sub, ← h2]
    abel
  have h4 : s' - Es' = matAct Z11⁻¹ (ξ' - matAct Z12 (u' - Eu')) := by
    rw [← h3, klS_matAct_inv_mul hZ11]
  calc s' = Es' + (s' - Es') := by abel
    _ = _ := by
      rw [h4, hEs, klS_matAct_sub Z11⁻¹ ξ', matAct_mul]
      abel

/-! ### The core: existence and uniqueness in the transformed coordinates -/

/-- Klein's construction for (2.11) in the transformed coordinates `x* = (s, u)`, written in
blocks (Miao, pp. 56–57). With `S₁₁`, `T₂₂`, `Z₁₁` invertible and the powers of `S₁₁⁻¹T₁₁`,
`T₂₂⁻¹S₂₂` summable, for stable adapted forcing `c¹, c²`, a stable adapted prediction error `ξ`
with `E_t ξ_{t+1} = 0` and an `F₀`-measurable `k₀`, there is exactly one stable adapted `(s, u)`
solving both blocks, with `k = Z₁₁s + Z₁₂u` having prediction error `ξ` and `k₀` as initial
value. -/
theorem klS_core_blocks [CompleteSpace V] (E : CondExpSystem ℂ V) {m p : ℕ}
    {S11 T11 Z11 : Matrix (Fin m) (Fin m) ℂ} {S12 T12 Z12 : Matrix (Fin m) (Fin p) ℂ}
    {S22 T22 : Matrix (Fin p) (Fin p) ℂ} (hS11 : S11.det ≠ 0) (hT22 : T22.det ≠ 0)
    (hZ11 : Z11.det ≠ 0) (hMs : Summable fun j => klS_ent ((S11⁻¹ * T11) ^ j))
    (hN : Summable fun j => klS_ent ((T22⁻¹ * S22) ^ j))
    {c1 : ℕ → Fin m → V} {c2 : ℕ → Fin p → V} (hc1 : IsStableProc c1) (hc2 : IsStableProc c2)
    (hc1a : ∀ t, Evec E t (c1 t) = c1 t) (hc2a : ∀ t, Evec E t (c2 t) = c2 t)
    {ξ : ℕ → Fin m → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t, Evec E (t + 1) (ξ (t + 1)) = ξ (t + 1)) (hξm : ∀ t, Evec E t (ξ (t + 1)) = 0)
    (k₀ : Fin m → V) (hk₀ : Evec E 0 k₀ = k₀) :
    ∃! su : (ℕ → Fin m → V) × (ℕ → Fin p → V),
      (∀ t, matAct S11 (Evec E t (su.1 (t + 1))) + matAct S12 (Evec E t (su.2 (t + 1))) =
        matAct T11 (su.1 t) + matAct T12 (su.2 t) + c1 t) ∧
      (∀ t, matAct S22 (Evec E t (su.2 (t + 1))) = matAct T22 (su.2 t) + c2 t) ∧
      IsStableProc su.1 ∧ IsStableProc su.2 ∧
      (∀ t, Evec E t (su.1 t) = su.1 t) ∧ (∀ t, Evec E t (su.2 t) = su.2 t) ∧
      (∀ t, matAct Z11 (su.1 (t + 1)) + matAct Z12 (su.2 (t + 1)) -
        Evec E t (matAct Z11 (su.1 (t + 1)) + matAct Z12 (su.2 (t + 1))) = ξ (t + 1)) ∧
      matAct Z11 (su.1 0) + matAct Z12 (su.2 0) = k₀ := by
  -- Step 1, (2.17): the forward solution for `u`
  obtain ⟨Cb, -, hCb⟩ := klS_stable_bound hc2
  have hW : ∀ t, ‖-matAct T22⁻¹ (c2 t)‖ ≤ klS_ent T22⁻¹ * Cb := fun t => by
    rw [norm_neg]
    exact (klS_norm_matAct_le _ _).trans (mul_le_mul_of_nonneg_left (hCb t) (klS_ent_nonneg _))
  have hwa : ∀ t, Evec E t (-matAct T22⁻¹ (c2 t)) = -matAct T22⁻¹ (c2 t) := fun t => by
    rw [klS_Evec_neg, Evec_matAct, hc2a]
  obtain ⟨uF, huFd⟩ : ∃ uF : ℕ → Fin p → V,
      ∀ t, uF t = klS_fwd E (T22⁻¹ * S22) (fun t => -matAct T22⁻¹ (c2 t)) t := ⟨_, fun _ => rfl⟩
  have huF : ∀ t, uF t = matAct (T22⁻¹ * S22) (Evec E t (uF (t + 1))) +
      -matAct T22⁻¹ (c2 t) := fun t => by
    rw [huFd, huFd]
    exact klS_fwd_rec E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW hwa t
  have huFa : ∀ t, Evec E t (uF t) = uF t := fun t => by
    rw [huFd]
    exact klS_fwd_adapted E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW t
  have huFs : IsStableProc uF := klS_stable_of_le fun t => by
    rw [huFd]
    exact klS_norm_fwd_le E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW t
  -- Step 2: the backward recursion for `s`
  obtain ⟨v, hvd⟩ : ∃ v : ℕ → Fin m → V, ∀ t, v t = matAct (S11⁻¹ * T12) (uF t) -
      matAct (S11⁻¹ * S12) (Evec E t (uF (t + 1))) + matAct S11⁻¹ (c1 t) -
      matAct (Z11⁻¹ * Z12) (uF (t + 1) - Evec E t (uF (t + 1))) + matAct Z11⁻¹ (ξ (t + 1)) :=
    ⟨_, fun _ => rfl⟩
  have hvs : IsStableProc v := by
    have := klS_stable_add (klS_stable_sub (klS_stable_add (klS_stable_sub
      (klS_stable_matAct huFs (S11⁻¹ * T12))
      (klS_stable_matAct (klS_stable_Evec E huFs 1) (S11⁻¹ * S12)))
      (klS_stable_matAct hc1 S11⁻¹))
      (klS_stable_matAct (klS_stable_sub (klS_stable_shift huFs 1) (klS_stable_Evec E huFs 1))
        (Z11⁻¹ * Z12)))
      (klS_stable_matAct (klS_stable_shift hξ 1) Z11⁻¹)
    rw [show v = _ from funext hvd]
    exact this
  have hEv : ∀ t, Evec E t (v t) = matAct (S11⁻¹ * T12) (uF t) -
      matAct (S11⁻¹ * S12) (Evec E t (uF (t + 1))) + matAct S11⁻¹ (c1 t) := fun t => by
    rw [hvd]
    simp only [klS_Evec_add, klS_Evec_sub, Evec_matAct, huFa t, klS_Evec_idem, hc1a t, hξm t,
      sub_self, klS_matAct_zero, sub_zero, add_zero]
  have hva : ∀ t, Evec E (t + 1) (v t) = v t := fun t => by
    rw [hvd]
    simp only [klS_Evec_add, klS_Evec_sub, Evec_matAct, klS_adapted_succ E (huFa t),
      klS_Evec_tower_ge E (Nat.le_add_right t 1), klS_adapted_succ E (hc1a t), huFa (t + 1),
      hξa t]
  obtain ⟨sF, hsF0, hsF⟩ : ∃ sF : ℕ → Fin m → V,
      sF 0 = matAct Z11⁻¹ (k₀ - matAct Z12 (uF 0)) ∧
        ∀ t, sF (t + 1) = matAct (S11⁻¹ * T11) (sF t) + v t :=
    ⟨fun t => Nat.rec (matAct Z11⁻¹ (k₀ - matAct Z12 (uF 0)))
      (fun t st => matAct (S11⁻¹ * T11) st + v t) t, rfl, fun _ => rfl⟩
  have hsFs : IsStableProc sF := klS_stable_of_rec hMs hvs hsF
  have hsFa : ∀ t, Evec E t (sF t) = sF t := by
    intro t
    induction t with
    | zero => rw [hsF0, Evec_matAct, klS_Evec_sub, Evec_matAct, hk₀, huFa 0]
    | succ t ih => rw [hsF, klS_Evec_add, Evec_matAct, klS_adapted_succ E ih, hva]
  have hEs : ∀ t, Evec E t (sF (t + 1)) = matAct (S11⁻¹ * T11) (sF t) +
      (matAct (S11⁻¹ * T12) (uF t) - matAct (S11⁻¹ * S12) (Evec E t (uF (t + 1))) +
        matAct S11⁻¹ (c1 t)) := fun t => by
    rw [hsF, klS_Evec_add, Evec_matAct, hsFa, hEv]
  refine ⟨(sF, uF), ⟨fun t => ?_, fun t => ?_, hsFs, huFs, hsFa, huFa, fun t => ?_, ?_⟩, ?_⟩
  · -- the `s`-block
    refine (eq_klein_Es hS11 _ _ _ _ _).2 ?_
    rw [hEs]
    abel
  · -- the `u`-block
    exact (klS_solve_fwd hT22 _ _ _).2 (huF t)
  · -- the prediction error of `k`
    dsimp only
    rw [eq_klein_xi, hEs, hsF, hvd]
    rw [show ∀ (a P Q R : Fin m → V), a + (P - Q + R) - (a + P) = R - Q from
      fun a P Q R => by abel]
    rw [klS_matAct_sub Z11 (matAct Z11⁻¹ (ξ (t + 1))), klS_matAct_mul_inv hZ11, matAct_mul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hZ11), Matrix.one_mul]
    abel
  · -- the initial condition
    dsimp only
    rw [hsF0, klS_matAct_mul_inv hZ11, sub_add_cancel]
  · -- uniqueness
    rintro ⟨s, u⟩ ⟨h1, h2, -, hus, -, hua, hp, h0⟩
    dsimp only at h1 h2 hus hua hp h0
    have hu : ∀ t, u t = uF t := fun t => by
      rw [huFd]
      exact klS_eq_fwd E hN (w := fun t => -matAct T22⁻¹ (c2 t)) hW hus hua
        (fun t => (klS_solve_fwd hT22 _ _ _).1 (h2 t)) t
    have hs : ∀ t, s t = sF t := by
      intro t
      induction t with
      | zero => rw [hsF0, ← h0, hu 0, add_sub_cancel_right, klS_matAct_inv_mul hZ11]
      | succ t ih =>
        have hp' := hp t
        rw [klS_Evec_add, Evec_matAct, Evec_matAct] at hp'
        rw [eq_klein_s hS11 hZ11 (h1 t) hp', hsF, hvd, ih]
        simp only [hu]
    exact Prod.ext (funext hs) (funext hu)

/-- Klein's construction for (2.11) in the transformed coordinates `x* = Zᴴx` (Miao, pp. 56–57):
with `S`, `T` upper triangular, the first `n_k` pairs stable and the rest unstable (none on the
unit circle) and `Z₁₁` invertible, there is exactly one stable adapted `y` with
`S E_t y_{t+1} = T y_t + c_t` whose block `k = (Zy)_K` has prediction error `ξ` and `k₀ = k₀`. -/
theorem klS_core [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny : ℕ}
    {S T Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖T i i‖ < ‖S i i‖)
    (hdiag : ∀ i, ‖T i i‖ ≠ ‖S i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    {c : ℕ → Fin (nk + ny) → V} (hc : IsStableProc c) (hca : ∀ t, Evec E t (c t) = c t)
    {ξ : ℕ → Fin nk → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t, Evec E (t + 1) (ξ (t + 1)) = ξ (t + 1)) (hξm : ∀ t, Evec E t (ξ (t + 1)) = 0)
    (k₀ : Fin nk → V) (hk₀ : Evec E 0 k₀ = k₀) :
    ∃! y : ℕ → Fin (nk + ny) → V,
      (∀ t, matAct S (Evec E t (y (t + 1))) = matAct T (y t) + c t) ∧ IsStableProc y ∧
      (∀ t, Evec E t (y t) = y t) ∧
      (∀ t, matAct Z (y (t + 1)) ∘ Fin.castAdd ny -
        Evec E t (matAct Z (y (t + 1)) ∘ Fin.castAdd ny) = ξ (t + 1)) ∧
      matAct Z (y 0) ∘ Fin.castAdd ny = k₀ := by
  obtain ⟨⟨s, u⟩, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, huniq⟩ := klS_core_blocks E
    (det_S11_ne_zero hS hord) (det_T22_ne_zero hT hord hdiag) hZ11
    (klS_summable_ent (summable_Ms hS hT hord)) (klS_summable_ent (summable_Mu hS hT hord hdiag))
    (c1 := fun t => c t ∘ Fin.castAdd ny) (c2 := fun t => c t ∘ Fin.natAdd nk)
    (klS_stable_comp hc _) (klS_stable_comp hc _)
    (fun t => by rw [klS_Evec_comp, hca]) (fun t => by rw [klS_Evec_comp, hca]) hξ hξa hξm k₀ hk₀
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨fun t => Fin.append (s t) (u t), ⟨fun t => ?_, klS_stable_append h3 h4, fun t => ?_,
    fun t => ?_, ?_⟩, ?_⟩
  · dsimp only
    rw [klS_Evec_append, klS_blocks_iff hS hT]
    simp only [klS_append_castAdd, klS_append_natAdd]
    exact ⟨h1 t, h2 t⟩
  · dsimp only
    rw [klS_Evec_append, h5, h6]
  · dsimp only
    rw [klS_matAct_blocks Z (Fin.castAdd ny)]
    simp only [klS_append_castAdd, klS_append_natAdd]
    exact h7 t
  · dsimp only
    rw [klS_matAct_blocks Z (Fin.castAdd ny)]
    simp only [klS_append_castAdd, klS_append_natAdd]
    exact h8
  · rintro y ⟨hy1, hy2, hy3, hy4, hy5⟩
    have hb := fun t => (klS_blocks_iff hS hT (y t) (Evec E t (y (t + 1))) (c t)).1 (hy1 t)
    have := huniq (fun t => y t ∘ Fin.castAdd ny, fun t => y t ∘ Fin.natAdd nk)
      ⟨fun t => (hb t).1, fun t => (hb t).2, klS_stable_comp hy2 _, klS_stable_comp hy2 _,
        fun t => by
          change Evec E t (y t ∘ Fin.castAdd ny) = y t ∘ Fin.castAdd ny
          rw [klS_Evec_comp, hy3],
        fun t => by
          change Evec E t (y t ∘ Fin.natAdd nk) = y t ∘ Fin.natAdd nk
          rw [klS_Evec_comp, hy3],
        fun t => by
          have := hy4 t
          rw [klS_matAct_blocks Z (Fin.castAdd ny)] at this
          exact this,
        by
          have := hy5
          rw [klS_matAct_blocks Z (Fin.castAdd ny)] at this
          exact this⟩
    funext t
    refine klS_ext_blocks ?_ ?_
    · rw [klS_append_castAdd]
      exact congrFun (congrArg Prod.fst this) t
    · rw [klS_append_natAdd]
      exact congrFun (congrArg Prod.snd this) t

/-- The unitary change of variables `x* = Zᴴx` (Miao, p. 56, as on p. 25): `x` solves (2.11) iff
`S E_t x*_{t+1} = T x*_t + QCz_t` with `S = QAZ`, `T = QBZ`. -/
theorem klS_isRESolution_iff (E : CondExpSystem ℂ V) {n nz : ℕ} {A B Q Z : Matrix (Fin n) (Fin n) ℂ}
    {C : Matrix (Fin n) (Fin nz) ℂ} (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (z : ℕ → Fin nz → V) (x : ℕ → Fin n → V) :
    IsRESolution E A B C z x ↔ ∀ t, matAct (Q * A * Z) (Evec E t (matAct (star Z) (x (t + 1)))) =
      matAct (Q * B * Z) (matAct (star Z) (x t)) + matAct Q (matAct C (z t)) := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hQQ : star Q * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → V),
      matAct (Q * M * Z) (matAct (star Z) v) = matAct Q (matAct M v) := fun M v => by
    simp only [matAct_mul, Matrix.mul_assoc, hZZ, Matrix.mul_one]
  simp only [IsRESolution, Evec_matAct, key, ← matAct_add]
  refine forall_congr' fun t => ⟨fun h => by rw [h], fun h => ?_⟩
  have := congrArg (matAct (star Q)) h
  simpa only [matAct_mul, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, matAct_one] using this

/-- **Klein's theorem for (2.11)** (Miao, §2.3.2, pp. 56–57). Let `(A, B)` be regular, with QZ
form `S = QAZ`, `T = QBZ` whose stable generalized eigenvalues come first (`theorem_1_4_4_stable`),
and partition `x_t = (k_t, y_t)` with `k_t` the first `n_k` coordinates. Suppose, as in
Theorem 1.4.5, (i) `n_s = n_k` (`hord`), (ii) `Z₁₁` invertible, (iii) no generalized eigenvalue
on the unit circle. Let `{z_t}` be stable and adapted, `{ξ_t}` a stable martingale difference
process with `ξ_{t+1}` `F_{t+1}`-measurable, and `k₀` `F₀`-measurable. Then (2.11) has exactly
one stable adapted solution such that `{k_t}` is predetermined with prediction error `{ξ_t}`
(Definition 2.3.4) and `k₀` is the given one. -/
theorem klein_stochastic [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1)
    {z : ℕ → Fin nz → V} (hz : IsStableProc z) (hza : IsAdaptedV E z)
    {ξ : ℕ → Fin nk → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t i, E.E (t + 1) (ξ (t + 1) i) = ξ (t + 1) i)
    (hξm : IsMartingaleDiffProc E ξ) (k₀ : Fin nk → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) :
    ∃! x : ℕ → Fin (nk + ny) → V,
      IsRESolution E A B C z x ∧ IsStableProc x ∧ IsAdaptedV E x ∧
      IsPredeterminedKlein E ξ (fun t i => x t (Fin.castAdd ny i)) ∧
      ∀ i, x 0 (Fin.castAdd ny i) = k₀ i := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hZ
  have hza' : ∀ t, Evec E t (z t) = z t := fun t => funext (hza t)
  obtain ⟨y, ⟨hy1, hy2, hy3, hy4, hy5⟩, hyu⟩ := klS_core E hS hT hord
    (diag_off_circle hreg hQ hZ hS hT hcirc) hZ11 (c := fun t => matAct Q (matAct C (z t)))
    (klS_stable_matAct (klS_stable_matAct hz C) Q)
    (fun t => by rw [Evec_matAct, Evec_matAct, hza']) hξ (fun t => funext (hξa t))
    (fun t => funext (hξm t)) k₀ (funext hk₀)
  have hback : ∀ v : Fin (nk + ny) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  refine ⟨fun t => matAct Z (y t), ⟨(klS_isRESolution_iff E hQ hZ z _).2 fun t => ?_,
    klS_stable_matAct hy2 Z, fun t i => ?_, ⟨fun t i => congrFun (hy4 t) i, hξm, fun i => ?_⟩,
    fun i => congrFun hy5 i⟩, ?_⟩
  · simpa only [matAct_mul, hZZ', matAct_one] using hy1 t
  · change Evec E t (matAct Z (y t)) i = matAct Z (y t) i
    rw [Evec_matAct, hy3]
  · change E.E 0 (matAct Z (y 0) (Fin.castAdd ny i)) = matAct Z (y 0) (Fin.castAdd ny i)
    have h := congrFun hy5 i
    simp only [Function.comp_apply] at h
    rw [h, hk₀ i]
  · rintro x ⟨hx1, hx2, hx3, ⟨hx4, -, -⟩, hx5⟩
    have := hyu (fun t => matAct (star Z) (x t)) ⟨(klS_isRESolution_iff E hQ hZ z x).1 hx1,
      klS_stable_matAct hx2 _, fun t => by
        rw [Evec_matAct, show Evec E t (x t) = x t from funext (hx3 t)],
      fun t => by
        simp only [hback]
        funext i
        exact hx4 t i,
      by
        simp only [hback]
        funext i
        exact hx5 i⟩
    funext t
    simp only [← this, hback]

/-! ### Real data -/

/-- A real matrix commutes with a conjugation of `V`. -/
theorem klS_cj_matAct {ι κ : Type*} [Fintype κ] (cj : V →ₗ⋆[ℂ] V) (M : Matrix ι κ ℝ)
    (v : κ → V) (i : ι) :
    cj (matAct (M.map Complex.ofRealHom) v i) =
      matAct (M.map Complex.ofRealHom) (fun j => cj (v j)) i := by
  simp only [matAct, map_sum, LinearMap.map_smulₛₗ, Matrix.map_apply, Complex.ofRealHom_eq_coe,
    Complex.conj_ofReal]

/-- **Klein's theorem for (2.11), real data** (Miao, p. 56, where `A`, `B`, `C` and the data are
real). Suppose `V` has a conjugation `cj` (conjugate-linear, isometric, commuting with every
`E_t`; for complex `L¹` it is pointwise conjugation, whose fixed points are the real random
variables). If `A`, `B`, `C` are real and `z`, `ξ`, `k₀` are fixed by `cj`, the unique solution
of `klein_stochastic` is fixed by `cj`, i.e. real: its conjugate is another solution. -/
theorem klein_stochastic_real [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℝ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℝ}
    (cj : V →ₗ⋆[ℂ] V) (hcjE : ∀ t X, cj (E.E t X) = E.E t (cj X)) (hcjn : ∀ X, ‖cj X‖ = ‖X‖)
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
      ‖lam‖ ≠ 1)
    {z : ℕ → Fin nz → V} (hz : IsStableProc z) (hza : IsAdaptedV E z)
    (hzr : ∀ t i, cj (z t i) = z t i)
    {ξ : ℕ → Fin nk → V} (hξ : IsStableProc ξ)
    (hξa : ∀ t i, E.E (t + 1) (ξ (t + 1) i) = ξ (t + 1) i)
    (hξm : IsMartingaleDiffProc E ξ) (hξr : ∀ t i, cj (ξ t i) = ξ t i)
    (k₀ : Fin nk → V) (hk₀ : ∀ i, E.E 0 (k₀ i) = k₀ i) (hk₀r : ∀ i, cj (k₀ i) = k₀ i) :
    ∃! x : ℕ → Fin (nk + ny) → V,
      (IsRESolution E (A.map Complex.ofRealHom) (B.map Complex.ofRealHom)
          (C.map Complex.ofRealHom) z x ∧ IsStableProc x ∧ IsAdaptedV E x ∧
        IsPredeterminedKlein E ξ (fun t i => x t (Fin.castAdd ny i)) ∧
        ∀ i, x 0 (Fin.castAdd ny i) = k₀ i) ∧
      ∀ t i, cj (x t i) = x t i := by
  obtain ⟨x, ⟨hx1, hx2, hx3, ⟨hx4, -, hx6⟩, hx5⟩, hu⟩ := klein_stochastic E hreg hQ hZ hS hT hord
    hZ11 hcirc (C := C.map Complex.ofRealHom) hz hza hξ hξa hξm k₀ hk₀
  have hconj : (fun t i => cj (x t i)) = x := by
    refine hu _ ⟨fun t => funext fun i => ?_, ?_, fun t i => ?_, ⟨fun t i => ?_, hξm, fun i => ?_⟩,
      fun i => ?_⟩
    · have e1 : Evec E t (fun j => cj (x (t + 1) j)) = fun j => cj (Evec E t (x (t + 1)) j) :=
        funext fun j => (hcjE t _).symm
      have e2 : z t = fun j => cj (z t j) := funext fun j => (hzr t j).symm
      rw [e1, Pi.add_apply, e2, ← klS_cj_matAct, ← klS_cj_matAct, ← klS_cj_matAct, ← map_add]
      exact congrArg cj (congrFun (hx1 t) i)
    · obtain ⟨M, hM, h⟩ := hx2
      exact ⟨M, hM, fun t i => by rw [hcjn]; exact h t i⟩
    · rw [← hcjE, hx3 t i]
    · rw [← hcjE, ← map_sub, hx4 t i, hξr]
    · change E.E 0 (cj (x 0 (Fin.castAdd ny i))) = cj (x 0 (Fin.castAdd ny i))
      rw [← hcjE, hx6 i]
    · change cj (x 0 (Fin.castAdd ny i)) = k₀ i
      rw [hx5 i, hk₀r]
  exact ⟨x, ⟨⟨hx1, hx2, hx3, ⟨hx4, hξm, hx6⟩, hx5⟩, fun t i => congrFun (congrFun hconj t) i⟩,
    fun x' hx' => hu x' hx'.1⟩

/-! ### The forward solution (2.17) -/

/-- Miao, (2.17) as corrected, p. 56: in a stable adapted solution of the `u`-block
`S₂₂E_t u_{t+1} = T₂₂u_t + c²_t` (`c²_t = Q₂Cz_t`),
`u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ E_t c²_{t+j}`. The book prints
`u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ Q₂CE_t z_{t+j}`, repeating the misprint of (1.37)
(`eq_2_17_printed_false`). -/
theorem eq_2_17 [CompleteSpace V] (E : CondExpSystem ℂ V) {m : ℕ}
    {S22 T22 : Matrix (Fin m) (Fin m) ℂ} (hT22 : T22.det ≠ 0)
    (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖) {c2 : ℕ → Fin m → V}
    (hc2 : IsStableProc c2) {u : ℕ → Fin m → V} (hu : IsStableProc u)
    (hua : ∀ t, Evec E t (u t) = u t)
    (h : ∀ t, matAct S22 (Evec E t (u (t + 1))) = matAct T22 (u t) + c2 t) (t : ℕ) :
    u t = -∑' j, matAct ((T22⁻¹ * S22) ^ j * T22⁻¹) (Evec E t (c2 (t + j))) := by
  obtain ⟨Cb, -, hCb⟩ := klS_stable_bound hc2
  have hW : ∀ t, ‖-matAct T22⁻¹ (c2 t)‖ ≤ klS_ent T22⁻¹ * Cb := fun t => by
    rw [norm_neg]
    exact (klS_norm_matAct_le _ _).trans (mul_le_mul_of_nonneg_left (hCb t) (klS_ent_nonneg _))
  rw [klS_eq_fwd E (klS_summable_ent hN) (w := fun t => -matAct T22⁻¹ (c2 t)) hW hu hua
    (fun t => (klS_solve_fwd hT22 _ _ _).1 (h t)) t, klS_fwd, ← tsum_neg]
  congr 1
  funext j
  rw [klS_Evec_neg, Evec_matAct, klS_matAct_neg, matAct_mul]

/-- Miao, (2.17) for the solution of `klein_stochastic`, with `x*_t = Zᴴx_t = (s_t, u_t)`:
`u_t = −∑ⱼ (T₂₂⁻¹S₂₂)ʲ T₂₂⁻¹ Q₂C E_t z_{t+j}`, where `Q₂C` is the lower block row of `QC`. -/
theorem eq_2_17_solution [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1)
    {z : ℕ → Fin nz → V} (hz : IsStableProc z)
    {x : ℕ → Fin (nk + ny) → V} (hx : IsRESolution E A B C z x) (hxs : IsStableProc x)
    (hxa : IsAdaptedV E x) (t : ℕ) :
    matAct (star Z) (x t) ∘ Fin.natAdd nk = -∑' j,
      matAct ((((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
        (Q * A * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk)) ^ j *
          ((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
            (Q * C).submatrix (Fin.natAdd nk) id) (Evec E t (z (t + j))) := by
  have hdiag := diag_off_circle hreg hQ hZ hS hT hcirc
  have h := (klS_isRESolution_iff E hQ hZ z x).1 hx
  rw [eq_2_17 E (det_T22_ne_zero hT hord hdiag) (summable_Mu hS hT hord hdiag)
    (c2 := fun t => matAct Q (matAct C (z t)) ∘ Fin.natAdd nk)
    (klS_stable_comp (klS_stable_matAct (klS_stable_matAct hz C) Q) _)
    (u := fun t => matAct (star Z) (x t) ∘ Fin.natAdd nk)
    (klS_stable_comp (klS_stable_matAct hxs _) _)
    (fun t => by
      rw [klS_Evec_comp, Evec_matAct, show Evec E t (x t) = x t from funext (hxa t)])
    (fun t => by
      have := ((klS_blocks_iff hS hT _ _ _).1 (h t)).2
      rw [← klS_Evec_comp] at this
      exact this) t]
  congr 2
  funext j
  change matAct _ (Evec E t (matAct Q (matAct C (z (t + j))) ∘ Fin.natAdd nk)) = _
  rw [klS_Evec_comp, Evec_matAct, Evec_matAct, matAct_mul Q C, klS_matAct_comp, matAct_mul]

/-- The trivial `CondExpSystem` `E_t = id` on `ℂ` (all information known at date 0): the
deterministic system of Chapter 1. -/
noncomputable def klS_detSystem : CondExpSystem ℂ ℂ where
  E _ := ContinuousLinearMap.id ℂ ℂ
  norm_le _ := ContinuousLinearMap.norm_id_le
  tower_le _ _ _ := ContinuousLinearMap.id_comp _
  tower_ge _ _ _ := ContinuousLinearMap.id_comp _

theorem klS_Evec_det {ι : Type*} (t : ℕ) (v : ι → ℂ) : Evec klS_detSystem t v = v := rfl

theorem klS_matAct_eq_mulVec {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (v : κ → ℂ) :
    matAct M v = M *ᵥ v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

/-- **Counterexample to (2.17) as printed** (Miao, p. 56). With `E_t = id`, the book's
`u_t = −T₂₂⁻¹∑ⱼ (T₂₂⁻¹S₂₂)ʲ E_t c²_{t+j}` need not solve `S₂₂E_t u_{t+1} = T₂₂u_t + c²_t`; this is
the counterexample to (1.37) (`eq_1_37_printed_false`): `S₂₂ = [[0, 1], [0, 0]]`,
`T₂₂ = diag(1, 2)`, `c²_1 = e₂`, `c²_t = 0` otherwise. The correct formula is `eq_2_17`. -/
theorem eq_2_17_printed_false :
    ∃ (S₂₂ T₂₂ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℕ → Fin 2 → ℂ),
      S₂₂.IsUpperTriangular ∧ T₂₂.IsUpperTriangular ∧ (∀ i, ‖S₂₂ i i‖ < ‖T₂₂ i i‖) ∧
      IsStableProc c ∧ (∀ t, Evec klS_detSystem t (c t) = c t) ∧
      ¬ ∀ t, matAct S₂₂ (Evec klS_detSystem t (-matAct T₂₂⁻¹
          (∑' j, matAct ((T₂₂⁻¹ * S₂₂) ^ j) (Evec klS_detSystem (t + 1) (c (t + 1 + j)))))) =
        matAct T₂₂ (-matAct T₂₂⁻¹
          (∑' j, matAct ((T₂₂⁻¹ * S₂₂) ^ j) (Evec klS_detSystem t (c (t + j))))) + c t := by
  obtain ⟨S₂₂, T₂₂, c, h1, h2, h3, ⟨M, hM, h4⟩, h5⟩ := eq_1_37_printed_false
  refine ⟨S₂₂, T₂₂, c, h1, h2, h3, ⟨M, hM, fun t i => (norm_le_pi_norm (c t) i).trans_lt (h4 t)⟩,
    fun t => rfl, fun h => h5 fun t => ?_⟩
  have := h t
  simpa only [klS_matAct_eq_mulVec, klS_Evec_det] using this

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Klein solution in state-space form

Miao, §2.3.2, p. 57: "We can simplify the solution if we assume that `{z_t}` satisfies (2.1). In
this case, the solution will be of the following form: `y_t = A_yk k_t + A_yz z_t`,
`k_{t+1} = A_kk k_t + A_kz z_t + ξ_{t+1}`" (the book refers to Klein (2000) for details).

* `klS_Ez_of_2_1`: under (2.1)–(2.2), `E_t z_{t+1} = Φz_t`; this is all that is used.
* `klS_sylvester_exists`: if the powers of `N = T₂₂⁻¹S₂₂` tend to zero and the powers of `Φ` are
  bounded, the Sylvester equation `F = NFΦ + W` has a solution (the map `F ↦ F − NFΦ` is
  injective on a finite-dimensional space).
* `klein_simplified_form`: under the hypotheses of `klein_stochastic`, with `E_t z_{t+1} = Φz_t`
  and `Φ` power bounded (e.g. stable, as in Klein (2000)), there are matrices `A_yk`, `A_yz`,
  `A_kk`, `A_kz`, depending only on `A, B, C, Φ` and the QZ form, such that every stable adapted
  solution whose `k` has prediction error `ξ` satisfies the book's two equations for all `t`.
  Explicitly, with `F` the Sylvester solution for `W = −T₂₂⁻¹Q₂C` (so `u_t = Fz_t`):
  `A_yk = Z₂₁Z₁₁⁻¹`, `A_yz = (Z₂₂ − Z₂₁Z₁₁⁻¹Z₁₂)F`, `A_kk = Z₁₁S₁₁⁻¹T₁₁Z₁₁⁻¹` and
  `A_kz = Z₁₁S₁₁⁻¹(T₁₂F − S₁₂FΦ + Q₁C) + Z₁₂FΦ − A_kk Z₁₂F`.

**Departure.** The book takes `{z_t}` to satisfy (2.1); the proof uses only `E_t z_{t+1} = Φz_t`
and needs `Φ` power bounded (the book is silent on `Φ`; Klein (2000) takes it stable).
-/

open Filter Topology

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Miao, (2.1)–(2.2), p. 45: if `z_{t+1} = Φz_t + Σε_{t+1}` with `E_t ε_{t+1} = 0` and `z`
adapted, then `E_t z_{t+1} = Φz_t`. -/
theorem klS_Ez_of_2_1 (E : CondExpSystem ℂ V) {nz ne : ℕ} (Φ : Matrix (Fin nz) (Fin nz) ℂ)
    (Sig : Matrix (Fin nz) (Fin ne) ℂ) {z : ℕ → Fin nz → V} {ε : ℕ → Fin ne → V}
    (hza : ∀ t, Evec E t (z t) = z t)
    (hrec : ∀ t, z (t + 1) = matAct Φ (z t) + matAct Sig (ε (t + 1)))
    (hε : ∀ t, Evec E t (ε (t + 1)) = 0) (t : ℕ) :
    Evec E t (z (t + 1)) = matAct Φ (z t) := by
  rw [hrec, klS_Evec_add, Evec_matAct, Evec_matAct, hza, hε, klS_matAct_zero, add_zero]

/-! ### The Sylvester equation `F = NFΦ + W` -/

theorem klS_entry_le_ent {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) (a : ι)
    (b : κ) : ‖M a b‖ ≤ klS_ent M :=
  (Finset.single_le_sum (f := fun j => ‖M a j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))

theorem klS_entry_mul_le {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (P : Matrix ι κ ℂ) (G : Matrix κ ρ ℂ) (a : ι) (b : ρ) :
    ‖(P * G) a b‖ ≤ klS_ent P * klS_ent G := by
  calc ‖(P * G) a b‖ = ‖∑ c, P a c * G c b‖ := rfl
    _ ≤ ∑ c, ‖P a c‖ * ‖G c b‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => (norm_mul _ _).le)
    _ ≤ ∑ c, ‖P a c‖ * klS_ent G := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left (klS_entry_le_ent G c b) (norm_nonneg _)
    _ = (∑ c, ‖P a c‖) * klS_ent G := by rw [Finset.sum_mul]
    _ ≤ klS_ent P * klS_ent G := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖P i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
        (klS_ent_nonneg G)

/-- If `Nʲ → 0` and the powers of `Φ` are bounded, `F = NFΦ` forces `F = 0`. -/
theorem klS_sylvester_unique {p q : ℕ} {N : Matrix (Fin p) (Fin p) ℂ}
    {Φ : Matrix (Fin q) (Fin q) ℂ} (hN : Tendsto (fun j => klS_ent (N ^ j)) atTop (𝓝 0))
    {Kb : ℝ} (hΦ : ∀ j a b, ‖(Φ ^ j) a b‖ ≤ Kb) {F : Matrix (Fin p) (Fin q) ℂ}
    (h : F = N * F * Φ) : F = 0 := by
  have hj : ∀ j, F = N ^ j * F * Φ ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc F = N * F * Φ := h
        _ = N * (N ^ j * F * Φ ^ j) * Φ := by rw [← ih]
        _ = N ^ (j + 1) * F * Φ ^ (j + 1) := by
          rw [pow_succ', pow_succ]
          simp only [Matrix.mul_assoc]
  ext a b
  have hb : ∀ j, ‖F a b‖ ≤ q * Kb * klS_ent F * klS_ent (N ^ j) := fun j => by
    calc ‖F a b‖ = ‖(N ^ j * F * Φ ^ j) a b‖ := by rw [← hj j]
      _ = ‖∑ d, (N ^ j * F) a d * (Φ ^ j) d b‖ := rfl
      _ ≤ ∑ d, ‖(N ^ j * F) a d‖ * ‖(Φ ^ j) d b‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => (norm_mul _ _).le)
      _ ≤ ∑ _d : Fin q, klS_ent (N ^ j) * klS_ent F * Kb := Finset.sum_le_sum fun d _ =>
          mul_le_mul (klS_entry_mul_le _ _ a d) (hΦ j d b) (norm_nonneg _)
            (mul_nonneg (klS_ent_nonneg _) (klS_ent_nonneg _))
      _ = q * Kb * klS_ent F * klS_ent (N ^ j) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hlim : Tendsto (fun j => q * Kb * klS_ent F * klS_ent (N ^ j)) atTop (𝓝 0) := by
    simpa using hN.const_mul (q * Kb * klS_ent F)
  have h0 := ge_of_tendsto' hlim hb
  simpa using norm_le_zero_iff.1 h0

/-- The Sylvester equation `F = NFΦ + W` is solvable when `Nʲ → 0` and the powers of `Φ` are
bounded. -/
theorem klS_sylvester_exists {p q : ℕ} {N : Matrix (Fin p) (Fin p) ℂ}
    {Φ : Matrix (Fin q) (Fin q) ℂ} (hN : Tendsto (fun j => klS_ent (N ^ j)) atTop (𝓝 0))
    {Kb : ℝ} (hΦ : ∀ j a b, ‖(Φ ^ j) a b‖ ≤ Kb) (W : Matrix (Fin p) (Fin q) ℂ) :
    ∃ F : Matrix (Fin p) (Fin q) ℂ, F = N * F * Φ + W := by
  let L : Matrix (Fin p) (Fin q) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ :=
    { toFun := fun F => F - N * F * Φ
      map_add' := fun F G => by
        simp only [Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c F => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, RingHom.id_apply] }
  have hinj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun F hF => by
    have h1 : F - N * F * Φ = 0 := hF
    exact klS_sylvester_unique hN hΦ (sub_eq_zero.1 h1)
  obtain ⟨F, hF⟩ := LinearMap.injective_iff_surjective.1 hinj W
  have h1 : F - N * F * Φ = W := hF
  exact ⟨F, by rw [← h1]; abel⟩

/-! ### The algebra of the simplified form -/

/-- Miao, p. 57, the `y` equation: from `k = Z₁₁s + Z₁₂u`, `y = Z₂₁s + Z₂₂u` and `u = Fz`,
`y = Z₂₁Z₁₁⁻¹k + (Z₂₂ − Z₂₁Z₁₁⁻¹Z₁₂)Fz`. -/
theorem klS_simpl_y {m p r q : ℕ} {Z11 : Matrix (Fin m) (Fin m) ℂ}
    {Z12 : Matrix (Fin m) (Fin p) ℂ} {Z21 : Matrix (Fin r) (Fin m) ℂ}
    {Z22 : Matrix (Fin r) (Fin p) ℂ} {F : Matrix (Fin p) (Fin q) ℂ} (hZ11 : Z11.det ≠ 0)
    {k s : Fin m → V} {u : Fin p → V} {yv : Fin r → V} {zt : Fin q → V}
    (hk : k = matAct Z11 s + matAct Z12 u) (hy : yv = matAct Z21 s + matAct Z22 u)
    (hu : u = matAct F zt) :
    yv = matAct (Z21 * Z11⁻¹) k + matAct ((Z22 - Z21 * Z11⁻¹ * Z12) * F) zt := by
  have hs : s = matAct Z11⁻¹ (k - matAct Z12 u) := by
    rw [hk, add_sub_cancel_right, klS_matAct_inv_mul hZ11]
  rw [hy, hs, hu]
  simp only [klS_matAct_sub, klS_sub_matAct, matAct_mul, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- Miao, p. 57, the `k` equation: from `k_t = Z₁₁s_t + Z₁₂u_t`,
`E_t k_{t+1} = Z₁₁E_t s_{t+1} + Z₁₂E_t u_{t+1}`, the `s`-block, `u_t = Fz_t`,
`E_t u_{t+1} = FΦz_t`, `c¹_t = Q₁Cz_t` and `k_{t+1} = E_t k_{t+1} + ξ_{t+1}`,
`k_{t+1} = A_kk k_t + A_kz z_t + ξ_{t+1}`. -/
theorem klS_simpl_k {m p q : ℕ} {S11 T11 Z11 : Matrix (Fin m) (Fin m) ℂ}
    {S12 T12 Z12 : Matrix (Fin m) (Fin p) ℂ} {F : Matrix (Fin p) (Fin q) ℂ}
    {Φ : Matrix (Fin q) (Fin q) ℂ} {QCK : Matrix (Fin m) (Fin q) ℂ} (hS11 : S11.det ≠ 0)
    (hZ11 : Z11.det ≠ 0) {k k' Ek' s Es' c1 ξ' : Fin m → V} {u Eu' : Fin p → V}
    {zt : Fin q → V} (hk : k = matAct Z11 s + matAct Z12 u)
    (hEk' : Ek' = matAct Z11 Es' + matAct Z12 Eu')
    (h1 : matAct S11 Es' + matAct S12 Eu' = matAct T11 s + matAct T12 u + c1)
    (hu : u = matAct F zt) (hEu : Eu' = matAct F (matAct Φ zt)) (hc : c1 = matAct QCK zt)
    (hk' : k' = Ek' + ξ') :
    k' = matAct (Z11 * (S11⁻¹ * T11) * Z11⁻¹) k +
      matAct (Z11 * (S11⁻¹ * (T12 * F - S12 * (F * Φ) + QCK)) + Z12 * (F * Φ) -
        Z11 * (S11⁻¹ * T11) * Z11⁻¹ * (Z12 * F)) zt + ξ' := by
  have hs : s = matAct Z11⁻¹ (k - matAct Z12 u) := by
    rw [hk, add_sub_cancel_right, klS_matAct_inv_mul hZ11]
  rw [hk', hEk', (eq_klein_Es hS11 _ _ _ _ _).1 h1, hs, hEu, hc, hu]
  simp only [matAct_add, klS_matAct_sub, klS_add_matAct, klS_sub_matAct, matAct_mul,
    Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **The simplified Klein solution** (Miao, p. 57; Klein (2000)). Under the hypotheses of
`klein_stochastic` on `A, B, C` and the QZ form, let `Φ` have bounded powers. There are matrices
`A_yk, A_yz, A_kk, A_kz` (depending only on `A, B, C, Φ, Q, Z`) such that for every stable
adapted `{z_t}` with `E_t z_{t+1} = Φz_t` (e.g. (2.1), `klS_Ez_of_2_1`) and every stable adapted
solution `x = (k, y)` of (2.11) whose `k` has prediction error `ξ`,
`y_t = A_yk k_t + A_yz z_t` and `k_{t+1} = A_kk k_t + A_kz z_t + ξ_{t+1}`. -/
theorem klein_simplified_form [CompleteSpace V] (E : CondExpSystem ℂ V) {nk ny nz : ℕ}
    {A B : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ} {C : Matrix (Fin (nk + ny)) (Fin nz) ℂ}
    (hreg : IsRegular A B) {Q Z : Matrix (Fin (nk + ny)) (Fin (nk + ny)) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (nk + ny)) ℂ)
    (hS : (Q * A * Z).IsUpperTriangular) (hT : (Q * B * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (nk + ny), i.val < nk ↔ ‖(Q * B * Z) i i‖ < ‖(Q * A * Z) i i‖)
    (hZ11 : (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny)).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues A B, ‖lam‖ ≠ 1) (Φ : Matrix (Fin nz) (Fin nz) ℂ) {Kb : ℝ}
    (hΦ : ∀ j a b, ‖(Φ ^ j) a b‖ ≤ Kb) :
    ∃ (Ayk : Matrix (Fin ny) (Fin nk) ℂ) (Ayz : Matrix (Fin ny) (Fin nz) ℂ)
      (Akk : Matrix (Fin nk) (Fin nk) ℂ) (Akz : Matrix (Fin nk) (Fin nz) ℂ),
      ∀ (z : ℕ → Fin nz → V) (ξ : ℕ → Fin nk → V) (x : ℕ → Fin (nk + ny) → V),
        IsStableProc z → IsAdaptedV E z → (∀ t, Evec E t (z (t + 1)) = matAct Φ (z t)) →
        IsRESolution E A B C z x → IsStableProc x → IsAdaptedV E x →
        (∀ t i, x (t + 1) (Fin.castAdd ny i) - E.E t (x (t + 1) (Fin.castAdd ny i)) =
          ξ (t + 1) i) →
        ∀ t, x t ∘ Fin.natAdd nk = matAct Ayk (x t ∘ Fin.castAdd ny) + matAct Ayz (z t) ∧
          x (t + 1) ∘ Fin.castAdd ny =
            matAct Akk (x t ∘ Fin.castAdd ny) + matAct Akz (z t) + ξ (t + 1) := by
  have hdiag := diag_off_circle hreg hQ hZ hS hT hcirc
  have hS11 := det_S11_ne_zero hS hord
  have hT22 := det_T22_ne_zero hT hord hdiag
  have hN := klS_summable_ent (summable_Mu hS hT hord hdiag)
  obtain ⟨F, hF⟩ := klS_sylvester_exists hN.tendsto_atTop_zero hΦ
    (-(((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹ *
      (Q * C).submatrix (Fin.natAdd nk) id))
  refine ⟨Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny) *
      (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹,
    (Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk) - Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny) *
      (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
        Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk)) * F,
    Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *
      (((Q * A * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
        (Q * B * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny)) *
      (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹,
    Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *
        (((Q * A * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
          ((Q * B * Z).submatrix (Fin.castAdd ny) (Fin.natAdd nk) * F -
            (Q * A * Z).submatrix (Fin.castAdd ny) (Fin.natAdd nk) * (F * Φ) +
              (Q * C).submatrix (Fin.castAdd ny) id)) +
      Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) * (F * Φ) -
      Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny) *
        (((Q * A * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
          (Q * B * Z).submatrix (Fin.castAdd ny) (Fin.castAdd ny)) *
        (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))⁻¹ *
        (Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk) * F), ?_⟩
  intro z ξ x hz hza hzΦ hx hxs hxa hp
  have hza' : ∀ t, Evec E t (z t) = z t := fun t => funext (hza t)
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hback : ∀ v : Fin (nk + ny) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  have h := (klS_isRESolution_iff E hQ hZ z x).1 hx
  have hb := fun t => (klS_blocks_iff hS hT _ _ _).1 (h t)
  -- the `u`-block: `u_t = Fz_t`
  have hwS : IsStableProc fun t =>
      -matAct ((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹
        (matAct Q (matAct C (z t)) ∘ Fin.natAdd nk) := by
    obtain ⟨M, hM, hM'⟩ := klS_stable_matAct (klS_stable_comp (klS_stable_matAct
      (klS_stable_matAct hz C) Q) (Fin.natAdd nk))
      ((Q * B * Z).submatrix (Fin.natAdd nk) (Fin.natAdd nk))⁻¹
    exact ⟨M, hM, fun t i => by simp only [Pi.neg_apply, norm_neg]; exact hM' t i⟩
  obtain ⟨Wb, -, hW⟩ := klS_stable_bound hwS
  have hu : ∀ t, matAct (star Z) (x t) ∘ Fin.natAdd nk = matAct F (z t) := fun t =>
    (klS_eq_fwd E hN hW (u := fun t => matAct (star Z) (x t) ∘ Fin.natAdd nk)
      (klS_stable_comp (klS_stable_matAct hxs _) _)
      (fun t => by
        rw [klS_Evec_comp, Evec_matAct, show Evec E t (x t) = x t from funext (hxa t)])
      (fun t => (klS_solve_fwd hT22 _ _ _).1 (hb t).2) t).trans
    (klS_eq_fwd E hN hW (u := fun t => matAct F (z t)) (klS_stable_matAct hz F)
      (fun t => by
        rw [Evec_matAct, hza'])
      (fun t => by
        rw [Evec_matAct, hzΦ]
        conv_lhs => rw [hF]
        simp only [klS_add_matAct, klS_neg_matAct, matAct_mul, klS_matAct_comp,
          Matrix.mul_assoc]) t).symm
  have hxK : ∀ t, x t ∘ Fin.castAdd ny =
      matAct (Z.submatrix (Fin.castAdd ny) (Fin.castAdd ny))
          (matAct (star Z) (x t) ∘ Fin.castAdd ny) +
        matAct (Z.submatrix (Fin.castAdd ny) (Fin.natAdd nk))
          (matAct (star Z) (x t) ∘ Fin.natAdd nk) := fun t => by
    have := klS_matAct_blocks Z (Fin.castAdd ny) (matAct (star Z) (x t))
    rwa [hback] at this
  have hxU : ∀ t, x t ∘ Fin.natAdd nk =
      matAct (Z.submatrix (Fin.natAdd nk) (Fin.castAdd ny))
          (matAct (star Z) (x t) ∘ Fin.castAdd ny) +
        matAct (Z.submatrix (Fin.natAdd nk) (Fin.natAdd nk))
          (matAct (star Z) (x t) ∘ Fin.natAdd nk) := fun t => by
    have := klS_matAct_blocks Z (Fin.natAdd nk) (matAct (star Z) (x t))
    rwa [hback] at this
  intro t
  refine ⟨klS_simpl_y hZ11 (hxK t) (hxU t) (hu t), klS_simpl_k hS11 hZ11
    (Ek' := Evec E t (x (t + 1) ∘ Fin.castAdd ny)) (hxK t) ?_ (hb t).1 (hu t) ?_ ?_ ?_⟩
  · rw [hxK (t + 1), klS_Evec_add, Evec_matAct, Evec_matAct, klS_Evec_comp, klS_Evec_comp]
  · rw [← klS_Evec_comp, hu (t + 1), Evec_matAct, hzΦ]
  · rw [matAct_mul]
    rfl
  · funext i
    change x (t + 1) (Fin.castAdd ny i) = E.E t (x (t + 1) (Fin.castAdd ny i)) + ξ (t + 1) i
    rw [← hp t i]
    abel

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linear-quadratic example of the Klein method

Miao, §2.3.2, pp. 57–58: maximise `−½E∑ βᵗ[x_t', u_t'][[Q, S], [S', R]][x_t; u_t]` subject to
`x_{t+1} = Ax_t + Bu_t + Cξ_{t+1}` (2.18), with multiplier `β^{t+1}λ_{t+1}`.

* `lq_predError` (p. 57): with `x`, `u` adapted, the prediction error of `x` is
  `x_{t+1} − E_t x_{t+1} = C(ξ_{t+1} − E_tξ_{t+1})`.
* `lq_predetermined` (p. 57, "`{x_t}` is predetermined with the prediction error `{ξ_t}`"): if
  `ξ` is a martingale difference, `x` is predetermined in the sense of Definition 2.3.4 with
  prediction error `Cξ`, and `E_t x_{t+1} = Ax_t + Bu_t`.
* `lq_variation_u`, `lq_variation_x`: the first-order conditions. With the multiplier term
  written as `+β^{t+1}λ_{t+1}'(x_{t+1} − Ax_t − Bu_t − Cξ_{t+1})`, the date-`t` terms of the
  Lagrangian (divided by `βᵗ`) are `ℓ = −½q(x_t, u_t) − βλ_{t+1}'(Ax_t + Bu_t) + λ_t'x_t`. For
  symmetric `Q`, `R`, the first variations are exactly
  `ℓ(x, u + h) − ℓ(x, u) = −(S'x + Ru + βB'λ_{t+1})·h − ½h'Rh` and
  `ℓ(x + h, u) − ℓ(x, u) = −(Qx + Su − λ_t + βA'λ_{t+1})·h − ½h'Qh`, so, after conditioning on
  `F_t` (`λ_{t+1}` enters linearly), the first-order conditions are
  `S'x_t + Ru_t + βB'E_tλ_{t+1} = 0` and `Qx_t + Su_t − λ_t + βA'E_tλ_{t+1} = 0`.
* `lq_system_iff` (p. 58): these first-order conditions together with `E_t x_{t+1} = Ax_t + Bu_t`
  are equivalent to the printed system `lqLeft · E_t(x, u, λ)_{t+1} = lqRight · (x, u, λ)_t`,
  i.e. (2.11) with no forcing. Entry by entry the printed matrices are correct for this sign
  convention of the multiplier (with the opposite convention `−β^{t+1}λ_{t+1}'(…)` the signs of
  the `λ` columns flip); no misprint.

**Departures and items not formalised.**
* The book takes `{ξ_t}` to be a white noise. A white noise need not be a martingale difference
  (`E_tξ_{t+1} ≠ 0` is possible for uncorrelated `ξ`), and then the prediction error of `x` is
  `C(ξ_{t+1} − E_tξ_{t+1})`, not `Cξ_{t+1}` (`lq_predError`); the claim needs `ξ` to be a
  martingale difference (e.g. (2.2)), which `lq_predetermined` assumes.
* The conditioning step (passing from the pointwise first variation to `E_tλ_{t+1}`) needs
  products of random variables, which the abstract setting does not have; it is not formalised.
* "First-order conditions together with the transversality condition are necessary and
  sufficient for optimality" (p. 58) is not formalised: it is the linear-quadratic control
  theory of Chapter 9.
-/

namespace Miao.RationalExpectations

open scoped Matrix

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-! ### The state is predetermined -/

/-- Miao, p. 57: with `x_{t+1} = Ax_t + Bu_t + Cξ_{t+1}` and `x`, `u` adapted, the prediction
error of `x` is `x_{t+1} − E_t x_{t+1} = C(ξ_{t+1} − E_tξ_{t+1})`. -/
theorem lq_predError {nx nu nξ : ℕ} (E : CondExpSystem 𝕜 V) (A : Matrix (Fin nx) (Fin nx) 𝕜)
    (B : Matrix (Fin nx) (Fin nu) 𝕜) (C : Matrix (Fin nx) (Fin nξ) 𝕜) {x : ℕ → Fin nx → V}
    {u : ℕ → Fin nu → V} {ξ : ℕ → Fin nξ → V} (hxa : IsAdaptedV E x) (hua : IsAdaptedV E u)
    (h : ∀ t, x (t + 1) = matAct A (x t) + matAct B (u t) + matAct C (ξ (t + 1))) (t : ℕ)
    (i : Fin nx) :
    x (t + 1) i - E.E t (x (t + 1) i) =
      matAct C (fun j => ξ (t + 1) j - E.E t (ξ (t + 1) j)) i := by
  rw [h t]
  simp only [matAct, Pi.add_apply, map_add, map_sum, map_smul, hxa t, hua t, smul_sub,
    Finset.sum_sub_distrib]
  abel

/-- Miao, p. 57: if `ξ` is a martingale difference (as under (2.2)), `x` and `u` are adapted and
`x₀` is `F₀`-measurable, then `x` is predetermined (Definition 2.3.4) with prediction error
`Cξ`, and `E_t x_{t+1} = Ax_t + Bu_t` (the first block row of the system on p. 58). -/
theorem lq_predetermined {nx nu nξ : ℕ} (E : CondExpSystem 𝕜 V) (A : Matrix (Fin nx) (Fin nx) 𝕜)
    (B : Matrix (Fin nx) (Fin nu) 𝕜) (C : Matrix (Fin nx) (Fin nξ) 𝕜) {x : ℕ → Fin nx → V}
    {u : ℕ → Fin nu → V} {ξ : ℕ → Fin nξ → V} (hxa : IsAdaptedV E x) (hua : IsAdaptedV E u)
    (hξ : IsMartingaleDiffProc E ξ)
    (h : ∀ t, x (t + 1) = matAct A (x t) + matAct B (u t) + matAct C (ξ (t + 1))) :
    IsPredeterminedKlein E (fun t => matAct C (ξ t)) x ∧
      ∀ t, Evec E t (x (t + 1)) = matAct A (x t) + matAct B (u t) := by
  have hE : ∀ t, Evec E t (x (t + 1)) = matAct A (x t) + matAct B (u t) := fun t => by
    funext i
    rw [h t]
    simp only [Evec, matAct, Pi.add_apply, map_add, map_sum, map_smul, hxa t, hua t, hξ t,
      smul_zero, Finset.sum_const_zero, add_zero]
  refine ⟨⟨fun t i => ?_, fun t i => ?_, fun i => hxa 0 i⟩, hE⟩
  · rw [lq_predError E A B C hxa hua h t i]
    simp only [hξ t, sub_zero]
  · simp only [matAct, map_sum, map_smul, hξ t, smul_zero, Finset.sum_const_zero]

/-! ### The first-order conditions -/

/-- The date-`t` terms of the Lagrangian of the LQ problem divided by `βᵗ` (Miao, p. 58), with the
multiplier term `+β^{t+1}λ_{t+1}'(x_{t+1} − Ax_t − Bu_t − Cξ_{t+1})`:
`ℓ = −½(x'Qx + 2x'Su + u'Ru) − βλ_{t+1}'(Ax + Bu) + λ_t'x`. -/
noncomputable def lqPeriod {nx nu : ℕ} (Q : Matrix (Fin nx) (Fin nx) ℝ)
    (S : Matrix (Fin nx) (Fin nu) ℝ)
    (R : Matrix (Fin nu) (Fin nu) ℝ) (A : Matrix (Fin nx) (Fin nx) ℝ)
    (B : Matrix (Fin nx) (Fin nu) ℝ) (β : ℝ) (lam lamN x : Fin nx → ℝ) (u : Fin nu → ℝ) :
    ℝ :=
  -(1 / 2) * (x ⬝ᵥ Q *ᵥ x + 2 * (x ⬝ᵥ S *ᵥ u) + u ⬝ᵥ R *ᵥ u) -
    β * (lamN ⬝ᵥ (A *ᵥ x + B *ᵥ u)) + lam ⬝ᵥ x

/-- The first-order condition for `u_t` (Miao, p. 58): for symmetric `R` the first variation of
the date-`t` Lagrangian in `u` is `−(S'x + Ru + βB'λ_{t+1})·h − ½h'Rh`, so the first-order
condition is `S'x_t + Ru_t + βB'λ_{t+1} = 0` (with `E_tλ_{t+1}` after conditioning). -/
theorem lq_variation_u {nx nu : ℕ} (Q : Matrix (Fin nx) (Fin nx) ℝ)
    (S : Matrix (Fin nx) (Fin nu) ℝ) (R : Matrix (Fin nu) (Fin nu) ℝ) (hR : Rᵀ = R)
    (A : Matrix (Fin nx) (Fin nx) ℝ) (B : Matrix (Fin nx) (Fin nu) ℝ) (β : ℝ)
    (lam lamN x : Fin nx → ℝ) (u h : Fin nu → ℝ) :
    lqPeriod Q S R A B β lam lamN x (u + h) - lqPeriod Q S R A B β lam lamN x u =
      -((Sᵀ *ᵥ x + R *ᵥ u + β • (Bᵀ *ᵥ lamN)) ⬝ᵥ h) - 1 / 2 * (h ⬝ᵥ R *ᵥ h) := by
  have e1 : x ⬝ᵥ S *ᵥ h = (Sᵀ *ᵥ x) ⬝ᵥ h := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have e2 : u ⬝ᵥ R *ᵥ h = (R *ᵥ u) ⬝ᵥ h := by
    conv_rhs => rw [← hR, Matrix.mulVec_transpose]
    rw [Matrix.dotProduct_mulVec]
  have e3 : h ⬝ᵥ R *ᵥ u = (R *ᵥ u) ⬝ᵥ h := dotProduct_comm _ _
  have e4 : lamN ⬝ᵥ B *ᵥ h = (Bᵀ *ᵥ lamN) ⬝ᵥ h := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  simp only [lqPeriod, Matrix.mulVec_add, dotProduct_add, add_dotProduct, smul_dotProduct,
    smul_eq_mul, e1, e2, e3, e4]
  ring

/-- The first-order condition for `x_t` (Miao, p. 58): for symmetric `Q` the first variation of
the date-`t` Lagrangian in `x` is `−(Qx + Su − λ_t + βA'λ_{t+1})·h − ½h'Qh`, so the first-order
condition is `Qx_t + Su_t − λ_t + βA'λ_{t+1} = 0` (with `E_tλ_{t+1}` after conditioning). -/
theorem lq_variation_x {nx nu : ℕ} (Q : Matrix (Fin nx) (Fin nx) ℝ) (hQ : Qᵀ = Q)
    (S : Matrix (Fin nx) (Fin nu) ℝ) (R : Matrix (Fin nu) (Fin nu) ℝ)
    (A : Matrix (Fin nx) (Fin nx) ℝ) (B : Matrix (Fin nx) (Fin nu) ℝ) (β : ℝ)
    (lam lamN x h : Fin nx → ℝ) (u : Fin nu → ℝ) :
    lqPeriod Q S R A B β lam lamN (x + h) u - lqPeriod Q S R A B β lam lamN x u =
      -((Q *ᵥ x + S *ᵥ u - lam + β • (Aᵀ *ᵥ lamN)) ⬝ᵥ h) - 1 / 2 * (h ⬝ᵥ Q *ᵥ h) := by
  have e1 : x ⬝ᵥ Q *ᵥ h = (Q *ᵥ x) ⬝ᵥ h := by
    conv_rhs => rw [← hQ, Matrix.mulVec_transpose]
    rw [Matrix.dotProduct_mulVec]
  have e2 : h ⬝ᵥ Q *ᵥ x = (Q *ᵥ x) ⬝ᵥ h := dotProduct_comm _ _
  have e3 : h ⬝ᵥ S *ᵥ u = (S *ᵥ u) ⬝ᵥ h := dotProduct_comm _ _
  have e4 : lamN ⬝ᵥ A *ᵥ h = (Aᵀ *ᵥ lamN) ⬝ᵥ h := by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  have e5 : lam ⬝ᵥ h = h ⬝ᵥ lam := dotProduct_comm _ _
  simp only [lqPeriod, Matrix.mulVec_add, dotProduct_add, add_dotProduct, sub_dotProduct,
    smul_dotProduct, smul_eq_mul, e1, e2, e3, e4, e5]
  ring

/-! ### The linear system on p. 58 -/

/-- The left matrix of the system on p. 58, `[[I, 0, 0], [0, 0, −βB'], [0, 0, βA']]`, on the
index `(x, u, λ) = (Fin nx ⊕ Fin nu) ⊕ Fin nx`. -/
def lqLeft {nx nu : ℕ} (A : Matrix (Fin nx) (Fin nx) 𝕜) (B : Matrix (Fin nx) (Fin nu) 𝕜) (β : 𝕜) :
    Matrix ((Fin nx ⊕ Fin nu) ⊕ Fin nx) ((Fin nx ⊕ Fin nu) ⊕ Fin nx) 𝕜 :=
  Matrix.fromBlocks (Matrix.fromBlocks 1 0 0 0) (Matrix.fromRows 0 (-(β • Bᵀ))) 0 (β • Aᵀ)

/-- The right matrix of the system on p. 58, `[[A, B, 0], [S', R, 0], [−Q, −S, I]]`. -/
def lqRight {nx nu : ℕ} (A : Matrix (Fin nx) (Fin nx) 𝕜) (B : Matrix (Fin nx) (Fin nu) 𝕜)
    (Q : Matrix (Fin nx) (Fin nx) 𝕜) (S : Matrix (Fin nx) (Fin nu) 𝕜)
    (R : Matrix (Fin nu) (Fin nu) 𝕜) :
    Matrix ((Fin nx ⊕ Fin nu) ⊕ Fin nx) ((Fin nx ⊕ Fin nu) ⊕ Fin nx) 𝕜 :=
  Matrix.fromBlocks (Matrix.fromBlocks A B Sᵀ R) 0 (Matrix.fromCols (-Q) (-S)) 1

theorem klL_matAct_fromBlocks {l m n o : Type*} [Fintype l] [Fintype m]
    (P : Matrix n l 𝕜) (P' : Matrix n m 𝕜) (R : Matrix o l 𝕜) (R' : Matrix o m 𝕜) (a : l → V)
    (b : m → V) :
    matAct (Matrix.fromBlocks P P' R R') (Sum.elim a b) =
      Sum.elim (matAct P a + matAct P' b) (matAct R a + matAct R' b) := by
  funext i
  cases i <;> simp [matAct, Fintype.sum_sum_type]

theorem klL_matAct_fromRows {m₁ m₂ n : Type*} [Fintype n] (P : Matrix m₁ n 𝕜)
    (R : Matrix m₂ n 𝕜) (v : n → V) :
    matAct (Matrix.fromRows P R) v = Sum.elim (matAct P v) (matAct R v) := by
  funext i
  cases i <;> simp [matAct]

theorem klL_matAct_fromCols {m n₁ n₂ : Type*} [Fintype n₁] [Fintype n₂] (P : Matrix m n₁ 𝕜)
    (R : Matrix m n₂ 𝕜) (a : n₁ → V) (b : n₂ → V) :
    matAct (Matrix.fromCols P R) (Sum.elim a b) = matAct P a + matAct R b := by
  funext i
  simp [matAct, Fintype.sum_sum_type]

theorem klL_matAct_zero {ι κ : Type*} [Fintype κ] (x : κ → V) :
    matAct (0 : Matrix ι κ 𝕜) x = 0 := by
  funext i
  simp [matAct]

theorem klL_matAct_smul {ι κ : Type*} [Fintype κ] (c : 𝕜) (M : Matrix ι κ 𝕜) (x : κ → V) :
    matAct (c • M) x = c • matAct M x := by
  funext i
  simp [matAct, Finset.smul_sum, smul_smul]

theorem klL_matAct_neg {ι κ : Type*} [Fintype κ] (M : Matrix ι κ 𝕜) (x : κ → V) :
    matAct (-M) x = -matAct M x := by
  funext i
  simp [matAct, Finset.sum_neg_distrib]

theorem klL_Evec_elim {α β : Type*} (E : CondExpSystem 𝕜 V) (t : ℕ) (a : α → V) (b : β → V) :
    Evec E t (Sum.elim a b) = Sum.elim (Evec E t a) (Evec E t b) := by
  funext i
  cases i <;> rfl

/-- **The LQ system** (Miao, p. 58). For processes `x`, `u`, `λ`, the system
`[[I, 0, 0], [0, 0, −βB'], [0, 0, βA']] E_t(x, u, λ)_{t+1} = [[A, B, 0], [S', R, 0], [−Q, −S, I]]
(x, u, λ)_t` ((2.11) with no forcing) holds iff `E_t x_{t+1} = Ax_t + Bu_t` and the first-order
conditions `S'x_t + Ru_t + βB'E_tλ_{t+1} = 0`, `Qx_t + Su_t − λ_t + βA'E_tλ_{t+1} = 0` hold
(`lq_variation_u`, `lq_variation_x`; `'` is the transpose). -/
theorem lq_system_iff {nx nu : ℕ} (E : CondExpSystem 𝕜 V) (A : Matrix (Fin nx) (Fin nx) 𝕜)
    (B : Matrix (Fin nx) (Fin nu) 𝕜) (Q : Matrix (Fin nx) (Fin nx) 𝕜)
    (S : Matrix (Fin nx) (Fin nu) 𝕜) (R : Matrix (Fin nu) (Fin nu) 𝕜) (β : 𝕜)
    (x lam : ℕ → Fin nx → V) (u : ℕ → Fin nu → V) :
    IsRESolution E (lqLeft A B β) (lqRight A B Q S R) (0 : Matrix _ (Fin 0) 𝕜) (fun _ => 0)
        (fun t => Sum.elim (Sum.elim (x t) (u t)) (lam t)) ↔
      ∀ t, Evec E t (x (t + 1)) = matAct A (x t) + matAct B (u t) ∧
        matAct Sᵀ (x t) + matAct R (u t) + β • matAct Bᵀ (Evec E t (lam (t + 1))) = 0 ∧
        matAct Q (x t) + matAct S (u t) - lam t + β • matAct Aᵀ (Evec E t (lam (t + 1))) = 0 := by
  refine forall_congr' fun t => ?_
  simp only [lqLeft, lqRight, klL_Evec_elim, klL_matAct_fromBlocks, klL_matAct_fromRows,
    klL_matAct_fromCols, klL_matAct_zero, klL_matAct_smul, klL_matAct_neg, matAct_one,
    zero_add, add_zero, ← Sum.elim_add_add, Sum.elim_eq_iff]
  have key1 : ∀ P a b : Fin nu → V, -P = a + b ↔ a + b + P = 0 := fun P a b => by
    rw [← sub_eq_zero, show -P - (a + b) = -(a + b + P) by abel, neg_eq_zero]
  have key2 : ∀ P a b c : Fin nx → V, P = -a + -b + c ↔ a + b - c + P = 0 := fun P a b c => by
    rw [← sub_eq_zero, show P - (-a + -b + c) = a + b - c + P by abel]
  rw [and_assoc]
  exact and_congr Iff.rfl (and_congr (key1 _ _ _) (key2 _ _ _ _))

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Sims method

Miao, §2.3.3, pp. 58–62, in the abstract setting of `Basics` with `𝕜 = ℂ` (the QZ form is
complex): `V` is a complete complex normed space of scalar random variables with conditional
expectations `E : CondExpSystem ℂ V`, a vector random variable is `Fin k → V`.

**Representation.** (2.20) `Γ₀y_t = Γ₁y_{t−1} + Ψε_t + Πη_t` is `IsSimsSolution` (for `t ≥ 1`,
indexed as `t + 1`; `y`, `η` adapted, `E_tη_{t+1} = 0`; `Pm` stands for `Π`). The exogenous
shock `ε` is an `IsSimsShock` (adapted, stable, martingale difference). An ordered QZ form
(`IsSimsQZ`, from `theorem_1_4_4_stable` via `isSimsQZ_of_regular`) has `n = n_s + n_u`, the
stable pairs first and none on the unit circle; rows of `Q`, `Zᴴ` are split by `simsTop`,
`simsBot`, blocks by `sims11`, `sims12`, `sims22`; `y* = Zᴴy = (s, u)`.

* (2.21) `eq_2_21`; (2.22) `eq_2_22` (pathwise forward solution) and `eq_2_22_expect`: a
  stable adapted `u` whose forcing is a martingale difference vanishes; hence every stable
  solution has `u_t = Z₂ᴴy_t = 0` for all `t` (`sims_u_eq_zero`), `Z₂ᴴy₀ = 0`
  (`sims_Z2_y0`) and (2.23) `Q₂.(Ψε_t + Πη_t) = 0` (`eq_2_23`).
* Lemma 2.3.1 (`lemma_2_3_1`, matrix form; `lemma_2_3_1_sims`; `lemma_2_3_1_random`, random
  right-hand sides); Assumptions 2.3.1–2.3.2 (`SimsAssumption1`, `SimsAssumption2`);
  Assumption 2.3.2 iff `ker(Q₂.Π) ⊆ ker(Q₁.Π)` (`simsAssumption2_iff_ker`);
  `assumption_2_3_1_nu_gt_m` (existence with `n_u > m`).
* (2.24) `eq_2_24` (any `Ξ`), `simsKmat_mul_Pm`; the matrices `G`, `H`, `K`, `Θ₁`, `Θ₂`
  (`simsGmat`, `simsHmat`, `simsKmat`, `simsTheta1`, `simsTheta2`).
* Theorem 2.3.1: `theorem_2_3_1_theta` (every stable solution is `y_t = Θ₁y_{t−1} + Θ₂ε_t`,
  under 2.3.2), `theorem_2_3_1_uniqueness` (2.3.2 only), `theorem_2_3_1_existence`
  (2.3.1 only, `η = −Λε`), `theorem_2_3_1_sufficiency`, `theorem_2_3_1_necessity_1`,
  `theorem_2_3_1_necessity_2` and the characterisation `theorem_2_3_1` under a rich
  filtration (`SimsRich`; `simsRich_trunc` shows the hypothesis is satisfiable).

**Corrections.**
* (2.22) is printed `u_t = −T₂₂⁻¹∑_{j≥1}(T₂₂⁻¹S₂₂)ʲQ₂.(Ψε_{t+j} + Πη_{t+j})`; the forward
  solution of `S₂₂u_t = T₂₂u_{t−1} + Q₂.(…)` is `u_t = −∑_{j≥1}(T₂₂⁻¹S₂₂)^{j−1}T₂₂⁻¹Q₂.(…)`
  (`eq_2_22`; `eq_2_22_printed_false`). The conclusion `u_t = 0` needs both stability (for
  the forward sum) and the martingale-difference property of `ε`, `η` (for `E_t` to kill it).
* `Θ₁` is printed `Z G⁻¹ H`; it must be `Z G⁻¹ H Zᴴ` (`theta_1_printed_false`). `Θ₂` and (2.24)
  are correct as printed.
* Theorem 2.3.1 ("necessary and sufficient", called "Theorem 2.19" on p. 62): sufficiency holds
  in every `CondExpSystem`, with "unique" meaning unique `y` (given `y₀`; `y₀` is free subject
  to `Z₂ᴴy₀ = 0`), not unique `(y, η)`. Existence needs only 2.3.1, uniqueness only 2.3.2.
  Necessity is false in general: in the deterministic system `E_t = id` martingale differences
  vanish and a system violating both assumptions has a unique stable solution
  (`theorem_2_3_1_necessity_false`); it holds when the filtration carries a nonzero stable
  martingale difference (`theorem_2_3_1`).
* Lemma 2.3.1's proof takes the `j`-th column of `Λ` to be the `η` solving (2.23) for
  `ε = I_j`; that gives `Q₂.Ψ = −Q₂.ΠΛ`, so the column must be `−η`.
* The book's hypotheses leave implicit that the shocks are adapted and stable; both are
  assumed (`IsSimsShock`).
-/

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Blocks -/

/-- The first `a` rows `M_{1·}` of a matrix with `a + b` rows (e.g. `Q₁.`, `Z₁ᴴ`). -/
abbrev simsTop {a b : ℕ} {κ : Type*} (M : Matrix (Fin (a + b)) κ ℂ) : Matrix (Fin a) κ ℂ :=
  M.submatrix (Fin.castAdd b) id

/-- The last `b` rows `M_{2·}` of a matrix with `a + b` rows (e.g. `Q₂.`, `Z₂ᴴ`). -/
abbrev simsBot {a b : ℕ} {κ : Type*} (M : Matrix (Fin (a + b)) κ ℂ) : Matrix (Fin b) κ ℂ :=
  M.submatrix (Fin.natAdd a) id

/-- The block `M₁₁`. -/
abbrev sims11 {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) : Matrix (Fin a) (Fin a) ℂ :=
  M.submatrix (Fin.castAdd b) (Fin.castAdd b)

/-- The block `M₁₂`. -/
abbrev sims12 {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) : Matrix (Fin a) (Fin b) ℂ :=
  M.submatrix (Fin.castAdd b) (Fin.natAdd a)

/-- The block `M₂₂`. -/
abbrev sims22 {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) : Matrix (Fin b) (Fin b) ℂ :=
  M.submatrix (Fin.natAdd a) (Fin.natAdd a)

/-- The block matrix `[[A, B], [C, D]]` indexed by `Fin (a + b)`. -/
def simsBlk {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin (a + b)) (Fin (a + b)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)

/-- The stacked matrix `[[A], [C]]` indexed by `Fin (a + b)` rows. -/
def simsRows {a b : ℕ} {κ : Type*} (A : Matrix (Fin a) κ ℂ) (C : Matrix (Fin b) κ ℂ) :
    Matrix (Fin (a + b)) κ ℂ :=
  Matrix.reindex finSumFinEquiv (Equiv.refl κ) (Matrix.fromRows A C)

theorem simsBlk_11 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    sims11 (simsBlk A B C D) = A := by
  ext i j
  simp [simsBlk]

theorem simsBlk_12 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    sims12 (simsBlk A B C D) = B := by
  ext i j
  simp [simsBlk]

theorem simsBlk_21 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    (simsBlk A B C D).submatrix (Fin.natAdd a) (Fin.castAdd b) = C := by
  ext i j
  simp [simsBlk]

theorem simsBlk_22 {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) :
    sims22 (simsBlk A B C D) = D := by
  ext i j
  simp [simsBlk]

theorem simsRows_top {a b : ℕ} {κ : Type*} (A : Matrix (Fin a) κ ℂ) (C : Matrix (Fin b) κ ℂ) :
    simsTop (simsRows A C) = A := by
  ext i j
  simp [simsRows]

theorem simsRows_bot {a b : ℕ} {κ : Type*} (A : Matrix (Fin a) κ ℂ) (C : Matrix (Fin b) κ ℂ) :
    simsBot (simsRows A C) = C := by
  ext i j
  simp [simsRows]

theorem simsBlk_det {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (D : Matrix (Fin b) (Fin b) ℂ) : (simsBlk A B 0 D).det = A.det * D.det := by
  rw [simsBlk, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem simsTop_mul {a b : ℕ} {κ ρ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (N : Matrix κ ρ ℂ) : simsTop M * N = simsTop (M * N) := by
  ext i j
  simp [Matrix.mul_apply]

theorem simsBot_mul {a b : ℕ} {κ ρ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (N : Matrix κ ρ ℂ) : simsBot M * N = simsBot (M * N) := by
  ext i j
  simp [Matrix.mul_apply]

theorem simsRows_mul {a b : ℕ} {κ ρ : Type*} [Fintype κ] (A : Matrix (Fin a) κ ℂ)
    (C : Matrix (Fin b) κ ℂ) (N : Matrix κ ρ ℂ) : simsRows A C * N = simsRows (A * N) (C * N) := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [simsRows, Matrix.mul_apply]

/-- The top rows of `Mv`: `(Mv)₁ = M₁.v`. -/
theorem simsH_top_matAct {a b : ℕ} {κ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (x : κ → V) : matAct M x ∘ Fin.castAdd b = matAct (simsTop M) x := rfl

/-- The bottom rows of `Mv`: `(Mv)₂ = M₂.v`. -/
theorem simsH_bot_matAct {a b : ℕ} {κ : Type*} [Fintype κ] (M : Matrix (Fin (a + b)) κ ℂ)
    (x : κ → V) : matAct M x ∘ Fin.natAdd a = matAct (simsBot M) x := rfl

/-- The top rows of a block matrix acting on a vector. -/
theorem simsH_blk_top {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) (x : Fin (a + b) → V) :
    matAct (simsBlk A B C D) x ∘ Fin.castAdd b =
      matAct A (x ∘ Fin.castAdd b) + matAct B (x ∘ Fin.natAdd a) := by
  rw [klS_matAct_blocks]
  rw [show (simsBlk A B C D).submatrix (Fin.castAdd b) (Fin.castAdd b) = A from simsBlk_11 A B C D,
    show (simsBlk A B C D).submatrix (Fin.castAdd b) (Fin.natAdd a) = B from simsBlk_12 A B C D]

/-- The bottom rows of a block matrix acting on a vector. -/
theorem simsH_blk_bot {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin a) (Fin b) ℂ)
    (C : Matrix (Fin b) (Fin a) ℂ) (D : Matrix (Fin b) (Fin b) ℂ) (x : Fin (a + b) → V) :
    matAct (simsBlk A B C D) x ∘ Fin.natAdd a =
      matAct C (x ∘ Fin.castAdd b) + matAct D (x ∘ Fin.natAdd a) := by
  rw [klS_matAct_blocks]
  rw [simsBlk_21, show (simsBlk A B C D).submatrix (Fin.natAdd a) (Fin.natAdd a) = D from
    simsBlk_22 A B C D]

/-- A matrix acting on a scalar multiple of one random variable:
`M(v ζ) = (Mv) ζ`. -/
theorem simsH_matAct_smul {ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℂ) (v : κ → ℂ) (X : V) :
    matAct M (fun k => v k • X) = fun i => (M *ᵥ v) i • X := by
  funext i
  simp only [matAct, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]

/-! ### The Sims form (2.20) -/

/-- Miao, (2.20), p. 58: `Γ₀y_t = Γ₁y_{t−1} + Ψε_t + Πη_t` for `t ≥ 1`, with `y` and the
prediction error `η` adapted ("all variables dated `t` are observable at `t`", p. 59) and `η` a
martingale difference, `E_t η_{t+1} = 0`. (`Pm` stands for `Π`, a reserved token.) The value
`η₀` does not enter the system. -/
def IsSimsSolution {n nε m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (Ψ : Matrix (Fin n) (Fin nε) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) (ε : ℕ → Fin nε → V)
    (y : ℕ → Fin n → V) (η : ℕ → Fin m → V) : Prop :=
  IsAdaptedV E y ∧ IsAdaptedV E η ∧ IsMartingaleDiffProc E η ∧
    ∀ t, matAct Γ₀ (y (t + 1)) = matAct Γ₁ (y t) + matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))

/-- The exogenous shocks of (2.20) (Miao, p. 59): `ε` is adapted, stable and a martingale
difference, `E_t ε_{t+1} = 0`. -/
def IsSimsShock {nε : ℕ} (E : CondExpSystem ℂ V) (ε : ℕ → Fin nε → V) : Prop :=
  IsAdaptedV E ε ∧ IsMartingaleDiffProc E ε ∧ IsStableProc ε

/-- An ordered complex QZ form of the pencil `(Γ₀, Γ₁)` (Miao, p. 59, via Theorem 1.4.4):
unitary `Q`, `Z` with `S = QΓ₀Z`, `T = QΓ₁Z` upper triangular, the first `n_s` pairs
`(sᵢᵢ, tᵢᵢ)` stable (`|tᵢᵢ| < |sᵢᵢ|`) and the remaining `n_u` unstable, none on the unit
circle (`|tᵢᵢ| ≠ |sᵢᵢ|`). For a regular pencil without generalized eigenvalues of modulus one
such a form exists (`theorem_1_4_4_stable`, `isSimsQZ_of_regular`). -/
structure IsSimsQZ {ns nu : ℕ} (G₀ G₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ) : Prop where
  unitary_Q : Q ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ
  unitary_Z : Z ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ
  upper_S : (Q * G₀ * Z).IsUpperTriangular
  upper_T : (Q * G₁ * Z).IsUpperTriangular
  ord : ∀ i : Fin (ns + nu), i.val < ns ↔ ‖(Q * G₁ * Z) i i‖ < ‖(Q * G₀ * Z) i i‖
  off_circle : ∀ i, ‖(Q * G₁ * Z) i i‖ ≠ ‖(Q * G₀ * Z) i i‖

/-- Miao, p. 59: for a regular pencil `(Γ₀, Γ₁)` (Assumption 1.4.1) without generalized
eigenvalues on the unit circle, any QZ form with the stable pairs first is an `IsSimsQZ`; such a
form exists by `theorem_1_4_4_stable`. -/
theorem isSimsQZ_of_regular {ns nu : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hreg : IsRegular Γ₀ Γ₁) (hcirc : ∀ lam ∈ genEigenvalues Γ₀ Γ₁, ‖lam‖ ≠ 1)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin (ns + nu)) ℂ)
    (hS : (Q * Γ₀ * Z).IsUpperTriangular) (hT : (Q * Γ₁ * Z).IsUpperTriangular)
    (hord : ∀ i : Fin (ns + nu), i.val < ns ↔ ‖(Q * Γ₁ * Z) i i‖ < ‖(Q * Γ₀ * Z) i i‖) :
    IsSimsQZ Γ₀ Γ₁ Q Z :=
  ⟨hQ, hZ, hS, hT, hord, diag_off_circle hreg hQ hZ hS hT hcirc⟩

/-- **Assumption 2.3.1** (Miao, p. 60): the column space of `Q₂.Ψ` is contained in that of
`Q₂.Π`, i.e. `Q₂.Ψ = Q₂.ΠΛ` for some `m × n_ε` matrix `Λ`. -/
def SimsAssumption1 {ns nu nε m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ) (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) : Prop :=
  ∃ Λ : Matrix (Fin m) (Fin nε) ℂ, simsBot Q * Ψ = simsBot Q * Pm * Λ

/-- **Assumption 2.3.2** (Miao, p. 61): `Q₁.Π = ΞQ₂.Π` for some `n_s × n_u` matrix `Ξ`. -/
def SimsAssumption2 {ns nu m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) : Prop :=
  ∃ Ξ : Matrix (Fin ns) (Fin nu) ℂ, simsTop Q * Pm = Ξ * (simsBot Q * Pm)

/-- The unitary change of variables `y* = Zᴴy` (Miao, p. 59): `Γ₀b = Γ₁a + w` iff
`S(Zᴴb) = T(Zᴴa) + Qw` with `S = QΓ₀Z`, `T = QΓ₁Z`. -/
theorem simsH_transform {n : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (a b w : Fin n → V) :
    matAct Γ₀ b = matAct Γ₁ a + w ↔
      matAct (Q * Γ₀ * Z) (matAct (star Z) b) = matAct (Q * Γ₁ * Z) (matAct (star Z) a) +
        matAct Q w := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hZ
  have hQQ : star Q * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ
  have key : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → V),
      matAct (Q * M * Z) (matAct (star Z) v) = matAct Q (matAct M v) := fun M v => by
    simp only [matAct_mul, Matrix.mul_assoc, hZZ, Matrix.mul_one]
  simp only [key, ← matAct_add]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have := congrArg (matAct (star Q)) h
  simpa only [matAct_mul, ← Matrix.mul_assoc, hQQ, Matrix.one_mul, matAct_one] using this

/-- Miao, (2.21), p. 59: in the coordinates `y* = Zᴴy = (s, u)`, the equation
`Γ₀b = Γ₁a + w` (`b = y_t`, `a = y_{t−1}`, `w = Ψε_t + Πη_t`) is the pair of block rows
`S₁₁s_t + S₁₂u_t = T₁₁s_{t−1} + T₁₂u_{t−1} + Q₁.w` and `S₂₂u_t = T₂₂u_{t−1} + Q₂.w`. -/
theorem eq_2_21 {ns nu : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) (a b w : Fin (ns + nu) → V) :
    matAct Γ₀ b = matAct Γ₁ a + w ↔
      (matAct (sims11 (Q * Γ₀ * Z)) (matAct (simsTop (star Z)) b) +
          matAct (sims12 (Q * Γ₀ * Z)) (matAct (simsBot (star Z)) b) =
        matAct (sims11 (Q * Γ₁ * Z)) (matAct (simsTop (star Z)) a) +
          matAct (sims12 (Q * Γ₁ * Z)) (matAct (simsBot (star Z)) a) + matAct (simsTop Q) w) ∧
      matAct (sims22 (Q * Γ₀ * Z)) (matAct (simsBot (star Z)) b) =
        matAct (sims22 (Q * Γ₁ * Z)) (matAct (simsBot (star Z)) a) + matAct (simsBot Q) w := by
  rw [simsH_transform hqz.unitary_Q hqz.unitary_Z, klS_blocks_iff hqz.upper_S hqz.upper_T]
  rfl

/-! ### The forward solution (2.22) and `u_t = 0` -/

/-- The pathwise system `E_t = id` on `V`, used for identities that hold realization by
realization (no expectations are taken). -/
noncomputable def simsH_idSystem : CondExpSystem ℂ V where
  E _ := ContinuousLinearMap.id ℂ V
  norm_le _ := ContinuousLinearMap.norm_id_le
  tower_le _ _ _ := ContinuousLinearMap.id_comp _
  tower_ge _ _ _ := ContinuousLinearMap.id_comp _

theorem simsH_Evec_id {ι : Type*} (t : ℕ) (x : ι → V) : Evec simsH_idSystem t x = x := rfl

/-- The unstable block solved forward pathwise: a stable `u` with
`S₂₂u_{t+1} = T₂₂u_t + c_{t+1}` is the forward sum `∑ⱼ (T₂₂⁻¹S₂₂)ʲ (−T₂₂⁻¹c_{t+1+j})`. -/
theorem simsH_fwd_data [CompleteSpace V] {p : ℕ} {S22 T22 : Matrix (Fin p) (Fin p) ℂ}
    (hT22 : T22.det ≠ 0) (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖)
    {u c : ℕ → Fin p → V} (hu : IsStableProc u)
    (h : ∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) :
    ∃ K, (∀ t, ‖-matAct T22⁻¹ (c (t + 1))‖ ≤ K) ∧ ∀ t, u t =
      klS_fwd simsH_idSystem (T22⁻¹ * S22) (fun t => -matAct T22⁻¹ (c (t + 1))) t := by
  have hc : ∀ t, c (t + 1) = matAct S22 (u (t + 1)) - matAct T22 (u t) := fun t => by
    rw [h t]
    abel
  have hcs : IsStableProc fun t => -matAct T22⁻¹ (c (t + 1)) := by
    have := klS_stable_matAct (klS_stable_sub (klS_stable_matAct (klS_stable_shift hu 1) S22)
      (klS_stable_matAct hu T22)) (-T22⁻¹)
    simpa only [klS_neg_matAct, hc] using this
  obtain ⟨K, -, hK⟩ := klS_stable_bound hcs
  exact ⟨K, hK, fun t => klS_eq_fwd simsH_idSystem (klS_summable_ent hN) hK hu (fun _ => rfl)
    (fun t => (klS_solve_fwd hT22 _ _ _).1 (h t)) t⟩

/-- Miao, (2.22) as corrected, p. 59. From `S₂₂u_t = T₂₂u_{t−1} + Q₂.(Ψε_t + Πη_t)`, written
`S₂₂u_{t+1} = T₂₂u_t + c_{t+1}`, a stable `u` satisfies (pathwise, without expectations)
`u_t = −∑_{j≥1} (T₂₂⁻¹S₂₂)^{j−1} T₂₂⁻¹ c_{t+j}`, here with the summation index shifted to
`j ≥ 0`. The book prints `u_t = −T₂₂⁻¹∑_{j≥1} (T₂₂⁻¹S₂₂)ʲ c_{t+j}`, which is false
(`eq_2_22_printed_false`). -/
theorem eq_2_22 [CompleteSpace V] {p : ℕ} {S22 T22 : Matrix (Fin p) (Fin p) ℂ}
    (hT22 : T22.det ≠ 0) (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖)
    {u c : ℕ → Fin p → V} (hu : IsStableProc u)
    (h : ∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) (t : ℕ) :
    u t = -∑' j, matAct ((T22⁻¹ * S22) ^ j * T22⁻¹) (c (t + 1 + j)) := by
  obtain ⟨K, -, hK⟩ := simsH_fwd_data hT22 hN hu h
  rw [hK t, klS_fwd, ← tsum_neg]
  congr 1
  funext j
  rw [simsH_Evec_id, klS_matAct_neg, matAct_mul, show t + j + 1 = t + 1 + j by ring]

/-- Miao, p. 60 ("Taking expectations `E_t` gives `E_t u_t = u_t = 0`"): if moreover `u` is
adapted and `c` is a martingale difference (`E_t c_{t+1} = 0`), then `u_t = 0`, because
`E_t c_{t+j} = 0` for all `j ≥ 1` and `E_t` passes through the convergent forward sum. -/
theorem eq_2_22_expect [CompleteSpace V] (E : CondExpSystem ℂ V) {p : ℕ}
    {S22 T22 : Matrix (Fin p) (Fin p) ℂ} (hT22 : T22.det ≠ 0)
    (hN : Summable fun j => ‖mclm ((T22⁻¹ * S22) ^ j)‖) {u c : ℕ → Fin p → V}
    (hu : IsStableProc u) (hua : ∀ t, Evec E t (u t) = u t)
    (hcm : ∀ t, Evec E t (c (t + 1)) = 0)
    (h : ∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) (t : ℕ) : u t = 0 := by
  obtain ⟨K, hKb, hK⟩ := simsH_fwd_data hT22 hN hu h
  have hE : ∀ j, Evec E t (c (t + j + 1)) = 0 := fun j => by
    rw [← klS_Evec_tower_le E (Nat.le_add_right t j), hcm, klS_Evec_zero]
  rw [← hua t, hK t, klS_fwd, ← klS_EvecCLM_apply, (klS_EvecCLM E t (Fin p)).map_tsum
    (klS_fwd_summable simsH_idSystem (klS_summable_ent hN) hKb t)]
  simp only [klS_EvecCLM_apply, simsH_Evec_id, Evec_matAct, klS_Evec_neg, hE, klS_matAct_zero,
    neg_zero, tsum_zero]

/-- Miao, p. 60: every stable solution of (2.20) has `u_t = Z₂ᴴy_t = 0` for all `t`
(including `t = 0`). This uses only that `u` is adapted and stable and that `ε`, `η` are
martingale differences; no condition on `Ψ`, `Π` is needed. -/
theorem sims_u_eq_zero [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) : matAct (simsBot (star Z)) (y t) = 0 := by
  obtain ⟨hya, -, hηm, heq⟩ := hsol
  refine eq_2_22_expect E (det_T22_ne_zero hqz.upper_T hqz.ord hqz.off_circle)
    (summable_Mu hqz.upper_S hqz.upper_T hqz.ord hqz.off_circle)
    (c := fun t => matAct (simsBot Q) (matAct Ψ (ε t) + matAct Pm (η t)))
    (klS_stable_matAct hy _) (fun t => by rw [Evec_matAct, show Evec E t (y t) = y t from
      funext (hya t)]) (fun t => ?_) (fun t => ?_) t
  · rw [Evec_matAct, klS_Evec_add, Evec_matAct, Evec_matAct,
      show Evec E t (ε (t + 1)) = 0 from funext (hεm t),
      show Evec E t (η (t + 1)) = 0 from funext (hηm t)]
    simp only [klS_matAct_zero, add_zero]
  · have := ((eq_2_21 hqz (y t) (y (t + 1)) _).1 (by rw [heq t, add_assoc])).2
    exact this

/-- Miao, p. 60: "It follows that `Z₂ᴴy₀ = 0`", the restriction on the initial value. -/
theorem sims_Z2_y0 [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y) :
    matAct (simsBot (star Z)) (y 0) = 0 :=
  sims_u_eq_zero E hqz hεm hsol hy 0

/-- Miao, (2.23), p. 60: in every stable solution, `Q₂.(Ψε_t + Πη_t) = 0` for `t ≥ 1`. -/
theorem eq_2_23 [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) : matAct (simsBot Q) (matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))) = 0 := by
  have h := ((eq_2_21 hqz (y t) (y (t + 1)) _).1 (by rw [hsol.2.2.2 t, add_assoc])).2
  rw [sims_u_eq_zero E hqz hεm hsol hy, sims_u_eq_zero E hqz hεm hsol hy, klS_matAct_zero,
    klS_matAct_zero, zero_add] at h
  exact h.symm

/-! ### Lemma 2.3.1 and the two assumptions -/

/-- **Lemma 2.3.1** (Miao, p. 60), with `A = Q₂.Ψ` and `B = Q₂.Π`: for every `ε ∈ ℂ^{n_ε}`
there is `η ∈ ℂ^m` with `Aε + Bη = 0` iff `A = BΛ` for some `m × n_ε` matrix `Λ`. ("For
every `ε_t`" is read as "for every vector value".) The book's proof takes the `j`-th column of
`Λ` to be a solution `η` for `ε = I_j`; that gives `A = −BΛ`, so the column is `−η`. -/
theorem lemma_2_3_1 {p nε m : ℕ} (A : Matrix (Fin p) (Fin nε) ℂ) (B : Matrix (Fin p) (Fin m) ℂ) :
    (∀ e : Fin nε → ℂ, ∃ h : Fin m → ℂ, A *ᵥ e + B *ᵥ h = 0) ↔
      ∃ Λ : Matrix (Fin m) (Fin nε) ℂ, A = B * Λ := by
  constructor
  · intro H
    choose h hh using fun j : Fin nε => H (Pi.single j 1)
    refine ⟨Matrix.of fun k j => -h j k, ?_⟩
    ext i j
    have := congrFun (hh j) i
    simp only [Matrix.mulVec_single_one, Pi.add_apply, Matrix.col_apply, Pi.zero_apply,
      Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_neg, Finset.sum_neg_distrib]
    linear_combination this
  · rintro ⟨Λ, rfl⟩ e
    exact ⟨-(Λ *ᵥ e), by rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, add_neg_cancel]⟩

/-- Lemma 2.3.1 in the notation of (2.23): (2.23) is solvable in `η` for every value of `ε` iff
Assumption 2.3.1 holds. -/
theorem lemma_2_3_1_sims {ns nu nε m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ) (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) :
    (∀ e : Fin nε → ℂ, ∃ h : Fin m → ℂ, simsBot Q *ᵥ (Ψ *ᵥ e + Pm *ᵥ h) = 0) ↔
      SimsAssumption1 Q Ψ Pm := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  exact lemma_2_3_1 _ _

/-- A vector equation with random right-hand sides proportional to one random variable
`X ≠ 0` has a scalar solution (apply a continuous functional `g` with `g X = ‖X‖`, by
Hahn–Banach). -/
theorem simsH_scalar_of_vec {p nε m : ℕ} (A : Matrix (Fin p) (Fin nε) ℂ)
    (B : Matrix (Fin p) (Fin m) ℂ) {X : V} (hX : X ≠ 0) (e : Fin nε → ℂ) (h : Fin m → V)
    (H : matAct A (fun i => e i • X) + matAct B h = 0) :
    ∃ h' : Fin m → ℂ, A *ᵥ e + B *ᵥ h' = 0 := by
  obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ X (norm_ne_zero_iff.2 hX)
  have hXn : ((‖X‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hX
  have key : A *ᵥ (((‖X‖ : ℝ) : ℂ) • e) + B *ᵥ (fun k => g (h k)) = 0 := by
    funext i
    have := congrArg g (congrFun H i)
    simp only [Pi.add_apply, matAct, map_add, map_sum, map_smul, hg, smul_eq_mul,
      Pi.zero_apply, map_zero] at this
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    rw [← this]
    congr 1
    exact Finset.sum_congr rfl fun j _ => congrArg (A i j * ·) (mul_comm _ _)
  refine ⟨(((‖X‖ : ℝ) : ℂ))⁻¹ • fun k => g (h k), ?_⟩
  have := congrArg ((((‖X‖ : ℝ) : ℂ))⁻¹ • ·) key
  simpa only [Matrix.mulVec_smul, smul_add, smul_smul, inv_mul_cancel₀ hXn, one_smul,
    smul_zero] using this

/-- Lemma 2.3.1 with random right-hand sides (Miao, p. 60, "for every `ε_t`" read as "for
every random vector"): if `V ≠ 0`, (2.23) `Aε + Bη = 0` is solvable in `η ∈ V^m` for every
`ε ∈ V^{n_ε}` iff `A = BΛ` for some matrix `Λ`. -/
theorem lemma_2_3_1_random [Nontrivial V] {p nε m : ℕ} (A : Matrix (Fin p) (Fin nε) ℂ)
    (B : Matrix (Fin p) (Fin m) ℂ) :
    (∀ e : Fin nε → V, ∃ h : Fin m → V, matAct A e + matAct B h = 0) ↔
      ∃ Λ : Matrix (Fin m) (Fin nε) ℂ, A = B * Λ := by
  constructor
  · intro H
    obtain ⟨X, hX⟩ := exists_ne (0 : V)
    refine (lemma_2_3_1 A B).1 fun e => ?_
    obtain ⟨h, hh⟩ := H fun i => e i • X
    exact simsH_scalar_of_vec A B hX e h hh
  · rintro ⟨Λ, rfl⟩ e
    exact ⟨-matAct Λ e, by rw [klS_matAct_neg, matAct_mul, add_neg_cancel]⟩

/-- Miao, p. 60: Assumption 2.3.1 "generalizes the usual existence condition `n_u ≤ m`… we may
have existence even if `n_u > m`": with `n_u = 2`, `m = 1`, `Q = I` and `Ψ = Π = (1, 1)ᵀ`,
Assumption 2.3.1 holds (`Λ = 1`) and `Q₂.Ψ ≠ 0`. -/
theorem assumption_2_3_1_nu_gt_m :
    ∃ (Q : Matrix (Fin (0 + 2)) (Fin (0 + 2)) ℂ) (Ψ Pm : Matrix (Fin (0 + 2)) (Fin 1) ℂ),
      SimsAssumption1 Q Ψ Pm ∧ simsBot Q * Ψ ≠ 0 := by
  refine ⟨1, !![1; 1], !![1; 1], ⟨1, by rw [Matrix.mul_one]⟩, fun h => ?_⟩
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.one_apply] at this

/-- Assumption 2.3.2 as a kernel condition: `C = ΞB` for some `Ξ` iff `ker B ⊆ ker C`. For
`B = Q₂.Π`, `C = Q₁.Π`: a combination of prediction errors that does not move the unstable
block does not move the stable block either. -/
theorem simsH_factor_iff {p q m : ℕ} (B : Matrix (Fin p) (Fin m) ℂ)
    (C : Matrix (Fin q) (Fin m) ℂ) :
    (∀ v, B *ᵥ v = 0 → C *ᵥ v = 0) ↔ ∃ Ξ : Matrix (Fin q) (Fin p) ℂ, C = Ξ * B := by
  constructor
  · intro H
    have hk : LinearMap.ker (Matrix.mulVecLin B) ≤ LinearMap.ker (Matrix.mulVecLin C) :=
      fun v hv => H v hv
    obtain ⟨h, hh⟩ := LinearMap.exists_extend
      (((LinearMap.ker (Matrix.mulVecLin B)).liftQ (Matrix.mulVecLin C) hk).comp
        (Matrix.mulVecLin B).quotKerEquivRange.symm.toLinearMap)
    refine ⟨LinearMap.toMatrix' h, ?_⟩
    have hv : ∀ v, C *ᵥ v = (LinearMap.toMatrix' h * B) *ᵥ v := fun v => by
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      have := LinearMap.congr_fun hh ⟨B *ᵥ v, LinearMap.mem_range_self _ v⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        LinearEquiv.coe_coe] at this
      rw [this]
      change _ = (LinearMap.ker (Matrix.mulVecLin B)).liftQ (Matrix.mulVecLin C) hk
        ((Matrix.mulVecLin B).quotKerEquivRange.symm ⟨(Matrix.mulVecLin B) v, _⟩)
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using this
  · rintro ⟨Ξ, rfl⟩ v hv
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

/-- Assumption 2.3.2 iff `ker(Q₂.Π) ⊆ ker(Q₁.Π)`. -/
theorem simsAssumption2_iff_ker {ns nu m : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ) :
    SimsAssumption2 Q Pm ↔
      ∀ v, (simsBot Q * Pm) *ᵥ v = 0 → (simsTop Q * Pm) *ᵥ v = 0 :=
  (simsH_factor_iff _ _).symm

/-! ### The matrices of (2.24) and the solution matrices `Θ₁`, `Θ₂` -/

/-- The left matrix `[[S₁₁, S₁₂ − ΞS₂₂], [0, I]]` of (2.24) (Miao, p. 61). -/
def simsGmat {ns nu : ℕ} (S : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  simsBlk (sims11 S) (sims12 S - Ξ * sims22 S) 0 1

/-- The matrix `[[T₁₁, T₁₂ − ΞT₂₂], [0, 0]]` of (2.24) (Miao, p. 61). -/
def simsHmat {ns nu : ℕ} (T : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  simsBlk (sims11 T) (sims12 T - Ξ * sims22 T) 0 0

/-- The matrix `[[Q₁. − ΞQ₂.], [0]]` of (2.24) (Miao, p. 61). -/
def simsKmat {ns nu : ℕ} (Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  simsRows (simsTop Q - Ξ * simsBot Q) 0

/-- `Θ₁ = Z G⁻¹ H Zᴴ` (Miao, p. 61, corrected: the book omits the final `Zᴴ`, see
`theta_1_printed_false`), with `G = simsGmat S Ξ`, `H = simsHmat T Ξ`. -/
noncomputable def simsTheta1 {ns nu : ℕ} (Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ :=
  Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsHmat (Q * Γ₁ * Z) Ξ * star Z

/-- `Θ₂ = Z G⁻¹ [[Q₁. − ΞQ₂.], [0]] Ψ` (Miao, p. 61, as printed). -/
noncomputable def simsTheta2 {ns nu nε : ℕ} (Γ₀ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) (Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ) :
    Matrix (Fin (ns + nu)) (Fin nε) ℂ :=
  Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsKmat Q Ξ * Ψ

/-- `G` is invertible: `det G = det S₁₁ ≠ 0`. -/
theorem simsGmat_det {ns nu : ℕ} {S T : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hS : S.IsUpperTriangular) (hord : ∀ i : Fin (ns + nu), i.val < ns ↔ ‖T i i‖ < ‖S i i‖)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) : (simsGmat S Ξ).det ≠ 0 := by
  rw [simsGmat, simsBlk_det, Matrix.det_one, mul_one]
  exact det_S11_ne_zero hS hord

omit [NormedSpace ℂ V] in
theorem simsH_add_comp {ι κ : Type*} (x z : ι → V) (f : κ → ι) : (x + z) ∘ f = x ∘ f + z ∘ f :=
  rfl

/-- Solving `Gx' = Hx + k` for `y' = Zx'` in terms of `y = Zx` (Miao, p. 61, "Using
`y_t = Zy*_t` and the above equation"): `Zx' = (ZG⁻¹HZᴴ)(Zx) + ZG⁻¹k`. -/
theorem simsH_solve_G {n : ℕ} {G H Z : Matrix (Fin n) (Fin n) ℂ} (hG : G.det ≠ 0)
    (hZ : Z ∈ Matrix.unitaryGroup (Fin n) ℂ) (x x' k : Fin n → V) :
    matAct G x' = matAct H x + k ↔
      matAct Z x' = matAct (Z * G⁻¹ * H * star Z) (matAct Z x) + matAct (Z * G⁻¹) k := by
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hZ
  have hback : ∀ v : Fin n → V, matAct (star Z) (matAct Z v) = v := fun v => by
    rw [matAct_mul, hZZ', matAct_one]
  have e1 : matAct (Z * G⁻¹ * H * star Z) (matAct Z x) =
      matAct Z (matAct G⁻¹ (matAct H x)) := by
    simp only [matAct_mul, Matrix.mul_assoc, hZZ', Matrix.mul_one]
  rw [e1, ← matAct_mul Z G⁻¹ k, ← matAct_add, ← matAct_add]
  constructor
  · intro h
    rw [← h, klS_matAct_inv_mul hG]
  · intro h
    have h1 := congrArg (matAct (star Z)) h
    rw [hback, hback] at h1
    rw [h1, klS_matAct_mul_inv hG]

/-- Miao, (2.24), p. 61: premultiplying (2.21) by `[I  −Ξ]` and appending `u_t = 0`, every
stable solution satisfies `G y*_t = H y*_{t−1} + [[Q₁. − ΞQ₂.], [0]](Ψε_t + Πη_t)`, for any
`n_s × n_u` matrix `Ξ` (Assumption 2.3.2 is not needed for this step). -/
theorem eq_2_24 [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) (t : ℕ) :
    matAct (simsGmat (Q * Γ₀ * Z) Ξ) (matAct (star Z) (y (t + 1))) =
      matAct (simsHmat (Q * Γ₁ * Z) Ξ) (matAct (star Z) (y t)) +
        matAct (simsKmat Q Ξ) (matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))) := by
  have hu := sims_u_eq_zero E hqz hεm hsol hy
  have h23 := eq_2_23 E hqz hεm hsol hy t
  have htop := ((eq_2_21 hqz (y t) (y (t + 1)) _).1 (by rw [hsol.2.2.2 t, add_assoc])).1
  rw [hu, hu, klS_matAct_zero, klS_matAct_zero, add_zero, add_zero] at htop
  refine klS_ext_blocks ?_ ?_
  · rw [simsGmat, simsH_blk_top, simsH_add_comp, simsHmat, simsH_blk_top, simsKmat,
      simsH_top_matAct (simsRows _ _), simsRows_top]
    simp only [simsH_top_matAct, simsH_bot_matAct, hu, klS_matAct_zero, add_zero,
      klS_sub_matAct, ← matAct_mul, h23, sub_zero]
    exact htop
  · rw [simsGmat, simsH_blk_bot, simsH_add_comp, simsHmat, simsH_blk_bot, simsKmat,
      simsH_bot_matAct (simsRows _ _), simsRows_bot]
    simp only [simsH_bot_matAct, hu, klS_zero_matAct, matAct_one, add_zero]

/-- Miao, p. 61: under Assumption 2.3.2 (`Q₁.Π = ΞQ₂.Π`) the prediction errors drop out of
(2.24): `[[Q₁. − ΞQ₂.], [0]]Π = 0`. -/
theorem simsKmat_mul_Pm {ns nu m : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} {Ξ : Matrix (Fin ns) (Fin nu) ℂ}
    (hΞ : simsTop Q * Pm = Ξ * (simsBot Q * Pm)) : simsKmat Q Ξ * Pm = 0 := by
  rw [simsKmat, simsRows_mul, Matrix.sub_mul, Matrix.mul_assoc, ← hΞ, sub_self,
    Matrix.zero_mul]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [simsRows]

/-- **Theorem 2.3.1, the solution formula** (Miao, p. 61). Under Assumption 2.3.2
(`Q₁.Π = ΞQ₂.Π`), every stable solution of (2.20) satisfies `y_t = Θ₁y_{t−1} + Θ₂ε_t` with
`Θ₁ = ZG⁻¹HZᴴ` and `Θ₂ = ZG⁻¹[[Q₁. − ΞQ₂.], [0]]Ψ`. -/
theorem theorem_2_3_1_theta [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {Ξ : Matrix (Fin ns) (Fin nu) ℂ} (hΞ : simsTop Q * Pm = Ξ * (simsBot Q * Pm))
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) :
    y (t + 1) = matAct (simsTheta1 Γ₀ Γ₁ Q Z Ξ) (y t) +
      matAct (simsTheta2 Γ₀ Q Z Ξ Ψ) (ε (t + 1)) := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hqz.unitary_Z
  have hback : ∀ v : Fin (ns + nu) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  have h := eq_2_24 E hqz hεm hsol hy Ξ t
  rw [matAct_add, matAct_mul (simsKmat Q Ξ) Pm, simsKmat_mul_Pm hΞ, klS_zero_matAct,
    add_zero] at h
  have h' := (simsH_solve_G (simsGmat_det hqz.upper_S hqz.ord Ξ) hqz.unitary_Z _ _ _).1 h
  rw [hback, hback] at h'
  rw [h']
  congr 1
  simp only [simsTheta2, matAct_mul, Matrix.mul_assoc]

/-- **Theorem 2.3.1, uniqueness** (Miao, p. 61). Under Assumption 2.3.2, two stable solutions
of (2.20) for the same `ε` with the same initial value `y₀` coincide (whatever their
prediction errors). Assumption 2.3.1 is not needed. -/
theorem theorem_2_3_1_uniqueness [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hA2 : SimsAssumption2 Q Pm) {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε)
    {y y' : ℕ → Fin (ns + nu) → V} {η η' : ℕ → Fin m → V}
    (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (hsol' : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y' η') (hy' : IsStableProc y') (h0 : y 0 = y' 0) :
    y = y' := by
  obtain ⟨Ξ, hΞ⟩ := hA2
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [theorem_2_3_1_theta E hqz hΞ hεm hsol hy t, theorem_2_3_1_theta E hqz hΞ hεm hsol' hy' t,
      ih]

/-! ### Existence -/

omit [NormedSpace ℂ V] in
theorem simsH_stable_zero {ι : Type*} : IsStableProc (fun _ : ℕ => (0 : ι → V)) :=
  ⟨1, one_pos, fun _ _ => by simp⟩

/-- The construction behind the existence half of Theorem 2.3.1 (Miao, pp. 60–61). Given a
stable adapted `ε` and a stable adapted martingale-difference `η` satisfying (2.23)
(`Q₂.(Ψε_t + Πη_t) = 0`), and an `F₀`-measurable `y₀` with `Z₂ᴴy₀ = 0`, the recursion
`u_t = 0`, `s_t = S₁₁⁻¹T₁₁s_{t−1} + S₁₁⁻¹Q₁.(Ψε_t + Πη_t)`, `s₀ = Z₁ᴴy₀` defines a stable
solution `y_t = Z(s_t, 0)` of (2.20) with prediction error `η`. -/
theorem simsH_core_exists [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ε : ℕ → Fin nε → V} (hεa : IsAdaptedV E ε) (hεs : IsStableProc ε)
    {η : ℕ → Fin m → V} (hηa : IsAdaptedV E η) (hηm : IsMartingaleDiffProc E η)
    (hηs : IsStableProc η)
    (h23 : ∀ t, matAct (simsBot Q) (matAct Ψ (ε (t + 1)) + matAct Pm (η (t + 1))) = 0)
    (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃ y, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η ∧ IsStableProc y ∧ y 0 = y₀ := by
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hqz.unitary_Z
  have hZZ' : star Z * Z = 1 := Matrix.mem_unitaryGroup_iff'.1 hqz.unitary_Z
  have hS11 := det_S11_ne_zero hqz.upper_S hqz.ord
  set w : ℕ → Fin (ns + nu) → V := fun t => matAct Ψ (ε t) + matAct Pm (η t) with hw
  have hwa : ∀ t, Evec E t (w t) = w t := fun t => by
    rw [hw]
    simp only [klS_Evec_add, Evec_matAct, show Evec E t (ε t) = ε t from funext (hεa t),
      show Evec E t (η t) = η t from funext (hηa t)]
  have hws : IsStableProc w := klS_stable_add (klS_stable_matAct hεs Ψ) (klS_stable_matAct hηs Pm)
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℕ → Fin ns → V, s 0 = matAct (simsTop (star Z)) y₀ ∧
      ∀ t, s (t + 1) = matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * sims11 (Q * Γ₁ * Z)) (s t) +
        matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * simsTop Q) (w (t + 1)) :=
    ⟨fun t => Nat.rec (matAct (simsTop (star Z)) y₀)
      (fun t st => matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * sims11 (Q * Γ₁ * Z)) st +
        matAct ((sims11 (Q * Γ₀ * Z))⁻¹ * simsTop Q) (w (t + 1))) t,
      rfl, fun _ => rfl⟩
  have hss : IsStableProc s := klS_stable_of_rec
    (klS_summable_ent (summable_Ms hqz.upper_S hqz.upper_T hqz.ord))
    (klS_stable_matAct (klS_stable_shift hws 1) _) hs
  have hsa : ∀ t, Evec E t (s t) = s t := by
    intro t
    induction t with
    | zero => rw [hs0, Evec_matAct, hy₀a]
    | succ t ih => rw [hs, klS_Evec_add, Evec_matAct, Evec_matAct, klS_adapted_succ E ih, hwa]
  set x : ℕ → Fin (ns + nu) → V := fun t => Fin.append (s t) 0 with hx
  have hxs : ∀ t, matAct (star Z) (matAct Z (x t)) = x t := fun t => by
    rw [matAct_mul, hZZ', matAct_one]
  have hxt : ∀ t, matAct (simsTop (star Z)) (matAct Z (x t)) = s t := fun t => by
    rw [← simsH_top_matAct, hxs, hx, klS_append_castAdd]
  have hxb : ∀ t, matAct (simsBot (star Z)) (matAct Z (x t)) = 0 := fun t => by
    rw [← simsH_bot_matAct, hxs, hx, klS_append_natAdd]
  refine ⟨fun t => matAct Z (x t), ⟨fun t i => ?_, hηa, hηm, fun t => ?_⟩, ?_, ?_⟩
  · change Evec E t (matAct Z (x t)) i = matAct Z (x t) i
    rw [Evec_matAct, hx, klS_Evec_append, hsa, klS_Evec_zero]
  · rw [add_assoc]
    refine (eq_2_21 hqz _ _ (w (t + 1))).2 ⟨?_, ?_⟩
    · rw [hxt, hxt, hxb, hxb, klS_matAct_zero, klS_matAct_zero, add_zero, add_zero, hs,
        matAct_add, ← matAct_mul, ← matAct_mul, klS_matAct_mul_inv hS11,
        klS_matAct_mul_inv hS11]
    · rw [hxb, hxb, klS_matAct_zero, klS_matAct_zero, zero_add]
      exact (h23 t).symm
  · exact klS_stable_matAct (klS_stable_append hss simsH_stable_zero) Z
  · change matAct Z (Fin.append (s 0) 0) = y₀
    have : Fin.append (s 0) 0 = matAct (star Z) y₀ := by
      refine klS_ext_blocks ?_ ?_
      · rw [klS_append_castAdd, hs0]
        rfl
      · rw [klS_append_natAdd, simsH_bot_matAct, hy₀]
    rw [this, matAct_mul, hZZ, matAct_one]

/-- **Theorem 2.3.1, existence** (Miao, pp. 60–61). Under Assumption 2.3.1 (`Q₂.Ψ = Q₂.ΠΛ`),
for every exogenous shock `ε` (adapted, stable, martingale difference) and every
`F₀`-measurable `y₀` with `Z₂ᴴy₀ = 0` there is a stable solution of (2.20) with `y_0 = y₀`,
whose prediction error is `η_t = −Λε_t` (stable). Assumption 2.3.2 is not needed. -/
theorem theorem_2_3_1_existence [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {Λ : Matrix (Fin m) (Fin nε) ℂ} (hΛ : simsBot Q * Ψ = simsBot Q * Pm * Λ)
    {ε : ℕ → Fin nε → V} (hε : IsSimsShock E ε)
    (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃ y, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y (fun t => -matAct Λ (ε t)) ∧ IsStableProc y ∧
      y 0 = y₀ := by
  obtain ⟨hεa, hεm, hεs⟩ := hε
  refine simsH_core_exists E hqz hεa hεs (fun t i => ?_) (fun t i => ?_)
    (by simpa only [klS_neg_matAct] using klS_stable_matAct hεs (-Λ)) (fun t => ?_) y₀ hy₀a hy₀
  · change Evec E t (-matAct Λ (ε t)) i = -matAct Λ (ε t) i
    rw [klS_Evec_neg, Evec_matAct, show Evec E t (ε t) = ε t from funext (hεa t)]
    rfl
  · change Evec E t (-matAct Λ (ε (t + 1))) i = (0 : Fin m → V) i
    rw [klS_Evec_neg, Evec_matAct, show Evec E t (ε (t + 1)) = 0 from funext (hεm t),
      klS_matAct_zero, neg_zero]
  · rw [matAct_add, klS_matAct_neg, klS_matAct_neg, matAct_mul, matAct_mul, matAct_mul, ← hΛ,
      add_neg_cancel]

/-- **Theorem 2.3.1, sufficiency** (Miao, p. 61). Under Assumptions 2.3.1 and 2.3.2, for every
exogenous shock `ε` and every `F₀`-measurable `y₀` with `Z₂ᴴy₀ = 0` there is exactly one
stable `y` with `y_0 = y₀` solving (2.20) for some prediction error `η`; it is
`y_t = Θ₁y_{t−1} + Θ₂ε_t` (`theorem_2_3_1_theta`). Uniqueness is of `y`, not of `η`
(see `SimsSVD`). The initial value is free subject to `Z₂ᴴy₀ = 0` (`sims_Z2_y0`). -/
theorem theorem_2_3_1_sufficiency [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hA1 : SimsAssumption1 Q Ψ Pm) (hA2 : SimsAssumption2 Q Pm) {ε : ℕ → Fin nε → V}
    (hε : IsSimsShock E ε) (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃! y, (∃ η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) ∧ IsStableProc y ∧ y 0 = y₀ := by
  obtain ⟨Λ, hΛ⟩ := hA1
  obtain ⟨y, hy1, hy2, hy3⟩ := theorem_2_3_1_existence E hqz hΛ hε y₀ hy₀a hy₀
  refine ⟨y, ⟨⟨_, hy1⟩, hy2, hy3⟩, ?_⟩
  rintro y' ⟨⟨η', h'⟩, hs', h0'⟩
  exact (theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 hy1 hy2 h' hs' (hy3.trans h0'.symm)).symm

/-! ### Necessity -/

/-- A filtration rich enough for the necessity half of Theorem 2.3.1: there is a stable adapted
scalar martingale difference `ζ` with `ζ₁ ≠ 0` (true for `L¹` of any probability space carrying
a nondegenerate shock at date 1, e.g. `simsRich_trunc`). Without such a `ζ` the stochastic
content of (2.20) is void (`theorem_2_3_1_necessity_false`). -/
def SimsRich (E : CondExpSystem ℂ V) : Prop :=
  ∃ ζ : ℕ → V, (∀ t, E.E t (ζ t) = ζ t) ∧ (∀ t, E.E t (ζ (t + 1)) = 0) ∧
    (∃ M, ∀ t, ‖ζ t‖ ≤ M) ∧ ζ 1 ≠ 0

/-- A vector `c` times a stable adapted scalar martingale difference `ζ` is an exogenous
shock. -/
theorem simsH_rich_shock {k : ℕ} (E : CondExpSystem ℂ V) {ζ : ℕ → V}
    (hζa : ∀ t, E.E t (ζ t) = ζ t) (hζm : ∀ t, E.E t (ζ (t + 1)) = 0) {M : ℝ}
    (hζb : ∀ t, ‖ζ t‖ ≤ M) (c : Fin k → ℂ) : IsSimsShock E (fun t i => c i • ζ t) := by
  refine ⟨fun t i => by simp only [map_smul, hζa], fun t i => by simp only [map_smul, hζm,
    smul_zero], isStableProc_of_uniformly_bounded (M := ‖c‖ * M) fun t i => ?_⟩
  rw [norm_smul]
  exact mul_le_mul (norm_le_pi_norm c i) (hζb t) (norm_nonneg _) (norm_nonneg _)

theorem simsH_zero_shock {k : ℕ} (E : CondExpSystem ℂ V) :
    IsSimsShock E (0 : ℕ → Fin k → V) :=
  ⟨fun _ _ => map_zero _, fun _ _ => map_zero _, simsH_stable_zero⟩

theorem simsH_zero_solution {n nε m : ℕ} (E : CondExpSystem ℂ V)
    (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin nε) ℂ)
    (Pm : Matrix (Fin n) (Fin m) ℂ) : IsSimsSolution E Γ₀ Γ₁ Ψ Pm 0 0 0 :=
  ⟨fun _ _ => map_zero _, fun _ _ => map_zero _, fun _ _ => map_zero _, fun _ => by
    simp only [Pi.zero_apply, klS_matAct_zero, add_zero]⟩

/-- **Theorem 2.3.1, necessity of Assumption 2.3.1** (Miao, p. 60, "for a solution to (2.20)
to exist, we must make the following"). If the filtration is rich (`SimsRich`) and (2.20) has a
stable solution for every exogenous shock `ε`, then Assumption 2.3.1 holds: take
`ε_t = eζ_t`; (2.23) at `t = 1` and a functional separating `ζ₁` give a scalar solution of
Lemma 2.3.1's equation for every `e`. -/
theorem theorem_2_3_1_necessity_1 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hex : ∀ ε : ℕ → Fin nε → V, IsSimsShock E ε →
      ∃ y η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η ∧ IsStableProc y) :
    SimsAssumption1 Q Ψ Pm := by
  obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
  refine (lemma_2_3_1 _ _).1 fun e => ?_
  have hsh := simsH_rich_shock E hζa hζm hζb e
  obtain ⟨y, η, hsol, hy⟩ := hex _ hsh
  have h := eq_2_23 E hqz hsh.2.1 hsol hy 0
  rw [matAct_add, matAct_mul, matAct_mul] at h
  exact simsH_scalar_of_vec _ _ hζ1 e _ h

/-- **Theorem 2.3.1, necessity of Assumption 2.3.2** (Miao, pp. 60–61). If the filtration is
rich and the homogeneous system (`ε = 0`) has only the zero stable solution from `y₀ = 0`, then
Assumption 2.3.2 holds. Otherwise there is `v` with `Q₂.Πv = 0`, `Q₁.Πv ≠ 0`, and the
sunspot-like prediction error `η_t = vζ_t` drives a nonzero stable solution. -/
theorem theorem_2_3_1_necessity_2 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (huniq : ∀ y η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm (0 : ℕ → Fin nε → V) y η → IsStableProc y →
      y 0 = 0 → y = 0) :
    SimsAssumption2 Q Pm := by
  obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
  rw [simsAssumption2_iff_ker]
  intro v hv
  by_contra hne
  obtain ⟨hηa, hηm, hηs⟩ := simsH_rich_shock E hζa hζm hζb v
  obtain ⟨y, hsol, hy, hy0⟩ := simsH_core_exists E hqz (simsH_zero_shock E).1
    (simsH_zero_shock E).2.2 hηa hηm hηs (fun t => by
      rw [Pi.zero_apply, klS_matAct_zero, zero_add, simsH_matAct_smul, simsH_matAct_smul,
        Matrix.mulVec_mulVec, hv]
      funext i
      simp) 0 (klS_Evec_zero E 0) (klS_matAct_zero _)
  have he := hsol.2.2.2 0
  rw [huniq y _ hsol hy hy0] at he
  simp only [Pi.zero_apply, klS_matAct_zero, zero_add, simsH_matAct_smul] at he
  have hPv : Pm *ᵥ v = 0 := funext fun i => by
    have := congrFun he i
    simp only [Pi.zero_apply] at this
    exact (smul_eq_zero.1 this.symm).resolve_right hζ1
  exact hne (by rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_zero])

/-- **Theorem 2.3.1** (Sims, Miao, p. 61), the correct form of "Assumptions 2.3.1–2.3.2 are
necessary and sufficient for the existence of a unique stable solution to (2.20)" (the text on
p. 62 calls it "Theorem 2.19"). For a regular pencil with an ordered QZ form and no generalized
eigenvalue on the unit circle, and a rich filtration (`SimsRich`): for every exogenous shock `ε`
and every admissible initial value `y₀` (`F₀`-measurable, `Z₂ᴴy₀ = 0`) there is exactly one
stable `y` with `y_0 = y₀` that solves (2.20) with some prediction error `η` iff Assumptions
2.3.1 and 2.3.2 hold. "Unique" refers to `y`; `η` is unique only when moreover `m = r`
(`corollary_2_3_1`). Sufficiency needs no richness (`theorem_2_3_1_sufficiency`); necessity
fails without it (`theorem_2_3_1_necessity_false`). -/
theorem theorem_2_3_1 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} :
    (∀ ε : ℕ → Fin nε → V, IsSimsShock E ε → ∀ y₀ : Fin (ns + nu) → V, Evec E 0 y₀ = y₀ →
      matAct (simsBot (star Z)) y₀ = 0 →
        ∃! y, (∃ η, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) ∧ IsStableProc y ∧ y 0 = y₀) ↔
      SimsAssumption1 Q Ψ Pm ∧ SimsAssumption2 Q Pm := by
  constructor
  · intro H
    refine ⟨theorem_2_3_1_necessity_1 E hrich hqz fun ε hε => ?_,
      theorem_2_3_1_necessity_2 E hrich hqz (Ψ := Ψ) fun y η hsol hy hy0 => ?_⟩
    · obtain ⟨y, ⟨⟨η, hsol⟩, hy, -⟩, -⟩ := H ε hε 0 (klS_Evec_zero E 0) (klS_matAct_zero _)
      exact ⟨y, η, hsol, hy⟩
    · obtain ⟨y', -, hu⟩ := H 0 (simsH_zero_shock E) 0 (klS_Evec_zero E 0) (klS_matAct_zero _)
      exact (hu y ⟨⟨η, hsol⟩, hy, hy0⟩).trans
        (hu 0 ⟨⟨0, simsH_zero_solution E Γ₀ Γ₁ Ψ Pm⟩, simsH_stable_zero, rfl⟩).symm
  · rintro ⟨hA1, hA2⟩ ε hε y₀ hy₀a hy₀
    exact theorem_2_3_1_sufficiency E hqz hA1 hA2 hε y₀ hy₀a hy₀

/-! ### Counterexamples and a rich filtration -/

/-- The truncation system on `ℓ^∞(ℕ)` (`klM_truncSystem`) is rich: `ζ_t = e_t` is adapted, a
martingale difference, bounded by `1`, and `ζ₁ ≠ 0`. -/
theorem simsRich_trunc : SimsRich klM_truncSystem := by
  refine ⟨fun t => lp.single ⊤ t 1, fun t => ?_, fun t => ?_, ⟨1, fun t => ?_⟩, ?_⟩
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rfl
    · rw [lp.single_apply_ne ⊤ t _ (by omega)]
  · refine lp.ext (funext fun n => ?_)
    change klM_trunc t _ n = _
    rw [klM_trunc_apply]
    split_ifs with h
    · rw [lp.single_apply_ne ⊤ (t + 1) _ (by omega)]
      rfl
    · rfl
  · rw [lp.norm_single ENNReal.zero_lt_top, norm_one]
  · intro h
    have := congrArg (fun f : lp (fun _ : ℕ => ℂ) ⊤ => f 1) h
    simp only [lp.single_apply_self] at this
    exact one_ne_zero this

/-- With `E_t = id` a martingale difference vanishes from date 1 on. -/
theorem simsH_det_mdiff {k : ℕ} {x : ℕ → Fin k → ℂ} (h : IsMartingaleDiffProc klS_detSystem x)
    (t : ℕ) : x (t + 1) = 0 :=
  funext (h t)

/-- With `E_t = id`, the shocks and prediction errors of (2.20) vanish, so `Ψ` and `Π` play no
role. -/
theorem simsH_det_sol_iff {n nε m : ℕ} {Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ}
    {Ψ : Matrix (Fin n) (Fin nε) ℂ} {Pm : Matrix (Fin n) (Fin m) ℂ} {ε : ℕ → Fin nε → ℂ}
    (hεm : IsMartingaleDiffProc klS_detSystem ε) (y : ℕ → Fin n → ℂ) (η : ℕ → Fin m → ℂ) :
    IsSimsSolution klS_detSystem Γ₀ Γ₁ Ψ Pm ε y η ↔
      IsSimsSolution klS_detSystem Γ₀ Γ₁ 0 0 ε y η := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun t => ?_⟩
    have := h4 t
    rw [simsH_det_mdiff hεm t, simsH_det_mdiff h3 t] at this ⊢
    simpa only [klS_matAct_zero, klS_zero_matAct, add_zero] using this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun t => ?_⟩
    have := h4 t
    rw [simsH_det_mdiff hεm t, simsH_det_mdiff h3 t] at this ⊢
    simpa only [klS_matAct_zero, klS_zero_matAct, add_zero] using this

/-- **Counterexample to the necessity half of Theorem 2.3.1 as printed** (Miao, p. 61). In the
deterministic system `E_t = id` (`klS_detSystem`), take `Γ₀ = I`, `Γ₁ = diag(1/2, 2)`,
`Q = Z = I`, `Ψ = e₂`, `Π = e₁`. Then `Q₂.Ψ = 1`, `Q₂.Π = 0`, `Q₁.Π = 1`, so both Assumption
2.3.1 and Assumption 2.3.2 fail; yet for every shock and every admissible `y₀` there is
exactly one stable solution (martingale differences are zero, so `Ψ` and `Π` play no role).
Necessity needs a rich filtration (`theorem_2_3_1`). -/
theorem theorem_2_3_1_necessity_false :
    ∃ (Γ₀ Γ₁ Q Z : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) (Ψ : Matrix (Fin (1 + 1)) (Fin 1) ℂ)
      (Pm : Matrix (Fin (1 + 1)) (Fin 1) ℂ),
      IsSimsQZ Γ₀ Γ₁ Q Z ∧ ¬ SimsAssumption1 Q Ψ Pm ∧ ¬ SimsAssumption2 Q Pm ∧
      ∀ ε : ℕ → Fin 1 → ℂ, IsSimsShock klS_detSystem ε → ∀ y₀ : Fin (1 + 1) → ℂ,
        Evec klS_detSystem 0 y₀ = y₀ → matAct (simsBot (star Z)) y₀ = 0 →
          ∃! y, (∃ η, IsSimsSolution klS_detSystem Γ₀ Γ₁ Ψ Pm ε y η) ∧ IsStableProc y ∧
            y 0 = y₀ := by
  have hqz : IsSimsQZ (1 : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) !![1 / 2, 0; 0, 2] 1 1 := by
    refine ⟨one_mem _, one_mem _, ?_, ?_, fun i => ?_, fun i => ?_⟩
    · rw [Matrix.mul_one, Matrix.mul_one]
      exact fun i j h => Matrix.one_apply_ne (ne_of_lt h).symm
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> norm_num
    · fin_cases i <;> norm_num
  refine ⟨1, !![1 / 2, 0; 0, 2], 1, 1, !![0; 1], !![1; 0], hqz, ?_, ?_, ?_⟩
  · rintro ⟨Λ, hΛ⟩
    have := congrFun (congrFun hΛ 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Fin.ext_iff] at this
  · rintro ⟨Ξ, hΞ⟩
    have := congrFun (congrFun hΞ 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Fin.ext_iff] at this
  · intro ε hε y₀ h1 h2
    refine (existsUnique_congr fun y => and_congr_left' (exists_congr fun η =>
      (simsH_det_sol_iff hε.2.1 y η).symm)).1 ?_
    exact theorem_2_3_1_sufficiency klS_detSystem hqz ⟨0, by simp⟩ ⟨0, by simp⟩ hε y₀ h1 h2

/-- `matAct (c • M) x = c • matAct M x`. -/
theorem simsH_smul_matAct {ι κ : Type*} [Fintype κ] (c : ℂ) (M : Matrix ι κ ℂ) (x : κ → V) :
    matAct (c • M) x = c • matAct M x := by
  funext i
  simp only [matAct, Matrix.smul_apply, smul_eq_mul, mul_smul, Pi.smul_apply, Finset.smul_sum]

theorem simsH_upper_one (M : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) : M.IsUpperTriangular := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  rw [Fin.lt_def] at h
  omega

/-- **Counterexample to the printed `Θ₁`** (Miao, p. 61). The book writes
`Θ₁ = Z G⁻¹ H`; the correct matrix is `Θ₁ = Z G⁻¹ H Zᴴ` (`theorem_2_3_1_theta`). With
`n = n_s = 1`, `Γ₀ = 1`, `Γ₁ = 1/2`, the QZ form `Q = Z = −1` (so `S = 1`, `T = 1/2`), `E_t = id`
and `ε = 0`, the stable solution from `y₀ = 1` has `y₁ = 1/2 = Θ₁y₀`, while the printed matrix
gives `Z G⁻¹ H y₀ = −1/2`. -/
theorem theta_1_printed_false :
    ∃ (Γ₀ Γ₁ Q Z : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) (Ξ : Matrix (Fin 1) (Fin 0) ℂ)
      (y : ℕ → Fin (1 + 0) → ℂ),
      IsSimsQZ Γ₀ Γ₁ Q Z ∧
      (∃ η, IsSimsSolution klS_detSystem Γ₀ Γ₁ (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ)
        (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ) 0 y η) ∧ IsStableProc y ∧
      y 1 = matAct (simsTheta1 Γ₀ Γ₁ Q Z Ξ) (y 0) ∧
      y 1 ≠ matAct (Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsHmat (Q * Γ₁ * Z) Ξ) (y 0) := by
  set Γ₁ : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ := (1 / 2 : ℂ) • 1
  have hu : (-1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) ∈ Matrix.unitaryGroup (Fin (1 + 0)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_neg, star_one, neg_mul_neg, Matrix.one_mul]
  have hS : (-1) * 1 * (-1) = (1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) := by
    rw [Matrix.mul_one, neg_mul_neg, Matrix.one_mul]
  have hT : (-1) * Γ₁ * (-1) = Γ₁ := by
    rw [neg_mul, Matrix.one_mul, neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  have hqz : IsSimsQZ 1 Γ₁ (-1) (-1) := by
    refine ⟨hu, hu, simsH_upper_one _, simsH_upper_one _, fun i => ?_, fun i => ?_⟩
    · rw [hS, hT]
      refine iff_of_true (by omega) ?_
      norm_num [Γ₁]
    · rw [hS, hT]
      norm_num [Γ₁]
  have hΞ : simsTop (-1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) *
      (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ) = (0 : Matrix (Fin 1) (Fin 0) ℂ) *
        (simsBot (-1 : Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) *
          (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ)) := by
    rw [Matrix.mul_zero, Matrix.mul_zero, Matrix.mul_zero]
  obtain ⟨y, hsol, hy, hy0⟩ := theorem_2_3_1_existence klS_detSystem hqz
    (Ψ := (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ)) (Pm := (0 : Matrix (Fin (1 + 0)) (Fin 1) ℂ))
    (Λ := 0) (by simp)
    (simsH_zero_shock _) (fun _ => 1) rfl (funext fun i => Fin.elim0 i)
  have h1 := theorem_2_3_1_theta klS_detSystem hqz hΞ (simsH_zero_shock _).2.1 hsol hy 0
  rw [Pi.zero_apply, klS_matAct_zero] at h1
  replace h1 := h1.trans (add_zero _)
  refine ⟨1, Γ₁, -1, -1, 0, y, hqz, ⟨_, hsol⟩, hy, h1, fun h => ?_⟩
  have he := hsol.2.2.2 0
  rw [matAct_one, klS_zero_matAct, klS_zero_matAct, hy0, simsH_smul_matAct, matAct_one] at he
  replace he := he.trans ((add_zero _).trans (add_zero _))
  have h10 : y 1 0 = 1 / 2 := by
    have := congrFun he 0
    simpa using this
  have hpr : (-1) * (simsGmat ((-1) * 1 * (-1)) 0)⁻¹ * simsHmat ((-1) * Γ₁ * (-1)) 0 =
      simsTheta1 1 Γ₁ (-1) (-1) (0 : Matrix (Fin 1) (Fin 0) ℂ) * (-1) := by
    simp only [simsTheta1, star_neg, star_one, Matrix.mul_assoc, neg_mul_neg,
      Matrix.mul_one]
  rw [hpr, ← matAct_mul, klS_neg_matAct, matAct_one, klS_matAct_neg, ← h1] at h
  have := congrFun h 0
  rw [Pi.neg_apply, h10] at this
  norm_num at this

/-- **Counterexample to (2.22) as printed** (Miao, p. 59). The book's forward solution
`u_t = −T₂₂⁻¹∑_{j≥1} (T₂₂⁻¹S₂₂)ʲ c_{t+j}` (with `c_t = Q₂.(Ψε_t + Πη_t)`) fails for the
scalar recursion `S₂₂u_{t+1} = T₂₂u_t + c_{t+1}` with `S₂₂ = 0`, `T₂₂ = 1` (an infinite
generalized eigenvalue), `c ≡ 1`, `u ≡ −1`: the printed sum vanishes. The correct formula is
`eq_2_22`. (In a stable solution of (2.20) both sides vanish after `E_t`, `eq_2_22_expect`.) -/
theorem eq_2_22_printed_false :
    ∃ (S22 T22 : Matrix (Fin 1) (Fin 1) ℂ) (u c : ℕ → Fin 1 → ℂ),
      T22.det ≠ 0 ∧ (∀ i, ‖S22 i i‖ < ‖T22 i i‖) ∧ IsStableProc u ∧ IsStableProc c ∧
      (∀ t, matAct S22 (u (t + 1)) = matAct T22 (u t) + c (t + 1)) ∧
      u 0 ≠ -matAct T22⁻¹ (∑' j, matAct ((T22⁻¹ * S22) ^ (j + 1)) (c (0 + 1 + j))) := by
  refine ⟨0, 1, fun _ _ => -1, fun _ _ => 1, by simp, fun i => by simp,
    isStableProc_of_uniformly_bounded (M := 1) fun t i => by simp,
    isStableProc_of_uniformly_bounded (M := 1) fun t i => by simp, fun t => ?_, ?_⟩
  · rw [klS_zero_matAct, matAct_one]
    funext i
    simp
  · simp only [Matrix.mul_zero, pow_succ, klS_zero_matAct, tsum_zero, klS_matAct_zero, neg_zero]
    intro h
    have := congrFun h 0
    simp at this

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Sims method: SVD, uniqueness of prediction errors, sunspots

Miao, §2.3.3, pp. 62–64, continuing `Sims`. The SVD (2.25) is taken as a hypothesis
(`IsThinSVD B U.1 D₁₁ V.1`: `B = U.1D₁₁V.1ᴴ`, orthonormal columns, `D₁₁` invertible; for the
sunspot part also `V.2` with `V.1ᴴV.2 = 0`, `V.2ᴴV.2 = I`, `V.1V.1ᴴ + V.2V.2ᴴ = I`); the
existence of an SVD is not formalised (it is not needed: Assumption 2.3.2 is characterised by
kernels in `simsAssumption2_iff_ker`).

* The column-space test: `colspace_iff`, `colspace_iff_thin`, `colspace_printed_false`.
* `Λ` and `Ξ` (p. 62): `lambda_formula` (any `r`), `xi_formula` (`m = r`), `xi_residual`
  (p. 63, `Q₁.Π − ΞQ₂.Π = Q₁.Π(I − V.1V.1ᴴ)`), `svd_injective_iff` (`m = r` iff `Q₂.Π`
  has full column rank).
* Uniqueness: `SimsYUnique`, `SimsPairUnique`; `simsY_unique_iff` (with a rich filtration,
  `y` is unique iff Assumption 2.3.2); `corollary_2_3_1` (the pair `(y, η)` is unique iff
  `m = r`); `corollary_2_3_1_printed_false`; `lubik_schorfheide`.
* Sunspots (pp. 63–64): `eq_2_26`, `eq_sunspot_identity`, `sunspot_term_simplified`,
  `simsTheta3`, `sunspot_solution` (every stable solution is
  `y_t = Θ₁y_{t−1} + Θ₂ε_t + Θ₃e_t`, `e_t = V.2ᴴη_t`), `sunspot_existence`.

**Corrections.**
* The column-space test "If `B`'s SVD is `TCW`, `A`'s column space includes `B`'s iff
  `(I − UUᴴ)T = 0`" is vacuous with the full unitary `U` (`colspace_printed_false`); the correct
  test uses the first `r` columns: `(I − U.1U.1ᴴ)B = 0`, equivalently `(I − U.1U.1ᴴ)T.1 = 0`.
* Corollary 2.3.1 ("given Assumption 2.3.1, uniqueness iff `m = r`") is true for the pair
  `(y, η)` (and needs no Assumption 2.3.1) but false for `y`, which is what Theorem 2.3.1 calls
  the solution: with a prediction error that enters nowhere (a zero column of `Π`), `m > r`
  and `y` is unique (`corollary_2_3_1_printed_false`). The correct condition for `y` is
  Assumption 2.3.2 (`simsY_unique_iff`); `m = r` implies it (`xi_formula`), and the two agree
  when `Π` has full column rank.
* Likewise "if `m > r` there are infinitely many stable solutions" (Lubik–Schorfheide) holds
  for `(y, η)` (`lubik_schorfheide`, with a rich filtration) but not for `y`.
* The sunspot formulas (2.26), the identity on p. 63 and `Θ₃` are correct as printed (with
  `V.1′ = V.1ᴴ`); the factor `I − V.1V.1ᴴ` in front of `V.2` is redundant
  (`sunspot_term_simplified`). The representation `sunspot_solution` needs neither
  Assumption 2.3.1 nor 2.3.2.
-/

namespace Miao.RationalExpectations

open scoped Matrix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### Thin singular value decompositions -/

variable {p m r : ℕ} (B : Matrix (Fin p) (Fin m) ℂ) (U1 : Matrix (Fin p) (Fin r) ℂ)
  (D : Matrix (Fin r) (Fin r) ℂ) (V1 : Matrix (Fin m) (Fin r) ℂ) in
/-- A thin singular value decomposition `B = U.1 D₁₁ V.1ᴴ` (Miao, (2.25), p. 62): `U.1` and `V.1`
have orthonormal columns and `D₁₁` is invertible; `r` is the rank. (That `D₁₁` is diagonal
with positive entries is not used anywhere.) Here `ᴴ` is `star`. -/
structure IsThinSVD : Prop where
  eq : B = U1 * D * V1ᴴ
  U1_orth : U1ᴴ * U1 = 1
  V1_orth : V1ᴴ * V1 = 1
  det_D : D.det ≠ 0

/-- `(I − U.1U.1ᴴ)U.1 = 0`. -/
theorem simsH_proj_mul {p r : ℕ} {U1 : Matrix (Fin p) (Fin r) ℂ} (h : U1ᴴ * U1 = 1) :
    (1 - U1 * U1ᴴ) * U1 = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_one, sub_self]

/-- `D₁₁⁻¹U.1ᴴB = V.1ᴴ`. -/
theorem simsH_svd_left {p m r : ℕ} {B : Matrix (Fin p) (Fin m) ℂ} {U1 : Matrix (Fin p) (Fin r) ℂ}
    {D : Matrix (Fin r) (Fin r) ℂ} {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) :
    D⁻¹ * U1ᴴ * B = V1ᴴ := by
  rw [h.eq, show D⁻¹ * U1ᴴ * (U1 * D * V1ᴴ) = D⁻¹ * (U1ᴴ * U1) * D * V1ᴴ by
    simp only [Matrix.mul_assoc], h.U1_orth, Matrix.mul_one,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h.det_D), Matrix.one_mul]

/-- The explicit `Λ` (Miao, p. 62): if `(I − U.1U.1ᴴ)C = 0` then `C = B(V.1D₁₁⁻¹U.1ᴴC)`. -/
theorem simsH_colspace_explicit {p m r k : ℕ} {B : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) {C : Matrix (Fin p) (Fin k) ℂ}
    (hC : (1 - U1 * U1ᴴ) * C = 0) : C = B * (V1 * D⁻¹ * U1ᴴ * C) := by
  have e : B * (V1 * D⁻¹ * U1ᴴ * C) = U1 * D * (V1ᴴ * V1) * D⁻¹ * U1ᴴ * C := by
    rw [h.eq]
    simp only [Matrix.mul_assoc]
  rw [e, h.V1_orth, Matrix.mul_one, Matrix.mul_assoc U1 D D⁻¹,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h.det_D), Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hC
  exact hC

/-- Miao, p. 62, the column-space test, corrected. The book states "If `B`'s SVD is `TCW`,
`A`'s column space includes `B`'s iff `(I − UUᴴ)T = 0`", which with the full unitary `U` of
`A`'s SVD is vacuous (`colspace_printed_false`). The correct test uses the first `r` columns
`U.1`: with `A = U.1D₁₁V.1ᴴ`, `col(C) ⊆ col(A)` iff `(I − U.1U.1ᴴ)C = 0`. -/
theorem colspace_iff {p m r k : ℕ} {A : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD A U1 D V1) (C : Matrix (Fin p) (Fin k) ℂ) :
    (∃ Λ, C = A * Λ) ↔ (1 - U1 * U1ᴴ) * C = 0 := by
  constructor
  · rintro ⟨Λ, rfl⟩
    rw [h.eq, show (1 - U1 * U1ᴴ) * (U1 * D * V1ᴴ * Λ) =
      (1 - U1 * U1ᴴ) * U1 * D * V1ᴴ * Λ by simp only [Matrix.mul_assoc],
      simsH_proj_mul h.U1_orth]
    simp only [Matrix.zero_mul]
  · intro hC
    exact ⟨_, simsH_colspace_explicit h hC⟩

/-- Miao, p. 62, the column-space test in terms of `C`'s own SVD `C = T.1C₁₁W.1ᴴ`: `col(C) ⊆
col(A)` iff `(I − U.1U.1ᴴ)T.1 = 0`, with the thin factors `U.1`, `T.1` (the reconstruction of
the garbled printed test). -/
theorem colspace_iff_thin {p m r k q : ℕ} {A : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD A U1 D V1) {C : Matrix (Fin p) (Fin k) ℂ}
    {T1 : Matrix (Fin p) (Fin q) ℂ} {C1 : Matrix (Fin q) (Fin q) ℂ}
    {W1 : Matrix (Fin k) (Fin q) ℂ} (hC : IsThinSVD C T1 C1 W1) :
    (∃ Λ, C = A * Λ) ↔ (1 - U1 * U1ᴴ) * T1 = 0 := by
  rw [colspace_iff h]
  constructor
  · intro h0
    have e : T1 = C * (W1 * C1⁻¹) := by
      rw [hC.eq, show T1 * C1 * W1ᴴ * (W1 * C1⁻¹) = T1 * (C1 * (W1ᴴ * W1) * C1⁻¹) by
        simp only [Matrix.mul_assoc], hC.V1_orth, Matrix.mul_one,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hC.det_D), Matrix.mul_one]
    rw [e, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  · intro h0
    rw [hC.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul]

/-- **Counterexample to the printed column-space test** (Miao, p. 62). With the full unitary `U`
of `A`'s SVD, `(I − UUᴴ)T = 0` always holds, yet for `A = 0`, `C = 1` (`1 × 1`,
`U = V = T = W = C₁₁ = 1`, `D = 0`) the column space of `A` does not include that of `C`. -/
theorem colspace_printed_false :
    ∃ (A C U D Vm T C1 W : Matrix (Fin 1) (Fin 1) ℂ),
      U ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧ Vm ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧
      T ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧ W ∈ Matrix.unitaryGroup (Fin 1) ℂ ∧
      A = U * D * star Vm ∧ C = T * C1 * star W ∧ (1 - U * star U) * T = 0 ∧
      ¬ ∃ Λ, C = A * Λ := by
  refine ⟨0, 1, 1, 0, 1, 1, 1, 1, one_mem _, one_mem _, one_mem _, one_mem _, by simp, by simp,
    by simp, ?_⟩
  rintro ⟨Λ, hΛ⟩
  have := congrFun (congrFun hΛ 0) 0
  simp at this

/-- Miao, p. 62: "`Λ = V.1D₁₁⁻¹U.1ᴴ(Q₂.Ψ)`". Under Assumption 2.3.1 this `Λ` works, whether or
not `m = r`. -/
theorem lambda_formula {ns nu nε m r : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD (simsBot Q * Pm) U1 D V1)
    (hA1 : SimsAssumption1 Q Ψ Pm) :
    simsBot Q * Ψ = simsBot Q * Pm * (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) := by
  obtain ⟨Λ, hΛ⟩ := hA1
  exact simsH_colspace_explicit h ((colspace_iff h _).1 ⟨Λ, hΛ⟩)

/-- Miao, p. 63: with `Ξ = Q₁.ΠV.1D₁₁⁻¹U.1ᴴ`, `Q₁.Π − ΞQ₂.Π = Q₁.Π(I − V.1V.1ᴴ)` (as printed;
"not equal to zero in general"). -/
theorem xi_residual {p q m r : ℕ} {B : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) (C : Matrix (Fin q) (Fin m) ℂ) :
    C - C * V1 * D⁻¹ * U1ᴴ * B = C * (1 - V1 * V1ᴴ) := by
  rw [show C * V1 * D⁻¹ * U1ᴴ * B = C * V1 * (D⁻¹ * U1ᴴ * B) by
    simp only [Matrix.mul_assoc], simsH_svd_left h, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_assoc]

/-- Miao, p. 62: "If `m = r` … `Ξ = (Q₁.Π)V.1D₁₁⁻¹U.1ᴴ`" satisfies Assumption 2.3.2. With
`m = r`, `V.1` is square with `V.1ᴴV.1 = I`, hence `V.1V.1ᴴ = I`. -/
theorem xi_formula {p q m : ℕ} {B : Matrix (Fin p) (Fin m) ℂ} {U1 : Matrix (Fin p) (Fin m) ℂ}
    {D : Matrix (Fin m) (Fin m) ℂ} {V1 : Matrix (Fin m) (Fin m) ℂ} (h : IsThinSVD B U1 D V1)
    (C : Matrix (Fin q) (Fin m) ℂ) : C = C * V1 * D⁻¹ * U1ᴴ * B := by
  have hV : V1 * V1ᴴ = 1 := mul_eq_one_comm.1 h.V1_orth
  have := xi_residual h C
  rw [hV, sub_self, Matrix.mul_zero, sub_eq_zero] at this
  exact this

/-- `m = r` means that `Q₂.Π` has full column rank: for a thin SVD `B = U.1D₁₁V.1ᴴ` of an
`n_u × m` matrix of rank `r`, `Bv = 0 → v = 0` iff `r = m`. -/
theorem svd_injective_iff {p m r : ℕ} {B : Matrix (Fin p) (Fin m) ℂ}
    {U1 : Matrix (Fin p) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (h : IsThinSVD B U1 D V1) :
    (∀ v, B *ᵥ v = 0 → v = 0) ↔ r = m := by
  have hker : ∀ v, B *ᵥ v = 0 ↔ V1ᴴ *ᵥ v = 0 := fun v => by
    constructor
    · intro hv
      rw [← simsH_svd_left h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    · intro hv
      rw [h.eq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hrm : r ≤ m := by
    have hinj : Function.Injective (Matrix.mulVecLin V1) := by
      intro a b hab
      have := congrArg (V1ᴴ *ᵥ ·) hab
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h.V1_orth,
        Matrix.one_mulVec] using this
    simpa only [Module.finrank_fin_fun] using LinearMap.finrank_le_finrank_of_injective hinj
  constructor
  · intro hinj
    by_contra hne
    have hlt : Module.finrank ℂ (Fin r → ℂ) < Module.finrank ℂ (Fin m → ℂ) := by
      simp only [Module.finrank_fin_fun]
      omega
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1
      (LinearMap.ker_ne_bot_of_finrank_lt (f := Matrix.mulVecLin (V1ᴴ)) hlt)
    exact hv0 (hinj v ((hker v).2 hv))
  · rintro rfl v hv
    have hV : V1 * V1ᴴ = 1 := mul_eq_one_comm.1 h.V1_orth
    rw [← Matrix.one_mulVec v, ← hV, ← Matrix.mulVec_mulVec, (hker v).1 hv, Matrix.mulVec_zero]

/-! ### Uniqueness of `y` and of `(y, η)` -/

/-- Uniqueness of the stable solution `y` of (2.20): for every exogenous shock, two stable
solutions with the same initial value coincide (their prediction errors may differ). -/
def SimsYUnique {n nε m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (Ψ : Matrix (Fin n) (Fin nε) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  ∀ ε : ℕ → Fin nε → V, IsSimsShock E ε → ∀ (y y' : ℕ → Fin n → V) (η η' : ℕ → Fin m → V),
    IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η → IsStableProc y → IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y' η' →
      IsStableProc y' → y 0 = y' 0 → y = y'

/-- Uniqueness of the pair `(y, η)` (with `η_t` for `t ≥ 1`; `η₀` does not enter (2.20)). -/
def SimsPairUnique {n nε m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (Ψ : Matrix (Fin n) (Fin nε) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) : Prop :=
  ∀ ε : ℕ → Fin nε → V, IsSimsShock E ε → ∀ (y y' : ℕ → Fin n → V) (η η' : ℕ → Fin m → V),
    IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η → IsStableProc y → IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y' η' →
      IsStableProc y' → y 0 = y' 0 → y = y' ∧ ∀ t, η (t + 1) = η' (t + 1)

/-- Solutions of (2.20) add: a solution for `ε` plus a solution of the homogeneous system
(`ε = 0`) is a solution for `ε`. -/
theorem simsH_sol_add {n nε m : ℕ} {E : CondExpSystem ℂ V} {Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ}
    {Ψ : Matrix (Fin n) (Fin nε) ℂ} {Pm : Matrix (Fin n) (Fin m) ℂ} {ε : ℕ → Fin nε → V}
    {y d : ℕ → Fin n → V} {η h : ℕ → Fin m → V} (h1 : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η)
    (h2 : IsSimsSolution E Γ₀ Γ₁ Ψ Pm 0 d h) : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε (y + d) (η + h) := by
  obtain ⟨a1, b1, c1, e1⟩ := h1
  obtain ⟨a2, b2, c2, e2⟩ := h2
  refine ⟨fun t i => ?_, fun t i => ?_, fun t i => ?_, fun t => ?_⟩
  · simp only [Pi.add_apply, map_add, a1 t i, a2 t i]
  · simp only [Pi.add_apply, map_add, b1 t i, b2 t i]
  · simp only [Pi.add_apply, map_add, c1 t i, c2 t i, add_zero]
  · have := e2 t
    rw [Pi.zero_apply, klS_matAct_zero, add_zero] at this
    simp only [Pi.add_apply, matAct_add, e1 t, this]
    abel

/-- A prediction error `η_t = vζ_t` in the kernel of `Q₂.Π` (`ζ` a stable adapted scalar
martingale difference) drives a stable solution of the homogeneous system with `y₀ = 0`. -/
theorem simsH_perturb [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {ζ : ℕ → V} (hζa : ∀ t, E.E t (ζ t) = ζ t) (hζm : ∀ t, E.E t (ζ (t + 1)) = 0) {M : ℝ}
    (hζb : ∀ t, ‖ζ t‖ ≤ M) {v : Fin m → ℂ} (hv : (simsBot Q * Pm) *ᵥ v = 0) :
    ∃ d, IsSimsSolution E Γ₀ Γ₁ Ψ Pm (0 : ℕ → Fin nε → V) d (fun t k => v k • ζ t) ∧
      IsStableProc d ∧ d 0 = 0 := by
  obtain ⟨hηa, hηm, hηs⟩ := simsH_rich_shock E hζa hζm hζb v
  exact simsH_core_exists E hqz (simsH_zero_shock E).1 (simsH_zero_shock E).2.2 hηa hηm hηs
    (fun t => by
      rw [Pi.zero_apply, klS_matAct_zero, zero_add, simsH_matAct_smul, simsH_matAct_smul,
        Matrix.mulVec_mulVec, hv]
      funext i
      simp) 0 (klS_Evec_zero E 0) (klS_matAct_zero _)

/-- Miao, pp. 61–62, uniqueness of `y` characterised: with a rich filtration, the stable
solution `y` is unique (given `y₀`, for every shock) iff Assumption 2.3.2 holds, i.e. iff
`ker(Q₂.Π) ⊆ ker(Q₁.Π)` (`simsAssumption2_iff_ker`). -/
theorem simsY_unique_iff [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} :
    SimsYUnique E Γ₀ Γ₁ Ψ Pm ↔ SimsAssumption2 Q Pm := by
  constructor
  · intro H
    exact theorem_2_3_1_necessity_2 E hrich hqz fun y η hsol hy hy0 => H 0 (simsH_zero_shock E)
      y 0 η 0 hsol hy (simsH_zero_solution E Γ₀ Γ₁ Ψ Pm) simsH_stable_zero hy0
  · intro hA2 ε hε y y' η η' h1 h2 h3 h4 h0
    exact theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 h1 h2 h3 h4 h0

/-- **Corollary 2.3.1** (Miao, p. 62), correct form. Let `Q₂.Π = U.1D₁₁V.1ᴴ` be a thin SVD of
rank `r` and let the filtration be rich. Then the stable solution together with its prediction
error, `(y, η)`, is unique (for every shock, given `y₀`) iff `m = r`. ("Given Assumption 2.3.1"
is not needed.) If `m = r`, Assumption 2.3.2 holds automatically (`xi_formula`). For the
uniqueness of `y` alone, `m = r` is not necessary (`corollary_2_3_1_printed_false`); the
condition is Assumption 2.3.2 (`simsY_unique_iff`). -/
theorem corollary_2_3_1 [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m r : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} {U1 : Matrix (Fin nu) (Fin r) ℂ}
    {D : Matrix (Fin r) (Fin r) ℂ} {V1 : Matrix (Fin m) (Fin r) ℂ}
    (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1) :
    SimsPairUnique E Γ₀ Γ₁ Ψ Pm ↔ r = m := by
  constructor
  · intro H
    by_contra hne
    have hni := mt (svd_injective_iff hsvd).1 hne
    push Not at hni
    obtain ⟨v, hv, hv0⟩ := hni
    obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
    obtain ⟨d, hd, hds, hd0⟩ := simsH_perturb E hqz (Ψ := Ψ) hζa hζm hζb hv
    obtain ⟨-, hη⟩ := H 0 (simsH_zero_shock E) 0 d 0 _ (simsH_zero_solution E Γ₀ Γ₁ Ψ Pm)
      simsH_stable_zero hd hds hd0.symm
    refine hv0 (funext fun k => ?_)
    have := congrFun (hη 0) k
    simp only [Pi.zero_apply] at this
    exact (smul_eq_zero.1 this.symm).resolve_right hζ1
  · rintro rfl ε hε y y' η η' h1 h2 h3 h4 h0
    have hinj := (svd_injective_iff hsvd).2 rfl
    have hA2 : SimsAssumption2 Q Pm := (simsAssumption2_iff_ker Q Pm).2 fun v hv => by
      rw [hinj v hv, Matrix.mulVec_zero]
    refine ⟨theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 h1 h2 h3 h4 h0, fun t => ?_⟩
    have e1 := eq_2_23 E hqz hε.2.1 h1 h2 t
    have e2 := eq_2_23 E hqz hε.2.1 h3 h4 t
    rw [matAct_add, matAct_mul, matAct_mul] at e1 e2
    have e3 : matAct (simsBot Q * Pm) (η (t + 1)) = matAct (simsBot Q * Pm) (η' (t + 1)) := by
      rw [← add_right_inj (matAct (simsBot Q * Ψ) (ε (t + 1))), e1, e2]
    have hL : V1 * (D⁻¹ * U1ᴴ * (simsBot Q * Pm)) = 1 := by
      rw [simsH_svd_left hsvd]
      exact mul_eq_one_comm.1 hsvd.V1_orth
    have := congrArg (matAct (V1 * (D⁻¹ * U1ᴴ))) e3
    rwa [matAct_mul, matAct_mul, Matrix.mul_assoc V1, hL, matAct_one, matAct_one] at this

/-- **Counterexample to Corollary 2.3.1 for the uniqueness of `y`, and to "if `m > r` there are
infinitely many stable solutions" (Lubik–Schorfheide, Miao, p. 62) for `y`.** Take `n = n_u = 1`,
`Γ₀ = 1`, `Γ₁ = 2`, `Q = Z = 1`, `Ψ = 0` and `Π = [1 0]`, whose second prediction error enters
nowhere (a zero column). Then `Q₂.Π = [1 0]` has the thin SVD `U.1 = D₁₁ = 1`,
`V.1 = (1, 0)ᵀ`, so `r = 1 < m = 2`; Assumptions 2.3.1–2.3.2 hold, and in every `CondExpSystem`
the stable solution `y` (here `y = 0`) is unique. Only the prediction error is indeterminate
(`lubik_schorfheide`). -/
theorem corollary_2_3_1_printed_false [CompleteSpace V] (E : CondExpSystem ℂ V) :
    ∃ (Γ₀ Γ₁ Q Z : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) (Ψ : Matrix (Fin (0 + 1)) (Fin 1) ℂ)
      (Pm : Matrix (Fin (0 + 1)) (Fin 2) ℂ) (U1 D : Matrix (Fin 1) (Fin 1) ℂ)
      (V1 : Matrix (Fin 2) (Fin 1) ℂ),
      IsSimsQZ Γ₀ Γ₁ Q Z ∧ SimsAssumption1 Q Ψ Pm ∧ SimsAssumption2 Q Pm ∧
      IsThinSVD (simsBot Q * Pm) U1 D V1 ∧ SimsYUnique E Γ₀ Γ₁ Ψ Pm := by
  have hS : (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) * 1 * 1 = 1 := by simp
  have hT : (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) * ((2 : ℂ) • 1) * 1 = (2 : ℂ) • 1 := by
    simp
  have hup : ∀ M : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ, M.IsUpperTriangular := fun M i j h => by
    have hi := i.isLt
    have hj := j.isLt
    rw [Fin.lt_def] at h
    omega
  have hqz : IsSimsQZ (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) ((2 : ℂ) • 1) 1 1 := by
    refine ⟨one_mem _, one_mem _, hup _, hup _, fun i => ?_, fun i => ?_⟩
    · rw [hS, hT]
      refine iff_of_false (by omega) ?_
      norm_num
    · rw [hS, hT]
      norm_num
  have hA2 : SimsAssumption2 (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℂ) !![1, 0] :=
    ⟨0, by ext i; exact Fin.elim0 i⟩
  refine ⟨1, (2 : ℂ) • 1, 1, 1, 0, !![1, 0], 1, 1, !![1; 0], hqz, ⟨0, by simp⟩, hA2,
    ⟨?_, by simp, ?_, by simp⟩, ?_⟩
  · ext i j
    fin_cases i
    fin_cases j <;> simp [Matrix.mul_apply, Matrix.one_apply, Fin.ext_iff]
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro ε hε y y' η η' h1 h2 h3 h4 h0
    exact theorem_2_3_1_uniqueness E hqz hA2 hε.2.1 h1 h2 h3 h4 h0

/-- **Lubik–Schorfheide** (Miao, p. 62), correct form: if `m > r` (equivalently `Q₂.Π` has a
nonzero kernel vector) and the filtration is rich, then every stable solution `(y, η)` lies in a
one-parameter family of distinct stable solutions with the same initial value: infinitely many
stable solutions, in the sense of pairs `(y, η)`. (For `y` alone this is false,
`corollary_2_3_1_printed_false`.) -/
theorem lubik_schorfheide [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E)
    {ns nu nε m r : ℕ} {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    (hqz : IsSimsQZ Γ₀ Γ₁ Q Z) {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} {U1 : Matrix (Fin nu) (Fin r) ℂ}
    {D : Matrix (Fin r) (Fin r) ℂ} {V1 : Matrix (Fin m) (Fin r) ℂ}
    (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1) (hr : r < m) {ε : ℕ → Fin nε → V}
    {y : ℕ → Fin (ns + nu) → V} {η : ℕ → Fin m → V}
    (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y) :
    ∃ f : ℂ → (ℕ → Fin (ns + nu) → V) × (ℕ → Fin m → V), Function.Injective f ∧
      ∀ c, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε (f c).1 (f c).2 ∧ IsStableProc (f c).1 ∧
        (f c).1 0 = y 0 := by
  have hni := mt (svd_injective_iff hsvd).1 (Nat.ne_of_lt hr)
  push Not at hni
  obtain ⟨v, hv, hv0⟩ := hni
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  obtain ⟨ζ, hζa, hζm, ⟨M, hζb⟩, hζ1⟩ := hrich
  choose d hd hds hd0 using fun c : ℂ => simsH_perturb E hqz (Ψ := Ψ) (v := c • v) hζa hζm hζb
    (by rw [Matrix.mulVec_smul, hv, smul_zero])
  refine ⟨fun c => (y + d c, η + fun t k => (c • v) k • ζ t), fun c c' hcc => ?_,
    fun c => ⟨simsH_sol_add hsol (hd c), klS_stable_add hy (hds c), ?_⟩⟩
  · have := congrFun (congrFun (congrArg Prod.snd hcc) 1) k
    simp only [Pi.add_apply, add_right_inj, Pi.smul_apply, smul_eq_mul] at this
    have h2 := (smul_left_injective ℂ hζ1) this
    exact mul_right_cancel₀ hk h2
  · change y 0 + d c 0 = y 0
    rw [hd0, add_zero]

/-! ### Sunspots: (2.26) and `Θ₃` -/

/-- Miao, (2.26), p. 63: under Assumption 2.3.1, with the full SVD `V = [V.1 V.2]`
(`V.1ᴴV.2 = 0`, `V.1V.1ᴴ + V.2V.2ᴴ = I`), the solutions `η` of (2.23) for a given `ε` are
exactly `η = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε + V.2e` with `e` arbitrary ("`V.2e_t` is a solution to the
homogeneous equation"). -/
theorem eq_2_26 {ns nu nε m r k : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hV12 : V1ᴴ * V2 = 0) (hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1)
    (hA1 : SimsAssumption1 Q Ψ Pm) (e : Fin nε → V) (h : Fin m → V) :
    matAct (simsBot Q) (matAct Ψ e + matAct Pm h) = 0 ↔
      ∃ s : Fin k → V, h = -matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) e + matAct V2 s := by
  have hΛ := lambda_formula hsvd hA1
  have hBV2 : simsBot Q * Pm * V2 = 0 := by
    rw [hsvd.eq, Matrix.mul_assoc, hV12, Matrix.mul_zero]
  rw [matAct_add, matAct_mul, matAct_mul]
  constructor
  · intro H
    have hBh : matAct (simsBot Q * Pm) h = -matAct (simsBot Q * Ψ) e := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
      exact H
    refine ⟨matAct V2ᴴ h, ?_⟩
    calc h = matAct (V1 * V1ᴴ + V2 * V2ᴴ) h := by rw [hcompl, matAct_one]
      _ = matAct V1 (matAct (D⁻¹ * U1ᴴ) (matAct (simsBot Q * Pm) h)) +
          matAct V2 (matAct V2ᴴ h) := by
        rw [matAct_mul (D⁻¹ * U1ᴴ), simsH_svd_left hsvd, klS_add_matAct, matAct_mul, matAct_mul]
      _ = _ := by
        rw [hBh, klS_matAct_neg, klS_matAct_neg, matAct_mul, matAct_mul, matAct_mul,
          Matrix.mul_assoc V1 D⁻¹, Matrix.mul_assoc V1]
  · rintro ⟨s, rfl⟩
    rw [matAct_add, klS_matAct_neg, matAct_mul, matAct_mul, ← hΛ, hBV2, klS_zero_matAct,
      add_zero, add_neg_cancel]

/-- The stable-block prediction-error term of the sunspot solution (Miao, p. 63): with
`Ξ = Q₁.ΠV.1D₁₁⁻¹U.1ᴴ` and `η = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε + V.2e`,
`(Q₁. − ΞQ₂.)Πη = Q₁.Π(I − V.1V.1ᴴ)V.2e`, as printed. -/
theorem eq_sunspot_identity {ns nu nε m r k : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    (V2 : Matrix (Fin m) (Fin k) ℂ) (e : Fin nε → V) (s : Fin k → V) :
    matAct ((simsTop Q - simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ * simsBot Q) * Pm)
        (-matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) e + matAct V2 s) =
      matAct (simsTop Q * Pm * (1 - V1 * V1ᴴ) * V2) s := by
  have hR : (simsTop Q - simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ * simsBot Q) * Pm =
      simsTop Q * Pm * (1 - V1 * V1ᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ), xi_residual hsvd]
  have hRV1 : simsTop Q * Pm * (1 - V1 * V1ᴴ) * V1 = 0 := by
    rw [Matrix.mul_assoc (simsTop Q * Pm), Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc V1,
      hsvd.V1_orth, Matrix.mul_one, sub_self, Matrix.mul_zero]
  rw [hR, matAct_add, klS_matAct_neg, show V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ) =
    V1 * (D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) by simp only [Matrix.mul_assoc], ← matAct_mul V1,
    matAct_mul _ V1, hRV1, klS_zero_matAct, neg_zero, zero_add, matAct_mul]

/-- The term of `eq_sunspot_identity` simplifies: `(I − V.1V.1ᴴ)V.2 = V.2` when `V.1ᴴV.2 = 0`, so
`Q₁.Π(I − V.1V.1ᴴ)V.2 = Q₁.ΠV.2` (the book keeps the redundant factor). -/
theorem sunspot_term_simplified {m r k q : ℕ} {V1 : Matrix (Fin m) (Fin r) ℂ}
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hV12 : V1ᴴ * V2 = 0) (C : Matrix (Fin q) (Fin m) ℂ) :
    C * (1 - V1 * V1ᴴ) * V2 = C * V2 := by
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV12, Matrix.mul_zero,
    sub_zero]

/-- `Θ₃ = ZG⁻¹[[Q₁.Π(I − V.1V.1ᴴ)], [0]]V.2` (Miao, p. 64, where `V.1′` means `V.1ᴴ`). -/
noncomputable def simsTheta3 {ns nu m r k : ℕ} (Γ₀ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ)
    (Ξ : Matrix (Fin ns) (Fin nu) ℂ) (Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ)
    (V1 : Matrix (Fin m) (Fin r) ℂ) (V2 : Matrix (Fin m) (Fin k) ℂ) :
    Matrix (Fin (ns + nu)) (Fin k) ℂ :=
  Z * (simsGmat (Q * Γ₀ * Z) Ξ)⁻¹ * simsRows (simsTop Q * Pm * (1 - V1 * V1ᴴ)) 0 * V2

theorem simsH_rows_zero {a b : ℕ} {κ : Type*} :
    simsRows (0 : Matrix (Fin a) κ ℂ) (0 : Matrix (Fin b) κ ℂ) = 0 := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [simsRows]

/-- **The sunspot solution** (Miao, pp. 63–64), first half: with `Ξ = Q₁.ΠV.1D₁₁⁻¹U.1ᴴ` and the
full SVD (`V.1V.1ᴴ + V.2V.2ᴴ = I`), every stable solution of (2.20) satisfies
`y_t = Θ₁y_{t−1} + Θ₂ε_t + Θ₃e_t` with `e_t = V.2ᴴη_t`. Neither Assumption 2.3.1 nor 2.3.2 is
needed for this representation. -/
theorem sunspot_solution [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m r k : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1)
    {ε : ℕ → Fin nε → V} (hεm : IsMartingaleDiffProc E ε) {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y)
    (t : ℕ) :
    y (t + 1) = matAct (simsTheta1 Γ₀ Γ₁ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ)) (y t) +
      matAct (simsTheta2 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Ψ) (ε (t + 1)) +
      matAct (simsTheta3 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Pm V1 V2)
        (matAct V2ᴴ (η (t + 1))) := by
  set Ξ := simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ with hΞ
  set R := simsTop Q * Pm * (1 - V1 * V1ᴴ) with hRdef
  have hZZ : Z * star Z = 1 := Matrix.mem_unitaryGroup_iff.1 hqz.unitary_Z
  have hback : ∀ v : Fin (ns + nu) → V, matAct Z (matAct (star Z) v) = v := fun v => by
    rw [matAct_mul, hZZ, matAct_one]
  have hR : (simsTop Q - Ξ * simsBot Q) * Pm = R := by
    rw [Matrix.sub_mul, Matrix.mul_assoc Ξ, hΞ, xi_residual hsvd]
  have hRV1 : R * V1 = 0 := by
    rw [hRdef, Matrix.mul_assoc (simsTop Q * Pm), Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc V1, hsvd.V1_orth, Matrix.mul_one, sub_self, Matrix.mul_zero]
  have hKP : simsKmat Q Ξ * Pm = simsRows R 0 := by
    rw [simsKmat, simsRows_mul, hR, Matrix.zero_mul]
  have hη : matAct (simsKmat Q Ξ) (matAct Pm (η (t + 1))) =
      matAct (simsRows R 0 * V2) (matAct V2ᴴ (η (t + 1))) := by
    have e1 : simsRows R (0 : Matrix (Fin nu) (Fin m) ℂ) =
        simsRows R (0 : Matrix (Fin nu) (Fin m) ℂ) * V2 * V2ᴴ := by
      calc simsRows R (0 : Matrix (Fin nu) (Fin m) ℂ) =
          simsRows R 0 * (V1 * V1ᴴ + V2 * V2ᴴ) := by rw [hcompl, Matrix.mul_one]
        _ = simsRows R 0 * V2 * V2ᴴ := by
          rw [Matrix.mul_add, ← Matrix.mul_assoc, simsRows_mul R, hRV1, Matrix.zero_mul,
            simsH_rows_zero, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
    rw [matAct_mul, hKP, matAct_mul, ← e1]
  have h := eq_2_24 E hqz hεm hsol hy Ξ t
  rw [matAct_add, hη] at h
  have h' := (simsH_solve_G (simsGmat_det hqz.upper_S hqz.ord Ξ) hqz.unitary_Z _ _ _).1 h
  rw [hback, hback] at h'
  rw [h', add_assoc]
  congr 1
  simp only [simsTheta2, simsTheta3, matAct_add, matAct_mul, Matrix.mul_assoc, hRdef]

/-- **The sunspot solution** (Miao, pp. 63–64), second half: under Assumption 2.3.1, for every
exogenous shock `ε`, every sunspot shock `e` (adapted, stable, `E_{t−1}e_t = 0`) and every
admissible `y₀`, the prediction error (2.26) `η_t = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε_t + V.2e_t` gives a stable
solution of (2.20) with `y_0 = y₀`; if `V.2` has orthonormal columns it is
`y_t = Θ₁y_{t−1} + Θ₂ε_t + Θ₃e_t` (`Θ₃` as printed). "Sunspot shocks can influence the
equilibrium allocations". -/
theorem sunspot_existence [CompleteSpace V] (E : CondExpSystem ℂ V) {ns nu nε m r k : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    {U1 : Matrix (Fin nu) (Fin r) ℂ} {D : Matrix (Fin r) (Fin r) ℂ}
    {V1 : Matrix (Fin m) (Fin r) ℂ} (hsvd : IsThinSVD (simsBot Q * Pm) U1 D V1)
    {V2 : Matrix (Fin m) (Fin k) ℂ} (hV12 : V1ᴴ * V2 = 0) (hV2 : V2ᴴ * V2 = 1)
    (hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1) (hA1 : SimsAssumption1 Q Ψ Pm)
    {ε : ℕ → Fin nε → V} (hε : IsSimsShock E ε) {e : ℕ → Fin k → V} (he : IsSimsShock E e)
    (y₀ : Fin (ns + nu) → V) (hy₀a : Evec E 0 y₀ = y₀)
    (hy₀ : matAct (simsBot (star Z)) y₀ = 0) :
    ∃ y, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y
        (fun t => -matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) (ε t) + matAct V2 (e t)) ∧
      IsStableProc y ∧ y 0 = y₀ ∧ ∀ t, y (t + 1) =
        matAct (simsTheta1 Γ₀ Γ₁ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ)) (y t) +
        matAct (simsTheta2 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Ψ) (ε (t + 1)) +
        matAct (simsTheta3 Γ₀ Q Z (simsTop Q * Pm * V1 * D⁻¹ * U1ᴴ) Pm V1 V2) (e (t + 1)) := by
  obtain ⟨hεa, hεm, hεs⟩ := hε
  obtain ⟨hea, hem, hes⟩ := he
  set Λ₀ := V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)
  have hηs : IsStableProc fun t => -matAct Λ₀ (ε t) + matAct V2 (e t) :=
    klS_stable_add (by simpa only [klS_neg_matAct] using klS_stable_matAct hεs (-Λ₀))
      (klS_stable_matAct hes V2)
  have hηa : IsAdaptedV E fun t => -matAct Λ₀ (ε t) + matAct V2 (e t) := fun t i => by
    change Evec E t (-matAct Λ₀ (ε t) + matAct V2 (e t)) i = _
    rw [klS_Evec_add, klS_Evec_neg, Evec_matAct, Evec_matAct,
      show Evec E t (ε t) = ε t from funext (hεa t), show Evec E t (e t) = e t from funext (hea t)]
  have hηm : IsMartingaleDiffProc E fun t => -matAct Λ₀ (ε t) + matAct V2 (e t) := fun t i => by
    change Evec E t (-matAct Λ₀ (ε (t + 1)) + matAct V2 (e (t + 1))) i = (0 : Fin m → V) i
    rw [klS_Evec_add, klS_Evec_neg, Evec_matAct, Evec_matAct,
      show Evec E t (ε (t + 1)) = 0 from funext (hεm t),
      show Evec E t (e (t + 1)) = 0 from funext (hem t), klS_matAct_zero, klS_matAct_zero,
      neg_zero, add_zero]
  obtain ⟨y, hsol, hy, hy0⟩ := simsH_core_exists E hqz hεa hεs hηa hηm hηs
    (fun t => (eq_2_26 hsvd hV12 hcompl hA1 _ _).2 ⟨e (t + 1), rfl⟩) y₀ hy₀a hy₀
  refine ⟨y, hsol, hy, hy0, fun t => ?_⟩
  have hV21 : V2ᴴ * V1 = 0 := by
    have := congrArg Matrix.conjTranspose hV12
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using this
  have hev : matAct V2ᴴ (-matAct Λ₀ (ε (t + 1)) + matAct V2 (e (t + 1))) = e (t + 1) := by
    rw [matAct_add, klS_matAct_neg, matAct_mul, matAct_mul, hV2, matAct_one,
      show V2ᴴ * Λ₀ = V2ᴴ * V1 * (D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) by simp only [Λ₀,
        Matrix.mul_assoc], hV21, Matrix.zero_mul, klS_zero_matAct, neg_zero, zero_add]
  rw [sunspot_solution E hqz hsvd hcompl hεm hsol hy t, hev]

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Sims form (2.19) and Example 2.3.2

Miao, §2.3.3, pp. 58 and 64, continuing `Sims`.

* `IsSims19Solution`: the general form (2.19) `Γ₀y_t = Γ₁y_{t−1} + C + Ψz_t + Πη_t`;
  `isSims19_zero_iff` (`C = 0`, `z = ε` is (2.20)).
* The reductions of p. 58, as equivalences of solution sets: `eq_2_19_const` (`C = 0` by
  `y ↦ y − (Γ₀ − Γ₁)⁻¹C`, when `Γ₀ − Γ₁` is invertible; stability is preserved) and
  `eq_2_19_append` (appending `z_t = Φz_{t−1} + Σε_t` to `y_t`, so that `ε` replaces `z`).
* Example 2.3.2: the New Keynesian model (2.13)–(2.15) (`IsNKSolution`), the printed matrices
  (`ex232Γ₀`, `ex232Γ₁`, `ex232Ψ`, `ex232Pm`), `example_2_3_2_rows` and the equivalence of
  solution sets `example_2_3_2`.

**Corrections.**
* The change of variables "as in Example 2.1.1" needs `Γ₀ − Γ₁` invertible (the analogue of
  `1 − b ≠ 0`); otherwise the reduction to `C = 0` can fail (`eq_2_19_const_singular`).
* The matrices of Example 2.3.2 are correct as printed (every entry checked), with
  `y_t = (i_t, ξ^x_t, ξ^π_t, x_t, π_t)`, `ε_t = (ε_t, ε^x_t)`, `η_t = (η^x_t, η^π_t)`; the
  equivalence holds for `t ≥ 1` (the equations at `t` involve `y_{t−1}`).
-/

namespace Miao.RationalExpectations

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The general form (2.19) and its reduction to (2.20) -/

/-- Miao, (2.19), p. 58: `Γ₀y_t = Γ₁y_{t−1} + C + Ψz_t + Πη_t` (`t ≥ 1`) with `y`, `η`
adapted and `η` a martingale difference. The constant `C` is a vector of deterministic random
variables (`E₀C = C`). -/
def IsSims19Solution {n nz m : ℕ} (E : CondExpSystem ℂ V) (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ)
    (C : Fin n → V) (Ψ : Matrix (Fin n) (Fin nz) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ)
    (z : ℕ → Fin nz → V) (y : ℕ → Fin n → V) (η : ℕ → Fin m → V) : Prop :=
  IsAdaptedV E y ∧ IsAdaptedV E η ∧ IsMartingaleDiffProc E η ∧
    ∀ t, matAct Γ₀ (y (t + 1)) = matAct Γ₁ (y t) + C + matAct Ψ (z (t + 1)) +
      matAct Pm (η (t + 1))

/-- (2.19) with `C = 0` and `z = ε` is (2.20). -/
theorem isSims19_zero_iff {n nz m : ℕ} (E : CondExpSystem ℂ V)
    (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin nz) ℂ)
    (Pm : Matrix (Fin n) (Fin m) ℂ) (z : ℕ → Fin nz → V) (y : ℕ → Fin n → V)
    (η : ℕ → Fin m → V) :
    IsSims19Solution E Γ₀ Γ₁ 0 Ψ Pm z y η ↔ IsSimsSolution E Γ₀ Γ₁ Ψ Pm z y η := by
  simp only [IsSims19Solution, IsSimsSolution, add_zero]

/-- Miao, p. 58 ("we may assume `C = 0` by appropriate change of variables as in Example
2.1.1"). If `Γ₀ − Γ₁` is invertible (`1` is not a generalized eigenvalue, the analogue of
`1 − b ≠ 0` in Example 2.1.1), put `ȳ = (Γ₀ − Γ₁)⁻¹C`. Then `(y, η)` solves (2.19) iff
`(y − ȳ, η)` solves (2.19) with `C = 0`, i.e. (2.20) with `z` in place of `ε`, and `y` is
stable iff `y − ȳ` is. Without the invertibility the reduction can fail
(`eq_2_19_const_singular`). -/
theorem eq_2_19_const {n nz m : ℕ} (E : CondExpSystem ℂ V) {Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ}
    (hdet : (Γ₀ - Γ₁).det ≠ 0) {C : Fin n → V} (hC : Evec E 0 C = C)
    (Ψ : Matrix (Fin n) (Fin nz) ℂ) (Pm : Matrix (Fin n) (Fin m) ℂ) (z : ℕ → Fin nz → V)
    (y : ℕ → Fin n → V) (η : ℕ → Fin m → V) :
    (IsSims19Solution E Γ₀ Γ₁ C Ψ Pm z y η ↔
      IsSimsSolution E Γ₀ Γ₁ Ψ Pm z (fun t => y t - matAct (Γ₀ - Γ₁)⁻¹ C) η) ∧
    (IsStableProc y ↔ IsStableProc fun t => y t - matAct (Γ₀ - Γ₁)⁻¹ C) := by
  set yb := matAct (Γ₀ - Γ₁)⁻¹ C with hyb
  have hyba : ∀ t, Evec E t yb = yb := fun t => by
    rw [hyb, Evec_matAct, ← hC, klS_Evec_tower_ge E (Nat.zero_le t)]
  have hCyb : matAct Γ₀ yb - matAct Γ₁ yb = C := by
    rw [← klS_sub_matAct, hyb, klS_matAct_mul_inv hdet]
  have hcst : IsStableProc fun _ : ℕ => yb := isStableProc_of_uniformly_bounded
    (M := ‖yb‖) fun _ i => norm_le_pi_norm yb i
  refine ⟨?_, ⟨fun h => klS_stable_sub h hcst, fun h => ?_⟩⟩
  · have hadapt : IsAdaptedV E y ↔ IsAdaptedV E fun t => y t - yb := by
      refine forall_congr' fun t => forall_congr' fun i => ?_
      have := congrFun (hyba t) i
      simp only [Evec] at this
      simp only [Pi.sub_apply, map_sub, this, sub_left_inj]
    refine and_congr hadapt (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun t => ?_)))
    rw [klS_matAct_sub, klS_matAct_sub, ← hCyb]
    constructor
    · intro h
      rw [h]
      abel
    · intro h
      linear_combination (norm := module) h
  · simpa only [sub_add_cancel] using klS_stable_add h hcst

/-- **The reduction `C = 0` needs `Γ₀ − Γ₁` invertible** (Miao, p. 58). With `Γ₀ = Γ₁ = 1`,
`C = 1`, `Ψ = Π = 0` and `E_t = id`, (2.19) is `y_t = y_{t−1} + 1`, which has no stable
solution, while the system with `C = 0` has the stable solution `y = 0`
(`simsH_zero_solution`). -/
theorem eq_2_19_const_singular :
    ¬ ∃ (y : ℕ → Fin 1 → ℂ) (η : ℕ → Fin 1 → ℂ),
      IsSims19Solution klS_detSystem 1 1 (fun _ => 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 y η ∧
        IsStableProc y := by
  rintro ⟨y, η, ⟨-, -, -, h⟩, ⟨M, -, hM⟩⟩
  have hy : ∀ t, y t 0 = y 0 0 + t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := congrFun (h t) 0
      simp only [matAct_one, klS_zero_matAct, Pi.add_apply, Pi.zero_apply, add_zero] at this
      rw [this, ih]
      push_cast
      ring
  obtain ⟨t, ht⟩ := exists_nat_gt (M + ‖y 0 0‖)
  have h1 := hM t 0
  rw [hy t] at h1
  have h2 : (t : ℝ) ≤ ‖y 0 0 + t‖ + ‖y 0 0‖ := by
    have := norm_sub_le (y 0 0 + t) (y 0 0)
    rw [add_sub_cancel_left, Complex.norm_natCast] at this
    exact this
  linarith

/-- Miao, p. 58 ("we may append `z_t` to `y_t` and replace `z_t` in (2.19) with `ε_t`"). If
`z_t = Φz_{t−1} + Σε_t` as in (2.1), then `(y, z)` stacked solves (2.20) with
`Γ̃₀ = [[Γ₀, −Ψ], [0, I]]`, `Γ̃₁ = [[Γ₁, 0], [0, Φ]]`, `Ψ̃ = [[0], [Σ]]`, `Π̃ = [[Π], [0]]` and
shock `ε` iff `y` solves (2.19) (with `C = 0`) driven by `z`, `z` is adapted and `z` follows
(2.1). (`Sg` stands for `Σ`, a reserved token.) -/
theorem eq_2_19_append {n nz nε m : ℕ} (E : CondExpSystem ℂ V)
    (Γ₀ Γ₁ : Matrix (Fin n) (Fin n) ℂ) (Ψ : Matrix (Fin n) (Fin nz) ℂ)
    (Pm : Matrix (Fin n) (Fin m) ℂ) (Φ : Matrix (Fin nz) (Fin nz) ℂ)
    (Sg : Matrix (Fin nz) (Fin nε) ℂ) (ε : ℕ → Fin nε → V) (y : ℕ → Fin n → V)
    (z : ℕ → Fin nz → V) (η : ℕ → Fin m → V) :
    IsSimsSolution E (simsBlk Γ₀ (-Ψ) 0 1) (simsBlk Γ₁ 0 0 Φ) (simsRows 0 Sg) (simsRows Pm 0)
        ε (fun t => Fin.append (y t) (z t)) η ↔
      IsSims19Solution E Γ₀ Γ₁ 0 Ψ Pm z y η ∧ IsAdaptedV E z ∧
        ∀ t, z (t + 1) = matAct Φ (z t) + matAct Sg (ε (t + 1)) := by
  have hadapt : IsAdaptedV E (fun t => Fin.append (y t) (z t)) ↔
      IsAdaptedV E y ∧ IsAdaptedV E z := by
    constructor
    · intro h
      exact ⟨fun t i => by simpa using h t (Fin.castAdd nz i),
        fun t i => by simpa using h t (Fin.natAdd n i)⟩
    · rintro ⟨h1, h2⟩ t i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using h1 t i
      · simpa using h2 t i
  have heq : ∀ t, (matAct (simsBlk Γ₀ (-Ψ) 0 1) (Fin.append (y (t + 1)) (z (t + 1))) =
      matAct (simsBlk Γ₁ 0 0 Φ) (Fin.append (y t) (z t)) + matAct (simsRows 0 Sg) (ε (t + 1)) +
        matAct (simsRows Pm 0) (η (t + 1))) ↔
      (matAct Γ₀ (y (t + 1)) = matAct Γ₁ (y t) + 0 + matAct Ψ (z (t + 1)) +
        matAct Pm (η (t + 1))) ∧ z (t + 1) = matAct Φ (z t) + matAct Sg (ε (t + 1)) := by
    intro t
    constructor
    · intro h
      have h1 := congrArg (· ∘ Fin.castAdd nz) h
      have h2 := congrArg (· ∘ Fin.natAdd n) h
      simp only [simsH_add_comp, simsH_blk_top, simsH_blk_bot] at h1 h2
      simp only [simsH_top_matAct, simsH_bot_matAct, simsRows_top, simsRows_bot,
        klS_append_castAdd, klS_append_natAdd, klS_zero_matAct, klS_neg_matAct, matAct_one,
        add_zero, zero_add] at h1 h2
      refine ⟨?_, h2⟩
      rw [add_zero]
      linear_combination (norm := module) h1
    · rintro ⟨h1, h2⟩
      refine klS_ext_blocks ?_ ?_
      · simp only [simsH_add_comp, simsH_blk_top]
        simp only [simsH_top_matAct, simsRows_top,
          klS_append_castAdd, klS_append_natAdd, klS_zero_matAct, klS_neg_matAct, add_zero]
        rw [h1]
        abel
      · simp only [simsH_add_comp, simsH_blk_bot]
        simp only [simsH_bot_matAct, simsRows_bot,
          klS_append_castAdd, klS_append_natAdd, klS_zero_matAct, matAct_one, add_zero,
          zero_add]
        exact h2
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨hy, hz⟩ := hadapt.1 h1
    exact ⟨⟨hy, h2, h3, fun t => ((heq t).1 (h4 t)).1⟩, hz, fun t => ((heq t).1 (h4 t)).2⟩
  · rintro ⟨⟨hy, h2, h3, h4⟩, hz, h5⟩
    exact ⟨hadapt.2 ⟨hy, hz⟩, h2, h3, fun t => (heq t).2 ⟨h4 t, h5 t⟩⟩

/-! ### Example 2.3.2 -/

/-- The New Keynesian model of Example 2.3.1 (Miao, (2.13)–(2.15), p. 54) for `t ≥ 1`:
`π_t = κx_t + βE_tπ_{t+1}`, `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1}) + ε^x_t`,
`i_t = ρ_r i_{t−1} + ε_t` (`p` is inflation `π`; `eI`, `eX` are the shocks `ε`, `ε^x`).
These are the three rows of (2.16). -/
def IsNKSolution (E : CondExpSystem ℂ V) (ρ κ β γ : ℂ) (eI eX : ℕ → V) (i x p : ℕ → V) :
    Prop :=
  ∀ t, p (t + 1) = κ • x (t + 1) + β • E.E (t + 1) (p (t + 2)) ∧
    x (t + 1) = E.E (t + 1) (x (t + 2)) - γ⁻¹ • (i (t + 1) - E.E (t + 1) (p (t + 2))) +
      eX (t + 1) ∧
    i (t + 1) = ρ • i t + eI (t + 1)

/-- `Γ₀` of Example 2.3.2 (Miao, p. 64), for `y_t = (i_t, ξ^x_t, ξ^π_t, x_t, π_t)`. -/
noncomputable def ex232Γ₀ (β γ : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, 0, 0, 0, 0; -γ⁻¹, 1, γ⁻¹, 0, 0; 0, 0, β, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

/-- `Γ₁` of Example 2.3.2 (Miao, p. 64). -/
def ex232Γ₁ (ρ κ : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![ρ, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, -κ, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0]

/-- `Ψ` of Example 2.3.2 (Miao, p. 64), for `ε_t = (ε_t, ε^x_t)`. -/
def ex232Ψ : Matrix (Fin 5) (Fin 2) ℂ :=
  !![1, 0; 0, -1; 0, 0; 0, 0; 0, 0]

/-- `Π` of Example 2.3.2 (Miao, p. 64), for `η_t = (η^x_t, η^π_t)`. -/
def ex232Pm (κ : ℂ) : Matrix (Fin 5) (Fin 2) ℂ :=
  !![0, 0; 1, 0; -κ, 1; 1, 0; 0, 1]

/-- The five rows of the Sims form of Example 2.3.2. -/
theorem example_2_3_2_rows (ρ κ β γ : ℂ) (a b : Fin 5 → V) (e h : Fin 2 → V) :
    matAct (ex232Γ₀ β γ) b = matAct (ex232Γ₁ ρ κ) a + matAct ex232Ψ e + matAct (ex232Pm κ) h ↔
      b 0 = ρ • a 0 + e 0 ∧ -γ⁻¹ • b 0 + b 1 + γ⁻¹ • b 2 = a 1 - e 1 + h 0 ∧
        β • b 2 = -κ • a 1 + a 2 + (-κ • h 0 + h 1) ∧ b 3 = a 1 + h 0 ∧ b 4 = a 2 + h 1 := by
  simp only [ex232Γ₀, ex232Γ₁, ex232Ψ, ex232Pm, funext_iff, Fin.forall_fin_succ, Pi.add_apply,
    matAct, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [sub_eq_add_neg, add_assoc]

/-- **Example 2.3.2** (Miao, p. 64). With `ξ^x_t = E_tx_{t+1}`, `ξ^π_t = E_tπ_{t+1}`,
`η^x_t = x_t − ξ^x_{t−1}`, `η^π_t = π_t − ξ^π_{t−1}`, system (2.16) is the Sims form (2.20) with
the printed `5 × 5` matrices `Γ₀`, `Γ₁` and `5 × 2` matrices `Ψ`, `Π` (every entry checked;
they are correct as printed): an adapted `y = (i, ξ^x, ξ^π, x, π)` with adapted `η` solves
(2.20) iff `(i, x, π)` solves (2.13)–(2.15) for `t ≥ 1`, `ξ^x`, `ξ^π` are the expectations
`E_tx_{t+1}`, `E_tπ_{t+1}`, and `η` is the stacked prediction error. -/
theorem example_2_3_2 (E : CondExpSystem ℂ V) (ρ κ β γ : ℂ) (eI eX : ℕ → V)
    (y : ℕ → Fin 5 → V) (η : ℕ → Fin 2 → V) :
    IsSimsSolution E (ex232Γ₀ β γ) (ex232Γ₁ ρ κ) ex232Ψ (ex232Pm κ) (fun t => ![eI t, eX t])
        y η ↔
      IsAdaptedV E y ∧ IsAdaptedV E η ∧
        IsNKSolution E ρ κ β γ eI eX (fun t => y t 0) (fun t => y t 3) (fun t => y t 4) ∧
        (∀ t, y t 1 = E.E t (y (t + 1) 3)) ∧ (∀ t, y t 2 = E.E t (y (t + 1) 4)) ∧
        ∀ t, η (t + 1) 0 = y (t + 1) 3 - y t 1 ∧ η (t + 1) 1 = y (t + 1) 4 - y t 2 := by
  constructor
  · rintro ⟨hya, hηa, hηm, heq⟩
    have hr := fun t => (example_2_3_2_rows ρ κ β γ (y t) (y (t + 1)) _ _).1 (heq t)
    have hξx : ∀ t, y t 1 = E.E t (y (t + 1) 3) := fun t => by
      rw [(hr t).2.2.2.1, map_add, hya t 1, hηm t 0, add_zero]
    have hξp : ∀ t, y t 2 = E.E t (y (t + 1) 4) := fun t => by
      rw [(hr t).2.2.2.2, map_add, hya t 2, hηm t 1, add_zero]
    refine ⟨hya, hηa, fun t => ⟨?_, ?_, ?_⟩, hξx, hξp, fun t => ⟨?_, ?_⟩⟩
    · obtain ⟨-, -, h2, h3, h4⟩ := hr t
      rw [← hξp (t + 1)]
      linear_combination (norm := module) h4 - κ • h3 - h2
    · obtain ⟨-, h1, -, h3, -⟩ := hr t
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      rw [← hξx (t + 1), ← hξp (t + 1)]
      linear_combination (norm := module) h3 - h1
    · have := (hr t).1
      simpa using this
    · rw [(hr t).2.2.2.1]
      abel
    · rw [(hr t).2.2.2.2]
      abel
  · rintro ⟨hya, hηa, hnk, hξx, hξp, hη⟩
    refine ⟨hya, hηa, fun t i => ?_, fun t => ?_⟩
    · fin_cases i
      · change E.E t (η (t + 1) 0) = 0
        rw [(hη t).1, map_sub, ← hξx t, hya t 1, sub_self]
      · change E.E t (η (t + 1) 1) = 0
        rw [(hη t).2, map_sub, ← hξp t, hya t 2, sub_self]
    · refine (example_2_3_2_rows ρ κ β γ (y t) (y (t + 1)) _ _).2 ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa using (hnk t).2.2
      · obtain ⟨-, h1, -⟩ := hnk t
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hξx (t + 1), hξp (t + 1), (hη t).1]
        linear_combination (norm := module) -h1
      · obtain ⟨h1, -, -⟩ := hnk t
        rw [hξp (t + 1), (hη t).1, (hη t).2]
        linear_combination (norm := module) -h1
      · rw [(hη t).1]
        abel
      · rw [(hη t).2]
        abel

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Existence of the singular value decomposition (2.25)

Miao, §2.3.3, p. 62, (2.25). `SimsSVD` takes the SVD `Q₂.Π = U.1D₁₁V.1ᴴ` as a hypothesis
(`IsThinSVD`). Here it is proved to exist for every complex `p × m` matrix `B`, with `D₁₁`
diagonal with positive entries and `r = rank B`, together with the complementary block `V.2`
of the unitary `V = [V.1 V.2]`: `V.1ᴴV.2 = 0`, `V.2ᴴV.2 = I`, `V.1V.1ᴴ + V.2V.2ᴴ = I`
(`exists_thinSVD`).

Route: the spectral theorem for the Hermitian positive semidefinite matrix `BᴴB`
(`Matrix.IsHermitian.eigenvectorBasis`, `mulVec_eigenvectorBasis`). The eigenvectors with
nonzero (hence positive) eigenvalue form `V.1`, the others `V.2`; `D₁₁ = diag(√λ)` and
`U.1 = BV.1D₁₁⁻¹`. The number of nonzero eigenvalues of `BᴴB` is `rank B`
(`rank_eq_card_non_zero_eigs`, `rank_conjTranspose_mul_self`).

Unconditional versions of the `SimsSVD` results that assumed an SVD: `colspace_iff_svd`,
`lambda_formula_svd`, `corollary_2_3_1_rank` (the pair `(y, η)` is unique iff `rank Q₂.Π = m`),
`lubik_schorfheide_rank`, `eq_2_26_svd`.

The full unitary `U = [U.1 U.2]` of (2.25) is not constructed: only `U.1` is used in the text.
-/

namespace Miao.RationalExpectations

open scoped Matrix

/-- The eigenvector matrix `W` of `BᴴB` satisfies `BᴴBW = W diag(λ)`. -/
theorem svdE_mul_eigen {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    H * (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) =
      (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.diagonal fun k => (hH.eigenvalues k : ℂ) := by
  ext a k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have := congrFun (hH.mulVec_eigenvectorBasis k) a
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at this
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, this, mul_comm]

/-- Columns of a unitary matrix selected by two maps: `(W.c₁)ᴴ(W.c₂)` is `1` at `(k, l)` iff
`c₁ k = c₂ l`. -/
theorem svdE_cols {m r k : ℕ} {W : Matrix (Fin m) (Fin m) ℂ} (hW : Wᴴ * W = 1)
    (c₁ : Fin r → Fin m) (c₂ : Fin k → Fin m) :
    (W.submatrix id c₁)ᴴ * W.submatrix id c₂ = (1 : Matrix (Fin m) (Fin m) ℂ).submatrix c₁ c₂ := by
  ext a b
  have := congrFun (congrFun hW (c₁ a)) (c₂ b)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id] using this

open scoped ComplexOrder in
/-- **Existence of the thin SVD** (Miao, (2.25), p. 62). Every complex `p × m` matrix `B` has
a thin SVD `B = U.1D₁₁V.1ᴴ` with `U.1ᴴU.1 = I`, `V.1ᴴV.1 = I`, `D₁₁ = diag(s)`, `s > 0`, and
`r = rank B`; and there is `V.2` (`k = m − r` columns) with `V.1ᴴV.2 = 0`, `V.2ᴴV.2 = I`,
`V.1V.1ᴴ + V.2V.2ᴴ = I`. -/
theorem exists_thinSVD {p m : ℕ} (B : Matrix (Fin p) (Fin m) ℂ) :
    ∃ (r k : ℕ) (U1 : Matrix (Fin p) (Fin r) ℂ) (s : Fin r → ℝ) (V1 : Matrix (Fin m) (Fin r) ℂ)
      (V2 : Matrix (Fin m) (Fin k) ℂ),
      IsThinSVD B U1 (Matrix.diagonal fun i => (s i : ℂ)) V1 ∧ (∀ i, 0 < s i) ∧
        r = B.rank ∧ r + k = m ∧ V1ᴴ * V2 = 0 ∧ V2ᴴ * V2 = 1 ∧ V1 * V1ᴴ + V2 * V2ᴴ = 1 := by
  classical
  have hP := Matrix.posSemidef_conjTranspose_mul_self B
  set hH := hP.1
  set lam := hH.eigenvalues
  set W : Matrix (Fin m) (Fin m) ℂ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hWdef
  have hWW : Wᴴ * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * Wᴴ = 1 := Unitary.coe_mul_star_self _
  have hHW := svdE_mul_eigen hH
  rw [← hWdef] at hHW
  set r := Fintype.card {i // lam i ≠ 0}
  set k := Fintype.card {i // ¬ lam i ≠ 0}
  let e1 := Fintype.equivFin {i // lam i ≠ 0}
  let e2 := Fintype.equivFin {i // ¬ lam i ≠ 0}
  let c1 : Fin r → Fin m := fun a => (e1.symm a).1
  let c2 : Fin k → Fin m := fun a => (e2.symm a).1
  have hc1 : Function.Injective c1 := fun a b h => e1.symm.injective (Subtype.ext h)
  have hc2 : Function.Injective c2 := fun a b h => e2.symm.injective (Subtype.ext h)
  have hpos : ∀ a, 0 < lam (c1 a) := fun a =>
    lt_of_le_of_ne (hP.eigenvalues_nonneg _) (e1.symm a).2.symm
  have hzero : ∀ a, lam (c2 a) = 0 := fun a => not_not.1 (e2.symm a).2
  set V1 := W.submatrix id c1 with hV1
  set V2 := W.submatrix id c2 with hV2
  have h11 : V1ᴴ * V1 = 1 := by rw [svdE_cols hWW, Matrix.submatrix_one _ hc1]
  have h22 : V2ᴴ * V2 = 1 := by rw [svdE_cols hWW, Matrix.submatrix_one _ hc2]
  have h12 : V1ᴴ * V2 = 0 := by
    rw [svdE_cols hWW]
    ext a b
    have hne : c1 a ≠ c2 b := fun h => by
      change (e1.symm a).1 = (e2.symm b).1 at h
      have h1 := (e1.symm a).2
      rw [h] at h1
      exact (e2.symm b).2 h1
    simp [Matrix.one_apply_ne hne]
  have hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1 := by
    rw [← hWW']
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply, id, hV1, hV2, c1, c2]
    rw [Equiv.sum_comp e1.symm (fun i => W a i.1 * star (W b i.1)),
      Equiv.sum_comp e2.symm (fun i => W a i.1 * star (W b i.1))]
    exact Fintype.sum_subtype_add_sum_subtype (fun i => lam i ≠ 0)
      (fun i => W a i * star (W b i))
  have hHV : ∀ (n : ℕ) (c : Fin n → Fin m),
      Bᴴ * B * W.submatrix id c = W.submatrix id c * Matrix.diagonal fun a => (lam (c a) : ℂ) := by
    intro n c
    ext a b
    have := congrFun (congrFun hHW a) (c b)
    rw [Matrix.mul_diagonal] at this
    rw [Matrix.mul_diagonal, Matrix.submatrix_apply, id, ← this]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  set s : Fin r → ℝ := fun a => Real.sqrt (lam (c1 a))
  have hs : ∀ a, 0 < s a := fun a => Real.sqrt_pos.2 (hpos a)
  have hs2 : ∀ a, (s a : ℂ) * (s a : ℂ) = (lam (c1 a) : ℂ) := fun a => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos a).le]
  set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => (s a : ℂ)
  set Di : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => ((s a)⁻¹ : ℂ)
  have hsne : ∀ a, (s a : ℂ) ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (hs a).ne'
  have hDiD : Di * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hsne a)
  have hDi : Diᴴ = Di := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hBV2 : B * V2 = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero, Matrix.conjTranspose_mul,
      show V2ᴴ * Bᴴ * (B * V2) = V2ᴴ * (Bᴴ * B * V2) by simp only [Matrix.mul_assoc], hHV k c2,
      ← Matrix.mul_assoc, h22, Matrix.one_mul]
    ext a b
    simp [Matrix.diagonal_apply, hzero]
  refine ⟨r, k, B * V1 * Di, s, V1, V2, ⟨?_, ?_, h11, ?_⟩, hs, ?_, ?_, h12, h22, hcompl⟩
  · calc B = B * (V1 * V1ᴴ + V2 * V2ᴴ) := by rw [hcompl, Matrix.mul_one]
      _ = B * V1 * (Di * D) * V1ᴴ := by
        rw [hDiD, Matrix.mul_add, ← Matrix.mul_assoc B V2, hBV2, Matrix.zero_mul, add_zero,
          Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]; rfl
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDi,
      show Di * (V1ᴴ * Bᴴ) * (B * V1 * Di) = Di * (V1ᴴ * (Bᴴ * B * V1)) * Di by
        simp only [Matrix.mul_assoc], hHV r c1, ← Matrix.mul_assoc V1ᴴ, h11, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hs2]
    field_simp [hsne a]
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hsne a
  · rw [← Matrix.rank_conjTranspose_mul_self, hH.rank_eq_card_non_zero_eigs]
  · have := Fintype.card_congr (Equiv.sumCompl fun i : Fin m => lam i ≠ 0)
    rw [Fintype.card_sum, Fintype.card_fin] at this
    exact this

/-- Miao, p. 62, the column-space test, unconditionally: every `A` has a thin SVD
`A = U.1D₁₁V.1ᴴ`, and for it `col(C) ⊆ col(A)` iff `(I − U.1U.1ᴴ)C = 0` for every `C`. -/
theorem colspace_iff_svd {p m : ℕ} (A : Matrix (Fin p) (Fin m) ℂ) :
    ∃ (r : ℕ) (U1 : Matrix (Fin p) (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ)
      (V1 : Matrix (Fin m) (Fin r) ℂ), IsThinSVD A U1 D V1 ∧
        ∀ (k : ℕ) (C : Matrix (Fin p) (Fin k) ℂ),
          (∃ Λ : Matrix (Fin m) (Fin k) ℂ, C = A * Λ) ↔ (1 - U1 * U1ᴴ) * C = 0 := by
  obtain ⟨r, -, U1, s, V1, -, h, -⟩ := exists_thinSVD A
  exact ⟨r, U1, _, V1, h, fun _ C => colspace_iff h C⟩

/-- Miao, p. 62, "`Λ = V.1D₁₁⁻¹U.1ᴴ(Q₂.Ψ)`", unconditionally: under Assumption 2.3.1 there is
a thin SVD of `Q₂.Π` for which this `Λ` works. -/
theorem lambda_formula_svd {ns nu nε m : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hA1 : SimsAssumption1 Q Ψ Pm) :
    ∃ (r : ℕ) (U1 : Matrix (Fin nu) (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ)
      (V1 : Matrix (Fin m) (Fin r) ℂ), IsThinSVD (simsBot Q * Pm) U1 D V1 ∧
        simsBot Q * Ψ = simsBot Q * Pm * (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) := by
  obtain ⟨r, -, U1, s, V1, -, h, -⟩ := exists_thinSVD (simsBot Q * Pm)
  exact ⟨r, U1, _, V1, h, lambda_formula h hA1⟩

/-- **Corollary 2.3.1** (Miao, p. 62), unconditional form of `corollary_2_3_1`: with a rich
filtration the stable solution with its prediction error, `(y, η)`, is unique iff
`rank(Q₂.Π) = m`. -/
theorem corollary_2_3_1_rank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} :
    SimsPairUnique E Γ₀ Γ₁ Ψ Pm ↔ (simsBot Q * Pm).rank = m := by
  obtain ⟨r, -, U1, s, V1, -, h, -, hr, -⟩ := exists_thinSVD (simsBot Q * Pm)
  rw [corollary_2_3_1 E hrich hqz h, hr]

/-- **Lubik–Schorfheide** (Miao, p. 62), unconditional form of `lubik_schorfheide`: if
`rank(Q₂.Π) < m` and the filtration is rich, every stable solution `(y, η)` lies in an
injective one-parameter family of stable solutions with the same initial value. -/
theorem lubik_schorfheide_rank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hr : (simsBot Q * Pm).rank < m) {ε : ℕ → Fin nε → V} {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y) :
    ∃ f : ℂ → (ℕ → Fin (ns + nu) → V) × (ℕ → Fin m → V), Function.Injective f ∧
      ∀ c, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε (f c).1 (f c).2 ∧ IsStableProc (f c).1 ∧
        (f c).1 0 = y 0 := by
  obtain ⟨r, -, U1, s, V1, -, h, -, hrk, -⟩ := exists_thinSVD (simsBot Q * Pm)
  exact lubik_schorfheide E hrich hqz h (hrk ▸ hr) hsol hy

/-- Miao, (2.26), p. 63, unconditionally: under Assumption 2.3.1 there is an SVD
`Q₂.Π = U.1D₁₁V.1ᴴ` with complement `V.2` such that the solutions `η` of (2.23) are exactly
`η = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε + V.2e`, `e` arbitrary. -/
theorem eq_2_26_svd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ns nu nε m : ℕ}
    {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} (hA1 : SimsAssumption1 Q Ψ Pm) :
    ∃ (r k : ℕ) (U1 : Matrix (Fin nu) (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ)
      (V1 : Matrix (Fin m) (Fin r) ℂ) (V2 : Matrix (Fin m) (Fin k) ℂ),
      IsThinSVD (simsBot Q * Pm) U1 D V1 ∧ ∀ (e : Fin nε → V) (h : Fin m → V),
        matAct (simsBot Q) (matAct Ψ e + matAct Pm h) = 0 ↔
          ∃ s : Fin k → V, h = -matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) e + matAct V2 s := by
  obtain ⟨r, k, U1, s, V1, V2, h, -, -, -, h12, -, hc⟩ := exists_thinSVD (simsBot Q * Pm)
  exact ⟨r, k, U1, _, V1, V2, h, fun e η => eq_2_26 h h12 hc hA1 e η⟩

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Nonlinear rational expectations models: the perturbation method

Miao, §2.4, pp. 64–69: the nonlinear model (2.27) `E_t f(y_{t+1}, y_t, x_{t+1}, x_t) = 0` and
the second-order perturbation method of Schmitt-Grohé and Uribe. Following the book ("we
consider the scalar case only"), `x`, `y`, `σ` are real; `f : ℝ⁴ → ℝ` is one equation (the
`2 × 2` systems are in `PerturbationSystem`), with arguments ordered `(y', y, x', x)`.

* Partial derivatives: `pertP f j v` (`j = 0, 1, 2, 3` for `y', y, x', x`), `pertDx`, `pertDs`
  (Fréchet derivative applied to a coordinate direction); `f_{jk} = pertP (pertP f j) k`, the
  derivative of `f_j` in direction `k`; `pertRow` is the bracket `[f_{jy'}w₁ + … + f_{jx}w₄]`.
* The chain rule along curves (`pert_hasDerivAt_two`, `pert_hasDerivAt_four`), and along the
  policy (2.29) `y = g(x, σ)`, `x' = h(x, σ) + ησε'` (`pertPsi`, `pertPhi`, `pert_psi_x`, …).
* `pertF`: `F(x, σ)` of (2.30); `pertF_Dx`, `pertF_Ds` (first partials at every point).
* At the steady state (`pertPsi_ss`, `pertPhi_ss`): `eq_F_x` (p. 68), `eq_F_sigma_E` (the first
  printed line for `F_σ`, with `ε'` terms) and `eq_F_sigma` (the second; the `ε'` terms vanish
  since `Eε' = 0`), `eq_F_xx` (p. 68), `eq_F_sigma_x` and `eq_F_sigma_sigma` (p. 69), all
  computed by the chain rule.

**Departures.** The shock has a finite distribution (`IsFiniteShock`: values `ε i` with weights
`p i ≥ 0`, `∑ p i = 1`, `∑ p i ε i = 0`), so `E` is a finite sum; the book has "IID with bounded
support". `f`, `g`, `h` are `C²` on all of `ℝ⁴`, `ℝ²`. The existence and smoothness of the policy
functions `g`, `h` is an assumption of the method (not proved in the book, nor here).

**Corrections.**
* `F_xx` (p. 68): the first term of the display is printed `f_{y'y}g_xh_x`; it is
  `f_{y'y'}g_xh_x` (`eq_F_xx`; counterexample `eq_F_xx_printed_false`).
* `F_σσ` (p. 69): the printed `I` must be `E[ε'²]` (the book does not normalise the variance);
  the display (and `F_σx`) also uses `g_σ = h_σ = 0`, which `eq_F_sigma_sigma` and
  `eq_F_sigma_x` take as hypotheses (`eq_F_sigma_sigma_printed_false`).
-/

namespace Miao.RationalExpectations

/-! ### Partial derivatives -/

/-- The coordinate directions of `(y', y, x', x) ∈ ℝ⁴` (the argument order of `f` in (2.27)). -/
def pertE4 : Fin 4 → ℝ × ℝ × ℝ × ℝ :=
  ![(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]

/-- The partial derivative `∂f/∂v_j` of `f : ℝ⁴ → ℝ` at `v` (`j = 0, 1, 2, 3` for
`y', y, x', x`): `f_{y'} = pertP f 0`, and `f_{jk} = pertP (pertP f j) k` is the derivative of
`f_j` in the direction `k`. -/
noncomputable def pertP (f : ℝ × ℝ × ℝ × ℝ → ℝ) (j : Fin 4) (v : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  fderiv ℝ f v (pertE4 j)

/-- The partial derivative `G_x` of `G(x, σ)`. -/
noncomputable def pertDx (G : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := fderiv ℝ G q (1, 0)

/-- The partial derivative `G_σ` of `G(x, σ)`. -/
noncomputable def pertDs (G : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := fderiv ℝ G q (0, 1)

/-- The chain rule along a curve in `ℝ²`. -/
theorem pert_hasDerivAt_two {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) {a b : ℝ → ℝ}
    {a' b' t : ℝ} (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => G (a s, b s)) (pertDx G (a t, b t) * a' + pertDs G (a t, b t) * b') t := by
  have := (hG (a t, b t)).hasFDerivAt.comp_hasDerivAt t (ha.prodMk hb)
  refine this.congr_deriv ?_
  have e : ((a', b') : ℝ × ℝ) = a' • ((1, 0) : ℝ × ℝ) + b' • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, pertDx, pertDs]
  ring

/-- The chain rule along a curve in `ℝ⁴`. -/
theorem pert_hasDerivAt_four {K : ℝ × ℝ × ℝ × ℝ → ℝ} (hK : Differentiable ℝ K)
    {a b c d : ℝ → ℝ} {a' b' c' d' t : ℝ} (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t)
    (hc : HasDerivAt c c' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun s => K (a s, b s, c s, d s))
      (pertP K 0 (a t, b t, c t, d t) * a' + pertP K 1 (a t, b t, c t, d t) * b' +
        pertP K 2 (a t, b t, c t, d t) * c' + pertP K 3 (a t, b t, c t, d t) * d') t := by
  have := (hK (a t, b t, c t, d t)).hasFDerivAt.comp_hasDerivAt t
    (ha.prodMk (hb.prodMk (hc.prodMk hd)))
  refine this.congr_deriv ?_
  have e : ((a', b', c', d') : ℝ × ℝ × ℝ × ℝ) =
      a' • pertE4 0 + b' • pertE4 1 + c' • pertE4 2 + d' • pertE4 3 := by
    ext <;> simp [pertE4]
  rw [e, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, pertP, pertP, pertP, pertP]
  ring

/-- Along the `x`-line. -/
theorem pert_line_x {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (x σ : ℝ) :
    HasDerivAt (fun t => G (t, σ)) (pertDx G (x, σ)) x :=
  (pert_hasDerivAt_two hG (hasDerivAt_id x) (hasDerivAt_const x σ)).congr_deriv (by
    simp only [id, mul_one, mul_zero, add_zero])

/-- Along the `σ`-line. -/
theorem pert_line_s {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (x σ : ℝ) :
    HasDerivAt (fun s => G (x, s)) (pertDs G (x, σ)) σ :=
  (pert_hasDerivAt_two hG (hasDerivAt_const σ x) (hasDerivAt_id σ)).congr_deriv (by
    simp only [id, mul_one, mul_zero, zero_add])

/-- A partial derivative `G_x` is the derivative along the `x`-line. -/
theorem pert_Dx_eq {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) {x σ d : ℝ}
    (h : HasDerivAt (fun t => G (t, σ)) d x) : pertDx G (x, σ) = d :=
  (pert_line_x hG x σ).unique h

/-- A partial derivative `G_σ` is the derivative along the `σ`-line. -/
theorem pert_Ds_eq {G : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) {x σ d : ℝ}
    (h : HasDerivAt (fun s => G (x, s)) d σ) : pertDs G (x, σ) = d :=
  (pert_line_s hG x σ).unique h

/-- The partial derivatives of a `C²` function are differentiable. -/
theorem pert_diff_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ}
    (hG : ContDiff ℝ 2 G) (w : E) : Differentiable ℝ fun q => fderiv ℝ G q w :=
  ((hG.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
    (by norm_num)

/-! ### The policy functions and `F` of (2.30) -/

/-- The argument `(h(x, σ) + ησε', σ)` of `g` in `g(x', σ)` (Miao, (2.29)–(2.30)). -/
def pertPsi (h : ℝ × ℝ → ℝ) (η e : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (h q + η * q.2 * e, q.2)

/-- `(y', y, x', x)` under the policy (2.29) when `ε' = e`:
`(g(h(x, σ) + ησe, σ), g(x, σ), h(x, σ) + ησe, x)`. -/
def pertPhi (g h : ℝ × ℝ → ℝ) (η e : ℝ) (q : ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (g (pertPsi h η e q), g q, h q + η * q.2 * e, q.1)

/-- `F(x, σ) = E f(g(h(x, σ) + ησε', σ), g(x, σ), h(x, σ) + ησε', x)` (Miao, (2.30)), for a shock
`ε'` taking the value `ε i` with probability `p i`. -/
def pertF (f : ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ)
    (q : ℝ × ℝ) : ℝ :=
  ∑ i, p i * f (pertPhi g h η (ε i) q)

theorem pert_psi_x {G h : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (hh : Differentiable ℝ h)
    (η e x σ : ℝ) :
    HasDerivAt (fun t => G (pertPsi h η e (t, σ)))
      (pertDx G (pertPsi h η e (x, σ)) * pertDx h (x, σ)) x := by
  have ha : HasDerivAt (fun t => h (t, σ) + η * σ * e) (pertDx h (x, σ)) x :=
    (pert_line_x hh x σ).add_const _
  exact (pert_hasDerivAt_two hG ha (hasDerivAt_const x σ)).congr_deriv (by
    simp only [mul_zero, add_zero]; rfl)

theorem pert_psi_s {G h : ℝ × ℝ → ℝ} (hG : Differentiable ℝ G) (hh : Differentiable ℝ h)
    (η e x σ : ℝ) :
    HasDerivAt (fun s => G (pertPsi h η e (x, s)))
      (pertDx G (pertPsi h η e (x, σ)) * (pertDs h (x, σ) + η * e) +
        pertDs G (pertPsi h η e (x, σ))) σ := by
  have ha : HasDerivAt (fun s => h (x, s) + η * s * e) (pertDs h (x, σ) + η * e) σ := by
    refine (pert_line_s hh x σ).add ?_
    simpa using ((hasDerivAt_id σ).const_mul η).mul_const e
  exact (pert_hasDerivAt_two hG ha (hasDerivAt_id σ)).congr_deriv (by
    simp only [id, mul_one]; rfl)

theorem pert_phi_x {K : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hK : Differentiable ℝ K)
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (η e x σ : ℝ) :
    HasDerivAt (fun t => K (pertPhi g h η e (t, σ)))
      (pertP K 0 (pertPhi g h η e (x, σ)) * (pertDx g (pertPsi h η e (x, σ)) * pertDx h (x, σ)) +
        pertP K 1 (pertPhi g h η e (x, σ)) * pertDx g (x, σ) +
        pertP K 2 (pertPhi g h η e (x, σ)) * pertDx h (x, σ) +
        pertP K 3 (pertPhi g h η e (x, σ))) x := by
  have hc : HasDerivAt (fun t => h (t, σ) + η * σ * e) (pertDx h (x, σ)) x :=
    (pert_line_x hh x σ).add_const _
  exact (pert_hasDerivAt_four hK (pert_psi_x hg hh η e x σ) (pert_line_x hg x σ) hc
    (hasDerivAt_id x)).congr_deriv (by simp only [mul_one]; rfl)

theorem pert_phi_s {K : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hK : Differentiable ℝ K)
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) (η e x σ : ℝ) :
    HasDerivAt (fun s => K (pertPhi g h η e (x, s)))
      (pertP K 0 (pertPhi g h η e (x, σ)) * (pertDx g (pertPsi h η e (x, σ)) *
          (pertDs h (x, σ) + η * e) + pertDs g (pertPsi h η e (x, σ))) +
        pertP K 1 (pertPhi g h η e (x, σ)) * pertDs g (x, σ) +
        pertP K 2 (pertPhi g h η e (x, σ)) * (pertDs h (x, σ) + η * e)) σ := by
  have hc : HasDerivAt (fun s => h (x, s) + η * s * e) (pertDs h (x, σ) + η * e) σ := by
    refine (pert_line_s hh x σ).add ?_
    simpa using ((hasDerivAt_id σ).const_mul η).mul_const e
  exact (pert_hasDerivAt_four hK (pert_psi_s hg hh η e x σ) (pert_line_s hg x σ) hc
    (hasDerivAt_const σ x)).congr_deriv (by simp only [mul_zero, add_zero]; rfl)

theorem pertF_contDiff {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) :
    ContDiff ℝ 2 (pertF f g h η p ε) := by
  unfold pertF pertPhi pertPsi
  fun_prop

/-- A shock `ε'` with a finite distribution: value `ε i` with probability `p i`, mean zero
(Miao, p. 66: "IID with bounded support"; here finitely supported). -/
structure IsFiniteShock {N : ℕ} (p ε : Fin N → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_one : ∑ i, p i = 1
  mean_zero : ∑ i, p i * ε i = 0

theorem pert_sum_lin {N : ℕ} {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {φ : Fin N → ℝ}
    {A : ℝ} (B : ℝ) (hφ : ∀ i, φ i = A + B * ε i) : ∑ i, p i * φ i = A := by
  simp only [hφ, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hp.sum_one, one_mul,
    show ∑ i, p i * (B * ε i) = B * ∑ i, p i * ε i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
    hp.mean_zero, mul_zero, add_zero]

theorem pert_sum_quad {N : ℕ} {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {φ : Fin N → ℝ}
    (A B C : ℝ) (hφ : ∀ i, φ i = A + B * ε i + C * ε i ^ 2) :
    ∑ i, p i * φ i = A + C * ∑ i, p i * ε i ^ 2 := by
  have e : ∀ i, p i * φ i = p i * (A + B * ε i) + C * (p i * ε i ^ 2) := fun i => by
    rw [hφ]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [pert_sum_lin hp B fun i => rfl]

/-- At the deterministic steady state, `(h(x̄, 0) + η·0·e, 0) = (x̄, 0)`. -/
theorem pertPsi_ss {h : ℝ × ℝ → ℝ} {xb : ℝ} (hx : h (xb, 0) = xb) (η e : ℝ) :
    pertPsi h η e (xb, 0) = (xb, 0) := by
  simp [pertPsi, hx]

/-- At the deterministic steady state, `Φ(x̄, 0) = (ȳ, ȳ, x̄, x̄)`. -/
theorem pertPhi_ss {g h : ℝ × ℝ → ℝ} {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (η e : ℝ) : pertPhi g h η e (xb, 0) = (yb, yb, xb, xb) := by
  simp [pertPhi, pertPsi_ss hx, hx, hy]

/-- `F_x(x, σ)` by the chain rule, at every `(x, σ)`. -/
theorem pertF_Dx {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) (x σ : ℝ) :
    pertDx (pertF f g h η p ε) (x, σ) = ∑ i, p i *
      (pertP f 0 (pertPhi g h η (ε i) (x, σ)) *
          (pertDx g (pertPsi h η (ε i) (x, σ)) * pertDx h (x, σ)) +
        pertP f 1 (pertPhi g h η (ε i) (x, σ)) * pertDx g (x, σ) +
        pertP f 2 (pertPhi g h η (ε i) (x, σ)) * pertDx h (x, σ) +
        pertP f 3 (pertPhi g h η (ε i) (x, σ))) :=
  pert_Dx_eq ((pertF_contDiff hf hg hh η p ε).differentiable (by norm_num))
    (HasDerivAt.fun_sum fun i _ => (pert_phi_x (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) (hh.differentiable (by norm_num)) η (ε i) x σ).const_mul
        (p i))

/-- `F_σ(x, σ)` by the chain rule, at every `(x, σ)`. -/
theorem pertF_Ds {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) (x σ : ℝ) :
    pertDs (pertF f g h η p ε) (x, σ) = ∑ i, p i *
      (pertP f 0 (pertPhi g h η (ε i) (x, σ)) * (pertDx g (pertPsi h η (ε i) (x, σ)) *
          (pertDs h (x, σ) + η * ε i) + pertDs g (pertPsi h η (ε i) (x, σ))) +
        pertP f 1 (pertPhi g h η (ε i) (x, σ)) * pertDs g (x, σ) +
        pertP f 2 (pertPhi g h η (ε i) (x, σ)) * (pertDs h (x, σ) + η * ε i)) :=
  pert_Ds_eq ((pertF_contDiff hf hg hh η p ε).differentiable (by norm_num))
    (HasDerivAt.fun_sum fun i _ => (pert_phi_s (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) (hh.differentiable (by norm_num)) η (ε i) x σ).const_mul
        (p i))

/-- Miao, p. 68: `F_x(x̄, 0) = f_{y'}g_xh_x + f_yg_x + f_{x'}h_x + f_x` (as printed), all
derivatives at the steady state. -/
theorem eq_F_x {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertF f g h η p ε) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDx h (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDx g (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDx h (xb, 0) + pertP f 3 (yb, yb, xb, xb) := by
  rw [pertF_Dx hf hg hh]
  simp only [pertPsi_ss hx, pertPhi_ss hx hy]
  exact pert_sum_lin hp 0 fun i => by ring

/-- Miao, p. 67: `F_σ(x̄, 0) = E{f_{y'}[g_x(h_σ + ηε') + g_σ] + f_yg_σ + f_{x'}(h_σ + ηε')}`
(the first printed line, with `E` the finite sum over the values of `ε'`). -/
theorem eq_F_sigma_E {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} (p ε : Fin N → ℝ) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDs (pertF f g h η p ε) (xb, 0) = ∑ i, p i *
      (pertP f 0 (yb, yb, xb, xb) * (pertDx g (xb, 0) * (pertDs h (xb, 0) + η * ε i) +
          pertDs g (xb, 0)) + pertP f 1 (yb, yb, xb, xb) * pertDs g (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * (pertDs h (xb, 0) + η * ε i)) := by
  rw [pertF_Ds hf hg hh]
  simp only [pertPsi_ss hx, pertPhi_ss hx hy]

/-- Miao, p. 67: `F_σ(x̄, 0) = f_{y'}[g_xh_σ + g_σ] + f_yg_σ + f_{x'}h_σ` (the second printed
line): the `ε'` terms of the first line vanish because `Eε' = 0`. -/
theorem eq_F_sigma {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDs (pertF f g h η p ε) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * (pertDx g (xb, 0) * pertDs h (xb, 0) + pertDs g (xb, 0)) +
        pertP f 1 (yb, yb, xb, xb) * pertDs g (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDs h (xb, 0) := by
  rw [eq_F_sigma_E hf hg hh η p ε hx hy]
  exact pert_sum_lin hp (pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * η +
    pertP f 2 (yb, yb, xb, xb) * η) fun i => by ring

/-- The bracket `[f_{jy'}w₁ + f_{jy}w₂ + f_{jx'}w₃ + f_{jx}w₄]` of the printed second-order
displays (Miao, p. 68): the derivative of `f_j` in the direction `w`, at `v`. -/
noncomputable def pertRow (f : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (j : Fin 4)
    (w₁ w₂ w₃ w₄ : ℝ) : ℝ :=
  pertP (pertP f j) 0 v * w₁ + pertP (pertP f j) 1 v * w₂ + pertP (pertP f j) 2 v * w₃ +
    pertP (pertP f j) 3 v * w₄

/-- Miao, p. 68, `F_xx(x̄, 0)`, computed by the chain rule. With `w = (g_xh_x, g_x, h_x, 1)` and
`S = (ȳ, ȳ, x̄, x̄)`:
`F_xx = [f_{y'y'}g_xh_x + f_{y'y}g_x + f_{y'x'}h_x + f_{y'x}]g_xh_x + f_{y'}g_xxh_xh_x +
f_{y'}g_xh_xx + [f_{yy'}g_xh_x + …]g_x + f_yg_xx + [f_{x'y'}g_xh_x + …]h_x + f_{x'}h_xx +
f_{xy'}g_xh_x + f_{xy}g_x + f_{xx'}h_x + f_{xx}`.
This is the printed display except for its first term, printed `f_{y'y}g_xh_x`: it must be
`f_{y'y'}g_xh_x` (`eq_F_xx_printed_false`). -/
theorem eq_F_xx {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertDx (pertF f g h η p ε)) (xb, 0) =
      pertRow f (yb, yb, xb, xb) 0 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 * (pertDx g (xb, 0) * pertDx h (xb, 0)) +
        pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) * pertDx h (xb, 0) *
          pertDx h (xb, 0) +
        pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDx (pertDx h) (xb, 0) +
        pertRow f (yb, yb, xb, xb) 1 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 * pertDx g (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) +
        pertRow f (yb, yb, xb, xb) 2 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 * pertDx h (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDx (pertDx h) (xb, 0) +
        pertRow f (yb, yb, xb, xb) 3 (pertDx g (xb, 0) * pertDx h (xb, 0)) (pertDx g (xb, 0))
          (pertDx h (xb, 0)) 1 := by
  have hg' := hg.differentiable (by norm_num)
  have hh' := hh.differentiable (by norm_num)
  have hfj : ∀ j, Differentiable ℝ (pertP f j) := fun j => pert_diff_fderiv hf (pertE4 j)
  have hgx : Differentiable ℝ (pertDx g) := pert_diff_fderiv hg _
  have hhx : Differentiable ℝ (pertDx h) := pert_diff_fderiv hh _
  have hDF : Differentiable ℝ (pertDx (pertF f g h η p ε)) :=
    pert_diff_fderiv (pertF_contDiff hf hg hh η p ε) _
  have key := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (((((pert_phi_x (hfj 0) hg' hh' η (ε i) xb 0).mul
      ((pert_psi_x hgx hh' η (ε i) xb 0).mul (pert_line_x hhx xb 0))).add
      ((pert_phi_x (hfj 1) hg' hh' η (ε i) xb 0).mul (pert_line_x hgx xb 0))).add
      ((pert_phi_x (hfj 2) hg' hh' η (ε i) xb 0).mul (pert_line_x hhx xb 0))).add
      (pert_phi_x (hfj 3) hg' hh' η (ε i) xb 0)).const_mul (p i)
  rw [pert_Dx_eq hDF (key.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => pertF_Dx hf hg hh η p ε t 0))]
  simp only [Pi.mul_apply, pertPsi_ss hx, pertPhi_ss hx hy]
  refine pert_sum_lin hp 0 fun i => ?_
  simp only [pertRow]
  ring

/-- Miao, p. 69, `F_σx(x̄, 0)`, given `g_σ = h_σ = 0` (which the book has established at this
point, `theorem_g_sigma_zero`): `F_σx = f_{y'}g_xh_σx + f_{y'}g_σxh_x + f_yg_σx + f_{x'}h_σx`,
as printed (`g_σx`, `h_σx` are the `σ`-derivatives of `g_x`, `h_x`). The `D²f` terms and the
`g_xx` term carry a factor `ε'` and vanish in expectation. Without `g_σ = h_σ = 0` there are
further, inhomogeneous terms (e.g. `f_{y'}g_xxh_σh_x`). -/
theorem eq_F_sigma_x {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDx (pertF f g h η p ε)) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDs (pertDx h) (xb, 0) +
        pertP f 0 (yb, yb, xb, xb) * pertDs (pertDx g) (xb, 0) * pertDx h (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDs (pertDx g) (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDs (pertDx h) (xb, 0) := by
  have hg' := hg.differentiable (by norm_num)
  have hh' := hh.differentiable (by norm_num)
  have hfj : ∀ j, Differentiable ℝ (pertP f j) := fun j => pert_diff_fderiv hf (pertE4 j)
  have hgx : Differentiable ℝ (pertDx g) := pert_diff_fderiv hg _
  have hhx : Differentiable ℝ (pertDx h) := pert_diff_fderiv hh _
  have hDF : Differentiable ℝ (pertDx (pertF f g h η p ε)) :=
    pert_diff_fderiv (pertF_contDiff hf hg hh η p ε) _
  have key := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (((((pert_phi_s (hfj 0) hg' hh' η (ε i) xb 0).mul
      ((pert_psi_s hgx hh' η (ε i) xb 0).mul (pert_line_s hhx xb 0))).add
      ((pert_phi_s (hfj 1) hg' hh' η (ε i) xb 0).mul (pert_line_s hgx xb 0))).add
      ((pert_phi_s (hfj 2) hg' hh' η (ε i) xb 0).mul (pert_line_s hhx xb 0))).add
      (pert_phi_s (hfj 3) hg' hh' η (ε i) xb 0)).const_mul (p i)
  rw [pert_Ds_eq hDF (key.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => pertF_Dx hf hg hh η p ε xb s))]
  simp only [Pi.mul_apply, pertPsi_ss hx, pertPhi_ss hx hy, hgs, hhs]
  refine pert_sum_lin hp
    (η * (pertRow f (yb, yb, xb, xb) 0 (pertDx g (xb, 0)) 0 1 0 * pertDx g (xb, 0) *
        pertDx h (xb, 0) + pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) *
        pertDx h (xb, 0) + pertRow f (yb, yb, xb, xb) 1 (pertDx g (xb, 0)) 0 1 0 *
        pertDx g (xb, 0) + pertRow f (yb, yb, xb, xb) 2 (pertDx g (xb, 0)) 0 1 0 *
        pertDx h (xb, 0) + pertRow f (yb, yb, xb, xb) 3 (pertDx g (xb, 0)) 0 1 0)) fun i => ?_
  simp only [pertRow]
  ring

/-- Miao, p. 69, `F_σσ(x̄, 0)`, given `g_σ = h_σ = 0`:
`F_σσ = f_{y'}g_xh_σσ + f_{y'y'}g_xηg_xηE[ε'²] + f_{y'x'}ηg_xηE[ε'²] + f_{y'}g_xxηηE[ε'²] +
f_{y'}g_σσ + f_yg_σσ + f_{x'}h_σσ + f_{x'y'}g_xηηE[ε'²] + f_{x'x'}ηηE[ε'²]`.
The printed display has `I` where `E[ε'²]` stands: the book never normalises the shock variance
(`ε` is only "IID with bounded support"), so the printed formula holds only when `E[ε'²] = 1`
(`eq_F_sigma_sigma_printed_false`). The cross terms `f_{y'}(g_σx + g_xσ)ηε'` vanish in
expectation. -/
theorem eq_F_sigma_sigma {f : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDs (pertF f g h η p ε)) (xb, 0) =
      pertP f 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDs (pertDs h) (xb, 0) +
        pertP (pertP f 0) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * η * pertDx g (xb, 0) * η *
          ∑ i, p i * ε i ^ 2 +
        pertP (pertP f 0) 2 (yb, yb, xb, xb) * η * pertDx g (xb, 0) * η * ∑ i, p i * ε i ^ 2 +
        pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) * η * η * ∑ i, p i * ε i ^ 2 +
        pertP f 0 (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
        pertP f 1 (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
        pertP f 2 (yb, yb, xb, xb) * pertDs (pertDs h) (xb, 0) +
        pertP (pertP f 2) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * η * η * ∑ i, p i * ε i ^ 2 +
        pertP (pertP f 2) 2 (yb, yb, xb, xb) * η * η * ∑ i, p i * ε i ^ 2 := by
  have hg' := hg.differentiable (by norm_num)
  have hh' := hh.differentiable (by norm_num)
  have hfj : ∀ j, Differentiable ℝ (pertP f j) := fun j => pert_diff_fderiv hf (pertE4 j)
  have hgx : Differentiable ℝ (pertDx g) := pert_diff_fderiv hg _
  have hgs' : Differentiable ℝ (pertDs g) := pert_diff_fderiv hg _
  have hhs' : Differentiable ℝ (pertDs h) := pert_diff_fderiv hh _
  have hDF : Differentiable ℝ (pertDs (pertF f g h η p ε)) :=
    pert_diff_fderiv (pertF_contDiff hf hg hh η p ε) _
  have key := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((((pert_phi_s (hfj 0) hg' hh' η (ε i) xb 0).mul
      (((pert_psi_s hgx hh' η (ε i) xb 0).mul ((pert_line_s hhs' xb 0).add_const (η * ε i))).add
        (pert_psi_s hgs' hh' η (ε i) xb 0))).add
      ((pert_phi_s (hfj 1) hg' hh' η (ε i) xb 0).mul (pert_line_s hgs' xb 0))).add
      ((pert_phi_s (hfj 2) hg' hh' η (ε i) xb 0).mul
        ((pert_line_s hhs' xb 0).add_const (η * ε i)))).const_mul (p i)
  rw [pert_Ds_eq hDF (key.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => pertF_Ds hf hg hh η p ε xb s))]
  simp only [Pi.mul_apply, Pi.add_apply, pertPsi_ss hx, pertPhi_ss hx hy, hgs, hhs]
  rw [pert_sum_quad hp
    (pertP f 0 (yb, yb, xb, xb) * (pertDx g (xb, 0) * pertDs (pertDs h) (xb, 0) +
      pertDs (pertDs g) (xb, 0)) + pertP f 1 (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
      pertP f 2 (yb, yb, xb, xb) * pertDs (pertDs h) (xb, 0))
    (pertP f 0 (yb, yb, xb, xb) * η *
      (pertDs (pertDx g) (xb, 0) + pertDx (pertDs g) (xb, 0)))
    (η * η * ((pertP (pertP f 0) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) +
      pertP (pertP f 0) 2 (yb, yb, xb, xb)) * pertDx g (xb, 0) +
      pertP f 0 (yb, yb, xb, xb) * pertDx (pertDx g) (xb, 0) +
      pertP (pertP f 2) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) +
      pertP (pertP f 2) 2 (yb, yb, xb, xb))) fun i => by ring]
  ring

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The perturbation method: the systems of equations and the summary claim

Miao, §2.4, pp. 64–69, continued: the scalar model with two equations `f = (f₀, f₁)`
(`n = n_x + n_y = 2`), so each step of the perturbation method is a `2 × 2` linear system.

* `IsPertSolution`: `f`, `g`, `h` are `C²`, the shock is finite with mean zero and `F ≡ 0`
  ((2.27), (2.29), (2.30)). `pert_partials_vanish`, `pert_F_partials_zero` (p. 67).
* `eq_steady_state` (p. 67, "`ȳ = g(x̄, 0)`, `x̄ = h(x̄, 0)`", correct direction) and
  `steady_state_printed_false`.
* First order: `g_sigma_system`, `pert_hom2_unique`, `theorem_g_sigma_zero` (certainty
  equivalence, p. 67); `eq_F_x_zero`, `eq_2_31`, `eq_2_32`, `eq_2_33`, `eq_2_31_of_2_33` (p. 68).
* (2.28): `eq_2_28_differential` (the total differential) and `eq_2_28` (the linearised system
  is `A E_t dX_{t+1} = B dX_t` of the form (2.11), with `A = [f_{x'} f_{y'}]`, `B = −[f_x f_y]`).
* Second order (p. 69): `g_sigma_x_system`, `theorem_g_sigma_x_zero`; `eq_F_sigma_sigma_linear`,
  `g_sigma_sigma_unique`; `eq_F_xx_linear`, `g_xx_unique`; `pertTaylor2`, `pertTaylor2_sigma`,
  `summary_uncertainty` (uncertainty enters the second-order solution only through
  `½g_σσσ²`, `½h_σσσ²`).

**Corrections.**
* "For a unique solution to exist, we must have `g_σ = h_σ = 0`" (p. 67): the homogeneous system
  always has the zero solution; it is the only one iff the determinant `A₀B₁ − B₀A₁ ≠ 0`
  (`pert_hom2_unique`), and then `g_σ = h_σ = 0` (`theorem_g_sigma_zero`). With determinant
  zero, `g_σ ≠ 0` is possible in a genuine solution (`g_sigma_not_forced`); likewise for
  `g_σx` (`g_sigma_x_not_forced`).
* The `F_σx` system is homogeneous only given `g_σ = h_σ = 0` (hypothesis of
  `g_sigma_x_system`); the summary claim needs both determinants nonzero.
* "(2.33) is equivalent to (2.28)/(2.31)": (2.31) implies (2.33) along the linearised path
  (`eq_2_33`); the converse needs `x̂₀ ≠ 0` (`eq_2_31_of_2_33`).
* "We first note `ȳ = g(x̄, 0)`, `x̄ = h(x̄, 0)`" is an assumption (a choice of steady state on
  the policy), not a consequence (`steady_state_printed_false`).
-/

namespace Miao.RationalExpectations

open scoped Matrix

/-! ### The model -/

variable (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (η : ℝ) {N : ℕ}
  (p ε : Fin N → ℝ) in
/-- The scalar nonlinear model (2.27) `E_t f(y_{t+1}, y_t, x_{t+1}, x_t) = 0` with one
predetermined variable `x` and one non-predetermined `y` (so `f = (f₀, f₁) : ℝ⁴ → ℝ²`), solved by
the policy (2.29) `y = g(x, σ)`, `x' = h(x, σ) + ησε'` (Miao, pp. 66–67): `f`, `g`, `h` are `C²`,
the shock is finite with mean zero, and `F(x, σ) = 0` for all `(x, σ)` ((2.30)). The existence
and smoothness of `g` and `h` is an assumption of the method, not proved by the book. -/
structure IsPertSolution : Prop where
  f_smooth : ∀ k, ContDiff ℝ 2 (f k)
  g_smooth : ContDiff ℝ 2 g
  h_smooth : ContDiff ℝ 2 h
  shock : IsFiniteShock p ε
  solves : ∀ k q, pertF (f k) g h η p ε q = 0

/-- Miao, p. 67: "Since `F(x, σ)` is equal to zero for any values of `(x, σ)`, we must have
`F_{xⁱσʲ}(x, σ) = 0`": the partial derivatives of a function that vanishes identically
vanish identically (so all iterated ones do too). -/
theorem pert_partials_vanish {G : ℝ × ℝ → ℝ} (hG : ∀ q, G q = 0) :
    (∀ q, pertDx G q = 0) ∧ ∀ q, pertDs G q = 0 := by
  have e : G = fun _ => 0 := funext hG
  subst e
  simp [pertDx, pertDs]

/-- Miao, p. 67, `F_{xⁱσʲ}(x, σ) = 0` for `i + j ≤ 2`, for each equation of a solution. -/
theorem pert_F_partials_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) (k : Fin 2) (q : ℝ × ℝ) :
    pertDx (pertF (f k) g h η p ε) q = 0 ∧ pertDs (pertF (f k) g h η p ε) q = 0 ∧
      pertDx (pertDx (pertF (f k) g h η p ε)) q = 0 ∧
      pertDs (pertDx (pertF (f k) g h η p ε)) q = 0 ∧
      pertDs (pertDs (pertF (f k) g h η p ε)) q = 0 := by
  obtain ⟨h1, h2⟩ := pert_partials_vanish (hs.solves k)
  exact ⟨h1 q, h2 q, (pert_partials_vanish h1).1 q, (pert_partials_vanish h1).2 q,
    (pert_partials_vanish h2).2 q⟩

/-- Miao, p. 67, "`ȳ = g(x̄, 0)`, `x̄ = h(x̄, 0)`", the correct direction: if `x̄` is a fixed
point of the deterministic policy `h(·, 0)` and `ȳ = g(x̄, 0)`, then `(x̄, ȳ)` is a
deterministic steady state, `f(ȳ, ȳ, x̄, x̄) = 0`. The converse is not automatic
(`steady_state_printed_false`): that the policy passes through the chosen steady state is part of
the method's assumptions. -/
theorem eq_steady_state {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb : ℝ} (hx : h (xb, 0) = xb)
    (k : Fin 2) : f k (g (xb, 0), g (xb, 0), xb, xb) = 0 := by
  have := hs.solves k (xb, 0)
  simp only [pertF, pertPhi_ss hx rfl] at this
  rwa [← Finset.sum_mul, hs.shock.sum_one, one_mul] at this

/-- **The steady state need not lie on the policy** (Miao, p. 67). With `f₀ = y − y'`,
`f₁ = (x' − x)(x' − 2x)`, `η = 0`, the policy `g = 0`, `h(x, σ) = 2x` solves (2.30), and
`(x̄, ȳ) = (1, 0)` is a deterministic steady state, yet `h(x̄, 0) = 2 ≠ x̄`. -/
theorem steady_state_printed_false :
    ∃ (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 1 → ℝ),
      IsPertSolution f g h 0 p ε ∧ (∀ k, f k (0, 0, 1, 1) = 0) ∧ h (1, 0) ≠ 1 := by
  refine ⟨![fun v => v.2.1 - v.1, fun v => (v.2.2.1 - v.2.2.2) * (v.2.2.1 - 2 * v.2.2.2)],
    fun _ => 0, fun q => 2 * q.1, ![1], ![0], ⟨fun k => ?_, contDiff_const, by fun_prop,
      ⟨fun i => by simp, by simp, by simp⟩, fun k q => ?_⟩, fun k => ?_, by norm_num⟩
  · fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;> fun_prop
  · fin_cases k <;> simp [pertF, pertPhi]
  · fin_cases k <;> simp

/-! ### `g_σ` and `h_σ` -/

/-- The coefficient of `g_σ` (and of `g_σσ`) in equation `k`: `f_{y'} + f_y` at `v`. -/
noncomputable def pertCoefA (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  pertP fk 0 v + pertP fk 1 v

/-- The coefficient of `h_σ` (and of `h_σσ`, `h_σx`) in equation `k`: `f_{y'}g_x + f_{x'}`. -/
noncomputable def pertCoefB (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (gx : ℝ) : ℝ :=
  pertP fk 0 v * gx + pertP fk 2 v

/-- The coefficient of `g_σx` in equation `k`: `f_{y'}h_x + f_y`. -/
noncomputable def pertCoefAx (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (hx : ℝ) : ℝ :=
  pertP fk 0 v * hx + pertP fk 1 v

/-- A homogeneous `2 × 2` system `au + bv = 0`, `cu + dv = 0` has only the zero solution iff
`ad − bc ≠ 0`. -/
theorem pert_hom2_unique (a b c d : ℝ) :
    (∀ u v, a * u + b * v = 0 → c * u + d * v = 0 → u = 0 ∧ v = 0) ↔ a * d - b * c ≠ 0 := by
  constructor
  · intro H hdet
    by_cases hab : a = 0 ∧ b = 0
    · by_cases hcd : c = 0 ∧ d = 0
      · have := H 1 0 (by rw [hab.1, hab.2]; ring) (by rw [hcd.1, hcd.2]; ring)
        exact one_ne_zero this.1
      · have := H d (-c) (by linear_combination hdet) (by ring)
        exact hcd ⟨by linarith [this.2], this.1⟩
    · have := H b (-a) (by ring) (by linear_combination -hdet)
      exact hab ⟨by linarith [this.2], this.1⟩
  · intro hdet u v h1 h2
    have hu : (a * d - b * c) * u = 0 := by linear_combination d * h1 - b * h2
    have hv : (a * d - b * c) * v = 0 := by linear_combination a * h2 - c * h1
    exact ⟨(mul_eq_zero.1 hu).resolve_left hdet, (mul_eq_zero.1 hv).resolve_left hdet⟩

/-- Miao, p. 67: `F_σ(x̄, 0) = 0` is the homogeneous linear system
`(f_{y'} + f_y)g_σ + (f_{y'}g_x + f_{x'})h_σ = 0` (one equation per component of `f`), which
always has the solution `g_σ = h_σ = 0`. -/
theorem g_sigma_system {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (k : Fin 2) :
    pertCoefA (f k) (yb, yb, xb, xb) * pertDs g (xb, 0) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDs h (xb, 0) = 0 := by
  have := (pert_F_partials_zero hs k (xb, 0)).2.1
  rw [eq_F_sigma (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy] at this
  rw [pertCoefA, pertCoefB]
  linear_combination this

/-- Miao, p. 67, "For a unique solution to exist, we must have `g_σ = h_σ = 0`", made precise:
the homogeneous system of `g_sigma_system` has the zero solution, and it is its unique solution
iff the determinant `A₀B₁ − B₀A₁` is nonzero (`pert_hom2_unique`); in that case
`g_σ = h_σ = 0` (certainty equivalence). -/
theorem theorem_g_sigma_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0) :
    pertDs g (xb, 0) = 0 ∧ pertDs h (xb, 0) = 0 :=
  (pert_hom2_unique _ _ _ _).2 hdet _ _ (g_sigma_system hs hx hy 0) (g_sigma_system hs hx hy 1)

/-! ### `F_x` and (2.31)–(2.33) -/

/-- Miao, p. 68: `F_x(x̄, 0) = f_{y'}g_xh_x + f_yg_x + f_{x'}h_x + f_x = 0` for each equation. -/
theorem eq_F_x_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (k : Fin 2) :
    pertP (f k) 0 (yb, yb, xb, xb) * pertDx g (xb, 0) * pertDx h (xb, 0) +
      pertP (f k) 1 (yb, yb, xb, xb) * pertDx g (xb, 0) +
      pertP (f k) 2 (yb, yb, xb, xb) * pertDx h (xb, 0) + pertP (f k) 3 (yb, yb, xb, xb) = 0 := by
  rw [← eq_F_x (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy]
  exact (pert_F_partials_zero hs k (xb, 0)).1

/-- Miao, (2.31), p. 68: the two equations `f_{y'}g_xh_x + f_yg_x + f_{x'}h_x + f_x = 0` are
`[f_{x'} f_{y'}][1; g_x]h_x = −[f_x f_y][1; g_x]`, with `A = [f_{x'} f_{y'}]`,
`B = −[f_x f_y]` (rows = equations). -/
theorem eq_2_31 (fyp fy fxp fx : Fin 2 → ℝ) (gx hx : ℝ) :
    (∀ k, fyp k * gx * hx + fy k * gx + fxp k * hx + fx k = 0) ↔
      hx • (!![fxp 0, fyp 0; fxp 1, fyp 1] *ᵥ ![1, gx]) =
        -!![fx 0, fy 0; fx 1, fy 1] *ᵥ ![1, gx] := by
  simp only [funext_iff, Fin.forall_fin_two]
  simp only [Fin.isValue, Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, one_smul,
    Matrix.mulVec_empty, add_zero, Pi.smul_apply, Pi.add_apply, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul, Matrix.mulVec,
    dotProduct, Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    neg_mul, Finset.sum_neg_distrib, Fin.sum_univ_two, mul_one, Matrix.cons_val_one, neg_add_rev]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨by linear_combination h0, by linear_combination h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨by linear_combination h0, by linear_combination h1⟩

/-- Miao, (2.32), p. 68: postmultiplying (2.31) by `x̂ = x − x̄`; (2.32) for all `x̂` is
equivalent to (2.31). -/
theorem eq_2_32 (A B : Matrix (Fin 2) (Fin 2) ℝ) (gx hx : ℝ) :
    hx • (A *ᵥ ![1, gx]) = B *ᵥ ![1, gx] ↔
      ∀ xh : ℝ, A *ᵥ ((hx * xh) • ![1, gx]) = B *ᵥ (xh • ![1, gx]) := by
  constructor
  · intro H xh
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← H, smul_smul, mul_comm]
  · intro H
    have := H 1
    rwa [mul_one, one_smul, Matrix.mulVec_smul] at this

/-- Miao, (2.33), p. 68: if (2.31) holds, the linearised non-stochastic solution
`x̂_{t+1} = h_xx̂_t`, `ŷ_t = g_xx̂_t` satisfies `A[x̂_{t+1}; ŷ_{t+1}] = B[x̂_t; ŷ_t]`, which is
(2.28) without shocks. -/
theorem eq_2_33 (A B : Matrix (Fin 2) (Fin 2) ℝ) {gx hx : ℝ}
    (H : hx • (A *ᵥ ![1, gx]) = B *ᵥ ![1, gx]) {xh yh : ℕ → ℝ}
    (hxh : ∀ t, xh (t + 1) = hx * xh t) (hyh : ∀ t, yh t = gx * xh t) (t : ℕ) :
    A *ᵥ ![xh (t + 1), yh (t + 1)] = B *ᵥ ![xh t, yh t] := by
  have e1 : ![xh (t + 1), yh (t + 1)] = (hx * xh t) • ![1, gx] := by
    rw [hyh, hxh]
    ext i
    fin_cases i <;> simp [mul_comm]
  have e2 : ![xh t, yh t] = xh t • ![1, gx] := by
    rw [hyh]
    ext i
    fin_cases i <;> simp [mul_comm]
  rw [e1, e2]
  exact (eq_2_32 A B gx hx).1 H (xh t)

/-- Miao, p. 68, "this equation is equivalent to (2.31)", made precise: conversely, if the
linearised non-stochastic solution satisfies (2.33) at `t = 0` with `x̂₀ ≠ 0`, then (2.31)
holds. (With `x̂₀ = 0` (2.33) is vacuous.) -/
theorem eq_2_31_of_2_33 (A B : Matrix (Fin 2) (Fin 2) ℝ) {gx hx : ℝ} {xh yh : ℕ → ℝ}
    (hxh : ∀ t, xh (t + 1) = hx * xh t) (hyh : ∀ t, yh t = gx * xh t) (h0 : xh 0 ≠ 0)
    (H : A *ᵥ ![xh 1, yh 1] = B *ᵥ ![xh 0, yh 0]) :
    hx • (A *ᵥ ![1, gx]) = B *ᵥ ![1, gx] := by
  have e1 : ![xh 1, yh 1] = xh 0 • (hx • ![1, gx]) := by
    rw [hyh, hxh]
    ext i
    fin_cases i <;> simp [mul_comm, mul_assoc]
  have e2 : ![xh 0, yh 0] = xh 0 • ![1, gx] := by
    rw [hyh]
    ext i
    fin_cases i <;> simp [mul_comm]
  rw [e1, e2, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul] at H
  exact smul_right_injective _ h0 H

/-! ### The linearised system (2.28) -/

/-- Miao, p. 65, "We totally differentiate (2.27)": for `f` differentiable at the steady state
`S`, `f(S + dv) = f(S) + f_{y'}dy' + f_ydy + f_{x'}dx' + f_xdx + o(‖dv‖)`. -/
theorem eq_2_28_differential {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {S : ℝ × ℝ × ℝ × ℝ}
    (hf : DifferentiableAt ℝ fk S) :
    HasFDerivAt fk (fderiv ℝ fk S) S ∧ ∀ dv : ℝ × ℝ × ℝ × ℝ,
      fderiv ℝ fk S dv = pertP fk 0 S * dv.1 + pertP fk 1 S * dv.2.1 +
        pertP fk 2 S * dv.2.2.1 + pertP fk 3 S * dv.2.2.2 := by
  refine ⟨hf.hasFDerivAt, fun dv => ?_⟩
  have e : dv = dv.1 • pertE4 0 + dv.2.1 • pertE4 1 + dv.2.2.1 • pertE4 2 +
      dv.2.2.2 • pertE4 3 := by
    ext <;> simp [pertE4]
  conv_lhs => rw [e]
  simp only [map_add, map_smul, smul_eq_mul, pertP]
  ring

/-- Miao, (2.28), p. 65: the linearised system
`E_t[f_{y'}dy_{t+1} + f_ydy_t + f_{x'}dx_{t+1} + f_xdx_t] = 0` (one equation per component of
`f`), for adapted `dx`, `dy`, is the system `A E_t dX_{t+1} = B dX_t` of the form (2.11) with
`dX = (dx, dy)`, `A = [f_{x'} f_{y'}]`, `B = −[f_x f_y]` (and no exogenous term). -/
theorem eq_2_28 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (E : CondExpSystem ℝ V)
    (fyp fy fxp fx : Fin 2 → ℝ) {dx dy : ℕ → V} (hdx : ∀ t, E.E t (dx t) = dx t)
    (hdy : ∀ t, E.E t (dy t) = dy t) :
    (∀ t k, E.E t (fyp k • dy (t + 1) + fy k • dy t + fxp k • dx (t + 1) + fx k • dx t) = 0) ↔
      ∀ t, matAct !![fxp 0, fyp 0; fxp 1, fyp 1] (Evec E t ![dx (t + 1), dy (t + 1)]) =
        matAct !![-fx 0, -fy 0; -fx 1, -fy 1] ![dx t, dy t] := by
  have e : ∀ t k, E.E t (fyp k • dy (t + 1) + fy k • dy t + fxp k • dx (t + 1) + fx k • dx t) =
      fyp k • E.E t (dy (t + 1)) + fy k • dy t + fxp k • E.E t (dx (t + 1)) + fx k • dx t :=
    fun t k => by simp only [map_add, map_smul, hdx, hdy]
  simp only [e, funext_iff, Fin.forall_fin_two]
  simp only [matAct, Evec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · intro H t
    exact ⟨by linear_combination (norm := module) (H t).1, by
      linear_combination (norm := module) (H t).2⟩
  · intro H t
    exact ⟨by linear_combination (norm := module) (H t).1, by
      linear_combination (norm := module) (H t).2⟩

/-! ### `g_σx`, `h_σx` -/

/-- Miao, p. 69: given `g_σ = h_σ = 0`, `F_σx(x̄, 0) = 0` is the homogeneous linear system
`(f_{y'}h_x + f_y)g_σx + (f_{y'}g_x + f_{x'})h_σx = 0` (one equation per component of `f`). -/
theorem g_sigma_x_system {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ} {N : ℕ}
    {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0)
    (k : Fin 2) :
    pertCoefAx (f k) (yb, yb, xb, xb) (pertDx h (xb, 0)) * pertDs (pertDx g) (xb, 0) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDs (pertDx h) (xb, 0) = 0 := by
  have := (pert_F_partials_zero hs k (xb, 0)).2.2.2.1
  rw [eq_F_sigma_x (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy hgs hhs] at this
  rw [pertCoefAx, pertCoefB]
  linear_combination this

/-- Miao, p. 69, "If a unique solution exists, then the solution must be equal to zero": if the
determinant of the `F_σ` system and that of the `F_σx` system are nonzero, then
`g_σ = h_σ = 0` and `g_σx = h_σx = 0`. -/
theorem theorem_g_sigma_x_zero {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0)
    (hdetx : pertCoefAx (f 0) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
        pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0)) -
      pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) *
        pertCoefAx (f 1) (yb, yb, xb, xb) (pertDx h (xb, 0)) ≠ 0) :
    pertDs (pertDx g) (xb, 0) = 0 ∧ pertDs (pertDx h) (xb, 0) = 0 := by
  obtain ⟨hgs, hhs⟩ := theorem_g_sigma_zero hs hx hy hdet
  exact (pert_hom2_unique _ _ _ _).2 hdetx _ _ (g_sigma_x_system hs hx hy hgs hhs 0)
    (g_sigma_x_system hs hx hy hgs hhs 1)

/-! ### `g_σσ`, `h_σσ` and `g_xx`, `h_xx` -/

/-- The inhomogeneous coefficient of the `F_σσ` equation (to be multiplied by `η²E[ε'²]`):
`f_{y'y'}g_x² + f_{y'x'}g_x + f_{y'}g_xx + f_{x'y'}g_x + f_{x'x'}`. -/
noncomputable def pertCoefSS (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (gx gxx : ℝ) : ℝ :=
  (pertP (pertP fk 0) 0 v * gx + pertP (pertP fk 0) 2 v) * gx + pertP fk 0 v * gxx +
    pertP (pertP fk 2) 0 v * gx + pertP (pertP fk 2) 2 v

/-- Miao, p. 69, "This is a system of `n` linear equations for `n` unknowns `g_σσ` and `h_σσ`",
precisely: `F_σσ(x̄, 0) = (f_{y'} + f_y)g_σσ + (f_{y'}g_x + f_{x'})h_σσ + η²E[ε'²]c` (given
`g_σ = h_σ = 0`), with the same coefficients as the `F_σ` system and `c = pertCoefSS`, which
does not involve `g_σσ`, `h_σσ`. -/
theorem eq_F_sigma_sigma_linear {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ 2 fk) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ}
    {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDs (pertF fk g h η p ε)) (xb, 0) =
      pertCoefA fk (yb, yb, xb, xb) * pertDs (pertDs g) (xb, 0) +
        pertCoefB fk (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDs (pertDs h) (xb, 0) +
        η * η * (∑ i, p i * ε i ^ 2) *
          pertCoefSS fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0)) := by
  rw [eq_F_sigma_sigma hf hg hh η hp hx hy hgs hhs, pertCoefA, pertCoefB, pertCoefSS]
  ring

/-- Miao, p. 69, solving `F_σσ(x̄, 0) = 0`: if the determinant of the `F_σ` system is nonzero,
`(g_σσ, h_σσ)` is the unique solution of the linear system of `eq_F_sigma_sigma_linear`. -/
theorem g_sigma_sigma_unique {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0) (u v : ℝ)
    (huv : ∀ k, pertCoefA (f k) (yb, yb, xb, xb) * u +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * v + η * η * (∑ i, p i * ε i ^ 2) *
        pertCoefSS (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0)) = 0) :
    u = pertDs (pertDs g) (xb, 0) ∧ v = pertDs (pertDs h) (xb, 0) := by
  obtain ⟨hgs, hhs⟩ := theorem_g_sigma_zero hs hx hy hdet
  have e : ∀ k, pertCoefA (f k) (yb, yb, xb, xb) * (u - pertDs (pertDs g) (xb, 0)) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * (v - pertDs (pertDs h) (xb, 0)) =
        0 := fun k => by
    have h0 := (pert_F_partials_zero hs k (xb, 0)).2.2.2.2
    rw [eq_F_sigma_sigma_linear (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy hgs
      hhs] at h0
    linear_combination huv k - h0
  obtain ⟨h1, h2⟩ := (pert_hom2_unique _ _ _ _).2 hdet _ _ (e 0) (e 1)
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-- The coefficient of `g_xx` in `F_xx`: `f_{y'}h_x² + f_y`. -/
noncomputable def pertCoefAxx (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (hx : ℝ) : ℝ :=
  pertP fk 0 v * hx * hx + pertP fk 1 v

/-- The part of `F_xx` free of `g_xx`, `h_xx`. -/
noncomputable def pertCoefXX (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ) (gx hx : ℝ) : ℝ :=
  pertRow fk v 0 (gx * hx) gx hx 1 * (gx * hx) + pertRow fk v 1 (gx * hx) gx hx 1 * gx +
    pertRow fk v 2 (gx * hx) gx hx 1 * hx + pertRow fk v 3 (gx * hx) gx hx 1

/-- Miao, p. 69, "the above equation represents a system of `n × n_x × n_x` linear equations
for the same number of unknowns given by the elements of `g_xx` and `h_xx`", precisely (scalar
case, two equations): `F_xx(x̄, 0) = (f_{y'}h_x² + f_y)g_xx + (f_{y'}g_x + f_{x'})h_xx + c` with
`c` free of `g_xx`, `h_xx`. -/
theorem eq_F_xx_linear {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 fk)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertDx (pertF fk g h η p ε)) (xb, 0) =
      pertCoefAxx fk (yb, yb, xb, xb) (pertDx h (xb, 0)) * pertDx (pertDx g) (xb, 0) +
        pertCoefB fk (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertDx (pertDx h) (xb, 0) +
        pertCoefXX fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx h (xb, 0)) := by
  rw [eq_F_xx hf hg hh η hp hx hy, pertCoefAxx, pertCoefB, pertCoefXX]
  ring

/-- Miao, p. 69, solving `F_xx(x̄, 0) = 0`: if its determinant is nonzero, `(g_xx, h_xx)` is
the unique solution of the linear system of `eq_F_xx_linear`. -/
theorem g_xx_unique {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefAxx (f 0) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
        pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0)) -
      pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) *
        pertCoefAxx (f 1) (yb, yb, xb, xb) (pertDx h (xb, 0)) ≠ 0) (u v : ℝ)
    (huv : ∀ k, pertCoefAxx (f k) (yb, yb, xb, xb) (pertDx h (xb, 0)) * u +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * v +
        pertCoefXX (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx h (xb, 0)) = 0) :
    u = pertDx (pertDx g) (xb, 0) ∧ v = pertDx (pertDx h) (xb, 0) := by
  have e : ∀ k, pertCoefAxx (f k) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
      (u - pertDx (pertDx g) (xb, 0)) +
      pertCoefB (f k) (yb, yb, xb, xb) (pertDx g (xb, 0)) * (v - pertDx (pertDx h) (xb, 0)) =
        0 := fun k => by
    have h0 := (pert_F_partials_zero hs k (xb, 0)).2.2.1
    rw [eq_F_xx_linear (hs.f_smooth k) hs.g_smooth hs.h_smooth η hs.shock hx hy] at h0
    linear_combination huv k - h0
  obtain ⟨h1, h2⟩ := (pert_hom2_unique _ _ _ _).2 hdet _ _ (e 0) (e 1)
  exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 h2⟩

/-! ### The summary claim -/

/-- The second-order Taylor polynomial of `G` at `(x̄, 0)` as printed (Miao, p. 66):
`G + G_x(x − x̄) + G_σσ + ½G_xx(x − x̄)² + G_xσ(x − x̄)σ + ½G_σσσ²`, with `G_xσ` taken as the
`σ`-derivative of `G_x`. -/
noncomputable def pertTaylor2 (G : ℝ × ℝ → ℝ) (xb x σ : ℝ) : ℝ :=
  G (xb, 0) + pertDx G (xb, 0) * (x - xb) + pertDs G (xb, 0) * σ +
    1 / 2 * pertDx (pertDx G) (xb, 0) * (x - xb) ^ 2 + pertDs (pertDx G) (xb, 0) * (x - xb) * σ +
    1 / 2 * pertDs (pertDs G) (xb, 0) * σ ^ 2

/-- If `G_σ = G_σx = 0` at `(x̄, 0)`, the second-order Taylor polynomial depends on `σ` only
through `½G_σσσ²`. -/
theorem pertTaylor2_sigma {G : ℝ × ℝ → ℝ} {xb : ℝ} (hs : pertDs G (xb, 0) = 0)
    (hsx : pertDs (pertDx G) (xb, 0) = 0) (x σ : ℝ) :
    pertTaylor2 G xb x σ = pertTaylor2 G xb x 0 + 1 / 2 * pertDs (pertDs G) (xb, 0) * σ ^ 2 := by
  simp only [pertTaylor2, hs, hsx]
  ring

/-- Miao, p. 69, "uncertainty matters in the second-order approximated solution only through the
terms `½g_σσ(x̄, 0)σ²` and `½h_σσ(x̄, 0)σ²`": if the determinants of the `F_σ` and `F_σx` systems
are nonzero, the second-order Taylor polynomials of `g` and `h` at `(x̄, 0)` equal their
certainty (`σ = 0`) parts plus `½g_σσσ²`, resp. `½h_σσσ²`. -/
theorem summary_uncertainty {f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} {η : ℝ}
    {N : ℕ} {p ε : Fin N → ℝ} (hs : IsPertSolution f g h η p ε) {xb yb : ℝ}
    (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb)
    (hdet : pertCoefA (f 0) (yb, yb, xb, xb) * pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0))
      - pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) * pertCoefA (f 1) (yb, yb, xb, xb)
      ≠ 0)
    (hdetx : pertCoefAx (f 0) (yb, yb, xb, xb) (pertDx h (xb, 0)) *
        pertCoefB (f 1) (yb, yb, xb, xb) (pertDx g (xb, 0)) -
      pertCoefB (f 0) (yb, yb, xb, xb) (pertDx g (xb, 0)) *
        pertCoefAx (f 1) (yb, yb, xb, xb) (pertDx h (xb, 0)) ≠ 0) (x σ : ℝ) :
    pertTaylor2 g xb x σ = pertTaylor2 g xb x 0 + 1 / 2 * pertDs (pertDs g) (xb, 0) * σ ^ 2 ∧
      pertTaylor2 h xb x σ = pertTaylor2 h xb x 0 + 1 / 2 * pertDs (pertDs h) (xb, 0) * σ ^ 2 := by
  obtain ⟨hgs, hhs⟩ := theorem_g_sigma_zero hs hx hy hdet
  obtain ⟨hgsx, hhsx⟩ := theorem_g_sigma_x_zero hs hx hy hdet hdetx
  exact ⟨pertTaylor2_sigma hgs hgsx x σ, pertTaylor2_sigma hhs hhsx x σ⟩

end Miao.RationalExpectations

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The perturbation method: misprints and counterexamples

Miao, §2.4, pp. 68–69: the misprints in the second-order displays, and the counterexamples
showing that certainty equivalence needs the determinant conditions.

* `pertFxxPrinted`, `eq_F_xx_printed` (true `F_xx` = printed + `(f_{y'y'} − f_{y'y})(g_xh_x)²`),
  `eq_F_xx_printed_false` (`f = y'²`, `g = h = x`: true `2`, printed `0`).
* `pertFssPrinted`, `eq_F_sigma_sigma_printed` (true `F_σσ` = printed + `(E[ε'²] − 1)η²c`),
  `eq_F_sigma_sigma_printed_false` (`f = x'²`, `ε' = ±2`: true `8`, printed `2`).
* `g_sigma_not_forced` (`f = (y − y', x' − x)`, `g = σ`, `h = x`: a genuine solution with zero
  determinant and `g_σ = 1`), `g_sigma_x_not_forced` (`g = σx`: `g_σx = 1`).
* `pert_P_eq`: a partial derivative computed along a coordinate line.
-/

namespace Miao.RationalExpectations

/-- A partial derivative `pertP K j v` computed along the line `v + t·e_j`. -/
theorem pert_P_eq {K : ℝ × ℝ × ℝ × ℝ → ℝ} (hK : Differentiable ℝ K) {v : ℝ × ℝ × ℝ × ℝ}
    {j : Fin 4} {φ : ℝ → ℝ} {d : ℝ} (hφ : ∀ t, K (v + t • pertE4 j) = φ t)
    (h : HasDerivAt φ d 0) : pertP K j v = d := by
  have hl : HasDerivAt (fun t : ℝ => v + t • pertE4 j) (pertE4 j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (pertE4 j)).const_add v
  have := (hK (v + (0 : ℝ) • pertE4 j)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  rw [zero_smul, add_zero] at this
  exact this.unique (h.congr_of_eventuallyEq (Filter.Eventually.of_forall hφ))

/-! ### `F_xx`: the misprinted first term -/

/-- The display for `F_xx(x̄, 0)` as printed (Miao, p. 68), whose first term is
`f_{y'y}g_xh_x`. -/
noncomputable def pertFxxPrinted (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ)
    (gx hx gxx hxx : ℝ) : ℝ :=
  (pertP (pertP fk 0) 1 v * (gx * hx) + pertP (pertP fk 0) 1 v * gx +
      pertP (pertP fk 0) 2 v * hx + pertP (pertP fk 0) 3 v) * (gx * hx) +
    pertP fk 0 v * gxx * hx * hx + pertP fk 0 v * gx * hxx +
    pertRow fk v 1 (gx * hx) gx hx 1 * gx + pertP fk 1 v * gxx +
    pertRow fk v 2 (gx * hx) gx hx 1 * hx + pertP fk 2 v * hxx + pertRow fk v 3 (gx * hx) gx hx 1

/-- Miao, p. 68: the true `F_xx(x̄, 0)` differs from the printed display by
`(f_{y'y'} − f_{y'y})(g_xh_x)²`. -/
theorem eq_F_xx_printed {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 fk)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ} {p ε : Fin N → ℝ}
    (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb) (hy : g (xb, 0) = yb) :
    pertDx (pertDx (pertF fk g h η p ε)) (xb, 0) =
      pertFxxPrinted fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx h (xb, 0))
          (pertDx (pertDx g) (xb, 0)) (pertDx (pertDx h) (xb, 0)) +
        (pertP (pertP fk 0) 0 (yb, yb, xb, xb) - pertP (pertP fk 0) 1 (yb, yb, xb, xb)) *
          (pertDx g (xb, 0) * pertDx h (xb, 0)) ^ 2 := by
  rw [eq_F_xx hf hg hh η hp hx hy, pertFxxPrinted]
  simp only [pertRow]
  ring

/-- **Counterexample to the printed `F_xx` display** (Miao, p. 68). With `f = y'²`,
`g(x, σ) = h(x, σ) = x` and the degenerate shock `ε' = 0`, at `(x̄, ȳ) = (0, 0)`:
`F_xx(x̄, 0) = 2` (`f_{y'y'}g_x²h_x² = 2`), while the printed display (with `f_{y'y} = 0` in
place of `f_{y'y'}`) gives `0`. -/
theorem eq_F_xx_printed_false :
    ∃ (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 1 → ℝ),
      ContDiff ℝ 2 fk ∧ ContDiff ℝ 2 g ∧ ContDiff ℝ 2 h ∧ IsFiniteShock p ε ∧
      h (0, 0) = 0 ∧ g (0, 0) = 0 ∧
      pertDx (pertDx (pertF fk g h 0 p ε)) (0, 0) ≠
        pertFxxPrinted fk (0, 0, 0, 0) (pertDx g (0, 0)) (pertDx h (0, 0))
          (pertDx (pertDx g) (0, 0)) (pertDx (pertDx h) (0, 0)) := by
  set fk : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.1 ^ 2 with hfk
  set g : ℝ × ℝ → ℝ := fun q => q.1 with hg
  have hfk2 : ContDiff ℝ 2 fk := by fun_prop
  have hg2 : ContDiff ℝ 2 g := by fun_prop
  have hp : IsFiniteShock ![(1 : ℝ)] ![0] := ⟨fun i => by simp, by simp, by simp⟩
  have hgx : pertDx g (0, 0) = 1 :=
    pert_Dx_eq (hg2.differentiable (by norm_num)) (hasDerivAt_id (0 : ℝ))
  have hP0 : pertP fk 0 = fun v => 2 * v.1 := funext fun v =>
    pert_P_eq (hfk2.differentiable (by norm_num)) (φ := fun t => (v.1 + t) ^ 2)
      (fun t => by simp [hfk, pertE4])
      (by simpa using ((hasDerivAt_id' (0 : ℝ)).const_add v.1).fun_pow 2)
  have h00 : pertP (pertP fk 0) 0 (0, 0, 0, 0) = 2 := by
    rw [hP0]
    exact pert_P_eq (by fun_prop) (φ := fun t => 2 * t) (fun t => by simp [pertE4])
      (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2)
  have h01 : pertP (pertP fk 0) 1 (0, 0, 0, 0) = 0 := by
    rw [hP0]
    exact pert_P_eq (by fun_prop) (φ := fun _ => 0) (fun t => by simp [pertE4])
      (hasDerivAt_const 0 0)
  refine ⟨fk, g, g, ![1], ![0], hfk2, hg2, hg2, hp, rfl, rfl, fun H => ?_⟩
  rw [eq_F_xx_printed (xb := 0) (yb := 0) hfk2 hg2 hg2 0 hp rfl rfl, h00, h01, hgx] at H
  norm_num at H

/-! ### `F_σσ`: the missing `E[ε'²]` -/

/-- The display for `F_σσ(x̄, 0)` as printed (Miao, p. 69), with `I = 1`. -/
noncomputable def pertFssPrinted (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (v : ℝ × ℝ × ℝ × ℝ)
    (η gx gxx gss hss : ℝ) : ℝ :=
  pertP fk 0 v * gx * hss + pertP (pertP fk 0) 0 v * gx * η * gx * η +
    pertP (pertP fk 0) 2 v * η * gx * η + pertP fk 0 v * gxx * η * η + pertP fk 0 v * gss +
    pertP fk 1 v * gss + pertP fk 2 v * hss + pertP (pertP fk 2) 0 v * gx * η * η +
    pertP (pertP fk 2) 2 v * η * η

/-- Miao, p. 69: the true `F_σσ(x̄, 0)` (given `g_σ = h_σ = 0`) is the printed display plus
`(E[ε'²] − 1)η²c`, `c = pertCoefSS`; so the display is right iff `E[ε'²] = 1` or `ηc = 0`. -/
theorem eq_F_sigma_sigma_printed {fk : ℝ × ℝ × ℝ × ℝ → ℝ} {g h : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ 2 fk) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (η : ℝ) {N : ℕ}
    {p ε : Fin N → ℝ} (hp : IsFiniteShock p ε) {xb yb : ℝ} (hx : h (xb, 0) = xb)
    (hy : g (xb, 0) = yb) (hgs : pertDs g (xb, 0) = 0) (hhs : pertDs h (xb, 0) = 0) :
    pertDs (pertDs (pertF fk g h η p ε)) (xb, 0) =
      pertFssPrinted fk (yb, yb, xb, xb) η (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0))
          (pertDs (pertDs g) (xb, 0)) (pertDs (pertDs h) (xb, 0)) +
        (∑ i, p i * ε i ^ 2 - 1) * η ^ 2 *
          pertCoefSS fk (yb, yb, xb, xb) (pertDx g (xb, 0)) (pertDx (pertDx g) (xb, 0)) := by
  rw [eq_F_sigma_sigma hf hg hh η hp hx hy hgs hhs, pertFssPrinted, pertCoefSS]
  ring

/-- **Counterexample to the printed `F_σσ` display** (Miao, p. 69). With `f = x'²`, `g = h = 0`,
`η = 1` and `ε' = ±2` with probability `½` each (so `E[ε'²] = 4`), at `(x̄, ȳ) = (0, 0)`:
`F_σσ(x̄, 0) = f_{x'x'}η²E[ε'²] = 8`, while the printed display gives `f_{x'x'}η² = 2`. -/
theorem eq_F_sigma_sigma_printed_false :
    ∃ (fk : ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 2 → ℝ),
      ContDiff ℝ 2 fk ∧ ContDiff ℝ 2 g ∧ ContDiff ℝ 2 h ∧ IsFiniteShock p ε ∧
      h (0, 0) = 0 ∧ g (0, 0) = 0 ∧ pertDs g (0, 0) = 0 ∧ pertDs h (0, 0) = 0 ∧
      pertDs (pertDs (pertF fk g h 1 p ε)) (0, 0) ≠
        pertFssPrinted fk (0, 0, 0, 0) 1 (pertDx g (0, 0)) (pertDx (pertDx g) (0, 0))
          (pertDs (pertDs g) (0, 0)) (pertDs (pertDs h) (0, 0)) := by
  set fk : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.2.2.1 ^ 2 with hfk
  set g : ℝ × ℝ → ℝ := fun _ => 0 with hg
  have hfk2 : ContDiff ℝ 2 fk := by fun_prop
  have hg2 : ContDiff ℝ 2 g := contDiff_const
  have hp : IsFiniteShock ![(1 / 2 : ℝ), 1 / 2] ![2, -2] :=
    ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num,
      by simp [Fin.sum_univ_two]⟩
  obtain ⟨hgx, hgs⟩ := pert_partials_vanish (G := g) fun _ => rfl
  have hgx' : pertDx g = fun _ => 0 := funext hgx
  have hgxx : pertDx (pertDx g) (0, 0) = 0 := by
    rw [hgx']
    exact (pert_partials_vanish (G := fun _ : ℝ × ℝ => (0 : ℝ)) fun _ => rfl).1 _
  have hP2 : pertP fk 2 = fun v => 2 * v.2.2.1 := funext fun v =>
    pert_P_eq (hfk2.differentiable (by norm_num)) (φ := fun t => (v.2.2.1 + t) ^ 2)
      (fun t => by simp [hfk, pertE4])
      (by simpa using ((hasDerivAt_id' (0 : ℝ)).const_add v.2.2.1).fun_pow 2)
  have h22 : pertP (pertP fk 2) 2 (0, 0, 0, 0) = 2 := by
    rw [hP2]
    exact pert_P_eq (by fun_prop) (φ := fun t => 2 * t) (fun t => by simp [pertE4])
      (by simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2)
  refine ⟨fk, g, g, ![1 / 2, 1 / 2], ![2, -2], hfk2, hg2, hg2, hp, rfl, rfl, hgs _, hgs _,
    fun H => ?_⟩
  rw [eq_F_sigma_sigma_printed (xb := 0) (yb := 0) hfk2 hg2 hg2 1 hp rfl rfl (hgs _)
    (hgs _), pertCoefSS, hgx, hgxx, h22] at H
  simp [Fin.sum_univ_two] at H
  norm_num at H

/-! ### `g_σ = h_σ = 0` and `g_σx = h_σx = 0` are not forced when the determinant vanishes -/

/-- **`g_σ = h_σ = 0` is not forced** (Miao, p. 67). With `f₀ = y − y'` (`y_t = E_ty_{t+1}`),
`f₁ = x' − x` (`x_{t+1} = x_t + σε_{t+1}`), `η = 1`, `ε' = ±1` with probability `½`, the policy
`g(x, σ) = σ`, `h(x, σ) = x` solves (2.30), passes through the steady state `(0, 0)`, the
determinant of the `F_σ` system is `0`, and `g_σ(0, 0) = 1 ≠ 0`. -/
theorem g_sigma_not_forced :
    ∃ (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 2 → ℝ),
      IsPertSolution f g h 1 p ε ∧ h (0, 0) = 0 ∧ g (0, 0) = 0 ∧
      pertCoefA (f 0) (0, 0, 0, 0) * pertCoefB (f 1) (0, 0, 0, 0) (pertDx g (0, 0)) -
        pertCoefB (f 0) (0, 0, 0, 0) (pertDx g (0, 0)) * pertCoefA (f 1) (0, 0, 0, 0) = 0 ∧
      pertDs g (0, 0) ≠ 0 := by
  set f0 : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.2.1 - v.1 with hf0
  have hf0d : Differentiable ℝ f0 := by fun_prop
  have h00 : pertP f0 0 (0, 0, 0, 0) = -1 :=
    pert_P_eq hf0d (φ := fun t => -t) (fun t => by simp [hf0, pertE4])
      (hasDerivAt_id' (0 : ℝ)).neg
  have h01 : pertP f0 1 (0, 0, 0, 0) = 1 :=
    pert_P_eq hf0d (φ := fun t => t) (fun t => by simp [hf0, pertE4]) (hasDerivAt_id 0)
  have h02 : pertP f0 2 (0, 0, 0, 0) = 0 :=
    pert_P_eq hf0d (φ := fun _ => 0) (fun t => by simp [hf0, pertE4]) (hasDerivAt_const 0 0)
  have hgd : Differentiable ℝ fun q : ℝ × ℝ => q.2 := by fun_prop
  have hgx : pertDx (fun q : ℝ × ℝ => q.2) (0, 0) = 0 := pert_Dx_eq hgd (hasDerivAt_const 0 0)
  have hgs : pertDs (fun q : ℝ × ℝ => q.2) (0, 0) = 1 := pert_Ds_eq hgd (hasDerivAt_id 0)
  refine ⟨![f0, fun v => v.2.2.1 - v.2.2.2], fun q => q.2, fun q => q.1, ![1 / 2, 1 / 2],
    ![1, -1], ⟨fun k => ?_, by fun_prop, by fun_prop, ⟨fun i => by fin_cases i <;> norm_num,
      by simp [Fin.sum_univ_two]; norm_num, by simp [Fin.sum_univ_two]⟩, fun k q => ?_⟩, rfl,
      rfl, ?_, by rw [hgs]; norm_num⟩
  · fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hf0] <;> fun_prop
  · fin_cases k <;> simp [pertF, pertPhi, pertPsi, Fin.sum_univ_two, hf0]
  · simp only [Matrix.cons_val_zero, pertCoefA, pertCoefB, h00, h01, h02, hgx]
    ring

/-- **`g_σx = h_σx = 0` is not forced** (Miao, p. 69). Same `f`, `η`, shock as
`g_sigma_not_forced`, with the policy `g(x, σ) = σx`, `h(x, σ) = x`: it solves (2.30), passes
through `(0, 0)`, `g_σ = h_σ = 0` there, the determinant of the `F_σx` system is `0`, and
`g_σx(0, 0) = 1 ≠ 0`. -/
theorem g_sigma_x_not_forced :
    ∃ (f : Fin 2 → ℝ × ℝ × ℝ × ℝ → ℝ) (g h : ℝ × ℝ → ℝ) (p ε : Fin 2 → ℝ),
      IsPertSolution f g h 1 p ε ∧ h (0, 0) = 0 ∧ g (0, 0) = 0 ∧ pertDs g (0, 0) = 0 ∧
      pertDs h (0, 0) = 0 ∧
      pertCoefAx (f 0) (0, 0, 0, 0) (pertDx h (0, 0)) *
          pertCoefB (f 1) (0, 0, 0, 0) (pertDx g (0, 0)) -
        pertCoefB (f 0) (0, 0, 0, 0) (pertDx g (0, 0)) *
          pertCoefAx (f 1) (0, 0, 0, 0) (pertDx h (0, 0)) = 0 ∧
      pertDs (pertDx g) (0, 0) ≠ 0 := by
  set f0 : ℝ × ℝ × ℝ × ℝ → ℝ := fun v => v.2.1 - v.1 with hf0
  have hf0d : Differentiable ℝ f0 := by fun_prop
  have h00 : pertP f0 0 (0, 0, 0, 0) = -1 :=
    pert_P_eq hf0d (φ := fun t => -t) (fun t => by simp [hf0, pertE4])
      (hasDerivAt_id' (0 : ℝ)).neg
  have h01 : pertP f0 1 (0, 0, 0, 0) = 1 :=
    pert_P_eq hf0d (φ := fun t => t) (fun t => by simp [hf0, pertE4]) (hasDerivAt_id 0)
  have h02 : pertP f0 2 (0, 0, 0, 0) = 0 :=
    pert_P_eq hf0d (φ := fun _ => 0) (fun t => by simp [hf0, pertE4]) (hasDerivAt_const 0 0)
  set g : ℝ × ℝ → ℝ := fun q => q.2 * q.1 with hg
  have hgd : Differentiable ℝ g := by fun_prop
  have hhd : Differentiable ℝ fun q : ℝ × ℝ => q.1 := by fun_prop
  have hgx : pertDx g = fun q => q.2 := funext fun q =>
    pert_Dx_eq hgd (by simpa using (hasDerivAt_id q.1).const_mul q.2)
  have hgs : pertDs g (0, 0) = 0 :=
    pert_Ds_eq hgd (by simpa [hg] using (hasDerivAt_id (0 : ℝ)).mul_const (0 : ℝ))
  have hhx : pertDx (fun q : ℝ × ℝ => q.1) (0, 0) = 1 := pert_Dx_eq hhd (hasDerivAt_id 0)
  have hhs : pertDs (fun q : ℝ × ℝ => q.1) (0, 0) = 0 := pert_Ds_eq hhd (hasDerivAt_const 0 0)
  have hgsx : pertDs (pertDx g) (0, 0) = 1 := by
    rw [hgx]
    exact pert_Ds_eq (by fun_prop) (hasDerivAt_id 0)
  refine ⟨![f0, fun v => v.2.2.1 - v.2.2.2], g, fun q => q.1, ![1 / 2, 1 / 2],
    ![1, -1], ⟨fun k => ?_, by fun_prop, by fun_prop, ⟨fun i => by fin_cases i <;> norm_num,
      by simp [Fin.sum_univ_two]; norm_num, by simp [Fin.sum_univ_two]⟩, fun k q => ?_⟩, rfl,
      by simp [hg], hgs, hhs, ?_, by rw [hgsx]; norm_num⟩
  · fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one,
      Matrix.cons_val_fin_one, hf0] <;> fun_prop
  · fin_cases k
    · simp [pertF, pertPhi, pertPsi, Fin.sum_univ_two, hf0, hg]
      ring
    · simp [pertF, pertPhi, pertPsi, Fin.sum_univ_two, hf0, hg]
  · simp only [Matrix.cons_val_zero, pertCoefAx, pertCoefB, h00, h01, h02, hgx, hhx]
    ring

end Miao.RationalExpectations

set_option linter.style.longLine false
#print axioms Miao.RationalExpectations.IsSolution
#print axioms Miao.RationalExpectations.IsRegular
#print axioms Miao.RationalExpectations.EventuallyConst
#print axioms Miao.RationalExpectations.IsStableSeq
#print axioms Miao.RationalExpectations.IsSteadyStateOf
#print axioms Miao.RationalExpectations.IsAsympStable
#print axioms Miao.RationalExpectations.basin
#print axioms Miao.RationalExpectations.IsGloballyStable
#print axioms Miao.RationalExpectations.IsStableMatrix
#print axioms Miao.RationalExpectations.isGloballyStable_iff_basin
#print axioms Miao.RationalExpectations.isAsympStable_iff_basin
#print axioms Miao.RationalExpectations.isStableSeq_iff_bddAbove
#print axioms Miao.RationalExpectations.tendsto_zero_of_le_rec
#print axioms Miao.RationalExpectations.tendsto_zero_of_rec
#print axioms Miao.RationalExpectations.triangular_step
#print axioms Miao.RationalExpectations.triangular_invariant
#print axioms Miao.RationalExpectations.triangular_tendsto_iff
#print axioms Miao.RationalExpectations.mclm
#print axioms Miao.RationalExpectations.mclm_apply
#print axioms Miao.RationalExpectations.norm_mulVec_le
#print axioms Miao.RationalExpectations.norm_mclm_mul_le
#print axioms Miao.RationalExpectations.tendsto_norm_mclm_pow
#print axioms Miao.RationalExpectations.summable_of_tendsto_zero
#print axioms Miao.RationalExpectations.diag_mul_of_upper
#print axioms Miao.RationalExpectations.upper_inv
#print axioms Miao.RationalExpectations.diag_inv_of_upper
#print axioms Miao.RationalExpectations.summable_norm_pow_of_triangular
#print axioms Miao.RationalExpectations.stableSubspace
#print axioms Miao.RationalExpectations.unstableSubspace
#print axioms Miao.RationalExpectations.convSubspace
#print axioms Miao.RationalExpectations.mem_convSubspace
#print axioms Miao.RationalExpectations.tendsto_of_mem_maxGenEigenspace
#print axioms Miao.RationalExpectations.not_tendsto_of_eigen
#print axioms Miao.RationalExpectations.stable_le_conv
#print axioms Miao.RationalExpectations.stable_sup_unstable
#print axioms Miao.RationalExpectations.disjoint_stable_unstable
#print axioms Miao.RationalExpectations.unstable_invariant
#print axioms Miao.RationalExpectations.tendsto_iff_mem_stable
#print axioms Miao.RationalExpectations.stable_eq_top
#print axioms Miao.RationalExpectations.cplx
#print axioms Miao.RationalExpectations.cplx_sub
#print axioms Miao.RationalExpectations.cplx_add
#print axioms Miao.RationalExpectations.tendsto_cplx_iff
#print axioms Miao.RationalExpectations.cplxEnd
#print axioms Miao.RationalExpectations.cplxEnd_pow_cplx
#print axioms Miao.RationalExpectations.hasEigenvalue_cplxEnd_iff
#print axioms Miao.RationalExpectations.finrank_biSup_maxGenEigenspace
#print axioms Miao.RationalExpectations.finrank_stableSubspace
#print axioms Miao.RationalExpectations.conjV
#print axioms Miao.RationalExpectations.conjV_conjV
#print axioms Miao.RationalExpectations.conjV_add
#print axioms Miao.RationalExpectations.conjV_sub
#print axioms Miao.RationalExpectations.conjV_smul
#print axioms Miao.RationalExpectations.conjV_zero
#print axioms Miao.RationalExpectations.conjV_cplx
#print axioms Miao.RationalExpectations.eq_cplx_re
#print axioms Miao.RationalExpectations.cplxEnd_conjV
#print axioms Miao.RationalExpectations.pow_sub_conjV
#print axioms Miao.RationalExpectations.conjV_mem_maxGenEigenspace
#print axioms Miao.RationalExpectations.conjV_mem_biSup
#print axioms Miao.RationalExpectations.conjV_mem_stable
#print axioms Miao.RationalExpectations.conjV_mem_unstable
#print axioms Miao.RationalExpectations.cplxL
#print axioms Miao.RationalExpectations.stableR
#print axioms Miao.RationalExpectations.unstableR
#print axioms Miao.RationalExpectations.mem_stableR
#print axioms Miao.RationalExpectations.mem_unstableR
#print axioms Miao.RationalExpectations.mem_stableR_iff
#print axioms Miao.RationalExpectations.cplx_mulVec
#print axioms Miao.RationalExpectations.stableR_invariant
#print axioms Miao.RationalExpectations.unstableR_invariant
#print axioms Miao.RationalExpectations.isCompl_stableR_unstableR
#print axioms Miao.RationalExpectations.linearIndependent_cplx
#print axioms Miao.RationalExpectations.finrank_le_of_cplx
#print axioms Miao.RationalExpectations.finrank_stableR
#print axioms Miao.RationalExpectations.unstableR_ker
#print axioms Miao.RationalExpectations.uniform_bound_of_basis
#print axioms Miao.RationalExpectations.exists_bound_of_tendsto
#print axioms Miao.RationalExpectations.mem_maxGen_smul
#print axioms Miao.RationalExpectations.projS
#print axioms Miao.RationalExpectations.projU
#print axioms Miao.RationalExpectations.projS_add_projU
#print axioms Miao.RationalExpectations.projS_mem
#print axioms Miao.RationalExpectations.projU_mem
#print axioms Miao.RationalExpectations.projS_of_mem
#print axioms Miao.RationalExpectations.projS_of_mem_unstable
#print axioms Miao.RationalExpectations.projU_of_mem
#print axioms Miao.RationalExpectations.projU_of_mem_stable
#print axioms Miao.RationalExpectations.projS_mulVec
#print axioms Miao.RationalExpectations.projU_mulVec
#print axioms Miao.RationalExpectations.pow_mulVec_mem_stableR
#print axioms Miao.RationalExpectations.tendsto_scaled_of_stable
#print axioms Miao.RationalExpectations.scaled_pow_cplx
#print axioms Miao.RationalExpectations.stable_bound
#print axioms Miao.RationalExpectations.isStableMatrix_iff_roots
#print axioms Miao.RationalExpectations.tendsto_of_isStableMatrix
#print axioms Miao.RationalExpectations.isStableMatrix_of_tendsto
#print axioms Miao.RationalExpectations.isStableMatrix_iff_tendsto
#print axioms Miao.RationalExpectations.HasGeomDecay
#print axioms Miao.RationalExpectations.hasGeomDecay_of_isStableMatrix
#print axioms Miao.RationalExpectations.isStableMatrix_inv
#print axioms Miao.RationalExpectations.footnote_2
#print axioms Miao.RationalExpectations.isRegular_of_isUnit_det
#print axioms Miao.RationalExpectations.example_scalar_not_regular
#print axioms Miao.RationalExpectations.example_scalar_no_solution
#print axioms Miao.RationalExpectations.remark_nonregular_no_solution
#print axioms Miao.RationalExpectations.remark_nonregular_counterexample
#print axioms Miao.RationalExpectations.eq_1_21
#print axioms Miao.RationalExpectations.eq_1_21_solution
#print axioms Miao.RationalExpectations.eq_1_21_steadyState
#print axioms Miao.RationalExpectations.isSteadyStateOf_of_not_mem_range
#print axioms Miao.RationalExpectations.isStableSeq_iff_exists_le
#print axioms Miao.RationalExpectations.exists_mulVec_bound
#print axioms Miao.RationalExpectations.bounded_mulVec
#print axioms Miao.RationalExpectations.norm_sum_type_le
#print axioms Miao.RationalExpectations.norm_comp_inl_le
#print axioms Miao.RationalExpectations.norm_comp_inr_le
#print axioms Miao.RationalExpectations.backward_sol_eq
#print axioms Miao.RationalExpectations.bounded_backward
#print axioms Miao.RationalExpectations.summable_geom_series
#print axioms Miao.RationalExpectations.mulVec_tsum_rs
#print axioms Miao.RationalExpectations.tsum_geom_series_succ
#print axioms Miao.RationalExpectations.eq_zero_of_bounded_orbit
#print axioms Miao.RationalExpectations.IsRealBlockSplit
#print axioms Miao.RationalExpectations.blockDiag_mulVec_inl
#print axioms Miao.RationalExpectations.blockDiag_mulVec_inr
#print axioms Miao.RationalExpectations.mulVec_comp_inl
#print axioms Miao.RationalExpectations.mulVec_comp_inr
#print axioms Miao.RationalExpectations.IsRealBlockSplit.mul_R
#print axioms Miao.RationalExpectations.card_add_card_of_inv
#print axioms Miao.RationalExpectations.IsRealBlockSplit.isUnit_one_sub
#print axioms Miao.RationalExpectations.eigen_transport
#print axioms Miao.RationalExpectations.exists_real_block_split
#print axioms Miao.RationalExpectations.eq_1_22
#print axioms Miao.RationalExpectations.exists_sol_rec
#print axioms Miao.RationalExpectations.sol_rec_unique
#print axioms Miao.RationalExpectations.exists_unique_solution
#print axioms Miao.RationalExpectations.eq_1_24
#print axioms Miao.RationalExpectations.eq_1_25
#print axioms Miao.RationalExpectations.isUnit_sub_det
#print axioms Miao.RationalExpectations.xbar_eq
#print axioms Miao.RationalExpectations.theorem_1_4_1
#print axioms Miao.RationalExpectations.forwardU
#print axioms Miao.RationalExpectations.forwardU_rec
#print axioms Miao.RationalExpectations.forwardU_bounded
#print axioms Miao.RationalExpectations.forwardU_unique
#print axioms Miao.RationalExpectations.split_rec_inl
#print axioms Miao.RationalExpectations.split_rec_inr
#print axioms Miao.RationalExpectations.bounded_of_split
#print axioms Miao.RationalExpectations.eq_1_29
#print axioms Miao.RationalExpectations.eq_1_30
#print axioms Miao.RationalExpectations.eq_1_31
#print axioms Miao.RationalExpectations.eq_1_32
#print axioms Miao.RationalExpectations.bk_exists
#print axioms Miao.RationalExpectations.bk_unique
#print axioms Miao.RationalExpectations.theorem_1_4_2
#print axioms Miao.RationalExpectations.blocks_of_inv
#print axioms Miao.RationalExpectations.rks_inv
#print axioms Miao.RationalExpectations.puy_inv_of_rks
#print axioms Miao.RationalExpectations.bk_order_iff
#print axioms Miao.RationalExpectations.eq_1_33
#print axioms Miao.RationalExpectations.corollary_1_4_1
#print axioms Miao.RationalExpectations.eq_1_34
#print axioms Miao.RationalExpectations.stable_initial_iff
#print axioms Miao.RationalExpectations.stableArm
#print axioms Miao.RationalExpectations.mem_stableArm
#print axioms Miao.RationalExpectations.stableArm_iff
#print axioms Miao.RationalExpectations.finrank_stableArm
#print axioms Miao.RationalExpectations.stable_initial_translate
#print axioms Miao.RationalExpectations.remark_unit_root
#print axioms Miao.RationalExpectations.IsGenEigenvector
#print axioms Miao.RationalExpectations.IsGenEigenvalue
#print axioms Miao.RationalExpectations.genEigenvalues
#print axioms Miao.RationalExpectations.isGenEigenvalue_iff_det
#print axioms Miao.RationalExpectations.det_ne_zero_of_unitary
#print axioms Miao.RationalExpectations.conj_lincomb
#print axioms Miao.RationalExpectations.det_conj_lincomb
#print axioms Miao.RationalExpectations.upper_lincomb
#print axioms Miao.RationalExpectations.det_upper_lincomb
#print axioms Miao.RationalExpectations.diag_ne_zero_of_regular
#print axioms Miao.RationalExpectations.genEigenvalues_eq_diag
#print axioms Miao.RationalExpectations.exists_eigenPair
#print axioms Miao.RationalExpectations.exists_unitary_col
#print axioms Miao.RationalExpectations.deflate
#print axioms Miao.RationalExpectations.det_of_col_zero
#print axioms Miao.RationalExpectations.blockOne
#print axioms Miao.RationalExpectations.blockOne_mul_zero
#print axioms Miao.RationalExpectations.blockOne_mul_succ
#print axioms Miao.RationalExpectations.mul_blockOne_zero
#print axioms Miao.RationalExpectations.mul_blockOne_succ
#print axioms Miao.RationalExpectations.blockOne_mul_blockOne
#print axioms Miao.RationalExpectations.star_blockOne
#print axioms Miao.RationalExpectations.blockOne_one
#print axioms Miao.RationalExpectations.blockOne_mem
#print axioms Miao.RationalExpectations.assemble_apply
#print axioms Miao.RationalExpectations.assemble_upper
#print axioms Miao.RationalExpectations.proportional_of_cross
#print axioms Miao.RationalExpectations.ScaleInvariant
#print axioms Miao.RationalExpectations.exists_qz_ordered
#print axioms Miao.RationalExpectations.theorem_1_4_4
#print axioms Miao.RationalExpectations.scaleInvariant_stable
#print axioms Miao.RationalExpectations.theorem_1_4_4_stable
#print axioms Miao.RationalExpectations.norm_mulVec_le_sum
#print axioms Miao.RationalExpectations.isStableSeq_of_le
#print axioms Miao.RationalExpectations.IsStableSeq.bound
#print axioms Miao.RationalExpectations.IsStableSeq.mulVec
#print axioms Miao.RationalExpectations.fwdSum
#print axioms Miao.RationalExpectations.summable_fwd
#print axioms Miao.RationalExpectations.norm_fwdSum_le
#print axioms Miao.RationalExpectations.fwdSum_rec
#print axioms Miao.RationalExpectations.eq_fwdSum
#print axioms Miao.RationalExpectations.isStableSeq_of_rec
#print axioms Miao.RationalExpectations.IsStableSeq.add
#print axioms Miao.RationalExpectations.IsStableSeq.sub
#print axioms Miao.RationalExpectations.IsStableSeq.shift
#print axioms Miao.RationalExpectations.norm_comp_le
#print axioms Miao.RationalExpectations.IsStableSeq.comp
#print axioms Miao.RationalExpectations.isStableSeq_append
#print axioms Miao.RationalExpectations.upper_castAdd
#print axioms Miao.RationalExpectations.upper_natAdd
#print axioms Miao.RationalExpectations.mulVec_castAdd
#print axioms Miao.RationalExpectations.mulVec_natAdd
#print axioms Miao.RationalExpectations.eq_1_36
#print axioms Miao.RationalExpectations.solve_fwd
#print axioms Miao.RationalExpectations.eq_1_38
#print axioms Miao.RationalExpectations.det_S11_ne_zero
#print axioms Miao.RationalExpectations.det_T22_ne_zero
#print axioms Miao.RationalExpectations.summable_Ms
#print axioms Miao.RationalExpectations.summable_Mu
#print axioms Miao.RationalExpectations.klein_core
#print axioms Miao.RationalExpectations.klein_homog
#print axioms Miao.RationalExpectations.eq_1_37
#print axioms Miao.RationalExpectations.eq_1_39_40
#print axioms Miao.RationalExpectations.isSolution_iff_transformed
#print axioms Miao.RationalExpectations.diag_off_circle
#print axioms Miao.RationalExpectations.theorem_1_4_5
#print axioms Miao.RationalExpectations.det_sub_ne_zero
#print axioms Miao.RationalExpectations.corollary_1_4_1_singular
#print axioms Miao.RationalExpectations.map_ofReal_mulVec
#print axioms Miao.RationalExpectations.norm_ofReal_vec
#print axioms Miao.RationalExpectations.isSolution_ofReal_iff
#print axioms Miao.RationalExpectations.theorem_1_4_5_real
#print axioms Miao.RationalExpectations.eq_s0
#print axioms Miao.RationalExpectations.remark_augmented
#print axioms Miao.RationalExpectations.remark_u_eq_zero
#print axioms Miao.RationalExpectations.eq_1_37_printed_false
#print axioms Miao.RationalExpectations.caganA
#print axioms Miao.RationalExpectations.caganB
#print axioms Miao.RationalExpectations.caganC
#print axioms Miao.RationalExpectations.example_cagan_iff
#print axioms Miao.RationalExpectations.example_cagan_det
#print axioms Miao.RationalExpectations.example_cagan_regular
#print axioms Miao.RationalExpectations.example_cagan_genEigenvalues
#print axioms Miao.RationalExpectations.example_cagan_genEigenvalues_zero
#print axioms Miao.RationalExpectations.CondExpSystem
#print axioms Miao.RationalExpectations.CondExpSystem.mk
#print axioms Miao.RationalExpectations.CondExpSystem.E
#print axioms Miao.RationalExpectations.CondExpSystem.norm_le
#print axioms Miao.RationalExpectations.CondExpSystem.tower_le
#print axioms Miao.RationalExpectations.CondExpSystem.tower_ge
#print axioms Miao.RationalExpectations.CondExpSystem.tower_le_apply
#print axioms Miao.RationalExpectations.CondExpSystem.tower_ge_apply
#print axioms Miao.RationalExpectations.CondExpSystem.idem
#print axioms Miao.RationalExpectations.CondExpSystem.norm_apply_le
#print axioms Miao.RationalExpectations.IsAdaptedV
#print axioms Miao.RationalExpectations.IsStableProc
#print axioms Miao.RationalExpectations.matAct
#print axioms Miao.RationalExpectations.Evec
#print axioms Miao.RationalExpectations.IsRESolution
#print axioms Miao.RationalExpectations.IsPredeterminedBK
#print axioms Miao.RationalExpectations.Evec_matAct
#print axioms Miao.RationalExpectations.matAct_add
#print axioms Miao.RationalExpectations.matAct_mul
#print axioms Miao.RationalExpectations.matAct_one
#print axioms Miao.RationalExpectations.condExpL1_norm_apply_le
#print axioms Miao.RationalExpectations.condExpL1_ae_eq_condExp
#print axioms Miao.RationalExpectations.condExpL1_tower_le
#print axioms Miao.RationalExpectations.condExpL1_tower_ge
#print axioms Miao.RationalExpectations.condExpL1CLMK
#print axioms Miao.RationalExpectations.condExpL1CLMK_apply
#print axioms Miao.RationalExpectations.condExpSystemL1
#print axioms Miao.RationalExpectations.condExpSystemL1_E_apply
#print axioms Miao.RationalExpectations.condExpSystemL1_real
#print axioms Miao.RationalExpectations.condExpSystemL1_complex
#print axioms Miao.RationalExpectations.condExpSystemL1_ae_eq
#print axioms Miao.RationalExpectations.condExpL1_eq_self_iff
#print axioms Miao.RationalExpectations.condExpL1_eq_self_iff_exists
#print axioms Miao.RationalExpectations.condExpL1_isAdaptedV_iff
#print axioms Miao.RationalExpectations.l1_norm_eq_integral_abs
#print axioms Miao.RationalExpectations.l1_isStableProc_iff
#print axioms Miao.RationalExpectations.l1_norm_eq_integral_norm_complex
#print axioms Miao.RationalExpectations.example_2_1_1
#print axioms Miao.RationalExpectations.example_2_1_2
#print axioms Miao.RationalExpectations.example_2_1_3
#print axioms Miao.RationalExpectations.var_pow_entry_le
#print axioms Miao.RationalExpectations.var_l1
#print axioms Miao.RationalExpectations.var_l1_nonneg
#print axioms Miao.RationalExpectations.var_sandwich_apply
#print axioms Miao.RationalExpectations.var_sandwich_le
#print axioms Miao.RationalExpectations.var_lyapMap
#print axioms Miao.RationalExpectations.var_lyapSol
#print axioms Miao.RationalExpectations.var_lyap_summable
#print axioms Miao.RationalExpectations.var_lyap_iterate
#print axioms Miao.RationalExpectations.lyap_iterate_tendsto
#print axioms Miao.RationalExpectations.var_lyapMap_apply
#print axioms Miao.RationalExpectations.var_lyapMap_continuous
#print axioms Miao.RationalExpectations.lyap_fixed
#print axioms Miao.RationalExpectations.lyap_unique
#print axioms Miao.RationalExpectations.var_ShockMDS
#print axioms Miao.RationalExpectations.var_ShockMDS.mk
#print axioms Miao.RationalExpectations.var_ShockMDS.memLp
#print axioms Miao.RationalExpectations.var_ShockMDS.meas
#print axioms Miao.RationalExpectations.var_ShockMDS.mds
#print axioms Miao.RationalExpectations.var_ShockMDS.cvar
#print axioms Miao.RationalExpectations.var_Model
#print axioms Miao.RationalExpectations.var_Model.mk
#print axioms Miao.RationalExpectations.var_Model.eq21
#print axioms Miao.RationalExpectations.var_Model.z0_memLp
#print axioms Miao.RationalExpectations.var_Model.z0_meas
#print axioms Miao.RationalExpectations.var_Model.shock
#print axioms Miao.RationalExpectations.var_mean
#print axioms Miao.RationalExpectations.var_mom
#print axioms Miao.RationalExpectations.var_rec_apply
#print axioms Miao.RationalExpectations.var_Model.z_memLp
#print axioms Miao.RationalExpectations.var_Model.z_meas
#print axioms Miao.RationalExpectations.var_cross_zero
#print axioms Miao.RationalExpectations.var_mean_eps_zero
#print axioms Miao.RationalExpectations.var_mom_eps
#print axioms Miao.RationalExpectations.var_integral_sum_mul
#print axioms Miao.RationalExpectations.var_integral_mul_sum
#print axioms Miao.RationalExpectations.var_mean_rec
#print axioms Miao.RationalExpectations.var_mean_eq
#print axioms Miao.RationalExpectations.var_mean_tendsto_zero
#print axioms Miao.RationalExpectations.var_stack
#print axioms Miao.RationalExpectations.var_rec_stack
#print axioms Miao.RationalExpectations.var_rec_stack_apply
#print axioms Miao.RationalExpectations.var_stack_memLp
#print axioms Miao.RationalExpectations.var_mom_rec
#print axioms Miao.RationalExpectations.var_mom_iterate
#print axioms Miao.RationalExpectations.var_mom_tendsto
#print axioms Miao.RationalExpectations.var_autocov
#print axioms Miao.RationalExpectations.var_IsCovStationary
#print axioms Miao.RationalExpectations.definition_2_1_1_not_symmetric
#print axioms Miao.RationalExpectations.var_stationary_moments
#print axioms Miao.RationalExpectations.var_stationary_of_initial
#print axioms Miao.RationalExpectations.var_ma_shift
#print axioms Miao.RationalExpectations.var_ma
#print axioms Miao.RationalExpectations.var_ma_initial_tendsto
#print axioms Miao.RationalExpectations.var_impulse_response
#print axioms Miao.RationalExpectations.var_IsWhiteNoise
#print axioms Miao.RationalExpectations.var_integral_abs_le_sqrt
#print axioms Miao.RationalExpectations.whiteNoise_stable
#print axioms Miao.RationalExpectations.whiteNoise_stable_L1
#print axioms Miao.RationalExpectations.mds_whiteNoise
#print axioms Miao.RationalExpectations.vex_unif
#print axioms Miao.RationalExpectations.vex_P
#print axioms Miao.RationalExpectations.vex_coord_measurable
#print axioms Miao.RationalExpectations.vex_integral_coord
#print axioms Miao.RationalExpectations.vex_integral_coord2
#print axioms Miao.RationalExpectations.vex_memLp
#print axioms Miao.RationalExpectations.vex_coord_meas_piLE
#print axioms Miao.RationalExpectations.vex_indep
#print axioms Miao.RationalExpectations.vex_condExp
#print axioms Miao.RationalExpectations.vex_f
#print axioms Miao.RationalExpectations.vex_g
#print axioms Miao.RationalExpectations.vex_F
#print axioms Miao.RationalExpectations.vex_wn
#print axioms Miao.RationalExpectations.vex_sum_F
#print axioms Miao.RationalExpectations.vex_sum_FF
#print axioms Miao.RationalExpectations.vex_sum_FG
#print axioms Miao.RationalExpectations.vex_g_ne_zero
#print axioms Miao.RationalExpectations.whiteNoise_example
#print axioms Miao.RationalExpectations.whiteNoise_not_mds
#print axioms Miao.RationalExpectations.vex_wn_adapted
#print axioms Miao.RationalExpectations.vex_sh
#print axioms Miao.RationalExpectations.vex_sh_mds
#print axioms Miao.RationalExpectations.vex_zero_stable
#print axioms Miao.RationalExpectations.vex_model
#print axioms Miao.RationalExpectations.vex_lyapSol_zero
#print axioms Miao.RationalExpectations.vex_a
#print axioms Miao.RationalExpectations.vex_b
#print axioms Miao.RationalExpectations.vex_a_sums
#print axioms Miao.RationalExpectations.vex_b_sums
#print axioms Miao.RationalExpectations.stationary_law_not_unique
#print axioms Miao.RationalExpectations.sre_IsAdapted
#print axioms Miao.RationalExpectations.sre_IsBounded
#print axioms Miao.RationalExpectations.sre_isStableProc_iff
#print axioms Miao.RationalExpectations.sre_isAdaptedV_iff
#print axioms Miao.RationalExpectations.sre_adapted_succ
#print axioms Miao.RationalExpectations.sre_adapted_le
#print axioms Miao.RationalExpectations.sre_shiftSys
#print axioms Miao.RationalExpectations.sre_shiftSys_E
#print axioms Miao.RationalExpectations.sre_lagInv
#print axioms Miao.RationalExpectations.sre_lag
#print axioms Miao.RationalExpectations.sre_lagE
#print axioms Miao.RationalExpectations.sre_lagE_self
#print axioms Miao.RationalExpectations.sre_lagInv_zero
#print axioms Miao.RationalExpectations.sre_lagInv_lagInv
#print axioms Miao.RationalExpectations.sre_lag_lag
#print axioms Miao.RationalExpectations.sre_lag_form
#print axioms Miao.RationalExpectations.sre_iter
#print axioms Miao.RationalExpectations.sre_bubble_bounded_zero
#print axioms Miao.RationalExpectations.sre_unique_of_bounded
#print axioms Miao.RationalExpectations.sre_fwd
#print axioms Miao.RationalExpectations.sre_inv_abs_lt_one
#print axioms Miao.RationalExpectations.sre_fwd_term_le
#print axioms Miao.RationalExpectations.sre_fwd_summable
#print axioms Miao.RationalExpectations.sre_fwd_bound
#print axioms Miao.RationalExpectations.sre_fwd_isBounded
#print axioms Miao.RationalExpectations.sre_fwd_adapted
#print axioms Miao.RationalExpectations.sre_fwd_rec
#print axioms Miao.RationalExpectations.eq_2_3
#print axioms Miao.RationalExpectations.eq_2_3_unique
#print axioms Miao.RationalExpectations.eq_2_4_of_particular
#print axioms Miao.RationalExpectations.eq_2_4
#print axioms Miao.RationalExpectations.eq_2_4_every
#print axioms Miao.RationalExpectations.sre_Transversality
#print axioms Miao.RationalExpectations.eq_2_5_of_bounded
#print axioms Miao.RationalExpectations.sre_bubble_tvc_zero
#print axioms Miao.RationalExpectations.eq_2_5_bubble_fails
#print axioms Miao.RationalExpectations.sre_unique_of_tvc
#print axioms Miao.RationalExpectations.eq_2_5_rules_out_bubbles
#print axioms Miao.RationalExpectations.sre_fwd_ar1
#print axioms Miao.RationalExpectations.example_2_2_1_Ed
#print axioms Miao.RationalExpectations.example_2_2_1_fundamental
#print axioms Miao.RationalExpectations.example_2_2_1_general
#print axioms Miao.RationalExpectations.sre_bounded_of_rec
#print axioms Miao.RationalExpectations.sre_smul_isBounded
#print axioms Miao.RationalExpectations.sre_smul_isAdapted
#print axioms Miao.RationalExpectations.sre_IsSol26
#print axioms Miao.RationalExpectations.sre_second
#print axioms Miao.RationalExpectations.eq_2_9
#print axioms Miao.RationalExpectations.sre_second_adapted
#print axioms Miao.RationalExpectations.eq_2_6_solution
#print axioms Miao.RationalExpectations.eq_2_6_unique
#print axioms Miao.RationalExpectations.sre_IsSol210
#print axioms Miao.RationalExpectations.eq_2_10_reduce
#print axioms Miao.RationalExpectations.sre_force210
#print axioms Miao.RationalExpectations.sre_force210_adapted
#print axioms Miao.RationalExpectations.sre_force210_bounded
#print axioms Miao.RationalExpectations.sre_sol210
#print axioms Miao.RationalExpectations.sre_sol210_adapted
#print axioms Miao.RationalExpectations.sre_sol210_E
#print axioms Miao.RationalExpectations.eq_2_10_solution
#print axioms Miao.RationalExpectations.eq_2_10_unique
#print axioms Miao.RationalExpectations.sre_sunspot
#print axioms Miao.RationalExpectations.eq_2_10_indeterminate
#print axioms Miao.RationalExpectations.sre_uc
#print axioms Miao.RationalExpectations.sre_uc_adapted
#print axioms Miao.RationalExpectations.uc_iff
#print axioms Miao.RationalExpectations.uc_sufficient
#print axioms Miao.RationalExpectations.uc_necessary
#print axioms Miao.RationalExpectations.uc_denominator_ne_zero
#print axioms Miao.RationalExpectations.uc_stable_root
#print axioms Miao.RationalExpectations.uc_eq_lag_solution
#print axioms Miao.RationalExpectations.example_2_2_1_coin
#print axioms Miao.RationalExpectations.example_2_2_1_bubble
#print axioms Miao.RationalExpectations.example_2_2_1_bubble_L1
#print axioms Miao.RationalExpectations.ex1_IsSol
#print axioms Miao.RationalExpectations.ex_1_iff
#print axioms Miao.RationalExpectations.ex_1_b_gt_one
#print axioms Miao.RationalExpectations.ex_1_unique
#print axioms Miao.RationalExpectations.ex_1_Em
#print axioms Miao.RationalExpectations.ex_1_solution
#print axioms Miao.RationalExpectations.ex_1_solution_eq_fwd
#print axioms Miao.RationalExpectations.ex_1
#print axioms Miao.RationalExpectations.ex_1_solution_iff
#print axioms Miao.RationalExpectations.ex_1_rho_one_martingale
#print axioms Miao.RationalExpectations.ex_1_rho_one_growth
#print axioms Miao.RationalExpectations.ex_1_rho_one
#print axioms Miao.RationalExpectations.bkS_matAct_sub
#print axioms Miao.RationalExpectations.bkS_matAct_neg
#print axioms Miao.RationalExpectations.bkS_matAct_zero
#print axioms Miao.RationalExpectations.bkS_matAct_zero_left
#print axioms Miao.RationalExpectations.bkS_matAct_smul
#print axioms Miao.RationalExpectations.bkS_matAct_sum
#print axioms Miao.RationalExpectations.bkS_matAct_add_left
#print axioms Miao.RationalExpectations.bkS_matAct_sub_left
#print axioms Miao.RationalExpectations.bkS_matAct_pow_succ
#print axioms Miao.RationalExpectations.bkS_matCLM
#print axioms Miao.RationalExpectations.bkS_matCLM_apply
#print axioms Miao.RationalExpectations.bkS_matAct_hasSum
#print axioms Miao.RationalExpectations.bkS_matAct_real
#print axioms Miao.RationalExpectations.bkS_norm_matAct_le
#print axioms Miao.RationalExpectations.bkS_matAct_bound
#print axioms Miao.RationalExpectations.bkS_geom_decay
#print axioms Miao.RationalExpectations.bkS_ECLM
#print axioms Miao.RationalExpectations.bkS_ECLM_apply
#print axioms Miao.RationalExpectations.bkS_Evec_hasSum
#print axioms Miao.RationalExpectations.bkS_Evec_add
#print axioms Miao.RationalExpectations.bkS_Evec_sub
#print axioms Miao.RationalExpectations.bkS_Evec_neg
#print axioms Miao.RationalExpectations.bkS_Evec_zero
#print axioms Miao.RationalExpectations.bkS_Evec_smul
#print axioms Miao.RationalExpectations.bkS_Evec_sumElim
#print axioms Miao.RationalExpectations.bkS_Evec_tower_le
#print axioms Miao.RationalExpectations.bkS_Evec_tower_ge
#print axioms Miao.RationalExpectations.bkS_Evec_idem
#print axioms Miao.RationalExpectations.bkS_Evec_of_le
#print axioms Miao.RationalExpectations.bkS_norm_Evec_le
#print axioms Miao.RationalExpectations.bkS_isAdaptedV_iff
#print axioms Miao.RationalExpectations.bkS_isStableProc_iff
#print axioms Miao.RationalExpectations.bkS_stable_Evec
#print axioms Miao.RationalExpectations.bkS_stable_shift
#print axioms Miao.RationalExpectations.bkS_stable_matAct
#print axioms Miao.RationalExpectations.bkS_stable_add
#print axioms Miao.RationalExpectations.bkS_summable_geom
#print axioms Miao.RationalExpectations.bkS_fwd
#print axioms Miao.RationalExpectations.eq_2_12
#print axioms Miao.RationalExpectations.bkS_fwd_adapted
#print axioms Miao.RationalExpectations.bkS_fwd_bound
#print axioms Miao.RationalExpectations.bkS_fwd_rec
#print axioms Miao.RationalExpectations.bkS_fwd_unique
#print axioms Miao.RationalExpectations.bkS_jump_unique
#print axioms Miao.RationalExpectations.eq_2_11_iff
#print axioms Miao.RationalExpectations.bkS_regular_of_det
#print axioms Miao.RationalExpectations.bkS_add_comp
#print axioms Miao.RationalExpectations.bkS_sub_comp
#print axioms Miao.RationalExpectations.bkS_Evec_comp
#print axioms Miao.RationalExpectations.bkS_comp_inl
#print axioms Miao.RationalExpectations.bkS_comp_inr
#print axioms Miao.RationalExpectations.bkS_blockDiag_inl
#print axioms Miao.RationalExpectations.bkS_blockDiag_inr
#print axioms Miao.RationalExpectations.bkS_split_inl
#print axioms Miao.RationalExpectations.bkS_split_inr
#print axioms Miao.RationalExpectations.bkS_norm_comp_inl_le
#print axioms Miao.RationalExpectations.bkS_norm_comp_inr_le
#print axioms Miao.RationalExpectations.bkS_norm_sum_type_le
#print axioms Miao.RationalExpectations.bkS_sumElim_eta
#print axioms Miao.RationalExpectations.bkS_backward_eq
#print axioms Miao.RationalExpectations.bkS_bounded_backward
#print axioms Miao.RationalExpectations.bkS_IsStableSol
#print axioms Miao.RationalExpectations.bkS_u_rec
#print axioms Miao.RationalExpectations.bkS_u_eq_fwd
#print axioms Miao.RationalExpectations.bkS_policy
#print axioms Miao.RationalExpectations.bkS_unique
#print axioms Miao.RationalExpectations.bkS_exists
#print axioms Miao.RationalExpectations.theorem_1_4_2_stoch
#print axioms Miao.RationalExpectations.bkS_k0_adapted
#print axioms Miao.RationalExpectations.bkS_trivial
#print axioms Miao.RationalExpectations.bkS_Evec_trivial
#print axioms Miao.RationalExpectations.certainty_equivalence
#print axioms Miao.RationalExpectations.certainty_equivalence_fwd
#print axioms Miao.RationalExpectations.theorem_1_4_2_of_stoch
#print axioms Miao.RationalExpectations.bkS_Evec_ar
#print axioms Miao.RationalExpectations.certainty_equivalence_ar
#print axioms Miao.RationalExpectations.certainty_equivalence_ar_det
#print axioms Miao.RationalExpectations.bkS_fwd_zero
#print axioms Miao.RationalExpectations.bkS_homog_u_zero
#print axioms Miao.RationalExpectations.theorem_1_4_3_gt_stoch
#print axioms Miao.RationalExpectations.theorem_1_4_3_lt_stoch
#print axioms Miao.RationalExpectations.theorem_1_4_3_lt_exists_stoch
#print axioms Miao.RationalExpectations.bkS_shift
#print axioms Miao.RationalExpectations.corollary_1_4_1_stoch
#print axioms Miao.RationalExpectations.nkA
#print axioms Miao.RationalExpectations.nkB
#print axioms Miao.RationalExpectations.nkC
#print axioms Miao.RationalExpectations.nkAinv
#print axioms Miao.RationalExpectations.nkSaddleW
#print axioms Miao.RationalExpectations.nkW
#print axioms Miao.RationalExpectations.nkG
#print axioms Miao.RationalExpectations.nkState
#print axioms Miao.RationalExpectations.nkShock
#print axioms Miao.RationalExpectations.nk_sumElim_eq_iff
#print axioms Miao.RationalExpectations.nk_matAct_A
#print axioms Miao.RationalExpectations.nk_matAct_B
#print axioms Miao.RationalExpectations.nk_matAct_C
#print axioms Miao.RationalExpectations.eq_2_16
#print axioms Miao.RationalExpectations.nkA_mul_inv
#print axioms Miao.RationalExpectations.eq_2_16_W
#print axioms Miao.RationalExpectations.nkSaddleP
#print axioms Miao.RationalExpectations.nkSaddleR
#print axioms Miao.RationalExpectations.nk_tri_stable
#print axioms Miao.RationalExpectations.nk_scalar_eig
#print axioms Miao.RationalExpectations.nk_saddle_split
#print axioms Miao.RationalExpectations.nk_saddle_eig
#print axioms Miao.RationalExpectations.nk_saddle_eig_l1
#print axioms Miao.RationalExpectations.nk_saddle_unstable
#print axioms Miao.RationalExpectations.nkTr
#print axioms Miao.RationalExpectations.nkLam1
#print axioms Miao.RationalExpectations.nkLam2
#print axioms Miao.RationalExpectations.nk_lam
#print axioms Miao.RationalExpectations.example_2_3_1_split
#print axioms Miao.RationalExpectations.example_2_3_1_eigen
#print axioms Miao.RationalExpectations.example_2_3_1_indeterminate
#print axioms Miao.RationalExpectations.example_2_3_1_indeterminate_det
#print axioms Miao.RationalExpectations.nkBothOut
#print axioms Miao.RationalExpectations.nk_eig2
#print axioms Miao.RationalExpectations.nk_out_of_bothOut
#print axioms Miao.RationalExpectations.nk_root_of_not_bothOut
#print axioms Miao.RationalExpectations.nk_eigvec2
#print axioms Miao.RationalExpectations.nk_jump2_unique
#print axioms Miao.RationalExpectations.nk_jump2_nonunique
#print axioms Miao.RationalExpectations.nkWT
#print axioms Miao.RationalExpectations.nkTaylorEqm
#print axioms Miao.RationalExpectations.nkDeterminate
#print axioms Miao.RationalExpectations.nk_taylor_iff
#print axioms Miao.RationalExpectations.nk_bothOut_WT
#print axioms Miao.RationalExpectations.nk_WT_trace
#print axioms Miao.RationalExpectations.ex_2_2_suff
#print axioms Miao.RationalExpectations.ex_2_2_nec
#print axioms Miao.RationalExpectations.ex_2_2_b_exact
#print axioms Miao.RationalExpectations.ex_2_2_b
#print axioms Miao.RationalExpectations.ex_2_2_a
#print axioms Miao.RationalExpectations.ex_2_2_a_taylor_principle
#print axioms Miao.RationalExpectations.ex_2_2_a_printed_false
#print axioms Miao.RationalExpectations.IsMartingaleProc
#print axioms Miao.RationalExpectations.IsMartingaleDiffProc
#print axioms Miao.RationalExpectations.IsPredeterminedKlein
#print axioms Miao.RationalExpectations.predError_isMartingaleDiff
#print axioms Miao.RationalExpectations.isPredeterminedKlein_zero_iff
#print axioms Miao.RationalExpectations.IsMartingaleProc.diff
#print axioms Miao.RationalExpectations.isStableProc_of_uniformly_bounded
#print axioms Miao.RationalExpectations.klM_trunc
#print axioms Miao.RationalExpectations.klM_trunc_apply
#print axioms Miao.RationalExpectations.klM_truncSystem
#print axioms Miao.RationalExpectations.example_mdiff_not_stable
#print axioms Miao.RationalExpectations.klS_matAct_sub
#print axioms Miao.RationalExpectations.klS_matAct_neg
#print axioms Miao.RationalExpectations.klS_matAct_zero
#print axioms Miao.RationalExpectations.klS_zero_matAct
#print axioms Miao.RationalExpectations.klS_add_matAct
#print axioms Miao.RationalExpectations.klS_sub_matAct
#print axioms Miao.RationalExpectations.klS_neg_matAct
#print axioms Miao.RationalExpectations.klS_matAct_comp
#print axioms Miao.RationalExpectations.klS_matCLM
#print axioms Miao.RationalExpectations.klS_matCLM_apply
#print axioms Miao.RationalExpectations.klS_matAct_sum
#print axioms Miao.RationalExpectations.klS_matAct_inv_mul
#print axioms Miao.RationalExpectations.klS_matAct_mul_inv
#print axioms Miao.RationalExpectations.klS_matAct_blocks
#print axioms Miao.RationalExpectations.klS_matAct_natAdd
#print axioms Miao.RationalExpectations.klS_ext_blocks
#print axioms Miao.RationalExpectations.klS_append_castAdd
#print axioms Miao.RationalExpectations.klS_append_natAdd
#print axioms Miao.RationalExpectations.klS_Evec_add
#print axioms Miao.RationalExpectations.klS_Evec_sub
#print axioms Miao.RationalExpectations.klS_Evec_neg
#print axioms Miao.RationalExpectations.klS_Evec_zero
#print axioms Miao.RationalExpectations.klS_Evec_idem
#print axioms Miao.RationalExpectations.klS_Evec_tower_le
#print axioms Miao.RationalExpectations.klS_Evec_tower_ge
#print axioms Miao.RationalExpectations.klS_Evec_comp
#print axioms Miao.RationalExpectations.klS_Evec_append
#print axioms Miao.RationalExpectations.klS_adapted_succ
#print axioms Miao.RationalExpectations.klS_EvecCLM
#print axioms Miao.RationalExpectations.klS_EvecCLM_apply
#print axioms Miao.RationalExpectations.klS_ent
#print axioms Miao.RationalExpectations.klS_ent_nonneg
#print axioms Miao.RationalExpectations.klS_norm_matAct_le
#print axioms Miao.RationalExpectations.klS_norm_Evec_le
#print axioms Miao.RationalExpectations.klS_stable_bound
#print axioms Miao.RationalExpectations.klS_stable_of_le
#print axioms Miao.RationalExpectations.klS_stable_add
#print axioms Miao.RationalExpectations.klS_stable_sub
#print axioms Miao.RationalExpectations.klS_stable_matAct
#print axioms Miao.RationalExpectations.klS_stable_Evec
#print axioms Miao.RationalExpectations.klS_stable_shift
#print axioms Miao.RationalExpectations.klS_stable_comp
#print axioms Miao.RationalExpectations.klS_stable_append
#print axioms Miao.RationalExpectations.klS_entry_le_mclm
#print axioms Miao.RationalExpectations.klS_ent_le_mclm
#print axioms Miao.RationalExpectations.klS_summable_ent
#print axioms Miao.RationalExpectations.klS_fwd
#print axioms Miao.RationalExpectations.klS_fwd_summable
#print axioms Miao.RationalExpectations.klS_norm_fwd_le
#print axioms Miao.RationalExpectations.klS_fwd_adapted
#print axioms Miao.RationalExpectations.klS_fwd_rec
#print axioms Miao.RationalExpectations.klS_eq_fwd
#print axioms Miao.RationalExpectations.klS_stable_of_rec
#print axioms Miao.RationalExpectations.klS_norm_comp_le
#print axioms Miao.RationalExpectations.klS_blocks_iff
#print axioms Miao.RationalExpectations.klS_solve_fwd
#print axioms Miao.RationalExpectations.eq_klein_Es
#print axioms Miao.RationalExpectations.eq_klein_xi
#print axioms Miao.RationalExpectations.eq_klein_k
#print axioms Miao.RationalExpectations.eq_klein_s
#print axioms Miao.RationalExpectations.klS_core_blocks
#print axioms Miao.RationalExpectations.klS_core
#print axioms Miao.RationalExpectations.klS_isRESolution_iff
#print axioms Miao.RationalExpectations.klein_stochastic
#print axioms Miao.RationalExpectations.klS_cj_matAct
#print axioms Miao.RationalExpectations.klein_stochastic_real
#print axioms Miao.RationalExpectations.eq_2_17
#print axioms Miao.RationalExpectations.eq_2_17_solution
#print axioms Miao.RationalExpectations.klS_detSystem
#print axioms Miao.RationalExpectations.klS_Evec_det
#print axioms Miao.RationalExpectations.klS_matAct_eq_mulVec
#print axioms Miao.RationalExpectations.eq_2_17_printed_false
#print axioms Miao.RationalExpectations.klS_Ez_of_2_1
#print axioms Miao.RationalExpectations.klS_entry_le_ent
#print axioms Miao.RationalExpectations.klS_entry_mul_le
#print axioms Miao.RationalExpectations.klS_sylvester_unique
#print axioms Miao.RationalExpectations.klS_sylvester_exists
#print axioms Miao.RationalExpectations.klS_simpl_y
#print axioms Miao.RationalExpectations.klS_simpl_k
#print axioms Miao.RationalExpectations.klein_simplified_form
#print axioms Miao.RationalExpectations.lq_predError
#print axioms Miao.RationalExpectations.lq_predetermined
#print axioms Miao.RationalExpectations.lqPeriod
#print axioms Miao.RationalExpectations.lq_variation_u
#print axioms Miao.RationalExpectations.lq_variation_x
#print axioms Miao.RationalExpectations.lqLeft
#print axioms Miao.RationalExpectations.lqRight
#print axioms Miao.RationalExpectations.klL_matAct_fromBlocks
#print axioms Miao.RationalExpectations.klL_matAct_fromRows
#print axioms Miao.RationalExpectations.klL_matAct_fromCols
#print axioms Miao.RationalExpectations.klL_matAct_zero
#print axioms Miao.RationalExpectations.klL_matAct_smul
#print axioms Miao.RationalExpectations.klL_matAct_neg
#print axioms Miao.RationalExpectations.klL_Evec_elim
#print axioms Miao.RationalExpectations.lq_system_iff
#print axioms Miao.RationalExpectations.simsTop
#print axioms Miao.RationalExpectations.simsBot
#print axioms Miao.RationalExpectations.sims11
#print axioms Miao.RationalExpectations.sims12
#print axioms Miao.RationalExpectations.sims22
#print axioms Miao.RationalExpectations.simsBlk
#print axioms Miao.RationalExpectations.simsRows
#print axioms Miao.RationalExpectations.simsBlk_11
#print axioms Miao.RationalExpectations.simsBlk_12
#print axioms Miao.RationalExpectations.simsBlk_21
#print axioms Miao.RationalExpectations.simsBlk_22
#print axioms Miao.RationalExpectations.simsRows_top
#print axioms Miao.RationalExpectations.simsRows_bot
#print axioms Miao.RationalExpectations.simsBlk_det
#print axioms Miao.RationalExpectations.simsTop_mul
#print axioms Miao.RationalExpectations.simsBot_mul
#print axioms Miao.RationalExpectations.simsRows_mul
#print axioms Miao.RationalExpectations.simsH_top_matAct
#print axioms Miao.RationalExpectations.simsH_bot_matAct
#print axioms Miao.RationalExpectations.simsH_blk_top
#print axioms Miao.RationalExpectations.simsH_blk_bot
#print axioms Miao.RationalExpectations.simsH_matAct_smul
#print axioms Miao.RationalExpectations.IsSimsSolution
#print axioms Miao.RationalExpectations.IsSimsShock
#print axioms Miao.RationalExpectations.IsSimsQZ
#print axioms Miao.RationalExpectations.IsSimsQZ.mk
#print axioms Miao.RationalExpectations.IsSimsQZ.unitary_Q
#print axioms Miao.RationalExpectations.IsSimsQZ.unitary_Z
#print axioms Miao.RationalExpectations.IsSimsQZ.upper_S
#print axioms Miao.RationalExpectations.IsSimsQZ.upper_T
#print axioms Miao.RationalExpectations.IsSimsQZ.ord
#print axioms Miao.RationalExpectations.IsSimsQZ.off_circle
#print axioms Miao.RationalExpectations.isSimsQZ_of_regular
#print axioms Miao.RationalExpectations.SimsAssumption1
#print axioms Miao.RationalExpectations.SimsAssumption2
#print axioms Miao.RationalExpectations.simsH_transform
#print axioms Miao.RationalExpectations.eq_2_21
#print axioms Miao.RationalExpectations.simsH_idSystem
#print axioms Miao.RationalExpectations.simsH_Evec_id
#print axioms Miao.RationalExpectations.simsH_fwd_data
#print axioms Miao.RationalExpectations.eq_2_22
#print axioms Miao.RationalExpectations.eq_2_22_expect
#print axioms Miao.RationalExpectations.sims_u_eq_zero
#print axioms Miao.RationalExpectations.sims_Z2_y0
#print axioms Miao.RationalExpectations.eq_2_23
#print axioms Miao.RationalExpectations.lemma_2_3_1
#print axioms Miao.RationalExpectations.lemma_2_3_1_sims
#print axioms Miao.RationalExpectations.simsH_scalar_of_vec
#print axioms Miao.RationalExpectations.lemma_2_3_1_random
#print axioms Miao.RationalExpectations.assumption_2_3_1_nu_gt_m
#print axioms Miao.RationalExpectations.simsH_factor_iff
#print axioms Miao.RationalExpectations.simsAssumption2_iff_ker
#print axioms Miao.RationalExpectations.simsGmat
#print axioms Miao.RationalExpectations.simsHmat
#print axioms Miao.RationalExpectations.simsKmat
#print axioms Miao.RationalExpectations.simsTheta1
#print axioms Miao.RationalExpectations.simsTheta2
#print axioms Miao.RationalExpectations.simsGmat_det
#print axioms Miao.RationalExpectations.simsH_add_comp
#print axioms Miao.RationalExpectations.simsH_solve_G
#print axioms Miao.RationalExpectations.eq_2_24
#print axioms Miao.RationalExpectations.simsKmat_mul_Pm
#print axioms Miao.RationalExpectations.theorem_2_3_1_theta
#print axioms Miao.RationalExpectations.theorem_2_3_1_uniqueness
#print axioms Miao.RationalExpectations.simsH_stable_zero
#print axioms Miao.RationalExpectations.simsH_core_exists
#print axioms Miao.RationalExpectations.theorem_2_3_1_existence
#print axioms Miao.RationalExpectations.theorem_2_3_1_sufficiency
#print axioms Miao.RationalExpectations.SimsRich
#print axioms Miao.RationalExpectations.simsH_rich_shock
#print axioms Miao.RationalExpectations.simsH_zero_shock
#print axioms Miao.RationalExpectations.simsH_zero_solution
#print axioms Miao.RationalExpectations.theorem_2_3_1_necessity_1
#print axioms Miao.RationalExpectations.theorem_2_3_1_necessity_2
#print axioms Miao.RationalExpectations.theorem_2_3_1
#print axioms Miao.RationalExpectations.simsRich_trunc
#print axioms Miao.RationalExpectations.simsH_det_mdiff
#print axioms Miao.RationalExpectations.simsH_det_sol_iff
#print axioms Miao.RationalExpectations.theorem_2_3_1_necessity_false
#print axioms Miao.RationalExpectations.simsH_smul_matAct
#print axioms Miao.RationalExpectations.simsH_upper_one
#print axioms Miao.RationalExpectations.theta_1_printed_false
#print axioms Miao.RationalExpectations.eq_2_22_printed_false
#print axioms Miao.RationalExpectations.IsThinSVD
#print axioms Miao.RationalExpectations.IsThinSVD.mk
#print axioms Miao.RationalExpectations.IsThinSVD.eq
#print axioms Miao.RationalExpectations.IsThinSVD.U1_orth
#print axioms Miao.RationalExpectations.IsThinSVD.V1_orth
#print axioms Miao.RationalExpectations.IsThinSVD.det_D
#print axioms Miao.RationalExpectations.simsH_proj_mul
#print axioms Miao.RationalExpectations.simsH_svd_left
#print axioms Miao.RationalExpectations.simsH_colspace_explicit
#print axioms Miao.RationalExpectations.colspace_iff
#print axioms Miao.RationalExpectations.colspace_iff_thin
#print axioms Miao.RationalExpectations.colspace_printed_false
#print axioms Miao.RationalExpectations.lambda_formula
#print axioms Miao.RationalExpectations.xi_residual
#print axioms Miao.RationalExpectations.xi_formula
#print axioms Miao.RationalExpectations.svd_injective_iff
#print axioms Miao.RationalExpectations.SimsYUnique
#print axioms Miao.RationalExpectations.SimsPairUnique
#print axioms Miao.RationalExpectations.simsH_sol_add
#print axioms Miao.RationalExpectations.simsH_perturb
#print axioms Miao.RationalExpectations.simsY_unique_iff
#print axioms Miao.RationalExpectations.corollary_2_3_1
#print axioms Miao.RationalExpectations.corollary_2_3_1_printed_false
#print axioms Miao.RationalExpectations.lubik_schorfheide
#print axioms Miao.RationalExpectations.eq_2_26
#print axioms Miao.RationalExpectations.eq_sunspot_identity
#print axioms Miao.RationalExpectations.sunspot_term_simplified
#print axioms Miao.RationalExpectations.simsTheta3
#print axioms Miao.RationalExpectations.simsH_rows_zero
#print axioms Miao.RationalExpectations.sunspot_solution
#print axioms Miao.RationalExpectations.sunspot_existence
#print axioms Miao.RationalExpectations.IsSims19Solution
#print axioms Miao.RationalExpectations.isSims19_zero_iff
#print axioms Miao.RationalExpectations.eq_2_19_const
#print axioms Miao.RationalExpectations.eq_2_19_const_singular
#print axioms Miao.RationalExpectations.eq_2_19_append
#print axioms Miao.RationalExpectations.IsNKSolution
#print axioms Miao.RationalExpectations.ex232Γ₀
#print axioms Miao.RationalExpectations.ex232Γ₁
#print axioms Miao.RationalExpectations.ex232Ψ
#print axioms Miao.RationalExpectations.ex232Pm
#print axioms Miao.RationalExpectations.example_2_3_2_rows
#print axioms Miao.RationalExpectations.example_2_3_2
#print axioms Miao.RationalExpectations.svdE_mul_eigen
#print axioms Miao.RationalExpectations.svdE_cols
#print axioms Miao.RationalExpectations.exists_thinSVD
#print axioms Miao.RationalExpectations.colspace_iff_svd
#print axioms Miao.RationalExpectations.lambda_formula_svd
#print axioms Miao.RationalExpectations.corollary_2_3_1_rank
#print axioms Miao.RationalExpectations.lubik_schorfheide_rank
#print axioms Miao.RationalExpectations.eq_2_26_svd
#print axioms Miao.RationalExpectations.pertE4
#print axioms Miao.RationalExpectations.pertP
#print axioms Miao.RationalExpectations.pertDx
#print axioms Miao.RationalExpectations.pertDs
#print axioms Miao.RationalExpectations.pert_hasDerivAt_two
#print axioms Miao.RationalExpectations.pert_hasDerivAt_four
#print axioms Miao.RationalExpectations.pert_line_x
#print axioms Miao.RationalExpectations.pert_line_s
#print axioms Miao.RationalExpectations.pert_Dx_eq
#print axioms Miao.RationalExpectations.pert_Ds_eq
#print axioms Miao.RationalExpectations.pert_diff_fderiv
#print axioms Miao.RationalExpectations.pertPsi
#print axioms Miao.RationalExpectations.pertPhi
#print axioms Miao.RationalExpectations.pertF
#print axioms Miao.RationalExpectations.pert_psi_x
#print axioms Miao.RationalExpectations.pert_psi_s
#print axioms Miao.RationalExpectations.pert_phi_x
#print axioms Miao.RationalExpectations.pert_phi_s
#print axioms Miao.RationalExpectations.pertF_contDiff
#print axioms Miao.RationalExpectations.IsFiniteShock
#print axioms Miao.RationalExpectations.IsFiniteShock.mk
#print axioms Miao.RationalExpectations.IsFiniteShock.nonneg
#print axioms Miao.RationalExpectations.IsFiniteShock.sum_one
#print axioms Miao.RationalExpectations.IsFiniteShock.mean_zero
#print axioms Miao.RationalExpectations.pert_sum_lin
#print axioms Miao.RationalExpectations.pert_sum_quad
#print axioms Miao.RationalExpectations.pertPsi_ss
#print axioms Miao.RationalExpectations.pertPhi_ss
#print axioms Miao.RationalExpectations.pertF_Dx
#print axioms Miao.RationalExpectations.pertF_Ds
#print axioms Miao.RationalExpectations.eq_F_x
#print axioms Miao.RationalExpectations.eq_F_sigma_E
#print axioms Miao.RationalExpectations.eq_F_sigma
#print axioms Miao.RationalExpectations.pertRow
#print axioms Miao.RationalExpectations.eq_F_xx
#print axioms Miao.RationalExpectations.eq_F_sigma_x
#print axioms Miao.RationalExpectations.eq_F_sigma_sigma
#print axioms Miao.RationalExpectations.IsPertSolution
#print axioms Miao.RationalExpectations.IsPertSolution.mk
#print axioms Miao.RationalExpectations.IsPertSolution.f_smooth
#print axioms Miao.RationalExpectations.IsPertSolution.g_smooth
#print axioms Miao.RationalExpectations.IsPertSolution.h_smooth
#print axioms Miao.RationalExpectations.IsPertSolution.shock
#print axioms Miao.RationalExpectations.IsPertSolution.solves
#print axioms Miao.RationalExpectations.pert_partials_vanish
#print axioms Miao.RationalExpectations.pert_F_partials_zero
#print axioms Miao.RationalExpectations.eq_steady_state
#print axioms Miao.RationalExpectations.steady_state_printed_false
#print axioms Miao.RationalExpectations.pertCoefA
#print axioms Miao.RationalExpectations.pertCoefB
#print axioms Miao.RationalExpectations.pertCoefAx
#print axioms Miao.RationalExpectations.pert_hom2_unique
#print axioms Miao.RationalExpectations.g_sigma_system
#print axioms Miao.RationalExpectations.theorem_g_sigma_zero
#print axioms Miao.RationalExpectations.eq_F_x_zero
#print axioms Miao.RationalExpectations.eq_2_31
#print axioms Miao.RationalExpectations.eq_2_32
#print axioms Miao.RationalExpectations.eq_2_33
#print axioms Miao.RationalExpectations.eq_2_31_of_2_33
#print axioms Miao.RationalExpectations.eq_2_28_differential
#print axioms Miao.RationalExpectations.eq_2_28
#print axioms Miao.RationalExpectations.g_sigma_x_system
#print axioms Miao.RationalExpectations.theorem_g_sigma_x_zero
#print axioms Miao.RationalExpectations.pertCoefSS
#print axioms Miao.RationalExpectations.eq_F_sigma_sigma_linear
#print axioms Miao.RationalExpectations.g_sigma_sigma_unique
#print axioms Miao.RationalExpectations.pertCoefAxx
#print axioms Miao.RationalExpectations.pertCoefXX
#print axioms Miao.RationalExpectations.eq_F_xx_linear
#print axioms Miao.RationalExpectations.g_xx_unique
#print axioms Miao.RationalExpectations.pertTaylor2
#print axioms Miao.RationalExpectations.pertTaylor2_sigma
#print axioms Miao.RationalExpectations.summary_uncertainty
#print axioms Miao.RationalExpectations.pert_P_eq
#print axioms Miao.RationalExpectations.pertFxxPrinted
#print axioms Miao.RationalExpectations.eq_F_xx_printed
#print axioms Miao.RationalExpectations.eq_F_xx_printed_false
#print axioms Miao.RationalExpectations.pertFssPrinted
#print axioms Miao.RationalExpectations.eq_F_sigma_sigma_printed
#print axioms Miao.RationalExpectations.eq_F_sigma_sigma_printed_false
#print axioms Miao.RationalExpectations.g_sigma_not_forced
#print axioms Miao.RationalExpectations.g_sigma_x_not_forced
