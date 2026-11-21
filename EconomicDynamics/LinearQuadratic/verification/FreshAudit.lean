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
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Zorn
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.Martingale.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Bounds.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi
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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Generalized eigenvalues and the complex generalized Schur (QZ) form

Copied from `EconomicDynamics/RationalExpectations` (module `QZ`), namespace renamed.

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Singular systems: Klein's method

Copied from `EconomicDynamics/RationalExpectations` (module `Singular`), namespace renamed.

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The conditional expectations of `L¹(Ω, F, Pr)` given a filtration

Copied from `EconomicDynamics/RationalExpectations` (module `CondExpL1`), namespace renamed.

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# First-order linear stochastic systems: moments

Copied from `EconomicDynamics/RationalExpectations` (module `VARMoments`), namespace renamed.

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Martingales and Klein's predetermined processes

Copied from `EconomicDynamics/RationalExpectations` (module `KleinMartingales`), namespace renamed.

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Klein method for linear rational expectations models

Copied from `EconomicDynamics/RationalExpectations` (module `StochasticKlein`), namespace renamed.

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Klein solution in state-space form

Copied from `EconomicDynamics/RationalExpectations` (module `KleinSimplified`), namespace renamed.

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

namespace Miao.LinearQuadratic

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

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Copied from `GeneralStates/AbstractDecisionProcesses` (module `Basics`), namespace renamed to
`Miao.LinearQuadratic.SS`.

Volume 2, Chapter 2 of Sargent and Stachurski, *Dynamic Programming*, uses the
Volume 1 vocabulary of Markov matrices (§2.3.1.3), the contraction machinery of
§1.2.2, global stability, Blackwell's condition (Lemma 2.2.4), the comparison of
fixed points of ordered operators (Proposition 2.2.7) and the estimate
`|max f − max g| ≤ max |f − g|` (Lemma 2.2.2). Each chapter project is
self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace Miao.LinearQuadratic.SS

variable {X : Type*} [Fintype X]

/-- A stochastic (Markov) matrix on the finite state space `X` (Vol. 1, p. 71): nonnegative with
unit row sums. -/
structure IsMarkov (P : Matrix X X ℝ) : Prop where
  nonneg : ∀ x x', 0 ≤ P x x'
  rowsum : ∀ x, ∑ x', P x x' = 1

/-- A distribution on `X` (Vol. 1, p. 31): nonnegative and summing to one. -/
structure IsDistribution (ψ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  sum_eq_one : ∑ x, ψ x = 1

/-- `(Ph)(x) = ∑ h(x')P(x, x')`, Vol. 1 (3.12). -/
theorem mulVec_apply_eq (P : Matrix X X ℝ) (h : X → ℝ) (x : X) :
    (P *ᵥ h) x = ∑ x', h x' * P x x' := by
  simp only [mulVec, dotProduct, mul_comm]

theorem IsMarkov.mul {P Q : Matrix X X ℝ} (hP : IsMarkov P) (hQ : IsMarkov Q) :
    IsMarkov (P * Q) where
  nonneg x x' := by
    rw [Matrix.mul_apply]
    exact sum_nonneg fun z _ => mul_nonneg (hP.nonneg x z) (hQ.nonneg z x')
  rowsum x := by
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    simp only [← mul_sum, hQ.rowsum, mul_one, hP.rowsum]

/-- `Pᵏ` is Markov. -/
theorem IsMarkov.pow [DecidableEq X] {P : Matrix X X ℝ} (hP : IsMarkov P) (k : ℕ) :
    IsMarkov (P ^ k) := by
  induction k with
  | zero =>
    refine ⟨fun x x' => ?_, fun x => ?_⟩
    · simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ k ih => rw [pow_succ]; exact ih.mul hP

/-- A Markov matrix preserves `≤` on functions. -/
theorem IsMarkov.mulVec_le_mulVec {P : Matrix X X ℝ} (hP : IsMarkov P) {f g : X → ℝ} (hfg : f ≤ g) :
    P *ᵥ f ≤ P *ᵥ g := fun x =>
  sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hfg x') (hP.nonneg x x')

/-- `P𝟙 = 𝟙`: constants are fixed by a Markov matrix. -/
theorem IsMarkov.mulVec_const {P : Matrix X X ℝ} (hP : IsMarkov P) (c : ℝ) :
    P *ᵥ (fun _ => c) = fun _ => c := by
  funext x
  simp only [mulVec, dotProduct, ← sum_mul, hP.rowsum, one_mul]

/-- `|Ph(x)| ≤ ‖h‖_∞` (Vol. 1, Ex 3.2.1). -/
theorem IsMarkov.abs_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) (x : X) :
    |(P *ᵥ h) x| ≤ ‖h‖ := by
  have hb : ∀ x', |h x'| ≤ ‖h‖ := fun x' => by
    have := norm_le_pi_norm h x'
    rwa [Real.norm_eq_abs] at this
  calc |(P *ᵥ h) x| = |∑ x', P x x' * h x'| := rfl
    _ ≤ ∑ x', |P x x' * h x'| := abs_sum_le_sum_abs _ _
    _ = ∑ x', P x x' * |h x'| := sum_congr rfl fun x' _ => by
        rw [abs_mul, abs_of_nonneg (hP.nonneg x x')]
    _ ≤ ∑ x', P x x' * ‖h‖ :=
        sum_le_sum fun x' _ => mul_le_mul_of_nonneg_left (hb x') (hP.nonneg x x')
    _ = ‖h‖ := by rw [← sum_mul, hP.rowsum, one_mul]

/-- `‖Ph‖_∞ ≤ ‖h‖_∞`. -/
theorem IsMarkov.norm_mulVec_le {P : Matrix X X ℝ} (hP : IsMarkov P) (h : X → ℝ) :
    ‖P *ᵥ h‖ ≤ ‖h‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro x
  rw [Real.norm_eq_abs]
  exact hP.abs_mulVec_le h x

/-- `|(Pf)(x) − (Pg)(x)| ≤ ‖f − g‖_∞`. -/
theorem IsMarkov.abs_mulVec_sub_le {P : Matrix X X ℝ} (hP : IsMarkov P) (f g : X → ℝ) (x : X) :
    |(P *ᵥ f) x - (P *ᵥ g) x| ≤ ‖f - g‖ := by
  have := hP.abs_mulVec_le (f - g) x
  rwa [mulVec_sub, Pi.sub_apply] at this

/-- Global stability (Vol. 1, p. 22). -/
def GloballyStable {U : Type*} [TopologicalSpace U] (T : U → U) : Prop :=
  ∃ u' : U, IsFixedPt T u' ∧ (∀ v, IsFixedPt T v → v = u') ∧
    ∀ u, Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')

variable {E : Type*} [NormedAddCommGroup E]

/-- A contraction of modulus `L` on `U` (Vol. 1, (1.17)). -/
structure IsContractionOn (T : E → E) (U : Set E) (L : ℝ) : Prop where
  mapsTo : Set.MapsTo T U U
  nonneg : 0 ≤ L
  lt_one : L < 1
  norm_sub_le : ∀ u ∈ U, ∀ v ∈ U, ‖T u - T v‖ ≤ L * ‖u - v‖

namespace IsContractionOn

variable {T : E → E} {U : Set E} {L : ℝ}

theorem fixedPt_unique (h : IsContractionOn T U L) {u v : E} (hu : u ∈ U) (hv : v ∈ U)
    (hfu : IsFixedPt T u) (hfv : IsFixedPt T v) : u = v := by
  have hb := h.norm_sub_le u hu v hv
  rw [hfu.eq, hfv.eq] at hb
  have hnn : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hpos : 0 < 1 - L := by linarith [h.lt_one]
  have : ‖u - v‖ ≤ 0 := by nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm this hnn))

theorem iterate_mem (h : IsContractionOn T U L) {u : E} (hu : u ∈ U) (k : ℕ) : T^[k] u ∈ U := by
  induction k with
  | zero => simpa using hu
  | succ k ih => rw [iterate_succ_apply']; exact h.mapsTo ih

theorem norm_iterate_sub_fixedPt_le (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U)
    (hu' : u' ∈ U) (hfix : IsFixedPt T u') (k : ℕ) :
    ‖T^[k] u - u'‖ ≤ L ^ k * ‖u - u'‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply']
    calc ‖T (T^[k] u) - u'‖ = ‖T (T^[k] u) - T u'‖ := by rw [hfix.eq]
      _ ≤ L * ‖T^[k] u - u'‖ := h.norm_sub_le _ (h.iterate_mem hu k) _ hu'
      _ ≤ L * (L ^ k * ‖u - u'‖) := mul_le_mul_of_nonneg_left ih h.nonneg
      _ = L ^ (k + 1) * ‖u - u'‖ := by ring

theorem tendsto_iterate_fixedPt (h : IsContractionOn T U L) {u u' : E} (hu : u ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  refine squeeze_zero (fun _ => norm_nonneg _) (h.norm_iterate_sub_fixedPt_le hu hu' hfix) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h.nonneg h.lt_one).mul_const ‖u - u'‖

/-- Banach's theorem (Vol. 1, Theorem 1.2.3), existence, from Mathlib's `ContractingWith`. -/
theorem exists_fixedPt [CompleteSpace E] (h : IsContractionOn T U L) (hU : IsClosed U)
    (hne : U.Nonempty) : ∃ u' ∈ U, IsFixedPt T u' := by
  have : CompleteSpace U := hU.completeSpace_coe
  have : Nonempty U := hne.to_subtype
  let T' : U → U := h.mapsTo.restrict T U U
  have hT' : ContractingWith ⟨L, h.nonneg⟩ T' := by
    refine ⟨by exact_mod_cast h.lt_one, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [T', Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    exact h.norm_sub_le x x.2 y y.2
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, IsFixedPt T' u₀ := ⟨_, hT'.fixedPoint_isFixedPt⟩
  exact ⟨u₀.1, u₀.2, congrArg Subtype.val hu₀⟩

/-- A contraction on the whole of a complete space is globally stable (Vol. 1, Theorem 1.2.3). -/
theorem globallyStable_univ [CompleteSpace E] (h : IsContractionOn T Set.univ L) :
    GloballyStable T := by
  obtain ⟨u', -, hu'⟩ := h.exists_fixedPt isClosed_univ ⟨0, Set.mem_univ 0⟩
  exact ⟨u', hu', fun v hv => h.fixedPt_unique (Set.mem_univ v) (Set.mem_univ u') hv hu',
    fun u => h.tendsto_iterate_fixedPt (Set.mem_univ u) (Set.mem_univ u') hu'⟩

end IsContractionOn

omit [Fintype X] in
/-- Vol. 1, Proposition 2.2.7, in the form used here: if `S ≤ T` pointwise, `T` is order
preserving and its iterates from any point converge to `u_T`, then every fixed point of `S` lies
below `u_T`. The ambient space is `ℝ^X` with the pointwise order. -/
theorem fixedPt_le_of_le {S T : (X → ℝ) → (X → ℝ)} (hST : ∀ v, S v ≤ T v) (hT : Monotone T)
    {uS uT : X → ℝ} (huS : IsFixedPt S uS) (hlim : Tendsto (fun k : ℕ => T^[k] uS) atTop (𝓝 uT)) :
    uS ≤ uT := by
  have hle : ∀ k : ℕ, uS ≤ T^[k] uS := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      calc uS = S uS := huS.eq.symm
        _ ≤ T uS := hST uS
        _ ≤ T (T^[k] uS) := hT ih
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

omit [Fintype X] in
/-- If `u ≤ Tu`, `T` is order preserving and `Tᵏu → u*`, then `u ≤ u*`: the monotone-improvement
step behind Howard policy iteration. -/
theorem le_fixedPt_of_le_apply {T : (X → ℝ) → (X → ℝ)} (hT : Monotone T) {u u' : X → ℝ}
    (hu : u ≤ T u) (hlim : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) : u ≤ u' := by
  have hle : ∀ k : ℕ, u ≤ T^[k] u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact hu.trans (hT ih)
  intro x
  exact ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

/-- Blackwell's condition (Vol. 1, Lemma 2.2.4) on all of `ℝ^X`: an order-preserving `T` with
`T(u + c) ≤ Tu + βc` for `c ≥ 0` is a contraction of modulus `β` in the supremum norm. -/
theorem isContractionOn_of_blackwell {T : (X → ℝ) → (X → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hmono : Monotone T)
    (hdisc : ∀ u : X → ℝ, ∀ c : ℝ, 0 ≤ c → T (u + fun _ : X => c) ≤ T u + fun _ : X => β * c) :
    IsContractionOn T Set.univ β := by
  refine ⟨Set.mapsTo_univ _ _, hβ0, hβ1, fun u _ v _ => ?_⟩
  have key : ∀ u v : X → ℝ, ∀ x : X, T u x - T v x ≤ β * ‖u - v‖ := by
    intro u v x
    have hle : u ≤ v + fun _ : X => ‖u - v‖ := fun y => by
      have := norm_le_pi_norm (u - v) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (u y - v y)]
    have h1 := hmono hle x
    have h2 := hdisc v ‖u - v‖ (norm_nonneg _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨key u v x, ?_⟩
  have := key v u x
  rwa [norm_sub_rev] at this

omit [Fintype X] in
/-- Vol. 1, Lemma 2.2.2: for a nonempty finite `D`, `|max f − max g| ≤ max |f − g|`. -/
theorem abs_sup'_sub_sup'_le {D : Type*} {s : Finset D} (hs : s.Nonempty) (f g : D → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs fun z => |f z - g z| := by
  have key : ∀ f g : D → ℝ, s.sup' hs f - s.sup' hs g ≤ s.sup' hs fun z => |f z - g z| := by
    intro f g
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le hs f fun z hz => ?_
    calc f z = (f z - g z) + g z := by ring
      _ ≤ |f z - g z| + g z := add_le_add (le_abs_self _) le_rfl
      _ ≤ (s.sup' hs fun z => |f z - g z|) + s.sup' hs g :=
          add_le_add (Finset.le_sup' (fun z => |f z - g z|) hz) (Finset.le_sup' g hz)
  rw [abs_sub_le_iff]
  refine ⟨key f g, ?_⟩
  have := key g f
  simpa [abs_sub_comm] using this

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix on a finite state space

Copied from `GeneralStates/AbstractDecisionProcesses` (module `SpectralRadius`), namespace renamed
to `Miao.LinearQuadratic.SS`.

The spectral radius `ρ(A)` of Vol. 1 (1.15) and the facts about it that
Chapters 6–10 use: Gelfand's formula (Lemma 1.2.2), the eventual bound
`‖Aᵏ‖ ≤ rᵏ` for `r > ρ(A)`, the Neumann series (Theorem 1.2.1), invariance
under transposition, monotonicity in the entries (Exercise 2.2.28), and the
row-sum characterisations of the ℓ∞ operator norm. These are the results of
the `FiniteStates/OperatorsFixedPoints` project restated for a matrix indexed by
an arbitrary finite type `X`, as Chapter 6 needs them on product state spaces
`Y × Z`; each chapter project is self-contained.
-/

open Filter Topology Matrix Finset

namespace Miao.LinearQuadratic.SS

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Powers of a nonnegative matrix are nonnegative. -/
theorem pow_nonneg_entries {A : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ)
    (i j : X) : 0 ≤ (A ^ k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (hA i l) (ih l j)

/-- Exercise 2.2.28 (p. 60), first part: `0 ≤ A ≤ B` implies `Aᵏ ≤ Bᵏ` for all `k`. -/
theorem pow_le_pow_entries {A B : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) (i j : X) : (A ^ k) i j ≤ (B ^ k) i j := by
  induction k generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    exact sum_le_sum fun l _ =>
      mul_le_mul (hAB i l) (ih l j) (pow_nonneg_entries hA k l j) ((hA i l).trans (hAB i l))




/-- The complexification of a real matrix. -/
def complexify (A : Matrix X X ℝ) : Matrix X X ℂ :=
  A.map Complex.ofReal

omit [Fintype X] [DecidableEq X] in
theorem complexify_apply (A : Matrix X X ℝ) (i j : X) :
    complexify A i j = (A i j : ℂ) := by
  classical
  exact rfl

theorem complexify_pow (A : Matrix X X ℝ) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := X)) A k

omit [Fintype X] [DecidableEq X] in
theorem complexify_transpose (A : Matrix X X ℝ) :
    complexify Aᵀ = (complexify A)ᵀ := by
  classical
  ext i j
  rfl

theorem nnnorm_complexify (A : Matrix X X ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix X X ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius (Vol. 1, (1.15)): the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix X X ℝ) : ℝ :=
  (spectralRadius ℂ (complexify A)).toReal

omit [DecidableEq X] in
theorem spectralRadius_complexify_ne_top [Nonempty X] (A : Matrix X X ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ := by
  classical
  exact
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

omit [DecidableEq X] in
theorem specRad_nonneg (A : Matrix X X ℝ) : 0 ≤ specRad A := by
  classical
  exact ENNReal.toReal_nonneg

/-- The spectrum of the complexification is the set of eigenvalues. -/
theorem mem_spectrum_iff_eigenpair (A : Matrix X X ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ ∃ e : X → ℂ, e ≠ 0 ∧ complexify A *ᵥ e = μ • e := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
    exact h.symm

/-- Gelfand's formula (Vol. 1, Lemma 1.2.2) for real matrices: `‖Aᵏ‖^{1/k} → ρ(A)`. -/
theorem tendsto_norm_pow_rpow [Nonempty X] (A : Matrix X X ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k => ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- If `ρ(A) < r` then `‖Aᵏ‖ ≤ rᵏ` for all large `k`. -/
theorem eventually_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- `ρ(A) < 1` implies `‖Aᵏ‖ → 0`. -/
theorem tendsto_norm_pow_zero [Nonempty X] (A : Matrix X X ℝ) (hρ : specRad A < 1) :
    Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (eventually_norm_pow_le A hr1)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr2)

/-- `ρ(A) < 1` implies `∑ₖ Aᵏ` converges. -/
theorem summable_pow [Nonempty X] (A : Matrix X X ℝ) (hρ : specRad A < 1) :
    Summable fun k : ℕ => A ^ k := by
  have : CompleteSpace (Matrix X X ℝ) := FiniteDimensional.complete ℝ _
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2)
    (eventually_norm_pow_le A hr1)

/-- `(I − A) ∑ₖ Aᵏ = I` when the series converges. -/
theorem one_sub_mul_tsum (A : Matrix X X ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (1 - A) * ∑' k : ℕ, A ^ k = 1 := by
  have h1 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ range K, A ^ k) atTop
      (𝓝 ((1 - A) * ∑' k : ℕ, A ^ k)) :=
    hs.hasSum.tendsto_sum_nat.const_mul (1 - A)
  have h2 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ range K, A ^ k) atTop (𝓝 1) := by
    simp_rw [mul_neg_geom_sum]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

theorem tsum_mul_one_sub (A : Matrix X X ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (∑' k : ℕ, A ^ k) * (1 - A) = 1 := by
  have h1 : Tendsto (fun K : ℕ => (∑ k ∈ range K, A ^ k) * (1 - A)) atTop
      (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have h2 : Tendsto (fun K : ℕ => (∑ k ∈ range K, A ^ k) * (1 - A)) atTop (𝓝 1) := by
    simp_rw [geom_sum_mul_neg]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

/-- The Neumann series lemma (Vol. 1, Theorem 1.2.1): `ρ(A) < 1` implies `I − A` is invertible with
inverse `∑ₖ Aᵏ`. -/
theorem neumann_series [Nonempty X] (A : Matrix X X ℝ) (hρ : specRad A < 1) :
    IsUnit (1 - A) ∧ (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  ⟨⟨⟨1 - A, ∑' k : ℕ, A ^ k, one_sub_mul_tsum A (summable_pow A hρ),
    tsum_mul_one_sub A (summable_pow A hρ)⟩, rfl⟩,
    Matrix.inv_eq_right_inv (one_sub_mul_tsum A (summable_pow A hρ))⟩

omit [DecidableEq X] in
/-- `ρ(Aᵀ) = ρ(A)`. -/
theorem specRad_transpose (A : Matrix X X ℝ) : specRad Aᵀ = specRad A := by
  classical
  unfold specRad
  rw [complexify_transpose, Matrix.spectralRadius_transpose]

/-- The ℓ∞ operator norm is monotone in the absolute values of the entries. -/
theorem norm_le_norm_of_abs_le {A B : Matrix X X ℝ} (h : ∀ i j, |A i j| ≤ |B i j|) :
    ‖A‖ ≤ ‖B‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  norm_cast
  refine Finset.sup_mono_fun fun i _ => sum_le_sum fun j _ => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
  exact h i j

omit [DecidableEq X] in
/-- Exercise 2.2.28 (p. 60), second half: `0 ≤ A ≤ B` implies `ρ(A) ≤ ρ(B)`, by Gelfand's
formula and `‖Aᵏ‖ ≤ ‖Bᵏ‖`. -/
theorem specRad_le_of_le [Nonempty X] {A B : Matrix X X ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) : specRad A ≤ specRad B := by
  classical
  refine le_of_tendsto_of_tendsto' (tendsto_norm_pow_rpow A) (tendsto_norm_pow_rpow B) fun k => ?_
  refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by positivity)
  refine norm_le_norm_of_abs_le fun i j => ?_
  have hAk := pow_nonneg_entries hA k i j
  have hBk := (pow_nonneg_entries hA k i j).trans (pow_le_pow_entries hA hAB k i j)
  rw [abs_of_nonneg hAk, abs_of_nonneg hBk]
  exact pow_le_pow_entries hA hAB k i j

/-- Row sums of absolute values are bounded by the ℓ∞ operator norm. -/
theorem rowsum_abs_le_norm (A : Matrix X X ℝ) (i : X) : ∑ j, |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have : (∑ j, ‖A i j‖₊ : NNReal) ≤ univ.sup fun i => ∑ j, ‖A i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (mem_univ i)
  have h := NNReal.coe_le_coe.2 this
  simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h

/-- The ℓ∞ operator norm is bounded by a bound on the row sums of absolute values. -/
theorem norm_le_of_rowsum_abs_le (A : Matrix X X ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have : (univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le fun i _ => ?_
    have hi := h i
    exact (NNReal.coe_le_coe (r₁ := ∑ j, ‖A i j‖₊) (r₂ := c.toNNReal)).1
      (by simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal c hc] using hi)
  have h2 := NNReal.coe_le_coe.2 this
  rwa [Real.coe_toNNReal c hc] at h2

/-- Each entry is bounded in absolute value by the ℓ∞ operator norm. -/
theorem abs_entry_le_norm (A : Matrix X X ℝ) (i j : X) : |A i j| ≤ ‖A‖ :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (A i j)) (mem_univ j)).trans (rowsum_abs_le_norm A i)

/-- For `A ≥ 0` with all row sums equal to `c`, `‖A‖ = c`. -/
theorem norm_eq_of_rowsum_eq [Nonempty X] (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, ∑ j, A i j = c) : ‖A‖ = c := by
  have habs : ∀ i, ∑ j, |A i j| = c := fun i => by
    rw [← h i]
    exact sum_congr rfl fun j _ => abs_of_nonneg (hA i j)
  refine le_antisymm (norm_le_of_rowsum_abs_le A hc fun i => (habs i).le) ?_
  obtain ⟨i⟩ : Nonempty X := inferInstance
  exact (habs i).symm.le.trans (rowsum_abs_le_norm A i)

/-- `ρ(A) ≤ ‖A‖`. -/
theorem specRad_le_norm [Nonempty X] (A : Matrix X X ℝ) : specRad A ≤ ‖A‖ := by
  have := ENNReal.toReal_mono ENNReal.coe_ne_top
    (spectralRadius_le_nnnorm (𝕜 := ℂ) (complexify A))
  rwa [ENNReal.coe_toReal, coe_nnnorm, norm_complexify] at this

/-- Every eigenvalue is bounded in modulus by the spectral radius. -/
theorem norm_le_specRad_of_mem_spectrum [Nonempty X] (A : Matrix X X ℝ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify A)) : ‖μ‖ ≤ specRad A := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have h1 : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (complexify A) := by
    rw [spectralRadius_eq_of_unital (𝕜 := ℂ) (complexify A)]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify A)) => (‖k‖₊ : ENNReal)) μ hμ
  have := ENNReal.toReal_mono (spectralRadius_complexify_ne_top A) h1
  rwa [ENNReal.coe_toReal, coe_nnnorm] at this

omit [DecidableEq X] in
/-- For `A ≥ 0` with all row sums equal to `c`, `ρ(A) = c`: the constant vector is an eigenvector
with eigenvalue `c`, and `‖A‖ = c`. -/
theorem specRad_eq_of_rowsum_eq [Nonempty X] (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ∑ j, A i j = c) : specRad A = c := by
  classical
  refine le_antisymm ((specRad_le_norm A).trans (norm_eq_of_rowsum_eq A hA hc h).le) ?_
  have hmem : (c : ℂ) ∈ spectrum ℂ (complexify A) := by
    rw [mem_spectrum_iff_eigenpair]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h0
      have := congrFun h0 (Classical.arbitrary X)
      simp at this
    · funext i
      simp only [mulVec, dotProduct, complexify_apply, mul_one, Pi.smul_apply, smul_eq_mul]
      rw [← Complex.ofReal_sum, h i]
  have := norm_le_specRad_of_mem_spectrum A hmem
  rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] at this

omit [DecidableEq X] in
/-- For `A ≥ 0` with all column sums equal to `c`, `ρ(A) = c`, by transposition. -/
theorem specRad_eq_of_colsum_eq [Nonempty X] (A : Matrix X X ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ j, ∑ i, A i j = c) : specRad A = c := by
  classical
  rw [← specRad_transpose]
  exact specRad_eq_of_rowsum_eq Aᵀ (fun i j => hA j i) hc h

/-- Entrywise Gelfand bound: for `r > ρ(A)`, `|(Aᵏ)ᵢⱼ| ≤ rᵏ` for all large `k`. -/
theorem eventually_abs_entry_pow_le [Nonempty X] (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) (i j : X) : ∀ᶠ k : ℕ in atTop, |(A ^ k) i j| ≤ r ^ k :=
  (eventually_norm_pow_le A hr).mono fun k hk => (abs_entry_le_norm (A ^ k) i j).trans hk

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Order stability, order completeness and order continuity

Copied from `GeneralStates/AbstractDecisionProcesses` (module `OrderTheory`), namespace renamed to
`Miao.LinearQuadratic.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 2, Appendix A: §A.1.2.10 (order
stability, Lemma A.1.5) and §A.5.1 (chain and Dedekind completeness, Knaster–Tarski, order
continuity, Tarski–Kantorovich), and Lemma A.5.19. These are the order-theoretic inputs of
Chapter 2.

* `S` is *order stable* if it has a unique fixed point `v̄`, and `v ≼ Sv ⟹ v ≼ v̄` and
  `Sv ≼ v ⟹ v̄ ≼ v`; *strongly* order stable if moreover `Sⁿv ↑ v̄` and `Sⁿv ↓ v̄`.
  **Lemma A.1.5**: both notions are self-dual.
* A poset is *chain complete* if every chain (the empty one included) has a supremum and an
  infimum. **Theorem A.5.2** (Knaster–Tarski) and **Lemma A.5.3**, proved by Zorn's lemma: an
  order preserving self-map of a chain complete poset has a fixed point above any point it maps
  up and below any point it maps down; if the fixed point is unique, the map is order stable.
  **Example A.5.1**: order intervals of `ℝ^X` are chain complete.
* *Countably Dedekind complete* posets; **Example A.5.2** (`ℝ^X`); **Exercise A.5.5** (duality).
* *Order continuous* maps; **Lemma A.5.5** (they are order preserving) and **Theorem A.5.6**
  (Tarski–Kantorovich).
* **Lemma A.5.19**: on a space with a closed partial order, an order preserving globally stable
  map is strongly order stable.
-/

open Set Function Filter Topology

namespace Miao.LinearQuadratic.SS

variable {V : Type*} [PartialOrder V]

/-! ### Order stability -/

/-- `S` is order stable on `V` (§A.1.2.10). -/
def OrderStable (S : V → V) : Prop :=
  ∃ u, S u = u ∧ (∀ w, S w = w → w = u) ∧ (∀ v, v ≤ S v → v ≤ u) ∧ ∀ v, S v ≤ v → u ≤ v

/-- `vₙ ↑ v`: `(vₙ)` is increasing with supremum `v`. -/
def IncreasesTo (f : ℕ → V) (v : V) : Prop := Monotone f ∧ IsLUB (range f) v

/-- `vₙ ↓ v`: `(vₙ)` is decreasing with infimum `v`. -/
def DecreasesTo (f : ℕ → V) (v : V) : Prop := Antitone f ∧ IsGLB (range f) v

/-- `S` is strongly order stable on `V` (§A.1.2.10): order stable with `Sⁿv ↑ v̄` when `v ≼ Sv`
and `Sⁿv ↓ v̄` when `Sv ≼ v`. -/
def StronglyOrderStable (S : V → V) : Prop :=
  ∃ u, S u = u ∧ (∀ w, S w = w → w = u) ∧ (∀ v, v ≤ S v → IncreasesTo (fun n => S^[n] v) u) ∧
    ∀ v, S v ≤ v → DecreasesTo (fun n => S^[n] v) u

/-- Upward and downward stability around a fixed point force it to be the only one. -/
theorem orderStable_of_up_down {S : V → V} {u : V} (hu : S u = u)
    (hup : ∀ v, v ≤ S v → v ≤ u) (hdown : ∀ v, S v ≤ v → u ≤ v) : OrderStable S :=
  ⟨u, hu, fun w hw => le_antisymm (hup w hw.ge) (hdown w hw.le), hup, hdown⟩

/-- Strong order stability implies order stability. -/
theorem StronglyOrderStable.orderStable {S : V → V} (h : StronglyOrderStable S) :
    OrderStable S := by
  obtain ⟨u, hu, -, hup, hdown⟩ := h
  refine orderStable_of_up_down hu (fun v hv => ?_) fun v hv => ?_
  · simpa using (hup v hv).2.1 ⟨0, rfl⟩
  · simpa using (hdown v hv).2.1 ⟨0, rfl⟩

/-- The map `S` read on the order dual. -/
def dualMap (S : V → V) : Vᵒᵈ → Vᵒᵈ := OrderDual.toDual ∘ S ∘ OrderDual.ofDual

/-- **Lemma A.1.5** (p. 337): `S` is order stable on `V` iff it is order stable on `V^∂`. -/
theorem orderStable_dual_iff (S : V → V) : OrderStable (dualMap S) ↔ OrderStable S := by
  constructor
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.ofDual u) (congrArg OrderDual.ofDual hu)
      (fun v hv => hdown (OrderDual.toDual v) hv) fun v hv => hup (OrderDual.toDual v) hv
  · rintro ⟨u, hu, -, hup, hdown⟩
    exact orderStable_of_up_down (u := OrderDual.toDual u) (congrArg OrderDual.toDual hu)
      (fun v hv => hdown (OrderDual.ofDual v) hv) fun v hv => hup (OrderDual.ofDual v) hv

omit [PartialOrder V] in
theorem dualMap_iterate (S : V → V) (n : ℕ) (v : Vᵒᵈ) :
    (dualMap S)^[n] v = OrderDual.toDual (S^[n] (OrderDual.ofDual v)) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply, ih]; rfl

/-- **Lemma A.1.5** (p. 337): strong order stability is self-dual too. -/
theorem stronglyOrderStable_dual_iff (S : V → V) :
    StronglyOrderStable (dualMap S) ↔ StronglyOrderStable S := by
  constructor
  · rintro ⟨u, hu, huniq, hup, hdown⟩
    refine ⟨OrderDual.ofDual u, congrArg OrderDual.ofDual hu,
      fun w hw => congrArg OrderDual.ofDual (huniq (OrderDual.toDual w)
        (congrArg OrderDual.toDual hw)), fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨hm, hl⟩ := hdown (OrderDual.toDual v) hv
      simp only [dualMap_iterate] at hm hl
      exact ⟨fun a b hab => hm hab, hl⟩
    · obtain ⟨hm, hl⟩ := hup (OrderDual.toDual v) hv
      simp only [dualMap_iterate] at hm hl
      exact ⟨fun a b hab => hm hab, hl⟩
  · rintro ⟨u, hu, huniq, hup, hdown⟩
    refine ⟨OrderDual.toDual u, congrArg OrderDual.toDual hu,
      fun w hw => congrArg OrderDual.toDual (huniq (OrderDual.ofDual w)
        (congrArg OrderDual.ofDual hw)), fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨hm, hl⟩ := hdown (OrderDual.ofDual v) hv
      simp only [dualMap_iterate]
      exact ⟨fun a b hab => hm hab, hl⟩
    · obtain ⟨hm, hl⟩ := hup (OrderDual.ofDual v) hv
      simp only [dualMap_iterate]
      exact ⟨fun a b hab => hm hab, hl⟩

/-! ### Chain completeness and Knaster–Tarski -/

/-- `V` is chain complete (§A.5.1.1): every chain, including the empty one, has a supremum and
an infimum. -/
def ChainComplete (V : Type*) [PartialOrder V] : Prop :=
  ∀ C : Set V, IsChain (· ≤ ·) C → (∃ s, IsLUB C s) ∧ ∃ i, IsGLB C i

/-- A chain complete poset has a least element. -/
theorem ChainComplete.exists_least (h : ChainComplete V) : ∃ b : V, ∀ v, b ≤ v := by
  obtain ⟨⟨b, hb⟩, -⟩ := h ∅ (Set.pairwise_empty _)
  exact ⟨b, fun v => hb.2 fun _ hx => absurd hx (notMem_empty _)⟩

/-- **Knaster–Tarski** for chain complete posets (Theorem A.5.2), upward form: an order
preserving `S` has a fixed point above every `v` with `v ≼ Sv`. -/
theorem ChainComplete.exists_fixedPt_ge (h : ChainComplete V) {S : V → V} (hS : Monotone S)
    {v : V} (hv : v ≤ S v) : ∃ u, S u = u ∧ v ≤ u := by
  set s := {u | v ≤ u ∧ u ≤ S u}
  obtain ⟨m, hvm, hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    obtain ⟨⟨ub, hub⟩, -⟩ := h c hc
    refine ⟨ub, ⟨(hcs hy).1.trans (hub.1 hy), hub.2 fun z hz => ?_⟩, fun z hz => hub.1 hz⟩
    exact (hcs hz).2.trans (hS (hub.1 hz))) v ⟨le_rfl, hv⟩
  have hm : m ∈ s := hmax.prop
  have hSm : S m ∈ s := ⟨hvm.trans hm.2, hS hm.2⟩
  exact ⟨m, le_antisymm (hmax.2 hSm hm.2) hm.2, hvm⟩

/-- **Knaster–Tarski** for chain complete posets, downward form: an order preserving `S` has a
fixed point below every `v` with `Sv ≼ v`. -/
theorem ChainComplete.exists_fixedPt_le (h : ChainComplete V) {S : V → V} (hS : Monotone S)
    {v : V} (hv : S v ≤ v) : ∃ u, S u = u ∧ u ≤ v := by
  obtain ⟨b, hb⟩ := h.exists_least
  set s := {u | u ≤ S u ∧ u ≤ v}
  obtain ⟨m, -, hmax⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    obtain ⟨⟨ub, hub⟩, -⟩ := h c hc
    refine ⟨ub, ⟨hub.2 fun z hz => (hcs hz).1.trans (hS (hub.1 hz)),
      hub.2 fun z hz => (hcs hz).2⟩, fun z hz => hub.1 hz⟩) b ⟨hb _, hb _⟩
  have hm : m ∈ s := hmax.prop
  have hSm : S m ∈ s := ⟨hS hm.1, (hS hm.2).trans hv⟩
  exact ⟨m, le_antisymm (hmax.2 hSm hm.1) hm.1, hm.2⟩

/-- **Theorem A.5.2** (Knaster–Tarski, p. 369): an order preserving self-map of a chain complete
poset has a fixed point. -/
theorem ChainComplete.exists_fixedPt (h : ChainComplete V) {S : V → V} (hS : Monotone S) :
    ∃ u, S u = u := by
  obtain ⟨b, hb⟩ := h.exists_least
  obtain ⟨u, hu, -⟩ := h.exists_fixedPt_ge hS (hb (S b))
  exact ⟨u, hu⟩

/-- **Lemma A.5.3** (p. 370): an order preserving self-map of a chain complete poset with at most
one fixed point is order stable. -/
theorem ChainComplete.orderStable (h : ChainComplete V) {S : V → V} (hS : Monotone S)
    (huniq : ∀ u w, S u = u → S w = w → u = w) : OrderStable S := by
  obtain ⟨u, hu⟩ := h.exists_fixedPt hS
  refine orderStable_of_up_down hu (fun v hv => ?_) fun v hv => ?_
  · obtain ⟨w, hw, hvw⟩ := h.exists_fixedPt_ge hS hv
    exact huniq w u hw hu ▸ hvw
  · obtain ⟨w, hw, hwv⟩ := h.exists_fixedPt_le hS hv
    exact huniq w u hw hu ▸ hwv

/-- **Example A.5.1** and **Lemma A.5.4** (p. 369): an order interval `[a, b]` of a conditionally
complete lattice, such as `ℝ^X`, is chain complete. -/
theorem chainComplete_Icc {L : Type*} [ConditionallyCompleteLattice L] {a b : L} (hab : a ≤ b) :
    ChainComplete (Icc a b) := by
  have : Fact (a ≤ b) := ⟨hab⟩
  intro C _
  exact ⟨⟨sSup C, isLUB_sSup C⟩, ⟨sInf C, isGLB_sInf C⟩⟩

/-! ### Dedekind completeness -/

/-- `V` is countably Dedekind complete (§A.5.1.2): every nonempty countable set that is bounded
above has a supremum, and every one bounded below has an infimum. -/
def CountablyDedekindComplete (V : Type*) [PartialOrder V] : Prop :=
  ∀ A : Set V, A.Nonempty → A.Countable →
    (BddAbove A → ∃ s, IsLUB A s) ∧ (BddBelow A → ∃ i, IsGLB A i)

/-- **Example A.5.2** (p. 370): `ℝ^X`, and more generally any conditionally complete lattice, is
(countably) Dedekind complete. -/
theorem countablyDedekindComplete_of_conditionallyCompleteLattice {L : Type*}
    [ConditionallyCompleteLattice L] : CountablyDedekindComplete L :=
  fun A hne _ => ⟨fun hb => ⟨sSup A, isLUB_csSup hne hb⟩, fun hb => ⟨sInf A, isGLB_csInf hne hb⟩⟩

/-- **Exercise A.5.5** (p. 371): the dual of a countably Dedekind complete poset is countably
Dedekind complete. -/
theorem CountablyDedekindComplete.dual (h : CountablyDedekindComplete V) :
    CountablyDedekindComplete Vᵒᵈ := fun A hne hc => by
  obtain ⟨h1, h2⟩ := h (OrderDual.ofDual '' A) (hne.image _) (hc.image _)
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨i, hi⟩ := h2 ⟨OrderDual.ofDual b, by rintro _ ⟨a, ha, rfl⟩; exact hb ha⟩
    exact ⟨OrderDual.toDual i, fun a ha => hi.1 ⟨a, ha, rfl⟩,
      fun w hw => hi.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩
  · obtain ⟨b, hb⟩ := hb
    obtain ⟨t, ht⟩ := h1 ⟨OrderDual.ofDual b, by rintro _ ⟨a, ha, rfl⟩; exact hb ha⟩
    exact ⟨OrderDual.toDual t, fun a ha => ht.1 ⟨a, ha, rfl⟩,
      fun w hw => ht.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩

/-! ### Order continuity -/

/-- `S` is order continuous (§A.5.1.3): `vₙ ↑ v` implies that `Svₙ` has supremum `Sv`. -/
def OrderContinuous {W : Type*} [PartialOrder W] (S : V → W) : Prop :=
  ∀ (f : ℕ → V) (v : V), Monotone f → IsLUB (range f) v → IsLUB (range (S ∘ f)) (S v)

/-- **Lemma A.5.5** (p. 372): order continuous maps are order preserving. -/
theorem OrderContinuous.monotone {W : Type*} [PartialOrder W] {S : V → W}
    (h : OrderContinuous S) : Monotone S := by
  intro v v' hvv'
  have hf : Monotone fun n : ℕ => if n = 0 then v else v' := by
    intro a b hab
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · simp [ha, hb]
      · simp [ha, hb, hvv']
    · have hb : b ≠ 0 := fun hb => ha (Nat.le_zero.1 (hb ▸ hab))
      simp [ha, hb]
  have hsup : IsLUB (range fun n : ℕ => if n = 0 then v else v') v' := by
    refine ⟨?_, fun w hw => hw ⟨1, by simp⟩⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · simp [hn, hvv']
    · simp [hn]
  have := (h _ _ hf hsup).1 ⟨0, rfl⟩
  simpa using this

/-- A monotone sequence and its shift have the same suprema. -/
theorem isLUB_range_succ_iff {f : ℕ → V} (hf : Monotone f) (v : V) :
    IsLUB (range fun n => f (n + 1)) v ↔ IsLUB (range f) v := by
  have key : upperBounds (range fun n => f (n + 1)) = upperBounds (range f) := by
    ext w
    simp only [mem_upperBounds, forall_mem_range]
    exact ⟨fun h n => (hf (Nat.le_succ n)).trans (h n), fun h n => h (n + 1)⟩
  rw [IsLUB, IsLUB, key]

/-- **Theorem A.5.6** (Tarski–Kantorovich, p. 372): if `S` is order continuous, `V` is countably
Dedekind complete, and `v_a ≼ v_b` with `v_a ≼ Sv_a` and `Sv_b ≼ v_b`, then `Sⁿv_a ↑ v̄` for
some fixed point `v̄` of `S`. -/
theorem tarski_kantorovich (hV : CountablyDedekindComplete V) {S : V → V}
    (hS : OrderContinuous S) {va vb : V} (hab : va ≤ vb) (ha : va ≤ S va) (hb : S vb ≤ vb) :
    ∃ v, S v = v ∧ IncreasesTo (fun n => S^[n] va) v := by
  have hmono := hS.monotone
  have hinc : Monotone fun n => S^[n] va := monotone_nat_of_le_succ fun n => by
    have := hmono.iterate n ha
    rwa [← iterate_succ_apply] at this
  have hbdd : ∀ n, S^[n] va ≤ vb := by
    intro n
    induction n with
    | zero => exact hab
    | succ n ih => rw [iterate_succ_apply']; exact (hmono ih).trans hb
  obtain ⟨v, hv⟩ := (hV _ (range_nonempty _) (countable_range _)).1
    ⟨vb, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
  refine ⟨v, ?_, hinc, hv⟩
  have h1 := hS _ _ hinc hv
  have h2 : IsLUB (range fun n => S^[n + 1] va) v := (isLUB_range_succ_iff hinc v).2 hv
  have h3 : (S ∘ fun n => S^[n] va) = fun n => S^[n + 1] va := by
    funext n; simp only [Function.comp_apply, iterate_succ_apply']
  rw [h3] at h1
  exact h1.unique h2

/-! ### Global stability (`GloballyStable`, §A.2.2.1, is restated in `Basics`) -/

/-- **Lemma A.5.19** (p. 380): on a space whose partial order is closed, an order preserving
globally stable map is strongly order stable. -/
theorem stronglyOrderStable_of_globallyStable {W : Type*} [TopologicalSpace W] [PartialOrder W]
    [OrderClosedTopology W] {S : W → W} (hS : Monotone S) (hg : GloballyStable S) :
    StronglyOrderStable S := by
  obtain ⟨u, hu, huniq, hlim⟩ := hg
  refine ⟨u, hu, huniq, fun v hv => ?_, fun v hv => ?_⟩
  · have hinc : Monotone fun n => S^[n] v := monotone_nat_of_le_succ fun n => by
      have := hS.iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hinc, isLUB_of_tendsto_atTop hinc (hlim v)⟩
  · have hdec : Antitone fun n => S^[n] v := antitone_nat_of_succ_le fun n => by
      have := hS.iterate n hv
      rwa [← iterate_succ_apply] at this
    exact ⟨hdec, isGLB_of_tendsto_atTop hdec (hlim v)⟩

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Abstract decision processes on posets

Copied from `GeneralStates/AbstractDecisionProcesses` (module `ADP`), namespace renamed to
`Miao.LinearQuadratic.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.1 (pp. 59–68).

An **abstract dynamic program** (ADP, Definition 2.1.1) is a partially ordered value space `V`
with a nonempty family of order preserving policy operators `T_σ`, `σ ∈ Σ`. Unlike Volume 1,
the existence of greedy policies is a property (regularity), not part of the definition.

* Greedy policies (Definition 2.1.2), `V_G` (2.2); well-posed, finite, regular, order stable and
  strongly order stable ADPs (§2.1.1.2).
* The Bellman equation (Definition 2.1.3) and the Bellman operator `T = ⋁_σ T_σ`
  (Definition 2.1.4), defined where the supremum exists; **Lemma 2.1.1** (`T` exists and is
  order preserving on `V_G`, and `T_σ v = Tv` iff `σ` is `v`-greedy).
* `V_G`, `V_U`, `V_Σ` (Definition 2.1.5) and **Lemma 2.1.2** (`V_Σ ∩ V_G ⊆ V_U`).
* Optimal policies, the value function `v* = ⋁_σ v_σ` and Bellman's principle of optimality
  (Definition 2.1.6); **Lemma 2.1.3**; the fundamental optimality properties (B1)–(B3)
  (Definition 2.1.7) and **Proposition 2.1.4**; **Exercise 2.1.1**.
* **Theorem 2.1.5** (with downward stability, a fixed point of `T` in `V_G` is equivalent to the
  fundamental optimality properties), **Corollary 2.1.6** and **Theorem 2.1.7** (regular and
  well-posed on a chain complete space).
-/

open Set Function

namespace Miao.LinearQuadratic.SS

/-- An abstract dynamic program `(V, 𝕋)` (Definition 2.1.1): order preserving self-maps `T_σ` of a
poset `V`, indexed by a nonempty set of policies `Σ`. -/
structure ADP (V P : Type*) [PartialOrder V] where
  /-- the policy operators -/
  T : P → V → V
  mono : ∀ σ, Monotone (T σ)
  nonempty : Nonempty P

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- `σ` is `v`-greedy (Definition 2.1.2, (2.1)): `T_τ v ≼ T_σ v` for all `τ`. -/
def IsGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T τ v ≤ A.T σ v

/-- `V_G`: the points at which a greedy policy exists (2.2). -/
def VG : Set V := {v | ∃ σ, A.IsGreedy v σ}

/-- Well-posed (§2.1.1.2): every `T_σ` has a unique fixed point. -/
def WellPosed : Prop := ∀ σ, ∃! v, A.T σ v = v

/-- Finite (§2.1.1.2): the family `𝕋` of policy operators is finite. -/
def IsFinite : Prop := (range A.T).Finite

/-- Regular (§2.1.1.2): `V_G = V`. -/
def Regular : Prop := ∀ v, ∃ σ, A.IsGreedy v σ

/-- Order stable (§2.1.1.2): every `T_σ` is order stable. -/
def IsOrderStable : Prop := ∀ σ, OrderStable (A.T σ)

/-- Strongly order stable (§2.1.1.2). -/
def IsStronglyOrderStable : Prop := ∀ σ, StronglyOrderStable (A.T σ)

/-- `w` is `Tv = ⋁_σ T_σ v` (Definition 2.1.4), when the supremum exists. -/
def IsBellmanValue (v w : V) : Prop := IsLUB (range fun σ => A.T σ v) w

/-- `v` satisfies the Bellman equation `v = ⋁_σ T_σ v` (Definition 2.1.3, (2.3)). -/
def SolvesBellman (v : V) : Prop := A.IsBellmanValue v v

theorem IsStronglyOrderStable.isOrderStable {A : ADP V P} (h : A.IsStronglyOrderStable) :
    A.IsOrderStable := fun σ => (h σ).orderStable

/-- Order stability implies well-posedness. -/
theorem IsOrderStable.wellPosed {A : ADP V P} (h : A.IsOrderStable) : A.WellPosed := fun σ => by
  obtain ⟨u, hu, huniq, -⟩ := h σ
  exact ⟨u, hu, huniq⟩

theorem regular_iff : A.Regular ↔ A.VG = univ :=
  ⟨fun h => eq_univ_of_forall h, fun h v => (h ▸ mem_univ v : v ∈ A.VG)⟩

/-! ### The Bellman operator -/

/-- A chosen `v`-greedy policy (the greedy selector of §2.2.1.1); arbitrary off `V_G`. -/
noncomputable def greedy (v : V) : P := @Classical.epsilon P A.nonempty fun σ => A.IsGreedy v σ

theorem isGreedy_greedy {v : V} (hv : v ∈ A.VG) : A.IsGreedy v (A.greedy v) := by
  obtain ⟨σ, hσ⟩ := hv
  exact @Classical.epsilon_spec P (fun σ => A.IsGreedy v σ) ⟨σ, hσ⟩

/-- The Bellman operator `Tv = T_σ v` for the chosen `v`-greedy `σ`; on `V_G` it is
`⋁_σ T_σ v` (Lemma 2.1.1). -/
noncomputable def bellman (v : V) : V := A.T (A.greedy v) v

/-- **Lemma 2.1.1 (ii)(a)** (p. 63): `T_σ v ≼ Tv` on `V_G`. -/
theorem T_le_bellman (σ : P) {v : V} (hv : v ∈ A.VG) : A.T σ v ≤ A.bellman v :=
  A.isGreedy_greedy hv σ

/-- **Lemma 2.1.1 (i)** (p. 63): on `V_G`, `Tv` is the supremum `⋁_σ T_σ v`. -/
theorem isBellmanValue_bellman {v : V} (hv : v ∈ A.VG) : A.IsBellmanValue v (A.bellman v) :=
  ⟨by rintro _ ⟨σ, rfl⟩; exact A.T_le_bellman σ hv, fun _ hw => hw ⟨_, rfl⟩⟩

/-- **Lemma 2.1.1 (ii)(b)** (p. 63): on `V_G`, `T_σ v = Tv` iff `σ` is `v`-greedy. -/
theorem isGreedy_iff {v : V} (hv : v ∈ A.VG) (σ : P) : A.IsGreedy v σ ↔ A.T σ v = A.bellman v :=
  ⟨fun h => le_antisymm (A.T_le_bellman σ hv) (h _), fun h τ => h ▸ A.T_le_bellman τ hv⟩

/-- A supremum attained by a policy operator is a greedy value. -/
theorem isGreedy_of_isBellmanValue {v w : V} {σ : P} (h : A.IsBellmanValue v w)
    (hσ : A.T σ v = w) : A.IsGreedy v σ := fun τ => hσ ▸ h.1 ⟨τ, rfl⟩

/-- On `V_G`, the Bellman equation reads `Tv = v`. -/
theorem solvesBellman_iff {v : V} (hv : v ∈ A.VG) : A.SolvesBellman v ↔ A.bellman v = v :=
  ⟨fun h => (A.isBellmanValue_bellman hv).unique h, fun h => by
    have := A.isBellmanValue_bellman hv
    rwa [h] at this⟩

/-- **Lemma 2.1.1 (i)** (p. 63): `T` is order preserving on `V_G`. -/
theorem bellman_mono {v w : V} (hw : w ∈ A.VG) (h : v ≤ w) :
    A.bellman v ≤ A.bellman w :=
  (A.mono _ h).trans (A.T_le_bellman _ hw)

/-! ### Subsets of the value space -/

/-- `V_U`: the points of `V_G` mapped up by `T` (Definition 2.1.5). -/
def VU : Set V := {v | v ∈ A.VG ∧ v ≤ A.bellman v}

/-- `V_Σ` (written `VSig`): the fixed points of policy operators (Definition 2.1.5). -/
def VSig : Set V := {v | ∃ σ, A.T σ v = v}

/-- **Lemma 2.1.2** (p. 64): `V_Σ ∩ V_G ⊆ V_U`. -/
theorem VSig_inter_VG_subset : A.VSig ∩ A.VG ⊆ A.VU := by
  rintro v ⟨⟨σ, hσ⟩, hv⟩
  exact ⟨hv, hσ.symm.le.trans (A.T_le_bellman σ hv)⟩

/-! ### Optimality -/

variable {A}

/-- The `σ`-value function of a well-posed ADP: the unique fixed point of `T_σ`. -/
noncomputable def vσ (hw : A.WellPosed) (σ : P) : V := (hw σ).exists.choose

theorem T_vσ (hw : A.WellPosed) (σ : P) : A.T σ (A.vσ hw σ) = A.vσ hw σ :=
  (hw σ).exists.choose_spec

theorem eq_vσ (hw : A.WellPosed) {σ : P} {v : V} (h : A.T σ v = v) : v = A.vσ hw σ :=
  (hw σ).unique h (T_vσ hw σ)

theorem VSig_eq_range (hw : A.WellPosed) : A.VSig = range (A.vσ hw) := by
  ext v
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (eq_vσ hw hσ).symm⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, T_vσ hw σ⟩

variable (A)

/-- `σ` is optimal (§2.1.2.1): `v_σ` is a greatest element of `V_Σ`. -/
def IsOptimal (hw : A.WellPosed) (σ : P) : Prop := IsGreatest A.VSig (A.vσ hw σ)

/-- `v` is the value function `v* = ⋁_σ v_σ` (§2.1.2.1). -/
def IsValueFunction (v : V) : Prop := IsLUB A.VSig v

/-- Bellman's principle of optimality (Definition 2.1.6, (2.5)): the optimal policies are the
`v*`-greedy ones (both sets being empty when `v*` does not exist). -/
def BellmanPrinciple (hw : A.WellPosed) : Prop :=
  ∀ σ, A.IsOptimal hw σ ↔ ∃ v, A.IsValueFunction v ∧ A.IsGreedy v σ

/-- The fundamental optimality properties (Definition 2.1.7): (B1) an optimal policy exists,
(B2) `v*` exists and is the unique solution of the Bellman equation in `V_G`, and (B3) Bellman's
principle of optimality holds. -/
def FundamentalOptimality (hw : A.WellPosed) : Prop :=
  (∃ σ, A.IsOptimal hw σ) ∧
    (∃ v, A.IsValueFunction v ∧ v ∈ A.VG ∧ A.SolvesBellman v ∧
      ∀ w ∈ A.VG, A.SolvesBellman w → w = v) ∧
    A.BellmanPrinciple hw

variable {A}

/-- An optimal policy's value is the value function (p. 64). -/
theorem IsOptimal.isValueFunction {hw : A.WellPosed} {σ : P} (h : A.IsOptimal hw σ) :
    A.IsValueFunction (A.vσ hw σ) := h.isLUB

/-- If `v* = v_σ`, then `σ` is optimal (p. 64). -/
theorem isOptimal_of_isValueFunction {hw : A.WellPosed} {σ : P}
    (h : A.IsValueFunction (A.vσ hw σ)) : A.IsOptimal hw σ :=
  ⟨⟨σ, T_vσ hw σ⟩, h.1⟩

theorem isOptimal_iff {hw : A.WellPosed} {σ : P} {v : V} (hv : A.IsValueFunction v) :
    A.IsOptimal hw σ ↔ A.vσ hw σ = v :=
  ⟨fun h => h.isValueFunction.unique hv, fun h => isOptimal_of_isValueFunction (h ▸ hv)⟩

/-- **Lemma 2.1.3 (i)** (p. 65): if `v*` exists and satisfies the Bellman equation, Bellman's
principle of optimality holds. -/
theorem bellmanPrinciple_of_solves {hw : A.WellPosed} {v : V} (hv : A.IsValueFunction v)
    (hb : A.SolvesBellman v) : A.BellmanPrinciple hw := by
  intro σ
  constructor
  · intro ho
    refine ⟨v, hv, A.isGreedy_of_isBellmanValue hb ?_⟩
    rw [← (isOptimal_iff hv).1 ho]
    exact T_vσ hw σ
  · rintro ⟨w, hw', hg⟩
    have hwv : w = v := hw'.unique hv
    rw [hwv] at hg
    -- `T_σ v* = v*`, so `v_σ = v*`
    have : A.T σ v = v := le_antisymm (hb.1 ⟨σ, rfl⟩) (hb.2 (by rintro _ ⟨τ, rfl⟩; exact hg τ))
    exact (isOptimal_iff hv).2 (eq_vσ hw this).symm

/-- **Lemma 2.1.3 (ii)** (p. 65): `v*` exists in `V_G` and satisfies the Bellman equation iff an
optimal policy exists and Bellman's principle of optimality holds. -/
theorem exists_solves_iff (hw : A.WellPosed) :
    (∃ v, A.IsValueFunction v ∧ v ∈ A.VG ∧ A.SolvesBellman v) ↔
      (∃ σ, A.IsOptimal hw σ) ∧ A.BellmanPrinciple hw := by
  constructor
  · rintro ⟨v, hv, hvG, hb⟩
    have hT := (A.solvesBellman_iff hvG).1 hb
    have hg := A.isGreedy_greedy hvG
    have hσ : A.T (A.greedy v) v = v := hT
    exact ⟨⟨_, (isOptimal_iff hv).2 (eq_vσ hw hσ).symm⟩, bellmanPrinciple_of_solves hv hb⟩
  · rintro ⟨⟨σ, ho⟩, hbp⟩
    obtain ⟨v, hv, hg⟩ := (hbp σ).1 ho
    have hvσ := (isOptimal_iff hv).1 ho
    refine ⟨v, hv, ⟨σ, hg⟩, ?_⟩
    have hTv : A.T σ v = v := hvσ ▸ T_vσ hw σ
    exact ⟨by rintro _ ⟨τ, rfl⟩; exact (hg τ).trans hTv.le,
      fun _ hu => hTv.symm.le.trans (hu ⟨σ, rfl⟩)⟩

/-- **Proposition 2.1.4** (p. 66): the fundamental optimality properties hold iff `v*` exists and
is the unique solution of the Bellman equation in `V_G`. -/
theorem fundamentalOptimality_iff (hw : A.WellPosed) :
    A.FundamentalOptimality hw ↔ ∃ v, A.IsValueFunction v ∧ v ∈ A.VG ∧ A.SolvesBellman v ∧
      ∀ w ∈ A.VG, A.SolvesBellman w → w = v := by
  constructor
  · exact fun h => h.2.1
  · intro h
    obtain ⟨v, hv, hvG, hb, huniq⟩ := h
    obtain ⟨hex, hbp⟩ := (exists_solves_iff hw).1 ⟨v, hv, hvG, hb⟩
    exact ⟨hex, ⟨v, hv, hvG, hb, huniq⟩, hbp⟩

/-- **Exercise 2.1.1** (p. 66): if `v*` exists and is the unique fixed point of `T` in `V`, then
a policy is optimal iff `Tv_σ = v_σ`. (Regularity, assumed in the book so that `T` is defined
everywhere, is not needed when `Tv = v` is read as the Bellman equation (2.3).) -/
theorem isOptimal_iff_solvesBellman (hw : A.WellPosed) {v : V} (hv : A.IsValueFunction v)
    (huniq : ∀ w, A.SolvesBellman w ↔ w = v) (σ : P) :
    A.IsOptimal hw σ ↔ A.SolvesBellman (A.vσ hw σ) := by
  rw [isOptimal_iff hv, huniq]

/-- **Theorem 2.1.5** (p. 66): if `A` is well-posed and `T_σ v ≼ v ⟹ v_σ ≼ v`, then `T` has a
fixed point in `V_G` iff the fundamental optimality properties hold. -/
theorem fundamentalOptimality_iff_exists_fixed (hw : A.WellPosed)
    (hdown : ∀ σ v, A.T σ v ≤ v → A.vσ hw σ ≤ v) :
    (∃ v ∈ A.VG, A.SolvesBellman v) ↔ A.FundamentalOptimality hw := by
  constructor
  · rintro ⟨v, hvG, hb⟩
    -- a fixed point of `T` in `V_G` is a greatest element of `V_Σ`
    have key : ∀ u ∈ A.VG, A.SolvesBellman u → IsGreatest A.VSig u ∧ u ∈ A.VSig := by
      intro u huG hub
      have hT := (A.solvesBellman_iff huG).1 hub
      have hσ : A.T (A.greedy u) u = u := hT
      have hu : u = A.vσ hw (A.greedy u) := eq_vσ hw hσ
      refine ⟨⟨⟨_, hσ⟩, ?_⟩, ⟨_, hσ⟩⟩
      rintro _ ⟨τ, hτ⟩
      rw [eq_vσ hw hτ]
      exact hdown τ u (hub.1 ⟨τ, rfl⟩)
    obtain ⟨hgv, -⟩ := key v hvG hb
    refine (fundamentalOptimality_iff hw).2 ⟨v, hgv.isLUB, hvG, hb, fun w hwG hwb => ?_⟩
    exact (key w hwG hwb).1.unique hgv
  · rintro ⟨-, ⟨v, -, hvG, hb, -⟩, -⟩
    exact ⟨v, hvG, hb⟩

/-- **Corollary 2.1.6** (p. 67): if `A` is order stable and `T` has a fixed point in `V_G`, the
fundamental optimality properties hold. -/
theorem IsOrderStable.fundamentalOptimality (h : A.IsOrderStable) {v : V} (hvG : v ∈ A.VG)
    (hb : A.SolvesBellman v) : A.FundamentalOptimality h.wellPosed := by
  refine (fundamentalOptimality_iff_exists_fixed h.wellPosed fun σ w hw' => ?_).1 ⟨v, hvG, hb⟩
  obtain ⟨u, hu, -, -, hdown⟩ := h σ
  rw [← eq_vσ h.wellPosed hu]
  exact hdown w hw'

/-- In a chain complete space, a well-posed ADP is order stable (Lemma A.5.3). -/
theorem WellPosed.isOrderStable (hw : A.WellPosed) (hV : ChainComplete V) : A.IsOrderStable :=
  fun σ => hV.orderStable (A.mono σ) fun _ _ hu hw' => (hw σ).unique hu hw'

/-- **Theorem 2.1.7** (p. 67): a regular, well-posed ADP on a chain complete space satisfies the
fundamental optimality properties. -/
theorem fundamentalOptimality_of_chainComplete (hw : A.WellPosed) (hr : A.Regular)
    (hV : ChainComplete V) : A.FundamentalOptimality hw := by
  have hos := hw.isOrderStable hV
  have hmono : Monotone A.bellman := fun _ w h => A.bellman_mono (hr w) h
  obtain ⟨v, hv⟩ := hV.exists_fixedPt hmono
  exact hos.fundamentalOptimality (hr v) ((A.solvesBellman_iff (hr v)).2 hv)

end ADP

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Algorithms and convergence

Copied from `GeneralStates/AbstractDecisionProcesses` (module `Algorithms`), namespace renamed to
`Miao.LinearQuadratic.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.2.1–§2.2.2 (pp. 68–74).

Value function iteration iterates the Bellman operator `T`; Howard policy iteration iterates the
Howard operator `Hv = v_σ` and optimistic policy iteration the operator `Wv = T_σ^m v`, where `σ`
is the `v`-greedy policy chosen by a greedy selector (Definition 2.2.1). As in the book, every
result below holds for every greedy selector `g`.

* **Lemma 2.2.1** (L1)–(L3), **Lemma 2.2.2** and Remark 2.2.1.
* Convergence of VFI, OPI and HPI (Definition 2.2.2); **Exercise 2.2.1**; **Lemmas 2.2.3–2.2.4**;
  **Corollary 2.2.5** (VFI convergence gives OPI and HPI convergence).
* **Theorem 2.2.6** (finite ADPs: the fundamental optimality properties and finite termination of
  HPI), **Theorem 2.2.7** (chain complete value spaces) and **Theorem 2.2.8** (countably Dedekind
  complete value spaces with order bounded, order continuous ADPs); Exercise 2.2.2.
-/

open Set Function

namespace Miao.LinearQuadratic.SS

namespace ADP

variable {V P : Type*} [PartialOrder V] {A : ADP V P}

variable (A) in
/-- A greedy selector: a choice of `v`-greedy policy at every `v` (§2.2.1.1). -/
def IsSelector (g : V → P) : Prop := ∀ v, A.IsGreedy v (g v)

theorem Regular.isSelector_greedy (hr : A.Regular) : A.IsSelector A.greedy := fun v =>
  A.isGreedy_greedy (hr v)

variable (A) in
/-- The Howard policy operator `Hv = v_σ` for the selected `v`-greedy `σ` (Definition 2.2.1). -/
noncomputable def howard (hw : A.WellPosed) (g : V → P) (v : V) : V := A.vσ hw (g v)

variable (A) in
/-- The optimistic policy operator `Wv = T_σ^m v` for the selected `v`-greedy `σ` (2.6). -/
def opt (m : ℕ) (g : V → P) (v : V) : V := (A.T (g v))^[m] v

/-- With a greedy selector, `T_{g(v)} v = Tv`. -/
theorem IsSelector.T_eq {g : V → P} (hg : A.IsSelector g) (hr : A.Regular) (v : V) :
    A.T (g v) v = A.bellman v :=
  (A.isGreedy_iff (hr v) (g v)).1 (hg v)

theorem mem_VU_iff (hr : A.Regular) {v : V} : v ∈ A.VU ↔ v ≤ A.bellman v :=
  ⟨fun h => h.2, fun h => ⟨hr v, h⟩⟩

/-- **Lemma 2.2.1 (L1)** (p. 69): a fixed point of `H` is a fixed point of `T`. -/
theorem bellman_eq_of_howard_eq (hw : A.WellPosed) (hr : A.Regular) {g : V → P}
    (hg : A.IsSelector g) {v : V} (h : A.howard hw g v = v) : A.bellman v = v := by
  rw [← hg.T_eq hr]
  have : A.T (g v) (A.vσ hw (g v)) = A.vσ hw (g v) := T_vσ hw _
  rw [show A.vσ hw (g v) = v from h] at this
  exact this

/-- The iterates `T_σᵏ v` increase when `v ≼ T_σ v`. -/
theorem iterate_mono_of_le {σ : P} {v : V} (hv : v ≤ A.T σ v) :
    Monotone fun k => (A.T σ)^[k] v :=
  monotone_nat_of_le_succ fun k => by
    have := (A.mono σ).iterate k hv
    rwa [← iterate_succ_apply] at this

/-- **Lemma 2.2.1 (L3)** (p. 69): for `v ∈ V_U` and `m ≥ 1`, `Tv ≼ Wv ≼ Tᵐv`. -/
theorem bellman_le_opt (hr : A.Regular) {g : V → P} (hg : A.IsSelector g) {m : ℕ} (hm : 1 ≤ m)
    {v : V} (hv : v ∈ A.VU) : A.bellman v ≤ A.opt m g v ∧ A.opt m g v ≤ A.bellman^[m] v := by
  have hT := hg.T_eq hr v
  have hle : v ≤ A.T (g v) v := hT ▸ hv.2
  refine ⟨?_, ?_⟩
  · rw [← hT]
    simpa [opt] using A.iterate_mono_of_le hle hm
  · -- `T_σ ≼ T` and both are order preserving
    have hTmono : Monotone A.bellman := fun _ w h => A.bellman_mono (hr w) h
    have : ∀ k u, (A.T (g v))^[k] u ≤ A.bellman^[k] u := by
      intro k
      induction k with
      | zero => intro u; exact le_rfl
      | succ k ih =>
        intro u
        rw [iterate_succ_apply', iterate_succ_apply']
        exact (A.T_le_bellman _ (hr _)).trans (hTmono (ih u))
    exact this m v

/-- (2.9) (p. 70): for `v ∈ V_U` with `σ` its selected greedy policy and `m ≥ 1`,
`v ≼ Tv = T_σ v ≼ T_σ^m v = Wv ≼ v_σ = Hv`, under upward stability of the policy operators. -/
theorem chain_2_9 (hw : A.WellPosed) (hr : A.Regular) (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ)
    {g : V → P} (hg : A.IsSelector g) {m : ℕ} (hm : 1 ≤ m) {v : V} (hv : v ∈ A.VU) :
    v ≤ A.bellman v ∧ A.bellman v ≤ A.opt m g v ∧ A.opt m g v ≤ A.howard hw g v := by
  have hT := hg.T_eq hr v
  have hle : v ≤ A.T (g v) v := hT ▸ hv.2
  refine ⟨hv.2, (A.bellman_le_opt hr hg hm hv).1, ?_⟩
  -- `T_σᵏ v ≼ T_σᵏ v_σ = v_σ`
  have hvσ := hup _ _ hle
  have : ∀ k, (A.T (g v))^[k] v ≤ A.vσ hw (g v) := by
    intro k
    induction k with
    | zero => exact hvσ
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (A.mono _ ih).trans (T_vσ hw _).le
  exact this m

/-- **Lemma 2.2.1 (L2)** (p. 69): `T`, `W` and `H` map `V_U` into itself. -/
theorem mapsTo_VU (hw : A.WellPosed) (hr : A.Regular) {g : V → P} (hg : A.IsSelector g)
    (m : ℕ) :
    MapsTo A.bellman A.VU A.VU ∧ MapsTo (A.opt m g) A.VU A.VU ∧
      MapsTo (A.howard hw g) A.VU A.VU := by
  refine ⟨fun v hv => (mem_VU_iff hr).2 (A.bellman_mono (hr _) hv.2), fun v hv => ?_,
    fun v _ => A.VSig_inter_VG_subset ⟨⟨g v, T_vσ hw _⟩, hr _⟩⟩
  -- `Wv = T_σ T_σ^{m−1} v ≼ T T_σ^{m−1} T v = T T_σ^m v = T Wv`
  have hT := hg.T_eq hr v
  have hle : v ≤ A.T (g v) v := hT ▸ hv.2
  refine (mem_VU_iff hr).2 ?_
  calc A.opt m g v = (A.T (g v))^[m] v := rfl
    _ ≤ (A.T (g v))^[m] (A.T (g v) v) := (A.mono _).iterate m hle
    _ = A.T (g v) ((A.T (g v))^[m] v) := by rw [← iterate_succ_apply, iterate_succ_apply']
    _ ≤ A.bellman ((A.T (g v))^[m] v) := A.T_le_bellman _ (hr _)

/-- (2.8) (p. 70): for `u ≼ v` in `V_U`, `Tu ≼ Wv` and `Tu ≼ Hv`. -/
theorem bellman_le_of_le (hw : A.WellPosed) (hr : A.Regular)
    (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ) {g : V → P} (hg : A.IsSelector g) {m : ℕ}
    (hm : 1 ≤ m) {u v : V} (hv : v ∈ A.VU) (huv : u ≤ v) :
    A.bellman u ≤ A.opt m g v ∧ A.bellman u ≤ A.howard hw g v := by
  obtain ⟨-, h2, h3⟩ := A.chain_2_9 hw hr hup hg hm hv
  have := A.bellman_mono (hr v) huv
  exact ⟨this.trans h2, this.trans (h2.trans h3)⟩

/-- **Lemma 2.2.2** (p. 70) and Remark 2.2.1: for a regular ADP whose policy operators are
upward stable, `v ∈ V_U` gives `Tⁿv ≼ Wⁿv` and `Tⁿv ≼ Hⁿv`, and `Tⁿv`, `Wⁿv`, `Hⁿv` increase. -/
theorem iterates_of_mem_VU (hw : A.WellPosed) (hr : A.Regular)
    (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ) {g : V → P} (hg : A.IsSelector g) {m : ℕ}
    (hm : 1 ≤ m) {v : V} (hv : v ∈ A.VU) :
    (∀ n, A.bellman^[n] v ≤ (A.opt m g)^[n] v ∧ A.bellman^[n] v ≤ (A.howard hw g)^[n] v) ∧
      Monotone (fun n => A.bellman^[n] v) ∧ Monotone (fun n => (A.opt m g)^[n] v) ∧
      Monotone (fun n => (A.howard hw g)^[n] v) := by
  obtain ⟨hT, hW, hH⟩ := A.mapsTo_VU hw hr hg m
  refine ⟨fun n => ?_, ?_, ?_, ?_⟩
  · induction n with
    | zero => exact ⟨le_rfl, le_rfl⟩
    | succ n ih =>
      rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply']
      exact ⟨(A.bellman_le_of_le hw hr hup hg hm (hW.iterate n hv) ih.1).1,
        (A.bellman_le_of_le hw hr hup hg hm (hH.iterate n hv) ih.2).2⟩
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [iterate_succ_apply']
    exact (hT.iterate n hv).2
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [iterate_succ_apply']
    obtain ⟨h1, h2, -⟩ := A.chain_2_9 hw hr hup hg hm (hW.iterate n hv)
    exact h1.trans h2
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [iterate_succ_apply']
    obtain ⟨h1, h2, h3⟩ := A.chain_2_9 hw hr hup hg hm (hH.iterate n hv)
    exact h1.trans (h2.trans h3)

/-! ### Convergence -/

variable (A) in
/-- VFI converges (Definition 2.2.2): `Tⁿv ↑ v*` for all `v ∈ V_U`. -/
def VFIConverges (vstar : V) : Prop := ∀ v ∈ A.VU, IncreasesTo (fun n => A.bellman^[n] v) vstar

variable (A) in
/-- OPI converges (Definition 2.2.2): `Wⁿv ↑ v*` for all `v ∈ V_U` and every step size `m`. -/
def OPIConverges (g : V → P) (vstar : V) : Prop :=
  ∀ m, 1 ≤ m → ∀ v ∈ A.VU, IncreasesTo (fun n => (A.opt m g)^[n] v) vstar

variable (A) in
/-- HPI converges (Definition 2.2.2): `Hⁿv ↑ v*` for all `v ∈ V_U`. -/
def HPIConverges (hw : A.WellPosed) (g : V → P) (vstar : V) : Prop :=
  ∀ v ∈ A.VU, IncreasesTo (fun n => (A.howard hw g)^[n] v) vstar

/-- With step `m = 1`, OPI is VFI. -/
theorem opt_one (hr : A.Regular) {g : V → P} (hg : A.IsSelector g) : A.opt 1 g = A.bellman := by
  funext v
  simp only [opt, iterate_one]
  exact hg.T_eq hr v

/-- **Exercise 2.2.1** (p. 71): convergence of OPI implies convergence of VFI. -/
theorem OPIConverges.vfi (hr : A.Regular) {g : V → P} (hg : A.IsSelector g) {vstar : V}
    (h : A.OPIConverges g vstar) : A.VFIConverges vstar := fun v hv => by
  simpa [opt_one hr hg] using h 1 le_rfl v hv

/-- **Lemma 2.2.3** (p. 71): for an order stable ADP, every `v ∈ V_U` lies below `v*`. -/
theorem le_vstar_of_mem_VU (hos : A.IsOrderStable) {vstar : V}
    (hvs : A.IsValueFunction vstar) {v : V} (hv : v ∈ A.VU) : v ≤ vstar := by
  have hle : v ≤ A.T (A.greedy v) v := hv.2
  obtain ⟨u, hu, -, hup, -⟩ := hos (A.greedy v)
  exact (hup v hle).trans (hvs.1 ⟨_, hu⟩)

/-- Upward stability of order stable policy operators, in terms of `v_σ`. -/
theorem IsOrderStable.le_vσ (hos : A.IsOrderStable) (σ : P) (v : V) (h : v ≤ A.T σ v) :
    v ≤ A.vσ hos.wellPosed σ := by
  obtain ⟨u, hu, -, hup, -⟩ := hos σ
  rw [← eq_vσ hos.wellPosed hu]
  exact hup v h

/-- Downward stability of order stable policy operators, in terms of `v_σ`. -/
theorem IsOrderStable.vσ_le (hos : A.IsOrderStable) (σ : P) (v : V) (h : A.T σ v ≤ v) :
    A.vσ hos.wellPosed σ ≤ v := by
  obtain ⟨u, hu, -, -, hdown⟩ := hos σ
  rw [← eq_vσ hos.wellPosed hu]
  exact hdown v h

/-- **Lemma 2.2.4** (p. 71): `v ≼ Tⁿv ≼ Wⁿv ≼ v*` and `v ≼ Tⁿv ≼ Hⁿv ≼ v*` for `v ∈ V_U`. -/
theorem iterates_le_vstar (hos : A.IsOrderStable) (hr : A.Regular) {g : V → P}
    (hg : A.IsSelector g) {m : ℕ} (hm : 1 ≤ m) {vstar : V} (hvs : A.IsValueFunction vstar)
    {v : V} (hv : v ∈ A.VU) (n : ℕ) :
    v ≤ A.bellman^[n] v ∧ A.bellman^[n] v ≤ (A.opt m g)^[n] v ∧
      (A.opt m g)^[n] v ≤ vstar ∧ A.bellman^[n] v ≤ (A.howard hos.wellPosed g)^[n] v ∧
      (A.howard hos.wellPosed g)^[n] v ≤ vstar := by
  have hw := hos.wellPosed
  obtain ⟨hcmp, hTm, -, -⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hg hm hv
  obtain ⟨-, hW, hH⟩ := A.mapsTo_VU hw hr hg m
  exact ⟨by simpa using hTm (Nat.zero_le n), (hcmp n).1,
    le_vstar_of_mem_VU hos hvs (hW.iterate n hv), (hcmp n).2,
    le_vstar_of_mem_VU hos hvs (hH.iterate n hv)⟩

/-- A sequence squeezed between a sequence increasing to `v*` and `v*` increases to `v*`. -/
theorem increasesTo_of_squeeze {f h : ℕ → V} {vstar : V} (hf : IncreasesTo f vstar)
    (hh : Monotone h) (hfh : ∀ n, f n ≤ h n) (hhv : ∀ n, h n ≤ vstar) : IncreasesTo h vstar :=
  ⟨hh, by rintro _ ⟨n, rfl⟩; exact hhv n, fun u hu =>
    hf.2.2 (by rintro _ ⟨n, rfl⟩; exact (hfh n).trans (hu ⟨n, rfl⟩))⟩

/-- **Corollary 2.2.5** (p. 71): for a regular, order stable ADP, convergence of VFI implies
convergence of OPI and HPI, for every greedy selector. -/
theorem VFIConverges.opi_hpi (hos : A.IsOrderStable) (hr : A.Regular) {g : V → P}
    (hg : A.IsSelector g) {vstar : V} (hvs : A.IsValueFunction vstar)
    (h : A.VFIConverges vstar) :
    A.OPIConverges g vstar ∧ A.HPIConverges hos.wellPosed g vstar := by
  refine ⟨fun m hm v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨hcmp, -, hW, -⟩ := A.iterates_of_mem_VU hos.wellPosed hr hos.le_vσ hg hm hv
    exact increasesTo_of_squeeze (h v hv) hW (fun n => (hcmp n).1)
      fun n => (A.iterates_le_vstar hos hr hg hm hvs hv n).2.2.1
  · obtain ⟨hcmp, -, -, hH⟩ := A.iterates_of_mem_VU hos.wellPosed hr hos.le_vσ hg le_rfl hv
    exact increasesTo_of_squeeze (h v hv) hH (fun n => (hcmp n).2)
      fun n => (A.iterates_le_vstar hos hr hg le_rfl hvs hv n).2.2.2.2

/-- `V_U` is nonempty for a regular, well-posed ADP (it contains `V_Σ`). -/
theorem VU_nonempty (hw : A.WellPosed) (hr : A.Regular) : A.VU.Nonempty := by
  obtain ⟨σ⟩ := A.nonempty
  exact ⟨_, A.VSig_inter_VG_subset ⟨⟨σ, T_vσ hw σ⟩, hr _⟩⟩

/-- For a finite ADP, `V_Σ` is finite: `v_σ` depends on `σ` only through `T_σ`. -/
theorem IsFinite.VSig_finite (hfin : A.IsFinite) (hw : A.WellPosed) : A.VSig.Finite := by
  rw [VSig_eq_range hw]
  let φ : (V → V) → V := fun F => A.vσ hw (@Classical.epsilon P A.nonempty fun τ => A.T τ = F)
  refine (hfin.image φ).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨A.T σ, ⟨σ, rfl⟩, ?_⟩
  have hτ : A.T (@Classical.epsilon P A.nonempty fun τ => A.T τ = A.T σ) = A.T σ :=
    @Classical.epsilon_spec P (fun τ => A.T τ = A.T σ) ⟨σ, rfl⟩
  have hfix : A.T (@Classical.epsilon P A.nonempty fun τ => A.T τ = A.T σ) (A.vσ hw σ) =
      A.vσ hw σ := by rw [hτ]; exact T_vσ hw σ
  exact (eq_vσ hw hfix).symm

/-- A monotone sequence in a finite set repeats a value at consecutive indices. -/
theorem exists_succ_eq_of_finite {f : ℕ → V} (hf : Monotone f) {s : Set V} (hs : s.Finite)
    (hfs : ∀ n, f n ∈ s) : ∃ n, f (n + 1) = f n := by
  by_contra hne
  push Not at hne
  have hsm : StrictMono f :=
    strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne (hf (Nat.le_succ n)) (hne n).symm
  exact (infinite_range_of_injective hsm.injective) (hs.subset (by rintro _ ⟨n, rfl⟩; exact hfs n))

/-- **Theorem 2.2.6** (p. 72): a regular, order stable, finite ADP satisfies the fundamental
optimality properties, and HPI reaches `v*` in finitely many steps from every `v ∈ V_U`, for
every greedy selector. -/
theorem fundamentalOptimality_of_finite (hos : A.IsOrderStable) (hr : A.Regular)
    (hfin : A.IsFinite) :
    A.FundamentalOptimality hos.wellPosed ∧ ∀ g, A.IsSelector g → ∀ v ∈ A.VU,
      ∃ n, A.IsValueFunction ((A.howard hos.wellPosed g)^[n] v) := by
  have hw := hos.wellPosed
  -- HPI from `v ∈ V_U` reaches a fixed point of `H`, hence of `T`
  have key : ∀ g, A.IsSelector g → ∀ v ∈ A.VU, ∃ n,
      A.bellman ((A.howard hw g)^[n] v) = (A.howard hw g)^[n] v := by
    intro g hg v hv
    obtain ⟨-, -, -, hH⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hg le_rfl hv
    obtain ⟨n, hn⟩ := exists_succ_eq_of_finite (f := fun n => (A.howard hw g)^[n + 1] v)
      (fun a b hab => hH (Nat.succ_le_succ hab)) (hfin.VSig_finite hw) fun n => by
        rw [iterate_succ_apply']
        exact ⟨g _, T_vσ hw _⟩
    refine ⟨n + 1, A.bellman_eq_of_howard_eq hw hr hg ?_⟩
    rw [← iterate_succ_apply' (A.howard hw g)]
    exact hn
  obtain ⟨v₀, hv₀⟩ := A.VU_nonempty hw hr
  obtain ⟨n, hn⟩ := key _ hr.isSelector_greedy v₀ hv₀
  have hfop := hos.fundamentalOptimality (hr _) ((A.solvesBellman_iff (hr _)).2 hn)
  refine ⟨hfop, fun g hg v hv => ?_⟩
  obtain ⟨-, ⟨u, hu, -, -, huniq⟩, -⟩ := hfop
  obtain ⟨k, hk⟩ := key g hg v hv
  exact ⟨k, huniq _ (hr _) ((A.solvesBellman_iff (hr _)).2 hk) ▸ hu⟩

/-- The value function and an optimal policy under the fundamental optimality properties. -/
theorem FundamentalOptimality.exists_vstar {hw : A.WellPosed} (h : A.FundamentalOptimality hw) :
    ∃ vstar σ, A.IsValueFunction vstar ∧ A.vσ hw σ = vstar ∧ vstar ∈ A.VG ∧
      A.SolvesBellman vstar := by
  obtain ⟨⟨σ, hσ⟩, ⟨v, hv, hvG, hb, -⟩, -⟩ := h
  exact ⟨v, σ, hv, (isOptimal_iff hv).1 hσ, hvG, hb⟩

/-- **Theorem 2.2.7** (p. 72): a regular, strongly order stable ADP on a chain complete space
satisfies the fundamental optimality properties, and VFI, OPI and HPI all converge. -/
theorem convergence_of_chainComplete (hsos : A.IsStronglyOrderStable) (hr : A.Regular)
    (hV : ChainComplete V) :
    A.FundamentalOptimality hsos.isOrderStable.wellPosed ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧
          A.HPIConverges hsos.isOrderStable.wellPosed g vstar := by
  have hos := hsos.isOrderStable
  have hw := hos.wellPosed
  have hfop := fundamentalOptimality_of_chainComplete hw hr hV
  obtain ⟨vstar, σ, hvs, hσ, -, -⟩ := hfop.exists_vstar
  obtain ⟨b, hb⟩ := hV.exists_least
  have hvfi : A.VFIConverges vstar := by
    intro v hv
    obtain ⟨-, hTmono, -, -⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hr.isSelector_greedy le_rfl hv
    -- `T_σⁿ ⊥ ↑ v_σ = v*` and `T_σⁿ ⊥ ≼ Tⁿ ⊥ ≼ Tⁿ v`
    obtain ⟨u, hu, -, hup, -⟩ := hsos σ
    have hinc := hup b (hb _)
    rw [eq_vσ hw hu, hσ] at hinc
    have hTmono' : Monotone A.bellman := fun _ w h => A.bellman_mono (hr w) h
    have hcmp : ∀ n, (A.T σ)^[n] b ≤ A.bellman^[n] v := by
      intro n
      induction n with
      | zero => exact hb v
      | succ n ih =>
        rw [iterate_succ_apply', iterate_succ_apply']
        exact (A.T_le_bellman σ (hr _)).trans (hTmono' ih)
    exact increasesTo_of_squeeze hinc hTmono hcmp fun n =>
      (A.iterates_le_vstar hos hr hr.isSelector_greedy le_rfl hvs hv n).2.2.1.trans_eq' (by
        simp [opt_one hr hr.isSelector_greedy])
  exact ⟨hfop, vstar, hvs, hvfi, fun g hg => hvfi.opi_hpi hos hr hg hvs⟩

variable (A) in
/-- Order bounded (§2.2.2.3): some `u` has `T_σ u ≼ u` for all `σ`. -/
def OrderBounded : Prop := ∃ u, ∀ σ, A.T σ u ≤ u

variable (A) in
/-- Order continuous (§2.2.2.3): every `T_σ` is order continuous. -/
def IsOrderContinuous : Prop := ∀ σ, OrderContinuous (A.T σ)

/-- **Exercise 2.2.2** (p. 73): for an order stable ADP with `T_σ u ≼ u` for all `σ`, every
`v ∈ V_U` lies below `u` (regularity, assumed in the book, is not needed). -/
theorem le_of_orderBounded (hos : A.IsOrderStable) {u : V}
    (hu : ∀ σ, A.T σ u ≤ u) {v : V} (hv : v ∈ A.VU) : v ≤ u :=
  (hos.le_vσ _ v hv.2).trans (hos.vσ_le _ u (hu _))

/-- **Theorem 2.2.8** (p. 73): a regular, order stable, order bounded and order continuous ADP on
a countably Dedekind complete space satisfies the fundamental optimality properties, and VFI,
OPI and HPI all converge. -/
theorem convergence_of_dedekind (hos : A.IsOrderStable) (hr : A.Regular)
    (hV : CountablyDedekindComplete V) (hb : A.OrderBounded) (hc : A.IsOrderContinuous) :
    A.FundamentalOptimality hos.wellPosed ∧
      ∃ vstar, A.IsValueFunction vstar ∧ A.VFIConverges vstar ∧
        ∀ g, A.IsSelector g → A.OPIConverges g vstar ∧
          A.HPIConverges hos.wellPosed g vstar := by
  have hw := hos.wellPosed
  obtain ⟨u, hu⟩ := hb
  -- from any `v ∈ V_U`, `Tⁿv` increases to a fixed point of `T`
  have key : ∀ v ∈ A.VU, ∃ vbar, A.bellman vbar = vbar ∧
      IncreasesTo (fun n => A.bellman^[n] v) vbar := by
    intro v hv
    obtain ⟨-, hTmono, -, -⟩ := A.iterates_of_mem_VU hw hr hos.le_vσ hr.isSelector_greedy le_rfl hv
    obtain ⟨-, hT⟩ := A.mapsTo_VU hw hr hr.isSelector_greedy 1
    have hbdd : ∀ n, A.bellman^[n] v ≤ u := fun n =>
      le_of_orderBounded hos hu ((A.mapsTo_VU hw hr hr.isSelector_greedy 1).1.iterate n hv)
    obtain ⟨vbar, hvbar⟩ := (hV _ (range_nonempty _) (countable_range _)).1
      ⟨u, by rintro _ ⟨n, rfl⟩; exact hbdd n⟩
    refine ⟨vbar, le_antisymm ?_ ?_, hTmono, hvbar⟩
    · -- `Tv̄ = T_σ v̄ = ⋁ T_σ vₙ ≼ ⋁ T vₙ = ⋁ vₙ₊₁ = v̄`
      have hσ := (hc (A.greedy vbar)) _ _ hTmono hvbar
      have hshift := (isLUB_range_succ_iff hTmono vbar).2 hvbar
      refine hσ.2 fun _ ⟨n, hn⟩ => hn ▸ ?_
      exact (A.T_le_bellman _ (hr _)).trans (by
        rw [← iterate_succ_apply' A.bellman]
        exact hshift.1 ⟨n, rfl⟩)
    · -- `vₙ₊₁ = T vₙ ≼ T v̄`
      have hshift := (isLUB_range_succ_iff hTmono vbar).2 hvbar
      refine hshift.2 fun _ ⟨n, hn⟩ => hn ▸ ?_
      change A.bellman^[n + 1] v ≤ A.bellman vbar
      rw [iterate_succ_apply']
      exact A.bellman_mono (hr _) (hvbar.1 ⟨n, rfl⟩)
  obtain ⟨v₀, hv₀⟩ := A.VU_nonempty hw hr
  obtain ⟨vbar, hfix, -⟩ := key v₀ hv₀
  have hfop := hos.fundamentalOptimality (hr _) ((A.solvesBellman_iff (hr _)).2 hfix)
  obtain ⟨-, ⟨vstar, hvs, -, -, huniq⟩, -⟩ := id hfop
  have hvfi : A.VFIConverges vstar := by
    intro v hv
    obtain ⟨w, hwfix, hwinc⟩ := key v hv
    rwa [huniq w (hr _) ((A.solvesBellman_iff (hr _)).2 hwfix)] at hwinc
  exact ⟨hfop, vstar, hvs, hvfi, fun g hg => hvfi.opi_hpi hos hr hg hvs⟩

end ADP

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Minimization

Copied from `GeneralStates/AbstractDecisionProcesses` (module `Minimization`), namespace renamed to
`Miao.LinearQuadratic.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.2.3 (pp. 74–78).

Minimization is maximization on the order dual. The min-notions are defined as in §2.2.3.1, and
the dual ADP `(V, 𝕋)^∂ = (V^∂, 𝕋)` (§2.2.3.2) translates each into its max-counterpart.

* **Exercise 2.2.3**: the dual is an ADP, and it is self-dual.
* **Exercise 2.2.4** (i)–(ix): min-greedy, min-regular, min-order bounded, `T▿`, `W▿`, `H▿`,
  `v▿*`, min-optimal and `V▿_G` are the dual's max-notions.
* **Exercise 2.2.5** (Bellman's principle of min-optimality) and **Exercise 2.2.6** (the
  fundamental min-optimality properties and min-convergence of VFI, OPI and HPI).
* **Theorem 2.2.9** (min-version of Theorem 2.1.5) and **Corollary 2.2.10**.
-/

open Set Function

namespace Miao.LinearQuadratic.SS

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- The dual ADP `(V^∂, 𝕋)` (§2.2.3.2) and **Exercise 2.2.3**: it is an ADP. -/
def dual : ADP Vᵒᵈ P where
  T σ := dualMap (A.T σ)
  mono σ _ _ h := A.mono σ h
  nonempty := A.nonempty

/-- Every ADP is self-dual (p. 77). -/
theorem dual_dual : A.dual.dual = A := rfl

/-! ### Min-notions (§2.2.3.1) -/

/-- `σ` is `v`-min-greedy: `T_σ v ≼ T_τ v` for all `τ`. -/
def IsMinGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T σ v ≤ A.T τ v

/-- `V▿_G`: the points at which a min-greedy policy exists. -/
def VGmin : Set V := {v | ∃ σ, A.IsMinGreedy v σ}

/-- Min-regular: a `v`-min-greedy policy exists at every `v`. -/
def MinRegular : Prop := ∀ v, ∃ σ, A.IsMinGreedy v σ

/-- Min-order bounded: some `b` has `b ≼ T_σ b` for all `σ`. -/
def MinOrderBounded : Prop := ∃ b, ∀ σ, b ≤ A.T σ b

/-- `w` is `T▿v = ⋀_σ T_σ v`, the Bellman min-operator. -/
def IsMinBellmanValue (v w : V) : Prop := IsGLB (range fun σ => A.T σ v) w

/-- `v` satisfies the Bellman min-equation `T▿v = v`. -/
def SolvesMinBellman (v : V) : Prop := A.IsMinBellmanValue v v

/-- `v` is the min-value function `v▿* = ⋀_σ v_σ`. -/
def IsMinValueFunction (v : V) : Prop := IsGLB A.VSig v

/-- `σ` is min-optimal: `v_σ = v▿*`, i.e. `v_σ` is a least element of `V_Σ`. -/
def IsMinOptimal (hw : A.WellPosed) (σ : P) : Prop := IsLeast A.VSig (A.vσ hw σ)

/-- Bellman's principle of min-optimality. -/
def MinBellmanPrinciple (hw : A.WellPosed) : Prop :=
  ∀ σ, A.IsMinOptimal hw σ ↔ ∃ v, A.IsMinValueFunction v ∧ A.IsMinGreedy v σ

/-- The fundamental min-optimality properties (B1')–(B3'). -/
def MinFundamentalOptimality (hw : A.WellPosed) : Prop :=
  (∃ σ, A.IsMinOptimal hw σ) ∧
    (∃ v, A.IsMinValueFunction v ∧ v ∈ A.VGmin ∧ A.SolvesMinBellman v ∧
      ∀ w ∈ A.VGmin, A.SolvesMinBellman w → w = v) ∧
    A.MinBellmanPrinciple hw

/-! ### Exercise 2.2.4 -/

/-- **Exercise 2.2.4 (i)**: `σ` is `v`-min-greedy for `A` iff it is `v`-max-greedy for `A^∂`. -/
theorem isMinGreedy_iff (v : V) (σ : P) :
    A.IsMinGreedy v σ ↔ A.dual.IsGreedy (OrderDual.toDual v) σ := Iff.rfl

/-- **Exercise 2.2.4 (ii)**: `A` is min-regular iff `A^∂` is max-regular. -/
theorem minRegular_iff : A.MinRegular ↔ A.dual.Regular :=
  ⟨fun h v => h (OrderDual.ofDual v), fun h v => h (OrderDual.toDual v)⟩

/-- **Exercise 2.2.4 (iii)**: `A` is min-order bounded iff `A^∂` is max-order bounded. -/
theorem minOrderBounded_iff : A.MinOrderBounded ↔ A.dual.OrderBounded :=
  ⟨fun ⟨b, hb⟩ => ⟨OrderDual.toDual b, hb⟩, fun ⟨b, hb⟩ => ⟨OrderDual.ofDual b, hb⟩⟩

/-- **Exercise 2.2.4 (iv)**: `T▿v` exists iff `T^∂v` does, and they agree. -/
theorem isMinBellmanValue_iff (v w : V) :
    A.IsMinBellmanValue v w ↔ A.dual.IsBellmanValue (OrderDual.toDual v) (OrderDual.toDual w) :=
  Iff.rfl

/-- **Exercise 2.2.4 (ix)**: `V▿_G = V_G^∂`. -/
theorem VGmin_eq : A.VGmin = OrderDual.ofDual ⁻¹' A.dual.VG := rfl

/-- `V_Σ` is the same for `A` and `A^∂`. -/
theorem dual_VSig : A.dual.VSig = OrderDual.ofDual ⁻¹' A.VSig := rfl

variable {A}

/-- Well-posedness transfers to the dual. -/
theorem WellPosed.dual (hw : A.WellPosed) : A.dual.WellPosed := hw

/-- The `σ`-value functions of `A` and `A^∂` agree. -/
theorem dual_vσ (hw : A.WellPosed) (σ : P) :
    OrderDual.ofDual (A.dual.vσ hw.dual σ) = A.vσ hw σ :=
  eq_vσ hw (T_vσ (A := A.dual) hw.dual σ)

/-- **Exercise 2.2.4 (vii)**: `v▿*` for `A` is `v*^∂` for `A^∂`. -/
theorem isMinValueFunction_iff (v : V) :
    A.IsMinValueFunction v ↔ A.dual.IsValueFunction (OrderDual.toDual v) := Iff.rfl

/-- **Exercise 2.2.4 (viii)**: `σ` is min-optimal for `A` iff max-optimal for `A^∂`. -/
theorem isMinOptimal_iff (hw : A.WellPosed) (σ : P) :
    A.IsMinOptimal hw σ ↔ A.dual.IsOptimal hw.dual σ := by
  unfold IsMinOptimal IsOptimal
  rw [← dual_vσ hw σ]
  rfl

/-- **Exercise 2.2.4 (v)–(vi)**: with a common selector, `W▿ = W^∂` and `H▿ = H^∂`. -/
theorem dual_opt_howard (hw : A.WellPosed) (m : ℕ) (g : V → P) (v : V) :
    A.dual.opt m (g ∘ OrderDual.ofDual) (OrderDual.toDual v) =
        OrderDual.toDual ((A.T (g v))^[m] v) ∧
      OrderDual.ofDual (A.dual.howard hw.dual (g ∘ OrderDual.ofDual) (OrderDual.toDual v)) =
        A.vσ hw (g v) :=
  ⟨dualMap_iterate _ m _, dual_vσ hw (g v)⟩

/-- **Exercise 2.2.5** (p. 77): Bellman's principle of min-optimality holds for `A` iff Bellman's
principle of max-optimality holds for `A^∂`. -/
theorem minBellmanPrinciple_iff (hw : A.WellPosed) :
    A.MinBellmanPrinciple hw ↔ A.dual.BellmanPrinciple hw.dual := by
  refine forall_congr' fun σ => ?_
  rw [isMinOptimal_iff hw σ]
  constructor
  · rintro h
    refine h.trans ⟨fun ⟨v, hv, hg⟩ => ⟨OrderDual.toDual v, hv, hg⟩, fun ⟨v, hv, hg⟩ =>
      ⟨OrderDual.ofDual v, hv, hg⟩⟩
  · rintro h
    refine h.trans ⟨fun ⟨v, hv, hg⟩ => ⟨OrderDual.ofDual v, hv, hg⟩, fun ⟨v, hv, hg⟩ =>
      ⟨OrderDual.toDual v, hv, hg⟩⟩

/-- **Exercise 2.2.6** (p. 78): the fundamental max-optimality properties hold for `A^∂` iff the
fundamental min-optimality properties hold for `A`. -/
theorem minFundamentalOptimality_iff (hw : A.WellPosed) :
    A.MinFundamentalOptimality hw ↔ A.dual.FundamentalOptimality hw.dual := by
  unfold MinFundamentalOptimality FundamentalOptimality
  rw [minBellmanPrinciple_iff hw]
  refine and_congr ⟨fun ⟨σ, h⟩ => ⟨σ, (isMinOptimal_iff hw σ).1 h⟩,
    fun ⟨σ, h⟩ => ⟨σ, (isMinOptimal_iff hw σ).2 h⟩⟩ (and_congr_left' ?_)
  constructor
  · rintro ⟨v, hv, hvG, hb, huniq⟩
    exact ⟨OrderDual.toDual v, hv, hvG, hb, fun w hwG hwb =>
      congrArg OrderDual.toDual (huniq (OrderDual.ofDual w) hwG hwb)⟩
  · rintro ⟨v, hv, hvG, hb, huniq⟩
    exact ⟨OrderDual.ofDual v, hv, hvG, hb, fun w hwG hwb =>
      congrArg OrderDual.ofDual (huniq (OrderDual.toDual w) hwG hwb)⟩

variable (A) in
/-- `V_D`: the points of `V▿_G` mapped down by `T▿`. -/
def VD : Set V := OrderDual.ofDual ⁻¹' A.dual.VU

variable (A) in
/-- min-VFI converges: `T▿ⁿv ↓ v▿*` for all `v ∈ V_D`. -/
def MinVFIConverges (vstar : V) : Prop :=
  ∀ v ∈ A.VD, DecreasesTo (fun n => OrderDual.ofDual (A.dual.bellman^[n] (OrderDual.toDual v)))
    vstar

/-- **Exercise 2.2.6 (i)** (p. 78): max-VFI converges for `A^∂` iff min-VFI converges for `A`. -/
theorem minVFIConverges_iff (vstar : V) :
    A.MinVFIConverges vstar ↔ A.dual.VFIConverges (OrderDual.toDual vstar) := by
  refine forall₂_congr fun v _ => ⟨fun ⟨hm, hl⟩ => ⟨fun a b h => hm h, hl⟩,
    fun ⟨hm, hl⟩ => ⟨fun a b h => hm h, hl⟩⟩

/-- **Theorem 2.2.9** (p. 78): if `A` is well-posed and `v ≼ T_σ v ⟹ v ≼ v_σ`, then `T▿` has a
fixed point in `V▿_G` iff the fundamental min-optimality properties hold. -/
theorem minFundamentalOptimality_iff_exists_fixed (hw : A.WellPosed)
    (hup : ∀ σ v, v ≤ A.T σ v → v ≤ A.vσ hw σ) :
    (∃ v ∈ A.VGmin, A.SolvesMinBellman v) ↔ A.MinFundamentalOptimality hw := by
  rw [minFundamentalOptimality_iff hw,
    ← fundamentalOptimality_iff_exists_fixed hw.dual fun σ v hv => by
      have := hup σ (OrderDual.ofDual v) hv
      rw [← dual_vσ hw σ] at this
      exact this]
  exact ⟨fun ⟨v, hv, hb⟩ => ⟨OrderDual.toDual v, hv, hb⟩,
    fun ⟨v, hv, hb⟩ => ⟨OrderDual.ofDual v, hv, hb⟩⟩

/-- **Corollary 2.2.10** (p. 78): if `A` is order stable and `T▿` has a fixed point in `V▿_G`,
the fundamental min-optimality properties hold. -/
theorem IsOrderStable.minFundamentalOptimality (hos : A.IsOrderStable) {v : V}
    (hvG : v ∈ A.VGmin) (hb : A.SolvesMinBellman v) :
    A.MinFundamentalOptimality hos.wellPosed :=
  (minFundamentalOptimality_iff_exists_fixed hos.wellPosed hos.le_vσ).1 ⟨v, hvG, hb⟩

end ADP

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# LQ control: the Riccati map and the control gain

Copied from `GeneralStates/AbstractDecisionProcesses` (module `LQAlgebra`), namespace renamed to
`Miao.LinearQuadratic.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.5.1–§2.3.5.2 and §2.3.5.6
(pp. 89–91, 94).

An LQ problem `(Q, R, A, B)` has `Q` positive semidefinite and `R` positive definite. For
positive semidefinite `P`, set `G(P) = BᵀPB + R` (positive definite), the Riccati map
`R(P) = AᵀPA − AᵀPB G(P)⁻¹ BᵀPA + Q` (2.27), the control gain `F(P) = −G(P)⁻¹BᵀPA` (2.28) and the
policy operators `T_F(P) = Q + FᵀRF + (A + BF)ᵀP(A + BF)` (2.32).

* **Exercise 2.3.13**: `R(P) = T_{F(P)}(P)`.
* **Exercise 2.3.14**: `R` maps the positive semidefinite cone `𝒫` into itself.
* **Exercise 2.3.16**: each `T_F` is an order preserving self-map of `(𝒫, ≼)` (Loewner order).
* **Lemma 2.3.3**: `F(P)x` is the unique minimizer of `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)`, by
  completing the square: the objective at `F(P)x + d` exceeds its minimum by `dᵀG(P)d`.
* **Exercise 2.3.17**: `F = F(P)` iff `T_F(P) ≼ T_G(P)` for every control matrix `G`.
-/

open Matrix

open scoped MatrixOrder

namespace Miao.LinearQuadratic.SS

/-- An LQ control problem `(Q, R, A, B)` (§2.3.5.1). -/
structure LQProblem (K U : Type*) [Fintype K] [Fintype U] where
  /-- the state transition matrix -/
  A : Matrix K K ℝ
  /-- the control matrix -/
  B : Matrix K U ℝ
  /-- the state cost -/
  Q : Matrix K K ℝ
  /-- the control cost -/
  R : Matrix U U ℝ
  Q_psd : Q.PosSemidef
  R_pd : R.PosDef

namespace LQProblem

variable {K U : Type*} [Fintype K] [Fintype U] (L : LQProblem K U)

/-- `G(P) = BᵀPB + R`. -/
def gainDen (P : Matrix K K ℝ) : Matrix U U ℝ := L.Bᵀ * P * L.B + L.R

/-- The policy operator (2.32): `T_F(P) = Q + FᵀRF + (A + BF)ᵀP(A + BF)`. -/
def TF (F : Matrix U K ℝ) (P : Matrix K K ℝ) : Matrix K K ℝ :=
  L.Q + Fᵀ * L.R * F + (L.A + L.B * F)ᵀ * P * (L.A + L.B * F)

/-- The one-period objective `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)` of (2.26). -/
def cost (P : Matrix K K ℝ) (x : K → ℝ) (u : U → ℝ) : ℝ :=
  x ⬝ᵥ (L.Q *ᵥ x) + u ⬝ᵥ (L.R *ᵥ u) +
    (L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))

/-! ### Positivity and quadratic forms -/

omit [Fintype U] in
theorem posSemidef_iff_real {n : Type*} [Fintype n] {M : Matrix n n ℝ} :
    M.PosSemidef ↔ Mᵀ = M ∧ ∀ x, 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rw [posSemidef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp

omit [Fintype U] in
theorem posDef_iff_real {n : Type*} [Fintype n] {M : Matrix n n ℝ} :
    M.PosDef ↔ Mᵀ = M ∧ ∀ ⦃x⦄, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x) := by
  rw [posDef_iff_dotProduct_mulVec, IsHermitian, conjTranspose_eq_transpose_of_trivial]
  simp

omit [Fintype U] in
/-- `Mᵀ P M` is positive semidefinite for positive semidefinite `P`. -/
theorem posSemidef_transpose_mul_mul {n m : Type*} [Fintype n] [Finite m]
    {P : Matrix n n ℝ} (hP : P.PosSemidef) (M : Matrix n m ℝ) : (Mᵀ * P * M).PosSemidef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hP.conjTranspose_mul_mul_same M

/-- `G(P) = BᵀPB + R` is positive definite for positive semidefinite `P`. -/
theorem gainDen_posDef {P : Matrix K K ℝ} (hP : P.PosSemidef) : (L.gainDen P).PosDef :=
  Matrix.PosDef.posSemidef_add (posSemidef_transpose_mul_mul hP L.B) L.R_pd

omit [Fintype U] in
/-- For symmetric `S`, `a ⬝ Sb = b ⬝ Sa`. -/
theorem dotProduct_mulVec_comm_of_symm {n : Type*} [Fintype n] {S : Matrix n n ℝ}
    (hS : Sᵀ = S) (a b : n → ℝ) : a ⬝ᵥ (S *ᵥ b) = b ⬝ᵥ (S *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

omit [Fintype U] in
/-- `(Bd) ⬝ w = d ⬝ (Bᵀw)`. -/
theorem mulVec_dotProduct {n m : Type*} [Fintype n] [Fintype m] (B : Matrix n m ℝ) (d : m → ℝ)
    (w : n → ℝ) : (B *ᵥ d) ⬝ᵥ w = d ⬝ᵥ (Bᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

omit [Fintype U] in
/-- `xᵀ(NᵀSN)x = (Nx)ᵀS(Nx)`. -/
theorem dotProduct_transpose_mul_mul {n m : Type*} [Fintype n] [Fintype m] (N : Matrix n m ℝ)
    (S : Matrix n n ℝ) (x : m → ℝ) :
    x ⬝ᵥ ((Nᵀ * S * N) *ᵥ x) = (N *ᵥ x) ⬝ᵥ (S *ᵥ (N *ᵥ x)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_dotProduct N x]

omit [Fintype U] in
/-- `(a + b)ᵀS(a + b) = aᵀSa + 2bᵀSa + bᵀSb` for symmetric `S`. -/
theorem quad_add {n : Type*} [Fintype n] {S : Matrix n n ℝ} (hS : Sᵀ = S) (a b : n → ℝ) :
    (a + b) ⬝ᵥ (S *ᵥ (a + b)) = a ⬝ᵥ (S *ᵥ a) + 2 * (b ⬝ᵥ (S *ᵥ a)) + b ⬝ᵥ (S *ᵥ b) := by
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_mulVec_comm_of_symm hS a b]
  ring

/-- The quadratic form of `T_F(P)` is the objective at `u = Fx`. -/
theorem dotProduct_TF (F : Matrix U K ℝ) (P : Matrix K K ℝ) (x : K → ℝ) :
    x ⬝ᵥ (L.TF F P *ᵥ x) = L.cost P x (F *ᵥ x) := by
  simp only [TF, cost, add_mulVec, dotProduct_add, dotProduct_transpose_mul_mul, mulVec_mulVec]

/-! ### Exercise 2.3.16 -/

/-- `T_F(P)` is positive semidefinite for positive semidefinite `P`. -/
theorem TF_posSemidef (F : Matrix U K ℝ) {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.TF F P).PosSemidef :=
  (L.Q_psd.add (posSemidef_transpose_mul_mul L.R_pd.posSemidef F)).add
    (posSemidef_transpose_mul_mul hP _)

/-- `T_F(P)` is symmetric for positive semidefinite `P`. -/
theorem TF_transpose (F : Matrix U K ℝ) {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.TF F P)ᵀ = L.TF F P :=
  (posSemidef_iff_real.1 (L.TF_posSemidef F hP)).1

/-- **Exercise 2.3.16** (p. 93): each `T_F` is order preserving for the Loewner order (and maps
`𝒫` into itself, `TF_posSemidef`). -/
theorem TF_mono (F : Matrix U K ℝ) {P P' : Matrix K K ℝ} (h : P ≤ P') : L.TF F P ≤ L.TF F P' := by
  rw [le_iff] at h ⊢
  have : L.TF F P' - L.TF F P = (L.A + L.B * F)ᵀ * (P' - P) * (L.A + L.B * F) := by
    simp only [TF, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [this]
  exact posSemidef_transpose_mul_mul h _

/-- Expanding `T_F(P)`. -/
theorem TF_expand (F : Matrix U K ℝ) (P : Matrix K K ℝ) :
    L.TF F P = L.Q + L.Aᵀ * P * L.A + L.Aᵀ * P * (L.B * F) + Fᵀ * (L.Bᵀ * P * L.A) +
      Fᵀ * (L.gainDen P * F) := by
  simp only [TF, gainDen, transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  abel

/-! ### The Riccati map and the control gain -/

variable [DecidableEq U]

/-- The Riccati map (2.27): `R(P) = AᵀPA − AᵀPB(BᵀPB + R)⁻¹BᵀPA + Q`. -/
noncomputable def riccati (P : Matrix K K ℝ) : Matrix K K ℝ :=
  L.Aᵀ * P * L.A - L.Aᵀ * P * L.B * (L.gainDen P)⁻¹ * L.Bᵀ * P * L.A + L.Q

/-- The control gain map (2.28): `F(P) = −(BᵀPB + R)⁻¹BᵀPA`. -/
noncomputable def gain (P : Matrix K K ℝ) : Matrix U K ℝ := -((L.gainDen P)⁻¹ * L.Bᵀ * P * L.A)

/-- `G(P)F(P) = −BᵀPA`. -/
theorem gainDen_mul_gain {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    L.gainDen P * L.gain P = -(L.Bᵀ * P * L.A) := by
  have h := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (L.gainDen_posDef hP).isUnit)
  simp only [gain, Matrix.mul_neg, ← Matrix.mul_assoc, h, Matrix.one_mul]

/-- **Exercise 2.3.13** (p. 90): `R(P) = (A + BF)ᵀP(A + BF) + FᵀRF + Q` when `F = F(P)`. -/
theorem riccati_eq_TF {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    L.riccati P = L.TF (L.gain P) P := by
  rw [TF_expand, L.gainDen_mul_gain hP]
  simp only [riccati, gain, Matrix.mul_neg, Matrix.mul_assoc]
  abel

/-- **Exercise 2.3.14** (p. 90): `R` maps `𝒫` into itself. -/
theorem riccati_posSemidef {P : Matrix K K ℝ} (hP : P.PosSemidef) :
    (L.riccati P).PosSemidef := by
  rw [L.riccati_eq_TF hP]
  exact L.TF_posSemidef _ hP

/-! ### Lemma 2.3.3: the control gain minimizes the one-period objective -/

/-- Completing the square: `J(F(P)x + d) = J(F(P)x) + dᵀG(P)d`. -/
theorem cost_gain_add {P : Matrix K K ℝ} (hP : P.PosSemidef) (x : K → ℝ) (d : U → ℝ) :
    L.cost P x (L.gain P *ᵥ x + d) = L.cost P x (L.gain P *ᵥ x) + d ⬝ᵥ (L.gainDen P *ᵥ d) := by
  have hPs : Pᵀ = P := (posSemidef_iff_real.1 hP).1
  have hRs : L.Rᵀ = L.R := (posDef_iff_real.1 L.R_pd).1
  set F := L.gain P
  set y := L.A *ᵥ x + L.B *ᵥ (F *ᵥ x)
  have hGF : L.gainDen P *ᵥ (F *ᵥ x) = -(L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x))) := by
    rw [mulVec_mulVec, L.gainDen_mul_gain hP, neg_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hsplit : L.A *ᵥ x + L.B *ᵥ (F *ᵥ x + d) = y + L.B *ᵥ d := by
    simp only [y, mulVec_add]
    abel
  -- the cross terms vanish: `R(Fx) + BᵀP(Ax + BFx) = (G F + BᵀPA)x = 0`
  have hcross : d ⬝ᵥ (L.R *ᵥ (F *ᵥ x)) + d ⬝ᵥ (L.Bᵀ *ᵥ (P *ᵥ y)) = 0 := by
    have e : L.gainDen P *ᵥ (F *ᵥ x) =
        L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))) + L.R *ᵥ (F *ᵥ x) := by
      rw [gainDen, add_mulVec, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    rw [hGF] at e
    have : L.R *ᵥ (F *ᵥ x) + L.Bᵀ *ᵥ (P *ᵥ y) = 0 := by
      simp only [y, mulVec_add]
      rw [← sub_eq_zero]
      have e' := congrArg (fun z => z + L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x))) e
      simp only [neg_add_cancel] at e'
      rw [sub_zero]
      calc L.R *ᵥ (F *ᵥ x) + (L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x)) + L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))))
          = L.Bᵀ *ᵥ (P *ᵥ (L.B *ᵥ (F *ᵥ x))) + L.R *ᵥ (F *ᵥ x) +
              L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x)) := by abel
        _ = 0 := e'.symm
    rw [← dotProduct_add, this, dotProduct_zero]
  have h1 := quad_add hRs (F *ᵥ x) d
  have h2 := quad_add hPs y (L.B *ᵥ d)
  have h3 : (L.B *ᵥ d) ⬝ᵥ (P *ᵥ y) = d ⬝ᵥ (L.Bᵀ *ᵥ (P *ᵥ y)) := mulVec_dotProduct L.B d _
  have h4 : (L.B *ᵥ d) ⬝ᵥ (P *ᵥ (L.B *ᵥ d)) = d ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ d) :=
    (dotProduct_transpose_mul_mul L.B P d).symm
  have h5 : d ⬝ᵥ (L.gainDen P *ᵥ d) = d ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ d) + d ⬝ᵥ (L.R *ᵥ d) := by
    rw [gainDen, add_mulVec, dotProduct_add]
  simp only [cost]
  rw [hsplit, h1, h2, h3, h4, h5]
  linear_combination (2 : ℝ) * hcross

/-- **Lemma 2.3.3** (p. 91): `F(P)x` minimizes `xᵀQx + uᵀRu + (Ax + Bu)ᵀP(Ax + Bu)` over
`u ∈ ℝᵐ`, and the minimizer is unique. -/
theorem gain_isMinimizer {P : Matrix K K ℝ} (hP : P.PosSemidef) (x : K → ℝ) :
    (∀ u, L.cost P x (L.gain P *ᵥ x) ≤ L.cost P x u) ∧
      ∀ u, L.cost P x u = L.cost P x (L.gain P *ᵥ x) → u = L.gain P *ᵥ x := by
  have hG := posDef_iff_real.1 (L.gainDen_posDef hP)
  have key : ∀ u, L.cost P x u = L.cost P x (L.gain P *ᵥ x) +
      (u - L.gain P *ᵥ x) ⬝ᵥ (L.gainDen P *ᵥ (u - L.gain P *ᵥ x)) := fun u => by
    have := L.cost_gain_add hP x (u - L.gain P *ᵥ x)
    rwa [add_sub_cancel] at this
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · rw [key u]
    rcases eq_or_ne (u - L.gain P *ᵥ x) 0 with h | h
    · rw [h]; simp
    · linarith [hG.2 h]
  · by_contra hne
    have := hG.2 (sub_ne_zero.2 hne)
    rw [key u] at hu
    linarith

/-- **Exercise 2.3.17** (p. 94): for `P ∈ 𝒫`, `F = F(P)` iff `T_F(P) ≼ T_G(P)` for every control
matrix `G`. -/
theorem gain_iff_TF_le {P : Matrix K K ℝ} (hP : P.PosSemidef) (F : Matrix U K ℝ) :
    F = L.gain P ↔ ∀ G : Matrix U K ℝ, L.TF F P ≤ L.TF G P := by
  classical
  constructor
  · rintro rfl G
    rw [le_iff, posSemidef_iff_real]
    refine ⟨by rw [transpose_sub, L.TF_transpose _ hP, L.TF_transpose _ hP], fun x => ?_⟩
    rw [sub_mulVec, dotProduct_sub, dotProduct_TF, dotProduct_TF, sub_nonneg]
    exact (L.gain_isMinimizer hP x).1 _
  · intro h
    -- `xᵀT_F x ≤ xᵀT_{F(P)}x`, so `Fx` attains the minimum, hence `Fx = F(P)x`
    have hx : ∀ x, F *ᵥ x = L.gain P *ᵥ x := by
      intro x
      have h1 := (posSemidef_iff_real.1 (le_iff.1 (h (L.gain P)))).2 x
      rw [sub_mulVec, dotProduct_sub, dotProduct_TF, dotProduct_TF, sub_nonneg] at h1
      exact (L.gain_isMinimizer hP x).2 _ (le_antisymm h1 ((L.gain_isMinimizer hP x).1 _))
    ext i j
    have := congrFun (hx (Pi.single j 1)) i
    simpa [mulVec, dotProduct, Pi.single_apply] using this

end LQProblem

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# LQ control as an ADP

Copied from `GeneralStates/AbstractDecisionProcesses` (module `LQControl`), namespace renamed to
`Miao.LinearQuadratic.SS`.

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.5.3–§2.3.5.8 (pp. 91–95).

A control matrix `F` is *stable* when `ρ(A + BF) < 1`.

* **Exercise 2.3.15**: for stable `F`, `xₜ = (A + BF)ᵗx₀ → 0`.
* **Lemma 2.3.5**: for stable `F`, `T_F` is globally stable on `𝒫` with fixed point
  `P_F = ∑ₜ ((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ` (2.35), and `xᵀP_F x` is the lifetime cost
  `ℓ_F(x) = ∑ₜ xₜᵀ(FᵀRF + Q)xₜ` (2.30).
* The ADP `(𝒫, 𝕋)` with the Loewner order and stable policies (§2.3.5.4) and **Lemma 2.3.6**
  (it is order stable).
* `𝒫_S`, **Lemma 2.3.7** (the control gain of `P ∈ 𝒫_S` is a stable `P`-min-greedy policy),
  **Lemma 2.3.8** (the Bellman min-operator is the Riccati map on `𝒫_S`) and **Lemma 2.3.9**
  (the Riccati equation, the Bellman min-equation and the LQ Bellman equation (2.26) agree).
* §2.3.5.8, given a fixed point `P*` of the Riccati map in `𝒫_S` (Lemma 2.3.4, which the book
  cites from Bertsekas): (a) `P*` is the least element of `𝒫_Σ`, (b) `T P* = P*`, (c) a policy is
  min-optimal iff it is `P*`-min-greedy; hence (2.38) and the optimality of `F(P*)`.
* **Example 2.3.1**: the scalar lifetime cost `c = (F² + 1)∑ (A + BF)^{2t}` (2.31), and with
  `A = B = 1`, `F = −0.6` costs less than `F = −0.9` from every state.
-/

open Matrix Filter Topology Set Function

open scoped MatrixOrder

namespace Miao.LinearQuadratic.SS

/-- The positive semidefinite cone `𝒫` (§2.3.5.2). -/
def psdCone (K : Type*) [Fintype K] : Set (Matrix K K ℝ) := {P | P.PosSemidef}

namespace LQProblem

variable {K U : Type*} [Fintype K] [DecidableEq K] [Fintype U] (L : LQProblem K U)

/-- The closed-loop matrix `A + BF`. -/
def closedLoop (F : Matrix U K ℝ) : Matrix K K ℝ := L.A + L.B * F

/-- `F` is a stable control matrix (§2.3.5.3): `ρ(A + BF) < 1`. -/
def IsStable (F : Matrix U K ℝ) : Prop := specRad (L.closedLoop F) < 1

/-- The per-period cost matrix `FᵀRF + Q`. -/
def costMat (F : Matrix U K ℝ) : Matrix K K ℝ := Fᵀ * L.R * F + L.Q

/-- The `t`-th term `((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ` of (2.35). -/
def discCost (F : Matrix U K ℝ) (t : ℕ) : Matrix K K ℝ :=
  (L.closedLoop F ^ t)ᵀ * L.costMat F * L.closedLoop F ^ t

omit [DecidableEq K] in
/-- `T_F(P) = (FᵀRF + Q) + (A + BF)ᵀP(A + BF)`. -/
theorem TF_eq (F : Matrix U K ℝ) (P : Matrix K K ℝ) :
    L.TF F P = L.costMat F + (L.closedLoop F)ᵀ * P * L.closedLoop F := by
  simp only [TF, costMat, closedLoop]
  abel

/-! ### Exercise 2.3.15 and the decay of `(A + BF)ᵗ` -/

variable {L}

/-- For stable `F`, the entries of `(A + BF)ᵗ` decay geometrically. -/
theorem IsStable.entry_decay [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    ∃ r, 0 ≤ r ∧ r < 1 ∧ ∀ᶠ t in atTop, ∀ i j, |(L.closedLoop F ^ t) i j| ≤ r ^ t := by
  set r := (specRad (L.closedLoop F) + 1) / 2
  have h0 := specRad_nonneg (L.closedLoop F)
  refine ⟨r, by positivity, by unfold IsStable at hF; simp only [r]; linarith, ?_⟩
  have hr : specRad (L.closedLoop F) < r := by unfold IsStable at hF; simp only [r]; linarith
  simp only [eventually_all]
  exact fun i j => eventually_abs_entry_pow_le _ hr i j

/-- For stable `F`, every entry of `(A + BF)ᵗ` tends to zero. -/
theorem IsStable.tendsto_entry [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (i j : K) :
    Tendsto (fun t => (L.closedLoop F ^ t) i j) atTop (𝓝 0) := by
  obtain ⟨r, hr0, hr1, hev⟩ := hF.entry_decay
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (hev.mono fun t ht => ht i j)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)

/-- **Exercise 2.3.15** (p. 92): for a stable control matrix, `xₜ = (A + BF)ᵗx₀ → 0`. -/
theorem IsStable.tendsto_state [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F)
    (x₀ : K → ℝ) : Tendsto (fun t => (L.closedLoop F ^ t) *ᵥ x₀) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [show (0 : ℝ) = ∑ j, 0 * x₀ j by simp]
  exact tendsto_finsetSum _ fun j _ => (hF.tendsto_entry i j).mul_const _

/-! ### Lemma 2.3.5 -/

omit [DecidableEq K] in
/-- `Nᵀ P N` in coordinates. -/
theorem transpose_mul_mul_apply (N P : Matrix K K ℝ) (a b : K) :
    (Nᵀ * P * N) a b = ∑ i, ∑ j, N i a * P i j * N j b := by
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq K] in
/-- If the entries of `Nₙ` tend to zero, so do those of `NₙᵀPNₙ`. -/
theorem tendsto_transpose_mul_mul_zero {N : ℕ → Matrix K K ℝ}
    (hN : ∀ i j, Tendsto (fun n => N n i j) atTop (𝓝 0)) (P : Matrix K K ℝ) (a b : K) :
    Tendsto (fun n => ((N n)ᵀ * P * N n) a b) atTop (𝓝 0) := by
  simp only [transpose_mul_mul_apply]
  rw [show (0 : ℝ) = ∑ i : K, ∑ j : K, 0 * P i j * 0 by simp]
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    ((hN i a).mul_const _).mul (hN j b)

/-- The iterates of `T_F`: `T_Fⁿ P = ∑_{t<n} (Mᵗ)ᵀCMᵗ + (Mⁿ)ᵀPMⁿ` with `M = A + BF`,
`C = FᵀRF + Q`. -/
theorem TF_iterate (F : Matrix U K ℝ) (P : Matrix K K ℝ) (n : ℕ) :
    (L.TF F)^[n] P = ∑ t ∈ Finset.range n, L.discCost F t +
      (L.closedLoop F ^ n)ᵀ * P * L.closedLoop F ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [discCost] at ih ⊢
    rw [iterate_succ_apply', ih, TF_eq, Finset.sum_range_succ', pow_zero, transpose_one,
      Matrix.one_mul, Matrix.mul_one, pow_succ, transpose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul, pow_succ,
      transpose_mul, Matrix.mul_assoc]
    abel

variable (L) in
/-- The lifetime cost matrix (2.35): `P_F = ∑ₜ ((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ`. -/
noncomputable def PF (F : Matrix U K ℝ) : Matrix K K ℝ :=
  Matrix.of fun a b => ∑' t : ℕ, L.discCost F t a b

/-- (2.35): the series defining `P_F` converges, entry by entry. -/
theorem IsStable.hasSum_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (a b : K) :
    HasSum (fun t => L.discCost F t a b)
      (L.PF F a b) := by
  obtain ⟨r, hr0, hr1, hev⟩ := hF.entry_decay
  set c := ∑ i : K, ∑ j : K, |L.costMat F i j|
  have hsum : Summable fun t => L.discCost F t a b := by
    refine Summable.of_norm_bounded_eventually (g := fun t : ℕ => c * (r ^ 2) ^ t)
      ((summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left c) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with t ht
    rw [Real.norm_eq_abs, discCost, transpose_mul_mul_apply]
    calc |∑ i, ∑ j, (L.closedLoop F ^ t) i a * L.costMat F i j * (L.closedLoop F ^ t) j b|
        ≤ ∑ i, ∑ j, |(L.closedLoop F ^ t) i a * L.costMat F i j * (L.closedLoop F ^ t) j b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, r ^ t * |L.costMat F i j| * r ^ t := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (ht i a) (abs_nonneg _)) (ht j b)
              (abs_nonneg _) (by positivity)
      _ = c * (r ^ 2) ^ t := by
          simp only [c, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  exact hsum.hasSum

/-- **Lemma 2.3.5** (p. 93), convergence: for stable `F`, `T_Fⁿ P → P_F` entrywise from every
`P`. -/
theorem IsStable.tendsto_TF_iterate [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F)
    (P : Matrix K K ℝ) (a b : K) :
    Tendsto (fun n => ((L.TF F)^[n] P) a b) atTop (𝓝 (L.PF F a b)) := by
  simp only [TF_iterate, Matrix.add_apply, Matrix.sum_apply]
  rw [← add_zero (L.PF F a b)]
  exact (hF.hasSum_PF a b).tendsto_sum_nat.add
    (tendsto_transpose_mul_mul_zero (hF.tendsto_entry) P a b)

omit [DecidableEq K] in
/-- `T_F` is continuous, entry by entry. -/
theorem tendsto_TF {F : Matrix U K ℝ} {Pn : ℕ → Matrix K K ℝ} {P : Matrix K K ℝ}
    (h : ∀ i j, Tendsto (fun n => Pn n i j) atTop (𝓝 (P i j))) (a b : K) :
    Tendsto (fun n => L.TF F (Pn n) a b) atTop (𝓝 (L.TF F P a b)) := by
  simp only [TF_eq, Matrix.add_apply, transpose_mul_mul_apply]
  exact tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    ((h i j).const_mul _).mul_const _)

/-- **Lemma 2.3.5** (p. 93), fixed point: `T_F P_F = P_F`. -/
theorem IsStable.TF_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    L.TF F (L.PF F) = L.PF F := by
  ext a b
  have h1 := (hF.tendsto_TF_iterate 0 a b).comp (tendsto_add_atTop_nat 1)
  have h2 := L.tendsto_TF (F := F) (fun i j => hF.tendsto_TF_iterate 0 i j) a b
  refine tendsto_nhds_unique h2 ?_
  refine h1.congr fun n => ?_
  simp only [Function.comp_apply, iterate_succ_apply']

/-- `P_F` is the only fixed point of `T_F`. -/
theorem IsStable.eq_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) {P : Matrix K K ℝ}
    (hP : L.TF F P = P) : P = L.PF F := by
  ext a b
  have : ∀ n, (L.TF F)^[n] P = P := fun n => iterate_fixed hP n
  exact tendsto_nhds_unique (by simp [this])
    (hF.tendsto_TF_iterate P a b)

/-- `P_F` is positive semidefinite: it is a limit of positive semidefinite partial sums. -/
theorem IsStable.PF_posSemidef [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    (L.PF F).PosSemidef := by
  have hC : (L.costMat F).PosSemidef :=
    (posSemidef_transpose_mul_mul L.R_pd.posSemidef F).add L.Q_psd
  have hmem : ∀ n, ((L.TF F)^[n] 0).PosSemidef := by
    intro n
    induction n with
    | zero => exact PosSemidef.zero
    | succ n ih => rw [iterate_succ_apply']; exact L.TF_posSemidef F ih
  have hlim : Tendsto (fun n => (L.TF F)^[n] 0) atTop (𝓝 (L.PF F)) :=
    tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hF.tendsto_TF_iterate 0 a b
  exact posSemidef_is_closed.mem_of_tendsto hlim (Eventually.of_forall hmem)

variable (L) in
/-- `T_F` restricted to the positive semidefinite cone `𝒫`. -/
def TFpsd (F : Matrix U K ℝ) (P : ↥(psdCone K)) : ↥(psdCone K) :=
  ⟨L.TF F P, L.TF_posSemidef F P.2⟩

omit [DecidableEq K] in
theorem TFpsd_iterate (F : Matrix U K ℝ) (P : ↥(psdCone K)) (n : ℕ) :
    ((L.TFpsd F)^[n] P : Matrix K K ℝ) = (L.TF F)^[n] P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl

omit [DecidableEq K] in
/-- **Lemma 2.3.5** (p. 93): for stable `F`, `T_F` is globally stable on `𝒫`, with fixed point
`P_F` (2.35). -/
theorem IsStable.globallyStable [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    GloballyStable (L.TFpsd F) := by
  classical
  refine ⟨⟨L.PF F, hF.PF_posSemidef⟩, Subtype.ext hF.TF_PF, fun P hP => Subtype.ext
    (hF.eq_PF (congrArg Subtype.val hP)), fun P => ?_⟩
  rw [tendsto_subtype_rng]
  simp only [TFpsd_iterate]
  exact tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hF.tendsto_TF_iterate P a b

/-- (2.30) and (2.35) (p. 93): `xᵀP_F x = ℓ_F(x) = ∑ₜ xₜᵀ(FᵀRF + Q)xₜ` with `xₜ = (A + BF)ᵗx`. -/
theorem IsStable.hasSum_cost [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (x : K → ℝ) :
    HasSum (fun t => ((L.closedLoop F ^ t) *ᵥ x) ⬝ᵥ (L.costMat F *ᵥ ((L.closedLoop F ^ t) *ᵥ x)))
      (x ⬝ᵥ (L.PF F *ᵥ x)) := by
  have e : ∀ t, ((L.closedLoop F ^ t) *ᵥ x) ⬝ᵥ (L.costMat F *ᵥ ((L.closedLoop F ^ t) *ᵥ x)) =
      x ⬝ᵥ (L.discCost F t *ᵥ x) := fun t => (dotProduct_transpose_mul_mul _ _ x).symm
  simp_rw [e]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact hasSum_sum fun a _ => hasSum_sum fun b _ =>
    ((hF.hasSum_PF a b).mul_right (x b)).mul_left (x a)

/-! ### The ADP `(𝒫, 𝕋)` -/

variable (L) in
/-- The stable control matrices, the policies of §2.3.5.4. -/
def StablePolicy : Type _ := {F : Matrix U K ℝ // L.IsStable F}

/-- The LQ ADP `(𝒫, 𝕋)` (§2.3.5.4) with the Loewner order, given that some stable control matrix
exists (otherwise `𝕋` would be empty). **Exercise 2.3.16** gives monotonicity. -/
noncomputable def adp (hne : ∃ F, L.IsStable F) : ADP ↥(psdCone K) (StablePolicy L) where
  T F := L.TFpsd F.1
  mono F _ _ h := L.TF_mono F.1 h
  nonempty := ⟨⟨_, hne.choose_spec⟩⟩

omit [DecidableEq K] in
/-- **Lemma 2.3.6** (p. 93): the LQ ADP is (strongly) order stable. -/
theorem adp_isStronglyOrderStable [Nonempty K] (hne : ∃ F, L.IsStable F) :
    (adp hne).IsStronglyOrderStable := fun F =>
  stronglyOrderStable_of_globallyStable ((adp hne).mono F) F.2.globallyStable

/-! ### Min-greedy policies and the Bellman min-equation -/

omit [DecidableEq K] in
/-- Symmetric matrices with the same quadratic form are equal. -/
theorem eq_of_dotProduct_mulVec_eq {S S' : Matrix K K ℝ} (hS : Sᵀ = S) (hS' : S'ᵀ = S')
    (h : ∀ x, x ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ (S' *ᵥ x)) : S = S' := by
  classical
  set D := S - S'
  have hD : Dᵀ = D := by simp only [D, transpose_sub, hS, hS']
  have h0 : ∀ x, x ⬝ᵥ (D *ᵥ x) = 0 := fun x => by
    simp only [D, sub_mulVec, dotProduct_sub, h x, sub_self]
  have hentry : ∀ i j, Pi.single i 1 ⬝ᵥ (D *ᵥ Pi.single j 1) = D i j := fun i j => by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [← sub_eq_zero]
  ext i j
  have hii := h0 (Pi.single i 1)
  have hjj := h0 (Pi.single j 1)
  have hij := h0 (Pi.single i 1 + Pi.single j 1)
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hentry, hentry, hentry,
    hentry] at hij
  rw [hentry] at hii hjj
  have hsym : D j i = D i j := by
    have := congrFun (congrFun hD i) j
    rwa [transpose_apply] at this
  change D i j = 0
  linarith

variable [DecidableEq U]

variable (L) in
/-- `𝒫_S`: the positive semidefinite `P` whose control gain `F(P)` is stable (§2.3.5.6). -/
def PS : Set (Matrix K K ℝ) := {P | P.PosSemidef ∧ L.IsStable (L.gain P)}

omit [DecidableEq K] in
/-- **Lemma 2.3.7** (p. 94): for `P ∈ 𝒫_S`, the control gain `F(P)` is a stable `P`-min-greedy
policy. -/
theorem gain_isMinGreedy (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (adp hne).IsMinGreedy ⟨P, hP.1⟩ ⟨L.gain P, hP.2⟩ :=
  fun G => (L.gain_iff_TF_le hP.1 _).1 rfl G.1

omit [DecidableEq K] in
/-- **Lemma 2.3.8** (p. 94): on `𝒫_S` the Bellman min-operator is the Riccati map. -/
theorem isMinBellmanValue_riccati (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (adp hne).IsMinBellmanValue ⟨P, hP.1⟩ ⟨L.riccati P, L.riccati_posSemidef hP.1⟩ := by
  have hT : (adp hne).T ⟨L.gain P, hP.2⟩ ⟨P, hP.1⟩ = ⟨L.riccati P, L.riccati_posSemidef hP.1⟩ :=
    Subtype.ext (L.riccati_eq_TF hP.1).symm
  refine ⟨?_, fun w hw => hT ▸ hw ⟨_, rfl⟩⟩
  rintro _ ⟨G, rfl⟩
  rw [← hT]
  exact gain_isMinGreedy hne hP G

omit [DecidableEq K] in
/-- **Lemma 2.3.9** (p. 95): for `P ∈ 𝒫_S`, (i) `R(P) = P` iff (ii) `T▿P = P` iff (iii)
`ℓ(x) = xᵀPx` satisfies the LQ Bellman equation (2.26),
`ℓ(x) = min_u {xᵀQx + uᵀRu + ℓ(Ax + Bu)}`. -/
theorem riccati_tfae (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (L.riccati P = P ↔ (adp hne).SolvesMinBellman ⟨P, hP.1⟩) ∧
      (L.riccati P = P ↔ ∀ x, IsLeast (range (L.cost P x)) (x ⬝ᵥ (P *ᵥ x))) := by
  have h8 := isMinBellmanValue_riccati hne hP
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h x => ?_, fun h => ?_⟩⟩
  · have : (⟨L.riccati P, L.riccati_posSemidef hP.1⟩ : ↥(psdCone K)) = ⟨P, hP.1⟩ :=
      Subtype.ext h
    rw [this] at h8
    exact h8
  · exact congrArg Subtype.val (h8.unique h)
  · have hval : x ⬝ᵥ (P *ᵥ x) = L.cost P x (L.gain P *ᵥ x) := by
      rw [← L.dotProduct_TF, ← L.riccati_eq_TF hP.1, h]
    rw [hval]
    exact ⟨⟨_, rfl⟩, by rintro _ ⟨u, rfl⟩; exact (L.gain_isMinimizer hP.1 x).1 u⟩
  · refine eq_of_dotProduct_mulVec_eq (posSemidef_iff_real.1 (L.riccati_posSemidef hP.1)).1
      (posSemidef_iff_real.1 hP.1).1 fun x => ?_
    rw [L.riccati_eq_TF hP.1, L.dotProduct_TF]
    have hmin : IsLeast (range (L.cost P x)) (L.cost P x (L.gain P *ᵥ x)) :=
      ⟨⟨_, rfl⟩, by rintro _ ⟨u, rfl⟩; exact (L.gain_isMinimizer hP.1 x).1 u⟩
    exact hmin.unique (h x)

omit [DecidableEq K] in
/-- §2.3.5.8 (p. 95): if `P* ∈ 𝒫_S` solves the Riccati equation (as Lemma 2.3.4 provides under
controllability and observability), then (a) `P*` is the least element of `𝒫_Σ`, (b) `P*` solves
the Bellman min-equation, (c) a policy is min-optimal iff it is `P*`-min-greedy, (2.38) holds,
and `F(P*)` is min-optimal. -/
theorem optimality [Nonempty K] (hne : ∃ F, L.IsStable F) {Pstar : Matrix K K ℝ}
    (hPS : Pstar ∈ L.PS) (hfix : L.riccati Pstar = Pstar) :
    IsLeast (adp hne).VSig ⟨Pstar, hPS.1⟩ ∧ (adp hne).SolvesMinBellman ⟨Pstar, hPS.1⟩ ∧
      (∀ F, (adp hne).IsMinOptimal (adp_isStronglyOrderStable hne).isOrderStable.wellPosed F ↔
        (adp hne).IsMinGreedy ⟨Pstar, hPS.1⟩ F) ∧
      (∀ x, IsLeast (range (L.cost Pstar x)) (x ⬝ᵥ (Pstar *ᵥ x))) ∧
      (adp hne).IsMinOptimal (adp_isStronglyOrderStable hne).isOrderStable.wellPosed
        ⟨L.gain Pstar, hPS.2⟩ := by
  have hos := (adp_isStronglyOrderStable hne).isOrderStable
  have hb : (adp hne).SolvesMinBellman ⟨Pstar, hPS.1⟩ := (riccati_tfae hne hPS).1.1 hfix
  have hG : (⟨Pstar, hPS.1⟩ : ↥(psdCone K)) ∈ (adp hne).VGmin :=
    ⟨⟨L.gain Pstar, hPS.2⟩, gain_isMinGreedy hne hPS⟩
  obtain ⟨⟨σ, hσ⟩, ⟨v, hv, -, -, huniq⟩, hbp⟩ := hos.minFundamentalOptimality hG hb
  have hvP : (⟨Pstar, hPS.1⟩ : ↥(psdCone K)) = v := huniq _ hG hb
  have hc : ∀ F, (adp hne).IsMinOptimal hos.wellPosed F ↔
      (adp hne).IsMinGreedy ⟨Pstar, hPS.1⟩ F := fun F => by
    rw [hbp F]
    constructor
    · rintro ⟨w, hw, hg⟩
      rwa [hvP, ← hw.unique hv]
    · intro hg
      exact ⟨v, hv, hvP ▸ hg⟩
  refine ⟨?_, hb, hc, (riccati_tfae hne hPS).2.1 hfix, (hc _).2 (gain_isMinGreedy hne hPS)⟩
  rw [hvP, ← hσ.isGLB.unique hv]
  exact hσ

/-! ### Example 2.3.1 -/

/-- **Example 2.3.1** (p. 91), (2.31): in the scalar case with `Q = R = 1`, a control `F` with
`|A + BF| < 1` has lifetime cost `ℓ_F(x₀) = c x₀²`, `c = (F² + 1)∑ₜ (A + BF)^{2t} =
(F² + 1)/(1 − (A + BF)²)`. -/
theorem scalar_lifetimeCost {A B F : ℝ} (h : |A + B * F| < 1) (x₀ : ℝ) :
    HasSum (fun t : ℕ => ((A + B * F) ^ t * x₀) ^ 2 * (F ^ 2 + 1))
      ((F ^ 2 + 1) / (1 - (A + B * F) ^ 2) * x₀ ^ 2) := by
  have hq0 : 0 ≤ (A + B * F) ^ 2 := sq_nonneg _
  have hq1 : (A + B * F) ^ 2 < 1 := by
    have := (sq_lt_one_iff_abs_lt_one _).2 h
    exact this
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((F ^ 2 + 1) * x₀ ^ 2)
  convert hg using 1
  · funext t
    rw [mul_pow, ← pow_mul, mul_comm t 2, pow_mul]
    ring
  · field_simp

/-- **Example 2.3.1** (p. 92): with `A = B = 1`, the control `F = −0.6` has lower lifetime cost
than `F = −0.9` from every state (`c = 34/21 < 181/99`). -/
theorem scalar_compare (x₀ : ℝ) :
    ((-0.6 : ℝ) ^ 2 + 1) / (1 - (1 + 1 * (-0.6)) ^ 2) * x₀ ^ 2 ≤
      ((-0.9 : ℝ) ^ 2 + 1) / (1 - (1 + 1 * (-0.9)) ^ 2) * x₀ ^ 2 := by
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  norm_num

end LQProblem

end Miao.LinearQuadratic.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stable matrices and asymptotic tools for Chapter 9

Miao, Chapter 9 (pp. 291–304) uses "stable matrix" in the sense of Definition 1.4.5 (p. 18):
every eigenvalue has modulus less than one. This module fixes that notion for real matrices
(`ls_Stable`) and collects the analytic facts the chapter's proofs use:

* `ls_stable_iff_tendsto`: `M` is stable iff `Mᵗv → 0` for every `v` (Chapter 1).
* `ls_stable_iff_specRad`: `M` is stable iff the Sargent–Stachurski spectral radius
  `ρ(M) < 1`, so the `SS` LQ results (stated with `ρ`) apply.
* `ls_tendsto_zero_of_le_rec`: `0 ≤ e_{t+1} ≤ re_t + δ_t`, `r < 1`, `δ_t → 0` give `e_t → 0`.
* `ls_tendsto_zero_of_stable_input`: `x_{t+1} = Mx_t + w_t` with `M` stable and `w_t → 0`
  gives `x_t → 0`.
* `ls_tendsto_of_quad`, `ls_exists_tendsto_of_quad`: convergence of symmetric matrices from
  convergence of their quadratic forms (polarization).
* `ls_posDef_coercive`, `ls_tendsto_zero_of_quad_posDef`: a positive definite form dominates
  `c‖x‖²`, so `x_t'Qx_t → 0` forces `x_t → 0`.
-/

open Filter Topology

namespace Miao.LinearQuadratic

open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Miao's stable matrix (Definition 1.4.5, p. 18), for a real matrix: every (complex)
eigenvalue has modulus less than one. -/
def ls_Stable (M : Matrix X X ℝ) : Prop := IsStableMatrix (M.map Complex.ofRealHom)

/-- A real matrix is stable iff all its orbits `Mᵗv` converge to zero (Chapter 1). -/
theorem ls_stable_iff_tendsto (M : Matrix X X ℝ) :
    ls_Stable M ↔ ∀ v : X → ℝ, Tendsto (fun t => (M ^ t) *ᵥ v) atTop (𝓝 0) :=
  isStableMatrix_iff_tendsto M

/-- `ρ(M) < 1` makes `M` stable. -/
theorem ls_stable_of_specRad [Nonempty X] {M : Matrix X X ℝ} (h : SS.specRad M < 1) :
    ls_Stable M := by
  rw [ls_stable_iff_tendsto]
  intro v
  obtain ⟨r, hr1, hr2⟩ := exists_between h
  have hr0 : 0 ≤ r := (SS.specRad_nonneg M).trans hr1.le
  have hent : ∀ i j, Tendsto (fun t => (M ^ t) i j) atTop (𝓝 0) := fun i j => by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (SS.eventually_abs_entry_pow_le M hr1 i j) (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr2)
  rw [tendsto_pi_nhds]
  intro i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [show (0 : ℝ) = ∑ j, 0 * v j by simp]
  exact tendsto_finsetSum _ fun j _ => (hent i j).mul_const _

/-- A stable matrix has `ρ(M) < 1`: the spectral radius is attained by an eigenvalue. -/
theorem ls_specRad_lt_of_stable [Nonempty X] {M : Matrix X X ℝ} (h : ls_Stable M) :
    SS.specRad M < 1 := by
  let _ : NormedRing (Matrix X X ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix X X ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  obtain ⟨z, hz, hnorm⟩ := spectrum.exists_nnnorm_eq_spectralRadius (SS.complexify M)
  obtain ⟨e, he, hev⟩ := (SS.mem_spectrum_iff_eigenpair M z).1 hz
  have hz1 : ‖z‖ < 1 := by
    refine h z ?_
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := e) ⟨?_, he⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hev
  have : SS.specRad M = ‖z‖ := by
    unfold SS.specRad
    rw [← hnorm, ENNReal.coe_toReal, coe_nnnorm]
  rw [this]
  exact hz1

/-- `M` is stable iff its spectral radius is below one. -/
theorem ls_stable_iff_specRad [Nonempty X] (M : Matrix X X ℝ) :
    ls_Stable M ↔ SS.specRad M < 1 :=
  ⟨ls_specRad_lt_of_stable, ls_stable_of_specRad⟩

/-- Stability is invariant under transposition. -/
theorem ls_stable_transpose [Nonempty X] (M : Matrix X X ℝ) : ls_Stable Mᵀ ↔ ls_Stable M := by
  rw [ls_stable_iff_specRad, ls_stable_iff_specRad, SS.specRad_transpose]

/-- A scalar recursion `0 ≤ e_{t+1} ≤ re_t + δ_t` with `0 ≤ r < 1` and `δ_t → 0` tends to zero. -/
theorem ls_tendsto_zero_of_le_rec {e δ : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (he : ∀ t, 0 ≤ e t) (hrec : ∀ t, e (t + 1) ≤ r * e t + δ t)
    (hδ : Tendsto δ atTop (𝓝 0)) : Tendsto e atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1r : 0 < 1 - r := by linarith
  set η := ε * (1 - r) / 2 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.1 hδ η hη0
  have hbound : ∀ m, e (T + m) ≤ r ^ m * e T + η / (1 - r) := by
    intro m
    induction m with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith [div_pos hη0 h1r]
    | succ m ih =>
      have hd : δ (T + m) < η := by
        have := hT (T + m) (Nat.le_add_right T m)
        rw [Real.dist_eq, sub_zero] at this
        exact (le_abs_self _).trans_lt this
      have e1 := hrec (T + m)
      rw [show T + (m + 1) = T + m + 1 by ring]
      have : r * e (T + m) ≤ r * (r ^ m * e T + η / (1 - r)) :=
        mul_le_mul_of_nonneg_left ih hr0
      have hid : r * (r ^ m * e T + η / (1 - r)) + η = r ^ (m + 1) * e T + η / (1 - r) := by
        field_simp
        ring
      linarith
  have hpow : Tendsto (fun m => r ^ m * e T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (e T)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hpow (ε / 2) (by positivity)
  refine ⟨T + M, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = T + m := ⟨n - T, by omega⟩
  have hm := hM m (by omega)
  rw [Real.dist_eq, sub_zero] at hm ⊢
  have hb := hbound m
  have hηr : η / (1 - r) = ε / 2 := by rw [hη]; field_simp
  rw [abs_of_nonneg (he _)]
  have := le_abs_self (r ^ m * e T)
  linarith

/-- With `M` stable, `x_{t+1} = Mx_t + w_t` and `w_t → 0` give `x_t → 0`. -/
theorem ls_tendsto_zero_of_stable_input {M : Matrix X X ℝ} (hM : ls_Stable M)
    {x w : ℕ → X → ℝ} (hx : ∀ t, x (t + 1) = M *ᵥ x t + w t)
    (hw : Tendsto w atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨K, a, ha0, ha1, hK0, hK⟩ := hasGeomDecay_of_isStableMatrix M hM
  set s : ℕ → ℝ := fun t => ∑ j ∈ Finset.range t, a ^ j * ‖w (t - 1 - j)‖ with hs
  have hs0 : ∀ t, 0 ≤ s t := fun t =>
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg ha0 j) (norm_nonneg _)
  have hsrec : ∀ t, s (t + 1) ≤ a * s t + ‖w t‖ := by
    intro t
    apply le_of_eq
    simp only [hs]
    rw [Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega, pow_succ]
      ring
    · simp
  have hδ : Tendsto (fun t => ‖w t‖) atTop (𝓝 0) := by
    simpa using hw.norm
  have hslim := ls_tendsto_zero_of_le_rec ha0 ha1 hs0 hsrec hδ
  have hbd : ∀ t, ‖x t‖ ≤ K * a ^ t * ‖x 0‖ + K * s t := by
    intro t
    rw [backward_sol_eq M hx t]
    refine (norm_add_le _ _).trans (add_le_add (hK t _) ?_)
    simp only [hs, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    calc ‖(M ^ j) *ᵥ w (t - 1 - j)‖ ≤ K * a ^ j * ‖w (t - 1 - j)‖ := hK j _
      _ = K * (a ^ j * ‖w (t - 1 - j)‖) := by ring
  have hlim : Tendsto (fun t => K * a ^ t * ‖x 0‖ + K * s t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => K * a ^ t * ‖x 0‖) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul K).mul_const ‖x 0‖
    simpa using h1.add (hslim.const_mul K)
  exact squeeze_zero_norm hbd hlim

/-- `Pᵢⱼ` from quadratic forms, for symmetric `P` (polarization). -/
theorem ls_entry_eq_polar {P : Matrix X X ℝ} (hP : Pᵀ = P) (i j : X) :
    P i j = ((Pi.single i 1 + Pi.single j 1) ⬝ᵥ (P *ᵥ (Pi.single i 1 + Pi.single j 1)) -
      Pi.single i (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single i 1) -
      Pi.single j (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single j 1)) / 2 := by
  rw [SS.LQProblem.quad_add hP]
  have hji : Pi.single j (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single i 1) = P i j := by
    rw [single_one_dotProduct, mulVec_single_one]
    exact congrFun (congrFun hP i) j
  rw [hji]
  ring

omit [DecidableEq X] in
/-- Symmetric matrices converge when their quadratic forms converge to those of a symmetric
limit. -/
theorem ls_tendsto_of_quad {P : ℕ → Matrix X X ℝ} {P₀ : Matrix X X ℝ}
    (hs : ∀ n, (P n)ᵀ = P n) (hP₀ : P₀ᵀ = P₀)
    (h : ∀ v : X → ℝ, Tendsto (fun n => v ⬝ᵥ (P n *ᵥ v)) atTop (𝓝 (v ⬝ᵥ (P₀ *ᵥ v)))) :
    Tendsto P atTop (𝓝 P₀) := by
  classical
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  simp only [ls_entry_eq_polar (hs _) i j, ls_entry_eq_polar hP₀ i j]
  exact (((h _).sub (h _)).sub (h _)).div_const 2

omit [DecidableEq X] in
/-- If every quadratic form of a sequence of symmetric matrices converges, the matrices converge
(entrywise) to a symmetric limit. -/
theorem ls_exists_tendsto_of_quad {P : ℕ → Matrix X X ℝ} (hs : ∀ n, (P n)ᵀ = P n)
    (h : ∀ v : X → ℝ, ∃ c, Tendsto (fun n => v ⬝ᵥ (P n *ᵥ v)) atTop (𝓝 c)) :
    ∃ P₀ : Matrix X X ℝ, P₀ᵀ = P₀ ∧ Tendsto P atTop (𝓝 P₀) := by
  classical
  choose c hc using h
  set e : X → X → ℝ := fun i => Pi.single i 1
  refine ⟨Matrix.of fun i j => (c (e i + e j) - c (e i) - c (e j)) / 2, ?_, ?_⟩
  · ext i j
    simp only [transpose_apply, of_apply]
    rw [add_comm (e j) (e i)]
    ring
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [ls_entry_eq_polar (hs _) i j, of_apply]
    exact (((hc _).sub (hc _)).sub (hc _)).div_const 2

omit [DecidableEq X] in
/-- A positive definite form dominates a multiple of `‖x‖²` (sup norm). -/
theorem ls_posDef_coercive {Q : Matrix X X ℝ} (hQ : Q.PosDef) :
    ∃ c > 0, ∀ x : X → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Q *ᵥ x) := by
  have hQ' := SS.LQProblem.posDef_iff_real.1 hQ
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  · have hcpt := isCompact_sphere (0 : X → ℝ) 1
    have hne : (Metric.sphere (0 : X → ℝ) 1).Nonempty :=
      NormedSpace.sphere_nonempty.2 zero_le_one
    have hcont : Continuous fun v : X → ℝ => v ⬝ᵥ (Q *ᵥ v) :=
      Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id)
    obtain ⟨v₀, hv₀, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hv₀
      exact zero_ne_one hv₀
    refine ⟨v₀ ⬝ᵥ (Q *ᵥ v₀), hQ'.2 hv₀ne, fun x => ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      simp
    · have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
      set v := ‖x‖⁻¹ • x with hv
      have hvS : v ∈ Metric.sphere (0 : X → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, hv, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnx.ne']
      have h1 := hmin hvS
      have hxv : x = ‖x‖ • v := by rw [hv, smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
      have hq : x ⬝ᵥ (Q *ᵥ x) = ‖x‖ ^ 2 * (v ⬝ᵥ (Q *ᵥ v)) := by
        conv_lhs => rw [hxv]
        rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
        ring
      rw [hq, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)

omit [DecidableEq X] in
/-- For positive definite `Q`, `x_t'Qx_t → 0` forces `x_t → 0`. -/
theorem ls_tendsto_zero_of_quad_posDef {Q : Matrix X X ℝ} (hQ : Q.PosDef) {x : ℕ → X → ℝ}
    (h : Tendsto (fun t => x t ⬝ᵥ (Q *ᵥ x t)) atTop (𝓝 0)) : Tendsto x atTop (𝓝 0) := by
  obtain ⟨c, hc, hcx⟩ := ls_posDef_coercive hQ
  have h2 : Tendsto (fun t => ‖x t‖ ^ 2) atTop (𝓝 0) := by
    have hl : Tendsto (fun t => x t ⬝ᵥ (Q *ᵥ x t) / c) atTop (𝓝 0) := by
      simpa using h.div_const c
    exact squeeze_zero (fun t => by positivity) (fun t => (le_div_iff₀' hc).2 (hcx (x t))) hl
  have h3 : Tendsto (fun t => Real.sqrt (‖x t‖ ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rwa [Real.sqrt_zero] at this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h3.congr fun t => ?_
  exact Real.sqrt_sq (norm_nonneg _)

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The LQ problem, the Riccati operator and completing the square

Miao, §9.2–§9.3, pp. 294–302. A (one-period) LQ problem `LSProblem` carries the matrices
`A, B, C, Q, R, S` of the transition `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}` (9.1) and of the loss
`r(x, u) = x'Qx + u'Ru + 2x'Su`, and the discount factor `β`. For a matrix `P` set

* `G(P) = R + βB'PB` and `N(P) = S' + βB'PA`;
* the Riccati operator (9.5)/(9.11) `T(P) = Q + βA'PA − (S + βA'PB)G(P)⁻¹(S' + βB'PA)`;
* the gain (9.8)/(9.17) `F(P) = G(P)⁻¹(S' + βB'PA)`;
* the policy map of (9.9) `T_F(P) = Q − F'S' − SF + F'RF + β(A − BF)'P(A − BF)`.

Main algebra (used by Proposition 9.2.1, §9.3 and the exercises):

* `G_posDef`: `R > 0`, `P ≥ 0`, `β ≥ 0` give `G(P) > 0` (Miao, p. 296).
* `TF_F`: `T_{F(P)}(P) = T(P)` (the rewritten Riccati equation of p. 302).
* `TF_eq_T_add`: `T_F(P) = T(P) + (F − F(P))'G(P)(F − F(P))`, hence (9.9): `T(P)` is the
  minimum of `T_F(P)` over `F` in the Loewner order, uniquely at `F(P)` (`TF_ge_T`,
  `TF_eq_T_iff`).
* `loss_add_cont`: completing the square,
  `r(x, u) + β(Ax + Bu)'P(Ax + Bu) = x'T(P)x + (u + F(P)x)'G(P)(u + F(P)x)`.
* `T_transpose`, `T_posSemidef`: `T(P)` is symmetric, and positive semidefinite when the joint
  matrix `[[Q, S], [S', R]]` is (`JointPSD`).
-/

open Matrix

open scoped MatrixOrder

namespace Miao.LinearQuadratic

/-- An LQ problem (Miao, §9.2–§9.3): the transition `x' = Ax + Bu + Cε` (9.1), the loss
`x'Qx + u'Ru + 2x'Su` and the discount factor `β`. -/
structure LSProblem (X U E : Type*) where
  /-- the state transition matrix -/
  A : Matrix X X ℝ
  /-- the control matrix -/
  B : Matrix X U ℝ
  /-- the shock loading -/
  C : Matrix X E ℝ
  /-- the state cost -/
  Q : Matrix X X ℝ
  /-- the control cost -/
  R : Matrix U U ℝ
  /-- the cross cost -/
  S : Matrix X U ℝ
  /-- the discount factor -/
  β : ℝ

namespace LSProblem

variable {X U E : Type*} [Fintype X] [Fintype U] (L : LSProblem X U E)

/-- The period loss `r(x, u) = x'Qx + u'Ru + 2x'Su` (the period return is `−r`). -/
def loss (x : X → ℝ) (u : U → ℝ) : ℝ :=
  x ⬝ᵥ (L.Q *ᵥ x) + u ⬝ᵥ (L.R *ᵥ u) + 2 * (x ⬝ᵥ (L.S *ᵥ u))

/-- The joint cost matrix `[[Q, S], [S', R]]` is positive semidefinite (Proposition 9.2.1). -/
def JointPSD : Prop := (fromBlocks L.Q L.S L.Sᵀ L.R).PosSemidef

/-- `G(P) = R + βB'PB`. -/
def G (P : Matrix X X ℝ) : Matrix U U ℝ := L.R + L.β • (L.Bᵀ * P * L.B)

/-- `N(P) = S' + βB'PA`. -/
def N (P : Matrix X X ℝ) : Matrix U X ℝ := L.Sᵀ + L.β • (L.Bᵀ * P * L.A)

/-- The policy map of (9.9): `T_F(P) = Q − F'S' − SF + F'RF + β(A − BF)'P(A − BF)`. -/
def TF (P : Matrix X X ℝ) (F : Matrix U X ℝ) : Matrix X X ℝ :=
  L.Q - Fᵀ * L.Sᵀ - L.S * F + Fᵀ * L.R * F + L.β • ((L.A - L.B * F)ᵀ * P * (L.A - L.B * F))

variable [DecidableEq U]

/-- The Riccati operator (9.5), (9.11):
`T(P) = Q + βA'PA − (S + βA'PB)(R + βB'PB)⁻¹(S' + βB'PA)`. -/
noncomputable def T (P : Matrix X X ℝ) : Matrix X X ℝ :=
  L.Q + L.β • (L.Aᵀ * P * L.A) - (L.S + L.β • (L.Aᵀ * P * L.B)) * (L.G P)⁻¹ * L.N P

/-- The gain (9.8), (9.17): `F(P) = (R + βB'PB)⁻¹(S' + βB'PA)`; the control is `u = −F(P)x`. -/
noncomputable def F (P : Matrix X X ℝ) : Matrix U X ℝ := (L.G P)⁻¹ * L.N P

omit [Fintype U] [DecidableEq U] in
/-- Miao, p. 296: `R > 0`, `P ≥ 0` (and `β ≥ 0`) make `R + βB'PB` positive definite. -/
theorem G_posDef [Finite U] (hR : L.R.PosDef) {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hβ : 0 ≤ L.β) :
    (L.G P).PosDef :=
  hR.add_posSemidef ((SS.LQProblem.posSemidef_transpose_mul_mul hP L.B).smul hβ)

omit [Fintype U] [DecidableEq U] in
theorem G_transpose (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) : (L.G P)ᵀ = L.G P := by
  simp only [G, transpose_add, transpose_smul, transpose_mul, transpose_transpose, hR, hP,
    Matrix.mul_assoc]

omit [Fintype U] [DecidableEq U] in
theorem N_transpose {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (L.N P)ᵀ = L.S + L.β • (L.Aᵀ * P * L.B) := by
  simp only [N, transpose_add, transpose_smul, transpose_mul, transpose_transpose, hP,
    Matrix.mul_assoc]

/-- `G(P)F(P) = N(P)`. -/
theorem G_mul_F {P : Matrix X X ℝ} (h : IsUnit (L.G P).det) : L.G P * L.F P = L.N P :=
  mul_nonsing_inv_cancel_left _ _ h

theorem T_eq_sub (P : Matrix X X ℝ) :
    L.T P = L.Q + L.β • (L.Aᵀ * P * L.A) - (L.S + L.β • (L.Aᵀ * P * L.B)) * L.F P := by
  simp only [T, F, Matrix.mul_assoc]

omit [DecidableEq U] in
/-- Expanding the policy map: `T_F(P) = Q + βA'PA − F'N(P) − (S + βA'PB)F + F'G(P)F`. -/
theorem TF_expand (P : Matrix X X ℝ) (F' : Matrix U X ℝ) :
    L.TF P F' = L.Q + L.β • (L.Aᵀ * P * L.A) - F'ᵀ * L.N P -
      (L.S + L.β • (L.Aᵀ * P * L.B)) * F' + F'ᵀ * (L.G P * F') := by
  simp only [TF, N, G, transpose_sub, transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    smul_sub]
  abel

/-- Miao, p. 302: the Riccati equation rewritten with `F = F(P)`:
`T(P) = Q + F'RF − SF − F'S' + β(A − BF)'P(A − BF)`. -/
theorem TF_F {P : Matrix X X ℝ} (h : IsUnit (L.G P).det) : L.TF P (L.F P) = L.T P := by
  rw [TF_expand, L.G_mul_F h, T_eq_sub]
  abel

/-- `T_F(P) = T(P) + (F − F(P))'G(P)(F − F(P))` for symmetric `R`, `P`. -/
theorem TF_eq_T_add (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) (h : IsUnit (L.G P).det)
    (F' : Matrix U X ℝ) :
    L.TF P F' = L.T P + (F' - L.F P)ᵀ * L.G P * (F' - L.F P) := by
  have hN : L.N P = L.G P * L.F P := (L.G_mul_F h).symm
  have hNs : L.S + L.β • (L.Aᵀ * P * L.B) = (L.F P)ᵀ * L.G P := by
    rw [← L.N_transpose hP, hN, transpose_mul, L.G_transpose hR hP]
  rw [TF_expand, T_eq_sub, hN, hNs]
  simp only [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- (9.9) (Miao, p. 297): `T(P) ≤ T_F(P)` for every `F` in the Loewner order. -/
theorem TF_ge_T (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) (hG : (L.G P).PosDef)
    (F' : Matrix U X ℝ) : L.T P ≤ L.TF P F' := by
  rw [Matrix.le_iff, L.TF_eq_T_add hR hP ((isUnit_iff_isUnit_det _).1 hG.isUnit) F',
    add_sub_cancel_left]
  exact SS.LQProblem.posSemidef_transpose_mul_mul hG.posSemidef _

/-- (9.9): the minimiser is unique, `T_F(P) = T(P)` iff `F = F(P)`. -/
theorem TF_eq_T_iff (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) (hG : (L.G P).PosDef)
    (F' : Matrix U X ℝ) : L.TF P F' = L.T P ↔ F' = L.F P := by
  classical
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  refine ⟨fun h => ?_, fun h => h ▸ L.TF_F hu⟩
  rw [L.TF_eq_T_add hR hP hu, add_eq_left] at h
  have hG' := SS.LQProblem.posDef_iff_real.1 hG
  have hx : ∀ x, (F' - L.F P) *ᵥ x = 0 := by
    intro x
    by_contra hne
    have h1 := hG'.2 hne
    rw [← SS.LQProblem.dotProduct_transpose_mul_mul, h, zero_mulVec, dotProduct_zero] at h1
    exact lt_irrefl _ h1
  rw [← sub_eq_zero]
  ext i j
  have := congrFun (hx (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-- Completing the square: for symmetric invertible `G`,
`u'Gu + 2u·n = (u + G⁻¹n)'G(u + G⁻¹n) − n'G⁻¹n`. -/
theorem ls_sq_complete {G : Matrix U U ℝ} (hG : Gᵀ = G) (h : IsUnit G.det) (u n : U → ℝ) :
    u ⬝ᵥ (G *ᵥ u) + 2 * (u ⬝ᵥ n) =
      (u + G⁻¹ *ᵥ n) ⬝ᵥ (G *ᵥ (u + G⁻¹ *ᵥ n)) - n ⬝ᵥ (G⁻¹ *ᵥ n) := by
  set f := G⁻¹ *ᵥ n
  have hGf : G *ᵥ f = n := by
    simp only [f, mulVec_mulVec, mul_nonsing_inv _ h, one_mulVec]
  rw [SS.LQProblem.quad_add hG u f, SS.LQProblem.dotProduct_mulVec_comm_of_symm hG f u, hGf,
    dotProduct_comm n f]
  ring

omit [DecidableEq U] in
/-- `x'Su = u'S'x`. -/
theorem dot_S_comm (M : Matrix X U ℝ) (x : X → ℝ) (u : U → ℝ) :
    x ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (Mᵀ *ᵥ x) := by
  rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- Completing the square (Miao, pp. 295–296): for symmetric `R`, `P` and invertible `G(P)`,
`r(x, u) + β(Ax + Bu)'P(Ax + Bu) = x'T(P)x + (u + F(P)x)'G(P)(u + F(P)x)`. -/
theorem loss_add_cont (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (h : IsUnit (L.G P).det) (x : X → ℝ) (u : U → ℝ) :
    L.loss x u + L.β * ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))) =
      x ⬝ᵥ (L.T P *ᵥ x) + (u + L.F P *ᵥ x) ⬝ᵥ (L.G P *ᵥ (u + L.F P *ᵥ x)) := by
  have hGs := L.G_transpose hR hP
  have e1 := SS.LQProblem.quad_add hP (L.A *ᵥ x) (L.B *ᵥ u)
  have e2 : (L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x)) = u ⬝ᵥ ((L.Bᵀ * P * L.A) *ᵥ x) := by
    rw [SS.LQProblem.mulVec_dotProduct, ← mulVec_mulVec, ← mulVec_mulVec]
  have e3 : (L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.B *ᵥ u)) = u ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ u) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul L.B P u).symm
  have e4 : (L.A *ᵥ x) ⬝ᵥ (P *ᵥ (L.A *ᵥ x)) = x ⬝ᵥ ((L.Aᵀ * P * L.A) *ᵥ x) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul L.A P x).symm
  have e5 := dot_S_comm L.S x u
  have eG : u ⬝ᵥ (L.G P *ᵥ u) = u ⬝ᵥ (L.R *ᵥ u) + L.β * (u ⬝ᵥ ((L.Bᵀ * P * L.B) *ᵥ u)) := by
    rw [G, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have eN : u ⬝ᵥ (L.N P *ᵥ x) = u ⬝ᵥ (L.Sᵀ *ᵥ x) + L.β * (u ⬝ᵥ ((L.Bᵀ * P * L.A) *ᵥ x)) := by
    rw [N, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hsq := ls_sq_complete hGs h u (L.N P *ᵥ x)
  have hF : L.F P *ᵥ x = (L.G P)⁻¹ *ᵥ (L.N P *ᵥ x) := by rw [F, mulVec_mulVec]
  have eT : x ⬝ᵥ (L.T P *ᵥ x) = x ⬝ᵥ (L.Q *ᵥ x) + L.β * (x ⬝ᵥ ((L.Aᵀ * P * L.A) *ᵥ x)) -
      (L.N P *ᵥ x) ⬝ᵥ ((L.G P)⁻¹ *ᵥ (L.N P *ᵥ x)) := by
    rw [T, ← L.N_transpose hP, sub_mulVec, add_mulVec, smul_mulVec, dotProduct_sub,
      dotProduct_add, dotProduct_smul, smul_eq_mul, SS.LQProblem.dotProduct_transpose_mul_mul L.A,
      SS.LQProblem.dotProduct_transpose_mul_mul (L.N P)]
  rw [hF, eT]
  simp only [loss]
  rw [e1, e2, e3, e4, e5]
  linear_combination hsq - eG - 2 * eN

omit [DecidableEq U] in
/-- The joint matrix's quadratic form is the loss: `[x; u]'[[Q, S], [S', R]][x; u] = r(x, u)`. -/
theorem quad_joint (x : X → ℝ) (u : U → ℝ) :
    Sum.elim x u ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ Sum.elim x u) = L.loss x u := by
  rw [fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
  rw [sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add, loss,
    ← dot_S_comm L.S x u]
  ring

omit [DecidableEq U] in
/-- Under `JointPSD`, the loss is nonnegative. -/
theorem loss_nonneg (hJ : L.JointPSD) (x : X → ℝ) (u : U → ℝ) : 0 ≤ L.loss x u := by
  rw [← L.quad_joint]
  exact (SS.LQProblem.posSemidef_iff_real.1 hJ).2 _

omit [Fintype X] [Fintype U] [DecidableEq U] in
/-- Under `JointPSD`, `Q` is symmetric. -/
theorem Q_transpose_of_joint [Finite X] [Finite U] (hJ : L.JointPSD) : L.Qᵀ = L.Q := by
  cases nonempty_fintype X
  cases nonempty_fintype U
  have h := (SS.LQProblem.posSemidef_iff_real.1 hJ).1
  rw [fromBlocks_transpose] at h
  exact (Matrix.fromBlocks_inj.1 h).1

omit [Fintype X] [Fintype U] [DecidableEq U] in
/-- Under `JointPSD`, `Q` is positive semidefinite. -/
theorem Q_posSemidef_of_joint [Finite X] [Finite U] (hJ : L.JointPSD) : L.Q.PosSemidef := by
  cases nonempty_fintype X
  cases nonempty_fintype U
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨L.Q_transpose_of_joint hJ, fun x => ?_⟩
  have := L.loss_nonneg hJ x 0
  simpa [loss] using this

/-- `T(P)` is symmetric for symmetric `Q`, `R`, `P` with `G(P)` invertible. -/
theorem T_transpose (hQ : L.Qᵀ = L.Q) (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (L.T P)ᵀ = L.T P := by
  have hNs := L.N_transpose hP
  rw [T, ← hNs, transpose_sub, transpose_add, transpose_mul, transpose_mul, transpose_transpose,
    transpose_smul, transpose_nonsing_inv, L.G_transpose hR hP, hQ]
  simp only [transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]

/-- Miao, p. 295 (`P_t ≥ 0`): under `JointPSD`, `R > 0`, `β ≥ 0` and `P ≥ 0`, `T(P) ≥ 0`. -/
theorem T_posSemidef (hJ : L.JointPSD) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) : (L.T P).PosSemidef := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hu := (isUnit_iff_isUnit_det _).1 (L.G_posDef hR hP hβ).isUnit
  refine SS.LQProblem.posSemidef_iff_real.2
    ⟨L.T_transpose (L.Q_transpose_of_joint hJ) hRs hPs, fun x => ?_⟩
  have h := L.loss_add_cont hRs hPs hu x (-(L.F P *ᵥ x))
  rw [neg_add_cancel, mulVec_zero, dotProduct_zero, add_zero] at h
  rw [← h]
  exact add_nonneg (L.loss_nonneg hJ _ _)
    (mul_nonneg hβ ((SS.LQProblem.posSemidef_iff_real.1 hP).2 _))

end LSProblem

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite-horizon LQ problems: Proposition 9.2.1

Miao, §9.2, pp. 294–297. The non-stationary problem
`max −E[∑_{t<T} βᵗ(x_t'Q_tx_t + u_t'R_tu_t + 2x_t'S_tu_t) + βᵀx_T'P_Tx_T]` subject to
`x_{t+1} = A_tx_t + B_tu_t + C_tε_{t+1}` (`LSFinProblem`; its date-`t` data form the
one-period problem `stage t`).

The shocks enter the Bellman equation only through the conditional law of `ε_{t+1}` given
`F_t`; under Assumption 9.1.1 this law has mean zero and identity second moments. We model it by
a probability measure `ν` on `ℝ^{nε}` with these moments (`LSShockLaw`); see `LSStateSpace` for
Assumption 9.1.1 itself and the conditional-expectation computation of p. 296.

* `ls_integral_quad` (p. 296): `E(y + Cε)'P(y + Cε) = y'Py + tr(PCC')`.
* `LSProblem.bellObj_quad`, `LSProblem.bellObj_isGreatest` (pp. 295–296): with a quadratic
  continuation value `−z'Pz − d`, the Bellman objective is
  `−x'T(P)x − β tr(PCC') − βd − (u + F(P)x)'G(P)(u + F(P)x)`, maximised exactly at
  `u = −F(P)x`; the first-order condition `(R + βB'PB)u = −(S' + βB'PA)x` (`ls_foc`) and the
  first variation (`ls_first_variation`).
* `LSFinProblem.V` is the value function defined by the Bellman recursion (with `sSup`), and
  `P`, `d`, `Fg` are the backward recursions (9.5), (9.6), (9.8).
* **Proposition 9.2.1** (`proposition_9_2_1`): `V_t(x) = −x'P_tx − d_t` (9.4), `P_t ≥ 0`,
  (9.5), (9.6), and the optimal control is `u_t = −F_tx_t` (9.7)–(9.8), uniquely.
* `eq_9_9`: (9.9), `P_t` is the Loewner minimum of `T_F` over `F`, attained at `F_t`.
* `ls_finite_seq_identity`, `ls_finite_seq_optimal`: for the deterministic problem, every control
  sequence satisfies `∑βᵗr_t + βᵀx_T'P_Tx_T = x_0'P_0x_0 + ∑βᵗ(u_t + F_tx_t)'G_t(u_t + F_tx_t)`,
  so the feedback rule is optimal among all (open-loop) sequences, uniquely.
* `certainty_equivalence` (p. 297): `C_t` affects neither `P_t` nor `F_t`, only `d_t`; the value
  of the stochastic problem is that of the deterministic one minus `d_t`, and the decision rules
  coincide.

Departure: Proposition 9.2.1 is stated for `β ∈ (0, 1]`; only `β ≥ 0` is used.
-/

open Matrix MeasureTheory

open scoped MatrixOrder

namespace Miao.LinearQuadratic

variable {X U E : Type*} [Fintype X] [Fintype U] [Fintype E]

/-- The conditional law of `ε_{t+1}` under Assumption 9.1.1: a probability measure on `ℝ^{nε}`
with integrable first and second moments, mean zero and second moments `I`. -/
structure LSShockLaw [DecidableEq E] (ν : Measure (E → ℝ)) : Prop where
  prob : IsProbabilityMeasure ν
  int1 : ∀ k, Integrable (fun e : E → ℝ => e k) ν
  int2 : ∀ k l, Integrable (fun e : E → ℝ => e k * e l) ν
  mean : ∀ k, ∫ e, e k ∂ν = 0
  cov : ∀ k l, ∫ e, e k * e l ∂ν = if k = l then 1 else 0

omit [Fintype X] in
/-- Expanding `(y + Ce)'P(y + Ce)` into constant, linear and quadratic terms in `e`. -/
theorem ls_quad_shock_expand [Fintype X] (y : X → ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ)
    (e : E → ℝ) :
    (y + C *ᵥ e) ⬝ᵥ (P *ᵥ (y + C *ᵥ e)) = y ⬝ᵥ (P *ᵥ y) +
      ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k +
      ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l) := by
  have h1 : y ⬝ᵥ (P *ᵥ (C *ᵥ e)) = ∑ k, (y ᵥ* (P * C)) k * e k := by
    rw [mulVec_mulVec, dotProduct_mulVec]
    rfl
  have h2 : (C *ᵥ e) ⬝ᵥ (P *ᵥ y) = ∑ k, (Cᵀ *ᵥ (P *ᵥ y)) k * e k := by
    rw [SS.LQProblem.mulVec_dotProduct, dotProduct_comm]
    rfl
  have h3 : (C *ᵥ e) ⬝ᵥ (P *ᵥ (C *ᵥ e)) = ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l) := by
    rw [← SS.LQProblem.dotProduct_transpose_mul_mul]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2, h3]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- Miao, p. 296: `E[(y + Cε)'P(y + Cε)] = y'Py + tr(PCC')` when `ε` has mean zero and second
moments `I` (and the integrand is integrable). -/
theorem ls_integral_quad [DecidableEq E] {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (y : X → ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Integrable (fun e : E → ℝ => (y + C *ᵥ e) ⬝ᵥ (P *ᵥ (y + C *ᵥ e))) ν ∧
      ∫ e, (y + C *ᵥ e) ⬝ᵥ (P *ᵥ (y + C *ᵥ e)) ∂ν = y ⬝ᵥ (P *ᵥ y) + trace (P * C * Cᵀ) := by
  have := hν.prob
  simp only [ls_quad_shock_expand]
  have hlin : Integrable (fun e : E → ℝ => ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k) ν :=
    integrable_finsetSum _ fun k _ => (hν.int1 k).const_mul _
  have hq : Integrable (fun e : E → ℝ => ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l)) ν :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hν.int2 k l).const_mul _
  have hcl : Integrable (fun e : E → ℝ => y ⬝ᵥ (P *ᵥ y) +
      ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k) ν := (integrable_const _).add hlin
  refine ⟨hcl.add hq, ?_⟩
  have hlin0 : ∫ e, ∑ k, (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k ∂ν = 0 := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => (y ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ y)) k * e k)
      _ fun k _ => (hν.int1 k).const_mul _]
    simp [integral_const_mul, hν.mean]
  have hrow : ∀ k, ∫ e, ∑ l, (Cᵀ * P * C) k l * (e k * e l) ∂ν = (Cᵀ * P * C) k k := by
    intro k
    rw [integral_finsetSum (f := fun l (e : E → ℝ) => (Cᵀ * P * C) k l * (e k * e l)) _
      fun l _ => (hν.int2 k l).const_mul _]
    simp [integral_const_mul, hν.cov]
  have hq0 : ∫ e, ∑ k, ∑ l, (Cᵀ * P * C) k l * (e k * e l) ∂ν = trace (Cᵀ * P * C) := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => ∑ l, (Cᵀ * P * C) k l * (e k * e l)) _
      fun k _ => integrable_finsetSum _ fun l _ => (hν.int2 k l).const_mul _]
    simp only [hrow]
    rfl
  have htr : trace (Cᵀ * P * C) = trace (P * C * Cᵀ) := by rw [Matrix.mul_assoc, trace_mul_comm]
  rw [integral_add hcl hq, integral_add (integrable_const _) hlin, integral_const, hlin0, hq0,
    probReal_univ, one_smul, add_zero, htr]

namespace LSProblem

variable (L : LSProblem X U E)

/-- The Bellman objective with continuation value `W`:
`−r(x, u) + βE W(Ax + Bu + Cε)`. -/
noncomputable def bellObj (ν : Measure (E → ℝ)) (W : (X → ℝ) → ℝ) (x : X → ℝ) (u : U → ℝ) :
    ℝ :=
  -L.loss x u + L.β * ∫ e, W (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν

variable [DecidableEq U] [DecidableEq E]

/-- Miao, pp. 295–296: with the quadratic continuation value `−z'Pz − d`,
`−r(x, u) + βE V(x') = −x'T(P)x − (β tr(PCC') + βd) − (u + F(P)x)'G(P)(u + F(P)x)`. -/
theorem bellObj_quad {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.Rᵀ = L.R)
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hu : IsUnit (L.G P).det) (d : ℝ) (x : X → ℝ)
    (u : U → ℝ) :
    L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x u =
      -(x ⬝ᵥ (L.T P *ᵥ x)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * d) -
        (u + L.F P *ᵥ x) ⬝ᵥ (L.G P *ᵥ (u + L.F P *ᵥ x)) := by
  have := hν.prob
  obtain ⟨hint, heq⟩ := ls_integral_quad hν (L.A *ᵥ x + L.B *ᵥ u) L.C P
  have hI : ∫ e, (-((L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ⬝ᵥ
      (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e))) - d) ∂ν =
      -((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u)) + trace (P * L.C * L.Cᵀ)) - d := by
    have hn : Integrable (fun e : E → ℝ => -((L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ⬝ᵥ
        (P *ᵥ (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)))) ν := hint.neg
    rw [integral_sub hn (integrable_const d), integral_neg, heq, integral_const,
      probReal_univ, one_smul]
  have hsq := L.loss_add_cont hR hP hu x u
  rw [bellObj, hI]
  linear_combination -hsq

/-- Miao, pp. 295–296: the Bellman maximum with continuation `−z'Pz − d` is
`−x'T(P)x − β tr(PCC') − βd`, attained exactly at `u = −F(P)x`. -/
theorem bellObj_isGreatest {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.R.PosDef)
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (hβ : 0 ≤ L.β) (d : ℝ) (x : X → ℝ) :
    IsGreatest (Set.range (L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x))
        (-(x ⬝ᵥ (L.T P *ᵥ x)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * d)) ∧
      ∀ u, L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x u =
          -(x ⬝ᵥ (L.T P *ᵥ x)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * d) ↔
        u = -(L.F P *ᵥ x) := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hG := L.G_posDef hR hP hβ
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  have hG' := SS.LQProblem.posDef_iff_real.1 hG
  have hq : ∀ v, 0 ≤ v ⬝ᵥ (L.G P *ᵥ v) := (SS.LQProblem.posSemidef_iff_real.1 hG.posSemidef).2
  refine ⟨⟨⟨-(L.F P *ᵥ x), ?_⟩, ?_⟩, fun u => ?_⟩
  · rw [L.bellObj_quad hν hRs hPs hu, neg_add_cancel, mulVec_zero, dotProduct_zero, sub_zero]
  · rintro _ ⟨u, rfl⟩
    rw [L.bellObj_quad hν hRs hPs hu]
    linarith [hq (u + L.F P *ᵥ x)]
  · rw [L.bellObj_quad hν hRs hPs hu, sub_eq_self]
    constructor
    · intro h
      by_contra hne
      have : u + L.F P *ᵥ x ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      linarith [hG'.2 this]
    · rintro rfl
      rw [neg_add_cancel, mulVec_zero, dotProduct_zero]

omit [DecidableEq E] [Fintype E] in
/-- The first-order condition (Miao, p. 296): `(R + βB'PB)u = −(S' + βB'PA)x` iff
`u = −F(P)x`. -/
theorem ls_foc {P : Matrix X X ℝ} (hu : IsUnit (L.G P).det) (x : X → ℝ) (u : U → ℝ) :
    L.G P *ᵥ u = -(L.N P *ᵥ x) ↔ u = -(L.F P *ᵥ x) := by
  constructor
  · intro h
    have := congrArg (fun v => (L.G P)⁻¹ *ᵥ v) h
    simp only [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, mulVec_neg] at this
    rw [this, F, ← mulVec_mulVec]
  · rintro rfl
    rw [mulVec_neg, mulVec_mulVec, G_mul_F _ hu]

/-- The first variation of the Bellman objective in the control (Miao, p. 296, footnote 1):
`obj(u + h) − obj(u) = −2h'(G(P)u + N(P)x) − h'G(P)h`; it vanishes to first order iff the
first-order condition `G(P)u + N(P)x = 0` holds. -/
theorem ls_first_variation {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.Rᵀ = L.R)
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hu : IsUnit (L.G P).det) (d : ℝ) (x : X → ℝ)
    (u h : U → ℝ) :
    L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x (u + h) -
        L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) x u =
      -2 * (h ⬝ᵥ (L.G P *ᵥ u + L.N P *ᵥ x)) - h ⬝ᵥ (L.G P *ᵥ h) := by
  have hGs := L.G_transpose hR hP
  rw [L.bellObj_quad hν hR hP hu, L.bellObj_quad hν hR hP hu]
  have hNF : L.N P *ᵥ x = L.G P *ᵥ (L.F P *ᵥ x) := by rw [mulVec_mulVec, G_mul_F _ hu]
  have e := SS.LQProblem.quad_add hGs (u + L.F P *ᵥ x) h
  rw [show u + h + L.F P *ᵥ x = u + L.F P *ᵥ x + h by abel, e, hNF,
    SS.LQProblem.dotProduct_mulVec_comm_of_symm hGs h, ← mulVec_add,
    SS.LQProblem.dotProduct_mulVec_comm_of_symm hGs h (u + L.F P *ᵥ x)]
  ring

end LSProblem

/-- The non-stationary finite-horizon problem of §9.2 (Miao, p. 294): date-`t` matrices
`A_t, B_t, C_t, Q_t, R_t, S_t`, discount factor `β`, horizon `T` (`hor`) and terminal `P_T`. -/
structure LSFinProblem (X U E : Type*) where
  /-- `A_t` -/
  A : ℕ → Matrix X X ℝ
  /-- `B_t` -/
  B : ℕ → Matrix X U ℝ
  /-- `C_t` -/
  C : ℕ → Matrix X E ℝ
  /-- `Q_t` -/
  Q : ℕ → Matrix X X ℝ
  /-- `R_t` -/
  R : ℕ → Matrix U U ℝ
  /-- `S_t` -/
  S : ℕ → Matrix X U ℝ
  /-- the discount factor -/
  β : ℝ
  /-- the horizon `T` -/
  hor : ℕ
  /-- the terminal matrix `P_T` -/
  PT : Matrix X X ℝ

namespace LSFinProblem

variable (L : LSFinProblem X U E)

/-- The date-`t` one-period problem. -/
def stage (t : ℕ) : LSProblem X U E := ⟨L.A t, L.B t, L.C t, L.Q t, L.R t, L.S t, L.β⟩

variable [DecidableEq U]

/-- The Riccati recursion (9.5), indexed by the number `s` of remaining periods. -/
noncomputable def Pbk : ℕ → Matrix X X ℝ
  | 0 => L.PT
  | s + 1 => (L.stage (L.hor - s - 1)).T (Pbk s)

/-- The constants (9.6), indexed by the number of remaining periods. -/
noncomputable def dbk : ℕ → ℝ
  | 0 => 0
  | s + 1 => L.β * trace (L.Pbk s * L.C (L.hor - s - 1) * (L.C (L.hor - s - 1))ᵀ) + L.β * dbk s

/-- `P_t` (9.5). -/
noncomputable def P (t : ℕ) : Matrix X X ℝ := L.Pbk (L.hor - t)

/-- `d_t` (9.6). -/
noncomputable def d (t : ℕ) : ℝ := L.dbk (L.hor - t)

/-- The gain `F_t = (R_t + βB_t'P_{t+1}B_t)⁻¹(S_t' + βB_t'P_{t+1}A_t)` (9.8). -/
noncomputable def Fg (t : ℕ) : Matrix U X ℝ := (L.stage t).F (L.P (t + 1))

/-- The value function, defined by the Bellman recursion
`V_t(x) = sup_u {−r_t(x, u) + βE V_{t+1}(A_tx + B_tu + C_tε)}`, `V_T(x) = −x'P_Tx`, indexed by
the number of remaining periods. -/
noncomputable def Vbk (ν : Measure (E → ℝ)) : ℕ → (X → ℝ) → ℝ
  | 0 => fun x => -(x ⬝ᵥ (L.PT *ᵥ x))
  | s + 1 => fun x => sSup (Set.range ((L.stage (L.hor - s - 1)).bellObj ν (Vbk ν s) x))

/-- The value function `V_t`. -/
noncomputable def V (ν : Measure (E → ℝ)) (t : ℕ) (x : X → ℝ) : ℝ := L.Vbk ν (L.hor - t) x

omit [Fintype E] in
theorem P_hor : L.P L.hor = L.PT := by simp [P, Pbk]

theorem d_hor : L.d L.hor = 0 := by simp [d, dbk]

omit [DecidableEq U] in
theorem V_hor (ν : Measure (E → ℝ)) (x : X → ℝ) : L.V ν L.hor x = -(x ⬝ᵥ (L.PT *ᵥ x)) := by
  simp [V, Vbk]

omit [Fintype E] in
/-- (9.5): `P_t = T_t(P_{t+1})` for `t < T`. -/
theorem P_succ {t : ℕ} (ht : t < L.hor) : L.P t = (L.stage t).T (L.P (t + 1)) := by
  have h1 : L.hor - t = L.hor - (t + 1) + 1 := by omega
  have h2 : L.hor - (L.hor - (t + 1)) - 1 = t := by omega
  rw [P, h1, Pbk, h2]
  rfl

/-- (9.6): `d_t = β tr(P_{t+1}C_tC_t') + βd_{t+1}` for `t < T`. -/
theorem d_succ {t : ℕ} (ht : t < L.hor) :
    L.d t = L.β * trace (L.P (t + 1) * L.C t * (L.C t)ᵀ) + L.β * L.d (t + 1) := by
  have h1 : L.hor - t = L.hor - (t + 1) + 1 := by omega
  have h2 : L.hor - (L.hor - (t + 1)) - 1 = t := by omega
  rw [d, h1, dbk, h2]
  rfl

omit [DecidableEq U] in
/-- The Bellman equation defining `V_t`, `t < T`. -/
theorem V_succ (ν : Measure (E → ℝ)) {t : ℕ} (ht : t < L.hor) (x : X → ℝ) :
    L.V ν t x = sSup (Set.range ((L.stage t).bellObj ν (L.V ν (t + 1)) x)) := by
  have h1 : L.hor - t = L.hor - (t + 1) + 1 := by omega
  have h2 : L.hor - (L.hor - (t + 1)) - 1 = t := by omega
  rw [V, h1, Vbk, h2]
  rfl

variable [DecidableEq E]

/-- **Proposition 9.2.1** (Miao, p. 295). Suppose `[[Q_t, S_t], [S_t', R_t]] ≥ 0`, `R_t > 0`
(`t < T`) and `P_T ≥ 0` (and `β ≥ 0`). Then for `t ≤ T`:
(i) the value function is `V_t(x) = −x'P_tx − d_t` (9.4), with `P_t ≥ 0`; `P_t` satisfies
(9.5) and `d_t` satisfies (9.6), `d_T = 0`;
(ii) for `t < T` the optimal control is `u_t = −F_tx_t` (9.7)–(9.8): it attains the Bellman
maximum, and it is the only control that does. -/
theorem proposition_9_2_1 {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (hJ : ∀ t < L.hor, (L.stage t).JointPSD) (hR : ∀ t < L.hor, (L.R t).PosDef)
    (hPT : L.PT.PosSemidef) (hβ : 0 ≤ L.β) :
    (∀ t ≤ L.hor, ∀ x, L.V ν t x = -(x ⬝ᵥ (L.P t *ᵥ x)) - L.d t) ∧
    (∀ t ≤ L.hor, (L.P t).PosSemidef) ∧
    (∀ t < L.hor, L.P t = L.Q t + L.β • ((L.A t)ᵀ * L.P (t + 1) * L.A t) -
      (L.S t + L.β • ((L.A t)ᵀ * L.P (t + 1) * L.B t)) *
        (L.R t + L.β • ((L.B t)ᵀ * L.P (t + 1) * L.B t))⁻¹ *
        (L.β • ((L.B t)ᵀ * L.P (t + 1) * L.A t) + (L.S t)ᵀ)) ∧
    (∀ t < L.hor, L.d t = L.β * trace (L.P (t + 1) * L.C t * (L.C t)ᵀ) + L.β * L.d (t + 1)) ∧
    L.d L.hor = 0 ∧
    (∀ t < L.hor, ∀ x, IsGreatest (Set.range ((L.stage t).bellObj ν (L.V ν (t + 1)) x))
        (L.V ν t x) ∧
      ∀ u, (L.stage t).bellObj ν (L.V ν (t + 1)) x u = L.V ν t x ↔ u = -(L.Fg t *ᵥ x)) := by
  -- the induction on the number of remaining periods
  have key : ∀ s ≤ L.hor, (L.Pbk s).PosSemidef ∧
      ∀ x, L.Vbk ν s x = -(x ⬝ᵥ (L.Pbk s *ᵥ x)) - L.dbk s := by
    intro s
    induction s with
    | zero => exact fun _ => ⟨hPT, fun x => by simp [Pbk, Vbk, dbk]⟩
    | succ s ih =>
      intro hs
      obtain ⟨hP, hV⟩ := ih (by omega)
      have ht : L.hor - s - 1 < L.hor := by omega
      have hW : L.Vbk ν s = fun z => -(z ⬝ᵥ (L.Pbk s *ᵥ z)) - L.dbk s := funext hV
      refine ⟨(L.stage _).T_posSemidef (hJ _ ht) (hR _ ht) hβ hP, fun x => ?_⟩
      have hg := ((L.stage (L.hor - s - 1)).bellObj_isGreatest hν (hR _ ht) hP hβ
        (L.dbk s) x).1
      simp only [Vbk, Pbk, dbk]
      rw [hW, hg.csSup_eq]
      rfl
  have hV : ∀ t ≤ L.hor, ∀ x, L.V ν t x = -(x ⬝ᵥ (L.P t *ᵥ x)) - L.d t :=
    fun t _ x => (key (L.hor - t) (by omega)).2 x
  have hP : ∀ t ≤ L.hor, (L.P t).PosSemidef := fun t _ => (key (L.hor - t) (by omega)).1
  refine ⟨hV, hP, fun t ht => ?_, fun t ht => L.d_succ ht, L.d_hor, fun t ht x => ?_⟩
  · rw [L.P_succ ht, LSProblem.T, LSProblem.N, add_comm (L.stage t).Sᵀ]
    rfl
  · have hW : L.V ν (t + 1) = fun z => -(z ⬝ᵥ (L.P (t + 1) *ᵥ z)) - L.d (t + 1) :=
      funext (hV (t + 1) ht)
    obtain ⟨hg, hu⟩ := (L.stage t).bellObj_isGreatest hν (hR t ht) (hP (t + 1) ht) hβ
      (L.d (t + 1)) x
    have hVt : L.V ν t x = -(x ⬝ᵥ ((L.stage t).T (L.P (t + 1)) *ᵥ x)) -
        (L.β * trace (L.P (t + 1) * L.C t * (L.C t)ᵀ) + L.β * L.d (t + 1)) := by
      rw [hV t ht.le, L.P_succ ht, L.d_succ ht]
    rw [hW, hVt]
    exact ⟨hg, hu⟩

omit [DecidableEq E] [Fintype E] in
/-- (9.9) (Miao, p. 297): `P_t = min_F [Q_t − F'S_t' − S_tF + F'R_tF + β(A_t − B_tF)'P_{t+1}
(A_t − B_tF)]` in the Loewner order, the minimum being attained exactly at `F = F_t`. -/
theorem eq_9_9 (hJ : ∀ t < L.hor, (L.stage t).JointPSD) (hR : ∀ t < L.hor, (L.R t).PosDef)
    (hPT : L.PT.PosSemidef) (hβ : 0 ≤ L.β) {t : ℕ} (ht : t < L.hor) :
    (∀ F' : Matrix U X ℝ, L.P t ≤ (L.stage t).TF (L.P (t + 1)) F') ∧
      ∀ F' : Matrix U X ℝ, (L.stage t).TF (L.P (t + 1)) F' = L.P t ↔ F' = L.Fg t := by
  have hPpsd : ∀ s ≤ L.hor, (L.Pbk s).PosSemidef := by
    intro s
    induction s with
    | zero => exact fun _ => hPT
    | succ s ih =>
      intro hs
      exact (L.stage _).T_posSemidef (hJ _ (by omega)) (hR _ (by omega)) hβ (ih (by omega))
  have hP1 : (L.P (t + 1)).PosSemidef := hPpsd _ (by omega)
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP1).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 (hR t ht)).1
  have hG := (L.stage t).G_posDef (hR t ht) hP1 hβ
  rw [L.P_succ ht]
  exact ⟨(L.stage t).TF_ge_T hRs hPs hG, (L.stage t).TF_eq_T_iff hRs hPs hG⟩

omit [DecidableEq E] [Fintype E] in
/-- Completing the square along a deterministic path (Miao, pp. 295–297): if
`x_{t+1} = A_tx_t + B_tu_t` for `t < T`, then
`∑_{t<T} βᵗr_t(x_t, u_t) + βᵀx_T'P_Tx_T = x_0'P_0x_0 + ∑_{t<T} βᵗ(u_t + F_tx_t)'G_t(u_t + F_tx_t)`,
where `G_t = R_t + βB_t'P_{t+1}B_t`. -/
theorem ls_finite_seq_identity (hRs : ∀ t < L.hor, (L.R t)ᵀ = L.R t)
    (hPs : ∀ t ≤ L.hor, (L.P t)ᵀ = L.P t)
    (hu : ∀ t < L.hor, IsUnit ((L.stage t).G (L.P (t + 1))).det)
    (x : ℕ → X → ℝ) (u : ℕ → U → ℝ) (hx : ∀ t < L.hor, x (t + 1) = L.A t *ᵥ x t + L.B t *ᵥ u t) :
    ∑ t ∈ Finset.range L.hor, L.β ^ t * (L.stage t).loss (x t) (u t) +
        L.β ^ L.hor * (x L.hor ⬝ᵥ (L.PT *ᵥ x L.hor)) =
      x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) + ∑ t ∈ Finset.range L.hor, L.β ^ t *
        ((u t + L.Fg t *ᵥ x t) ⬝ᵥ ((L.stage t).G (L.P (t + 1)) *ᵥ (u t + L.Fg t *ᵥ x t))) := by
  have step : ∀ n ≤ L.hor, ∑ t ∈ Finset.range n, L.β ^ t * (L.stage t).loss (x t) (u t) +
      L.β ^ n * (x n ⬝ᵥ (L.P n *ᵥ x n)) = x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) +
      ∑ t ∈ Finset.range n, L.β ^ t *
        ((u t + L.Fg t *ᵥ x t) ⬝ᵥ ((L.stage t).G (L.P (t + 1)) *ᵥ (u t + L.Fg t *ᵥ x t))) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have ht : n < L.hor := by omega
      have hsq := (L.stage n).loss_add_cont (hRs n ht) (hPs (n + 1) hn) (hu n ht) (x n) (u n)
      rw [← L.P_succ ht] at hsq
      have hx' : (L.stage n).A *ᵥ x n + (L.stage n).B *ᵥ u n = x (n + 1) := (hx n ht).symm
      rw [hx'] at hsq
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hb : (L.stage n).β = L.β := rfl
      rw [hb] at hsq
      simp only [Fg] at ih ⊢
      linear_combination ih (by omega) + L.β ^ n * hsq
  have := step L.hor le_rfl
  rwa [L.P_hor] at this

omit [DecidableEq E] [Fintype E] in
/-- Optimality of the feedback rule among all control sequences for the deterministic problem
(Miao, pp. 296–297): under the hypotheses of Proposition 9.2.1 and `β > 0`, every sequence
satisfies `∑_{t<T} βᵗr_t + βᵀx_T'P_Tx_T ≥ x_0'P_0x_0`, with equality iff `u_t = −F_tx_t` for all
`t < T`. -/
theorem ls_finite_seq_optimal (hJ : ∀ t < L.hor, (L.stage t).JointPSD)
    (hR : ∀ t < L.hor, (L.R t).PosDef) (hPT : L.PT.PosSemidef) (hβ : 0 < L.β)
    (x : ℕ → X → ℝ) (u : ℕ → U → ℝ) (hx : ∀ t < L.hor, x (t + 1) = L.A t *ᵥ x t + L.B t *ᵥ u t) :
    x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) ≤ ∑ t ∈ Finset.range L.hor, L.β ^ t * (L.stage t).loss (x t) (u t) +
        L.β ^ L.hor * (x L.hor ⬝ᵥ (L.PT *ᵥ x L.hor)) ∧
      (x 0 ⬝ᵥ (L.P 0 *ᵥ x 0) = ∑ t ∈ Finset.range L.hor, L.β ^ t * (L.stage t).loss (x t) (u t) +
        L.β ^ L.hor * (x L.hor ⬝ᵥ (L.PT *ᵥ x L.hor)) ↔ ∀ t < L.hor, u t = -(L.Fg t *ᵥ x t)) := by
  have hPpsd : ∀ s ≤ L.hor, (L.Pbk s).PosSemidef := by
    intro s
    induction s with
    | zero => exact fun _ => hPT
    | succ s ih =>
      intro hs
      exact (L.stage _).T_posSemidef (hJ _ (by omega)) (hR _ (by omega)) hβ.le (ih (by omega))
  have hP : ∀ t ≤ L.hor, (L.P t).PosSemidef := fun t _ => hPpsd _ (by omega)
  have hG : ∀ t < L.hor, ((L.stage t).G (L.P (t + 1))).PosDef := fun t ht =>
    (L.stage t).G_posDef (hR t ht) (hP (t + 1) ht) hβ.le
  have hid := L.ls_finite_seq_identity (fun t ht => (SS.LQProblem.posDef_iff_real.1 (hR t ht)).1)
    (fun t ht => (SS.LQProblem.posSemidef_iff_real.1 (hP t ht)).1)
    (fun t ht => (isUnit_iff_isUnit_det _).1 (hG t ht).isUnit) x u hx
  have hnn : ∀ t ∈ Finset.range L.hor, 0 ≤ L.β ^ t *
      ((u t + L.Fg t *ᵥ x t) ⬝ᵥ ((L.stage t).G (L.P (t + 1)) *ᵥ (u t + L.Fg t *ᵥ x t))) :=
    fun t ht => mul_nonneg (pow_nonneg hβ.le t)
      ((SS.LQProblem.posSemidef_iff_real.1 (hG t (Finset.mem_range.1 ht)).posSemidef).2 _)
  rw [hid]
  refine ⟨le_add_of_nonneg_right (Finset.sum_nonneg hnn), ?_⟩
  rw [left_eq_add, Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h t ht
    have h1 := h t (Finset.mem_range.2 ht)
    rw [mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (pow_ne_zero _ hβ.ne')
    · by_contra hne
      have : u t + L.Fg t *ᵥ x t ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      have := (SS.LQProblem.posDef_iff_real.1 (hG t ht)).2 this
      linarith
  · intro h t ht
    rw [h t (Finset.mem_range.1 ht), neg_add_cancel, mulVec_zero, dotProduct_zero, mul_zero]

/-- The same problem with the shock loadings `C_t` set to zero: the corresponding deterministic
problem. -/
def zeroC : LSFinProblem X U E := { L with C := fun _ => 0 }

omit [DecidableEq E] [Fintype E] in
theorem zeroC_Pbk (s : ℕ) : L.zeroC.Pbk s = L.Pbk s := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [Pbk, ih]; rfl

omit [DecidableEq E] in
theorem zeroC_dbk (s : ℕ) : L.zeroC.dbk s = 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [dbk, ih]
    simp [zeroC]

/-- **Certainty equivalence principle** (Miao, p. 297): the shock loadings affect neither the
Riccati matrices `P_t` nor the decision rules `F_t`; they only shift the constants `d_t` (which
vanish in the deterministic problem). Hence the value of the stochastic problem is that of the
deterministic problem minus `d_t`, and the two problems have the same optimal decision rule
`u_t = −F_tx_t`. -/
theorem certainty_equivalence {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (hJ : ∀ t < L.hor, (L.stage t).JointPSD) (hR : ∀ t < L.hor, (L.R t).PosDef)
    (hPT : L.PT.PosSemidef) (hβ : 0 ≤ L.β) :
    (∀ t, L.zeroC.P t = L.P t) ∧ (∀ t, L.zeroC.Fg t = L.Fg t) ∧ (∀ t, L.zeroC.d t = 0) ∧
    (∀ t ≤ L.hor, ∀ x, L.V ν t x = L.zeroC.V ν t x - L.d t) ∧
    (∀ t < L.hor, ∀ x u, (L.stage t).bellObj ν (L.V ν (t + 1)) x u = L.V ν t x ↔
      (L.zeroC.stage t).bellObj ν (L.zeroC.V ν (t + 1)) x u = L.zeroC.V ν t x) := by
  have hPe : ∀ t, L.zeroC.P t = L.P t := fun t => L.zeroC_Pbk _
  have hFe : ∀ t, L.zeroC.Fg t = L.Fg t := fun t => by
    simp only [Fg, hPe]
    rfl
  have hde : ∀ t, L.zeroC.d t = 0 := fun t => L.zeroC_dbk _
  have h1 := L.proposition_9_2_1 hν hJ hR hPT hβ
  have h0 := L.zeroC.proposition_9_2_1 hν hJ hR hPT hβ
  refine ⟨hPe, hFe, hde, fun t ht x => ?_, fun t ht x u => ?_⟩
  · rw [h1.1 t ht, h0.1 t ht, hPe, hde]
    ring
  · rw [(h1.2.2.2.2.2 t ht x).2 u, (h0.2.2.2.2.2 t ht x).2 u, hFe]

end LSFinProblem

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The controlled linear state-space system (Miao §9.1)

Miao, §9.1, pp. 291–294.

* **Assumption 9.1.1** (`LSAssumption911`): `E[ε_{t+1} | F_t] = 0`, `E[ε_{t+1}ε'_{t+1} | F_t] = I`;
  and the computation of p. 296 in this setting (`ls_condExp_quad`):
  `E_t(y + Cε_{t+1})'P(y + Cε_{t+1}) = y'Py + tr(PCC')` for `F_t`-measurable `y`.
* The state transition equation (9.1) (`ls_state`; deterministic `ls_traj`) and the measurement
  equation (9.2) (`ls_output`).
* **Definition 9.1.1** (`ls_Stabilizable`) with its motivation: under `u_t = Hx_t`,
  `x_{t+1} = (A + BH)x_t + Cε_{t+1}` and the deterministic steady state `0` is stable iff `A + BH`
  is stable (`definition_9_1_1_closed_loop`, `definition_9_1_1_steady_state`).
* **Definition 9.1.2** (`ls_Controllable`: `∑_{j<nₓ} AʲBB'A'ʲ > 0`) and its equivalence with
  reachability (`definition_9_1_2_iff`): every state can be steered to every target in `r` steps
  for every `r ≥ nₓ` — but not "for any `r > 0`" as printed (`ls_controllable_not_reach_one`).
* Stabilizable does not imply controllable (`ls_stabilizable_not_controllable`, the book's
  example: `A` stable, `B = 0`); controllable implies stabilizable is
  `controllable_stabilizable` in `LSInfiniteHorizon`.
* **Definition 9.1.3** (`ls_Observable`: `∑_{j<nₓ} A'ʲG'GAʲ > 0`) and its equivalence with the
  determination of `x₀` from `y₀, …, y_r` (knowing the inputs and shocks) for every
  `r ≥ nₓ − 1` (`definition_9_1_3_iff`), not for every `r > 0` (`ls_observable_not_two_outputs`).
* **Definition 9.1.4** (`ls_Detectable`) and its motivation (9.3): the estimation error obeys
  `Δ_{t+1} = (A − AKG)Δ_t + Cε_{t+1} − AKDε_t` (`eq_9_3_error`; the book prints `Δ_{t−1}` and
  `+AKDε_t`), and if `A − AKG` is stable the noise-free error vanishes (`eq_9_3_tendsto`); for
  invertible `A` a detecting `J` gives such a `K = A⁻¹J` (`definition_9_1_4_rule`).
-/

open Filter Topology Matrix MeasureTheory

namespace Miao.LinearQuadratic

variable {X U : Type*} [Fintype X] [DecidableEq X] [Fintype U]

/-! ### Assumption 9.1.1 -/

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} [DecidableEq E] (μ : Measure Ω)
  (ℱ : Filtration ℕ m0) (ε : ℕ → Ω → E → ℝ) in
/-- **Assumption 9.1.1** (Miao, p. 291): (i) `E[ε_{t+1} | F_t] = 0`;
(ii) `E[ε_{t+1}ε'_{t+1} | F_t] = I`. -/
structure LSAssumption911 : Prop where
  /-- (i) -/
  mean : ∀ t k, μ[fun ω => ε (t + 1) ω k | ℱ t] =ᵐ[μ] 0
  /-- (ii) -/
  cov : ∀ t k l, μ[fun ω => ε (t + 1) ω k * ε (t + 1) ω l | ℱ t] =ᵐ[μ]
    fun _ => if k = l then 1 else 0

omit [DecidableEq X] [Fintype U] in
/-- Miao, p. 296, in the setting of Assumption 9.1.1: for `F_t`-measurable square-integrable `y`
and square-integrable `ε_{t+1}`, `E_t[(y + Cε_{t+1})'P(y + Cε_{t+1})] = y'Py + tr(PCC')`. -/
theorem ls_condExp_quad {Ω E : Type*} {m0 : MeasurableSpace Ω} [Fintype E] [DecidableEq E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {ε : ℕ → Ω → E → ℝ}
    (hA : LSAssumption911 μ ℱ ε) {t : ℕ} (hε : ∀ k, MemLp (fun ω => ε (t + 1) ω k) 2 μ)
    {y : Ω → X → ℝ} (hym : ∀ i, Measurable[ℱ t] fun ω => y ω i)
    (hy : ∀ i, MemLp (fun ω => y ω i) 2 μ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    μ[fun ω => (y ω + C *ᵥ ε (t + 1) ω) ⬝ᵥ (P *ᵥ (y ω + C *ᵥ ε (t + 1) ω)) | ℱ t] =ᵐ[μ]
      fun ω => y ω ⬝ᵥ (P *ᵥ y ω) + trace (P * C * Cᵀ) := by
  set W : Matrix X E ℝ := P * C + Pᵀ * C
  set M : Matrix E E ℝ := Cᵀ * P * C
  have hm := ℱ.le t
  -- the linear coefficients
  have ha : ∀ (z : X → ℝ) k, (z ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ z)) k = ∑ i, W i k * z i := by
    intro z k
    simp only [W, Pi.add_apply, vecMul, mulVec, dotProduct, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib, transpose_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (f := fun j i => C j k * (P j i * z i))]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hexp : (fun ω => (y ω + C *ᵥ ε (t + 1) ω) ⬝ᵥ (P *ᵥ (y ω + C *ᵥ ε (t + 1) ω))) =
      (fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j)) +
      (fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k)) +
      (fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) := by
    funext ω
    rw [ls_quad_shock_expand]
    simp only [Pi.add_apply, ha, Finset.sum_mul]
    congr 2
    · simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  -- integrability
  have hyy : ∀ i j, Integrable (fun ω => y ω i * y ω j) μ := fun i j =>
    (hy i).integrable_mul (hy j)
  have hye : ∀ i k, Integrable (fun ω => y ω i * ε (t + 1) ω k) μ := fun i k =>
    (hy i).integrable_mul (hε k)
  have hee : ∀ k l, Integrable (fun ω => ε (t + 1) ω k * ε (t + 1) ω l) μ := fun k l =>
    (hε k).integrable_mul (hε l)
  have hi1 : Integrable (fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hyy i j).const_mul _
  have hi2 : ∀ k, Integrable (fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) μ := fun k =>
    integrable_finsetSum _ fun i _ => (hye i k).const_mul _
  have hi2' : Integrable (fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k)) μ :=
    integrable_finsetSum _ fun k _ => hi2 k
  have hi3 : ∀ k, Integrable (fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) μ :=
    fun k => integrable_finsetSum _ fun l _ => (hee k l).const_mul _
  have hi3' : Integrable (fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) μ :=
    integrable_finsetSum _ fun k _ => hi3 k
  -- the constant term is `F_t`-measurable
  have hc : μ[fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j) | ℱ t] =
      fun ω => ∑ i, ∑ j, P i j * (y ω i * y ω j) := by
    refine condExp_of_stronglyMeasurable hm ?_ hi1
    refine Measurable.stronglyMeasurable ?_
    exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((hym i).mul (hym j)).const_mul _
  -- the linear terms vanish
  have hlin : ∀ k, μ[fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k) | ℱ t] =ᵐ[μ] 0 := by
    intro k
    have hfac : (fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) =
        (fun ω => ∑ i, W i k * y ω i) * fun ω => ε (t + 1) ω k := by
      funext ω
      simp only [Pi.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsm : StronglyMeasurable[ℱ t] fun ω => ∑ i, W i k * y ω i :=
      (Finset.measurable_sum _ fun i _ => (hym i).const_mul _).stronglyMeasurable
    rw [hfac]
    refine (condExp_mul_of_stronglyMeasurable_left hsm (hfac ▸ hi2 k)
      ((hε k).integrable one_le_two)).trans ?_
    filter_upwards [hA.mean t k] with ω hω
    simp [hω]
  have hlin' : μ[fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k) | ℱ t] =ᵐ[μ] 0 := by
    have h1 := condExp_finsetSum (s := Finset.univ)
      (f := fun k ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) (fun k _ => hi2 k) (ℱ t)
    have h2 : ∀ᵐ ω ∂μ, ∀ k, (μ[fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k) | ℱ t]) ω = 0 :=
      ae_all_iff.2 fun k => hlin k
    have heq : (∑ k, fun ω => ∑ i, W i k * (y ω i * ε (t + 1) ω k)) =
        fun ω => ∑ k, ∑ i, W i k * (y ω i * ε (t + 1) ω k) := by
      funext ω; simp
    rw [heq] at h1
    filter_upwards [h1, h2] with ω h1ω h2ω
    rw [h1ω, Finset.sum_apply]
    simp [h2ω]
  -- the quadratic terms give the trace
  have hq : ∀ k, μ[fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) | ℱ t] =ᵐ[μ]
      fun _ => M k k := by
    intro k
    have h1 := condExp_finsetSum (s := Finset.univ)
      (f := fun l ω => M k l * (ε (t + 1) ω k * ε (t + 1) ω l))
      (fun l _ => (hee k l).const_mul _) (ℱ t)
    have heq : (∑ l, fun ω => M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) =
        fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) := by
      funext ω; simp
    rw [heq] at h1
    have h2 : ∀ l, μ[fun ω => M k l * (ε (t + 1) ω k * ε (t + 1) ω l) | ℱ t] =ᵐ[μ]
        fun _ => M k l * (if k = l then 1 else 0) := by
      intro l
      have := condExp_smul (μ := μ) (M k l) (fun ω => ε (t + 1) ω k * ε (t + 1) ω l) (ℱ t)
      refine this.trans ?_
      filter_upwards [hA.cov t k l] with ω hω
      simp only [Pi.smul_apply, smul_eq_mul, hω]
    have h3 := ae_all_iff.2 h2
    filter_upwards [h1, h3] with ω h1ω h3ω
    rw [h1ω, Finset.sum_apply]
    simp only [h3ω, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
  have hq' : μ[fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) | ℱ t] =ᵐ[μ]
      fun _ => trace (P * C * Cᵀ) := by
    have h1 := condExp_finsetSum (s := Finset.univ)
      (f := fun k ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) (fun k _ => hi3 k) (ℱ t)
    have heq : (∑ k, fun ω => ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l)) =
        fun ω => ∑ k, ∑ l, M k l * (ε (t + 1) ω k * ε (t + 1) ω l) := by
      funext ω; simp
    rw [heq] at h1
    have h3 := ae_all_iff.2 hq
    have htr : trace (Cᵀ * P * C) = trace (P * C * Cᵀ) := by
      rw [Matrix.mul_assoc, trace_mul_comm]
    filter_upwards [h1, h3] with ω h1ω h3ω
    rw [h1ω, Finset.sum_apply]
    simp only [h3ω]
    rw [← htr]
    rfl
  rw [hexp]
  refine (condExp_add (hi1.add hi2') hi3' _).trans ?_
  have h12 := condExp_add hi1 hi2' (ℱ t)
  filter_upwards [h12, hlin', hq'] with ω h12ω hlω hqω
  rw [Pi.add_apply, h12ω, Pi.add_apply, hc, hlω, hqω]
  simp only [Pi.zero_apply, add_zero]
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The state-space system -/

/-- The state transition equation (9.1): `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}`, `x₀` given. -/
def ls_state {E : Type*} [Fintype E] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (x₀ : X → ℝ) (u : ℕ → U → ℝ) (ε : ℕ → E → ℝ) : ℕ → X → ℝ
  | 0 => x₀
  | t + 1 => A *ᵥ ls_state A B C x₀ u ε t + B *ᵥ u t + C *ᵥ ε (t + 1)

/-- The deterministic transition `x_{t+1} = Ax_t + Bu_t`. -/
def ls_traj (A : Matrix X X ℝ) (B : Matrix X U ℝ) (x₀ : X → ℝ) (u : ℕ → U → ℝ) : ℕ → X → ℝ
  | 0 => x₀
  | t + 1 => A *ᵥ ls_traj A B x₀ u t + B *ᵥ u t

/-- The measurement equation (9.2): `y_t = Gx_t + Hu_{t−1} + Dε_t`, with `w t` standing for
`u_{t−1}` (so `w 0` is a given `u_{−1}`). -/
def ls_output {Y W E : Type*} [Fintype W] [Fintype E] (G : Matrix Y X ℝ) (H : Matrix Y W ℝ)
    (D : Matrix Y E ℝ) (x : ℕ → X → ℝ) (w : ℕ → W → ℝ) (ε : ℕ → E → ℝ) (t : ℕ) : Y → ℝ :=
  G *ᵥ x t + H *ᵥ w t + D *ᵥ ε t

/-! ### Definition 9.1.1: stabilizability -/

/-- **Definition 9.1.1** (Miao, p. 292): `(A, B)` is stabilizable if `A + BH` is stable for some
`H`. -/
def ls_Stabilizable (A : Matrix X X ℝ) (B : Matrix X U ℝ) : Prop :=
  ∃ H : Matrix U X ℝ, ls_Stable (A + B * H)

omit [DecidableEq X] in
/-- Miao, p. 292: under the control `u_t = Hx_t` the transition (9.1) becomes
`x_{t+1} = (A + BH)x_t + Cε_{t+1}`. -/
theorem definition_9_1_1_closed_loop {E : Type*} [Fintype E] (A : Matrix X X ℝ)
    (B : Matrix X U ℝ) (C : Matrix X E ℝ) (H : Matrix U X ℝ) {x : ℕ → X → ℝ}
    {u : ℕ → U → ℝ} {ε : ℕ → E → ℝ} (hx : ∀ t, x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε (t + 1))
    (hu : ∀ t, u t = H *ᵥ x t) (t : ℕ) :
    x (t + 1) = (A + B * H) *ᵥ x t + C *ᵥ ε (t + 1) := by
  rw [hx, hu, add_mulVec, mulVec_mulVec]

/-- Miao, pp. 292–293: the deterministic steady state `x̄ = 0` of the closed loop
`x_{t+1} = (A + BH)x_t` is (globally asymptotically) stable iff `A + BH` is stable. -/
theorem definition_9_1_1_steady_state (A : Matrix X X ℝ) (B : Matrix X U ℝ) (H : Matrix U X ℝ) :
    ls_Stable (A + B * H) ↔ ∀ (x : ℕ → X → ℝ), (∀ t, x (t + 1) = (A + B * H) *ᵥ x t) →
      Tendsto x atTop (𝓝 0) := by
  rw [ls_stable_iff_tendsto]
  constructor
  · intro h x hx
    have : ∀ t, x t = ((A + B * H) ^ t) *ᵥ x 0 := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [hx, ih, mulVec_mulVec, pow_succ']
    simpa only [← this] using h (x 0)
  · intro h v
    exact h (fun t => ((A + B * H) ^ t) *ᵥ v) fun t => by rw [mulVec_mulVec, pow_succ']

/-! ### Definition 9.1.2: controllability -/

/-- The controllability Gramian `∑_{j<r} AʲBB'A'ʲ`. -/
def ls_gram (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) : Matrix X X ℝ :=
  ∑ j ∈ Finset.range r, A ^ j * B * Bᵀ * Aᵀ ^ j

/-- **Definition 9.1.2** (Miao, p. 293): `(A, B)` is controllable if
`∑_{j=0}^{nₓ−1} AʲBB'A'ʲ > 0`. -/
def ls_Controllable (A : Matrix X X ℝ) (B : Matrix X U ℝ) : Prop :=
  (ls_gram A B (Fintype.card X)).PosDef

/-- The quadratic form of the Gramian: `v'W_rv = ∑_{j<r} |B'A'ʲv|²`. -/
theorem ls_gram_quad (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) (v : X → ℝ) :
    v ⬝ᵥ (ls_gram A B r *ᵥ v) =
      ∑ j ∈ Finset.range r, ((Bᵀ * Aᵀ ^ j) *ᵥ v) ⬝ᵥ ((Bᵀ * Aᵀ ^ j) *ᵥ v) := by
  classical
  simp only [ls_gram, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : A ^ j * B * Bᵀ * Aᵀ ^ j = (Bᵀ * Aᵀ ^ j)ᵀ * (1 : Matrix U U ℝ) * (Bᵀ * Aᵀ ^ j) := by
    rw [transpose_mul, transpose_pow, transpose_transpose, transpose_transpose, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [this, SS.LQProblem.dotProduct_transpose_mul_mul, one_mulVec]

theorem ls_gram_posSemidef (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) :
    (ls_gram A B r).PosSemidef := by
  classical
  induction r with
  | zero => simpa [ls_gram] using PosSemidef.zero
  | succ r ih =>
    rw [ls_gram, Finset.sum_range_succ]
    refine ih.add ?_
    have : A ^ r * B * Bᵀ * Aᵀ ^ r = (Bᵀ * Aᵀ ^ r)ᵀ * (1 : Matrix U U ℝ) * (Bᵀ * Aᵀ ^ r) := by
      rw [transpose_mul, transpose_pow, transpose_transpose, transpose_transpose, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [this]
    exact SS.LQProblem.posSemidef_transpose_mul_mul PosSemidef.one _

omit [DecidableEq X] in
theorem ls_dot_self_nonneg (v : X → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- The Gramian is positive definite iff every `v ≠ 0` has `B'A'ʲv ≠ 0` for some `j < r`. -/
theorem ls_gram_posDef_iff (A : Matrix X X ℝ) (B : Matrix X U ℝ) (r : ℕ) :
    (ls_gram A B r).PosDef ↔ ∀ v : X → ℝ, v ≠ 0 → ∃ j < r, (Bᵀ * Aᵀ ^ j) *ᵥ v ≠ 0 := by
  have hs := (SS.LQProblem.posSemidef_iff_real.1 (ls_gram_posSemidef A B r)).1
  rw [SS.LQProblem.posDef_iff_real]
  constructor
  · rintro ⟨-, h⟩ v hv
    by_contra hne
    push Not at hne
    have := h hv
    rw [ls_gram_quad, Finset.sum_eq_zero fun j hj => by
      rw [hne j (Finset.mem_range.1 hj), dotProduct_zero]] at this
    exact lt_irrefl _ this
  · intro h
    refine ⟨hs, fun v hv => ?_⟩
    obtain ⟨j, hj, hne⟩ := h v hv
    rw [ls_gram_quad]
    refine Finset.sum_pos' (fun i _ => ls_dot_self_nonneg _) ⟨j, Finset.mem_range.2 hj, ?_⟩
    exact lt_of_le_of_ne (ls_dot_self_nonneg _) (Ne.symm (mt dotProduct_self_eq_zero.1 hne))

omit [DecidableEq X] in
/-- The deterministic path: `x_r = Aʳx₀ + ∑_{j<r} AʲBu_{r−1−j}`. -/
theorem ls_traj_eq [DecidableEq X] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (x₀ : X → ℝ)
    (u : ℕ → U → ℝ) (r : ℕ) :
    ls_traj A B x₀ u r = (A ^ r) *ᵥ x₀ + ∑ j ∈ Finset.range r, (A ^ j) *ᵥ (B *ᵥ u (r - 1 - j)) :=
  backward_sol_eq A (g := fun t => B *ᵥ u t) (fun _ => rfl) r

/-- With a positive definite Gramian `W_r`, any `x₀` can be steered to any `x̄` in `r` steps (with
`u_j = B'A'^{r−1−j}W_r⁻¹(x̄ − Aʳx₀)`, and `u_t = 0` from `r` on). -/
theorem ls_reach_of_gram {A : Matrix X X ℝ} {B : Matrix X U ℝ} {r : ℕ}
    (h : (ls_gram A B r).PosDef) (x₀ xbar : X → ℝ) :
    ∃ u : ℕ → U → ℝ, (∀ t, r ≤ t → u t = 0) ∧ ls_traj A B x₀ u r = xbar := by
  set W := ls_gram A B r
  have hW : IsUnit W.det := (isUnit_iff_isUnit_det _).1 h.isUnit
  set w := W⁻¹ *ᵥ (xbar - (A ^ r) *ᵥ x₀)
  refine ⟨fun j => if j < r then (Bᵀ * Aᵀ ^ (r - 1 - j)) *ᵥ w else 0,
    fun t ht => by simp [not_lt.2 ht], ?_⟩
  rw [ls_traj_eq]
  have hsum : ∑ j ∈ Finset.range r, (A ^ j) *ᵥ (B *ᵥ
      (if r - 1 - j < r then (Bᵀ * Aᵀ ^ (r - 1 - (r - 1 - j))) *ᵥ w else 0)) = W *ᵥ w := by
    simp only [W, ls_gram, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    simp only [show r - 1 - j < r by omega, ↓reduceIte, show r - 1 - (r - 1 - j) = j by omega,
      mulVec_mulVec, Matrix.mul_assoc]
  rw [hsum, mulVec_mulVec, mul_nonsing_inv _ hW, one_mulVec, add_sub_cancel]

/-- **Definition 9.1.2** and the reachability characterisation (Miao, p. 293, Whittle (1982),
Theorem 4.3.1): `(A, B)` is controllable iff from every initial state every target can be reached
in `r` steps, for every `r ≥ nₓ`. -/
theorem definition_9_1_2_iff (A : Matrix X X ℝ) (B : Matrix X U ℝ) :
    ls_Controllable A B ↔ ∀ r, Fintype.card X ≤ r → ∀ x₀ xbar : X → ℝ,
      ∃ u : ℕ → U → ℝ, ls_traj A B x₀ u r = xbar := by
  constructor
  · intro h r hr x₀ xbar
    have hr' : (ls_gram A B r).PosDef := by
      rw [ls_Controllable, ls_gram_posDef_iff] at h
      rw [ls_gram_posDef_iff]
      intro v hv
      obtain ⟨j, hj, hne⟩ := h v hv
      exact ⟨j, by omega, hne⟩
    obtain ⟨u, -, hu⟩ := ls_reach_of_gram hr' x₀ xbar
    exact ⟨u, hu⟩
  · intro h
    rw [ls_Controllable, ls_gram_posDef_iff]
    intro v hv
    by_contra hne
    push Not at hne
    obtain ⟨u, hu⟩ := h _ le_rfl 0 v
    rw [ls_traj_eq, mulVec_zero, zero_add] at hu
    have hvv : v ⬝ᵥ v = 0 := by
      nth_rewrite 1 [← hu]
      rw [sum_dotProduct]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [mulVec_mulVec, SS.LQProblem.mulVec_dotProduct, transpose_mul, transpose_pow,
        hne j (Finset.mem_range.1 hj), dotProduct_zero]
    exact hv (dotProduct_self_eq_zero.1 hvv)

/-- Miao, p. 293, "for any `r > 0`" is false: the shift `A = [[0, 0], [1, 0]]`, `B = e₁` is
controllable, but not every target can be reached in one step. -/
theorem ls_controllable_not_reach_one :
    ls_Controllable (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) ∧
      ¬ ∀ x₀ xbar : Fin 2 → ℝ, ∃ u : ℕ → Fin 1 → ℝ,
        ls_traj (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) !![1; 0] x₀ u 1 = xbar := by
  refine ⟨?_, fun h => ?_⟩
  · have : ls_gram (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ)
        (Fintype.card (Fin 2)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ls_gram, Finset.sum_range_succ, vecMul, dotProduct, Matrix.mul_apply,
          Fin.sum_univ_two]
    rw [ls_Controllable, this]
    exact PosDef.one
  · obtain ⟨u, hu⟩ := h 0 (Pi.single 1 1)
    have := congrFun hu 1
    simp [ls_traj, dotProduct] at this

/-- Miao, p. 293: stabilizable does not imply controllable. If `A` is stable and `B = 0`, then
`(A, B)` is stabilizable but (for `nₓ ≥ 1`) not controllable. -/
theorem ls_stabilizable_not_controllable [Nonempty X] {A : Matrix X X ℝ} (hA : ls_Stable A) :
    ls_Stabilizable A (0 : Matrix X U ℝ) ∧ ¬ ls_Controllable A (0 : Matrix X U ℝ) := by
  refine ⟨⟨0, by simpa using hA⟩, fun h => ?_⟩
  obtain ⟨i⟩ := ‹Nonempty X›
  have h1 := (SS.LQProblem.posDef_iff_real.1 h).2 (x := Pi.single i 1) (by simp)
  simp [ls_gram] at h1

/-! ### Definition 9.1.3: observability -/

variable {Y : Type*} [Fintype Y]

/-- **Definition 9.1.3** (Miao, p. 293): `(A, G)` is observable if
`∑_{j=0}^{nₓ−1} A'ʲG'GAʲ > 0`, i.e. `(A', G')` is controllable. -/
def ls_Observable (A : Matrix X X ℝ) (G : Matrix Y X ℝ) : Prop :=
  (ls_gram Aᵀ Gᵀ (Fintype.card X)).PosDef

theorem ls_observable_gram (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (r : ℕ) :
    ls_gram Aᵀ Gᵀ r = ∑ j ∈ Finset.range r, Aᵀ ^ j * Gᵀ * G * A ^ j := by
  simp only [ls_gram, transpose_transpose]

/-- Two paths of (9.1) with the same inputs and shocks differ by `Aᵗ(x₀ − x₀')`. -/
theorem ls_state_sub {E : Type*} [Fintype E] (A : Matrix X X ℝ) (B : Matrix X U ℝ)
    (C : Matrix X E ℝ) (x₀ x₀' : X → ℝ) (u : ℕ → U → ℝ) (ε : ℕ → E → ℝ) (t : ℕ) :
    ls_state A B C x₀ u ε t - ls_state A B C x₀' u ε t = (A ^ t) *ᵥ (x₀ - x₀') := by
  induction t with
  | zero => simp [ls_state]
  | succ t ih =>
    simp only [ls_state]
    rw [pow_succ', ← mulVec_mulVec, ← ih, mulVec_sub]
    abel

/-- **Definition 9.1.3** and its characterisation (Miao, p. 293, Whittle (1982), Theorem 4.4.1):
`(A, G)` is observable iff, for every `r ≥ nₓ − 1`, `x₀` is determined by `y₀, …, y_r` of
(9.1)–(9.2) given the inputs `u` and shocks `ε`. -/
theorem definition_9_1_3_iff {E W : Type*} [Fintype E] [Fintype W] (A : Matrix X X ℝ)
    (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ) (H : Matrix Y W ℝ)
    (D : Matrix Y E ℝ) :
    ls_Observable A G ↔ ∀ r, Fintype.card X - 1 ≤ r → ∀ (u : ℕ → U → ℝ) (w : ℕ → W → ℝ)
      (ε : ℕ → E → ℝ) (x₀ x₀' : X → ℝ),
      (∀ t ≤ r, ls_output G H D (ls_state A B C x₀ u ε) w ε t =
        ls_output G H D (ls_state A B C x₀' u ε) w ε t) → x₀ = x₀' := by
  have hdiff : ∀ (u : ℕ → U → ℝ) (w : ℕ → W → ℝ) (ε : ℕ → E → ℝ) (x₀ x₀' : X → ℝ) t,
      ls_output G H D (ls_state A B C x₀ u ε) w ε t -
        ls_output G H D (ls_state A B C x₀' u ε) w ε t = (G * A ^ t) *ᵥ (x₀ - x₀') := by
    intro u w ε x₀ x₀' t
    simp only [ls_output]
    rw [← mulVec_mulVec, ← ls_state_sub A B C x₀ x₀' u ε t, mulVec_sub]
    abel
  have hgen : ∀ j, (Gᵀᵀ * Aᵀᵀ ^ j) = G * A ^ j := fun j => by simp only [transpose_transpose]
  rw [ls_Observable, ls_gram_posDef_iff]
  simp only [hgen]
  constructor
  · intro h r hr u w ε x₀ x₀' hy
    by_contra hne
    obtain ⟨j, hj, hj0⟩ := h (x₀ - x₀') (sub_ne_zero.2 hne)
    apply hj0
    rw [← hdiff u w ε, hy j (by omega), sub_self]
  · intro h v hv
    by_contra hne
    push Not at hne
    have hpos : 0 < Fintype.card X := by
      by_contra h0
      have : IsEmpty X := Fintype.card_eq_zero_iff.1 (by omega)
      exact hv (Subsingleton.elim _ _)
    have := h (Fintype.card X - 1) le_rfl 0 0 0 v 0 fun t ht => by
      rw [← sub_eq_zero, hdiff, sub_zero, hne t (by omega)]
    exact hv this

/-- Miao, p. 293, "for any `r > 0`" is false: with the shift `A` (`e₀ ↦ e₁ ↦ e₂ ↦ 0`) and
`G = e₂'`, `(A, G)` is observable, but `y₀, y₁` do not determine `x₀` (here `nₓ = 3`). -/
theorem ls_observable_not_two_outputs :
    ls_Observable (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
        (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ) ∧
      ∃ x₀ x₀' : Fin 3 → ℝ, x₀ ≠ x₀' ∧ ∀ t ≤ 1,
        ls_output (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (ls_state (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
            (0 : Matrix (Fin 3) (Fin 1) ℝ) (0 : Matrix (Fin 3) (Fin 1) ℝ) x₀ 0 0) 0 0 t =
        ls_output (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (0 : Matrix (Fin 1) (Fin 1) ℝ)
          (ls_state (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
            (0 : Matrix (Fin 3) (Fin 1) ℝ) (0 : Matrix (Fin 3) (Fin 1) ℝ) x₀' 0 0) 0 0 t := by
  refine ⟨?_, Pi.single 0 1, 0, fun h => by simpa using congrFun h 0, fun t ht => ?_⟩
  · have : ls_gram (!![0, 0, 0; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
        (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℝ)ᵀ (Fintype.card (Fin 3)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ls_gram, Finset.sum_range_succ, Matrix.mul_apply, Fin.sum_univ_three, pow_succ]
    rw [ls_Observable, this]
    exact PosDef.one
  · interval_cases t <;> funext i <;> fin_cases i <;>
      simp [ls_output, ls_state, dotProduct, Fin.sum_univ_three]

/-! ### Definition 9.1.4: detectability -/

/-- **Definition 9.1.4** (Miao, p. 294): `(A, G)` is detectable if `A − JG` is stable for some
`J`. -/
def ls_Detectable (A : Matrix X X ℝ) (G : Matrix Y X ℝ) : Prop :=
  ∃ J : Matrix X Y ℝ, ls_Stable (A - J * G)

omit [DecidableEq X] in
/-- (9.3) and the error equation (Miao, p. 294), corrected: if `x̂_{t+1} = Ax̂_t + Bu_t + AKa_t`
with `a_t = G(x_t − x̂_t) + Dε_t`, then `Δ_t = x_t − x̂_t` satisfies
`Δ_{t+1} = (A − AKG)Δ_t + Cε_{t+1} − AKDε_t`. -/
theorem eq_9_3_error {E : Type*} [Fintype E] (A : Matrix X X ℝ) (B : Matrix X U ℝ)
    (C : Matrix X E ℝ) (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (K : Matrix X Y ℝ)
    {x xh : ℕ → X → ℝ} {u : ℕ → U → ℝ} {ε : ℕ → E → ℝ}
    (hx : ∀ t, x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε (t + 1))
    (hxh : ∀ t, xh (t + 1) = A *ᵥ xh t + B *ᵥ u t + (A * K) *ᵥ (G *ᵥ (x t - xh t) + D *ᵥ ε t))
    (t : ℕ) :
    x (t + 1) - xh (t + 1) =
      (A - A * K * G) *ᵥ (x t - xh t) + C *ᵥ ε (t + 1) - (A * K * D) *ᵥ ε t := by
  rw [hx, hxh]
  simp only [sub_mulVec, mulVec_add, mulVec_sub, mulVec_mulVec]
  abel

/-- Miao, p. 294: if `A − AKG` is stable, the noise-free estimation error `Δ_t` tends to zero. -/
theorem eq_9_3_tendsto (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (K : Matrix X Y ℝ)
    (hK : ls_Stable (A - A * K * G)) {Δ : ℕ → X → ℝ}
    (hΔ : ∀ t, Δ (t + 1) = (A - A * K * G) *ᵥ Δ t) : Tendsto Δ atTop (𝓝 0) := by
  have : ∀ t, Δ t = ((A - A * K * G) ^ t) *ᵥ Δ 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hΔ, ih, mulVec_mulVec, pow_succ']
  simpa only [← this] using (ls_stable_iff_tendsto _).1 hK (Δ 0)

/-- The printed error equation `Δ_{t+1} = (A − AKG)Δ_{t−1} + Cε_{t+1} + AKDε_t` is false: with
`A = 2`, all other matrices zero, `x₀ = 1`, `x̂₀ = 0`, (9.1) and (9.3) give `Δ_t = 2ᵗ`, so
`Δ₂ = 4 ≠ 2 = (A − AKG)Δ₀`. -/
theorem eq_9_3_misprint :
    ∃ (x xh : ℕ → Fin 1 → ℝ), (∀ t, x (t + 1) = (2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x t) ∧
      (∀ t, xh (t + 1) = (2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ xh t) ∧
      x 2 - xh 2 ≠ (2 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (x 0 - xh 0) := by
  refine ⟨fun t _ => 2 ^ t, fun _ _ => 0, fun t => ?_, fun t => ?_, ?_⟩
  · funext i
    fin_cases i
    simp [mulVec, dotProduct, pow_succ, Matrix.ofNat_apply, mul_comm]
  · funext i
    simp [mulVec, dotProduct]
  · intro h
    have := congrFun h 0
    norm_num [mulVec, dotProduct, Matrix.ofNat_apply] at this

/-- Miao, p. 294: for invertible `A`, detectability gives an updating rule (9.3) whose error
matrix `A − AKG` is stable (`K = A⁻¹J`). -/
theorem definition_9_1_4_rule {A : Matrix X X ℝ} {G : Matrix Y X ℝ} (hA : IsUnit A.det)
    (hd : ls_Detectable A G) : ∃ K : Matrix X Y ℝ, ls_Stable (A - A * K * G) := by
  obtain ⟨J, hJ⟩ := hd
  refine ⟨A⁻¹ * J, ?_⟩
  rwa [mul_nonsing_inv_cancel_left _ _ hA]

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence of the Riccati iteration (the undiscounted core of Propositions 9.3.1–9.3.2)

Miao, §9.3, pp. 298–301, for an undiscounted LQ problem `(Q, R, A, B)` in the
Sargent–Stachurski form `SS.LQProblem` (Riccati map `R(P)`, gain `F(P) = −G(P)⁻¹B'PA`, closed
loop `A + BF`). The discounted problem of the book is the case `(√βA, √βB)`
(`LSInfiniteHorizon`). This module proves the existence of the Riccati fixed point that
`SS.LQProblem.optimality` takes as a hypothesis.

* `ls_riccati_mono`: the Riccati map is monotone in the Loewner order (it is the minimum of the
  monotone maps `T_F`); `ls_iter_zero_mono`: `R^s(0)` increases in `s`.
* `ls_finite_lower`: every control sequence costs at least `x₀'R^s(P₀)x₀` over `s` periods with
  terminal cost `P₀` (the finite-horizon optimality of the Riccati iterates).
* `ls_iter_le_PF` (stabilizable case: the cost of a stable feedback bounds `R^s(0)`) and
  `ls_iter_bdd_of_controllable` (controllable case: steer to zero in `nₓ` steps).
* `ls_iter_converges`: bounded monotone iterates converge to a positive semidefinite limit;
  `ls_tendsto_riccati`: `R` is continuous on the positive semidefinite cone; the limit is a fixed
  point.
* `ls_stable_of_fixed`: along the closed loop `x'Px − x₊'Px₊ = x'(Q + F'RF)x`, so the costs are
  summable and tend to zero (9.14); under a detection condition `ls_Detects` this forces
  `xₜ → 0`, i.e. `A + BF(P)` is stable. The detection condition holds if `Q > 0`
  (`ls_detects_of_posDef`), if `Q = L'L` with `(A, L)` detectable (`ls_detects_of_detectable`)
  or observable (`ls_detects_of_observable`).
* `ls_riccati_main`: existence and uniqueness of the positive semidefinite fixed point,
  convergence `R^s(P₀) → P` from every positive semidefinite `P₀`, stability of `F(P)`, and
  `P = P_{F(P)}`.
-/

open Filter Topology Matrix

open scoped MatrixOrder

namespace Miao.LinearQuadratic

variable {K U : Type*} [Fintype K] [DecidableEq K] [Fintype U] [DecidableEq U]
  (L : SS.LQProblem K U)

omit [DecidableEq K] in
/-- `R(P) ≤ T_F(P)` for every `F`. -/
theorem ls_riccati_le_TF {P : Matrix K K ℝ} (hP : P.PosSemidef) (F : Matrix U K ℝ) :
    L.riccati P ≤ L.TF F P := by
  rw [L.riccati_eq_TF hP]
  exact (L.gain_iff_TF_le hP _).1 rfl F

omit [Fintype K] [DecidableEq K] in
theorem ls_posSemidef_of_le {P P' : Matrix K K ℝ} (hP : P.PosSemidef) (h : P ≤ P') :
    P'.PosSemidef := by
  have := hP.add (Matrix.le_iff.1 h)
  rwa [add_sub_cancel] at this

omit [DecidableEq K] in
/-- `P ≤ P'` gives `v'Pv ≤ v'P'v`. -/
theorem ls_quad_le {P P' : Matrix K K ℝ} (h : P ≤ P') (v : K → ℝ) :
    v ⬝ᵥ (P *ᵥ v) ≤ v ⬝ᵥ (P' *ᵥ v) := by
  have := (SS.LQProblem.posSemidef_iff_real.1 (Matrix.le_iff.1 h)).2 v
  rw [sub_mulVec, dotProduct_sub, sub_nonneg] at this
  exact this

omit [DecidableEq K] in
/-- The Riccati map is monotone in the Loewner order. -/
theorem ls_riccati_mono {P P' : Matrix K K ℝ} (hP : P.PosSemidef) (h : P ≤ P') :
    L.riccati P ≤ L.riccati P' := by
  have hP' := ls_posSemidef_of_le hP h
  calc L.riccati P ≤ L.TF (L.gain P') P := ls_riccati_le_TF L hP _
    _ ≤ L.TF (L.gain P') P' := L.TF_mono _ h
    _ = L.riccati P' := (L.riccati_eq_TF hP').symm

omit [DecidableEq K] in
theorem ls_iter_psd {P : Matrix K K ℝ} (hP : P.PosSemidef) (s : ℕ) :
    (L.riccati^[s] P).PosSemidef := by
  induction s with
  | zero => exact hP
  | succ s ih => rw [Function.iterate_succ_apply']; exact L.riccati_posSemidef ih

omit [DecidableEq K] in
theorem ls_iter_mono_le {P P' : Matrix K K ℝ} (hP : P.PosSemidef) (h : P ≤ P') (s : ℕ) :
    L.riccati^[s] P ≤ L.riccati^[s] P' := by
  induction s with
  | zero => exact h
  | succ s ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ls_riccati_mono L (ls_iter_psd L hP s) ih

omit [Fintype K] [DecidableEq K] in
theorem ls_zero_le_psd {P : Matrix K K ℝ} (hP : P.PosSemidef) : 0 ≤ P := by
  rw [Matrix.le_iff, sub_zero]
  exact hP

omit [DecidableEq K] in
/-- `R^s(0) ≤ R^{s+1}(0)`: the Riccati iterates from `0` increase. -/
theorem ls_iter_zero_mono (s : ℕ) : L.riccati^[s] 0 ≤ L.riccati^[s + 1] 0 := by
  rw [Function.iterate_succ_apply]
  exact ls_iter_mono_le L PosSemidef.zero (ls_zero_le_psd (L.riccati_posSemidef PosSemidef.zero)) s

omit [DecidableEq K] in
theorem ls_iter_zero_mono_add (s m : ℕ) : L.riccati^[s] 0 ≤ L.riccati^[s + m] 0 := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans (ls_iter_zero_mono L (s + m))

omit [DecidableEq K] in
/-- Finite-horizon optimality of the Riccati iterates: for every control sequence with
`x_{t+1} = Ax_t + Bu_t`, `x₀'R^s(P₀)x₀ ≤ ∑_{t<s}(x_t'Qx_t + u_t'Ru_t) + x_s'P₀x_s`. -/
theorem ls_finite_lower {P₀ : Matrix K K ℝ} (hP₀ : P₀.PosSemidef) (s : ℕ) :
    ∀ (x : ℕ → K → ℝ) (u : ℕ → U → ℝ), (∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) →
      x 0 ⬝ᵥ (L.riccati^[s] P₀ *ᵥ x 0) ≤
        ∑ t ∈ Finset.range s, (x t ⬝ᵥ (L.Q *ᵥ x t) + u t ⬝ᵥ (L.R *ᵥ u t)) +
          x s ⬝ᵥ (P₀ *ᵥ x s) := by
  induction s with
  | zero => intro x u _; simp
  | succ s ih =>
    intro x u hx
    have hP := ls_iter_psd L hP₀ s
    have h1 : x 0 ⬝ᵥ (L.riccati^[s + 1] P₀ *ᵥ x 0) ≤ L.cost (L.riccati^[s] P₀) (x 0) (u 0) := by
      rw [Function.iterate_succ_apply', L.riccati_eq_TF hP, L.dotProduct_TF]
      exact (L.gain_isMinimizer hP (x 0)).1 _
    have h2 := ih (fun t => x (t + 1)) (fun t => u (t + 1)) fun t => hx (t + 1)
    have h3 : L.cost (L.riccati^[s] P₀) (x 0) (u 0) = x 0 ⬝ᵥ (L.Q *ᵥ x 0) +
        u 0 ⬝ᵥ (L.R *ᵥ u 0) + x 1 ⬝ᵥ (L.riccati^[s] P₀ *ᵥ x 1) := by
      rw [SS.LQProblem.cost, hx 0]
    rw [Finset.sum_range_succ']
    linarith

/-- The stabilizable case (Miao, p. 299): a stable feedback `F` bounds the iterates,
`R^s(0) ≤ P_F`. -/
theorem ls_iter_le_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (s : ℕ) :
    L.riccati^[s] 0 ≤ L.PF F := by
  induction s with
  | zero => exact ls_zero_le_psd hF.PF_posSemidef
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    calc L.riccati (L.riccati^[s] 0) ≤ L.TF F (L.riccati^[s] 0) :=
          ls_riccati_le_TF L (ls_iter_psd L PosSemidef.zero s) F
      _ ≤ L.TF F (L.PF F) := L.TF_mono F ih
      _ = L.PF F := hF.TF_PF

/-- The controllable case (Miao, p. 299): steering `x₀` to zero in `nₓ` steps and holding it
there bounds `x₀'R^s(0)x₀` uniformly in `s`. -/
theorem ls_iter_bdd_of_controllable (hc : ls_Controllable L.A L.B) (x₀ : K → ℝ) :
    ∃ c, ∀ s, x₀ ⬝ᵥ (L.riccati^[s] 0 *ᵥ x₀) ≤ c := by
  obtain ⟨u, hu0, hun⟩ := ls_reach_of_gram hc x₀ 0
  set n := Fintype.card K
  set x := ls_traj L.A L.B x₀ u
  have hx : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t := fun t => rfl
  have hxz : ∀ m, x (n + m) = 0 := by
    intro m
    induction m with
    | zero => exact hun
    | succ m ih => rw [← add_assoc, hx, ih, hu0 _ (by omega)]; simp
  refine ⟨∑ t ∈ Finset.range n, (x t ⬝ᵥ (L.Q *ᵥ x t) + u t ⬝ᵥ (L.R *ᵥ u t)), fun s => ?_⟩
  have h1 := ls_quad_le (ls_iter_zero_mono_add L s n) x₀
  have h2 := ls_finite_lower L PosSemidef.zero (s + n) x u hx
  rw [show s + n = n + s by ring, Finset.sum_range_add, hxz s] at h2
  have hz : ∑ t ∈ Finset.range s, (x (n + t) ⬝ᵥ (L.Q *ᵥ x (n + t)) +
      u (n + t) ⬝ᵥ (L.R *ᵥ u (n + t))) = 0 :=
    Finset.sum_eq_zero fun t _ => by rw [hxz t, hu0 _ (by omega)]; simp
  rw [hz] at h2
  have h0 : x 0 = x₀ := rfl
  rw [h0, show n + s = s + n by ring] at h2
  simp only [add_zero, zero_mulVec, dotProduct_zero] at h2
  exact h1.trans h2

omit [DecidableEq K] in
/-- Quadratic forms are continuous in the matrix. -/
theorem ls_tendsto_quad {M : ℕ → Matrix K K ℝ} {M₀ : Matrix K K ℝ}
    (h : Tendsto M atTop (𝓝 M₀)) (v : K → ℝ) :
    Tendsto (fun s => v ⬝ᵥ (M s *ᵥ v)) atTop (𝓝 (v ⬝ᵥ (M₀ *ᵥ v))) :=
  ((Continuous.dotProduct continuous_const
    (Continuous.matrix_mulVec continuous_id continuous_const)).tendsto M₀).comp h

omit [DecidableEq K] in
/-- Bounded Riccati iterates from `0` converge to a positive semidefinite limit. -/
theorem ls_iter_converges (hbdd : ∀ x₀ : K → ℝ, ∃ c, ∀ s, x₀ ⬝ᵥ (L.riccati^[s] 0 *ᵥ x₀) ≤ c) :
    ∃ P : Matrix K K ℝ, P.PosSemidef ∧ Tendsto (fun s => L.riccati^[s] 0) atTop (𝓝 P) := by
  have hsym : ∀ s, (L.riccati^[s] 0)ᵀ = L.riccati^[s] 0 := fun s =>
    (SS.LQProblem.posSemidef_iff_real.1 (ls_iter_psd L PosSemidef.zero s)).1
  have hq : ∀ v : K → ℝ, ∃ c, Tendsto (fun s => v ⬝ᵥ (L.riccati^[s] 0 *ᵥ v)) atTop (𝓝 c) := by
    intro v
    obtain ⟨c, hc⟩ := hbdd v
    have hmono : Monotone fun s => v ⬝ᵥ (L.riccati^[s] 0 *ᵥ v) :=
      monotone_nat_of_le_succ fun s => ls_quad_le (ls_iter_zero_mono L s) v
    exact ⟨_, tendsto_atTop_ciSup hmono ⟨c, by rintro _ ⟨s, rfl⟩; exact hc s⟩⟩
  obtain ⟨P, -, hP⟩ := ls_exists_tendsto_of_quad hsym hq
  exact ⟨P, posSemidef_is_closed.mem_of_tendsto hP
    (Eventually.of_forall fun s => ls_iter_psd L PosSemidef.zero s), hP⟩

omit [DecidableEq K] in
/-- Products of convergent matrix sequences converge. -/
theorem ls_tendsto_mul {m n p : Type*} [Fintype n] {f : ℕ → Matrix m n ℝ} {g : ℕ → Matrix n p ℝ}
    {a : Matrix m n ℝ} {b : Matrix n p ℝ} (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 b)) : Tendsto (fun s => f s * g s) atTop (𝓝 (a * b)) :=
  ((Continuous.matrix_mul continuous_fst continuous_snd).tendsto (a, b)).comp (hf.prodMk_nhds hg)

omit [DecidableEq K] in
/-- Inversion is continuous at an invertible matrix. -/
theorem ls_tendsto_inv {f : ℕ → Matrix U U ℝ} {a : Matrix U U ℝ} (ha : IsUnit a.det)
    (hf : Tendsto f atTop (𝓝 a)) : Tendsto (fun s => (f s)⁻¹) atTop (𝓝 a⁻¹) := by
  have h : ContinuousAt Ring.inverse a.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ ha.ne_zero
  exact (continuousAt_matrix_inv a h).tendsto.comp hf

omit [DecidableEq K] in
/-- The gain `F(P)` is continuous on the positive semidefinite cone. -/
theorem ls_tendsto_gain {Pn : ℕ → Matrix K K ℝ} {P : Matrix K K ℝ} (hP : P.PosSemidef)
    (h : Tendsto Pn atTop (𝓝 P)) : Tendsto (fun n => L.gain (Pn n)) atTop (𝓝 (L.gain P)) := by
  have hG : Tendsto (fun n => L.gainDen (Pn n)) atTop (𝓝 (L.gainDen P)) :=
    (ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).add
      tendsto_const_nhds
  have hGi := ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.gainDen_posDef hP).isUnit) hG
  exact (ls_tendsto_mul (ls_tendsto_mul (ls_tendsto_mul hGi tendsto_const_nhds) h)
    tendsto_const_nhds).neg

omit [DecidableEq K] in
/-- The Riccati map is continuous on the positive semidefinite cone. -/
theorem ls_tendsto_riccati {Pn : ℕ → Matrix K K ℝ} {P : Matrix K K ℝ} (hP : P.PosSemidef)
    (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.riccati (Pn n)) atTop (𝓝 (L.riccati P)) := by
  have hG : Tendsto (fun n => L.gainDen (Pn n)) atTop (𝓝 (L.gainDen P)) :=
    (ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).add
      tendsto_const_nhds
  have hGi := ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.gainDen_posDef hP).isUnit) hG
  have hAPA : Tendsto (fun n => L.Aᵀ * Pn n * L.A) atTop (𝓝 (L.Aᵀ * P * L.A)) :=
    ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds
  have hmid : Tendsto (fun n => L.Aᵀ * Pn n * L.B * (L.gainDen (Pn n))⁻¹ * L.Bᵀ * Pn n * L.A)
      atTop (𝓝 (L.Aᵀ * P * L.B * (L.gainDen P)⁻¹ * L.Bᵀ * P * L.A)) :=
    ls_tendsto_mul (ls_tendsto_mul (ls_tendsto_mul (ls_tendsto_mul
      (ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds) hGi)
      tendsto_const_nhds) h) tendsto_const_nhds
  exact (hAPA.sub hmid).add tendsto_const_nhds

omit [DecidableEq K] in
/-- A positive semidefinite limit of the iterates `R^s(P₀)` is a fixed point of `R`. -/
theorem ls_fixed_of_tendsto {P₀ P : Matrix K K ℝ} (hP : P.PosSemidef)
    (h : Tendsto (fun s => L.riccati^[s] P₀) atTop (𝓝 P)) : L.riccati P = P := by
  have h1 := ls_tendsto_riccati L hP h
  have h2 : Tendsto (fun s => L.riccati^[s + 1] P₀) atTop (𝓝 P) :=
    (tendsto_add_atTop_iff_nat 1).2 h
  simp only [Function.iterate_succ_apply'] at h2
  exact tendsto_nhds_unique h1 h2

/-- The detection condition: along the closed loop `x_{t+1} = (A + BF)x_t`, `x_t'Qx_t → 0` and
`Fx_t → 0` force `x_t → 0`. -/
def ls_Detects (F : Matrix U K ℝ) : Prop :=
  ∀ x : ℕ → K → ℝ, (∀ t, x (t + 1) = L.closedLoop F *ᵥ x t) →
    Tendsto (fun t => x t ⬝ᵥ (L.Q *ᵥ x t)) atTop (𝓝 0) →
    Tendsto (fun t => F *ᵥ x t) atTop (𝓝 0) → Tendsto x atTop (𝓝 0)

omit [DecidableEq K] in
/-- (9.14) (Miao, p. 300): at a fixed point `P = R(P)`, along the closed loop
`x_{t+1} = (A + BF(P))x_t` the costs `x_t'(Q + F'RF)x_t` are summable (with sum at most
`x₀'Px₀`), hence `x_t'Qx_t → 0` and `F(P)x_t → 0`. -/
theorem ls_cost_tendsto_zero {P : Matrix K K ℝ} (hP : P.PosSemidef) (hfix : L.riccati P = P)
    {x : ℕ → K → ℝ} (hx : ∀ t, x (t + 1) = L.closedLoop (L.gain P) *ᵥ x t) :
    (∀ n, ∑ t ∈ Finset.range n, x t ⬝ᵥ (L.costMat (L.gain P) *ᵥ x t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - x n ⬝ᵥ (P *ᵥ x n)) ∧
    Tendsto (fun t => x t ⬝ᵥ (L.Q *ᵥ x t)) atTop (𝓝 0) ∧
    Tendsto (fun t => L.gain P *ᵥ x t) atTop (𝓝 0) := by
  set F := L.gain P
  have hTF : P = L.costMat F + (L.closedLoop F)ᵀ * P * L.closedLoop F := by
    conv_lhs => rw [← hfix, L.riccati_eq_TF hP, SS.LQProblem.TF_eq]
  have hstep : ∀ t, x t ⬝ᵥ (P *ᵥ x t) =
      x t ⬝ᵥ (L.costMat F *ᵥ x t) + x (t + 1) ⬝ᵥ (P *ᵥ x (t + 1)) := by
    intro t
    conv_lhs => rw [hTF]
    rw [add_mulVec, dotProduct_add, SS.LQProblem.dotProduct_transpose_mul_mul, ← hx t]
  have hsum : ∀ n, ∑ t ∈ Finset.range n, x t ⬝ᵥ (L.costMat F *ᵥ x t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - x n ⬝ᵥ (P *ᵥ x n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, hstep n]; ring
  have hPq := (SS.LQProblem.posSemidef_iff_real.1 hP).2
  have hRq := (SS.LQProblem.posSemidef_iff_real.1 L.R_pd.posSemidef).2
  have hQq := (SS.LQProblem.posSemidef_iff_real.1 L.Q_psd).2
  have hsplit : ∀ t, x t ⬝ᵥ (L.costMat F *ᵥ x t) =
      (F *ᵥ x t) ⬝ᵥ (L.R *ᵥ (F *ᵥ x t)) + x t ⬝ᵥ (L.Q *ᵥ x t) := by
    intro t
    rw [SS.LQProblem.costMat, add_mulVec, dotProduct_add,
      SS.LQProblem.dotProduct_transpose_mul_mul]
  have hnn : ∀ t, 0 ≤ x t ⬝ᵥ (L.costMat F *ᵥ x t) := fun t => by
    rw [hsplit]; exact add_nonneg (hRq _) (hQq _)
  have hs : Summable fun t => x t ⬝ᵥ (L.costMat F *ᵥ x t) :=
    summable_of_sum_range_le hnn fun n => by rw [hsum n]; linarith [hPq (x n)]
  have h0 := hs.tendsto_atTop_zero
  refine ⟨hsum, ?_, ?_⟩
  · refine squeeze_zero (fun t => hQq _) (fun t => ?_) h0
    rw [hsplit]
    linarith [hRq (F *ᵥ x t)]
  · refine ls_tendsto_zero_of_quad_posDef L.R_pd ?_
    refine squeeze_zero (fun t => hRq _) (fun t => ?_) h0
    rw [hsplit]
    linarith [hQq (x t)]

omit [DecidableEq K] in
/-- Miao, p. 300: under the detection condition, the closed loop of a fixed point is stable. -/
theorem ls_stable_of_fixed [Nonempty K] {P : Matrix K K ℝ} (hP : P.PosSemidef)
    (hfix : L.riccati P = P) (hD : ls_Detects L (L.gain P)) : L.IsStable (L.gain P) := by
  classical
  rw [SS.LQProblem.IsStable, ← ls_stable_iff_specRad, ls_stable_iff_tendsto]
  intro v
  have hx : ∀ t, (L.closedLoop (L.gain P) ^ (t + 1)) *ᵥ v =
      L.closedLoop (L.gain P) *ᵥ ((L.closedLoop (L.gain P) ^ t) *ᵥ v) := fun t => by
    rw [pow_succ', mulVec_mulVec]
  obtain ⟨-, hQ, hF⟩ := ls_cost_tendsto_zero L hP hfix
    (x := fun t => (L.closedLoop (L.gain P) ^ t) *ᵥ v) hx
  exact hD _ hx hQ hF

omit [DecidableEq K] [DecidableEq U] in
/-- The detection condition when `Q > 0` (Proposition 9.3.1). -/
theorem ls_detects_of_posDef (hQ : L.Q.PosDef) (F : Matrix U K ℝ) : ls_Detects L F :=
  fun _ _ hq _ => ls_tendsto_zero_of_quad_posDef hQ hq

omit [DecidableEq K] in
theorem ls_tendsto_mulVec_zero {m n : Type*} [Fintype n] (M : Matrix m n ℝ) {z : ℕ → n → ℝ}
    (hz : Tendsto z atTop (𝓝 0)) : Tendsto (fun t => M *ᵥ z t) atTop (𝓝 0) := by
  have := ((Continuous.matrix_mulVec (continuous_const (y := M)) continuous_id).tendsto
    (0 : n → ℝ)).comp hz
  simpa [Function.comp_def] using this

omit [DecidableEq K] [DecidableEq U] in
/-- With `Q = L'L`, `x_t'Qx_t → 0` gives `Lx_t → 0`. -/
theorem ls_tendsto_L {Y : Type*} [Fintype Y] {Lm : Matrix Y K ℝ} (hQ : L.Q = Lmᵀ * Lm)
    {x : ℕ → K → ℝ} (hq : Tendsto (fun t => x t ⬝ᵥ (L.Q *ᵥ x t)) atTop (𝓝 0)) :
    Tendsto (fun t => Lm *ᵥ x t) atTop (𝓝 0) := by
  classical
  refine ls_tendsto_zero_of_quad_posDef PosDef.one ?_
  refine hq.congr fun t => ?_
  rw [hQ, one_mulVec, ← mulVec_mulVec, ← SS.LQProblem.mulVec_dotProduct]

omit [DecidableEq U] in
/-- The detection condition when `Q = L'L` with `(A, L)` detectable (Proposition 9.3.2): with
`A − HL` stable, `x_{t+1} = (A − HL)x_t + HLx_t + BFx_t` is a stable system with vanishing
input. -/
theorem ls_detects_of_detectable {Y : Type*} [Fintype Y] {Lm : Matrix Y K ℝ}
    (hQ : L.Q = Lmᵀ * Lm) (hd : ls_Detectable L.A Lm) (F : Matrix U K ℝ) : ls_Detects L F := by
  obtain ⟨H, hH⟩ := hd
  intro x hx hq hF
  have hL := ls_tendsto_L L hQ hq
  refine ls_tendsto_zero_of_stable_input hH (w := fun t => H *ᵥ (Lm *ᵥ x t) + L.B *ᵥ (F *ᵥ x t))
    (fun t => ?_) ?_
  · rw [hx, SS.LQProblem.closedLoop, sub_mulVec, add_mulVec, mulVec_mulVec, mulVec_mulVec]
    abel
  · simpa using (ls_tendsto_mulVec_zero H hL).add (ls_tendsto_mulVec_zero L.B hF)

omit [DecidableEq U] in
/-- The detection condition when `Q = L'L` with `(A, L)` observable (Proposition 9.3.2): for each
`j`, `x_{t+j} − Aʲx_t → 0`, hence `LAʲx_t → 0` and `Wx_t → 0` for the positive definite
observability Gramian `W`. -/
theorem ls_detects_of_observable {Y : Type*} [Fintype Y] {Lm : Matrix Y K ℝ}
    (hQ : L.Q = Lmᵀ * Lm) (ho : ls_Observable L.A Lm) (F : Matrix U K ℝ) : ls_Detects L F := by
  intro x hx hq hF
  have hL := ls_tendsto_L L hQ hq
  have hshift : ∀ j, Tendsto (fun t => x (t + j) - (L.A ^ j) *ᵥ x t) atTop (𝓝 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : ∀ t, x (t + (j + 1)) - (L.A ^ (j + 1)) *ᵥ x t =
          L.A *ᵥ (x (t + j) - (L.A ^ j) *ᵥ x t) + L.B *ᵥ (F *ᵥ x (t + j)) := by
        intro t
        rw [← add_assoc, hx, SS.LQProblem.closedLoop, add_mulVec, pow_succ', ← mulVec_mulVec,
          mulVec_sub, ← mulVec_mulVec]
        abel
      have hFj : Tendsto (fun t => F *ᵥ x (t + j)) atTop (𝓝 0) :=
        hF.comp (tendsto_add_atTop_nat j)
      simpa [e] using (ls_tendsto_mulVec_zero L.A ih).add (ls_tendsto_mulVec_zero L.B hFj)
  have hLj : ∀ j, Tendsto (fun t => (Lm * L.A ^ j) *ᵥ x t) atTop (𝓝 0) := by
    intro j
    have h1 : Tendsto (fun t => Lm *ᵥ x (t + j)) atTop (𝓝 0) := hL.comp (tendsto_add_atTop_nat j)
    have h2 := ls_tendsto_mulVec_zero Lm (hshift j)
    have := h1.sub h2
    simp only [sub_zero] at this
    refine this.congr fun t => ?_
    rw [mulVec_sub, ← mulVec_mulVec]
    abel
  set W := ls_gram L.Aᵀ Lmᵀ (Fintype.card K)
  have hW : Tendsto (fun t => W *ᵥ x t) atTop (𝓝 0) := by
    have e : ∀ t, W *ᵥ x t = ∑ j ∈ Finset.range (Fintype.card K),
        (L.Aᵀ ^ j * Lmᵀ) *ᵥ ((Lm * L.A ^ j) *ᵥ x t) := by
      intro t
      simp only [W, ls_gram, Matrix.sum_mulVec, transpose_transpose, mulVec_mulVec,
        Matrix.mul_assoc]
    have := tendsto_finsetSum (Finset.range (Fintype.card K))
      fun j _ => ls_tendsto_mulVec_zero (L.Aᵀ ^ j * Lmᵀ) (hLj j)
    simp only [Finset.sum_const_zero] at this
    exact this.congr fun t => (e t).symm
  have hu : IsUnit W.det := (isUnit_iff_isUnit_det _).1 ho.isUnit
  have := ls_tendsto_mulVec_zero W⁻¹ hW
  refine this.congr fun t => ?_
  rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- The Riccati iterates converge to the positive semidefinite fixed point (Propositions
9.3.1–9.3.2, undiscounted form). Suppose `(A, B)` is stabilizable (some stable `F`) or
controllable, and the detection condition holds for every feedback. Then the Riccati equation
`P = R(P)` has a positive semidefinite solution `P`, unique among positive semidefinite matrices;
`R^s(P₀) → P` from every positive semidefinite `P₀`; `F(P)` is stable; and `P = P_{F(P)}`. -/
theorem ls_riccati_main [Nonempty K] (hstab : (∃ F, L.IsStable F) ∨ ls_Controllable L.A L.B)
    (hD : ∀ F, ls_Detects L F) :
    ∃ P : Matrix K K ℝ, P.PosSemidef ∧ L.riccati P = P ∧ L.IsStable (L.gain P) ∧
      P = L.PF (L.gain P) ∧
      (∀ P₀ : Matrix K K ℝ, P₀.PosSemidef → Tendsto (fun s => L.riccati^[s] P₀) atTop (𝓝 P)) ∧
      ∀ P' : Matrix K K ℝ, P'.PosSemidef → L.riccati P' = P' → P' = P := by
  have hbdd : ∀ x₀ : K → ℝ, ∃ c, ∀ s, x₀ ⬝ᵥ (L.riccati^[s] 0 *ᵥ x₀) ≤ c := by
    rcases hstab with ⟨F, hF⟩ | hc
    · exact fun x₀ => ⟨_, fun s => ls_quad_le (ls_iter_le_PF L hF s) x₀⟩
    · exact ls_iter_bdd_of_controllable L hc
  obtain ⟨P, hP, hlim⟩ := ls_iter_converges L hbdd
  have hfix := ls_fixed_of_tendsto L hP hlim
  have hst := ls_stable_of_fixed L hP hfix (hD _)
  have hTF : L.TF (L.gain P) P = P := by rw [← L.riccati_eq_TF hP, hfix]
  have hPF : P = L.PF (L.gain P) := hst.eq_PF hTF
  have hconv : ∀ P₀ : Matrix K K ℝ, P₀.PosSemidef →
      Tendsto (fun s => L.riccati^[s] P₀) atTop (𝓝 P) := by
    intro P₀ hP₀
    set F := L.gain P
    have hup : ∀ s, L.riccati^[s] P₀ ≤ (L.TF F)^[s] P₀ := by
      intro s
      induction s with
      | zero => exact le_rfl
      | succ s ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (ls_riccati_le_TF L (ls_iter_psd L hP₀ s) F).trans (L.TF_mono F ih)
    have hlow : ∀ s, L.riccati^[s] 0 ≤ L.riccati^[s] P₀ := fun s =>
      ls_iter_mono_le L PosSemidef.zero (ls_zero_le_psd hP₀) s
    have hTlim : Tendsto (fun s => (L.TF F)^[s] P₀) atTop (𝓝 P) := by
      rw [hPF]
      exact tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hst.tendsto_TF_iterate P₀ a b
    refine ls_tendsto_of_quad (fun s => (SS.LQProblem.posSemidef_iff_real.1
      (ls_iter_psd L hP₀ s)).1) (SS.LQProblem.posSemidef_iff_real.1 hP).1 fun v => ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (ls_tendsto_quad hlim v)
      (ls_tendsto_quad hTlim v) (fun s => ls_quad_le (hlow s) v) (fun s => ls_quad_le (hup s) v)
  refine ⟨P, hP, hfix, hst, hPF, hconv, fun P' hP' hfix' => ?_⟩
  have h := hconv P' hP'
  have hc : (fun s => L.riccati^[s] P') = fun _ => P' :=
    funext fun s => Function.iterate_fixed hfix' s
  rw [hc] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Infinite-horizon limits: Propositions 9.3.1 and 9.3.2

Miao, §9.3, pp. 298–304. For an `LSProblem` with `S = 0` the Riccati operator (9.11) of the
discounted problem is the undiscounted Riccati map of `(√βA, √βB)` (`toSS`, `toSS_riccati`,
`toSS_gain`): discounting is removed by the transformation `x̂_t = β^{t/2}x_t`,
`û_t = β^{t/2}u_t` (`ls_discount_rescale`). The results of `LSRiccatiConvergence` then give:

* (9.11) for the stationary finite-horizon problem: `P(s) = T(P(s − 1)) = Tˢ(P(0))`,
  `F(s) = F(P(s − 1))`, and the constants `d(s)` (`eq_9_11`, `toFin_dbk`).
* The proof of Proposition 9.3.1: `P(1) = Q` (`ls_P_one`), `P(s) ≤ P(s + 1)` (`ls_P_mono`; the
  book's strict `P(s + 1) > P(s)` is false, `ls_P_mono_not_strict`).
* **Proposition 9.3.1** (`proposition_9_3_1`): `Q > 0`, `R > 0`, `(√βA, √βB)` controllable or
  stabilizable ⇒ `P = T(P)` (9.12) has a unique positive semidefinite solution, and
  `P(s) → P` from every positive semidefinite `P(0)`.
* **Proposition 9.3.2** (`proposition_9_3_2`): the same with `Q = L'L`, `(√βA, L)` observable or
  detectable.
* `ls_discounted_main`: the full conclusion, also giving that `√β(A − BF)` is stable,
  (9.13) `P = Q + F'RF + βΓ'PΓ` and the series `P = ∑ (√βΓ')ʲ(Q + F'RF)(√βΓ)ʲ`
  (`eq_9_13`, `eq_9_13_series`); (9.14) (`eq_9_14`); the upper bound
  `P(s) ≤ ∑_{j<s} βʲΓ'ʲ(Q + F'RF)Γʲ + βˢΓ'ˢP(0)Γˢ` (`ls_P_le_policy`; the book omits `βˢ`).
* The value function and the optimal policy of the infinite-horizon deterministic problem
  (`ls_infinite_value`), and, in the general case with `S ≠ 0` and noise,
  `V(x) = −x'Px − d`, `d = (1 − β)⁻¹β tr(PCC')`, `u = −Fx` (9.16)–(9.17) (`eq_9_16_9_17`).
* The limits `F(s) → F` and `d(s) → d` (`ls_F_tendsto`, `ls_dIter_tendsto`).
* The side condition (9.10) (`eq_9_10_growth`, `ls_stable_of_side_condition`).
* Policy improvement: the rewritten Riccati equation and solvability of its Lyapunov step
  (`ls_policy_riccati`, `ls_policy_lyapunov`).
* The Lagrange method: the multiplier `λ_t = Px_t` satisfies the first-order conditions and the
  constraint (`ls_lagrange`), and `V(x + h) = V(x) − 2λ·h − h'Ph` (`ls_envelope`).
* Controllability implies stabilizability (`controllable_stabilizable`, Miao p. 293).
-/

open Filter Topology Matrix MeasureTheory

open scoped MatrixOrder

namespace Miao.LinearQuadratic

namespace LSProblem

variable {X U E : Type*} [Fintype X] [Fintype U] [DecidableEq U] (L : LSProblem X U E)

/-- The undiscounted Sargent–Stachurski problem `(Q, R, √βA, √βB)` of an `LSProblem`. -/
noncomputable def toSS (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) : SS.LQProblem X U :=
  ⟨Real.sqrt L.β • L.A, Real.sqrt L.β • L.B, L.Q, L.R, hQ, hR⟩

omit [DecidableEq U] in
theorem toSS_gainDen (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (P : Matrix X X ℝ) : (L.toSS hQ hR).gainDen P = L.G P := by
  simp only [SS.LQProblem.gainDen, toSS, G, transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt hβ]
  abel

/-- With `S = 0`, the Riccati operator (9.11) is the Riccati map of `(Q, R, √βA, √βB)`. -/
theorem toSS_riccati (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (P : Matrix X X ℝ) : (L.toSS hQ hR).riccati P = L.T P := by
  have hb := Real.mul_self_sqrt hβ
  rw [SS.LQProblem.riccati, toSS_gainDen L hβ]
  simp only [toSS, T, N, hS, transpose_zero, zero_add, transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [show Real.sqrt L.β * (Real.sqrt L.β * (Real.sqrt L.β * Real.sqrt L.β)) = L.β * L.β by
    rw [hb, ← mul_assoc, hb], hb]
  abel

/-- With `S = 0`, the gain (9.17) is minus the Sargent–Stachurski gain of `(√βA, √βB)`. -/
theorem toSS_gain (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (P : Matrix X X ℝ) : (L.toSS hQ hR).gain P = -L.F P := by
  have hb := Real.mul_self_sqrt hβ
  rw [SS.LQProblem.gain, toSS_gainDen L hβ]
  simp only [toSS, F, N, hS, transpose_zero, zero_add, transpose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hb]

omit [DecidableEq U] in
theorem toSS_closedLoop (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) (F : Matrix U X ℝ) :
    (L.toSS hQ hR).closedLoop (-F) = Real.sqrt L.β • (L.A - L.B * F) := by
  simp only [SS.LQProblem.closedLoop, toSS, Matrix.smul_mul, Matrix.mul_neg, smul_sub]
  abel

omit [DecidableEq U] in
theorem toSS_costMat (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) (F : Matrix U X ℝ) :
    (L.toSS hQ hR).costMat (-F) = L.Q + Fᵀ * L.R * F := by
  simp only [SS.LQProblem.costMat, toSS, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  abel

theorem toSS_riccati_iter (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef)
    (hR : L.R.PosDef) (s : ℕ) : (L.toSS hQ hR).riccati^[s] = L.T^[s] := by
  have : (L.toSS hQ hR).riccati = L.T := funext (L.toSS_riccati hS hβ hQ hR)
  rw [this]

omit [DecidableEq U] in
/-- The loss with `S = 0`. -/
theorem loss_S_zero (hS : L.S = 0) (x : X → ℝ) (u : U → ℝ) :
    L.loss x u = x ⬝ᵥ (L.Q *ᵥ x) + u ⬝ᵥ (L.R *ᵥ u) := by
  simp [loss, hS]

omit [DecidableEq U] in
/-- Removing the discount (Miao, pp. 299–301): with `x̂_t = β^{t/2}x_t`, `û_t = β^{t/2}u_t`,
the transition `x_{t+1} = Ax_t + Bu_t` becomes `x̂_{t+1} = √βAx̂_t + √βBû_t` and
`βᵗr(x_t, u_t) = r(x̂_t, û_t)`. -/
theorem ls_discount_rescale (hβ : 0 ≤ L.β) {x : ℕ → X → ℝ} {u : ℕ → U → ℝ}
    (hx : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) (t : ℕ) :
    Real.sqrt L.β ^ (t + 1) • x (t + 1) =
        (Real.sqrt L.β • L.A) *ᵥ (Real.sqrt L.β ^ t • x t) +
          (Real.sqrt L.β • L.B) *ᵥ (Real.sqrt L.β ^ t • u t) ∧
      L.β ^ t * L.loss (x t) (u t) =
        L.loss (Real.sqrt L.β ^ t • x t) (Real.sqrt L.β ^ t • u t) := by
  have hb : Real.sqrt L.β ^ t * Real.sqrt L.β ^ t = L.β ^ t := by
    rw [← mul_pow, Real.mul_self_sqrt hβ]
  refine ⟨?_, ?_⟩
  · rw [hx, smul_add, smul_mulVec, smul_mulVec, mulVec_smul, mulVec_smul, smul_smul, smul_smul,
      pow_succ']
  · simp only [loss, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [← hb]
    ring

/-! ### The stationary finite-horizon problem and (9.11) -/

/-- The stationary finite-horizon problem with horizon `T` and terminal matrix `P(0)`. -/
def toFin (hor : ℕ) (PT : Matrix X X ℝ) : LSFinProblem X U E :=
  ⟨fun _ => L.A, fun _ => L.B, fun _ => L.C, fun _ => L.Q, fun _ => L.R, fun _ => L.S, L.β,
    hor, PT⟩

omit [Fintype X] [Fintype U] [DecidableEq U] in
theorem toFin_stage (hor : ℕ) (PT : Matrix X X ℝ) (t : ℕ) : (L.toFin hor PT).stage t = L := rfl

theorem toFin_Pbk (hor : ℕ) (PT : Matrix X X ℝ) (s : ℕ) :
    (L.toFin hor PT).Pbk s = L.T^[s] PT := by
  induction s with
  | zero => rfl
  | succ s ih => rw [LSFinProblem.Pbk, ih, toFin_stage, Function.iterate_succ_apply']

/-- The constants `d(s)` of the stationary finite-horizon problem:
`d(s + 1) = β tr(P(s)CC') + βd(s)`, `d(0) = 0`. -/
noncomputable def dIter [Fintype E] (P₀ : Matrix X X ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => L.β * trace (L.T^[s] P₀ * L.C * L.Cᵀ) + L.β * dIter P₀ s

theorem toFin_dbk [Fintype E] (hor : ℕ) (PT : Matrix X X ℝ) (s : ℕ) :
    (L.toFin hor PT).dbk s = L.dIter PT s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [LSFinProblem.dbk, ih, toFin_Pbk, dIter]
    rfl

/-- (9.11) (Miao, p. 298): for the stationary problem, with `s = T − t` periods remaining,
`P(s) = T(P(s − 1)) = Tˢ(P(0))` and `F(s) = (R + βB'P(s − 1)B)⁻¹(S' + βB'P(s − 1)A)`. -/
theorem eq_9_11 (hor : ℕ) (PT : Matrix X X ℝ) {s : ℕ} (hs : s ≤ hor) :
    (L.toFin hor PT).P (hor - s) = L.T^[s] PT ∧
      (0 < s → (L.toFin hor PT).Fg (hor - s) = L.F (L.T^[s - 1] PT)) := by
  refine ⟨?_, fun hs0 => ?_⟩
  · rw [LSFinProblem.P, show (L.toFin hor PT).hor - (hor - s) = s from by
      change hor - (hor - s) = s; omega, toFin_Pbk]
  · rw [LSFinProblem.Fg, toFin_stage, LSFinProblem.P,
      show (L.toFin hor PT).hor - (hor - s + 1) = s - 1 from by
        change hor - (hor - s + 1) = s - 1; omega, toFin_Pbk]

theorem T_zero_S (hS : L.S = 0) : L.T 0 = L.Q := by
  simp [T, hS, N]

/-- Miao, p. 299: `P(0) = 0` gives `P(1) = Q`, so `V₁(x) = −x'Qx < 0 = V₀(x)` for `x ≠ 0` when
`Q > 0`. -/
theorem ls_P_one (hS : L.S = 0) (hQ : L.Q.PosDef) :
    L.T^[1] 0 = L.Q ∧ ∀ x : X → ℝ, x ≠ 0 → -(x ⬝ᵥ (L.T^[1] 0 *ᵥ x)) < -(x ⬝ᵥ (0 *ᵥ x)) := by
  have h1 : L.T^[1] 0 = L.Q := by simp [T_zero_S L hS]
  refine ⟨h1, fun x hx => ?_⟩
  rw [h1, zero_mulVec, dotProduct_zero, neg_zero, neg_lt_zero]
  exact (SS.LQProblem.posDef_iff_real.1 hQ).2 hx

/-- Miao, p. 299 (corrected): `P(s) ≤ P(s + 1)` for `P(0) = 0`. -/
theorem ls_P_mono (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (s : ℕ) : L.T^[s] 0 ≤ L.T^[s + 1] 0 := by
  rw [← toSS_riccati_iter L hS hβ hQ hR, ← toSS_riccati_iter L hS hβ hQ hR]
  exact ls_iter_zero_mono _ s

/-- Miao, p. 299, "`P(s + 1) > P(s)` for any `s`" is false: with `A = 0` (scalar, `Q = R = 1`,
`B = 1`, `β = 1`), `T(P) = Q` for every `P`, so `P(2) = P(1)`. -/
theorem ls_P_mono_not_strict :
    let L0 : LSProblem (Fin 1) (Fin 1) (Fin 1) := ⟨0, 1, 0, 1, 1, 0, 1⟩
    L0.T^[2] 0 = L0.T^[1] 0 := by
  intro L0
  have hT : ∀ P, L0.T P = 1 := fun P => by simp [L0, T, N]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hT]

/-! ### Propositions 9.3.1 and 9.3.2 -/

/-- The common conclusion of Propositions 9.3.1–9.3.2 (Miao, pp. 299–301), for `S = 0` and
`β ≥ 0`: if `(√βA, √βB)` is controllable or stabilizable and the detection condition holds,
the Riccati equation (9.12) has a positive semidefinite solution `P`, unique among positive
semidefinite matrices, `P(s) = Tˢ(P(0)) → P` for every positive semidefinite `P(0)`,
`√β(A − BF)` is stable for `F = F(P)`, and `P = ∑ (√βΓ')ʲ(Q + F'RF)(√βΓ)ʲ`. -/
theorem ls_discounted_main [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hβ : 0 ≤ L.β)
    (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B))
    (hD : ∀ F, ls_Detects (L.toSS hQ hR) F) :
    ∃ P : Matrix X X ℝ, P.PosSemidef ∧ L.T P = P ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P) ∧
      (∀ P₀ : Matrix X X ℝ, P₀.PosSemidef → Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P)) ∧
      ls_Stable (Real.sqrt L.β • (L.A - L.B * L.F P)) ∧
      P = (L.toSS hQ hR).PF (-L.F P) := by
  have hstab' : (∃ F, (L.toSS hQ hR).IsStable F) ∨
      ls_Controllable (L.toSS hQ hR).A (L.toSS hQ hR).B := by
    rcases hstab with hc | ⟨H, hH⟩
    · exact Or.inr hc
    · exact Or.inl ⟨H, ls_specRad_lt_of_stable hH⟩
  obtain ⟨P, hP, hfix, hst, hPF, hconv, huniq⟩ := ls_riccati_main (L.toSS hQ hR) hstab' hD
  rw [L.toSS_riccati hS hβ] at hfix
  rw [L.toSS_gain hS hβ] at hst hPF
  refine ⟨P, hP, hfix, fun P' hP' h' => huniq P' hP' (by rw [L.toSS_riccati hS hβ]; exact h'),
    fun P₀ hP₀ => ?_, ?_, hPF⟩
  · simpa only [L.toSS_riccati_iter hS hβ hQ hR] using hconv P₀ hP₀
  · have := ls_stable_of_specRad hst
    rwa [toSS_closedLoop] at this

/-- **Proposition 9.3.1** (Miao, p. 299). Suppose `S = 0`, (i) `Q > 0`, (ii) `R > 0`, (iii)
`(√βA, √βB)` is controllable or stabilizable (and `β ≥ 0`; the book has `β ∈ (0, 1]`). Then
(i) the Riccati equation `P = T(P)` (9.12) has a unique positive semidefinite solution `P`;
(ii) `P(s) = Tˢ(P(0)) → P` for every positive semidefinite `P(0)`. -/
theorem proposition_9_3_1 [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hQ : L.Q.PosDef)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B)) :
    ∃ P : Matrix X X ℝ, (P.PosSemidef ∧ L.T P = P) ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P) ∧
      ∀ P₀ : Matrix X X ℝ, P₀.PosSemidef → Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P) := by
  obtain ⟨P, hP, hfix, huniq, hconv, -⟩ := L.ls_discounted_main hS hβ hQ.posSemidef hR hstab
    fun F => ls_detects_of_posDef (L.toSS hQ.posSemidef hR) hQ F
  exact ⟨P, ⟨hP, hfix⟩, huniq, hconv⟩

/-- **Proposition 9.3.2** (Miao, p. 301): Proposition 9.3.1 holds with (i) weakened to
`Q = L'L` with `(√βA, L)` observable or detectable. -/
theorem proposition_9_3_2 [Nonempty X] [DecidableEq X] {Y : Type*} [Fintype Y] (hS : L.S = 0)
    {Lm : Matrix Y X ℝ} (hQL : L.Q = Lmᵀ * Lm)
    (hobs : ls_Observable (Real.sqrt L.β • L.A) Lm ∨ ls_Detectable (Real.sqrt L.β • L.A) Lm)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B)) :
    ∃ P : Matrix X X ℝ, (P.PosSemidef ∧ L.T P = P) ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P) ∧
      ∀ P₀ : Matrix X X ℝ, P₀.PosSemidef → Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P) := by
  have hQ : L.Q.PosSemidef := by
    rw [hQL]
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self Lm
  have hD : ∀ F, ls_Detects (L.toSS hQ hR) F := by
    rcases hobs with ho | hd
    · exact fun F => ls_detects_of_observable (L.toSS hQ hR) hQL ho F
    · exact fun F => ls_detects_of_detectable (L.toSS hQ hR) hQL hd F
  obtain ⟨P, hP, hfix, huniq, hconv, -⟩ := L.ls_discounted_main hS hβ hQ hR hstab hD
  exact ⟨P, ⟨hP, hfix⟩, huniq, hconv⟩

/-- (9.13) (Miao, p. 300): with `S = 0`, a fixed point `P = T(P)` satisfies
`P = Q + F'RF + βΓ'PΓ`, `F = (R + βB'PB)⁻¹βB'PA`, `Γ = A − BF`. -/
theorem eq_9_13 (hS : L.S = 0) {P : Matrix X X ℝ} (hG : IsUnit (L.G P).det) (hfix : L.T P = P) :
    P = L.Q + (L.F P)ᵀ * L.R * L.F P +
      L.β • ((L.A - L.B * L.F P)ᵀ * P * (L.A - L.B * L.F P)) := by
  conv_lhs => rw [← hfix, ← L.TF_F hG]
  simp [TF, hS]

omit [Fintype U] [DecidableEq U] in
/-- `((√βM)ʲ)'W(√βM)ʲ = βʲ(Mʲ)'WMʲ`. -/
theorem ls_sqrt_sandwich [DecidableEq X] {β : ℝ} (hβ : 0 ≤ β) (M W : Matrix X X ℝ) (j : ℕ) :
    ((Real.sqrt β • M) ^ j)ᵀ * W * (Real.sqrt β • M) ^ j = β ^ j • ((M ^ j)ᵀ * W * M ^ j) := by
  simp only [smul_pow, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← mul_pow, Real.mul_self_sqrt hβ]

/-- The series form of (9.13) (Miao, p. 300): if `√βΓ` is stable,
`P = ∑ⱼ (√βΓ')ʲ(Q + F'RF)(√βΓ)ʲ = ∑ⱼ βʲΓ'ʲ(Q + F'RF)Γʲ` (entrywise). -/
theorem eq_9_13_series [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hβ : 0 ≤ L.β)
    (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hfix : L.T P = P) (hst : ls_Stable (Real.sqrt L.β • (L.A - L.B * L.F P))) (a b : X) :
    HasSum (fun j => ((L.β ^ j • (((L.A - L.B * L.F P) ^ j)ᵀ *
      (L.Q + (L.F P)ᵀ * L.R * L.F P) * (L.A - L.B * L.F P) ^ j) : Matrix X X ℝ) a b))
      (P a b) := by
  have hst' : (L.toSS hQ hR).IsStable (-L.F P) := by
    rw [SS.LQProblem.IsStable, toSS_closedLoop]
    exact ls_specRad_lt_of_stable hst
  have hTF : (L.toSS hQ hR).TF (-L.F P) P = P := by
    rw [← L.toSS_gain hS hβ hQ hR, ← SS.LQProblem.riccati_eq_TF _ hP, L.toSS_riccati hS hβ, hfix]
  have hPF := hst'.eq_PF hTF
  have h := hst'.hasSum_PF a b
  rw [← hPF] at h
  refine h.congr_fun fun j => ?_
  simp only [SS.LQProblem.discCost, toSS_closedLoop, toSS_costMat, ls_sqrt_sandwich hβ]

/-- (9.14) (Miao, p. 300): at a fixed point, along `x_{t+1} = √βΓx_t`, `V(x) = −x'Px` increases,
`V(x_{t+1}) − V(x_t) = x_t'(Q + F'RF)x_t ≥ 0`, and `x_t'(Q + F'RF)x_t → 0`. -/
theorem eq_9_14 (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef) (hR : L.R.PosDef)
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (hfix : L.T P = P) {x : ℕ → X → ℝ}
    (hx : ∀ t, x (t + 1) = (Real.sqrt L.β • (L.A - L.B * L.F P)) *ᵥ x t) :
    (∀ t, -(x (t + 1) ⬝ᵥ (P *ᵥ x (t + 1))) - -(x t ⬝ᵥ (P *ᵥ x t)) =
      x t ⬝ᵥ ((L.Q + (L.F P)ᵀ * L.R * L.F P) *ᵥ x t)) ∧
    Tendsto (fun t => x t ⬝ᵥ ((L.Q + (L.F P)ᵀ * L.R * L.F P) *ᵥ x t)) atTop (𝓝 0) := by
  have hfix' : (L.toSS hQ hR).riccati P = P := by rw [L.toSS_riccati hS hβ, hfix]
  have hx' : ∀ t, x (t + 1) = (L.toSS hQ hR).closedLoop ((L.toSS hQ hR).gain P) *ᵥ x t := by
    intro t
    rw [L.toSS_gain hS hβ, toSS_closedLoop, hx]
  obtain ⟨hsum, hQt, hFt⟩ := ls_cost_tendsto_zero (L.toSS hQ hR) hP hfix' hx'
  have hcm : (L.toSS hQ hR).costMat ((L.toSS hQ hR).gain P) = L.Q + (L.F P)ᵀ * L.R * L.F P := by
    rw [L.toSS_gain hS hβ, toSS_costMat]
  refine ⟨fun t => ?_, ?_⟩
  · have h1 := hsum (t + 1)
    have h2 := hsum t
    rw [Finset.sum_range_succ, hcm] at h1
    rw [hcm] at h2
    linarith
  · have hFt' : Tendsto (fun t => (L.F P *ᵥ x t) ⬝ᵥ (L.R *ᵥ (L.F P *ᵥ x t))) atTop (𝓝 0) := by
      rw [L.toSS_gain hS hβ] at hFt
      have h := hFt.neg
      simp only [neg_zero] at h
      have hc : Continuous fun v : U → ℝ => v ⬝ᵥ (L.R *ᵥ v) :=
        Continuous.dotProduct continuous_id
          (Continuous.matrix_mulVec continuous_const continuous_id)
      have := (hc.tendsto 0).comp h
      simpa [Function.comp_def, neg_mulVec] using this
    have := hQt.add hFt'
    rw [add_zero] at this
    refine this.congr fun t => ?_
    rw [add_mulVec, dotProduct_add, SS.LQProblem.dotProduct_transpose_mul_mul]
    rfl

/-- The upper bound of p. 300, corrected: for any `F`, with `Γ = A − BF`,
`P(s) = Tˢ(P(0)) ≤ ∑_{j<s} βʲΓ'ʲ(Q + F'RF)Γʲ + βˢΓ'ˢP(0)Γˢ` (the book omits `βˢ`). -/
theorem ls_P_le_policy [DecidableEq X] (hS : L.S = 0) (hβ : 0 ≤ L.β) (hQ : L.Q.PosSemidef)
    (hR : L.R.PosDef) {P₀ : Matrix X X ℝ} (hP₀ : P₀.PosSemidef) (F : Matrix U X ℝ) (s : ℕ) :
    L.T^[s] P₀ ≤ ∑ j ∈ Finset.range s, L.β ^ j • (((L.A - L.B * F) ^ j)ᵀ *
      (L.Q + Fᵀ * L.R * F) * (L.A - L.B * F) ^ j) +
      L.β ^ s • (((L.A - L.B * F) ^ s)ᵀ * P₀ * (L.A - L.B * F) ^ s) := by
  set L' := L.toSS hQ hR
  have hup : ∀ s, L'.riccati^[s] P₀ ≤ (L'.TF (-F))^[s] P₀ := by
    intro s
    induction s with
    | zero => exact le_rfl
    | succ s ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (ls_riccati_le_TF L' (ls_iter_psd L' hP₀ s) (-F)).trans (L'.TF_mono (-F) ih)
  have h := hup s
  rw [L.toSS_riccati_iter hS hβ hQ hR, SS.LQProblem.TF_iterate] at h
  simpa only [SS.LQProblem.discCost, L', toSS_closedLoop, toSS_costMat, ls_sqrt_sandwich hβ]
    using h

/-- The printed bound of p. 300 does not tend to `P`: with `A = 1`, `B = 0`, `Q = R = 1`,
`β = 1/4` (so `(√βA, √βB)` is stabilizable and Proposition 9.3.1 applies), `Γ = A − BF = 1` for
every `F`, so the printed remainder `Γ'ˢP(0)Γˢ = P(0)` does not vanish. -/
theorem ls_P_le_policy_misprint (F : Matrix (Fin 1) (Fin 1) ℝ) (P₀ : Matrix (Fin 1) (Fin 1) ℝ)
    (s : ℕ) :
    let L0 : LSProblem (Fin 1) (Fin 1) (Fin 1) := ⟨1, 0, 0, 1, 1, 0, 1 / 4⟩
    ((L0.A - L0.B * F) ^ s)ᵀ * P₀ * (L0.A - L0.B * F) ^ s = P₀ := by
  intro L0
  simp [L0]

/-! ### The value function and the optimal policy -/

/-- The infinite-horizon value function and optimal policy (Miao, pp. 299–301), deterministic
case with `S = 0`, `β > 0`: if `P = T(P)` is the limit of `Tˢ(0)` and `√β(A − BF)` is stable
(`F = F(P)`), then (a) every control sequence costs at least `x₀'Tˢ(0)x₀` over `s` periods, and
at least `x₀'Px₀` in total; (b) the stationary rule `u_t = −Fx_t` costs exactly `x₀'Px₀`. So
`V(x) = −x'Px` and `u = −Fx` is optimal. -/
theorem ls_infinite_value [Nonempty X] [DecidableEq X] (hS : L.S = 0) (hβ : 0 < L.β)
    (hQ : L.Q.PosSemidef) (hR : L.R.PosDef) {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hfix : L.T P = P) (hlim : Tendsto (fun s => L.T^[s] 0) atTop (𝓝 P))
    (hst : ls_Stable (Real.sqrt L.β • (L.A - L.B * L.F P))) (x₀ : X → ℝ) :
    (∀ (x : ℕ → X → ℝ) (u : ℕ → U → ℝ), x 0 = x₀ →
      (∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) →
      (∀ s, x₀ ⬝ᵥ (L.T^[s] 0 *ᵥ x₀) ≤
        ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t)) ∧
      (Summable (fun t => L.β ^ t * L.loss (x t) (u t)) →
        x₀ ⬝ᵥ (P *ᵥ x₀) ≤ ∑' t, L.β ^ t * L.loss (x t) (u t))) ∧
    ∀ x : ℕ → X → ℝ, x 0 = x₀ → (∀ t, x (t + 1) = (L.A - L.B * L.F P) *ᵥ x t) →
      HasSum (fun t => L.β ^ t * L.loss (x t) (-(L.F P *ᵥ x t))) (x₀ ⬝ᵥ (P *ᵥ x₀)) := by
  set sb := Real.sqrt L.β
  refine ⟨fun x u hx0 hx => ?_, fun x hx0 hx => ?_⟩
  · have hfin : ∀ s, x₀ ⬝ᵥ (L.T^[s] 0 *ᵥ x₀) ≤
        ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) := by
      intro s
      have h := ls_finite_lower (L.toSS hQ hR) PosSemidef.zero s (fun t => sb ^ t • x t)
        (fun t => sb ^ t • u t) fun t => (L.ls_discount_rescale hβ.le hx t).1
      rw [L.toSS_riccati_iter hS hβ.le hQ hR] at h
      simp only [pow_zero, one_smul, hx0, zero_mulVec, dotProduct_zero, add_zero] at h
      refine h.trans (le_of_eq (Finset.sum_congr rfl fun t _ => ?_))
      rw [(L.ls_discount_rescale hβ.le hx t).2, L.loss_S_zero hS]
      rfl
    refine ⟨hfin, fun hs => ?_⟩
    exact le_of_tendsto_of_tendsto' (ls_tendsto_quad hlim x₀) hs.hasSum.tendsto_sum_nat hfin
  · have hst' : (L.toSS hQ hR).IsStable (-L.F P) := by
      rw [SS.LQProblem.IsStable, toSS_closedLoop]
      exact ls_specRad_lt_of_stable hst
    have hTF : (L.toSS hQ hR).TF (-L.F P) P = P := by
      rw [← L.toSS_gain hS hβ.le hQ hR, ← SS.LQProblem.riccati_eq_TF _ hP,
        L.toSS_riccati hS hβ.le, hfix]
    have hPF := hst'.eq_PF hTF
    have h := hst'.hasSum_cost x₀
    rw [← hPF] at h
    have hxt : ∀ t, x t = ((L.A - L.B * L.F P) ^ t) *ᵥ x₀ := by
      intro t
      induction t with
      | zero => simp [hx0]
      | succ t ih => rw [hx, ih, mulVec_mulVec, pow_succ']
    have hu : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ (-(L.F P *ᵥ x t)) := fun t => by
      rw [hx, sub_mulVec, mulVec_neg, ← mulVec_mulVec, sub_eq_add_neg]
    refine h.congr_fun fun t => ?_
    rw [(L.ls_discount_rescale hβ.le hu t).2, L.loss_S_zero hS, toSS_closedLoop, toSS_costMat,
      smul_pow, smul_mulVec, ← hxt t, add_mulVec, dotProduct_add,
      SS.LQProblem.dotProduct_transpose_mul_mul]
    simp only [mulVec_smul, smul_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

variable [Fintype E] [DecidableEq E]

/-- (9.16)–(9.17) (Miao, pp. 301–302), the general case with `S ≠ 0` and uncertainty: if
`P ≥ 0` solves (9.12) and `0 ≤ β < 1`, then `V(x) = −x'Px − d` with
`d = (1 − β)⁻¹β tr(PCC')` satisfies the Bellman equation
`V(x) = max_u {−r(x, u) + βE V(Ax + Bu + Cε)}`, and the maximum is attained exactly at
`u = −Fx` with `F = (R + βB'PB)⁻¹(S' + βB'PA)`. -/
theorem eq_9_16_9_17 {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.R.PosDef)
    (hβ0 : 0 ≤ L.β) (hβ1 : L.β < 1) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hfix : L.T P = P)
    (x : X → ℝ) :
    IsGreatest (Set.range (L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) -
        (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) x))
        (-(x ⬝ᵥ (P *ᵥ x)) - (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) ∧
      ∀ u, L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) -
          (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) x u =
          -(x ⬝ᵥ (P *ᵥ x)) - (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)) ↔
        u = -(L.F P *ᵥ x) := by
  have hd : L.β * trace (P * L.C * L.Cᵀ) + L.β * ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) =
      (1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)) := by
    have : (1 - L.β) ≠ 0 := by linarith
    field_simp
    ring
  have h := L.bellObj_isGreatest hν hR hP hβ0 ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ))) x
  rw [hd, hfix] at h
  exact h

end LSProblem

/-- Miao, p. 293: controllability implies stabilizability. (With `Q = R = I`, the controllable
case of Proposition 9.3.1 gives a fixed point whose gain `H` makes `A + BH` stable.) -/
theorem controllable_stabilizable {X U : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype U] {A : Matrix X X ℝ} {B : Matrix X U ℝ}
    (hc : ls_Controllable A B) : ls_Stabilizable A B := by
  classical
  set L0 : SS.LQProblem X U := ⟨A, B, 1, 1, PosSemidef.one, PosDef.one⟩
  obtain ⟨P, -, -, hst, -⟩ := ls_riccati_main L0 (Or.inr hc)
    fun F => ls_detects_of_posDef L0 PosDef.one F
  exact ⟨L0.gain P, ls_stable_of_specRad hst⟩


end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Limits, the side condition and the numerical methods of §9.3

Miao, §9.3, pp. 298–304.

* `ls_F_tendsto` (p. 299): `P(s) → P` gives `F(s) = F(P(s − 1)) → F(P)`.
* `ls_dIter_tendsto` (pp. 299, 302): for `β < 1`, `d(s) → d = (1 − β)⁻¹β tr(PCC')`.
* (9.10) (p. 298): `E∑βᵗ(u_t·u_t + x_t·x_t) < ∞` forces `βᵗ|x_t|² → 0` and `βᵗ|u_t|² → 0`
  (`eq_9_10_growth`); if every closed-loop path `x_{t+1} = Γx_t` satisfies the side condition
  then `√βΓ` is stable (`ls_stable_of_side_condition`), which is how (9.10) replaces
  observability or detectability in Proposition 9.3.2 (p. 301).
* Policy improvement (p. 302): the Riccati equation rewritten with `F = F(P)`
  (`ls_policy_riccati`), and the Lyapunov step
  `P_j = Q + F_j'RF_j − SF_j − F_j'S' + β(A − BF_j)'P_j(A − BF_j)` has a unique solution when the
  eigenvalues of `A − BF_j` are below `1/√β` in modulus, i.e. `√β(A − BF_j)` is stable
  (`ls_policy_lyapunov`).
* The Lagrange method (pp. 303–304): with `u_t = −Fx_t` and `λ_t = Px_t`, the first-order
  conditions `Ru_t + S'x_t + βB'E_tλ_{t+1} = 0`, `λ_t = Qx_t + Su_t + βA'E_tλ_{t+1}` hold
  (`ls_lagrange`), where `E_tλ_{t+1} = PE_tx_{t+1} = P(Ax_t + Bu_t)`; and for `V(x) = −x'Px − d`,
  `V(x + h) = V(x) − 2λ·h − h'Ph` (`ls_envelope`): the gradient of `V` is `−2λ`, not `λ` as printed.
-/

open Filter Topology Matrix

namespace Miao.LinearQuadratic

variable {X U E : Type*} [Fintype X] [Fintype U]

omit [Fintype U] in
/-- (9.10) (Miao, p. 298): if `∑βᵗ(u_t·u_t + x_t·x_t) < ∞` then `βᵗ x_t·x_t → 0` and
`βᵗ u_t·u_t → 0`: `x_t`, `u_t` cannot grow at a rate exceeding `1/√β`. -/
theorem eq_9_10_growth [Fintype U] {β : ℝ} (hβ : 0 ≤ β) {x : ℕ → X → ℝ} {u : ℕ → U → ℝ}
    (h : Summable fun t => β ^ t * (u t ⬝ᵥ u t + x t ⬝ᵥ x t)) :
    Tendsto (fun t => β ^ t * (x t ⬝ᵥ x t)) atTop (𝓝 0) ∧
      Tendsto (fun t => β ^ t * (u t ⬝ᵥ u t)) atTop (𝓝 0) := by
  classical
  have h0 := h.tendsto_atTop_zero
  have hx : ∀ t, 0 ≤ x t ⬝ᵥ x t := fun t => ls_dot_self_nonneg _
  have hu : ∀ t, 0 ≤ u t ⬝ᵥ u t := fun t => ls_dot_self_nonneg _
  refine ⟨squeeze_zero (fun t => mul_nonneg (pow_nonneg hβ t) (hx t)) (fun t => ?_) h0,
    squeeze_zero (fun t => mul_nonneg (pow_nonneg hβ t) (hu t)) (fun t => ?_) h0⟩
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hu t)) (pow_nonneg hβ t)
  · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hx t)) (pow_nonneg hβ t)

/-- Miao, p. 301: if every path of `x_{t+1} = Γx_t` satisfies the side condition
`∑βᵗx_t·x_t < ∞`, then `√βΓ` is stable. -/
theorem ls_stable_of_side_condition [DecidableEq X] {β : ℝ} (hβ : 0 ≤ β) (Γ : Matrix X X ℝ)
    (h : ∀ x : ℕ → X → ℝ, (∀ t, x (t + 1) = Γ *ᵥ x t) → Summable fun t => β ^ t * (x t ⬝ᵥ x t)) :
    ls_Stable (Real.sqrt β • Γ) := by
  rw [ls_stable_iff_tendsto]
  intro v
  have hs := h (fun t => (Γ ^ t) *ᵥ v) fun t => by rw [pow_succ', mulVec_mulVec]
  have h0 := hs.tendsto_atTop_zero
  refine ls_tendsto_zero_of_quad_posDef PosDef.one (h0.congr fun t => ?_)
  rw [one_mulVec, smul_pow, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← mul_pow, Real.mul_self_sqrt hβ]

namespace LSProblem

variable [DecidableEq U] (L : LSProblem X U E)

omit [Fintype U] [DecidableEq U] in
theorem ls_G_tendsto {Pn : ℕ → Matrix X X ℝ} {P : Matrix X X ℝ} (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.G (Pn n)) atTop (𝓝 (L.G P)) :=
  tendsto_const_nhds.add
    ((ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).const_smul L.β)

omit [Fintype U] [DecidableEq U] in
theorem ls_N_tendsto {Pn : ℕ → Matrix X X ℝ} {P : Matrix X X ℝ} (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.N (Pn n)) atTop (𝓝 (L.N P)) :=
  tendsto_const_nhds.add
    ((ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).const_smul L.β)

/-- Miao, p. 299: if `P(s) → P ≥ 0` then `F(s) = F(P(s − 1)) → F = F(P)`. -/
theorem ls_F_tendsto (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {Pn : ℕ → Matrix X X ℝ}
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.F (Pn n)) atTop (𝓝 (L.F P)) :=
  ls_tendsto_mul (ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.G_posDef hR hP hβ).isUnit)
    (L.ls_G_tendsto h)) (L.ls_N_tendsto h)

/-- Miao, pp. 299 and 302: for `0 ≤ β < 1`, if `P(s) = Tˢ(P(0)) → P` then the constants
`d(s + 1) = β tr(P(s)CC') + βd(s)` converge to `d = (1 − β)⁻¹β tr(PCC')`. -/
theorem ls_dIter_tendsto [Fintype E] (hβ0 : 0 ≤ L.β) (hβ1 : L.β < 1) {P₀ P : Matrix X X ℝ}
    (h : Tendsto (fun s => L.T^[s] P₀) atTop (𝓝 P)) :
    Tendsto (L.dIter P₀) atTop (𝓝 ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)))) := by
  set c := trace (P * L.C * L.Cᵀ)
  set dstar := (1 - L.β)⁻¹ * (L.β * c)
  set tr : ℕ → ℝ := fun s => trace (L.T^[s] P₀ * L.C * L.Cᵀ)
  have hc : Tendsto tr atTop (𝓝 c) :=
    ((Continuous.matrix_trace continuous_id).tendsto _).comp
      (ls_tendsto_mul (ls_tendsto_mul h tendsto_const_nhds) tendsto_const_nhds)
  have hfix : dstar = L.β * c + L.β * dstar := by
    have : (1 - L.β) ≠ 0 := by linarith
    simp only [dstar]
    field_simp
    ring
  have hrec : ∀ s, |L.dIter P₀ (s + 1) - dstar| ≤
      L.β * |L.dIter P₀ s - dstar| + L.β * |tr s - c| := by
    intro s
    have e : L.dIter P₀ (s + 1) - dstar = L.β * (tr s - c) + L.β * (L.dIter P₀ s - dstar) := by
      simp only [dIter, tr]
      linear_combination (-1 : ℝ) * hfix
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hβ0]
    linarith
  have hδ : Tendsto (fun s => L.β * |tr s - c|) atTop (𝓝 0) := by
    have := ((hc.sub (tendsto_const_nhds (x := c))).abs.const_mul L.β)
    simpa using this
  have he := ls_tendsto_zero_of_le_rec hβ0 hβ1 (fun s => abs_nonneg (L.dIter P₀ s - dstar))
    hrec hδ
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using he

/-- Policy improvement (Miao, p. 302): by (9.9) the Riccati equation reads
`P = Q + F'RF − SF − F'S' + β(A − BF)'P(A − BF)` with `F = F(P)`. -/
theorem ls_policy_riccati {P : Matrix X X ℝ} (hG : IsUnit (L.G P).det) :
    L.T P = L.Q + (L.F P)ᵀ * L.R * L.F P - L.S * L.F P - (L.F P)ᵀ * L.Sᵀ +
      L.β • ((L.A - L.B * L.F P)ᵀ * P * (L.A - L.B * L.F P)) := by
  rw [← L.TF_F hG, TF]
  abel

omit [DecidableEq U] in
/-- Policy improvement (Miao, pp. 302–303): if the eigenvalues of `A − BF_j` are less than
`1/√β` in modulus (`√β(A − BF_j)` stable), the Lyapunov (Sylvester) equation
`P_j = Q + F_j'RF_j − SF_j − F_j'S' + β(A − BF_j)'P_j(A − BF_j)` has a unique solution. -/
theorem ls_policy_lyapunov [DecidableEq X] [Nonempty X] (hβ : 0 ≤ L.β) (Fj : Matrix U X ℝ)
    (hst : ls_Stable (Real.sqrt L.β • (L.A - L.B * Fj))) :
    ∃ P : Matrix X X ℝ, P = L.Q + Fjᵀ * L.R * Fj - L.S * Fj - Fjᵀ * L.Sᵀ +
        L.β • ((L.A - L.B * Fj)ᵀ * P * (L.A - L.B * Fj)) ∧
      ∀ P' : Matrix X X ℝ, P' = L.Q + Fjᵀ * L.R * Fj - L.S * Fj - Fjᵀ * L.Sᵀ +
        L.β • ((L.A - L.B * Fj)ᵀ * P' * (L.A - L.B * Fj)) → P' = P := by
  set M := L.A - L.B * Fj
  set W := L.Q + Fjᵀ * L.R * Fj - L.S * Fj - Fjᵀ * L.Sᵀ
  set Φ := (Real.sqrt L.β • M)ᵀ
  have hΦ : ls_Stable Φ := (ls_stable_transpose _).2 hst
  have hmap : ∀ Y, var_lyapMap Φ W Y = W + L.β • (Mᵀ * Y * M) := by
    intro Y
    simp only [var_lyapMap, Φ, transpose_transpose, transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hβ]
    abel
  refine ⟨var_lyapSol Φ W, ?_, fun P' hP' => lyap_unique Φ hΦ W P' (by rw [hmap]; exact hP'.symm)⟩
  rw [← hmap]
  exact (lyap_fixed Φ hΦ W).symm

/-- The Lagrange method (Miao, pp. 303–304): at a fixed point `P = T(P)`, with `u = −Fx`,
`x₊ = Ax + Bu` (`= E_tx_{t+1}`) and multipliers `λ = Px`, `λ₊ = Px₊` (`= E_tλ_{t+1}`), the
first-order conditions hold: `Ru + S'x + βB'λ₊ = 0` and `λ = Qx + Su + βA'λ₊`. -/
theorem ls_lagrange {P : Matrix X X ℝ} (hG : IsUnit (L.G P).det) (hfix : L.T P = P)
    (x : X → ℝ) :
    L.R *ᵥ (-(L.F P *ᵥ x)) + L.Sᵀ *ᵥ x +
        L.β • (L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ (-(L.F P *ᵥ x))))) = 0 ∧
      P *ᵥ x = L.Q *ᵥ x + L.S *ᵥ (-(L.F P *ᵥ x)) +
        L.β • (L.Aᵀ *ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ (-(L.F P *ᵥ x))))) := by
  set y := L.F P *ᵥ x
  have hGy : L.G P *ᵥ y = L.N P *ᵥ x := by rw [mulVec_mulVec, G_mul_F _ hG]
  refine ⟨?_, ?_⟩
  · have e : L.R *ᵥ (-y) + L.Sᵀ *ᵥ x + L.β • (L.Bᵀ *ᵥ (P *ᵥ (L.A *ᵥ x + L.B *ᵥ (-y)))) =
        L.N P *ᵥ x - L.G P *ᵥ y := by
      simp only [G, N, add_mulVec, smul_mulVec, mulVec_add, mulVec_neg, smul_add, smul_neg,
        ← mulVec_mulVec]
      abel
    rw [e, hGy, sub_self]
  · conv_lhs => rw [← hfix, T_eq_sub]
    simp only [sub_mulVec, add_mulVec, smul_mulVec, mulVec_add, mulVec_neg, smul_add, smul_neg,
      ← mulVec_mulVec]
    abel

omit [Fintype U] [DecidableEq U] in
/-- The envelope condition (Miao, p. 303), corrected: for `V(x) = −x'Px − d` with symmetric `P`
and `λ = Px`, `V(x + h) = V(x) − 2λ·h − h'Ph`, so `∂V/∂x = −2λ` (the book prints
`∂V/∂x = Qλ_t + Su_t + βA'E_tλ_{t+1} = λ_t`). -/
theorem ls_envelope {P : Matrix X X ℝ} (hP : Pᵀ = P) (d : ℝ) (x h : X → ℝ) :
    -((x + h) ⬝ᵥ (P *ᵥ (x + h))) - d =
      (-(x ⬝ᵥ (P *ᵥ x)) - d) - 2 * ((P *ᵥ x) ⬝ᵥ h) - h ⬝ᵥ (P *ᵥ h) := by
  rw [SS.LQProblem.quad_add hP, dotProduct_comm (P *ᵥ x) h]
  ring

/-- Verification with the side condition (Miao, p. 298, Hansen and Sargent): if `P` is a
symmetric solution of (9.12) with `G(P) > 0` and `β ≥ 0`, then along every deterministic path
`x_{t+1} = Ax_t + Bu_t`,
`∑_{t<s}βᵗr(x_t, u_t) = x₀'Px₀ − βˢx_s'Px_s + ∑_{t<s}βᵗ(u_t + Fx_t)'G(u_t + Fx_t)`; hence every
path with `βˢx_s'Px_s → 0` and summable losses costs at least `x₀'Px₀`, and (for a positive
semidefinite joint cost matrix) the rule `u_t = −Fx_t` costs exactly `x₀'Px₀` when its path
satisfies `βˢx_s'Px_s → 0`. -/
theorem ls_verification (hJ : L.JointPSD) (hR : L.Rᵀ = L.R) {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (hG : (L.G P).PosDef) (hβ : 0 ≤ L.β) (hfix : L.T P = P) {x : ℕ → X → ℝ}
    {u : ℕ → U → ℝ} (hx : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) :
    (∀ s, ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) + ∑ t ∈ Finset.range s, L.β ^ t *
        ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t)))) ∧
    (Tendsto (fun s => L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s))) atTop (𝓝 0) →
      Summable (fun t => L.β ^ t * L.loss (x t) (u t)) →
      x 0 ⬝ᵥ (P *ᵥ x 0) ≤ ∑' t, L.β ^ t * L.loss (x t) (u t)) ∧
    ((∀ t, u t = -(L.F P *ᵥ x t)) →
      Tendsto (fun s => L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s))) atTop (𝓝 0) →
      HasSum (fun t => L.β ^ t * L.loss (x t) (u t)) (x 0 ⬝ᵥ (P *ᵥ x 0))) := by
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  have hid : ∀ s, ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) + ∑ t ∈ Finset.range s, L.β ^ t *
        ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t))) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      have hsq := L.loss_add_cont hR hP hu (x s) (u s)
      rw [hfix, ← hx s] at hsq
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
      linear_combination L.β ^ s * hsq
  have hnn : ∀ t, 0 ≤ L.β ^ t * ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t))) :=
    fun t => mul_nonneg (pow_nonneg hβ t)
      ((SS.LQProblem.posSemidef_iff_real.1 hG.posSemidef).2 _)
  refine ⟨hid, fun hlim hs => ?_, fun hpol hlim => ?_⟩
  · have hle : ∀ s, x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) ≤
        ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) := fun s => by
      rw [hid s]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun t _ => hnn t)
    have h1 : Tendsto (fun s => x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s))) atTop
        (𝓝 (x 0 ⬝ᵥ (P *ᵥ x 0))) := by simpa using tendsto_const_nhds.sub hlim
    exact le_of_tendsto_of_tendsto' h1 hs.hasSum.tendsto_sum_nat hle
  · have hz : ∀ t, L.β ^ t * ((u t + L.F P *ᵥ x t) ⬝ᵥ (L.G P *ᵥ (u t + L.F P *ᵥ x t))) = 0 :=
      fun t => by rw [hpol t, neg_add_cancel, mulVec_zero, dotProduct_zero, mul_zero]
    have h2 : ∀ s, ∑ t ∈ Finset.range s, L.β ^ t * L.loss (x t) (u t) =
        x 0 ⬝ᵥ (P *ᵥ x 0) - L.β ^ s * (x s ⬝ᵥ (P *ᵥ x s)) := fun s => by
      rw [hid s, Finset.sum_eq_zero fun t _ => hz t, add_zero]
    have hlos : ∀ t, 0 ≤ L.β ^ t * L.loss (x t) (u t) := fun t =>
      mul_nonneg (pow_nonneg hβ t) (L.loss_nonneg hJ _ _)
    refine (hasSum_iff_tendsto_nat_of_nonneg hlos _).2 ?_
    simp only [h2]
    simpa using tendsto_const_nhds.sub hlim

end LSProblem

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 9.1 and 9.2

Miao, §9.7, p. 325.

* **Exercise 9.1** (`ex_9_1_loss`, `ex_9_1_transition`, `ex_9_1`): with
  `ũ_t = u_t + R⁻¹S'x_t` (the book prints `R⁻¹Sx_t`), `Q̃ = Q − SR⁻¹S'`, `Ã = A − BR⁻¹S'`, the
  problem becomes one with `S̃ = 0` (`normS`): the losses and transitions agree, the Riccati
  operators agree, `T̃ = T`, and the gains satisfy `F = F̃ + R⁻¹S'`. This is the normalisation
  `S = 0` used in §9.3 (p. 299).
* **Exercise 9.2** (`ex_9_2_transition`, `ex_9_2_loss`, `ex_9_2`): the uncentered problem, with
  loss the quadratic form of `[x_t − x*; u_t − u*]` in `[[Q, S], [S', R]]`, is the centered problem
  (`augment`) on the augmented state `z_t = [x_t − x*; 1]` with control `u_t − u*`; for `β < 1`
  and a positive semidefinite solution `P̃` of the augmented Riccati equation, the value function
  is `V(x) = −z'P̃z − d̃` and the optimal rule is `u = u* − F̃z`, uniquely.
-/

open Filter Topology Matrix MeasureTheory

namespace Miao.LinearQuadratic

namespace LSProblem

variable {X U E : Type*} [Fintype X] [Fintype U] [DecidableEq U] (L : LSProblem X U E)

/-! ### Exercise 9.1 -/

/-- The normalised problem of Exercise 9.1: `Ã = A − BR⁻¹S'`, `Q̃ = Q − SR⁻¹S'`, `S̃ = 0`. -/
noncomputable def normS : LSProblem X U E :=
  { L with A := L.A - L.B * (L.R⁻¹ * L.Sᵀ), Q := L.Q - L.S * (L.R⁻¹ * L.Sᵀ), S := 0 }

/-- **Exercise 9.1** (Miao, p. 325), the loss: `r(x, u) = x'Q̃x + ũ'Rũ` with `ũ = u + R⁻¹S'x`. -/
theorem ex_9_1_loss (hR : L.Rᵀ = L.R) (hu : IsUnit L.R.det) (x : X → ℝ) (u : U → ℝ) :
    L.loss x u = L.normS.loss x (u + (L.R⁻¹ * L.Sᵀ) *ᵥ x) := by
  set K := L.R⁻¹ * L.Sᵀ
  have hRK : L.R *ᵥ (K *ᵥ x) = L.Sᵀ *ᵥ x := by
    rw [mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := SS.LQProblem.quad_add hR u (K *ᵥ x)
  have e2 : (K *ᵥ x) ⬝ᵥ (L.R *ᵥ u) = u ⬝ᵥ (L.Sᵀ *ᵥ x) := by
    rw [SS.LQProblem.dotProduct_mulVec_comm_of_symm hR, hRK]
  have e3 : (K *ᵥ x) ⬝ᵥ (L.R *ᵥ (K *ᵥ x)) = x ⬝ᵥ ((L.S * K) *ᵥ x) := by
    rw [hRK, ← dot_S_comm L.S x (K *ᵥ x), mulVec_mulVec]
  have e4 := dot_S_comm L.S x u
  simp only [loss, normS, sub_mulVec, dotProduct_sub, zero_mulVec, dotProduct_zero, mul_zero,
    add_zero]
  rw [e1, e2, e3, e4]
  ring

omit [DecidableEq U] in
/-- **Exercise 9.1**, the transition: `Ax + Bu = Ãx + Bũ`. -/
theorem ex_9_1_transition [DecidableEq U] (x : X → ℝ) (u : U → ℝ) :
    L.A *ᵥ x + L.B *ᵥ u = L.normS.A *ᵥ x + L.normS.B *ᵥ (u + (L.R⁻¹ * L.Sᵀ) *ᵥ x) := by
  simp only [normS, sub_mulVec, mulVec_add, mulVec_mulVec]
  abel

/-- **Exercise 9.1**: the normalisation leaves the Riccati operator unchanged, `T̃(P) = T(P)`,
and shifts the gain, `F(P) = F̃(P) + R⁻¹S'` (so `u = −Fx` iff `ũ = −F̃x`). -/
theorem ex_9_1 (hQ : L.Qᵀ = L.Q) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) :
    L.normS.T P = L.T P ∧ L.F P = L.normS.F P + L.R⁻¹ * L.Sᵀ := by
  classical
  set K := L.R⁻¹ * L.Sᵀ
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hRu : IsUnit L.R.det := (isUnit_iff_isUnit_det _).1 hR.isUnit
  have hG := L.G_posDef hR hP hβ
  have hGe : L.normS.G P = L.G P := rfl
  have hu := (isUnit_iff_isUnit_det _).1 hG.isUnit
  have hq : ∀ v, 0 ≤ v ⬝ᵥ (L.G P *ᵥ v) := (SS.LQProblem.posSemidef_iff_real.1 hG.posSemidef).2
  -- the two completed squares
  have key : ∀ x u, x ⬝ᵥ (L.T P *ᵥ x) + (u + L.F P *ᵥ x) ⬝ᵥ (L.G P *ᵥ (u + L.F P *ᵥ x)) =
      x ⬝ᵥ (L.normS.T P *ᵥ x) + (u + K *ᵥ x + L.normS.F P *ᵥ x) ⬝ᵥ
        (L.G P *ᵥ (u + K *ᵥ x + L.normS.F P *ᵥ x)) := by
    intro x u
    rw [← L.loss_add_cont hRs hPs hu, ← hGe, ← L.normS.loss_add_cont hRs hPs hu,
      ← L.ex_9_1_loss hRs hRu, ← L.ex_9_1_transition]
    rfl
  have hle : ∀ x, x ⬝ᵥ (L.T P *ᵥ x) = x ⬝ᵥ (L.normS.T P *ᵥ x) ∧
      L.F P *ᵥ x = L.normS.F P *ᵥ x + K *ᵥ x := by
    intro x
    have h1 := key x (-(L.F P *ᵥ x))
    have h2 := key x (-(L.normS.F P *ᵥ x) - K *ᵥ x)
    rw [neg_add_cancel, mulVec_zero, dotProduct_zero, add_zero] at h1
    rw [show -(L.normS.F P *ᵥ x) - K *ᵥ x + K *ᵥ x + L.normS.F P *ᵥ x = 0 by abel,
      mulVec_zero, dotProduct_zero, add_zero] at h2
    have hq1 := hq (-(L.F P *ᵥ x) + K *ᵥ x + L.normS.F P *ᵥ x)
    have hq2 := hq (-(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x)
    have heq : x ⬝ᵥ (L.T P *ᵥ x) = x ⬝ᵥ (L.normS.T P *ᵥ x) := by linarith
    refine ⟨heq, ?_⟩
    have h0 : (-(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x) ⬝ᵥ
        (L.G P *ᵥ (-(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x)) = 0 := by linarith
    by_contra hne
    have hv : -(L.normS.F P *ᵥ x) - K *ᵥ x + L.F P *ᵥ x ≠ 0 := by
      intro h0'
      apply hne
      rw [← sub_eq_zero, ← h0']
      abel
    have := (SS.LQProblem.posDef_iff_real.1 hG).2 hv
    linarith
  have hQs : L.normS.Qᵀ = L.normS.Q := by
    simp only [normS, transpose_sub, transpose_mul, transpose_nonsing_inv, transpose_transpose,
      hQ, hRs, Matrix.mul_assoc]
  refine ⟨SS.LQProblem.eq_of_dotProduct_mulVec_eq (L.normS.T_transpose hQs hRs hPs)
    (L.T_transpose hQ hRs hPs) fun x => ((hle x).1).symm, ?_⟩
  ext i j
  have := congrFun ((hle (Pi.single j 1)).2) i
  simpa [mulVec_single_one] using this

/-! ### Exercise 9.2 -/

/-- The augmented problem of Exercise 9.2 on the state `z = [x − x*; 1]` with control `u − u*`:
`Ã = [[A, Ax* + Bu* − x*], [0, 1]]`, `B̃ = [B; 0]`, `C̃ = [C; 0]`, `Q̃ = [[Q, 0], [0, 0]]`,
`S̃ = [S; 0]`. -/
noncomputable def augment (xs : X → ℝ) (us : U → ℝ) : LSProblem (X ⊕ Unit) U E where
  A := fromBlocks L.A (Matrix.of fun i _ => (L.A *ᵥ xs + L.B *ᵥ us - xs) i) 0 1
  B := fromRows L.B 0
  C := fromRows L.C 0
  Q := fromBlocks L.Q 0 0 0
  R := L.R
  S := fromRows L.S 0
  β := L.β

/-- The augmented state `z = [x − x*; 1]`. -/
def ls_aug (xs x : X → ℝ) : X ⊕ Unit → ℝ := Sum.elim (x - xs) fun _ => 1

omit [DecidableEq U] in
/-- **Exercise 9.2** (Miao, p. 325): (9.57) in the augmented state,
`z_{t+1} = Ãz_t + B̃(u_t − u*) + C̃ε_{t+1}`. -/
theorem ex_9_2_transition [Fintype E] (xs : X → ℝ) (us : U → ℝ) (x : X → ℝ)
    (u : U → ℝ) (e : E → ℝ) :
    ls_aug xs (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) =
      (L.augment xs us).A *ᵥ ls_aug xs x + (L.augment xs us).B *ᵥ (u - us) +
        (L.augment xs us).C *ᵥ e := by
  funext i
  rcases i with i | i
  · simp only [augment, ls_aug, fromBlocks_mulVec, fromRows_mulVec, Pi.add_apply,
      Sum.elim_inl, Pi.sub_apply, mulVec_sub, Function.comp_def]
    simp only [mulVec, dotProduct, of_apply, Fintype.univ_unit, Finset.sum_singleton,
      Sum.elim_inr, mul_one]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · simp [augment, ls_aug, fromBlocks_mulVec, fromRows_mulVec, mulVec, dotProduct]

omit [DecidableEq U] in
/-- **Exercise 9.2**: the uncentered loss, the quadratic form of `[x − x*; u − u*]` in
`[[Q, S], [S', R]]`, is the centered loss of the augmented problem. -/
theorem ex_9_2_loss (xs : X → ℝ) (us : U → ℝ) (x : X → ℝ) (u : U → ℝ) :
    Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ Sum.elim (x - xs) (u - us)) =
      (L.augment xs us).loss (ls_aug xs x) (u - us) := by
  rw [L.quad_joint]
  simp only [loss, augment, ls_aug, fromBlocks_mulVec, fromRows_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, sumElim_dotProduct_sumElim, zero_mulVec, add_zero, dotProduct_zero]

/-- **Exercise 9.2**: for `0 ≤ β < 1`, if `P̃ ≥ 0` solves the augmented Riccati equation, then
`V(x) = −z'P̃z − d̃` (`z = [x − x*; 1]`, `d̃ = (1 − β)⁻¹β tr(P̃C̃C̃')`) solves the Bellman equation
of the uncentered problem, and the maximum is attained exactly at `u = u* − F̃z`. -/
theorem ex_9_2 [Fintype E] [DecidableEq E] {ν : Measure (E → ℝ)} (hν : LSShockLaw ν)
    (hR : L.R.PosDef) (hβ0 : 0 ≤ L.β) (hβ1 : L.β < 1) (xs : X → ℝ) (us : U → ℝ)
    {P : Matrix (X ⊕ Unit) (X ⊕ Unit) ℝ} (hP : P.PosSemidef) (hfix : (L.augment xs us).T P = P)
    (x : X → ℝ) :
    let d := (1 - L.β)⁻¹ * (L.β * trace (P * (L.augment xs us).C * (L.augment xs us).Cᵀ))
    let V := fun x' : X → ℝ => -(ls_aug xs x' ⬝ᵥ (P *ᵥ ls_aug xs x')) - d
    IsGreatest (Set.range fun u : U → ℝ =>
        -(Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ
          Sum.elim (x - xs) (u - us))) + L.β * ∫ e, V (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν)
        (V x) ∧
      ∀ u, -(Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ
          Sum.elim (x - xs) (u - us))) + L.β * ∫ e, V (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν =
          V x ↔ u = us - (L.augment xs us).F P *ᵥ ls_aug xs x := by
  intro d V
  set La := L.augment xs us
  have hobj : ∀ u : U → ℝ, -(Sum.elim (x - xs) (u - us) ⬝ᵥ (fromBlocks L.Q L.S L.Sᵀ L.R *ᵥ
      Sum.elim (x - xs) (u - us))) + L.β * ∫ e, V (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) ∂ν =
      La.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) (ls_aug xs x) (u - us) := by
    intro u
    rw [L.ex_9_2_loss, bellObj]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun e => ?_)
    simp only [V]
    rw [L.ex_9_2_transition xs us x u e]
  have h := La.eq_9_16_9_17 hν hR hβ0 hβ1 hP hfix (ls_aug xs x)
  simp only [hobj]
  have hsurj : Function.Surjective fun u : U → ℝ => u - us := fun v => ⟨v + us, by simp⟩
  refine ⟨?_, fun u => ?_⟩
  · have := hsurj.range_comp (La.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - d) (ls_aug xs x))
    simp only [Function.comp_def] at this
    rw [this]
    exact h.1
  · refine (h.2 (u - us)).trans ?_
    rw [sub_eq_iff_eq_add, neg_add_eq_sub]

end LSProblem

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 9.4: Hall's consumption problem

Miao, §9.7, Exercise 9.4, pp. 325–326: `max −E∑βᵗ(c_t − b)²` subject to
`c_t + a_{t+1} = Ra_t + y_t`, `y_{t+1} = μ(1 − ρ) + ρy_t + σε_{t+1}`, with state
`x_t = [1, a_t, y_t]'` and control `c_t` (`hallProblem`; `ex_9_4_loss`, `ex_9_4_transition`).
Here `S ≠ 0` and `Q − SR⁻¹S' = 0`, so Propositions 9.3.1–9.3.2 do not apply; we solve the
Riccati equation explicitly.

With `κ = βR² > 1` (true in Hall's case `βR = 1`, as `R > 1`), `q = 1 − 1/κ` and
`w = [μR/(R − 1) − μR/(R − ρ) − bR/(R − 1), R, R/(R − ρ)]`:

* `ex_9_4_riccati`: `P = q ww'` solves the Riccati equation (9.12), with gain
  `F = −(b e₁' + q w')`, i.e. the consumption rule (`ex_9_4_rule`)
  `c_t = b + q(Ra_t + Ry_t/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`;
  for `βR = 1` this is Hall's `c_t = (R − 1)a_t + μ + (R − 1)(y_t − μ)/(R − ρ)`
  (`ex_9_4_martingale`).
* `ex_9_4_optimal`: in the deterministic (certainty-equivalent) problem, every plan with
  `βᵗx_t'Px_t → 0` (for instance under the side condition (9.10)) has loss at least `x₀'Px₀`, and
  the rule attains `x₀'Px₀` (along it, `c_{t+1} − b = (βR)⁻¹(c_t − b)`).
* `ex_9_4_bellman`: with shocks, `V(x) = −x'Px − d` solves the Bellman equation and the rule is
  the unique maximiser (certainty equivalence).
* `ex_9_4_impatient`: for `βR² < 1`, `P = 0` solves (9.12) with rule `c_t = b`, which attains the
  infimum `0` of the loss (with debt growing at rate `R < 1/√β`, permitted by (9.10)).
-/

open Filter Topology Matrix MeasureTheory

namespace Miao.LinearQuadratic

/-- A positive semidefinite joint cost matrix from a nonnegative loss. -/
theorem ls_jointPSD_of_loss {X U E : Type*} [Fintype X] [Fintype U] (L : LSProblem X U E)
    (hQ : L.Qᵀ = L.Q) (hR : L.Rᵀ = L.R) (h : ∀ x u, 0 ≤ L.loss x u) : L.JointPSD := by
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun v => ?_⟩
  · rw [fromBlocks_transpose, hQ, hR, transpose_transpose]
  · have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) := by
      funext i; rcases i with i | i <;> rfl
    rw [hv, L.quad_joint]
    exact h _ _

/-- Hall's problem (Exercise 9.4) with state `x = [1, a, y]'`, control `c`, shock `ε`. -/
noncomputable def hallProblem (b μ Rr ρ σ β : ℝ) : LSProblem (Fin 3) (Fin 1) (Fin 1) where
  A := !![1, 0, 0; 0, Rr, 1; μ * (1 - ρ), 0, ρ]
  B := !![0; -1; 0]
  C := !![0; 0; σ]
  Q := !![b ^ 2, 0, 0; 0, 0, 0; 0, 0, 0]
  R := 1
  S := !![-b; 0; 0]
  β := β

variable (b μ Rr ρ σ β : ℝ)

/-- Exercise 9.4: the loss of `x = [1, a, y]'`, `c` is `(c − b)²`. -/
theorem ex_9_4_loss (a y c : ℝ) :
    (hallProblem b μ Rr ρ σ β).loss ![1, a, y] ![c] = (c - b) ^ 2 := by
  simp [LSProblem.loss, hallProblem, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Exercise 9.4: the transition `[1, a, y] ↦ [1, Ra + y − c, μ(1 − ρ) + ρy + σε]`. -/
theorem ex_9_4_transition (a y c e : ℝ) :
    (hallProblem b μ Rr ρ σ β).A *ᵥ ![1, a, y] + (hallProblem b μ Rr ρ σ β).B *ᵥ ![c] +
        (hallProblem b μ Rr ρ σ β).C *ᵥ ![e] =
      ![1, Rr * a + y - c, μ * (1 - ρ) + ρ * y + σ * e] := by
  funext i
  fin_cases i <;> simp [hallProblem] <;> ring

theorem ex_9_4_jointPSD : (hallProblem b μ Rr ρ σ β).JointPSD := by
  refine ls_jointPSD_of_loss _ ?_ ?_ fun x u => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hallProblem]
  · simp [hallProblem]
  · have : (hallProblem b μ Rr ρ σ β).loss x u = (u 0 - b * x 0) ^ 2 := by
      simp [LSProblem.loss, hallProblem, mulVec, dotProduct, Fin.sum_univ_three]
      ring
    rw [this]
    positivity

/-- `q = 1 − 1/(βR²)`. -/
noncomputable def hallq : ℝ := 1 - 1 / (β * Rr ^ 2)

/-- `w = [μR/(R − 1) − μR/(R − ρ) − bR/(R − 1), R, R/(R − ρ)]`. -/
noncomputable def hallW : Fin 3 → ℝ :=
  ![μ * Rr / (Rr - 1) - μ * Rr / (Rr - ρ) - b * Rr / (Rr - 1), Rr, Rr / (Rr - ρ)]

/-- The Riccati solution `P = q ww'`. -/
noncomputable def hallP : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => hallq Rr β * hallW b μ Rr ρ i * hallW b μ Rr ρ j

/-- The gain `F = −(b e₁' + q w')`. -/
noncomputable def hallF : Matrix (Fin 1) (Fin 3) ℝ :=
  Matrix.of fun _ j => -(![b, 0, 0] j + hallq Rr β * hallW b μ Rr ρ j)

variable {b μ Rr ρ σ β}

theorem hallP_quad (x : Fin 3 → ℝ) :
    x ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x) = hallq Rr β * (hallW b μ Rr ρ ⬝ᵥ x) ^ 2 := by
  simp only [hallP, dotProduct, mulVec, of_apply, Fin.sum_univ_three]
  ring

/-- **Exercise 9.4** (Miao, p. 325): for `β > 0`, `R > 1` and `|ρ| < 1`, `P = q ww'` solves
the Riccati equation (9.12) and the gain (9.17) is `F = −(b e₁' + q w')`. -/
theorem ex_9_4_riccati (hβ : 0 < β) (hR1 : 1 < Rr) (hρ : |ρ| < 1) :
    (hallProblem b μ Rr ρ σ β).T (hallP b μ Rr ρ β) = hallP b μ Rr ρ β ∧
      (hallProblem b μ Rr ρ σ β).F (hallP b μ Rr ρ β) = hallF b μ Rr ρ β ∧
      ((hallProblem b μ Rr ρ σ β).G (hallP b μ Rr ρ β)).PosDef := by
  set L := hallProblem b μ Rr ρ σ β
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hκ0 : β * Rr ^ 2 ≠ 0 := by positivity
  have hRr : Rr ≠ 0 := by linarith
  have hGe : L.G (hallP b μ Rr ρ β) = !![β * Rr ^ 2] := by
    ext i j
    fin_cases i; fin_cases j
    simp [L, LSProblem.G, hallProblem, hallP, hallq, hallW, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
    ring
  have hGpd : (L.G (hallP b μ Rr ρ β)).PosDef := by
    rw [hGe]
    refine SS.LQProblem.posDef_iff_real.2 ⟨by ext i j; fin_cases i; fin_cases j; rfl,
      fun v hv => ?_⟩
    have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i; exact h0)
    simp only [dotProduct, mulVec, Fin.sum_univ_one, of_apply, cons_val', cons_val_fin_one,
      empty_val']
    have : 0 < v 0 * v 0 := mul_self_pos.2 hv0
    nlinarith [mul_pos (by positivity : 0 < β * Rr ^ 2) this]
  have hu := (isUnit_iff_isUnit_det _).1 hGpd.isUnit
  have hGF : L.G (hallP b μ Rr ρ β) * hallF b μ Rr ρ β = L.N (hallP b μ Rr ρ β) := by
    rw [hGe]
    ext i j
    fin_cases i; fin_cases j <;>
      simp [L, LSProblem.N, hallProblem, hallP, hallF, hallq, hallW, Matrix.mul_apply,
        Fin.sum_univ_three] <;> field_simp <;> ring
  have hF : L.F (hallP b μ Rr ρ β) = hallF b μ Rr ρ β := by
    rw [LSProblem.F, ← hGF, nonsing_inv_mul_cancel_left _ _ hu]
  refine ⟨?_, hF, hGpd⟩
  rw [LSProblem.T_eq_sub, hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L, hallProblem, hallP, hallF, hallq, hallW, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- **Exercise 9.4**, the consumption rule `c = −Fx` at `x = [1, a, y]'`:
`c = b + q(Ra + Ry/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`. -/
theorem ex_9_4_rule (a y : ℝ) :
    (-(hallF b μ Rr ρ β *ᵥ ![1, a, y])) 0 = b + hallq Rr β *
      (Rr * a + Rr * y / (Rr - ρ) + μ * Rr / (Rr - 1) - μ * Rr / (Rr - ρ) -
        b * Rr / (Rr - 1)) := by
  simp [hallF, hallW, vecHead, vecTail]
  ring

/-- **Exercise 9.4**, Hall's case `βR = 1`: `c_t = (R − 1)a_t + μ + (R − 1)(y_t − μ)/(R − ρ)`;
consumption is a martingale (`ex_9_4_closed_loop`). -/
theorem ex_9_4_martingale (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hβR : β * Rr = 1) (a y : ℝ) :
    (-(hallF b μ Rr ρ β *ᵥ ![1, a, y])) 0 = (Rr - 1) * a + μ + (Rr - 1) * (y - μ) / (Rr - ρ) := by
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hRr : Rr ≠ 0 := by linarith
  have hβ : β = 1 / Rr := by field_simp; linarith
  rw [ex_9_4_rule, hallq, hβ]
  field_simp
  ring

/-- **Exercise 9.4**: along the rule, `w'x_{t+1} = (βR)⁻¹w'x_t`, i.e.
`c_{t+1} − b = (βR)⁻¹(c_t − b)` (the Euler equation). -/
theorem ex_9_4_closed_loop (hβ : 0 < β) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (x : Fin 3 → ℝ) :
    hallW b μ Rr ρ ⬝ᵥ (((hallProblem b μ Rr ρ σ β).A - (hallProblem b μ Rr ρ σ β).B *
      hallF b μ Rr ρ β) *ᵥ x) = (β * Rr)⁻¹ * (hallW b μ Rr ρ ⬝ᵥ x) := by
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hRr : Rr ≠ 0 := by linarith
  have hβ0 : β ≠ 0 := hβ.ne'
  simp [hallProblem, hallF, hallW, hallq, mulVec, dotProduct, Fin.sum_univ_three]
  field_simp
  ring

/-- **Exercise 9.4**, optimality in the deterministic problem (`ε = 0`): for `βR² > 1`, every plan
`x_{t+1} = Ax_t + Bc_t` with `βᵗx_t'Px_t → 0` and summable losses has
`∑βᵗ(c_t − b)² ≥ x₀'Px₀`, and the rule `c_t = −Fx_t` attains `x₀'Px₀`. -/
theorem ex_9_4_optimal (hβ : 0 < β) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) :
    (∀ (x : ℕ → Fin 3 → ℝ) (c : ℕ → Fin 1 → ℝ),
      (∀ t, x (t + 1) = (hallProblem b μ Rr ρ σ β).A *ᵥ x t +
        (hallProblem b μ Rr ρ σ β).B *ᵥ c t) →
      Tendsto (fun s => β ^ s * (x s ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x s))) atTop (𝓝 0) →
      Summable (fun t => β ^ t * (hallProblem b μ Rr ρ σ β).loss (x t) (c t)) →
      x 0 ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x 0) ≤
        ∑' t, β ^ t * (hallProblem b μ Rr ρ σ β).loss (x t) (c t)) ∧
    ∀ x : ℕ → Fin 3 → ℝ, (∀ t, x (t + 1) = ((hallProblem b μ Rr ρ σ β).A -
        (hallProblem b μ Rr ρ σ β).B * hallF b μ Rr ρ β) *ᵥ x t) →
      HasSum (fun t => β ^ t * (hallProblem b μ Rr ρ σ β).loss (x t)
        (-(hallF b μ Rr ρ β *ᵥ x t))) (x 0 ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x 0)) := by
  set L := hallProblem b μ Rr ρ σ β
  obtain ⟨hfix, hF, hG⟩ := ex_9_4_riccati (σ := σ) hβ hR1 hρ
  have hPs : (hallP b μ Rr ρ β)ᵀ = hallP b μ Rr ρ β := by
    ext i j
    simp only [hallP, transpose_apply, of_apply]
    ring
  have hRs : L.Rᵀ = L.R := by simp [L, hallProblem]
  have hJ := ex_9_4_jointPSD b μ Rr ρ σ β
  refine ⟨fun x c hx hlim hs => ?_, fun x hx => ?_⟩
  · exact (L.ls_verification hJ hRs hPs hG hβ.le hfix hx).2.1 hlim hs
  · have hx' : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ (-(hallF b μ Rr ρ β *ᵥ x t)) := fun t => by
      rw [hx, sub_mulVec, mulVec_neg, ← mulVec_mulVec, sub_eq_add_neg]
    have hw : ∀ t, hallW b μ Rr ρ ⬝ᵥ x t = (β * Rr)⁻¹ ^ t * (hallW b μ Rr ρ ⬝ᵥ x 0) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [hx, ex_9_4_closed_loop hβ hR1 hρ, ih, pow_succ]; ring
    have hlim : Tendsto (fun s => β ^ s * (x s ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x s))) atTop (𝓝 0) := by
      have hr0 : 0 ≤ (β * Rr ^ 2)⁻¹ := by positivity
      have hr1 : (β * Rr ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hκ
      have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const
        (hallq Rr β * (hallW b μ Rr ρ ⬝ᵥ x 0) ^ 2)
      rw [zero_mul] at h0
      refine h0.congr fun s => ?_
      rw [hallP_quad, hw s]
      have hRr : Rr ≠ 0 := by linarith
      have hβ0 : β ≠ 0 := hβ.ne'
      have hb : (β * Rr ^ 2)⁻¹ = β * ((β * Rr)⁻¹) ^ 2 := by field_simp
      rw [hb, mul_pow, ← pow_mul, pow_mul']
      ring
    exact (L.ls_verification hJ hRs hPs hG hβ.le hfix hx').2.2 (fun t => by rw [hF]) hlim

/-- **Exercise 9.4** with shocks (certainty equivalence): for `0 < β < 1` and `βR² > 1`,
`V(x) = −x'Px − d`, `d = (1 − β)⁻¹β tr(PCC')`, solves the Bellman equation, and the rule
`c = −Fx` is the unique maximiser. -/
theorem ex_9_4_bellman {ν : Measure (Fin 1 → ℝ)} (hν : LSShockLaw ν) (hβ : 0 < β)
    (hβ1 : β < 1) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) (x : Fin 3 → ℝ) :
    IsGreatest (Set.range ((hallProblem b μ Rr ρ σ β).bellObj ν
        (fun z => -(z ⬝ᵥ (hallP b μ Rr ρ β *ᵥ z)) - (1 - β)⁻¹ *
          (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
            (hallProblem b μ Rr ρ σ β).Cᵀ))) x))
        (-(x ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x)) - (1 - β)⁻¹ *
          (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
            (hallProblem b μ Rr ρ σ β).Cᵀ))) ∧
      ∀ u, (hallProblem b μ Rr ρ σ β).bellObj ν
          (fun z => -(z ⬝ᵥ (hallP b μ Rr ρ β *ᵥ z)) - (1 - β)⁻¹ *
            (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
              (hallProblem b μ Rr ρ σ β).Cᵀ))) x u =
          -(x ⬝ᵥ (hallP b μ Rr ρ β *ᵥ x)) - (1 - β)⁻¹ *
            (β * trace (hallP b μ Rr ρ β * (hallProblem b μ Rr ρ σ β).C *
              (hallProblem b μ Rr ρ σ β).Cᵀ)) ↔ u = -(hallF b μ Rr ρ β *ᵥ x) := by
  obtain ⟨hfix, hF, -⟩ := ex_9_4_riccati (σ := σ) hβ hR1 hρ
  have hq : 0 < hallq Rr β := by
    rw [hallq, sub_pos, div_lt_one (by positivity)]
    exact hκ
  have hP : (hallP b μ Rr ρ β).PosSemidef := by
    refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun v => ?_⟩
    · ext i j
      simp only [hallP, transpose_apply, of_apply]
      ring
    · rw [hallP_quad]
      positivity
  have hR : (hallProblem b μ Rr ρ σ β).R.PosDef := by
    simpa [hallProblem] using (PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef)
  have h := (hallProblem b μ Rr ρ σ β).eq_9_16_9_17 hν hR hβ.le hβ1 hP hfix x
  rw [hF] at h
  exact h

/-- **Exercise 9.4**, a second solution: `P = 0` always solves (9.12) for Hall's problem, with
rule `c = b` (the loss `0` is then attained, financed by debt growing at rate `R`, which the
side condition (9.10) permits iff `βR² < 1`). So for `βR² > 1` the Riccati equation has two
positive semidefinite solutions (`Q − SR⁻¹S' = 0`, so the detectability of Proposition 9.3.2
fails), and the side condition selects `P = q ww'`. -/
theorem ex_9_4_zero_solution (a y : ℝ) :
    (hallProblem b μ Rr ρ σ β).T 0 = 0 ∧
      (-((hallProblem b μ Rr ρ σ β).F 0 *ᵥ ![1, a, y])) 0 = b := by
  have hG : (hallProblem b μ Rr ρ σ β).G 0 = 1 := by simp [LSProblem.G, hallProblem]
  refine ⟨?_, ?_⟩
  · rw [LSProblem.T, hG, inv_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hallProblem, LSProblem.N, vecMul, dotProduct]
    all_goals ring
  · rw [LSProblem.F, hG, inv_one, Matrix.one_mul]
    simp [hallProblem, LSProblem.N, mulVec, dotProduct, Fin.sum_univ_three]

/-- For `βR² > 1` the two solutions differ: `P = q ww' ≠ 0`. -/
theorem ex_9_4_two_solutions (hβ : 0 < β) (hR1 : 1 < Rr) (hκ : 1 < β * Rr ^ 2) :
    hallP b μ Rr ρ β ≠ 0 := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  have hq : 0 < hallq Rr β := by
    rw [hallq, sub_pos, div_lt_one (by positivity)]
    exact hκ
  have hRr : Rr ≠ 0 := by linarith
  have h11' : hallP b μ Rr ρ β 1 1 = hallq Rr β * Rr * Rr := by simp [hallP, hallW]
  rw [h11'] at h11
  exact mul_ne_zero (mul_ne_zero hq.ne' hRr) hRr h11

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policy under commitment: the Ramsey problem and its first-order conditions

Miao, §9.4, pp. 304–307. The equilibrium system (9.18) is
`D[z_{t+1}; E_t y_{t+1}] = A[z_t; y_t] + Bu_t + [Cε_{t+1}; 0]` with `D = [I 0; D₂₁ D₂₂]`, the
period loss is (9.19), and the policymaker minimises `E∑ βᵗL_t` once and for all at date `0`.

**Representation.** The predetermined variables `z_t`, the forward-looking variables `y_t` and
the instruments `u_t` are indexed by arbitrary finite types `Z`, `Y`, `U`; the state
`(z_t, y_t)` is a vector on `Z ⊕ Y` and the augmented vector `x_t = (z_t, y_t, u_t)` a vector on
`(Z ⊕ Y) ⊕ U`. The augmented matrices are `D̄ = [D 0]` (`cpDbar`), `Ā = [A B]` (`cpAbar`) and
`W = [Q S; S' R]` (`cpW`).

* `eq_9_19_W` (p. 306): `L_t = ½x_t'Wx_t`; `cp_augmented` (p. 306): the augmented system is
  `D̄x_{t+1} = Āx_t + [Cε_{t+1}; 0]`.
* The Lagrangian (p. 306), truncated at a horizon `T` and with the shocks and expectations
  replaced by a given (perfect-foresight) path: `cpLagrangian`, with the multiplier term
  `β^{t+1}μ_{t+1}'(D̄x_{t+1} − Āx_t − c_{t+1})` and the initial term `μ_{z0}'(z₀ − z̄₀)`.
  `cp_lagrangian_perturb` computes it exactly along a perturbation `x_s ↦ x_s + εh` of one
  date `s < T`: it changes by `εβˢ g_s·h + ε²βˢ½h'Wh`, where `g_s` (`cpGrad`) is
  `Wx_s + D̄'μ_s − βĀ'μ_{s+1}` (for `s = 0`, `D̄'μ_0` is replaced by `(μ_{z0}, 0, 0)`).
  `cp_hasDerivAt` is the derivative, and `eq_foc_9_4` the first-order conditions: the
  Lagrangian is stationary in `x_s` iff `g_s = 0`. `cp_init_eq_Dbar` shows that with
  `μ_{y0} = 0` and `D = [I 0; D₂₁ D₂₂]` the date-`0` condition has the same form
  `Wx₀ + D̄'μ₀ − βĀ'μ₁ = 0` (`cp_grad_eq`), as the book writes it.
* `eq_9_22` (p. 307): the first-order conditions together with (9.18) are the stacked system
  `[D̄ 0; 0 βĀ'][x_{t+1}; μ_{t+1}] = [Ā 0; W D̄'][x_t; μ_t] + [c_{t+1}; 0]`.

**Departures.** The book's first-order conditions contain `E_t μ_{t+1}`; the conditioning step
(the multiplier enters linearly) is not formalised, so the Lagrangian is written along one
realised path (perfect foresight), as in `LQKlein`. The book writes the initial term as
`μ_{z0}'D̄(z₀ − z̄₀)`, which is not dimensionally consistent; we use `μ_{z0}'(z₀ − z̄₀)`, which
is what the book's date-`0` first-order condition uses (`cp_init_eq_Dbar`). The garbled printed
`D̄` is read as `[D 0]`, the only reading consistent with (9.22).
-/

namespace Miao.LinearQuadratic

open scoped Matrix

/-! ### Dot products -/

/-- The dot product of two vectors on a sum type. -/
theorem cp_sumElim_dotProduct {α β : Type*} [Fintype α] [Fintype β] (a c : α → ℝ)
    (b d : β → ℝ) : Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- `v'Mw = w'M'v`. -/
theorem cp_dotProduct_mulVec_comm {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℝ)
    (v : α → ℝ) (w : β → ℝ) : v ⬝ᵥ (M *ᵥ w) = w ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- For symmetric `M`, `v'Mw = (Mv)·w`. -/
theorem cp_dotProduct_mulVec_symm {α : Type*} [Fintype α] {M : Matrix α α ℝ} (hM : Mᵀ = M)
    (v w : α → ℝ) : v ⬝ᵥ (M *ᵥ w) = (M *ᵥ v) ⬝ᵥ w := by
  rw [cp_dotProduct_mulVec_comm, hM, dotProduct_comm]

variable {Z Y U : Type*} [Fintype Z] [Fintype Y] [Fintype U]

/-! ### The loss function and the augmented system -/

/-- The period loss (9.19) (Miao, p. 304):
`L = ½[z; y]'Q[z; y] + ½u'Ru + [z; y]'Su`. -/
noncomputable def cpLoss (Q : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (S : Matrix (Z ⊕ Y) U ℝ) (R : Matrix U U ℝ)
    (s : Z ⊕ Y → ℝ) (u : U → ℝ) : ℝ :=
  (1 / 2) * (s ⬝ᵥ (Q *ᵥ s)) + (1 / 2) * (u ⬝ᵥ (R *ᵥ u)) + s ⬝ᵥ (S *ᵥ u)

/-- The weighting matrix `W = [Q S; S' R]` (Miao, p. 306). -/
def cpW (Q : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (S : Matrix (Z ⊕ Y) U ℝ) (R : Matrix U U ℝ) :
    Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ :=
  Matrix.fromBlocks Q S Sᵀ R

/-- `D̄ = [D 0]` (Miao, p. 306). -/
def cpDbar (U : Type*) (D : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ :=
  Matrix.fromCols D 0

/-- `Ā = [A B]` (Miao, p. 306). -/
def cpAbar (A : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (B : Matrix (Z ⊕ Y) U ℝ) :
    Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ :=
  Matrix.fromCols A B

/-- Miao, p. 306: the period loss (9.19) is `L_t = ½[z_t; y_t; u_t]'W[z_t; y_t; u_t]`. -/
theorem eq_9_19_W (Q : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (S : Matrix (Z ⊕ Y) U ℝ)
    (R : Matrix U U ℝ) (s : Z ⊕ Y → ℝ) (u : U → ℝ) :
    cpLoss Q S R s u = (1 / 2) * (Sum.elim s u ⬝ᵥ (cpW Q S R *ᵥ Sum.elim s u)) := by
  simp only [cpLoss, cpW, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    cp_sumElim_dotProduct, dotProduct_add]
  rw [cp_dotProduct_mulVec_comm Sᵀ u s, Matrix.transpose_transpose]
  ring

/-- Miao, p. 306: appending the instruments, (9.18) reads `D̄x_{t+1} = Āx_t + [Cε_{t+1}; 0]`
with `x_t = (z_t, y_t, u_t)`: `D̄x = D[z; y]` and `Āx = A[z; y] + Bu`. -/
theorem cp_augmented (D A : Matrix (Z ⊕ Y) (Z ⊕ Y) ℝ) (B : Matrix (Z ⊕ Y) U ℝ)
    (s : Z ⊕ Y → ℝ) (u : U → ℝ) :
    cpDbar U D *ᵥ Sum.elim s u = D *ᵥ s ∧ cpAbar A B *ᵥ Sum.elim s u = A *ᵥ s + B *ᵥ u := by
  refine ⟨?_, ?_⟩
  · rw [cpDbar, Matrix.fromCols_mulVec_sumElim, Matrix.zero_mulVec, add_zero]
  · rw [cpAbar, Matrix.fromCols_mulVec_sumElim]

/-! ### The Lagrangian and the first-order conditions -/

/-- The Lagrangian of the Ramsey problem (Miao, p. 306), truncated at horizon `T`, along a
given path: `∑_{t<T} βᵗ[½x_t'Wx_t + βμ_{t+1}'(D̄x_{t+1} − Āx_t − c_{t+1})] + μ_{z0}'(z₀ − z̄₀)`,
where `c_{t+1} = [Cε_{t+1}; 0]` and `β^{t+1}μ_{t+1}` is the multiplier on (9.18) at date `t`. -/
noncomputable def cpLagrangian (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) (T : ℕ) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * ((1 / 2) * (x t ⬝ᵥ (W *ᵥ x t)) +
      β * (μ (t + 1) ⬝ᵥ (Dbar *ᵥ x (t + 1) - Abar *ᵥ x t - c (t + 1)))) +
    (fun i => μ 0 (Sum.inl i)) ⬝ᵥ (fun i => x 0 (Sum.inl (Sum.inl i)) - zbar i)

/-- The path `x` with `x_s` perturbed to `x_s + εh`. -/
def cpPerturb (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) (s : ℕ) (h : (Z ⊕ Y) ⊕ U → ℝ) (ε : ℝ) :
    ℕ → (Z ⊕ Y) ⊕ U → ℝ :=
  fun t => x t + (if t = s then ε else 0) • h

/-- The vector `(μ_{z0}, 0, 0)`: the derivative of the initial term `μ_{z0}'(z₀ − z̄₀)`. -/
def cpInit (μ0 : Z ⊕ Y → ℝ) : (Z ⊕ Y) ⊕ U → ℝ :=
  Sum.elim (Sum.elim (fun i => μ0 (Sum.inl i)) 0) 0

/-- The gradient of the Lagrangian in `x_s` (divided by `βˢ`):
`g_s = Wx_s + D̄'μ_s − βĀ'μ_{s+1}`, with `D̄'μ_0` replaced by `(μ_{z0}, 0, 0)` at `s = 0`. -/
def cpGrad (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (μ : ℕ → Z ⊕ Y → ℝ)
    (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) (s : ℕ) : (Z ⊕ Y) ⊕ U → ℝ :=
  W *ᵥ x s + (if s = 0 then cpInit (μ 0) else Dbarᵀ *ᵥ μ s) - β • (Abarᵀ *ᵥ μ (s + 1))

/-- One date-`t` term of the Lagrangian when `x_t` moves by `a h` and `x_{t+1}` by `b h`. -/
theorem cp_lagr_term {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c' m : Z ⊕ Y → ℝ)
    (x x' h : (Z ⊕ Y) ⊕ U → ℝ) (a b : ℝ) (t : ℕ) :
    β ^ t * ((1 / 2) * ((x + a • h) ⬝ᵥ (W *ᵥ (x + a • h))) +
      β * (m ⬝ᵥ (Dbar *ᵥ (x' + b • h) - Abar *ᵥ (x + a • h) - c'))) =
    β ^ t * ((1 / 2) * (x ⬝ᵥ (W *ᵥ x)) + β * (m ⬝ᵥ (Dbar *ᵥ x' - Abar *ᵥ x - c'))) +
      a * (β ^ t * ((W *ᵥ x) ⬝ᵥ h - β * (m ⬝ᵥ (Abar *ᵥ h)))) +
      a ^ 2 * (β ^ t * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) +
      b * (β ^ (t + 1) * (m ⬝ᵥ (Dbar *ᵥ h))) := by
  have h1 := cp_dotProduct_mulVec_symm hW x h
  have h2 : h ⬝ᵥ (W *ᵥ x) = (W *ᵥ x) ⬝ᵥ h := dotProduct_comm _ _
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, dotProduct_sub, h1, h2]
  ring

/-- Miao, p. 306: the Lagrangian along the perturbation `x_s ↦ x_s + εh` (`s < T`, `W`
symmetric) is exactly `ℒ + εβˢ g_s·h + ε²βˢ½h'Wh`. -/
theorem cp_lagrangian_perturb {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) {T s : ℕ} (hs : s < T) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ)
    (h : (Z ⊕ Y) ⊕ U → ℝ) (ε : ℝ) :
    cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε) =
      cpLagrangian W Dbar Abar β c μ zbar T x +
        ε * (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h)) +
        ε ^ 2 * (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) := by
  set δ : ℕ → ℝ := fun t => if t = s then ε else 0 with hδ
  have hterm := fun t => cp_lagr_term hW Dbar Abar β (c (t + 1)) (μ (t + 1)) (x t) (x (t + 1))
    h (δ t) (δ (t + 1)) t
  have hinit : (fun i => μ 0 (Sum.inl i)) ⬝ᵥ
      (fun i => cpPerturb x s h ε 0 (Sum.inl (Sum.inl i)) - zbar i) =
      (fun i => μ 0 (Sum.inl i)) ⬝ᵥ (fun i => x 0 (Sum.inl (Sum.inl i)) - zbar i) +
        δ 0 * (cpInit (μ 0) ⬝ᵥ h) := by
    simp only [cpPerturb, cpInit, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      add_zero, Finset.mul_sum, ← Finset.sum_add_distrib, δ]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsum1 : ∑ t ∈ Finset.range T, δ t * (β ^ t * ((W *ᵥ x t) ⬝ᵥ h -
      β * (μ (t + 1) ⬝ᵥ (Abar *ᵥ h)))) =
      ε * (β ^ s * ((W *ᵥ x s) ⬝ᵥ h - β * (μ (s + 1) ⬝ᵥ (Abar *ᵥ h)))) := by
    simp only [δ, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_range, hs, ↓reduceIte]
  have hsum2 : ∑ t ∈ Finset.range T, δ t ^ 2 * (β ^ t * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) =
      ε ^ 2 * (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) := by
    simp only [δ, ite_pow, ite_mul, zero_pow two_ne_zero, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_range, hs, ↓reduceIte]
  have hsum3 : ∑ t ∈ Finset.range T, δ (t + 1) * (β ^ (t + 1) * (μ (t + 1) ⬝ᵥ (Dbar *ᵥ h))) =
      if s = 0 then 0 else ε * (β ^ s * (μ s ⬝ᵥ (Dbar *ᵥ h))) := by
    rcases Nat.eq_zero_or_eq_succ_pred s with h0 | h0
    · simp only [δ, h0, Nat.add_one_ne_zero, ↓reduceIte, zero_mul, Finset.sum_const_zero]
    · have hne : s ≠ 0 := by omega
      have hr : s - 1 < T := by omega
      have hiff : ∀ t, (t + 1 = s) ↔ (t = s - 1) := fun t => by omega
      simp only [δ, hiff, ite_mul, zero_mul, hne, ↓reduceIte]
      simp only [Finset.sum_ite_eq', Finset.mem_range, hr, ↓reduceIte,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hne)]
  have hP : cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε) =
      ∑ t ∈ Finset.range T, β ^ t * ((1 / 2) * ((x t + δ t • h) ⬝ᵥ (W *ᵥ (x t + δ t • h))) +
        β * (μ (t + 1) ⬝ᵥ (Dbar *ᵥ (x (t + 1) + δ (t + 1) • h) - Abar *ᵥ (x t + δ t • h) -
          c (t + 1)))) +
      (fun i => μ 0 (Sum.inl i)) ⬝ᵥ
        (fun i => cpPerturb x s h ε 0 (Sum.inl (Sum.inl i)) - zbar i) := rfl
  rw [hP, hinit, Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hsum1, hsum2, hsum3]
  simp only [cpLagrangian, cpGrad]
  have e1 : (Dbarᵀ *ᵥ μ s) ⬝ᵥ h = μ s ⬝ᵥ (Dbar *ᵥ h) := by
    rw [cp_dotProduct_mulVec_comm, dotProduct_comm]
  have e2 : (Abarᵀ *ᵥ μ (s + 1)) ⬝ᵥ h = μ (s + 1) ⬝ᵥ (Abar *ᵥ h) := by
    rw [cp_dotProduct_mulVec_comm, dotProduct_comm]
  by_cases h0 : s = 0
  · subst h0
    simp only [δ, ↓reduceIte, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul, e2,
      pow_zero]
    ring
  · have h0' : ¬ (0 = s) := fun h => h0 h.symm
    simp only [δ, h0, h0', ↓reduceIte, add_dotProduct, sub_dotProduct, smul_dotProduct,
      smul_eq_mul, e1, e2, zero_mul, add_zero]
    ring

/-- Miao, p. 306: the derivative of the Lagrangian in the direction `h` of `x_s` (`s < T`) is
`βˢ g_s·h`. -/
theorem cp_hasDerivAt {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) {T s : ℕ} (hs : s < T) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ)
    (h : (Z ⊕ Y) ⊕ U → ℝ) :
    HasDerivAt (fun ε => cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε))
      (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h)) 0 := by
  have := (((hasDerivAt_id (0 : ℝ)).mul_const (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h))).const_add
    (cpLagrangian W Dbar Abar β c μ zbar T x)).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))))
  have hf : (fun ε => cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε)) =
      (fun ε => cpLagrangian W Dbar Abar β c μ zbar T x +
        id ε * (β ^ s * (cpGrad W Dbar Abar β μ x s ⬝ᵥ h))) +
      fun ε => ε ^ 2 * (β ^ s * ((1 / 2) * (h ⬝ᵥ (W *ᵥ h)))) := by
    funext ε
    rw [cp_lagrangian_perturb hW Dbar Abar β c μ zbar hs x h, Pi.add_apply, id]
  rw [hf]
  convert this using 1
  simp

/-- **First-order conditions** (Miao, p. 306). For `β ≠ 0`, symmetric `W` and `s < T`, the
Lagrangian is stationary in `x_s` (zero derivative in every direction) iff
`Wx_s + D̄'μ_s − βĀ'μ_{s+1} = 0` (with `(μ_{z0}, 0, 0)` for `D̄'μ_0` at `s = 0`). -/
theorem eq_foc_9_4 {W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ} (hW : Wᵀ = W)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) {β : ℝ} (hβ : β ≠ 0) (c μ : ℕ → Z ⊕ Y → ℝ)
    (zbar : Z → ℝ) {T s : ℕ} (hs : s < T) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) :
    (∀ h, HasDerivAt (fun ε => cpLagrangian W Dbar Abar β c μ zbar T (cpPerturb x s h ε)) 0 0) ↔
      cpGrad W Dbar Abar β μ x s = 0 := by
  constructor
  · intro H
    have h1 := (cp_hasDerivAt hW Dbar Abar β c μ zbar hs x (cpGrad W Dbar Abar β μ x s)).unique
      (H _)
    have h2 : cpGrad W Dbar Abar β μ x s ⬝ᵥ cpGrad W Dbar Abar β μ x s = 0 := by
      rcases mul_eq_zero.1 h1 with h3 | h3
      · exact absurd h3 (pow_ne_zero _ hβ)
      · exact h3
    exact dotProduct_self_eq_zero.1 h2
  · intro H h
    have := cp_hasDerivAt hW Dbar Abar β c μ zbar hs x h
    rwa [H, zero_dotProduct, mul_zero] at this

omit [Fintype U] in
/-- Miao, p. 307: if `D = [I 0; D₂₁ D₂₂]` and `μ_{y0} = 0` ("no past promises"), then
`(μ_{z0}, 0, 0) = D̄'μ₀`. -/
theorem cp_init_eq_Dbar [DecidableEq Z] (D21 : Matrix Y Z ℝ) (D22 : Matrix Y Y ℝ)
    (μ0 : Z ⊕ Y → ℝ) (hμ : ∀ i, μ0 (Sum.inr i) = 0) :
    cpInit (U := U) μ0 = (cpDbar U (Matrix.fromBlocks 1 0 D21 D22))ᵀ *ᵥ μ0 := by
  have hμ' : μ0 = Sum.elim (fun i => μ0 (Sum.inl i)) 0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact hμ i
  rw [cpDbar, Matrix.transpose_fromCols, Matrix.fromRows_mulVec, Matrix.fromBlocks_transpose]
  conv_rhs => rw [hμ']
  rw [Matrix.fromBlocks_mulVec]
  simp only [cpInit, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.transpose_one,
    Matrix.one_mulVec, Matrix.mulVec_zero, add_zero, Matrix.transpose_zero, Matrix.zero_mulVec]

/-- **First-order conditions with respect to `z_t, y_t, u_t`** (Miao, p. 306). With
`D = [I 0; D₂₁ D₂₂]` and `μ_{y0} = 0`, the gradient is `Wx_s + D̄'μ_s − βĀ'μ_{s+1}` at every
date `s ≥ 0`, including `s = 0`. -/
theorem cp_grad_eq [DecidableEq Z] (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (D21 : Matrix Y Z ℝ) (D22 : Matrix Y Y ℝ) (Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ)
    (μ : ℕ → Z ⊕ Y → ℝ) (hμ : ∀ i, μ 0 (Sum.inr i) = 0) (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) (s : ℕ) :
    cpGrad W (cpDbar U (Matrix.fromBlocks 1 0 D21 D22)) Abar β μ x s =
      W *ᵥ x s + (cpDbar U (Matrix.fromBlocks 1 0 D21 D22))ᵀ *ᵥ μ s - β • (Abarᵀ *ᵥ μ (s + 1)) := by
  rw [cpGrad]
  by_cases h0 : s = 0
  · subst h0
    simp only [↓reduceIte, cp_init_eq_Dbar D21 D22 (μ 0) hμ]
  · simp only [h0, ↓reduceIte]

/-! ### The stacked system (9.22) -/

/-- The left matrix of (9.22): `[D̄ 0; 0 βĀ']`. -/
def cpLeft (β : ℝ) (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) :
    Matrix ((Z ⊕ Y) ⊕ ((Z ⊕ Y) ⊕ U)) (((Z ⊕ Y) ⊕ U) ⊕ (Z ⊕ Y)) ℝ :=
  Matrix.fromBlocks Dbar 0 0 (β • Abarᵀ)

/-- The right matrix of (9.22): `[Ā 0; W D̄']`. -/
def cpRight (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) :
    Matrix ((Z ⊕ Y) ⊕ ((Z ⊕ Y) ⊕ U)) (((Z ⊕ Y) ⊕ U) ⊕ (Z ⊕ Y)) ℝ :=
  Matrix.fromBlocks Abar 0 W Dbarᵀ

/-- Miao, (9.22), p. 307: the constraints `D̄x_{t+1} = Āx_t + c_{t+1}` together with the
first-order conditions `Wx_t + D̄'μ_t − βĀ'μ_{t+1} = 0` are the stacked system
`[D̄ 0; 0 βĀ'][x_{t+1}; μ_{t+1}] = [Ā 0; W D̄'][x_t; μ_t] + [c_{t+1}; 0]`. -/
theorem eq_9_22 (W : Matrix ((Z ⊕ Y) ⊕ U) ((Z ⊕ Y) ⊕ U) ℝ)
    (Dbar Abar : Matrix (Z ⊕ Y) ((Z ⊕ Y) ⊕ U) ℝ) (β : ℝ) (c μ : ℕ → Z ⊕ Y → ℝ)
    (x : ℕ → (Z ⊕ Y) ⊕ U → ℝ) :
    ((∀ t, Dbar *ᵥ x (t + 1) = Abar *ᵥ x t + c (t + 1)) ∧
      ∀ t, W *ᵥ x t + Dbarᵀ *ᵥ μ t - β • (Abarᵀ *ᵥ μ (t + 1)) = 0) ↔
    ∀ t, cpLeft β Dbar Abar *ᵥ Sum.elim (x (t + 1)) (μ (t + 1)) =
      cpRight W Dbar Abar *ᵥ Sum.elim (x t) (μ t) + Sum.elim (c (t + 1)) 0 := by
  simp only [cpLeft, cpRight, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, add_zero, zero_add, Matrix.smul_mulVec, ← Sum.elim_add_add,
    Sum.elim_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩ t
    exact ⟨h1 t, (sub_eq_zero.1 (h2 t)).symm⟩
  · intro h
    exact ⟨fun t => (h t).1, fun t => sub_eq_zero.2 (h t).2.symm⟩

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policy under commitment: the saddle path and time inconsistency

Miao, §9.4, pp. 307–308. The stacked system (9.22) (`eq_9_22`) is reordered with the
predetermined block `k_t = (z_t, μ_{yt})` first and the non-predetermined block
`λ_t = (y_t, u_t, μ_{zt})` second, `J E_t[k_{t+1}; λ_{t+1}] = H[k_t; λ_t]`, and solved by
Klein's method (Chapter 2's `Singular` and `KleinSimplified`).

**Representation.** `z`, `y`, `u` are indexed by `Fin nz`, `Fin ny`, `Fin nu`; the reordered
vector `(k, λ)` lives on `Fin ((nz + ny) + ((ny + nu) + nz))`, with `k_t` the first `nz + ny`
coordinates (`z_t`, then `μ_{yt}`) and `λ_t` the rest (`y_t`, `u_t`, then `μ_{zt}`).
`cpColEquiv` maps these coordinates to the `(x, μ)` coordinates of (9.22) and `cpRowEquiv`
orders the equations. `J = cpJ`, `H = cpH`.

* `cp_reordered_iff` (p. 307, "we reorder equations in (9.22)"): a path solves
  `J[k; λ]_{t+1} = H[k; λ]_t + C'ε_{t+1}` iff the corresponding path solves (9.22).
* `cp_saddle_path` (p. 307, "the above system has a unique saddle path solution as long as a
  stability condition and a rank condition is satisfied"): under the hypotheses of Klein's
  Theorem 1.4.5 for `(J, H)` (regularity, an ordered QZ form with as many stable generalised
  eigenvalues as predetermined variables, invertible `Z₁₁`, no eigenvalue on the unit circle),
  for every `z̄₀` and every bounded shock path, (9.22) has a unique bounded solution with
  `z₀ = z̄₀` and `μ_{y0} = 0`.
* `cp_recursive_form` (pp. 307–308): with uncertainty (the system in expectations, `ε`
  entering through the prediction error of `z`), there are matrices with
  `z_{t+1} = A_zz z_t + A_zμ μ_{yt} + Cε_{t+1}`, `μ_{y,t+1} = A_μz z_t + A_μμ μ_{yt}`,
  `y_t = A_yz z_t + A_yμ μ_{yt}`, `u_t = A_uz z_t + A_uμ μ_{yt}`,
  `μ_{zt} = A_{μz z} z_t + A_{μz μ} μ_{yt}` for every stable adapted solution: the multiplier
  `μ_y` on the forward-looking variables is a state variable.
* `cp_time_inconsistency` (p. 308): reoptimising at date `t₀` restarts the system from
  `(z_{t₀}, 0)`; the reoptimised plan coincides with the continuation of the date-`0` plan iff
  `μ_{y,t₀} = 0`.

**Departures.** The deterministic saddle-path statement is the perfect-foresight form (the shock
path given); the recursive form uses the stochastic Klein theorem of Chapter 2, whose
coefficient matrices are complex (the QZ form is complex); that they are real is not proved.
-/

namespace Miao.LinearQuadratic

open scoped Matrix

/-! ### Reordering -/

/-- The reordering `(k, λ) = ((z, μ_y), ((y, u), μ_z)) ↦ ((z, y, u), (μ_z, μ_y))`. -/
def cpReorder (Z Y U : Type*) :
    (Z ⊕ Y) ⊕ ((Y ⊕ U) ⊕ Z) ≃ ((Z ⊕ Y) ⊕ U) ⊕ (Z ⊕ Y) where
  toFun
    | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inl (Sum.inl i)) => Sum.inl (Sum.inl (Sum.inr i))
    | Sum.inr (Sum.inl (Sum.inr i)) => Sum.inl (Sum.inr i)
    | Sum.inr (Sum.inr i) => Sum.inr (Sum.inl i)
  invFun
    | Sum.inl (Sum.inl (Sum.inl i)) => Sum.inl (Sum.inl i)
    | Sum.inl (Sum.inl (Sum.inr i)) => Sum.inr (Sum.inl (Sum.inl i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inl (Sum.inr i))
    | Sum.inr (Sum.inl i) => Sum.inr (Sum.inr i)
    | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr i)
  left_inv := by rintro ((i | i) | ((i | i) | i)) <;> rfl
  right_inv := by rintro (((i | i) | i) | (i | i)) <;> rfl

/-- The coordinates of `(k, λ)`: `Fin ((nz + ny) + ((ny + nu) + nz)) ≃ (x, μ)`-coordinates. -/
def cpColEquiv (nz ny nu : ℕ) :
    Fin ((nz + ny) + ((ny + nu) + nz)) ≃
      ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))))).trans
    (cpReorder (Fin nz) (Fin ny) (Fin nu))

/-- An ordering of the equations of (9.22). -/
def cpRowEquiv (nz ny nu : ℕ) :
    Fin ((nz + ny) + ((ny + nu) + nz)) ≃
      (Fin nz ⊕ Fin ny) ⊕ ((Fin nz ⊕ Fin ny) ⊕ Fin nu) :=
  (finCongr (by omega : (nz + ny) + ((ny + nu) + nz) = (nz + ny) + ((nz + ny) + nu))).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm
      (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)))))

/-- `J` of Miao, p. 307: the reordered left matrix of (9.22). -/
def cpJ {nz ny nu : ℕ} (β : ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ) :
    Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℝ :=
  (cpLeft β Dbar Abar).submatrix (cpRowEquiv nz ny nu) (cpColEquiv nz ny nu)

/-- `H` of Miao, p. 307: the reordered right matrix of (9.22). -/
def cpH {nz ny nu : ℕ}
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ) :
    Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℝ :=
  (cpRight W Dbar Abar).submatrix (cpRowEquiv nz ny nu) (cpColEquiv nz ny nu)

/-- The shock loading `[C; 0; 0]` in the reordered equations. -/
def cpCfin {nz ny nu ne : ℕ} (C : Matrix (Fin nz) (Fin ne) ℝ) :
    Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ne) ℝ :=
  (Matrix.fromRows (Matrix.fromRows C (0 : Matrix (Fin ny) (Fin ne) ℝ))
    (0 : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) (Fin ne) ℝ)).submatrix (cpRowEquiv nz ny nu)
      (Equiv.refl _)

theorem cp_submatrix_id_mulVec {α β γ : Type*} [Fintype γ] (M : Matrix β γ ℝ) (e : α → β)
    (v : γ → ℝ) : M.submatrix e id *ᵥ v = (M *ᵥ v) ∘ e :=
  rfl

theorem cp_comp_equiv_iff {α β : Type*} (e : α ≃ β) (f g k : β → ℝ) :
    f ∘ e = g ∘ e + k ∘ e ↔ f = g + k := by
  constructor
  · intro H
    funext i
    have := congrFun H (e.symm i)
    simpa using this
  · intro H
    rw [H]
    rfl

/-- Miao, p. 307 ("we reorder equations in (9.22) and rewrite it as `J[k; λ]_{t+1} =
H[k; λ]_t`"): a path `v` of `(k, λ)` solves the reordered system iff `v ∘ cpColEquiv⁻¹` solves
(9.22) with `c_{t+1} = [Cε_{t+1}; 0]`. -/
theorem cp_reordered_iff {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℝ) (ε : ℕ → Fin ne → ℝ)
    (v : ℕ → Fin ((nz + ny) + ((ny + nu) + nz)) → ℝ) :
    IsSolution (cpJ β Dbar Abar) (cpH W Dbar Abar) (cpCfin (ny := ny) (nu := nu) C)
        (fun t => ε (t + 1)) v ↔
      ∀ t, cpLeft β Dbar Abar *ᵥ (v (t + 1) ∘ (cpColEquiv nz ny nu).symm) =
        cpRight W Dbar Abar *ᵥ (v t ∘ (cpColEquiv nz ny nu).symm) +
          Sum.elim (Sum.elim (C *ᵥ ε (t + 1)) 0) 0 := by
  simp only [IsSolution, cpJ, cpH, cpCfin, Matrix.submatrix_mulVec_equiv, Equiv.coe_refl,
    cp_submatrix_id_mulVec, cp_comp_equiv_iff, Matrix.fromRows_mulVec, Matrix.zero_mulVec]

/-- The sup norm is invariant under relabelling coordinates. -/
theorem cp_norm_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (v : β → ℝ) :
    ‖v ∘ e‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · exact norm_le_pi_norm v (e i)
  · have := norm_le_pi_norm (v ∘ e) (e.symm i)
    simpa using this

/-! ### The saddle path -/

/-- **The saddle-path solution** (Miao, p. 307). Suppose `(J, H)` satisfies the hypotheses of
Klein's Theorem 1.4.5 (`theorem_1_4_5_real`) with `n_k = n_z + n_y` predetermined variables
`k = (z, μ_y)`. Then for every initial state `z̄₀` and every bounded shock path, (9.22) has a
unique bounded solution with `z₀ = z̄₀` and `μ_{y0} = 0`. -/
theorem cp_saddle_path {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℝ)
    (hreg : IsRegular ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom))
    {Q Zq : Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup _ ℂ) (hZ : Zq ∈ Matrix.unitaryGroup _ ℂ)
    (hS : (Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hT : (Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hord : ∀ i : Fin ((nz + ny) + ((ny + nu) + nz)), i.val < nz + ny ↔
      ‖(Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq) i i‖ <
        ‖(Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq) i i‖)
    (hZ11 : (Zq.submatrix (Fin.castAdd ((ny + nu) + nz))
      (Fin.castAdd ((ny + nu) + nz))).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom), ‖lam‖ ≠ 1)
    (zbar : Fin nz → ℝ) {ε : ℕ → Fin ne → ℝ} (hε : IsStableSeq ε) :
    ∃! w : ℕ → ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) → ℝ,
      (∀ t, cpLeft β Dbar Abar *ᵥ w (t + 1) =
        cpRight W Dbar Abar *ᵥ w t + Sum.elim (Sum.elim (C *ᵥ ε (t + 1)) 0) 0) ∧
      IsStableSeq w ∧ (∀ i, w 0 (Sum.inl (Sum.inl (Sum.inl i))) = zbar i) ∧
      ∀ i, w 0 (Sum.inr (Sum.inr i)) = 0 := by
  set e := cpColEquiv nz ny nu
  obtain ⟨v, ⟨h1, h2, h3⟩, hu⟩ := theorem_1_4_5_real (C := cpCfin (ny := ny) (nu := nu) C)
    hreg hQ hZ hS hT hord hZ11 hcirc (Fin.append zbar 0) (hε.shift 1)
  have he1 : ∀ i, e (Fin.castAdd _ (Fin.castAdd ny i)) = Sum.inl (Sum.inl (Sum.inl i)) :=
    fun i => by simp [e, cpColEquiv, cpReorder]
  have he2 : ∀ i, e (Fin.castAdd _ (Fin.natAdd nz i)) = Sum.inr (Sum.inr i) :=
    fun i => by simp [e, cpColEquiv, cpReorder]
  refine ⟨fun t => v t ∘ e.symm, ⟨(cp_reordered_iff β W Dbar Abar C ε v).1 h1, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨M, hM, h⟩ := h2
    exact ⟨M, hM, fun t => by rw [cp_norm_comp_equiv]; exact h t⟩
  · intro i
    have := h3 (Fin.castAdd ny i)
    rw [Fin.append_left] at this
    simp only [Function.comp_apply, ← he1, Equiv.symm_apply_apply]
    exact this
  · intro i
    have := h3 (Fin.natAdd nz i)
    rw [Fin.append_right] at this
    simp only [Function.comp_apply, ← he2, Equiv.symm_apply_apply]
    exact this
  · rintro w ⟨hw1, hw2, hw3, hw4⟩
    have hwv : ∀ t, (w t ∘ e) ∘ e.symm = w t := fun t => by
      funext i
      simp
    have := hu (fun t => w t ∘ e) ⟨(cp_reordered_iff β W Dbar Abar C ε _).2 (fun t => by
      rw [hwv, hwv]
      exact hw1 t), ?_, ?_⟩
    · funext t
      rw [← this]
      funext i
      simp
    · obtain ⟨M, hM, h⟩ := hw2
      exact ⟨M, hM, fun t => by rw [cp_norm_comp_equiv]; exact h t⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Function.comp_apply, he1, Fin.append_left]
        exact hw3 i
      · simp only [Function.comp_apply, he2, Fin.append_right, Pi.zero_apply]
        exact hw4 i

/-- **Time inconsistency** (Miao, p. 308). Let `w` be the commitment plan chosen at date `0`
(the bounded solution of (9.22) from `(z̄₀, μ_{y0} = 0)`), and let `ŵ` be the plan chosen by
reoptimising at date `t₀`: the bounded solution of (9.22) for the remaining shocks from
`(z_{t₀}, μ_{y t₀} = 0)` ("we must have `μ_{yt} = 0` because `y_t` is freely chosen"). Under
the hypotheses of `cp_saddle_path`, the reoptimised plan is the continuation of the date-`0`
plan iff `μ_{y t₀} = 0`. -/
theorem cp_time_inconsistency {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℝ)
    (hreg : IsRegular ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom))
    {Q Zq : Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup _ ℂ) (hZ : Zq ∈ Matrix.unitaryGroup _ ℂ)
    (hS : (Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hT : (Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hord : ∀ i : Fin ((nz + ny) + ((ny + nu) + nz)), i.val < nz + ny ↔
      ‖(Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq) i i‖ <
        ‖(Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq) i i‖)
    (hZ11 : (Zq.submatrix (Fin.castAdd ((ny + nu) + nz))
      (Fin.castAdd ((ny + nu) + nz))).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom), ‖lam‖ ≠ 1)
    {ε : ℕ → Fin ne → ℝ} (hε : IsStableSeq ε)
    {w : ℕ → ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) → ℝ}
    (hw : ∀ t, cpLeft β Dbar Abar *ᵥ w (t + 1) =
      cpRight W Dbar Abar *ᵥ w t + Sum.elim (Sum.elim (C *ᵥ ε (t + 1)) 0) 0)
    (hws : IsStableSeq w) (t₀ : ℕ)
    {ŵ : ℕ → ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ⊕ (Fin nz ⊕ Fin ny) → ℝ}
    (hŵ : ∀ t, cpLeft β Dbar Abar *ᵥ ŵ (t + 1) =
      cpRight W Dbar Abar *ᵥ ŵ t + Sum.elim (Sum.elim (C *ᵥ ε (t + t₀ + 1)) 0) 0)
    (hŵs : IsStableSeq ŵ)
    (hŵz : ∀ i, ŵ 0 (Sum.inl (Sum.inl (Sum.inl i))) = w t₀ (Sum.inl (Sum.inl (Sum.inl i))))
    (hŵμ : ∀ i, ŵ 0 (Sum.inr (Sum.inr i)) = 0) :
    (∀ s, ŵ s = w (s + t₀)) ↔ ∀ i, w t₀ (Sum.inr (Sum.inr i)) = 0 := by
  constructor
  · intro h i
    rw [← hŵμ i, h 0, zero_add]
  · intro hμ
    have hu := cp_saddle_path β W Dbar Abar C hreg hQ hZ hS hT hord hZ11 hcirc
      (fun i => w t₀ (Sum.inl (Sum.inl (Sum.inl i)))) (hε.shift t₀)
    have := hu.unique (y₁ := ŵ) (y₂ := fun s => w (s + t₀))
      ⟨fun t => by simpa only [add_right_comm] using hŵ t, hŵs, hŵz, hŵμ⟩
      ⟨fun t => by simpa only [add_right_comm] using hw (t + t₀), hws.shift t₀,
        fun i => by simp, fun i => by simpa using hμ i⟩
    exact fun s => congrFun this s

/-! ### The recursive form of the solution -/

/-- **The recursive solution** (Miao, pp. 307–308). Under the hypotheses of Klein's theorem for
the complexified `(J, H)` (`klein_simplified_form`), there are matrices such that every stable
adapted solution `(k, λ) = ((z, μ_y), ((y, u), μ_z))` of the system in expectations
`J E_t[k; λ]_{t+1} = H[k; λ]_t`, in which `z` has prediction error `Cε_{t+1}` and `μ_y` is
predetermined, satisfies
`z_{t+1} = A_zz z_t + A_zμ μ_{yt} + Cε_{t+1}`, `μ_{y,t+1} = A_μz z_t + A_μμ μ_{yt}`,
`y_t = A_yz z_t + A_yμ μ_{yt}`, `u_t = A_uz z_t + A_uμ μ_{yt}` and
`μ_{zt} = A_{μz,z} z_t + A_{μz,μ} μ_{yt}`. -/
theorem cp_recursive_form {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (E : CondExpSystem ℂ V) {nz ny nu ne : ℕ} (β : ℝ)
    (W : Matrix ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (Dbar Abar : Matrix (Fin nz ⊕ Fin ny) ((Fin nz ⊕ Fin ny) ⊕ Fin nu) ℝ)
    (C : Matrix (Fin nz) (Fin ne) ℂ)
    (hreg : IsRegular ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom))
    {Q Zq : Matrix (Fin ((nz + ny) + ((ny + nu) + nz))) (Fin ((nz + ny) + ((ny + nu) + nz))) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup _ ℂ) (hZ : Zq ∈ Matrix.unitaryGroup _ ℂ)
    (hS : (Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hT : (Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq).IsUpperTriangular)
    (hord : ∀ i : Fin ((nz + ny) + ((ny + nu) + nz)), i.val < nz + ny ↔
      ‖(Q * (cpH W Dbar Abar).map Complex.ofRealHom * Zq) i i‖ <
        ‖(Q * (cpJ β Dbar Abar).map Complex.ofRealHom * Zq) i i‖)
    (hZ11 : (Zq.submatrix (Fin.castAdd ((ny + nu) + nz))
      (Fin.castAdd ((ny + nu) + nz))).det ≠ 0)
    (hcirc : ∀ lam ∈ genEigenvalues ((cpJ β Dbar Abar).map Complex.ofRealHom)
      ((cpH W Dbar Abar).map Complex.ofRealHom), ‖lam‖ ≠ 1) :
    ∃ (Azz : Matrix (Fin nz) (Fin nz) ℂ) (Azμ : Matrix (Fin nz) (Fin ny) ℂ)
      (Aμz : Matrix (Fin ny) (Fin nz) ℂ) (Aμμ : Matrix (Fin ny) (Fin ny) ℂ)
      (Ayz : Matrix (Fin ny) (Fin nz) ℂ) (Ayμ : Matrix (Fin ny) (Fin ny) ℂ)
      (Auz : Matrix (Fin nu) (Fin nz) ℂ) (Auμ : Matrix (Fin nu) (Fin ny) ℂ)
      (Amz : Matrix (Fin nz) (Fin nz) ℂ) (Amμ : Matrix (Fin nz) (Fin ny) ℂ),
      ∀ (ε : ℕ → Fin ne → V) (x : ℕ → Fin ((nz + ny) + ((ny + nu) + nz)) → V),
        IsRESolution E ((cpJ β Dbar Abar).map Complex.ofRealHom)
          ((cpH W Dbar Abar).map Complex.ofRealHom) (0 : Matrix _ (Fin 0) ℂ) (fun _ => 0) x →
        IsStableProc x → IsAdaptedV E x →
        (∀ t i, x (t + 1) (Fin.castAdd _ (Fin.castAdd ny i)) -
          E.E t (x (t + 1) (Fin.castAdd _ (Fin.castAdd ny i))) = matAct C (ε (t + 1)) i) →
        (∀ t i, E.E t (x (t + 1) (Fin.castAdd _ (Fin.natAdd nz i))) =
          x (t + 1) (Fin.castAdd _ (Fin.natAdd nz i))) →
        ∀ t,
          (x (t + 1) ∘ Fin.castAdd _) ∘ Fin.castAdd ny =
            matAct Azz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Azμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) + matAct C (ε (t + 1)) ∧
          (x (t + 1) ∘ Fin.castAdd _) ∘ Fin.natAdd nz =
            matAct Aμz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Aμμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) ∧
          (x t ∘ Fin.natAdd (nz + ny)) ∘ (Fin.castAdd nz ∘ Fin.castAdd nu) =
            matAct Ayz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Ayμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) ∧
          (x t ∘ Fin.natAdd (nz + ny)) ∘ (Fin.castAdd nz ∘ Fin.natAdd ny) =
            matAct Auz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Auμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) ∧
          (x t ∘ Fin.natAdd (nz + ny)) ∘ Fin.natAdd (ny + nu) =
            matAct Amz ((x t ∘ Fin.castAdd _) ∘ Fin.castAdd ny) +
              matAct Amμ ((x t ∘ Fin.castAdd _) ∘ Fin.natAdd nz) := by
  have hΦ : ∀ (j : ℕ) (a b : Fin 0), ‖((0 : Matrix (Fin 0) (Fin 0) ℂ) ^ j) a b‖ ≤ 0 :=
    fun _ a => a.elim0
  obtain ⟨Ayk, Ayz', Akk, Akz, hK⟩ := klein_simplified_form E hreg hQ hZ hS hT hord hZ11 hcirc
    (C := (0 : Matrix _ (Fin 0) ℂ)) 0 hΦ
  refine ⟨Akk.submatrix (Fin.castAdd ny) (Fin.castAdd ny),
    Akk.submatrix (Fin.castAdd ny) (Fin.natAdd nz),
    Akk.submatrix (Fin.natAdd nz) (Fin.castAdd ny), Akk.submatrix (Fin.natAdd nz) (Fin.natAdd nz),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.castAdd nu) (Fin.castAdd ny),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.castAdd nu) (Fin.natAdd nz),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.natAdd ny) (Fin.castAdd ny),
    Ayk.submatrix (Fin.castAdd nz ∘ Fin.natAdd ny) (Fin.natAdd nz),
    Ayk.submatrix (Fin.natAdd (ny + nu)) (Fin.castAdd ny),
    Ayk.submatrix (Fin.natAdd (ny + nu)) (Fin.natAdd nz), ?_⟩
  intro ε x hx hxs hxa hz hμ t
  have h0 : ∀ (M : Matrix (Fin (nz + ny)) (Fin 0) ℂ) (v : Fin 0 → V), matAct M v = 0 :=
    fun M v => funext fun i => by simp [matAct]
  have h0' : ∀ (M : Matrix (Fin ((ny + nu) + nz)) (Fin 0) ℂ) (v : Fin 0 → V), matAct M v = 0 :=
    fun M v => funext fun i => by simp [matAct]
  obtain ⟨hy, hk⟩ := hK (fun _ => 0) (fun t => Fin.append (matAct C (ε t)) 0) x
    ⟨1, one_pos, fun _ a => a.elim0⟩ (fun _ a => a.elim0) (fun _ => funext fun a => a.elim0)
    hx hxs hxa (fun t i => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        exact hz t i
      · rw [Fin.append_right, hμ t i, sub_self]
        rfl) t
  rw [h0', add_zero] at hy
  rw [h0, add_zero] at hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hk, Pi.add_comp, klS_append_castAdd, klS_matAct_blocks]
  · rw [hk, Pi.add_comp, klS_append_natAdd, klS_matAct_blocks, add_zero]
  · rw [hy, klS_matAct_blocks]
  · rw [hy, klS_matAct_blocks]
  · rw [hy, klS_matAct_blocks]

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian model under commitment: Examples 9.4.1 and 9.4.2

Miao, §9.4, pp. 305–311.

**Example 9.4.1** (p. 305). The basic New Keynesian model (9.20)–(9.21) with predetermined
variables `(1, z_t, Ŷ^f_t, r^n_t)` (`Fin 4`), forward-looking variables `(π_t, x_t)` (`Fin 2`)
and instrument `i_t` (`Fin 1`).
* `example_9_4_1`: the model is the state-space form (9.18) with the explicit `D`, `A`, `B`, `C`
  (`ex941D`, …); the natural rate `r^n_t = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)` becomes the
  predetermined law `r^n_{t+1} = −(1 − ρ_y)ln β + ρ_y r^n_t + γ(ρ_y − 1)ε_{y,t+1}`, which is
  consistent with the definition at every date (`example_9_4_1_rn`).
* `example_9_4_1_loss`: with unity in the state, `½(π_t − π*)² + ½λx_t²` is the loss (9.19)
  for an explicit symmetric `Q` and `R = 0`, `S = 0`.

**Example 9.4.2** (pp. 308–311). Commitment in the model (9.23) with `z_{t+1} = ρz_t + ε_{t+1}`.
* `eq_9_25`, `eq_9_26`, `eq_9_27`: the derivatives of the (horizon-`T`, perfect-foresight)
  Lagrangian `ex942Lagr` in `π_s`, `x_s`, `z_s` are `βˢ` times the left sides of (9.25)–(9.27)
  (with `μ_{x0} = 0`); `cp_stationary_iff` turns this into the first-order conditions.
* `example_9_4_2_system` (p. 310): (9.25)–(9.27), (9.23) and the shock law are the printed
  `5 × 5` system (with the fourth row of the left matrix corrected, see below).
* `eq_9_28`: (9.25), (9.26) and (9.23) give the second-order equation (9.28).
* `eq_9_29`: for `κ ≠ 0`, `λ > 0`, `0 < β < 1`, the characteristic equation (9.29) has exactly
  the two real roots `0 < a₁ < 1 < a₂` (`ex942a`), with `a₁a₂ = 1/β`.
* `ex942_lag_sum`: the lag-operator expression
  `−(1/(β²a₂))∑ⱼ a₂⁻ʲ(κx* + E_t z_{t+j})` equals `−(a/β)(κx*/(1 − βa) + z_t/(1 − βaρ))`.
* `ex942_rule_solves`, `ex942_rule_expected`: the rule
  `μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + z_t/(1 − βaρ))` solves (9.28) in expectation, for
  any mean-zero shock; `ex942_unique_bounded`: every bounded solution of (9.28) along the
  expected path `E_0 z_t = ρᵗz₀` follows the rule (the forward inversion of `L⁻¹ − a₂`).
* `ex942_solution`: with `μ_{x0} = 0`, the rule and `π_t = β(μ_{xt} − μ_{x,t+1})`,
  `x_t = x* + (βκ/λ)μ_{x,t+1}` solve (9.23), (9.25), (9.26); `ex942_muz`: the forward sum
  `μ_{zt} = −β∑ⱼ(βρ)ʲμ_{x,t+1+j}` solves (9.27) — `μ_z` plays no role in the other variables
  (footnote 4).
* `ex942_time_inconsistent`: reoptimising at date 1 (restarting from `μ_{x1} = 0`) changes
  inflation at date 1 by `−β(1 − a)μ_{x1} ≠ 0` whenever `κx*/(1 − βa) + z₀/(1 − βaρ) ≠ 0`.

**Corrections.** (9.29) has roots `0 < a₁ < 1 < a₂` only if `κ ≠ 0`; for `κ = 0` the roots are
`1` and `1/β` (`eq_9_29_kappa_zero`). In our text extraction the fourth row of the left matrix
on p. 310 reads `(0, β, 0, 0, 0)`; the row that gives (9.23) is `(0, 0, 0, β, 0)`, and with the
extracted row the system does not imply (9.23) (`example_9_4_2_printed_row_false`). The book's
expectations `E_t` are replaced by the expected (perfect-foresight) paths, except in
`ex942_rule_expected`.
-/

namespace Miao.LinearQuadratic

open scoped Matrix
open Filter Topology MeasureTheory

/-! ### Example 9.4.1 -/

/-- `D` of Example 9.4.1: `[I 0; 0 D₂₂]` with `D₂₂ = [β 0; 1/γ 1]`. -/
noncomputable def ex941D (β γ : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks 1 0 0 !![β, 0; 1 / γ, 1]

/-- `A` of Example 9.4.1. -/
noncomputable def ex941A (β γ κ ρz ρy : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1, 0, 0, 0; 0, ρz, 0, 0; 0, 0, ρy, 0; -(1 - ρy) * Real.log β, 0, 0, ρy] 0
    !![0, -1, 0, 0; 0, 0, 0, -(1 / γ)] !![1, -κ; 0, 1]

/-- `B` of Example 9.4.1. -/
noncomputable def ex941B (γ : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 1) ℝ :=
  Matrix.fromRows 0 !![0; 1 / γ]

/-- `C` of Example 9.4.1 (shocks `(ε_z, ε_y)`). -/
def ex941C (γ ρy : ℝ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![0, 0; 1, 0; 0, 1; 0, γ * (ρy - 1)]

/-- **Example 9.4.1** (Miao, p. 305). With `z = (1, z, Ŷ^f, r^n)`, `y = (π, x)`, `u = i`, the
state-space form (9.18) `D[z'; E y'] = A[z; y] + Bu + [Cε'; 0]` holds iff unity stays unity,
`z' = ρ_z z + ε_z'`, `Ŷ' = ρ_yŶ + ε_y'`,
`r^n' = −(1 − ρ_y)ln β + ρ_y r^n + γ(ρ_y − 1)ε_y'`, and (9.20)–(9.21) hold:
`π = κx + βE π' + z` and `x = E x' − (1/γ)(i − E π' − r^n)`. -/
theorem example_9_4_1 (β γ κ ρz ρy : ℝ) (z z' : Fin 4 → ℝ) (y Ey : Fin 2 → ℝ) (i : Fin 1 → ℝ)
    (e : Fin 2 → ℝ) :
    ex941D β γ *ᵥ Sum.elim z' Ey =
        ex941A β γ κ ρz ρy *ᵥ Sum.elim z y + ex941B γ *ᵥ i + Sum.elim (ex941C γ ρy *ᵥ e) 0 ↔
      (z' 0 = z 0 ∧ z' 1 = ρz * z 1 + e 0 ∧ z' 2 = ρy * z 2 + e 1 ∧
        z' 3 = -(1 - ρy) * Real.log β * z 0 + ρy * z 3 + γ * (ρy - 1) * e 1) ∧
      y 0 = κ * y 1 + β * Ey 0 + z 1 ∧ y 1 = Ey 1 - 1 / γ * (i 0 - Ey 0 - z 3) := by
  have hD : ex941D β γ *ᵥ Sum.elim z' Ey =
      Sum.elim z' ![β * Ey 0, 1 / γ * Ey 0 + Ey 1] := by
    ext (j | j) <;> fin_cases j <;>
      simp [ex941D, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply,
        Fin.succ_zero_eq_one]
  have hA : ex941A β γ κ ρz ρy *ᵥ Sum.elim z y + ex941B γ *ᵥ i + Sum.elim (ex941C γ ρy *ᵥ e) 0 =
      Sum.elim ![z 0, ρz * z 1 + e 0, ρy * z 2 + e 1,
          -(1 - ρy) * Real.log β * z 0 + ρy * z 3 + γ * (ρy - 1) * e 1]
        ![-z 1 + y 0 - κ * y 1, -(1 / γ) * z 3 + y 1 + 1 / γ * i 0] := by
    ext (j | j) <;> fin_cases j <;>
      simp [ex941A, ex941B, ex941C, Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec,
        dotProduct, Fin.sum_univ_succ]
    ring
  rw [hD, hA, Sum.elim_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have a0 : z' 0 = z 0 := congrFun h1 0
    have a1 : z' 1 = ρz * z 1 + e 0 := congrFun h1 1
    have a2 : z' 2 = ρy * z 2 + e 1 := congrFun h1 2
    have a3 : z' 3 = -(1 - ρy) * Real.log β * z 0 + ρy * z 3 + γ * (ρy - 1) * e 1 :=
      congrFun h1 3
    have b0 : β * Ey 0 = -z 1 + y 0 - κ * y 1 := congrFun h2 0
    have b1 : 1 / γ * Ey 0 + Ey 1 = -(1 / γ) * z 3 + y 1 + 1 / γ * i 0 := congrFun h2 1
    refine ⟨⟨a0, a1, a2, a3⟩, by linarith, by linarith⟩
  · rintro ⟨⟨a0, a1, a2, a3⟩, b0, b1⟩
    refine ⟨funext fun j => ?_, funext fun j => ?_⟩
    · fin_cases j
      · exact a0
      · exact a1
      · exact a2
      · exact a3
    · fin_cases j
      · change β * Ey 0 = -z 1 + y 0 - κ * y 1
        linarith
      · change 1 / γ * Ey 0 + Ey 1 = -(1 / γ) * z 3 + y 1 + 1 / γ * i 0
        linarith

/-- Miao, p. 305: the natural rate `r^n_t = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)`, with
`E_tŶ^f_{t+1} = ρ_yŶ^f_t`, is reproduced at `t + 1` by the predetermined law of
`example_9_4_1`. -/
theorem example_9_4_1_rn (β γ ρy Yf r Yf' r' ey : ℝ)
    (hr : r = -Real.log β + γ * (ρy * Yf - Yf)) (hY : Yf' = ρy * Yf + ey)
    (hr' : r' = -(1 - ρy) * Real.log β * 1 + ρy * r + γ * (ρy - 1) * ey) :
    r' = -Real.log β + γ * (ρy * Yf' - Yf') := by
  rw [hr', hr, hY]
  ring

/-- `Q` of Example 9.4.1: the loss `½(π − π*)² + ½λx²` with unity in the state. -/
def ex941Q (πs lam : ℝ) : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![πs ^ 2, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
    !![-πs, 0; 0, 0; 0, 0; 0, 0] !![-πs, 0, 0, 0; 0, 0, 0, 0] !![1, 0; 0, lam]

/-- **Example 9.4.1, the loss** (Miao, p. 305): with `z₀ = 1` (unity), `½(π_t − π*)² + ½λx_t²`
is the loss (9.19) with the symmetric `Q = ex941Q`, `R = 0`, `S = 0`. -/
theorem example_9_4_1_loss (πs lam : ℝ) (z : Fin 4 → ℝ) (hz : z 0 = 1) (y : Fin 2 → ℝ)
    (i : Fin 1 → ℝ) :
    (1 / 2) * (y 0 - πs) ^ 2 + (1 / 2) * lam * y 1 ^ 2 =
      cpLoss (ex941Q πs lam) (0 : Matrix (Fin 4 ⊕ Fin 2) (Fin 1) ℝ) 0 (Sum.elim z y) i ∧
    (ex941Q πs lam)ᵀ = ex941Q πs lam := by
  refine ⟨?_, ?_⟩
  · simp [cpLoss, ex941Q, Matrix.fromBlocks_mulVec, dotProduct, Fin.sum_univ_succ,
      Fintype.sum_sum_type, hz]
    ring
  · rw [ex941Q, Matrix.fromBlocks_transpose]
    congr 1 <;> ext a b <;> fin_cases a <;> fin_cases b <;> rfl

/-! ### Example 9.4.2: the Lagrangian and the first-order conditions -/

/-- The perturbation `f_s ↦ f_s + a` of one date. -/
def cpPert (f : ℕ → ℝ) (s : ℕ) (a : ℝ) : ℕ → ℝ := fun t => f t + if t = s then a else 0

theorem cp_pert_zero (f : ℕ → ℝ) (s : ℕ) : cpPert f s 0 = f := by
  funext t
  simp [cpPert]

theorem cp_sum_delta {T s : ℕ} (hs : s < T) (a : ℝ) (g : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (if t = s then a else 0) * g t = a * g s := by
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, hs, ↓reduceIte]

theorem cp_sum_delta_sq {T s : ℕ} (hs : s < T) (a : ℝ) (g : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (if t = s then a else 0) ^ 2 * g t = a ^ 2 * g s := by
  simp only [ite_pow, ite_mul, zero_pow two_ne_zero, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, hs, ↓reduceIte]

theorem cp_sum_delta_succ {T s : ℕ} (hs : s < T) (a : ℝ) (g : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (if t + 1 = s then a else 0) * g t =
      if s = 0 then 0 else a * g (s - 1) := by
  by_cases h0 : s = 0
  · simp only [h0, Nat.add_one_ne_zero, ↓reduceIte, zero_mul, Finset.sum_const_zero]
  · have hr : s - 1 < T := by omega
    have hiff : ∀ t, (t + 1 = s) ↔ (t = s - 1) := fun t => by omega
    simp only [hiff, ite_mul, zero_mul, h0, Finset.sum_ite_eq', Finset.mem_range, hr,
      ↓reduceIte]

/-- A function that is exactly `c + ab + a²d` has derivative `b` at `0`. -/
theorem cp_hasDerivAt_quad {f : ℝ → ℝ} {b c d : ℝ} (hf : ∀ a, f a = c + a * b + a ^ 2 * d) :
    HasDerivAt f b 0 := by
  have := (((hasDerivAt_id (0 : ℝ)).mul_const b).const_add c).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const d)
  have hf' : f = (fun a => c + id a * b) + fun a => a ^ 2 * d := by
    funext a
    rw [hf a, Pi.add_apply, id]
  rw [hf']
  convert this using 1
  simp

/-- Stationarity: if the derivative is `βˢg` with `β ≠ 0`, it vanishes iff `g = 0`. -/
theorem cp_stationary_iff {f : ℝ → ℝ} {β g : ℝ} (s : ℕ) (hβ : β ≠ 0)
    (hf : HasDerivAt f (β ^ s * g) 0) : HasDerivAt f 0 0 ↔ g = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.1 (hf.unique h) with h1 | h1
    · exact absurd h1 (pow_ne_zero _ hβ)
    · exact h1
  · intro h
    rwa [h, mul_zero] at hf

/-- The Lagrangian of Example 9.4.2 (Miao, p. 309), truncated at `T`, along given paths:
`∑_{t<T} βᵗ[½π_t² + ½λ(x_t − x*)² − βμ_{z,t+1}(z_{t+1} − ρz_t − ε_{t+1})
− βμ_{x,t+1}(κx_t + βπ_{t+1} + z_t − π_t)] − μ_{z0}(z₀ − z̄₀)`. -/
noncomputable def ex942Lagr (β κ lam ρ xs zbar : ℝ) (eps μx μz : ℕ → ℝ) (T : ℕ)
    (pin x z : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
      β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
      β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) -
    μz 0 * (z 0 - zbar)

/-- Miao, (9.25), p. 309: with `μ_{x0} = 0`, the derivative of the Lagrangian in `π_s`
(`s < T`) is `βˢ(π_s + βμ_{x,s+1} − βμ_{xs})`. -/
theorem eq_9_25 (β κ lam ρ xs zbar : ℝ) (eps μx μz : ℕ → ℝ) (hμ0 : μx 0 = 0) {T s : ℕ}
    (hs : s < T) (pin x z : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam ρ xs zbar eps μx μz T (cpPert pin s a) x z)
      (β ^ s * (pin s + β * μx (s + 1) - β * μx s)) 0 := by
  refine cp_hasDerivAt_quad (c := ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x z)
    (d := β ^ s * (1 / 2)) fun a => ?_
  have hterm : ∀ t, β ^ t * ((1 / 2) * cpPert pin s a t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
      β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
      β * μx (t + 1) * (κ * x t + β * cpPert pin s a (t + 1) + z t - cpPert pin s a t)) =
      β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
        β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
        β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) +
      (if t = s then a else 0) * (β ^ t * (pin t + β * μx (t + 1))) +
      (if t + 1 = s then a else 0) * (-(β ^ (t + 1) * β * μx (t + 1))) +
      (if t = s then a else 0) ^ 2 * (β ^ t * (1 / 2)) := fun t => by
    simp only [cpPert]
    ring
  simp only [ex942Lagr]
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, cp_sum_delta hs, cp_sum_delta_succ hs, cp_sum_delta_sq hs]
  by_cases h0 : s = 0
  · subst h0
    simp only [↓reduceIte, hμ0]
    ring
  · simp only [h0, ↓reduceIte, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
    ring

/-- Miao, (9.26), p. 309: the derivative of the Lagrangian in `x_s` (`s < T`) is
`βˢ(λ(x_s − x*) − βκμ_{x,s+1})`. -/
theorem eq_9_26 (β κ lam ρ xs zbar : ℝ) (eps μx μz : ℕ → ℝ) {T s : ℕ} (hs : s < T)
    (pin x z : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam ρ xs zbar eps μx μz T pin (cpPert x s a) z)
      (β ^ s * (lam * (x s - xs) - β * κ * μx (s + 1))) 0 := by
  refine cp_hasDerivAt_quad (c := ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x z)
    (d := β ^ s * (lam / 2)) fun a => ?_
  have hterm : ∀ t, β ^ t * ((1 / 2) * pin t ^ 2 +
      (1 / 2) * lam * (cpPert x s a t - xs) ^ 2 -
      β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
      β * μx (t + 1) * (κ * cpPert x s a t + β * pin (t + 1) + z t - pin t)) =
      β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
        β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
        β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) +
      (if t = s then a else 0) * (β ^ t * (lam * (x t - xs) - β * κ * μx (t + 1))) +
      (if t = s then a else 0) ^ 2 * (β ^ t * (lam / 2)) := fun t => by
    simp only [cpPert]
    ring
  simp only [ex942Lagr]
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    cp_sum_delta hs, cp_sum_delta_sq hs]
  ring

/-- Miao, (9.27), p. 309: the derivative of the Lagrangian in `z_s` (`s < T`) is
`βˢ(−βμ_{x,s+1} + βρμ_{z,s+1} − μ_{zs})`. -/
theorem eq_9_27 (β κ lam ρ xs zbar : ℝ) (hβ : β ≠ 0) (eps μx μz : ℕ → ℝ) {T s : ℕ}
    (hs : s < T) (pin x z : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x (cpPert z s a))
      (β ^ s * (-(β * μx (s + 1)) + β * ρ * μz (s + 1) - μz s)) 0 := by
  refine cp_hasDerivAt_quad (c := ex942Lagr β κ lam ρ xs zbar eps μx μz T pin x z)
    (d := 0) fun a => ?_
  have hterm : ∀ t, β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
      β * μz (t + 1) * (cpPert z s a (t + 1) - ρ * cpPert z s a t - eps (t + 1)) -
      β * μx (t + 1) * (κ * x t + β * pin (t + 1) + cpPert z s a t - pin t)) =
      β ^ t * ((1 / 2) * pin t ^ 2 + (1 / 2) * lam * (x t - xs) ^ 2 -
        β * μz (t + 1) * (z (t + 1) - ρ * z t - eps (t + 1)) -
        β * μx (t + 1) * (κ * x t + β * pin (t + 1) + z t - pin t)) +
      (if t = s then a else 0) * (β ^ t * (β * ρ * μz (t + 1) - β * μx (t + 1))) +
      (if t + 1 = s then a else 0) * (-(β ^ (t + 1) * μz (t + 1))) := fun t => by
    simp only [cpPert]
    ring
  simp only [ex942Lagr]
  rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    cp_sum_delta hs, cp_sum_delta_succ hs]
  by_cases h0 : s = 0
  · subst h0
    simp only [cpPert, ↓reduceIte]
    ring
  · have h0' : ¬ (0 = s) := fun h => h0 h.symm
    have hp : β ^ s = β ^ (s - 1 + 1) := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
    simp only [cpPert, h0, h0', ↓reduceIte, add_zero]
    rw [hp, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
    have := hβ
    ring

/-! ### Example 9.4.2: the system and its solution -/

/-- The left matrix of the system on p. 310 (fourth row corrected), in the variables
`(z, μ_x, x, π, μ_z)`. -/
def ex942L (β κ ρ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 0, β, 0, 0, 0; 0, β * κ, 0, 0, 0; 0, 0, 0, β, 0; 0, -β, 0, 0, β * ρ]

/-- The right matrix of the system on p. 310. -/
def ex942R (β κ lam ρ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ρ, 0, 0, 0, 0; 0, β, 0, -1, 0; 0, 0, lam, 0, 0; -1, 0, -κ, 1, 0; 0, 0, 0, 0, 1]

/-- **Example 9.4.2, the system** (Miao, p. 310). For `v = (z_t, μ_{xt}, x_t, π_t, μ_{zt})` and
`v' = E_t v_{t+1}`, `Lv' = Rv − (0, 0, λx*, 0, 0)` iff `E_t z_{t+1} = ρz_t`, (9.25), (9.26),
(9.23) and (9.27) hold. -/
theorem example_9_4_2_system (β κ lam ρ xs : ℝ) (v v' : Fin 5 → ℝ) :
    ex942L β κ ρ *ᵥ v' = ex942R β κ lam ρ *ᵥ v - ![0, 0, lam * xs, 0, 0] ↔
      v' 0 = ρ * v 0 ∧ v 3 + β * v' 1 - β * v 1 = 0 ∧ lam * (v 2 - xs) - β * κ * v' 1 = 0 ∧
      v 3 = κ * v 2 + β * v' 3 + v 0 ∧ -(β * v' 1) + β * ρ * v' 4 - v 4 = 0 := by
  have hL : ex942L β κ ρ *ᵥ v' = ![v' 0, β * v' 1, β * κ * v' 1, β * v' 3,
      -β * v' 1 + β * ρ * v' 4] := by
    ext j
    fin_cases j <;> simp [ex942L, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hR : ex942R β κ lam ρ *ᵥ v - ![0, 0, lam * xs, 0, 0] = ![ρ * v 0, β * v 1 - v 3,
      lam * v 2 - lam * xs, -v 0 - κ * v 2 + v 3, v 4] := by
    ext j
    fin_cases j <;> simp [ex942R, dotProduct, Fin.sum_univ_succ] <;> ring
  rw [hL, hR]
  constructor
  · intro h
    have a0 : v' 0 = ρ * v 0 := congrFun h 0
    have a1 : β * v' 1 = β * v 1 - v 3 := congrFun h 1
    have a2 : β * κ * v' 1 = lam * v 2 - lam * xs := congrFun h 2
    have a3 : β * v' 3 = -v 0 - κ * v 2 + v 3 := congrFun h 3
    have a4 : -β * v' 1 + β * ρ * v' 4 = v 4 := congrFun h 4
    refine ⟨a0, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨a0, a1, a2, a3, a4⟩
    funext j
    fin_cases j
    · exact a0
    · change β * v' 1 = β * v 1 - v 3
      linarith
    · change β * κ * v' 1 = lam * v 2 - lam * xs
      linarith
    · change β * v' 3 = -v 0 - κ * v 2 + v 3
      linarith
    · change -β * v' 1 + β * ρ * v' 4 = v 4
      linarith

/-- The left matrix as it appears in our extraction of p. 310 (fourth row `(0, β, 0, 0, 0)`). -/
def ex942Lprinted (β κ ρ : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 0, β, 0, 0, 0; 0, β * κ, 0, 0, 0; 0, β, 0, 0, 0; 0, -β, 0, 0, β * ρ]

/-- Correction (Miao, p. 310): with the fourth row `(0, β, 0, 0, 0)`, the system does not
imply (9.23): for `β = 1/2`, `κ = λ = 1`, `ρ = x* = 0` the point `v = 0`, `v' = (0,0,0,1,0)`
solves it but `π_t ≠ κx_t + βE_tπ_{t+1} + z_t`. -/
theorem example_9_4_2_printed_row_false :
    ex942Lprinted (1 / 2) 1 0 *ᵥ ![0, 0, 0, 1, 0] = ex942R (1 / 2) 1 1 0 *ᵥ ![0, 0, 0, 0, 0] -
      ![0, 0, 1 * 0, 0, 0] ∧
    ¬ ((![0, 0, 0, 0, 0] : Fin 5 → ℝ) 3 = 1 * (![0, 0, 0, 0, 0] : Fin 5 → ℝ) 2 +
      (1 / 2) * (![0, 0, 0, 1, 0] : Fin 5 → ℝ) 3 + (![0, 0, 0, 0, 0] : Fin 5 → ℝ) 0) := by
  refine ⟨?_, ?_⟩
  · ext i
    fin_cases i <;> simp [ex942Lprinted, ex942R, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · norm_num

/-- Miao, (9.28), p. 310: (9.25) at `t` and `t + 1`, (9.26) at `t` and (9.23) at `t` (in
expected values) give `βμ_{t+2} − (1 + β + κ²/λ)μ_{t+1} + μ_t = κx*/β + z_t/β`. -/
theorem eq_9_28 {β κ lam xs : ℝ} (hβ : β ≠ 0) (hlam : lam ≠ 0) (pin x z μ : ℕ → ℝ) (t : ℕ)
    (h25 : pin t + β * μ (t + 1) - β * μ t = 0)
    (h25' : pin (t + 1) + β * μ (t + 2) - β * μ (t + 1) = 0)
    (h26 : lam * (x t - xs) - β * κ * μ (t + 1) = 0)
    (h23 : pin t = κ * x t + β * pin (t + 1) + z t) :
    β * μ (t + 2) - (1 + β + κ ^ 2 / lam) * μ (t + 1) + μ t = κ * xs / β + z t / β := by
  have hx : x t = xs + β * κ / lam * μ (t + 1) := by
    field_simp
    linarith
  have hp : pin t = β * (μ t - μ (t + 1)) := by linarith
  have hp' : pin (t + 1) = β * (μ (t + 1) - μ (t + 2)) := by linarith
  rw [hx, hp, hp'] at h23
  have key : β * (β * μ (t + 2) - (1 + β + κ ^ 2 / lam) * μ (t + 1) + μ t) = κ * xs + z t := by
    linear_combination h23
  rw [← add_div, eq_div_iff hβ]
  linear_combination key

/-- The coefficient `1 + β + κ²/λ` of (9.28). -/
noncomputable def ex942b (β κ lam : ℝ) : ℝ := 1 + β + κ ^ 2 / lam

/-- The stable root `a₁` of (9.29). -/
noncomputable def ex942a (β κ lam : ℝ) : ℝ :=
  (ex942b β κ lam - Real.sqrt (ex942b β κ lam ^ 2 - 4 * β)) / (2 * β)

/-- A root `a ≠ 0` of (9.29) gives `1 + β + κ²/λ = βa + 1/a`. -/
theorem ex942_b_eq {β κ lam a : ℝ} (ha : a ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) : ex942b β κ lam = β * a + a⁻¹ := by
  have h1 : ex942b β κ lam * a = β * a ^ 2 + 1 := by linear_combination (-1) * hroot
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  linear_combination a⁻¹ * h1 - (ex942b β κ lam - β * a) * hia

/-- **The characteristic equation (9.29)** (Miao, p. 310). For `0 < β < 1`, `λ > 0`, `κ ≠ 0`,
`βa² − (1 + β + κ²/λ)a + 1 = 0` has the two real roots `a₁ = ex942a` and `a₂ = 1/(βa₁)`, with
`0 < a₁ < 1 < a₂`, and no others. -/
theorem eq_9_29 {β κ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam) (hκ : κ ≠ 0) :
    let a := ex942a β κ lam
    0 < a ∧ a < 1 ∧ 1 < 1 / (β * a) ∧
      β * a ^ 2 - ex942b β κ lam * a + 1 = 0 ∧
      β * (1 / (β * a)) ^ 2 - ex942b β κ lam * (1 / (β * a)) + 1 = 0 ∧
      ∀ r, β * r ^ 2 - ex942b β κ lam * r + 1 = 0 ↔ r = a ∨ r = 1 / (β * a) := by
  intro a
  set b := ex942b β κ lam with hb
  have hk2 : 0 < κ ^ 2 / lam := div_pos (by positivity) hlam
  have hb1 : 1 + β < b := by rw [hb, ex942b]; linarith
  have hD : 0 ≤ b ^ 2 - 4 * β := by nlinarith
  set q := Real.sqrt (b ^ 2 - 4 * β) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = b ^ 2 - 4 * β := Real.sq_sqrt hD
  have hqb : q < b := by nlinarith
  have hqb2 : b - 2 * β < q := by nlinarith
  have ha : a = (b - q) / (2 * β) := rfl
  have hapos : 0 < a := by rw [ha]; apply div_pos <;> linarith
  have ha1 : a < 1 := by rw [ha, div_lt_one (by linarith)]; linarith
  have hroot : β * a ^ 2 - b * a + 1 = 0 := by
    rw [ha]
    field_simp
    nlinarith
  have hβa : 0 < β * a := mul_pos hβ0 hapos
  have hβa1 : β * a < 1 := by nlinarith
  have ha2 : 1 < 1 / (β * a) := by rw [lt_div_iff₀ hβa]; linarith
  have hb' : b = β * a + a⁻¹ := ex942_b_eq hapos.ne' hroot
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ hapos.ne'
  have hib : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ0.ne'
  have hfac : ∀ r, β * r ^ 2 - b * r + 1 = β * (r - a) * (r - 1 / (β * a)) := by
    intro r
    rw [hb']
    linear_combination (a⁻¹ * r - 1) * hib - β * β⁻¹ * hia
  have hroot2 : β * (1 / (β * a)) ^ 2 - b * (1 / (β * a)) + 1 = 0 := by
    rw [hfac]
    ring
  refine ⟨hapos, ha1, ha2, hroot, hroot2, fun r => ?_⟩
  rw [hfac r]
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hβ0.ne'
      · exact Or.inl (sub_eq_zero.1 h2)
    · exact Or.inr (sub_eq_zero.1 h1)
  · rintro (h | h) <;> rw [h] <;> ring

/-- Correction to (9.29) (Miao, p. 310): for `κ = 0` the roots are `1` and `1/β`, so
`0 < a₁ < 1 < a₂` fails. -/
theorem eq_9_29_kappa_zero {β lam : ℝ} (hβ : β ≠ 0) :
    β * 1 ^ 2 - ex942b β 0 lam * 1 + 1 = 0 ∧
      β * (1 / β) ^ 2 - ex942b β 0 lam * (1 / β) + 1 = 0 := by
  simp only [ex942b]
  constructor
  · ring
  · field_simp
    ring

/-- Miao, p. 311: with `a₂ = 1/(βa)`, `0 < βa < 1` and `|ρ| ≤ 1`, the forward (lag-operator)
sum `−(1/(β²a₂))∑ⱼ a₂⁻ʲ(κx* + ρʲz)` equals `−(a/β)(κx*/(1 − βa) + z/(1 − βaρ))`
(`E_t z_{t+j} = ρʲz_t`). -/
theorem ex942_lag_sum {β a ρ κ xs z : ℝ} (hβ : β ≠ 0) (ha0 : 0 < β * a) (ha1 : β * a < 1)
    (hρ : |ρ| ≤ 1) :
    -(1 / (β ^ 2 * (1 / (β * a)))) * ∑' j : ℕ, ((1 / (β * a)) ^ j)⁻¹ * (κ * xs + ρ ^ j * z) =
      -(a / β) * (κ * xs / (1 - β * a) + z / (1 - β * a * ρ)) := by
  have h1 : |β * a| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have h2 : |β * a * ρ| < 1 := by
    rw [abs_mul, abs_of_pos ha0]
    nlinarith [abs_nonneg ρ]
  have hs1 := summable_geometric_of_abs_lt_one h1
  have hs2 := summable_geometric_of_abs_lt_one h2
  have hterm : ∀ j : ℕ, ((1 / (β * a)) ^ j)⁻¹ * (κ * xs + ρ ^ j * z) =
      κ * xs * (β * a) ^ j + z * (β * a * ρ) ^ j := fun j => by
    rw [one_div, inv_pow, inv_inv, mul_pow]
    ring
  have ha : a ≠ 0 := by
    rintro rfl
    simp at ha0
  have hd1 : 1 - β * a ≠ 0 := by linarith
  have hd2 : 1 - β * a * ρ ≠ 0 := by
    have := (abs_lt.1 h2).2
    linarith
  rw [tsum_congr hterm, (hs1.mul_left _).tsum_add (hs2.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one h1, tsum_geometric_of_abs_lt_one h2]
  field_simp

/-- The commitment rule for the multiplier (Miao, p. 311):
`μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + z_t/(1 − βaρ))`. -/
noncomputable def ex942Rule (β κ ρ xs a μ z : ℝ) : ℝ :=
  a * μ - a / β * (κ * xs / (1 - β * a) + z / (1 - β * a * ρ))

/-- Miao, p. 311: if `a` is a root of (9.29), the rule solves (9.28) in expectation:
with `μ_{t+1}` given by the rule and `E_tμ_{t+2} = rule(μ_{t+1}, E_t z_{t+1})`,
`E_t z_{t+1} = ρz_t`, (9.28) holds. -/
theorem ex942_rule_solves {β κ lam ρ xs a : ℝ} (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hd2 : 1 - β * a * ρ ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (μ z : ℝ) :
    β * ex942Rule β κ ρ xs a (ex942Rule β κ ρ xs a μ z) (ρ * z) -
        ex942b β κ lam * ex942Rule β κ ρ xs a μ z + μ = κ * xs / β + z / β := by
  have hia : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  have hK : κ * xs / (1 - β * a) * (1 - β * a) = κ * xs := div_mul_cancel₀ _ hd1
  have hc : (1 - β * a * ρ)⁻¹ * (1 - β * a * ρ) = 1 := inv_mul_cancel₀ hd2
  rw [ex942_b_eq ha hroot, ex942Rule, ex942Rule]
  linear_combination (-μ + β⁻¹ * (κ * xs / (1 - β * a)) + β⁻¹ * (1 - β * a * ρ)⁻¹ * z) * hia +
    β⁻¹ * hK + β⁻¹ * z * hc

/-- Miao, p. 311 (the conditional expectation): for a mean-zero integrable shock `ε` with
`z_{t+1} = ρz_t + ε`, `E_t μ_{x,t+2} = E[rule(μ_{x,t+1}, ρz_t + ε)] = rule(μ_{x,t+1}, ρz_t)`. -/
theorem ex942_rule_expected {β κ ρ xs a : ℝ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun e => e) ν) (hmean : ∫ e, e ∂ν = 0) (μ z : ℝ) :
    ∫ e, ex942Rule β κ ρ xs a μ (ρ * z + e) ∂ν = ex942Rule β κ ρ xs a μ (ρ * z) := by
  have h : ∀ e, ex942Rule β κ ρ xs a μ (ρ * z + e) =
      ex942Rule β κ ρ xs a μ (ρ * z) + (-(a / β) / (1 - β * a * ρ)) * e := fun e => by
    simp only [ex942Rule]
    ring
  simp only [h]
  rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
    hmean]
  simp

/-- **Uniqueness of the bounded solution** (Miao, p. 311: inverting `L⁻¹ − a₂` forward). Let
`a` be a root of (9.29) with `0 < βa < 1`, `|ρ| ≤ 1`, and let `z_{t+1} = ρz_t` (the expected
path). Every bounded solution of (9.28) follows the rule `μ_{t+1} = rule(μ_t, z_t)`. -/
theorem ex942_unique_bounded {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (ha0 : 0 < β * a)
    (ha1 : β * a < 1) (hρ : |ρ| ≤ 1) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0)
    (z μ : ℕ → ℝ) (hz : ∀ t, z (t + 1) = ρ * z t)
    (h28 : ∀ t, β * μ (t + 2) - ex942b β κ lam * μ (t + 1) + μ t = κ * xs / β + z t / β)
    (hμb : ∃ M, ∀ t, |μ t| ≤ M) :
    ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (z t) := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at ha0
  have hd1 : 1 - β * a ≠ 0 := by linarith
  have h2 : |β * a * ρ| < 1 := by
    rw [abs_mul, abs_of_pos ha0]
    nlinarith [abs_nonneg ρ]
  have hd2 : 1 - β * a * ρ ≠ 0 := by
    have := (abs_lt.1 h2).2
    linarith
  have hb : ex942b β κ lam = β * a + a⁻¹ := ex942_b_eq ha hroot
  have hib : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  set e : ℕ → ℝ := fun t => μ (t + 1) - ex942Rule β κ ρ xs a (μ t) (z t) with he
  have hrec : ∀ t, e (t + 1) = 1 / (β * a) * e t := by
    intro t
    have h := h28 t
    have hs := ex942_rule_solves (κ := κ) (lam := lam) (xs := xs) ha hd1 hd2 hroot (μ t) (z t)
    rw [hb] at h hs
    have hlin : ex942Rule β κ ρ xs a (μ (t + 1)) (ρ * z t) =
        ex942Rule β κ ρ xs a (ex942Rule β κ ρ xs a (μ t) (z t)) (ρ * z t) +
          a * (μ (t + 1) - ex942Rule β κ ρ xs a (μ t) (z t)) := by
      simp only [ex942Rule]
      ring
    simp only [he, hz t, hlin]
    linear_combination β⁻¹ * h - β⁻¹ * hs -
      ((μ (t + 1 + 1) - ex942Rule β κ ρ xs a (ex942Rule β κ ρ xs a (μ t) (z t)) (ρ * z t)) -
        a * (μ (t + 1) - ex942Rule β κ ρ xs a (μ t) (z t))) * hib
  have hpow : ∀ t, e t = (1 / (β * a)) ^ t * e 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hrec, ih, pow_succ]; ring
  have hzb : ∀ t, |z t| ≤ |z 0| := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ n ih =>
      rw [hz, abs_mul]
      nlinarith [abs_nonneg (z n)]
  obtain ⟨M, hM⟩ := hμb
  have heb : ∀ t, |e t| ≤ M + |a| * M + |a / β| * (|κ * xs / (1 - β * a)| +
      |z 0| / |1 - β * a * ρ|) := by
    intro t
    simp only [he, ex942Rule]
    have h1 := hM (t + 1)
    have h2 := hM t
    have h3 : |z t / (1 - β * a * ρ)| ≤ |z 0| / |1 - β * a * ρ| := by
      rw [abs_div]
      exact div_le_div_of_nonneg_right (hzb t) (abs_nonneg _)
    calc |μ (t + 1) - (a * μ t - a / β * (κ * xs / (1 - β * a) + z t / (1 - β * a * ρ)))|
        ≤ |μ (t + 1)| + |a * μ t| + |a / β * (κ * xs / (1 - β * a) + z t / (1 - β * a * ρ))| :=
          by
            have := abs_sub (μ (t + 1)) (a * μ t - a / β * (κ * xs / (1 - β * a) +
              z t / (1 - β * a * ρ)))
            have := abs_sub (a * μ t) (a / β * (κ * xs / (1 - β * a) + z t / (1 - β * a * ρ)))
            linarith
      _ ≤ M + |a| * M + |a / β| * (|κ * xs / (1 - β * a)| + |z 0| / |1 - β * a * ρ|) := by
          rw [abs_mul, abs_mul]
          have := abs_add_le (κ * xs / (1 - β * a)) (z t / (1 - β * a * ρ))
          have h4 : |κ * xs / (1 - β * a) + z t / (1 - β * a * ρ)| ≤
              |κ * xs / (1 - β * a)| + |z 0| / |1 - β * a * ρ| := by linarith
          have h5 := mul_le_mul_of_nonneg_left h4 (abs_nonneg (a / β))
          have h6 := mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
          linarith
  have he0 : e 0 = 0 := by
    by_contra hne
    have hgt : 1 < 1 / (β * a) := by rw [lt_div_iff₀ ha0]; linarith
    have ht := tendsto_pow_atTop_atTop_of_one_lt hgt
    have ht2 := (ht.atTop_mul_const (abs_pos.2 hne)).eventually_gt_atTop
      (M + |a| * M + |a / β| * (|κ * xs / (1 - β * a)| + |z 0| / |1 - β * a * ρ|))
    obtain ⟨t, ht3⟩ := ht2.exists
    have := heb t
    rw [hpow t, abs_mul, abs_of_pos (pow_pos (by linarith) t)] at this
    linarith
  intro t
  have := hpow t
  rw [he0, mul_zero] at this
  simp only [he] at this
  linarith

/-- **The commitment solution of Example 9.4.2** (Miao, p. 311). Let `a` be a root of (9.29),
`μ_{x0} = 0`, `μ_{x,t+1} = rule(μ_{xt}, z_t)`, `π_t = β(μ_{xt} − μ_{x,t+1})` and
`x_t = x* + (βκ/λ)μ_{x,t+1}`. Along `z_{t+1} = ρz_t`, (9.25), (9.26) and (9.23) hold at every
date. -/
theorem ex942_solution {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (hlam : lam ≠ 0) (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hd2 : 1 - β * a * ρ ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (z μ : ℕ → ℝ)
    (hz : ∀ t, z (t + 1) = ρ * z t) (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (z t)) :
    let pin : ℕ → ℝ := fun t => β * (μ t - μ (t + 1))
    let x : ℕ → ℝ := fun t => xs + β * κ / lam * μ (t + 1)
    ∀ t, pin t + β * μ (t + 1) - β * μ t = 0 ∧ lam * (x t - xs) - β * κ * μ (t + 1) = 0 ∧
      pin t = κ * x t + β * pin (t + 1) + z t := by
  intro pin x t
  refine ⟨by simp only [pin]; ring, by simp only [x]; field_simp; ring, ?_⟩
  have h := ex942_rule_solves (κ := κ) (lam := lam) (xs := xs) ha hd1 hd2 hroot (μ t) (z t)
  have hib : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  simp only [pin, x]
  rw [hμ (t + 1), hz t, hμ t]
  simp only [ex942b] at h
  linear_combination β * h + (κ * xs + z t) * hib

/-- Miao, p. 311 ("(9.25)–(9.27) then determine … `μ_{zt}`"): for bounded `μ_x` and
`|βρ| < 1`, the forward sum `μ_{zt} = −β∑ⱼ(βρ)ʲμ_{x,t+1+j}` solves (9.27). -/
theorem ex942_muz {β ρ : ℝ} (hβρ : |β * ρ| < 1) (μx : ℕ → ℝ) (hμ : ∃ M, ∀ t, |μx t| ≤ M)
    (t : ℕ) :
    let μz : ℕ → ℝ := fun t => -β * ∑' j : ℕ, (β * ρ) ^ j * μx (t + 1 + j)
    (-(β * μx (t + 1)) + β * ρ * μz (t + 1) - μz t) = 0 := by
  intro μz
  obtain ⟨M, hM⟩ := hμ
  have hsum : ∀ s, Summable fun j : ℕ => (β * ρ) ^ j * μx (s + 1 + j) := fun s => by
    refine Summable.of_norm_bounded (g := fun j => M * |β * ρ| ^ j)
      ((summable_geometric_of_lt_one (abs_nonneg _) hβρ).mul_left M) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (pow_nonneg (abs_nonneg _) _)
  have h := (hsum t).tsum_eq_zero_add
  simp only [μz]
  rw [h]
  have hs : ∀ j : ℕ, (β * ρ) ^ (j + 1) * μx (t + 1 + (j + 1)) =
      β * ρ * ((β * ρ) ^ j * μx (t + 1 + 1 + j)) := fun j => by
    rw [pow_succ, show t + 1 + (j + 1) = t + 1 + 1 + j by ring]
    ring
  rw [tsum_congr hs, tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  ring

/-- **Time inconsistency in Example 9.4.2** (Miao, p. 308 and p. 311). Commitment from date `0`
gives `μ_{x1} = rule(0, z₀)`, `μ_{x2} = rule(μ_{x1}, z₁)`, `π₁ = β(μ_{x1} − μ_{x2})`.
Reoptimising at date `1` restarts the rule from `μ_{x1} = 0`: `π̂₁ = β(0 − rule(0, z₁))`. Then
`π₁ − π̂₁ = β(1 − a)μ_{x1}`, which is nonzero when `a ≠ 1`, `β ≠ 0` and
`κx*/(1 − βa) + z₀/(1 − βaρ) ≠ 0`. -/
theorem ex942_time_inconsistent {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (z0 z1 : ℝ) (hK : κ * xs / (1 - β * a) + z0 / (1 - β * a * ρ) ≠ 0) :
    let μ1 := ex942Rule β κ ρ xs a 0 z0
    let pin1 := β * (μ1 - ex942Rule β κ ρ xs a μ1 z1)
    let pinhat1 := β * (0 - ex942Rule β κ ρ xs a 0 z1)
    pin1 - pinhat1 = β * (1 - a) * μ1 ∧ pin1 ≠ pinhat1 := by
  intro μ1 pin1 pinhat1
  have h1 : pin1 - pinhat1 = β * (1 - a) * μ1 := by
    simp only [pin1, pinhat1, ex942Rule]
    ring
  refine ⟨h1, fun h => ?_⟩
  rw [sub_eq_zero.2 h] at h1
  have hμ1 : μ1 ≠ 0 := by
    simp only [μ1, ex942Rule, mul_zero, zero_sub, neg_ne_zero]
    exact mul_ne_zero (div_ne_zero ha hβ) hK
  have : β * (1 - a) * μ1 ≠ 0 := mul_ne_zero (mul_ne_zero hβ (sub_ne_zero.2 (Ne.symm ha1))) hμ1
  exact this h1.symm

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal discretionary policy: Markov perfect equilibrium in linear rules

Miao, §9.5, pp. 311–315. The system (9.18) with `C = I`, `D = [I 0; D₂₁ D₂₂]`, partitioned as
`z_{t+1} = A_zz z_t + A_zy y_t + B_z u_t + ε_{t+1}` and
`D₂₁E_t z_{t+1} + D₂₂E_t y_{t+1} = A_yz z_t + A_yy y_t + B_y u_t`, with `Cov(ε) = Σ`, the loss
(9.19) and linear rules `y_t = Mz_t`, `u_t = −Fz_t` (9.30). The model data are bundled in
`CPDisc`.

* `cp_disc_loss_eq` (p. 313): the loss written blockwise (Step 2, first line) is (9.19).
* `cp_expected_quadratic` (pp. 312–314): for a mean-zero shock with covariance `Σ`,
  `E[½(m + ε)'V(m + ε) + ½v] = ½m'Vm + ½tr(VΣ) + ½v`; this is how `E_t J_{t+1}(z_{t+1})`
  enters (9.39) and gives `v_t = β tr(V_{t+1}Σ) + βv_{t+1}`.
* Step 1: `eq_9_35_36` (the private sector's expectations `E_t y_{t+1} = M_{t+1}E_t z_{t+1}`
  in the lower block of (9.18)), `eq_9_37` (with `G = D₂₁ + D₂₂M_{t+1}` and
  `A_yy − GA_zy` invertible, the constraint holds iff `y_t = H_z z_t + H_u u_t`), `eq_9_38`
  (`z_{t+1} = A*z_t + B*u_t + ε_{t+1}`).
* Step 2: `eq_step2` (the loss is `½z'Q*z + ½u'R*u + z'S*u` with the corrected `Q*, R*, S*`).
* Step 3: `cp_obj_complete_square` and `eq_9_40` (`u = −Fz` is the unique minimiser of (9.39)
  when `R* + βB*'VB*` is positive definite), `eq_9_41` (the minimised value is
  `½z'V_t z + ½v_t` with the book's (9.41) and `v_t = β tr(VΣ) + βv`), `eq_9_42`
  (`y_t = (H_z − H_uF)z_t`).
* `cp_bellman_step` (9.33): one step of the backward induction — given `(V_{t+1}, v_{t+1},
  M_{t+1})`, the pair `(M_t z, −F_t z)` is the unique minimiser of the period-`t` Bellman
  problem over all `(y, u)` satisfying the constraint, with value `J_t(z) = ½z'V_t z + ½v_t`.
* `definition_9_5_1` (`IsMPE`) and `cp_mpe_of_fixed_point`: a fixed point `(V, v, M)` of the
  Step 1–3 map gives a Markov perfect equilibrium `(M, F)` with `J(z) = ½z'Vz + ½v`.

**Corrections.**
* (9.36) omits `D₂₁E_t z_{t+1}`: the lower block of (9.18) is
  `D₂₁E_t z_{t+1} + D₂₂E_t y_{t+1} = …`, so `D_yy M_{t+1}` in `H_zt`, `H_ut` must be
  `G = D₂₁ + D₂₂M_{t+1}`; the book's formulas are right only when `D₂₁ = 0`
  (`eq_9_37_book`, counterexample `eq_9_36_false`). (9.35) also takes `C = I`.
* Step 2: the printed `S*_t = Q_zy H_ut + S_z + H_zt S_y` lacks the transpose (`H_zt'S_y`) and
  the cross term `H_zt'Q_yy H_ut`; the printed `R*_t = R + H_ut'Q_yy H_ut + H_ut'S_y` lacks a
  factor 2 on `H_ut'S_y` (symmetrised: `H_ut'S_y + S_y'H_ut`). Counterexamples:
  `step2_book_S_false`, `step2_book_R_false`. The printed `Q*_t` (with `2Q_zy H_zt`) is right
  as a quadratic form (`cp_Qbook_quad`), but not symmetric; we use the symmetric
  `Q_zy H_zt + H_zt'Q_zy'`.
* (9.41) is right as a quadratic form (`eq_9_41`) but the matrix it defines is not symmetric
  (`−2S*F`); the gain formula (9.40) at the next step presumes `V_{t+1}` symmetric, so the
  iteration must use the symmetrised `cpVnext` (`cp_Vnext_quad`, `cp_Vnext_symm`).
* Definition 9.5.1 (i) speaks of `E_t y_{t+1} = f(z_t)` taken as given; the derivation that
  follows (9.32)–(9.33) has the policymaker take the private sector's *rule* `y_{t+1} =
  M_{t+1}z_{t+1}` as given, so that `u_t` affects `E_t y_{t+1}` through `E_t z_{t+1}`. We
  formalise the definition in the form the derivation uses: the constraint set is
  `G(A_zz z + A_zy y + B_z u) = A_yz z + A_yy y + B_y u`, `G = D₂₁ + D₂₂M` (which is (i)–(ii)
  with `f(z_t) = ME_t z_{t+1}`).
* Convergence of the iteration ("iterating this process until convergence") is not proved in
  the book and is not formalised; `cp_mpe_of_fixed_point` proves that a limit that is a fixed
  point is an equilibrium.
-/

namespace Miao.LinearQuadratic

open scoped Matrix
open MeasureTheory

/-! ### Bilinear-form identities -/

/-- `(Hv)'(Mw) = v'(H'M)w`. -/
theorem cp_dot_left {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (H : Matrix α β ℝ)
    (M : Matrix α γ ℝ) (v : β → ℝ) (w : γ → ℝ) :
    (H *ᵥ v) ⬝ᵥ (M *ᵥ w) = v ⬝ᵥ ((Hᵀ * M) *ᵥ w) := by
  calc (H *ᵥ v) ⬝ᵥ (M *ᵥ w) = (M *ᵥ w) ⬝ᵥ (H *ᵥ v) := dotProduct_comm _ _
    _ = v ⬝ᵥ (Hᵀ *ᵥ (M *ᵥ w)) := cp_dotProduct_mulVec_comm H (M *ᵥ w) v
    _ = v ⬝ᵥ ((Hᵀ * M) *ᵥ w) := by rw [Matrix.mulVec_mulVec]

/-- `v'M'v = v'Mv`. -/
theorem cp_quad_transpose {α : Type*} [Fintype α] (M : Matrix α α ℝ) (v : α → ℝ) :
    v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
  rw [cp_dotProduct_mulVec_comm Mᵀ, Matrix.transpose_transpose]

/-- `u'Nz = z'N'u`. -/
theorem cp_dot_swap {α β : Type*} [Fintype α] [Fintype β] (N : Matrix α β ℝ) (u : α → ℝ)
    (z : β → ℝ) : u ⬝ᵥ (N *ᵥ z) = z ⬝ᵥ (Nᵀ *ᵥ u) :=
  cp_dotProduct_mulVec_comm N u z

/-! ### The model -/

/-- The data of §9.5 (Miao, pp. 311–313): the blocks of `A`, `B`, `D` in (9.18) (with `C = I`),
the blocks of the loss (9.19), the discount factor and the shock covariance `Σ`. -/
structure CPDisc (Z Y U : Type*) where
  /-- `A_zz` -/
  Azz : Matrix Z Z ℝ
  /-- `A_zy` -/
  Azy : Matrix Z Y ℝ
  /-- `A_yz` -/
  Ayz : Matrix Y Z ℝ
  /-- `A_yy` -/
  Ayy : Matrix Y Y ℝ
  /-- `B_z` -/
  Bz : Matrix Z U ℝ
  /-- `B_y` -/
  By : Matrix Y U ℝ
  /-- `D₂₁` -/
  D21 : Matrix Y Z ℝ
  /-- `D₂₂` (the book's `D_yy`) -/
  D22 : Matrix Y Y ℝ
  /-- `Q_zz` -/
  Qzz : Matrix Z Z ℝ
  /-- `Q_zy` -/
  Qzy : Matrix Z Y ℝ
  /-- `Q_yy` -/
  Qyy : Matrix Y Y ℝ
  /-- `R` -/
  R : Matrix U U ℝ
  /-- `S_z` -/
  Sz : Matrix Z U ℝ
  /-- `S_y` -/
  Sy : Matrix Y U ℝ
  /-- the discount factor -/
  β : ℝ
  /-- the covariance matrix `Σ` of `ε` -/
  Sig : Matrix Z Z ℝ

variable {Z Y U : Type*} [Fintype Z] [Fintype Y] [Fintype U]

namespace CPDisc

/-- The period loss in block form (Miao, p. 313, Step 2). -/
noncomputable def loss (P : CPDisc Z Y U) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) : ℝ :=
  (1 / 2) * (z ⬝ᵥ (P.Qzz *ᵥ z)) + (1 / 2) * (y ⬝ᵥ (P.Qyy *ᵥ y)) + z ⬝ᵥ (P.Qzy *ᵥ y) +
    (1 / 2) * (u ⬝ᵥ (P.R *ᵥ u)) + z ⬝ᵥ (P.Sz *ᵥ u) + y ⬝ᵥ (P.Sy *ᵥ u)

/-- `E_t z_{t+1} = A_zz z + A_zy y + B_z u`. -/
def mean (P : CPDisc Z Y U) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) : Z → ℝ :=
  P.Azz *ᵥ z + P.Azy *ᵥ y + P.Bz *ᵥ u

/-- `G = D₂₁ + D₂₂M`: the coefficient of `E_t z_{t+1}` in the lower block of (9.18) once the
public expects `y_{t+1} = Mz_{t+1}`. -/
def G (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y Z ℝ := P.D21 + P.D22 * M

/-- The constraint on `(y_t, u_t)` (Miao, (9.36) as corrected):
`G(A_zz z + A_zy y + B_z u) = A_yz z + A_yy y + B_y u`. -/
def Feasible (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) : Prop :=
  P.G M *ᵥ P.mean z y u = P.Ayz *ᵥ z + P.Ayy *ᵥ y + P.By *ᵥ u

/-- `A_yy − GA_zy`. -/
def K (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y Y ℝ := P.Ayy - P.G M * P.Azy

/-- `H_zt = (A_yy − GA_zy)⁻¹(GA_zz − A_yz)` (Miao, p. 313, with `G = D₂₁ + D₂₂M_{t+1}`). -/
noncomputable def Hz [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y Z ℝ :=
  (P.K M)⁻¹ * (P.G M * P.Azz - P.Ayz)

/-- `H_ut = (A_yy − GA_zy)⁻¹(GB_z − B_y)` (Miao, p. 313). -/
noncomputable def Hu [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) : Matrix Y U ℝ :=
  (P.K M)⁻¹ * (P.G M * P.Bz - P.By)

/-- `A* = A_zz + A_zy H_z`. -/
def Ast (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) : Matrix Z Z ℝ := P.Azz + P.Azy * Hz

/-- `B* = B_z + A_zy H_u`. -/
def Bst (P : CPDisc Z Y U) (Hu : Matrix Y U ℝ) : Matrix Z U ℝ := P.Bz + P.Azy * Hu

/-- `Q* = Q_zz + H_z'Q_yy H_z + Q_zy H_z + H_z'Q_zy'` (symmetric form of the book's
`Q_zz + H_z'Q_yy H_z + 2Q_zy H_z`). -/
def Qst (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) : Matrix Z Z ℝ :=
  P.Qzz + Hzᵀ * P.Qyy * Hz + P.Qzy * Hz + Hzᵀ * P.Qzyᵀ

/-- `R* = R + H_u'Q_yy H_u + H_u'S_y + S_y'H_u` (corrected). -/
def Rst (P : CPDisc Z Y U) (Hu : Matrix Y U ℝ) : Matrix U U ℝ :=
  P.R + Huᵀ * P.Qyy * Hu + Huᵀ * P.Sy + P.Syᵀ * Hu

/-- `S* = Q_zy H_u + S_z + H_z'S_y + H_z'Q_yy H_u` (corrected). -/
def Sst (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) (Hu : Matrix Y U ℝ) : Matrix Z U ℝ :=
  P.Qzy * Hu + P.Sz + Hzᵀ * P.Sy + Hzᵀ * P.Qyy * Hu

end CPDisc

/-- Miao, p. 313 (Step 2, first line): the blockwise loss is (9.19) with
`Q = [Q_zz Q_zy; Q_zy' Q_yy]` and `S = [S_z; S_y]`. -/
theorem cp_disc_loss_eq (P : CPDisc Z Y U) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) :
    P.loss z y u = cpLoss (Matrix.fromBlocks P.Qzz P.Qzy P.Qzyᵀ P.Qyy) (Matrix.fromRows P.Sz P.Sy)
      P.R (Sum.elim z y) u := by
  simp only [CPDisc.loss, cpLoss, Matrix.fromBlocks_mulVec, Matrix.fromRows_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, cp_sumElim_dotProduct, dotProduct_add]
  rw [cp_dotProduct_mulVec_comm P.Qzyᵀ y z, Matrix.transpose_transpose]
  ring

/-! ### The expected continuation value -/

/-- Miao, pp. 312–314: for a probability measure `ν` of the shock `ε` with mean zero and
covariance `Σ` (`∫εᵢεⱼ = Σᵢⱼ`), `E[½(m + ε)'V(m + ε) + ½v] = ½m'Vm + ½tr(VΣ) + ½v`. -/
theorem cp_expected_quadratic (ν : Measure (Z → ℝ)) [IsProbabilityMeasure ν]
    (Sig V : Matrix Z Z ℝ) (m : Z → ℝ) (v : ℝ)
    (hint1 : ∀ i, Integrable (fun e : Z → ℝ => e i) ν)
    (hint2 : ∀ i j, Integrable (fun e : Z → ℝ => e i * e j) ν)
    (hmean : ∀ i, ∫ e, e i ∂ν = 0) (hcov : ∀ i j, ∫ e, e i * e j ∂ν = Sig i j) :
    ∫ e, ((1 / 2) * ((m + e) ⬝ᵥ (V *ᵥ (m + e))) + (1 / 2) * v) ∂ν =
      (1 / 2) * (m ⬝ᵥ (V *ᵥ m)) + (1 / 2) * Matrix.trace (V * Sig) + (1 / 2) * v := by
  have hterm : ∀ i j, (fun e : Z → ℝ => (m + e) i * (V i j * (m + e) j)) =
      fun e => m i * V i j * m j + (m i * V i j) * e j + (V i j * m j) * e i +
        V i j * (e i * e j) := fun i j => by
    funext e
    simp only [Pi.add_apply]
    ring
  have hint : ∀ i j, Integrable (fun e : Z → ℝ => (m + e) i * (V i j * (m + e) j)) ν :=
    fun i j => by
      rw [hterm]
      exact (((integrable_const _).add ((hint1 j).const_mul _)).add
        ((hint1 i).const_mul _)).add ((hint2 i j).const_mul _)
  have hval : ∀ i j, ∫ e, (m + e) i * (V i j * (m + e) j) ∂ν = m i * V i j * m j +
      V i j * Sig i j := fun i j => by
    have i1 : Integrable (fun _ : Z → ℝ => m i * V i j * m j) ν := integrable_const _
    have i2 : Integrable (fun e : Z → ℝ => m i * V i j * e j) ν := (hint1 j).const_mul _
    have i3 : Integrable (fun e : Z → ℝ => V i j * m j * e i) ν := (hint1 i).const_mul _
    have i4 : Integrable (fun e : Z → ℝ => V i j * (e i * e j)) ν := (hint2 i j).const_mul _
    have i12 : Integrable (fun e : Z → ℝ => m i * V i j * m j + m i * V i j * e j) ν :=
      i1.add i2
    have i123 : Integrable (fun e : Z → ℝ => m i * V i j * m j + m i * V i j * e j +
        V i j * m j * e i) ν := i12.add i3
    rw [hterm, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_const,
      integral_const_mul, integral_const_mul, integral_const_mul, hmean, hmean, hcov]
    simp
  have hsym : ∀ i j, Sig i j = Sig j i := fun i j => by
    rw [← hcov, ← hcov]
    simp_rw [mul_comm]
  have hdot : (fun e : Z → ℝ => (1 / 2) * ((m + e) ⬝ᵥ (V *ᵥ (m + e))) + (1 / 2) * v) =
      fun e => (1 / 2) * ∑ i, ∑ j, (m + e) i * (V i j * (m + e) j) + (1 / 2) * v := by
    funext e
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hiint : ∀ i, Integrable (fun e : Z → ℝ => ∑ j, (m + e) i * (V i j * (m + e) j)) ν :=
    fun i => integrable_finsetSum _ fun j _ => hint i j
  have hq : m ⬝ᵥ (V *ᵥ m) = ∑ i, ∑ j, m i * V i j * m j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have htr : Matrix.trace (V * Sig) = ∑ i, ∑ j, V i j * Sig i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
  have hint' : Integrable (fun e : Z → ℝ => ∑ i, ∑ j, (m + e) i * (V i j * (m + e) j)) ν :=
    integrable_finsetSum _ fun i _ => hiint i
  rw [hdot, integral_add (hint'.const_mul _) (integrable_const _), integral_const_mul,
    integral_finsetSum _ fun i _ => hiint i, integral_const]
  simp only [fun i => integral_finsetSum _ fun j (_ : j ∈ Finset.univ) => hint i j, hval,
    Finset.sum_add_distrib, probReal_univ, one_smul, hq, htr]
  ring

/-! ### Step 1 -/

/-- Miao, (9.35)–(9.36), p. 312: if the public expects `y_{t+1} = Mz_{t+1}` and
`E_t z_{t+1} = A_zz z + A_zy y + B_z u` (the upper block of (9.18), `E_tε_{t+1} = 0`), the
lower block `D₂₁E_t z_{t+1} + D₂₂E_t y_{t+1} = A_yz z + A_yy y + B_y u` is the constraint
`Feasible`. -/
theorem eq_9_35_36 (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ)
    (Ez' : Z → ℝ) (Ey' : Y → ℝ) (hz : Ez' = P.mean z y u) (hy : Ey' = M *ᵥ Ez') :
    (P.D21 *ᵥ Ez' + P.D22 *ᵥ Ey' = P.Ayz *ᵥ z + P.Ayy *ᵥ y + P.By *ᵥ u) ↔
      P.Feasible M z y u := by
  rw [CPDisc.Feasible, CPDisc.G, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← hz, ← hy]

/-- Miao, (9.37), p. 313 (with `G = D₂₁ + D₂₂M_{t+1}`): if `A_yy − GA_zy` is invertible, the
constraint holds iff `y_t = H_z z_t + H_u u_t`. -/
theorem eq_9_37 [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ)
    (hK : IsUnit (P.K M).det) (z : Z → ℝ) (y : Y → ℝ) (u : U → ℝ) :
    P.Feasible M z y u ↔ y = P.Hz M *ᵥ z + P.Hu M *ᵥ u := by
  have key : P.K M *ᵥ y - ((P.G M * P.Azz - P.Ayz) *ᵥ z + (P.G M * P.Bz - P.By) *ᵥ u) =
      (P.Ayz *ᵥ z + P.Ayy *ᵥ y + P.By *ᵥ u) - P.G M *ᵥ P.mean z y u := by
    simp only [CPDisc.K, CPDisc.mean, Matrix.sub_mulVec, Matrix.mulVec_add,
      ← Matrix.mulVec_mulVec]
    abel
  have h1 : P.Feasible M z y u ↔
      P.K M *ᵥ y = (P.G M * P.Azz - P.Ayz) *ᵥ z + (P.G M * P.Bz - P.By) *ᵥ u := by
    rw [CPDisc.Feasible]
    constructor
    · intro h
      rw [h, sub_self] at key
      exact sub_eq_zero.1 key
    · intro h
      rw [h, sub_self] at key
      exact (sub_eq_zero.1 key.symm).symm
  rw [h1, CPDisc.Hz, CPDisc.Hu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_add]
  constructor
  · intro h
    rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hK, Matrix.one_mulVec]
  · intro h
    rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hK, Matrix.one_mulVec]

omit [Fintype U] in
/-- Miao, p. 313: when `D₂₁ = 0`, `H_z` and `H_u` are the book's
`(A_yy − D_yy M A_zy)⁻¹(D_yy M A_zz − A_yz)` and `(A_yy − D_yy M A_zy)⁻¹(D_yy M B_z − B_y)`. -/
theorem eq_9_37_book [DecidableEq Y] (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (h21 : P.D21 = 0) :
    P.Hz M = (P.Ayy - P.D22 * M * P.Azy)⁻¹ * (P.D22 * M * P.Azz - P.Ayz) ∧
      P.Hu M = (P.Ayy - P.D22 * M * P.Azy)⁻¹ * (P.D22 * M * P.Bz - P.By) := by
  simp only [CPDisc.Hz, CPDisc.Hu, CPDisc.K, CPDisc.G, h21, zero_add, and_self]

/-- The data of the counterexample to (9.36): `D₂₁ = D₂₂ = A_zz = A_yy = 1`, all else zero. -/
def cpDiscEx : CPDisc (Fin 1) (Fin 1) (Fin 1) where
  Azz := 1
  Azy := 0
  Ayz := 0
  Ayy := 1
  Bz := 0
  By := 0
  D21 := 1
  D22 := 1
  Qzz := 0
  Qzy := 0
  Qyy := 0
  R := 0
  Sz := 0
  Sy := 0
  β := 0
  Sig := 0

/-- Correction to (9.36) (Miao, p. 312): dropping `D₂₁E_t z_{t+1}` is wrong when `D₂₁ ≠ 0`. With
`cpDiscEx` and `M = 0`, the book's rule `y = (A_yy − D_yy M A_zy)⁻¹(D_yy M A_zz − A_yz)z +
(A_yy − D_yy M A_zy)⁻¹(D_yy M B_z − B_y)u` gives `y = 0` at `z = u = 1`, which violates the
constraint, while `y = 1` satisfies it. -/
theorem eq_9_36_false :
    let P := cpDiscEx
    let O : Matrix (Fin 1) (Fin 1) ℝ := 0
    let ybook := ((P.Ayy - P.D22 * O * P.Azy)⁻¹ * (P.D22 * O * P.Azz - P.Ayz)) *ᵥ (fun _ => 1) +
      ((P.Ayy - P.D22 * O * P.Azy)⁻¹ * (P.D22 * O * P.Bz - P.By)) *ᵥ (fun _ => 1)
    ¬ P.Feasible O (fun _ => 1) ybook (fun _ => 1) ∧ P.Feasible O (fun _ => 1) (fun _ => 1)
      (fun _ => 1) := by
  intro P O ybook
  have hy : ybook = 0 := by
    funext i
    simp [ybook, P, O, cpDiscEx]
  refine ⟨?_, ?_⟩
  · rw [hy]
    intro h
    have := congrFun h 0
    simp [P, O, cpDiscEx, CPDisc.mean, CPDisc.G, Matrix.mulVec, dotProduct] at this
  · funext i
    fin_cases i
    simp [P, O, cpDiscEx, CPDisc.mean, CPDisc.G, Matrix.mulVec, dotProduct]

/-- Miao, (9.38), p. 313: substituting `y = H_z z + H_u u` into the upper block,
`E_t z_{t+1} = A*z + B*u`. -/
theorem eq_9_38 (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) (Hu : Matrix Y U ℝ) (z : Z → ℝ)
    (u : U → ℝ) : P.mean z (Hz *ᵥ z + Hu *ᵥ u) u = P.Ast Hz *ᵥ z + P.Bst Hu *ᵥ u := by
  simp only [CPDisc.mean, CPDisc.Ast, CPDisc.Bst, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel

/-! ### Step 2 -/

/-- Miao, p. 313 (Step 2, as corrected): with `Q_yy` symmetric and `y = H_z z + H_u u`, the
loss is `½z'Q*z + ½u'R*u + z'S*u`. -/
theorem eq_step2 (P : CPDisc Z Y U) (hQ : P.Qyyᵀ = P.Qyy) (Hz : Matrix Y Z ℝ)
    (Hu : Matrix Y U ℝ) (z : Z → ℝ) (u : U → ℝ) :
    P.loss z (Hz *ᵥ z + Hu *ᵥ u) u = (1 / 2) * (z ⬝ᵥ (P.Qst Hz *ᵥ z)) +
      (1 / 2) * (u ⬝ᵥ (P.Rst Hu *ᵥ u)) + z ⬝ᵥ (P.Sst Hz Hu *ᵥ u) := by
  have e1 : u ⬝ᵥ ((Huᵀ * (P.Qyy * Hz)) *ᵥ z) = z ⬝ᵥ ((Hzᵀ * (P.Qyy * Hu)) *ᵥ u) := by
    rw [cp_dot_swap]
    congr 2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hQ,
      Matrix.mul_assoc]
  have e2 : z ⬝ᵥ ((Hzᵀ * P.Qzyᵀ) *ᵥ z) = z ⬝ᵥ ((P.Qzy * Hz) *ᵥ z) := by
    rw [← cp_quad_transpose (P.Qzy * Hz), Matrix.transpose_mul]
  have e3 : u ⬝ᵥ ((P.Syᵀ * Hu) *ᵥ u) = u ⬝ᵥ ((Huᵀ * P.Sy) *ᵥ u) := by
    rw [← cp_quad_transpose (Huᵀ * P.Sy), Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [CPDisc.loss, CPDisc.Qst, CPDisc.Rst, CPDisc.Sst, Matrix.add_mulVec,
    Matrix.mulVec_add, dotProduct_add, add_dotProduct, cp_dot_left, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]
  rw [e1, e2, e3]
  ring

/-- The book's `Q*_t = Q_zz + H_z'Q_yy H_z + 2Q_zy H_z` (Miao, p. 313). -/
def CPDisc.Qbook (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) : Matrix Z Z ℝ :=
  P.Qzz + Hzᵀ * P.Qyy * Hz + (2 : ℝ) • (P.Qzy * Hz)

omit [Fintype U] in
/-- Miao, p. 313: the book's `Q*` has the same quadratic form as the symmetric `Q*`. -/
theorem cp_Qbook_quad (P : CPDisc Z Y U) (Hz : Matrix Y Z ℝ) (z : Z → ℝ) :
    z ⬝ᵥ (P.Qbook Hz *ᵥ z) = z ⬝ᵥ (P.Qst Hz *ᵥ z) := by
  have e2 : z ⬝ᵥ ((Hzᵀ * P.Qzyᵀ) *ᵥ z) = z ⬝ᵥ ((P.Qzy * Hz) *ᵥ z) := by
    rw [← cp_quad_transpose (P.Qzy * Hz), Matrix.transpose_mul]
  simp only [CPDisc.Qbook, CPDisc.Qst, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, e2, smul_eq_mul]
  ring

/-- The printed data of the Step 2 counterexamples, `Q_yy` and `S_y` free. -/
def cpDiscEx2 (qyy sy : ℝ) : CPDisc (Fin 1) (Fin 1) (Fin 1) where
  Azz := 0
  Azy := 0
  Ayz := 0
  Ayy := 0
  Bz := 0
  By := 0
  D21 := 0
  D22 := 0
  Qzz := 0
  Qzy := 0
  Qyy := Matrix.of fun _ _ => qyy
  R := 0
  Sz := 0
  Sy := Matrix.of fun _ _ => sy
  β := 0
  Sig := 0

/-- Correction to Step 2 (Miao, p. 313): the printed `S* = Q_zy H_u + S_z + H_z'S_y` misses
`H_z'Q_yy H_u`. With `Q_yy = 1`, `H_z = H_u = 1`, all else zero, at `z = u = 1` the loss is `2`
but the printed `½z'Q*z + ½u'R*u + z'S*u` is `1`. -/
theorem step2_book_S_false :
    let P := cpDiscEx2 1 0
    let H : Matrix (Fin 1) (Fin 1) ℝ := 1
    let o : Fin 1 → ℝ := fun _ => 1
    P.loss o (H *ᵥ o + H *ᵥ o) o = 2 ∧
      (1 / 2) * (o ⬝ᵥ (P.Qbook H *ᵥ o)) +
        (1 / 2) * (o ⬝ᵥ ((P.R + Hᵀ * P.Qyy * H + Hᵀ * P.Sy) *ᵥ o)) +
        o ⬝ᵥ ((P.Qzy * H + P.Sz + Hᵀ * P.Sy) *ᵥ o) = 1 := by
  intro P H o
  constructor
  · simp [P, H, o, cpDiscEx2, CPDisc.loss, Matrix.mulVec, dotProduct]
    norm_num
  · simp [P, H, o, cpDiscEx2, CPDisc.Qbook, Matrix.mulVec, dotProduct]
    norm_num

/-- Correction to Step 2 (Miao, p. 313): the printed `R* = R + H_u'Q_yy H_u + H_u'S_y` misses a
factor 2 on `H_u'S_y`. With `S_y = 1`, `H_z = 0`, `H_u = 1`, all else zero, at `z = 0`, `u = 1`
the loss is `1` but the printed form gives `½`. -/
theorem step2_book_R_false :
    let P := cpDiscEx2 0 1
    let Hu : Matrix (Fin 1) (Fin 1) ℝ := 1
    let o : Fin 1 → ℝ := fun _ => 1
    P.loss 0 (Hu *ᵥ o) o = 1 ∧
      (1 / 2) * ((0 : Fin 1 → ℝ) ⬝ᵥ (P.Qbook 0 *ᵥ 0)) +
        (1 / 2) * (o ⬝ᵥ ((P.R + Huᵀ * P.Qyy * Hu + Huᵀ * P.Sy) *ᵥ o)) +
        (0 : Fin 1 → ℝ) ⬝ᵥ ((P.Qzy * Hu + P.Sz) *ᵥ o) = 1 / 2 := by
  intro P Hu o
  constructor
  · simp [P, Hu, o, cpDiscEx2, CPDisc.loss, Matrix.mulVec, dotProduct]
  · simp [P, Hu, o, cpDiscEx2, Matrix.mulVec, dotProduct]

/-! ### Step 3 -/

/-- The objective of (9.39) (Miao, p. 314), with `E_t J_{t+1}(z_{t+1})` evaluated by
`cp_expected_quadratic`: `½z'Q*z + ½u'R*u + z'S*u + β[½m'Vm + ½tr(VΣ) + ½v]`,
`m = A*z + B*u`. -/
noncomputable def cpObj (β : ℝ) (Sig : Matrix Z Z ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ)
    (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (v : ℝ)
    (z : Z → ℝ) (u : U → ℝ) : ℝ :=
  (1 / 2) * (z ⬝ᵥ (Qs *ᵥ z)) + (1 / 2) * (u ⬝ᵥ (Rs *ᵥ u)) + z ⬝ᵥ (Ss *ᵥ u) +
    β * ((1 / 2) * ((As *ᵥ z + Bs *ᵥ u) ⬝ᵥ (V *ᵥ (As *ᵥ z + Bs *ᵥ u))) +
      (1 / 2) * Matrix.trace (V * Sig) + (1 / 2) * v)

/-- `R* + βB*'VB*`. -/
def cpGain (β : ℝ) (Rs : Matrix U U ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) :
    Matrix U U ℝ :=
  Rs + β • (Bsᵀ * V * Bs)

/-- `F = (R* + βB*'VB*)⁻¹(S*' + βB*'VA*)` (Miao, (9.40), p. 314). -/
noncomputable def cpF [DecidableEq U] (β : ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) : Matrix U Z ℝ :=
  (cpGain β Rs Bs V)⁻¹ * (Ssᵀ + β • (Bsᵀ * V * As))

/-- The objective (9.39) is `½u'Gu + u'(S*' + βB*'VA*)z + c(z)`, `G = R* + βB*'VB*`. -/
theorem cp_obj_expand {β : ℝ} (Sig Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (v : ℝ)
    (z : Z → ℝ) (u : U → ℝ) :
    cpObj β Sig Qs Rs Ss As Bs V v z u =
      (1 / 2) * (u ⬝ᵥ (cpGain β Rs Bs V *ᵥ u)) + u ⬝ᵥ ((Ssᵀ + β • (Bsᵀ * V * As)) *ᵥ z) +
        ((1 / 2) * (z ⬝ᵥ (Qs *ᵥ z)) + β * ((1 / 2) * ((As *ᵥ z) ⬝ᵥ (V *ᵥ (As *ᵥ z))) +
          (1 / 2) * Matrix.trace (V * Sig) + (1 / 2) * v)) := by
  have e1 : (As *ᵥ z) ⬝ᵥ (V *ᵥ (Bs *ᵥ u)) = (Bs *ᵥ u) ⬝ᵥ (V *ᵥ (As *ᵥ z)) := by
    rw [cp_dotProduct_mulVec_comm, hV, dotProduct_comm]
  have e2 : z ⬝ᵥ (Ss *ᵥ u) = u ⬝ᵥ (Ssᵀ *ᵥ z) := cp_dot_swap Ss z u
  simp only [cpObj, cpGain, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_eq_mul, e1, e2]
  rw [cp_dot_left Bs V u (Bs *ᵥ u), cp_dot_left Bs V u (As *ᵥ z)]
  simp only [Matrix.mulVec_mulVec]
  ring

/-- **Completing the square in (9.39)** (Miao, p. 314). With `V`, `R*` symmetric and
`G = R* + βB*'VB*` invertible, the objective is `obj(u) = obj(−Fz) + ½(u + Fz)'G(u + Fz)`. -/
theorem cp_obj_complete_square [DecidableEq U] {β : ℝ} (Sig Qs : Matrix Z Z ℝ)
    {Rs : Matrix U U ℝ} (hR : Rsᵀ = Rs) (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ)
    (Bs : Matrix Z U ℝ) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (hG : IsUnit (cpGain β Rs Bs V).det)
    (v : ℝ) (z : Z → ℝ) (u : U → ℝ) :
    cpObj β Sig Qs Rs Ss As Bs V v z u =
      cpObj β Sig Qs Rs Ss As Bs V v z (-(cpF β Rs Ss As Bs V *ᵥ z)) +
        (1 / 2) * ((u + cpF β Rs Ss As Bs V *ᵥ z) ⬝ᵥ
          (cpGain β Rs Bs V *ᵥ (u + cpF β Rs Ss As Bs V *ᵥ z))) := by
  set G := cpGain β Rs Bs V with hGdef
  set w := cpF β Rs Ss As Bs V *ᵥ z
  have hGs : Gᵀ = G := by
    rw [hGdef, cpGain, Matrix.transpose_add, Matrix.transpose_smul, hR, Matrix.transpose_mul,
      Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hGw : G *ᵥ w = (Ssᵀ + β • (Bsᵀ * V * As)) *ᵥ z := by
    simp only [w, cpF, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← hGdef,
      Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hwu : w ⬝ᵥ (G *ᵥ u) = u ⬝ᵥ ((Ssᵀ + β • (Bsᵀ * V * As)) *ᵥ z) := by
    rw [cp_dotProduct_mulVec_symm hGs, dotProduct_comm, hGw]
  rw [cp_obj_expand Sig Qs Rs Ss As Bs hV v z u, cp_obj_expand Sig Qs Rs Ss As Bs hV v z (-w)]
  simp only [← hGdef, Matrix.mulVec_neg, Matrix.mulVec_add, neg_dotProduct, dotProduct_neg,
    add_dotProduct, dotProduct_add, hGw, hwu]
  ring

/-- Miao, (9.40), p. 314: if `V` and `R*` are symmetric and `R* + βB*'VB*` is positive
definite, `u = −Fz` is the unique minimiser of the objective (9.39). -/
theorem eq_9_40 [DecidableEq U] {β : ℝ} (Sig Qs : Matrix Z Z ℝ) {Rs : Matrix U U ℝ}
    (hR : Rsᵀ = Rs) (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ)
    {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (hG : (cpGain β Rs Bs V).PosDef) (v : ℝ) (z : Z → ℝ) :
    (∀ u, cpObj β Sig Qs Rs Ss As Bs V v z (-(cpF β Rs Ss As Bs V *ᵥ z)) ≤
      cpObj β Sig Qs Rs Ss As Bs V v z u) ∧
    ∀ u, cpObj β Sig Qs Rs Ss As Bs V v z u =
      cpObj β Sig Qs Rs Ss As Bs V v z (-(cpF β Rs Ss As Bs V *ᵥ z)) →
        u = -(cpF β Rs Ss As Bs V *ᵥ z) := by
  have hGu : IsUnit (cpGain β Rs Bs V).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
  have hpos : ∀ x : U → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (cpGain β Rs Bs V *ᵥ x) := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hnn : ∀ x : U → ℝ, 0 ≤ x ⬝ᵥ (cpGain β Rs Bs V *ᵥ x) := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  refine ⟨fun u => ?_, fun u hu => ?_⟩
  · rw [cp_obj_complete_square Sig Qs hR Ss As Bs hV hGu v z u]
    have := hnn (u + cpF β Rs Ss As Bs V *ᵥ z)
    linarith
  · rw [cp_obj_complete_square Sig Qs hR Ss As Bs hV hGu v z u] at hu
    by_contra hne
    have hx : u + cpF β Rs Ss As Bs V *ᵥ z ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
    have := hpos _ hx
    linarith

/-- The book's (9.41) (Miao, p. 314):
`V_t = Q* + F'R*F − 2S*F + β(A* − B*F)'V_{t+1}(A* − B*F)`. -/
def cpVbook (β : ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (F : Matrix U Z ℝ) :
    Matrix Z Z ℝ :=
  Qs + Fᵀ * Rs * F - (2 : ℝ) • (Ss * F) + β • ((As - Bs * F)ᵀ * V * (As - Bs * F))

/-- The symmetrised (9.41): `Q* + F'R*F − S*F − F'S*' + β(A* − B*F)'V(A* − B*F)`. -/
def cpVnext (β : ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (F : Matrix U Z ℝ) :
    Matrix Z Z ℝ :=
  Qs + Fᵀ * Rs * F - (Ss * F + Fᵀ * Ssᵀ) + β • ((As - Bs * F)ᵀ * V * (As - Bs * F))

/-- Miao, (9.41) and the recursion for `v_t`, p. 314: at `u = −Fz` the objective (9.39) equals
`½z'V_t z + ½v_t` with the book's `V_t` and `v_t = β tr(V_{t+1}Σ) + βv_{t+1}`. -/
theorem eq_9_41 (β : ℝ) (Sig Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (v : ℝ) (F : Matrix U Z ℝ)
    (z : Z → ℝ) :
    cpObj β Sig Qs Rs Ss As Bs V v z (-(F *ᵥ z)) =
      (1 / 2) * (z ⬝ᵥ (cpVbook β Qs Rs Ss As Bs V F *ᵥ z)) +
        (1 / 2) * (β * Matrix.trace (V * Sig) + β * v) := by
  have e1 : As *ᵥ z + Bs *ᵥ -(F *ᵥ z) = (As - Bs * F) *ᵥ z := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_neg, sub_eq_add_neg]
  have e2 : ((As - Bs * F) *ᵥ z) ⬝ᵥ (V *ᵥ ((As - Bs * F) *ᵥ z)) =
      z ⬝ᵥ (((As - Bs * F)ᵀ * V * (As - Bs * F)) *ᵥ z) := by
    rw [cp_dot_left, Matrix.mulVec_mulVec]
  have e3 : (F *ᵥ z) ⬝ᵥ ((Rs * F) *ᵥ z) = z ⬝ᵥ ((Fᵀ * Rs * F) *ᵥ z) := by
    rw [cp_dot_left, Matrix.mul_assoc]
  rw [cpObj, e1, e2]
  simp only [cpVbook, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, Matrix.mulVec_neg, neg_dotProduct,
    dotProduct_neg, neg_neg, Matrix.mulVec_mulVec, e3, smul_eq_mul]
  ring

/-- The symmetrised `V_t` has the same quadratic form as the book's (9.41). -/
theorem cp_Vnext_quad (β : ℝ) (Qs : Matrix Z Z ℝ) (Rs : Matrix U U ℝ) (Ss : Matrix Z U ℝ)
    (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ) (V : Matrix Z Z ℝ) (F : Matrix U Z ℝ)
    (z : Z → ℝ) :
    z ⬝ᵥ (cpVnext β Qs Rs Ss As Bs V F *ᵥ z) = z ⬝ᵥ (cpVbook β Qs Rs Ss As Bs V F *ᵥ z) := by
  have e : z ⬝ᵥ ((Fᵀ * Ssᵀ) *ᵥ z) = z ⬝ᵥ ((Ss * F) *ᵥ z) := by
    rw [← cp_quad_transpose (Ss * F), Matrix.transpose_mul]
  simp only [cpVnext, cpVbook, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add,
    dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, e, smul_eq_mul]
  ring

/-- The symmetrised `V_t` is symmetric when `Q*`, `R*` and `V_{t+1}` are. -/
theorem cp_Vnext_symm (β : ℝ) {Qs : Matrix Z Z ℝ} (hQ : Qsᵀ = Qs) {Rs : Matrix U U ℝ}
    (hR : Rsᵀ = Rs) (Ss : Matrix Z U ℝ) (As : Matrix Z Z ℝ) (Bs : Matrix Z U ℝ)
    {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (F : Matrix U Z ℝ) :
    (cpVnext β Qs Rs Ss As Bs V F)ᵀ = cpVnext β Qs Rs Ss As Bs V F := by
  simp only [cpVnext, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hQ, hR, hV, Matrix.mul_assoc]
  abel

omit [Fintype Z] [Fintype U] in
/-- `Q*` is symmetric when `Q_zz`, `Q_yy` are. -/
theorem cp_Qst_symm (P : CPDisc Z Y U) (hQz : P.Qzzᵀ = P.Qzz) (hQy : P.Qyyᵀ = P.Qyy)
    (Hz : Matrix Y Z ℝ) : (P.Qst Hz)ᵀ = P.Qst Hz := by
  simp only [CPDisc.Qst, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    hQz, hQy, Matrix.mul_assoc]
  abel

omit [Fintype Z] [Fintype U] in
/-- `R*` is symmetric when `R`, `Q_yy` are. -/
theorem cp_Rst_symm (P : CPDisc Z Y U) (hR : P.Rᵀ = P.R) (hQy : P.Qyyᵀ = P.Qyy)
    (Hu : Matrix Y U ℝ) : (P.Rst Hu)ᵀ = P.Rst Hu := by
  simp only [CPDisc.Rst, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    hR, hQy, Matrix.mul_assoc]
  abel

omit [Fintype Y] in
/-- Miao, (9.42), p. 314: with `u = −Fz`, `y = H_z z + H_u u = (H_z − H_uF)z`. -/
theorem eq_9_42 (Hz : Matrix Y Z ℝ) (Hu : Matrix Y U ℝ) (F : Matrix U Z ℝ) (z : Z → ℝ) :
    Hz *ᵥ z + Hu *ᵥ (-(F *ᵥ z)) = (Hz - Hu * F) *ᵥ z := by
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_neg, sub_eq_add_neg]

/-! ### The Bellman step and Markov perfect equilibrium -/

namespace CPDisc

/-- The right side of the Bellman equations (9.31)/(9.33) with `J_{t+1}(z) = ½z'Vz + ½v`:
`L(z, y, u) + β E_t J_{t+1}(z_{t+1})`, the expectation evaluated by `cp_expected_quadratic`. -/
noncomputable def total (P : CPDisc Z Y U) (V : Matrix Z Z ℝ) (v : ℝ) (z : Z → ℝ) (y : Y → ℝ)
    (u : U → ℝ) : ℝ :=
  P.loss z y u + P.β * ((1 / 2) * (P.mean z y u ⬝ᵥ (V *ᵥ P.mean z y u)) +
    (1 / 2) * Matrix.trace (V * P.Sig) + (1 / 2) * v)

/-- `F_t` of (9.40) for the period-`t` problem given `(V_{t+1}, M_{t+1})`. -/
noncomputable def Fnext [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix U Z ℝ :=
  cpF P.β (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M)) (P.Ast (P.Hz M)) (P.Bst (P.Hu M)) V

/-- `V_t` (symmetrised (9.41)). -/
noncomputable def Vnext [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix Z Z ℝ :=
  cpVnext P.β (P.Qst (P.Hz M)) (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M)) (P.Ast (P.Hz M))
    (P.Bst (P.Hu M)) V (P.Fnext V M)

/-- `M_t = H_z − H_uF_t` (9.42). -/
noncomputable def Mnext [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix Y Z ℝ :=
  P.Hz M - P.Hu M * P.Fnext V M

/-- The gain matrix `R*_t + βB*'V_{t+1}B*`. -/
noncomputable def Gain [DecidableEq Y] (P : CPDisc Z Y U) (V : Matrix Z Z ℝ)
    (M : Matrix Y Z ℝ) : Matrix U U ℝ :=
  cpGain P.β (P.Rst (P.Hu M)) (P.Bst (P.Hu M)) V

end CPDisc

/-- The period-`t` objective is (9.39) once the constraint is used. -/
theorem cp_total_eq [DecidableEq Y] (P : CPDisc Z Y U) (hQy : P.Qyyᵀ = P.Qyy)
    (V : Matrix Z Z ℝ) (v : ℝ) (M : Matrix Y Z ℝ) (z : Z → ℝ) (u : U → ℝ) :
    P.total V v z (P.Hz M *ᵥ z + P.Hu M *ᵥ u) u =
      cpObj P.β P.Sig (P.Qst (P.Hz M)) (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M))
        (P.Ast (P.Hz M)) (P.Bst (P.Hu M)) V v z u := by
  rw [CPDisc.total, eq_step2 P hQy, eq_9_38, cpObj]

/-- **One step of the backward induction** (Miao, (9.33)–(9.42), pp. 312–314). Let `Q_yy`, `R`
and `V_{t+1}` be symmetric, `A_yy − GA_zy` invertible and `R*_t + βB*'V_{t+1}B*` positive
definite. For every `z`, among all `(y, u)` satisfying the constraint given the public's rule
`M_{t+1}`, `(M_t z, −F_t z)` is the unique minimiser of `L + βE_t J_{t+1}`, and the minimum is
`J_t(z) = ½z'V_t z + ½v_t` with `v_t = β tr(V_{t+1}Σ) + βv_{t+1}`. -/
theorem cp_bellman_step [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U)
    (hQy : P.Qyyᵀ = P.Qyy) (hR : P.Rᵀ = P.R) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) (v : ℝ)
    (M : Matrix Y Z ℝ) (hK : IsUnit (P.K M).det) (hG : (P.Gain V M).PosDef) (z : Z → ℝ) :
    P.Feasible M z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) ∧
    (∀ y u, P.Feasible M z y u →
      P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) ≤ P.total V v z y u) ∧
    (∀ y u, P.Feasible M z y u →
      P.total V v z y u = P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) →
        y = P.Mnext V M *ᵥ z ∧ u = -(P.Fnext V M *ᵥ z)) ∧
    P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) =
      (1 / 2) * (z ⬝ᵥ (P.Vnext V M *ᵥ z)) +
        (1 / 2) * (P.β * Matrix.trace (V * P.Sig) + P.β * v) := by
  have hRs := cp_Rst_symm P hR hQy (P.Hu M)
  have hM : P.Mnext V M *ᵥ z = P.Hz M *ᵥ z + P.Hu M *ᵥ (-(P.Fnext V M *ᵥ z)) := by
    rw [eq_9_42]
    rfl
  have hmin := eq_9_40 P.Sig (P.Qst (P.Hz M)) hRs (P.Sst (P.Hz M) (P.Hu M)) (P.Ast (P.Hz M))
    (P.Bst (P.Hu M)) hV hG v z
  have hopt : P.total V v z (P.Mnext V M *ᵥ z) (-(P.Fnext V M *ᵥ z)) =
      cpObj P.β P.Sig (P.Qst (P.Hz M)) (P.Rst (P.Hu M)) (P.Sst (P.Hz M) (P.Hu M))
        (P.Ast (P.Hz M)) (P.Bst (P.Hu M)) V v z (-(P.Fnext V M *ᵥ z)) := by
    rw [hM, cp_total_eq P hQy]
  refine ⟨(eq_9_37 P M hK _ _ _).2 hM, fun y u hf => ?_, fun y u hf heq => ?_, ?_⟩
  · rw [(eq_9_37 P M hK z y u).1 hf, cp_total_eq P hQy, hopt]
    exact hmin.1 u
  · have hy := (eq_9_37 P M hK z y u).1 hf
    rw [hy, cp_total_eq P hQy, hopt] at heq
    have hu := hmin.2 u heq
    refine ⟨?_, hu⟩
    rw [hy, hM, hu]
    rfl
  · rw [hopt, eq_9_41, ← cp_Vnext_quad]
    rfl

/-- **Definition 9.5.1** (Miao, p. 311). The linear rules `y_t = Mz_t`, `u_t = −Fz_t` form a
Markov perfect equilibrium if there is a quadratic value function `J(z) = ½z'Vz + ½v` (`V`
symmetric) such that, for every state `z`, (i) `(Mz, −Fz)` solves the Bellman equation (9.31):
it minimises `L(z, y, u) + βE_t J(z_{t+1})` over all `(y, u)` satisfying (9.18) when the public
expects `E_t y_{t+1} = f(z_t)`, and attains `J(z)`; and (ii) `f(z_t) = ME_t z_{t+1}`, i.e. the
constraint is `Feasible` with the public's rule `M`. -/
def IsMPE (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (F : Matrix U Z ℝ) : Prop :=
  ∃ (V : Matrix Z Z ℝ) (v : ℝ), Vᵀ = V ∧ ∀ z,
    P.Feasible M z (M *ᵥ z) (-(F *ᵥ z)) ∧
    (∀ y u, P.Feasible M z y u → P.total V v z (M *ᵥ z) (-(F *ᵥ z)) ≤ P.total V v z y u) ∧
    (1 / 2) * (z ⬝ᵥ (V *ᵥ z)) + (1 / 2) * v = P.total V v z (M *ᵥ z) (-(F *ᵥ z))

/-- **Definition 9.5.1**, unfolded (Miao, p. 311). -/
theorem definition_9_5_1 (P : CPDisc Z Y U) (M : Matrix Y Z ℝ) (F : Matrix U Z ℝ) :
    IsMPE P M F ↔ ∃ (V : Matrix Z Z ℝ) (v : ℝ), Vᵀ = V ∧ ∀ z,
      P.Feasible M z (M *ᵥ z) (-(F *ᵥ z)) ∧
      (∀ y u, P.Feasible M z y u → P.total V v z (M *ᵥ z) (-(F *ᵥ z)) ≤ P.total V v z y u) ∧
      (1 / 2) * (z ⬝ᵥ (V *ᵥ z)) + (1 / 2) * v = P.total V v z (M *ᵥ z) (-(F *ᵥ z)) :=
  Iff.rfl

/-- **The fixed point of the iteration is an equilibrium** (Miao, pp. 314–315: "Iterating this
process until convergence gives `V` and `M` in a Markov perfect equilibrium"). If
`V = V_t(V, M)`, `M = M_t(V, M)` and `v = β tr(VΣ) + βv` (the fixed points of (9.41), (9.42) and
the `v`-recursion), with the hypotheses of `cp_bellman_step`, then `(M, F(V, M))` is a Markov
perfect equilibrium with `J(z) = ½z'Vz + ½v`. -/
theorem cp_mpe_of_fixed_point [DecidableEq Y] [DecidableEq U] (P : CPDisc Z Y U)
    (hQy : P.Qyyᵀ = P.Qyy) (hR : P.Rᵀ = P.R) {V : Matrix Z Z ℝ} (hV : Vᵀ = V) {v : ℝ}
    {M : Matrix Y Z ℝ} (hK : IsUnit (P.K M).det) (hG : (P.Gain V M).PosDef)
    (hVfix : P.Vnext V M = V) (hMfix : P.Mnext V M = M)
    (hvfix : v = P.β * Matrix.trace (V * P.Sig) + P.β * v) :
    IsMPE P M (P.Fnext V M) := by
  refine ⟨V, v, hV, fun z => ?_⟩
  obtain ⟨h1, h2, -, h4⟩ := cp_bellman_step P hQy hR hV v M hK hG z
  rw [hMfix] at h1 h2 h4
  refine ⟨h1, h2, ?_⟩
  rw [h4, hVfix, ← hvfix]

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian model under discretion: Example 9.5.1, and commitment versus discretion

Miao, §9.5, p. 315 (Example 9.5.1), with the comparison to Example 9.4.2 (pp. 308–311).
Throughout `θ = λ/(κ² + λ)`.

* `eq_9_43`: for `λ > 0`, the static problem `min ½π² + (λ/2)(x − x*)²` subject to
  `π = κx + βπᵉ + z` has the unique solution with `π = θ(κx* + βπᵉ + z)` (9.43).
* `IsMPE951`, `example_9_5_1`: a Markov perfect equilibrium is a pair `π(z)`, `πᵉ(z)` with
  `π(z) = θ(κx* + βπᵉ(z) + z)` and `πᵉ(z) = E π(ρz + ε)`; for `0 < β < 1`, `|ρ| ≤ 1` and any
  integrable mean-zero shock, `π(z) = θ(κx*/(1 − βθ) + z/(1 − βθρ))` is one, and it is the
  only one with `π` affine in `z` (`example_9_5_1_unique`).
* `ex951_forward`: every bounded solution of the forward recursion
  `E_tπ_{t+j} = θ(κx* + βE_tπ_{t+j+1} + E_t z_{t+j})` (`E_t z_{t+j} = ρʲz_t`) has
  `π_t = θ∑ⱼ βʲθʲ(κx* + E_t z_{t+j})`, the book's formula; `ex951_series` sums it to the
  closed form above.
* `cp_commitment_vs_discretion` (the comparison of §§9.4–9.5): without cost-push shocks,
  inflation under commitment is `π_t = a^{t+1}κx*/(1 − βa) → 0`, while under discretion it is
  the constant inflation bias `θκx*/(1 − βθ) = λκx*/(κ² + (1 − β)λ)`, nonzero when `κx* ≠ 0`.
-/

namespace Miao.LinearQuadratic

open Filter Topology MeasureTheory

/-- `θ = λ/(κ² + λ)`. -/
noncomputable def ex951θ (κ lam : ℝ) : ℝ := lam / (κ ^ 2 + lam)

theorem ex951θ_pos {κ lam : ℝ} (hlam : 0 < lam) : 0 < ex951θ κ lam :=
  div_pos hlam (by positivity)

theorem ex951θ_le_one {κ lam : ℝ} (hlam : 0 < lam) : ex951θ κ lam ≤ 1 := by
  rw [ex951θ, div_le_one (by positivity)]
  nlinarith [sq_nonneg κ]

/-- Miao, (9.43), p. 315. For `λ > 0`, the problem `min ½π² + (λ/2)(x − x*)²` subject to
`π = κx + βπᵉ + z` (with `πᵉ` taken as given) is solved by
`x̂ = (λx* − κ(βπᵉ + z))/(κ² + λ)`, `π̂ = κx̂ + βπᵉ + z = θ(κx* + βπᵉ + z)`, and by no other
feasible pair. -/
theorem eq_9_43 {κ lam xs β πe z : ℝ} (hlam : 0 < lam) :
    let xh := (lam * xs - κ * (β * πe + z)) / (κ ^ 2 + lam)
    let ph := κ * xh + β * πe + z
    ph = ex951θ κ lam * (κ * xs + β * πe + z) ∧
    ∀ p x, p = κ * x + β * πe + z →
      (1 / 2) * ph ^ 2 + lam / 2 * (xh - xs) ^ 2 ≤ (1 / 2) * p ^ 2 + lam / 2 * (x - xs) ^ 2 ∧
      ((1 / 2) * ph ^ 2 + lam / 2 * (xh - xs) ^ 2 = (1 / 2) * p ^ 2 + lam / 2 * (x - xs) ^ 2 →
        x = xh ∧ p = ph) := by
  intro xh ph
  have hd : κ ^ 2 + lam ≠ 0 := by positivity
  have hsq : ∀ x, (1 / 2) * (κ * x + β * πe + z) ^ 2 + lam / 2 * (x - xs) ^ 2 =
      ((1 / 2) * ph ^ 2 + lam / 2 * (xh - xs) ^ 2) + (κ ^ 2 + lam) / 2 * (x - xh) ^ 2 := by
    intro x
    simp only [ph, xh]
    field_simp
    ring
  refine ⟨?_, fun p x hp => ?_⟩
  · simp only [ph, xh, ex951θ]
    field_simp
    ring
  · rw [hp, hsq x]
    refine ⟨by nlinarith [sq_nonneg (x - xh)], fun h => ?_⟩
    have h2 : (κ ^ 2 + lam) / 2 * (x - xh) ^ 2 = 0 := by linarith
    have h3 : (x - xh) ^ 2 = 0 := by
      rcases mul_eq_zero.1 h2 with h4 | h4
      · exact absurd h4 (by positivity)
      · exact h4
    have hx : x = xh := by nlinarith [sq_nonneg (x - xh)]
    exact ⟨hx, by rw [hx]⟩

/-- **Markov perfect equilibrium of Example 9.5.1** (Miao, p. 315): `π(z) = θ(κx* + βπᵉ(z) + z)`
(9.43 at `πᵉ = πᵉ(z)`) and `πᵉ(z) = E_t π(z_{t+1})` with `z_{t+1} = ρz + ε`, `ε ∼ ν`. -/
def IsMPE951 (β κ lam ρ xs : ℝ) (ν : Measure ℝ) (pf pe : ℝ → ℝ) : Prop :=
  (∀ z, pf z = ex951θ κ lam * (κ * xs + β * pe z + z)) ∧ ∀ z, pe z = ∫ e, pf (ρ * z + e) ∂ν

/-- The discretionary inflation rule `π(z) = θ(κx*/(1 − βθ) + z/(1 − βθρ))`. -/
noncomputable def ex951pi (β κ lam ρ xs z : ℝ) : ℝ :=
  ex951θ κ lam * (κ * xs / (1 - β * ex951θ κ lam) + z / (1 - β * ex951θ κ lam * ρ))

theorem ex951_denoms {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) : 1 - β * ex951θ κ lam ≠ 0 ∧ 1 - β * ex951θ κ lam * ρ ≠ 0 ∧
      |β * ex951θ κ lam| < 1 ∧ |β * ex951θ κ lam * ρ| < 1 := by
  have h0 := ex951θ_pos (κ := κ) hlam
  have h1 := ex951θ_le_one (κ := κ) hlam
  have hb : β * ex951θ κ lam < 1 := by nlinarith
  have hb0 : 0 < β * ex951θ κ lam := mul_pos hβ0 h0
  have hc : |β * ex951θ κ lam * ρ| < 1 := by
    rw [abs_mul, abs_of_pos hb0]
    nlinarith [abs_nonneg ρ]
  refine ⟨by linarith, ?_, by rw [abs_of_pos hb0]; exact hb, hc⟩
  have := (abs_lt.1 hc).2
  linarith

/-- **Example 9.5.1** (Miao, p. 315). For `0 < β < 1`, `λ > 0`, `|ρ| ≤ 1` and an integrable
mean-zero shock, `π(z) = θ(κx*/(1 − βθ) + z/(1 − βθρ))` with
`πᵉ(z) = θ(κx*/(1 − βθ) + ρz/(1 − βθρ))` is a Markov perfect equilibrium. -/
theorem example_9_5_1 {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable (fun e => e) ν)
    (hmean : ∫ e, e ∂ν = 0) :
    IsMPE951 β κ lam ρ xs ν (ex951pi β κ lam ρ xs) (fun z => ex951pi β κ lam ρ xs (ρ * z)) := by
  obtain ⟨hd1, hd2, -, -⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  refine ⟨fun z => ?_, fun z => ?_⟩
  · have hA := inv_mul_cancel₀ hd1
    have hB := inv_mul_cancel₀ hd2
    simp only [ex951pi]
    linear_combination ex951θ κ lam * κ * xs * hA + ex951θ κ lam * z * hB
  · have h : ∀ e, ex951pi β κ lam ρ xs (ρ * z + e) =
        ex951pi β κ lam ρ xs (ρ * z) + (ex951θ κ lam / (1 - β * ex951θ κ lam * ρ)) * e :=
      fun e => by
        simp only [ex951pi]
        ring
    simp only [h]
    rw [integral_add (integrable_const _) (hint.const_mul _), integral_const, integral_const_mul,
      hmean]
    simp

/-- **Uniqueness among affine rules** (Example 9.5.1). If `π(z) = c₀ + c₁z` is part of a
Markov perfect equilibrium, then `π` is the rule of `example_9_5_1`. -/
theorem example_9_5_1_unique {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable (fun e => e) ν)
    (hmean : ∫ e, e ∂ν = 0) (c0 c1 : ℝ) (pe : ℝ → ℝ)
    (h : IsMPE951 β κ lam ρ xs ν (fun z => c0 + c1 * z) pe) :
    ∀ z, c0 + c1 * z = ex951pi β κ lam ρ xs z := by
  obtain ⟨hd1, hd2, -, -⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  obtain ⟨h1, h2⟩ := h
  have hpe : ∀ z, pe z = c0 + c1 * (ρ * z) := fun z => by
    rw [h2 z]
    have : ∀ e, c0 + c1 * (ρ * z + e) = (c0 + c1 * (ρ * z)) + c1 * e := fun e => by ring
    simp only [this]
    rw [integral_add (integrable_const _) (hint.const_mul _), integral_const,
      integral_const_mul, hmean]
    simp
  set θ := ex951θ κ lam
  have e0 := h1 0
  have e1 := h1 1
  rw [hpe] at e0 e1
  have hc0 : c0 = θ * (κ * xs) / (1 - β * θ) := by
    rw [eq_div_iff hd1]
    linarith
  have hc1 : c1 = θ / (1 - β * θ * ρ) := by
    rw [eq_div_iff hd2]
    linarith
  intro z
  rw [hc0, hc1, ex951pi]
  field_simp
  ring

/-- Miao, p. 315: the book's series sums to the closed form,
`θ∑ⱼ βʲθʲ(κx* + ρʲz) = θ(κx*/(1 − βθ) + z/(1 − βθρ))`. -/
theorem ex951_series {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (z : ℝ) :
    ex951θ κ lam * ∑' j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * z) =
      ex951pi β κ lam ρ xs z := by
  obtain ⟨hd1, hd2, h1, h2⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  have hterm : ∀ j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * z) =
      κ * xs * (β * ex951θ κ lam) ^ j + z * (β * ex951θ κ lam * ρ) ^ j := fun j => by
    rw [mul_pow, mul_pow]
    ring
  rw [tsum_congr hterm, ((summable_geometric_of_abs_lt_one h1).mul_left _).tsum_add
      ((summable_geometric_of_abs_lt_one h2).mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one h1, tsum_geometric_of_abs_lt_one h2, ex951pi]
  ring

/-- Miao, p. 315 ("we can then solve for the discretionary inflation rate"): if
`p_j = E_tπ_{t+j}` is bounded and satisfies `p_j = θ(κx* + βp_{j+1} + ρʲz)` (9.43 with
`πᵉ = E_tπ_{t+j+1}` and `E_t z_{t+j} = ρʲz`), then `p₀ = θ∑ⱼ βʲθʲ(κx* + ρʲz)`. -/
theorem ex951_forward {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (z : ℝ) (p : ℕ → ℝ) (hp : ∀ j, p j =
      ex951θ κ lam * (κ * xs + β * p (j + 1) + ρ ^ j * z)) (hb : ∃ M, ∀ j, |p j| ≤ M) :
    p 0 = ex951θ κ lam * ∑' j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * z) := by
  obtain ⟨-, -, h1, h2⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  set θ := ex951θ κ lam
  set f : ℕ → ℝ := fun j => β ^ j * θ ^ j * (κ * xs + ρ ^ j * z) with hf
  have hsum : Summable f := by
    have : f = fun j => κ * xs * (β * θ) ^ j + z * (β * θ * ρ) ^ j := by
      funext j
      simp only [hf, mul_pow]
      ring
    rw [this]
    exact ((summable_geometric_of_abs_lt_one h1).mul_left _).add
      ((summable_geometric_of_abs_lt_one h2).mul_left _)
  have hiter : ∀ n, p 0 = θ * ∑ j ∈ Finset.range n, f j + (β * θ) ^ n * p n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, Finset.sum_range_succ, hp n]
      simp only [hf]
      ring
  obtain ⟨M, hM⟩ := hb
  have hrem : Tendsto (fun n => (β * θ) ^ n * p n) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => |β * θ| ^ n * M) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h1).mul_const M
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM n) (pow_nonneg (abs_nonneg _) _)
  have hlim : Tendsto (fun n => θ * ∑ j ∈ Finset.range n, f j + (β * θ) ^ n * p n) atTop
      (𝓝 (θ * ∑' j, f j + 0)) :=
    (hsum.hasSum.tendsto_sum_nat.const_mul θ).add hrem
  have hconst : Tendsto (fun n => θ * ∑ j ∈ Finset.range n, f j + (β * θ) ^ n * p n) atTop
      (𝓝 (p 0)) := by
    simp only [← hiter]
    exact tendsto_const_nhds
  rw [add_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

/-- **Commitment versus discretion** (Miao, §§9.4–9.5). Let `κ ≠ 0`, `λ > 0`, `0 < β < 1`,
`a = ex942a` the stable root of (9.29), and no cost-push shocks (`z ≡ 0`). Under commitment
(`μ_{x0} = 0`, the rule of Example 9.4.2, `π_t = β(μ_{xt} − μ_{x,t+1})`) inflation is
`π_t = a^{t+1}κx*/(1 − βa)`, which tends to `0`; under discretion it is the constant
`θκx*/(1 − βθ) = λκx*/(κ² + (1 − β)λ)` at every date, nonzero whenever `κx* ≠ 0`. -/
theorem cp_commitment_vs_discretion {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hκ : κ ≠ 0) (ρ : ℝ) (μ : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs (ex942a β κ lam) (μ t) 0) :
    (∀ t, β * (μ t - μ (t + 1)) =
        ex942a β κ lam ^ (t + 1) * (κ * xs / (1 - β * ex942a β κ lam))) ∧
      Tendsto (fun t => β * (μ t - μ (t + 1))) atTop (𝓝 0) ∧
      ex951pi β κ lam ρ xs 0 = lam * κ * xs / (κ ^ 2 + (1 - β) * lam) ∧
      (κ * xs ≠ 0 → ex951pi β κ lam ρ xs 0 ≠ 0) := by
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  set a := ex942a β κ lam
  have hd : 1 - β * a ≠ 0 := by nlinarith
  have h1a : 1 - a ≠ 0 := by linarith
  set K := κ * xs / (1 - β * a)
  set mbar := -(a / β) * K / (1 - a)
  have hclosed : ∀ t, μ t = mbar * (1 - a ^ t) := by
    intro t
    induction t with
    | zero => simp [hμ0]
    | succ n ih =>
      rw [hμ n, ih, ex942Rule]
      simp only [mbar, K]
      field_simp
      ring
  have hpi : ∀ t, β * (μ t - μ (t + 1)) = a ^ (t + 1) * K := by
    intro t
    rw [hclosed, hclosed]
    simp only [mbar]
    field_simp
    ring
  refine ⟨hpi, ?_, ?_, fun hk => ?_⟩
  · simp only [hpi]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).comp (tendsto_add_atTop_nat 1)
    simpa using this.mul_const K
  · have hθd : κ ^ 2 + lam ≠ 0 := by positivity
    have hden : κ ^ 2 + (1 - β) * lam ≠ 0 := by nlinarith [sq_nonneg κ]
    simp only [ex951pi, ex951θ]
    field_simp
    ring
  · obtain ⟨hd1, -, -, -⟩ := ex951_denoms (κ := κ) (ρ := 0) hβ0 hβ1 hlam (by simp)
    simp only [ex951pi, zero_div, add_zero]
    exact mul_ne_zero (ex951θ_pos hlam).ne' (div_ne_zero hk hd1)

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Belief distortions and entropy

Miao, §9.6, pp. 316–319 ("Belief Distortions and Entropy" and (9.45)–(9.46)). The reference
model is a probability space `(Ω, μ)` with the filtration `ℱ_t = σ(x₀, ε^t)`. A belief
distortion is a sequence of one-step likelihood ratios `m_{t+1} = π̂(ε_{t+1}|ε^t)/π(ε_{t+1})`,
`ℱ_{t+1}`-measurable, nonnegative, with `E[m_{t+1}|ε^t] = 1` (`RCRatios`; we also assume them
bounded, see below). Then `M_t = ∏_{j ≤ t} m_j` (`rcM`) and `Q_t = M_t · μ` (`rcQ`).

* `rc_lr_mean_one` (p. 317): `∫ (π̂(ε|ε^t)/π(ε)) π(ε) dε = 1`.
* `rcM_succ`: `M_{t+1} = m_{t+1}M_t`; `rc_martingale`: `{M_t}` is a martingale.
* `rc_distorted_integral` (p. 317): `E^Q φ = E[M_tφ]`; `rcQ_isProbability`; the distorted
  measures are consistent across horizons (`rc_distorted_consistent`).
* `rc_rnDeriv`, `rc_relEntropy`: `dQ/dP|_{ℱ_t} = M_t` and `E^Q[ln dQ/dP] = E[M_t ln M_t]`.
* `rc_entropy_nonneg`, `rc_entropy_eq_zero_iff`, `rcQ_eq_iff`: relative entropy is nonnegative
  and zero iff `M_t = 1` a.e. iff `Q = P`.
* `rc_entropy_decomp` (p. 317): `E[M_t ln M_t] = ∑_{j<t} E[M_j E(m_{j+1} ln m_{j+1}|ε^j)]`, each
  term nonnegative (`rc_increment_nonneg`).
* `rc_discounted_entropy` (p. 318): `(1 − β)∑βʲE[M_j ln M_j] = β∑βʲE[M_jE(m_{j+1} ln m_{j+1}|ε^j)]`
  (the abstract summation identity is `rc_discounted_sum`); the entropy constraint (9.45) is
  `rcEntropyConstraint`.
* `eq_9_46` (p. 319): the multiplier objective under `Q` equals
  `E∑βᵗM_t(r_t + βθE(m_{t+1} ln m_{t+1}|ε^t))`, over a finite horizon `T` (with `Q = Q_T`).

Departures: the ratios are assumed bounded (`m_{t+1} ≤ K`), which makes every expectation
finite; the book's Gaussian worst-case ratios are unbounded, but the general statements here are
the book's identities, which it uses without integrability conditions. The objective (9.46) is
treated over a finite horizon: `Q` on the whole path space (a projective limit of the `Q_T`) is not
constructed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real

namespace Miao.LinearQuadratic

/-- Miao, p. 317: the one-step likelihood ratio `m(ε) = π̂(ε|h)/π(ε)` of a density `π̂(·|h)`
with respect to a positive density `π` has mean one under `π`: `∫ (π̂/π) π = 1`. -/
theorem rc_lr_mean_one {H Eps : Type*} [MeasurableSpace Eps] (ν : Measure Eps)
    (dens : Eps → ℝ) (dhat : H → Eps → ℝ) (hpos : ∀ e, 0 < dens e)
    (hint : ∀ h, ∫ e, dhat h e ∂ν = 1) (h : H) :
    ∫ e, dhat h e / dens e * dens e ∂ν = 1 := by
  have : (fun e => dhat h e / dens e * dens e) = dhat h :=
    funext fun e => div_mul_cancel₀ _ (hpos e).ne'
  rw [this]
  exact hint h

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The one-step likelihood ratios of a belief distortion (Miao, p. 317): `m_{t+1}` is
`ℱ_{t+1}`-measurable, `0 ≤ m_{t+1} ≤ K` and `E[m_{t+1}|ℱ_t] = 1`. -/
structure RCRatios (μ : Measure Ω) (ℱ : Filtration ℕ m0) (m : ℕ → Ω → ℝ) (K : ℝ) : Prop where
  meas : ∀ t, Measurable[ℱ (t + 1)] (m (t + 1))
  nonneg : ∀ t ω, 0 ≤ m (t + 1) ω
  le : ∀ t ω, m (t + 1) ω ≤ K
  mean : ∀ t, μ[m (t + 1) | ℱ t] =ᵐ[μ] 1

/-- The likelihood ratio of the distorted joint density, `M_t = ∏_{j<t} m_{j+1}`, `M_0 = 1`. -/
def rcM (m : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := ∏ j ∈ Finset.range t, m (j + 1) ω

/-- Miao, p. 317: `M_0 = 1`. -/
theorem rcM_zero (m : ℕ → Ω → ℝ) : rcM m 0 = 1 := by
  funext ω
  simp [rcM]

/-- Miao, p. 317: `M_{t+1} = m_{t+1}M_t`. -/
theorem rcM_succ (m : ℕ → Ω → ℝ) (t : ℕ) : rcM m (t + 1) = fun ω => m (t + 1) ω * rcM m t ω := by
  funext ω
  simp [rcM, Finset.prod_range_succ, mul_comm]

variable {μ : Measure Ω} {ℱ : Filtration ℕ m0} {m : ℕ → Ω → ℝ} {K : ℝ}

theorem RCRatios.K_nonneg (hm : RCRatios μ ℱ m K) (ω : Ω) : 0 ≤ K :=
  (hm.nonneg 0 ω).trans (hm.le 0 ω)

theorem rcM_measurable (hm : RCRatios μ ℱ m K) (t : ℕ) : Measurable[ℱ t] (rcM m t) := by
  induction t with
  | zero => rw [rcM_zero]; exact measurable_const
  | succ t ih =>
    rw [rcM_succ]
    exact (hm.meas t).mul (ih.mono (ℱ.mono (Nat.le_succ t)) le_rfl)

theorem rcM_nonneg (hm : RCRatios μ ℱ m K) (t : ℕ) (ω : Ω) : 0 ≤ rcM m t ω :=
  Finset.prod_nonneg fun j _ => hm.nonneg j ω

theorem rcM_le (hm : RCRatios μ ℱ m K) (t : ℕ) (ω : Ω) : rcM m t ω ≤ K ^ t := by
  calc rcM m t ω = ∏ j ∈ Finset.range t, m (j + 1) ω := rfl
    _ ≤ ∏ _j ∈ Finset.range t, K :=
        Finset.prod_le_prod₀ (fun j _ => hm.nonneg j ω) (fun j _ => hm.le j ω)
    _ = K ^ t := by simp

/-- `|x ln x| ≤ 1 + c²` for `0 ≤ x ≤ c`. -/
theorem rc_abs_mul_log_le {x c : ℝ} (hx : 0 ≤ x) (hxc : x ≤ c) : |x * log x| ≤ 1 + c ^ 2 := by
  have h1 : x - 1 ≤ x * log x := by
    have := InformationTheory.klFun_nonneg hx
    rw [InformationTheory.klFun_apply] at this
    linarith
  have h2 : x * log x ≤ x * (x - 1) := by
    rcases hx.eq_or_lt with h | h
    · subst h; simp
    · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) hx
  rw [abs_le]
  constructor <;> nlinarith

theorem rc_integrable_of_bound [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (c : ℝ)
    (hc : ∀ ω, |f ω| ≤ c) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable c
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hc ω)

theorem rc_m_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (m (t + 1)) μ :=
  rc_integrable_of_bound ((hm.meas t).mono (ℱ.le _) le_rfl) K
    fun ω => by rw [abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω

theorem rcM_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (rcM m t) μ :=
  rc_integrable_of_bound ((rcM_measurable hm t).mono (ℱ.le _) le_rfl) (K ^ t)
    fun ω => by rw [abs_of_nonneg (rcM_nonneg hm t ω)]; exact rcM_le hm t ω

theorem rcM_bound (hm : RCRatios μ ℱ m K) (t : ℕ) : ∀ᵐ ω ∂μ, ‖rcM m t ω‖ ≤ K ^ t :=
  Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rcM_nonneg hm t ω)]; exact rcM_le hm t ω

/-- The one-step property: `E[m_{t+1}ψ] = E[ψ]` for `ℱ_t`-measurable integrable `ψ`. -/
theorem rc_one_step [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) {ψ : Ω → ℝ}
    (hψ : StronglyMeasurable[ℱ t] ψ) (hψi : Integrable ψ μ) :
    ∫ ω, m (t + 1) ω * ψ ω ∂μ = ∫ ω, ψ ω ∂μ := by
  have hmi := rc_m_integrable hm t
  have hprod : Integrable (ψ * m (t + 1)) μ :=
    hψi.mul_bdd (c := K) hmi.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω)
  calc ∫ ω, m (t + 1) ω * ψ ω ∂μ = ∫ ω, (ψ * m (t + 1)) ω ∂μ := by
        congr 1; funext ω; simp [mul_comm]
    _ = ∫ ω, (μ[ψ * m (t + 1) | ℱ t]) ω ∂μ := (integral_condExp (ℱ.le t)).symm
    _ = ∫ ω, (ψ * μ[m (t + 1) | ℱ t]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hψ hprod hmi)
    _ = ∫ ω, ψ ω ∂μ := integral_congr_ae ((hm.mean t).mono fun ω h => by simp [h])

/-- Miao, p. 317: the likelihood-ratio process `{M_t}` is a martingale. -/
theorem rc_martingale [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) :
    Martingale (rcM m) ℱ μ := by
  refine martingale_nat (fun t => (rcM_measurable hm t).stronglyMeasurable)
    (fun t => rcM_integrable hm t) fun t => ?_
  have hmi := rc_m_integrable hm t
  have hprod : Integrable (rcM m t * m (t + 1)) μ :=
    (rcM_integrable hm t).mul_bdd (c := K) hmi.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω)
  have h1 : rcM m (t + 1) = rcM m t * m (t + 1) := by
    rw [rcM_succ]; funext ω; simp [mul_comm]
  rw [h1]
  refine ((condExp_mul_of_stronglyMeasurable_left (rcM_measurable hm t).stronglyMeasurable
    hprod hmi).trans ?_).symm
  filter_upwards [hm.mean t] with ω h
  simp [h]

/-- `E[M_Tφ] = E[M_sφ]` for `s ≤ T` and `ℱ_s`-measurable integrable `φ`. -/
theorem rc_tower [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {s T : ℕ} (hsT : s ≤ T)
    {φ : Ω → ℝ} (hφ : StronglyMeasurable[ℱ s] φ) (hφi : Integrable φ μ) :
    ∫ ω, rcM m T ω * φ ω ∂μ = ∫ ω, rcM m s ω * φ ω ∂μ := by
  induction T, hsT using Nat.le_induction with
  | base => rfl
  | succ T hsT ih =>
    rw [← ih]
    have hψ : StronglyMeasurable[ℱ T] (fun ω => rcM m T ω * φ ω) :=
      (rcM_measurable hm T).stronglyMeasurable.mul (hφ.mono (ℱ.mono hsT))
    have hψi : Integrable (fun ω => rcM m T ω * φ ω) μ :=
      hφi.bdd_mul (c := K ^ T) ((rcM_measurable hm T).mono (ℱ.le T) le_rfl).aestronglyMeasurable
        (rcM_bound hm T)
    rw [← rc_one_step hm T hψ hψi, rcM_succ]
    congr 1
    funext ω
    ring

theorem rc_integral_M [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω ∂μ = 1 := by
  have h := rc_tower hm (Nat.zero_le t) (φ := fun _ => 1) stronglyMeasurable_const
    (integrable_const 1)
  simpa [rcM_zero] using h

/-- The distorted measure `Q_t = M_t · μ` on `ℱ_t` (Miao, p. 317). -/
noncomputable def rcQ (μ : Measure Ω) (m : ℕ → Ω → ℝ) (t : ℕ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal (rcM m t ω)

/-- Miao, p. 317: `E^Q φ = E[M_tφ]`. -/
theorem rc_distorted_integral (hm : RCRatios μ ℱ m K) (t : ℕ) (φ : Ω → ℝ) :
    ∫ ω, φ ω ∂(rcQ μ m t) = ∫ ω, rcM m t ω * φ ω ∂μ := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  rw [rcQ, integral_withDensity_eq_integral_toReal_smul hM.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext ω
  rw [ENNReal.toReal_ofReal (rcM_nonneg hm t ω), smul_eq_mul]

/-- `Q_t` is a probability measure. -/
theorem rcQ_isProbability [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    IsProbabilityMeasure (rcQ μ m t) := by
  constructor
  rw [rcQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (rcM_integrable hm t)
      (Eventually.of_forall fun ω => rcM_nonneg hm t ω), rc_integral_M hm t, ENNReal.ofReal_one]

/-- The distorted measures are consistent (Miao, p. 317, "`{M_t}` induces a distorted measure
`Q`"): for `s ≤ T` and `ℱ_s`-measurable `φ`, `E^{Q_T}φ = E^{Q_s}φ`. -/
theorem rc_distorted_consistent [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {s T : ℕ}
    (hsT : s ≤ T) {φ : Ω → ℝ} (hφ : StronglyMeasurable[ℱ s] φ) (hφi : Integrable φ μ) :
    ∫ ω, φ ω ∂(rcQ μ m T) = ∫ ω, φ ω ∂(rcQ μ m s) := by
  rw [rc_distorted_integral hm, rc_distorted_integral hm, rc_tower hm hsT hφ hφi]

/-- Miao, p. 317: `dQ/dP` on `ℱ_t` is `M_t`. -/
theorem rc_rnDeriv [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    (fun ω => ((rcQ μ m t).rnDeriv μ ω).toReal) =ᵐ[μ] rcM m t := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  filter_upwards [Measure.rnDeriv_withDensity μ hM.ennreal_ofReal] with ω h
  simp only [rcQ, h, ENNReal.toReal_ofReal (rcM_nonneg hm t ω)]

/-- Miao, p. 317: relative entropy `E^Q[ln dQ/dP] = E[M_t ln M_t]`. -/
theorem rc_relEntropy [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, log ((rcQ μ m t).rnDeriv μ ω).toReal ∂(rcQ μ m t) =
      ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
  have hac : rcQ μ m t ≪ μ := withDensity_absolutelyContinuous _ _
  have h1 : (fun ω => ((rcQ μ m t).rnDeriv μ ω).toReal) =ᵐ[rcQ μ m t] rcM m t :=
    hac.ae_eq (rc_rnDeriv hm t)
  rw [integral_congr_ae (g := fun ω => log (rcM m t ω)) (by filter_upwards [h1] with ω h; rw [h]),
    rc_distorted_integral hm t]

theorem rc_MlogM_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (fun ω => rcM m t ω * log (rcM m t ω)) μ := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  exact rc_integrable_of_bound (hM.mul hM.log) (1 + (K ^ t) ^ 2)
    fun ω => rc_abs_mul_log_le (rcM_nonneg hm t ω) (rcM_le hm t ω)

/-- Miao, p. 317: relative entropy is nonnegative, `E[M_t ln M_t] ≥ 0`. -/
theorem rc_entropy_nonneg [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    0 ≤ ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
  have h : ∫ ω, (rcM m t ω - 1) ∂μ ≤ ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
    refine integral_mono ((rcM_integrable hm t).sub (integrable_const 1))
      (rc_MlogM_integrable hm t) fun ω => ?_
    have := InformationTheory.klFun_nonneg (rcM_nonneg hm t ω)
    rw [InformationTheory.klFun_apply] at this
    simp only
    linarith
  rwa [integral_sub (rcM_integrable hm t) (integrable_const 1), rc_integral_M hm t,
    integral_const, probReal_univ, one_smul, sub_self] at h

/-- Miao, p. 317: relative entropy is zero iff `M_t = 1` (a.e.). -/
theorem rc_entropy_eq_zero_iff [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ = 0 ↔ rcM m t =ᵐ[μ] 1 := by
  have hkl : Integrable (fun ω => InformationTheory.klFun (rcM m t ω)) μ := by
    simp only [InformationTheory.klFun_apply]
    exact ((rc_MlogM_integrable hm t).add (integrable_const 1)).sub (rcM_integrable hm t)
  have hint : ∫ ω, InformationTheory.klFun (rcM m t ω) ∂μ =
      ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ := by
    simp only [InformationTheory.klFun_apply]
    rw [integral_sub (f := fun ω => rcM m t ω * log (rcM m t ω) + 1)
      ((rc_MlogM_integrable hm t).add (integrable_const 1)) (rcM_integrable hm t),
      integral_add (f := fun ω => rcM m t ω * log (rcM m t ω)) (rc_MlogM_integrable hm t)
        (integrable_const 1), rc_integral_M hm t,
      integral_const, probReal_univ, one_smul]
    ring
  constructor
  · intro h
    rw [← hint, integral_eq_zero_iff_of_nonneg
      (fun ω => InformationTheory.klFun_nonneg (rcM_nonneg hm t ω)) hkl] at h
    filter_upwards [h] with ω hω
    exact (InformationTheory.klFun_eq_zero_iff (rcM_nonneg hm t ω)).1 hω
  · intro h
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by filter_upwards [h] with ω hω; simp [hω]),
      integral_zero]

/-- Miao, p. 317: `Q = P` (on `ℱ_t`) iff `M_t = 1` a.e. -/
theorem rcQ_eq_iff [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    rcQ μ m t = μ ↔ rcM m t =ᵐ[μ] 1 := by
  have hM : Measurable (rcM m t) := (rcM_measurable hm t).mono (ℱ.le t) le_rfl
  have hfin : ∫⁻ ω, ENNReal.ofReal (rcM m t ω) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (rcM_integrable hm t)
      (Eventually.of_forall fun ω => rcM_nonneg hm t ω)]
    exact ENNReal.ofReal_ne_top
  have h := withDensity_eq_iff (μ := μ) hM.ennreal_ofReal.aemeasurable
    (aemeasurable_const (b := (1 : ENNReal))) hfin
  have e : (μ.withDensity fun _ => (1 : ENNReal)) = μ := withDensity_one
  rw [e] at h
  rw [rcQ, h]
  constructor
  · intro h'
    filter_upwards [h'] with ω hω
    have h0 := rcM_nonneg hm t ω
    rw [ENNReal.ofReal_eq_one] at hω
    simp [hω]
  · intro h'
    filter_upwards [h'] with ω hω
    simp [hω]

/-- The conditional relative entropy integrand `m_{t+1} ln m_{t+1}`. -/
noncomputable def rcG (m : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := m (t + 1) ω * log (m (t + 1) ω)

theorem rcG_measurable (hm : RCRatios μ ℱ m K) (t : ℕ) : Measurable (rcG m t) := by
  have h := (hm.meas t).mono (ℱ.le _) le_rfl
  exact h.mul h.log

theorem rcG_abs_le (hm : RCRatios μ ℱ m K) (t : ℕ) (ω : Ω) : |rcG m t ω| ≤ 1 + K ^ 2 :=
  rc_abs_mul_log_le (hm.nonneg t ω) (hm.le t ω)

theorem rcG_integrable [IsFiniteMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    Integrable (rcG m t) μ :=
  rc_integrable_of_bound (rcG_measurable hm t) _ (rcG_abs_le hm t)

/-- `E[M_tE(m_{t+1} ln m_{t+1}|ε^t)] = E[M_t m_{t+1} ln m_{t+1}]`. -/
theorem rc_increment_eq [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ = ∫ ω, rcM m t ω * rcG m t ω ∂μ := by
  have hfg : Integrable (rcM m t * rcG m t) μ :=
    (rcG_integrable hm t).bdd_mul (c := K ^ t)
      ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (rcM_bound hm t)
  calc ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ = ∫ ω, (rcM m t * μ[rcG m t | ℱ t]) ω ∂μ := rfl
    _ = ∫ ω, (μ[rcM m t * rcG m t | ℱ t]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left
          (rcM_measurable hm t).stronglyMeasurable hfg (rcG_integrable hm t)).symm
    _ = ∫ ω, (rcM m t * rcG m t) ω ∂μ := integral_condExp (ℱ.le t)
    _ = ∫ ω, rcM m t ω * rcG m t ω ∂μ := rfl

/-- Miao, p. 318: each conditional relative-entropy term is nonnegative,
`E[M_tE(m_{t+1} ln m_{t+1}|ε^t)] ≥ 0`. -/
theorem rc_increment_nonneg [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    0 ≤ ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ := by
  rw [rc_increment_eq hm t]
  have hMi := rcM_integrable hm t
  have hM1 := rcM_integrable hm (t + 1)
  have hfg : Integrable (fun ω => rcM m t ω * rcG m t ω) μ :=
    (rcG_integrable hm t).bdd_mul (c := K ^ t)
      ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (rcM_bound hm t)
  have h : ∫ ω, (rcM m (t + 1) ω - rcM m t ω) ∂μ ≤ ∫ ω, rcM m t ω * rcG m t ω ∂μ := by
    refine integral_mono (hM1.sub hMi) hfg fun ω => ?_
    have := InformationTheory.klFun_nonneg (hm.nonneg t ω)
    rw [InformationTheory.klFun_apply] at this
    rw [rcM_succ]
    simp only [rcG]
    nlinarith [rcM_nonneg hm t ω]
  rwa [integral_sub hM1 hMi, rc_integral_M hm, rc_integral_M hm, sub_self] at h

/-- Miao, p. 317: the decomposition of relative entropy,
`E[M_t ln M_t] = ∑_{j<t} E[M_j E(m_{j+1} ln m_{j+1}|ε^j)]`. -/
theorem rc_entropy_decomp [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (t : ℕ) :
    ∫ ω, rcM m t ω * log (rcM m t ω) ∂μ =
      ∑ j ∈ Finset.range t, ∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ := by
  induction t with
  | zero => simp [rcM_zero]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih, rc_increment_eq hm t]
    have key : ∀ ω, rcM m (t + 1) ω * log (rcM m (t + 1) ω) =
        m (t + 1) ω * (rcM m t ω * log (rcM m t ω)) + rcM m t ω * rcG m t ω := by
      intro ω
      rw [rcM_succ]
      simp only [rcG]
      by_cases ha : m (t + 1) ω = 0
      · simp [ha]
      by_cases hb : rcM m t ω = 0
      · simp [hb]
      rw [Real.log_mul ha hb]
      ring
    have hψ : StronglyMeasurable[ℱ t] (fun ω => rcM m t ω * log (rcM m t ω)) :=
      ((rcM_measurable hm t).mul (rcM_measurable hm t).log).stronglyMeasurable
    have h1 : Integrable (fun ω => m (t + 1) ω * (rcM m t ω * log (rcM m t ω))) μ :=
      (rc_MlogM_integrable hm t).bdd_mul (c := K) (rc_m_integrable hm t).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hm.nonneg t ω)]; exact hm.le t ω)
    have h2 : Integrable (fun ω => rcM m t ω * rcG m t ω) μ :=
      (rcG_integrable hm t).bdd_mul (c := K ^ t)
        ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (rcM_bound hm t)
    simp_rw [key]
    rw [integral_add h1 h2, rc_one_step hm t hψ (rc_MlogM_integrable hm t)]

/-- The summation identity behind (9.45) (Miao, p. 318): for `e_j = ∑_{i<j} c_i` with bounded
`c` and `0 ≤ β < 1`, `(1 − β)∑βʲe_j = β∑βʲc_j`, both series converging. -/
theorem rc_discounted_sum {β C : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c : ℕ → ℝ}
    (hc : ∀ j, |c j| ≤ C) :
    Summable (fun j => β ^ j * ∑ i ∈ Finset.range j, c i) ∧ Summable (fun j => β ^ j * c j) ∧
      (1 - β) * ∑' j, β ^ j * ∑ i ∈ Finset.range j, c i = β * ∑' j, β ^ j * c j := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hc 0)
  have he : ∀ j, |∑ i ∈ Finset.range j, c i| ≤ j * C := by
    intro j
    calc |∑ i ∈ Finset.range j, c i| ≤ ∑ i ∈ Finset.range j, |c i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.range j, C := Finset.sum_le_sum fun i _ => hc i
      _ = j * C := by simp
  have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1
  have hs1 : Summable (fun j => β ^ j * ∑ i ∈ Finset.range j, c i) := by
    refine Summable.of_norm_bounded
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_left C) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), pow_one]
    calc β ^ j * |∑ i ∈ Finset.range j, c i| ≤ β ^ j * (j * C) :=
          mul_le_mul_of_nonneg_left (he j) (pow_nonneg hβ0 j)
      _ = C * ((j : ℝ) * β ^ j) := by ring
  have hs2 : Summable (fun j => β ^ j * c j) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left C)
      fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j)]
    calc β ^ j * |c j| ≤ β ^ j * C := mul_le_mul_of_nonneg_left (hc j) (pow_nonneg hβ0 j)
      _ = C * β ^ j := by ring
  refine ⟨hs1, hs2, ?_⟩
  have hpart : ∀ n, (1 - β) * ∑ j ∈ Finset.range n, β ^ j * ∑ i ∈ Finset.range j, c i +
      β ^ n * ∑ i ∈ Finset.range n, c i = β * ∑ j ∈ Finset.range n, β ^ j * c j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => β ^ j * c j),
        Finset.sum_range_succ c]
      linear_combination ih
  have hrem : Tendsto (fun n => β ^ n * ∑ i ∈ Finset.range n, c i) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (by simpa using (tendsto_self_mul_const_pow_of_lt_one hβ0 hβ1).mul_const C)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n)]
      calc β ^ n * |∑ i ∈ Finset.range n, c i| ≤ β ^ n * (n * C) :=
            mul_le_mul_of_nonneg_left (he n) (pow_nonneg hβ0 n)
        _ = (n : ℝ) * β ^ n * C := by ring
  have hL : Tendsto (fun n => (1 - β) * ∑ j ∈ Finset.range n, β ^ j * ∑ i ∈ Finset.range j, c i +
      β ^ n * ∑ i ∈ Finset.range n, c i) atTop
      (𝓝 ((1 - β) * ∑' j, β ^ j * ∑ i ∈ Finset.range j, c i + 0)) :=
    (hs1.hasSum.tendsto_sum_nat.const_mul _).add hrem
  have hR : Tendsto (fun n => β * ∑ j ∈ Finset.range n, β ^ j * c j) atTop
      (𝓝 (β * ∑' j, β ^ j * c j)) := hs2.hasSum.tendsto_sum_nat.const_mul _
  rw [add_zero] at hL
  exact tendsto_nhds_unique (hL.congr hpart) hR

/-- Miao, p. 318: discounted entropy,
`(1 − β)∑βʲE[M_j ln M_j] = β∑βʲE[M_jE(m_{j+1} ln m_{j+1}|ε^j)]`. -/
theorem rc_discounted_entropy [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (1 - β) * ∑' j, β ^ j * ∫ ω, rcM m j ω * log (rcM m j ω) ∂μ =
      β * ∑' j, β ^ j * ∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ := by
  have hc : ∀ j, |∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ| ≤ 1 + K ^ 2 := by
    intro j
    rw [rc_increment_eq hm j]
    have h2 : Integrable (fun ω => rcM m j ω * rcG m j ω) μ :=
      (rcG_integrable hm j).bdd_mul (c := K ^ j)
        ((rcM_measurable hm j).mono (ℱ.le j) le_rfl).aestronglyMeasurable (rcM_bound hm j)
    calc |∫ ω, rcM m j ω * rcG m j ω ∂μ| ≤ ∫ ω, |rcM m j ω * rcG m j ω| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, rcM m j ω * (1 + K ^ 2) ∂μ := by
          refine integral_mono h2.abs ((rcM_integrable hm j).mul_const _) fun ω => ?_
          rw [abs_mul, abs_of_nonneg (rcM_nonneg hm j ω)]
          exact mul_le_mul_of_nonneg_left (rcG_abs_le hm j ω) (rcM_nonneg hm j ω)
      _ = 1 + K ^ 2 := by rw [integral_mul_const, rc_integral_M hm, one_mul]
  have h := (rc_discounted_sum hβ0 hβ1 hc).2.2
  simp_rw [rc_entropy_decomp hm]
  exact h

/-- The discounted entropy `β∑_{j≥0}βʲE[M_jE(m_{j+1} ln m_{j+1}|ε^j)]` of (9.45). -/
noncomputable def rcDiscEntropy (μ : Measure Ω) (ℱ : Filtration ℕ m0) (m : ℕ → Ω → ℝ) (β : ℝ) :
    ℝ :=
  β * ∑' j, β ^ j * ∫ ω, rcM m j ω * (μ[rcG m j | ℱ j]) ω ∂μ

/-- The entropy constraint (9.45) (Miao, p. 318): discounted entropy at most `η₀`. -/
def rcEntropyConstraint (μ : Measure Ω) (ℱ : Filtration ℕ m0) (m : ℕ → Ω → ℝ) (β η₀ : ℝ) :
    Prop :=
  rcDiscEntropy μ ℱ m β ≤ η₀

/-- Discounted entropy is nonnegative, so (9.45) with `η₀ = 0` forces no distortion of any
conditional law (Miao, p. 318). -/
theorem rc_discEntropy_nonneg [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) {β : ℝ}
    (hβ0 : 0 ≤ β) : 0 ≤ rcDiscEntropy μ ℱ m β :=
  mul_nonneg hβ0 (tsum_nonneg fun j => mul_nonneg (pow_nonneg hβ0 j) (rc_increment_nonneg hm j))

/-- `E[M_T ∑_{t<T} φ_t] = ∑_{t<T} E[M_tφ_t]` for adapted integrable `φ`. -/
theorem rc_tower_sum [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (T : ℕ)
    (φ : ℕ → Ω → ℝ) (hφ : ∀ t, StronglyMeasurable[ℱ t] (φ t)) (hφi : ∀ t, Integrable (φ t) μ) :
    ∫ ω, rcM m T ω * ∑ t ∈ Finset.range T, φ t ω ∂μ =
      ∑ t ∈ Finset.range T, ∫ ω, rcM m t ω * φ t ω ∂μ := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun t _ => (hφi t).bdd_mul (c := K ^ T)
    ((rcM_measurable hm T).mono (ℱ.le T) le_rfl).aestronglyMeasurable (rcM_bound hm T)]
  refine Finset.sum_congr rfl fun t ht => ?_
  exact rc_tower hm (Finset.mem_range.1 ht).le (hφ t) (hφi t)

/-- (9.46) (Miao, p. 319), over a finite horizon `T`: the multiplier objective
`E^Q∑βᵗr_t + βθE^Q∑βᵗE(m_{t+1} ln m_{t+1}|ε^t)` equals
`E∑βᵗM_t(r_t + βθE(m_{t+1} ln m_{t+1}|ε^t))`, with `Q = Q_T`. -/
theorem eq_9_46 [IsProbabilityMeasure μ] (hm : RCRatios μ ℱ m K) (T : ℕ) (β θ : ℝ)
    (r : ℕ → Ω → ℝ) (hr : ∀ t, StronglyMeasurable[ℱ t] (r t)) (hri : ∀ t, Integrable (r t) μ) :
    ∫ ω, ∑ t ∈ Finset.range T, β ^ t * r t ω ∂(rcQ μ m T) +
        β * θ * ∫ ω, ∑ t ∈ Finset.range T, β ^ t * (μ[rcG m t | ℱ t]) ω ∂(rcQ μ m T) =
      ∑ t ∈ Finset.range T,
        ∫ ω, β ^ t * rcM m t ω * (r t ω + β * θ * (μ[rcG m t | ℱ t]) ω) ∂μ := by
  have hc : ∀ t, StronglyMeasurable[ℱ t] (μ[rcG m t | ℱ t]) := fun t => stronglyMeasurable_condExp
  have hci : ∀ t, Integrable (μ[rcG m t | ℱ t]) μ := fun t => integrable_condExp
  rw [rc_distorted_integral hm, rc_distorted_integral hm,
    rc_tower_sum hm T (fun t ω => β ^ t * r t ω) (fun t => (hr t).const_mul _)
      (fun t => (hri t).const_mul _),
    rc_tower_sum hm T (fun t ω => β ^ t * (μ[rcG m t | ℱ t]) ω) (fun t => (hc t).const_mul _)
      (fun t => (hci t).const_mul _), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : Integrable (fun ω => rcM m t ω * r t ω) μ :=
    (hri t).bdd_mul (c := K ^ t) ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable
      (rcM_bound hm t)
  have h2 : Integrable (fun ω => rcM m t ω * (μ[rcG m t | ℱ t]) ω) μ :=
    (hci t).bdd_mul (c := K ^ t) ((rcM_measurable hm t).mono (ℱ.le t) le_rfl).aestronglyMeasurable
      (rcM_bound hm t)
  have e : ∀ ω, β ^ t * rcM m t ω * (r t ω + β * θ * (μ[rcG m t | ℱ t]) ω) =
      β ^ t * (rcM m t ω * r t ω) + β * θ * β ^ t * (rcM m t ω * (μ[rcG m t | ℱ t]) ω) := by
    intro ω; ring
  simp_rw [e]
  rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
  have e1 : ∫ ω, rcM m t ω * (β ^ t * r t ω) ∂μ = β ^ t * ∫ ω, rcM m t ω * r t ω ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  have e2 : ∫ ω, rcM m t ω * (β ^ t * (μ[rcG m t | ℱ t]) ω) ∂μ =
      β ^ t * ∫ ω, rcM m t ω * (μ[rcG m t | ℱ t]) ω ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  rw [e1, e2]
  ring

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The constraint and multiplier problems

Miao, §9.6, pp. 318–320 ("Two Robust Control Problems" and the start of "Recursive
Formulation"). The problems are stated abstractly: a control `u` (a plan `{u_t}`) and a belief
distortion `m` (a sequence `{m_{t+1}}`) give the expected discounted reward `J u m` under the
distorted belief, and the distortion has discounted entropy `ent m ≥ 0` (the left side of
(9.45)), with `ent m₀ = 0` for the reference model `m₀ = 1`.

* The constraint problem: `max_u min_{ent m ≤ η} J u m`; the multiplier problem:
  `max_u min_m (J u m + θ ent m)` (`rcMultObj`).
* `rc_lagrange` (p. 319, "θ as the Lagrange multiplier associated with (9.45)"): a minimiser of the
  multiplier objective satisfying complementary slackness `θ(ent m* − η) = 0` solves the
  constraint problem, with value `min(J + θ ent) − θη`; `rc_weak_duality`: for every `θ ≥ 0`,
  `min_m(J + θ ent) − θη` is a lower bound for the constrained value.
* `rc_mult_mono`, `rc_mult_le_ref` (p. 319): the multiplier value increases with `θ` (a smaller
  `θ` means more concern about misspecification), and never exceeds the reference value.
* `rc_mult_tendsto` (p. 319, "when `θ → ∞` the multiplier problem converges to the standard control
  problem under `P`"): under a Pinsker-type bound `|J u m − J u m₀| ≤ c√(ent m)` the inner value is
  within `c²/(4θ)` of `J u m₀`, and the robust value converges to the standard one.
* `rc_bellman_scale`, `rc_bellman_divide` (p. 320): the conjecture `W(M, x) = MV(x)`: for `M > 0`,
  `MV(x) = max_u min_m M·g(u, m)` iff `V(x) = max_u min_m g(u, m)`; `rc_min_add` pulls the reward
  `r(x, u)`, which does not depend on `m`, out of the minimisation.

Departure: the convergence as `θ → ∞` needs some continuity of `J` in the distortion; we take the
bound `|J u m − J u m₀| ≤ c√(ent m)` (Pinsker's inequality for bounded rewards) as a hypothesis.
-/

open Filter Topology

namespace Miao.LinearQuadratic

variable {Ctrl Dist : Type*}

/-- The multiplier objective `J(u, m) + θ ent(m)` (Miao, p. 318). -/
def rcMultObj (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (θ : ℝ) (u : Ctrl) (m : Dist) : ℝ :=
  J u m + θ * ent m

/-- Miao, p. 319: `θ` as the Lagrange multiplier of (9.45). If `m*` minimises
`J(u, ·) + θ ent` with `θ ≥ 0`, `ent m* ≤ η` and `θ(ent m* − η) = 0`, then `m*` minimises
`J(u, ·)` subject to the entropy constraint `ent m ≤ η`, and the constrained value is the
multiplier value minus `θη`. -/
theorem rc_lagrange (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) {θ η : ℝ} (hθ : 0 ≤ θ) (u : Ctrl)
    {mstar : Dist} (hmin : ∀ m, rcMultObj J ent θ u mstar ≤ rcMultObj J ent θ u m)
    (hfeas : ent mstar ≤ η) (hcs : θ * (ent mstar - η) = 0) :
    IsLeast ((J u) '' {m | ent m ≤ η}) (J u mstar) ∧
      J u mstar = rcMultObj J ent θ u mstar - θ * η := by
  have hval : J u mstar = rcMultObj J ent θ u mstar - θ * η := by
    simp only [rcMultObj]; linarith
  refine ⟨⟨⟨mstar, hfeas, rfl⟩, ?_⟩, hval⟩
  rintro _ ⟨m, hm, rfl⟩
  have h1 := hmin m
  simp only [rcMultObj] at h1
  have h2 : θ * ent m ≤ θ * η := mul_le_mul_of_nonneg_left hm hθ
  nlinarith

/-- Weak duality (Miao, p. 319): for `θ ≥ 0`, a lower bound `v` of the multiplier objective gives
the lower bound `v − θη` on `J(u, m)` over the constraint set `ent m ≤ η`. -/
theorem rc_weak_duality (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) {θ η v : ℝ} (hθ : 0 ≤ θ)
    (u : Ctrl) (hv : ∀ m, v ≤ rcMultObj J ent θ u m) {m : Dist} (hm : ent m ≤ η) :
    v - θ * η ≤ J u m := by
  have h1 := hv m
  simp only [rcMultObj] at h1
  have h2 : θ * ent m ≤ θ * η := mul_le_mul_of_nonneg_left hm hθ
  linarith

/-- Miao, p. 319: with nonnegative entropy the multiplier value is increasing in `θ`. -/
theorem rc_mult_mono (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (hent : ∀ m, 0 ≤ ent m) (u : Ctrl)
    {θ θ' v v' : ℝ} (hθ : θ ≤ θ') (hv : IsLeast (Set.range (rcMultObj J ent θ u)) v)
    (hv' : IsLeast (Set.range (rcMultObj J ent θ' u)) v') : v ≤ v' := by
  obtain ⟨m, hm⟩ := hv'.1
  rw [← hm]
  refine (hv.2 ⟨m, rfl⟩).trans ?_
  simp only [rcMultObj]
  nlinarith [hent m]

/-- Miao, p. 319: the multiplier value never exceeds the value under the reference model `m₀`
(which has zero entropy). -/
theorem rc_mult_le_ref (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) {m₀ : Dist} (h0 : ent m₀ = 0)
    (u : Ctrl) {θ v : ℝ} (hv : IsLeast (Set.range (rcMultObj J ent θ u)) v) : v ≤ J u m₀ := by
  have := hv.2 ⟨m₀, rfl⟩
  simpa [rcMultObj, h0] using this

/-- The key inequality for `θ → ∞`: `θe − c√e ≥ −c²/(4θ)`. -/
theorem rc_sqrt_penalty {θ c e : ℝ} (hθ : 0 < θ) (he : 0 ≤ e) :
    -(c ^ 2 / (4 * θ)) ≤ θ * e - c * Real.sqrt e := by
  have hs := Real.sq_sqrt he
  have h : 0 ≤ θ * (Real.sqrt e - c / (2 * θ)) ^ 2 := by positivity
  have e1 : θ * (Real.sqrt e - c / (2 * θ)) ^ 2 =
      θ * (Real.sqrt e) ^ 2 - c * Real.sqrt e + c ^ 2 / (4 * θ) := by
    field_simp
    ring
  rw [e1, hs] at h
  linarith

/-- Miao, p. 319: under the Pinsker-type bound `|J u m − J u m₀| ≤ c√(ent m)`, every multiplier
objective value is at least `J u m₀ − c²/(4θ)`. -/
theorem rc_mult_lower (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (hent : ∀ m, 0 ≤ ent m)
    {m₀ : Dist} {c θ : ℝ} (hθ : 0 < θ)
    (hpin : ∀ u m, |J u m - J u m₀| ≤ c * Real.sqrt (ent m)) (u : Ctrl) (m : Dist) :
    J u m₀ - c ^ 2 / (4 * θ) ≤ rcMultObj J ent θ u m := by
  have h1 := (abs_le.1 (hpin u m)).1
  have h2 := rc_sqrt_penalty (c := c) hθ (hent m)
  simp only [rcMultObj]
  linarith

/-- Miao, p. 319: as `θ → ∞` the multiplier problem converges to the standard control problem.
Under the Pinsker-type bound, if `W θ` is the robust value `max_u min_m (J + θ ent)` and `W₀` the
standard value `max_u J(u, m₀)`, then `W₀ − c²/(4θ) ≤ W θ ≤ W₀` and `W θ → W₀`. -/
theorem rc_mult_tendsto (J : Ctrl → Dist → ℝ) (ent : Dist → ℝ) (hent : ∀ m, 0 ≤ ent m)
    {m₀ : Dist} (h0 : ent m₀ = 0) {c : ℝ}
    (hpin : ∀ u m, |J u m - J u m₀| ≤ c * Real.sqrt (ent m))
    (v : ℝ → Ctrl → ℝ) (hv : ∀ θ, 0 < θ → ∀ u, IsLeast (Set.range (rcMultObj J ent θ u)) (v θ u))
    (W : ℝ → ℝ) (hW : ∀ θ, 0 < θ → IsGreatest (Set.range (v θ)) (W θ)) {W₀ : ℝ}
    (hW₀ : IsGreatest (Set.range fun u => J u m₀) W₀) :
    (∀ θ, 0 < θ → W₀ - c ^ 2 / (4 * θ) ≤ W θ ∧ W θ ≤ W₀) ∧ Tendsto W atTop (𝓝 W₀) := by
  have hb : ∀ θ, 0 < θ → W₀ - c ^ 2 / (4 * θ) ≤ W θ ∧ W θ ≤ W₀ := by
    intro θ hθ
    obtain ⟨u₀, hu₀⟩ := hW₀.1
    refine ⟨?_, ?_⟩
    · have hlow : J u₀ m₀ - c ^ 2 / (4 * θ) ≤ v θ u₀ := by
        obtain ⟨m, hm⟩ := (hv θ hθ u₀).1
        rw [← hm]
        exact rc_mult_lower J ent hent hθ hpin u₀ m
      have := (hW θ hθ).2 ⟨u₀, rfl⟩
      simp only at hu₀
      linarith
    · obtain ⟨u, hu⟩ := (hW θ hθ).1
      rw [← hu]
      exact (rc_mult_le_ref J ent h0 u (hv θ hθ u)).trans (hW₀.2 ⟨u, rfl⟩)
  refine ⟨hb, ?_⟩
  have hlim : Tendsto (fun θ : ℝ => W₀ - c ^ 2 / (4 * θ)) atTop (𝓝 W₀) := by
    have h : Tendsto (fun θ : ℝ => c ^ 2 / (4 * θ)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (c ^ 2 / 4)
      rw [mul_zero] at this
      refine this.congr fun θ => ?_
      rw [div_mul_eq_div_div, div_eq_mul_inv (c ^ 2 / 4)]
    simpa using (tendsto_const_nhds (x := W₀)).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with θ hθ using (hb θ hθ).1
  · filter_upwards [eventually_gt_atTop 0] with θ hθ using (hb θ hθ).2

/-- Miao, p. 320: the conjecture `W(M, x) = MV(x)`. If `w u = min_m g(u, m)` and
`V = max_u w u`, then for `M > 0`, `M·w u = min_m M·g(u, m)` and `MV = max_u M·w u`. -/
theorem rc_bellman_scale {g : Ctrl → Dist → ℝ} {w : Ctrl → ℝ} {V M : ℝ} (hM : 0 < M)
    (hw : ∀ u, IsLeast (Set.range (g u)) (w u)) (hV : IsGreatest (Set.range w) V) :
    (∀ u, IsLeast (Set.range fun m => M * g u m) (M * w u)) ∧
      IsGreatest (Set.range fun u => M * w u) (M * V) := by
  refine ⟨fun u => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm⟩ := (hw u).1
    exact ⟨m, by simp only; rw [hm]⟩
  · rintro _ ⟨m, rfl⟩
    exact mul_le_mul_of_nonneg_left ((hw u).2 ⟨m, rfl⟩) hM.le
  · obtain ⟨u, hu⟩ := hV.1
    exact ⟨u, by simp only; rw [hu]⟩
  · rintro _ ⟨u, rfl⟩
    exact mul_le_mul_of_nonneg_left (hV.2 ⟨u, rfl⟩) hM.le

/-- Miao, p. 320: dividing the Bellman equation for `W(M, x) = MV(x)` by `M > 0`. -/
theorem rc_bellman_divide {g : Ctrl → Dist → ℝ} {w : Ctrl → ℝ} {V M : ℝ} (hM : 0 < M)
    (hw : ∀ u, IsLeast (Set.range fun m => M * g u m) (M * w u))
    (hV : IsGreatest (Set.range fun u => M * w u) (M * V)) :
    (∀ u, IsLeast (Set.range (g u)) (w u)) ∧ IsGreatest (Set.range w) V := by
  have h := rc_bellman_scale (inv_pos.2 hM) hw hV
  simp only [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul] at h
  exact h

/-- Miao, p. 320: the reward `r(x, u)` does not depend on the distortion, so
`min_m (r + βh(m)) = r + β min_m h(m)` for `β > 0`. -/
theorem rc_min_add {h : Dist → ℝ} {a r β : ℝ} (hβ : 0 < β) :
    IsLeast (Set.range h) a ↔ IsLeast (Set.range fun m => r + β * h m) (r + β * a) := by
  constructor
  · rintro ⟨⟨m, hm⟩, hle⟩
    refine ⟨⟨m, by simp only; rw [hm]⟩, ?_⟩
    rintro _ ⟨m', rfl⟩
    have := hle ⟨m', rfl⟩
    simp only
    nlinarith
  · rintro ⟨⟨m, hm⟩, hle⟩
    refine ⟨⟨m, ?_⟩, ?_⟩
    · simp only at hm
      have : β * h m = β * a := by linarith
      exact mul_left_cancel₀ hβ.ne' this
    · rintro _ ⟨m', rfl⟩
      have := hle ⟨m', rfl⟩
      simp only at this
      nlinarith

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The worst-case distortion and the risk-sensitive operator

Miao, §9.6, pp. 319–321, (9.47)–(9.49). Fix a state `x` and control `u`; the shock `ε` has law
`ν` (the density `π`) and `W(ε) = V(f(x, u, ε))` is the continuation value. The minimising agent
chooses a likelihood ratio `m(ε) ≥ 0` with `E m = 1` (`rcAdm`) to minimise
`∫ (m W + θ m ln m) dν` (`rcObj`).

* `eq_9_47_9_48` (Gibbs variational principle): for `θ > 0` with `E exp(−W/θ) < ∞`, the minimiser is
  `m* = exp(−W/θ)/E exp(−W/θ)` (9.47) (`rcWorst`), uniquely (a.e.), and the minimum is
  `R(V) = −θ ln E exp(−W/θ)` (9.48) (`rcR`).
* `eq_9_47_foc`, `eq_9_47_log`: the first-order condition. The derivative of the pointwise
  integrand `mW + θ m ln m` at `m*(ε)` is the same constant `θ(1 − ln E exp(−W/θ))` for every `ε`
  (the Lagrange multiplier of `E m = 1`), i.e. `ln m*(ε) = −W(ε)/θ + λ`. The book prints
  `m*(ε) = −V(f(x, u, ε))/θ + λ`; `eq_9_47_misprint` shows that the printed rule can give a
  negative "likelihood ratio".
* `rc_R_le_mean` (p. 320): `R(V) ≤ E W`: the adjustment is a risk-sensitive certainty equivalent,
  `1/θ` enhancing risk aversion.
* `eq_9_49` (p. 320): the recursive multiplier problem
  `V(x) = max_u {r(x, u) + β min_m ∫ (m V(f) + θ m ln m) π}` is the risk-sensitive problem
  `V(x) = max_u {r(x, u) + βR(V)(x, u)}`.

The entropy term uses Lean's `0 · ln 0 = 0`; admissible distortions must have an integrable
objective (otherwise the book's integral is not defined).
-/

open MeasureTheory Real

namespace Miao.LinearQuadratic

variable {Eps : Type*} [MeasurableSpace Eps]

/-- The admissible likelihood ratios: measurable, nonnegative, `E m = 1`, and the objective
`m W + θ m ln m` integrable. -/
def rcAdm (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) : Set (Eps → ℝ) :=
  {m | Measurable m ∧ (∀ e, 0 ≤ m e) ∧ Integrable m ν ∧ ∫ e, m e ∂ν = 1 ∧
    Integrable (fun e => m e * W e + θ * (m e * log (m e))) ν}

/-- The inner objective `∫ (m(ε)W(ε) + θ m(ε) ln m(ε)) π(ε) dε` (Miao, p. 320). -/
noncomputable def rcObj (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) (m : Eps → ℝ) : ℝ :=
  ∫ e, (m e * W e + θ * (m e * log (m e))) ∂ν

/-- The normaliser `∫ exp(−W/θ) π`. -/
noncomputable def rcZ (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) : ℝ := ∫ e, exp (-W e / θ) ∂ν

/-- The worst-case likelihood ratio (9.47): `m*(ε) = exp(−W(ε)/θ)/∫ exp(−W/θ) π`. -/
noncomputable def rcWorst (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) (e : Eps) : ℝ :=
  exp (-W e / θ) / rcZ ν W θ

/-- The risk-sensitive adjustment (9.48): `R(V) = −θ ln ∫ exp(−W/θ) π`. -/
noncomputable def rcR (ν : Measure Eps) (W : Eps → ℝ) (θ : ℝ) : ℝ := -θ * log (rcZ ν W θ)

/-- The pointwise identity behind (9.47)–(9.48): with `b > 0`,
`a ln a − a ln b = b·klFun(a/b) + a − b`, where `klFun x = x ln x + 1 − x ≥ 0`. -/
theorem rc_mul_log_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * log a - a * log b = b * InformationTheory.klFun (a / b) + a - b := by
  rw [InformationTheory.klFun_apply]
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hb.ne']
    field_simp
    ring

variable (ν : Measure Eps) [IsProbabilityMeasure ν]

theorem rcZ_pos {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν) :
    0 < rcZ ν W θ :=
  integral_exp_pos hZ

theorem rcWorst_pos {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν)
    (e : Eps) : 0 < rcWorst ν W θ e :=
  div_pos (exp_pos _) (rcZ_pos ν hZ)

/-- `ln m*(ε) = −W(ε)/θ − ln ∫ exp(−W/θ) π`. -/
theorem rcWorst_log {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν)
    (e : Eps) : log (rcWorst ν W θ e) = -W e / θ - log (rcZ ν W θ) := by
  rw [rcWorst, Real.log_div (exp_pos _).ne' (rcZ_pos ν hZ).ne', log_exp]

/-- **(9.47)–(9.48)** (Miao, p. 320), the Gibbs variational principle: for `θ > 0` and
`∫ exp(−W/θ) π < ∞`, the worst-case ratio `m* = exp(−W/θ)/∫ exp(−W/θ) π` is admissible, it
attains `R(V) = −θ ln ∫ exp(−W/θ) π`, every admissible `m` has objective at least `R(V)`, and
`m*` is the unique minimiser (a.e.). -/
theorem eq_9_47_9_48 {W : Eps → ℝ} {θ : ℝ} (hθ : 0 < θ) (hW : Measurable W)
    (hZ : Integrable (fun e => exp (-W e / θ)) ν) :
    rcWorst ν W θ ∈ rcAdm ν W θ ∧ rcObj ν W θ (rcWorst ν W θ) = rcR ν W θ ∧
      (∀ m ∈ rcAdm ν W θ, rcR ν W θ ≤ rcObj ν W θ m) ∧
      ∀ m ∈ rcAdm ν W θ, rcObj ν W θ m = rcR ν W θ → m =ᵐ[ν] rcWorst ν W θ := by
  have hZp := rcZ_pos ν hZ
  set Z := rcZ ν W θ with hZdef
  set ms := rcWorst ν W θ with hms
  have hmsi : Integrable ms ν := hZ.div_const Z
  have hms1 : ∫ e, ms e ∂ν = 1 := by
    simp only [hms, rcWorst]
    rw [integral_div]
    exact div_self hZp.ne'
  have hmsm : Measurable ms := ((hW.neg.div_const θ).exp).div_const Z
  have hpt : ∀ e, ms e * W e + θ * (ms e * log (ms e)) = -θ * log Z * ms e := by
    intro e
    rw [rcWorst_log ν hZ e]
    field_simp
    ring
  have hobj : rcObj ν W θ ms = rcR ν W θ := by
    simp only [rcObj, hpt, rcR]
    rw [integral_const_mul, hms1, mul_one]
  have hadm : ms ∈ rcAdm ν W θ := by
    refine ⟨hmsm, fun e => (rcWorst_pos ν hZ e).le, hmsi, hms1, ?_⟩
    simp only [hpt]
    exact hmsi.const_mul _
  -- the decomposition of the objective of an admissible `m`
  have hdec : ∀ m : Eps → ℝ, (∀ e, 0 ≤ m e) → ∀ e,
      m e * W e + θ * (m e * log (m e)) =
        θ * (ms e * InformationTheory.klFun (m e / ms e)) + θ * (m e - ms e) -
          θ * log Z * m e := by
    intro m hm0 e
    have h := rc_mul_log_sub (hm0 e) (rcWorst_pos ν hZ e)
    rw [rcWorst_log ν hZ e] at h
    have : θ * (m e * log (m e)) = θ * (ms e * InformationTheory.klFun (m e / ms e) + m e - ms e) +
        θ * (m e * (-W e / θ - log Z)) := by rw [← h]; ring
    rw [this]
    field_simp
    ring
  have hg : ∀ m ∈ rcAdm ν W θ, Integrable
      (fun e => ms e * InformationTheory.klFun (m e / ms e)) ν ∧
      rcObj ν W θ m = θ * ∫ e, ms e * InformationTheory.klFun (m e / ms e) ∂ν + rcR ν W θ := by
    rintro m ⟨-, hm0, hmi, hm1, hoi⟩
    have hgi : Integrable (fun e => ms e * InformationTheory.klFun (m e / ms e)) ν := by
      have h1 : (fun e => ms e * InformationTheory.klFun (m e / ms e)) = fun e =>
          θ⁻¹ * ((m e * W e + θ * (m e * log (m e))) + θ * log Z * m e) - (m e - ms e) := by
        funext e
        rw [hdec m hm0 e]
        field_simp
        ring
      rw [h1]
      exact ((hoi.add (hmi.const_mul _)).const_mul _).sub (hmi.sub hmsi)
    refine ⟨hgi, ?_⟩
    have i1 : Integrable (fun e => θ * (ms e * InformationTheory.klFun (m e / ms e))) ν :=
      hgi.const_mul θ
    have i2 : Integrable (fun e => θ * (m e - ms e)) ν := (hmi.sub hmsi).const_mul θ
    have i3 : Integrable (fun e => θ * log Z * m e) ν := hmi.const_mul _
    simp only [rcObj, hdec m hm0, rcR]
    rw [integral_sub (f := fun e => θ * (ms e * InformationTheory.klFun (m e / ms e)) +
        θ * (m e - ms e)) (i1.add i2) i3,
      integral_add (f := fun e => θ * (ms e * InformationTheory.klFun (m e / ms e))) i1 i2,
      integral_const_mul,
      integral_const_mul, integral_const_mul, integral_sub hmi hmsi, hm1, hms1]
    ring
  have hkl0 : ∀ m ∈ rcAdm ν W θ, ∀ e, 0 ≤ ms e * InformationTheory.klFun (m e / ms e) :=
    fun m hm e => mul_nonneg (rcWorst_pos ν hZ e).le
      (InformationTheory.klFun_nonneg (div_nonneg (hm.2.1 e) (rcWorst_pos ν hZ e).le))
  refine ⟨hadm, hobj, fun m hm => ?_, fun m hm heq => ?_⟩
  · rw [(hg m hm).2]
    have := integral_nonneg (μ := ν)
      (f := fun e => ms e * InformationTheory.klFun (m e / ms e)) fun e => hkl0 m hm e
    nlinarith
  · rw [(hg m hm).2, add_eq_right, mul_eq_zero] at heq
    rcases heq with h | h
    · exact absurd h hθ.ne'
    rw [integral_eq_zero_iff_of_nonneg (hkl0 m hm) (hg m hm).1] at h
    filter_upwards [h] with e he
    have hp := rcWorst_pos ν hZ e
    have he' : ms e * InformationTheory.klFun (m e / ms e) = 0 := he
    rcases mul_eq_zero.1 he' with h0 | h0
    · exact absurd h0 hp.ne'
    rw [InformationTheory.klFun_eq_zero_iff (div_nonneg (hm.2.1 e) hp.le),
      div_eq_one_iff_eq hp.ne'] at h0
    exact h0

/-- The first-order condition of the minimisation (Miao, p. 320), corrected: the derivative of the
pointwise Lagrangian integrand `m ↦ mW(ε) + θ m ln m` at `m*(ε)` is
`W(ε) + θ(ln m*(ε) + 1) = θ(1 − ln ∫ exp(−W/θ) π)`, the same for every `ε` (the multiplier of the
constraint `E m = 1`). -/
theorem eq_9_47_foc {W : Eps → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hZ : Integrable (fun e => exp (-W e / θ)) ν) (e : Eps) :
    HasDerivAt (fun y => y * W e + θ * (y * log y)) (θ * (1 - log (rcZ ν W θ)))
      (rcWorst ν W θ e) := by
  have hp := rcWorst_pos ν hZ e
  have h : HasDerivAt (fun y => y * W e + θ * (y * log y))
      (1 * W e + θ * (log (rcWorst ν W θ e) + 1)) (rcWorst ν W θ e) :=
    ((hasDerivAt_id' (rcWorst ν W θ e)).mul_const (W e)).add
      ((Real.hasDerivAt_mul_log hp.ne').const_mul θ)
  convert h using 1
  rw [rcWorst_log ν hZ e]
  field_simp
  ring

/-- (9.47), the corrected first-order condition: `ln m*(ε) = −W(ε)/θ + λ` with the constant
`λ = −ln ∫ exp(−W/θ) π` chosen so that `E m* = 1`. -/
theorem eq_9_47_log {W : Eps → ℝ} {θ : ℝ} (hZ : Integrable (fun e => exp (-W e / θ)) ν) :
    ∃ lam : ℝ, ∀ e, log (rcWorst ν W θ e) = -W e / θ + lam :=
  ⟨-log (rcZ ν W θ), fun e => by rw [rcWorst_log ν hZ e, sub_eq_add_neg]⟩

/-- The printed first-order condition is false (Miao, p. 320): the book's
`m*(ε) = −V(f(x, u, ε))/θ + λ`, with `λ` chosen so that `E m* = 1`, can be negative. For the
two-point law `ν = (δ_true + δ_false)/2` with `W(true) = 0`, `W(false) = 4θ`, `λ = 3` and the
printed rule takes the value `−1`. -/
theorem eq_9_47_misprint {θ : ℝ} (hθ : 0 < θ) :
    let ν₂ : Measure Bool := (1 / 2 : ENNReal) • (Measure.dirac true + Measure.dirac false)
    let W : Bool → ℝ := fun b => if b then 0 else 4 * θ
    let lam : ℝ := 1 + (∫ b, W b ∂ν₂) / θ
    ∫ b, (-W b / θ + lam) ∂ν₂ = 1 ∧ -W false / θ + lam < 0 := by
  intro ν₂ W lam
  have hint : ∀ f : Bool → ℝ, ∫ b, f b ∂ν₂ = (f true + f false) / 2 := by
    intro f
    simp only [ν₂]
    rw [integral_smul_measure, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
      integral_dirac, integral_dirac]
    simp
    ring
  have hW : ∫ b, W b ∂ν₂ = 2 * θ := by rw [hint]; simp [W]; ring
  have hlam : lam = 3 := by simp only [lam, hW]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [hint, hlam]
    simp only [W, ite_true, Bool.false_eq_true, ite_false]
    field_simp
    ring
  · rw [hlam]
    simp only [W, Bool.false_eq_true, ite_false]
    rw [neg_div, mul_div_assoc, div_self hθ.ne']
    norm_num

/-- Miao, p. 320: the risk-sensitive adjustment is at most the expectation, `R(V) ≤ E W`
(`m = 1` is admissible); `1/θ` acts as extra risk aversion. -/
theorem rc_R_le_mean {W : Eps → ℝ} {θ : ℝ} (hθ : 0 < θ) (hW : Measurable W) (hWi : Integrable W ν)
    (hZ : Integrable (fun e => exp (-W e / θ)) ν) : rcR ν W θ ≤ ∫ e, W e ∂ν := by
  have h1 : (fun _ : Eps => (1 : ℝ)) ∈ rcAdm ν W θ := by
    refine ⟨measurable_const, fun _ => zero_le_one, integrable_const 1, by simp, ?_⟩
    simpa using hWi
  have := (eq_9_47_9_48 ν hθ hW hZ).2.2.1 _ h1
  simpa [rcObj] using this

/-- **(9.49)** (Miao, p. 320): the recursive multiplier problem is the risk-sensitive control
problem. For a return `r`, transition `f` and value `V` with `E exp(−V(f)/θ) < ∞`,
`V(x) = max_u {r(x, u) + βR(V)(x, u)}` iff `V(x) = max_u {r(x, u) + β min_m ∫(mV(f) + θ m ln m) π}`
(the inner minimum taken over admissible likelihood ratios). -/
theorem eq_9_49 {X U : Type*} (r : X → U → ℝ) (f : X → U → Eps → X) (V : X → ℝ) {β θ : ℝ}
    (hθ : 0 < θ) (hmeas : ∀ x u, Measurable fun e => V (f x u e))
    (hint : ∀ x u, Integrable (fun e => exp (-V (f x u e) / θ)) ν) (x : X) :
    IsGreatest (Set.range fun u => r x u + β * rcR ν (fun e => V (f x u e)) θ) (V x) ↔
      ∃ w : U → ℝ, (∀ u, IsLeast (rcObj ν (fun e => V (f x u e)) θ ''
          rcAdm ν (fun e => V (f x u e)) θ) (w u)) ∧
        IsGreatest (Set.range fun u => r x u + β * w u) (V x) := by
  have hR : ∀ u, IsLeast (rcObj ν (fun e => V (f x u e)) θ '' rcAdm ν (fun e => V (f x u e)) θ)
      (rcR ν (fun e => V (f x u e)) θ) := by
    intro u
    obtain ⟨hadm, hobj, hle, -⟩ := eq_9_47_9_48 ν hθ (hmeas x u) (hint x u)
    refine ⟨⟨_, hadm, hobj⟩, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    exact hle m hm
  constructor
  · intro h
    exact ⟨_, hR, h⟩
  · rintro ⟨w, hw, h⟩
    have : w = fun u => rcR ν (fun e => V (f x u e)) θ := funext fun u => (hw u).unique (hR u)
    rw [this] at h
    exact h

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The linear-quadratic robust control problem

Miao, §9.6, pp. 321–325 ("Linear Quadratic Model with Gaussian Disturbances" and "Modified
Certainty Equivalence Principle"). The data are those of §9.3 (`LSProblem`: `A, B, C, Q, R, S, β`)
in the normalisation of §9.6: the return is `r(x, u) = −½(x'Qx + u'Ru + 2x'Su) = −½ loss` and the
value function is `V(x) = −½x'Px − d/2` (9.50) (`rcV`). For `θ > 0` set

* `H = θI − C'PC` (`rcH`) and `K = I − θ⁻¹C'PC = θ⁻¹H` (`rcK`);
* the operator `D(P) = P + PC(θI − C'PC)⁻¹C'P` (`rcD`);
* the worst-case mean distortion `w* = (θI − C'PC)⁻¹C'P(Ax + Bu)` (`rcWstar`);
* `d = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'PC)⁻¹` (9.55) (`rcd`).

Results.

* `rc_mce_decomp`, `rc_mce` (p. 324, the deterministic minimisation of the modified certainty
  equivalence principle): `−½(y + Cw)'P(y + Cw) + (θ/2)w'w = −½y'D(P)y + ½(w − w*)'H(w − w*)`,
  so for `H > 0` the minimum over `w` is `−½y'D(P)y`, uniquely at `w = w*`.
* `rc_breakdown` (p. 319, the breakdown point): if `H` has a direction of negative curvature the
  minimising agent pushes the objective to `−∞`.
* `RCGaussian`: the Gaussian moment generating identity
  `E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)` for `I − K > 0`, which the
  standard normal shock satisfies; `rc_R_quad` (p. 322): for quadratic `V`,
  `R(V)(x, u) = −½(Ax + Bu)'D(P)(Ax + Bu) − d/2 − (θ/2) ln det(I − θ⁻¹C'PC)⁻¹`.
* `rc_robObj_eq` (p. 322): substituting into (9.49), the objective is
  `−½x'T(D(P))x − ½(u + Fx)'G(u + Fx) − βd/2 − (βθ/2) ln det K⁻¹` with `T` the operator (9.54) =
  (9.11) and `F` the gain (9.52).
* `eq_9_51_9_55`: if `P = T(D(P))` (9.53) and `d` is (9.55) then `V` solves the robust Bellman
  equation (9.49), with the unique maximiser `u = −Fx` (9.51)–(9.52); `rc_bellman_converse`:
  conversely (matching coefficients) the Bellman equation forces (9.53) and (9.55);
  `rc_robust_bellman`: with Gibbs' principle the inner problem is the minimisation over all
  likelihood ratios.
* `rc_modified_ce` (pp. 324–325): the deterministic robust problem with distorted mean `w` has the
  same `P` and the same decision rule; `rc_C_matters`: unlike the standard problem, `C` changes
  both `P` and the rule (a scalar example).

The results are stated for any shock law satisfying `RCGaussian`; the IID standard normal shock
satisfies it (`rc_gaussian_std` in `RCGaussianStd`, with the corollaries `eq_9_51_9_55_std`,
`rc_robust_bellman_std`).
-/

open Matrix MeasureTheory Real

namespace Miao.LinearQuadratic

variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]

/-- `H = θI − C'PC`. -/
def rcH (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : Matrix E E ℝ := θ • 1 - Cᵀ * P * C

/-- `K = I − θ⁻¹C'PC`. -/
noncomputable def rcK (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : Matrix E E ℝ :=
  1 - θ⁻¹ • (Cᵀ * P * C)

/-- The operator `D(P) = P + PC(θI − C'PC)⁻¹C'P` (Miao, p. 322). -/
noncomputable def rcD (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : Matrix X X ℝ :=
  P + P * C * (rcH θ C P)⁻¹ * Cᵀ * P

/-- The worst-case mean distortion `w* = (θI − C'PC)⁻¹C'Py` (Miao, pp. 321, 324). -/
noncomputable def rcWstar (θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) (y : X → ℝ) : E → ℝ :=
  (rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y))

/-- The quadratic value function (9.50): `V(x) = −½x'Px − d/2`. -/
noncomputable def rcV (P : Matrix X X ℝ) (d : ℝ) (x : X → ℝ) : ℝ :=
  -(1 / 2) * (x ⬝ᵥ (P *ᵥ x)) - d / 2

/-- The constant (9.55): `d = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'PC)⁻¹`. -/
noncomputable def rcd (β θ : ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) : ℝ :=
  (1 - β)⁻¹ * (β * θ * log (rcK θ C P)⁻¹.det)

omit [Fintype E] in
theorem rcH_transpose {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (rcH θ C P)ᵀ = rcH θ C P := by
  simp [rcH, transpose_sub, transpose_smul, transpose_one, transpose_mul, hP, Matrix.mul_assoc]

omit [Fintype E] in
theorem rcK_eq_smul {θ : ℝ} (hθ : θ ≠ 0) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    rcK θ C P = θ⁻¹ • rcH θ C P := by
  simp [rcK, rcH, smul_sub, smul_smul, inv_mul_cancel₀ hθ]

omit [Fintype E] in
theorem rcH_eq_smul {θ : ℝ} (hθ : θ ≠ 0) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    rcH θ C P = θ • rcK θ C P := by
  rw [rcK_eq_smul hθ, smul_smul, mul_inv_cancel₀ hθ, one_smul]

omit [Fintype E] in
theorem rcK_posDef_iff {θ : ℝ} (hθ : 0 < θ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    (rcK θ C P).PosDef ↔ (rcH θ C P).PosDef :=
  ⟨fun h => by rw [rcH_eq_smul hθ.ne']; exact h.smul hθ,
    fun h => by rw [rcK_eq_smul hθ.ne']; exact h.smul (inv_pos.2 hθ)⟩

theorem rcK_inv {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hH : IsUnit (rcH θ C P).det) : (rcK θ C P)⁻¹ = θ • (rcH θ C P)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [rcK_eq_smul hθ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hθ, one_smul,
    nonsing_inv_mul _ hH]

theorem rcD_transpose {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    (rcD θ C P)ᵀ = rcD θ C P := by
  simp [rcD, transpose_add, transpose_mul, transpose_nonsing_inv, rcH_transpose hP, hP,
    Matrix.mul_assoc]

/-- `y'D(P)y = y'Py + (C'Py)'(θI − C'PC)⁻¹(C'Py)`. -/
theorem rcD_quad {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (y : X → ℝ) :
    y ⬝ᵥ (rcD θ C P *ᵥ y) = y ⬝ᵥ (P *ᵥ y) +
      (Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y))) := by
  rw [rcD, add_mulVec, dotProduct_add]
  congr 1
  simp only [← mulVec_mulVec]
  rw [SS.LQProblem.dotProduct_mulVec_comm_of_symm hP, SS.LQProblem.mulVec_dotProduct,
    dotProduct_comm]

/-- `D(P) ≥ 0` for `P ≥ 0` and `θI − C'PC > 0`. -/
theorem rcD_posSemidef {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (hH : (rcH θ C P).PosDef) : (rcD θ C P).PosSemidef := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP)
  have hHi := SS.LQProblem.posSemidef_iff_real.1 hH.inv.posSemidef
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨rcD_transpose hPs.1, fun y => ?_⟩
  rw [rcD_quad hPs.1]
  exact add_nonneg (hPs.2 y) (hHi.2 _)

/-- Expanding the deterministic robust objective:
`−½(y + Cw)'P(y + Cw) + (θ/2)w'w = −½y'Py − w'C'Py + ½w'(θI − C'PC)w`. -/
theorem rc_mce_expand {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (y : X → ℝ) (w : E → ℝ) :
    -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w) =
      -(1 / 2) * (y ⬝ᵥ (P *ᵥ y)) - w ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)) +
        1 / 2 * (w ⬝ᵥ (rcH θ C P *ᵥ w)) := by
  have e1 := SS.LQProblem.quad_add hP y (C *ᵥ w)
  have e2 : (C *ᵥ w) ⬝ᵥ (P *ᵥ y) = w ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)) :=
    SS.LQProblem.mulVec_dotProduct C w (P *ᵥ y)
  have e3 : (C *ᵥ w) ⬝ᵥ (P *ᵥ (C *ᵥ w)) = w ⬝ᵥ ((Cᵀ * P * C) *ᵥ w) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul C P w).symm
  have e4 : w ⬝ᵥ (rcH θ C P *ᵥ w) = θ * (w ⬝ᵥ w) - w ⬝ᵥ ((Cᵀ * P * C) *ᵥ w) := by
    rw [rcH, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [e1, e2, e3, e4]
  ring

/-- Miao, p. 324: completing the square in the distortion,
`−½(y + Cw)'P(y + Cw) + (θ/2)w'w = −½y'D(P)y + ½(w − w*)'(θI − C'PC)(w − w*)`. -/
theorem rc_mce_decomp {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (hH : IsUnit (rcH θ C P).det) (y : X → ℝ) (w : E → ℝ) :
    -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w) =
      -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) +
        1 / 2 * ((w - rcWstar θ C P y) ⬝ᵥ (rcH θ C P *ᵥ (w - rcWstar θ C P y))) := by
  set a := Cᵀ *ᵥ (P *ᵥ y) with ha
  have hsq := LSProblem.ls_sq_complete (rcH_transpose (θ := θ) (C := C) hP) hH w (-a)
  have e5 : w + (rcH θ C P)⁻¹ *ᵥ (-a) = w - rcWstar θ C P y := by
    rw [mulVec_neg, ← sub_eq_add_neg, rcWstar]
  have e6 : (-a) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (-a)) = a ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ a) := by
    rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [e5, e6, dotProduct_neg] at hsq
  rw [rc_mce_expand hP, rcD_quad hP, ← ha]
  linear_combination (1 / 2) * hsq

/-- **Modified certainty equivalence** (Miao, p. 324): for `θI − C'PC > 0` the minimum of
`−½(y + Cw)'P(y + Cw) + (θ/2)w'w` over `w` is `−½y'D(P)y`, attained exactly at
`w* = (θI − C'PC)⁻¹C'Py`, the mean of the worst-case normal distribution. -/
theorem rc_mce {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (hH : (rcH θ C P).PosDef) (y : X → ℝ) :
    IsLeast (Set.range fun w : E → ℝ =>
        -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w))
        (-(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y))) ∧
      ∀ w, -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w) =
          -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) ↔ w = rcWstar θ C P y := by
  have hu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  have hH' := SS.LQProblem.posDef_iff_real.1 hH
  have hq := (SS.LQProblem.posSemidef_iff_real.1 hH.posSemidef).2
  refine ⟨⟨⟨rcWstar θ C P y, ?_⟩, ?_⟩, fun w => ?_⟩
  · simp only
    rw [rc_mce_decomp hP hu, sub_self, mulVec_zero, dotProduct_zero, mul_zero, add_zero]
  · rintro _ ⟨w, rfl⟩
    simp only
    rw [rc_mce_decomp hP hu]
    linarith [hq (w - rcWstar θ C P y)]
  · rw [rc_mce_decomp hP hu, add_eq_left, mul_eq_zero]
    constructor
    · rintro (h | h)
      · norm_num at h
      · by_contra hne
        exact absurd h (hH'.2 (sub_ne_zero.2 hne)).ne'
    · rintro rfl
      right
      rw [sub_self, mulVec_zero, dotProduct_zero]

/-- The breakdown point (Miao, p. 319): if `θI − C'PC` has a direction `v` of negative curvature,
the minimising agent can push `−½(y + Cw)'P(y + Cw) + (θ/2)w'w` to `−∞`. -/
theorem rc_breakdown {θ : ℝ} {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (y : X → ℝ)
    {v : E → ℝ} (hv : v ⬝ᵥ (rcH θ C P *ᵥ v) < 0) :
    ¬ BddBelow (Set.range fun w : E → ℝ =>
        -(1 / 2) * ((y + C *ᵥ w) ⬝ᵥ (P *ᵥ (y + C *ᵥ w))) + θ / 2 * (w ⬝ᵥ w)) := by
  rintro ⟨b, hb⟩
  set c0 := -(1 / 2) * (y ⬝ᵥ (P *ᵥ y))
  set c1 := -(v ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)))
  set c2 := 1 / 2 * (v ⬝ᵥ (rcH θ C P *ᵥ v))
  have hc2 : c2 < 0 := by simp only [c2]; linarith
  have hval : ∀ t : ℝ, -(1 / 2) * ((y + C *ᵥ (t • v)) ⬝ᵥ (P *ᵥ (y + C *ᵥ (t • v)))) +
      θ / 2 * ((t • v) ⬝ᵥ (t • v)) = c0 + c1 * t + c2 * t ^ 2 := by
    intro t
    rw [rc_mce_expand hP]
    simp only [c0, c1, c2, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  set S := |c0| + |c1| + |b| + 1
  set M := S / (-c2) + 1
  have hS : 0 < S := by positivity
  have hMdef : M = S / (-c2) + 1 := rfl
  have hM1 : 1 ≤ M := by
    have : 0 ≤ S / (-c2) := div_nonneg hS.le (by linarith)
    rw [hMdef]
    linarith
  have hcM : -c2 * M ≥ S := by
    have h1 : -c2 * (S / (-c2)) = S := mul_div_cancel₀ S (by linarith)
    rw [hMdef, mul_add, h1]
    linarith
  have hc2M : c2 * M ^ 2 ≤ -S * M := by nlinarith
  have h0 : c0 ≤ |c0| * M := (le_abs_self c0).trans (le_mul_of_one_le_right (abs_nonneg _) hM1)
  have h1 : c1 * M ≤ |c1| * M := mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith)
  have hlt : c0 + c1 * M + c2 * M ^ 2 < b := by
    have : c0 + c1 * M + c2 * M ^ 2 ≤ -(|b| + 1) * M := by
      simp only [S] at hc2M
      nlinarith
    have hbM : -(|b| + 1) * M ≤ -(|b| + 1) := by nlinarith [abs_nonneg b]
    linarith [neg_abs_le b]
  have h' : b ≤ c0 + c1 * M + c2 * M ^ 2 := by
    have := hb ⟨M • v, rfl⟩
    simpa only [hval] using this
  linarith

/-- The Gaussian moment generating identity of the standard normal shock: for symmetric `K` with
`I − K > 0`, `E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)`. -/
structure RCGaussian (ν : Measure (E → ℝ)) : Prop where
  prob : IsProbabilityMeasure ν
  integrable : ∀ (K : Matrix E E ℝ) (b : E → ℝ), Kᵀ = K → (1 - K).PosDef →
    Integrable (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ν
  mgf : ∀ (K : Matrix E E ℝ) (b : E → ℝ), Kᵀ = K → (1 - K).PosDef →
    ∫ e, exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e) ∂ν =
      (Real.sqrt (1 - K).det)⁻¹ * exp (1 / 2 * (b ⬝ᵥ ((1 - K)⁻¹ *ᵥ b)))

omit [DecidableEq E] in
/-- The exponent of the worst-case likelihood ratio (Miao, p. 321): for `V = −½z'Pz − d/2`,
`−V(y + Cε)/θ = ½ε'(θ⁻¹C'PC)ε + (θ⁻¹C'Py)'ε + (y'Py + d)/(2θ)`. -/
theorem rc_exponent {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (y : X → ℝ) (d : ℝ) (e : E → ℝ) :
    -rcV P d (y + C *ᵥ e) / θ = 1 / 2 * (e ⬝ᵥ ((θ⁻¹ • (Cᵀ * P * C)) *ᵥ e)) +
      (θ⁻¹ • (Cᵀ *ᵥ (P *ᵥ y))) ⬝ᵥ e + (y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ) := by
  have e1 := SS.LQProblem.quad_add hP y (C *ᵥ e)
  have e2 : (C *ᵥ e) ⬝ᵥ (P *ᵥ y) = (Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ e := by
    rw [SS.LQProblem.mulVec_dotProduct, dotProduct_comm]
  have e3 : (C *ᵥ e) ⬝ᵥ (P *ᵥ (C *ᵥ e)) = e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e) :=
    (SS.LQProblem.dotProduct_transpose_mul_mul C P e).symm
  rw [rcV, e1, e2, e3, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- Miao, p. 322: for the quadratic value function and Gaussian shocks, `E exp(−V(f)/θ) < ∞` and
`R(V)(x, u) = −½y'D(P)y − d/2 − (θ/2) ln det(I − θ⁻¹C'PC)⁻¹`, `y = Ax + Bu` (computed from the
second line of (9.48)). -/
theorem rc_R_quad {ν : Measure (E → ℝ)} (hν : RCGaussian ν) {θ : ℝ} (hθ : 0 < θ)
    {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ)
    (d : ℝ) :
    Integrable (fun e => exp (-rcV P d (y + C *ᵥ e) / θ)) ν ∧
      rcR ν (fun e => rcV P d (y + C *ᵥ e)) θ =
        -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) - d / 2 - θ / 2 * log (rcK θ C P)⁻¹.det := by
  set K' : Matrix E E ℝ := θ⁻¹ • (Cᵀ * P * C)
  set b : E → ℝ := θ⁻¹ • (Cᵀ *ᵥ (P *ᵥ y))
  set c0 : ℝ := (y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ)
  have hK's : K'ᵀ = K' := by
    simp [K', transpose_smul, transpose_mul, hP, Matrix.mul_assoc]
  have h1K : 1 - K' = rcK θ C P := rfl
  have hpos : (1 - K').PosDef := by rw [h1K]; exact (rcK_posDef_iff hθ C P).2 hH
  have hpt : (fun e => exp (-rcV P d (y + C *ᵥ e) / θ)) =
      fun e => exp c0 * exp (1 / 2 * (e ⬝ᵥ (K' *ᵥ e)) + b ⬝ᵥ e) := by
    funext e
    rw [rc_exponent hθ.ne' hP, ← exp_add]
    congr 1
    ring
  have hint := hν.integrable K' b hK's hpos
  refine ⟨by rw [hpt]; exact hint.const_mul _, ?_⟩
  have hdet : 0 < (rcK θ C P).det := ((rcK_posDef_iff hθ C P).2 hH).det_pos
  have hu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  have hb : b ⬝ᵥ ((1 - K')⁻¹ *ᵥ b) =
      θ⁻¹ * ((Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y)))) := by
    rw [h1K, rcK_inv hθ.ne' hu]
    simp only [b, smul_mulVec, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
  have hZ : rcZ ν (fun e => rcV P d (y + C *ᵥ e)) θ =
      exp c0 * ((Real.sqrt (rcK θ C P).det)⁻¹ *
        exp (1 / 2 * (θ⁻¹ * ((Cᵀ *ᵥ (P *ᵥ y)) ⬝ᵥ ((rcH θ C P)⁻¹ *ᵥ (Cᵀ *ᵥ (P *ᵥ y))))))) := by
    rw [rcZ, hpt, integral_const_mul, hν.mgf K' b hK's hpos, hb, h1K]
  have hsq : 0 < Real.sqrt (rcK θ C P).det := Real.sqrt_pos.2 hdet
  have hinvdet : (rcK θ C P)⁻¹.det = ((rcK θ C P).det)⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv']
  rw [rcR, hZ, Real.log_mul (exp_pos _).ne' (mul_pos (inv_pos.2 hsq) (exp_pos _)).ne',
    Real.log_mul (inv_pos.2 hsq).ne' (exp_pos _).ne', log_exp, log_exp, Real.log_inv,
    Real.log_sqrt hdet.le, hinvdet, Real.log_inv, rcD_quad hP]
  simp only [c0]
  field_simp
  ring

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The robust Bellman objective (9.49) with the quadratic value (9.50):
`r(x, u) + βR(V)(x, u)`, `r = −½ loss`. -/
noncomputable def rcRobObj (L : LSProblem X U E) (ν : Measure (E → ℝ)) (θ : ℝ)
    (P : Matrix X X ℝ) (d : ℝ) (x : X → ℝ) (u : U → ℝ) : ℝ :=
  -(1 / 2) * L.loss x u + L.β * rcR ν (fun e => rcV P d (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ

/-- The outer step: `−½r(x, u) − (β/2)(Ax + Bu)'D(P)(Ax + Bu) =
−½x'T(D(P))x − ½(u + Fx)'G(u + Fx)` with `F = F(D(P))` (9.52), `G = G(D(P))`. -/
theorem rc_outer_eq (L : LSProblem X U E) (hRs : L.Rᵀ = L.R) {θ : ℝ} {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (hG : IsUnit (L.G (rcD θ L.C P)).det) (x : X → ℝ) (u : U → ℝ) :
    -(1 / 2) * L.loss x u + L.β * (-(1 / 2) * ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ
        (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u)))) =
      -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) -
        1 / 2 * ((u + L.F (rcD θ L.C P) *ᵥ x) ⬝ᵥ
          (L.G (rcD θ L.C P) *ᵥ (u + L.F (rcD θ L.C P) *ᵥ x))) := by
  have h := L.loss_add_cont hRs (rcD_transpose hP) hG x u
  linear_combination (-1 / 2) * h

/-- Miao, p. 322: substituting (9.50) and `R(V)` into (9.49),
`r(x, u) + βR(V)(x, u) = −½x'T(D(P))x − ½(u + Fx)'G(u + Fx) − βd/2 − (βθ/2) ln det K⁻¹`. -/
theorem rc_robObj_eq (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hRs : L.Rᵀ = L.R) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : Pᵀ = P)
    (hH : (rcH θ L.C P).PosDef) (hG : IsUnit (L.G (rcD θ L.C P)).det) (d : ℝ) (x : X → ℝ)
    (u : U → ℝ) :
    rcRobObj L ν θ P d x u = -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) -
        1 / 2 * ((u + L.F (rcD θ L.C P) *ᵥ x) ⬝ᵥ
          (L.G (rcD θ L.C P) *ᵥ (u + L.F (rcD θ L.C P) *ᵥ x))) -
        L.β * (d / 2) - L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) := by
  rw [rcRobObj, (rc_R_quad hν hθ hP hH (L.A *ᵥ x + L.B *ᵥ u) d).2]
  have h := rc_outer_eq L hRs hP hG x u
  linear_combination h

/-- The maximum of the robust Bellman objective: `−½x'T(D(P))x − βd/2 − (βθ/2) ln det K⁻¹`,
attained exactly at `u = −F(D(P))x`. -/
theorem rc_robObj_max (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef) (d : ℝ) (x : X → ℝ) :
    IsGreatest (Set.range (rcRobObj L ν θ P d x))
        (-(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) - L.β * (d / 2) -
          L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det)) ∧
      ∀ u, rcRobObj L ν θ P d x u = -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) -
          L.β * (d / 2) - L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) ↔
        u = -(L.F (rcD θ L.C P) *ᵥ x) := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hGp := L.G_posDef hR (rcD_posSemidef hP hH) hβ
  have hG := (isUnit_iff_isUnit_det _).1 hGp.isUnit
  have hG' := SS.LQProblem.posDef_iff_real.1 hGp
  have hq := (SS.LQProblem.posSemidef_iff_real.1 hGp.posSemidef).2
  refine ⟨⟨⟨-(L.F (rcD θ L.C P) *ᵥ x), ?_⟩, ?_⟩, fun u => ?_⟩
  · rw [rc_robObj_eq L hν hRs hθ hPs hH hG, neg_add_cancel, mulVec_zero, dotProduct_zero]
    ring
  · rintro _ ⟨u, rfl⟩
    rw [rc_robObj_eq L hν hRs hθ hPs hH hG]
    linarith [hq (u + L.F (rcD θ L.C P) *ᵥ x)]
  · rw [rc_robObj_eq L hν hRs hθ hPs hH hG]
    constructor
    · intro h
      by_contra hne
      have : u + L.F (rcD θ L.C P) *ᵥ x ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      linarith [hG'.2 this]
    · rintro rfl
      rw [neg_add_cancel, mulVec_zero, dotProduct_zero]
      ring

/-- **(9.51)–(9.55)** (Miao, pp. 322–323): if `P ≥ 0` solves the robust Riccati equation
`P = T(D(P))` (9.53), with `T` the operator (9.54) of (9.11), and `d` is (9.55), then
`V(x) = −½x'Px − d/2` solves the robust Bellman equation (9.49) for Gaussian shocks, and the
robust decision rule `u = −Fx` (9.51), `F = (R + βB'D(P)B)⁻¹(S' + βB'D(P)A)` (9.52), is the unique
maximiser. -/
theorem eq_9_51_9_55 (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef) (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    IsGreatest (Set.range (rcRobObj L ν θ P (rcd L.β θ L.C P) x)) (rcV P (rcd L.β θ L.C P) x) ∧
      ∀ u, rcRobObj L ν θ P (rcd L.β θ L.C P) x u = rcV P (rcd L.β θ L.C P) x ↔
        u = -(L.F (rcD θ L.C P) *ᵥ x) := by
  have h := rc_robObj_max L hν hR hβ hθ hP hH (rcd L.β θ L.C P) x
  have hval : -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) - L.β * (rcd L.β θ L.C P / 2) -
      L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) = rcV P (rcd L.β θ L.C P) x := by
    have h1 : (1 - L.β) ≠ 0 := by linarith
    rw [hfix, rcV, rcd]
    field_simp
    ring
  rw [hval] at h
  exact h

/-- Matching coefficients (Miao, p. 322): if `V(x) = −½x'Px − d/2` solves the robust Bellman
equation for every `x`, then `P = T(D(P))` (9.53) and `d` is (9.55). -/
theorem rc_bellman_converse (L : LSProblem X U E) {ν : Measure (E → ℝ)}
    (hν : RCGaussian ν) (hQ : L.Qᵀ = L.Q) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1)
    {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    {d : ℝ} (hV : ∀ x, IsGreatest (Set.range (rcRobObj L ν θ P d x)) (rcV P d x)) :
    L.T (rcD θ L.C P) = P ∧ d = rcd L.β θ L.C P := by
  classical
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have heq : ∀ x, rcV P d x = -(1 / 2) * (x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x)) - L.β * (d / 2) -
      L.β * (θ / 2 * log (rcK θ L.C P)⁻¹.det) :=
    fun x => (hV x).unique (rc_robObj_max L hν hR hβ hθ hP hH d x).1
  have h0 := heq 0
  simp only [rcV, mulVec_zero, dotProduct_zero, mul_zero] at h0
  have hd : d = rcd L.β θ L.C P := by
    have h1 : (1 - L.β) ≠ 0 := by linarith
    rw [rcd]
    field_simp
    linarith
  refine ⟨?_, hd⟩
  have hquad : ∀ x, x ⬝ᵥ (L.T (rcD θ L.C P) *ᵥ x) = x ⬝ᵥ (P *ᵥ x) := by
    intro x
    have := heq x
    simp only [rcV] at this
    linarith
  have hTs : (L.T (rcD θ L.C P))ᵀ = L.T (rcD θ L.C P) := L.T_transpose hQ hRs (rcD_transpose hPs)
  ext i j
  rw [ls_entry_eq_polar hTs, ls_entry_eq_polar hPs, hquad, hquad, hquad]

omit [DecidableEq E] in
theorem rcV_comp_measurable (P : Matrix X X ℝ) (d : ℝ) (y : X → ℝ) (C : Matrix X E ℝ) :
    Measurable fun e : E → ℝ => rcV P d (y + C *ᵥ e) := by
  have : Continuous fun e : E → ℝ => rcV P d (y + C *ᵥ e) := by
    unfold rcV
    fun_prop
  exact this.measurable

/-- **The robust Bellman equation** (Miao, pp. 320–323): under (9.53) and (9.55), for every `x`
the inner problem `min_m ∫(m V(Ax + Bu + Cε) + θ m ln m) π dε` over all likelihood ratios has a
value `w(u)` (namely `R(V)(x, u)`), and `V(x) = max_u {r(x, u) + βw(u)}`. -/
theorem rc_robust_bellman (L : LSProblem X U E) {ν : Measure (E → ℝ)} (hν : RCGaussian ν)
    (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ} (hθ : 0 < θ) {P : Matrix X X ℝ}
    (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef) (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    ∃ w : (U → ℝ) → ℝ,
      (∀ u, IsLeast
        (rcObj ν (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ ''
          rcAdm ν (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ)
        (w u)) ∧
      IsGreatest (Set.range fun u => -(1 / 2) * L.loss x u + L.β * w u)
        (rcV P (rcd L.β θ L.C P) x) := by
  have := hν.prob
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  exact (eq_9_49 ν (fun x u => -(1 / 2) * L.loss x u)
    (fun x u e => L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e) (rcV P (rcd L.β θ L.C P)) hθ
    (fun x u => rcV_comp_measurable _ _ _ _)
    (fun x u => (rc_R_quad hν hθ hPs hH (L.A *ᵥ x + L.B *ᵥ u) _).1) x).1
    (eq_9_51_9_55 L hν hR hβ hβ1 hθ hP hH hfix x).1

/-- **Modified certainty equivalence** (Miao, pp. 324–325): the deterministic robust problem
`V(x) = max_u min_w {r(x, u) + β(V(Ax + Bu + Cw) + (θ/2)w'w)}` with `V = −½x'Px` has the inner
value `−½(Ax + Bu)'D(P)(Ax + Bu)` at `w = w*`, and if `P = T(D(P))` the outer maximum is
`−½x'Px`, attained exactly at the same robust rule `u = −F(D(P))x` as the stochastic problem;
the worst-case covariance and the constant `d` play no role. -/
theorem rc_modified_ce (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {θ : ℝ}
    {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    (∀ u, IsLeast (Set.range fun w : E → ℝ =>
        rcV P 0 (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ w) + θ / 2 * (w ⬝ᵥ w))
        (-(1 / 2) * ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))))) ∧
      IsGreatest (Set.range fun u => -(1 / 2) * L.loss x u + L.β * (-(1 / 2) *
        ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u))))) (rcV P 0 x) ∧
      ∀ u, -(1 / 2) * L.loss x u + L.β * (-(1 / 2) *
          ((L.A *ᵥ x + L.B *ᵥ u) ⬝ᵥ (rcD θ L.C P *ᵥ (L.A *ᵥ x + L.B *ᵥ u)))) = rcV P 0 x ↔
        u = -(L.F (rcD θ L.C P) *ᵥ x) := by
  have hPs := (SS.LQProblem.posSemidef_iff_real.1 hP).1
  have hRs := (SS.LQProblem.posDef_iff_real.1 hR).1
  have hGp := L.G_posDef hR (rcD_posSemidef hP hH) hβ
  have hG := (isUnit_iff_isUnit_det _).1 hGp.isUnit
  have hG' := SS.LQProblem.posDef_iff_real.1 hGp
  have hq := (SS.LQProblem.posSemidef_iff_real.1 hGp.posSemidef).2
  have hV0 : ∀ z, rcV P 0 z = -(1 / 2) * (z ⬝ᵥ (P *ᵥ z)) := fun z => by simp [rcV]
  refine ⟨fun u => ?_, ⟨⟨-(L.F (rcD θ L.C P) *ᵥ x), ?_⟩, ?_⟩, fun u => ?_⟩
  · simp only [hV0]
    exact (rc_mce hPs hH _).1
  · simp only
    rw [rc_outer_eq L hRs hPs hG, neg_add_cancel, mulVec_zero, dotProduct_zero, hfix, hV0]
    ring
  · rintro _ ⟨u, rfl⟩
    simp only
    rw [rc_outer_eq L hRs hPs hG, hfix, hV0]
    linarith [hq (u + L.F (rcD θ L.C P) *ᵥ x)]
  · rw [rc_outer_eq L hRs hPs hG, hfix, hV0]
    constructor
    · intro h
      by_contra hne
      have : u + L.F (rcD θ L.C P) *ᵥ x ≠ 0 := fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
      linarith [hG'.2 this]
    · rintro rfl
      rw [neg_add_cancel, mulVec_zero, dotProduct_zero]
      ring

/-- The inverse of a `1 × 1` matrix. -/
theorem rc_inv_fin_one (a : ℝ) : (!![a] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![a⁻¹] := by
  rw [Matrix.inv_def, adjugate_fin_one, det_fin_one_of, Ring.inverse_eq_inv']
  ext i j
  fin_cases i; fin_cases j
  simp

/-- The scalar problem of `rc_C_matters`: `A = B = R = 1`, `Q = 3/2`, `S = 0`, `β = 1/2`,
shock loading `c`. -/
noncomputable def rcScalarProblem (c : ℝ) : LSProblem (Fin 1) (Fin 1) (Fin 1) :=
  ⟨!![1], !![1], !![c], !![3 / 2], !![1], 0, 1 / 2⟩

/-- Miao, p. 325: unlike the standard problem, the volatility matrix `C` affects both the decision
rule and `P` in the robust problem. In the scalar problem `rcScalarProblem c` with `θ = 52/11`:
for `c = 0`, `D(P) = P`, the robust equation is the standard Riccati equation, solved by `P = 2`
with gain `F = 1/2`; for `c = 1`, `P = 13/6` solves `P = T(D(P))` with gain `F = 2/3`, while
`P = 2` does not. -/
theorem rc_C_matters :
    (∀ P, rcD (52 / 11) (rcScalarProblem 0).C P = P) ∧
      (rcScalarProblem 0).T !![2] = !![2] ∧ (rcScalarProblem 0).F !![2] = !![1 / 2] ∧
      (rcScalarProblem 1).T (rcD (52 / 11) (rcScalarProblem 1).C !![13 / 6]) = !![13 / 6] ∧
      (rcScalarProblem 1).F (rcD (52 / 11) (rcScalarProblem 1).C !![13 / 6]) = !![2 / 3] ∧
      (rcScalarProblem 1).T (rcD (52 / 11) (rcScalarProblem 1).C !![2]) ≠ !![2] := by
  have hC0 : (rcScalarProblem 0).C = 0 := by
    ext i j; fin_cases i; fin_cases j; simp [rcScalarProblem]
  have hD : ∀ p : ℝ, rcD (52 / 11) (rcScalarProblem 1).C !![p] =
      !![p + p ^ 2 / (52 / 11 - p)] := by
    intro p
    have hH : rcH (52 / 11) (rcScalarProblem 1).C !![p] = !![52 / 11 - p] := by
      ext i j; fin_cases i; fin_cases j
      simp [rcH, rcScalarProblem, Matrix.mul_apply]
    rw [rcD, hH, rc_inv_fin_one]
    ext i j; fin_cases i; fin_cases j
    simp [rcScalarProblem, Matrix.mul_apply, vecMul, dotProduct]
    ring
  have hG : ∀ (c p : ℝ), (rcScalarProblem c).G !![p] = !![1 + p / 2] := by
    intro c p
    ext i j; fin_cases i; fin_cases j
    simp [LSProblem.G, rcScalarProblem, Matrix.mul_apply]
    ring
  have hN : ∀ (c p : ℝ), (rcScalarProblem c).N !![p] = !![p / 2] := by
    intro c p
    ext i j; fin_cases i; fin_cases j
    simp [LSProblem.N, rcScalarProblem, Matrix.mul_apply]
    ring
  have hT : ∀ (c p : ℝ), (rcScalarProblem c).T !![p] =
      !![3 / 2 + p / 2 - (p / 2) ^ 2 / (1 + p / 2)] := by
    intro c p
    rw [LSProblem.T, hG, hN, rc_inv_fin_one]
    ext i j; fin_cases i; fin_cases j
    simp [rcScalarProblem, Matrix.mul_apply]
    ring
  have hF : ∀ (c p : ℝ), (rcScalarProblem c).F !![p] = !![(p / 2) / (1 + p / 2)] := by
    intro c p
    rw [LSProblem.F, hG, hN, rc_inv_fin_one]
    ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
    ring
  refine ⟨fun P => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rcD, hC0]
  · rw [hT]; norm_num
  · rw [hF]; norm_num
  · rw [hD, hT]; norm_num
  · rw [hD, hF]; norm_num
  · rw [hD, hT]
    intro h
    have := congrFun (congrFun h 0) 0
    norm_num at this

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The worst-case normal distribution and relative entropy of normals

Miao, §9.6, pp. 321–324. The standard normal density is `rcStdPdf` and the normal density with
mean `w` and covariance `Σ` is `rcGaussPdf w Σ`. Expectations under a law with mean `w` and
covariance `Σ` use only these two moments (`RCMoments`).

* `rc_worst_ratio` (p. 321): `m*(ε) ∝ exp(ε'C'PCε/(2θ) + ε'C'P(Ax + Bu)/θ)`;
  `rc_worst_exponent`: `π(ε)m*(ε) ∝ exp(−½ε'Kε + ε'K(θI − C'PC)⁻¹C'P(Ax + Bu))`,
  `K = I − θ⁻¹C'PC`; `rc_worst_density`: `π m*` is proportional to the normal density with mean
  `w* = (θI − C'PC)⁻¹C'P(Ax + Bu)` and covariance `K⁻¹`.
* `rc_nonsingular_not_enough` (correction): the book requires only that `K` be nonsingular; it must
  be positive definite. With `K = −1` the worst-case kernel is not integrable.
* `rc_llr_normal` (p. 323): `ln(π̂/π) = ½(−(ε − w)'Σ⁻¹(ε − w) + ε'ε − ln det Σ)`.
* `rc_moment_quad`, `rc_moment_trace_inv` (p. 323): `∫(ε − w)'Σ⁻¹(ε − w)π̂ = tr(I)`, so
  `−½∫(ε − w)'Σ⁻¹(ε − w)π̂ = −½ tr(I)` (`rc_moment_half`); the book prints `+½ tr(I)`
  (`rc_moment_sign_misprint`).
* `rc_half_sq_split`, `rc_half_sq_moment` (pp. 323–324): `½ε'ε = ½w'w + ½(ε − w)'(ε − w) +
  w'(ε − w)` and `½∫ε'επ̂ = ½w'w + ½ tr Σ`.
* **(9.56)** (`eq_9_56`): `∫π̂ ln(π̂/π) = ½w'w − ½ ln det Σ + ½ tr(Σ − I)`.
* `rc_R_first_line` (p. 322): computing `R(V)` from the first line of (9.48),
  `∫V π* + θ∫π* ln(π*/π) = −½y'D(P)y − d/2 − (θ/2) ln det K⁻¹`, and `rc_R_lines_agree`: it agrees
  with the second line (`rc_R_quad`).

Departure: "`π̂` is normal with mean `w` and covariance `Σ`" enters through the explicit density in
the log-likelihood ratio and through the two moments of the law integrated against.
-/

open Matrix MeasureTheory Real

namespace Miao.LinearQuadratic

variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]

/-- The normal density with mean `w` and covariance `Σ` on `ℝ^{nε}`. -/
noncomputable def rcGaussPdf (w : E → ℝ) (Sg : Matrix E E ℝ) (e : E → ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi) ^ Fintype.card E)⁻¹ * (Real.sqrt Sg.det)⁻¹ *
    exp (-(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))))

omit [DecidableEq E] in
/-- The standard normal density `π`. -/
noncomputable def rcStdPdf (e : E → ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi) ^ Fintype.card E)⁻¹ * exp (-(1 / 2) * (e ⬝ᵥ e))

/-- `π` is the normal density with mean `0` and covariance `I`. -/
theorem rcStdPdf_eq (e : E → ℝ) : rcStdPdf e = rcGaussPdf 0 1 e := by
  simp [rcStdPdf, rcGaussPdf]

/-- Miao, p. 323: the log likelihood ratio of normals,
`ln(π̂(ε)/π(ε)) = ½(−(ε − w)'Σ⁻¹(ε − w) + ε'ε − ln det Σ)`. -/
theorem rc_llr_normal {Sg : Matrix E E ℝ} (hS : Sg.PosDef) (w e : E → ℝ) :
    log (rcGaussPdf w Sg e / rcStdPdf e) =
      1 / 2 * (-((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + e ⬝ᵥ e - log Sg.det) := by
  have hdet := hS.det_pos
  have hs : 0 < Real.sqrt Sg.det := Real.sqrt_pos.2 hdet
  have hc : 0 < (Real.sqrt (2 * Real.pi) ^ Fintype.card E)⁻¹ := by positivity
  have h : rcGaussPdf w Sg e / rcStdPdf e = (Real.sqrt Sg.det)⁻¹ *
      exp (-(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) - -(1 / 2) * (e ⬝ᵥ e)) := by
    rw [rcGaussPdf, rcStdPdf, exp_sub]
    field_simp
  rw [h, Real.log_mul (inv_pos.2 hs).ne' (exp_pos _).ne', Real.log_inv, Real.log_sqrt hdet.le,
    log_exp]
  ring

/-- A law on `ℝ^{nε}` with mean `w` and covariance `Σ` (integrable second moments). -/
structure RCMoments (ν : Measure (E → ℝ)) (w : E → ℝ) (Sg : Matrix E E ℝ) : Prop where
  prob : IsProbabilityMeasure ν
  int1 : ∀ k, Integrable (fun e : E → ℝ => e k) ν
  int2 : ∀ k l, Integrable (fun e : E → ℝ => e k * e l) ν
  mean : ∀ k, ∫ e, e k ∂ν = w k
  cov : ∀ k l, ∫ e, (e k - w k) * (e l - w l) ∂ν = Sg k l

omit [DecidableEq E] in
/-- `E(z + C(ε − w))'P(z + C(ε − w)) = z'Pz + tr(C'PCΣ)` under a law with mean `w` and covariance
`Σ`. -/
theorem rc_moment_quad {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) (z : X → ℝ) (C : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Integrable (fun e : E → ℝ => (z + C *ᵥ (e - w)) ⬝ᵥ (P *ᵥ (z + C *ᵥ (e - w)))) ν ∧
      ∫ e, (z + C *ᵥ (e - w)) ⬝ᵥ (P *ᵥ (z + C *ᵥ (e - w))) ∂ν =
        z ⬝ᵥ (P *ᵥ z) + trace (Cᵀ * P * C * Sg) := by
  have := hν.prob
  simp only [ls_quad_shock_expand]
  have i1 : ∀ k, Integrable (fun e : E → ℝ => (e - w) k) ν := fun k =>
    (hν.int1 k).sub (integrable_const (w k))
  have i2 : ∀ k l, Integrable (fun e : E → ℝ => (e - w) k * (e - w) l) ν := fun k l => by
    have h : (fun e : E → ℝ => (e - w) k * (e - w) l) = fun e => e k * e l - w l * e k -
        w k * e l + w k * w l := by
      funext e; simp only [Pi.sub_apply]; ring
    rw [h]
    exact (((hν.int2 k l).sub ((hν.int1 k).const_mul _)).sub ((hν.int1 l).const_mul _)).add
      (integrable_const _)
  have m1 : ∀ k, ∫ e, (e - w) k ∂ν = 0 := fun k => by
    simp only [Pi.sub_apply]
    rw [integral_sub (hν.int1 k) (integrable_const _), hν.mean, integral_const, probReal_univ,
      one_smul, sub_self]
  have m2 : ∀ k l, ∫ e, (e - w) k * (e - w) l ∂ν = Sg k l := fun k l => by
    simp only [Pi.sub_apply]
    exact hν.cov k l
  have hSs : ∀ k l, Sg l k = Sg k l := fun k l => by
    rw [← m2, ← m2]; congr 1; funext e; ring
  set cf := z ᵥ* (P * C) + Cᵀ *ᵥ (P *ᵥ z)
  have hlin : Integrable (fun e : E → ℝ => ∑ k, cf k * (e - w) k) ν :=
    integrable_finsetSum _ fun k _ => (i1 k).const_mul _
  have hq : Integrable (fun e : E → ℝ => ∑ k, ∑ l, (Cᵀ * P * C) k l * ((e - w) k * (e - w) l))
      ν := integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (i2 k l).const_mul _
  have hcl : Integrable (fun e : E → ℝ => z ⬝ᵥ (P *ᵥ z) + ∑ k, cf k * (e - w) k) ν :=
    (integrable_const _).add hlin
  refine ⟨hcl.add hq, ?_⟩
  have hlin0 : ∫ e, ∑ k, cf k * (e - w) k ∂ν = 0 := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => cf k * (e - w) k) _
      fun k _ => (i1 k).const_mul _]
    simp only [integral_const_mul, m1, mul_zero, Finset.sum_const_zero]
  have hrow : ∀ k, ∫ e, ∑ l, (Cᵀ * P * C) k l * ((e - w) k * (e - w) l) ∂ν =
      ∑ l, (Cᵀ * P * C) k l * Sg l k := by
    intro k
    rw [integral_finsetSum (f := fun l (e : E → ℝ) => (Cᵀ * P * C) k l *
      ((e - w) k * (e - w) l)) _ fun l _ => (i2 k l).const_mul _]
    simp only [integral_const_mul, m2, hSs]
  have hq0 : ∫ e, ∑ k, ∑ l, (Cᵀ * P * C) k l * ((e - w) k * (e - w) l) ∂ν =
      trace (Cᵀ * P * C * Sg) := by
    rw [integral_finsetSum (f := fun k (e : E → ℝ) => ∑ l, (Cᵀ * P * C) k l *
      ((e - w) k * (e - w) l)) _ fun k _ => integrable_finsetSum _ fun l _ =>
        (i2 k l).const_mul _]
    simp only [hrow]
    rfl
  rw [integral_add hcl hq, integral_add (integrable_const _) hlin, integral_const, hlin0, hq0,
    probReal_univ, one_smul, add_zero]

/-- Miao, p. 323: `∫(ε − w)'Σ⁻¹(ε − w)π̂(ε)dε = tr(I)`. -/
theorem rc_moment_trace_inv {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) (hSu : IsUnit Sg.det) :
    Integrable (fun e : E → ℝ => (e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) ν ∧
      ∫ e, (e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w)) ∂ν = trace (1 : Matrix E E ℝ) := by
  have h := rc_moment_quad hν (0 : E → ℝ) (1 : Matrix E E ℝ) Sg⁻¹
  simp only [zero_add, one_mulVec, mulVec_zero, dotProduct_zero, transpose_one,
    Matrix.one_mul, Matrix.mul_one, nonsing_inv_mul _ hSu] at h
  exact h

/-- Miao, p. 323 (corrected sign): `−½∫(ε − w)'Σ⁻¹(ε − w)π̂(ε)dε = −½ tr(I)`. -/
theorem rc_moment_half {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) (hSu : IsUnit Sg.det) :
    -∫ e, 1 / 2 * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) ∂ν = -(1 / 2) * trace (1 : Matrix E E ℝ) := by
  rw [integral_const_mul, (rc_moment_trace_inv hν hSu).2]
  ring

omit [Fintype E] in
/-- The sign printed on p. 323 (`+½ tr(I)`) is wrong whenever `nε ≥ 1`. -/
theorem rc_moment_sign_misprint [Fintype E] [Nonempty E] :
    -(1 / 2) * trace (1 : Matrix E E ℝ) ≠ 1 / 2 * trace (1 : Matrix E E ℝ) := by
  rw [trace_one]
  have : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  intro h
  linarith

omit [Fintype E] [DecidableEq E] in
/-- Miao, p. 323: `½ε'ε = ½w'w + ½(ε − w)'(ε − w) + w'(ε − w)`. -/
theorem rc_half_sq_split [Fintype E] (w e : E → ℝ) :
    1 / 2 * (e ⬝ᵥ e) = 1 / 2 * (w ⬝ᵥ w) + 1 / 2 * ((e - w) ⬝ᵥ (e - w)) + w ⬝ᵥ (e - w) := by
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm w e]
  ring

omit [DecidableEq E] in
/-- Miao, p. 324: `½∫ε'επ̂(ε)dε = ½w'w + ½ tr(Σ)`. -/
theorem rc_half_sq_moment {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ}
    (hν : RCMoments ν w Sg) :
    Integrable (fun e : E → ℝ => e ⬝ᵥ e) ν ∧
      ∫ e, 1 / 2 * (e ⬝ᵥ e) ∂ν = 1 / 2 * (w ⬝ᵥ w) + 1 / 2 * trace Sg := by
  classical
  have h := rc_moment_quad hν w (1 : Matrix E E ℝ) (1 : Matrix E E ℝ)
  simp only [one_mulVec, add_sub_cancel, transpose_one, Matrix.one_mul] at h
  refine ⟨h.1, ?_⟩
  rw [integral_const_mul, h.2]
  ring

/-- **(9.56)** (Miao, p. 324): for the standard normal `π` and the normal `π̂` with mean `w` and
covariance `Σ > 0`, `∫π̂ ln(π̂/π) = ½w'w − ½ ln det Σ + ½ tr(Σ − I)` (the integral taken against
any law with mean `w` and covariance `Σ`, in particular `N(w, Σ)`). -/
theorem eq_9_56 {ν : Measure (E → ℝ)} {w : E → ℝ} {Sg : Matrix E E ℝ} (hν : RCMoments ν w Sg)
    (hS : Sg.PosDef) :
    ∫ e, log (rcGaussPdf w Sg e / rcStdPdf e) ∂ν =
      1 / 2 * (w ⬝ᵥ w) - 1 / 2 * log Sg.det + 1 / 2 * trace (Sg - 1) := by
  have := hν.prob
  have hSu := (isUnit_iff_isUnit_det _).1 hS.isUnit
  obtain ⟨i1, h1⟩ := rc_moment_trace_inv hν hSu
  obtain ⟨i2, h2⟩ := rc_half_sq_moment hν
  simp only [rc_llr_normal hS]
  have e1 : ∀ e : E → ℝ, 1 / 2 * (-((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + e ⬝ᵥ e - log Sg.det) =
      -(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + 1 / 2 * (e ⬝ᵥ e) - 1 / 2 * log Sg.det :=
    fun e => by ring
  simp only [e1]
  rw [integral_sub (f := fun e => -(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))) + 1 / 2 * (e ⬝ᵥ e))
      ((i1.const_mul _).add (i2.const_mul _)) (integrable_const _),
    integral_add (f := fun e => -(1 / 2) * ((e - w) ⬝ᵥ (Sg⁻¹ *ᵥ (e - w))))
      (i1.const_mul _) (i2.const_mul _), integral_const_mul, h1, h2, integral_const,
    probReal_univ, one_smul, trace_sub]
  ring

omit [DecidableEq E] in
/-- Miao, p. 321: the worst-case likelihood ratio for `V = −½z'Pz − d/2`:
`exp(−V(y + Cε)/θ) = exp((y'Py + d)/(2θ)) exp(ε'C'PCε/(2θ) + ε'C'Py/θ)`. -/
theorem rc_worst_ratio {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (y : X → ℝ) (d : ℝ) (e : E → ℝ) :
    exp (-rcV P d (y + C *ᵥ e) / θ) = exp ((y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ)) *
      exp (1 / (2 * θ) * (e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e)) + θ⁻¹ * (e ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y)))) := by
  rw [← exp_add, rc_exponent hθ hP, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, dotProduct_comm (Cᵀ *ᵥ (P *ᵥ y)) e]
  congr 1
  field_simp
  ring

/-- Miao, p. 321: the exponent of `π m*`,
`−½ε'ε + ε'C'PCε/(2θ) + ε'C'Py/θ = −½ε'Kε + ε'K(θI − C'PC)⁻¹C'Py`, `K = I − θ⁻¹C'PC`. -/
theorem rc_worst_exponent {θ : ℝ} (hθ : θ ≠ 0) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hH : IsUnit (rcH θ C P).det) (y : X → ℝ) (e : E → ℝ) :
    -(1 / 2) * (e ⬝ᵥ e) + 1 / (2 * θ) * (e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e)) +
        θ⁻¹ * (e ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y))) =
      -(1 / 2) * (e ⬝ᵥ (rcK θ C P *ᵥ e)) + e ⬝ᵥ (rcK θ C P *ᵥ rcWstar θ C P y) := by
  have hKw : rcK θ C P *ᵥ rcWstar θ C P y = θ⁻¹ • (Cᵀ *ᵥ (P *ᵥ y)) := by
    rw [rcK_eq_smul hθ, smul_mulVec, rcWstar, mulVec_mulVec, mul_nonsing_inv _ hH, one_mulVec]
  rw [hKw, rcK, sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- Miao, p. 321: the worst-case distorted density `π*(ε) = π(ε)m*(ε)` is proportional to the
normal density with mean `w* = (θI − C'PC)⁻¹C'P(Ax + Bu)` and covariance `(I − θ⁻¹C'PC)⁻¹`
(here `y = Ax + Bu`), when `θI − C'PC > 0`. -/
theorem rc_worst_density {θ : ℝ} (hθ : 0 < θ) {C : Matrix X E ℝ} {P : Matrix X X ℝ}
    (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ) (d : ℝ) :
    ∃ k : ℝ, 0 < k ∧ ∀ e, rcStdPdf e * exp (-rcV P d (y + C *ᵥ e) / θ) =
      k * rcGaussPdf (rcWstar θ C P y) (rcK θ C P)⁻¹ e := by
  have hK := (rcK_posDef_iff hθ C P).2 hH
  have hKu := (isUnit_iff_isUnit_det _).1 hK.isUnit
  have hKs := (SS.LQProblem.posDef_iff_real.1 hK).1
  have hHu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  have hdet : 0 < (rcK θ C P)⁻¹.det := hK.inv.det_pos
  set ws := rcWstar θ C P y
  set c0 := (y ⬝ᵥ (P *ᵥ y) + d) / (2 * θ)
  refine ⟨exp (1 / 2 * (ws ⬝ᵥ (rcK θ C P *ᵥ ws)) + c0) * Real.sqrt (rcK θ C P)⁻¹.det,
    mul_pos (exp_pos _) (Real.sqrt_pos.2 hdet), fun e => ?_⟩
  have hq : (e - ws) ⬝ᵥ (rcK θ C P *ᵥ (e - ws)) = e ⬝ᵥ (rcK θ C P *ᵥ e) -
      2 * (e ⬝ᵥ (rcK θ C P *ᵥ ws)) + ws ⬝ᵥ (rcK θ C P *ᵥ ws) := by
    rw [sub_eq_add_neg, SS.LQProblem.quad_add hKs]
    simp only [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
    rw [SS.LQProblem.dotProduct_mulVec_comm_of_symm hKs ws e]
    ring
  have hexp : -(1 / 2) * (e ⬝ᵥ e) + -rcV P d (y + C *ᵥ e) / θ =
      -(1 / 2) * ((e - ws) ⬝ᵥ (rcK θ C P *ᵥ (e - ws))) +
        (1 / 2 * (ws ⬝ᵥ (rcK θ C P *ᵥ ws)) + c0) := by
    have h1 := rc_worst_exponent hθ.ne' hHu y e
    have h2 : -rcV P d (y + C *ᵥ e) / θ = 1 / (2 * θ) * (e ⬝ᵥ ((Cᵀ * P * C) *ᵥ e)) +
        θ⁻¹ * (e ⬝ᵥ (Cᵀ *ᵥ (P *ᵥ y))) + c0 := by
      simp only [c0]
      rw [rc_exponent hθ.ne' hP, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        smul_eq_mul, dotProduct_comm (Cᵀ *ᵥ (P *ᵥ y)) e]
      field_simp
    rw [h2, hq]
    linear_combination h1
  have hs : 0 < Real.sqrt (rcK θ C P)⁻¹.det := Real.sqrt_pos.2 hdet
  rw [rcStdPdf, rcGaussPdf, nonsing_inv_nonsing_inv _ hKu, mul_assoc, ← exp_add, hexp, exp_add]
  field_simp

/-- Correction to p. 321: nonsingularity of `I − θ⁻¹C'PC` is not enough. With `θ = 1`, `C = 1`,
`P = 2` (scalar), `I − θ⁻¹C'PC = −1` is nonsingular, but the worst-case kernel
`π(ε) exp(−V(Cε)/θ) ∝ exp(−ε²/2) exp(ε²)` is not integrable: the minimising agent drives the
objective to `−∞` (the breakdown point); `I − θ⁻¹C'PC` must be positive definite. -/
theorem rc_nonsingular_not_enough :
    (1 : ℝ) - 1⁻¹ * 2 ≠ 0 ∧
      ¬ Integrable (fun e : ℝ => exp (-(1 / 2) * e ^ 2) * exp (e ^ 2)) volume := by
  refine ⟨by norm_num, ?_⟩
  have h : (fun e : ℝ => exp (-(1 / 2) * e ^ 2) * exp (e ^ 2)) =
      fun e => exp (-(-(1 / 2)) * e ^ 2) := by
    funext e
    rw [← exp_add]
    ring_nf
  rw [h, integrable_exp_neg_mul_sq_iff]
  norm_num

/-- Miao, p. 322: `R(V)` from the first line of (9.48). Under the worst-case law `π*` (mean
`w* = (θI − C'PC)⁻¹C'Py`, covariance `K⁻¹`), `∫V(y + Cε)π* + θ∫π* ln(π*/π) =
−½y'D(P)y − d/2 − (θ/2) ln det K⁻¹`. -/
theorem rc_R_first_line {ν : Measure (E → ℝ)} {θ : ℝ} (hθ : 0 < θ) {C : Matrix X E ℝ}
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ) (d : ℝ)
    (hν : RCMoments ν (rcWstar θ C P y) (rcK θ C P)⁻¹) :
    ∫ e, rcV P d (y + C *ᵥ e) ∂ν +
        θ * ∫ e, log (rcGaussPdf (rcWstar θ C P y) (rcK θ C P)⁻¹ e / rcStdPdf e) ∂ν =
      -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) - d / 2 - θ / 2 * log (rcK θ C P)⁻¹.det := by
  have := hν.prob
  have hK := (rcK_posDef_iff hθ C P).2 hH
  have hKu := (isUnit_iff_isUnit_det _).1 hK.isUnit
  have hHu := (isUnit_iff_isUnit_det _).1 hH.isUnit
  set ws := rcWstar θ C P y
  have hy : ∀ e : E → ℝ, y + C *ᵥ e = (y + C *ᵥ ws) + C *ᵥ (e - ws) := fun e => by
    rw [mulVec_sub]; abel
  obtain ⟨hi, hq⟩ := rc_moment_quad hν (y + C *ᵥ ws) C P
  have hV : ∫ e, rcV P d (y + C *ᵥ e) ∂ν = -(1 / 2) * ((y + C *ᵥ ws) ⬝ᵥ (P *ᵥ (y + C *ᵥ ws)) +
      trace (Cᵀ * P * C * (rcK θ C P)⁻¹)) - d / 2 := by
    have hfun : (fun e => rcV P d (y + C *ᵥ e)) = fun e =>
        -(1 / 2) * (((y + C *ᵥ ws) + C *ᵥ (e - ws)) ⬝ᵥ (P *ᵥ ((y + C *ᵥ ws) + C *ᵥ (e - ws)))) -
          d / 2 := funext fun e => by rw [rcV, hy e]
    rw [hfun, integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul, hq,
      integral_const, probReal_univ, one_smul]
  have hCPC : Cᵀ * P * C = θ • (1 - rcK θ C P) := by
    rw [rcK, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hθ.ne', one_smul]
  have htr : trace (Cᵀ * P * C * (rcK θ C P)⁻¹) =
      θ * (trace (rcK θ C P)⁻¹ - trace (1 : Matrix E E ℝ)) := by
    rw [hCPC, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, mul_nonsing_inv _ hKu, trace_smul,
      trace_sub, smul_eq_mul]
  have hmce := rc_mce_decomp (θ := θ) (C := C) hP hHu y ws
  rw [sub_self, mulVec_zero, dotProduct_zero, mul_zero, add_zero] at hmce
  rw [hV, eq_9_56 hν hK.inv, htr, trace_sub]
  linear_combination hmce

/-- The two lines of (9.48) agree for the quadratic value function (Miao, p. 322, "Alternatively,
we can compute this adjustment directly using the expression in the second line"). -/
theorem rc_R_lines_agree {ν ν' : Measure (E → ℝ)} (hν : RCGaussian ν) {θ : ℝ} (hθ : 0 < θ)
    {C : Matrix X E ℝ} {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ)
    (d : ℝ) (hν' : RCMoments ν' (rcWstar θ C P y) (rcK θ C P)⁻¹) :
    ∫ e, rcV P d (y + C *ᵥ e) ∂ν' +
        θ * ∫ e, log (rcGaussPdf (rcWstar θ C P y) (rcK θ C P)⁻¹ e / rcStdPdf e) ∂ν' =
      rcR ν (fun e => rcV P d (y + C *ᵥ e)) θ := by
  rw [rc_R_first_line hθ hP hH y d hν', (rc_R_quad hν hθ hP hH y d).2]

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 9.3: the multiplier problem as `θ → ∞`

Miao, §9.7, Exercise 9.3, p. 325: as `θ → ∞` the solution of the multiplier problem (9.52)–(9.55)
converges to the solution of the standard control problem.

* `rc_log_det_bounds`: for `Y ≥ 0` with `I − Y > 0` and `tr Y < 1`,
  `tr Y ≤ −ln det(I − Y) ≤ tr Y/(1 − tr Y)` (via the eigenvalues of `I − Y`).
* `rc_D_tendsto`: along any family `P_θ → P` (with `P_θ ≥ 0`), `D_θ(P_θ) → P`; in particular
  `D_θ(P) → P` for fixed `P`.
* `rc_d_tendsto`: `d_θ(P_θ) = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'P_θC)⁻¹ → (1 − β)⁻¹β tr(PCC')`, the
  constant of the standard problem (§9.3, (9.16)).
* `rc_T_tendsto`, `rc_F_tendsto`: continuity of `T` and of the gain at `P ≥ 0`.
* **Exercise 9.3** (`ex_9_3`): if `P_θ ≥ 0` solve `P_θ = T(D_θ(P_θ))` (9.53) with
  `θI − C'P_θC > 0` and `P_θ → P` as `θ → ∞`, then `P ≥ 0` solves the standard Riccati equation
  `P = T(P)` (9.12), the robust gain (9.52) converges to the standard gain `F(P)` (9.17), and
  `d_θ` (9.55) converges to the standard constant; `ex_9_3_unique`: under the hypotheses of
  Proposition 9.3.1 the limit is the unique positive semidefinite solution of (9.12).

Departure: the exercise asks to show convergence; we assume that the robust solutions converge
(as they do along the monotone value iteration when it is bounded) and identify the limit, and we
prove the convergence of the constant, of `D_θ` and of the gain.
-/

open Matrix Filter Topology Real

namespace Miao.LinearQuadratic

variable {X E : Type*} [Fintype X] [Fintype E] [DecidableEq E]

/-- `tr Y ≤ −ln det(I − Y) ≤ tr Y/(1 − tr Y)` for `Y ≥ 0`, `I − Y > 0`, `tr Y < 1`. -/
theorem rc_log_det_bounds {Y : Matrix E E ℝ} (hY : Y.PosSemidef) (hK : (1 - Y).PosDef)
    (htr : trace Y < 1) :
    trace Y ≤ -log (1 - Y).det ∧ -log (1 - Y).det ≤ trace Y / (1 - trace Y) := by
  have hKh : (1 - Y).IsHermitian := hK.isHermitian
  have hdet : (1 - Y).det = ∏ i, hKh.eigenvalues i := by
    simpa using hKh.det_eq_prod_eigenvalues
  have htrK : trace (1 - Y) = ∑ i, hKh.eigenvalues i := by
    simpa using hKh.trace_eq_sum_eigenvalues
  have hpos : ∀ i, 0 < hKh.eigenvalues i := hK.eigenvalues_pos
  have hYq := (SS.LQProblem.posSemidef_iff_real.1 hY).2
  have hle : ∀ i, hKh.eigenvalues i ≤ 1 := by
    intro i
    set v := (hKh.eigenvectorBasis i).ofLp
    have hmv : (1 - Y) *ᵥ v = hKh.eigenvalues i • v := hKh.mulVec_eigenvectorBasis i
    have hv0 : v ≠ 0 := by
      simpa [v] using hKh.eigenvectorBasis.orthonormal.ne_zero i
    have hvv : 0 < v ⬝ᵥ v := by
      have h0 : 0 ≤ v ⬝ᵥ v := Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)
      refine lt_of_le_of_ne h0 fun h => hv0 ?_
      exact dotProduct_self_eq_zero.1 h.symm
    have h1 : v ⬝ᵥ ((1 - Y) *ᵥ v) = v ⬝ᵥ v - v ⬝ᵥ (Y *ᵥ v) := by
      rw [sub_mulVec, one_mulVec, dotProduct_sub]
    rw [hmv, dotProduct_smul, smul_eq_mul] at h1
    have := hYq v
    by_contra hgt
    push Not at hgt
    nlinarith
  have hlog : log (1 - Y).det = ∑ i, log (hKh.eigenvalues i) := by
    rw [hdet, Real.log_prod]
    intro i _
    exact (hpos i).ne'
  have htrY : trace Y = ∑ i, (1 - hKh.eigenvalues i) := by
    rw [Finset.sum_sub_distrib, ← htrK, trace_sub, trace_one]
    simp
  have hδ : ∀ i, 1 - hKh.eigenvalues i ≤ trace Y := by
    intro i
    rw [htrY]
    exact Finset.single_le_sum (f := fun j => 1 - hKh.eigenvalues j)
      (fun j _ => by linarith [hle j]) (Finset.mem_univ i)
  refine ⟨?_, ?_⟩
  · rw [hlog, htrY, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    linarith [Real.log_le_sub_one_of_pos (hpos i)]
  · rw [hlog, ← Finset.sum_neg_distrib, htrY, Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hk := hpos i
    have h1 : -log (hKh.eigenvalues i) ≤ (1 - hKh.eigenvalues i) / hKh.eigenvalues i := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hk)
      rw [Real.log_inv] at this
      rw [sub_div, div_self hk.ne']
      linarith [one_div (hKh.eigenvalues i)]
    refine h1.trans ?_
    have hlow : 1 - trace Y ≤ hKh.eigenvalues i := by linarith [hδ i]
    rw [← htrY]
    exact div_le_div_of_nonneg_left (by linarith [hle i]) (by linarith) hlow

/-- Matrix multiplication is continuous along any filter. -/
theorem rc_tendsto_mul {α : Type*} {l : Filter α} {m n p : Type*} [Fintype n]
    {f : α → Matrix m n ℝ} {g : α → Matrix n p ℝ} {a : Matrix m n ℝ} {b : Matrix n p ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun s => f s * g s) l (𝓝 (a * b)) :=
  ((Continuous.matrix_mul continuous_fst continuous_snd).tendsto (a, b)).comp (hf.prodMk_nhds hg)

/-- Inversion is continuous at an invertible matrix, along any filter. -/
theorem rc_tendsto_inv {α : Type*} {l : Filter α} {f : α → Matrix E E ℝ} {a : Matrix E E ℝ}
    (ha : IsUnit a.det) (hf : Tendsto f l (𝓝 a)) : Tendsto (fun s => (f s)⁻¹) l (𝓝 a⁻¹) := by
  have h : ContinuousAt Ring.inverse a.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ ha.ne_zero
  exact (continuousAt_matrix_inv a h).tendsto.comp hf

omit [DecidableEq E] in
theorem rc_tendsto_smul {α : Type*} {l : Filter α} {m n : Type*} {c : α → ℝ} {f : α → Matrix m n ℝ}
    {c₀ : ℝ} {a : Matrix m n ℝ} (hc : Tendsto c l (𝓝 c₀)) (hf : Tendsto f l (𝓝 a)) :
    Tendsto (fun s => c s • f s) l (𝓝 (c₀ • a)) := hc.smul hf

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for `c ≠ 0`. -/
theorem rc_inv_smul {c : ℝ} (hc : c ≠ 0) (A : Matrix E E ℝ) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_smul' _ (Units.mk0 c hc) h
  · have h' : ¬ IsUnit (c • A).det := by
      rw [det_smul]
      exact fun hu => h (isUnit_of_mul_isUnit_right hu)
    rw [nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit _ h', smul_zero]

/-- Exercise 9.3: `D_θ(P_θ) = P_θ + P_θC(θI − C'P_θC)⁻¹C'P_θ → P` as `θ → ∞` when `P_θ → P`. -/
theorem rc_D_tendsto {C : Matrix X E ℝ} {Pθ : ℝ → Matrix X X ℝ} {P : Matrix X X ℝ}
    (hlim : Tendsto Pθ atTop (𝓝 P)) :
    Tendsto (fun θ => rcD θ C (Pθ θ)) atTop (𝓝 P) := by
  have hX : Tendsto (fun θ => Cᵀ * Pθ θ * C) atTop (𝓝 (Cᵀ * P * C)) :=
    rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds hlim) tendsto_const_nhds
  have hK : Tendsto (fun θ => rcK θ C (Pθ θ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Matrix E E ℝ))).sub
      (rc_tendsto_smul (tendsto_inv_atTop_zero (𝕜 := ℝ)) hX)
    rw [zero_smul, sub_zero] at this
    exact this
  have hKi : Tendsto (fun θ => (rcK θ C (Pθ θ))⁻¹) atTop (𝓝 1) := by
    simpa using rc_tendsto_inv (by simp) hK
  have hHi : Tendsto (fun θ => (rcH θ C (Pθ θ))⁻¹) atTop (𝓝 0) := by
    have h := rc_tendsto_smul (tendsto_inv_atTop_zero (𝕜 := ℝ)) hKi
    rw [zero_smul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with θ hθ
    rw [rcH_eq_smul hθ.ne', rc_inv_smul hθ.ne']
  have h := rc_tendsto_mul (rc_tendsto_mul (rc_tendsto_mul (rc_tendsto_mul hlim
    (tendsto_const_nhds (x := C))) hHi) (tendsto_const_nhds (x := Cᵀ))) hlim
  simpa [rcD] using hlim.add h

/-- Exercise 9.3: the constant (9.55) converges to the constant of the standard problem,
`d_θ(P_θ) = (1 − β)⁻¹βθ ln det(I − θ⁻¹C'P_θC)⁻¹ → (1 − β)⁻¹β tr(PCC')`. -/
theorem rc_d_tendsto (β : ℝ) {C : Matrix X E ℝ} {Pθ : ℝ → Matrix X X ℝ} {P : Matrix X X ℝ}
    (hpsd : ∀ᶠ θ in atTop, (Pθ θ).PosSemidef) (hH : ∀ᶠ θ in atTop, (rcH θ C (Pθ θ)).PosDef)
    (hlim : Tendsto Pθ atTop (𝓝 P)) :
    Tendsto (fun θ => rcd β θ C (Pθ θ)) atTop (𝓝 ((1 - β)⁻¹ * (β * trace (P * C * Cᵀ)))) := by
  have hX : Tendsto (fun θ => Cᵀ * Pθ θ * C) atTop (𝓝 (Cᵀ * P * C)) :=
    rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds hlim) tendsto_const_nhds
  have htrX : Tendsto (fun θ => trace (Cᵀ * Pθ θ * C)) atTop (𝓝 (trace (Cᵀ * P * C))) :=
    ((continuous_id.matrix_trace).tendsto _).comp hX
  have htrY : Tendsto (fun θ : ℝ => θ⁻¹ * trace (Cᵀ * Pθ θ * C)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul htrX
  have hup : Tendsto (fun θ : ℝ => trace (Cᵀ * Pθ θ * C) / (1 - θ⁻¹ * trace (Cᵀ * Pθ θ * C)))
      atTop (𝓝 (trace (Cᵀ * P * C))) := by
    have := htrX.div ((tendsto_const_nhds (x := (1 : ℝ))).sub htrY) (by norm_num)
    rw [sub_zero, div_one] at this
    exact this
  have hg : Tendsto (fun θ => θ * log (rcK θ C (Pθ θ))⁻¹.det) atTop
      (𝓝 (trace (Cᵀ * P * C))) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htrX hup ?_ ?_
    · filter_upwards [hpsd, hH, eventually_gt_atTop 0, htrY.eventually (gt_mem_nhds one_pos)]
        with θ hP hHθ hθ hlt
      have hY : (θ⁻¹ • (Cᵀ * Pθ θ * C)).PosSemidef :=
        (SS.LQProblem.posSemidef_transpose_mul_mul hP C).smul (inv_nonneg.2 hθ.le)
      have hK : (1 - θ⁻¹ • (Cᵀ * Pθ θ * C)).PosDef := (rcK_posDef_iff hθ C _).2 hHθ
      have htr : trace (θ⁻¹ • (Cᵀ * Pθ θ * C)) < 1 := by rw [trace_smul, smul_eq_mul]; exact hlt
      have hb := (rc_log_det_bounds hY hK htr).1
      rw [trace_smul, smul_eq_mul] at hb
      rw [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
      have := mul_le_mul_of_nonneg_left hb hθ.le
      rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul] at this
      exact this
    · filter_upwards [hpsd, hH, eventually_gt_atTop 0, htrY.eventually (gt_mem_nhds one_pos)]
        with θ hP hHθ hθ hlt
      have hY : (θ⁻¹ • (Cᵀ * Pθ θ * C)).PosSemidef :=
        (SS.LQProblem.posSemidef_transpose_mul_mul hP C).smul (inv_nonneg.2 hθ.le)
      have hK : (1 - θ⁻¹ • (Cᵀ * Pθ θ * C)).PosDef := (rcK_posDef_iff hθ C _).2 hHθ
      have htr : trace (θ⁻¹ • (Cᵀ * Pθ θ * C)) < 1 := by rw [trace_smul, smul_eq_mul]; exact hlt
      have hb := (rc_log_det_bounds hY hK htr).2
      rw [trace_smul, smul_eq_mul] at hb
      rw [det_nonsing_inv, Ring.inverse_eq_inv', Real.log_inv]
      have := mul_le_mul_of_nonneg_left hb hθ.le
      refine this.trans_eq ?_
      have h1 : 1 - θ⁻¹ * trace (Cᵀ * Pθ θ * C) ≠ 0 := by linarith
      field_simp
  have htr : trace (Cᵀ * P * C) = trace (P * C * Cᵀ) := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [← htr]
  refine (hg.const_mul β).const_mul (1 - β)⁻¹ |>.congr fun θ => ?_
  rw [rcd]
  ring

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype E] [DecidableEq E] in
/-- The gain map `P ↦ F(P)` and the Riccati operator `T` are continuous at `P ≥ 0`
(`R > 0`, `β ≥ 0`). -/
theorem rc_T_F_tendsto (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {α : Type*}
    {l : Filter α} {Pn : α → Matrix X X ℝ} {P : Matrix X X ℝ} (hP : P.PosSemidef)
    (h : Tendsto Pn l (𝓝 P)) :
    Tendsto (fun s => L.T (Pn s)) l (𝓝 (L.T P)) ∧ Tendsto (fun s => L.F (Pn s)) l (𝓝 (L.F P)) := by
  have hG : Tendsto (fun s => L.G (Pn s)) l (𝓝 (L.G P)) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have hGi := rc_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.G_posDef hR hP hβ).isUnit) hG
  have hN : Tendsto (fun s => L.N (Pn s)) l (𝓝 (L.N P)) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have hF : Tendsto (fun s => L.F (Pn s)) l (𝓝 (L.F P)) := rc_tendsto_mul hGi hN
  refine ⟨?_, hF⟩
  have h1 : Tendsto (fun s => L.Q + L.β • (L.Aᵀ * Pn s * L.A)) l
      (𝓝 (L.Q + L.β • (L.Aᵀ * P * L.A))) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have h2 : Tendsto (fun s => L.S + L.β • (L.Aᵀ * Pn s * L.B)) l
      (𝓝 (L.S + L.β • (L.Aᵀ * P * L.B))) :=
    tendsto_const_nhds.add (rc_tendsto_smul tendsto_const_nhds
      (rc_tendsto_mul (rc_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds))
  have h3 := h1.sub (rc_tendsto_mul h2 hF)
  simp only [← LSProblem.T_eq_sub] at h3
  exact h3

omit [Fintype X] in
/-- A limit of positive semidefinite matrices is positive semidefinite. -/
theorem rc_posSemidef_of_tendsto [Finite X] {α : Type*} {l : Filter α} [l.NeBot]
    {Pn : α → Matrix X X ℝ} {P : Matrix X X ℝ} (hpsd : ∀ᶠ s in l, (Pn s).PosSemidef)
    (h : Tendsto Pn l (𝓝 P)) : P.PosSemidef := by
  cases nonempty_fintype X
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun x => ?_⟩
  · have ht : Tendsto (fun s => (Pn s)ᵀ) l (𝓝 Pᵀ) :=
      ((continuous_id.matrix_transpose).tendsto _).comp h
    refine tendsto_nhds_unique_of_eventuallyEq ht h ?_
    filter_upwards [hpsd] with s hs
    exact (SS.LQProblem.posSemidef_iff_real.1 hs).1
  · have hq : Tendsto (fun s => x ⬝ᵥ (Pn s *ᵥ x)) l (𝓝 (x ⬝ᵥ (P *ᵥ x))) :=
      ((continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)).tendsto
        _).comp h
    refine ge_of_tendsto hq ?_
    filter_upwards [hpsd] with s hs
    exact (SS.LQProblem.posSemidef_iff_real.1 hs).2 x

/-- **Exercise 9.3** (Miao, p. 325): as `θ → ∞` the solution of the multiplier problem
(9.52)–(9.55) converges to the solution of the standard problem. If `P_θ ≥ 0` solve the robust
Riccati equation `P_θ = T(D_θ(P_θ))` (9.53) with `θI − C'P_θC > 0` and `P_θ → P`, then `P ≥ 0`
solves the standard Riccati equation `P = T(P)` (9.12); `D_θ(P_θ) → P`; the robust gain (9.52)
converges to the standard gain `F(P)` (9.17); and `d_θ` (9.55) converges to the standard constant
`(1 − β)⁻¹β tr(PCC')`. -/
theorem ex_9_3 (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) {Pθ : ℝ → Matrix X X ℝ}
    {P : Matrix X X ℝ} (hpsd : ∀ᶠ θ in atTop, (Pθ θ).PosSemidef)
    (hH : ∀ᶠ θ in atTop, (rcH θ L.C (Pθ θ)).PosDef)
    (hfix : ∀ᶠ θ in atTop, L.T (rcD θ L.C (Pθ θ)) = Pθ θ) (hlim : Tendsto Pθ atTop (𝓝 P)) :
    P.PosSemidef ∧ L.T P = P ∧ Tendsto (fun θ => rcD θ L.C (Pθ θ)) atTop (𝓝 P) ∧
      Tendsto (fun θ => L.F (rcD θ L.C (Pθ θ))) atTop (𝓝 (L.F P)) ∧
      Tendsto (fun θ => rcd L.β θ L.C (Pθ θ)) atTop
        (𝓝 ((1 - L.β)⁻¹ * (L.β * trace (P * L.C * L.Cᵀ)))) := by
  have hP := rc_posSemidef_of_tendsto hpsd hlim
  have hD := rc_D_tendsto (C := L.C) hlim
  obtain ⟨hT, hF⟩ := rc_T_F_tendsto L hR hβ hP hD
  refine ⟨hP, ?_, hD, hF, rc_d_tendsto L.β hpsd hH hlim⟩
  exact tendsto_nhds_unique_of_eventuallyEq hT hlim hfix

/-- **Exercise 9.3**, the limit is the standard solution: under the hypotheses of
Proposition 9.3.1 (`S = 0`, `Q > 0`, `R > 0`, `(√βA, √βB)` controllable or stabilizable), the
limit `P` of the robust solutions is the unique positive semidefinite solution of (9.12). -/
theorem ex_9_3_unique [Nonempty X] [DecidableEq X] (L : LSProblem X U E) (hS : L.S = 0)
    (hQ : L.Q.PosDef) (hR : L.R.PosDef) (hβ : 0 ≤ L.β)
    (hstab : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B))
    {Pθ : ℝ → Matrix X X ℝ} {P : Matrix X X ℝ} (hpsd : ∀ᶠ θ in atTop, (Pθ θ).PosSemidef)
    (hH : ∀ᶠ θ in atTop, (rcH θ L.C (Pθ θ)).PosDef)
    (hfix : ∀ᶠ θ in atTop, L.T (rcD θ L.C (Pθ θ)) = Pθ θ) (hlim : Tendsto Pθ atTop (𝓝 P)) :
    ∀ P' : Matrix X X ℝ, P'.PosSemidef → L.T P' = P' → P' = P := by
  obtain ⟨hP, hfixP, -⟩ := ex_9_3 L hR hβ hpsd hH hfix hlim
  obtain ⟨Ps, -, huniq, -⟩ := L.proposition_9_3_1 hS hQ hR hβ hstab
  intro P' hP' hfix'
  rw [huniq P' hP' hfix', huniq P hP hfixP]

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 9.5: the robust consumption rule

Miao, §9.7, Exercise 9.5, p. 326: the multiplier problem for Hall's consumption-saving problem
(Exercise 9.4), `max −E∑βᵗ(c_t − b)²`, `c_t + a_{t+1} = Ra_t + y_t`,
`y_{t+1} = μ(1 − ρ) + ρy_t + σε_{t+1}`, state `x = [1, a, y]'`. In the normalisation of §9.6,
`r = −½(x'Qx + u'Ru + 2x'Su) = −(c − b)²` (`rcHallRobust`: Hall's `Q, R, S` doubled;
`ex_9_5_loss`; the transition is that of Exercise 9.4, `ex_9_5_data`).

With `κ = βR² > 1`, `w = [μR/(R − 1) − μR/(R − ρ) − bR/(R − 1), R, R/(R − ρ)]` (`hallW`, the vector
of Exercise 9.4), `k = σ²R²/(R − ρ)² = (w'C)²` (`rcHallK`) and `θ > 2k`:

* `ex_9_5`: `P = 2q_θ ww'` with `q_θ = θ(κ − 1)/(θκ − 2k)` (`rcHallQθ`, `rcHallPθ`) solves the
  robust Riccati equation `P = T(D(P))` (9.53), with `θ − C'PC > 0` and `D(P) = θP/(θ − 2q_θk)`
  (rank one in the same direction); the robust gain (9.52) is `F = −(be₁' + q_θw')`.
* `ex_9_5_rule`: the robust consumption rule
  `c_t = b + q_θ(Ra_t + Ry_t/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`; in Hall's case
  `βR = 1`, `q_θ = θ(R − 1)/(θR − 2k)` (`ex_9_5_hall_case`).
* `ex_9_5_bellman`: with Gaussian shocks and `β < 1`, `V(x) = −½x'Px − d/2` with (9.55) solves the
  robust Bellman equation, and the rule is the unique maximiser.
* `ex_9_5_limit`: `q_θ → q = 1 − 1/(βR²)` as `θ → ∞` (the rule of Exercise 9.4, cf. Exercise 9.3);
  `ex_9_5_more_responsive`: for `σ ≠ 0`, `q_θ > q`: the robust consumer's consumption responds more
  to wealth.
* `ex_9_5_breakdown`: the breakdown point is `θ = 2k`: on the robust solution
  `θ − C'PC = θκ(θ − 2k)/(θκ − 2k)`.
-/

open Matrix Filter Topology

namespace Miao.LinearQuadratic

/-- Hall's problem in the normalisation of §9.6: `−½(x'Qx + u'Ru + 2x'Su) = −(c − b)²`. -/
noncomputable def rcHallRobust (b μ Rr ρ σ β : ℝ) : LSProblem (Fin 3) (Fin 1) (Fin 1) where
  A := !![1, 0, 0; 0, Rr, 1; μ * (1 - ρ), 0, ρ]
  B := !![0; -1; 0]
  C := !![0; 0; σ]
  Q := !![2 * b ^ 2, 0, 0; 0, 0, 0; 0, 0, 0]
  R := !![2]
  S := !![-2 * b; 0; 0]
  β := β

/-- `k = σ²R²/(R − ρ)²`. -/
noncomputable def rcHallK (Rr ρ σ : ℝ) : ℝ := σ ^ 2 * (Rr / (Rr - ρ)) ^ 2

/-- `q_θ = θ(βR² − 1)/(θβR² − 2k)`. -/
noncomputable def rcHallQθ (Rr ρ σ β θ : ℝ) : ℝ :=
  θ * (β * Rr ^ 2 - 1) / (θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ)

/-- A rank-one matrix `p ww'`. -/
noncomputable def rcHallRank1 (b μ Rr ρ p : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => p * hallW b μ Rr ρ i * hallW b μ Rr ρ j

/-- The robust Riccati solution `P = 2q_θ ww'`. -/
noncomputable def rcHallPθ (b μ Rr ρ σ β θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  rcHallRank1 b μ Rr ρ (2 * rcHallQθ Rr ρ σ β θ)

/-- The gain `−(be₁' + q w')`. -/
noncomputable def rcHallGain (b μ Rr ρ q : ℝ) : Matrix (Fin 1) (Fin 3) ℝ :=
  Matrix.of fun _ j => -(![b, 0, 0] j + q * hallW b μ Rr ρ j)

variable (b μ Rr ρ σ β : ℝ)

/-- Exercise 9.5: `−½ loss = −(c − b)²` at `x = [1, a, y]'`, `u = c`. -/
theorem ex_9_5_loss (a y c : ℝ) :
    -(1 / 2) * (rcHallRobust b μ Rr ρ σ β).loss ![1, a, y] ![c] = -(c - b) ^ 2 := by
  simp [LSProblem.loss, rcHallRobust, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Exercise 9.5: the transition is that of Exercise 9.4. -/
theorem ex_9_5_data :
    (rcHallRobust b μ Rr ρ σ β).A = (hallProblem b μ Rr ρ σ β).A ∧
      (rcHallRobust b μ Rr ρ σ β).B = (hallProblem b μ Rr ρ σ β).B ∧
      (rcHallRobust b μ Rr ρ σ β).C = (hallProblem b μ Rr ρ σ β).C ∧
      (rcHallRobust b μ Rr ρ σ β).β = β :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {b μ Rr ρ σ β}

/-- The Riccati operator and gain on rank-one matrices `pww'`, parametrised by
`g = s/(2 + s)`, `s = βR²p` (so `p = 2g/(βR²(1 − g))`): `G = 2/(1 − g)`,
`F(pww') = −(be₁' + gw')` and `T(pww') = 2g ww'`. -/
theorem rc_hall_rank1_T (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : β * Rr ^ 2 ≠ 0) {g : ℝ} (hg : g ≠ 1) :
    (rcHallRobust b μ Rr ρ σ β).G (rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))) =
        !![2 / (1 - g)] ∧
      (rcHallRobust b μ Rr ρ σ β).F (rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))) =
        rcHallGain b μ Rr ρ g ∧
      (rcHallRobust b μ Rr ρ σ β).T (rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))) =
        rcHallRank1 b μ Rr ρ (2 * g) := by
  set L := rcHallRobust b μ Rr ρ σ β
  have hg' : 1 - g ≠ 0 := sub_ne_zero.2 (Ne.symm hg)
  have hβ0 : β ≠ 0 := fun h => hκ (by rw [h, zero_mul])
  have hR1' : Rr - 1 ≠ 0 := by linarith
  have hRr : Rr ≠ 0 := by linarith
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  set P := rcHallRank1 b μ Rr ρ (2 * g / (β * Rr ^ 2 * (1 - g)))
  have hGe : L.G P = !![2 / (1 - g)] := by
    ext i j
    fin_cases i; fin_cases j
    simp [L, P, LSProblem.G, rcHallRobust, rcHallRank1, hallW, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
    ring
  have hu : IsUnit (L.G P).det := by
    rw [hGe, det_fin_one_of]
    exact (div_ne_zero two_ne_zero hg').isUnit
  have hGF : L.G P * rcHallGain b μ Rr ρ g = L.N P := by
    rw [hGe]
    ext i j
    fin_cases i; fin_cases j <;>
      simp [L, P, LSProblem.N, rcHallRobust, rcHallRank1, rcHallGain, hallW, Matrix.mul_apply,
        Fin.sum_univ_three] <;> field_simp <;> ring
  have hF : L.F P = rcHallGain b μ Rr ρ g := by
    rw [LSProblem.F, ← hGF, nonsing_inv_mul_cancel_left _ _ hu]
  refine ⟨hGe, hF, ?_⟩
  rw [LSProblem.T_eq_sub, hF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L, P, rcHallRobust, rcHallRank1, rcHallGain, hallW, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- `θ − C'(pww')C = θ − pk` and `D(pww') = (θp/(θ − pk))ww'`. -/
theorem rc_hall_rank1_D {θ p : ℝ} (hθp : θ - p * rcHallK Rr ρ σ ≠ 0) :
    rcH θ (rcHallRobust b μ Rr ρ σ β).C (rcHallRank1 b μ Rr ρ p) = !![θ - p * rcHallK Rr ρ σ] ∧
      rcD θ (rcHallRobust b μ Rr ρ σ β).C (rcHallRank1 b μ Rr ρ p) =
        rcHallRank1 b μ Rr ρ (θ * p / (θ - p * rcHallK Rr ρ σ)) := by
  have hk : rcHallK Rr ρ σ = σ ^ 2 * hallW b μ Rr ρ 2 ^ 2 := by simp [rcHallK, hallW]
  rw [hk] at hθp ⊢
  have hθp' : -(p * hallW b μ Rr ρ 2 ^ 2 * σ ^ 2) + θ ≠ 0 := by
    intro h; apply hθp; linarith
  have hH : rcH θ (rcHallRobust b μ Rr ρ σ β).C (rcHallRank1 b μ Rr ρ p) =
      !![θ - p * (σ ^ 2 * hallW b μ Rr ρ 2 ^ 2)] := by
    ext i j
    fin_cases i; fin_cases j
    simp [rcH, rcHallRobust, rcHallRank1, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  refine ⟨hH, ?_⟩
  set t := (θ - p * (σ ^ 2 * hallW b μ Rr ρ 2 ^ 2))⁻¹ with htdef
  have ht : t * (θ - p * (σ ^ 2 * hallW b μ Rr ρ 2 ^ 2)) = 1 := inv_mul_cancel₀ hθp
  rw [rcD, hH, rc_inv_fin_one, ← htdef, div_eq_mul_inv, ← htdef]
  ext i j
  simp [rcHallRobust, rcHallRank1, Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination (-(p * hallW b μ Rr ρ i * hallW b μ Rr ρ j)) * ht

/-- The breakdown point of Exercise 9.5: on `P = 2q_θww'`,
`θ − C'PC = θκ(θ − 2k)/(θκ − 2k)`, `κ = βR²`; positive iff `θ > 2k` (given `κ > 1`). -/
theorem ex_9_5_breakdown {θ : ℝ} (hden : θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ ≠ 0) :
    θ - 2 * rcHallQθ Rr ρ σ β θ * rcHallK Rr ρ σ =
      θ * (β * Rr ^ 2) * (θ - 2 * rcHallK Rr ρ σ) / (θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ) := by
  rw [rcHallQθ]
  generalize hD : θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ = D at hden ⊢
  field_simp
  subst hD
  ring

/-- **Exercise 9.5** (Miao, p. 326): for `R > 1`, `|ρ| < 1`, `κ = βR² > 1` and
`θ > 2k`, `P = 2q_θww'` is positive semidefinite with `θ − C'PC > 0` and solves the robust
Riccati equation `P = T(D(P))` (9.53), and the robust gain (9.52) is `F = −(be₁' + q_θw')`. -/
theorem ex_9_5 (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) {θ : ℝ}
    (hθ : 2 * rcHallK Rr ρ σ < θ) :
    (rcHallPθ b μ Rr ρ σ β θ).PosSemidef ∧
      (rcH θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)).PosDef ∧
      (rcHallRobust b μ Rr ρ σ β).T
          (rcD θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) =
        rcHallPθ b μ Rr ρ σ β θ ∧
      (rcHallRobust b μ Rr ρ σ β).F
          (rcD θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) =
        rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) := by
  set k := rcHallK Rr ρ σ with hk
  set κ := β * Rr ^ 2 with hκdef
  have hk0 : 0 ≤ k := by simp only [k, rcHallK]; positivity
  have hθ0 : 0 < θ := by linarith
  have hden : 0 < θ * κ - 2 * k := by nlinarith
  set q := rcHallQθ Rr ρ σ β θ with hq
  have hqpos : 0 < q := by
    simp only [q, rcHallQθ, ← hκdef, ← hk]
    exact div_pos (mul_pos hθ0 (by linarith)) hden
  have hH0 : 0 < θ - 2 * q * k := by
    have h := ex_9_5_breakdown (σ := σ) (θ := θ) (β := β) (Rr := Rr) (ρ := ρ) hden.ne'
    rw [← hκdef, ← hk] at h
    rw [h]
    exact div_pos (mul_pos (mul_pos hθ0 (by linarith)) (by linarith)) hden
  obtain ⟨hH, hD⟩ := rc_hall_rank1_D (b := b) (μ := μ) (β := β) (θ := θ) (p := 2 * q) hH0.ne'
  have hq1 : 0 < 1 - q := by
    have : 1 - q = (θ - 2 * k) / (θ * κ - 2 * k) := by
      simp only [q, rcHallQθ, ← hκdef, ← hk]
      field_simp
      ring
    rw [this]
    exact div_pos (by linarith) hden
  have hκ0 : κ ≠ 0 := by linarith
  have hpt : θ * (2 * q) / (θ - 2 * q * k) = 2 * q / (κ * (1 - q)) := by
    have h := ex_9_5_breakdown (σ := σ) (θ := θ) (β := β) (Rr := Rr) (ρ := ρ) hden.ne'
    rw [← hκdef, ← hk] at h
    rw [h]
    have h1 : 1 - q = (θ - 2 * k) / (θ * κ - 2 * k) := by
      simp only [q, rcHallQθ, ← hκdef, ← hk]
      field_simp
      ring
    rw [h1]
    have h2 : θ - 2 * k ≠ 0 := by linarith
    field_simp
  obtain ⟨-, hF, hT⟩ := rc_hall_rank1_T (b := b) (μ := μ) (σ := σ) (β := β) hR1 hρ hκ0
    (g := q) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine SS.LQProblem.posSemidef_iff_real.2 ⟨?_, fun x => ?_⟩
    · ext i j
      simp only [rcHallPθ, rcHallRank1, transpose_apply, of_apply]
      ring
    · have : x ⬝ᵥ (rcHallPθ b μ Rr ρ σ β θ *ᵥ x) = 2 * q * (hallW b μ Rr ρ ⬝ᵥ x) ^ 2 := by
        simp only [rcHallPθ, rcHallRank1, dotProduct, mulVec, of_apply, Fin.sum_univ_three]
        ring
      rw [this]
      positivity
  · rw [rcHallPθ, hH]
    refine SS.LQProblem.posDef_iff_real.2 ⟨by ext i j; fin_cases i; fin_cases j; rfl,
      fun v hv => ?_⟩
    have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i; exact h0)
    simp only [dotProduct, mulVec, Fin.sum_univ_one, of_apply, cons_val', cons_val_fin_one,
      empty_val']
    have : 0 < v 0 * v 0 := mul_self_pos.2 hv0
    nlinarith
  · rw [rcHallPθ, hD, hpt, hT]
  · rw [rcHallPθ, hD, hpt, hF]

/-- **Exercise 9.5**, the robust consumption rule `c = −Fx` at `x = [1, a, y]'`:
`c = b + q_θ(Ra + Ry/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))`. -/
theorem ex_9_5_rule (θ a y : ℝ) :
    (-(rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) *ᵥ ![1, a, y])) 0 = b + rcHallQθ Rr ρ σ β θ *
      (Rr * a + Rr * y / (Rr - ρ) + μ * Rr / (Rr - 1) - μ * Rr / (Rr - ρ) -
        b * Rr / (Rr - 1)) := by
  simp [rcHallGain, hallW, vecHead, vecTail]
  ring

/-- **Exercise 9.5**, Hall's case `βR = 1`: `q_θ = θ(R − 1)/(θR − 2k)`. -/
theorem ex_9_5_hall_case (hβR : β * Rr = 1) (θ : ℝ) :
    rcHallQθ Rr ρ σ β θ = θ * (Rr - 1) / (θ * Rr - 2 * rcHallK Rr ρ σ) := by
  have h : β * Rr ^ 2 = Rr := by rw [pow_two, ← mul_assoc, hβR, one_mul]
  rw [rcHallQθ, h]

/-- **Exercise 9.5**, the robust Bellman equation: with Gaussian shocks and `0 < β < 1`,
`V(x) = −½x'Px − d/2` (`P = 2q_θww'`, `d` from (9.55)) solves the robust Bellman equation (9.49),
and the robust consumption rule is its unique maximiser. -/
theorem ex_9_5_bellman {ν : MeasureTheory.Measure (Fin 1 → ℝ)} (hν : RCGaussian ν) (hβ : 0 < β)
    (hβ1 : β < 1) (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) {θ : ℝ}
    (hθ : 2 * rcHallK Rr ρ σ < θ) (x : Fin 3 → ℝ) :
    IsGreatest (Set.range (rcRobObj (rcHallRobust b μ Rr ρ σ β) ν θ (rcHallPθ b μ Rr ρ σ β θ)
        (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x))
        (rcV (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x) ∧
      ∀ u, rcRobObj (rcHallRobust b μ Rr ρ σ β) ν θ (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x u =
          rcV (rcHallPθ b μ Rr ρ σ β θ)
            (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x ↔
        u = -(rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) *ᵥ x) := by
  obtain ⟨hP, hH, hfix, hF⟩ := ex_9_5 (b := b) (μ := μ) hR1 hρ hκ hθ
  have hR : (rcHallRobust b μ Rr ρ σ β).R.PosDef := by
    refine SS.LQProblem.posDef_iff_real.2 ⟨by ext i j; fin_cases i; fin_cases j; rfl,
      fun v hv => ?_⟩
    have hv0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i; exact h0)
    simp only [rcHallRobust, dotProduct, mulVec, Fin.sum_univ_one, of_apply, cons_val',
      cons_val_fin_one, empty_val']
    have : 0 < v 0 * v 0 := mul_self_pos.2 hv0
    nlinarith
  have hk0 : 0 ≤ rcHallK Rr ρ σ := by simp only [rcHallK]; positivity
  have hθ0 : 0 < θ := by linarith
  have h := eq_9_51_9_55 (rcHallRobust b μ Rr ρ σ β) hν hR hβ.le hβ1 hθ0 hP hH hfix x
  rw [hF] at h
  exact h

/-- **Exercise 9.5** and Exercise 9.3: `q_θ → q = 1 − 1/(βR²)` as `θ → ∞`, the rule of
Exercise 9.4. -/
theorem ex_9_5_limit (hκ : 1 < β * Rr ^ 2) :
    Tendsto (fun θ => rcHallQθ Rr ρ σ β θ) atTop (𝓝 (hallq Rr β)) := by
  have hκ0 : β * Rr ^ 2 ≠ 0 := by linarith
  have h : Tendsto (fun θ : ℝ => (β * Rr ^ 2 - 1) / (β * Rr ^ 2 - 2 * rcHallK Rr ρ σ * θ⁻¹))
      atTop (𝓝 ((β * Rr ^ 2 - 1) / (β * Rr ^ 2 - 2 * rcHallK Rr ρ σ * 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero (𝕜 := ℝ)))) (by simpa using hκ0)
  have hq : hallq Rr β = (β * Rr ^ 2 - 1) / (β * Rr ^ 2 - 2 * rcHallK Rr ρ σ * 0) := by
    rw [hallq, mul_zero, sub_zero, sub_div, div_self hκ0]
  rw [hq]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  rw [rcHallQθ]
  field_simp

/-- **Exercise 9.5**: for `σ ≠ 0` the robust consumer's marginal propensity to consume out of
`w'x` exceeds the standard one, `q_θ > q = 1 − 1/(βR²)`. -/
theorem ex_9_5_more_responsive (hR1 : 1 < Rr) (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) (hσ : σ ≠ 0)
    {θ : ℝ} (hθ : 2 * rcHallK Rr ρ σ < θ) : hallq Rr β < rcHallQθ Rr ρ σ β θ := by
  have hRρ : Rr - ρ ≠ 0 := by
    have := (abs_lt.1 hρ).2
    linarith
  have hk : 0 < rcHallK Rr ρ σ := by
    simp only [rcHallK]
    have : Rr / (Rr - ρ) ≠ 0 := div_ne_zero (by linarith) hRρ
    positivity
  have hθ0 : 0 < θ := by linarith
  have hden : 0 < θ * (β * Rr ^ 2) - 2 * rcHallK Rr ρ σ := by nlinarith
  rw [hallq, rcHallQθ, lt_div_iff₀ hden]
  have hκ0 : 0 < β * Rr ^ 2 := by linarith
  rw [one_sub_div hκ0.ne']
  rw [div_mul_eq_mul_div, div_lt_iff₀ hκ0]
  nlinarith

end Miao.LinearQuadratic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The standard normal shock satisfies the Gaussian identity

Miao, §9.6, pp. 321–322: the shocks are IID standard normal. Here we prove that the standard
normal law `N(0, I) = Measure.pi fun _ => gaussianReal 0 1` on `ℝ^{nε}` satisfies the moment
generating identity `RCGaussian` used in `RCRobustLQ`, for every symmetric `K` with `I − K > 0`
and every `b`:
`E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)`.

* `rc_gauss_1d`: the one-dimensional case, `E exp(½kx² + cx) = (1 − k)^{−1/2} exp(c²/(2(1 − k)))`
  for `k < 1`, by writing `π(x)exp(½kx² + cx)` as a multiple of the `N(c/(1 − k), 1/(1 − k))`
  density.
* `rc_std_map_eigen`: `N(0, I)` is invariant under the orthogonal eigenvector matrix `U` of `K`
  (from Mathlib's `stdGaussian` and its independence of the orthonormal basis).
* `rc_gaussian_std`: rotating by `U` diagonalises `K`, the integral factors into one-dimensional
  integrals, and `∏(1 − λᵢ) = det(I − K)`, `∑cᵢ²/(1 − λᵢ) = b'(I − K)⁻¹b` with `c = U'b`.
* Corollaries for the standard normal shock: `rc_R_quad_std`, `eq_9_51_9_55_std`,
  `rc_robust_bellman_std`, `ex_9_5_bellman_std`.
-/

open Matrix MeasureTheory ProbabilityTheory Real

namespace Miao.LinearQuadratic

/-- The one-dimensional Gaussian integral: for `k < 1`,
`E exp(½kx² + cx) = (1 − k)^{−1/2} exp(c²/(2(1 − k)))` under `N(0, 1)`. -/
theorem rc_gauss_1d {k : ℝ} (hk : k < 1) (c : ℝ) :
    Integrable (fun x => exp (1 / 2 * k * x ^ 2 + c * x)) (gaussianReal 0 1) ∧
      ∫ x, exp (1 / 2 * k * x ^ 2 + c * x) ∂(gaussianReal 0 1) =
        (√(1 - k))⁻¹ * exp (c ^ 2 / (2 * (1 - k))) := by
  have ha : 0 < 1 - k := by linarith
  have hv : (((1 - k)⁻¹).toNNReal : ℝ) = (1 - k)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 ha.le)
  have hv0 : ((1 - k)⁻¹).toNNReal ≠ 0 := by
    intro h
    have := congrArg (fun z : NNReal => (z : ℝ)) h
    simp only [hv, NNReal.coe_zero] at this
    exact (inv_pos.2 ha).ne' this
  have hs : 0 < √(1 - k) := Real.sqrt_pos.2 ha
  have hpi : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  have key : ∀ x, gaussianPDFReal 0 1 x * exp (1 / 2 * k * x ^ 2 + c * x) =
      ((√(1 - k))⁻¹ * exp (c ^ 2 / (2 * (1 - k)))) *
        gaussianPDFReal (c / (1 - k)) ((1 - k)⁻¹).toNNReal x := by
    intro x
    simp only [gaussianPDFReal, hv, NNReal.coe_one, mul_one, sub_zero]
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 * π by positivity) ((1 - k)⁻¹), Real.sqrt_inv]
    have h2 : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have h3 : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
    have e : -x ^ 2 / 2 + (1 / 2 * k * x ^ 2 + c * x) =
        c ^ 2 / (2 * (1 - k)) + -(x - c / (1 - k)) ^ 2 / (2 * (1 - k)⁻¹) := by
      field_simp
      ring
    rw [mul_assoc, ← exp_add, e, exp_add]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero, integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    simp only [toReal_gaussianPDF, smul_eq_mul, key]
    exact (integrable_gaussianPDFReal _ _).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul, key]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hv0, mul_one]

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The standard normal law on `ℝ^{nε}` is invariant under the orthogonal eigenvector matrix of a
symmetric matrix: `(U·)_*N(0, I) = N(0, I)`. -/
theorem rc_std_map_eigen {K : Matrix E E ℝ} (hK : K.IsHermitian) :
    (Measure.pi fun _ : E => gaussianReal 0 1).map
        (fun x => (hK.eigenvectorUnitary : Matrix E E ℝ) *ᵥ x) =
      Measure.pi fun _ : E => gaussianReal 0 1 := by
  set ν := Measure.pi fun _ : E => gaussianReal 0 1
  set U : Matrix E E ℝ := (hK.eigenvectorUnitary : Matrix E E ℝ)
  have hΦ : (fun x : E → ℝ => ∑ i, x i • hK.eigenvectorBasis i) =
      (WithLp.toLp 2 : (E → ℝ) → EuclideanSpace ℝ E) ∘ fun x => U *ᵥ x := by
    funext x
    ext j
    simp [U, mulVec, dotProduct, mul_comm]
  have hto : Measurable (WithLp.toLp 2 : (E → ℝ) → EuclideanSpace ℝ E) := by fun_prop
  have hof : Measurable (WithLp.ofLp : EuclideanSpace ℝ E → (E → ℝ)) := by fun_prop
  have hT : Measurable fun x : E → ℝ => U *ᵥ x :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have h1 := map_pi_eq_stdGaussian (ι := E)
  rw [stdGaussian_eq_map_pi_orthonormalBasis hK.eigenvectorBasis, hΦ,
    ← Measure.map_map hto hT] at h1
  have h2 := congrArg (fun m : Measure (EuclideanSpace ℝ E) => m.map WithLp.ofLp) h1
  simp only [Measure.map_map hof hto] at h2
  have hid : (WithLp.ofLp : EuclideanSpace ℝ E → (E → ℝ)) ∘ WithLp.toLp 2 = id := by
    funext x; rfl
  rw [hid, Measure.map_id, Measure.map_id] at h2
  exact h2.symm

/-- **The standard normal shock satisfies `RCGaussian`** (Miao, p. 321): for symmetric `K` with
`I − K > 0`, `E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)` under
`ε ~ N(0, I)`, with the integrand integrable. -/
theorem rc_gaussian_std : RCGaussian (Measure.pi fun _ : E => gaussianReal 0 1) := by
  set ν := Measure.pi fun _ : E => gaussianReal 0 1 with hνdef
  have key : ∀ (K : Matrix E E ℝ) (b : E → ℝ), Kᵀ = K → (1 - K).PosDef →
      Integrable (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ν ∧
      ∫ e, exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e) ∂ν =
        (Real.sqrt (1 - K).det)⁻¹ * exp (1 / 2 * (b ⬝ᵥ ((1 - K)⁻¹ *ᵥ b))) := by
    intro K b hKs hpos
    have hK : K.IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact hKs
    set U : Matrix E E ℝ := (hK.eigenvectorUnitary : Matrix E E ℝ) with hUdef
    set lam := hK.eigenvalues
    have hstar : star U = Uᵀ := by
      rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    have hUU : Uᵀ * U = 1 := by rw [← hstar]; exact Unitary.coe_star_mul_self _
    have hUU' : U * Uᵀ = 1 := by rw [← hstar]; exact Unitary.coe_mul_star_self _
    have hD : Uᵀ * K * U = diagonal lam := by
      have h2 := hK.conjStarAlgAut_star_eigenvectorUnitary
      simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h2
      rw [← hstar]
      simpa using h2
    have hKU : K = U * diagonal lam * Uᵀ := by
      rw [← hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU', Matrix.one_mul, Matrix.mul_assoc,
        hUU', Matrix.mul_one]
    set c := Uᵀ *ᵥ b
    -- the quadratic form in the rotated coordinates
    have hquad : ∀ x : E → ℝ, (U *ᵥ x) ⬝ᵥ (K *ᵥ (U *ᵥ x)) = ∑ i, lam i * x i ^ 2 := by
      intro x
      rw [← SS.LQProblem.dotProduct_transpose_mul_mul, hD]
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hlin : ∀ x : E → ℝ, b ⬝ᵥ (U *ᵥ x) = ∑ i, c i * x i := by
      intro x
      rw [dotProduct_mulVec, ← mulVec_transpose]
      rfl
    have hlam : ∀ i, lam i < 1 := by
      intro i
      set v := U *ᵥ Pi.single i (1 : ℝ)
      have hv : v ≠ 0 := by
        intro h0
        have : Uᵀ *ᵥ v = Pi.single i 1 := by
          simp only [v, mulVec_mulVec, hUU, one_mulVec]
        rw [h0, mulVec_zero] at this
        have := congrFun this i
        simp at this
      have h := (SS.LQProblem.posDef_iff_real.1 hpos).2 hv
      have hvv : v ⬝ᵥ v = 1 := by
        have : v ⬝ᵥ ((1 : Matrix E E ℝ) *ᵥ v) = Pi.single i (1 : ℝ) ⬝ᵥ
            ((Uᵀ * 1 * U) *ᵥ Pi.single i 1) :=
          SS.LQProblem.dotProduct_transpose_mul_mul U 1 _ |>.symm
        rw [one_mulVec, Matrix.mul_one, hUU, one_mulVec] at this
        rw [this]
        simp
      rw [sub_mulVec, one_mulVec, dotProduct_sub, hvv, hquad] at h
      have hs : ∑ j, lam j * (Pi.single i (1 : ℝ) : E → ℝ) j ^ 2 = lam i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      linarith
    have h1d := fun i => rc_gauss_1d (hlam i) (c i)
    have hFT : (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ∘ (fun x => U *ᵥ x) =
        fun x => ∏ i, exp (1 / 2 * lam i * x i ^ 2 + c i * x i) := by
      funext x
      simp only [Function.comp_apply, hquad, hlin, ← Real.exp_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hT : Measurable fun x : E → ℝ => U *ᵥ x :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    have hFc : Continuous fun e : E → ℝ => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e) := by
      fun_prop
    have hmap := rc_std_map_eigen hK
    rw [← hνdef, ← hUdef] at hmap
    have hint : Integrable (fun e => exp (1 / 2 * (e ⬝ᵥ (K *ᵥ e)) + b ⬝ᵥ e)) ν := by
      rw [← hmap, integrable_map_measure hFc.aestronglyMeasurable hT.aemeasurable, hFT]
      exact Integrable.fintype_prod fun i => (h1d i).1
    refine ⟨hint, ?_⟩
    rw [← hmap, integral_map hT.aemeasurable hFc.aestronglyMeasurable]
    have e1 : ∫ x, exp (1 / 2 * ((U *ᵥ x) ⬝ᵥ (K *ᵥ (U *ᵥ x))) + b ⬝ᵥ (U *ᵥ x)) ∂ν =
        ∫ x, ∏ i, exp (1 / 2 * lam i * x i ^ 2 + c i * x i) ∂ν := by
      rw [← hFT]; rfl
    rw [e1, integral_fintype_prod_eq_prod (fun i x => exp (1 / 2 * lam i * x ^ 2 + c i * x))]
    simp only [fun i => (h1d i).2]
    -- the determinant and the exponent
    have h1K : 1 - K = U * diagonal (fun i => 1 - lam i) * Uᵀ := by
      rw [hKU, show (diagonal fun i => 1 - lam i) = 1 - diagonal lam by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.diagonal, one_apply], Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_one, hUU']
    have hdet : (1 - K).det = ∏ i, (1 - lam i) := by
      have hd : Uᵀ.det * U.det = 1 := by rw [← det_mul, hUU, det_one]
      rw [h1K, det_mul, det_mul, det_diagonal]
      linear_combination (∏ i, (1 - lam i)) * hd
    have hinv : (1 - K)⁻¹ = U * diagonal (fun i => (1 - lam i)⁻¹) * Uᵀ := by
      apply Matrix.inv_eq_left_inv
      have : (diagonal fun i => (1 - lam i)⁻¹ * (1 - lam i)) = 1 := by
        rw [← diagonal_one]
        congr 1
        funext i
        exact inv_mul_cancel₀ (by linarith [hlam i])
      rw [h1K]
      calc U * diagonal (fun i => (1 - lam i)⁻¹) * Uᵀ * (U * diagonal (fun i => 1 - lam i) * Uᵀ)
          = U * (diagonal (fun i => (1 - lam i)⁻¹) * (Uᵀ * U) * diagonal (fun i => 1 - lam i)) *
              Uᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hUU, Matrix.mul_one, diagonal_mul_diagonal, this, Matrix.mul_one, hUU']
    have hexp : b ⬝ᵥ ((1 - K)⁻¹ *ᵥ b) = ∑ i, c i ^ 2 / (1 - lam i) := by
      rw [hinv, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by
        change c i * ((1 - lam i)⁻¹ * c i) = _
        ring
    rw [hdet, hexp, Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_inv_distrib,
      ← Real.sqrt_prod _ fun i _ => (by linarith [hlam i]), Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : 1 - lam i ≠ 0 := by linarith [hlam i]
    field_simp
  exact ⟨inferInstance, fun K b hKs hpos => (key K b hKs hpos).1,
    fun K b hKs hpos => (key K b hKs hpos).2⟩

/-- Miao, p. 322, for the standard normal shock: `R(V)(x, u)` for the quadratic value function. -/
theorem rc_R_quad_std {X : Type*} [Fintype X] {θ : ℝ} (hθ : 0 < θ) {C : Matrix X E ℝ}
    {P : Matrix X X ℝ} (hP : Pᵀ = P) (hH : (rcH θ C P).PosDef) (y : X → ℝ) (d : ℝ) :
    rcR (Measure.pi fun _ : E => gaussianReal 0 1) (fun e => rcV P d (y + C *ᵥ e)) θ =
      -(1 / 2) * (y ⬝ᵥ (rcD θ C P *ᵥ y)) - d / 2 - θ / 2 * log (rcK θ C P)⁻¹.det :=
  (rc_R_quad rc_gaussian_std hθ hP hH y d).2

/-- **(9.51)–(9.55)** for IID standard normal shocks (Miao, pp. 321–323). -/
theorem eq_9_51_9_55_std {X U : Type*} [Fintype X] [Fintype U] [DecidableEq U]
    (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ}
    (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    IsGreatest (Set.range (rcRobObj L (Measure.pi fun _ : E => gaussianReal 0 1) θ P
        (rcd L.β θ L.C P) x)) (rcV P (rcd L.β θ L.C P) x) ∧
      ∀ u, rcRobObj L (Measure.pi fun _ : E => gaussianReal 0 1) θ P (rcd L.β θ L.C P) x u =
          rcV P (rcd L.β θ L.C P) x ↔ u = -(L.F (rcD θ L.C P) *ᵥ x) :=
  eq_9_51_9_55 L rc_gaussian_std hR hβ hβ1 hθ hP hH hfix x

/-- The robust Bellman equation, with the minimisation over all likelihood ratios, for IID
standard normal shocks (Miao, pp. 320–323). -/
theorem rc_robust_bellman_std {X U : Type*} [Fintype X] [Fintype U] [DecidableEq U]
    (L : LSProblem X U E) (hR : L.R.PosDef) (hβ : 0 ≤ L.β) (hβ1 : L.β < 1) {θ : ℝ}
    (hθ : 0 < θ) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hH : (rcH θ L.C P).PosDef)
    (hfix : L.T (rcD θ L.C P) = P) (x : X → ℝ) :
    ∃ w : (U → ℝ) → ℝ,
      (∀ u, IsLeast
        (rcObj (Measure.pi fun _ : E => gaussianReal 0 1)
            (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ ''
          rcAdm (Measure.pi fun _ : E => gaussianReal 0 1)
            (fun e => rcV P (rcd L.β θ L.C P) (L.A *ᵥ x + L.B *ᵥ u + L.C *ᵥ e)) θ)
        (w u)) ∧
      IsGreatest (Set.range fun u => -(1 / 2) * L.loss x u + L.β * w u)
        (rcV P (rcd L.β θ L.C P) x) :=
  rc_robust_bellman L rc_gaussian_std hR hβ hβ1 hθ hP hH hfix x

/-- **Exercise 9.5** with an IID standard normal income shock: the robust Bellman equation holds
and the robust consumption rule is its unique maximiser. -/
theorem ex_9_5_bellman_std {b μ Rr ρ σ β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hR1 : 1 < Rr)
    (hρ : |ρ| < 1) (hκ : 1 < β * Rr ^ 2) {θ : ℝ} (hθ : 2 * rcHallK Rr ρ σ < θ)
    (x : Fin 3 → ℝ) :
    IsGreatest (Set.range (rcRobObj (rcHallRobust b μ Rr ρ σ β)
        (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) θ (rcHallPθ b μ Rr ρ σ β θ)
        (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x))
        (rcV (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x) ∧
      ∀ u, rcRobObj (rcHallRobust b μ Rr ρ σ β) (Measure.pi fun _ : Fin 1 => gaussianReal 0 1)
          θ (rcHallPθ b μ Rr ρ σ β θ)
          (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x u =
          rcV (rcHallPθ b μ Rr ρ σ β θ)
            (rcd β θ (rcHallRobust b μ Rr ρ σ β).C (rcHallPθ b μ Rr ρ σ β θ)) x ↔
        u = -(rcHallGain b μ Rr ρ (rcHallQθ Rr ρ σ β θ) *ᵥ x) :=
  ex_9_5_bellman rc_gaussian_std hβ hβ1 hR1 hρ hκ hθ x

end Miao.LinearQuadratic

set_option linter.style.longLine false
#print axioms Miao.LinearQuadratic.IsSolution
#print axioms Miao.LinearQuadratic.IsRegular
#print axioms Miao.LinearQuadratic.EventuallyConst
#print axioms Miao.LinearQuadratic.IsStableSeq
#print axioms Miao.LinearQuadratic.IsSteadyStateOf
#print axioms Miao.LinearQuadratic.IsAsympStable
#print axioms Miao.LinearQuadratic.basin
#print axioms Miao.LinearQuadratic.IsGloballyStable
#print axioms Miao.LinearQuadratic.IsStableMatrix
#print axioms Miao.LinearQuadratic.isGloballyStable_iff_basin
#print axioms Miao.LinearQuadratic.isAsympStable_iff_basin
#print axioms Miao.LinearQuadratic.isStableSeq_iff_bddAbove
#print axioms Miao.LinearQuadratic.tendsto_zero_of_le_rec
#print axioms Miao.LinearQuadratic.tendsto_zero_of_rec
#print axioms Miao.LinearQuadratic.triangular_step
#print axioms Miao.LinearQuadratic.triangular_invariant
#print axioms Miao.LinearQuadratic.triangular_tendsto_iff
#print axioms Miao.LinearQuadratic.mclm
#print axioms Miao.LinearQuadratic.mclm_apply
#print axioms Miao.LinearQuadratic.norm_mulVec_le
#print axioms Miao.LinearQuadratic.norm_mclm_mul_le
#print axioms Miao.LinearQuadratic.tendsto_norm_mclm_pow
#print axioms Miao.LinearQuadratic.summable_of_tendsto_zero
#print axioms Miao.LinearQuadratic.diag_mul_of_upper
#print axioms Miao.LinearQuadratic.upper_inv
#print axioms Miao.LinearQuadratic.diag_inv_of_upper
#print axioms Miao.LinearQuadratic.summable_norm_pow_of_triangular
#print axioms Miao.LinearQuadratic.stableSubspace
#print axioms Miao.LinearQuadratic.unstableSubspace
#print axioms Miao.LinearQuadratic.convSubspace
#print axioms Miao.LinearQuadratic.mem_convSubspace
#print axioms Miao.LinearQuadratic.tendsto_of_mem_maxGenEigenspace
#print axioms Miao.LinearQuadratic.not_tendsto_of_eigen
#print axioms Miao.LinearQuadratic.stable_le_conv
#print axioms Miao.LinearQuadratic.stable_sup_unstable
#print axioms Miao.LinearQuadratic.disjoint_stable_unstable
#print axioms Miao.LinearQuadratic.unstable_invariant
#print axioms Miao.LinearQuadratic.tendsto_iff_mem_stable
#print axioms Miao.LinearQuadratic.stable_eq_top
#print axioms Miao.LinearQuadratic.cplx
#print axioms Miao.LinearQuadratic.cplx_sub
#print axioms Miao.LinearQuadratic.cplx_add
#print axioms Miao.LinearQuadratic.tendsto_cplx_iff
#print axioms Miao.LinearQuadratic.cplxEnd
#print axioms Miao.LinearQuadratic.cplxEnd_pow_cplx
#print axioms Miao.LinearQuadratic.hasEigenvalue_cplxEnd_iff
#print axioms Miao.LinearQuadratic.finrank_biSup_maxGenEigenspace
#print axioms Miao.LinearQuadratic.finrank_stableSubspace
#print axioms Miao.LinearQuadratic.conjV
#print axioms Miao.LinearQuadratic.conjV_conjV
#print axioms Miao.LinearQuadratic.conjV_add
#print axioms Miao.LinearQuadratic.conjV_sub
#print axioms Miao.LinearQuadratic.conjV_smul
#print axioms Miao.LinearQuadratic.conjV_zero
#print axioms Miao.LinearQuadratic.conjV_cplx
#print axioms Miao.LinearQuadratic.eq_cplx_re
#print axioms Miao.LinearQuadratic.cplxEnd_conjV
#print axioms Miao.LinearQuadratic.pow_sub_conjV
#print axioms Miao.LinearQuadratic.conjV_mem_maxGenEigenspace
#print axioms Miao.LinearQuadratic.conjV_mem_biSup
#print axioms Miao.LinearQuadratic.conjV_mem_stable
#print axioms Miao.LinearQuadratic.conjV_mem_unstable
#print axioms Miao.LinearQuadratic.cplxL
#print axioms Miao.LinearQuadratic.stableR
#print axioms Miao.LinearQuadratic.unstableR
#print axioms Miao.LinearQuadratic.mem_stableR
#print axioms Miao.LinearQuadratic.mem_unstableR
#print axioms Miao.LinearQuadratic.mem_stableR_iff
#print axioms Miao.LinearQuadratic.cplx_mulVec
#print axioms Miao.LinearQuadratic.stableR_invariant
#print axioms Miao.LinearQuadratic.unstableR_invariant
#print axioms Miao.LinearQuadratic.isCompl_stableR_unstableR
#print axioms Miao.LinearQuadratic.linearIndependent_cplx
#print axioms Miao.LinearQuadratic.finrank_le_of_cplx
#print axioms Miao.LinearQuadratic.finrank_stableR
#print axioms Miao.LinearQuadratic.unstableR_ker
#print axioms Miao.LinearQuadratic.uniform_bound_of_basis
#print axioms Miao.LinearQuadratic.exists_bound_of_tendsto
#print axioms Miao.LinearQuadratic.mem_maxGen_smul
#print axioms Miao.LinearQuadratic.projS
#print axioms Miao.LinearQuadratic.projU
#print axioms Miao.LinearQuadratic.projS_add_projU
#print axioms Miao.LinearQuadratic.projS_mem
#print axioms Miao.LinearQuadratic.projU_mem
#print axioms Miao.LinearQuadratic.projS_of_mem
#print axioms Miao.LinearQuadratic.projS_of_mem_unstable
#print axioms Miao.LinearQuadratic.projU_of_mem
#print axioms Miao.LinearQuadratic.projU_of_mem_stable
#print axioms Miao.LinearQuadratic.projS_mulVec
#print axioms Miao.LinearQuadratic.projU_mulVec
#print axioms Miao.LinearQuadratic.pow_mulVec_mem_stableR
#print axioms Miao.LinearQuadratic.tendsto_scaled_of_stable
#print axioms Miao.LinearQuadratic.scaled_pow_cplx
#print axioms Miao.LinearQuadratic.stable_bound
#print axioms Miao.LinearQuadratic.isStableMatrix_iff_roots
#print axioms Miao.LinearQuadratic.tendsto_of_isStableMatrix
#print axioms Miao.LinearQuadratic.isStableMatrix_of_tendsto
#print axioms Miao.LinearQuadratic.isStableMatrix_iff_tendsto
#print axioms Miao.LinearQuadratic.HasGeomDecay
#print axioms Miao.LinearQuadratic.hasGeomDecay_of_isStableMatrix
#print axioms Miao.LinearQuadratic.isStableMatrix_inv
#print axioms Miao.LinearQuadratic.footnote_2
#print axioms Miao.LinearQuadratic.isRegular_of_isUnit_det
#print axioms Miao.LinearQuadratic.example_scalar_not_regular
#print axioms Miao.LinearQuadratic.example_scalar_no_solution
#print axioms Miao.LinearQuadratic.remark_nonregular_no_solution
#print axioms Miao.LinearQuadratic.remark_nonregular_counterexample
#print axioms Miao.LinearQuadratic.eq_1_21
#print axioms Miao.LinearQuadratic.eq_1_21_solution
#print axioms Miao.LinearQuadratic.eq_1_21_steadyState
#print axioms Miao.LinearQuadratic.isSteadyStateOf_of_not_mem_range
#print axioms Miao.LinearQuadratic.isStableSeq_iff_exists_le
#print axioms Miao.LinearQuadratic.exists_mulVec_bound
#print axioms Miao.LinearQuadratic.bounded_mulVec
#print axioms Miao.LinearQuadratic.norm_sum_type_le
#print axioms Miao.LinearQuadratic.norm_comp_inl_le
#print axioms Miao.LinearQuadratic.norm_comp_inr_le
#print axioms Miao.LinearQuadratic.backward_sol_eq
#print axioms Miao.LinearQuadratic.bounded_backward
#print axioms Miao.LinearQuadratic.summable_geom_series
#print axioms Miao.LinearQuadratic.mulVec_tsum_rs
#print axioms Miao.LinearQuadratic.tsum_geom_series_succ
#print axioms Miao.LinearQuadratic.eq_zero_of_bounded_orbit
#print axioms Miao.LinearQuadratic.IsGenEigenvector
#print axioms Miao.LinearQuadratic.IsGenEigenvalue
#print axioms Miao.LinearQuadratic.genEigenvalues
#print axioms Miao.LinearQuadratic.isGenEigenvalue_iff_det
#print axioms Miao.LinearQuadratic.det_ne_zero_of_unitary
#print axioms Miao.LinearQuadratic.conj_lincomb
#print axioms Miao.LinearQuadratic.det_conj_lincomb
#print axioms Miao.LinearQuadratic.upper_lincomb
#print axioms Miao.LinearQuadratic.det_upper_lincomb
#print axioms Miao.LinearQuadratic.diag_ne_zero_of_regular
#print axioms Miao.LinearQuadratic.genEigenvalues_eq_diag
#print axioms Miao.LinearQuadratic.exists_eigenPair
#print axioms Miao.LinearQuadratic.exists_unitary_col
#print axioms Miao.LinearQuadratic.deflate
#print axioms Miao.LinearQuadratic.det_of_col_zero
#print axioms Miao.LinearQuadratic.blockOne
#print axioms Miao.LinearQuadratic.blockOne_mul_zero
#print axioms Miao.LinearQuadratic.blockOne_mul_succ
#print axioms Miao.LinearQuadratic.mul_blockOne_zero
#print axioms Miao.LinearQuadratic.mul_blockOne_succ
#print axioms Miao.LinearQuadratic.blockOne_mul_blockOne
#print axioms Miao.LinearQuadratic.star_blockOne
#print axioms Miao.LinearQuadratic.blockOne_one
#print axioms Miao.LinearQuadratic.blockOne_mem
#print axioms Miao.LinearQuadratic.assemble_apply
#print axioms Miao.LinearQuadratic.assemble_upper
#print axioms Miao.LinearQuadratic.proportional_of_cross
#print axioms Miao.LinearQuadratic.ScaleInvariant
#print axioms Miao.LinearQuadratic.exists_qz_ordered
#print axioms Miao.LinearQuadratic.theorem_1_4_4
#print axioms Miao.LinearQuadratic.scaleInvariant_stable
#print axioms Miao.LinearQuadratic.theorem_1_4_4_stable
#print axioms Miao.LinearQuadratic.norm_mulVec_le_sum
#print axioms Miao.LinearQuadratic.isStableSeq_of_le
#print axioms Miao.LinearQuadratic.IsStableSeq.bound
#print axioms Miao.LinearQuadratic.IsStableSeq.mulVec
#print axioms Miao.LinearQuadratic.fwdSum
#print axioms Miao.LinearQuadratic.summable_fwd
#print axioms Miao.LinearQuadratic.norm_fwdSum_le
#print axioms Miao.LinearQuadratic.fwdSum_rec
#print axioms Miao.LinearQuadratic.eq_fwdSum
#print axioms Miao.LinearQuadratic.isStableSeq_of_rec
#print axioms Miao.LinearQuadratic.IsStableSeq.add
#print axioms Miao.LinearQuadratic.IsStableSeq.sub
#print axioms Miao.LinearQuadratic.IsStableSeq.shift
#print axioms Miao.LinearQuadratic.norm_comp_le
#print axioms Miao.LinearQuadratic.IsStableSeq.comp
#print axioms Miao.LinearQuadratic.isStableSeq_append
#print axioms Miao.LinearQuadratic.upper_castAdd
#print axioms Miao.LinearQuadratic.upper_natAdd
#print axioms Miao.LinearQuadratic.mulVec_castAdd
#print axioms Miao.LinearQuadratic.mulVec_natAdd
#print axioms Miao.LinearQuadratic.eq_1_36
#print axioms Miao.LinearQuadratic.solve_fwd
#print axioms Miao.LinearQuadratic.eq_1_38
#print axioms Miao.LinearQuadratic.det_S11_ne_zero
#print axioms Miao.LinearQuadratic.det_T22_ne_zero
#print axioms Miao.LinearQuadratic.summable_Ms
#print axioms Miao.LinearQuadratic.summable_Mu
#print axioms Miao.LinearQuadratic.klein_core
#print axioms Miao.LinearQuadratic.klein_homog
#print axioms Miao.LinearQuadratic.eq_1_37
#print axioms Miao.LinearQuadratic.eq_1_39_40
#print axioms Miao.LinearQuadratic.isSolution_iff_transformed
#print axioms Miao.LinearQuadratic.diag_off_circle
#print axioms Miao.LinearQuadratic.theorem_1_4_5
#print axioms Miao.LinearQuadratic.det_sub_ne_zero
#print axioms Miao.LinearQuadratic.corollary_1_4_1_singular
#print axioms Miao.LinearQuadratic.map_ofReal_mulVec
#print axioms Miao.LinearQuadratic.norm_ofReal_vec
#print axioms Miao.LinearQuadratic.isSolution_ofReal_iff
#print axioms Miao.LinearQuadratic.theorem_1_4_5_real
#print axioms Miao.LinearQuadratic.eq_s0
#print axioms Miao.LinearQuadratic.remark_augmented
#print axioms Miao.LinearQuadratic.remark_u_eq_zero
#print axioms Miao.LinearQuadratic.eq_1_37_printed_false
#print axioms Miao.LinearQuadratic.caganA
#print axioms Miao.LinearQuadratic.caganB
#print axioms Miao.LinearQuadratic.caganC
#print axioms Miao.LinearQuadratic.example_cagan_iff
#print axioms Miao.LinearQuadratic.example_cagan_det
#print axioms Miao.LinearQuadratic.example_cagan_regular
#print axioms Miao.LinearQuadratic.example_cagan_genEigenvalues
#print axioms Miao.LinearQuadratic.example_cagan_genEigenvalues_zero
#print axioms Miao.LinearQuadratic.CondExpSystem
#print axioms Miao.LinearQuadratic.CondExpSystem.mk
#print axioms Miao.LinearQuadratic.CondExpSystem.E
#print axioms Miao.LinearQuadratic.CondExpSystem.norm_le
#print axioms Miao.LinearQuadratic.CondExpSystem.tower_le
#print axioms Miao.LinearQuadratic.CondExpSystem.tower_ge
#print axioms Miao.LinearQuadratic.CondExpSystem.tower_le_apply
#print axioms Miao.LinearQuadratic.CondExpSystem.tower_ge_apply
#print axioms Miao.LinearQuadratic.CondExpSystem.idem
#print axioms Miao.LinearQuadratic.CondExpSystem.norm_apply_le
#print axioms Miao.LinearQuadratic.IsAdaptedV
#print axioms Miao.LinearQuadratic.IsStableProc
#print axioms Miao.LinearQuadratic.matAct
#print axioms Miao.LinearQuadratic.Evec
#print axioms Miao.LinearQuadratic.IsRESolution
#print axioms Miao.LinearQuadratic.IsPredeterminedBK
#print axioms Miao.LinearQuadratic.Evec_matAct
#print axioms Miao.LinearQuadratic.matAct_add
#print axioms Miao.LinearQuadratic.matAct_mul
#print axioms Miao.LinearQuadratic.matAct_one
#print axioms Miao.LinearQuadratic.condExpL1_norm_apply_le
#print axioms Miao.LinearQuadratic.condExpL1_ae_eq_condExp
#print axioms Miao.LinearQuadratic.condExpL1_tower_le
#print axioms Miao.LinearQuadratic.condExpL1_tower_ge
#print axioms Miao.LinearQuadratic.condExpL1CLMK
#print axioms Miao.LinearQuadratic.condExpL1CLMK_apply
#print axioms Miao.LinearQuadratic.condExpSystemL1
#print axioms Miao.LinearQuadratic.condExpSystemL1_E_apply
#print axioms Miao.LinearQuadratic.condExpSystemL1_real
#print axioms Miao.LinearQuadratic.condExpSystemL1_complex
#print axioms Miao.LinearQuadratic.condExpSystemL1_ae_eq
#print axioms Miao.LinearQuadratic.condExpL1_eq_self_iff
#print axioms Miao.LinearQuadratic.condExpL1_eq_self_iff_exists
#print axioms Miao.LinearQuadratic.condExpL1_isAdaptedV_iff
#print axioms Miao.LinearQuadratic.l1_norm_eq_integral_abs
#print axioms Miao.LinearQuadratic.l1_isStableProc_iff
#print axioms Miao.LinearQuadratic.l1_norm_eq_integral_norm_complex
#print axioms Miao.LinearQuadratic.example_2_1_1
#print axioms Miao.LinearQuadratic.example_2_1_2
#print axioms Miao.LinearQuadratic.example_2_1_3
#print axioms Miao.LinearQuadratic.var_pow_entry_le
#print axioms Miao.LinearQuadratic.var_l1
#print axioms Miao.LinearQuadratic.var_l1_nonneg
#print axioms Miao.LinearQuadratic.var_sandwich_apply
#print axioms Miao.LinearQuadratic.var_sandwich_le
#print axioms Miao.LinearQuadratic.var_lyapMap
#print axioms Miao.LinearQuadratic.var_lyapSol
#print axioms Miao.LinearQuadratic.var_lyap_summable
#print axioms Miao.LinearQuadratic.var_lyap_iterate
#print axioms Miao.LinearQuadratic.lyap_iterate_tendsto
#print axioms Miao.LinearQuadratic.var_lyapMap_apply
#print axioms Miao.LinearQuadratic.var_lyapMap_continuous
#print axioms Miao.LinearQuadratic.lyap_fixed
#print axioms Miao.LinearQuadratic.lyap_unique
#print axioms Miao.LinearQuadratic.var_ShockMDS
#print axioms Miao.LinearQuadratic.var_ShockMDS.mk
#print axioms Miao.LinearQuadratic.var_ShockMDS.memLp
#print axioms Miao.LinearQuadratic.var_ShockMDS.meas
#print axioms Miao.LinearQuadratic.var_ShockMDS.mds
#print axioms Miao.LinearQuadratic.var_ShockMDS.cvar
#print axioms Miao.LinearQuadratic.var_Model
#print axioms Miao.LinearQuadratic.var_Model.mk
#print axioms Miao.LinearQuadratic.var_Model.eq21
#print axioms Miao.LinearQuadratic.var_Model.z0_memLp
#print axioms Miao.LinearQuadratic.var_Model.z0_meas
#print axioms Miao.LinearQuadratic.var_Model.shock
#print axioms Miao.LinearQuadratic.var_mean
#print axioms Miao.LinearQuadratic.var_mom
#print axioms Miao.LinearQuadratic.var_rec_apply
#print axioms Miao.LinearQuadratic.var_Model.z_memLp
#print axioms Miao.LinearQuadratic.var_Model.z_meas
#print axioms Miao.LinearQuadratic.var_cross_zero
#print axioms Miao.LinearQuadratic.var_mean_eps_zero
#print axioms Miao.LinearQuadratic.var_mom_eps
#print axioms Miao.LinearQuadratic.var_integral_sum_mul
#print axioms Miao.LinearQuadratic.var_integral_mul_sum
#print axioms Miao.LinearQuadratic.var_mean_rec
#print axioms Miao.LinearQuadratic.var_mean_eq
#print axioms Miao.LinearQuadratic.var_mean_tendsto_zero
#print axioms Miao.LinearQuadratic.var_stack
#print axioms Miao.LinearQuadratic.var_rec_stack
#print axioms Miao.LinearQuadratic.var_rec_stack_apply
#print axioms Miao.LinearQuadratic.var_stack_memLp
#print axioms Miao.LinearQuadratic.var_mom_rec
#print axioms Miao.LinearQuadratic.var_mom_iterate
#print axioms Miao.LinearQuadratic.var_mom_tendsto
#print axioms Miao.LinearQuadratic.var_autocov
#print axioms Miao.LinearQuadratic.var_IsCovStationary
#print axioms Miao.LinearQuadratic.definition_2_1_1_not_symmetric
#print axioms Miao.LinearQuadratic.var_stationary_moments
#print axioms Miao.LinearQuadratic.var_stationary_of_initial
#print axioms Miao.LinearQuadratic.var_ma_shift
#print axioms Miao.LinearQuadratic.var_ma
#print axioms Miao.LinearQuadratic.var_ma_initial_tendsto
#print axioms Miao.LinearQuadratic.var_impulse_response
#print axioms Miao.LinearQuadratic.var_IsWhiteNoise
#print axioms Miao.LinearQuadratic.var_integral_abs_le_sqrt
#print axioms Miao.LinearQuadratic.whiteNoise_stable
#print axioms Miao.LinearQuadratic.whiteNoise_stable_L1
#print axioms Miao.LinearQuadratic.mds_whiteNoise
#print axioms Miao.LinearQuadratic.IsMartingaleProc
#print axioms Miao.LinearQuadratic.IsMartingaleDiffProc
#print axioms Miao.LinearQuadratic.IsPredeterminedKlein
#print axioms Miao.LinearQuadratic.predError_isMartingaleDiff
#print axioms Miao.LinearQuadratic.isPredeterminedKlein_zero_iff
#print axioms Miao.LinearQuadratic.IsMartingaleProc.diff
#print axioms Miao.LinearQuadratic.isStableProc_of_uniformly_bounded
#print axioms Miao.LinearQuadratic.klM_trunc
#print axioms Miao.LinearQuadratic.klM_trunc_apply
#print axioms Miao.LinearQuadratic.klM_truncSystem
#print axioms Miao.LinearQuadratic.example_mdiff_not_stable
#print axioms Miao.LinearQuadratic.klS_matAct_sub
#print axioms Miao.LinearQuadratic.klS_matAct_neg
#print axioms Miao.LinearQuadratic.klS_matAct_zero
#print axioms Miao.LinearQuadratic.klS_zero_matAct
#print axioms Miao.LinearQuadratic.klS_add_matAct
#print axioms Miao.LinearQuadratic.klS_sub_matAct
#print axioms Miao.LinearQuadratic.klS_neg_matAct
#print axioms Miao.LinearQuadratic.klS_matAct_comp
#print axioms Miao.LinearQuadratic.klS_matCLM
#print axioms Miao.LinearQuadratic.klS_matCLM_apply
#print axioms Miao.LinearQuadratic.klS_matAct_sum
#print axioms Miao.LinearQuadratic.klS_matAct_inv_mul
#print axioms Miao.LinearQuadratic.klS_matAct_mul_inv
#print axioms Miao.LinearQuadratic.klS_matAct_blocks
#print axioms Miao.LinearQuadratic.klS_matAct_natAdd
#print axioms Miao.LinearQuadratic.klS_ext_blocks
#print axioms Miao.LinearQuadratic.klS_append_castAdd
#print axioms Miao.LinearQuadratic.klS_append_natAdd
#print axioms Miao.LinearQuadratic.klS_Evec_add
#print axioms Miao.LinearQuadratic.klS_Evec_sub
#print axioms Miao.LinearQuadratic.klS_Evec_neg
#print axioms Miao.LinearQuadratic.klS_Evec_zero
#print axioms Miao.LinearQuadratic.klS_Evec_idem
#print axioms Miao.LinearQuadratic.klS_Evec_tower_le
#print axioms Miao.LinearQuadratic.klS_Evec_tower_ge
#print axioms Miao.LinearQuadratic.klS_Evec_comp
#print axioms Miao.LinearQuadratic.klS_Evec_append
#print axioms Miao.LinearQuadratic.klS_adapted_succ
#print axioms Miao.LinearQuadratic.klS_EvecCLM
#print axioms Miao.LinearQuadratic.klS_EvecCLM_apply
#print axioms Miao.LinearQuadratic.klS_ent
#print axioms Miao.LinearQuadratic.klS_ent_nonneg
#print axioms Miao.LinearQuadratic.klS_norm_matAct_le
#print axioms Miao.LinearQuadratic.klS_norm_Evec_le
#print axioms Miao.LinearQuadratic.klS_stable_bound
#print axioms Miao.LinearQuadratic.klS_stable_of_le
#print axioms Miao.LinearQuadratic.klS_stable_add
#print axioms Miao.LinearQuadratic.klS_stable_sub
#print axioms Miao.LinearQuadratic.klS_stable_matAct
#print axioms Miao.LinearQuadratic.klS_stable_Evec
#print axioms Miao.LinearQuadratic.klS_stable_shift
#print axioms Miao.LinearQuadratic.klS_stable_comp
#print axioms Miao.LinearQuadratic.klS_stable_append
#print axioms Miao.LinearQuadratic.klS_entry_le_mclm
#print axioms Miao.LinearQuadratic.klS_ent_le_mclm
#print axioms Miao.LinearQuadratic.klS_summable_ent
#print axioms Miao.LinearQuadratic.klS_fwd
#print axioms Miao.LinearQuadratic.klS_fwd_summable
#print axioms Miao.LinearQuadratic.klS_norm_fwd_le
#print axioms Miao.LinearQuadratic.klS_fwd_adapted
#print axioms Miao.LinearQuadratic.klS_fwd_rec
#print axioms Miao.LinearQuadratic.klS_eq_fwd
#print axioms Miao.LinearQuadratic.klS_stable_of_rec
#print axioms Miao.LinearQuadratic.klS_norm_comp_le
#print axioms Miao.LinearQuadratic.klS_blocks_iff
#print axioms Miao.LinearQuadratic.klS_solve_fwd
#print axioms Miao.LinearQuadratic.eq_klein_Es
#print axioms Miao.LinearQuadratic.eq_klein_xi
#print axioms Miao.LinearQuadratic.eq_klein_k
#print axioms Miao.LinearQuadratic.eq_klein_s
#print axioms Miao.LinearQuadratic.klS_core_blocks
#print axioms Miao.LinearQuadratic.klS_core
#print axioms Miao.LinearQuadratic.klS_isRESolution_iff
#print axioms Miao.LinearQuadratic.klein_stochastic
#print axioms Miao.LinearQuadratic.klS_cj_matAct
#print axioms Miao.LinearQuadratic.klein_stochastic_real
#print axioms Miao.LinearQuadratic.eq_2_17
#print axioms Miao.LinearQuadratic.eq_2_17_solution
#print axioms Miao.LinearQuadratic.klS_detSystem
#print axioms Miao.LinearQuadratic.klS_Evec_det
#print axioms Miao.LinearQuadratic.klS_matAct_eq_mulVec
#print axioms Miao.LinearQuadratic.eq_2_17_printed_false
#print axioms Miao.LinearQuadratic.klS_Ez_of_2_1
#print axioms Miao.LinearQuadratic.klS_entry_le_ent
#print axioms Miao.LinearQuadratic.klS_entry_mul_le
#print axioms Miao.LinearQuadratic.klS_sylvester_unique
#print axioms Miao.LinearQuadratic.klS_sylvester_exists
#print axioms Miao.LinearQuadratic.klS_simpl_y
#print axioms Miao.LinearQuadratic.klS_simpl_k
#print axioms Miao.LinearQuadratic.klein_simplified_form
#print axioms Miao.LinearQuadratic.SS.IsMarkov
#print axioms Miao.LinearQuadratic.SS.IsMarkov.mk
#print axioms Miao.LinearQuadratic.SS.IsMarkov.nonneg
#print axioms Miao.LinearQuadratic.SS.IsMarkov.rowsum
#print axioms Miao.LinearQuadratic.SS.IsDistribution
#print axioms Miao.LinearQuadratic.SS.IsDistribution.mk
#print axioms Miao.LinearQuadratic.SS.IsDistribution.nonneg
#print axioms Miao.LinearQuadratic.SS.IsDistribution.sum_eq_one
#print axioms Miao.LinearQuadratic.SS.mulVec_apply_eq
#print axioms Miao.LinearQuadratic.SS.IsMarkov.mul
#print axioms Miao.LinearQuadratic.SS.IsMarkov.pow
#print axioms Miao.LinearQuadratic.SS.IsMarkov.mulVec_le_mulVec
#print axioms Miao.LinearQuadratic.SS.IsMarkov.mulVec_const
#print axioms Miao.LinearQuadratic.SS.IsMarkov.abs_mulVec_le
#print axioms Miao.LinearQuadratic.SS.IsMarkov.norm_mulVec_le
#print axioms Miao.LinearQuadratic.SS.IsMarkov.abs_mulVec_sub_le
#print axioms Miao.LinearQuadratic.SS.GloballyStable
#print axioms Miao.LinearQuadratic.SS.IsContractionOn
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.mk
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.mapsTo
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.nonneg
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.lt_one
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.norm_sub_le
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.fixedPt_unique
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.iterate_mem
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.tendsto_iterate_fixedPt
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.exists_fixedPt
#print axioms Miao.LinearQuadratic.SS.IsContractionOn.globallyStable_univ
#print axioms Miao.LinearQuadratic.SS.fixedPt_le_of_le
#print axioms Miao.LinearQuadratic.SS.le_fixedPt_of_le_apply
#print axioms Miao.LinearQuadratic.SS.isContractionOn_of_blackwell
#print axioms Miao.LinearQuadratic.SS.abs_sup'_sub_sup'_le
#print axioms Miao.LinearQuadratic.SS.pow_nonneg_entries
#print axioms Miao.LinearQuadratic.SS.pow_le_pow_entries
#print axioms Miao.LinearQuadratic.SS.complexify
#print axioms Miao.LinearQuadratic.SS.complexify_apply
#print axioms Miao.LinearQuadratic.SS.complexify_pow
#print axioms Miao.LinearQuadratic.SS.complexify_transpose
#print axioms Miao.LinearQuadratic.SS.nnnorm_complexify
#print axioms Miao.LinearQuadratic.SS.norm_complexify
#print axioms Miao.LinearQuadratic.SS.specRad
#print axioms Miao.LinearQuadratic.SS.spectralRadius_complexify_ne_top
#print axioms Miao.LinearQuadratic.SS.specRad_nonneg
#print axioms Miao.LinearQuadratic.SS.mem_spectrum_iff_eigenpair
#print axioms Miao.LinearQuadratic.SS.tendsto_norm_pow_rpow
#print axioms Miao.LinearQuadratic.SS.eventually_norm_pow_le
#print axioms Miao.LinearQuadratic.SS.tendsto_norm_pow_zero
#print axioms Miao.LinearQuadratic.SS.summable_pow
#print axioms Miao.LinearQuadratic.SS.one_sub_mul_tsum
#print axioms Miao.LinearQuadratic.SS.tsum_mul_one_sub
#print axioms Miao.LinearQuadratic.SS.neumann_series
#print axioms Miao.LinearQuadratic.SS.specRad_transpose
#print axioms Miao.LinearQuadratic.SS.norm_le_norm_of_abs_le
#print axioms Miao.LinearQuadratic.SS.specRad_le_of_le
#print axioms Miao.LinearQuadratic.SS.rowsum_abs_le_norm
#print axioms Miao.LinearQuadratic.SS.norm_le_of_rowsum_abs_le
#print axioms Miao.LinearQuadratic.SS.abs_entry_le_norm
#print axioms Miao.LinearQuadratic.SS.norm_eq_of_rowsum_eq
#print axioms Miao.LinearQuadratic.SS.specRad_le_norm
#print axioms Miao.LinearQuadratic.SS.norm_le_specRad_of_mem_spectrum
#print axioms Miao.LinearQuadratic.SS.specRad_eq_of_rowsum_eq
#print axioms Miao.LinearQuadratic.SS.specRad_eq_of_colsum_eq
#print axioms Miao.LinearQuadratic.SS.eventually_abs_entry_pow_le
#print axioms Miao.LinearQuadratic.SS.OrderStable
#print axioms Miao.LinearQuadratic.SS.IncreasesTo
#print axioms Miao.LinearQuadratic.SS.DecreasesTo
#print axioms Miao.LinearQuadratic.SS.StronglyOrderStable
#print axioms Miao.LinearQuadratic.SS.orderStable_of_up_down
#print axioms Miao.LinearQuadratic.SS.StronglyOrderStable.orderStable
#print axioms Miao.LinearQuadratic.SS.dualMap
#print axioms Miao.LinearQuadratic.SS.orderStable_dual_iff
#print axioms Miao.LinearQuadratic.SS.dualMap_iterate
#print axioms Miao.LinearQuadratic.SS.stronglyOrderStable_dual_iff
#print axioms Miao.LinearQuadratic.SS.ChainComplete
#print axioms Miao.LinearQuadratic.SS.ChainComplete.exists_least
#print axioms Miao.LinearQuadratic.SS.ChainComplete.exists_fixedPt_ge
#print axioms Miao.LinearQuadratic.SS.ChainComplete.exists_fixedPt_le
#print axioms Miao.LinearQuadratic.SS.ChainComplete.exists_fixedPt
#print axioms Miao.LinearQuadratic.SS.ChainComplete.orderStable
#print axioms Miao.LinearQuadratic.SS.chainComplete_Icc
#print axioms Miao.LinearQuadratic.SS.CountablyDedekindComplete
#print axioms Miao.LinearQuadratic.SS.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms Miao.LinearQuadratic.SS.CountablyDedekindComplete.dual
#print axioms Miao.LinearQuadratic.SS.OrderContinuous
#print axioms Miao.LinearQuadratic.SS.OrderContinuous.monotone
#print axioms Miao.LinearQuadratic.SS.isLUB_range_succ_iff
#print axioms Miao.LinearQuadratic.SS.tarski_kantorovich
#print axioms Miao.LinearQuadratic.SS.stronglyOrderStable_of_globallyStable
#print axioms Miao.LinearQuadratic.SS.ADP
#print axioms Miao.LinearQuadratic.SS.ADP.mk
#print axioms Miao.LinearQuadratic.SS.ADP.T
#print axioms Miao.LinearQuadratic.SS.ADP.mono
#print axioms Miao.LinearQuadratic.SS.ADP.nonempty
#print axioms Miao.LinearQuadratic.SS.ADP.IsGreedy
#print axioms Miao.LinearQuadratic.SS.ADP.VG
#print axioms Miao.LinearQuadratic.SS.ADP.WellPosed
#print axioms Miao.LinearQuadratic.SS.ADP.IsFinite
#print axioms Miao.LinearQuadratic.SS.ADP.Regular
#print axioms Miao.LinearQuadratic.SS.ADP.IsOrderStable
#print axioms Miao.LinearQuadratic.SS.ADP.IsStronglyOrderStable
#print axioms Miao.LinearQuadratic.SS.ADP.IsBellmanValue
#print axioms Miao.LinearQuadratic.SS.ADP.SolvesBellman
#print axioms Miao.LinearQuadratic.SS.ADP.IsStronglyOrderStable.isOrderStable
#print axioms Miao.LinearQuadratic.SS.ADP.IsOrderStable.wellPosed
#print axioms Miao.LinearQuadratic.SS.ADP.regular_iff
#print axioms Miao.LinearQuadratic.SS.ADP.greedy
#print axioms Miao.LinearQuadratic.SS.ADP.isGreedy_greedy
#print axioms Miao.LinearQuadratic.SS.ADP.bellman
#print axioms Miao.LinearQuadratic.SS.ADP.T_le_bellman
#print axioms Miao.LinearQuadratic.SS.ADP.isBellmanValue_bellman
#print axioms Miao.LinearQuadratic.SS.ADP.isGreedy_iff
#print axioms Miao.LinearQuadratic.SS.ADP.isGreedy_of_isBellmanValue
#print axioms Miao.LinearQuadratic.SS.ADP.solvesBellman_iff
#print axioms Miao.LinearQuadratic.SS.ADP.bellman_mono
#print axioms Miao.LinearQuadratic.SS.ADP.VU
#print axioms Miao.LinearQuadratic.SS.ADP.VSig
#print axioms Miao.LinearQuadratic.SS.ADP.VSig_inter_VG_subset
#print axioms Miao.LinearQuadratic.SS.ADP.vσ
#print axioms Miao.LinearQuadratic.SS.ADP.T_vσ
#print axioms Miao.LinearQuadratic.SS.ADP.eq_vσ
#print axioms Miao.LinearQuadratic.SS.ADP.VSig_eq_range
#print axioms Miao.LinearQuadratic.SS.ADP.IsOptimal
#print axioms Miao.LinearQuadratic.SS.ADP.IsValueFunction
#print axioms Miao.LinearQuadratic.SS.ADP.BellmanPrinciple
#print axioms Miao.LinearQuadratic.SS.ADP.FundamentalOptimality
#print axioms Miao.LinearQuadratic.SS.ADP.IsOptimal.isValueFunction
#print axioms Miao.LinearQuadratic.SS.ADP.isOptimal_of_isValueFunction
#print axioms Miao.LinearQuadratic.SS.ADP.isOptimal_iff
#print axioms Miao.LinearQuadratic.SS.ADP.bellmanPrinciple_of_solves
#print axioms Miao.LinearQuadratic.SS.ADP.exists_solves_iff
#print axioms Miao.LinearQuadratic.SS.ADP.fundamentalOptimality_iff
#print axioms Miao.LinearQuadratic.SS.ADP.isOptimal_iff_solvesBellman
#print axioms Miao.LinearQuadratic.SS.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms Miao.LinearQuadratic.SS.ADP.IsOrderStable.fundamentalOptimality
#print axioms Miao.LinearQuadratic.SS.ADP.WellPosed.isOrderStable
#print axioms Miao.LinearQuadratic.SS.ADP.fundamentalOptimality_of_chainComplete
#print axioms Miao.LinearQuadratic.SS.ADP.IsSelector
#print axioms Miao.LinearQuadratic.SS.ADP.Regular.isSelector_greedy
#print axioms Miao.LinearQuadratic.SS.ADP.howard
#print axioms Miao.LinearQuadratic.SS.ADP.opt
#print axioms Miao.LinearQuadratic.SS.ADP.IsSelector.T_eq
#print axioms Miao.LinearQuadratic.SS.ADP.mem_VU_iff
#print axioms Miao.LinearQuadratic.SS.ADP.bellman_eq_of_howard_eq
#print axioms Miao.LinearQuadratic.SS.ADP.iterate_mono_of_le
#print axioms Miao.LinearQuadratic.SS.ADP.bellman_le_opt
#print axioms Miao.LinearQuadratic.SS.ADP.chain_2_9
#print axioms Miao.LinearQuadratic.SS.ADP.mapsTo_VU
#print axioms Miao.LinearQuadratic.SS.ADP.bellman_le_of_le
#print axioms Miao.LinearQuadratic.SS.ADP.iterates_of_mem_VU
#print axioms Miao.LinearQuadratic.SS.ADP.VFIConverges
#print axioms Miao.LinearQuadratic.SS.ADP.OPIConverges
#print axioms Miao.LinearQuadratic.SS.ADP.HPIConverges
#print axioms Miao.LinearQuadratic.SS.ADP.opt_one
#print axioms Miao.LinearQuadratic.SS.ADP.OPIConverges.vfi
#print axioms Miao.LinearQuadratic.SS.ADP.le_vstar_of_mem_VU
#print axioms Miao.LinearQuadratic.SS.ADP.IsOrderStable.le_vσ
#print axioms Miao.LinearQuadratic.SS.ADP.IsOrderStable.vσ_le
#print axioms Miao.LinearQuadratic.SS.ADP.iterates_le_vstar
#print axioms Miao.LinearQuadratic.SS.ADP.increasesTo_of_squeeze
#print axioms Miao.LinearQuadratic.SS.ADP.VFIConverges.opi_hpi
#print axioms Miao.LinearQuadratic.SS.ADP.VU_nonempty
#print axioms Miao.LinearQuadratic.SS.ADP.IsFinite.VSig_finite
#print axioms Miao.LinearQuadratic.SS.ADP.exists_succ_eq_of_finite
#print axioms Miao.LinearQuadratic.SS.ADP.fundamentalOptimality_of_finite
#print axioms Miao.LinearQuadratic.SS.ADP.FundamentalOptimality.exists_vstar
#print axioms Miao.LinearQuadratic.SS.ADP.convergence_of_chainComplete
#print axioms Miao.LinearQuadratic.SS.ADP.OrderBounded
#print axioms Miao.LinearQuadratic.SS.ADP.IsOrderContinuous
#print axioms Miao.LinearQuadratic.SS.ADP.le_of_orderBounded
#print axioms Miao.LinearQuadratic.SS.ADP.convergence_of_dedekind
#print axioms Miao.LinearQuadratic.SS.ADP.dual
#print axioms Miao.LinearQuadratic.SS.ADP.dual_dual
#print axioms Miao.LinearQuadratic.SS.ADP.IsMinGreedy
#print axioms Miao.LinearQuadratic.SS.ADP.VGmin
#print axioms Miao.LinearQuadratic.SS.ADP.MinRegular
#print axioms Miao.LinearQuadratic.SS.ADP.MinOrderBounded
#print axioms Miao.LinearQuadratic.SS.ADP.IsMinBellmanValue
#print axioms Miao.LinearQuadratic.SS.ADP.SolvesMinBellman
#print axioms Miao.LinearQuadratic.SS.ADP.IsMinValueFunction
#print axioms Miao.LinearQuadratic.SS.ADP.IsMinOptimal
#print axioms Miao.LinearQuadratic.SS.ADP.MinBellmanPrinciple
#print axioms Miao.LinearQuadratic.SS.ADP.MinFundamentalOptimality
#print axioms Miao.LinearQuadratic.SS.ADP.isMinGreedy_iff
#print axioms Miao.LinearQuadratic.SS.ADP.minRegular_iff
#print axioms Miao.LinearQuadratic.SS.ADP.minOrderBounded_iff
#print axioms Miao.LinearQuadratic.SS.ADP.isMinBellmanValue_iff
#print axioms Miao.LinearQuadratic.SS.ADP.VGmin_eq
#print axioms Miao.LinearQuadratic.SS.ADP.dual_VSig
#print axioms Miao.LinearQuadratic.SS.ADP.WellPosed.dual
#print axioms Miao.LinearQuadratic.SS.ADP.dual_vσ
#print axioms Miao.LinearQuadratic.SS.ADP.isMinValueFunction_iff
#print axioms Miao.LinearQuadratic.SS.ADP.isMinOptimal_iff
#print axioms Miao.LinearQuadratic.SS.ADP.dual_opt_howard
#print axioms Miao.LinearQuadratic.SS.ADP.minBellmanPrinciple_iff
#print axioms Miao.LinearQuadratic.SS.ADP.minFundamentalOptimality_iff
#print axioms Miao.LinearQuadratic.SS.ADP.VD
#print axioms Miao.LinearQuadratic.SS.ADP.MinVFIConverges
#print axioms Miao.LinearQuadratic.SS.ADP.minVFIConverges_iff
#print axioms Miao.LinearQuadratic.SS.ADP.minFundamentalOptimality_iff_exists_fixed
#print axioms Miao.LinearQuadratic.SS.ADP.IsOrderStable.minFundamentalOptimality
#print axioms Miao.LinearQuadratic.SS.LQProblem
#print axioms Miao.LinearQuadratic.SS.LQProblem.mk
#print axioms Miao.LinearQuadratic.SS.LQProblem.A
#print axioms Miao.LinearQuadratic.SS.LQProblem.B
#print axioms Miao.LinearQuadratic.SS.LQProblem.Q
#print axioms Miao.LinearQuadratic.SS.LQProblem.R
#print axioms Miao.LinearQuadratic.SS.LQProblem.Q_psd
#print axioms Miao.LinearQuadratic.SS.LQProblem.R_pd
#print axioms Miao.LinearQuadratic.SS.LQProblem.gainDen
#print axioms Miao.LinearQuadratic.SS.LQProblem.TF
#print axioms Miao.LinearQuadratic.SS.LQProblem.cost
#print axioms Miao.LinearQuadratic.SS.LQProblem.posSemidef_iff_real
#print axioms Miao.LinearQuadratic.SS.LQProblem.posDef_iff_real
#print axioms Miao.LinearQuadratic.SS.LQProblem.posSemidef_transpose_mul_mul
#print axioms Miao.LinearQuadratic.SS.LQProblem.gainDen_posDef
#print axioms Miao.LinearQuadratic.SS.LQProblem.dotProduct_mulVec_comm_of_symm
#print axioms Miao.LinearQuadratic.SS.LQProblem.mulVec_dotProduct
#print axioms Miao.LinearQuadratic.SS.LQProblem.dotProduct_transpose_mul_mul
#print axioms Miao.LinearQuadratic.SS.LQProblem.quad_add
#print axioms Miao.LinearQuadratic.SS.LQProblem.dotProduct_TF
#print axioms Miao.LinearQuadratic.SS.LQProblem.TF_posSemidef
#print axioms Miao.LinearQuadratic.SS.LQProblem.TF_transpose
#print axioms Miao.LinearQuadratic.SS.LQProblem.TF_mono
#print axioms Miao.LinearQuadratic.SS.LQProblem.TF_expand
#print axioms Miao.LinearQuadratic.SS.LQProblem.riccati
#print axioms Miao.LinearQuadratic.SS.LQProblem.gain
#print axioms Miao.LinearQuadratic.SS.LQProblem.gainDen_mul_gain
#print axioms Miao.LinearQuadratic.SS.LQProblem.riccati_eq_TF
#print axioms Miao.LinearQuadratic.SS.LQProblem.riccati_posSemidef
#print axioms Miao.LinearQuadratic.SS.LQProblem.cost_gain_add
#print axioms Miao.LinearQuadratic.SS.LQProblem.gain_isMinimizer
#print axioms Miao.LinearQuadratic.SS.LQProblem.gain_iff_TF_le
#print axioms Miao.LinearQuadratic.SS.psdCone
#print axioms Miao.LinearQuadratic.SS.LQProblem.closedLoop
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable
#print axioms Miao.LinearQuadratic.SS.LQProblem.costMat
#print axioms Miao.LinearQuadratic.SS.LQProblem.discCost
#print axioms Miao.LinearQuadratic.SS.LQProblem.TF_eq
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.entry_decay
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.tendsto_entry
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.tendsto_state
#print axioms Miao.LinearQuadratic.SS.LQProblem.transpose_mul_mul_apply
#print axioms Miao.LinearQuadratic.SS.LQProblem.tendsto_transpose_mul_mul_zero
#print axioms Miao.LinearQuadratic.SS.LQProblem.TF_iterate
#print axioms Miao.LinearQuadratic.SS.LQProblem.PF
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.hasSum_PF
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.tendsto_TF_iterate
#print axioms Miao.LinearQuadratic.SS.LQProblem.tendsto_TF
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.TF_PF
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.eq_PF
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.PF_posSemidef
#print axioms Miao.LinearQuadratic.SS.LQProblem.TFpsd
#print axioms Miao.LinearQuadratic.SS.LQProblem.TFpsd_iterate
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.globallyStable
#print axioms Miao.LinearQuadratic.SS.LQProblem.IsStable.hasSum_cost
#print axioms Miao.LinearQuadratic.SS.LQProblem.StablePolicy
#print axioms Miao.LinearQuadratic.SS.LQProblem.adp
#print axioms Miao.LinearQuadratic.SS.LQProblem.adp_isStronglyOrderStable
#print axioms Miao.LinearQuadratic.SS.LQProblem.eq_of_dotProduct_mulVec_eq
#print axioms Miao.LinearQuadratic.SS.LQProblem.PS
#print axioms Miao.LinearQuadratic.SS.LQProblem.gain_isMinGreedy
#print axioms Miao.LinearQuadratic.SS.LQProblem.isMinBellmanValue_riccati
#print axioms Miao.LinearQuadratic.SS.LQProblem.riccati_tfae
#print axioms Miao.LinearQuadratic.SS.LQProblem.optimality
#print axioms Miao.LinearQuadratic.SS.LQProblem.scalar_lifetimeCost
#print axioms Miao.LinearQuadratic.SS.LQProblem.scalar_compare
#print axioms Miao.LinearQuadratic.ls_Stable
#print axioms Miao.LinearQuadratic.ls_stable_iff_tendsto
#print axioms Miao.LinearQuadratic.ls_stable_of_specRad
#print axioms Miao.LinearQuadratic.ls_specRad_lt_of_stable
#print axioms Miao.LinearQuadratic.ls_stable_iff_specRad
#print axioms Miao.LinearQuadratic.ls_stable_transpose
#print axioms Miao.LinearQuadratic.ls_tendsto_zero_of_le_rec
#print axioms Miao.LinearQuadratic.ls_tendsto_zero_of_stable_input
#print axioms Miao.LinearQuadratic.ls_entry_eq_polar
#print axioms Miao.LinearQuadratic.ls_tendsto_of_quad
#print axioms Miao.LinearQuadratic.ls_exists_tendsto_of_quad
#print axioms Miao.LinearQuadratic.ls_posDef_coercive
#print axioms Miao.LinearQuadratic.ls_tendsto_zero_of_quad_posDef
#print axioms Miao.LinearQuadratic.LSProblem
#print axioms Miao.LinearQuadratic.LSProblem.mk
#print axioms Miao.LinearQuadratic.LSProblem.A
#print axioms Miao.LinearQuadratic.LSProblem.B
#print axioms Miao.LinearQuadratic.LSProblem.C
#print axioms Miao.LinearQuadratic.LSProblem.Q
#print axioms Miao.LinearQuadratic.LSProblem.R
#print axioms Miao.LinearQuadratic.LSProblem.S
#print axioms Miao.LinearQuadratic.LSProblem.β
#print axioms Miao.LinearQuadratic.LSProblem.loss
#print axioms Miao.LinearQuadratic.LSProblem.JointPSD
#print axioms Miao.LinearQuadratic.LSProblem.G
#print axioms Miao.LinearQuadratic.LSProblem.N
#print axioms Miao.LinearQuadratic.LSProblem.TF
#print axioms Miao.LinearQuadratic.LSProblem.T
#print axioms Miao.LinearQuadratic.LSProblem.F
#print axioms Miao.LinearQuadratic.LSProblem.G_posDef
#print axioms Miao.LinearQuadratic.LSProblem.G_transpose
#print axioms Miao.LinearQuadratic.LSProblem.N_transpose
#print axioms Miao.LinearQuadratic.LSProblem.G_mul_F
#print axioms Miao.LinearQuadratic.LSProblem.T_eq_sub
#print axioms Miao.LinearQuadratic.LSProblem.TF_expand
#print axioms Miao.LinearQuadratic.LSProblem.TF_F
#print axioms Miao.LinearQuadratic.LSProblem.TF_eq_T_add
#print axioms Miao.LinearQuadratic.LSProblem.TF_ge_T
#print axioms Miao.LinearQuadratic.LSProblem.TF_eq_T_iff
#print axioms Miao.LinearQuadratic.LSProblem.ls_sq_complete
#print axioms Miao.LinearQuadratic.LSProblem.dot_S_comm
#print axioms Miao.LinearQuadratic.LSProblem.loss_add_cont
#print axioms Miao.LinearQuadratic.LSProblem.quad_joint
#print axioms Miao.LinearQuadratic.LSProblem.loss_nonneg
#print axioms Miao.LinearQuadratic.LSProblem.Q_transpose_of_joint
#print axioms Miao.LinearQuadratic.LSProblem.Q_posSemidef_of_joint
#print axioms Miao.LinearQuadratic.LSProblem.T_transpose
#print axioms Miao.LinearQuadratic.LSProblem.T_posSemidef
#print axioms Miao.LinearQuadratic.LSShockLaw
#print axioms Miao.LinearQuadratic.LSShockLaw.mk
#print axioms Miao.LinearQuadratic.LSShockLaw.prob
#print axioms Miao.LinearQuadratic.LSShockLaw.int1
#print axioms Miao.LinearQuadratic.LSShockLaw.int2
#print axioms Miao.LinearQuadratic.LSShockLaw.mean
#print axioms Miao.LinearQuadratic.LSShockLaw.cov
#print axioms Miao.LinearQuadratic.ls_quad_shock_expand
#print axioms Miao.LinearQuadratic.ls_integral_quad
#print axioms Miao.LinearQuadratic.LSProblem.bellObj
#print axioms Miao.LinearQuadratic.LSProblem.bellObj_quad
#print axioms Miao.LinearQuadratic.LSProblem.bellObj_isGreatest
#print axioms Miao.LinearQuadratic.LSProblem.ls_foc
#print axioms Miao.LinearQuadratic.LSProblem.ls_first_variation
#print axioms Miao.LinearQuadratic.LSFinProblem
#print axioms Miao.LinearQuadratic.LSFinProblem.mk
#print axioms Miao.LinearQuadratic.LSFinProblem.A
#print axioms Miao.LinearQuadratic.LSFinProblem.B
#print axioms Miao.LinearQuadratic.LSFinProblem.C
#print axioms Miao.LinearQuadratic.LSFinProblem.Q
#print axioms Miao.LinearQuadratic.LSFinProblem.R
#print axioms Miao.LinearQuadratic.LSFinProblem.S
#print axioms Miao.LinearQuadratic.LSFinProblem.β
#print axioms Miao.LinearQuadratic.LSFinProblem.hor
#print axioms Miao.LinearQuadratic.LSFinProblem.PT
#print axioms Miao.LinearQuadratic.LSFinProblem.stage
#print axioms Miao.LinearQuadratic.LSFinProblem.Pbk
#print axioms Miao.LinearQuadratic.LSFinProblem.dbk
#print axioms Miao.LinearQuadratic.LSFinProblem.P
#print axioms Miao.LinearQuadratic.LSFinProblem.d
#print axioms Miao.LinearQuadratic.LSFinProblem.Fg
#print axioms Miao.LinearQuadratic.LSFinProblem.Vbk
#print axioms Miao.LinearQuadratic.LSFinProblem.V
#print axioms Miao.LinearQuadratic.LSFinProblem.P_hor
#print axioms Miao.LinearQuadratic.LSFinProblem.d_hor
#print axioms Miao.LinearQuadratic.LSFinProblem.V_hor
#print axioms Miao.LinearQuadratic.LSFinProblem.P_succ
#print axioms Miao.LinearQuadratic.LSFinProblem.d_succ
#print axioms Miao.LinearQuadratic.LSFinProblem.V_succ
#print axioms Miao.LinearQuadratic.LSFinProblem.proposition_9_2_1
#print axioms Miao.LinearQuadratic.LSFinProblem.eq_9_9
#print axioms Miao.LinearQuadratic.LSFinProblem.ls_finite_seq_identity
#print axioms Miao.LinearQuadratic.LSFinProblem.ls_finite_seq_optimal
#print axioms Miao.LinearQuadratic.LSFinProblem.zeroC
#print axioms Miao.LinearQuadratic.LSFinProblem.zeroC_Pbk
#print axioms Miao.LinearQuadratic.LSFinProblem.zeroC_dbk
#print axioms Miao.LinearQuadratic.LSFinProblem.certainty_equivalence
#print axioms Miao.LinearQuadratic.LSAssumption911
#print axioms Miao.LinearQuadratic.LSAssumption911.mk
#print axioms Miao.LinearQuadratic.LSAssumption911.mean
#print axioms Miao.LinearQuadratic.LSAssumption911.cov
#print axioms Miao.LinearQuadratic.ls_condExp_quad
#print axioms Miao.LinearQuadratic.ls_state
#print axioms Miao.LinearQuadratic.ls_traj
#print axioms Miao.LinearQuadratic.ls_output
#print axioms Miao.LinearQuadratic.ls_Stabilizable
#print axioms Miao.LinearQuadratic.definition_9_1_1_closed_loop
#print axioms Miao.LinearQuadratic.definition_9_1_1_steady_state
#print axioms Miao.LinearQuadratic.ls_gram
#print axioms Miao.LinearQuadratic.ls_Controllable
#print axioms Miao.LinearQuadratic.ls_gram_quad
#print axioms Miao.LinearQuadratic.ls_gram_posSemidef
#print axioms Miao.LinearQuadratic.ls_dot_self_nonneg
#print axioms Miao.LinearQuadratic.ls_gram_posDef_iff
#print axioms Miao.LinearQuadratic.ls_traj_eq
#print axioms Miao.LinearQuadratic.ls_reach_of_gram
#print axioms Miao.LinearQuadratic.definition_9_1_2_iff
#print axioms Miao.LinearQuadratic.ls_controllable_not_reach_one
#print axioms Miao.LinearQuadratic.ls_stabilizable_not_controllable
#print axioms Miao.LinearQuadratic.ls_Observable
#print axioms Miao.LinearQuadratic.ls_observable_gram
#print axioms Miao.LinearQuadratic.ls_state_sub
#print axioms Miao.LinearQuadratic.definition_9_1_3_iff
#print axioms Miao.LinearQuadratic.ls_observable_not_two_outputs
#print axioms Miao.LinearQuadratic.ls_Detectable
#print axioms Miao.LinearQuadratic.eq_9_3_error
#print axioms Miao.LinearQuadratic.eq_9_3_tendsto
#print axioms Miao.LinearQuadratic.eq_9_3_misprint
#print axioms Miao.LinearQuadratic.definition_9_1_4_rule
#print axioms Miao.LinearQuadratic.ls_riccati_le_TF
#print axioms Miao.LinearQuadratic.ls_posSemidef_of_le
#print axioms Miao.LinearQuadratic.ls_quad_le
#print axioms Miao.LinearQuadratic.ls_riccati_mono
#print axioms Miao.LinearQuadratic.ls_iter_psd
#print axioms Miao.LinearQuadratic.ls_iter_mono_le
#print axioms Miao.LinearQuadratic.ls_zero_le_psd
#print axioms Miao.LinearQuadratic.ls_iter_zero_mono
#print axioms Miao.LinearQuadratic.ls_iter_zero_mono_add
#print axioms Miao.LinearQuadratic.ls_finite_lower
#print axioms Miao.LinearQuadratic.ls_iter_le_PF
#print axioms Miao.LinearQuadratic.ls_iter_bdd_of_controllable
#print axioms Miao.LinearQuadratic.ls_tendsto_quad
#print axioms Miao.LinearQuadratic.ls_iter_converges
#print axioms Miao.LinearQuadratic.ls_tendsto_mul
#print axioms Miao.LinearQuadratic.ls_tendsto_inv
#print axioms Miao.LinearQuadratic.ls_tendsto_gain
#print axioms Miao.LinearQuadratic.ls_tendsto_riccati
#print axioms Miao.LinearQuadratic.ls_fixed_of_tendsto
#print axioms Miao.LinearQuadratic.ls_Detects
#print axioms Miao.LinearQuadratic.ls_cost_tendsto_zero
#print axioms Miao.LinearQuadratic.ls_stable_of_fixed
#print axioms Miao.LinearQuadratic.ls_detects_of_posDef
#print axioms Miao.LinearQuadratic.ls_tendsto_mulVec_zero
#print axioms Miao.LinearQuadratic.ls_tendsto_L
#print axioms Miao.LinearQuadratic.ls_detects_of_detectable
#print axioms Miao.LinearQuadratic.ls_detects_of_observable
#print axioms Miao.LinearQuadratic.ls_riccati_main
#print axioms Miao.LinearQuadratic.LSProblem.toSS
#print axioms Miao.LinearQuadratic.LSProblem.toSS_gainDen
#print axioms Miao.LinearQuadratic.LSProblem.toSS_riccati
#print axioms Miao.LinearQuadratic.LSProblem.toSS_gain
#print axioms Miao.LinearQuadratic.LSProblem.toSS_closedLoop
#print axioms Miao.LinearQuadratic.LSProblem.toSS_costMat
#print axioms Miao.LinearQuadratic.LSProblem.toSS_riccati_iter
#print axioms Miao.LinearQuadratic.LSProblem.loss_S_zero
#print axioms Miao.LinearQuadratic.LSProblem.ls_discount_rescale
#print axioms Miao.LinearQuadratic.LSProblem.toFin
#print axioms Miao.LinearQuadratic.LSProblem.toFin_stage
#print axioms Miao.LinearQuadratic.LSProblem.toFin_Pbk
#print axioms Miao.LinearQuadratic.LSProblem.dIter
#print axioms Miao.LinearQuadratic.LSProblem.toFin_dbk
#print axioms Miao.LinearQuadratic.LSProblem.eq_9_11
#print axioms Miao.LinearQuadratic.LSProblem.T_zero_S
#print axioms Miao.LinearQuadratic.LSProblem.ls_P_one
#print axioms Miao.LinearQuadratic.LSProblem.ls_P_mono
#print axioms Miao.LinearQuadratic.LSProblem.ls_P_mono_not_strict
#print axioms Miao.LinearQuadratic.LSProblem.ls_discounted_main
#print axioms Miao.LinearQuadratic.LSProblem.proposition_9_3_1
#print axioms Miao.LinearQuadratic.LSProblem.proposition_9_3_2
#print axioms Miao.LinearQuadratic.LSProblem.eq_9_13
#print axioms Miao.LinearQuadratic.LSProblem.ls_sqrt_sandwich
#print axioms Miao.LinearQuadratic.LSProblem.eq_9_13_series
#print axioms Miao.LinearQuadratic.LSProblem.eq_9_14
#print axioms Miao.LinearQuadratic.LSProblem.ls_P_le_policy
#print axioms Miao.LinearQuadratic.LSProblem.ls_P_le_policy_misprint
#print axioms Miao.LinearQuadratic.LSProblem.ls_infinite_value
#print axioms Miao.LinearQuadratic.LSProblem.eq_9_16_9_17
#print axioms Miao.LinearQuadratic.controllable_stabilizable
#print axioms Miao.LinearQuadratic.eq_9_10_growth
#print axioms Miao.LinearQuadratic.ls_stable_of_side_condition
#print axioms Miao.LinearQuadratic.LSProblem.ls_G_tendsto
#print axioms Miao.LinearQuadratic.LSProblem.ls_N_tendsto
#print axioms Miao.LinearQuadratic.LSProblem.ls_F_tendsto
#print axioms Miao.LinearQuadratic.LSProblem.ls_dIter_tendsto
#print axioms Miao.LinearQuadratic.LSProblem.ls_policy_riccati
#print axioms Miao.LinearQuadratic.LSProblem.ls_policy_lyapunov
#print axioms Miao.LinearQuadratic.LSProblem.ls_lagrange
#print axioms Miao.LinearQuadratic.LSProblem.ls_envelope
#print axioms Miao.LinearQuadratic.LSProblem.ls_verification
#print axioms Miao.LinearQuadratic.LSProblem.normS
#print axioms Miao.LinearQuadratic.LSProblem.ex_9_1_loss
#print axioms Miao.LinearQuadratic.LSProblem.ex_9_1_transition
#print axioms Miao.LinearQuadratic.LSProblem.ex_9_1
#print axioms Miao.LinearQuadratic.LSProblem.augment
#print axioms Miao.LinearQuadratic.LSProblem.ls_aug
#print axioms Miao.LinearQuadratic.LSProblem.ex_9_2_transition
#print axioms Miao.LinearQuadratic.LSProblem.ex_9_2_loss
#print axioms Miao.LinearQuadratic.LSProblem.ex_9_2
#print axioms Miao.LinearQuadratic.ls_jointPSD_of_loss
#print axioms Miao.LinearQuadratic.hallProblem
#print axioms Miao.LinearQuadratic.ex_9_4_loss
#print axioms Miao.LinearQuadratic.ex_9_4_transition
#print axioms Miao.LinearQuadratic.ex_9_4_jointPSD
#print axioms Miao.LinearQuadratic.hallq
#print axioms Miao.LinearQuadratic.hallW
#print axioms Miao.LinearQuadratic.hallP
#print axioms Miao.LinearQuadratic.hallF
#print axioms Miao.LinearQuadratic.hallP_quad
#print axioms Miao.LinearQuadratic.ex_9_4_riccati
#print axioms Miao.LinearQuadratic.ex_9_4_rule
#print axioms Miao.LinearQuadratic.ex_9_4_martingale
#print axioms Miao.LinearQuadratic.ex_9_4_closed_loop
#print axioms Miao.LinearQuadratic.ex_9_4_optimal
#print axioms Miao.LinearQuadratic.ex_9_4_bellman
#print axioms Miao.LinearQuadratic.ex_9_4_zero_solution
#print axioms Miao.LinearQuadratic.ex_9_4_two_solutions
#print axioms Miao.LinearQuadratic.cp_sumElim_dotProduct
#print axioms Miao.LinearQuadratic.cp_dotProduct_mulVec_comm
#print axioms Miao.LinearQuadratic.cp_dotProduct_mulVec_symm
#print axioms Miao.LinearQuadratic.cpLoss
#print axioms Miao.LinearQuadratic.cpW
#print axioms Miao.LinearQuadratic.cpDbar
#print axioms Miao.LinearQuadratic.cpAbar
#print axioms Miao.LinearQuadratic.eq_9_19_W
#print axioms Miao.LinearQuadratic.cp_augmented
#print axioms Miao.LinearQuadratic.cpLagrangian
#print axioms Miao.LinearQuadratic.cpPerturb
#print axioms Miao.LinearQuadratic.cpInit
#print axioms Miao.LinearQuadratic.cpGrad
#print axioms Miao.LinearQuadratic.cp_lagr_term
#print axioms Miao.LinearQuadratic.cp_lagrangian_perturb
#print axioms Miao.LinearQuadratic.cp_hasDerivAt
#print axioms Miao.LinearQuadratic.eq_foc_9_4
#print axioms Miao.LinearQuadratic.cp_init_eq_Dbar
#print axioms Miao.LinearQuadratic.cp_grad_eq
#print axioms Miao.LinearQuadratic.cpLeft
#print axioms Miao.LinearQuadratic.cpRight
#print axioms Miao.LinearQuadratic.eq_9_22
#print axioms Miao.LinearQuadratic.cpReorder
#print axioms Miao.LinearQuadratic.cpColEquiv
#print axioms Miao.LinearQuadratic.cpRowEquiv
#print axioms Miao.LinearQuadratic.cpJ
#print axioms Miao.LinearQuadratic.cpH
#print axioms Miao.LinearQuadratic.cpCfin
#print axioms Miao.LinearQuadratic.cp_submatrix_id_mulVec
#print axioms Miao.LinearQuadratic.cp_comp_equiv_iff
#print axioms Miao.LinearQuadratic.cp_reordered_iff
#print axioms Miao.LinearQuadratic.cp_norm_comp_equiv
#print axioms Miao.LinearQuadratic.cp_saddle_path
#print axioms Miao.LinearQuadratic.cp_time_inconsistency
#print axioms Miao.LinearQuadratic.cp_recursive_form
#print axioms Miao.LinearQuadratic.ex941D
#print axioms Miao.LinearQuadratic.ex941A
#print axioms Miao.LinearQuadratic.ex941B
#print axioms Miao.LinearQuadratic.ex941C
#print axioms Miao.LinearQuadratic.example_9_4_1
#print axioms Miao.LinearQuadratic.example_9_4_1_rn
#print axioms Miao.LinearQuadratic.ex941Q
#print axioms Miao.LinearQuadratic.example_9_4_1_loss
#print axioms Miao.LinearQuadratic.cpPert
#print axioms Miao.LinearQuadratic.cp_pert_zero
#print axioms Miao.LinearQuadratic.cp_sum_delta
#print axioms Miao.LinearQuadratic.cp_sum_delta_sq
#print axioms Miao.LinearQuadratic.cp_sum_delta_succ
#print axioms Miao.LinearQuadratic.cp_hasDerivAt_quad
#print axioms Miao.LinearQuadratic.cp_stationary_iff
#print axioms Miao.LinearQuadratic.ex942Lagr
#print axioms Miao.LinearQuadratic.eq_9_25
#print axioms Miao.LinearQuadratic.eq_9_26
#print axioms Miao.LinearQuadratic.eq_9_27
#print axioms Miao.LinearQuadratic.ex942L
#print axioms Miao.LinearQuadratic.ex942R
#print axioms Miao.LinearQuadratic.example_9_4_2_system
#print axioms Miao.LinearQuadratic.ex942Lprinted
#print axioms Miao.LinearQuadratic.example_9_4_2_printed_row_false
#print axioms Miao.LinearQuadratic.eq_9_28
#print axioms Miao.LinearQuadratic.ex942b
#print axioms Miao.LinearQuadratic.ex942a
#print axioms Miao.LinearQuadratic.ex942_b_eq
#print axioms Miao.LinearQuadratic.eq_9_29
#print axioms Miao.LinearQuadratic.eq_9_29_kappa_zero
#print axioms Miao.LinearQuadratic.ex942_lag_sum
#print axioms Miao.LinearQuadratic.ex942Rule
#print axioms Miao.LinearQuadratic.ex942_rule_solves
#print axioms Miao.LinearQuadratic.ex942_rule_expected
#print axioms Miao.LinearQuadratic.ex942_unique_bounded
#print axioms Miao.LinearQuadratic.ex942_solution
#print axioms Miao.LinearQuadratic.ex942_muz
#print axioms Miao.LinearQuadratic.ex942_time_inconsistent
#print axioms Miao.LinearQuadratic.cp_dot_left
#print axioms Miao.LinearQuadratic.cp_quad_transpose
#print axioms Miao.LinearQuadratic.cp_dot_swap
#print axioms Miao.LinearQuadratic.CPDisc
#print axioms Miao.LinearQuadratic.CPDisc.mk
#print axioms Miao.LinearQuadratic.CPDisc.Azz
#print axioms Miao.LinearQuadratic.CPDisc.Azy
#print axioms Miao.LinearQuadratic.CPDisc.Ayz
#print axioms Miao.LinearQuadratic.CPDisc.Ayy
#print axioms Miao.LinearQuadratic.CPDisc.Bz
#print axioms Miao.LinearQuadratic.CPDisc.By
#print axioms Miao.LinearQuadratic.CPDisc.D21
#print axioms Miao.LinearQuadratic.CPDisc.D22
#print axioms Miao.LinearQuadratic.CPDisc.Qzz
#print axioms Miao.LinearQuadratic.CPDisc.Qzy
#print axioms Miao.LinearQuadratic.CPDisc.Qyy
#print axioms Miao.LinearQuadratic.CPDisc.R
#print axioms Miao.LinearQuadratic.CPDisc.Sz
#print axioms Miao.LinearQuadratic.CPDisc.Sy
#print axioms Miao.LinearQuadratic.CPDisc.β
#print axioms Miao.LinearQuadratic.CPDisc.Sig
#print axioms Miao.LinearQuadratic.CPDisc.loss
#print axioms Miao.LinearQuadratic.CPDisc.mean
#print axioms Miao.LinearQuadratic.CPDisc.G
#print axioms Miao.LinearQuadratic.CPDisc.Feasible
#print axioms Miao.LinearQuadratic.CPDisc.K
#print axioms Miao.LinearQuadratic.CPDisc.Hz
#print axioms Miao.LinearQuadratic.CPDisc.Hu
#print axioms Miao.LinearQuadratic.CPDisc.Ast
#print axioms Miao.LinearQuadratic.CPDisc.Bst
#print axioms Miao.LinearQuadratic.CPDisc.Qst
#print axioms Miao.LinearQuadratic.CPDisc.Rst
#print axioms Miao.LinearQuadratic.CPDisc.Sst
#print axioms Miao.LinearQuadratic.cp_disc_loss_eq
#print axioms Miao.LinearQuadratic.cp_expected_quadratic
#print axioms Miao.LinearQuadratic.eq_9_35_36
#print axioms Miao.LinearQuadratic.eq_9_37
#print axioms Miao.LinearQuadratic.eq_9_37_book
#print axioms Miao.LinearQuadratic.cpDiscEx
#print axioms Miao.LinearQuadratic.eq_9_36_false
#print axioms Miao.LinearQuadratic.eq_9_38
#print axioms Miao.LinearQuadratic.eq_step2
#print axioms Miao.LinearQuadratic.CPDisc.Qbook
#print axioms Miao.LinearQuadratic.cp_Qbook_quad
#print axioms Miao.LinearQuadratic.cpDiscEx2
#print axioms Miao.LinearQuadratic.step2_book_S_false
#print axioms Miao.LinearQuadratic.step2_book_R_false
#print axioms Miao.LinearQuadratic.cpObj
#print axioms Miao.LinearQuadratic.cpGain
#print axioms Miao.LinearQuadratic.cpF
#print axioms Miao.LinearQuadratic.cp_obj_expand
#print axioms Miao.LinearQuadratic.cp_obj_complete_square
#print axioms Miao.LinearQuadratic.eq_9_40
#print axioms Miao.LinearQuadratic.cpVbook
#print axioms Miao.LinearQuadratic.cpVnext
#print axioms Miao.LinearQuadratic.eq_9_41
#print axioms Miao.LinearQuadratic.cp_Vnext_quad
#print axioms Miao.LinearQuadratic.cp_Vnext_symm
#print axioms Miao.LinearQuadratic.cp_Qst_symm
#print axioms Miao.LinearQuadratic.cp_Rst_symm
#print axioms Miao.LinearQuadratic.eq_9_42
#print axioms Miao.LinearQuadratic.CPDisc.total
#print axioms Miao.LinearQuadratic.CPDisc.Fnext
#print axioms Miao.LinearQuadratic.CPDisc.Vnext
#print axioms Miao.LinearQuadratic.CPDisc.Mnext
#print axioms Miao.LinearQuadratic.CPDisc.Gain
#print axioms Miao.LinearQuadratic.cp_total_eq
#print axioms Miao.LinearQuadratic.cp_bellman_step
#print axioms Miao.LinearQuadratic.IsMPE
#print axioms Miao.LinearQuadratic.definition_9_5_1
#print axioms Miao.LinearQuadratic.cp_mpe_of_fixed_point
#print axioms Miao.LinearQuadratic.ex951θ
#print axioms Miao.LinearQuadratic.ex951θ_pos
#print axioms Miao.LinearQuadratic.ex951θ_le_one
#print axioms Miao.LinearQuadratic.eq_9_43
#print axioms Miao.LinearQuadratic.IsMPE951
#print axioms Miao.LinearQuadratic.ex951pi
#print axioms Miao.LinearQuadratic.ex951_denoms
#print axioms Miao.LinearQuadratic.example_9_5_1
#print axioms Miao.LinearQuadratic.example_9_5_1_unique
#print axioms Miao.LinearQuadratic.ex951_series
#print axioms Miao.LinearQuadratic.ex951_forward
#print axioms Miao.LinearQuadratic.cp_commitment_vs_discretion
#print axioms Miao.LinearQuadratic.rc_lr_mean_one
#print axioms Miao.LinearQuadratic.RCRatios
#print axioms Miao.LinearQuadratic.RCRatios.mk
#print axioms Miao.LinearQuadratic.RCRatios.meas
#print axioms Miao.LinearQuadratic.RCRatios.nonneg
#print axioms Miao.LinearQuadratic.RCRatios.le
#print axioms Miao.LinearQuadratic.RCRatios.mean
#print axioms Miao.LinearQuadratic.rcM
#print axioms Miao.LinearQuadratic.rcM_zero
#print axioms Miao.LinearQuadratic.rcM_succ
#print axioms Miao.LinearQuadratic.RCRatios.K_nonneg
#print axioms Miao.LinearQuadratic.rcM_measurable
#print axioms Miao.LinearQuadratic.rcM_nonneg
#print axioms Miao.LinearQuadratic.rcM_le
#print axioms Miao.LinearQuadratic.rc_abs_mul_log_le
#print axioms Miao.LinearQuadratic.rc_integrable_of_bound
#print axioms Miao.LinearQuadratic.rc_m_integrable
#print axioms Miao.LinearQuadratic.rcM_integrable
#print axioms Miao.LinearQuadratic.rcM_bound
#print axioms Miao.LinearQuadratic.rc_one_step
#print axioms Miao.LinearQuadratic.rc_martingale
#print axioms Miao.LinearQuadratic.rc_tower
#print axioms Miao.LinearQuadratic.rc_integral_M
#print axioms Miao.LinearQuadratic.rcQ
#print axioms Miao.LinearQuadratic.rc_distorted_integral
#print axioms Miao.LinearQuadratic.rcQ_isProbability
#print axioms Miao.LinearQuadratic.rc_distorted_consistent
#print axioms Miao.LinearQuadratic.rc_rnDeriv
#print axioms Miao.LinearQuadratic.rc_relEntropy
#print axioms Miao.LinearQuadratic.rc_MlogM_integrable
#print axioms Miao.LinearQuadratic.rc_entropy_nonneg
#print axioms Miao.LinearQuadratic.rc_entropy_eq_zero_iff
#print axioms Miao.LinearQuadratic.rcQ_eq_iff
#print axioms Miao.LinearQuadratic.rcG
#print axioms Miao.LinearQuadratic.rcG_measurable
#print axioms Miao.LinearQuadratic.rcG_abs_le
#print axioms Miao.LinearQuadratic.rcG_integrable
#print axioms Miao.LinearQuadratic.rc_increment_eq
#print axioms Miao.LinearQuadratic.rc_increment_nonneg
#print axioms Miao.LinearQuadratic.rc_entropy_decomp
#print axioms Miao.LinearQuadratic.rc_discounted_sum
#print axioms Miao.LinearQuadratic.rc_discounted_entropy
#print axioms Miao.LinearQuadratic.rcDiscEntropy
#print axioms Miao.LinearQuadratic.rcEntropyConstraint
#print axioms Miao.LinearQuadratic.rc_discEntropy_nonneg
#print axioms Miao.LinearQuadratic.rc_tower_sum
#print axioms Miao.LinearQuadratic.eq_9_46
#print axioms Miao.LinearQuadratic.rcMultObj
#print axioms Miao.LinearQuadratic.rc_lagrange
#print axioms Miao.LinearQuadratic.rc_weak_duality
#print axioms Miao.LinearQuadratic.rc_mult_mono
#print axioms Miao.LinearQuadratic.rc_mult_le_ref
#print axioms Miao.LinearQuadratic.rc_sqrt_penalty
#print axioms Miao.LinearQuadratic.rc_mult_lower
#print axioms Miao.LinearQuadratic.rc_mult_tendsto
#print axioms Miao.LinearQuadratic.rc_bellman_scale
#print axioms Miao.LinearQuadratic.rc_bellman_divide
#print axioms Miao.LinearQuadratic.rc_min_add
#print axioms Miao.LinearQuadratic.rcAdm
#print axioms Miao.LinearQuadratic.rcObj
#print axioms Miao.LinearQuadratic.rcZ
#print axioms Miao.LinearQuadratic.rcWorst
#print axioms Miao.LinearQuadratic.rcR
#print axioms Miao.LinearQuadratic.rc_mul_log_sub
#print axioms Miao.LinearQuadratic.rcZ_pos
#print axioms Miao.LinearQuadratic.rcWorst_pos
#print axioms Miao.LinearQuadratic.rcWorst_log
#print axioms Miao.LinearQuadratic.eq_9_47_9_48
#print axioms Miao.LinearQuadratic.eq_9_47_foc
#print axioms Miao.LinearQuadratic.eq_9_47_log
#print axioms Miao.LinearQuadratic.eq_9_47_misprint
#print axioms Miao.LinearQuadratic.rc_R_le_mean
#print axioms Miao.LinearQuadratic.eq_9_49
#print axioms Miao.LinearQuadratic.rcH
#print axioms Miao.LinearQuadratic.rcK
#print axioms Miao.LinearQuadratic.rcD
#print axioms Miao.LinearQuadratic.rcWstar
#print axioms Miao.LinearQuadratic.rcV
#print axioms Miao.LinearQuadratic.rcd
#print axioms Miao.LinearQuadratic.rcH_transpose
#print axioms Miao.LinearQuadratic.rcK_eq_smul
#print axioms Miao.LinearQuadratic.rcH_eq_smul
#print axioms Miao.LinearQuadratic.rcK_posDef_iff
#print axioms Miao.LinearQuadratic.rcK_inv
#print axioms Miao.LinearQuadratic.rcD_transpose
#print axioms Miao.LinearQuadratic.rcD_quad
#print axioms Miao.LinearQuadratic.rcD_posSemidef
#print axioms Miao.LinearQuadratic.rc_mce_expand
#print axioms Miao.LinearQuadratic.rc_mce_decomp
#print axioms Miao.LinearQuadratic.rc_mce
#print axioms Miao.LinearQuadratic.rc_breakdown
#print axioms Miao.LinearQuadratic.RCGaussian
#print axioms Miao.LinearQuadratic.RCGaussian.mk
#print axioms Miao.LinearQuadratic.RCGaussian.prob
#print axioms Miao.LinearQuadratic.RCGaussian.integrable
#print axioms Miao.LinearQuadratic.RCGaussian.mgf
#print axioms Miao.LinearQuadratic.rc_exponent
#print axioms Miao.LinearQuadratic.rc_R_quad
#print axioms Miao.LinearQuadratic.rcRobObj
#print axioms Miao.LinearQuadratic.rc_outer_eq
#print axioms Miao.LinearQuadratic.rc_robObj_eq
#print axioms Miao.LinearQuadratic.rc_robObj_max
#print axioms Miao.LinearQuadratic.eq_9_51_9_55
#print axioms Miao.LinearQuadratic.rc_bellman_converse
#print axioms Miao.LinearQuadratic.rcV_comp_measurable
#print axioms Miao.LinearQuadratic.rc_robust_bellman
#print axioms Miao.LinearQuadratic.rc_modified_ce
#print axioms Miao.LinearQuadratic.rc_inv_fin_one
#print axioms Miao.LinearQuadratic.rcScalarProblem
#print axioms Miao.LinearQuadratic.rc_C_matters
#print axioms Miao.LinearQuadratic.rcGaussPdf
#print axioms Miao.LinearQuadratic.rcStdPdf
#print axioms Miao.LinearQuadratic.rcStdPdf_eq
#print axioms Miao.LinearQuadratic.rc_llr_normal
#print axioms Miao.LinearQuadratic.RCMoments
#print axioms Miao.LinearQuadratic.RCMoments.mk
#print axioms Miao.LinearQuadratic.RCMoments.prob
#print axioms Miao.LinearQuadratic.RCMoments.int1
#print axioms Miao.LinearQuadratic.RCMoments.int2
#print axioms Miao.LinearQuadratic.RCMoments.mean
#print axioms Miao.LinearQuadratic.RCMoments.cov
#print axioms Miao.LinearQuadratic.rc_moment_quad
#print axioms Miao.LinearQuadratic.rc_moment_trace_inv
#print axioms Miao.LinearQuadratic.rc_moment_half
#print axioms Miao.LinearQuadratic.rc_moment_sign_misprint
#print axioms Miao.LinearQuadratic.rc_half_sq_split
#print axioms Miao.LinearQuadratic.rc_half_sq_moment
#print axioms Miao.LinearQuadratic.eq_9_56
#print axioms Miao.LinearQuadratic.rc_worst_ratio
#print axioms Miao.LinearQuadratic.rc_worst_exponent
#print axioms Miao.LinearQuadratic.rc_worst_density
#print axioms Miao.LinearQuadratic.rc_nonsingular_not_enough
#print axioms Miao.LinearQuadratic.rc_R_first_line
#print axioms Miao.LinearQuadratic.rc_R_lines_agree
#print axioms Miao.LinearQuadratic.rc_log_det_bounds
#print axioms Miao.LinearQuadratic.rc_tendsto_mul
#print axioms Miao.LinearQuadratic.rc_tendsto_inv
#print axioms Miao.LinearQuadratic.rc_tendsto_smul
#print axioms Miao.LinearQuadratic.rc_inv_smul
#print axioms Miao.LinearQuadratic.rc_D_tendsto
#print axioms Miao.LinearQuadratic.rc_d_tendsto
#print axioms Miao.LinearQuadratic.rc_T_F_tendsto
#print axioms Miao.LinearQuadratic.rc_posSemidef_of_tendsto
#print axioms Miao.LinearQuadratic.ex_9_3
#print axioms Miao.LinearQuadratic.ex_9_3_unique
#print axioms Miao.LinearQuadratic.rcHallRobust
#print axioms Miao.LinearQuadratic.rcHallK
#print axioms Miao.LinearQuadratic.rcHallQθ
#print axioms Miao.LinearQuadratic.rcHallRank1
#print axioms Miao.LinearQuadratic.rcHallPθ
#print axioms Miao.LinearQuadratic.rcHallGain
#print axioms Miao.LinearQuadratic.ex_9_5_loss
#print axioms Miao.LinearQuadratic.ex_9_5_data
#print axioms Miao.LinearQuadratic.rc_hall_rank1_T
#print axioms Miao.LinearQuadratic.rc_hall_rank1_D
#print axioms Miao.LinearQuadratic.ex_9_5_breakdown
#print axioms Miao.LinearQuadratic.ex_9_5
#print axioms Miao.LinearQuadratic.ex_9_5_rule
#print axioms Miao.LinearQuadratic.ex_9_5_hall_case
#print axioms Miao.LinearQuadratic.ex_9_5_bellman
#print axioms Miao.LinearQuadratic.ex_9_5_limit
#print axioms Miao.LinearQuadratic.ex_9_5_more_responsive
#print axioms Miao.LinearQuadratic.rc_gauss_1d
#print axioms Miao.LinearQuadratic.rc_std_map_eigen
#print axioms Miao.LinearQuadratic.rc_gaussian_std
#print axioms Miao.LinearQuadratic.rc_R_quad_std
#print axioms Miao.LinearQuadratic.eq_9_51_9_55_std
#print axioms Miao.LinearQuadratic.rc_robust_bellman_std
#print axioms Miao.LinearQuadratic.ex_9_5_bellman_std
