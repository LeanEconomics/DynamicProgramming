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
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block
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
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Markov matrices, contractions and Blackwell's condition: the shared vocabulary

Copied from `GeneralStates/AbstractDecisionProcesses` (module `Basics`), namespace renamed to
`Miao.PartialInformation.SS`.

Volume 2, Chapter 2 of Sargent and Stachurski, *Dynamic Programming*, uses the
Volume 1 vocabulary of Markov matrices (§2.3.1.3), the contraction machinery of
§1.2.2, global stability, Blackwell's condition (Lemma 2.2.4), the comparison of
fixed points of ordered operators (Proposition 2.2.7) and the estimate
`|max f − max g| ≤ max |f − g|` (Lemma 2.2.2). Each chapter project is
self-contained, so these are restated here with short Mathlib proofs.
-/

open Finset Matrix Filter Topology Function

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The spectral radius of a real matrix on a finite state space

Copied from `GeneralStates/AbstractDecisionProcesses` (module `SpectralRadius`), namespace renamed
to `Miao.PartialInformation.SS`.

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

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Order stability, order completeness and order continuity

Copied from `GeneralStates/AbstractDecisionProcesses` (module `OrderTheory`), namespace renamed to
`Miao.PartialInformation.SS`.

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

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Abstract decision processes on posets

Copied from `GeneralStates/AbstractDecisionProcesses` (module `ADP`), namespace renamed to
`Miao.PartialInformation.SS`.

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

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Algorithms and convergence

Copied from `GeneralStates/AbstractDecisionProcesses` (module `Algorithms`), namespace renamed to
`Miao.PartialInformation.SS`.

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

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Minimization

Copied from `GeneralStates/AbstractDecisionProcesses` (module `Minimization`), namespace renamed to
`Miao.PartialInformation.SS`.

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

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# LQ control: the Riccati map and the control gain

Copied from `GeneralStates/AbstractDecisionProcesses` (module `LQAlgebra`), namespace renamed to
`Miao.PartialInformation.SS`.

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

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# LQ control as an ADP

Copied from `GeneralStates/AbstractDecisionProcesses` (module `LQControl`), namespace renamed to
`Miao.PartialInformation.SS`.

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

namespace Miao.PartialInformation.SS

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

end Miao.PartialInformation.SS

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Stable matrices and asymptotic tools for Chapter 9

Copied from `EconomicDynamics/LinearQuadratic` (module `LSStability`), namespace renamed.

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The LQ problem, the Riccati operator and completing the square

Copied from `EconomicDynamics/LinearQuadratic` (module `LSRiccati`), namespace renamed.

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite-horizon LQ problems: Proposition 9.2.1

Copied from `EconomicDynamics/LinearQuadratic` (module `LSFiniteHorizon`), namespace renamed.

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The controlled linear state-space system (Miao §9.1)

Copied from `EconomicDynamics/LinearQuadratic` (module `LSStateSpace`), namespace renamed.

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Convergence of the Riccati iteration (the undiscounted core of Propositions 9.3.1–9.3.2)

Copied from `EconomicDynamics/LinearQuadratic` (module `LSRiccatiConvergence`), namespace renamed.

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Infinite-horizon limits: Propositions 9.3.1 and 9.3.2

Copied from `EconomicDynamics/LinearQuadratic` (module `LSInfiniteHorizon`), namespace renamed.

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

namespace Miao.PartialInformation

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


end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Limits, the side condition and the numerical methods of §9.3

Copied from `EconomicDynamics/LinearQuadratic` (module `LSInfiniteLimits`), namespace renamed.

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

namespace Miao.PartialInformation

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

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Second moments of square-integrable random vectors

Miao, §10.1.1, pp. 327–333. The Kalman filter of §10.1.1 is proved here in its
linear-projection (second-moment) reading: every computation of the text that takes an
expectation `E[vw']` of products of the state, the shocks, the estimation errors and the
innovations is an identity between the second-moment matrices `var_mom μ v w = E[vw']` (from the
copied Chapter 2 module `VARMoments`) of square-integrable random vectors.

This module provides the calculus of these matrices:

* `kf_L2 μ v`: every coordinate of `v : Ω → I → ℝ` is in `L²(μ)`; it is preserved by linear
  maps `kf_app M v = Mv`, sums, differences and (for finite `μ`) constants (`kf_L2_app`,
  `kf_L2_add`, `kf_L2_sub`, `kf_L2_const`, `kf_L2_zero`);
* bilinearity: `E[(Mv)w'] = M E[vw']`, `E[v(Nw)'] = E[vw']N'`, additivity in both arguments
  (`kf_mom_app_left`, `kf_mom_app_right`, `kf_mom_add_left`, `kf_mom_add_right`,
  `kf_mom_sub_left`, `kf_mom_sub_right`, `kf_mom_lin2`, `kf_mom_lin_sub`), symmetry
  `E[wv'] = (E[vw'])'` (`kf_mom_transpose`), and `E[vv'] ≥ 0` (`kf_mom_self_psd`);
* means: `kf_mean μ v = E v`, linear (`kf_mean_app`, `kf_mean_add`, `kf_mean_sub`,
  `kf_mean_const`), and `E[c w'] = c (Ew)'`, `E[v c'] = (Ev)c'` for a constant `c`
  (`kf_mom_const_left`, `kf_mom_const_right`);
* `kf_app` is additive and composes (`kf_app_add`, `kf_app_sub`, `kf_app_app`,
  `kf_app_sub_mat`, `kf_app_zero_mat`).
-/

open MeasureTheory Matrix

namespace Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)

/-- Square integrability of a random vector: every coordinate is in `L²(μ)`. -/
def kf_L2 {I : Type*} (v : Ω → I → ℝ) : Prop := ∀ i, MemLp (fun ω => v ω i) 2 μ

/-- The random vector `ω ↦ Mv(ω)`. -/
def kf_app {I J : Type*} [Fintype J] (M : Matrix I J ℝ) (v : Ω → J → ℝ) : Ω → I → ℝ :=
  fun ω => M *ᵥ v ω

/-- The mean vector `Ev`. -/
noncomputable def kf_mean {I : Type*} (v : Ω → I → ℝ) : I → ℝ := fun i => ∫ ω, v ω i ∂μ

variable {μ}
variable {I J K : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
/-- Linear images of square-integrable vectors are square integrable. -/
theorem kf_L2_app {v : Ω → J → ℝ} (hv : kf_L2 μ v) (M : Matrix I J ℝ) :
    kf_L2 μ (kf_app M v) := by
  intro i
  unfold kf_app
  have : (fun ω => (M *ᵥ v ω) i) = fun ω => ∑ j, M i j * v ω j := by
    funext ω
    simp [mulVec, dotProduct]
  rw [this]
  exact memLp_finsetSum _ fun j _ => (hv j).const_mul _

omit [Fintype I] [Fintype J] in
theorem kf_L2_add {v w : Ω → I → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w) : kf_L2 μ (v + w) :=
  fun i => (hv i).add (hw i)

omit [Fintype I] [Fintype J] in
theorem kf_L2_sub {v w : Ω → I → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w) : kf_L2 μ (v - w) :=
  fun i => (hv i).sub (hw i)

omit [Fintype I] [Fintype J] in
theorem kf_L2_const [IsFiniteMeasure μ] (c : I → ℝ) : kf_L2 μ (fun _ : Ω => c) :=
  fun i => memLp_const (c i)

omit [Fintype I] [Fintype J] in
theorem kf_L2_zero : kf_L2 μ (0 : Ω → I → ℝ) := fun _ => MemLp.zero

omit [Fintype I] [Fintype J] in
/-- `E[wv'] = (E[vw'])'`. -/
theorem kf_mom_transpose (v : Ω → I → ℝ) (w : Ω → J → ℝ) :
    var_mom μ w v = (var_mom μ v w)ᵀ := by
  ext i j
  simp only [var_mom, of_apply, transpose_apply, mul_comm]

omit [Fintype I] in
/-- `E[(Mv)w'] = M E[vw']`. -/
theorem kf_mom_app_left {v : Ω → J → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w)
    (M : Matrix I J ℝ) : var_mom μ (kf_app M v) w = M * var_mom μ v w := by
  ext i k
  simp only [kf_app, var_mom, of_apply, mul_apply]
  have := var_integral_sum_mul (μ := μ) (M i) (f := fun j ω => v ω j) hv (hw k)
  simpa [mulVec, dotProduct] using this

omit [Fintype I] in
/-- `E[w(Mv)'] = E[wv']M'`. -/
theorem kf_mom_app_right {v : Ω → J → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hw : kf_L2 μ w)
    (M : Matrix I J ℝ) : var_mom μ w (kf_app M v) = var_mom μ w v * Mᵀ := by
  rw [kf_mom_transpose, kf_mom_app_left hv hw, transpose_mul, ← kf_mom_transpose]

omit [Fintype I] [Fintype J] in
theorem kf_mom_add_left {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hv' : kf_L2 μ v')
    (hw : kf_L2 μ w) : var_mom μ (v + v') w = var_mom μ v w + var_mom μ v' w := by
  ext i k
  simp only [var_mom, of_apply, Pi.add_apply, add_mul, Matrix.add_apply]
  exact integral_add ((hv i).integrable_mul (hw k)) ((hv' i).integrable_mul (hw k))

omit [Fintype I] [Fintype J] in
theorem kf_mom_sub_left {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v) (hv' : kf_L2 μ v')
    (hw : kf_L2 μ w) : var_mom μ (v - v') w = var_mom μ v w - var_mom μ v' w := by
  ext i k
  simp only [var_mom, of_apply, Pi.sub_apply, sub_mul, Matrix.sub_apply]
  exact integral_sub ((hv i).integrable_mul (hw k)) ((hv' i).integrable_mul (hw k))

omit [Fintype I] [Fintype J] in
theorem kf_mom_add_right {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v)
    (hv' : kf_L2 μ v') (hw : kf_L2 μ w) :
    var_mom μ w (v + v') = var_mom μ w v + var_mom μ w v' := by
  rw [kf_mom_transpose, kf_mom_add_left hv hv' hw, transpose_add, ← kf_mom_transpose,
    ← kf_mom_transpose]

omit [Fintype I] [Fintype J] in
theorem kf_mom_sub_right {v v' : Ω → I → ℝ} {w : Ω → K → ℝ} (hv : kf_L2 μ v)
    (hv' : kf_L2 μ v') (hw : kf_L2 μ w) :
    var_mom μ w (v - v') = var_mom μ w v - var_mom μ w v' := by
  rw [kf_mom_transpose, kf_mom_sub_left hv hv' hw, transpose_sub, ← kf_mom_transpose,
    ← kf_mom_transpose]

omit [Fintype I] [Fintype J] in
/-- `E[c w'] = c (Ew)'` for a constant vector `c`. -/
theorem kf_mom_const_left (c : I → ℝ) (w : Ω → K → ℝ) :
    var_mom μ (fun _ => c) w = Matrix.of fun i k => c i * kf_mean μ w k := by
  ext i k
  simp only [var_mom, of_apply, kf_mean, integral_const_mul]

omit [Fintype I] in
/-- `E(Mv) = M Ev`. -/
theorem kf_mean_app {v : Ω → J → ℝ} (hv : kf_L2 μ v) [IsFiniteMeasure μ]
    (M : Matrix I J ℝ) : kf_mean μ (kf_app M v) = M *ᵥ kf_mean μ v := by
  funext i
  simp only [kf_app, kf_mean, mulVec, dotProduct]
  rw [integral_finsetSum _ fun j _ => ((hv j).integrable one_le_two).const_mul _]
  simp only [integral_const_mul]

omit [Fintype I] [Fintype J] in
theorem kf_mean_add {v w : Ω → I → ℝ} [IsFiniteMeasure μ] (hv : kf_L2 μ v) (hw : kf_L2 μ w) :
    kf_mean μ (v + w) = kf_mean μ v + kf_mean μ w := by
  funext i
  exact integral_add ((hv i).integrable one_le_two) ((hw i).integrable one_le_two)

omit [Fintype I] [Fintype J] in
theorem kf_mean_sub {v w : Ω → I → ℝ} [IsFiniteMeasure μ] (hv : kf_L2 μ v) (hw : kf_L2 μ w) :
    kf_mean μ (v - w) = kf_mean μ v - kf_mean μ w := by
  funext i
  exact integral_sub ((hv i).integrable one_le_two) ((hw i).integrable one_le_two)

omit [Fintype I] in
theorem kf_app_add (M : Matrix I J ℝ) (v w : Ω → J → ℝ) :
    kf_app M (v + w) = kf_app M v + kf_app M w := by
  funext ω
  simp [kf_app, mulVec_add]

omit [Fintype I] in
theorem kf_app_sub (M : Matrix I J ℝ) (v w : Ω → J → ℝ) :
    kf_app M (v - w) = kf_app M v - kf_app M w := by
  funext ω
  simp [kf_app, mulVec_sub]

omit [Fintype I] in
theorem kf_app_app [Fintype K] (M : Matrix I J ℝ) (N : Matrix J K ℝ) (v : Ω → K → ℝ) :
    kf_app M (kf_app N v) = kf_app (M * N) v := by
  funext ω
  simp [kf_app, mulVec_mulVec]

omit [Fintype I] in
theorem kf_app_zero_mat (v : Ω → J → ℝ) : kf_app (0 : Matrix I J ℝ) v = 0 := by
  funext ω
  simp [kf_app]

omit [Fintype I] in
theorem kf_app_sub_mat (M N : Matrix I J ℝ) (v : Ω → J → ℝ) :
    kf_app (M - N) v = kf_app M v - kf_app N v := by
  funext ω
  simp [kf_app, sub_mulVec]

omit [Fintype I] [Fintype J] in
/-- `E[v c'] = (Ev) c'` for a constant vector `c`. -/
theorem kf_mom_const_right (v : Ω → I → ℝ) (c : K → ℝ) :
    var_mom μ v (fun _ => c) = Matrix.of fun i k => kf_mean μ v i * c k := by
  ext i k
  simp only [var_mom, of_apply, kf_mean, integral_mul_const]

omit [Fintype I] [Fintype J] in
theorem kf_mean_const [IsProbabilityMeasure μ] (c : I → ℝ) : kf_mean μ (fun _ : Ω => c) = c := by
  funext i
  simp [kf_mean]

omit [Fintype I] [Fintype J] in
/-- `E[(Ge + Dc)w'] = G E[ew'] + D E[cw']`. -/
theorem kf_mom_lin2 {L : Type*} [Fintype K] [Fintype L] {e : Ω → K → ℝ} {c : Ω → L → ℝ}
    {Z : Type*} {w : Ω → Z → ℝ} (he : kf_L2 μ e) (hc : kf_L2 μ c) (hw : kf_L2 μ w)
    (G : Matrix I K ℝ) (D : Matrix I L ℝ) :
    var_mom μ (kf_app G e + kf_app D c) w = G * var_mom μ e w + D * var_mom μ c w := by
  rw [kf_mom_add_left (kf_L2_app he G) (kf_L2_app hc D) hw, kf_mom_app_left he hw,
    kf_mom_app_left hc hw]

omit [Fintype I] in
/-- `E[(e − Ka)w'] = E[ew'] − K E[aw']`. -/
theorem kf_mom_lin_sub {e : Ω → I → ℝ} {a : Ω → J → ℝ} {Z : Type*} {w : Ω → Z → ℝ}
    (he : kf_L2 μ e) (ha : kf_L2 μ a) (hw : kf_L2 μ w) (K : Matrix I J ℝ) :
    var_mom μ (e - kf_app K a) w = var_mom μ e w - K * var_mom μ a w := by
  rw [kf_mom_sub_left he (kf_L2_app ha K) hw, kf_mom_app_left ha hw]

omit [Fintype I] [Fintype J] in
/-- A second-moment matrix `E[vv']` is positive semidefinite. -/
theorem kf_mom_self_psd [Finite I] {v : Ω → I → ℝ} (hv : kf_L2 μ v) :
    (var_mom μ v v).PosSemidef := by
  have := Fintype.ofFinite I
  refine SS.LQProblem.posSemidef_iff_real.2 ⟨by rw [← kf_mom_transpose], fun z => ?_⟩
  set M : Matrix Unit I ℝ := Matrix.of fun _ i => z i
  have h := kf_mom_app_right hv (kf_L2_app hv M) M
  rw [kf_mom_app_left hv hv M] at h
  have h1 := congrFun (congrFun h ()) ()
  have hq : (M * var_mom μ v v * Mᵀ) () () = z ⬝ᵥ (var_mom μ v v *ᵥ z) := by
    simp only [M, mul_apply, transpose_apply, of_apply, dotProduct, mulVec, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [← hq, ← h1]
  exact integral_nonneg fun ω => mul_self_nonneg _

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Kalman filter: the covariance algebra of one updating step

Miao, §10.1.1, pp. 329–333: the matrix algebra of one step of the Kalman filter. Fix the date-`t`
matrices `G = G_t`, `D = D_t`, the predicted covariance `P = Σ_{t|t−1}` and the cross covariance
`Cℓ = E[(x_t − x̂_{t|t−1})ε_t']` (by (10.9) this is the shock loading of `ε_t` in `x_t`; see
`KFFilter`). Then

* (10.8) `Ω = GPG' + DD' + GCℓD' + DCℓ'G'` (`kf_Om`), the innovation covariance;
* `M = PG' + CℓD'` (`kf_Mx`), the covariance of the state and the innovation (p. 332);
* (10.10) `K = MΩ⁻¹` (`kf_gain`), the Kalman gain;
* (10.11) `Σ(K) = (I − KG)P(I − KG)' + KDD'K' − (I − KG)CℓD'K' − KDCℓ'(I − KG)'`
  (`kf_joseph`), the covariance of `x_t − x̂_{t|t−1} − Ka_t` for an arbitrary gain `K`;
* `Σ_{t|t} = (I − KG)P − KDCℓ'` (`kf_filtCov`), the book's simplified form at the Kalman gain.

Main results:

* `kf_joseph_expand`: `Σ(K) = P − KM' − MK' + KΩK'`;
* `kf_joseph_complete`: completing the square,
  `Σ(K) = P − MΩ⁻¹M' + (K − K*)Ω(K − K*)'` with `K* = MΩ⁻¹`;
* `eq_10_10`: if `Ω > 0`, the Kalman gain minimises `Σ(K)` in the Loewner order and
  `tr Σ(K)` (the book's criterion `E(x_t − x̂_{t|t})'(x_t − x̂_{t|t})`), uniquely;
  `eq_10_10_foc`: the first-order condition of p. 331 (`kf_trace_perturb` is the expansion of
  `tr Σ(K + sΔ)` whose linear term is the derivative), `KΩ = M`;
* `eq_10_11_gain`: at the Kalman gain (10.11) reduces to `Σ_{t|t} = (I − KG)P − KDCℓ'`;
* `kf_riccati_pred`: the Riccati form of `Σ_{t+1|t} = AΣ_{t|t}A' + CC'` (p. 333).

Correction (p. 331): the printed first-order condition
`0 = −2(ΣG' + DC') + 2K(GΣG' + DD' + GCD' + DC'G)` has the non-conformable terms `DC'` and
`DC'G`; the derivative is `−2(ΣG' + CD') + 2K(GΣG' + DD' + GCD' + DC'G')` (`kf_trace_perturb`).
-/

open Matrix

open scoped MatrixOrder

namespace Miao.PartialInformation

variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y]

/-- (10.8) (Miao, p. 330): the innovation covariance `Ω = GPG' + DD' + GCℓD' + DCℓ'G'`. -/
def kf_Om (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Matrix Y Y ℝ :=
  G * P * Gᵀ + D * Dᵀ + G * Cl * Dᵀ + D * Clᵀ * Gᵀ

/-- Miao, p. 332: `Cov(x_t, y_t | y^{t−1}) = PG' + CℓD'`. -/
def kf_Mx (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) (P : Matrix X X ℝ) :
    Matrix X Y ℝ :=
  P * Gᵀ + Cl * Dᵀ

/-- (10.10) (Miao, p. 330): the Kalman gain `K = (PG' + CℓD')Ω⁻¹`. -/
noncomputable def kf_gain (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ)
    (P : Matrix X X ℝ) : Matrix X Y ℝ :=
  kf_Mx G D Cl P * (kf_Om G D Cl P)⁻¹

/-- (10.11) (Miao, p. 331): the error covariance for an arbitrary gain `K`. -/
def kf_joseph (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) (P : Matrix X X ℝ)
    (K : Matrix X Y ℝ) : Matrix X X ℝ :=
  (1 - K * G) * P * (1 - K * G)ᵀ + K * D * Dᵀ * Kᵀ - (1 - K * G) * Cl * Dᵀ * Kᵀ -
    K * D * Clᵀ * (1 - K * G)ᵀ

/-- Miao, p. 332: `Σ_{t|t} = (I − KG)Σ_{t|t−1} − KDCℓ'` at the Kalman gain. -/
noncomputable def kf_filtCov (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ)
    (P : Matrix X X ℝ) : Matrix X X ℝ :=
  (1 - kf_gain G D Cl P * G) * P - kf_gain G D Cl P * D * Clᵀ

variable (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (Cl : Matrix X E ℝ) {P : Matrix X X ℝ}

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- `Ω' = Ω` for symmetric `P`. -/
theorem kf_Om_transpose (hP : Pᵀ = P) : (kf_Om G D Cl P)ᵀ = kf_Om G D Cl P := by
  simp only [kf_Om, transpose_add, transpose_mul, transpose_transpose, hP, Matrix.mul_assoc]
  abel

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- `M' = GP + DCℓ'` for symmetric `P`. -/
theorem kf_Mx_transpose (hP : Pᵀ = P) : (kf_Mx G D Cl P)ᵀ = G * P + D * Clᵀ := by
  simp only [kf_Mx, transpose_add, transpose_mul, transpose_transpose, hP]

omit [DecidableEq Y] in
/-- (10.11) expanded: `Σ(K) = P − KM' − MK' + KΩK'`. -/
theorem kf_joseph_expand (hP : Pᵀ = P) (K : Matrix X Y ℝ) :
    kf_joseph G D Cl P K = P - K * (kf_Mx G D Cl P)ᵀ - kf_Mx G D Cl P * Kᵀ +
      K * kf_Om G D Cl P * Kᵀ := by
  rw [kf_Mx_transpose G D Cl hP]
  simp only [kf_joseph, kf_Mx, kf_Om, transpose_sub, transpose_one, transpose_mul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- Completing the square in (10.11): `Σ(K) = P − MΩ⁻¹M' + (K − K*)Ω(K − K*)'`, `K* = MΩ⁻¹`. -/
theorem kf_joseph_complete (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det)
    (K : Matrix X Y ℝ) :
    kf_joseph G D Cl P K = P - kf_Mx G D Cl P * (kf_Om G D Cl P)⁻¹ * (kf_Mx G D Cl P)ᵀ +
      (K - kf_gain G D Cl P) * kf_Om G D Cl P * (K - kf_gain G D Cl P)ᵀ := by
  rw [kf_joseph_expand G D Cl hP]
  have hs : ((kf_Om G D Cl P)⁻¹)ᵀ = (kf_Om G D Cl P)⁻¹ := by
    rw [transpose_nonsing_inv, kf_Om_transpose G D Cl hP]
  simp only [kf_gain, transpose_sub, transpose_mul, hs, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu, nonsing_inv_mul_cancel_left _ _ hu]
  abel

/-- (10.11) at the Kalman gain (Miao, p. 332): `Σ(K*) = (I − K*G)P − K*DCℓ'`. -/
theorem eq_10_11_gain (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det) :
    kf_joseph G D Cl P (kf_gain G D Cl P) = kf_filtCov G D Cl P := by
  rw [kf_joseph_complete G D Cl hP hu]
  simp only [sub_self, Matrix.zero_mul, add_zero]
  simp only [kf_filtCov, kf_gain, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [kf_Mx_transpose G D Cl hP]
  simp only [Matrix.mul_add]
  abel

/-- `Σ_{t|t} = P − MΩ⁻¹M'`. -/
theorem kf_filtCov_eq (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det) :
    kf_filtCov G D Cl P =
      P - kf_Mx G D Cl P * (kf_Om G D Cl P)⁻¹ * (kf_Mx G D Cl P)ᵀ := by
  rw [← eq_10_11_gain G D Cl hP hu, kf_joseph_complete G D Cl hP hu]
  simp only [sub_self, Matrix.zero_mul, add_zero]

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in
/-- `(NΩN')ᵢᵢ = Nᵢ'ΩNᵢ` (row `i` of `N`). -/
theorem kf_diag_sandwich {Z : Type*} (N : Matrix X Z ℝ) [Fintype Z] (W : Matrix Z Z ℝ) (i : X) :
    (N * W * Nᵀ) i i = N i ⬝ᵥ (W *ᵥ N i) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [DecidableEq X] [DecidableEq Y] in
/-- `tr(NΩN') ≥ 0` for `Ω > 0`, with equality iff `N = 0`. -/
theorem kf_trace_sandwich {Z : Type*} [Fintype Z] {W : Matrix Z Z ℝ} (hW : W.PosDef)
    (N : Matrix X Z ℝ) : 0 ≤ trace (N * W * Nᵀ) ∧ (trace (N * W * Nᵀ) = 0 ↔ N = 0) := by
  have hW' := SS.LQProblem.posDef_iff_real.1 hW
  have hnn : ∀ i, 0 ≤ N i ⬝ᵥ (W *ᵥ N i) := by
    intro i
    rcases eq_or_ne (N i) 0 with h | h
    · simp [h]
    · exact (hW'.2 h).le
  have htr : trace (N * W * Nᵀ) = ∑ i, N i ⬝ᵥ (W *ᵥ N i) := by
    simp only [trace, Matrix.diag, kf_diag_sandwich]
  rw [htr]
  refine ⟨Finset.sum_nonneg fun i _ => hnn i, ⟨fun h => ?_, fun h => ?_⟩⟩
  swap
  · have h0 : ∀ i, N i = 0 := fun i => by rw [h]; rfl
    simp [h0]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i] at h
  funext i
  by_contra hne
  have := hW'.2 hne
  rw [h i (Finset.mem_univ i)] at this
  exact lt_irrefl _ this

/-- **(10.10)** (Miao, p. 330): if `Ω > 0`, the Kalman gain `K* = (PG' + CℓD')Ω⁻¹` minimises the
error covariance (10.11) over all gains, in the Loewner order and in trace (the book's criterion
`E(x_t − x̂_{t|t})'(x_t − x̂_{t|t}) = tr Σ_{t|t}`), and is the unique trace minimiser. -/
theorem eq_10_10 (hP : Pᵀ = P) (hΩ : (kf_Om G D Cl P).PosDef) (K : Matrix X Y ℝ) :
    kf_filtCov G D Cl P ≤ kf_joseph G D Cl P K ∧
      trace (kf_filtCov G D Cl P) ≤ trace (kf_joseph G D Cl P K) ∧
      (trace (kf_joseph G D Cl P K) = trace (kf_filtCov G D Cl P) ↔ K = kf_gain G D Cl P) := by
  have hu : IsUnit (kf_Om G D Cl P).det := (isUnit_iff_isUnit_det _).1 hΩ.isUnit
  have hJ := kf_joseph_complete G D Cl hP hu K
  rw [kf_filtCov_eq G D Cl hP hu]
  set N := K - kf_gain G D Cl P
  have hpsd : (N * kf_Om G D Cl P * Nᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hΩ.posSemidef.mul_mul_conjTranspose_same N
  obtain ⟨h0, hiff⟩ := kf_trace_sandwich hΩ N
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.le_iff, hJ, add_sub_cancel_left]
    exact hpsd
  · rw [hJ, trace_add]
    linarith
  · rw [hJ, trace_add, add_eq_left, hiff, sub_eq_zero]

omit [DecidableEq Y] in
/-- The first-order expansion behind the trace condition of p. 331:
`tr Σ(K + sΔ) = tr Σ(K) + 2s tr(Δ(ΩK' − M')) + s² tr(ΔΩΔ')`; the derivative in `K` is
`2(KΩ − M)` (= `−2(PG' + CℓD') + 2KΩ`). -/
theorem kf_trace_perturb (hP : Pᵀ = P) (K Δ : Matrix X Y ℝ) (s : ℝ) :
    trace (kf_joseph G D Cl P (K + s • Δ)) = trace (kf_joseph G D Cl P K) +
      2 * s * trace (Δ * (kf_Om G D Cl P * Kᵀ - (kf_Mx G D Cl P)ᵀ)) +
      s ^ 2 * trace (Δ * kf_Om G D Cl P * Δᵀ) := by
  rw [kf_joseph_expand G D Cl hP, kf_joseph_expand G D Cl hP]
  set Om := kf_Om G D Cl P
  set M := kf_Mx G D Cl P
  have hOm : Omᵀ = Om := kf_Om_transpose G D Cl hP
  have t1 : trace (M * Δᵀ) = trace (Δ * Mᵀ) := by
    rw [← trace_transpose, transpose_mul, transpose_transpose]
  have t2 : trace (K * Om * Δᵀ) = trace (Δ * (Om * Kᵀ)) := by
    rw [← trace_transpose, transpose_mul, transpose_mul, transpose_transpose, hOm]
  have t3 : trace (Δ * Om * Kᵀ) = trace (Δ * (Om * Kᵀ)) := by rw [Matrix.mul_assoc]
  simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, trace_add, trace_sub, trace_smul, smul_eq_mul, smul_add, Matrix.mul_sub,
    trace_sub] at *
  rw [t1, t2, t3]
  ring

omit [DecidableEq X] [DecidableEq Y] in
/-- The first-order condition of p. 331: the linear term of `tr Σ(K + sΔ)` vanishes for every
direction `Δ` iff `KΩ = PG' + CℓD'`; for invertible `Ω` this is (10.10), `K = MΩ⁻¹`. -/
theorem eq_10_10_foc (hP : Pᵀ = P) (K : Matrix X Y ℝ) :
    (∀ Δ : Matrix X Y ℝ, trace (Δ * (kf_Om G D Cl P * Kᵀ - (kf_Mx G D Cl P)ᵀ)) = 0) ↔
      K * kf_Om G D Cl P = kf_Mx G D Cl P := by
  set Om := kf_Om G D Cl P
  set M := kf_Mx G D Cl P
  have hOm : Omᵀ = Om := kf_Om_transpose G D Cl hP
  have key : K * Om = M ↔ Om * Kᵀ - Mᵀ = 0 := by
    rw [sub_eq_zero]
    constructor
    · intro h
      rw [← hOm, ← transpose_mul, h]
    · intro h
      rw [← transpose_transpose (K * Om), transpose_mul, hOm, h, transpose_transpose]
  rw [key]
  constructor
  · intro h
    have h0 := h (Om * Kᵀ - Mᵀ)ᵀ
    have := (trace_mul_conjTranspose_self_eq_zero_iff (A := (Om * Kᵀ - Mᵀ)ᵀ)).1
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
    exact transpose_eq_zero.1 (this h0)
  · intro h Δ
    rw [h, Matrix.mul_zero, trace_zero]

/-- The Riccati form of `Σ_{t+1|t} = AΣ_{t|t}A' + CC'` (Miao, p. 333):
`AΣ_{t|t}A' + CC' = APA' + CC' − A(GP + DCℓ')'Ω⁻¹(GP + DCℓ')A'`. -/
theorem kf_riccati_pred {E' : Type*} [Fintype E'] (A : Matrix X X ℝ) (C : Matrix X E' ℝ)
    (hP : Pᵀ = P) (hu : IsUnit (kf_Om G D Cl P).det) :
    A * kf_filtCov G D Cl P * Aᵀ + C * Cᵀ = A * P * Aᵀ + C * Cᵀ -
      A * (G * P + D * Clᵀ)ᵀ * (kf_Om G D Cl P)⁻¹ * (G * P + D * Clᵀ) * Aᵀ := by
  rw [kf_filtCov_eq G D Cl hP hu, ← kf_Mx_transpose G D Cl hP, transpose_transpose]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Kalman filter

Miao, §10.1.1, pp. 327–334. The linear state-space system (10.1)–(10.2)

* `x_{t+1} = A_tx_t + B_tu_t + C_tε_{t+1}` (state transition),
* `y_t = G_tx_t + H_{t−1}u_{t−1} + D_tε_t` (measurement)

with time-varying matrices (`KFSystem`), and the Kalman filter of Step 1–Step 3 (p. 332):
`x̂_{0|−1} = x̄₀`, `Σ_{0|−1} = Σ₀`, `a_t = y_t − G_tx̂_{t|t−1} − H_{t−1}u_{t−1}` (`innov`),
`x̂_{t|t} = x̂_{t|t−1} + K_ta_t` (10.7) (`xfilt`), `x̂_{t+1|t} = A_tx̂_{t|t} + B_tu_t` (`xpred`),
and
the deterministic covariance recursion `Σ_{t|t−1}` (`Spred`), `Ω_{t|t−1}` (`Om`), `K_t` (`K`),
`Σ_{t|t}` (`Sfilt`).

**Reading.** The filter is proved in its *linear-projection* (second-moment) version. The
probability space `(Ω, μ)` is arbitrary; the shocks are square integrable, mean zero, mutually
uncorrelated with `Eε_tε_t' = I`, and `x₀` has mean `x̄₀`, covariance `Σ₀` and is uncorrelated with
the shocks. No Gaussianity, no independence and no measurability of the controls is used: the
controls `u_t` and the measurement input (`h_t`, the book's `H_{t−1}u_{t−1}`, `inp`) are
arbitrary random vectors, because the estimation error does not depend on them
(`kf_err_control_free`). What is proved:

* the error recursion `x_{t+1} − x̂_{t+1|t} = A_t(x_t − x̂_{t|t}) + C_tε_{t+1}` with
  `a_t = G_t(x_t − x̂_{t|t−1}) + D_tε_t` (`kf_err_succ`, `kf_innov_eq`, (10.9) first line);
* `kf_moments`: `x_t − x̂_{t|t−1}` has mean zero and second moments `Σ_{t|t−1}`, and
  `E[(x_t − x̂_{t|t−1})ε_s'] = 0` for `s > t` and `= C_{t−1}` for `s = t` (10.9);
* (10.8) `Ea_ta_t' = Ω_{t|t−1}` (`eq_10_8`); `E(x_t − x̂_{t|t−1})a_t' = Σ_{t|t−1}G_t' + C_{t−1}D_t'`
  (`eq_10_12_cov`, the covariance in (10.12));
* (10.11) for an arbitrary gain (`eq_10_11`), the Kalman gain (10.10) is optimal
  (`eq_10_10_random`), and `E(x_t − x̂_{t|t})(x_t − x̂_{t|t})' = Σ_{t|t}` (`kf_filt_moments`);
* the projection property (10.12): the innovations have mean zero and are mutually uncorrelated
  (`kf_innov_orth`), the prediction error is orthogonal to all past innovations and the filtered
  error to all innovations up to `t` (`kf_err_orth`, `kf_filt_orth`), and
  `x̂_{t|t−1}` is the best predictor of `x_t` among all predictors `x̂_{t|t−1} + ∑_{s<t}L_sa_s + c`
  (`eq_10_12`): their error second moment is `Σ_{t|t−1} + ∑L_sΩ_sL_s' + cc'`.
* the fully recursive forms of p. 333 (`kf_pred_recursive`, `kf_filt_recursive`) and the Riccati
  equations (`kf_riccati_Spred`, `kf_riccati_Sfilt`).

**The Gaussian reading** (`x_t | F_t ∼ N(x̂_{t|t}, Σ_{t|t})`, innovations independent and
normal, conditional = unconditional covariances, p. 328 and p. 333) is not formalised; the
second-moment statements above are its content for the first two moments.

**Corrections.** (i) The cross covariance is `E[(x_t − x̂_{t|t−1})ε_t'] = C_{t−1}` (the loading of
`ε_t` in `x_t = A_{t−1}x_{t−1} + B_{t−1}u_{t−1} + C_{t−1}ε_t`), not `C_t` as printed in (10.9),
and it is `0` at `t = 0` (the initialisation `x₀ ∼ N(x̄₀, Σ₀)` is independent of `ε₀`). So the
`C_t` in (10.8), (10.10), (10.11), the formula for `Σ_{t|t}` and the Riccati equations of
p. 333 is `C_{t−1}` (`Cl t`), which matters when `C_t` varies or at `t = 0`
(`eq_10_9`; counterexample at `t = 0`: `kf_cross_book_false`). (ii) The simplification of
(10.11) to `Σ_{t|t} = (I − KG)Σ_{t|t−1} − KDC'` needs `Ω_{t|t−1}` invertible (assumed: `hΩ`).
-/

open MeasureTheory Matrix

open scoped MatrixOrder

namespace Miao.PartialInformation

/-- The state-space system (10.1)–(10.2) (Miao, pp. 327–328): `x_{t+1} = A_tx_t + B_tu_t +
C_tε_{t+1}`, `y_t = G_tx_t + H_{t−1}u_{t−1} + D_tε_t`, `x₀` with mean `x̄₀` and covariance `Σ₀`. -/
structure KFSystem (X U Y E : Type*) where
  /-- the state transition matrices `A_t` -/
  A : ℕ → Matrix X X ℝ
  /-- the control matrices `B_t` -/
  B : ℕ → Matrix X U ℝ
  /-- the state shock loadings `C_t` -/
  C : ℕ → Matrix X E ℝ
  /-- the measurement matrices `G_t` -/
  G : ℕ → Matrix Y X ℝ
  /-- the measurement control matrices `H_t` -/
  H : ℕ → Matrix Y U ℝ
  /-- the measurement shock loadings `D_t` -/
  D : ℕ → Matrix Y E ℝ
  /-- the mean `x̄₀` of `x₀` -/
  xbar0 : X → ℝ
  /-- the covariance `Σ₀` of `x₀` -/
  S0 : Matrix X X ℝ

namespace KFSystem

variable {X U Y E : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X]
  [DecidableEq Y] (S : KFSystem X U Y E)

/-- The cross covariance `E[(x_t − x̂_{t|t−1})ε_t']`: `0` at `t = 0`, `C_{t−1}` for `t ≥ 1`
(the book's (10.9), corrected). -/
def Cl : ℕ → Matrix X E ℝ
  | 0 => 0
  | t + 1 => S.C t

/-- The predicted covariances `Σ_{t|t−1}` (Step 1–Step 3, Miao, pp. 332–333): `Σ_{0|−1} = Σ₀`,
`Σ_{t+1|t} = A_tΣ_{t|t}A_t' + C_tC_t'`. -/
noncomputable def Spred : ℕ → Matrix X X ℝ
  | 0 => S.S0
  | t + 1 => S.A t * kf_filtCov (S.G t) (S.D t) (S.Cl t) (Spred t) * (S.A t)ᵀ + S.C t * (S.C t)ᵀ

/-- (10.8): `Ω_{t|t−1}`. -/
noncomputable def Om (t : ℕ) : Matrix Y Y ℝ := kf_Om (S.G t) (S.D t) (S.Cl t) (S.Spred t)

/-- (10.10): the Kalman gain `K_t`. -/
noncomputable def K (t : ℕ) : Matrix X Y ℝ := kf_gain (S.G t) (S.D t) (S.Cl t) (S.Spred t)

/-- The filtered covariance `Σ_{t|t} = (I − K_tG_t)Σ_{t|t−1} − K_tD_tC_{t−1}'`. -/
noncomputable def Sfilt (t : ℕ) : Matrix X X ℝ :=
  kf_filtCov (S.G t) (S.D t) (S.Cl t) (S.Spred t)

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The measurement input of (10.2): `0` at `t = 0`, `H_{t−1}u_{t−1}` for `t ≥ 1`. -/
def inp (u : ℕ → Ω → U → ℝ) : ℕ → Ω → Y → ℝ
  | 0 => 0
  | t + 1 => kf_app (S.H t) (u t)

/-- The predictions `x̂_{t|t−1}` computed from the observations `y`, the known measurement input
`h` and the controls `u` (Step 1–Step 3, Miao, pp. 332–333). -/
noncomputable def xpred (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) : ℕ → Ω → X → ℝ
  | 0 => fun _ => S.xbar0
  | t + 1 => kf_app (S.A t) (xpred y h u t + kf_app (S.K t)
      (y t - kf_app (S.G t) (xpred y h u t) - h t)) + kf_app (S.B t) (u t)

/-- The innovation `a_t = y_t − ŷ_{t|t−1}`, `ŷ_{t|t−1} = G_tx̂_{t|t−1} + h_t`. -/
noncomputable def innov (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) : Ω → Y → ℝ :=
  y t - kf_app (S.G t) (S.xpred y h u t) - h t

/-- (10.7): the filtered estimate `x̂_{t|t} = x̂_{t|t−1} + K_ta_t`. -/
noncomputable def xfilt (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) : Ω → X → ℝ :=
  S.xpred y h u t + kf_app (S.K t) (S.innov y h u t)

/-- The prediction error `x_t − x̂_{t|t−1}`. -/
noncomputable def err (x : ℕ → Ω → X → ℝ) (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) :
    Ω → X → ℝ :=
  x t - S.xpred y h u t

/-- Miao, p. 330: `x̂_{t+1|t} = A_tx̂_{t|t} + B_tu_t`. -/
theorem xpred_succ (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) :
    S.xpred y h u (t + 1) = kf_app (S.A t) (S.xfilt y h u t) + kf_app (S.B t) (u t) := rfl

variable {x : ℕ → Ω → X → ℝ} {y h : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ} {ε : ℕ → Ω → E → ℝ}

/-- The innovation in terms of the error (Miao, p. 330): `a_t = G_t(x_t − x̂_{t|t−1}) + D_tε_t`. -/
theorem kf_innov_eq (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
    (t : ℕ) : S.innov y h u t = kf_app (S.G t) (S.err x y h u t) + kf_app (S.D t) (ε t) := by
  rw [innov, hy, err, kf_app_sub]
  abel

/-- The error recursion (Miao, pp. 330 and 344): `x_{t+1} − x̂_{t+1|t} =
A_t(x_t − x̂_{t|t}) + C_tε_{t+1}`, with `x_t − x̂_{t|t} = (x_t − x̂_{t|t−1}) − K_ta_t`. -/
theorem kf_err_succ
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1))) (t : ℕ) :
    S.err x y h u (t + 1) = kf_app (S.A t) (S.err x y h u t - kf_app (S.K t) (S.innov y h u t)) +
      kf_app (S.C t) (ε (t + 1)) := by
  rw [err, hx, xpred_succ, xfilt, err, kf_app_sub, kf_app_sub, kf_app_add]
  abel

theorem err_zero : S.err x y h u 0 = x 0 - fun _ => S.xbar0 := rfl

/-- Miao, p. 344: the estimation error does not depend on the controls (nor on the known
measurement input). Two control sequences `u, u'` with the same `x₀` and shocks give the same
prediction errors and the same innovations. -/
theorem kf_err_control_free {x' : ℕ → Ω → X → ℝ} {y' h' : ℕ → Ω → Y → ℝ} {u' : ℕ → Ω → U → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1)))
    (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
    (hx' : ∀ t, x' (t + 1) = kf_app (S.A t) (x' t) + kf_app (S.B t) (u' t) +
      kf_app (S.C t) (ε (t + 1)))
    (hy' : ∀ t, y' t = kf_app (S.G t) (x' t) + h' t + kf_app (S.D t) (ε t))
    (h0 : x' 0 = x 0) (t : ℕ) :
    S.err x' y' h' u' t = S.err x y h u t ∧ S.innov y' h' u' t = S.innov y h u t := by
  have he : ∀ t, S.err x' y' h' u' t = S.err x y h u t := by
    intro t
    induction t with
    | zero => rw [err_zero, err_zero, h0]
    | succ t ih =>
      rw [S.kf_err_succ hx', S.kf_err_succ hx, S.kf_innov_eq hy', S.kf_innov_eq hy, ih]
  exact ⟨he t, by rw [S.kf_innov_eq hy', S.kf_innov_eq hy, he t]⟩

/-! ### Second moments -/

variable {μ : Measure Ω}

omit [Fintype U] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- One updating step in second moments. Let `e` (the prediction error), `c` (the current shock)
and `n` (the next shock) be square integrable with `Eee' = P`, `Eec' = Cℓ`, `Ecc' = Enn' = I`,
`Een' = Ecn' = 0`; let `a = Ge + Dc` and `f = e − Ka`. Then `Eaa' = Ω` (10.8), `Eea' = PG' + CℓD'`,
`Eff' = Σ(K)` (10.11), and `e' = Af + Cn` has `Ee'e' = AΣ(K)A' + CC'` and `Ee'n' = C`. -/
theorem kf_step {W : Type*} [Fintype W] [DecidableEq E] {e : Ω → X → ℝ}
    {c n : Ω → E → ℝ} {a : Ω → W → ℝ} {f : Ω → X → ℝ} (he : kf_L2 μ e) (hc : kf_L2 μ c)
    (hn : kf_L2 μ n) [DecidableEq X] (G : Matrix W X ℝ) (D : Matrix W E ℝ)
    (Cl : Matrix X E ℝ) (K : Matrix X W ℝ) (A : Matrix X X ℝ) (C : Matrix X E ℝ)
    {P : Matrix X X ℝ} (ha : a = kf_app G e + kf_app D c) (hf : f = e - kf_app K a)
    (hee : var_mom μ e e = P) (hec : var_mom μ e c = Cl) (hcc : var_mom μ c c = 1)
    (hen : var_mom μ e n = 0) (hcn : var_mom μ c n = 0) (hnn : var_mom μ n n = 1) :
    var_mom μ a a = kf_Om G D Cl P ∧ var_mom μ e a = kf_Mx G D Cl P ∧
      var_mom μ f a = kf_Mx G D Cl P - K * kf_Om G D Cl P ∧
      var_mom μ f f = kf_joseph G D Cl P K ∧
      var_mom μ (kf_app A f + kf_app C n) (kf_app A f + kf_app C n) =
        A * kf_joseph G D Cl P K * Aᵀ + C * Cᵀ ∧
      var_mom μ (kf_app A f + kf_app C n) n = C ∧ var_mom μ f n = 0 := by
  subst ha hf
  set a := kf_app G e + kf_app D c with ha
  set f := e - kf_app K a with hf
  have hP : Pᵀ = P := by rw [← hee, ← kf_mom_transpose]
  have ha2 : kf_L2 μ a := kf_L2_add (kf_L2_app he G) (kf_L2_app hc D)
  have hf2 : kf_L2 μ f := kf_L2_sub he (kf_L2_app ha2 K)
  have hce : var_mom μ c e = Clᵀ := by rw [kf_mom_transpose, hec]
  have hae : var_mom μ a e = G * P + D * Clᵀ := by rw [kf_mom_lin2 he hc he, hee, hce]
  have hac : var_mom μ a c = G * Cl + D := by rw [kf_mom_lin2 he hc hc, hec, hcc, Matrix.mul_one]
  have hea : var_mom μ e a = kf_Mx G D Cl P := by
    rw [kf_mom_transpose, hae, ← kf_Mx_transpose G D Cl hP, transpose_transpose]
  have haa : var_mom μ a a = kf_Om G D Cl P := by
    rw [kf_mom_lin2 he hc ha2, hea, kf_mom_transpose, hac]
    simp only [kf_Om, kf_Mx, transpose_add, transpose_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  have hfa : var_mom μ f a = kf_Mx G D Cl P - K * kf_Om G D Cl P := by
    rw [kf_mom_lin_sub he ha2 ha2, hea, haa]
  have hfe : var_mom μ f e = P - K * (kf_Mx G D Cl P)ᵀ := by
    rw [kf_mom_lin_sub he ha2 he, hee, hae, kf_Mx_transpose G D Cl hP]
  have hff : var_mom μ f f = kf_joseph G D Cl P K := by
    rw [kf_mom_lin_sub he ha2 hf2, kf_mom_transpose f e, hfe, kf_mom_transpose f a, hfa,
      kf_joseph_expand G D Cl hP]
    simp only [transpose_sub, transpose_mul, hP, transpose_transpose, Matrix.mul_sub,
      kf_Om_transpose G D Cl hP, Matrix.mul_assoc]
    abel
  have han : var_mom μ a n = 0 := by
    rw [kf_mom_lin2 he hc hn, hen, hcn, Matrix.mul_zero, Matrix.mul_zero,
      add_zero]
  have hfn : var_mom μ f n = 0 := by
    rw [kf_mom_lin_sub he ha2 hn, hen, han, Matrix.mul_zero, sub_zero]
  have hAf := kf_L2_app hf2 A
  have hCn := kf_L2_app hn C
  have hn' : var_mom μ (kf_app A f + kf_app C n) n = C := by
    rw [kf_mom_add_left hAf hCn hn, kf_mom_app_left hf2 hn, kf_mom_app_left hn hn, hfn, hnn,
      Matrix.mul_zero, zero_add, Matrix.mul_one]
  have hef : var_mom μ (kf_app A f + kf_app C n) f = A * kf_joseph G D Cl P K := by
    rw [kf_mom_add_left hAf hCn hf2, kf_mom_app_left hf2 hf2, kf_mom_app_left hn hf2, hff,
      kf_mom_transpose f n, hfn, transpose_zero, Matrix.mul_zero, add_zero]
  have hJ : (kf_joseph G D Cl P K)ᵀ = kf_joseph G D Cl P K := by
    rw [← hff, ← kf_mom_transpose]
  refine ⟨haa, hea, hfa, hff, ?_, hn', hfn⟩
  rw [kf_mom_add_left hAf hCn (kf_L2_add hAf hCn), kf_mom_app_left hf2 (kf_L2_add hAf hCn),
    kf_mom_app_left hn (kf_L2_add hAf hCn), kf_mom_transpose (kf_app A f + kf_app C n) f, hef,
    kf_mom_transpose (kf_app A f + kf_app C n) n, hn',
    transpose_mul, hJ, Matrix.mul_assoc]

variable (μ)

/-- The prediction errors and their second moments (Miao, pp. 330–333). Under (10.1)–(10.2),
for every `t`: `x_t − x̂_{t|t−1}` is square integrable with mean zero, its second-moment matrix is
`Σ_{t|t−1}`, and (10.9) `E[(x_t − x̂_{t|t−1})ε_s'] = C_{t−1}` for `s = t` (`0` at `t = 0`) and
`= 0` for `s > t`. -/
theorem kf_moments [IsProbabilityMeasure μ] [DecidableEq E]
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1)))
    (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = S.xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => S.xbar0) (x 0 - fun _ => S.xbar0) = S.S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => S.xbar0) (ε t) = 0)
    (hΩ : ∀ t, IsUnit (S.Om t).det) (t : ℕ) :
    kf_L2 μ (S.err x y h u t) ∧ kf_mean μ (S.err x y h u t) = 0 ∧
      var_mom μ (S.err x y h u t) (S.err x y h u t) = S.Spred t ∧
      ∀ s, t ≤ s → var_mom μ (S.err x y h u t) (ε s) = if s = t then S.Cl t else 0 := by
  induction t with
  | zero =>
    rw [err_zero]
    refine ⟨kf_L2_sub hL0 (kf_L2_const _), ?_, hS0, fun s _ => ?_⟩
    · rw [kf_mean_sub hL0 (kf_L2_const _), hm0, kf_mean_const, sub_self]
    · rw [h0ε]
      split_ifs <;> rfl
  | succ t ih =>
    obtain ⟨he, hme, hee, hes⟩ := ih
    have hεs : ∀ s, t + 1 ≤ s → var_mom μ (ε t) (ε s) = 0 := by
      intro s hs
      rw [hεε]
      simp only [ite_eq_right_iff]
      intro h
      omega
    have hes' : ∀ s, t + 1 ≤ s → var_mom μ (S.err x y h u t) (ε s) = 0 := by
      intro s hs
      rw [hes s (by omega)]
      simp only [ite_eq_right_iff]
      intro h
      omega
    obtain ⟨-, -, -, -, hmom, hcn, hfn⟩ := kf_step (μ := μ) he (hLε t) (hLε (t + 1)) (S.G t)
      (S.D t) (S.Cl t) (S.K t) (S.A t) (S.C t) (S.kf_innov_eq hy t) rfl hee
      (by rw [hes t le_rfl]; simp) (by rw [hεε]; simp) (hes' _ le_rfl)
      (hεs _ le_rfl) (by rw [hεε]; simp)
    have ha2 : kf_L2 μ (S.innov y h u t) := by
      rw [S.kf_innov_eq hy]; exact kf_L2_add (kf_L2_app he _) (kf_L2_app (hLε t) _)
    have hf2 : kf_L2 μ (S.err x y h u t - kf_app (S.K t) (S.innov y h u t)) :=
      kf_L2_sub he (kf_L2_app ha2 _)
    rw [S.kf_err_succ hx]
    refine ⟨kf_L2_add (kf_L2_app hf2 _) (kf_L2_app (hLε _) _), ?_, ?_, fun s hs => ?_⟩
    · rw [kf_mean_add (kf_L2_app hf2 _) (kf_L2_app (hLε _) _), kf_mean_app hf2,
        kf_mean_app (hLε _), kf_mean_sub he (kf_L2_app ha2 _), kf_mean_app ha2,
        S.kf_innov_eq hy, kf_mean_add (kf_L2_app he _) (kf_L2_app (hLε _) _), kf_mean_app he,
        kf_mean_app (hLε _), hme, hmε, hmε]
      simp
    · have hPs : (S.Spred t)ᵀ = S.Spred t := by rw [← hee, ← kf_mom_transpose]
      rw [hmom, show S.K t = kf_gain (S.G t) (S.D t) (S.Cl t) (S.Spred t) from rfl,
        eq_10_11_gain (P := S.Spred t) _ _ _ hPs (hΩ t)]
      rfl
    · rcases eq_or_lt_of_le hs with hst | hst
      · subst hst
        rw [hcn]
        simp only [↓reduceIte]
        rfl
      · have hfs : var_mom μ (S.err x y h u t - kf_app (S.K t) (S.innov y h u t)) (ε s) = 0 := by
          rw [kf_mom_sub_left he (kf_L2_app ha2 _) (hLε s), kf_mom_app_left ha2 (hLε s),
            S.kf_innov_eq hy, kf_mom_add_left (kf_L2_app he _) (kf_L2_app (hLε t) _) (hLε s),
            kf_mom_app_left he (hLε s), kf_mom_app_left (hLε t) (hLε s), hes' s (by omega),
            hεs s (by omega)]
          simp
        rw [kf_mom_add_left (kf_L2_app hf2 _) (kf_L2_app (hLε _) _) (hLε s),
          kf_mom_app_left hf2 (hLε s), kf_mom_app_left (hLε _) (hLε s), hfs, hεε]
        have h1 : t + 1 ≠ s := by omega
        have h2 : s ≠ t + 1 := by omega
        simp [h1, h2]

/-! ### Consequences under the model hypotheses -/

variable [IsProbabilityMeasure μ] [DecidableEq E]
  (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
    kf_app (S.C t) (ε (t + 1)))
  (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
  (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = S.xbar0)
  (hmε : ∀ t, kf_mean μ (ε t) = 0)
  (hS0 : var_mom μ (x 0 - fun _ => S.xbar0) (x 0 - fun _ => S.xbar0) = S.S0)
  (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
  (h0ε : ∀ t, var_mom μ (x 0 - fun _ => S.xbar0) (ε t) = 0)
  (hΩ : ∀ t, IsUnit (S.Om t).det)

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The innovations are square integrable with mean zero. -/
theorem kf_innov_L2 (t : ℕ) :
    kf_L2 μ (S.innov y h u t) ∧ kf_mean μ (S.innov y h u t) = 0 := by
  obtain ⟨he, hme, -, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  rw [S.kf_innov_eq hy]
  refine ⟨kf_L2_add (kf_L2_app he _) (kf_L2_app (hLε t) _), ?_⟩
  rw [kf_mean_add (kf_L2_app he _) (kf_L2_app (hLε t) _), kf_mean_app he, kf_mean_app (hLε t),
    hme, hmε]
  simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.9)** (Miao, p. 330), corrected: `E[(x_t − x̂_{t|t−1})ε_t'] = C_{t−1}` (`0` at
`t = 0`). -/
theorem eq_10_9 (t : ℕ) : var_mom μ (S.err x y h u t) (ε t) = S.Cl t := by
  obtain ⟨-, -, -, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  rw [hes t le_rfl]
  simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.8)** (Miao, p. 330) and the covariances of (10.12) (p. 332): `Ea_ta_t' = Ω_{t|t−1}`,
`E[(x_t − x̂_{t|t−1})a_t'] = Σ_{t|t−1}G_t' + C_{t−1}D_t'`. -/
theorem eq_10_8 (t : ℕ) :
    var_mom μ (S.innov y h u t) (S.innov y h u t) = S.Om t ∧
      var_mom μ (S.err x y h u t) (S.innov y h u t) =
        kf_Mx (S.G t) (S.D t) (S.Cl t) (S.Spred t) := by
  obtain ⟨he, -, hee, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  obtain ⟨haa, hea, -⟩ := kf_step (μ := μ) he (hLε t) (hLε (t + 1)) (S.G t) (S.D t) (S.Cl t)
    (S.K t) (S.A t) (S.C t) (S.kf_innov_eq hy t) rfl hee (by rw [hes t le_rfl]; simp)
    (by rw [hεε]; simp) (by rw [hes _ (Nat.le_succ t)]; simp) (by rw [hεε]; simp)
    (by rw [hεε]; simp)
  exact ⟨haa, hea⟩

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.11)** (Miao, p. 331): for an arbitrary gain `K'`, the error of the update
`x̂_{t|t−1} + K'a_t` has second moments `(I − K'G)Σ(I − K'G)' + K'DD'K' − (I − K'G)CD'K' −
K'DC'(I − K'G)'` (with `C = C_{t−1}`). -/
theorem eq_10_11 (t : ℕ) (K' : Matrix X Y ℝ) :
    var_mom μ (S.err x y h u t - kf_app K' (S.innov y h u t))
        (S.err x y h u t - kf_app K' (S.innov y h u t)) =
      kf_joseph (S.G t) (S.D t) (S.Cl t) (S.Spred t) K' := by
  obtain ⟨he, -, hee, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  obtain ⟨-, -, -, hff, -⟩ := kf_step (μ := μ) he (hLε t) (hLε (t + 1)) (S.G t) (S.D t)
    (S.Cl t) K' (S.A t) (S.C t) (S.kf_innov_eq hy t) rfl hee (by rw [hes t le_rfl]; simp)
    (by rw [hεε]; simp) (by rw [hes _ (Nat.le_succ t)]; simp) (by rw [hεε]; simp)
    (by rw [hεε]; simp)
  exact hff

omit [DecidableEq E] in
/-- The filtered error: `x_t − x̂_{t|t} = (x_t − x̂_{t|t−1}) − K_ta_t`. -/
theorem kf_filt_err (t : ℕ) :
    x t - S.xfilt y h u t = S.err x y h u t - kf_app (S.K t) (S.innov y h u t) := by
  rw [xfilt, err]
  abel

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- Miao, pp. 331–332: `E(x_t − x̂_{t|t})(x_t − x̂_{t|t})' = Σ_{t|t} = (I − K_tG_t)Σ_{t|t−1} −
K_tD_tC_{t−1}'`. -/
theorem kf_filt_moments (t : ℕ) :
    var_mom μ (x t - S.xfilt y h u t) (x t - S.xfilt y h u t) = S.Sfilt t := by
  have hP : (S.Spred t)ᵀ = S.Spred t := by
    obtain ⟨-, -, hee, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
    rw [← hee, ← kf_mom_transpose]
  rw [S.kf_filt_err, S.eq_10_11 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
  exact eq_10_11_gain _ _ _ hP (hΩ t)

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.10)** (Miao, p. 330), the random version: if `Ω_{t|t−1} > 0`, among all updates
`x̂_{t|t−1} + K'a_t` the Kalman gain minimises the error second-moment matrix (Loewner order) and
the mean squared error `E(x_t − x̂)'(x_t − x̂)` (its trace), uniquely. -/
theorem eq_10_10_random (t : ℕ) (hpos : (S.Om t).PosDef) (K' : Matrix X Y ℝ) :
    var_mom μ (x t - S.xfilt y h u t) (x t - S.xfilt y h u t) ≤
        var_mom μ (S.err x y h u t - kf_app K' (S.innov y h u t))
          (S.err x y h u t - kf_app K' (S.innov y h u t)) ∧
      (trace (var_mom μ (S.err x y h u t - kf_app K' (S.innov y h u t))
          (S.err x y h u t - kf_app K' (S.innov y h u t))) =
        trace (var_mom μ (x t - S.xfilt y h u t) (x t - S.xfilt y h u t)) ↔ K' = S.K t) := by
  have hP : (S.Spred t)ᵀ = S.Spred t := by
    obtain ⟨-, -, hee, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
    rw [← hee, ← kf_mom_transpose]
  rw [S.kf_filt_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ,
    S.eq_10_11 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
  obtain ⟨h1, -, h3⟩ := eq_10_10 (S.G t) (S.D t) (S.Cl t) hP hpos K'
  exact ⟨h1, h3⟩

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- Shocks dated after `s` are orthogonal to the innovation `a_s`. -/
theorem kf_shock_innov (s r : ℕ) (hr : s < r) :
    var_mom μ (ε r) (S.innov y h u s) = 0 := by
  obtain ⟨he, -, -, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s
  rw [kf_mom_transpose, S.kf_innov_eq hy, kf_mom_lin2 he (hLε s) (hLε r), hes r hr.le, hεε]
  have h1 : r ≠ s := by omega
  have h2 : s ≠ r := by omega
  simp [h1, h2]

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The projection property behind (10.12) (Miao, p. 332): the prediction error
`x_t − x̂_{t|t−1}` is orthogonal to every past innovation `a_s`, `s < t`. -/
theorem kf_err_orth (s k : ℕ) :
    var_mom μ (S.err x y h u (s + 1 + k)) (S.innov y h u s) = 0 := by
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ
  have hI := fun t => (S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).1
  have hsucc : ∀ t, var_mom μ (S.err x y h u (t + 1)) (S.innov y h u s) =
      S.A t * (var_mom μ (S.err x y h u t) (S.innov y h u s) -
        S.K t * var_mom μ (S.innov y h u t) (S.innov y h u s)) +
        S.C t * var_mom μ (ε (t + 1)) (S.innov y h u s) := by
    intro t
    rw [S.kf_err_succ hx, kf_mom_add_left (kf_L2_app (kf_L2_sub (hM t).1 (kf_L2_app (hI t) _)) _)
      (kf_L2_app (hLε _) _) (hI s), kf_mom_app_left (kf_L2_sub (hM t).1 (kf_L2_app (hI t) _))
      (hI s), kf_mom_app_left (hLε _) (hI s), kf_mom_lin_sub (hM t).1 (hI t) (hI s)]
  induction k with
  | zero =>
    rw [add_zero, hsucc, S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s (s + 1)
      (by omega), (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).1,
      (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).2]
    have hinv : (kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s))⁻¹ *
        kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s) = 1 := nonsing_inv_mul _ (hΩ s)
    simp only [K, Om, kf_gain, Matrix.mul_assoc, hinv, Matrix.mul_one, sub_self,
      Matrix.mul_zero, add_zero]
  | succ k ih =>
    rw [show s + 1 + (k + 1) = (s + 1 + k) + 1 by omega, hsucc, ih,
      S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ (by omega), S.kf_innov_eq hy,
      kf_mom_lin2 (hM _).1 (hLε _) (hI s), ih,
      S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ (by omega)]
    simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- Miao, p. 333: the innovations are mutually uncorrelated, `Ea_ta_s' = 0` for `s < t` (the
second-moment content of "`a_t` is independently distributed"). -/
theorem kf_innov_orth (s t : ℕ) (hst : s < t) :
    var_mom μ (S.innov y h u t) (S.innov y h u s) = 0 := by
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  have hI := (S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).1
  obtain ⟨k, rfl⟩ : ∃ k, t = s + 1 + k := ⟨t - s - 1, by omega⟩
  rw [S.kf_innov_eq hy, kf_mom_lin2 hM.1 (hLε _) hI,
    S.kf_err_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ,
    S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ (by omega)]
  simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The filtered error `x_t − x̂_{t|t}` is orthogonal to the innovations `a_0, …, a_t`. -/
theorem kf_filt_orth (s t : ℕ) (hst : s ≤ t) :
    var_mom μ (x t - S.xfilt y h u t) (S.innov y h u s) = 0 := by
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  have hI := fun t => (S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).1
  rw [S.kf_filt_err, kf_mom_lin_sub hM.1 (hI t) (hI s)]
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [(S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).1,
      (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).2]
    have hinv : (kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s))⁻¹ *
        kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s) = 1 := nonsing_inv_mul _ (hΩ s)
    simp only [K, Om, kf_gain, Matrix.mul_assoc, hinv, Matrix.mul_one, sub_self]
  · obtain ⟨k, rfl⟩ : ∃ k, t = s + 1 + k := ⟨t - s - 1, by omega⟩
    rw [S.kf_err_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ,
      S.kf_innov_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ hlt]
    simp

/-- The innovation-based predictor term `∑_{s<n} L_sa_s`. -/
noncomputable def kf_wsum (L : ℕ → Matrix X Y ℝ) (n : ℕ) : Ω → X → ℝ :=
  ∑ s ∈ Finset.range n, kf_app (L s) (S.innov y h u s)

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The second moments of `W_n = ∑_{s<n} L_sa_s`: square integrable, mean zero,
`E[a_rW_n'] = 0` and `E[(x_r − x̂_{r|r−1})W_n'] = 0` for `n ≤ r`, `EW_nW_n' = ∑ L_sΩ_sL_s'`. -/
theorem kf_wsum_moments (L : ℕ → Matrix X Y ℝ) (n : ℕ) :
    kf_L2 μ (S.kf_wsum (y := y) (h := h) (u := u) L n) ∧
      kf_mean μ (S.kf_wsum (y := y) (h := h) (u := u) L n) = 0 ∧
      (∀ r, n ≤ r → var_mom μ (S.innov y h u r) (S.kf_wsum (y := y) (h := h) (u := u) L n) = 0 ∧
        var_mom μ (S.err x y h u r) (S.kf_wsum (y := y) (h := h) (u := u) L n) = 0) ∧
      var_mom μ (S.kf_wsum (y := y) (h := h) (u := u) L n)
        (S.kf_wsum (y := y) (h := h) (u := u) L n) =
        ∑ s ∈ Finset.range n, L s * S.Om s * (L s)ᵀ := by
  have hI := fun t => S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ
  induction n with
  | zero =>
    simp only [kf_wsum, Finset.range_zero, Finset.sum_empty]
    refine ⟨kf_L2_zero, ?_, fun r _ => ⟨?_, ?_⟩, ?_⟩ <;>
      first | (funext i; simp [kf_mean]) | (ext i j; simp [var_mom])
  | succ n ih =>
    obtain ⟨hW, hmW, horth, hWW⟩ := ih
    have hZ := kf_L2_app (hI n).1 (L n)
    have hrec : S.kf_wsum (y := y) (h := h) (u := u) L (n + 1) =
        S.kf_wsum (y := y) (h := h) (u := u) L n + kf_app (L n) (S.innov y h u n) := by
      simp only [kf_wsum, Finset.sum_range_succ]
    rw [hrec]
    refine ⟨kf_L2_add hW hZ, ?_, fun r hr => ⟨?_, ?_⟩, ?_⟩
    · rw [kf_mean_add hW hZ, hmW, kf_mean_app (hI n).1, (hI n).2]
      simp
    · rw [kf_mom_add_right hW hZ (hI r).1, (horth r (by omega)).1, kf_mom_app_right (hI n).1
        (hI r).1, S.kf_innov_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ n r (by omega)]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, r = n + 1 + k := ⟨r - n - 1, by omega⟩
      rw [kf_mom_add_right hW hZ (hM _).1, (horth _ (by omega)).2, kf_mom_app_right (hI n).1
        (hM _).1, S.kf_err_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
      simp
    · rw [kf_mom_add_left hW hZ (kf_L2_add hW hZ), kf_mom_add_right hW hZ hW,
        kf_mom_add_right hW hZ hZ, hWW, kf_mom_app_right (hI n).1 hW,
        kf_mom_transpose (S.innov y h u n), kf_mom_app_left (hI n).1 hZ,
        kf_mom_app_right (hI n).1 (hI n).1, kf_mom_app_left (hI n).1 hW, (horth n le_rfl).1,
        (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ n).1, Finset.sum_range_succ]
      simp [Matrix.mul_assoc]

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.12)** (Miao, p. 332), the projection theorem in second moments: `x̂_{t|t−1}` is the best
predictor of `x_t` among all predictors `x̂_{t|t−1} + ∑_{s<t}L_sa_s + c` that are affine in the
past innovations. The error second-moment matrix of such a predictor is
`Σ_{t|t−1} + ∑_{s<t}L_sΩ_{s|s−1}L_s' + cc'`, which dominates `Σ_{t|t−1}` in the Loewner order. -/
theorem eq_10_12 (t : ℕ) (L : ℕ → Matrix X Y ℝ) (c : X → ℝ) :
    var_mom μ (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) =
      S.Spred t + ∑ s ∈ Finset.range t, L s * S.Om s * (L s)ᵀ + Matrix.of (fun i j => c i * c j) ∧
      S.Spred t ≤ var_mom μ (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) := by
  obtain ⟨he, hme, hee, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  obtain ⟨hW, hmW, horth, hWW⟩ :=
    S.kf_wsum_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ L t
  set W := S.kf_wsum (y := y) (h := h) (u := u) L t
  have hc := kf_L2_const (μ := μ) c
  have hrw : x t - (S.xpred y h u t + W + fun _ => c) = (S.err x y h u t - W) - fun _ => c := by
    rw [err]
    abel
  have hd := kf_L2_sub he hW
  have hmd : kf_mean μ (S.err x y h u t - W) = 0 := by
    rw [kf_mean_sub he hW, hme, hmW, sub_zero]
  have hdd : var_mom μ (S.err x y h u t - W) (S.err x y h u t - W) =
      S.Spred t + var_mom μ W W := by
    rw [kf_mom_sub_left he hW hd, kf_mom_sub_right he hW he, kf_mom_sub_right he hW hW, hee,
      (horth t le_rfl).2, kf_mom_transpose (S.err x y h u t) W, (horth t le_rfl).2]
    simp
  have hcc : var_mom μ (fun _ : Ω => c) (fun _ : Ω => c) = Matrix.of (fun i j => c i * c j) := by
    rw [kf_mom_const_left, kf_mean_const]
  have hdc : var_mom μ (S.err x y h u t - W) (fun _ : Ω => c) = 0 := by
    rw [kf_mom_const_right, hmd]
    ext i j
    simp
  have hcd : var_mom μ (fun _ : Ω => c) (S.err x y h u t - W) = 0 := by
    rw [kf_mom_transpose, hdc, transpose_zero]
  have htot : var_mom μ (x t - (S.xpred y h u t + W + fun _ => c))
      (x t - (S.xpred y h u t + W + fun _ => c)) =
      S.Spred t + ∑ s ∈ Finset.range t, L s * S.Om s * (L s)ᵀ +
        Matrix.of (fun i j => c i * c j) := by
    rw [hrw, kf_mom_sub_left hd hc (kf_L2_sub hd hc), kf_mom_sub_right hd hc hd,
      kf_mom_sub_right hd hc hc, hdd, hdc, hcd, hcc, hWW]
    abel
  refine ⟨htot, ?_⟩
  rw [htot, Matrix.le_iff, add_assoc, add_sub_cancel_left, ← hWW, ← hcc]
  exact (kf_mom_self_psd hW).add (kf_mom_self_psd hc)

/-! ### Recursive forms (Miao, p. 333) -/

omit [DecidableEq E] in
/-- Miao, p. 333: the fully recursive form `x̂_{t+1|t} = A_tx̂_{t|t−1} + B_tu_t + A_tK_ta_t`. -/
theorem kf_pred_recursive (t : ℕ) :
    S.xpred y h u (t + 1) = kf_app (S.A t) (S.xpred y h u t) + kf_app (S.B t) (u t) +
      kf_app (S.A t * S.K t) (S.innov y h u t) := by
  rw [xpred_succ, xfilt, kf_app_add, kf_app_app]
  abel

omit [DecidableEq E] in
/-- Miao, p. 333: the alternative form `x̂_{t+1|t+1} = A_tx̂_{t|t} + B_tu_t + K_{t+1}a_{t+1}`. -/
theorem kf_filt_recursive (t : ℕ) :
    S.xfilt y h u (t + 1) = kf_app (S.A t) (S.xfilt y h u t) + kf_app (S.B t) (u t) +
      kf_app (S.K (t + 1)) (S.innov y h u (t + 1)) := by
  rw [xfilt, xpred_succ]

omit [Fintype U] [DecidableEq E] in
/-- Miao, p. 333: the Riccati equation for the predicted covariances,
`Σ_{t+1|t} = A_tΣ_{t|t−1}A_t' + C_tC_t' − A_t(G_tΣ_{t|t−1} + D_tC'_{t−1})'Ω⁻¹(G_tΣ_{t|t−1} +
D_tC'_{t−1})A_t'`, for symmetric `Σ_{t|t−1}` and invertible `Ω_{t|t−1}`. -/
theorem kf_riccati_Spred (t : ℕ) (hP : (S.Spred t)ᵀ = S.Spred t) (hu : IsUnit (S.Om t).det) :
    S.Spred (t + 1) = S.A t * S.Spred t * (S.A t)ᵀ + S.C t * (S.C t)ᵀ -
      S.A t * (S.G t * S.Spred t + S.D t * (S.Cl t)ᵀ)ᵀ * (S.Om t)⁻¹ *
        (S.G t * S.Spred t + S.D t * (S.Cl t)ᵀ) * (S.A t)ᵀ :=
  kf_riccati_pred _ _ _ _ _ hP hu

omit [Fintype U] [DecidableEq E] in
/-- Miao, p. 333: the recursion for the filtered covariances,
`Σ_{t+1|t+1} = (I − K_{t+1}G_{t+1})(A_tΣ_{t|t}A_t' + C_tC_t') − K_{t+1}D_{t+1}C_t'`. -/
theorem kf_riccati_Sfilt (t : ℕ) :
    S.Sfilt (t + 1) = (1 - S.K (t + 1) * S.G (t + 1)) *
      (S.A t * S.Sfilt t * (S.A t)ᵀ + S.C t * (S.C t)ᵀ) -
      S.K (t + 1) * S.D (t + 1) * (S.C t)ᵀ := rfl

end KFSystem

/-! ### The printed cross covariance (10.9) -/

/-- The uniform probability on two points. -/
noncomputable def kf_twoPoint : Measure (Fin 2) := (2 : ENNReal)⁻¹ • Measure.count

/-- The two-point measure is a probability measure. -/
theorem kf_twoPoint_prob : IsProbabilityMeasure kf_twoPoint := by
  constructor
  simp only [kf_twoPoint, Measure.smul_apply, Measure.count_univ, smul_eq_mul,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  simp only [Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- Integrals against the two-point measure. -/
theorem kf_twoPoint_integral (f : Fin 2 → ℝ) : ∫ ω, f ω ∂kf_twoPoint = (f 0 + f 1) / 2 := by
  have := kf_twoPoint_prob
  rw [integral_fintype]
  · simp [kf_twoPoint, Fin.sum_univ_two, Measure.real]
    ring
  · exact Integrable.of_finite

/-- (10.9) as printed is false at `t = 0` (Miao, p. 330): the book's
`E[(x_t − x̂_{t|t−1})ε_t'] = C_t` fails for `t = 0`, where the cross moment is `Cℓ₀ = 0`. Here
`x₀ = x̄₀ = 0`, `Σ₀ = 0`, `C₀ = 1`, and `ε₀ = ±1` with probability `½` each (mean `0`, variance
`1`, uncorrelated with `x₀`). -/
theorem kf_cross_book_false :
    ∃ (S : KFSystem (Fin 1) (Fin 1) (Fin 1) (Fin 1)) (x : ℕ → Fin 2 → Fin 1 → ℝ)
      (ε : ℕ → Fin 2 → Fin 1 → ℝ),
      kf_mean kf_twoPoint (ε 0) = 0 ∧ var_mom kf_twoPoint (ε 0) (ε 0) = 1 ∧
      var_mom kf_twoPoint (x 0 - fun _ => S.xbar0) (x 0 - fun _ => S.xbar0) = S.S0 ∧
      var_mom kf_twoPoint (x 0 - fun _ => S.xbar0) (ε 0) = 0 ∧
      ∀ (y h : ℕ → Fin 2 → Fin 1 → ℝ) (u : ℕ → Fin 2 → Fin 1 → ℝ),
        var_mom kf_twoPoint (S.err x y h u 0) (ε 0) = S.Cl 0 ∧
        var_mom kf_twoPoint (S.err x y h u 0) (ε 0) ≠ S.C 0 := by
  refine ⟨⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0, 0, 0⟩,
    fun _ _ => 0, fun _ ω _ => if ω = 0 then 1 else -1, ?_, ?_, ?_, ?_, fun y h u => ⟨?_, ?_⟩⟩
  · funext i
    simp [kf_mean, kf_twoPoint_integral]
  · ext i j
    fin_cases i
    fin_cases j
    simp [var_mom, kf_twoPoint_integral]
  · ext i j
    simp [var_mom]
  · ext i j
    simp [var_mom]
  · ext i j
    simp [var_mom, KFSystem.err, KFSystem.xpred, KFSystem.Cl]
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp [var_mom, KFSystem.err, KFSystem.xpred] at this
end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The stationary Kalman filter

Miao, §10.1.1, pp. 332–334. The time-invariant system (`KFSystem.const`: `A_t = A`, …, `D_t = D`)
and the "long-run stationary Kalman filter in which `Σ_t → Σ` and `K_t → K`" (p. 334).

* Step 1 (p. 332), the stationary initialisation: for stable `A`, `x̂₀ = Ax̂₀` forces `x̂₀ = 0`
  (`kf_step1_mean`), and `Σ₀ = AΣ₀A' + Q` has exactly one solution, given in vectorised form by
  `vec Σ₀ = (I − A ⊗ A)⁻¹ vec Q` (`kf_step1_cov`). The book's `Q` (undefined there) is the state
  noise covariance `CC'`.
* Duality (`kf_dual`, `kf_dual_T`): when the state and measurement noises are uncorrelated
  (`CD' = 0`, the case "often considered in applications", p. 328), the covariance recursion
  `Σ_{t+1|t} = AΣ_{t|t}A' + CC'` is the Riccati operator (9.11) of the dual LQ problem
  `(Â, B̂, Q̂, R̂, Ŝ, β) = (A', G', CC', DD', 0, 1)` of Chapter 9 (`LSProblem.T`).
* `kf_steady_state`: if `CD' = 0`, `DD' > 0`, `(A, G)` is detectable (Definition 9.1.4) and
  `(A, C)` is stabilizable (Definition 9.1.1), the steady-state Riccati equation
  `Σ = AΣA' + CC' − AΣG'(GΣG' + DD')⁻¹GΣA'` has a unique positive semidefinite solution `Σ`; from
  every positive semidefinite `Σ₀` the filter covariances `Σ_{t|t−1} → Σ` and gains `K_t → K =
  ΣG'(GΣG' + DD')⁻¹`; and the error matrix `A − AKG` of (9.3) is stable. This is Proposition 9.3.2
  (`LSProblem.ls_discounted_main`) applied to the dual problem: detectability of `(A, G)` is
  stabilizability of `(A', G')`, stabilizability of `(A, C)` is detectability of `(A', C')`.
* `kf_steady_fixed`: started at the steady state, the filter covariance stays there.

The book gives no conditions for the convergence `Σ_t → Σ`; the conditions above are the dual of
those of Propositions 9.3.1–9.3.2. The correlated case `CD' ≠ 0` is not covered by the stated
theorem (the dual problem then has a cross term).
-/

open Filter Topology Matrix

open scoped MatrixOrder Kronecker

namespace Miao.PartialInformation

variable {X U Y E : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X]
  [DecidableEq Y]

/-- The time-invariant system: `A_t = A`, …, `D_t = D` (Miao, p. 333). -/
def KFSystem.const (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ)
    (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ) (S0 : Matrix X X ℝ) :
    KFSystem X U Y E :=
  ⟨fun _ => A, fun _ => B, fun _ => C, fun _ => G, fun _ => H, fun _ => D, xbar0, S0⟩

omit [Fintype Y] [Fintype E] [DecidableEq Y] in
/-- Step 1 (Miao, p. 332): for stable `A`, the stationary mean `x̂₀ = Ax̂₀` is `0`. -/
theorem kf_step1_mean {A : Matrix X X ℝ} (hA : ls_Stable A) {m : X → ℝ} (hm : A *ᵥ m = m) :
    m = 0 := by
  have h := (ls_stable_iff_tendsto A).1 hA m
  have hc : ∀ t : ℕ, (A ^ t) *ᵥ m = m := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← mulVec_mulVec, hm, ih]
  simp only [hc] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

omit [Fintype Y] [Fintype E] [DecidableEq Y] in
/-- Step 1 (Miao, p. 332): for stable `A`, the stationary covariance `Σ₀ = AΣ₀A' + Q` exists and
is unique (`var_lyapSol`, Chapter 2), and in vectorised form it is
`vec Σ₀ = (I − A ⊗ A)⁻¹ vec Q`, `I − A ⊗ A` being invertible. -/
theorem kf_step1_cov {A : Matrix X X ℝ} (hA : ls_Stable A) (Q : Matrix X X ℝ) :
    var_lyapSol A Q = A * var_lyapSol A Q * Aᵀ + Q ∧
      (∀ S0 : Matrix X X ℝ, S0 = A * S0 * Aᵀ + Q → S0 = var_lyapSol A Q) ∧
      IsUnit (1 - A ⊗ₖ A) ∧ ∀ S0 : Matrix X X ℝ, S0 = A * S0 * Aᵀ + Q →
        vec S0 = (1 - A ⊗ₖ A)⁻¹ *ᵥ vec Q := by
  have hfix := lyap_fixed A hA Q
  have huniq : ∀ S0 : Matrix X X ℝ, S0 = A * S0 * Aᵀ + Q → S0 = var_lyapSol A Q :=
    fun S0 h => lyap_unique A hA Q S0 h.symm
  have hvec : ∀ V : Matrix X X ℝ, (1 - A ⊗ₖ A) *ᵥ vec V = vec (V - A * V * Aᵀ) := by
    intro V
    rw [sub_mulVec, one_mulVec, kronecker_mulVec_vec, vec_sub]
  have hunit : IsUnit (1 - A ⊗ₖ A) := by
    refine mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
    obtain ⟨V, rfl⟩ := vec_bijective.2 v
    obtain ⟨W, rfl⟩ := vec_bijective.2 w
    rw [hvec, hvec, vec_inj] at hvw
    have h0 : ∀ Z : Matrix X X ℝ, Z = A * Z * Aᵀ + 0 → Z = var_lyapSol A 0 :=
      fun Z h => lyap_unique A hA 0 Z h.symm
    have hVW : V - W = A * (V - W) * Aᵀ + 0 := by
      calc V - W = (V - A * V * Aᵀ) - (W - A * W * Aᵀ) + (A * V * Aᵀ - A * W * Aᵀ) := by abel
        _ = A * (V - W) * Aᵀ + 0 := by
          rw [hvw, sub_self, zero_add, add_zero, Matrix.mul_sub, Matrix.sub_mul]
    have hz : (0 : Matrix X X ℝ) = A * 0 * Aᵀ + 0 := by simp
    rw [← sub_eq_zero, ← vec_sub, h0 _ hVW, ← h0 0 hz, vec_zero]
  refine ⟨hfix.symm, huniq, hunit, fun S0 h => ?_⟩
  have h1 : (1 - A ⊗ₖ A) *ᵥ vec S0 = vec Q := by
    rw [hvec, sub_eq_iff_eq_add'.2 h]
  rw [← h1, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hunit), one_mulVec]

/-- The dual LQ problem of the filter (Miao, pp. 333–334, with Chapter 9):
`(Â, B̂, Ĉ, Q̂, R̂, Ŝ, β) = (A', G', C, CC', DD', 0, 1)`. -/
def kf_dual (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ) (D : Matrix Y E ℝ) :
    LSProblem X Y E :=
  ⟨Aᵀ, Gᵀ, C, C * Cᵀ, D * Dᵀ, 0, 1⟩

omit [DecidableEq X] in
/-- Duality (uncorrelated noise, `CℓD' = 0`): `AΣ_{t|t}A' + CC' = T̂(Σ_{t|t−1})`, the Riccati
operator (9.11) of the dual problem: `T̂(P) = CC' + APA' − APG'(DD' + GPG')⁻¹GPA'`. -/
theorem kf_dual_T [DecidableEq X] (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) {Cl : Matrix X E ℝ} (hCD : Cl * Dᵀ = 0) (P : Matrix X X ℝ) :
    A * kf_filtCov G D Cl P * Aᵀ + C * Cᵀ = (kf_dual A G C D).T P := by
  have hDC : D * Clᵀ = 0 := by
    rw [← transpose_transpose (D * Clᵀ), transpose_mul, transpose_transpose, hCD,
      transpose_zero]
  have hΩ : kf_Om G D Cl P = D * Dᵀ + G * P * Gᵀ := by
    rw [kf_Om, Matrix.mul_assoc G Cl, hCD, hDC]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    abel
  simp only [kf_filtCov, kf_gain, kf_Mx, hCD, add_zero, hΩ, LSProblem.T, kf_dual, LSProblem.G,
    LSProblem.N, one_smul, transpose_transpose, transpose_zero, zero_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc, hDC, Matrix.mul_zero, sub_zero]
  abel

/-- The steady-state gain `K = ΣG'(GΣG' + DD')⁻¹`. -/
noncomputable def kf_steadyGain (G : Matrix Y X ℝ) (D : Matrix Y E ℝ) (P : Matrix X X ℝ) :
    Matrix X Y ℝ :=
  P * Gᵀ * (G * P * Gᵀ + D * Dᵀ)⁻¹

omit [Fintype U] in
/-- With `CD' = 0`, the time-invariant filter covariances follow the dual Riccati operator:
`Σ_{t+1|t} = T̂(Σ_{t|t−1})`, hence `Σ_{t|t−1} = T̂ᵗ(Σ₀)`; and `K_t = Σ_{t|t−1}G'(GΣ_{t|t−1}G' +
DD')⁻¹`. -/
theorem kf_const_Spred (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (S0 : Matrix X X ℝ) (hCD : C * Dᵀ = 0) (t : ℕ) :
    (KFSystem.const A B C G H D xbar0 S0).Spred t = (kf_dual A G C D).T^[t] S0 ∧
      (KFSystem.const A B C G H D xbar0 S0).K t =
        kf_steadyGain G D ((KFSystem.const A B C G H D xbar0 S0).Spred t) := by
  set S := KFSystem.const A B C G H D xbar0 S0
  have hCl : ∀ t, S.Cl t * Dᵀ = 0 := by
    intro t
    cases t with
    | zero => exact Matrix.zero_mul _
    | succ t => exact hCD
  have hClD : ∀ t, D * (S.Cl t)ᵀ = 0 := by
    intro t
    rw [← transpose_transpose (D * (S.Cl t)ᵀ), transpose_mul, transpose_transpose, hCl t,
      transpose_zero]
  refine ⟨?_, ?_⟩
  · induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ← ih]
      exact kf_dual_T A G C D (hCl t) (S.Spred t)
  · simp only [KFSystem.K, kf_gain, kf_Mx, kf_Om, kf_steadyGain]
    rw [show S.G t = G from rfl, show S.D t = D from rfl, Matrix.mul_assoc G (S.Cl t), hCl t,
      hClD t]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

omit [Fintype U] in
/-- **The stationary Kalman filter** (Miao, pp. 333–334), uncorrelated case `CD' = 0`, via
Proposition 9.3.2 for the dual LQ problem. If `DD' > 0`, `(A, G)` is detectable and `(A, C)` is
stabilizable, then the steady-state Riccati equation
`Σ = AΣA' + CC' − AΣG'(GΣG' + DD')⁻¹GΣA'` has a positive semidefinite solution `Σ`, unique among
positive semidefinite matrices; from every positive semidefinite `Σ₀` the filter covariances
converge, `Σ_{t|t−1} → Σ`, and so do the gains, `K_t → K = ΣG'(GΣG' + DD')⁻¹`; and `A − AKG` is
stable. -/
theorem kf_steady_state [Nonempty X] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (hCD : C * Dᵀ = 0) (hR : (D * Dᵀ).PosDef) (hdet : ls_Detectable A G)
    (hstab : ls_Stabilizable A C) :
    ∃ P : Matrix X X ℝ, P.PosSemidef ∧
      P = A * P * Aᵀ + C * Cᵀ - A * P * Gᵀ * (G * P * Gᵀ + D * Dᵀ)⁻¹ * G * P * Aᵀ ∧
      (∀ P' : Matrix X X ℝ, P'.PosSemidef →
        P' = A * P' * Aᵀ + C * Cᵀ - A * P' * Gᵀ * (G * P' * Gᵀ + D * Dᵀ)⁻¹ * G * P' * Aᵀ →
          P' = P) ∧
      (∀ S0 : Matrix X X ℝ, S0.PosSemidef →
        Tendsto (fun t => (KFSystem.const A B C G H D xbar0 S0).Spred t) atTop (𝓝 P) ∧
        Tendsto (fun t => (KFSystem.const A B C G H D xbar0 S0).K t) atTop
          (𝓝 (kf_steadyGain G D P))) ∧
      ls_Stable (A - A * kf_steadyGain G D P * G) := by
  set L := kf_dual A G C D
  have hQ : L.Q.PosSemidef := by
    simpa [L, kf_dual, conjTranspose_eq_transpose_of_trivial] using
      posSemidef_self_mul_conjTranspose C
  have hS : L.S = 0 := rfl
  have hβ : (0 : ℝ) ≤ L.β := zero_le_one
  have hsq : Real.sqrt L.β = 1 := Real.sqrt_one
  have hstab' : ls_Controllable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) ∨
      ls_Stabilizable (Real.sqrt L.β • L.A) (Real.sqrt L.β • L.B) := by
    right
    obtain ⟨J, hJ⟩ := hdet
    refine ⟨-Jᵀ, ?_⟩
    rw [hsq, one_smul, one_smul, ← ls_stable_transpose]
    convert hJ using 1
    simp [L, kf_dual, transpose_mul, sub_eq_add_neg]
  have hD : ∀ F, ls_Detects (L.toSS hQ hR) F := by
    intro F
    refine ls_detects_of_detectable (L.toSS hQ hR) (Lm := Cᵀ) ?_ ?_ F
    · simp [LSProblem.toSS, L, kf_dual]
    · obtain ⟨Hm, hH⟩ := hstab
      refine ⟨-Hmᵀ, ?_⟩
      rw [← ls_stable_transpose]
      convert hH using 1
      simp [LSProblem.toSS, L, kf_dual, transpose_mul, sub_eq_add_neg]
  obtain ⟨P, hP, hfix, huniq, hconv, hst, -⟩ := L.ls_discounted_main hS hβ hQ hR hstab' hD
  have hT : ∀ P' : Matrix X X ℝ, L.T P' =
      A * P' * Aᵀ + C * Cᵀ - A * P' * Gᵀ * (G * P' * Gᵀ + D * Dᵀ)⁻¹ * G * P' * Aᵀ := by
    intro P'
    simp only [L, LSProblem.T, kf_dual, LSProblem.G, LSProblem.N, one_smul, transpose_transpose,
      transpose_zero, zero_add, Matrix.mul_assoc]
    rw [add_comm (D * Dᵀ)]
    abel
  have hGP : (G * P * Gᵀ + D * Dᵀ).PosDef := by
    have := L.G_posDef hR hP hβ
    simpa [L, LSProblem.G, kf_dual, add_comm, Matrix.mul_assoc] using this
  refine ⟨P, hP, by rw [← hT, hfix], fun P' hP' h' => huniq P' hP' (by rw [hT]; exact h'.symm),
    fun S0 hS0 => ?_, ?_⟩
  · have hlim : Tendsto (fun t => (KFSystem.const A B C G H D xbar0 S0).Spred t) atTop (𝓝 P) :=
      (hconv S0 hS0).congr fun t => (kf_const_Spred A B C G H D xbar0 S0 hCD t).1.symm
    refine ⟨hlim, ?_⟩
    have hK : (fun t => (KFSystem.const A B C G H D xbar0 S0).K t) =
        fun t => kf_steadyGain G D ((KFSystem.const A B C G H D xbar0 S0).Spred t) :=
      funext fun t => (kf_const_Spred A B C G H D xbar0 S0 hCD t).2
    rw [hK]
    exact ls_tendsto_mul (ls_tendsto_mul hlim tendsto_const_nhds)
      (ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 hGP.isUnit)
        ((ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds hlim) tendsto_const_nhds).add
          tendsto_const_nhds))
  · rw [hsq, one_smul, ← ls_stable_transpose] at hst
    convert hst using 1
    have hsym : ((G * P * Gᵀ + D * Dᵀ)⁻¹)ᵀ = (G * P * Gᵀ + D * Dᵀ)⁻¹ := by
      rw [transpose_nonsing_inv, transpose_add, transpose_mul, transpose_mul, transpose_transpose,
        transpose_mul, transpose_transpose, (SS.LQProblem.posSemidef_iff_real.1 hP).1]
      simp [Matrix.mul_assoc]
    have hsym2 : ((G * (P * Gᵀ) + D * Dᵀ)⁻¹)ᵀ = (G * (P * Gᵀ) + D * Dᵀ)⁻¹ := by
      rw [← Matrix.mul_assoc]; exact hsym
    simp only [L, kf_dual, LSProblem.F, LSProblem.G, LSProblem.N, kf_steadyGain, one_smul,
      transpose_zero, zero_add, transpose_sub, transpose_mul, transpose_transpose,
      (SS.LQProblem.posSemidef_iff_real.1 hP).1, Matrix.mul_assoc]
    rw [add_comm (D * Dᵀ), hsym2]

omit [Fintype U] in
/-- Started at the steady state (Step 1 with `Σ₀ = Σ`), the time-invariant filter covariance stays
there: `Σ_{t|t−1} = Σ` and `K_t = K` for all `t` (uncorrelated case). -/
theorem kf_steady_fixed (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (hCD : C * Dᵀ = 0) {P : Matrix X X ℝ} (hfix : (kf_dual A G C D).T P = P) (t : ℕ) :
    (KFSystem.const A B C G H D xbar0 P).Spred t = P ∧
      (KFSystem.const A B C G H D xbar0 P).K t = kf_steadyGain G D P := by
  have h1 := (kf_const_Spred A B C G H D xbar0 P hCD t)
  rw [Function.iterate_fixed hfix] at h1
  rw [h1.2, h1.1]
  exact ⟨rfl, rfl⟩

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Examples 10.1.1–10.1.4

Miao, §10.1.1, pp. 329 and 334–337.

* **Example 10.1.1** (Guvenen's labor income process): the state-space form with
  `x_t = (α, β, z_t)'`, `ε_t = (η_t/σ_η, v_t/σ_v)'` (`example_10_1_1`); the noises are
  uncorrelated (`CD' = 0`). Correction: the printed measurement equation uses
  `(η_{t+1}, v_{t+1})'`; with `y_t = α + βt + z_t + v_t` the shock is `ε_t = (η_t, v_t)'`, as
  (10.2) requires (`example_10_1_1_misprint`). The book also takes unit variances in `C, D`; here
  the loadings carry `σ_η, σ_v` so that `Eε_tε_t' = I`.
* The scalar filter (`kf_scalarSys`: `x_{t+1} = ax_t + cε¹_{t+1}`, `y_t = x_t + dε²_t`): the
  covariance recursion is `Σ_{t+1|t} = a²d²Σ/(Σ + d²) + c²` (`kf_scalarRic`), the gain
  `K_t = Σ/(Σ + d²)`, `Ω_t = Σ + d²` (`kf_scalar_filter`), and for `c ≠ 0, d ≠ 0` the iterates
  converge from every `Σ₀ ≥ 0` to the unique nonnegative fixed point, the positive root of
  `Σ² + d²(1 − a² − c²/d²)Σ − c²d² = 0` (`kf_scalar_tendsto`, a contraction argument).
* **Example 10.1.2** (Muth): `K_t = Σ_t/(Σ_t + R)`, `Σ_{t+1} = (Σ_t(R + Q) + QR)/(Σ_t + R)`,
  `Σ_t → Σ = (Q + √(Q² + 4QR))/2`, `K_t → K`, the filter `x̂_{t+1|t} = (1 − K_t)x̂_{t|t−1} + K_ty_t`
  and, at the steady state, Cagan's adaptive expectations formula (`example_10_1_2`,
  `example_10_1_2_adaptive`); the case `Q = 0`: `σ_{t+1} = σ_tR/(σ_t + R)`, the innovation form
  and `K²(σ + R) = Kσ` (`example_10_1_2_constant`).
* **Example 10.1.3** (long-run productivity growth): the stationary `Σ` and `K` formulas, the
  innovation variance `Σ + σ_v²`, `K²(Σ + σ_v²) = KΣ`, the filter in levels (`example_10_1_3`,
  `example_10_1_3_filter`); misprint `Eε_t` for `Eη_t` noted.
* **Example 10.1.4** (likelihood): the Gaussian log density `kf_logDens` is the logarithm of the
  `N(0, Ω)` density formula `kf_gaussDens`, and the log-likelihood of the innovations is
  `−(n_yT/2)ln 2π − ½∑ ln|Ω_t| − ½∑ a_t'Ω_t⁻¹a_t` (`example_10_1_4`). That the conditional density
  of `y_t` given `y^{t−1}` is this normal density is the Gaussian reading, which is not
  formalised; the prediction-error decomposition is taken as the definition of the likelihood.
-/

open Filter Topology Matrix

namespace Miao.PartialInformation

/-! ### Example 10.1.1 -/

/-- The measurement matrix `G_t = [1 t 1]` of Example 10.1.1. -/
def kf_laborG (t : ℕ) : Matrix (Fin 1) (Fin 3) ℝ := !![1, (t : ℝ), 1]

/-- **Example 10.1.1** (Miao, p. 329): Guvenen's log labor income `y_t = α + βt + z_t + v_t`,
`z_{t+1} = ρz_t + η_{t+1}` (with `η_t = σ_ηe¹_t`, `v_t = σ_ve²_t`) has the state-space form
`x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = G_tx_t + Dε_t` with `x_t = (α, β, z_t)'`, `ε_t = (e¹_t, e²_t)'`,
`A = diag(1, 1, ρ)`, `C = [0 0; 0 0; σ_η 0]`, `G_t = [1 t 1]`, `D = [0 σ_v]`, and `CD' = 0`. -/
theorem example_10_1_1 (α β ρ ση σv : ℝ) (z e1 e2 : ℕ → ℝ) (y : ℕ → ℝ)
    (hz : ∀ t, z (t + 1) = ρ * z t + ση * e1 (t + 1))
    (hy : ∀ t, y t = α + β * t + z t + σv * e2 t) (t : ℕ) :
    ![α, β, z (t + 1)] = !![1, 0, 0; 0, 1, 0; 0, 0, ρ] *ᵥ ![α, β, z t] +
      !![0, 0; 0, 0; ση, 0] *ᵥ ![e1 (t + 1), e2 (t + 1)] ∧
    (fun _ : Fin 1 => y t) = kf_laborG t *ᵥ ![α, β, z t] + !![0, σv] *ᵥ ![e1 t, e2 t] ∧
    !![0, 0; 0, 0; ση, 0] * (!![0, σv] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [hz, mul_comm]
  · funext i
    simp [kf_laborG, hy]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply]

/-- Example 10.1.1, the printed measurement equation `y_t = G_tx_t + D(η_{t+1}, v_{t+1})'` is a
misprint: with `α = β = z = 0` and `v₀ = 1`, all other shocks `0`, the income process gives
`y₀ = 1` while the printed form gives `0`. -/
theorem example_10_1_1_misprint :
    ∃ (z e1 e2 y : ℕ → ℝ), (∀ t, z (t + 1) = 0 * z t + 1 * e1 (t + 1)) ∧
      (∀ t, y t = 0 + 0 * t + z t + 1 * e2 t) ∧
      (fun _ : Fin 1 => y 0) ≠ kf_laborG 0 *ᵥ ![0, 0, z 0] + !![0, 1] *ᵥ ![e1 1, e2 1] := by
  refine ⟨fun _ => 0, fun _ => 0, fun t => if t = 0 then 1 else 0,
    fun t => if t = 0 then 1 else 0, fun t => by simp, fun t => by simp, fun h => ?_⟩
  have := congrFun h 0
  simp [kf_laborG] at this

/-! ### The scalar filter -/

theorem kf_inv_fin_one (M : Matrix (Fin 1) (Fin 1) ℝ) : M⁻¹ 0 0 = (M 0 0)⁻¹ := by
  simp

/-- The scalar system `x_{t+1} = ax_t + cε¹_{t+1}`, `y_t = x_t + dε²_t`, `x₀ ∼ (x̄₀, s₀)`. -/
noncomputable def kf_scalarSys (a c d xbar0 s0 : ℝ) : KFSystem (Fin 1) (Fin 1) (Fin 1) (Fin 2) :=
  KFSystem.const !![a] 0 !![c, 0] 1 0 !![0, d] (fun _ => xbar0) !![s0]

/-- The scalar Riccati map `s ↦ aRs/(s + R) + q`. -/
noncomputable def kf_scalarRic (a R q s : ℝ) : ℝ := a * R * s / (s + R) + q

/-- The positive root of `s² + (R − aR − q)s − qR = 0`. -/
noncomputable def kf_scalarRoot (a R q : ℝ) : ℝ :=
  (-(R - a * R - q) + Real.sqrt ((R - a * R - q) ^ 2 + 4 * q * R)) / 2

theorem kf_scalar_CD (c d : ℝ) :
    (!![c, 0] : Matrix (Fin 1) (Fin 2) ℝ) * (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [mul_apply]

theorem kf_scalar_DD (d : ℝ) :
    ((!![0, d] : Matrix (Fin 1) (Fin 2) ℝ) * (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ) 0 0 =
      d ^ 2 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, add_zero,
    Fin.succ_zero_eq_one]
  ring

/-- The filter recursion of the scalar system (with `B = 0` and no measurement input):
`x̂_{t+1|t} = ax̂_{t|t−1} + aK_t(y_t − x̂_{t|t−1})`. -/
theorem kf_scalar_xpred (a c d xbar0 s0 : ℝ) {Ω : Type*} (y : ℕ → Ω → Fin 1 → ℝ)
    (u : ℕ → Ω → Fin 1 → ℝ) (t : ℕ) (ω : Ω) :
    (kf_scalarSys a c d xbar0 s0).xpred y 0 u (t + 1) ω 0 =
      a * (kf_scalarSys a c d xbar0 s0).xpred y 0 u t ω 0 +
        a * (kf_scalarSys a c d xbar0 s0).K t 0 0 *
          (y t ω 0 - (kf_scalarSys a c d xbar0 s0).xpred y 0 u t ω 0) := by
  rw [KFSystem.kf_pred_recursive]
  simp only [kf_app, KFSystem.innov, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, mulVec,
    dotProduct, Fin.sum_univ_one, Matrix.mul_apply, kf_scalarSys, KFSystem.const, of_apply,
    cons_val', empty_val', cons_val_fin_one, Matrix.zero_apply, zero_mul, add_zero,
    Matrix.one_apply_eq, one_mul, sub_zero]

/-- The dual Riccati operator of the scalar system, entrywise. -/
theorem kf_scalar_dualT (a c d : ℝ) (P : Matrix (Fin 1) (Fin 1) ℝ) (hp : P 0 0 + d ^ 2 ≠ 0) :
    (kf_dual !![a] (1 : Matrix (Fin 1) (Fin 1) ℝ) !![c, 0] !![0, d]).T P 0 0 =
      kf_scalarRic (a ^ 2) (d ^ 2) (c ^ 2) (P 0 0) := by
  have hinv := kf_inv_fin_one (!![0, d] * !![0, d]ᵀ + 1 * P * 1)
  simp only [LSProblem.T, kf_dual, LSProblem.G, LSProblem.N, one_smul, transpose_transpose,
    transpose_zero, zero_add, transpose_one, Matrix.one_mul, Matrix.mul_one] at hinv ⊢
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_zero, transpose_apply, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, hinv, add_zero, Fin.succ_zero_eq_one]
  rw [show 0 * 0 + d * d + P 0 0 = P 0 0 + d ^ 2 by ring, kf_scalarRic]
  field_simp
  ring

/-- The scalar filter (Miao, pp. 334–336): `Σ_{t|t−1} ≥ 0`,
`Σ_{t+1|t} = a²d²Σ_{t|t−1}/(Σ_{t|t−1} + d²) + c²`, `K_t = Σ_{t|t−1}/(Σ_{t|t−1} + d²)` and
`Ω_{t|t−1} = Σ_{t|t−1} + d²`, for `d ≠ 0`, `s₀ ≥ 0`. -/
theorem kf_scalar_filter (a c d xbar0 s0 : ℝ) (hd : d ≠ 0) (hs0 : 0 ≤ s0) (t : ℕ) :
    0 ≤ (kf_scalarSys a c d xbar0 s0).Spred t 0 0 ∧
      (kf_scalarSys a c d xbar0 s0).Spred (t + 1) 0 0 =
        kf_scalarRic (a ^ 2) (d ^ 2) (c ^ 2) ((kf_scalarSys a c d xbar0 s0).Spred t 0 0) ∧
      (kf_scalarSys a c d xbar0 s0).K t 0 0 = (kf_scalarSys a c d xbar0 s0).Spred t 0 0 /
        ((kf_scalarSys a c d xbar0 s0).Spred t 0 0 + d ^ 2) ∧
      (kf_scalarSys a c d xbar0 s0).Om t 0 0 =
        (kf_scalarSys a c d xbar0 s0).Spred t 0 0 + d ^ 2 := by
  have hS : kf_scalarSys a c d xbar0 s0 =
      KFSystem.const !![a] 0 !![c, 0] 1 0 !![0, d] (fun _ => xbar0) !![s0] := rfl
  rw [hS]
  set S := KFSystem.const !![a] 0 !![c, 0] 1 0 !![0, d] (fun _ => xbar0) !![s0] with hSdef
  have hd2 : 0 < d ^ 2 := by positivity
  have hrec : ∀ t, S.Spred (t + 1) = (kf_dual !![a] 1 !![c, 0] !![0, d]).T (S.Spred t) := by
    intro t
    rw [hSdef, (kf_const_Spred _ _ _ _ _ _ _ _ (kf_scalar_CD c d) (t + 1)).1,
      Function.iterate_succ_apply', ← (kf_const_Spred _ _ _ _ _ _ _ _ (kf_scalar_CD c d) t).1]
  have hnn : ∀ t, 0 ≤ S.Spred t 0 0 := by
    intro t
    induction t with
    | zero =>
      change 0 ≤ (!![s0] : Matrix (Fin 1) (Fin 1) ℝ) 0 0
      simpa using hs0
    | succ t ih =>
      rw [hrec, kf_scalar_dualT a c d _ (by positivity), kf_scalarRic]
      positivity
  refine ⟨hnn t, by rw [hrec, kf_scalar_dualT a c d _ (by linarith [hnn t])], ?_, ?_⟩
  · rw [hSdef, (kf_const_Spred _ _ _ _ _ _ _ _ (kf_scalar_CD c d) t).2, ← hSdef]
    have hinv := kf_inv_fin_one (1 * S.Spred t * 1ᵀ + !![0, d] * !![0, d]ᵀ)
    simp only [kf_steadyGain, transpose_one, Matrix.one_mul, Matrix.mul_apply, Fin.sum_univ_one,
      mul_one] at hinv ⊢
    rw [hinv, Matrix.add_apply, kf_scalar_DD, div_eq_mul_inv]
  · have hCl : S.Cl t * (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ = 0 := by
      cases t with
      | zero => exact Matrix.zero_mul _
      | succ t => exact kf_scalar_CD c d
    have hDC : (!![0, d] : Matrix (Fin 1) (Fin 2) ℝ) * (S.Cl t)ᵀ = 0 := by
      rw [← transpose_transpose (!![0, d] * (S.Cl t)ᵀ), transpose_mul, transpose_transpose, hCl,
        transpose_zero]
    simp only [KFSystem.Om, kf_Om]
    rw [show S.G t = 1 from rfl, show S.D t = !![0, d] from rfl, Matrix.mul_assoc 1 (S.Cl t),
      hCl, hDC]
    simp only [Matrix.mul_zero, add_zero, Matrix.one_mul, transpose_one, Matrix.mul_one,
      Matrix.add_apply, kf_scalar_DD, Matrix.zero_apply]

/-- The scalar Riccati map is nonnegative on `[0, ∞)`. -/
theorem kf_scalarRic_nonneg {a R q s : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    0 ≤ kf_scalarRic a R q s := by
  unfold kf_scalarRic
  have : 0 < s + R := by linarith
  positivity

/-- The scalar steady state (Miao, pp. 334–336): for `a ≥ 0`, `R > 0`, `q > 0` the root
`s* = (−(R − aR − q) + √((R − aR − q)² + 4qR))/2` is positive, is the unique nonnegative fixed
point of `s ↦ aRs/(s + R) + q`, and the iterates converge to it from every `s₀ ≥ 0` (the map is a
contraction with modulus `aR/(s* + R) < 1` towards `s*`). -/
theorem kf_scalar_tendsto {a R q : ℝ} (ha : 0 ≤ a) (hR : 0 < R) (hq : 0 < q) :
    0 < kf_scalarRoot a R q ∧ kf_scalarRic a R q (kf_scalarRoot a R q) = kf_scalarRoot a R q ∧
      (∀ s, 0 ≤ s → kf_scalarRic a R q s = s → s = kf_scalarRoot a R q) ∧
      ∀ s0, 0 ≤ s0 → Tendsto (fun t => (kf_scalarRic a R q)^[t] s0) atTop
        (𝓝 (kf_scalarRoot a R q)) := by
  set b := R - a * R - q
  set Δ := b ^ 2 + 4 * q * R
  set r := kf_scalarRoot a R q
  have hΔ : b ^ 2 < Δ := by simp only [Δ]; nlinarith
  have hsq : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt (by nlinarith)
  have hgt : b < Real.sqrt Δ ∧ -b < Real.sqrt Δ := by
    have h0 : |b| < Real.sqrt Δ := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hΔ
    exact ⟨lt_of_le_of_lt (le_abs_self b) h0, lt_of_le_of_lt (neg_le_abs b) h0⟩
  have hr : r = (-b + Real.sqrt Δ) / 2 := rfl
  have hrpos : 0 < r := by rw [hr]; linarith [hgt.1, hgt.2]
  have hquad : r ^ 2 + b * r - q * R = 0 := by
    rw [hr]
    nlinarith [hsq]
  have hfix : kf_scalarRic a R q r = r := by
    unfold kf_scalarRic
    have : r + R ≠ 0 := by linarith
    field_simp
    nlinarith [hquad]
  have hκ : a * R < r + R := by
    have h1 : r * (r + R - a * R) = q * (r + R) := by nlinarith [hquad]
    have h2 : 0 < r * (r + R - a * R) := by rw [h1]; positivity
    have := (pos_iff_pos_of_mul_pos h2).1 hrpos
    linarith
  refine ⟨hrpos, hfix, fun s hs hfs => ?_, fun s0 hs0 => ?_⟩
  · have hsR : s + R ≠ 0 := by linarith
    unfold kf_scalarRic at hfs
    field_simp at hfs
    have hq' : s ^ 2 + b * s - q * R = 0 := by simp only [b]; nlinarith [hfs]
    have hprod : (s - r) * (s + r + b) = 0 := by nlinarith [hquad, hq']
    have hpos : 0 < s + r + b := by rw [hr]; linarith [hgt.2]
    have := (mul_eq_zero.1 hprod).resolve_right hpos.ne'
    linarith
  · set κ := a * R / (r + R)
    have hκ0 : 0 ≤ κ := by positivity
    have hκ1 : κ < 1 := (div_lt_one (by linarith)).2 hκ
    have hcontr : ∀ s, 0 ≤ s → |kf_scalarRic a R q s - r| ≤ κ * |s - r| := by
      intro s hs
      have hsR : 0 < s + R := by linarith
      have hrR : 0 < r + R := by linarith
      have heq : kf_scalarRic a R q s - r = a * R * R * (s - r) / ((s + R) * (r + R)) := by
        conv_lhs => rw [← hfix]
        unfold kf_scalarRic
        field_simp
        ring
      rw [heq, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a * R * R),
        abs_of_pos (by positivity : 0 < (s + R) * (r + R))]
      rw [div_le_iff₀ (by positivity)]
      have : κ * |s - r| * ((s + R) * (r + R)) = a * R * |s - r| * (s + R) := by
        simp only [κ]
        field_simp
      rw [this]
      have habs := abs_nonneg (s - r)
      nlinarith [mul_nonneg (mul_nonneg ha hR.le) habs]
    have hnn : ∀ t, 0 ≤ (kf_scalarRic a R q)^[t] s0 := by
      intro t
      induction t with
      | zero => exact hs0
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        exact kf_scalarRic_nonneg ha hR hq.le ih
    have hbd : ∀ t, |(kf_scalarRic a R q)^[t] s0 - r| ≤ κ ^ t * |s0 - r| := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [Function.iterate_succ_apply', pow_succ]
        calc _ ≤ κ * |(kf_scalarRic a R q)^[t] s0 - r| := hcontr _ (hnn t)
          _ ≤ κ * (κ ^ t * |s0 - r|) := mul_le_mul_of_nonneg_left ih hκ0
          _ = κ ^ t * κ * |s0 - r| := by ring
    have hlim : Tendsto (fun t => κ ^ t * |s0 - r|) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const |s0 - r|
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun t => dist_nonneg) (fun t => by rw [Real.dist_eq]; exact hbd t) hlim

/-! ### Example 10.1.2 (Muth) -/

/-- **Example 10.1.2** (Muth, Miao, p. 334). The scalar system `x_{t+1} = x_t + η_{t+1}`,
`y_t = x_t + v_t`, `Eη² = Q`, `Ev² = R > 0`, `Σ₀ ≥ 0`: (i) `K_t = Σ_{t|t−1}/(Σ_{t|t−1} + R)` and
`Σ_{t+1|t} = (Σ_{t|t−1}(R + Q) + QR)/(Σ_{t|t−1} + R)`; (ii) the filter is
`x̂_{t+1|t} = (1 − K_t)x̂_{t|t−1} + K_ty_t`; (iii) for `Q > 0`,
`Σ_{t|t−1} → Σ = (Q + √(Q² + 4QR))/2`
and `K_t → K = Σ/(Σ + R)`. -/
theorem example_10_1_2 {Q R : ℝ} (hQ : 0 ≤ Q) (hR : 0 < R) (xbar0 s0 : ℝ) (hs0 : 0 ≤ s0)
    {Ω : Type*} (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) :
    (∀ t, (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0 =
        (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 /
          ((kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 + R) ∧
      (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred (t + 1) 0 0 =
        ((kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 * (R + Q) + Q * R) /
          ((kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0 + R)) ∧
    (∀ t ω, (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).xpred y 0 u (t + 1) ω 0 =
      (1 - (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0) *
        (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).xpred y 0 u t ω 0 +
      (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0 * y t ω 0) ∧
    (0 < Q → Tendsto (fun t => (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).Spred t 0 0)
        atTop (𝓝 ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2)) ∧
      Tendsto (fun t => (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0).K t 0 0) atTop
        (𝓝 ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 /
          ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 + R)))) := by
  set S := kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hQ2 : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ
  have hF := fun t => kf_scalar_filter 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s0 hd hs0 t
  have hrec : ∀ t, S.Spred (t + 1) 0 0 = kf_scalarRic 1 R Q (S.Spred t 0 0) := by
    intro t
    rw [(hF t).2.1, hR2, hQ2, one_pow]
  have hK : ∀ t, S.K t 0 0 = S.Spred t 0 0 / (S.Spred t 0 0 + R) := by
    intro t
    rw [(hF t).2.2.1, hR2]
  refine ⟨fun t => ⟨hK t, ?_⟩, fun t ω => ?_, fun hQp => ?_⟩
  · rw [hrec, kf_scalarRic]
    have : S.Spred t 0 0 + R ≠ 0 := by linarith [(hF t).1]
    field_simp
    ring
  · rw [kf_scalar_xpred]
    ring
  · have hSt : Tendsto (fun t => S.Spred t 0 0) atTop
        (𝓝 ((Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2)) := by
      have hroot : kf_scalarRoot 1 R Q = (Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 := by
        simp only [kf_scalarRoot]
        ring_nf
      rw [← hroot]
      have h := (kf_scalar_tendsto zero_le_one hR hQp).2.2.2 (S.Spred 0 0 0) (hF 0).1
      refine (tendsto_add_atTop_iff_nat 0).1 (h.congr fun t => ?_)
      induction t with
      | zero => rfl
      | succ t ih => rw [Function.iterate_succ_apply', ih, ← hrec]
    refine ⟨hSt, ?_⟩
    have hpos : 0 < (Q + Real.sqrt (Q ^ 2 + 4 * Q * R)) / 2 + R := by
      have := Real.sqrt_nonneg (Q ^ 2 + 4 * Q * R)
      linarith
    simp only [hK]
    exact hSt.div (hSt.add_const R) hpos.ne'

/-- Example 10.1.2 (Miao, p. 334): started at the steady state `Σ` (a fixed point of the Riccati
map), the gain is constant, `K_t = K`, and the filter is Cagan's adaptive expectations formula
`x̂_{t+1|t} = (1 − K)x̂_{t|t−1} + Ky_t`. -/
theorem example_10_1_2_adaptive {Q R : ℝ} (hR : 0 < R) (xbar0 : ℝ) {s : ℝ}
    (hfix : (kf_dual !![1] (1 : Matrix (Fin 1) (Fin 1) ℝ) !![Real.sqrt Q, 0]
      !![0, Real.sqrt R]).T !![s] = !![s]) (hs : 0 ≤ s)
    {Ω : Type*} (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) (t : ℕ) (ω : Ω) :
    (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).K t 0 0 = s / (s + R) ∧
      (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).xpred y 0 u (t + 1) ω 0 =
        (1 - s / (s + R)) * (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).xpred y 0 u t ω 0
          + s / (s + R) * y t ω 0 := by
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hP : (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).Spred t = !![s] :=
    (kf_steady_fixed _ _ _ _ _ _ _ (kf_scalar_CD _ _) hfix t).1
  have hK : (kf_scalarSys 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s).K t 0 0 = s / (s + R) := by
    rw [(kf_scalar_filter 1 (Real.sqrt Q) (Real.sqrt R) xbar0 s hd hs t).2.2.1, hP, hR2]
    simp
  refine ⟨hK, ?_⟩
  rw [kf_scalar_xpred, hK]
  ring

/-- Example 10.1.2 with `Q = 0` (Miao, pp. 334–335): `σ_{t+1} = σ_tR/(σ_t + R)` (with
`σ_t = Σ_{t|t−1}`), `K_t = σ_t/(σ_t + R)`, `m_t = (1 − K_t)m_{t−1} + K_ty_t`
(`m_{t−1} = x̂_{t|t−1}`),
and the variance of `K_ta_t`, `K_t²(σ_t + R)`, equals `K_tσ_t` (so `K_ta_t = √(K_tσ_t) ξ_t` with
`ξ_t` of unit variance). -/
theorem example_10_1_2_constant {R : ℝ} (hR : 0 < R) (xbar0 s0 : ℝ) (hs0 : 0 ≤ s0) (t : ℕ) :
    (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred (t + 1) 0 0 =
        (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 * R /
          ((kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 + R) ∧
      (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).K t 0 0 ^ 2 *
          ((kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 + R) =
        (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).K t 0 0 *
          (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 := by
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  obtain ⟨hnn, hrec, hK, -⟩ := kf_scalar_filter 1 0 (Real.sqrt R) xbar0 s0 hd hs0 t
  have hpos : (kf_scalarSys 1 0 (Real.sqrt R) xbar0 s0).Spred t 0 0 + R ≠ 0 := by linarith
  rw [hR2] at hrec hK
  refine ⟨?_, ?_⟩
  · rw [hrec, kf_scalarRic]
    field_simp
    ring
  · rw [hK]
    field_simp

/-! ### Example 10.1.3 -/

/-- **Example 10.1.3** (Miao, pp. 335–336), the stationary filter. With `φ = σ_η²/σ_v²` and
`b = 1 − ρ² − φ`, the stationary covariance `Σ = (σ_v²/2)(−b + √(b² + 4φ))` is the unique
nonnegative solution of `Σ = ρ²(1 − Σ(Σ + σ_v²)⁻¹)Σ + σ_η²`, the stationary gain is
`K = Σ/(Σ + σ_v²) = 1 − 2/(2 − b + √(b² + 4φ))`, and `K²(Σ + σ_v²) = KΣ`. The filter covariances
of the scalar system `(a, c, d) = (ρ, σ_η, σ_v)` converge to `Σ` from every `Σ₀ ≥ 0`, and the
innovation variance is `Ω_t = Σ_{t|t−1} + σ_v²` (`→ Σ + σ_v²`). -/
theorem example_10_1_3 {ρ ση σv : ℝ} (hη : ση ≠ 0) (hv : σv ≠ 0) (xbar0 s0 : ℝ) (hs0 : 0 ≤ s0) :
    let φ := ση ^ 2 / σv ^ 2
    let b := 1 - ρ ^ 2 - φ
    let Sg := σv ^ 2 / 2 * (-b + Real.sqrt (b ^ 2 + 4 * φ))
    0 < Sg ∧ Sg = ρ ^ 2 * (1 - Sg * (Sg + σv ^ 2)⁻¹) * Sg + ση ^ 2 ∧
      (∀ s, 0 ≤ s → s = ρ ^ 2 * (1 - s * (s + σv ^ 2)⁻¹) * s + ση ^ 2 → s = Sg) ∧
      Sg / (Sg + σv ^ 2) = 1 - 2 / (2 - b + Real.sqrt (b ^ 2 + 4 * φ)) ∧
      (Sg / (Sg + σv ^ 2)) ^ 2 * (Sg + σv ^ 2) = Sg / (Sg + σv ^ 2) * Sg ∧
      Tendsto (fun t => (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0) atTop (𝓝 Sg) ∧
      ∀ t, (kf_scalarSys ρ ση σv xbar0 s0).Om t 0 0 =
        (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0 + σv ^ 2 := by
  intro φ b Sg
  have hv2 : 0 < σv ^ 2 := by positivity
  have hη2 : 0 < ση ^ 2 := by positivity
  obtain ⟨hpos, hfix, huniq, hconv⟩ := kf_scalar_tendsto (sq_nonneg ρ) hv2 hη2
  have hroot : kf_scalarRoot (ρ ^ 2) (σv ^ 2) (ση ^ 2) = Sg := by
    simp only [kf_scalarRoot, Sg, b, φ]
    have h1 : (σv ^ 2 - ρ ^ 2 * σv ^ 2 - ση ^ 2) ^ 2 + 4 * ση ^ 2 * σv ^ 2 =
        (σv ^ 2) ^ 2 * ((1 - ρ ^ 2 - ση ^ 2 / σv ^ 2) ^ 2 + 4 * (ση ^ 2 / σv ^ 2)) := by
      field_simp
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hv2.le]
    field_simp
  have hform : ∀ s, 0 ≤ s → ρ ^ 2 * (1 - s * (s + σv ^ 2)⁻¹) * s + ση ^ 2 =
      kf_scalarRic (ρ ^ 2) (σv ^ 2) (ση ^ 2) s := by
    intro s hs
    have : s + σv ^ 2 ≠ 0 := by linarith
    unfold kf_scalarRic
    field_simp
    ring
  rw [hroot] at hpos hfix huniq hconv
  have hSg1 : Sg + σv ^ 2 ≠ 0 := by linarith
  have hsq : Real.sqrt (b ^ 2 + 4 * φ) ^ 2 = b ^ 2 + 4 * φ :=
    Real.sq_sqrt (by have : 0 ≤ φ := by positivity
                     nlinarith)
  have hSgdef : Sg = σv ^ 2 / 2 * (-b + Real.sqrt (b ^ 2 + 4 * φ)) := rfl
  refine ⟨hpos, by rw [hform _ hpos.le, hfix], fun s hs h => huniq s hs (by rw [← hform s hs,
    ← h]), ?_, by field_simp, ?_, fun t => ?_⟩
  · have h2 : 2 - b + Real.sqrt (b ^ 2 + 4 * φ) ≠ 0 := by
      have : 0 < -b + Real.sqrt (b ^ 2 + 4 * φ) := by
        have := hpos
        rw [hSgdef] at this
        exact (pos_iff_pos_of_mul_pos this).1 (by positivity)
      linarith
    rw [eq_sub_iff_add_eq, div_add_div _ _ hSg1 h2, div_eq_one_iff_eq (mul_ne_zero hSg1 h2),
      hSgdef]
    field_simp
    ring
  · have hd : σv ≠ 0 := hv
    have hF := fun t => kf_scalar_filter ρ ση σv xbar0 s0 hd hs0 t
    have h := hconv ((kf_scalarSys ρ ση σv xbar0 s0).Spred 0 0 0) (hF 0).1
    refine (h.congr fun t => ?_)
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', ih, ← (hF t).2.1]
  · exact (kf_scalar_filter ρ ση σv xbar0 s0 hv hs0 t).2.2.2

/-- Example 10.1.3 (Miao, pp. 335–336), the filter in levels: with `y_t = z_t − z_{t−1}`, the
deviation-form filter `m̃_{t+1} = ρm̃_t + K(ỹ_{t+1} − ρm̃_t)` (`m̃ = x̂ − g`, `ỹ = y − g`) is
`x̂_{t+1|t+1} = ρx̂_{t|t} + (1 − ρ)g + Ka_{t+1}`,
`a_{t+1} = z_{t+1} − z_t − ρx̂_{t|t} − (1 − ρ)g`. -/
theorem example_10_1_3_filter (ρ g K : ℝ) (m z : ℕ → ℝ)
    (hm : ∀ t, m (t + 1) - g = ρ * (m t - g) + K * ((z (t + 1) - z t - g) - ρ * (m t - g)))
    (t : ℕ) :
    m (t + 1) = ρ * m t + (1 - ρ) * g + K * (z (t + 1) - z t - ρ * m t - (1 - ρ) * g) := by
  linear_combination hm t

/-! ### Example 10.1.4 -/

/-- The `N(0, Ω)` density formula `(2π)^{−n/2}|Ω|^{−1/2}exp(−½a'Ω⁻¹a)`. -/
noncomputable def kf_gaussDens {Y : Type*} [Fintype Y] [DecidableEq Y] (Om : Matrix Y Y ℝ)
    (a : Y → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(Fintype.card Y : ℝ) / 2) * Om.det ^ (-(1 : ℝ) / 2) *
    Real.exp (-(1 / 2) * (a ⬝ᵥ (Om⁻¹ *ᵥ a)))

/-- The Gaussian log density `−(n/2)ln 2π − ½ln|Ω| − ½a'Ω⁻¹a`. -/
noncomputable def kf_logDens {Y : Type*} [Fintype Y] [DecidableEq Y] (Om : Matrix Y Y ℝ)
    (a : Y → ℝ) : ℝ :=
  -(Fintype.card Y / 2) * Real.log (2 * Real.pi) - 1 / 2 * Real.log Om.det -
    1 / 2 * (a ⬝ᵥ (Om⁻¹ *ᵥ a))

/-- **Example 10.1.4** (Miao, pp. 336–337): for `|Ω_t| > 0`, the log-likelihood
`∑_{t=1}^T ln p(y_t|y^{t−1})`, each factor the `N(ŷ_{t|t−1}, Ω_{t|t−1})` density at `y_t`, i.e. the
`N(0, Ω_t)` density at the innovation `a_t`, is
`−(n_yT/2)ln 2π − ½∑ln|Ω_t| − ½∑a_t'Ω_t⁻¹a_t`. -/
theorem example_10_1_4 {Y : Type*} [Fintype Y] [DecidableEq Y] (Om : ℕ → Matrix Y Y ℝ)
    (a : ℕ → Y → ℝ) (T : ℕ) (hdet : ∀ t, 0 < (Om t).det) :
    (∀ t, Real.log (kf_gaussDens (Om t) (a t)) = kf_logDens (Om t) (a t)) ∧
      ∑ t ∈ Finset.Icc 1 T, Real.log (kf_gaussDens (Om t) (a t)) =
        -(Fintype.card Y * T / 2) * Real.log (2 * Real.pi) -
          1 / 2 * ∑ t ∈ Finset.Icc 1 T, Real.log (Om t).det -
          1 / 2 * ∑ t ∈ Finset.Icc 1 T, a t ⬝ᵥ ((Om t)⁻¹ *ᵥ a t) := by
  have hlog : ∀ t, Real.log (kf_gaussDens (Om t) (a t)) = kf_logDens (Om t) (a t) := by
    intro t
    have h2 : 0 < 2 * Real.pi := by positivity
    unfold kf_gaussDens kf_logDens
    have h3 := Real.rpow_pos_of_pos h2 (-(Fintype.card Y : ℝ) / 2)
    have h4 := Real.rpow_pos_of_pos (hdet t) (-(1 : ℝ) / 2)
    rw [Real.log_mul (mul_pos h3 h4).ne' (Real.exp_pos _).ne', Real.log_mul h3.ne' h4.ne',
      Real.log_rpow h2, Real.log_rpow (hdet t), Real.log_exp]
    ring
  refine ⟨hlog, ?_⟩
  simp only [hlog, kf_logDens, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  ring

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Linear-quadratic control under partial information

Miao, §10.3, pp. 342–345. The LQ problem `max −E∑βᵗr(x_t, u_t)`, `x_{t+1} = Ax_t + Bu_t + η_{t+1}`,
`y_t = Gx_t + v_t`, when the decision maker observes only `y^t`. The book sketches the separation
principle (certainty equivalence): with the (stationary) Kalman filter, the value function is
`V(x̂_{t|t}) = −½x̂'_{t|t}Px̂_{t|t} + constant` with the same `P` as under full information (9.12),
and the policy is `u_t = −Fx̂_{t|t}` with the same `F` (9.17).

The project's LQ conventions (Chapter 9) are used: the loss is `r(x, u) = x'Qx + u'Ru + 2x'Su`
(the book's `r` without the factor `½`) and `V(x) = −x'Px − d`.

* `kf_Delta_succ`: `Δ_t = x_t − x̂_{t|t}` satisfies `Δ_{t+1} = AΔ_t + Cε_{t+1} − K_{t+1}a_{t+1}`
  (the book's `Δ_t = Ax_{t−1} + η_t − Ax̂_{t−1|t−1} − Ka_t`; the control terms cancel), and it
  does not depend on the controls (`KFSystem.kf_err_control_free`).
* `kf_expected_loss`: `E_t r(x̂ + Δ, u) = r(x̂, u) + E_tΔ'QΔ` when `Δ` has conditional mean zero —
  the decomposition `E_t[x'Qx + u'Ru + 2x'Su] = x̂'Qx̂ + u'Ru + 2x̂'Su + …` of p. 344.
* `kf_expected_cont`: with the filter law of motion `x̂_{t+1|t+1} = Ax̂_{t|t} + Bu_t + K a_{t+1}`
  (`KFSystem.kf_filt_recursive`) and `Ka_{t+1} = (KW)ξ_{t+1}`, `WW' = Ω`, `ξ` with mean zero and
  second moments `I`: `E_t x̂'_{t+1|t+1}Px̂_{t+1|t+1} = (Ax̂ + Bu)'P(Ax̂ + Bu) + tr(PKWW'K')`.
* `kf_certainty_equivalence` (**the separation principle**, pp. 343–345): the partial-information
  Bellman equation `V(x̂) = max_u {−E_t r(x̂ + Δ, u) + βE_tV(Ax̂ + Bu + KWξ)}` is solved by
  `V(x̂) = −x̂'Px̂ − d̂` with `P` the full-information Riccati fixed point (9.12), maximised exactly
  at `u = −F(P)x̂` with the full-information gain (9.17); only the constant changes:
  `d̂ = (1 − β)⁻¹(E Δ'QΔ + β tr(PKWW'K'))` instead of `(1 − β)⁻¹β tr(PCC')`
  (`LSProblem.eq_9_16_9_17`). The Riccati operator and gain do not depend on the shock loading
  (`kf_filt_T`).

Reading: the conditional laws given `y^t` are represented by a probability law `κ` of the
filtered error `Δ_t` (mean zero) and a law `ν` of the standardised innovation (mean zero, second
moments `I`); that `Δ_t` and `a_{t+1}` are conditionally mean zero given `y^t` and independent of
the control is the Gaussian reading of §10.1.1, whose second-moment content is `KFFilter`.
-/

open MeasureTheory Matrix

namespace Miao.PartialInformation

variable {X U E : Type*} [Fintype X] [Fintype U] [Fintype E]

namespace KFSystem

variable {Y : Type*} [Fintype Y] [DecidableEq X] [DecidableEq Y] (S : KFSystem X U Y E)
  {Ω : Type*} {x : ℕ → Ω → X → ℝ} {y h : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ}
  {ε : ℕ → Ω → E → ℝ}

/-- Miao, p. 344: the filtered error `Δ_t = x_t − x̂_{t|t}` satisfies
`Δ_{t+1} = A_tΔ_t + C_tε_{t+1} − K_{t+1}a_{t+1}` (the control terms cancel). -/
theorem kf_Delta_succ
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1))) (t : ℕ) :
    x (t + 1) - S.xfilt y h u (t + 1) = kf_app (S.A t) (x t - S.xfilt y h u t) +
      kf_app (S.C t) (ε (t + 1)) - kf_app (S.K (t + 1)) (S.innov y h u (t + 1)) := by
  rw [S.kf_filt_err, S.kf_err_succ hx, ← S.kf_filt_err]

end KFSystem

variable [DecidableEq U] [DecidableEq E]

/-- The filtered-state problem: the LQ problem `L` with the shock loading replaced by `KW`
(the law of motion `x̂_{t+1|t+1} = Ax̂_{t|t} + Bu_t + KWξ_{t+1}`). -/
def kf_filtProblem {E' : Type*} (L : LSProblem X U E') (KW : Matrix X E ℝ) : LSProblem X U E :=
  ⟨L.A, L.B, KW, L.Q, L.R, L.S, L.β⟩

omit [Fintype E] [DecidableEq E] in
/-- Miao, p. 343: the Riccati operator (9.12) and the gain (9.17) of the filtered-state problem
are those of the full-information problem: they do not involve the shock loading. -/
theorem kf_filt_T {E' : Type*} (L : LSProblem X U E') (KW : Matrix X E ℝ) :
    (kf_filtProblem L KW).T = L.T ∧ (kf_filtProblem L KW).F = L.F := ⟨rfl, rfl⟩

omit [Fintype U] [Fintype E] [DecidableEq U] [DecidableEq E] in
/-- The expansion `r(x̂ + Δ, u) = r(x̂, u) + ℓ'Δ + Δ'QΔ` with `ℓ = Q'x̂ + Qx̂ + 2Su`. -/
theorem kf_loss_expand [Fintype U] (L : LSProblem X U E) (xh δ : X → ℝ) (v : U → ℝ) :
    L.loss (xh + δ) v = L.loss xh v +
      (xh ᵥ* L.Q + L.Q *ᵥ xh + (2 : ℝ) • (L.S *ᵥ v)) ⬝ᵥ δ + δ ⬝ᵥ (L.Q *ᵥ δ) := by
  simp only [LSProblem.loss, mulVec_add, dotProduct_add, add_dotProduct, smul_dotProduct,
    smul_eq_mul, dotProduct_mulVec xh L.Q δ, dotProduct_comm δ (L.Q *ᵥ xh),
    dotProduct_comm δ (L.S *ᵥ v)]
  ring

omit [Fintype U] [Fintype E] [DecidableEq U] [DecidableEq E] in
/-- Miao, p. 344: if the estimation error `Δ` has (conditional) law `κ` with mean zero and
integrable second moments, then `E_t r(x̂ + Δ, u) = r(x̂, u) + E_tΔ'QΔ`; the second term does not
depend on the control. -/
theorem kf_expected_loss [Fintype U] (L : LSProblem X U E) {κ : Measure (X → ℝ)}
    [IsProbabilityMeasure κ] (h1 : ∀ k, Integrable (fun δ : X → ℝ => δ k) κ)
    (h2 : ∀ k l, Integrable (fun δ : X → ℝ => δ k * δ l) κ) (hm : ∀ k, ∫ δ, δ k ∂κ = 0)
    (xh : X → ℝ) (v : U → ℝ) :
    Integrable (fun δ => L.loss (xh + δ) v) κ ∧
      ∫ δ, L.loss (xh + δ) v ∂κ = L.loss xh v + ∫ δ, δ ⬝ᵥ (L.Q *ᵥ δ) ∂κ := by
  set ℓ := xh ᵥ* L.Q + L.Q *ᵥ xh + (2 : ℝ) • (L.S *ᵥ v)
  have hq : ∀ δ : X → ℝ, δ ⬝ᵥ (L.Q *ᵥ δ) = ∑ k, ∑ l, L.Q k l * (δ k * δ l) := by
    intro δ
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hqi : Integrable (fun δ : X → ℝ => δ ⬝ᵥ (L.Q *ᵥ δ)) κ := by
    simp only [hq]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (h2 k l).const_mul _
  have hli : Integrable (fun δ : X → ℝ => ℓ ⬝ᵥ δ) κ := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun k _ => (h1 k).const_mul _
  have hl0 : ∫ δ, ℓ ⬝ᵥ δ ∂κ = 0 := by
    simp only [dotProduct]
    rw [integral_finsetSum _ fun k _ => (h1 k).const_mul _]
    simp [integral_const_mul, hm]
  have hI : Integrable (fun δ : X → ℝ => (L.loss xh v + ℓ ⬝ᵥ δ) + δ ⬝ᵥ (L.Q *ᵥ δ)) κ :=
    ((integrable_const _).add hli).add hqi
  have e : (fun δ => L.loss (xh + δ) v) =
      fun δ : X → ℝ => (L.loss xh v + ℓ ⬝ᵥ δ) + δ ⬝ᵥ (L.Q *ᵥ δ) :=
    funext fun δ => kf_loss_expand L xh δ v
  rw [e]
  refine ⟨hI, ?_⟩
  have hA : Integrable (fun δ : X → ℝ => L.loss xh v + ℓ ⬝ᵥ δ) κ := (integrable_const _).add hli
  rw [integral_add hA hqi, integral_add (integrable_const _) hli, hl0, integral_const,
    probReal_univ, one_smul, add_zero]

omit [Fintype U] [DecidableEq U] in
/-- Miao, p. 344: with the filter law of motion `x̂_{t+1|t+1} = Ax̂_{t|t} + Bu_t + KWξ_{t+1}`,
`E_t x̂'_{t+1|t+1}Px̂_{t+1|t+1} = (Ax̂_{t|t} + Bu_t)'P(Ax̂_{t|t} + Bu_t) + tr(P(KW)(KW)')`; the
second term does not depend on the control. -/
theorem kf_expected_cont {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (z : X → ℝ)
    (KW : Matrix X E ℝ) (P : Matrix X X ℝ) :
    ∫ e, (z + KW *ᵥ e) ⬝ᵥ (P *ᵥ (z + KW *ᵥ e)) ∂ν = z ⬝ᵥ (P *ᵥ z) + trace (P * KW * KWᵀ) :=
  (ls_integral_quad hν z KW P).2

/-- The partial-information Bellman objective (Miao, pp. 344–345):
`−E_t r(x̂ + Δ, u) + βE_t W(Ax̂ + Bu + KWξ)`, with `Δ ∼ κ` and `ξ ∼ ν`. -/
noncomputable def kf_piObj (L : LSProblem X U E) (κ : Measure (X → ℝ)) (ν : Measure (E → ℝ))
    (W : (X → ℝ) → ℝ) (xh : X → ℝ) (v : U → ℝ) : ℝ :=
  -∫ δ, L.loss (xh + δ) v ∂κ + L.β * ∫ e, W (L.A *ᵥ xh + L.B *ᵥ v + L.C *ᵥ e) ∂ν

/-- **The separation principle / certainty equivalence** (Miao, §10.3, pp. 343–345). Let `L` be
the filtered-state LQ problem (its shock loading `C = KW` is the filter's innovation loading),
`R > 0`, `0 ≤ β < 1`, `P ≥ 0` a fixed point `P = T(P)` of the full-information Riccati equation
(9.12), `κ` the law of the estimation error (mean zero, integrable second moments), `ν` the law
of the standardised innovation. Then with `d̂ = (1 − β)⁻¹(EΔ'QΔ + β tr(PCC'))` the function
`V(x̂) = −x̂'Px̂ − d̂` solves the partial-information Bellman equation: `V(x̂)` is the maximum over
`u` of `−E_t r(x̂ + Δ, u) + βE_tV(Ax̂ + Bu + Cξ)`, attained exactly at `u = −F(P)x̂`, the
full-information policy (9.17) applied to the filtered state. -/
theorem kf_certainty_equivalence (L : LSProblem X U E) {κ : Measure (X → ℝ)}
    [IsProbabilityMeasure κ] (h1 : ∀ k, Integrable (fun δ : X → ℝ => δ k) κ)
    (h2 : ∀ k l, Integrable (fun δ : X → ℝ => δ k * δ l) κ) (hm : ∀ k, ∫ δ, δ k ∂κ = 0)
    {ν : Measure (E → ℝ)} (hν : LSShockLaw ν) (hR : L.R.PosDef) (hβ0 : 0 ≤ L.β)
    (hβ1 : L.β < 1) {P : Matrix X X ℝ} (hP : P.PosSemidef) (hfix : L.T P = P) (xh : X → ℝ) :
    let dh := (1 - L.β)⁻¹ * (∫ δ, δ ⬝ᵥ (L.Q *ᵥ δ) ∂κ + L.β * trace (P * L.C * L.Cᵀ))
    IsGreatest (Set.range (kf_piObj L κ ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh))
        (-(xh ⬝ᵥ (P *ᵥ xh)) - dh) ∧
      ∀ v, kf_piObj L κ ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh v = -(xh ⬝ᵥ (P *ᵥ xh)) - dh ↔
        v = -(L.F P *ᵥ xh) := by
  intro dh
  set c := ∫ δ, δ ⬝ᵥ (L.Q *ᵥ δ) ∂κ
  have hobj : ∀ v, kf_piObj L κ ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh v =
      L.bellObj ν (fun z => -(z ⬝ᵥ (P *ᵥ z)) - dh) xh v - c := by
    intro v
    rw [kf_piObj, LSProblem.bellObj, (kf_expected_loss L h1 h2 hm xh v).2]
    ring
  have hd : -(xh ⬝ᵥ (P *ᵥ xh)) - (L.β * trace (P * L.C * L.Cᵀ) + L.β * dh) - c =
      -(xh ⬝ᵥ (P *ᵥ xh)) - dh := by
    have : (1 - L.β) ≠ 0 := by linarith
    simp only [dh, c]
    field_simp
    ring
  obtain ⟨hg, hiff⟩ := L.bellObj_isGreatest hν hR hP hβ0 dh xh
  rw [hfix] at hg hiff
  refine ⟨⟨⟨-(L.F P *ᵥ xh), ?_⟩, ?_⟩, fun v => ?_⟩
  · rw [hobj, (hiff _).2 rfl, hd]
  · rintro _ ⟨v, rfl⟩
    rw [hobj, ← hd]
    exact sub_le_sub_right (hg.2 ⟨v, rfl⟩) c
  · rw [hobj, ← hd, sub_left_inj]
    exact hiff v

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercises 10.1–10.5

Miao, §10.4, p. 345 (items 1–5). All filters are in the linear-projection (second-moment) reading
of `KFFilter`.

* **Exercise 10.1**: `y_t = μ + ε_t + bε_{t−1}` in the form (10.3)–(10.4) with
  `x_t = (ε_t, ε_{t−1})'`
  and `z_t = 1` (`ex_10_1`).
* **Exercise 10.2**: with `ρ` unknown, the state `(ρ, z_t)` has the non-linear transition
  `(ρ, z) ↦ (ρ, ρz)`, which no matrix represents (`ex_10_2_nonlinear`): the Kalman filter does not
  apply to `(ρ, z_t)`. What is proved is the Kalman filter conditional on `ρ` (`ex_10_2`): the
  scalar filter with `a = ρ`, `c = σ_η`, `d = σ_v`, its gain and Riccati recursion, and its
  convergence. (A filter for the unknown `ρ` would be a non-linear filter, §10.1.2.)
* **Exercise 10.3**: `x_t = θ`, `y_t = θ + v_t`, `θ ∼ (μ, Σ₀)`: `Σ_{t|t−1} = Σ₀R/(R + tΣ₀)`,
  `K_t = Σ₀/(R + (t + 1)Σ₀)`, `x̂_{t|t−1} = (Rμ + Σ₀∑_{s<t}y_s)/(R + tΣ₀)` (`ex_10_3`); in the
  long run `Σ_{t|t−1} → 0` and `K_t → 0`, and the mean squared error of `x̂_{t|t}` tends to `0`
  (`ex_10_3_mse`).
* **Exercise 10.4**: the timing `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}`, `y_{t+1} = Gx_t + Hu_t +
  Dε_{t+1}`. The filter `x̂_{t+1} = Ax̂_t + Bu_t + K_t(y_{t+1} − Gx̂_t − Hu_t)` with
  `K_t = (AΣ_tG' + CD')(GΣ_tG' + DD')⁻¹` and `Σ_{t+1} = T̂(Σ_t)`, `T̂` the Riccati operator (9.11)
  of
  the dual LQ problem `(A', G', CC', DD', CD', β = 1)` (`kf_ex4Dual`): the error recursion, the
  second moments `Σ_t`, and the optimality of `K_t` among all gains (`ex_10_4_err`, `ex_10_4_gain`,
  `ex_10_4`). The "equivalent" second form `x_{t+1} = Ax_t + Bu_t + Cε_t`,
  `y_t = Gx_t + Hu_{t−1} + Dε_t` is the first form after re-dating the shock and the observation,
  but with `Hu_{t−1}` in place of `Hu_t` (`ex_10_4_equiv`); the control term does not affect the
  filter covariances.
* **Exercise 10.5**: the representation (10.3)–(10.4) is the system (10.1)–(10.2) with `B = 0` and
  the known measurement input `h_t = Hz_t`; the filter is `x̂_{t+1|t} = Ax̂_{t|t−1} +
  AK_t(y_t − Gx̂_{t|t−1} − Hz_t)` with the covariances of `KFFilter` (`ex_10_5`). The book's
  assumption that `z_t` is independent of `x_s, ε_s` (`s ≥ t`) is not needed: the estimation error
  does not depend on `z`.
-/

open Filter Topology Matrix MeasureTheory

open scoped MatrixOrder

namespace Miao.PartialInformation

/-! ### Exercise 10.1 -/

/-- **Exercise 10.1** (Miao, p. 345): `y_t = μ + ε_t + bε_{t−1}` has the state-space form
`x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = Gx_t + Hz_t` with `x_t = (ε_t, ε_{t−1})'`, `z_t = 1`,
`A = [0 0; 1 0]`, `C = (1, 0)'`, `G = [1 b]`, `H = μ`, `D = 0`. -/
theorem ex_10_1 (m b : ℝ) (ε y : ℤ → ℝ) (hy : ∀ t, y t = m + ε t + b * ε (t - 1)) (t : ℤ) :
    ![ε (t + 1), ε (t + 1 - 1)] = !![0, 0; 1, 0] *ᵥ ![ε t, ε (t - 1)] +
      !![1; 0] *ᵥ ![ε (t + 1)] ∧
    (fun _ : Fin 1 => y t) = !![1, b] *ᵥ ![ε t, ε (t - 1)] + !![m] *ᵥ ![1] := by
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i <;> simp
  · funext i
    simp [hy]
    ring

/-! ### Exercise 10.2 -/

/-- Exercise 10.2 (Miao, p. 345): with `ρ` unknown, the transition `(ρ, z) ↦ (ρ, ρz)` of the state
`(ρ, z_t)` is not linear: no matrix `A` satisfies `A(ρ, z)' = (ρ, ρz)'` for all `ρ, z`. -/
theorem ex_10_2_nonlinear :
    ¬ ∃ A : Matrix (Fin 2) (Fin 2) ℝ, ∀ r z : ℝ, A *ᵥ ![r, z] = ![r, r * z] := by
  rintro ⟨A, hA⟩
  have h1 := congrFun (hA 1 1) 1
  have h2 := congrFun (hA 2 2) 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
  linarith

/-- **Exercise 10.2** (Miao, p. 345), the Kalman filter conditional on `ρ`: for Example 10.1.1 with
`α = β = 0` (`z_{t+1} = ρz_t + σ_ηe¹_{t+1}`, `y_t = z_t + σ_ve²_t`), `Σ_{t+1|t} =
ρ²σ_v²Σ_{t|t−1}/(Σ_{t|t−1} + σ_v²) + σ_η²`, `K_t = Σ_{t|t−1}/(Σ_{t|t−1} + σ_v²)`,
`ẑ_{t+1|t} = ρẑ_{t|t−1} + ρK_t(y_t − ẑ_{t|t−1})`, and for `σ_η ≠ 0` the covariances converge to
the positive root `kf_scalarRoot (ρ²) σ_v² σ_η²`. -/
theorem ex_10_2 (ρ ση σv xbar0 s0 : ℝ) (hη : ση ≠ 0) (hv : σv ≠ 0) (hs0 : 0 ≤ s0) {Ω : Type*}
    (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) :
    (∀ t, (kf_scalarSys ρ ση σv xbar0 s0).Spred (t + 1) 0 0 =
        kf_scalarRic (ρ ^ 2) (σv ^ 2) (ση ^ 2) ((kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0) ∧
      (kf_scalarSys ρ ση σv xbar0 s0).K t 0 0 = (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0 /
        ((kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0 + σv ^ 2)) ∧
    (∀ t ω, (kf_scalarSys ρ ση σv xbar0 s0).xpred y 0 u (t + 1) ω 0 =
      ρ * (kf_scalarSys ρ ση σv xbar0 s0).xpred y 0 u t ω 0 +
        ρ * (kf_scalarSys ρ ση σv xbar0 s0).K t 0 0 *
          (y t ω 0 - (kf_scalarSys ρ ση σv xbar0 s0).xpred y 0 u t ω 0)) ∧
    Tendsto (fun t => (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0) atTop
      (𝓝 (kf_scalarRoot (ρ ^ 2) (σv ^ 2) (ση ^ 2))) := by
  have hF := fun t => kf_scalar_filter ρ ση σv xbar0 s0 hv hs0 t
  refine ⟨fun t => ⟨(hF t).2.1, (hF t).2.2.1⟩, fun t ω => kf_scalar_xpred _ _ _ _ _ y u t ω, ?_⟩
  have hv2 : 0 < σv ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hv))
  have hη2 : 0 < ση ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hη))
  have h := (kf_scalar_tendsto (sq_nonneg ρ) hv2 hη2).2.2.2
    ((kf_scalarSys ρ ση σv xbar0 s0).Spred 0 0 0) (hF 0).1
  refine h.congr fun t => ?_
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, ← (hF t).2.1]

/-! ### Exercise 10.3 -/

/-- **Exercise 10.3** (Miao, p. 345): `x_t = θ`, `y_t = θ + v_t`, `θ ∼ (μ, Σ₀)`, `Ev² = R > 0`
(the scalar system with `a = 1`, `c = 0`, `d = √R`). Then `Σ_{t|t−1} = Σ₀R/(R + tΣ₀)`,
`K_t = Σ₀/(R + (t + 1)Σ₀)`, the estimate is `x̂_{t|t−1} = (Rμ + Σ₀∑_{s<t}y_s)/(R + tΣ₀)`, and in the
long run `Σ_{t|t−1} → 0` and `K_t → 0`. -/
theorem ex_10_3 {R : ℝ} (hR : 0 < R) (m s0 : ℝ) (hs0 : 0 ≤ s0) {Ω : Type*}
    (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) :
    (∀ t : ℕ, (kf_scalarSys 1 0 (Real.sqrt R) m s0).Spred t 0 0 = s0 * R / (R + t * s0)) ∧
      (∀ t : ℕ, (kf_scalarSys 1 0 (Real.sqrt R) m s0).K t 0 0 = s0 / (R + (t + 1) * s0)) ∧
      (∀ (t : ℕ) ω, (kf_scalarSys 1 0 (Real.sqrt R) m s0).xpred y 0 u t ω 0 =
        (R * m + s0 * ∑ s ∈ Finset.range t, y s ω 0) / (R + t * s0)) ∧
      Tendsto (fun t => (kf_scalarSys 1 0 (Real.sqrt R) m s0).Spred t 0 0) atTop (𝓝 0) ∧
      Tendsto (fun t => (kf_scalarSys 1 0 (Real.sqrt R) m s0).K t 0 0) atTop (𝓝 0) := by
  set S := kf_scalarSys 1 0 (Real.sqrt R) m s0
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hF := fun t => kf_scalar_filter 1 0 (Real.sqrt R) m s0 hd hs0 t
  have hden : ∀ t : ℕ, 0 < R + t * s0 := fun t => by positivity
  have hP : ∀ t : ℕ, S.Spred t 0 0 = s0 * R / (R + t * s0) := by
    intro t
    induction t with
    | zero =>
      change (!![s0] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = _
      simp only [of_apply, cons_val', empty_val', cons_val_fin_one, Nat.cast_zero, zero_mul,
        add_zero]
      field_simp
    | succ t ih =>
      rw [(hF t).2.1, hR2, ih, kf_scalarRic]
      have h1 := hden t
      have h2 := hden (t + 1)
      push_cast at h2 ⊢
      field_simp
      ring
  have hK : ∀ t : ℕ, S.K t 0 0 = s0 / (R + (t + 1) * s0) := by
    intro t
    rw [(hF t).2.2.1, hR2, hP]
    have h1 := hden t
    have h2 : 0 < R + (t + 1) * s0 := by positivity
    field_simp
    ring
  have hlim : ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ,
      Tendsto (fun t : ℕ => c * s0 / (R + (t + k) * s0)) atTop (𝓝 0) := by
    intro k hk c
    rcases hs0.eq_or_lt with h0 | hpos
    · simp [← h0]
    · have h1 : Tendsto (fun t : ℕ => R + ((t : ℝ) + k) * s0) atTop atTop := by
        refine tendsto_atTop_add_const_left _ R ?_
        refine Tendsto.atTop_mul_const hpos ?_
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact Tendsto.div_atTop tendsto_const_nhds h1
  refine ⟨hP, hK, fun t ω => ?_, ?_, ?_⟩
  · induction t with
    | zero =>
      change S.xbar0 0 = _
      simp only [S, kf_scalarSys, KFSystem.const, Finset.range_zero, Finset.sum_empty, mul_zero,
        add_zero, Nat.cast_zero, zero_mul]
      field_simp
    | succ t ih =>
      rw [kf_scalar_xpred, ih, hK, Finset.sum_range_succ]
      have h1 := hden t
      have h2 : 0 < R + (t + 1) * s0 := by positivity
      push_cast
      field_simp
      ring
  · refine (hlim 0 le_rfl R).congr fun t => ?_
    rw [hP, add_zero, mul_comm R]
  · refine (hlim 1 zero_le_one 1).congr fun t => ?_
    rw [hK, one_mul]

/-- **Exercise 10.3** (Miao, p. 345), "what happens in the long run": under the hypotheses of
`KFSystem.kf_moments`, the mean squared error of the filtered estimate,
`E(θ − x̂_{t|t})² = Σ_{t|t}`, tends to `0` (the estimate converges to `θ` in mean square). -/
theorem ex_10_3_mse {R : ℝ} (hR : 0 < R) (m s0 : ℝ) (hs0 : 0 ≤ s0) {Ω : Type*}
    {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {x : ℕ → Ω → Fin 1 → ℝ} {y : ℕ → Ω → Fin 1 → ℝ} {u : ℕ → Ω → Fin 1 → ℝ}
    {ε : ℕ → Ω → Fin 2 → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).A t) (x t) +
      kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).B t) (u t) +
      kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).C t) (ε (t + 1)))
    (hy : ∀ t, y t = kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).G t) (x t) +
      (0 : ℕ → Ω → Fin 1 → ℝ) t +
      kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).D t) (ε t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t))
    (hm0 : kf_mean μ (x 0) = (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0)
      (x 0 - fun _ => (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0) =
      (kf_scalarSys 1 0 (Real.sqrt R) m s0).S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0)
      (ε t) = 0) :
    Tendsto (fun t => var_mom μ (x t - (kf_scalarSys 1 0 (Real.sqrt R) m s0).xfilt y 0 u t)
      (x t - (kf_scalarSys 1 0 (Real.sqrt R) m s0).xfilt y 0 u t) 0 0) atTop (𝓝 0) := by
  set S := kf_scalarSys 1 0 (Real.sqrt R) m s0
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hF := fun t => kf_scalar_filter 1 0 (Real.sqrt R) m s0 hd hs0 t
  have hΩ : ∀ t, IsUnit (S.Om t).det := by
    intro t
    rw [det_fin_one, (hF t).2.2.2, isUnit_iff_ne_zero]
    have := (hF t).1
    have : 0 < Real.sqrt R ^ 2 := by positivity
    linarith
  have hlim := ((ex_10_3 hR m s0 hs0 (fun _ _ _ => (0 : ℝ)) u).2.2.2.1).comp
    (tendsto_add_atTop_nat 1)
  refine hlim.congr fun t => ?_
  rw [Function.comp_apply, S.kf_filt_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
  change ((!![1] : Matrix (Fin 1) (Fin 1) ℝ) * S.Sfilt t * (!![1] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ +
    (!![0, 0] : Matrix (Fin 1) (Fin 2) ℝ) * (!![0, 0] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ) 0 0 =
    S.Sfilt t 0 0
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    transpose_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, Fin.succ_zero_eq_one]
  ring

/-! ### Exercise 10.4 -/

variable {X U Y E : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X]
  [DecidableEq Y]

/-- The dual LQ problem of Exercise 10.4: `(A', G', C, CC', DD', CD', 1)`. -/
def kf_ex4Dual (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ) (D : Matrix Y E ℝ) :
    LSProblem X Y E :=
  ⟨Aᵀ, Gᵀ, C, C * Cᵀ, D * Dᵀ, C * Dᵀ, 1⟩

/-- Exercise 10.4: the error covariances `Σ_0 = Σ₀`, `Σ_{t+1} = T̂(Σ_t)`. -/
noncomputable def kf_ex4Sig (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) (S0 : Matrix X X ℝ) : ℕ → Matrix X X ℝ
  | 0 => S0
  | t + 1 => (kf_ex4Dual A G C D).T (kf_ex4Sig A G C D S0 t)

/-- Exercise 10.4: the gains `K_t = F̂(Σ_t)'`. -/
noncomputable def kf_ex4Gain (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) (S0 : Matrix X X ℝ) (t : ℕ) : Matrix X Y ℝ :=
  ((kf_ex4Dual A G C D).F (kf_ex4Sig A G C D S0 t))ᵀ

/-- Exercise 10.4: the estimates `x̂_0 = x̄₀`,
`x̂_{t+1} = Ax̂_t + Bu_t + K_t(y_{t+1} − Gx̂_t − Hu_t)`. -/
noncomputable def kf_ex4Est {Ω : Type*} (A : Matrix X X ℝ) (B : Matrix X U ℝ) (G : Matrix Y X ℝ)
    (H : Matrix Y U ℝ) (K : ℕ → Matrix X Y ℝ) (xbar0 : X → ℝ) (y : ℕ → Ω → Y → ℝ)
    (u : ℕ → Ω → U → ℝ) : ℕ → Ω → X → ℝ
  | 0 => fun _ => xbar0
  | t + 1 => kf_app A (kf_ex4Est A B G H K xbar0 y u t) + kf_app B (u t) +
      kf_app (K t) (y (t + 1) - kf_app G (kf_ex4Est A B G H K xbar0 y u t) - kf_app H (u t))

omit [Fintype U] [DecidableEq X] in
/-- Exercise 10.4, the gain: for symmetric `Σ`, `F̂(Σ)' = (AΣG' + CD')(GΣG' + DD')⁻¹`. -/
theorem ex_10_4_gain (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    ((kf_ex4Dual A G C D).F P)ᵀ = (A * P * Gᵀ + C * Dᵀ) * (G * P * Gᵀ + D * Dᵀ)⁻¹ := by
  have hs : (G * P * Gᵀ + D * Dᵀ)ᵀ = G * P * Gᵀ + D * Dᵀ := by
    simp [transpose_add, transpose_mul, hP, Matrix.mul_assoc]
  simp only [LSProblem.F, LSProblem.G, LSProblem.N, kf_ex4Dual, one_smul, transpose_transpose,
    transpose_mul, transpose_add, transpose_nonsing_inv, hP]
  rw [add_comm (C * Dᵀ), add_comm (D * Dᵀ)]
  simp only [Matrix.mul_assoc]

omit [DecidableEq X] [DecidableEq Y] in
/-- Exercise 10.4, the error recursion: `x_{t+1} − x̂_{t+1} = (A − K_tG)(x_t − x̂_t) +
(C − K_tD)ε_{t+1}`. -/
theorem ex_10_4_err {Ω : Type*} (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (K : ℕ → Matrix X Y ℝ)
    (xbar0 : X → ℝ) {x : ℕ → Ω → X → ℝ} {y : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ}
    {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (u t) + kf_app C (ε (t + 1)))
    (hy : ∀ t, y (t + 1) = kf_app G (x t) + kf_app H (u t) + kf_app D (ε (t + 1))) (t : ℕ) :
    x (t + 1) - kf_ex4Est A B G H K xbar0 y u (t + 1) =
      kf_app (A - K t * G) (x t - kf_ex4Est A B G H K xbar0 y u t) +
        kf_app (C - K t * D) (ε (t + 1)) := by
  funext ω
  simp only [kf_ex4Est, hx, hy, kf_app, Pi.add_apply, Pi.sub_apply, sub_mulVec, mulVec_add,
    mulVec_sub, mulVec_mulVec]
  abel

omit [Fintype U] [DecidableEq X] [DecidableEq Y] in
/-- The second moments of `Me + Nn` when `e` and `n` are uncorrelated and `Enn' = I`. -/
theorem kf_mom_two {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [DecidableEq E]
    {e : Ω → X → ℝ} {n : Ω → E → ℝ} (he : kf_L2 μ e) (hn : kf_L2 μ n) (M : Matrix X X ℝ)
    (N : Matrix X E ℝ) (hen : var_mom μ e n = 0) (hnn : var_mom μ n n = 1) :
    var_mom μ (kf_app M e + kf_app N n) (kf_app M e + kf_app N n) =
      M * var_mom μ e e * Mᵀ + N * Nᵀ := by
  have hw := kf_L2_add (kf_L2_app he M) (kf_L2_app hn N)
  have hsym : (var_mom μ e e)ᵀ = var_mom μ e e := (kf_mom_transpose e e).symm
  rw [kf_mom_lin2 he hn hw, kf_mom_transpose (kf_app M e + kf_app N n) e,
    kf_mom_transpose (kf_app M e + kf_app N n) n, kf_mom_lin2 he hn he, kf_mom_lin2 he hn hn,
    kf_mom_transpose e n, hen, hnn]
  simp [transpose_mul, hsym, Matrix.mul_assoc]

omit [Fintype U] [DecidableEq X] [DecidableEq Y] in
/-- The one-step covariance of Exercise 10.4 for an arbitrary gain `K` is the policy map (9.9) of
the dual problem: `(A − KG)Σ(A − KG)' + (C − KD)(C − KD)' = T̂_{K'}(Σ)`. -/
theorem kf_ex4_TF (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ) (D : Matrix Y E ℝ)
    (P : Matrix X X ℝ) (K : Matrix X Y ℝ) :
    (A - K * G) * P * (A - K * G)ᵀ + (C - K * D) * (C - K * D)ᵀ =
      (kf_ex4Dual A G C D).TF P Kᵀ := by
  simp only [LSProblem.TF, kf_ex4Dual, one_smul, transpose_transpose, transpose_sub,
    transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [DecidableEq X] in
/-- **Exercise 10.4** (Miao, p. 345). For `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}`,
`y_{t+1} = Gx_t + Hu_t + Dε_{t+1}` (`x₀` with mean `x̄₀`, covariance `Σ₀`, uncorrelated with the
shocks; `DD' > 0`), the filter `x̂_{t+1} = Ax̂_t + Bu_t + K_t(y_{t+1} − Gx̂_t − Hu_t)` with
`K_t = (AΣ_tG' + CD')(GΣ_tG' + DD')⁻¹` (`ex_10_4_gain`) and `Σ_{t+1} = T̂(Σ_t) =
AΣ_tA' + CC' − (AΣ_tG' + CD')(GΣ_tG' + DD')⁻¹(GΣ_tA' + DC')` has: errors `x_t − x̂_t` with mean
zero, second moments `Σ_t`, uncorrelated with future shocks; and for every gain `K'` the error
second moments of `Ax̂_t + Bu_t + K'(y_{t+1} − Gx̂_t − Hu_t)` are `T̂_{K'}(Σ_t) ≥ Σ_{t+1}`. -/
theorem ex_10_4 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    [DecidableEq E] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ)
    (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ) (S0 : Matrix X X ℝ)
    (hR : (D * Dᵀ).PosDef) {x : ℕ → Ω → X → ℝ} {y : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ}
    {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (u t) + kf_app C (ε (t + 1)))
    (hy : ∀ t, y (t + 1) = kf_app G (x t) + kf_app H (u t) + kf_app D (ε (t + 1)))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => xbar0) (x 0 - fun _ => xbar0) = S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => xbar0) (ε t) = 0) (t : ℕ) :
    let e := fun t => x t - kf_ex4Est A B G H (kf_ex4Gain A G C D S0) xbar0 y u t
    kf_L2 μ (e t) ∧ kf_mean μ (e t) = 0 ∧ var_mom μ (e t) (e t) = kf_ex4Sig A G C D S0 t ∧
      (∀ s, t < s → var_mom μ (e t) (ε s) = 0) ∧
      ∀ K' : Matrix X Y ℝ, kf_ex4Sig A G C D S0 (t + 1) ≤
        var_mom μ (kf_app (A - K' * G) (e t) + kf_app (C - K' * D) (ε (t + 1)))
          (kf_app (A - K' * G) (e t) + kf_app (C - K' * D) (ε (t + 1))) := by
  intro e
  set L := kf_ex4Dual A G C D
  have hRs : L.Rᵀ = L.R := by simp [L, kf_ex4Dual, transpose_mul]
  have hnn : var_mom μ (ε (t + 1)) (ε (t + 1)) = 1 := by rw [hεε]; simp
  have main : ∀ t, kf_L2 μ (e t) ∧ kf_mean μ (e t) = 0 ∧
      var_mom μ (e t) (e t) = kf_ex4Sig A G C D S0 t ∧
      ∀ s, t < s → var_mom μ (e t) (ε s) = 0 := by
    intro t
    induction t with
    | zero =>
      refine ⟨kf_L2_sub hL0 (kf_L2_const _), ?_, hS0, fun s _ => h0ε s⟩
      change kf_mean μ (x 0 - fun _ => xbar0) = 0
      rw [kf_mean_sub hL0 (kf_L2_const _), hm0, kf_mean_const, sub_self]
    | succ t ih =>
      obtain ⟨he, hme, hee, hes⟩ := ih
      have hrec : e (t + 1) = kf_app (A - kf_ex4Gain A G C D S0 t * G) (e t) +
          kf_app (C - kf_ex4Gain A G C D S0 t * D) (ε (t + 1)) :=
        ex_10_4_err A B C G H D _ xbar0 hx hy t
      have hPsd : (kf_ex4Sig A G C D S0 t).PosSemidef := by rw [← hee]; exact kf_mom_self_psd he
      have hPs : (kf_ex4Sig A G C D S0 t)ᵀ = kf_ex4Sig A G C D S0 t :=
        (SS.LQProblem.posSemidef_iff_real.1 hPsd).1
      have hG := L.G_posDef hR hPsd zero_le_one
      rw [hrec]
      refine ⟨kf_L2_add (kf_L2_app he _) (kf_L2_app (hLε _) _), ?_, ?_, fun s hs => ?_⟩
      · rw [kf_mean_add (kf_L2_app he _) (kf_L2_app (hLε _) _), kf_mean_app he,
          kf_mean_app (hLε _), hme, hmε]
        simp
      · rw [kf_mom_two he (hLε _) _ _ (hes _ (Nat.lt_succ_self t)) (by rw [hεε]; simp), hee,
          kf_ex4_TF, kf_ex4Gain, transpose_transpose,
          L.TF_F ((isUnit_iff_isUnit_det _).1 hG.isUnit)]
        rfl
      · rw [kf_mom_lin2 he (hLε _) (hLε s), hes s (by omega), hεε]
        have h1 : t + 1 ≠ s := by omega
        simp [h1]
  obtain ⟨he, -, hee, hes⟩ := main t
  refine ⟨he, (main t).2.1, hee, hes, fun K' => ?_⟩
  have hPsd : (kf_ex4Sig A G C D S0 t).PosSemidef := by rw [← hee]; exact kf_mom_self_psd he
  have hPs : (kf_ex4Sig A G C D S0 t)ᵀ = kf_ex4Sig A G C D S0 t :=
    (SS.LQProblem.posSemidef_iff_real.1 hPsd).1
  rw [kf_mom_two he (hLε _) _ _ (hes _ (Nat.lt_succ_self t)) hnn, hee, kf_ex4_TF]
  exact L.TF_ge_T hRs hPs (L.G_posDef hR hPsd zero_le_one) K'ᵀ

omit [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] in
/-- Exercise 10.4 (Miao, pp. 345–346), the second form `x_{t+1} = Ax_t + Bu_t + Cε_t`,
`y_t = Gx_t + Hu_{t−1} + Dε_t`: with the re-dated shock `ε'_{t+1} = ε_t` and observation
`y'_{t+1} = y_t` it reads `x_{t+1} = Ax_t + Bu_t + Cε'_{t+1}`, `y'_{t+2} = Gx_{t+1} + Hu_t +
Dε'_{t+2}`, i.e. the first form with `Hu_t` replaced by `Hu_{t−1}`. -/
theorem ex_10_4_equiv [Fintype X] [Fintype U] [Fintype E] (A : Matrix X X ℝ)
    (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ) (H : Matrix Y U ℝ)
    (D : Matrix Y E ℝ) (x : ℕ → X → ℝ) (y : ℕ → Y → ℝ) (u : ℕ → U → ℝ) (ε : ℕ → E → ℝ)
    (hx : ∀ t, x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε t)
    (hy : ∀ t, y (t + 1) = G *ᵥ x (t + 1) + H *ᵥ u t + D *ᵥ ε (t + 1)) (t : ℕ) :
    let ε' := fun s => ε (s - 1)
    let y' := fun s => y (s - 1)
    x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε' (t + 1) ∧
      y' (t + 2) = G *ᵥ x (t + 1) + H *ᵥ u t + D *ᵥ ε' (t + 2) := by
  intro ε' y'
  exact ⟨hx t, hy t⟩

/-! ### Exercise 10.5 -/

/-- **Exercise 10.5** (Miao, p. 346): the Kalman filter for (10.3)–(10.4),
`x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = Gx_t + Hz_t + Dε_t`. It is the filter of the system
(10.1)–(10.2) with `B = 0` and the known measurement input `h_t = Hz_t`:
`x̂_{t+1|t} = Ax̂_{t|t−1} + AK_ta_t`, `a_t = y_t − Gx̂_{t|t−1} − Hz_t`, `K_t = (Σ_{t|t−1}G' +
C_{t−1}D')Ω⁻¹`; the prediction errors have second moments `Σ_{t|t−1}` and the innovations
`Ω_{t|t−1}` (Step 2 of p. 332). -/
theorem ex_10_5 {Z : Type*} [Fintype Z] {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] [DecidableEq E] (A : Matrix X X ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y Z ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (S0 : Matrix X X ℝ) {x : ℕ → Ω → X → ℝ} {y : ℕ → Ω → Y → ℝ} {z : ℕ → Ω → Z → ℝ}
    {u : ℕ → Ω → U → ℝ} {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app C (ε (t + 1)))
    (hy : ∀ t, y t = kf_app G (x t) + kf_app H (z t) + kf_app D (ε t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => xbar0) (x 0 - fun _ => xbar0) = S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => xbar0) (ε t) = 0)
    (hΩ : ∀ t, IsUnit ((KFSystem.const A (0 : Matrix X U ℝ) C G 0 D xbar0 S0).Om t).det)
    (t : ℕ) :
    let S := KFSystem.const A (0 : Matrix X U ℝ) C G 0 D xbar0 S0
    let h := fun t => kf_app H (z t)
    S.xpred y h u (t + 1) = kf_app A (S.xpred y h u t) +
        kf_app (A * S.K t) (y t - kf_app G (S.xpred y h u t) - h t) ∧
      var_mom μ (x t - S.xpred y h u t) (x t - S.xpred y h u t) = S.Spred t ∧
      var_mom μ (S.innov y h u t) (S.innov y h u t) = S.Om t := by
  intro S h
  have hx' : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1)) := by
    intro t
    rw [hx, show S.B t = 0 from rfl, kf_app_zero_mat, add_zero]
    rfl
  have hy' : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t) := hy
  refine ⟨?_, (S.kf_moments μ hx' hy' hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).2.2.1,
    (S.eq_10_8 μ hx' hy' hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).1⟩
  rw [KFSystem.kf_pred_recursive, show S.B t = 0 from rfl, kf_app_zero_mat, add_zero]
  rfl

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Filtering a hidden finite-state Markov chain

Miao, §10.1.2–§10.1.3, pp. 337–340. The probability model behind the filters of the two
sections: a hidden chain `x₀, x₁, …` on a finite set `X` with initial law `μ₀` and transition
matrix `P` (`P i j = Pr(x_{t+1} = j | x_t = i)`), and signals `y_t` drawn independently given
the states with emission weight `f(x, y) = Pr(y_t = y | x_t = x)`. In §10.1.2 `f` is the
`N × M` matrix `Q` and the signals are finite; in §10.1.3 `f(x, ·)` is the density of
`h(x, ε)`, and the same algebra applies with densities in place of probabilities.

The joint weight of a state path `x⁰…xᵗ` and a signal path `y⁰…yᵗ` is
`μ₀(x₀) f(x₀, y₀) ∏ₛ P(xₛ, xₛ₊₁) f(xₛ₊₁, yₛ₊₁)` (`hm_weight`). Everything else is computed from it
by summing out states:

* `hm_joint t ys i = Pr(x_t = i, yᵗ)`, `hm_lik t ys = Pr(yᵗ)` (the likelihood),
  `hm_post t ys i = π_t(i | yᵗ)`;
* `hm_predJoint t ys i = Pr(x_{t+1} = i, yᵗ)` (the last emission factor left out),
  `hm_pred t ys i = π_{t+1}(i | yᵗ)`.

Proved: the prediction step `Pr(x_{t+1} = i, yᵗ) = Σⱼ pⱼᵢ Pr(x_t = j, yᵗ)` and its normalised
form `π_{t+1}(i | yᵗ) = Σⱼ pⱼᵢ π_t(j | yᵗ)` (`hm_predJoint_eq`, `hm_pred_eq`); the updating step
`π_{t+1}(i | yᵗ⁺¹) = f(i, y) π_{t+1}(i | yᵗ) / Σⱼ f(j, y) π_{t+1}(j | yᵗ)` (`hm_post_update`);
the likelihood factorisation `Pr(yᵗ⁺¹) = Pr(yᵗ) Σⱼ f(j, y) π_{t+1}(j | yᵗ)` (`hm_lik_snoc`);
and, when `μ₀`, `P` and `f` are stochastic, that `hm_lik t` is a probability mass function on
signal paths, the states alone form the Markov chain `(μ₀, P)`, and the filter is a
probability vector (`hm_lik_sum`, `hm_stateLaw`, `hm_markov`, `hm_post_sum`).
-/

namespace Miao.PartialInformation

/-- Splitting a sum over `(t + 2)`-tuples into the last entry and the first `t + 1` entries. -/
theorem hm_sum_snoc {α Z : Type*} [Fintype α] [AddCommMonoid Z] (t : ℕ)
    (F : (Fin (t + 2) → α) → Z) :
    ∑ xs, F xs = ∑ j, ∑ xs : Fin (t + 1) → α, F (Fin.snoc xs j) := by
  rw [← (Fintype.sum_equiv (Fin.snocEquiv (fun _ => α)) _ _ (fun _ => rfl)),
    Fintype.sum_prod_type]
  rfl

/-- Splitting a sum over `1`-tuples. -/
theorem hm_sum_fin_one {α Z : Type*} [Fintype α] [AddCommMonoid Z] (F : (Fin 1 → α) → Z) :
    ∑ xs, F xs = ∑ j, F (fun _ => j) :=
  (Fintype.sum_equiv (Equiv.funUnique (Fin 1) α).symm _ _ (fun _ => rfl)).symm

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Miao, pp. 338–339: the joint weight of the state path `xs = (x₀, …, x_t)` and the signal
path `ys = (y₀, …, y_t)`, `μ₀(x₀) f(x₀, y₀) ∏ₛ P(xₛ, xₛ₊₁) f(xₛ₊₁, yₛ₊₁)`. -/
def hm_weight (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (xs : Fin (t + 1) → X) (ys : Fin (t + 1) → Y) : ℝ :=
  μ0 (xs 0) * f (xs 0) (ys 0) *
    ∏ s : Fin t, (P (xs s.castSucc) (xs s.succ) * f (xs s.succ) (ys s.succ))

omit [Fintype X] [DecidableEq X] in
/-- Extending both paths by one date multiplies the weight by `P(x_t, j) f(j, y)`. -/
theorem hm_weight_snoc (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (xs : Fin (t + 1) → X) (ys : Fin (t + 1) → Y) (j : X) (y : Y) :
    hm_weight μ0 P f (t + 1) (Fin.snoc xs j) (Fin.snoc ys y) =
      hm_weight μ0 P f t xs ys * (P (xs (Fin.last t)) j * f j y) := by
  unfold hm_weight
  rw [Fin.prod_univ_castSucc]
  have h0 : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
  simp only [h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
  ring

/-- `Pr(x_t = i, yᵗ)`: the weight of all state paths ending in `i`. -/
def hm_joint (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  ∑ xs : Fin (t + 1) → X, if xs (Fin.last t) = i then hm_weight μ0 P f t xs ys else 0

/-- The likelihood `Pr(yᵗ) = Σᵢ Pr(x_t = i, yᵗ)`. -/
def hm_lik (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) : ℝ :=
  ∑ i, hm_joint μ0 P f t ys i

/-- The filter `π_t(i | yᵗ) = Pr(x_t = i, yᵗ) / Pr(yᵗ)`. -/
noncomputable def hm_post (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  hm_joint μ0 P f t ys i / hm_lik μ0 P f t ys

/-- `Pr(x_{t+1} = i, yᵗ)`: paths of length `t + 2` ending in `i`, weighted without the emission
factor of date `t + 1`. -/
def hm_predJoint (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  ∑ xs : Fin (t + 2) → X, if xs (Fin.last (t + 1)) = i then
    hm_weight μ0 P f t (Fin.init xs) ys * P (xs (Fin.last t).castSucc) i else 0

/-- The predicted distribution `π_{t+1}(i | yᵗ)`. -/
noncomputable def hm_pred (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : ℝ :=
  hm_predJoint μ0 P f t ys i / ∑ k, hm_predJoint μ0 P f t ys k

theorem hm_lik_eq (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) : hm_lik μ0 P f t ys = ∑ xs, hm_weight μ0 P f t xs ys := by
  unfold hm_lik hm_joint
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Miao, p. 339 (prediction step): `Pr(x_{t+1} = i, yᵗ) = Σⱼ pⱼᵢ Pr(x_t = j, yᵗ)`. -/
theorem hm_predJoint_eq (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) :
    hm_predJoint μ0 P f t ys i = ∑ j, P j i * hm_joint μ0 P f t ys j := by
  unfold hm_predJoint hm_joint
  rw [hm_sum_snoc]
  simp only [Fin.snoc_last, Fin.init_snoc, Fin.snoc_castSucc, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, mul_comm]

/-- Miao, p. 338 (Bayes' rule, numerator): `Pr(x_{t+1} = i, yᵗ⁺¹) = f(i, y) Pr(x_{t+1} = i, yᵗ)`. -/
theorem hm_joint_snoc (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (y : Y) (i : X) :
    hm_joint μ0 P f (t + 1) (Fin.snoc ys y) i = f i y * hm_predJoint μ0 P f t ys i := by
  unfold hm_joint hm_predJoint
  rw [hm_sum_snoc, hm_sum_snoc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  simp only [Fin.snoc_last, Fin.init_snoc, Fin.snoc_castSucc, hm_weight_snoc]
  split_ifs with h
  · rw [h]; ring
  · simp

/-- The forward recursion `Pr(x_{t+1} = i, yᵗ⁺¹) = f(i, y) Σⱼ pⱼᵢ Pr(x_t = j, yᵗ)`. -/
theorem hm_joint_forward (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (y : Y) (i : X) :
    hm_joint μ0 P f (t + 1) (Fin.snoc ys y) i = f i y * ∑ j, P j i * hm_joint μ0 P f t ys j := by
  rw [hm_joint_snoc, hm_predJoint_eq]

/-- The date-0 joint `Pr(x₀ = i, y₀) = μ₀(i) f(i, y₀)`. -/
theorem hm_joint_zero (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (ys : Fin 1 → Y) (i : X) : hm_joint μ0 P f 0 ys i = μ0 i * f i (ys 0) := by
  unfold hm_joint hm_weight
  rw [hm_sum_fin_one]
  simp

/-- With stochastic rows of `P`, `Σᵢ Pr(x_{t+1} = i, yᵗ) = Pr(yᵗ)`. -/
theorem hm_predJoint_sum (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) :
    ∑ k, hm_predJoint μ0 P f t ys k = hm_lik μ0 P f t ys := by
  simp only [hm_predJoint_eq]
  rw [Finset.sum_comm]
  unfold hm_lik
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_mul, hP, one_mul]

/-- Miao, p. 339 (prediction step, normalised):
`π_{t+1}(eᵢ | yᵗ) = Σⱼ pⱼᵢ π_t(eⱼ | yᵗ)`. -/
theorem hm_pred_eq (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (i : X) :
    hm_pred μ0 P f t ys i = ∑ j, P j i * hm_post μ0 P f t ys j := by
  unfold hm_pred hm_post
  rw [hm_predJoint_sum μ0 P f hP, hm_predJoint_eq, Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => mul_div_assoc _ _ _)

/-- Miao, p. 340 (updating step):
`π_{t+1}(eᵢ | yᵗ⁺¹) = f(eᵢ, y) π_{t+1}(eᵢ | yᵗ) / Σⱼ f(eⱼ, y) π_{t+1}(eⱼ | yᵗ)`, whenever
`Pr(yᵗ) ≠ 0`. -/
theorem hm_post_update (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (y : Y)
    (hl : hm_lik μ0 P f t ys ≠ 0) (i : X) :
    hm_post μ0 P f (t + 1) (Fin.snoc ys y) i =
      f i y * hm_pred μ0 P f t ys i / ∑ j, f j y * hm_pred μ0 P f t ys j := by
  have e : hm_lik μ0 P f (t + 1) (Fin.snoc ys y) = ∑ j, f j y * hm_predJoint μ0 P f t ys j := by
    unfold hm_lik
    simp only [hm_joint_snoc]
  unfold hm_post hm_pred
  rw [hm_predJoint_sum μ0 P f hP, e, hm_joint_snoc]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  rw [div_div_div_cancel_right₀ hl]

/-- Miao, p. 340: the likelihood factorises as `Pr(yᵗ⁺¹) = Pr(yᵗ) Pr(y_{t+1} | yᵗ)` with
`Pr(y_{t+1} = y | yᵗ) = Σⱼ f(eⱼ, y) π_{t+1}(eⱼ | yᵗ)`. -/
theorem hm_lik_snoc (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (y : Y)
    (hl : hm_lik μ0 P f t ys ≠ 0) :
    hm_lik μ0 P f (t + 1) (Fin.snoc ys y) =
      hm_lik μ0 P f t ys * ∑ j, f j y * hm_pred μ0 P f t ys j := by
  have e : hm_lik μ0 P f (t + 1) (Fin.snoc ys y) = ∑ j, f j y * hm_predJoint μ0 P f t ys j := by
    unfold hm_lik
    simp only [hm_joint_snoc]
  unfold hm_pred
  rw [hm_predJoint_sum μ0 P f hP, e, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  field_simp

omit [Fintype X] [DecidableEq X] in
/-- Nonnegative inputs give nonnegative weights. -/
theorem hm_weight_nonneg (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∀ i, 0 ≤ μ0 i) (hP : ∀ i j, 0 ≤ P i j) (hf : ∀ i y, 0 ≤ f i y) (t : ℕ)
    (xs : Fin (t + 1) → X) (ys : Fin (t + 1) → Y) : 0 ≤ hm_weight μ0 P f t xs ys :=
  mul_nonneg (mul_nonneg (hμ _) (hf _ _))
    (Finset.prod_nonneg (fun _ _ => mul_nonneg (hP _ _) (hf _ _)))

theorem hm_joint_nonneg (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∀ i, 0 ≤ μ0 i) (hP : ∀ i j, 0 ≤ P i j) (hf : ∀ i y, 0 ≤ f i y) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : 0 ≤ hm_joint μ0 P f t ys i :=
  Finset.sum_nonneg (fun xs _ => by
    split_ifs
    · exact hm_weight_nonneg μ0 P f hμ hP hf t xs ys
    · exact le_rfl)

/-- The filter is a probability vector whenever `Pr(yᵗ) > 0`. -/
theorem hm_post_sum (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Y) (hl : hm_lik μ0 P f t ys ≠ 0) :
    ∑ i, hm_post μ0 P f t ys i = 1 := by
  unfold hm_post
  rw [← Finset.sum_div]
  exact div_self hl

theorem hm_post_nonneg (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∀ i, 0 ≤ μ0 i) (hP : ∀ i j, 0 ≤ P i j) (hf : ∀ i y, 0 ≤ f i y) (t : ℕ)
    (ys : Fin (t + 1) → Y) (i : X) : 0 ≤ hm_post μ0 P f t ys i :=
  div_nonneg (hm_joint_nonneg μ0 P f hμ hP hf t ys i)
    (Finset.sum_nonneg (fun j _ => hm_joint_nonneg μ0 P f hμ hP hf t ys j))

/-- With stochastic `μ₀`, `P` and `f` (finite signals), the likelihood `Pr(yᵗ)` sums to one over
signal paths: `hm_weight` is a genuine joint probability of state and signal paths. -/
theorem hm_lik_sum [Fintype Y] (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hμ : ∑ i, μ0 i = 1) (hP : ∀ i, ∑ j, P i j = 1) (hf : ∀ i, ∑ y, f i y = 1) :
    ∀ t : ℕ, ∑ ys : Fin (t + 1) → Y, hm_lik μ0 P f t ys = 1
  | 0 => by
    simp only [hm_lik, hm_joint_zero]
    rw [hm_sum_fin_one, Finset.sum_comm]
    simp only [← Finset.mul_sum, hf, mul_one, hμ]
  | t + 1 => by
    rw [hm_sum_snoc, Finset.sum_comm, ← hm_lik_sum μ0 P f hμ hP hf t]
    refine Finset.sum_congr rfl (fun ys _ => ?_)
    rw [← hm_predJoint_sum μ0 P f hP]
    unfold hm_lik
    simp only [hm_joint_snoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hf, one_mul]

omit [Fintype X] [DecidableEq X] in
/-- The law of the state path alone: `Σ_{yᵗ} weight = μ₀(x₀) ∏ₛ P(xₛ, xₛ₊₁)`. -/
theorem hm_stateLaw [Fintype Y] (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hf : ∀ i, ∑ y, f i y = 1) :
    ∀ (t : ℕ) (xs : Fin (t + 1) → X), ∑ ys, hm_weight μ0 P f t xs ys =
      μ0 (xs 0) * ∏ s : Fin t, P (xs s.castSucc) (xs s.succ)
  | 0, xs => by
    rw [hm_sum_fin_one]
    simp [hm_weight, ← Finset.mul_sum, hf]
  | t + 1, xs => by
    rw [← Fin.snoc_init_self xs, hm_sum_snoc]
    simp only [hm_weight_snoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hm_stateLaw μ0 P f hf t, ← Finset.mul_sum, hf, mul_one]
    rw [Fin.prod_univ_castSucc]
    have h0 : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
    simp only [h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
    ring

/-- The probability that the states at dates `t` and `t + 1` are `i` and `j`. -/
def hm_pairLaw (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (i j : X) : ℝ :=
  ∑ xs : Fin (t + 2) → X, if xs (Fin.last t).castSucc = i ∧ xs (Fin.last (t + 1)) = j then
    μ0 (xs 0) * ∏ s : Fin (t + 1), P (xs s.castSucc) (xs s.succ) else 0

/-- The probability that the state at date `t` is `i`. -/
def hm_margLaw (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (i : X) : ℝ :=
  ∑ xs : Fin (t + 1) → X, if xs (Fin.last t) = i then
    μ0 (xs 0) * ∏ s : Fin t, P (xs s.castSucc) (xs s.succ) else 0

/-- Miao, p. 337: the hidden states form a Markov chain with transition matrix `P`,
`Pr(x_t = eᵢ, x_{t+1} = eⱼ) = Pr(x_t = eᵢ) pᵢⱼ`, so `pᵢⱼ = Pr(x_{t+1} = eⱼ | x_t = eᵢ)`. -/
theorem hm_markov (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (i j : X) :
    hm_pairLaw μ0 P t i j = hm_margLaw μ0 P t i * P i j := by
  unfold hm_pairLaw hm_margLaw
  rw [hm_sum_snoc, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  have h0 : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
  simp only [Fin.prod_univ_castSucc, h0, Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last,
    Fin.snoc_last]
  by_cases hi : xs (Fin.last t) = i
  · simp only [hi, true_and, ↓reduceIte]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  · simp [hi]

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hidden Markov chain

Miao, §10.1.2, pp. 337–339. The `N` states are the unit vectors `e₁, …, e_N` of `ℝᴺ`
(`hm_e i = Pi.single i 1`) and the `M` signals the unit vectors `ξ₁, …, ξ_M` of `ℝᴹ`; the hidden
chain has transition matrix `P` (`pᵢⱼ = Pr(x_{t+1} = eⱼ | x_t = eᵢ)`) and the signals have the
`N × M` emission matrix `Q` (`qᵢⱼ = Pr(y_t = ξⱼ | x_t = eᵢ)`).

* (10.13): `E[x_{t+1} | x_t] = P′x_t`, so `v_{t+1} = x_{t+1} − P′x_t` has conditional mean
  zero; the algebra `x x′ = diag(x)` for a unit vector, the expansion of `v v′`, and
  `E[v_{t+1}v′_{t+1} | x_t] = diag(P′x_t) − P′ diag(x_t) P` (`eq_10_13`, `eq_10_13_mds`,
  `hm_unit_outer`, `hm_vv_expansion`, `eq_10_13_cov`). Conditional expectations given
  `x_t = eᵢ` are the finite sums `Σⱼ pᵢⱼ (·)(eⱼ)`; that `pᵢⱼ` is indeed the conditional
  probability in the path model of `HMFilter` is `hm_markov`.
* (10.14): the same for the signals, `E[y_t | x_t] = Q′x_t` and
  `E[w_t w′_t | x_t] = diag(Q′x_t) − Q′ diag(x_t) Q` (`eq_10_14`, `eq_10_14_mds`,
  `eq_10_14_cov`). The book writes the left side as `E[u_t u′_t | x_t]`; the shock is `w_t`.
* Bayes' rule, p. 338: `π_t(eᵢ | yᵗ⁻¹, y_t = ξⱼ) = Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹) /
  Σᵢ Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹)` (`hm_bayes`, with the intermediate expression
  `hm_bayes_joint`), and the initial filter `π₀(eᵢ | y₀ = ξⱼ) = qᵢⱼ π^{ss}ᵢ / Σᵢ qᵢⱼ π^{ss}ᵢ`
  (`hm_bayes_initial`); with the stationary prior every `x_t` has law `π^{ss}`
  (`hm_stationary_marg`).
-/

namespace Miao.PartialInformation

open Matrix

variable {X Z : Type*} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- The unit vector `eᵢ`. -/
def hm_e (i : X) : X → ℝ := Pi.single i 1

omit [Fintype Z] [DecidableEq Z] in
/-- `A′eᵢ` is the `i`-th row of `A`. -/
theorem hm_transpose_mulVec_e (A : Matrix X Z ℝ) (i : X) : Aᵀ *ᵥ hm_e i = fun k => A i k := by
  unfold hm_e
  rw [mulVec_single_one]
  rfl

/-- Conditional expectation of a vector function of the next unit vector, given `eᵢ` today and
the stochastic matrix `A`: `E[g(x′) | x = eᵢ] = Σⱼ aᵢⱼ g(eⱼ)`. -/
def hm_condE (A : Matrix X Z ℝ) (i : X) {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (g : (Z → ℝ) → V) : V :=
  ∑ j, A i j • g (hm_e j)

omit [DecidableEq Z] in
/-- The conditional mean of the next unit vector is `A′eᵢ`. -/
theorem hm_condE_id (A : Matrix X Z ℝ) (i : X) [DecidableEq Z] :
    hm_condE A i id = Aᵀ *ᵥ hm_e i := by
  rw [hm_transpose_mulVec_e]
  funext k
  simp [hm_condE, hm_e, Finset.sum_apply, Pi.single_apply]

/-- Miao, (10.13), p. 337: `E[x_{t+1} | x_t = eᵢ] = P′eᵢ`. -/
theorem eq_10_13 (P : Matrix X X ℝ) (i : X) : hm_condE P i id = Pᵀ *ᵥ hm_e i :=
  hm_condE_id P i

/-- A stochastic matrix leaves a zero-mean shock: `E[x′ − A′x | x = eᵢ] = 0`. -/
theorem hm_condE_mds (A : Matrix X Z ℝ) (hA : ∀ i, ∑ j, A i j = 1) (i : X) :
    hm_condE A i (fun z => z - Aᵀ *ᵥ hm_e i) = 0 := by
  have h := hm_condE_id A i
  unfold hm_condE at h ⊢
  rw [show (∑ j, A i j • (hm_e j - Aᵀ *ᵥ hm_e i)) =
      (∑ j, A i j • hm_e j) - (∑ j, A i j) • Aᵀ *ᵥ hm_e i by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]]
  rw [hA, one_smul]
  simp only [id] at h
  rw [h, sub_self]

/-- Miao, (10.13), p. 337: `v_{t+1} = x_{t+1} − P′x_t` is a martingale difference,
`E[v_{t+1} | x_t] = 0`. -/
theorem eq_10_13_mds (P : Matrix X X ℝ) (hP : ∀ i, ∑ j, P i j = 1) (i : X) :
    hm_condE P i (fun z => z - Pᵀ *ᵥ hm_e i) = 0 :=
  hm_condE_mds P hP i

omit [Fintype X] in
/-- Miao, p. 337: for a unit vector, `x x′ = diag(x)`. -/
theorem hm_unit_outer (j : X) : vecMulVec (hm_e j) (hm_e j) = diagonal (hm_e j) := by
  ext k l
  by_cases hkl : k = l
  · subst hkl
    by_cases hj : k = j
    · subst hj; simp [hm_e, vecMulVec_apply]
    · simp [hm_e, vecMulVec_apply, hj]
  · by_cases hj : k = j
    · subst hj; simp [hm_e, vecMulVec_apply, Ne.symm hkl, hkl]
    · simp [hm_e, vecMulVec_apply, hj, hkl]

omit [Fintype X] in
/-- Miao, p. 337: with `x′ = m + v` (here `m = P′x_t`) the expansion
`x′x′′ = m m′ + m v′ + v m′ + v v′`, and, for a unit vector `x′`,
`v v′ = diag(m) + diag(v) − (m m′ + m v′ + v m′)`. -/
theorem hm_vv_expansion (j : X) (m : X → ℝ) :
    vecMulVec (hm_e j) (hm_e j) = vecMulVec m m + vecMulVec m (hm_e j - m) +
        vecMulVec (hm_e j - m) m + vecMulVec (hm_e j - m) (hm_e j - m) ∧
      diagonal (hm_e j) = diagonal m + diagonal (hm_e j - m) ∧
      vecMulVec (hm_e j - m) (hm_e j - m) = diagonal m + diagonal (hm_e j - m) -
        (vecMulVec m m + vecMulVec m (hm_e j - m) + vecMulVec (hm_e j - m) m) := by
  have h1 : vecMulVec (hm_e j) (hm_e j) = vecMulVec m m + vecMulVec m (hm_e j - m) +
      vecMulVec (hm_e j - m) m + vecMulVec (hm_e j - m) (hm_e j - m) := by
    ext k l; simp only [vecMulVec_apply, Matrix.add_apply, Pi.sub_apply]; ring
  have h2 : diagonal (hm_e j) = diagonal m + diagonal (hm_e j - m) := by
    rw [diagonal_add]; congr 1; funext k; simp
  refine ⟨h1, h2, ?_⟩
  rw [← h2, ← hm_unit_outer, h1]
  abel

/-- The conditional second moment of the shock of a stochastic matrix:
`E[(x′ − A′eᵢ)(x′ − A′eᵢ)′ | x = eᵢ] = diag(A′eᵢ) − A′ diag(eᵢ) A`. -/
theorem hm_condE_cov (A : Matrix X Z ℝ) (hA : ∀ i, ∑ j, A i j = 1) (i : X) :
    hm_condE A i (fun z => vecMulVec (z - Aᵀ *ᵥ hm_e i) (z - Aᵀ *ᵥ hm_e i)) =
      diagonal (Aᵀ *ᵥ hm_e i) - Aᵀ * diagonal (hm_e i) * A := by
  rw [hm_transpose_mulVec_e]
  ext k l
  have hs : ∀ k, ∑ j, A i j * Pi.single (M := fun _ => ℝ) j 1 k = A i k := by
    intro k; simp [Pi.single_apply]
  simp only [hm_condE, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, hm_e,
    smul_eq_mul, Matrix.sub_apply, diagonal_apply, mul_apply, transpose_apply]
  have e1 : ∑ j, A i j * ((Pi.single (M := fun _ => ℝ) j (1 : ℝ) k - A i k) *
      (Pi.single (M := fun _ => ℝ) j (1 : ℝ) l - A i l)) =
      ∑ j, A i j * (Pi.single (M := fun _ => ℝ) j (1 : ℝ) k *
        Pi.single (M := fun _ => ℝ) j (1 : ℝ) l)
        - A i k * ∑ j, A i j * Pi.single (M := fun _ => ℝ) j 1 l
        - A i l * ∑ j, A i j * Pi.single (M := fun _ => ℝ) j 1 k
        + A i k * A i l * ∑ j, A i j := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e1, hs, hs, hA]
  have e2 : ∑ x, (∑ x_1, A x_1 k * (if x_1 = x then Pi.single (M := fun _ => ℝ) i (1 : ℝ) x_1
      else 0)) * A x l = A i k * A i l := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [e2]
  by_cases hkl : k = l
  · subst hkl
    have : ∑ j, A i j * (Pi.single (M := fun _ => ℝ) j (1 : ℝ) k *
        Pi.single (M := fun _ => ℝ) j (1 : ℝ) k) = A i k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    simp only [this, ↓reduceIte]
    ring
  · have : ∑ j, A i j * (Pi.single (M := fun _ => ℝ) j (1 : ℝ) k *
        Pi.single (M := fun _ => ℝ) j (1 : ℝ) l) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hj : k = j
      · subst hj; simp [Ne.symm hkl]
      · simp [Pi.single_apply, hj]
    simp only [this, hkl, ↓reduceIte]
    ring

/-- Miao, p. 338: `E[v_{t+1}v′_{t+1} | x_t] = diag(P′x_t) − P′ diag(x_t) P`, for
`x_t = eᵢ`. -/
theorem eq_10_13_cov (P : Matrix X X ℝ) (hP : ∀ i, ∑ j, P i j = 1) (i : X) :
    hm_condE P i (fun z => vecMulVec (z - Pᵀ *ᵥ hm_e i) (z - Pᵀ *ᵥ hm_e i)) =
      diagonal (Pᵀ *ᵥ hm_e i) - Pᵀ * diagonal (hm_e i) * P :=
  hm_condE_cov P hP i

/-- Miao, (10.14), p. 338: `E[y_t | x_t = eᵢ] = Q′eᵢ`. -/
theorem eq_10_14 (Q : Matrix X Z ℝ) (i : X) : hm_condE Q i id = Qᵀ *ᵥ hm_e i :=
  hm_condE_id Q i

/-- Miao, (10.14), p. 338: `w_t = y_t − Q′x_t` satisfies `E[w_t | x_t] = 0`. -/
theorem eq_10_14_mds (Q : Matrix X Z ℝ) (hQ : ∀ i, ∑ j, Q i j = 1) (i : X) :
    hm_condE Q i (fun z => z - Qᵀ *ᵥ hm_e i) = 0 :=
  hm_condE_mds Q hQ i

/-- Miao, p. 338: `E[w_t w′_t | x_t] = diag(Q′x_t) − Q′ diag(x_t) Q` for `x_t = eᵢ` (the book
writes `u_t` for `w_t`). -/
theorem eq_10_14_cov (Q : Matrix X Z ℝ) (hQ : ∀ i, ∑ j, Q i j = 1) (i : X) :
    hm_condE Q i (fun z => vecMulVec (z - Qᵀ *ᵥ hm_e i) (z - Qᵀ *ᵥ hm_e i)) =
      diagonal (Qᵀ *ᵥ hm_e i) - Qᵀ * diagonal (hm_e i) * Q :=
  hm_condE_cov Q hQ i

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 338 (Bayes' rule, first line): `π_t(eᵢ | yᵗ) = Pr(x_t = eᵢ, y_t | yᵗ⁻¹) /
Pr(y_t | yᵗ⁻¹)` with `Pr(x_t = eᵢ, y_t = ξⱼ | yᵗ⁻¹) = Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹)` and
`Pr(y_t = ξⱼ | yᵗ⁻¹)` its sum over `i`. Here date `t − 1` is `t`, and `ys` is `yᵗ⁻¹`. -/
theorem hm_bayes_joint (μ0 : X → ℝ) (P : Matrix X X ℝ) (Q : X → Z → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Z) (hl : hm_lik μ0 P Q t ys ≠ 0) (j : Z) (i : X) :
    hm_joint μ0 P Q (t + 1) (Fin.snoc ys j) i / hm_lik μ0 P Q t ys =
      ∑ s, Q i j * P s i * hm_post μ0 P Q t ys s := by
  rw [hm_joint_forward, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  unfold hm_post
  field_simp

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 338 (Bayes' rule): `π_t(eᵢ | yᵗ⁻¹, y_t = ξⱼ) =
Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹) / Σᵢ Σₛ qᵢⱼ pₛᵢ π_{t−1}(eₛ | yᵗ⁻¹)`, whenever
`Pr(yᵗ⁻¹) ≠ 0`. -/
theorem hm_bayes (μ0 : X → ℝ) (P : Matrix X X ℝ) (Q : X → Z → ℝ) (t : ℕ)
    (ys : Fin (t + 1) → Z) (hl : hm_lik μ0 P Q t ys ≠ 0) (j : Z) (i : X) :
    hm_post μ0 P Q (t + 1) (Fin.snoc ys j) i =
      (∑ s, Q i j * P s i * hm_post μ0 P Q t ys s) /
        ∑ i', ∑ s, Q i' j * P s i' * hm_post μ0 P Q t ys s := by
  simp only [← hm_bayes_joint μ0 P Q t ys hl j]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ hl]
  rfl

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 339: with prior `π^{ss}` for `x₀`,
`π₀(eᵢ | y₀ = ξⱼ) = qᵢⱼ π^{ss}ᵢ / Σᵢ qᵢⱼ π^{ss}ᵢ`. -/
theorem hm_bayes_initial (pss : X → ℝ) (P : Matrix X X ℝ) (Q : X → Z → ℝ)
    (ys : Fin 1 → Z) (i : X) :
    hm_post pss P Q 0 ys i = Q i (ys 0) * pss i / ∑ i', Q i' (ys 0) * pss i' := by
  unfold hm_post hm_lik
  simp only [hm_joint_zero, mul_comm (pss _)]

omit [Fintype Z] [DecidableEq Z] in
/-- The law of `x_{t+1}` is the sum over `i` of the pair law of `(x_t, x_{t+1})`. -/
theorem hm_margLaw_succ (μ0 : X → ℝ) (P : Matrix X X ℝ) (t : ℕ) (j : X) :
    hm_margLaw μ0 P (t + 1) j = ∑ i, hm_pairLaw μ0 P t i j := by
  unfold hm_margLaw hm_pairLaw
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun xs _ => ?_)
  by_cases h : xs (Fin.last (t + 1)) = j
  · simp only [h, and_true, ↓reduceIte, Finset.sum_ite_eq, Finset.mem_univ]
  · simp [h]

omit [Fintype Z] [DecidableEq Z] in
/-- Miao, p. 339: when `x₀` has the stationary law `π^{ss}` (`π^{ss}′P = π^{ss}′`), every
`x_t` has law `π^{ss}`. -/
theorem hm_stationary_marg (pss : X → ℝ) (P : Matrix X X ℝ)
    (hss : ∀ j, ∑ i, pss i * P i j = pss j) : ∀ (t : ℕ) (i : X), hm_margLaw pss P t i = pss i
  | 0, i => by
    unfold hm_margLaw
    rw [hm_sum_fin_one]
    simp
  | t + 1, j => by
    rw [hm_margLaw_succ]
    simp only [hm_markov, hm_stationary_marg pss P hss t]
    exact hss j

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Hidden Markov-switching model (the Hamilton filter)

Miao, §10.1.3, pp. 339–340. The hidden chain is as in §10.1.2 and the measurement equation is
`y_t = h(x_t, ε_t)` with `ε_t` IID; `f(x, y) = Pr(h(x, ε) = y)` is read as the density of
`h(x, ε)` (for continuous signals `Pr(h(x, ε) = y)` is zero; the filter uses the density). The
filter recursion is that of `HMFilter` with emission weight `f`:

* prediction `π_t(eᵢ | yᵗ⁻¹) = Σⱼ pⱼᵢ π_{t−1}(eⱼ | yᵗ⁻¹)` (`hm_hamilton_predict`),
* updating `π_t(eᵢ | yᵗ) = f(eᵢ, y_t) π_t(eᵢ | yᵗ⁻¹) / Σⱼ f(eⱼ, y_t) π_t(eⱼ | yᵗ⁻¹)`
  (`hm_hamilton_update`; the book prints `f(x, y_t)` in the numerator for `f(eᵢ, y_t)`).

For the consumption example `Δ ln C_t = κ(x_t) + ε_t`, `ε_t ~ N(0, σ²)`: the law of
`κ(x) + ε` is `N(κ(x), σ²)` with density `f(x, ·)` (`hm_switch_law`, `hm_switch_density`), the
predictive density `Σⱼ f(eⱼ, y) π_t(eⱼ | yᵗ⁻¹)` integrates to one (`hm_switch_predictive`), and
in the two-regime case the update is the log-odds rule
`log(π₁/π₂ | yᵗ) = log(π₁/π₂ | yᵗ⁻¹) + ((y − κ₂)² − (y − κ₁)²)/(2σ²)` (`hm_switch_logodds`).
The stationary prior of a two-state chain is `(p₂₁, p₁₂)/(p₁₂ + p₂₁)` (`hm_two_state_stationary`).
-/

namespace Miao.PartialInformation

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {X Y : Type*} [Fintype X] [DecidableEq X]

/-- Miao, p. 339 (Hamilton filter, prediction):
`π_t(eᵢ | yᵗ⁻¹) = Σⱼ pⱼᵢ π_{t−1}(eⱼ | yᵗ⁻¹)`; date `t − 1` is `t` here. -/
theorem hm_hamilton_predict (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (i : X) :
    hm_pred μ0 P f t ys i = ∑ j, P j i * hm_post μ0 P f t ys j :=
  hm_pred_eq μ0 P f hP t ys i

/-- Miao, p. 340 (Hamilton filter, updating):
`π_t(eᵢ | yᵗ) = f(eᵢ, y_t) π_t(eᵢ | yᵗ⁻¹) / Σⱼ f(eⱼ, y_t) π_t(eⱼ | yᵗ⁻¹)`. -/
theorem hm_hamilton_update (μ0 : X → ℝ) (P : Matrix X X ℝ) (f : X → Y → ℝ)
    (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → Y) (y : Y)
    (hl : hm_lik μ0 P f t ys ≠ 0) (i : X) :
    hm_post μ0 P f (t + 1) (Fin.snoc ys y) i =
      f i y * hm_pred μ0 P f t ys i / ∑ j, f j y * hm_pred μ0 P f t ys j :=
  hm_post_update μ0 P f hP t ys y hl i

omit [Fintype X] [DecidableEq X] in
/-- Miao, p. 339: in `Δ ln C_t = κ(x_t) + ε_t` with `ε_t ~ N(0, σ²)`, the law of `κ(x) + ε` is
`N(κ(x), σ²)`. -/
theorem hm_switch_law (κ : X → ℝ) (σ2 : ℝ≥0) (x : X) :
    (gaussianReal 0 σ2).map (fun e => κ x + e) = gaussianReal (κ x) σ2 := by
  rw [gaussianReal_map_const_add, zero_add]

/-- The emission density of the consumption-growth example, `f(x, y) = φ(y; κ(x), σ²)`. -/
noncomputable def hm_switchDensity (κ : X → ℝ) (σ2 : ℝ≥0) (x : X) (y : ℝ) : ℝ :=
  gaussianPDFReal (κ x) σ2 y

omit [Fintype X] [DecidableEq X] in
/-- Miao, p. 339: `f(x, ·)` is the density of `h(x, ε) = κ(x) + ε`: for `σ² ≠ 0` the law of
`κ(x) + ε` has density `f(x, ·)` with respect to Lebesgue measure, `f > 0`, `∫ f(x, y) dy = 1`. -/
theorem hm_switch_density (κ : X → ℝ) {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (x : X) :
    (gaussianReal 0 σ2).map (fun e => κ x + e) =
        volume.withDensity (fun y => ENNReal.ofReal (hm_switchDensity κ σ2 x y)) ∧
      (∀ y, 0 < hm_switchDensity κ σ2 x y) ∧ ∫ y, hm_switchDensity κ σ2 x y = 1 := by
  refine ⟨?_, fun y => gaussianPDFReal_pos _ _ _ hσ, integral_gaussianPDFReal_eq_one _ hσ⟩
  rw [hm_switch_law, gaussianReal_of_var_ne_zero _ hσ]
  rfl

/-- Miao, p. 340: the one-step predictive density `Σⱼ f(eⱼ, y) π_t(eⱼ | yᵗ⁻¹)` of the
consumption-growth example integrates to one. -/
theorem hm_switch_predictive (μ0 : X → ℝ) (P : Matrix X X ℝ) (κ : X → ℝ) {σ2 : ℝ≥0}
    (hσ : σ2 ≠ 0) (hP : ∀ i, ∑ j, P i j = 1) (t : ℕ) (ys : Fin (t + 1) → ℝ)
    (hl : hm_lik μ0 P (hm_switchDensity κ σ2) t ys ≠ 0) :
    ∫ y, ∑ j, hm_switchDensity κ σ2 j y * hm_pred μ0 P (hm_switchDensity κ σ2) t ys j = 1 := by
  rw [integral_finsetSum _ (fun j _ => by
    unfold hm_switchDensity
    exact (integrable_gaussianPDFReal _ _).mul_const _)]
  simp only [integral_mul_const, (hm_switch_density κ hσ _).2.2, one_mul]
  unfold hm_pred
  rw [← Finset.sum_div, div_self]
  rw [hm_predJoint_sum μ0 P _ hP]
  exact hl

/-- Miao, p. 340, two-regime case: the Hamilton update in log-odds form,
`log(π₁/π₂ | yᵗ) = log(π₁/π₂ | yᵗ⁻¹) + ((y − κ₂)² − (y − κ₁)²)/(2σ²)`, for positive predicted
probabilities. -/
theorem hm_switch_logodds (κ : Fin 2 → ℝ) {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (p : Fin 2 → ℝ)
    (hp : ∀ i, 0 < p i) (y : ℝ) :
    Real.log ((hm_switchDensity κ σ2 0 y * p 0 / ∑ j, hm_switchDensity κ σ2 j y * p j) /
        (hm_switchDensity κ σ2 1 y * p 1 / ∑ j, hm_switchDensity κ σ2 j y * p j)) =
      Real.log (p 0 / p 1) + ((y - κ 1) ^ 2 - (y - κ 0) ^ 2) / (2 * σ2) := by
  have h0 := gaussianPDFReal_pos (κ 0) σ2 y hσ
  have h1 := gaussianPDFReal_pos (κ 1) σ2 y hσ
  have hS : 0 < ∑ j, hm_switchDensity κ σ2 j y * p j :=
    Finset.sum_pos (fun j _ => mul_pos (gaussianPDFReal_pos _ _ _ hσ) (hp j)) Finset.univ_nonempty
  rw [div_div_div_cancel_right₀ hS.ne']
  unfold hm_switchDensity at h0 h1 ⊢
  rw [show gaussianPDFReal (κ 0) σ2 y * p 0 / (gaussianPDFReal (κ 1) σ2 y * p 1) =
      (gaussianPDFReal (κ 0) σ2 y / gaussianPDFReal (κ 1) σ2 y) * (p 0 / p 1) by
    field_simp]
  rw [Real.log_mul (div_pos h0 h1).ne' (div_pos (hp 0) (hp 1)).ne', Real.log_div h0.ne' h1.ne']
  simp only [gaussianPDFReal]
  have hc : 0 < (√(2 * Real.pi * (σ2 : ℝ)))⁻¹ := by
    have : (0 : ℝ) < σ2 := lt_of_le_of_ne σ2.2 (fun h => hσ (by exact_mod_cast h.symm))
    positivity
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_mul hc.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp]
  ring

/-- Miao, p. 340: the stationary distribution of a two-state chain with switching
probabilities `p₁₂, p₂₁` (not both zero) is `(p₂₁, p₁₂)/(p₁₂ + p₂₁)`; it may serve as the
initial prior `π₀(· | y⁻¹)`. -/
theorem hm_two_state_stationary (a b : ℝ) (hab : a + b ≠ 0) :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1 - a, a; b, 1 - b]
    let pss : Fin 2 → ℝ := ![b / (a + b), a / (a + b)]
    (∀ j, ∑ i, pss i * P i j = pss j) ∧ ∑ i, pss i = 1 := by
  intro P pss
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> simp [P, pss, Fin.sum_univ_two] <;> field_simp <;> ring
  · simp only [pss, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← add_div, add_comm b a, div_self hab]

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Control under partial information: the belief state

Miao, §10.2, pp. 340–341, for finite hidden states `X`, signals `Y` and actions `U` (the book's
"discrete states" case, where the posterior is finite-dimensional). The model `HMPOMDP` has the
transition kernel `a(x′ | z, u) = Pr(x_{t+1} = x′ | x_t = z, u_t = u)` (assumption (ii)), the signal
kernel `q(y | x′, u) = Pr(y_{t+1} = y | x_{t+1} = x′, u_t = u)` (assumption (iii)), rewards
`r(x, u, t)`, terminal reward `R` and discount `β`. The book's
`a_t(x′, y | z, u) = Pr(x_{t+1} = x′, y_{t+1} = y | x_t = z, u_t = u) = q(y | x′, u) a(x′ | z, u)`
is `hm_at` (`hm_at_sum`: it is a probability on `X × Y`).

* Expected total reward. A (deterministic, history-dependent) policy `σ` picks `u_k` from the
  signals `y₁, …, y_k` seen so far (past actions are themselves functions of past signals). For
  an initial (sub-)probability `m` on `x₀`, `hm_cw` is the probability of a state path
  `x₀ … x_n` and signal path `y₁ … y_n`, `hm_rew` the discounted reward
  `Σ_{k<n} βᵏ r(x_k, u_k, t + k) + βⁿ R(x_n)`, and `hm_J n t σ m` the expectation. The total
  mass is preserved (`hm_cw_mass`) and conditioning on the first period gives
  `J_{n+1}(σ, m) = Σₓ m(x) r(x, u₀, t) + β Σ_y J_n(σ_y, m′_y)` (`hm_J_succ`), where `m′_y` is the
  unnormalised posterior (`hm_nextM`).
* Posterior recursion (p. 341):
  `P*(x′) = Σₓ P(x) a_t(x′, y | x, u) / Σ_{x′} Σₓ P(x) a_t(x′, y | x, u)`
  (`hm_bayesNext`); for one period it is the conditional probability of `x₁` given `y₁` in the
  path model (`hm_posterior_one_step`).
* Bellman equation in beliefs (p. 341): `V(P, T) = Σₓ P(x) R(x)`,
  `V(P, t) = max_u [Σₓ P(x) r(x, u, t) + β Σₓ Σ_y Σ_z P(z) a_t(x, y | z, u) V(P*, t + 1)]`
  (`hm_V`, `hm_bookV`, `hm_bellman_terminal`, `hm_bellman`).
* The belief is a sufficient statistic: no history-dependent policy does better than `V(P, t)`
  (`hm_J_le_V`), the policy that maximises the right side of the Bellman equation at the
  current belief attains it (`hm_J_beliefPol`), so `V(P, t)` is the optimal expected reward over
  all history-dependent policies (`hm_value_isGreatest`).
-/

namespace Miao.PartialInformation

/-- Miao, p. 340: a finite partially observed control problem: transition kernel `a z u x`,
signal kernel `q x u y` (signal `y_{t+1}` given `x_{t+1}` and `u_t`), rewards `r x u t`,
terminal reward `R`, discount `β`. -/
structure HMPOMDP (X Y U : Type*) where
  /-- `a z u x = Pr(x_{t+1} = x | x_t = z, u_t = u)`. -/
  a : X → U → X → ℝ
  /-- `q x u y = Pr(y_{t+1} = y | x_{t+1} = x, u_t = u)`. -/
  q : X → U → Y → ℝ
  /-- Period reward `r(x, u, t)`. -/
  r : X → U → ℕ → ℝ
  /-- Terminal reward. -/
  R : X → ℝ
  /-- Discount factor. -/
  β : ℝ

variable {X Y U : Type*} [Fintype X] [Fintype Y] [Fintype U]

/-- Miao, p. 340: `a_t(x, y | z, u) = Pr(x_{t+1} = x, y_{t+1} = y | x_t = z, u_t = u)
= Pr(y_{t+1} | x_{t+1}, u_t) Pr(x_{t+1} | x_t, u_t)`. -/
def hm_at (M : HMPOMDP X Y U) (z : X) (u : U) (x : X) (y : Y) : ℝ := M.q x u y * M.a z u x

omit [Fintype U] in
/-- `a_t(·, · | z, u)` is a probability on `X × Y` when `a` and `q` are stochastic. -/
theorem hm_at_sum (M : HMPOMDP X Y U) (ha : ∀ z u, ∑ x, M.a z u x = 1)
    (hq : ∀ x u, ∑ y, M.q x u y = 1) (z : X) (u : U) : ∑ x, ∑ y, hm_at M z u x y = 1 := by
  simp only [hm_at, ← Finset.sum_mul, hq, one_mul, ha]

/-- The unnormalised posterior `m′(x′) = Σ_z m(z) a_t(x′, y | z, u)`. -/
def hm_nextM (M : HMPOMDP X Y U) (m : X → ℝ) (u : U) (y : Y) : X → ℝ :=
  fun x => ∑ z, m z * hm_at M z u x y

/-- The predictive probability of the signal, `Σ_{x′} Σ_z m(z) a_t(x′, y | z, u)`. -/
def hm_py (M : HMPOMDP X Y U) (m : X → ℝ) (u : U) (y : Y) : ℝ := ∑ x, hm_nextM M m u y x

/-- Miao, p. 341: the posterior
`P*(x′) = Σₓ P(x) a_t(x′, y | x, u) / Σ_{x′} Σₓ P(x) a_t(x′, y | x, u)`. -/
noncomputable def hm_bayesNext (M : HMPOMDP X Y U) (m : X → ℝ) (u : U) (y : Y) : X → ℝ :=
  fun x => hm_nextM M m u y x / hm_py M m u y

/-- Miao, p. 341: the value function in beliefs, by the number `n` of decision dates left at
calendar date `t`: `V₀(P) = Σₓ P(x) R(x)` and
`V_{n+1}(P, t) = max_u [Σₓ P(x) r(x, u, t) + β Σ_y Pr(y | P, u) V_n(P*, t + 1)]`. -/
noncomputable def hm_V [Nonempty U] (M : HMPOMDP X Y U) : ℕ → ℕ → (X → ℝ) → ℝ
  | 0, _, m => ∑ x, m x * M.R x
  | n + 1, t, m => Finset.univ.sup' Finset.univ_nonempty (fun u => ∑ x, m x * M.r x u t +
      M.β * ∑ y, hm_py M m u y * hm_V M n (t + 1) (hm_bayesNext M m u y))

/-- The right side of the Bellman equation at action `u`. -/
noncomputable def hm_obj [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) (u : U) : ℝ :=
  ∑ x, m x * M.r x u t + M.β * ∑ y, hm_py M m u y * hm_V M n (t + 1) (hm_bayesNext M m u y)

theorem hm_V_succ [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) :
    hm_V M (n + 1) t m = Finset.univ.sup' Finset.univ_nonempty (hm_obj M n t m) := rfl

/-- The book's `V(P, t)` for horizon `T`: `n = T − t` decisions remain. -/
noncomputable def hm_bookV [Nonempty U] (M : HMPOMDP X Y U) (T t : ℕ) (m : X → ℝ) : ℝ :=
  hm_V M (T - t) t m

omit [Fintype Y] [Fintype U] in
/-- Miao, p. 341: `V(P, T) = Σₓ P(x) R(x)`. -/
theorem hm_bellman_terminal [Fintype Y] [Fintype U] [Nonempty U] (M : HMPOMDP X Y U) (T : ℕ)
    (m : X → ℝ) : hm_bookV M T T m = ∑ x, m x * M.R x := by
  simp [hm_bookV, hm_V]

/-- Miao, p. 341 (the Bellman equation in beliefs): for `t < T`,
`V(P, t) = max_u [Σₓ P(x) r(x, u, t) + β Σₓ Σ_y Σ_z P(z) a_t(x, y | z, u) V(P*, t + 1)]`, with
`P* = hm_bayesNext P u y`. -/
theorem hm_bellman [Nonempty U] (M : HMPOMDP X Y U) (T t : ℕ) (ht : t < T) (m : X → ℝ) :
    hm_bookV M T t m = Finset.univ.sup' Finset.univ_nonempty (fun u => ∑ x, m x * M.r x u t +
      M.β * ∑ x, ∑ y, ∑ z, m z * hm_at M z u x y *
        hm_bookV M T (t + 1) (hm_bayesNext M m u y)) := by
  unfold hm_bookV
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have hn' : T - (t + 1) = n := by omega
  rw [hn, hn', hm_V]
  congr 1
  funext u
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  simp only [hm_py, hm_nextM, Finset.sum_mul]

/-- The first `k` signals of a signal path. -/
def hm_pre {n : ℕ} (ys : Fin n → Y) (k : Fin n) : Fin k → Y :=
  fun i => ys ⟨i, i.2.trans k.2⟩

/-- The probability of the state path `x₀ … x_n` and the signal path `y₁ … y_n` when `x₀ ~ m`
and the policy `σ` chooses `u_k = σ_k(y₁, …, y_k)`. -/
def hm_cw (M : HMPOMDP X Y U) (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ)
    (xs : Fin (n + 1) → X) (ys : Fin n → Y) : ℝ :=
  m (xs 0) * ∏ k : Fin n, hm_at M (xs k.castSucc) (σ k (hm_pre ys k)) (xs k.succ) (ys k)

/-- The discounted reward `Σ_{k<n} βᵏ r(x_k, u_k, t + k) + βⁿ R(x_n)` along a path. -/
def hm_rew (M : HMPOMDP X Y U) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (xs : Fin (n + 1) → X) (ys : Fin n → Y) : ℝ :=
  ∑ k : Fin n, M.β ^ (k : ℕ) * M.r (xs k.castSucc) (σ k (hm_pre ys k)) (t + k) +
    M.β ^ n * M.R (xs (Fin.last n))

/-- Miao, p. 340: the expected total reward `E[Σ_{k<n} βᵏ r(x_k, u_k, t + k) + βⁿ R(x_n)]` of the
policy `σ` from the initial law `m`. -/
def hm_J (M : HMPOMDP X Y U) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ) : ℝ :=
  ∑ xs : Fin (n + 1) → X, ∑ ys : Fin n → Y, hm_cw M n σ m xs ys * hm_rew M n t σ xs ys

/-- The continuation of `σ` after the first signal `y`. -/
def hm_shift (σ : (k : ℕ) → (Fin k → Y) → U) (y : Y) : (k : ℕ) → (Fin k → Y) → U :=
  fun k ys => σ (k + 1) (Fin.cons y ys)

/-- Splitting a sum over `(n + 1)`-tuples into the first entry and the rest. -/
theorem hm_sum_cons {α Z : Type*} [Fintype α] [AddCommMonoid Z] (n : ℕ)
    (F : (Fin (n + 1) → α) → Z) :
    ∑ xs, F xs = ∑ j, ∑ xs : Fin n → α, F (Fin.cons j xs) := by
  rw [← (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)),
    Fintype.sum_prod_type]
  rfl

omit [Fintype Y] [Fintype U] in
theorem hm_pre_cons_succ (σ : (k : ℕ) → (Fin k → Y) → U) {n : ℕ} (y : Y) (yr : Fin n → Y)
    (k : Fin n) :
    σ (k.succ : ℕ) (hm_pre (Fin.cons y yr) k.succ) = hm_shift σ y k (hm_pre yr k) := by
  change σ ((k : ℕ) + 1) (hm_pre (Fin.cons y yr) k.succ) = σ ((k : ℕ) + 1) (Fin.cons y _)
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

omit [Fintype Y] [Fintype U] in
theorem hm_pre_zero (σ : (k : ℕ) → (Fin k → Y) → U) {n : ℕ} (ys : Fin (n + 1) → Y) :
    σ ((0 : Fin (n + 1)) : ℕ) (hm_pre ys 0) = σ 0 Fin.elim0 := by
  change σ 0 _ = σ 0 _
  congr 1
  funext i
  exact i.elim0

omit [Fintype Y] [Fintype U] in
/-- One period of the path probability: summing out `x₀` leaves the path probability of the
continuation from the unnormalised posterior `m′_y`. -/
theorem hm_cw_cons_sum (M : HMPOMDP X Y U) (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) (xr : Fin (n + 1) → X) (y : Y) (yr : Fin n → Y) :
    ∑ x0, hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) =
      hm_cw M n (hm_shift σ y) (hm_nextM M m (σ 0 Fin.elim0) y) xr yr := by
  unfold hm_cw hm_nextM
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x0 _ => ?_)
  rw [Fin.prod_univ_succ]
  simp only [hm_pre_cons_succ, hm_pre_zero, Fin.cons_zero, Fin.castSucc_zero, Fin.succ_zero_eq_one,
    ← Fin.succ_castSucc, Fin.cons_succ]
  have h1 : (Fin.cons x0 xr : Fin (n + 2) → X) 1 = xr 0 := rfl
  rw [h1]
  ring

omit [Fintype U] in
/-- Conditioning a path sum on the first period. -/
theorem hm_cw_decomp (M : HMPOMDP X Y U) (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) (G : Y → (Fin (n + 1) → X) → (Fin n → Y) → ℝ) :
    ∑ xs : Fin (n + 2) → X, ∑ ys : Fin (n + 1) → Y,
        hm_cw M (n + 1) σ m xs ys * G (ys 0) (Fin.tail xs) (Fin.tail ys) =
      ∑ y, ∑ xr, ∑ yr, hm_cw M n (hm_shift σ y) (hm_nextM M m (σ 0 Fin.elim0) y) xr yr *
        G y xr yr := by
  rw [hm_sum_cons (n := n + 1) (α := X)]
  simp only [hm_sum_cons (n := n) (α := Y) (Z := ℝ), Fin.cons_zero, Fin.tail_cons]
  calc _ = ∑ x0 : X, ∑ y : Y, ∑ xr : Fin (n + 1) → X, ∑ yr : Fin n → Y,
        hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) * G y xr yr :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ y : Y, ∑ x0 : X, ∑ xr : Fin (n + 1) → X, ∑ yr : Fin n → Y,
        hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) * G y xr yr := Finset.sum_comm
    _ = ∑ y : Y, ∑ xr : Fin (n + 1) → X, ∑ yr : Fin n → Y, ∑ x0 : X,
        hm_cw M (n + 1) σ m (Fin.cons x0 xr) (Fin.cons y yr) * G y xr yr :=
        Finset.sum_congr rfl (fun _ _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun xr _ =>
        Finset.sum_congr rfl (fun yr _ => by rw [← Finset.sum_mul, hm_cw_cons_sum])))

omit [Fintype U] in
/-- The path probabilities have total mass `Σₓ m(x)`. -/
theorem hm_cw_mass (M : HMPOMDP X Y U) (ha : ∀ z u, ∑ x, M.a z u x = 1)
    (hq : ∀ x u, ∑ y, M.q x u y = 1) :
    ∀ (n : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ),
      ∑ xs : Fin (n + 1) → X, ∑ ys : Fin n → Y, hm_cw M n σ m xs ys = ∑ x, m x
  | 0, σ, m => by
    simp only [hm_cw, Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_unique, one_nsmul]
    exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun _ => rfl))
  | n + 1, σ, m => by
    have h := hm_cw_decomp M n σ m (fun _ _ _ => 1)
    simp only [mul_one] at h
    rw [h]
    simp only [hm_cw_mass M ha hq n, hm_nextM]
    calc _ = ∑ x : X, ∑ y : Y, ∑ z : X, m z * hm_at M z (σ 0 Fin.elim0) x y := Finset.sum_comm
      _ = ∑ x : X, ∑ z : X, ∑ y : Y, m z * hm_at M z (σ 0 Fin.elim0) x y :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ z : X, ∑ x : X, ∑ y : Y, m z * hm_at M z (σ 0 Fin.elim0) x y := Finset.sum_comm
      _ = ∑ z, m z := Finset.sum_congr rfl (fun z _ => by
        simp only [← Finset.mul_sum]
        rw [hm_at_sum M ha hq, mul_one])

omit [Fintype X] [Fintype Y] [Fintype U] in
theorem hm_rew_cons (M : HMPOMDP X Y U) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (x0 : X) (xr : Fin (n + 1) → X) (y : Y) (yr : Fin n → Y) :
    hm_rew M (n + 1) t σ (Fin.cons x0 xr) (Fin.cons y yr) =
      M.r x0 (σ 0 Fin.elim0) t + M.β * hm_rew M n (t + 1) (hm_shift σ y) xr yr := by
  unfold hm_rew
  rw [Fin.sum_univ_succ]
  simp only [hm_pre_cons_succ, hm_pre_zero]
  have hl : (Fin.cons x0 xr : Fin (n + 2) → X) (Fin.last (n + 1)) = xr (Fin.last n) := by
    rw [← Fin.succ_last, Fin.cons_succ]
  have hc : ∀ k : Fin n, (Fin.cons x0 xr : Fin (n + 2) → X) k.succ.castSucc = xr k.castSucc :=
    fun k => by rw [← Fin.succ_castSucc, Fin.cons_succ]
  have h0 : (Fin.cons x0 xr : Fin (n + 2) → X) (Fin.castSucc 0) = x0 := rfl
  simp only [hl, hc, h0, Fin.val_zero, Fin.val_succ, pow_zero, one_mul, add_zero]
  rw [add_assoc, mul_add, Finset.mul_sum]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show t + ((k : ℕ) + 1) = t + 1 + k by omega, pow_succ]
    ring
  · ring

omit [Fintype U] in
/-- Miao, p. 340: conditioning on the first period,
`J_{n+1}(σ, m) = Σₓ m(x) r(x, u₀, t) + β Σ_y J_n(σ_y, m′_y)`. -/
theorem hm_J_succ (M : HMPOMDP X Y U) (ha : ∀ z u, ∑ x, M.a z u x = 1)
    (hq : ∀ x u, ∑ y, M.q x u y = 1) (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) :
    hm_J M (n + 1) t σ m = ∑ x, m x * M.r x (σ 0 Fin.elim0) t +
      M.β * ∑ y, hm_J M n (t + 1) (hm_shift σ y) (hm_nextM M m (σ 0 Fin.elim0) y) := by
  have e1 : hm_J M (n + 1) t σ m =
      ∑ xs : Fin (n + 2) → X, ∑ ys : Fin (n + 1) → Y,
        hm_cw M (n + 1) σ (fun x => m x * M.r x (σ 0 Fin.elim0) t) xs ys +
      M.β * ∑ xs : Fin (n + 2) → X, ∑ ys : Fin (n + 1) → Y, hm_cw M (n + 1) σ m xs ys *
        hm_rew M n (t + 1) (hm_shift σ (ys 0)) (Fin.tail xs) (Fin.tail ys) := by
    unfold hm_J
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun xs _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ys _ => ?_)
    rw [← Fin.cons_self_tail xs, ← Fin.cons_self_tail ys, hm_rew_cons]
    simp only [hm_cw, Fin.cons_zero, Fin.tail_cons]
    ring
  rw [e1, hm_cw_mass M ha hq,
    hm_cw_decomp M n σ m (fun y xr yr => hm_rew M n (t + 1) (hm_shift σ y) xr yr)]
  rfl

omit [Fintype U] in
theorem hm_J_zero (M : HMPOMDP X Y U) (t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U)
    (m : X → ℝ) : hm_J M 0 t σ m = ∑ x, m x * M.R x := by
  unfold hm_J hm_cw hm_rew
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.sum_empty, zero_add,
    pow_zero, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_nsmul]
  exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) X) _ _ (fun _ => rfl))

omit [Fintype Y] [Fintype U] in
theorem hm_nextM_nonneg (M : HMPOMDP X Y U) (ha : ∀ z u x, 0 ≤ M.a z u x)
    (hq : ∀ x u y, 0 ≤ M.q x u y) (m : X → ℝ) (hm : ∀ x, 0 ≤ m x) (u : U) (y : Y) (x : X) :
    0 ≤ hm_nextM M m u y x :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (hm z) (mul_nonneg (hq _ _ _) (ha _ _ _)))

omit [Fintype Y] [Fintype U] in
theorem hm_nextM_smul (M : HMPOMDP X Y U) (c : ℝ) (m : X → ℝ) (u : U) (y : Y) :
    hm_nextM M (c • m) u y = c • hm_nextM M m u y := by
  funext x
  simp only [hm_nextM, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [Fintype Y] [Fintype U] in
theorem hm_bayesNext_smul (M : HMPOMDP X Y U) {c : ℝ} (hc : c ≠ 0) (m : X → ℝ) (u : U)
    (y : Y) : hm_bayesNext M (c • m) u y = hm_bayesNext M m u y := by
  funext x
  simp only [hm_bayesNext, hm_py, hm_nextM_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- A positive multiple of a nonnegative function: `sup (c g) = c sup g` for `c ≥ 0`. -/
theorem hm_sup'_mul {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) : s.sup' hs (fun i => c * g i) = c * s.sup' hs g := by
  apply le_antisymm
  · exact Finset.sup'_le hs _ (fun i hi => mul_le_mul_of_nonneg_left (Finset.le_sup' g hi) hc)
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs g
    rw [he]
    exact Finset.le_sup' (fun i => c * g i) hi

/-- The value function is positively homogeneous in the (unnormalised) belief. -/
theorem hm_V_smul [Nonempty U] (M : HMPOMDP X Y U) :
    ∀ (n t : ℕ) (m : X → ℝ) {c : ℝ}, 0 ≤ c → hm_V M n t (c • m) = c * hm_V M n t m
  | 0, t, m, c, _ => by
    simp only [hm_V, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  | n + 1, t, m, c, hc => by
    rw [hm_V_succ, hm_V_succ, ← hm_sup'_mul _ _ _ hc]
    congr 1
    funext u
    rcases hc.lt_or_eq with hc | hc
    · simp only [hm_obj, hm_bayesNext_smul M hc.ne', hm_py, hm_nextM_smul, Pi.smul_apply,
        smul_eq_mul, ← Finset.mul_sum, mul_assoc, mul_add, mul_left_comm c M.β]
    · subst hc
      simp [hm_obj, hm_py, hm_nextM]

/-- `Pr(y | m, u) V_n(P*_y) = V_n(m′_y)`: the value of the unnormalised posterior. -/
theorem hm_py_mul_V [Nonempty U] (M : HMPOMDP X Y U) (ha : ∀ z u x, 0 ≤ M.a z u x)
    (hq : ∀ x u y, 0 ≤ M.q x u y) (m : X → ℝ) (hm : ∀ x, 0 ≤ m x) (n t : ℕ) (u : U) (y : Y) :
    hm_py M m u y * hm_V M n t (hm_bayesNext M m u y) = hm_V M n t (hm_nextM M m u y) := by
  have hnn := hm_nextM_nonneg M ha hq m hm u y
  have hpy : 0 ≤ hm_py M m u y := Finset.sum_nonneg (fun x _ => hnn x)
  rcases hpy.lt_or_eq with hp | hp
  · rw [← hm_V_smul M n t _ hp.le]
    congr 1
    funext x
    simp only [hm_bayesNext, Pi.smul_apply, smul_eq_mul]
    field_simp
  · have h0 : hm_nextM M m u y = (0 : ℝ) • hm_nextM M m u y := by
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hnn x)).1 hp.symm x
        (Finset.mem_univ _)
      simp [this]
    rw [← hp, zero_mul, h0, hm_V_smul M n t _ le_rfl, zero_mul]

/-- Miao, p. 341 (the belief is a sufficient statistic, upper bound): every history-dependent
policy earns at most `V_n(m, t)` from a nonnegative initial law `m`. -/
theorem hm_J_le_V [Nonempty U] (M : HMPOMDP X Y U) (hβ : 0 ≤ M.β)
    (ha0 : ∀ z u x, 0 ≤ M.a z u x) (hq0 : ∀ x u y, 0 ≤ M.q x u y)
    (ha : ∀ z u, ∑ x, M.a z u x = 1) (hq : ∀ x u, ∑ y, M.q x u y = 1) :
    ∀ (n t : ℕ) (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ), (∀ x, 0 ≤ m x) →
      hm_J M n t σ m ≤ hm_V M n t m
  | 0, t, σ, m, _ => by rw [hm_J_zero]; rfl
  | n + 1, t, σ, m, hm => by
    rw [hm_J_succ M ha hq, hm_V_succ]
    refine le_trans ?_ (Finset.le_sup' (hm_obj M n t m) (Finset.mem_univ (σ 0 Fin.elim0)))
    unfold hm_obj
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => ?_)) hβ)
    rw [hm_py_mul_V M ha0 hq0 m hm]
    exact hm_J_le_V M hβ ha0 hq0 ha hq n (t + 1) _ _ (hm_nextM_nonneg M ha0 hq0 m hm _ y)

/-- A maximiser of the right side of the Bellman equation at the belief `m`. -/
noncomputable def hm_greedy [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) : U :=
  (Finset.exists_mem_eq_sup' Finset.univ_nonempty (hm_obj M n t m)).choose

theorem hm_greedy_spec [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) :
    hm_V M (n + 1) t m = hm_obj M n t m (hm_greedy M n t m) :=
  (Finset.exists_mem_eq_sup' Finset.univ_nonempty (hm_obj M n t m)).choose_spec.2

/-- The belief policy of an `(n + 1)`-period problem: act greedily at the current belief, then
update the belief by Bayes' rule (`hm_nextM`) and continue. It depends on the signal history
only through the belief. -/
noncomputable def hm_beliefPol [Nonempty U] (M : HMPOMDP X Y U) :
    ℕ → ℕ → (X → ℝ) → (k : ℕ) → (Fin k → Y) → U
  | n, t, m, 0, _ => hm_greedy M n t m
  | n, t, m, k + 1, ys =>
      hm_beliefPol M (n - 1) (t + 1) (hm_nextM M m (hm_greedy M n t m) (ys 0)) k (Fin.tail ys)

theorem hm_shift_beliefPol [Nonempty U] (M : HMPOMDP X Y U) (n t : ℕ) (m : X → ℝ) (y : Y) :
    hm_shift (hm_beliefPol M (n + 1) t m) y =
      hm_beliefPol M n (t + 1) (hm_nextM M m (hm_greedy M (n + 1) t m) y) := by
  funext k ys
  simp only [hm_shift, hm_beliefPol, Fin.cons_zero, Fin.tail_cons, Nat.add_sub_cancel]

/-- Miao, p. 341 (the belief is a sufficient statistic, attainment): the belief policy earns
exactly `V_{n+1}(m, t)`. -/
theorem hm_J_beliefPol [Nonempty U] (M : HMPOMDP X Y U)
    (ha0 : ∀ z u x, 0 ≤ M.a z u x) (hq0 : ∀ x u y, 0 ≤ M.q x u y)
    (ha : ∀ z u, ∑ x, M.a z u x = 1) (hq : ∀ x u, ∑ y, M.q x u y = 1) :
    ∀ (n t : ℕ) (m : X → ℝ), (∀ x, 0 ≤ m x) →
      hm_J M (n + 1) t (hm_beliefPol M n t m) m = hm_V M (n + 1) t m
  | 0, t, m, hm => by
    rw [hm_J_succ M ha hq, hm_greedy_spec, hm_obj]
    have hu : hm_beliefPol M 0 t m 0 Fin.elim0 = hm_greedy M 0 t m := rfl
    rw [hu]
    congr 2
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hm_J_zero, hm_py_mul_V M ha0 hq0 m hm]
    rfl
  | n + 1, t, m, hm => by
    rw [hm_J_succ M ha hq, hm_greedy_spec, hm_obj]
    have hu : hm_beliefPol M (n + 1) t m 0 Fin.elim0 = hm_greedy M (n + 1) t m := rfl
    rw [hu]
    congr 2
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hm_shift_beliefPol, hm_J_beliefPol M ha0 hq0 ha hq n (t + 1) _
      (hm_nextM_nonneg M ha0 hq0 m hm _ y), hm_py_mul_V M ha0 hq0 m hm]

/-- Miao, pp. 340–341: `V_n(m, t)` is the largest expected reward over all history-dependent
policies, and it is attained (by the belief policy when `n ≥ 1`). -/
theorem hm_value_isGreatest [Nonempty U] (M : HMPOMDP X Y U) (hβ : 0 ≤ M.β)
    (ha0 : ∀ z u x, 0 ≤ M.a z u x) (hq0 : ∀ x u y, 0 ≤ M.q x u y)
    (ha : ∀ z u, ∑ x, M.a z u x = 1) (hq : ∀ x u, ∑ y, M.q x u y = 1) (n t : ℕ)
    (m : X → ℝ) (hm : ∀ x, 0 ≤ m x) :
    IsGreatest (Set.range (fun σ : (k : ℕ) → (Fin k → Y) → U => hm_J M n t σ m))
      (hm_V M n t m) := by
  refine ⟨?_, ?_⟩
  · cases n with
    | zero => exact ⟨fun _ _ => Classical.arbitrary U, by simp only [hm_J_zero]; rfl⟩
    | succ n => exact ⟨hm_beliefPol M n t m, hm_J_beliefPol M ha0 hq0 ha hq n t m hm⟩
  · rintro _ ⟨σ, rfl⟩
    exact hm_J_le_V M hβ ha0 hq0 ha hq n t σ m hm

omit [Fintype U] in
/-- Miao, p. 341 (the posterior recursion as a conditional probability): in the one-period path
model, `Pr(x₁ = x′ | y₁ = y) = Σₓ m(x) a_t(x′, y | x, u) / Σ_{x′} Σₓ m(x) a_t(x′, y | x, u)`,
with `u = σ₀`. -/
theorem hm_posterior_one_step [DecidableEq X] [DecidableEq Y] (M : HMPOMDP X Y U)
    (σ : (k : ℕ) → (Fin k → Y) → U) (m : X → ℝ) (x : X) (y : Y) :
    (∑ xs : Fin 2 → X, ∑ ys : Fin 1 → Y,
        if xs 1 = x ∧ ys 0 = y then hm_cw M 1 σ m xs ys else 0) /
      (∑ xs : Fin 2 → X, ∑ ys : Fin 1 → Y, if ys 0 = y then hm_cw M 1 σ m xs ys else 0) =
      hm_bayesNext M m (σ 0 Fin.elim0) y x := by
  have key : ∀ G : X → Y → Prop, ∀ [∀ a b, Decidable (G a b)],
      (∑ xs : Fin 2 → X, ∑ ys : Fin 1 → Y,
        if G (xs 1) (ys 0) then hm_cw M 1 σ m xs ys else 0) =
      ∑ y', ∑ x', if G x' y' then hm_nextM M m (σ 0 Fin.elim0) y' x' else 0 := by
    intro G _
    have h := hm_cw_decomp M 0 σ m (fun y' xr _ => if G (xr 0) y' then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at h
    refine Eq.trans h ?_
    refine Finset.sum_congr rfl (fun y' _ => ?_)
    rw [hm_sum_fin_one]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    simp [hm_cw]
  rw [key (fun x' y' => x' = x ∧ y' = y), key (fun _ y' => y' = y)]
  simp only [hm_bayesNext, hm_py]
  congr 1
  · rw [Finset.sum_eq_single y (fun b _ hb => Finset.sum_eq_zero (fun x' _ => by simp [hb]))
      (by simp)]
    simp
  · rw [Finset.sum_eq_single y (fun b _ hb => Finset.sum_eq_zero (fun x' _ => by simp [hb]))
      (by simp)]
    simp

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The scalar Kalman filter of Exercise 10.6(a) and the recursion (10.16)

Miao, Exercise 10.6(a), p. 346, with Example 10.1.1 (p. 329) and Example 10.2.1 (p. 342). With
`α = β = 0` the labour-income model (10.5)–(10.6) is `y_t = z_t + v_t`, `z_{t+1} = ρz_t + η_{t+1}`:
the state space form `x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = Gx_t + Dε_t` with `x = z`, `A = ρ`,
`G = 1`, `ε = (η, v)′`, `C = (σ_η, 0)`, `D = (0, σ_v)`, so `CC′ = σ_η²`, `DD′ = σ_v²`, `CD′ = 0`
(`ex_10_6_a_shocks`). The scalar Kalman objects are defined here under the prefix `hm_`.

Two readings of the filter are proved.

* Least squares (book's (10.8)–(10.11) in the scalar case). For a prior error `e = x − x̂` and
  measurement noise `d = Dε` with second moments `Σ`, `CD′`, `DD′`, the error of the update
  `x̂ + k(Ge + d)` has mean square `(1 − kG)²Σ + k²DD′ − 2(1 − kG)k CD′` (`hm_mse_eq`, the scalar
  (10.11) as an integral against any probability measure), minimised exactly at the gain (10.10)
  `K = (ΣG + CD′)/Ω` with `Ω = G²Σ + DD′ + 2G CD′` (10.8), with minimum
  `Σ_{t|t} = (1 − KG)Σ − K CD′` (`hm_mse_min`). For Exercise 10.6:
  `K_t = Σ_t/(Σ_t + σ_v²)`, `Σ_{t|t} = Σ_t σ_v²/(Σ_t + σ_v²)`, the Riccati equation
  `Σ_{t+1} = ρ²Σ_tσ_v²/(Σ_t + σ_v²) + σ_η²` and the forecast recursion
  `x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y_t − x̂_{t|t−1})` (`ex_10_6_a_gain`, `ex_10_6_a_riccati`,
  `ex_10_6_a_recursion`).
* Gaussian conditioning (book p. 328). With prior `z_t | yᵗ⁻¹ ~ N(x̂, Σ)` and `y_t = z_t + v_t`,
  Bayes' rule gives `z_t | yᵗ ~ N(x̂ + K(y − x̂), Σσ_v²/(Σ + σ_v²))` and
  `y_t | yᵗ⁻¹ ~ N(x̂, Σ + σ_v²)`
  (`hm_gauss_bayes`, `hm_gauss_marginal`); the prediction `z_{t+1} = ρz_t + η` gives
  `N(ρx̂_{t|t}, ρ²Σ_{t|t} + σ_η²)`, and `y_{t+1} | yᵗ ~ N(x̂_{t+1|t}, Ω_{t+1|t})`, the conditional
  law used in Example 10.2.1 (`hm_gauss_predict`, `ex_10_6_a_predictive`).

Finally (10.16): `x̂_{t|t} = x̂_{t|t−1} + K_t(y_t − G_t x̂_{t|t−1})` (10.7) and
`x̂_{t+1|t} = A x̂_{t|t}`
give `x̂_{t+1|t} = A x̂_{t|t−1} + AK_t(y_t − G_t x̂_{t|t−1})` (`eq_10_16`).
-/

namespace Miao.PartialInformation

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Miao, (10.16), p. 342: with the updating equation (10.7) (no control) and
`x̂_{t+1|t} = Ax̂_{t|t}`, `x̂_{t+1|t} = Ax̂_{t|t−1} + AK_t(y_t − G_tx̂_{t|t−1})`. -/
theorem eq_10_16 {n m : Type*} [Fintype n] [Fintype m] (A : Matrix n n ℝ) (G : Matrix m n ℝ)
    (K : Matrix n m ℝ) (xpred xfilt xnext : n → ℝ) (y : m → ℝ)
    (h107 : xfilt = xpred + K.mulVec (y - G.mulVec xpred)) (hnext : xnext = A.mulVec xfilt) :
    xnext = A.mulVec xpred + (A * K).mulVec (y - G.mulVec xpred) := by
  rw [hnext, h107, Matrix.mulVec_add, Matrix.mulVec_mulVec]

/-- Miao, Exercise 10.6(a) with Example 10.1.1, p. 329: for `C = (σ_η, 0)`, `D = (0, σ_v)`,
`CC′ = σ_η²`, `DD′ = σ_v²`, `CD′ = 0`. -/
theorem ex_10_6_a_shocks (ση σv : ℝ) :
    let C : Fin 2 → ℝ := ![ση, 0]
    let D : Fin 2 → ℝ := ![0, σv]
    (∑ i, C i * C i = ση ^ 2) ∧ (∑ i, D i * D i = σv ^ 2) ∧ ∑ i, C i * D i = 0 := by
  intro C D
  simp [C, D, Fin.sum_univ_two, sq]

/-- The scalar innovation variance (10.8): `Ω = GΣG′ + DD′ + GCD′ + DC′G′`. -/
def hm_kOmega (G S DD CD : ℝ) : ℝ := G * S * G + DD + G * CD + CD * G

/-- The scalar Kalman gain (10.10): `K = (ΣG′ + CD′)Ω⁻¹`. -/
noncomputable def hm_kGain (G S DD CD : ℝ) : ℝ := (S * G + CD) / hm_kOmega G S DD CD

/-- The scalar mean-square error (10.11) of the update with gain `k`. -/
def hm_kMSE (G S DD CD k : ℝ) : ℝ :=
  (1 - k * G) * S * (1 - k * G) + k * DD * k - (1 - k * G) * CD * k - k * CD * (1 - k * G)

/-- Miao, (10.11), p. 331 (scalar case): if the prior error `e = x_t − x̂_{t|t−1}` and the noise
`d = D_tε_t` have `E[e²] = Σ`, `E[ed] = C_tD′_t` and `E[d²] = D_tD′_t`, the error
`x_t − x̂_{t|t}` of the update `x̂_{t|t} = x̂_{t|t−1} + k a_t`, `a_t = Ge + d`, has mean square
`(1 − kG)Σ(1 − kG) + kDD′k − (1 − kG)CD′k − kDC′(1 − kG)`. -/
theorem hm_mse_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (e d : Ω → ℝ)
    (he : Integrable (fun w => e w ^ 2) μ) (hed : Integrable (fun w => e w * d w) μ)
    (hd : Integrable (fun w => d w ^ 2) μ) (G S DD CD k : ℝ) (hS : ∫ w, e w ^ 2 ∂μ = S)
    (hCD : ∫ w, e w * d w ∂μ = CD) (hDD : ∫ w, d w ^ 2 ∂μ = DD) :
    ∫ w, (e w - k * (G * e w + d w)) ^ 2 ∂μ = hm_kMSE G S DD CD k := by
  have h : (fun w => (e w - k * (G * e w + d w)) ^ 2) = fun w =>
      (1 - k * G) ^ 2 * e w ^ 2 + (k ^ 2 * d w ^ 2 - 2 * (1 - k * G) * k * (e w * d w)) := by
    funext w; ring
  have i1 : Integrable (fun w => (1 - k * G) ^ 2 * e w ^ 2) μ := he.const_mul _
  have i2 : Integrable (fun w => k ^ 2 * d w ^ 2) μ := hd.const_mul _
  have i3 : Integrable (fun w => 2 * (1 - k * G) * k * (e w * d w)) μ := hed.const_mul _
  have i23 : Integrable (fun w => k ^ 2 * d w ^ 2 - 2 * (1 - k * G) * k * (e w * d w)) μ :=
    i2.sub i3
  rw [h, integral_add i1 i23, integral_sub i2 i3, integral_const_mul, integral_const_mul,
    integral_const_mul, hS, hCD, hDD]
  unfold hm_kMSE
  ring

/-- Miao, (10.10)–(10.11), pp. 330–332 (scalar case): when `Ω ≠ 0`,
`MSE(k) = MSE(K) + Ω(k − K)²`, so (for `Ω > 0`) the gain `K = (ΣG + CD′)/Ω` is the unique
minimiser, and `MSE(K) = (1 − KG)Σ − KDC′`. -/
theorem hm_mse_min (G S DD CD k : ℝ) (hΩ : hm_kOmega G S DD CD ≠ 0) :
    hm_kMSE G S DD CD k = hm_kMSE G S DD CD (hm_kGain G S DD CD) +
        hm_kOmega G S DD CD * (k - hm_kGain G S DD CD) ^ 2 ∧
      hm_kMSE G S DD CD (hm_kGain G S DD CD) =
        (1 - hm_kGain G S DD CD * G) * S - hm_kGain G S DD CD * CD := by
  have hM : ∀ k, hm_kMSE G S DD CD k = S - 2 * k * (S * G + CD) + k ^ 2 * hm_kOmega G S DD CD :=
    fun k => by unfold hm_kMSE hm_kOmega; ring
  unfold hm_kGain
  rw [hM, hM]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- Miao, (10.10)–(10.11): for `Ω > 0` the Kalman gain minimises the mean-square error. -/
theorem hm_mse_le (G S DD CD k : ℝ) (hΩ : 0 < hm_kOmega G S DD CD) :
    hm_kMSE G S DD CD (hm_kGain G S DD CD) ≤ hm_kMSE G S DD CD k := by
  rw [(hm_mse_min G S DD CD k hΩ.ne').1]
  exact le_add_of_nonneg_right (mul_nonneg hΩ.le (sq_nonneg _))

/-- Miao, Exercise 10.6(a): with `G = 1`, `DD′ = σ_v²`, `CD′ = 0`, `Ω_t = Σ_t + σ_v²`,
`K_t = Σ_t/(Σ_t + σ_v²)` and `Σ_{t|t} = Σ_tσ_v²/(Σ_t + σ_v²)`. -/
theorem ex_10_6_a_gain (S sv2 : ℝ) (h : S + sv2 ≠ 0) :
    hm_kOmega 1 S sv2 0 = S + sv2 ∧ hm_kGain 1 S sv2 0 = S / (S + sv2) ∧
      (1 - hm_kGain 1 S sv2 0 * 1) * S - hm_kGain 1 S sv2 0 * 0 = S * sv2 / (S + sv2) := by
  have hO : hm_kOmega 1 S sv2 0 = S + sv2 := by unfold hm_kOmega; ring
  have hK : hm_kGain 1 S sv2 0 = S / (S + sv2) := by unfold hm_kGain; rw [hO]; ring
  refine ⟨hO, hK, ?_⟩
  rw [hK]
  field_simp
  ring

/-- The prediction-error variances `Σ_{t|t−1}` of Exercise 10.6:
`Σ_{0|−1} = Σ₀`, `Σ_{t+1|t} = ρ²Σ_{t|t} + σ_η²` with `Σ_{t|t} = Σ_tσ_v²/(Σ_t + σ_v²)`. -/
noncomputable def hm_kSig (ρ sη2 sv2 S0 : ℝ) : ℕ → ℝ
  | 0 => S0
  | t + 1 => ρ ^ 2 * (hm_kSig ρ sη2 sv2 S0 t * sv2 / (hm_kSig ρ sη2 sv2 S0 t + sv2)) + sη2

/-- The Kalman gains `K_t = Σ_t/(Σ_t + σ_v²)` of Exercise 10.6. -/
noncomputable def hm_kK (ρ sη2 sv2 S0 : ℝ) (t : ℕ) : ℝ :=
  hm_kSig ρ sη2 sv2 S0 t / (hm_kSig ρ sη2 sv2 S0 t + sv2)

/-- The innovation variances `Ω_{t|t−1} = Σ_t + σ_v²`, as `ℝ≥0`. -/
noncomputable def hm_kOm (ρ sη2 sv2 S0 : ℝ) (t : ℕ) : ℝ≥0 :=
  Real.toNNReal (hm_kSig ρ sη2 sv2 S0 t + sv2)

/-- Miao, Exercise 10.6(a): the prediction variances are nonnegative when
`Σ₀, σ_η² ≥ 0` and `σ_v² > 0`. -/
theorem hm_kSig_nonneg (ρ sη2 sv2 S0 : ℝ) (hS0 : 0 ≤ S0) (hη : 0 ≤ sη2) (hv : 0 < sv2) :
    ∀ t, 0 ≤ hm_kSig ρ sη2 sv2 S0 t
  | 0 => hS0
  | t + 1 => by
    have := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv t
    simp only [hm_kSig]
    have : 0 < hm_kSig ρ sη2 sv2 S0 t + sv2 := by linarith
    positivity

/-- Miao, Exercise 10.6(a) (Riccati equation): `Σ_{t+1|t} = ρ²Σ_{t|t} + σ_η²` with
`Σ_{t|t} = (1 − K_t)Σ_t`, i.e. the book's `Σ_{t+1|t} = A Σ_{t|t} A′ + CC′`. -/
theorem ex_10_6_a_riccati (ρ sη2 sv2 S0 : ℝ) (hS0 : 0 ≤ S0) (hη : 0 ≤ sη2) (hv : 0 < sv2)
    (t : ℕ) :
    hm_kSig ρ sη2 sv2 S0 (t + 1) =
      ρ * ((1 - hm_kK ρ sη2 sv2 S0 t) * hm_kSig ρ sη2 sv2 S0 t) * ρ + sη2 := by
  have h0 := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv t
  have : hm_kSig ρ sη2 sv2 S0 t + sv2 ≠ 0 := by linarith
  simp only [hm_kSig, hm_kK]
  field_simp
  ring

/-- Miao, Exercise 10.6(a) and (10.16): `x̂_{t|t} = x̂_{t|t−1} + K_t(y_t − x̂_{t|t−1})` and
`x̂_{t+1|t} = ρx̂_{t|t}` give `x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y_t − x̂_{t|t−1})`. -/
theorem ex_10_6_a_recursion (ρ K xpred y : ℝ) :
    ρ * (xpred + K * (y - xpred)) = ρ * xpred + ρ * K * (y - xpred) := by ring

/-- Miao, p. 328 (Gaussian conditioning, scalar): with prior `z ~ N(m, v₁)` and `y = z + v`,
`v ~ N(0, v₂)` independent, the joint density factors as
`φ(z; m, v₁) φ(y; z, v₂) = φ(y; m, v₁ + v₂) φ(z; m + K(y − m), v₁v₂/(v₁ + v₂))`,
`K = v₁/(v₁ + v₂)`. -/
theorem hm_gauss_bayes (m : ℝ) {v1 v2 : ℝ≥0} (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (z y : ℝ) :
    gaussianPDFReal m v1 z * gaussianPDFReal z v2 y =
      gaussianPDFReal m (v1 + v2) y *
        gaussianPDFReal (m + v1 / (v1 + v2) * (y - m)) (v1 * v2 / (v1 + v2)) z := by
  have p1 : (0 : ℝ) < v1 := lt_of_le_of_ne v1.2 (fun h => h1 (by exact_mod_cast h.symm))
  have p2 : (0 : ℝ) < v2 := lt_of_le_of_ne v2.2 (fun h => h2 (by exact_mod_cast h.symm))
  have p12 : (0 : ℝ) < v1 + v2 := by linarith
  simp only [gaussianPDFReal, NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul]
  have hs : √(2 * Real.pi * v1) * √(2 * Real.pi * v2) =
      √(2 * Real.pi * (v1 + v2)) * √(2 * Real.pi * (v1 * v2 / (v1 + v2))) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have he : -(z - m) ^ 2 / (2 * (v1 : ℝ)) + -(y - z) ^ 2 / (2 * v2) =
      -(y - m) ^ 2 / (2 * (v1 + v2)) +
        -(z - (m + v1 / (v1 + v2) * (y - m))) ^ 2 / (2 * (v1 * v2 / (v1 + v2))) := by
    field_simp
    ring
  calc _ = (√(2 * Real.pi * v1) * √(2 * Real.pi * v2))⁻¹ *
        Real.exp (-(z - m) ^ 2 / (2 * (v1 : ℝ)) + -(y - z) ^ 2 / (2 * v2)) := by
        rw [mul_inv, Real.exp_add]; ring
    _ = _ := by rw [hs, he, mul_inv, Real.exp_add]; ring

/-- Miao, p. 329: the predictive density of the signal, `y | yᵗ⁻¹ ~ N(m, v₁ + v₂)`:
`∫ φ(z; m, v₁) φ(y; z, v₂) dz = φ(y; m, v₁ + v₂)`. -/
theorem hm_gauss_marginal (m : ℝ) {v1 v2 : ℝ≥0} (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (y : ℝ) :
    ∫ z, gaussianPDFReal m v1 z * gaussianPDFReal z v2 y = gaussianPDFReal m (v1 + v2) y := by
  have hw : v1 * v2 / (v1 + v2) ≠ 0 := by
    have : v1 + v2 ≠ 0 := by
      intro h; exact h1 (le_antisymm (h ▸ le_add_of_nonneg_right v2.2) v1.2)
    exact div_ne_zero (mul_ne_zero h1 h2) this
  simp only [hm_gauss_bayes m h1 h2]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ hw, mul_one]

/-- Miao, p. 328 (prediction step, Gaussian): if `z ~ N(m, P)` and `η ~ N(0, σ_η²)` are
independent then `ρz + η ~ N(ρm, ρ²P + σ_η²)`. -/
theorem hm_gauss_predict (ρ m : ℝ) (P sη2 : ℝ≥0) :
    ((gaussianReal m P).map (ρ * ·)) ∗ gaussianReal 0 sη2 =
      gaussianReal (ρ * m) (Real.toNNReal (ρ ^ 2) * P + sη2) := by
  rw [gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal, add_zero]
  congr 2
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg ρ)]
  rfl

/-- Miao, Example 10.2.1, p. 342, in the setting of Exercise 10.6(a): if
`z_t | yᵗ ~ N(x̂_{t|t}, Σ_{t|t})` with `Σ_{t|t} = Σ_tσ_v²/(Σ_t + σ_v²)`, then
`y_{t+1} = ρz_t + η_{t+1} + v_{t+1}` has the conditional law `N(ρx̂_{t|t}, Ω_{t+1|t})`,
`Ω_{t+1|t} = Σ_{t+1|t} + σ_v²`. -/
theorem ex_10_6_a_predictive (ρ sη2 sv2 S0 : ℝ) (hS0 : 0 ≤ S0) (hη : 0 ≤ sη2) (hv : 0 < sv2)
    (t : ℕ) (xfilt : ℝ) :
    (((gaussianReal xfilt (Real.toNNReal (hm_kSig ρ sη2 sv2 S0 t * sv2 /
        (hm_kSig ρ sη2 sv2 S0 t + sv2)))).map (ρ * ·)) ∗ gaussianReal 0 (Real.toNNReal sη2)) ∗
        gaussianReal 0 (Real.toNNReal sv2) =
      gaussianReal (ρ * xfilt) (hm_kOm ρ sη2 sv2 S0 (t + 1)) := by
  rw [hm_gauss_predict, gaussianReal_conv_gaussianReal, add_zero]
  congr 1
  have h0 := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv t
  have h1 := hm_kSig_nonneg ρ sη2 sv2 S0 hS0 hη hv (t + 1)
  unfold hm_kOm
  apply NNReal.eq
  have hp : 0 ≤ hm_kSig ρ sη2 sv2 S0 t * sv2 / (hm_kSig ρ sη2 sv2 S0 t + sv2) := by positivity
  rw [Real.coe_toNNReal _ (by linarith), NNReal.coe_add, NNReal.coe_add, NNReal.coe_mul,
    Real.coe_toNNReal _ (sq_nonneg ρ), Real.coe_toNNReal _ hp, Real.coe_toNNReal _ hη,
    Real.coe_toNNReal _ hv.le]
  rfl

end Miao.PartialInformation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Life-cycle saving with learning: Example 10.2.1 and Exercise 10.6(b)–(d)

Miao, Example 10.2.1, p. 342, and Exercise 10.6, p. 346. The household has wealth
`W = Rs_t + exp(y_t)` and chooses `s_{t+1}` (consumption `c_t = W − s_{t+1}`, the budget (10.15)).
Its beliefs about the hidden income component are summarised by the forecast `x̂_{t|t−1}`; the
next forecast is `x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y_t − x̂_{t|t−1})` ((10.16) with `A = ρ`, `G = 1`,
the setting of Exercise 10.6 with `α = β = 0`) and the next signal is
`y_{t+1} | yᵗ ~ N(x̂_{t+1|t}, Ω_{t+1|t})` (`ex_10_6_a_predictive`).

* `hm_gV u β R ρ K Ω T feas k` is the value function `V_t(s_t, y_t, x̂_{t|t−1})` of
  Example 10.2.1 at date `t = T − k`, with `V_{T+1} = 0`, utility `u`, gains `K_t`, innovation
  variances `Ω_t`, and feasible savings `feas k` (`s_{t+1} ≥ 0` in the book); the maximum is a
  `sSup`. `example_10_2_1` is the book's Bellman equation, `example_10_2_1_terminal` the last date.
* (b) `T = 1`, CARA utility `u(c) = −exp(−γc)/γ`, `s_{t+1} ≥ 0`: `V₁ = u(W)` and
  `V₀ = u(W − s*) − (β/γ)N exp(−γRs*)` with `s* = max(0, (γW + log(βRN))/(γ(1 + R)))`,
  `N = E[exp(−γ exp(y₁)) | y₀] = ∫ exp(−γe^{y′}) dN(x̂_{1|0}, Ω_{1|0})` (`ex_10_6_b_terminal`,
  `ex_10_6_b`).
* (c) Any finite `T`. With the borrowing constraint at every date the value is not of closed form
  (already for `T = 1` the policy has the kink of (b)); we solve the problem with
  `s_{T+1} ≥ 0` only (borrowing allowed before `T`, the usual CARA setting). Then
  `V_t = −(1/γ) φ_k(x̂_{t+1|t}) exp(−γ a_k W)`, `k = T − t`, with `a₀ = 1`,
  `a_{k+1} = a_kR/(1 + a_kR)` (so `1/a_k = Σ_{j≤k} R⁻ʲ`), `φ₀ = 1`,
  `φ_{k+1}(m) = (βa_kR N_k(m))^{1/(1+a_kR)}(1 + 1/(a_kR))`,
  `N_k(m) = ∫ exp(−γa_ke^{y′}) φ_k(ρm + ρK(y′ − m)) dN(m, Ω)`, and the optimal saving is
  `s_{t+1} = (γW + log(βa_kR N_k))/(γ(1 + a_kR))` (`ex_10_6_c`, `ex_10_6_c_policy`, `hm_a_inv`).
  The `φ_k` are continuous, positive and bounded, so every expectation is finite and positive
  (`hm_phi_props`, `hm_N_props`).
* (d) With `x̂_{t|t}` as the state: `x̂_{t+1|t} = ρx̂_{t|t}`, `y_{t+1} ~ N(ρx̂_{t|t}, Ω_{t+1|t})`
  and
  `x̂_{t+1|t+1} = ρx̂_{t|t} + K_{t+1}(y_{t+1} − ρx̂_{t|t})`; the Bellman equation `hm_gVf` in this
  state has the same value, `V^f_t(s, y, x̂_{t|t−1} + K_t(y − x̂_{t|t−1})) = V_t(s, y, x̂_{t|t−1})`
  (`ex_10_6_d`).
-/

namespace Miao.PartialInformation

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Miao, Exercise 10.6: CARA utility `u(c) = −exp(−γc)/γ`. -/
noncomputable def hm_cara (γ c : ℝ) : ℝ := -Real.exp (-γ * c) / γ

/-- Miao, Example 10.2.1, p. 342: the value `V_t(s, y, x̂_{t|t−1})` with `k = T − t` periods left
after date `t`; `V_{T+1} = 0`; savings `s′ ∈ feas k`; `c = Rs + exp(y) − s′`; the next forecast
`m = ρx̂ + ρK_t(y − x̂)` and `y′ ~ N(m, Ω_{t+1})`. -/
noncomputable def hm_gV (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, s, y, _ => sSup ((fun s' => u (R * s + Real.exp y - s')) '' feas 0)
  | k + 1, s, y, xh => sSup ((fun s' => u (R * s + Real.exp y - s') + β *
      ∫ y', hm_gV u β R ρ K Om T feas k s' y' (ρ * xh + ρ * K (T - (k + 1)) * (y - xh))
        ∂gaussianReal (ρ * xh + ρ * K (T - (k + 1)) * (y - xh)) (Om (T - k))) '' feas (k + 1))

/-- The book's `V_t(s_t, y_t, x̂_{t|t−1})` for horizon `T`. -/
noncomputable def hm_bookGV (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (t : ℕ) (s y xh : ℝ) : ℝ :=
  hm_gV u β R ρ K Om T feas (T - t) s y xh

/-- **Example 10.2.1** (Miao, p. 342), the Bellman equation: for `t < T`,
`V_t(s, y, x̂_{t|t−1}) = max_{s′} u(Rs + exp(y) − s′) + βE[V_{t+1}(s′, y′, x̂_{t+1|t})]` with
`x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y − x̂_{t|t−1})` (10.16) and `y′ ~ N(x̂_{t+1|t}, Ω_{t+1|t})`. -/
theorem example_10_2_1 (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (t : ℕ) (ht : t < T) (s y xh : ℝ) :
    hm_bookGV u β R ρ K Om T feas t s y xh = sSup ((fun s' => u (R * s + Real.exp y - s') + β *
      ∫ y', hm_bookGV u β R ρ K Om T feas (t + 1) s' y' (ρ * xh + ρ * K t * (y - xh))
        ∂gaussianReal (ρ * xh + ρ * K t * (y - xh)) (Om (t + 1))) '' feas (T - t)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt ht
  have h1 : t + k + 1 - t = k + 1 := by omega
  have h2 : t + k + 1 - (t + 1) = k := by omega
  have h3 : t + k + 1 - (k + 1) = t := by omega
  have h4 : t + k + 1 - k = t + 1 := by omega
  simp only [hm_bookGV, h1, h2, hm_gV, h3, h4]

/-- **Example 10.2.1** (Miao, p. 342), last date: `V_T(s, y, x̂) = max_{s′} u(Rs + exp(y) − s′)`
since `V_{T+1} = 0`. -/
theorem example_10_2_1_terminal (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (s y xh : ℝ) :
    hm_bookGV u β R ρ K Om T feas T s y xh =
      sSup ((fun s' => u (R * s + Real.exp y - s')) '' feas 0) := by
  simp [hm_bookGV, hm_gV]

/-- The tangent-line bound `exp x₀ (1 + (x − x₀)) ≤ exp x`. -/
theorem hm_exp_tangent (x x0 : ℝ) : Real.exp x0 * (1 + (x - x0)) ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x - x0)
  calc Real.exp x0 * (1 + (x - x0)) ≤ Real.exp x0 * Real.exp (x - x0) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = Real.exp x := by rw [← Real.exp_add]; ring_nf

/-- The (negated, scaled) CARA objective `f(s′) = exp(−γ(W − s′)) + c exp(−γbs′)`. -/
noncomputable def hm_f (γ c b W s : ℝ) : ℝ :=
  Real.exp (-γ * (W - s)) + c * Real.exp (-γ * b * s)

/-- Convexity of `f`: `f(s₀) + γ(s − s₀)(exp(−γ(W − s₀)) − cb exp(−γbs₀)) ≤ f(s)`. -/
theorem hm_f_tangent (γ c b W s0 s : ℝ) (hc : 0 ≤ c) :
    hm_f γ c b W s0 + γ * (s - s0) * (Real.exp (-γ * (W - s0)) - c * b *
      Real.exp (-γ * b * s0)) ≤ hm_f γ c b W s := by
  have h1 := hm_exp_tangent (-γ * (W - s)) (-γ * (W - s0))
  have h2 := mul_le_mul_of_nonneg_left (hm_exp_tangent (-γ * b * s) (-γ * b * s0)) hc
  unfold hm_f
  nlinarith [h1, h2]

/-- Miao, Exercise 10.6(c), the one-period CARA problem without constraint: for `γ, c, b > 0`,
`s* = (γW + log(cb))/(γ(1 + b))` minimises `f` and
`f(s*) = exp(−γ(b/(1 + b))W)(cb)^{1/(1+b)}(1 + 1/b)`. -/
theorem hm_f_min {γ c b : ℝ} (hγ : 0 < γ) (hc : 0 < c) (hb : 0 < b) (W : ℝ) :
    (∀ s, hm_f γ c b W ((γ * W + Real.log (c * b)) / (γ * (1 + b))) ≤ hm_f γ c b W s) ∧
      hm_f γ c b W ((γ * W + Real.log (c * b)) / (γ * (1 + b))) =
        Real.exp (-γ * (b / (1 + b)) * W) * (c * b) ^ (1 / (1 + b)) * (1 + 1 / b) := by
  set s0 := (γ * W + Real.log (c * b)) / (γ * (1 + b)) with hs0
  have hcb : 0 < c * b := mul_pos hc hb
  have h1b : 0 < 1 + b := by linarith
  have key : Real.exp (-γ * (W - s0)) = c * b * Real.exp (-γ * b * s0) := by
    rw [← Real.exp_log hcb, ← Real.exp_add]
    congr 1
    rw [hs0]
    field_simp
    ring
  refine ⟨fun s => ?_, ?_⟩
  · have := hm_f_tangent γ c b W s0 s hc.le
    rw [key, sub_self, mul_zero, add_zero] at this
    exact this
  · have hval : hm_f γ c b W s0 = Real.exp (-γ * (W - s0)) * (1 + 1 / b) := by
      unfold hm_f
      rw [key]
      field_simp
    rw [hval, Real.rpow_def_of_pos hcb, ← Real.exp_add]
    congr 2
    rw [hs0]
    field_simp
    ring

/-- Miao, Exercise 10.6(b), the one-period CARA problem with `s′ ≥ 0`: the minimiser of `f` on
`[0, ∞)` is `max(0, s*)`. -/
theorem hm_f_min_nonneg {γ c b : ℝ} (hγ : 0 < γ) (hc : 0 < c) (hb : 0 < b) (W s : ℝ)
    (hs : 0 ≤ s) :
    hm_f γ c b W (max 0 ((γ * W + Real.log (c * b)) / (γ * (1 + b)))) ≤ hm_f γ c b W s := by
  by_cases h : 0 ≤ (γ * W + Real.log (c * b)) / (γ * (1 + b))
  · rw [max_eq_right h]
    exact (hm_f_min hγ hc hb W).1 s
  · push Not at h
    rw [max_eq_left h.le]
    have hcb : 0 < c * b := mul_pos hc hb
    have hneg : γ * W + Real.log (c * b) < 0 := by
      have hd : 0 < γ * (1 + b) := by positivity
      by_contra hn
      push Not at hn
      exact absurd h (not_lt.2 (div_nonneg hn hd.le))
    have hle : c * b ≤ Real.exp (-γ * (W - 0)) := by
      have : Real.log (c * b) < -γ * (W - 0) := by linarith
      exact ((Real.log_lt_iff_lt_exp hcb).1 this).le
    have ht := hm_f_tangent γ c b W 0 s hc.le
    have h0 : Real.exp (-γ * b * 0) = 1 := by simp
    rw [h0, mul_one] at ht
    have : 0 ≤ γ * (s - 0) * (Real.exp (-γ * (W - 0)) - c * b) :=
      mul_nonneg (mul_nonneg hγ.le (by linarith)) (by linarith)
    linarith

/-- The marginal-utility weights `a₀ = 1`, `a_{k+1} = a_kR/(1 + a_kR)`. -/
noncomputable def hm_a (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => hm_a R k * R / (1 + hm_a R k * R)

theorem hm_a_pos {R : ℝ} (hR : 0 < R) : ∀ k, 0 < hm_a R k
  | 0 => one_pos
  | k + 1 => by
    have := hm_a_pos hR k
    simp only [hm_a]
    positivity

/-- Miao, Exercise 10.6(c): `1/a_k = Σ_{j=0}^{k} R⁻ʲ` (the annuity factor). -/
theorem hm_a_inv {R : ℝ} (hR : 0 < R) :
    ∀ k, 1 / hm_a R k = ∑ j ∈ Finset.range (k + 1), R⁻¹ ^ j
  | 0 => by simp [hm_a]
  | k + 1 => by
    have ih := hm_a_inv hR k
    have ha := hm_a_pos hR k
    rw [Finset.sum_range_succ']
    simp only [pow_succ, ← Finset.sum_mul, ← ih, pow_zero]
    simp only [hm_a]
    field_simp

/-- The continuation factors `φ_k` of the CARA value function (Exercise 10.6(c)). -/
noncomputable def hm_phi (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun m => (β * hm_a R k * R * ∫ y', Real.exp (-γ * hm_a R k * Real.exp y') *
      hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m)) ∂gaussianReal m (Om (T - k))) ^
      (1 / (1 + hm_a R k * R)) * (1 + 1 / (hm_a R k * R))

/-- `N_k(m) = E[exp(−γa_k e^{y′}) φ_k(x̂′)]` with `y′ ~ N(m, Ω_{T−k})`. -/
noncomputable def hm_N (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ) (m : ℝ) : ℝ :=
  ∫ y', Real.exp (-γ * hm_a R k * Real.exp y') *
    hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m)) ∂gaussianReal m (Om (T - k))

theorem hm_phi_succ (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ) (m : ℝ) :
    hm_phi γ β R ρ K Om T (k + 1) m = (β * hm_a R k * R * hm_N γ β R ρ K Om T k m) ^
      (1 / (1 + hm_a R k * R)) * (1 + 1 / (hm_a R k * R)) := rfl

/-- If `φ_k` is continuous, positive and bounded by `B`, then `N_k` is continuous, positive and
bounded by `B`. -/
theorem hm_N_props {γ β R ρ : ℝ} (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ) (hγ : 0 < γ)
    (hR : 0 < R) (hc : Continuous (hm_phi γ β R ρ K Om T k))
    (hpos : ∀ m, 0 < hm_phi γ β R ρ K Om T k m) (B : ℝ)
    (hB : ∀ m, hm_phi γ β R ρ K Om T k m ≤ B) :
    Continuous (hm_N γ β R ρ K Om T k) ∧ (∀ m, 0 < hm_N γ β R ρ K Om T k m) ∧
      ∀ m, hm_N γ β R ρ K Om T k m ≤ B := by
  have ha := hm_a_pos hR k
  set a := hm_a R k
  set φ := hm_phi γ β R ρ K Om T k
  set g : ℝ → ℝ → ℝ := fun m y' => Real.exp (-γ * a * Real.exp y') *
    φ (ρ * m + ρ * K (T - k) * (y' - m)) with hg
  have gc : Continuous (fun p : ℝ × ℝ => g p.1 p.2) := by
    simp only [hg]
    fun_prop
  have gpos : ∀ m y', 0 < g m y' := fun m y' => mul_pos (Real.exp_pos _) (hpos _)
  have gle : ∀ m y', g m y' ≤ B := by
    intro m y'
    have e1 : Real.exp (-γ * a * Real.exp y') ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.exp_pos y'
      have : 0 < γ * a * Real.exp y' := by positivity
      linarith
    calc g m y' ≤ 1 * φ (ρ * m + ρ * K (T - k) * (y' - m)) :=
          mul_le_mul_of_nonneg_right e1 (hpos _).le
      _ ≤ B := by rw [one_mul]; exact hB _
  have gm : ∀ m, Continuous (g m) := fun m => gc.comp (Continuous.prodMk_right m)
  have gint : ∀ m (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (g m) μ := by
    intro m μ _
    refine (integrable_const B).mono' (gm m).aestronglyMeasurable (ae_of_all _ (fun y' => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (gpos m y')]
    exact gle m y'
  have hN : ∀ m, hm_N γ β R ρ K Om T k m = ∫ y', g m y' ∂gaussianReal m (Om (T - k)) :=
    fun m => rfl
  refine ⟨?_, fun m => ?_, fun m => ?_⟩
  · have e : ∀ m, hm_N γ β R ρ K Om T k m = ∫ u, g m (u + m) ∂gaussianReal 0 (Om (T - k)) := by
      intro m
      have hμ : gaussianReal m (Om (T - k)) = (gaussianReal 0 (Om (T - k))).map (· + m) := by
        rw [gaussianReal_map_add_const, zero_add]
      rw [hN, hμ, integral_map (measurable_add_const m).aemeasurable
        (gm m).aestronglyMeasurable]
    rw [show hm_N γ β R ρ K Om T k = fun m => ∫ u, g m (u + m) ∂gaussianReal 0 (Om (T - k)) from
      funext e]
    refine continuous_of_dominated (bound := fun _ => B) (fun m => ?_) (fun m => ?_)
      (integrable_const B) (ae_of_all _ (fun u => ?_))
    · exact ((gm m).comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · refine ae_of_all _ (fun u => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (gpos m _)]
      exact gle m _
    · exact gc.comp (continuous_id.prodMk (continuous_const.add continuous_id))
  · rw [hN, integral_pos_iff_support_of_nonneg (fun y' => (gpos m y').le) (gint m _)]
    have : Function.support (g m) = Set.univ :=
      Set.eq_univ_of_forall (fun y' => (gpos m y').ne')
    rw [this, measure_univ]
    exact one_pos
  · rw [hN]
    calc ∫ y', g m y' ∂gaussianReal m (Om (T - k)) ≤ ∫ _, B ∂gaussianReal m (Om (T - k)) :=
          integral_mono (gint m _) (integrable_const B) (fun y' => gle m y')
      _ = B := by simp

/-- Miao, Exercise 10.6(c): every `φ_k` is continuous, positive and bounded. -/
theorem hm_phi_props {γ β R ρ : ℝ} (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ) (hγ : 0 < γ)
    (hβ : 0 < β) (hR : 0 < R) :
    ∀ k, Continuous (hm_phi γ β R ρ K Om T k) ∧ (∀ m, 0 < hm_phi γ β R ρ K Om T k m) ∧
      ∃ B, ∀ m, hm_phi γ β R ρ K Om T k m ≤ B
  | 0 => ⟨continuous_const, fun _ => one_pos, 1, fun _ => le_rfl⟩
  | k + 1 => by
    obtain ⟨hc, hpos, B, hB⟩ := hm_phi_props K Om T hγ hβ hR k
    obtain ⟨Nc, Npos, NB⟩ := hm_N_props K Om T k hγ hR hc hpos B hB
    have ha := hm_a_pos hR k
    have hp : 0 < 1 / (1 + hm_a R k * R) := by positivity
    have hq : 0 < 1 + 1 / (hm_a R k * R) := by positivity
    have hbase : ∀ m, 0 < β * hm_a R k * R * hm_N γ β R ρ K Om T k m :=
      fun m => by have := Npos m; positivity
    refine ⟨?_, fun m => ?_, (β * hm_a R k * R * B) ^ (1 / (1 + hm_a R k * R)) *
      (1 + 1 / (hm_a R k * R)), fun m => ?_⟩
    · have : Continuous (fun m => (β * hm_a R k * R * hm_N γ β R ρ K Om T k m) ^
          (1 / (1 + hm_a R k * R)) * (1 + 1 / (hm_a R k * R))) :=
        ((continuous_const.mul Nc).rpow_const (fun _ => Or.inr hp.le)).mul continuous_const
      exact this
    · rw [hm_phi_succ]
      exact mul_pos (Real.rpow_pos_of_pos (hbase m) _) hq
    · rw [hm_phi_succ]
      refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hbase m).le ?_ hp.le) hq.le
      have := NB m
      have : 0 < β * hm_a R k * R := by positivity
      exact mul_le_mul_of_nonneg_left (NB m) this.le

/-- The closed form `−(1/γ) φ_k(x̂_{t+1|t}) exp(−γa_k(Rs + exp y))` at date `t = T − k`. -/
noncomputable def hm_closed (γ β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ)
    (s y xh : ℝ) : ℝ :=
  -(1 / γ) * hm_phi γ β R ρ K Om T k (ρ * xh + ρ * K (T - k) * (y - xh)) *
    Real.exp (-γ * hm_a R k * (R * s + Real.exp y))

/-- At the last date, with `s_{T+1} ≥ 0`, the household consumes its wealth:
`V_T = u(Rs + exp y)`. -/
theorem hm_terminal {γ β R ρ : ℝ} (hγ : 0 < γ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) (hf : feas 0 = Set.Ici 0) (s y xh : ℝ) :
    hm_gV (hm_cara γ) β R ρ K Om T feas 0 s y xh = hm_cara γ (R * s + Real.exp y) := by
  simp only [hm_gV, hf]
  refine IsGreatest.csSup_eq ⟨⟨0, Set.mem_Ici.2 le_rfl, by simp⟩, ?_⟩
  rintro _ ⟨s', hs', rfl⟩
  simp only [hm_cara]
  have : Real.exp (-γ * (R * s + Real.exp y)) ≤ Real.exp (-γ * (R * s + Real.exp y - s')) := by
    apply Real.exp_le_exp.2
    have := Set.mem_Ici.1 hs'
    nlinarith
  exact div_le_div_of_nonneg_right (by linarith) hγ.le

/-- The expectation of a closed-form continuation value:
`E[V_k(s′, y′, m)] = −(1/γ) exp(−γa_kRs′) N_k(m)`. -/
theorem hm_int_closed {γ β R ρ : ℝ} (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T k : ℕ)
    (V : ℝ → ℝ → ℝ → ℝ) (hV : ∀ s y xh, V s y xh = hm_closed γ β R ρ K Om T k s y xh)
    (s' m : ℝ) :
    ∫ y', V s' y' m ∂gaussianReal m (Om (T - k)) =
      -(1 / γ) * Real.exp (-γ * (hm_a R k * R) * s') * hm_N γ β R ρ K Om T k m := by
  simp only [hV, hm_closed]
  have e : (fun y' => -(1 / γ) * hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m)) *
      Real.exp (-γ * hm_a R k * (R * s' + Real.exp y'))) = fun y' =>
      (-(1 / γ) * Real.exp (-γ * (hm_a R k * R) * s')) * (Real.exp (-γ * hm_a R k * Real.exp y') *
        hm_phi γ β R ρ K Om T k (ρ * m + ρ * K (T - k) * (y' - m))) := by
    funext y'
    rw [show -γ * hm_a R k * (R * s' + Real.exp y') =
      -γ * (hm_a R k * R) * s' + -γ * hm_a R k * Real.exp y' by ring, Real.exp_add]
    ring
  rw [e, integral_const_mul]
  rfl

/-- The CARA Bellman objective in terms of `f`. -/
theorem hm_obj_eq (γ β N b W s' : ℝ) (hγ : γ ≠ 0) :
    hm_cara γ (W - s') + β * (-(1 / γ) * Real.exp (-γ * b * s') * N) =
      -(1 / γ) * hm_f γ (β * N) b W s' := by
  unfold hm_cara hm_f
  field_simp
  ring

/-- One step of backward induction for Exercise 10.6(c): if `V_k` has the closed form then the
maximisation at date `T − (k + 1)` (no constraint) is solved by
`s* = (γW + log(βN_k a_kR))/(γ(1 + a_kR))` with the closed form at `k + 1` as value. -/
theorem hm_step {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (T k : ℕ) (V : ℝ → ℝ → ℝ → ℝ)
    (hV : ∀ s y xh, V s y xh = hm_closed γ β R ρ K Om T k s y xh) (s y xh : ℝ) :
    let m := ρ * xh + ρ * K (T - (k + 1)) * (y - xh)
    let obj := fun s' => hm_cara γ (R * s + Real.exp y - s') + β *
      ∫ y', V s' y' m ∂gaussianReal m (Om (T - k))
    let sstar := (γ * (R * s + Real.exp y) +
      Real.log (β * hm_N γ β R ρ K Om T k m * (hm_a R k * R))) / (γ * (1 + hm_a R k * R))
    IsGreatest (obj '' Set.univ) (hm_closed γ β R ρ K Om T (k + 1) s y xh) ∧
      obj sstar = hm_closed γ β R ρ K Om T (k + 1) s y xh := by
  intro m obj sstar
  obtain ⟨hc, hpos, B, hB⟩ := hm_phi_props K Om T hγ hβ hR k
  obtain ⟨-, Npos, -⟩ := hm_N_props K Om T k hγ hR hc hpos B hB
  have ha := hm_a_pos hR k
  have hb : 0 < hm_a R k * R := mul_pos ha hR
  have hcN : 0 < β * hm_N γ β R ρ K Om T k m := mul_pos hβ (Npos m)
  have hobj : ∀ s', obj s' = -(1 / γ) * hm_f γ (β * hm_N γ β R ρ K Om T k m) (hm_a R k * R)
      (R * s + Real.exp y) s' := by
    intro s'
    simp only [obj]
    rw [hm_int_closed K Om T k V hV s' m, hm_obj_eq _ _ _ _ _ _ hγ.ne']
  obtain ⟨hmin, hval⟩ := hm_f_min hγ hcN hb (R * s + Real.exp y)
  have hstar : obj sstar = hm_closed γ β R ρ K Om T (k + 1) s y xh := by
    rw [hobj, hval, hm_closed, hm_phi_succ]
    simp only [hm_a]
    rw [show β * hm_N γ β R ρ K Om T k m * (hm_a R k * R) =
      β * hm_a R k * R * hm_N γ β R ρ K Om T k m by ring]
    ring
  refine ⟨⟨⟨sstar, Set.mem_univ _, hstar⟩, ?_⟩, hstar⟩
  rintro _ ⟨s', -, rfl⟩
  rw [← hstar, hobj, hobj]
  have hγ' : -(1 / γ) < 0 := by
    have : 0 < 1 / γ := by positivity
    linarith
  exact mul_le_mul_of_nonpos_left (hmin s') hγ'.le

/-- **Exercise 10.6(c)** (Miao, p. 346): with CARA utility, `α = β = 0`, and the borrowing
constraint only at the last date (`s_{T+1} ≥ 0`), the value function at date `t = T − k` is
`V_t(s, y, x̂_{t|t−1}) = −(1/γ) φ_k(x̂_{t+1|t}) exp(−γa_k(Rs + exp y))`. -/
theorem ex_10_6_c {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (T : ℕ) :
    ∀ k s y xh, hm_gV (hm_cara γ) β R ρ K Om T
      (fun k => if k = 0 then Set.Ici 0 else Set.univ) k s y xh =
        hm_closed γ β R ρ K Om T k s y xh
  | 0, s, y, xh => by
    rw [hm_terminal hγ K Om T _ (by simp) s y xh]
    simp only [hm_closed, hm_phi, hm_a, hm_cara]
    ring_nf
  | k + 1, s, y, xh => by
    have ih := ex_10_6_c (ρ := ρ) hγ hβ hR K Om T k
    have h := (hm_step hγ hβ hR K Om T k _ ih s y xh).1
    simp only [hm_gV, Nat.add_one_ne_zero, ↓reduceIte]
    exact h.csSup_eq

/-- **Exercise 10.6(c)** (Miao, p. 346), the policy: at date `t = T − (k + 1)` the optimal
saving is `s_{t+1} = (γW + log(βN_k(x̂_{t+1|t}) a_kR))/(γ(1 + a_kR))`, `W = Rs + exp y`. -/
theorem ex_10_6_c_policy {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (T k : ℕ) (s y xh : ℝ) :
    let V := hm_gV (hm_cara γ) β R ρ K Om T (fun k => if k = 0 then Set.Ici 0 else Set.univ)
    let m := ρ * xh + ρ * K (T - (k + 1)) * (y - xh)
    let sstar := (γ * (R * s + Real.exp y) +
      Real.log (β * hm_N γ β R ρ K Om T k m * (hm_a R k * R))) / (γ * (1 + hm_a R k * R))
    V (k + 1) s y xh = hm_cara γ (R * s + Real.exp y - sstar) +
      β * ∫ y', V k sstar y' m ∂gaussianReal m (Om (T - k)) := by
  intro V m sstar
  simp only [V]
  have ih := ex_10_6_c (ρ := ρ) hγ hβ hR K Om T k
  rw [ex_10_6_c (ρ := ρ) hγ hβ hR K Om T (k + 1)]
  exact (hm_step hγ hβ hR K Om T k _ ih s y xh).2.symm

/-- **Exercise 10.6(b)** (Miao, p. 346), the last date of the `T = 1` problem: `V₁ = u(Rs + exp y)`
(`s₂ = 0`). -/
theorem ex_10_6_b_terminal {γ β R ρ : ℝ} (hγ : 0 < γ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0)
    (s y xh : ℝ) :
    hm_bookGV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 1 s y xh =
      hm_cara γ (R * s + Real.exp y) :=
  hm_terminal hγ K Om 1 (fun _ => Set.Ici 0) rfl s y xh

/-- **Exercise 10.6(b)** (Miao, p. 346): with `T = 1`, CARA utility and `s_{t+1} ≥ 0`, the date-0
value is `V₀ = u(W − s*) − (β/γ) N exp(−γRs*)` with `W = Rs + exp(y)`,
`N = ∫ exp(−γe^{y′}) dN(x̂_{1|0}, Ω_{1|0})` and `s* = max(0, (γW + log(βNR))/(γ(1 + R)))`;
`s*` is the optimal saving. -/
theorem ex_10_6_b {γ β R ρ : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) (K : ℕ → ℝ)
    (Om : ℕ → ℝ≥0) (s y xh : ℝ) :
    let m := ρ * xh + ρ * K 0 * (y - xh)
    let N := ∫ y', Real.exp (-γ * Real.exp y') ∂gaussianReal m (Om 1)
    let sstar := max 0 ((γ * (R * s + Real.exp y) + Real.log (β * N * R)) / (γ * (1 + R)))
    0 < N ∧ 0 ≤ sstar ∧
      hm_bookGV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 0 s y xh =
        hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) ∧
      ∀ s', 0 ≤ s' → hm_cara γ (R * s + Real.exp y - s') +
          β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) ≤
        hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) := by
  intro m N sstar
  obtain ⟨hc, hpos, B, hB⟩ := hm_phi_props (β := β) (ρ := ρ) K Om 1 hγ hβ hR 0
  obtain ⟨-, Npos, -⟩ := hm_N_props K Om 1 0 hγ hR hc hpos B hB
  have hNN : hm_N γ β R ρ K Om 1 0 m = N := by
    simp only [hm_N, hm_a, hm_phi, mul_one, Nat.sub_zero]
    rfl
  have hN : 0 < N := hNN ▸ Npos m
  have hV0 : ∀ s y xh, hm_gV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 0 s y xh =
      hm_closed γ β R ρ K Om 1 0 s y xh := by
    intro s y xh
    rw [hm_terminal hγ K Om 1 (fun _ => Set.Ici 0) rfl s y xh]
    simp only [hm_closed, hm_phi, hm_a, hm_cara]
    ring_nf
  have hint : ∀ s', ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) =
      -(1 / γ) * Real.exp (-γ * R * s') * N := by
    intro s'
    have := hm_int_closed (γ := γ) (β := β) (ρ := ρ) K Om 1 0
      (fun s y xh => hm_cara γ (R * s + Real.exp y)) (fun s y xh => by
        rw [← hm_terminal hγ K Om 1 (fun _ => Set.Ici 0) rfl s y xh]; exact hV0 s y xh) s' m
    simp only [hm_a, one_mul, Nat.sub_zero] at this
    rw [this, hNN]
  have hobj : ∀ s', hm_cara γ (R * s + Real.exp y - s') +
      β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) =
      -(1 / γ) * hm_f γ (β * N) R (R * s + Real.exp y) s' := by
    intro s'
    rw [hint, hm_obj_eq _ _ _ _ _ _ hγ.ne']
  have hcN : 0 < β * N := mul_pos hβ hN
  have hval : hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) =
      -(1 / γ) * hm_f γ (β * N) R (R * s + Real.exp y) sstar := by
    rw [← hobj, hint]
    ring
  have hle : ∀ s', 0 ≤ s' → hm_cara γ (R * s + Real.exp y - s') +
      β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1) ≤
      hm_cara γ (R * s + Real.exp y - sstar) - β / γ * N * Real.exp (-γ * R * sstar) := by
    intro s' hs'
    rw [hobj, hval]
    have hγ' : -(1 / γ) < 0 := by
      have : 0 < 1 / γ := by positivity
      linarith
    refine mul_le_mul_of_nonpos_left ?_ hγ'.le
    have := hm_f_min_nonneg hγ hcN hR (R * s + Real.exp y) s' hs'
    simp only [sstar]
    rw [show β * N * R = β * N * R from rfl]
    exact this
  refine ⟨hN, le_max_left _ _, ?_, hle⟩
  have hset : hm_bookGV (hm_cara γ) β R ρ K Om 1 (fun _ => Set.Ici 0) 0 s y xh =
      sSup ((fun s' => hm_cara γ (R * s + Real.exp y - s') +
        β * ∫ y', hm_cara γ (R * s' + Real.exp y') ∂gaussianReal m (Om 1)) '' Set.Ici 0) := by
    simp only [hm_bookGV, Nat.sub_zero, hm_gV, zero_add]
    congr 1
    refine Set.image_congr (fun s' _ => ?_)
    congr 2
    refine integral_congr_ae (ae_of_all _ (fun y' => ?_))
    exact hm_terminal (β := β) (ρ := ρ) hγ K Om 1 (fun _ => Set.Ici 0) rfl s' y' m
  rw [hset]
  refine IsGreatest.csSup_eq ⟨⟨sstar, Set.mem_Ici.2 (le_max_left _ _), ?_⟩, ?_⟩
  · exact (hobj sstar).trans hval.symm
  · rintro _ ⟨s', hs', rfl⟩
    exact hle s' hs'

/-- Miao, Exercise 10.6(d): the Bellman equation with the filtered state `x̂_{t|t}`:
`x̂_{t+1|t} = ρx̂_{t|t}`, `y′ ~ N(ρx̂_{t|t}, Ω_{t+1|t})`,
`x̂_{t+1|t+1} = ρx̂_{t|t} + K_{t+1}(y′ − ρx̂_{t|t})`. -/
noncomputable def hm_gVf (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, s, y, _ => sSup ((fun s' => u (R * s + Real.exp y - s')) '' feas 0)
  | k + 1, s, y, xf => sSup ((fun s' => u (R * s + Real.exp y - s') + β *
      ∫ y', hm_gVf u β R ρ K Om T feas k s' y' (ρ * xf + K (T - k) * (y' - ρ * xf))
        ∂gaussianReal (ρ * xf) (Om (T - k))) '' feas (k + 1))

/-- **Exercise 10.6(d)** (Miao, p. 346): the Bellman equation in `x̂_{t|t}` has the same value as
the one in `x̂_{t|t−1}`: `V^f_t(s, y, x̂_{t|t−1} + K_t(y − x̂_{t|t−1})) = V_t(s, y, x̂_{t|t−1})`. -/
theorem ex_10_6_d (u : ℝ → ℝ) (β R ρ : ℝ) (K : ℕ → ℝ) (Om : ℕ → ℝ≥0) (T : ℕ)
    (feas : ℕ → Set ℝ) :
    ∀ k s y xh, hm_gVf u β R ρ K Om T feas k s y (xh + K (T - k) * (y - xh)) =
      hm_gV u β R ρ K Om T feas k s y xh
  | 0, s, y, xh => by simp only [hm_gVf, hm_gV]
  | k + 1, s, y, xh => by
    have ih := ex_10_6_d u β R ρ K Om T feas k
    have hm : ρ * (xh + K (T - (k + 1)) * (y - xh)) = ρ * xh + ρ * K (T - (k + 1)) * (y - xh) := by
      ring
    simp only [hm_gVf, hm_gV, hm, ih]

end Miao.PartialInformation

set_option linter.style.longLine false
#print axioms Miao.PartialInformation.IsSolution
#print axioms Miao.PartialInformation.IsRegular
#print axioms Miao.PartialInformation.EventuallyConst
#print axioms Miao.PartialInformation.IsStableSeq
#print axioms Miao.PartialInformation.IsSteadyStateOf
#print axioms Miao.PartialInformation.IsAsympStable
#print axioms Miao.PartialInformation.basin
#print axioms Miao.PartialInformation.IsGloballyStable
#print axioms Miao.PartialInformation.IsStableMatrix
#print axioms Miao.PartialInformation.isGloballyStable_iff_basin
#print axioms Miao.PartialInformation.isAsympStable_iff_basin
#print axioms Miao.PartialInformation.isStableSeq_iff_bddAbove
#print axioms Miao.PartialInformation.tendsto_zero_of_le_rec
#print axioms Miao.PartialInformation.tendsto_zero_of_rec
#print axioms Miao.PartialInformation.triangular_step
#print axioms Miao.PartialInformation.triangular_invariant
#print axioms Miao.PartialInformation.triangular_tendsto_iff
#print axioms Miao.PartialInformation.mclm
#print axioms Miao.PartialInformation.mclm_apply
#print axioms Miao.PartialInformation.norm_mulVec_le
#print axioms Miao.PartialInformation.norm_mclm_mul_le
#print axioms Miao.PartialInformation.tendsto_norm_mclm_pow
#print axioms Miao.PartialInformation.summable_of_tendsto_zero
#print axioms Miao.PartialInformation.diag_mul_of_upper
#print axioms Miao.PartialInformation.upper_inv
#print axioms Miao.PartialInformation.diag_inv_of_upper
#print axioms Miao.PartialInformation.summable_norm_pow_of_triangular
#print axioms Miao.PartialInformation.stableSubspace
#print axioms Miao.PartialInformation.unstableSubspace
#print axioms Miao.PartialInformation.convSubspace
#print axioms Miao.PartialInformation.mem_convSubspace
#print axioms Miao.PartialInformation.tendsto_of_mem_maxGenEigenspace
#print axioms Miao.PartialInformation.not_tendsto_of_eigen
#print axioms Miao.PartialInformation.stable_le_conv
#print axioms Miao.PartialInformation.stable_sup_unstable
#print axioms Miao.PartialInformation.disjoint_stable_unstable
#print axioms Miao.PartialInformation.unstable_invariant
#print axioms Miao.PartialInformation.tendsto_iff_mem_stable
#print axioms Miao.PartialInformation.stable_eq_top
#print axioms Miao.PartialInformation.cplx
#print axioms Miao.PartialInformation.cplx_sub
#print axioms Miao.PartialInformation.cplx_add
#print axioms Miao.PartialInformation.tendsto_cplx_iff
#print axioms Miao.PartialInformation.cplxEnd
#print axioms Miao.PartialInformation.cplxEnd_pow_cplx
#print axioms Miao.PartialInformation.hasEigenvalue_cplxEnd_iff
#print axioms Miao.PartialInformation.finrank_biSup_maxGenEigenspace
#print axioms Miao.PartialInformation.finrank_stableSubspace
#print axioms Miao.PartialInformation.conjV
#print axioms Miao.PartialInformation.conjV_conjV
#print axioms Miao.PartialInformation.conjV_add
#print axioms Miao.PartialInformation.conjV_sub
#print axioms Miao.PartialInformation.conjV_smul
#print axioms Miao.PartialInformation.conjV_zero
#print axioms Miao.PartialInformation.conjV_cplx
#print axioms Miao.PartialInformation.eq_cplx_re
#print axioms Miao.PartialInformation.cplxEnd_conjV
#print axioms Miao.PartialInformation.pow_sub_conjV
#print axioms Miao.PartialInformation.conjV_mem_maxGenEigenspace
#print axioms Miao.PartialInformation.conjV_mem_biSup
#print axioms Miao.PartialInformation.conjV_mem_stable
#print axioms Miao.PartialInformation.conjV_mem_unstable
#print axioms Miao.PartialInformation.cplxL
#print axioms Miao.PartialInformation.stableR
#print axioms Miao.PartialInformation.unstableR
#print axioms Miao.PartialInformation.mem_stableR
#print axioms Miao.PartialInformation.mem_unstableR
#print axioms Miao.PartialInformation.mem_stableR_iff
#print axioms Miao.PartialInformation.cplx_mulVec
#print axioms Miao.PartialInformation.stableR_invariant
#print axioms Miao.PartialInformation.unstableR_invariant
#print axioms Miao.PartialInformation.isCompl_stableR_unstableR
#print axioms Miao.PartialInformation.linearIndependent_cplx
#print axioms Miao.PartialInformation.finrank_le_of_cplx
#print axioms Miao.PartialInformation.finrank_stableR
#print axioms Miao.PartialInformation.unstableR_ker
#print axioms Miao.PartialInformation.uniform_bound_of_basis
#print axioms Miao.PartialInformation.exists_bound_of_tendsto
#print axioms Miao.PartialInformation.mem_maxGen_smul
#print axioms Miao.PartialInformation.projS
#print axioms Miao.PartialInformation.projU
#print axioms Miao.PartialInformation.projS_add_projU
#print axioms Miao.PartialInformation.projS_mem
#print axioms Miao.PartialInformation.projU_mem
#print axioms Miao.PartialInformation.projS_of_mem
#print axioms Miao.PartialInformation.projS_of_mem_unstable
#print axioms Miao.PartialInformation.projU_of_mem
#print axioms Miao.PartialInformation.projU_of_mem_stable
#print axioms Miao.PartialInformation.projS_mulVec
#print axioms Miao.PartialInformation.projU_mulVec
#print axioms Miao.PartialInformation.pow_mulVec_mem_stableR
#print axioms Miao.PartialInformation.tendsto_scaled_of_stable
#print axioms Miao.PartialInformation.scaled_pow_cplx
#print axioms Miao.PartialInformation.stable_bound
#print axioms Miao.PartialInformation.isStableMatrix_iff_roots
#print axioms Miao.PartialInformation.tendsto_of_isStableMatrix
#print axioms Miao.PartialInformation.isStableMatrix_of_tendsto
#print axioms Miao.PartialInformation.isStableMatrix_iff_tendsto
#print axioms Miao.PartialInformation.HasGeomDecay
#print axioms Miao.PartialInformation.hasGeomDecay_of_isStableMatrix
#print axioms Miao.PartialInformation.isStableMatrix_inv
#print axioms Miao.PartialInformation.footnote_2
#print axioms Miao.PartialInformation.isRegular_of_isUnit_det
#print axioms Miao.PartialInformation.example_scalar_not_regular
#print axioms Miao.PartialInformation.example_scalar_no_solution
#print axioms Miao.PartialInformation.remark_nonregular_no_solution
#print axioms Miao.PartialInformation.remark_nonregular_counterexample
#print axioms Miao.PartialInformation.eq_1_21
#print axioms Miao.PartialInformation.eq_1_21_solution
#print axioms Miao.PartialInformation.eq_1_21_steadyState
#print axioms Miao.PartialInformation.isSteadyStateOf_of_not_mem_range
#print axioms Miao.PartialInformation.isStableSeq_iff_exists_le
#print axioms Miao.PartialInformation.exists_mulVec_bound
#print axioms Miao.PartialInformation.bounded_mulVec
#print axioms Miao.PartialInformation.norm_sum_type_le
#print axioms Miao.PartialInformation.norm_comp_inl_le
#print axioms Miao.PartialInformation.norm_comp_inr_le
#print axioms Miao.PartialInformation.backward_sol_eq
#print axioms Miao.PartialInformation.bounded_backward
#print axioms Miao.PartialInformation.summable_geom_series
#print axioms Miao.PartialInformation.mulVec_tsum_rs
#print axioms Miao.PartialInformation.tsum_geom_series_succ
#print axioms Miao.PartialInformation.eq_zero_of_bounded_orbit
#print axioms Miao.PartialInformation.CondExpSystem
#print axioms Miao.PartialInformation.CondExpSystem.mk
#print axioms Miao.PartialInformation.CondExpSystem.E
#print axioms Miao.PartialInformation.CondExpSystem.norm_le
#print axioms Miao.PartialInformation.CondExpSystem.tower_le
#print axioms Miao.PartialInformation.CondExpSystem.tower_ge
#print axioms Miao.PartialInformation.CondExpSystem.tower_le_apply
#print axioms Miao.PartialInformation.CondExpSystem.tower_ge_apply
#print axioms Miao.PartialInformation.CondExpSystem.idem
#print axioms Miao.PartialInformation.CondExpSystem.norm_apply_le
#print axioms Miao.PartialInformation.IsAdaptedV
#print axioms Miao.PartialInformation.IsStableProc
#print axioms Miao.PartialInformation.matAct
#print axioms Miao.PartialInformation.Evec
#print axioms Miao.PartialInformation.IsRESolution
#print axioms Miao.PartialInformation.IsPredeterminedBK
#print axioms Miao.PartialInformation.Evec_matAct
#print axioms Miao.PartialInformation.matAct_add
#print axioms Miao.PartialInformation.matAct_mul
#print axioms Miao.PartialInformation.matAct_one
#print axioms Miao.PartialInformation.condExpL1_norm_apply_le
#print axioms Miao.PartialInformation.condExpL1_ae_eq_condExp
#print axioms Miao.PartialInformation.condExpL1_tower_le
#print axioms Miao.PartialInformation.condExpL1_tower_ge
#print axioms Miao.PartialInformation.condExpL1CLMK
#print axioms Miao.PartialInformation.condExpL1CLMK_apply
#print axioms Miao.PartialInformation.condExpSystemL1
#print axioms Miao.PartialInformation.condExpSystemL1_E_apply
#print axioms Miao.PartialInformation.condExpSystemL1_real
#print axioms Miao.PartialInformation.condExpSystemL1_complex
#print axioms Miao.PartialInformation.condExpSystemL1_ae_eq
#print axioms Miao.PartialInformation.condExpL1_eq_self_iff
#print axioms Miao.PartialInformation.condExpL1_eq_self_iff_exists
#print axioms Miao.PartialInformation.condExpL1_isAdaptedV_iff
#print axioms Miao.PartialInformation.l1_norm_eq_integral_abs
#print axioms Miao.PartialInformation.l1_isStableProc_iff
#print axioms Miao.PartialInformation.l1_norm_eq_integral_norm_complex
#print axioms Miao.PartialInformation.example_2_1_1
#print axioms Miao.PartialInformation.example_2_1_2
#print axioms Miao.PartialInformation.example_2_1_3
#print axioms Miao.PartialInformation.var_pow_entry_le
#print axioms Miao.PartialInformation.var_l1
#print axioms Miao.PartialInformation.var_l1_nonneg
#print axioms Miao.PartialInformation.var_sandwich_apply
#print axioms Miao.PartialInformation.var_sandwich_le
#print axioms Miao.PartialInformation.var_lyapMap
#print axioms Miao.PartialInformation.var_lyapSol
#print axioms Miao.PartialInformation.var_lyap_summable
#print axioms Miao.PartialInformation.var_lyap_iterate
#print axioms Miao.PartialInformation.lyap_iterate_tendsto
#print axioms Miao.PartialInformation.var_lyapMap_apply
#print axioms Miao.PartialInformation.var_lyapMap_continuous
#print axioms Miao.PartialInformation.lyap_fixed
#print axioms Miao.PartialInformation.lyap_unique
#print axioms Miao.PartialInformation.var_ShockMDS
#print axioms Miao.PartialInformation.var_ShockMDS.mk
#print axioms Miao.PartialInformation.var_ShockMDS.memLp
#print axioms Miao.PartialInformation.var_ShockMDS.meas
#print axioms Miao.PartialInformation.var_ShockMDS.mds
#print axioms Miao.PartialInformation.var_ShockMDS.cvar
#print axioms Miao.PartialInformation.var_Model
#print axioms Miao.PartialInformation.var_Model.mk
#print axioms Miao.PartialInformation.var_Model.eq21
#print axioms Miao.PartialInformation.var_Model.z0_memLp
#print axioms Miao.PartialInformation.var_Model.z0_meas
#print axioms Miao.PartialInformation.var_Model.shock
#print axioms Miao.PartialInformation.var_mean
#print axioms Miao.PartialInformation.var_mom
#print axioms Miao.PartialInformation.var_rec_apply
#print axioms Miao.PartialInformation.var_Model.z_memLp
#print axioms Miao.PartialInformation.var_Model.z_meas
#print axioms Miao.PartialInformation.var_cross_zero
#print axioms Miao.PartialInformation.var_mean_eps_zero
#print axioms Miao.PartialInformation.var_mom_eps
#print axioms Miao.PartialInformation.var_integral_sum_mul
#print axioms Miao.PartialInformation.var_integral_mul_sum
#print axioms Miao.PartialInformation.var_mean_rec
#print axioms Miao.PartialInformation.var_mean_eq
#print axioms Miao.PartialInformation.var_mean_tendsto_zero
#print axioms Miao.PartialInformation.var_stack
#print axioms Miao.PartialInformation.var_rec_stack
#print axioms Miao.PartialInformation.var_rec_stack_apply
#print axioms Miao.PartialInformation.var_stack_memLp
#print axioms Miao.PartialInformation.var_mom_rec
#print axioms Miao.PartialInformation.var_mom_iterate
#print axioms Miao.PartialInformation.var_mom_tendsto
#print axioms Miao.PartialInformation.var_autocov
#print axioms Miao.PartialInformation.var_IsCovStationary
#print axioms Miao.PartialInformation.definition_2_1_1_not_symmetric
#print axioms Miao.PartialInformation.var_stationary_moments
#print axioms Miao.PartialInformation.var_stationary_of_initial
#print axioms Miao.PartialInformation.var_ma_shift
#print axioms Miao.PartialInformation.var_ma
#print axioms Miao.PartialInformation.var_ma_initial_tendsto
#print axioms Miao.PartialInformation.var_impulse_response
#print axioms Miao.PartialInformation.var_IsWhiteNoise
#print axioms Miao.PartialInformation.var_integral_abs_le_sqrt
#print axioms Miao.PartialInformation.whiteNoise_stable
#print axioms Miao.PartialInformation.whiteNoise_stable_L1
#print axioms Miao.PartialInformation.mds_whiteNoise
#print axioms Miao.PartialInformation.SS.IsMarkov
#print axioms Miao.PartialInformation.SS.IsMarkov.mk
#print axioms Miao.PartialInformation.SS.IsMarkov.nonneg
#print axioms Miao.PartialInformation.SS.IsMarkov.rowsum
#print axioms Miao.PartialInformation.SS.IsDistribution
#print axioms Miao.PartialInformation.SS.IsDistribution.mk
#print axioms Miao.PartialInformation.SS.IsDistribution.nonneg
#print axioms Miao.PartialInformation.SS.IsDistribution.sum_eq_one
#print axioms Miao.PartialInformation.SS.mulVec_apply_eq
#print axioms Miao.PartialInformation.SS.IsMarkov.mul
#print axioms Miao.PartialInformation.SS.IsMarkov.pow
#print axioms Miao.PartialInformation.SS.IsMarkov.mulVec_le_mulVec
#print axioms Miao.PartialInformation.SS.IsMarkov.mulVec_const
#print axioms Miao.PartialInformation.SS.IsMarkov.abs_mulVec_le
#print axioms Miao.PartialInformation.SS.IsMarkov.norm_mulVec_le
#print axioms Miao.PartialInformation.SS.IsMarkov.abs_mulVec_sub_le
#print axioms Miao.PartialInformation.SS.GloballyStable
#print axioms Miao.PartialInformation.SS.IsContractionOn
#print axioms Miao.PartialInformation.SS.IsContractionOn.mk
#print axioms Miao.PartialInformation.SS.IsContractionOn.mapsTo
#print axioms Miao.PartialInformation.SS.IsContractionOn.nonneg
#print axioms Miao.PartialInformation.SS.IsContractionOn.lt_one
#print axioms Miao.PartialInformation.SS.IsContractionOn.norm_sub_le
#print axioms Miao.PartialInformation.SS.IsContractionOn.fixedPt_unique
#print axioms Miao.PartialInformation.SS.IsContractionOn.iterate_mem
#print axioms Miao.PartialInformation.SS.IsContractionOn.norm_iterate_sub_fixedPt_le
#print axioms Miao.PartialInformation.SS.IsContractionOn.tendsto_iterate_fixedPt
#print axioms Miao.PartialInformation.SS.IsContractionOn.exists_fixedPt
#print axioms Miao.PartialInformation.SS.IsContractionOn.globallyStable_univ
#print axioms Miao.PartialInformation.SS.fixedPt_le_of_le
#print axioms Miao.PartialInformation.SS.le_fixedPt_of_le_apply
#print axioms Miao.PartialInformation.SS.isContractionOn_of_blackwell
#print axioms Miao.PartialInformation.SS.abs_sup'_sub_sup'_le
#print axioms Miao.PartialInformation.SS.pow_nonneg_entries
#print axioms Miao.PartialInformation.SS.pow_le_pow_entries
#print axioms Miao.PartialInformation.SS.complexify
#print axioms Miao.PartialInformation.SS.complexify_apply
#print axioms Miao.PartialInformation.SS.complexify_pow
#print axioms Miao.PartialInformation.SS.complexify_transpose
#print axioms Miao.PartialInformation.SS.nnnorm_complexify
#print axioms Miao.PartialInformation.SS.norm_complexify
#print axioms Miao.PartialInformation.SS.specRad
#print axioms Miao.PartialInformation.SS.spectralRadius_complexify_ne_top
#print axioms Miao.PartialInformation.SS.specRad_nonneg
#print axioms Miao.PartialInformation.SS.mem_spectrum_iff_eigenpair
#print axioms Miao.PartialInformation.SS.tendsto_norm_pow_rpow
#print axioms Miao.PartialInformation.SS.eventually_norm_pow_le
#print axioms Miao.PartialInformation.SS.tendsto_norm_pow_zero
#print axioms Miao.PartialInformation.SS.summable_pow
#print axioms Miao.PartialInformation.SS.one_sub_mul_tsum
#print axioms Miao.PartialInformation.SS.tsum_mul_one_sub
#print axioms Miao.PartialInformation.SS.neumann_series
#print axioms Miao.PartialInformation.SS.specRad_transpose
#print axioms Miao.PartialInformation.SS.norm_le_norm_of_abs_le
#print axioms Miao.PartialInformation.SS.specRad_le_of_le
#print axioms Miao.PartialInformation.SS.rowsum_abs_le_norm
#print axioms Miao.PartialInformation.SS.norm_le_of_rowsum_abs_le
#print axioms Miao.PartialInformation.SS.abs_entry_le_norm
#print axioms Miao.PartialInformation.SS.norm_eq_of_rowsum_eq
#print axioms Miao.PartialInformation.SS.specRad_le_norm
#print axioms Miao.PartialInformation.SS.norm_le_specRad_of_mem_spectrum
#print axioms Miao.PartialInformation.SS.specRad_eq_of_rowsum_eq
#print axioms Miao.PartialInformation.SS.specRad_eq_of_colsum_eq
#print axioms Miao.PartialInformation.SS.eventually_abs_entry_pow_le
#print axioms Miao.PartialInformation.SS.OrderStable
#print axioms Miao.PartialInformation.SS.IncreasesTo
#print axioms Miao.PartialInformation.SS.DecreasesTo
#print axioms Miao.PartialInformation.SS.StronglyOrderStable
#print axioms Miao.PartialInformation.SS.orderStable_of_up_down
#print axioms Miao.PartialInformation.SS.StronglyOrderStable.orderStable
#print axioms Miao.PartialInformation.SS.dualMap
#print axioms Miao.PartialInformation.SS.orderStable_dual_iff
#print axioms Miao.PartialInformation.SS.dualMap_iterate
#print axioms Miao.PartialInformation.SS.stronglyOrderStable_dual_iff
#print axioms Miao.PartialInformation.SS.ChainComplete
#print axioms Miao.PartialInformation.SS.ChainComplete.exists_least
#print axioms Miao.PartialInformation.SS.ChainComplete.exists_fixedPt_ge
#print axioms Miao.PartialInformation.SS.ChainComplete.exists_fixedPt_le
#print axioms Miao.PartialInformation.SS.ChainComplete.exists_fixedPt
#print axioms Miao.PartialInformation.SS.ChainComplete.orderStable
#print axioms Miao.PartialInformation.SS.chainComplete_Icc
#print axioms Miao.PartialInformation.SS.CountablyDedekindComplete
#print axioms Miao.PartialInformation.SS.countablyDedekindComplete_of_conditionallyCompleteLattice
#print axioms Miao.PartialInformation.SS.CountablyDedekindComplete.dual
#print axioms Miao.PartialInformation.SS.OrderContinuous
#print axioms Miao.PartialInformation.SS.OrderContinuous.monotone
#print axioms Miao.PartialInformation.SS.isLUB_range_succ_iff
#print axioms Miao.PartialInformation.SS.tarski_kantorovich
#print axioms Miao.PartialInformation.SS.stronglyOrderStable_of_globallyStable
#print axioms Miao.PartialInformation.SS.ADP
#print axioms Miao.PartialInformation.SS.ADP.mk
#print axioms Miao.PartialInformation.SS.ADP.T
#print axioms Miao.PartialInformation.SS.ADP.mono
#print axioms Miao.PartialInformation.SS.ADP.nonempty
#print axioms Miao.PartialInformation.SS.ADP.IsGreedy
#print axioms Miao.PartialInformation.SS.ADP.VG
#print axioms Miao.PartialInformation.SS.ADP.WellPosed
#print axioms Miao.PartialInformation.SS.ADP.IsFinite
#print axioms Miao.PartialInformation.SS.ADP.Regular
#print axioms Miao.PartialInformation.SS.ADP.IsOrderStable
#print axioms Miao.PartialInformation.SS.ADP.IsStronglyOrderStable
#print axioms Miao.PartialInformation.SS.ADP.IsBellmanValue
#print axioms Miao.PartialInformation.SS.ADP.SolvesBellman
#print axioms Miao.PartialInformation.SS.ADP.IsStronglyOrderStable.isOrderStable
#print axioms Miao.PartialInformation.SS.ADP.IsOrderStable.wellPosed
#print axioms Miao.PartialInformation.SS.ADP.regular_iff
#print axioms Miao.PartialInformation.SS.ADP.greedy
#print axioms Miao.PartialInformation.SS.ADP.isGreedy_greedy
#print axioms Miao.PartialInformation.SS.ADP.bellman
#print axioms Miao.PartialInformation.SS.ADP.T_le_bellman
#print axioms Miao.PartialInformation.SS.ADP.isBellmanValue_bellman
#print axioms Miao.PartialInformation.SS.ADP.isGreedy_iff
#print axioms Miao.PartialInformation.SS.ADP.isGreedy_of_isBellmanValue
#print axioms Miao.PartialInformation.SS.ADP.solvesBellman_iff
#print axioms Miao.PartialInformation.SS.ADP.bellman_mono
#print axioms Miao.PartialInformation.SS.ADP.VU
#print axioms Miao.PartialInformation.SS.ADP.VSig
#print axioms Miao.PartialInformation.SS.ADP.VSig_inter_VG_subset
#print axioms Miao.PartialInformation.SS.ADP.vσ
#print axioms Miao.PartialInformation.SS.ADP.T_vσ
#print axioms Miao.PartialInformation.SS.ADP.eq_vσ
#print axioms Miao.PartialInformation.SS.ADP.VSig_eq_range
#print axioms Miao.PartialInformation.SS.ADP.IsOptimal
#print axioms Miao.PartialInformation.SS.ADP.IsValueFunction
#print axioms Miao.PartialInformation.SS.ADP.BellmanPrinciple
#print axioms Miao.PartialInformation.SS.ADP.FundamentalOptimality
#print axioms Miao.PartialInformation.SS.ADP.IsOptimal.isValueFunction
#print axioms Miao.PartialInformation.SS.ADP.isOptimal_of_isValueFunction
#print axioms Miao.PartialInformation.SS.ADP.isOptimal_iff
#print axioms Miao.PartialInformation.SS.ADP.bellmanPrinciple_of_solves
#print axioms Miao.PartialInformation.SS.ADP.exists_solves_iff
#print axioms Miao.PartialInformation.SS.ADP.fundamentalOptimality_iff
#print axioms Miao.PartialInformation.SS.ADP.isOptimal_iff_solvesBellman
#print axioms Miao.PartialInformation.SS.ADP.fundamentalOptimality_iff_exists_fixed
#print axioms Miao.PartialInformation.SS.ADP.IsOrderStable.fundamentalOptimality
#print axioms Miao.PartialInformation.SS.ADP.WellPosed.isOrderStable
#print axioms Miao.PartialInformation.SS.ADP.fundamentalOptimality_of_chainComplete
#print axioms Miao.PartialInformation.SS.ADP.IsSelector
#print axioms Miao.PartialInformation.SS.ADP.Regular.isSelector_greedy
#print axioms Miao.PartialInformation.SS.ADP.howard
#print axioms Miao.PartialInformation.SS.ADP.opt
#print axioms Miao.PartialInformation.SS.ADP.IsSelector.T_eq
#print axioms Miao.PartialInformation.SS.ADP.mem_VU_iff
#print axioms Miao.PartialInformation.SS.ADP.bellman_eq_of_howard_eq
#print axioms Miao.PartialInformation.SS.ADP.iterate_mono_of_le
#print axioms Miao.PartialInformation.SS.ADP.bellman_le_opt
#print axioms Miao.PartialInformation.SS.ADP.chain_2_9
#print axioms Miao.PartialInformation.SS.ADP.mapsTo_VU
#print axioms Miao.PartialInformation.SS.ADP.bellman_le_of_le
#print axioms Miao.PartialInformation.SS.ADP.iterates_of_mem_VU
#print axioms Miao.PartialInformation.SS.ADP.VFIConverges
#print axioms Miao.PartialInformation.SS.ADP.OPIConverges
#print axioms Miao.PartialInformation.SS.ADP.HPIConverges
#print axioms Miao.PartialInformation.SS.ADP.opt_one
#print axioms Miao.PartialInformation.SS.ADP.OPIConverges.vfi
#print axioms Miao.PartialInformation.SS.ADP.le_vstar_of_mem_VU
#print axioms Miao.PartialInformation.SS.ADP.IsOrderStable.le_vσ
#print axioms Miao.PartialInformation.SS.ADP.IsOrderStable.vσ_le
#print axioms Miao.PartialInformation.SS.ADP.iterates_le_vstar
#print axioms Miao.PartialInformation.SS.ADP.increasesTo_of_squeeze
#print axioms Miao.PartialInformation.SS.ADP.VFIConverges.opi_hpi
#print axioms Miao.PartialInformation.SS.ADP.VU_nonempty
#print axioms Miao.PartialInformation.SS.ADP.IsFinite.VSig_finite
#print axioms Miao.PartialInformation.SS.ADP.exists_succ_eq_of_finite
#print axioms Miao.PartialInformation.SS.ADP.fundamentalOptimality_of_finite
#print axioms Miao.PartialInformation.SS.ADP.FundamentalOptimality.exists_vstar
#print axioms Miao.PartialInformation.SS.ADP.convergence_of_chainComplete
#print axioms Miao.PartialInformation.SS.ADP.OrderBounded
#print axioms Miao.PartialInformation.SS.ADP.IsOrderContinuous
#print axioms Miao.PartialInformation.SS.ADP.le_of_orderBounded
#print axioms Miao.PartialInformation.SS.ADP.convergence_of_dedekind
#print axioms Miao.PartialInformation.SS.ADP.dual
#print axioms Miao.PartialInformation.SS.ADP.dual_dual
#print axioms Miao.PartialInformation.SS.ADP.IsMinGreedy
#print axioms Miao.PartialInformation.SS.ADP.VGmin
#print axioms Miao.PartialInformation.SS.ADP.MinRegular
#print axioms Miao.PartialInformation.SS.ADP.MinOrderBounded
#print axioms Miao.PartialInformation.SS.ADP.IsMinBellmanValue
#print axioms Miao.PartialInformation.SS.ADP.SolvesMinBellman
#print axioms Miao.PartialInformation.SS.ADP.IsMinValueFunction
#print axioms Miao.PartialInformation.SS.ADP.IsMinOptimal
#print axioms Miao.PartialInformation.SS.ADP.MinBellmanPrinciple
#print axioms Miao.PartialInformation.SS.ADP.MinFundamentalOptimality
#print axioms Miao.PartialInformation.SS.ADP.isMinGreedy_iff
#print axioms Miao.PartialInformation.SS.ADP.minRegular_iff
#print axioms Miao.PartialInformation.SS.ADP.minOrderBounded_iff
#print axioms Miao.PartialInformation.SS.ADP.isMinBellmanValue_iff
#print axioms Miao.PartialInformation.SS.ADP.VGmin_eq
#print axioms Miao.PartialInformation.SS.ADP.dual_VSig
#print axioms Miao.PartialInformation.SS.ADP.WellPosed.dual
#print axioms Miao.PartialInformation.SS.ADP.dual_vσ
#print axioms Miao.PartialInformation.SS.ADP.isMinValueFunction_iff
#print axioms Miao.PartialInformation.SS.ADP.isMinOptimal_iff
#print axioms Miao.PartialInformation.SS.ADP.dual_opt_howard
#print axioms Miao.PartialInformation.SS.ADP.minBellmanPrinciple_iff
#print axioms Miao.PartialInformation.SS.ADP.minFundamentalOptimality_iff
#print axioms Miao.PartialInformation.SS.ADP.VD
#print axioms Miao.PartialInformation.SS.ADP.MinVFIConverges
#print axioms Miao.PartialInformation.SS.ADP.minVFIConverges_iff
#print axioms Miao.PartialInformation.SS.ADP.minFundamentalOptimality_iff_exists_fixed
#print axioms Miao.PartialInformation.SS.ADP.IsOrderStable.minFundamentalOptimality
#print axioms Miao.PartialInformation.SS.LQProblem
#print axioms Miao.PartialInformation.SS.LQProblem.mk
#print axioms Miao.PartialInformation.SS.LQProblem.A
#print axioms Miao.PartialInformation.SS.LQProblem.B
#print axioms Miao.PartialInformation.SS.LQProblem.Q
#print axioms Miao.PartialInformation.SS.LQProblem.R
#print axioms Miao.PartialInformation.SS.LQProblem.Q_psd
#print axioms Miao.PartialInformation.SS.LQProblem.R_pd
#print axioms Miao.PartialInformation.SS.LQProblem.gainDen
#print axioms Miao.PartialInformation.SS.LQProblem.TF
#print axioms Miao.PartialInformation.SS.LQProblem.cost
#print axioms Miao.PartialInformation.SS.LQProblem.posSemidef_iff_real
#print axioms Miao.PartialInformation.SS.LQProblem.posDef_iff_real
#print axioms Miao.PartialInformation.SS.LQProblem.posSemidef_transpose_mul_mul
#print axioms Miao.PartialInformation.SS.LQProblem.gainDen_posDef
#print axioms Miao.PartialInformation.SS.LQProblem.dotProduct_mulVec_comm_of_symm
#print axioms Miao.PartialInformation.SS.LQProblem.mulVec_dotProduct
#print axioms Miao.PartialInformation.SS.LQProblem.dotProduct_transpose_mul_mul
#print axioms Miao.PartialInformation.SS.LQProblem.quad_add
#print axioms Miao.PartialInformation.SS.LQProblem.dotProduct_TF
#print axioms Miao.PartialInformation.SS.LQProblem.TF_posSemidef
#print axioms Miao.PartialInformation.SS.LQProblem.TF_transpose
#print axioms Miao.PartialInformation.SS.LQProblem.TF_mono
#print axioms Miao.PartialInformation.SS.LQProblem.TF_expand
#print axioms Miao.PartialInformation.SS.LQProblem.riccati
#print axioms Miao.PartialInformation.SS.LQProblem.gain
#print axioms Miao.PartialInformation.SS.LQProblem.gainDen_mul_gain
#print axioms Miao.PartialInformation.SS.LQProblem.riccati_eq_TF
#print axioms Miao.PartialInformation.SS.LQProblem.riccati_posSemidef
#print axioms Miao.PartialInformation.SS.LQProblem.cost_gain_add
#print axioms Miao.PartialInformation.SS.LQProblem.gain_isMinimizer
#print axioms Miao.PartialInformation.SS.LQProblem.gain_iff_TF_le
#print axioms Miao.PartialInformation.SS.psdCone
#print axioms Miao.PartialInformation.SS.LQProblem.closedLoop
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable
#print axioms Miao.PartialInformation.SS.LQProblem.costMat
#print axioms Miao.PartialInformation.SS.LQProblem.discCost
#print axioms Miao.PartialInformation.SS.LQProblem.TF_eq
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.entry_decay
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.tendsto_entry
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.tendsto_state
#print axioms Miao.PartialInformation.SS.LQProblem.transpose_mul_mul_apply
#print axioms Miao.PartialInformation.SS.LQProblem.tendsto_transpose_mul_mul_zero
#print axioms Miao.PartialInformation.SS.LQProblem.TF_iterate
#print axioms Miao.PartialInformation.SS.LQProblem.PF
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.hasSum_PF
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.tendsto_TF_iterate
#print axioms Miao.PartialInformation.SS.LQProblem.tendsto_TF
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.TF_PF
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.eq_PF
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.PF_posSemidef
#print axioms Miao.PartialInformation.SS.LQProblem.TFpsd
#print axioms Miao.PartialInformation.SS.LQProblem.TFpsd_iterate
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.globallyStable
#print axioms Miao.PartialInformation.SS.LQProblem.IsStable.hasSum_cost
#print axioms Miao.PartialInformation.SS.LQProblem.StablePolicy
#print axioms Miao.PartialInformation.SS.LQProblem.adp
#print axioms Miao.PartialInformation.SS.LQProblem.adp_isStronglyOrderStable
#print axioms Miao.PartialInformation.SS.LQProblem.eq_of_dotProduct_mulVec_eq
#print axioms Miao.PartialInformation.SS.LQProblem.PS
#print axioms Miao.PartialInformation.SS.LQProblem.gain_isMinGreedy
#print axioms Miao.PartialInformation.SS.LQProblem.isMinBellmanValue_riccati
#print axioms Miao.PartialInformation.SS.LQProblem.riccati_tfae
#print axioms Miao.PartialInformation.SS.LQProblem.optimality
#print axioms Miao.PartialInformation.SS.LQProblem.scalar_lifetimeCost
#print axioms Miao.PartialInformation.SS.LQProblem.scalar_compare
#print axioms Miao.PartialInformation.ls_Stable
#print axioms Miao.PartialInformation.ls_stable_iff_tendsto
#print axioms Miao.PartialInformation.ls_stable_of_specRad
#print axioms Miao.PartialInformation.ls_specRad_lt_of_stable
#print axioms Miao.PartialInformation.ls_stable_iff_specRad
#print axioms Miao.PartialInformation.ls_stable_transpose
#print axioms Miao.PartialInformation.ls_tendsto_zero_of_le_rec
#print axioms Miao.PartialInformation.ls_tendsto_zero_of_stable_input
#print axioms Miao.PartialInformation.ls_entry_eq_polar
#print axioms Miao.PartialInformation.ls_tendsto_of_quad
#print axioms Miao.PartialInformation.ls_exists_tendsto_of_quad
#print axioms Miao.PartialInformation.ls_posDef_coercive
#print axioms Miao.PartialInformation.ls_tendsto_zero_of_quad_posDef
#print axioms Miao.PartialInformation.LSProblem
#print axioms Miao.PartialInformation.LSProblem.mk
#print axioms Miao.PartialInformation.LSProblem.A
#print axioms Miao.PartialInformation.LSProblem.B
#print axioms Miao.PartialInformation.LSProblem.C
#print axioms Miao.PartialInformation.LSProblem.Q
#print axioms Miao.PartialInformation.LSProblem.R
#print axioms Miao.PartialInformation.LSProblem.S
#print axioms Miao.PartialInformation.LSProblem.β
#print axioms Miao.PartialInformation.LSProblem.loss
#print axioms Miao.PartialInformation.LSProblem.JointPSD
#print axioms Miao.PartialInformation.LSProblem.G
#print axioms Miao.PartialInformation.LSProblem.N
#print axioms Miao.PartialInformation.LSProblem.TF
#print axioms Miao.PartialInformation.LSProblem.T
#print axioms Miao.PartialInformation.LSProblem.F
#print axioms Miao.PartialInformation.LSProblem.G_posDef
#print axioms Miao.PartialInformation.LSProblem.G_transpose
#print axioms Miao.PartialInformation.LSProblem.N_transpose
#print axioms Miao.PartialInformation.LSProblem.G_mul_F
#print axioms Miao.PartialInformation.LSProblem.T_eq_sub
#print axioms Miao.PartialInformation.LSProblem.TF_expand
#print axioms Miao.PartialInformation.LSProblem.TF_F
#print axioms Miao.PartialInformation.LSProblem.TF_eq_T_add
#print axioms Miao.PartialInformation.LSProblem.TF_ge_T
#print axioms Miao.PartialInformation.LSProblem.TF_eq_T_iff
#print axioms Miao.PartialInformation.LSProblem.ls_sq_complete
#print axioms Miao.PartialInformation.LSProblem.dot_S_comm
#print axioms Miao.PartialInformation.LSProblem.loss_add_cont
#print axioms Miao.PartialInformation.LSProblem.quad_joint
#print axioms Miao.PartialInformation.LSProblem.loss_nonneg
#print axioms Miao.PartialInformation.LSProblem.Q_transpose_of_joint
#print axioms Miao.PartialInformation.LSProblem.Q_posSemidef_of_joint
#print axioms Miao.PartialInformation.LSProblem.T_transpose
#print axioms Miao.PartialInformation.LSProblem.T_posSemidef
#print axioms Miao.PartialInformation.LSShockLaw
#print axioms Miao.PartialInformation.LSShockLaw.mk
#print axioms Miao.PartialInformation.LSShockLaw.prob
#print axioms Miao.PartialInformation.LSShockLaw.int1
#print axioms Miao.PartialInformation.LSShockLaw.int2
#print axioms Miao.PartialInformation.LSShockLaw.mean
#print axioms Miao.PartialInformation.LSShockLaw.cov
#print axioms Miao.PartialInformation.ls_quad_shock_expand
#print axioms Miao.PartialInformation.ls_integral_quad
#print axioms Miao.PartialInformation.LSProblem.bellObj
#print axioms Miao.PartialInformation.LSProblem.bellObj_quad
#print axioms Miao.PartialInformation.LSProblem.bellObj_isGreatest
#print axioms Miao.PartialInformation.LSProblem.ls_foc
#print axioms Miao.PartialInformation.LSProblem.ls_first_variation
#print axioms Miao.PartialInformation.LSFinProblem
#print axioms Miao.PartialInformation.LSFinProblem.mk
#print axioms Miao.PartialInformation.LSFinProblem.A
#print axioms Miao.PartialInformation.LSFinProblem.B
#print axioms Miao.PartialInformation.LSFinProblem.C
#print axioms Miao.PartialInformation.LSFinProblem.Q
#print axioms Miao.PartialInformation.LSFinProblem.R
#print axioms Miao.PartialInformation.LSFinProblem.S
#print axioms Miao.PartialInformation.LSFinProblem.β
#print axioms Miao.PartialInformation.LSFinProblem.hor
#print axioms Miao.PartialInformation.LSFinProblem.PT
#print axioms Miao.PartialInformation.LSFinProblem.stage
#print axioms Miao.PartialInformation.LSFinProblem.Pbk
#print axioms Miao.PartialInformation.LSFinProblem.dbk
#print axioms Miao.PartialInformation.LSFinProblem.P
#print axioms Miao.PartialInformation.LSFinProblem.d
#print axioms Miao.PartialInformation.LSFinProblem.Fg
#print axioms Miao.PartialInformation.LSFinProblem.Vbk
#print axioms Miao.PartialInformation.LSFinProblem.V
#print axioms Miao.PartialInformation.LSFinProblem.P_hor
#print axioms Miao.PartialInformation.LSFinProblem.d_hor
#print axioms Miao.PartialInformation.LSFinProblem.V_hor
#print axioms Miao.PartialInformation.LSFinProblem.P_succ
#print axioms Miao.PartialInformation.LSFinProblem.d_succ
#print axioms Miao.PartialInformation.LSFinProblem.V_succ
#print axioms Miao.PartialInformation.LSFinProblem.proposition_9_2_1
#print axioms Miao.PartialInformation.LSFinProblem.eq_9_9
#print axioms Miao.PartialInformation.LSFinProblem.ls_finite_seq_identity
#print axioms Miao.PartialInformation.LSFinProblem.ls_finite_seq_optimal
#print axioms Miao.PartialInformation.LSFinProblem.zeroC
#print axioms Miao.PartialInformation.LSFinProblem.zeroC_Pbk
#print axioms Miao.PartialInformation.LSFinProblem.zeroC_dbk
#print axioms Miao.PartialInformation.LSFinProblem.certainty_equivalence
#print axioms Miao.PartialInformation.LSAssumption911
#print axioms Miao.PartialInformation.LSAssumption911.mk
#print axioms Miao.PartialInformation.LSAssumption911.mean
#print axioms Miao.PartialInformation.LSAssumption911.cov
#print axioms Miao.PartialInformation.ls_condExp_quad
#print axioms Miao.PartialInformation.ls_state
#print axioms Miao.PartialInformation.ls_traj
#print axioms Miao.PartialInformation.ls_output
#print axioms Miao.PartialInformation.ls_Stabilizable
#print axioms Miao.PartialInformation.definition_9_1_1_closed_loop
#print axioms Miao.PartialInformation.definition_9_1_1_steady_state
#print axioms Miao.PartialInformation.ls_gram
#print axioms Miao.PartialInformation.ls_Controllable
#print axioms Miao.PartialInformation.ls_gram_quad
#print axioms Miao.PartialInformation.ls_gram_posSemidef
#print axioms Miao.PartialInformation.ls_dot_self_nonneg
#print axioms Miao.PartialInformation.ls_gram_posDef_iff
#print axioms Miao.PartialInformation.ls_traj_eq
#print axioms Miao.PartialInformation.ls_reach_of_gram
#print axioms Miao.PartialInformation.definition_9_1_2_iff
#print axioms Miao.PartialInformation.ls_controllable_not_reach_one
#print axioms Miao.PartialInformation.ls_stabilizable_not_controllable
#print axioms Miao.PartialInformation.ls_Observable
#print axioms Miao.PartialInformation.ls_observable_gram
#print axioms Miao.PartialInformation.ls_state_sub
#print axioms Miao.PartialInformation.definition_9_1_3_iff
#print axioms Miao.PartialInformation.ls_observable_not_two_outputs
#print axioms Miao.PartialInformation.ls_Detectable
#print axioms Miao.PartialInformation.eq_9_3_error
#print axioms Miao.PartialInformation.eq_9_3_tendsto
#print axioms Miao.PartialInformation.eq_9_3_misprint
#print axioms Miao.PartialInformation.definition_9_1_4_rule
#print axioms Miao.PartialInformation.ls_riccati_le_TF
#print axioms Miao.PartialInformation.ls_posSemidef_of_le
#print axioms Miao.PartialInformation.ls_quad_le
#print axioms Miao.PartialInformation.ls_riccati_mono
#print axioms Miao.PartialInformation.ls_iter_psd
#print axioms Miao.PartialInformation.ls_iter_mono_le
#print axioms Miao.PartialInformation.ls_zero_le_psd
#print axioms Miao.PartialInformation.ls_iter_zero_mono
#print axioms Miao.PartialInformation.ls_iter_zero_mono_add
#print axioms Miao.PartialInformation.ls_finite_lower
#print axioms Miao.PartialInformation.ls_iter_le_PF
#print axioms Miao.PartialInformation.ls_iter_bdd_of_controllable
#print axioms Miao.PartialInformation.ls_tendsto_quad
#print axioms Miao.PartialInformation.ls_iter_converges
#print axioms Miao.PartialInformation.ls_tendsto_mul
#print axioms Miao.PartialInformation.ls_tendsto_inv
#print axioms Miao.PartialInformation.ls_tendsto_gain
#print axioms Miao.PartialInformation.ls_tendsto_riccati
#print axioms Miao.PartialInformation.ls_fixed_of_tendsto
#print axioms Miao.PartialInformation.ls_Detects
#print axioms Miao.PartialInformation.ls_cost_tendsto_zero
#print axioms Miao.PartialInformation.ls_stable_of_fixed
#print axioms Miao.PartialInformation.ls_detects_of_posDef
#print axioms Miao.PartialInformation.ls_tendsto_mulVec_zero
#print axioms Miao.PartialInformation.ls_tendsto_L
#print axioms Miao.PartialInformation.ls_detects_of_detectable
#print axioms Miao.PartialInformation.ls_detects_of_observable
#print axioms Miao.PartialInformation.ls_riccati_main
#print axioms Miao.PartialInformation.LSProblem.toSS
#print axioms Miao.PartialInformation.LSProblem.toSS_gainDen
#print axioms Miao.PartialInformation.LSProblem.toSS_riccati
#print axioms Miao.PartialInformation.LSProblem.toSS_gain
#print axioms Miao.PartialInformation.LSProblem.toSS_closedLoop
#print axioms Miao.PartialInformation.LSProblem.toSS_costMat
#print axioms Miao.PartialInformation.LSProblem.toSS_riccati_iter
#print axioms Miao.PartialInformation.LSProblem.loss_S_zero
#print axioms Miao.PartialInformation.LSProblem.ls_discount_rescale
#print axioms Miao.PartialInformation.LSProblem.toFin
#print axioms Miao.PartialInformation.LSProblem.toFin_stage
#print axioms Miao.PartialInformation.LSProblem.toFin_Pbk
#print axioms Miao.PartialInformation.LSProblem.dIter
#print axioms Miao.PartialInformation.LSProblem.toFin_dbk
#print axioms Miao.PartialInformation.LSProblem.eq_9_11
#print axioms Miao.PartialInformation.LSProblem.T_zero_S
#print axioms Miao.PartialInformation.LSProblem.ls_P_one
#print axioms Miao.PartialInformation.LSProblem.ls_P_mono
#print axioms Miao.PartialInformation.LSProblem.ls_P_mono_not_strict
#print axioms Miao.PartialInformation.LSProblem.ls_discounted_main
#print axioms Miao.PartialInformation.LSProblem.proposition_9_3_1
#print axioms Miao.PartialInformation.LSProblem.proposition_9_3_2
#print axioms Miao.PartialInformation.LSProblem.eq_9_13
#print axioms Miao.PartialInformation.LSProblem.ls_sqrt_sandwich
#print axioms Miao.PartialInformation.LSProblem.eq_9_13_series
#print axioms Miao.PartialInformation.LSProblem.eq_9_14
#print axioms Miao.PartialInformation.LSProblem.ls_P_le_policy
#print axioms Miao.PartialInformation.LSProblem.ls_P_le_policy_misprint
#print axioms Miao.PartialInformation.LSProblem.ls_infinite_value
#print axioms Miao.PartialInformation.LSProblem.eq_9_16_9_17
#print axioms Miao.PartialInformation.controllable_stabilizable
#print axioms Miao.PartialInformation.eq_9_10_growth
#print axioms Miao.PartialInformation.ls_stable_of_side_condition
#print axioms Miao.PartialInformation.LSProblem.ls_G_tendsto
#print axioms Miao.PartialInformation.LSProblem.ls_N_tendsto
#print axioms Miao.PartialInformation.LSProblem.ls_F_tendsto
#print axioms Miao.PartialInformation.LSProblem.ls_dIter_tendsto
#print axioms Miao.PartialInformation.LSProblem.ls_policy_riccati
#print axioms Miao.PartialInformation.LSProblem.ls_policy_lyapunov
#print axioms Miao.PartialInformation.LSProblem.ls_lagrange
#print axioms Miao.PartialInformation.LSProblem.ls_envelope
#print axioms Miao.PartialInformation.LSProblem.ls_verification
#print axioms Miao.PartialInformation.kf_L2
#print axioms Miao.PartialInformation.kf_app
#print axioms Miao.PartialInformation.kf_mean
#print axioms Miao.PartialInformation.kf_L2_app
#print axioms Miao.PartialInformation.kf_L2_add
#print axioms Miao.PartialInformation.kf_L2_sub
#print axioms Miao.PartialInformation.kf_L2_const
#print axioms Miao.PartialInformation.kf_L2_zero
#print axioms Miao.PartialInformation.kf_mom_transpose
#print axioms Miao.PartialInformation.kf_mom_app_left
#print axioms Miao.PartialInformation.kf_mom_app_right
#print axioms Miao.PartialInformation.kf_mom_add_left
#print axioms Miao.PartialInformation.kf_mom_sub_left
#print axioms Miao.PartialInformation.kf_mom_add_right
#print axioms Miao.PartialInformation.kf_mom_sub_right
#print axioms Miao.PartialInformation.kf_mom_const_left
#print axioms Miao.PartialInformation.kf_mean_app
#print axioms Miao.PartialInformation.kf_mean_add
#print axioms Miao.PartialInformation.kf_mean_sub
#print axioms Miao.PartialInformation.kf_app_add
#print axioms Miao.PartialInformation.kf_app_sub
#print axioms Miao.PartialInformation.kf_app_app
#print axioms Miao.PartialInformation.kf_app_zero_mat
#print axioms Miao.PartialInformation.kf_app_sub_mat
#print axioms Miao.PartialInformation.kf_mom_const_right
#print axioms Miao.PartialInformation.kf_mean_const
#print axioms Miao.PartialInformation.kf_mom_lin2
#print axioms Miao.PartialInformation.kf_mom_lin_sub
#print axioms Miao.PartialInformation.kf_mom_self_psd
#print axioms Miao.PartialInformation.kf_Om
#print axioms Miao.PartialInformation.kf_Mx
#print axioms Miao.PartialInformation.kf_gain
#print axioms Miao.PartialInformation.kf_joseph
#print axioms Miao.PartialInformation.kf_filtCov
#print axioms Miao.PartialInformation.kf_Om_transpose
#print axioms Miao.PartialInformation.kf_Mx_transpose
#print axioms Miao.PartialInformation.kf_joseph_expand
#print axioms Miao.PartialInformation.kf_joseph_complete
#print axioms Miao.PartialInformation.eq_10_11_gain
#print axioms Miao.PartialInformation.kf_filtCov_eq
#print axioms Miao.PartialInformation.kf_diag_sandwich
#print axioms Miao.PartialInformation.kf_trace_sandwich
#print axioms Miao.PartialInformation.eq_10_10
#print axioms Miao.PartialInformation.kf_trace_perturb
#print axioms Miao.PartialInformation.eq_10_10_foc
#print axioms Miao.PartialInformation.kf_riccati_pred
#print axioms Miao.PartialInformation.KFSystem
#print axioms Miao.PartialInformation.KFSystem.mk
#print axioms Miao.PartialInformation.KFSystem.A
#print axioms Miao.PartialInformation.KFSystem.B
#print axioms Miao.PartialInformation.KFSystem.C
#print axioms Miao.PartialInformation.KFSystem.G
#print axioms Miao.PartialInformation.KFSystem.H
#print axioms Miao.PartialInformation.KFSystem.D
#print axioms Miao.PartialInformation.KFSystem.xbar0
#print axioms Miao.PartialInformation.KFSystem.S0
#print axioms Miao.PartialInformation.KFSystem.Cl
#print axioms Miao.PartialInformation.KFSystem.Spred
#print axioms Miao.PartialInformation.KFSystem.Om
#print axioms Miao.PartialInformation.KFSystem.K
#print axioms Miao.PartialInformation.KFSystem.Sfilt
#print axioms Miao.PartialInformation.KFSystem.inp
#print axioms Miao.PartialInformation.KFSystem.xpred
#print axioms Miao.PartialInformation.KFSystem.innov
#print axioms Miao.PartialInformation.KFSystem.xfilt
#print axioms Miao.PartialInformation.KFSystem.err
#print axioms Miao.PartialInformation.KFSystem.xpred_succ
#print axioms Miao.PartialInformation.KFSystem.kf_innov_eq
#print axioms Miao.PartialInformation.KFSystem.kf_err_succ
#print axioms Miao.PartialInformation.KFSystem.err_zero
#print axioms Miao.PartialInformation.KFSystem.kf_err_control_free
#print axioms Miao.PartialInformation.KFSystem.kf_step
#print axioms Miao.PartialInformation.KFSystem.kf_moments
#print axioms Miao.PartialInformation.KFSystem.kf_innov_L2
#print axioms Miao.PartialInformation.KFSystem.eq_10_9
#print axioms Miao.PartialInformation.KFSystem.eq_10_8
#print axioms Miao.PartialInformation.KFSystem.eq_10_11
#print axioms Miao.PartialInformation.KFSystem.kf_filt_err
#print axioms Miao.PartialInformation.KFSystem.kf_filt_moments
#print axioms Miao.PartialInformation.KFSystem.eq_10_10_random
#print axioms Miao.PartialInformation.KFSystem.kf_shock_innov
#print axioms Miao.PartialInformation.KFSystem.kf_err_orth
#print axioms Miao.PartialInformation.KFSystem.kf_innov_orth
#print axioms Miao.PartialInformation.KFSystem.kf_filt_orth
#print axioms Miao.PartialInformation.KFSystem.kf_wsum
#print axioms Miao.PartialInformation.KFSystem.kf_wsum_moments
#print axioms Miao.PartialInformation.KFSystem.eq_10_12
#print axioms Miao.PartialInformation.KFSystem.kf_pred_recursive
#print axioms Miao.PartialInformation.KFSystem.kf_filt_recursive
#print axioms Miao.PartialInformation.KFSystem.kf_riccati_Spred
#print axioms Miao.PartialInformation.KFSystem.kf_riccati_Sfilt
#print axioms Miao.PartialInformation.kf_twoPoint
#print axioms Miao.PartialInformation.kf_twoPoint_prob
#print axioms Miao.PartialInformation.kf_twoPoint_integral
#print axioms Miao.PartialInformation.kf_cross_book_false
#print axioms Miao.PartialInformation.KFSystem.const
#print axioms Miao.PartialInformation.kf_step1_mean
#print axioms Miao.PartialInformation.kf_step1_cov
#print axioms Miao.PartialInformation.kf_dual
#print axioms Miao.PartialInformation.kf_dual_T
#print axioms Miao.PartialInformation.kf_steadyGain
#print axioms Miao.PartialInformation.kf_const_Spred
#print axioms Miao.PartialInformation.kf_steady_state
#print axioms Miao.PartialInformation.kf_steady_fixed
#print axioms Miao.PartialInformation.kf_laborG
#print axioms Miao.PartialInformation.example_10_1_1
#print axioms Miao.PartialInformation.example_10_1_1_misprint
#print axioms Miao.PartialInformation.kf_inv_fin_one
#print axioms Miao.PartialInformation.kf_scalarSys
#print axioms Miao.PartialInformation.kf_scalarRic
#print axioms Miao.PartialInformation.kf_scalarRoot
#print axioms Miao.PartialInformation.kf_scalar_CD
#print axioms Miao.PartialInformation.kf_scalar_DD
#print axioms Miao.PartialInformation.kf_scalar_xpred
#print axioms Miao.PartialInformation.kf_scalar_dualT
#print axioms Miao.PartialInformation.kf_scalar_filter
#print axioms Miao.PartialInformation.kf_scalarRic_nonneg
#print axioms Miao.PartialInformation.kf_scalar_tendsto
#print axioms Miao.PartialInformation.example_10_1_2
#print axioms Miao.PartialInformation.example_10_1_2_adaptive
#print axioms Miao.PartialInformation.example_10_1_2_constant
#print axioms Miao.PartialInformation.example_10_1_3
#print axioms Miao.PartialInformation.example_10_1_3_filter
#print axioms Miao.PartialInformation.kf_gaussDens
#print axioms Miao.PartialInformation.kf_logDens
#print axioms Miao.PartialInformation.example_10_1_4
#print axioms Miao.PartialInformation.KFSystem.kf_Delta_succ
#print axioms Miao.PartialInformation.kf_filtProblem
#print axioms Miao.PartialInformation.kf_filt_T
#print axioms Miao.PartialInformation.kf_loss_expand
#print axioms Miao.PartialInformation.kf_expected_loss
#print axioms Miao.PartialInformation.kf_expected_cont
#print axioms Miao.PartialInformation.kf_piObj
#print axioms Miao.PartialInformation.kf_certainty_equivalence
#print axioms Miao.PartialInformation.ex_10_1
#print axioms Miao.PartialInformation.ex_10_2_nonlinear
#print axioms Miao.PartialInformation.ex_10_2
#print axioms Miao.PartialInformation.ex_10_3
#print axioms Miao.PartialInformation.ex_10_3_mse
#print axioms Miao.PartialInformation.kf_ex4Dual
#print axioms Miao.PartialInformation.kf_ex4Sig
#print axioms Miao.PartialInformation.kf_ex4Gain
#print axioms Miao.PartialInformation.kf_ex4Est
#print axioms Miao.PartialInformation.ex_10_4_gain
#print axioms Miao.PartialInformation.ex_10_4_err
#print axioms Miao.PartialInformation.kf_mom_two
#print axioms Miao.PartialInformation.kf_ex4_TF
#print axioms Miao.PartialInformation.ex_10_4
#print axioms Miao.PartialInformation.ex_10_4_equiv
#print axioms Miao.PartialInformation.ex_10_5
#print axioms Miao.PartialInformation.hm_sum_snoc
#print axioms Miao.PartialInformation.hm_sum_fin_one
#print axioms Miao.PartialInformation.hm_weight
#print axioms Miao.PartialInformation.hm_weight_snoc
#print axioms Miao.PartialInformation.hm_joint
#print axioms Miao.PartialInformation.hm_lik
#print axioms Miao.PartialInformation.hm_post
#print axioms Miao.PartialInformation.hm_predJoint
#print axioms Miao.PartialInformation.hm_pred
#print axioms Miao.PartialInformation.hm_lik_eq
#print axioms Miao.PartialInformation.hm_predJoint_eq
#print axioms Miao.PartialInformation.hm_joint_snoc
#print axioms Miao.PartialInformation.hm_joint_forward
#print axioms Miao.PartialInformation.hm_joint_zero
#print axioms Miao.PartialInformation.hm_predJoint_sum
#print axioms Miao.PartialInformation.hm_pred_eq
#print axioms Miao.PartialInformation.hm_post_update
#print axioms Miao.PartialInformation.hm_lik_snoc
#print axioms Miao.PartialInformation.hm_weight_nonneg
#print axioms Miao.PartialInformation.hm_joint_nonneg
#print axioms Miao.PartialInformation.hm_post_sum
#print axioms Miao.PartialInformation.hm_post_nonneg
#print axioms Miao.PartialInformation.hm_lik_sum
#print axioms Miao.PartialInformation.hm_stateLaw
#print axioms Miao.PartialInformation.hm_pairLaw
#print axioms Miao.PartialInformation.hm_margLaw
#print axioms Miao.PartialInformation.hm_markov
#print axioms Miao.PartialInformation.hm_e
#print axioms Miao.PartialInformation.hm_transpose_mulVec_e
#print axioms Miao.PartialInformation.hm_condE
#print axioms Miao.PartialInformation.hm_condE_id
#print axioms Miao.PartialInformation.eq_10_13
#print axioms Miao.PartialInformation.hm_condE_mds
#print axioms Miao.PartialInformation.eq_10_13_mds
#print axioms Miao.PartialInformation.hm_unit_outer
#print axioms Miao.PartialInformation.hm_vv_expansion
#print axioms Miao.PartialInformation.hm_condE_cov
#print axioms Miao.PartialInformation.eq_10_13_cov
#print axioms Miao.PartialInformation.eq_10_14
#print axioms Miao.PartialInformation.eq_10_14_mds
#print axioms Miao.PartialInformation.eq_10_14_cov
#print axioms Miao.PartialInformation.hm_bayes_joint
#print axioms Miao.PartialInformation.hm_bayes
#print axioms Miao.PartialInformation.hm_bayes_initial
#print axioms Miao.PartialInformation.hm_margLaw_succ
#print axioms Miao.PartialInformation.hm_stationary_marg
#print axioms Miao.PartialInformation.hm_hamilton_predict
#print axioms Miao.PartialInformation.hm_hamilton_update
#print axioms Miao.PartialInformation.hm_switch_law
#print axioms Miao.PartialInformation.hm_switchDensity
#print axioms Miao.PartialInformation.hm_switch_density
#print axioms Miao.PartialInformation.hm_switch_predictive
#print axioms Miao.PartialInformation.hm_switch_logodds
#print axioms Miao.PartialInformation.hm_two_state_stationary
#print axioms Miao.PartialInformation.HMPOMDP
#print axioms Miao.PartialInformation.HMPOMDP.mk
#print axioms Miao.PartialInformation.HMPOMDP.a
#print axioms Miao.PartialInformation.HMPOMDP.q
#print axioms Miao.PartialInformation.HMPOMDP.r
#print axioms Miao.PartialInformation.HMPOMDP.R
#print axioms Miao.PartialInformation.HMPOMDP.β
#print axioms Miao.PartialInformation.hm_at
#print axioms Miao.PartialInformation.hm_at_sum
#print axioms Miao.PartialInformation.hm_nextM
#print axioms Miao.PartialInformation.hm_py
#print axioms Miao.PartialInformation.hm_bayesNext
#print axioms Miao.PartialInformation.hm_V
#print axioms Miao.PartialInformation.hm_obj
#print axioms Miao.PartialInformation.hm_V_succ
#print axioms Miao.PartialInformation.hm_bookV
#print axioms Miao.PartialInformation.hm_bellman_terminal
#print axioms Miao.PartialInformation.hm_bellman
#print axioms Miao.PartialInformation.hm_pre
#print axioms Miao.PartialInformation.hm_cw
#print axioms Miao.PartialInformation.hm_rew
#print axioms Miao.PartialInformation.hm_J
#print axioms Miao.PartialInformation.hm_shift
#print axioms Miao.PartialInformation.hm_sum_cons
#print axioms Miao.PartialInformation.hm_pre_cons_succ
#print axioms Miao.PartialInformation.hm_pre_zero
#print axioms Miao.PartialInformation.hm_cw_cons_sum
#print axioms Miao.PartialInformation.hm_cw_decomp
#print axioms Miao.PartialInformation.hm_cw_mass
#print axioms Miao.PartialInformation.hm_rew_cons
#print axioms Miao.PartialInformation.hm_J_succ
#print axioms Miao.PartialInformation.hm_J_zero
#print axioms Miao.PartialInformation.hm_nextM_nonneg
#print axioms Miao.PartialInformation.hm_nextM_smul
#print axioms Miao.PartialInformation.hm_bayesNext_smul
#print axioms Miao.PartialInformation.hm_sup'_mul
#print axioms Miao.PartialInformation.hm_V_smul
#print axioms Miao.PartialInformation.hm_py_mul_V
#print axioms Miao.PartialInformation.hm_J_le_V
#print axioms Miao.PartialInformation.hm_greedy
#print axioms Miao.PartialInformation.hm_greedy_spec
#print axioms Miao.PartialInformation.hm_beliefPol
#print axioms Miao.PartialInformation.hm_shift_beliefPol
#print axioms Miao.PartialInformation.hm_J_beliefPol
#print axioms Miao.PartialInformation.hm_value_isGreatest
#print axioms Miao.PartialInformation.hm_posterior_one_step
#print axioms Miao.PartialInformation.eq_10_16
#print axioms Miao.PartialInformation.ex_10_6_a_shocks
#print axioms Miao.PartialInformation.hm_kOmega
#print axioms Miao.PartialInformation.hm_kGain
#print axioms Miao.PartialInformation.hm_kMSE
#print axioms Miao.PartialInformation.hm_mse_eq
#print axioms Miao.PartialInformation.hm_mse_min
#print axioms Miao.PartialInformation.hm_mse_le
#print axioms Miao.PartialInformation.ex_10_6_a_gain
#print axioms Miao.PartialInformation.hm_kSig
#print axioms Miao.PartialInformation.hm_kK
#print axioms Miao.PartialInformation.hm_kOm
#print axioms Miao.PartialInformation.hm_kSig_nonneg
#print axioms Miao.PartialInformation.ex_10_6_a_riccati
#print axioms Miao.PartialInformation.ex_10_6_a_recursion
#print axioms Miao.PartialInformation.hm_gauss_bayes
#print axioms Miao.PartialInformation.hm_gauss_marginal
#print axioms Miao.PartialInformation.hm_gauss_predict
#print axioms Miao.PartialInformation.ex_10_6_a_predictive
#print axioms Miao.PartialInformation.hm_cara
#print axioms Miao.PartialInformation.hm_gV
#print axioms Miao.PartialInformation.hm_bookGV
#print axioms Miao.PartialInformation.example_10_2_1
#print axioms Miao.PartialInformation.example_10_2_1_terminal
#print axioms Miao.PartialInformation.hm_exp_tangent
#print axioms Miao.PartialInformation.hm_f
#print axioms Miao.PartialInformation.hm_f_tangent
#print axioms Miao.PartialInformation.hm_f_min
#print axioms Miao.PartialInformation.hm_f_min_nonneg
#print axioms Miao.PartialInformation.hm_a
#print axioms Miao.PartialInformation.hm_a_pos
#print axioms Miao.PartialInformation.hm_a_inv
#print axioms Miao.PartialInformation.hm_phi
#print axioms Miao.PartialInformation.hm_N
#print axioms Miao.PartialInformation.hm_phi_succ
#print axioms Miao.PartialInformation.hm_N_props
#print axioms Miao.PartialInformation.hm_phi_props
#print axioms Miao.PartialInformation.hm_closed
#print axioms Miao.PartialInformation.hm_terminal
#print axioms Miao.PartialInformation.hm_int_closed
#print axioms Miao.PartialInformation.hm_obj_eq
#print axioms Miao.PartialInformation.hm_step
#print axioms Miao.PartialInformation.ex_10_6_c
#print axioms Miao.PartialInformation.ex_10_6_c_policy
#print axioms Miao.PartialInformation.ex_10_6_b_terminal
#print axioms Miao.PartialInformation.ex_10_6_b
#print axioms Miao.PartialInformation.hm_gVf
#print axioms Miao.PartialInformation.ex_10_6_d
