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
import Mathlib.Probability.ConditionalExpectation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Scalar linear rational expectations models

Copied from `EconomicDynamics/RationalExpectations` (module `ScalarRE`), namespace renamed.

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Optimal policy under commitment: the Ramsey problem and its first-order conditions

Copied from `EconomicDynamics/LinearQuadratic` (module `CPRamsey`), namespace renamed.

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian model under commitment: Examples 9.4.1 and 9.4.2

Copied from `EconomicDynamics/LinearQuadratic` (module `CPNKCommitment`), namespace renamed.

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian model under discretion: Example 9.5.1, and commitment versus discretion

Copied from `EconomicDynamics/LinearQuadratic` (module `CPNKDiscretion`), namespace renamed.

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

namespace Miao.NewKeynesian

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

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic DNK model: households (Miao §19.1.1)

Miao, §19.1.1, pp. 616–618. The household has the separable money-in-the-utility period utility
(19.1) `u(C, N, m) = C^{1−γ}/(1 − γ) − χN^{1+ν}/(1 + ν) + m^{1−ϕ}/(1 − ϕ)`.

* The partial derivatives of (19.1) and the sign conditions `u₁ > 0`, `u₂ < 0`, `u₃ > 0`,
  `u₁₁ < 0`, `u₂₂ < 0`, `u₃₃ < 0` (`nk_u_C`, `nk_u_N`, `nk_u_m`, `nk_u_CC`, `nk_u_NN`, `nk_u_mm`,
  `nk_u_signs`), for `γ, ϕ ≠ 1` (the printed formula is undefined at `γ = 1` or `ϕ = 1`) and
  `χ > 0` (needed for `u₂ < 0`, not stated in the book).
* The satiation assumption "`u₃(·, ·, m) ≤ 0` for `m > m*`" quoted on p. 617 fails for (19.1):
  `u₃ = m^{−ϕ} > 0` everywhere (`nk_u_no_satiation`).
* (19.2) from the first-order conditions for `C_t` and `N_t` (`eq_19_2`).
* (19.3), the consumption Euler equation, from the bond first-order condition; `E_t` is
  Mathlib's conditional expectation `μ[·|ℱ_t]` and the `F_t`-measurable factor `C_t^γP_t` is
  pulled out of it (`eq_19_3`).
* (19.4), the money demand equation, from the money and bond first-order conditions
  (`eq_19_4`); solving it for the money supply (p. 622) needs `i_t > 0`, and then
  `M_{t+1} = P_t(C_t^{−γ}i_t/(1 + i_t))^{−1/ϕ}` (`nk_money_supply`, `nk_money_demand_pos_rate`).

The first-order conditions themselves are listed, not derived, in the book; they are the
hypotheses here (with `Λ_t = C_t^{−γ}` for the `C_t` condition). The transversality conditions
are stated in the book and play no role in the derivations.
-/

open MeasureTheory

namespace Miao.NewKeynesian

/-- The period utility (19.1) (Miao, p. 617):
`u(C, N, m) = C^{1−γ}/(1 − γ) − χN^{1+ν}/(1 + ν) + m^{1−ϕ}/(1 − ϕ)`. -/
noncomputable def nk_u (γ ν ϕ χ C N m : ℝ) : ℝ :=
  C ^ (1 - γ) / (1 - γ) - χ * N ^ (1 + ν) / (1 + ν) + m ^ (1 - ϕ) / (1 - ϕ)

/-- `d/dx [x^{1−a}/(1 − a)] = x^{−a}` for `x > 0`, `a ≠ 1`. -/
theorem nk_hasDerivAt_pow_div {a x : ℝ} (ha : a ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y ^ (1 - a) / (1 - a)) (x ^ (-a)) x := by
  have h1 : (1 : ℝ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have h := (Real.hasDerivAt_rpow_const (p := 1 - a) (Or.inl hx.ne')).div_const (1 - a)
  convert h using 1
  rw [show (1 : ℝ) - a - 1 = -a by ring]
  field_simp

/-- (19.1), Miao, p. 617: `u₁ = C^{−γ}`. -/
theorem nk_u_C {γ ν ϕ χ C N m : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun c => nk_u γ ν ϕ χ c N m) (C ^ (-γ)) C := by
  have h := ((nk_hasDerivAt_pow_div hγ hC).sub_const (χ * N ^ (1 + ν) / (1 + ν))).add_const
    (m ^ (1 - ϕ) / (1 - ϕ))
  exact h

/-- (19.1), Miao, p. 617: `u₂ = −χN^ν`. -/
theorem nk_u_N {γ ν ϕ χ C N m : ℝ} (hν : 0 < ν) (hN : 0 < N) :
    HasDerivAt (fun n => nk_u γ ν ϕ χ C n m) (-(χ * N ^ ν)) N := by
  have h1 : (1 : ℝ) + ν ≠ 0 := by linarith
  have hd := ((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + ν)
  have h := (hd.const_sub (C ^ (1 - γ) / (1 - γ))).add_const (m ^ (1 - ϕ) / (1 - ϕ))
  convert h using 1
  · funext n
    simp only [nk_u]
  · rw [show (1 : ℝ) + ν - 1 = ν by ring]
    field_simp

/-- (19.1), Miao, p. 617: `u₃ = m^{−ϕ}`. -/
theorem nk_u_m {γ ν ϕ χ C N m : ℝ} (hϕ : ϕ ≠ 1) (hm : 0 < m) :
    HasDerivAt (fun x => nk_u γ ν ϕ χ C N x) (m ^ (-ϕ)) m := by
  have h := (nk_hasDerivAt_pow_div hϕ hm).const_add
    (C ^ (1 - γ) / (1 - γ) - χ * N ^ (1 + ν) / (1 + ν))
  exact h

/-- (19.1), Miao, p. 617: `u₁₁ = −γC^{−γ−1}`. -/
theorem nk_u_CC {γ C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun c : ℝ => c ^ (-γ)) (-γ * C ^ (-γ - 1)) C :=
  Real.hasDerivAt_rpow_const (Or.inl hC.ne')

/-- (19.1), Miao, p. 617: `u₂₂ = −χνN^{ν−1}`. -/
theorem nk_u_NN {ν χ N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n : ℝ => -(χ * n ^ ν)) (-(χ * (ν * N ^ (ν - 1)))) N :=
  ((Real.hasDerivAt_rpow_const (Or.inl hN.ne')).const_mul χ).neg

/-- (19.1), Miao, p. 617: `u₃₃ = −ϕm^{−ϕ−1}`. -/
theorem nk_u_mm {ϕ m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun x : ℝ => x ^ (-ϕ)) (-ϕ * m ^ (-ϕ - 1)) m :=
  Real.hasDerivAt_rpow_const (Or.inl hm.ne')

/-- Miao, p. 617: the sign conditions `u₁ > 0`, `u₂ < 0`, `u₃ > 0`, `u₁₁ < 0`, `u₂₂ < 0`,
`u₃₃ < 0` hold for (19.1) with `γ, ν, ϕ, χ > 0` at `C, N, m > 0`. -/
theorem nk_u_signs {γ ν ϕ χ C N m : ℝ} (hγ : 0 < γ) (hν : 0 < ν) (hϕ : 0 < ϕ) (hχ : 0 < χ)
    (hC : 0 < C) (hN : 0 < N) (hm : 0 < m) :
    0 < C ^ (-γ) ∧ -(χ * N ^ ν) < 0 ∧ 0 < m ^ (-ϕ) ∧ -γ * C ^ (-γ - 1) < 0 ∧
      -(χ * (ν * N ^ (ν - 1))) < 0 ∧ -ϕ * m ^ (-ϕ - 1) < 0 := by
  have h1 := Real.rpow_pos_of_pos hC (-γ)
  have h2 := Real.rpow_pos_of_pos hN ν
  have h3 := Real.rpow_pos_of_pos hm (-ϕ)
  have h4 := Real.rpow_pos_of_pos hC (-γ - 1)
  have h5 := Real.rpow_pos_of_pos hN (ν - 1)
  have h6 := Real.rpow_pos_of_pos hm (-ϕ - 1)
  refine ⟨h1, ?_, h3, ?_, ?_, ?_⟩
  · have := mul_pos hχ h2
    linarith
  · have := mul_pos hγ h4
    linarith
  · have := mul_pos hχ (mul_pos hν h5)
    linarith
  · have := mul_pos hϕ h6
    linarith

/-- Miao, p. 617: the satiation assumption "there is a finite `m* > 0` with `u₃(·, ·, m) ≤ 0`
for all `m > m*`" fails for the specification (19.1): `u₃ = m^{−ϕ} > 0` for every `m > 0`. -/
theorem nk_u_no_satiation (ϕ : ℝ) : ¬ ∃ mstar : ℝ, 0 < mstar ∧ ∀ m, mstar < m → m ^ (-ϕ) ≤ 0 := by
  rintro ⟨mstar, hms, h⟩
  have := h (mstar + 1) (by linarith)
  have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < mstar + 1) (-ϕ)
  linarith

/-- **(19.2)** (Miao, p. 618): the first-order conditions `C_t^{−γ} = Λ_t` and
`χN_t^ν = Λ_tW_t/P_t` give `χN_t^ν/C_t^{−γ} = W_t/P_t`. -/
theorem eq_19_2 {γ χ C N W P Λ ν : ℝ} (hC : 0 < C) (hΛ : C ^ (-γ) = Λ)
    (hN : χ * N ^ ν = Λ * (W / P)) : χ * N ^ ν / C ^ (-γ) = W / P := by
  have h := Real.rpow_pos_of_pos hC (-γ)
  rw [hN, ← hΛ]
  field_simp

/-- **(19.3)** (Miao, p. 618), the consumption Euler equation. With `Λ_s = C_s^{−γ}` and the
bond first-order condition `Λ_t/(P_t(1 + i_t)) = E_t[βΛ_{t+1}/P_{t+1}]` (`E_t = μ[·|ℱ_t]`),
`1 = β(1 + i_t)E_t[(C_{t+1}/C_t)^{−γ}P_t/P_{t+1}]` almost surely. The `F_t`-measurability of
`C_t^γP_t` and the integrability of the two integrands are used to pull `C_t^γP_t` out of
`E_t`. -/
theorem eq_19_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {ℱ : MeasurableSpace Ω}
    {β γ : ℝ} {C P i Λ : ℕ → Ω → ℝ} (t : ℕ) (hC : ∀ s ω, 0 < C s ω) (hP : ∀ s ω, 0 < P s ω)
    (hi : ∀ ω, 0 < 1 + i t ω) (hΛ : ∀ s ω, Λ s ω = C s ω ^ (-γ))
    (hB : (fun ω => Λ t ω / (P t ω * (1 + i t ω))) =ᵐ[μ]
      μ[fun ω => β * Λ (t + 1) ω / P (t + 1) ω | ℱ])
    (hmeas : StronglyMeasurable[ℱ] (fun ω => C t ω ^ γ * P t ω))
    (hint1 : Integrable (fun ω => C (t + 1) ω ^ (-γ) / P (t + 1) ω) μ)
    (hint2 : Integrable (fun ω => (C (t + 1) ω / C t ω) ^ (-γ) * (P t ω / P (t + 1) ω)) μ) :
    (fun _ => (1 : ℝ)) =ᵐ[μ] fun ω => β * (1 + i t ω) *
      μ[fun ω => (C (t + 1) ω / C t ω) ^ (-γ) * (P t ω / P (t + 1) ω) | ℱ] ω := by
  set k : Ω → ℝ := fun ω => C t ω ^ γ * P t ω
  set g : Ω → ℝ := fun ω => C (t + 1) ω ^ (-γ) / P (t + 1) ω
  have hkg : (fun ω => (C (t + 1) ω / C t ω) ^ (-γ) * (P t ω / P (t + 1) ω)) = k * g := by
    funext ω
    have h0 := hC t ω
    have h1 := hC (t + 1) ω
    have h2 := hP t ω
    have h3 := hP (t + 1) ω
    simp only [k, g, Pi.mul_apply]
    rw [Real.div_rpow h1.le h0.le, Real.rpow_neg h0.le γ]
    have := Real.rpow_pos_of_pos h0 γ
    field_simp
  have hβg : (fun ω => β * Λ (t + 1) ω / P (t + 1) ω) = β • g := by
    funext ω
    simp only [g, hΛ, Pi.smul_apply, smul_eq_mul]
    ring
  have hpull : μ[k * g | ℱ] =ᵐ[μ] k * μ[g | ℱ] :=
    condExp_mul_of_stronglyMeasurable_left hmeas (by rw [← hkg]; exact hint2) hint1
  have hsm : μ[β • g | ℱ] =ᵐ[μ] β • μ[g | ℱ] := condExp_smul β g ℱ
  rw [hβg] at hB
  rw [hkg]
  filter_upwards [hpull, hsm, hB] with ω h1 h2 h3
  rw [h1]
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h2 h3 ⊢
  have e : β * μ[g | ℱ] ω = Λ t ω / (P t ω * (1 + i t ω)) := by rw [h3, h2]
  have hc := hC t ω
  have hp := hP t ω
  have hii := hi ω
  have ec : C t ω ^ γ * C t ω ^ (-γ) = 1 := by
    rw [← Real.rpow_add hc]
    simp
  calc (1 : ℝ) = (1 + i t ω) * (C t ω ^ γ * P t ω) * (Λ t ω / (P t ω * (1 + i t ω))) := by
        rw [hΛ]
        field_simp
        linear_combination -ec
    _ = β * (1 + i t ω) * (k ω * μ[g | ℱ] ω) := by
        rw [← e]
        simp only [k]
        ring

/-- **(19.4)** (Miao, p. 618), the money demand equation. From the money first-order condition
`(M_{t+1}/P_t)^{−ϕ}/P_t − Λ_t/P_t + E_t[βΛ_{t+1}/P_{t+1}] = 0`, the bond first-order condition
and `Λ_t = C_t^{−γ}`: `(M_{t+1}/P_t)^{−ϕ}/C_t^{−γ} = i_t/(1 + i_t)` almost surely. -/
theorem eq_19_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {ℱ : MeasurableSpace Ω}
    {β γ ϕ : ℝ} {C P i Λ M : ℕ → Ω → ℝ} (t : ℕ) (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω)
    (hi : ∀ ω, 0 < 1 + i t ω) (hΛ : ∀ ω, Λ t ω = C t ω ^ (-γ))
    (hB : (fun ω => Λ t ω / (P t ω * (1 + i t ω))) =ᵐ[μ]
      μ[fun ω => β * Λ (t + 1) ω / P (t + 1) ω | ℱ])
    (hM : (fun ω => (M (t + 1) ω / P t ω) ^ (-ϕ) / P t ω - Λ t ω / P t ω +
      μ[fun ω => β * Λ (t + 1) ω / P (t + 1) ω | ℱ] ω) =ᵐ[μ] fun _ => 0) :
    (fun ω => (M (t + 1) ω / P t ω) ^ (-ϕ) / C t ω ^ (-γ)) =ᵐ[μ]
      fun ω => i t ω / (1 + i t ω) := by
  filter_upwards [hB, hM] with ω h1 h2
  rw [← h1] at h2
  have hc := Real.rpow_pos_of_pos (hC ω) (-γ)
  have hp := hP ω
  have hii := hi ω
  rw [hΛ] at h2
  rw [div_eq_div_iff hc.ne' hii.ne']
  have e2 : (M (t + 1) ω / P t ω) ^ (-ϕ) - C t ω ^ (-γ) + C t ω ^ (-γ) / (1 + i t ω) = 0 := by
    have := congrArg (· * P t ω) h2
    simp only [zero_mul] at this
    rw [← this]
    field_simp
  field_simp at e2
  linear_combination e2

/-- Miao, p. 622: (19.4) determines the money supply. For `C_t, P_t, M_{t+1} > 0`, `ϕ > 0` and
`i_t > 0`, (19.4) holds iff `M_{t+1} = P_t(C_t^{−γ}i_t/(1 + i_t))^{−1/ϕ}`. -/
theorem nk_money_supply {γ ϕ C P M i : ℝ} (hϕ : 0 < ϕ) (hC : 0 < C) (hP : 0 < P) (hM : 0 < M)
    (hi : 0 < i) :
    (M / P) ^ (-ϕ) / C ^ (-γ) = i / (1 + i) ↔
      M = P * (C ^ (-γ) * (i / (1 + i))) ^ (-1 / ϕ) := by
  have hc := Real.rpow_pos_of_pos hC (-γ)
  have hq : 0 < C ^ (-γ) * (i / (1 + i)) := by positivity
  have hmp : 0 < M / P := div_pos hM hP
  rw [div_eq_iff hc.ne']
  constructor
  · intro h
    have h' : (M / P) ^ (-ϕ) = C ^ (-γ) * (i / (1 + i)) := by rw [h]; ring
    have e : M / P = (C ^ (-γ) * (i / (1 + i))) ^ (-1 / ϕ) := by
      rw [← h', ← Real.rpow_mul hmp.le]
      rw [show -ϕ * (-1 / ϕ) = 1 by field_simp, Real.rpow_one]
    rw [← e]
    field_simp
  · intro h
    have e : M / P = (C ^ (-γ) * (i / (1 + i))) ^ (-1 / ϕ) := by
      rw [h]
      field_simp
    rw [e, ← Real.rpow_mul hq.le, show -1 / ϕ * -ϕ = 1 by field_simp, Real.rpow_one]
    ring

/-- Miao, pp. 618, 622: a monetary equilibrium needs a positive nominal interest rate. If
`1 + i_t > 0` and `i_t ≤ 0`, (19.4) has no solution `M_{t+1}/P_t > 0`. -/
theorem nk_money_demand_pos_rate {γ ϕ C mreal i : ℝ} (hC : 0 < C) (hm : 0 < mreal)
    (hi1 : 0 < 1 + i) (hi : i ≤ 0) : mreal ^ (-ϕ) / C ^ (-γ) ≠ i / (1 + i) := by
  have h1 : 0 < mreal ^ (-ϕ) / C ^ (-γ) :=
    div_pos (Real.rpow_pos_of_pos hm _) (Real.rpow_pos_of_pos hC _)
  have h2 : i / (1 + i) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hi hi1.le
  intro h
  linarith

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic DNK model: final goods firms (Miao §19.1.2)

Miao, §19.1.2, pp. 618–619. The intermediate goods are indexed by `j` in a probability space
`(J, μ)` (the book's `[0, 1]` with Lebesgue measure is the leading case); `ε > 1`.

* (19.5): the Dixit–Stiglitz aggregator `Y = (∫ y_j^{(ε−1)/ε} dj)^{ε/(ε−1)}` (`nk_aggY`), and
  (19.7): the price index `P = (∫ p_j^{1−ε} dj)^{1/(1−ε)}` (`nk_priceIndex`).
* (19.6), the first-order condition: `P Y^{1/ε} y_j^{−1/ε} = p_j` iff `y_j = (p_j/P)^{−ε}Y`
  (`eq_19_6_foc`).
* (19.6) solves the final goods firm's problem: with `P` the index (19.7), every input profile
  `y ≥ 0` costs at least `P · Y(y)`, so the profit `P·Y(y) − ∫p_jy_j dj` is at most `0`
  (`eq_19_6`), and the demand curve (19.6) attains `0`: it delivers exactly `Y`
  (`nk_demand_agg`) at cost `PY` (`nk_demand_cost`). The proof is the tangent-line
  (weighted AM–GM) inequality `y^ρ ≤ ρyd^{ρ−1} + (1 − ρ)d^ρ`, integrated.
* (19.7) from the zero profit condition: along the demand curve, `∫p_jy_j dj = PY` iff `P` is
  the index (19.7) (`eq_19_7`).
-/

open MeasureTheory

namespace Miao.NewKeynesian

/-- **(19.5)** (Miao, p. 618): the Dixit–Stiglitz aggregate `(∫ y_j^{(ε−1)/ε} dj)^{ε/(ε−1)}`. -/
noncomputable def nk_aggY {J : Type*} [MeasurableSpace J] (μ : Measure J) (ε : ℝ) (y : J → ℝ) :
    ℝ :=
  (∫ j, y j ^ ((ε - 1) / ε) ∂μ) ^ (ε / (ε - 1))

/-- **(19.7)** (Miao, p. 619): the price index `(∫ p_j^{1−ε} dj)^{1/(1−ε)}`. -/
noncomputable def nk_priceIndex {J : Type*} [MeasurableSpace J] (μ : Measure J) (ε : ℝ)
    (p : J → ℝ) : ℝ :=
  (∫ j, p j ^ (1 - ε) ∂μ) ^ (1 / (1 - ε))

/-- **(19.6)**, the first-order condition (Miao, p. 619): for `y_j, p_j, Y, P > 0` and `ε > 0`,
`P Y^{1/ε} y_j^{−1/ε} = p_j` iff `y_j = (p_j/P)^{−ε}Y`. -/
theorem eq_19_6_foc {ε P Y yj pj : ℝ} (hε : 0 < ε) (hP : 0 < P) (hY : 0 < Y) (hy : 0 < yj)
    (hpj : 0 < pj) :
    P * Y ^ (1 / ε) * yj ^ (-1 / ε) = pj ↔ yj = (pj / P) ^ (-ε) * Y := by
  have hYe := Real.rpow_pos_of_pos hY (1 / ε)
  have hye := Real.rpow_pos_of_pos hy (-1 / ε)
  constructor
  · intro h
    have e : pj / P = Y ^ (1 / ε) * yj ^ (-1 / ε) := by
      rw [← h]
      field_simp
    rw [e, Real.mul_rpow hYe.le hye.le, ← Real.rpow_mul hY.le, ← Real.rpow_mul hy.le,
      show 1 / ε * -ε = -1 by field_simp, show -1 / ε * -ε = 1 by field_simp, Real.rpow_one,
      Real.rpow_neg_one]
    field_simp
  · intro h
    have hq : 0 < pj / P := div_pos hpj hP
    have e : yj / Y = (pj / P) ^ (-ε) := by
      rw [h]
      field_simp
    have e2 : yj ^ (-1 / ε) = (pj / P) * Y ^ (-1 / ε) := by
      have : yj = (pj / P) ^ (-ε) * Y := h
      rw [this, Real.mul_rpow (Real.rpow_nonneg hq.le _) hY.le, ← Real.rpow_mul hq.le,
        show -ε * (-1 / ε) = 1 by field_simp, Real.rpow_one]
    rw [e2, mul_comm (pj / P), ← mul_assoc, mul_assoc P, ← Real.rpow_add hY,
      show 1 / ε + -1 / ε = 0 by ring, Real.rpow_zero]
    field_simp

/-- The integral of `p_j^{1−ε}` is positive when every `p_j > 0` (`μ` a probability measure). -/
theorem nk_integral_rpow_pos {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε : ℝ} {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) : 0 < ∫ j, p j ^ (1 - ε) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun j => (Real.rpow_pos_of_pos (hp j) _).le) hI]
  have : Function.support (fun j => p j ^ (1 - ε)) = Set.univ :=
    Set.eq_univ_of_forall fun j => (Real.rpow_pos_of_pos (hp j) _).ne'
  rw [this, measure_univ]
  exact one_pos

/-- (19.7): `P^{1−ε} = ∫ p_j^{1−ε} dj` for the price index, `ε ≠ 1`. -/
theorem nk_priceIndex_rpow {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε : ℝ}
    (hε : ε ≠ 1) {p : J → ℝ} (hI : 0 ≤ ∫ j, p j ^ (1 - ε) ∂μ) :
    nk_priceIndex μ ε p ^ (1 - ε) = ∫ j, p j ^ (1 - ε) ∂μ := by
  have h1 : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  rw [nk_priceIndex, ← Real.rpow_mul hI, show 1 / (1 - ε) * (1 - ε) = 1 by field_simp,
    Real.rpow_one]

/-- The price index is positive. -/
theorem nk_priceIndex_pos {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε : ℝ} {p : J → ℝ}
    (hI : 0 < ∫ j, p j ^ (1 - ε) ∂μ) : 0 < nk_priceIndex μ ε p :=
  Real.rpow_pos_of_pos hI _

/-- Along the demand curve, `((p_j/P)^{−ε}Y)^{(ε−1)/ε} = (p_j/P)^{1−ε}Y^{(ε−1)/ε}`. -/
theorem nk_demand_rpow {ε P Y pj : ℝ} (hε : 0 < ε) (hq : 0 < pj / P) (hY : 0 < Y) :
    ((pj / P) ^ (-ε) * Y) ^ ((ε - 1) / ε) = (pj / P) ^ (1 - ε) * Y ^ ((ε - 1) / ε) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hq.le _) hY.le, ← Real.rpow_mul hq.le,
    show -ε * ((ε - 1) / ε) = 1 - ε by field_simp; ring]

/-- (19.5)–(19.7) (Miao, pp. 618–619): the demand curve `y_j = (p_j/P)^{−ε}Y`, with `P` the
index (19.7), aggregates to `Y`. -/
theorem nk_demand_agg {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε Y : ℝ} (hε : 1 < ε) (hY : 0 < Y) {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) :
    nk_aggY μ ε (fun j => (p j / nk_priceIndex μ ε p) ^ (-ε) * Y) = Y := by
  have hIp := nk_integral_rpow_pos hp hI
  have hP := nk_priceIndex_pos hIp
  have hPe := nk_priceIndex_rpow (by linarith : ε ≠ 1) hIp.le
  set P := nk_priceIndex μ ε p
  have hPr : 0 < P ^ (1 - ε) := Real.rpow_pos_of_pos hP _
  have hpt : ∀ j, ((p j / P) ^ (-ε) * Y) ^ ((ε - 1) / ε) =
      p j ^ (1 - ε) * (Y ^ ((ε - 1) / ε) / P ^ (1 - ε)) := fun j => by
    rw [nk_demand_rpow (by linarith) (div_pos (hp j) hP) hY, Real.div_rpow (hp j).le hP.le]
    ring
  have hint : ∫ j, ((p j / P) ^ (-ε) * Y) ^ ((ε - 1) / ε) ∂μ = Y ^ ((ε - 1) / ε) := by
    simp only [hpt]
    rw [integral_mul_const, ← hPe]
    field_simp
  rw [nk_aggY, hint, ← Real.rpow_mul hY.le, show (ε - 1) / ε * (ε / (ε - 1)) = 1 by
    have : ε - 1 ≠ 0 := by linarith
    field_simp, Real.rpow_one]

/-- (19.6)–(19.7) (Miao, p. 619): the demand curve costs `∫p_jy_j dj = PY`. -/
theorem nk_demand_cost {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε Y : ℝ} (hε : 1 < ε) {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) :
    ∫ j, p j * ((p j / nk_priceIndex μ ε p) ^ (-ε) * Y) ∂μ = nk_priceIndex μ ε p * Y := by
  have hIp := nk_integral_rpow_pos hp hI
  have hP := nk_priceIndex_pos hIp
  have hPe := nk_priceIndex_rpow (by linarith : ε ≠ 1) hIp.le
  set P := nk_priceIndex μ ε p
  have hpt : ∀ j, p j * ((p j / P) ^ (-ε) * Y) = p j ^ (1 - ε) * (P ^ ε * Y) := fun j => by
    have hpj := hp j
    rw [Real.div_rpow hpj.le hP.le, Real.rpow_neg hpj.le, Real.rpow_neg hP.le,
      Real.rpow_sub hpj, Real.rpow_one]
    field_simp
  simp only [hpt]
  rw [integral_mul_const, ← hPe, ← mul_assoc, ← Real.rpow_add hP,
    show 1 - ε + ε = 1 by ring, Real.rpow_one]

/-- **(19.7)** (Miao, p. 619), from zero profit: along the demand curve
`y_j = (p_j/P)^{−ε}Y` (`Y > 0`, `P > 0`), `∫p_jy_j dj = PY` iff `P = (∫p_j^{1−ε}dj)^{1/(1−ε)}`. -/
theorem eq_19_7 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε Y P : ℝ} (hε : 1 < ε) (hY : 0 < Y) (hP : 0 < P) {p : J → ℝ} (hp : ∀ j, 0 < p j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ) :
    ∫ j, p j * ((p j / P) ^ (-ε) * Y) ∂μ = P * Y ↔ P = nk_priceIndex μ ε p := by
  have hIp := nk_integral_rpow_pos hp hI
  set I := ∫ j, p j ^ (1 - ε) ∂μ
  have hpt : ∀ j, p j * ((p j / P) ^ (-ε) * Y) = p j ^ (1 - ε) * (P ^ ε * Y) := fun j => by
    have hpj := hp j
    rw [Real.div_rpow hpj.le hP.le, Real.rpow_neg hpj.le, Real.rpow_neg hP.le,
      Real.rpow_sub hpj, Real.rpow_one]
    field_simp
  simp only [hpt]
  rw [integral_mul_const]
  have hPe : 0 < P ^ ε := Real.rpow_pos_of_pos hP _
  have h1 : (1 : ℝ) - ε ≠ 0 := by linarith
  have key : I * (P ^ ε * Y) = P * Y ↔ P ^ (1 - ε) = I := by
    rw [Real.rpow_sub hP, Real.rpow_one]
    constructor
    · intro h
      field_simp
      nlinarith [h]
    · intro h
      rw [← h]
      field_simp
  rw [key]
  constructor
  · intro h
    change P = I ^ (1 / (1 - ε))
    rw [← h, ← Real.rpow_mul hP.le, show (1 - ε) * (1 / (1 - ε)) = 1 by
      field_simp, Real.rpow_one]
  · intro h
    rw [h]
    exact nk_priceIndex_rpow (by linarith) hIp.le

/-- The tangent-line inequality for `x ↦ x^ρ`, `0 < ρ < 1`: `y^ρ ≤ ρyd^{ρ−1} + (1 − ρ)d^ρ` for
`y ≥ 0`, `d > 0`. -/
theorem nk_rpow_tangent {ρ y d : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (hy : 0 ≤ y) (hd : 0 < d) :
    y ^ ρ ≤ ρ * y * d ^ (ρ - 1) + (1 - ρ) * d ^ ρ := by
  have h := Real.geom_mean_le_arith_mean2_weighted h0.le (by linarith : 0 ≤ 1 - ρ) hy hd.le
    (by ring)
  have hdm : 0 < d ^ (ρ - 1) := Real.rpow_pos_of_pos hd _
  have e1 : d ^ (1 - ρ) * d ^ (ρ - 1) = 1 := by
    rw [← Real.rpow_add hd]
    simp
  have e2 : d * d ^ (ρ - 1) = d ^ ρ := by
    rw [mul_comm, ← Real.rpow_add_one hd.ne']
    ring_nf
  have := mul_le_mul_of_nonneg_right h hdm.le
  calc y ^ ρ = y ^ ρ * (d ^ (1 - ρ) * d ^ (ρ - 1)) := by rw [e1, mul_one]
    _ = y ^ ρ * d ^ (1 - ρ) * d ^ (ρ - 1) := by ring
    _ ≤ (ρ * y + (1 - ρ) * d) * d ^ (ρ - 1) := this
    _ = ρ * y * d ^ (ρ - 1) + (1 - ρ) * (d * d ^ (ρ - 1)) := by ring
    _ = ρ * y * d ^ (ρ - 1) + (1 - ρ) * d ^ ρ := by rw [e2]

/-- **(19.6)** (Miao, p. 619): the demand curve solves the final goods firm's problem. With `P`
the index (19.7), every input profile `y ≥ 0` (with `y^{(ε−1)/ε}` and `py` integrable) costs at
least `P·Y(y)`: the profit `P·Y(y) − ∫p_jy_j dj` is at most `0`, the profit of the demand curve
(`nk_demand_agg`, `nk_demand_cost`). -/
theorem eq_19_6 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {ε : ℝ} (hε : 1 < ε) {p y : J → ℝ} (hp : ∀ j, 0 < p j) (hy : ∀ j, 0 ≤ y j)
    (hI : Integrable (fun j => p j ^ (1 - ε)) μ)
    (hyI : Integrable (fun j => y j ^ ((ε - 1) / ε)) μ)
    (hpy : Integrable (fun j => p j * y j) μ) :
    nk_priceIndex μ ε p * nk_aggY μ ε y - ∫ j, p j * y j ∂μ ≤ 0 := by
  have hε0 : 0 < ε := by linarith
  have hIp := nk_integral_rpow_pos hp hI
  have hP := nk_priceIndex_pos hIp
  have hPe := nk_priceIndex_rpow (by linarith : ε ≠ 1) hIp.le
  set P := nk_priceIndex μ ε p
  set ρ := (ε - 1) / ε with hρ
  have hρ0 : 0 < ρ := div_pos (by linarith) hε0
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one hε0]; linarith
  have hS : 0 ≤ ∫ j, y j ^ ρ ∂μ := integral_nonneg fun j => Real.rpow_nonneg (hy j) _
  have hpyn : 0 ≤ ∫ j, p j * y j ∂μ := integral_nonneg fun j => mul_nonneg (hp j).le (hy j)
  set Y := nk_aggY μ ε y with hYdef
  rcases hS.lt_or_eq with hSp | hS0
  swap
  · have : Y = 0 := by
      rw [hYdef, nk_aggY, ← hS0, Real.zero_rpow (by
        have : ε - 1 ≠ 0 := by linarith
        positivity)]
    rw [this, mul_zero]
    linarith
  have hY : 0 < Y := Real.rpow_pos_of_pos hSp _
  have hYρ : Y ^ ρ = ∫ j, y j ^ ρ ∂μ := by
    rw [hYdef, nk_aggY, ← Real.rpow_mul hS, show ε / (ε - 1) * ρ = 1 by
      rw [hρ]
      have : ε - 1 ≠ 0 := by linarith
      field_simp, Real.rpow_one]
  set d : J → ℝ := fun j => (p j / P) ^ (-ε) * Y
  have hd : ∀ j, 0 < d j := fun j => mul_pos (Real.rpow_pos_of_pos (div_pos (hp j) hP) _) hY
  have hdρ1 : ∀ j, d j ^ (ρ - 1) = p j * (Y ^ (ρ - 1) / P) := fun j => by
    have hq := div_pos (hp j) hP
    simp only [d]
    rw [Real.mul_rpow (Real.rpow_nonneg hq.le _) hY.le, ← Real.rpow_mul hq.le,
      show -ε * (ρ - 1) = 1 by rw [hρ]; field_simp; ring, Real.rpow_one]
    ring
  have hdρ : ∀ j, d j ^ ρ = p j ^ (1 - ε) * (Y ^ ρ / P ^ (1 - ε)) := fun j => by
    simp only [d]
    rw [nk_demand_rpow hε0 (div_pos (hp j) hP) hY, Real.div_rpow (hp j).le hP.le]
    ring
  have hpt : ∀ j, y j ^ ρ ≤ (p j * y j) * (ρ * (Y ^ (ρ - 1) / P)) +
      p j ^ (1 - ε) * ((1 - ρ) * (Y ^ ρ / P ^ (1 - ε))) := fun j => by
    have := nk_rpow_tangent hρ0 hρ1 (hy j) (hd j)
    rw [hdρ1, hdρ] at this
    linarith [this]
  set c1 := ρ * (Y ^ (ρ - 1) / P)
  set c2 := (1 - ρ) * (Y ^ ρ / P ^ (1 - ε))
  have hmono : ∫ j, y j ^ ρ ∂μ ≤ ∫ j, ((p j * y j) * c1 + p j ^ (1 - ε) * c2) ∂μ :=
    integral_mono hyI ((hpy.mul_const c1).add (hI.mul_const c2)) hpt
  rw [integral_add (hpy.mul_const c1) (hI.mul_const c2), integral_mul_const, integral_mul_const,
    ← hYρ, ← hPe] at hmono
  have hPr : 0 < P ^ (1 - ε) := Real.rpow_pos_of_pos hP _
  have e : P ^ (1 - ε) * ((1 - ρ) * (Y ^ ρ / P ^ (1 - ε))) = (1 - ρ) * Y ^ ρ := by
    field_simp
  rw [e] at hmono
  have hYr : Y ^ ρ = Y * Y ^ (ρ - 1) := by
    rw [← Real.rpow_one_add' hY.le (by linarith)]
    ring_nf
  have hYm : 0 < Y ^ (ρ - 1) := Real.rpow_pos_of_pos hY _
  have key : ρ * (Y * Y ^ (ρ - 1)) ≤ (∫ j, p j * y j ∂μ) * (ρ * (Y ^ (ρ - 1) / P)) := by
    rw [← hYr]
    linarith
  have key2 : P * Y ≤ ∫ j, p j * y j ∂μ := by
    have hc : 0 < ρ * Y ^ (ρ - 1) / P := by positivity
    have : (P * Y) * (ρ * Y ^ (ρ - 1) / P) ≤ (∫ j, p j * y j ∂μ) * (ρ * Y ^ (ρ - 1) / P) := by
      calc (P * Y) * (ρ * Y ^ (ρ - 1) / P) = ρ * (Y * Y ^ (ρ - 1)) := by field_simp
        _ ≤ (∫ j, p j * y j ∂μ) * (ρ * (Y ^ (ρ - 1) / P)) := key
        _ = (∫ j, p j * y j ∂μ) * (ρ * Y ^ (ρ - 1) / P) := by ring
    exact le_of_mul_le_mul_right this hc
  linarith

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic DNK model: intermediate goods firms and Calvo pricing (Miao §19.1.3)

Miao, §19.1.3, pp. 619–621. Firm `j` produces `Y^j = A(N^j)^{1−α}`, `α ∈ [0, 1)` (19.8), and
faces the demand curve (19.6). Write `w = W/P` for the real wage.

* Cost minimisation: the labour requirement `N = (Y/A)^{1/(1−α)}` (`nk_labor_req`), the real
  total cost `TC(Y) = w(Y/A)^{1/(1−α)}` (`nk_TC`) and the real marginal cost
  `MC = TC'(Y) = w/(A(1 − α)N^{−α}) = w/(A(1 − α)(Y/A)^{−α/(1−α)})` (`nk_MC_deriv`), equal to the
  Lagrange multiplier of the constraint (19.8) (`nk_MC_lagrange`).
* (19.9), the average marginal cost (`nk_MCavg`), and (19.10):
  `MC^j = MC(Y/Y^j)^{−α/(1−α)} = MC(P^j/P)^{εα/(α−1)}` (`eq_19_10`); firms with higher prices
  have lower marginal costs when `α > 0` (`nk_MC_antitone`).
* Calvo pricing. The derivative of the period-`t + k` profit
  `P*Y_{t+k|t}/P_{t+k} − TC_{t+k}(Y_{t+k|t})`, `Y_{t+k|t} = (P*/P_{t+k})^{−ε}Y_{t+k}`, is
  `(1 − ε)P*^{−ε−1}(Y_{t+k}/P_{t+k}^{1−ε})(P* − μMC_{t+k|t}P_{t+k})`, `μ = ε/(ε − 1)`
  (`nk_calvo_term_deriv`); for an objective with finitely many (date, state) terms and weights
  `w_k` (the products `θ^kβ^kΛ_{t+k}/Λ_t` times probabilities), the first-order condition is the
  printed one (`nk_calvo_foc`).
* (19.11), the optimal reset price, solves the first-order condition, for a summable family of
  terms indexed by any type (dates and states) (`eq_19_11`); (19.12), the marginal cost of a
  firm that reset its price at `t` (`eq_19_12`).

**Departure.** The derivative of the infinite-horizon objective is not formalised: the
first-order condition is derived for objectives with finitely many terms (`nk_calvo_foc`), and
(19.11) is derived from the first-order condition for infinitely many terms (`eq_19_11`).
-/

namespace Miao.NewKeynesian

/-- Miao, p. 619: the labour needed for output `Y` under (19.8): `Y = AN^{1−α}` iff
`N = (Y/A)^{1/(1−α)}` (`A, N, Y > 0`, `α < 1`). -/
theorem nk_labor_req {A N Y α : ℝ} (hA : 0 < A) (hN : 0 < N) (hY0 : 0 < Y) (hα : α < 1) :
    Y = A * N ^ (1 - α) ↔ N = (Y / A) ^ (1 / (1 - α)) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  constructor
  · intro h
    rw [h, mul_div_cancel_left₀ _ hA.ne', ← Real.rpow_mul hN.le,
      show (1 - α) * (1 / (1 - α)) = 1 by field_simp, Real.rpow_one]
  · intro h
    have hY : 0 ≤ Y / A := (div_pos hY0 hA).le
    rw [h, ← Real.rpow_mul hY, show 1 / (1 - α) * (1 - α) = 1 by field_simp, Real.rpow_one]
    field_simp

/-- Miao, p. 619: the real total cost `TC(Y) = w(Y/A)^{1/(1−α)}` of output `Y` at real wage
`w = W/P`. -/
noncomputable def nk_TC (w A α Y : ℝ) : ℝ := w * (Y / A) ^ (1 / (1 - α))

/-- **(19.9)** (Miao, p. 620): the real marginal cost `MC = w/(A(1 − α)(Y/A)^{−α/(1−α)})`. -/
noncomputable def nk_MCavg (w A α Y : ℝ) : ℝ := w / (A * (1 - α) * (Y / A) ^ (-α / (1 - α)))

/-- Miao, p. 620: the real marginal cost is the derivative of the total cost:
`TC'(Y) = w/(A(1 − α)(Y/A)^{−α/(1−α)})` for `Y, A > 0`, `α < 1`. -/
theorem nk_MC_deriv {w A α Y : ℝ} (hA : 0 < A) (hY : 0 < Y) (hα : α < 1) :
    HasDerivAt (nk_TC w A α) (nk_MCavg w A α Y) Y := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have hq : 0 < Y / A := div_pos hY hA
  have hd := (((hasDerivAt_id Y).div_const A).rpow_const (p := 1 / (1 - α))
    (Or.inl hq.ne')).const_mul w
  refine hd.congr_deriv ?_
  simp only [id, nk_MCavg]
  have e : 1 / (1 - α) - 1 = -(-α / (1 - α)) := by field_simp; ring
  rw [e, Real.rpow_neg hq.le]
  have := Real.rpow_pos_of_pos hq (-α / (1 - α))
  field_simp

/-- Miao, p. 620: `MC` is the Lagrange multiplier of the cost-minimisation problem: the
first-order condition `w = λA(1 − α)N^{−α}` gives `λ = MC` at `N = (Y/A)^{1/(1−α)}`. -/
theorem nk_MC_lagrange {w A α Y lam : ℝ} (hA : 0 < A) (hY : 0 < Y) (hα : α < 1)
    (hfoc : w = lam * (A * (1 - α) * ((Y / A) ^ (1 / (1 - α))) ^ (-α))) :
    lam = nk_MCavg w A α Y ∧
      nk_MCavg w A α Y = w / (A * (1 - α) * ((Y / A) ^ (1 / (1 - α))) ^ (-α)) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have hq : 0 < Y / A := div_pos hY hA
  have e : ((Y / A) ^ (1 / (1 - α))) ^ (-α) = (Y / A) ^ (-α / (1 - α)) := by
    rw [← Real.rpow_mul hq.le]
    congr 1
    ring
  have hpos : 0 < A * (1 - α) * (Y / A) ^ (-α / (1 - α)) := by
    have := Real.rpow_pos_of_pos hq (-α / (1 - α))
    positivity
  rw [e] at hfoc ⊢
  refine ⟨?_, rfl⟩
  rw [nk_MCavg, hfoc]
  field_simp

/-- Miao, p. 620: with `MC^j` the marginal cost at output `Y^j` and `MC` the average (19.9),
`MC^j = MC(Y/Y^j)^{−α/(1−α)}`. -/
theorem nk_MC_ratio {w A α Y Yj : ℝ} (hA : 0 < A) (hY : 0 < Y) (hYj : 0 < Yj) :
    nk_MCavg w A α Yj = nk_MCavg w A α Y * (Y / Yj) ^ (-α / (1 - α)) := by
  have hq : 0 < Y / A := div_pos hY hA
  have hqj : 0 < Yj / A := div_pos hYj hA
  simp only [nk_MCavg]
  rw [show Y / Yj = (Y / A) / (Yj / A) by field_simp, Real.div_rpow hq.le hqj.le]
  have := Real.rpow_pos_of_pos hq (-α / (1 - α))
  have := Real.rpow_pos_of_pos hqj (-α / (1 - α))
  by_cases h : A * (1 - α) = 0
  · simp [h]
  · field_simp

/-- **(19.10)** (Miao, p. 620): `MC^j = MC(Y/Y^j)^{−α/(1−α)} = MC(P^j/P)^{εα/(α−1)}` for a firm on
the demand curve `Y^j = (P^j/P)^{−ε}Y`. -/
theorem eq_19_10 {w A α ε Y Pj P : ℝ} (hA : 0 < A) (hY : 0 < Y) (hPj : 0 < Pj) (hP : 0 < P)
    (hα : α < 1) :
    nk_MCavg w A α ((Pj / P) ^ (-ε) * Y) =
        nk_MCavg w A α Y * (Y / ((Pj / P) ^ (-ε) * Y)) ^ (-α / (1 - α)) ∧
      nk_MCavg w A α ((Pj / P) ^ (-ε) * Y) =
        nk_MCavg w A α Y * (Pj / P) ^ (ε * α / (α - 1)) := by
  have hq : 0 < Pj / P := div_pos hPj hP
  have hd : 0 < (Pj / P) ^ (-ε) * Y := mul_pos (Real.rpow_pos_of_pos hq _) hY
  have h1 := nk_MC_ratio (w := w) (α := α) hA hY hd
  refine ⟨h1, ?_⟩
  rw [h1]
  congr 1
  have e : Y / ((Pj / P) ^ (-ε) * Y) = (Pj / P) ^ ε := by
    rw [Real.rpow_neg hq.le]
    have := Real.rpow_pos_of_pos hq ε
    field_simp
  rw [e, ← Real.rpow_mul hq.le]
  congr 1
  have : (1 : ℝ) - α ≠ 0 := by linarith
  have : α - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Miao, p. 620: "firms with relatively high prices have relatively low real marginal costs":
for `0 < α < 1`, `ε > 0` and `MC > 0`, `P^j ↦ MC(P^j/P)^{εα/(α−1)}` is strictly decreasing. -/
theorem nk_MC_antitone {α ε P MC : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hP : 0 < P)
    (hMC : 0 < MC) {p1 p2 : ℝ} (hp1 : 0 < p1) (h12 : p1 < p2) :
    MC * (p2 / P) ^ (ε * α / (α - 1)) < MC * (p1 / P) ^ (ε * α / (α - 1)) := by
  have hexp : ε * α / (α - 1) < 0 := div_neg_of_pos_of_neg (mul_pos hε hα0) (by linarith)
  have := Real.rpow_lt_rpow_of_neg (div_pos hp1 hP) (div_lt_div_of_pos_right h12 hP) hexp
  exact mul_lt_mul_of_pos_left this hMC

/-- Miao, p. 621: the derivative of the period-`t + k` real profit of a firm that resets its
price to `x = P*` at `t`, `x·Y_{t+k|t}/P_{t+k} − TC(Y_{t+k|t})` with
`Y_{t+k|t} = (x/P_{t+k})^{−ε}Y_{t+k}` and `TC' = MC_{t+k|t}` at `Y_{t+k|t}`, is
`(1 − ε)x^{−ε−1}(Y_{t+k}/P_{t+k}^{1−ε})(x − μMC_{t+k|t}P_{t+k})`, `μ = ε/(ε − 1)`. -/
theorem nk_calvo_term_deriv {ε Pk Yk x MC : ℝ} {TC : ℝ → ℝ} (hε : 1 < ε) (hPk : 0 < Pk)
    (hx : 0 < x) (hTC : HasDerivAt TC MC ((x / Pk) ^ (-ε) * Yk)) :
    HasDerivAt (fun z => z * ((z / Pk) ^ (-ε) * Yk) / Pk - TC ((z / Pk) ^ (-ε) * Yk))
      ((1 - ε) * x ^ (-ε - 1) * (Yk / Pk ^ (1 - ε) * (x - ε / (ε - 1) * MC * Pk))) x := by
  have hq : 0 < x / Pk := div_pos hx hPk
  have hin : HasDerivAt (fun z => (z / Pk) ^ (-ε) * Yk)
      ((1 / Pk * (-ε * (x / Pk) ^ (-ε - 1))) * Yk) x := by
    have := ((hasDerivAt_id x).div_const Pk).rpow_const (p := -ε) (Or.inl hq.ne')
    exact (this.mul_const Yk).congr_deriv (by simp only [id]; ring)
  have hrev : HasDerivAt (fun z => z ^ (1 - ε) * (Pk ^ (ε - 1) * Yk))
      ((1 - ε) * x ^ (1 - ε - 1) * (Pk ^ (ε - 1) * Yk)) x :=
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).mul_const _
  have hev : (fun z => z * ((z / Pk) ^ (-ε) * Yk) / Pk) =ᶠ[nhds x]
      fun z => z ^ (1 - ε) * (Pk ^ (ε - 1) * Yk) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    have hz' : (0 : ℝ) < z := hz
    rw [Real.div_rpow hz'.le hPk.le, Real.rpow_neg hz'.le, Real.rpow_neg hPk.le,
      Real.rpow_sub hz', Real.rpow_sub hPk, Real.rpow_one, Real.rpow_one]
    have := Real.rpow_pos_of_pos hz' ε
    have := Real.rpow_pos_of_pos hPk ε
    field_simp
  have h := (hrev.congr_of_eventuallyEq hev).sub (hTC.comp x hin)
  refine h.congr_deriv ?_
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [show (1 : ℝ) - ε - 1 = -ε by ring, Real.div_rpow hx.le hPk.le,
    show -ε - 1 = -ε + -1 by ring, Real.rpow_add hx, Real.rpow_add hPk, Real.rpow_neg_one,
    Real.rpow_neg_one, Real.rpow_sub hPk, Real.rpow_sub hPk, Real.rpow_one, Real.rpow_neg hx.le,
    Real.rpow_neg hPk.le]
  have := Real.rpow_pos_of_pos hx ε
  have := Real.rpow_pos_of_pos hPk ε
  field_simp
  ring

/-- Miao, p. 621: the first-order condition of the reset-price problem with finitely many
(date, state) terms `k ∈ K` and weights `w_k` (`θ^kβ^kΛ_{t+k}/Λ_t` times probabilities). The
objective `∑_k w_k(xY_{k|t}/P_k − TC_k(Y_{k|t}))` has derivative
`(1 − ε)x^{−ε−1}∑_k w_k(Y_k/P_k^{1−ε})(x − μMC_{k|t}P_k)`, and it vanishes iff the printed
condition `∑_k w_k(Y_k/P_k^{1−ε})(x − μMC_{k|t}P_k) = 0` holds. -/
theorem nk_calvo_foc {K : Type*} (S : Finset K) {ε x : ℝ} {wt Pk Yk MC : K → ℝ}
    {TC : K → ℝ → ℝ} (hε : 1 < ε) (hPk : ∀ k, 0 < Pk k) (hx : 0 < x)
    (hTC : ∀ k, HasDerivAt (TC k) (MC k) ((x / Pk k) ^ (-ε) * Yk k)) :
    HasDerivAt (fun z => ∑ k ∈ S, wt k *
        (z * ((z / Pk k) ^ (-ε) * Yk k) / Pk k - TC k ((z / Pk k) ^ (-ε) * Yk k)))
      ((1 - ε) * x ^ (-ε - 1) *
        ∑ k ∈ S, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k))) x ∧
    ((1 - ε) * x ^ (-ε - 1) *
        ∑ k ∈ S, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) = 0 ↔
      ∑ k ∈ S, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) = 0) := by
  refine ⟨?_, ?_⟩
  · have h := HasDerivAt.fun_sum (u := S) fun k _ =>
      (nk_calvo_term_deriv hε (hPk k) hx (hTC k)).const_mul (wt k)
    convert h using 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · have hne : (1 - ε) * x ^ (-ε - 1) ≠ 0 :=
      mul_ne_zero (by linarith) (Real.rpow_pos_of_pos hx _).ne'
    exact ⟨fun h => (mul_eq_zero.1 h).resolve_left hne, fun h => by rw [h, mul_zero]⟩

/-- **(19.11)** (Miao, p. 621): the optimal reset price. If the first-order condition
`∑_k w_k(Y_k/P_k^{1−ε})(P* − μMC_{k|t}P_k) = 0` holds for a summable family of (date, state)
terms (`w_k = θ^kβ^kΛ_{t+k}` times probabilities) and `∑_k w_kP_k^{ε−1}Y_k ≠ 0`, then
`P* = (ε/(ε − 1)) ∑_k w_kP_k^εY_kMC_{k|t} / ∑_k w_kP_k^{ε−1}Y_k`. -/
theorem eq_19_11 {K : Type*} {ε x : ℝ} {wt Pk Yk MC : K → ℝ} (hPk : ∀ k, 0 < Pk k)
    (hs1 : Summable fun k => wt k * Pk k ^ (ε - 1) * Yk k)
    (hs2 : Summable fun k => wt k * Pk k ^ ε * Yk k * MC k)
    (hfoc : ∑' k, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) = 0)
    (hden : ∑' k, wt k * Pk k ^ (ε - 1) * Yk k ≠ 0) :
    x = ε / (ε - 1) * (∑' k, wt k * Pk k ^ ε * Yk k * MC k) /
      ∑' k, wt k * Pk k ^ (ε - 1) * Yk k := by
  have hterm : ∀ k, wt k * (Yk k / Pk k ^ (1 - ε) * (x - ε / (ε - 1) * MC k * Pk k)) =
      x * (wt k * Pk k ^ (ε - 1) * Yk k) - ε / (ε - 1) * (wt k * Pk k ^ ε * Yk k * MC k) :=
    fun k => by
      have hp := hPk k
      rw [Real.rpow_sub hp, Real.rpow_sub hp, Real.rpow_one]
      have := Real.rpow_pos_of_pos hp ε
      field_simp
  simp only [hterm] at hfoc
  rw [Summable.tsum_sub (hs1.mul_left x) (hs2.mul_left _), tsum_mul_left, tsum_mul_left]
    at hfoc
  rw [eq_div_iff hden]
  linarith

/-- **(19.12)** (Miao, p. 621): the real marginal cost in `t + k` of a firm that reset its price
to `P*` in `t` is `MC_{t+k|t} = MC_{t+k}(P*/P_{t+k})^{εα/(α−1)}` (from (19.10), with
`Y_{t+k|t} = (P*/P_{t+k})^{−ε}Y_{t+k}`). -/
theorem eq_19_12 {w A α ε Yk Pstar Pk : ℝ} (hA : 0 < A) (hY : 0 < Yk) (hPs : 0 < Pstar)
    (hPk : 0 < Pk) (hα : α < 1) :
    nk_MCavg w A α ((Pstar / Pk) ^ (-ε) * Yk) =
      nk_MCavg w A α Yk * (Pstar / Pk) ^ (ε * α / (α - 1)) :=
  (eq_19_10 hA hY hPs hPk hα).2

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic DNK model: aggregation, the Taylor rule and the sticky price equilibrium
(Miao §§19.1.3–19.1.5)

Miao, pp. 621–623. Firms are indexed by a probability space `(J, μ)`; in period `t` the firms in
a measurable set `S` (the non-adjusters, `μ(S) = θ`) keep last period's price and the others
set `P*_t`.

* The law of large numbers used by the book is the hypothesis that the non-adjusters are a
  representative sample of last period's prices: `∫_S f(P^j_{t−1}) dj = θ∫ f(P^j_{t−1}) dj` for
  the relevant `f` (`nk_calvo_avg` is the averaging step). Under it:
  (19.13) `P_t^{1−ε} = θP_{t−1}^{1−ε} + (1 − θ)(P*_t)^{1−ε}` (`eq_19_13`), and
  (19.17) `Δ_t = θΠ_t^{ε/(1−α)}Δ_{t−1} + (1 − θ)(P*_t/P_t)^{−ε/(1−α)}` (`eq_19_17`).
* (19.14), the Taylor rule (`nk_taylorRule`).
* (19.15) `N_t = (Y_t/A_t)^{1/(1−α)}Δ_t` and (19.16) `Y_t = A_tN_t^{1−α}Δ_t^{α−1}`
  (`eq_19_15`, `eq_19_16`), with the price dispersion `Δ_t` (`nk_dispersion`).
* The zero-inflation deterministic steady state used in §19.1.7: with constant `P = P*`,
  `Π = 1`, `Δ = 1`, `1 + i = 1/β`, `MC = 1/μ` and `Y = Y^f`, the Euler equation (19.3), (19.11),
  (19.13), (19.14) and (19.17) hold (`nk_steady_state`, with the steady-state (19.11) computed
  in `nk_reset_constant`: constant inputs and weights `(θβ)^kΛ` give `P* = μMC·P`).
-/

open MeasureTheory

namespace Miao.NewKeynesian

/-- The Calvo averaging step (Miao, pp. 621–622): if `g = f` on the set `S` of non-adjusters,
`g = c` off it, `μ(S) = θ` and `∫_S f = θ∫ f` (the law of large numbers), then
`∫ g = θ∫ f + (1 − θ)c`. -/
theorem nk_calvo_avg {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ c : ℝ} (hθ : μ.real S = θ) {f g : J → ℝ}
    (hf : Integrable f μ) (hgS : ∀ j ∈ S, g j = f j) (hgc : ∀ j ∉ S, g j = c)
    (hLLN : ∫ j in S, f j ∂μ = θ * ∫ j, f j ∂μ) :
    ∫ j, g j ∂μ = θ * ∫ j, f j ∂μ + (1 - θ) * c := by
  have h1 : ∫ j in S, g j ∂μ = ∫ j in S, f j ∂μ := setIntegral_congr_fun hS fun j hj => hgS j hj
  have h2 : ∫ j in Sᶜ, g j ∂μ = ∫ _ in Sᶜ, c ∂μ :=
    setIntegral_congr_fun hS.compl fun j hj => hgc j hj
  have hgi : Integrable g μ := by
    have hon1 : IntegrableOn g S μ :=
      (hf.integrableOn).congr_fun (fun j hj => (hgS j hj).symm) hS
    have hon2 : IntegrableOn g Sᶜ μ :=
      (integrableOn_const (C := c)).congr_fun (fun j hj => (hgc j hj).symm) hS.compl
    rw [← integrableOn_univ, ← Set.union_compl_self S]
    exact hon1.union hon2
  rw [← integral_add_compl hS hgi, h1, h2, setIntegral_const, probReal_compl_eq_one_sub hS, hθ,
    hLLN, smul_eq_mul]

/-- **(19.13)** (Miao, p. 621): Calvo price-index dynamics. Prices at `t` are `p₁ = p₀` on the
non-adjusters `S` (`μ(S) = θ`) and `P* > 0` elsewhere; under the law of large numbers
`∫_S p₀^{1−ε} = θ∫ p₀^{1−ε}`, `P_t^{1−ε} = θP_{t−1}^{1−ε} + (1 − θ)(P*)^{1−ε}`. -/
theorem eq_19_13 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε Pstar : ℝ} (hε : 1 < ε) (hθ : μ.real S = θ)
    {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j) (hPs : 0 < Pstar)
    (hI : Integrable (fun j => p₀ j ^ (1 - ε)) μ) (hS1 : ∀ j ∈ S, p₁ j = p₀ j)
    (hSc : ∀ j ∉ S, p₁ j = Pstar)
    (hLLN : ∫ j in S, p₀ j ^ (1 - ε) ∂μ = θ * ∫ j, p₀ j ^ (1 - ε) ∂μ) :
    nk_priceIndex μ ε p₁ ^ (1 - ε) =
      θ * nk_priceIndex μ ε p₀ ^ (1 - ε) + (1 - θ) * Pstar ^ (1 - ε) := by
  have hint := nk_calvo_avg (g := fun j => p₁ j ^ (1 - ε)) (c := Pstar ^ (1 - ε)) hS hθ hI
    (fun j hj => by simp only [hS1 j hj]) (fun j hj => by simp only [hSc j hj]) hLLN
  have hI0 := (nk_integral_rpow_pos hp₀ hI).le
  have hθ0 : 0 ≤ θ := hθ ▸ measureReal_nonneg
  have hθ1 : θ ≤ 1 := hθ ▸ measureReal_le_one
  have hI1 : 0 ≤ ∫ j, p₁ j ^ (1 - ε) ∂μ := by
    rw [hint]
    have := mul_nonneg (sub_nonneg.2 hθ1) (Real.rpow_pos_of_pos hPs (1 - ε)).le
    have := mul_nonneg hθ0 hI0
    linarith
  rw [nk_priceIndex_rpow (by linarith) hI1, nk_priceIndex_rpow (by linarith) hI0, hint]

/-- Miao, p. 622: the price dispersion `Δ_t = ∫ (P^j_t/P_t)^{−ε/(1−α)} dj`. -/
noncomputable def nk_dispersion {J : Type*} [MeasurableSpace J] (μ : Measure J) (ε α : ℝ)
    (p : J → ℝ) (P : ℝ) : ℝ :=
  ∫ j, (p j / P) ^ (-ε / (1 - α)) ∂μ

/-- **(19.15)** (Miao, p. 622): with each firm on its demand curve (19.6) and using the labour
`N^j = (Y^j/A)^{1/(1−α)}` that (19.8) requires, aggregate labour is
`N = ∫ N^j dj = (Y/A)^{1/(1−α)}Δ`. -/
theorem eq_19_15 {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε α A Y P : ℝ}
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) {p : J → ℝ} (hp : ∀ j, 0 < p j) :
    ∫ j, ((p j / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)) ∂μ =
      (Y / A) ^ (1 / (1 - α)) * nk_dispersion μ ε α p P := by
  have hpt : ∀ j, ((p j / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)) =
      (p j / P) ^ (-ε / (1 - α)) * (Y / A) ^ (1 / (1 - α)) := fun j => by
    have hq := div_pos (hp j) hP
    rw [mul_div_assoc, Real.mul_rpow (Real.rpow_nonneg hq.le _) (div_pos hY hA).le,
      ← Real.rpow_mul hq.le]
    congr 2
    ring
  simp only [hpt]
  rw [integral_mul_const, nk_dispersion, mul_comm]

/-- **(19.16)** (Miao, p. 622): from (19.15), `Y = AN^{1−α}Δ^{α−1}` (`A, Y, Δ > 0`, `α < 1`). -/
theorem eq_19_16 {α A Y N Δ : ℝ} (hA : 0 < A) (hY : 0 < Y) (hΔ : 0 < Δ) (hα : α < 1)
    (h15 : N = (Y / A) ^ (1 / (1 - α)) * Δ) : Y = A * N ^ (1 - α) * Δ ^ (α - 1) := by
  have hq := div_pos hY hA
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  rw [h15, Real.mul_rpow (Real.rpow_nonneg hq.le _) hΔ.le, ← Real.rpow_mul hq.le,
    show 1 / (1 - α) * (1 - α) = 1 by field_simp, Real.rpow_one]
  have e : Δ ^ (1 - α) * Δ ^ (α - 1) = 1 := by
    rw [← Real.rpow_add hΔ]
    norm_num
  calc Y = A * (Y / A) * (Δ ^ (1 - α) * Δ ^ (α - 1)) := by rw [e]; field_simp
    _ = A * (Y / A * Δ ^ (1 - α)) * Δ ^ (α - 1) := by ring

/-- **(19.17)** (Miao, p. 622): price-dispersion dynamics. Prices at `t` are `p₁ = p₀` on the
non-adjusters `S` (`μ(S) = θ`) and `P*` elsewhere; under the law of large numbers
`∫_S (p₀/P₀)^{−ε/(1−α)} = θΔ_{t−1}`,
`Δ_t = θΠ_t^{ε/(1−α)}Δ_{t−1} + (1 − θ)(P*/P₁)^{−ε/(1−α)}` with `Π_t = P₁/P₀`. -/
theorem eq_19_17 {J : Type*} [MeasurableSpace J] {μ : Measure J} [IsProbabilityMeasure μ]
    {S : Set J} (hS : MeasurableSet S) {θ ε α Pstar P₀ P₁ : ℝ} (hθ : μ.real S = θ)
    (hP₀ : 0 < P₀) (hP₁ : 0 < P₁) {p₀ p₁ : J → ℝ} (hp₀ : ∀ j, 0 < p₀ j)
    (hI : Integrable (fun j => (p₀ j / P₀) ^ (-ε / (1 - α))) μ)
    (hS1 : ∀ j ∈ S, p₁ j = p₀ j) (hSc : ∀ j ∉ S, p₁ j = Pstar)
    (hLLN : ∫ j in S, (p₀ j / P₀) ^ (-ε / (1 - α)) ∂μ = θ * nk_dispersion μ ε α p₀ P₀) :
    nk_dispersion μ ε α p₁ P₁ = θ * (P₁ / P₀) ^ (ε / (1 - α)) * nk_dispersion μ ε α p₀ P₀ +
      (1 - θ) * (Pstar / P₁) ^ (-ε / (1 - α)) := by
  set a := -ε / (1 - α)
  set k := (P₀ / P₁) ^ a
  have hk : k = (P₁ / P₀) ^ (ε / (1 - α)) := by
    simp only [k, a]
    rw [show P₀ / P₁ = (P₁ / P₀)⁻¹ by rw [inv_div], Real.inv_rpow (div_pos hP₁ hP₀).le,
      ← Real.rpow_neg (div_pos hP₁ hP₀).le]
    congr 2
    ring
  have hf : ∀ j, (p₀ j / P₁) ^ a = k * (p₀ j / P₀) ^ a := fun j => by
    simp only [k]
    rw [← Real.mul_rpow (div_pos hP₀ hP₁).le (div_pos (hp₀ j) hP₀).le]
    congr 1
    field_simp
  have hfI : Integrable (fun j => (p₀ j / P₁) ^ a) μ := by
    simp only [hf]
    exact hI.const_mul k
  have hLLN' : ∫ j in S, (p₀ j / P₁) ^ a ∂μ = θ * ∫ j, (p₀ j / P₁) ^ a ∂μ := by
    simp only [hf]
    rw [integral_const_mul, integral_const_mul, hLLN, nk_dispersion]
    ring
  have h := nk_calvo_avg (g := fun j => (p₁ j / P₁) ^ a) (c := (Pstar / P₁) ^ a) hS hθ hfI
    (fun j hj => by simp only [hS1 j hj]) (fun j hj => by simp only [hSc j hj]) hLLN'
  rw [nk_dispersion, h]
  simp only [hf]
  rw [integral_const_mul, ← hk]
  simp only [nk_dispersion, a]
  ring

/-- **(19.14)** (Miao, p. 621), the Taylor rule
`ln((1 + i_t)/(1 + i)) = φ_π ln(P_t/P_{t−1}) + φ_y ln(Y_t/Y^f_t) + v_t`, `i = 1/β − 1`. -/
def nk_taylorRule (φπ φy β i Pt Ptm1 Y Yf v : ℝ) : Prop :=
  Real.log ((1 + i) / (1 + (1 / β - 1))) = φπ * Real.log (Pt / Ptm1) + φy * Real.log (Y / Yf) + v

/-- Miao, p. 624: (19.11) at constant inputs. With weights `w_k = (θβ)^kΛ` (`0 ≤ θβ < 1`,
`Λ, P, Y > 0`, `MC ≠ 0`) and constant `P_k = P`, `Y_k = Y`, `MC_k = MC`, the right side of
(19.11) is `μMC·P`, `μ = ε/(ε − 1)`. -/
theorem nk_reset_constant {θ β Λ ε P Y MC : ℝ} (h0 : 0 ≤ θ * β) (h1 : θ * β < 1) (hΛ : 0 < Λ)
    (hP : 0 < P) (hY : 0 < Y) :
    ε / (ε - 1) * (∑' k : ℕ, (θ * β) ^ k * Λ * P ^ ε * Y * MC) /
        ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ (ε - 1) * Y = ε / (ε - 1) * MC * P := by
  have hg := tsum_geometric_of_lt_one h0 h1
  have e1 : ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ ε * Y * MC =
      (∑' k : ℕ, (θ * β) ^ k) * (Λ * P ^ ε * Y * MC) := by
    rw [← tsum_mul_right]
    exact tsum_congr fun k => by ring
  have e2 : ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ (ε - 1) * Y =
      (∑' k : ℕ, (θ * β) ^ k) * (Λ * P ^ (ε - 1) * Y) := by
    rw [← tsum_mul_right]
    exact tsum_congr fun k => by ring
  have hs : 0 < ∑' k : ℕ, (θ * β) ^ k := by
    rw [hg]
    exact inv_pos.2 (by linarith)
  rw [e1, e2, Real.rpow_sub hP, Real.rpow_one]
  have := Real.rpow_pos_of_pos hP ε
  field_simp

/-- The zero-inflation deterministic steady state (Miao, pp. 621–624). At constant
`C = Y > 0`, `P = P* > 0`, `Π = 1`, `Δ = 1`, `MC`, `1 + i = 1/β` and `Y = Y^f`, `v = 0`:
the Euler equation (19.3) holds, (19.11) holds (with weights `(θβ)^kΛ`) iff `MC = 1/μ`,
(19.13) and (19.17) hold, and the Taylor rule (19.14) holds. -/
theorem nk_steady_state {θ β γ ε α φπ φy Λ P Y MC : ℝ} (hβ : 0 < β) (hθ0 : 0 ≤ θ)
    (hθβ : θ * β < 1) (hε : 1 < ε) (hΛ : 0 < Λ) (hP : 0 < P) (hY : 0 < Y) :
    (1 = β * (1 + (1 / β - 1)) * ((Y / Y) ^ (-γ) * (P / P))) ∧
    (P = ε / (ε - 1) * (∑' k : ℕ, (θ * β) ^ k * Λ * P ^ ε * Y * MC) /
        ∑' k : ℕ, (θ * β) ^ k * Λ * P ^ (ε - 1) * Y ↔ MC = (ε - 1) / ε) ∧
    (P ^ (1 - ε) = θ * P ^ (1 - ε) + (1 - θ) * P ^ (1 - ε)) ∧
    ((1 : ℝ) = θ * (P / P) ^ (ε / (1 - α)) * 1 + (1 - θ) * (P / P) ^ (-ε / (1 - α))) ∧
    nk_taylorRule φπ φy β (1 / β - 1) P P Y Y 0 := by
  have hPP : P / P = 1 := div_self hP.ne'
  have hYY : Y / Y = 1 := div_self hY.ne'
  refine ⟨?_, ?_, by ring, ?_, ?_⟩
  · rw [hPP, hYY, Real.one_rpow]
    field_simp
    ring
  · rw [nk_reset_constant (mul_nonneg hθ0 hβ.le) hθβ hΛ hP hY]
    have hε0 : ε ≠ 0 := by linarith
    have hε1 : ε - 1 ≠ 0 := by linarith
    constructor
    · intro h
      have h2 : ε / (ε - 1) * MC * P = 1 * P := by rw [one_mul]; exact h.symm
      have h3 := mul_right_cancel₀ hP.ne' h2
      field_simp at h3 ⊢
      linarith
    · intro h
      rw [h]
      field_simp
  · rw [hPP, Real.one_rpow, Real.one_rpow]
    ring
  · have hb : (1 : ℝ) + (1 / β - 1) ≠ 0 := by
      rw [show (1 : ℝ) + (1 / β - 1) = 1 / β by ring]
      positivity
    simp only [nk_taylorRule, hPP, hYY, Real.log_one, mul_zero, add_zero, div_self hb]

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic DNK model: the flexible price equilibrium (Miao §19.1.6)

Miao, §19.1.6, p. 623, with `μ = ε/(ε − 1)` the desired markup.

* At `θ = 0` the weights `θ^kβ^kΛ_{t+k}` of (19.11) vanish for `k ≥ 1`, and (19.11) becomes
  `P*_t/P_t = μMC^j_t` (`nk_flex_reset`). The book writes "`θ → 0`"; the formula is the value
  at `θ = 0` (the limit is not formalised).
* With symmetric prices `P* = P`: `MC^j = 1/μ`, `Y^j = Y` (`nk_flex_symmetric`), and by (19.9)
  with `Y = AN^{1−α}`, `W/P = (1/μ)(1 − α)AN^{−α}` (`nk_flex_wage`).
* **(19.18)**: with (19.2) and `C = Y = AN^{1−α}`, the labour market clears iff
  `ln N = (ln((1 − α)/(μχ)) + (1 − γ)ln A)/(γ(1 − α) + α + ν)`, and then
  `Y^f = ((1 − α)/(μχ))^{(1−α)/(γ(1−α)+α+ν)}A^{(1+ν)/(γ(1−α)+α+ν)}` (`eq_19_18`): a unique
  flexible-price equilibrium, with output determined by productivity alone.
-/

namespace Miao.NewKeynesian

/-- Miao, p. 623: (19.11) at `θ = 0`. With weights `w_k = 0^k c_k` (`c₀ ≠ 0`), the right side
of (19.11) is `μMC₀P₀`; so the reset price satisfies `P*/P₀ = μMC₀`, a markup over marginal
cost. -/
theorem nk_flex_reset {ε x : ℝ} {c Pk Yk MC : ℕ → ℝ} (hc : c 0 ≠ 0) (hP : 0 < Pk 0)
    (hY : 0 < Yk 0)
    (h11 : x = ε / (ε - 1) * (∑' k, (0 : ℝ) ^ k * c k * Pk k ^ ε * Yk k * MC k) /
      ∑' k, (0 : ℝ) ^ k * c k * Pk k ^ (ε - 1) * Yk k) :
    x / Pk 0 = ε / (ε - 1) * MC 0 := by
  have e1 : ∑' k, (0 : ℝ) ^ k * c k * Pk k ^ ε * Yk k * MC k = c 0 * Pk 0 ^ ε * Yk 0 * MC 0 := by
    rw [tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
    simp
  have e2 : ∑' k, (0 : ℝ) ^ k * c k * Pk k ^ (ε - 1) * Yk k = c 0 * Pk 0 ^ (ε - 1) * Yk 0 := by
    rw [tsum_eq_single 0 fun k hk => by simp [zero_pow hk]]
    simp
  rw [h11, e1, e2, Real.rpow_sub hP, Real.rpow_one]
  have := Real.rpow_pos_of_pos hP ε
  field_simp

/-- Miao, p. 623: with flexible prices all firms are symmetric. If `P* = P` and
`P*/P = μMC^j` (`ε > 1`) then `MC^j = 1/μ`, and the demand (19.6) gives `Y^j = Y`. -/
theorem nk_flex_symmetric {ε P MCj Y : ℝ} (hε : 1 < ε) (hP : 0 < P)
    (h : P / P = ε / (ε - 1) * MCj) : MCj = (ε - 1) / ε ∧ (P / P) ^ (-ε) * Y = Y := by
  rw [div_self hP.ne'] at h
  refine ⟨?_, by rw [div_self hP.ne', Real.one_rpow, one_mul]⟩
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  field_simp at h ⊢
  linarith

/-- Miao, p. 623: with `MC = 1/μ` and `Y = AN^{1−α}`, (19.9) gives
`W/P = (1/μ)(1 − α)AN^{−α}`. -/
theorem nk_flex_wage {w A α N mu : ℝ} (hA : 0 < A) (hN : 0 < N) (hα : α < 1)
    (h : nk_MCavg w A α (A * N ^ (1 - α)) = 1 / mu) :
    w = 1 / mu * (1 - α) * A * N ^ (-α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have e : (A * N ^ (1 - α) / A) ^ (-α / (1 - α)) = N ^ (-α) := by
    rw [mul_div_cancel_left₀ _ hA.ne', ← Real.rpow_mul hN.le]
    congr 1
    field_simp
  rw [nk_MCavg, e] at h
  have hpos : 0 < A * (1 - α) * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  rw [div_eq_iff hpos.ne'] at h
  rw [h]
  ring

/-- **(19.18)** (Miao, p. 623), the flexible-price (natural) output. With
`D = γ(1 − α) + α + ν > 0`, `α < 1`, `μ, χ, A, N > 0`: the labour-market condition
`χN^ν/C^{−γ} = (1/μ)(1 − α)AN^{−α}` with `C = AN^{1−α}` holds iff
`ln N = (ln((1 − α)/(μχ)) + (1 − γ)ln A)/D`, and then
`AN^{1−α} = ((1 − α)/(μχ))^{(1−α)/D}A^{(1+ν)/D}`. -/
theorem eq_19_18 {γ ν α χ mu A N : ℝ} (hα1 : α < 1) (hχ : 0 < χ)
    (hmu : 0 < mu) (hA : 0 < A) (hN : 0 < N) (hD : 0 < γ * (1 - α) + α + ν) :
    (χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ) = 1 / mu * (1 - α) * A * N ^ (-α) ↔
      Real.log N = (Real.log ((1 - α) / (mu * χ)) + (1 - γ) * Real.log A) /
        (γ * (1 - α) + α + ν)) ∧
    (Real.log N = (Real.log ((1 - α) / (mu * χ)) + (1 - γ) * Real.log A) /
        (γ * (1 - α) + α + ν) →
      A * N ^ (1 - α) = ((1 - α) / (mu * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν)) *
        A ^ ((1 + ν) / (γ * (1 - α) + α + ν))) := by
  set D := γ * (1 - α) + α + ν
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have hk : 0 < (1 - α) / (mu * χ) := by positivity
  have hY : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have hL : 0 < χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ) :=
    div_pos (mul_pos hχ (Real.rpow_pos_of_pos hN _)) (Real.rpow_pos_of_pos hY _)
  have hR : 0 < 1 / mu * (1 - α) * A * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  have logL : Real.log (χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ)) =
      Real.log χ + ν * Real.log N + γ * (Real.log A + (1 - α) * Real.log N) := by
    rw [Real.log_div (mul_pos hχ (Real.rpow_pos_of_pos hN _)).ne'
      (Real.rpow_pos_of_pos hY _).ne', Real.log_mul hχ.ne' (Real.rpow_pos_of_pos hN _).ne',
      Real.log_rpow hN, Real.log_rpow hY, Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne',
      Real.log_rpow hN]
    ring
  have logR : Real.log (1 / mu * (1 - α) * A * N ^ (-α)) =
      -Real.log mu + Real.log (1 - α) + Real.log A - α * Real.log N := by
    rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hN _).ne',
      Real.log_mul (by positivity) hA.ne', Real.log_mul (by positivity) h1p.ne',
      one_div, Real.log_inv, Real.log_rpow hN]
    ring
  have logk : Real.log ((1 - α) / (mu * χ)) = Real.log (1 - α) - Real.log mu - Real.log χ := by
    rw [Real.log_div h1p.ne' (by positivity), Real.log_mul hmu.ne' hχ.ne']
    ring
  refine ⟨?_, ?_⟩
  · rw [← Real.log_injOn_pos.eq_iff hL hR, logL, logR, logk, eq_div_iff hD.ne']
    constructor <;> intro h <;> linarith
  · intro h
    apply Real.log_injOn_pos hY (mul_pos (Real.rpow_pos_of_pos hk _) (Real.rpow_pos_of_pos hA _))
    rw [Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN,
      Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hA _).ne',
      Real.log_rpow hk, Real.log_rpow hA, h]
    field_simp
    ring

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The basic DNK model: log-linearising the equilibrium conditions (Miao §19.1.7)

Miao, §19.1.7, pp. 624–627. A log-linearisation is made precise as a first-order perturbation:
every variable is a positive differentiable path `s ↦ X(s)` through its zero-inflation
steady-state value `X(0)`, the nonlinear equation holds for every `s`, and the hat variable is
the log-derivative `X̂ = d ln X(s)/ds` at `s = 0`. Differentiating the equation at `s = 0` gives
the log-linear equation exactly. Tools: `nk_path_deriv`, `nk_rpow_path`.

* (19.19) from (19.13): `P̂_t = θP̂_{t−1} + (1 − θ)P̂*_t`, so `q_t = θπ_t/(1 − θ)` (`eq_19_19`).
* The terms of (19.11) (`nk_loglin_reset_terms`); the "simplifying" step to (19.20) is
  `eq_19_20` in `NKPhillips`.
* (19.21) from (19.12), with `b` of (19.22) (`eq_19_21`, `nk_b`).
* The log-linear (19.2) (`nk_loglin_19_2`), (19.9) (`nk_loglin_MC`), (19.16)
  (`nk_loglin_19_16`), (19.17) (`nk_loglin_19_17`) and (19.18) (`nk_loglin_19_18`).
  With (19.19), the dispersion obeys `Δ̂_t = θΔ̂_{t−1}` (`nk_loglin_dispersion`), so from the
  steady state (`Δ̂_{−1} = 0`) `Δ̂_t = 0` for all `t` and `Ŷ_t = Â_t + (1 − α)N̂_t`
  (`nk_dispersion_zero`, `nk_loglin_output`): "the price dispersion term does not matter up to
  first order". The book's total differential of (19.16) treats the dispersion of the previous
  period as fixed; the recursion makes this explicit.
* (19.26) and the natural rate (19.27) from the Euler equations, for `E_t` an expectation over
  finitely many successor states with probabilities `q_j` (`nk_loglin_euler`, `eq_19_26`,
  `nk_loglin_natural_rate`); in them `i_t` and `r^n_t` stand for `ln(1 + i_t)`,
  `ln(1 + r^n_t)`, and `ı̂_t = ln(1 + i_t) − ln(1 + i) = ln(1 + i_t) + ln β` exactly. The book's
  `ı̂_t = i_t + ln β` uses `ln(1 + i_t) ≈ i_t` in addition.
* (19.29) from (19.14): exact, with `i_t := ln(1 + i_t)`, `π_t = ln Π_t`, `x_t = ln(Y_t/Y^f_t)`
  (`eq_19_29`).

**Departure.** The conditional expectation in (19.26)–(19.27) is over finitely many successor
states; the infinite sum in (19.11) is log-linearised term by term (`nk_loglin_reset_terms`).
-/

namespace Miao.NewKeynesian

/-- A positive path with log-derivative `x̂` at `0` has derivative `X(0)x̂` at `0`. -/
theorem nk_path_deriv {X : ℝ → ℝ} {xh : ℝ} (hX : ∀ s, 0 < X s)
    (h : HasDerivAt (fun s => Real.log (X s)) xh 0) : HasDerivAt X (X 0 * xh) 0 := by
  have hd := (Real.hasDerivAt_exp (Real.log (X 0))).comp 0 h
  rw [Real.exp_log (hX 0)] at hd
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (Real.exp_log (hX s)).symm)

/-- The derivative of `X(s)^a` along a positive path: `aX(0)^a x̂`. -/
theorem nk_rpow_path {X : ℝ → ℝ} {xh : ℝ} (a : ℝ) (hX : ∀ s, 0 < X s)
    (h : HasDerivAt (fun s => Real.log (X s)) xh 0) :
    HasDerivAt (fun s => X s ^ a) (a * X 0 ^ a * xh) 0 := by
  have e : (fun s => X s ^ a) = fun s => Real.exp (a * Real.log (X s)) :=
    funext fun s => by rw [Real.rpow_def_of_pos (hX s), mul_comm]
  have hd := (Real.hasDerivAt_exp _).comp 0 (h.const_mul a)
  rw [e]
  refine hd.congr_deriv ?_
  rw [← mul_comm (Real.log (X 0)), ← Real.rpow_def_of_pos (hX 0)]
  ring

/-- **(19.19)** (Miao, p. 624): log-linearising (19.13). If `P_t(s), P_{t−1}(s), P*_t(s) > 0`
satisfy (19.13) for every `s`, all equal `P̄` at `s = 0` (zero inflation), and have
log-derivatives `p̂, p̂₋, p̂*`, then `p̂ = θp̂₋ + (1 − θ)p̂*`, and for `θ ≠ 1`,
`q = p̂* − p̂ = θπ/(1 − θ)` with `π = p̂ − p̂₋`. -/
theorem eq_19_19 {θ ε : ℝ} {P Pm Ps : ℝ → ℝ} {ph pmh psh : ℝ} (hε : ε ≠ 1) (hθ : θ ≠ 1)
    (hP : ∀ s, 0 < P s) (hPm : ∀ s, 0 < Pm s) (hPs : ∀ s, 0 < Ps s)
    (h0m : Pm 0 = P 0) (h0s : Ps 0 = P 0)
    (dP : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (dPm : HasDerivAt (fun s => Real.log (Pm s)) pmh 0)
    (dPs : HasDerivAt (fun s => Real.log (Ps s)) psh 0)
    (h13 : ∀ s, P s ^ (1 - ε) = θ * Pm s ^ (1 - ε) + (1 - θ) * Ps s ^ (1 - ε)) :
    ph = θ * pmh + (1 - θ) * psh ∧ psh - ph = θ / (1 - θ) * (ph - pmh) := by
  have d1 := nk_rpow_path (1 - ε) hP dP
  have d2 := ((nk_rpow_path (1 - ε) hPm dPm).const_mul θ).add
    ((nk_rpow_path (1 - ε) hPs dPs).const_mul (1 - θ))
  have e : (fun s => P s ^ (1 - ε)) =
      (fun s => θ * Pm s ^ (1 - ε)) + fun s => (1 - θ) * Ps s ^ (1 - ε) := funext h13
  rw [e] at d1
  have hu := d1.unique d2
  rw [h0m, h0s] at hu
  have hc : (1 - ε) * P 0 ^ (1 - ε) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (Ne.symm hε)) (Real.rpow_pos_of_pos (hP 0) _).ne'
  have h1 : ph = θ * pmh + (1 - θ) * psh := by
    apply mul_left_cancel₀ hc
    linear_combination hu
  refine ⟨h1, ?_⟩
  have h2 : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  field_simp
  linear_combination (-1) * h1

/-- **(19.22)** (Miao, p. 624): `b = εα/(1 − α)`. -/
noncomputable def nk_b (ε α : ℝ) : ℝ := ε * α / (1 - α)

/-- **(19.21)** (Miao, p. 624): log-linearising (19.12). If
`MC_{k|t}(s) = MC_k(s)(P*(s)/P_k(s))^{εα/(α−1)}` for every `s` (positive paths), then
`m̂_{k|t} = m̂_k − b(p̂* − p̂_k)`, `b = εα/(1 − α)`. -/
theorem eq_19_21 {ε α : ℝ} {MCkt MCk Ps Pk : ℝ → ℝ} {mkt mk psh pkh : ℝ} (hα : α ≠ 1)
    (h2 : ∀ s, 0 < MCk s) (h3 : ∀ s, 0 < Ps s) (h4 : ∀ s, 0 < Pk s)
    (d1 : HasDerivAt (fun s => Real.log (MCkt s)) mkt 0)
    (d2 : HasDerivAt (fun s => Real.log (MCk s)) mk 0)
    (d3 : HasDerivAt (fun s => Real.log (Ps s)) psh 0)
    (d4 : HasDerivAt (fun s => Real.log (Pk s)) pkh 0)
    (h12 : ∀ s, MCkt s = MCk s * (Ps s / Pk s) ^ (ε * α / (α - 1))) :
    mkt = mk - nk_b ε α * (psh - pkh) := by
  have e : (fun s => Real.log (MCkt s)) = fun s => Real.log (MCk s) +
      ε * α / (α - 1) * (Real.log (Ps s) - Real.log (Pk s)) := funext fun s => by
    rw [h12, Real.log_mul (h2 s).ne' (Real.rpow_pos_of_pos (div_pos (h3 s) (h4 s)) _).ne',
      Real.log_rpow (div_pos (h3 s) (h4 s)), Real.log_div (h3 s).ne' (h4 s).ne']
  rw [e] at d1
  have hu := d1.unique (d2.add ((d3.sub d4).const_mul _))
  rw [hu, nk_b]
  have : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have : α - 1 ≠ 0 := sub_ne_zero.2 hα
  field_simp
  ring

/-- Miao, p. 624: log-linearising the terms of (19.11) in the form
`P*_t Y_{t+k}^{1−γ}P_{t+k}^{ε−1} = μY_{t+k}^{1−γ}P_{t+k}^εMC_{t+k|t}` (term by term). Along
positive paths through a steady state with `P*(0) = P_k(0) = P̄` and `μMC_{k|t}(0) = 1`, the
derivatives of the two sides are `c(p̂* + (1 − γ)ŷ_k + (ε − 1)p̂_k)` and
`c((1 − γ)ŷ_k + εp̂_k + m̂_{k|t})` with the same `c = P̄Y_k(0)^{1−γ}P̄^{ε−1} > 0`. -/
theorem nk_loglin_reset_terms {γ ε mu : ℝ} {Ps Yk Pk MC : ℝ → ℝ} {psh yh pkh mh : ℝ}
    (h1 : ∀ s, 0 < Ps s) (h2 : ∀ s, 0 < Yk s) (h3 : ∀ s, 0 < Pk s) (h4 : ∀ s, 0 < MC s)
    (hss : Ps 0 = Pk 0) (hmc : mu * MC 0 = 1)
    (d1 : HasDerivAt (fun s => Real.log (Ps s)) psh 0)
    (d2 : HasDerivAt (fun s => Real.log (Yk s)) yh 0)
    (d3 : HasDerivAt (fun s => Real.log (Pk s)) pkh 0)
    (d4 : HasDerivAt (fun s => Real.log (MC s)) mh 0) :
    HasDerivAt (fun s => Ps s * Yk s ^ (1 - γ) * Pk s ^ (ε - 1))
      (Pk 0 * Yk 0 ^ (1 - γ) * Pk 0 ^ (ε - 1) * (psh + (1 - γ) * yh + (ε - 1) * pkh)) 0 ∧
    HasDerivAt (fun s => mu * Yk s ^ (1 - γ) * Pk s ^ ε * MC s)
      (Pk 0 * Yk 0 ^ (1 - γ) * Pk 0 ^ (ε - 1) * ((1 - γ) * yh + ε * pkh + mh)) 0 ∧
    0 < Pk 0 * Yk 0 ^ (1 - γ) * Pk 0 ^ (ε - 1) := by
  have a1 := nk_path_deriv h1 d1
  have a2 := nk_rpow_path (1 - γ) h2 d2
  have a3 := nk_rpow_path (ε - 1) h3 d3
  have a3' := nk_rpow_path ε h3 d3
  have a4 := nk_path_deriv h4 d4
  have hp := h3 0
  have hy := Real.rpow_pos_of_pos (h2 0) (1 - γ)
  have hpe : Pk 0 ^ ε = Pk 0 * Pk 0 ^ (ε - 1) := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    field_simp
  refine ⟨?_, ?_, by have := Real.rpow_pos_of_pos hp (ε - 1); positivity⟩
  · refine ((a1.mul a2).mul a3).congr_deriv ?_
    simp only [Pi.mul_apply, hss]
    ring
  · refine ((((hasDerivAt_const (0 : ℝ) mu).mul a2).mul a3').mul a4).congr_deriv ?_
    have hm : MC 0 = 1 / mu := by
      have : mu ≠ 0 := by
        rintro rfl
        simp at hmc
      field_simp
      linarith
    simp only [Pi.mul_apply]
    rw [hm, hpe]
    have : mu ≠ 0 := by
      rintro rfl
      simp at hmc
    field_simp
    ring

/-- Miao, p. 625: log-linearising (19.2). If `χN(s)^ν/C(s)^{−γ} = W(s)/P(s)` for every `s`
(positive paths), then `ŵ − p̂ = νn̂ + γĉ`. -/
theorem nk_loglin_19_2 {χ ν γ : ℝ} {N C W P : ℝ → ℝ} {nh ch wh ph : ℝ} (hχ : 0 < χ)
    (h1 : ∀ s, 0 < N s) (h2 : ∀ s, 0 < C s) (h3 : ∀ s, 0 < W s) (h4 : ∀ s, 0 < P s)
    (d1 : HasDerivAt (fun s => Real.log (N s)) nh 0)
    (d2 : HasDerivAt (fun s => Real.log (C s)) ch 0)
    (d3 : HasDerivAt (fun s => Real.log (W s)) wh 0)
    (d4 : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (h : ∀ s, χ * N s ^ ν / C s ^ (-γ) = W s / P s) : wh - ph = ν * nh + γ * ch := by
  have e : (fun s => Real.log (W s) - Real.log (P s)) =
      fun s => Real.log χ + ν * Real.log (N s) + γ * Real.log (C s) := funext fun s => by
    rw [← Real.log_div (h3 s).ne' (h4 s).ne', ← h s,
      Real.log_div (mul_pos hχ (Real.rpow_pos_of_pos (h1 s) _)).ne'
        (Real.rpow_pos_of_pos (h2 s) _).ne',
      Real.log_mul hχ.ne' (Real.rpow_pos_of_pos (h1 s) _).ne', Real.log_rpow (h1 s),
      Real.log_rpow (h2 s)]
    ring
  have hd : HasDerivAt (fun s => Real.log (W s) - Real.log (P s)) (wh - ph) 0 := d3.sub d4
  rw [e] at hd
  have hu := hd.unique (((hasDerivAt_const (0 : ℝ) (Real.log χ)).add (d1.const_mul ν)).add
    (d2.const_mul γ))
  linarith

/-- Miao, p. 625: log-linearising (19.9). If
`MC(s) = (W(s)/P(s))/(A(s)(1 − α)(Y(s)/A(s))^{−α/(1−α)})`
for every `s` (positive paths, `α < 1`), then `m̂ = ŵ − p̂ + α/(1 − α)ŷ − 1/(1 − α)â`. -/
theorem nk_loglin_MC {α : ℝ} {MC W P A Y : ℝ → ℝ} {mh wh ph ah yh : ℝ} (hα : α < 1)
    (h2 : ∀ s, 0 < W s) (h3 : ∀ s, 0 < P s) (h4 : ∀ s, 0 < A s)
    (h5 : ∀ s, 0 < Y s)
    (d1 : HasDerivAt (fun s => Real.log (MC s)) mh 0)
    (d2 : HasDerivAt (fun s => Real.log (W s)) wh 0)
    (d3 : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (d4 : HasDerivAt (fun s => Real.log (A s)) ah 0)
    (d5 : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (h : ∀ s, MC s = nk_MCavg (W s / P s) (A s) α (Y s)) :
    mh = wh - ph + α / (1 - α) * yh - 1 / (1 - α) * ah := by
  have h1p : (0 : ℝ) < 1 - α := by linarith
  have e : (fun s => Real.log (MC s)) = fun s => Real.log (W s) - Real.log (P s) -
      Real.log (A s) - Real.log (1 - α) + α / (1 - α) * (Real.log (Y s) - Real.log (A s)) :=
    funext fun s => by
      have hq := div_pos (h5 s) (h4 s)
      have hr := Real.rpow_pos_of_pos hq (-α / (1 - α))
      have hm : 0 < A s * (1 - α) := mul_pos (h4 s) h1p
      rw [h s, nk_MCavg, Real.log_div (div_pos (h2 s) (h3 s)).ne' (mul_pos hm hr).ne',
        Real.log_div (h2 s).ne' (h3 s).ne', Real.log_mul hm.ne' hr.ne',
        Real.log_mul (h4 s).ne' h1p.ne', Real.log_rpow hq, Real.log_div (h5 s).ne' (h4 s).ne']
      ring
  rw [e] at d1
  have hu := d1.unique (((((d2.sub d3).sub d4).sub (hasDerivAt_const (0 : ℝ) _)).add
    ((d5.sub d4).const_mul (α / (1 - α)))))
  rw [hu]
  field_simp
  ring

/-- Miao, p. 625: log-linearising (19.16). If `Y(s) = A(s)N(s)^{1−α}Δ(s)^{α−1}` for every `s`
(positive paths), then `ŷ = â + (1 − α)n̂ + (α − 1)Δ̂`. -/
theorem nk_loglin_19_16 {α : ℝ} {Y A N Δ : ℝ → ℝ} {yh ah nh dh : ℝ}
    (h2 : ∀ s, 0 < A s) (h3 : ∀ s, 0 < N s) (h4 : ∀ s, 0 < Δ s)
    (d1 : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (d2 : HasDerivAt (fun s => Real.log (A s)) ah 0)
    (d3 : HasDerivAt (fun s => Real.log (N s)) nh 0)
    (d4 : HasDerivAt (fun s => Real.log (Δ s)) dh 0)
    (h : ∀ s, Y s = A s * N s ^ (1 - α) * Δ s ^ (α - 1)) :
    yh = ah + (1 - α) * nh + (α - 1) * dh := by
  have e : (fun s => Real.log (Y s)) = fun s => Real.log (A s) + (1 - α) * Real.log (N s) +
      (α - 1) * Real.log (Δ s) := funext fun s => by
    rw [h s, Real.log_mul (mul_pos (h2 s) (Real.rpow_pos_of_pos (h3 s) _)).ne'
      (Real.rpow_pos_of_pos (h4 s) _).ne', Real.log_mul (h2 s).ne'
      (Real.rpow_pos_of_pos (h3 s) _).ne', Real.log_rpow (h3 s), Real.log_rpow (h4 s)]
  rw [e] at d1
  exact d1.unique ((d2.add (d3.const_mul _)).add (d4.const_mul _))

/-- Miao, pp. 622, 625: log-linearising (19.17) around `Δ = Π = P*/P = 1`. If
`Δ(s) = θΠ(s)^{ε/(1−α)}Δ₋(s) + (1 − θ)Q(s)^{−ε/(1−α)}` for every `s` (positive paths, all `1` at
`s = 0`), then `Δ̂ = θΔ̂₋ + (ε/(1 − α))(θπ − (1 − θ)q)`. -/
theorem nk_loglin_19_17 {θ ε α : ℝ} {Δ Δm Infl Q : ℝ → ℝ} {dh dmh pih qh : ℝ}
    (h1 : ∀ s, 0 < Δ s) (h2 : ∀ s, 0 < Δm s) (h3 : ∀ s, 0 < Infl s) (h4 : ∀ s, 0 < Q s)
    (e1 : Δ 0 = 1) (e2 : Δm 0 = 1) (e3 : Infl 0 = 1) (e4 : Q 0 = 1)
    (d1 : HasDerivAt (fun s => Real.log (Δ s)) dh 0)
    (d2 : HasDerivAt (fun s => Real.log (Δm s)) dmh 0)
    (d3 : HasDerivAt (fun s => Real.log (Infl s)) pih 0)
    (d4 : HasDerivAt (fun s => Real.log (Q s)) qh 0)
    (h : ∀ s, Δ s = θ * Infl s ^ (ε / (1 - α)) * Δm s + (1 - θ) * Q s ^ (-ε / (1 - α))) :
    dh = θ * dmh + ε / (1 - α) * (θ * pih - (1 - θ) * qh) := by
  have a1 := nk_path_deriv h1 d1
  have a2 := nk_path_deriv h2 d2
  have a3 := nk_rpow_path (ε / (1 - α)) h3 d3
  have a4 := nk_rpow_path (-ε / (1 - α)) h4 d4
  have a5 := (((hasDerivAt_const (0 : ℝ) θ).mul a3).mul a2).add
    ((hasDerivAt_const (0 : ℝ) (1 - θ)).mul a4)
  have a6 : HasDerivAt Δ _ 0 := a5.congr_of_eventuallyEq (Filter.Eventually.of_forall h)
  have hu := a1.unique a6
  simp only [Pi.mul_apply, e1, e2, e3, e4, Real.one_rpow] at hu
  linear_combination hu

/-- Miao, p. 625: with (19.19) (`q = θπ/(1 − θ)`, `θ ≠ 1`), the log-linear (19.17) is
`Δ̂ = θΔ̂₋`. -/
theorem nk_loglin_dispersion {θ ε α dh dmh pih qh : ℝ} (hθ : θ ≠ 1)
    (h17 : dh = θ * dmh + ε / (1 - α) * (θ * pih - (1 - θ) * qh))
    (h19 : qh = θ / (1 - θ) * pih) : dh = θ * dmh := by
  have : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  rw [h17, h19]
  field_simp
  ring

/-- Miao, p. 626: starting from the steady state (`Δ̂_{−1} = 0`), `Δ̂_t = θΔ̂_{t−1}` gives
`Δ̂_t = 0` for every `t`; from any `Δ̂_{−1}`, `Δ̂_t = θ^{t+1}Δ̂_{−1}`. -/
theorem nk_dispersion_zero {θ : ℝ} {dh : ℕ → ℝ} (h : ∀ t, dh (t + 1) = θ * dh t) :
    (∀ t, dh t = θ ^ t * dh 0) ∧ (dh 0 = 0 → ∀ t, dh t = 0) := by
  have h1 : ∀ t, dh t = θ ^ t * dh 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [h n, ih, pow_succ]; ring
  exact ⟨h1, fun h0 t => by rw [h1 t, h0, mul_zero]⟩

/-- Miao, pp. 625–626: with `Δ̂ = 0`, the log-linear (19.16) is `Ŷ = Â + (1 − α)N̂`. -/
theorem nk_loglin_output {α yh ah nh dh : ℝ} (h16 : yh = ah + (1 - α) * nh + (α - 1) * dh)
    (hd : dh = 0) : yh = ah + (1 - α) * nh := by
  rw [h16, hd, mul_zero, add_zero]

/-- Miao, p. 626: log-linearising (19.18). If
`Y^f(s) = ((1 − α)/(μχ))^{(1−α)/D}A(s)^{(1+ν)/D}` for every `s`, `D = γ(1 − α) + α + ν`, then
`Ŷ^f = ((1 + ν)/D)Â`. -/
theorem nk_loglin_19_18 {γ ν α χ mu : ℝ} {Yf A : ℝ → ℝ} {yfh ah : ℝ} (hk : 0 < (1 - α) / (mu * χ))
    (h2 : ∀ s, 0 < A s)
    (d1 : HasDerivAt (fun s => Real.log (Yf s)) yfh 0)
    (d2 : HasDerivAt (fun s => Real.log (A s)) ah 0)
    (h : ∀ s, Yf s = ((1 - α) / (mu * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν)) *
      A s ^ ((1 + ν) / (γ * (1 - α) + α + ν))) :
    yfh = (1 + ν) / (γ * (1 - α) + α + ν) * ah := by
  have e : (fun s => Real.log (Yf s)) = fun s =>
      Real.log (((1 - α) / (mu * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν))) +
        (1 + ν) / (γ * (1 - α) + α + ν) * Real.log (A s) := funext fun s => by
    rw [h s, Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos (h2 s) _).ne',
      Real.log_rpow (h2 s)]
  rw [e] at d1
  have hu := d1.unique ((hasDerivAt_const (0 : ℝ) _).add (d2.const_mul _))
  linarith

/-- The Euler-equation perturbation (Miao, pp. 626–627). Let `E_t` be the expectation over
finitely many successor states `j` with probabilities `q_j` (`∑q_j = 1`). If
`1 = βR(s)∑_j q_j exp(L_j(s))` for every `s` with `R(s) > 0`, `βR(0) = 1`, `L_j(0) = 0`, `ln R`
having derivative `r̂` and `L_j` derivative `ℓ_j` at `0`, then `r̂ + ∑_j q_jℓ_j = 0`. -/
theorem nk_loglin_euler {n : ℕ} {β : ℝ} {q : Fin n → ℝ} {R : ℝ → ℝ} {L : Fin n → ℝ → ℝ}
    {rh : ℝ} {lh : Fin n → ℝ} (hq : ∑ j, q j = 1) (hR : ∀ s, 0 < R s) (hR0 : β * R 0 = 1)
    (hL0 : ∀ j, L j 0 = 0) (dR : HasDerivAt (fun s => Real.log (R s)) rh 0)
    (dL : ∀ j, HasDerivAt (L j) (lh j) 0)
    (h : ∀ s, 1 = β * R s * ∑ j, q j * Real.exp (L j s)) :
    rh + ∑ j, q j * lh j = 0 := by
  have aR := nk_path_deriv hR dR
  have aS : HasDerivAt (fun s => ∑ j, q j * Real.exp (L j s))
      (∑ j, q j * (Real.exp (L j 0) * lh j)) 0 :=
    HasDerivAt.fun_sum fun j _ => ((dL j).exp).const_mul (q j)
  have hd := (aR.const_mul β).mul aS
  have e : (fun s => β * R s * ∑ j, q j * Real.exp (L j s)) = fun _ => 1 := funext fun s =>
    (h s).symm
  have hd' : HasDerivAt (fun s => β * R s * ∑ j, q j * Real.exp (L j s)) 0 0 := by
    rw [e]
    exact hasDerivAt_const _ _
  have hu := hd.unique hd'
  simp only [hL0, Real.exp_zero, one_mul, mul_one, hq] at hu
  have : β * (R 0 * rh) + β * R 0 * ∑ j, q j * lh j = rh + ∑ j, q j * lh j := by
    rw [show β * (R 0 * rh) = (β * R 0) * rh by ring, hR0, one_mul, one_mul]
  linarith

/-- **(19.26)** (Miao, p. 626): log-linearising the Euler equation (19.3) with `C = Y`. With
finitely many successor states `j` (probabilities `q_j`), positive paths `Y(s), Y_j(s), P(s),
P_j(s), R(s) = 1 + i(s)` with `Y_j(0) = Y(0)`, `P_j(0) = P(0)`, `βR(0) = 1`, and
`1 = βR(s)∑_j q_j(Y_j(s)/Y(s))^{−γ}P(s)/P_j(s)` for every `s` (`γ ≠ 0`):
`ŷ = ∑_j q_jŷ_j − γ⁻¹(ı̂ − ∑_j q_jπ_j)`, `π_j = p̂_j − p̂`, `ı̂ = d ln(1 + i)`. -/
theorem eq_19_26 {n : ℕ} {β γ : ℝ} (hγ : γ ≠ 0) {q : Fin n → ℝ} {R Y P : ℝ → ℝ}
    {Yj Pj : Fin n → ℝ → ℝ} {ih yh ph : ℝ} {yjh pjh : Fin n → ℝ} (hq : ∑ j, q j = 1)
    (hR : ∀ s, 0 < R s) (hY : ∀ s, 0 < Y s) (hP : ∀ s, 0 < P s) (hYj : ∀ j s, 0 < Yj j s)
    (hPj : ∀ j s, 0 < Pj j s) (hR0 : β * R 0 = 1) (hY0 : ∀ j, Yj j 0 = Y 0)
    (hP0 : ∀ j, Pj j 0 = P 0)
    (dR : HasDerivAt (fun s => Real.log (R s)) ih 0)
    (dY : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (dP : HasDerivAt (fun s => Real.log (P s)) ph 0)
    (dYj : ∀ j, HasDerivAt (fun s => Real.log (Yj j s)) (yjh j) 0)
    (dPj : ∀ j, HasDerivAt (fun s => Real.log (Pj j s)) (pjh j) 0)
    (h : ∀ s, 1 = β * R s * ∑ j, q j * ((Yj j s / Y s) ^ (-γ) * (P s / Pj j s))) :
    yh = ∑ j, q j * yjh j - γ⁻¹ * (ih - ∑ j, q j * (pjh j - ph)) := by
  set L : Fin n → ℝ → ℝ := fun j s =>
    -γ * (Real.log (Yj j s) - Real.log (Y s)) + (Real.log (P s) - Real.log (Pj j s))
  have hexp : ∀ j s, (Yj j s / Y s) ^ (-γ) * (P s / Pj j s) = Real.exp (L j s) := fun j s => by
    simp only [L]
    rw [Real.exp_add, Real.rpow_def_of_pos (div_pos (hYj j s) (hY s)),
      Real.log_div (hYj j s).ne' (hY s).ne', ← Real.log_div (hP s).ne' (hPj j s).ne',
      Real.exp_log (div_pos (hP s) (hPj j s)), mul_comm (-γ)]
  have hu := nk_loglin_euler (L := L) (lh := fun j => -γ * (yjh j - yh) + (ph - pjh j)) hq hR
    hR0 (fun j => by simp [L, hY0, hP0]) dR
    (fun j => ((((dYj j).sub dY).const_mul (-γ)).add (dP.sub (dPj j))))
    (fun s => by rw [h s]; simp only [hexp])
  have e1 : ∑ j, q j * (-γ * (yjh j - yh) + (ph - pjh j)) =
      -γ * (∑ j, q j * yjh j) + γ * yh - ∑ j, q j * (pjh j - ph) := by
    have : ∑ j, q j * (-γ * (yjh j - yh) + (ph - pjh j)) =
        ∑ j, (-γ * (q j * yjh j) + γ * yh * q j - q j * (pjh j - ph)) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hq]
    ring
  rw [e1] at hu
  field_simp
  linear_combination hu

/-- Miao, p. 627: the natural rate of interest. With finitely many successor states, if
`1 = βR^n(s)∑_j q_j(Y^f_j(s)/Y^f(s))^{−γ}` for every `s` (`R^n = 1 + r^n`, positive paths,
`Y^f_j(0) = Y^f(0)`, `βR^n(0) = 1`), then `r̂^n = γ(∑_j q_jŷ^f_j − ŷ^f)`, i.e.
`ln(1 + r^n) = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)` to first order, which is (19.27):
`ŷ^f = ∑_j q_jŷ^f_j − γ⁻¹r̂^n`. -/
theorem nk_loglin_natural_rate {n : ℕ} {β γ : ℝ} (hγ : γ ≠ 0) {q : Fin n → ℝ} {R Y : ℝ → ℝ}
    {Yj : Fin n → ℝ → ℝ} {rh yh : ℝ} {yjh : Fin n → ℝ} (hq : ∑ j, q j = 1)
    (hR : ∀ s, 0 < R s) (hY : ∀ s, 0 < Y s) (hYj : ∀ j s, 0 < Yj j s) (hR0 : β * R 0 = 1)
    (hY0 : ∀ j, Yj j 0 = Y 0)
    (dR : HasDerivAt (fun s => Real.log (R s)) rh 0)
    (dY : HasDerivAt (fun s => Real.log (Y s)) yh 0)
    (dYj : ∀ j, HasDerivAt (fun s => Real.log (Yj j s)) (yjh j) 0)
    (h : ∀ s, 1 = β * R s * ∑ j, q j * (Yj j s / Y s) ^ (-γ)) :
    rh = γ * (∑ j, q j * yjh j - yh) ∧ yh = ∑ j, q j * yjh j - γ⁻¹ * rh := by
  have h' := eq_19_26 (P := fun _ => 1) (Pj := fun _ _ => 1) (ph := 0) (pjh := fun _ => 0)
    hγ hq hR hY (fun _ => one_pos) hYj (fun _ _ => one_pos) hR0 hY0 (fun _ => rfl) dR dY
    (by simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)) dYj
    (fun _ => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ))
    (fun s => by simpa using h s)
  simp only [sub_zero, mul_zero, Finset.sum_const_zero] at h'
  refine ⟨?_, h'⟩
  rw [h']
  field_simp
  ring

/-- **(19.29)** (Miao, p. 627): the Taylor rule (19.14) in logs is exactly
`ln(1 + i_t) = −ln β + φ_π ln Π_t + φ_y ln(Y_t/Y^f_t) + v_t` (`β > 0`, `1 + i_t > 0`). -/
theorem eq_19_29 {φπ φy β i Pt Ptm1 Y Yf v : ℝ} (hβ : 0 < β) (hi : 0 < 1 + i) :
    nk_taylorRule φπ φy β i Pt Ptm1 Y Yf v ↔
      Real.log (1 + i) = -Real.log β + φπ * Real.log (Pt / Ptm1) + φy * Real.log (Y / Yf) + v := by
  rw [nk_taylorRule, show (1 : ℝ) + (1 / β - 1) = 1 / β by ring,
    Real.log_div hi.ne' (by positivity), one_div, Real.log_inv]
  constructor <;> intro h <;> linarith

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The New Keynesian Phillips curve and the IS curve (Miao §19.1.7)

Miao, §19.1.7, pp. 624–627. The log-linear variables are random variables in a normed space
`V` with conditional expectations `E_t` (a `CondExpSystem`, as in Chapter 2); `δ = βθ`,
`|δ| < 1`. Present values are `PV_t(g) = ∑_k δ^kE_tg_{t+k}` (`nk_pv`), which equals
`E_t∑_k δ^kg_{t+k}` since `E_t` is continuous.

* (19.20): the "simplifying" step from the log-linearised (19.11) (`eq_19_20`).
* Plugging in (19.21): `P̂*_t(1 + b)/(1 − βθ) = E_t∑_k θ^kβ^k((1 + b)P̂_{t+k} + MĈ_{t+k})`
  (`nk_reset_plugged`); its recursive form
  `P̂*_t = (1 − βθ)(MĈ_t/(1 + b) + P̂_t) + βθE_tP̂*_{t+1}` (`nk_reset_recursive`, from the
  present-value recursion `nk_pv_rec`); the same for `q_t = P̂*_t − P̂_t` (`nk_q_recursive`).
* With (19.19): `π_t = βE_tπ_{t+1} + ((1 − βθ)(1 − θ)/(θ(1 + b)))MĈ_t` (`nk_pc_mc`).
* (19.23) (`eq_19_23`); with `Ŷ = Â + (1 − α)N̂` and the log-linear (19.18),
  `MĈ = ((ν + α + γ(1 − α))/(1 − α))(Ŷ − Ŷ^f)` (`nk_mc_gap`).
* (19.24), the New Keynesian Phillips curve, with the slope κ of (19.25) in both printed forms
  (`eq_19_24`, `nk_kappa`, `eq_19_25`, `nk_kappa_pos`).
* (19.27) from the definition of the natural rate (`eq_19_27`) and (19.28), the intertemporal
  IS curve (`eq_19_28`). The constant `ln β` is `ln β · 𝟙` for a fixed `F_0`-measurable unit
  `𝟙 ∈ V` (the constant random variable `1`).
-/

namespace Miao.NewKeynesian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The present value `PV_t(g) = ∑_k δ^kE_tg_{t+k}` (Miao, p. 621 with weights `(θβ)^k`). -/
noncomputable def nk_pv (E : CondExpSystem ℝ V) (δ : ℝ) (g : ℕ → V) (t : ℕ) : V :=
  ∑' k : ℕ, δ ^ k • E.E t (g (t + k))

omit [NormedSpace ℝ V] in
/-- A bounded sequence weighted by `δ^k`, `|δ| < 1`, is summable. -/
theorem nk_summable_geom [NormedSpace ℝ V] [CompleteSpace V] {δ : ℝ} (hδ : |δ| < 1)
    {f : ℕ → V} {C : ℝ} (hf : ∀ k, ‖f k‖ ≤ C) : Summable fun k => δ ^ k • f k :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg _) hδ).mul_right C)
    fun k => by
      rw [norm_smul, norm_pow, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf k) (pow_nonneg (abs_nonneg _) _)

/-- `∑_k δ^k • v = (1 − δ)⁻¹ • v` for `|δ| < 1`. -/
theorem nk_tsum_geom_smul {δ : ℝ} (hδ : |δ| < 1) (v : V) :
    ∑' k : ℕ, δ ^ k • v = (1 - δ)⁻¹ • v := by
  rw [(summable_geometric_of_abs_lt_one hδ).tsum_smul_const, tsum_geometric_of_abs_lt_one hδ]

/-- The present-value recursion (Miao, p. 625): for adapted bounded `g`,
`PV_t(g) = g_t + δE_tPV_{t+1}(g)`. -/
theorem nk_pv_rec [CompleteSpace V] (E : CondExpSystem ℝ V) {δ : ℝ} (hδ : |δ| < 1)
    {g : ℕ → V} {C : ℝ} (hg : ∀ t, ‖g t‖ ≤ C) (hga : ∀ t, E.E t (g t) = g t) (t : ℕ) :
    nk_pv E δ g t = g t + δ • E.E t (nk_pv E δ g (t + 1)) := by
  have hb : ∀ s k, ‖E.E s (g (s + k))‖ ≤ C := fun s k => (E.norm_apply_le _ _).trans (hg _)
  have hs := nk_summable_geom hδ (hb t)
  have hs1 := nk_summable_geom hδ (hb (t + 1))
  simp only [nk_pv]
  rw [(E.E t).map_tsum hs1, hs.tsum_eq_zero_add]
  simp only [map_smul, E.tower_le_apply (Nat.le_succ t), pow_zero, one_smul, add_zero, hga t]
  rw [← (nk_summable_geom hδ (fun k => (E.norm_apply_le t _).trans
    (hg (t + 1 + k)))).tsum_const_smul δ]
  congr 1
  refine tsum_congr fun k => ?_
  rw [smul_smul, pow_succ, mul_comm, show t + (k + 1) = t + 1 + k by omega]

/-- **(19.20)** (Miao, p. 624), the simplifying step. Divide the log-linearised (19.11) by the
common steady-state factor (`nk_loglin_reset_terms`): if for every `t`
`∑_k δ^kE_t(P̂*_t + (1 − γ)Ŷ_{t+k} + (ε − 1)P̂_{t+k}) =
 ∑_k δ^kE_t((1 − γ)Ŷ_{t+k} + εP̂_{t+k} + MĈ_{t+k|t})` with `P̂*` adapted and `Ŷ, P̂, MĈ`
bounded, then `P̂*_t/(1 − βθ) = ∑_k δ^kE_t(P̂_{t+k} + MĈ_{t+k|t})`, `δ = βθ`. -/
theorem eq_19_20 [CompleteSpace V] (E : CondExpSystem ℝ V) {δ γ ε : ℝ} (hδ : |δ| < 1)
    {ps y p : ℕ → V} {mkt : ℕ → ℕ → V} {C : ℝ} (hy : ∀ t, ‖y t‖ ≤ C) (hp : ∀ t, ‖p t‖ ≤ C)
    (hm : ∀ t k, ‖mkt t k‖ ≤ C) (hpsa : ∀ t, E.E t (ps t) = ps t)
    (hlin : ∀ t, ∑' k : ℕ, δ ^ k • E.E t (ps t + (1 - γ) • y (t + k) + (ε - 1) • p (t + k)) =
      ∑' k : ℕ, δ ^ k • E.E t ((1 - γ) • y (t + k) + ε • p (t + k) + mkt t k)) (t : ℕ) :
    (1 - δ)⁻¹ • ps t = ∑' k : ℕ, δ ^ k • E.E t (p (t + k) + mkt t k) := by
  set A : ℕ → V := fun k => δ ^ k • E.E t ((1 - γ) • y (t + k) + (ε - 1) • p (t + k))
  set B : ℕ → V := fun k => δ ^ k • E.E t (p (t + k) + mkt t k)
  have hA : Summable A := nk_summable_geom hδ (C := (|1 - γ| * C + |ε - 1| * C)) fun k => by
    refine (E.norm_apply_le _ _).trans ((norm_add_le _ _).trans (add_le_add ?_ ?_)) <;>
      rw [norm_smul, Real.norm_eq_abs] <;> gcongr <;> simp_all
  have hB : Summable B := nk_summable_geom hδ (C := C + C) fun k =>
    (E.norm_apply_le _ _).trans ((norm_add_le _ _).trans (add_le_add (hp _) (hm _ _)))
  have hG : Summable fun k : ℕ => δ ^ k • ps t := nk_summable_geom hδ (C := ‖ps t‖) fun _ => le_rfl
  have hl : ∀ k, δ ^ k • E.E t (ps t + (1 - γ) • y (t + k) + (ε - 1) • p (t + k)) =
      δ ^ k • ps t + A k := fun k => by
    simp only [A, map_add, map_smul, hpsa t, add_assoc, smul_add]
  have hr : ∀ k, δ ^ k • E.E t ((1 - γ) • y (t + k) + ε • p (t + k) + mkt t k) =
      A k + B k := fun k => by
    simp only [A, B, map_add, map_smul, ← smul_add]
    congr 1
    module
  have h := hlin t
  simp only [hl, hr] at h
  rw [hG.tsum_add hA, hA.tsum_add hB, add_comm, add_left_cancel_iff, nk_tsum_geom_smul hδ] at h
  exact h

/-- Miao, p. 625: plugging (19.21) `MĈ_{t+k|t} = MĈ_{t+k} − b(P̂*_t − P̂_{t+k})` into (19.20):
`(1 + b)(1 − βθ)⁻¹P̂*_t = ∑_k δ^kE_t((1 + b)P̂_{t+k} + MĈ_{t+k})`. -/
theorem nk_reset_plugged [CompleteSpace V] (E : CondExpSystem ℝ V) {δ b : ℝ} (hδ : |δ| < 1)
    {ps p m : ℕ → V} {C : ℝ} (hp : ∀ t, ‖p t‖ ≤ C) (hmC : ∀ t, ‖m t‖ ≤ C)
    (hpsa : ∀ t, E.E t (ps t) = ps t) (t : ℕ)
    (h20 : (1 - δ)⁻¹ • ps t =
      ∑' k : ℕ, δ ^ k • E.E t (p (t + k) + (m (t + k) - b • (ps t - p (t + k))))) :
    (1 + b) • (1 - δ)⁻¹ • ps t = nk_pv E δ (fun s => (1 + b) • p s + m s) t := by
  set B : ℕ → V := fun k => δ ^ k • E.E t ((1 + b) • p (t + k) + m (t + k))
  have hB : Summable B := nk_summable_geom hδ (C := |1 + b| * C + C) fun k => by
    refine (E.norm_apply_le _ _).trans ((norm_add_le _ _).trans (add_le_add ?_ (hmC _)))
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
  have hG : Summable fun k : ℕ => δ ^ k • (-(b • ps t)) :=
    nk_summable_geom hδ (C := ‖-(b • ps t)‖) fun _ => le_rfl
  have he : ∀ k, δ ^ k • E.E t (p (t + k) + (m (t + k) - b • (ps t - p (t + k)))) =
      B k + δ ^ k • (-(b • ps t)) := fun k => by
    simp only [B, map_add, map_sub, map_smul, hpsa t, ← smul_add]
    congr 1
    module
  simp only [he] at h20
  rw [hB.tsum_add hG, nk_tsum_geom_smul hδ] at h20
  simp only [nk_pv]
  change (1 + b) • (1 - δ)⁻¹ • ps t = ∑' k, B k
  rw [smul_comm]
  have : ∑' k, B k = (1 - δ)⁻¹ • ps t + (1 - δ)⁻¹ • (b • ps t) := by
    rw [h20]
    module
  rw [this]
  module

/-- Miao, p. 625: the recursive form of the reset price,
`P̂*_t = (1 − βθ)(MĈ_t/(1 + b) + P̂_t) + βθE_tP̂*_{t+1}` (`δ = βθ`, `1 + b ≠ 0`, `P̂`, `MĈ`
adapted and bounded). -/
theorem nk_reset_recursive [CompleteSpace V] (E : CondExpSystem ℝ V) {δ b : ℝ} (hδ : |δ| < 1)
    (hb : 1 + b ≠ 0) {ps p m : ℕ → V} {C : ℝ} (hp : ∀ t, ‖p t‖ ≤ C) (hmC : ∀ t, ‖m t‖ ≤ C)
    (hpa : ∀ t, E.E t (p t) = p t) (hma : ∀ t, E.E t (m t) = m t)
    (hpv : ∀ t, (1 + b) • (1 - δ)⁻¹ • ps t = nk_pv E δ (fun s => (1 + b) • p s + m s) t)
    (t : ℕ) : ps t = (1 - δ) • ((1 + b)⁻¹ • m t + p t) + δ • E.E t (ps (t + 1)) := by
  have hδ1 : 1 - δ ≠ 0 := by
    have := (abs_lt.1 hδ).2
    linarith
  have hgC : ∀ s, ‖(1 + b) • p s + m s‖ ≤ |1 + b| * C + C := fun s => by
    have h1 : ‖(1 + b) • p s‖ ≤ |1 + b| * C := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hp s) (abs_nonneg _)
    exact (norm_add_le _ _).trans (add_le_add h1 (hmC s))
  have hrec := nk_pv_rec E hδ hgC (fun s => by simp only [map_add, map_smul, hpa, hma]) t
  rw [← hpv t, ← hpv (t + 1)] at hrec
  simp only [map_smul] at hrec
  have h2 : ps t = ((1 + b)⁻¹ * (1 - δ)) • ((1 + b) • p t + m t +
      δ • ((1 + b) • (1 - δ)⁻¹ • E.E t (ps (t + 1)))) := by
    rw [← hrec, smul_smul, smul_smul]
    have : (1 + b)⁻¹ * (1 - δ) * (1 + b) * (1 - δ)⁻¹ = 1 := by field_simp
    rw [this, one_smul]
  rw [h2]
  simp only [smul_add, smul_smul]
  match_scalars <;> field_simp

/-- Miao, p. 625: with `q_t = P̂*_t − P̂_t` and `P̂` adapted,
`q_t = ((1 − βθ)/(1 + b))MĈ_t + βθE_t(q_{t+1} + P̂_{t+1} − P̂_t)`. -/
theorem nk_q_recursive (E : CondExpSystem ℝ V) {δ b : ℝ} {ps p m : ℕ → V}
    (hpa : ∀ t, E.E t (p t) = p t) (t : ℕ)
    (h : ps t = (1 - δ) • ((1 + b)⁻¹ • m t + p t) + δ • E.E t (ps (t + 1))) :
    ps t - p t = ((1 - δ) / (1 + b)) • m t +
      δ • E.E t ((ps (t + 1) - p (t + 1)) + p (t + 1) - p t) := by
  simp only [map_sub, hpa t, sub_add_cancel]
  rw [h]
  match_scalars <;> ring

/-- Miao, p. 625: with (19.19) `q_t = θπ_t/(1 − θ)` and `π_{t+1} = P̂_{t+1} − P̂_t`, the
`q`-recursion gives `π_t = βE_tπ_{t+1} + ((1 − βθ)(1 − θ)/(θ(1 + b)))MĈ_t`. -/
theorem nk_pc_mc (E : CondExpSystem ℝ V) {β θ b : ℝ} (hθ0 : θ ≠ 0) (hθ1 : θ ≠ 1)
    {q p m pi : ℕ → V} (t : ℕ) (hq : ∀ s, q s = (θ / (1 - θ)) • pi s)
    (hpi : pi (t + 1) = p (t + 1) - p t)
    (h : q t = ((1 - β * θ) / (1 + b)) • m t +
      (β * θ) • E.E t (q (t + 1) + p (t + 1) - p t)) :
    pi t = β • E.E t (pi (t + 1)) + ((1 - β * θ) * (1 - θ) / (θ * (1 + b))) • m t := by
  have h1 : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ1)
  rw [hq t, hq (t + 1), add_sub_assoc, ← hpi] at h
  have e : (θ / (1 - θ)) • pi (t + 1) + pi (t + 1) = (1 - θ)⁻¹ • pi (t + 1) := by
    match_scalars
    field_simp
    ring
  rw [e, map_smul] at h
  have h2 : pi t = ((1 - θ) / θ) • ((θ / (1 - θ)) • pi t) := by
    rw [smul_smul, div_mul_div_comm, mul_comm (1 - θ), div_self (mul_ne_zero hθ0 h1), one_smul]
  rw [h2, h]
  match_scalars <;> field_simp

/-- **(19.23)** (Miao, p. 625): from the log-linear (19.9), `MĈ = Ŵ − P̂ + (α/(1 − α))Ŷ −
(1/(1 − α))Â` (`nk_loglin_MC`), the log-linear (19.2), `Ŵ − P̂ = νN̂ + γĈ`
(`nk_loglin_19_2`), and `Ĉ = Ŷ`: `MĈ = νN̂ + γŶ + (α/(1 − α))Ŷ − (1/(1 − α))Â`. -/
theorem eq_19_23 {α ν γ : ℝ} {m w n c y a : V} (hm : m = w + (α / (1 - α)) • y - (1 / (1 - α)) • a)
    (hw : w = ν • n + γ • c) (hc : c = y) :
    m = ν • n + γ • y + (α / (1 - α)) • y - (1 / (1 - α)) • a := by
  rw [hm, hw, hc]

/-- Miao, p. 626: with `Ŷ = Â + (1 − α)N̂` (`nk_loglin_output`) and `Ŷ^f = ((1 + ν)/D)Â`
(`nk_loglin_19_18`), `D = γ(1 − α) + α + ν ≠ 0`, `α ≠ 1`, (19.23) becomes
`MĈ = (D/(1 − α))Ŷ − ((ν + 1)/(1 − α))Â = (D/(1 − α))(Ŷ − Ŷ^f)`. -/
theorem nk_mc_gap {α ν γ : ℝ} (hα : α ≠ 1) (hD : γ * (1 - α) + α + ν ≠ 0) {m n y a yf : V}
    (h23 : m = ν • n + γ • y + (α / (1 - α)) • y - (1 / (1 - α)) • a)
    (hy : y = a + (1 - α) • n) (hyf : yf = ((1 + ν) / (γ * (1 - α) + α + ν)) • a) :
    m = ((ν + α + γ * (1 - α)) / (1 - α)) • y - ((ν + 1) / (1 - α)) • a ∧
      m = ((ν + α + γ * (1 - α)) / (1 - α)) • (y - yf) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn : n = (1 - α)⁻¹ • (y - a) := by
    rw [hy]
    match_scalars
    · field_simp
    · ring
  have e1 : m = ((ν + α + γ * (1 - α)) / (1 - α)) • y - ((ν + 1) / (1 - α)) • a := by
    rw [h23, hn]
    match_scalars <;> field_simp <;> ring
  refine ⟨e1, ?_⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = γ * (1 - α) + α + ν := ⟨_, rfl⟩
  rw [← hDdef] at hyf hD
  rw [e1, hyf, show ν + α + γ * (1 - α) = D by rw [hDdef]; ring]
  match_scalars
  · rfl
  · field_simp
    ring

/-- **(19.25)** (Miao, p. 626): the slope of the Phillips curve,
`κ = ((1 − βθ)(1 − θ)/(θ(1 + b)))·((ν + α + γ(1 − α))/(1 − α))`, `b = εα/(1 − α)`. -/
noncomputable def nk_kappa (β θ γ ν α ε : ℝ) : ℝ :=
  (1 - β * θ) * (1 - θ) / (θ * (1 + nk_b ε α)) * ((ν + α + γ * (1 - α)) / (1 - α))

/-- **(19.25)** (Miao, p. 626), the second printed form:
`κ = (1 − βθ)(1 − θ)(ν + α + γ(1 − α))/(θ(1 − α + εα))` for `α < 1`, `ε ≥ 0`. -/
theorem eq_19_25 {β θ γ ν α ε : ℝ} (hα : α < 1) (hε : 0 ≤ ε) (hα0 : 0 ≤ α) :
    nk_kappa β θ γ ν α ε =
      (1 - β * θ) * (1 - θ) * (ν + α + γ * (1 - α)) / (θ * (1 - α + ε * α)) := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have h2 : 0 < 1 - α + ε * α := by nlinarith
  have h3 : (1 : ℝ) + nk_b ε α = (1 - α + ε * α) / (1 - α) := by
    rw [nk_b]
    field_simp
  rw [nk_kappa, h3]
  by_cases hθ : θ = 0
  · simp [hθ]
  · field_simp

/-- Miao, p. 626: `κ > 0` for `0 < θ < 1`, `0 < β < 1` (`βθ < 1`), `0 ≤ α < 1`, `ε ≥ 0` and
`ν, γ ≥ 0` with `ν + α + γ(1 − α) > 0` (e.g. `ν, γ > 0`). -/
theorem nk_kappa_pos {β θ γ ν α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 ≤ ε) (hD : 0 < ν + α + γ * (1 - α)) :
    0 < nk_kappa β θ γ ν α ε := by
  rw [eq_19_25 hα1 hε hα0]
  have h2 : 0 < 1 - α + ε * α := by nlinarith
  have : 0 < 1 - β * θ := by linarith
  have : 0 < 1 - θ := by linarith
  positivity

/-- **(19.24)** (Miao, p. 626), the New Keynesian Phillips curve `π_t = βE_tπ_{t+1} + κx_t`,
`x_t = Ŷ_t − Ŷ^f_t`, from `π_t = βE_tπ_{t+1} + ((1 − βθ)(1 − θ)/(θ(1 + b)))MĈ_t`
(`nk_pc_mc`) and `MĈ_t = ((ν + α + γ(1 − α))/(1 − α))x_t` (`nk_mc_gap`). -/
theorem eq_19_24 (E : CondExpSystem ℝ V) {β θ γ ν α ε : ℝ} {pi m x : ℕ → V} (t : ℕ)
    (hpc : pi t = β • E.E t (pi (t + 1)) +
      ((1 - β * θ) * (1 - θ) / (θ * (1 + nk_b ε α))) • m t)
    (hm : m t = ((ν + α + γ * (1 - α)) / (1 - α)) • x t) :
    pi t = β • E.E t (pi (t + 1)) + nk_kappa β θ γ ν α ε • x t := by
  rw [hpc, hm, smul_smul, nk_kappa]

/-- **(19.27)** (Miao, p. 627): the natural rate `r^n_t = −ln β + γ(E_tŶ^f_{t+1} − Ŷ^f_t)` (in
log-linear form, `𝟙` the constant random variable) gives
`Ŷ^f_t = E_tŶ^f_{t+1} − γ⁻¹(r^n_t + ln β)` (`γ ≠ 0`). -/
theorem eq_19_27 (E : CondExpSystem ℝ V) {β γ : ℝ} (hγ : γ ≠ 0) {one : V} {yf rn : ℕ → V}
    (t : ℕ) (h : rn t = (-Real.log β) • one + γ • (E.E t (yf (t + 1)) - yf t)) :
    yf t = E.E t (yf (t + 1)) - γ⁻¹ • (rn t + Real.log β • one) := by
  rw [h]
  match_scalars <;> field_simp <;> ring

/-- **(19.28)** (Miao, p. 627), the intertemporal IS curve: from (19.26)
`Ŷ_t = E_tŶ_{t+1} − γ⁻¹(i_t + ln β − E_tπ_{t+1})` and (19.27), the output gap
`x_t = Ŷ_t − Ŷ^f_t` satisfies `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1} − r^n_t)`. -/
theorem eq_19_28 (E : CondExpSystem ℝ V) {β γ : ℝ} {one : V} {y yf i pi rn : ℕ → V} (t : ℕ)
    (h26 : y t = E.E t (y (t + 1)) - γ⁻¹ • (i t + Real.log β • one - E.E t (pi (t + 1))))
    (h27 : yf t = E.E t (yf (t + 1)) - γ⁻¹ • (rn t + Real.log β • one)) :
    y t - yf t = E.E t (y (t + 1) - yf (t + 1)) - γ⁻¹ • (i t - E.E t (pi (t + 1)) - rn t) := by
  rw [h26, h27, map_sub]
  module

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Determinacy of the basic DNK model: Exercise 19.1 (Bullard–Mitra)

Miao, §19.1.7, p. 627 ((19.24), (19.28), (19.29)), condition (19.31), p. 635, and Exercise 1 of
§19.5, p. 668. The log-linear system is, for random variables in a Banach space `V` with
conditional expectations `E_t` and the constant random variable `𝟙` (adapted, nonzero):

`π_t = βE_tπ_{t+1} + κx_t`, `x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1} − r^n_t)`,
`i_t = −ln β + φ_ππ_t + φ_yx_t + v_t` (`nk_dnkSystem`).

* Substituting the Taylor rule, the system is the jump-only system of Exercise 2.2 with
  `ε_t = v_t − r^n_t − ln β` (`nk_dnk_iff`); the proof of Exercise 19.1 uses the Chapter 2
  Blanchard–Kahn results for it (`ex_2_2_suff`, `nk_jump2_nonunique`, `nk_bothOut_WT`).
* **Exercise 19.1** (`ex_19_1`): for `κ, γ > 0`, `0 < β < 1` and `φ_π, φ_y ≥ 0`, the model has a
  unique stable (bounded, adapted) equilibrium for all bounded adapted shocks `v`, `r^n`
  (`nk_dnkDeterminate`) iff (19.31) `κ(φ_π − 1) + (1 − β)φ_y > 0`.
* For `φ_y ≥ 0` and any `φ_π` the exact condition adds the branch
  `κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0` (`ex_19_1_exact`); without `φ_π ≥ 0`, (19.31) is not
  necessary (`ex_19_1_not_necessary`: `κ = γ = 1`, `β = 1/2`, `φ_π = −5`, `φ_y = 0`). The book
  states no sign restriction; Bullard and Mitra assume nonnegative coefficients.
* With the structural slope κ of (19.25) (`ex_19_1_structural`).
* Figures 19.1–19.2 (qualitative). For an AR(1) monetary shock (`E_tv_{t+1} = ρv_t`,
  `0 ≤ ρ < 1`) the unique equilibrium is `x_t = −(1 − βρ)Λv_t`, `π_t = −κΛv_t` with
  `Λ = 1/((1 − βρ)(γ(1 − ρ) + φ_y) + κ(φ_π − ρ)) > 0` under (19.31): the output gap and
  inflation fall after a positive shock, the real rate `i_t − E_tπ_{t+1}` rises, and rises by
  `ρκΛv_t` more than the nominal rate (`nk_fig_19_1`). For an AR(1) natural-rate shock
  `r̂^n` the output gap, inflation and the nominal rate rise and the real rate rises by a
  fraction in `(0, 1)` of the shock (`nk_fig_19_2`). The plotted magnitudes (Dynare) are not
  formalised.
-/

namespace Miao.NewKeynesian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The log-linear basic DNK model (19.24), (19.28), (19.29) (Miao, p. 627). -/
def nk_dnkSystem (E : CondExpSystem ℝ V) (β γ κ φπ φy : ℝ) (one : V) (v rn x pi i : ℕ → V) :
    Prop :=
  ∀ t, pi t = β • E.E t (pi (t + 1)) + κ • x t ∧
    x t = E.E t (x (t + 1)) - γ⁻¹ • (i t - E.E t (pi (t + 1)) - rn t) ∧
    i t = (-Real.log β) • one + φπ • pi t + φy • x t + v t

/-- Exercise 19.1 (Miao, p. 668): a unique stable equilibrium for all bounded adapted shocks
`v` and `r^n`: exactly one triple `(x, π, i)` of adapted bounded processes solves the model. -/
def nk_dnkDeterminate (E : CondExpSystem ℝ V) (β γ κ φπ φy : ℝ) (one : V) : Prop :=
  ∀ v rn : ℕ → V, sre_IsBounded v → sre_IsBounded rn → sre_IsAdapted E v →
    sre_IsAdapted E rn →
    ∃! z : (ℕ → V) × (ℕ → V) × (ℕ → V), nk_dnkSystem E β γ κ φπ φy one v rn z.1 z.2.1 z.2.2 ∧
      sre_IsAdapted E z.1 ∧ sre_IsAdapted E z.2.1 ∧ sre_IsAdapted E z.2.2 ∧
      sre_IsBounded z.1 ∧ sre_IsBounded z.2.1 ∧ sre_IsBounded z.2.2

/-- Miao, p. 627: substituting the Taylor rule (19.29) into (19.28), the model is the
Exercise 2.2 system `nkTaylorEqm` for the state `(x_t, π_t)` with `ε_t = v_t − r^n_t − ln β`,
`ε^x = 0`, together with the rule determining `i_t`. -/
theorem nk_dnk_iff (E : CondExpSystem ℝ V) (β γ κ φπ φy : ℝ) (one : V) (v rn x pi i : ℕ → V) :
    nk_dnkSystem E β γ κ φπ φy one v rn x pi i ↔
      nkTaylorEqm E κ β γ φπ φy (fun t => v t - rn t - Real.log β • one) (fun _ => 0)
          (fun t => ![x t, pi t]) ∧
        ∀ t, i t = (-Real.log β) • one + φπ • pi t + φy • x t + v t := by
  simp only [nk_dnkSystem, nkTaylorEqm, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
  constructor
  · intro h
    refine ⟨fun t => ⟨?_, ?_⟩, fun t => (h t).2.2⟩
    · rw [(h t).1, add_comm]
    · obtain ⟨-, h2, h3⟩ := h t
      refine h2.trans ?_
      rw [h3]
      congr 2
      module
  · rintro ⟨h, hi⟩ t
    refine ⟨by rw [(h t).1, add_comm], (h t).2.trans ?_, hi t⟩
    rw [hi t]
    congr 2
    module

omit [NormedSpace ℝ V] in
/-- Two bounded processes form a stable pair. -/
theorem nk_pair_stable {x pi : ℕ → V} (hx : sre_IsBounded x) (hp : sre_IsBounded pi) :
    IsStableProc (fun t => ![x t, pi t]) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  refine ⟨|M| + |N| + 1, by positivity, fun t j => ?_⟩
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    linarith [hM t, le_abs_self M, abs_nonneg N]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith [hN t, le_abs_self N, abs_nonneg M]

/-- Two adapted processes form an adapted pair. -/
theorem nk_pair_adapted (E : CondExpSystem ℝ V) {x pi : ℕ → V} (hx : sre_IsAdapted E x)
    (hp : sre_IsAdapted E pi) : IsAdaptedV E (fun t => ![x t, pi t]) := fun t j => by
  fin_cases j
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, hx t]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hp t]

/-- The Taylor-rule interest rate of bounded adapted `x, π, v` is bounded and adapted. -/
theorem nk_rule_regular (E : CondExpSystem ℝ V) {β φπ φy : ℝ} {one : V}
    (hone : ∀ t, E.E t one = one) {x pi v : ℕ → V} (hx : sre_IsBounded x)
    (hp : sre_IsBounded pi) (hv : sre_IsBounded v) (hxa : sre_IsAdapted E x)
    (hpa : sre_IsAdapted E pi) (hva : sre_IsAdapted E v) :
    sre_IsAdapted E (fun t => (-Real.log β) • one + φπ • pi t + φy • x t + v t) ∧
      sre_IsBounded (fun t => (-Real.log β) • one + φπ • pi t + φy • x t + v t) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  obtain ⟨K, hK⟩ := hv
  refine ⟨fun t => by simp only [map_add, map_smul, hone, hxa t, hpa t, hva t], ?_⟩
  refine ⟨‖(-Real.log β) • one‖ + |φπ| * N + |φy| * M + K, fun t => ?_⟩
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)) (hK t))
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hN t) (abs_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)

/-- **Exercise 19.1, sufficiency** (Miao, p. 668): with `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0` and
an adapted constant `𝟙`, if `κ(φ_π − 1) + (1 − β)φ_y > 0` (or
`κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0`), the model has a unique stable equilibrium. -/
theorem ex_19_1_suff [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy)
    (hone : ∀ t, E.E t one = one)
    (hc : 0 < κ * (φπ - 1) + (1 - β) * φy ∨ κ * (1 + φπ) + (1 + β) * (2 * γ + φy) < 0) :
    nk_dnkDeterminate E β γ κ φπ φy one := by
  intro v rn hv hrn hva hrna
  have hdet := ex_2_2_suff E hκ hβ0 hβ1 hγ hφy hc
  obtain ⟨Mv, hMv⟩ := hv
  obtain ⟨Mr, hMr⟩ := hrn
  obtain ⟨X, ⟨hX, hXa, hXs⟩, hXu⟩ := hdet (fun t => v t - rn t - Real.log β • one)
    (fun _ => 0) ⟨Mv + Mr + ‖Real.log β • one‖, fun t =>
      (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (hMv t)
        (hMr t))) le_rfl)⟩ ⟨0, fun _ => by simp⟩
    (fun t => by simp only [map_sub, map_smul, hva t, hrna t, hone]) (fun _ => map_zero _)
  have hXeq : X = fun t => ![X t 0, X t 1] := funext fun t => funext fun j => by
    fin_cases j <;> rfl
  obtain ⟨C, hC⟩ := (bkS_isStableProc_iff X).1 hXs
  have hb0 : sre_IsBounded (fun t => X t 0) := ⟨C, fun t => (norm_le_pi_norm _ 0).trans (hC t)⟩
  have hb1 : sre_IsBounded (fun t => X t 1) := ⟨C, fun t => (norm_le_pi_norm _ 1).trans (hC t)⟩
  have ha0 : sre_IsAdapted E (fun t => X t 0) := fun t => hXa t 0
  have ha1 : sre_IsAdapted E (fun t => X t 1) := fun t => hXa t 1
  obtain ⟨hia, hib⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) hone hb0 hb1
    ⟨Mv, hMv⟩ ha0 ha1 hva
  refine ⟨(fun t => X t 0, fun t => X t 1,
    fun t => (-Real.log β) • one + φπ • X t 1 + φy • X t 0 + v t), ⟨?_, ha0, ha1, hia, hb0, hb1,
    hib⟩, ?_⟩
  · rw [nk_dnk_iff]
    exact ⟨hXeq ▸ hX, fun t => rfl⟩
  · rintro ⟨x', pi', i'⟩ ⟨hsys, hxa, hpa, -, hxb, hpb, -⟩
    obtain ⟨hT, hi⟩ := (nk_dnk_iff E β γ κ φπ φy one v rn x' pi' i').1 hsys
    have hu := hXu (fun t => ![x' t, pi' t]) ⟨hT, nk_pair_adapted E hxa hpa,
      nk_pair_stable hxb hpb⟩
    have h0 : x' = fun t => X t 0 := funext fun t => by
      have := congrFun (congrFun hu t) 0
      simpa using this
    have h1 : pi' = fun t => X t 1 := funext fun t => by
      have := congrFun (congrFun hu t) 1
      simpa using this
    have h2 : i' = fun t => (-Real.log β) • one + φπ • X t 1 + φy • X t 0 + v t :=
      funext fun t => by rw [hi t, h0, h1]
    rw [h0, h1, h2]

/-- **Exercise 19.1, necessity** (Miao, p. 668): with `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0` and an
adapted constant `𝟙 ≠ 0`, if the model has a unique stable equilibrium then
`κ(φ_π − 1) + (1 − β)φ_y > 0` or `κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0`. Otherwise a root of the
jump matrix inside the closed unit disc gives a nonzero stable solution of the homogeneous
system, which can be added to the equilibrium with `v = r^n = 0`. -/
theorem ex_19_1_nec (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy) (hone0 : one ≠ 0)
    (hone : ∀ t, E.E t one = one) (hdet : nk_dnkDeterminate E β γ κ φπ φy one) :
    0 < κ * (φπ - 1) + (1 - β) * φy ∨ κ * (1 + φπ) + (1 + β) * (2 * γ + φy) < 0 := by
  by_contra hc
  have hnb := fun hb => hc ((nk_bothOut_WT (δπ := φπ) hκ hβ0 hβ1 hγ hφy).1 hb)
  have hM10 : nkWT κ β γ φπ φy 1 0 ≠ 0 := by
    have e : nkWT κ β γ φπ φy 1 0 = -κ / β := by simp [nkWT]
    rw [e]
    exact div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  obtain ⟨H, hH0, hHe, hHa, hHs⟩ := nk_jump2_nonunique E (nkWT κ β γ φπ φy) hM10
    (nk_WT_trace hκ hβ0 hβ1 hγ hφy) hnb hone0 (hone 0)
  obtain ⟨⟨x, pi, i⟩, ⟨hsys, hxa, hpa, hia, hxb, hpb, hib⟩, hu⟩ :=
    hdet (fun _ => 0) (fun _ => 0) ⟨0, fun _ => by simp⟩ ⟨0, fun _ => by simp⟩
      (fun _ => map_zero _) (fun _ => map_zero _)
  obtain ⟨hT, hi⟩ := (nk_dnk_iff E β γ κ φπ φy one _ _ x pi i).1 hsys
  have hT' := (nk_taylor_iff E φπ φy hβ0.ne' _ _ _).1 hT
  set x' : ℕ → V := fun t => x t + H t 0
  set pi' : ℕ → V := fun t => pi t + H t 1
  have hXsum : ∀ t, (![x' t, pi' t] : Fin 2 → V) = ![x t, pi t] + H t := fun t =>
    funext fun j => by fin_cases j <;> rfl
  have hT2 : nkTaylorEqm E κ β γ φπ φy (fun t => (0 : V) - 0 - Real.log β • one) (fun _ => 0)
      (fun t => ![x' t, pi' t]) := by
    rw [nk_taylor_iff E φπ φy hβ0.ne']
    intro t
    have h1 := hT' t
    have h2 := hHe t
    rw [hXsum, hXsum, bkS_Evec_add, matAct_add, h1, h2]
    abel
  obtain ⟨Ma, hMa⟩ := (bkS_isStableProc_iff H).1 hHs
  have hb0 : sre_IsBounded x' := by
    obtain ⟨M, hM⟩ := hxb
    exact ⟨M + Ma, fun t => (norm_add_le _ _).trans (add_le_add (hM t)
      ((norm_le_pi_norm _ 0).trans (hMa t)))⟩
  have hb1 : sre_IsBounded pi' := by
    obtain ⟨M, hM⟩ := hpb
    exact ⟨M + Ma, fun t => (norm_add_le _ _).trans (add_le_add (hM t)
      ((norm_le_pi_norm _ 1).trans (hMa t)))⟩
  have ha0 : sre_IsAdapted E x' := fun t => by simp only [x', map_add, hxa t, hHa t 0]
  have ha1 : sre_IsAdapted E pi' := fun t => by simp only [pi', map_add, hpa t, hHa t 1]
  obtain ⟨hia', hib'⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) (v := fun _ => 0)
    hone hb0 hb1 ⟨0, fun _ => by simp⟩ ha0 ha1 (fun _ => map_zero _)
  have hsys' : nk_dnkSystem E β γ κ φπ φy one (fun _ => 0) (fun _ => 0) x' pi'
      (fun t => (-Real.log β) • one + φπ • pi' t + φy • x' t + 0) :=
    (nk_dnk_iff E β γ κ φπ φy one _ _ _ _ _).2 ⟨hT2, fun _ => rfl⟩
  have h1 := hu (x', pi', _) ⟨hsys', ha0, ha1, hia', hb0, hb1, hib'⟩
  have hx : x' = x := congrArg (fun z => z.1) h1
  have hp : pi' = pi := congrArg (fun z => z.2.1) h1
  apply hH0
  funext t j
  fin_cases j
  · have := congrFun hx t
    simp only [x'] at this
    simpa using this
  · have := congrFun hp t
    simp only [pi'] at this
    simpa using this

/-- **Exercise 19.1**, exact conditions (Miao, p. 668): for `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0`
and an adapted constant `𝟙 ≠ 0`, the model has a unique stable equilibrium iff
`κ(φ_π − 1) + (1 − β)φ_y > 0` or `κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0`. -/
theorem ex_19_1_exact [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy) (hone0 : one ≠ 0)
    (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E β γ κ φπ φy one ↔
      (0 < κ * (φπ - 1) + (1 - β) * φy ∨ κ * (1 + φπ) + (1 + β) * (2 * γ + φy) < 0) :=
  ⟨ex_19_1_nec E hκ hβ0 hβ1 hγ hφy hone0 hone, ex_19_1_suff E hκ hβ0 hβ1 hγ hφy hone⟩

/-- **Exercise 19.1** (Bullard and Mitra; Miao, p. 668), condition (19.31): for `κ, γ > 0`,
`0 < β < 1`, `φ_π, φ_y ≥ 0` and an adapted constant `𝟙 ≠ 0`, the model of §19.1 has a unique
stable equilibrium for all bounded adapted shocks iff `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem ex_19_1 [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E β γ κ φπ φy one ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  rw [ex_19_1_exact E hκ hβ0 hβ1 hγ hφy hone0 hone]
  refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
  nlinarith [mul_nonneg hκ.le hφπ, mul_nonneg hβ0.le hφy]

/-- **Exercise 19.1** with the structural slope (19.25) (Miao, pp. 626, 668): for
`0 < θ < 1`, `0 < β < 1`, `0 ≤ α < 1`, `ε ≥ 0`, `γ > 0`, `ν ≥ 0`, `φ_π, φ_y ≥ 0`, determinacy
holds iff `κ(φ_π − 1) + (1 − β)φ_y > 0` with `κ = nk_kappa β θ γ ν α ε`. -/
theorem ex_19_1_structural [CompleteSpace V] (E : CondExpSystem ℝ V) {β θ γ ν α ε φπ φy : ℝ}
    {one : V} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 ≤ ε) (hγ : 0 < γ) (hν : 0 ≤ ν) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E β γ (nk_kappa β θ γ ν α ε) φπ φy one ↔
      0 < nk_kappa β θ γ ν α ε * (φπ - 1) + (1 - β) * φy := by
  have hβθ : β * θ < 1 := by nlinarith
  have hD : 0 < ν + α + γ * (1 - α) := by nlinarith
  exact ex_19_1 E (nk_kappa_pos hθ0 hθ1 hβθ hα0 hα1 hε hD) hβ0 hβ1 hγ hφπ hφy hone0 hone

/-- Exercise 19.1 without sign restrictions (Miao, p. 668): (19.31) is not necessary. For
`κ = γ = 1`, `β = 1/2`, `φ_π = −5`, `φ_y = 0`, the equilibrium is unique although
`κ(φ_π − 1) + (1 − β)φ_y = −6 < 0`. -/
theorem ex_19_1_not_necessary [CompleteSpace V] (E : CondExpSystem ℝ V) {one : V}
    (hone : ∀ t, E.E t one = one) :
    nk_dnkDeterminate E (1 / 2) 1 1 (-5) 0 one ∧ ¬ (0 < 1 * ((-5 : ℝ) - 1) + (1 - 1 / 2) * 0) :=
  ⟨ex_19_1_suff E one_pos (by norm_num) (by norm_num) one_pos le_rfl hone
    (Or.inr (by norm_num)), by norm_num⟩

/-- The coefficient `Λ = 1/((1 − βρ)(γ(1 − ρ) + φ_y) + κ(φ_π − ρ))` of the impulse responses
(Miao, Figures 19.1–19.2, p. 628). -/
noncomputable def nk_irfLam (β γ κ φπ φy ρ : ℝ) : ℝ :=
  1 / ((1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ))

/-- Under (19.31), with `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0` and `ρ < 1`, the denominator of
`Λ` is positive, hence `Λ > 0`, and `γ(1 − ρ)(1 − βρ)Λ < 1`. -/
theorem nk_irfLam_pos {β γ κ φπ φy ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hφy : 0 ≤ φy) (hρ1 : ρ < 1)
    (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy) :
    0 < (1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ) ∧ 0 < nk_irfLam β γ κ φπ φy ρ ∧
      γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ < 1 := by
  have hbr : 0 < 1 - β * ρ := by nlinarith
  have p1 : 0 ≤ β * (1 - ρ) * φy :=
    mul_nonneg (mul_nonneg hβ0.le (by linarith)) hφy
  have p2 : 0 < κ * (1 - ρ) := mul_pos hκ (by linarith)
  have h2 : 0 < (1 - β * ρ) * φy + κ * (φπ - ρ) := by nlinarith
  have hden : 0 < (1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ) := by
    nlinarith [mul_pos hbr (mul_pos hγ (by linarith : (0 : ℝ) < 1 - ρ))]
  refine ⟨hden, by rw [nk_irfLam]; positivity, ?_⟩
  rw [nk_irfLam, ← mul_div_assoc, mul_one, div_lt_one hden]
  nlinarith

/-- The closed-form equilibrium for AR(1) shocks (Miao, Figures 19.1–19.2): if
`E_t s_{t+1} = ρs_t` and the shocks are `v = a•s` and `r^n = −ln β + c•s`, then
`x_t = ((1 − βρ)Λ(c − a))s_t`, `π_t = (κΛ(c − a))s_t` and the Taylor-rule `i_t` solve the
model. -/
theorem nk_irf_solves (E : CondExpSystem ℝ V) {β γ κ φπ φy ρ a c : ℝ} {one : V} {s : ℕ → V}
    (hγ : γ ≠ 0) (hden : (1 - β * ρ) * (γ * (1 - ρ) + φy) + κ * (φπ - ρ) ≠ 0)
    (hs : ∀ t, E.E t (s (t + 1)) = ρ • s t) :
    nk_dnkSystem E β γ κ φπ φy one (fun t => a • s t)
      (fun t => (-Real.log β) • one + c • s t)
      (fun t => ((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t)
      (fun t => (κ * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t)
      (fun t => (-Real.log β) • one +
        φπ • (κ * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t +
        φy • ((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ * (c - a)) • s t + a • s t) := by
  intro t
  refine ⟨?_, ?_, rfl⟩
  · simp only [map_smul, hs t, nk_irfLam]
    match_scalars
    field_simp
    ring
  · simp only [map_smul, hs t, nk_irfLam]
    match_scalars
    · field_simp
      ring
    · ring

/-- **Figure 19.1** (Miao, pp. 627–628), qualitatively: an AR(1) monetary policy shock
(`E_tv_{t+1} = ρv_t`, `0 ≤ ρ < 1`, `r^n = −ln β`). Under (19.31) with `κ, γ > 0`,
`0 < β < 1`, `φ_π, φ_y ≥ 0`, every stable equilibrium has `x_t = −((1 − βρ)Λ)v_t`,
`π_t = −(κΛ)v_t` with `(1 − βρ)Λ, κΛ > 0` (the output gap and inflation fall after a positive
shock), the real rate `i_t − E_tπ_{t+1}` is `−ln β + (γ(1 − ρ)(1 − βρ)Λ)v_t` with a positive
coefficient, and the nominal rate is the real rate minus `(ρκΛ)v_t`, `ρκΛ ≥ 0`. -/
theorem nk_fig_19_1 [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy ρ : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) {v : ℕ → V} (hvb : sre_IsBounded v)
    (hva : sre_IsAdapted E v) (hv : ∀ t, E.E t (v (t + 1)) = ρ • v t)
    {x pi i : ℕ → V} (hsys : nk_dnkSystem E β γ κ φπ φy one v (fun _ => (-Real.log β) • one)
      x pi i) (hxa : sre_IsAdapted E x) (hpa : sre_IsAdapted E pi) (hia : sre_IsAdapted E i)
    (hxb : sre_IsBounded x) (hpb : sre_IsBounded pi) (hib : sre_IsBounded i) :
    0 < (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧ 0 < κ * nk_irfLam β γ κ φπ φy ρ ∧
    0 < γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧
    0 ≤ ρ * κ * nk_irfLam β γ κ φπ φy ρ ∧
    (∀ t, x t = -(((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • v t)) ∧
    (∀ t, pi t = -((κ * nk_irfLam β γ κ φπ φy ρ) • v t)) ∧
    (∀ t, i t - E.E t (pi (t + 1)) =
      (-Real.log β) • one + (γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • v t) ∧
    (∀ t, i t = (i t - E.E t (pi (t + 1))) - (ρ * κ * nk_irfLam β γ κ φπ φy ρ) • v t) := by
  obtain ⟨hden, hL, -⟩ := nk_irfLam_pos hκ hβ0 hβ1 hγ hφy hρ1 h31
  set L := nk_irfLam β γ κ φπ φy ρ with hLdef
  have hbr : 0 < 1 - β * ρ := by nlinarith
  have hsol := nk_irf_solves E (one := one) (a := 1) (c := 0) hγ.ne' hden.ne' hv
  have hdet := (ex_19_1 E hκ hβ0 hβ1 hγ hφπ hφy hone0 hone).2 h31
  obtain ⟨Mv, hMv⟩ := hvb
  have hvb' : sre_IsBounded (fun t => (1 : ℝ) • v t) := ⟨Mv, fun t => by simpa using hMv t⟩
  have hva' : sre_IsAdapted E (fun t => (1 : ℝ) • v t) := fun t => by simp [hva t]
  obtain ⟨z, -, hzu⟩ := hdet (fun t => (1 : ℝ) • v t) (fun _ => (-Real.log β) • one) hvb'
    ⟨‖(-Real.log β) • one‖, fun _ => le_rfl⟩ hva' (fun t => by simp [hone])
  have hsmul : ∀ (k : ℝ), sre_IsBounded (fun t => k • v t) ∧ sre_IsAdapted E (fun t => k • v t) :=
    fun k => ⟨⟨|k| * Mv, fun t => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMv t) (abs_nonneg _)⟩, fun t => by simp [hva t]⟩
  have hrn : (fun t => (-Real.log β) • one + (0 : ℝ) • v t) = fun _ => (-Real.log β) • one :=
    funext fun t => by simp
  rw [hrn] at hsol
  have hv1 : (fun t => (1 : ℝ) • v t) = v := funext fun t => one_smul _ _
  rw [hv1] at hsol hzu
  obtain ⟨hb1, ha1⟩ := hsmul ((1 - β * ρ) * L * (0 - 1))
  obtain ⟨hb2, ha2⟩ := hsmul (κ * L * (0 - 1))
  obtain ⟨hia', hib'⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) hone hb1 hb2
    ⟨Mv, fun t => by simpa using hMv t⟩ ha1 ha2 (fun t => by simp [hva t])
  simp only [one_smul, ← hLdef] at hsol
  have e1 := hzu (x, pi, i) ⟨hsys, hxa, hpa, hia, hxb, hpb, hib⟩
  have e2 := hzu (fun t => ((1 - β * ρ) * L * (0 - 1)) • v t,
    fun t => (κ * L * (0 - 1)) • v t, fun t => (-Real.log β) • one +
      φπ • (κ * L * (0 - 1)) • v t + φy • ((1 - β * ρ) * L * (0 - 1)) • v t + v t)
    ⟨hsol, ha1, ha2, hia', hb1, hb2, hib'⟩
  have hz := e1.trans e2.symm
  have hx : x = fun t => ((1 - β * ρ) * L * (0 - 1)) • v t := congrArg (fun z => z.1) hz
  have hp : pi = fun t => (κ * L * (0 - 1)) • v t := congrArg (fun z => z.2.1) hz
  have hi : i = fun t => (-Real.log β) • one + φπ • (κ * L * (0 - 1)) • v t +
      φy • ((1 - β * ρ) * L * (0 - 1)) • v t + v t := congrArg (fun z => z.2.2) hz
  have hreal : ∀ t, i t - E.E t (pi (t + 1)) =
      (-Real.log β) • one + (γ * (1 - ρ) * (1 - β * ρ) * L) • v t := fun t => by
    rw [hi, hp]
    simp only [map_smul, hv t]
    rw [hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring
  refine ⟨mul_pos hbr hL, mul_pos hκ hL, by
    have : (0 : ℝ) < 1 - ρ := by linarith
    positivity, by positivity, fun t => ?_, fun t => ?_, hreal, fun t => ?_⟩
  · rw [hx, ← neg_smul]
    ring_nf
  · rw [hp, ← neg_smul]
    ring_nf
  · rw [hreal t, hi, hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring

/-- **Figure 19.2** (Miao, p. 628), qualitatively: an AR(1) shock to the natural rate
(`r^n_t = −ln β + r̂^n_t`, `E_tr̂^n_{t+1} = ρr̂^n_t`, `0 ≤ ρ < 1`, `v = 0`). Under (19.31) with
`κ, γ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`, every stable equilibrium has
`x_t = ((1 − βρ)Λ)r̂^n_t`, `π_t = (κΛ)r̂^n_t` (both rise after a positive shock), the real rate
`i_t − E_tπ_{t+1} = −ln β + kr̂^n_t` with `0 < k < 1` (it rises by less than one percent), and
the nominal rate is the real rate plus `(ρκΛ)r̂^n_t`, so its response `k + ρκΛ` is positive. -/
theorem nk_fig_19_2 [CompleteSpace V] (E : CondExpSystem ℝ V) {β γ κ φπ φy ρ : ℝ} {one : V}
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (hone0 : one ≠ 0) (hone : ∀ t, E.E t one = one) {r : ℕ → V} (hrb : sre_IsBounded r)
    (hra : sre_IsAdapted E r) (hr : ∀ t, E.E t (r (t + 1)) = ρ • r t)
    {x pi i : ℕ → V} (hsys : nk_dnkSystem E β γ κ φπ φy one (fun _ => 0)
      (fun t => (-Real.log β) • one + r t) x pi i) (hxa : sre_IsAdapted E x)
    (hpa : sre_IsAdapted E pi) (hia : sre_IsAdapted E i)
    (hxb : sre_IsBounded x) (hpb : sre_IsBounded pi) (hib : sre_IsBounded i) :
    0 < (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧ 0 < κ * nk_irfLam β γ κ φπ φy ρ ∧
    0 < 1 - γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ ∧
    1 - γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ < 1 ∧
    0 ≤ ρ * κ * nk_irfLam β γ κ φπ φy ρ ∧
    (∀ t, x t = ((1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • r t) ∧
    (∀ t, pi t = (κ * nk_irfLam β γ κ φπ φy ρ) • r t) ∧
    (∀ t, i t - E.E t (pi (t + 1)) = (-Real.log β) • one +
      (1 - γ * (1 - ρ) * (1 - β * ρ) * nk_irfLam β γ κ φπ φy ρ) • r t) ∧
    (∀ t, i t = (i t - E.E t (pi (t + 1))) + (ρ * κ * nk_irfLam β γ κ φπ φy ρ) • r t) := by
  obtain ⟨hden, hL, hlt⟩ := nk_irfLam_pos hκ hβ0 hβ1 hγ hφy hρ1 h31
  set L := nk_irfLam β γ κ φπ φy ρ with hLdef
  have hbr : 0 < 1 - β * ρ := by nlinarith
  have hsol := nk_irf_solves E (one := one) (a := 0) (c := 1) hγ.ne' hden.ne' hr
  have hdet := (ex_19_1 E hκ hβ0 hβ1 hγ hφπ hφy hone0 hone).2 h31
  obtain ⟨Mr, hMr⟩ := hrb
  have hsmul : ∀ (k : ℝ), sre_IsBounded (fun t => k • r t) ∧ sre_IsAdapted E (fun t => k • r t) :=
    fun k => ⟨⟨|k| * Mr, fun t => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMr t) (abs_nonneg _)⟩, fun t => by simp [hra t]⟩
  obtain ⟨z, -, hzu⟩ := hdet (fun _ => 0) (fun t => (-Real.log β) • one + r t)
    ⟨0, fun _ => by simp⟩ ⟨‖(-Real.log β) • one‖ + Mr, fun t => (norm_add_le _ _).trans
      (add_le_add le_rfl (hMr t))⟩ (fun _ => map_zero _)
    (fun t => by simp [hone, hra t])
  have hv0 : (fun t => (0 : ℝ) • r t) = fun _ => (0 : V) := funext fun t => zero_smul _ _
  have hrn1 : (fun t => (-Real.log β) • one + (1 : ℝ) • r t) =
      fun t => (-Real.log β) • one + r t := funext fun t => by rw [one_smul]
  rw [hv0, hrn1] at hsol
  obtain ⟨hb1, ha1⟩ := hsmul ((1 - β * ρ) * L * (1 - 0))
  obtain ⟨hb2, ha2⟩ := hsmul (κ * L * (1 - 0))
  obtain ⟨hia', hib'⟩ := nk_rule_regular E (β := β) (φπ := φπ) (φy := φy) (v := fun _ => 0)
    hone hb1 hb2 ⟨0, fun _ => by simp⟩ ha1 ha2 (fun _ => map_zero _)
  simp only [zero_smul, ← hLdef] at hsol
  have e1 := hzu (x, pi, i) ⟨hsys, hxa, hpa, hia, hxb, hpb, hib⟩
  have e2 := hzu (fun t => ((1 - β * ρ) * L * (1 - 0)) • r t,
    fun t => (κ * L * (1 - 0)) • r t, fun t => (-Real.log β) • one +
      φπ • (κ * L * (1 - 0)) • r t + φy • ((1 - β * ρ) * L * (1 - 0)) • r t + 0)
    ⟨hsol, ha1, ha2, hia', hb1, hb2, hib'⟩
  have hz := e1.trans e2.symm
  have hx : x = fun t => ((1 - β * ρ) * L * (1 - 0)) • r t := congrArg (fun z => z.1) hz
  have hp : pi = fun t => (κ * L * (1 - 0)) • r t := congrArg (fun z => z.2.1) hz
  have hi : i = fun t => (-Real.log β) • one + φπ • (κ * L * (1 - 0)) • r t +
      φy • ((1 - β * ρ) * L * (1 - 0)) • r t + 0 := congrArg (fun z => z.2.2) hz
  have hreal : ∀ t, i t - E.E t (pi (t + 1)) =
      (-Real.log β) • one + (1 - γ * (1 - ρ) * (1 - β * ρ) * L) • r t := fun t => by
    rw [hi, hp]
    simp only [map_smul, hr t]
    rw [hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring
  have hk : 0 < 1 - γ * (1 - ρ) * (1 - β * ρ) * L := by linarith
  refine ⟨mul_pos hbr hL, mul_pos hκ hL, hk, by
    have : (0 : ℝ) < 1 - ρ := by linarith
    have : 0 < γ * (1 - ρ) * (1 - β * ρ) * L := by positivity
    linarith, by positivity, fun t => ?_, fun t => ?_, hreal, fun t => ?_⟩
  · rw [hx]
    ring_nf
  · rw [hp]
    ring_nf
  · rw [hreal t, hi, hLdef, nk_irfLam]
    match_scalars
    · rfl
    · field_simp
      ring

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary policy design: the efficient allocation (Miao §19.2.1)

Miao, §19.2.1, pp. 630–631, with the inefficiency measure `Φ` and `x*` of p. 634.

The planner's problem of p. 630 is static date by date. With the firms indexed by a probability
space `(Ω, μ)` (the book's `dj` on `[0, 1]`), firm output `Y_j = A N_j^{1−α}` and the CES
aggregate `Y = (∫ Y_j^{(ε−1)/ε})^{ε/(ε−1)}`:
* `mp_ces_le`, `mp_ces_symmetric`, `mp_ces_lt`: for any labour allocation with `∫ N_j = N`,
  `Y ≤ AN^{1−α}`, with equality for the symmetric allocation `N_j = N` (then `Y_j = Y`) and
  strict inequality unless `N_j = N` almost everywhere ("`Y_t^j = Y_t = C_t`, `N_t^j = N_t`").
* `mp_planner_foc`: with the utility (19.1) without money (`mpU`), an interior maximiser of
  `u(AN^{1−α}, N)` satisfies `−u_N/u_C = (1 − α)AN^{−α} = MPN`.
* `mp_mrs_iff_log`, `mp_mrs_output`: the condition `MRS = MPN/m` (`m = 1` efficient, `m = μ`
  flexible prices) has the unique solution `ln N = (ln((1 − α)/(mχ)) + (1 − γ)ln A)/D`,
  `D = γ(1 − α) + α + ν`, and then output is `mpYout = ((1 − α)/(mχ))^{(1−α)/D} A^{(1+ν)/D}`,
  i.e. (19.18), with `m = 1` the efficient output `Y^e`.
* `mp_subsidy`: the employment subsidy `τ = 1/ε` gives `(1 − τ)μ = 1`, so the firm's condition
  `(1 − τ)W/P = MPN/μ` becomes `W/P = MPN`, and `τ = 1/ε` is the only such subsidy;
  `mp_subsidy_household` (footnote 6): a subsidy to the household must be `1/(ε − 1)`;
  `mp_flex_subsidy_efficient`: with the subsidy the flexible-price output is `Y^e`.
* `mp_distortion`: in the flexible-price equilibrium with subsidy `τ`,
  `−u_N/u_C = MPN(1 − Φ)` with `Φ = 1 − 1/((1 − τ)μ)` (p. 634), and `Φ = 0` iff `τ = 1/ε`.
* `mp_yf_loglinear`: `ŷ^f = (1 + ν)/D · â` (used on p. 634); `mp_xstar_first_order`:
  `ln(Y^e/Y^f) = −((1 − α)/D)ln(1 − Φ)`, which equals `x* = Φ(1 − α)/D` up to `2((1 − α)/D)Φ²`
  for `|Φ| ≤ 1/2` ("up to first-order approximation, `x*` is the log of `Y^e/Y^f`").

The firm FOC, the household FOC and the flexible-price equilibrium are §19.1 (another part);
here they enter as the equations the text writes on p. 631.
-/

namespace Miao.NewKeynesian

open MeasureTheory

/-! ### The CES aggregate and the symmetric allocation -/

/-- The CES aggregate `Y = (∫ Y_j^{(ε−1)/ε} dj)^{ε/(ε−1)}` (Miao, p. 630). -/
noncomputable def mpCES {Ω : Type*} [MeasurableSpace Ω] (ε : ℝ) (μ : Measure Ω) (Yj : Ω → ℝ) :
    ℝ :=
  (∫ j, Yj j ^ ((ε - 1) / ε) ∂μ) ^ (ε / (ε - 1))

/-- The exponent `q = (1 − α)(ε − 1)/ε` of `N_j` in `Y_j^{(ε−1)/ε}`; `0 < q < 1`. -/
theorem mp_q_bounds {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) :
    0 < (1 - α) * ((ε - 1) / ε) ∧ (1 - α) * ((ε - 1) / ε) < 1 := by
  have he0 : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  have he1 : (ε - 1) / ε < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine ⟨mul_pos (by linarith) he0, ?_⟩
  nlinarith

/-- `(AN_j^{1−α})^{(ε−1)/ε} = A^{(ε−1)/ε} N_j^q`. -/
theorem mp_firm_term {α ε A n : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n) :
    (A * n ^ (1 - α)) ^ ((ε - 1) / ε) = A ^ ((ε - 1) / ε) * n ^ ((1 - α) * ((ε - 1) / ε)) := by
  rw [Real.mul_rpow hA (Real.rpow_nonneg hn _), ← Real.rpow_mul hn]

/-- `(A^{(ε−1)/ε} N^q)^{ε/(ε−1)} = AN^{1−α}`. -/
theorem mp_ces_const {α ε A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N) (hε : 1 < ε) :
    (A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))) ^ (ε / (ε - 1)) = A * N ^ (1 - α) := by
  have he : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) (by linarith)
  have hinv : ε / (ε - 1) = ((ε - 1) / ε)⁻¹ := by rw [inv_div]
  rw [Real.rpow_mul hN, ← Real.mul_rpow hA (Real.rpow_nonneg hN _), hinv,
    Real.rpow_rpow_inv (mul_nonneg hA (Real.rpow_nonneg hN _)) he]

/-- `N_j^q` is integrable whenever `N_j ≥ 0` is (`N^q ≤ 1 + N` for `0 < q < 1`). -/
theorem mp_integrable_rpow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {n : Ω → ℝ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hn : ∀ j, 0 ≤ n j) (hi : Integrable n μ) :
    Integrable (fun j => n j ^ q) μ := by
  refine Integrable.mono' ((integrable_const 1).add hi)
    ((Real.continuous_rpow_const hq0.le).comp_aestronglyMeasurable hi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hn j) _)]
  rcases le_total (n j) 1 with h | h
  · have := Real.rpow_le_one (hn j) h hq0.le
    simp only [Pi.add_apply]
    linarith [hn j]
  · have := Real.rpow_le_rpow_of_exponent_le h hq1.le
    rw [Real.rpow_one] at this
    simp only [Pi.add_apply]
    linarith

/-- **The symmetric allocation is output-maximising** (Miao, p. 630). For a probability measure
on the firms, `A ≥ 0`, `0 ≤ α < 1`, `ε > 1` and any integrable labour allocation `N_j ≥ 0`,
`Y = (∫(AN_j^{1−α})^{(ε−1)/ε})^{ε/(ε−1)} ≤ A(∫N_j)^{1−α}`. -/
theorem mp_ces_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α ε A : ℝ} (hA : 0 ≤ A) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) {n : Ω → ℝ}
    (hn : ∀ j, 0 ≤ n j) (hi : Integrable n μ) :
    mpCES ε μ (fun j => A * n j ^ (1 - α)) ≤ A * (∫ j, n j ∂μ) ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := mp_q_bounds hα0 hα1 hε
  set q := (1 - α) * ((ε - 1) / ε)
  have hN : 0 ≤ ∫ j, n j ∂μ := integral_nonneg hn
  have hqi := mp_integrable_rpow hq0 hq1 hn hi
  have hJ : ∫ j, n j ^ q ∂μ ≤ (∫ j, n j ∂μ) ^ q :=
    (Real.strictConcaveOn_rpow hq0 hq1).concaveOn.le_map_integral
      (Real.continuous_rpow_const hq0.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hn) hi hqi
  have hI0 : 0 ≤ ∫ j, n j ^ q ∂μ := integral_nonneg fun j => Real.rpow_nonneg (hn j) _
  simp only [mpCES]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun j => mp_firm_term hA (hn j)),
    integral_const_mul, ← mp_ces_const (α := α) hA hN hε]
  exact Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hA _) hI0)
    (mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hA _)) (div_pos (by linarith) (by linarith)).le

/-- Miao, p. 631: at the symmetric allocation `N_j = N`, `Y_j = Y = AN^{1−α}`. -/
theorem mp_ces_symmetric {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {α ε A N : ℝ} (hA : 0 ≤ A) (hN : 0 ≤ N) (hε : 1 < ε) :
    mpCES ε μ (fun _ => A * N ^ (1 - α)) = A * N ^ (1 - α) := by
  simp only [mpCES, integral_const, probReal_univ, one_smul]
  rw [mp_firm_term hA hN, mp_ces_const hA hN hε]

/-- **Uniqueness of the symmetric allocation** (Miao, p. 631: "`Y_t^j = Y_t`, `N_t^j = N_t` for
all `j`"). For `A > 0`, unless `N_j = ∫N_j` for almost every `j`, output is strictly below
`A(∫N_j)^{1−α}`. -/
theorem mp_ces_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {α ε A : ℝ} (hA : 0 < A) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) {n : Ω → ℝ}
    (hn : ∀ j, 0 ≤ n j) (hi : Integrable n μ)
    (hne : ¬ n =ᵐ[μ] Function.const Ω (∫ j, n j ∂μ)) :
    mpCES ε μ (fun j => A * n j ^ (1 - α)) < A * (∫ j, n j ∂μ) ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := mp_q_bounds hα0 hα1 hε
  set q := (1 - α) * ((ε - 1) / ε)
  have hN : 0 ≤ ∫ j, n j ∂μ := integral_nonneg hn
  have hqi := mp_integrable_rpow hq0 hq1 hn hi
  have hJ : ∫ j, n j ^ q ∂μ < (∫ j, n j ∂μ) ^ q := by
    rcases (Real.strictConcaveOn_rpow hq0 hq1).ae_eq_const_or_lt_map_average
      (Real.continuous_rpow_const hq0.le).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall hn) hi hqi with h | h
    · rw [average_eq_integral] at h
      exact absurd h hne
    · simpa only [average_eq_integral] using h
  have hI0 : 0 ≤ ∫ j, n j ^ q ∂μ := integral_nonneg fun j => Real.rpow_nonneg (hn j) _
  simp only [mpCES]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun j => mp_firm_term hA.le (hn j)),
    integral_const_mul, ← mp_ces_const (α := α) hA.le hN hε]
  exact Real.rpow_lt_rpow (mul_nonneg (Real.rpow_nonneg hA.le _) hI0)
    (mul_lt_mul_of_pos_left hJ (Real.rpow_pos_of_pos hA _)) (div_pos (by linarith) (by linarith))

/-! ### The planner's first-order condition -/

/-- The period utility (19.1) without money: `u(C, N) = C^{1−γ}/(1 − γ) − χN^{1+ν}/(1 + ν)`. -/
noncomputable def mpU (γ χ ν C N : ℝ) : ℝ := C ^ (1 - γ) / (1 - γ) - χ * N ^ (1 + ν) / (1 + ν)

/-- `u_C = C^{−γ}` for (19.1) (`γ ≠ 1`, `C > 0`). -/
theorem mp_hasDerivAt_uC {γ χ ν C N : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) :
    HasDerivAt (fun c => mpU γ χ ν c N) (C ^ (-γ)) C := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hC.ne')).div_const (1 - γ)).sub_const
    (χ * N ^ (1 + ν) / (1 + ν))
  refine this.congr_deriv ?_
  rw [show 1 - γ - 1 = -γ by ring]
  field_simp

/-- `u_N = −χN^ν` for (19.1) (`ν ≠ −1`, `N > 0`). -/
theorem mp_hasDerivAt_uN {γ χ ν C N : ℝ} (hν : ν ≠ -1) (hN : 0 < N) :
    HasDerivAt (fun n => mpU γ χ ν C n) (-(χ * N ^ ν)) N := by
  have h1 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  have := (((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + ν)).const_sub (C ^ (1 - γ) / (1 - γ))
  refine this.congr_deriv ?_
  rw [show 1 + ν - 1 = ν by ring]
  field_simp

/-- The marginal product of labour: `d(AN^{1−α})/dN = (1 − α)AN^{−α}`. -/
theorem mp_hasDerivAt_mpn {α A N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => A * n ^ (1 - α)) ((1 - α) * A * N ^ (-α)) N := by
  have := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A
  convert this using 1
  rw [show 1 - α - 1 = -α by ring]
  ring

/-- **The planner's condition** (Miao, p. 631). If `N > 0` maximises `u(AN^{1−α}, N)` locally
(`γ ≠ 1`, `ν ≠ −1`, `A > 0`), then `−u_N/u_C = (1 − α)AN^{−α}`: with `C = AN^{1−α}`,
`χN^ν/C^{−γ} = MPN`. -/
theorem mp_planner_foc {γ χ ν α A N : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hA : 0 < A) (hN : 0 < N)
    (hmax : IsLocalMax (fun n => mpU γ χ ν (A * n ^ (1 - α)) n) N) :
    χ * N ^ ν / (A * N ^ (1 - α)) ^ (-γ) = (1 - α) * A * N ^ (-α) := by
  set C := A * N ^ (1 - α)
  have hC : 0 < C := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h2 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  have hc := ((Real.hasDerivAt_rpow_const (p := 1 - γ) (Or.inl hC.ne')).comp N
    (mp_hasDerivAt_mpn (α := α) (A := A) hN)).div_const (1 - γ)
  have hn := ((Real.hasDerivAt_rpow_const (p := 1 + ν) (Or.inl hN.ne')).const_mul χ).div_const
    (1 + ν)
  have hd := hc.sub hn
  have h0 := hmax.hasDerivAt_eq_zero hd
  have hCg : 0 < C ^ (-γ) := Real.rpow_pos_of_pos hC _
  rw [show 1 - γ - 1 = -γ by ring, show 1 + ν - 1 = ν by ring] at h0
  rw [div_eq_iff hCg.ne']
  field_simp at h0
  linear_combination (-1) * h0

/-! ### Solving `MRS = MPN/m` -/

/-- The output solving `MRS = MPN/m`: `((1 − α)/(mχ))^{(1−α)/D} A^{(1+ν)/D}`,
`D = γ(1 − α) + α + ν` (Miao, (19.18); `m = 1` is the efficient output `Y^e`). -/
noncomputable def mpYout (α γ ν χ m A : ℝ) : ℝ :=
  ((1 - α) / (m * χ)) ^ ((1 - α) / (γ * (1 - α) + α + ν)) *
    A ^ ((1 + ν) / (γ * (1 - α) + α + ν))

/-- Miao, p. 631: for `A, N, χ, m > 0`, `α < 1`, `D = γ(1 − α) + α + ν ≠ 0`, the condition
`χN^ν = (AN^{1−α})^{−γ}(1 − α)AN^{−α}/m` holds iff
`ln N = (ln((1 − α)/(mχ)) + (1 − γ)ln A)/D`; in particular it has exactly one solution. -/
theorem mp_mrs_iff_log {α γ ν χ m A N : ℝ} (hα : α < 1) (hχ : 0 < χ) (hm : 0 < m) (hA : 0 < A)
    (hN : 0 < N) (hD : γ * (1 - α) + α + ν ≠ 0) :
    χ * N ^ ν = (A * N ^ (1 - α)) ^ (-γ) * ((1 - α) * A * N ^ (-α)) / m ↔
      Real.log N = (Real.log ((1 - α) / (m * χ)) + (1 - γ) * Real.log A) /
        (γ * (1 - α) + α + ν) := by
  have h1a : 0 < 1 - α := by linarith
  have hNa := Real.rpow_pos_of_pos hN (1 - α)
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA hNa
  have hL : 0 < χ * N ^ ν := mul_pos hχ (Real.rpow_pos_of_pos hN _)
  have hR : 0 < (A * N ^ (1 - α)) ^ (-γ) * ((1 - α) * A * N ^ (-α)) / m :=
    div_pos (mul_pos (Real.rpow_pos_of_pos hC _)
      (mul_pos (mul_pos h1a hA) (Real.rpow_pos_of_pos hN _))) hm
  rw [← Real.log_injOn_pos.eq_iff hL hR]
  rw [Real.log_mul hχ.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN,
    Real.log_div (ne_of_gt (mul_pos (Real.rpow_pos_of_pos hC _)
      (mul_pos (mul_pos h1a hA) (Real.rpow_pos_of_pos hN _)))) hm.ne',
    Real.log_mul (Real.rpow_pos_of_pos hC _).ne'
      (mul_pos (mul_pos h1a hA) (Real.rpow_pos_of_pos hN _)).ne',
    Real.log_rpow hC, Real.log_mul hA.ne' hNa.ne', Real.log_rpow hN,
    Real.log_mul (mul_pos h1a hA).ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN,
    Real.log_mul h1a.ne' hA.ne', Real.log_div h1a.ne' (mul_pos hm hχ).ne',
    Real.log_mul hm.ne' hχ.ne', eq_div_iff hD]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- **Output under `MRS = MPN/m`** (Miao, p. 631 and (19.18)): if `ln N` solves the condition of
`mp_mrs_iff_log`, then `Y = AN^{1−α} = mpYout`. -/
theorem mp_mrs_output {α γ ν χ m A N : ℝ} (hα : α < 1) (hχ : 0 < χ) (hm : 0 < m) (hA : 0 < A)
    (hN : 0 < N) (hD : γ * (1 - α) + α + ν ≠ 0)
    (h : χ * N ^ ν = (A * N ^ (1 - α)) ^ (-γ) * ((1 - α) * A * N ^ (-α)) / m) :
    A * N ^ (1 - α) = mpYout α γ ν χ m A := by
  have hlog := (mp_mrs_iff_log hα hχ hm hA hN hD).1 h
  have h1a : 0 < 1 - α := by linarith
  have hk : 0 < (1 - α) / (m * χ) := div_pos h1a (mul_pos hm hχ)
  rw [mpYout, Real.rpow_def_of_pos hk, Real.rpow_def_of_pos hA, ← Real.exp_add,
    Real.rpow_def_of_pos hN, ← Real.exp_log hA, ← Real.exp_add, Real.log_exp, hlog]
  congr 1
  have hDi : (γ * (1 - α) + α + ν) * (γ * (1 - α) + α + ν)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv]
  linear_combination (-Real.log A) * hDi

/-! ### The employment subsidy -/

/-- **The employment subsidy** (Miao, p. 631). With `μ = ε/(ε − 1)` (`ε > 1`), the subsidy
`τ = 1/ε` gives `(1 − τ)μ = 1`, so the firm's condition `(1 − τ)W/P = MPN/μ` becomes
`W/P = MPN`; conversely `(1 − τ)μ = 1` forces `τ = 1/ε`. -/
theorem mp_subsidy {ε τ w mpn : ℝ} (hε : 1 < ε) :
    ((1 - τ) * (ε / (ε - 1)) = 1 ↔ τ = 1 / ε) ∧
      (τ = 1 / ε → (1 - τ) * w = mpn / (ε / (ε - 1)) → w = mpn) := by
  have h0 : ε ≠ 0 := by linarith
  have h1 : ε - 1 ≠ 0 := by linarith
  have key : (1 - τ) * (ε / (ε - 1)) = 1 ↔ τ = 1 / ε := by
    constructor
    · intro h
      field_simp at h ⊢
      linarith
    · intro h
      rw [h]
      field_simp
  refine ⟨key, fun hτ hw => ?_⟩
  have hk := key.2 hτ
  have hμ : ε / (ε - 1) ≠ 0 := div_ne_zero h0 h1
  rw [eq_div_iff hμ] at hw
  linear_combination hw - w * hk

/-- **Footnote 6** (Miao, p. 631): if the subsidy `τ_h` is paid to the household, the household's
condition `MRS = (1 + τ_h)W/P` and the firm's `W/P = MPN/μ` give `MRS = MPN` (for `MPN ≠ 0`) iff
`τ_h = 1/(ε − 1)`. -/
theorem mp_subsidy_household {ε τh mpn mrs w : ℝ} (hε : 1 < ε) (hmpn : mpn ≠ 0)
    (hhh : mrs = (1 + τh) * w) (hfirm : w = mpn / (ε / (ε - 1))) :
    mrs = mpn ↔ τh = 1 / (ε - 1) := by
  have h0 : ε ≠ 0 := by linarith
  have h1 : ε - 1 ≠ 0 := by linarith
  rw [hhh, hfirm]
  have e : (1 + τh) * (mpn / (ε / (ε - 1))) = mpn * ((1 + τh) * (ε - 1) / ε) := by
    field_simp
  rw [e]
  constructor
  · intro h
    have hk : (1 + τh) * (ε - 1) / ε = 1 := mul_left_cancel₀ hmpn (by rw [h, mul_one])
    rw [div_eq_one_iff_eq h0] at hk
    rw [eq_div_iff h1]
    linear_combination hk
  · intro h
    have hk : (1 + τh) * (ε - 1) / ε = 1 := by
      rw [h, div_eq_one_iff_eq h0]
      field_simp
      ring
    rw [hk, mul_one]

/-- Miao, p. 631: with the subsidy `τ = 1/ε` the flexible-price condition `MRS = MPN/((1 − τ)μ)`
is the efficient one, so flexible-price output is the efficient output `Y^e = mpYout … 1 …`. -/
theorem mp_flex_subsidy_efficient {α γ ν χ ε A : ℝ} (hε : 1 < ε) :
    mpYout α γ ν χ ((1 - 1 / ε) * (ε / (ε - 1))) A = mpYout α γ ν χ 1 A := by
  rw [((mp_subsidy (τ := 1 / ε) (w := 0) (mpn := 0) hε).1).2 rfl]

/-- **The steady-state distortion `Φ`** (Miao, p. 634). In the flexible-price equilibrium with
subsidy `τ` (household `MRS = W/P`, firm `(1 − τ)W/P = MPN/μ`, `(1 − τ)μ ≠ 0`),
`MRS = MPN(1 − Φ)` with `Φ = 1 − 1/((1 − τ)μ)`; `Φ = 0` iff `τ = 1/ε`. -/
theorem mp_distortion {ε τ w mpn mrs : ℝ} (hε : 1 < ε) (hτ : (1 - τ) * (ε / (ε - 1)) ≠ 0)
    (hhh : mrs = w) (hfirm : (1 - τ) * w = mpn / (ε / (ε - 1))) :
    mrs = mpn * (1 - (1 - 1 / ((1 - τ) * (ε / (ε - 1))))) ∧
      (1 - 1 / ((1 - τ) * (ε / (ε - 1))) = 0 ↔ τ = 1 / ε) := by
  have h0 : ε ≠ 0 := by linarith
  have h1 : ε - 1 ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [hhh, sub_sub_cancel, mul_one_div, eq_div_iff hτ]
    rw [eq_div_iff (div_ne_zero h0 h1)] at hfirm
    linear_combination hfirm
  · rw [← (mp_subsidy (w := 0) (mpn := 0) hε).1, sub_eq_zero, eq_comm, div_eq_one_iff_eq hτ,
      eq_comm]

/-- Miao, p. 634 ("`ŷ^f_t = (1 + ν)/(γ(1 − α) + ν + α) a_t`"): log flexible-price (or efficient)
output is affine in `ln A` with slope `(1 + ν)/D`. -/
theorem mp_yf_loglinear {α γ ν χ m A A' : ℝ} (hα : α < 1) (hχ : 0 < χ) (hm : 0 < m)
    (hA : 0 < A) (hA' : 0 < A') :
    Real.log (mpYout α γ ν χ m A) - Real.log (mpYout α γ ν χ m A') =
      (1 + ν) / (γ * (1 - α) + α + ν) * (Real.log A - Real.log A') := by
  have hk : 0 < (1 - α) / (m * χ) := div_pos (by linarith) (mul_pos hm hχ)
  simp only [mpYout]
  rw [Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hA _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (Real.rpow_pos_of_pos hA' _).ne',
    Real.log_rpow hk, Real.log_rpow hA, Real.log_rpow hA']
  ring

/-- `x* = Φ(1 − α)/(γ(1 − α) + ν + α)` (Miao, p. 634). -/
noncomputable def mpXstar (α γ ν Φ : ℝ) : ℝ := Φ * (1 - α) / (γ * (1 - α) + ν + α)

/-- **`x*` and the efficiency gap** (Miao, p. 634). With the effective markup
`m = (1 − τ)μ = 1/(1 − Φ)` (`Φ < 1`), `ln(Y^e/Y^f) = −((1 − α)/D)ln(1 − Φ)`, and for `|Φ| ≤ 1/2`
it differs from `x*` by at most `2((1 − α)/D)Φ²`: `x*` is `ln(Y^e/Y^f)` to first order. -/
theorem mp_xstar_first_order {α γ ν χ Φ A : ℝ} (hα : α < 1) (hχ : 0 < χ) (hA : 0 < A)
    (hD : 0 < γ * (1 - α) + ν + α) (hΦ : |Φ| ≤ 1 / 2) :
    Real.log (mpYout α γ ν χ 1 A / mpYout α γ ν χ (1 / (1 - Φ)) A) =
        -((1 - α) / (γ * (1 - α) + ν + α)) * Real.log (1 - Φ) ∧
      |Real.log (mpYout α γ ν χ 1 A / mpYout α γ ν χ (1 / (1 - Φ)) A) - mpXstar α γ ν Φ| ≤
        2 * ((1 - α) / (γ * (1 - α) + ν + α)) * Φ ^ 2 := by
  have h1a : 0 < 1 - α := by linarith
  have hΦ1 : 0 < 1 - Φ := by have := (abs_le.1 hΦ).2; linarith
  have hm : 0 < 1 / (1 - Φ) := by positivity
  have hk1 : 0 < (1 - α) / (1 * χ) := div_pos h1a (by linarith)
  have hk2 : 0 < (1 - α) / (1 / (1 - Φ) * χ) := div_pos h1a (mul_pos hm hχ)
  have hD' : γ * (1 - α) + α + ν = γ * (1 - α) + ν + α := by ring
  have heq : Real.log (mpYout α γ ν χ 1 A / mpYout α γ ν χ (1 / (1 - Φ)) A) =
      -((1 - α) / (γ * (1 - α) + ν + α)) * Real.log (1 - Φ) := by
    simp only [mpYout]
    rw [Real.log_div (mul_pos (Real.rpow_pos_of_pos hk1 _) (Real.rpow_pos_of_pos hA _)).ne'
        (mul_pos (Real.rpow_pos_of_pos hk2 _) (Real.rpow_pos_of_pos hA _)).ne',
      Real.log_mul (Real.rpow_pos_of_pos hk1 _).ne' (Real.rpow_pos_of_pos hA _).ne',
      Real.log_mul (Real.rpow_pos_of_pos hk2 _).ne' (Real.rpow_pos_of_pos hA _).ne',
      Real.log_rpow hk1, Real.log_rpow hk2, Real.log_div h1a.ne' (by positivity),
      Real.log_div h1a.ne' (mul_pos hm hχ).ne', one_mul,
      Real.log_mul hm.ne' hχ.ne', one_div, Real.log_inv, hD']
    ring
  refine ⟨heq, ?_⟩
  rw [heq, mpXstar]
  have hl : |(∑ i ∈ Finset.range 1, Φ ^ (i + 1) / (i + 1)) + Real.log (1 - Φ)| ≤
      |Φ| ^ (1 + 1) / (1 - |Φ|) :=
    Real.abs_log_sub_add_sum_range_le (by linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_zero, pow_one,
    div_one] at hl
  have hb : |Φ| ^ 2 / (1 - |Φ|) ≤ 2 * Φ ^ 2 := by
    rw [div_le_iff₀ (by linarith), sq_abs]
    nlinarith [sq_nonneg Φ]
  have hc : 0 ≤ (1 - α) / (γ * (1 - α) + ν + α) := div_nonneg h1a.le hD.le
  have : -((1 - α) / (γ * (1 - α) + ν + α)) * Real.log (1 - Φ) -
      Φ * (1 - α) / (γ * (1 - α) + ν + α) =
      -((1 - α) / (γ * (1 - α) + ν + α)) * (Φ + Real.log (1 - Φ)) := by ring
  rw [this, abs_mul, abs_neg, abs_of_nonneg hc]
  calc (1 - α) / (γ * (1 - α) + ν + α) * |Φ + Real.log (1 - Φ)|
      ≤ (1 - α) / (γ * (1 - α) + ν + α) * (2 * Φ ^ 2) :=
        mul_le_mul_of_nonneg_left (hl.trans hb) hc
    _ = 2 * ((1 - α) / (γ * (1 - α) + ν + α)) * Φ ^ 2 := by ring

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary policy design: price dispersion to second order (Miao §19.2.2, Step 1)

Miao, §19.2.2, Step 1, p. 633. Notation: `b = ε/(1 − α)`, `c = ε/((1 − α)(ε − 1))`,
`g(π) = (1 − θe^{(ε−1)π})/(1 − θ)` and `π_t = ln(P_t/P_{t−1})`.

* `mp_labor_log` (Step 1, first display): from (19.16), `Y = AN^{1−α}Δ^{α−1}`,
  `ln N = (ln Y − ln A)/(1 − α) + ln Δ` exactly; in deviations
  `n̂_t = (ŷ_t − a_t)/(1 − α) + Δ̂_t` (`mp_labor_dev`).
* `mp_dispersion_recursion`: (19.13) and (19.17) give
  `Δ_t = θe^{bπ_t}Δ_{t−1} + (1 − θ)g(π_t)^c` (the display "By (19.13) and (19.17)").
* `mp_dispersion_zero_inflation`: with `π_t = 0`, `Δ_t − 1 = θ(Δ_{t−1} − 1)` (no new dispersion).
* `mp_dispersion_delta`: with `δ_t = Δ_t − 1`, exactly
  `δ_t = θδ_{t−1} + h(π_t) + θ(e^{bπ_t} − 1)δ_{t−1}`, `h = mpH`.
* `mp_h_expansion`: `h(π) = Kπ² + o(π²)`, `K = (1 − α + αε)εθ/(2(1 − α)²(1 − θ))` (`mpK`):
  a precise Peano-remainder statement, proved from `h(0) = h'(0) = 0`, `h''(0) = 2K`
  (`mp_h_zero`, `mp_hd_zero`, `mp_hasDerivAt_h`, `mp_hasDerivAt_hd`) and the general lemma
  `mp_peano2`.
* `mp_dispersion_second_order`: the book's second-order expansion
  `Δ̂_t = θΔ̂_{t−1} + Kπ_t²`: for every `ε' > 0` there is `δ > 0` such that `|π_t| < δ` implies
  `|δ_t − θδ_{t−1} − Kπ_t²| ≤ ε'π_t² + 2θb|π_t||δ_{t−1}|`; the last term is a product of a
  first-order and a second-order term (third order), which the book drops.
  `mp_log_dev`: `|ln Δ − (Δ − 1)| ≤ 2(Δ − 1)²` for `|Δ − 1| ≤ 1/2`, so the expansion holds for
  `Δ̂ = ln Δ` up to fourth-order terms.
* `mp_dispersion_sum`: for the second-order law `Δ̂_t = θΔ̂_{t−1} + Kπ_t²`, `Δ̂_{−1} = 0`,
  `0 ≤ β, θ < 1` and bounded `π`, `∑βᵗΔ̂_t = K/(1 − θβ)·∑βᵗπ_t²`, and
  `K/(1 − θβ) = εθ/(2(1 − α)Θ(1 − θ)(1 − θβ))`, `Θ = (1 − α)/(1 − α + αε)` (`mp_K_Theta`).
-/

namespace Miao.NewKeynesian

open Filter Topology

/-! ### Step 1: labour and dispersion -/

/-- **Step 1** (Miao, p. 633). From (19.16) in the form `Y = AN^{1−α}Δ^{α−1}` (`A, N, Δ > 0`,
`α ≠ 1`), `ln N = (ln Y − ln A)/(1 − α) + ln Δ`. -/
theorem mp_labor_log {α A N Δ : ℝ} (hα : α ≠ 1) (hA : 0 < A) (hN : 0 < N) (hΔ : 0 < Δ) :
    Real.log N = (Real.log (A * N ^ (1 - α) * Δ ^ (α - 1)) - Real.log A) / (1 - α) +
      Real.log Δ := by
  have h1 : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  rw [Real.log_mul (mul_pos hA (Real.rpow_pos_of_pos hN _)).ne' (Real.rpow_pos_of_pos hΔ _).ne',
    Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN, Real.log_rpow hΔ]
  field_simp
  ring

/-- **Step 1** in deviations (Miao, p. 633): if `n_t = (y_t − a_t)/(1 − α) + ln Δ_t` at every
date and in the steady state (`Δ = 1`, `A = 1`), then `n̂_t = (ŷ_t − a_t)/(1 − α) + Δ̂_t`. -/
theorem mp_labor_dev {α n y a d n0 y0 : ℝ} (ht : n = (y - a) / (1 - α) + d)
    (hs : n0 = (y0 - 0) / (1 - α) + 0) :
    n - n0 = ((y - y0) - a) / (1 - α) + d := by
  rw [ht, hs]
  ring

/-- `g(π) = (1 − θe^{(ε−1)π})/(1 − θ)`, the value of `(P*/P)^{1−ε}` implied by (19.13). -/
noncomputable def mpG (ε θ x : ℝ) : ℝ := (1 - θ * Real.exp ((ε - 1) * x)) / (1 - θ)

/-- `h(π) = θe^{bπ} + (1 − θ)g(π)^c − 1`, `b = ε/(1 − α)`, `c = ε/((1 − α)(ε − 1))`. -/
noncomputable def mpH (α ε θ x : ℝ) : ℝ :=
  θ * Real.exp (ε / (1 - α) * x) + (1 - θ) * mpG ε θ x ^ (ε / ((1 - α) * (ε - 1))) - 1

/-- `h'(π) = θb(e^{bπ} − g(π)^{c−1}e^{(ε−1)π})`. -/
noncomputable def mpHd (α ε θ x : ℝ) : ℝ :=
  θ * (ε / (1 - α)) * Real.exp (ε / (1 - α) * x) -
    θ * (ε / (1 - α)) * mpG ε θ x ^ (ε / ((1 - α) * (ε - 1)) - 1) * Real.exp ((ε - 1) * x)

/-- The coefficient `K = (1 − α + αε)εθ/(2(1 − α)²(1 − θ))` of `π_t²` (Miao, p. 633). -/
noncomputable def mpK (α ε θ : ℝ) : ℝ := (1 - α + α * ε) * ε * θ / (2 * (1 - α) ^ 2 * (1 - θ))

/-- `Θ = (1 − α)/(1 − α + αε)` (Miao, p. 633). -/
noncomputable def mpTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- **The dispersion recursion** (Miao, p. 633, "By (19.13) and (19.17)"). Let
`P, P_{−1}, P* > 0`, `θ ≠ 1`, `ε ≠ 1`, `α ≠ 1`, `π = ln(P/P_{−1})`. If (19.13)
`P^{1−ε} = θP_{−1}^{1−ε} + (1 − θ)P*^{1−ε}` and (19.17)
`Δ = θ(P/P_{−1})^{ε/(1−α)}Δ_{−1} + (1 − θ)(P*/P)^{−ε/(1−α)}` hold, then
`Δ = θe^{bπ}Δ_{−1} + (1 − θ)g(π)^c`. -/
theorem mp_dispersion_recursion {α ε θ P Pm Ps Δ Δm : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1)
    (hθ : θ ≠ 1) (hP : 0 < P) (hPm : 0 < Pm) (hPs : 0 < Ps)
    (h13 : P ^ (1 - ε) = θ * Pm ^ (1 - ε) + (1 - θ) * Ps ^ (1 - ε))
    (h17 : Δ = θ * (P / Pm) ^ (ε / (1 - α)) * Δm + (1 - θ) * (Ps / P) ^ (-(ε / (1 - α)))) :
    Δ = θ * Real.exp (ε / (1 - α) * Real.log (P / Pm)) * Δm +
      (1 - θ) * mpG ε θ (Real.log (P / Pm)) ^ (ε / ((1 - α) * (ε - 1))) := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have he : (ε - 1) ≠ 0 := sub_ne_zero.2 hε
  have hPP := div_pos hP hPm
  have hg : mpG ε θ (Real.log (P / Pm)) = (Ps / P) ^ (1 - ε) := by
    simp only [mpG]
    rw [eq_comm, eq_div_iff h1, Real.div_rpow hPs.le hP.le, div_mul_eq_mul_div,
      div_eq_iff (Real.rpow_pos_of_pos hP _).ne']
    have hx : Real.exp ((ε - 1) * Real.log (P / Pm)) * P ^ (1 - ε) = Pm ^ (1 - ε) := by
      rw [Real.rpow_def_of_pos hP, Real.rpow_def_of_pos hPm, ← Real.exp_add,
        Real.log_div hP.ne' hPm.ne']
      congr 1
      ring
    linear_combination (-1) * h13 + θ * hx
  rw [h17, hg, ← Real.rpow_mul (div_pos hPs hP).le, Real.rpow_def_of_pos hPP,
    show (1 - ε) * (ε / ((1 - α) * (ε - 1))) = -(ε / (1 - α)) by field_simp; ring]
  ring_nf

/-- Miao, p. 633: with `δ_t = Δ_t − 1`, the dispersion recursion is exactly
`δ_t = θδ_{t−1} + h(π_t) + θ(e^{bπ_t} − 1)δ_{t−1}`. -/
theorem mp_dispersion_delta {α ε θ x Δ Δm : ℝ}
    (h : Δ = θ * Real.exp (ε / (1 - α) * x) * Δm +
      (1 - θ) * mpG ε θ x ^ (ε / ((1 - α) * (ε - 1)))) :
    Δ - 1 = θ * (Δm - 1) + mpH α ε θ x + θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1) := by
  rw [h, mpH]
  ring

/-! ### The second-order expansion of `h` -/

/-- **A second-order Peano remainder.** If `φ` has derivative `φ'` near `0`, `φ(0) = 0`,
`φ'(0) = 0` and `φ'` has derivative `L` at `0`, then `φ(x) = (L/2)x² + o(x²)`: for every
`ε > 0` there is `δ > 0` with `|φ(x) − (L/2)x²| ≤ εx²` for `|x| < δ`. -/
theorem mp_peano2 {φ φ' : ℝ → ℝ} {L : ℝ} (hd : ∀ᶠ x in 𝓝 0, HasDerivAt φ (φ' x) x)
    (h0 : φ 0 = 0) (h0' : φ' 0 = 0) (h2 : HasDerivAt φ' L 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |φ x - L / 2 * x ^ 2| ≤ ε * x ^ 2 := by
  intro ε hε
  have ho := (hasDerivAt_iff_isLittleO_nhds_zero.1 h2).def hε
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 (hd.and ho)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hin : ∀ y ∈ Set.Icc (-|x|) |x|, |y| < δ := fun y hy => (abs_le.2 hy).trans_lt hx
  have hP' : ∀ y ∈ Set.Icc (-|x|) |x|, HasDerivAt φ (φ' y) y ∧ |φ' y - L * y| ≤ ε * |y| := by
    intro y hy
    obtain ⟨h1, h2⟩ := hP (show dist y 0 < δ by rw [Real.dist_eq, sub_zero]; exact hin y hy)
    refine ⟨h1, ?_⟩
    simpa [h0', smul_eq_mul, mul_comm] using h2
  have hψ : ∀ y ∈ Set.Icc (-|x|) |x|, HasDerivWithinAt (fun z => φ z - L / 2 * z ^ 2)
      (φ' y - L * y) (Set.Icc (-|x|) |x|) y := by
    intro y hy
    refine (((hP' y hy).1.sub ((hasDerivAt_pow 2 y).const_mul (L / 2))).congr_deriv ?_)
      |>.hasDerivWithinAt
    push_cast
    ring
  have hbd : ∀ y ∈ Set.Icc (-|x|) |x|, ‖φ' y - L * y‖ ≤ ε * |x| := by
    intro y hy
    rw [Real.norm_eq_abs]
    exact (hP' y hy).2.trans (mul_le_mul_of_nonneg_left (abs_le.2 hy) hε.le)
  have hmv := (convex_Icc (-|x|) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le hψ hbd
    (show (0 : ℝ) ∈ Set.Icc (-|x|) |x| by simp)
    (show x ∈ Set.Icc (-|x|) |x| from ⟨neg_abs_le x, le_abs_self x⟩)
  simp only [h0, Real.norm_eq_abs, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero] at hmv
  calc |φ x - L / 2 * x ^ 2| ≤ ε * |x| * |x| := hmv
    _ = ε * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- `g(0) = 1`. -/
theorem mp_G_zero {ε θ : ℝ} (hθ : θ ≠ 1) : mpG ε θ 0 = 1 := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  simp [mpG, h1]

/-- Miao, p. 635 ("the relative price distortion is removed"): under zero inflation
(`P_t = P_{t−1}`) the dispersion recursion is `Δ_t − 1 = θ(Δ_{t−1} − 1)` (`θ ≠ 1`), so dispersion
stays at `1` if it starts there and otherwise decays to `1` geometrically. -/
theorem mp_dispersion_zero_inflation {α ε θ Δ Δm : ℝ} (hθ : θ ≠ 1)
    (h : Δ = θ * Real.exp (ε / (1 - α) * 0) * Δm +
      (1 - θ) * mpG ε θ 0 ^ (ε / ((1 - α) * (ε - 1)))) :
    Δ - 1 = θ * (Δm - 1) := by
  rw [h, mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow]
  ring

/-- `g` has derivative `−θ(ε − 1)e^{(ε−1)π}/(1 − θ)`. -/
theorem mp_hasDerivAt_G (ε θ x : ℝ) :
    HasDerivAt (mpG ε θ) (-(θ * (ε - 1) * Real.exp ((ε - 1) * x)) / (1 - θ)) x := by
  have h := ((((hasDerivAt_id' x).const_mul (ε - 1)).exp).const_mul θ).const_sub 1
  refine (h.div_const (1 - θ)).congr_deriv ?_
  ring

/-- `g > 0` near `0`. -/
theorem mp_G_pos_near {ε θ : ℝ} (hθ1 : θ < 1) :
    ∀ᶠ x in 𝓝 0, 0 < mpG ε θ x := by
  have hc : ContinuousAt (mpG ε θ) 0 := (mp_hasDerivAt_G ε θ 0).continuousAt
  have h1 : (0 : ℝ) < mpG ε θ 0 := by rw [mp_G_zero hθ1.ne]; exact one_pos
  exact hc.eventually (lt_mem_nhds h1)
    |>.mono fun x hx => hx

/-- `h(0) = 0`. -/
theorem mp_h_zero {α ε θ : ℝ} (hθ : θ ≠ 1) : mpH α ε θ 0 = 0 := by
  simp only [mpH, mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow]
  ring

/-- `h'(0) = 0`. -/
theorem mp_hd_zero {α ε θ : ℝ} (hθ : θ ≠ 1) : mpHd α ε θ 0 = 0 := by
  simp only [mpHd, mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow]
  ring

/-- `h` has derivative `h' = mpHd` wherever `g > 0` (`α ≠ 1`, `ε ≠ 1`, `θ ≠ 1`). -/
theorem mp_hasDerivAt_h {α ε θ x : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1) (hθ : θ ≠ 1)
    (hg : 0 < mpG ε θ x) : HasDerivAt (mpH α ε θ) (mpHd α ε θ x) x := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have he : (ε - 1) ≠ 0 := sub_ne_zero.2 hε
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hA := (((hasDerivAt_id' x).const_mul (ε / (1 - α))).exp).const_mul θ
  have hB := ((mp_hasDerivAt_G ε θ x).rpow_const (p := ε / ((1 - α) * (ε - 1)))
    (Or.inl hg.ne')).const_mul (1 - θ)
  refine ((hA.add hB).sub_const 1).congr_deriv ?_
  simp only [mpHd]
  field_simp
  ring

/-- `h'` has derivative `2K` at `0`. -/
theorem mp_hasDerivAt_hd {α ε θ : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1) (hθ : θ ≠ 1) :
    HasDerivAt (mpHd α ε θ) (2 * mpK α ε θ) 0 := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have he : (ε - 1) ≠ 0 := sub_ne_zero.2 hε
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hA := (((hasDerivAt_id' (0 : ℝ)).const_mul (ε / (1 - α))).exp).const_mul
    (θ * (ε / (1 - α)))
  have hB := (((mp_hasDerivAt_G ε θ 0).rpow_const (p := ε / ((1 - α) * (ε - 1)) - 1)
    (Or.inl (by rw [mp_G_zero hθ]; exact one_ne_zero))).const_mul (θ * (ε / (1 - α)))).mul
    (((hasDerivAt_id' (0 : ℝ)).const_mul (ε - 1)).exp)
  refine (hA.sub hB).congr_deriv ?_
  simp only [mul_zero, Real.exp_zero, mp_G_zero hθ, Real.one_rpow, mpK]
  field_simp
  ring

/-- **The second-order expansion of `h`** (Miao, p. 633): for `θ < 1`, `ε ≠ 1`, `α ≠ 1`,
`h(π) = Kπ² + o(π²)`. -/
theorem mp_h_expansion {α ε θ : ℝ} (hα : α ≠ 1) (hε : ε ≠ 1) (hθ1 : θ < 1) :
    ∀ ε' > 0, ∃ δ > 0, ∀ x, |x| < δ → |mpH α ε θ x - mpK α ε θ * x ^ 2| ≤ ε' * x ^ 2 := by
  intro ε' hε'
  obtain ⟨δ, hδ, h⟩ := mp_peano2 ((mp_G_pos_near hθ1).mono fun x hx =>
    mp_hasDerivAt_h hα hε hθ1.ne hx) (mp_h_zero hθ1.ne) (mp_hd_zero hθ1.ne)
    (mp_hasDerivAt_hd hα hε hθ1.ne) ε' hε'
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := h x hx
  rwa [show 2 * mpK α ε θ / 2 = mpK α ε θ by ring] at this

/-- **The second-order dispersion law** (Miao, p. 633,
`Δ̂_t = θΔ̂_{t−1} + (1 − α + αε)εθ/(2(1 − α)²(1 − θ)) π_t²`). For `0 ≤ θ < 1`, `ε > 1`,
`α < 1` and every `ε' > 0` there is `δ > 0` such that whenever (19.13) and (19.17) hold with
`|π_t| < δ`, `π_t = ln(P_t/P_{t−1})`,
`|(Δ_t − 1) − θ(Δ_{t−1} − 1) − Kπ_t²| ≤ ε'π_t² + 2θb|π_t||Δ_{t−1} − 1|`. -/
theorem mp_dispersion_second_order {α ε θ : ℝ} (hα : α < 1) (hε : 1 < ε) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) : ∀ ε' > 0, ∃ δ > 0, ∀ P Pm Ps Δ Δm : ℝ, 0 < P → 0 < Pm → 0 < Ps →
      P ^ (1 - ε) = θ * Pm ^ (1 - ε) + (1 - θ) * Ps ^ (1 - ε) →
      Δ = θ * (P / Pm) ^ (ε / (1 - α)) * Δm + (1 - θ) * (Ps / P) ^ (-(ε / (1 - α))) →
      |Real.log (P / Pm)| < δ →
      |(Δ - 1) - θ * (Δm - 1) - mpK α ε θ * Real.log (P / Pm) ^ 2| ≤
        ε' * Real.log (P / Pm) ^ 2 + 2 * θ * (ε / (1 - α)) * |Real.log (P / Pm)| * |Δm - 1| := by
  intro ε' hε'
  have hb : 0 < ε / (1 - α) := div_pos (by linarith) (by linarith)
  obtain ⟨δ, hδ, hh⟩ := mp_h_expansion hα.ne hε.ne' hθ1 ε' hε'
  refine ⟨min δ ((1 - α) / ε), lt_min hδ (div_pos (by linarith) (by linarith)),
    fun P Pm Ps Δ Δm hP hPm hPs h13 h17 hx => ?_⟩
  set x := Real.log (P / Pm)
  have hrec := mp_dispersion_delta (mp_dispersion_recursion hα.ne hε.ne' hθ1.ne hP hPm hPs h13
    h17)
  have hbx : |ε / (1 - α) * x| ≤ 1 := by
    rw [abs_mul, abs_of_pos hb]
    have := (lt_min_iff.1 hx).2
    rw [lt_div_iff₀ (by linarith)] at this
    rw [div_mul_eq_mul_div, div_le_one (by linarith)]
    linarith
  have he := Real.abs_exp_sub_one_le hbx
  rw [abs_mul, abs_of_pos hb] at he
  have h1 := hh x (lt_min_iff.1 hx).1
  have e : (Δ - 1) - θ * (Δm - 1) - mpK α ε θ * x ^ 2 =
      (mpH α ε θ x - mpK α ε θ * x ^ 2) + θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1) := by
    rw [hrec]
    ring
  rw [e]
  calc |(mpH α ε θ x - mpK α ε θ * x ^ 2) + θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1)|
      ≤ |mpH α ε θ x - mpK α ε θ * x ^ 2| +
          |θ * (Real.exp (ε / (1 - α) * x) - 1) * (Δm - 1)| := abs_add_le _ _
    _ ≤ ε' * x ^ 2 + 2 * θ * (ε / (1 - α)) * |x| * |Δm - 1| := by
        refine add_le_add h1 ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hθ0]
        have := mul_le_mul_of_nonneg_left he hθ0
        have := mul_le_mul_of_nonneg_right this (abs_nonneg (Δm - 1))
        linarith

/-- Miao, p. 633: the log deviation `Δ̂ = ln Δ` and `Δ − 1` agree to second order:
`|ln Δ − (Δ − 1)| ≤ 2(Δ − 1)²` for `|Δ − 1| ≤ 1/2`. -/
theorem mp_log_dev {Δ : ℝ} (h : |Δ - 1| ≤ 1 / 2) : |Real.log Δ - (Δ - 1)| ≤ 2 * (Δ - 1) ^ 2 := by
  have hl := Real.abs_log_sub_add_sum_range_le (x := 1 - Δ) (by rw [abs_sub_comm]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, Nat.cast_zero, pow_one,
    div_one, sub_sub_cancel] at hl
  have hb : |1 - Δ| ^ (1 + 1) / (1 - |1 - Δ|) ≤ 2 * (Δ - 1) ^ 2 := by
    rw [abs_sub_comm, div_le_iff₀ (by linarith), show 1 + 1 = 2 by rfl, sq_abs]
    nlinarith [sq_nonneg (Δ - 1)]
  have e : Real.log Δ - (Δ - 1) = 1 - Δ + Real.log Δ := by ring
  rw [e]
  exact hl.trans hb

/-! ### The discounted sum -/

/-- `K/(1 − θβ) = εθ/(2(1 − α)Θ(1 − θ)(1 − θβ))` (Miao, p. 633). -/
theorem mp_K_Theta {α ε θ β : ℝ} (hα : α ≠ 1) (hd : 1 - α + α * ε ≠ 0) (hθ : θ ≠ 1)
    (hθβ : 1 - θ * β ≠ 0) :
    mpK α ε θ / (1 - θ * β) =
      ε * θ / (2 * (1 - α) * mpTheta α ε * (1 - θ) * (1 - θ * β)) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  simp only [mpK, mpTheta]
  field_simp

/-- A path satisfying `d_t = θd_{t−1} + Kπ_t²` from `d_{−1} = 0` with `|π_t| ≤ M` and
`0 ≤ θ < 1` is bounded by `|K|M²/(1 − θ)`. -/
theorem mp_disp_bounded {θ K M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (pin d : ℕ → ℝ)
    (hM : ∀ t, |pin t| ≤ M) (h0 : d 0 = K * pin 0 ^ 2)
    (hs : ∀ t, d (t + 1) = θ * d t + K * pin (t + 1) ^ 2) :
    ∀ t, |d t| ≤ |K| * M ^ 2 / (1 - θ) := by
  have hq : ∀ t, |K * pin t ^ 2| ≤ |K| * M ^ 2 := fun t => by
    rw [abs_mul, abs_pow]
    have h0' : 0 ≤ |pin t| := abs_nonneg _
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0' (hM t) 2) (abs_nonneg K)
  have hB : 0 ≤ |K| * M ^ 2 := by positivity
  intro t
  rw [le_div_iff₀ (by linarith)]
  induction t with
  | zero =>
    rw [h0]
    nlinarith [hq 0]
  | succ n ih =>
    rw [hs]
    have h1 : |θ * d n + K * pin (n + 1) ^ 2| ≤ θ * |d n| + |K| * M ^ 2 := by
      have := abs_add_le (θ * d n) (K * pin (n + 1) ^ 2)
      rw [abs_mul, abs_of_nonneg hθ0] at this
      linarith [hq (n + 1)]
    have h2 : θ * |d n| ≤ θ * (|K| * M ^ 2 / (1 - θ)) := by
      apply mul_le_mul_of_nonneg_left _ hθ0
      rw [le_div_iff₀ (by linarith)]
      exact ih
    have hne : (1 : ℝ) - θ ≠ 0 := ne_of_gt (by linarith)
    have h3 : θ * (|K| * M ^ 2 / (1 - θ)) + |K| * M ^ 2 = |K| * M ^ 2 / (1 - θ) := by
      field_simp
      ring
    nlinarith

/-- **Step 1, the discounted sum** (Miao, p. 633). If `Δ̂_t = θΔ̂_{t−1} + Kπ_t²` with
`Δ̂_{−1} = 0` (so `Δ̂_0 = Kπ_0²`), `0 ≤ β < 1`, `0 ≤ θ < 1` and `π` is bounded, then
`∑βᵗΔ̂_t = K/(1 − θβ) · ∑βᵗπ_t²`. -/
theorem mp_dispersion_sum {θ β K M : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (pin d : ℕ → ℝ) (hM : ∀ t, |pin t| ≤ M) (h0 : d 0 = K * pin 0 ^ 2)
    (hs : ∀ t, d (t + 1) = θ * d t + K * pin (t + 1) ^ 2) :
    ∑' t, β ^ t * d t = K / (1 - θ * β) * ∑' t, β ^ t * pin t ^ 2 := by
  have hdb := mp_disp_bounded hθ0 hθ1 pin d hM h0 hs
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hsd : Summable fun t => β ^ t * d t := by
    refine Summable.of_norm_bounded (g := fun t => |K| * M ^ 2 / (1 - θ) * β ^ t)
      (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hdb t) (pow_nonneg hβ0 t)
  have hsp : Summable fun t => β ^ t * pin t ^ 2 := by
    refine Summable.of_norm_bounded (g := fun t => M ^ 2 * β ^ t) (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM t) 2)
      (pow_nonneg hβ0 t)
  have hθβ : 1 - θ * β ≠ 0 := by nlinarith
  have e1 := hsd.tsum_eq_zero_add
  have e2 := hsp.tsum_eq_zero_add
  have hshift : ∀ t, β ^ (t + 1) * d (t + 1) =
      θ * β * (β ^ t * d t) + K * (β ^ (t + 1) * pin (t + 1) ^ 2) := fun t => by
    rw [hs, pow_succ]
    ring
  have hsum2 : Summable fun t => β ^ (t + 1) * pin (t + 1) ^ 2 :=
    (summable_nat_add_iff 1).2 hsp
  rw [tsum_congr hshift, (hsd.mul_left (θ * β)).tsum_add (hsum2.mul_left K), tsum_mul_left,
    tsum_mul_left] at e1
  have e3 : ∑' t, β ^ (t + 1) * pin (t + 1) ^ 2 = (∑' t, β ^ t * pin t ^ 2) - pin 0 ^ 2 := by
    simp only [pow_zero, one_mul] at e2
    linarith
  rw [e3] at e1
  simp only [pow_zero, one_mul, h0] at e1
  rw [div_mul_eq_mul_div, eq_div_iff hθβ]
  linear_combination e1

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary policy design: the quadratic approximation to utility (Miao §19.2.2)

Miao, §19.2.2, pp. 631–635. Hats are log deviations from the zero-inflation steady state
`(C̄, N̄)`: `C = C̄e^ĉ`, `N = N̄e^n̂`.

* `mp_taylor_exp` (p. 632): `(C − C̄)/C̄ = e^ĉ − 1 = ĉ + ĉ²/2 + R`, `|R| ≤ |ĉ|³` for
  `|ĉ| ≤ 1`.
* `mp_uCC`, `mp_uNN`: for (19.1), `u_CC C/u_C = −γ` and `u_NN N/u_N = ν`;
  `mp_eq_19_30_truncation`: the book's second display (the Taylor expansion of `u` in levels,
  with `(C − C̄)/C̄` replaced by `ĉ + ĉ²/2`) equals the right side of (19.30) times `u_C C` plus
  the explicit third- and fourth-order terms the book drops.
* `mp_util_exact`: the exact identity
  `(u_t − u)/(u_C C) = (e^{(1−γ)ĉ} − 1)/(1 − γ) + (u_N N/(u_C C))(e^{(1+ν)n̂} − 1)/(1 + ν)`.
* `eq_19_30`: **(19.30) as a precise Taylor statement**: the remainder
  `(u_t − u)/(u_C C) − [ĉ + (1 − γ)ĉ²/2 + (u_N N/(u_C C))(n̂ + (1 + ν)n̂²/2)]` is bounded by
  `(1 − γ)²|ĉ|³ + |u_N N/(u_C C)|(1 + ν)²|n̂|³` when `|(1 − γ)ĉ|, |(1 + ν)n̂| ≤ 1`, and it is
  `o(ĉ² + n̂²)` (`eq_19_30_littleO`).
* Step 2 (pp. 633–634): `mp_step2_subst` (substituting `ĉ = ŷ`, Step 1's `n̂`),
  `mp_step2_phi` (`u_N N/(u_C C) = −(1 − α)(1 − Φ)` from `−u_N/u_C = MPN(1 − Φ)`,
  `MPN = (1 − α)Y/N`, `Y = C`), `mp_step2_small` (the small-distortion step: the expression
  equals the book's next line plus `Φ × [second-order terms]`, the term the book neglects) and
  `mp_step2_square` (completing the square with `ŷ^f = (1 + ν)a/D`, `x* = Φ(1 − α)/D`:
  `−½Λ(x − x*)² − (1 − α)Δ̂ + t.i.p.`, `Λ = γ + (ν + α)/(1 − α)`, the t.i.p. `mpTip` depending
  only on `a` and `Φ`).
* Step 3 (p. 635): `mp_step3`: for bounded paths and the second-order dispersion law,
  `∑βᵗ[−½Λ(x_t − x*)² − (1 − α)Δ̂_t] = −(Ω/2)∑βᵗ[λ(x_t − x*)² + π_t²]`,
  `Ω = εθ/(Θ(1 − θ)(1 − θβ))`, `λ = Λ/Ω`; `mp_omega_pos`, `mp_lam_pos`: `Ω, λ > 0`;
  `mp_xstar_zero_iff`: `x* = 0` iff `Φ = 0` (distortions move `x*` only, `λ` does not involve
  `Φ`).

Expectations are taken path by path: the identities of Step 3 hold for every realisation, so
they hold under `E` whenever the sums may be interchanged with it.
-/

namespace Miao.NewKeynesian

/-! ### The Taylor expansion of `u` -/

/-- Miao, p. 632: `(e^{c} − e^{c̄})/e^{c̄} = ĉ + ĉ²/2 + R` with `ĉ = c − c̄` and `|R| ≤ |ĉ|³` for
`|ĉ| ≤ 1`. -/
theorem mp_taylor_exp {c cbar : ℝ} (h : |c - cbar| ≤ 1) :
    |(Real.exp c - Real.exp cbar) / Real.exp cbar - ((c - cbar) + (c - cbar) ^ 2 / 2)| ≤
      |c - cbar| ^ 3 := by
  have e : (Real.exp c - Real.exp cbar) / Real.exp cbar = Real.exp (c - cbar) - 1 := by
    rw [Real.exp_sub]
    field_simp
  have hb := Real.exp_bound h (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.succ_eq_add_one] at hb
  norm_num at hb
  rw [e]
  have e2 : Real.exp (c - cbar) - 1 - ((c - cbar) + (c - cbar) ^ 2 / 2) =
      Real.exp (c - cbar) - (1 + (c - cbar) + (c - cbar) ^ 2 / 2) := by ring
  rw [e2]
  refine hb.trans ?_
  have := pow_nonneg (abs_nonneg (c - cbar)) 3
  nlinarith

/-- For (19.1), `u_CC = −γC^{−γ−1}`, so `u_CC C/u_C = −γ` (`C > 0`). -/
theorem mp_uCC {γ C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun c => c ^ (-γ)) (-γ * C ^ (-γ - 1)) C ∧
      -γ * C ^ (-γ - 1) * C / C ^ (-γ) = -γ := by
  refine ⟨Real.hasDerivAt_rpow_const (Or.inl hC.ne'), ?_⟩
  rw [Real.rpow_sub hC, Real.rpow_one]
  field_simp

/-- For (19.1), `u_N = −χN^ν` has derivative `u_NN = −χνN^{ν−1}`, so `u_NN N/u_N = ν`
(`N, χ > 0`). -/
theorem mp_uNN {χ ν N : ℝ} (hχ : 0 < χ) (hN : 0 < N) :
    HasDerivAt (fun n => -(χ * n ^ ν)) (-(χ * (ν * N ^ (ν - 1)))) N ∧
      -(χ * (ν * N ^ (ν - 1))) * N / (-(χ * N ^ ν)) = ν := by
  refine ⟨((Real.hasDerivAt_rpow_const (Or.inl hN.ne')).const_mul χ).neg, ?_⟩
  rw [Real.rpow_sub hN, Real.rpow_one]
  have : 0 < N ^ ν := Real.rpow_pos_of_pos hN _
  field_simp

/-- **The truncation step** (Miao, p. 632, "keeping terms up to second order"). With
`u_CC C² = −γu_C C` and `u_NN N² = νu_N N`, the second display on p. 632,
`u_C C(ĉ + ĉ²/2) + u_N N(n̂ + n̂²/2) + ½u_CC C²(ĉ + ĉ²/2)² + ½u_NN N²(n̂ + n̂²/2)²`, equals
`u_C C[ĉ + (1 − γ)ĉ²/2] + u_N N[n̂ + (1 + ν)n̂²/2]` plus the third- and fourth-order terms
`−γu_C C(ĉ³ + ĉ⁴/4)/2 + νu_N N(n̂³ + n̂⁴/4)/2`. -/
theorem mp_eq_19_30_truncation {γ ν uCC uC uNN uN c n : ℝ} (hc : uCC = -γ * uC)
    (hn : uNN = ν * uN) :
    uC * (c + c ^ 2 / 2) + uN * (n + n ^ 2 / 2) + 1 / 2 * uCC * (c + c ^ 2 / 2) ^ 2 +
        1 / 2 * uNN * (n + n ^ 2 / 2) ^ 2 =
      uC * (c + (1 - γ) / 2 * c ^ 2) + uN * (n + (1 + ν) / 2 * n ^ 2) +
        (-γ * uC * (c ^ 3 + c ^ 4 / 4) / 2 + ν * uN * (n ^ 3 + n ^ 4 / 4) / 2) := by
  rw [hc, hn]
  ring

/-- **The exact form of `(u_t − u)/(u_C C)`** (Miao, p. 632). For (19.1) with `γ ≠ 1`,
`ν ≠ −1`, `C̄, N̄ > 0`, `C = C̄e^ĉ`, `N = N̄e^n̂`, `u_C C = C̄^{−γ}C̄` and
`u_N N = −χN̄^νN̄`: `(u_t − u)/(u_C C) = (e^{(1−γ)ĉ} − 1)/(1 − γ) +
(u_N N/(u_C C))(e^{(1+ν)n̂} − 1)/(1 + ν)`. -/
theorem mp_util_exact {γ χ ν C N c n : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hC : 0 < C)
    (hN : 0 < N) :
    (mpU γ χ ν (C * Real.exp c) (N * Real.exp n) - mpU γ χ ν C N) / (C ^ (-γ) * C) =
      (Real.exp ((1 - γ) * c) - 1) / (1 - γ) +
        (-(χ * N ^ ν) * N) / (C ^ (-γ) * C) * ((Real.exp ((1 + ν) * n) - 1) / (1 + ν)) := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h2 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  have hCg : C ^ (-γ) * C = C ^ (1 - γ) := by
    rw [sub_eq_neg_add, Real.rpow_add hC, Real.rpow_one]
  have hNn : N ^ ν * N = N ^ (1 + ν) := by
    rw [add_comm, Real.rpow_add hN, Real.rpow_one]
  have hCp : 0 < C ^ (1 - γ) := Real.rpow_pos_of_pos hC _
  simp only [mpU]
  rw [Real.mul_rpow hC.le (Real.exp_pos c).le, Real.mul_rpow hN.le (Real.exp_pos n).le,
    ← Real.exp_mul, ← Real.exp_mul, hCg,
    show -(χ * N ^ ν) * N = -(χ * N ^ (1 + ν)) by rw [← hNn]; ring, mul_comm c, mul_comm n]
  field_simp
  ring

/-- `|(e^{kx} − 1)/k − x − kx²/2| ≤ k²|x|³` for `k ≠ 0`, `|kx| ≤ 1`. -/
theorem mp_exp_quad_bound {k x : ℝ} (hk : k ≠ 0) (h : |k * x| ≤ 1) :
    |(Real.exp (k * x) - 1) / k - (x + k / 2 * x ^ 2)| ≤ k ^ 2 * |x| ^ 3 := by
  have hb := mp_taylor_exp (c := k * x) (cbar := 0) (by simpa using h)
  simp only [sub_zero, Real.exp_zero, div_one] at hb
  have e : (Real.exp (k * x) - 1) / k - (x + k / 2 * x ^ 2) =
      (Real.exp (k * x) - 1 - (k * x + (k * x) ^ 2 / 2)) / k := by
    field_simp
  rw [e, abs_div, div_le_iff₀ (abs_pos.2 hk)]
  calc |Real.exp (k * x) - 1 - (k * x + (k * x) ^ 2 / 2)| ≤ |k * x| ^ 3 := hb
    _ = k ^ 2 * |x| ^ 3 * |k| := by
        rw [abs_mul, mul_pow, ← sq_abs k]
        ring

/-- **(19.30)** (Miao, p. 632), as a precise Taylor statement. For (19.1) with `γ ≠ 1`,
`ν ≠ −1`, `C̄, N̄ > 0`, write `s = u_N N/(u_C C)`. Then
`(u_t − u)/(u_C C) = ĉ + (1 − γ)ĉ²/2 + s(n̂ + (1 + ν)n̂²/2) + R` with
`|R| ≤ (1 − γ)²|ĉ|³ + |s|(1 + ν)²|n̂|³` whenever `|(1 − γ)ĉ| ≤ 1` and `|(1 + ν)n̂| ≤ 1`. -/
theorem eq_19_30 {γ χ ν C N c n : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hC : 0 < C) (hN : 0 < N)
    (hc : |(1 - γ) * c| ≤ 1) (hn : |(1 + ν) * n| ≤ 1) :
    |(mpU γ χ ν (C * Real.exp c) (N * Real.exp n) - mpU γ χ ν C N) / (C ^ (-γ) * C) -
        (c + (1 - γ) / 2 * c ^ 2 +
          (-(χ * N ^ ν) * N) / (C ^ (-γ) * C) * (n + (1 + ν) / 2 * n ^ 2))| ≤
      (1 - γ) ^ 2 * |c| ^ 3 + |(-(χ * N ^ ν) * N) / (C ^ (-γ) * C)| * ((1 + ν) ^ 2 * |n| ^ 3) := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h2 : (1 + ν) ≠ 0 := fun h => hν (by linarith)
  rw [mp_util_exact hγ hν hC hN]
  set s := (-(χ * N ^ ν) * N) / (C ^ (-γ) * C)
  have e : (Real.exp ((1 - γ) * c) - 1) / (1 - γ) + s * ((Real.exp ((1 + ν) * n) - 1) / (1 + ν)) -
      (c + (1 - γ) / 2 * c ^ 2 + s * (n + (1 + ν) / 2 * n ^ 2)) =
      ((Real.exp ((1 - γ) * c) - 1) / (1 - γ) - (c + (1 - γ) / 2 * c ^ 2)) +
        s * ((Real.exp ((1 + ν) * n) - 1) / (1 + ν) - (n + (1 + ν) / 2 * n ^ 2)) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add (mp_exp_quad_bound h1 hc) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (mp_exp_quad_bound h2 hn) (abs_nonneg s)

/-- **(19.30), little-o form** (Miao, p. 632): the remainder of (19.30) is `o(ĉ² + n̂²)`: for
every `ε > 0` there is `δ > 0` with `|R| ≤ ε(ĉ² + n̂²)` whenever `|ĉ|, |n̂| < δ`. -/
theorem eq_19_30_littleO {γ χ ν C N : ℝ} (hγ : γ ≠ 1) (hν : ν ≠ -1) (hC : 0 < C) (hN : 0 < N) :
    ∀ ε > 0, ∃ δ > 0, ∀ c n, |c| < δ → |n| < δ →
      |(mpU γ χ ν (C * Real.exp c) (N * Real.exp n) - mpU γ χ ν C N) / (C ^ (-γ) * C) -
        (c + (1 - γ) / 2 * c ^ 2 +
          (-(χ * N ^ ν) * N) / (C ^ (-γ) * C) * (n + (1 + ν) / 2 * n ^ 2))| ≤
      ε * (c ^ 2 + n ^ 2) := by
  intro ε hε
  set s := (-(χ * N ^ ν) * N) / (C ^ (-γ) * C)
  set B := (1 - γ) ^ 2 + |s| * (1 + ν) ^ 2 + |1 - γ| + |1 + ν| + 1
  have hB : 0 < B := by positivity
  refine ⟨min (1 / B) (ε / B), lt_min (div_pos one_pos hB) (div_pos hε hB),
    fun c n hc hn => ?_⟩
  have hc1 := (lt_min_iff.1 hc).1
  have hn1 := (lt_min_iff.1 hn).1
  have hc2 := (lt_min_iff.1 hc).2
  have hn2 := (lt_min_iff.1 hn).2
  have hc1' : |c| * B < 1 := by rwa [lt_div_iff₀ hB] at hc1
  have hn1' : |n| * B < 1 := by rwa [lt_div_iff₀ hB] at hn1
  have hcB : |c| * B < ε := by rwa [lt_div_iff₀ hB] at hc2
  have hnB : |n| * B < ε := by rwa [lt_div_iff₀ hB] at hn2
  have hkc : |(1 - γ) * c| ≤ 1 := by
    rw [abs_mul]
    have : |1 - γ| * |c| ≤ B * |c| := mul_le_mul_of_nonneg_right (by
      simp only [B]; nlinarith [sq_nonneg (1 - γ), abs_nonneg s, sq_nonneg (1 + ν),
        abs_nonneg (1 + ν)]) (abs_nonneg c)
    linarith [mul_comm B |c|]
  have hkn : |(1 + ν) * n| ≤ 1 := by
    rw [abs_mul]
    have : |1 + ν| * |n| ≤ B * |n| := mul_le_mul_of_nonneg_right (by
      simp only [B]; nlinarith [sq_nonneg (1 - γ), mul_nonneg (abs_nonneg s) (sq_nonneg (1 + ν)),
        abs_nonneg (1 - γ)]) (abs_nonneg n)
    linarith [mul_comm B |n|]
  refine (eq_19_30 hγ hν hC hN hkc hkn).trans ?_
  have hc3 : |c| ^ 3 = |c| * c ^ 2 := by rw [pow_succ, sq_abs]; ring
  have hn3 : |n| ^ 3 = |n| * n ^ 2 := by rw [pow_succ, sq_abs]; ring
  rw [hc3, hn3]
  have hA1 : (1 - γ) ^ 2 ≤ B := by
    simp only [B]; nlinarith [mul_nonneg (abs_nonneg s) (sq_nonneg (1 + ν)), abs_nonneg (1 - γ),
      abs_nonneg (1 + ν)]
  have hA2 : |s| * (1 + ν) ^ 2 ≤ B := by
    simp only [B]; nlinarith [sq_nonneg (1 - γ), abs_nonneg (1 - γ), abs_nonneg (1 + ν)]
  have hc0 := abs_nonneg c
  have hn0 := abs_nonneg n
  have e1 : (1 - γ) ^ 2 * (|c| * c ^ 2) ≤ ε * c ^ 2 := by
    have : (1 - γ) ^ 2 * |c| ≤ ε := by nlinarith
    nlinarith [sq_nonneg c]
  have e2 : |s| * ((1 + ν) ^ 2 * (|n| * n ^ 2)) ≤ ε * n ^ 2 := by
    have : |s| * (1 + ν) ^ 2 * |n| ≤ ε := by nlinarith
    nlinarith [sq_nonneg n]
  linarith

/-! ### Step 2 -/

/-- **Step 2, substitution** (Miao, p. 633). With `ĉ = ŷ` and Step 1's
`n̂ = (ŷ − a)/(1 − α) + Δ̂` (`α ≠ 1`), the right side of (19.30) equals
`ŷ + (1 − γ)ŷ²/2 + (s/(1 − α))[ŷ + (1 − α)Δ̂ + (1 + ν)(ŷ − a)²/(2(1 − α))]` plus the t.i.p.
`−sa/(1 − α)` plus the terms `s(1 + ν)((ŷ − a)Δ̂/(1 − α) + Δ̂²/2)` of order three and four
(`Δ̂` is of second order, Step 1). -/
theorem mp_step2_subst {α γ ν s y a d : ℝ} (hα : α ≠ 1) :
    y + (1 - γ) / 2 * y ^ 2 + s * (((y - a) / (1 - α) + d) +
        (1 + ν) / 2 * ((y - a) / (1 - α) + d) ^ 2) =
      y + (1 - γ) / 2 * y ^ 2 +
        s / (1 - α) * (y + (1 - α) * d + (1 + ν) / (2 * (1 - α)) * (y - a) ^ 2) +
        (-(s * a / (1 - α))) + s * (1 + ν) * ((y - a) * d / (1 - α) + d ^ 2 / 2) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  field_simp
  ring

/-- **Step 2, the distortion `Φ`** (Miao, p. 634). If `−u_N/u_C = MPN(1 − Φ)`,
`MPN = (1 − α)Y/N` and `Y = C` (`u_C, C, N ≠ 0`), then `u_N N/(u_C C) = −(1 − α)(1 − Φ)`, so
`s/(1 − α) = −(1 − Φ)`. -/
theorem mp_step2_phi {α Φ uC uN C N Y : ℝ} (huC : uC ≠ 0) (hC : C ≠ 0) (hN : N ≠ 0)
    (hΦ : -uN / uC = (1 - α) * Y / N * (1 - Φ)) (hY : Y = C) :
    uN * N / (uC * C) = -((1 - α) * (1 - Φ)) := by
  rw [hY, div_eq_iff huC] at hΦ
  rw [div_eq_iff (mul_ne_zero huC hC)]
  have h' : uN * N = -((1 - α) * C / N * (1 - Φ) * uC) * N := by rw [← hΦ]; ring
  rw [h']
  field_simp

/-- **Step 2, small distortions** (Miao, p. 634). With `s/(1 − α) = −(1 − Φ)`, the expression
`ŷ + (1 − γ)ŷ²/2 − (1 − Φ)[ŷ + (1 − α)Δ̂ + (1 + ν)(ŷ − a)²/(2(1 − α))]` equals
`Φŷ − (1 − α)Δ̂ − ½[(1 + ν)(ŷ − a)²/(1 − α) − (1 − γ)ŷ²]` plus
`Φ[(1 − α)Δ̂ + (1 + ν)(ŷ − a)²/(2(1 − α))]`, the product of `Φ` with second-order terms that the
book neglects under the small-distortion assumption. -/
theorem mp_step2_small {α γ ν Φ y a d : ℝ} (hα : α ≠ 1) :
    y + (1 - γ) / 2 * y ^ 2 - (1 - Φ) * (y + (1 - α) * d + (1 + ν) / (2 * (1 - α)) * (y - a) ^ 2) =
      Φ * y - (1 - α) * d - 1 / 2 * ((1 + ν) / (1 - α) * (y - a) ^ 2 - (1 - γ) * y ^ 2) +
        Φ * ((1 - α) * d + (1 + ν) / (2 * (1 - α)) * (y - a) ^ 2) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  field_simp
  ring

/-- `Λ = γ + (ν + α)/(1 − α)`, the weight on `(x_t − x*)²` before normalisation. -/
noncomputable def mpLambdaBar (α γ ν : ℝ) : ℝ := γ + (ν + α) / (1 - α)

/-- The terms independent of policy in Step 2: `½Λ(ŷ^f + x*)² − (1 + ν)a²/(2(1 − α))`. -/
noncomputable def mpTip (α γ ν Φ a : ℝ) : ℝ :=
  1 / 2 * mpLambdaBar α γ ν * ((1 + ν) / (γ * (1 - α) + ν + α) * a + mpXstar α γ ν Φ) ^ 2 -
    (1 + ν) / (2 * (1 - α)) * a ^ 2

/-- **Step 2, completing the square** (Miao, p. 634). With `ŷ^f = (1 + ν)a/D`,
`x* = Φ(1 − α)/D`, `D = γ(1 − α) + ν + α ≠ 0`, `α ≠ 1`, and the output gap `x = ŷ − ŷ^f`:
`Φŷ − (1 − α)Δ̂ − ½[(1 + ν)(ŷ − a)²/(1 − α) − (1 − γ)ŷ²] =
−½Λ(x − x*)² − (1 − α)Δ̂ + t.i.p.`, with t.i.p. `mpTip` independent of `ŷ` and `Δ̂`. The
intermediate line `−½Λ[ŷ² − 2(x* + ŷ^f)ŷ] − (1 − α)Δ̂ + t.i.p.` is the second conjunct. -/
theorem mp_step2_square {α γ ν Φ y a d : ℝ} (hα : α ≠ 1) (hD : γ * (1 - α) + ν + α ≠ 0) :
    (Φ * y - (1 - α) * d - 1 / 2 * ((1 + ν) / (1 - α) * (y - a) ^ 2 - (1 - γ) * y ^ 2) =
      -(1 / 2) * mpLambdaBar α γ ν *
          (y - (1 + ν) / (γ * (1 - α) + ν + α) * a - mpXstar α γ ν Φ) ^ 2 -
        (1 - α) * d + mpTip α γ ν Φ a) ∧
    (Φ * y - (1 - α) * d - 1 / 2 * ((1 + ν) / (1 - α) * (y - a) ^ 2 - (1 - γ) * y ^ 2) =
      -(1 / 2) * mpLambdaBar α γ ν * (y ^ 2 - 2 * (mpXstar α γ ν Φ +
          (1 + ν) / (γ * (1 - α) + ν + α) * a) * y) - (1 - α) * d +
        (-(1 + ν) / (2 * (1 - α)) * a ^ 2)) := by
  have ha : (1 - α) ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  simp only [mpTip, mpLambdaBar, mpXstar]
  set D := γ * (1 - α) + ν + α with hDdef
  constructor
  · field_simp
    rw [hDdef]
    ring
  · field_simp
    rw [hDdef]
    ring

/-! ### Step 3 -/

/-- `Ω = εθ/(Θ(1 − θ)(1 − θβ))` (Miao, p. 635). -/
noncomputable def mpOmega (α ε θ β : ℝ) : ℝ := ε * θ / (mpTheta α ε * (1 - θ) * (1 - θ * β))

/-- `λ = (γ + (ν + α)/(1 − α))/Ω` (Miao, p. 635). -/
noncomputable def mpLam (α γ ν ε θ β : ℝ) : ℝ := mpLambdaBar α γ ν / mpOmega α ε θ β

/-- `Ω > 0` for `0 ≤ α < 1`, `ε > 0`, `0 < θ < 1`, `β < 1`. -/
theorem mp_omega_pos {α ε θ β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hβ1 : β < 1) : 0 < mpOmega α ε θ β := by
  have h1 : 0 < 1 - α := by linarith
  have hT : 0 < mpTheta α ε := div_pos h1 (by nlinarith)
  have hθβ : 0 < 1 - θ * β := by nlinarith
  exact div_pos (mul_pos hε hθ0) (mul_pos (mul_pos hT (by linarith)) hθβ)

/-- `λ > 0` for `γ > 0`, `ν ≥ 0` (with the conditions of `mp_omega_pos`). -/
theorem mp_lam_pos {α γ ν ε θ β : ℝ} (hγ : 0 < γ) (hν : 0 ≤ ν) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 0 < ε) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1) :
    0 < mpLam α γ ν ε θ β := by
  have h1 : 0 < 1 - α := by linarith
  exact div_pos (add_pos_of_pos_of_nonneg hγ (div_nonneg (by linarith) h1.le))
    (mp_omega_pos hα0 hα1 hε hθ0 hθ1 hβ1)

/-- **Step 3** (Miao, p. 635). Let `0 ≤ α < 1`, `ε > 0`, `0 < θ < 1`, `0 ≤ β < 1`, `π` and `x`
bounded, and `Δ̂` follow the second-order law of Step 1 (`Δ̂_0 = Kπ_0²`,
`Δ̂_{t+1} = θΔ̂_t + Kπ_{t+1}²`). Then the discounted sum of the Step 2 approximation is
`∑βᵗ[−½Λ(x_t − x*)² − (1 − α)Δ̂_t] = −(Ω/2)∑βᵗ[λ(x_t − x*)² + π_t²]`. -/
theorem mp_step3 {α γ ν ε θ β xs M : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (pin x d : ℕ → ℝ)
    (hM : ∀ t, |pin t| ≤ M) (hMx : ∀ t, |x t - xs| ≤ M) (h0 : d 0 = mpK α ε θ * pin 0 ^ 2)
    (hs : ∀ t, d (t + 1) = θ * d t + mpK α ε θ * pin (t + 1) ^ 2) :
    ∑' t, β ^ t * (-(1 / 2) * mpLambdaBar α γ ν * (x t - xs) ^ 2 - (1 - α) * d t) =
      -(mpOmega α ε θ β / 2) *
        ∑' t, β ^ t * (mpLam α γ ν ε θ β * (x t - xs) ^ 2 + pin t ^ 2) := by
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hO := mp_omega_pos hα0 hα1 hε hθ0 hθ1 hβ1
  have hsq : ∀ f : ℕ → ℝ, (∀ t, |f t| ≤ M) → Summable fun t => β ^ t * f t ^ 2 := by
    intro f hf
    refine Summable.of_norm_bounded (g := fun t => M ^ 2 * β ^ t) (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hf t) 2)
      (pow_nonneg hβ0 t)
  have hsx := hsq (fun t => x t - xs) hMx
  have hsp := hsq pin hM
  have hdb := mp_disp_bounded hθ0.le hθ1 pin d hM h0 hs
  have hsd : Summable fun t => β ^ t * d t := by
    refine Summable.of_norm_bounded (g := fun t => |mpK α ε θ| * M ^ 2 / (1 - θ) * β ^ t)
      (hg.mul_left _) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hdb t) (pow_nonneg hβ0 t)
  have hD := mp_dispersion_sum hθ0.le hθ1 hβ0 hβ1 pin d hM h0 hs
  have hθβ : 1 - θ * β ≠ 0 := by nlinarith
  have hα : α ≠ 1 := hα1.ne
  have ha : (1 - α) ≠ 0 := by linarith
  have hd : 1 - α + α * ε ≠ 0 := by nlinarith
  have hK := mp_K_Theta (β := β) hα hd hθ1.ne hθβ
  have hKO : (1 - α) * (mpK α ε θ / (1 - θ * β)) = mpOmega α ε θ β / 2 := by
    rw [hK, mpOmega]
    have hT : mpTheta α ε ≠ 0 := div_ne_zero ha hd
    have h1 : (1 - θ) ≠ 0 := by linarith
    field_simp
  have e1 : ∀ t, β ^ t * (-(1 / 2) * mpLambdaBar α γ ν * (x t - xs) ^ 2 - (1 - α) * d t) =
      (-(1 / 2) * mpLambdaBar α γ ν) * (β ^ t * (x t - xs) ^ 2) + (-(1 - α)) * (β ^ t * d t) :=
    fun t => by ring
  have e2 : ∀ t, β ^ t * (mpLam α γ ν ε θ β * (x t - xs) ^ 2 + pin t ^ 2) =
      mpLam α γ ν ε θ β * (β ^ t * (x t - xs) ^ 2) + β ^ t * pin t ^ 2 := fun t => by ring
  rw [tsum_congr e1, tsum_congr e2, (hsx.mul_left _).tsum_add (hsd.mul_left _),
    (hsx.mul_left _).tsum_add hsp, tsum_mul_left, tsum_mul_left, tsum_mul_left, hD]
  have hL : mpLam α γ ν ε θ β * mpOmega α ε θ β = mpLambdaBar α γ ν := by
    rw [mpLam, div_mul_cancel₀ _ hO.ne']
  linear_combination ((1 / 2) * ∑' t, β ^ t * (x t - xs) ^ 2) * hL -
    (∑' t, β ^ t * pin t ^ 2) * hKO

/-- Miao, p. 635: "when there is no economic distortion, `Φ = 0` so that `x* = 0`"; and
`x* = 0` only if `Φ = 0` (for `α < 1`, `D ≠ 0`). The weight `λ = mpLam` does not involve `Φ`. -/
theorem mp_xstar_zero_iff {α γ ν Φ : ℝ} (hα : α < 1) (hD : γ * (1 - α) + ν + α ≠ 0) :
    mpXstar α γ ν Φ = 0 ↔ Φ = 0 := by
  have ha : (1 - α) ≠ 0 := by linarith
  simp only [mpXstar, div_eq_zero_iff, mul_eq_zero, hD, ha, or_false]

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Monetary policy design: commitment versus discretion (Miao §19.2.3)

Miao, §19.2.3, pp. 635–640. The policy problem is the one of Miao, Examples 9.4.2 and 9.5.1:
the Phillips curve with cost-push shock (19.32) `π_t = κx_t + βE_tπ_{t+1} + u_t` is (9.23) with
`z_t = u_t`, and the loss `½∑βᵗ[π_t² + λ(x_t − x*)²]` is the one of Chapter 9. We reuse the
Chapter 9 modules `CPNKCommitment` and `CPNKDiscretion` (`ex942a` is the stable root `a` of
(9.29), `ex942Rule` the multiplier rule, `ex951θ = λ/(κ² + λ)`, `ex951pi` the discretionary
rule). As in Chapter 9 the expectations are replaced by the expected paths
`E_tu_{t+j} = ρ_u^ju_t` where a forward solution is involved; the laws of motion derived from
the multiplier rule are identities along every path of `u`.

**Strict inflation targeting** (p. 635). `mp_strict_targeting`: without cost-push shocks and
with `x* = 0`, the path `π = x = 0` satisfies (19.24) and has zero loss, every path has
nonnegative loss, and a path of zero loss has `π = x = 0`; `mp_strict_targeting_pi_zero`:
`π ≡ 0` forces `x ≡ 0` (`κ ≠ 0`); `mp_strict_targeting_rate`: then the IS curve (19.28) holds
iff `i_t = r^n_t`. `mp_cost_push_tradeoff` (p. 636): with (19.32), `π_t = 0` forces
`x_t = −u_t/κ ≠ 0` when `u_t ≠ 0`.

**Commitment** (pp. 636–637). `eq_19_33`, `eq_19_34`: the first-order conditions are the
derivatives of the Lagrangian of Chapter 9 (`ex942Lagr`, with the multiplier `β^{t+1}μ_{x,t+1}`
on (19.32)); for `π_0` the condition is (19.33) with `μ_{x0} = 0`. `mp_commit_rule`: every bounded
solution has `μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + u_t/(1 − βaρ_u))` ("as in Chapter
9.4"). `mp_commit_x_law`, `mp_commit_pi_law`, `mp_commit_initial`: the laws
`x_t = ax_{t−1} − (aκ/λ)u_t/(1 − βaρ_u)`, `π_t = aπ_{t−1} + a(u_t − u_{t−1})/(1 − βaρ_u)` and the
initial values `x_0`, `π_0` exactly as printed. `mp_price_level`, `mp_price_level_stationary`:
the price level is `p_t = p_{−1} − βμ_{x,t+1}`, bounded, and
`p_t = ap_{t−1} + au_t/(1 − βaρ_u) + (1 − a)p_{−1} + aκx*/(1 − βa)`; the printed law
`p_t = ap_{t−1} + au_t/(1 − βaρ_u)` needs `(1 − a)p_{−1} + aκx*/(1 − βa) = 0` (with `p_{−1} = 0`:
`x* = 0`), `mp_price_level_printed_false`.

**Timeless perspective** (pp. 637–638). `eq_19_35`; `mp_timeless_euler`
(`(1 + β + κ²/λ)x_t = βE_tx_{t+1} + x_{t−1} − (κ/λ)u_t`); `mp_timeless_coeff` (the coefficient
`κ/(λ(1 + β(1 − ρ − a)) + κ²)` equals `aκ/(λ(1 − βaρ))`, so the law is the commitment law);
`mp_timeless_solves`, `mp_timeless_unique`; `mp_timeless_pi`; `mp_commit_pi0`
(`π_0 = −(λ/κ)(x_0 − x*)` under precommitment); `mp_timeless_vs_commitment` (if `x_{−1} = x*`
the timeless path is the commitment path, and it is only then, for `a ≠ 0`).

**Discretion** (pp. 638–639). `mp_discretion_inflation`: the forward solution gives
`π_t = λκx*/(κ² + λ − βλ) + λu_t/(κ² + λ − βλρ_u)`; the book prints the shock coefficient as
`λκ/(κ² + λ − βλρ_u)`, which is false unless `κ = 1` (`mp_discretion_printed_false`).
`mp_inflation_bias`: the long-run inflation `λκx*/(κ² + (1 − β)λ)` is positive for
`κ, x* > 0`. `mp_a_lt_theta`, `mp_discretion_above_commitment`: `a < λ/(κ² + λ)`, and without
shocks discretionary inflation exceeds commitment inflation at every date;
`mp_discretion_gap_impact`: at the date of a cost-push shock the gap is
`(θ/(1 − βθ) − a/(1 − βa))κx* + (θ − a)u_0/((1 − βθρ)(1 − βaρ))`, increasing in `u_0`.

**Figure 19.3** (the qualitative facts stated, for all parameters with `κ, λ > 0`,
`0 < β < 1`, `x* = 0`, `ρ_u = 0`, one shock `u_0 = σ > 0`): `mp_fig_19_3_commitment` (inflation
rises on impact and is negative afterwards, the output gap is negative at every date and
serially correlated, `x_{t+1} = ax_t`) and `mp_fig_19_3_discretion` (inflation rises and the
output gap falls on impact, both are zero from the next period on). The plotted numbers are
computational and not formalised.
-/

namespace Miao.NewKeynesian

open Filter Topology MeasureTheory

/-! ### Strict inflation targeting -/

/-- **Strict inflation targeting is optimal** (Miao, p. 635). Without cost-push shocks and with
`x* = 0` (efficient steady state), let the loss be `∑βᵗ(π_t² + λx_t²)` (`β > 0`, `λ > 0`). The
path `π = x = 0` satisfies (19.24) `π_t = κx_t + βπ_{t+1}` and has loss `0`; every summable path
has loss `≥ 0`; a summable path with loss `0` is `π = x = 0`. -/
theorem mp_strict_targeting {β κ lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) :
    (∀ t : ℕ, (fun _ : ℕ => (0 : ℝ)) t =
      κ * (fun _ : ℕ => (0 : ℝ)) t + β * (fun _ : ℕ => (0 : ℝ)) (t + 1)) ∧
      ∑' t : ℕ, β ^ t * ((0 : ℝ) ^ 2 + lam * (0 : ℝ) ^ 2) = 0 ∧
      (∀ pin x : ℕ → ℝ, 0 ≤ ∑' t, β ^ t * (pin t ^ 2 + lam * x t ^ 2)) ∧
      (∀ pin x : ℕ → ℝ, Summable (fun t => β ^ t * (pin t ^ 2 + lam * x t ^ 2)) →
        ∑' t, β ^ t * (pin t ^ 2 + lam * x t ^ 2) = 0 → ∀ t, pin t = 0 ∧ x t = 0) := by
  have hnn : ∀ (pin x : ℕ → ℝ) t, 0 ≤ β ^ t * (pin t ^ 2 + lam * x t ^ 2) := fun pin x t =>
    mul_nonneg (pow_nonneg hβ.le t) (by positivity)
  refine ⟨fun _ => by simp, by simp, fun pin x => tsum_nonneg (hnn pin x),
    fun pin x hs h0 t => ?_⟩
  have hle : β ^ t * (pin t ^ 2 + lam * x t ^ 2) ≤ 0 := by
    rw [← h0]
    exact hs.le_tsum t fun j _ => hnn pin x j
  have hz : pin t ^ 2 + lam * x t ^ 2 = 0 := by
    have := hnn pin x t
    have hb := pow_pos hβ t
    have h2 : β ^ t * (pin t ^ 2 + lam * x t ^ 2) = 0 := le_antisymm hle this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hb.ne'
    · exact h
  have h1 : pin t ^ 2 = 0 := by nlinarith [sq_nonneg (pin t), sq_nonneg (x t)]
  have h2 : x t ^ 2 = 0 := by nlinarith [sq_nonneg (pin t), sq_nonneg (x t)]
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2⟩

/-- Miao, p. 635: with (19.24) and no cost-push shock, `π_t = 0` for all `t` implies `x_t = 0`
for all `t` (`κ ≠ 0`). -/
theorem mp_strict_targeting_pi_zero {β κ : ℝ} (hκ : κ ≠ 0) (pin x : ℕ → ℝ)
    (h24 : ∀ t, pin t = κ * x t + β * pin (t + 1)) (hpi : ∀ t, pin t = 0) : ∀ t, x t = 0 := by
  intro t
  have := h24 t
  rw [hpi t, hpi (t + 1), mul_zero, add_zero] at this
  rcases mul_eq_zero.1 this.symm with h | h
  · exact absurd h hκ
  · exact h

/-- Miao, p. 635 ("Hence, `i_t = r^n_t`"): at `π = x = 0` the IS curve (19.28)
`x_t = x_{t+1} − γ⁻¹(i_t − π_{t+1} − r^n_t)` holds iff `i_t = r^n_t` (`γ ≠ 0`). -/
theorem mp_strict_targeting_rate {γ i rn : ℝ} (hγ : γ ≠ 0) :
    ((0 : ℝ) = 0 - γ⁻¹ * (i - 0 - rn)) ↔ i = rn := by
  constructor
  · intro h
    have : γ⁻¹ * (i - rn) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (inv_ne_zero hγ)
    · linarith
  · intro h
    rw [h]
    ring

/-- **The short-run trade-off** (Miao, p. 636): with the cost-push shock in (19.32),
`π_t = π_{t+1} = 0` forces `x_t = −u_t/κ`, which is nonzero when `u_t ≠ 0` (`κ ≠ 0`). -/
theorem mp_cost_push_tradeoff {β κ x u : ℝ} (hκ : κ ≠ 0) (h32 : (0 : ℝ) = κ * x + β * 0 + u) :
    x = -u / κ ∧ (u ≠ 0 → x ≠ 0) := by
  have hx : x = -u / κ := by
    rw [eq_div_iff hκ]
    linarith
  refine ⟨hx, fun hu h => hu ?_⟩
  rw [h] at h32
  linarith

/-! ### Commitment: first-order conditions and the multiplier -/

/-- **(19.33)** (Miao, p. 636). For the Lagrangian of the commitment problem (`ex942Lagr` with
no shock-law multiplier, `u_t` the cost-push shock in place of `z_t`, multiplier
`β^{t+1}μ_{x,t+1}` on (19.32)) the derivative in `π_s` (`s < T`) is
`βˢ(π_s + βμ_{x,s+1} − βμ_{xs})`, where `μ_{x0} = 0`: at `s = 0` (the first-order condition for
`π_0`) this is `π_0 + βμ_{x1}`, i.e. (19.33) holds at `t = 0` with `μ_{x0} = 0`. -/
theorem eq_19_33 (β κ lam xs : ℝ) (μ u : ℕ → ℝ) (hμ0 : μ 0 = 0) {T s : ℕ} (hs : s < T)
    (pin x : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) T
      (cpPert pin s a) x u) (β ^ s * (pin s + β * μ (s + 1) - β * μ s)) 0 :=
  eq_9_25 β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) hμ0 hs pin x u

/-- **(19.34)** (Miao, p. 636): the derivative of the commitment Lagrangian in `x_s` (`s < T`) is
`βˢ(λ(x_s − x*) − βκμ_{x,s+1})`. -/
theorem eq_19_34 (β κ lam xs : ℝ) (μ u : ℕ → ℝ) {T s : ℕ} (hs : s < T) (pin x : ℕ → ℝ) :
    HasDerivAt (fun a => ex942Lagr β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) T pin
      (cpPert x s a) u) (β ^ s * (lam * (x s - xs) - β * κ * μ (s + 1))) 0 :=
  eq_9_26 β κ lam 0 xs 0 (fun _ => 0) μ (fun _ => 0) hs pin x u

/-- **The commitment multiplier** (Miao, p. 636, "as in Chapter 9.4"). Let `0 < β < 1`,
`λ > 0`, `κ ≠ 0`, `|ρ_u| ≤ 1`, `a = ex942a` the smaller root of (9.29), and let the expected
shock path be `u_{t+1} = ρ_uu_t`. If bounded `π, x, μ` with `μ_{x0} = 0` satisfy (19.33),
(19.34) and (19.32) at every date, then
`μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + u_t/(1 − βaρ_u))` for every `t`. -/
theorem mp_commit_rule {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : κ ≠ 0) (hρ : |ρ| ≤ 1) (pin x u μ : ℕ → ℝ) (hu : ∀ t, u (t + 1) = ρ * u t)
    (h33 : ∀ t, pin t + β * μ (t + 1) - β * μ t = 0)
    (h34 : ∀ t, lam * (x t - xs) - β * κ * μ (t + 1) = 0)
    (h32 : ∀ t, pin t = κ * x t + β * pin (t + 1) + u t) (hμb : ∃ M, ∀ t, |μ t| ≤ M) :
    ∀ t, μ (t + 1) = ex942Rule β κ ρ xs (ex942a β κ lam) (μ t) (u t) := by
  obtain ⟨ha0, ha1, -, hroot, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  have h28 : ∀ t, β * μ (t + 2) - ex942b β κ lam * μ (t + 1) + μ t = κ * xs / β + u t / β :=
    fun t => eq_9_28 hβ0.ne' hlam.ne' pin x u μ t (h33 t) (h33 (t + 1)) (h34 t) (h32 t)
  exact ex942_unique_bounded hβ0.ne' (mul_pos hβ0 ha0) (by nlinarith) hρ hroot u μ hu h28 hμb

/-- The multiplier rule in terms of `βμ`: `βμ_{x,t+1} = a(βμ_{xt}) − a(κx*/(1 − βa) +
u_t/(1 − βaρ_u))` (`β ≠ 0`). -/
theorem mp_beta_rule {β κ ρ xs a μ z : ℝ} (hβ : β ≠ 0) :
    β * ex942Rule β κ ρ xs a μ z =
      a * (β * μ) - a * (κ * xs / (1 - β * a) + z / (1 - β * a * ρ)) := by
  simp only [ex942Rule]
  field_simp

/-- For a root `a` of (9.29) with `1 − βa ≠ 0`: `1 − a − aκ²/(λ(1 − βa)) = 0`. -/
theorem mp_root_identity {β κ lam a : ℝ} (hd1 : 1 - β * a ≠ 0)
    (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) :
    1 - a - a * κ ^ 2 * lam⁻¹ * (1 - β * a)⁻¹ = 0 := by
  have h : (1 - a - a * κ ^ 2 * lam⁻¹ * (1 - β * a)⁻¹) * (1 - β * a) =
      β * a ^ 2 - ex942b β κ lam * a + 1 := by
    have hinv : (1 - β * a)⁻¹ * (1 - β * a) = 1 := inv_mul_cancel₀ hd1
    simp only [ex942b, div_eq_mul_inv]
    linear_combination (-a * κ ^ 2 * lam⁻¹) * hinv
  rw [hroot] at h
  rcases mul_eq_zero.1 h with h1 | h1
  · exact h1
  · exact absurd h1 hd1

/-- **The commitment law for the output gap** (Miao, p. 637). Let `a` be a root of (9.29),
`β ≠ 0`, `1 − βa ≠ 0`, `μ` follow the multiplier rule along any path `u`,
and `x_t = x* + (βκ/λ)μ_{x,t+1}` ((19.34)). Then `x_{t+1} = ax_t − (aκ/λ)u_{t+1}/(1 − βaρ_u)`. -/
theorem mp_commit_x_law {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (u μ : ℕ → ℝ)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) (t : ℕ) :
    xs + β * κ / lam * μ (t + 2) =
      a * (xs + β * κ / lam * μ (t + 1)) - a * κ / lam * (u (t + 1) / (1 - β * a * ρ)) := by
  have hid := mp_root_identity hd1 hroot
  have hb := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ (t + 1)) (z := u (t + 1))
    hβ
  rw [← hμ (t + 1)] at hb
  have e : β * κ / lam * μ (t + 2) = κ * lam⁻¹ * (β * μ (t + 1 + 1)) := by ring
  rw [e, hb]
  simp only [div_eq_mul_inv]
  linear_combination xs * hid

/-- **The commitment law for inflation** (Miao, p. 637). With `π_t = β(μ_{xt} − μ_{x,t+1})`
((19.33)) and the multiplier rule along any path `u` (`β ≠ 0`):
`π_{t+1} = aπ_t + a(u_{t+1} − u_t)/(1 − βaρ_u)`. -/
theorem mp_commit_pi_law {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (u μ : ℕ → ℝ)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) (t : ℕ) :
    β * (μ (t + 1) - μ (t + 2)) =
      a * (β * (μ t - μ (t + 1))) + a * (u (t + 1) - u t) / (1 - β * a * ρ) := by
  have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ t) (z := u t) hβ
  have h2 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ (t + 1))
    (z := u (t + 1)) hβ
  rw [← hμ t] at h1
  rw [← hμ (t + 1)] at h2
  have h2' : β * μ (t + 2) = a * (β * μ (t + 1)) -
      a * (κ * xs / (1 - β * a) + u (t + 1) / (1 - β * a * ρ)) := h2
  linear_combination h1 - h2'

/-- **The commitment initial values** (Miao, p. 637). With `μ_{x0} = 0`:
`x_0 = x* + (βκ/λ)μ_{x1} = x* − (aκ/λ)(κx*/(1 − βa) + u_0/(1 − βaρ_u))` and
`π_0 = −βμ_{x1} = a(κx*/(1 − βa) + u_0/(1 − βaρ_u))`. -/
theorem mp_commit_initial {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (u μ : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) :
    xs + β * κ / lam * μ 1 =
        xs - a * κ / lam * (κ * xs / (1 - β * a) + u 0 / (1 - β * a * ρ)) ∧
      β * (μ 0 - μ 1) = a * (κ * xs / (1 - β * a) + u 0 / (1 - β * a * ρ)) := by
  have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ 0) (z := u 0) hβ
  rw [← hμ 0, hμ0, mul_zero, mul_zero, zero_sub] at h1
  constructor
  · have e : β * κ / lam * μ 1 = κ / lam * (β * μ 1) := by ring
    rw [e, h1]
    ring
  · rw [hμ0]
    simp only [zero_add] at h1
    linarith

/-- **The price level under commitment** (Miao, p. 637). Let `P_t = p_{t−1}` (so `P_0 = p_{−1}`)
with `p_t − p_{t−1} = π_t = β(μ_{xt} − μ_{x,t+1})`, `μ_{x0} = 0` and the multiplier rule. Then
`p_t = p_{−1} − βμ_{x,t+1}` and
`p_t = ap_{t−1} + au_t/(1 − βaρ_u) + (1 − a)p_{−1} + aκx*/(1 − βa)`. -/
theorem mp_price_level {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (u μ P : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t))
    (hP : ∀ t, P (t + 1) - P t = β * (μ t - μ (t + 1))) :
    (∀ t, P (t + 1) = P 0 - β * μ (t + 1)) ∧
      ∀ t, P (t + 1) = a * P t + a * u t / (1 - β * a * ρ) + (1 - a) * P 0 +
        a * (κ * xs / (1 - β * a)) := by
  have hlev : ∀ t, P (t + 1) = P 0 - β * μ (t + 1) := by
    intro t
    induction t with
    | zero =>
      have h := hP 0
      rw [hμ0] at h
      linarith
    | succ n ih => linarith [hP (n + 1)]
  refine ⟨hlev, fun t => ?_⟩
  have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ t) (z := u t) hβ
  rw [← hμ t] at h1
  have hPt : P t = P 0 - β * μ t := by
    cases t with
    | zero => rw [hμ0]; ring
    | succ n => exact hlev n
  rw [hlev t, h1, hPt]
  ring

/-- **The printed price-level law fails for `x* ≠ 0`** (Miao, p. 637). With the normalisation
`p_{−1} = 0`, `0 < a`, `1 − βa ≠ 0` and `κx* ≠ 0`, `p_0 ≠ ap_{−1} + au_0/(1 − βaρ_u)`. -/
theorem mp_price_level_printed_false {β κ ρ xs a : ℝ} (hβ : β ≠ 0) (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hκx : κ * xs ≠ 0) (u μ P : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t))
    (hP : ∀ t, P (t + 1) - P t = β * (μ t - μ (t + 1))) (hP0 : P 0 = 0) :
    P 1 ≠ a * P 0 + a * u 0 / (1 - β * a * ρ) := by
  have h := (mp_price_level hβ u μ P hμ0 hμ hP).2 0
  rw [hP0] at h ⊢
  intro h'
  rw [h'] at h
  have : a * (κ * xs / (1 - β * a)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · exact ha h1
  · exact hκx (by rw [div_eq_zero_iff] at h1; tauto)

/-- **The price level is stationary** (Miao, p. 637). If `0 ≤ a < 1`, `|u_t| ≤ U` and
`1 − βaρ_u ≠ 0`, the commitment multiplier satisfies
`|βμ_{xt}| ≤ a(|κx*/(1 − βa)| + U/|1 − βaρ_u|)/(1 − a)`, so `p_t = p_{−1} − βμ_{x,t+1}` is
bounded. -/
theorem mp_price_level_stationary {β κ ρ xs a U : ℝ} (hβ : β ≠ 0) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u μ : ℕ → ℝ) (hU : ∀ t, |u t| ≤ U) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t)) :
    ∀ t, |β * μ t| ≤ a * (|κ * xs / (1 - β * a)| + U / |1 - β * a * ρ|) / (1 - a) := by
  set B := a * (|κ * xs / (1 - β * a)| + U / |1 - β * a * ρ|)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hB : 0 ≤ B := mul_nonneg ha0 (by positivity)
  intro t
  rw [le_div_iff₀ (by linarith)]
  induction t with
  | zero => rw [hμ0]; simp only [mul_zero, abs_zero, zero_mul]; exact hB
  | succ n ih =>
    have h1 := mp_beta_rule (κ := κ) (ρ := ρ) (xs := xs) (a := a) (μ := μ n) (z := u n) hβ
    rw [← hμ n] at h1
    rw [h1]
    have hk : |κ * xs / (1 - β * a) + u n / (1 - β * a * ρ)| ≤
        |κ * xs / (1 - β * a)| + U / |1 - β * a * ρ| := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_div]
      exact div_le_div_of_nonneg_right (hU n) (abs_nonneg _)
    have h2 : |a * (β * μ n) - a * (κ * xs / (1 - β * a) + u n / (1 - β * a * ρ))| ≤
        a * |β * μ n| + B := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul a, abs_mul a, abs_of_nonneg ha0]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hk ha0)
    have h3 : a * |β * μ n| ≤ a * (B / (1 - a)) := by
      apply mul_le_mul_of_nonneg_left _ ha0
      rw [le_div_iff₀ (by linarith)]
      exact ih
    have h4 : a * (B / (1 - a)) + B = B / (1 - a) := by
      have : (1 : ℝ) - a ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ring
    have h5 : |a * (β * μ n) - a * (κ * xs / (1 - β * a) + u n / (1 - β * a * ρ))| ≤
        B / (1 - a) := by linarith
    rwa [le_div_iff₀ (by linarith)] at h5

/-! ### The timeless perspective -/

/-- **(19.35)** (Miao, p. 637). If (19.33) holds at `t` and (19.34) at `t` and `t − 1`
(`κ ≠ 0`), then `π_t = −(λ/κ)(x_t − x_{t−1})`. -/
theorem eq_19_35 {β κ lam xs pin x xm μ μ' : ℝ} (hκ : κ ≠ 0)
    (h33 : pin + β * μ' - β * μ = 0) (h34 : lam * (x - xs) - β * κ * μ' = 0)
    (h34m : lam * (xm - xs) - β * κ * μ = 0) : pin = -(lam / κ) * (x - xm) := by
  field_simp
  linear_combination κ * h33 + h34 - h34m

/-- Miao, p. 637: substituting (19.35) at `t` and `t + 1` into (19.32) gives
`(1 + β + κ²/λ)x_t = βE_tx_{t+1} + x_{t−1} − (κ/λ)u_t` (`κ, λ ≠ 0`). -/
theorem mp_timeless_euler {β κ lam pin pin' x x' xm u : ℝ} (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (h35 : pin = -(lam / κ) * (x - xm)) (h35' : pin' = -(lam / κ) * (x' - x))
    (h32 : pin = κ * x + β * pin' + u) :
    (1 + β + κ ^ 2 / lam) * x = β * x' + xm - κ / lam * u := by
  rw [h35, h35'] at h32
  field_simp at h32 ⊢
  linear_combination (-1) * h32

/-- Miao, pp. 637–638: for a root `a` of (9.29) with `a ≠ 0`, the timeless coefficient
`κ/(λ(1 + β(1 − ρ − a)) + κ²)` equals `aκ/(λ(1 − βaρ))` (`λ ≠ 0`, `1 − βaρ ≠ 0`), so the law
`x_t = ax_{t−1} − κu_t/(λ(1 + β(1 − ρ − a)) + κ²)` is the commitment law of p. 637
("the same as that under optimal commitment"). -/
theorem mp_timeless_coeff {β κ lam ρ a : ℝ} (ha : a ≠ 0) (hlam : lam ≠ 0)
    (hd2 : 1 - β * a * ρ ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) :
    lam * (1 + β * (1 - ρ - a)) + κ ^ 2 = lam * (1 - β * a * ρ) / a ∧
      κ / (lam * (1 + β * (1 - ρ - a)) + κ ^ 2) = a * κ / (lam * (1 - β * a * ρ)) := by
  have hb := ex942_b_eq ha hroot
  simp only [ex942b] at hb
  have e : lam * (1 + β * (1 - ρ - a)) + κ ^ 2 = lam * (1 - β * a * ρ) / a := by
    have : κ ^ 2 = lam * (β * a + a⁻¹ - 1 - β) := by
      field_simp at hb ⊢
      linear_combination hb
    rw [this]
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e]
  field_simp

/-- Miao, p. 637 ("Solving yields"): if `a` is a root of (9.29), `a ≠ 0`, `λ ≠ 0`,
`1 − βaρ ≠ 0`, `x_t = ax_{t−1} + cu_t` with `c = −aκ/(λ(1 − βaρ))`, and
`E_tx_{t+1} = ax_t + cρu_t` (`E_tu_{t+1} = ρu_t`), then
`(1 + β + κ²/λ)x_t = βE_tx_{t+1} + x_{t−1} − (κ/λ)u_t`. -/
theorem mp_timeless_solves {β κ lam ρ a xm u : ℝ} (ha : a ≠ 0) (hlam : lam ≠ 0)
    (hd2 : 1 - β * a * ρ ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) :
    let c := -(a * κ / (lam * (1 - β * a * ρ)))
    let x := a * xm + c * u
    ex942b β κ lam * x = β * (a * x + c * ρ * u) + xm - κ / lam * u := by
  intro c x
  rw [ex942_b_eq ha hroot]
  simp only [x, c]
  field_simp
  ring

/-- **Uniqueness of the timeless solution** (Miao, p. 637). Let `0 < β`, `0 < βa < 1`,
`|ρ| ≤ 1`, `a` a root of (9.29), `u_{t+1} = ρu_t` (expected path) and `X_s = x_{s−1}` bounded with
`βX_{s+2} − (1 + β + κ²/λ)X_{s+1} + X_s = (κ/λ)u_s` (the timeless equation at date `s`). Then
`x_s = ax_{s−1} − aκu_s/(λ(1 − βaρ))`. -/
theorem mp_timeless_unique {β κ lam ρ a : ℝ} (hβ : β ≠ 0) (ha0 : 0 < β * a) (ha1 : β * a < 1)
    (hρ : |ρ| ≤ 1) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0) (u X : ℕ → ℝ)
    (hu : ∀ t, u (t + 1) = ρ * u t)
    (heq : ∀ s, β * X (s + 2) - ex942b β κ lam * X (s + 1) + X s = κ / lam * u s)
    (hXb : ∃ M, ∀ t, |X t| ≤ M) :
    ∀ s, X (s + 1) = a * X s - a * κ / lam * (u s / (1 - β * a * ρ)) := by
  have h := ex942_unique_bounded (xs := 0) hβ ha0 ha1 hρ hroot (fun s => β * (κ / lam) * u s) X
    (fun t => by simp only [hu t]; ring) (fun s => by rw [heq s]; field_simp; ring) hXb
  intro s
  rw [h s, ex942Rule]
  field_simp
  ring

/-- Miao, p. 638: substituting the timeless law `x_t = ax_{t−1} + cu_t`,
`c = −κ/(λ(1 + β(1 − ρ − a)) + κ²)`, into (19.35) gives
`π_t = (λ/κ)(1 − a)x_{t−1} + λu_t/(λ(1 + β(1 − ρ − a)) + κ²)` (`κ ≠ 0`). -/
theorem mp_timeless_pi {β κ lam ρ a xm u : ℝ} (hκ : κ ≠ 0) :
    -(lam / κ) * ((a * xm - κ / (lam * (1 + β * (1 - ρ - a)) + κ ^ 2) * u) - xm) =
      lam / κ * (1 - a) * xm + lam / (lam * (1 + β * (1 - ρ - a)) + κ ^ 2) * u := by
  field_simp
  ring

/-- Miao, p. 638: under optimal precommitment `μ_{x0} = 0`, so (19.33) and (19.34) at `t = 0`
give `π_0 = −(λ/κ)(x_0 − x*)` (`κ ≠ 0`), which differs from (19.35) at `t = 0` unless
`x_{−1} = x*`. -/
theorem mp_commit_pi0 {β κ lam xs pin x μ' : ℝ} (hκ : κ ≠ 0) (h33 : pin + β * μ' - β * 0 = 0)
    (h34 : lam * (x - xs) - β * κ * μ' = 0) : pin = -(lam / κ) * (x - xs) := by
  field_simp
  linear_combination κ * h33 + h34

/-- **Timeless perspective versus commitment** (Miao, p. 638). Let `a` be a root of (9.29) with
`a ≠ 0`, `β ≠ 0`, `1 − βa ≠ 0`, `μ` the commitment multiplier (`μ_{x0} = 0`, the rule along
`u`), `x^c_t = x* + (βκ/λ)μ_{x,t+1}` the commitment output gap, and `x^{tl}` the timeless path
`x^{tl}_t = ax^{tl}_{t−1} − (aκ/λ)u_t/(1 − βaρ)` from `x^{tl}_{−1} = X_0`
(`X_{t+1} = x^{tl}_t`). Then `x^{tl} = x^c` at every date iff `X_0 = x*`. -/
theorem mp_timeless_vs_commitment {β κ lam ρ xs a : ℝ} (hβ : β ≠ 0) (ha : a ≠ 0)
    (hd1 : 1 - β * a ≠ 0) (hroot : β * a ^ 2 - ex942b β κ lam * a + 1 = 0)
    (u μ X : ℕ → ℝ) (hμ0 : μ 0 = 0) (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs a (μ t) (u t))
    (hX : ∀ t, X (t + 1) = a * X t - a * κ / lam * (u t / (1 - β * a * ρ))) :
    (∀ t, X (t + 1) = xs + β * κ / lam * μ (t + 1)) ↔ X 0 = xs := by
  have hx0 : xs + β * κ / lam * μ 1 = a * xs - a * κ / lam * (u 0 / (1 - β * a * ρ)) := by
    rw [(mp_commit_initial (lam := lam) hβ u μ hμ0 hμ).1]
    have hid := mp_root_identity hd1 hroot
    simp only [div_eq_mul_inv]
    linear_combination xs * hid
  constructor
  · intro h
    have h0 := h 0
    rw [hX 0, hx0] at h0
    have : a * (X 0 - xs) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 ha
    · linarith
  · intro h0 t
    induction t with
    | zero => rw [hX 0, hx0, h0]
    | succ n ih =>
      rw [hX (n + 1), ih, mp_commit_x_law hβ hd1 hroot u μ hμ n]

/-! ### Discretion -/

/-- The discretionary rule in the book's closed form:
`θ(κx*/(1 − βθ) + u/(1 − βθρ)) = λκx*/(κ² + λ − βλ) + λu/(κ² + λ − βλρ)`. -/
theorem mp_ex951pi_closed {β κ lam ρ xs u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) :
    ex951pi β κ lam ρ xs u =
      lam * κ * xs / (κ ^ 2 + lam - β * lam) + lam / (κ ^ 2 + lam - β * lam * ρ) * u := by
  obtain ⟨hd1, hd2, -, -⟩ := ex951_denoms (κ := κ) hβ0 hβ1 hlam hρ
  have hk : κ ^ 2 + lam ≠ 0 := by positivity
  have e1 : κ ^ 2 + lam - β * lam = (κ ^ 2 + lam) * (1 - β * ex951θ κ lam) := by
    simp only [ex951θ]
    field_simp
  have e2 : κ ^ 2 + lam - β * lam * ρ = (κ ^ 2 + lam) * (1 - β * ex951θ κ lam * ρ) := by
    simp only [ex951θ]
    field_simp
  rw [e1, e2, ex951pi]
  simp only [ex951θ] at hd1 hd2 ⊢
  field_simp

/-- **Discretionary inflation** (Miao, p. 638). For `0 < β < 1`, `λ > 0`, `|ρ_u| ≤ 1`, let
`p_j = E_tπ_{t+j}` be bounded with `p_j = θ(κx* + βp_{j+1} + ρ_u^ju_t)`, `θ = λ/(κ² + λ)` (the
discretionary condition (9.43)). Then
`π_t = θ∑ⱼβʲθʲ(κx* + E_tu_{t+j}) = λκx*/(κ² + λ − βλ) + λu_t/(κ² + λ − βλρ_u)`. -/
theorem mp_discretion_inflation {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (u : ℝ) (p : ℕ → ℝ)
    (hp : ∀ j, p j = ex951θ κ lam * (κ * xs + β * p (j + 1) + ρ ^ j * u))
    (hb : ∃ M, ∀ j, |p j| ≤ M) :
    p 0 = ex951θ κ lam * ∑' j : ℕ, β ^ j * ex951θ κ lam ^ j * (κ * xs + ρ ^ j * u) ∧
      p 0 = lam * κ * xs / (κ ^ 2 + lam - β * lam) + lam / (κ ^ 2 + lam - β * lam * ρ) * u := by
  have h1 := ex951_forward hβ0 hβ1 hlam hρ u p hp hb
  refine ⟨h1, ?_⟩
  rw [h1, ex951_series hβ0 hβ1 hlam hρ u, mp_ex951pi_closed hβ0 hβ1 hlam hρ]

/-- **The printed discretionary coefficient is wrong** (Miao, p. 638). The book's closed form
`λκx*/(κ² + λ − βλ) + λκu_t/(κ² + λ − βλρ_u)` differs from the discretionary inflation rate
whenever `κ ≠ 1` and `u_t ≠ 0` (`0 < β < 1`, `λ > 0`, `|ρ_u| ≤ 1`). -/
theorem mp_discretion_printed_false {β κ lam ρ xs u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hρ : |ρ| ≤ 1) (hκ : κ ≠ 1) (hu : u ≠ 0) :
    ex951pi β κ lam ρ xs u ≠
      lam * κ * xs / (κ ^ 2 + lam - β * lam) + lam * κ / (κ ^ 2 + lam - β * lam * ρ) * u := by
  rw [mp_ex951pi_closed hβ0 hβ1 hlam hρ]
  intro h
  have hden : 0 < κ ^ 2 + lam - β * lam * ρ := by
    have h1 : β * ρ ≤ |β * ρ| := le_abs_self _
    rw [abs_mul, abs_of_pos hβ0] at h1
    have h2 : |ρ| * β ≤ β := mul_le_of_le_one_left hβ0.le hρ
    nlinarith [sq_nonneg κ]
  have : lam / (κ ^ 2 + lam - β * lam * ρ) * u * (1 - κ) = 0 := by
    have e : lam * κ / (κ ^ 2 + lam - β * lam * ρ) * u =
        κ * (lam / (κ ^ 2 + lam - β * lam * ρ) * u) := by ring
    rw [e] at h
    linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (div_pos hlam hden).ne'
    · exact hu h2
  · exact hκ (by linarith)

/-- **Inflation bias** (Miao, p. 638): without shocks, discretionary inflation is
`λκx*/(κ² + (1 − β)λ)`, positive for `κ, x*, λ > 0`, `0 < β < 1`. -/
theorem mp_inflation_bias {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hρ : |ρ| ≤ 1) (hκ : 0 < κ) (hxs : 0 < xs) :
    ex951pi β κ lam ρ xs 0 = lam * κ * xs / (κ ^ 2 + (1 - β) * lam) ∧
      0 < ex951pi β κ lam ρ xs 0 := by
  have e : ex951pi β κ lam ρ xs 0 = lam * κ * xs / (κ ^ 2 + (1 - β) * lam) := by
    rw [mp_ex951pi_closed hβ0 hβ1 hlam hρ, mul_zero, add_zero]
    congr 1
    ring
  refine ⟨e, ?_⟩
  rw [e]
  have : 0 < (1 - β) * lam := mul_pos (by linarith) hlam
  positivity

/-- Miao, p. 638: the commitment root is below the discretionary coefficient,
`a < θ = λ/(κ² + λ)` (`0 < β < 1`, `λ > 0`, `κ ≠ 0`). -/
theorem mp_a_lt_theta {β κ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam) (hκ : κ ≠ 0) :
    ex942a β κ lam < ex951θ κ lam := by
  obtain ⟨ha0, ha1, -, hroot, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  set a := ex942a β κ lam
  set θ := ex951θ κ lam
  have hθ1 : θ ≤ 1 := ex951θ_le_one hlam
  have hk2 : 0 < κ ^ 2 := by positivity
  have hPθ : β * θ ^ 2 - ex942b β κ lam * θ + 1 = -(β * κ ^ 2 * lam / (κ ^ 2 + lam) ^ 2) := by
    simp only [θ, ex951θ, ex942b]
    field_simp
    ring
  have hneg : β * θ ^ 2 - ex942b β κ lam * θ + 1 < 0 := by
    rw [hPθ, neg_lt_zero]
    positivity
  have hb := ex942_b_eq ha0.ne' hroot
  have hfac : β * θ ^ 2 - ex942b β κ lam * θ + 1 = (θ - a) * (β * θ - a⁻¹) := by
    rw [hb]
    have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
    linear_combination (-1) * hia
  have hai : 1 < a⁻¹ := one_lt_inv_iff₀.2 ⟨ha0, ha1⟩
  by_contra hle
  push Not at hle
  have h1 : β * θ - a⁻¹ < 0 := by nlinarith
  have h2 : 0 ≤ (θ - a) * (β * θ - a⁻¹) := mul_nonneg_of_nonpos_of_nonpos (by linarith) h1.le
  linarith

/-- **Discretion has higher inflation at all times** (Miao, pp. 638–639). Without cost-push
shocks, with `κx* > 0`, `0 < β < 1`, `λ > 0`, commitment inflation `π_t = β(μ_{xt} − μ_{x,t+1})`
(`μ_{x0} = 0`, the rule with `a = ex942a`) is below the discretionary rate at every date. -/
theorem mp_discretion_above_commitment {β κ lam ρ xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hκx : 0 < κ * xs) (μ : ℕ → ℝ) (hμ0 : μ 0 = 0)
    (hμ : ∀ t, μ (t + 1) = ex942Rule β κ ρ xs (ex942a β κ lam) (μ t) 0) :
    ∀ t, β * (μ t - μ (t + 1)) < ex951pi β κ lam ρ xs 0 := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at hκx
  obtain ⟨hc, -, -, -⟩ := cp_commitment_vs_discretion hβ0 hβ1 hlam hκ ρ μ hμ0 hμ
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  have hat := mp_a_lt_theta hβ0 hβ1 hlam hκ
  set a := ex942a β κ lam
  set θ := ex951θ κ lam
  have hθ1 : θ ≤ 1 := ex951θ_le_one hlam
  have hd1 : 0 < 1 - β * a := by nlinarith
  have hd2 : 0 < 1 - β * θ := by nlinarith
  have hpd : ex951pi β κ lam ρ xs 0 = θ * (κ * xs / (1 - β * θ)) := by
    simp only [ex951pi, zero_div, add_zero]
    rfl
  intro t
  rw [hc t, hpd]
  have hpow : a ^ (t + 1) ≤ a := by
    rw [pow_succ]
    exact mul_le_of_le_one_left ha0.le (pow_le_one₀ ha0.le ha1.le)
  have hK : 0 < κ * xs / (1 - β * a) := div_pos hκx hd1
  have hcmp : a * (κ * xs / (1 - β * a)) < θ * (κ * xs / (1 - β * θ)) := by
    rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ hd1 hd2]
    nlinarith
  calc a ^ (t + 1) * (κ * xs / (1 - β * a)) ≤ a * (κ * xs / (1 - β * a)) :=
        mul_le_mul_of_nonneg_right hpow hK.le
    _ < θ * (κ * xs / (1 - β * θ)) := hcmp

/-- The algebra of the impact gap:
`θ(K/(1 − βθ) + u/(1 − βθρ)) − a(K/(1 − βa) + u/(1 − βaρ)) =
(θ/(1 − βθ) − a/(1 − βa))K + (θ − a)u/((1 − βθρ)(1 − βaρ))`. -/
theorem mp_gap_algebra {β ρ a θ K u : ℝ} (h3 : 1 - β * θ * ρ ≠ 0) (h4 : 1 - β * a * ρ ≠ 0) :
    θ * (K / (1 - β * θ) + u / (1 - β * θ * ρ)) - a * (K / (1 - β * a) + u / (1 - β * a * ρ)) =
      (θ / (1 - β * θ) - a / (1 - β * a)) * K + (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) * u
    := by
  have e : θ / (1 - β * θ * ρ) - a / (1 - β * a * ρ) =
      (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) := by
    rw [div_sub_div _ _ h3 h4, show θ * (1 - β * a * ρ) - (1 - β * θ * ρ) * a = θ - a by ring]
  rw [← e]
  ring

/-- **The gap at the date of a cost-push shock** (Miao, p. 639). With `0 < β < 1`, `λ > 0`,
`κ ≠ 0`, `|ρ_u| ≤ 1`, the date-0 discretionary inflation minus the date-0 commitment inflation
`a(κx*/(1 − βa) + u_0/(1 − βaρ_u))` is
`(θ/(1 − βθ) − a/(1 − βa))κx* + (θ − a)u_0/((1 − βθρ_u)(1 − βaρ_u))`, and both coefficients are
positive: the gap rises with the shock. -/
theorem mp_discretion_gap_impact {β κ lam ρ xs u0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlam : 0 < lam) (hκ : κ ≠ 0) (hρ : |ρ| ≤ 1) :
    let a := ex942a β κ lam
    let θ := ex951θ κ lam
    ex951pi β κ lam ρ xs u0 - a * (κ * xs / (1 - β * a) + u0 / (1 - β * a * ρ)) =
        (θ / (1 - β * θ) - a / (1 - β * a)) * (κ * xs) +
          (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) * u0 ∧
      0 < θ / (1 - β * θ) - a / (1 - β * a) ∧
      0 < (θ - a) / ((1 - β * θ * ρ) * (1 - β * a * ρ)) := by
  intro a θ
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ
  have hat : a < θ := mp_a_lt_theta hβ0 hβ1 hlam hκ
  have hθ1 : θ ≤ 1 := ex951θ_le_one hlam
  have hθ0 : 0 < θ := ex951θ_pos hlam
  have hβρ : |β * ρ| < 1 := by
    rw [abs_mul, abs_of_pos hβ0]
    nlinarith [abs_nonneg ρ]
  have hr := abs_lt.1 hβρ
  have hd1 : 0 < 1 - β * a := by nlinarith
  have hd2 : 0 < 1 - β * θ := by nlinarith
  have hd3 : 0 < 1 - β * θ * ρ := by nlinarith
  have hd4 : 0 < 1 - β * a * ρ := by nlinarith
  refine ⟨?_, ?_, div_pos (by linarith) (mul_pos hd3 hd4)⟩
  · simp only [ex951pi]
    exact mp_gap_algebra hd3.ne' hd4.ne'
  · rw [sub_pos, div_lt_div_iff₀ hd1 hd2]
    nlinarith

/-! ### Figure 19.3: the qualitative facts -/

/-- **Figure 19.3, commitment** (Miao, pp. 639–640). Let `0 < β < 1`, `λ > 0`, `κ > 0`,
`x* = 0`, `ρ_u = 0`, a single cost-push shock `u_0 = σ > 0` (`u_t = 0` for `t ≥ 1`), `μ_{x0} = 0`
and the commitment rule. Then `βμ_{x,t+1} = −a^{t+1}σ`; the output gap
`x_t = (βκ/λ)μ_{x,t+1} = −(κ/λ)a^{t+1}σ` is negative at every date and serially correlated
(`x_{t+1} = ax_t`); inflation rises on impact (`π_0 = aσ > 0`) and is negative afterwards
(`π_{t+1} = −a^{t+1}(1 − a)σ < 0`). -/
theorem mp_fig_19_3_commitment {β κ lam σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hσ : 0 < σ) (u μ : ℕ → ℝ) (hu0 : u 0 = σ) (hu : ∀ t, u (t + 1) = 0)
    (hμ0 : μ 0 = 0) (hμ : ∀ t, μ (t + 1) = ex942Rule β κ 0 0 (ex942a β κ lam) (μ t) (u t)) :
    let a := ex942a β κ lam
    (∀ t, β * μ (t + 1) = -(a ^ (t + 1) * σ)) ∧
      (∀ t, β * κ / lam * μ (t + 1) < 0) ∧
      (∀ t, β * κ / lam * μ (t + 2) = a * (β * κ / lam * μ (t + 1))) ∧
      0 < β * (μ 0 - μ 1) ∧ (∀ t, β * (μ (t + 1) - μ (t + 2)) < 0) := by
  intro a
  obtain ⟨ha0, ha1, -, -, -, -⟩ := eq_9_29 hβ0 hβ1 hlam hκ.ne'
  have hrule : ∀ t, β * μ (t + 1) = a * (β * μ t) - a * u t := fun t => by
    rw [hμ t, mp_beta_rule hβ0.ne']
    simp only [mul_zero, zero_div, zero_add, sub_zero, div_one]
    rfl
  have hclosed : ∀ t, β * μ (t + 1) = -(a ^ (t + 1) * σ) := by
    intro t
    induction t with
    | zero => rw [hrule 0, hμ0, hu0]; ring
    | succ n ih => rw [hrule (n + 1), ih, hu n]; ring
  have hx : ∀ t, β * κ / lam * μ (t + 1) = κ / lam * -(a ^ (t + 1) * σ) := fun t => by
    rw [← hclosed t]
    ring
  refine ⟨hclosed, fun t => ?_, fun t => ?_, ?_, fun t => ?_⟩
  · rw [hx t]
    have : 0 < a ^ (t + 1) * σ := mul_pos (pow_pos ha0 _) hσ
    have : 0 < κ / lam := div_pos hκ hlam
    nlinarith
  · rw [hx, hx]
    ring
  · have h1 := hclosed 0
    have : β * (μ 0 - μ 1) = a * σ := by
      rw [mul_sub, hμ0, mul_zero, zero_sub, h1]
      ring
    rw [this]
    exact mul_pos ha0 hσ
  · have e : β * (μ (t + 1) - μ (t + 2)) = -(a ^ (t + 1) * σ) + a ^ (t + 2) * σ := by
      rw [mul_sub, hclosed t, hclosed (t + 1)]
      ring
    rw [e]
    have : a ^ (t + 2) < a ^ (t + 1) := pow_lt_pow_right_of_lt_one₀ ha0 ha1 (by omega)
    nlinarith

/-- **Figure 19.3, discretion** (Miao, pp. 639–640). With `x* = 0`, `ρ_u = 0`, `λ > 0`, `κ > 0`,
`0 < β < 1` and a single shock `u_0 = σ > 0`, the discretionary policy
`π_t = ex951pi(u_t)`, `x_t = (λx* − κ(βE_tπ_{t+1} + u_t))/(κ² + λ)` ((9.43) with
`E_tπ_{t+1} = ex951pi(ρ_uu_t)`) has inflation rising and the output gap falling on impact, and
both are `0` from the next period on. -/
theorem mp_fig_19_3_discretion {β κ lam σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlam : 0 < lam)
    (hκ : 0 < κ) (hσ : 0 < σ) (u : ℕ → ℝ) (hu0 : u 0 = σ) (hu : ∀ t, u (t + 1) = 0) :
    let pin : ℕ → ℝ := fun t => ex951pi β κ lam 0 0 (u t)
    let x : ℕ → ℝ := fun t =>
      (lam * 0 - κ * (β * ex951pi β κ lam 0 0 (0 * u t) + u t)) / (κ ^ 2 + lam)
    0 < pin 0 ∧ x 0 < 0 ∧ ∀ t, pin (t + 1) = 0 ∧ x (t + 1) = 0 := by
  intro pin x
  have hρ : |(0 : ℝ)| ≤ 1 := by simp
  have hcl : ∀ v, ex951pi β κ lam 0 0 v = lam / (κ ^ 2 + lam) * v := fun v => by
    rw [mp_ex951pi_closed hβ0 hβ1 hlam hρ]
    ring_nf
  have hk : 0 < κ ^ 2 + lam := by positivity
  refine ⟨?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · simp only [pin, hcl, hu0]
    positivity
  · simp only [x, hcl, hu0, zero_mul, mul_zero, zero_sub, zero_add]
    rw [div_neg_iff]
    right
    exact ⟨by nlinarith [mul_pos hκ hσ], hk⟩
  · simp only [pin, hcl, hu t, mul_zero]
  · simp only [x, hcl, hu t, mul_zero, zero_add, sub_zero, zero_div]

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Implementing strict inflation targeting: the Taylor principle (19.31) and Exercise 19.2

Miao, §19.2.3, p. 635 ((19.31)), and Exercise 19.2 of §19.5, p. 669. The setting is the one of
Miao, Exercise 2.2 (module `NewKeynesian`): a `CondExpSystem ℝ V`, the state
`X_t = (x_t, π_t)` (both jump variables), stable (bounded) adapted processes. The model is the
Phillips curve (19.24) `π_t = κx_t + βE_tπ_{t+1}`, the IS curve (19.28)
`x_t = E_tx_{t+1} − γ⁻¹(i_t − E_tπ_{t+1} − r^n_t)` and an interest-rate rule
`i_t = ī_t + φ_ππ_t + φ_yx_t` (`mpRuleEqm`; no policy shock).

* `mp_rule_eqm_iff`: with intercept `ī`, the model is Exercise 2.2's Taylor-rule model with the
  shock `ε_t = ī_t − r^n_t` (and no IS shock).
* `mp_zero_eqm_iff`: strict inflation targeting `π = x = 0` is an equilibrium iff `ī_t = r^n_t`
  at every date (`γ ≠ 0`); in that case `i_t = r^n_t` (`mp_strict_targeting_rate`).
* `mpImplements`: the rule implements the optimal policy if `π = x = 0` is an equilibrium and the
  only stable adapted one.
* `eq_19_31`: for `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0`, the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t`
  implements the optimal policy when `κ(φ_π − 1) + (1 − β)φ_y > 0`.
* `ex_19_2`: **Exercise 19.2**, corrected: for `φ_π, φ_y ≥ 0` (and `V` containing a nonzero
  `F_0`-measurable `w`), the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t` implements the optimal policy
  iff (19.31) holds. `mp_ex_19_2_instance`: a concrete instance (deterministic system, `κ = γ = 1`,
  `β = 1/2`, `φ_π = 3/2`, `φ_y = 0`), so the hypotheses are satisfiable.

**Correction.** The text and the exercise use the rule (19.29) `i_t = −ln β + φ_ππ_t + φ_yx_t`
"where the monetary policy shock is removed". Since `π = x = 0` requires `i_t = r^n_t`, that
rule implements strict inflation targeting only if the natural rate is constant at `−ln β`
(`mp_zero_eqm_iff`); `mp_printed_rule_fails` and `mp_printed_rule_counterexample` (deterministic
system, `r^n ≡ 1`, intercept `0`) show the printed statement fails otherwise. With the intercept
`r^n_t` (equivalently, (19.29) with `i_t, r^n_t` measured as deviations, no natural-rate shocks)
the exercise is true. (For `φ_π < 0` the exact determinacy condition has a second branch,
Exercise 2.2(b).)
-/

namespace Miao.NewKeynesian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The model (19.24), (19.28) with the rule `i_t = ī_t + φ_ππ_t + φ_yx_t` (Miao, p. 635);
`X t 0 = x_t`, `X t 1 = π_t`. -/
def mpRuleEqm (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn ibar : ℕ → V)
    (X : ℕ → Fin 2 → V) : Prop :=
  ∀ t, X t 1 = κ • X t 0 + β • E.E t (X (t + 1) 1) ∧
    X t 0 = E.E t (X (t + 1) 0) -
      γ⁻¹ • ((ibar t + φπ • X t 1 + φy • X t 0) - E.E t (X (t + 1) 1) - rn t)

/-- Miao, p. 635: the model with intercept `ī` is Exercise 2.2's Taylor-rule model
`nkTaylorEqm` with monetary shock `ε_t = ī_t − r^n_t` and no IS shock. -/
theorem mp_rule_eqm_iff (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn ibar : ℕ → V)
    (X : ℕ → Fin 2 → V) :
    mpRuleEqm E κ β γ φπ φy rn ibar X ↔
      nkTaylorEqm E κ β γ φπ φy (fun t => ibar t - rn t) (fun _ => 0) X := by
  refine forall_congr' fun t => and_congr Iff.rfl ?_
  have e : E.E t (X (t + 1) 0) -
      γ⁻¹ • ((ibar t + φπ • X t 1 + φy • X t 0) - E.E t (X (t + 1) 1) - rn t) =
      E.E t (X (t + 1) 0) - γ⁻¹ • ((φπ • X t 1 + φy • X t 0 + (ibar t - rn t)) -
        E.E t (X (t + 1) 1)) + 0 := by module
  rw [e]

/-- With intercept `r^n_t`, the model is Exercise 2.2's model with no shocks. -/
theorem mp_rule_eqm_rn_iff (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn : ℕ → V)
    (X : ℕ → Fin 2 → V) :
    mpRuleEqm E κ β γ φπ φy rn rn X ↔ nkTaylorEqm E κ β γ φπ φy (fun _ => 0) (fun _ => 0) X := by
  rw [mp_rule_eqm_iff]
  simp only [sub_self]

/-- **Strict inflation targeting as an equilibrium** (Miao, p. 635). For `γ ≠ 0`, the path
`π = x = 0` solves the model with the rule `i_t = ī_t + φ_ππ_t + φ_yx_t` iff `ī_t = r^n_t` at
every date. -/
theorem mp_zero_eqm_iff (E : CondExpSystem ℝ V) {γ : ℝ} (hγ : γ ≠ 0) (κ β φπ φy : ℝ)
    (rn ibar : ℕ → V) :
    mpRuleEqm E κ β γ φπ φy rn ibar 0 ↔ ∀ t, ibar t = rn t := by
  simp only [mpRuleEqm, Pi.zero_apply, map_zero, smul_zero, add_zero, sub_zero, zero_sub,
    true_and]
  refine forall_congr' fun t => ?_
  rw [eq_comm, neg_eq_zero, smul_eq_zero, sub_eq_zero]
  simp [hγ]

/-- The rule with intercept `ī` **implements the optimal policy** (Miao, p. 635) if strict
inflation targeting `π = x = 0` is an equilibrium and it is the only stable adapted one. -/
def mpImplements (E : CondExpSystem ℝ V) (κ β γ φπ φy : ℝ) (rn ibar : ℕ → V) : Prop :=
  mpRuleEqm E κ β γ φπ φy rn ibar 0 ∧
    ∀ X, mpRuleEqm E κ β γ φπ φy rn ibar X → IsAdaptedV E X → IsStableProc X → X = 0

/-- **The Taylor principle (19.31)** (Miao, p. 635). For `κ, γ > 0`, `0 < β < 1`, `φ_y ≥ 0`, if
`κ(φ_π − 1) + (1 − β)φ_y > 0`, the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t` implements strict inflation
targeting, for any natural-rate process `r^n`. -/
theorem eq_19_31 [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ φπ φy : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφy : 0 ≤ φy)
    (h31 : 0 < κ * (φπ - 1) + (1 - β) * φy) (rn : ℕ → V) :
    mpImplements E κ β γ φπ φy rn rn := by
  have hz : mpRuleEqm E κ β γ φπ φy rn rn 0 := (mp_zero_eqm_iff E hγ.ne' κ β φπ φy rn rn).2
    fun _ => rfl
  refine ⟨hz, fun X hX hXa hXs => ?_⟩
  have hdet := ex_2_2_suff E hκ hβ0 hβ1 hγ hφy (Or.inl h31)
  obtain ⟨Y, -, hYu⟩ := hdet (fun _ => 0) (fun _ => 0) ⟨0, fun _ => by simp⟩
    ⟨0, fun _ => by simp⟩ (fun _ => map_zero _) (fun _ => map_zero _)
  have h1 := hYu X ⟨(mp_rule_eqm_rn_iff E κ β γ φπ φy rn X).1 hX, hXa, hXs⟩
  have h2 := hYu 0 ⟨(mp_rule_eqm_rn_iff E κ β γ φπ φy rn 0).1 hz, fun _ _ => map_zero _,
    ⟨1, one_pos, fun _ _ => by simp⟩⟩
  exact h1.trans h2.symm

/-- **Exercise 19.2** (Miao, p. 669), corrected. For `κ, γ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`, and
`V` containing a nonzero `F_0`-measurable `w`, the rule `i_t = r^n_t + φ_ππ_t + φ_yx_t` implements
the optimal policy (strict inflation targeting) iff (19.31) `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem ex_19_2 [CompleteSpace V] (E : CondExpSystem ℝ V) {κ β γ φπ φy : ℝ} (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) {w : V}
    (hw : w ≠ 0) (hw0 : E.E 0 w = w) (rn : ℕ → V) :
    mpImplements E κ β γ φπ φy rn rn ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  refine ⟨fun himp => ?_, fun h31 => eq_19_31 E hκ hβ0 hβ1 hγ hφy h31 rn⟩
  by_contra hc
  have hnb : ¬ nkBothOut (nkWT κ β γ φπ φy 0 0 + nkWT κ β γ φπ φy 1 1)
      (nkWT κ β γ φπ φy 0 0 * nkWT κ β γ φπ φy 1 1 -
        nkWT κ β γ φπ φy 0 1 * nkWT κ β γ φπ φy 1 0) := by
    intro hb
    rcases (nk_bothOut_WT hκ hβ0 hβ1 hγ hφy).1 hb with h | h
    · exact hc h
    · nlinarith [mul_nonneg hκ.le hφπ, mul_nonneg hβ0.le hφy]
  have hM10 : nkWT κ β γ φπ φy 1 0 ≠ 0 := by
    have e : nkWT κ β γ φπ φy 1 0 = -κ / β := by simp [nkWT]
    rw [e]
    exact div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  obtain ⟨X, hX0, hXe, hXa, hXs⟩ := nk_jump2_nonunique E (nkWT κ β γ φπ φy) hM10
    (nk_WT_trace hκ hβ0 hβ1 hγ hφy) hnb hw hw0
  have hz : (![γ⁻¹ • (0 : V) - 0, 0] : Fin 2 → V) = 0 := by
    funext i
    fin_cases i <;> simp
  have hXeq : mpRuleEqm E κ β γ φπ φy rn rn X :=
    (mp_rule_eqm_rn_iff E κ β γ φπ φy rn X).2
      ((nk_taylor_iff E φπ φy hβ0.ne' _ _ X).2 fun t => by rw [hXe t, hz, add_zero])
  exact hX0 (himp.2 X hXeq hXa hXs)

/-- **The printed rule (19.29) fails** (Miao, pp. 635 and 669). With a constant intercept `c`
(`c = −ln β` in (19.29)), if the natural rate differs from `c` at some date (`γ ≠ 0`), strict
inflation targeting is not an equilibrium, so the rule does not implement it. -/
theorem mp_printed_rule_fails (E : CondExpSystem ℝ V) {γ : ℝ} (hγ : γ ≠ 0) (κ β φπ φy : ℝ)
    (rn : ℕ → V) (c : V) (hrn : ∃ t, rn t ≠ c) :
    ¬ mpImplements E κ β γ φπ φy rn (fun _ => c) := by
  rintro ⟨h0, -⟩
  obtain ⟨t, ht⟩ := hrn
  exact ht ((mp_zero_eqm_iff E hγ κ β φπ φy rn (fun _ => c)).1 h0 t).symm

/-- The deterministic conditional-expectation system on `ℝ`: `E_t = id`. -/
noncomputable def mpDetSystem : CondExpSystem ℝ ℝ where
  E := fun _ => ContinuousLinearMap.id ℝ ℝ
  norm_le := fun _ => ContinuousLinearMap.norm_id_le
  tower_le := fun _ _ _ => ContinuousLinearMap.id_comp _
  tower_ge := fun _ _ _ => ContinuousLinearMap.id_comp _

/-- **Counterexample to the printed Exercise 19.2** (Miao, p. 669). In the deterministic system
with `κ = γ = 1`, `β = 1/2`, `φ_π = 3/2`, `φ_y = 0` ((19.31) holds), a natural rate `r^n ≡ 1`
and the printed constant intercept `0` (the steady-state rate), the rule does not implement
strict inflation targeting, while the rule with intercept `r^n_t` does. -/
theorem mp_printed_rule_counterexample :
    0 < (1 : ℝ) * (3 / 2 - 1) + (1 - 1 / 2) * 0 ∧
      ¬ mpImplements mpDetSystem 1 (1 / 2) 1 (3 / 2) 0 (fun _ => 1) (fun _ => 0) ∧
      mpImplements mpDetSystem 1 (1 / 2) 1 (3 / 2) 0 (fun _ => 1) (fun _ => 1) := by
  refine ⟨by norm_num, mp_printed_rule_fails mpDetSystem one_ne_zero 1 (1 / 2) (3 / 2) 0 _ 0
    ⟨0, one_ne_zero⟩, eq_19_31 mpDetSystem one_pos (by norm_num) (by norm_num) one_pos le_rfl
    (by norm_num) _⟩

/-- **Exercise 19.2, an instance**: the hypotheses of `ex_19_2` are satisfiable (deterministic
system, `w = 1`), and there the rule with `φ_π = 3/2`, `φ_y = 0` implements the optimal policy
while `φ_π = 1/2` does not. -/
theorem mp_ex_19_2_instance (rn : ℕ → ℝ) :
    mpImplements mpDetSystem 1 (1 / 2) 1 (3 / 2) 0 rn rn ∧
      ¬ mpImplements mpDetSystem 1 (1 / 2) 1 (1 / 2) 0 rn rn := by
  have hw0 : mpDetSystem.E 0 (1 : ℝ) = 1 := rfl
  refine ⟨(ex_19_2 mpDetSystem one_pos (by norm_num) (by norm_num) one_pos (by norm_num) le_rfl
    one_ne_zero hw0 rn).2 (by norm_num), fun h => ?_⟩
  have := (ex_19_2 mpDetSystem one_pos (by norm_num) (by norm_num) one_pos (by norm_num) le_rfl
    one_ne_zero hw0 rn).1 h
  norm_num at this

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiscal stimulus: the neoclassical benchmark and monopolistic competition

Miao, §19.3, pp. 640–643, (19.36)–(19.43) (following Woodford 2011).

The household maximises `Σ βᵗ[u(C_t) − v(N_t)]` (19.36), output is `Y_t = f(N_t)` (19.37) and
`C_t + G_t = Y_t` (19.38). With `f` a bijection of `ℝ` with inverse `f⁻¹` and `f' > 0`, the
disutility of producing `Y` is `ṽ(Y) = v(f⁻¹(Y))` (`fs_vtilde`).

* `fs_vtilde_hasDerivAt`, `fs_vtilde_deriv2`: `ṽ'(Y) = v'(f⁻¹Y)/f'(f⁻¹Y)` and
  `ṽ'' = (v''f' − v'f'')/f'³`, so `ṽ'' > 0` when `v'' ≥ 0` and `f'' < 0` (`fs_vtilde_deriv2_pos`).
* (19.39) ⟹ (19.40): `eq_19_40` (the book writes `ṽ(Y_t)` for the derivative `ṽ'(Y_t)`).
* (19.41): the steady-state multiplier `dY/dG = η_u/(η_u + η_v) ∈ (0, 1)`, proved by implicit
  differentiation of any differentiable solution path of `u'(Y − G) = μṽ'(Y)` (`eq_19_41`,
  general wedge `μ > 0`, so also the monopolistic case (19.43); `fs_multiplier_formula` without
  sign conditions).
* The markup `μ = ε/(ε − 1)` from the monopolist's first-order condition (`fs_markup_foc`),
  (19.42) (`eq_19_42`) and (19.43) (`eq_19_43`).
* An endogenous wedge falling with `G` raises the multiplier (`fs_endogenous_wedge`).

**Correction.** The book assumes `v'' < 0`; then `η_v` can be negative and the multiplier can
exceed one (`fs_eq_19_41_vpp_neg`: `u = log`, `f = id`, `v = 2 log(1 + N)` gives `dY/dG = 2`).
The correct assumption is `v'' > 0` (convex disutility of work), or `v'' ≥ 0` with `f'' < 0`.
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- The disutility of producing output `Y`: `ṽ(Y) = v(f⁻¹(Y))` (Miao, (19.40), p. 641). -/
def fs_vtilde (v finv : ℝ → ℝ) : ℝ → ℝ := fun Y => v (finv Y)

/-- The (positive) elasticity of marginal utility `η_u = −Ȳu''/u'` (Miao, p. 641). -/
noncomputable def fs_etaU (Y u1 u2 : ℝ) : ℝ := -Y * u2 / u1

/-- The elasticity `η_v = Ȳṽ''/ṽ'` (Miao, p. 641). -/
noncomputable def fs_etaV (Y vt1 vt2 : ℝ) : ℝ := Y * vt2 / vt1

/-- The neoclassical multiplier `Γ = η_u/(η_u + η_v)` (Miao, (19.41), p. 641). -/
noncomputable def fs_Gamma (ηu ηv : ℝ) : ℝ := ηu / (ηu + ηv)

/-- Miao, p. 641: `Γ > 0` for `η_u, η_v > 0`. -/
theorem fs_Gamma_pos {ηu ηv : ℝ} (hu : 0 < ηu) (hv : 0 < ηv) : 0 < fs_Gamma ηu ηv :=
  div_pos hu (by linarith)

/-- Miao, p. 641: `Γ < 1` for `η_u, η_v > 0` (government purchases crowd out consumption). -/
theorem fs_Gamma_lt_one {ηu ηv : ℝ} (hu : 0 < ηu) (hv : 0 < ηv) : fs_Gamma ηu ηv < 1 := by
  unfold fs_Gamma
  rw [div_lt_one (by linarith)]
  linarith

/-- Miao, (19.40), p. 641: if `f` is a bijection with inverse `finv` and `f' > 0`, then the
inverse is differentiable and `ṽ'(Y) = v'(f⁻¹(Y))/f'(f⁻¹(Y))`. -/
theorem fs_vtilde_hasDerivAt {v v1 f f1 finv : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (v1 x) x)
    (hf : ∀ x, HasDerivAt f (f1 x) x) (hf1 : ∀ x, 0 < f1 x) (hfg : ∀ y, f (finv y) = y)
    (hgf : ∀ x, finv (f x) = x) (Y : ℝ) :
    HasDerivAt (fs_vtilde v finv) (v1 (finv Y) / f1 (finv Y)) Y := by
  have hmono : StrictMono f := strictMono_of_deriv_pos fun x => by rw [(hf x).deriv]; exact hf1 x
  have hgmono : Monotone finv := by
    intro a b hab
    by_contra h
    push Not at h
    have := hmono h
    rw [hfg, hfg] at this
    linarith
  have hgsurj : Function.Surjective finv := fun x => ⟨f x, hgf x⟩
  have hgc : Continuous finv := hgmono.continuous_of_surjective hgsurj
  have hg : HasDerivAt finv (f1 (finv Y))⁻¹ Y :=
    HasDerivAt.of_local_left_inverse hgc.continuousAt (hf (finv Y)) (hf1 _).ne'
      (Eventually.of_forall hfg)
  have := (hv (finv Y)).comp Y hg
  rw [div_eq_mul_inv]
  exact this

/-- Miao, (19.40)–(19.41), p. 641: the second derivative of `ṽ`. If `ṽ'(Y) = v'(g Y)/f'(g Y)`
with `g = f⁻¹` differentiable with derivative `1/f'(g Y)`, then
`ṽ''(Y) = (v''f' − v'f'')/f'³` evaluated at `N = f⁻¹(Y)`. -/
theorem fs_vtilde_deriv2 {v1 v2 f1 f2 finv : ℝ → ℝ} {Y : ℝ}
    (hv1 : HasDerivAt v1 (v2 (finv Y)) (finv Y)) (hf1 : HasDerivAt f1 (f2 (finv Y)) (finv Y))
    (hg : HasDerivAt finv (f1 (finv Y))⁻¹ Y) (hpos : 0 < f1 (finv Y)) :
    HasDerivAt (fun y => v1 (finv y) / f1 (finv y))
      ((v2 (finv Y) * f1 (finv Y) - v1 (finv Y) * f2 (finv Y)) / f1 (finv Y) ^ 3) Y := by
  have h1 := hv1.comp Y hg
  have h2 := hf1.comp Y hg
  refine (h1.div h2 hpos.ne').congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp

/-- Miao, p. 641: `η_v > 0`, i.e. `ṽ'' > 0`, when `v' > 0`, `v'' ≥ 0`, `f' > 0` and `f'' < 0`
(the book's `v'' < 0` is a misprint, see `fs_eq_19_41_vpp_neg`). -/
theorem fs_vtilde_deriv2_pos {v1N v2N f1N f2N : ℝ} (hv1 : 0 < v1N) (hv2 : 0 ≤ v2N)
    (hf1 : 0 < f1N) (hf2 : f2N < 0) : 0 < (v2N * f1N - v1N * f2N) / f1N ^ 3 := by
  apply div_pos _ (by positivity)
  nlinarith [mul_nonneg hv2 hf1.le, mul_pos hv1 (neg_pos.2 hf2)]

/-- Miao, (19.39) ⟹ (19.40), p. 641: in a competitive equilibrium (`v'(N)/u'(C) = W/P`,
`f'(N) = W/P`), with `Y = f(N)` and `C + G = Y`, `u'(Y − G) = v'(f⁻¹Y)/f'(f⁻¹Y)`, which is
`ṽ'(Y)` by `fs_vtilde_hasDerivAt`. -/
theorem eq_19_40 {u1 v1 f f1 finv : ℝ → ℝ} {N C G Y w : ℝ} (hY : Y = f N) (hC : C + G = Y)
    (hlab : v1 N / u1 C = w) (hfirm : f1 N = w) (hu : u1 C ≠ 0) (hv : v1 N ≠ 0)
    (hgf : finv (f N) = N) : u1 (Y - G) = v1 (finv Y) / f1 (finv Y) := by
  have hCY : Y - G = C := by linarith
  rw [hCY, hY, hgf, hfirm, ← hlab]
  field_simp

/-- Miao, (19.41), p. 641, without sign conditions: if `Ysol` is a solution path of the
steady-state condition `u'(Y − G) = μṽ'(Y)` near `Ḡ`, differentiable at `Ḡ`, then
`(u'' − μṽ'')·dY/dG = u''`. -/
theorem fs_multiplier_formula {u1 vt1 Ysol : ℝ → ℝ} {Gb Y' u2 vt2 μ : ℝ}
    (hY : HasDerivAt Ysol Y' Gb) (heq : ∀ᶠ G in 𝓝 Gb, u1 (Ysol G - G) = μ * vt1 (Ysol G))
    (hu : HasDerivAt u1 u2 (Ysol Gb - Gb)) (hvt : HasDerivAt vt1 vt2 (Ysol Gb)) :
    (u2 - μ * vt2) * Y' = u2 := by
  have hC : HasDerivAt (fun G => Ysol G - G) (Y' - 1) Gb := hY.sub (hasDerivAt_id Gb)
  have h1 := hu.comp (h := fun G => Ysol G - G) Gb hC
  have h2 := (hvt.comp Gb hY).const_mul μ
  have hF := h1.sub h2
  have h0 : HasDerivAt (fun G => u1 (Ysol G - G) - μ * vt1 (Ysol G)) 0 Gb := by
    apply (hasDerivAt_const Gb (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [heq] with G hG
    simp [hG]
  have := hF.unique h0
  linear_combination this

/-- Miao, (19.41) and (19.43), pp. 641–643: the steady-state fiscal multiplier. Let `Ysol` be a
solution path of `u'(Y − G) = μṽ'(Y)` (`μ = 1`: (19.40); `μ > 0` the efficiency wedge: (19.43)),
differentiable at `Ḡ`, with `Ȳ = Ysol Ḡ > 0`, `u' > 0`, `u'' < 0`, `ṽ'' > 0`. Then
`dY/dG = η_u/(η_u + η_v)`, and `0 < dY/dG < 1`. -/
theorem eq_19_41 {u1 vt1 Ysol : ℝ → ℝ} {Gb Y' u2 vt2 μ : ℝ}
    (hY : HasDerivAt Ysol Y' Gb) (heq : ∀ᶠ G in 𝓝 Gb, u1 (Ysol G - G) = μ * vt1 (Ysol G))
    (hu : HasDerivAt u1 u2 (Ysol Gb - Gb)) (hvt : HasDerivAt vt1 vt2 (Ysol Gb))
    (hYb : 0 < Ysol Gb) (hu1 : 0 < u1 (Ysol Gb - Gb)) (hu2 : u2 < 0) (hvt2 : 0 < vt2)
    (hμ : 0 < μ) :
    Y' = fs_Gamma (fs_etaU (Ysol Gb) (u1 (Ysol Gb - Gb)) u2)
        (fs_etaV (Ysol Gb) (vt1 (Ysol Gb)) vt2) ∧ 0 < Y' ∧ Y' < 1 := by
  have hf := fs_multiplier_formula hY heq hu hvt
  have hss : u1 (Ysol Gb - Gb) = μ * vt1 (Ysol Gb) := heq.self_of_nhds
  have hvt1 : 0 < vt1 (Ysol Gb) := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ.le h]
  have hden : u2 - μ * vt2 < 0 := by nlinarith [mul_pos hμ hvt2]
  have hY' : Y' = u2 / (u2 - μ * vt2) := by
    rw [eq_div_iff hden.ne]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hY']
    unfold fs_Gamma fs_etaU fs_etaV
    rw [hss]
    have hne2 : -u2 + μ * vt2 ≠ 0 := by linarith
    have hne1 : u2 - μ * vt2 ≠ 0 := hden.ne
    field_simp
    ring
  · rw [hY']
    exact div_pos_of_neg_of_neg hu2 hden
  · rw [hY', div_lt_one_of_neg hden]
    nlinarith [mul_pos hμ hvt2]

/-- Miao, p. 642: profit maximisation of a monopolist facing demand with elasticity `ε > 1`.
The derivative of the profit `(p − m)p^{−ε}` (real price `p`, real marginal cost `m`) is zero
iff `p = μm` with `μ = ε/(ε − 1)`. -/
theorem fs_markup_foc {ε m p : ℝ} (hε : 1 < ε) (hp : 0 < p) :
    HasDerivAt (fun q => (q - m) * q ^ (-ε))
      (p ^ (-ε) + (p - m) * (-ε * p ^ (-ε - 1))) p ∧
    (p ^ (-ε) + (p - m) * (-ε * p ^ (-ε - 1)) = 0 ↔ p = ε / (ε - 1) * m) := by
  refine ⟨?_, ?_⟩
  · have h := Real.hasDerivAt_rpow_const (p := -ε) (Or.inl hp.ne')
    refine (((hasDerivAt_id p).sub_const m).mul h).congr_deriv ?_
    simp
  · have hpe : p ^ (-ε - 1) = p ^ (-ε) / p := by
      rw [Real.rpow_sub hp, Real.rpow_one]
    have hpos : 0 < p ^ (-ε) := Real.rpow_pos_of_pos hp _
    have hε1 : ε - 1 ≠ 0 := by linarith
    have key : p ^ (-ε) + (p - m) * (-ε * p ^ (-ε - 1)) =
        p ^ (-ε) * ((1 - ε) * p + ε * m) / p := by
      rw [hpe]
      field_simp
      ring
    rw [key]
    constructor
    · intro h
      have h2 : (1 - ε) * p + ε * m = 0 := by
        rcases div_eq_zero_iff.1 h with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact absurd h4 hpos.ne'
          · exact h4
        · exact absurd h3 hp.ne'
      field_simp
      linarith
    · intro h
      have h2 : (1 - ε) * p + ε * m = 0 := by
        rw [h]
        field_simp
        ring
      rw [h2]
      simp

/-- Miao, (19.42), p. 642: the real price is the markup over real marginal cost, so real marginal
cost is `1/μ`: `W/(Pf'(N)) = 1/μ` iff `P = μW/f'(N)`. -/
theorem eq_19_42 {W P f1N μ : ℝ} (hP : 0 < P) (hf : 0 < f1N) (hμ : 0 < μ) :
    W / (P * f1N) = 1 / μ ↔ P = μ * W / f1N := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    have hW : W ≠ 0 := by
      rintro rfl
      simp at h
      linarith
    field_simp

/-- Miao, (19.43), p. 643: with the labour-supply condition `v'(N)/u'(C) = W/P` and the markup
(19.42) `W/P = f'(N)/μ`, `Y = f(N)`, `C + G = Y`: `u'(Y − G) = μ·v'(f⁻¹Y)/f'(f⁻¹Y)`, i.e.
`u'(Y − G) = μṽ'(Y)`. -/
theorem eq_19_43 {u1 v1 f f1 finv : ℝ → ℝ} {N C G Y w μ : ℝ} (hY : Y = f N) (hC : C + G = Y)
    (hlab : v1 N / u1 C = w) (hmark : w = f1 N / μ) (hu : u1 C ≠ 0) (hf1 : f1 N ≠ 0)
    (hμ : μ ≠ 0) (hgf : finv (f N) = N) :
    u1 (Y - G) = μ * (v1 (finv Y) / f1 (finv Y)) := by
  have hCY : Y - G = C := by linarith
  rw [hCY, hY, hgf]
  rw [hmark] at hlab
  field_simp at hlab ⊢
  linarith

/-- Miao, p. 643: an endogenous efficiency wedge. If the wedge `μ(G)` falls with government
purchases (`μ'(Ḡ) < 0`, e.g. sticky prices), the multiplier exceeds the fixed-wedge multiplier
`u''/(u'' − μ̄ṽ'') = η_u/(η_u + η_v)` of (19.43). -/
theorem fs_endogenous_wedge {u1 vt1 Ysol μf : ℝ → ℝ} {Gb Y' u2 vt2 μ' : ℝ}
    (hY : HasDerivAt Ysol Y' Gb) (hμf : HasDerivAt μf μ' Gb)
    (heq : ∀ᶠ G in 𝓝 Gb, u1 (Ysol G - G) = μf G * vt1 (Ysol G))
    (hu : HasDerivAt u1 u2 (Ysol Gb - Gb)) (hvt : HasDerivAt vt1 vt2 (Ysol Gb))
    (hu2 : u2 < 0) (hvt2 : 0 < vt2) (hμ : 0 < μf Gb) (hvt1 : 0 < vt1 (Ysol Gb)) :
    Y' = (u2 + μ' * vt1 (Ysol Gb)) / (u2 - μf Gb * vt2) ∧
      (μ' < 0 → u2 / (u2 - μf Gb * vt2) < Y') := by
  have hC : HasDerivAt (fun G => Ysol G - G) (Y' - 1) Gb := hY.sub (hasDerivAt_id Gb)
  have h1 := hu.comp (h := fun G => Ysol G - G) Gb hC
  have h2 := hμf.mul (hvt.comp Gb hY)
  have hF := h1.sub h2
  have h0 : HasDerivAt (fun G => u1 (Ysol G - G) - μf G * vt1 (Ysol G)) 0 Gb := by
    apply (hasDerivAt_const Gb (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [heq] with G hG
    simp [hG]
  have := hF.unique h0
  simp only [Function.comp_def] at this
  have hden : u2 - μf Gb * vt2 < 0 := by nlinarith [mul_pos hμ hvt2]
  have hY' : Y' = (u2 + μ' * vt1 (Ysol Gb)) / (u2 - μf Gb * vt2) := by
    rw [eq_div_iff hden.ne]
    linear_combination this
  refine ⟨hY', fun hneg => ?_⟩
  rw [hY', add_div]
  have : 0 < μ' * vt1 (Ysol Gb) / (u2 - μf Gb * vt2) :=
    div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hneg hvt1) hden
  linarith

/-- **Counterexample to the printed `v'' < 0`** (Miao, p. 640–641): with `u = log`, `f = id` and
the concave disutility `v(N) = 2 log(1 + N)` (`v' > 0`, `v'' < 0` on `N > −1`), the path
`Y(G) = 1 + 2G` solves (19.40) `u'(Y − G) = ṽ'(Y)` for `G > −1`, and `dY/dG = 2 > 1`:
the multiplier is not less than one. -/
theorem fs_eq_19_41_vpp_neg :
    (∀ N : ℝ, -1 < N → HasDerivAt (fun n => 2 * Real.log (1 + n)) (2 / (1 + N)) N ∧
      0 < 2 / (1 + N) ∧ HasDerivAt (fun n => 2 / (1 + n)) (-2 / (1 + N) ^ 2) N ∧
      -2 / (1 + N) ^ 2 < 0) ∧
    (∀ G : ℝ, -1 < G → 1 / ((1 + 2 * G) - G) = 2 / (1 + (1 + 2 * G))) ∧
    HasDerivAt (fun G : ℝ => 1 + 2 * G) 2 0 ∧ (1 : ℝ) < 2 := by
  refine ⟨fun N hN => ?_, fun G hG => ?_, ?_, by norm_num⟩
  · have h1 : 0 < 1 + N := by linarith
    refine ⟨?_, by positivity, ?_, ?_⟩
    · have := ((hasDerivAt_id' N).const_add 1).log h1.ne'
      convert this.const_mul 2 using 1
      ring
    · have := ((hasDerivAt_id N).const_add 1).inv h1.ne'
      convert this.const_mul 2 using 1
      · funext n
        simp [div_eq_mul_inv]
      · simp
        ring
    · have : 0 < (1 + N) ^ 2 := by positivity
      exact div_neg_of_neg_of_pos (by norm_num) this
  · have h1 : (1 + 2 * G) - G ≠ 0 := by linarith
    have h2 : 1 + (1 + 2 * G) ≠ 0 := by linarith
    field_simp
    ring
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_add 1

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiscal stimulus in a DNK model: the Phillips curve and the Taylor-rule multiplier

Miao, §19.3, pp. 643–647, (19.44)–(19.52) (following Woodford 2011). The model is deterministic.

* (19.44): the zero-inflation steady state has `r̄ = −ln β` (`eq_19_44`); with `r_t = r̄` for all
  `t` and `C_t → C̄`, consumption is constant at `C̄` and the multiplier is one
  (`fs_constant_real_rate`).
* (19.45)–(19.46): the firm's cost-minimisation first-order conditions (`fs_costmin_foc`), the
  common labour/capital ratio (`fs_ratio_strictMonoOn`, `fs_common_ratio`), which equals aggregate
  hours (`fs_ratio_eq_hours`), and the common marginal cost (`eq_19_46`).
* (19.47): `ṽ'(Y)/u'(Y − G) = MC` (`eq_19_47`).
* The recursive reset-price equation, `q_t` and the Phillips curve
  `π_t = βπ_{t+1} + (1 − βθ)(1 − θ)/θ · MĈ_t` (`fs_reset_recursive`, `fs_q_recursive`,
  `fs_nkpc`).
* The log-linearised Euler equation (19.50) with `σ = 1/η_u` (`fs_euler_loglin`, `eq_19_50`).
* The log-linearisation of (19.47): `MĈ = (η_u + η_v)(Ŷ − ΓĜ)` (`fs_mc_loglin`, as a directional
  derivative). The book prints `(η_u + η_v)Ŷ_t − ΓĜ_t`; the `Γ` term must also be multiplied by
  `η_u + η_v`, as the book's own (19.48) uses.
* (19.48): the forward solution `π_t = κΣβʲ(Ŷ_{t+j} − ΓĜ_{t+j})`, the unique bounded solution
  (`fs_forward_hasSum`, `fs_forward_exists`, `eq_19_48`, `fs_kappa_pos`).
* (19.49)–(19.52): with `Ĝ_t = ρᵗĜ₀` the conjecture (19.51) is an equilibrium iff the
  coefficients are given by (19.52) (`eq_19_52`); `ψ > 0` (`fs_psi_pos`), `0 < γ_y < 1`
  (`fs_gammaY_pos`, `fs_gammaY_lt_one`), and `γ_y < Γ` iff `φ_y` is large enough
  (`fs_gammaY_lt_Gamma_iff`). We read the garbled (19.52) as
  `γ_y = (1 − ρ + (ψ − σφ_y)Γ)/(1 − ρ + ψ)`, which is what the derivation gives.
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- A real sequence is bounded. -/
def fs_Bdd (x : ℕ → ℝ) : Prop := ∃ B, ∀ t, |x t| ≤ B

/-- Miao, (19.44), p. 644: in a zero-inflation steady state `C_t = C̄`, the Euler equation
`u'(C_t)/(βu'(C_{t+1})) = exp(r_t)` gives `r̄ = −ln β`. -/
theorem eq_19_44 {β uC r : ℝ} (hβ : 0 < β) (hu : uC ≠ 0) (h : uC / (β * uC) = Real.exp r) :
    r = -Real.log β := by
  have : Real.exp r = β⁻¹ := by
    rw [← h]
    field_simp
  rw [← Real.log_exp r, this, Real.log_inv]

/-- Miao, p. 644: if monetary policy keeps `r_t = r̄ = −ln β` for all `t`, `u'` is injective
and `C_t → C̄`, then `C_t = C̄` for all `t`, and `Y_t = C̄ + G_t`: every unit of government
purchases raises output by one unit (`Y_t − Y_s = G_t − G_s`). -/
theorem fs_constant_real_rate {β Cb : ℝ} {u1 : ℝ → ℝ} {C G Y : ℕ → ℝ} (hβ : 0 < β)
    (hinj : Function.Injective u1) (hu : ∀ t, u1 (C (t + 1)) ≠ 0)
    (heul : ∀ t, u1 (C t) / (β * u1 (C (t + 1))) = Real.exp (-Real.log β))
    (hlim : Tendsto C atTop (𝓝 Cb)) (hres : ∀ t, C t + G t = Y t) :
    (∀ t, C t = Cb) ∧ ∀ t s, Y t - Y s = G t - G s := by
  have hstep : ∀ t, C (t + 1) = C t := by
    intro t
    have h := heul t
    rw [Real.exp_neg, Real.exp_log hβ] at h
    have hb : u1 (C t) = u1 (C (t + 1)) := by
      have := hu t
      field_simp at h
      linarith
    exact (hinj hb).symm
  have hconst : ∀ t, C t = C 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
  have hC0 : C 0 = Cb := by
    have : Tendsto C atTop (𝓝 (C 0)) := by
      have : C = fun _ => C 0 := funext hconst
      rw [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique this hlim
  refine ⟨fun t => (hconst t).trans hC0, fun t s => ?_⟩
  rw [← hres t, ← hres s, hconst t, hconst s]
  ring

/-- Miao, (19.45), p. 644–645: the partial derivatives of the constant-returns technology
`F(K, N) = Kf(N/K)` at `K > 0`: `∂F/∂K = f(n) − nf'(n)` and `∂F/∂N = f'(n)`, `n = N/K`. The
cost-minimisation first-order conditions are `R^k/P = MC·∂F/∂K` and `W/P = MC·∂F/∂N`. -/
theorem fs_costmin_foc {f f1 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x) {K N : ℝ}
    (hK : 0 < K) :
    HasDerivAt (fun k => k * f (N / k)) (f (N / K) - N / K * f1 (N / K)) K ∧
      HasDerivAt (fun m => K * f (m / K)) (f1 (N / K)) N := by
  constructor
  · have h1 : HasDerivAt (fun k => N / k) (-N / K ^ 2) K := by
      refine ((hasDerivAt_const K N).div (hasDerivAt_id' K) hK.ne').congr_deriv ?_
      ring
    have h2 := (hf (N / K)).comp K h1
    refine ((hasDerivAt_id' K).mul h2).congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
    ring
  · have h1 : HasDerivAt (fun m => m / K) (1 / K) N := by
      simpa using (hasDerivAt_id N).div_const K
    refine (((hf (N / K)).comp N h1).const_mul K).congr_deriv ?_
    field_simp

/-- Miao, p. 645: eliminating `MC` from the two first-order conditions gives
`(R^k/P)/(W/P) = h(n) = f(n)/f'(n) − n`; `h` is strictly increasing on `n > 0` when `f > 0`,
`f' > 0` and `f'' < 0` (`h' = −ff''/f'² > 0`). -/
theorem fs_ratio_strictMonoOn {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hpos : ∀ x, 0 < x → 0 < f x) (hd : ∀ x, 0 < f1 x)
    (hcc : ∀ x, f2 x < 0) : StrictMonoOn (fun n => f n / f1 n - n) (Set.Ioi 0) := by
  have hder : ∀ x, HasDerivAt (fun n => f n / f1 n - n)
      ((f1 x * f1 x - f x * f2 x) / f1 x ^ 2 - 1) x := fun x =>
    ((hf x).div (hf1 x) (hd x).ne').sub (hasDerivAt_id x)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact fun x _ => (hder x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hder x).deriv]
    have h1 := hd x
    have h2 := hpos x hx
    have h3 := hcc x
    have : (f1 x * f1 x - f x * f2 x) / f1 x ^ 2 - 1 = -(f x * f2 x) / f1 x ^ 2 := by
      field_simp
      ring
    rw [this]
    apply div_pos _ (by positivity)
    nlinarith [mul_pos h2 (neg_pos.2 h3)]

/-- Miao, p. 645: every firm chooses the same labour/capital ratio: if two firms' ratios
`n₁, n₂ > 0` both satisfy the first-order conditions with the same factor prices
(`h(n₁) = h(n₂)`), then
`n₁ = n₂`. -/
theorem fs_common_ratio {f f1 f2 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x, HasDerivAt f1 (f2 x) x) (hpos : ∀ x, 0 < x → 0 < f x) (hd : ∀ x, 0 < f1 x)
    (hcc : ∀ x, f2 x < 0) {n₁ n₂ : ℝ} (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (h : f n₁ / f1 n₁ - n₁ = f n₂ / f1 n₂ - n₂) : n₁ = n₂ :=
  (fs_ratio_strictMonoOn hf hf1 hpos hd hcc).injOn h₁ h₂ h

/-- Miao, p. 645: with a common labour/capital ratio `n` (`N_j = nK_j`) and total capital one
(`Σ K_j = 1`), the ratio equals aggregate hours `N = Σ N_j`. -/
theorem fs_ratio_eq_hours {ι : Type*} (s : Finset ι) (K L : ι → ℝ) (n : ℝ)
    (hL : ∀ j ∈ s, L j = n * K j) (hK : ∑ j ∈ s, K j = 1) : ∑ j ∈ s, L j = n := by
  rw [Finset.sum_congr rfl hL, ← Finset.mul_sum, hK, mul_one]

/-- Miao, (19.46), p. 645: the common real marginal cost `MC = W/(Pf'(N))`, from
`W/P = MC·f'(N)`. -/
theorem eq_19_46 {W P f1N MC : ℝ} (hP : P ≠ 0) (hf : f1N ≠ 0) (h : W / P = MC * f1N) :
    MC = W / (P * f1N) := by
  field_simp at h ⊢
  linarith

/-- Miao, (19.47), p. 645: from the labour-supply condition `v'(N)/u'(Y − G) = W/P` and
`W/P = MC·f'(N)`, with `N = f⁻¹(Y)`: `ṽ'(Y)/u'(Y − G) = MC`, where `ṽ'(Y) = v'(N)/f'(N)`
(`fs_vtilde_hasDerivAt`). -/
theorem eq_19_47 {u1 v1 f1 finv : ℝ → ℝ} {N Y G w MC : ℝ} (hN : finv Y = N)
    (hlab : v1 N / u1 (Y - G) = w) (hmc : w = MC * f1 N) (hf : f1 N ≠ 0) (hu : u1 (Y - G) ≠ 0) :
    v1 (finv Y) / f1 (finv Y) / u1 (Y - G) = MC := by
  rw [hN]
  rw [hmc] at hlab
  field_simp at hlab ⊢
  linarith

/-- Miao, p. 646: the recursive form of the log-linearised reset price,
`P̂*_t = (1 − βθ)(MĈ_t + P̂_t) + βθP̂*_{t+1}`, from
`P̂*_t = (1 − βθ)Σ_k (θβ)ᵏ(P̂_{t+k} + MĈ_{t+k})`. -/
theorem fs_reset_recursive {β θ : ℝ} {P MC Ps : ℕ → ℝ}
    (hs : ∀ t, Summable fun k => (θ * β) ^ k * (P (t + k) + MC (t + k)))
    (hPs : ∀ t, Ps t = (1 - β * θ) * ∑' k, (θ * β) ^ k * (P (t + k) + MC (t + k))) (t : ℕ) :
    Ps t = (1 - β * θ) * (MC t + P t) + β * θ * Ps (t + 1) := by
  rw [hPs t, hPs (t + 1), (hs t).tsum_eq_zero_add]
  have : ∀ k, (θ * β) ^ (k + 1) * (P (t + (k + 1)) + MC (t + (k + 1))) =
      θ * β * ((θ * β) ^ k * (P (t + 1 + k) + MC (t + 1 + k))) := fun k => by
    rw [show t + (k + 1) = t + 1 + k by ring]
    ring
  simp_rw [this, tsum_mul_left]
  simp only [pow_zero, add_zero, one_mul]
  ring

/-- Miao, p. 646: `q_t = P̂*_t − P̂_t` satisfies
`q_t = (1 − βθ)MĈ_t + βθ(q_{t+1} + P̂_{t+1} − P̂_t)`. -/
theorem fs_q_recursive {β θ : ℝ} {P MC Ps : ℕ → ℝ}
    (hrec : ∀ t, Ps t = (1 - β * θ) * (MC t + P t) + β * θ * Ps (t + 1)) (t : ℕ) :
    Ps t - P t = (1 - β * θ) * MC t + β * θ * ((Ps (t + 1) - P (t + 1)) + P (t + 1) - P t) := by
  rw [hrec t]
  ring

/-- Miao, p. 646: with (19.19) `q_t = θπ_t/(1 − θ)` and `π_{t+1} = P̂_{t+1} − P̂_t`, the
recursion for `q_t` is the New Keynesian Phillips curve
`π_t = βπ_{t+1} + (1 − βθ)(1 − θ)/θ · MĈ_t`. -/
theorem fs_nkpc {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {P MC q infl : ℕ → ℝ}
    (hq : ∀ t, q t = (1 - β * θ) * MC t + β * θ * (q (t + 1) + P (t + 1) - P t))
    (h19 : ∀ t, q t = θ / (1 - θ) * infl t) (hπ : ∀ t, infl (t + 1) = P (t + 1) - P t) (t : ℕ) :
    infl t = β * infl (t + 1) + (1 - β * θ) * (1 - θ) / θ * MC t := by
  have h := hq t
  rw [h19 t, h19 (t + 1), add_sub_assoc, ← hπ t] at h
  have h1 : 1 - θ ≠ 0 := by linarith
  field_simp at h ⊢
  linear_combination h

/-- Miao, p. 646: the log-linearisation of (19.47) `MC = ṽ'(Y)/u'(Y − G)`. Along the direction
`Y = Ȳ(1 + sŶ)`, `G = Ḡ + sȲĜ`, the derivative of `ln MC` at `s = 0` is
`(η_u + η_v)(Ŷ − ΓĜ)`, i.e. `MĈ = (η_u + η_v)(Ŷ − ΓĜ)` to first order. -/
theorem fs_mc_loglin {u1 vt1 : ℝ → ℝ} {Yb Gb u2 vt2 a b : ℝ}
    (hu : HasDerivAt u1 u2 (Yb - Gb)) (hvt : HasDerivAt vt1 vt2 Yb) (hu1 : 0 < u1 (Yb - Gb))
    (hvt1 : 0 < vt1 Yb) (hYb : 0 < Yb)
    (hsum : fs_etaU Yb (u1 (Yb - Gb)) u2 + fs_etaV Yb (vt1 Yb) vt2 ≠ 0) :
    HasDerivAt (fun s => Real.log (vt1 (Yb + s * (Yb * a)) /
        u1 ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))))
      ((fs_etaU Yb (u1 (Yb - Gb)) u2 + fs_etaV Yb (vt1 Yb) vt2) *
        (a - fs_Gamma (fs_etaU Yb (u1 (Yb - Gb)) u2) (fs_etaV Yb (vt1 Yb) vt2) * b)) 0 := by
  have hl1 : HasDerivAt (fun s : ℝ => Yb + s * (Yb * a)) (Yb * a) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (Yb * a)).const_add Yb).congr_deriv (by ring)
  have hl2 : HasDerivAt (fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))
      (Yb * a - Yb * b) 0 :=
    (hl1.sub (((hasDerivAt_id' (0 : ℝ)).mul_const (Yb * b)).const_add Gb)).congr_deriv
      (by ring)
  have hv : HasDerivAt (fun s : ℝ => vt1 (Yb + s * (Yb * a))) (vt2 * (Yb * a)) 0 := by
    have hvt' : HasDerivAt vt1 vt2 (Yb + 0 * (Yb * a)) := by simpa using hvt
    exact hvt'.comp (h := fun s : ℝ => Yb + s * (Yb * a)) 0 hl1
  have hw : HasDerivAt (fun s : ℝ => u1 ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b))))
      (u2 * (Yb * a - Yb * b)) 0 := by
    have hu' : HasDerivAt u1 u2 ((Yb + 0 * (Yb * a)) - (Gb + 0 * (Yb * b))) := by simpa using hu
    exact hu'.comp (h := fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) 0 hl2
  have hq := hv.div hw (by simpa using hu1.ne')
  have hlog := hq.log (by
    simp only [Pi.div_apply, zero_mul, add_zero]
    exact div_ne_zero hvt1.ne' hu1.ne')
  refine hlog.congr_deriv ?_
  simp only [zero_mul, add_zero, Pi.div_apply]
  have hΓ : ∀ A B : ℝ, A + B ≠ 0 → (A + B) * (a - fs_Gamma A B * b) = (A + B) * a - A * b :=
    fun A B h => by
      unfold fs_Gamma
      field_simp
  rw [hΓ _ _ hsum]
  unfold fs_etaU fs_etaV
  field_simp
  ring

/-- Forward solution of `p_t = a p_{t+1} + x_t` with `|a| < 1`: every bounded solution is the
discounted sum `p_t = Σⱼ aʲ x_{t+j}` (Miao, (19.48), p. 646, and (1.8) of Chapter 1). -/
theorem fs_forward_hasSum {a : ℝ} (ha : |a| < 1) {p x : ℕ → ℝ} (hp : fs_Bdd p) (hx : fs_Bdd x)
    (hrec : ∀ t, p t = a * p (t + 1) + x t) (t : ℕ) :
    HasSum (fun j => a ^ j * x (t + j)) (p t) := by
  obtain ⟨B, hB⟩ := hp
  obtain ⟨Bx, hBx⟩ := hx
  have hpart : ∀ n, ∑ j ∈ Finset.range n, a ^ j * x (t + j) = p t - a ^ n * p (t + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hrec (t + n), show t + (n + 1) = t + n + 1 by ring]
      ring
  have haa : |(|a|)| < 1 := by rwa [abs_abs]
  have hsum : Summable (fun j => a ^ j * x (t + j)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one haa).mul_right Bx) ?_
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hBx _) (by positivity)
  rw [hsum.hasSum_iff_tendsto_nat]
  have hz : Tendsto (fun n => a ^ n * p (t + n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n => |a| ^ n * B) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const B
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
  have := (tendsto_const_nhds (x := p t)).sub hz
  simp only [sub_zero] at this
  refine this.congr (fun n => ?_)
  rw [hpart]

/-- The discounted sum `p_t = Σⱼ aʲ x_{t+j}` (`|a| < 1`, `x` bounded) is a bounded solution of
`p_t = a p_{t+1} + x_t` (Miao, (19.48), p. 646). -/
theorem fs_forward_exists {a : ℝ} (ha : |a| < 1) {x : ℕ → ℝ} (hx : fs_Bdd x) :
    fs_Bdd (fun t => ∑' j, a ^ j * x (t + j)) ∧
      ∀ t, ∑' j, a ^ j * x (t + j) = a * ∑' j, a ^ j * x (t + 1 + j) + x t := by
  obtain ⟨Bx, hBx⟩ := hx
  have haa : |(|a|)| < 1 := by rwa [abs_abs]
  have hbd : ∀ t j, ‖a ^ j * x (t + j)‖ ≤ |a| ^ j * Bx := fun t j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hBx _) (by positivity)
  have hsum : ∀ t, Summable (fun j => a ^ j * x (t + j)) := fun t =>
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one haa).mul_right Bx) (hbd t)
  refine ⟨⟨(1 - |a|)⁻¹ * Bx, fun t => ?_⟩, fun t => ?_⟩
  · have := tsum_of_norm_bounded ((hasSum_geometric_of_abs_lt_one haa).mul_right Bx) (hbd t)
    rwa [Real.norm_eq_abs] at this
  · rw [(hsum t).tsum_eq_zero_add]
    have : ∀ j, a ^ (j + 1) * x (t + (j + 1)) = a * (a ^ j * x (t + 1 + j)) := fun j => by
      rw [show t + (j + 1) = t + 1 + j by ring]
      ring
    simp_rw [this, tsum_mul_left]
    simp only [pow_zero, add_zero, one_mul]
    ring

/-- Miao, p. 646: `κ = (1 − βθ)(1 − θ)(η_u + η_v)/θ > 0`. -/
theorem fs_kappa_pos {β θ ηu ηv : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hu : 0 < ηu) (hv : 0 < ηv) : 0 < (1 - β * θ) * (1 - θ) * (ηu + ηv) / θ := by
  have : β * θ < 1 := by nlinarith
  apply div_pos _ hθ0
  apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)

/-- Miao, (19.48), p. 646: combining the Phillips curve
`π_t = βπ_{t+1} + (1 − βθ)(1 − θ)/θ · MĈ_t` with `MĈ_t = (η_u + η_v)(Ŷ_t − ΓĜ_t)`, every bounded
inflation path satisfies `π_t = κΣⱼ βʲ(Ŷ_{t+j} − ΓĜ_{t+j})` with
`κ = (1 − βθ)(1 − θ)(η_u + η_v)/θ`; conversely this sum is a bounded solution. -/
theorem eq_19_48 {β θ ηu ηv : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {infl Y G MC : ℕ → ℝ}
    (hY : fs_Bdd Y) (hG : fs_Bdd G)
    (hmc : ∀ t, MC t = (ηu + ηv) * (Y t - fs_Gamma ηu ηv * G t)) :
    ((fs_Bdd infl ∧ ∀ t, infl t = β * infl (t + 1) + (1 - β * θ) * (1 - θ) / θ * MC t) ↔
      ∀ t, infl t = (1 - β * θ) * (1 - θ) * (ηu + ηv) / θ *
        ∑' j, β ^ j * (Y (t + j) - fs_Gamma ηu ηv * G (t + j))) := by
  set κ := (1 - β * θ) * (1 - θ) * (ηu + ηv) / θ
  set Γ := fs_Gamma ηu ηv
  have hβa : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  obtain ⟨BY, hBY⟩ := hY
  obtain ⟨BG, hBG⟩ := hG
  have hx : fs_Bdd (fun t => κ * (Y t - Γ * G t)) := by
    refine ⟨|κ| * (BY + |Γ| * BG), fun t => ?_⟩
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc |Y t - Γ * G t| ≤ |Y t| + |Γ * G t| := abs_sub _ _
      _ ≤ BY + |Γ| * BG := by
        rw [abs_mul]
        exact add_le_add (hBY t) (mul_le_mul_of_nonneg_left (hBG t) (abs_nonneg _))
  have hkx : ∀ t, (1 - β * θ) * (1 - θ) / θ * MC t = κ * (Y t - Γ * G t) := fun t => by
    rw [hmc t]
    ring
  have hfac : ∀ t, ∑' j, β ^ j * (κ * (Y (t + j) - Γ * G (t + j))) =
      κ * ∑' j, β ^ j * (Y (t + j) - Γ * G (t + j)) := fun t => by
    rw [← tsum_mul_left]
    congr 1
    funext j
    ring
  constructor
  · rintro ⟨hπ, hrec⟩ t
    have h := (fs_forward_hasSum hβa hπ hx (fun t => by rw [hrec t, hkx t]) t).tsum_eq
    rw [← h, hfac]
  · intro h
    obtain ⟨hb, hr⟩ := fs_forward_exists hβa hx
    have hπeq : infl = fun t => ∑' j, β ^ j * (κ * (Y (t + j) - Γ * G (t + j))) := by
      funext t
      rw [h t, hfac]
    rw [hπeq]
    refine ⟨hb, fun t => ?_⟩
    beta_reduce
    rw [hkx t, hr t]

/-- Miao, p. 646: the log-linearisation of marginal utility in the Euler equation (19.44). Along
`C = C̄ + sȲ(Ŷ − Ĝ)` the derivative of `ln u'(C)` at `s = 0` is `−η_u(Ŷ − Ĝ)`. -/
theorem fs_euler_loglin {u1 : ℝ → ℝ} {Cb Yb u2 a b : ℝ} (hu : HasDerivAt u1 u2 Cb)
    (hu1 : 0 < u1 Cb) (hYb : 0 < Yb) :
    HasDerivAt (fun s => Real.log (u1 (Cb + s * (Yb * (a - b)))))
      (-fs_etaU Yb (u1 Cb) u2 * (a - b)) 0 := by
  have hl : HasDerivAt (fun s : ℝ => Cb + s * (Yb * (a - b))) (Yb * (a - b)) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).mul_const (Yb * (a - b))).const_add Cb).congr_deriv (by ring)
  have hu' : HasDerivAt u1 u2 (Cb + 0 * (Yb * (a - b))) := by simpa using hu
  have h := (hu'.comp (h := fun s : ℝ => Cb + s * (Yb * (a - b))) 0 hl).log
    (by simpa using hu1.ne')
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, zero_mul, add_zero]
  unfold fs_etaU
  field_simp

/-- Miao, (19.50), p. 646: with the log-linear marginal utility `ln u'(C_t) = ln u'(C̄) − η_u x_t`
(`x_t = Ŷ_t − Ĝ_t`, `fs_euler_loglin`), the Euler equation (19.44) in logs,
`ln u'(C_t) − ln u'(C_{t+1}) = r_t + ln β` with `r_t = i_t − π_{t+1}` and `r̄ = −ln β`, gives
`x_t = x_{t+1} − σ(i_t − π_{t+1} − r̄)` with `σ = 1/η_u`. -/
theorem eq_19_50 {ηu L x0 x1 l0 l1 i π1 β : ℝ} (hηu : ηu ≠ 0) (h0 : l0 = L - ηu * x0)
    (h1 : l1 = L - ηu * x1) (heul : l0 - l1 = (i - π1) + Real.log β) :
    x0 = x1 - 1 / ηu * (i - π1 - -Real.log β) := by
  rw [h0, h1] at heul
  field_simp
  linear_combination -heul

/-- `ψ = σ(φ_y + κ(φ_π − ρ)/(1 − βρ))` (Miao, p. 647). -/
noncomputable def fs_psi (σ φy κ φπ β ρ : ℝ) : ℝ := σ * (φy + κ / (1 - β * ρ) * (φπ - ρ))

/-- The Taylor-rule multiplier `γ_y = (1 − ρ + (ψ − σφ_y)Γ)/(1 − ρ + ψ)` (Miao, (19.52), p. 647). -/
noncomputable def fs_gammaY (σ φy κ φπ β ρ Γ : ℝ) : ℝ :=
  (1 - ρ + (fs_psi σ φy κ φπ β ρ - σ * φy) * Γ) / (1 - ρ + fs_psi σ φy κ φπ β ρ)

/-- Miao, p. 647: `ψ > 0` (for `σ, κ > 0`, `φ_y ≥ 0`, `0 < β < 1`, `ρ < 1 < φ_π`), and
`ψ − σφ_y > 0`. -/
theorem fs_psi_pos {σ φy κ φπ β ρ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) :
    0 < fs_psi σ φy κ φπ β ρ - σ * φy ∧ 0 < fs_psi σ φy κ φπ β ρ := by
  have hD : 0 < 1 - β * ρ := by nlinarith
  have h1 : 0 < κ / (1 - β * ρ) * (φπ - ρ) := mul_pos (div_pos hκ hD) (by linarith)
  unfold fs_psi
  constructor
  · nlinarith
  · positivity

/-- Miao, p. 647: `γ_y > 0` (for `0 ≤ Γ`). -/
theorem fs_gammaY_pos {σ φy κ φπ β ρ Γ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) (hΓ : 0 ≤ Γ) :
    0 < fs_gammaY σ φy κ φπ β ρ Γ := by
  obtain ⟨h1, h2⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  unfold fs_gammaY
  apply div_pos _ (by linarith)
  nlinarith [mul_nonneg h1.le hΓ]

/-- Miao, p. 647: "One can check that `γ_y < 1`" (for `Γ < 1`): the multiplier under the Taylor
rule is smaller than under the constant-real-rate policy. -/
theorem fs_gammaY_lt_one {σ φy κ φπ β ρ Γ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) (hΓ : Γ < 1) :
    fs_gammaY σ φy κ φπ β ρ Γ < 1 := by
  obtain ⟨h1, h2⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  unfold fs_gammaY
  rw [div_lt_one (by linarith)]
  nlinarith [mul_pos h1 (sub_pos.2 hΓ), mul_nonneg hσ.le hφy]

/-- Miao, p. 647: the Taylor-rule multiplier is smaller than the neoclassical multiplier `Γ`
iff `φ_y > (1 − ρ)(1 − Γ)/(σΓ)`, i.e. for any large enough `φ_y`. -/
theorem fs_gammaY_lt_Gamma_iff {σ φy κ φπ β ρ Γ : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφπ : 1 < φπ) (hΓ : 0 < Γ) :
    fs_gammaY σ φy κ φπ β ρ Γ < Γ ↔ (1 - ρ) * (1 - Γ) / (σ * Γ) < φy := by
  obtain ⟨h1, h2⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  unfold fs_gammaY
  rw [div_lt_iff₀ (by linarith), div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- The Taylor-rule equilibrium conditions (19.48)–(19.50) (Miao, pp. 646–647):
`π_t = κΣⱼβʲ(Ŷ_{t+j} − ΓĜ_{t+j})`, `i_t = r̄ + φ_ππ_t + φ_yŶ_t` and
`Ŷ_t − Ĝ_t = Ŷ_{t+1} − Ĝ_{t+1} − σ(i_t − π_{t+1} − r̄)`. -/
def fs_TaylorEqm (κ β σ Γ φπ φy rb : ℝ) (Y infl i G : ℕ → ℝ) : Prop :=
  ∀ t, infl t = κ * ∑' j, β ^ j * (Y (t + j) - Γ * G (t + j)) ∧
    i t = rb + φπ * infl t + φy * Y t ∧
    Y t - G t = Y (t + 1) - G (t + 1) - σ * (i t - infl (t + 1) - rb)

/-- Miao, (19.51)–(19.52), p. 647: with `Ĝ_t = ρᵗĜ₀`, `Ĝ₀ ≠ 0`, the conjecture
`Ŷ_t = γ_yĜ_t`, `π_t = γ_πĜ_t`, `i_t = r̄ + γ_iĜ_t` is an equilibrium iff
`γ_y = (1 − ρ + (ψ − σφ_y)Γ)/(1 − ρ + ψ)` (19.52), `γ_π = κ(γ_y − Γ)/(1 − βρ)` and
`γ_i = φ_πγ_π + φ_yγ_y`. -/
theorem eq_19_52 {κ β σ Γ φπ φy rb ρ G0 γy γπ γi : ℝ} (hσ : 0 < σ) (hφy : 0 ≤ φy)
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hφπ : 1 < φπ)
    (hG0 : G0 ≠ 0) :
    fs_TaylorEqm κ β σ Γ φπ φy rb (fun t => γy * (ρ ^ t * G0)) (fun t => γπ * (ρ ^ t * G0))
        (fun t => rb + γi * (ρ ^ t * G0)) (fun t => ρ ^ t * G0) ↔
      γy = fs_gammaY σ φy κ φπ β ρ Γ ∧ γπ = κ * (γy - Γ) / (1 - β * ρ) ∧
        γi = φπ * γπ + φy * γy := by
  have hD : 0 < 1 - β * ρ := by nlinarith
  have hβρ0 : 0 ≤ β * ρ := by positivity
  have hβρ1 : β * ρ < 1 := by nlinarith
  obtain ⟨-, hψ⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hρ1 hφπ
  have hsum : ∀ t, ∑' j, β ^ j * (γy * (ρ ^ (t + j) * G0) - Γ * (ρ ^ (t + j) * G0)) =
      (γy - Γ) * (ρ ^ t * G0) / (1 - β * ρ) := fun t => by
    have : ∀ j, β ^ j * (γy * (ρ ^ (t + j) * G0) - Γ * (ρ ^ (t + j) * G0)) =
        (γy - Γ) * (ρ ^ t * G0) * (β * ρ) ^ j := fun j => by
      rw [pow_add, mul_pow]
      ring
    simp_rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβρ0 hβρ1]
    field_simp
  unfold fs_TaylorEqm
  simp_rw [hsum]
  have hψd : 0 < 1 - ρ + fs_psi σ φy κ φπ β ρ := by linarith
  have hc : κ * (γy - Γ) / (1 - β * ρ) = κ / (1 - β * ρ) * (γy - Γ) := by ring
  rw [hc]
  constructor
  · intro h
    obtain ⟨e1, e2, e3⟩ := h 0
    simp only [pow_zero, one_mul, zero_add, pow_one] at e1 e2 e3
    have hγπ : γπ = κ / (1 - β * ρ) * (γy - Γ) := by
      apply mul_right_cancel₀ hG0
      rw [e1]
      ring
    have hγi : γi = φπ * γπ + φy * γy := by
      apply mul_right_cancel₀ hG0
      linear_combination e2
    have key : (1 - ρ) * (γy - 1) = -σ * (γi - ρ * γπ) := by
      apply mul_right_cancel₀ hG0
      linear_combination e3
    refine ⟨?_, hγπ, hγi⟩
    rw [hγi, hγπ] at key
    unfold fs_gammaY
    rw [eq_div_iff hψd.ne']
    unfold fs_psi
    linear_combination key
  · rintro ⟨hγy, hγπ, hγi⟩ t
    have hγ' : γy * (1 - ρ + fs_psi σ φy κ φπ β ρ) =
        1 - ρ + (fs_psi σ φy κ φπ β ρ - σ * φy) * Γ := by
      rw [hγy]
      unfold fs_gammaY
      field_simp
    have key : (1 - ρ) * (γy - 1) = -σ * (γi - ρ * γπ) := by
      rw [hγi, hγπ]
      unfold fs_psi at hγ'
      linear_combination hγ'
    refine ⟨?_, ?_, ?_⟩
    · rw [hγπ]
      ring
    · rw [hγi]
      ring
    · rw [pow_succ]
      linear_combination (ρ ^ t * G0) * key

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Fiscal stimulus at the zero lower bound

Miao, §19.3, pp. 648–654, (19.53)–(19.60), and Exercise 19.3 (p. 669), following Eggertsson
(2009) and Woodford (2011).

The two-state setting: the crisis state `L` (with `r^net_t = r_L`, `Ĝ_t = Ĝ_L`) persists each
period with probability `μ`; the normal state is absorbing, with `π = Ŷ = Ĝ = 0` and `i = r̄`.
For a variable equal to `x_L` in the crisis and `0` in the normal state, the expectation in the
crisis is `E_t x_{t+1} = μx_L`, and `E_t x_{t+j} = μʲx_L`. A path in the crisis state is a
sequence `(Ŷ_t, π_t)` of crisis values (the only history in which the crisis lasts until `t`).

* (19.53): it reduces to (19.50) when `Δ_t = 0` (`eq_19_53`); with `r^net < 0` the zero bound
  rules out the zero-inflation steady state (`fs_zlb_no_steady_state`).
* (19.55): `h(μ) = (1 − μ)(1 − βμ) − κσμ` is strictly decreasing on `[0, 1]`, `h(0) = 1`,
  `h(1) = −κσ`; there is a unique `μ̄ ∈ (0, 1)` with `h(μ̄) = 0`, and (19.55) holds on `[0, 1]` iff
  `μ < μ̄` (`fs_h_strictAntiOn`, `fs_mubar_exists`, `eq_19_55_iff`). The book's "for all
  `0 ≤ μ ≤ μ̄`" must exclude `μ̄` (`eq_19_55_fails_at_mubar`).
* **Exercise 19.3** (`ex_19_3`): with `i_t = 0`, the crisis system obtained from (19.48) and
  (19.53) has a unique bounded solution for every `(r_L, Ĝ_L)` iff (19.55); the solution is then
  the constant one of (19.56) and (19.60) (`ex_19_3_solution`). The recursive form of (19.48)
  is equivalent to the summed one for bounded paths (`fs_zlb_sum_form`). The proof uses the
  jump-only `2 × 2` Blanchard–Kahn results of Chapter 2 (`nk_jump2_unique`,
  `nk_jump2_nonunique`) with the trivial conditional expectation `fs_trivE`.
* (19.56)–(19.60): `eq_19_56`, `eq_19_57`, `eq_19_58` (an equivalence), `eq_19_60`; `ϑ_r > 0`,
  `ϑ_G > 1` for `μ > 0` (`eq_19_59`), and `ϑ_G = 1` at `μ = 0` (`fs_thetaG_zero`).
* The branches of (19.54): for every `Ĝ_L` there is exactly one constant crisis equilibrium, and
  `i_L = 0` iff `Ĝ_L ≤ Ĝ_c` (`eq_19_54_branches`; the book says `Ĝ_L < Ĝ_c`, but at `Ĝ_c` both
  branches give `i_L = 0`). `Ĝ_c > 0` iff `r_L` is negative enough (`fs_Gc_pos_iff`; the book
  prints `Ĝ_c > 0` as if unconditional). Above `Ĝ_c`, the solution "left as an exercise":
  `Ŷ_L = γ_yĜ_L + σ(r_L − r̄)/(1 − μ + ψ)` with `γ_y` of (19.52) at `ρ = μ` (`fs_taylor_branch`).
* Figure 19.4: `Ĝ_c ∈ (0.135, 0.137)` at the book's parameters (`fs_fig_19_4_Gc`).
* Figure 19.5: `ϑ_G` and `ϑ_r` are strictly increasing in `μ` on `[0, μ̄)` and tend to `+∞` as
  `μ ↑ μ̄` (`fs_thetaG_strictMonoOn`, `fs_thetaR_strictMonoOn`, `fs_thetaG_tendsto_atTop`,
  `fs_thetaR_tendsto_atTop`).
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- Miao, (19.53), p. 648: with `r^net_t = −ln β − Δ_t`, (19.53) is (19.50) when `Δ_t = 0`. -/
theorem eq_19_53 {β σ Yt Gt Y1 G1 it π1 Δ : ℝ} (hΔ : Δ = 0) :
    (Yt - Gt = Y1 - G1 - σ * (it - π1 - (-Real.log β - Δ))) ↔
      (Yt - Gt = Y1 - G1 - σ * (it - π1 - (-Real.log β))) := by
  rw [hΔ, sub_zero]

/-- Miao, p. 648: if `r^net < 0` the zero lower bound `i ≥ 0` is incompatible with the
zero-inflation steady state `Ŷ = π = Ĝ = 0` in (19.53) (`σ > 0`). -/
theorem fs_zlb_no_steady_state {σ i rnet : ℝ} (hσ : 0 < σ) (hr : rnet < 0) (hi : 0 ≤ i) :
    ¬ ((0 : ℝ) - 0 = 0 - 0 - σ * (i - 0 - rnet)) := by
  intro h
  have : σ * (i - rnet) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

/-- `h(μ) = (1 − μ)(1 − βμ) − κσμ`, positive iff (19.55) (Miao, p. 650). -/
def fs_h (β κ σ μ : ℝ) : ℝ := (1 - μ) * (1 - β * μ) - κ * σ * μ

/-- `ϑ_r = σ(1 − βμ)/h(μ)` (Miao, (19.59), p. 650). -/
noncomputable def fs_thetaR (β κ σ μ : ℝ) : ℝ := σ * (1 - β * μ) / fs_h β κ σ μ

/-- `ϑ_G = ((1 − μ)(1 − βμ) − κσμΓ)/h(μ)` (Miao, (19.59), p. 650). -/
noncomputable def fs_thetaG (β κ σ μ Γ : ℝ) : ℝ :=
  ((1 - μ) * (1 - β * μ) - κ * σ * μ * Γ) / fs_h β κ σ μ

/-- Miao, p. 650: `h` is strictly decreasing on `[0, 1]` (for `0 < β < 1`, `κσ > 0`). -/
theorem fs_h_strictAntiOn {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ) :
    StrictAntiOn (fs_h β κ σ) (Set.Icc 0 1) := by
  intro a ha b hb hab
  unfold fs_h
  have : 0 < 1 + β + κ * σ - β * (a + b) := by nlinarith [ha.1, hb.2]
  nlinarith [mul_pos (sub_pos.2 hab) this]

/-- Miao, p. 650: there is a unique `μ̄ ∈ (0, 1)` with `h(μ̄) = 0`. -/
theorem fs_mubar_exists {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ) :
    ∃! μb, μb ∈ Set.Ioo (0 : ℝ) 1 ∧ fs_h β κ σ μb = 0 := by
  have hcont : ContinuousOn (fs_h β κ σ) (Set.Icc 0 1) := by
    unfold fs_h
    fun_prop
  have h0 : fs_h β κ σ 0 = 1 := by simp [fs_h]
  have h1 : fs_h β κ σ 1 = -(κ * σ) := by simp [fs_h]
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont
    (show (0 : ℝ) ∈ Set.Icc (fs_h β κ σ 1) (fs_h β κ σ 0) by
      rw [h0, h1]
      constructor <;> linarith)
  have hc0' : c ≠ 0 := by
    rintro rfl
    rw [h0] at hc0
    norm_num at hc0
  have hc1' : c ≠ 1 := by
    rintro rfl
    rw [h1] at hc0
    linarith
  refine ⟨c, ⟨⟨lt_of_le_of_ne hc.1 (Ne.symm hc0'), lt_of_le_of_ne hc.2 hc1'⟩, hc0⟩, ?_⟩
  rintro d ⟨hd, hd0⟩
  exact (fs_h_strictAntiOn hβ0 hβ1 hκσ).injOn ⟨hd.1.le, hd.2.le⟩ hc (hd0.trans hc0.symm)

/-- Miao, p. 650: for `μ ∈ [0, 1]`, condition (19.55) `κσμ < (1 − μ)(1 − βμ)` holds iff
`μ < μ̄`. -/
theorem eq_19_55_iff {β κ σ μb μ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ)
    (hμb : μb ∈ Set.Ioo (0 : ℝ) 1) (hμb0 : fs_h β κ σ μb = 0) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    κ * σ * μ < (1 - μ) * (1 - β * μ) ↔ μ < μb := by
  have hanti := fs_h_strictAntiOn hβ0 hβ1 hκσ
  have hμb' : μb ∈ Set.Icc (0 : ℝ) 1 := ⟨hμb.1.le, hμb.2.le⟩
  have e : κ * σ * μ < (1 - μ) * (1 - β * μ) ↔ 0 < fs_h β κ σ μ := by
    unfold fs_h
    constructor <;> intro h <;> linarith
  rw [e, ← hμb0]
  exact hanti.lt_iff_gt hμb' hμ

/-- **Correction** (Miao, p. 650): (19.55) fails at `μ = μ̄`, so it holds for `0 ≤ μ < μ̄`, not
for all `0 ≤ μ ≤ μ̄`. -/
theorem eq_19_55_fails_at_mubar {β κ σ μb : ℝ} (hμb0 : fs_h β κ σ μb = 0) :
    ¬ κ * σ * μb < (1 - μb) * (1 - β * μb) := by
  unfold fs_h at hμb0
  intro h
  linarith

/-- Miao, (19.56), p. 650: in the crisis state (19.48) reads
`π_L = κΣⱼβʲ E(Ŷ_{t+j} − ΓĜ_{t+j})` with `E(x_{t+j}) = μʲx_L + (1 − μʲ)·0`, i.e.
`π_L = κ(Ŷ_L − ΓĜ_L)/(1 − βμ)`. -/
theorem eq_19_56 {β κ μ Γ YL gL πL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1)
    (h : πL = κ * ∑' j : ℕ, β ^ j * (μ ^ j * (YL - Γ * gL) + (1 - μ ^ j) * (0 - Γ * 0))) :
    πL = κ / (1 - β * μ) * (YL - Γ * gL) := by
  have hβμ0 : 0 ≤ β * μ := by positivity
  have hβμ1 : β * μ < 1 := by nlinarith
  have : ∀ j : ℕ, β ^ j * (μ ^ j * (YL - Γ * gL) + (1 - μ ^ j) * (0 - Γ * 0)) =
      (YL - Γ * gL) * (β * μ) ^ j := fun j => by
    rw [mul_pow]
    ring
  simp_rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβμ0 hβμ1] at h
  rw [h]
  ring

/-- Miao, (19.57), p. 650: in the crisis state (19.53) reads
`Ŷ_L − Ĝ_L = μ(Ŷ_L − Ĝ_L) + (1 − μ)(0 − 0) − σ(i_L − (μπ_L + (1 − μ)·0) − r_L)`, i.e.
`(1 − μ)(Ŷ_L − Ĝ_L) = σ(−i_L + μπ_L + r_L)`. -/
theorem eq_19_57 {μ σ YL gL iL πL rL : ℝ} :
    YL - gL = μ * (YL - gL) + (1 - μ) * (0 - 0) - σ * (iL - (μ * πL + (1 - μ) * 0) - rL) ↔
      (1 - μ) * (YL - gL) = σ * (-iL + μ * πL + rL) := by
  constructor <;> intro h <;> linarith

/-- Miao, (19.58), p. 650: when `h(μ) ≠ 0` and `βμ ≠ 1`, (19.56) and (19.57) hold iff
`Ŷ_L = ϑ_r(r_L − i_L) + ϑ_GĜ_L` and `π_L = κ(Ŷ_L − ΓĜ_L)/(1 − βμ)`. -/
theorem eq_19_58 {β κ σ μ Γ YL gL iL πL rL : ℝ} (hh : fs_h β κ σ μ ≠ 0)
    (hD : 1 - β * μ ≠ 0) :
    (πL = κ / (1 - β * μ) * (YL - Γ * gL) ∧ (1 - μ) * (YL - gL) = σ * (-iL + μ * πL + rL)) ↔
      (YL = fs_thetaR β κ σ μ * (rL - iL) + fs_thetaG β κ σ μ Γ * gL ∧
        πL = κ / (1 - β * μ) * (YL - Γ * gL)) := by
  have hc : κ / (1 - β * μ) * (1 - β * μ) = κ := div_mul_cancel₀ κ hD
  have e : ∀ Y, (Y = fs_thetaR β κ σ μ * (rL - iL) + fs_thetaG β κ σ μ Γ * gL ↔
      Y * fs_h β κ σ μ = σ * (1 - β * μ) * (rL - iL) +
        ((1 - μ) * (1 - β * μ) - κ * σ * μ * Γ) * gL) := by
    intro Y
    unfold fs_thetaR fs_thetaG
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hh]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(e YL).2 ?_, h1⟩
    rw [h1] at h2
    unfold fs_h
    linear_combination (1 - β * μ) * h2 + σ * μ * (YL - Γ * gL) * hc
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have k := (e YL).1 h1
    rw [h2]
    apply mul_left_cancel₀ hD
    unfold fs_h at k
    linear_combination k - σ * μ * (YL - Γ * gL) * hc

/-- Miao, (19.59), p. 650: under (19.55), `ϑ_r > 0`, and `ϑ_G > 1` when `μ > 0` and `Γ < 1`. -/
theorem eq_19_59 {β κ σ μ Γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hΓ : Γ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    0 < fs_thetaR β κ σ μ ∧ 1 < fs_thetaG β κ σ μ Γ := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  refine ⟨div_pos (mul_pos hσ hD) hh, ?_⟩
  unfold fs_thetaG
  rw [one_lt_div hh]
  unfold fs_h
  nlinarith [mul_pos (mul_pos (mul_pos hκ hσ) hμ0) (sub_pos.2 hΓ)]

/-- Miao, p. 652: with `μ = 0` the multiplier `ϑ_G` is one. -/
theorem fs_thetaG_zero {β κ σ Γ : ℝ} : fs_thetaG β κ σ 0 Γ = 1 := by
  simp [fs_thetaG, fs_h]

/-- Miao, (19.60), p. 650: at the zero bound (`i_L = 0`), `Ŷ_L = ϑ_r r_L + ϑ_GĜ_L`. -/
theorem eq_19_60 {β κ σ μ Γ YL gL πL rL : ℝ} (hh : fs_h β κ σ μ ≠ 0) (hD : 1 - β * μ ≠ 0)
    (h56 : πL = κ / (1 - β * μ) * (YL - Γ * gL))
    (h57 : (1 - μ) * (YL - gL) = σ * (-0 + μ * πL + rL)) :
    YL = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL := by
  have := ((eq_19_58 hh hD).1 ⟨h56, h57⟩).1
  rw [this, sub_zero]

/-- The critical level `Ĝ_c` (Miao, p. 650). -/
noncomputable def fs_Gc (β κ σ μ Γ φπ φy rL rb : ℝ) : ℝ :=
  (-(κ * φπ / (1 - β * μ) + φy) * fs_thetaR β κ σ μ * rL - rb) /
    (κ * φπ / (1 - β * μ) * (fs_thetaG β κ σ μ Γ - Γ) + φy * fs_thetaG β κ σ μ Γ)

/-- The two branches of (19.54) (Miao, pp. 649–651). Under (19.55) (with `0 ≤ μ < 1`,
`Γ < 1`, `φ_π > 0`, `φ_y ≥ 0`), for every `Ĝ_L` there is exactly one constant crisis
equilibrium `(i_L, Ŷ_L, π_L)` of (19.56), (19.57) and `i_L = max(r̄ + φ_ππ_L + φ_yŶ_L, 0)`; and
the zero bound binds, `i_L = 0`, iff `Ĝ_L ≤ Ĝ_c`. -/
theorem eq_19_54_branches {β κ σ μ Γ φπ φy rL rb gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hΓ : Γ < 1)
    (hφπ : 0 < φπ) (hφy : 0 ≤ φy) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    (∃! x : ℝ × ℝ × ℝ, x.2.2 = κ / (1 - β * μ) * (x.2.1 - Γ * gL) ∧
        (1 - μ) * (x.2.1 - gL) = σ * (-x.1 + μ * x.2.2 + rL) ∧
        x.1 = max (rb + φπ * x.2.2 + φy * x.2.1) 0) ∧
      ∀ x : ℝ × ℝ × ℝ, x.2.2 = κ / (1 - β * μ) * (x.2.1 - Γ * gL) →
        (1 - μ) * (x.2.1 - gL) = σ * (-x.1 + μ * x.2.2 + rL) →
        x.1 = max (rb + φπ * x.2.2 + φy * x.2.1) 0 →
        (x.1 = 0 ↔ gL ≤ fs_Gc β κ σ μ Γ φπ φy rL rb) := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  set tr := fs_thetaR β κ σ μ
  set tg := fs_thetaG β κ σ μ Γ
  have htr : 0 < tr := div_pos (mul_pos hσ hD) hh
  have htg : 1 ≤ tg := by
    unfold tg fs_thetaG
    rw [one_le_div hh]
    unfold fs_h
    nlinarith [mul_nonneg (mul_nonneg (mul_pos hκ hσ).le hμ0) (sub_pos.2 hΓ).le]
  set b := κ * φπ / (1 - β * μ)
  have hb : 0 < b := div_pos (mul_pos hκ hφπ) hD
  set a := b + φy
  have ha : 0 < a := by positivity
  set Dc := b * (tg - Γ) + φy * tg
  have hDc : 0 < Dc := by nlinarith [mul_nonneg hφy (by linarith : (0 : ℝ) ≤ tg)]
  -- the Taylor value as a function of `i`, given (19.56)–(19.58)
  set sh := rb + a * tr * rL + Dc * gL
  have hred : ∀ x : ℝ × ℝ × ℝ, x.2.2 = κ / (1 - β * μ) * (x.2.1 - Γ * gL) →
      (1 - μ) * (x.2.1 - gL) = σ * (-x.1 + μ * x.2.2 + rL) →
      x.2.1 = tr * (rL - x.1) + tg * gL ∧
        rb + φπ * x.2.2 + φy * x.2.1 = sh - a * tr * x.1 := by
    intro x h1 h2
    have hY := ((eq_19_58 hh.ne' hD.ne').1 ⟨h1, h2⟩).1
    refine ⟨hY, ?_⟩
    rw [h1, hY]
    unfold sh Dc a b
    field_simp
    ring
  have hGc : gL ≤ fs_Gc β κ σ μ Γ φπ φy rL rb ↔ sh ≤ 0 := by
    unfold fs_Gc
    change gL ≤ (-(b + φy) * tr * rL - rb) / Dc ↔ sh ≤ 0
    rw [le_div_iff₀ hDc]
    unfold sh
    constructor <;> intro h <;> nlinarith
  -- the candidate
  set i0 := max (sh / (1 + a * tr)) 0
  have hden : 0 < 1 + a * tr := by positivity
  have hi0 : i0 = max (sh - a * tr * i0) 0 := by
    unfold i0
    rcases le_or_gt sh 0 with hs | hs
    · have : sh / (1 + a * tr) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs hden.le
      rw [max_eq_right this]
      simp [hs]
    · have hpos : 0 < sh / (1 + a * tr) := div_pos hs hden
      rw [max_eq_left hpos.le]
      have : sh - a * tr * (sh / (1 + a * tr)) = sh / (1 + a * tr) := by
        field_simp
        ring
      rw [this, max_eq_left hpos.le]
  have huniq_i : ∀ i, i = max (sh - a * tr * i) 0 → i = i0 := by
    intro i hi
    have hi0' := hi0
    rcases le_or_gt sh 0 with hs | hs
    · have hin : 0 ≤ i := hi ▸ le_max_right _ _
      have : sh - a * tr * i ≤ 0 := by nlinarith [mul_nonneg (mul_pos ha htr).le hin]
      rw [max_eq_right this] at hi
      have : sh - a * tr * i0 ≤ 0 := by
        have hin0 : 0 ≤ i0 := le_max_right _ _
        nlinarith [mul_nonneg (mul_pos ha htr).le hin0]
      rw [max_eq_right this] at hi0'
      rw [hi, hi0']
    · rcases le_or_gt (sh - a * tr * i) 0 with h1 | h1
      · rw [max_eq_right h1] at hi
        rw [hi] at h1
        linarith
      · rw [max_eq_left h1.le] at hi
        unfold i0
        have hpos : 0 < sh / (1 + a * tr) := div_pos hs hden
        rw [max_eq_left hpos.le, eq_div_iff hden.ne']
        linarith
  have hshz : i0 = 0 ↔ sh ≤ 0 := by
    unfold i0
    constructor
    · intro h
      by_contra hs
      push Not at hs
      have hpos : 0 < sh / (1 + a * tr) := div_pos hs hden
      rw [max_eq_left hpos.le] at h
      linarith
    · intro hs
      exact max_eq_right (div_nonpos_of_nonpos_of_nonneg hs hden.le)
  refine ⟨⟨(i0, tr * (rL - i0) + tg * gL,
      κ / (1 - β * μ) * (tr * (rL - i0) + tg * gL - Γ * gL)), ?_, ?_⟩, ?_⟩
  · have hpair := (eq_19_58 (Γ := Γ) (gL := gL) (rL := rL) (iL := i0)
      (YL := tr * (rL - i0) + tg * gL)
      (πL := κ / (1 - β * μ) * (tr * (rL - i0) + tg * gL - Γ * gL)) hh.ne' hD.ne').2
      ⟨rfl, rfl⟩
    refine ⟨hpair.1, hpair.2, ?_⟩
    have := (hred (i0, tr * (rL - i0) + tg * gL,
      κ / (1 - β * μ) * (tr * (rL - i0) + tg * gL - Γ * gL)) hpair.1 hpair.2).2
    simp only at this ⊢
    rw [this]
    exact hi0
  · rintro ⟨i, Y, p⟩ ⟨h1, h2, h3⟩
    obtain ⟨hY, hT⟩ := hred (i, Y, p) h1 h2
    simp only at hY hT h1 h3 ⊢
    rw [hT] at h3
    have hi := huniq_i i h3
    subst hi
    rw [h1, hY]
  · rintro ⟨i, Y, p⟩ h1 h2 h3
    obtain ⟨-, hT⟩ := hred (i, Y, p) h1 h2
    simp only at hT h3 ⊢
    rw [hT] at h3
    rw [huniq_i i h3, hshz, hGc]

/-- Miao, p. 650: `Ĝ_c > 0` iff `r_L < −r̄/((κφ_π/(1 − βμ) + φ_y)ϑ_r)`: the zero bound binds at
`Ĝ_L = 0` only if the shock `r_L` is negative enough (the book prints `Ĝ_c > 0` as if it held
always). -/
theorem fs_Gc_pos_iff {β κ σ μ Γ φπ φy rL rb : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hΓ : Γ < 1)
    (hφπ : 0 < φπ) (hφy : 0 ≤ φy) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    0 < fs_Gc β κ σ μ Γ φπ φy rL rb ↔
      rL < -rb / ((κ * φπ / (1 - β * μ) + φy) * fs_thetaR β κ σ μ) := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  have htr : 0 < fs_thetaR β κ σ μ := div_pos (mul_pos hσ hD) hh
  have htg : 1 ≤ fs_thetaG β κ σ μ Γ := by
    unfold fs_thetaG
    rw [one_le_div hh]
    unfold fs_h
    nlinarith [mul_nonneg (mul_nonneg (mul_pos hκ hσ).le hμ0) (sub_pos.2 hΓ).le]
  have hb : 0 < κ * φπ / (1 - β * μ) := div_pos (mul_pos hκ hφπ) hD
  have hDc : 0 < κ * φπ / (1 - β * μ) * (fs_thetaG β κ σ μ Γ - Γ) +
      φy * fs_thetaG β κ σ μ Γ := by
    nlinarith [mul_nonneg hφy (by linarith : (0 : ℝ) ≤ fs_thetaG β κ σ μ Γ)]
  have hA : 0 < (κ * φπ / (1 - β * μ) + φy) * fs_thetaR β κ σ μ := by positivity
  unfold fs_Gc
  rw [div_pos_iff_of_pos_right hDc, lt_div_iff₀ hA]
  constructor <;> intro h <;> linarith

/-- Miao, p. 651, the branch "left as an exercise": if the zero bound does not bind,
(19.56), (19.57) and `i_L = r̄ + φ_ππ_L + φ_yŶ_L` give
`Ŷ_L = γ_yĜ_L + σ(r_L − r̄)/(1 − μ + ψ)`, with `γ_y` and `ψ` of (19.52) at `ρ = μ`: the
multiplier above `Ĝ_c` is `γ_y` (p. 652). -/
theorem fs_taylor_branch {β κ σ μ Γ φπ φy rL rb YL gL πL iL : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hμ1 : μ < 1) (hφπ : 1 < φπ) (hφy : 0 ≤ φy)
    (h56 : πL = κ / (1 - β * μ) * (YL - Γ * gL))
    (h57 : (1 - μ) * (YL - gL) = σ * (-iL + μ * πL + rL))
    (hT : iL = rb + φπ * πL + φy * YL) :
    YL = fs_gammaY σ φy κ φπ β μ Γ * gL + σ * (rL - rb) / (1 - μ + fs_psi σ φy κ φπ β μ) := by
  obtain ⟨-, hψ⟩ := fs_psi_pos hσ hφy hκ hβ0 hβ1 hμ1 hφπ
  have hψd : 0 < 1 - μ + fs_psi σ φy κ φπ β μ := by linarith
  have key : YL * (1 - μ + fs_psi σ φy κ φπ β μ) =
      (1 - μ + (fs_psi σ φy κ φπ β μ - σ * φy) * Γ) * gL + σ * (rL - rb) := by
    rw [hT, h56] at h57
    unfold fs_psi
    linear_combination h57
  unfold fs_gammaY
  field_simp
  linear_combination key

/-- Miao, Figure 19.5, p. 653: `ϑ_G` is strictly increasing in `μ` on `[0, μ̄)` (where
`h > 0`), for `Γ < 1`. -/
theorem fs_thetaG_strictMonoOn {β κ σ Γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκσ : 0 < κ * σ)
    (hΓ : Γ < 1) :
    StrictMonoOn (fun μ => fs_thetaG β κ σ μ Γ) {μ | 0 ≤ μ ∧ μ ≤ 1 ∧ 0 < fs_h β κ σ μ} := by
  intro a ⟨ha0, ha1, hha⟩ b ⟨hb0, hb1, hhb⟩ hab
  have hanti := fs_h_strictAntiOn hβ0 hβ1 hκσ ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hab
  have e : ∀ μ, 0 < fs_h β κ σ μ →
      fs_thetaG β κ σ μ Γ = 1 + κ * σ * (1 - Γ) * μ / fs_h β κ σ μ := fun μ hμ => by
    unfold fs_thetaG
    field_simp
    unfold fs_h
    ring
  simp only
  rw [e a hha, e b hhb]
  have hc : 0 < κ * σ * (1 - Γ) := mul_pos hκσ (by linarith)
  rw [add_lt_add_iff_left, div_lt_div_iff₀ hha hhb]
  nlinarith [mul_le_mul_of_nonneg_left hanti.le ha0, mul_lt_mul_of_pos_right hab hha]

/-- Miao, Figure 19.5, p. 653: `ϑ_r` is strictly increasing in `μ` on `[0, μ̄)`. -/
theorem fs_thetaR_strictMonoOn {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) :
    StrictMonoOn (fun μ => fs_thetaR β κ σ μ) {μ | 0 ≤ μ ∧ μ ≤ 1 ∧ 0 < fs_h β κ σ μ} := by
  intro a ⟨ha0, ha1, hha⟩ b ⟨hb0, hb1, hhb⟩ hab
  simp only
  unfold fs_thetaR
  rw [div_lt_div_iff₀ hha hhb]
  have hDa : 0 < 1 - β * a := by nlinarith
  have hDb : 0 < 1 - β * b := by nlinarith
  have e : σ * (1 - β * a) * fs_h β κ σ b - σ * (1 - β * b) * fs_h β κ σ a =
      -σ * (b - a) * ((1 - β * a) * (1 - β * b) + κ * σ) := by
    unfold fs_h
    ring
  have : 0 < σ * (b - a) * ((1 - β * a) * (1 - β * b) + κ * σ) := by
    have := mul_pos hDa hDb
    have := mul_pos hκ hσ
    have := sub_pos.2 hab
    positivity
  linarith

/-- Miao, p. 654: the multiplier `ϑ_G` "increases without bound as `μ` approaches `μ̄`". -/
theorem fs_thetaG_tendsto_atTop {β κ σ Γ μb : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκσ : 0 < κ * σ) (hΓ : Γ < 1) (hμb : μb ∈ Set.Ioo (0 : ℝ) 1)
    (hμb0 : fs_h β κ σ μb = 0) :
    Tendsto (fun μ => fs_thetaG β κ σ μ Γ) (𝓝[<] μb) atTop := by
  have hcont : Continuous (fs_h β κ σ) := by unfold fs_h; fun_prop
  have hpos : ∀ᶠ μ in 𝓝[<] μb, 0 < fs_h β κ σ μ := by
    have hI : Set.Ioo (0 : ℝ) μb ∈ 𝓝[<] μb := Ioo_mem_nhdsLT hμb.1
    filter_upwards [hI] with μ hμ
    rw [← hμb0]
    exact fs_h_strictAntiOn hβ0 hβ1 hκσ ⟨hμ.1.le, (hμ.2.trans hμb.2).le⟩
      ⟨hμb.1.le, hμb.2.le⟩ hμ.2
  have hh : Tendsto (fs_h β κ σ) (𝓝[<] μb) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hpos⟩
    have := hcont.tendsto μb
    rw [hμb0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinv := tendsto_inv_nhdsGT_zero.comp hh
  have hnum : Tendsto (fun μ => κ * σ * (1 - Γ) * μ) (𝓝[<] μb) (𝓝 (κ * σ * (1 - Γ) * μb)) :=
    ((continuous_const.mul continuous_id).tendsto μb).mono_left nhdsWithin_le_nhds
  have hc : 0 < κ * σ * (1 - Γ) * μb := mul_pos (mul_pos hκσ (by linarith)) hμb.1
  have hprod := hnum.pos_mul_atTop hc hinv
  have hsum := tendsto_atTop_add_const_left (𝓝[<] μb) 1 hprod
  refine hsum.congr' ?_
  filter_upwards [hpos] with μ hμ
  simp only [Function.comp_apply]
  unfold fs_thetaG
  field_simp
  unfold fs_h
  ring

/-- Miao, p. 654 and Figure 19.5: `ϑ_r = dY_L/dr_L` also tends to `+∞` as `μ ↑ μ̄`. -/
theorem fs_thetaR_tendsto_atTop {β κ σ μb : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hμb : μb ∈ Set.Ioo (0 : ℝ) 1) (hμb0 : fs_h β κ σ μb = 0) :
    Tendsto (fun μ => fs_thetaR β κ σ μ) (𝓝[<] μb) atTop := by
  have hκσ : 0 < κ * σ := mul_pos hκ hσ
  have hcont : Continuous (fs_h β κ σ) := by unfold fs_h; fun_prop
  have hpos : ∀ᶠ μ in 𝓝[<] μb, 0 < fs_h β κ σ μ := by
    have hI : Set.Ioo (0 : ℝ) μb ∈ 𝓝[<] μb := Ioo_mem_nhdsLT hμb.1
    filter_upwards [hI] with μ hμ
    rw [← hμb0]
    exact fs_h_strictAntiOn hβ0 hβ1 hκσ ⟨hμ.1.le, (hμ.2.trans hμb.2).le⟩
      ⟨hμb.1.le, hμb.2.le⟩ hμ.2
  have hh : Tendsto (fs_h β κ σ) (𝓝[<] μb) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hpos⟩
    have := hcont.tendsto μb
    rw [hμb0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinv := tendsto_inv_nhdsGT_zero.comp hh
  have hnum : Tendsto (fun μ => σ * (1 - β * μ)) (𝓝[<] μb) (𝓝 (σ * (1 - β * μb))) := by
    have : Continuous (fun μ : ℝ => σ * (1 - β * μ)) := by fun_prop
    exact (this.tendsto μb).mono_left nhdsWithin_le_nhds
  have hc : 0 < σ * (1 - β * μb) := mul_pos hσ (by nlinarith [hμb.2])
  refine (hnum.pos_mul_atTop hc hinv).congr' ?_
  filter_upwards [hpos] with μ _
  simp only [Function.comp_apply]
  unfold fs_thetaR
  rw [div_eq_mul_inv]

/-- Miao, p. 652 (Figure 19.4): at `β = 0.997` (`r̄ = −ln β`), `κ = 0.00859`, `σ = 0.862`,
`Γ = 0.425`, `φ_π = 1.5`, `φ_y = 0.25`, `r_L = −0.0104`, `μ = 0.903`, the kink is at
`Ĝ_c ∈ (0.135, 0.137)` (the book: `0.136`). -/
theorem fs_fig_19_4_Gc :
    (0.135 : ℝ) < fs_Gc 0.997 0.00859 0.862 0.903 0.425 1.5 0.25 (-0.0104) (-Real.log 0.997) ∧
      fs_Gc 0.997 0.00859 0.862 0.903 0.425 1.5 0.25 (-0.0104) (-Real.log 0.997) < 0.137 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 0.997 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 0.997 by norm_num)
  set r := -Real.log 0.997
  have hr1 : 0.003 ≤ r := by unfold r; norm_num at h1 ⊢; linarith
  have hr2 : r ≤ 0.00301 := by unfold r; norm_num at h2 ⊢; linarith
  unfold fs_Gc fs_thetaR fs_thetaG fs_h
  norm_num
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

/-- The crisis system of Exercise 19.3 with `i_t = 0` (Miao, p. 669): the recursive form of
(19.48), `π_t = κ(Ŷ_t − ΓĜ_L) + βμπ_{t+1}`, and (19.53),
`Ŷ_t − Ĝ_L = μ(Ŷ_{t+1} − Ĝ_L) − σ(0 − μπ_{t+1} − r_L)` (next-period normal-state values are
zero). -/
def fs_zlbSys (β κ σ μ Γ rL gL : ℝ) (Y p : ℕ → ℝ) : Prop :=
  ∀ t, p t = κ * (Y t - Γ * gL) + β * μ * p (t + 1) ∧
    Y t - gL = μ * (Y (t + 1) - gL) - σ * (0 - μ * p (t + 1) - rL)

/-- Miao, (19.48) in the crisis state: for bounded `Ŷ`, a bounded `π` satisfies the recursive
Phillips curve iff `π_t = κΣⱼ(βμ)ʲ(Ŷ_{t+j} − ΓĜ_L)`. -/
theorem fs_zlb_sum_form {β κ μ Γ gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1) {Y p : ℕ → ℝ} (hY : fs_Bdd Y) :
    (fs_Bdd p ∧ ∀ t, p t = κ * (Y t - Γ * gL) + β * μ * p (t + 1)) ↔
      ∀ t, p t = ∑' j, (β * μ) ^ j * (κ * (Y (t + j) - Γ * gL)) := by
  have ha : |β * μ| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  obtain ⟨B, hB⟩ := hY
  have hx : fs_Bdd (fun t => κ * (Y t - Γ * gL)) := by
    refine ⟨|κ| * (B + |Γ * gL|), fun t => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hB t) le_rfl))
      (abs_nonneg _)
  constructor
  · rintro ⟨hp, hrec⟩ t
    exact (fs_forward_hasSum ha hp hx (fun t => by rw [hrec t]; ring) t).tsum_eq.symm
  · intro h
    obtain ⟨hb, hr⟩ := fs_forward_exists ha hx
    have hpe : p = fun t => ∑' j, (β * μ) ^ j * (κ * (Y (t + j) - Γ * gL)) := funext h
    rw [hpe]
    refine ⟨hb, fun t => ?_⟩
    beta_reduce
    rw [hr t]
    ring

/-- The trivial (deterministic) conditional expectation `E_t = id` on `ℝ`. -/
def fs_trivE : CondExpSystem ℝ ℝ where
  E _ := ContinuousLinearMap.id ℝ ℝ
  norm_le _ := ContinuousLinearMap.norm_id_le
  tower_le _ _ _ := ContinuousLinearMap.id_comp _
  tower_ge _ _ _ := ContinuousLinearMap.id_comp _

/-- The forward matrix `A⁻¹` of the homogeneous crisis system: `X_{t+1} = A⁻¹X_t` with
`X = (Ŷ, π)`. -/
noncomputable def fs_zlbM (β κ σ μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(κ * σ + β) / (μ * β), -σ / (μ * β); -κ / (μ * β), 1 / (μ * β)]

/-- The homogeneous crisis system is the forward system `X_{t+1} = A⁻¹X_t` (`μ, β > 0`). -/
theorem fs_zlb_hom_iff {β κ σ μ : ℝ} (hβ : 0 < β) (hμ : 0 < μ) (Y p : ℕ → ℝ) (t : ℕ) :
    (p t = κ * Y t + β * μ * p (t + 1) ∧ Y t = μ * Y (t + 1) + σ * μ * p (t + 1)) ↔
      Evec fs_trivE t (![Y (t + 1), p (t + 1)]) =
        matAct (fs_zlbM β κ σ μ) ![Y t, p t] + 0 := by
  have hev : Evec fs_trivE t (![Y (t + 1), p (t + 1)]) = ![Y (t + 1), p (t + 1)] := rfl
  rw [hev, add_zero]
  have hμβ : μ * β ≠ 0 := by positivity
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · simp [matAct, fs_zlbM, Fin.sum_univ_two]
      field_simp
      linear_combination -(β * h2) + σ * h1
    · simp [matAct, fs_zlbM, Fin.sum_univ_two]
      field_simp
      linear_combination -h1
  · intro h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp [matAct, fs_zlbM, Fin.sum_univ_two] at e0 e1
    field_simp at e0 e1
    constructor
    · linear_combination -e1
    · have hb : β * (Y t - (μ * Y (t + 1) + σ * μ * p (t + 1))) = β * 0 := by
        linear_combination -e0 - σ * e1
      exact sub_eq_zero.1 (mul_left_cancel₀ hβ.ne' hb)

/-- The trace and determinant of `fs_zlbM`: `(κσ + β + 1)/(μβ)` and `1/(μ²β)`; and
`1 − tr + det = h(μ)/(μ²β)`. -/
theorem fs_zlbM_tr_det {β κ σ μ : ℝ} (hβ : 0 < β) (hμ : 0 < μ) :
    fs_zlbM β κ σ μ 0 0 + fs_zlbM β κ σ μ 1 1 = (κ * σ + β + 1) / (μ * β) ∧
      fs_zlbM β κ σ μ 0 0 * fs_zlbM β κ σ μ 1 1 - fs_zlbM β κ σ μ 0 1 * fs_zlbM β κ σ μ 1 0 =
        1 / (μ ^ 2 * β) ∧
      1 - (κ * σ + β + 1) / (μ * β) + 1 / (μ ^ 2 * β) = fs_h β κ σ μ / (μ ^ 2 * β) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [fs_zlbM]
    field_simp
  · simp [fs_zlbM]
    field_simp
    ring
  · unfold fs_h
    field_simp
    ring

/-- **Exercise 19.3** (Miao, p. 669), (19.55) (p. 650). With `i_t = 0`, the crisis-state
equilibrium conditions (19.48) and (19.53) (`fs_zlbSys`) have a unique bounded solution
`(Ŷ_t, π_t)` for every `(r_L, Ĝ_L)` iff `κσμ < (1 − μ)(1 − βμ)`
(for `0 < β < 1`, `κ, σ > 0`, `0 ≤ μ < 1`). -/
theorem ex_19_3 {β κ σ μ Γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) :
    (∀ rL gL : ℝ, ∃! YP : (ℕ → ℝ) × (ℕ → ℝ),
        fs_Bdd YP.1 ∧ fs_Bdd YP.2 ∧ fs_zlbSys β κ σ μ Γ rL gL YP.1 YP.2) ↔
      κ * σ * μ < (1 - μ) * (1 - β * μ) := by
  -- bounded homogeneous solutions
  have hhom : ∀ rL gL (Y p Y' p' : ℕ → ℝ), fs_zlbSys β κ σ μ Γ rL gL Y p →
      fs_zlbSys β κ σ μ Γ rL gL Y' p' → ∀ t,
        (p t - p' t = κ * (Y t - Y' t) + β * μ * (p (t + 1) - p' (t + 1)) ∧
          Y t - Y' t = μ * (Y (t + 1) - Y' (t + 1)) + σ * μ * (p (t + 1) - p' (t + 1))) := by
    intro rL gL Y p Y' p' h h' t
    obtain ⟨a1, a2⟩ := h t
    obtain ⟨b1, b2⟩ := h' t
    constructor
    · linear_combination a1 - b1
    · linear_combination a2 - b2
  have hstab : ∀ x : ℕ → ℝ, fs_Bdd x → ∃ B, 0 < B ∧ ∀ t, |x t| < B := by
    rintro x ⟨B, hB⟩
    exact ⟨|B| + 1, by positivity, fun t => (hB t).trans_lt (by linarith [le_abs_self B])⟩
  have hsubB : ∀ x y : ℕ → ℝ, fs_Bdd x → fs_Bdd y → fs_Bdd (fun t => x t - y t) := by
    rintro x y ⟨B, hB⟩ ⟨C, hC⟩
    exact ⟨B + C, fun t => (abs_sub _ _).trans (add_le_add (hB t) (hC t))⟩
  constructor
  · intro h
    by_contra hc
    push Not at hc
    -- `μ > 0`, since (19.55) holds at `μ = 0`
    have hμ : 0 < μ := by
      rcases hμ0.lt_or_eq with h0 | h0
      · exact h0
      · subst h0
        norm_num at hc
    have hμβ : 0 < μ * β := by positivity
    set M := fs_zlbM β κ σ μ
    have hM10 : M 1 0 ≠ 0 := by
      have e : M 1 0 = -κ / (μ * β) := rfl
      rw [e]
      exact div_ne_zero (neg_ne_zero.2 hκ.ne') hμβ.ne'
    obtain ⟨eT, eD, e1⟩ := fs_zlbM_tr_det (κ := κ) (σ := σ) hβ0 hμ
    have hT : 4 ≤ (M 0 0 + M 1 1) ^ 2 := by
      rw [eT]
      have h2 : 2 ≤ (κ * σ + β + 1) / (μ * β) := by
        rw [le_div_iff₀ hμβ]
        nlinarith [mul_pos hκ hσ, mul_le_mul_of_nonneg_right hμ1.le hβ0.le]
      nlinarith
    have hnb : ¬ nkBothOut (M 0 0 + M 1 1) (M 0 0 * M 1 1 - M 0 1 * M 1 0) := by
      rw [eT, eD]
      have hD0 : 0 < 1 / (μ ^ 2 * β) := by positivity
      rintro (⟨-, h2, -⟩ | ⟨h1, -, -⟩)
      · rw [e1] at h2
        have hhn : fs_h β κ σ μ ≤ 0 := by unfold fs_h; linarith
        have : fs_h β κ σ μ / (μ ^ 2 * β) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hhn (by positivity)
        linarith
      · linarith
    obtain ⟨X, hX0, hXe, -, ⟨B, -, hXB⟩⟩ := nk_jump2_nonunique fs_trivE M hM10 hT hnb
      (w := (1 : ℝ)) one_ne_zero rfl
    obtain ⟨YP, -, hYP⟩ := h 0 0
    have hsol : ∀ Y p : ℕ → ℝ, (∀ t, p t = κ * Y t + β * μ * p (t + 1) ∧
        Y t = μ * Y (t + 1) + σ * μ * p (t + 1)) → fs_zlbSys β κ σ μ Γ 0 0 Y p := by
      intro Y p hYp t
      obtain ⟨a, b⟩ := hYp t
      constructor
      · linear_combination a
      · linear_combination b
    have hXsol : ∀ t, X t 1 = κ * X t 0 + β * μ * X (t + 1) 1 ∧
        X t 0 = μ * X (t + 1) 0 + σ * μ * X (t + 1) 1 := by
      intro t
      have hx : ∀ s, X s = ![X s 0, X s 1] := fun s => by
        funext i
        fin_cases i <;> rfl
      have := hXe t
      rw [hx t, hx (t + 1), ← add_zero (matAct M _)] at this
      exact (fs_zlb_hom_iff hβ0 hμ (fun s => X s 0) (fun s => X s 1) t).2 this
    have hXbdd : ∀ i, fs_Bdd (fun t => X t i) := fun i => ⟨B, fun t => (hXB t i).le⟩
    have e1 := hYP (fun t => X t 0, fun t => X t 1) ⟨hXbdd 0, hXbdd 1, hsol _ _ hXsol⟩
    have e2 := hYP (fun _ => 0, fun _ => 0) ⟨⟨0, fun _ => by simp⟩, ⟨0, fun _ => by simp⟩,
      hsol _ _ (fun _ => by simp)⟩
    apply hX0
    funext t i
    have := congrArg (fun q => (q.1 t, q.2 t)) (e1.trans e2.symm)
    simp only [Prod.mk.injEq] at this
    fin_cases i
    · exact this.1
    · exact this.2
  · intro h55 rL gL
    have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
    have hD : 0 < 1 - β * μ := by nlinarith
    set YL := fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL
    set πL := κ / (1 - β * μ) * (YL - Γ * gL)
    have hpair := (eq_19_58 (Γ := Γ) (gL := gL) (rL := rL) (iL := 0) (YL := YL) (πL := πL)
      hh.ne' hD.ne').2 ⟨by rw [sub_zero], rfl⟩
    refine ⟨(fun _ => YL, fun _ => πL), ⟨⟨|YL|, fun _ => le_rfl⟩, ⟨|πL|, fun _ => le_rfl⟩,
      fun t => ⟨?_, ?_⟩⟩, ?_⟩
    · simp only
      rw [hpair.1]
      field_simp
      ring
    · simp only
      linear_combination hpair.2
    · rintro ⟨Y, p⟩ ⟨hYb, hpb, hsys⟩
      have hsys0 : fs_zlbSys β κ σ μ Γ rL gL (fun _ => YL) (fun _ => πL) := fun t => by
        constructor
        · rw [hpair.1]
          field_simp
          ring
        · linear_combination hpair.2
      have hdiff := hhom rL gL Y p _ _ hsys hsys0
      -- the difference is a bounded homogeneous solution, hence zero
      have hzero : ∀ t, Y t - YL = 0 ∧ p t - πL = 0 := by
        rcases hμ0.lt_or_eq with hμ | hμ
        · set X : ℕ → Fin 2 → ℝ := fun t => ![Y t - YL, p t - πL]
          have hXe : ∀ t, Evec fs_trivE t (X (t + 1)) = matAct (fs_zlbM β κ σ μ) (X t) + 0 :=
            fun t => (fs_zlb_hom_iff hβ0 hμ (fun s => Y s - YL) (fun s => p s - πL) t).1
              (hdiff t)
          have hM : nkBothOut (fs_zlbM β κ σ μ 0 0 + fs_zlbM β κ σ μ 1 1)
              (fs_zlbM β κ σ μ 0 0 * fs_zlbM β κ σ μ 1 1 -
                fs_zlbM β κ σ μ 0 1 * fs_zlbM β κ σ μ 1 0) := by
            obtain ⟨eT, eD, e1⟩ := fs_zlbM_tr_det (κ := κ) (σ := σ) hβ0 hμ
            rw [eT, eD]
            left
            refine ⟨?_, ?_, ?_⟩
            · rw [lt_div_iff₀ (by positivity)]
              nlinarith [mul_lt_mul_of_pos_left hμ1 hμ, mul_pos hμ hμ]
            · rw [e1]
              positivity
            · positivity
          obtain ⟨Z, -, hZu⟩ := nk_jump2_unique fs_trivE (fs_zlbM β κ σ μ) hM
            (c := fun _ => 0) ⟨1, one_pos, fun _ _ => by simp⟩ (fun _ _ => by simp)
          have hXs : IsStableProc X := by
            obtain ⟨B1, hB1, hB1'⟩ := hstab _ (hsubB Y (fun _ => YL) hYb ⟨|YL|, fun _ => le_rfl⟩)
            obtain ⟨B2, hB2, hB2'⟩ := hstab _ (hsubB p (fun _ => πL) hpb ⟨|πL|, fun _ => le_rfl⟩)
            refine ⟨B1 + B2, by positivity, fun t i => ?_⟩
            fin_cases i
            · simp only [X]
              simp
              linarith [hB1' t]
            · simp only [X]
              simp
              linarith [hB2' t]
          have hX := hZu X ⟨hXe, fun _ _ => rfl, hXs⟩
          have h0 := hZu (fun _ => 0) ⟨fun t => by
            funext i
            simp [Evec, matAct, fs_trivE], fun _ _ => rfl, ⟨1, one_pos, fun _ _ => by simp⟩⟩
          intro t
          have := congrFun (hX.trans h0.symm) t
          exact ⟨by simpa [X] using congrFun this 0, by simpa [X] using congrFun this 1⟩
        · subst hμ
          intro t
          obtain ⟨d1, d2⟩ := hdiff t
          simp only [mul_zero, zero_mul, add_zero] at d1 d2
          refine ⟨d2, ?_⟩
          rw [d1, d2, mul_zero]
      have hY : Y = fun _ => YL := funext fun t => by linarith [(hzero t).1]
      have hp : p = fun _ => πL := funext fun t => by linarith [(hzero t).2]
      rw [hY, hp]

/-- **Exercise 19.3**, the solution (Miao, pp. 650, 669): under (19.55) the unique bounded
solution is the constant one with `Ŷ_t = ϑ_r r_L + ϑ_GĜ_L` (19.60) and
`π_t = κ(Ŷ_t − ΓĜ_L)/(1 − βμ)` (19.56). -/
theorem ex_19_3_solution {β κ σ μ Γ rL gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ))
    {Y p : ℕ → ℝ} (hY : fs_Bdd Y) (hp : fs_Bdd p) (hsys : fs_zlbSys β κ σ μ Γ rL gL Y p)
    (t : ℕ) :
    Y t = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL ∧
      p t = κ / (1 - β * μ) * (Y t - Γ * gL) := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  set YL := fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL
  set πL := κ / (1 - β * μ) * (YL - Γ * gL)
  have hpair := (eq_19_58 (Γ := Γ) (gL := gL) (rL := rL) (iL := 0) (YL := YL) (πL := πL)
    hh.ne' hD.ne').2 ⟨by rw [sub_zero], rfl⟩
  have hsys0 : fs_zlbSys β κ σ μ Γ rL gL (fun _ => YL) (fun _ => πL) := fun t => by
    constructor
    · rw [hpair.1]
      field_simp
      ring
    · linear_combination hpair.2
  obtain ⟨_, -, hu⟩ := (ex_19_3 (Γ := Γ) hβ0 hβ1 hκ hσ hμ0 hμ1).2 h55 rL gL
  have e1 := hu (Y, p) ⟨hY, hp, hsys⟩
  have e2 := hu (fun _ => YL, fun _ => πL) ⟨⟨|YL|, fun _ => le_rfl⟩, ⟨|πL|, fun _ => le_rfl⟩,
    hsys0⟩
  have := e1.trans e2.symm
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2]
  exact ⟨rfl, rfl⟩

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Duration of fiscal stimulus: the three-state example and the multiplier (19.61)

Miao, §19.3, pp. 654–656, and Exercise 19.4 (p. 669).

Three states: the crisis `L` (`r^net = r_L`, `Ĝ = Ĝ_L`, zero bound binding, persists with
probability `μ`), the transitional state `S` (`r^net = r̄`, `Ĝ = Ĝ_L`, Taylor rule, persists with
probability `λ`, entered from `L` with probability `(1 − μ)λ`), and the absorbing normal state
(`π = Ŷ = Ĝ = 0`). From `L`, `E_tx_{t+1} = μx_L + (1 − μ)λx_S`; from `S`, `E_tx_{t+j} = λʲx_S`.

* The transitional state (`ex_19_4_transitional`): `Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L`, with `γ_y` of
  (19.52) at `ρ = λ` and `γ_π = κ(γ_y − Γ)/(1 − βλ)`.
* The crisis state (`fs_crisis_three_state`):
  `Ŷ_L = ϑ_r r_L + ϑ_GĜ_L + ϑ_ππ_S + ϑ_C(Ŷ_S − Ĝ_L)` with
  `ϑ_π = σ(1 − μ)λ/h(μ) = (1 − μ)λϑ_r/(1 − βμ)` and `ϑ_C = (1 − μ)λ(1 − βμ)/h(μ)`;
  `ϑ_π, ϑ_C > 0` for `λ > 0` (`fs_thetaPi_pos`).
* **Correction.** The book prints `ϑ_π ≡ (1 − μ)λϑ_r` and `ϑ_C ≡ σ⁻¹ϑ_π`. Its `ϑ_C` is right
  (`fs_thetaC_eq_printed`), but its `ϑ_π` is `(1 − βμ)` times the true coefficient
  (`fs_thetaPi_printed`), and so differs from it whenever `μ, λ > 0` (`fs_thetaPi_printed_ne`);
  consequently the printed relation `ϑ_C = σ⁻¹ϑ_π` is false for the true `ϑ_π`. With the
  corrected `ϑ_π` the numbers in the text are reproduced
  (`fs_fig_19_6_point_eight`, `fs_fig_19_6_point_nine_one`).
* (19.61) and **Exercise 19.4** (`eq_19_61`, `ex_19_4`): `dY_L/dG_L = ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1)`
  (with the corrected `ϑ_π`). The final term is negative for `λ > 0` (`fs_eq_19_61_last_neg`); if
  `γ_y ≤ Γ` (`φ_y` large, `fs_gammaY_lt_Gamma_iff`) the multiplier is below `ϑ_G`
  (`fs_eq_19_61_lt_thetaG`); at `λ = 0` it equals `ϑ_G` (`fs_eq_19_61_lambda_zero`).
* Numerical claims of pp. 652 and 656 at the Eggertsson parameters: `γ_y(μ) ≈ 0.324`,
  `ϑ_G ≈ 2.29` ("nearly 2.3") and the multiplier `< 1` at `λ = 0.8`, `< 0` at `λ = 0.91`
  (`fs_fig_19_4_gammaY`, `fs_fig_19_6_lambda_zero`, `fs_fig_19_6_point_eight`,
  `fs_fig_19_6_point_nine_one`). Monotonicity in `λ` (Figure 19.6) is not formalised.
-/

namespace Miao.NewKeynesian

/-- `ϑ_π = σ(1 − μ)λ/h(μ)` (Miao, p. 655, corrected). -/
noncomputable def fs_thetaPi (β κ σ μ lam : ℝ) : ℝ := σ * (1 - μ) * lam / fs_h β κ σ μ

/-- `ϑ_C = (1 − μ)λ(1 − βμ)/h(μ)` (Miao, p. 655). -/
noncomputable def fs_thetaC (β κ σ μ lam : ℝ) : ℝ := (1 - μ) * lam * (1 - β * μ) / fs_h β κ σ μ

/-- The multiplier (19.61) `ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1)`, with `γ_y`, `γ_π` at `ρ = λ`. -/
noncomputable def fs_mult61 (β κ σ μ lam Γ φπ φy : ℝ) : ℝ :=
  fs_thetaG β κ σ μ Γ +
    fs_thetaPi β κ σ μ lam * (κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam)) +
    fs_thetaC β κ σ μ lam * (fs_gammaY σ φy κ φπ β lam Γ - 1)

/-- **Exercise 19.4**, the transitional state (Miao, p. 655): if in state `S` (19.48) holds in
the summed form with `E x_{t+j} = λʲx_S`, (19.53) holds with `r^net = r̄` and the Taylor rule
`i_S = r̄ + φ_ππ_S + φ_yŶ_S`, then `Ŷ_S = γ_yĜ_L` and `π_S = γ_πĜ_L` with `γ_y` of (19.52) at
`ρ = λ` and `γ_π = κ(γ_y − Γ)/(1 − βλ)`. -/
theorem ex_19_4_transitional {β κ σ lam Γ φπ φy rb YS gL πS iS : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hφπ : 1 < φπ)
    (hφy : 0 ≤ φy)
    (h48 : πS = κ * ∑' j : ℕ, β ^ j * (lam ^ j * (YS - Γ * gL) + (1 - lam ^ j) * (0 - Γ * 0)))
    (h53 : YS - gL = lam * (YS - gL) + (1 - lam) * (0 - 0) -
      σ * (iS - (lam * πS + (1 - lam) * 0) - rb))
    (hT : iS = rb + φπ * πS + φy * YS) :
    YS = fs_gammaY σ φy κ φπ β lam Γ * gL ∧
      πS = κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) * gL := by
  have h56 := eq_19_56 hβ0 hβ1 hl0 hl1 h48
  have h57 := (eq_19_57 (rL := rb)).1 h53
  have hY := fs_taylor_branch hβ0 hβ1 hσ hκ hl1 hφπ hφy h56 h57 hT
  rw [sub_self, mul_zero, zero_div, add_zero] at hY
  refine ⟨hY, ?_⟩
  rw [h56, hY]
  ring

/-- The crisis state of the three-state example (Miao, p. 655): with `i_L = 0`, the Phillips
curve `π_L = κ(Ŷ_L − ΓĜ_L) + β(μπ_L + (1 − μ)λπ_S)` and the Euler equation
`Ŷ_L − Ĝ_L = μ(Ŷ_L − Ĝ_L) + (1 − μ)λ(Ŷ_S − Ĝ_L) − σ(0 − (μπ_L + (1 − μ)λπ_S) − r_L)` give
`Ŷ_L = ϑ_r r_L + ϑ_GĜ_L + ϑ_ππ_S + ϑ_C(Ŷ_S − Ĝ_L)` (when `h(μ) ≠ 0`). -/
theorem fs_crisis_three_state {β κ σ μ lam Γ YL gL πL rL YS πS : ℝ}
    (hh : fs_h β κ σ μ ≠ 0)
    (hPC : πL = κ * (YL - Γ * gL) + β * (μ * πL + (1 - μ) * lam * πS))
    (hE : YL - gL = μ * (YL - gL) + (1 - μ) * lam * (YS - gL) -
      σ * (0 - (μ * πL + (1 - μ) * lam * πS) - rL)) :
    YL = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL + fs_thetaPi β κ σ μ lam * πS +
      fs_thetaC β κ σ μ lam * (YS - gL) := by
  unfold fs_thetaR fs_thetaG fs_thetaPi fs_thetaC
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    ← add_div, ← add_div, ← add_div, eq_div_iff hh]
  unfold fs_h
  linear_combination (1 - β * μ) * hE + σ * μ * hPC

/-- Miao, p. 655: `ϑ_π > 0` and `ϑ_C > 0` for `λ > 0` under (19.55). -/
theorem fs_thetaPi_pos {β κ σ μ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hμ1 : μ < 1) (hl : 0 < lam) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    0 < fs_thetaPi β κ σ μ lam ∧ 0 < fs_thetaC β κ σ μ lam := by
  have hh : 0 < fs_h β κ σ μ := by unfold fs_h; linarith
  have hD : 0 < 1 - β * μ := by nlinarith
  have h1 : 0 < 1 - μ := by linarith
  exact ⟨div_pos (by positivity) hh, div_pos (by positivity) hh⟩

/-- Miao, p. 655: the book's `ϑ_C = σ⁻¹ϑ_π^{book}` with `ϑ_π^{book} = (1 − μ)λϑ_r` is the true
`ϑ_C`. -/
theorem fs_thetaC_eq_printed {β κ σ μ lam : ℝ} (hσ : σ ≠ 0) :
    fs_thetaC β κ σ μ lam = σ⁻¹ * ((1 - μ) * lam * fs_thetaR β κ σ μ) := by
  unfold fs_thetaC fs_thetaR
  field_simp

/-- **Correction** (Miao, p. 655): the printed `ϑ_π ≡ (1 − μ)λϑ_r` is `(1 − βμ)` times the true
coefficient: `(1 − μ)λϑ_r = (1 − βμ)ϑ_π`. -/
theorem fs_thetaPi_printed {β κ σ μ lam : ℝ} :
    (1 - μ) * lam * fs_thetaR β κ σ μ = (1 - β * μ) * fs_thetaPi β κ σ μ lam := by
  unfold fs_thetaR fs_thetaPi
  ring

/-- **Counterexample to the printed `ϑ_π`** (Miao, p. 655): for `0 < μ < 1`, `λ > 0` and
`h(μ) ≠ 0`, `(1 − μ)λϑ_r ≠ ϑ_π`, so the printed coefficient is not the one the derivation
gives (`fs_crisis_three_state`). -/
theorem fs_thetaPi_printed_ne {β κ σ μ lam : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hl : 0 < lam) (hh : fs_h β κ σ μ ≠ 0) :
    (1 - μ) * lam * fs_thetaR β κ σ μ ≠ fs_thetaPi β κ σ μ lam := by
  rw [fs_thetaPi_printed]
  intro h
  have hne : fs_thetaPi β κ σ μ lam ≠ 0 := by
    unfold fs_thetaPi
    have : 0 < 1 - μ := by linarith
    exact div_ne_zero (by positivity) hh
  have : (1 - β * μ) = 1 := by
    have := mul_right_cancel₀ hne (h.trans (one_mul _).symm)
    exact this
  have : β * μ = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

/-- **Exercise 19.4** and (19.61) (Miao, pp. 655, 669): with the transitional values
`Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L` (`ex_19_4_transitional`), the crisis output is
`Ŷ_L = ϑ_r r_L + (ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1))Ĝ_L`, so the multiplier `dY_L/dG_L` is (19.61). -/
theorem eq_19_61 {β κ σ μ lam Γ φπ φy YL gL πL rL YS πS : ℝ} (hh : fs_h β κ σ μ ≠ 0)
    (hYS : YS = fs_gammaY σ φy κ φπ β lam Γ * gL)
    (hπS : πS = κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) * gL)
    (hPC : πL = κ * (YL - Γ * gL) + β * (μ * πL + (1 - μ) * lam * πS))
    (hE : YL - gL = μ * (YL - gL) + (1 - μ) * lam * (YS - gL) -
      σ * (0 - (μ * πL + (1 - μ) * lam * πS) - rL)) :
    YL = fs_thetaR β κ σ μ * rL + fs_mult61 β κ σ μ lam Γ φπ φy * gL := by
  rw [fs_crisis_three_state hh hPC hE, hYS, hπS]
  unfold fs_mult61
  ring

/-- **Exercise 19.4** (Miao, p. 669): the full three-state statement. In the transitional state
(19.48) (summed), (19.53) with `r̄` and the Taylor rule; in the crisis the three-state Phillips
curve and Euler equation with `i_L = 0`. Then `Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L` and
`Ŷ_L = ϑ_r r_L + (ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1))Ĝ_L`, whose slope in `Ĝ_L` is the multiplier
(19.61) (`HasDerivAt` of the affine map). -/
theorem ex_19_4 {β κ σ μ lam Γ φπ φy rb rL YL gL πL YS πS iS : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hφπ : 1 < φπ)
    (hφy : 0 ≤ φy) (hh : fs_h β κ σ μ ≠ 0)
    (h48 : πS = κ * ∑' j : ℕ, β ^ j * (lam ^ j * (YS - Γ * gL) + (1 - lam ^ j) * (0 - Γ * 0)))
    (h53 : YS - gL = lam * (YS - gL) + (1 - lam) * (0 - 0) -
      σ * (iS - (lam * πS + (1 - lam) * 0) - rb))
    (hT : iS = rb + φπ * πS + φy * YS)
    (hPC : πL = κ * (YL - Γ * gL) + β * (μ * πL + (1 - μ) * lam * πS))
    (hE : YL - gL = μ * (YL - gL) + (1 - μ) * lam * (YS - gL) -
      σ * (0 - (μ * πL + (1 - μ) * lam * πS) - rL)) :
    YS = fs_gammaY σ φy κ φπ β lam Γ * gL ∧
      πS = κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) * gL ∧
      YL = fs_thetaR β κ σ μ * rL + fs_mult61 β κ σ μ lam Γ φπ φy * gL ∧
      HasDerivAt (fun g => fs_thetaR β κ σ μ * rL + fs_mult61 β κ σ μ lam Γ φπ φy * g)
        (fs_mult61 β κ σ μ lam Γ φπ φy) gL := by
  obtain ⟨hYS, hπS⟩ := ex_19_4_transitional hβ0 hβ1 hσ hκ hl0 hl1 hφπ hφy h48 h53 hT
  refine ⟨hYS, hπS, eq_19_61 hh hYS hπS hPC hE, ?_⟩
  simpa using ((hasDerivAt_id gL).const_mul (fs_mult61 β κ σ μ lam Γ φπ φy)).const_add
    (fs_thetaR β κ σ μ * rL)

/-- Miao, p. 655: "Since `γ_y < 1` ... the contribution of the final term is necessarily
negative": `ϑ_C(γ_y − 1) < 0` for `λ > 0`. -/
theorem fs_eq_19_61_last_neg {β κ σ μ lam Γ φπ φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ1 : μ < 1) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hφπ : 1 < φπ) (hφy : 0 ≤ φy) (hΓ : Γ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ)) :
    fs_thetaC β κ σ μ lam * (fs_gammaY σ φy κ φπ β lam Γ - 1) < 0 :=
  mul_neg_of_pos_of_neg (fs_thetaPi_pos hβ0 hβ1 hσ hμ1 hl0 h55).2
    (sub_neg.2 (fs_gammaY_lt_one hσ hφy hκ hβ0 hβ1 hl1 hφπ hΓ))

/-- Miao, p. 656: if the Taylor rule is aggressive enough that `γ_y ≤ Γ` (for instance `φ_y`
large, `fs_gammaY_lt_Gamma_iff`), the multiplier (19.61) is smaller than `ϑ_G` when `λ > 0`. -/
theorem fs_eq_19_61_lt_thetaG {β κ σ μ lam Γ φπ φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hμ1 : μ < 1) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hφπ : 1 < φπ) (hφy : 0 ≤ φy) (hΓ : Γ < 1) (h55 : κ * σ * μ < (1 - μ) * (1 - β * μ))
    (hγ : fs_gammaY σ φy κ φπ β lam Γ ≤ Γ) :
    fs_mult61 β κ σ μ lam Γ φπ φy < fs_thetaG β κ σ μ Γ := by
  have hlast := fs_eq_19_61_last_neg hβ0 hβ1 hσ hκ hμ1 hl0 hl1 hφπ hφy hΓ h55
  have hpi := (fs_thetaPi_pos hβ0 hβ1 hσ hμ1 hl0 h55).1
  have hD : 0 < 1 - β * lam := by nlinarith
  have hγπ : κ * (fs_gammaY σ φy κ φπ β lam Γ - Γ) / (1 - β * lam) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hκ.le (by linarith)) hD.le
  have := mul_nonpos_of_nonneg_of_nonpos hpi.le hγπ
  unfold fs_mult61
  linarith

/-- Miao, p. 656: at `λ = 0` the multiplier (19.61) is `ϑ_G`. -/
theorem fs_eq_19_61_lambda_zero {β κ σ μ Γ φπ φy : ℝ} :
    fs_mult61 β κ σ μ 0 Γ φπ φy = fs_thetaG β κ σ μ Γ := by
  simp [fs_mult61, fs_thetaPi, fs_thetaC]

/-- Miao, p. 652 (Figure 19.4): at `β = 0.997`, `κ = 0.00859`, `σ = 0.862`, `Γ = 0.425`,
`φ_π = 1.5`, `φ_y = 0.25`, `μ = 0.903`, the Taylor-branch multiplier is
`γ_y(μ) ∈ (0.324, 0.325)`, and (19.55) holds. -/
theorem fs_fig_19_4_gammaY :
    (0.324 : ℝ) < fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.903 0.425 ∧
      fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.903 0.425 < 0.325 ∧
      (0.00859 : ℝ) * 0.862 * 0.903 < (1 - 0.903) * (1 - 0.997 * 0.903) := by
  unfold fs_gammaY fs_psi
  norm_num

/-- Miao, p. 656 (Figure 19.6): at the same parameters with `λ = 0`, the multiplier is
`ϑ_G ∈ (2.28, 2.29)` ("nearly 2.3"). -/
theorem fs_fig_19_6_lambda_zero :
    (2.28 : ℝ) < fs_mult61 0.997 0.00859 0.862 0.903 0 0.425 1.5 0.25 ∧
      fs_mult61 0.997 0.00859 0.862 0.903 0 0.425 1.5 0.25 < 2.29 := by
  rw [fs_eq_19_61_lambda_zero]
  unfold fs_thetaG fs_h
  norm_num

/-- Miao, p. 656 (Figure 19.6): at `λ = 0.8` the multiplier (19.61) (with the corrected `ϑ_π`)
is below one. -/
theorem fs_fig_19_6_point_eight :
    fs_mult61 0.997 0.00859 0.862 0.903 0.8 0.425 1.5 0.25 < 1 := by
  unfold fs_mult61 fs_thetaG fs_thetaPi fs_thetaC fs_gammaY fs_psi fs_h
  norm_num

/-- Miao, p. 656 (Figure 19.6): at `λ = 0.91` the multiplier (19.61) (with the corrected `ϑ_π`)
is negative. With the printed `ϑ_π = (1 − μ)λϑ_r` it would be positive (about `0.23`), so the
text's numbers confirm the correction. -/
theorem fs_fig_19_6_point_nine_one :
    fs_mult61 0.997 0.00859 0.862 0.903 0.91 0.425 1.5 0.25 < 0 ∧
      0 < fs_thetaG 0.997 0.00859 0.862 0.903 0.425 +
        (1 - 0.903) * 0.91 * fs_thetaR 0.997 0.00859 0.862 0.903 *
          (0.00859 * (fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.91 0.425 - 0.425) /
            (1 - 0.997 * 0.91)) +
        fs_thetaC 0.997 0.00859 0.862 0.903 0.91 *
          (fs_gammaY 0.862 0.25 0.00859 1.5 0.997 0.91 0.425 - 1) := by
  unfold fs_mult61 fs_thetaG fs_thetaPi fs_thetaC fs_thetaR fs_gammaY fs_psi fs_h
  norm_num

end Miao.NewKeynesian

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Government purchases and welfare

Miao, §19.3, pp. 657–661, (19.62)–(19.65), the optimal crisis purchases, and Exercise 19.5
(p. 669).

* (19.63): the first-order condition `u'(Y − G) = g'(G)` at an optimum (`eq_19_63`); the
  welfare derivative `(u' − ṽ')dY/dG + g' − u'` (`fs_welfare_deriv`), whose first term vanishes
  in the neoclassical model (`fs_welfare_deriv_neoclassical`); without `g` the derivative is
  `−u' < 0` (`fs_welfare_no_g`).
* Without the zero bound the first best `π = Ŷ − ΓĜ = Ĝ = 0` is feasible, minimises (19.64), and
  is implemented by the Taylor rule (`fs_first_best`).
* (19.65): the value of (19.64) in the two-state equilibrium (`eq_19_65`).
* The optimal `Ĝ_L`: the loss is `ξx² + λ_gĜ²` with `x = Ŷ_L − ΓĜ_L` (`fs_loss_reduced`); the
  unique minimiser `Ĝ*_L = −ξ(ϑ_G − Γ)ϑ_r r_L/(ξ(ϑ_G − Γ)² + λ_g)` (`fs_optimal_GL`), positive for
  `r_L < 0` (`fs_optimal_GL_pos`), with `ξ = (κ/(1 − βμ))² + λ_y` (the book prints `γ_y` for
  `λ_y` in `ξ`, see below).
* **Correction (zero output gap).** The level of `Ĝ_L` that eliminates the output gap and the
  deflation is `ϑ_r|r_L|/(ϑ_G − Γ)` (`fs_zero_gap_GL`), not the printed `ϑ_r|r_L|/ϑ_G`; the latter
  keeps `Ŷ_L = 0` but leaves the gap `Γϑ_r r_L/ϑ_G < 0` and deflation (`fs_zero_gap_printed`). The
  optimum lies strictly below the zero-gap level when `λ_g > 0` (`fs_optimal_GL_lt_zero_gap`), as
  in Figure 19.7 (`fs_fig_19_7`; at the printed level the inequality would fail).
* **Corrections (weights).** `λ_y = κ/ε` with `ε` the elasticity of substitution (the book writes
  `κ/θ`, using Woodford's `θ` for `ε`, while `θ` is the Calvo parameter elsewhere; Figure 19.7's
  `θ = 12.77` is `ε`); `λ_g = λ_yΓ(η_g/η_u + 1 − Γ)` (the book prints `Γγ_y` for `Γλ_y`); and
  `η_g = −Ȳg''/g'` (the elasticity with respect to `G/Ȳ`, which is what case B, `η_g = 4η_u`,
  needs). Positivity: `fs_weights_pos`.
* **Exercise 19.5** (19.64) by second-order approximation:
  - a general second-order Taylor lemma (`fs_taylor2`);
  - the flexible-price period utility `u(Y − G) + g(G) − ṽ(Y)` around the efficient steady state
    (`u' = g' = ṽ'`): zero first derivative and second derivative
    `−u'Ȳ(η_u + η_v)[(Ŷ − ΓĜ)² + Γ(η_g/η_u + 1 − Γ)Ĝ²]` along every direction
    (`ex_19_5_flex`, with the `o(s²)` remainder);
  - the price-dispersion index `Δ = θΔ₋₁e^{επ} + (1 − θ)((1 − θe^{(ε−1)π})/(1 − θ))^{ε/(ε−1)}`:
    `Δ = 1`, zero first derivative and second derivative `εθ/(1 − θ)` in `π` at `Δ₋₁ = 1`
    (`ex_19_5_dispersion`), and `Δ − 1 = θ(Δ₋₁ − 1)` at `π = 0` (`fs_dispersion_lin`);
  - the labour cost of dispersion `ṽ(YΔ)`: derivative `ṽ'(Ȳ)Ȳ` in `Δ` (`fs_labor_dispersion`);
  - the discounted dispersion `Σβᵗd_t = c/(1 − βθ)·Σβᵗπ_t²` for `d_t = θd_{t−1} + cπ_t²`
    (`fs_dispersion_sum`);
  - the assembly (`ex_19_5`): the discounted sum of the second-order terms is
    `−(u'Ȳε/(2κ̃))·Σβᵗ[π_t² + λ_y(Ŷ_t − ΓĜ_t)² + λ_gĜ_t²]`, `κ̃ = (1 − θ)(1 − βθ)/θ`, so welfare
    varies inversely with (19.64).
  The approximation argument itself (dropping third-order terms, in particular
  `θ(e^{επ} − 1)(Δ₋₁ − 1)`) is the book's; each step is proved as a precise statement.
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- Miao, (19.63), p. 657: at an optimum of `G ↦ u(Y − G) + g(G)` (output `Y` given),
`u'(Y − G) = g'(G)`. -/
theorem eq_19_63 {u u1 g g1 : ℝ → ℝ} {Y G : ℝ} (hu : HasDerivAt u (u1 (Y - G)) (Y - G))
    (hg : HasDerivAt g (g1 G) G) (hmax : IsLocalMax (fun G' => u (Y - G') + g G') G) :
    u1 (Y - G) = g1 G := by
  have hc : HasDerivAt (fun G' : ℝ => Y - G') (-1) G := by
    simpa using (hasDerivAt_id G).const_sub Y
  have h := (hu.comp (h := fun G' : ℝ => Y - G') G hc).add hg
  have := hmax.hasDerivAt_eq_zero h
  linarith

/-- Miao, p. 657: the welfare effect of government purchases. With `W(G) = u(Y(G) − G) + g(G) −
ṽ(Y(G))`, `dW/dG = (u' − ṽ')dY/dG + g' − u'`, so utility increases iff this is positive. -/
theorem fs_welfare_deriv {u u1 g g1 vt vt1 Ysol : ℝ → ℝ} {G Y' : ℝ}
    (hu : HasDerivAt u (u1 (Ysol G - G)) (Ysol G - G)) (hg : HasDerivAt g (g1 G) G)
    (hv : HasDerivAt vt (vt1 (Ysol G)) (Ysol G)) (hY : HasDerivAt Ysol Y' G) :
    HasDerivAt (fun G' => u (Ysol G' - G') + g G' - vt (Ysol G'))
      ((u1 (Ysol G - G) - vt1 (Ysol G)) * Y' + g1 G - u1 (Ysol G - G)) G := by
  have hC : HasDerivAt (fun G' => Ysol G' - G') (Y' - 1) G := hY.sub (hasDerivAt_id G)
  have h1 := hu.comp (h := fun G' => Ysol G' - G') G hC
  have h2 := hv.comp G hY
  refine ((h1.add hg).sub h2).congr_deriv ?_
  ring

/-- Miao, p. 657: "In the neoclassical model, the first term in the above expression is zero":
with (19.40) `u'(Y − G) = ṽ'(Y)`, `dW/dG = g' − u'`. -/
theorem fs_welfare_deriv_neoclassical {u1 g1 vt1 Ysol : ℝ → ℝ} {G Y' : ℝ}
    (h40 : u1 (Ysol G - G) = vt1 (Ysol G)) :
    (u1 (Ysol G - G) - vt1 (Ysol G)) * Y' + g1 G - u1 (Ysol G - G) = g1 G - u1 (Ysol G - G) := by
  rw [h40]
  ring

/-- Miao, p. 657: without intrinsic value of purchases (`g = 0`), in the neoclassical model
`dW/dG = −u' < 0`: welfare falls with `G`, so optimal purchases are as low as possible. -/
theorem fs_welfare_no_g {u u1 vt vt1 Ysol : ℝ → ℝ} {G Y' : ℝ}
    (hu : HasDerivAt u (u1 (Ysol G - G)) (Ysol G - G))
    (hv : HasDerivAt vt (vt1 (Ysol G)) (Ysol G)) (hY : HasDerivAt Ysol Y' G)
    (h40 : u1 (Ysol G - G) = vt1 (Ysol G)) (hpos : 0 < u1 (Ysol G - G)) :
    HasDerivAt (fun G' => u (Ysol G' - G') + (fun _ => (0 : ℝ)) G' - vt (Ysol G'))
      (-u1 (Ysol G - G)) G ∧ -u1 (Ysol G - G) < 0 := by
  refine ⟨(fs_welfare_deriv (g1 := fun _ => 0) hu (hasDerivAt_const G 0) hv hY).congr_deriv ?_,
    by linarith⟩
  rw [h40]
  ring

/-- The period loss in (19.64): `π² + λ_y(Ŷ − ΓĜ)² + λ_gĜ²`. -/
def fs_loss (lamy lamg Γ infl Y G : ℝ) : ℝ := infl ^ 2 + lamy * (Y - Γ * G) ^ 2 + lamg * G ^ 2

/-- Miao, pp. 658–659: if the zero bound never binds, the first best is feasible: `π_t = 0`,
`Ŷ_t = Ĝ_t = 0`, `i_t = r̄` satisfies (19.48)–(19.50) (it is implemented by the Taylor rule), it
gives zero loss, and every path has nonnegative loss, zero only if `π = Ŷ − ΓĜ = Ĝ = 0`
(`λ_y, λ_g > 0`). -/
theorem fs_first_best {κ β σ Γ φπ φy rb lamy lamg : ℝ} (hy : 0 < lamy) (hg : 0 < lamg) :
    fs_TaylorEqm κ β σ Γ φπ φy rb (fun _ => 0) (fun _ => 0) (fun _ => rb) (fun _ => 0) ∧
      fs_loss lamy lamg Γ 0 0 0 = 0 ∧
      ∀ infl Y G, 0 ≤ fs_loss lamy lamg Γ infl Y G ∧
        (fs_loss lamy lamg Γ infl Y G = 0 → infl = 0 ∧ Y - Γ * G = 0 ∧ G = 0) := by
  refine ⟨fun t => ⟨by simp, by simp, by simp⟩, by simp [fs_loss], fun infl Y G => ⟨?_, ?_⟩⟩
  · unfold fs_loss
    positivity
  · intro h
    unfold fs_loss at h
    have h1 := sq_nonneg infl
    have h2 := mul_nonneg hy.le (sq_nonneg (Y - Γ * G))
    have h3 := mul_nonneg hg.le (sq_nonneg G)
    refine ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith), ?_, ?_⟩
    · have : (Y - Γ * G) ^ 2 = 0 := by
        have : lamy * (Y - Γ * G) ^ 2 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hy.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    · have : G ^ 2 = 0 := by
        have : lamg * G ^ 2 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hg.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- Miao, (19.65), p. 659: in the two-state equilibrium the loss is `L_L` in the crisis
(probability `μᵗ` at date `t`) and `0` afterwards, so (19.64) equals
`(π_L² + λ_y(Ŷ_L − ΓĜ_L)² + λ_gĜ_L²)/(1 − βμ)`. -/
theorem eq_19_65 {β μ lamy lamg Γ πL YL gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1) :
    ∑' t : ℕ, β ^ t * (μ ^ t * fs_loss lamy lamg Γ πL YL gL +
        (1 - μ ^ t) * fs_loss lamy lamg Γ 0 0 0) =
      1 / (1 - β * μ) * fs_loss lamy lamg Γ πL YL gL := by
  have hβμ0 : 0 ≤ β * μ := by positivity
  have hβμ1 : β * μ < 1 := by nlinarith
  have : ∀ t : ℕ, β ^ t * (μ ^ t * fs_loss lamy lamg Γ πL YL gL +
      (1 - μ ^ t) * fs_loss lamy lamg Γ 0 0 0) = fs_loss lamy lamg Γ πL YL gL * (β * μ) ^ t :=
    fun t => by
      simp only [fs_loss]
      rw [mul_pow]
      ring
  simp_rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβμ0 hβμ1]
  ring

/-- `ξ = (κ/(1 − βμ))² + λ_y` (Miao, p. 659, with `λ_y` for the printed `γ_y`). -/
noncomputable def fs_xi (β κ μ lamy : ℝ) : ℝ := (κ / (1 - β * μ)) ^ 2 + lamy

/-- Miao, p. 659: with (19.56) and (19.60), the crisis loss is `ξx² + λ_gĜ_L²` where
`x = Ŷ_L − ΓĜ_L = ϑ_r r_L + (ϑ_G − Γ)Ĝ_L`. -/
theorem fs_loss_reduced {β κ σ μ Γ lamy lamg rL gL YL πL : ℝ}
    (h60 : YL = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL)
    (h56 : πL = κ / (1 - β * μ) * (YL - Γ * gL)) :
    fs_loss lamy lamg Γ πL YL gL = fs_xi β κ μ lamy *
      (fs_thetaR β κ σ μ * rL + (fs_thetaG β κ σ μ Γ - Γ) * gL) ^ 2 + lamg * gL ^ 2 := by
  rw [h56, h60]
  unfold fs_loss fs_xi
  ring

/-- Miao, p. 659: the optimal crisis purchases. For `ξ > 0`, `λ_g > 0`, the quadratic loss
`F(G) = ξ(ϑ_r r_L + (ϑ_G − Γ)G)² + λ_gG²` has the unique minimiser
`G* = −ξ(ϑ_G − Γ)ϑ_r r_L/(ξ(ϑ_G − Γ)² + λ_g)`; indeed
`F(G) − F(G*) = (ξ(ϑ_G − Γ)² + λ_g)(G − G*)²`. -/
theorem fs_optimal_GL {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg) (G : ℝ) :
    ξ * (tr * rL + (tg - Γ) * G) ^ 2 + lamg * G ^ 2 -
      (ξ * (tr * rL + (tg - Γ) * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL)) ^ 2 +
        lamg * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2) =
      (ξ * (tg - Γ) ^ 2 + lamg) *
        (G - -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 := by
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  field_simp
  ring

/-- Miao, p. 659: the minimiser is unique: `F(G) ≥ F(G*)`, with equality iff `G = G*`. -/
theorem fs_optimal_GL_unique {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg) (G : ℝ) :
    ξ * (tr * rL + (tg - Γ) * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL)) ^ 2 +
        lamg * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 ≤
      ξ * (tr * rL + (tg - Γ) * G) ^ 2 + lamg * G ^ 2 ∧
    (ξ * (tr * rL + (tg - Γ) * G) ^ 2 + lamg * G ^ 2 =
        ξ * (tr * rL + (tg - Γ) * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL)) ^ 2 +
        lamg * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 ↔
      G = -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) := by
  have h := fs_optimal_GL (tr := tr) (tg := tg) (Γ := Γ) (rL := rL) hξ hg G
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  constructor
  · nlinarith [mul_nonneg hd.le (sq_nonneg (G - -(ξ * (tg - Γ) * tr) /
      (ξ * (tg - Γ) ^ 2 + lamg) * rL))]
  · constructor
    · intro he
      have : (ξ * (tg - Γ) ^ 2 + lamg) *
          (G - -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hd.ne'
      exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    · intro he
      rw [he]

/-- Miao, p. 659: `Ĝ*_L > 0` when `r_L < 0`, `ϑ_r > 0`, `ϑ_G > Γ`, `ξ, λ_g > 0`. -/
theorem fs_optimal_GL_pos {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg) (htr : 0 < tr)
    (htg : Γ < tg) (hr : rL < 0) :
    0 < -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL := by
  have h1 : 0 < ξ * (tg - Γ) * tr := mul_pos (mul_pos hξ (sub_pos.2 htg)) htr
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos h1) hd) hr

/-- **Correction** (Miao, pp. 660–661): the purchases that eliminate the output gap,
`Ĝ_L = ϑ_r|r_L|/(ϑ_G − Γ)` (`r_L < 0`), give `Ŷ_L − ΓĜ_L = 0` and `π_L = 0` in (19.56), (19.60). -/
theorem fs_zero_gap_GL {β κ σ μ Γ rL : ℝ} (htg : fs_thetaG β κ σ μ Γ - Γ ≠ 0) (hr : rL < 0) :
    fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) -
      Γ * (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) = 0 ∧
    κ / (1 - β * μ) * (fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) -
      Γ * (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ))) = 0 := by
  have h0 : fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) -
      Γ * (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) = 0 := by
    rw [abs_of_neg hr]
    field_simp
    ring
  exact ⟨h0, by rw [h0, mul_zero]⟩

/-- **Counterexample to the printed zero-gap level** (Miao, p. 660): at `Ĝ_L = ϑ_r|r_L|/ϑ_G`
output is at its steady state, `Ŷ_L = 0`, but the output gap is `Γϑ_r r_L/ϑ_G < 0` (and so
`π_L < 0`) when `r_L < 0`, `ϑ_r, ϑ_G, Γ > 0`, `βμ < 1`, `κ > 0`. -/
theorem fs_zero_gap_printed {β κ σ μ Γ rL : ℝ} (htr : 0 < fs_thetaR β κ σ μ)
    (htg : 0 < fs_thetaG β κ σ μ Γ) (hΓ : 0 < Γ) (hr : rL < 0) (hκ : 0 < κ)
    (hD : 0 < 1 - β * μ) :
    fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / fs_thetaG β κ σ μ Γ) = 0 ∧
      0 - Γ * (fs_thetaR β κ σ μ * |rL| / fs_thetaG β κ σ μ Γ) =
        Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ ∧
      Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ < 0 ∧
      κ / (1 - β * μ) * (Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ) < 0 := by
  have hneg : Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hΓ htr) hr) htg
  refine ⟨?_, ?_, hneg, mul_neg_of_pos_of_neg (div_pos hκ hD) hneg⟩
  · rw [abs_of_neg hr]
    field_simp
    ring
  · rw [abs_of_neg hr]
    field_simp
    ring

/-- Miao, p. 661 and Figure 19.7: with `λ_g > 0` the optimal `Ĝ_L` lies strictly below the
zero-gap level `ϑ_r|r_L|/(ϑ_G − Γ)` (`r_L < 0`, `ϑ_r > 0`, `ϑ_G > Γ`, `ξ > 0`). -/
theorem fs_optimal_GL_lt_zero_gap {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg)
    (htr : 0 < tr) (htg : Γ < tg) (hr : rL < 0) :
    -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL < tr * |rL| / (tg - Γ) := by
  rw [abs_of_neg hr]
  have h1 : 0 < tg - Γ := sub_pos.2 htg
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hd h1]
  have : 0 < tr * -rL := mul_pos htr (neg_pos.2 hr)
  nlinarith [mul_pos this hg]

/-- Miao, (19.64), p. 658, the weights, corrected: `λ_y = κ/ε > 0` and
`λ_g = λ_yΓ(η_g/η_u + 1 − Γ) > 0` (for `κ, ε, η_u > 0`, `η_g ≥ 0`, `0 < Γ < 1`); also `ξ > 0`. -/
theorem fs_weights_pos {β κ μ ε ηu ηg Γ : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hu : 0 < ηu)
    (hg : 0 ≤ ηg) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) :
    0 < κ / ε ∧ 0 < κ / ε * Γ * (ηg / ηu + 1 - Γ) ∧ 0 < fs_xi β κ μ (κ / ε) := by
  have h1 : 0 < κ / ε := div_pos hκ hε
  have h2 : 0 < ηg / ηu + 1 - Γ := by
    have := div_nonneg hg hu.le
    linarith
  refine ⟨h1, by positivity, ?_⟩
  unfold fs_xi
  positivity

/-- Miao, Figure 19.7 (p. 660) at `μ = 0.903` with the parameters of Figure 19.4, `ε = 12.77`
(`λ_y = κ/ε`) and `η_g = 0` (case A, `λ_g = λ_yΓ(1 − Γ)`): the optimal `Ĝ_L/|r_L|` is in
`(15.3, 15.4)`, the corrected zero-gap level `ϑ_r/(ϑ_G − Γ)` in `(15.4, 15.5)`, and the printed
level `ϑ_r/ϑ_G` in `(12.5, 12.6)`, below the optimum. -/
theorem fs_fig_19_7 :
    (15.3 : ℝ) < fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) * fs_thetaR 0.997 0.00859 0.862 0.903 /
      (fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) ^ 2 +
        0.00859 / 12.77 * 0.425 * (1 - 0.425)) ∧
    fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) * fs_thetaR 0.997 0.00859 0.862 0.903 /
      (fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) ^ 2 +
        0.00859 / 12.77 * 0.425 * (1 - 0.425)) < 15.4 ∧
    (15.4 : ℝ) < fs_thetaR 0.997 0.00859 0.862 0.903 /
      (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) ∧
    fs_thetaR 0.997 0.00859 0.862 0.903 / (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) <
      15.5 ∧
    (12.5 : ℝ) < fs_thetaR 0.997 0.00859 0.862 0.903 / fs_thetaG 0.997 0.00859 0.862 0.903 0.425 ∧
    fs_thetaR 0.997 0.00859 0.862 0.903 / fs_thetaG 0.997 0.00859 0.862 0.903 0.425 < 12.6 := by
  unfold fs_xi fs_thetaG fs_thetaR fs_h
  norm_num

/-- A second-order Taylor statement: if `φ' = φ₁` near `0` and `φ₁` has derivative `Q` at `0`, then
`φ(s) = φ(0) + φ₁(0)s + Qs²/2 + o(s²)` (used for Exercise 19.5). -/
theorem fs_taylor2 {φ φ1 : ℝ → ℝ} {Q : ℝ} (hφ : ∀ᶠ s in 𝓝 0, HasDerivAt φ (φ1 s) s)
    (h1 : HasDerivAt φ1 Q 0) :
    (fun s => φ s - φ 0 - φ1 0 * s - Q / 2 * s ^ 2) =o[𝓝 0] (fun s => s ^ 2) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hφ
  set B := Metric.ball (0 : ℝ) δ
  have hg : ∀ x ∈ B, HasDerivWithinAt (fun s => φ s - φ 0 - φ1 0 * s - Q / 2 * s ^ 2)
      (φ1 x - φ1 0 - Q * x) B x := by
    intro x hx
    have h2 : HasDerivAt (fun s : ℝ => Q / 2 * s ^ 2) (Q / 2 * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (Q / 2)
    have := (((hball x hx).sub_const (φ 0)).sub ((hasDerivAt_id x).const_mul (φ1 0))).sub h2
    refine (this.congr_deriv ?_).hasDerivWithinAt
    ring
  have ho : (fun x => φ1 x - φ1 0 - Q * x) =o[𝓝[B] 0] fun x => (x - 0) ^ 1 := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 h1
    simp only [zero_add, smul_eq_mul] at this
    refine (this.congr_left (fun x => by ring)).mono nhdsWithin_le_nhds |>.congr_right ?_
    intro x
    ring
  have := Convex.isLittleO_pow_succ_real (convex_ball 0 δ) (Metric.mem_ball_self hδ) hg ho
  rw [nhdsWithin_eq_nhds.2 (Metric.ball_mem_nhds 0 hδ)] at this
  simpa using this

/-- **Exercise 19.5**, flexible-price part (Miao, (19.64), pp. 658, 669). Let the period utility
be `U(Y, G) = u(Y − G) + g(G) − ṽ(Y)` around a steady state `(Ȳ, Ḡ)` that is efficient and has
optimal purchases: `u'(C̄) = ṽ'(Ȳ)` (subsidy) and `u'(C̄) = g'(Ḡ)` (19.63), `C̄ = Ȳ − Ḡ`. Along
`Y = Ȳ(1 + sŶ)`, `G = Ḡ + sȲĜ`, the first derivative at `s = 0` is zero and the second is
`−u'Ȳ(η_u + η_v)[(Ŷ − ΓĜ)² + Γ(η_g/η_u + 1 − Γ)Ĝ²]`, with `η_g = −Ȳg''/g'`; so
`U = Ū + s²/2·(that) + o(s²)`. -/
theorem ex_19_5_flex {u u1 g g1 vt vt1 : ℝ → ℝ} {Yb Gb u2 g2 vt2 a b ηu ηv ηg : ℝ}
    (hu : ∀ x, HasDerivAt u (u1 x) x) (hg : ∀ x, HasDerivAt g (g1 x) x)
    (hv : ∀ x, HasDerivAt vt (vt1 x) x) (hu1 : HasDerivAt u1 u2 (Yb - Gb))
    (hg1 : HasDerivAt g1 g2 Gb) (hv1 : HasDerivAt vt1 vt2 Yb) (hYb : 0 < Yb)
    (hpos : 0 < u1 (Yb - Gb)) (heff : u1 (Yb - Gb) = vt1 Yb) (hopt : u1 (Yb - Gb) = g1 Gb)
    (hdu : ηu = fs_etaU Yb (u1 (Yb - Gb)) u2) (hdv : ηv = fs_etaV Yb (vt1 Yb) vt2)
    (hdg : ηg = fs_etaU Yb (g1 Gb) g2) (hηu : ηu ≠ 0) (hsum : ηu + ηv ≠ 0) :
    let U : ℝ → ℝ := fun s => u ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) +
      g (Gb + s * (Yb * b)) - vt (Yb + s * (Yb * a))
    let U1 : ℝ → ℝ := fun s =>
      u1 ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) * (Yb * a - Yb * b) +
        g1 (Gb + s * (Yb * b)) * (Yb * b) - vt1 (Yb + s * (Yb * a)) * (Yb * a)
    let Q := -(u1 (Yb - Gb) * Yb * (ηu + ηv)) *
      ((a - fs_Gamma ηu ηv * b) ^ 2 + fs_Gamma ηu ηv * (ηg / ηu + 1 - fs_Gamma ηu ηv) * b ^ 2)
    (∀ s, HasDerivAt U (U1 s) s) ∧ U1 0 = 0 ∧ HasDerivAt U1 Q 0 ∧
      (fun s => U s - U 0 - Q / 2 * s ^ 2) =o[𝓝 0] (fun s => s ^ 2) := by
  intro U U1 Q
  have hl1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Yb + s * (Yb * a)) (Yb * a) s := fun s =>
    (((hasDerivAt_id' s).mul_const (Yb * a)).const_add Yb).congr_deriv (by ring)
  have hlG : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Gb + s * (Yb * b)) (Yb * b) s := fun s =>
    (((hasDerivAt_id' s).mul_const (Yb * b)).const_add Gb).congr_deriv (by ring)
  have hl2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))
      (Yb * a - Yb * b) s := fun s => (hl1 s).sub (hlG s)
  have hU : ∀ s, HasDerivAt U (U1 s) s := by
    intro s
    have h1 := (hu ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))).comp
      (h := fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) s (hl2 s)
    have h2 := (hg (Gb + s * (Yb * b))).comp (h := fun s : ℝ => Gb + s * (Yb * b)) s (hlG s)
    have h3 := (hv (Yb + s * (Yb * a))).comp (h := fun s : ℝ => Yb + s * (Yb * a)) s (hl1 s)
    exact (h1.add h2).sub h3
  have hU10 : U1 0 = 0 := by
    simp only [U1, zero_mul, add_zero]
    rw [← heff, ← hopt]
    ring
  have hU1 : HasDerivAt U1 Q 0 := by
    have hu1' : HasDerivAt u1 u2 ((Yb + 0 * (Yb * a)) - (Gb + 0 * (Yb * b))) := by simpa using hu1
    have hg1' : HasDerivAt g1 g2 (Gb + 0 * (Yb * b)) := by simpa using hg1
    have hv1' : HasDerivAt vt1 vt2 (Yb + 0 * (Yb * a)) := by simpa using hv1
    have k1 := (hu1'.comp (h := fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) 0
      (hl2 0)).mul_const (Yb * a - Yb * b)
    have k2 := (hg1'.comp (h := fun s : ℝ => Gb + s * (Yb * b)) 0 (hlG 0)).mul_const (Yb * b)
    have k3 := (hv1'.comp (h := fun s : ℝ => Yb + s * (Yb * a)) 0 (hl1 0)).mul_const (Yb * a)
    refine ((k1.add k2).sub k3).congr_deriv ?_
    have hvt1 : vt1 Yb ≠ 0 := heff ▸ hpos.ne'
    have hg1n : g1 Gb ≠ 0 := hopt ▸ hpos.ne'
    have e1 : u2 = -(ηu * u1 (Yb - Gb)) / Yb := by
      rw [hdu]
      unfold fs_etaU
      field_simp
    have e2 : vt2 = ηv * u1 (Yb - Gb) / Yb := by
      rw [hdv, heff]
      unfold fs_etaV
      field_simp
    have e3 : g2 = -(ηg * u1 (Yb - Gb)) / Yb := by
      rw [hdg, hopt]
      unfold fs_etaU
      field_simp
    simp only [Q]
    rw [e1, e2, e3]
    have hsq : (a - fs_Gamma ηu ηv * b) ^ 2 + fs_Gamma ηu ηv * (ηg / ηu + 1 - fs_Gamma ηu ηv) *
        b ^ 2 = ((ηu + ηv) * a ^ 2 - 2 * ηu * a * b + (ηu + ηg) * b ^ 2) / (ηu + ηv) := by
      rw [eq_div_iff hsum]
      have hG : fs_Gamma ηu ηv = ηu / (ηu + ηv) := rfl
      rw [hG]
      field_simp
      ring
    rw [hsq]
    field_simp
    ring
  refine ⟨hU, hU10, hU1, ?_⟩
  have := fs_taylor2 (Eventually.of_forall hU) hU1
  rw [hU10] at this
  simpa using this

/-- The price-dispersion index after one period of Calvo pricing, in terms of last period's
dispersion `d` and inflation `π = ln Π` (Miao, (19.13), p. 621):
`Δ = θde^{επ} + (1 − θ)((1 − θe^{(ε−1)π})/(1 − θ))^{ε/(ε−1)}`. -/
noncomputable def fs_disp (θ ε d infl : ℝ) : ℝ :=
  θ * d * Real.exp (ε * infl) +
    (1 - θ) * ((1 - θ * Real.exp ((ε - 1) * infl)) / (1 - θ)) ^ (ε / (ε - 1))

/-- Miao, p. 658: dispersion is linear in last period's dispersion, with slope `θ` at `π = 0`:
`Δ − 1 = θ(Δ₋₁ − 1)`. -/
theorem fs_dispersion_lin {θ ε d : ℝ} (hθ1 : θ < 1) : fs_disp θ ε d 0 - 1 = θ * (d - 1) := by
  have h1 : 1 - θ ≠ 0 := by linarith
  simp [fs_disp, div_self h1]
  ring

/-- **Exercise 19.5**, price dispersion (Miao, p. 658). At `Δ₋₁ = 1`, for `0 < θ < 1`, `ε > 1`,
the dispersion index as a function of `π` has `Δ(0) = 1`, zero first derivative and second
derivative `εθ/(1 − θ)`; hence `Δ = 1 + εθ/(2(1 − θ))·π² + o(π²)`. -/
theorem ex_19_5_dispersion {θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 1 < ε) :
    let w : ℝ → ℝ := fun infl => (1 - θ * Real.exp ((ε - 1) * infl)) / (1 - θ)
    let w1 : ℝ → ℝ := fun infl => -(θ * ((ε - 1) * Real.exp ((ε - 1) * infl))) / (1 - θ)
    let ψ1 : ℝ → ℝ := fun infl => θ * 1 * (ε * Real.exp (ε * infl)) +
      (1 - θ) * (w1 infl * (ε / (ε - 1)) * w infl ^ (ε / (ε - 1) - 1))
    fs_disp θ ε 1 0 = 1 ∧ (∀ᶠ infl in 𝓝 0, HasDerivAt (fs_disp θ ε 1) (ψ1 infl) infl) ∧ ψ1 0 = 0 ∧
      HasDerivAt ψ1 (ε * θ / (1 - θ)) 0 ∧
      (fun infl => fs_disp θ ε 1 infl - 1 - ε * θ / (1 - θ) / 2 * infl ^ 2) =o[𝓝 0]
        (fun infl => infl ^ 2) := by
  intro w w1 ψ1
  have h1θ : 1 - θ ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  set k := ε / (ε - 1)
  have hw : ∀ infl, HasDerivAt w (w1 infl) infl := fun infl => by
    have := (((hasDerivAt_id' infl).const_mul (ε - 1)).exp.const_mul θ).const_sub 1
    refine (this.div_const (1 - θ)).congr_deriv ?_
    simp only [w1]
    ring
  have hw0 : w 0 = 1 := by simp [w, div_self h1θ]
  have hwc : Continuous w := by
    simp only [w]
    fun_prop
  have hwpos : ∀ᶠ infl in 𝓝 0, 0 < w infl :=
    continuousAt_const.eventually_lt hwc.continuousAt (by rw [hw0]; exact one_pos)
  have hD0 : fs_disp θ ε 1 0 = 1 := by
    simp [fs_disp, div_self h1θ]
  have hderiv : ∀ infl, 0 < w infl → HasDerivAt (fs_disp θ ε 1) (ψ1 infl) infl := by
    intro infl hπ
    have e1 := ((hasDerivAt_id' infl).const_mul ε).exp.const_mul (θ * 1)
    have e2 := ((hw infl).rpow_const (p := k) (Or.inl hπ.ne')).const_mul (1 - θ)
    refine (e1.add e2).congr_deriv ?_
    simp only [ψ1, k]
    ring
  have hψ10 : ψ1 0 = 0 := by
    simp only [ψ1, w1, hw0, Real.one_rpow, mul_zero, Real.exp_zero]
    field_simp
    ring
  have hw1d : HasDerivAt w1 (-(θ * ((ε - 1) * ((ε - 1) * 1))) / (1 - θ)) 0 := by
    have := ((((hasDerivAt_id' (0 : ℝ)).const_mul (ε - 1)).exp.const_mul (ε - 1)).const_mul
      θ).neg.div_const (1 - θ)
    refine this.congr_deriv ?_
    simp
  have hψ1 : HasDerivAt ψ1 (ε * θ / (1 - θ)) 0 := by
    have e1 := (((hasDerivAt_id' (0 : ℝ)).const_mul ε).exp.const_mul ε).const_mul (θ * 1)
    have e2 := (hw 0).rpow_const (p := k - 1) (Or.inl (by rw [hw0]; exact one_ne_zero))
    have e3 := ((hw1d.mul_const k).mul e2).const_mul (1 - θ)
    refine (e1.add e3).congr_deriv ?_
    simp only [w1, hw0, Real.one_rpow, mul_zero, Real.exp_zero, k]
    field_simp
    ring
  have hev : ∀ᶠ infl in 𝓝 0, HasDerivAt (fs_disp θ ε 1) (ψ1 infl) infl := by
    filter_upwards [hwpos] with infl hπ
    exact hderiv infl hπ
  refine ⟨hD0, hev, hψ10, hψ1, ?_⟩
  have := fs_taylor2 hev hψ1
  rw [hψ10, hD0] at this
  simpa using this

/-- Miao, p. 658: the labour cost of dispersion. With `∫ Y_j = YΔ = f(N)`, hours cost
`ṽ(YΔ)`, whose derivative in `Δ` at `Δ = 1` is `ṽ'(Ȳ)Ȳ`; so `ṽ(YΔ) ≈ ṽ(Y) + ṽ'(Ȳ)Ȳ(Δ − 1)`. -/
theorem fs_labor_dispersion {vt vt1 : ℝ → ℝ} {Yb : ℝ} (hv : HasDerivAt vt (vt1 Yb) Yb) :
    HasDerivAt (fun D => vt (Yb * D)) (vt1 Yb * Yb) 1 := by
  have hl : HasDerivAt (fun D : ℝ => Yb * D) Yb 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_mul Yb
  have hv' : HasDerivAt vt (vt1 Yb) (Yb * 1) := by simpa using hv
  exact hv'.comp (h := fun D : ℝ => Yb * D) 1 hl

/-- Miao, p. 658: the discounted dispersion. If `d_0 = cπ_0²`, `d_{t+1} = θd_t + cπ_{t+1}²`
(`0 ≤ θ < 1`, `0 < β < 1`, `π` bounded), then `Σβᵗd_t = c/(1 − βθ)·Σβᵗπ_t²`. -/
theorem fs_dispersion_sum {β θ c : ℝ} {d infl : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hπ : fs_Bdd infl) (hd0 : d 0 = c * infl 0 ^ 2)
    (hd : ∀ t, d (t + 1) = θ * d t + c * infl (t + 1) ^ 2) :
    ∑' t, β ^ t * d t = c / (1 - β * θ) * ∑' t, β ^ t * infl t ^ 2 := by
  obtain ⟨B, hB⟩ := hπ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hπ2 : ∀ t, |infl t ^ 2| ≤ B ^ 2 := fun t => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  have hdB : ∀ t, |d t| ≤ |c| * B ^ 2 / (1 - θ) := by
    have h1 : 0 < 1 - θ := by linarith
    have key : |c| * B ^ 2 ≤ |c| * B ^ 2 / (1 - θ) := by
      rw [le_div_iff₀ h1]
      nlinarith [mul_nonneg (abs_nonneg c) (sq_nonneg B)]
    intro t
    induction t with
    | zero =>
      rw [hd0, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hπ2 0) (abs_nonneg c)).trans key
    | succ n ih =>
      rw [hd n]
      calc |θ * d n + c * infl (n + 1) ^ 2| ≤ |θ * d n| + |c * infl (n + 1) ^ 2| := abs_add_le _ _
        _ ≤ θ * (|c| * B ^ 2 / (1 - θ)) + |c| * B ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg hθ0]
          exact add_le_add (mul_le_mul_of_nonneg_left ih hθ0)
            (mul_le_mul_of_nonneg_left (hπ2 _) (abs_nonneg c))
        _ = |c| * B ^ 2 / (1 - θ) := by
          field_simp
          ring
  have hβa : |(β : ℝ)| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hsd : Summable (fun t => β ^ t * d t) :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right
      (|c| * B ^ 2 / (1 - θ))) (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hdB t) (by positivity))
  have hsp : Summable (fun t => β ^ t * infl t ^ 2) :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right (B ^ 2))
      (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hπ2 t) (by positivity))
  have hsp1 : Summable (fun t => β ^ t * infl (t + 1) ^ 2) :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right (B ^ 2))
      (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hπ2 (t + 1)) (by positivity))
  have eS := hsd.tsum_eq_zero_add
  have eP := hsp.tsum_eq_zero_add
  have hshift : ∀ t, β ^ (t + 1) * d (t + 1) =
      β * θ * (β ^ t * d t) + β * c * (β ^ t * infl (t + 1) ^ 2) := fun t => by
    rw [hd t]
    ring
  have hshiftP : ∀ t, β ^ (t + 1) * infl (t + 1) ^ 2 = β * (β ^ t * infl (t + 1) ^ 2) := fun t => by
    ring
  simp_rw [hshift] at eS
  simp_rw [hshiftP] at eP
  rw [Summable.tsum_add (hsd.mul_left _) (hsp1.mul_left _), tsum_mul_left, tsum_mul_left] at eS
  rw [tsum_mul_left] at eP
  simp only [pow_zero, one_mul] at eS eP
  have hD : 0 < 1 - β * θ := by nlinarith
  rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
  rw [hd0] at eS
  linear_combination eS - c * eP

/-- **Exercise 19.5**, the assembly (Miao, (19.64), p. 658). Let `uY = u'(C̄)Ȳ > 0`,
`Γ = η_u/(η_u + η_v)` (the identity holds for every `Γ`), `κ̃ = (1 − θ)(1 − βθ)/θ`,
`κ = κ̃(η_u + η_v)`, `λ_y = κ/ε` and
`λ_g = λ_yΓ(η_g/η_u + 1 − Γ)`. Let `d_t` (the dispersion term `Δ_t − 1`) follow the second-order
recursion `d_t = θd_{t−1} + εθ/(2(1 − θ))·π_t²`, `d_{−1} = 0` (`ex_19_5_dispersion`,
`fs_dispersion_lin`). Then the discounted sum of the second-order terms of the period utility,
`−uY(η_u + η_v)/2·[(Ŷ_t − ΓĜ_t)² + Γ(η_g/η_u + 1 − Γ)Ĝ_t²]` (`ex_19_5_flex`) minus the labour cost
of dispersion `uY·d_t` (`fs_labor_dispersion`, `u' = ṽ'`), equals
`−(uYε/(2κ̃))·Σβᵗ[π_t² + λ_y(Ŷ_t − ΓĜ_t)² + λ_gĜ_t²]`: welfare varies inversely with (19.64). -/
theorem ex_19_5 {β θ ε ηu ηv ηg uY Γ κt lamy lamg : ℝ} {infl Y G d : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (hu : 0 < ηu) (hv : 0 < ηv)
    (hπ : fs_Bdd infl) (hY : fs_Bdd Y) (hG : fs_Bdd G)
    (hd0 : d 0 = ε * θ / (2 * (1 - θ)) * infl 0 ^ 2)
    (hd : ∀ t, d (t + 1) = θ * d t + ε * θ / (2 * (1 - θ)) * infl (t + 1) ^ 2)
    (hκt : κt = (1 - θ) * (1 - β * θ) / θ)
    (hly : lamy = κt * (ηu + ηv) / ε) (hlg : lamg = lamy * Γ * (ηg / ηu + 1 - Γ)) :
    ∑' t, β ^ t * (-(uY * (ηu + ηv) / 2) *
        ((Y t - Γ * G t) ^ 2 + Γ * (ηg / ηu + 1 - Γ) * G t ^ 2) - uY * d t) =
      -(uY * ε / (2 * κt)) * ∑' t, β ^ t * fs_loss lamy lamg Γ (infl t) (Y t) (G t) := by
  have hβa : |(β : ℝ)| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hsum : ∀ x : ℕ → ℝ, fs_Bdd x → Summable (fun t => β ^ t * x t) := by
    rintro x ⟨B, hB⟩
    exact Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right B)
      (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hB t) (by positivity))
  have hsq : ∀ x : ℕ → ℝ, fs_Bdd x → fs_Bdd (fun t => x t ^ 2) := by
    rintro x ⟨B, hB⟩
    exact ⟨B ^ 2, fun t => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2⟩
  have hgap : fs_Bdd (fun t => Y t - Γ * G t) := by
    obtain ⟨B1, h1⟩ := hY
    obtain ⟨B2, h2⟩ := hG
    exact ⟨B1 + |Γ| * B2, fun t => (abs_sub _ _).trans (add_le_add (h1 t)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h2 t) (abs_nonneg _)))⟩
  have sP := (hsum _ (hsq _ hπ)).hasSum
  have sX := (hsum _ (hsq _ hgap)).hasSum
  have sG := (hsum _ (hsq _ hG)).hasSum
  have hdsum := fs_dispersion_sum hβ0 hβ1 hθ0.le hθ1 hπ hd0 hd
  have hdB : fs_Bdd d := by
    obtain ⟨B, hB⟩ := hπ
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    set c := ε * θ / (2 * (1 - θ))
    have hc : 0 ≤ c := by
      have : 0 < 1 - θ := by linarith
      positivity
    have h1 : 0 < 1 - θ := by linarith
    refine ⟨c * B ^ 2 / (1 - θ), fun t => ?_⟩
    have hπ2 : ∀ t, |infl t ^ 2| ≤ B ^ 2 := fun t => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
    have key : c * B ^ 2 ≤ c * B ^ 2 / (1 - θ) := by
      rw [le_div_iff₀ h1]
      nlinarith [mul_nonneg hc (sq_nonneg B)]
    induction t with
    | zero =>
      rw [hd0, abs_mul, abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left (hπ2 0) hc).trans key
    | succ n ih =>
      rw [hd n]
      calc |θ * d n + c * infl (n + 1) ^ 2| ≤ |θ * d n| + |c * infl (n + 1) ^ 2| := abs_add_le _ _
        _ ≤ θ * (c * B ^ 2 / (1 - θ)) + c * B ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos hθ0, abs_of_nonneg hc]
          exact add_le_add (mul_le_mul_of_nonneg_left ih hθ0.le)
            (mul_le_mul_of_nonneg_left (hπ2 _) hc)
        _ = c * B ^ 2 / (1 - θ) := by
          field_simp
          ring
  have sD := (hsum _ hdB).hasSum
  have hL : HasSum (fun t => β ^ t * (-(uY * (ηu + ηv) / 2) *
      ((Y t - Γ * G t) ^ 2 + Γ * (ηg / ηu + 1 - Γ) * G t ^ 2) - uY * d t))
      (-(uY * (ηu + ηv) / 2) * ∑' t, β ^ t * (Y t - Γ * G t) ^ 2 +
        -(uY * (ηu + ηv) / 2) * (Γ * (ηg / ηu + 1 - Γ)) * ∑' t, β ^ t * G t ^ 2 -
        uY * ∑' t, β ^ t * d t) :=
    (((sX.mul_left (-(uY * (ηu + ηv) / 2))).add
      (sG.mul_left (-(uY * (ηu + ηv) / 2) * (Γ * (ηg / ηu + 1 - Γ))))).sub
        (sD.mul_left uY)).congr_fun (fun t => by ring)
  have hR : HasSum (fun t => β ^ t * fs_loss lamy lamg Γ (infl t) (Y t) (G t))
      (∑' t, β ^ t * infl t ^ 2 + lamy * ∑' t, β ^ t * (Y t - Γ * G t) ^ 2 +
        lamg * ∑' t, β ^ t * G t ^ 2) :=
    ((sP.add (sX.mul_left lamy)).add (sG.mul_left lamg)).congr_fun (fun t => by
      simp only [fs_loss]
      ring)
  rw [hL.tsum_eq, hR.tsum_eq, hdsum]
  have h1θ : 0 < 1 - θ := by linarith
  have hD : 0 < 1 - β * θ := by nlinarith
  have hκt0 : 0 < κt := by rw [hκt]; positivity
  have e1 : ε * θ / (2 * (1 - θ)) / (1 - β * θ) = ε / (2 * κt) := by
    rw [hκt]
    field_simp
  have e2 : uY * ε / (2 * κt) * lamy = uY * (ηu + ηv) / 2 := by
    rw [hly]
    field_simp
  rw [hlg]
  linear_combination (-(uY * ∑' t, β ^ t * infl t ^ 2)) * e1 +
    (∑' t, β ^ t * (Y t - Γ * G t) ^ 2) * e2 +
    (Γ * (ηg / ηu + 1 - Γ) * ∑' t, β ^ t * G t ^ 2) * e2

end Miao.NewKeynesian

set_option linter.style.longLine false
#print axioms Miao.NewKeynesian.IsSolution
#print axioms Miao.NewKeynesian.IsRegular
#print axioms Miao.NewKeynesian.EventuallyConst
#print axioms Miao.NewKeynesian.IsStableSeq
#print axioms Miao.NewKeynesian.IsSteadyStateOf
#print axioms Miao.NewKeynesian.IsAsympStable
#print axioms Miao.NewKeynesian.basin
#print axioms Miao.NewKeynesian.IsGloballyStable
#print axioms Miao.NewKeynesian.IsStableMatrix
#print axioms Miao.NewKeynesian.isGloballyStable_iff_basin
#print axioms Miao.NewKeynesian.isAsympStable_iff_basin
#print axioms Miao.NewKeynesian.isStableSeq_iff_bddAbove
#print axioms Miao.NewKeynesian.tendsto_zero_of_le_rec
#print axioms Miao.NewKeynesian.tendsto_zero_of_rec
#print axioms Miao.NewKeynesian.triangular_step
#print axioms Miao.NewKeynesian.triangular_invariant
#print axioms Miao.NewKeynesian.triangular_tendsto_iff
#print axioms Miao.NewKeynesian.mclm
#print axioms Miao.NewKeynesian.mclm_apply
#print axioms Miao.NewKeynesian.norm_mulVec_le
#print axioms Miao.NewKeynesian.norm_mclm_mul_le
#print axioms Miao.NewKeynesian.tendsto_norm_mclm_pow
#print axioms Miao.NewKeynesian.summable_of_tendsto_zero
#print axioms Miao.NewKeynesian.diag_mul_of_upper
#print axioms Miao.NewKeynesian.upper_inv
#print axioms Miao.NewKeynesian.diag_inv_of_upper
#print axioms Miao.NewKeynesian.summable_norm_pow_of_triangular
#print axioms Miao.NewKeynesian.stableSubspace
#print axioms Miao.NewKeynesian.unstableSubspace
#print axioms Miao.NewKeynesian.convSubspace
#print axioms Miao.NewKeynesian.mem_convSubspace
#print axioms Miao.NewKeynesian.tendsto_of_mem_maxGenEigenspace
#print axioms Miao.NewKeynesian.not_tendsto_of_eigen
#print axioms Miao.NewKeynesian.stable_le_conv
#print axioms Miao.NewKeynesian.stable_sup_unstable
#print axioms Miao.NewKeynesian.disjoint_stable_unstable
#print axioms Miao.NewKeynesian.unstable_invariant
#print axioms Miao.NewKeynesian.tendsto_iff_mem_stable
#print axioms Miao.NewKeynesian.stable_eq_top
#print axioms Miao.NewKeynesian.cplx
#print axioms Miao.NewKeynesian.cplx_sub
#print axioms Miao.NewKeynesian.cplx_add
#print axioms Miao.NewKeynesian.tendsto_cplx_iff
#print axioms Miao.NewKeynesian.cplxEnd
#print axioms Miao.NewKeynesian.cplxEnd_pow_cplx
#print axioms Miao.NewKeynesian.hasEigenvalue_cplxEnd_iff
#print axioms Miao.NewKeynesian.finrank_biSup_maxGenEigenspace
#print axioms Miao.NewKeynesian.finrank_stableSubspace
#print axioms Miao.NewKeynesian.conjV
#print axioms Miao.NewKeynesian.conjV_conjV
#print axioms Miao.NewKeynesian.conjV_add
#print axioms Miao.NewKeynesian.conjV_sub
#print axioms Miao.NewKeynesian.conjV_smul
#print axioms Miao.NewKeynesian.conjV_zero
#print axioms Miao.NewKeynesian.conjV_cplx
#print axioms Miao.NewKeynesian.eq_cplx_re
#print axioms Miao.NewKeynesian.cplxEnd_conjV
#print axioms Miao.NewKeynesian.pow_sub_conjV
#print axioms Miao.NewKeynesian.conjV_mem_maxGenEigenspace
#print axioms Miao.NewKeynesian.conjV_mem_biSup
#print axioms Miao.NewKeynesian.conjV_mem_stable
#print axioms Miao.NewKeynesian.conjV_mem_unstable
#print axioms Miao.NewKeynesian.cplxL
#print axioms Miao.NewKeynesian.stableR
#print axioms Miao.NewKeynesian.unstableR
#print axioms Miao.NewKeynesian.mem_stableR
#print axioms Miao.NewKeynesian.mem_unstableR
#print axioms Miao.NewKeynesian.mem_stableR_iff
#print axioms Miao.NewKeynesian.cplx_mulVec
#print axioms Miao.NewKeynesian.stableR_invariant
#print axioms Miao.NewKeynesian.unstableR_invariant
#print axioms Miao.NewKeynesian.isCompl_stableR_unstableR
#print axioms Miao.NewKeynesian.linearIndependent_cplx
#print axioms Miao.NewKeynesian.finrank_le_of_cplx
#print axioms Miao.NewKeynesian.finrank_stableR
#print axioms Miao.NewKeynesian.unstableR_ker
#print axioms Miao.NewKeynesian.uniform_bound_of_basis
#print axioms Miao.NewKeynesian.exists_bound_of_tendsto
#print axioms Miao.NewKeynesian.mem_maxGen_smul
#print axioms Miao.NewKeynesian.projS
#print axioms Miao.NewKeynesian.projU
#print axioms Miao.NewKeynesian.projS_add_projU
#print axioms Miao.NewKeynesian.projS_mem
#print axioms Miao.NewKeynesian.projU_mem
#print axioms Miao.NewKeynesian.projS_of_mem
#print axioms Miao.NewKeynesian.projS_of_mem_unstable
#print axioms Miao.NewKeynesian.projU_of_mem
#print axioms Miao.NewKeynesian.projU_of_mem_stable
#print axioms Miao.NewKeynesian.projS_mulVec
#print axioms Miao.NewKeynesian.projU_mulVec
#print axioms Miao.NewKeynesian.pow_mulVec_mem_stableR
#print axioms Miao.NewKeynesian.tendsto_scaled_of_stable
#print axioms Miao.NewKeynesian.scaled_pow_cplx
#print axioms Miao.NewKeynesian.stable_bound
#print axioms Miao.NewKeynesian.isStableMatrix_iff_roots
#print axioms Miao.NewKeynesian.tendsto_of_isStableMatrix
#print axioms Miao.NewKeynesian.isStableMatrix_of_tendsto
#print axioms Miao.NewKeynesian.isStableMatrix_iff_tendsto
#print axioms Miao.NewKeynesian.HasGeomDecay
#print axioms Miao.NewKeynesian.hasGeomDecay_of_isStableMatrix
#print axioms Miao.NewKeynesian.isStableMatrix_inv
#print axioms Miao.NewKeynesian.footnote_2
#print axioms Miao.NewKeynesian.isRegular_of_isUnit_det
#print axioms Miao.NewKeynesian.example_scalar_not_regular
#print axioms Miao.NewKeynesian.example_scalar_no_solution
#print axioms Miao.NewKeynesian.remark_nonregular_no_solution
#print axioms Miao.NewKeynesian.remark_nonregular_counterexample
#print axioms Miao.NewKeynesian.eq_1_21
#print axioms Miao.NewKeynesian.eq_1_21_solution
#print axioms Miao.NewKeynesian.eq_1_21_steadyState
#print axioms Miao.NewKeynesian.isSteadyStateOf_of_not_mem_range
#print axioms Miao.NewKeynesian.isStableSeq_iff_exists_le
#print axioms Miao.NewKeynesian.exists_mulVec_bound
#print axioms Miao.NewKeynesian.bounded_mulVec
#print axioms Miao.NewKeynesian.norm_sum_type_le
#print axioms Miao.NewKeynesian.norm_comp_inl_le
#print axioms Miao.NewKeynesian.norm_comp_inr_le
#print axioms Miao.NewKeynesian.backward_sol_eq
#print axioms Miao.NewKeynesian.bounded_backward
#print axioms Miao.NewKeynesian.summable_geom_series
#print axioms Miao.NewKeynesian.mulVec_tsum_rs
#print axioms Miao.NewKeynesian.tsum_geom_series_succ
#print axioms Miao.NewKeynesian.eq_zero_of_bounded_orbit
#print axioms Miao.NewKeynesian.IsRealBlockSplit
#print axioms Miao.NewKeynesian.blockDiag_mulVec_inl
#print axioms Miao.NewKeynesian.blockDiag_mulVec_inr
#print axioms Miao.NewKeynesian.mulVec_comp_inl
#print axioms Miao.NewKeynesian.mulVec_comp_inr
#print axioms Miao.NewKeynesian.IsRealBlockSplit.mul_R
#print axioms Miao.NewKeynesian.card_add_card_of_inv
#print axioms Miao.NewKeynesian.IsRealBlockSplit.isUnit_one_sub
#print axioms Miao.NewKeynesian.eigen_transport
#print axioms Miao.NewKeynesian.exists_real_block_split
#print axioms Miao.NewKeynesian.eq_1_22
#print axioms Miao.NewKeynesian.exists_sol_rec
#print axioms Miao.NewKeynesian.sol_rec_unique
#print axioms Miao.NewKeynesian.exists_unique_solution
#print axioms Miao.NewKeynesian.eq_1_24
#print axioms Miao.NewKeynesian.eq_1_25
#print axioms Miao.NewKeynesian.isUnit_sub_det
#print axioms Miao.NewKeynesian.xbar_eq
#print axioms Miao.NewKeynesian.theorem_1_4_1
#print axioms Miao.NewKeynesian.forwardU
#print axioms Miao.NewKeynesian.forwardU_rec
#print axioms Miao.NewKeynesian.forwardU_bounded
#print axioms Miao.NewKeynesian.forwardU_unique
#print axioms Miao.NewKeynesian.split_rec_inl
#print axioms Miao.NewKeynesian.split_rec_inr
#print axioms Miao.NewKeynesian.bounded_of_split
#print axioms Miao.NewKeynesian.eq_1_29
#print axioms Miao.NewKeynesian.eq_1_30
#print axioms Miao.NewKeynesian.eq_1_31
#print axioms Miao.NewKeynesian.eq_1_32
#print axioms Miao.NewKeynesian.bk_exists
#print axioms Miao.NewKeynesian.bk_unique
#print axioms Miao.NewKeynesian.theorem_1_4_2
#print axioms Miao.NewKeynesian.blocks_of_inv
#print axioms Miao.NewKeynesian.rks_inv
#print axioms Miao.NewKeynesian.puy_inv_of_rks
#print axioms Miao.NewKeynesian.bk_order_iff
#print axioms Miao.NewKeynesian.eq_1_33
#print axioms Miao.NewKeynesian.corollary_1_4_1
#print axioms Miao.NewKeynesian.eq_1_34
#print axioms Miao.NewKeynesian.stable_initial_iff
#print axioms Miao.NewKeynesian.stableArm
#print axioms Miao.NewKeynesian.mem_stableArm
#print axioms Miao.NewKeynesian.stableArm_iff
#print axioms Miao.NewKeynesian.finrank_stableArm
#print axioms Miao.NewKeynesian.stable_initial_translate
#print axioms Miao.NewKeynesian.remark_unit_root
#print axioms Miao.NewKeynesian.IsGenEigenvector
#print axioms Miao.NewKeynesian.IsGenEigenvalue
#print axioms Miao.NewKeynesian.genEigenvalues
#print axioms Miao.NewKeynesian.isGenEigenvalue_iff_det
#print axioms Miao.NewKeynesian.det_ne_zero_of_unitary
#print axioms Miao.NewKeynesian.conj_lincomb
#print axioms Miao.NewKeynesian.det_conj_lincomb
#print axioms Miao.NewKeynesian.upper_lincomb
#print axioms Miao.NewKeynesian.det_upper_lincomb
#print axioms Miao.NewKeynesian.diag_ne_zero_of_regular
#print axioms Miao.NewKeynesian.genEigenvalues_eq_diag
#print axioms Miao.NewKeynesian.exists_eigenPair
#print axioms Miao.NewKeynesian.exists_unitary_col
#print axioms Miao.NewKeynesian.deflate
#print axioms Miao.NewKeynesian.det_of_col_zero
#print axioms Miao.NewKeynesian.blockOne
#print axioms Miao.NewKeynesian.blockOne_mul_zero
#print axioms Miao.NewKeynesian.blockOne_mul_succ
#print axioms Miao.NewKeynesian.mul_blockOne_zero
#print axioms Miao.NewKeynesian.mul_blockOne_succ
#print axioms Miao.NewKeynesian.blockOne_mul_blockOne
#print axioms Miao.NewKeynesian.star_blockOne
#print axioms Miao.NewKeynesian.blockOne_one
#print axioms Miao.NewKeynesian.blockOne_mem
#print axioms Miao.NewKeynesian.assemble_apply
#print axioms Miao.NewKeynesian.assemble_upper
#print axioms Miao.NewKeynesian.proportional_of_cross
#print axioms Miao.NewKeynesian.ScaleInvariant
#print axioms Miao.NewKeynesian.exists_qz_ordered
#print axioms Miao.NewKeynesian.theorem_1_4_4
#print axioms Miao.NewKeynesian.scaleInvariant_stable
#print axioms Miao.NewKeynesian.theorem_1_4_4_stable
#print axioms Miao.NewKeynesian.norm_mulVec_le_sum
#print axioms Miao.NewKeynesian.isStableSeq_of_le
#print axioms Miao.NewKeynesian.IsStableSeq.bound
#print axioms Miao.NewKeynesian.IsStableSeq.mulVec
#print axioms Miao.NewKeynesian.fwdSum
#print axioms Miao.NewKeynesian.summable_fwd
#print axioms Miao.NewKeynesian.norm_fwdSum_le
#print axioms Miao.NewKeynesian.fwdSum_rec
#print axioms Miao.NewKeynesian.eq_fwdSum
#print axioms Miao.NewKeynesian.isStableSeq_of_rec
#print axioms Miao.NewKeynesian.IsStableSeq.add
#print axioms Miao.NewKeynesian.IsStableSeq.sub
#print axioms Miao.NewKeynesian.IsStableSeq.shift
#print axioms Miao.NewKeynesian.norm_comp_le
#print axioms Miao.NewKeynesian.IsStableSeq.comp
#print axioms Miao.NewKeynesian.isStableSeq_append
#print axioms Miao.NewKeynesian.upper_castAdd
#print axioms Miao.NewKeynesian.upper_natAdd
#print axioms Miao.NewKeynesian.mulVec_castAdd
#print axioms Miao.NewKeynesian.mulVec_natAdd
#print axioms Miao.NewKeynesian.eq_1_36
#print axioms Miao.NewKeynesian.solve_fwd
#print axioms Miao.NewKeynesian.eq_1_38
#print axioms Miao.NewKeynesian.det_S11_ne_zero
#print axioms Miao.NewKeynesian.det_T22_ne_zero
#print axioms Miao.NewKeynesian.summable_Ms
#print axioms Miao.NewKeynesian.summable_Mu
#print axioms Miao.NewKeynesian.klein_core
#print axioms Miao.NewKeynesian.klein_homog
#print axioms Miao.NewKeynesian.eq_1_37
#print axioms Miao.NewKeynesian.eq_1_39_40
#print axioms Miao.NewKeynesian.isSolution_iff_transformed
#print axioms Miao.NewKeynesian.diag_off_circle
#print axioms Miao.NewKeynesian.theorem_1_4_5
#print axioms Miao.NewKeynesian.det_sub_ne_zero
#print axioms Miao.NewKeynesian.corollary_1_4_1_singular
#print axioms Miao.NewKeynesian.map_ofReal_mulVec
#print axioms Miao.NewKeynesian.norm_ofReal_vec
#print axioms Miao.NewKeynesian.isSolution_ofReal_iff
#print axioms Miao.NewKeynesian.theorem_1_4_5_real
#print axioms Miao.NewKeynesian.eq_s0
#print axioms Miao.NewKeynesian.remark_augmented
#print axioms Miao.NewKeynesian.remark_u_eq_zero
#print axioms Miao.NewKeynesian.eq_1_37_printed_false
#print axioms Miao.NewKeynesian.caganA
#print axioms Miao.NewKeynesian.caganB
#print axioms Miao.NewKeynesian.caganC
#print axioms Miao.NewKeynesian.example_cagan_iff
#print axioms Miao.NewKeynesian.example_cagan_det
#print axioms Miao.NewKeynesian.example_cagan_regular
#print axioms Miao.NewKeynesian.example_cagan_genEigenvalues
#print axioms Miao.NewKeynesian.example_cagan_genEigenvalues_zero
#print axioms Miao.NewKeynesian.CondExpSystem
#print axioms Miao.NewKeynesian.CondExpSystem.mk
#print axioms Miao.NewKeynesian.CondExpSystem.E
#print axioms Miao.NewKeynesian.CondExpSystem.norm_le
#print axioms Miao.NewKeynesian.CondExpSystem.tower_le
#print axioms Miao.NewKeynesian.CondExpSystem.tower_ge
#print axioms Miao.NewKeynesian.CondExpSystem.tower_le_apply
#print axioms Miao.NewKeynesian.CondExpSystem.tower_ge_apply
#print axioms Miao.NewKeynesian.CondExpSystem.idem
#print axioms Miao.NewKeynesian.CondExpSystem.norm_apply_le
#print axioms Miao.NewKeynesian.IsAdaptedV
#print axioms Miao.NewKeynesian.IsStableProc
#print axioms Miao.NewKeynesian.matAct
#print axioms Miao.NewKeynesian.Evec
#print axioms Miao.NewKeynesian.IsRESolution
#print axioms Miao.NewKeynesian.IsPredeterminedBK
#print axioms Miao.NewKeynesian.Evec_matAct
#print axioms Miao.NewKeynesian.matAct_add
#print axioms Miao.NewKeynesian.matAct_mul
#print axioms Miao.NewKeynesian.matAct_one
#print axioms Miao.NewKeynesian.condExpL1_norm_apply_le
#print axioms Miao.NewKeynesian.condExpL1_ae_eq_condExp
#print axioms Miao.NewKeynesian.condExpL1_tower_le
#print axioms Miao.NewKeynesian.condExpL1_tower_ge
#print axioms Miao.NewKeynesian.condExpL1CLMK
#print axioms Miao.NewKeynesian.condExpL1CLMK_apply
#print axioms Miao.NewKeynesian.condExpSystemL1
#print axioms Miao.NewKeynesian.condExpSystemL1_E_apply
#print axioms Miao.NewKeynesian.condExpSystemL1_real
#print axioms Miao.NewKeynesian.condExpSystemL1_complex
#print axioms Miao.NewKeynesian.condExpSystemL1_ae_eq
#print axioms Miao.NewKeynesian.condExpL1_eq_self_iff
#print axioms Miao.NewKeynesian.condExpL1_eq_self_iff_exists
#print axioms Miao.NewKeynesian.condExpL1_isAdaptedV_iff
#print axioms Miao.NewKeynesian.l1_norm_eq_integral_abs
#print axioms Miao.NewKeynesian.l1_isStableProc_iff
#print axioms Miao.NewKeynesian.l1_norm_eq_integral_norm_complex
#print axioms Miao.NewKeynesian.sre_IsAdapted
#print axioms Miao.NewKeynesian.sre_IsBounded
#print axioms Miao.NewKeynesian.sre_isStableProc_iff
#print axioms Miao.NewKeynesian.sre_isAdaptedV_iff
#print axioms Miao.NewKeynesian.sre_adapted_succ
#print axioms Miao.NewKeynesian.sre_adapted_le
#print axioms Miao.NewKeynesian.sre_shiftSys
#print axioms Miao.NewKeynesian.sre_shiftSys_E
#print axioms Miao.NewKeynesian.sre_lagInv
#print axioms Miao.NewKeynesian.sre_lag
#print axioms Miao.NewKeynesian.sre_lagE
#print axioms Miao.NewKeynesian.sre_lagE_self
#print axioms Miao.NewKeynesian.sre_lagInv_zero
#print axioms Miao.NewKeynesian.sre_lagInv_lagInv
#print axioms Miao.NewKeynesian.sre_lag_lag
#print axioms Miao.NewKeynesian.sre_lag_form
#print axioms Miao.NewKeynesian.sre_iter
#print axioms Miao.NewKeynesian.sre_bubble_bounded_zero
#print axioms Miao.NewKeynesian.sre_unique_of_bounded
#print axioms Miao.NewKeynesian.sre_fwd
#print axioms Miao.NewKeynesian.sre_inv_abs_lt_one
#print axioms Miao.NewKeynesian.sre_fwd_term_le
#print axioms Miao.NewKeynesian.sre_fwd_summable
#print axioms Miao.NewKeynesian.sre_fwd_bound
#print axioms Miao.NewKeynesian.sre_fwd_isBounded
#print axioms Miao.NewKeynesian.sre_fwd_adapted
#print axioms Miao.NewKeynesian.sre_fwd_rec
#print axioms Miao.NewKeynesian.eq_2_3
#print axioms Miao.NewKeynesian.eq_2_3_unique
#print axioms Miao.NewKeynesian.eq_2_4_of_particular
#print axioms Miao.NewKeynesian.eq_2_4
#print axioms Miao.NewKeynesian.eq_2_4_every
#print axioms Miao.NewKeynesian.sre_Transversality
#print axioms Miao.NewKeynesian.eq_2_5_of_bounded
#print axioms Miao.NewKeynesian.sre_bubble_tvc_zero
#print axioms Miao.NewKeynesian.eq_2_5_bubble_fails
#print axioms Miao.NewKeynesian.sre_unique_of_tvc
#print axioms Miao.NewKeynesian.eq_2_5_rules_out_bubbles
#print axioms Miao.NewKeynesian.sre_fwd_ar1
#print axioms Miao.NewKeynesian.example_2_2_1_Ed
#print axioms Miao.NewKeynesian.example_2_2_1_fundamental
#print axioms Miao.NewKeynesian.example_2_2_1_general
#print axioms Miao.NewKeynesian.sre_bounded_of_rec
#print axioms Miao.NewKeynesian.sre_smul_isBounded
#print axioms Miao.NewKeynesian.sre_smul_isAdapted
#print axioms Miao.NewKeynesian.sre_IsSol26
#print axioms Miao.NewKeynesian.sre_second
#print axioms Miao.NewKeynesian.eq_2_9
#print axioms Miao.NewKeynesian.sre_second_adapted
#print axioms Miao.NewKeynesian.eq_2_6_solution
#print axioms Miao.NewKeynesian.eq_2_6_unique
#print axioms Miao.NewKeynesian.sre_IsSol210
#print axioms Miao.NewKeynesian.eq_2_10_reduce
#print axioms Miao.NewKeynesian.sre_force210
#print axioms Miao.NewKeynesian.sre_force210_adapted
#print axioms Miao.NewKeynesian.sre_force210_bounded
#print axioms Miao.NewKeynesian.sre_sol210
#print axioms Miao.NewKeynesian.sre_sol210_adapted
#print axioms Miao.NewKeynesian.sre_sol210_E
#print axioms Miao.NewKeynesian.eq_2_10_solution
#print axioms Miao.NewKeynesian.eq_2_10_unique
#print axioms Miao.NewKeynesian.sre_sunspot
#print axioms Miao.NewKeynesian.eq_2_10_indeterminate
#print axioms Miao.NewKeynesian.sre_uc
#print axioms Miao.NewKeynesian.sre_uc_adapted
#print axioms Miao.NewKeynesian.uc_iff
#print axioms Miao.NewKeynesian.uc_sufficient
#print axioms Miao.NewKeynesian.uc_necessary
#print axioms Miao.NewKeynesian.uc_denominator_ne_zero
#print axioms Miao.NewKeynesian.uc_stable_root
#print axioms Miao.NewKeynesian.uc_eq_lag_solution
#print axioms Miao.NewKeynesian.example_2_2_1_coin
#print axioms Miao.NewKeynesian.example_2_2_1_bubble
#print axioms Miao.NewKeynesian.example_2_2_1_bubble_L1
#print axioms Miao.NewKeynesian.bkS_matAct_sub
#print axioms Miao.NewKeynesian.bkS_matAct_neg
#print axioms Miao.NewKeynesian.bkS_matAct_zero
#print axioms Miao.NewKeynesian.bkS_matAct_zero_left
#print axioms Miao.NewKeynesian.bkS_matAct_smul
#print axioms Miao.NewKeynesian.bkS_matAct_sum
#print axioms Miao.NewKeynesian.bkS_matAct_add_left
#print axioms Miao.NewKeynesian.bkS_matAct_sub_left
#print axioms Miao.NewKeynesian.bkS_matAct_pow_succ
#print axioms Miao.NewKeynesian.bkS_matCLM
#print axioms Miao.NewKeynesian.bkS_matCLM_apply
#print axioms Miao.NewKeynesian.bkS_matAct_hasSum
#print axioms Miao.NewKeynesian.bkS_matAct_real
#print axioms Miao.NewKeynesian.bkS_norm_matAct_le
#print axioms Miao.NewKeynesian.bkS_matAct_bound
#print axioms Miao.NewKeynesian.bkS_geom_decay
#print axioms Miao.NewKeynesian.bkS_ECLM
#print axioms Miao.NewKeynesian.bkS_ECLM_apply
#print axioms Miao.NewKeynesian.bkS_Evec_hasSum
#print axioms Miao.NewKeynesian.bkS_Evec_add
#print axioms Miao.NewKeynesian.bkS_Evec_sub
#print axioms Miao.NewKeynesian.bkS_Evec_neg
#print axioms Miao.NewKeynesian.bkS_Evec_zero
#print axioms Miao.NewKeynesian.bkS_Evec_smul
#print axioms Miao.NewKeynesian.bkS_Evec_sumElim
#print axioms Miao.NewKeynesian.bkS_Evec_tower_le
#print axioms Miao.NewKeynesian.bkS_Evec_tower_ge
#print axioms Miao.NewKeynesian.bkS_Evec_idem
#print axioms Miao.NewKeynesian.bkS_Evec_of_le
#print axioms Miao.NewKeynesian.bkS_norm_Evec_le
#print axioms Miao.NewKeynesian.bkS_isAdaptedV_iff
#print axioms Miao.NewKeynesian.bkS_isStableProc_iff
#print axioms Miao.NewKeynesian.bkS_stable_Evec
#print axioms Miao.NewKeynesian.bkS_stable_shift
#print axioms Miao.NewKeynesian.bkS_stable_matAct
#print axioms Miao.NewKeynesian.bkS_stable_add
#print axioms Miao.NewKeynesian.bkS_summable_geom
#print axioms Miao.NewKeynesian.bkS_fwd
#print axioms Miao.NewKeynesian.eq_2_12
#print axioms Miao.NewKeynesian.bkS_fwd_adapted
#print axioms Miao.NewKeynesian.bkS_fwd_bound
#print axioms Miao.NewKeynesian.bkS_fwd_rec
#print axioms Miao.NewKeynesian.bkS_fwd_unique
#print axioms Miao.NewKeynesian.bkS_jump_unique
#print axioms Miao.NewKeynesian.eq_2_11_iff
#print axioms Miao.NewKeynesian.bkS_regular_of_det
#print axioms Miao.NewKeynesian.bkS_add_comp
#print axioms Miao.NewKeynesian.bkS_sub_comp
#print axioms Miao.NewKeynesian.bkS_Evec_comp
#print axioms Miao.NewKeynesian.bkS_comp_inl
#print axioms Miao.NewKeynesian.bkS_comp_inr
#print axioms Miao.NewKeynesian.bkS_blockDiag_inl
#print axioms Miao.NewKeynesian.bkS_blockDiag_inr
#print axioms Miao.NewKeynesian.bkS_split_inl
#print axioms Miao.NewKeynesian.bkS_split_inr
#print axioms Miao.NewKeynesian.bkS_norm_comp_inl_le
#print axioms Miao.NewKeynesian.bkS_norm_comp_inr_le
#print axioms Miao.NewKeynesian.bkS_norm_sum_type_le
#print axioms Miao.NewKeynesian.bkS_sumElim_eta
#print axioms Miao.NewKeynesian.bkS_backward_eq
#print axioms Miao.NewKeynesian.bkS_bounded_backward
#print axioms Miao.NewKeynesian.bkS_IsStableSol
#print axioms Miao.NewKeynesian.bkS_u_rec
#print axioms Miao.NewKeynesian.bkS_u_eq_fwd
#print axioms Miao.NewKeynesian.bkS_policy
#print axioms Miao.NewKeynesian.bkS_unique
#print axioms Miao.NewKeynesian.bkS_exists
#print axioms Miao.NewKeynesian.theorem_1_4_2_stoch
#print axioms Miao.NewKeynesian.bkS_k0_adapted
#print axioms Miao.NewKeynesian.bkS_trivial
#print axioms Miao.NewKeynesian.bkS_Evec_trivial
#print axioms Miao.NewKeynesian.certainty_equivalence
#print axioms Miao.NewKeynesian.certainty_equivalence_fwd
#print axioms Miao.NewKeynesian.theorem_1_4_2_of_stoch
#print axioms Miao.NewKeynesian.bkS_Evec_ar
#print axioms Miao.NewKeynesian.certainty_equivalence_ar
#print axioms Miao.NewKeynesian.certainty_equivalence_ar_det
#print axioms Miao.NewKeynesian.bkS_fwd_zero
#print axioms Miao.NewKeynesian.bkS_homog_u_zero
#print axioms Miao.NewKeynesian.theorem_1_4_3_gt_stoch
#print axioms Miao.NewKeynesian.theorem_1_4_3_lt_stoch
#print axioms Miao.NewKeynesian.theorem_1_4_3_lt_exists_stoch
#print axioms Miao.NewKeynesian.bkS_shift
#print axioms Miao.NewKeynesian.corollary_1_4_1_stoch
#print axioms Miao.NewKeynesian.nkA
#print axioms Miao.NewKeynesian.nkB
#print axioms Miao.NewKeynesian.nkC
#print axioms Miao.NewKeynesian.nkAinv
#print axioms Miao.NewKeynesian.nkSaddleW
#print axioms Miao.NewKeynesian.nkW
#print axioms Miao.NewKeynesian.nkG
#print axioms Miao.NewKeynesian.nkState
#print axioms Miao.NewKeynesian.nkShock
#print axioms Miao.NewKeynesian.nk_sumElim_eq_iff
#print axioms Miao.NewKeynesian.nk_matAct_A
#print axioms Miao.NewKeynesian.nk_matAct_B
#print axioms Miao.NewKeynesian.nk_matAct_C
#print axioms Miao.NewKeynesian.eq_2_16
#print axioms Miao.NewKeynesian.nkA_mul_inv
#print axioms Miao.NewKeynesian.eq_2_16_W
#print axioms Miao.NewKeynesian.nkSaddleP
#print axioms Miao.NewKeynesian.nkSaddleR
#print axioms Miao.NewKeynesian.nk_tri_stable
#print axioms Miao.NewKeynesian.nk_scalar_eig
#print axioms Miao.NewKeynesian.nk_saddle_split
#print axioms Miao.NewKeynesian.nk_saddle_eig
#print axioms Miao.NewKeynesian.nk_saddle_eig_l1
#print axioms Miao.NewKeynesian.nk_saddle_unstable
#print axioms Miao.NewKeynesian.nkTr
#print axioms Miao.NewKeynesian.nkLam1
#print axioms Miao.NewKeynesian.nkLam2
#print axioms Miao.NewKeynesian.nk_lam
#print axioms Miao.NewKeynesian.example_2_3_1_split
#print axioms Miao.NewKeynesian.example_2_3_1_eigen
#print axioms Miao.NewKeynesian.example_2_3_1_indeterminate
#print axioms Miao.NewKeynesian.example_2_3_1_indeterminate_det
#print axioms Miao.NewKeynesian.nkBothOut
#print axioms Miao.NewKeynesian.nk_eig2
#print axioms Miao.NewKeynesian.nk_out_of_bothOut
#print axioms Miao.NewKeynesian.nk_root_of_not_bothOut
#print axioms Miao.NewKeynesian.nk_eigvec2
#print axioms Miao.NewKeynesian.nk_jump2_unique
#print axioms Miao.NewKeynesian.nk_jump2_nonunique
#print axioms Miao.NewKeynesian.nkWT
#print axioms Miao.NewKeynesian.nkTaylorEqm
#print axioms Miao.NewKeynesian.nkDeterminate
#print axioms Miao.NewKeynesian.nk_taylor_iff
#print axioms Miao.NewKeynesian.nk_bothOut_WT
#print axioms Miao.NewKeynesian.nk_WT_trace
#print axioms Miao.NewKeynesian.ex_2_2_suff
#print axioms Miao.NewKeynesian.ex_2_2_nec
#print axioms Miao.NewKeynesian.ex_2_2_b_exact
#print axioms Miao.NewKeynesian.ex_2_2_b
#print axioms Miao.NewKeynesian.ex_2_2_a
#print axioms Miao.NewKeynesian.ex_2_2_a_taylor_principle
#print axioms Miao.NewKeynesian.ex_2_2_a_printed_false
#print axioms Miao.NewKeynesian.cp_sumElim_dotProduct
#print axioms Miao.NewKeynesian.cp_dotProduct_mulVec_comm
#print axioms Miao.NewKeynesian.cp_dotProduct_mulVec_symm
#print axioms Miao.NewKeynesian.cpLoss
#print axioms Miao.NewKeynesian.cpW
#print axioms Miao.NewKeynesian.cpDbar
#print axioms Miao.NewKeynesian.cpAbar
#print axioms Miao.NewKeynesian.eq_9_19_W
#print axioms Miao.NewKeynesian.cp_augmented
#print axioms Miao.NewKeynesian.cpLagrangian
#print axioms Miao.NewKeynesian.cpPerturb
#print axioms Miao.NewKeynesian.cpInit
#print axioms Miao.NewKeynesian.cpGrad
#print axioms Miao.NewKeynesian.cp_lagr_term
#print axioms Miao.NewKeynesian.cp_lagrangian_perturb
#print axioms Miao.NewKeynesian.cp_hasDerivAt
#print axioms Miao.NewKeynesian.eq_foc_9_4
#print axioms Miao.NewKeynesian.cp_init_eq_Dbar
#print axioms Miao.NewKeynesian.cp_grad_eq
#print axioms Miao.NewKeynesian.cpLeft
#print axioms Miao.NewKeynesian.cpRight
#print axioms Miao.NewKeynesian.eq_9_22
#print axioms Miao.NewKeynesian.ex941D
#print axioms Miao.NewKeynesian.ex941A
#print axioms Miao.NewKeynesian.ex941B
#print axioms Miao.NewKeynesian.ex941C
#print axioms Miao.NewKeynesian.example_9_4_1
#print axioms Miao.NewKeynesian.example_9_4_1_rn
#print axioms Miao.NewKeynesian.ex941Q
#print axioms Miao.NewKeynesian.example_9_4_1_loss
#print axioms Miao.NewKeynesian.cpPert
#print axioms Miao.NewKeynesian.cp_pert_zero
#print axioms Miao.NewKeynesian.cp_sum_delta
#print axioms Miao.NewKeynesian.cp_sum_delta_sq
#print axioms Miao.NewKeynesian.cp_sum_delta_succ
#print axioms Miao.NewKeynesian.cp_hasDerivAt_quad
#print axioms Miao.NewKeynesian.cp_stationary_iff
#print axioms Miao.NewKeynesian.ex942Lagr
#print axioms Miao.NewKeynesian.eq_9_25
#print axioms Miao.NewKeynesian.eq_9_26
#print axioms Miao.NewKeynesian.eq_9_27
#print axioms Miao.NewKeynesian.ex942L
#print axioms Miao.NewKeynesian.ex942R
#print axioms Miao.NewKeynesian.example_9_4_2_system
#print axioms Miao.NewKeynesian.ex942Lprinted
#print axioms Miao.NewKeynesian.example_9_4_2_printed_row_false
#print axioms Miao.NewKeynesian.eq_9_28
#print axioms Miao.NewKeynesian.ex942b
#print axioms Miao.NewKeynesian.ex942a
#print axioms Miao.NewKeynesian.ex942_b_eq
#print axioms Miao.NewKeynesian.eq_9_29
#print axioms Miao.NewKeynesian.eq_9_29_kappa_zero
#print axioms Miao.NewKeynesian.ex942_lag_sum
#print axioms Miao.NewKeynesian.ex942Rule
#print axioms Miao.NewKeynesian.ex942_rule_solves
#print axioms Miao.NewKeynesian.ex942_rule_expected
#print axioms Miao.NewKeynesian.ex942_unique_bounded
#print axioms Miao.NewKeynesian.ex942_solution
#print axioms Miao.NewKeynesian.ex942_muz
#print axioms Miao.NewKeynesian.ex942_time_inconsistent
#print axioms Miao.NewKeynesian.ex951θ
#print axioms Miao.NewKeynesian.ex951θ_pos
#print axioms Miao.NewKeynesian.ex951θ_le_one
#print axioms Miao.NewKeynesian.eq_9_43
#print axioms Miao.NewKeynesian.IsMPE951
#print axioms Miao.NewKeynesian.ex951pi
#print axioms Miao.NewKeynesian.ex951_denoms
#print axioms Miao.NewKeynesian.example_9_5_1
#print axioms Miao.NewKeynesian.example_9_5_1_unique
#print axioms Miao.NewKeynesian.ex951_series
#print axioms Miao.NewKeynesian.ex951_forward
#print axioms Miao.NewKeynesian.cp_commitment_vs_discretion
#print axioms Miao.NewKeynesian.nk_u
#print axioms Miao.NewKeynesian.nk_hasDerivAt_pow_div
#print axioms Miao.NewKeynesian.nk_u_C
#print axioms Miao.NewKeynesian.nk_u_N
#print axioms Miao.NewKeynesian.nk_u_m
#print axioms Miao.NewKeynesian.nk_u_CC
#print axioms Miao.NewKeynesian.nk_u_NN
#print axioms Miao.NewKeynesian.nk_u_mm
#print axioms Miao.NewKeynesian.nk_u_signs
#print axioms Miao.NewKeynesian.nk_u_no_satiation
#print axioms Miao.NewKeynesian.eq_19_2
#print axioms Miao.NewKeynesian.eq_19_3
#print axioms Miao.NewKeynesian.eq_19_4
#print axioms Miao.NewKeynesian.nk_money_supply
#print axioms Miao.NewKeynesian.nk_money_demand_pos_rate
#print axioms Miao.NewKeynesian.nk_aggY
#print axioms Miao.NewKeynesian.nk_priceIndex
#print axioms Miao.NewKeynesian.eq_19_6_foc
#print axioms Miao.NewKeynesian.nk_integral_rpow_pos
#print axioms Miao.NewKeynesian.nk_priceIndex_rpow
#print axioms Miao.NewKeynesian.nk_priceIndex_pos
#print axioms Miao.NewKeynesian.nk_demand_rpow
#print axioms Miao.NewKeynesian.nk_demand_agg
#print axioms Miao.NewKeynesian.nk_demand_cost
#print axioms Miao.NewKeynesian.eq_19_7
#print axioms Miao.NewKeynesian.nk_rpow_tangent
#print axioms Miao.NewKeynesian.eq_19_6
#print axioms Miao.NewKeynesian.nk_labor_req
#print axioms Miao.NewKeynesian.nk_TC
#print axioms Miao.NewKeynesian.nk_MCavg
#print axioms Miao.NewKeynesian.nk_MC_deriv
#print axioms Miao.NewKeynesian.nk_MC_lagrange
#print axioms Miao.NewKeynesian.nk_MC_ratio
#print axioms Miao.NewKeynesian.eq_19_10
#print axioms Miao.NewKeynesian.nk_MC_antitone
#print axioms Miao.NewKeynesian.nk_calvo_term_deriv
#print axioms Miao.NewKeynesian.nk_calvo_foc
#print axioms Miao.NewKeynesian.eq_19_11
#print axioms Miao.NewKeynesian.eq_19_12
#print axioms Miao.NewKeynesian.nk_calvo_avg
#print axioms Miao.NewKeynesian.eq_19_13
#print axioms Miao.NewKeynesian.nk_dispersion
#print axioms Miao.NewKeynesian.eq_19_15
#print axioms Miao.NewKeynesian.eq_19_16
#print axioms Miao.NewKeynesian.eq_19_17
#print axioms Miao.NewKeynesian.nk_taylorRule
#print axioms Miao.NewKeynesian.nk_reset_constant
#print axioms Miao.NewKeynesian.nk_steady_state
#print axioms Miao.NewKeynesian.nk_flex_reset
#print axioms Miao.NewKeynesian.nk_flex_symmetric
#print axioms Miao.NewKeynesian.nk_flex_wage
#print axioms Miao.NewKeynesian.eq_19_18
#print axioms Miao.NewKeynesian.nk_path_deriv
#print axioms Miao.NewKeynesian.nk_rpow_path
#print axioms Miao.NewKeynesian.eq_19_19
#print axioms Miao.NewKeynesian.nk_b
#print axioms Miao.NewKeynesian.eq_19_21
#print axioms Miao.NewKeynesian.nk_loglin_reset_terms
#print axioms Miao.NewKeynesian.nk_loglin_19_2
#print axioms Miao.NewKeynesian.nk_loglin_MC
#print axioms Miao.NewKeynesian.nk_loglin_19_16
#print axioms Miao.NewKeynesian.nk_loglin_19_17
#print axioms Miao.NewKeynesian.nk_loglin_dispersion
#print axioms Miao.NewKeynesian.nk_dispersion_zero
#print axioms Miao.NewKeynesian.nk_loglin_output
#print axioms Miao.NewKeynesian.nk_loglin_19_18
#print axioms Miao.NewKeynesian.nk_loglin_euler
#print axioms Miao.NewKeynesian.eq_19_26
#print axioms Miao.NewKeynesian.nk_loglin_natural_rate
#print axioms Miao.NewKeynesian.eq_19_29
#print axioms Miao.NewKeynesian.nk_pv
#print axioms Miao.NewKeynesian.nk_summable_geom
#print axioms Miao.NewKeynesian.nk_tsum_geom_smul
#print axioms Miao.NewKeynesian.nk_pv_rec
#print axioms Miao.NewKeynesian.eq_19_20
#print axioms Miao.NewKeynesian.nk_reset_plugged
#print axioms Miao.NewKeynesian.nk_reset_recursive
#print axioms Miao.NewKeynesian.nk_q_recursive
#print axioms Miao.NewKeynesian.nk_pc_mc
#print axioms Miao.NewKeynesian.eq_19_23
#print axioms Miao.NewKeynesian.nk_mc_gap
#print axioms Miao.NewKeynesian.nk_kappa
#print axioms Miao.NewKeynesian.eq_19_25
#print axioms Miao.NewKeynesian.nk_kappa_pos
#print axioms Miao.NewKeynesian.eq_19_24
#print axioms Miao.NewKeynesian.eq_19_27
#print axioms Miao.NewKeynesian.eq_19_28
#print axioms Miao.NewKeynesian.nk_dnkSystem
#print axioms Miao.NewKeynesian.nk_dnkDeterminate
#print axioms Miao.NewKeynesian.nk_dnk_iff
#print axioms Miao.NewKeynesian.nk_pair_stable
#print axioms Miao.NewKeynesian.nk_pair_adapted
#print axioms Miao.NewKeynesian.nk_rule_regular
#print axioms Miao.NewKeynesian.ex_19_1_suff
#print axioms Miao.NewKeynesian.ex_19_1_nec
#print axioms Miao.NewKeynesian.ex_19_1_exact
#print axioms Miao.NewKeynesian.ex_19_1
#print axioms Miao.NewKeynesian.ex_19_1_structural
#print axioms Miao.NewKeynesian.ex_19_1_not_necessary
#print axioms Miao.NewKeynesian.nk_irfLam
#print axioms Miao.NewKeynesian.nk_irfLam_pos
#print axioms Miao.NewKeynesian.nk_irf_solves
#print axioms Miao.NewKeynesian.nk_fig_19_1
#print axioms Miao.NewKeynesian.nk_fig_19_2
#print axioms Miao.NewKeynesian.mpCES
#print axioms Miao.NewKeynesian.mp_q_bounds
#print axioms Miao.NewKeynesian.mp_firm_term
#print axioms Miao.NewKeynesian.mp_ces_const
#print axioms Miao.NewKeynesian.mp_integrable_rpow
#print axioms Miao.NewKeynesian.mp_ces_le
#print axioms Miao.NewKeynesian.mp_ces_symmetric
#print axioms Miao.NewKeynesian.mp_ces_lt
#print axioms Miao.NewKeynesian.mpU
#print axioms Miao.NewKeynesian.mp_hasDerivAt_uC
#print axioms Miao.NewKeynesian.mp_hasDerivAt_uN
#print axioms Miao.NewKeynesian.mp_hasDerivAt_mpn
#print axioms Miao.NewKeynesian.mp_planner_foc
#print axioms Miao.NewKeynesian.mpYout
#print axioms Miao.NewKeynesian.mp_mrs_iff_log
#print axioms Miao.NewKeynesian.mp_mrs_output
#print axioms Miao.NewKeynesian.mp_subsidy
#print axioms Miao.NewKeynesian.mp_subsidy_household
#print axioms Miao.NewKeynesian.mp_flex_subsidy_efficient
#print axioms Miao.NewKeynesian.mp_distortion
#print axioms Miao.NewKeynesian.mp_yf_loglinear
#print axioms Miao.NewKeynesian.mpXstar
#print axioms Miao.NewKeynesian.mp_xstar_first_order
#print axioms Miao.NewKeynesian.mp_labor_log
#print axioms Miao.NewKeynesian.mp_labor_dev
#print axioms Miao.NewKeynesian.mpG
#print axioms Miao.NewKeynesian.mpH
#print axioms Miao.NewKeynesian.mpHd
#print axioms Miao.NewKeynesian.mpK
#print axioms Miao.NewKeynesian.mpTheta
#print axioms Miao.NewKeynesian.mp_dispersion_recursion
#print axioms Miao.NewKeynesian.mp_dispersion_delta
#print axioms Miao.NewKeynesian.mp_peano2
#print axioms Miao.NewKeynesian.mp_G_zero
#print axioms Miao.NewKeynesian.mp_dispersion_zero_inflation
#print axioms Miao.NewKeynesian.mp_hasDerivAt_G
#print axioms Miao.NewKeynesian.mp_G_pos_near
#print axioms Miao.NewKeynesian.mp_h_zero
#print axioms Miao.NewKeynesian.mp_hd_zero
#print axioms Miao.NewKeynesian.mp_hasDerivAt_h
#print axioms Miao.NewKeynesian.mp_hasDerivAt_hd
#print axioms Miao.NewKeynesian.mp_h_expansion
#print axioms Miao.NewKeynesian.mp_dispersion_second_order
#print axioms Miao.NewKeynesian.mp_log_dev
#print axioms Miao.NewKeynesian.mp_K_Theta
#print axioms Miao.NewKeynesian.mp_disp_bounded
#print axioms Miao.NewKeynesian.mp_dispersion_sum
#print axioms Miao.NewKeynesian.mp_taylor_exp
#print axioms Miao.NewKeynesian.mp_uCC
#print axioms Miao.NewKeynesian.mp_uNN
#print axioms Miao.NewKeynesian.mp_eq_19_30_truncation
#print axioms Miao.NewKeynesian.mp_util_exact
#print axioms Miao.NewKeynesian.mp_exp_quad_bound
#print axioms Miao.NewKeynesian.eq_19_30
#print axioms Miao.NewKeynesian.eq_19_30_littleO
#print axioms Miao.NewKeynesian.mp_step2_subst
#print axioms Miao.NewKeynesian.mp_step2_phi
#print axioms Miao.NewKeynesian.mp_step2_small
#print axioms Miao.NewKeynesian.mpLambdaBar
#print axioms Miao.NewKeynesian.mpTip
#print axioms Miao.NewKeynesian.mp_step2_square
#print axioms Miao.NewKeynesian.mpOmega
#print axioms Miao.NewKeynesian.mpLam
#print axioms Miao.NewKeynesian.mp_omega_pos
#print axioms Miao.NewKeynesian.mp_lam_pos
#print axioms Miao.NewKeynesian.mp_step3
#print axioms Miao.NewKeynesian.mp_xstar_zero_iff
#print axioms Miao.NewKeynesian.mp_strict_targeting
#print axioms Miao.NewKeynesian.mp_strict_targeting_pi_zero
#print axioms Miao.NewKeynesian.mp_strict_targeting_rate
#print axioms Miao.NewKeynesian.mp_cost_push_tradeoff
#print axioms Miao.NewKeynesian.eq_19_33
#print axioms Miao.NewKeynesian.eq_19_34
#print axioms Miao.NewKeynesian.mp_commit_rule
#print axioms Miao.NewKeynesian.mp_beta_rule
#print axioms Miao.NewKeynesian.mp_root_identity
#print axioms Miao.NewKeynesian.mp_commit_x_law
#print axioms Miao.NewKeynesian.mp_commit_pi_law
#print axioms Miao.NewKeynesian.mp_commit_initial
#print axioms Miao.NewKeynesian.mp_price_level
#print axioms Miao.NewKeynesian.mp_price_level_printed_false
#print axioms Miao.NewKeynesian.mp_price_level_stationary
#print axioms Miao.NewKeynesian.eq_19_35
#print axioms Miao.NewKeynesian.mp_timeless_euler
#print axioms Miao.NewKeynesian.mp_timeless_coeff
#print axioms Miao.NewKeynesian.mp_timeless_solves
#print axioms Miao.NewKeynesian.mp_timeless_unique
#print axioms Miao.NewKeynesian.mp_timeless_pi
#print axioms Miao.NewKeynesian.mp_commit_pi0
#print axioms Miao.NewKeynesian.mp_timeless_vs_commitment
#print axioms Miao.NewKeynesian.mp_ex951pi_closed
#print axioms Miao.NewKeynesian.mp_discretion_inflation
#print axioms Miao.NewKeynesian.mp_discretion_printed_false
#print axioms Miao.NewKeynesian.mp_inflation_bias
#print axioms Miao.NewKeynesian.mp_a_lt_theta
#print axioms Miao.NewKeynesian.mp_discretion_above_commitment
#print axioms Miao.NewKeynesian.mp_gap_algebra
#print axioms Miao.NewKeynesian.mp_discretion_gap_impact
#print axioms Miao.NewKeynesian.mp_fig_19_3_commitment
#print axioms Miao.NewKeynesian.mp_fig_19_3_discretion
#print axioms Miao.NewKeynesian.mpRuleEqm
#print axioms Miao.NewKeynesian.mp_rule_eqm_iff
#print axioms Miao.NewKeynesian.mp_rule_eqm_rn_iff
#print axioms Miao.NewKeynesian.mp_zero_eqm_iff
#print axioms Miao.NewKeynesian.mpImplements
#print axioms Miao.NewKeynesian.eq_19_31
#print axioms Miao.NewKeynesian.ex_19_2
#print axioms Miao.NewKeynesian.mp_printed_rule_fails
#print axioms Miao.NewKeynesian.mpDetSystem
#print axioms Miao.NewKeynesian.mp_printed_rule_counterexample
#print axioms Miao.NewKeynesian.mp_ex_19_2_instance
#print axioms Miao.NewKeynesian.fs_vtilde
#print axioms Miao.NewKeynesian.fs_etaU
#print axioms Miao.NewKeynesian.fs_etaV
#print axioms Miao.NewKeynesian.fs_Gamma
#print axioms Miao.NewKeynesian.fs_Gamma_pos
#print axioms Miao.NewKeynesian.fs_Gamma_lt_one
#print axioms Miao.NewKeynesian.fs_vtilde_hasDerivAt
#print axioms Miao.NewKeynesian.fs_vtilde_deriv2
#print axioms Miao.NewKeynesian.fs_vtilde_deriv2_pos
#print axioms Miao.NewKeynesian.eq_19_40
#print axioms Miao.NewKeynesian.fs_multiplier_formula
#print axioms Miao.NewKeynesian.eq_19_41
#print axioms Miao.NewKeynesian.fs_markup_foc
#print axioms Miao.NewKeynesian.eq_19_42
#print axioms Miao.NewKeynesian.eq_19_43
#print axioms Miao.NewKeynesian.fs_endogenous_wedge
#print axioms Miao.NewKeynesian.fs_eq_19_41_vpp_neg
#print axioms Miao.NewKeynesian.fs_Bdd
#print axioms Miao.NewKeynesian.eq_19_44
#print axioms Miao.NewKeynesian.fs_constant_real_rate
#print axioms Miao.NewKeynesian.fs_costmin_foc
#print axioms Miao.NewKeynesian.fs_ratio_strictMonoOn
#print axioms Miao.NewKeynesian.fs_common_ratio
#print axioms Miao.NewKeynesian.fs_ratio_eq_hours
#print axioms Miao.NewKeynesian.eq_19_46
#print axioms Miao.NewKeynesian.eq_19_47
#print axioms Miao.NewKeynesian.fs_reset_recursive
#print axioms Miao.NewKeynesian.fs_q_recursive
#print axioms Miao.NewKeynesian.fs_nkpc
#print axioms Miao.NewKeynesian.fs_mc_loglin
#print axioms Miao.NewKeynesian.fs_forward_hasSum
#print axioms Miao.NewKeynesian.fs_forward_exists
#print axioms Miao.NewKeynesian.fs_kappa_pos
#print axioms Miao.NewKeynesian.eq_19_48
#print axioms Miao.NewKeynesian.fs_euler_loglin
#print axioms Miao.NewKeynesian.eq_19_50
#print axioms Miao.NewKeynesian.fs_psi
#print axioms Miao.NewKeynesian.fs_gammaY
#print axioms Miao.NewKeynesian.fs_psi_pos
#print axioms Miao.NewKeynesian.fs_gammaY_pos
#print axioms Miao.NewKeynesian.fs_gammaY_lt_one
#print axioms Miao.NewKeynesian.fs_gammaY_lt_Gamma_iff
#print axioms Miao.NewKeynesian.fs_TaylorEqm
#print axioms Miao.NewKeynesian.eq_19_52
#print axioms Miao.NewKeynesian.eq_19_53
#print axioms Miao.NewKeynesian.fs_zlb_no_steady_state
#print axioms Miao.NewKeynesian.fs_h
#print axioms Miao.NewKeynesian.fs_thetaR
#print axioms Miao.NewKeynesian.fs_thetaG
#print axioms Miao.NewKeynesian.fs_h_strictAntiOn
#print axioms Miao.NewKeynesian.fs_mubar_exists
#print axioms Miao.NewKeynesian.eq_19_55_iff
#print axioms Miao.NewKeynesian.eq_19_55_fails_at_mubar
#print axioms Miao.NewKeynesian.eq_19_56
#print axioms Miao.NewKeynesian.eq_19_57
#print axioms Miao.NewKeynesian.eq_19_58
#print axioms Miao.NewKeynesian.eq_19_59
#print axioms Miao.NewKeynesian.fs_thetaG_zero
#print axioms Miao.NewKeynesian.eq_19_60
#print axioms Miao.NewKeynesian.fs_Gc
#print axioms Miao.NewKeynesian.eq_19_54_branches
#print axioms Miao.NewKeynesian.fs_Gc_pos_iff
#print axioms Miao.NewKeynesian.fs_taylor_branch
#print axioms Miao.NewKeynesian.fs_thetaG_strictMonoOn
#print axioms Miao.NewKeynesian.fs_thetaR_strictMonoOn
#print axioms Miao.NewKeynesian.fs_thetaG_tendsto_atTop
#print axioms Miao.NewKeynesian.fs_thetaR_tendsto_atTop
#print axioms Miao.NewKeynesian.fs_fig_19_4_Gc
#print axioms Miao.NewKeynesian.fs_zlbSys
#print axioms Miao.NewKeynesian.fs_zlb_sum_form
#print axioms Miao.NewKeynesian.fs_trivE
#print axioms Miao.NewKeynesian.fs_zlbM
#print axioms Miao.NewKeynesian.fs_zlb_hom_iff
#print axioms Miao.NewKeynesian.fs_zlbM_tr_det
#print axioms Miao.NewKeynesian.ex_19_3
#print axioms Miao.NewKeynesian.ex_19_3_solution
#print axioms Miao.NewKeynesian.fs_thetaPi
#print axioms Miao.NewKeynesian.fs_thetaC
#print axioms Miao.NewKeynesian.fs_mult61
#print axioms Miao.NewKeynesian.ex_19_4_transitional
#print axioms Miao.NewKeynesian.fs_crisis_three_state
#print axioms Miao.NewKeynesian.fs_thetaPi_pos
#print axioms Miao.NewKeynesian.fs_thetaC_eq_printed
#print axioms Miao.NewKeynesian.fs_thetaPi_printed
#print axioms Miao.NewKeynesian.fs_thetaPi_printed_ne
#print axioms Miao.NewKeynesian.eq_19_61
#print axioms Miao.NewKeynesian.ex_19_4
#print axioms Miao.NewKeynesian.fs_eq_19_61_last_neg
#print axioms Miao.NewKeynesian.fs_eq_19_61_lt_thetaG
#print axioms Miao.NewKeynesian.fs_eq_19_61_lambda_zero
#print axioms Miao.NewKeynesian.fs_fig_19_4_gammaY
#print axioms Miao.NewKeynesian.fs_fig_19_6_lambda_zero
#print axioms Miao.NewKeynesian.fs_fig_19_6_point_eight
#print axioms Miao.NewKeynesian.fs_fig_19_6_point_nine_one
#print axioms Miao.NewKeynesian.eq_19_63
#print axioms Miao.NewKeynesian.fs_welfare_deriv
#print axioms Miao.NewKeynesian.fs_welfare_deriv_neoclassical
#print axioms Miao.NewKeynesian.fs_welfare_no_g
#print axioms Miao.NewKeynesian.fs_loss
#print axioms Miao.NewKeynesian.fs_first_best
#print axioms Miao.NewKeynesian.eq_19_65
#print axioms Miao.NewKeynesian.fs_xi
#print axioms Miao.NewKeynesian.fs_loss_reduced
#print axioms Miao.NewKeynesian.fs_optimal_GL
#print axioms Miao.NewKeynesian.fs_optimal_GL_unique
#print axioms Miao.NewKeynesian.fs_optimal_GL_pos
#print axioms Miao.NewKeynesian.fs_zero_gap_GL
#print axioms Miao.NewKeynesian.fs_zero_gap_printed
#print axioms Miao.NewKeynesian.fs_optimal_GL_lt_zero_gap
#print axioms Miao.NewKeynesian.fs_weights_pos
#print axioms Miao.NewKeynesian.fs_fig_19_7
#print axioms Miao.NewKeynesian.fs_taylor2
#print axioms Miao.NewKeynesian.ex_19_5_flex
#print axioms Miao.NewKeynesian.fs_disp
#print axioms Miao.NewKeynesian.fs_dispersion_lin
#print axioms Miao.NewKeynesian.ex_19_5_dispersion
#print axioms Miao.NewKeynesian.fs_labor_dispersion
#print axioms Miao.NewKeynesian.fs_dispersion_sum
#print axioms Miao.NewKeynesian.ex_19_5
