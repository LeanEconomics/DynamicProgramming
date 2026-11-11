/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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
