/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul

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
