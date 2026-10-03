/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.PartialOrders
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear operators, positive operators and Markov operators

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.3.3 (pp. 75–80).

A linear operator on `ℝ^X` is a linear map `(X → ℝ) →ₗ[ℝ] (X → ℝ)`; every
matrix gives one by `u ↦ Au` and every linear operator comes from a matrix
(Theorem 2.3.4, Mathlib's `LinearMap.toMatrix'`). The kernel representation
(2.16), the product-space operator (2.17), positive operators (2.18) and
Markov operators are treated, with Lemma 2.3.6 and Exercises 2.3.8–2.3.14.
-/

open Finset Set Matrix

namespace SargentStachurski.OperatorsFixedPoints

variable {X : Type*} [Fintype X]

/-- Theorem 2.3.4 (p. 76), one direction: a matrix acts as a linear operator, (2.15). -/
theorem mulVec_linear (A : Matrix X X ℝ) (α β : ℝ) (u v : X → ℝ) :
    A *ᵥ (α • u + β • v) = α • (A *ᵥ u) + β • (A *ᵥ v) := by
  rw [mulVec_add, mulVec_smul, mulVec_smul]

/-- Theorem 2.3.4 (p. 76): every linear operator on `ℝⁿ` is given by a matrix, `Lu = Au`. -/
theorem exists_matrix_of_linear (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :
    ∃ A : Matrix X X ℝ, ∀ u, L u = A *ᵥ u := by
  classical
  exact ⟨LinearMap.toMatrix' L, fun u => by rw [LinearMap.toMatrix'_mulVec]⟩

/-- Lemma 2.3.5 (p. 77), (a) ↔ (b): matrices and linear operators on `ℝ^X` correspond
one-to-one. -/
noncomputable def matrixLinearEquiv [DecidableEq X] :
    Matrix X X ℝ ≃ₗ[ℝ] ((X → ℝ) →ₗ[ℝ] (X → ℝ)) :=
  Matrix.toLin'

theorem matrixLinearEquiv_apply [DecidableEq X] (A : Matrix X X ℝ) (u : X → ℝ) :
    matrixLinearEquiv A u = A *ᵥ u :=
  Matrix.toLin'_apply A u

/-- Lemma 2.3.5 (p. 77), (a) ↔ (d): matrices and functions `X × X → ℝ` correspond one-to-one. -/
def matrixFunEquiv : Matrix X X ℝ ≃ (X × X → ℝ) where
  toFun A p := A p.1 p.2
  invFun f := Matrix.of fun i j => f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The operator induced by a kernel `L : X × X → ℝ`, (2.16): `(Lu)(x) = ∑ L(x, x') u(x')`. -/
def kernelOp (L : X → X → ℝ) (u : X → ℝ) : X → ℝ := fun x => ∑ x', L x x' * u x'

/-- Exercise 2.3.8 (p. 77): the kernel operator is linear; indeed it is `u ↦ Lu` for the matrix
with entries `L(x, x')`. -/
theorem kernelOp_eq_mulVec (L : X → X → ℝ) (u : X → ℝ) : kernelOp L u = Matrix.of L *ᵥ u := rfl

theorem kernelOp_linear (L : X → X → ℝ) (α β : ℝ) (u v : X → ℝ) :
    kernelOp L (α • u + β • v) = α • kernelOp L u + β • kernelOp L v := by
  rw [kernelOp_eq_mulVec, kernelOp_eq_mulVec, kernelOp_eq_mulVec, mulVec_linear]

/-- The product-space operator (2.17): on `X = Y × Z`, `(Lu)(y, z) = ∑_{z'} u(y, z') Q(z, z')`. -/
def productOp {Y Z : Type*} [Fintype Z] (Q : Z → Z → ℝ) (u : Y × Z → ℝ) : Y × Z → ℝ :=
  fun p => ∑ z', u (p.1, z') * Q p.2 z'

/-- Exercise 2.3.9 (p. 78): the product-space operator is linear. -/
theorem productOp_linear {Y Z : Type*} [Fintype Z] (Q : Z → Z → ℝ) (α β : ℝ) (u v : Y × Z → ℝ) :
    productOp Q (α • u + β • v) = α • productOp Q u + β • productOp Q v := by
  funext p
  simp only [productOp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
    mul_assoc, ← mul_sum]

/-! ### Positive operators and Markov operators (§2.3.3.4) -/

/-- A linear operator is positive (2.18), p. 79, if it maps the positive cone `ℝ^X₊` into itself. -/
def IsPositiveOp (L : (X → ℝ) → (X → ℝ)) : Prop := ∀ u : X → ℝ, 0 ≤ u → 0 ≤ L u

/-- Example 2.3.1 (p. 79): the product-space operator is positive when `Q ≥ 0`. -/
theorem isPositiveOp_productOp {Y Z : Type*} [Fintype Z] {Q : Z → Z → ℝ} (hQ : ∀ z z', 0 ≤ Q z z') :
    IsPositiveOp (productOp Q (Y := Y)) := fun _ hu p =>
  sum_nonneg fun z' _ => mul_nonneg (hu (p.1, z')) (hQ p.2 z')

/-- Lemma 2.3.6 (p. 79) and Exercise 2.3.10: `u ↦ Au` is positive iff `A ≥ 0`. -/
theorem isPositiveOp_mulVec_iff (A : Matrix X X ℝ) :
    IsPositiveOp (fun u => A *ᵥ u) ↔ ∀ i j, 0 ≤ A i j := by
  classical
  constructor
  · intro h i j
    -- test against the indicator of `j`
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simp
      · simp [hk]) i
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  · intro h u hu i
    exact sum_nonneg fun j _ => mul_nonneg (h i j) (hu j)

omit [Fintype X] in
/-- Exercise 2.3.11 (p. 79): a linear operator is positive iff it is order preserving. -/
theorem isPositiveOp_iff_monotone (L : (X → ℝ) →ₗ[ℝ] (X → ℝ)) :
    IsPositiveOp L ↔ Monotone L := by
  constructor
  · intro h u v huv
    have := h (v - u) (fun x => by simpa using huv x)
    rw [map_sub] at this
    intro x
    have := this x
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    linarith
  · intro h u hu
    have := h hu
    rwa [map_zero] at this

/-- A Markov operator (p. 79): positive and fixing the constant function `1`. -/
def IsMarkovOp (L : (X → ℝ) → (X → ℝ)) : Prop := IsPositiveOp L ∧ L (fun _ => 1) = fun _ => 1

/-- Exercise 2.3.12 (p. 80): `u ↦ Pu` is a Markov operator iff `P ≥ 0` and every row sums to one. -/
theorem isMarkovOp_mulVec_iff (P : Matrix X X ℝ) :
    IsMarkovOp (fun u => P *ᵥ u) ↔ (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1 := by
  rw [IsMarkovOp, isPositiveOp_mulVec_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    have := congrFun h2 i
    simpa [mulVec, dotProduct] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, funext fun i => ?_⟩
    simpa [mulVec, dotProduct] using h2 i

/-- Exercise 2.3.13 (p. 80): a Markov matrix maps everywhere-positive vectors to
everywhere-positive vectors. -/
theorem mulVec_pos_of_markov {P : Matrix X X ℝ} (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    {v : X → ℝ} (hv : ∀ j, 0 < v j) (i : X) : 0 < (P *ᵥ v) i := by
  simp only [mulVec, dotProduct]
  have hne : ∃ j, 0 < P i j := by
    by_contra hcon
    have hz : ∀ j, P i j = 0 := fun j => le_antisymm (le_of_not_gt fun h => hcon ⟨j, h⟩) (hP i j)
    have := hrow i
    simp [hz] at this
  obtain ⟨j₀, hj₀⟩ := hne
  exact sum_pos' (fun j _ => mul_nonneg (hP i j) (hv j).le)
    ⟨j₀, mem_univ _, mul_pos hj₀ (hv j₀)⟩

/-- The row-vector action `φ ↦ φP`, (2.19): `(φP)(x') = ∑ P(x, x') φ(x)`. -/
def vecMulOp (P : Matrix X X ℝ) (φ : X → ℝ) : X → ℝ := fun x' => ∑ x, P x x' * φ x

theorem vecMulOp_eq_vecMul (P : Matrix X X ℝ) (φ : X → ℝ) : vecMulOp P φ = φ ᵥ* P := by
  funext x'
  simp only [vecMulOp, vecMul, dotProduct, mul_comm]

/-- Exercise 2.3.14 (p. 80): `u ↦ Pu` is a Markov operator iff `φ ↦ φP` maps distributions to
distributions. -/
theorem isMarkovOp_iff_vecMulOp_distribution (P : Matrix X X ℝ) :
    IsMarkovOp (fun u => P *ᵥ u) ↔
      ∀ φ : X → ℝ, (∀ x, 0 ≤ φ x) → ∑ x, φ x = 1 →
        (∀ x', 0 ≤ vecMulOp P φ x') ∧ ∑ x', vecMulOp P φ x' = 1 := by
  classical
  rw [isMarkovOp_mulVec_iff]
  constructor
  · rintro ⟨hP, hrow⟩ φ hφ hsum
    refine ⟨fun x' => sum_nonneg fun x _ => mul_nonneg (hP x x') (hφ x), ?_⟩
    simp only [vecMulOp]
    rw [sum_comm]
    simp only [← sum_mul, hrow, one_mul, hsum]
  · intro h
    -- test against point masses
    have hpoint : ∀ x, (∀ x', 0 ≤ vecMulOp P (Pi.single x 1) x') ∧
        ∑ x', vecMulOp P (Pi.single x 1) x' = 1 := fun x =>
      h _ (fun k => by
        by_cases hk : k = x
        · subst hk; simp
        · simp [hk]) (by simp)
    refine ⟨fun x x' => ?_, fun x => ?_⟩
    · have := (hpoint x).1 x'
      simpa [vecMulOp, Pi.single_apply] using this
    · have := (hpoint x).2
      simpa [vecMulOp, Pi.single_apply] using this

end SargentStachurski.OperatorsFixedPoints
