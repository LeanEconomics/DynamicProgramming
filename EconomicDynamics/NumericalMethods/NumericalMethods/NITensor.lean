/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import NumericalMethods.NIInterpolation

/-!
# Multidimensional approximation: tensor products (Miao, §11.3.3, pp. 364–366)

On `I = ∏ᵢ [aᵢ, bᵢ]` with univariate bases `φᵢⱼ` and nodes `xᵢⱼ` (`j = 1, …, nᵢ`), the tensor basis
is `φ_{j₁⋯j_d}(x) = ∏ᵢ φᵢⱼᵢ(xᵢ)`; evaluated on the tensor grid of nodes its interpolation matrix is
the tensor (Kronecker) product `Φ = Φ_d ⊗ ⋯ ⊗ Φ₁` of the univariate matrices.

* `ni_tensorMatrix Φ`: the `d`-fold tensor product, indexed by multi-indices;
  `ni_tensor_interpMatrix`: it is the interpolation matrix of the tensor basis on the tensor grid.
* `ni_tensorMatrix_mul`, `ni_tensorMatrix_one`: `(⊗Aᵢ)(⊗Bᵢ) = ⊗(AᵢBᵢ)`, `⊗1 = 1`.
* `ni_tensor_inverse`, `ni_tensor_coeff`: if every `Φᵢ` is invertible then
  `Φ⁻¹ = ⊗Φᵢ⁻¹` and `c = (Φ_d⁻¹ ⊗ ⋯ ⊗ Φ₁⁻¹) y` is the unique solution of `Φc = y`.
* `ni_tensor_card`: the tensor grid has `n = ∏ᵢ nᵢ` points, so `mᵈ` when every `nᵢ = m` (the
  curse of dimensionality).
* `ni_tensor_example_*`: the Miranda–Fackler example (`n₁ = 3`, `n₂ = 2`, monomial bases,
  nodes `{0, 1, 2}` and `{0, 1}`): the basis vector, the stacked nodes `X` and the `6 × 6`
  matrix `Φ = Φ₂ ⊗ Φ₁`.

Complete polynomial bases are only recommended by reference to Judd (1998) and are not
formalised; Smolyak grids are not discussed in the book.
-/

open Matrix

namespace Miao.NumericalMethods

/-- The tensor product `⊗ᵢ Φᵢ` of square matrices, indexed by multi-indices:
`(⊗Φᵢ)_{r c} = ∏ᵢ (Φᵢ)_{rᵢ cᵢ}`. -/
def ni_tensorMatrix {d : ℕ} {m : Fin d → ℕ} (Φ : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) :
    Matrix (∀ i, Fin (m i)) (∀ i, Fin (m i)) ℝ :=
  Matrix.of fun r c => ∏ i, Φ i (r i) (c i)

/-- The tensor basis `φ_{j₁⋯j_d}(x₁, …, x_d) = ∏ᵢ φᵢⱼᵢ(xᵢ)` (Miao, p. 364). -/
def ni_tensorBasis {d : ℕ} {m : Fin d → ℕ} (φ : ∀ i, Fin (m i) → ℝ → ℝ) (j : ∀ i, Fin (m i))
    (x : Fin d → ℝ) : ℝ :=
  ∏ i, φ i (j i) (x i)

/-- Miao, p. 365: evaluated on the tensor grid of nodes `(x₁ᵣ₁, …, x_dᵣ_d)`, the interpolation
matrix of the tensor basis is the tensor product of the univariate interpolation matrices
`Φᵢ = [φᵢⱼ(xᵢₖ)]`. -/
theorem ni_tensor_interpMatrix {d : ℕ} {m : Fin d → ℕ} (φ : ∀ i, Fin (m i) → ℝ → ℝ)
    (x : ∀ i, Fin (m i) → ℝ) (r c : ∀ i, Fin (m i)) :
    ni_tensorBasis φ c (fun i => x i (r i)) =
      ni_tensorMatrix (fun i => ni_interpMatrix (φ i) (x i)) r c := by
  simp [ni_tensorBasis, ni_tensorMatrix, ni_interpMatrix]

/-- `(⊗Aᵢ)(⊗Bᵢ) = ⊗(AᵢBᵢ)` (mixed-product property). -/
theorem ni_tensorMatrix_mul {d : ℕ} {m : Fin d → ℕ}
    (A B : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ) :
    ni_tensorMatrix A * ni_tensorMatrix B = ni_tensorMatrix (fun i => A i * B i) := by
  ext r c
  simp only [ni_tensorMatrix, mul_apply, of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

/-- `⊗1 = 1`. -/
theorem ni_tensorMatrix_one {d : ℕ} {m : Fin d → ℕ} :
    ni_tensorMatrix (fun i => (1 : Matrix (Fin (m i)) (Fin (m i)) ℝ)) = 1 := by
  ext r c
  simp only [ni_tensorMatrix, of_apply, one_apply]
  by_cases h : r = c
  · subst h
    simp
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ c i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Miao, p. 365: if every `Φᵢ` is invertible then `Φ = ⊗Φᵢ` is invertible with
`Φ⁻¹ = Φ_d⁻¹ ⊗ ⋯ ⊗ Φ₁⁻¹`. -/
theorem ni_tensor_inverse {d : ℕ} {m : Fin d → ℕ} (Φ : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (h : ∀ i, IsUnit (Φ i).det) :
    (ni_tensorMatrix Φ)⁻¹ = ni_tensorMatrix (fun i => (Φ i)⁻¹) ∧
      ni_tensorMatrix Φ * ni_tensorMatrix (fun i => (Φ i)⁻¹) = 1 := by
  have h1 : ni_tensorMatrix (fun i => (Φ i)⁻¹) * ni_tensorMatrix Φ = 1 := by
    rw [ni_tensorMatrix_mul]
    simp_rw [Matrix.nonsing_inv_mul _ (h _)]
    exact ni_tensorMatrix_one
  have h2 : ni_tensorMatrix Φ * ni_tensorMatrix (fun i => (Φ i)⁻¹) = 1 := by
    rw [ni_tensorMatrix_mul]
    simp_rw [Matrix.mul_nonsing_inv _ (h _)]
    exact ni_tensorMatrix_one
  exact ⟨Matrix.inv_eq_left_inv h1, h2⟩

/-- Miao, p. 365: if every `Φᵢ` is invertible, `c = (Φ_d⁻¹ ⊗ ⋯ ⊗ Φ₁⁻¹) y` is the unique solution
of the interpolation equation `Φc = y`. -/
theorem ni_tensor_coeff {d : ℕ} {m : Fin d → ℕ} (Φ : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℝ)
    (h : ∀ i, IsUnit (Φ i).det) (y : (∀ i, Fin (m i)) → ℝ) :
    ∃! c, ni_tensorMatrix Φ *ᵥ c = y ∧ c = ni_tensorMatrix (fun i => (Φ i)⁻¹) *ᵥ y := by
  obtain ⟨-, hmul⟩ := ni_tensor_inverse Φ h
  refine ⟨ni_tensorMatrix (fun i => (Φ i)⁻¹) *ᵥ y, ⟨?_, rfl⟩, fun c hc => hc.2⟩
  rw [mulVec_mulVec, hmul, one_mulVec]

/-- Miao, p. 364: the tensor grid has `n = ∏ᵢ nᵢ` points; with `nᵢ = m` for all `i` this is
`mᵈ`, which grows exponentially in the dimension (the curse of dimensionality, p. 366). -/
theorem ni_tensor_card {d : ℕ} (m : Fin d → ℕ) :
    Fintype.card (∀ i, Fin (m i)) = ∏ i, m i ∧
      ∀ M : ℕ, (∀ i, m i = M) → Fintype.card (∀ i, Fin (m i)) = M ^ d := by
  refine ⟨by simp, fun M hM => ?_⟩
  simp [hM]

/-- Miao, p. 365: the univariate monomial basis matrix on the nodes `{0, 1, 2}`. -/
theorem ni_tensor_example_Φ₁ :
    ni_interpMatrix (ni_monomial (n := 3)) ![0, 1, 2] = !![1, 0, 0; 1, 1, 1; 1, 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ni_interpMatrix, ni_monomial]

/-- Miao, p. 366: the univariate monomial basis matrix on the nodes `{0, 1}`. -/
theorem ni_tensor_example_Φ₂ :
    ni_interpMatrix (ni_monomial (n := 2)) ![0, 1] = !![1, 0; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ni_interpMatrix, ni_monomial]

/-- Miao, p. 365: the full basis `[1 x₂] ⊗ [1 x₁ x₁²] = [1 x₁ x₁² x₂ x₁x₂ x₁²x₂]`. -/
theorem ni_tensor_example_basis (x₁ x₂ : ℝ) :
    (fun r : Fin 6 => (fun ab : Fin 2 × Fin 3 => ![1, x₂] ab.1 * ![1, x₁, x₁ ^ 2] ab.2)
      (finProdFinEquiv.symm r)) = ![1, x₁, x₁ ^ 2, x₂, x₁ * x₂, x₁ ^ 2 * x₂] := by
  funext r
  fin_cases r <;> simp [finProdFinEquiv, Fin.divNat, Fin.modNat] <;> ring

/-- Miao, p. 366: the stacked nodes `X` (row `r` is the grid point `zᵣ = (x₁, x₂)`). -/
theorem ni_tensor_example_X :
    (Matrix.of fun (r : Fin 6) (c : Fin 2) =>
      ![![(0 : ℝ), 1, 2] ((finProdFinEquiv (m := 2) (n := 3)).symm r).2,
        ![(0 : ℝ), 1] ((finProdFinEquiv (m := 2) (n := 3)).symm r).1] c)
      = !![0, 0; 1, 0; 2, 0; 0, 1; 1, 1; 2, 1] := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [finProdFinEquiv, Fin.divNat, Fin.modNat]

/-- Miao, p. 366: `Φ = Φ₂ ⊗ Φ₁` is the displayed `6 × 6` matrix. -/
theorem ni_tensor_example_Φ :
    (kroneckerMap (· * ·) (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ)
        (!![1, 0, 0; 1, 1, 1; 1, 2, 4] : Matrix (Fin 3) (Fin 3) ℝ)).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm =
      !![1, 0, 0, 0, 0, 0;
         1, 1, 1, 0, 0, 0;
         1, 2, 4, 0, 0, 0;
         1, 0, 0, 1, 0, 0;
         1, 1, 1, 1, 1, 1;
         1, 2, 4, 1, 2, 4] := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [finProdFinEquiv, kroneckerMap, Fin.divNat, Fin.modNat]

/-- Miao, p. 366: the example's interpolation matrix is invertible, so the coefficients are
`c = (Φ₂⁻¹ ⊗ Φ₁⁻¹) y`. -/
theorem ni_tensor_example_invertible :
    IsUnit (!![1, 0, 0; 1, 1, 1; 1, 2, 4] : Matrix (Fin 3) (Fin 3) ℝ).det ∧
      IsUnit (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  refine ⟨?_, ?_⟩ <;> rw [isUnit_iff_ne_zero] <;> norm_num [det_fin_three, det_fin_two]

end Miao.NumericalMethods
