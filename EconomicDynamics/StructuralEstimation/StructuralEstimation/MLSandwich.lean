/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Sandwich covariance matrices and the optimal weighting matrix

Matrix algebra behind the asymptotic variances of §12.3 (Miao, pp. 402 and 406–407): for a
`q × k` Jacobian `B`, a long-run covariance `Ω` and a symmetric weighting matrix `W`, the GMM-type
estimator has the sandwich variance
`V(W) = (BᵀWB)⁻¹ BᵀWΩWB (BᵀWB)⁻¹` (`ml_sandwich`).

* `ml_sandwich_inv`: for `W = (aΩ)⁻¹`, `a ≠ 0`, the sandwich collapses to `(BᵀΩ⁻¹B)⁻¹`.
* `ml_sandwich_optimal`: `V(W) − (BᵀΩ⁻¹B)⁻¹` is positive semidefinite for every symmetric `W`
  with `BᵀWB` invertible, so `W ∝ Ω⁻¹` is optimal. Proof: with `H = (BᵀWB)⁻¹BᵀW` and
  `G = (BᵀΩ⁻¹B)⁻¹BᵀΩ⁻¹`, `V(W) − (BᵀΩ⁻¹B)⁻¹ = (H − G) Ω (H − G)ᵀ`.

These are the specific algebraic facts §12.3 needs from the GMM theory of §12.1 (proved here,
not imported).
-/

namespace Miao.StructuralEstimation

open Matrix

/-- The sandwich variance `(BᵀWB)⁻¹ BᵀWΩWB (BᵀWB)⁻¹`. -/
noncomputable def ml_sandwich {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (B : Matrix m n ℝ) (Ω W : Matrix m m ℝ) : Matrix n n ℝ :=
  (Bᵀ * W * B)⁻¹ * (Bᵀ * W * Ω * W * B) * (Bᵀ * W * B)⁻¹

/-- `(aΩ)⁻¹ = a⁻¹ Ω⁻¹` for `a ≠ 0` and invertible `Ω`. -/
theorem ml_inv_smul {m : Type*} [Fintype m] [DecidableEq m] (Ω : Matrix m m ℝ)
    (hΩ : IsUnit Ω.det) {a : ℝ} (ha : a ≠ 0) : (a • Ω)⁻¹ = a⁻¹ • Ω⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul,
    Matrix.nonsing_inv_mul _ hΩ]

/-- With `W = (aΩ)⁻¹` (`a ≠ 0`) the sandwich collapses: `V(W) = (BᵀΩ⁻¹B)⁻¹`. -/
theorem ml_sandwich_inv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℝ) (Ω : Matrix m m ℝ) (hΩ : IsUnit Ω.det)
    (hM : IsUnit (Bᵀ * Ω⁻¹ * B).det) {a : ℝ} (ha : a ≠ 0) :
    ml_sandwich B Ω (a • Ω)⁻¹ = (Bᵀ * Ω⁻¹ * B)⁻¹ := by
  set M := Bᵀ * Ω⁻¹ * B with hMdef
  have hA : Bᵀ * (a • Ω)⁻¹ * B = a⁻¹ • M := by
    rw [ml_inv_smul Ω hΩ ha, Matrix.mul_smul, Matrix.smul_mul]
  have hMid : Bᵀ * (a • Ω)⁻¹ * Ω * (a • Ω)⁻¹ * B = (a⁻¹ * a⁻¹) • M := by
    rw [ml_inv_smul Ω hΩ ha]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    rw [hMdef, Matrix.mul_assoc (Bᵀ * Ω⁻¹) Ω, Matrix.mul_nonsing_inv _ hΩ, Matrix.mul_one]
  have hAinv : (a⁻¹ • M)⁻¹ = a • M⁻¹ := by
    rw [ml_inv_smul M hM (inv_ne_zero ha), inv_inv]
  unfold ml_sandwich
  rw [hA, hMid, hAinv]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]
  have : a * (a⁻¹ * a⁻¹ * a) = 1 := by field_simp
  rw [this, one_smul]

/-- The optimal weighting matrix (Miao, pp. 402 and 407): for `Ω` positive semidefinite and
invertible and any symmetric `W` with `BᵀWB` invertible, `V(W) − (BᵀΩ⁻¹B)⁻¹` is positive
semidefinite; by `ml_sandwich_inv` the lower bound is attained at `W ∝ Ω⁻¹`. -/
theorem ml_sandwich_optimal {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (B : Matrix m n ℝ) (Ω W : Matrix m m ℝ) (hΩ : Ω.PosSemidef)
    (hΩu : IsUnit Ω.det) (hW : Wᵀ = W) (hA : IsUnit (Bᵀ * W * B).det)
    (hM : IsUnit (Bᵀ * Ω⁻¹ * B).det) :
    (ml_sandwich B Ω W - (Bᵀ * Ω⁻¹ * B)⁻¹).PosSemidef := by
  set A := Bᵀ * W * B with hAdef
  set M := Bᵀ * Ω⁻¹ * B with hMdef
  have hΩt : Ωᵀ = Ω := by
    have := hΩ.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hΩit : (Ω⁻¹)ᵀ = Ω⁻¹ := by rw [transpose_nonsing_inv, hΩt]
  have hAt : Aᵀ = A := by
    rw [hAdef, transpose_mul, transpose_mul, transpose_transpose, hW, Matrix.mul_assoc]
  have hMt : Mᵀ = M := by
    rw [hMdef, transpose_mul, transpose_mul, transpose_transpose, hΩit, Matrix.mul_assoc]
  have hAit : (A⁻¹)ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hAt]
  have hMit : (M⁻¹)ᵀ = M⁻¹ := by rw [transpose_nonsing_inv, hMt]
  set H := A⁻¹ * Bᵀ * W with hH
  set G := M⁻¹ * Bᵀ * Ω⁻¹ with hG
  have hHt : Hᵀ = W * B * A⁻¹ := by
    rw [hH, transpose_mul, transpose_mul, transpose_transpose, hW, hAit, Matrix.mul_assoc]
  have hGt : Gᵀ = Ω⁻¹ * B * M⁻¹ := by
    rw [hG, transpose_mul, transpose_mul, transpose_transpose, hΩit, hMit, Matrix.mul_assoc]
  have hΩΩ : Ω * Ω⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΩu
  have hΩΩ' : Ω⁻¹ * Ω = 1 := Matrix.nonsing_inv_mul _ hΩu
  have h1 : H * Ω * Hᵀ = ml_sandwich B Ω W := by
    rw [hHt, hH, ml_sandwich, ← hAdef]
    simp only [Matrix.mul_assoc]
  have h2 : H * Ω * Gᵀ = M⁻¹ := by
    rw [hGt, hH]
    calc A⁻¹ * Bᵀ * W * Ω * (Ω⁻¹ * B * M⁻¹)
        = A⁻¹ * (Bᵀ * W * (Ω * Ω⁻¹) * B) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ := by
        rw [hΩΩ, Matrix.mul_one, ← hAdef, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  have h3 : G * Ω * Hᵀ = M⁻¹ := by
    rw [hHt, hG]
    calc M⁻¹ * Bᵀ * Ω⁻¹ * Ω * (W * B * A⁻¹)
        = M⁻¹ * (Bᵀ * (Ω⁻¹ * Ω) * W * B) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ := by
        rw [hΩΩ', Matrix.mul_one, ← hAdef, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
          Matrix.mul_one]
  have h4 : G * Ω * Gᵀ = M⁻¹ := by
    rw [hGt, hG]
    calc M⁻¹ * Bᵀ * Ω⁻¹ * Ω * (Ω⁻¹ * B * M⁻¹)
        = M⁻¹ * (Bᵀ * (Ω⁻¹ * Ω) * Ω⁻¹ * B) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ := by
        rw [hΩΩ', Matrix.mul_one, ← hMdef, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]
  have key : (H - G) * Ω * (H - G)ᴴ = ml_sandwich B Ω W - M⁻¹ := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_sub, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_sub, h1, h2, h3, h4]
    abel
  rw [← key]
  exact hΩ.mul_mul_conjTranspose_same (H - G)

end Miao.StructuralEstimation
