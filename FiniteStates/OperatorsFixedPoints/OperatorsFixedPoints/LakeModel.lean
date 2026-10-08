/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.SpectralRadius
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The lake model

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.3.2 (pp. 71–75).

Workers exit the labour market at rate `d`, enter at rate `b` (initially
unemployed), separate at rate `α` and find jobs at rate `λ`, all in `(0, 1)`.
The unemployed and employed stocks `xₜ = (uₜ, eₜ)` follow `xₜ₊₁ = A xₜ` with the
matrix (2.13). Exercise 2.3.4: the workforce grows at `g = b − d`; Exercise
2.3.5: `ρ(A) = 1 + g`, because every column of `A ≥ 0` sums to `1 + g`;
Exercise 2.3.6: `1ᵀ` is a left eigenvector; Exercise 2.3.7: the right
eigenvector normalised by `1ᵀx̄ = 1` is (2.14). The long-run approximation
`Aᵗx₀ ≈ (1 + g)ᵗ n₀ x̄` rests on the convergence (2.11) of the
Perron–Frobenius theorem for positive matrices, which is not claimed here.
-/

open Matrix Finset

namespace SargentStachurski.OperatorsFixedPoints

/-- The lake model's rates, all in `(0, 1)` (p. 72). `lam` is the book's `λ`. -/
structure LakeModel where
  d : ℝ
  b : ℝ
  α : ℝ
  lam : ℝ
  d_pos : 0 < d
  d_lt_one : d < 1
  b_pos : 0 < b
  b_lt_one : b < 1
  α_pos : 0 < α
  α_lt_one : α < 1
  lam_pos : 0 < lam
  lam_lt_one : lam < 1

namespace LakeModel

variable (m : LakeModel)

/-- The transition matrix `A` of (2.13), acting on `x = (u, e)`. -/
noncomputable def A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - m.d) * (1 - m.lam) + m.b, (1 - m.d) * m.α + m.b;
     (1 - m.d) * m.lam, (1 - m.d) * (1 - m.α)]

/-- The growth rate of the workforce, `g = b − d` (p. 73). -/
def g : ℝ := m.b - m.d

theorem one_sub_d_pos : 0 < 1 - m.d := by linarith [m.d_lt_one]

theorem one_add_g_pos : 0 < 1 + m.g := by
  unfold g
  linarith [m.b_pos, m.d_lt_one]

/-- `A ≥ 0`. -/
theorem A_nonneg (i j : Fin 2) : 0 ≤ m.A i j := by
  have h1 := m.one_sub_d_pos
  have h2 := m.b_pos
  have h3 := m.α_pos
  have h4 := m.lam_pos
  have h5 := m.α_lt_one
  have h6 := m.lam_lt_one
  fin_cases i <;> fin_cases j <;> simp [A] <;> nlinarith

/-- Exercise 2.3.4 (p. 73): `nₜ₊₁ = (1 + g) nₜ`, since `uₜ₊₁ + eₜ₊₁ = (1 + g)(uₜ + eₜ)`. -/
theorem sum_mulVec (x : Fin 2 → ℝ) : (m.A *ᵥ x) 0 + (m.A *ᵥ x) 1 = (1 + m.g) * (x 0 + x 1) := by
  simp [A, mulVec, dotProduct, Fin.sum_univ_two, g]
  ring

/-- Every column of `A` sums to `1 + g`. -/
theorem colsum (j : Fin 2) : ∑ i, m.A i j = 1 + m.g := by
  fin_cases j <;> simp [A, Fin.sum_univ_two, g] <;> ring

/-- Exercise 2.3.5 (p. 73): `ρ(A) = 1 + g`. -/
theorem specRad_A : specRad m.A = 1 + m.g :=
  specRad_eq_of_colsum_eq m.A m.A_nonneg m.one_add_g_pos.le m.colsum

/-- Exercise 2.3.6 (p. 73): `1ᵀ = (1, 1)` is a left eigenvector of `A` for the eigenvalue
`1 + g`. -/
theorem one_vecMul : (fun _ => (1 : ℝ)) ᵥ* m.A = (1 + m.g) • fun _ => (1 : ℝ) := by
  funext j
  simp only [vecMul, dotProduct, one_mul, Pi.smul_apply, smul_eq_mul, mul_one]
  exact m.colsum j

/-- The long-run unemployment rate `ū` of (2.14), p. 74. -/
noncomputable def ubar : ℝ :=
  (1 + m.g - (1 - m.d) * (1 - m.α)) / (1 + m.g - (1 - m.d) * (1 - m.α) + (1 - m.d) * m.lam)

/-- The dominant right eigenvector `x̄ = (ū, ē)` with `ē = 1 − ū`, (2.14). -/
noncomputable def xbar : Fin 2 → ℝ := ![m.ubar, 1 - m.ubar]

theorem numer_eq : 1 + m.g - (1 - m.d) * (1 - m.α) = m.b + (1 - m.d) * m.α := by
  unfold g
  ring

theorem denom_pos : 0 < 1 + m.g - (1 - m.d) * (1 - m.α) + (1 - m.d) * m.lam := by
  rw [numer_eq]
  have := m.one_sub_d_pos
  have := m.b_pos
  have := m.α_pos
  have := m.lam_pos
  positivity

theorem xbar_sum : m.xbar 0 + m.xbar 1 = 1 := by
  simp [xbar]

/-- Exercise 2.3.7 (p. 73): `x̄` is a right eigenvector for `1 + g`. -/
theorem A_mulVec_xbar : m.A *ᵥ m.xbar = (1 + m.g) • m.xbar := by
  have hD := m.denom_pos
  have hub : m.ubar * (1 + m.g - (1 - m.d) * (1 - m.α) + (1 - m.d) * m.lam) =
      1 + m.g - (1 - m.d) * (1 - m.α) := by
    unfold ubar
    rw [div_mul_cancel₀ _ hD.ne']
  funext i
  fin_cases i <;> simp [A, xbar, mulVec, dotProduct, Fin.sum_univ_two, g] at hub ⊢ <;>
    nlinarith [hub]

/-- Exercise 2.3.7 (p. 73): `x̄` is the unique right eigenvector for `1 + g` with `1ᵀx = 1`. -/
theorem eq_xbar_of_eigen {x : Fin 2 → ℝ} (hx : m.A *ᵥ x = (1 + m.g) • x) (hsum : x 0 + x 1 = 1) :
    x = m.xbar := by
  have hD := m.denom_pos
  -- the first row gives `((1 − d)α + b) x₁ = (1 − d)λ x₀`; with `x₀ + x₁ = 1` this pins `x₀`
  have h0 : ((1 - m.d) * (1 - m.lam) + m.b) * x 0 + ((1 - m.d) * m.α + m.b) * x 1 =
      (1 + (m.b - m.d)) * x 0 := by
    have := congrFun hx 0
    simpa [A, mulVec, dotProduct, Fin.sum_univ_two, g] using this
  have hx0 : x 0 = m.ubar := by
    unfold ubar
    rw [eq_div_iff hD.ne', numer_eq]
    have hx1 : x 1 = 1 - x 0 := by linarith
    rw [hx1] at h0
    nlinarith [h0]
  funext i
  fin_cases i
  · simpa [xbar] using hx0
  · simp [xbar]
    linarith

end LakeModel

end SargentStachurski.OperatorsFixedPoints
