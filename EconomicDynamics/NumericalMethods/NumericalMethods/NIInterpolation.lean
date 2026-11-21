/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NumericalMethods.NIWeighted

/-!
# The interpolation problem (Miao, §11.3, pp. 354–356)

The interpolant `f̂(x) = ∑ⱼ cⱼ φⱼ(x)` with basis functions `φⱼ`, the interpolation equation
`Φ c = y` with `Φᵢⱼ = φⱼ(xᵢ)`, the least-squares (regression) coefficients
`c = (Φ'Φ)⁻¹ Φ'y` when there are more nodes than coefficients, and the monomial basis of
§11.3.1.

* `ni_interp_eq_iff`: `f̂(xᵢ) = yᵢ` for all `i` iff `Φ c = y`.
* `ni_leastSquares_optimal`: `c = (Φ'Φ)⁻¹Φ'y` minimises `∑ᵢ (yᵢ − ∑ⱼ cⱼ φⱼ(xᵢ))²`.
* `ni_leastSquares_eq_interp`: when `m = n` and `Φ` is invertible, the least-squares
  coefficients solve the interpolation equation exactly.
* `ni_monomial_interp_unique`: for the monomial basis the interpolation matrix is the
  Vandermonde matrix; it is invertible iff the nodes are distinct, and then the interpolating
  coefficients exist and are unique; `ni_poly_interp_unique` is the polynomial (Lagrange) form.
* `ni_monomials_not_orthogonal`: the monomial basis is not mutually orthogonal with respect to
  any weighting function on a nondegenerate bounded interval (Miao, p. 356).

The claim that the Vandermonde matrix is "ill-conditioned" is qualitative and is not formalised.
-/

open Matrix MeasureTheory

namespace Miao.NumericalMethods

/-- The interpolant `f̂(x) = ∑ⱼ cⱼ φⱼ(x)` (Miao, p. 354). -/
def ni_fhat {n : ℕ} (φ : Fin n → ℝ → ℝ) (c : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ j, c j * φ j x

/-- The interpolation matrix `Φᵢⱼ = φⱼ(xᵢ)` (Miao, p. 355). -/
def ni_interpMatrix {m n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin m → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => φ j (x i)

/-- Miao, p. 355 (the interpolation equation): `∑ⱼ cⱼ φⱼ(xᵢ) = yᵢ` for all `i` iff `Φ c = y`. -/
theorem ni_interp_eq_iff {m n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin m → ℝ) (c : Fin n → ℝ)
    (y : Fin m → ℝ) : (∀ i, ni_fhat φ c (x i) = y i) ↔ ni_interpMatrix φ x *ᵥ c = y := by
  constructor
  · intro h
    funext i
    rw [← h i]
    simp [ni_fhat, ni_interpMatrix, mulVec, dotProduct, mul_comm]
  · intro h i
    rw [← h]
    simp [ni_fhat, ni_interpMatrix, mulVec, dotProduct, mul_comm]

/-- The sum of squared residuals `∑ᵢ (yᵢ − (Φc)ᵢ)²` of the regression method (Miao, p. 355). -/
def ni_ssr {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, (y i - (Φ *ᵥ c) i) ^ 2

/-- The normal equations: `Φ'(y − Φc) = 0` for `c = (Φ'Φ)⁻¹Φ'y` (Miao, p. 355). -/
theorem ni_normal_equations {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (h : IsUnit (Φᵀ * Φ).det) : Φᵀ *ᵥ (y - Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y))) = 0 := by
  rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, Matrix.mul_nonsing_inv _ h, one_mulVec,
    sub_self]

/-- Miao, p. 355 (least squares): when `Φ'Φ` is invertible, `c = (Φ'Φ)⁻¹Φ'y` minimises
`∑ᵢ (f(xᵢ) − ∑ⱼ cⱼ φⱼ(xᵢ))²`. -/
theorem ni_leastSquares_optimal {m n : ℕ} (Φ : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ)
    (h : IsUnit (Φᵀ * Φ).det) (c : Fin n → ℝ) :
    ni_ssr Φ y ((Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y)) ≤ ni_ssr Φ y c := by
  set cs := (Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y)
  set r := y - Φ *ᵥ cs
  set d := Φ *ᵥ (cs - c)
  have hnorm := ni_normal_equations Φ y h
  have hrd : r ⬝ᵥ d = 0 := by
    simp only [d, dotProduct_mulVec, ← mulVec_transpose]
    rw [hnorm, zero_dotProduct]
  have hsplit : ∀ i, y i - (Φ *ᵥ c) i = r i + d i := by
    intro i
    simp only [r, d, mulVec_sub, Pi.sub_apply]
    ring
  have h1 : ni_ssr Φ y c = ni_ssr Φ y cs + 2 * (r ⬝ᵥ d) + ∑ i, d i ^ 2 := by
    unfold ni_ssr
    simp only [hsplit, dotProduct]
    have : ∀ i, y i - (Φ *ᵥ cs) i = r i := fun i => rfl
    simp only [this, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h1, hrd]
  have : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

/-- Miao, p. 356: when `m = n` and `Φ` is invertible, the least-squares coefficients
`(Φ'Φ)⁻¹Φ'y` solve the interpolation equation `Φc = y`, i.e. regression is equivalent to the
interpolation equation. -/
theorem ni_leastSquares_eq_interp {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (h : IsUnit Φ.det) :
    (Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y) = Φ⁻¹ *ᵥ y ∧ Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ (Φᵀ *ᵥ y)) = y := by
  have ht : IsUnit Φᵀ.det := by rwa [det_transpose]
  have e : (Φᵀ * Φ)⁻¹ * Φᵀ = Φ⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · rw [mulVec_mulVec, e]
  · rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, e, Matrix.mul_nonsing_inv _ h,
      one_mulVec]

/-- The monomial basis `φⱼ(x) = x^(j−1)` (Miao, p. 356; indices from `0` here). -/
def ni_monomial {n : ℕ} (j : Fin n) (x : ℝ) : ℝ := x ^ (j : ℕ)

/-- Miao, p. 356: with the monomial basis the interpolation matrix is the Vandermonde matrix
`Φ = [1 xᵢ ⋯ xᵢⁿ⁻¹]`. -/
theorem ni_monomial_interpMatrix {n : ℕ} (x : Fin n → ℝ) :
    ni_interpMatrix ni_monomial x = Matrix.vandermonde x := by
  ext i j
  simp [ni_interpMatrix, ni_monomial, Matrix.vandermonde_apply]

/-- Miao, pp. 355–356 (monomial interpolation): the Vandermonde interpolation matrix is invertible
iff the nodes are distinct, and then for all data `y` there is exactly one coefficient vector
with `f̂(xᵢ) = yᵢ`. -/
theorem ni_monomial_interp_unique {n : ℕ} (x : Fin n → ℝ) :
    (ni_interpMatrix ni_monomial x).det ≠ 0 ↔ Function.Injective x := by
  rw [ni_monomial_interpMatrix]
  exact det_vandermonde_ne_zero_iff

/-- Miao, pp. 355–356: at distinct nodes the monomial interpolation equation has exactly one
solution. -/
theorem ni_monomial_interp_existsUnique {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (y : Fin n → ℝ) : ∃! c : Fin n → ℝ, ∀ i, ni_fhat ni_monomial c (x i) = y i := by
  set Φ := ni_interpMatrix ni_monomial x
  have hdet : IsUnit Φ.det := isUnit_iff_ne_zero.mpr ((ni_monomial_interp_unique x).mpr hx)
  refine ⟨Φ⁻¹ *ᵥ y, ?_, ?_⟩
  · change ∀ i, ni_fhat ni_monomial (Φ⁻¹ *ᵥ y) (x i) = y i
    rw [ni_interp_eq_iff, mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  · intro c hc
    rw [ni_interp_eq_iff] at hc
    rw [← hc, mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]

/-- Miao, pp. 355–356 (polynomial interpolation, Lagrange form): at `n` distinct nodes there is
exactly one polynomial of degree `< n` taking prescribed values, namely the Lagrange
interpolant. -/
theorem ni_poly_interp_unique {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (y : Fin n → ℝ) :
    ∃! p : Polynomial ℝ, p.degree < n ∧ ∀ i, p.eval (x i) = y i := by
  classical
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin n)) := fun a _ b _ h => hx h
  refine ⟨Lagrange.interpolate Finset.univ x y, ⟨?_, fun i => ?_⟩, ?_⟩
  · simpa using Lagrange.degree_interpolate_lt (r := y) hinj
  · exact Lagrange.eval_interpolate_at_node y hinj (Finset.mem_univ i)
  · rintro q ⟨hq, hqy⟩
    refine Polynomial.eq_of_degrees_lt_of_eval_finset_eq (s := Finset.univ.image x) ?_ ?_ ?_
    · rwa [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
    · rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin]
      simpa using Lagrange.degree_interpolate_lt (r := y) hinj
    · intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      rw [hqy i, Lagrange.eval_interpolate_at_node y hinj (Finset.mem_univ i)]

/-- Miao, p. 356: the monomial basis functions are not mutually orthogonal for any weighting
function on a nondegenerate bounded interval: `⟨x⁰, x²⟩_w = ∫ x² w > 0`. -/
theorem ni_monomials_not_orthogonal {w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hw : ni_IsWeightingFunction w (Set.Ioo a b)) :
    0 < ni_inner w (Set.Ioo a b) (fun x => x ^ 0) (fun x => x ^ 2) := by
  unfold ni_inner
  have hint : IntegrableOn (fun x : ℝ => x ^ 0 * x ^ 2 * w x) (Set.Ioo a b) := by
    have hc : ContinuousOn (fun x : ℝ => x ^ 0 * x ^ 2) (Set.Icc a b) := by fun_prop
    exact hw.2.continuousOn_mul_of_subset hc isCompact_Icc measurableSet_Ioo
      Set.Ioo_subset_Icc_self
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · have hsub : Set.Ioo a b \ {0} ⊆ Function.support (fun x : ℝ => x ^ 0 * x ^ 2 * w x)
        ∩ Set.Ioo a b := by
      intro x ⟨hx, hx0⟩
      refine ⟨?_, hx⟩
      have : x ≠ 0 := hx0
      simp only [Function.mem_support, pow_zero, one_mul]
      exact (mul_pos (by positivity) (hw.1 x hx)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [measure_sdiff_null (by simp)]
    simp [hab]
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun x hx => ?_)
    exact mul_nonneg (by positivity) (hw.1 x hx).le

end Miao.NumericalMethods
