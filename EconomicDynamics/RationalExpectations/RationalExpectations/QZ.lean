/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.DeterministicBasics
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Generalized eigenvalues and the complex generalized Schur (QZ) form

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

namespace Miao.RationalExpectations

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

end Miao.RationalExpectations
