/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.LinearSystems

/-!
# The linearized Euler equations

SLP §6.4, pp. 149–151. For a quadratic return, with `l × l` matrices `F_xx`, `F_xy`, `F_yy` of
second derivatives (`F_xx`, `F_yy` symmetric), the Euler equations in deviations are
`z_{t+2} = Jz_{t+1} + Kz_t`, with `J = −β⁻¹F_xy⁻¹(F_yy + βF_xx)` and `K = −β⁻¹F_xy⁻¹F'_xy`.
Stacked as `Z_{t+1} = AZ_t`, the matrix is `A = [[J, K], [I, 0]]` (`eulerA`).

* **Exercise 6.5** (`ex_6_5`): if `F_xy` and `F'_xy + F_yy + βF_xx + βF_xy` are nonsingular, so
  are `A` and `I − A`.
* **Lemma 6.7** (`lemma_6_7`, Levhari–Liviatan): if `λ` is a characteristic root of `A`, so is
  `(βλ)⁻¹`. The algebra is done over any field (`root_inv_of_root`) from the relations
  `F_xyJ = −β⁻¹(F_yy + βF_xx)` and `F_xyK = −β⁻¹F'_xy`. `λ` is a root iff (5)
  `det[β⁻¹F'_xy + λβ⁻¹(F_yy + βF_xx) + λ²F_xy] = 0` (`det_char_eq`), and the matrix at
  `(βλ)⁻¹`, times `λ²β`, is the transpose of the matrix at `λ`.
-/

namespace StokeyLucasPrescott.DeterministicDynamics

open Matrix

variable {l : ℕ}

/-- `J = −β⁻¹F_xy⁻¹(F_yy + βF_xx)`. -/
noncomputable def eulerJ (Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) :
    Matrix (Fin l) (Fin l) ℝ := -(β⁻¹ • (Fxy⁻¹ * (Fyy + β • Fxx)))

/-- `K = −β⁻¹F_xy⁻¹F'_xy`. -/
noncomputable def eulerK (Fxy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) : Matrix (Fin l) (Fin l) ℝ :=
  -(β⁻¹ • (Fxy⁻¹ * Fxyᵀ))

/-- The stacked matrix `A = [[J, K], [I, 0]]`. -/
noncomputable def eulerA (Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) :
    Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) ℝ :=
  fromBlocks (eulerJ Fxx Fxy Fyy β) (eulerK Fxy β) 1 0

/-! ### Determinants of block matrices -/

variable {𝕜 : Type*} [Field 𝕜]

/-- `det [[J, K], [I, 0]] = ±det K`: the block swap `S = [[0, I], [I, 0]]` squares to `I` and
`[[J, K], [I, 0]]·S = [[K, J], [0, I]]`. -/
theorem det_fromBlocks_one_zero (J K : Matrix (Fin l) (Fin l) 𝕜) :
    (fromBlocks J K 1 0).det ≠ 0 ↔ K.det ≠ 0 := by
  set S : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) 𝕜 := fromBlocks 0 1 1 0
  have hS : S * S = 1 := by
    simp only [S, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero]
    exact fromBlocks_one
  have hSdet : S.det * S.det = 1 := by rw [← det_mul, hS, det_one]
  have hAS : fromBlocks J K 1 0 * S =
      fromBlocks K J (0 : Matrix (Fin l) (Fin l) 𝕜) 1 := by
    simp only [S, fromBlocks_multiply, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero]
  have hdet : (fromBlocks J K 1 0).det * S.det = K.det := by
    rw [← det_mul, hAS, det_fromBlocks_zero₂₁, det_one, mul_one]
  have hS0 : S.det ≠ 0 := fun h => by rw [h, zero_mul] at hSdet; exact zero_ne_one hSdet
  constructor
  · intro h; rw [← hdet]; exact mul_ne_zero h hS0
  · intro h h0; rw [h0, zero_mul] at hdet; exact h hdet.symm

/-- Block triangular factorization: for `λ ≠ 0`,
`det [[λ − J, −K], [−I, λ]] = det(λ²I − λJ − K)`. -/
theorem det_char_block {J K : Matrix (Fin l) (Fin l) 𝕜} {μ : 𝕜} (hμ : μ ≠ 0) :
    (scalar (Fin l ⊕ Fin l) μ - fromBlocks J K 1 0).det = (μ ^ 2 • 1 - μ • J - K).det := by
  have hsc : scalar (Fin l ⊕ Fin l) μ - fromBlocks J K 1 0 =
      fromBlocks (μ • 1 - J) (-K) (-1) (μ • 1) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]
  -- `[[P, Q], [R, D]] = [[1, QD⁻¹], [0, 1]]·[[P − QD⁻¹R, 0], [R, D]]` with `D = μ`
  have hfac : fromBlocks (μ • 1 - J) (-K) (-1) (μ • (1 : Matrix (Fin l) (Fin l) 𝕜)) =
      fromBlocks 1 (μ⁻¹ • -K) 0 1 * fromBlocks (μ • 1 - J - μ⁻¹ • K) 0 (-1) (μ • 1) := by
    rw [fromBlocks_multiply]
    congr 1
    · simp only [Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, smul_neg, neg_neg]
      abel
    · simp only [Matrix.mul_zero, zero_add, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        mul_inv_cancel₀ hμ, one_smul]
    · simp
    · simp
  rw [hsc, hfac, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
  simp only [det_one, one_mul]
  rw [mul_comm, det_smul, det_one, mul_one, ← det_smul]
  congr 1
  rw [smul_sub, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hμ, one_smul, ← pow_two]

variable {P S J K : Matrix (Fin l) (Fin l) 𝕜} {β : 𝕜}

/-- (5): with `PJ = −β⁻¹S` and `PK = −β⁻¹Pᵀ`,
`P(λ²I − λJ − K) = λ²P + λβ⁻¹S + β⁻¹Pᵀ`. -/
theorem det_char_eq (hJ : P * J = -(β⁻¹ • S)) (hK : P * K = -(β⁻¹ • Pᵀ)) (μ : 𝕜) :
    P * (μ ^ 2 • 1 - μ • J - K) = μ ^ 2 • P + μ • (β⁻¹ • S) + β⁻¹ • Pᵀ := by
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, hJ, hK]
  simp only [smul_neg]
  abel

/-- **Lemma 6.7** over a field. Let `P` be nonsingular, `S` symmetric, `β ≠ 0`, `PJ = −β⁻¹S` and
`PK = −β⁻¹Pᵀ`. If `λ` is a characteristic root of `[[J, K], [I, 0]]`, so is `(βλ)⁻¹`. -/
theorem root_inv_of_root (hP : P.det ≠ 0) (hS : Sᵀ = S) (hβ : β ≠ 0)
    (hJ : P * J = -(β⁻¹ • S)) (hK : P * K = -(β⁻¹ • Pᵀ)) {μ : 𝕜}
    (hroot : (scalar (Fin l ⊕ Fin l) μ - fromBlocks J K 1 0).det = 0) :
    (scalar (Fin l ⊕ Fin l) (β * μ)⁻¹ - fromBlocks J K 1 0).det = 0 := by
  -- `K` is nonsingular, so `0` is not a root
  have hKdet : K.det ≠ 0 := by
    have := congrArg det hK
    rw [det_mul, det_neg, det_smul, det_transpose] at this
    intro h0
    rw [h0, mul_zero] at this
    have h2 : (-1 : 𝕜) ^ Fintype.card (Fin l) * (β⁻¹ ^ Fintype.card (Fin l) * P.det) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hβ)) hP)
    exact h2 this.symm
  have hμ : μ ≠ 0 := by
    rintro rfl
    have hA := (det_fromBlocks_one_zero J K).2 hKdet
    have : (scalar (Fin l ⊕ Fin l) (0 : 𝕜) - fromBlocks J K 1 0).det =
        (-1) ^ Fintype.card (Fin l ⊕ Fin l) * (fromBlocks J K 1 0).det := by
      rw [map_zero, zero_sub, ← det_smul, neg_one_smul]
    rw [this] at hroot
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hA hroot
  set ν := (β * μ)⁻¹
  have hν : ν ≠ 0 := inv_ne_zero (mul_ne_zero hβ hμ)
  -- the matrix of (5)
  set M : 𝕜 → Matrix (Fin l) (Fin l) 𝕜 := fun t => t ^ 2 • P + t • (β⁻¹ • S) + β⁻¹ • Pᵀ
  have hdet : ∀ t : 𝕜, t ≠ 0 →
      (scalar (Fin l ⊕ Fin l) t - fromBlocks J K 1 0).det * P.det = (M t).det := fun t ht => by
    rw [det_char_block ht, mul_comm, ← det_mul, det_char_eq hJ hK]
  have hMμ : (M μ).det = 0 := by rw [← hdet μ hμ, hroot, zero_mul]
  -- `λ²β·M(ν) = M(λ)ᵀ`
  have htr : (μ ^ 2 * β) • M ν = (M μ)ᵀ := by
    simp only [M, ν, transpose_add, transpose_smul, transpose_transpose, hS, smul_add,
      smul_smul]
    have e1 : μ ^ 2 * β * (β * μ)⁻¹ ^ 2 = β⁻¹ := by field_simp
    have e2 : μ ^ 2 * β * ((β * μ)⁻¹ * β⁻¹) = μ * β⁻¹ := by field_simp
    have e3 : μ ^ 2 * β * β⁻¹ = μ ^ 2 := by field_simp
    rw [e1, e2, e3]
    abel
  have hMν : (M ν).det = 0 := by
    have := congrArg det htr
    rw [det_smul, det_transpose, hMμ] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hμ) hβ))
  have := hdet ν hν
  rw [hMν] at this
  exact (mul_eq_zero.1 this).resolve_right hP

/-! ### The real Euler matrix -/

theorem fxy_mul_eulerJ {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hxy : Fxy.det ≠ 0) :
    Fxy * eulerJ Fxx Fxy Fyy β = -(β⁻¹ • (Fyy + β • Fxx)) := by
  rw [eulerJ, Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hxy), Matrix.one_mul]

theorem fxy_mul_eulerK {Fxy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hxy : Fxy.det ≠ 0) :
    Fxy * eulerK Fxy β = -(β⁻¹ • Fxyᵀ) := by
  rw [eulerK, Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hxy), Matrix.one_mul]

/-- **Exercise 6.5.** If `F_xy` and `F'_xy + F_yy + βF_xx + βF_xy` are nonsingular (and `β ≠ 0`),
then `A` and `I − A` are nonsingular. -/
theorem ex_6_5 {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hβ : β ≠ 0)
    (hxy : Fxy.det ≠ 0) (hS : (Fxyᵀ + Fyy + β • Fxx + β • Fxy).det ≠ 0) :
    (eulerA Fxx Fxy Fyy β).det ≠ 0 ∧ (1 - eulerA Fxx Fxy Fyy β).det ≠ 0 := by
  have hcard : ∀ c : ℝ, c ≠ 0 → c ^ Fintype.card (Fin l) ≠ 0 := fun c hc => pow_ne_zero _ hc
  refine ⟨(det_fromBlocks_one_zero _ _).2 ?_, ?_⟩
  · -- `F_xy K = −β⁻¹F'_xy` is nonsingular
    intro h0
    have := congrArg det (fxy_mul_eulerK (β := β) hxy)
    rw [det_mul, h0, mul_zero, det_neg, det_smul, det_transpose] at this
    exact mul_ne_zero (hcard _ (by norm_num)) (mul_ne_zero (hcard _ (inv_ne_zero hβ)) hxy)
      this.symm
  · -- `I − A = [[I − J, −K], [−I, I]]`, with determinant `det(I − J − K)`
    have h1 : 1 - eulerA Fxx Fxy Fyy β =
        fromBlocks (1 - eulerJ Fxx Fxy Fyy β) (-eulerK Fxy β) (-1) 1 := by
      ext (i | i) (j | j) <;> simp [eulerA, Matrix.one_apply]
    rw [h1, det_fromBlocks_one₂₂]
    have h2 : Fxy * (1 - eulerJ Fxx Fxy Fyy β - -eulerK Fxy β * -1) =
        β⁻¹ • (Fxyᵀ + Fyy + β • Fxx + β • Fxy) := by
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg, Matrix.mul_sub, Matrix.mul_sub,
        Matrix.mul_one, fxy_mul_eulerJ hxy, fxy_mul_eulerK hxy]
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hβ, one_smul, sub_neg_eq_add]
      abel
    intro h0
    have := congrArg det h2
    rw [det_mul, h0, mul_zero, det_smul] at this
    exact mul_ne_zero (hcard _ (inv_ne_zero hβ)) hS this.symm

/-- **Lemma 6.7.** If `F_xy` is nonsingular, `F_xx` and `F_yy` are symmetric and `β ≠ 0`, then
whenever `λ` is a characteristic root of `A`, so is `(βλ)⁻¹`. -/
theorem lemma_6_7 {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hβ : β ≠ 0)
    (hxy : Fxy.det ≠ 0) (hxx : Fxxᵀ = Fxx) (hyy : Fyyᵀ = Fyy) {μ : ℂ}
    (hμ : ((eulerA Fxx Fxy Fyy β).charpoly.map Complex.ofRealHom).IsRoot μ) :
    ((eulerA Fxx Fxy Fyy β).charpoly.map Complex.ofRealHom).IsRoot ((β * μ)⁻¹ : ℂ) := by
  set f := Complex.ofRealHom
  have hroot : ∀ ν : ℂ, ((eulerA Fxx Fxy Fyy β).charpoly.map f).IsRoot ν ↔
      (scalar (Fin l ⊕ Fin l) ν - fromBlocks ((eulerJ Fxx Fxy Fyy β).map f)
        ((eulerK Fxy β).map f) 1 0).det = 0 := fun ν => by
    rw [Polynomial.IsRoot.def, ← Matrix.charpoly_map, Matrix.eval_charpoly, eulerA,
      fromBlocks_map, Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_zero _ (map_zero f)]
  rw [hroot] at hμ ⊢
  have hP : (Fxy.map f).det ≠ 0 := by
    have : (Fxy.map f).det = f Fxy.det := by rw [RingHom.map_det]; rfl
    rw [this]; exact (map_ne_zero f).2 hxy
  have hS : ((Fyy + β • Fxx).map f)ᵀ = (Fyy + β • Fxx).map f := by
    rw [← Matrix.transpose_map, transpose_add, transpose_smul, hxx, hyy]
  have hJ : Fxy.map f * (eulerJ Fxx Fxy Fyy β).map f =
      -((f β)⁻¹ • (Fyy + β • Fxx).map f) := by
    rw [← Matrix.map_mul, fxy_mul_eulerJ hxy]
    ext i j
    simp [f]
    ring
  have hK : Fxy.map f * (eulerK Fxy β).map f = -((f β)⁻¹ • (Fxy.map f)ᵀ) := by
    rw [← Matrix.map_mul, fxy_mul_eulerK hxy]
    ext i j
    simp [f]
  have := root_inv_of_root hP hS ((map_ne_zero f).2 hβ) hJ hK hμ
  simpa [f] using this

end StokeyLucasPrescott.DeterministicDynamics
