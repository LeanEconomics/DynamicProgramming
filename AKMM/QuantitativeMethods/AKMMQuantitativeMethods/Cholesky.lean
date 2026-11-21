/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMQuantitativeMethods.SVAR
import Mathlib.Analysis.Matrix.LDL

/-!
# Recursive (Cholesky) identification

AKMM, §8.4, the box "Recursive identification", p. 224, the system (8.8)–(8.9), and the
normalisation of footnote 6, p. 227.

* **The Cholesky decomposition**: a positive definite `Σ` is `LL'` for a lower-triangular `L` with
  positive diagonal (`ch_exists`, from Mathlib's LDL decomposition), and that `L` is unique
  (`ch_unique`; not in Mathlib).
* **Recursive identification**: if the impact matrix `B₀⁻¹` is lower triangular with positive
  diagonal and `Var(εₜ) = I`, then the Cholesky factor of `Var(uₜ)` is `B₀⁻¹`
  (`ch_recursive_identification`).
* The book's statement omits the sign normalisation: without "positive diagonal" the
  triangular factor is determined only up to the signs of its columns
  (`ch_sign_counterexample`).
* (8.8)–(8.9) ordered as `(ĝ, ŷ)`: the impact matrix `[[σ_g, 0], [χσ_g, σ_A]]` is lower
  triangular, so `χ = L₂₁/L₁₁` for the Cholesky factor `L` of `Var(ĝ, ŷ)` (`ch_fiscal_example`).
* Footnote 6's weights: for `Σ = LL'` with `L` lower triangular, `Σ_{i1}/Σ₁₁ = L_{i1}/L₁₁`
  (`ch_first_column`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

variable {n : Type*} [Fintype n] [LinearOrder n]

omit [Fintype n] in
/-- A lower-triangular matrix: `L i j = 0` for `i < j`. -/
theorem ch_lower_apply {L : Matrix n n ℝ} (hL : L.IsLowerTriangular) {i j : n} (h : i < j) :
    L i j = 0 :=
  hL (by simpa using h)

/-- The diagonal of a product of lower-triangular matrices. -/
theorem ch_lower_mul_diag {L M : Matrix n n ℝ} (hL : L.IsLowerTriangular)
    (hM : M.IsLowerTriangular) (i : n) : (L * M) i i = L i i * M i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [ch_lower_apply hM h, mul_zero]
    · rw [ch_lower_apply hL h, zero_mul]
  · simp

/-- **Uniqueness of the Cholesky factor**: two lower-triangular matrices with positive diagonal
and `L₁L₁' = L₂L₂'` are equal. -/
theorem ch_unique {L1 L2 : Matrix n n ℝ} (h1 : L1.IsLowerTriangular) (h2 : L2.IsLowerTriangular)
    (hp1 : ∀ i, 0 < L1 i i) (hp2 : ∀ i, 0 < L2 i i) (h : L1 * L1ᵀ = L2 * L2ᵀ) : L1 = L2 := by
  have hdet : IsUnit L2.det := by
    rw [det_of_isLowerTriangular L2 h2]
    exact (Finset.prod_pos fun i _ => hp2 i).ne'.isUnit
  have : Invertible L2 := invertibleOfIsUnitDet L2 hdet
  have hinv : L2⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular h2
  set Q := L2⁻¹ * L1 with hQ
  have hQl : Q.IsLowerTriangular := hinv.mul h1
  have hL1 : L1 = L2 * Q := by rw [hQ, ← Matrix.mul_assoc, mul_nonsing_inv L2 hdet, one_mul]
  have hQQ : Q * Qᵀ = 1 := by
    rw [hQ, transpose_mul]
    calc L2⁻¹ * L1 * (L1ᵀ * L2⁻¹ᵀ) = L2⁻¹ * (L1 * L1ᵀ) * L2⁻¹ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = (L2⁻¹ * L2) * (L2⁻¹ * L2)ᵀ := by
          rw [h, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul L2 hdet, transpose_one, Matrix.one_mul]
  have hQinv : Q⁻¹ = Qᵀ := inv_eq_right_inv hQQ
  have hQdet : IsUnit Q.det := isUnit_det_of_right_inverse hQQ
  have : Invertible Q := invertibleOfIsUnitDet Q hQdet
  have hQtl : Qᵀ.IsLowerTriangular := by
    rw [← hQinv]; exact blockTriangular_inv_of_blockTriangular hQl
  -- `Q` is diagonal
  have hoff : ∀ i j, i ≠ j → Q i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ch_lower_apply hQl h
    · have := ch_lower_apply hQtl h
      rwa [transpose_apply] at this
  -- its diagonal entries are positive
  have hpos : ∀ i, 0 < Q i i := by
    intro i
    have := ch_lower_mul_diag h2 hQl i
    rw [← hL1] at this
    have h1i := hp1 i
    rw [this] at h1i
    exact pos_of_mul_pos_right h1i (hp2 i).le
  -- and square to one
  have hone : ∀ i, Q i i = 1 := by
    intro i
    have := congrFun (congrFun hQQ i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by
      rw [transpose_apply, hoff i k (Ne.symm hk), zero_mul]) (by simp)] at this
    rw [transpose_apply, one_apply_eq] at this
    nlinarith [hpos i]
  have hQ1 : Q = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; rw [hone, one_apply_eq]
    · rw [hoff i j hij, one_apply_ne hij]
  rw [hL1, hQ1, Matrix.mul_one]

/-- **The Cholesky decomposition**: a positive definite real matrix is `LL'` for a
lower-triangular `L` with positive diagonal. -/
theorem ch_exists [WellFoundedLT n] [LocallyFiniteOrderBot n] {S : Matrix n n ℝ}
    (hS : S.PosDef) : ∃ L : Matrix n n ℝ, L.IsLowerTriangular ∧ (∀ i, 0 < L i i) ∧
      L * Lᵀ = S := by
  set d := LDL.diagEntries hS with hd
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    have hU : IsUnit (LDL.lowerInv hS) := isUnit_of_invertible _
    rw [← star_eq_conjTranspose]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hU).2 hS
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have := hD.diag_pos (i := i)
    simpa [LDL.diag, hd] using this
  set L0 := LDL.lower hS * diagonal (fun i => Real.sqrt (d i)) with hL0
  have hL0l : L0.IsLowerTriangular := (LDL.isLowerTriangular_lower hS).mul
    (blockTriangular_diagonal _)
  have hL0S : L0 * L0ᵀ = S := by
    have hsq : diagonal (fun i => Real.sqrt (d i)) * (diagonal fun i => Real.sqrt (d i))ᵀ =
        LDL.diag hS := by
      rw [diagonal_transpose, diagonal_mul_diagonal, LDL.diag]
      congr 1
      funext i
      rw [← hd, Real.mul_self_sqrt (hdpos i).le]
    have hLDL := LDL.lower_conj_diag hS
    rw [conjTranspose_eq_transpose_of_trivial] at hLDL
    rw [hL0, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hsq,
      ← Matrix.mul_assoc, hLDL]
  -- the diagonal of `L0` is nonzero
  have hne : ∀ i, L0 i i ≠ 0 := by
    have hdet : S.det ≠ 0 := (hS.det_pos).ne'
    rw [← hL0S, det_mul, det_transpose, det_of_isLowerTriangular L0 hL0l] at hdet
    intro i hi
    apply hdet
    have h0 : ∏ j, L0 j j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [h0, zero_mul]
  set sg : n → ℝ := fun i => if 0 < L0 i i then 1 else -1 with hsg
  have hsg2 : ∀ i, sg i * sg i = 1 := by intro i; simp only [hsg]; split_ifs <;> norm_num
  refine ⟨L0 * diagonal sg, hL0l.mul (blockTriangular_diagonal _), fun i => ?_, ?_⟩
  · rw [mul_diagonal]
    simp only [hsg]
    split_ifs with h
    · linarith
    · have := lt_of_le_of_ne (not_lt.1 h) (hne i); linarith
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal sg), diagonal_transpose,
      diagonal_mul_diagonal]
    have : (diagonal fun i => sg i * sg i) = (1 : Matrix n n ℝ) := by
      rw [show (fun i => sg i * sg i) = fun _ => (1 : ℝ) from funext hsg2]; rfl
    rw [this, Matrix.one_mul, hL0S]

/-- **Recursive identification** (AKMM, p. 224): if the variables are ordered so that the
impact matrix `B₀⁻¹` is lower triangular with positive diagonal, and `Var(εₜ) = I`, then every
lower-triangular `L` with positive diagonal and `LL' = Var(uₜ)` (the Cholesky factor) is
`B₀⁻¹`. -/
theorem ch_recursive_identification {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    {B0 L : Matrix n n ℝ} (hB : B0⁻¹.IsLowerTriangular) (hBp : ∀ i, 0 < B0⁻¹ i i)
    (hL : L.IsLowerTriangular) (hLp : ∀ i, 0 < L i i)
    (hLS : L * Lᵀ = var_mom μ (kf_app B0⁻¹ ε) (kf_app B0⁻¹ ε)) : L = B0⁻¹ := by
  rw [sv_var_u hε hI] at hLS
  exact ch_unique hL hB hLp hBp hLS

/-- **The sign normalisation is needed** (AKMM, p. 224): "a Cholesky decomposition of
`Var(uₜ)` gives `B₀⁻¹`" needs the diagonal of `B₀⁻¹` to be positive. Flipping the sign of a
column of a lower-triangular `L` gives another lower-triangular factor of the same `LL'`, and a
different one when that diagonal entry is nonzero. -/
theorem ch_sign_counterexample {L : Matrix n n ℝ} (hL : L.IsLowerTriangular)
    (k : n) (hk : L k k ≠ 0) :
    let L' := L * diagonal (fun i => if i = k then -1 else 1)
    L'.IsLowerTriangular ∧ L' * L'ᵀ = L * Lᵀ ∧ L' ≠ L := by
  intro L'
  refine ⟨hL.mul (blockTriangular_diagonal _), ?_, fun h => hk ?_⟩
  · simp only [L']
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_transpose,
      diagonal_mul_diagonal]
    have : (diagonal fun i => (if i = k then (-1 : ℝ) else 1) * if i = k then -1 else 1) =
        (1 : Matrix n n ℝ) := by
      rw [show (fun i => (if i = k then (-1 : ℝ) else 1) * if i = k then -1 else 1) =
        fun _ => (1 : ℝ) from funext fun i => by split_ifs <;> norm_num]
      rfl
    rw [this, Matrix.one_mul]
  · have := congrFun (congrFun h k) k
    simp only [L', mul_diagonal, ↓reduceIte] at this
    linarith

/-- **Footnote 6's weights** (AKMM, p. 227): if `Σ = LL'` with `L` lower triangular and `1` the
first variable (the least index), then `Σ_{i1} = L_{i1}L₁₁` and `Σ₁₁ = L₁₁²`, so
`Σ_{i1}/Σ₁₁ = L_{i1}/L₁₁`: the first column of `L` normalised to have first element `1`. -/
theorem ch_first_column {L S : Matrix n n ℝ} (hL : L.IsLowerTriangular) (hS : S = L * Lᵀ)
    (i1 : n) (hmin : ∀ j, i1 ≤ j) (i : n) :
    S i i1 = L i i1 * L i1 i1 ∧ S i1 i1 = L i1 i1 ^ 2 ∧ S i i1 / S i1 i1 = L i i1 / L i1 i1 := by
  have hcol : ∀ i, S i i1 = L i i1 * L i1 i1 := by
    intro i
    rw [hS, Matrix.mul_apply, Finset.sum_eq_single i1]
    · rfl
    · intro k _ hk
      rw [transpose_apply, ch_lower_apply hL (lt_of_le_of_ne (hmin k) (Ne.symm hk)), mul_zero]
    · simp
  refine ⟨hcol i, by rw [hcol i1, sq], ?_⟩
  rw [hcol i, hcol i1]
  rcases eq_or_ne (L i1 i1) 0 with h | h
  · simp [h]
  · field_simp

/-- **The fiscal example** (AKMM, (8.8)–(8.9), p. 224): ordering the variables as `(ĝ, ŷ)` and
normalising the shocks to unit variance, `ĝ = σ_g ε₁` and `ŷ = χσ_g ε₁ + σ_A ε₂`; the impact
matrix `[[σ_g, 0], [χσ_g, σ_A]]` is lower triangular with positive diagonal, so it is the
Cholesky factor of `Var(ĝ, ŷ)`, and `χ = L₂₁/L₁₁`. -/
theorem ch_fiscal_example {ε : Ω → Fin 2 → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    {χ σg σA : ℝ} (hg : 0 < σg) (hA : 0 < σA) {L : Matrix (Fin 2) (Fin 2) ℝ}
    (hL : L.IsLowerTriangular) (hLp : ∀ i, 0 < L i i)
    (hLS : L * Lᵀ = var_mom μ (kf_app !![σg, 0; χ * σg, σA] ε)
      (kf_app !![σg, 0; χ * σg, σA] ε)) :
    L = !![σg, 0; χ * σg, σA] ∧ χ = L 1 0 / L 0 0 := by
  have hb : (!![σg, 0; χ * σg, σA] : Matrix (Fin 2) (Fin 2) ℝ).IsLowerTriangular := by
    intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hbp : ∀ i, 0 < (!![σg, 0; χ * σg, σA] : Matrix (Fin 2) (Fin 2) ℝ) i i := by
    intro i; fin_cases i <;> simp [hg, hA]
  have hV : var_mom μ (kf_app !![σg, 0; χ * σg, σA] ε) (kf_app !![σg, 0; χ * σg, σA] ε) =
      !![σg, 0; χ * σg, σA] * (!![σg, 0; χ * σg, σA])ᵀ := by
    rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hI, Matrix.one_mul]
  rw [hV] at hLS
  have hLeq := ch_unique hL hb hLp hbp hLS
  refine ⟨hLeq, ?_⟩
  rw [hLeq]
  simp [hg.ne']

end AKMM.QuantitativeMethods
