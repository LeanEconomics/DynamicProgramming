/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.SimsSVD
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Existence of the singular value decomposition (2.25)

Miao, §2.3.3, p. 62, (2.25). `SimsSVD` takes the SVD `Q₂.Π = U.1D₁₁V.1ᴴ` as a hypothesis
(`IsThinSVD`). Here it is proved to exist for every complex `p × m` matrix `B`, with `D₁₁`
diagonal with positive entries and `r = rank B`, together with the complementary block `V.2`
of the unitary `V = [V.1 V.2]`: `V.1ᴴV.2 = 0`, `V.2ᴴV.2 = I`, `V.1V.1ᴴ + V.2V.2ᴴ = I`
(`exists_thinSVD`).

Route: the spectral theorem for the Hermitian positive semidefinite matrix `BᴴB`
(`Matrix.IsHermitian.eigenvectorBasis`, `mulVec_eigenvectorBasis`). The eigenvectors with
nonzero (hence positive) eigenvalue form `V.1`, the others `V.2`; `D₁₁ = diag(√λ)` and
`U.1 = BV.1D₁₁⁻¹`. The number of nonzero eigenvalues of `BᴴB` is `rank B`
(`rank_eq_card_non_zero_eigs`, `rank_conjTranspose_mul_self`).

Unconditional versions of the `SimsSVD` results that assumed an SVD: `colspace_iff_svd`,
`lambda_formula_svd`, `corollary_2_3_1_rank` (the pair `(y, η)` is unique iff `rank Q₂.Π = m`),
`lubik_schorfheide_rank`, `eq_2_26_svd`.

The full unitary `U = [U.1 U.2]` of (2.25) is not constructed: only `U.1` is used in the text.
-/

namespace Miao.RationalExpectations

open scoped Matrix

/-- The eigenvector matrix `W` of `BᴴB` satisfies `BᴴBW = W diag(λ)`. -/
theorem svdE_mul_eigen {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : H.IsHermitian) :
    H * (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) =
      (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.diagonal fun k => (hH.eigenvalues k : ℂ) := by
  ext a k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have := congrFun (hH.mulVec_eigenvectorBasis k) a
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Complex.real_smul] at this
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, this, mul_comm]

/-- Columns of a unitary matrix selected by two maps: `(W.c₁)ᴴ(W.c₂)` is `1` at `(k, l)` iff
`c₁ k = c₂ l`. -/
theorem svdE_cols {m r k : ℕ} {W : Matrix (Fin m) (Fin m) ℂ} (hW : Wᴴ * W = 1)
    (c₁ : Fin r → Fin m) (c₂ : Fin k → Fin m) :
    (W.submatrix id c₁)ᴴ * W.submatrix id c₂ = (1 : Matrix (Fin m) (Fin m) ℂ).submatrix c₁ c₂ := by
  ext a b
  have := congrFun (congrFun hW (c₁ a)) (c₂ b)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id] using this

open scoped ComplexOrder in
/-- **Existence of the thin SVD** (Miao, (2.25), p. 62). Every complex `p × m` matrix `B` has
a thin SVD `B = U.1D₁₁V.1ᴴ` with `U.1ᴴU.1 = I`, `V.1ᴴV.1 = I`, `D₁₁ = diag(s)`, `s > 0`, and
`r = rank B`; and there is `V.2` (`k = m − r` columns) with `V.1ᴴV.2 = 0`, `V.2ᴴV.2 = I`,
`V.1V.1ᴴ + V.2V.2ᴴ = I`. -/
theorem exists_thinSVD {p m : ℕ} (B : Matrix (Fin p) (Fin m) ℂ) :
    ∃ (r k : ℕ) (U1 : Matrix (Fin p) (Fin r) ℂ) (s : Fin r → ℝ) (V1 : Matrix (Fin m) (Fin r) ℂ)
      (V2 : Matrix (Fin m) (Fin k) ℂ),
      IsThinSVD B U1 (Matrix.diagonal fun i => (s i : ℂ)) V1 ∧ (∀ i, 0 < s i) ∧
        r = B.rank ∧ r + k = m ∧ V1ᴴ * V2 = 0 ∧ V2ᴴ * V2 = 1 ∧ V1 * V1ᴴ + V2 * V2ᴴ = 1 := by
  classical
  have hP := Matrix.posSemidef_conjTranspose_mul_self B
  set hH := hP.1
  set lam := hH.eigenvalues
  set W : Matrix (Fin m) (Fin m) ℂ := (hH.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) with hWdef
  have hWW : Wᴴ * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * Wᴴ = 1 := Unitary.coe_mul_star_self _
  have hHW := svdE_mul_eigen hH
  rw [← hWdef] at hHW
  set r := Fintype.card {i // lam i ≠ 0}
  set k := Fintype.card {i // ¬ lam i ≠ 0}
  let e1 := Fintype.equivFin {i // lam i ≠ 0}
  let e2 := Fintype.equivFin {i // ¬ lam i ≠ 0}
  let c1 : Fin r → Fin m := fun a => (e1.symm a).1
  let c2 : Fin k → Fin m := fun a => (e2.symm a).1
  have hc1 : Function.Injective c1 := fun a b h => e1.symm.injective (Subtype.ext h)
  have hc2 : Function.Injective c2 := fun a b h => e2.symm.injective (Subtype.ext h)
  have hpos : ∀ a, 0 < lam (c1 a) := fun a =>
    lt_of_le_of_ne (hP.eigenvalues_nonneg _) (e1.symm a).2.symm
  have hzero : ∀ a, lam (c2 a) = 0 := fun a => not_not.1 (e2.symm a).2
  set V1 := W.submatrix id c1 with hV1
  set V2 := W.submatrix id c2 with hV2
  have h11 : V1ᴴ * V1 = 1 := by rw [svdE_cols hWW, Matrix.submatrix_one _ hc1]
  have h22 : V2ᴴ * V2 = 1 := by rw [svdE_cols hWW, Matrix.submatrix_one _ hc2]
  have h12 : V1ᴴ * V2 = 0 := by
    rw [svdE_cols hWW]
    ext a b
    have hne : c1 a ≠ c2 b := fun h => by
      change (e1.symm a).1 = (e2.symm b).1 at h
      have h1 := (e1.symm a).2
      rw [h] at h1
      exact (e2.symm b).2 h1
    simp [Matrix.one_apply_ne hne]
  have hcompl : V1 * V1ᴴ + V2 * V2ᴴ = 1 := by
    rw [← hWW']
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply, id, hV1, hV2, c1, c2]
    rw [Equiv.sum_comp e1.symm (fun i => W a i.1 * star (W b i.1)),
      Equiv.sum_comp e2.symm (fun i => W a i.1 * star (W b i.1))]
    exact Fintype.sum_subtype_add_sum_subtype (fun i => lam i ≠ 0)
      (fun i => W a i * star (W b i))
  have hHV : ∀ (n : ℕ) (c : Fin n → Fin m),
      Bᴴ * B * W.submatrix id c = W.submatrix id c * Matrix.diagonal fun a => (lam (c a) : ℂ) := by
    intro n c
    ext a b
    have := congrFun (congrFun hHW a) (c b)
    rw [Matrix.mul_diagonal] at this
    rw [Matrix.mul_diagonal, Matrix.submatrix_apply, id, ← this]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  set s : Fin r → ℝ := fun a => Real.sqrt (lam (c1 a))
  have hs : ∀ a, 0 < s a := fun a => Real.sqrt_pos.2 (hpos a)
  have hs2 : ∀ a, (s a : ℂ) * (s a : ℂ) = (lam (c1 a) : ℂ) := fun a => by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos a).le]
  set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => (s a : ℂ)
  set Di : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a => ((s a)⁻¹ : ℂ)
  have hsne : ∀ a, (s a : ℂ) ≠ 0 := fun a => Complex.ofReal_ne_zero.2 (hs a).ne'
  have hDiD : Di * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hsne a)
  have hDi : Diᴴ = Di := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp only [Pi.star_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hBV2 : B * V2 = 0 := by
    rw [← Matrix.conjTranspose_mul_self_eq_zero, Matrix.conjTranspose_mul,
      show V2ᴴ * Bᴴ * (B * V2) = V2ᴴ * (Bᴴ * B * V2) by simp only [Matrix.mul_assoc], hHV k c2,
      ← Matrix.mul_assoc, h22, Matrix.one_mul]
    ext a b
    simp [Matrix.diagonal_apply, hzero]
  refine ⟨r, k, B * V1 * Di, s, V1, V2, ⟨?_, ?_, h11, ?_⟩, hs, ?_, ?_, h12, h22, hcompl⟩
  · calc B = B * (V1 * V1ᴴ + V2 * V2ᴴ) := by rw [hcompl, Matrix.mul_one]
      _ = B * V1 * (Di * D) * V1ᴴ := by
        rw [hDiD, Matrix.mul_add, ← Matrix.mul_assoc B V2, hBV2, Matrix.zero_mul, add_zero,
          Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]; rfl
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDi,
      show Di * (V1ᴴ * Bᴴ) * (B * V1 * Di) = Di * (V1ᴴ * (Bᴴ * B * V1)) * Di by
        simp only [Matrix.mul_assoc], hHV r c1, ← Matrix.mul_assoc V1ᴴ, h11, Matrix.one_mul,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hs2]
    field_simp [hsne a]
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hsne a
  · rw [← Matrix.rank_conjTranspose_mul_self, hH.rank_eq_card_non_zero_eigs]
  · have := Fintype.card_congr (Equiv.sumCompl fun i : Fin m => lam i ≠ 0)
    rw [Fintype.card_sum, Fintype.card_fin] at this
    exact this

/-- Miao, p. 62, the column-space test, unconditionally: every `A` has a thin SVD
`A = U.1D₁₁V.1ᴴ`, and for it `col(C) ⊆ col(A)` iff `(I − U.1U.1ᴴ)C = 0` for every `C`. -/
theorem colspace_iff_svd {p m : ℕ} (A : Matrix (Fin p) (Fin m) ℂ) :
    ∃ (r : ℕ) (U1 : Matrix (Fin p) (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ)
      (V1 : Matrix (Fin m) (Fin r) ℂ), IsThinSVD A U1 D V1 ∧
        ∀ (k : ℕ) (C : Matrix (Fin p) (Fin k) ℂ),
          (∃ Λ : Matrix (Fin m) (Fin k) ℂ, C = A * Λ) ↔ (1 - U1 * U1ᴴ) * C = 0 := by
  obtain ⟨r, -, U1, s, V1, -, h, -⟩ := exists_thinSVD A
  exact ⟨r, U1, _, V1, h, fun _ C => colspace_iff h C⟩

/-- Miao, p. 62, "`Λ = V.1D₁₁⁻¹U.1ᴴ(Q₂.Ψ)`", unconditionally: under Assumption 2.3.1 there is
a thin SVD of `Q₂.Π` for which this `Λ` works. -/
theorem lambda_formula_svd {ns nu nε m : ℕ} {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ}
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hA1 : SimsAssumption1 Q Ψ Pm) :
    ∃ (r : ℕ) (U1 : Matrix (Fin nu) (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ)
      (V1 : Matrix (Fin m) (Fin r) ℂ), IsThinSVD (simsBot Q * Pm) U1 D V1 ∧
        simsBot Q * Ψ = simsBot Q * Pm * (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) := by
  obtain ⟨r, -, U1, s, V1, -, h, -⟩ := exists_thinSVD (simsBot Q * Pm)
  exact ⟨r, U1, _, V1, h, lambda_formula h hA1⟩

/-- **Corollary 2.3.1** (Miao, p. 62), unconditional form of `corollary_2_3_1`: with a rich
filtration the stable solution with its prediction error, `(y, η)`, is unique iff
`rank(Q₂.Π) = m`. -/
theorem corollary_2_3_1_rank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} :
    SimsPairUnique E Γ₀ Γ₁ Ψ Pm ↔ (simsBot Q * Pm).rank = m := by
  obtain ⟨r, -, U1, s, V1, -, h, -, hr, -⟩ := exists_thinSVD (simsBot Q * Pm)
  rw [corollary_2_3_1 E hrich hqz h, hr]

/-- **Lubik–Schorfheide** (Miao, p. 62), unconditional form of `lubik_schorfheide`: if
`rank(Q₂.Π) < m` and the filtration is rich, every stable solution `(y, η)` lies in an
injective one-parameter family of stable solutions with the same initial value. -/
theorem lubik_schorfheide_rank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] (E : CondExpSystem ℂ V) (hrich : SimsRich E) {ns nu nε m : ℕ}
    {Γ₀ Γ₁ Q Z : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} (hqz : IsSimsQZ Γ₀ Γ₁ Q Z)
    {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ} {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ}
    (hr : (simsBot Q * Pm).rank < m) {ε : ℕ → Fin nε → V} {y : ℕ → Fin (ns + nu) → V}
    {η : ℕ → Fin m → V} (hsol : IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε y η) (hy : IsStableProc y) :
    ∃ f : ℂ → (ℕ → Fin (ns + nu) → V) × (ℕ → Fin m → V), Function.Injective f ∧
      ∀ c, IsSimsSolution E Γ₀ Γ₁ Ψ Pm ε (f c).1 (f c).2 ∧ IsStableProc (f c).1 ∧
        (f c).1 0 = y 0 := by
  obtain ⟨r, -, U1, s, V1, -, h, -, hrk, -⟩ := exists_thinSVD (simsBot Q * Pm)
  exact lubik_schorfheide E hrich hqz h (hrk ▸ hr) hsol hy

/-- Miao, (2.26), p. 63, unconditionally: under Assumption 2.3.1 there is an SVD
`Q₂.Π = U.1D₁₁V.1ᴴ` with complement `V.2` such that the solutions `η` of (2.23) are exactly
`η = −V.1D₁₁⁻¹U.1ᴴQ₂.Ψε + V.2e`, `e` arbitrary. -/
theorem eq_2_26_svd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ns nu nε m : ℕ}
    {Q : Matrix (Fin (ns + nu)) (Fin (ns + nu)) ℂ} {Ψ : Matrix (Fin (ns + nu)) (Fin nε) ℂ}
    {Pm : Matrix (Fin (ns + nu)) (Fin m) ℂ} (hA1 : SimsAssumption1 Q Ψ Pm) :
    ∃ (r k : ℕ) (U1 : Matrix (Fin nu) (Fin r) ℂ) (D : Matrix (Fin r) (Fin r) ℂ)
      (V1 : Matrix (Fin m) (Fin r) ℂ) (V2 : Matrix (Fin m) (Fin k) ℂ),
      IsThinSVD (simsBot Q * Pm) U1 D V1 ∧ ∀ (e : Fin nε → V) (h : Fin m → V),
        matAct (simsBot Q) (matAct Ψ e + matAct Pm h) = 0 ↔
          ∃ s : Fin k → V, h = -matAct (V1 * D⁻¹ * U1ᴴ * (simsBot Q * Ψ)) e + matAct V2 s := by
  obtain ⟨r, k, U1, s, V1, V2, h, -, -, -, h12, -, hc⟩ := exists_thinSVD (simsBot Q * Pm)
  exact ⟨r, k, U1, _, V1, V2, h, fun e η => eq_2_26 h h12 hc hA1 e η⟩

end Miao.RationalExpectations
