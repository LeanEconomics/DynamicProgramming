/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RationalExpectations.LinearSystems
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection

/-!
# A real block diagonalisation `W = P⁻¹ diag(J_s, J_u) P`

Copied from `EconomicDynamics/DifferenceEquations` (Miao, Chapter 1).

Miao, §1.4.1, pp. 17–20. The book takes the complex Jordan form `W = P⁻¹JP` and orders the
Jordan blocks as `J = diag(J_s, J_u)`, stable roots first. Only the split into a stable and an
unstable block is used in the proofs of Theorem 1.4.2, Corollary 1.4.1 and Theorem 1.4.3, so
here a **real** invertible `P` is used (`IsRealBlockSplit W P R J_s J_u`):

* `PR = I`, `RP = I` (`R = P⁻¹`, (1.28)), `PW = diag(J_s, J_u)P`;
* all eigenvalues of `J_s` have modulus `< 1`, all eigenvalues of `J_u` modulus `> 1`.

`exists_real_block_split`: such a real `P` exists whenever `W` has no eigenvalue on the unit
circle, with `J_s` of size `n_s = dim E_s`, the number of stable characteristic roots counted
with multiplicity (`finrank_stableR`). The columns of `R` are a basis of `E_s` followed by a
basis of `E_u` (`RealSplitting`); `J = PWR` is block diagonal because `E_s` and `E_u` are
`W`-invariant. An eigenvector `w` of a block gives the eigenvector `R(w, 0)` (or `R(0, w)`) of
`W` in the complex stable (unstable) subspace, which fixes the modulus of its eigenvalue.

Consequences used later: `WR = RJ` (`mul_R`), `n_s + n_u = n` (`card_add_card`),
`I − W` is invertible (`isUnit_one_sub`), and the block formulas for `P x` and `R x*`.
-/

open Filter Topology

namespace Miao.RationalExpectations

open Module
open scoped Matrix

variable {ι σ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ]
  [DecidableEq τ]

/-- A real block diagonalisation of `W` (Miao, pp. 18–20, with a real `P` in place of the
Jordan form): `R = P⁻¹`, `PW = diag(J_s, J_u)P`, `J_s` stable, every eigenvalue of `J_u` of
modulus greater than one. -/
def IsRealBlockSplit (W : Matrix ι ι ℝ) (P : Matrix (σ ⊕ τ) ι ℝ) (R : Matrix ι (σ ⊕ τ) ℝ)
    (Js : Matrix σ σ ℝ) (Ju : Matrix τ τ ℝ) : Prop :=
  P * R = 1 ∧ R * P = 1 ∧ P * W = Matrix.fromBlocks Js 0 0 Ju * P ∧
    IsStableMatrix (Js.map Complex.ofRealHom) ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (Ju.map Complex.ofRealHom)) μ → 1 < ‖μ‖

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] [DecidableEq τ] in
/-- `diag(J_s, J_u)` acts blockwise: the `s` part. -/
theorem blockDiag_mulVec_inl (Js : Matrix σ σ ℝ) (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → ℝ) :
    (Matrix.fromBlocks Js 0 0 Ju *ᵥ v) ∘ Sum.inl = Js *ᵥ (v ∘ Sum.inl) := by
  rw [Matrix.fromBlocks_mulVec]
  simp

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] [DecidableEq τ] in
/-- `diag(J_s, J_u)` acts blockwise: the `u` part. -/
theorem blockDiag_mulVec_inr (Js : Matrix σ σ ℝ) (Ju : Matrix τ τ ℝ) (v : σ ⊕ τ → ℝ) :
    (Matrix.fromBlocks Js 0 0 Ju *ᵥ v) ∘ Sum.inr = Ju *ᵥ (v ∘ Sum.inr) := by
  rw [Matrix.fromBlocks_mulVec]
  simp

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
/-- The first block row of a matrix with block columns. -/
theorem mulVec_comp_inl {κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inl = P.toBlocks₁₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₁₂ *ᵥ (x ∘ Sum.inr) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
/-- The second block row of a matrix with block columns. -/
theorem mulVec_comp_inr {κ υ : Type*} [Fintype κ] [Fintype υ] (P : Matrix (σ ⊕ τ) (κ ⊕ υ) ℝ)
    (x : κ ⊕ υ → ℝ) :
    (P *ᵥ x) ∘ Sum.inr = P.toBlocks₂₁ *ᵥ (x ∘ Sum.inl) + P.toBlocks₂₂ *ᵥ (x ∘ Sum.inr) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

/-- `WR = RJ`. -/
theorem IsRealBlockSplit.mul_R {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ}
    {R : Matrix ι (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (h : IsRealBlockSplit W P R Js Ju) : W * R = R * Matrix.fromBlocks Js 0 0 Ju := by
  obtain ⟨hPR, hRP, hPW, -, -⟩ := h
  calc W * R = R * P * W * R := by rw [hRP, Matrix.one_mul]
    _ = R * (P * W) * R := by rw [Matrix.mul_assoc R P W]
    _ = R * Matrix.fromBlocks Js 0 0 Ju * (P * R) := by
        rw [hPW, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = R * Matrix.fromBlocks Js 0 0 Ju := by rw [hPR, Matrix.mul_one]

/-- `n_s + n_u = n`: `P` is invertible. -/
theorem card_add_card_of_inv {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    (hPR : P * R = 1) (hRP : R * P = 1) : Fintype.card σ + Fintype.card τ = Fintype.card ι := by
  classical
  have e : (σ ⊕ τ → ℝ) ≃ₗ[ℝ] (ι → ℝ) := LinearEquiv.ofLinearMap (Matrix.toLin' R)
    (Matrix.toLin' P) (by rw [← Matrix.toLin'_mul, hRP, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hPR, Matrix.toLin'_one])
  have := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] at this
  exact this

/-- `I − W` is invertible under a block split: `1` is not an eigenvalue. -/
theorem IsRealBlockSplit.isUnit_one_sub {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ}
    {R : Matrix ι (σ ⊕ τ) ℝ} {Js : Matrix σ σ ℝ} {Ju : Matrix τ τ ℝ}
    (h : IsRealBlockSplit W P R Js Ju) : IsUnit (1 - W).det := by
  obtain ⟨hPR, hRP, hPW, hJs, hJu⟩ := h
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v v' hvv
  rw [← sub_eq_zero]
  set d := v - v'
  have hd : W *ᵥ d = d := by
    have : (1 - W) *ᵥ d = 0 := by simp only [d, Matrix.mulVec_sub, hvv, sub_self]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this.symm
  have hJ : Matrix.fromBlocks Js 0 0 Ju *ᵥ (P *ᵥ d) = P *ᵥ d := by
    rw [Matrix.mulVec_mulVec, ← hPW, ← Matrix.mulVec_mulVec, hd]
  -- the stable part: `J_sᵗs = s → 0`
  have hs : (P *ᵥ d) ∘ Sum.inl = 0 := by
    have h1 : Js *ᵥ ((P *ᵥ d) ∘ Sum.inl) = (P *ᵥ d) ∘ Sum.inl := by
      rw [← blockDiag_mulVec_inl Js Ju, hJ]
    have hpow : ∀ k, (Js ^ k) *ᵥ ((P *ᵥ d) ∘ Sum.inl) = (P *ᵥ d) ∘ Sum.inl := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h1, ih]
    have := tendsto_of_isStableMatrix Js hJs ((P *ᵥ d) ∘ Sum.inl)
    simp only [hpow] at this
    exact tendsto_nhds_unique tendsto_const_nhds this
  -- the unstable part: a bounded `J_u`-orbit is zero
  have hu : (P *ᵥ d) ∘ Sum.inr = 0 := by
    have h1 : Ju *ᵥ ((P *ᵥ d) ∘ Sum.inr) = (P *ᵥ d) ∘ Sum.inr := by
      rw [← blockDiag_mulVec_inr Js Ju, hJ]
    have hpow : ∀ k, (Ju ^ k) *ᵥ ((P *ᵥ d) ∘ Sum.inr) = (P *ᵥ d) ∘ Sum.inr := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h1, ih]
    obtain ⟨hdet, hinv⟩ := isStableMatrix_inv Ju hJu
    obtain ⟨K, a, hKa⟩ := hasGeomDecay_of_isStableMatrix _ hinv
    exact eq_zero_of_bounded_orbit Ju⁻¹ Ju hKa (Matrix.nonsing_inv_mul _ hdet)
      (fun k => by rw [hpow k])
  have hP0 : P *ᵥ d = 0 := by
    funext i
    rcases i with i | i
    · exact congrFun hs i
    · exact congrFun hu i
  have : d = R *ᵥ (P *ᵥ d) := by rw [Matrix.mulVec_mulVec, hRP, Matrix.one_mulVec]
  rw [this, hP0, Matrix.mulVec_zero]

/-! ### Existence of a real block split -/

/-- An eigenvector of `J` transported by `R` is an eigenvector of `W`. -/
theorem eigen_transport {W : Matrix ι ι ℝ} {P : Matrix (σ ⊕ τ) ι ℝ} {R : Matrix ι (σ ⊕ τ) ℝ}
    {J : Matrix (σ ⊕ τ) (σ ⊕ τ) ℝ} (hPR : P * R = 1) (hWR : W * R = R * J) {μ : ℂ}
    {w : σ ⊕ τ → ℂ} (hw : w ≠ 0) (hJw : J.map Complex.ofRealHom *ᵥ w = μ • w) :
    cplxEnd W (R.map Complex.ofRealHom *ᵥ w) = μ • (R.map Complex.ofRealHom *ᵥ w) ∧
      R.map Complex.ofRealHom *ᵥ w ≠ 0 := by
  classical
  set f := Complex.ofRealHom
  refine ⟨?_, fun h0 => hw ?_⟩
  · rw [cplxEnd, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hWR,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, hJw, Matrix.mulVec_smul]
  · have : P.map f *ᵥ (R.map f *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPR,
        Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_mulVec]
    rw [← this, h0, Matrix.mulVec_zero]

/-- **A real block split exists** (Miao, pp. 18–20) when `W` has no eigenvalue on the unit
circle: with `n_s = dim E_s` (the number of stable characteristic roots with multiplicity,
`finrank_stableR`) and `n_u = dim E_u`, there are a real invertible `P` and blocks `J_s`
(`n_s × n_s`, stable) and `J_u` (`n_u × n_u`, all eigenvalues of modulus `> 1`) with
`PWP⁻¹ = diag(J_s, J_u)`. -/
theorem exists_real_block_split (W : Matrix ι ι ℝ)
    (hW : ∀ μ : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (W.map Complex.ofRealHom)) μ →
      ‖μ‖ ≠ 1) :
    ∃ (P : Matrix (Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W))) ι ℝ)
      (R : Matrix ι (Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W))) ℝ)
      (Js : Matrix (Fin (finrank ℝ (stableR W))) (Fin (finrank ℝ (stableR W))) ℝ)
      (Ju : Matrix (Fin (finrank ℝ (unstableR W))) (Fin (finrank ℝ (unstableR W))) ℝ),
      IsRealBlockSplit W P R Js Ju := by
  set f := Complex.ofRealHom
  have hc := isCompl_stableR_unstableR W
  set bs := Module.finBasis ℝ (stableR W)
  set bu := Module.finBasis ℝ (unstableR W)
  set bb := (bs.prod bu).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hbl : ∀ a, bb (Sum.inl a) = (bs a : ι → ℝ) := fun a => by
    simp [bb, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  have hbr : ∀ b, bb (Sum.inr b) = (bu b : ι → ℝ) := fun b => by
    simp [bb, Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  set P := LinearMap.toMatrix' bb.equivFun.toLinearMap
  set R := LinearMap.toMatrix' bb.equivFun.symm.toLinearMap
  have hPv : ∀ v, P *ᵥ v = bb.equivFun v := fun v => LinearMap.toMatrix'_mulVec _ v
  have hRv : ∀ c, R *ᵥ c = bb.equivFun.symm c := fun c => LinearMap.toMatrix'_mulVec _ c
  have hPR : P * R = 1 := Matrix.toLin'.injective (LinearMap.ext fun c => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, hRv, hPv, Matrix.one_mulVec, LinearEquiv.apply_symm_apply])
  have hRP : R * P = 1 := Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, hPv, hRv, Matrix.one_mulVec, LinearEquiv.symm_apply_apply])
  have hRcol : ∀ j, R *ᵥ Pi.single j 1 = bb j := fun j => by
    rw [hRv, LinearEquiv.symm_apply_eq]
    funext i
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  set J := P * W * R
  -- `E_s` has no `u`-coordinates, `E_u` no `s`-coordinates
  have hPs : ∀ v ∈ stableR W, ∀ b, (P *ᵥ v) (Sum.inr b) = 0 := fun v hv b => by
    rw [hPv, Basis.equivFun_apply]
    simp only [bb, Basis.map_repr, LinearEquiv.trans_apply]
    have := Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hc (⟨v, hv⟩ : stableR W)
    simp only at this
    rw [this, Basis.prod_repr_inr, map_zero, Finsupp.zero_apply]
  have hPu : ∀ v ∈ unstableR W, ∀ a, (P *ᵥ v) (Sum.inl a) = 0 := fun v hv a => by
    rw [hPv, Basis.equivFun_apply]
    simp only [bb, Basis.map_repr, LinearEquiv.trans_apply]
    have := Submodule.prodEquivOfIsCompl_symm_apply_right _ _ hc (⟨v, hv⟩ : unstableR W)
    simp only at this
    rw [this, Basis.prod_repr_inl, map_zero, Finsupp.zero_apply]
  have hJcol : ∀ j, J *ᵥ Pi.single j 1 = P *ᵥ (W *ᵥ bb j) := fun j => by
    rw [← hRcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hJ12 : J.toBlocks₁₂ = 0 := by
    ext a b
    have := congrFun (hJcol (Sum.inr b)) (Sum.inl a)
    rw [Matrix.mulVec_single_one, hbr] at this
    simp only [Matrix.col_apply] at this
    rw [Matrix.toBlocks₁₂, Matrix.of_apply, this, Matrix.zero_apply]
    exact hPu _ (unstableR_invariant W (bu b).2) a
  have hJ21 : J.toBlocks₂₁ = 0 := by
    ext b a
    have := congrFun (hJcol (Sum.inl a)) (Sum.inr b)
    rw [Matrix.mulVec_single_one, hbl] at this
    simp only [Matrix.col_apply] at this
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, this, Matrix.zero_apply]
    exact hPs _ (stableR_invariant W (bs a).2) b
  have hJ : J = Matrix.fromBlocks J.toBlocks₁₁ 0 0 J.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks J, hJ12, hJ21]
  have hPW : P * W = J * P := by
    simp only [J]; rw [Matrix.mul_assoc, hRP, Matrix.mul_one]
  have hWR : W * R = R * J := by
    simp only [J]; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRP, Matrix.one_mul]
  -- the column `j` of `R` is `bb j`
  have hRmem : ∀ (w : _ → ℂ) (S : Submodule ℂ (ι → ℂ)), (∀ j, w j ≠ 0 → cplx (bb j) ∈ S) →
      R.map f *ᵥ w ∈ S := fun w S hS => by
    have hsum : R.map f *ᵥ w = ∑ j, w j • cplx (bb j) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, cplx]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hRcol, Matrix.mulVec_single_one, Matrix.col_apply, mul_comm]
      rfl
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : w j = 0
    · rw [hj, zero_smul]; exact S.zero_mem
    · exact S.smul_mem _ (hS j hj)
  have hJmap : J.map f = Matrix.fromBlocks (J.toBlocks₁₁.map f) 0 0 (J.toBlocks₂₂.map f) := by
    conv_lhs => rw [hJ]
    simp only [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f)]
  refine ⟨P, R, J.toBlocks₁₁, J.toBlocks₂₂, hPR, hRP, hJ ▸ hPW, fun μ hμ => ?_, fun μ hμ => ?_⟩
  · -- the stable block
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : J.toBlocks₁₁.map f *ᵥ w = μ • w := by
      simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hw.1
    set w' : Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W)) → ℂ := Sum.elim w 0
    have hw' : w' ≠ 0 := fun h => hw.2 (by funext a; exact congrFun h (Sum.inl a))
    have hJw : J.map f *ᵥ w' = μ • w' := by
      rw [hJmap, Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i <;> simp [w', hw1]
    obtain ⟨hev, hne⟩ := eigen_transport hPR hWR hw' hJw
    have hmem : R.map f *ᵥ w' ∈ stableSubspace (cplxEnd W) :=
      hRmem w' _ fun j hj => by
        rcases j with a | b
        · rw [hbl]; exact (bs a).2
        · exact absurd rfl hj
    by_contra hge
    push Not at hge
    have hU : R.map f *ᵥ w' ∈ unstableSubspace (cplxEnd W) :=
      le_biSup (fun μ => (cplxEnd W).maxGenEigenspace μ) (show μ ∈ {μ : ℂ | 1 ≤ ‖μ‖} from hge)
        (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hev))
    exact hne ((Submodule.disjoint_def.1 (disjoint_stable_unstable _)) _ hmem hU)
  · -- the unstable block
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : J.toBlocks₂₂.map f *ᵥ w = μ • w := by
      simpa [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.1 hw.1
    set w' : Fin (finrank ℝ (stableR W)) ⊕ Fin (finrank ℝ (unstableR W)) → ℂ := Sum.elim 0 w
    have hw' : w' ≠ 0 := fun h => hw.2 (by funext a; exact congrFun h (Sum.inr a))
    have hJw : J.map f *ᵥ w' = μ • w' := by
      rw [hJmap, Matrix.fromBlocks_mulVec]
      funext i
      rcases i with i | i <;> simp [w', hw1]
    obtain ⟨hev, hne⟩ := eigen_transport hPR hWR hw' hJw
    have hmem : R.map f *ᵥ w' ∈ unstableSubspace (cplxEnd W) :=
      hRmem w' _ fun j hj => by
        rcases j with a | b
        · exact absurd rfl hj
        · rw [hbr]; exact (bu b).2
    have h1 := hW μ (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hev, hne⟩)
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hS : R.map f *ᵥ w' ∈ stableSubspace (cplxEnd W) :=
        le_biSup (fun μ => (cplxEnd W).maxGenEigenspace μ) (show μ ∈ {μ : ℂ | ‖μ‖ < 1} from hlt)
          (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hev))
      exact absurd ((Submodule.disjoint_def.1 (disjoint_stable_unstable _)) _ hS hmem) hne
    · exact hgt

end Miao.RationalExpectations
