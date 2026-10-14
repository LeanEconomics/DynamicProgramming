/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.StableManifold
import DeterministicDynamics.EulerLinear

/-!
# The Euler equation as a difference equation

SLP §6.4, p. 153, proof of Theorem 6.9. With `F_xy` nonsingular, the Euler equation
`G(x, y, z) = F_y(x, y) + βF_x(y, z) = 0` defines `z = ζ(x, y)` near the stationary point
(`exists_eulerZeta`). The map `Ψ(x, y, z) = (x, y, G(x, y, z))` has invertible derivative
`Ψ'` (`psiCLE`), and `ζ` is the last component of its local inverse at `(x, y, 0)`. Its
derivative is `(u, v) ↦ Ku + Jv`, with `J` and `K` the blocks of the matrix `A` of (4).
-/

open Set Filter Topology Module
open scoped Matrix

namespace StokeyLucasPrescott.DeterministicDynamics

variable {l : ℕ}

/-- `(u, v) ↦ Mu + Nv`. -/
noncomputable def blockCLM (M N : Matrix (Fin l) (Fin l) ℝ) :
    (Fin l → ℝ) × (Fin l → ℝ) →L[ℝ] (Fin l → ℝ) :=
  (clmOf M).comp (ContinuousLinearMap.fst ℝ _ _) + (clmOf N).comp (ContinuousLinearMap.snd ℝ _ _)

theorem blockCLM_apply (M N : Matrix (Fin l) (Fin l) ℝ) (p : (Fin l → ℝ) × (Fin l → ℝ)) :
    blockCLM M N p = M *ᵥ p.1 + N *ᵥ p.2 := rfl

/-- The Euler residual `G(x, y, z) = F_y(x, y) + βF_x(y, z)`. -/
def eulerG (Fx Fy : (Fin l → ℝ) → (Fin l → ℝ) → (Fin l → ℝ)) (β : ℝ)
    (q : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) : Fin l → ℝ :=
  Fy q.1 q.2.1 + β • Fx q.2.1 q.2.2

/-- `Ψ(x, y, z) = (x, y, G(x, y, z))`. -/
def eulerPsi (Fx Fy : (Fin l → ℝ) → (Fin l → ℝ) → (Fin l → ℝ)) (β : ℝ)
    (q : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) :
    (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ) :=
  (q.1, q.2.1, eulerG Fx Fy β q)

/-- `Ψ'(u, v, w) = (u, v, F'_xy u + F_yy v + β(F_xx v + F_xy w))`. -/
noncomputable def psiLin (Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) :
    ((Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) →ₗ[ℝ]
      ((Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) where
  toFun q := (q.1, q.2.1, Fxyᵀ *ᵥ q.1 + Fyy *ᵥ q.2.1 + β • (Fxx *ᵥ q.2.1 + Fxy *ᵥ q.2.2))
  map_add' q q' := by
    simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, smul_add, Prod.mk_add_mk]
    congr 2; abel
  map_smul' c q := by
    simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, RingHom.id_apply,
      Prod.smul_mk, smul_add, smul_comm β c]

/-- The inverse of `Ψ'`. -/
noncomputable def psiInvLin (Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) :
    ((Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) →ₗ[ℝ]
      ((Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) where
  toFun q := (q.1, q.2.1,
    Fxy⁻¹ *ᵥ (β⁻¹ • (q.2.2 - Fxyᵀ *ᵥ q.1 - Fyy *ᵥ q.2.1) - Fxx *ᵥ q.2.1))
  map_add' q q' := by
    simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, smul_add, Prod.mk_add_mk,
      Matrix.mulVec_sub, smul_sub]
    congr 2; abel
  map_smul' c q := by
    simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, RingHom.id_apply,
      Prod.smul_mk, smul_sub, Matrix.mulVec_sub, smul_comm β⁻¹ c]

theorem psi_inv_left {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hQ : Fxy.det ≠ 0)
    (hβ : β ≠ 0) (q : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) :
    psiInvLin Fxx Fxy Fyy β (psiLin Fxx Fxy Fyy β q) = q := by
  obtain ⟨u, v, w⟩ := q
  simp only [psiInvLin, psiLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  simp only
  have e : β⁻¹ • (Fxyᵀ *ᵥ u + Fyy *ᵥ v + β • (Fxx *ᵥ v + Fxy *ᵥ w) - Fxyᵀ *ᵥ u - Fyy *ᵥ v) -
      Fxx *ᵥ v = Fxy *ᵥ w := by
    rw [show Fxyᵀ *ᵥ u + Fyy *ᵥ v + β • (Fxx *ᵥ v + Fxy *ᵥ w) - Fxyᵀ *ᵥ u - Fyy *ᵥ v =
      β • (Fxx *ᵥ v + Fxy *ᵥ w) by abel, smul_smul, inv_mul_cancel₀ hβ, one_smul]
    abel
  rw [e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ),
    Matrix.one_mulVec]

theorem psi_inv_right {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hQ : Fxy.det ≠ 0)
    (hβ : β ≠ 0) (q : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) :
    psiLin Fxx Fxy Fyy β (psiInvLin Fxx Fxy Fyy β q) = q := by
  obtain ⟨u, v, s⟩ := q
  simp only [psiInvLin, psiLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  simp only
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ),
    Matrix.one_mulVec]
  simp only [smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hβ, one_smul]
  abel

/-- `Ψ'` as a continuous linear equivalence. -/
noncomputable def psiCLE (Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ) (β : ℝ) (hQ : Fxy.det ≠ 0)
    (hβ : β ≠ 0) :
    ((Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) ≃L[ℝ]
      ((Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) :=
  LinearEquiv.toContinuousLinearEquiv
    { psiLin Fxx Fxy Fyy β with
      invFun := psiInvLin Fxx Fxy Fyy β
      left_inv := psi_inv_left hQ hβ
      right_inv := psi_inv_right hQ hβ }

theorem psiCLE_apply {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hQ : Fxy.det ≠ 0)
    (hβ : β ≠ 0) (q : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) :
    psiCLE Fxx Fxy Fyy β hQ hβ q = psiLin Fxx Fxy Fyy β q := rfl

theorem psiCLE_symm_apply {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ} {β : ℝ} (hQ : Fxy.det ≠ 0)
    (hβ : β ≠ 0) (q : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ)) :
    (psiCLE Fxx Fxy Fyy β hQ hβ).symm q = psiInvLin Fxx Fxy Fyy β q := rfl

variable {Fx Fy : (Fin l → ℝ) → (Fin l → ℝ) → (Fin l → ℝ)} {Fxx Fxy Fyy : Matrix (Fin l) (Fin l) ℝ}
  {β : ℝ} {xbar : Fin l → ℝ}

/-- `Ψ` is strictly differentiable at `(x̄, x̄, x̄)` with derivative `Ψ'`. -/
theorem hasStrictFDerivAt_psi (hQ : Fxy.det ≠ 0) (hβ : β ≠ 0)
    (hFx : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fx p.1 p.2)
      (blockCLM Fxx Fxy) (xbar, xbar))
    (hFy : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fy p.1 p.2)
      (blockCLM Fxyᵀ Fyy) (xbar, xbar)) :
    HasStrictFDerivAt (eulerPsi Fx Fy β)
      ((psiCLE Fxx Fxy Fyy β hQ hβ : _ ≃L[ℝ] _) : _ →L[ℝ] _) (xbar, xbar, xbar) := by
  set L1 : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ) →L[ℝ] (Fin l → ℝ) × (Fin l → ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
  set L2 : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ) →L[ℝ] (Fin l → ℝ) × (Fin l → ℝ) :=
    ContinuousLinearMap.snd ℝ _ _
  have hG1 := hFy.comp (xbar, xbar, xbar) L1.hasStrictFDerivAt
  have hG2 := hFx.comp (xbar, xbar, xbar) L2.hasStrictFDerivAt
  have hG := hG1.add (hG2.const_smul β)
  have hΨ := (hasStrictFDerivAt_fst (p := (xbar, xbar, xbar))).prodMk
    ((hasStrictFDerivAt_fst.comp (xbar, xbar, xbar) hasStrictFDerivAt_snd).prodMk hG)
  have hΨ' : HasStrictFDerivAt (eulerPsi Fx Fy β) _ (xbar, xbar, xbar) := hΨ
  refine hΨ'.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
  change _ = psiLin Fxx Fxy Fyy β q
  simp only [psiLin, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_snd', _root_.add_apply, FunLike.coe_smul,
    Pi.smul_apply, blockCLM_apply, L1, L2, smul_add]

/-- **The Euler map.** Near the stationary point, `G(x, y, z) = 0` is solved by `z = ζ(x, y)`,
with `ζ(x̄, x̄) = x̄` and derivative `(u, v) ↦ Ku + Jv`. -/
theorem exists_eulerZeta (hQ : Fxy.det ≠ 0) (hβ : β ≠ 0)
    (hstat : eulerG Fx Fy β (xbar, xbar, xbar) = 0)
    (hFx : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fx p.1 p.2)
      (blockCLM Fxx Fxy) (xbar, xbar))
    (hFy : HasStrictFDerivAt (fun p : (Fin l → ℝ) × (Fin l → ℝ) => Fy p.1 p.2)
      (blockCLM Fxyᵀ Fyy) (xbar, xbar)) :
    ∃ ζ : (Fin l → ℝ) × (Fin l → ℝ) → (Fin l → ℝ), ζ (xbar, xbar) = xbar ∧
      (∀ᶠ p in 𝓝 (xbar, xbar), eulerG Fx Fy β (p.1, p.2, ζ p) = 0) ∧
      HasStrictFDerivAt ζ (blockCLM (eulerK Fxy β) (eulerJ Fxx Fxy Fyy β)) (xbar, xbar) := by
  have hΨ := hasStrictFDerivAt_psi (Fxx := Fxx) hQ hβ hFx hFy
  set inv := hΨ.localInverse (eulerPsi Fx Fy β) _ (xbar, xbar, xbar)
  set emb : (Fin l → ℝ) × (Fin l → ℝ) →L[ℝ] (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).prod ((ContinuousLinearMap.snd ℝ _ _).prod 0)
  have hemb : emb (xbar, xbar) = eulerPsi Fx Fy β (xbar, xbar, xbar) := by
    simp [emb, eulerPsi, hstat]
  set π3 : (Fin l → ℝ) × (Fin l → ℝ) × (Fin l → ℝ) →L[ℝ] (Fin l → ℝ) :=
    (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  refine ⟨fun p => π3 (inv (emb p)), ?_, ?_, ?_⟩
  · change π3 (inv (emb (xbar, xbar))) = xbar
    rw [hemb]
    simp only [inv, hΨ.localInverse_apply_image]
    rfl
  · have ht : Tendsto emb (𝓝 (xbar, xbar)) (𝓝 (eulerPsi Fx Fy β (xbar, xbar, xbar))) := by
      rw [← hemb]; exact emb.continuous.tendsto _
    filter_upwards [ht.eventually hΨ.eventually_right_inverse] with p hp
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg (fun q => q.2.1) hp
    have h3 := congrArg (fun q => q.2.2) hp
    simp only [eulerPsi, emb, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', _root_.zero_apply] at h1 h2 h3
    have e : inv (emb p) = (p.1, p.2, π3 (inv (emb p))) := by
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · exact h1
      · exact h2
    rw [← e]
    exact h3
  · have hinv := hΨ.to_localInverse
    rw [← hemb] at hinv
    have := (π3.hasStrictFDerivAt.comp _ hinv).comp (xbar, xbar) emb.hasStrictFDerivAt
    refine this.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
    change π3 (psiInvLin Fxx Fxy Fyy β (emb p)) = _
    obtain ⟨u, v⟩ := p
    simp only [π3, emb, psiInvLin, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', _root_.zero_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, blockCLM_apply, eulerK, eulerJ]
    simp only [Matrix.neg_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_add, smul_add, smul_smul,
      inv_mul_cancel₀ hβ, one_smul, smul_sub, zero_sub, Matrix.mulVec_neg, smul_neg]
    abel

/-- The stacked map `H(x_{t+1}, x_t) = (ζ(x_t, x_{t+1}), x_{t+1})` on `ℝˡ ⊕ ℝˡ`. -/
def stackH (ζ : (Fin l → ℝ) × (Fin l → ℝ) → (Fin l → ℝ)) (Y : Fin l ⊕ Fin l → ℝ) :
    Fin l ⊕ Fin l → ℝ :=
  Sum.elim (ζ (Y ∘ Sum.inr, Y ∘ Sum.inl)) (Y ∘ Sum.inl)

/-- **`H` has Jacobian `A` at the stationary point.** -/
theorem hasStrictFDerivAt_stackH {ζ : (Fin l → ℝ) × (Fin l → ℝ) → (Fin l → ℝ)}
    (hζ : HasStrictFDerivAt ζ (blockCLM (eulerK Fxy β) (eulerJ Fxx Fxy Fyy β)) (xbar, xbar)) :
    HasStrictFDerivAt (stackH ζ) (clmOf (eulerA Fxx Fxy Fyy β)) (Sum.elim xbar xbar) := by
  set πr : (Fin l ⊕ Fin l → ℝ) →L[ℝ] (Fin l → ℝ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℝ ℝ Sum.inr)
  set πl : (Fin l ⊕ Fin l → ℝ) →L[ℝ] (Fin l → ℝ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℝ ℝ Sum.inl)
  set S : ((Fin l → ℝ) × (Fin l → ℝ)) →L[ℝ] (Fin l ⊕ Fin l → ℝ) :=
    LinearMap.toContinuousLinearMap
      (LinearEquiv.sumArrowLequivProdArrow (Fin l) (Fin l) ℝ ℝ).symm.toLinearMap
  have h1 := hζ.comp (Sum.elim xbar xbar) (πr.prod πl).hasStrictFDerivAt
  have h := S.hasStrictFDerivAt.comp (Sum.elim xbar xbar) (h1.prodMk πl.hasStrictFDerivAt)
  have hf : (fun Y => S (ζ ((πr.prod πl) Y), πl Y)) = stackH ζ := by
    funext Y s
    rcases s with i | i <;> rfl
  rw [hf] at h
  refine h.congr_fderiv (ContinuousLinearMap.ext fun Y => funext fun s => ?_)
  rcases s with i | i
  · change (blockCLM (eulerK Fxy β) (eulerJ Fxx Fxy Fyy β) (Y ∘ Sum.inr, Y ∘ Sum.inl)) i =
      (eulerA Fxx Fxy Fyy β *ᵥ Y) (Sum.inl i)
    rw [eulerA_mulVec_inl, blockCLM_apply, add_comm]
  · change Y (Sum.inl i) = (eulerA Fxx Fxy Fyy β *ᵥ Y) (Sum.inr i)
    rw [eulerA_mulVec_inr]

end StokeyLucasPrescott.DeterministicDynamics
