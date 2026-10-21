/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Irreducibility.LinearRestriction

/-!
# Further claims of Chapter 4

Text claims of MT Chapter 4 not covered by the other modules.

* `ar_isPhiIrreducible` (MT p. 89): the AR(k) model with an innovation law equivalent to
  Lebesgue measure (an everywhere positive density, e.g. Gaussian) is `μ_Leb`-irreducible on
  `ℝᵏ` for any coefficients, with Lebesgue measure maximal and every set of positive measure
  uniformly accessible from every compact set (Propositions 4.4.2, 4.4.3 and the state space
  form (2.1)).
* `range_gramian` (MT p. 93): the range of the controllability Gramian `Σ_k` equals the range of
  `C_k`, not only its rank; `range_gramian_n`: for `k = n` both are `X₀`.
* `isControllable_of_rank_G`, `lss_fullRank_G_irreducible` (MT p. 92): if `p = n` and `G` has full
  rank, `(F, G)` is controllable, so the Gaussian LSS(F, G) is `μ_Leb`-irreducible.
* `finrank_ctrbSubspace` (MT p. 93): `dim X₀ = rank C_n`; `finrank_ctrbSubspace_lt`: if `(F, G)` is
  not controllable, `dim X₀ < n`.
* `countable_absorbing_classes` (MT (4.8), p. 81): on a countable space the decomposition (4.5) is
  a Doeblin decomposition, with countably many absorbing classes. The general-space Doeblin
  decomposition (4.8) is not a precise claim of the book ("`D` in some sense ephemeral") and is
  explicitly not discussed there.
* `unifAccessible_not_refl` (MT p. 86): `⇝` is not reflexive.

**Corrections.** None.
-/

namespace MeynTweedie.Irreducibility

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal Matrix

/-! ### AR(k) -/

/-- An innovation law on `ℝ` equivalent to Lebesgue measure, viewed on `ℝ¹`, is equivalent to
Lebesgue measure on `ℝ¹`. -/
theorem map_fin_one_equiv (Γ : Measure ℝ) (h1 : Γ ≪ volume) (h2 : volume ≪ Γ) :
    Γ.map (fun w _ => w : ℝ → Fin 1 → ℝ) ≪ volume ∧
      volume ≪ Γ.map (fun w _ => w : ℝ → Fin 1 → ℝ) := by
  have he : (fun w _ => w : ℝ → Fin 1 → ℝ) = ⇑(MeasurableEquiv.funUnique (Fin 1) ℝ).symm := rfl
  have hv : (volume : Measure ℝ).map (MeasurableEquiv.funUnique (Fin 1) ℝ).symm =
      (volume : Measure (Fin 1 → ℝ)) :=
    ((volume_preserving_funUnique (Fin 1) ℝ).symm _).map_eq
  rw [he, ← hv]
  exact ⟨h1.map (MeasurableEquiv.measurable _), h2.map (MeasurableEquiv.measurable _)⟩

/-- MT p. 89 (with Propositions 4.4.2 and 4.4.3): the AR(k) model `Yₙ = Σ αᵢ Yₙ₋ᵢ + Wₙ` in its
state space form on `ℝᵏ`, with an innovation law equivalent to Lebesgue measure, is
`φ`-irreducible for every `φ ≪ μ_Leb` whatever the coefficients `α`; Lebesgue measure is a
maximal irreducibility measure, and `A ⇝ B` for compact `A` and `μ_Leb(B) > 0`. -/
theorem ar_isPhiIrreducible {k : ℕ} (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h1 : Γ ≪ volume)
    (h2 : volume ≪ Γ) (α : Fin k → ℝ) :
    ∃ _ : IsMarkovKernel (arKernel Γ α),
      (∀ φ : Measure (Fin k → ℝ), φ ≪ volume → IsPhiIrreducible (arKernel Γ α) φ) ∧
      IsMaximalIrreducibility (arKernel Γ α) volume ∧
      ∀ A B : Set (Fin k → ℝ), IsCompact A → MeasurableSet B → 0 < volume B →
        UnifAccessible (arKernel Γ α) A B := by
  obtain ⟨g1, g2⟩ := map_fin_one_equiv Γ h1 h2
  have hP : IsProbabilityMeasure (Γ.map (fun w _ => w : ℝ → Fin 1 → ℝ)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_pi_iff.mpr fun _ => measurable_id).aemeasurable).2 inferInstance
  have heq := arKernel_eq_lssMatrixKernel Γ α
  rw [heq]
  exact proposition_4_4_3 _ (proposition_4_4_2 α).2 g1 g2

/-! ### The Gramian and the controllable subspace -/

variable {n p : ℕ}

/-- MT p. 93: the range of the Gramian `Σ_k = C_k C_kᵀ` equals the range of `C_k`. -/
theorem range_gramian (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) (k : ℕ) :
    LinearMap.range (gramian F G k).mulVecLin = LinearMap.range (ctrbMap F G k) := by
  rw [← range_ctrbMatrix]
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro x ⟨v, rfl⟩
    refine ⟨(ctrbMatrix F G k)ᵀ *ᵥ v, ?_⟩
    simp only [mulVecLin_apply, mulVec_mulVec, gramian_eq]
  · have := rank_gramian F G k
    exact this

/-- MT p. 93: the range of `Σ_n` is the controllable subspace `X₀`. -/
theorem range_gramian_n (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    LinearMap.range (gramian F G n).mulVecLin = ctrbSubspace F G :=
  range_gramian F G n

/-- MT p. 93: `dim X₀ = rank C_n`. -/
theorem finrank_ctrbSubspace (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ) :
    Module.finrank ℝ (ctrbSubspace F G) = (ctrbMatrix F G n).rank := by
  rw [Matrix.rank, range_ctrbMatrix]

/-- MT p. 93: if `(F, G)` is not controllable, `X₀` has dimension strictly less than `n`. -/
theorem finrank_ctrbSubspace_lt (F : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (h : ¬ IsControllable F G) : Module.finrank ℝ (ctrbSubspace F G) < n := by
  rw [finrank_ctrbSubspace]
  have hle : (ctrbMatrix F G n).rank ≤ n := by
    rw [← finrank_ctrbSubspace]
    simpa using Submodule.finrank_le (ctrbSubspace F G)
  rw [isControllable_iff_rank] at h
  exact lt_of_le_of_ne hle h

/-- MT p. 92: if `p = n` and `G` has full rank, `(F, G)` is controllable (in one step). -/
theorem isControllable_of_rank_G (F G : Matrix (Fin n) (Fin n) ℝ) (hG : G.rank = n) :
    IsControllable F G := by
  rw [isControllable_iff_exists_rank]
  refine ⟨1, (rank_ctrbMatrix_eq_iff F G 1).2 (eq_top_iff.2 fun x _ => ?_)⟩
  have hG' : LinearMap.range G.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [← Matrix.rank, hG, Module.finrank_fin_fun])
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 hG' x
  refine ⟨fun _ => v, ?_⟩
  rw [ctrbMap_apply, Fin.sum_univ_one]
  simpa using hv

/-- MT p. 92: with `p = n`, `G` of full rank and Gaussian noise, LSS(F, G) is
`μ_Leb`-irreducible, with Lebesgue measure maximal. -/
theorem lss_fullRank_G_irreducible (F G : Matrix (Fin n) (Fin n) ℝ) (hG : G.rank = n) :
    ∃ _ : IsMarkovKernel (lssMatrixKernel (Measure.pi fun _ : Fin n => gaussianReal 0 1) F G),
      (∀ φ : Measure (Fin n → ℝ), φ ≪ volume →
        IsPhiIrreducible (lssMatrixKernel (Measure.pi fun _ : Fin n => gaussianReal 0 1) F G) φ) ∧
      IsMaximalIrreducibility (lssMatrixKernel (Measure.pi fun _ : Fin n => gaussianReal 0 1) F G)
        volume := by
  obtain ⟨hM, h1, h2, -⟩ := proposition_4_4_3_gaussian (isControllable_of_rank_G F G hG)
  exact ⟨hM, h1, h2⟩

/-! ### Countable chains and accessibility -/

/-- MT (4.8), p. 81: on a countable space, (4.5) is a Doeblin decomposition: `X` is the union of
countably many disjoint absorbing communicating classes and the remainder `D`. -/
theorem countable_absorbing_classes {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] (P : Kernel X X) [IsMarkovKernel P] :
    (commClass P '' {x | IsAbsorbing P (commClass P x)}).Countable ∧
      (∀ C ∈ commClass P '' {x | IsAbsorbing P (commClass P x)}, IsAbsorbing P C) ∧
      (⋃₀ (commClass P '' {x | IsAbsorbing P (commClass P x)})) ∪ nonAbsorbingPart P = univ := by
  refine ⟨(Set.to_countable _).image _, ?_, ?_⟩
  · rintro C ⟨x, hx, rfl⟩
    exact hx
  · rw [sUnion_image]
    exact decomposition_4_5 P

/-- MT p. 86: `⇝` is not reflexive. For the chain on `Bool` that jumps to `false` and stays
there, `{true}` is not even accessible from itself. -/
theorem unifAccessible_not_refl :
    ∃ _ : IsMarkovKernel (Kernel.const Bool (Measure.dirac false)),
      ¬ UnifAccessible (Kernel.const Bool (Measure.dirac false)) {true} {true} := by
  have hM : IsMarkovKernel (Kernel.const Bool (Measure.dirac false)) := inferInstance
  refine ⟨hM, fun ⟨δ, hδ, h⟩ => ?_⟩
  have h0 : hitProb (Kernel.const Bool (Measure.dirac false)) {true} true = 0 := by
    by_contra hc
    obtain ⟨n, hn⟩ := (hitProb_pos_iff _ (measurableSet_singleton true) true).1
      (pos_iff_ne_zero.2 hc)
    rw [pow_succ_apply' _ n true (measurableSet_singleton true)] at hn
    simp at hn
  have := h true (mem_singleton true)
  rw [h0] at this
  exact hδ.ne' (nonpos_iff_eq_zero.1 this)

end MeynTweedie.Irreducibility
