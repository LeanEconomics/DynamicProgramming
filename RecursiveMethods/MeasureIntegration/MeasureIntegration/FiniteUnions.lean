/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.Extension

/-!
# Finite unions of a semialgebra

The common structure behind Exercises 7.6 and 7.27, Theorem 7.13 and Exercise 7.29. A
*semialgebra* `𝒞` (`IsSemialgebra`) contains `∅` and the whole space, is closed under
intersections, and the complement of each member is a finite disjoint union of members: the
half-open intervals of `ℝ`, and the measurable rectangles of a product, are examples.

* The finite unions of members of `𝒞` form an algebra (`isSetAlgebra_finUnions`), the smallest
  one containing `𝒞` (`finUnions_subset`).
* Each finite union is a finite **disjoint** union of members (`exists_disjoint_rep`).
* A function `μ` on `𝒞` with `μ(∅) = 0` that is countably additive on `𝒞` has a well-defined
  additive extension to the finite unions (`sum_eq_of_rep`, `semiExtend`), which agrees with `μ`
  on `𝒞` (`semiExtend_of_mem`) and is a measure on the algebra of finite unions
  (`semiExtend_isAlgebraMeasure`). This is the argument of SLP's proof of Theorem 7.13, completed
  with the countable additivity that the book leaves implicit.
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory Function
open scoped ENNReal

variable {α : Type*}

/-- A **semialgebra** of subsets of `α`. -/
structure IsSemialgebra (𝒞 : Set (Set α)) : Prop where
  empty_mem : ∅ ∈ 𝒞
  univ_mem : univ ∈ 𝒞
  inter_mem : ∀ A ∈ 𝒞, ∀ B ∈ 𝒞, A ∩ B ∈ 𝒞
  compl_eq : ∀ A ∈ 𝒞, ∃ K : Finset (Set α), ↑K ⊆ 𝒞 ∧
    (↑K : Set (Set α)).PairwiseDisjoint id ∧ Aᶜ = ⋃₀ ↑K

/-- The finite unions of members of `𝒞`. -/
def finUnions (𝒞 : Set (Set α)) : Set (Set α) :=
  {A | ∃ I : Finset (Set α), ↑I ⊆ 𝒞 ∧ A = ⋃₀ ↑I}

theorem sUnion_inter_sUnion [DecidableEq (Set α)] (I J : Finset (Set α)) :
    ⋃₀ (↑I : Set (Set α)) ∩ ⋃₀ ↑J = ⋃₀ ↑(Finset.image₂ (· ∩ ·) I J) := by
  ext x
  simp only [mem_inter_iff, mem_sUnion, Finset.mem_coe, Finset.mem_image₂]
  constructor
  · rintro ⟨⟨P, hP, hxP⟩, ⟨Q, hQ, hxQ⟩⟩
    exact ⟨P ∩ Q, ⟨P, hP, Q, hQ, rfl⟩, hxP, hxQ⟩
  · rintro ⟨_, ⟨P, hP, Q, hQ, rfl⟩, hxP, hxQ⟩
    exact ⟨⟨P, hP, hxP⟩, Q, hQ, hxQ⟩

variable {𝒞 : Set (Set α)}

theorem subset_finUnions : 𝒞 ⊆ finUnions 𝒞 := fun A hA => ⟨{A}, by simpa using hA, by simp⟩

theorem finUnions_inter (h : IsSemialgebra 𝒞) {A B : Set α} (hA : A ∈ finUnions 𝒞)
    (hB : B ∈ finUnions 𝒞) : A ∩ B ∈ finUnions 𝒞 := by
  classical
  obtain ⟨I, hI, rfl⟩ := hA
  obtain ⟨J, hJ, rfl⟩ := hB
  refine ⟨Finset.image₂ (· ∩ ·) I J, fun X hX => ?_, sUnion_inter_sUnion I J⟩
  simp only [Finset.coe_image₂, mem_image2] at hX
  obtain ⟨P, hP, Q, hQ, rfl⟩ := hX
  exact h.inter_mem P (hI hP) Q (hJ hQ)

theorem finUnions_compl (h : IsSemialgebra 𝒞) {A : Set α} (hA : A ∈ finUnions 𝒞) :
    Aᶜ ∈ finUnions 𝒞 := by
  classical
  obtain ⟨I, hI, rfl⟩ := hA
  induction I using Finset.induction_on with
  | empty => exact ⟨{univ}, by simpa using h.univ_mem, by simp⟩
  | insert R I _ ih =>
    rw [Finset.coe_insert, sUnion_insert, compl_union]
    have hR : R ∈ 𝒞 := hI (by simp)
    obtain ⟨K, hK, -, hKeq⟩ := h.compl_eq R hR
    exact finUnions_inter h ⟨K, hK, hKeq⟩
      (ih fun P hP => hI (by simp only [Finset.coe_insert]; exact Or.inr hP))

/-- The finite unions of a semialgebra form an algebra (Exercises 7.6a and 7.27). -/
theorem isSetAlgebra_finUnions (h : IsSemialgebra 𝒞) : IsSetAlgebra (finUnions 𝒞) := by
  classical
  refine ⟨⟨∅, by simp, by simp⟩, fun A hA => finUnions_compl h hA, ?_⟩
  rintro _ _ ⟨I, hI, rfl⟩ ⟨J, hJ, rfl⟩
  exact ⟨I ∪ J, by simp [hI, hJ], by simp [sUnion_union]⟩

/-- Every algebra containing `𝒞` contains its finite unions. -/
theorem finUnions_subset {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜) (h : 𝒞 ⊆ 𝒜) :
    finUnions 𝒞 ⊆ 𝒜 := by
  rintro _ ⟨I, hI, rfl⟩
  have := h𝒜.biUnion_mem (s := id) I fun P hP => h (hI hP)
  simpa [sUnion_eq_biUnion] using this

/-- Each finite union of members of a semialgebra is a finite disjoint union of members (the
hint to Exercise 7.6a; Exercise 7.27). -/
theorem exists_disjoint_rep (h : IsSemialgebra 𝒞) {A : Set α} (hA : A ∈ finUnions 𝒞) :
    ∃ J : Finset (Set α), ↑J ⊆ 𝒞 ∧ (↑J : Set (Set α)).PairwiseDisjoint id ∧ A = ⋃₀ ↑J := by
  classical
  obtain ⟨I, hI, rfl⟩ := hA
  induction I using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert R I _ ih =>
    have hRC : R ∈ 𝒞 := hI (by simp)
    obtain ⟨J, hJ, hJd, hJeq⟩ :=
      ih fun P hP => hI (by simp only [Finset.coe_insert]; exact Or.inr hP)
    obtain ⟨K, hK, hKd, hKeq⟩ := h.compl_eq R hRC
    refine ⟨insert R (Finset.image₂ (· ∩ ·) J K), ?_, ?_, ?_⟩
    · intro X hX
      simp only [Finset.coe_insert, Finset.coe_image₂, mem_insert_iff, mem_image2] at hX
      rcases hX with rfl | ⟨P, hP, Q, hQ, rfl⟩
      · exact hRC
      · exact h.inter_mem P (hJ hP) Q (hK hQ)
    · rw [Finset.coe_insert]
      refine PairwiseDisjoint.insert ?_ ?_
      · intro X hX Y hY hXY
        simp only [Finset.coe_image₂, mem_image2] at hX hY
        obtain ⟨P, hP, Q, hQ, rfl⟩ := hX
        obtain ⟨P', hP', Q', hQ', rfl⟩ := hY
        by_cases hPP : P = P'
        · subst hPP
          have hQQ : Q ≠ Q' := fun hQQ => hXY (by rw [hQQ])
          exact (hKd hQ hQ' hQQ).mono inter_subset_right inter_subset_right
        · exact (hJd hP hP' hPP).mono inter_subset_left inter_subset_left
      · intro Y hY _
        simp only [Finset.coe_image₂, mem_image2] at hY
        obtain ⟨P, -, Q, hQ, rfl⟩ := hY
        have hQR : Q ⊆ Rᶜ := hKeq ▸ subset_sUnion_of_mem hQ
        exact disjoint_compl_right.mono_right (inter_subset_right.trans hQR)
    · rw [Finset.coe_insert, Finset.coe_insert, sUnion_insert, sUnion_insert,
        ← sUnion_inter_sUnion, ← hJeq, ← hKeq]
      ext x
      simp only [mem_union, mem_inter_iff, mem_compl_iff]
      tauto

variable {μ : Set α → ℝ≥0∞}

/-- Splitting `P ∈ 𝒞` along a disjoint family covering it. -/
theorem sum_inter_eq (h : IsSemialgebra 𝒞) (hμ : IsCountablyAdditiveOn 𝒞 μ) (h0 : μ ∅ = 0)
    {P : Set α} (hP : P ∈ 𝒞) {J : Finset (Set α)} (hJ : ↑J ⊆ 𝒞)
    (hJd : (↑J : Set (Set α)).PairwiseDisjoint id) (hPJ : P ⊆ ⋃₀ ↑J) :
    μ P = ∑ Q ∈ J, μ (P ∩ Q) := by
  have hU : (⋃ Q : (↑J : Set (Set α)), P ∩ Q.1) = P := by
    rw [← inter_iUnion, ← sUnion_eq_iUnion, inter_eq_left.2 hPJ]
  have := hμ.countable h0 h.empty_mem (fun Q : (↑J : Set (Set α)) => P ∩ Q.1)
    (fun Q => h.inter_mem P hP Q.1 (hJ Q.2))
    (fun Q Q' hQQ => (hJd Q.2 Q'.2 (Subtype.coe_ne_coe.2 hQQ)).mono inter_subset_right
      inter_subset_right) (hU.symm ▸ hP)
  rw [hU] at this
  rw [this]
  exact Finset.tsum_subtype J fun Q => μ (P ∩ Q)

/-- **Well-definedness** (SLP's proof of Theorem 7.13): two disjoint representations of the same
set give the same sum. -/
theorem sum_eq_of_rep (h : IsSemialgebra 𝒞) (hμ : IsCountablyAdditiveOn 𝒞 μ) (h0 : μ ∅ = 0)
    {J J' : Finset (Set α)} (hJ : ↑J ⊆ 𝒞) (hJd : (↑J : Set (Set α)).PairwiseDisjoint id)
    (hJ' : ↑J' ⊆ 𝒞) (hJ'd : (↑J' : Set (Set α)).PairwiseDisjoint id)
    (heq : ⋃₀ (↑J : Set (Set α)) = ⋃₀ ↑J') : ∑ P ∈ J, μ P = ∑ Q ∈ J', μ Q := by
  calc ∑ P ∈ J, μ P = ∑ P ∈ J, ∑ Q ∈ J', μ (P ∩ Q) :=
        Finset.sum_congr rfl fun P hP => sum_inter_eq h hμ h0 (hJ hP) hJ' hJ'd
          (heq ▸ subset_sUnion_of_mem hP)
    _ = ∑ Q ∈ J', ∑ P ∈ J, μ (P ∩ Q) := Finset.sum_comm
    _ = ∑ Q ∈ J', μ Q := Finset.sum_congr rfl fun Q hQ => by
        rw [sum_inter_eq h hμ h0 (hJ' hQ) hJ hJd (heq.symm ▸ subset_sUnion_of_mem hQ)]
        exact Finset.sum_congr rfl fun P _ => by rw [inter_comm]

open Classical in
/-- The additive extension of `μ` from `𝒞` to its finite unions. -/
noncomputable def semiExtend (𝒞 : Set (Set α)) (μ : Set α → ℝ≥0∞) (A : Set α) : ℝ≥0∞ :=
  if h : ∃ J : Finset (Set α), ↑J ⊆ 𝒞 ∧ (↑J : Set (Set α)).PairwiseDisjoint id ∧ A = ⋃₀ ↑J
  then ∑ P ∈ h.choose, μ P else 0

theorem semiExtend_eq (h : IsSemialgebra 𝒞) (hμ : IsCountablyAdditiveOn 𝒞 μ) (h0 : μ ∅ = 0)
    {A : Set α} {J : Finset (Set α)} (hJ : ↑J ⊆ 𝒞)
    (hJd : (↑J : Set (Set α)).PairwiseDisjoint id) (hA : A = ⋃₀ ↑J) :
    semiExtend 𝒞 μ A = ∑ P ∈ J, μ P := by
  have hex : ∃ J : Finset (Set α), ↑J ⊆ 𝒞 ∧ (↑J : Set (Set α)).PairwiseDisjoint id ∧
      A = ⋃₀ ↑J := ⟨J, hJ, hJd, hA⟩
  rw [semiExtend, dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  exact sum_eq_of_rep h hμ h0 h1 h2 hJ hJd (h3.symm.trans hA)

/-- The extension agrees with `μ` on `𝒞`. -/
theorem semiExtend_of_mem (h : IsSemialgebra 𝒞) (hμ : IsCountablyAdditiveOn 𝒞 μ)
    (h0 : μ ∅ = 0) {A : Set α} (hA : A ∈ 𝒞) : semiExtend 𝒞 μ A = μ A := by
  classical
  rw [semiExtend_eq h hμ h0 (J := {A}) (by simpa using hA) (by simp) (by simp)]
  simp

/-- **The extension is a measure on the algebra of finite unions.** -/
theorem semiExtend_isAlgebraMeasure (h : IsSemialgebra 𝒞) (hμ : IsCountablyAdditiveOn 𝒞 μ)
    (h0 : μ ∅ = 0) : IsAlgebraMeasure (finUnions 𝒞) (semiExtend 𝒞 μ) := by
  classical
  refine ⟨by rw [semiExtend_eq h hμ h0 (J := ∅) (by simp) (by simp) (by simp)]; simp, ?_⟩
  intro E hE hd hU
  choose J hJ hJd hJeq using fun n => exists_disjoint_rep h (hE n)
  obtain ⟨K, hK, hKd, hKeq⟩ := exists_disjoint_rep h hU
  rw [semiExtend_eq h hμ h0 hK hKd hKeq]
  simp_rw [semiExtend_eq h hμ h0 (hJ _) (hJd _) (hJeq _)]
  have hsubK : ∀ n, ∀ C ∈ J n, C ⊆ ⋃₀ (↑K : Set (Set α)) := fun n C hC =>
    hKeq ▸ (hJeq n ▸ subset_sUnion_of_mem hC).trans (subset_iUnion E n)
  have hD : ∀ D ∈ K, μ D = ∑' n, ∑ C ∈ J n, μ (C ∩ D) := by
    intro D hDK
    have hDC : D ∈ 𝒞 := hK hDK
    let f : (Σ n, (↑(J n) : Set (Set α))) → Set α := fun x => x.2.1 ∩ D
    have hfU : (⋃ x, f x) = D := by
      apply Subset.antisymm
      · exact iUnion_subset fun x => inter_subset_right
      · intro y hy
        have : y ∈ ⋃ n, E n := hKeq ▸ subset_sUnion_of_mem hDK hy
        obtain ⟨n, hn⟩ := mem_iUnion.1 this
        rw [hJeq n] at hn
        obtain ⟨C, hC, hyC⟩ := mem_sUnion.1 hn
        exact mem_iUnion.2 ⟨⟨n, C, hC⟩, hyC, hy⟩
    have hfd : Pairwise (Disjoint on f) := by
      rintro ⟨n, C, hC⟩ ⟨n', C', hC'⟩ hne
      simp only [onFun, f]
      by_cases hnn : n = n'
      · subst hnn
        have hCC : C ≠ C' := fun hCC => hne (by subst hCC; rfl)
        exact (hJd n hC hC' hCC).mono inter_subset_left inter_subset_left
      · have h1 : C ⊆ E n := hJeq n ▸ subset_sUnion_of_mem hC
        have h2 : C' ⊆ E n' := hJeq n' ▸ subset_sUnion_of_mem hC'
        exact ((hd hnn).mono h1 h2).mono inter_subset_left inter_subset_left
    have := hμ.countable h0 h.empty_mem f (fun x => h.inter_mem _ (hJ x.1 x.2.2) D hDC) hfd
      (hfU.symm ▸ hDC)
    rw [hfU] at this
    rw [this, ENNReal.tsum_sigma']
    exact tsum_congr fun n => Finset.tsum_subtype (J n) fun C => μ (C ∩ D)
  rw [Finset.sum_congr rfl hD, ← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine tsum_congr fun n => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun C hC =>
    (sum_inter_eq h hμ h0 (hJ n hC) hK hKd (hsubK n C hC)).symm

end StokeyLucasPrescott.MeasureIntegration
