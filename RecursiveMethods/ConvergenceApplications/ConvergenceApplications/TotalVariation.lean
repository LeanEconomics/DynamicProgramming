/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# The total variation norm

SLP §11.3, pp. 338–344. For a set function `D` (a signed measure, or `λ₁ − λ₂` for finite
measures) the total variation is `‖D‖ = sup Σᵢ |D(Aᵢ)|` over finite measurable partitions
`A₁, …, Aₖ` of `S` (`tvOf`, (1) on p. 339). `tvNorm ν` is the norm of a signed measure (the book's
`Φ(S, 𝒮)` is Mathlib's `SignedMeasure S`), and `tvDist λ₁ λ₂ = ‖λ₁ − λ₂‖`.

* **Exercise 11.3** (`ex_11_3`): every signed measure is a difference of finite measures, and
  `‖·‖` is a norm on signed measures.
* **Lemma 11.5** (`lemma_11_5`): for finite measures of equal mass,
  `‖λ₁ − λ₂‖ = 2 sup_A |λ₁(A) − λ₂(A)|`. The book proves it for probability measures, using
  Lemma 7.12, and applies it in Lemma 11.11 to measures of equal but smaller mass. Here it is
  proved for equal masses, using the Hahn decomposition.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory Set Finset
open scoped Pointwise

variable {S : Type*} [MeasurableSpace S]

/-- A finite measurable partition `A₁, …, Aₖ` of `S`. -/
def IsPartition {k : ℕ} (A : Fin k → Set S) : Prop :=
  (∀ i, MeasurableSet (A i)) ∧ Pairwise (Function.onFun Disjoint A) ∧ ⋃ i, A i = Set.univ

/-- The sums `Σᵢ |D(Aᵢ)|` over finite measurable partitions. -/
def partSums (D : Set S → ℝ) : Set ℝ :=
  {x | ∃ k, ∃ A : Fin k → Set S, IsPartition A ∧ x = ∑ i, |D (A i)|}

/-- The total variation `sup Σᵢ |D(Aᵢ)|` over finite measurable partitions ((1), p. 339). -/
noncomputable def tvOf (D : Set S → ℝ) : ℝ := sSup (partSums D)

/-- The **total variation norm** of a signed measure. -/
noncomputable def tvNorm (ν : SignedMeasure S) : ℝ := tvOf fun A => ν A

/-- `‖λ₁ − λ₂‖` for finite measures. -/
noncomputable def tvDist (μ₁ μ₂ : Measure S) : ℝ := tvOf fun A => μ₁.real A - μ₂.real A

/-- `sup_A |λ₁(A) − λ₂(A)|` over measurable `A`. -/
noncomputable def supDiff (μ₁ μ₂ : Measure S) : ℝ :=
  sSup ((fun A => |μ₁.real A - μ₂.real A|) '' {A | MeasurableSet A})

theorem isPartition_univ : IsPartition (fun _ : Fin 1 => (Set.univ : Set S)) :=
  ⟨fun _ => MeasurableSet.univ, fun i j hij => absurd (Subsingleton.elim i j) hij,
    iUnion_const _⟩

/-- The partition `{B, Bᶜ}`. -/
theorem isPartition_pair {B : Set S} (hB : MeasurableSet B) :
    IsPartition (fun i : Fin 2 => if i = 0 then B else Bᶜ) := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hB
    · exact hB.compl
  · fin_cases i <;> fin_cases j <;> simp_all [Function.onFun, disjoint_compl_right,
      disjoint_compl_left]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ B
    · exact ⟨0, by simpa using hx⟩
    · exact ⟨1, by simpa using hx⟩

theorem partSums_nonempty (D : Set S → ℝ) : (partSums D).Nonempty :=
  ⟨_, 1, _, isPartition_univ, rfl⟩

/-- A finite measure of a partition adds up to the whole. -/
theorem sum_partition_real (μ : Measure S) [IsFiniteMeasure μ] {k : ℕ} {A : Fin k → Set S}
    (hA : IsPartition A) : ∑ i, μ.real (A i) = μ.real Set.univ := by
  rw [← measureReal_iUnion_fintype hA.2.1 hA.1, hA.2.2]

theorem sum_partition_inter_real (μ : Measure S) [IsFiniteMeasure μ] {k : ℕ}
    {A : Fin k → Set S} (hA : IsPartition A) {B : Set S} (hB : MeasurableSet B) :
    ∑ i, μ.real (A i ∩ B) = μ.real B := by
  rw [← measureReal_iUnion_fintype (fun i j hij => (hA.2.1 hij).mono inter_subset_left
    inter_subset_left) fun i => (hA.1 i).inter hB, ← iUnion_inter, hA.2.2, univ_inter]

theorem partSums_bddAbove_of_le {D : Set S → ℝ} {C : ℝ}
    (h : ∀ k (A : Fin k → Set S), IsPartition A → ∑ i, |D (A i)| ≤ C) :
    BddAbove (partSums D) :=
  ⟨C, by rintro _ ⟨k, A, hA, rfl⟩; exact h k A hA⟩

/-- For finite measures the partition sums are bounded by `λ₁(S) + λ₂(S)`. -/
theorem partSums_le_of_measures (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {k : ℕ} {A : Fin k → Set S} (hA : IsPartition A) :
    ∑ i, |μ₁.real (A i) - μ₂.real (A i)| ≤ μ₁.real Set.univ + μ₂.real Set.univ := by
  rw [← sum_partition_real μ₁ hA, ← sum_partition_real μ₂ hA, ← sum_add_distrib]
  exact sum_le_sum fun i _ => (abs_sub _ _).trans (by
    rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg])

theorem bddAbove_tvDist (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    BddAbove (partSums fun A => μ₁.real A - μ₂.real A) :=
  partSums_bddAbove_of_le fun _ _ hA => partSums_le_of_measures μ₁ μ₂ hA

/-- **Lemma 11.5**, for finite measures of equal mass: `‖λ₁ − λ₂‖ = 2 sup_A |λ₁(A) − λ₂(A)|`.
Let `B` be a Hahn set (`λ₁ ≥ λ₂` on subsets of `B`, `λ₁ ≤ λ₂` on subsets of `Bᶜ`) and
`D = λ₁ − λ₂`. Then `|D(A)| ≤ D(B)` for every `A`, each partition sum is at most
`D(B) − D(Bᶜ) = 2D(B)`, and `{B, Bᶜ}` attains it. -/
theorem lemma_11_5 (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : μ₁ Set.univ = μ₂ Set.univ) :
    tvDist μ₁ μ₂ = 2 * supDiff μ₁ μ₂ ∧ ∃ B, MeasurableSet B ∧
      supDiff μ₁ μ₂ = μ₁.real B - μ₂.real B ∧ μ₂.real Bᶜ - μ₁.real Bᶜ = μ₁.real B - μ₂.real B := by
  obtain ⟨B, hB, hpos, hneg⟩ := hahn_decomposition μ₁ μ₂
  set D : Set S → ℝ := fun A => μ₁.real A - μ₂.real A
  have hP : ∀ t, MeasurableSet t → t ⊆ B → 0 ≤ D t := fun t ht htB => by
    have := ENNReal.toReal_mono (measure_ne_top μ₁ t) (hpos t ht htB)
    simp only [D, measureReal_def]; linarith
  have hN : ∀ t, MeasurableSet t → t ⊆ Bᶜ → D t ≤ 0 := fun t ht htB => by
    have := ENNReal.toReal_mono (measure_ne_top μ₂ t) (hneg t ht htB)
    simp only [D, measureReal_def]; linarith
  have hsplit : ∀ A, MeasurableSet A → D A = D (A ∩ B) + D (A ∩ Bᶜ) := fun A hA => by
    have h1 := measureReal_inter_add_sdiff (μ := μ₁) (s := A) hB
    have h2 := measureReal_inter_add_sdiff (μ := μ₂) (s := A) hB
    rw [sdiff_eq] at h1 h2
    simp only [D]; linarith
  have hcompl : D Bᶜ = -D B := by
    have h1 := measureReal_add_measureReal_compl (μ := μ₁) hB
    have h2 := measureReal_add_measureReal_compl (μ := μ₂) hB
    have h3 : μ₁.real Set.univ = μ₂.real Set.univ := by simp only [measureReal_def, h]
    simp only [D]; linarith
  have hDB : 0 ≤ D B := hP B hB subset_rfl
  -- `|D(A)| ≤ D(B)`
  have habs : ∀ A, MeasurableSet A → |D A| ≤ D B := by
    intro A hA
    have e1 := hsplit A hA
    have e2 := hsplit B hB
    have e3 := hsplit Bᶜ hB.compl
    have a1 := hP (A ∩ B) (hA.inter hB) inter_subset_right
    have a2 := hN (A ∩ Bᶜ) (hA.inter hB.compl) inter_subset_right
    have a3 : D (B ∩ Bᶜ) = 0 := by simp [D]
    have hBA : D (A ∩ B) ≤ D B := by
      have := hsplit (B) hB
      have h4 := measureReal_inter_add_sdiff (μ := μ₁) (s := B) hA
      have h5 := measureReal_inter_add_sdiff (μ := μ₂) (s := B) hA
      have h6 := hP (B \ A) (hB.diff hA) sdiff_subset
      rw [inter_comm] at h4 h5
      simp only [D] at h6 ⊢; linarith
    have hBA' : D Bᶜ ≤ D (A ∩ Bᶜ) := by
      have h4 := measureReal_inter_add_sdiff (μ := μ₁) (s := Bᶜ) hA
      have h5 := measureReal_inter_add_sdiff (μ := μ₂) (s := Bᶜ) hA
      have h6 := hN (Bᶜ \ A) (hB.compl.diff hA) sdiff_subset
      rw [inter_comm] at h4 h5
      simp only [D] at h6 ⊢; linarith
    rw [abs_le]; constructor <;> linarith
  -- every partition sum is at most `2 D(B)`
  have hpart : ∀ k (A : Fin k → Set S), IsPartition A → ∑ i, |D (A i)| ≤ 2 * D B := by
    intro k A hA
    calc ∑ i, |D (A i)| ≤ ∑ i, (D (A i ∩ B) - D (A i ∩ Bᶜ)) := sum_le_sum fun i _ => by
          rw [hsplit (A i) (hA.1 i)]
          have := hP (A i ∩ B) ((hA.1 i).inter hB) inter_subset_right
          have := hN (A i ∩ Bᶜ) ((hA.1 i).inter hB.compl) inter_subset_right
          rw [abs_le]; constructor <;> linarith
      _ = D B - D Bᶜ := by
          simp only [D, sum_sub_distrib, sum_partition_inter_real μ₁ hA hB,
            sum_partition_inter_real μ₂ hA hB, sum_partition_inter_real μ₁ hA hB.compl,
            sum_partition_inter_real μ₂ hA hB.compl]
      _ = 2 * D B := by rw [hcompl]; ring
  have htv : tvDist μ₁ μ₂ = 2 * D B := by
    refine le_antisymm (csSup_le (partSums_nonempty _) ?_) ?_
    · rintro _ ⟨k, A, hA, rfl⟩; exact hpart k A hA
    · refine le_csSup (bddAbove_tvDist μ₁ μ₂) ⟨2, _, isPartition_pair hB, ?_⟩
      simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
      change 2 * D B = |D B| + |D Bᶜ|
      rw [hcompl, abs_neg, abs_of_nonneg hDB]; ring
  have hsup : supDiff μ₁ μ₂ = D B := by
    refine le_antisymm (csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_) ?_
    · rintro _ ⟨A, hA, rfl⟩; exact habs A hA
    · refine le_csSup ⟨D B, ?_⟩ ⟨B, hB, abs_of_nonneg hDB⟩
      rintro _ ⟨A, hA, rfl⟩; exact habs A hA
  refine ⟨by rw [htv, hsup], B, hB, hsup, ?_⟩
  have := hcompl
  simp only [D] at this ⊢; linarith

/-- Every signed measure is a difference of finite measures (its Jordan decomposition). -/
theorem exists_sub_measures (ν : SignedMeasure S) :
    ∃ (μ₁ μ₂ : Measure S) (_ : IsFiniteMeasure μ₁) (_ : IsFiniteMeasure μ₂),
      ν = μ₁.toSignedMeasure - μ₂.toSignedMeasure :=
  ⟨_, _, inferInstance, inferInstance, (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm⟩

theorem tvNorm_sub_eq (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    tvNorm (μ₁.toSignedMeasure - μ₂.toSignedMeasure) = tvDist μ₁ μ₂ := by
  unfold tvNorm tvDist tvOf partSums
  congr 1
  ext x
  refine exists_congr fun k => exists_congr fun A => and_congr_right fun hA => ?_
  have e : ∑ i, |(μ₁.toSignedMeasure - μ₂.toSignedMeasure) (A i)| =
      ∑ i, |μ₁.real (A i) - μ₂.real (A i)| :=
    sum_congr rfl fun i _ => by rw [Measure.toSignedMeasure_sub_apply (hA.1 i)]
  exact Iff.of_eq (congrArg (x = ·) e)

theorem bddAbove_tvNorm (ν : SignedMeasure S) : BddAbove (partSums fun A => ν A) := by
  obtain ⟨μ₁, μ₂, _, _, rfl⟩ := exists_sub_measures ν
  refine partSums_bddAbove_of_le (C := μ₁.real Set.univ + μ₂.real Set.univ) fun k A hA => ?_
  have e : ∑ i, |(μ₁.toSignedMeasure - μ₂.toSignedMeasure) (A i)| =
      ∑ i, |μ₁.real (A i) - μ₂.real (A i)| :=
    sum_congr rfl fun i _ => by rw [Measure.toSignedMeasure_sub_apply (hA.1 i)]
  exact e ▸ partSums_le_of_measures μ₁ μ₂ hA

theorem tvOf_nonneg {D : Set S → ℝ} (hD : BddAbove (partSums D)) : 0 ≤ tvOf D :=
  le_trans (sum_nonneg fun _ _ => abs_nonneg _) (le_csSup hD ⟨1, _, isPartition_univ, rfl⟩)

theorem abs_le_tvOf {D : Set S → ℝ} (hD : BddAbove (partSums D)) {A : Set S}
    (hA : MeasurableSet A) : |D A| ≤ tvOf D := by
  refine le_trans ?_ (le_csSup hD ⟨2, _, isPartition_pair hA, rfl⟩)
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
  linarith [abs_nonneg (D Aᶜ)]

/-- **Exercise 11.3.** Signed measures (differences of finite measures) form a vector space,
and the total variation `‖ν‖ = sup Σᵢ |ν(Aᵢ)|` is a norm on it. -/
theorem ex_11_3 :
    (∀ ν : SignedMeasure S, ∃ (μ₁ μ₂ : Measure S) (_ : IsFiniteMeasure μ₁)
      (_ : IsFiniteMeasure μ₂), ν = μ₁.toSignedMeasure - μ₂.toSignedMeasure) ∧
    tvNorm (0 : SignedMeasure S) = 0 ∧ (∀ ν : SignedMeasure S, 0 ≤ tvNorm ν) ∧
    (∀ ν : SignedMeasure S, tvNorm ν = 0 → ν = 0) ∧
    (∀ (c : ℝ) (ν : SignedMeasure S), tvNorm (c • ν) = |c| * tvNorm ν) ∧
    ∀ ν ν' : SignedMeasure S, tvNorm (ν + ν') ≤ tvNorm ν + tvNorm ν' := by
  refine ⟨exists_sub_measures, ?_, fun ν => tvOf_nonneg (bddAbove_tvNorm ν), fun ν h => ?_,
    fun c ν => ?_, fun ν ν' => ?_⟩
  · refine le_antisymm (csSup_le (partSums_nonempty _) ?_) (tvOf_nonneg (bddAbove_tvNorm 0))
    rintro _ ⟨k, A, -, rfl⟩
    simp
  · ext A hA
    have := abs_le_tvOf (bddAbove_tvNorm ν) hA
    change |ν A| ≤ tvNorm ν at this
    rw [h] at this
    simpa using abs_nonpos_iff.1 this
  · have hset : partSums (fun A => (c • ν) A) = |c| • partSums fun A => ν A := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨k, A, hA, rfl⟩
        refine ⟨_, ⟨k, A, hA, rfl⟩, ?_⟩
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
      · rintro ⟨_, ⟨k, A, hA, rfl⟩, rfl⟩
        refine ⟨k, A, hA, ?_⟩
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
    unfold tvNorm tvOf
    rw [hset, Real.sSup_smul_of_nonneg (abs_nonneg c), smul_eq_mul]
  · refine csSup_le (partSums_nonempty _) ?_
    rintro _ ⟨k, A, hA, rfl⟩
    calc ∑ i, |(ν + ν') (A i)| ≤ ∑ i, |ν (A i)| + ∑ i, |ν' (A i)| := by
          rw [← sum_add_distrib]
          exact sum_le_sum fun i _ => by
            simp only [FunLike.coe_add, Pi.add_apply]; exact abs_add_le _ _
      _ ≤ tvNorm ν + tvNorm ν' := add_le_add (le_csSup (bddAbove_tvNorm ν) ⟨k, A, hA, rfl⟩)
          (le_csSup (bddAbove_tvNorm ν') ⟨k, A, hA, rfl⟩)

end StokeyLucasPrescott.ConvergenceApplications
