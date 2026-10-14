/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.Extension

/-!
# A set that is not Lebesgue measurable

SLP p. 178 cites Royden for a subset of `ℝ` that is not Borel measurable; Exercise 7.30 needs one
that is not even Lebesgue measurable. This is Vitali's construction (`vitaliSet`): one
representative in `[0, 1)` of each class of `ℝ` modulo the rationals. Its rational translates by
`q ∈ (−1, 1)` are disjoint, cover `[0, 1)` and lie in `(−1, 2)`; by translation invariance
they all have the measure of the set, which is therefore neither zero nor positive
(`vitaliSet_not_nullMeasurable`).
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory

/-- The rationals as an additive subgroup of `ℝ`. -/
noncomputable def ratSubgroup : AddSubgroup ℝ := (Rat.castHom ℝ).toAddMonoidHom.range

theorem mem_ratSubgroup {x : ℝ} : x ∈ ratSubgroup ↔ ∃ q : ℚ, (q : ℝ) = x :=
  AddMonoidHom.mem_range

/-- The representative in `[0, 1)` of a class modulo the rationals. -/
noncomputable def vitaliRep (c : ℝ ⧸ ratSubgroup) : ℝ := Int.fract c.out

/-- **The Vitali set**: one point in `[0, 1)` from each class of `ℝ` modulo `ℚ`. -/
def vitaliSet : Set ℝ := range vitaliRep

theorem vitaliSet_subset : vitaliSet ⊆ Ico 0 1 := by
  rintro _ ⟨c, rfl⟩
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Every real number is a rational translate of a point of the Vitali set. -/
theorem exists_rat_sub_mem_vitaliSet (x : ℝ) : ∃ q : ℚ, x - q ∈ vitaliSet := by
  set c : ℝ ⧸ ratSubgroup := (x : ℝ ⧸ ratSubgroup)
  have hc : ((c.out : ℝ) : ℝ ⧸ ratSubgroup) = c := QuotientAddGroup.out_eq' c
  rw [QuotientAddGroup.eq] at hc
  obtain ⟨q, hq⟩ := mem_ratSubgroup.1 hc
  refine ⟨q + ⌊c.out⌋, ⟨c, ?_⟩⟩
  rw [vitaliRep, Int.fract]
  push_cast
  linarith

/-- Two points of the Vitali set that differ by a rational are equal. -/
theorem vitaliSet_eq_of_sub {y y' : ℝ} (hy : y ∈ vitaliSet) (hy' : y' ∈ vitaliSet) {q : ℚ}
    (h : y - y' = q) : y = y' := by
  obtain ⟨c, rfl⟩ := hy
  obtain ⟨c', rfl⟩ := hy'
  have hcc : c' = c := by
    rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' c', QuotientAddGroup.eq]
    refine mem_ratSubgroup.2 ⟨q + ⌊c.out⌋ - ⌊c'.out⌋, ?_⟩
    simp only [vitaliRep, Int.fract] at h
    push_cast
    linarith
  rw [hcc]

/-- The translate `N + q`. -/
def vitaliTranslate (q : ℚ) : Set ℝ := (· + -(q : ℝ)) ⁻¹' vitaliSet

theorem vitaliTranslate_disjoint : Pairwise (Function.onFun Disjoint fun q :
    {q : ℚ // -1 < q ∧ q < 1} => vitaliTranslate q) := by
  intro q q' hqq'
  refine disjoint_left.2 fun x hx hx' => hqq' (Subtype.ext ?_)
  have := vitaliSet_eq_of_sub hx hx' (q := q' - q) (by push_cast; ring)
  have : ((q : ℚ) : ℝ) = q' := by linarith
  exact_mod_cast this

theorem Ico_subset_iUnion_vitaliTranslate :
    Ico (0 : ℝ) 1 ⊆ ⋃ q : {q : ℚ // -1 < q ∧ q < 1}, vitaliTranslate q := by
  intro x hx
  obtain ⟨q, hq⟩ := exists_rat_sub_mem_vitaliSet x
  have h01 := vitaliSet_subset hq
  have h1 : (-1 : ℝ) < q := by linarith [hx.1, h01.2]
  have h2 : (q : ℝ) < 1 := by linarith [hx.2, h01.1]
  refine mem_iUnion.2 ⟨⟨q, by exact_mod_cast h1, by exact_mod_cast h2⟩, ?_⟩
  simpa [vitaliTranslate, sub_eq_add_neg] using hq

theorem iUnion_vitaliTranslate_subset :
    (⋃ q : {q : ℚ // -1 < q ∧ q < 1}, vitaliTranslate q) ⊆ Ioo (-1 : ℝ) 2 := by
  refine iUnion_subset fun q x hx => ?_
  have h01 := vitaliSet_subset hx
  have h1 : (-1 : ℝ) < q := by exact_mod_cast q.2.1
  have h2 : (q : ℝ) < 1 := by exact_mod_cast q.2.2
  simp only [mem_Ico] at h01
  constructor <;> linarith [h01.1, h01.2]

theorem infinite_ratIoo : Infinite {q : ℚ // -1 < q ∧ q < 1} := by
  refine Infinite.of_injective (fun n : ℕ => ⟨1 / ((n : ℚ) + 2), ?_, ?_⟩) fun m n h => ?_
  · have : (0 : ℚ) < 1 / ((n : ℚ) + 2) := by positivity
    linarith
  · rw [div_lt_one (by positivity)]
    have : (0 : ℚ) ≤ n := n.cast_nonneg
    linarith
  · simp only [Subtype.mk.injEq] at h
    have : ((m : ℚ) + 2) = (n : ℚ) + 2 := by
      have hm : (0 : ℚ) < (m : ℚ) + 2 := by positivity
      have hn : (0 : ℚ) < (n : ℚ) + 2 := by positivity
      field_simp at h
      linarith
    exact_mod_cast (add_right_cancel this)

/-- **The Vitali set is not Lebesgue measurable.** -/
theorem vitaliSet_not_nullMeasurable : ¬ NullMeasurableSet vitaliSet volume := by
  intro hN
  have hT : ∀ q : {q : ℚ // -1 < q ∧ q < 1}, NullMeasurableSet (vitaliTranslate q) volume :=
    fun q => hN.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving
  have hTm : ∀ q : {q : ℚ // -1 < q ∧ q < 1}, volume (vitaliTranslate q) = volume vitaliSet :=
    fun q => measure_preimage_add_right volume _ _
  have hU : volume (⋃ q : {q : ℚ // -1 < q ∧ q < 1}, vitaliTranslate q) =
      ∑' _ : {q : ℚ // -1 < q ∧ q < 1}, volume vitaliSet := by
    rw [measure_iUnion₀ (fun q q' h => (vitaliTranslate_disjoint h).aedisjoint) hT]
    exact tsum_congr hTm
  by_cases h0 : volume vitaliSet = 0
  · have h1 : volume (Ico (0 : ℝ) 1) ≤ 0 := by
      calc volume (Ico (0 : ℝ) 1) ≤ volume (⋃ q : {q : ℚ // -1 < q ∧ q < 1},
            vitaliTranslate q) := measure_mono Ico_subset_iUnion_vitaliTranslate
        _ = 0 := by rw [hU, h0, tsum_zero]
    simp at h1
  · have hinf := infinite_ratIoo
    have h1 : (⊤ : ENNReal) ≤ volume (Ioo (-1 : ℝ) 2) := by
      calc (⊤ : ENNReal) = ∑' _ : {q : ℚ // -1 < q ∧ q < 1}, volume vitaliSet :=
            (ENNReal.tsum_const_eq_top_of_ne_zero h0).symm
        _ = volume (⋃ q : {q : ℚ // -1 < q ∧ q < 1}, vitaliTranslate q) := hU.symm
        _ ≤ volume (Ioo (-1 : ℝ) 2) := measure_mono iUnion_vitaliTranslate_subset
    simp at h1

end StokeyLucasPrescott.MeasureIntegration
