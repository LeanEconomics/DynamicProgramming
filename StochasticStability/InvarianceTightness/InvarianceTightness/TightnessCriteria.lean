/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.BoundednessCriteria

/-!
# Lemma D.5.3 (i): tightness and coercive functions (MT Appendix D, p. 559)

Meyn and Tweedie, Lemma D.5.3 (i), p. 559, used in §12.5.

* `lemma_D_5_3_i_necessity`: a tight sequence of probabilities `{νₙ}` on a σ-compact Hausdorff
  space admits a coercive `V` with `∫ V dνₙ ≤ 2` for every `n`. Take compact sets `Lⱼ`, increasing
  and exhausting `X`, with `νₙ(Lⱼᶜ) ≤ 4⁻ʲ` for all `n`, and set `V = Σⱼ 2ʲ 1_{Lⱼᶜ}`, which is
  finite everywhere. Then `{V ≤ r} ⊆ Lⱼ` once `2ʲ > r`.
* `lemma_D_5_3_i`: the equivalence. The sufficiency half is
  `isTightMeasureSet_range_of_lintegral_le` (in `BoundednessCriteria`).

**Hypotheses.** The book uses `limsup_k νₖ(V) < ∞`. Here the bound is uniform,
`sup_n ∫ V dνₙ < ∞`. That is stronger for the necessity half and weaker for the sufficiency half;
the two forms are equivalent because each single probability on such a space is tight.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [OpensMeasurableSpace X] [SigmaCompactSpace X] [WeaklyLocallyCompactSpace X]

/-- **Lemma D.5.3 (i)**, the necessity half (MT p. 559): if `{νₙ}` is a tight sequence of
probabilities, there is a coercive `V` with `∫ V dνₙ ≤ 2` for every `n`. With compact sets `Lⱼ`,
increasing, exhausting `X` and with `νₙ(Lⱼᶜ) ≤ 4⁻ʲ`, take `V = Σⱼ 2ʲ 1_{Lⱼᶜ}`. -/
theorem lemma_D_5_3_i_necessity (ν : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ν n)]
    (h : IsTightMeasureSet (range ν)) :
    ∃ V : X → ℝ≥0, Measurable V ∧ IsCoercive V ∧ ∀ n, ∫⁻ x, (V x : ℝ≥0∞) ∂ν n ≤ 2 := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at h
  choose K hK hKle using fun j : ℕ =>
    h ((4 : ℝ≥0∞)⁻¹ ^ j) (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) j)
  let Kx : CompactExhaustion X := CompactExhaustion.choice X
  set L : ℕ → Set X := fun j => (⋃ i ∈ Finset.range (j + 1), K i) ∪ Kx j
  have hLc : ∀ j, IsCompact (L j) := fun j =>
    ((Finset.range (j + 1)).isCompact_biUnion fun i _ => hK i).union (Kx.isCompact j)
  have hLm : ∀ j, MeasurableSet (L j) := fun j => (hLc j).isClosed.measurableSet
  have hLmono : Monotone L := fun a b hab x hx => by
    rcases hx with hx | hx
    · simp only [mem_iUnion] at hx
      obtain ⟨i, hi, hx⟩ := hx
      exact Or.inl (mem_biUnion (Finset.mem_range.2 (by simp at hi; omega)) hx)
    · exact Or.inr (Kx.subset hab hx)
  have hLcov : ∀ x, ∃ m, x ∈ L m := fun x => ⟨Kx.find x, Or.inr (Kx.mem_find x)⟩
  have hLν : ∀ j n, ν n (L j)ᶜ ≤ (4 : ℝ≥0∞)⁻¹ ^ j := fun j n =>
    (measure_mono (compl_subset_compl.2 fun x hx =>
      Or.inl (mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self j)) hx))).trans
      (hKle j _ ⟨n, rfl⟩)
  set W : X → ℝ≥0∞ := fun x => ∑' j, 2 ^ j * (L j)ᶜ.indicator 1 x
  have hWm : Measurable W :=
    Measurable.tsum fun j => measurable_const.mul (measurable_one.indicator (hLm j).compl)
  have hWfin : ∀ x, W x ≠ ∞ := fun x => by
    obtain ⟨m, hm⟩ := hLcov x
    have hz : ∀ j ∉ Finset.range m, 2 ^ j * (L j)ᶜ.indicator 1 x = (0 : ℝ≥0∞) := fun j hj => by
      have : x ∈ L j := hLmono (by simp at hj; omega) hm
      simp [this]
    simp only [W]
    rw [tsum_eq_sum hz]
    exact ENNReal.sum_ne_top.2 fun j _ => by
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ?_
      by_cases hj : x ∈ (L j)ᶜ <;> simp [hj]
  refine ⟨fun x => (W x).toNNReal, hWm.ennreal_toNNReal, fun r => ?_, fun n => ?_⟩
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (r : ℝ≥0∞) < 2 ^ j := by
      obtain ⟨j, hj⟩ := ENNReal.exists_nat_gt (ENNReal.coe_ne_top (r := r))
      exact ⟨j, hj.trans_le (by exact_mod_cast (Nat.lt_two_pow_self).le)⟩
    have hsub : {x | (W x).toNNReal ≤ r} ⊆ L j := fun x hx => by
      by_contra hxL
      have h1 : (2 : ℝ≥0∞) ^ j ≤ W x := by
        calc (2 : ℝ≥0∞) ^ j = 2 ^ j * (L j)ᶜ.indicator 1 x := by simp [hxL]
          _ ≤ W x := ENNReal.le_tsum (f := fun j => 2 ^ j * (L j)ᶜ.indicator 1 x) j
      have h2 : W x ≤ r := by
        rw [← ENNReal.coe_toNNReal (hWfin x)]
        exact_mod_cast hx
      exact absurd (h1.trans h2) (not_le.2 hj)
    exact (hLc j).of_isClosed_subset isClosed_closure (closure_minimal hsub (hLc j).isClosed)
  · calc ∫⁻ x, (((W x).toNNReal : ℝ≥0) : ℝ≥0∞) ∂ν n = ∫⁻ x, W x ∂ν n :=
          lintegral_congr fun x => ENNReal.coe_toNNReal (hWfin x)
      _ = ∑' j, 2 ^ j * ν n (L j)ᶜ := by
          change ∫⁻ x, ∑' j, 2 ^ j * (L j)ᶜ.indicator 1 x ∂ν n = _
          rw [lintegral_tsum (f := fun j x => 2 ^ j * (L j)ᶜ.indicator 1 x) fun j =>
            (measurable_const.mul
            (measurable_one.indicator (hLm j).compl)).aemeasurable]
          congr 1
          funext j
          rw [lintegral_const_mul _ (measurable_one.indicator (hLm j).compl),
            lintegral_indicator_one (hLm j).compl]
      _ ≤ ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          calc (2 : ℝ≥0∞) ^ j * ν n (L j)ᶜ ≤ 2 ^ j * (4 : ℝ≥0∞)⁻¹ ^ j := by gcongr; exact hLν j n
            _ = 2⁻¹ ^ j := by
                rw [← mul_pow]
                congr 1
                rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
                  ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
      _ = 2 := by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

/-- **Lemma D.5.3 (i)** (MT p. 559), with a uniform bound in place of the `limsup`: a sequence of
probabilities is tight iff there is a coercive `V` with `sup_n ∫ V dνₙ < ∞`. -/
theorem lemma_D_5_3_i (ν : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ν n)] :
    IsTightMeasureSet (range ν) ↔ ∃ V : X → ℝ≥0, Measurable V ∧ IsCoercive V ∧
      ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, ∫⁻ x, (V x : ℝ≥0∞) ∂ν n ≤ M := by
  constructor
  · intro h
    obtain ⟨V, hVm, hV, hb⟩ := lemma_D_5_3_i_necessity ν h
    exact ⟨V, hVm, hV, 2, by simp, hb⟩
  · rintro ⟨V, hVm, hV, M, hM, hb⟩
    exact isTightMeasureSet_range_of_lintegral_le ν hVm hV hM hb

end MeynTweedie.InvarianceTightness
