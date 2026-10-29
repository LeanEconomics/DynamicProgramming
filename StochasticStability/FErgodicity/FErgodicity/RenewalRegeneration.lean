/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FErgodicity.RenewalMeasure
import FErgodicity.RenewalSmallSets

/-!
# The continuous-time regeneration identity (MT (14.43))

Meyn and Tweedie, (14.43), p. 356: for `A ⊆ [s, ∞)`, `Γ₀ ∗ U(A) = Γ₀Pˢ ∗ U(A − s)`, where
`Γ₀Pˢ` is the law of the forward recurrence time `V⁺(s)`. Here `s = nδ` and `Γ₀Pⁿᵟ` is the law of
the `δ`-skeleton `V⁺_δ(n)`, that is `(P^δ)ⁿ` applied to the first-epoch law.

* `tsum_indicator_resEpoch_eq`: pathwise, the epochs in `A ⊆ (nδ, ∞)` are those of the renewal
  process restarted at the first epoch after `nδ`, with first epoch `V⁺(nδ)` and the increments
  that follow, shifted by `nδ`.
* **(14.43)** (`renMeas_eq_lintegral_skeleton`): for a first-epoch law `μ` on `(0, ∞)` and
  measurable `A ⊆ (nδ, ∞)`, `μ ∗ U(A) = ∫ (μ(P^δ)ⁿ)(dv) δ_v ∗ U(A − nδ)`, by the regeneration of the
  increments at the random index of the first epoch after `nδ` (`lintegral_regeneration`).
-/

namespace MeynTweedie.FErgodicity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- **The epochs after `nδ`**: if the increments are nonnegative with divergent partial sums and
`A ⊆ (nδ, ∞)`, the number of epochs in `A` equals the number of epochs of the process restarted
at the first epoch after `nδ` in `A − nδ`. -/
theorem tsum_indicator_resEpoch_eq {δ : ℝ} (n : ℕ) {x : ℝ} {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, w i) atTop atTop) {A : Set ℝ}
    (hAn : A ⊆ Ioi ((n : ℝ) * δ)) :
    ∑' m : ℕ, A.indicator 1 (resEpoch x w (m + 1)) =
      ∑' j : ℕ, A.indicator (1 : ℝ → ℝ≥0∞)
        (resEpoch (fwdSkel δ n (x, w)) (tailSeq (fwdIndex δ n (x, w)) w) (j + 1) + n * δ) := by
  set τ := fwdIndex δ n (x, w) with hτdef
  have hex := exists_resEpoch_gt (x := x) hdiv ((n : ℝ) * δ)
  have hmin : ∀ m < τ, resEpoch x w (m + 1) ≤ (n : ℝ) * δ := fun m hm =>
    not_lt.1 (Nat.notMem_of_lt_sInf hm)
  have hW : fwdSkel δ n (x, w) = resEpoch x w (τ + 1) - n * δ :=
    fwdTimeCts_eq_resEpoch hw hdiv
  have htail : ∀ j, resEpoch (fwdSkel δ n (x, w)) (tailSeq τ w) (j + 1) =
      resEpoch x w (τ + 1 + j) - n * δ := fun j => by
    rw [hW, resEpoch_succ_eq, show τ + 1 + j = τ + j + 1 by omega, resEpoch_succ_eq,
      resEpoch_succ_eq, Finset.sum_range_add]
    simp only [tailSeq]
    ring
  rw [← ENNReal.summable.sum_add_tsum_nat_add' (k := τ)]
  have h0 : ∑ m ∈ Finset.range τ, A.indicator (1 : ℝ → ℝ≥0∞) (resEpoch x w (m + 1)) = 0 :=
    Finset.sum_eq_zero fun m hm => indicator_of_notMem (fun h =>
      absurd (hAn h) (not_lt.2 (hmin m (Finset.mem_range.1 hm)))) _
  rw [h0, zero_add]
  refine tsum_congr fun j => ?_
  rw [htail, sub_add_cancel, show j + τ + 1 = τ + 1 + j by omega]

/-- **(14.43), the regeneration identity** (MT p. 356): for a first-epoch law `μ` on `(0, ∞)`,
`δ ≥ 0` and measurable `A ⊆ (nδ, ∞)`, `μ ∗ U(A) = ∫ (μ(P^δ)ⁿ)(dv) δ_v ∗ U(A − nδ)`. -/
theorem renMeas_eq_lintegral_skeleton (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hΓ0 : Γ (Iio 0) = 0) (hΓpos : 0 < Γ (Ioi 0)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iic 0) = 0) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) {A : Set ℝ} (hA : MeasurableSet A)
    (hAn : A ⊆ Ioi ((n : ℝ) * δ)) :
    haveI := isMarkovKernel_fwdSkelKernel Γ δ
    renMeas Γ μ A = ∫⁻ v, renMeas Γ (Measure.dirac v) ((fun u => u + n * δ) ⁻¹' A)
      ∂((fwdSkelKernel Γ δ ^ n : Kernel ℝ ℝ) ∘ₘ μ) := by
  have := isMarkovKernel_fwdSkelKernel Γ δ
  set ν := incr Γ with hν
  set P0 := μ.prod ν with hP0
  set A' := (fun u => u + (n : ℝ) * δ) ⁻¹' A with hA'def
  have hA' : MeasurableSet A' := (measurable_id.add measurable_const) hA
  set g : ℝ × (ℕ → ℝ) → ℝ≥0∞ := fun q => ∑' j : ℕ, A'.indicator 1 (resEpoch q.1 q.2 (j + 1))
    with hgdef
  have hg : Measurable g := Measurable.tsum fun j : ℕ =>
    (measurable_one.indicator hA').comp (measurable_resEpoch (j + 1))
  -- the renewal measure as an integral over paths
  have h1 : renMeas Γ μ A = ∫⁻ p, ∑' m : ℕ, A.indicator 1 (resEpoch p.1 p.2 (m + 1)) ∂P0 := by
    rw [renMeas_apply Γ μ hA, lintegral_tsum
      (f := fun m (p : ℝ × (ℕ → ℝ)) => A.indicator (1 : ℝ → ℝ≥0∞) (resEpoch p.1 p.2 (m + 1)))
      fun m => ((measurable_one.indicator hA).comp (measurable_resEpoch (m + 1))).aemeasurable]
    refine tsum_congr fun m => ?_
    exact ((lintegral_indicator_const_comp (measurable_resEpoch (m + 1)) hA 1).trans
      (one_mul _)).symm
  -- pathwise regeneration
  have h2 : ∫⁻ p, ∑' m : ℕ, A.indicator 1 (resEpoch p.1 p.2 (m + 1)) ∂P0 =
      ∫⁻ p, g (fwdSkel δ n p, tailSeq (fwdIndex δ n p) p.2) ∂P0 := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_good_prod μ Γ hΓ0 hΓpos] with p ⟨hdiv, hw⟩
    obtain ⟨x, w⟩ := p
    rw [tsum_indicator_resEpoch_eq n hw hdiv hAn]
    rfl
  -- the regeneration at the index of the first epoch after `nδ`
  have h3 := lintegral_regeneration P0 ν (fwdIndex δ n) (measurableSet_fwdIndex_eq δ n)
    (fun k p => (p.1, truncSeq k p.2))
    (fun k => measurable_fst.prodMk ((measurable_truncSeq k).comp measurable_snd))
    (fun k p => tailSeq k p.2) (fun k => (measurable_tailSeq k).comp measurable_snd)
    (fun k => prod_map_trunc_tail μ Γ k) (fwdSkel δ n) (S := univ) MeasurableSet.univ
    (fun k => ?_) hg
  · have h4 : ∀ v, ∫⁻ y, g (v, y) ∂ν = renMeas Γ (Measure.dirac v) A' := fun v => by
      rw [renMeas_dirac_apply Γ v hA']
      change ∫⁻ y, ∑' j : ℕ, A'.indicator (1 : ℝ → ℝ≥0∞) (resEpoch v y (j + 1)) ∂ν = _
      rw [lintegral_tsum
        (f := fun j (y : ℕ → ℝ) => A'.indicator (1 : ℝ → ℝ≥0∞) (resEpoch v y (j + 1)))
        fun j => ((measurable_one.indicator hA').comp
          ((measurable_resEpoch (j + 1)).comp measurable_prodMk_left)).aemeasurable]
      refine tsum_congr fun j => ?_
      exact (lintegral_indicator_const_comp ((measurable_resEpoch (j + 1)).comp
        measurable_prodMk_left) hA' 1).trans (one_mul _)
    have hmc := (fwdSkeleton_isMarkovChain_delayed Γ hΓ0 hΓpos μ hμ hδ).map_eq n
    have hcond : ∀ v : ℝ, ν[|{y | (v, y) ∈ (univ : Set (ℝ × (ℕ → ℝ)))}] = ν := fun v => by
      simp only [mem_univ, ofPred_true, cond_univ]
    rw [h1, h2, h3]
    simp_rw [hcond, h4]
    rw [← hmc, lintegral_map (measurable_renMeas_dirac Γ hA') (measurable_fwdSkel δ n)]
  · refine ⟨{b | (n : ℝ) * δ < resEpoch b.1 b.2 (k + 1) ∧
        ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ}, ?_,
      fun b => fwdTimeCts (resEpoch b.1 b.2) ((n : ℝ) * δ), ?_, ?_⟩
    · have hset : {b : ℝ × (ℕ → ℝ) | ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} =
          ⋂ m, ⋂ (_ : m < k), {b | resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} := by
        ext b
        simp only [mem_ofPred_eq, mem_iInter]
      have hT2 : MeasurableSet
          {b : ℝ × (ℕ → ℝ) | ∀ m < k, resEpoch b.1 b.2 (m + 1) ≤ (n : ℝ) * δ} := by
        rw [hset]
        exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
          measurableSet_le (measurable_resEpoch (m + 1)) measurable_const
      exact (measurableSet_lt measurable_const (measurable_resEpoch (k + 1))).inter hT2
    · exact measurable_fwdTimeCts (Z := fun q : ℝ × (ℕ → ℝ) => resEpoch q.1 q.2)
        (fun k => measurable_resEpoch k) _
    · filter_upwards [ae_good_prod μ Γ hΓ0 hΓpos] with p ⟨hdiv, hw⟩
      obtain ⟨x, w⟩ := p
      simp only at hdiv hw
      have hex := exists_resEpoch_gt (x := x) hdiv ((n : ℝ) * δ)
      have hiff : fwdIndex δ n (x, w) = k ↔ ((n : ℝ) * δ < resEpoch x w (k + 1) ∧
          ∀ m < k, resEpoch x w (m + 1) ≤ (n : ℝ) * δ) := by
        unfold fwdIndex
        rw [natSInf_eq_iff]
        simp only [not_lt]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · obtain ⟨m, hm⟩ := hex
            exact absurd hm (not_lt.2 (h m))
        · exact Or.inl
      refine ⟨?_, fun hk => ?_⟩
      · rw [hiff]
        simp only [mem_univ, and_true]
        rw [resEpoch_truncSeq_of_le le_rfl]
        refine and_congr_right fun _ => forall₂_congr fun m hm => ?_
        rw [resEpoch_truncSeq_of_le (by omega)]
      · have hk' := (hiff.1 hk).1
        exact (fwdTimeCts_truncSeq hw hk').symm

end MeynTweedie.FErgodicity
