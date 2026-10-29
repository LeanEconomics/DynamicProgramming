/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import HarrisRecurrence.StochasticComparison
import HarrisRecurrence.FellerModels

/-!
# Proposition 9.5.2 under the book's own hypotheses (MT §9.5.1)

Meyn and Tweedie, Proposition 9.5.2, p. 220. The noise `W` of the scalar linear model
`Xₙ = αXₙ₋₁ + Wₙ` is symmetric, with a density positive on `[−R, R]` and zero elsewhere; here this
is `Γ ≪ Leb|[−R,R]`, `Leb|[−R,R] ≪ Γ` and `Γ ∘ (−·)⁻¹ = Γ`.

`StochasticComparison` proved Proposition 9.5.2 assuming that the model is a `ψ`-irreducible
T-chain. This module removes those hypotheses:

* `ar1_kernel_pos`: `P(y, B) > 0` as soon as `B` meets `[αy − R, αy + R]` in positive Lebesgue
  measure.
* `ar1_isTChain`: `P` is its own continuous component (`Γ ≪ Leb`, continuity of translation,
  `lsc_translate`), so the model is a T-chain for every `α`.
* `ar1_isPhiIrreducible`: for `|α| ≤ 1` the model is `Leb|[−R/2, R/2]`-irreducible: from
  `|y| ≤ (k + 1)R/2` the chain charges any such set at time `k + 1`
  (`ar1_pow_pos`, by induction on `k`).
* `ar1_integral_eq_zero`: symmetry gives mean zero.
* **Proposition 9.5.2** (`proposition_9_5_2_full`): the model is Harris recurrent (for some
  maximal irreducibility measure) iff `|α| ≤ 1`.

**Corrections.** As recorded in `StochasticComparison`, the book's claim that the model is
`μ^Leb`-irreducible on all of `ℝ` is false for `|α| ≠ 1`; the irreducibility measure used here is
Lebesgue measure on `[−R/2, R/2]`, which every starting point reaches when `|α| ≤ 1`.
-/

namespace MeynTweedie.HarrisRecurrence

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-- The noise is carried by `[−R, R]`. -/
theorem ar1_noise_support {Γ : Measure ℝ} {R : ℝ} (h1 : Γ ≪ volume.restrict (Icc (-R) R)) :
    Γ (Icc (-R) R)ᶜ = 0 :=
  h1 (by rw [Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self, measure_empty])

/-- **One-step positivity**: `P(y, B) > 0` when `Leb(B ∩ [αy − R, αy + R]) > 0`. -/
theorem ar1_kernel_pos (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {R α : ℝ}
    (h2 : volume.restrict (Icc (-R) R) ≪ Γ) {B : Set ℝ} (hB : MeasurableSet B) (y : ℝ)
    (hpos : 0 < volume (B ∩ Icc (α * y - R) (α * y + R))) : 0 < ar1Kernel Γ α y B := by
  rw [ar1Kernel_apply' Γ α y hB]
  refine pos_iff_ne_zero.2 fun h0 => hpos.ne' ?_
  have h := h2 h0
  have hm : MeasurableSet {w : ℝ | α * y + w ∈ B} := measurable_const_add (α * y) hB
  rw [Measure.restrict_apply hm] at h
  have hset : {w : ℝ | α * y + w ∈ B} ∩ Icc (-R) R =
      (fun w => α * y + w) ⁻¹' (B ∩ Icc (α * y - R) (α * y + R)) := by
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  rw [hset, measure_preimage_add] at h
  exact h

/-- **The model is a T-chain** when the noise has a density: `P` is a continuous component of
itself. -/
theorem ar1_isTChain (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (hac : Γ ≪ volume) (α : ℝ) :
    IsTChain (ar1Kernel Γ α) := by
  have := isMarkovKernel_ar1Kernel Γ α
  refine ⟨diracDist 1, ar1Kernel Γ α, isSamplingDist_diracDist 1,
    ⟨isSubstochasticKernel_of_markov _, fun x => by rw [sampledKernel_diracDist, pow_one],
      fun A hA => ?_⟩, fun x => by simp⟩
  have heq : (fun x => ar1Kernel Γ α x A) = (fun t => Γ {w | t + w ∈ A}) ∘ fun x => α * x := by
    ext x; exact ar1Kernel_apply' Γ α x hA
  rw [heq]
  exact (lsc_translate volume hac hA).comp (continuous_const.mul continuous_id)

/-- **Reaching a neighbourhood of `0`**: for `|α| ≤ 1`, if `A` meets `[−R/2, R/2]` in positive
Lebesgue measure, then `Pᵏ⁺¹(y, A) > 0` whenever `|y| ≤ (k + 1)R/2`. -/
theorem ar1_pow_pos (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {R α : ℝ} (hR : 0 < R)
    (hα : |α| ≤ 1) (h2 : volume.restrict (Icc (-R) R) ≪ Γ) {A : Set ℝ} (hA : MeasurableSet A)
    (hApos : 0 < volume (A ∩ Icc (-(R / 2)) (R / 2))) (k : ℕ) :
    ∀ y : ℝ, |y| ≤ (k + 1) * (R / 2) → 0 < (ar1Kernel Γ α ^ (k + 1)) y A := by
  have := isMarkovKernel_ar1Kernel Γ α
  have hay : ∀ y : ℝ, |α * y| ≤ |y| := fun y => by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg y) hα
  induction k with
  | zero =>
    intro y hy
    rw [zero_add, pow_one]
    refine ar1_kernel_pos Γ h2 hA y (hpos := lt_of_lt_of_le hApos (measure_mono ?_))
    refine inter_subset_inter_right _ (Icc_subset_Icc ?_ ?_) <;>
    · have := abs_le.1 ((hay y).trans (by simpa using hy)); linarith [this.1, this.2]
  | succ k ih =>
    intro y hy
    set M : ℝ := (k + 1) * (R / 2)
    have hM : 0 < M := by positivity
    set J := Icc (α * y - R) (α * y + R) ∩ Icc (-M) M
    have hJm : MeasurableSet J := measurableSet_Icc.inter measurableSet_Icc
    have hayM : |α * y| ≤ M + R / 2 := (hay y).trans (by
      have : ((k + 1 : ℕ) + 1 : ℝ) * (R / 2) = M + R / 2 := by simp only [M]; push_cast; ring
      rw [← this]; exact hy)
    have hJpos : 0 < ar1Kernel Γ α y J := by
      refine ar1_kernel_pos Γ h2 hJm y ?_
      rw [inter_eq_left.2 inter_subset_left, Icc_inter_Icc, Real.volume_Icc,
        ENNReal.ofReal_pos, sub_pos]
      have := abs_le.1 hayM
      simp only [sup_lt_iff, lt_inf_iff]
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    rw [pow_succ_apply _ (k + 1) y hA]
    by_contra h0
    push Not at h0
    have hzero : ∫⁻ z, (ar1Kernel Γ α ^ (k + 1)) z A ∂ar1Kernel Γ α y = 0 :=
      le_antisymm h0 zero_le
    rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hA)] at hzero
    refine hJpos.ne' (measure_mono_null (fun z hz => ?_) (ae_iff.1 hzero))
    simp only [mem_ofPred_eq, Pi.zero_apply]
    exact (ih z (abs_le.2 ⟨by linarith [hz.2.1], hz.2.2⟩)).ne'

/-- **Irreducibility for `|α| ≤ 1`**: the model is `Leb|[−R/2, R/2]`-irreducible. -/
theorem ar1_isPhiIrreducible (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {R α : ℝ} (hR : 0 < R)
    (hα : |α| ≤ 1) (h2 : volume.restrict (Icc (-R) R) ≪ Γ) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    IsPhiIrreducible (ar1Kernel Γ α) (volume.restrict (Icc (-(R / 2)) (R / 2))) := by
  have := isMarkovKernel_ar1Kernel Γ α
  intro A hA hpos x
  rw [Measure.restrict_apply hA] at hpos
  obtain ⟨k, hk⟩ := exists_nat_ge (|x| / (R / 2))
  refine (hitProb_pos_iff _ hA x).2 ⟨k, ar1_pow_pos Γ hR hα h2 hA hpos k x ?_⟩
  rw [div_le_iff₀ (by positivity)] at hk
  nlinarith

/-- A symmetric noise carried by a bounded interval has mean zero. -/
theorem ar1_integral_eq_zero (Γ : Measure ℝ) [IsProbabilityMeasure Γ]
    (hsymm : Γ.map Neg.neg = Γ) : ∫ w, w ∂Γ = 0 := by
  have h : ∫ w, w ∂(Γ.map Neg.neg) = ∫ w, -w ∂Γ :=
    integral_map measurable_neg.aemeasurable measurable_id.aestronglyMeasurable
  rw [hsymm, integral_neg] at h
  linarith

/-- **Proposition 9.5.2** (MT p. 220), with the book's hypotheses: if the noise is symmetric with
a density positive on `[−R, R]` and zero elsewhere, the scalar linear model is Harris recurrent
iff `|α| ≤ 1`. -/
theorem proposition_9_5_2_full (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {R : ℝ} (hR : 0 < R)
    (h1 : Γ ≪ volume.restrict (Icc (-R) R)) (h2 : volume.restrict (Icc (-R) R) ≪ Γ)
    (hsymm : Γ.map Neg.neg = Γ) (α : ℝ) :
    haveI := isMarkovKernel_ar1Kernel Γ α
    (∃ ψ : Measure ℝ, IsHarris (ar1Kernel Γ α) ψ) ↔ |α| ≤ 1 := by
  have := isMarkovKernel_ar1Kernel Γ α
  have hsupp := ar1_noise_support h1
  refine ⟨fun ⟨ψ, hH⟩ => proposition_9_5_2_necessity Γ hsupp hH, fun hα => ?_⟩
  have hac : Γ ≪ volume := h1.trans Measure.absolutelyContinuous_restrict
  have hW2 : Integrable (fun w => w ^ 2) Γ := by
    refine Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable (R ^ 2) ?_
    rw [ae_iff]
    refine measure_mono_null (fun w hw => ?_) hsupp
    simp only [mem_ofPred_eq, Real.norm_eq_abs, not_le] at hw
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]
    by_contra h
    push Not at h
    rw [abs_of_nonneg (sq_nonneg w)] at hw
    nlinarith [abs_le.2 h, sq_abs w, abs_nonneg w]
  have hψ0 : volume.restrict (Icc (-(R / 2)) (R / 2)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    simp only [ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hmax := isMaximalIrreducibility_maxIrrMeasure (ar1Kernel Γ α)
    (ar1_isPhiIrreducible Γ hR hα h2) hψ0
  exact ⟨_, proposition_9_5_2_sufficiency Γ hW2 (ar1_integral_eq_zero Γ hsymm) hα hmax
    (ar1_isTChain Γ hac α)⟩

end MeynTweedie.HarrisRecurrence
