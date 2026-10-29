/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeneralizedDrift.GIG1Embedding
import GeneralizedDrift.SmallSets

/-!
# Small sets for the GI/G/1 queue (MT Proposition 5.3.2, from the queue)

Meyn and Tweedie, §5.3.3, p. 108. Here `gig1Ladder H G` is the ladder kernel (3.40), (3.42)–(3.43)
of the embedded GI/G/1 process `Φₙ = (Nₙ, Rₙ)`. By `gig1_isMarkovChain` (copied from the
`TransitionProbabilities` project), it is the transition kernel of the queue built from its
primitives.

* `gig1Lambda_zero_univ`: `Λ₀(x, ℝ) = G(−∞, x)`, the probability that the next arrival comes
  before the service in progress ends.
* `gig1Lambda_tail_univ`: `Σ_{j ≥ 1} Λⱼ(x, ℝ) = G[x, ∞)`.
* `gig1Ladder_bottom`: the bottom rung, `P(0, x; {0} × A) = Λ₀*(x, A) = G[x, ∞) H(A)`, derived
  from (3.42)–(3.43).
* **Proposition 5.3.2** (`proposition_5_3_2_gig1`, p. 108): if `G(β, ∞) > 0`, then
  `{0} × (−∞, β]` is `ν₁`-small for the GI/G/1 ladder chain, with `ν₁ = G(β, ∞) H` on the bottom
  rung. `proposition_5_3_2_queue` combines this with `gig1_isMarkovChain`.
* `gig1Lambda_zero_counterexample`, `gig1Ladder_bottom_counterexample`: the book's
  `Λ₀(x, [0, ∞)) = G(−∞, x]` and `Λ₀*(x, ·) = H(·) G(x, ∞)` fail at atoms of `G`. With
  `G = H = δ₁` and `x = 1`: `Λ₀(1, ℝ) = 0 ≠ 1 = G(−∞, 1]` and `Λ₀*(1, ℝ) = 1 ≠ 0 = G(1, ∞)`.

**Corrections.** On p. 108, `G(−∞, x]` should be `G(−∞, x)` and `G(x, ∞)` should be `G[x, ∞)`. A
service ending exactly at the next arrival empties the queue. The conclusion of
Proposition 5.3.2 is unaffected, since `G[x, ∞) ≥ G(β, ∞)` for `x ≤ β`.
-/

namespace MeynTweedie.GeneralizedDrift

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable (H G : Measure ℝ) [IsProbabilityMeasure H]

/-- `Λ₀(x, ℝ) = G(−∞, x)` when interarrival times are nonnegative. -/
theorem gig1Lambda_zero_univ [IsProbabilityMeasure G] (hG0 : G (Iio 0) = 0) (x : ℝ) :
    gig1Lambda H G 0 x univ = G (Iio x) := by
  change gig1LambdaMeasure H G 0 x univ = _
  rw [gig1LambdaMeasure_apply H G 0 x MeasurableSet.univ]
  have hset : Prod.mk x ⁻¹' gig1Set 0 univ = Ico 0 x ×ˢ (univ : Set (ℕ → ℝ)) := by
    ext p
    simp [gig1Set, resEpoch]
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  refine le_antisymm (measure_mono Ico_subset_Iio_self) ?_
  calc G (Iio x) ≤ G (Ico 0 x ∪ Iio 0) := measure_mono fun t ht => by
        by_cases h : 0 ≤ t
        · exact Or.inl ⟨h, ht⟩
        · exact Or.inr (not_le.1 h)
    _ ≤ G (Ico 0 x) + G (Iio 0) := measure_union_le _ _
    _ = G (Ico 0 x) := by rw [hG0, add_zero]

/-- `Σ_{j ≥ 1} Λⱼ(x, ℝ) = G[x, ∞)`. -/
theorem gig1Lambda_tail_univ [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0)
    (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) (x : ℝ) :
    ∑' j, gig1Lambda H G (j + 1) x univ = G (Ici x) := by
  have h := ennreal_sum_add_tsum_nat_add (fun k => gig1Lambda H G k x univ) 1
  rw [gig1Lambda_tsum_univ H G hH0 hHpos hG0 x, Finset.sum_range_one,
    gig1Lambda_zero_univ H G hG0 x] at h
  rw [← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio, ← h,
    ENNReal.add_sub_cancel_left (measure_ne_top _ _)]

/-- **The bottom rung of the GI/G/1 ladder chain** (MT p. 108):
`P(0, x; {0} × A) = Λ₀*(x, A) = G[x, ∞) H(A)`. -/
theorem gig1Ladder_bottom [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0)
    (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    gig1Ladder H G (0, x) ({0} ×ˢ A) = G (Ici x) * H A := by
  rw [gig1Ladder, eq_3_40_zero _ _ 0 x hA]
  change ((∑' j, gig1Lambda H G (j + 0 + 1) x univ) • H) A = _
  rw [Measure.smul_apply, smul_eq_mul]
  simp only [add_zero]
  rw [gig1Lambda_tail_univ H G hH0 hHpos hG0 x]

/-- **Proposition 5.3.2** (MT p. 108), for the GI/G/1 ladder chain. If `G(β, ∞) > 0`, then
`{0} × (−∞, β]` is `ν₁`-small with `ν₁ = G(β, ∞) H` placed on the bottom rung. -/
theorem proposition_5_3_2_gig1 [IsProbabilityMeasure G] (hH0 : H (Iio 0) = 0)
    (hHpos : 0 < H (Ioi 0)) (hG0 : G (Iio 0) = 0) {β : ℝ} (hG : 0 < G (Ioi β)) :
    IsSmallSet (gig1Ladder H G) 1 (G (Ioi β) • H.map (fun y => ((0 : ℕ), y)))
      ({0} ×ˢ Iic β) := by
  have hmk : Measurable fun y : ℝ => ((0 : ℕ), y) := measurable_const.prodMk measurable_id
  refine ⟨(measurableSet_singleton 0).prod measurableSet_Iic, one_pos, smul_measure_ne_zero ?_
    hG.ne', fun z hz => ?_⟩
  · intro h0
    have := congrArg (fun μ : Measure (ℕ × ℝ) => μ univ) h0
    simp [Measure.map_apply hmk MeasurableSet.univ] at this
  obtain ⟨z1, z2⟩ := z
  obtain ⟨hz1, hz2⟩ := hz
  have hz1' : z1 = 0 := hz1
  subst hz1'
  rw [pow_one]
  refine Measure.le_intro fun B hB _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hmk hB]
  have hsec : MeasurableSet ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B) := hmk hB
  calc G (Ioi β) * H ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B)
      ≤ G (Ici z2) * H ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B) := by
        gcongr
        exact fun t ht => mem_Ici.2 (le_of_lt (lt_of_le_of_lt (mem_Iic.1 hz2) (mem_Ioi.1 ht)))
    _ = gig1Ladder H G (0, z2) ({0} ×ˢ ((fun y : ℝ => ((0 : ℕ), y)) ⁻¹' B)) :=
        (gig1Ladder_bottom H G hH0 hHpos hG0 z2 hsec).symm
    _ ≤ gig1Ladder H G (0, z2) B := by
        refine measure_mono ?_
        rintro ⟨q1, q2⟩ ⟨hq1, hq2⟩
        have hq1' : q1 = 0 := hq1
        subst hq1'
        exact hq2

/-- **Proposition 5.3.2 for the queue** (MT p. 108). Suppose interarrival times are nonnegative,
service times positive, and `G(β, ∞) > 0`. Then the embedded GI/G/1 process `Φₙ = (Nₙ, Rₙ)`, built
from the primitives of the queue, is a Markov chain with kernel `gig1Ladder H G`, and
`{0} × (−∞, β]` is `G(β, ∞) H`-small for it. -/
theorem proposition_5_3_2_queue [IsProbabilityMeasure G] (hH0 : H (Iic 0) = 0)
    (hG0 : G (Iio 0) = 0) {β : ℝ} (hG : 0 < G (Ioi β)) :
    IsMarkovChain (gig1Ladder H G) ((Measure.dirac 0).prod H)
        ((Measure.infinitePi fun _ : ℕ => G).prod (Measure.infinitePi fun _ : ℕ => H))
        (fun n ω => (queueN ω.1 ω.2 n, queueR ω.1 ω.2 n)) ∧
      IsSmallSet (gig1Ladder H G) 1 (G (Ioi β) • H.map (fun y => ((0 : ℕ), y)))
        ({0} ×ˢ Iic β) := by
  have hH0' : H (Iio 0) = 0 := measure_mono_null Iio_subset_Iic_self hH0
  have hHpos : 0 < H (Ioi 0) := by
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, hH0, tsub_zero]
    exact one_pos
  exact ⟨gig1_isMarkovChain H G hH0 hG0, proposition_5_3_2_gig1 H G hH0' hHpos hG0 hG⟩

/-- **Correction to p. 108**: `Λ₀(x, [0, ∞)) = G(−∞, x]` fails at an atom of `G`. With
`G = H = δ₁` and `x = 1`, `Λ₀(1, ℝ) = 0` but `G(−∞, 1] = 1`. -/
theorem gig1Lambda_zero_counterexample :
    gig1Lambda (Measure.dirac 1) (Measure.dirac 1) 0 1 univ = 0 ∧
      (Measure.dirac (1 : ℝ)) (Iic 1) = 1 := by
  refine ⟨?_, by simp⟩
  rw [gig1Lambda_zero_univ _ _ (by simp) 1]
  simp

/-- **Correction to p. 108**: `Λ₀*(x, ·) = H(·) G(x, ∞)` fails at an atom of `G`. With
`G = H = δ₁` and `x = 1`, `P(0, 1; {0} × ℝ) = Λ₀*(1, ℝ) = 1`, but `G(1, ∞) H(ℝ) = 0`. -/
theorem gig1Ladder_bottom_counterexample :
    gig1Ladder (Measure.dirac 1) (Measure.dirac 1) (0, 1) ({0} ×ˢ univ) = 1 ∧
      (Measure.dirac (1 : ℝ)) (Ioi 1) * (Measure.dirac (1 : ℝ)) univ = 0 := by
  refine ⟨?_, by simp⟩
  rw [gig1Ladder_bottom _ _ (by simp) (by simp) (by simp) 1 MeasurableSet.univ]
  simp

end MeynTweedie.GeneralizedDrift
