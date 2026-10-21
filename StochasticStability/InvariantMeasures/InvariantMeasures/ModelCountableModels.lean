/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvariantMeasures.ModelRecursion
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Countable-space models

Copied for Chapter 5 from the `TransitionProbabilities` project
(`TransitionProbabilities/ModelCountableModels.lean`), with the namespace changed to
`MeynTweedie.InvariantMeasures` and the imports to `InvariantMeasures.*`.

That module was in turn copied from the `MarkovModels` project
(`MarkovModels/CountableModels.lean`).

Countable-space chains previewed in MT, Chapters 1–2: the random walk on `ℤ₊` (reflected at `0`)
that the embedded queue length chains of §2.4.2 follow (MT, (2.28), p. 41), and the birth–death
chain on `ℤ₊`.

* `reflectedWalkKernel p`: `Nₙ₊₁ = [Nₙ + ξₙ₊₁]⁺` on `ℕ` with increments `ξ ~ p` on `ℤ`. Up to
  `0` the chain moves like the free walk, `P(j, {i}) = p{i − j}` for `i ≥ 1`
  (`reflectedWalkKernel_apply_pos`); `0` collects the whole lower tail,
  `P(j, {0}) = p(−∞, −j]` (`reflectedWalkKernel_apply_zero`).
* **Correction to (2.28).** MT claim that the queue length at arrivals satisfies
  `P(Nₙ₊₁ = j + k | Nₙ = j, …) = p_k` for all `k ≥ −j`, a random walk on `ℤ₊`. Taken literally,
  for all `j`, this forces the chain never to move down (`not_down_of_eq_2_28`): row `0` already
  has total mass `Σ_{k ≥ 0} p_k = 1`. For a random walk on `ℤ₊` the identity holds only for
  `j + k ≥ 1`, the boundary state `0` receiving the tail mass instead
  (`reflectedWalkKernel_apply_pos`, `reflectedWalkKernel_apply_zero`); `reflectedWalk_2_28_fails`
  is a concrete instance where `P(j, {0}) ≠ p_{−j}`.
* `birthDeathKernel b d`: from `i` up with probability `bᵢ`, down with probability `dᵢ`
  (staying at `0` instead of moving below it), and otherwise staying put.
-/

namespace MeynTweedie.InvariantMeasures

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The step `(j, ξ) ↦ [j + ξ]⁺` of random walk on `ℤ₊`. -/
def reflectStep (q : ℕ × ℤ) : ℕ := ((q.1 : ℤ) + q.2).toNat

/-- Random walk on `ℤ₊ = ℕ`: `Nₙ₊₁ = [Nₙ + ξₙ₊₁]⁺` with i.i.d. increments of law `p` on `ℤ`. -/
noncomputable def reflectedWalkKernel (p : Measure ℤ) : Kernel ℕ ℕ :=
  recursionKernel p reflectStep

/-- The reflected walk on `ℤ₊` is a Markov kernel. -/
theorem isMarkovKernel_reflectedWalkKernel (p : Measure ℤ) [IsProbabilityMeasure p] :
    IsMarkovKernel (reflectedWalkKernel p) :=
  isMarkovKernel_recursionKernel p (measurable_of_countable _)

/-- Away from `0` the reflected walk moves as the free walk: `P(j, {i}) = p{i − j}` for `i ≥ 1`. -/
theorem reflectedWalkKernel_apply_pos (p : Measure ℤ) [SFinite p] (j i : ℕ) (hi : 1 ≤ i) :
    reflectedWalkKernel p j {i} = p {(i : ℤ) - j} := by
  rw [reflectedWalkKernel, recursionKernel_apply' p (measurable_of_countable _) j
    (measurableSet_singleton i)]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff, reflectStep]
  omega

/-- `0` collects the lower tail: `P(j, {0}) = p(−∞, −j]`. -/
theorem reflectedWalkKernel_apply_zero (p : Measure ℤ) [SFinite p] (j : ℕ) :
    reflectedWalkKernel p j {0} = p (Iic (-(j : ℤ))) := by
  rw [reflectedWalkKernel, recursionKernel_apply' p (measurable_of_countable _) j
    (measurableSet_singleton 0)]
  congr 1
  ext w
  simp only [mem_ofPred_eq, mem_singleton_iff, mem_Iic, reflectStep]
  omega

/-- **Correction to (2.28).** If a Markov kernel on `ℕ` satisfied `P(j, {j + k}) = p_k` for every
`j` and every `k ≥ −j`, as (2.28) states, then it could never move down: `P(j, {i}) = 0` for
`i < j`. -/
theorem not_down_of_eq_2_28 (P : Kernel ℕ ℕ) [IsMarkovKernel P] (p : ℤ → ℝ≥0∞)
    (h : ∀ (j : ℕ) (k : ℤ), -(j : ℤ) ≤ k → P j {((j : ℤ) + k).toNat} = p k) (j i : ℕ)
    (hij : i < j) : P j {i} = 0 := by
  have hdisj : ∀ n : ℕ, Pairwise (Function.onFun Disjoint fun k : ℕ => ({n + k} : Set ℕ)) :=
    fun n a b hab => by
      simp only [Function.onFun, disjoint_singleton]
      omega
  have hup : ∀ n : ℕ, P n (Ici n) = ∑' k : ℕ, p k := by
    intro n
    have hU : Ici n = ⋃ k : ℕ, ({n + k} : Set ℕ) := by
      ext m
      simp only [mem_Ici, mem_iUnion, mem_singleton_iff]
      exact ⟨fun hm => ⟨m - n, by omega⟩, fun ⟨k, hk⟩ => by omega⟩
    rw [hU, measure_iUnion (hdisj n) fun _ => measurableSet_singleton _]
    refine tsum_congr fun k => ?_
    have := h n k (by omega)
    rw [← this]
    congr 2
  have h0 : ∑' k : ℕ, p k = 1 := by
    rw [← hup 0, show Ici (0 : ℕ) = univ from Ici_bot, measure_univ]
  have hlow : P j (Iio j) = 0 := by
    have hc : (Iio j)ᶜ = Ici j := by
      ext m
      simp
    have := measure_add_measure_compl (μ := P j) (measurableSet_Iio (a := j))
    rw [hc, hup j, h0, measure_univ] at this
    have h1 : P j (Iio j) + 1 = 0 + 1 := by rw [this, zero_add]
    exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp h1
  exact measure_mono_null (singleton_subset_iff.mpr hij) hlow

/-- The increment law of `reflectedWalk_2_28_fails`: `ξ ∈ {−2, 1}` with probability `1/2`
each. -/
noncomputable def twoPointLaw : Measure ℤ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (-2) + Measure.dirac 1)

/-- An instance of the failure of (2.28) at `k = −j`: for increments `ξ ∈ {−2, 1}` with
probability `1/2` each, `P(1, {0}) = 1/2` while `p_{−1} = 0`. -/
theorem reflectedWalk_2_28_fails :
    reflectedWalkKernel twoPointLaw 1 {0} ≠ twoPointLaw {(1 : ℤ) + (-1)} := by
  rw [reflectedWalkKernel_apply_zero]
  simp only [twoPointLaw, Measure.smul_apply, Measure.add_apply, smul_eq_mul, Nat.cast_one]
  rw [Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic,
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  norm_num [indicator]

/-- The birth–death chain on `ℤ₊`: from `i`, up to `i + 1` with probability `bᵢ`, down to
`i − 1` with probability `dᵢ` (at `0` this means staying at `0`), and otherwise stay at `i`. -/
noncomputable def birthDeathKernel (b d : ℕ → ℝ≥0∞) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun i => b i • Measure.dirac (i + 1) + d i • Measure.dirac (i - 1) +
    (1 - (b i + d i)) • Measure.dirac i

/-- The birth–death transition law from `i`. -/
theorem birthDeathKernel_apply (b d : ℕ → ℝ≥0∞) (i : ℕ) :
    birthDeathKernel b d i = b i • Measure.dirac (i + 1) + d i • Measure.dirac (i - 1) +
      (1 - (b i + d i)) • Measure.dirac i := rfl

/-- The birth–death chain is a Markov kernel when `bᵢ + dᵢ ≤ 1`. -/
theorem isMarkovKernel_birthDeathKernel (b d : ℕ → ℝ≥0∞) (h : ∀ i, b i + d i ≤ 1) :
    IsMarkovKernel (birthDeathKernel b d) := by
  refine ⟨fun i => ⟨?_⟩⟩
  simp only [birthDeathKernel_apply, Measure.add_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [add_tsub_cancel_of_le (h i)]

/-- The birth–death chain moves up with probability `bᵢ`. -/
theorem birthDeathKernel_apply_succ (b d : ℕ → ℝ≥0∞) (i : ℕ) :
    birthDeathKernel b d i {i + 1} = b i := by
  simp only [birthDeathKernel_apply, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp [indicator]

/-- The birth–death chain moves down from `i + 1` with probability `dᵢ₊₁`. -/
theorem birthDeathKernel_apply_pred (b d : ℕ → ℝ≥0∞) (i : ℕ) :
    birthDeathKernel b d (i + 1) {i} = d (i + 1) := by
  simp only [birthDeathKernel_apply, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _),
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  have hne : i + 1 + 1 ≠ i := by omega
  simp [indicator, hne]

end MeynTweedie.InvariantMeasures
