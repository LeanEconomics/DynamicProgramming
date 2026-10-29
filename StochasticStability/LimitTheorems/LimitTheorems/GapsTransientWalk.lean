/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LimitTheorems.GapsChaconOrnstein
import LimitTheorems.RandomWalkIntegers

/-!
# Theorem 17.3.2 (ii) ⇒ (iii) fails for irreducible chains

Meyn and Tweedie, Theorem 17.3.2, p. 436. The statement "(ii) the invariant σ-field is
`P_x`-trivial for all `x`" does not imply Harris recurrence even for a `ψ`-irreducible chain with
a σ-finite invariant measure: recurrence is needed (`theorem_17_3_2_tfae`).

* `biasedStep = ¾ δ₁ + ¼ δ₋₁` and `biasedKernel`, the random walk on `ℤ` with these increments;
  `biasedKernel_apply`: `P(x, ·) = ¾ δ_{x+1} + ¼ δ_{x−1}`.
* `biased_isIrreducibleChain`, `biased_isTransientChain` (Proposition 8.4.5: non-zero mean),
  `biased_isInvariant_count` (counting measure is invariant).
* `biased_harmonic_const`: every bounded harmonic function is constant. If `d(x) = h(x+1) − h(x)`,
  harmonicity gives `d(x − 1) = 3 d(x)`, so `d(x − n) = 3ⁿ d(x)` is bounded only if `d = 0`.
* **Correction** (`theorem_17_3_2_counterexample_irreducible`): the walk is `ψ`-irreducible
  (`ψ` = counting measure), counting measure is a σ-finite invariant measure, every invariant
  event has `P_μ`-probability `0` or `1` for every initial law `μ` (Proposition 17.1.4), in
  particular (ii) holds; but the walk is transient, so it is not Harris and the ratio limit (i)
  fails. Together with `theorem_17_3_2_counterexample` (the identity chain on `Bool`), this shows
  that (ii) ⇒ (iii) needs both irreducibility and recurrence.
-/

namespace MeynTweedie.LimitTheorems

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

/-- The increment law `Γ = ¾ δ₁ + ¼ δ₋₁`. -/
noncomputable def biasedStep (w : ℤ) : ℝ≥0∞ :=
  if w = 1 then 3 / 4 else if w = -1 then 1 / 4 else 0

/-- `Γ` vanishes off `{1, −1}`. -/
theorem biasedStep_eq_zero {w : ℤ} (hw : w ≠ 1) (hw' : w ≠ -1) : biasedStep w = 0 := by
  simp [biasedStep, hw, hw']

/-- `Γ` is a probability on `ℤ`. -/
theorem tsum_biasedStep : ∑' w, biasedStep w = 1 := by
  rw [tsum_eq_sum (s := {1, -1}) fun w hw => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    exact biasedStep_eq_zero hw.1 hw.2]
  have e1 : biasedStep 1 = 3 / 4 := by simp [biasedStep]
  have e2 : biasedStep (-1) = 1 / 4 := by simp [biasedStep]
  rw [Finset.sum_pair (by norm_num), e1, e2, ENNReal.div_add_div_same,
    show (3 : ℝ≥0∞) + 1 = 4 by norm_num, ENNReal.div_self (by norm_num) (by norm_num)]

/-- The biased random walk `Φₙ₊₁ = Φₙ + Wₙ₊₁`, `W ∼ ¾ δ₁ + ¼ δ₋₁`. -/
noncomputable def biasedKernel : Kernel ℤ ℤ := matKernel (rwMatrix biasedStep)

/-- The walk is a Markov kernel. -/
theorem isMarkovKernel_biasedKernel : IsMarkovKernel biasedKernel :=
  isMarkovKernel_matKernel (isTransitionMatrix_rwMatrix tsum_biasedStep)

/-- `P(x, ·) = ¾ δ_{x+1} + ¼ δ_{x−1}`. -/
theorem biasedKernel_apply (x : ℤ) :
    biasedKernel x = (3 / 4 : ℝ≥0∞) • Measure.dirac (x + 1) +
      (1 / 4 : ℝ≥0∞) • Measure.dirac (x - 1) := by
  refine Measure.ext_of_singleton fun y => ?_
  rw [biasedKernel, matKernel_singleton, rwMatrix, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.dirac_apply, Measure.dirac_apply]
  by_cases h1 : y = x + 1
  · subst h1
    have h2 : x + 1 ≠ x - 1 := by omega
    simp [biasedStep, h2]
  · by_cases h2 : y = x - 1
    · subst h2
      have h3 : x - 1 - x = -1 := by ring
      have h4 : x + 1 ≠ x - 1 := by omega
      simp [biasedStep, h3, h4.symm]
    · have h3 : y - x ≠ 1 := by omega
      have h4 : y - x ≠ -1 := by omega
      have h5 : x + 1 ≠ y := fun h => h1 h.symm
      have h6 : x - 1 ≠ y := fun h => h2 h.symm
      simp [biasedStep_eq_zero h3 h4, h5, h6]

/-- The walk is irreducible: the support `{1, −1}` generates `ℤ`. -/
theorem biased_isIrreducibleChain :
    haveI := isMarkovKernel_biasedKernel
    IsIrreducibleChain biasedKernel := by
  have hM : IsMarkovKernel (matKernel (rwMatrix biasedStep)) := isMarkovKernel_biasedKernel
  have h31 : biasedStep 1 ≠ 0 := by simp [biasedStep]
  have h41 : biasedStep (-1) ≠ 0 := by simp [biasedStep]
  refine ⟨0, ?_⟩
  have hc := rw_commClass_eq (Γ := biasedStep) one_pos h31 (by norm_num : (-1 : ℤ) < 0) h41 0
  change commClass (matKernel (rwMatrix biasedStep)) 0 = univ
  rw [hc]
  ext y
  simp only [mem_ofPred_eq, sub_zero, mem_univ, iff_true]
  have h1 : (1 : ℤ) ∈ rwSupportGroup biasedStep := AddSubgroup.subset_closure h31
  have := AddSubgroup.zsmul_mem _ h1 y
  rwa [smul_eq_mul, mul_one] at this

/-- The walk is transient (Proposition 8.4.5: bounded range and mean `1/2 ≠ 0`). -/
theorem biased_isTransientChain :
    haveI := isMarkovKernel_biasedKernel
    IsTransientChain biasedKernel Measure.count := by
  have := isMarkovKernel_biasedKernel
  refine proposition_8_4_5 tsum_biasedStep (r := 1) (fun w hw => ?_) biased_isIrreducibleChain ?_
  · refine biasedStep_eq_zero ?_ ?_ <;> · intro h; subst h; norm_num at hw
  · have hw : window 1 = {-1, 0, 1} := by decide
    rw [rwMean, hw]
    simp [biasedStep]
    norm_num

/-- Counting measure is invariant for the walk. -/
theorem biased_isInvariant_count : IsInvariant biasedKernel Measure.count := by
  have := isMarkovKernel_biasedKernel
  refine Measure.ext_of_singleton fun y => ?_
  rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _), lintegral_count,
    Measure.count_singleton]
  simp_rw [biasedKernel, matKernel_singleton, rwMatrix]
  rw [← tsum_biasedStep]
  exact (Equiv.subLeft y).tsum_eq biasedStep

/-- Bounded harmonic functions of the walk are constant. -/
theorem biased_harmonic_const {h : ℤ → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (hh : IsHarmonic biasedKernel h) : ∃ c, ∀ x, h x = c := by
  have hint : ∀ a : ℤ, Integrable h (Measure.dirac a) := fun a =>
    integrable_dirac (by simp)
  have heq : ∀ x, 3 * h (x + 1) + h (x - 1) = 4 * h x := fun x => by
    have := hh x
    rw [biasedKernel_apply, integral_add_measure ((hint _).smul_measure
      (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne) ((hint _).smul_measure
      (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne), integral_smul_measure,
      integral_smul_measure,
      integral_dirac, integral_dirac] at this
    norm_num [ENNReal.toReal_div] at this
    linarith
  set d : ℤ → ℝ := fun x => h (x + 1) - h x with hd
  have hd1 : ∀ x, d (x - 1) = 3 * d x := fun x => by
    simp only [hd, sub_add_cancel]
    linarith [heq x]
  have hdn : ∀ (n : ℕ) (x : ℤ), d (x - n) = 3 ^ n * d x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [show x - ((n + 1 : ℕ) : ℤ) = (x - n) - 1 by push_cast; ring, hd1, ih]
      ring
  have hdb : ∀ x, |d x| ≤ 2 * C := fun x => by
    simp only [hd]
    have h1 := hC (x + 1)
    have h2 := hC x
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  have hd0 : ∀ x, d x = 0 := fun x => by
    by_contra hne
    have hpos : 0 < |d x| := abs_pos.2 hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * C / |d x|) (by norm_num : (1 : ℝ) < 3)
    have h1 := hdb (x - n)
    rw [hdn, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at h1
    rw [div_lt_iff₀ hpos] at hn
    linarith
  refine ⟨h 0, fun x => ?_⟩
  induction x using Int.induction_on with
  | zero => rfl
  | succ k ih =>
    have := hd0 k
    simp only [hd] at this
    linarith
  | pred k ih =>
    have := hd0 (-(k : ℤ) - 1)
    simp only [hd, sub_add_cancel] at this
    linarith

/-- **Correction to Theorem 17.3.2** (MT p. 436), irreducible case: the biased walk on `ℤ` is
`ψ`-irreducible with the σ-finite invariant counting measure, and its invariant σ-field is
trivial under every initial law (so (ii) holds); but it is transient, hence not Harris, and the
ratio limit property (i) fails. (ii) ⇒ (iii) needs recurrence. -/
theorem theorem_17_3_2_counterexample_irreducible :
    haveI := isMarkovKernel_biasedKernel
    IsMaximalIrreducibility biasedKernel Measure.count ∧
      IsInvariantMeasure biasedKernel Measure.count ∧
      (∀ μ : Measure ℤ, IsProbabilityMeasure μ → ∀ A : Set (ℕ → ℤ), MeasurableSet A →
        IsInvariantRV biasedKernel (A.indicator 1) →
          pathMeasure biasedKernel μ A = 0 ∨ pathMeasure biasedKernel μ A = 1) ∧
      ¬ HasRatioLimit biasedKernel Measure.count ∧ ¬ ∃ ψ, IsHarris biasedKernel ψ := by
  have := isMarkovKernel_biasedKernel
  have hmax := isMaximalIrreducibility_count biasedKernel biased_isIrreducibleChain
  have hinv : IsInvariantMeasure biasedKernel Measure.count :=
    ⟨inferInstance, biased_isInvariant_count⟩
  have hnot : ¬ ∃ ψ, IsHarris biasedKernel ψ := by
    rintro ⟨ψ, hH⟩
    exact biased_isTransientChain.not_isRecurrentChain
      (hH.of_isMaximalIrreducibility hmax).isRecurrentChain
  have h0 : (Measure.count : Measure ℤ) ≠ 0 := hmax.1
  refine ⟨hmax, hinv, fun μ hμ A hA hA' => ?_, fun hR => hnot
    ((theorem_17_3_2_i_iff_iii hinv h0).1 hR), hnot⟩
  exact (proposition_17_1_4 biasedKernel).1 (fun _ _ ⟨_, hC⟩ hh => biased_harmonic_const hC hh)
    μ hμ A hA (hA' μ hμ)

end MeynTweedie.LimitTheorems
