/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PseudoAtoms.SplitPetite

/-!
# The counterexample to Proposition 5.5.6 (ii) is ψ-irreducible

Meyn and Tweedie, Proposition 5.5.6 (ii), p. 120, assumes that `Φ` is `ψ`-irreducible. This module
shows that the ladder chain `ladderKernel` of `SplitPetite` satisfies that hypothesis, so the
counterexample `proposition_5_5_6_ii_counterexample` applies to the proposition as stated.

* `ladder_pow_odd`: the odd states descend, `Pᵏ(2j + 1, ·) = δ_{2j+1−2k}` for `k ≤ j + 1`, and
  `ladder_reaches_zero`: every state reaches `0`.
* `ladder_isPhiIrreducible_dirac`: the ladder chain is `δ₀`-irreducible.
* `ladder_isAbsorbing_zero_one`: `{0, 1}` is absorbing.
* `ladder_isMaximalIrreducibility`: `δ₀ + δ₁` is a maximal irreducibility measure.
* `proposition_5_5_6_ii_counterexample_irreducible`, the strengthened counterexample: the ladder
  chain has a maximal irreducibility measure `ψ`, is strongly aperiodic, and the set `A` of even
  states is `½δ₀`-small with `ψ(A) > 0`. Yet `A × Bool` is not petite for the chain split on `A`.

**Corrections.** None beyond those of `SplitPetite`.
-/

namespace MeynTweedie.PseudoAtoms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- An odd state moves to `n − 2`. -/
theorem ladderKernel_odd {n : ℕ} (hn : ¬ Even n) : ladderKernel n = Measure.dirac (n - 2) := by
  change ladderMeas n = _
  simp only [ladderMeas, hn, ite_false]

/-- An even state moves to `0` with probability at least `½`. -/
theorem ladderKernel_even_zero {n : ℕ} (hn : Even n) : 2⁻¹ ≤ ladderKernel n {0} := by
  change 2⁻¹ ≤ ladderMeas n {0}
  simp only [ladderMeas, hn, ite_true, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  simp

/-- The odd states descend: `Pᵏ(2j + 1, ·) = δ_{2j+1−2k}` for `k ≤ j + 1`. -/
theorem ladder_pow_odd (j : ℕ) {k : ℕ} (hk : k ≤ j + 1) :
    (ladderKernel ^ k) (2 * j + 1) = Measure.dirac (2 * j + 1 - 2 * k) := by
  induction k with
  | zero => rw [pow_zero_apply, Nat.mul_zero, Nat.sub_zero]
  | succ k ih =>
    rw [pow_succ']
    change (ladderKernel ∘ₖ (ladderKernel ^ k)) (2 * j + 1) = _
    rw [Kernel.comp_apply, ih (by omega), Measure.dirac_bind (Kernel.measurable _),
      ladderKernel_odd (by rw [Nat.not_even_iff_odd]; exact ⟨j - k, by omega⟩)]
    congr 1

/-- Every state reaches `0`: `Pᵏ⁺¹(n, {0}) > 0` for some `k`. -/
theorem ladder_reaches_zero (n : ℕ) : ∃ k, 0 < (ladderKernel ^ (k + 1)) n {0} := by
  rcases Nat.even_or_odd n with hn | ⟨j, rfl⟩
  · refine ⟨0, ?_⟩
    rw [zero_add, pow_one]
    exact (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top).trans_le (ladderKernel_even_zero hn)
  · refine ⟨j, ?_⟩
    rw [ladder_pow_odd j le_rfl, show 2 * j + 1 - 2 * (j + 1) = 0 by omega]
    simp

/-- The ladder chain is `δ₀`-irreducible. -/
theorem ladder_isPhiIrreducible_dirac :
    haveI := isMarkovKernel_ladderKernel
    IsPhiIrreducible ladderKernel (Measure.dirac 0) := by
  have := isMarkovKernel_ladderKernel
  rw [isPhiIrreducible_dirac_iff]
  exact fun n => (hitProb_pos_iff _ (measurableSet_singleton 0) n).2 (ladder_reaches_zero n)

/-- `{0, 1}` is absorbing for the ladder chain. -/
theorem ladder_isAbsorbing_zero_one : IsAbsorbing ladderKernel {0, 1} := by
  have := isMarkovKernel_ladderKernel
  intro x hx
  rcases hx with rfl | hx
  · change ladderMeas 0 {0, 1} = 1
    simp only [ladderMeas, Even.zero, ite_true, Measure.add_apply, Measure.smul_apply,
      smul_eq_mul]
    simp [ENNReal.inv_two_add_inv_two]
  · rw [mem_singleton_iff.1 hx, ladderKernel_odd (by decide)]
    simp

/-- Every state reaches `1`. -/
theorem ladder_reaches_one (n : ℕ) : ∃ k, 0 < (ladderKernel ^ (k + 1)) n {1} := by
  obtain ⟨k, hk⟩ := ladder_reaches_zero n
  refine ⟨k + 1, ?_⟩
  have h01 : 0 < (ladderKernel ^ 1) 0 {1} := by
    rw [pow_one]
    change 0 < ladderMeas 0 {1}
    simp [ladderMeas, Measure.add_apply, Measure.smul_apply]
  exact (ENNReal.mul_pos hk.ne' h01.ne').trans_le (pow_add_singleton_ge _ (k + 1) 1 n 0 1)

/-- **`δ₀ + δ₁` is a maximal irreducibility measure for the ladder chain.** -/
theorem ladder_isMaximalIrreducibility :
    haveI := isMarkovKernel_ladderKernel
    IsMaximalIrreducibility ladderKernel (Measure.dirac 0 + Measure.dirac 1) := by
  have := isMarkovKernel_ladderKernel
  refine ⟨fun h => by simpa using congrArg (fun μ : Measure ℕ => μ {0}) h, ?_, ?_⟩
  · intro B hB hpos x
    rw [Measure.add_apply, Measure.dirac_apply' _ hB, Measure.dirac_apply' _ hB] at hpos
    by_cases h0 : (0 : ℕ) ∈ B
    · obtain ⟨k, hk⟩ := ladder_reaches_zero x
      exact (hk.trans_le (measure_mono (singleton_subset_iff.2 h0))).trans_le
        (pow_le_hitProb _ hB k x)
    · have h1 : (1 : ℕ) ∈ B := by
        by_contra h1
        simp [h0, h1] at hpos
      obtain ⟨k, hk⟩ := ladder_reaches_one x
      exact (hk.trans_le (measure_mono (singleton_subset_iff.2 h1))).trans_le
        (pow_le_hitProb _ hB k x)
  · intro φ hφ
    refine Measure.AbsolutelyContinuous.mk fun B hB h0 => ?_
    rw [Measure.add_apply, Measure.dirac_apply' _ hB, Measure.dirac_apply' _ hB,
      add_eq_zero] at h0
    have hB01 : B ⊆ ({0, 1} : Set ℕ)ᶜ := fun y hy hy01 => by
      rcases hy01 with rfl | rfl
      · simp [hy] at h0
      · simp [hy] at h0
    by_contra hpos
    have h := hφ B hB (pos_iff_ne_zero.2 hpos) 0
    have hc := ladder_isAbsorbing_zero_one.hitProb_compl (measurableSet_of_countable _)
      (show (0 : ℕ) ∈ ({0, 1} : Set ℕ) from Or.inl rfl)
    exact h.ne' (le_antisymm ((measure_mono fun ω hω => by
      obtain ⟨n, hn, h'⟩ := (firstReturn_ne_top_iff B ω).1 hω
      exact (firstReturn_ne_top_iff _ ω).2 ⟨n, hn, hB01 h'⟩).trans_eq hc) zero_le)

/-- **Correction to Proposition 5.5.6 (ii)**, with all of the book's hypotheses. The ladder
chain is `ψ`-irreducible (with maximal `ψ = δ₀ + δ₁`) and strongly aperiodic. The set `A` of even
states is `½δ₀`-small with `ψ(A) > 0`, and it is the set on which the chain is split. Yet
`A × Bool = A₀ ∪ A₁` is not petite for the split chain. -/
theorem proposition_5_5_6_ii_counterexample_irreducible :
    haveI := isMarkovKernel_ladderKernel
    IsMaximalIrreducibility ladderKernel (Measure.dirac 0 + Measure.dirac 1) ∧
      IsStronglyAperiodic ladderKernel ∧
      IsSmallSet ladderKernel 1 ((2⁻¹ : ℝ≥0∞) • Measure.dirac 0) {n | Even n} ∧
      0 < (Measure.dirac 0 + Measure.dirac 1 : Measure ℕ) {n | Even n} ∧
      ladderMinorization.C = {n | Even n} ∧
      ¬ IsPetite ladderMinorization.splitKernel ({n | Even n} ×ˢ univ) := by
  have := isMarkovKernel_ladderKernel
  refine ⟨ladder_isMaximalIrreducibility, ladder_isStronglyAperiodic,
    ⟨measurableSet_of_countable _, one_pos, smul_measure_ne_zero (by simp) (by simp),
      fun x hx => by rw [pow_one]; exact ladderMinorization.le x hx⟩, ?_, rfl,
    proposition_5_5_6_ii_counterexample.2⟩
  rw [Measure.add_apply, Measure.dirac_apply' _ (measurableSet_of_countable _)]
  simp

end MeynTweedie.PseudoAtoms
