/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Positivity.SplitErgodic
import Positivity.PositiveNull

/-!
# The Aperiodic Ergodic Theorem (MT Theorem 13.0.1, §13.3.2)

Meyn and Tweedie, pp. 313–314 and 327–329. The state space is countably generated (the book's
standing assumption, used through the existence of small sets).

**Skeletons.**
* `exists_skeleton_minorization`: an aperiodic chain has an `m`-skeleton with a minorization
  `Pᵐ(x, ·) ≥ δν` on a set `C ∈ B⁺(X)` with `ν(C) > 0` (Proposition 5.4.5 (iii), keeping track of
  the small set).

**Results.**
* **Theorem 13.3.3** (`theorem_13_3_3`, p. 328): for a positive Harris aperiodic chain,
  `‖λPⁿ − π‖ → 0` for every initial probability `λ`. The proof is the book's: the skeleton is
  positive Harris (Theorems 9.1.6, 10.4.5) and has a minorization on a set in `B⁺(X)`, so
  Theorem 13.3.1 (ii) applies to it; Proposition 13.3.2 passes from `Pᵐⁿ` to `Pⁿ`.
* `theorem_13_3_3_dirac`: the same from every initial state, `‖Pⁿ(x, ·) − π‖ → 0`, i.e. (13.4)
  (`theorem_13_3_3_sup`, in the form `sup_A |Pⁿ(x, A) − π(A)| → 0`).
* `isPositive_of_tendsto_split_skeleton`: if the split `m`-skeleton satisfies
  `νPᵐⁿ(C) → c > 0`, then the chain is positive: the renewal sequence of the atom `α̌` converges
  to `δc > 0`, so the atom is recurrent and (renewal theorem) its return time has finite mean,
  and Kac's theorem makes the split skeleton, hence the skeleton, hence the chain positive.
* **Theorem 13.3.5** (p. 329): for a `ψ`-irreducible aperiodic chain with a `ν`-small set
  `C ∈ B⁺(X)` such that `∫ ν_C(dx)(Pⁿ(x, C) − P^∞(C)) → 0` with `P^∞(C) > 0`, the chain is
  positive (`theorem_13_3_5_positive`, no Harris hypothesis); if it is Harris, then
  `‖λPⁿ − π‖ → 0` for every `λ` (`theorem_13_3_5`).
* **Theorem 13.0.1** (`theorem_13_0_1`, p. 313), for an aperiodic Harris chain: the following
  are equivalent: (i) the chain is positive; (ii) there is a small set `C ∈ B⁺(X)` with
  `Pⁿ(x, C) → P^∞(C) > 0` for every `x ∈ C`, (13.1); (13.4) there is an invariant probability `π`
  with `sup_A |Pⁿ(x, A) − π(A)| → 0` for every `x`.

**Hypotheses.** In Theorem 13.3.5 the small set has `ν(C) > 0`: the book normalises
`ν_C = ν/ν(C)`, which needs it.

**Elsewhere.** Conditions (iii) (a regular set) and (iv) (the drift condition (13.3)) of
Theorem 13.0.1, which come from Theorem 11.0.1, and the summability (13.5) are added in
`ErgodicTheorem` (`theorem_13_0_1_full`, `theorem_13_0_1_sum`). The version of Theorem 13.3.5 for
chains that are not Harris (convergence off a `ψ`-null set, (13.64)) is `theorem_13_3_5_null` in
`PeriodicErgodic`.
-/

namespace MeynTweedie.Positivity

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-- A minorization of the skeleton `Pᵐ` from a bound `Pᵐ(x, ·) ≥ ν'` on `C` with `ν'(C) > 0`:
it lives on `C`, and its probability `ν = ν'(· ∩ C)/ν'(C)` has `ν(C) = 1`. -/
theorem exists_minorization_of_le {P : Kernel X X} [IsMarkovKernel P] {C : Set X}
    (hC : MeasurableSet C) (hne : C.Nonempty) {ν' : Measure X} (hle : ∀ x ∈ C, ν' ≤ P x)
    (hpos : 0 < ν' C) : ∃ M : Minorization P, M.C = C ∧ M.ν M.C = 1 ∧ M.IsConcentrated := by
  obtain ⟨x, hx⟩ := hne
  have hfin : ν' C ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top ((hle x hx C).trans prob_le_one)
  set M := Minorization.ofLe hC hle hpos hfin
  have hconc := Minorization.ofLe_isConcentrated hC hle hpos hfin
  have := M.isProbabilityMeasure_ν
  exact ⟨M, rfl, (prob_compl_eq_zero_iff M.measurableSet_C).1 hconc, hconc⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- An aperiodic chain has a skeleton `Pᵐ`, `m ≥ 1`, with a minorization on a set `C ∈ B⁺(X)`
with `ν(C) > 0`. -/
theorem exists_skeleton_minorization {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) :
    ∃ m, 1 ≤ m ∧ ∃ M : Minorization (P ^ m : Kernel X X), 0 < ψ M.C ∧ 0 < M.ν M.C := by
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨C, -, m, ν, hC, hψC, hνC⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
  obtain ⟨N, hN⟩ := exists_forall_mem_smallTimes_of_aperiodic P hψ hap hC hψC hνC
  obtain ⟨-, δ, hδ, hδn⟩ := hN (N + 1) (by omega)
  have := isMarkovKernel_pow P (N + 1)
  have hpos : 0 < (δ • ν) C := by
    rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_pos hδ.ne' hνC.ne'
  obtain ⟨M, hMC, hMν, -⟩ := exists_minorization_of_le hC.1
    (nonempty_of_measure_ne_zero hψC.ne') hδn hpos
  exact ⟨N + 1, by omega, M, hMC ▸ hψC, by rw [hMν]; exact one_pos⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.3** (MT p. 328): for a positive Harris aperiodic chain with invariant
probability `π`, `‖λPⁿ − π‖ → 0` for every initial probability `λ`. -/
theorem theorem_13_3_3 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (μ : Measure X) [IsProbabilityMeasure μ] :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) π) atTop (𝓝 0) := by
  obtain ⟨m, hm, M, hψC, hνC⟩ := exists_skeleton_minorization hph.1.1 hap
  have := isMarkovKernel_pow P m
  have hH : IsHarris (P ^ m : Kernel X X) ψ := (theorem_9_1_6 hph.1.1 hap).1 hph.1 m hm
  have hpos : IsPositive (P ^ m : Kernel X X) ψ :=
    (theorem_10_4_5_positive hph.1.1 hap).1.1 hph.2 m hm
  have hsk := theorem_13_3_1_ii ⟨hH, hpos⟩ M hψC hνC (hπ.pow m) μ
  have hanti := proposition_13_3_2 P hπ μ
  have hdiv : Tendsto (fun n => n / m) atTop atTop := Nat.tendsto_div_const_atTop (by omega)
  refine squeeze_zero (fun n => tvNorm_nonneg _ _) (fun n => ?_) (hsk.comp hdiv)
  simp only [Function.comp_apply, ← pow_mul]
  exact hanti (Nat.mul_div_le n m)

variable [MeasurableSpace.CountablyGenerated X] in
/-- Theorem 13.3.3 from a starting point: `‖Pⁿ(x, ·) − π‖ → 0` for every `x`. -/
theorem theorem_13_3_3_dirac {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (x : X) :
    Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) x) π) atTop (𝓝 0) := by
  have h := theorem_13_3_3 hph hap hπ (Measure.dirac x)
  simp_rw [dirac_kernel] at h
  exact h

variable [MeasurableSpace.CountablyGenerated X] in
/-- (13.4): for a positive Harris aperiodic chain, `sup_A |Pⁿ(x, A) − π(A)| → 0` for every `x`. -/
theorem theorem_13_3_3_sup {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hph : IsPositiveHarris P ψ) (hap : IsAperiodic P ψ) {π : Measure X} [IsProbabilityMeasure π]
    (hπ : IsInvariant P π) (x : X) :
    Tendsto (fun n => tvSup ((P ^ n : Kernel X X) x) π) atTop (𝓝 0) := by
  have hm : ∀ n, (P ^ n : Kernel X X) x univ = π univ := fun n => by
    have := isMarkovKernel_pow P n; simp
  have : ∀ n, IsFiniteMeasure ((P ^ n : Kernel X X) x) := fun n => by
    have := isMarkovKernel_pow P n; infer_instance
  exact (tendsto_tvNorm_iff_tvSup hm).1 (theorem_13_3_3_dirac hph hap hπ x)

/-! ### Positivity from convergence on a small set -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Positivity from the split skeleton.** Let `M` be a minorization of a skeleton `Pᵐ` of an
aperiodic `ψ`-irreducible chain on a set `C ∈ B⁺(X)` with `ν(C) > 0`. If `νPᵐⁿ(C) → c > 0`,
then the chain is positive. -/
theorem isPositive_of_tendsto_split_skeleton {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {m : ℕ} (hm : 1 ≤ m)
    (M : Minorization (P ^ m : Kernel X X)) (hψC : 0 < ψ M.C) (hνC : 0 < M.ν M.C) {c : ℝ}
    (hc : 0 < c)
    (hlim : Tendsto (fun n => (((P ^ (m * n) : Kernel X X) ∘ₘ M.ν) M.C).toReal) atTop (𝓝 c)) :
    IsPositive P ψ := by
  have := isMarkovKernel_pow P m
  have := M.isMarkovKernel_splitKernel
  have := M.isProbabilityMeasure_ν
  have hQmax : IsMaximalIrreducibility (P ^ m : Kernel X X) ψ :=
    ((proposition_5_4_5_iii P hψ hap).1 m hm).1
  obtain ⟨c0, hc0⟩ : M.C.Nonempty := nonempty_of_measure_ne_zero hψC.ne'
  have hca : (c0, true) ∈ M.checkAlpha := ⟨hc0, rfl⟩
  have hacc := ((M.theorem_5_1_3_ii ψ).2 hQmax.2.1 hψC).2.2 _
    (M.isMaximalIrreducibility_split hQmax)
  -- the renewal sequence of `α̌` converges to `δc > 0`
  have hu : ∀ n, atomRenewal M.splitKernel M.checkAlpha (c0, true) (n + 1) =
      M.δ.toReal * (((P ^ (m * n) : Kernel X X) ∘ₘ M.ν) M.C).toReal := fun n => by
    rw [atomRenewal, M.splitKernel_pow_succ_apply, Minorization.baseK_apply_true,
      Minorization.checkAlpha,
      M.split_apply_true _ M.measurableSet_C, inter_self, ENNReal.toReal_mul, ← pow_mul]
  have hL0 : 0 < M.δ.toReal * c := mul_pos (ENNReal.toReal_pos M.δ_pos.ne' M.δ_ne_top) hc
  have hlimu : Tendsto (atomRenewal M.splitKernel M.checkAlpha (c0, true)) atTop
      (𝓝 (M.δ.toReal * c)) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simp_rw [hu]
    exact hlim.const_mul _
  -- the atom is recurrent
  have hrecα : hitProb M.splitKernel M.checkAlpha (c0, true) = 1 := by
    rw [← (M.isAtom_checkAlpha).potKernel_eq_top_iff hca, potKernel_apply _ _
      M.measurableSet_checkAlpha]
    by_contra hne
    have h0 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne
    have h1 : Tendsto (fun n => atomRenewal M.splitKernel M.checkAlpha (c0, true) (n + 1)) atTop
        (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
      exact this
    have h2 := (tendsto_add_atTop_iff_nat 1).2 hlimu
    exact absurd (tendsto_nhds_unique h2 h1) hL0.ne'
  -- the renewal theorem: the mean return time is finite
  set p := entryLaw M.splitKernel M.measurableSet_checkAlpha (Measure.dirac (c0, true))
  have hp := isIncrementLaw_entryLaw M.splitKernel M.measurableSet_checkAlpha hrecα
  have hren := renewal_theorem hp (M.isAperiodicLaw_entryLaw_checkAlpha hνC)
  rw [← atomRenewal_eq_realRenewalSeq M.isAtom_checkAlpha hca] at hren
  have hinv : (incrMean p)⁻¹ = M.δ.toReal * c := tendsto_nhds_unique hren hlimu
  have hsum : Summable fun n : ℕ => (n : ℝ) * p n := by
    by_contra hns
    rw [incrMean, tsum_eq_zero_of_not_summable hns, inv_zero] at hinv
    exact hL0.ne' hinv.symm
  have htail := (summable_renewalTail_iff hp).2 hsum
  have hmean : meanReturnTime M.splitKernel M.checkAlpha (c0, true) ≠ ∞ := by
    rw [meanReturnTime_eq_tabooPotKernel _ M.measurableSet_checkAlpha, tabooPotKernel,
      Kernel.sum_apply, Measure.sum_apply _ MeasurableSet.univ]
    have heq : ∀ n, tabooKernel M.splitKernel M.measurableSet_checkAlpha n (c0, true) univ =
        ENNReal.ofReal (renewalTail p n) := fun n => by
      rw [renewalTail_entryLaw, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
        (tabooKernel_apply_le_one _ _ n _ univ))]
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (renewalTail_nonneg hp) htail]
    exact ENNReal.ofReal_ne_top
  -- Kac's theorem: the split skeleton is positive
  obtain ⟨-, πs, hπs, hπsinv⟩ := (theorem_10_2_2 hacc hca).1.2 hmean
  have hmarg := (proposition_10_4_1_i M hπsinv).2
  have : IsProbabilityMeasure (πs.map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).2 hπs
  have hQpos : IsPositive (P ^ m : Kernel X X) ψ := ⟨hQmax, _, inferInstance, hmarg⟩
  exact (theorem_10_4_5_positive hψ hap).2.2 ⟨m, hm, hQpos⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.5** (MT p. 329), positivity: let the chain be `ψ`-irreducible and aperiodic and
let `C ∈ B⁺(X)` be `νₘ`-small with `ν(C) > 0`. If `∫ ν_C(dx) Pⁿ(x, C) → P^∞(C) > 0`, where
`ν_C = ν(· ∩ C)/ν(C)`, then the chain is positive. -/
theorem theorem_13_3_5_positive {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) {m : ℕ} {ν : Measure X}
    {C : Set X} (hC : IsSmallSet P m ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun n => (((P ^ n : Kernel X X) ∘ₘ ((ν C)⁻¹ • ν.restrict C)) C).toReal)
      atTop (𝓝 c)) :
    IsPositive P ψ := by
  have := isMarkovKernel_pow P m
  have hfin : ν C ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hC.2.2.2 x hx C).trans prob_le_one)
  set M := Minorization.ofLe (P := (P ^ m : Kernel X X)) hC.1 hC.2.2.2 hνC hfin
  have hMν : M.ν = (ν C)⁻¹ • ν.restrict C := rfl
  have hMC : M.C = C := rfl
  have hνM : 0 < M.ν M.C := by
    rw [hMν, hMC, Measure.smul_apply, Measure.restrict_apply hC.1, inter_self, smul_eq_mul,
      ENNReal.inv_mul_cancel hνC.ne' hfin]
    exact one_pos
  refine isPositive_of_tendsto_split_skeleton hψ hap hC.2.1 M (hMC ▸ hψC) hνM hc ?_
  rw [hMν, hMC]
  exact hlim.comp (tendsto_id.const_mul_atTop' hC.2.1)

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.3.5** (MT p. 329) for a Harris chain: under the hypotheses of
`theorem_13_3_5_positive`, `‖λPⁿ − π‖ → 0` for every initial probability `λ`, where `π` is the
invariant probability, and `P^∞(C) = π(C)`. -/
theorem theorem_13_3_5 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) (hap : IsAperiodic P ψ) {m : ℕ} {ν : Measure X}
    {C : Set X} (hC : IsSmallSet P m ν C) (hψC : 0 < ψ C) (hνC : 0 < ν C) {c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun n => (((P ^ n : Kernel X X) ∘ₘ ((ν C)⁻¹ • ν.restrict C)) C).toReal)
      atTop (𝓝 c)) :
    IsPositive P ψ ∧ ∀ (hpos : IsPositive P ψ) (μ : Measure X) [IsProbabilityMeasure μ],
      haveI := isProbabilityMeasure_stationaryDist hpos
      Tendsto (fun n => tvNorm ((P ^ n : Kernel X X) ∘ₘ μ) (stationaryDist P hpos)) atTop (𝓝 0) ∧
      c = (stationaryDist P hpos C).toReal := by
  have hpos := theorem_13_3_5_positive hH.1 hap hC hψC hνC hc hlim
  refine ⟨hpos, fun hpos μ _ => ?_⟩
  have := isProbabilityMeasure_stationaryDist hpos
  have hπ := isInvariant_stationaryDist hpos
  set π := stationaryDist P hpos
  have hfin : ν C ≠ ∞ := by
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
    have := isMarkovKernel_pow P m
    exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hC.2.2.2 x hx C).trans prob_le_one)
  set νC := (ν C)⁻¹ • ν.restrict C
  have : IsProbabilityMeasure νC := ⟨by
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul,
      ENNReal.inv_mul_cancel hνC.ne' hfin]⟩
  have hconv := theorem_13_3_3 ⟨hH, hpos⟩ hap hπ μ
  refine ⟨hconv, ?_⟩
  have h2 : Tendsto (fun n => (((P ^ n : Kernel X X) ∘ₘ νC) C).toReal) atTop
      (𝓝 (π C).toReal) := by
    have hconvC := theorem_13_3_3 ⟨hH, hpos⟩ hap hπ νC
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hconvC
    have := isMarkovKernel_pow P n
    rw [Real.norm_eq_abs]
    exact abs_measureReal_sub_le_tvNorm _ _ hC.1
  exact tendsto_nhds_unique hlim h2

/-! ### Theorem 13.0.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 13.0.1** (the Aperiodic Ergodic Theorem, MT p. 313), conditions (i), (ii) and
(13.4): for an aperiodic Harris chain the following are equivalent:
(i) the chain is positive;
(ii) there are a small set `C ∈ B⁺(X)` and `P^∞(C) > 0` with `Pⁿ(x, C) → P^∞(C)` for `x ∈ C`;
(13.4) there is an invariant probability `π` with `sup_A |Pⁿ(x, A) − π(A)| → 0` for every `x`. -/
theorem theorem_13_0_1 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    (hap : IsAperiodic P ψ) :
    List.TFAE [IsPositive P ψ,
      ∃ (C : Set X) (m : ℕ) (ν : Measure X) (c : ℝ), IsSmallSet P m ν C ∧ 0 < ψ C ∧ 0 < c ∧
        ∀ x ∈ C, Tendsto (fun n => ((P ^ n : Kernel X X) x C).toReal) atTop (𝓝 c),
      ∃ π : Measure X, IsProbabilityMeasure π ∧ IsInvariant P π ∧
        ∀ x, Tendsto (fun n => tvSup ((P ^ n : Kernel X X) x) π) atTop (𝓝 0)] := by
  have hψ := hH.1
  have hψu : 0 < ψ univ := pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  tfae_have 1 → 3 := fun hpos => by
    have := isProbabilityMeasure_stationaryDist hpos
    exact ⟨stationaryDist P hpos, inferInstance, isInvariant_stationaryDist hpos,
      theorem_13_3_3_sup ⟨hH, hpos⟩ hap (isInvariant_stationaryDist hpos)⟩
  tfae_have 3 → 2 := by
    rintro ⟨π, hπ, hπinv, hconv⟩
    obtain ⟨C, -, m, ν, hC, hψC, -⟩ := theorem_5_2_2 P hψ MeasurableSet.univ hψu
    have hπC : 0 < π C := hπinv.isSubinvariant.pos_of_pos hψ.2.1 (IsProbabilityMeasure.ne_zero π)
      hC.1 hψC
    refine ⟨C, m, ν, (π C).toReal, hC, hψC, ENNReal.toReal_pos hπC.ne' (measure_ne_top π C),
      fun x _ => ?_⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (hconv x)
    have := isMarkovKernel_pow P n
    rw [Real.norm_eq_abs]
    exact abs_sub_le_tvSup _ _ hC.1
  tfae_have 2 → 1 := by
    rintro ⟨C, m, ν, c, hC, hψC, hc, hconv⟩
    have := isMarkovKernel_pow P m
    -- a minorizing measure charging `C`
    obtain ⟨k, hk⟩ := exists_pow_comp_pos hψ.2.1 hC.2.2.1 hC.1 hψC
    have := isMarkovKernel_pow P (k + 1)
    set ν' : Measure X := (P ^ (k + 1) : Kernel X X) ∘ₘ ν
    have hle : ∀ x ∈ C, ν' ≤ (P ^ (m + (k + 1)) : Kernel X X) x := fun x hx => by
      rw [pow_add_eq, Kernel.comp_apply]
      exact comp_le_comp _ (hC.2.2.2 x hx)
    have hν'0 : ν' ≠ 0 := fun h0 => by
      rw [h0, Measure.coe_zero, Pi.zero_apply] at hk
      exact lt_irrefl 0 hk
    have hC' : IsSmallSet P (m + (k + 1)) ν' C := ⟨hC.1, by omega, hν'0, hle⟩
    have hfin : ν' C ≠ ∞ := by
      obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hψC.ne'
      have := isMarkovKernel_pow P (m + (k + 1))
      exact ne_top_of_le_ne_top ENNReal.one_ne_top ((hle x hx C).trans prob_le_one)
    set νC := (ν' C)⁻¹ • ν'.restrict C
    have : IsProbabilityMeasure νC := ⟨by
      rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        smul_eq_mul, ENNReal.inv_mul_cancel hk.ne' hfin]⟩
    have hνCc : νC Cᶜ = 0 := by
      rw [Measure.smul_apply, Measure.restrict_apply hC.1.compl, compl_inter_self, measure_empty,
        smul_zero]
    -- dominated convergence for `∫ ν_C(dx) Pⁿ(x, C)`
    have hlim : Tendsto (fun n => (((P ^ n : Kernel X X) ∘ₘ νC) C).toReal) atTop (𝓝 c) := by
      have hae : ∀ᵐ x ∂νC, Tendsto (fun n => (P ^ n : Kernel X X) x C) atTop
          (𝓝 (ENNReal.ofReal c)) := by
        have : ∀ᵐ x ∂νC, x ∈ C := measure_eq_zero_iff_ae_notMem.1 hνCc |>.mono fun x hx => by
          simpa using hx
        filter_upwards [this] with x hx
        have h := (ENNReal.tendsto_ofReal (hconv x hx))
        refine h.congr fun n => ?_
        have := isMarkovKernel_pow P n
        exact ENNReal.ofReal_toReal (measure_ne_top _ _)
      have h1 : Tendsto (fun n => ∫⁻ x, (P ^ n : Kernel X X) x C ∂νC) atTop
          (𝓝 (∫⁻ _, ENNReal.ofReal c ∂νC)) :=
        tendsto_lintegral_of_dominated_convergence (fun _ => 1)
          (fun n => (Kernel.measurable_coe _ hC.1))
          (fun n => Eventually.of_forall fun x => by
            have := isMarkovKernel_pow P n; exact prob_le_one)
          (by rw [lintegral_one, measure_univ]; exact ENNReal.one_ne_top) hae
      rw [lintegral_const, measure_univ, mul_one] at h1
      have h2 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h1
      rw [ENNReal.toReal_ofReal hc.le] at h2
      refine h2.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [measure_kernel_apply _ _ hC.1]
    have hν'C : 0 < ν' C := hk
    exact theorem_13_3_5_positive hψ hap hC' hψC hν'C hc hlim
  tfae_finish

end MeynTweedie.Positivity
