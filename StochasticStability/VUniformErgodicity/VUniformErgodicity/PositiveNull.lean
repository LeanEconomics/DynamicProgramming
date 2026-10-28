/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import VUniformErgodicity.UniqueInvariant

/-!
# Positive and null chains (MT §10.4.3, Theorem 10.0.1)

Meyn and Tweedie, pp. 230, 246–247. The state space is countably generated where the uniqueness
of Theorem 10.4.4 is used.

**Mean return times.**
* `one_le_meanReturnTime`: `E_x[τ_A] ≥ 1`; `hitProb_eq_one_of_meanReturnTime_ne_top`:
  `E_x[τ_A] < ∞` forces `L(x, A) = 1`.
* `minimalMeasure_univ`: `μ°_A(X) = ∫_A μ(dy) E_y[τ_A]`, the identity in the proof of
  Theorem 10.4.10.

**Results.**
* **Theorem 10.4.10** (p. 246): for a `ψ`-irreducible chain and a subinvariant measure `μ`,
  (i) `theorem_10_4_10_i` (for `μ ≠ 0`): the chain is positive iff `∫_A μ(dy) E_y[τ_A] < ∞`
  for one, and then every, measurable `A` with `μ(A) > 0`; the two halves are
  `theorem_10_4_10_i_of_exists` (which needs no countable generation) and
  `theorem_10_4_10_i_forall`; (ii) `theorem_10_4_10_ii`: if `sup_{y ∈ C} E_y[τ_C] < ∞` for a
  petite `C ∈ B⁺(X)`, the chain is positive and `μ` is finite; if also `E_x[τ_C] < ∞` for every
  `x`, the chain is positive Harris.
* **Theorem 10.0.1**, finiteness (`theorem_10_0_1_finite`, p. 230): for a recurrent chain, the
  invariant measure is finite when `sup_{x ∈ C} E_x[τ_C] < ∞` for a non-empty petite set `C`.

**The invariant probability of a positive chain.**
* `IsPositive.invariant_prob_unique`: a positive chain has exactly one invariant probability;
  `stationaryDist P h` is that probability, with `isProbabilityMeasure_stationaryDist`,
  `isInvariant_stationaryDist` and `eq_stationaryDist`.
* `IsPositive.eq_smul_stationaryDist`: every subinvariant measure of a positive chain is a finite
  multiple of `stationaryDist`, hence finite.
* `isPositive_iff_invMeasure_univ`: a recurrent chain is positive iff its invariant measure is
  finite.

**Corrections.**
* Theorem 10.0.1 needs the petite set `C` to be non-empty: `∅` is petite and
  `sup_{x ∈ ∅} E_x[τ_∅] = 0`, while null recurrent chains exist. The counterexample, a null
  recurrent forward recurrence time chain, is `theorem_10_0_1_counterexample` in
  `CountableInvariant`. For non-empty `C` the bound gives `L(·, C) ≡ 1` on `C` and so `C ∈ B⁺(X)`
  (Theorem 8.3.6), as Theorem 10.4.10 (ii) requires.
* In Theorem 10.4.10 (i), "for every set with `μ(A) > 0`" is read for measurable `A`; for a
  positive chain such sets lie in `B⁺(X)` because `μ` is a multiple of `π ≡ ψ`. The "one set"
  direction of the equivalence needs `μ ≠ 0`: for `μ = 0` there is no set with `μ(A) > 0`.
-/

namespace MeynTweedie.VUniformErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-! ### Mean return times -/

/-- `E_x[τ_A] ≥ 1`, since `τ_A ≥ 1`. -/
theorem one_le_meanReturnTime [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A) (x : X) :
    1 ≤ meanReturnTime P A x := by
  rw [meanReturnTime_eq_tabooPotKernel P hA x, tabooPotKernel_apply P hA x MeasurableSet.univ]
  calc (1 : ℝ≥0∞) = tabooProb P A (0 + 1) x univ := by
        rw [tabooProb_one P A x MeasurableSet.univ, measure_univ]
    _ ≤ _ := ENNReal.le_tsum (f := fun n => tabooProb P A (n + 1) x univ) 0

/-- If `E_x[τ_A] < ∞` then `L(x, A) = 1`. -/
theorem hitProb_eq_one_of_meanReturnTime_ne_top [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {x : X} (h : meanReturnTime P A x ≠ ∞) : hitProb P A x = 1 := by
  have := isMarkovKernel_pathKernel P
  set N := {ω : ℕ → X | firstReturn A ω = ⊤} with hN
  have hNm : MeasurableSet N := by
    have h' := (measurableSet_firstReturn_ne_top hA).compl
    convert h' using 1
    ext ω
    simp [hN]
  have hN0 : pathKernel P x N = 0 := by
    by_contra hne
    apply h
    rw [meanReturnTime_eq_tabooPotKernel P hA x, tabooPotKernel_apply P hA x MeasurableSet.univ]
    refine top_le_iff.1 ?_
    rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hne]
    refine ENNReal.tsum_le_tsum fun n => measure_mono fun ω hω => ?_
    simp only [hN, mem_ofPred_eq] at hω
    exact ⟨mem_univ _, by simp [hω]⟩
  have hc : {ω : ℕ → X | firstReturn A ω ≠ ⊤} = Nᶜ := by ext ω; simp [hN]
  rw [hitProb, hc, prob_compl_eq_one_sub hNm, hN0, tsub_zero]

/-- `μ°_A(X) = ∫_A μ(dy) E_y[τ_A]` (proof of Theorem 10.4.10). -/
theorem minimalMeasure_univ [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (μ : Measure X) :
    minimalMeasure P hA μ univ = ∫⁻ y in A, meanReturnTime P A y ∂μ := by
  rw [minimalMeasure_apply P hA μ MeasurableSet.univ]
  simp_rw [meanReturnTime_eq_tabooPotKernel P hA]

/-! ### Theorem 10.4.10 -/

/-- **Theorem 10.4.10 (i)**, sufficiency (MT p. 246): for a `ψ`-irreducible chain and a
subinvariant `μ`, if `∫_A μ(dy) E_y[τ_A] < ∞` for some measurable `A` with `μ(A) > 0`, the
chain is positive. -/
theorem theorem_10_4_10_i_of_exists [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) {μ : Measure X} (hμ : IsSubinvariant P μ) {A : Set X}
    (hA : MeasurableSet A) (hμA : 0 < μ A) (hfin : ∫⁻ y in A, meanReturnTime P A y ∂μ ≠ ∞) :
    IsPositive P ψ := by
  set M := minimalMeasure P hA μ
  have hMfin : M univ ≠ ∞ := by rw [minimalMeasure_univ]; exact hfin
  have hinv : IsInvariant P M := proposition_10_1_2_iv (proposition_10_4_6 hμ hA) hMfin
  have hM0 : M univ ≠ 0 := by
    rw [minimalMeasure_univ]
    refine (lt_of_lt_of_le hμA ?_).ne'
    calc μ A = ∫⁻ _ in A, 1 ∂μ := by rw [setLIntegral_const, one_mul]
      _ ≤ _ := lintegral_mono fun y => one_le_meanReturnTime hA y
  refine ⟨hψ, (M univ)⁻¹ • M, ⟨?_⟩, hinv.smul _⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hM0 hMfin]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.10 (i)**, necessity (MT p. 246): for a positive chain and any subinvariant
measure `μ`, `∫_A μ(dy) E_y[τ_A] < ∞` for every measurable `A` with `μ(A) > 0`. -/
theorem theorem_10_4_10_i_forall [IsMarkovKernel P] {ψ : Measure X} (hpos : IsPositive P ψ)
    {μ : Measure X} (hμ : IsSubinvariantMeasure P μ) {A : Set X} (hA : MeasurableSet A)
    (hμA : 0 < μ A) : ∫⁻ y in A, meanReturnTime P A y ∂μ ≠ ∞ := by
  have hrec := proposition_10_1_1 hpos
  obtain ⟨-, π, hπ, hinvπ⟩ := hpos
  have hπm : IsInvariantMeasure P π := ⟨inferInstance, hinvπ⟩
  have hπ0 : π ≠ 0 := IsProbabilityMeasure.ne_zero π
  obtain ⟨c, hc, rfl⟩ := hrec.exists_eq_smul hμ hπm.isSubinvariantMeasure hπ0
  have hc0 : c ≠ 0 := by rintro rfl; simp at hμA
  have hπA : 0 < π A := by
    rw [Measure.smul_apply, smul_eq_mul] at hμA
    exact pos_iff_ne_zero.2 fun h => by rw [h, mul_zero] at hμA; exact lt_irrefl _ hμA
  have hψA : 0 < ψ A := pos_iff_ne_zero.2 fun h =>
    hπA.ne' ((theorem_10_4_9_equiv hrec hπm hπ0).1 h)
  have hcinv : IsInvariantMeasure P (c • π) := ⟨hμ.1, hinvπ.smul c⟩
  have hfinA : (c • π) A ≠ ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top hc (measure_ne_top π A)
  rw [← minimalMeasure_univ hA, theorem_10_4_9 hrec hcinv hA hψA hfinA, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  exact hc

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.10 (i)** (MT p. 246): for a `ψ`-irreducible chain and a nonzero subinvariant
measure `μ`, the chain is positive iff `∫_A μ(dy) E_y[τ_A] < ∞` for one, and then for every,
measurable set `A` with `μ(A) > 0`. -/
theorem theorem_10_4_10_i [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {μ : Measure X} (hμ : IsSubinvariantMeasure P μ) (hμ0 : μ ≠ 0) :
    (IsPositive P ψ ↔ ∃ A, MeasurableSet A ∧ 0 < μ A ∧
      ∫⁻ y in A, meanReturnTime P A y ∂μ ≠ ∞) ∧
    (IsPositive P ψ → ∀ A, MeasurableSet A → 0 < μ A →
      ∫⁻ y in A, meanReturnTime P A y ∂μ ≠ ∞) := by
  have hu : 0 < μ univ := pos_iff_ne_zero.2 fun h => hμ0 (Measure.measure_univ_eq_zero.1 h)
  exact ⟨⟨fun hpos => ⟨univ, MeasurableSet.univ, hu,
      theorem_10_4_10_i_forall hpos hμ MeasurableSet.univ hu⟩,
    fun ⟨A, hA, hμA, hfin⟩ => theorem_10_4_10_i_of_exists hψ hμ.2 hA hμA hfin⟩,
    fun hpos A hA hμA => theorem_10_4_10_i_forall hpos hμ hA hμA⟩

/-! ### The invariant probability of a positive chain -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- A positive chain has exactly one invariant probability measure. -/
theorem IsPositive.invariant_prob_unique [IsMarkovKernel P] {ψ : Measure X}
    (hpos : IsPositive P ψ) {π π' : Measure X} [IsProbabilityMeasure π]
    [IsProbabilityMeasure π'] (hπ : IsInvariant P π) (hπ' : IsInvariant P π') : π = π' := by
  have hrec := proposition_10_1_1 hpos
  obtain ⟨c, -, hc⟩ := hrec.exists_eq_smul ⟨inferInstance, hπ.isSubinvariant⟩
    ⟨inferInstance, hπ'.isSubinvariant⟩ (IsProbabilityMeasure.ne_zero π')
  have h1 := congrArg (fun m : Measure X => m univ) hc
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at h1
  rw [hc, ← h1, one_smul]

/-- The invariant probability measure `π` of a positive chain (MT p. 236: "we shall use `π` to
denote the unique invariant measure ... normalized to be a probability measure"). -/
noncomputable def stationaryDist (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (h : IsPositive P ψ) : Measure X :=
  Classical.choose h.2

/-- `stationaryDist` is a probability measure. -/
theorem isProbabilityMeasure_stationaryDist [IsMarkovKernel P] {ψ : Measure X}
    (h : IsPositive P ψ) : IsProbabilityMeasure (stationaryDist P h) :=
  (Classical.choose_spec h.2).1

/-- `stationaryDist` is invariant. -/
theorem isInvariant_stationaryDist [IsMarkovKernel P] {ψ : Measure X} (h : IsPositive P ψ) :
    IsInvariant P (stationaryDist P h) :=
  (Classical.choose_spec h.2).2

variable [MeasurableSpace.CountablyGenerated X] in
/-- Every invariant probability of a positive chain is `stationaryDist`. -/
theorem eq_stationaryDist [IsMarkovKernel P] {ψ : Measure X} (h : IsPositive P ψ)
    {π : Measure X} [IsProbabilityMeasure π] (hπ : IsInvariant P π) : π = stationaryDist P h :=
  have := isProbabilityMeasure_stationaryDist h
  h.invariant_prob_unique hπ (isInvariant_stationaryDist h)

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a positive chain every subinvariant measure is a finite multiple of `stationaryDist`;
in particular it is finite. -/
theorem IsPositive.eq_smul_stationaryDist [IsMarkovKernel P] {ψ : Measure X}
    (h : IsPositive P ψ) {μ : Measure X} (hμ : IsSubinvariantMeasure P μ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • stationaryDist P h := by
  have := isProbabilityMeasure_stationaryDist h
  exact (proposition_10_1_1 h).exists_eq_smul hμ ⟨inferInstance,
    (isInvariant_stationaryDist h).isSubinvariant⟩ (IsProbabilityMeasure.ne_zero _)

variable [MeasurableSpace.CountablyGenerated X] in
/-- A recurrent chain is positive iff its invariant measure is finite. -/
theorem isPositive_iff_invMeasure_univ [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) : IsPositive P ψ ↔ invMeasure P hrec univ ≠ ∞ := by
  have hπ := isInvariantMeasure_invMeasure hrec
  have hπ0 := invMeasure_ne_zero hrec
  constructor
  · intro hpos
    obtain ⟨c, hc, he⟩ := hpos.eq_smul_stationaryDist hπ.isSubinvariantMeasure
    have := isProbabilityMeasure_stationaryDist hpos
    rw [he, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact hc
  · intro hfin
    have h0 : invMeasure P hrec univ ≠ 0 := fun h => hπ0 (Measure.measure_univ_eq_zero.1 h)
    refine ⟨hrec.1, (invMeasure P hrec univ)⁻¹ • invMeasure P hrec, ⟨?_⟩, hπ.2.smul _⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hfin]

/-! ### Theorem 10.4.10 (ii) and Theorem 10.0.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.10 (ii)** (MT p. 247): for a `ψ`-irreducible chain, if a petite set
`C ∈ B⁺(X)` has `sup_{y ∈ C} E_y[τ_C] < ∞` (10.33), then the chain is positive and every
subinvariant measure `μ` is finite; if also `E_x[τ_C] < ∞` for every `x` (10.34), the chain is
positive Harris. -/
theorem theorem_10_4_10_ii [IsMarkovKernel P] {ψ : Measure X} (hψ : IsMaximalIrreducibility P ψ)
    {C : Set X} (hC : IsPetite P C) (hψC : 0 < ψ C) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hbound : ∀ y ∈ C, meanReturnTime P C y ≤ K) :
    IsPositive P ψ ∧ (∀ μ, IsSubinvariantMeasure P μ → μ univ ≠ ∞) ∧
      ((∀ x, meanReturnTime P C x ≠ ∞) → IsPositiveHarris P ψ) := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hL : ∀ y ∈ C, hitProb P C y = 1 := fun y hy =>
    hitProb_eq_one_of_meanReturnTime_ne_top hCm (ne_top_of_le_ne_top hK (hbound y hy))
  have hne : C.Nonempty := nonempty_of_measure_ne_zero hψC.ne'
  have hrec := (theorem_8_3_6_i P hψ hC hne hL).1
  have hπ := isInvariantMeasure_invMeasure hrec
  have hπ0 := invMeasure_ne_zero hrec
  have hπC : invMeasure P hrec C < ∞ := hπ.isSubinvariantMeasure.measure_lt_top_of_petite hψ hC
  have hπCpos : 0 < invMeasure P hrec C := hπ.2.isSubinvariant.pos_of_pos hψ.2.1 hπ0 hCm hψC
  have hint : ∫⁻ y in C, meanReturnTime P C y ∂invMeasure P hrec ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hK hπC.ne) ?_
    calc ∫⁻ y in C, meanReturnTime P C y ∂invMeasure P hrec
        ≤ ∫⁻ _ in C, K ∂invMeasure P hrec := setLIntegral_mono measurable_const hbound
      _ = K * invMeasure P hrec C := setLIntegral_const _ _
  have hpos := theorem_10_4_10_i_of_exists hψ hπ.2.isSubinvariant hCm hπCpos hint
  refine ⟨hpos, fun μ hμ => ?_, fun hall => ⟨proposition_9_1_7_ii hψ hC fun x =>
    hitProb_eq_one_of_meanReturnTime_ne_top hCm (hall x), hpos⟩⟩
  obtain ⟨c, hc, he⟩ := hpos.eq_smul_stationaryDist hμ
  have := isProbabilityMeasure_stationaryDist hpos
  rw [he, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact hc

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.0.1**, finiteness (MT p. 230): for a recurrent chain, every invariant measure is
finite if `sup_{x ∈ C} E_x[τ_C] < ∞` for a non-empty petite set `C`. -/
theorem theorem_10_0_1_finite [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ)
    {C : Set X} (hC : IsPetite P C) (hne : C.Nonempty) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hbound : ∀ x ∈ C, meanReturnTime P C x ≤ K) {π : Measure X}
    (hπ : IsInvariantMeasure P π) : π univ ≠ ∞ := by
  have hCm : MeasurableSet C := by obtain ⟨_, _, h⟩ := hC; exact h.1
  have hL : ∀ y ∈ C, hitProb P C y = 1 := fun y hy =>
    hitProb_eq_one_of_meanReturnTime_ne_top hCm (ne_top_of_le_ne_top hK (hbound y hy))
  have hψC := (theorem_8_3_6_i P hrec.1 hC hne hL).2
  exact (theorem_10_4_10_ii hrec.1 hC hψC hK hbound).2.1 π hπ.isSubinvariantMeasure

end MeynTweedie.VUniformErgodicity
