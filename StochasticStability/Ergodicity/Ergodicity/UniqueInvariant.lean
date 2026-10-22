/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Ergodicity.SplitInvariant
import Ergodicity.HarrisDecomposition

/-!
# The invariant measure of a recurrent chain (MT §10.4.1, §10.4.3, Theorem 10.0.1)

Meyn and Tweedie, pp. 230, 242–246. The state space is countably generated throughout (the
book's standing assumption, used through the existence of small sets, Theorem 5.2.2).

**Existence and uniqueness.**
* **Theorem 10.4.4** (`theorem_10_4_4`, p. 242): a recurrent chain has a nonzero invariant
  measure `π`, and every subinvariant measure is a finite multiple of `π`; in particular every
  subinvariant measure is invariant (`IsRecurrentChain.isInvariant_of_isSubinvariantMeasure`).
  The proof is the book's: split the resolvent `K_{a_{1/2}}` (Proposition 10.4.2) and transfer
  invariance back with Theorem 10.4.3.
* `IsRecurrentChain.exists_eq_smul`: any two subinvariant measures, the second nonzero, are
  proportional with a finite constant.
* `invMeasure P h` is a chosen nonzero invariant measure of the recurrent chain, with
  `isInvariantMeasure_invMeasure`, `invMeasure_ne_zero` and `eq_smul_invMeasure`.

**Skeletons.**
* **Theorem 10.4.5** (p. 243): for an aperiodic recurrent chain, `theorem_10_4_5`: a σ-finite
  measure is invariant for the `m`-skeleton iff it is invariant for `Φ`;
  `theorem_10_4_5_positive`: an aperiodic chain is positive iff every `m`-skeleton is positive,
  iff some `m`-skeleton is positive.

**The structure of `π`** (§10.4.3).
* `tabooPotKernel_le_potKernel`: `U_A ≤ U`.
* **Theorem 10.4.9** (p. 246): for a recurrent chain and a nonzero invariant measure `π`,
  `theorem_10_4_9_equiv`: `π` is equivalent to `ψ`; `theorem_10_4_9`: for every `A ∈ B⁺(X)`
  with `π(A) < ∞`, `π(B) = ∫_A π(dy) U_A(y, B)` (10.31); `theorem_10_4_9_path`: the same as
  `∫_A π(dy) E_y[Σ_{k=1}^{τ_A} 1{Φₖ ∈ B}]`; `theorem_10_4_9_path'`: the same as
  `∫_A π(dy) E_y[Σ_{k=0}^{τ_A − 1} 1{Φₖ ∈ B}]`, through the pathwise identity
  `sum_before_return_add`.
* **Theorem 10.0.1** (`theorem_10_0_1`, p. 230), existence, uniqueness and the representation
  (10.2); its finiteness criterion is `theorem_10_0_1_finite` in `PositiveNull`.

**Hypotheses added.**
* Theorem 10.4.5 (first part) is proved for recurrent chains: the book's proof uses the uniqueness
  of the invariant measure of the `m`-skeleton (Theorem 10.4.4 for `Pᵐ`), which needs `Pᵐ`, and
  hence `Φ`, to be recurrent. The positivity statement needs no recurrence (positive chains are
  recurrent).
* In (10.31) and (10.2) the set `A ∈ B⁺(X)` is taken with `π(A) < ∞`, the standing assumption
  of §10.4.2 (`0 < μ(A) < ∞`) on which Theorem 10.4.7 rests.
-/

namespace MeynTweedie.Ergodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {P : Kernel X X}

/-! ### Theorem 10.4.4 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.4** (MT p. 242): a recurrent chain has a nonzero invariant measure `π`, and
every subinvariant measure is a finite multiple `c π` of it. -/
theorem theorem_10_4_4 [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ) :
    ∃ π : Measure X, IsInvariantMeasure P π ∧ π ≠ 0 ∧
      ∀ μ, IsSubinvariantMeasure P μ → ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • π := by
  have hε0 : (0 : ℝ≥0∞) < 2⁻¹ := by simp
  have hε1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have := isMarkovKernel_resolvent P hε1
  have hrecK : IsRecurrentChain (resolvent P 2⁻¹) ψ :=
    ((proposition_8_2_4 P hrec.1 hε0 hε1).2).1 hrec
  obtain ⟨M, -, hC⟩ := theorem_5_2_3_resolvent P hrec.1 hε0 hε1
  obtain ⟨π, ⟨hσ, hinvK⟩, hπ0, -, huniq⟩ := proposition_10_4_2 hrecK M hC
  have hinv : IsInvariant P π := (theorem_10_4_3 hε0 hε1).1 hinvK
  exact ⟨π, ⟨hσ, hinv⟩, hπ0, fun μ hμ => huniq μ ⟨hμ.1, hμ.2.resolvent hε1⟩⟩

variable [MeasurableSpace.CountablyGenerated X] in
/-- Theorem 10.4.4: for a recurrent chain every subinvariant measure is invariant. -/
theorem IsRecurrentChain.isInvariant_of_isSubinvariantMeasure [IsMarkovKernel P]
    {ψ : Measure X} (hrec : IsRecurrentChain P ψ) {μ : Measure X}
    (hμ : IsSubinvariantMeasure P μ) : IsInvariant P μ := by
  obtain ⟨π, hπ, -, huniq⟩ := theorem_10_4_4 hrec
  obtain ⟨c, -, rfl⟩ := huniq μ hμ
  exact hπ.2.smul c

variable [MeasurableSpace.CountablyGenerated X] in
/-- Theorem 10.4.4, uniqueness up to constant multiples: for a recurrent chain, any two
subinvariant measures `μ`, `ν` with `ν ≠ 0` satisfy `μ = c ν` for a finite `c`. -/
theorem IsRecurrentChain.exists_eq_smul [IsMarkovKernel P] {ψ : Measure X}
    (hrec : IsRecurrentChain P ψ) {μ ν : Measure X} (hμ : IsSubinvariantMeasure P μ)
    (hν : IsSubinvariantMeasure P ν) (hν0 : ν ≠ 0) : ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • ν := by
  obtain ⟨π, -, -, huniq⟩ := theorem_10_4_4 hrec
  obtain ⟨a, ha, rfl⟩ := huniq μ hμ
  obtain ⟨b, hb, rfl⟩ := huniq ν hν
  have hb0 : b ≠ 0 := by rintro rfl; exact hν0 (zero_smul _ _)
  refine ⟨a * b⁻¹, ENNReal.mul_ne_top ha (ENNReal.inv_ne_top.2 hb0), ?_⟩
  rw [smul_smul, mul_assoc, ENNReal.inv_mul_cancel hb0 hb, mul_one]

variable [MeasurableSpace.CountablyGenerated X] in
/-- A chosen nonzero invariant measure `π` of a recurrent chain (Theorem 10.4.4); it is unique
up to a constant multiple. -/
noncomputable def invMeasure (P : Kernel X X) [IsMarkovKernel P] {ψ : Measure X}
    (h : IsRecurrentChain P ψ) : Measure X :=
  Classical.choose (theorem_10_4_4 h)

variable [MeasurableSpace.CountablyGenerated X] in
/-- `invMeasure` is an invariant measure. -/
theorem isInvariantMeasure_invMeasure [IsMarkovKernel P] {ψ : Measure X}
    (h : IsRecurrentChain P ψ) : IsInvariantMeasure P (invMeasure P h) :=
  (Classical.choose_spec (theorem_10_4_4 h)).1

variable [MeasurableSpace.CountablyGenerated X] in
/-- `invMeasure` is nonzero. -/
theorem invMeasure_ne_zero [IsMarkovKernel P] {ψ : Measure X} (h : IsRecurrentChain P ψ) :
    invMeasure P h ≠ 0 :=
  (Classical.choose_spec (theorem_10_4_4 h)).2.1

variable [MeasurableSpace.CountablyGenerated X] in
/-- Every subinvariant measure is a finite multiple of `invMeasure`. -/
theorem eq_smul_invMeasure [IsMarkovKernel P] {ψ : Measure X} (h : IsRecurrentChain P ψ)
    {μ : Measure X} (hμ : IsSubinvariantMeasure P μ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • invMeasure P h :=
  (Classical.choose_spec (theorem_10_4_4 h)).2.2 μ hμ

/-! ### Theorem 10.4.5 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.5** (MT p. 243), for a recurrent aperiodic chain: a σ-finite measure is
invariant for the `m`-skeleton (`m ≥ 1`) iff it is invariant for `Φ`. -/
theorem theorem_10_4_5 [IsMarkovKernel P] {ψ : Measure X} (hap : IsAperiodic P ψ)
    (hrec : IsRecurrentChain P ψ) {m : ℕ} (hm : 1 ≤ m) {π : Measure X} [SigmaFinite π] :
    IsInvariant (P ^ m) π ↔ IsInvariant P π := by
  refine ⟨fun h => ?_, fun h => h.pow m⟩
  have := isMarkovKernel_pow P m
  have hrecm : IsRecurrentChain (P ^ m) ψ := (theorem_8_2_6_ii P hrec.1 hap).2.1 hrec m hm
  obtain ⟨π0, ⟨hσ0, hinv0⟩, hπ00, -⟩ := theorem_10_4_4 hrec
  obtain ⟨c, -, rfl⟩ := hrecm.exists_eq_smul ⟨inferInstance, h.isSubinvariant⟩
    ⟨hσ0, (hinv0.pow m).isSubinvariant⟩ hπ00
  exact hinv0.smul c

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.5**, positivity (MT p. 243): an aperiodic chain is positive iff every
`m`-skeleton is positive, iff some `m`-skeleton (`m ≥ 1`) is positive. -/
theorem theorem_10_4_5_positive [IsMarkovKernel P] {ψ : Measure X}
    (hψ : IsMaximalIrreducibility P ψ) (hap : IsAperiodic P ψ) :
    (IsPositive P ψ ↔ ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m; IsPositive (P ^ m) ψ) ∧
      (IsPositive P ψ ↔ ∃ m, 1 ≤ m ∧ haveI := isMarkovKernel_pow P m; IsPositive (P ^ m) ψ) := by
  have hsk := (proposition_5_4_5_iii P hψ hap).1
  have hall : IsPositive P ψ → ∀ m, 1 ≤ m → haveI := isMarkovKernel_pow P m;
      IsPositive (P ^ m) ψ := by
    rintro ⟨-, π, hπ, hinv⟩ m hm
    have := isMarkovKernel_pow P m
    exact ⟨(hsk m hm).1, π, hπ, hinv.pow m⟩
  have hsome : (∃ m, 1 ≤ m ∧ haveI := isMarkovKernel_pow P m; IsPositive (P ^ m) ψ) →
      IsPositive P ψ := by
    rintro ⟨m, hm, hpos⟩
    have := isMarkovKernel_pow P m
    have hrecm := proposition_10_1_1 hpos
    have hrec : IsRecurrentChain P ψ := (theorem_8_2_6_ii P hψ hap).1.2 ⟨m, hm, hrecm⟩
    obtain ⟨-, π, hπ, hinv⟩ := hpos
    exact ⟨hψ, π, hπ, (theorem_10_4_5 hap hrec hm).1 hinv⟩
  exact ⟨⟨hall, fun h => hsome ⟨1, le_rfl, h 1 le_rfl⟩⟩,
    ⟨fun h => ⟨1, le_rfl, hall h 1 le_rfl⟩, hsome⟩⟩

/-! ### Theorem 10.4.9 -/

/-- `U_A(x, B) ≤ U(x, B)`: visits before the return to `A` are visits. -/
theorem tabooPotKernel_le_potKernel [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    (x : X) {B : Set X} (hB : MeasurableSet B) : tabooPotKernel P hA x B ≤ potKernel P x B := by
  rw [tabooPotKernel_apply P hA x hB, potKernel_apply P x hB]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [tabooProb, ← pathKernel_coord_mem P x (n + 1) hB]
  exact measure_mono inter_subset_left

/-- If `L(y, B) = 0` then `U_A(y, B) = 0`. -/
theorem tabooPotKernel_eq_zero_of_hitProb [IsMarkovKernel P] {A : Set X} (hA : MeasurableSet A)
    {B : Set X} (hB : MeasurableSet B) {y : X} (hy : hitProb P B y = 0) :
    tabooPotKernel P hA y B = 0 := by
  refine le_antisymm ((tabooPotKernel_le_potKernel hA y hB).trans (le_of_eq ?_)) zero_le
  by_contra h
  have hpos := (potKernel_pos_iff P hB y).1 (pos_iff_ne_zero.2 h)
  rw [← hitProb_pos_iff P hB y] at hpos
  exact hpos.ne' hy

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.9**, equivalence (MT p. 246): for a recurrent chain, a nonzero invariant
measure `π` is equivalent to `ψ`. -/
theorem theorem_10_4_9_equiv [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ)
    {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) : π ≪ ψ ∧ ψ ≪ π := by
  have hψ := hrec.1
  refine ⟨Measure.AbsolutelyContinuous.mk fun B hB hψB => ?_,
    proposition_10_1_2_ii hψ.2.1 hπ.2.isSubinvariant hπ0⟩
  have := hπ.1
  set A := noHitSet P B with hAdef
  have hAm : MeasurableSet A := measurable_hitProb P hB (measurableSet_singleton 0)
  have hψA : 0 < ψ A := by
    have hnull := hψ.hitSet_null hB hψB
    have hu : ψ univ ≤ ψ A + ψ {y | 0 < hitProb P B y} := by
      refine le_trans (measure_mono fun y _ => ?_) (measure_union_le _ _)
      by_cases h : hitProb P B y = 0
      · exact Or.inl h
      · exact Or.inr (pos_iff_ne_zero.2 h)
    rw [hnull, add_zero] at hu
    exact lt_of_lt_of_le (pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)) hu
  -- `π°_A ≤ π` is a nonzero subinvariant measure with `π°_A(B) = 0`
  have hle := proposition_10_4_6_minimal hπ.2.isSubinvariant hAm
  have hsub := proposition_10_4_6 hπ.2.isSubinvariant hAm
  have hσ : SigmaFinite (minimalMeasure P hAm π) := Measure.sigmaFinite_of_le π hle
  obtain ⟨c, -, hc⟩ := hrec.exists_eq_smul ⟨hσ, hsub⟩ hπ.isSubinvariantMeasure hπ0
  have hB0 : minimalMeasure P hAm π B = 0 := by
    rw [minimalMeasure_apply P hAm π hB]
    refine (setLIntegral_congr_fun hAm fun y hy => ?_).trans lintegral_zero
    exact tabooPotKernel_eq_zero_of_hitProb hAm hB hy
  have hA0 : minimalMeasure P hAm π A ≠ 0 := by
    rw [minimalMeasure_self P hAm π]
    have hπA : π A ≠ 0 := (hπ.2.isSubinvariant.pos_of_pos hψ.2.1 hπ0 hAm hψA).ne'
    have hne : π.restrict A ≠ 0 := by
      intro h; apply hπA; rw [← Measure.restrict_apply_univ, h]; rfl
    exact (lintegral_pos_of_pos hne (measurable_hitProb P hAm) (hψ.2.1 A hAm hψA)).ne'
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hA0 (by rw [hc]; rfl)
  rw [hc, Measure.smul_apply, smul_eq_mul] at hB0
  exact (mul_eq_zero.1 hB0).resolve_left hc0

variable [MeasurableSpace.CountablyGenerated X] in
/-- For a recurrent chain, a nonzero invariant measure `π` and `A ∈ B⁺(X)`: `L(x, A) = 1` for
`π`-almost every `x` (the chain is Harris off a `ψ`-null set). -/
theorem ae_hitProb_eq_one [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ)
    {π : Measure X} (hπ : IsInvariantMeasure P π) (hπ0 : π ≠ 0) {A : Set X}
    (hA : MeasurableSet A) (hψA : 0 < ψ A) : ∀ᵐ x ∂π, hitProb P A x = 1 := by
  obtain ⟨H, hH, -, hψH⟩ := theorem_9_1_5 hrec
  have hπH : π Hᶜ = 0 := (theorem_10_4_9_equiv hrec hπ hπ0).1 hψH
  refine measure_mono_null (fun x hx => ?_) hπH
  intro hxH
  exact hx (le_antisymm (hitProb_le_one P A x)
    ((hH.2.2.2.2 A hA hψA x hxH).symm.le.trans (harrisQ_le_hitProb P A x)))

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.9** (MT p. 246), (10.31): for a recurrent chain, an invariant measure `π` and
`A ∈ B⁺(X)` with `π(A) < ∞`, `π = π°_A`, that is `π(B) = ∫_A π(dy) U_A(y, B)`. -/
theorem theorem_10_4_9 [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ)
    {π : Measure X} (hπ : IsInvariantMeasure P π) {A : Set X} (hA : MeasurableSet A)
    (hψA : 0 < ψ A) (hπA : π A ≠ ∞) : minimalMeasure P hA π = π := by
  by_cases hπ0 : π = 0
  · subst hπ0
    simp [minimalMeasure, Measure.bind_zero_left]
  have hL : ∀ᵐ x ∂π.restrict A, hitProb P A x = 1 :=
    ae_restrict_of_ae (ae_hitProb_eq_one hrec hπ hπ0 hA hψA)
  have hsub := hπ.2.isSubinvariant
  have hinv := (theorem_10_4_7_ii hsub hA hπA hL).1
  have hσ : SigmaFinite (minimalMeasure P hA π) :=
    have := hπ.1
    Measure.sigmaFinite_of_le π (proposition_10_4_6_minimal hsub hA)
  obtain ⟨c, -, hc⟩ := hrec.exists_eq_smul ⟨hσ, hinv.isSubinvariant⟩ hπ.isSubinvariantMeasure
    hπ0
  have hself := minimalMeasure_self_eq hA hL
  have hπApos : π A ≠ 0 := (hsub.pos_of_pos hrec.1.2.1 hπ0 hA hψA).ne'
  rw [hc, Measure.smul_apply, smul_eq_mul] at hself
  have hc1 : c = 1 := (ENNReal.mul_eq_right hπApos hπA).1 hself
  rw [hc, hc1, one_smul]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.9**, second form of (10.31): `π(B) = ∫_A π(dy) E_y[Σ_{k=1}^{τ_A} 1{Φₖ ∈ B}]`. -/
theorem theorem_10_4_9_path [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ)
    {π : Measure X} (hπ : IsInvariantMeasure P π) {A : Set X} (hA : MeasurableSet A)
    (hψA : 0 < ψ A) (hπA : π A ≠ ∞) {B : Set X} (hB : MeasurableSet B) :
    π B = ∫⁻ y in A, ∫⁻ ω, ∑' n : ℕ, ({ω : ℕ → X | ω (n + 1) ∈ B} ∩
      {ω | WithTop.some (n + 1) ≤ firstReturn A ω}).indicator 1 ω ∂pathKernel P y ∂π := by
  conv_lhs => rw [← theorem_10_4_9 hrec hπ hA hψA hπA]
  rw [minimalMeasure_apply P hA π hB]
  exact setLIntegral_congr_fun hA fun y _ => tabooPotKernel_eq_lintegral P hA y hB

omit [MeasurableSpace X] in
/-- `τ_A ≥ n + 2` iff `τ_A ≥ n + 1` and `Φₙ₊₁ ∉ A`. -/
theorem le_firstReturn_add_two_iff (A : Set X) (ω : ℕ → X) (n : ℕ) :
    WithTop.some (n + 1 + 1) ≤ firstReturn A ω ↔
      WithTop.some (n + 1) ≤ firstReturn A ω ∧ ω (n + 1) ∉ A := by
  rw [le_firstReturn_iff, le_firstReturn_iff]
  constructor
  · intro h
    exact ⟨fun j h1 h2 => h j h1 (by omega), h (n + 1) (by omega) (by omega)⟩
  · rintro ⟨h, hn⟩ j h1 h2
    by_cases hj : j = n + 1
    · rw [hj]; exact hn
    · exact h j h1 (by omega)

omit [MeasurableSpace X] in
/-- The pathwise identity behind the third form of (10.31):
`Σ_{k=0}^{τ_A − 1} 1_B(Φₖ) + 1{τ_A < ∞} 1_{B ∩ A}(Φ_{τ_A}) = 1_B(Φ₀) + Σ_{k=1}^{τ_A} 1_B(Φₖ)`. -/
theorem sum_before_return_add (A B : Set X) (ω : ℕ → X) :
    (∑' k : ℕ, ({ω : ℕ → X | ω k ∈ B} ∩
      {ω | WithTop.some (k + 1) ≤ firstReturn A ω}).indicator (1 : (ℕ → X) → ℝ≥0∞) ω) +
      ∑' n : ℕ, ({ω : ℕ → X | ω (n + 1) ∈ B ∩ A} ∩
        {ω | WithTop.some (n + 1) ≤ firstReturn A ω}).indicator 1 ω =
    B.indicator 1 (ω 0) + ∑' n : ℕ, ({ω : ℕ → X | ω (n + 1) ∈ B} ∩
      {ω | WithTop.some (n + 1) ≤ firstReturn A ω}).indicator 1 ω := by
  rw [tsum_eq_zero_add' ENNReal.summable, add_assoc, ← ENNReal.tsum_add]
  congr 1
  · by_cases h : ω 0 ∈ B
    · have h' : WithTop.some (0 + 1) ≤ firstReturn A ω := one_le_firstReturn A ω
      simp only [indicator, mem_inter_iff, mem_ofPred_eq, h, h', and_self, ite_true,
        Pi.one_apply]
    · simp only [indicator, mem_inter_iff, mem_ofPred_eq, h, false_and, ite_false]
  · refine tsum_congr fun n => ?_
    have key := le_firstReturn_add_two_iff A ω n
    by_cases hB : ω (n + 1) ∈ B
    · by_cases h1 : WithTop.some (n + 1) ≤ firstReturn A ω
      · by_cases hA : ω (n + 1) ∈ A
        · have h2 : ¬ WithTop.some (n + 1 + 1) ≤ firstReturn A ω := fun h => (key.1 h).2 hA
          simp only [indicator, mem_inter_iff, mem_ofPred_eq, hB, hA, h1, h2, and_self,
            and_false, ite_true, ite_false, zero_add]
        · have h2 : WithTop.some (n + 1 + 1) ≤ firstReturn A ω := key.2 ⟨h1, hA⟩
          simp only [indicator, mem_inter_iff, mem_ofPred_eq, hB, hA, h1, h2, and_self,
            and_false, false_and, ite_true, ite_false, add_zero]
      · have h2 : ¬ WithTop.some (n + 1 + 1) ≤ firstReturn A ω := fun h => h1 (key.1 h).1
        simp only [indicator, mem_inter_iff, mem_ofPred_eq, hB, h1, h2, and_false,
          ite_false, add_zero]
    · simp only [indicator, mem_inter_iff, mem_ofPred_eq, hB, false_and, ite_false, add_zero]

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.4.9**, third form of (10.31):
`π(B) = ∫_A π(dy) E_y[Σ_{k=0}^{τ_A − 1} 1{Φₖ ∈ B}]`. -/
theorem theorem_10_4_9_path' [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ)
    {π : Measure X} (hπ : IsInvariantMeasure P π) {A : Set X} (hA : MeasurableSet A)
    (hψA : 0 < ψ A) (hπA : π A ≠ ∞) {B : Set X} (hB : MeasurableSet B) :
    π B = ∫⁻ y in A, ∫⁻ ω, ∑' k : ℕ, ({ω : ℕ → X | ω k ∈ B} ∩
      {ω | WithTop.some (k + 1) ≤ firstReturn A ω}).indicator 1 ω ∂pathKernel P y ∂π := by
  have hmin := theorem_10_4_9 hrec hπ hA hψA hπA
  have hBA : MeasurableSet (B ∩ A) := hB.inter hA
  have hmS : Measurable fun ω : ℕ → X => ∑' k : ℕ, ({ω : ℕ → X | ω k ∈ B} ∩
      {ω | WithTop.some (k + 1) ≤ firstReturn A ω}).indicator (1 : (ℕ → X) → ℝ≥0∞) ω :=
    Measurable.tsum fun k => measurable_one.indicator
      ((measurable_pi_apply k hB).inter (measurableSet_le_firstReturn hA (k + 1)))
  -- integrate the pathwise identity under `P_y`
  have hy : ∀ y, ∫⁻ ω, ∑' k : ℕ, ({ω : ℕ → X | ω k ∈ B} ∩
      {ω | WithTop.some (k + 1) ≤ firstReturn A ω}).indicator 1 ω ∂pathKernel P y +
      tabooPotKernel P hA y (B ∩ A) = B.indicator 1 y + tabooPotKernel P hA y B := by
    intro y
    rw [tabooPotKernel_eq_lintegral P hA y hBA, tabooPotKernel_eq_lintegral P hA y hB,
      ← lintegral_add_left hmS]
    have h0 : B.indicator 1 y = ∫⁻ ω, B.indicator (1 : X → ℝ≥0∞) (ω 0) ∂pathKernel P y := by
      rw [← pathKernel_zero_mem P y hB,
        ← lintegral_indicator_one (s := {ω : ℕ → X | ω 0 ∈ B}) (measurable_pi_apply 0 hB)]
      refine lintegral_congr fun ω => ?_
      by_cases h : ω 0 ∈ B
      · simp only [indicator, mem_ofPred_eq, h, ite_true, Pi.one_apply]
      · simp only [indicator, mem_ofPred_eq, h, ite_false]
    have hm0 : Measurable fun ω : ℕ → X => B.indicator (1 : X → ℝ≥0∞) (ω 0) :=
      (measurable_one.indicator hB).comp (measurable_pi_apply 0)
    rw [h0, ← lintegral_add_left hm0]
    exact lintegral_congr fun ω => sum_before_return_add A B ω
  have hint := congrArg (fun f : X → ℝ≥0∞ => ∫⁻ y in A, f y ∂π) (funext hy)
  have hm1 : Measurable fun y => ∫⁻ ω, ∑' k : ℕ, ({ω : ℕ → X | ω k ∈ B} ∩
      {ω | WithTop.some (k + 1) ≤ firstReturn A ω}).indicator 1 ω ∂pathKernel P y :=
    hmS.lintegral_kernel
  rw [lintegral_add_left hm1, lintegral_add_left (measurable_one.indicator hB)] at hint
  rw [← minimalMeasure_apply P hA π hBA, ← minimalMeasure_apply P hA π hB, hmin,
    lintegral_indicator_one hB, Measure.restrict_apply hB] at hint
  have hfin : π (B ∩ A) ≠ ∞ := ne_top_of_le_ne_top hπA (measure_mono inter_subset_right)
  rw [add_comm (π (B ∩ A))] at hint
  exact ((ENNReal.add_left_inj hfin).1 hint).symm

/-! ### Theorem 10.0.1 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 10.0.1** (MT p. 230), existence, uniqueness and representation: a recurrent chain
has a nonzero invariant measure `π`, unique up to finite constant multiples among subinvariant
measures, and for every `A ∈ B⁺(X)` with `π(A) < ∞`,
`π(B) = ∫_A π(dw) E_w[Σ_{n=1}^{τ_A} 1{Φₙ ∈ B}]` (10.2). -/
theorem theorem_10_0_1 [IsMarkovKernel P] {ψ : Measure X} (hrec : IsRecurrentChain P ψ) :
    ∃ π : Measure X, IsInvariantMeasure P π ∧ π ≠ 0 ∧
      (∀ μ, IsSubinvariantMeasure P μ → ∃ c : ℝ≥0∞, c ≠ ∞ ∧ μ = c • π) ∧
      ∀ A, MeasurableSet A → 0 < ψ A → π A ≠ ∞ → ∀ B, MeasurableSet B →
        π B = ∫⁻ w in A, ∫⁻ ω, ∑' n : ℕ, ({ω : ℕ → X | ω (n + 1) ∈ B} ∩
          {ω | WithTop.some (n + 1) ≤ firstReturn A ω}).indicator 1 ω ∂pathKernel P w ∂π := by
  obtain ⟨π, hπ, hπ0, huniq⟩ := theorem_10_4_4 hrec
  exact ⟨π, hπ, hπ0, huniq, fun A hA hψA hπA B hB => theorem_10_4_9_path hrec hπ hA hψA hπA hB⟩

end MeynTweedie.Ergodicity
