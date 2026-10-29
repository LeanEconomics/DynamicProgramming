/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.HarrisDefinitions
import Mathlib.Probability.Martingale.Convergence

/-!
# Harris properties of sets (MT §9.1.1)

Meyn and Tweedie, §9.1.1, pp. 201–203.

* **Proposition 9.1.1** (`proposition_9_1_1`, p. 201): if `L(x, A) = 1` for every `x ∈ A`, then
  `Q(x, A) = L(x, A)` for every `x`, and `A` is Harris recurrent. The proof is the book's: by the
  strong Markov property `P_x(η_A ≥ k) = 1` on `A` for every `k`
  (`pathKernel_occTime_ge_succ`).
* `lintegral_pow_hitProb_le`: `∫ Pⁿ(x, dy) L(y, A) ≤ L(x, A)`, and
  `IsPetite.unifAccessible` (Lemma 5.5.1 for petite sets): for a `φ`-irreducible chain, a petite
  set `C` satisfies `C ⇝ A` for every `A` with `φ(A) > 0`.
* **Theorem 9.1.3** (p. 202), through Lévy's upward theorem
  (`MeasureTheory.Integrable.tendsto_ae_condExp`) on the path space:
  (i) `theorem_9_1_3_ae`: if `P_y(σ_A < ∞) ≥ δ > 0` on `D` (in particular if `D ⇝ A`), then
  `{Φ ∈ D i.o.} ⊆ {Φ ∈ A i.o.}`, `P_μ`-a.s. for every initial law `μ`; `theorem_9_1_3_i`: hence
  `Q(y, D) ≤ Q(y, A)`; (ii) `theorem_9_1_3_ii`: if `X ⇝ A` then `Q(x, A) = 1` for every `x`.
* **Theorem 9.1.4** (`theorem_9_1_4`, p. 203): for a Harris chain, `Q(x, B) = 1` for every
  `x ∈ X` and `B ∈ B⁺(X)`; `IsHarris.isRecurrentChain`: a Harris chain is recurrent.

The proof of Theorem 9.1.3 uses only the sets `Hₖ = {Φⱼ ∉ A for all j ≥ k}`: by the Markov
property `P_μ(Hₙ | 𝓕ₙ) = P_{Φₙ}(σ_A = ∞) ≤ 1 − δ` whenever `Φₙ ∈ D`, while
`P_μ(Hₖ | 𝓕ₙ) ≤ P_μ(Hₙ | 𝓕ₙ)` for `n ≥ k` tends to `1_{Hₖ}`. So a path in `D` infinitely often lies
in no `Hₖ`. This is the book's argument (9.7)–(9.10) with the complementary events.

**Hypotheses.** Theorem 9.1.4 uses Proposition 5.5.5, hence a countably generated σ-algebra.

**Corrections.** Theorem 9.1.3 holds under the weaker hypothesis `P_y(σ_A < ∞) ≥ δ` on `D` (the
first hitting time, time `0` included), which the topological applications of §9.2–9.3 need.
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Proposition 9.1.1 -/

omit [MeasurableSpace X] in
/-- `η_A = ∞` iff `η_A ≥ k` for every `k`. -/
theorem setOf_occTime_eq_top (A : Set X) :
    {ω : ℕ → X | occTime A ω = ∞} = ⋂ k : ℕ, {ω | (k : ℝ≥0∞) ≤ occTime A ω} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter]
  constructor
  · intro h k; rw [h]; exact le_top
  · intro h
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    calc (r : ℝ≥0∞) ≤ (⌈(r : ℝ)⌉₊ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ occTime A ω := h _

/-- **Proposition 9.1.1** (MT p. 201): if `L(x, A) = 1` for every `x ∈ A`, then
`Q(x, A) = L(x, A)` for every `x ∈ X`; in particular `A` is Harris recurrent. -/
theorem proposition_9_1_1 (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (h : ∀ x ∈ A, hitProb P A x = 1) :
    (∀ x, harrisQ P A x = hitProb P A x) ∧ IsHarrisRecurrentSet P A := by
  have := isMarkovKernel_pathKernel P
  have hT := measurableSet_firstReturn_ne_top (X := X) hA
  -- `P_x(η_A ≥ k) = 1` on `A`
  have hk : ∀ k : ℕ, ∀ x ∈ A, pathKernel P x {ω | (k : ℝ≥0∞) ≤ occTime A ω} = 1 := by
    intro k
    induction k with
    | zero => intro x _; simp
    | succ k ih =>
      intro x hx
      rw [Nat.cast_succ, pathKernel_occTime_ge_succ P hA x]
      calc ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, pathKernel P (stoppedState (firstReturn A) ω)
            {ω | (k : ℝ≥0∞) ≤ occTime A ω} ∂pathKernel P x
          = ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}, 1 ∂pathKernel P x :=
            setLIntegral_congr_fun hT fun ω hω => ih _ (stoppedState_firstReturn_mem A hω)
        _ = 1 := by rw [setLIntegral_const, one_mul]; exact h x hx
  have hQ : ∀ x ∈ A, harrisQ P A x = 1 := by
    intro x hx
    rw [harrisQ_eq_occTime, setOf_occTime_eq_top]
    refine (prob_compl_eq_zero_iff (MeasurableSet.iInter fun k : ℕ =>
      measurableSet_le_occTime hA (k : ℝ≥0∞))).1 ?_
    rw [compl_iInter]
    refine measure_iUnion_null fun k => ?_
    rw [prob_compl_eq_zero_iff (measurableSet_le_occTime hA _)]
    exact hk k x hx
  refine ⟨fun x => ?_, hQ⟩
  rw [harrisQ_eq_firstReturn P hA x]
  calc ∫⁻ ω in {ω | firstReturn A ω ≠ ⊤}, harrisQ P A (stoppedState (firstReturn A) ω)
        ∂pathKernel P x = ∫⁻ _ in {ω | firstReturn A ω ≠ ⊤}, 1 ∂pathKernel P x :=
        setLIntegral_congr_fun hT fun ω hω => hQ _ (stoppedState_firstReturn_mem A hω)
    _ = hitProb P A x := by rw [setLIntegral_const, one_mul]; rfl

/-! ### Petite sets reach every set of positive measure uniformly -/

/-- `∫ Pⁿ(x, dy) L(y, A) ≤ L(x, A)`: a visit to `A` after time `n` is a visit to `A`. -/
theorem lintegral_pow_hitProb_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (n : ℕ) (x : X) :
    ∫⁻ y, hitProb P A y ∂(P ^ n) x ≤ hitProb P A x := by
  have hT := measurableSet_firstReturn_ne_top (X := X) hA
  have hi : Measurable ({ω : ℕ → X | firstReturn A ω ≠ ⊤}.indicator (1 : (ℕ → X) → ℝ≥0∞)) :=
    measurable_one.indicator hT
  have h := markov_lintegral_univ P (Measure.dirac x) n hi
  rw [pathMeasure_dirac] at h
  simp_rw [lintegral_indicator_one hT] at h
  rw [← pathKernel_map_coord P x n, lintegral_map (measurable_hitProb P hA)
    (measurable_pi_apply n)]
  change ∫⁻ ω, pathKernel P (ω n) {ω | firstReturn A ω ≠ ⊤} ∂pathKernel P x ≤ _
  rw [← h]
  change ∫⁻ ω, (shift n ⁻¹' {ω : ℕ → X | firstReturn A ω ≠ ⊤}).indicator 1 ω ∂pathKernel P x ≤ _
  rw [lintegral_indicator_one (measurable_shift n hT)]
  refine measure_mono fun ω hω => ?_
  simp only [mem_preimage, mem_ofPred_eq, firstReturn_ne_top_iff, shift_apply] at hω ⊢
  obtain ⟨j, hj, hjA⟩ := hω
  exact ⟨n + j, by omega, hjA⟩

/-- **Petite sets are uniformly accessible to `B⁺(X)`** (Lemma 5.5.1 for petite sets): for a
`φ`-irreducible chain, if `C` is petite and `φ(A) > 0`, then `C ⇝ A`. -/
theorem IsPetite.unifAccessible {P : Kernel X X} [IsMarkovKernel P] {φ : Measure X}
    (hφ : IsPhiIrreducible P φ) {C A : Set X} (hC : IsPetite P C) (hA : MeasurableSet A)
    (hφA : 0 < φ A) : UnifAccessible P C A := by
  obtain ⟨a, ν, -, ha, hν, hle⟩ := hC
  have hL := measurable_hitProb P hA
  refine ⟨∫⁻ z, hitProb P A z ∂ν, lintegral_pos_of_pos hν hL fun z => hφ A hA hφA z,
    fun y hy => ?_⟩
  calc ∫⁻ z, hitProb P A z ∂ν ≤ ∫⁻ z, hitProb P A z ∂sampledKernel P a y :=
        lintegral_mono' (hle y hy) le_rfl
    _ = ∑' n, a n * ∫⁻ z, hitProb P A z ∂(P ^ n) y := by
        change ∫⁻ z, hitProb P A z ∂(Measure.sum fun n => a n • (P ^ n) y) = _
        rw [lintegral_sum_measure]
        simp_rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ∑' n, a n * hitProb P A y :=
        ENNReal.tsum_le_tsum fun n => by gcongr; exact lintegral_pow_hitProb_le P hA n y
    _ ≤ hitProb P A y := by
        rw [ENNReal.tsum_mul_right]
        calc (∑' n, a n) * hitProb P A y ≤ 1 * hitProb P A y := by
              gcongr
              exact le_of_eq ha
          _ = hitProb P A y := one_mul _

/-! ### Theorem 9.1.3 -/

/-- The set `Hₖ = {Φⱼ ∉ A for every j ≥ k}` of paths with no visit to `A` from time `k` on. -/
def noVisitFrom (A : Set X) (k : ℕ) : Set (ℕ → X) := {ω | ∀ j, k ≤ j → ω j ∉ A}

omit [MeasurableSpace X] in
/-- `Hₖ = θ⁻ᵏ{σ_A = ∞}`. -/
theorem noVisitFrom_eq_preimage (A : Set X) (k : ℕ) :
    noVisitFrom A k = shift k ⁻¹' {ω | firstHit A ω = ⊤} := by
  ext ω
  simp only [noVisitFrom, mem_ofPred_eq, mem_preimage, firstHit, hittingAfter_eq_top_iff,
    shift_apply, zero_le, true_imp_iff]
  constructor
  · intro h j; exact h (k + j) (by omega)
  · intro h j hj; have := h (j - k); rwa [show k + (j - k) = j by omega] at this

/-- `Hₖ` is an event. -/
theorem measurableSet_noVisitFrom {A : Set X} (hA : MeasurableSet A) (k : ℕ) :
    MeasurableSet (noVisitFrom A k) := by
  have h : {ω : ℕ → X | firstHit A ω = ⊤} = {ω | firstHit A ω ≠ ⊤}ᶜ := by ext; simp
  rw [noVisitFrom_eq_preimage, h]
  exact measurable_shift k (measurableSet_ne_top (proposition_3_4_4 hA).2).compl

omit [MeasurableSpace X] in
/-- `Hₖ ⊆ Hₙ` for `k ≤ n`. -/
theorem noVisitFrom_mono (A : Set X) {k n : ℕ} (hkn : k ≤ n) :
    noVisitFrom A k ⊆ noVisitFrom A n := fun _ hω j hj => hω j (by omega)

omit [MeasurableSpace X] in
/-- A path not in `A` infinitely often lies in some `Hₖ`. -/
theorem exists_noVisitFrom_of_notMem_ioSet (A : Set X) {ω : ℕ → X} (h : ω ∉ ioSet A) :
    ∃ k, ω ∈ noVisitFrom A k := by
  simp only [ioSet, mem_ofPred_eq, not_forall, not_exists, not_and] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk⟩

/-- **Theorem 9.1.3 (i)**, path form (MT p. 202): if `P_y(σ_A < ∞) ≥ δ > 0` for every `y ∈ D`
(in particular if `D ⇝ A`), then `{Φ ∈ D i.o.} ⊆ {Φ ∈ A i.o.}` almost surely, for every initial
distribution. -/
theorem theorem_9_1_3_ae (P : Kernel X X) [IsMarkovKernel P] (μ : Measure X)
    [IsProbabilityMeasure μ] {A D : Set X} (hA : MeasurableSet A) {δ : ℝ≥0∞} (hδ : 0 < δ)
    (hD : ∀ y ∈ D, δ ≤ hitProbZero P A y) :
    ∀ᵐ ω ∂pathMeasure P μ, ω ∈ ioSet D → ω ∈ ioSet A := by
  have := isMarkovKernel_pathKernel P
  have := isProbabilityMeasure_pathMeasure P μ
  set Pμ := pathMeasure P μ
  set N : Set (ℕ → X) := {ω | firstHit A ω = ⊤}
  have hN : MeasurableSet N := by
    have h : N = {ω | firstHit A ω ≠ ⊤}ᶜ := by ext; simp [N]
    rw [h]; exact (measurableSet_ne_top (proposition_3_4_4 hA).2).compl
  set g : ℕ → (ℕ → X) → ℝ := fun k => (noVisitFrom A k).indicator 1
  have hgm : ∀ k, Measurable (g k) := fun k =>
    measurable_one.indicator (measurableSet_noVisitFrom hA k)
  have hgi : ∀ k, Integrable (g k) Pμ := fun k =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_noVisitFrom hA k)
  -- Lévy's upward theorem for each `g k`
  have hlevy : ∀ k, ∀ᵐ ω ∂Pμ, Tendsto (fun n => (Pμ[g k | natFilt n]) ω) atTop (𝓝 (g k ω)) :=
    fun k => (hgi k).tendsto_ae_condExp
      ((hgm k).stronglyMeasurable.mono (iSup_natFilt (X := X)).ge)
  -- monotonicity of conditional expectations
  have hmono : ∀ k n, k ≤ n → Pμ[g k | natFilt n] ≤ᵐ[Pμ] Pμ[g n | natFilt n] := fun k n hkn =>
    condExp_mono (hgi k) (hgi n) (Eventually.of_forall fun ω => indicator_le_indicator_of_subset
      (noVisitFrom_mono A hkn) (fun _ => zero_le_one) ω)
  -- the Markov property: `P(Hₙ | 𝓕ₙ) = P_{Φₙ}(σ_A = ∞)`
  have hH : Measurable (N.indicator (1 : (ℕ → X) → ℝ)) := measurable_one.indicator hN
  have hmarkov : ∀ n, Pμ[g n | natFilt n] =ᵐ[Pμ] fun ω => (pathKernel P (ω n) N).toReal := by
    intro n
    have hg : g n = fun ω => N.indicator (1 : (ℕ → X) → ℝ) (shift n ω) := by
      funext ω
      simp only [g, noVisitFrom_eq_preimage]
      rfl
    have hint : Integrable (fun ω => N.indicator (1 : (ℕ → X) → ℝ) (shift n ω)) Pμ := by
      rw [← hg]; exact hgi n
    rw [hg]
    refine (markov_property P μ n hH hint).trans (Eventually.of_forall fun ω => ?_)
    simp only
    rw [integral_indicator_one hN]
    rfl
  -- the bound `P_y(σ_A = ∞) ≤ 1 − δ` on `D`
  set c : ℝ := (1 - δ).toReal with hc
  have hc1 : c < 1 := by
    rw [hc]
    rcases le_or_gt 1 δ with h1 | h1
    · rw [tsub_eq_zero_of_le h1]; simp
    · rw [ENNReal.toReal_sub_of_le h1.le ENNReal.one_ne_top, ENNReal.toReal_one]
      have : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' (h1.trans ENNReal.one_lt_top).ne
      linarith
  have hbound : ∀ y ∈ D, (pathKernel P y N).toReal ≤ c := by
    intro y hy
    have heq : pathKernel P y N = 1 - hitProbZero P A y := by
      rw [show N = {ω | firstHit A ω ≠ ⊤}ᶜ from by ext; simp [N],
        prob_compl_eq_one_sub (measurableSet_ne_top (proposition_3_4_4 hA).2)]
      rfl
    rw [heq]
    exact ENNReal.toReal_mono (by simp) (tsub_le_tsub_left (hD y hy) 1)
  -- combine the countably many almost sure statements
  have hall_levy := ae_all_iff.2 hlevy
  have hall_mono : ∀ᵐ ω ∂Pμ, ∀ k n, k ≤ n →
      (Pμ[g k | natFilt n]) ω ≤ (Pμ[g n | natFilt n]) ω := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun n => ?_
    by_cases hkn : k ≤ n
    · filter_upwards [hmono k n hkn] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hkn
  have hall_markov := ae_all_iff.2 hmarkov
  filter_upwards [hall_levy, hall_mono, hall_markov] with ω hlev hmon hmar hDio
  by_contra hAio
  obtain ⟨k, hk⟩ := exists_noVisitFrom_of_notMem_ioSet A hAio
  have hgk : g k ω = 1 := by simp [g, hk]
  have hlim := hlev k
  rw [hgk] at hlim
  -- eventually `P(Hₖ | 𝓕ₙ)(ω) > c`
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds hc1))
  obtain ⟨n, hn, hnD⟩ := hDio (max M k)
  have h1 := hM n (le_of_max_le_left hn)
  have h2 := hmon k n (le_of_max_le_right hn)
  rw [hmar n] at h2
  exact absurd (h1.trans_le (h2.trans (hbound _ hnD))) (lt_irrefl c)

/-- **Theorem 9.1.3 (i)** (MT p. 202): if `D ⇝ A`, then `Q(y, D) ≤ Q(y, A)` for every `y`. The
hypothesis is the weaker `P_y(σ_A < ∞) ≥ δ > 0` on `D`. -/
theorem theorem_9_1_3_i (P : Kernel X X) [IsMarkovKernel P] {A D : Set X}
    (hA : MeasurableSet A) {δ : ℝ≥0∞} (hδ : 0 < δ) (hD : ∀ y ∈ D, δ ≤ hitProbZero P A y)
    (y : X) : harrisQ P D y ≤ harrisQ P A y := by
  have h := theorem_9_1_3_ae P (Measure.dirac y) hA hδ hD
  rw [pathMeasure_dirac] at h
  exact measure_mono_ae h

/-- `L(x, A) ≤ P_x(σ_A < ∞)`. -/
theorem hitProb_le_hitProbZero (P : Kernel X X) [IsMarkovKernel P] (A : Set X) (x : X) :
    hitProb P A x ≤ hitProbZero P A x := by
  refine measure_mono fun ω hω => ?_
  simp only [mem_ofPred_eq, firstReturn_ne_top_iff] at hω ⊢
  obtain ⟨n, -, hn⟩ := hω
  rw [firstHit, ne_eq, hittingAfter_eq_top_iff]
  push Not
  exact ⟨n, zero_le, hn⟩

/-- **Theorem 9.1.3 (i)** with the book's hypothesis `D ⇝ A`. -/
theorem theorem_9_1_3_i_unifAccessible (P : Kernel X X) [IsMarkovKernel P] {A D : Set X}
    (hA : MeasurableSet A) (hDA : UnifAccessible P D A) (y : X) :
    harrisQ P D y ≤ harrisQ P A y := by
  obtain ⟨δ, hδ, h⟩ := hDA
  exact theorem_9_1_3_i P hA hδ (fun z hz => (h z hz).trans (hitProb_le_hitProbZero P A z)) y

/-- **Theorem 9.1.3 (ii)** (MT p. 202): if `X ⇝ A` (here: `P_x(σ_A < ∞) ≥ δ > 0` for every
`x`), then `Q(x, A) = 1` for every `x`; in particular `A` is Harris recurrent. -/
theorem theorem_9_1_3_ii (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {δ : ℝ≥0∞} (hδ : 0 < δ) (h : ∀ y, δ ≤ hitProbZero P A y) (x : X) :
    harrisQ P A x = 1 := by
  have := isMarkovKernel_pathKernel P
  have h1 := theorem_9_1_3_i P (D := univ) hA hδ (fun y _ => h y) x
  have hu : harrisQ P univ x = 1 := by
    have : ioSet (univ : Set X) = univ := by
      ext ω; simp only [ioSet, mem_univ, and_true, mem_ofPred_eq, iff_true]
      exact fun N => ⟨N, le_rfl⟩
    rw [harrisQ, this, measure_univ]
  exact le_antisymm (harrisQ_le_one P A x) (hu ▸ h1)

/-! ### Theorem 9.1.4 -/

variable [MeasurableSpace.CountablyGenerated X] in
/-- **Theorem 9.1.4** (MT p. 203): if the chain is Harris recurrent, then `Q(x, B) = 1` for every
`x ∈ X` and every `B ∈ B⁺(X)`. -/
theorem theorem_9_1_4 {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X} (hH : IsHarris P ψ)
    {B : Set X} (hB : MeasurableSet B) (hψB : 0 < ψ B) (x : X) : harrisQ P B x = 1 := by
  obtain ⟨hψ, hHar⟩ := hH
  obtain ⟨c, ψc, -, Cs, hmono, hpet, hcov⟩ := proposition_5_5_5_iii_cover P hψ
  have hψu : 0 < ψ (⋃ n, Cs n) := by
    rw [hcov]; exact pos_iff_ne_zero.2 fun h => hψ.1 (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨N, hN⟩ := exists_measure_pos_of_iUnion hψu
  obtain ⟨m, hm⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ n, Cs n)
  set n := max m N
  have hxn : x ∈ Cs n := hmono (le_max_left m N) hm
  have hψn : 0 < ψ (Cs n) := hN.trans_le (measure_mono (hmono (le_max_right m N)))
  have hCm : MeasurableSet (Cs n) := (hpet n).1
  have hQ := hHar (Cs n) hCm hψn x hxn
  have hacc := IsPetite.unifAccessible hψ.2.1 ⟨_, _, hpet n⟩ hB hψB
  exact le_antisymm (harrisQ_le_one P B x)
    (hQ ▸ theorem_9_1_3_i_unifAccessible P hB hacc x)

variable [MeasurableSpace.CountablyGenerated X] in
/-- A Harris chain is recurrent: `Q(x, A) = 1` gives `U(x, A) = ∞` for every `x` and
`A ∈ B⁺(X)` (MT p. 200). -/
theorem IsHarris.isRecurrentChain {P : Kernel X X} [IsMarkovKernel P] {ψ : Measure X}
    (hH : IsHarris P ψ) : IsRecurrentChain P ψ :=
  ⟨hH.1, fun A hA hψA x => potKernel_eq_top_of_harrisQ_pos P hA
    (by rw [theorem_9_1_4 hH hA hψA x]; exact one_pos)⟩

end MeynTweedie.GeometricErgodicity
