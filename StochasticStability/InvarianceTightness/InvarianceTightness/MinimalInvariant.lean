/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InvarianceTightness.Invariance

/-!
# Minimal subinvariant measures (MT §10.4.2)

Meyn and Tweedie, §10.4.2, pp. 243–245. No irreducibility is assumed in this module. For a
measurable `A` and a measure `ρ`, the measures `ρ_APⁿ⁺¹ = ρ (P I_{Aᶜ})ⁿ P` are
`tabooSeq P hA ρ n`; they satisfy `ρ_APⁿ⁺² = (ρ_APⁿ⁺¹ restricted to Aᶜ) P` (`tabooSeq_succ`), and
their sum is `ρU_A` (`tabooPotKernel_comp`).

**The basic identities** (the computations (10.11), (10.30)).
* `tabooPotKernel_comp_eq`: `ρU_A = ρP + Σₙ ρ_APⁿ⁺²`;
* `comp_tabooPotKernel_comp`: `(ρU_A)P = (ρU_A restricted to A)P + Σₙ ρ_APⁿ⁺²`.

**The minimal measure.** For a measure `μ`, `minimalMeasure P hA μ = μ°_A` (10.27) is
`μ°_A(B) = ∫_A μ(dy) U_A(y, B)` (`minimalMeasure_apply`), and `minimalMeasure_self`:
`μ°_A(A) = ∫_A μ(dy) L(y, A)`.

**Results.**
* **Proposition 10.4.6** (p. 243): for a subinvariant `μ`, `proposition_10_4_6_minimal`
  (`μ°_A ≤ μ`) and `proposition_10_4_6` (`μ°_A` is subinvariant).
* **Theorem 10.4.7** (p. 244): if `μ(A) < ∞` and `L(x, A) = 1` for `μ`-almost every `x ∈ A`, then
  (i) `theorem_10_4_7_i`, `μ°_A = μ` on subsets of `A`, (10.28)–(10.29); (ii) `theorem_10_4_7_ii`,
  `μ°_A` is invariant and `μ°_A(Āᶜ) = 0`, where `Āᶜ = {x : L(x, A) = 0}` (`noHitSet`).
* **Proposition 10.4.8** (`proposition_10_4_8`, p. 245): if `∫_A ν(dx) U_A(x, B) = ν(B)` for
  `B ⊆ A`, then `ν° = ∫_A ν(dx) U_A(x, ·)` is invariant.
* `eq_of_le_of_lintegral_le`: the uniqueness device used for Theorem 10.2.1 (ii): if `μ₀ ≤ μ`
  and `∫ f dμ ≤ ∫ f dμ₀ < ∞` for some `f` with `0 < f < ∞`, then `μ = μ₀`.

**Corrections.**
* Theorem 10.4.7 (i) is proved for measurable `B ⊆ A` by the book's computation (10.28), which
  needs only `μ(A) < ∞`; the book's final contradiction argument (with the resolvent) is not
  needed.
* In Theorem 10.4.7 (ii) the book says `μ°_A(Āᶜ) = 0` "follows by definition". It does not
  follow from the definition alone: the proof here shows that the masses
  `bₙ = μ_APⁿ⁺¹(Aᶜ)` tend to `0` (because `μ°_A(A) = μ(A)`) while `μ_APⁿ⁺¹(Āᶜ ∩ Aᶜ)` is
  nondecreasing in `n` (from `Āᶜ` the chain moves into `Āᶜ ∩ Aᶜ` with probability one).
* Proposition 10.4.8 needs neither that `ν` is a probability nor that it is supported on `A`.
-/

namespace MeynTweedie.InvarianceTightness

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

/-! ### Composition lemmas -/

/-- `I_B ∘ₘ m` is `m` restricted to `B`. -/
theorem indKernel_comp_eq_restrict {B : Set X} (hB : MeasurableSet B) (m : Measure X) :
    indKernel hB ∘ₘ m = m.restrict B := by
  ext C hC
  rw [measure_kernel_apply m _ hC, Measure.restrict_apply hC]
  simp_rw [indKernel_apply hB _ hC]
  exact lintegral_indicator_one (hC.inter hB)

/-- `(Σₙ κₙ) ∘ₘ ρ = Σₙ κₙ ∘ₘ ρ`. -/
theorem kernelSum_comp (κ : ℕ → Kernel X X) (ρ : Measure X) :
    Kernel.sum κ ∘ₘ ρ = Measure.sum fun n => κ n ∘ₘ ρ := by
  ext B hB
  rw [measure_kernel_apply ρ _ hB, Measure.sum_apply _ hB]
  simp_rw [Kernel.sum_apply' _ _ hB]
  rw [lintegral_tsum fun n => (Kernel.measurable_coe _ hB).aemeasurable]
  exact tsum_congr fun n => (measure_kernel_apply ρ _ hB).symm

/-- `K ∘ₘ (Σₙ mₙ) = Σₙ K ∘ₘ mₙ`. -/
theorem comp_measureSum (K : Kernel X X) (m : ℕ → Measure X) :
    K ∘ₘ Measure.sum m = Measure.sum fun n => K ∘ₘ m n := by
  ext B hB
  rw [measure_kernel_apply _ _ hB, lintegral_sum_measure, Measure.sum_apply _ hB]
  exact tsum_congr fun n => (measure_kernel_apply _ _ hB).symm

/-- `K ∘ₘ (Σ_{n < N} mₙ)|_B = Σ_{n < N} K ∘ₘ mₙ|_B`. -/
theorem comp_restrict_finsetSum (K : Kernel X X) (m : ℕ → Measure X) (B : Set X) (N : ℕ) :
    K ∘ₘ (∑ n ∈ Finset.range N, m n).restrict B =
      ∑ n ∈ Finset.range N, K ∘ₘ (m n).restrict B := by
  induction N with
  | zero => simp [Measure.bind_zero_left]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Measure.restrict_add, Measure.comp_add, ih]

/-- `(P I_{Aᶜ})ⁿ⁺¹ P = P I_{Aᶜ} [(P I_{Aᶜ})ⁿ P]`, read as "first `(P I_{Aᶜ})ⁿ P`, then kill outside
`Aᶜ`, then `P`". -/
theorem tabooKernel_succ_eq (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (n : ℕ) :
    tabooKernel P hA (n + 1) = P ∘ₖ (indKernel hA.compl ∘ₖ tabooKernel P hA n) := by
  unfold tabooKernel
  rw [pow_add_eq _ n 1, pow_one]
  simp only [Kernel.comp_assoc]

/-! ### The taboo sequence of a measure -/

/-- The measures `ρ_APⁿ⁺¹ = ρ (P I_{Aᶜ})ⁿ P` (MT p. 243). -/
noncomputable def tabooSeq (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (ρ : Measure X)
    (n : ℕ) : Measure X :=
  tabooKernel P hA n ∘ₘ ρ

/-- `ρ_AP¹ = ρP`. -/
theorem tabooSeq_zero (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (ρ : Measure X) :
    tabooSeq P hA ρ 0 = P ∘ₘ ρ := by
  rw [tabooSeq, tabooKernel_zero]

/-- `ρ_APⁿ⁺² = (ρ_APⁿ⁺¹ restricted to Aᶜ) P`. -/
theorem tabooSeq_succ (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) (ρ : Measure X)
    (n : ℕ) : tabooSeq P hA ρ (n + 1) = P ∘ₘ (tabooSeq P hA ρ n).restrict Aᶜ := by
  rw [tabooSeq, tabooKernel_succ_eq, ← Measure.comp_assoc, ← Measure.comp_assoc,
    indKernel_comp_eq_restrict]
  rfl

/-- `ρU_A = Σₙ ρ_APⁿ⁺¹`. -/
theorem tabooPotKernel_comp (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (ρ : Measure X) : tabooPotKernel P hA ∘ₘ ρ = Measure.sum (tabooSeq P hA ρ) :=
  kernelSum_comp _ ρ

/-- `ρU_A = ρP + Σₙ ρ_APⁿ⁺²`. -/
theorem tabooPotKernel_comp_eq (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (ρ : Measure X) :
    tabooPotKernel P hA ∘ₘ ρ = P ∘ₘ ρ + Measure.sum fun n => tabooSeq P hA ρ (n + 1) := by
  rw [tabooPotKernel_comp]
  ext B hB
  rw [Measure.sum_apply _ hB, Measure.add_apply, Measure.sum_apply _ hB,
    tsum_eq_zero_add' ENNReal.summable, tabooSeq_zero]

/-- The identity behind (10.11) and (10.30):
`(ρU_A)P = (ρU_A restricted to A)P + Σₙ ρ_APⁿ⁺²`. -/
theorem comp_tabooPotKernel_comp (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (ρ : Measure X) :
    P ∘ₘ (tabooPotKernel P hA ∘ₘ ρ) = P ∘ₘ (tabooPotKernel P hA ∘ₘ ρ).restrict A +
      Measure.sum fun n => tabooSeq P hA ρ (n + 1) := by
  rw [tabooPotKernel_comp, comp_measureSum, Measure.restrict_sum _ hA, comp_measureSum,
    Measure.sum_add_sum]
  congr 1
  funext n
  rw [tabooSeq_succ, ← Measure.comp_add, Measure.restrict_add_restrict_compl hA]

/-! ### The minimal measure `μ°_A` -/

/-- The measure `μ°_A(B) = ∫_A μ(dy) U_A(y, B)` (10.27), MT p. 243. -/
noncomputable def minimalMeasure (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (μ : Measure X) : Measure X :=
  tabooPotKernel P hA ∘ₘ μ.restrict A

/-- (10.27): `μ°_A(B) = ∫_A μ(dy) U_A(y, B)`. -/
theorem minimalMeasure_apply (P : Kernel X X) {A : Set X} (hA : MeasurableSet A)
    (μ : Measure X) {B : Set X} (hB : MeasurableSet B) :
    minimalMeasure P hA μ B = ∫⁻ y in A, tabooPotKernel P hA y B ∂μ :=
  measure_kernel_apply _ _ hB

/-- `μ°_A(A) = ∫_A μ(dy) L(y, A)`. -/
theorem minimalMeasure_self (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) :
    minimalMeasure P hA μ A = ∫⁻ y in A, hitProb P A y ∂μ := by
  rw [minimalMeasure_apply P hA μ hA]
  simp_rw [tabooPotKernel_self P hA]

/-- `μ°_A(A) ≤ μ(A)`, since `L ≤ 1`. -/
theorem minimalMeasure_self_le (P : Kernel X X) [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) (μ : Measure X) : minimalMeasure P hA μ A ≤ μ A := by
  rw [minimalMeasure_self P hA μ]
  calc ∫⁻ y in A, hitProb P A y ∂μ ≤ ∫⁻ _ in A, 1 ∂μ :=
        lintegral_mono fun y => hitProb_le_one P A y
    _ = μ A := by rw [setLIntegral_const, one_mul]

/-- **Proposition 10.4.6**, minimality (MT p. 243): if `μ` is subinvariant, then
`μ ≥ μ°_A`. -/
theorem proposition_10_4_6_minimal {P : Kernel X X} {μ : Measure X} (h : IsSubinvariant P μ)
    {A : Set X} (hA : MeasurableSet A) : minimalMeasure P hA μ ≤ μ := by
  set m := tabooSeq P hA (μ.restrict A)
  have hN : ∀ N, ∑ n ∈ Finset.range N, m n ≤ μ := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact Measure.zero_le μ
    | succ N ih =>
      rw [Finset.sum_range_succ']
      have e : ∑ n ∈ Finset.range N, m (n + 1) =
          P ∘ₘ (∑ n ∈ Finset.range N, m n).restrict Aᶜ := by
        rw [comp_restrict_finsetSum]
        exact Finset.sum_congr rfl fun n _ => tabooSeq_succ P hA _ n
      rw [e, show m 0 = P ∘ₘ μ.restrict A from tabooSeq_zero P hA _]
      calc P ∘ₘ (∑ n ∈ Finset.range N, m n).restrict Aᶜ + P ∘ₘ μ.restrict A
          ≤ P ∘ₘ μ.restrict Aᶜ + P ∘ₘ μ.restrict A :=
            add_le_add_left (comp_le_comp P (Measure.restrict_mono subset_rfl ih)) _
        _ = P ∘ₘ μ := by
            rw [← Measure.comp_add, add_comm, Measure.restrict_add_restrict_compl hA]
        _ ≤ μ := h
  refine Measure.le_intro fun B hB _ => ?_
  rw [minimalMeasure, tabooPotKernel_comp, Measure.sum_apply _ hB, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← Measure.finsetSum_apply]
  exact hN N B

/-- **Proposition 10.4.6**, subinvariance (MT p. 243): if `μ` is subinvariant, so is `μ°_A`. -/
theorem proposition_10_4_6 {P : Kernel X X} {μ : Measure X} (h : IsSubinvariant P μ)
    {A : Set X} (hA : MeasurableSet A) : IsSubinvariant P (minimalMeasure P hA μ) := by
  unfold IsSubinvariant minimalMeasure
  rw [comp_tabooPotKernel_comp P hA]
  conv_rhs => rw [tabooPotKernel_comp_eq P hA (μ.restrict A)]
  exact add_le_add_left (comp_le_comp P
    (Measure.restrict_mono subset_rfl (proposition_10_4_6_minimal h hA))) _

/-! ### Theorem 10.4.7 -/

/-- `a ≤ c`, `b ≤ d`, `c + d = a + b ≠ ∞` force `a = c`. -/
theorem eq_of_add_eq_of_le {a b c d : ℝ≥0∞} (hac : a ≤ c) (hbd : b ≤ d)
    (hsum : c + d = a + b) (hd : d ≠ ∞) : a = c := by
  refine le_antisymm hac ((ENNReal.add_le_add_iff_right hd).1 ?_)
  calc c + d = a + b := hsum
    _ ≤ a + d := add_le_add_right hbd _

/-- Under the hypotheses of Theorem 10.4.7, `μ°_A(A) = μ(A)`. -/
theorem minimalMeasure_self_eq {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    {A : Set X} (hA : MeasurableSet A)
    (hL : ∀ᵐ x ∂μ.restrict A, hitProb P A x = 1) : minimalMeasure P hA μ A = μ A := by
  rw [minimalMeasure_self P hA μ, lintegral_congr_ae (hL.mono fun x hx => by rw [hx]),
    lintegral_one, Measure.restrict_apply_univ]

/-- **Theorem 10.4.7 (i)** (MT p. 244), (10.28)–(10.29): if `μ` is subinvariant, `μ(A) < ∞` and
`L(x, A) = 1` for `μ`-almost every `x ∈ A`, then `μ°_A(B) = μ(B)` for every measurable `B ⊆ A`;
that is, `μ°_A` and `μ` agree on `A`. -/
theorem theorem_10_4_7_i {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    (h : IsSubinvariant P μ) {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (hL : ∀ᵐ x ∂μ.restrict A, hitProb P A x = 1) :
    (minimalMeasure P hA μ).restrict A = μ.restrict A := by
  have hmin := proposition_10_4_6_minimal h hA
  ext C hC
  rw [Measure.restrict_apply hC, Measure.restrict_apply hC]
  have hB : MeasurableSet (C ∩ A) := hC.inter hA
  have hsplit : ∀ ν : Measure X, ν (A ∩ (C ∩ A)) + ν (A \ (C ∩ A)) = ν A :=
    fun ν => measure_inter_add_sdiff A hB
  have hAB : A ∩ (C ∩ A) = C ∩ A := by
    ext x; simp only [mem_inter_iff]; tauto
  have h1 := hsplit μ
  have h2 := hsplit (minimalMeasure P hA μ)
  rw [hAB] at h1 h2
  refine eq_of_add_eq_of_le (hmin (C ∩ A)) (hmin (A \ (C ∩ A))) ?_
    (ne_top_of_le_ne_top hμA (measure_mono (s := A \ (C ∩ A)) sdiff_subset))
  rw [h1, h2, minimalMeasure_self_eq hA hL]

/-- For `y` with `L(y, A) = 0`, the chain moves into `{L(·, A) = 0} ∩ Aᶜ` with probability one. -/
theorem prob_noHitSet_inter_compl {P : Kernel X X} [IsMarkovKernel P] {A : Set X}
    (hA : MeasurableSet A) {y : X} (hy : hitProb P A y = 0) :
    P y (noHitSet P A ∩ Aᶜ) = 1 := by
  have hN : MeasurableSet (noHitSet P A) :=
    measurable_hitProb P hA (measurableSet_singleton 0)
  rw [hitProb_first_step P hA y, add_eq_zero] at hy
  obtain ⟨h1, h2⟩ := hy
  rw [setLIntegral_eq_zero_iff hA.compl (measurable_hitProb P hA)] at h2
  have h3 : P y ((noHitSet P A)ᶜ ∩ Aᶜ) = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 h2)
    simp only [mem_inter_iff, mem_compl_iff, noHitSet, mem_ofPred_eq] at hx
    simp only [mem_ofPred_eq, mem_compl_iff, not_imp]
    exact ⟨hx.2, hx.1⟩
  have hc : (noHitSet P A ∩ Aᶜ)ᶜ ⊆ A ∪ ((noHitSet P A)ᶜ ∩ Aᶜ) := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · refine Or.inr ⟨fun hxN => hx ⟨hxN, hxA⟩, hxA⟩
  have h4 : P y (noHitSet P A ∩ Aᶜ)ᶜ = 0 :=
    measure_mono_null hc (measure_union_null h1 h3)
  rw [prob_compl_eq_zero_iff (hN.inter hA.compl)] at h4
  exact h4

/-- **Theorem 10.4.7 (ii)** (MT p. 244), (10.30): if `μ` is subinvariant, `μ(A) < ∞` and
`L(x, A) = 1` for `μ`-almost every `x ∈ A`, then `μ°_A` is invariant and
`μ°_A(Āᶜ) = μ°_A{x : L(x, A) = 0} = 0`. -/
theorem theorem_10_4_7_ii {P : Kernel X X} [IsMarkovKernel P] {μ : Measure X}
    (h : IsSubinvariant P μ) {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (hL : ∀ᵐ x ∂μ.restrict A, hitProb P A x = 1) :
    IsInvariant P (minimalMeasure P hA μ) ∧ minimalMeasure P hA μ (noHitSet P A) = 0 := by
  have hi := theorem_10_4_7_i h hA hμA hL
  have hrA : (μ.restrict A).restrict A = μ.restrict A := by
    rw [Measure.restrict_restrict hA, inter_self]
  refine ⟨?_, ?_⟩
  · unfold IsInvariant
    have e1 := comp_tabooPotKernel_comp P hA (μ.restrict A)
    have e2 := tabooPotKernel_comp_eq P hA (μ.restrict A)
    unfold minimalMeasure at hi ⊢
    rw [e1, hi, e2]
  -- the mass argument
  set m := tabooSeq P hA (μ.restrict A) with hm
  have hN : MeasurableSet (noHitSet P A) :=
    measurable_hitProb P hA (measurableSet_singleton 0)
  set a : ℕ → ℝ≥0∞ := fun n => m n A with ha
  set b : ℕ → ℝ≥0∞ := fun n => m n Aᶜ with hb
  have hmass : ∀ n, m (n + 1) univ = b n := fun n => by
    rw [hm, tabooSeq_succ, comp_apply_univ, Measure.restrict_apply_univ]
  have hsplit : ∀ n, a n + b n = m n univ := fun n => measure_add_measure_compl hA
  have hsumA : ∑' n, a n = μ A := by
    have := minimalMeasure_self_eq hA hL
    rwa [minimalMeasure, tabooPotKernel_comp, Measure.sum_apply _ hA] at this
  have hm0 : m 0 univ = μ A := by
    rw [hm, tabooSeq_zero, comp_apply_univ, Measure.restrict_apply_univ]
  have hafin : ∀ n, a n ≠ ∞ := fun n =>
    ne_top_of_le_ne_top hμA (hsumA ▸ ENNReal.le_tsum n)
  have hsum1 : ∑' n, a (n + 1) = b 0 := by
    have h1 : a 0 + ∑' n, a (n + 1) = a 0 + b 0 := by
      rw [← tsum_eq_zero_add' ENNReal.summable, hsumA, hsplit 0, hm0]
    exact (ENNReal.add_right_inj (hafin 0)).1 h1
  -- `bₙ` is the tail `Σ_{k > n} a_k`
  have htail : ∀ n, b n = ∑' k, a (k + (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using hsum1.symm
    | succ n ih =>
      have e1 : a (n + 1) + b (n + 1) = b n := by rw [hsplit, hmass]
      have e2 : ∑' k, a (k + (n + 1)) = a (n + 1) + ∑' k, a (k + (n + 1 + 1)) := by
        rw [tsum_eq_zero_add' ENNReal.summable, zero_add]
        congr 1
        exact tsum_congr fun k => by congr 1; omega
      rw [ih, e2] at e1
      exact (ENNReal.add_right_inj (hafin (n + 1))).1 e1
  have hlim : Tendsto b atTop (𝓝 0) := by
    have := (ENNReal.tendsto_sum_nat_add a (hsumA ▸ hμA)).comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact (htail n).symm
  -- `cₙ = μ_APⁿ⁺¹(Āᶜ ∩ Aᶜ)` is nondecreasing and bounded by `bₙ`
  set c : ℕ → ℝ≥0∞ := fun n => m n (noHitSet P A ∩ Aᶜ) with hc
  have hcb : ∀ n, c n ≤ b n := fun n => measure_mono inter_subset_right
  have hcmono : Monotone c := by
    refine monotone_nat_of_le_succ fun n => ?_
    simp only [hc]
    rw [hm, tabooSeq_succ, measure_kernel_apply _ _ (hN.inter hA.compl)]
    calc tabooSeq P hA (μ.restrict A) n (noHitSet P A ∩ Aᶜ)
        = ∫⁻ _ in noHitSet P A, 1 ∂(tabooSeq P hA (μ.restrict A) n).restrict Aᶜ := by
          rw [setLIntegral_const, one_mul, Measure.restrict_apply hN]
      _ = ∫⁻ y in noHitSet P A, P y (noHitSet P A ∩ Aᶜ)
            ∂(tabooSeq P hA (μ.restrict A) n).restrict Aᶜ :=
          setLIntegral_congr_fun hN fun y hy => (prob_noHitSet_inter_compl hA hy).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hc0 : ∀ n, c n = 0 := by
    intro n
    refine le_antisymm (ge_of_tendsto hlim (eventually_atTop.2 ⟨n, fun k hk => ?_⟩)) zero_le
    exact (hcmono hk).trans (hcb k)
  -- assemble
  have hA' : minimalMeasure P hA μ (noHitSet P A ∩ A) = 0 := by
    have := congrArg (fun ν : Measure X => ν (noHitSet P A)) hi
    simp only [Measure.restrict_apply hN] at this
    rw [this]
    rw [← Measure.restrict_apply hN]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hL)
    simp only [noHitSet, mem_ofPred_eq] at hx
    simp [hx]
  have hAc : minimalMeasure P hA μ (noHitSet P A ∩ Aᶜ) = 0 := by
    rw [minimalMeasure, tabooPotKernel_comp, Measure.sum_apply _ (hN.inter hA.compl)]
    exact ENNReal.tsum_eq_zero.2 hc0
  rw [← measure_inter_add_sdiff (noHitSet P A) hA, hA', zero_add, sdiff_eq, hAc]

/-! ### Proposition 10.4.8 -/

/-- **Proposition 10.4.8** (MT p. 245): if `∫_A ν(dx) U_A(x, B) = ν(B)` for every measurable
`B ⊆ A` (`ν` is invariant for the process on `A`), then `ν°(B) = ∫_A ν(dx) U_A(x, B)` is
invariant for `Φ`. -/
theorem proposition_10_4_8 (P : Kernel X X) {A : Set X} (hA : MeasurableSet A) {ν : Measure X}
    (hν : ∀ B, MeasurableSet B → B ⊆ A → ∫⁻ x in A, tabooPotKernel P hA x B ∂ν = ν B) :
    IsInvariant P (minimalMeasure P hA ν) := by
  have hr : (minimalMeasure P hA ν).restrict A = ν.restrict A := by
    ext C hC
    rw [Measure.restrict_apply hC, Measure.restrict_apply hC, minimalMeasure_apply P hA ν
      (hC.inter hA)]
    exact hν _ (hC.inter hA) inter_subset_right
  unfold IsInvariant
  have e1 := comp_tabooPotKernel_comp P hA (ν.restrict A)
  have e2 := tabooPotKernel_comp_eq P hA (ν.restrict A)
  unfold minimalMeasure at hr ⊢
  rw [e1, hr, e2]

/-! ### A uniqueness device -/

/-- If `μ₀ ≤ μ` and `∫ f dμ ≤ ∫ f dμ₀ < ∞` for a measurable `f` with `0 < f < ∞` everywhere,
then `μ = μ₀`. (In the proof of Theorem 10.2.1 (ii), `f = K_{a_{1/2}}(·, α)`.) -/
theorem eq_of_le_of_lintegral_le {μ₀ μ : Measure X} (hle : μ₀ ≤ μ) {f : X → ℝ≥0∞}
    (hf : Measurable f) (hpos : ∀ x, f x ≠ 0) (hfin : ∀ x, f x ≠ ∞)
    (hint : ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂μ₀) (hint' : ∫⁻ x, f x ∂μ₀ ≠ ∞) : μ = μ₀ := by
  have hd : μ.withDensity f = μ₀.withDensity f := by
    ext B hB
    rw [withDensity_apply _ hB, withDensity_apply _ hB]
    have h1 : ∫⁻ x in B, f x ∂μ₀ ≤ ∫⁻ x in B, f x ∂μ :=
      lintegral_mono' (Measure.restrict_mono subset_rfl hle) le_rfl
    have h2 : ∫⁻ x in Bᶜ, f x ∂μ₀ ≤ ∫⁻ x in Bᶜ, f x ∂μ :=
      lintegral_mono' (Measure.restrict_mono subset_rfl hle) le_rfl
    have hc : ∫⁻ x in Bᶜ, f x ∂μ₀ ≠ ∞ :=
      ne_top_of_le_ne_top hint' (setLIntegral_le_lintegral _ _)
    refine le_antisymm ?_ h1
    refine (ENNReal.add_le_add_iff_right hc).1 ?_
    calc ∫⁻ x in B, f x ∂μ + ∫⁻ x in Bᶜ, f x ∂μ₀
        ≤ ∫⁻ x in B, f x ∂μ + ∫⁻ x in Bᶜ, f x ∂μ := add_le_add_right h2 _
      _ = ∫⁻ x, f x ∂μ := lintegral_add_compl f hB
      _ ≤ ∫⁻ x, f x ∂μ₀ := hint
      _ = ∫⁻ x in B, f x ∂μ₀ + ∫⁻ x in Bᶜ, f x ∂μ₀ := (lintegral_add_compl f hB).symm
  calc μ = (μ.withDensity f).withDensity fun x => (f x)⁻¹ :=
        (withDensity_inv_same hf (ae_of_all _ hpos) (ae_of_all _ hfin)).symm
    _ = (μ₀.withDensity f).withDensity fun x => (f x)⁻¹ := by rw [hd]
    _ = μ₀ := withDensity_inv_same hf (ae_of_all _ hpos) (ae_of_all _ hfin)

end MeynTweedie.InvarianceTightness
