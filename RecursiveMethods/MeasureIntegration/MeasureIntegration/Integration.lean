/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.MeasurableFunctions

/-!
# Integration of nonnegative functions

SLP §7.4, pp. 184–190. The integral of a nonnegative simple function in standard
representation (`simpleIntegral`) and its agreement with Mathlib's integral
(`simpleIntegral_eq_lintegral`); Exercise 7.17 (`ex_7_17`). The integral of `f ∈ M⁺(S, 𝒮)` as the
supremum over simple `0 ≤ φ ≤ f` (`bookIntegral`), which is Mathlib's `lintegral`
(`bookIntegral_eq_lintegral`, by Mathlib's reduction to finite-valued simple functions, without
the Monotone Convergence Theorem). Lemma 7.7 with the book's proof (`lemma_7_7`), Exercise 7.18
(`ex_7_18a`, `ex_7_18b`), the Monotone Convergence Theorem 7.8 with the book's proof
(`theorem_7_8`), Exercise 7.19 (`ex_7_19`), Exercises 7.20–7.22, Fatou's Lemma 7.9 with the
book's proof (`lemma_7_9`), and Exercises 7.23–7.24.
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- The integral of a nonnegative simple function `φ`, through its standard representation
`φ = Σ aᵢ χ_{Aᵢ}` with `Aᵢ = {φ = aᵢ}` (SLP p. 185): `∫ φ dμ = Σᵢ aᵢ μ(Aᵢ)`. -/
noncomputable def simpleIntegral (μ : Measure S) (φ : S → ℝ) (hφ : (range φ).Finite) : ℝ≥0∞ :=
  ∑ a ∈ hφ.toFinset, ENNReal.ofReal a * μ (φ ⁻¹' {a})

/-- A measurable function with finite range, as a Mathlib simple function. -/
def toSimpleFunc (φ : S → ℝ) (hm : Measurable φ) (hφ : (range φ).Finite) :
    SimpleFunc S ℝ :=
  ⟨φ, fun x => hm (measurableSet_singleton x), hφ⟩

/-- The book's integral of a simple function is Mathlib's. -/
theorem simpleIntegral_eq_lintegral (μ : Measure S) {φ : S → ℝ} (hm : Measurable φ)
    (hφ : (range φ).Finite) :
    simpleIntegral μ φ hφ = ∫⁻ s, ENNReal.ofReal (φ s) ∂μ := by
  have : ∫⁻ s, ENNReal.ofReal (φ s) ∂μ =
      ((toSimpleFunc φ hm hφ).map ENNReal.ofReal).lintegral μ := by
    rw [← SimpleFunc.lintegral_eq_lintegral]
    rfl
  rw [this, SimpleFunc.map_lintegral]
  rfl

omit [MeasurableSpace S] in
theorem finite_range_add {φ ψ : S → ℝ} (hφ : (range φ).Finite) (hψ : (range ψ).Finite) :
    (range (φ + ψ)).Finite :=
  (hφ.image2 (· + ·) hψ).subset (by rintro _ ⟨s, rfl⟩; exact mem_image2_of_mem ⟨s, rfl⟩ ⟨s, rfl⟩)

omit [MeasurableSpace S] in
theorem finite_range_smul {φ : S → ℝ} (hφ : (range φ).Finite) (c : ℝ) :
    (range (c • φ)).Finite :=
  (hφ.image (c • ·)).subset (by rintro _ ⟨s, rfl⟩; exact ⟨φ s, ⟨s, rfl⟩, rfl⟩)

/-- **Exercise 7.17.** The integral of nonnegative simple functions is additive and positively
homogeneous. -/
theorem ex_7_17 (μ : Measure S) {φ ψ : S → ℝ} (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφ : (range φ).Finite) (hψ : (range ψ).Finite) (hφ0 : ∀ s, 0 ≤ φ s) (hψ0 : ∀ s, 0 ≤ ψ s)
    {c : ℝ} (hc : 0 ≤ c) :
    simpleIntegral μ (φ + ψ) (finite_range_add hφ hψ) =
        simpleIntegral μ φ hφ + simpleIntegral μ ψ hψ ∧
      simpleIntegral μ (c • φ) (finite_range_smul hφ c) =
        ENNReal.ofReal c * simpleIntegral μ φ hφ := by
  rw [simpleIntegral_eq_lintegral μ (hφm.add hψm), simpleIntegral_eq_lintegral μ hφm,
    simpleIntegral_eq_lintegral μ hψm, simpleIntegral_eq_lintegral μ (hφm.const_smul c),
    ← lintegral_const_mul _ hφm.ennreal_ofReal, ← lintegral_add_left hφm.ennreal_ofReal]
  refine ⟨lintegral_congr fun s => ?_, lintegral_congr fun s => ?_⟩
  · exact ENNReal.ofReal_add (hφ0 s) (hψ0 s)
  · exact ENNReal.ofReal_mul hc

/-- The **integral** of `f ∈ M⁺(S, 𝒮)` (SLP p. 186): the supremum of `∫ φ dμ` over measurable
simple functions `0 ≤ φ ≤ f`. -/
noncomputable def bookIntegral (μ : Measure S) (f : S → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (φ : S → ℝ) (h : Measurable φ ∧ (range φ).Finite ∧
    ∀ s, 0 ≤ φ s ∧ ENNReal.ofReal (φ s) ≤ f s), simpleIntegral μ φ h.2.1

/-- The book's integral is Mathlib's `lintegral`. -/
theorem bookIntegral_eq_lintegral (μ : Measure S) (f : S → ℝ≥0∞) :
    bookIntegral μ f = ∫⁻ s, f s ∂μ := by
  apply le_antisymm
  · refine iSup₂_le fun φ h => ?_
    rw [simpleIntegral_eq_lintegral μ h.1 h.2.1]
    exact lintegral_mono fun s => (h.2.2 s).2
  · rw [lintegral_eq_nnreal]
    refine iSup₂_le fun ψ hψ => ?_
    let φ : S → ℝ := fun s => (ψ s : ℝ)
    have hm : Measurable φ := measurable_coe_nnreal_real.comp ψ.measurable
    have hfin : (range φ).Finite := (ψ.finite_range.image fun x : NNReal => (x : ℝ)).subset (by
      rintro _ ⟨s, rfl⟩
      exact ⟨ψ s, ⟨s, rfl⟩, rfl⟩)
    have h : Measurable φ ∧ (range φ).Finite ∧ ∀ s, 0 ≤ φ s ∧ ENNReal.ofReal (φ s) ≤ f s :=
      ⟨hm, hfin, fun s => ⟨(ψ s).2, by simp only [φ, ENNReal.ofReal_coe_nnreal]; exact hψ s⟩⟩
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun φ (h : Measurable φ ∧ (range φ).Finite ∧
      ∀ s, 0 ≤ φ s ∧ ENNReal.ofReal (φ s) ≤ f s) => simpleIntegral μ φ h.2.1) φ h)
    rw [simpleIntegral_eq_lintegral μ hm hfin, ← SimpleFunc.lintegral_eq_lintegral]
    simp [φ, ENNReal.ofReal_coe_nnreal]

/-- The integral over `A` is the integral of `f χ_A` (SLP p. 186). -/
theorem setIntegral_book (μ : Measure S) (f : S → ℝ≥0∞) {A : Set S} (hA : MeasurableSet A) :
    ∫⁻ s in A, f s ∂μ = ∫⁻ s, A.indicator f s ∂μ :=
  (lintegral_indicator hA f).symm

omit [MeasurableSpace S] in
/-- A finite sum of measures is a measure (Exercise 7.4a, iterated). -/
theorem IsMeasure.finset_sum {𝒮 : Set (Set S)} {ι : Type*} (F : Finset ι)
    {μ : ι → Set S → ℝ≥0∞} (h : ∀ i ∈ F, IsMeasure 𝒮 (μ i)) :
    IsMeasure 𝒮 fun A => ∑ i ∈ F, μ i A := by
  refine ⟨by simp [Finset.sum_eq_zero fun i hi => (h i hi).empty], fun A hA hd => ?_⟩
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  exact Finset.sum_congr rfl fun i hi => (h i hi).iUnion A hA hd

omit [MeasurableSpace S] in
/-- A nonnegative multiple of a measure is a measure. -/
theorem IsMeasure.const_mul {𝒮 : Set (Set S)} {μ : Set S → ℝ≥0∞} (h : IsMeasure 𝒮 μ)
    (c : ℝ≥0∞) : IsMeasure 𝒮 fun A => c * μ A :=
  ⟨by simp [h.empty], fun A hA hd => by rw [h.iUnion A hA hd, ENNReal.tsum_mul_left]⟩

/-- **Lemma 7.7.** For a nonnegative simple `φ`, `λ(A) = ∫_A φ dμ` is a measure. The book's
proof: `λ(A) = Σᵢ aᵢ μ(A ∩ Bᵢ)` is a combination of measures (Exercise 7.4). -/
theorem lemma_7_7 (μ : Measure S) {φ : S → ℝ} (hm : Measurable φ) (hφ : (range φ).Finite) :
    IsMeasure {A | MeasurableSet A} fun A => ∫⁻ s in A, ENNReal.ofReal (φ s) ∂μ := by
  have heq : ∀ A, MeasurableSet A → ∫⁻ s in A, ENNReal.ofReal (φ s) ∂μ =
      ∑ a ∈ hφ.toFinset, ENNReal.ofReal a * μ (A ∩ φ ⁻¹' {a}) := by
    intro A hA
    rw [← simpleIntegral_eq_lintegral (μ.restrict A) hm hφ, simpleIntegral]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Measure.restrict_apply (hm (measurableSet_singleton a)), inter_comm]
  have hsum : IsMeasure {A | MeasurableSet A}
      fun A => ∑ a ∈ hφ.toFinset, ENNReal.ofReal a * μ (A ∩ φ ⁻¹' {a}) :=
    IsMeasure.finset_sum _ fun a _ =>
      (ex_7_4b (isMeasure_coe μ) (isSigmaAlgebra_measurableSet _)
        (hm (measurableSet_singleton a))).const_mul _
  refine ⟨by simp, fun A hA hd => ?_⟩
  rw [heq _ (MeasurableSet.iUnion hA), hsum.iUnion A hA hd]
  exact tsum_congr fun n => (heq _ (hA n)).symm

/-- **Exercise 7.18.** (a) `f ≤ g` implies `∫ f ≤ ∫ g`; (b) `A ⊆ B` implies `∫_A f ≤ ∫_B f`. -/
theorem ex_7_18a (μ : Measure S) {f g : S → ℝ≥0∞} (hfg : f ≤ g) :
    ∫⁻ s, f s ∂μ ≤ ∫⁻ s, g s ∂μ :=
  lintegral_mono hfg

theorem ex_7_18b (μ : Measure S) (f : S → ℝ≥0∞) {A B : Set S} (hAB : A ⊆ B) :
    ∫⁻ s in A, f s ∂μ ≤ ∫⁻ s in B, f s ∂μ :=
  lintegral_mono_set hAB

/-- **Theorem 7.8 (Monotone Convergence Theorem).** If `fₙ ∈ M⁺` increase pointwise to `f`,
then `∫ f = lim ∫ fₙ`. The book's proof: for simple `0 ≤ φ ≤ f` and `0 < α < 1`, the sets
`Aₙ = {αφ ≤ fₙ}` increase to `S`, so by Lemma 7.7 and Theorem 7.1,
`α ∫ φ = lim α ∫_{Aₙ} φ ≤ lim ∫ fₙ`. -/
theorem theorem_7_8 (μ : Measure S) {f : ℕ → S → ℝ≥0∞} {g : S → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f)
    (hlim : ∀ s, Tendsto (fun n => f n s) atTop (𝓝 (g s))) :
    Tendsto (fun n => ∫⁻ s, f n s ∂μ) atTop (𝓝 (∫⁻ s, g s ∂μ)) := by
  have hint_mono : Monotone fun n => ∫⁻ s, f n s ∂μ := fun m n hmn => lintegral_mono (hmono hmn)
  have hfg : ∀ n s, f n s ≤ g s := fun n s =>
    ge_of_tendsto (hlim s) (eventually_atTop.2 ⟨n, fun k hk => hmono hk s⟩)
  have hL := tendsto_atTop_iSup hint_mono
  convert hL using 2
  apply le_antisymm
  · rw [← bookIntegral_eq_lintegral]
    refine iSup₂_le fun φ h => ?_
    obtain ⟨hm, hfin, hφf⟩ := h
    refine ENNReal.le_of_forall_lt_one_mul_le fun c hc => ?_
    have hcfin : c ≠ ∞ := ne_top_of_lt hc
    set α := c.toReal
    have hα0 : 0 ≤ α := ENNReal.toReal_nonneg
    have hcα : c = ENNReal.ofReal α := (ENNReal.ofReal_toReal hcfin).symm
    have hα1 : α < 1 := by
      rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα0, ← hcα, ENNReal.ofReal_one]
      exact hc
    set A : ℕ → Set S := fun n => {s | ENNReal.ofReal (α * φ s) ≤ f n s}
    have hA : ∀ n, MeasurableSet (A n) := fun n =>
      measurableSet_le (hm.const_mul α).ennreal_ofReal (hf n)
    have hAmono : Monotone A := fun m n hmn s hs => hs.trans (hmono hmn s)
    have hAU : (⋃ n, A n) = univ := by
      refine eq_univ_of_forall fun s => mem_iUnion.2 ?_
      by_cases h0 : φ s = 0
      · exact ⟨0, by simp [A, h0]⟩
      · have hpos : 0 < φ s := lt_of_le_of_ne (hφf s).1 (Ne.symm h0)
        have hlt : ENNReal.ofReal (α * φ s) < g s := by
          refine lt_of_lt_of_le ?_ ((hφf s).2.trans (le_of_eq rfl))
          · exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by nlinarith)
        obtain ⟨n, hn⟩ := ((hlim s).eventually (lt_mem_nhds hlt)).exists
        exact ⟨n, hn.le⟩
    have h77 := lemma_7_7 μ hm hfin
    have h71 := theorem_7_1a h77 (isSigmaAlgebra_measurableSet _) hA hAmono
    rw [hAU, Measure.restrict_univ, ← simpleIntegral_eq_lintegral μ hm hfin] at h71
    have hlim' := ENNReal.Tendsto.const_mul h71 (Or.inr hcfin)
    refine le_of_tendsto' hlim' fun n => ?_
    calc c * ∫⁻ s in A n, ENNReal.ofReal (φ s) ∂μ
        = ∫⁻ s in A n, ENNReal.ofReal (α * φ s) ∂μ := by
          rw [← lintegral_const_mul _ hm.ennreal_ofReal, hcα]
          exact lintegral_congr fun s => (ENNReal.ofReal_mul hα0).symm
      _ ≤ ∫⁻ s in A n, f n s ∂μ := setLIntegral_mono (hf n) fun s hs => hs
      _ ≤ ∫⁻ s, f n s ∂μ := setLIntegral_le_lintegral _ _
      _ ≤ ⨆ n, ∫⁻ s, f n s ∂μ := le_iSup (fun n => ∫⁻ s, f n s ∂μ) n
  · exact iSup_le fun n => lintegral_mono (hfg n)

omit [MeasurableSpace S] in
/-- **Exercise 7.19.** The proof fails for `α = 1`: with `fₙ = 1 − 1/(n+1)` increasing to
`f = 1` and `φ = 1`, the sets `{φ ≤ fₙ}` are all empty, so they do not exhaust `S`. -/
theorem ex_7_19 [Nonempty S] :
    let f : ℕ → S → ℝ := fun n _ => 1 - 1 / ((n : ℝ) + 1)
    (∀ s, Tendsto (fun n => f n s) atTop (𝓝 1)) ∧ (⋃ n, {s | (1 : ℝ) ≤ f n s}) ≠ univ := by
  intro f
  refine ⟨fun s => ?_, fun h => ?_⟩
  · have := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa [f] using this
  · obtain ⟨s⟩ := ‹Nonempty S›
    have := h ▸ mem_univ s
    obtain ⟨n, hn⟩ := mem_iUnion.1 this
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [f, mem_ofPred_eq] at hn
    linarith

/-- **Exercise 7.20a.** The integral on `M⁺` is additive and positively homogeneous. -/
theorem ex_7_20a (μ : Measure S) {f g : S → ℝ≥0∞} (hf : Measurable f) (c : ℝ≥0∞) :
    ∫⁻ s, f s + g s ∂μ = ∫⁻ s, f s ∂μ + ∫⁻ s, g s ∂μ ∧
      ∫⁻ s, c * f s ∂μ = c * ∫⁻ s, f s ∂μ :=
  ⟨lintegral_add_left hf g, lintegral_const_mul c hf⟩

/-- **Exercise 7.20b.** If `μ(A) = 0` then `∫_A f = 0`. -/
theorem ex_7_20b (μ : Measure S) (f : S → ℝ≥0∞) {A : Set S} (hA : μ A = 0) :
    ∫⁻ s in A, f s ∂μ = 0 :=
  setLIntegral_measure_zero A f hA

/-- **Exercise 7.20c.** If `∫ f < ∞` then `μ{f = +∞} = 0`. -/
theorem ex_7_20c (μ : Measure S) {f : S → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ s, f s ∂μ < ∞) : μ {s | f s = ∞} = 0 := by
  have := ae_lt_top hf hfin.ne
  rw [ae_iff] at this
  simpa using this

/-- **Exercise 7.21.** For `f ∈ M⁺`, `λ(A) = ∫_A f dμ` is a measure. -/
theorem ex_7_21 (μ : Measure S) (f : S → ℝ≥0∞) :
    IsMeasure {A | MeasurableSet A} fun A => ∫⁻ s in A, f s ∂μ := by
  have := isMeasure_coe (μ.withDensity f)
  refine ⟨by simp, fun A hA hd => ?_⟩
  rw [← withDensity_apply _ (MeasurableSet.iUnion hA), this.iUnion A hA hd]
  exact tsum_congr fun n => withDensity_apply _ (hA n)

/-- **Exercise 7.22.** `∫ Σᵢ gᵢ dμ = Σᵢ ∫ gᵢ dμ` for `gᵢ ∈ M⁺`. -/
theorem ex_7_22 (μ : Measure S) {g : ℕ → S → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) :
    ∫⁻ s, ∑' i, g i s ∂μ = ∑' i, ∫⁻ s, g i s ∂μ :=
  lintegral_tsum fun i => (hg i).aemeasurable

/-- **Lemma 7.9 (Fatou's Lemma).** `∫ lim inf fₙ ≤ lim inf ∫ fₙ`. The book's proof: apply the
Monotone Convergence Theorem to `gₘ = inf_{n ≥ m} fₙ`. -/
theorem lemma_7_9 (μ : Measure S) {f : ℕ → S → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    ∫⁻ s, liminf (fun n => f n s) atTop ∂μ ≤ liminf (fun n => ∫⁻ s, f n s ∂μ) atTop := by
  set g : ℕ → S → ℝ≥0∞ := fun m s => ⨅ n ≥ m, f n s
  have hg : ∀ m, Measurable (g m) := fun m =>
    Measurable.iInf fun n => Measurable.iInf fun _ => hf n
  have hgmono : Monotone g := fun m m' hmm' s =>
    le_iInf₂ fun n hn => iInf₂_le n (hmm'.trans hn)
  have hglim : ∀ s, Tendsto (fun m => g m s) atTop (𝓝 (liminf (fun n => f n s) atTop)) := by
    intro s
    rw [liminf_eq_iSup_iInf_of_nat]
    exact tendsto_atTop_iSup fun m m' hmm' => hgmono hmm' s
  have hMCT := theorem_7_8 μ hg hgmono hglim
  rw [← hMCT.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun m => ?_)
  exact lintegral_mono fun s => iInf₂_le m le_rfl

/-- **Exercise 7.23.** Fatou's inequality can be strict: on `ℝ` with Lebesgue measure,
`fₙ = χ_{[n, n+1)}` has `lim inf fₙ = 0` but `∫ fₙ = 1`. -/
theorem ex_7_23 :
    let f : ℕ → ℝ → ℝ≥0∞ := fun n => (Ico (n : ℝ) (n + 1)).indicator 1
    (∫⁻ x, liminf (fun n => f n x) atTop) = 0 ∧ ∀ n, ∫⁻ x, f n x = 1 := by
  intro f
  constructor
  · have : ∀ x : ℝ, liminf (fun n => f n x) atTop = 0 := by
      intro x
      have hev : ∀ᶠ n : ℕ in atTop, f n x = 0 := by
        obtain ⟨N, hN⟩ := exists_nat_gt x
        filter_upwards [eventually_ge_atTop N] with n hn
        refine indicator_of_notMem (fun h => ?_) _
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith [h.1]
      rw [liminf_congr hev]
      exact liminf_const 0
    simp [this]
  · intro n
    simp only [f]
    rw [lintegral_indicator_one measurableSet_Ico, Real.volume_Ico]
    simp

/-- **Exercise 7.24a.** For `f ∈ M⁺`, `f = 0` a.e. iff `∫ f = 0`. -/
theorem ex_7_24a (μ : Measure S) {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∀ᵐ s ∂μ, f s = 0) ↔ ∫⁻ s, f s ∂μ = 0 :=
  (lintegral_eq_zero_iff hf).symm

/-- **Exercise 7.24b.** The Monotone Convergence Theorem holds when `fₙ → f` only almost
everywhere. -/
theorem ex_7_24b (μ : Measure S) {f : ℕ → S → ℝ≥0∞} {g : S → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f)
    (hlim : ∀ᵐ s ∂μ, Tendsto (fun n => f n s) atTop (𝓝 (g s))) :
    Tendsto (fun n => ∫⁻ s, f n s ∂μ) atTop (𝓝 (∫⁻ s, g s ∂μ)) :=
  lintegral_tendsto_of_tendsto_of_monotone (fun n => (hf n).aemeasurable)
    (Eventually.of_forall fun s _ _ hmn => hmono hmn s) hlim

end StokeyLucasPrescott.MeasureIntegration
