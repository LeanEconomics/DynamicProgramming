/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Almost everywhere convergence and convergence in probability

SLP Chapter 14, introduction and §14.1, pp. 415–420.

* Convergence almost everywhere (`ConvAE`) and in probability (`ConvInProb`).
* **Lemma 14.1** (`lemma_14_1`): `fₙ → f` a.e. iff `μ(|fₙ − f| ≤ ε for all n ≥ m) → 1` for every
  `ε > 0`.
* `μ(Aₙ i.o.) = lim_m μ(⋃_{n≥m} Aₙ)` (`measure_limsupSet`, (2) on p. 418).
* **Lemma 14.2** (`lemma_14_2`): `fₙ → f` a.e. iff `μ(|fₙ − f| > ε i.o.) = 0` for every `ε > 0`.
* **Lemma 14.3** (`lemma_14_3`, the first Borel–Cantelli lemma applied).
* A.e. convergence implies convergence in probability (`ConvAE.convInProb`).
* **Exercise 14.1**: the sliding indicators converge nowhere, but converge to `0` in
  probability, and their diagonal subsequence converges everywhere (`ex_14_1a`, `ex_14_1b`,
  `ex_14_1c`).
* **Exercise 14.2**: summable `μ(|fₙ − f| > εₙ)` with `εₙ → 0` gives a.e. convergence;
  convergence in probability gives an a.e. convergent subsequence (`ex_14_2a`, `ex_14_2b`).
-/

namespace StokeyLucasPrescott.LawsOfLargeNumbers

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `fₙ → f` almost everywhere (p. 415). -/
def ConvAE (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))

/-- `fₙ → f` in probability (p. 415). -/
def ConvInProb (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => μ {ω | ε < |f n ω - g ω|}) atTop (𝓝 0)

/-- `lim sup Aₙ = ⋂ₘ ⋃_{n≥m} Aₙ`, the event "`Aₙ` infinitely often" (p. 418). -/
def limsupSet (A : ℕ → Set Ω) : Set Ω := ⋂ m, ⋃ n ≥ m, A n

omit [MeasurableSpace Ω] in
theorem mem_limsupSet {A : ℕ → Set Ω} {ω : Ω} : ω ∈ limsupSet A ↔ ∃ᶠ n in atTop, ω ∈ A n := by
  simp only [limsupSet, mem_iInter, mem_iUnion, exists_prop, frequently_atTop]

/-- (2), p. 418: `μ(Aₙ i.o.) = lim_m μ(⋃_{n≥m} Aₙ)`. -/
theorem measure_limsupSet (μ : Measure Ω) [IsFiniteMeasure μ] {A : ℕ → Set Ω}
    (hA : ∀ n, MeasurableSet (A n)) :
    Tendsto (fun m => μ (⋃ n ≥ m, A n)) atTop (𝓝 (μ (limsupSet A))) :=
  tendsto_measure_iInter_atTop
    (fun _ => (MeasurableSet.biUnion (to_countable _) fun n _ => hA n).nullMeasurableSet)
    (fun m₁ m₂ h => biUnion_subset_biUnion_left fun n (hn : m₂ ≤ n) => (h.trans hn : m₁ ≤ n))
    ⟨0, measure_ne_top _ _⟩

theorem measurableSet_dev {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ n, Measurable (f n))
    (hg : Measurable g) (ε : ℝ) (n : ℕ) : MeasurableSet {ω | ε < |f n ω - g ω|} :=
  measurableSet_lt measurable_const ((hf n).sub hg).abs

/-- **Lemma 14.1.** `fₙ → f` a.e. iff `μ(|fₙ − f| ≤ ε for all n ≥ m) → 1` for every `ε > 0`. -/
theorem lemma_14_1 (μ : Measure Ω) [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) :
    ConvAE μ f g ↔
      ∀ ε > 0, Tendsto (fun m => μ {ω | ∀ n ≥ m, |f n ω - g ω| ≤ ε}) atTop (𝓝 1) := by
  set A : ℝ → ℕ → Set Ω := fun ε m => {ω | ∀ n ≥ m, |f n ω - g ω| ≤ ε}
  have hAm : ∀ ε m, MeasurableSet (A ε m) := fun ε m => by
    have : A ε m = ⋂ n, ⋂ (_ : n ≥ m), {ω | |f n ω - g ω| ≤ ε} := by
      ext ω; simp [A]
    rw [this]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      measurableSet_le ((hf n).sub hg).abs measurable_const
  have hmono : ∀ ε, Monotone (A ε) := fun ε m₁ m₂ h ω hω n hn => hω n (h.trans hn)
  have hlim : ∀ ε, Tendsto (fun m => μ (A ε m)) atTop (𝓝 (μ (⋃ m, A ε m))) := fun ε =>
    tendsto_measure_iUnion_atTop (hmono ε)
  constructor
  · intro h ε hε
    have h1 : μ (⋃ m, A ε m) = 1 := by
      rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion (hAm ε))]
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
      simp only [mem_ofPred_eq]
      intro ht
      obtain ⟨m, hm⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 ht) ε hε)
      exact hω (mem_iUnion.2 ⟨m, fun n hn => by
        have := hm n hn; rw [Real.dist_eq] at this; exact this.le⟩)
    rw [← h1]; exact hlim ε
  · intro h
    have hfull : ∀ k : ℕ, μ (⋃ m, A (1 / ((k : ℝ) + 1)) m) = 1 := fun k =>
      tendsto_nhds_unique (hlim _) (h _ (by positivity))
    have hae : ∀ᵐ ω ∂μ, ∀ k : ℕ, ω ∈ ⋃ m, A (1 / ((k : ℝ) + 1)) m := by
      rw [ae_all_iff]
      intro k
      rw [ae_iff, ← compl_def]
      exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion (hAm _))).2 (hfull k)
    filter_upwards [hae] with ω hω
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    obtain ⟨m, hm⟩ := mem_iUnion.1 (hω k)
    exact ⟨m, fun n hn => by rw [Real.dist_eq]; exact lt_of_le_of_lt (hm n hn) hk⟩

/-- **Lemma 14.2.** `fₙ → f` a.e. iff `μ(|fₙ − f| > ε i.o.) = 0` for every `ε > 0`. -/
theorem lemma_14_2 (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} :
    ConvAE μ f g ↔ ∀ ε > 0, μ (limsupSet fun n => {ω | ε < |f n ω - g ω|}) = 0 := by
  constructor
  · intro h ε hε
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
    simp only [mem_ofPred_eq]
    intro ht
    rw [mem_limsupSet] at hω
    obtain ⟨m, hm⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 ht) ε hε)
    obtain ⟨n, hn, hn'⟩ := frequently_atTop.1 hω m
    have := hm n hn
    rw [Real.dist_eq] at this
    exact absurd hn' (not_lt.2 this.le)
  · intro h
    have hae : ∀ᵐ ω ∂μ, ∀ k : ℕ,
        ω ∉ limsupSet fun n => {ω | 1 / ((k : ℝ) + 1) < |f n ω - g ω|} := by
      rw [ae_all_iff]
      intro k
      rw [ae_iff]
      simpa using h (1 / ((k : ℝ) + 1)) (by positivity)
    filter_upwards [hae] with ω hω
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    have := hω k
    rw [mem_limsupSet, not_frequently] at this
    obtain ⟨m, hm⟩ := eventually_atTop.1 this
    exact ⟨m, fun n hn => by
      rw [Real.dist_eq]
      have := hm n hn
      simp only [mem_ofPred_eq, not_lt] at this
      exact lt_of_le_of_lt this hk⟩

/-- The first Borel–Cantelli lemma, `Σ μ(Aₙ) < ∞ ⇒ μ(Aₙ i.o.) = 0` (proof of Lemma 14.3). -/
theorem measure_limsupSet_eq_zero (μ : Measure Ω) {A : ℕ → Set Ω} (hA : ∑' n, μ (A n) ≠ ∞) :
    μ (limsupSet A) = 0 := by
  have := measure_limsup_atTop_eq_zero (μ := μ) hA
  rwa [limsup_eq_iInf_iSup_of_nat] at this

/-- **Lemma 14.3.** If `Σₙ μ(|fₙ − f| > ε) < ∞` for every `ε > 0`, then `fₙ → f` a.e. -/
theorem lemma_14_3 (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (h : ∀ ε > 0, ∑' n, μ {ω | ε < |f n ω - g ω|} ≠ ∞) : ConvAE μ f g :=
  (lemma_14_2 μ).2 fun ε hε => measure_limsupSet_eq_zero μ (h ε hε)

/-- A.e. convergence implies convergence in probability (p. 420). -/
theorem ConvAE.convInProb {μ : Measure Ω} [IsFiniteMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (h : ConvAE μ f g) : ConvInProb μ f g := by
  intro ε hε
  have h0 := (lemma_14_2 μ).1 h ε hε
  have hlim := measure_limsupSet μ (measurableSet_dev hf hg ε)
  rw [h0] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun m => zero_le) fun m => measure_mono (subset_biUnion_of_mem (u := fun n =>
      {ω | ε < |f n ω - g ω|}) (le_refl m))

/-- **Exercise 14.2a.** If `εₙ → 0` and `Σₙ μ(|fₙ − f| > εₙ) < ∞`, then `fₙ → f` a.e. -/
theorem ex_14_2a (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∑' n, μ {ω | ε n < |f n ω - g ω|} ≠ ∞) :
    ConvAE μ f g := by
  have h0 := measure_limsupSet_eq_zero μ h
  rw [ConvAE, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [mem_ofPred_eq] at hω
  rw [mem_limsupSet]
  intro hev
  apply hω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hε
  filter_upwards [hev] with n hn
  simp only [not_lt] at hn
  rw [norm_norm, Real.norm_eq_abs]
  exact hn

/-- **Exercise 14.2b.** Convergence in probability gives an a.e. convergent subsequence. -/
theorem ex_14_2b (μ : Measure Ω) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (h : ConvInProb μ f g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvAE μ (fun k => f (φ k)) g := by
  have hev : ∀ k : ℕ, ∀ᶠ n in atTop,
      μ {ω | 1 / ((k : ℝ) + 1) < |f n ω - g ω|} ≤ ((2 : ℝ≥0∞)⁻¹) ^ k := fun k =>
    (h _ (by positivity)).eventually (ge_mem_nhds
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) k))
  obtain ⟨φ, hφ, hφk⟩ := extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ex_14_2a μ (ε := fun k => 1 / ((k : ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat ?_⟩
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hφk)
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

end StokeyLucasPrescott.LawsOfLargeNumbers
