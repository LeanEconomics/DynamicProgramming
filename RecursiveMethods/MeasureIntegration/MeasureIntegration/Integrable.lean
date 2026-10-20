/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MeasureIntegration.Integration

/-!
# Integrable functions, dominated convergence and the Radon–Nikodym Theorem

SLP §7.4, pp. 190–195. Positive and negative parts (`posPart`, `negPart`); the book's
integrable functions and integral (`IsBookIntegrable`, `bookIntegralReal`), which are Mathlib's
(`isBookIntegrable_iff`, `bookIntegralReal_eq`); Exercises 7.25–7.26; the Lebesgue Dominated
Convergence Theorem 7.10 (`theorem_7_10`) and its bounded case; absolute continuity,
concentration and mutual singularity (`absolutelyContinuous_iff_book`,
`mutuallySingular_iff_book`); the Radon–Nikodym Theorem 7.11 (`theorem_7_11`), with the book's
uniqueness proof for finite `λ` (`theorem_7_11_unique_book`) and the σ-finite case
(`theorem_7_11_unique`); and Lemma 7.12 with the book's proof (`lemma_7_12`).

**Correction to Theorem 7.11.** The book's `h` is "an integrable function". For a σ-finite
`λ` with `λ(S) = ∞` no density is integrable: with `λ = μ` Lebesgue measure on `ℝ`, every
density has integral `+∞` (`theorem_7_11_not_integrable`). The density is a finite-valued
nonnegative measurable function, integrable exactly when `λ` is finite.
-/

namespace StokeyLucasPrescott.MeasureIntegration

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- The positive part `f⁺ = max(f, 0)` (SLP p. 191). -/
def posPart (f : S → ℝ) : S → ℝ := fun s => max (f s) 0

/-- The negative part `f⁻ = max(−f, 0)` (SLP p. 191). -/
def negPart (f : S → ℝ) : S → ℝ := fun s => max (-f s) 0

omit [MeasurableSpace S] in
theorem posPart_sub_negPart (f : S → ℝ) : posPart f - negPart f = f := by
  funext s
  simp only [Pi.sub_apply, posPart, negPart]
  rcases le_total (f s) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

theorem ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-- `f` is **integrable** (SLP p. 191): measurable, with `∫ f⁺ < ∞` and `∫ f⁻ < ∞`. -/
def IsBookIntegrable (μ : Measure S) (f : S → ℝ) : Prop :=
  Measurable f ∧ ∫⁻ s, ENNReal.ofReal (posPart f s) ∂μ < ∞ ∧
    ∫⁻ s, ENNReal.ofReal (negPart f s) ∂μ < ∞

/-- The integral `∫ f = ∫ f⁺ − ∫ f⁻` (SLP p. 191). -/
noncomputable def bookIntegralReal (μ : Measure S) (f : S → ℝ) : ℝ :=
  (∫⁻ s, ENNReal.ofReal (posPart f s) ∂μ).toReal - (∫⁻ s, ENNReal.ofReal (negPart f s) ∂μ).toReal

/-- The book's integrable functions are Mathlib's measurable integrable functions. -/
theorem isBookIntegrable_iff (μ : Measure S) (f : S → ℝ) :
    IsBookIntegrable μ f ↔ Measurable f ∧ Integrable f μ := by
  simp only [IsBookIntegrable, posPart, negPart, ofReal_max_zero]
  constructor
  · rintro ⟨hm, hp, hn⟩
    refine ⟨hm, ?_⟩
    have hip : Integrable (fun s => max (f s) 0) μ := by
      refine ⟨(hm.max measurable_const).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (f := fun s => max (f s) 0)
          (Eventually.of_forall fun s => le_max_right _ _)).2 ?_⟩
      simpa [ofReal_max_zero] using hp
    have hin : Integrable (fun s => max (-f s) 0) μ := by
      refine ⟨(hm.neg.max measurable_const).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (f := fun s => max (-f s) 0)
          (Eventually.of_forall fun s => le_max_right _ _)).2 ?_⟩
      simpa [ofReal_max_zero] using hn
    have := hip.sub hin
    convert this using 1
    exact (posPart_sub_negPart f).symm
  · rintro ⟨hm, hi⟩
    have hle : ∀ g : S → ℝ, Integrable g μ → ∫⁻ s, ENNReal.ofReal (g s) ∂μ < ∞ := fun g hg =>
      lt_of_le_of_lt (lintegral_mono fun s => by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)) hg.2
    exact ⟨hm, hle f hi, hle (fun s => -f s) hi.neg⟩

/-- The book's integral is Mathlib's. -/
theorem bookIntegralReal_eq (μ : Measure S) {f : S → ℝ} (hf : IsBookIntegrable μ f) :
    bookIntegralReal μ f = ∫ s, f s ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part ((isBookIntegrable_iff μ f).1 hf).2,
    bookIntegralReal]
  simp only [posPart, negPart, ofReal_max_zero]

/-- **Exercise 7.25.** A bounded measurable function on a finite measure space is integrable. -/
theorem ex_7_25 (μ : Measure S) [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ s, |f s| ≤ M) : IsBookIntegrable μ f := by
  have hle : ∀ g : S → ℝ, (∀ s, g s ≤ M) → ∫⁻ s, ENNReal.ofReal (max (g s) 0) ∂μ < ∞ :=
    fun g hg => by
      calc ∫⁻ s, ENNReal.ofReal (max (g s) 0) ∂μ ≤ ∫⁻ _, ENNReal.ofReal M ∂μ :=
            lintegral_mono fun s => ENNReal.ofReal_le_ofReal (max_le (hg s)
              ((abs_nonneg (f s)).trans (hM s)))
        _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)
  exact ⟨hf, hle f fun s => (le_abs_self _).trans (hM s),
    hle (fun s => -f s) fun s => (neg_le_abs _).trans (hM s)⟩

/-- **Exercise 7.26a.** A measurable `f` is integrable iff `|f|` is, and then
`|∫ f| ≤ ∫ |f|`. -/
theorem ex_7_26a (μ : Measure S) {f : S → ℝ} (hf : Measurable f) :
    (Integrable f μ ↔ Integrable (fun s => |f s|) μ) ∧ |∫ s, f s ∂μ| ≤ ∫ s, |f s| ∂μ := by
  refine ⟨?_, ?_⟩
  · simp only [← Real.norm_eq_abs]
    exact (integrable_norm_iff hf.aestronglyMeasurable).symm
  · simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) f

/-- **Exercise 7.26b.** If `f` is measurable, `g` integrable and `|f| ≤ |g|`, then `f` is
integrable and `∫ |f| ≤ ∫ |g|`. -/
theorem ex_7_26b (μ : Measure S) {f g : S → ℝ} (hf : Measurable f) (hg : Integrable g μ)
    (hfg : ∀ s, |f s| ≤ |g s|) : Integrable f μ ∧ ∫ s, |f s| ∂μ ≤ ∫ s, |g s| ∂μ := by
  have hi : Integrable f μ := hg.mono hf.aestronglyMeasurable
    (Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hfg s)
  exact ⟨hi, integral_mono hi.abs hg.abs hfg⟩

/-- **Exercise 7.26c.** Linearity of the integral. -/
theorem ex_7_26c (μ : Measure S) {f g : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (α : ℝ) : Integrable (fun s => α * f s) μ ∧ Integrable (fun s => f s + g s) μ ∧
      ∫ s, α * f s ∂μ = α * ∫ s, f s ∂μ ∧
      ∫ s, f s + g s ∂μ = ∫ s, f s ∂μ + ∫ s, g s ∂μ :=
  ⟨hf.const_mul α, hf.add hg, integral_const_mul α f, integral_add hf hg⟩

/-- **Theorem 7.10 (Lebesgue Dominated Convergence Theorem).** If integrable `fₙ` converge
a.e. to a measurable `f` and `|fₙ| ≤ g` with `g` integrable, then `f` is integrable and
`∫ f = lim ∫ fₙ`. -/
theorem theorem_7_10 (μ : Measure S) {F : ℕ → S → ℝ} {f g : S → ℝ} (hf : Measurable f)
    (hF : ∀ n, Integrable (F n) μ) (hg : Integrable g μ) (hFg : ∀ n s, |F n s| ≤ g s)
    (hlim : ∀ᵐ s ∂μ, Tendsto (fun n => F n s) atTop (𝓝 (f s))) :
    Integrable f μ ∧ Tendsto (fun n => ∫ s, F n s ∂μ) atTop (𝓝 (∫ s, f s ∂μ)) := by
  refine ⟨hg.mono' hf.aestronglyMeasurable ?_, tendsto_integral_of_dominated_convergence g
    (fun n => (hF n).1) hg (fun n => Eventually.of_forall fun s => ?_) hlim⟩
  · filter_upwards [hlim] with s hs
    rw [Real.norm_eq_abs]
    exact le_of_tendsto (hs.abs) (Eventually.of_forall fun n => hFg n s)
  · rw [Real.norm_eq_abs]
    exact hFg n s

/-- **Bounded convergence** (SLP p. 193): uniformly bounded measurable functions converging
pointwise on a finite measure space have converging integrals. -/
theorem bounded_convergence (μ : Measure S) [IsFiniteMeasure μ] {F : ℕ → S → ℝ} {f : S → ℝ}
    (hf : Measurable f) (hF : ∀ n, Measurable (F n)) {M : ℝ} (hM : ∀ n s, |F n s| ≤ M)
    (hlim : ∀ s, Tendsto (fun n => F n s) atTop (𝓝 (f s))) :
    Tendsto (fun n => ∫ s, F n s ∂μ) atTop (𝓝 (∫ s, f s ∂μ)) :=
  (theorem_7_10 μ hf (fun n => ((isBookIntegrable_iff μ _).1 (ex_7_25 μ (hF n) (hM n))).2)
    (integrable_const M) hM (Eventually.of_forall hlim)).2

/-- `λ ≪ μ` (SLP p. 193): `μ(A) = 0` implies `λ(A) = 0` for measurable `A`. -/
theorem absolutelyContinuous_iff_book (ν μ : Measure S) :
    ν ≪ μ ↔ ∀ A, MeasurableSet A → μ A = 0 → ν A = 0 :=
  ⟨fun h _ _ hA => h hA, fun h => Measure.AbsolutelyContinuous.mk h⟩

/-- `λ` is **concentrated on** `A` (SLP p. 193). -/
def IsConcentratedOn (ν : Measure S) (A : Set S) : Prop :=
  ∀ B, MeasurableSet B → ν B = ν (A ∩ B)

/-- **Mutual singularity** (SLP p. 193): `λ` and `μ` are concentrated on disjoint measurable
sets. This is Mathlib's `MutuallySingular`. -/
theorem mutuallySingular_iff_book (ν μ : Measure S) :
    ν ⟂ₘ μ ↔ ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧ Disjoint A B ∧
      IsConcentratedOn ν A ∧ IsConcentratedOn μ B := by
  constructor
  · rintro ⟨s, hs, hνs, hμs⟩
    refine ⟨sᶜ, s, hs.compl, hs, disjoint_compl_left, fun B hB => ?_, fun B hB => ?_⟩
    · rw [← measure_inter_add_sdiff B hs, measure_mono_null inter_subset_right hνs, zero_add,
        sdiff_eq, inter_comm]
    · rw [← measure_inter_add_sdiff B hs.compl, measure_mono_null inter_subset_right hμs,
        zero_add, sdiff_eq, compl_compl, inter_comm]
  · rintro ⟨A, B, hA, hB, hAB, hνA, hμB⟩
    refine ⟨Aᶜ, hA.compl, ?_, ?_⟩
    · rw [hνA _ hA.compl, inter_compl_self, measure_empty]
    · rw [compl_compl, hμB _ hA, (hAB.symm.inter_eq), measure_empty]

/-- The measure obtained by integrating `f ∈ M⁺` is absolutely continuous (SLP p. 194). -/
theorem withDensity_absolutelyContinuous_book (μ : Measure S) (f : S → ℝ≥0∞) :
    μ.withDensity f ≪ μ :=
  withDensity_absolutelyContinuous μ f

/-- **Theorem 7.11 (Radon–Nikodym Theorem).** For σ-finite `λ ≪ μ` there is a finite-valued
nonnegative measurable `h` with `λ(A) = ∫_A h dμ` for every measurable `A`. -/
theorem theorem_7_11 {ν μ : Measure S} [SigmaFinite ν] [SigmaFinite μ] (hνμ : ν ≪ μ) :
    ∃ h : S → NNReal, Measurable h ∧ ∀ A, MeasurableSet A → ν A = ∫⁻ s in A, (h s : ℝ≥0∞) ∂μ := by
  refine ⟨fun s => (ν.rnDeriv μ s).toNNReal, (Measure.measurable_rnDeriv ν μ).ennreal_toNNReal,
    fun A hA => ?_⟩
  have hae : (fun s => ((ν.rnDeriv μ s).toNNReal : ℝ≥0∞)) =ᵐ[μ] ν.rnDeriv μ := by
    filter_upwards [Measure.rnDeriv_lt_top ν μ] with s hs
    exact ENNReal.coe_toNNReal hs.ne
  rw [setLIntegral_congr_fun_ae hA (hae.mono fun s hs _ => hs), ← withDensity_apply _ hA,
    Measure.withDensity_rnDeriv_eq ν μ hνμ]

/-- **Theorem 7.11, uniqueness: the book's proof** (for finite `λ`). If `∫_A g = λ(A) = ∫_A h`
for all `A`, then on `X = {g > h}`, `∫_X (g − h) = 0`, so `μ(X) = 0`; symmetrically `g = h`
a.e. -/
theorem theorem_7_11_unique_book {ν μ : Measure S} [IsFiniteMeasure ν] {g h : S → ℝ≥0∞}
    (hg : Measurable g) (hh : Measurable h)
    (hgν : ∀ A, MeasurableSet A → ∫⁻ s in A, g s ∂μ = ν A)
    (hhν : ∀ A, MeasurableSet A → ∫⁻ s in A, h s ∂μ = ν A) : g =ᵐ[μ] h := by
  have key : ∀ {g h : S → ℝ≥0∞}, Measurable g → Measurable h →
      (∀ A, MeasurableSet A → ∫⁻ s in A, g s ∂μ = ν A) →
      (∀ A, MeasurableSet A → ∫⁻ s in A, h s ∂μ = ν A) → μ {s | h s < g s} = 0 := by
    intro g h hg hh hgν hhν
    set X := {s | h s < g s}
    have hX : MeasurableSet X := measurableSet_lt hh hg
    have hfin : ∫⁻ s in X, h s ∂μ ≠ ∞ := by rw [hhν X hX]; exact measure_ne_top ν X
    have hsub : ∫⁻ s in X, g s - h s ∂μ = 0 := by
      rw [lintegral_sub hh hfin ((ae_restrict_iff' hX).2 (Eventually.of_forall fun s hs =>
        (show h s < g s from hs).le)), hgν X hX, hhν X hX, tsub_self]
    have hz := (lintegral_eq_zero_iff (f := fun s => g s - h s) (by exact hg.sub hh)).1 hsub
    have hX0 : ∀ᵐ s ∂μ, s ∈ X → g s - h s = 0 := (ae_restrict_iff' hX).1 hz
    refine measure_eq_zero_iff_ae_notMem.2 (hX0.mono fun s hs hsX => ?_)
    have := hs hsX
    rw [tsub_eq_zero_iff_le] at this
    exact absurd (show h s < g s from hsX) (not_lt.2 this)
  have h1 := key hg hh hgν hhν
  have h2 := key hh hg hhν hgν
  have : ∀ᵐ s ∂μ, s ∉ {s | h s < g s} ∪ {s | g s < h s} :=
    measure_eq_zero_iff_ae_notMem.1 (measure_union_null h1 h2)
  filter_upwards [this] with s hs
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hs
  exact le_antisymm hs.1 hs.2

/-- **Theorem 7.11, uniqueness** for σ-finite `μ`: two densities agree `μ`-a.e. -/
theorem theorem_7_11_unique {ν μ : Measure S} [SigmaFinite μ] {g h : S → ℝ≥0∞}
    (hg : Measurable g) (hh : Measurable h)
    (hgν : ∀ A, MeasurableSet A → ∫⁻ s in A, g s ∂μ = ν A)
    (hhν : ∀ A, MeasurableSet A → ∫⁻ s in A, h s ∂μ = ν A) : g =ᵐ[μ] h :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hg hh fun A hA _ =>
    (hgν A hA).trans (hhν A hA).symm

/-- **Correction to Theorem 7.11.** With `λ = μ` Lebesgue measure on `ℝ` (σ-finite), no density
is integrable. -/
theorem theorem_7_11_not_integrable (h : ℝ → NNReal)
    (hh : ∀ A, MeasurableSet A → volume A = ∫⁻ x in A, (h x : ℝ≥0∞)) :
    ¬ Integrable (fun x => (h x : ℝ)) := by
  intro hi
  have h1 : ∫⁻ x, (h x : ℝ≥0∞) = ∞ := by
    rw [← setLIntegral_univ, ← hh univ MeasurableSet.univ, Real.volume_univ]
  have he : ∀ x : NNReal, ‖(x : ℝ)‖ₑ = (x : ℝ≥0∞) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (NNReal.coe_nonneg x), ENNReal.ofReal_coe_nnreal]
  have h2 := hi.2
  simp only [HasFiniteIntegral, he] at h2
  exact absurd h1 h2.ne

/-- **Lemma 7.12.** Two finite measures `λ₁`, `λ₂` decompose as `λᵢ = γ + αᵢ` with `α₁ ⊥ α₂`.
The book's proof: with `μ = λ₁ + λ₂` and densities `hᵢ = dλᵢ/dμ`, take `h = min(h₁, h₂)`,
`γ = h μ`, `αᵢ = (hᵢ − h) μ`; then `α₁` is concentrated on `{h₁ > h}` and `α₂` on
`{h₂ > h}`, which are disjoint. -/
theorem lemma_7_12 (ν₁ ν₂ : Measure S) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    ∃ γ α₁ α₂ : Measure S, ν₁ = γ + α₁ ∧ ν₂ = γ + α₂ ∧ α₁ ⟂ₘ α₂ := by
  set μ := ν₁ + ν₂
  set h₁ := ν₁.rnDeriv μ
  set h₂ := ν₂.rnDeriv μ
  have hm₁ : Measurable h₁ := Measure.measurable_rnDeriv _ _
  have hm₂ : Measurable h₂ := Measure.measurable_rnDeriv _ _
  set h : S → ℝ≥0∞ := fun s => min (h₁ s) (h₂ s)
  have hm : Measurable h := hm₁.min hm₂
  have hν₁ : ν₁ = μ.withDensity h₁ :=
    (Measure.withDensity_rnDeriv_eq ν₁ μ (Measure.AbsolutelyContinuous.rfl.add_right ν₂)).symm
  have hν₂ : ν₂ = μ.withDensity h₂ :=
    (Measure.withDensity_rnDeriv_eq ν₂ μ (Measure.AbsolutelyContinuous.rfl.add_right' ν₁)).symm
  refine ⟨μ.withDensity h, μ.withDensity (h₁ - h), μ.withDensity (h₂ - h), ?_, ?_, ?_⟩
  · rw [← withDensity_add_left hm, hν₁]
    congr 1
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    exact (add_tsub_cancel_of_le (min_le_left _ _)).symm
  · rw [← withDensity_add_left hm, hν₂]
    congr 1
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    exact (add_tsub_cancel_of_le (min_le_right _ _)).symm
  · set B := {s | h s < h₁ s}
    have hB : MeasurableSet B := measurableSet_lt hm hm₁
    refine ⟨Bᶜ, hB.compl, ?_, ?_⟩
    · rw [withDensity_apply _ hB.compl]
      have h0 : ∀ s ∈ Bᶜ, (h₁ - h) s = 0 := fun s hs => by
        simp only [B, mem_compl_iff, mem_ofPred_eq, not_lt] at hs
        exact tsub_eq_zero_of_le hs
      rw [setLIntegral_congr_fun (g := fun _ => 0) hB.compl h0, lintegral_zero]
    · rw [compl_compl, withDensity_apply _ hB]
      have h0 : ∀ s ∈ B, (h₂ - h) s = 0 := fun s hs => by
        simp only [B, mem_ofPred_eq] at hs
        have h21 : h₂ s < h₁ s := by
          rcases min_lt_iff.1 hs with h' | h'
          · exact absurd h' (lt_irrefl _)
          · exact h'
        simp only [Pi.sub_apply, h, min_eq_right h21.le, tsub_self]
      rw [setLIntegral_congr_fun (g := fun _ => 0) hB h0, lintegral_zero]

end StokeyLucasPrescott.MeasureIntegration
