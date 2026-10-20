/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ConvergenceApplications.ConvergenceConcepts
import ConvergenceApplications.TotalVariation

/-!
# Characterizations of strong convergence

SLP §11.3, Theorems 11.6–11.7 and Lemma 11.8, pp. 340–344. Throughout, `λₙ` and `λ` are
probability measures.

* `abs_integral_sub_le_tvDist`: `|∫ f dλ₁ − ∫ f dλ₂| ≤ ‖λ₁ − λ₂‖` for measurable `|f| ≤ 1`. With a
  Hahn set `B`, `λ₁ = λ₂ + α₁` on `B` and `λ₂ = λ₁ + α₂` on `Bᶜ`, and the difference of the
  integrals is `∫ f dα₁ − ∫ f dα₂`.
* **Theorem 11.6** (`theorem_11_6`): `‖λₙ − λ‖ → 0` iff `λₙ(A) → λ(A)` uniformly in `A`.
* **Theorem 11.7** (`theorem_11_7`): `‖λₙ − λ‖ → 0` iff `λₙ → λ` strongly. The book
  approximates by simple functions; here the bound above is used directly.
* **Lemma 11.8** (`lemma_11_8`): the probability measures are complete in the total variation
  norm. The book's proof that the limit `λ(A) = lim λₙ(A)` is countably additive exchanges a
  limit and a sum without justification. The exchange holds because the convergence is uniform
  in `A`: the tails `λ(⋃_{i ≥ K} Aᵢ)` are within `ε` of `λₙ(⋃_{i ≥ K} Aᵢ)`, which tend to `0`.
-/

namespace StokeyLucasPrescott.ConvergenceApplications

open MeasureTheory Filter Topology Set

variable {S : Type*} [MeasurableSpace S]

theorem abs_sub_le_add (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (A : Set S) : |μ₁.real A - μ₂.real A| ≤ μ₁.real univ + μ₂.real univ :=
  (abs_sub _ _).trans (by
    rw [abs_of_nonneg measureReal_nonneg, abs_of_nonneg measureReal_nonneg]
    exact add_le_add (measureReal_mono (subset_univ A)) (measureReal_mono (subset_univ A)))

theorem bddAbove_supDiff (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    BddAbove ((fun A => |μ₁.real A - μ₂.real A|) '' {A | MeasurableSet A}) :=
  ⟨_, by rintro _ ⟨A, -, rfl⟩; exact abs_sub_le_add μ₁ μ₂ A⟩

/-- `2|λ₁(A) − λ₂(A)| ≤ ‖λ₁ − λ₂‖` for probability measures. -/
theorem two_abs_le_tvDist (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {A : Set S} (hA : MeasurableSet A) :
    2 * |μ₁.real A - μ₂.real A| ≤ tvDist μ₁ μ₂ := by
  rw [(lemma_11_5 μ₁ μ₂ (by simp)).1]
  exact mul_le_mul_of_nonneg_left (le_csSup (bddAbove_supDiff μ₁ μ₂) ⟨A, hA, rfl⟩)
    zero_le_two

/-- If `|λ₁(A) − λ₂(A)| ≤ δ` for all `A`, then `‖λ₁ − λ₂‖ ≤ 2δ`. -/
theorem tvDist_le_of_forall (μ₁ μ₂ : Measure S) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {δ : ℝ} (h : ∀ A, MeasurableSet A → |μ₁.real A - μ₂.real A| ≤ δ) :
    tvDist μ₁ μ₂ ≤ 2 * δ := by
  rw [(lemma_11_5 μ₁ μ₂ (by simp)).1]
  refine mul_le_mul_of_nonneg_left (csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_) zero_le_two
  rintro _ ⟨A, hA, rfl⟩
  exact h A hA

theorem tvDist_nonneg (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    0 ≤ tvDist μ₁ μ₂ :=
  tvOf_nonneg (bddAbove_tvDist μ₁ μ₂)

/-- For a nonnegative sequence, `uₙ → 0` iff eventually `uₙ < ε` for every `ε > 0`. -/
theorem tendsto_zero_iff_of_nonneg {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) :
    Tendsto u atTop (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ n in atTop, u n < ε := by
  rw [tendsto_order]
  exact ⟨fun h => h.2, fun h => ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hu n), h⟩⟩

/-- **Theorem 11.6.** `‖λₙ − λ‖ → 0` iff `λₙ(A) → λ(A)` uniformly in `A`. -/
theorem theorem_11_6 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) ↔
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ A, MeasurableSet A → |(ls n).real A - l.real A| < ε := by
  rw [tendsto_zero_iff_of_nonneg fun n => tvDist_nonneg (ls n) l]
  constructor
  · intro h ε hε
    filter_upwards [h (2 * ε) (by positivity)] with n hn A hA
    have := two_abs_le_tvDist (ls n) l hA
    linarith
  · intro h ε hε
    filter_upwards [h (ε / 4) (by positivity)] with n hn
    have := tvDist_le_of_forall (ls n) l fun A hA => (hn A hA).le
    linarith

theorem integrable_of_abs_le (μ : Measure S) [IsFiniteMeasure μ] {f : S → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ s, |f s| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact hC s)

/-- The partition `{B, Bᶜ}` bounds `|D(B)| + |D(Bᶜ)|` by the total variation. -/
theorem abs_add_abs_compl_le (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {B : Set S} (hB : MeasurableSet B) :
    |μ₁.real B - μ₂.real B| + |μ₁.real Bᶜ - μ₂.real Bᶜ| ≤ tvDist μ₁ μ₂ := by
  refine le_trans (le_of_eq ?_) (le_csSup (bddAbove_tvDist μ₁ μ₂) ⟨2, _, isPartition_pair hB, rfl⟩)
  simp [Fin.sum_univ_two]

/-- `|∫ f dλ₁ − ∫ f dλ₂| ≤ ‖λ₁ − λ₂‖` for measurable `f` with `|f| ≤ 1`. -/
theorem abs_integral_sub_le_tvDist (μ₁ μ₂ : Measure S) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {f : S → ℝ} (hf : Measurable f) (h1 : ∀ s, |f s| ≤ 1) :
    |∫ s, f s ∂μ₁ - ∫ s, f s ∂μ₂| ≤ tvDist μ₁ μ₂ := by
  obtain ⟨B, hB, hpos, hneg⟩ := hahn_decomposition μ₁ μ₂
  have hle1 : μ₂.restrict B ≤ μ₁.restrict B := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hpos _ (ht.inter hB) inter_subset_right
  have hle2 : μ₁.restrict Bᶜ ≤ μ₂.restrict Bᶜ := Measure.le_iff.2 fun t ht => by
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hneg _ (ht.inter hB.compl) inter_subset_right
  set α₁ := μ₁.restrict B - μ₂.restrict B
  set α₂ := μ₂.restrict Bᶜ - μ₁.restrict Bᶜ
  have e1 : α₁ + μ₂.restrict B = μ₁.restrict B := Measure.sub_add_cancel_of_le hle1
  have e2 : α₂ + μ₁.restrict Bᶜ = μ₂.restrict Bᶜ := Measure.sub_add_cancel_of_le hle2
  have : IsFiniteMeasure α₁ := isFiniteMeasure_of_le _ (Measure.sub_le (μ := μ₁.restrict B))
  have : IsFiniteMeasure α₂ := isFiniteMeasure_of_le _ (Measure.sub_le (μ := μ₂.restrict Bᶜ))
  have hi : ∀ (μ : Measure S) [IsFiniteMeasure μ], Integrable f μ := fun μ _ =>
    integrable_of_abs_le μ hf h1
  have hsplit1 : ∫ s, f s ∂μ₁ = ∫ s, f s ∂α₁ + ∫ s in B, f s ∂μ₂ + ∫ s in Bᶜ, f s ∂μ₁ := by
    rw [← integral_add_compl hB (hi μ₁), ← e1, integral_add_measure (hi α₁) (hi _)]
  have hsplit2 : ∫ s, f s ∂μ₂ = ∫ s in B, f s ∂μ₂ + (∫ s, f s ∂α₂ + ∫ s in Bᶜ, f s ∂μ₁) := by
    rw [← integral_add_compl hB (hi μ₂), ← e2, integral_add_measure (hi α₂) (hi _)]
  have hb : ∀ (α : Measure S) [IsFiniteMeasure α], |∫ s, f s ∂α| ≤ α.real univ := fun α _ => by
    have := norm_integral_le_of_norm_le_const (μ := α) (C := 1)
      (Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact h1 s)
    rwa [Real.norm_eq_abs, one_mul] at this
  have hm1 : α₁.real univ = μ₁.real B - μ₂.real B := by
    have := congrArg (fun μ : Measure S => (μ univ).toReal) e1
    simp only [Measure.coe_add, Pi.add_apply, Measure.restrict_apply_univ] at this
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp only [Measure.real]; linarith
  have hm2 : α₂.real univ = μ₂.real Bᶜ - μ₁.real Bᶜ := by
    have := congrArg (fun μ : Measure S => (μ univ).toReal) e2
    simp only [Measure.coe_add, Pi.add_apply, Measure.restrict_apply_univ] at this
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
    simp only [Measure.real]; linarith
  have hD1 : 0 ≤ μ₁.real B - μ₂.real B := by
    have := ENNReal.toReal_mono (measure_ne_top μ₁ B) (hpos B hB subset_rfl)
    simp only [Measure.real]; linarith
  have hD2 : μ₁.real Bᶜ - μ₂.real Bᶜ ≤ 0 := by
    have := ENNReal.toReal_mono (measure_ne_top μ₂ Bᶜ) (hneg Bᶜ hB.compl subset_rfl)
    simp only [Measure.real]; linarith
  have htv := abs_add_abs_compl_le μ₁ μ₂ hB
  rw [abs_of_nonneg hD1, abs_of_nonpos hD2] at htv
  have hb1 := hb α₁
  have hb2 := hb α₂
  rw [hsplit1, hsplit2]
  calc |∫ s, f s ∂α₁ + ∫ s in B, f s ∂μ₂ + ∫ s in Bᶜ, f s ∂μ₁ -
        (∫ s in B, f s ∂μ₂ + (∫ s, f s ∂α₂ + ∫ s in Bᶜ, f s ∂μ₁))|
      = |∫ s, f s ∂α₁ - ∫ s, f s ∂α₂| := by ring_nf
    _ ≤ |∫ s, f s ∂α₁| + |∫ s, f s ∂α₂| := abs_sub _ _
    _ ≤ tvDist μ₁ μ₂ := by linarith

/-- **Theorem 11.7.** `‖λₙ − λ‖ → 0` iff `λₙ → λ` strongly: `∫ f dλₙ → ∫ f dλ` for every bounded
measurable `f`, uniformly over `‖f‖ ≤ 1`. -/
theorem theorem_11_7 (ls : ℕ → Measure S) (l : Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] :
    Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) ↔ ConvStrong ls l := by
  have hnn := fun n => tvDist_nonneg (ls n) l
  constructor
  · intro h
    refine ⟨fun f hf ⟨C, hC⟩ => ?_, fun ε hε => ?_⟩
    · -- scale `f` into the unit ball
      set K := |C| + 1
      have hK : 0 < K := by positivity
      have hg : ∀ s, |f s / K| ≤ 1 := fun s => by
        rw [abs_div, abs_of_pos hK, div_le_one hK]
        exact (hC s).trans ((le_abs_self C).trans (by linarith))
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        ((h.const_mul K).trans_eq (by rw [mul_zero]) : Tendsto (fun n => K * tvDist (ls n) l)
          atTop (𝓝 0))
      have := abs_integral_sub_le_tvDist (ls n) l (hf.div_const K) hg
      rw [integral_div, integral_div, ← sub_div, abs_div, abs_of_pos hK, div_le_iff₀ hK] at this
      rw [Real.norm_eq_abs]; linarith
    · filter_upwards [(tendsto_zero_iff_of_nonneg hnn).1 h ε hε] with n hn f hf h1
      exact (abs_integral_sub_le_tvDist (ls n) l hf h1).trans_lt hn
  · rintro ⟨-, h⟩
    refine (theorem_11_6 ls l).2 fun ε hε => ?_
    filter_upwards [h ε hε] with n hn A hA
    have := hn (A.indicator 1) (measurable_one.indicator hA) fun s => by
      by_cases hs : s ∈ A <;> simp [hs]
    simpa [integral_indicator_one hA] using this

omit [MeasurableSpace S] in
/-- The tails `⋃_{i ≥ K} Aᵢ` of a disjoint sequence decrease to `∅`. -/
theorem iInter_tails_eq_empty {f : ℕ → Set S} (hd : Pairwise (Function.onFun Disjoint f)) :
    (⋂ K, ⋃ i, ⋃ (_ : K ≤ i), f i) = ∅ := by
  ext x
  simp only [mem_iInter, mem_iUnion, mem_empty_iff_false, iff_false, not_forall, not_exists]
  by_cases hx : ∃ i, x ∈ f i
  · obtain ⟨i, hi⟩ := hx
    refine ⟨i + 1, fun j hj hxj => ?_⟩
    exact Set.disjoint_left.1 (hd (show i ≠ j by omega)) hi hxj
  · push Not at hx
    exact ⟨0, fun j _ hj => hx j hj⟩

/-- **Lemma 11.8.** The probability measures are complete in the total variation norm: a Cauchy
sequence `λₙ` converges to the probability measure `λ(A) = lim λₙ(A)`. -/
theorem lemma_11_8 (ls : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ls n)]
    (hC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, tvDist (ls n) (ls m) < ε) :
    ∃ l : Measure S, IsProbabilityMeasure l ∧ Tendsto (fun n => tvDist (ls n) l) atTop (𝓝 0) := by
  -- (7): the measures of sets are uniformly Cauchy
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ A, MeasurableSet A →
      |(ls n).real A - (ls m).real A| < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC (2 * ε) (by positivity)
    exact ⟨N, fun n hn m hm A hA => by
      have := two_abs_le_tvDist (ls n) (ls m) hA; have := hN n hn m hm; linarith⟩
  have hcauchy : ∀ A, MeasurableSet A → CauchySeq fun n => (ls n).real A := fun A hA =>
    Metric.cauchySeq_iff.2 fun ε hε =>
      let ⟨N, hN⟩ := hunif ε hε
      ⟨N, fun m hm n hn => by rw [Real.dist_eq]; exact hN m hm n hn A hA⟩
  set F : Set S → ℝ := fun A => limUnder atTop fun n => (ls n).real A
  have hF : ∀ A, MeasurableSet A → Tendsto (fun n => (ls n).real A) atTop (𝓝 (F A)) :=
    fun A hA => (hcauchy A hA).tendsto_limUnder
  have hFu : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ A, MeasurableSet A → |(ls n).real A - F A| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hunif ε hε
    refine ⟨N, fun n hn A hA => ?_⟩
    have hlim : Tendsto (fun m => |(ls n).real A - (ls m).real A|) atTop
        (𝓝 |(ls n).real A - F A|) := ((hF A hA).const_sub _).abs
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => (hN n hn m hm A hA).le⟩)
  have hF0 : ∀ A, MeasurableSet A → 0 ≤ F A := fun A hA =>
    ge_of_tendsto (hF A hA) (Eventually.of_forall fun n => measureReal_nonneg)
  have hFe : F ∅ = 0 := tendsto_nhds_unique (hF ∅ MeasurableSet.empty) (by simp)
  have hFuniv : F univ = 1 := tendsto_nhds_unique (hF univ MeasurableSet.univ) (by simp)
  -- countable additivity
  have hsum : ∀ (f : ℕ → Set S), (∀ i, MeasurableSet (f i)) →
      Pairwise (Function.onFun Disjoint f) → HasSum (fun i => F (f i)) (F (⋃ i, f i)) := by
    intro f hf hd
    set T : ℕ → Set S := fun K => ⋃ i, ⋃ (_ : K ≤ i), f i
    have hT : ∀ K, MeasurableSet (T K) := fun K =>
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hf i
    -- for each `λₙ`: `λₙ(⋃ Aᵢ) = Σ_{i<K} λₙ(Aᵢ) + λₙ(T_K)`
    have hsplit : ∀ n K, (ls n).real (⋃ i, f i) =
        ∑ i ∈ Finset.range K, (ls n).real (f i) + (ls n).real (T K) := by
      intro n K
      have hU : (⋃ i, f i) = (⋃ i ∈ Finset.range K, f i) ∪ T K := by
        ext x
        simp only [mem_iUnion, mem_union, Finset.mem_range, T]
        constructor
        · rintro ⟨i, hi⟩
          by_cases hiK : i < K
          · exact Or.inl ⟨i, hiK, hi⟩
          · exact Or.inr ⟨i, by omega, hi⟩
        · rintro (⟨i, -, hi⟩ | ⟨i, -, hi⟩) <;> exact ⟨i, hi⟩
      have hdisj : Disjoint (⋃ i ∈ Finset.range K, f i) (T K) := by
        refine Set.disjoint_left.2 fun x hx hx' => ?_
        simp only [mem_iUnion, Finset.mem_range, T] at hx hx'
        obtain ⟨i, hi, hxi⟩ := hx
        obtain ⟨j, hj, hxj⟩ := hx'
        exact Set.disjoint_left.1 (hd (show i ≠ j by omega)) hxi hxj
      rw [hU, measureReal_union hdisj (hT K) (measure_ne_top _ _) (measure_ne_top _ _),
        measureReal_biUnion_finset (fun i _ j _ hij => hd hij) (fun i _ => hf i)
          (fun i _ => measure_ne_top _ _)]
    have hlimsplit : ∀ K, F (⋃ i, f i) = ∑ i ∈ Finset.range K, F (f i) + F (T K) := by
      intro K
      have h1 := hF _ (MeasurableSet.iUnion hf)
      have h2 : Tendsto (fun n => ∑ i ∈ Finset.range K, (ls n).real (f i) + (ls n).real (T K))
          atTop (𝓝 (∑ i ∈ Finset.range K, F (f i) + F (T K))) :=
        (tendsto_finsetSum _ fun i _ => hF _ (hf i)).add (hF _ (hT K))
      exact tendsto_nhds_unique (h1.congr fun n => hsplit n K) h2
    -- the tails tend to zero, uniformly
    have htail : Tendsto (fun K => F (T K)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_of_nonneg fun K => hF0 _ (hT K)]
      intro ε hε
      obtain ⟨N, hN⟩ := hFu (ε / 2) (by positivity)
      have hanti : Antitone T := fun K K' hKK' => iUnion_mono fun i =>
        iUnion_subset fun hi => subset_iUnion (fun _ : K ≤ i => f i) (hKK'.trans hi)
      have hlim := tendsto_measure_iInter_atTop (μ := ls N) (fun K => (hT K).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      rw [iInter_tails_eq_empty hd, measure_empty] at hlim
      have hlim' : Tendsto (fun K => (ls N).real (T K)) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
        simpa [Function.comp_def, Measure.real] using this
      filter_upwards [hlim'.eventually (gt_mem_nhds (half_pos hε))] with K hK
      have := hN N le_rfl (T K) (hT K)
      rw [abs_le] at this
      linarith
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => hF0 _ (hf i))]
    have := htail.const_sub (F (⋃ i, f i))
    rw [sub_zero] at this
    exact this.congr fun K => by rw [hlimsplit K]; ring
  -- the limit measure
  set l : Measure S := Measure.ofMeasurable (fun A _ => ENNReal.ofReal (F A)) (by simp [hFe])
    (fun f hf hd => by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hF0 _ (hf i)) (hsum f hf hd).summable,
        (hsum f hf hd).tsum_eq])
  have hl : ∀ A, MeasurableSet A → l.real A = F A := fun A hA => by
    rw [measureReal_def, Measure.ofMeasurable_apply A hA, ENNReal.toReal_ofReal (hF0 A hA)]
  have hlp : IsProbabilityMeasure l :=
    ⟨by rw [Measure.ofMeasurable_apply _ MeasurableSet.univ, hFuniv, ENNReal.ofReal_one]⟩
  refine ⟨l, hlp, (tendsto_zero_iff_of_nonneg fun n => tvDist_nonneg (ls n) l).2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hFu (ε / 4) (by positivity)
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have := tvDist_le_of_forall (ls n) l fun A hA => by rw [hl A hA]; exact hN n hn A hA
  linarith

end StokeyLucasPrescott.ConvergenceApplications
