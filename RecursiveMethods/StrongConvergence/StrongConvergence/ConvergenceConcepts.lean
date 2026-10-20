/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib

/-!
# Convergence concepts for measures

SLP §11.2, pp. 334–338. For probability measures `λₙ`, `λ`:

* `ConvSetwise`: `λₙ(A) → λ(A)` for every measurable `A` ((1), p. 335).
* `ConvIntegrals`: `∫ f dλₙ → ∫ f dλ` for every bounded measurable `f` ((2), p. 335).
* `ConvWeak`: `∫ f dλₙ → ∫ f dλ` for every bounded continuous `f` ((3), p. 337).
* `ConvStrong`: (2), uniformly over measurable `f` with `‖f‖ ≤ 1` (p. 337).

Results:

* **Exercise 11.2** (`ex_11_2`): (1) implies (2); so the two are equivalent (`convSetwise_iff`).
  The book's route is uniform approximation by simple functions. Here, for `0 ≤ f ≤ C`, the
  layer-cake formula `∫ f dλ = ∫₀^C λ{f > t} dt` and dominated convergence in `t` are used.
* The halving example (p. 336, `halving_not_setwise`, `halving_weak`): unit masses at `2⁻ⁿ`
  converge weakly to the unit mass at `0`, but converge setwise to no probability measure at all.
  The book takes `S = [0, 1]`; here `S = ℝ`, and the masses all lie in `[0, 1]`.
-/

namespace StokeyLucasPrescott.StrongConvergence

open MeasureTheory Filter Topology Set BoundedContinuousFunction

variable {S : Type*} [MeasurableSpace S]

/-- `λₙ` converges **setwise** to `λ` ((1), p. 335). -/
def ConvSetwise (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ A, MeasurableSet A → Tendsto (fun n => (ls n).real A) atTop (𝓝 (l.real A))

/-- `∫ f dλₙ → ∫ f dλ` for every bounded measurable `f` ((2), p. 335). -/
def ConvIntegrals (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S → ℝ, Measurable f → (∃ C, ∀ s, |f s| ≤ C) →
    Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- `λₙ` converges **weakly** to `λ` ((3), p. 337). -/
def ConvWeak [TopologicalSpace S] (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ∀ f : S →ᵇ ℝ, Tendsto (fun n => ∫ s, f s ∂ls n) atTop (𝓝 (∫ s, f s ∂l))

/-- `λₙ` converges **strongly** to `λ` (p. 337): (2) holds, uniformly over `‖f‖ ≤ 1`. -/
def ConvStrong (ls : ℕ → Measure S) (l : Measure S) : Prop :=
  ConvIntegrals ls l ∧ ∀ ε > 0, ∀ᶠ n in atTop, ∀ f : S → ℝ, Measurable f →
    (∀ s, |f s| ≤ 1) → |∫ s, f s ∂ls n - ∫ s, f s ∂l| < ε

/-- (2) implies (1): integrate indicator functions. -/
theorem convSetwise_of_convIntegrals {ls : ℕ → Measure S} {l : Measure S}
    (h : ConvIntegrals ls l) : ConvSetwise ls l := by
  intro A hA
  have := h (A.indicator 1) (measurable_one.indicator hA) ⟨1, fun s => by
    by_cases hs : s ∈ A <;> simp [hs]⟩
  simpa [integral_indicator_one hA] using this

/-- The layer-cake integrand `t ↦ λ{f > t}` is antitone, hence measurable. -/
theorem measurable_meas_lt (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) :
    Measurable fun t : ℝ => μ.real {a | t < f a} := by
  refine Antitone.measurable fun t t' htt' => ?_
  exact measureReal_mono fun a (ha : t' < f a) => lt_of_le_of_lt htt' ha

/-- **Exercise 11.2.** Setwise convergence of probability measures implies convergence of the
integrals of all bounded measurable functions. -/
theorem ex_11_2 {ls : ℕ → Measure S} {l : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] (h : ConvSetwise ls l) : ConvIntegrals ls l := by
  intro f hf ⟨C, hC⟩
  -- reduce to `g = f + C`, with `0 ≤ g ≤ 2C`
  set g := fun s => f s + C
  have hg0 : ∀ s, 0 ≤ g s := fun s => by have := (abs_le.1 (hC s)).1; simp only [g]; linarith
  have hg1 : ∀ s, g s ≤ 2 * C := fun s => by
    have := (abs_le.1 (hC s)).2; simp only [g]; linarith
  have hgm : Measurable g := hf.add_const C
  have hint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], Integrable g μ := fun μ _ =>
    Integrable.of_bound hgm.aestronglyMeasurable (2 * C) (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 s)]; exact hg1 s)
  have hfint : ∀ (μ : Measure S) [IsProbabilityMeasure μ], Integrable f μ := fun μ _ =>
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hC s)
  have hcake : ∀ (μ : Measure S) [IsProbabilityMeasure μ],
      ∫ s, f s ∂μ = (∫ t in Ioi 0, μ.real {a | t < g a}) - C := fun μ _ => by
    rw [← (hint μ).integral_eq_integral_meas_lt (Eventually.of_forall hg0), integral_add (hfint μ)
      (integrable_const C)]
    simp
  simp_rw [hcake]
  refine Tendsto.sub_const ?_ C
  -- dominated convergence in `t`
  refine tendsto_integral_of_dominated_convergence ((Ioc (0 : ℝ) (2 * C)).indicator 1)
    (fun n => (measurable_meas_lt (ls n) g).aestronglyMeasurable) ?_ (fun n => ?_) ?_
  · exact ((integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne)).restrict
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun t (ht : 0 < t) => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    by_cases htC : t ≤ 2 * C
    · rw [indicator_of_mem (show t ∈ Ioc 0 (2 * C) from ⟨ht, htC⟩), Pi.one_apply]
      exact measureReal_le_one
    · have : {a | t < g a} = ∅ := by
        ext a; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hg1 a).trans (le_of_lt (not_le.1 htC))
      rw [this, measureReal_empty]
      exact indicator_nonneg (fun _ _ => zero_le_one) t
  · exact Eventually.of_forall fun t => h _ (measurableSet_lt measurable_const hgm)

/-- (1) and (2) are equivalent for probability measures. -/
theorem convSetwise_iff {ls : ℕ → Measure S} {l : Measure S} [∀ n, IsProbabilityMeasure (ls n)]
    [IsProbabilityMeasure l] : ConvSetwise ls l ↔ ConvIntegrals ls l :=
  ⟨ex_11_2, convSetwise_of_convIntegrals⟩

/-- The deterministic system `s_{t+1} = s_t/2` started at `1`: unit masses at `2⁻ⁿ`. -/
noncomputable def halving (n : ℕ) : Measure ℝ := Measure.dirac ((1 / 2 : ℝ) ^ n)

/-- The halving example (p. 336): the unit masses at `2⁻ⁿ` converge setwise to no finite
measure. Each interval `(0, 2⁻ᵏ)` has `λₙ`-measure `1` for `n > k`, so a setwise limit would give
it measure `1`; but the intervals decrease to `∅`. -/
theorem halving_not_setwise (l : Measure ℝ) [IsFiniteMeasure l] : ¬ ConvSetwise halving l := by
  intro h
  set U : ℕ → Set ℝ := fun k => Ioo 0 ((1 / 2 : ℝ) ^ k)
  have hU1 : ∀ k, l (U k) = 1 := by
    intro k
    have hlim := h (U k) measurableSet_Ioo
    have hev : ∀ᶠ n in atTop, (halving n).real (U k) = 1 := by
      filter_upwards [eventually_gt_atTop k] with n hn
      have hmem : (1 / 2 : ℝ) ^ n ∈ U k :=
        ⟨by positivity, pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hn⟩
      rw [halving, measureReal_def, Measure.dirac_apply_of_mem hmem]
      rfl
    have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at this
    exact this
  have hanti : Antitone U := fun k k' hkk' => Ioo_subset_Ioo_right
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hkk')
  have hempty : (⋂ k, U k) = ∅ := by
    ext t
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall, U, mem_Ioo, not_and,
      not_lt]
    by_cases ht : 0 < t
    · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨k, fun _ => hk.le⟩
    · exact ⟨0, fun h0 => absurd h0 ht⟩
  have hlim := tendsto_measure_iInter_atTop (μ := l) (fun k => measurableSet_Ioo.nullMeasurableSet)
    hanti ⟨0, measure_ne_top l _⟩
  rw [hempty, measure_empty] at hlim
  have : (fun k => l (U k)) = fun _ => 1 := funext hU1
  rw [Function.comp_def, this] at hlim
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- The halving example (p. 337): the unit masses at `2⁻ⁿ` converge weakly to the unit mass at
`0`. -/
theorem halving_weak : ConvWeak halving (Measure.dirac 0) := by
  intro f
  simp only [halving, integral_dirac]
  exact (f.continuous.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    (by norm_num))

end StokeyLucasPrescott.StrongConvergence
