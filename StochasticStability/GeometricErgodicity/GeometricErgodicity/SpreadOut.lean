/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GeometricErgodicity.SmallSetsModels
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Spread-out random walks (MT §5.3.2, Proposition 5.3.1)

Meyn and Tweedie, §5.3.2, p. 107. A random walk on `ℝ` is spread out (RW2) if some convolution
power `Γ^{n∗}` is not singular with respect to Lebesgue measure (`IsSpreadOut`, Chapter 3).

* `exists_lebesgue_minorant`: a finite measure on `ℝ` that is not singular with respect to
  Lebesgue measure dominates `η μ_Leb|_E` for some `η > 0` and some bounded `E` with
  `μ_Leb(E) > 0`.
* `selfConv E u = μ_Leb(E ∩ (u − E))`, the self-convolution of `1_E`;
  `lintegral_selfConv`: `∫ selfConv E = μ_Leb(E)²`, so it is positive somewhere;
  `eventually_lt_selfConv`: it is lower semicontinuous (by continuity of translation in measure,
  Mathlib's `tendsto_measure_symmDiff_preimage_nhds_zero`). Together these replace Lemma D.4.3
  (continuity of `γ ∗ γ`) in the book's proof.
* `randomWalk_pow_two_mul_ge`: `P²ⁿ(x, B) ≥ η² ∫_B selfConv E (u − x) du`, the bound (5.28).
* **Proposition 5.3.1** (`proposition_5_3_1`, p. 107): for a spread-out random walk there are
  `β > 0`, an interval `[s, t]` and `ε > 0` such that `[−β, β]` is `ν₂ₙ`-small with
  `ν₂ₙ = ε μ_Leb|_{[s, t]}`.

**Corrections.** None.
-/

namespace MeynTweedie.GeometricErgodicity

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology symmDiff

/-! ### A Lebesgue minorant -/

/-- A finite measure on `ℝ` which is not singular with respect to Lebesgue measure dominates
`η μ_Leb|_E` for some `η > 0` and some bounded measurable `E` with `μ_Leb(E) > 0`. -/
theorem exists_lebesgue_minorant {μ : Measure ℝ} [IsFiniteMeasure μ] (h : ¬ μ ⟂ₘ volume) :
    ∃ E : Set ℝ, MeasurableSet E ∧ 0 < volume E ∧ volume E ≠ ∞ ∧
      ∃ η : ℝ≥0∞, 0 < η ∧ η • volume.restrict E ≤ μ := by
  set f := μ.rnDeriv volume with hf
  have hfm : Measurable f := Measure.measurable_rnDeriv μ volume
  have hwd : volume.withDensity f ≠ 0 := fun h0 => h ((Measure.withDensity_rnDeriv_eq_zero μ
    volume).1 h0)
  set L : ℕ → ℕ → Set ℝ := fun k R => {x | ((k : ℝ≥0∞) + 1)⁻¹ ≤ f x} ∩ Icc (-(R : ℝ)) R
  have hLm : ∀ k R, MeasurableSet (L k R) := fun k R =>
    (measurableSet_le measurable_const hfm).inter measurableSet_Icc
  obtain ⟨k, R, hkR⟩ : ∃ k R, 0 < volume (L k R) := by
    by_contra hc
    push Not at hc
    apply hwd
    have hnull : volume {x | f x ≠ 0} = 0 := by
      refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null fun k =>
        measure_iUnion_null fun R => nonpos_iff_eq_zero.1 (hc k R))
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hx
      obtain ⟨R, hR⟩ := exists_nat_ge |x|
      refine mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨R, ?_, ?_⟩⟩
      · refine le_trans ?_ hk.le
        change ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹
        gcongr
        exact le_self_add
      · rw [mem_Icc, ← abs_le]; exact hR
    have hae : f =ᵐ[volume] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      simpa using hnull
    rw [withDensity_congr_ae hae, withDensity_zero]
  refine ⟨L k R, hLm k R, hkR, ne_top_of_le_ne_top (by simp [Real.volume_Icc])
    (measure_mono inter_subset_right), ((k : ℝ≥0∞) + 1)⁻¹, ENNReal.inv_pos.2 (by simp),
    Measure.le_intro fun B hB _ => ?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  calc ((k : ℝ≥0∞) + 1)⁻¹ * volume (B ∩ L k R) = ∫⁻ _ in B ∩ L k R, ((k : ℝ≥0∞) + 1)⁻¹ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in B ∩ L k R, f x := setLIntegral_mono' (hB.inter (hLm k R)) fun x hx => hx.2.1
    _ ≤ ∫⁻ x in B, f x := lintegral_mono_set inter_subset_left
    _ = volume.withDensity f B := (withDensity_apply _ hB).symm
    _ ≤ μ B := Measure.withDensity_rnDeriv_le μ volume B

/-! ### The self-convolution of an indicator -/

/-- `selfConv E u = μ_Leb(E ∩ (u − E)) = ∫ 1_E(v) 1_E(u − v) dv`. -/
noncomputable def selfConv (E : Set ℝ) (u : ℝ) : ℝ≥0∞ := volume (E ∩ {v | u - v ∈ E})

/-- The integrand form of `selfConv`. -/
theorem selfConv_eq_lintegral {E : Set ℝ} (hE : MeasurableSet E) (u : ℝ) :
    selfConv E u = ∫⁻ v, E.indicator 1 v * E.indicator 1 (u - v) := by
  have hm : MeasurableSet {v | u - v ∈ E} := (measurable_const.sub measurable_id) hE
  rw [selfConv, ← lintegral_indicator_one (hE.inter hm)]
  refine lintegral_congr fun v => ?_
  by_cases h1 : v ∈ E <;> by_cases h2 : u - v ∈ E <;> simp [h1, h2, indicator]

/-- `∫ selfConv E = μ_Leb(E)²`. -/
theorem lintegral_selfConv {E : Set ℝ} (hE : MeasurableSet E) :
    ∫⁻ u, selfConv E u = volume E * volume E := by
  simp_rw [selfConv_eq_lintegral hE]
  have hmeas : Measurable (Function.uncurry fun (u v : ℝ) =>
      E.indicator (1 : ℝ → ℝ≥0∞) v * E.indicator 1 (u - v)) :=
    ((measurable_one.indicator hE).comp measurable_snd).mul
      ((measurable_one.indicator hE).comp (measurable_fst.sub measurable_snd))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h1 : ∀ v, ∫⁻ u, E.indicator (1 : ℝ → ℝ≥0∞) v * E.indicator 1 (u - v) =
      E.indicator 1 v * volume E := fun v => by
    rw [lintegral_const_mul' _ _ (by by_cases hv : v ∈ E <;> simp [hv]),
      lintegral_sub_right_eq_self (fun u => E.indicator (1 : ℝ → ℝ≥0∞) u) v,
      lintegral_indicator_one hE]
  simp_rw [h1]
  rw [lintegral_mul_const _ (measurable_one.indicator hE), lintegral_indicator_one hE]

/-- `selfConv E` is lower semicontinuous: if `c < selfConv E u₀` then `c < selfConv E u` for all
`u` near `u₀`. This follows from the continuity of translation in measure. -/
theorem eventually_lt_selfConv {E : Set ℝ} (hE : MeasurableSet E) (hfin : volume E ≠ ∞)
    {u₀ : ℝ} {c : ℝ≥0∞} (hc : c < selfConv E u₀) : ∀ᶠ u in 𝓝 u₀, c < selfConv E u := by
  set g : ℝ → C(ℝ, ℝ) := ⇑(ContinuousMap.curry ⟨fun q : ℝ × ℝ => q.2 - q.1, by fun_prop⟩)
    with hg
  set S : Set ℝ := {x | -x ∈ E} with hS
  have hSm : MeasurableSet S := measurable_neg hE
  have hSfin : volume S ≠ ∞ := by
    rw [hS, show {x : ℝ | -x ∈ E} = -E from rfl, Measure.measure_neg]
    exact hfin
  have hpre : ∀ u, ⇑(g u) ⁻¹' S = {v | u - v ∈ E} := fun u => by
    ext v
    simp [hg, hS]
  have hfg : Tendsto g (𝓝 u₀) (𝓝 (g u₀)) := (ContinuousMap.curry _).continuous.tendsto u₀
  have hmp : ∀ u, MeasurePreserving (g u) volume volume := fun u =>
    measurePreserving_sub_right volume u
  have hvol := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume) hfg
    (Eventually.of_forall hmp) (hmp u₀) hSm.nullMeasurableSet hSfin
  have hε : 0 < selfConv E u₀ - c := tsub_pos_of_lt hc
  filter_upwards [hvol.eventually (gt_mem_nhds hε)] with u hu
  have hle : selfConv E u₀ ≤ selfConv E u + volume ((g u ⁻¹' S) ∆ (g u₀ ⁻¹' S)) := by
    rw [selfConv, selfConv, ← hpre, ← hpre]
    calc volume (E ∩ g u₀ ⁻¹' S)
        ≤ volume ((E ∩ g u ⁻¹' S) ∪ ((g u ⁻¹' S) ∆ (g u₀ ⁻¹' S))) := measure_mono fun v hv => by
          by_cases h : v ∈ g u ⁻¹' S
          · exact Or.inl ⟨hv.1, h⟩
          · exact Or.inr (Or.inr ⟨hv.2, h⟩)
      _ ≤ _ := measure_union_le _ _
  by_contra hcon
  push Not at hcon
  have : selfConv E u₀ < selfConv E u₀ :=
    calc selfConv E u₀ ≤ c + volume ((g u ⁻¹' S) ∆ (g u₀ ⁻¹' S)) :=
          hle.trans (add_le_add_left hcon _)
      _ < c + (selfConv E u₀ - c) := ENNReal.add_lt_add_left hc.ne_top hu
      _ = selfConv E u₀ := add_tsub_cancel_of_le hc.le
  exact lt_irrefl _ this

/-! ### The bound (5.28) -/

/-- The bound (5.28), MT p. 107: if `Γ^{n∗} ≥ η μ_Leb|_E`, then
`P²ⁿ(x, B) ≥ η² ∫_B μ_Leb(E ∩ (u − x − E)) du`. -/
theorem randomWalk_pow_two_mul_ge (Γ : Measure ℝ) [IsProbabilityMeasure Γ] {n : ℕ} {E : Set ℝ}
    (hE : MeasurableSet E) {η : ℝ≥0∞} (hle : η • volume.restrict E ≤ convPow Γ n) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    η * η * ∫⁻ u in B, selfConv E (u - x) ≤ (randomWalkKernel Γ ^ (n + n)) x B := by
  have iE : Measurable (E.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hE
  have iB : Measurable (B.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hB
  -- `F(y) = μ_Leb(E ∩ (B − y))`
  set F : ℝ → ℝ≥0∞ := fun y => ∫⁻ w, E.indicator 1 w * B.indicator 1 (y + w) with hF
  have hFm : Measurable F := by
    refine Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ =>
      E.indicator (1 : ℝ → ℝ≥0∞) p.2 * B.indicator 1 (p.1 + p.2)) ?_
    exact (iE.comp measurable_snd).mul (iB.comp (measurable_fst.add measurable_snd))
  have hy : ∀ y, η * F y ≤ (randomWalkKernel Γ ^ n) y B := fun y => by
    have hpre : MeasurableSet {w | y + w ∈ B} := (measurable_const_add y) hB
    rw [randomWalkKernel_pow_apply, Measure.map_apply (measurable_const_add y) hB]
    have h1 := hle {w | y + w ∈ B}
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hpre] at h1
    refine le_trans (le_of_eq ?_) h1
    rw [hF, ← lintegral_indicator_one (hpre.inter hE)]
    congr 1
    refine lintegral_congr fun w => ?_
    by_cases h1 : w ∈ E <;> by_cases h2 : y + w ∈ B <;> simp [h1, h2, indicator]
  -- integrate against `Pⁿ(x, ·) ≥ η μ_Leb|_E` shifted by `x`
  have hstep : η * ∫⁻ v in E, η * F (x + v) ≤ ∫⁻ y, (randomWalkKernel Γ ^ n) y B
      ∂(randomWalkKernel Γ ^ n) x := by
    rw [randomWalkKernel_pow_apply, lintegral_map (Kernel.measurable_coe _ hB)
      (measurable_const_add x)]
    calc η * ∫⁻ v in E, η * F (x + v) = ∫⁻ v, η * F (x + v) ∂(η • volume.restrict E) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ∫⁻ v, η * F (x + v) ∂convPow Γ n := lintegral_mono' hle le_rfl
      _ ≤ ∫⁻ v, (randomWalkKernel Γ ^ n) (x + v) B ∂convPow Γ n :=
          lintegral_mono fun v => hy (x + v)
  -- the change of variables `u = x + v + w`
  have hcv : ∫⁻ v in E, F (x + v) = ∫⁻ u in B, selfConv E (u - x) := by
    have h1 : ∀ v, F (x + v) = ∫⁻ u, E.indicator 1 (u - (x + v)) * B.indicator 1 u := fun v => by
      rw [hF]
      simp only
      rw [← lintegral_sub_right_eq_self (fun w => E.indicator (1 : ℝ → ℝ≥0∞) w *
        B.indicator 1 (x + v + w)) (x + v)]
      simp only [add_sub_cancel]
    rw [← lintegral_indicator hE]
    have h2 : ∀ v, E.indicator (fun v => F (x + v)) v =
        ∫⁻ u, E.indicator 1 v * (E.indicator 1 (u - (x + v)) * B.indicator 1 u) := fun v => by
      rw [lintegral_const_mul' _ _ (by by_cases hv : v ∈ E <;> simp [hv]), ← h1]
      by_cases hv : v ∈ E <;> simp [hv]
    simp_rw [h2]
    have hmeas : Measurable (Function.uncurry fun (v u : ℝ) =>
        E.indicator (1 : ℝ → ℝ≥0∞) v * (E.indicator 1 (u - (x + v)) * B.indicator 1 u)) :=
      (iE.comp measurable_fst).mul ((iE.comp (measurable_snd.sub
        (measurable_const.add measurable_fst))).mul (iB.comp measurable_snd))
    rw [lintegral_lintegral_swap hmeas.aemeasurable, ← lintegral_indicator hB]
    refine lintegral_congr fun u => ?_
    by_cases hu : u ∈ B
    · have hR : B.indicator (fun u => selfConv E (u - x)) u = selfConv E (u - x) :=
        indicator_of_mem hu _
      rw [hR, selfConv_eq_lintegral hE]
      refine lintegral_congr fun v => ?_
      rw [indicator_of_mem hu, Pi.one_apply, mul_one, show u - (x + v) = u - x - v by ring]
    · rw [indicator_of_notMem hu]
      simp [hu]
  rw [Kernel.pow_add_apply_eq_lintegral _ n n x hB]
  calc η * η * ∫⁻ u in B, selfConv E (u - x) = η * ∫⁻ v in E, η * F (x + v) := by
        rw [lintegral_const_mul η (f := fun v => F (x + v)) (hFm.comp (measurable_const_add x)),
          hcv, mul_assoc]
    _ ≤ _ := hstep

/-! ### Proposition 5.3.1 -/

/-- **Proposition 5.3.1** (MT p. 107). If the random walk is spread out, with `Γ^{n∗}` not
singular with respect to Lebesgue measure, there are `β > 0`, an interval `[s, t]` and `ε > 0`
such that `C_β = [−β, β]` is `ν₂ₙ`-small with `ν₂ₙ = ε μ_Leb|_{[s, t]}`. -/
theorem proposition_5_3_1 (Γ : Measure ℝ) [IsProbabilityMeasure Γ] (h : IsSpreadOut Γ) :
    ∃ n, 1 ≤ n ∧ ∃ β : ℝ, 0 < β ∧ ∃ s t : ℝ, s < t ∧ ∃ ε : ℝ≥0∞, 0 < ε ∧
      IsSmallSet (randomWalkKernel Γ) (2 * n) (ε • volume.restrict (Icc s t)) (Icc (-β) β) := by
  obtain ⟨n, hn, hns⟩ := h
  have : IsFiniteMeasure (convPow Γ n) := by unfold convPow; infer_instance
  obtain ⟨E, hEm, hEpos, hEfin, η, hη, hle⟩ := exists_lebesgue_minorant hns
  -- a point where the self-convolution is positive
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, 0 < selfConv E u₀ := by
    by_contra hc
    push Not at hc
    have h0 : ∫⁻ u, selfConv E u = 0 := by
      rw [lintegral_congr fun u => nonpos_iff_eq_zero.1 (hc u), lintegral_zero]
    rw [lintegral_selfConv hEm] at h0
    exact (ENNReal.mul_pos hEpos.ne' hEpos.ne').ne' h0
  have hcfin : selfConv E u₀ ≠ ⊤ := ne_top_of_le_ne_top hEfin (measure_mono inter_subset_left)
  have hc0 : 0 < selfConv E u₀ / 2 := ENNReal.div_pos hu₀.ne' (by simp)
  have hclt : selfConv E u₀ / 2 < selfConv E u₀ := ENNReal.half_lt_self hu₀.ne' hcfin
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_lt_selfConv hEm hEfin hclt)
  refine ⟨n, hn, r / 4, by positivity, u₀ - r / 4, u₀ + r / 4, by linarith,
    η * η * (selfConv E u₀ / 2), ENNReal.mul_pos (ENNReal.mul_pos hη.ne' hη.ne').ne' hc0.ne',
    measurableSet_Icc, by omega, smul_measure_ne_zero ?_ (ENNReal.mul_pos (ENNReal.mul_pos
      hη.ne' hη.ne').ne' hc0.ne').ne', fun x hx => Measure.le_intro fun B hB _ => ?_⟩
  · rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le]
    linarith
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB, two_mul]
  refine le_trans ?_ (randomWalk_pow_two_mul_ge Γ hEm hle x hB)
  rw [mul_assoc]
  gcongr
  calc selfConv E u₀ / 2 * volume (B ∩ Icc (u₀ - r / 4) (u₀ + r / 4))
      = ∫⁻ _ in B ∩ Icc (u₀ - r / 4) (u₀ + r / 4), selfConv E u₀ / 2 := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ u in B ∩ Icc (u₀ - r / 4) (u₀ + r / 4), selfConv E (u - x) := by
        refine setLIntegral_mono' (hB.inter measurableSet_Icc) fun u hu => (hball ?_).le
        rw [Real.dist_eq]
        have h1 := hu.2.1
        have h2 := hu.2.2
        have h3 := hx.1
        have h4 := hx.2
        rw [abs_lt]
        constructor <;> linarith
    _ ≤ ∫⁻ u in B, selfConv E (u - x) := lintegral_mono_set inter_subset_left

end MeynTweedie.GeometricErgodicity
