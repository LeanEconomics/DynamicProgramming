/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearDecisionProcesses.LDPOptimality
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Feller properties

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §6.1.1 (pp. 185–187).

* `shockKernel F φ`: the stochastic kernel `z ↦ law of F(z, W)`, `W ∼ φ`, with
  `∫ h dK(z) = ∫ h(F(z, w)) φ(dw)`.
* **Example 6.1.1**: `(Kh)(x, a) = β(x, a) ∫ h(F(x, a, w)) φ(dw)` is weak Feller when `β` is
  continuous on `G` and `(x, a) ↦ F(x, a, w)` is continuous on `G` for `φ`-almost all `w`.
* **Lemma 6.1.1**: with a density kernel `p` (`∫ p(x, a, x')μ(dx') = 1`) continuous in `(x, a)` for
  `μ`-almost all `x'`, `(Kh)(x, a) = β(x, a) ∫ h(x')p(x, a, x')μ(dx')` is strong Feller. Scheffé's
  lemma (`scheffe`) is proved along the way: `∫ |p(z, ·) − p(z₀, ·)| dμ → 0` as `z → z₀` in `G`.
* **Example 6.1.2**: on a group with a translation-invariant measure,
  `(Kh)(x, a) = β(x) ∫ h(g(x, a) + w)φ(w) dw` with a continuous density `φ` is strong Feller.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.LinearDecisionProcesses

/-! ### Kernels driven by shocks -/

theorem measurable_section {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] {F : Z → W → X} (hF : Measurable (uncurry F)) (z : Z) :
    Measurable (F z) :=
  hF.comp measurable_prodMk_left

/-- The kernel `z ↦ law of F(z, W)` with `W ∼ φ`. -/
noncomputable def shockKernel {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] : Kernel Z X where
  toFun z := φ.map (F z)
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    have heq : (fun z => φ.map (F z) s) = fun z => φ (Prod.mk z ⁻¹' (uncurry F ⁻¹' s)) :=
      funext fun z => Measure.map_apply (measurable_section hF z) hs
    rw [heq]
    exact measurable_measure_prodMk_left (hF hs)

theorem shockKernel_apply {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] (z : Z) : shockKernel F hF φ z = φ.map (F z) := rfl

theorem shockKernel_isMarkov {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] : IsMarkovKernel (shockKernel F hF φ) :=
  ⟨fun z => by
    rw [shockKernel_apply]
    infer_instance⟩

/-- `∫ h dK(z) = ∫ h(F(z, w)) φ(dw)`. -/
theorem integral_shockKernel {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace X] (F : Z → W → X) (hF : Measurable (uncurry F)) (φ : Measure W)
    [IsProbabilityMeasure φ] {h : X → ℝ} (hh : Measurable h) (z : Z) :
    ∫ x, h x ∂(shockKernel F hF φ z) = ∫ w, h (F z w) ∂φ := by
  rw [shockKernel_apply, integral_map (measurable_section hF z).aemeasurable
    hh.aestronglyMeasurable]

variable {Y W : Type*} [TopologicalSpace Y] [MeasurableSpace W]

/-- **Example 6.1.1** (p. 186): if `β` is continuous on `G` and `(x, a) ↦ F(x, a, w)` is continuous
on `G` for `φ`-almost all `w`, then `(x, a) ↦ β(x, a) ∫ h(F(x, a, w)) φ(dw)` is continuous on `G`
for every bounded continuous `h`: the kernel is weak Feller. -/
theorem example_6_1_1 [FirstCountableTopology Y] {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X]
    [OpensMeasurableSpace X] {G : Set Y} {β : Y → ℝ} (hβ : ContinuousOn β G) {F : Y → W → X}
    {φ : Measure W} [IsProbabilityMeasure φ] (hFm : ∀ z, Measurable (F z))
    (hFc : ∀ᵐ w ∂φ, ContinuousOn (fun z => F z w) G) {h : X → ℝ} (hc : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) :
    ContinuousOn (fun z => β z * ∫ w, h (F z w) ∂φ) G := by
  refine hβ.mul (continuousOn_of_dominated (bound := fun _ => C)
    (fun z _ => (hc.measurable.comp (hFm z)).aestronglyMeasurable)
    (fun z _ => Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hC _)
    (integrable_const C) ?_)
  filter_upwards [hFc] with w hw
  exact hc.comp_continuousOn hw

/-- **Scheffé's lemma** (p. 365) for a density kernel: if `∫ p(z, ·) dμ = 1` on `G` and
`z ↦ p(z, x')` is continuous on `G` for `μ`-almost all `x'`, then
`∫ |p(z, ·) − p(z₀, ·)| dμ → 0` as `z → z₀` within `G`. -/
theorem scheffe [FirstCountableTopology Y] {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {G : Set Y} {p : Y → X → ℝ} (hp0 : ∀ z x, 0 ≤ p z x) (hp1 : ∀ z ∈ G, ∫ x, p z x ∂μ = 1)
    (hpc : ∀ᵐ x ∂μ, ContinuousOn (fun z => p z x) G) {z₀ : Y} (hz₀ : z₀ ∈ G) :
    Tendsto (fun z => ∫ x, |p z x - p z₀ x| ∂μ) (𝓝[G] z₀) (𝓝 0) := by
  have hint : ∀ z ∈ G, Integrable (p z) μ := fun z hz =>
    Integrable.of_integral_ne_zero (by rw [hp1 z hz]; exact one_ne_zero)
  -- `∫ |p_z − p_{z₀}| = 2 ∫ (p_{z₀} − p_z)⁺`
  have hkey : ∀ z ∈ G, ∫ x, |p z x - p z₀ x| ∂μ = 2 * ∫ x, max (p z₀ x - p z x) 0 ∂μ := by
    intro z hz
    have hi1 : Integrable (fun x => p z₀ x - p z x) μ := (hint z₀ hz₀).sub (hint z hz)
    have hi2 : Integrable (fun x => max (p z₀ x - p z x) 0) μ := hi1.pos_part
    have habs : ∀ x, |p z x - p z₀ x| = 2 * max (p z₀ x - p z x) 0 - (p z₀ x - p z x) := by
      intro x
      rcases le_total (p z₀ x) (p z x) with h | h
      · rw [max_eq_right (sub_nonpos.2 h), abs_of_nonneg (sub_nonneg.2 h)]
        ring
      · rw [max_eq_left (sub_nonneg.2 h), abs_of_nonpos (sub_nonpos.2 h)]
        ring
    simp_rw [habs]
    rw [integral_sub (hi2.const_mul 2) hi1, integral_const_mul, integral_sub (hint z₀ hz₀)
      (hint z hz), hp1 z hz, hp1 z₀ hz₀]
    ring
  have hlim : Tendsto (fun z => ∫ x, max (p z₀ x - p z x) 0 ∂μ) (𝓝[G] z₀) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[G] z₀)
      (F := fun z x => max (p z₀ x - p z x) 0) (f := fun _ => (0 : ℝ)) (p z₀)
      (eventually_nhdsWithin_of_forall fun z hz =>
        ((hint z₀ hz₀).sub (hint z hz)).pos_part.aestronglyMeasurable)
      (eventually_nhdsWithin_of_forall fun z _ => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hp0 z x]) (hp0 z₀ x))
      (hint z₀ hz₀) (by
        filter_upwards [hpc] with x hx
        have h1 := ((hx z₀ hz₀).tendsto)
        have h2 := (tendsto_const_nhds (x := p z₀ x)).sub h1
        rw [sub_self] at h2
        have h3 := h2.max (tendsto_const_nhds (x := (0 : ℝ)))
        rwa [max_self] at h3)
    simpa using this
  have := hlim.const_mul 2
  rw [mul_zero] at this
  exact this.congr' (eventually_nhdsWithin_of_forall fun z hz => (hkey z hz).symm)

/-- **Lemma 6.1.1** (p. 187): if `β` is continuous on `G` and `p` is a density kernel with respect
to `μ` such that `(x, a) ↦ p(x, a, x')` is continuous on `G` for `μ`-almost all `x'`, then
`(Kh)(x, a) = β(x, a) ∫ h(x')p(x, a, x')μ(dx')` is continuous on `G` for every bounded measurable
`h`: `K` is strong Feller. -/
theorem lemma_6_1_1 [FirstCountableTopology Y] {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {G : Set Y} {β : Y → ℝ} (hβ : ContinuousOn β G) {p : Y → X → ℝ} (hp0 : ∀ z x, 0 ≤ p z x)
    (hp1 : ∀ z ∈ G, ∫ x, p z x ∂μ = 1) (hpc : ∀ᵐ x ∂μ, ContinuousOn (fun z => p z x) G)
    {h : X → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ContinuousOn (fun z => β z * ∫ x, h x * p z x ∂μ) G := by
  refine hβ.mul fun z₀ hz₀ => ?_
  have hint : ∀ z ∈ G, Integrable (p z) μ := fun z hz =>
    Integrable.of_integral_ne_zero (by rw [hp1 z hz]; exact one_ne_zero)
  have hhint : ∀ z ∈ G, Integrable (fun x => h x * p z x) μ := fun z hz =>
    (hint z hz).bdd_mul hm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have hs := scheffe hp0 hp1 hpc hz₀
  refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ (by simpa using hs.const_mul C))
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [← integral_sub (hhint z hz) (hhint z₀ hz₀)]
  calc ‖∫ x, (h x * p z x - h x * p z₀ x) ∂μ‖ ≤ ∫ x, C * |p z x - p z₀ x| ∂μ :=
        norm_integral_le_of_norm_le (((hint z hz).sub (hint z₀ hz₀)).abs.const_mul C)
          (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
            exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _))
    _ = C * ∫ x, |p z x - p z₀ x| ∂μ := integral_const_mul _ _

/-- **Example 6.1.2** (p. 187): on a group `X` with a translation-invariant measure `μ` (Lebesgue
measure on `ℝᵐ`), if `β` and `g` are continuous on `G` and `φ` is a continuous density, then
`(Kh)(x, a) = β(x, a) ∫ h(g(x, a) + w)φ(w)μ(dw)` is continuous on `G` for every bounded measurable
`h`: `K` is strong Feller (change of variable `x' = g(x, a) + w` and Lemma 6.1.1). -/
theorem example_6_1_2 [FirstCountableTopology Y] {X : Type*} [NormedAddCommGroup X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.IsAddRightInvariant] {G : Set Y}
    {β : Y → ℝ} (hβ : ContinuousOn β G) {g : Y → X} (hg : ContinuousOn g G) {φ : X → ℝ}
    (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∫ x, φ x ∂μ = 1) {h : X → ℝ}
    (hm : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) :
    ContinuousOn (fun z => β z * ∫ w, h (g z + w) * φ w ∂μ) G := by
  have heq : ∀ z, ∫ w, h (g z + w) * φ w ∂μ = ∫ x, h x * φ (x - g z) ∂μ := fun z => by
    rw [← integral_sub_right_eq_self (μ := μ) (fun w => h (g z + w) * φ w) (g z)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change h (g z + (x - g z)) * φ (x - g z) = h x * φ (x - g z)
    rw [add_sub_cancel]
  simp_rw [heq]
  exact lemma_6_1_1 hβ (p := fun z x => φ (x - g z)) (fun _ _ => hφ0 _)
    (fun z _ => by rw [integral_sub_right_eq_self (fun x => φ x) (g z)]; exact hφ1)
    (Eventually.of_forall fun x => hφc.comp_continuousOn (continuousOn_const.sub hg)) hm hC

end SargentStachurski.LinearDecisionProcesses
