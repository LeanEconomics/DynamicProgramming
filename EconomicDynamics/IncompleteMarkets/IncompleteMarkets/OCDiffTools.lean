/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Two facts about concave functions of one variable

Copied from `EconomicDynamics/FiniteHorizonDP` (module `OCDiffTools`), namespace renamed.

Tools for Theorem 6.4.4 (Miao, §6.4, pp. 178–180).

* `oc_hasDerivAt_integral_concave`: **differentiation under `∫ Q(z, dz′)`**. If each
  `F(·, z′)` is concave on a ball around `x₀`, bounded there by a constant, and differentiable
  at `x₀`, then `∫ F(·, z′) μ(dz′)` is differentiable at `x₀` with derivative
  `∫ ∂F(x₀, z′)/∂x μ(dz′)`. A concave function bounded by `C` on `B(x₀, r)` is `4C/r`-Lipschitz
  on `B(x₀, r/2)` (Mathlib's `ConcaveOn.lipschitzOnWith_of_abs_le`), which gives the domination;
  the derivative is measurable as a limit of difference quotients.
* `oc_continuousOn_deriv_of_concave`: a concave function differentiable on an open set has a
  **continuous derivative** there. For `y` near `x₀` the derivative `f′(y)` lies between
  `f′(x₀)` and the slope of `f` between `y` and `2y − x₀`, which tends to `f′(x₀)`.
-/

namespace Miao.IncompleteMarkets

open MeasureTheory Filter Topology Metric

/-- **Differentiation under the integral sign for concave integrands.** Let `μ` be a probability
measure, each `F(·, z)` concave on `B(x₀, r)` with `|F(y, z)| ≤ C` there, each `F(y, ·)`
integrable for `y ∈ B(x₀, r)`, and `∂F(x₀, z)/∂x = F′(z)`. Then `F′` is integrable and
`x ↦ ∫ F(x, z) μ(dz)` has derivative `∫ F′ dμ` at `x₀`. -/
theorem oc_hasDerivAt_integral_concave {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    [IsProbabilityMeasure μ] {F : ℝ → Z → ℝ} {F' : Z → ℝ} {x₀ r C : ℝ} (hr : 0 < r)
    (hconc : ∀ z, ConcaveOn ℝ (ball x₀ r) fun y => F y z)
    (hbd : ∀ y ∈ ball x₀ r, ∀ z, |F y z| ≤ C)
    (hint : ∀ y ∈ ball x₀ r, Integrable (F y) μ)
    (hd : ∀ z, HasDerivAt (fun y => F y z) (F' z) x₀) :
    Integrable F' μ ∧ HasDerivAt (fun y => ∫ z, F y z ∂μ) (∫ z, F' z ∂μ) x₀ := by
  set K : ℝ := 2 * C / (r / 2)
  have hlip : ∀ z, LipschitzOnWith (Real.nnabs K) (fun y => F y z) (ball x₀ (r / 2)) := by
    intro z
    have h := (hconc z).lipschitzOnWith_of_abs_le (ε := r / 2) (by positivity)
      fun y hy => hbd y hy z
    rw [show r - r / 2 = r / 2 by ring] at h
    refine h.weaken ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal', Real.coe_nnabs]
    exact max_le (le_abs_self K) (abs_nonneg K)
  -- the derivative is measurable: a limit of difference quotients
  set δ : ℕ → ℝ := fun n => r / ((n : ℝ) + 2)
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlt : ∀ n, δ n < r := fun n => by
    have : (1 : ℝ) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (div_lt_iff₀ (by positivity)).2 (by nlinarith)
  have hδmem : ∀ n, x₀ + δ n ∈ ball x₀ r := fun n => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos (hδpos n)]
    exact hδlt n
  have hδlim : Tendsto (fun n => x₀ + δ n) atTop (𝓝[≠] x₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto δ atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        exact h1.const_div_atTop r
      simpa using (tendsto_const_nhds (x := x₀)).add this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith [hδpos n]
  have hF'm : AEStronglyMeasurable F' μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n z => slope (fun y => F y z) x₀ (x₀ + δ n)) (fun n => ?_)
      (ae_of_all _ fun z => (hasDerivAt_iff_tendsto_slope.1 (hd z)).comp hδlim)
    simp only [slope_def_field]
    exact (((hint _ (hδmem n)).sub (hint x₀ (mem_ball_self hr))).div_const _).aestronglyMeasurable
  exact hasDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ (half_pos hr))
    (Eventually.mono (ball_mem_nhds x₀ hr) fun y hy => (hint y hy).aestronglyMeasurable)
    (hint x₀ (mem_ball_self hr)) hF'm (ae_of_all _ hlip) (integrable_const K) (ae_of_all _ hd)

/-- The slope of `f` between `y` and `2y − x₀`, written through slopes from `x₀`. -/
theorem oc_slope_double (f : ℝ → ℝ) {x₀ y : ℝ} (hy : y ≠ x₀) :
    slope f y (2 * y - x₀) = 2 * slope f x₀ (2 * y - x₀) - slope f x₀ y := by
  have h1 : y - x₀ ≠ 0 := sub_ne_zero.2 hy
  have h2 : 2 * y - x₀ - x₀ ≠ 0 := by
    intro h; apply h1; linarith
  have h3 : 2 * y - x₀ - y ≠ 0 := by
    intro h; apply h1; linarith
  simp only [slope_def_field]
  field_simp
  ring

/-- **A concave function differentiable on an open set is continuously differentiable there.** -/
theorem oc_continuousOn_deriv_of_concave {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U)
    (hc : ConcaveOn ℝ U f) (hd : ∀ x ∈ U, DifferentiableAt ℝ f x) :
    ContinuousOn (deriv f) U := by
  intro x₀ hx₀
  refine ContinuousAt.continuousWithinAt ?_
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  set d := deriv f x₀
  have hslope : Tendsto (slope f x₀) (𝓝[≠] x₀) (𝓝 d) :=
    hasDerivAt_iff_tendsto_slope.1 (hd x₀ hx₀).hasDerivAt
  have hmap : Tendsto (fun y => 2 * y - x₀) (𝓝[≠] x₀) (𝓝[≠] x₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun y : ℝ => 2 * y - x₀) (𝓝 x₀) (𝓝 (2 * x₀ - x₀)) :=
        ((continuous_const.mul continuous_id).sub continuous_const).tendsto x₀
      rw [show 2 * x₀ - x₀ = x₀ by ring] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
      intro h; apply hy; linarith
  have hq : Tendsto (fun y => slope f y (2 * y - x₀)) (𝓝[≠] x₀) (𝓝 d) := by
    have := ((hslope.comp hmap).const_mul 2).sub hslope
    rw [show 2 * d - d = d by ring] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (oc_slope_double f hy).symm
  -- `f′(y)` lies between `f′(x₀)` and the slope from `y` to `2y − x₀`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hanti := hc.antitoneOn_deriv hd
  have hnear : ∀ᶠ y in 𝓝[≠] x₀, |deriv f y - d| ≤ |slope f y (2 * y - x₀) - d| := by
    have hb : ball x₀ (ε / 2) ∈ 𝓝[≠] x₀ :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (by linarith))
    filter_upwards [hb, self_mem_nhdsWithin] with y hy hne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
    rw [mem_ball, Real.dist_eq] at hy
    have hyU : y ∈ U := hball (by rw [mem_ball, Real.dist_eq]; linarith)
    have hwU : 2 * y - x₀ ∈ U := hball (by
      rw [mem_ball, Real.dist_eq, show 2 * y - x₀ - x₀ = 2 * (y - x₀) by ring, abs_mul]
      norm_num; linarith)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `2y − x₀ < y < x₀`
      have h1 : d ≤ deriv f y := hanti hyU hx₀ hlt.le
      have h2 : deriv f y ≤ slope f (2 * y - x₀) y :=
        hc.deriv_le_slope hwU hyU (by linarith) (hd y hyU)
      rw [slope_comm] at h2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · -- `x₀ < y < 2y − x₀`
      have h1 : deriv f y ≤ d := hanti hx₀ hyU hgt.le
      have h2 : slope f y (2 * y - x₀) ≤ deriv f y :=
        hc.slope_le_deriv hyU hwU (by linarith) (hd y hyU)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  have hq0 : Tendsto (fun y => |slope f y (2 * y - x₀) - d|) (𝓝[≠] x₀) (𝓝 0) := by
    have := (hq.sub_const d).abs
    simpa using this
  have h0 : Tendsto (fun y => deriv f y - d) (𝓝[≠] x₀) (𝓝 0) :=
    squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using hnear) hq0
  simpa using h0.add_const d

end Miao.IncompleteMarkets
