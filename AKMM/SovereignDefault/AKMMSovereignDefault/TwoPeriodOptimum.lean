/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import CapitalMarketImperfections.DebtOverhangLaffer
import AKMMSovereignDefault.TwoPeriod

/-!
# The two-period default model: optimal borrowing and the Euler equation (24.6)

AKMM, §24.3, p. 741. The government chooses `B₂ ≥ 0` to maximise
`W(B₂) = u(B₂q₁(B₂)) + βE u(Ĉ₂(B₂, Y₂))`.

* **Existence** (`tp_exists_optimal`): if `u` is continuous, nondecreasing and strictly
  increasing on `[0, ∞)`, `E|u(Y₂)|`, `E|u((1 − φ)Y₂)|` and `E Y₂` are finite, `Y₂ ≥ 0` has no
  atoms and is positive with positive probability, then an optimal `B̂₂ ≥ 0` exists. The revenue
  `B₂q₁(B₂) ≤ φE[Y₂; Y₂ ≥ B₂/φ]` vanishes as `B₂ → ∞`, so `W` tends to a limit that some small
  positive debt beats; on a compact interval `W` is continuous.
* **The Laffer side** (`tp_laffer_side`): at an optimum `B̂₂ > 0` the revenue `B₂q₁(B₂)` cannot be
  decreasing, `q₁ + B₂ dq₁/dB₂ ≥ 0`: otherwise a write-down raises revenue (Obstfeld–Rogoff's
  `writedown_raises_value`, imported) and weakly raises `Ĉ₂`.
* **Leibniz rule** (`tp_hasDerivAt_expectedUtility`): for `0 < φ < 1` and concave increasing
  differentiable `u`, `d/dB₂ E u(Ĉ₂) = −E[u′(Ĉ₂)(1 − D̂₂)]`; the boundary term vanishes because
  `Ĉ₂` is continuous at `Y₂ = B₂/φ` and the threshold has probability zero.
* **(24.6)** (`eq_24_6`): at an interior optimum where `q₁` is differentiable,
  `u′(C₁)[q₁ + B₂ dq₁/dB₂] = βE[u′(Ĉ₂)(1 − D̂₂)]`.

Departure: `u` is real valued (the Inada condition `u′(0) = ∞` is not needed; `log` is excluded
from the existence theorem, which needs `u` continuous at `0`, but not from the Leibniz rule).
-/

namespace AKMM.SovereignDefault

open MeasureTheory Filter Topology ProbabilityTheory

/-- AKMM, p. 741: the period-1 objective `W(B₂) = u(B₂q₁(B₂)) + βE u(Ĉ₂(B₂, Y₂))`. -/
noncomputable def tp_objective (μ : Measure ℝ) (φ β : ℝ) (u : ℝ → ℝ) (B : ℝ) : ℝ :=
  u (B * price μ φ B) + β * ∫ y, u (cons2 φ B y) ∂μ

/-- `Ĉ₂` is continuous in `Y₂`. -/
theorem tp_cons2_continuous_Y {φ : ℝ} (hφ : 0 < φ) (B : ℝ) : Continuous fun Y => cons2 φ B Y := by
  simp only [tp_cons2_eq hφ]
  fun_prop

/-- `Ĉ₂` is `1`-Lipschitz in `B₂`. -/
theorem tp_cons2_lipschitz {φ : ℝ} (hφ : 0 < φ) (B B' Y : ℝ) :
    |cons2 φ B Y - cons2 φ B' Y| ≤ |B - B'| := by
  simp only [tp_cons2_eq hφ]
  have := abs_min_sub_min_le_max (φ * Y) B (φ * Y) B'
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at this
  rw [show Y - min (φ * Y) B - (Y - min (φ * Y) B') = -(min (φ * Y) B - min (φ * Y) B') by ring,
    abs_neg]
  exact this

/-- The revenue `B₂q₁(B₂)` vanishes as `B₂ → ∞` when `E Y₂ < ∞`:
`B₂ Pr(Y₂ ≥ B₂/φ) ≤ φE[Y₂; Y₂ ≥ B₂/φ] → 0`. -/
theorem tp_revenue_tendsto_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] {φ : ℝ} (hφ : 0 < φ)
    (hY : Integrable (fun y : ℝ => y) μ) :
    Tendsto (fun B => B * price μ φ B) atTop (𝓝 0) := by
  have hT : Tendsto (fun B : ℝ => φ * ∫ y, (Set.Ici (B / φ)).indicator (fun y => y) y ∂μ)
      atTop (𝓝 (φ * 0)) := by
    refine Tendsto.const_mul φ ?_
    refine tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun B y => (Set.Ici (B / φ)).indicator (fun y : ℝ => y) y) (f := fun _ => (0 : ℝ))
      (fun y => |y|) ?_ ?_ hY.abs ?_ |>.trans_eq (by rw [integral_zero])
    · exact Eventually.of_forall fun B =>
        (hY.aestronglyMeasurable.indicator measurableSet_Ici)
    · exact Eventually.of_forall fun B => Eventually.of_forall fun y => by
        simp only [Set.indicator]; split_ifs <;> simp
    · refine Eventually.of_forall fun y => ?_
      have hev : ∀ᶠ B in atTop, y < B / φ :=
        (tendsto_id.atTop_div_const hφ).eventually (eventually_gt_atTop y)
      refine tendsto_const_nhds.congr' (hev.mono fun B hB => ?_)
      have : y ∉ Set.Ici (B / φ) := fun h => absurd (Set.mem_Ici.1 h) (not_le.2 hB)
      simp only [Set.indicator, this, ↓reduceIte]
  rw [mul_zero] at hT
  have hle : ∀ᶠ B in atTop, B * price μ φ B ≤
      φ * ∫ y, (Set.Ici (B / φ)).indicator (fun y => y) y ∂μ := by
    filter_upwards [eventually_ge_atTop 0] with B hB
    rw [price, ← integral_const_mul, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => ?_)
      ((hY.indicator measurableSet_Ici).const_mul φ) (Eventually.of_forall fun y => ?_)
    · simp only [tp_one_sub_defaultRule, Pi.zero_apply]
      exact mul_nonneg hB (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · simp only [tp_one_sub_defaultRule, Set.indicator, Pi.one_apply]
      split_ifs with h
      · rw [Set.mem_Ici, div_le_iff₀ hφ] at h; linarith
      · simp
  have hge : ∀ᶠ B in atTop, 0 ≤ B * price μ φ B := by
    filter_upwards [eventually_ge_atTop 0] with B hB
    exact mul_nonneg hB (tp_price_mem_Icc μ φ B).1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT hge hle

/-- **Existence of an optimal `B₂`** (AKMM, p. 741). Under the hypotheses listed in the module
docstring the period-1 problem `max_{B₂ ≥ 0} W(B₂)` has a solution. -/
theorem tp_exists_optimal {μ : Measure ℝ} [IsProbabilityMeasure μ] (hna : ∀ x, μ {x} = 0)
    (h0 : μ (Set.Iio 0) = 0) (hpos : μ (Set.Ioi 0) ≠ 0) {φ β : ℝ} (hφ : 0 < φ) (hβ : 0 ≤ β)
    {u : ℝ → ℝ} (hu : Continuous u) (hmono : Monotone u) (hstrict : StrictMonoOn u (Set.Ici 0))
    (hiY : Integrable (fun y => u y) μ) (hiD : Integrable (fun y => u (y - φ * y)) μ)
    (hY : Integrable (fun y : ℝ => y) μ) :
    ∃ B₀, 0 ≤ B₀ ∧ ∀ B, 0 ≤ B → tp_objective μ φ β u B ≤ tp_objective μ φ β u B₀ := by
  have hy0 : ∀ᵐ y ∂μ, 0 ≤ y := by
    rw [ae_iff]; simp only [not_le]; exact h0
  have hmeasB : ∀ B, AEStronglyMeasurable (fun y => u (cons2 φ B y)) μ := fun B =>
    (hu.comp (tp_cons2_continuous_Y hφ B)).aestronglyMeasurable
  have hbound : ∀ B, 0 ≤ B → ∀ᵐ y ∂μ, ‖u (cons2 φ B y)‖ ≤ |u y| + |u (y - φ * y)| := by
    intro B hB
    filter_upwards [hy0] with y hy
    obtain ⟨h1, h2⟩ := tp_cons2_bounds hφ hB hy
    have a1 := hmono h1
    have a2 := hmono h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> cases abs_cases (u y) <;> cases abs_cases (u (y - φ * y)) <;> linarith
  have hint : ∀ B, 0 ≤ B → Integrable (fun y => u (cons2 φ B y)) μ := fun B hB =>
    (hiY.abs.add hiD.abs).mono' (hmeasB B) (hbound B hB)
  set G : ℝ → ℝ := fun B => ∫ y, u (cons2 φ B y) ∂μ with hG
  -- continuity of `G` on `[0, ∞)`
  have hGc : ContinuousOn G (Set.Ici 0) :=
    continuousOn_of_dominated (fun B _ => hmeasB B) (fun B hB => hbound B hB)
      (hiY.abs.add hiD.abs) (Eventually.of_forall fun y =>
        (hu.comp (tp_cons2_continuous hφ y)).continuousOn)
  -- the limit of `G`
  have hGlim : Tendsto G atTop (𝓝 (∫ y, u (y - φ * y) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => |u y| + |u (y - φ * y)|)
      (Eventually.of_forall fun B => hmeasB B) ?_ (hiY.abs.add hiD.abs) ?_
    · filter_upwards [eventually_ge_atTop 0] with B hB using hbound B hB
    · refine Eventually.of_forall fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (φ * y)] with B hB
      rw [tp_cons2_eq hφ, min_eq_left hB.le]
  have hRc : Continuous fun B => B * price μ φ B := continuous_id.mul (tp_price_continuous hna φ)
  have hWc : ContinuousOn (tp_objective μ φ β u) (Set.Ici 0) :=
    ((hu.comp hRc).continuousOn).add (continuousOn_const.mul hGc)
  have hWlim : Tendsto (tp_objective μ φ β u) atTop
      (𝓝 (u 0 + β * ∫ y, u (y - φ * y) ∂μ)) :=
    ((hu.tendsto 0).comp (tp_revenue_tendsto_zero hφ hY)).add (hGlim.const_mul β)
  -- a debt level with positive revenue
  obtain ⟨x, hx, hxμ⟩ : ∃ x : ℝ, 0 < x ∧ μ (Set.Ici x) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hpos
    have : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ici (1 / ((n : ℝ) + 1)) := by
      ext y
      simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
      constructor
      · intro hy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hy
        exact ⟨n, hn.le⟩
      · rintro ⟨n, hn⟩
        exact lt_of_lt_of_le (by positivity) hn
    rw [this]
    exact measure_iUnion_null fun n => hcon _ (by positivity)
  set B₁ := φ * x with hB₁
  have hB₁0 : 0 < B₁ := mul_pos hφ hx
  have hR₁ : 0 < B₁ * price μ φ B₁ := by
    refine mul_pos hB₁0 ?_
    rw [tp_price_eq_measure, hB₁, mul_div_cancel_left₀ _ hφ.ne', Measure.real,
      ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.2 hxμ, measure_lt_top _ _⟩
  have hGge : ∫ y, u (y - φ * y) ∂μ ≤ G B₁ := by
    refine integral_mono_ae hiD (hint B₁ hB₁0.le) ?_
    filter_upwards [hy0] with y hy using hmono (tp_cons2_bounds hφ hB₁0.le hy).1
  have hbeat : u 0 + β * ∫ y, u (y - φ * y) ∂μ < tp_objective μ φ β u B₁ := by
    have := hstrict (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hR₁.le) hR₁
    unfold tp_objective
    nlinarith [mul_le_mul_of_nonneg_left hGge hβ]
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hWlim.eventually (gt_mem_nhds hbeat))
  set M := max K B₁
  obtain ⟨B₀, hB₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_isMaxOn
    ⟨0, Set.left_mem_Icc.2 (hB₁0.le.trans (le_max_right _ _))⟩
    (hWc.mono Set.Icc_subset_Ici_self)
  refine ⟨B₀, hB₀.1, fun B hB => ?_⟩
  rcases le_or_gt B M with h | h
  · exact hmax ⟨hB, h⟩
  · have hB1 : B₁ ∈ Set.Icc 0 M := ⟨hB₁0.le, le_max_right _ _⟩
    exact ((hK B ((le_max_left _ _).trans h.le)).le).trans (hmax hB1)

/-- **The optimum is on the increasing side of the debt Laffer curve** (AKMM, p. 741, the
marginal revenue `q₁ + B₂dq₁/dB₂` in (24.6)): at an optimum `B̂₂ > 0` where the revenue
`R(B₂) = B₂q₁(B₂)` has derivative `r`, `r ≥ 0`. Proof: if `r < 0`, a small write-down raises
revenue (Obstfeld–Rogoff, p. 395, `writedown_raises_value`) and weakly raises `Ĉ₂`. -/
theorem tp_laffer_side {μ : Measure ℝ} {φ β : ℝ} (hφ : 0 < φ) (hβ : 0 ≤ β) {u : ℝ → ℝ}
    (hmono : Monotone u) (hstrict : StrictMonoOn u (Set.Ici 0))
    (hint : ∀ B, 0 ≤ B → Integrable (fun y => u (cons2 φ B y)) μ) [IsProbabilityMeasure μ]
    {B₀ r : ℝ} (hB₀ : 0 < B₀)
    (hopt : ∀ B, 0 ≤ B → tp_objective μ φ β u B ≤ tp_objective μ φ β u B₀)
    (hr : HasDerivAt (fun B => B * price μ φ B) r B₀) : 0 ≤ r := by
  by_contra hneg
  rw [not_le] at hneg
  have hev := ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer.writedown_raises_value
    hr hneg
  have hpos : ∀ᶠ B in 𝓝[<] B₀, 0 < B := nhdsWithin_le_nhds (eventually_gt_nhds hB₀)
  obtain ⟨B, ⟨hB1, hB2⟩, hB3⟩ := ((hev.and hpos).and self_mem_nhdsWithin).exists
  have hR0 : 0 ≤ B₀ * price μ φ B₀ := mul_nonneg hB₀.le (tp_price_mem_Icc μ φ B₀).1
  have hu1 := hstrict (Set.mem_Ici.2 hR0) (Set.mem_Ici.2 (hR0.trans hB1.le)) hB1
  have hG : ∫ y, u (cons2 φ B₀ y) ∂μ ≤ ∫ y, u (cons2 φ B y) ∂μ :=
    integral_mono (hint B₀ hB₀.le) (hint B hB2.le) fun y =>
      hmono (tp_cons2_antitone hφ y (le_of_lt (Set.mem_Iio.1 hB3)))
  have := hopt B hB2.le
  unfold tp_objective at this
  nlinarith [mul_le_mul_of_nonneg_left hG hβ]

/-- **Leibniz rule for the expected period-2 utility** (AKMM, p. 741, the right-hand side of
(24.6)): for `0 < φ < 1`, `B₂ > 0`, `Y₂` without atoms and `u` differentiable, increasing and
concave on `(0, ∞)`, `d/dB₂ E u(Ĉ₂(B₂, Y₂)) = −E[u′(Ĉ₂)(1 − D̂₂)]`. -/
theorem tp_hasDerivAt_expectedUtility {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hna : ∀ x, μ {x} = 0) {φ : ℝ} (hφ : 0 < φ) (hφ1 : φ < 1) {u : ℝ → ℝ} (hum : Measurable u)
    (hd : ∀ c, 0 < c → DifferentiableAt ℝ u c) (hanti : AntitoneOn (deriv u) (Set.Ioi 0))
    (hnn : ∀ c, 0 < c → 0 ≤ deriv u c) {B₀ : ℝ} (hB₀ : 0 < B₀)
    (hint : Integrable (fun y => u (cons2 φ B₀ y)) μ) :
    HasDerivAt (fun B => ∫ y, u (cons2 φ B y) ∂μ)
      (-∫ y, deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y) ∂μ) B₀ := by
  set c₀ := (1 - φ) * (B₀ / 2) / φ with hc₀
  have hc₀pos : 0 < c₀ := div_pos (mul_pos (by linarith) (by linarith)) hφ
  set L := deriv u c₀
  have hL : 0 ≤ L := hnn c₀ hc₀pos
  -- `u` is `L`-Lipschitz on `[c₀, ∞)`
  have hLip : LipschitzOnWith (Real.nnabs L) u (Set.Ici c₀) := by
    refine (convex_Ici c₀).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := deriv u)
      (fun c hc => ((hd c (hc₀pos.trans_le hc)).hasDerivAt).hasDerivWithinAt) fun c hc => ?_
    have hc' : 0 < c := hc₀pos.trans_le hc
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Real.coe_nnabs,
      abs_of_nonneg (hnn c hc'), abs_of_nonneg hL]
    exact hanti hc₀pos hc' hc
  set F' : ℝ → ℝ := fun y => -(deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y)) with hF'
  have hball : Metric.ball B₀ (B₀ / 2) ∈ 𝓝 B₀ := Metric.ball_mem_nhds _ (by linarith)
  have hmeas : ∀ B, AEStronglyMeasurable (fun y => u (cons2 φ B y)) μ := fun B =>
    (hum.comp (tp_cons2_continuous_Y hφ B).measurable).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable F' μ := by
    have h1 : (fun y => 1 - defaultRule φ B₀ y) = (Set.Ici (B₀ / φ)).indicator 1 :=
      funext (tp_one_sub_defaultRule φ B₀)
    have h2 : Measurable fun y => 1 - defaultRule φ B₀ y := by
      rw [h1]; exact measurable_const.indicator measurableSet_Ici
    exact (((measurable_deriv u).comp (tp_cons2_continuous_Y hφ B₀).measurable).mul h2).neg
      |>.aestronglyMeasurable
  have hlip : ∀ y, LipschitzOnWith (Real.nnabs L) (fun B => u (cons2 φ B y))
      (Metric.ball B₀ (B₀ / 2)) := by
    intro y
    refine LipschitzOnWith.of_dist_le_mul fun B hB B' hB' => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hB hB'
    rw [Real.coe_nnabs, abs_of_nonneg hL]
    by_cases hy : φ * y < B₀ / 2
    · rw [tp_cons2_eq hφ, tp_cons2_eq hφ, min_eq_left (by linarith), min_eq_left (by linarith),
        dist_self]
      exact mul_nonneg hL dist_nonneg
    · rw [not_lt] at hy
      have hy' : B₀ / 2 / φ ≤ y := by rw [div_le_iff₀ hφ]; linarith
      have hmem : ∀ B'', c₀ ≤ cons2 φ B'' y := fun B'' => by
        rw [tp_cons2_eq hφ, hc₀]
        have : (1 - φ) * (B₀ / 2) / φ ≤ (1 - φ) * y := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hy' (by linarith)
        linarith [min_le_left (φ * y) B'']
      have := (hLip.dist_le_mul _ (hmem B) _ (hmem B'))
      rw [Real.coe_nnabs, abs_of_nonneg hL] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hL)
      rw [Real.dist_eq, Real.dist_eq]
      exact tp_cons2_lipschitz hφ B B' y
  have hdiff : ∀ᵐ y ∂μ, HasDerivAt (fun B => u (cons2 φ B y)) (F' y) B₀ := by
    have hnull : ∀ᵐ y ∂μ, y ≠ B₀ / φ := by
      rw [ae_iff]; simpa using hna (B₀ / φ)
    filter_upwards [hnull] with y hy
    rcases lt_or_gt_of_ne hy with h | h
    · -- default region: locally constant
      have hφy : φ * y < B₀ := by rwa [lt_div_iff₀ hφ, mul_comm] at h
      have hev : (fun B => u (cons2 φ B y)) =ᶠ[𝓝 B₀] fun _ => u (y - φ * y) := by
        filter_upwards [eventually_gt_nhds hφy] with B hB
        rw [tp_cons2_eq hφ, min_eq_left hB.le]
      have hD : defaultRule φ B₀ y = 1 := by
        rw [tp_defaultRule_eq hφ]; simp only [hφy, ↓reduceIte]
      rw [hF']
      simp only [hD, sub_self, mul_zero, neg_zero]
      exact (hasDerivAt_const B₀ _).congr_of_eventuallyEq hev
    · -- repayment region
      have hφy : B₀ < φ * y := by rwa [div_lt_iff₀ hφ, mul_comm] at h
      have hpos : 0 < y - B₀ := by
        have : 0 < y := lt_trans (div_pos hB₀ hφ) h
        nlinarith
      have hev : (fun B => u (cons2 φ B y)) =ᶠ[𝓝 B₀] fun B => u (y - B) := by
        filter_upwards [eventually_lt_nhds hφy] with B hB
        rw [tp_cons2_eq hφ, min_eq_right hB.le]
      have hD : defaultRule φ B₀ y = 0 := by
        rw [tp_defaultRule_eq hφ]; simp only [not_lt.2 hφy.le, ↓reduceIte]
      have hc : cons2 φ B₀ y = y - B₀ := by rw [tp_cons2_eq hφ, min_eq_right hφy.le]
      have hd1 : HasDerivAt (fun B => u (y - B)) (deriv u (y - B₀) * (0 - 1)) B₀ :=
        HasDerivAt.comp B₀ (hd _ hpos).hasDerivAt ((hasDerivAt_const B₀ y).sub (hasDerivAt_id B₀))
      rw [hF']
      simp only [hD, hc, sub_zero, mul_one]
      convert hd1.congr_of_eventuallyEq hev using 1
      ring
  have := hasDerivAt_integral_of_dominated_loc_of_lip (bound := fun _ => L) hball
    (Eventually.of_forall hmeas) hint hF'm (Eventually.of_forall hlip) (integrable_const L) hdiff
  rw [hF'] at this
  simpa only [integral_neg] using this.2

/-- **AKMM, (24.6)**, p. 741: at an optimum `B̂₂ > 0` (with positive period-1 consumption, a
price differentiable at `B̂₂` with derivative `q′`, and the hypotheses of the Leibniz rule),
`u′(C₁)[q₁(B̂₂) + B̂₂q′] = βE[u′(Ĉ₂)(1 − D̂₂)]`. -/
theorem eq_24_6 {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hna : ∀ x, μ {x} = 0) {φ β : ℝ} (hφ : 0 < φ) (hφ1 : φ < 1) {u : ℝ → ℝ} (hum : Measurable u)
    (hd : ∀ c, 0 < c → DifferentiableAt ℝ u c) (hanti : AntitoneOn (deriv u) (Set.Ioi 0))
    (hnn : ∀ c, 0 < c → 0 ≤ deriv u c) {B₀ q' : ℝ} (hB₀ : 0 < B₀)
    (hint : Integrable (fun y => u (cons2 φ B₀ y)) μ)
    (hopt : ∀ B, 0 ≤ B → tp_objective μ φ β u B ≤ tp_objective μ φ β u B₀)
    (hq : HasDerivAt (price μ φ) q' B₀) (hC₁ : 0 < B₀ * price μ φ B₀) :
    deriv u (B₀ * price μ φ B₀) * (price μ φ B₀ + B₀ * q') =
      β * ∫ y, deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y) ∂μ := by
  have hR : HasDerivAt (fun B => B * price μ φ B) (1 * price μ φ B₀ + B₀ * q') B₀ :=
    (hasDerivAt_id B₀).mul hq
  have hU := HasDerivAt.comp B₀ (hd _ hC₁).hasDerivAt hR
  have hG := tp_hasDerivAt_expectedUtility hna hφ hφ1 hum hd hanti hnn hB₀ hint
  have hW : HasDerivAt (tp_objective μ φ β u)
      (deriv u (B₀ * price μ φ B₀) * (1 * price μ φ B₀ + B₀ * q') +
        β * -∫ y, deriv u (cons2 φ B₀ y) * (1 - defaultRule φ B₀ y) ∂μ) B₀ :=
    hU.add (hG.const_mul β)
  have hmax : IsLocalMax (tp_objective μ φ β u) B₀ :=
    Filter.mem_of_superset (Ici_mem_nhds hB₀) fun B hB => hopt B hB
  have := hmax.hasDerivAt_eq_zero hW
  linarith

end AKMM.SovereignDefault
