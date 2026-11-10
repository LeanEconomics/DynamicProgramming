/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The young agent's saving problem in the Diamond model

Miao, §16.2, p. 545. A young agent with wage `w` solves
`max u(c_t^t) + βu(c_{t+1}^t)` subject to `c_t^t + s_t = w_t`, `c_{t+1}^t = R_{t+1}s_t`.

* Tangent-line inequalities for (strictly) concave differentiable functions
  (`op_concave_tangent`, `op_strictConcave_tangent`).
* The Euler equation `u′(w − s) = βu′(Rs)R`: necessary at an interior maximum
  (`op_euler_necessary`), sufficient for concave `u` (`op_euler_sufficient`), and for strictly
  concave `u` the maximum is unique (`op_euler_sufficient_strict`).
* The saving function `s = s(w, R)`: with a continuous, strictly decreasing marginal utility
  satisfying the Inada condition at `0`, the Euler equation has exactly one solution in `(0, w)`
  (`op_saving_exists`, `op_saving_unique`).
* `0 < s_w < 1`: saving and first-period consumption both rise strictly with the wage
  (`op_saving_wage_mono`); with a differentiable saving function the implicit derivative is
  `s_w = u″(c_y)/(u″(c_y) + βR²u″(c_o)) ∈ (0, 1)` (`op_saving_sw`).
* Log utility with second-period income `y₂` (used for Exercises 16.4–16.8): the optimal saving
  is `s = (βy₁ − y₂/R)/(1 + β)` (`opLogSaving`, `op_log_saving`).

Departure: the book states `0 < s_w < 1` as a property of the derivative of the saving
function; the derivative-free monotonicity statement `op_saving_wage_mono` needs no
differentiability, and `op_saving_sw` is the derivative statement.
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- The tangent line of a concave function lies above its graph. -/
theorem op_concave_tangent {u : ℝ → ℝ} {S : Set ℝ} (hu : ConcaveOn ℝ S u) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt u d x) : u y ≤ u x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hu.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    nlinarith
  · simp
  · have h := hu.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    nlinarith

/-- The tangent line of a strictly concave function lies strictly above its graph off `x`. -/
theorem op_strictConcave_tangent {u : ℝ → ℝ} {S : Set ℝ} (hu : StrictConcaveOn ℝ S u)
    {x y d : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hne : y ≠ x) (hd : HasDerivAt u d x) :
    u y < u x + d * (y - x) := by
  rcases lt_or_gt_of_ne hne with hyx | hxy
  · have h := hu.lt_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at h
    nlinarith
  · have h := hu.slope_lt_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at h
    nlinarith

/-- The derivative of the lifetime utility `s ↦ u(w − s) + βu(Rs)`. -/
theorem op_lifetime_hasDerivAt {u up : ℝ → ℝ} {β w R s : ℝ}
    (hy : HasDerivAt u (up (w - s)) (w - s)) (ho : HasDerivAt u (up (R * s)) (R * s)) :
    HasDerivAt (fun x => u (w - x) + β * u (R * x))
      (-up (w - s) + β * (up (R * s) * R)) s := by
  have h1 : HasDerivAt (fun x => u (w - x)) (up (w - s) * (-1)) s := by
    have := (hasDerivAt_id s).const_sub w
    exact hy.comp s this
  have h2 : HasDerivAt (fun x => u (R * x)) (up (R * s) * R) s := by
    have := (hasDerivAt_id s).const_mul R
    simp only [mul_one] at this
    exact ho.comp s this
  convert h1.add (h2.const_mul β) using 1
  ring

/-- Miao, p. 545: the consumption Euler equation `u′(w − s) = βu′(Rs)R` is necessary at an
interior maximum of the young agent's problem. -/
theorem op_euler_necessary {u up : ℝ → ℝ} {β w R s : ℝ} (hs0 : 0 < s) (hsw : s < w)
    (hmax : ∀ s' ∈ Set.Ioo 0 w, u (w - s') + β * u (R * s') ≤ u (w - s) + β * u (R * s))
    (hy : HasDerivAt u (up (w - s)) (w - s)) (ho : HasDerivAt u (up (R * s)) (R * s)) :
    up (w - s) = β * up (R * s) * R := by
  have hloc : IsLocalMax (fun x => u (w - x) + β * u (R * x)) s :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs0 hsw) hmax
  have := hloc.hasDerivAt_eq_zero (op_lifetime_hasDerivAt hy ho)
  linarith

/-- Miao, p. 545: for concave `u` the Euler equation is sufficient: a saving level `s ∈ (0, w)`
satisfying it maximises lifetime utility over `(0, w)`. -/
theorem op_euler_sufficient {u up : ℝ → ℝ} {β w R s : ℝ} (hu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hβ : 0 ≤ β) (hR : 0 < R) (hs0 : 0 < s) (hsw : s < w)
    (hy : HasDerivAt u (up (w - s)) (w - s)) (ho : HasDerivAt u (up (R * s)) (R * s))
    (heul : up (w - s) = β * up (R * s) * R) :
    ∀ s' ∈ Set.Ioo 0 w, u (w - s') + β * u (R * s') ≤ u (w - s) + β * u (R * s) := by
  intro s' hs'
  have h1 := op_concave_tangent hu (show w - s ∈ Set.Ioi 0 from by simp; linarith)
    (show w - s' ∈ Set.Ioi 0 from by simp; linarith [hs'.2]) hy
  have h2 := op_concave_tangent hu (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
    (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs'.1) ho
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  have : up (w - s) * (w - s' - (w - s)) + β * (up (R * s) * (R * s' - R * s)) = 0 := by
    rw [heul]; ring
  nlinarith

/-- Miao, p. 545: for strictly concave `u` the saving level satisfying the Euler equation is the
unique maximiser over `(0, w)`. -/
theorem op_euler_sufficient_strict {u up : ℝ → ℝ} {β w R s : ℝ}
    (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) (hβ : 0 ≤ β) (hR : 0 < R) (hs0 : 0 < s)
    (hsw : s < w) (hy : HasDerivAt u (up (w - s)) (w - s))
    (ho : HasDerivAt u (up (R * s)) (R * s)) (heul : up (w - s) = β * up (R * s) * R) :
    ∀ s' ∈ Set.Ioo 0 w, s' ≠ s →
      u (w - s') + β * u (R * s') < u (w - s) + β * u (R * s) := by
  intro s' hs' hne
  have h1 := op_strictConcave_tangent hu (show w - s ∈ Set.Ioi 0 from by simp; linarith)
    (show w - s' ∈ Set.Ioi 0 from by simp; linarith [hs'.2])
    (fun h => hne (by linarith)) hy
  have h2 := op_concave_tangent hu.concaveOn (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
    (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs'.1) ho
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  have : up (w - s) * (w - s' - (w - s)) + β * (up (R * s) * (R * s' - R * s)) = 0 := by
    rw [heul]; ring
  nlinarith

/-- The Inada condition `u′(0) = ∞`, in the form used below. -/
theorem op_inada_small {up : ℝ → ℝ} (hinada : Tendsto up (𝓝[>] 0) atTop) (M : ℝ) :
    ∃ ε > 0, ∀ c, 0 < c → c < ε → M < up c := by
  obtain ⟨ε, hε, hsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 (hinada.eventually_gt_atTop M)
  exact ⟨ε, hε, fun c hc hcε => hsub ⟨hc, hcε⟩⟩

/-- Miao, p. 545: "solving yields a saving function `s_t = s(w_t, R_{t+1})`". With a
continuous, strictly decreasing marginal utility `u′ > 0` satisfying the Inada condition at `0`,
the Euler equation has a solution `s ∈ (0, w)` for every `w > 0`, `R > 0`. -/
theorem op_saving_exists {up : ℝ → ℝ} {β w R : ℝ} (hβ : 0 < β) (hw : 0 < w) (hR : 0 < R)
    (hcont : ContinuousOn up (Set.Ioi 0)) (hanti : StrictAntiOn up (Set.Ioi 0))
    (hinada : Tendsto up (𝓝[>] 0) atTop) :
    ∃ s, 0 < s ∧ s < w ∧ up (w - s) = β * up (R * s) * R := by
  have hβR : 0 < β * R := mul_pos hβ hR
  obtain ⟨ε1, hε1, h1⟩ := op_inada_small hinada (up (w / 2) / (β * R))
  obtain ⟨ε2, hε2, h2⟩ := op_inada_small hinada (β * R * up (R * w / 2))
  set c1 := min (ε1 / 2) (R * w / 4) with hc1
  have hc1pos : 0 < c1 := lt_min (by linarith) (by positivity)
  have hc1le : c1 ≤ R * w / 4 := min_le_right _ _
  have hc1lt : c1 < ε1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set s1 := c1 / R with hs1
  have hs1pos : 0 < s1 := div_pos hc1pos hR
  have hRs1 : R * s1 = c1 := by rw [hs1]; field_simp
  have hs1le : s1 ≤ w / 4 := by
    rw [hs1, div_le_iff₀ hR]; linarith
  set c2 := min (ε2 / 2) (w / 4) with hc2
  have hc2pos : 0 < c2 := lt_min (by linarith) (by positivity)
  have hc2le : c2 ≤ w / 4 := min_le_right _ _
  have hc2lt : c2 < ε2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set s2 := w - c2 with hs2
  set g : ℝ → ℝ := fun s => up (w - s) - β * up (R * s) * R with hg
  have hg1 : g s1 < 0 := by
    have ha := h1 c1 hc1pos hc1lt
    have hb : up (w - s1) < up (w / 2) :=
      hanti (show w / 2 ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s1 ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    rw [div_lt_iff₀ hβR] at ha
    simp only [hg, hRs1]
    nlinarith
  have hg2 : 0 < g s2 := by
    have ha : β * R * up (R * w / 2) < up c2 := h2 c2 hc2pos hc2lt
    have hb : up (R * s2) < up (R * w / 2) :=
      hanti (show R * w / 2 ∈ Set.Ioi 0 from by rw [Set.mem_Ioi]; positivity)
        (show R * s2 ∈ Set.Ioi 0 from mul_pos hR (by simp [hs2]; linarith))
        (by rw [hs2]; nlinarith)
    have hc : w - s2 = c2 := by rw [hs2]; ring
    simp only [hg, hc]
    nlinarith
  have hle : s1 ≤ s2 := by rw [hs2]; linarith
  have hsub : Set.Icc s1 s2 ⊆ Set.Ioo 0 w := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hgc : ContinuousOn g (Set.Icc s1 s2) := by
    apply ContinuousOn.sub
    · exact hcont.comp (continuousOn_const.sub continuousOn_id)
        (fun x hx => by simp; linarith [(hsub hx).2])
    · apply ContinuousOn.mul _ continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact hcont.comp (continuousOn_const.mul continuousOn_id)
        (fun x hx => by simp only [Set.mem_Ioi]; exact mul_pos hR (hsub hx).1)
  obtain ⟨s, hs, hgs⟩ := intermediate_value_Icc hle hgc ⟨hg1.le, hg2.le⟩
  refine ⟨s, (hsub hs).1, (hsub hs).2, ?_⟩
  simp only [hg] at hgs
  linarith

/-- Miao, p. 545: the saving function is well defined: with strictly decreasing marginal
utility the Euler equation has at most one solution in `(0, w)`. -/
theorem op_saving_unique {up : ℝ → ℝ} {β w R s s' : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hanti : StrictAntiOn up (Set.Ioi 0)) (hs0 : 0 < s) (hsw : s < w) (hs0' : 0 < s')
    (hsw' : s' < w) (he : up (w - s) = β * up (R * s) * R)
    (he' : up (w - s') = β * up (R * s') * R) : s = s' := by
  have hβR : 0 < β * R := mul_pos hβ hR
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have ha : up (w - s) < up (w - s') :=
      hanti (show w - s' ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    have hb : up (R * s') < up (R * s) :=
      hanti (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
        (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0') (by nlinarith)
    nlinarith
  · have ha : up (w - s') < up (w - s) :=
      hanti (show w - s ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s' ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    have hb : up (R * s) < up (R * s') :=
      hanti (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0')
        (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0) (by nlinarith)
    nlinarith

/-- Miao, p. 545: "`0 < s_w < 1`; saving is an increasing function of the wage rate by the
concavity of `u`". If `s` solves the Euler equation at the wage `w` and `s′` at `w′ > w` (same
`R`), then saving rises strictly, `s < s′`, and so does first-period consumption,
`w − s < w′ − s′` (so `0 < s′ − s < w′ − w`). -/
theorem op_saving_wage_mono {up : ℝ → ℝ} {β w w' R s s' : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hanti : StrictAntiOn up (Set.Ioi 0)) (hww : w < w') (hs0 : 0 < s) (hsw : s < w)
    (hs0' : 0 < s') (hsw' : s' < w') (he : up (w - s) = β * up (R * s) * R)
    (he' : up (w' - s') = β * up (R * s') * R) : s < s' ∧ w - s < w' - s' := by
  have hβR : 0 < β * R := mul_pos hβ hR
  constructor
  · by_contra h
    push Not at h
    have ha : up (w' - s') < up (w - s) :=
      hanti (show w - s ∈ Set.Ioi 0 from by simp; linarith)
        (show w' - s' ∈ Set.Ioi 0 from by simp; linarith) (by linarith)
    have hb : up (R * s) ≤ up (R * s') :=
      hanti.antitoneOn (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0')
        (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0) (by nlinarith)
    nlinarith
  · by_contra h
    push Not at h
    have ha : up (w - s) ≤ up (w' - s') :=
      hanti.antitoneOn (show w' - s' ∈ Set.Ioi 0 from by simp; linarith)
        (show w - s ∈ Set.Ioi 0 from by simp; linarith) h
    have hb : up (R * s') < up (R * s) :=
      hanti (show R * s ∈ Set.Ioi 0 from mul_pos hR hs0)
        (show R * s' ∈ Set.Ioi 0 from mul_pos hR hs0') (by nlinarith)
    nlinarith

/-- Miao, p. 545: the implicit derivative of the saving function. If `sf` is a saving function
(it solves the Euler equation for all wages near `w`), differentiable at `w` with derivative
`s_w`, and `u′` has derivative `u″` at both consumptions, then
`u″(c_y)(1 − s_w) = βR²u″(c_o)s_w`; with `u″ < 0` this gives `0 < s_w < 1`. -/
theorem op_saving_sw {up upp sf : ℝ → ℝ} {β w R sw : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hsf : ∀ᶠ w' in 𝓝 w, up (w' - sf w') = β * up (R * sf w') * R)
    (hd : HasDerivAt sf sw w) (hy : HasDerivAt up (upp (w - sf w)) (w - sf w))
    (ho : HasDerivAt up (upp (R * sf w)) (R * sf w)) :
    upp (w - sf w) * (1 - sw) = β * R ^ 2 * upp (R * sf w) * sw ∧
      (upp (w - sf w) < 0 → upp (R * sf w) < 0 → 0 < sw ∧ sw < 1) := by
  have h1 : HasDerivAt (fun x => up (x - sf x)) (upp (w - sf w) * (1 - sw)) w :=
    hy.comp w ((hasDerivAt_id w).sub hd)
  have h2 : HasDerivAt (fun x => β * up (R * sf x) * R)
      (β * (upp (R * sf w) * (R * sw)) * R) w :=
    ((ho.comp w (hd.const_mul R)).const_mul β).mul_const R
  have h1' : HasDerivAt (fun x => β * up (R * sf x) * R) (upp (w - sf w) * (1 - sw)) w :=
    h1.congr_of_eventuallyEq (hsf.mono fun x hx => hx.symm)
  have heq := h1'.unique h2
  refine ⟨by rw [heq]; ring, fun hny hno => ?_⟩
  have hk : 0 < β * R ^ 2 := by positivity
  have hpos : 0 < -upp (R * sf w) * (β * R ^ 2) := mul_pos (by linarith) hk
  constructor
  · by_contra h
    push Not at h
    have : upp (w - sf w) * (1 - sw) < 0 := mul_neg_of_neg_of_pos hny (by linarith)
    have : 0 ≤ β * R ^ 2 * upp (R * sf w) * sw := by nlinarith
    linarith
  · by_contra h
    push Not at h
    have : 0 ≤ upp (w - sf w) * (1 - sw) := mul_nonneg_of_nonpos_of_nonpos hny.le (by linarith)
    have : β * R ^ 2 * upp (R * sf w) * sw < 0 := by nlinarith
    linarith

/-- Optimal saving with log utility, wage `y₁` and second-period income `y₂`:
`s = (βy₁ − y₂/R)/(1 + β)`. -/
noncomputable def opLogSaving (β y1 y2 R : ℝ) : ℝ :=
  (β * y1 - y2 / R) / (1 + β)

/-- Log utility `ln c_y + β ln c_o` with budget `c_y = y₁ − s`, `c_o = Rs + y₂`: the saving
`opLogSaving` gives `c_y = W/(1 + β)`, `c_o = βRW/(1 + β)` with `W = y₁ + y₂/R`, and maximises
lifetime utility over every `s` with both consumptions positive. -/
theorem op_log_saving {β y1 y2 R : ℝ} (hβ : 0 < β) (hR : 0 < R) (hW : 0 < y1 + y2 / R) :
    y1 - opLogSaving β y1 y2 R = (y1 + y2 / R) / (1 + β) ∧
      R * opLogSaving β y1 y2 R + y2 = β * R * (y1 + y2 / R) / (1 + β) ∧
      ∀ s, 0 < y1 - s → 0 < R * s + y2 →
        Real.log (y1 - s) + β * Real.log (R * s + y2) ≤
          Real.log (y1 - opLogSaving β y1 y2 R) +
            β * Real.log (R * opLogSaving β y1 y2 R + y2) := by
  have hcy : y1 - opLogSaving β y1 y2 R = (y1 + y2 / R) / (1 + β) := by
    unfold opLogSaving; field_simp; ring
  have hco : R * opLogSaving β y1 y2 R + y2 = β * R * (y1 + y2 / R) / (1 + β) := by
    unfold opLogSaving; field_simp; ring
  refine ⟨hcy, hco, fun s hs1 hs2 => ?_⟩
  set W := y1 + y2 / R
  have hcyp : 0 < W / (1 + β) := by positivity
  have hcop : 0 < β * R * W / (1 + β) := by positivity
  have key : ∀ x c : ℝ, 0 < x → 0 < c → Real.log x ≤ Real.log c + x / c - 1 := by
    intro x c hx hc
    have := Real.log_le_sub_one_of_pos (div_pos hx hc)
    rw [Real.log_div hx.ne' hc.ne'] at this
    linarith
  have k1 := key (y1 - s) _ hs1 hcyp
  have k2 := key (R * s + y2) _ hs2 hcop
  rw [hcy, hco]
  have h3 := mul_le_mul_of_nonneg_left k2 hβ.le
  have : (y1 - s) / (W / (1 + β)) - 1 + β * ((R * s + y2) / (β * R * W / (1 + β)) - 1) = 0 := by
    have hW' : W ≠ 0 := hW.ne'
    have hWR : W * R = y1 * R + y2 := by simp only [W]; field_simp
    field_simp
    linear_combination (-(1 + β)) * hWR
  nlinarith

end Miao.OverlappingGenerations
