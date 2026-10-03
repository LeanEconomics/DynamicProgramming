/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.Basics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Convergence rates and Newton's fixed-point iteration

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.1.3–§2.1.4
(pp. 46–51).

A sequence converges to `u*` at rate at least `q` if `eₖ₊₁ ≤ β eₖ^q`
eventually, where `eₖ = ‖uₖ − u*‖`; `q = 1` with `β < 1` is linear
convergence, `q = 2` quadratic. Example 2.1.5: the orbit of a contraction
converges at least linearly. Exercise 2.1.7: for a differentiable self-map of
an interval, the ratio `eₖ₊₁/eₖ` converges to `|T'(u*)|`, so the rate is
linear when `0 < |T'(u*)| < 1`. The book assumes `T` twice continuously
differentiable and uses a second-order Taylor expansion; a continuous first
derivative suffices, and that is what is assumed here.

Newton's fixed-point iteration (2.2) is defined in one dimension, where the
Jacobian is the derivative, and shown to have the same fixed points as `T`.
Its quadratic convergence, which the book cites from Atkinson and Han (2005),
is not claimed.
-/

open Filter Topology Function Set

namespace SargentStachurski.OperatorsFixedPoints

variable {E : Type*} [NormedAddCommGroup E]

/-- Convergence of `(uₖ)` to `u*` at rate at least `q` (p. 46): `q ≥ 1` and, for some `β > 0`,
`eₖ₊₁ ≤ β eₖ^q` for all large `k`, where `eₖ = ‖uₖ − u*‖`. -/
def ConvergesAtRateAtLeast (u : ℕ → E) (u' : E) (q β : ℝ) : Prop :=
  1 ≤ q ∧ 0 < β ∧ ∃ N : ℕ, ∀ k ≥ N, ‖u (k + 1) - u'‖ ≤ β * ‖u k - u'‖ ^ q

/-- Linear convergence (p. 46): rate at least `1` with `β < 1`. -/
def ConvergesLinearly (u : ℕ → E) (u' : E) : Prop :=
  ∃ β : ℝ, β < 1 ∧ ConvergesAtRateAtLeast u u' 1 β

/-- Quadratic convergence (p. 46): rate at least `2`. -/
def ConvergesQuadratically (u : ℕ → E) (u' : E) : Prop :=
  ∃ β : ℝ, ConvergesAtRateAtLeast u u' 2 β

/-- Example 2.1.5 (p. 46): the orbit of a contraction of modulus `λ ∈ (0, 1)` converges to the
fixed point at least linearly, since `eₖ₊₁ = ‖Tuₖ − Tu*‖ ≤ λeₖ`. -/
theorem IsContractionOn.convergesAtRateAtLeast {T : E → E} {U : Set E} {L : ℝ}
    (h : IsContractionOn T U L) (hL : 0 < L) {u₀ u' : E} (hu₀ : u₀ ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : ConvergesAtRateAtLeast (fun k => T^[k] u₀) u' 1 L := by
  refine ⟨le_rfl, hL, 0, fun k _ => ?_⟩
  change ‖T^[k + 1] u₀ - u'‖ ≤ L * ‖T^[k] u₀ - u'‖ ^ (1 : ℝ)
  rw [Real.rpow_one, iterate_succ_apply']
  calc ‖T (T^[k] u₀) - u'‖ = ‖T (T^[k] u₀) - T u'‖ := by rw [hfix.eq]
    _ ≤ L * ‖T^[k] u₀ - u'‖ := h.norm_sub_le _ (h.iterate_mem hu₀ k) _ hu'

theorem IsContractionOn.convergesLinearly {T : E → E} {U : Set E} {L : ℝ}
    (h : IsContractionOn T U L) (hL : 0 < L) {u₀ u' : E} (hu₀ : u₀ ∈ U) (hu' : u' ∈ U)
    (hfix : IsFixedPt T u') : ConvergesLinearly (fun k => T^[k] u₀) u' :=
  ⟨L, h.lt_one, h.convergesAtRateAtLeast hL hu₀ hu' hfix⟩

/-- The one-dimensional estimate behind Exercise 2.1.7: near a fixed point `u*` of a
differentiable `T` whose derivative is continuous at `u*`, the error ratio is within `ε` of
`|T'(u*)|`. The proof applies the mean value inequality to `x ↦ Tx − T'(u*)x`, whose derivative
is small near `u*`. -/
theorem error_ratio_near {T T' : ℝ → ℝ} {u' : ℝ} (hT : ∀ x, HasDerivAt T (T' x) x)
    (hcont : ContinuousAt T' u') (hfix : T u' = u') {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, |x - u'| < δ →
      |T' u'| * |x - u'| - ε * |x - u'| ≤ |T x - u'| ∧
        |T x - u'| ≤ |T' u'| * |x - u'| + ε * |x - u'| := by
  have hev : ∀ᶠ x in 𝓝 u', |T' x - T' u'| < ε := by
    have := Metric.tendsto_nhds.1 hcont ε hε
    simpa [Real.dist_eq] using this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  set B := Metric.ball u' δ with hB
  have hxB : x ∈ B := by rwa [hB, Metric.mem_ball, Real.dist_eq]
  have hu'B : u' ∈ B := Metric.mem_ball_self hδ
  -- the auxiliary map `F x = T x − T'(u*) x` has derivative `T' x − T'(u*)`, of size `< ε` on `B`
  have hF : ∀ y ∈ B, HasDerivWithinAt (fun y => T y - T' u' * y) (T' y - T' u') B y :=
    fun y _ => ((hT y).sub ((hasDerivAt_id y).const_mul (T' u'))).hasDerivWithinAt |>.congr_deriv
      (by ring)
  have hbound : ∀ y ∈ B, ‖T' y - T' u'‖ ≤ ε := fun y hy =>
    (hball (by rwa [← Metric.mem_ball])).le
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hF hbound (convex_ball u' δ)
    hu'B hxB
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  -- `|T x − u* − T'(u*)(x − u*)| ≤ ε|x − u*|`
  have hlin : |T x - u' - T' u' * (x - u')| ≤ ε * |x - u'| := by
    have : T x - T' u' * x - (T u' - T' u' * u') = T x - u' - T' u' * (x - u') := by
      rw [hfix]; ring
    rwa [this] at hmvt
  constructor
  · have := abs_sub_abs_le_abs_sub (T' u' * (x - u')) (T x - u')
    rw [abs_mul, abs_sub_comm (T' u' * (x - u'))] at this
    linarith
  · have := abs_sub_abs_le_abs_sub (T x - u') (T' u' * (x - u'))
    rw [abs_mul] at this
    linarith

/-- Exercise 2.1.7 (p. 47): if `uₖ → u*` with `uₖ ≠ u*` for all `k`, then `eₖ₊₁/eₖ → |T'(u*)|`. -/
theorem tendsto_error_ratio {T T' : ℝ → ℝ} {u' : ℝ} (hT : ∀ x, HasDerivAt T (T' x) x)
    (hcont : ContinuousAt T' u') (hfix : T u' = u') {u : ℕ → ℝ} (hu : ∀ k, u (k + 1) = T (u k))
    (hne : ∀ k, u k ≠ u') (hlim : Tendsto u atTop (𝓝 u')) :
    Tendsto (fun k => |u (k + 1) - u'| / |u k - u'|) atTop (𝓝 |T' u'|) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := error_ratio_near hT hcont hfix (half_pos hε)
  have hev : ∀ᶠ k in atTop, |u k - u'| < δ := by
    have := Metric.tendsto_atTop.1 hlim δ hδ
    simpa [Real.dist_eq] using this
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun k hk => ?_⟩
  have hpos : 0 < |u k - u'| := abs_pos.2 (sub_ne_zero.2 (hne k))
  obtain ⟨h1, h2⟩ := hδε (u k) (hN k hk)
  rw [hu k] at *
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor
  · rw [div_sub' hpos.ne', div_lt_iff₀ hpos]
    nlinarith
  · rw [sub_div' hpos.ne', div_lt_iff₀ hpos]
    nlinarith

/-- Exercise 2.1.7 (p. 47), conclusion: when `0 < |T'(u*)| < 1` the convergence is linear, with
any `β ∈ (|T'(u*)|, 1)` as the constant. -/
theorem convergesLinearly_of_abs_deriv_lt_one {T T' : ℝ → ℝ} {u' : ℝ}
    (hT : ∀ x, HasDerivAt T (T' x) x) (hcont : ContinuousAt T' u') (hfix : T u' = u')
    {u : ℕ → ℝ} (hu : ∀ k, u (k + 1) = T (u k)) (hne : ∀ k, u k ≠ u')
    (hlim : Tendsto u atTop (𝓝 u')) (hlt : |T' u'| < 1) : ConvergesLinearly u u' := by
  obtain ⟨β, hβ1, hβ2⟩ := exists_between hlt
  have hβ0 : 0 < β := (abs_nonneg _).trans_lt hβ1
  refine ⟨β, hβ2, le_rfl, hβ0, ?_⟩
  have hev : ∀ᶠ k in atTop, |u (k + 1) - u'| / |u k - u'| < β :=
    (tendsto_error_ratio hT hcont hfix hu hne hlim).eventually (gt_mem_nhds hβ1)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun k hk => ?_⟩
  have hpos : 0 < |u k - u'| := abs_pos.2 (sub_ne_zero.2 (hne k))
  have := hN k hk
  rw [div_lt_iff₀ hpos] at this
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs]
  exact this.le

/-! ### Newton's fixed-point iteration (§2.1.4.1), one dimension -/

/-- The Newton map (2.2) in one dimension: the fixed point of the first-order approximation
`T̂v = Tu + T'(u)(v − u)`, namely `Qu = (Tu − T'(u)u)/(1 − T'(u))`. -/
noncomputable def newtonMap (T T' : ℝ → ℝ) (u : ℝ) : ℝ := (T u - T' u * u) / (1 - T' u)

/-- `Qu` is the fixed point of the linearisation of `T` at `u` (p. 47–48). -/
theorem newtonMap_fixedPt_linearisation (T T' : ℝ → ℝ) {u : ℝ} (hT' : T' u ≠ 1) (v : ℝ) :
    T u + T' u * (v - u) = v ↔ v = newtonMap T T' u := by
  have h : 1 - T' u ≠ 0 := sub_ne_zero.2 (Ne.symm hT')
  rw [newtonMap, eq_div_iff h]
  constructor <;> intro hv <;> linarith

/-- Fixed points of `T` with `T'(u) ≠ 1` are exactly the fixed points of the Newton map `Q`. -/
theorem isFixedPt_newtonMap_iff (T T' : ℝ → ℝ) {u : ℝ} (hT' : T' u ≠ 1) :
    IsFixedPt (newtonMap T T') u ↔ IsFixedPt T u := by
  simp only [IsFixedPt]
  have h : 1 - T' u ≠ 0 := sub_ne_zero.2 (Ne.symm hT')
  rw [newtonMap, div_eq_iff h]
  constructor <;> intro hu <;> linarith

end SargentStachurski.OperatorsFixedPoints
