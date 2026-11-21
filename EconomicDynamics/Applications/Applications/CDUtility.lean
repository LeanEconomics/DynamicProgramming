/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Applications.EUPhelps
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The utility function of the consumption–saving problem

Miao, §8.3, p. 237: "the utility function `u` satisfies the usual conditions: `u′ > 0`,
`u′′ < 0`, `lim_{c→0} u′(c) = ∞`, and `lim_{c→∞} u′(c) = 0`."

`cd_Utility` records these conditions on `(0, ∞)`: `u` has derivative `du` there, `du > 0`,
`du` is strictly decreasing (the content of `u′′ < 0` that is used) and continuous, and the two
Inada limits hold. Consumption is strictly positive throughout this part (`u` may be `−∞` at
`0`, e.g. `log`); see the corrections file.

* `cd_tangent`, `cd_tangent_strict`: `u(c′) ≤ u(c) + u′(c)(c′ − c)`, strictly if `c′ ≠ c`.
* `cd_u_strictMono`, `cd_u_strictConcave`: `u` is strictly increasing and strictly concave.
* `cd_du_surj`, `cd_duInv`: `u′` maps `(0, ∞)` onto `(0, ∞)`; its inverse `(u′)⁻¹` is strictly
  decreasing and continuous (`cd_duInv_cont`), by monotonicity and surjectivity.
* `cd_crraUtility`: CRRA utility `c^{1−γ}/(1−γ)` (`log` at `γ = 1`), `γ > 0`, is a `cd_Utility`
  with `u′(c) = c^{−γ}`.
-/

namespace Miao.Applications

open Filter Topology

/-- Miao, §8.3, p. 237: the "usual conditions" on the utility function, on `(0, ∞)`:
`u′ = du > 0`, `u′` strictly decreasing (`u′′ < 0`) and continuous, `u′(0+) = ∞`,
`u′(∞) = 0`. -/
structure cd_Utility where
  /-- The period utility function. -/
  u : ℝ → ℝ
  /-- Its derivative on `(0, ∞)`. -/
  du : ℝ → ℝ
  hasDerivAt : ∀ c, 0 < c → HasDerivAt u (du c) c
  du_pos : ∀ c, 0 < c → 0 < du c
  du_anti : StrictAntiOn du (Set.Ioi 0)
  du_cont : ContinuousOn du (Set.Ioi 0)
  inada_zero : Tendsto du (𝓝[>] 0) atTop
  inada_top : Tendsto du atTop (𝓝 0)

namespace cd_Utility

variable (U : cd_Utility)

/-- Miao, p. 237 (`u′′ < 0`): the tangent-line inequality `u(c′) ≤ u(c) + u′(c)(c′ − c)` for
`c, c′ > 0`, strict when `c′ ≠ c` (mean value theorem and `u′` strictly decreasing). -/
theorem cd_tangent_strict {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (hne : c' ≠ c) :
    U.u c' < U.u c + U.du c * (c' - c) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hcont : ContinuousOn U.u (Set.Icc c' c) := fun z hz =>
      (U.hasDerivAt z (lt_of_lt_of_le hc' hz.1)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope U.u U.du h hcont
      (fun z hz => U.hasDerivAt z (lt_trans hc' hz.1))
    have hξ0 : 0 < ξ := lt_trans hc' hξ.1
    have hlt : U.du c < U.du ξ := U.du_anti (Set.mem_Ioi.2 hξ0) (Set.mem_Ioi.2 hc) hξ.2
    have hpos : 0 < c - c' := sub_pos.2 h
    have e : U.u c - U.u c' = U.du ξ * (c - c') := by
      rw [hξeq]; field_simp
    nlinarith
  · have hcont : ContinuousOn U.u (Set.Icc c c') := fun z hz =>
      (U.hasDerivAt z (lt_of_lt_of_le hc hz.1)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope U.u U.du h hcont
      (fun z hz => U.hasDerivAt z (lt_trans hc hz.1))
    have hξ0 : 0 < ξ := lt_trans hc hξ.1
    have hlt : U.du ξ < U.du c := U.du_anti (Set.mem_Ioi.2 hc) (Set.mem_Ioi.2 hξ0) hξ.1
    have hpos : 0 < c' - c := sub_pos.2 h
    have e : U.u c' - U.u c = U.du ξ * (c' - c) := by
      rw [hξeq]; field_simp
    nlinarith

/-- Miao, p. 237: the tangent-line inequality `u(c′) ≤ u(c) + u′(c)(c′ − c)` for `c, c′ > 0`. -/
theorem cd_tangent {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    U.u c' ≤ U.u c + U.du c * (c' - c) := by
  by_cases h : c' = c
  · subst h; simp
  · exact (U.cd_tangent_strict hc hc' h).le

/-- Miao, p. 237 (`u′ > 0`): `u` is strictly increasing on `(0, ∞)`. -/
theorem cd_u_strictMono : StrictMonoOn U.u (Set.Ioi 0) := by
  intro c hc c' hc' h
  have hc0 : (0 : ℝ) < c := hc
  have hc0' : (0 : ℝ) < c' := hc'
  have h1 := U.cd_tangent hc0' hc0
  have h2 := U.du_pos c' hc0'
  have : U.du c' * (c - c') < 0 := mul_neg_of_pos_of_neg h2 (sub_neg.2 h)
  linarith

/-- Miao, p. 237 (`u′′ < 0`): `u` is strictly concave on `(0, ∞)`. -/
theorem cd_u_strictConcave : StrictConcaveOn ℝ (Set.Ioi 0) U.u := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) ?_ ?_
  · exact fun z hz => (U.hasDerivAt z hz).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [(U.hasDerivAt a ha).deriv, (U.hasDerivAt b hb).deriv]
    exact U.du_anti ha hb hab

/-- Miao, p. 237 (Inada conditions): `u′` maps `(0, ∞)` onto `(0, ∞)`. -/
theorem cd_du_surj {v : ℝ} (hv : 0 < v) : ∃ c, 0 < c ∧ U.du c = v := by
  have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), v < U.du c := U.inada_zero.eventually_gt_atTop v
  have h1' : ∀ᶠ c in 𝓝[>] (0 : ℝ), 0 < c := self_mem_nhdsWithin
  obtain ⟨c₁, hc₁, hc₁0⟩ := (h1.and h1').exists
  have h2 : ∀ᶠ c in atTop, U.du c < v := U.inada_top.eventually (gt_mem_nhds hv)
  obtain ⟨c₂, hc₂, hc₂le⟩ := (h2.and (eventually_ge_atTop c₁)).exists
  have hcont : ContinuousOn U.du (Set.Icc c₁ c₂) := U.du_cont.mono fun z hz =>
    Set.mem_Ioi.2 (lt_of_lt_of_le hc₁0 hz.1)
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc' hc₂le hcont ⟨hc₂.le, hc₁.le⟩
  exact ⟨c, lt_of_lt_of_le hc₁0 hc.1, hcv⟩

/-- Miao, p. 241: the inverse `(u′)⁻¹` of marginal utility on `(0, ∞)` (junk value `1`
elsewhere). -/
noncomputable def cd_duInv (v : ℝ) : ℝ :=
  if h : 0 < v then Classical.choose (U.cd_du_surj h) else 1

/-- `(u′)⁻¹(v) > 0`. -/
theorem cd_duInv_pos (v : ℝ) : 0 < U.cd_duInv v := by
  unfold cd_duInv
  split_ifs with h
  · exact (Classical.choose_spec (U.cd_du_surj h)).1
  · exact one_pos

/-- `u′((u′)⁻¹(v)) = v` for `v > 0`. -/
theorem cd_du_duInv {v : ℝ} (hv : 0 < v) : U.du (U.cd_duInv v) = v := by
  simp only [cd_duInv, hv, ↓reduceDIte]
  exact (Classical.choose_spec (U.cd_du_surj hv)).2

/-- `u′` is injective on `(0, ∞)`. -/
theorem cd_du_inj {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (h : U.du c = U.du c') : c = c' :=
  U.du_anti.injOn hc hc' h

/-- `(u′)⁻¹(u′(c)) = c` for `c > 0`. -/
theorem cd_duInv_du {c : ℝ} (hc : 0 < c) : U.cd_duInv (U.du c) = c :=
  U.cd_du_inj (U.cd_duInv_pos _) hc (U.cd_du_duInv (U.du_pos c hc))

/-- `(u′)⁻¹` is strictly decreasing on `(0, ∞)`. -/
theorem cd_duInv_anti : StrictAntiOn U.cd_duInv (Set.Ioi 0) := by
  intro v hv v' hv' h
  have hv0 : (0 : ℝ) < v := hv
  have hv0' : (0 : ℝ) < v' := hv'
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · have := U.du_anti (Set.mem_Ioi.2 (U.cd_duInv_pos v)) (Set.mem_Ioi.2 (U.cd_duInv_pos v')) hlt
    rw [U.cd_du_duInv hv0, U.cd_du_duInv hv0'] at this
    linarith
  · have := congrArg U.du heq
    rw [U.cd_du_duInv hv0, U.cd_du_duInv hv0'] at this
    linarith

/-- `(u′)⁻¹` is continuous on `(0, ∞)`: it is monotone and maps `(0, ∞)` onto `(0, ∞)`. -/
theorem cd_duInv_cont : ContinuousOn U.cd_duInv (Set.Ioi 0) := by
  intro v hv
  have hv0 : (0 : ℝ) < v := hv
  have hmono : MonotoneOn (fun w => -U.cd_duInv w) (Set.Ioi 0) := fun a ha b hb hab => by
    rcases hab.lt_or_eq with h | h
    · exact neg_le_neg (U.cd_duInv_anti ha hb h).le
    · rw [h]
  have himage : (fun w => -U.cd_duInv w) '' Set.Ioi 0 = Set.Iio 0 := by
    ext z
    constructor
    · rintro ⟨w, _, rfl⟩
      exact Set.mem_Iio.2 (neg_lt_zero.2 (U.cd_duInv_pos w))
    · intro hz
      have hz' : 0 < -z := neg_pos.2 hz
      refine ⟨U.du (-z), Set.mem_Ioi.2 (U.du_pos _ hz'), ?_⟩
      simp only [U.cd_duInv_du hz', neg_neg]
  have hc : ContinuousAt (fun w => -U.cd_duInv w) v := by
    refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono (Ioi_mem_nhds hv0) ?_
    rw [himage]
    exact Iio_mem_nhds (neg_lt_zero.2 (U.cd_duInv_pos v))
  have : ContinuousAt U.cd_duInv v := by
    have h2 := hc.neg
    have e : (-fun w => -U.cd_duInv w) = U.cd_duInv := funext fun w => neg_neg _
    rw [e] at h2
    exact h2
  exact this.continuousWithinAt

end cd_Utility

/-- CRRA marginal utility `c^{−γ}` is strictly decreasing on `(0, ∞)` for `γ > 0`. -/
theorem cd_rpow_neg_strictAnti {γ : ℝ} (hγ : 0 < γ) :
    StrictAntiOn (fun c : ℝ => c ^ (-γ)) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact Real.rpow_lt_rpow_of_neg ha hab (neg_neg_of_pos hγ)

/-- Miao, p. 237 and Exercise 8.8: CRRA utility `c^{1−γ}/(1−γ)` (`log c` at `γ = 1`), `γ > 0`,
satisfies the usual conditions, with `u′(c) = c^{−γ}`. -/
noncomputable def cd_crraUtility {γ : ℝ} (hγ : 0 < γ) : cd_Utility where
  u := cs_crra γ
  du := fun c => c ^ (-γ)
  hasDerivAt := fun _ hc => eu_crra_hasDerivAt hc
  du_pos := fun _ hc => Real.rpow_pos_of_pos hc _
  du_anti := cd_rpow_neg_strictAnti hγ
  du_cont := fun _ hc =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hc))).continuousWithinAt
  inada_zero := tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hγ)
  inada_top := tendsto_rpow_neg_atTop hγ

/-- The CRRA instance has `u = cs_crra γ`. -/
theorem cd_crraUtility_u {γ : ℝ} (hγ : 0 < γ) : (cd_crraUtility hγ).u = cs_crra γ := rfl

/-- The CRRA instance has `u′(c) = c^{−γ}`. -/
theorem cd_crraUtility_du {γ : ℝ} (hγ : 0 < γ) (c : ℝ) : (cd_crraUtility hγ).du c = c ^ (-γ) :=
  rfl

end Miao.Applications
