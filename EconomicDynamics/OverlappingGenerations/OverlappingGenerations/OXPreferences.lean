/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Preferences of the Samuelson (1958) exchange economy

Miao, §16.1, p. 530: a generation-`t` agent has utility `u(c_t^t) + βu(c_{t+1}^t)` with
`β ∈ (0, 1]`, `u' > 0`, `u'' < 0` and `lim_{c→0} u'(c) = ∞`.

* `OXPrefs`: the period utility `u` and its derivative `u'` (field `ox_du`) on `(0, ∞)`,
  `u' > 0`, `u'` strictly decreasing (the content of `u'' < 0` used in §16.1), `u'`
  continuous, and the Inada condition. The concrete instance `ox_logPrefs` (`u = ln`) shows the
  hypotheses are satisfiable.
* Concavity consequences used throughout the section: the (strict) tangent-line inequality
  (`ox_tangent`, `ox_tangent_strict`), strict monotonicity of `u` (`ox_u_strictMonoOn`), a
  uniform chord bound (`ox_chord`), the first-order condition at a local maximum along a budget
  line (`ox_foc`), and sufficiency of the Euler equation on a budget line (`ox_line_optimal`,
  `ox_line_optimal_strict`).

**Departure.** Utility is defined on `(0, ∞)`: consumption is required to be positive
throughout the chapter (with the Inada condition zero consumption is never chosen).
-/

open Filter Topology

namespace Miao.OverlappingGenerations

/-- Miao, §16.1, p. 530: period utility `u` with derivative `u'` on `(0, ∞)`, `u' > 0`, `u'`
strictly decreasing (from `u'' < 0`), `u'` continuous, `lim_{c → 0} u'(c) = ∞`, and the discount
factor `β ∈ (0, 1]`. -/
structure OXPrefs where
  /-- The period utility `u`. -/
  ox_u : ℝ → ℝ
  /-- Its derivative `u'`. -/
  ox_du : ℝ → ℝ
  /-- The discount factor. -/
  ox_β : ℝ
  ox_β_pos : 0 < ox_β
  ox_β_le : ox_β ≤ 1
  ox_hasDeriv : ∀ c, 0 < c → HasDerivAt ox_u (ox_du c) c
  ox_du_pos : ∀ c, 0 < c → 0 < ox_du c
  ox_du_anti : StrictAntiOn ox_du (Set.Ioi 0)
  ox_du_cont : ContinuousOn ox_du (Set.Ioi 0)
  ox_inada : Tendsto ox_du (𝓝[>] 0) atTop

/-- Logarithmic utility `u = ln`, `u'(c) = 1/c`: a concrete instance of `OXPrefs`. -/
noncomputable def ox_logPrefs (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) : OXPrefs where
  ox_u := Real.log
  ox_du := fun c => c⁻¹
  ox_β := β
  ox_β_pos := hβ
  ox_β_le := hβ1
  ox_hasDeriv := fun _ hc => Real.hasDerivAt_log hc.ne'
  ox_du_pos := fun _ hc => inv_pos.2 hc
  ox_du_anti := fun _ hx _ _ hxy => inv_strictAnti₀ (Set.mem_Ioi.1 hx) hxy
  ox_du_cont := continuousOn_inv₀.mono fun _ hx => (Set.mem_Ioi.1 hx).ne'
  ox_inada := tendsto_inv_nhdsGT_zero

/-- Miao, p. 530: the logarithmic instance has `u = ln` and `u'(c) = 1/c`. -/
theorem ox_logPrefs_spec (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (ox_logPrefs β hβ hβ1).ox_u = Real.log ∧ (ox_logPrefs β hβ hβ1).ox_du = (fun c => c⁻¹) ∧
      (ox_logPrefs β hβ hβ1).ox_β = β :=
  ⟨rfl, rfl, rfl⟩

namespace OXPrefs

variable (P : OXPrefs)

/-- Lifetime utility `u(c₁) + βu(c₂)` of a two-period-lived agent (Miao, p. 530). -/
def ox_U (c1 c2 : ℝ) : ℝ := P.ox_u c1 + P.ox_β * P.ox_u c2

/-- Strict concavity of `u` (Miao, p. 530, `u'' < 0`): for `x, y > 0`, `y ≠ x`,
`u(y) < u(x) + u'(x)(y − x)`. -/
theorem ox_tangent_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hne : y ≠ x) :
    P.ox_u y < P.ox_u x + P.ox_du x * (y - x) := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope P.ox_u P.ox_du hlt
      (fun z hz => (P.ox_hasDeriv z (by linarith [hz.1])).continuousAt.continuousWithinAt)
      (fun z hz => P.ox_hasDeriv z (by linarith [hz.1]))
    have hc0 : 0 < c := by linarith [hc.1]
    have hdu : P.ox_du x < P.ox_du c := P.ox_du_anti hc0 hx hc.2
    have hxy : 0 < x - y := by linarith
    rw [eq_div_iff hxy.ne'] at hcd
    nlinarith
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope P.ox_u P.ox_du hlt
      (fun z hz => (P.ox_hasDeriv z (by linarith [hz.1])).continuousAt.continuousWithinAt)
      (fun z hz => P.ox_hasDeriv z (by linarith [hz.1]))
    have hc0 : 0 < c := by linarith [hc.1]
    have hdu : P.ox_du c < P.ox_du x := P.ox_du_anti hx hc0 hc.1
    have hxy : 0 < y - x := by linarith
    rw [eq_div_iff hxy.ne'] at hcd
    nlinarith

/-- Concavity of `u`: `u(y) ≤ u(x) + u'(x)(y − x)` for `x, y > 0`. -/
theorem ox_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    P.ox_u y ≤ P.ox_u x + P.ox_du x * (y - x) := by
  rcases eq_or_ne y x with h | h
  · subst h; simp
  · exact (P.ox_tangent_strict hx hy h).le

/-- `u' > 0`: `u` is strictly increasing on `(0, ∞)`. -/
theorem ox_u_strictMonoOn : StrictMonoOn P.ox_u (Set.Ioi 0) := by
  intro x hx y hy hxy
  have h := P.ox_tangent_strict (Set.mem_Ioi.1 hy) (Set.mem_Ioi.1 hx) hxy.ne
  have hd := P.ox_du_pos y (Set.mem_Ioi.1 hy)
  nlinarith

/-- `u` strictly increasing, in the form used for consumption comparisons. -/
theorem ox_u_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) : P.ox_u x < P.ox_u y :=
  P.ox_u_strictMonoOn hx (show (0 : ℝ) < y by linarith) hxy

/-- `u'` strictly decreasing, in the form used for marginal-utility comparisons. -/
theorem ox_du_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) : P.ox_du y < P.ox_du x :=
  P.ox_du_anti hx (show (0 : ℝ) < y by linarith) hxy

/-- A uniform chord bound from strict concavity: for `0 < ε₀ < c` there is `κ > u'(c)` with
`u(c) − u(c − ε) ≥ κε` for every `ε ∈ [ε₀, c)`. -/
theorem ox_chord {c ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀c : ε₀ < c) :
    ∃ κ, P.ox_du c < κ ∧ ∀ ε, ε₀ ≤ ε → ε < c → κ * ε ≤ P.ox_u c - P.ox_u (c - ε) := by
  have hc : 0 < c := by linarith
  have hc0 : 0 < c - ε₀ := by linarith
  set a := P.ox_du (c - ε₀)
  set D := P.ox_u c - P.ox_u (c - ε₀)
  have ha : P.ox_du c < a := P.ox_du_lt hc0 (by linarith)
  have hD : P.ox_du c * ε₀ < D := by
    have := P.ox_tangent_strict hc hc0 (by linarith)
    simp only [D]; nlinarith
  refine ⟨min (D / ε₀) a, lt_min ((lt_div_iff₀ hε₀).2 hD) ha, fun ε hε hεc => ?_⟩
  have hce : 0 < c - ε := by linarith
  have ht := P.ox_tangent hc0 hce
  have h1 : min (D / ε₀) a * ε₀ ≤ D := by
    have := min_le_left (D / ε₀) a
    calc min (D / ε₀) a * ε₀ ≤ D / ε₀ * ε₀ := mul_le_mul_of_nonneg_right this hε₀.le
      _ = D := div_mul_cancel₀ D hε₀.ne'
  have h2 : min (D / ε₀) a * (ε - ε₀) ≤ a * (ε - ε₀) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
  have : P.ox_u (c - ε) ≤ P.ox_u (c - ε₀) - a * (ε - ε₀) := by
    have : c - ε - (c - ε₀) = -(ε - ε₀) := by ring
    rw [this] at ht; linarith
  nlinarith

/-- Positivity of an affine function near `0`: if `0 < a` then `0 < a + bs` for `s` near `0`. -/
theorem ox_eventually_pos (a b : ℝ) (ha : 0 < a) : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < a + b * s := by
  have : Tendsto (fun s : ℝ => a + b * s) (𝓝 0) (𝓝 (a + b * 0)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).tendsto 0)
  rw [mul_zero, add_zero] at this
  exact this.eventually (lt_mem_nhds ha)

/-- The first-order condition along a budget line: if moving `s` units along the line
`(c₁ − as, c₂ + bs)` never raises utility for `s` near `0`, then `a u'(c₁) = βb u'(c₂)`. -/
theorem ox_foc {c1 c2 a b : ℝ} (h1 : 0 < c1) (h2 : 0 < c2)
    (hmax : ∀ᶠ s in 𝓝 (0 : ℝ), P.ox_U (c1 - a * s) (c2 + b * s) ≤ P.ox_U c1 c2) :
    a * P.ox_du c1 = P.ox_β * b * P.ox_du c2 := by
  have hl1 : HasDerivAt (fun s : ℝ => c1 - a * s) (-a) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a |>.const_sub c1
  have hl2 : HasDerivAt (fun s : ℝ => c2 + b * s) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul b).const_add c2
  have hu1 : HasDerivAt P.ox_u (P.ox_du c1) ((fun s : ℝ => c1 - a * s) 0) := by
    simpa using P.ox_hasDeriv c1 h1
  have hu2 : HasDerivAt P.ox_u (P.ox_du c2) ((fun s : ℝ => c2 + b * s) 0) := by
    simpa using P.ox_hasDeriv c2 h2
  have hphi : HasDerivAt (fun s => P.ox_U (c1 - a * s) (c2 + b * s))
      (P.ox_du c1 * -a + P.ox_β * (P.ox_du c2 * b)) 0 :=
    (hu1.comp 0 hl1).add ((hu2.comp 0 hl2).const_mul P.ox_β)
  have hloc : IsLocalMax (fun s => P.ox_U (c1 - a * s) (c2 + b * s)) 0 := by
    filter_upwards [hmax] with s hs
    simpa using hs
  have := hloc.hasDerivAt_eq_zero hphi
  linarith

/-- Sufficiency of the Euler equation (Miao, (16.4)): if `u'(c₁) = βRu'(c₂)` then `(c₁, c₂)`
maximises `u(c₁') + βu(c₂')` over the budget line `c₁' + c₂'/R ≤ c₁ + c₂/R`. -/
theorem ox_line_optimal {c1 c2 R c1' c2' : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (hR : 0 < R)
    (heul : P.ox_du c1 = P.ox_β * R * P.ox_du c2) (h1' : 0 < c1') (h2' : 0 < c2')
    (hline : c1' + c2' / R ≤ c1 + c2 / R) : P.ox_U c1' c2' ≤ P.ox_U c1 c2 := by
  have t1 := P.ox_tangent h1 h1'
  have t2 := mul_le_mul_of_nonneg_left (P.ox_tangent h2 h2') P.ox_β_pos.le
  have hK : R * ((c1' + c2' / R) - (c1 + c2 / R)) = R * (c1' - c1) + (c2' - c2) := by
    field_simp; ring
  have hpos : 0 ≤ P.ox_β * P.ox_du c2 := (mul_pos P.ox_β_pos (P.ox_du_pos c2 h2)).le
  have hneg : P.ox_β * P.ox_du c2 * (R * (c1' - c1) + (c2' - c2)) ≤ 0 := by
    rw [← hK]
    exact mul_nonpos_of_nonneg_of_nonpos hpos
      (mul_nonpos_of_nonneg_of_nonpos hR.le (by linarith))
  rw [heul] at t1
  unfold ox_U
  nlinarith

/-- The strict version of `ox_line_optimal`: any other point of the budget set is strictly
worse. -/
theorem ox_line_optimal_strict {c1 c2 R c1' c2' : ℝ} (h1 : 0 < c1) (h2 : 0 < c2) (hR : 0 < R)
    (heul : P.ox_du c1 = P.ox_β * R * P.ox_du c2) (h1' : 0 < c1') (h2' : 0 < c2')
    (hline : c1' + c2' / R ≤ c1 + c2 / R) (hne : c1' ≠ c1 ∨ c2' ≠ c2) :
    P.ox_U c1' c2' < P.ox_U c1 c2 := by
  have hK : R * ((c1' + c2' / R) - (c1 + c2 / R)) = R * (c1' - c1) + (c2' - c2) := by
    field_simp; ring
  have hpos : 0 < P.ox_β * P.ox_du c2 := mul_pos P.ox_β_pos (P.ox_du_pos c2 h2)
  have hneg : P.ox_β * P.ox_du c2 * (R * (c1' - c1) + (c2' - c2)) ≤ 0 := by
    rw [← hK]
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le
      (mul_nonpos_of_nonneg_of_nonpos hR.le (by linarith))
  unfold ox_U
  rcases hne with hne | hne
  · have t1 := P.ox_tangent_strict h1 h1' hne
    have t2 := mul_le_mul_of_nonneg_left (P.ox_tangent h2 h2') P.ox_β_pos.le
    rw [heul] at t1
    nlinarith
  · have t1 := P.ox_tangent h1 h1'
    have t2 := mul_lt_mul_of_pos_left (P.ox_tangent_strict h2 h2' hne) P.ox_β_pos
    rw [heul] at t1
    nlinarith

end OXPrefs

end Miao.OverlappingGenerations
