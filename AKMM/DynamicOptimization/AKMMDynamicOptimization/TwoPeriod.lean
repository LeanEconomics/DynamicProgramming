/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicDynamics.GrowthStability

/-!
# The two-period consumption–saving model

AKMM, §4.2.1, pp. 99–100. Endowments `w₀, w₁`, a constant interest rate `r`, no initial assets
and a borrowing constraint `a₁ ≥ 0`; `c₀ = w₀ − a₁` and `c₁ = w₁ + (1 + r)a₁`.

* The lifetime budget constraint `c₀ + c₁/(1 + r) = w₀ + w₁/(1 + r)` (`twoPeriod_lifetime_budget`).
* The Kuhn–Tucker conditions (4.4)–(4.6) are sufficient for a maximum when `u` is concave
  (`eq_4_4_to_4_6`), and with `λ = 0` they give the Euler equation
  `u'(c₀) = β(1 + r)u'(c₁)` (`twoPeriod_euler`).
* With a decreasing endowment `w₀ > w₁`, strictly decreasing marginal utility and `β(1 + r) ≥ 1`,
  the borrowing constraint does not bind at a maximum (`twoPeriod_interior`).
* When `β(1 + r) = 1`: `c₀ = c₁ = (w₀ + βw₁)/(1 + β)` and `a₁ = (w₀ − w₁)/(2 + r) > 0`
  (`twoPeriod_closed_form`, `twoPeriod_closed_form_optimal`).

The concavity tools (`tangent_le`) are imported from SLP `DeterministicDynamics`.
-/

namespace AKMM.DynamicOptimization

open Filter Topology StokeyLucasPrescott.DeterministicDynamics

/-- The two-period objective as a function of saving `a₁`:
`u(w₀ − a₁) + βu(w₁ + (1 + r)a₁)`. -/
noncomputable def twoPeriodValue (u : ℝ → ℝ) (β r w0 w1 a : ℝ) : ℝ :=
  u (w0 - a) + β * u (w1 + (1 + r) * a)

/-- AKMM, p. 99: combining `c₀ = w₀ − a₁` and `c₁ = w₁ + (1 + r)a₁` gives the lifetime budget
constraint `c₀ + c₁/(1 + r) = w₀ + w₁/(1 + r)`. -/
theorem twoPeriod_lifetime_budget {w0 w1 r a1 c0 c1 : ℝ} (hr : -1 < r) (h0 : c0 = w0 - a1)
    (h1 : c1 = w1 + (1 + r) * a1) : c0 + c1 / (1 + r) = w0 + w1 / (1 + r) := by
  have : (1 + r) ≠ 0 := by linarith
  rw [h0, h1]
  field_simp
  ring

/-- **AKMM, (4.4)–(4.6), p. 100: the Kuhn–Tucker conditions are sufficient.** Let `u` be concave
on `[0, ∞)` with derivative `u'(cᵢ)` at the candidate consumptions. If multipliers `μ` and
`λ ≥ 0` satisfy `u'(c₀) − μ − λ = 0`, `βu'(c₁) − μ/(1 + r) = 0` and `λ(w₀ − c₀) = 0` with
`w₀ − c₀ ≥ 0`, then `a₁ = w₀ − c₀` maximizes `u(w₀ − a) + βu(w₁ + (1 + r)a)` over all `a ≥ 0`
with nonnegative consumption. -/
theorem eq_4_4_to_4_6 {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Set.Ici 0) u) {β r w0 w1 a1 d0 d1 μ lam : ℝ}
    (hβ : 0 ≤ β) (hr : -1 < r) (hc0 : 0 ≤ w0 - a1) (hc1 : 0 ≤ w1 + (1 + r) * a1)
    (hd0 : HasDerivAt u d0 (w0 - a1)) (hd1 : HasDerivAt u d1 (w1 + (1 + r) * a1))
    (h44 : d0 - μ - lam = 0) (h45 : β * d1 - μ / (1 + r) = 0)
    (h46 : lam * a1 = 0) (ha1 : 0 ≤ a1) (hlam : 0 ≤ lam) {a : ℝ} (ha : 0 ≤ a)
    (hca0 : 0 ≤ w0 - a) (hca1 : 0 ≤ w1 + (1 + r) * a) :
    twoPeriodValue u β r w0 w1 a ≤ twoPeriodValue u β r w0 w1 a1 := by
  have t0 := tangent_le hu (Set.mem_Ici.2 hc0) (Set.mem_Ici.2 hca0) hd0
  have t1 := tangent_le hu (Set.mem_Ici.2 hc1) (Set.mem_Ici.2 hca1) hd1
  have hr' : (0 : ℝ) < 1 + r := by linarith
  have hμ : μ = β * d1 * (1 + r) := by field_simp at h45; linarith
  unfold twoPeriodValue
  have key : β * u (w1 + (1 + r) * a) ≤
      β * u (w1 + (1 + r) * a1) + β * d1 * ((1 + r) * (a - a1)) := by
    have := mul_le_mul_of_nonneg_left t1 hβ
    nlinarith
  nlinarith [mul_nonneg hlam ha]

/-- AKMM, p. 100: with `λ = 0` (an interior solution), (4.4) and (4.5) give the Euler equation
`u'(c₀) = β(1 + r)u'(c₁)`. -/
theorem twoPeriod_euler {β r d0 d1 μ : ℝ} (hr : -1 < r) (h44 : d0 - μ - 0 = 0)
    (h45 : β * d1 - μ / (1 + r) = 0) : d0 = β * (1 + r) * d1 := by
  have : (1 + r) ≠ 0 := by linarith
  field_simp at h45
  linarith

/-- AKMM, p. 100: "a decreasing wage path `w₀ > w₁` and strictly decreasing marginal utility can
guarantee the solution to be interior when `β(1 + r) ≥ 1`". If `u' > 0` is strictly decreasing
on `(0, ∞)`, `0 < w₁ < w₀` and `β(1 + r) ≥ 1`, then `a₁ = 0` is not a maximizer over `[0, w₀]`. -/
theorem twoPeriod_interior {u u' : ℝ → ℝ} (hd : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) (hanti : StrictAntiOn u' (Set.Ioi 0)) {β r w0 w1 : ℝ}
    (hw1 : 0 < w1) (hw : w1 < w0) (hβr : 1 ≤ β * (1 + r)) :
    ∃ a, 0 < a ∧ a < w0 ∧ twoPeriodValue u β r w0 w1 0 < twoPeriodValue u β r w0 w1 a := by
  have hw0 : 0 < w0 := hw1.trans hw
  obtain ⟨D, hDdef⟩ : ∃ D, D = -u' w0 + β * (1 + r) * u' w1 := ⟨_, rfl⟩
  have hD : 0 < D := by
    rw [hDdef]
    have h1 : u' w0 < u' w1 := hanti (Set.mem_Ioi.2 hw1) (Set.mem_Ioi.2 hw0) hw
    have h2 := hpos w1 hw1
    nlinarith
  have hV : HasDerivAt (twoPeriodValue u β r w0 w1) D 0 := by
    have e0 : HasDerivAt (fun a : ℝ => w0 - a) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub w0
    have e1 : HasDerivAt (fun a : ℝ => w1 + (1 + r) * a) (1 + r) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r)).const_add w1
    have h0 : HasDerivAt (fun a => u (w0 - a)) (u' w0 * -1) 0 := by
      have := hd w0 hw0
      exact (show HasDerivAt u (u' w0) (w0 - 0) by simpa using this).comp 0 e0
    have h1 : HasDerivAt (fun a => u (w1 + (1 + r) * a)) (u' w1 * (1 + r)) 0 := by
      have := hd w1 hw1
      exact (show HasDerivAt u (u' w1) (w1 + (1 + r) * 0) by simpa using this).comp 0 e1
    have := h0.add (h1.const_mul β)
    convert this using 1
    · funext a; simp [twoPeriodValue]
    · rw [hDdef]; ring
  have hslope := hV.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (twoPeriodValue u β r w0 w1 (0 + t) -
      twoPeriodValue u β r w0 w1 0) ∧ t < w0 := by
    refine (hslope.eventually (lt_mem_nhds hD)).and ?_
    exact nhdsWithin_le_nhds (gt_mem_nhds hw0)
  have hev' := hev.and self_mem_nhdsWithin
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ := hev'.exists
  refine ⟨t, ht, h2, ?_⟩
  rw [zero_add, smul_eq_mul] at h1
  have := (pos_iff_pos_of_mul_pos h1).1 (inv_pos.2 ht)
  linarith

/-- AKMM, p. 100: when `β(1 + r) = 1`, the Euler equation with strictly decreasing marginal
utility gives `c₀ = c₁`, hence `a₁ = (w₀ − w₁)/(2 + r)` and `c₀ = c₁ = (w₀ + βw₁)/(1 + β)`; the
saving is positive exactly when `w₀ > w₁`. -/
theorem twoPeriod_closed_form {u' : ℝ → ℝ} (hinj : Set.InjOn u' (Set.Ioi 0)) {β r w0 w1 a1 : ℝ}
    (hr : -1 < r) (hβr : β * (1 + r) = 1) (hc0 : 0 < w0 - a1) (hc1 : 0 < w1 + (1 + r) * a1)
    (heuler : u' (w0 - a1) = β * (1 + r) * u' (w1 + (1 + r) * a1)) :
    w0 - a1 = w1 + (1 + r) * a1 ∧ a1 = (w0 - w1) / (2 + r) ∧
      w0 - a1 = (w0 + β * w1) / (1 + β) ∧ (0 < a1 ↔ w1 < w0) := by
  rw [hβr, one_mul] at heuler
  have he := hinj hc0 hc1 heuler
  have h2r : (2 + r) ≠ 0 := by linarith
  have ha : a1 = (w0 - w1) / (2 + r) := by field_simp; linarith
  have h1r : (1 + r) ≠ 0 := by linarith
  have hβ : β = 1 / (1 + r) := by rw [eq_div_iff h1r]; exact hβr
  refine ⟨he, ha, ?_, ?_⟩
  · have hβ0 : 0 < β := by rw [hβ]; exact div_pos one_pos (by linarith)
    have h1β : (1 + β) ≠ 0 := by linarith
    rw [ha, eq_div_iff h1β, hβ]
    field_simp
    ring
  · rw [ha, div_pos_iff_of_pos_right (by linarith), sub_pos]

/-- AKMM, p. 100: when `β(1 + r) = 1` and `w₀ ≥ w₁`, the plan `a₁ = (w₀ − w₁)/(2 + r)` with
`c₀ = c₁` is optimal for concave `u` (the Kuhn–Tucker conditions hold with `λ = 0`). -/
theorem twoPeriod_closed_form_optimal {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Set.Ici 0) u) {β r w0 w1 d : ℝ}
    (hβ : 0 ≤ β) (hr : -1 < r) (hβr : β * (1 + r) = 1) (hw : w1 ≤ w0) (hw1 : 0 ≤ w1)
    (hd : HasDerivAt u d (((1 + r) * w0 + w1) / (2 + r))) {a : ℝ} (ha : 0 ≤ a)
    (hca0 : 0 ≤ w0 - a) (hca1 : 0 ≤ w1 + (1 + r) * a) :
    twoPeriodValue u β r w0 w1 a ≤ twoPeriodValue u β r w0 w1 ((w0 - w1) / (2 + r)) := by
  have h2r : (0 : ℝ) < 2 + r := by linarith
  have hc0 : w0 - (w0 - w1) / (2 + r) = ((1 + r) * w0 + w1) / (2 + r) := by
    field_simp; ring
  have hc1 : w1 + (1 + r) * ((w0 - w1) / (2 + r)) = ((1 + r) * w0 + w1) / (2 + r) := by
    field_simp; ring
  have hpos : 0 ≤ ((1 + r) * w0 + w1) / (2 + r) :=
    div_nonneg (by nlinarith) h2r.le
  refine eq_4_4_to_4_6 hu hβ hr (by rw [hc0]; exact hpos) (by rw [hc1]; exact hpos)
    (by rw [hc0]; exact hd) (by rw [hc1]; exact hd) (μ := d) (lam := 0) (by ring) ?_ (by ring)
    (div_nonneg (by linarith) h2r.le) le_rfl ha hca0 hca1
  have : (1 + r) ≠ 0 := by linarith
  field_simp
  linear_combination d * hβr

end AKMM.DynamicOptimization
