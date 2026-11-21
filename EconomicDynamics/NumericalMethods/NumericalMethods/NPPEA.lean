/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NPEuler
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Monotone.Basic

/-!
# The parameterized expectations approach: irreversible investment

Miao, *Economic Dynamics in Discrete Time*, §11.6.2 (pp. 381–383), (11.13)–(11.14).

With the irreversibility constraint `K' ≥ (1 − δ)K` (11.13) the first-order
conditions are `u'(f − g) − h = β∫m q`, `h(g − (1 − δ)k) = 0`,
`g − (1 − δ)k ≥ 0`, `h ≥ 0`, with
`m(k', z'; g, h) = u'(f(k', z') − g(k', z'))f'(k', z') − h(k', z')(1 − δ)`.

* `np_irreversible_kkt`: these Kuhn–Tucker conditions follow from the
  maximisation in the Bellman equation, with multiplier
  `h = u'(c) − βW'(g)`.
* `eq_11_14_envelope`: `m` is the derivative of the value function, as the text
  says ("`m` is the derivative of the value function").
* `eq_11_14_pos`: for the Cobb–Douglas technology `f(k, z) = zk^α + (1 − δ)k`,
  `m = u'(c)αzk^{α−1} + (1 − δ)e > 0` when `e = u'(c) − h ≥ 0`, which is the
  inequality in (11.14).
* PEA (p. 383): for any value `e > 0` of the conditional expectation, the
  formulas `g = max{(1 − δ)k, f − (u')⁻¹(e)}`, `h = u'(f − g) − e` give the unique
  solution of the system `u'(f − g) − h = e`, `h(g − (1 − δ)k) = 0`,
  `g ≥ (1 − δ)k`, `h ≥ 0` (`np_pea_kkt`, `np_pea_kkt_unique`). So the functional
  equation `F(e) = 0` is equivalent to the original first-order conditions.

The sufficiency of these conditions together with the transversality condition
(p. 382) is stated without proof in the text and is not formalised here.
-/

namespace Miao.NumericalMethods.NP

open Filter Topology

/-- The Kuhn–Tucker conditions under the irreversibility constraint (11.13) (Miao, p. 382),
derived from the Bellman maximisation `max_{(1−δ)k ≤ k' < f(k)} u(f(k) − k') + βW(k')` at an optimum
`g₀`: with `h = u'(c₀) − βW'(g₀)`, `c₀ = f(k) − g₀`, we have `h ≥ 0` and
`h(g₀ − (1 − δ)k) = 0`, and `u'(c₀) − h = βW'(g₀)`. -/
theorem np_irreversible_kkt {u W : ℝ → ℝ} {up : ℝ → ℝ} {W' β δ k fk g0 : ℝ}
    (hc : g0 < fk) (hlow : (1 - δ) * k ≤ g0)
    (hu : HasDerivAt u (up (fk - g0)) (fk - g0)) (hW : HasDerivAt W W' g0)
    (hmax : ∀ k', (1 - δ) * k ≤ k' → k' < fk → u (fk - k') + β * W k' ≤ u (fk - g0) + β * W g0) :
    0 ≤ up (fk - g0) - β * W' ∧ (up (fk - g0) - β * W') * (g0 - (1 - δ) * k) = 0 ∧
      up (fk - g0) - (up (fk - g0) - β * W') = β * W' := by
  set φ : ℝ → ℝ := fun k' => u (fk - k') + β * W k' with hφ
  have hd : HasDerivAt φ (up (fk - g0) * (-1) + β * W') g0 := by
    have h2 := hu.comp g0 ((hasDerivAt_id' g0).const_sub fk)
    exact h2.add (hW.const_mul β)
  -- the right-hand slope is nonpositive
  have hright : up (fk - g0) * (-1) + β * W' ≤ 0 := by
    have ht := hd.tendsto_slope_zero_right
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hc)] with t ht'
    have hle := hmax (g0 + t) (by linarith [ht'.1]) (by linarith [ht'.2])
    simp only [smul_eq_mul, hφ]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht'.1.le) (by linarith)
  refine ⟨by linarith, ?_, by ring⟩
  rcases hlow.eq_or_lt with heq | hlt
  · rw [← heq, sub_self, mul_zero]
  · -- interior: a local maximum, so the derivative vanishes
    have hmaxl : IsLocalMax φ g0 := by
      filter_upwards [Ioo_mem_nhds hlt hc] with k' hk'
      exact hmax k' hk'.1.le hk'.2
    have := hmaxl.hasDerivAt_eq_zero hd
    have h0 : up (fk - g0) - β * W' = 0 := by linarith
    rw [h0, zero_mul]

/-- **(11.14)**, the envelope condition (Miao, p. 382): under (11.13), if `V(k) ≥ u(f(k) − k') +
βW(k')` for all feasible `k' ∈ [(1 − δ)k, f(k))` with equality at the optimum `g₀` for `k₀`, and
`V`, `f`, `u`, `W` are differentiable, then `V'(k₀) = u'(c₀)f'(k₀) − h(1 − δ) = m` with
`h = u'(c₀) − βW'(g₀)`. -/
theorem eq_11_14_envelope {u W V f : ℝ → ℝ} {up : ℝ → ℝ} {W' V' f' β δ k0 g0 : ℝ}
    (hc : g0 < f k0) (hlow : (1 - δ) * k0 ≤ g0)
    (hu : HasDerivAt u (up (f k0 - g0)) (f k0 - g0)) (hW : HasDerivAt W W' g0)
    (hf : HasDerivAt f f' k0) (hV : HasDerivAt V V' k0)
    (hBell : ∀ k k', (1 - δ) * k ≤ k' → k' < f k → u (f k - k') + β * W k' ≤ V k)
    (heq : V k0 = u (f k0 - g0) + β * W g0) :
    V' = up (f k0 - g0) * f' - (up (f k0 - g0) - β * W') * (1 - δ) := by
  set a : ℝ → ℝ := fun k => g0 + (1 - δ) * (k - k0) with ha
  have hda : HasDerivAt a (1 - δ) k0 := by
    have h := (((hasDerivAt_id' k0).sub_const k0).const_mul (1 - δ)).const_add g0
    rw [mul_one] at h
    exact h
  have ha0 : a k0 = g0 := by simp [ha]
  have hc' : HasDerivAt (fun k => f k - a k) (f' - (1 - δ)) k0 := hf.sub hda
  have hlowd : HasDerivAt (fun k => u (f k - a k) + β * W (a k))
      (up (f k0 - g0) * (f' - (1 - δ)) + β * (W' * (1 - δ))) k0 := by
    have h1 := hu.comp_of_eq k0 hc' (by rw [ha0])
    have h2 := hW.comp_of_eq k0 hda ha0.symm
    exact h1.add (h2.const_mul β)
  have hev : ∀ᶠ k in 𝓝 k0, a k < f k := by
    have hpos : 0 < f k0 - a k0 := by rw [ha0]; linarith
    filter_upwards [hc'.continuousAt.eventually (lt_mem_nhds hpos)] with k hk
    linarith
  have := np_envelope (V := V) (W := fun k => u (f k - a k) + β * W (a k)) ?_ ?_ hV hlowd
  · rw [this]
    ring
  · filter_upwards [hev] with k hk
    exact hBell k (a k) (by simp only [ha]; nlinarith) hk
  · simp only [ha0]
    exact heq.symm

/-- **(11.14)**, the inequality `m ≥ 0` (Miao, p. 382), for `f(k, z) = zk^α + (1 − δ)k`: with
`h = u'(c) − e`, `m = u'(c)f_k − h(1 − δ) = u'(c)αzk^{α−1} + (1 − δ)e`, which is positive when
`u'(c) > 0`, `e ≥ 0`, `k, z > 0`, `α > 0` and `δ ≤ 1`. -/
theorem eq_11_14_pos {upc e α δ k z : ℝ} (hup : 0 < upc) (he : 0 ≤ e) (hk : 0 < k) (hz : 0 < z)
    (hα : 0 < α) (hδ : δ ≤ 1) :
    upc * (α * z * k ^ (α - 1) + (1 - δ)) - (upc - e) * (1 - δ) =
        upc * (α * z * k ^ (α - 1)) + (1 - δ) * e ∧
      0 < upc * (α * z * k ^ (α - 1) + (1 - δ)) - (upc - e) * (1 - δ) := by
  have hk' : 0 < k ^ (α - 1) := Real.rpow_pos_of_pos hk _
  refine ⟨by ring, ?_⟩
  have : 0 < upc * (α * z * k ^ (α - 1)) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hδ) he]

/-- The PEA policy and multiplier (Miao, p. 383): `g = max{(1 − δ)k, f − (u')⁻¹(e)}` and
`h = u'(f − g) − e`; they solve the first-order system with expectation `e`. Hypotheses: `u'` is
strictly decreasing on the positive reals with inverse `(u')⁻¹` there, `e > 0` and
`f > (1 − δ)k` (positive consumption when the constraint binds). -/
theorem np_pea_kkt {up upinv : ℝ → ℝ} (hanti : StrictAntiOn up (Set.Ioi 0))
    (hinv : ∀ y, 0 < y → up (upinv y) = y ∧ 0 < upinv y) {e fk δ k : ℝ} (he : 0 < e)
    (hc : (1 - δ) * k < fk) :
    (1 - δ) * k ≤ max ((1 - δ) * k) (fk - upinv e) ∧
      0 ≤ up (fk - max ((1 - δ) * k) (fk - upinv e)) - e ∧
      (up (fk - max ((1 - δ) * k) (fk - upinv e)) - e) *
          (max ((1 - δ) * k) (fk - upinv e) - (1 - δ) * k) = 0 ∧
      0 < fk - max ((1 - δ) * k) (fk - upinv e) := by
  obtain ⟨hue, hpos⟩ := hinv e he
  refine ⟨le_max_left _ _, ?_⟩
  rcases le_total ((1 - δ) * k) (fk - upinv e) with h | h
  · rw [max_eq_right h, sub_sub_cancel, hue, sub_self, zero_mul]
    exact ⟨le_rfl, rfl, hpos⟩
  · rw [max_eq_left h, sub_self, mul_zero]
    have hlt : fk - (1 - δ) * k ≤ upinv e := by linarith
    have hpos' : 0 < fk - (1 - δ) * k := by linarith
    refine ⟨?_, rfl, hpos'⟩
    rcases hlt.eq_or_lt with h1 | h1
    · rw [h1, hue, sub_self]
    · have := hanti hpos' hpos h1
      rw [hue] at this
      linarith

/-- PEA, uniqueness (Miao, p. 383): any `(g, h)` with `u'(f − g) − h = e`, `h(g − (1 − δ)k) = 0`,
`g ≥ (1 − δ)k`, `h ≥ 0` and positive consumption is given by the PEA formulas
`g = max{(1 − δ)k, f − (u')⁻¹(e)}`, `h = u'(f − g) − e`. -/
theorem np_pea_kkt_unique {up upinv : ℝ → ℝ} (hanti : StrictAntiOn up (Set.Ioi 0))
    (hinv : ∀ y, 0 < y → up (upinv y) = y ∧ 0 < upinv y) {e fk δ k g h : ℝ} (he : 0 < e)
    (hfoc : up (fk - g) - h = e) (hcs : h * (g - (1 - δ) * k) = 0) (hg : (1 - δ) * k ≤ g)
    (hh : 0 ≤ h) (hc : 0 < fk - g) :
    g = max ((1 - δ) * k) (fk - upinv e) ∧ h = up (fk - g) - e := by
  obtain ⟨hue, hpos⟩ := hinv e he
  refine ⟨?_, by linarith⟩
  rcases hh.eq_or_lt with h0 | h0
  · -- `h = 0`: unconstrained, `f − g = (u')⁻¹(e)`
    subst h0
    have h1 : up (fk - g) = up (upinv e) := by rw [hue]; linarith
    have h2 : fk - g = upinv e := hanti.injOn hc hpos h1
    have h3 : g = fk - upinv e := by linarith
    rw [max_eq_right (by linarith), h3]
  · -- `h > 0`: the constraint binds
    have hb : g = (1 - δ) * k := by
      have := (mul_eq_zero.1 hcs).resolve_left h0.ne'
      linarith
    have h1 : up (upinv e) < up (fk - g) := by rw [hue]; linarith
    have h2 : fk - g < upinv e := by
      by_contra hcon
      push Not at hcon
      rcases hcon.eq_or_lt with h3 | h3
      · rw [h3] at h1
        exact lt_irrefl _ h1
      · exact lt_asymm h1 (hanti hpos hc h3)
    rw [max_eq_left (by linarith), hb]

end Miao.NumericalMethods.NP
