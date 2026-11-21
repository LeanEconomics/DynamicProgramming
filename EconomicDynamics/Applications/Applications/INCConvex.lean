/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.Compact

/-!
# c-convexity (Scarf's K-convexity): Definition 8.5.1 and Lemma 8.5.1

Miao, §8.5, pp. 265–268. For `c ≥ 0` a function `h : ℝ → ℝ` is *c-convex* if
`c + h(x + a) − h(x) − a (h(x) − h(x − b))/b ≥ 0` for all `a, b > 0` ((8.25), `in_CConvex`);
for differentiable `h` the book also uses `c + h(x + a) − h(x) − a h′(x) ≥ 0` for all `a > 0`
((8.24), `in_CConvexDiff`).

* `definition_8_5_1`: for a differentiable `h`, (8.25) implies (8.24) (let `b → 0⁺`).
* `lemma_8_5_1`: for a differentiable c-convex `h`, `c + h(y) − h(x) − (y − x)h′(u) ≥ 0` for
  `y > x > u` (the book's two-case proof).
* Properties (i)–(iii), p. 266–267: `in_cconvex_zero_of_convexOn`, `in_cconvex_mono`,
  `in_cconvex_comp_add`, `in_cconvex_add_smul`; affine functions are `0`-convex
  (`in_cconvex_affine`); a probability mixture of translates `x ↦ ∫ f(x − z) dφ(z)` of a
  c-convex `f` is c-convex (`in_cconvex_integral`, used for `E f_n(x − z)` on p. 270).
* Figure 8.6 (pp. 267–268): a c-convex function has no "not order / order / not order"
  pattern: at a point `x` with `h(x − b) ≤ h(x)` (for instance a local maximiser from the left)
  ordering never pays, `h(x) ≤ c + h(y)` for `y > x` (`in_cconvex_local_max`), and so, for a
  continuous `h`, once `h(u) ≤ c + h(S)` with `u < S` we have `h(v) ≤ c + h(S)` on all of
  `(u, S)` (`fig_8_6`).

**Departure.** Property (iii) is stated in the book for `α, γ > 0`; we prove it for `α, γ ≥ 0`.
-/

namespace Miao.Applications

open MeasureTheory Filter Topology

/-- **Definition 8.5.1** (Miao, p. 266), (8.25): `h` is *c-convex* if
`c + h(x + a) − h(x) − a (h(x) − h(x − b))/b ≥ 0` for all `x` and all `a, b > 0`. -/
def in_CConvex (c : ℝ) (h : ℝ → ℝ) : Prop :=
  ∀ x a b : ℝ, 0 < a → 0 < b → 0 ≤ c + h (x + a) - h x - a * ((h x - h (x - b)) / b)

/-- **Definition 8.5.1** (Miao, p. 266), (8.24): the differentiable form,
`c + h(x + a) − h(x) − a h′(x) ≥ 0` for all `x` and all `a > 0`. -/
def in_CConvexDiff (c : ℝ) (h : ℝ → ℝ) : Prop :=
  ∀ x a : ℝ, 0 < a → 0 ≤ c + h (x + a) - h x - a * deriv h x

/-- **Definition 8.5.1** (Miao, p. 266): for a differentiable function, (8.25) implies (8.24)
(let `b → 0⁺` in (8.25)). -/
theorem definition_8_5_1 {c : ℝ} {h : ℝ → ℝ} (hd : Differentiable ℝ h)
    (hc : in_CConvex c h) : in_CConvexDiff c h := by
  intro x a ha
  have hslope := (hd x).hasDerivAt.tendsto_slope_zero_left
  have hneg : Tendsto (fun b : ℝ => -b) (𝓝[>] 0) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun b : ℝ => -b) (𝓝 0) (𝓝 (-0)) := tendsto_neg 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with b hb
      exact neg_lt_zero.2 (Set.mem_Ioi.1 hb)
  have hq : Tendsto (fun b : ℝ => (h x - h (x - b)) / b) (𝓝[>] 0) (𝓝 (deriv h x)) := by
    refine (hslope.comp hneg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hb' : b ≠ 0 := ne_of_gt hb
    simp only [Function.comp_apply, smul_eq_mul, ← sub_eq_add_neg]
    field_simp
    ring
  have hlim : Tendsto (fun b : ℝ => c + h (x + a) - h x - a * ((h x - h (x - b)) / b))
      (𝓝[>] 0) (𝓝 (c + h (x + a) - h x - a * deriv h x)) :=
    tendsto_const_nhds.sub (hq.const_mul a)
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with b hb
  exact hc x a b ha hb

/-- **Lemma 8.5.1** (Miao, p. 266). If `h` is a differentiable c-convex function, then
`c + h(y) − h(x) − (y − x) h′(u) ≥ 0` for all `y > x > u`. -/
theorem lemma_8_5_1 {c : ℝ} {h : ℝ → ℝ} (hd : Differentiable ℝ h) (hc : in_CConvex c h)
    {x y u : ℝ} (hxy : x < y) (hux : u < x) :
    0 ≤ c + h y - h x - (y - x) * deriv h u := by
  have hc' := definition_8_5_1 hd hc
  have hxu : 0 < x - u := sub_pos.2 hux
  have hyx : 0 < y - x := sub_pos.2 hxy
  rcases le_or_gt (h u - h x + (x - u) * deriv h u) 0 with h1 | h1
  · -- Case 1: `h′(u) ≤ (h(x) − h(u))/(x − u)`; use (8.25) at `x` with `a = y − x`, `b = x − u`.
    have key := hc x (y - x) (x - u) hyx hxu
    have hxa : x + (y - x) = y := by ring
    have hxb : x - (x - u) = u := by ring
    rw [hxa, hxb] at key
    have hder : deriv h u ≤ (h x - h u) / (x - u) := by
      rw [le_div_iff₀ hxu]; linarith
    have : (y - x) * deriv h u ≤ (y - x) * ((h x - h u) / (x - u)) :=
      mul_le_mul_of_nonneg_left hder hyx.le
    linarith
  · -- Case 2: use (8.24) at `u` with `a = y − u`.
    have key := hc' u (y - u) (by linarith)
    have hua : u + (y - u) = y := by ring
    rw [hua] at key
    nlinarith

/-- Miao, p. 266, property (i): a convex function is `0`-convex. -/
theorem in_cconvex_zero_of_convexOn {h : ℝ → ℝ} (hh : ConvexOn ℝ Set.univ h) :
    in_CConvex 0 h := by
  intro x a b ha hb
  have key := hh.slope_mono_adjacent (Set.mem_univ (x - b)) (Set.mem_univ (x + a))
    (by linarith : x - b < x) (by linarith : x < x + a)
  have e1 : x - (x - b) = b := by ring
  have e2 : x + a - x = a := by ring
  rw [e1, e2] at key
  have : a * ((h x - h (x - b)) / b) ≤ a * ((h (x + a) - h x) / a) :=
    mul_le_mul_of_nonneg_left key ha.le
  rw [mul_div_cancel₀ _ ha.ne'] at this
  linarith

/-- Miao, p. 266, property (i): a c-convex function is `c′`-convex for every `c′ ≥ c`. -/
theorem in_cconvex_mono {c c' : ℝ} {h : ℝ → ℝ} (hcc : c ≤ c') (hh : in_CConvex c h) :
    in_CConvex c' h := by
  intro x a b ha hb
  have := hh x a b ha hb
  linarith

/-- Miao, p. 266, property (ii): if `h` is c-convex then so is `x ↦ h(x + t)`. -/
theorem in_cconvex_comp_add {c : ℝ} {h : ℝ → ℝ} (hh : in_CConvex c h) (t : ℝ) :
    in_CConvex c (fun x => h (x + t)) := by
  intro x a b ha hb
  have := hh (x + t) a b ha hb
  have e1 : x + a + t = x + t + a := by ring
  have e2 : x - b + t = x + t - b := by ring
  simp only [e1, e2]
  exact this

/-- Miao, p. 267, property (iii): if `f` is c-convex and `g` is b-convex, then `αf + γg` is
`(αc + γb)`-convex (`α, γ ≥ 0`). -/
theorem in_cconvex_add_smul {c d α γ : ℝ} {f g : ℝ → ℝ} (hf : in_CConvex c f)
    (hg : in_CConvex d g) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    in_CConvex (α * c + γ * d) (fun x => α * f x + γ * g x) := by
  intro x a b ha hb
  have h1 := mul_nonneg hα (hf x a b ha hb)
  have h2 := mul_nonneg hγ (hg x a b ha hb)
  have e : α * c + γ * d + (α * f (x + a) + γ * g (x + a)) - (α * f x + γ * g x) -
      a * ((α * f x + γ * g x - (α * f (x - b) + γ * g (x - b))) / b) =
      α * (c + f (x + a) - f x - a * ((f x - f (x - b)) / b)) +
      γ * (d + g (x + a) - g x - a * ((g x - g (x - b)) / b)) := by
    field_simp
    ring
  rw [e]
  exact add_nonneg h1 h2

/-- Miao, p. 266: affine functions `x ↦ qx + r` are `0`-convex. -/
theorem in_cconvex_affine (q r : ℝ) : in_CConvex 0 (fun x => q * x + r) := by
  intro x a b ha hb
  have e : (0 : ℝ) + (q * (x + a) + r) - (q * x + r) - a * ((q * x + r - (q * (x - b) + r)) / b)
      = 0 := by
    field_simp
    ring
  rw [e]

/-- Miao, p. 270: if `f` is c-convex and every translate `z ↦ f(y − z)` is `φ`-integrable,
then `x ↦ ∫ f(x − z) dφ(z)` is c-convex, for a probability measure `φ`. -/
theorem in_cconvex_integral {c : ℝ} {f : ℝ → ℝ} (φ : Measure ℝ) [IsProbabilityMeasure φ]
    (hf : in_CConvex c f) (hint : ∀ y, Integrable (fun z => f (y - z)) φ) :
    in_CConvex c (fun x => ∫ z, f (x - z) ∂φ) := by
  intro x a b ha hb
  have hpt : ∀ z, 0 ≤ c + f (x + a - z) - f (x - z) - a * ((f (x - z) - f (x - b - z)) / b) := by
    intro z
    have := hf (x - z) a b ha hb
    have e1 : x - z + a = x + a - z := by ring
    have e2 : x - z - b = x - b - z := by ring
    rw [e1, e2] at this
    exact this
  have hI : 0 ≤ ∫ z, (c + f (x + a - z) - f (x - z) - a * ((f (x - z) - f (x - b - z)) / b)) ∂φ :=
    integral_nonneg hpt
  have i1 := hint (x + a)
  have i2 := hint x
  have i3 := hint (x - b)
  have e : (∫ z, (c + f (x + a - z) - f (x - z) - a * ((f (x - z) - f (x - b - z)) / b)) ∂φ) =
      c + (∫ z, f (x + a - z) ∂φ) - (∫ z, f (x - z) ∂φ) -
        a * (((∫ z, f (x - z) ∂φ) - ∫ z, f (x - b - z) ∂φ) / b) := by
    have hfun : (fun z => c + f (x + a - z) - f (x - z) - a * ((f (x - z) - f (x - b - z)) / b))
        = fun z => (c + f (x + a - z) - f (x - z)) - (a / b) * (f (x - z) - f (x - b - z)) := by
      funext z; ring
    have j3 : Integrable (fun z => c + f (x + a - z)) φ := (integrable_const c).add i1
    have j1 : Integrable (fun z => c + f (x + a - z) - f (x - z)) φ := j3.sub i2
    have j4 : Integrable (fun z => f (x - z) - f (x - b - z)) φ := i2.sub i3
    have j2 : Integrable (fun z => a / b * (f (x - z) - f (x - b - z))) φ := j4.const_mul _
    rw [hfun, integral_sub j1 j2, integral_const_mul, integral_sub j3 i2,
      integral_add (integrable_const c) i1, integral_sub i2 i3]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [e] at hI
  exact hI

/-- Miao, pp. 267–268 (the argument of Figure 8.6): if `h` is c-convex and
`h(x − b) ≤ h(x)` for some `b > 0` (e.g. `x` is a local maximiser), then `h(x) ≤ c + h(y)` for
every `y > x`: it never pays to order from such a stock level. -/
theorem in_cconvex_local_max {c : ℝ} {h : ℝ → ℝ} (hh : in_CConvex c h) {x y b : ℝ}
    (hxy : x < y) (hb : 0 < b) (hmax : h (x - b) ≤ h x) : h x ≤ c + h y := by
  have key := hh x (y - x) b (sub_pos.2 hxy) hb
  have e : x + (y - x) = y := by ring
  rw [e] at key
  have : 0 ≤ (y - x) * ((h x - h (x - b)) / b) :=
    mul_nonneg (sub_pos.2 hxy).le (div_nonneg (sub_nonneg.2 hmax) hb.le)
  linarith

/-- **Figure 8.6** (Miao, pp. 267–268): for a continuous c-convex `h` it is impossible that not
ordering (up to `S`) is optimal at `u`, ordering is strictly optimal at some `v ∈ (u, S)`:
`h(u) ≤ c + h(S)` and `u < v < S` give `h(v) ≤ c + h(S)`. -/
theorem fig_8_6 {c : ℝ} {h : ℝ → ℝ} (hh : in_CConvex c h) (hcont : Continuous h)
    {u v S : ℝ} (huv : u < v) (hvS : v < S) (hu : h u ≤ c + h S) : h v ≤ c + h S := by
  by_contra hcon
  push Not at hcon
  obtain ⟨xs, hxs, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc u v)).exists_isMaxOn
    (Set.nonempty_Icc.2 huv.le) hcont.continuousOn
  have hv : h v ≤ h xs := hmax (Set.right_mem_Icc.2 huv.le)
  have hxu : u < xs := by
    rcases eq_or_lt_of_le hxs.1 with h' | h'
    · rw [← h'] at hv; linarith
    · exact h'
  have hloc : h (xs - (xs - u)) ≤ h xs := hmax ⟨by linarith, by linarith [hxs.2]⟩
  have := in_cconvex_local_max hh (lt_of_le_of_lt hxs.2 hvS) (sub_pos.2 hxu) hloc
  linarith

end Miao.Applications
