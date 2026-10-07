/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv

/-!
# The Epstein–Zin aggregator in one variable

Sargent and Stachurski, *Dynamic Programming*, Volume 2, solution to Exercise 5.1.10 (p. 405).

For `c > 0`, `0 ≤ β < 1` and `θ ≠ 0`, let `f(t) = ((1 − β)c + βt^{1/θ})^θ` on `t > 0`.

* `f` is order preserving, and `f(d^θ) = ((1 − β)c + βd)^θ`.
* `f'(t) = β((1 − β)c t^{−1/θ} + β)^{θ−1}`, so `f` is convex when `0 < θ ≤ 1` and concave when
  `θ < 0` or `1 ≤ θ`.
-/

open Set Filter Topology

namespace SargentStachurski.ADPTransformations

namespace EZ

/-- `f(t) = ((1 − β)c + βt^{1/θ})^θ`. -/
noncomputable def f (β θ c t : ℝ) : ℝ := ((1 - β) * c + β * t ^ θ⁻¹) ^ θ

/-- The inner aggregate `(1 − β)c + βt^{1/θ}`. -/
noncomputable def g (β θ c t : ℝ) : ℝ := (1 - β) * c + β * t ^ θ⁻¹

/-- The derivative `β((1 − β)c t^{−1/θ} + β)^{θ−1}`. -/
noncomputable def f' (β θ c t : ℝ) : ℝ := β * ((1 - β) * c * t ^ (-θ⁻¹) + β) ^ (θ - 1)

variable {β θ c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc : 0 < c)
include hβ0 hβ1 hc

theorem g_pos {t : ℝ} (ht : 0 ≤ t) : 0 < g β θ c t :=
  add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 hβ1) hc)
    (mul_nonneg hβ0 (Real.rpow_nonneg ht _))

/-- `f` is order preserving on `(0, ∞)`. -/
theorem f_monotoneOn (hθ : θ ≠ 0) : MonotoneOn (f β θ c) (Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  have hgs := g_pos hβ0 hβ1 hc (θ := θ) hs'.le
  have hgt := g_pos hβ0 hβ1 hc (θ := θ) ht'.le
  change g β θ c s ^ θ ≤ g β θ c t ^ θ
  rcases lt_or_gt_of_ne hθ with hneg | hpos
  · have hinv : θ⁻¹ < 0 := inv_lt_zero.2 hneg
    have h1 : t ^ θ⁻¹ ≤ s ^ θ⁻¹ := Real.rpow_le_rpow_of_nonpos hs' hst hinv.le
    have h2 : g β θ c t ≤ g β θ c s :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 hβ0)
    exact Real.rpow_le_rpow_of_nonpos hgt h2 hneg.le
  · have h1 : s ^ θ⁻¹ ≤ t ^ θ⁻¹ := Real.rpow_le_rpow hs'.le hst (inv_nonneg.2 hpos.le)
    have h2 : g β θ c s ≤ g β θ c t :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 hβ0)
    exact Real.rpow_le_rpow hgs.le h2 hpos.le

omit hβ0 hβ1 hc in
/-- `f(d^θ) = ((1 − β)c + βd)^θ`. -/
theorem f_rpow (hθ : θ ≠ 0) {d : ℝ} (hd : 0 < d) :
    f β θ c (d ^ θ) = ((1 - β) * c + β * d) ^ θ := by
  rw [f, Real.rpow_rpow_inv hd.le hθ]

/-- `f'(t) = β((1 − β)c t^{−1/θ} + β)^{θ−1}`. -/
theorem hasDerivAt_f (hθ : θ ≠ 0) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (f β θ c) (f' β θ c t) t := by
  have hg : HasDerivAt (g β θ c) (β * (θ⁻¹ * t ^ (θ⁻¹ - 1))) t :=
    ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul β).const_add ((1 - β) * c)
  have hgt := g_pos hβ0 hβ1 hc (θ := θ) ht.le
  have hf := hg.rpow_const (p := θ) (Or.inl hgt.ne')
  have hfg : f β θ c = fun y => g β θ c y ^ θ := rfl
  rw [hfg]
  convert hf using 1
  -- `β((1−β)c t^{−1/θ} + β)^{θ−1} = βθ⁻¹t^{θ⁻¹−1} · θ · g(t)^{θ−1}`
  have hsplit : (1 - β) * c * t ^ (-θ⁻¹) + β = g β θ c t * t ^ (-θ⁻¹) := by
    rw [g, add_mul, mul_assoc β, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
  have hpow : (t ^ (-θ⁻¹)) ^ (θ - 1) = t ^ (θ⁻¹ - 1) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    field_simp
    ring
  unfold f'
  rw [hsplit, Real.mul_rpow hgt.le (Real.rpow_nonneg ht.le _), hpow]
  field_simp

theorem deriv_f (hθ : θ ≠ 0) {t : ℝ} (ht : 0 < t) : deriv (f β θ c) t = f' β θ c t :=
  (hasDerivAt_f hβ0 hβ1 hc hθ ht).deriv

theorem f'_inner_pos {t : ℝ} (ht : 0 < t) : 0 < (1 - β) * c * t ^ (-θ⁻¹) + β :=
  add_pos_of_pos_of_nonneg (mul_pos (mul_pos (sub_pos.2 hβ1) hc) (Real.rpow_pos_of_pos ht _)) hβ0

theorem continuousOn_f (hθ : θ ≠ 0) : ContinuousOn (f β θ c) (Ioi 0) := fun _ ht =>
  (hasDerivAt_f hβ0 hβ1 hc hθ ht).continuousAt.continuousWithinAt

theorem differentiableOn_f (hθ : θ ≠ 0) : DifferentiableOn ℝ (f β θ c) (interior (Ioi 0)) := by
  rw [interior_Ioi]
  exact fun _ ht => (hasDerivAt_f hβ0 hβ1 hc hθ ht).differentiableAt.differentiableWithinAt

/-- **Exercise 5.1.10 (i)**, scalar form: if `0 < θ ≤ 1`, `f` is convex on `(0, ∞)`. -/
theorem convexOn_f (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : ConvexOn ℝ (Ioi 0) (f β θ c) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioi 0) (continuousOn_f hβ0 hβ1 hc hθ0.ne')
    (differentiableOn_f hβ0 hβ1 hc hθ0.ne') ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  rw [deriv_f hβ0 hβ1 hc hθ0.ne' hs', deriv_f hβ0 hβ1 hc hθ0.ne' ht]
  refine mul_le_mul_of_nonneg_left ?_ hβ0
  have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
    Real.rpow_le_rpow_of_nonpos hs' hst (neg_nonpos.2 (inv_nonneg.2 hθ0.le))
  have h2 : (1 - β) * c * t ^ (-θ⁻¹) + β ≤ (1 - β) * c * s ^ (-θ⁻¹) + β :=
    add_le_add (mul_le_mul_of_nonneg_left h1 (mul_pos (sub_pos.2 hβ1) hc).le) le_rfl
  exact Real.rpow_le_rpow_of_nonpos (f'_inner_pos hβ0 hβ1 hc ht) h2 (by linarith)

/-- **Exercise 5.1.10 (ii)**, scalar form: if `θ < 0` or `1 ≤ θ`, `f` is concave on `(0, ∞)`. -/
theorem concaveOn_f (hθ : θ < 0 ∨ 1 ≤ θ) : ConcaveOn ℝ (Ioi 0) (f β θ c) := by
  have hθ0 : θ ≠ 0 := by
    rcases hθ with h | h
    · exact h.ne
    · exact (by linarith : (0 : ℝ) < θ).ne'
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) (continuousOn_f hβ0 hβ1 hc hθ0)
    (differentiableOn_f hβ0 hβ1 hc hθ0) ?_
  rw [interior_Ioi]
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  rw [deriv_f hβ0 hβ1 hc hθ0 hs', deriv_f hβ0 hβ1 hc hθ0 ht']
  refine mul_le_mul_of_nonneg_left ?_ hβ0
  have hk : 0 ≤ (1 - β) * c := (mul_pos (sub_pos.2 hβ1) hc).le
  rcases hθ with hneg | hge
  · -- `t ↦ t^{−1/θ}` is increasing, the exponent `θ − 1` is negative
    have h1 : s ^ (-θ⁻¹) ≤ t ^ (-θ⁻¹) :=
      Real.rpow_le_rpow hs'.le hst (neg_nonneg.2 (inv_lt_zero.2 hneg).le)
    have h2 : (1 - β) * c * s ^ (-θ⁻¹) + β ≤ (1 - β) * c * t ^ (-θ⁻¹) + β :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hk) le_rfl
    exact Real.rpow_le_rpow_of_nonpos (f'_inner_pos hβ0 hβ1 hc hs') h2 (by linarith)
  · -- `t ↦ t^{−1/θ}` is decreasing, the exponent `θ − 1` is nonnegative
    have h1 : t ^ (-θ⁻¹) ≤ s ^ (-θ⁻¹) :=
      Real.rpow_le_rpow_of_nonpos hs' hst (neg_nonpos.2 (inv_nonneg.2 (by linarith)))
    have h2 : (1 - β) * c * t ^ (-θ⁻¹) + β ≤ (1 - β) * c * s ^ (-θ⁻¹) + β :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hk) le_rfl
    exact Real.rpow_le_rpow (f'_inner_pos hβ0 hβ1 hc ht').le h2 (by linarith)

end EZ

end SargentStachurski.ADPTransformations
