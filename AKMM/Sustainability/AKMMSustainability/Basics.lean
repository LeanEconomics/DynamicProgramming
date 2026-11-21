/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.CESIndex

/-!
# Tangent-line inequalities

Auxiliary inequalities used throughout the chapter's optimisation arguments (AKMM Chapter 25,
pp. 763–782): every optimum in the chapter is verified by a tangent-line (supergradient)
bound rather than by first-order conditions alone.

* `log y ≤ log c + (y − c)/c`, strictly for `y ≠ c` (`sust_log_le_tangent`,
  `sust_log_lt_tangent`);
* for `x ≥ 1`, `c^x + x c^{x−1}(y − c) ≤ y^x` (`sust_tangent_le_rpow`), strictly for `x > 1` and
  `y ≠ c` (`sust_tangent_lt_rpow`);
* for `0 < ν < 1`, `y^ν < c^ν + ν c^{ν−1}(y − c)` when `y ≠ c` (`sust_rpow_lt_tangent`).

The weak concave and negative-power versions are those of `RealExchangeRate.CESIndex`
(Obstfeld–Rogoff, p. 227): `ces_rpow_le_tangent`, `ces_tangent_le_rpow`.
-/

namespace AKMM.Sustainability

open Real

/-- Tangent-line bound for the logarithm: `log y ≤ log c + (y − c)/c`. -/
theorem sust_log_le_tangent {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Real.log y ≤ Real.log c + (y - c) / c := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hc)
  rw [Real.log_div hy.ne' hc.ne'] at h
  have : y / c - 1 = (y - c) / c := by field_simp
  linarith

/-- Strict tangent-line bound for the logarithm away from the tangency point. -/
theorem sust_log_lt_tangent {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (hyc : y ≠ c) :
    Real.log y < Real.log c + (y - c) / c := by
  have hne : y / c ≠ 1 := by
    intro h; exact hyc (by field_simp at h; linarith)
  have h := Real.log_lt_sub_one_of_pos (div_pos hy hc) hne
  rw [Real.log_div hy.ne' hc.ne'] at h
  have : y / c - 1 = (y - c) / c := by field_simp
  linarith

/-- Tangent-line bound for a convex power `x ≥ 1`: `c^x + x c^{x−1}(y − c) ≤ y^x`. -/
theorem sust_tangent_le_rpow {x y c : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    c ^ x + x * c ^ (x - 1) * (y - c) ≤ y ^ x := by
  have hs : -1 ≤ y / c - 1 := by have := div_nonneg hy hc.le; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hx
  rw [add_sub_cancel, div_rpow hy hc.le] at hb
  have hcx := rpow_pos_of_pos hc x
  rw [le_div_iff₀ hcx] at hb
  rw [rpow_sub_one hc.ne']
  calc c ^ x + x * (c ^ x / c) * (y - c) = (1 + x * (y / c - 1)) * c ^ x := by field_simp
    _ ≤ y ^ x := hb

/-- Strict tangent-line bound for a strictly convex power `x > 1` away from the tangency
point. -/
theorem sust_tangent_lt_rpow {x y c : ℝ} (hx : 1 < x) (hy : 0 ≤ y) (hc : 0 < c) (hyc : y ≠ c) :
    c ^ x + x * c ^ (x - 1) * (y - c) < y ^ x := by
  have hs : -1 ≤ y / c - 1 := by have := div_nonneg hy hc.le; linarith
  have hs' : y / c - 1 ≠ 0 := by
    intro h; exact hyc (by field_simp at h; linarith)
  have hb := one_add_mul_self_lt_rpow_one_add hs hs' hx
  rw [add_sub_cancel, div_rpow hy hc.le] at hb
  have hcx := rpow_pos_of_pos hc x
  rw [lt_div_iff₀ hcx] at hb
  rw [rpow_sub_one hc.ne']
  calc c ^ x + x * (c ^ x / c) * (y - c) = (1 + x * (y / c - 1)) * c ^ x := by field_simp
    _ < y ^ x := hb

/-- Strict tangent-line bound for a strictly concave power `0 < ν < 1` away from the tangency
point: `y^ν < c^ν + ν c^{ν−1}(y − c)`. -/
theorem sust_rpow_lt_tangent {ν y c : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hy : 0 ≤ y) (hc : 0 < c)
    (hyc : y ≠ c) : y ^ ν < c ^ ν + ν * c ^ (ν - 1) * (y - c) := by
  have hs : -1 ≤ y / c - 1 := by have := div_nonneg hy hc.le; linarith
  have hs' : y / c - 1 ≠ 0 := by
    intro h; exact hyc (by field_simp at h; linarith)
  have hb := rpow_one_add_lt_one_add_mul_self hs hs' hν0 hν1
  rw [add_sub_cancel, div_rpow hy hc.le] at hb
  have hcx := rpow_pos_of_pos hc ν
  rw [div_lt_iff₀ hcx] at hb
  rw [rpow_sub_one hc.ne']
  calc y ^ ν < (1 + ν * (y / c - 1)) * c ^ ν := hb
    _ = c ^ ν + ν * (c ^ ν / c) * (y - c) := by field_simp

end AKMM.Sustainability
