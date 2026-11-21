/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Example 1: root finding and optimisation in the labour–leisure choice

AKMM, §10.3.3, Example 1, pp. 269–270. The consumer maximises `ln c − (ω/γ)ℓ^γ` subject to
`c = ℓ^α + x`, i.e. (10.4) `F(ℓ) = ln(ℓ^α + x) − (ω/γ)ℓ^γ`, with first-order condition (10.5)
`αℓ^{α−1}/(ℓ^α + x) − ωℓ^{γ−1} = 0`.

* (10.5) is `F′(ℓ) = 0` (`eq_10_5`), and for `α ∈ (0, 1)`, `x > 0`, `ω > 0`, `γ ≥ 1` its left
  side is strictly decreasing on `(0, ∞)` (`ex1_foc_strictAnti`), so it has at most one root,
  and a root is the unique maximiser of (10.4) on `(0, ∞)` (`ex1_root_isMax`): maximising
  (10.4) and solving (10.5) are the same problem, as §10.3.3 says.
* For the book's parameters `α = 1/3`, `x = 0.5`, `ω = 1`, `γ = 2`, (10.5) has exactly one root, and
  it lies in `(1/8, 1)` ⊂ `[0, 1]` (`ex1_unique_root`), which is what the bisection, Newton and
  golden-section codes compute.
-/

namespace AKMM.ComputationalTools

open Set Real

/-- AKMM, (10.4), p. 270: the objective `ln(ℓ^α + x) − (ω/γ)ℓ^γ`. -/
noncomputable def ex1Obj (α x ω γ ℓ : ℝ) : ℝ := Real.log (ℓ ^ α + x) - ω / γ * ℓ ^ γ

/-- AKMM, (10.5), p. 270: the left side of the first-order condition. -/
noncomputable def ex1Foc (α x ω γ ℓ : ℝ) : ℝ := α * ℓ ^ (α - 1) / (ℓ ^ α + x) - ω * ℓ ^ (γ - 1)

/-- AKMM, (10.5), p. 270: the first-order condition is the derivative of (10.4) (for `ℓ > 0`,
`x ≥ 0`, `γ ≠ 0`). -/
theorem eq_10_5 {α x ω γ ℓ : ℝ} (hx : 0 ≤ x) (hγ : γ ≠ 0) (hℓ : 0 < ℓ) :
    HasDerivAt (ex1Obj α x ω γ) (ex1Foc α x ω γ ℓ) ℓ := by
  have h1 : HasDerivAt (fun l => l ^ α) (α * ℓ ^ (α - 1)) ℓ :=
    Real.hasDerivAt_rpow_const (Or.inl hℓ.ne')
  have h2 : HasDerivAt (fun l => l ^ γ) (γ * ℓ ^ (γ - 1)) ℓ :=
    Real.hasDerivAt_rpow_const (Or.inl hℓ.ne')
  have hpos : 0 < ℓ ^ α + x := by have := Real.rpow_pos_of_pos hℓ α; linarith
  have h := ((h1.add_const x).log hpos.ne').sub (h2.const_mul (ω / γ))
  refine h.congr_deriv ?_
  unfold ex1Foc
  field_simp

/-- AKMM, Example 1: for `α ∈ (0, 1)`, `x > 0`, `ω > 0`, `γ ≥ 1` the left side of (10.5) is
strictly decreasing on `(0, ∞)`. -/
theorem ex1_foc_strictAnti {α x ω γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) (hω : 0 < ω)
    (hγ : 1 ≤ γ) : StrictAntiOn (ex1Foc α x ω γ) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  have hn : b ^ (α - 1) < a ^ (α - 1) := Real.rpow_lt_rpow_of_neg ha' hab (by linarith)
  have hn0 : 0 < b ^ (α - 1) := Real.rpow_pos_of_pos hb' _
  have hd : a ^ α < b ^ α := Real.rpow_lt_rpow ha'.le hab hα0
  have hd0 : 0 < a ^ α := Real.rpow_pos_of_pos ha' _
  have hg : a ^ (γ - 1) ≤ b ^ (γ - 1) := Real.rpow_le_rpow ha'.le hab.le (by linarith)
  have hfirst : α * b ^ (α - 1) / (b ^ α + x) < α * a ^ (α - 1) / (a ^ α + x) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    have e1 : α * b ^ (α - 1) * (a ^ α + x) < α * a ^ (α - 1) * (a ^ α + x) := by
      apply mul_lt_mul_of_pos_right _ (by linarith)
      exact mul_lt_mul_of_pos_left hn hα0
    have e2 : α * a ^ (α - 1) * (a ^ α + x) ≤ α * a ^ (α - 1) * (b ^ α + x) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      exact (mul_pos hα0 (hn0.trans hn)).le
    linarith
  unfold ex1Foc
  have := mul_le_mul_of_nonneg_left hg hω.le
  linarith

/-- AKMM, §10.3.3 and Example 1: with the hypotheses of `ex1_foc_strictAnti`, a root `ℓ*` of
(10.5) is the unique maximiser of (10.4) on `(0, ∞)`. -/
theorem ex1_root_isMax {α x ω γ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) (hω : 0 < ω)
    (hγ : 1 ≤ γ) {ls : ℝ} (hls : 0 < ls) (hroot : ex1Foc α x ω γ ls = 0) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hne : ℓ ≠ ls) : ex1Obj α x ω γ ℓ < ex1Obj α x ω γ ls := by
  have hγ0 : γ ≠ 0 := by linarith
  have hanti := ex1_foc_strictAnti hα0 hα1 hx hω hγ
  have hderiv : ∀ y, 0 < y → deriv (ex1Obj α x ω γ) y = ex1Foc α x ω γ y :=
    fun y hy => (eq_10_5 hx.le hγ0 hy).deriv
  have hcont : ContinuousOn (ex1Obj α x ω γ) (Ioi 0) := fun y hy =>
    (eq_10_5 hx.le hγ0 hy).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- increasing on `(0, ℓ*]`
    have hmono : StrictMonoOn (ex1Obj α x ω γ) (Ioc 0 ls) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioc 0 ls) (hcont.mono Ioc_subset_Ioi_self)
        fun y hy => ?_
      rw [interior_Ioc] at hy
      rw [hderiv y hy.1, ← hroot]
      exact hanti hy.1 hls hy.2
    exact hmono ⟨hℓ, hlt.le⟩ ⟨hls, le_rfl⟩ hlt
  · -- decreasing on `[ℓ*, ∞)`
    have hmono : StrictAntiOn (ex1Obj α x ω γ) (Ici ls) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici ls)
        (hcont.mono fun y hy => lt_of_lt_of_le hls hy) fun y hy => ?_
      rw [interior_Ici] at hy
      have hy0 : 0 < y := hls.trans hy
      rw [hderiv y hy0, ← hroot]
      exact hanti hls hy0 hy
    exact hmono (le_refl ls) hgt.le hgt

/-- `(1/8)^{1/3} = 1/2`. -/
theorem ex1_cbrt_eighth : (1 / 8 : ℝ) ^ (1 / 3 : ℝ) = 1 / 2 := by
  rw [show (1 / 8 : ℝ) = (1 / 2) ^ (3 : ℕ) by norm_num,
    show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (by norm_num)
    (by norm_num)]

/-- AKMM, Example 1, p. 270: with `α = 1/3`, `x = 0.5`, `ω = 1`, `γ = 2`, the first-order
condition (10.5) has exactly one root in `(0, ∞)`; it lies in `(1/8, 1)`, and it maximises
(10.4). -/
theorem ex1_unique_root :
    ∃! ls, 0 < ls ∧ ex1Foc (1 / 3) (1 / 2) 1 2 ls = 0 ∧ ls ∈ Ioo (1 / 8) 1 ∧
      ∀ ℓ, 0 < ℓ → ℓ ≠ ls → ex1Obj (1 / 3) (1 / 2) 1 2 ℓ < ex1Obj (1 / 3) (1 / 2) 1 2 ls := by
  have hanti := ex1_foc_strictAnti (α := 1 / 3) (x := 1 / 2) (ω := 1) (γ := 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : 0 < ex1Foc (1 / 3) (1 / 2) 1 2 (1 / 8) := by
    unfold ex1Foc
    rw [show (1 / 3 : ℝ) - 1 = (1 / 3) * (-2) by norm_num, Real.rpow_mul (by norm_num),
      ex1_cbrt_eighth, show (2 : ℝ) - 1 = (1 : ℕ) by norm_num, Real.rpow_natCast]
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have h1 : ex1Foc (1 / 3) (1 / 2) 1 2 1 < 0 := by
    unfold ex1Foc
    simp only [Real.one_rpow]
    norm_num
  have hcont : ContinuousOn (ex1Foc (1 / 3) (1 / 2) 1 2) (Icc (1 / 8) 1) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num) hy.1
    have c1 : ContinuousAt (fun l : ℝ => l ^ ((1 : ℝ) / 3 - 1)) y :=
      Real.continuousAt_rpow_const _ _ (Or.inl hy0.ne')
    have c2 : ContinuousAt (fun l : ℝ => l ^ ((1 : ℝ) / 3)) y :=
      Real.continuousAt_rpow_const _ _ (Or.inl hy0.ne')
    have c3 : ContinuousAt (fun l : ℝ => l ^ ((2 : ℝ) - 1)) y :=
      Real.continuousAt_rpow_const _ _ (Or.inl hy0.ne')
    have hden : y ^ ((1 : ℝ) / 3) + 1 / 2 ≠ 0 := by
      have := Real.rpow_pos_of_pos hy0 ((1 : ℝ) / 3); linarith
    exact ((((c1.const_mul _).div (c2.add continuousAt_const) hden)).sub
      (c3.const_mul _)).continuousWithinAt
  obtain ⟨ls, hls, hroot⟩ := intermediate_value_Icc' (by norm_num : (1 / 8 : ℝ) ≤ 1) hcont
    ⟨h1.le, h8.le⟩
  have hls0 : 0 < ls := lt_of_lt_of_le (by norm_num) hls.1
  have hlsI : ls ∈ Ioo (1 / 8 : ℝ) 1 := by
    refine ⟨lt_of_le_of_ne hls.1 ?_, lt_of_le_of_ne hls.2 ?_⟩
    · rintro rfl; rw [hroot] at h8; exact lt_irrefl _ h8
    · rintro rfl; rw [hroot] at h1; exact lt_irrefl _ h1
  refine ⟨ls, ⟨hls0, hroot, hlsI, fun ℓ hℓ hne => ex1_root_isMax (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hls0 hroot hℓ hne⟩, ?_⟩
  rintro l ⟨hl0, hlroot, -, -⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hanti hl0 hls0 h; rw [hlroot, hroot] at this; exact lt_irrefl _ this
  · have := hanti hls0 hl0 h; rw [hlroot, hroot] at this; exact lt_irrefl _ this

end AKMM.ComputationalTools
