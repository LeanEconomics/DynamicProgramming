/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic

/-!
# Balanced growth and CRRA utility: Theorem .4

AKMM, App. 4.A.2, pp. 829–830.

* `bgp_marginal_ratio`: on a balanced path `c_{t+1} = (1 + γ)c_t` the Euler equation
  `u'(c_t) = β(1 + r)u'(c_{t+1})` gives `u'((1 + γ)c)/u'(c) = 1/(β(1 + r))`; the book prints
  `(1 + r)/β` (the constancy in `c`, which is all the proof uses, is unaffected).
* **Theorem .4** (`theorem_4A_4`): if `u` is twice differentiable on `(0, ∞)`, `u' > 0`, and for
  every growth rate `γ > −1` the ratio `u'((1 + γ)c)/u'(c)` does not depend on `c`, then
  `u'(c) = u'(1)c^{−σ}` and `u` is a positive affine transformation of `log c` (`σ = 1`) or of
  `c^{1−σ}/(1 − σ)`; and `σ > 0` iff `u'` is strictly decreasing (`theorem_4A_4_sigma_pos`).
* The book's statement — `u = log c` or `u = c^{1−σ}/(1 − σ)` with `σ > 0` — holds only up to
  positive affine transformations (`theorem_4A_4_affine_counterexample`, `u = 2 log c`) and needs
  concavity for `σ > 0` (`u = c²/2` has `σ = −1`, `theorem_4A_4_convex_example`).
-/

namespace AKMM.DynamicOptimization

open Real

/-- AKMM, p. 830, corrected: on a balanced path `c' = (1 + γ)c`, the Euler equation
`u'(c) = β(1 + r)u'(c')` gives `u'((1 + γ)c)/u'(c) = 1/(β(1 + r))`. -/
theorem bgp_marginal_ratio {u' : ℝ → ℝ} {β r γ c : ℝ} (hβr : β * (1 + r) ≠ 0)
    (hu : u' c ≠ 0) (heuler : u' c = β * (1 + r) * u' ((1 + γ) * c)) :
    u' ((1 + γ) * c) / u' c = 1 / (β * (1 + r)) := by
  rw [div_eq_div_iff hu hβr, heuler]; ring

/-- Constancy on `(0, ∞)` from a zero derivative. -/
theorem crraBGP_const {φ : ℝ → ℝ} (hφ : ∀ x, 0 < x → HasDerivAt φ 0 x) {x : ℝ} (hx : 0 < x) :
    φ x = φ 1 :=
  isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
    (fun y hy => (hφ y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hφ y hy).deriv) hx (Set.mem_Ioi.2 one_pos)

/-- **Theorem .4** (AKMM, App. 4.A.2, pp. 829–830). Let `u` have derivative `u' > 0` and `u'` have
derivative `u''` on `(0, ∞)`. If for every `γ > −1` there is `#(γ)` with
`u'((1 + γ)c) = #(γ)u'(c)` for all `c > 0`, then with `σ = −u''(1)/u'(1)`:
`u'(c) = u'(1)c^{−σ}`, and `u(c) = u'(1) log c + u(1)` if `σ = 1`, otherwise
`u(c) = u'(1)c^{1−σ}/(1 − σ) + b` for a constant `b`. -/
theorem theorem_4A_4 {u u' u'' : ℝ → ℝ} (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hu' : ∀ c, 0 < c → HasDerivAt u' (u'' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hbgp : ∀ γ, -1 < γ → ∃ M, ∀ c, 0 < c → u' ((1 + γ) * c) = M * u' c) :
    (∀ c, 0 < c → u' c = u' 1 * c ^ (-(-u'' 1 / u' 1))) ∧
      ((-u'' 1 / u' 1 = 1 → ∀ c, 0 < c → u c = u' 1 * Real.log c + u 1) ∧
        (-u'' 1 / u' 1 ≠ 1 → ∃ b, ∀ c, 0 < c →
          u c = u' 1 * c ^ (1 - -u'' 1 / u' 1) / (1 - -u'' 1 / u' 1) + b)) := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = -u'' 1 / u' 1 := ⟨_, rfl⟩
  rw [← hσdef]
  have h1 : 0 < u' 1 := hpos 1 one_pos
  -- the multiplicative equation `u'(xc) = (u'(x)/u'(1))u'(c)`
  have hmul : ∀ x, 0 < x → ∀ c, 0 < c → u' (x * c) = u' x / u' 1 * u' c := by
    intro x hx c hc
    obtain ⟨M, hM⟩ := hbgp (x - 1) (by linarith)
    have e : 1 + (x - 1) = x := by ring
    have hM1 := hM 1 one_pos
    rw [e, mul_one] at hM1
    have hMc := hM c hc
    rw [e] at hMc
    rw [hMc, hM1]
    field_simp
  -- differentiating in `c` at `c = 1`: `x u''(x) = (u'(x)/u'(1)) u''(1)`
  have hode : ∀ x, 0 < x → x * u'' x = -σ * u' x := by
    intro x hx
    have hl : HasDerivAt (fun c => u' (x * c)) (u'' (x * 1) * x) 1 := by
      have := (hu' (x * 1) (by linarith)).comp 1 ((hasDerivAt_id (1 : ℝ)).const_mul x)
      simpa [Function.comp_def] using this
    have hr : HasDerivAt (fun c => u' x / u' 1 * u' c) (u' x / u' 1 * u'' 1) 1 :=
      (hu' 1 one_pos).const_mul _
    have heq : (fun c => u' (x * c)) =ᶠ[nhds 1] fun c => u' x / u' 1 * u' c :=
      Filter.eventually_of_mem (Ioi_mem_nhds one_pos) fun c hc => hmul x hx c hc
    have := hl.unique (hr.congr_of_eventuallyEq heq)
    rw [mul_one, div_mul_eq_mul_div, eq_div_iff h1.ne'] at this
    rw [hσdef]
    field_simp
    linear_combination this
  -- `u'(x)x^σ` is constant
  have hconst : ∀ x, 0 < x → u' x * x ^ σ = u' 1 := by
    intro x hx
    have hd : ∀ y, 0 < y → HasDerivAt (fun y => u' y * y ^ σ) 0 y := by
      intro y hy
      have h2 := (hu' y hy).mul (hasDerivAt_rpow_const (p := σ) (Or.inl hy.ne'))
      convert h2 using 1
      have h3 : u'' y = -σ * u' y / y := by rw [← hode y hy]; field_simp
      rw [rpow_sub_one hy.ne', h3]
      field_simp
      ring
    have := crraBGP_const hd hx
    simpa using this
  have hform : ∀ c, 0 < c → u' c = u' 1 * c ^ (-σ) := by
    intro c hc
    rw [← hconst c hc, mul_assoc, ← rpow_add hc, add_neg_cancel, rpow_zero, mul_one]
  refine ⟨hform, fun hσ c hc => ?_, fun hσ => ?_⟩
  · -- `σ = 1`: `u − u'(1) log` has zero derivative
    have hd : ∀ y, 0 < y → HasDerivAt (fun y => u y - u' 1 * Real.log y) 0 y := by
      intro y hy
      have h2 := (hu y hy).sub ((Real.hasDerivAt_log hy.ne').const_mul (u' 1))
      convert h2 using 1
      rw [hform y hy, hσ, rpow_neg hy.le, rpow_one]
      ring
    have := crraBGP_const hd hc
    simp only [Real.log_one, mul_zero, sub_zero] at this
    linarith
  · -- `σ ≠ 1`: `u − u'(1)c^{1−σ}/(1 − σ)` has zero derivative
    have h1σ : (1 - σ) ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    refine ⟨u 1 - u' 1 / (1 - σ), fun c hc => ?_⟩
    have hd : ∀ y, 0 < y → HasDerivAt (fun y => u y - u' 1 * y ^ (1 - σ) / (1 - σ)) 0 y := by
      intro y hy
      have h2 := (hu y hy).sub (((hasDerivAt_rpow_const (p := 1 - σ)
        (Or.inl hy.ne')).const_mul (u' 1)).div_const (1 - σ))
      convert h2 using 1
      rw [hform y hy, show 1 - σ - 1 = -σ by ring]
      field_simp
      ring
    have := crraBGP_const hd hc
    simp only [one_rpow, mul_one] at this
    linarith

/-- **AKMM, Theorem .4: `σ > 0` needs concavity.** If `u'(c) = u'(1)c^{−σ}` with `u'(1) > 0`, then
`σ > 0` iff `u'` is strictly decreasing on `(0, ∞)`. -/
theorem theorem_4A_4_sigma_pos {u' : ℝ → ℝ} {σ : ℝ} (h1 : 0 < u' 1)
    (hform : ∀ c, 0 < c → u' c = u' 1 * c ^ (-σ)) :
    0 < σ ↔ StrictAntiOn u' (Set.Ioi 0) := by
  constructor
  · intro hσ x hx y hy hxy
    rw [hform x hx, hform y hy]
    exact mul_lt_mul_of_pos_left (rpow_lt_rpow_of_neg hx hxy (by linarith)) h1
  · intro h
    by_contra hle
    push Not at hle
    have := h (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos) one_lt_two
    rw [hform 1 one_pos, hform 2 two_pos, one_rpow, mul_one] at this
    have : 1 ≤ (2 : ℝ) ^ (-σ) := one_le_rpow (by norm_num) (by linarith)
    nlinarith

/-- **AKMM, Theorem .4 as printed is false: affine transformations.** `u(c) = 2 log c` satisfies
the balanced-growth hypothesis (`u'((1 + γ)c) = (1 + γ)^{−1}u'(c)`) but is neither `log c` nor
`c^{1−σ}/(1 − σ)` for any `σ`. -/
theorem theorem_4A_4_affine_counterexample :
    (∀ γ : ℝ, -1 < γ → ∀ c : ℝ, 0 < c → 2 / ((1 + γ) * c) = (1 + γ)⁻¹ * (2 / c)) ∧
      (∃ c : ℝ, 0 < c ∧ 2 * Real.log c ≠ Real.log c) ∧
      ∀ σ : ℝ, (fun c : ℝ => 2 * Real.log c) 1 ≠ (1 : ℝ) ^ (1 - σ) / (1 - σ) ∨ σ = 1 := by
  refine ⟨fun γ hγ c hc => ?_, ⟨2, two_pos, fun h => ?_⟩, fun σ => ?_⟩
  · have : (1 + γ) ≠ 0 := by linarith
    field_simp
  · have : Real.log 2 = 0 := by linarith
    exact absurd this (Real.log_pos one_lt_two).ne'
  · by_cases hσ : σ = 1
    · exact Or.inr hσ
    · left
      simp only [Real.log_one, mul_zero, one_rpow]
      exact (one_div_ne_zero (sub_ne_zero.2 (Ne.symm hσ))).symm

/-- **AKMM, Theorem .4: without concavity `σ` can be negative.** `u(c) = c²/2`, with `u'(c) = c`
and `u''(c) = 1`, satisfies every hypothesis of `theorem_4A_4` (`u'((1 + γ)c) = (1 + γ)u'(c)`),
and its `σ = −u''(1)/u'(1)` is `−1 < 0`. -/
theorem theorem_4A_4_convex_example :
    (∀ c : ℝ, 0 < c → HasDerivAt (fun c : ℝ => c ^ 2 / 2) c c) ∧
      (∀ c : ℝ, 0 < c → HasDerivAt (fun c : ℝ => c) 1 c) ∧ (∀ c : ℝ, 0 < c → 0 < c) ∧
      (∀ γ : ℝ, -1 < γ → ∃ M, ∀ c : ℝ, 0 < c → (1 + γ) * c = M * c) ∧
      -(1 : ℝ) / 1 < 0 := by
  refine ⟨fun c _ => ?_, fun c _ => hasDerivAt_id c, fun c hc => hc,
    fun γ _ => ⟨1 + γ, fun c _ => rfl⟩, by norm_num⟩
  have := (hasDerivAt_pow 2 c).div_const 2
  convert this using 1
  ring

end AKMM.DynamicOptimization
