/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optimal savings without labor income: the CRRA solution

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.3.2.3 (pp. 43–45).

With `Y ≡ 0`, CRRA utility `u(c) = c^{1−γ}/(1 − γ)` (`γ > 0`, `γ ≠ 1`) (1.52), `R > 0` and
`βR^{1−γ} < 1`:

* **Exercise 1.3.3**: lifetime values of all feasible policies are bounded above by a function
  `m(w)`: every partial sum `∑_{t<n} βᵗu(C_t)` is at most `u(w)/(1 − βR^{1−γ})` when `γ < 1`
  and at most `0` when `γ > 1`.
* (1.55): `η = 1 − (βR^{1−γ})^{1/γ}` lies in `(0, 1)` and `(1 − η)^γ = βR^{1−γ}`.
* (1.54): `v*(w) = η^{−γ}u(w)` solves the Bellman equation
  `v(w) = max_{0 < c < w} {u(c) + βv(R(w − c))}`, with the maximum attained at `c = ηw` (the
  linear policy (1.53)). The proof replaces the book's first-order condition by the tangent
  line inequality for the concave function `u`.
* The consumption growth factor is `C_{t+1}/C_t = R(1 − η) = (βR)^{1/γ}` (p. 45).
-/

open Finset

namespace SargentStachurski.PreludeExamples

/-- CRRA utility (1.52): `u(c) = c^{1−γ}/(1 − γ)`. -/
noncomputable def crra (γ c : ℝ) : ℝ := c ^ (1 - γ) / (1 - γ)

/-- Bernoulli's inequality in the form used here: for `p < 1`, `p ≠ 0` and `t > 0`,
`(tᵖ − 1)/p ≤ t − 1`. -/
theorem rpow_sub_one_div_le {p t : ℝ} (hp1 : p < 1) (hp0 : p ≠ 0) (ht : 0 < t) :
    (t ^ p - 1) / p ≤ t - 1 := by
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · -- `p < 0`: Bernoulli with exponent `1 − p ≥ 1` at `t⁻¹`
    have hb := one_add_mul_self_le_rpow_one_add (s := t⁻¹ - 1)
      (by have := inv_pos.2 ht; linarith) (p := 1 - p) (by linarith)
    rw [show 1 + (t⁻¹ - 1) = t⁻¹ by ring, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le,
      neg_sub] at hb
    have h2 : t ^ p = t * t ^ (p - 1) := by
      rw [← Real.rpow_one_add' ht.le (by linarith), show 1 + (p - 1) = p by ring]
    have h3 : 1 + p * (t - 1) ≤ t ^ p := by
      rw [h2]
      calc 1 + p * (t - 1) = t * (1 + (1 - p) * (t⁻¹ - 1)) := by field_simp; ring
        _ ≤ t * t ^ (p - 1) := mul_le_mul_of_nonneg_left hb ht.le
    rw [div_le_iff_of_neg hneg]
    linarith
  · -- `0 < p < 1`
    have hb := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hpos.le hp1.le
    rw [show 1 + (t - 1) = t by ring] at hb
    rw [div_le_iff₀ hpos]
    linarith

/-- The tangent line inequality for CRRA utility: `u(c) ≤ u(c₀) + c₀^{−γ}(c − c₀)` for
`c, c₀ > 0`, since `u` is concave with `u'(c₀) = c₀^{−γ}`. -/
theorem crra_le_tangent {γ c c₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≠ 1) (hc : 0 < c) (hc₀ : 0 < c₀) :
    crra γ c ≤ crra γ c₀ + c₀ ^ (-γ) * (c - c₀) := by
  have hp1 : 1 - γ < 1 := by linarith
  have hp0 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  have key := rpow_sub_one_div_le hp1 hp0 (div_pos hc hc₀)
  rw [Real.div_rpow hc.le hc₀.le] at key
  have hc₀p : 0 < c₀ ^ (1 - γ) := Real.rpow_pos_of_pos hc₀ _
  have e2 : c₀ ^ (-γ) = c₀ ^ (1 - γ) / c₀ := by
    rw [show -γ = (1 - γ) - 1 by ring, Real.rpow_sub_one hc₀.ne']
  have h := mul_le_mul_of_nonneg_left key hc₀p.le
  have l : c₀ ^ (1 - γ) * ((c ^ (1 - γ) / c₀ ^ (1 - γ) - 1) / (1 - γ)) =
      c ^ (1 - γ) / (1 - γ) - c₀ ^ (1 - γ) / (1 - γ) := by
    field_simp
  have r : c₀ ^ (1 - γ) * (c / c₀ - 1) = c₀ ^ (1 - γ) / c₀ * (c - c₀) := by
    field_simp
  rw [l, r] at h
  rw [crra, crra, e2]
  linarith

variable {β R γ : ℝ}

/-- (1.55): `η = 1 − (βR^{1−γ})^{1/γ}`. -/
noncomputable def crraEta (β R γ : ℝ) : ℝ := 1 - (β * R ^ (1 - γ)) ^ (1 / γ)

/-- (1.55) (p. 44): if `0 < βR^{1−γ} < 1` then `0 < η < 1` and `(1 − η)^γ = βR^{1−γ}`. -/
theorem crraEta_spec (hγ : 0 < γ) (hk0 : 0 < β * R ^ (1 - γ)) (hk1 : β * R ^ (1 - γ) < 1) :
    0 < crraEta β R γ ∧ crraEta β R γ < 1 ∧ (1 - crraEta β R γ) ^ γ = β * R ^ (1 - γ) := by
  have hpos : 0 < (β * R ^ (1 - γ)) ^ (1 / γ) := Real.rpow_pos_of_pos hk0 _
  have hlt : (β * R ^ (1 - γ)) ^ (1 / γ) < 1 := Real.rpow_lt_one hk0.le hk1 (by positivity)
  refine ⟨by unfold crraEta; linarith, by unfold crraEta; linarith, ?_⟩
  rw [crraEta, sub_sub_cancel, one_div, Real.rpow_inv_rpow hk0.le hγ.ne']

/-- (p. 45): the consumption growth factor `R(1 − η)` equals `(βR)^{1/γ}`. -/
theorem crra_growth (hγ : 0 < γ) (hβ : 0 ≤ β) (hR : 0 < R) :
    R * (1 - crraEta β R γ) = (β * R) ^ (1 / γ) := by
  rw [crraEta, sub_sub_cancel, Real.mul_rpow hβ (Real.rpow_nonneg hR.le _),
    ← Real.rpow_mul hR.le, Real.mul_rpow hβ hR.le]
  have h1 : 1 + (1 - γ) * (1 / γ) = 1 / γ := by
    field_simp
    ring
  have : R * R ^ ((1 - γ) * (1 / γ)) = R ^ (1 / γ) := by
    rw [← Real.rpow_one_add' hR.le (by rw [h1]; positivity), h1]
  linear_combination β ^ (1 / γ) * this

/-- (1.54), the value: with `η` from (1.55) and `m = η^{−γ}`, the linear policy `c = ηw` attains
`u(ηw) + βm u(R(1 − η)w) = m u(w)`, so `v*(w) = η^{−γ}u(w)`. -/
theorem crra_value (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hR : 0 < R) (hk0 : 0 < β * R ^ (1 - γ))
    (hk1 : β * R ^ (1 - γ) < 1) {w : ℝ} (hw : 0 < w) :
    crra γ (crraEta β R γ * w) +
        β * (crraEta β R γ ^ (-γ) * crra γ (R * (w - crraEta β R γ * w))) =
      crraEta β R γ ^ (-γ) * crra γ w := by
  obtain ⟨ha0, ha1, hb⟩ := crraEta_spec hγ hk0 hk1
  set a := crraEta β R γ
  have hb0 : 0 < 1 - a := by linarith
  have hp0 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  have e1 : (a * w) ^ (1 - γ) = a * a ^ (-γ) * w ^ (1 - γ) := by
    rw [Real.mul_rpow ha0.le hw.le, show 1 - γ = 1 + -γ by ring,
      Real.rpow_add ha0, Real.rpow_one]
  have e2 : (R * (w - a * w)) ^ (1 - γ) = R ^ (1 - γ) * (1 - a) ^ (1 - γ) * w ^ (1 - γ) := by
    rw [show w - a * w = (1 - a) * w by ring, ← mul_assoc,
      Real.mul_rpow (mul_pos hR hb0).le hw.le, Real.mul_rpow hR.le hb0.le]
  have e3 : β * R ^ (1 - γ) * (1 - a) ^ (1 - γ) = 1 - a := by
    rw [← hb, ← Real.rpow_add hb0, show γ + (1 - γ) = 1 by ring, Real.rpow_one]
  simp only [crra, e1, e2]
  linear_combination (a ^ (-γ) * w ^ (1 - γ) / (1 - γ)) * e3

/-- (1.54), the maximum: for `0 < c < w`, `u(c) + βm u(R(w − c)) ≤ m u(w)` with `m = η^{−γ}`.
Together with `crra_value`, `v*(w) = η^{−γ}u(w)` solves the Bellman equation (1.54) and the
linear policy `σ(w) = ηw` (1.53) attains the maximum. -/
theorem crra_bellman_le (hγ : 0 < γ) (hγ1 : γ ≠ 1) (hR : 0 < R) (hk0 : 0 < β * R ^ (1 - γ))
    (hk1 : β * R ^ (1 - γ) < 1) {w c : ℝ} (hc : 0 < c) (hcw : c < w) :
    crra γ c + β * (crraEta β R γ ^ (-γ) * crra γ (R * (w - c))) ≤
      crraEta β R γ ^ (-γ) * crra γ w := by
  obtain ⟨ha0, ha1, hb⟩ := crraEta_spec hγ hk0 hk1
  have hw : 0 < w := hc.trans hcw
  set a := crraEta β R γ
  have hb0 : 0 < 1 - a := by linarith
  have hβ : 0 < β := by
    have : 0 < R ^ (1 - γ) := Real.rpow_pos_of_pos hR _
    exact pos_of_mul_pos_left hk0 this.le
  have hm : 0 < a ^ (-γ) := Real.rpow_pos_of_pos ha0 _
  -- tangent lines at `c₀ = ηw` and `d₀ = R(1 − η)w`
  have t1 := crra_le_tangent hγ hγ1 hc (mul_pos ha0 hw)
  have t2 := crra_le_tangent hγ hγ1 (mul_pos hR (sub_pos.2 hcw))
    (mul_pos hR (sub_pos.2 (show a * w < w by nlinarith)))
  -- the first-order condition `c₀^{−γ} = βmR d₀^{−γ}`
  have foc : (a * w) ^ (-γ) = β * a ^ (-γ) * R * (R * (w - a * w)) ^ (-γ) := by
    rw [show w - a * w = (1 - a) * w by ring, ← mul_assoc,
      Real.mul_rpow (mul_pos hR hb0).le hw.le, Real.mul_rpow hR.le hb0.le,
      Real.mul_rpow ha0.le hw.le]
    have hRR : R * R ^ (-γ) = R ^ (1 - γ) := by
      rw [show 1 - γ = 1 + -γ by ring, Real.rpow_add hR, Real.rpow_one]
    have hbb : (1 - a) ^ (-γ) = (β * R ^ (1 - γ))⁻¹ := by
      rw [Real.rpow_neg hb0.le, hb]
    rw [hbb]
    have hKK : β * R ^ (1 - γ) * (β * R ^ (1 - γ))⁻¹ = 1 := mul_inv_cancel₀ hk0.ne'
    linear_combination (-(β * a ^ (-γ) * (β * R ^ (1 - γ))⁻¹ * w ^ (-γ))) * hRR +
      (-(a ^ (-γ) * w ^ (-γ))) * hKK
  have hval := crra_value hγ hγ1 hR hk0 hk1 hw
  have hβm : 0 ≤ β * a ^ (-γ) := (mul_pos hβ hm).le
  have hsplit : R * (w - c) - R * (w - a * w) = -R * (c - a * w) := by ring
  rw [hsplit] at t2
  have t2' := mul_le_mul_of_nonneg_left t2 hβm
  calc crra γ c + β * (a ^ (-γ) * crra γ (R * (w - c)))
      = crra γ c + β * a ^ (-γ) * crra γ (R * (w - c)) := by ring
    _ ≤ (crra γ (a * w) + (a * w) ^ (-γ) * (c - a * w)) +
        β * a ^ (-γ) * (crra γ (R * (w - a * w)) +
          (R * (w - a * w)) ^ (-γ) * (-R * (c - a * w))) := add_le_add t1 t2'
    _ = a ^ (-γ) * crra γ w := by linear_combination hval + (c - a * w) * foc

/-! ### Exercise 1.3.3 -/

/-- Wealth along a deterministic path (`Y ≡ 0`): `W_{t+1} = R(W_t − σ(W_t))`. -/
def crraPath (R : ℝ) (σ : ℝ → ℝ) (w : ℝ) : ℕ → ℝ
  | 0 => w
  | t + 1 => R * (crraPath R σ w t - σ (crraPath R σ w t))

/-- **Exercise 1.3.3** (p. 43): if `βR^{1−γ} < 1`, every feasible policy (`0 ≤ σ(w) ≤ w`) has
lifetime value at most `m(w)`, where `m(w) = u(w)/(1 − βR^{1−γ})` for `γ < 1` and `m(w) = 0`
for `γ > 1`: every partial sum of `∑ βᵗu(σ(W_t))` is at most `m(w)`. -/
theorem crra_lifetime_bound (hγ1 : γ ≠ 1) (hβ : 0 ≤ β) (hR : 0 < R)
    (hk1 : β * R ^ (1 - γ) < 1) {σ : ℝ → ℝ} (hσ0 : ∀ w, 0 ≤ w → 0 ≤ σ w)
    (hσw : ∀ w, 0 ≤ w → σ w ≤ w) {w : ℝ} (hw : 0 ≤ w) (n : ℕ) :
    ∑ t ∈ range n, β ^ t * crra γ (σ (crraPath R σ w t)) ≤
      if γ < 1 then crra γ w / (1 - β * R ^ (1 - γ)) else 0 := by
  -- the path stays in `[0, Rᵗw]`
  have hpath : ∀ t, 0 ≤ crraPath R σ w t ∧ crraPath R σ w t ≤ R ^ t * w := by
    intro t
    induction t with
    | zero => simp [crraPath, hw]
    | succ t ih =>
      obtain ⟨h0, h1⟩ := ih
      have := hσw _ h0
      have := hσ0 _ h0
      refine ⟨mul_nonneg hR.le (by linarith), ?_⟩
      simp only [crraPath, pow_succ]
      nlinarith
  split_ifs with hlt
  · -- `γ < 1`: `u ≥ 0` is increasing and `u(Rᵗw) = (R^{1−γ})ᵗu(w)`
    have hp : 0 < 1 - γ := by linarith
    have hk0 : 0 ≤ β * R ^ (1 - γ) := mul_nonneg hβ (Real.rpow_nonneg hR.le _)
    have hterm : ∀ t, β ^ t * crra γ (σ (crraPath R σ w t)) ≤
        (β * R ^ (1 - γ)) ^ t * crra γ w := by
      intro t
      obtain ⟨h0, h1⟩ := hpath t
      have hc0 := hσ0 _ h0
      have hc1 := (hσw _ h0).trans h1
      have hmono : σ (crraPath R σ w t) ^ (1 - γ) ≤ (R ^ t * w) ^ (1 - γ) :=
        Real.rpow_le_rpow hc0 hc1 hp.le
      have hsplit : (R ^ t * w) ^ (1 - γ) = (R ^ (1 - γ)) ^ t * w ^ (1 - γ) := by
        rw [Real.mul_rpow (pow_nonneg hR.le t) hw, ← Real.rpow_natCast_mul hR.le,
          mul_comm (t : ℝ), Real.rpow_mul_natCast hR.le]
      rw [mul_pow, mul_assoc, crra, crra]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ t)
      rw [← mul_div_assoc, ← hsplit]
      exact div_le_div_of_nonneg_right hmono hp.le
    calc ∑ t ∈ range n, β ^ t * crra γ (σ (crraPath R σ w t))
        ≤ ∑ t ∈ range n, (β * R ^ (1 - γ)) ^ t * crra γ w := sum_le_sum fun t _ => hterm t
      _ = crra γ w * ∑ t ∈ range n, (β * R ^ (1 - γ)) ^ t := by rw [mul_sum]; simp [mul_comm]
      _ ≤ crra γ w * (1 / (1 - β * R ^ (1 - γ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Real.rpow_nonneg hw _) hp.le)
          have hk1' : 0 < 1 - β * R ^ (1 - γ) := by linarith
          rw [geom_sum_eq (by linarith : β * R ^ (1 - γ) ≠ 1) n]
          have e : ((β * R ^ (1 - γ)) ^ n - 1) / (β * R ^ (1 - γ) - 1) =
              (1 - (β * R ^ (1 - γ)) ^ n) / (1 - β * R ^ (1 - γ)) := by
            rw [← neg_sub, ← neg_sub (1 : ℝ) (β * R ^ (1 - γ)), neg_div_neg_eq]
          rw [e]
          exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hk0 n]) hk1'.le
      _ = crra γ w / (1 - β * R ^ (1 - γ)) := by ring
  · -- `γ > 1`: `u ≤ 0`
    have hp : 1 - γ < 0 := by
      have : 1 < γ := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hγ1)
      linarith
    refine sum_nonpos fun t _ => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ t) ?_
    exact div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hσ0 _ (hpath t).1) _) hp.le

end SargentStachurski.PreludeExamples
