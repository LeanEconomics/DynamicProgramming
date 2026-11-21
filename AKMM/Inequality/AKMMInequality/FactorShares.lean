/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Solow1956.Growth.Neoclassical

/-!
# §21.2.1: the labor share and the capital–output ratio

AKMM, §21.2.1, pp. 636–638. With a constant-returns production function
`F(A_k k, A_h h)` and competitive input pricing the capital share is
`r k/y = A_k F₁(A_k k, A_h h) k / F(A_k k, A_h h) = F₁(1, x)/F(1, x)`, `x = A_h h/(A_k k)`.

* `fs_partial_homog`, `fs_capital_share_homog`: the partial derivative `F₁` is homogeneous of
  degree zero, so the share depends only on `x` (p. 637).
* `fs_ces`, `fs_ces_hasDerivAt`, `fs_ces_capital_share`: for the CES function of footnote 8 the
  share is `1/(1 + ((1 − α)/α)^{1/ρ} x^{(ρ−1)/ρ})` (p. 637).
* `fs_share_strictAntiOn`, `fs_share_strictMonoOn`, `fs_cd_capital_share`: for `ρ > 1` a fall in
  `x` raises the share, for `ρ < 1` it lowers it, and under Cobb–Douglas it is `α` whatever `x`.
* `fs_bgp_ky`, `fs_steady_ky`: on a balanced growth path `sy = (δ + g)k`, so `k/y = s/(δ + g)`;
  the Solow steady state of `Solow1956` has `k*/f(k*) = s/(δ + g)`.
* `fs_ky_strictMonoOn`, `fs_ky_below`, `fs_ky_above`: `k/f(k)` is strictly increasing
  (Solow1956's `Technology.average_strictAnti`), so below the steady state `k/y` is below
  `s/(δ + g)` while `k` rises, and above it the reverse (p. 638).
-/

namespace AKMM.Inequality

open Solow1956.Neoclassical

/-- AKMM, p. 637: for `F` homogeneous of degree one, `F₁` is homogeneous of degree zero:
if `∂F/∂X(X, Y) = d` then `∂F/∂X(λX, λY) = d` for `λ > 0`. -/
theorem fs_partial_homog {F : ℝ → ℝ → ℝ}
    (hF : ∀ l : ℝ, 0 < l → ∀ x y, F (l * x) (l * y) = l * F x y)
    {X Y d l : ℝ} (hl : 0 < l) (hd : HasDerivAt (fun z => F z Y) d X) :
    HasDerivAt (fun z => F z (l * Y)) d (l * X) := by
  have hfun : (fun z => F z (l * Y)) = fun z => l * F (l⁻¹ * z) Y := by
    funext z
    rw [← hF l hl, ← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul]
  have hX : l⁻¹ * (l * X) = X := by field_simp
  have h1 : HasDerivAt (fun z => l⁻¹ * z) l⁻¹ (l * X) := by
    simpa using (hasDerivAt_id (l * X)).const_mul l⁻¹
  have h2 : HasDerivAt (fun z => F z Y) d (l⁻¹ * (l * X)) := by rw [hX]; exact hd
  have h3 := (h2.comp (l * X) h1).const_mul l
  rw [hfun]
  exact h3.congr_deriv (by field_simp)

/-- **AKMM, p. 637: the capital share depends only on `A_h h/(A_k k)`.** If `F` has constant
returns and `d = F₁(1, x)` with `x = A_h h/(A_k k)`, then `F₁(A_k k, A_h h) = d` and
`A_k F₁(A_k k, A_h h) k / F(A_k k, A_h h) = F₁(1, x)/F(1, x)`. -/
theorem fs_capital_share_homog {F : ℝ → ℝ → ℝ}
    (hF : ∀ l : ℝ, 0 < l → ∀ x y, F (l * x) (l * y) = l * F x y) {Ak k Ah h d : ℝ}
    (hk : 0 < Ak * k) (hd : HasDerivAt (fun z => F z (Ah * h / (Ak * k))) d 1) :
    HasDerivAt (fun z => F z (Ah * h)) d (Ak * k) ∧
      Ak * d * k / F (Ak * k) (Ah * h) = d / F 1 (Ah * h / (Ak * k)) := by
  have e1 : Ak * k * (Ah * h / (Ak * k)) = Ah * h := by
    rw [mul_comm]; exact div_mul_cancel₀ _ hk.ne'
  have hd' := fs_partial_homog hF hk hd
  rw [e1, mul_one] at hd'
  refine ⟨hd', ?_⟩
  have e2 : F (Ak * k) (Ah * h) = Ak * k * F 1 (Ah * h / (Ak * k)) := by
    rw [← hF _ hk, mul_one, e1]
  rw [e2]
  rcases eq_or_ne (F 1 (Ah * h / (Ak * k))) 0 with h0 | h0
  · simp [h0]
  · rw [show Ak * d * k = d * (Ak * k) by ring, mul_comm (Ak * k) (F 1 _),
      mul_div_mul_right _ _ hk.ne']

/-- AKMM, footnote 8, p. 637: the CES function with elasticity `ρ`,
`F(X, Y) = (α^{1/ρ} X^{(ρ−1)/ρ} + (1 − α)^{1/ρ} Y^{(ρ−1)/ρ})^{ρ/(ρ−1)}`. -/
noncomputable def fs_ces (α ρ X Y : ℝ) : ℝ :=
  (α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ)) ^ (ρ / (ρ - 1))

/-- AKMM, p. 637: the CES marginal product
`F₁(X, Y) = α^{1/ρ} X^{(ρ−1)/ρ − 1} S^{ρ/(ρ−1) − 1}`, `S` the inner sum. -/
theorem fs_ces_hasDerivAt {α ρ X Y : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun z => fs_ces α ρ z Y)
      (α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ - 1) *
        (α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ)) ^
          (ρ / (ρ - 1) - 1)) X := by
  have hS : 0 < α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ) := by
    have := Real.rpow_pos_of_pos hα (1 / ρ)
    have := Real.rpow_pos_of_pos hX ((ρ - 1) / ρ)
    have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
    have := Real.rpow_pos_of_pos hY ((ρ - 1) / ρ)
    positivity
  have hin : HasDerivAt (fun z => α ^ (1 / ρ) * z ^ ((ρ - 1) / ρ) +
      (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ))
      (α ^ (1 / ρ) * ((ρ - 1) / ρ * X ^ ((ρ - 1) / ρ - 1))) X :=
    ((Real.hasDerivAt_rpow_const (Or.inl hX.ne')).const_mul _).add_const _
  have h := hin.rpow_const (p := ρ / (ρ - 1)) (Or.inl hS.ne')
  unfold fs_ces
  convert h using 1
  have hr : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  field_simp

/-- **AKMM, p. 637: the CES capital share.** With `F` the CES function of footnote 8,
`r k/y = A_k F₁ k/F = 1/(1 + ((1 − α)/α)^{1/ρ} (A_h h/(A_k k))^{(ρ−1)/ρ})`. -/
theorem fs_ces_capital_share {α ρ Ak k Ah h : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (hX : 0 < Ak * k) (hY : 0 < Ah * h) :
    HasDerivAt (fun z => fs_ces α ρ z (Ah * h))
      (α ^ (1 / ρ) * (Ak * k) ^ ((ρ - 1) / ρ - 1) *
        (α ^ (1 / ρ) * (Ak * k) ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * (Ah * h) ^ ((ρ - 1) / ρ))
          ^ (ρ / (ρ - 1) - 1)) (Ak * k) ∧
    Ak * (α ^ (1 / ρ) * (Ak * k) ^ ((ρ - 1) / ρ - 1) *
        (α ^ (1 / ρ) * (Ak * k) ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * (Ah * h) ^ ((ρ - 1) / ρ))
          ^ (ρ / (ρ - 1) - 1)) * k / fs_ces α ρ (Ak * k) (Ah * h) =
      1 / (1 + ((1 - α) / α) ^ (1 / ρ) * (Ah * h / (Ak * k)) ^ ((ρ - 1) / ρ)) := by
  refine ⟨fs_ces_hasDerivAt hα hα1 hρ hρ1 hX hY, ?_⟩
  set X := Ak * k with hXd
  set Y := Ah * h
  set θ := (ρ - 1) / ρ
  set a := α ^ (1 / ρ)
  set b := (1 - α) ^ (1 / ρ)
  have ha : 0 < a := Real.rpow_pos_of_pos hα _
  have hb : 0 < b := Real.rpow_pos_of_pos (sub_pos.2 hα1) _
  have hXθ : 0 < X ^ θ := Real.rpow_pos_of_pos hX _
  have hYθ : 0 < Y ^ θ := Real.rpow_pos_of_pos hY _
  set S := a * X ^ θ + b * Y ^ θ with hSd
  have hS : 0 < S := by positivity
  have hpow : S ^ (ρ / (ρ - 1) - 1) = S ^ (ρ / (ρ - 1)) / S := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have hXp : X ^ (θ - 1) = X ^ θ / X := by rw [Real.rpow_sub hX, Real.rpow_one]
  have hF : fs_ces α ρ X Y = S ^ (ρ / (ρ - 1)) := rfl
  have hSp : 0 < S ^ (ρ / (ρ - 1)) := Real.rpow_pos_of_pos hS _
  have hlhs : Ak * (a * X ^ (θ - 1) * S ^ (ρ / (ρ - 1) - 1)) * k / fs_ces α ρ X Y =
      a * X ^ θ / S := by
    rw [show Ak * (a * X ^ (θ - 1) * S ^ (ρ / (ρ - 1) - 1)) * k =
      X * (a * X ^ (θ - 1) * S ^ (ρ / (ρ - 1) - 1)) by rw [hXd]; ring]
    rw [hF, hpow, hXp]
    have hX' : X ≠ 0 := hX.ne'
    field_simp
  rw [hlhs]
  have hratio : ((1 - α) / α) ^ (1 / ρ) * (Y / X) ^ θ = b * Y ^ θ / (a * X ^ θ) := by
    rw [Real.div_rpow (sub_pos.2 hα1).le hα.le, Real.div_rpow hY.le hX.le]
    field_simp
    exact mul_comm _ _
  rw [hratio]
  field_simp
  ring

/-- AKMM, p. 637: the share as a function of `x = A_h h/(A_k k)`: `1/(1 + c x^θ)`, with
`c = ((1 − α)/α)^{1/ρ}` and `θ = (ρ − 1)/ρ`. -/
noncomputable def fs_share (c θ x : ℝ) : ℝ := 1 / (1 + c * x ^ θ)

/-- **AKMM, p. 637.** "If `ρ > 1` … a decrease in `(A_h h)/(A_k k)` increases the capital
share": for `θ = (ρ − 1)/ρ > 0` and `c > 0` the share is strictly decreasing in `x > 0`. -/
theorem fs_share_strictAntiOn {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    StrictAntiOn (fs_share c θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have h1 : x ^ θ < y ^ θ := Real.rpow_lt_rpow hx'.le hxy hθ
  have h0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx' θ
  unfold fs_share
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

/-- AKMM, p. 637 (the case `ρ < 1`): for `θ = (ρ − 1)/ρ < 0` a decrease in `x` lowers the
capital share: the share is strictly increasing in `x > 0`. -/
theorem fs_share_strictMonoOn {c θ : ℝ} (hc : 0 < c) (hθ : θ < 0) :
    StrictMonoOn (fs_share c θ) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have h1 : y ^ θ < x ^ θ := Real.rpow_lt_rpow_of_neg hx' hxy hθ
  have h0 : 0 < y ^ θ := Real.rpow_pos_of_pos hy' θ
  unfold fs_share
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

/-- AKMM, `θ = (ρ − 1)/ρ` has the sign of `ρ − 1` for `ρ > 0`. -/
theorem fs_theta_pos_iff {ρ : ℝ} (hρ : 0 < ρ) : 0 < (ρ - 1) / ρ ↔ 1 < ρ := by
  rw [div_pos_iff_of_pos_right hρ, sub_pos]

/-- **AKMM, p. 636: Cobb–Douglas shares are invariant.** For `F = X^α Y^{1−α}`,
`X ∂F/∂X / F = α` whatever `X, Y > 0`. -/
theorem fs_cd_capital_share {α X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun z => z ^ α * Y ^ (1 - α)) (α * X ^ (α - 1) * Y ^ (1 - α)) X ∧
      X * (α * X ^ (α - 1) * Y ^ (1 - α)) / (X ^ α * Y ^ (1 - α)) = α := by
  refine ⟨((Real.hasDerivAt_rpow_const (Or.inl hX.ne')).mul_const _), ?_⟩
  have hXa : 0 < X ^ α := Real.rpow_pos_of_pos hX α
  have hYa : 0 < Y ^ (1 - α) := Real.rpow_pos_of_pos hY _
  rw [Real.rpow_sub hX, Real.rpow_one]
  field_simp

/-- **AKMM, p. 637: `k/y` on a balanced growth path.** `sy = (δ + g)k` with `y ≠ 0`,
`δ + g ≠ 0` gives `k/y = s/(δ + g)`. -/
theorem fs_bgp_ky {s δ g k y : ℝ} (hy : y ≠ 0) (hm : δ + g ≠ 0) (h : s * y = (δ + g) * k) :
    k / y = s / (δ + g) := by
  rw [div_eq_div_iff hy hm]
  linarith

/-- AKMM, p. 637, with `Solow1956`'s neoclassical technology: the unique positive steady state
`k*` of `k̇ = s f(k) − (δ + g)k` has `k*/f(k*) = s/(δ + g)`. -/
theorem fs_steady_ky {f : ℝ → ℝ} (hf : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    ∃! k : ℝ, 0 < k ∧ rate f s m k = 0 ∧ k / f k = s / m := by
  obtain ⟨k, ⟨hk, hr⟩, hu⟩ := existsUnique_steadyState hf hs hm
  have hfk := hf.output_pos hk
  have hky : k / f k = s / m := by
    rw [div_eq_div_iff hfk.ne' hm.ne']; simp only [rate] at hr; linarith
  exact ⟨k, ⟨hk, hr, hky⟩, fun y hy => hu y ⟨hy.1, hy.2.1⟩⟩

/-- **AKMM, p. 638: "`k/y = k/F(k, h)` is an increasing function of `k`"**, for a neoclassical
`f = F(·, h)` (strictly concave, `f(0) = 0`): `k/f(k)` is strictly increasing on `k > 0`. -/
theorem fs_ky_strictMonoOn {f : ℝ → ℝ} (hf : Technology f) :
    StrictMonoOn (fun k => k / f k) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have h := hf.average_strictAnti hx hy hxy
  have hfx := hf.output_pos hx'
  have hfy := hf.output_pos hy'
  simp only at h ⊢
  rw [div_lt_div_iff₀ hfx hfy]
  rw [div_lt_div_iff₀ hy' hx'] at h
  linarith

/-- **AKMM, p. 638.** Below the steady state `k*`, `k/y < s/(δ + g)` and capital rises, so `k/y`
increases toward its steady-state value. -/
theorem fs_ky_below {f : ℝ → ℝ} (hf : Technology f) {s m ks k : ℝ} (hs : 0 < s) (hm : 0 < m)
    (hk : 0 < k) (hkk : k < ks) (hks : rate f s m ks = 0) :
    k / f k < s / m ∧ 0 < rate f s m k := by
  have hkspos := hk.trans hkk
  have hky : ks / f ks = s / m := by
    rw [div_eq_div_iff (hf.output_pos hkspos).ne' hm.ne']; simp only [rate] at hks; linarith
  exact ⟨hky ▸ fs_ky_strictMonoOn hf hk hkspos hkk, rate_pos_below hf hs hk hkk hks⟩

/-- **AKMM, p. 638.** Above the steady state, `k/y > s/(δ + g)` and capital falls. -/
theorem fs_ky_above {f : ℝ → ℝ} (hf : Technology f) {s m ks k : ℝ} (hs : 0 < s) (hm : 0 < m)
    (hkspos : 0 < ks) (hkk : ks < k) (hks : rate f s m ks = 0) :
    s / m < k / f k ∧ rate f s m k < 0 := by
  have hky : ks / f ks = s / m := by
    rw [div_eq_div_iff (hf.output_pos hkspos).ne' hm.ne']; simp only [rate] at hks; linarith
  exact ⟨hky ▸ fs_ky_strictMonoOn hf hkspos (hkspos.trans hkk) hkk,
    rate_neg_above hf hs hkspos hkk hks⟩

end AKMM.Inequality
