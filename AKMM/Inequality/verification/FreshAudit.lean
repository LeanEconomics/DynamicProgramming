import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Solow1956.Growth.Neoclassical
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import AKMMConsumption.Deterministic
import LifeCycleFiscalPolicy.RicardianEquivalence
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import IncompleteMarkets.SIStationary
import Mathlib.Analysis.Calculus.Deriv.Slope
import IncompleteMarkets.AYComputation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.IdentDistrib
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §21.2.2: wage inequality

AKMM, §21.2.2, pp. 638–641. Relative wages are ratios of marginal products.

* `fs_ces_symm`, `wi_ces_hasDerivAt`: the CES marginal product is `F₁ = α^{1/ρ}(F/X)^{1/ρ}`.
* **Katz–Murphy** (p. 639): `km_premium_eq`, `km_log_premium`: with `G` CES,
  `log(w_s/w_u) = −(1/ρ) log(s/u) + ((ρ − 1)/ρ) log(A_s/A_u) + (1/ρ) log((1 − α)/α)`;
  `km_premium_strictAnti_supply`, `km_sbtc_strictMono_iff`: the premium falls with `s/u` and
  rises with `A_s/A_u` iff `ρ > 1`; `km_cd_premium`: under Cobb–Douglas `A_s/A_u` drops out;
  `km_identify`: the regression coefficients identify `ρ` and `γ`.
* **Directed technical change** (pp. 640–641): `dt_term_le` (Bernoulli's inequality), `dt_optimal`
  (the first-order condition is sufficient and the optimum unique), `dt_foc_iff_ratio`,
  `dt_exists`, `dt_maximiser_ratio`: the optimum has
  `A_s/A_u = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}`; the printed factor `λ/(1 − λ)` is right only
  for `λ = 1/2` (`dt_printed_ratio_iff`); `dt_ratio_strictMono`; `dt_wage_ratio`,
  `dt_premium_closed`, `dt_log_premium`: `log(w_s/w_u) = (σ/(σ − φ)) log(λ/(1 − λ))
  + ((σ − φ(1 − σ))/(φ − σ)) log(s/u)`; `dt_exponent_pos_iff`, `dt_rho_gt_two`.
* **Capital–skill complementarity** (p. 641): `cs_ex1_wages`, `cs_ex1_premium_strictMono`
  (`u + s^ν k^{1−ν}`); `cs_ex2_wu_strictAnti` (`s^ν (k + u)^{1−ν}`); `cs_nest_wu`,
  `cs_nest_wu_monotone` (under `F(u, G(k, s))` the unskilled wage cannot fall as `k` rises);
  `cs_ces_nest_premium`, `cs_ces_nest_strictMono` (both nests CES: the premium rises with `k`
  iff the elasticity in `F` exceeds the elasticity in `G`).
-/

namespace AKMM.Inequality

/-- The CES function is symmetric after swapping the weights. -/
theorem fs_ces_symm (α ρ X Y : ℝ) : fs_ces α ρ X Y = fs_ces (1 - α) ρ Y X := by
  unfold fs_ces
  rw [sub_sub_cancel, add_comm]

/-- AKMM, p. 639: the CES marginal product in closed form, `F₁(X, Y) = α^{1/ρ}(F/X)^{1/ρ}`. -/
theorem wi_ces_hasDerivAt {α ρ X Y : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hX : 0 < X) (hY : 0 < Y) :
    HasDerivAt (fun z => fs_ces α ρ z Y) (α ^ (1 / ρ) * (fs_ces α ρ X Y / X) ^ (1 / ρ)) X := by
  refine (fs_ces_hasDerivAt hα hα1 hρ hρ1 hX hY).congr_deriv ?_
  have hS : 0 < α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ) := by
    have := Real.rpow_pos_of_pos hα (1 / ρ)
    have := Real.rpow_pos_of_pos hX ((ρ - 1) / ρ)
    have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
    have := Real.rpow_pos_of_pos hY ((ρ - 1) / ρ)
    positivity
  set S := α ^ (1 / ρ) * X ^ ((ρ - 1) / ρ) + (1 - α) ^ (1 / ρ) * Y ^ ((ρ - 1) / ρ)
  have hF : fs_ces α ρ X Y = S ^ (ρ / (ρ - 1)) := rfl
  have hr : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  rw [hF, Real.div_rpow (Real.rpow_pos_of_pos hS _).le hX.le, ← Real.rpow_mul hS.le]
  have e1 : ρ / (ρ - 1) * (1 / ρ) = ρ / (ρ - 1) - 1 := by field_simp; ring
  have e2 : (ρ - 1) / ρ - 1 = -(1 / ρ) := by field_simp; ring
  rw [e1, e2, Real.rpow_neg hX.le]
  field_simp

/-! ### Katz–Murphy -/

/-- AKMM, p. 639: the Katz–Murphy skill premium with `G` CES,
`((1 − α)/α)^{1/ρ} (A_s/A_u)^{(ρ−1)/ρ} (s/u)^{−1/ρ}`. -/
noncomputable def km_premium (α ρ zA zS : ℝ) : ℝ :=
  ((1 - α) / α) ^ (1 / ρ) * zA ^ ((ρ - 1) / ρ) * zS ^ (-(1 / ρ))

/-- **AKMM, p. 639: the Katz–Murphy skill premium.** With `G(A_u u, A_s s)` CES (elasticity `ρ`,
weight `α` on unskilled labor), `w_s/w_u = A_s G_s/(A_u G_u) = km_premium α ρ (A_s/A_u) (s/u)`. -/
theorem km_premium_eq {α ρ Au u As s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hAu : 0 < Au) (hu : 0 < u) (hAs : 0 < As) (hs : 0 < s) :
    ∃ Gu Gs : ℝ, HasDerivAt (fun z => fs_ces α ρ z (As * s)) Gu (Au * u) ∧
      HasDerivAt (fun z => fs_ces α ρ (Au * u) z) Gs (As * s) ∧
      As * Gs / (Au * Gu) = km_premium α ρ (As / Au) (s / u) := by
  have hX : 0 < Au * u := mul_pos hAu hu
  have hY : 0 < As * s := mul_pos hAs hs
  have h1 := wi_ces_hasDerivAt hα hα1 hρ hρ1 hX hY
  have h2 := wi_ces_hasDerivAt (α := 1 - α) (by linarith) (by linarith) hρ hρ1 hY hX
  simp only [← fs_ces_symm] at h2
  refine ⟨_, _, h1, h2, ?_⟩
  set F := fs_ces α ρ (Au * u) (As * s)
  have hFpos : 0 < F := Real.rpow_pos_of_pos (by
    have := Real.rpow_pos_of_pos hα (1 / ρ)
    have := Real.rpow_pos_of_pos hX ((ρ - 1) / ρ)
    have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
    have := Real.rpow_pos_of_pos hY ((ρ - 1) / ρ)
    positivity) _
  unfold km_premium
  rw [Real.div_rpow hFpos.le hY.le, Real.div_rpow hFpos.le hX.le,
    Real.div_rpow (sub_pos.2 hα1).le hα.le, Real.mul_rpow hAs.le hs.le,
    Real.mul_rpow hAu.le hu.le, Real.div_rpow hAs.le hAu.le, Real.div_rpow hs.le hu.le,
    Real.rpow_neg hs.le, Real.rpow_neg hu.le]
  have hρ' : (ρ - 1) / ρ = 1 - 1 / ρ := by field_simp
  rw [hρ', Real.rpow_sub hAs, Real.rpow_sub hAu, Real.rpow_one, Real.rpow_one]
  have := Real.rpow_pos_of_pos hAs (1 / ρ)
  have := Real.rpow_pos_of_pos hAu (1 / ρ)
  have := Real.rpow_pos_of_pos hs (1 / ρ)
  have := Real.rpow_pos_of_pos hu (1 / ρ)
  have := Real.rpow_pos_of_pos hFpos (1 / ρ)
  have := Real.rpow_pos_of_pos hα (1 / ρ)
  have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
  field_simp

/-- **AKMM, p. 639: the Katz–Murphy equation.**
`log(w_s/w_u) = −(1/ρ) log(s/u) + ((ρ − 1)/ρ) log(A_s/A_u) + constant`, the constant being
`(1/ρ) log((1 − α)/α)`. -/
theorem km_log_premium {α ρ zA zS : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < zA) (hS : 0 < zS) :
    Real.log (km_premium α ρ zA zS) =
      -(1 / ρ) * Real.log zS + (ρ - 1) / ρ * Real.log zA + 1 / ρ * Real.log ((1 - α) / α) := by
  have hc : 0 < (1 - α) / α := div_pos (sub_pos.2 hα1) hα
  unfold km_premium
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hS _).ne',
    Real.log_mul (Real.rpow_pos_of_pos hc _).ne' (Real.rpow_pos_of_pos hA _).ne',
    Real.log_rpow hc, Real.log_rpow hA, Real.log_rpow hS]
  ring

/-- **AKMM, p. 639:** "As the relative supply of skilled workers increases … the skill premium
falls": `km_premium` is strictly decreasing in `s/u` for `ρ > 0`. -/
theorem km_premium_strictAnti_supply {α ρ zA : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hA : 0 < zA) : StrictAntiOn (km_premium α ρ zA) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hc : 0 < ((1 - α) / α) ^ (1 / ρ) * zA ^ ((ρ - 1) / ρ) :=
    mul_pos (Real.rpow_pos_of_pos (div_pos (sub_pos.2 hα1) hα) _) (Real.rpow_pos_of_pos hA _)
  unfold km_premium
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_neg hx' hxy (by
    have := one_div_pos.2 hρ; linarith)) hc

/-- **AKMM, p. 639: "skill-biased technological change makes the skill premium rise if and only
if the substitution elasticity between the two skill types is above one."** For `ρ > 0`,
`km_premium` is strictly increasing in `A_s/A_u` iff `ρ > 1`. -/
theorem km_sbtc_strictMono_iff {α ρ zS : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hS : 0 < zS) :
    StrictMonoOn (fun zA => km_premium α ρ zA zS) (Set.Ioi 0) ↔ 1 < ρ := by
  have hc : 0 < ((1 - α) / α) ^ (1 / ρ) := Real.rpow_pos_of_pos (div_pos (sub_pos.2 hα1) hα) _
  have hs : 0 < zS ^ (-(1 / ρ)) := Real.rpow_pos_of_pos hS _
  constructor
  · intro h
    by_contra hle
    have hle := not_lt.1 hle
    have h12 := h (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos)
      one_lt_two
    simp only [km_premium, Real.one_rpow, mul_one] at h12
    have hθ : (ρ - 1) / ρ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hρ.le
    have h2 : (2 : ℝ) ^ ((ρ - 1) / ρ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two hθ
    have : ((1 - α) / α) ^ (1 / ρ) * 2 ^ ((ρ - 1) / ρ) * zS ^ (-(1 / ρ)) ≤
        ((1 - α) / α) ^ (1 / ρ) * zS ^ (-(1 / ρ)) := by
      have := mul_le_mul_of_nonneg_left h2 hc.le
      nlinarith
    linarith
  · intro h1 x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hθ : 0 < (ρ - 1) / ρ := (fs_theta_pos_iff hρ).2 h1
    simp only [km_premium]
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow hx'.le hxy hθ) hc) hs

/-- **AKMM, p. 639: "with a Cobb–Douglas function, factor-augmenting technological change cannot
affect the relative input prices".** For `G = X^α Y^{1−α}`, `A_s G_Y/(A_u G_X) = ((1 − α)/α)(u/s)`
whatever `A_s, A_u`. -/
theorem km_cd_premium {α Au u As s : ℝ} (hα : 0 < α) (hAu : 0 < Au) (hu : 0 < u) (hAs : 0 < As)
    (hs : 0 < s) :
    HasDerivAt (fun z => z ^ α * (As * s) ^ (1 - α))
        (α * (Au * u) ^ (α - 1) * (As * s) ^ (1 - α)) (Au * u) ∧
      HasDerivAt (fun z => (Au * u) ^ α * z ^ (1 - α))
        ((Au * u) ^ α * ((1 - α) * (As * s) ^ (1 - α - 1))) (As * s) ∧
      As * ((Au * u) ^ α * ((1 - α) * (As * s) ^ (1 - α - 1))) /
        (Au * (α * (Au * u) ^ (α - 1) * (As * s) ^ (1 - α))) = (1 - α) / α * (u / s) := by
  have hX : 0 < Au * u := mul_pos hAu hu
  have hY : 0 < As * s := mul_pos hAs hs
  refine ⟨(Real.hasDerivAt_rpow_const (Or.inl hX.ne')).mul_const _,
    (Real.hasDerivAt_rpow_const (Or.inl hY.ne')).const_mul _, ?_⟩
  rw [Real.rpow_sub hX, Real.rpow_sub hY, Real.rpow_one, Real.rpow_one]
  have := Real.rpow_pos_of_pos hX α
  have := Real.rpow_pos_of_pos hY (1 - α)
  field_simp

/-- **AKMM, p. 639: the Katz–Murphy regression.** With `A_s/A_u = (1 + γ)ᵗ` the log premium is
`−β₁ log(s/u) + β₂ t + c` with `β₁ = 1/ρ`, `β₂ = ((ρ − 1)/ρ) log(1 + γ)`; conversely `β₁`
identifies `ρ = 1/β₁` and then `β₂` identifies `1 + γ = exp(β₂/(1 − β₁))` (for `ρ ≠ 1`). -/
theorem km_identify {α ρ γ zS : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (hγ : 0 < 1 + γ) (hS : 0 < zS) (t : ℕ) :
    Real.log (km_premium α ρ ((1 + γ) ^ t) zS) =
        -(1 / ρ) * Real.log zS + ((ρ - 1) / ρ * Real.log (1 + γ)) * t +
          1 / ρ * Real.log ((1 - α) / α) ∧
      ρ = 1 / (1 / ρ) ∧ 1 + γ = Real.exp ((ρ - 1) / ρ * Real.log (1 + γ) / (1 - 1 / ρ)) := by
  refine ⟨?_, by field_simp, ?_⟩
  · rw [km_log_premium hα hα1 (pow_pos hγ t) hS, Real.log_pow]
    ring
  · have hr : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
    have e : (ρ - 1) / ρ * Real.log (1 + γ) / (1 - 1 / ρ) = Real.log (1 + γ) := by
      field_simp
    rw [e, Real.exp_log hγ]

/-! ### Directed technical change -/

/-- AKMM, p. 640: the objective `(A_s s)^σ + (A_u u)^σ` (a monotone transform of
`[(A_s s)^σ + (A_u u)^σ]^{1/σ}` for `σ > 0`). -/
noncomputable def dt_obj (σ s u As Au : ℝ) : ℝ := (As * s) ^ σ + (Au * u) ^ σ

/-- AKMM, p. 640: the technology frontier `λA_s^φ + (1 − λ)A_u^φ`. -/
noncomputable def dt_con (lam φ As Au : ℝ) : ℝ := lam * As ^ φ + (1 - lam) * Au ^ φ

/-- AKMM, p. 640: the tangent bound behind the first-order condition. For `0 < σ < φ`,
`B ≥ 0`, `A, s > 0`: `(Bs)^σ ≤ (As)^σ + (σ/φ) s^σ A^{σ−φ} (B^φ − A^φ)`, strictly if `B ≠ A`
(Bernoulli's inequality for the exponent `σ/φ ∈ (0, 1)`). -/
theorem dt_term_le {σ φ s A B : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hs : 0 < s) (hA : 0 < A)
    (hB : 0 ≤ B) :
    (B * s) ^ σ ≤ (A * s) ^ σ + σ / φ * s ^ σ * A ^ (σ - φ) * (B ^ φ - A ^ φ) ∧
      (B ≠ A → (B * s) ^ σ < (A * s) ^ σ + σ / φ * s ^ σ * A ^ (σ - φ) * (B ^ φ - A ^ φ)) := by
  have hφ : 0 < φ := hσ.trans hσφ
  set κ := σ / φ with hκ
  have hκ0 : 0 < κ := div_pos hσ hφ
  have hκ1 : κ < 1 := (div_lt_one hφ).2 hσφ
  set z0 := A ^ φ
  set z := B ^ φ
  have hz0 : 0 < z0 := Real.rpow_pos_of_pos hA φ
  have hz : 0 ≤ z := Real.rpow_nonneg hB φ
  have hBpow : B ^ σ = z ^ κ := by
    rw [← Real.rpow_mul hB]; congr 1; rw [hκ]; field_simp
  have hApow : A ^ σ = z0 ^ κ := by
    rw [← Real.rpow_mul hA.le]; congr 1; rw [hκ]; field_simp
  have hAm : A ^ (σ - φ) = z0 ^ κ / z0 := by
    rw [Real.rpow_sub hA, hApow]
  set t := z / z0 - 1 with ht
  have ht1 : -1 ≤ t := by rw [ht]; have := div_nonneg hz hz0.le; linarith
  have hzt : z = z0 * (1 + t) := by rw [ht]; field_simp; ring
  have hzk : z ^ κ = z0 ^ κ * (1 + t) ^ κ := by
    rw [hzt, Real.mul_rpow hz0.le (by linarith)]
  have hsσ : 0 < s ^ σ := Real.rpow_pos_of_pos hs σ
  have hz0k : 0 < z0 ^ κ := Real.rpow_pos_of_pos hz0 κ
  have key : ∀ q : ℝ, q ≤ 1 + κ * t →
      s ^ σ * (z0 ^ κ * q) ≤ (A * s) ^ σ + σ / φ * s ^ σ * A ^ (σ - φ) * (B ^ φ - A ^ φ) := by
    intro q hq
    rw [Real.mul_rpow hA.le hs.le, hApow, hAm, ← hκ]
    have e : κ * s ^ σ * (z0 ^ κ / z0) * (z - z0) = s ^ σ * z0 ^ κ * (κ * t) := by
      rw [ht]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hq (mul_pos hsσ hz0k).le
    nlinarith
  have hlhs : (B * s) ^ σ = s ^ σ * (z0 ^ κ * (1 + t) ^ κ) := by
    rw [Real.mul_rpow hB hs.le, hBpow, hzk]; ring
  refine ⟨?_, fun hne => ?_⟩
  · rw [hlhs]
    exact key _ (rpow_one_add_le_one_add_mul_self ht1 hκ0.le hκ1.le)
  · have htne : t ≠ 0 := by
      intro h0
      apply hne
      have hzz : z = z0 := by rw [hzt, h0]; ring
      have := congrArg (fun x => x ^ φ⁻¹) hzz
      simp only [z, z0] at this
      rwa [Real.rpow_rpow_inv hB hφ.ne', Real.rpow_rpow_inv hA.le hφ.ne'] at this
    have hlt := rpow_one_add_lt_one_add_mul_self ht1 htne hκ0 hκ1
    have hq := key (1 + κ * t) le_rfl
    rw [hlhs]
    have : s ^ σ * (z0 ^ κ * (1 + t) ^ κ) < s ^ σ * (z0 ^ κ * (1 + κ * t)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hlt hz0k) hsσ
    linarith

/-- **AKMM, p. 640: the first-order condition solves the directed-technology problem.** If
`(A_s, A_u) > 0` is on the frontier and satisfies `A_s^{σ−φ}s^σ/λ = A_u^{σ−φ}u^σ/(1 − λ)`, then
every `(B_s, B_u) ≥ 0` on the frontier gives a weakly lower objective, strictly lower unless it
equals `(A_s, A_u)`. -/
theorem dt_optimal {σ φ lam s u As Au : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hs : 0 < s) (hu : 0 < u) (hAs : 0 < As) (hAu : 0 < Au)
    (hcon : dt_con lam φ As Au = 1)
    (hfoc : As ^ (σ - φ) * s ^ σ / lam = Au ^ (σ - φ) * u ^ σ / (1 - lam)) {Bs Bu : ℝ}
    (hBs : 0 ≤ Bs) (hBu : 0 ≤ Bu) (hconB : dt_con lam φ Bs Bu = 1) :
    dt_obj σ s u Bs Bu ≤ dt_obj σ s u As Au ∧
      ((Bs, Bu) ≠ (As, Au) → dt_obj σ s u Bs Bu < dt_obj σ s u As Au) := by
  obtain ⟨h1, h1s⟩ := dt_term_le hσ hσφ hs hAs hBs
  obtain ⟨h2, h2s⟩ := dt_term_le hσ hσφ hu hAu hBu
  set μ := As ^ (σ - φ) * s ^ σ / lam with hμ
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have e1 : s ^ σ * As ^ (σ - φ) = μ * lam := by rw [hμ]; field_simp
  have e2 : u ^ σ * Au ^ (σ - φ) = μ * (1 - lam) := by rw [hfoc]; field_simp
  have hsum : σ / φ * s ^ σ * As ^ (σ - φ) * (Bs ^ φ - As ^ φ) +
      σ / φ * u ^ σ * Au ^ (σ - φ) * (Bu ^ φ - Au ^ φ) = 0 := by
    have : σ / φ * (μ * lam) * (Bs ^ φ - As ^ φ) + σ / φ * (μ * (1 - lam)) * (Bu ^ φ - Au ^ φ)
        = σ / φ * μ * (dt_con lam φ Bs Bu - dt_con lam φ As Au) := by
      unfold dt_con; ring
    rw [hconB, hcon, sub_self, mul_zero] at this
    rw [mul_assoc (σ / φ) (s ^ σ), e1, mul_assoc (σ / φ) (u ^ σ), e2]
    exact this
  unfold dt_obj
  refine ⟨by linarith, fun hne => ?_⟩
  by_cases hb : Bs = As
  · have hb' : Bu ≠ Au := fun h => hne (by rw [hb, h])
    have := h2s hb'
    linarith
  · have := h1s hb
    linarith

/-- AKMM, p. 640: the optimal direction `ζ = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}`. -/
noncomputable def dt_ratio (σ φ lam s u : ℝ) : ℝ :=
  (lam / (1 - lam)) ^ (1 / (σ - φ)) * (s / u) ^ (σ / (φ - σ))

/-- AKMM, p. 640: for positive technologies the first-order condition is equivalent to
`A_s/A_u = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}`. -/
theorem dt_foc_iff_ratio {σ φ lam s u As Au : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hs : 0 < s) (hu : 0 < u) (hAs : 0 < As) (hAu : 0 < Au) :
    As ^ (σ - φ) * s ^ σ / lam = Au ^ (σ - φ) * u ^ σ / (1 - lam) ↔
      As / Au = dt_ratio σ φ lam s u := by
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have he : σ - φ ≠ 0 := by linarith
  have hc : 0 < lam / (1 - lam) := div_pos hl0 hl1'
  have hsu : 0 < s / u := div_pos hs hu
  have hζ : 0 < dt_ratio σ φ lam s u :=
    mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos hsu _)
  have hζe : dt_ratio σ φ lam s u ^ (σ - φ) = lam / (1 - lam) * (u ^ σ / s ^ σ) := by
    unfold dt_ratio
    rw [Real.mul_rpow (Real.rpow_pos_of_pos hc _).le (Real.rpow_pos_of_pos hsu _).le,
      ← Real.rpow_mul hc.le, ← Real.rpow_mul hsu.le]
    have e1 : 1 / (σ - φ) * (σ - φ) = 1 := by field_simp
    have e2 : σ / (φ - σ) * (σ - φ) = -σ := by
      have : φ - σ ≠ 0 := by linarith
      field_simp; ring
    rw [e1, e2, Real.rpow_one, Real.rpow_neg hsu.le, Real.div_rpow hs.le hu.le]
    have := Real.rpow_pos_of_pos hs σ
    have := Real.rpow_pos_of_pos hu σ
    field_simp
  have hAA : 0 < As / Au := div_pos hAs hAu
  have hsσ := Real.rpow_pos_of_pos hs σ
  have huσ := Real.rpow_pos_of_pos hu σ
  have hAsσ := Real.rpow_pos_of_pos hAs (σ - φ)
  have hAuσ := Real.rpow_pos_of_pos hAu (σ - φ)
  constructor
  · intro hfoc
    have hpow : (As / Au) ^ (σ - φ) = dt_ratio σ φ lam s u ^ (σ - φ) := by
      rw [hζe, Real.div_rpow hAs.le hAu.le]
      field_simp at hfoc ⊢
      linarith
    have := congrArg (fun x => x ^ (σ - φ)⁻¹) hpow
    rwa [Real.rpow_rpow_inv hAA.le he, Real.rpow_rpow_inv hζ.le he] at this
  · intro hr
    have hpow : (As / Au) ^ (σ - φ) = lam / (1 - lam) * (u ^ σ / s ^ σ) := by rw [hr, hζe]
    rw [Real.div_rpow hAs.le hAu.le] at hpow
    field_simp at hpow ⊢
    linarith

/-- AKMM, p. 640: a point on the frontier with the optimal direction exists:
`A_u = (λζ^φ + 1 − λ)^{−1/φ}`, `A_s = ζA_u`. -/
theorem dt_exists {σ φ lam s u : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hs : 0 < s) (hu : 0 < u) :
    ∃ As Au : ℝ, 0 < As ∧ 0 < Au ∧ dt_con lam φ As Au = 1 ∧
      As / Au = dt_ratio σ φ lam s u := by
  have hφ : 0 < φ := hσ.trans hσφ
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have hζ : 0 < dt_ratio σ φ lam s u :=
    mul_pos (Real.rpow_pos_of_pos (div_pos hl0 hl1') _) (Real.rpow_pos_of_pos (div_pos hs hu) _)
  set ζ := dt_ratio σ φ lam s u
  set D := lam * ζ ^ φ + (1 - lam)
  have hD : 0 < D := by have := Real.rpow_pos_of_pos hζ φ; positivity
  set Au := D ^ (-(1 / φ))
  have hAu : 0 < Au := Real.rpow_pos_of_pos hD _
  have hAuφ : Au ^ φ = D⁻¹ := by
    rw [← Real.rpow_mul hD.le, show -(1 / φ) * φ = -1 by field_simp, Real.rpow_neg_one]
  refine ⟨ζ * Au, Au, mul_pos hζ hAu, hAu, ?_, by field_simp⟩
  unfold dt_con
  rw [Real.mul_rpow hζ.le hAu.le, hAuφ]
  field_simp
  rfl

/-- **AKMM, p. 640: "The first-order condition becomes `A_s/A_u = …`".** Every maximiser of the
objective on the frontier (over `A_s, A_u ≥ 0`) has
`A_s/A_u = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}` (book: `σ ∈ (0, 1)`, `φ > 1`; `0 < σ < φ`
suffices). -/
theorem dt_maximiser_ratio {σ φ lam s u Bs Bu : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hs : 0 < s) (hu : 0 < u) (hBs : 0 ≤ Bs) (hBu : 0 ≤ Bu)
    (hcon : dt_con lam φ Bs Bu = 1)
    (hmax : ∀ Cs Cu : ℝ, 0 ≤ Cs → 0 ≤ Cu → dt_con lam φ Cs Cu = 1 →
      dt_obj σ s u Cs Cu ≤ dt_obj σ s u Bs Bu) :
    0 < Bu ∧ Bs / Bu = dt_ratio σ φ lam s u := by
  obtain ⟨As, Au, hAs, hAu, hc, hr⟩ := dt_exists hσ hσφ hl0 hl1 hs hu
  have hfoc := (dt_foc_iff_ratio hσφ hl0 hl1 hs hu hAs hAu).2 hr
  obtain ⟨-, hstrict⟩ := dt_optimal hσ hσφ hl0 hl1 hs hu hAs hAu hc hfoc hBs hBu hcon
  have heq : (Bs, Bu) = (As, Au) := by
    by_contra hne
    have h1 := hstrict hne
    have h2 := hmax As Au hAs.le hAu.le hc
    linarith
  simp only [Prod.mk.injEq] at heq
  rw [heq.1, heq.2]
  exact ⟨hAu, hr⟩

/-- **AKMM, p. 640, the printed first-order condition** `A_s/A_u = (λ/(1 − λ))(s/u)^{σ/(φ−σ)}`
agrees with the optimum only for `λ = 1/2`: for `σ < φ`,
`(λ/(1 − λ))^{1/(σ−φ)} = λ/(1 − λ)` iff `λ = 1/2`. -/
theorem dt_printed_ratio_iff {σ φ lam : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1) :
    (lam / (1 - lam)) ^ (1 / (σ - φ)) = lam / (1 - lam) ↔ lam = 1 / 2 := by
  have hl1' : 0 < 1 - lam := sub_pos.2 hl1
  have hx : 0 < lam / (1 - lam) := div_pos hl0 hl1'
  have he : 1 / (σ - φ) < 0 := one_div_neg.2 (by linarith)
  constructor
  · intro h
    have hlog := congrArg Real.log h
    rw [Real.log_rpow hx] at hlog
    have hl : Real.log (lam / (1 - lam)) = 0 := by
      have : (1 / (σ - φ) - 1) * Real.log (lam / (1 - lam)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exact h0
    have h1 := Real.eq_one_of_pos_of_log_eq_zero hx hl
    field_simp at h1
    linarith
  · intro h
    have h1 : lam / (1 - lam) = 1 := by rw [h]; norm_num
    rw [h1, Real.one_rpow]

/-- **AKMM, p. 640:** "a higher relative skill supply attracts more R&D": for `0 < σ < φ` the
optimal `A_s/A_u` is strictly increasing in `s/u` (here in `s` for fixed `u`). -/
theorem dt_ratio_strictMono {σ φ lam u : ℝ} (hσ : 0 < σ) (hσφ : σ < φ) (hl0 : 0 < lam)
    (hl1 : lam < 1) (hu : 0 < u) : StrictMonoOn (fun s => dt_ratio σ φ lam s u) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hc : 0 < (lam / (1 - lam)) ^ (1 / (σ - φ)) :=
    Real.rpow_pos_of_pos (div_pos hl0 (sub_pos.2 hl1)) _
  simp only [dt_ratio]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (div_pos hx' hu).le
    (div_lt_div_of_pos_right hxy hu) (div_pos hσ (by linarith))) hc

/-- **AKMM, p. 640: the relative wage.** With output `Y = [(A_s s)^σ + (A_u u)^σ]^{1/σ}`, the
marginal products give `w_s/w_u = (A_s/A_u)^σ (s/u)^{σ−1}`. -/
theorem dt_wage_ratio {σ s u As Au : ℝ} (hσ : σ ≠ 0) (hs : 0 < s) (hu : 0 < u) (hAs : 0 < As)
    (hAu : 0 < Au) :
    ∃ ws wu : ℝ, HasDerivAt (fun z => dt_obj σ z u As Au ^ (1 / σ)) ws s ∧
      HasDerivAt (fun z => dt_obj σ s z As Au ^ (1 / σ)) wu u ∧
      ws / wu = (As / Au) ^ σ * (s / u) ^ (σ - 1) := by
  have hO : 0 < dt_obj σ s u As Au := by
    unfold dt_obj
    have := Real.rpow_pos_of_pos (mul_pos hAs hs) σ
    have := Real.rpow_pos_of_pos (mul_pos hAu hu) σ
    positivity
  have h1 : HasDerivAt (fun z => dt_obj σ z u As Au)
      (As * (σ * (As * s) ^ (σ - 1))) s := by
    unfold dt_obj
    exact (((hasDerivAt_id s).const_mul As).rpow_const (p := σ)
      (Or.inl (mul_pos hAs hs).ne')).add_const _ |>.congr_deriv (by simp only [id]; ring)
  have h2 : HasDerivAt (fun z => dt_obj σ s z As Au)
      (Au * (σ * (Au * u) ^ (σ - 1))) u := by
    unfold dt_obj
    exact (((hasDerivAt_id u).const_mul Au).rpow_const (p := σ)
      (Or.inl (mul_pos hAu hu).ne')).const_add _ |>.congr_deriv (by simp only [id]; ring)
  refine ⟨_, _, h1.rpow_const (Or.inl hO.ne'), h2.rpow_const (Or.inl hO.ne'), ?_⟩
  have hP := Real.rpow_pos_of_pos hO (1 / σ - 1)
  rw [Real.mul_rpow hAs.le hs.le, Real.mul_rpow hAu.le hu.le, Real.div_rpow hAs.le hAu.le,
    Real.div_rpow hs.le hu.le, Real.rpow_sub hAs, Real.rpow_sub hAu, Real.rpow_sub hs,
    Real.rpow_sub hu, Real.rpow_one, Real.rpow_one, Real.rpow_one, Real.rpow_one]
  have := Real.rpow_pos_of_pos hAs σ
  have := Real.rpow_pos_of_pos hAu σ
  have := Real.rpow_pos_of_pos hs σ
  have := Real.rpow_pos_of_pos hu σ
  field_simp

/-- **AKMM, p. 640: the premium at the directed-technology optimum.** Substituting
`A_s/A_u = ζ` into `(A_s/A_u)^σ (s/u)^{σ−1}` gives
`(λ/(1 − λ))^{σ/(σ−φ)} (s/u)^{(σ − φ(1 − σ))/(φ − σ)}`. -/
theorem dt_premium_closed {σ φ lam s u : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hs : 0 < s) (hu : 0 < u) :
    dt_ratio σ φ lam s u ^ σ * (s / u) ^ (σ - 1) =
      (lam / (1 - lam)) ^ (σ / (σ - φ)) * (s / u) ^ ((σ - φ * (1 - σ)) / (φ - σ)) := by
  have hc : 0 < lam / (1 - lam) := div_pos hl0 (sub_pos.2 hl1)
  have hsu : 0 < s / u := div_pos hs hu
  have h1 : σ - φ ≠ 0 := by linarith
  have h2 : φ - σ ≠ 0 := by linarith
  unfold dt_ratio
  rw [Real.mul_rpow (Real.rpow_pos_of_pos hc _).le (Real.rpow_pos_of_pos hsu _).le,
    ← Real.rpow_mul hc.le, ← Real.rpow_mul hsu.le, mul_assoc, ← Real.rpow_add hsu]
  congr 2
  · field_simp
  · field_simp; ring

/-- **AKMM, p. 640:** `log(w_s/w_u) = (σ/(σ − φ)) log(λ/(1 − λ))
+ ((σ − φ(1 − σ))/(φ − σ)) log(s/u)`, i.e. `log(w_s/w_u) ∝ ((σ − φ(1 − σ))/(φ − σ)) log(s/u)`. -/
theorem dt_log_premium {σ φ lam s u : ℝ} (hσφ : σ < φ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hs : 0 < s) (hu : 0 < u) :
    Real.log (dt_ratio σ φ lam s u ^ σ * (s / u) ^ (σ - 1)) =
      σ / (σ - φ) * Real.log (lam / (1 - lam)) +
        (σ - φ * (1 - σ)) / (φ - σ) * Real.log (s / u) := by
  have hc : 0 < lam / (1 - lam) := div_pos hl0 (sub_pos.2 hl1)
  have hsu : 0 < s / u := div_pos hs hu
  rw [dt_premium_closed hσφ hl0 hl1 hs hu, Real.log_mul (Real.rpow_pos_of_pos hc _).ne'
    (Real.rpow_pos_of_pos hsu _).ne', Real.log_rpow hc, Real.log_rpow hsu]

/-- **AKMM, p. 640: "the skill premium is increasing in `s/u` as long as
`ρ − 1 = σ/(1 − σ) > φ`".** For `0 < σ < 1` and `σ < φ` the exponent
`(σ − φ(1 − σ))/(φ − σ)` is positive iff `σ/(1 − σ) > φ`, and `ρ = 1/(1 − σ)` has
`ρ − 1 = σ/(1 − σ)`. -/
theorem dt_exponent_pos_iff {σ φ : ℝ} (hσ1 : σ < 1) (hσφ : σ < φ) :
    (0 < (σ - φ * (1 - σ)) / (φ - σ) ↔ φ < σ / (1 - σ)) ∧ 1 / (1 - σ) - 1 = σ / (1 - σ) := by
  have h1 : 0 < 1 - σ := sub_pos.2 hσ1
  refine ⟨?_, by field_simp; ring⟩
  rw [div_pos_iff_of_pos_right (sub_pos.2 hσφ), lt_div_iff₀ h1, sub_pos]

/-- **AKMM, p. 640:** "with a large enough elasticity of substitution … (at least above 2)":
`ρ − 1 > φ > 1` gives `ρ = 1/(1 − σ) > 2`. -/
theorem dt_rho_gt_two {σ φ : ℝ} (hσ1 : σ < 1) (hφ : 1 < φ) (h : φ < σ / (1 - σ)) :
    2 < 1 / (1 - σ) := by
  have h1 : 0 < 1 - σ := sub_pos.2 hσ1
  have e : 1 / (1 - σ) = σ / (1 - σ) + 1 := by field_simp; ring
  linarith

/-! ### Capital–skill complementarity -/

/-- **AKMM, p. 641: `F(k, u, s) = u + s^ν k^{1−ν}`.** The unskilled wage is `1` and the skilled
wage `ν s^{ν−1} k^{1−ν}`. -/
theorem cs_ex1_wages {ν k u s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun z => z + s ^ ν * k ^ (1 - ν)) 1 u ∧
      HasDerivAt (fun z => u + z ^ ν * k ^ (1 - ν)) (ν * s ^ (ν - 1) * k ^ (1 - ν)) s :=
  ⟨(hasDerivAt_id u).add_const _,
    ((Real.hasDerivAt_rpow_const (Or.inl hs.ne')).mul_const _).const_add _⟩

/-- **AKMM, p. 641:** "higher capital raises the marginal product of skilled labor, whereas the
unskilled marginal product is unaffected": for `0 < ν < 1`, `s > 0` the premium
`ν s^{ν−1}k^{1−ν}/1` is strictly increasing in `k ≥ 0`. -/
theorem cs_ex1_premium_strictMono {ν s : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hs : 0 < s) :
    StrictMonoOn (fun k => ν * s ^ (ν - 1) * k ^ (1 - ν) / 1) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  simp only [div_one]
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx' hxy (by linarith))
    (mul_pos hν (Real.rpow_pos_of_pos hs _))

/-- **AKMM, p. 641: `F = s^ν (k + u)^{1−ν}`.** The unskilled wage
`w_u = (1 − ν) s^ν (k + u)^{−ν}` … -/
theorem cs_ex2_wu {ν k u s : ℝ} (hku : 0 < k + u) :
    HasDerivAt (fun z => s ^ ν * (k + z) ^ (1 - ν)) (s ^ ν * ((1 - ν) * (k + u) ^ (-ν))) u := by
  have h := ((hasDerivAt_id u).const_add k).rpow_const (p := 1 - ν) (Or.inl hku.ne')
  refine (h.const_mul (s ^ ν)).congr_deriv ?_
  simp only [id, sub_sub_cancel_left, one_mul]

/-- **AKMM, p. 641:** "a rise in the capital stock now allows the real wage of unskilled
workers, `w_u`, to fall": for `0 < ν < 1`, `s > 0`, `u > 0`,
`w_u = (1 − ν) s^ν (k + u)^{−ν}` is strictly decreasing in `k ≥ 0`. -/
theorem cs_ex2_wu_strictAnti {ν u s : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hs : 0 < s) (hu : 0 < u) :
    StrictAntiOn (fun k => s ^ ν * ((1 - ν) * (k + u) ^ (-ν))) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  have h := Real.rpow_lt_rpow_of_neg (by linarith : 0 < x + u) (by linarith : x + u < y + u)
    (by linarith : -ν < 0)
  have hc : 0 < s ^ ν * (1 - ν) := mul_pos (Real.rpow_pos_of_pos hs _) (by linarith)
  have := mul_lt_mul_of_pos_left h hc
  simp only
  linarith [this, show s ^ ν * ((1 - ν) * (y + u) ^ (-ν)) = s ^ ν * (1 - ν) * (y + u) ^ (-ν)
    by ring, show s ^ ν * ((1 - ν) * (x + u) ^ (-ν)) = s ^ ν * (1 - ν) * (x + u) ^ (-ν) by ring]

/-- AKMM, p. 641: under the nesting `F(u, G(k, s))` with `F` of constant returns,
`F(u, G) = u f(G/u)`, the unskilled wage is `w_u = f(x) − x f′(x)`, `x = G/u`. -/
theorem cs_nest_wu {f : ℝ → ℝ} {f' u G : ℝ} (hu : 0 < u)
    (hf : HasDerivAt f f' (G / u)) :
    HasDerivAt (fun z => z * f (G / z)) (f (G / u) - G / u * f') u := by
  have hq : HasDerivAt (fun z => G / z) (-(G / u ^ 2)) u :=
    ((hasDerivAt_const u G).div (hasDerivAt_id u) hu.ne').congr_deriv (by simp [neg_div])
  have h := (hasDerivAt_id u).mul (hf.comp u hq)
  refine h.congr_deriv ?_
  simp only [id, Function.comp]
  field_simp
  ring

/-- **AKMM, p. 641: "This feature … cannot be obtained under the previous nesting."** If `f`
is concave (tangent inequalities with derivative `f′`), then `w_u = f(x) − x f′(x)` is
nondecreasing in `x = G/u ≥ 0`; since `G` is increasing in `k`, `w_u` cannot fall as `k`
rises under `F(u, G(k, s))`. -/
theorem cs_nest_wu_monotone {f f' : ℝ → ℝ}
    (htan : ∀ x y, 0 ≤ x → 0 ≤ y → f x ≤ f y + f' y * (x - y)) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : f x - x * f' x ≤ f y - y * f' y := by
  have hy : 0 ≤ y := hx.trans hxy
  have h1 := htan x y hx hy
  have h2 := htan y x hy hx
  -- concavity: f' y ≤ f' x
  have hmono : (f' y - f' x) * (y - x) ≤ 0 := by nlinarith
  have hd : f' y ≤ f' x := by
    rcases hxy.eq_or_lt with h | h
    · rw [h]
    · nlinarith
  nlinarith

/-- **AKMM, p. 641: both nests CES.** With `F(u, G) = fs_ces α ρ u G` and
`G(k, s) = fs_ces β η k s`, the premium `w_s/w_u = F_G G_s/F_u` equals
`((1 − α)/α)^{1/ρ} (1 − β)^{1/η} u^{1/ρ} s^{−1/η} G^{1/η − 1/ρ}`. -/
theorem cs_ces_nest_premium {α ρ β η u k s : ℝ} (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (hβ : 0 < β) (hβ1 : β < 1) (hη : 0 < η) (hη1 : η ≠ 1) (hu : 0 < u)
    (hk : 0 < k) (hs : 0 < s) :
    ∃ Fu FG Gs : ℝ,
      HasDerivAt (fun z => fs_ces α ρ z (fs_ces β η k s)) Fu u ∧
      HasDerivAt (fun z => fs_ces α ρ u z) FG (fs_ces β η k s) ∧
      HasDerivAt (fun z => fs_ces β η k z) Gs s ∧
      FG * Gs / Fu = ((1 - α) / α) ^ (1 / ρ) * (1 - β) ^ (1 / η) * u ^ (1 / ρ) *
        s ^ (-(1 / η)) * fs_ces β η k s ^ (1 / η - 1 / ρ) := by
  have hG : 0 < fs_ces β η k s := Real.rpow_pos_of_pos (by
    have := Real.rpow_pos_of_pos hβ (1 / η)
    have := Real.rpow_pos_of_pos hk ((η - 1) / η)
    have := Real.rpow_pos_of_pos (sub_pos.2 hβ1) (1 / η)
    have := Real.rpow_pos_of_pos hs ((η - 1) / η)
    positivity) _
  set G := fs_ces β η k s
  have h1 := wi_ces_hasDerivAt hα hα1 hρ hρ1 hu hG
  have h2 := wi_ces_hasDerivAt (α := 1 - α) (by linarith) (by linarith) hρ hρ1 hG hu
  simp only [← fs_ces_symm] at h2
  have h3 := wi_ces_hasDerivAt (α := 1 - β) (by linarith) (by linarith) hη hη1 hs hk
  simp only [← fs_ces_symm] at h3
  refine ⟨_, _, _, h1, h2, h3, ?_⟩
  set F := fs_ces α ρ u G
  have hF : 0 < F := Real.rpow_pos_of_pos (by
    have := Real.rpow_pos_of_pos hα (1 / ρ)
    have := Real.rpow_pos_of_pos hu ((ρ - 1) / ρ)
    have := Real.rpow_pos_of_pos (sub_pos.2 hα1) (1 / ρ)
    have := Real.rpow_pos_of_pos hG ((ρ - 1) / ρ)
    positivity) _
  rw [Real.div_rpow hF.le hG.le, Real.div_rpow hF.le hu.le, Real.div_rpow hG.le hs.le,
    Real.div_rpow (sub_pos.2 hα1).le hα.le, Real.rpow_neg hs.le, Real.rpow_sub hG]
  have := Real.rpow_pos_of_pos hF (1 / ρ)
  have := Real.rpow_pos_of_pos hG (1 / ρ)
  have := Real.rpow_pos_of_pos hG (1 / η)
  have := Real.rpow_pos_of_pos hu (1 / ρ)
  have := Real.rpow_pos_of_pos hs (1 / η)
  have := Real.rpow_pos_of_pos hα (1 / ρ)
  field_simp

/-- **AKMM, p. 641: "if the elasticity in `F` is greater than that in `G`, then the skill
premium rises as `k` goes up".** `G = fs_ces β η k s` is strictly increasing in `k > 0`, and the
premium `C·G^{1/η − 1/ρ}` (`C > 0`) is strictly increasing in `G > 0` iff `ρ > η`. -/
theorem cs_ces_nest_strictMono {β η ρ s C : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hη : 0 < η)
    (hη1 : η ≠ 1) (hρ : 0 < ρ) (hs : 0 < s) (hC : 0 < C) :
    StrictMonoOn (fun k => fs_ces β η k s) (Set.Ioi 0) ∧
      (StrictMonoOn (fun G => C * G ^ (1 / η - 1 / ρ)) (Set.Ioi 0) ↔ η < ρ) := by
  constructor
  · have hd : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun k => fs_ces β η k s)
        (β ^ (1 / η) * (fs_ces β η x s / x) ^ (1 / η)) x :=
      fun x hx => wi_ces_hasDerivAt hβ hβ1 hη hη1 hx hs
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hx' : (0 : ℝ) < x := hx
      rw [(hd x hx).deriv]
      have hG : 0 < fs_ces β η x s := Real.rpow_pos_of_pos (by
        have := Real.rpow_pos_of_pos hβ (1 / η)
        have := Real.rpow_pos_of_pos hx' ((η - 1) / η)
        have := Real.rpow_pos_of_pos (sub_pos.2 hβ1) (1 / η)
        have := Real.rpow_pos_of_pos hs ((η - 1) / η)
        positivity) _
      exact mul_pos (Real.rpow_pos_of_pos hβ _) (Real.rpow_pos_of_pos (div_pos hG hx') _)
  · constructor
    · intro h
      by_contra hle
      have hle := not_lt.1 hle
      have he : 1 / η - 1 / ρ ≤ 0 := by
        have := one_div_le_one_div_of_le hρ hle
        linarith
      have h12 := h (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos)
        one_lt_two
      simp only [Real.one_rpow, mul_one] at h12
      have h2 : (2 : ℝ) ^ (1 / η - 1 / ρ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos one_le_two he
      nlinarith
    · intro hlt x hx y hy hxy
      have hx' : (0 : ℝ) < x := hx
      have he : 0 < 1 / η - 1 / ρ := by
        have := one_div_lt_one_div_of_lt hη hlt
        linarith
      exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hx'.le hxy he) hC

end AKMM.Inequality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §21.2.3: deterministic dynastic models

AKMM, §21.2.3, pp. 644–649. Consumer `i` maximises `Σ βᵗu(cᵢ,ₜ)` subject to
`cᵢ,ₜ + aᵢ,ₜ₊₁ = (1 + r − δ)aᵢ,ₜ + εᵢw` and the no-Ponzi condition (fn 21). With
`R = 1 + r − δ` and `Aₜ = Raₜ` this is the deterministic problem (11.12) of AKMM Chapter 11
(`AKMM.Consumption.cd_Optimal`), with income `y = εᵢw`; `dy_Optimal` records the translation and
`dy_plan_iff` checks it. Optimality is from Chapter 11: the Euler equation (11.13) is necessary
(`eq_11_13`) and, with concave `u`, sufficient (`cd_optimal_of_euler`).

* **Steady-state indeterminacy** (p. 645): `dy_constant_optimal`: if `β(1 + r − δ) = 1`, holding
  any initial wealth forever is optimal; `dy_indeterminacy`: every wealth distribution summing to
  `k` with positive consumption is a steady state; `dy_indeterminacy_example`: two different ones;
  `dy_mpc`: the marginal propensity to consume out of wealth is `r − δ`.
* **OLG with altruism** (pp. 646–647): `ol_budget_iff`, `ol_IsIndirect`,
  `ol_isIndirect_prod` (instance), `ol_bellman_reduction`: the altruistic Bellman problem in
  `(c_y, c_o, a′)` has the same maximal values as the dynastic problem in `(R_y, a′)`;
  `ol_dynastic_utility` (Obstfeld–Rogoff's `utility_eq_tsum_iff`); `ol_indeterminacy`,
  `ol_example`: the steady-state wealth distribution is again indeterminate.
* **Discount-factor heterogeneity** (p. 647): `hd_constant_beta`, `hd_unique_beta`: constant
  positive consumption forces `βR = 1`, so agents with different `β` cannot both be at a steady
  state; `hd_strictAnti`, `hd_tendsto_zero`, `hd_assets_limit`: when `βᵢR < 1` consumption falls
  strictly to zero and wealth converges to `−εᵢw/(r − δ)`; `hd_strictMono`: `βR > 1` makes
  consumption rise forever, so `R = 1/max βᵢ`.
* **Return heterogeneity** (p. 649): `rh_lower_return_iff`: with common `β` and
  `βR_max = 1`, every agent with a lower return has `βRᵢ < 1`, and the results above apply.
-/

namespace AKMM.Inequality

open Filter Topology AKMM.Consumption

/-- AKMM, p. 645: consumer `i`'s problem `max Σ βᵗu(cₜ)` s.t. `cₜ + aₜ₊₁ = Raₜ + y`, `a₀` given,
no Ponzi games, `c > 0`, in Chapter 11's form with `Aₜ = Raₜ` (`R = 1 + r − δ`, `y = εᵢw`). -/
def dy_Optimal (β R a₀ y : ℝ) (u : ℝ → ℝ) (c a : ℕ → ℝ) : Prop :=
  cd_Optimal β R (R * a₀) u (fun _ => y) c (fun t => R * a t)

/-- AKMM, p. 645: the translation is exact: Chapter 11's plan with `Aₜ = Raₜ` is the Chapter 21
budget `cₜ + aₜ₊₁ = Raₜ + y` with `a₀` given, `c > 0` and `aₜ/Rᵗ → 0`. -/
theorem dy_plan_iff {R a₀ y : ℝ} (hR : 0 < R) {c a : ℕ → ℝ} :
    cd_Plan R (R * a₀) (fun _ => y) c (fun t => R * a t) ↔
      a 0 = a₀ ∧ (∀ t, c t + a (t + 1) = R * a t + y) ∧ (∀ t, 0 < c t) ∧
        Tendsto (fun t => a t / R ^ t) atTop (𝓝 0) := by
  have hfun : (fun t => R * a t / R ^ t) = fun t => R * (a t / R ^ t) := by
    funext t; ring
  constructor
  · rintro ⟨h0, hb, hc, ht⟩
    refine ⟨mul_left_cancel₀ hR.ne' h0, fun t => ?_, hc, ?_⟩
    · have := hb t
      have h2 : a (t + 1) = y + R * a t - c t := mul_left_cancel₀ hR.ne' this
      linarith
    · rw [hfun] at ht
      have := ht.const_mul R⁻¹
      simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul] at this
      exact this
  · rintro ⟨h0, hb, hc, ht⟩
    refine ⟨by simp only [h0], fun t => ?_, hc, ?_⟩
    · have := hb t
      simp only
      rw [show a (t + 1) = R * a t + y - c t by linarith]
      ring
    · rw [hfun]
      simpa using ht.const_mul R

/-- **AKMM, p. 645: holding wealth constant is optimal when `β(1 + r − δ) = 1`.** For
`0 < β < 1`, `βR = 1` and concave `u` (tangent inequalities with derivative `du`), the plan
`aₜ = a₀`, `cₜ = (R − 1)a₀ + y > 0` solves the consumer's problem. -/
theorem dy_constant_optimal {β R a₀ y : ℝ} {u du : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hβR : β * R = 1) (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z))
    (hc : 0 < (R - 1) * a₀ + y) :
    dy_Optimal β R a₀ y u (fun _ => (R - 1) * a₀ + y) (fun _ => a₀) := by
  have hRb : R = β⁻¹ := eq_inv_of_mul_eq_one_right hβR
  have hR : 0 < R := by rw [hRb]; exact inv_pos.2 hβ
  have hRi : R⁻¹ = β := by rw [hRb, inv_inv]
  apply cd_optimal_of_euler hβ hR htan
  · refine ⟨rfl, fun t => by ring, fun _ => hc, ?_⟩
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).const_mul (R * a₀)
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    rw [div_eq_mul_inv, ← inv_pow, hRi]
  · intro t; rw [hβR, one_mul]
  · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  · rw [hRi]; exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _

/-- **AKMM, p. 645: steady-state indeterminacy of the wealth distribution.** Let
`β(1 + r − δ) = 1`, `Σᵢ εᵢ = 1`. For every wealth distribution `(aᵢ)` with `Σᵢ aᵢ = k` and
`cᵢ = (r − δ)aᵢ + εᵢw > 0`, holding `aᵢ` forever is optimal for every consumer, and aggregate
consumption is `(r − δ)k + w`. -/
theorem dy_indeterminacy {ι : Type*} [Fintype ι] {β r δ w k : ℝ} {u du : ℝ → ℝ}
    (ε a : ι → ℝ) (hβ : 0 < β) (hβ1 : β < 1) (hss : β * (1 + r - δ) = 1)
    (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z)) (hk : ∑ i, a i = k)
    (hε : ∑ i, ε i = 1) (hc : ∀ i, 0 < (r - δ) * a i + ε i * w) :
    (∀ i, dy_Optimal β (1 + r - δ) (a i) (ε i * w) u (fun _ => (r - δ) * a i + ε i * w)
      (fun _ => a i)) ∧ ∑ i, ((r - δ) * a i + ε i * w) = (r - δ) * k + w := by
  refine ⟨fun i => ?_, ?_⟩
  · have h := dy_constant_optimal (a₀ := a i) (y := ε i * w) hβ hβ1 hss htan
      (by rw [show 1 + r - δ - 1 = r - δ by ring]; exact hc i)
    rwa [show 1 + r - δ - 1 = r - δ by ring] at h
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hk, hε, one_mul]

/-- AKMM, p. 645: the tangent inequality of `log`. -/
theorem dy_log_tangent (x z : ℝ) (hx : 0 < x) (hz : 0 < z) :
    Real.log x ≤ Real.log z + z⁻¹ * (x - z) := by
  have := Real.log_le_sub_one_of_pos (div_pos hx hz)
  rw [Real.log_div hx.ne' hz.ne'] at this
  have e : z⁻¹ * (x - z) = x / z - 1 := by field_simp
  linarith

/-- **AKMM, p. 645: "any combination is possible".** With log utility, `β = 1/2`, `r − δ = 1`,
`w = 1`, two consumers with `ε = 1/2` each and `k = 1`, both `(1/2, 1/2)` and `(0, 1)` are
steady-state wealth distributions. -/
theorem dy_indeterminacy_example :
    ∃ a b : Fin 2 → ℝ, a ≠ b ∧ ∑ i, a i = 1 ∧ ∑ i, b i = 1 ∧
      (∀ i, dy_Optimal (1 / 2) 2 (a i) (1 / 2) Real.log (fun _ => a i + 1 / 2) (fun _ => a i)) ∧
      ∀ i, dy_Optimal (1 / 2) 2 (b i) (1 / 2) Real.log (fun _ => b i + 1 / 2) (fun _ => b i) := by
  refine ⟨fun _ => 1 / 2, ![0, 1], fun h => ?_, by simp, by simp, fun i => ?_,
    fun i => ?_⟩
  · have := congrFun h 0
    norm_num at this
  · have h := dy_constant_optimal (β := 1 / 2) (R := 2) (a₀ := 1 / 2)
      (y := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) dy_log_tangent (by norm_num)
    convert h using 2
    ring
  · have hb : 0 ≤ ![(0 : ℝ), 1] i := by fin_cases i <;> simp
    have h := dy_constant_optimal (β := 1 / 2) (R := 2) (a₀ := ![(0 : ℝ), 1] i)
      (y := 1 / 2) (by norm_num)
      (by norm_num) (by norm_num) dy_log_tangent (by linarith)
    convert h using 2
    ring

/-- **AKMM, p. 645: "a marginal propensity `r − δ`".** Steady-state consumption
`c = (r − δ)a + εw` has derivative `r − δ` in wealth. -/
theorem dy_mpc (r δ ε w a : ℝ) : HasDerivAt (fun x => (r - δ) * x + ε * w) (r - δ) a := by
  simpa using ((hasDerivAt_id a).const_mul (r - δ)).add_const (ε * w)

/-! ### Overlapping generations with altruism -/

/-- **AKMM, p. 646: the generation's budget.** `c_y + c_o/R + a′ = aR + w(ε_y + ε_o/R)` is
`R_y + a′ = aR + wε̂` with `R_y = c_y + c_o/R` and `ε̂ = ε_y + ε_o/R`. -/
theorem ol_budget_iff (cy co a' a R w εy εo : ℝ) :
    cy + co / R + a' = a * R + w * (εy + εo / R) ↔
      (cy + co / R) + a' = a * R + w * (εy + εo / R) := Iff.rfl

/-- AKMM, p. 646: `u(R) = max U(c_y, c_o)` s.t. `c_y + c_o/R̃ = R` (`R̃ = 1 + r − δ`): for every
`R` the maximum exists and equals `u(R)`. -/
def ol_IsIndirect (U : ℝ → ℝ → ℝ) (Rt : ℝ) (uR : ℝ → ℝ) : Prop :=
  ∀ R, IsGreatest {x | ∃ cy co, cy + co / Rt = R ∧ x = U cy co} (uR R)

/-- An instance: for `U(c_y, c_o) = c_y c_o` and `R̃ > 0`, `u(R) = R̃R²/4`. -/
theorem ol_isIndirect_prod {Rt : ℝ} (hRt : 0 < Rt) :
    ol_IsIndirect (fun cy co => cy * co) Rt (fun R => Rt * R ^ 2 / 4) := by
  intro R
  refine ⟨⟨R / 2, Rt * R / 2, by field_simp; ring, by ring⟩, ?_⟩
  rintro x ⟨cy, co, hb, rfl⟩
  have hco : co = Rt * (R - cy) := by field_simp at hb; linarith
  rw [hco]
  nlinarith [sq_nonneg (R - 2 * cy), hRt]

/-- **AKMM, p. 646: the altruistic problem is a dynastic problem.** For any continuation value
`V`, the two Bellman right-hand sides
`max_{c_y, c_o, a′} U(c_y, c_o) + βV(a′)` s.t. `c_y + c_o/R̃ + a′ = aR̃ + w(ε_y + ε_o/R̃)` and
`max_{R_y, a′} u(R_y) + βV(a′)` s.t. `R_y + a′ = aR̃ + wε̂` have the same maximum. -/
theorem ol_bellman_reduction {U : ℝ → ℝ → ℝ} {Rt : ℝ} {uR : ℝ → ℝ} (hU : ol_IsIndirect U Rt uR)
    (V : ℝ → ℝ) (β a w εy εo v : ℝ) :
    IsGreatest {x | ∃ cy co a', cy + co / Rt + a' = a * Rt + w * (εy + εo / Rt) ∧
        x = U cy co + β * V a'} v ↔
      IsGreatest {x | ∃ R a', R + a' = a * Rt + w * (εy + εo / Rt) ∧ x = uR R + β * V a'} v := by
  constructor
  · rintro ⟨⟨cy, co, a', hb, rfl⟩, hub⟩
    obtain ⟨⟨cy', co', hb', he'⟩, hle⟩ := hU (cy + co / Rt)
    have h1 : U cy co ≤ uR (cy + co / Rt) := hle ⟨cy, co, rfl, rfl⟩
    have h2 : U cy' co' + β * V a' ≤ U cy co + β * V a' :=
      hub ⟨cy', co', a', by rw [hb', hb], rfl⟩
    refine ⟨⟨cy + co / Rt, a', hb, by linarith⟩, ?_⟩
    rintro x ⟨R, b, hR, rfl⟩
    obtain ⟨⟨cy'', co'', hb'', he''⟩, -⟩ := hU R
    rw [he'']
    exact hub ⟨cy'', co'', b, by rw [hb'', hR], rfl⟩
  · rintro ⟨⟨R, a', hb, rfl⟩, hub⟩
    obtain ⟨⟨cy, co, hb', he⟩, -⟩ := hU R
    refine ⟨⟨cy, co, a', by rw [hb', hb], by rw [he]⟩, ?_⟩
    rintro x ⟨cy', co', b, hR, rfl⟩
    have h1 : U cy' co' ≤ uR (cy' + co' / Rt) := (hU _).2 ⟨cy', co', rfl, rfl⟩
    have h2 := hub ⟨cy' + co' / Rt, b, hR, rfl⟩
    linarith

/-- AKMM, p. 646, with Obstfeld–Rogoff (3.56)–(3.60): the altruistic recursion
`Wₜ = u(R_{y,t}) + βWₜ₊₁` gives the dynastic utility `W₀ = Σ βᵗu(R_{y,t})` iff `βⁿWₙ → 0`. -/
theorem ol_dynastic_utility {β : ℝ} {u : ℝ → ℝ} {Ry W : ℕ → ℝ}
    (hW : ∀ t, W t = u (Ry t) + β * W (t + 1)) (hsum : Summable fun t => β ^ t * u (Ry t)) :
    W 0 = ∑' t, β ^ t * u (Ry t) ↔ Tendsto (fun n => β ^ n * W n) atTop (𝓝 0) := by
  have h := ObstfeldRogoff.LifeCycleFiscalPolicy.RicardianEquivalence.utility_eq_tsum_iff hW 0
    (by simpa using hsum)
  simpa using h

/-- **AKMM, p. 646: "the steady-state wealth distribution is indeterminate"** in the altruistic
OLG economy: with `β(1 + r − δ) = 1` and a concave indirect utility `u`, holding any bequest `a₀`
forever (`R_y = (r − δ)a₀ + wε̂ > 0`) solves the dynastic problem. -/
theorem ol_indeterminacy {β r δ w εy εo a₀ : ℝ} {uR du : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hss : β * (1 + r - δ) = 1) (htan : ∀ x z, 0 < x → 0 < z → uR x ≤ uR z + du z * (x - z))
    (hc : 0 < (r - δ) * a₀ + w * (εy + εo / (1 + r - δ))) :
    dy_Optimal β (1 + r - δ) a₀ (w * (εy + εo / (1 + r - δ))) uR
      (fun _ => (r - δ) * a₀ + w * (εy + εo / (1 + r - δ))) (fun _ => a₀) := by
  have h := dy_constant_optimal (a₀ := a₀) (y := w * (εy + εo / (1 + r - δ))) hβ hβ1 hss htan
    (by rw [show 1 + r - δ - 1 = r - δ by ring]; exact hc)
  rwa [show 1 + r - δ - 1 = r - δ by ring] at h

/-- AKMM, p. 646: a concrete altruistic economy: `U(c_y, c_o) = log(c_y + c_o/R̃)` has indirect
utility `u = log`, which is concave, so `ol_indeterminacy` applies. -/
theorem ol_example {Rt : ℝ} :
    ol_IsIndirect (fun cy co => Real.log (cy + co / Rt)) Rt Real.log ∧
      ∀ x z : ℝ, 0 < x → 0 < z → Real.log x ≤ Real.log z + z⁻¹ * (x - z) := by
  refine ⟨fun R => ⟨⟨R, 0, by simp, by simp⟩, ?_⟩, dy_log_tangent⟩
  rintro x ⟨cy, co, hb, rfl⟩
  simp only [hb, le_refl]

/-! ### Discount-factor heterogeneity -/

/-- **AKMM, p. 647.** An optimal plan with constant positive consumption and `u′(c) ≠ 0` has
`βR = 1`. -/
theorem hd_constant_beta {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hu : ∀ x, 0 < x → HasDerivAt u (du x) x) (hopt : dy_Optimal β R a₀ y u c a)
    (hconst : ∀ t, c t = c 0) (hdu : du (c 0) ≠ 0) : β * R = 1 := by
  have h := eq_11_13 hβ hR hu hopt 0
  rw [hconst 1] at h
  have : (β * R - 1) * du (c 0) = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · linarith
  · exact absurd h0 hdu

/-- **AKMM, p. 647: "the long-run wealth distribution is determinate".** Two consumers facing
the same `R` with `βᵢ ≠ βⱼ` cannot both have constant positive consumption (`u′ ≠ 0`). -/
theorem hd_unique_beta {βi βj R ai aj yi yj : ℝ} {u du : ℝ → ℝ} {ci cj ai' aj' : ℕ → ℝ}
    (hβi : 0 < βi) (hβj : 0 < βj) (hR : 0 < R) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hi : dy_Optimal βi R ai yi u ci ai') (hj : dy_Optimal βj R aj yj u cj aj')
    (hci : ∀ t, ci t = ci 0) (hcj : ∀ t, cj t = cj 0) (hdi : du (ci 0) ≠ 0)
    (hdj : du (cj 0) ≠ 0) : βi = βj := by
  have h1 := hd_constant_beta hβi hR hu hi hci hdi
  have h2 := hd_constant_beta hβj hR hu hj hcj hdj
  have : (βi - βj) * R = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- **AKMM, p. 647.** If `βR < 1` and `u′` is positive and strictly decreasing, optimal
consumption is strictly decreasing. -/
theorem hd_strictAnti {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : β * R < 1) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : StrictAnti c := by
  have hc : ∀ t, 0 < c t := hopt.1.2.2.1
  apply strictAnti_nat_of_succ_lt
  intro t
  have he := eq_11_13 hβ hR hu hopt t
  have hlt : du (c t) < du (c (t + 1)) := by
    have := hdu _ (hc (t + 1))
    have : β * R * du (c (t + 1)) < 1 * du (c (t + 1)) := mul_lt_mul_of_pos_right hβR this
    linarith
  by_contra hle
  have hle := not_lt.1 hle
  rcases hle.eq_or_lt with h | h
  · rw [h] at hlt; exact lt_irrefl _ hlt
  · have := hanti (hc t) (hc (t + 1)) h
    linarith

/-- **AKMM, p. 647: "all other consumers' consumption levels are converging to zero".** If
`βR < 1` (here `R = 1/β_max` and `β < β_max`) and `u′` is positive and strictly decreasing,
optimal consumption converges to `0`. -/
theorem hd_tendsto_zero {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : β * R < 1) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : Tendsto c atTop (𝓝 0) := by
  have hc : ∀ t, 0 < c t := hopt.1.2.2.1
  have hq : 1 < (β * R)⁻¹ := one_lt_inv_iff₀.2 ⟨mul_pos hβ hR, hβR⟩
  have hpow : ∀ t, du (c t) = (β * R)⁻¹ ^ t * du (c 0) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have he := eq_11_13 hβ hR hu hopt t
      have hne : β * R ≠ 0 := (mul_pos hβ hR).ne'
      rw [pow_succ, mul_comm ((β * R)⁻¹ ^ t), mul_assoc, ← ih, he]
      field_simp
  have hdiv : Tendsto (fun t => du (c t)) atTop atTop := by
    exact ((tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const (hdu _ (hc 0))).congr
      fun t => (hpow t).symm
  rw [tendsto_order]
  refine ⟨fun e he => Eventually.of_forall fun t => he.trans (hc t), fun e he => ?_⟩
  filter_upwards [hdiv.eventually_gt_atTop (du e)] with t ht
  by_contra hle
  have hle := not_lt.1 hle
  rcases hle.eq_or_lt with h | h
  · rw [h] at ht; exact lt_irrefl _ ht
  · have := hanti he (hc t) h
    linarith

/-- **AKMM, p. 647: "`0 = (r − δ)aᵢ + εᵢw`".** With `R = 1 + r − δ > 1` and `βR < 1`, the
wealth of the impatient consumer converges to `−y/(R − 1) = −εᵢw/(r − δ)` (the natural debt
limit), where consumption is zero. -/
theorem hd_assets_limit {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR1 : 1 < R)
    (hβR : β * R < 1) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : Tendsto a atTop (𝓝 (-y / (R - 1))) := by
  have hR : 0 < R := one_pos.trans hR1
  have hopt1 : cd_Plan R (R * a₀) (fun _ => y) c (fun t => R * a t) := hopt.1
  obtain ⟨-, hb, hcpos, htvc⟩ := hopt1
  have hc0 := hd_tendsto_zero hβ hR hβR hu hdu hanti hopt
  have hdec := hd_strictAnti hβ hR hβR hu hdu hanti hopt
  have hq0 : 0 ≤ R⁻¹ := inv_nonneg.2 hR.le
  have hq1 : R⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR1
  have hy : ∀ t : ℕ, Summable fun j : ℕ => R⁻¹ ^ j * y := fun _ =>
    (summable_geometric_of_lt_one hq0 hq1).mul_right y
  have hpv : ∀ t, Summable fun j => R⁻¹ ^ j * c (t + j) := fun t =>
    cd_summable_pv_cons (y := fun _ => y) (a := fun t => R * a t) hR hb (fun s => (hcpos s).le) t
      (cd_tvc_shift hR htvc t) (hy t)
  have hib : ∀ t, ∑' j, R⁻¹ ^ j * c (t + j) = R * a t + y * (1 - R⁻¹)⁻¹ := by
    intro t
    have := cd_intertemporal_budget (y := fun _ => y) (a := fun t => R * a t) hR hb t
      (cd_tvc_shift hR htvc t) (hy t) (hpv t)
    rw [this, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
    ring
  have hbound : ∀ t, ∑' j, R⁻¹ ^ j * c (t + j) ≤ c t * (1 - R⁻¹)⁻¹ := by
    intro t
    rw [← tsum_geometric_of_lt_one hq0 hq1, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (hpv t)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
    rw [mul_comm (c t)]
    exact mul_le_mul_of_nonneg_left (hdec.antitone (Nat.le_add_right t j)) (pow_nonneg hq0 j)
  have hnn : ∀ t, 0 ≤ ∑' j, R⁻¹ ^ j * c (t + j) := fun t =>
    tsum_nonneg fun j => mul_nonneg (pow_nonneg hq0 j) (hcpos _).le
  have hS : Tendsto (fun t => ∑' j, R⁻¹ ^ j * c (t + j)) atTop (𝓝 0) := by
    have hup : Tendsto (fun t => c t * (1 - R⁻¹)⁻¹) atTop (𝓝 0) := by
      simpa using hc0.mul_const (1 - R⁻¹)⁻¹
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hnn hbound
  have ha : ∀ t, a t = R⁻¹ * (∑' j, R⁻¹ ^ j * c (t + j) - y * (1 - R⁻¹)⁻¹) := by
    intro t
    rw [hib t]
    field_simp
    ring
  have hlim : -y / (R - 1) = R⁻¹ * (0 - y * (1 - R⁻¹)⁻¹) := by
    have h1 : R - 1 ≠ 0 := by linarith
    have h2 : R ≠ 0 := hR.ne'
    field_simp
    ring
  rw [hlim]
  exact ((hS.sub_const _).const_mul _).congr fun t => (ha t).symm

/-- **AKMM, p. 647.** If `βR > 1` (a consumer more patient than `1/R`), optimal consumption is
strictly increasing, so it is never constant: the steady-state `R` is `1/max βᵢ`. -/
theorem hd_strictMono {β R a₀ y : ℝ} {u du : ℝ → ℝ} {c a : ℕ → ℝ} (hβ : 0 < β) (hR : 0 < R)
    (hβR : 1 < β * R) (hu : ∀ x, 0 < x → HasDerivAt u (du x) x)
    (hdu : ∀ x, 0 < x → 0 < du x) (hanti : StrictAntiOn du (Set.Ioi 0))
    (hopt : dy_Optimal β R a₀ y u c a) : StrictMono c := by
  have hc : ∀ t, 0 < c t := hopt.1.2.2.1
  apply strictMono_nat_of_lt_succ
  intro t
  have he := eq_11_13 hβ hR hu hopt t
  have hlt : du (c (t + 1)) < du (c t) := by
    have := hdu _ (hc (t + 1))
    have : 1 * du (c (t + 1)) < β * R * du (c (t + 1)) := mul_lt_mul_of_pos_right hβR this
    linarith
  by_contra hle
  have hle := not_lt.1 hle
  rcases hle.eq_or_lt with h | h
  · rw [h] at hlt; exact lt_irrefl _ hlt
  · have := hanti (hc (t + 1)) (hc t) h
    linarith

/-- **AKMM, p. 649: return heterogeneity.** With a common `β` and `βR_max = 1` for the highest
return, every consumer with `Rᵢ < R_max` has `βRᵢ < 1`, so by `hd_tendsto_zero` and
`hd_assets_limit` their consumption vanishes and their wealth tends to `−εᵢw/(Rᵢ − 1)`. -/
theorem rh_lower_return_iff {β Rmax Ri : ℝ} (hβ : 0 < β) (hmax : β * Rmax = 1) :
    β * Ri < 1 ↔ Ri < Rmax := by
  rw [← hmax]
  exact mul_lt_mul_iff_of_pos_left hβ

end AKMM.Inequality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §21.2.3: distortions and credit-market restrictions

AKMM, §21.2.3, pp. 647–648.

* **A progressive capital-income tax** (p. 647, fn 25): gross capital income
  `f(a) = a(1 + (r − δ)(1 − τ(a)))`. `pt_hasDerivAt`: the gross marginal return is
  `1 + (r − δ)(1 − τ(a) − aτ′(a))`; footnote 25 prints `τ′(a)/a` in place of `aτ′(a)`, which agrees
  only for `a² = 1` or `τ′(a) = 0` (`pt_printed_iff`, `pt_printed_counterexample`).
  `pt_steady_euler`: in a steady state with no profitable one-period deviation,
  `β(1 + (r − δ)(1 − τ(a) − aτ′(a))) = 1` (`pt_steady_euler_example` shows the hypothesis is met).
  `pt_g_strictMonoOn`: if `τ′ > 0` is nondecreasing, `τ(a) + aτ′(a)` is strictly increasing on
  `a ≥ 0`; `pt_unique`, `pt_equal_wealth`: the steady-state condition then holds at most at one
  `a ≥ 0`, so all savers hold the same wealth. `pt_proportional`: a flat tax leaves the
  condition independent of `a`.
* **Two agents with alternating endowments** (p. 648): `ta_q_eq_beta`: without borrowing
  limits the Euler equations of both agents and market clearing force `qₜ = β` and constant
  consumption; `ta_footnote_26`: the equilibrium with `a₀ = 0` (consumption
  `(ȳ + βy)/(1 + β)` and `(βȳ + y)/(1 + β)`, optimal by Chapter 11's Euler sufficiency) and
  `ta_footnote_26_richer`: agent A consumes more.
  `ta_binding_alloc`: with the limit `a` binding, `c = ȳ + a(1 + q)` and `y − a(1 + q)`;
  `ta_binding_kkt`: if `q` solves `qu′(ȳ + a(1 + q)) = βu′(y − a(1 + q))` and the borrower is
  poorer, the borrower's Euler inequality holds strictly (the limit binds) and `q > β`;
  `ta_binding_strictMono`, `ta_binding_unique`, `ta_binding_exists`: the equation has exactly one
  solution.
-/

namespace AKMM.Inequality

open Filter Topology AKMM.Consumption

/-! ### Progressive capital taxation -/

/-- AKMM, p. 647: gross capital income `a(1 + (r − δ)(1 − τ(a)))`. -/
def pt_gross (r δ : ℝ) (τ : ℝ → ℝ) (a : ℝ) : ℝ := a * (1 + (r - δ) * (1 - τ a))

/-- **AKMM, fn 25, p. 648 (corrected): the gross return on saving.**
`d/da [a(1 + (r − δ)(1 − τ(a)))] = 1 + (r − δ)(1 − τ(a) − aτ′(a))`. -/
theorem pt_hasDerivAt {r δ a τ' : ℝ} {τ : ℝ → ℝ} (hτ : HasDerivAt τ τ' a) :
    HasDerivAt (pt_gross r δ τ) (1 + (r - δ) * (1 - τ a - a * τ')) a := by
  have h := (hasDerivAt_id a).mul ((hτ.const_sub 1).const_mul (r - δ) |>.const_add 1)
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- **AKMM, fn 25: the printed return `1 + (r − δ)(1 − τ(a) − τ′(a)/a)`** equals the true one iff
`r = δ`, `τ′(a) = 0` or `a² = 1` (for `a ≠ 0`). -/
theorem pt_printed_iff {r δ a τa τ' : ℝ} (ha : a ≠ 0) :
    1 + (r - δ) * (1 - τa - τ' / a) = 1 + (r - δ) * (1 - τa - a * τ') ↔
      r = δ ∨ τ' = 0 ∨ a ^ 2 = 1 := by
  constructor
  · intro h
    have h1 : (r - δ) * τ' * (a ^ 2 - 1) = 0 := by
      have : (r - δ) * (a * τ' - τ' / a) = 0 := by linarith
      have e : (r - δ) * τ' * (a ^ 2 - 1) = a * ((r - δ) * (a * τ' - τ' / a)) := by
        field_simp
      rw [e, this, mul_zero]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (by linarith))
  · rintro (h | h | h)
    · rw [h, sub_self, zero_mul, zero_mul]
    · rw [h, zero_div, mul_zero]
    · have e : τ' / a = a * τ' := by
        rw [div_eq_iff ha]
        linear_combination (-τ') * h
      rw [e]

/-- AKMM, fn 25: a concrete discrepancy: `τ(a) = a/10`, `r − δ = 1/10`, `a = 2`: the true gross
return is `1.06`, the printed formula gives `1.075`. -/
theorem pt_printed_counterexample :
    HasDerivAt (pt_gross (1 / 10) 0 (fun a => a / 10)) (53 / 50) 2 ∧
      1 + (1 / 10 - 0) * (1 - 2 / 10 - (1 / 10) / 2) ≠ (53 / 50 : ℝ) := by
  refine ⟨?_, by norm_num⟩
  have h := pt_hasDerivAt (r := 1 / 10) (δ := 0) (a := 2) (τ := fun a => a / 10)
    (τ' := 1 / 10) (by simpa using (hasDerivAt_id (2 : ℝ)).div_const 10)
  convert h using 1
  norm_num

/-- **AKMM, fn 25: "in steady state this expression times `β` must equal 1".** Let the
consumer hold `a` forever with consumption `c = f(a) − a + y`. If saving `a + h` for one
period and returning to `a` is never better
(`u(c − h) + βu(c + f(a + h) − f(a)) ≤ u(c) + βu(c)`), `u′(c) ≠ 0` and `f′(a)` exists, then
`βf′(a) = 1`. With `f = pt_gross r δ τ` this is `β(1 + (r − δ)(1 − τ(a) − aτ′(a))) = 1`. -/
theorem pt_steady_euler {β a c du f' : ℝ} {u f : ℝ → ℝ} (hu : HasDerivAt u du c)
    (hf : HasDerivAt f f' a) (hdu : du ≠ 0)
    (hdev : ∀ h, u (c - h) + β * u (c + (f (a + h) - f a)) ≤ u c + β * u c) :
    β * f' = 1 := by
  set φ := fun h => u (c - h) + β * u (c + (f (a + h) - f a)) with hφ
  have hd1 : HasDerivAt (fun h => u (c - h)) (du * (-1)) 0 := by
    have : HasDerivAt (fun h : ℝ => c - h) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub c
    have hu' : HasDerivAt u du (c - 0) := by rw [sub_zero]; exact hu
    exact hu'.comp 0 this
  have hd2 : HasDerivAt (fun h => u (c + (f (a + h) - f a))) (du * f') 0 := by
    have hin : HasDerivAt (fun h : ℝ => c + (f (a + h) - f a)) f' 0 := by
      have hf' : HasDerivAt (fun h => f (a + h)) f' 0 := by
        have := HasDerivAt.comp_const_add a 0 (by rwa [add_zero])
        simpa using this
      simpa using (hf'.sub_const (f a)).const_add c
    have hu' : HasDerivAt u du (c + (f (a + 0) - f a)) := by simpa using hu
    exact hu'.comp 0 hin
  have hφd : HasDerivAt φ (du * (-1) + β * (du * f')) 0 := hd1.add (hd2.const_mul β)
  have hmax : IsLocalMax φ 0 := Filter.Eventually.of_forall fun h => by
    simp only [hφ, add_zero, sub_self, sub_zero]
    exact hdev h
  have h0 := hmax.hasDerivAt_eq_zero hφd
  have : du * (β * f' - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hdu
  · linarith

/-- The hypothesis of `pt_steady_euler` is met: linear utility, `f(a) = Ra`, `βR = 1`. -/
theorem pt_steady_euler_example {β R a c : ℝ} (hβR : β * R = 1) :
    ∀ h, (c - h) + β * (c + (R * (a + h) - R * a)) ≤ c + β * c := by
  intro h
  have : β * (R * (a + h) - R * a) = h := by
    have e : R * (a + h) - R * a = R * h := by ring
    rw [e, ← mul_assoc, hβR, one_mul]
  linarith

/-- **AKMM, p. 647.** If `τ′ > 0` is nondecreasing on `a ≥ 0` (the book: "positive and strictly
increasing"), then `g(a) = τ(a) + aτ′(a)` is strictly increasing on `a ≥ 0`. -/
theorem pt_g_strictMonoOn {τ τd : ℝ → ℝ} (hτ : ∀ a, HasDerivAt τ (τd a) a)
    (hpos : ∀ a, 0 ≤ a → 0 < τd a) (hmono : MonotoneOn τd (Set.Ici 0)) :
    StrictMonoOn (fun a => τ a + a * τd a) (Set.Ici 0) := by
  have hτm : StrictMonoOn τ (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x _ => (hτ x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hτ x).deriv]
      exact hpos x (le_of_lt hx)
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  have h1 := hτm hx hy hxy
  have h2 : τd x ≤ τd y := hmono hx hy hxy.le
  have h3 : x * τd x ≤ y * τd y :=
    mul_le_mul hxy.le h2 (hpos x hx').le (hx'.trans hxy.le)
  simp only
  linarith

/-- **AKMM, p. 647.** If `g = τ + aτ′` is strictly increasing on a set `S` and `r ≠ δ`, the
steady-state condition `β(1 + (r − δ)(1 − g(a))) = 1` holds for at most one `a ∈ S`. -/
theorem pt_unique {β r δ : ℝ} {g : ℝ → ℝ} {S : Set ℝ} (hβ : β ≠ 0) (hr : r ≠ δ)
    (hg : StrictMonoOn g S) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hsa : β * (1 + (r - δ) * (1 - g a)) = 1) (hsb : β * (1 + (r - δ) * (1 - g b)) = 1) :
    a = b := by
  have hrd : r - δ ≠ 0 := sub_ne_zero.2 hr
  have h1 : β * (r - δ) * (g a - g b) = 0 := by linarith
  have hgab : g a = g b := by
    rcases mul_eq_zero.1 h1 with h | h
    · rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hβ
      · exact absurd h' hrd
    · linarith
  exact hg.injOn ha hb hgab

/-- **AKMM, p. 648: "in steady state, `aᵢ = aᵢ′` for all `i` and `i′`".** Under the hypotheses of
`pt_g_strictMonoOn`, any two savers (`a ≥ 0`) satisfying the steady-state condition hold the
same wealth. -/
theorem pt_equal_wealth {ι : Type*} {β r δ : ℝ} {τ τd : ℝ → ℝ} (hβ : β ≠ 0) (hr : r ≠ δ)
    (hτ : ∀ a, HasDerivAt τ (τd a) a) (hpos : ∀ a, 0 ≤ a → 0 < τd a)
    (hmono : MonotoneOn τd (Set.Ici 0)) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hss : ∀ i, β * (1 + (r - δ) * (1 - τ (a i) - a i * τd (a i))) = 1) (i j : ι) :
    a i = a j := by
  have hg := pt_g_strictMonoOn hτ hpos hmono
  refine pt_unique hβ hr hg (ha i) (ha j) ?_ ?_
  · linear_combination hss i
  · linear_combination hss j

/-- **AKMM, p. 648: "proportional taxes … lower saving, but not differentially across saving
levels".** With a flat rate (`τ′ = 0`) the steady-state condition does not depend on `a`. -/
theorem pt_proportional (β r δ τ0 a b : ℝ) :
    β * (1 + (r - δ) * (1 - τ0 - a * 0)) = β * (1 + (r - δ) * (1 - τ0 - b * 0)) := by
  ring

/-! ### Two agents with alternating endowments -/

/-- **AKMM, p. 648: "there will be full consumption smoothing and `q = β`".** If both agents'
Euler equations `qₜu′(cₜ) = βu′(cₜ₊₁)` hold, total consumption is constant and `u′` is
strictly decreasing, then `qₜ = β` and each agent's consumption is constant. -/
theorem ta_q_eq_beta {β Y : ℝ} {du : ℝ → ℝ} {q cA cB : ℕ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x)
    (hcA : ∀ t, 0 < cA t) (hcB : ∀ t, 0 < cB t)
    (hA : ∀ t, q t * du (cA t) = β * du (cA (t + 1)))
    (hB : ∀ t, q t * du (cB t) = β * du (cB (t + 1)))
    (hY : ∀ t, cA t + cB t = Y) (t : ℕ) :
    q t = β ∧ cA (t + 1) = cA t ∧ cB (t + 1) = cB t := by
  have hYt := hY t
  have hYs := hY (t + 1)
  -- compare consumptions through marginal utilities
  have key : ∀ x y : ℝ, 0 < x → 0 < y → (du x < du y ↔ y < x) := by
    intro x y hx hy
    constructor
    · intro h
      by_contra hle
      have hle := not_lt.1 hle
      rcases hle.eq_or_lt with e | e
      · rw [e] at h; exact lt_irrefl _ h
      · have := hanti hx hy e; linarith
    · intro h; exact hanti hy hx h
  have hdA := hdu _ (hcA t)
  have hdB := hdu _ (hcB t)
  rcases lt_trichotomy (q t) β with hq | hq | hq
  · exfalso
    have h1 : du (cA (t + 1)) < du (cA t) := by
      have := hA t
      have : q t * du (cA t) < β * du (cA t) := mul_lt_mul_of_pos_right hq hdA
      nlinarith
    have h2 : du (cB (t + 1)) < du (cB t) := by
      have := hB t
      have : q t * du (cB t) < β * du (cB t) := mul_lt_mul_of_pos_right hq hdB
      nlinarith
    have := (key _ _ (hcA _) (hcA _)).1 h1
    have := (key _ _ (hcB _) (hcB _)).1 h2
    linarith
  · refine ⟨hq, ?_, ?_⟩
    · have h := hA t
      rw [hq] at h
      have h' : du (cA t) = du (cA (t + 1)) := mul_left_cancel₀ hβ.ne' h
      by_contra hne
      rcases lt_or_gt_of_ne hne with e | e
      · have := hanti (hcA _) (hcA _) e; linarith
      · have := hanti (hcA _) (hcA _) e; linarith
    · have h := hB t
      rw [hq] at h
      have h' : du (cB t) = du (cB (t + 1)) := mul_left_cancel₀ hβ.ne' h
      by_contra hne
      rcases lt_or_gt_of_ne hne with e | e
      · have := hanti (hcB _) (hcB _) e; linarith
      · have := hanti (hcB _) (hcB _) e; linarith
  · exfalso
    have h1 : du (cA t) < du (cA (t + 1)) := by
      have := hA t
      have : β * du (cA t) < q t * du (cA t) := mul_lt_mul_of_pos_right hq hdA
      nlinarith
    have h2 : du (cB t) < du (cB (t + 1)) := by
      have := hB t
      have : β * du (cB t) < q t * du (cB t) := mul_lt_mul_of_pos_right hq hdB
      nlinarith
    have := (key _ _ (hcA _) (hcA _)).1 h1
    have := (key _ _ (hcB _) (hcB _)).1 h2
    linarith

/-- AKMM, p. 648: agent A's endowment, `ȳ` in even periods and `y` in odd periods. -/
def ta_endow (yH yL : ℝ) (t : ℕ) : ℝ := if Even t then yH else yL

/-- AKMM, fn 26: agent A's assets with `a₀ = 0`: `0` in even periods, `(ȳ − y)/(1 + β)` in odd
periods. -/
noncomputable def ta_assets (β yH yL : ℝ) (t : ℕ) : ℝ :=
  if Even t then 0 else (yH - yL) / (1 + β)

/-- **AKMM, fn 26, p. 648: the unconstrained equilibrium with `a₀ = 0`.** With `q = β`
(`R = 1/β`), agent A consumes `(ȳ + βy)/(1 + β)` and agent B `(βȳ + y)/(1 + β)` every period;
A's assets alternate between `0` and `(ȳ − y)/(1 + β)`, B's are their negative (bonds clear), and
both plans are optimal (Chapter 11's Euler sufficiency, `cd_optimal_of_euler`). -/
theorem ta_footnote_26 {β yH yL : ℝ} {u du : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hyL : 0 < yL)
    (hy : yL < yH) (htan : ∀ x z, 0 < x → 0 < z → u x ≤ u z + du z * (x - z)) :
    cd_Optimal β β⁻¹ 0 u (ta_endow yH yL) (fun _ => (yH + β * yL) / (1 + β))
        (ta_assets β yH yL) ∧
      cd_Optimal β β⁻¹ 0 u (ta_endow yL yH) (fun _ => (β * yH + yL) / (1 + β))
        (fun t => -ta_assets β yH yL t) ∧
      ∀ t, ta_assets β yH yL t + -ta_assets β yH yL t = 0 := by
  have hR : 0 < β⁻¹ := inv_pos.2 hβ
  have h1β : 0 < 1 + β := by linarith
  have hsum : ∀ yA yB : ℝ, 0 ≤ yA → 0 ≤ yB →
      Summable fun j => β⁻¹⁻¹ ^ j * ta_endow yA yB j := by
    intro yA yB hA hB
    rw [inv_inv]
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ.le j) ?_) (fun j => ?_)
      ((summable_geometric_of_lt_one hβ.le hβ1).mul_right (yA + yB))
    · unfold ta_endow; split_ifs <;> assumption
    · unfold ta_endow
      split_ifs <;> exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hβ.le j)
  have htvc : ∀ s : ℝ, Tendsto (fun t => (s * ta_assets β yH yL t) / β⁻¹ ^ t) atTop (𝓝 0) := by
    intro s
    have hb : ∀ t, |s * ta_assets β yH yL t| ≤ |s| * ((yH - yL) / (1 + β)) := by
      intro t
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
      unfold ta_assets
      have : 0 ≤ (yH - yL) / (1 + β) := div_nonneg (by linarith) h1β.le
      split_ifs
      · simpa using this
      · rw [abs_of_nonneg this]
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).const_mul
      (|s| * ((yH - yL) / (1 + β)))
    rw [mul_zero] at hg
    have e : ∀ t : ℕ, (s * ta_assets β yH yL t) / β⁻¹ ^ t = (s * ta_assets β yH yL t) * β ^ t :=
      fun t => by rw [inv_pow, div_inv_eq_mul]
    simp_rw [e]
    refine squeeze_zero_norm (fun t => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ t)]
    exact mul_le_mul_of_nonneg_right (hb t) (pow_nonneg hβ.le t)
  refine ⟨?_, ?_, fun t => by ring⟩
  · apply cd_optimal_of_euler hβ hR htan
    · refine ⟨by simp [ta_assets], fun t => ?_, fun _ => div_pos (by nlinarith) h1β, ?_⟩
      · unfold ta_assets ta_endow
        rcases Nat.even_or_odd t with ht | ht
        · have ht1 : ¬ Even (t + 1) := Nat.not_even_iff_odd.2 (Even.add_one ht)
          simp only [ht, ht1, ↓reduceIte]
          field_simp
          ring
        · have ht1 : Even (t + 1) := Odd.add_one ht
          have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
          simp only [ht', ht1, ↓reduceIte]
          field_simp
          ring
      · simpa using htvc 1
    · intro t; rw [mul_inv_cancel₀ hβ.ne', one_mul]
    · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
    · exact hsum yH yL (by linarith) hyL.le
  · apply cd_optimal_of_euler hβ hR htan
    · refine ⟨by simp [ta_assets], fun t => ?_, fun _ => div_pos (by nlinarith) h1β, ?_⟩
      · unfold ta_assets ta_endow
        rcases Nat.even_or_odd t with ht | ht
        · have ht1 : ¬ Even (t + 1) := Nat.not_even_iff_odd.2 (Even.add_one ht)
          simp only [ht, ht1, ↓reduceIte]
          field_simp
          ring
        · have ht1 : Even (t + 1) := Odd.add_one ht
          have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
          simp only [ht', ht1, ↓reduceIte]
          field_simp
          ring
      · have := htvc (-1)
        simpa using this
    · intro t; rw [mul_inv_cancel₀ hβ.ne', one_mul]
    · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
    · exact hsum yL yH hyL.le (by linarith)

/-- **AKMM, fn 26: "agent A is richer in present-value terms … and will therefore permanently
have a somewhat higher consumption".** For `0 < β < 1` and `ȳ > y`,
`(ȳ + βy)/(1 + β) > (βȳ + y)/(1 + β)`. -/
theorem ta_footnote_26_richer {β yH yL : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hy : yL < yH) :
    (β * yH + yL) / (1 + β) < (yH + β * yL) / (1 + β) := by
  apply div_lt_div_of_pos_right _ (by linarith)
  nlinarith

/-- **AKMM, p. 648: the stationary allocation with a binding limit `a < 0`.** The currently poor
agent borrows to the limit (`a′ = a`), the currently rich one enters with debt `a` and lends
`−a`: their budgets `c + q(−a) = ȳ + a` and `c + qa = y − a` give consumption `ȳ + a(1 + q)` and
`y − a(1 + q)`, which sum to `ȳ + y`. -/
theorem ta_binding_alloc (q a yH yL : ℝ) :
    (yH + a * (1 + q)) + q * (-a) = yH + a ∧ (yL - a * (1 + q)) + q * a = yL + (-a) ∧
      (yH + a * (1 + q)) + (yL - a * (1 + q)) = yH + yL := by
  refine ⟨by ring, by ring, by ring⟩

/-- **AKMM, p. 648: the limit binds.** If `q` solves `qu′(ȳ + a(1 + q)) = βu′(y − a(1 + q))`
and the borrower consumes less (`y − a(1 + q) < ȳ + a(1 + q)`), then `q > β` and the borrower's
Euler inequality holds strictly: `qu′(y − a(1 + q)) > βu′(ȳ + a(1 + q))`, so he would borrow
more if allowed. -/
theorem ta_binding_kkt {β q a yH yL : ℝ} {du : ℝ → ℝ} (hβ : 0 < β)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x)
    (hpoor : 0 < yL - a * (1 + q)) (hlt : yL - a * (1 + q) < yH + a * (1 + q))
    (heq : q * du (yH + a * (1 + q)) = β * du (yL - a * (1 + q))) :
    β < q ∧ β * du (yH + a * (1 + q)) < q * du (yL - a * (1 + q)) := by
  have hrich : 0 < yH + a * (1 + q) := hpoor.trans hlt
  have hd : du (yH + a * (1 + q)) < du (yL - a * (1 + q)) := hanti hpoor hrich hlt
  have hdr := hdu _ hrich
  have hdp := hdu _ hpoor
  constructor
  · by_contra hle
    have hle := not_lt.1 hle
    have : q * du (yH + a * (1 + q)) < β * du (yL - a * (1 + q)) :=
      calc q * du (yH + a * (1 + q)) ≤ β * du (yH + a * (1 + q)) :=
            mul_le_mul_of_nonneg_right hle hdr.le
        _ < β * du (yL - a * (1 + q)) := mul_lt_mul_of_pos_left hd hβ
    linarith
  · have h1 : β * du (yH + a * (1 + q)) * du (yH + a * (1 + q)) <
        β * du (yL - a * (1 + q)) * du (yL - a * (1 + q)) := by
      have := mul_lt_mul hd hd.le hdr hdp.le
      nlinarith
    rw [← heq] at h1
    have : β * du (yH + a * (1 + q)) * du (yH + a * (1 + q)) <
        q * du (yL - a * (1 + q)) * du (yH + a * (1 + q)) := by nlinarith
    exact lt_of_mul_lt_mul_right this hdr.le

/-- AKMM, p. 648: the excess of the lender's marginal valuation,
`h(q) = qu′(ȳ + a(1 + q)) − βu′(y − a(1 + q))`. -/
def ta_h (β a yH yL : ℝ) (du : ℝ → ℝ) (q : ℝ) : ℝ :=
  q * du (yH + a * (1 + q)) - β * du (yL - a * (1 + q))

/-- **AKMM, p. 648: "one equation and one unknown".** For `a < 0`, `u′ > 0` strictly decreasing,
`h` is strictly increasing on the prices `q > 0` with positive consumptions. -/
theorem ta_binding_strictMono {β a yH yL : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (ha : a < 0)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x) :
    StrictMonoOn (ta_h β a yH yL du)
      {q | 0 < q ∧ 0 < yH + a * (1 + q) ∧ 0 < yL - a * (1 + q)} := by
  rintro p ⟨hp, hpr, hpp⟩ q ⟨hq, hqr, hqp⟩ hpq
  have hr : yH + a * (1 + q) < yH + a * (1 + p) := by nlinarith
  have hpo : yL - a * (1 + p) < yL - a * (1 + q) := by nlinarith
  have h1 : du (yH + a * (1 + p)) < du (yH + a * (1 + q)) := hanti hqr hpr hr
  have h2 : du (yL - a * (1 + q)) < du (yL - a * (1 + p)) := hanti hpp hqp hpo
  have hd1 := hdu _ hpr
  unfold ta_h
  have : p * du (yH + a * (1 + p)) < q * du (yH + a * (1 + q)) :=
    calc p * du (yH + a * (1 + p)) < q * du (yH + a * (1 + p)) :=
          mul_lt_mul_of_pos_right hpq hd1
      _ < q * du (yH + a * (1 + q)) := mul_lt_mul_of_pos_left h1 hq
  have : β * du (yL - a * (1 + q)) < β * du (yL - a * (1 + p)) := mul_lt_mul_of_pos_left h2 hβ
  linarith

/-- **AKMM, p. 648: the stationary interest rate is unique.** -/
theorem ta_binding_unique {β a yH yL p q : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (ha : a < 0)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ x, 0 < x → 0 < du x)
    (hp : 0 < p ∧ 0 < yH + a * (1 + p) ∧ 0 < yL - a * (1 + p))
    (hq : 0 < q ∧ 0 < yH + a * (1 + q) ∧ 0 < yL - a * (1 + q))
    (hhp : ta_h β a yH yL du p = 0) (hhq : ta_h β a yH yL du q = 0) : p = q :=
  (ta_binding_strictMono hβ ha hanti hdu).injOn hp hq (hhp.trans hhq.symm)

/-- **AKMM, p. 648: the stationary interest rate exists.** If `u′` is continuous on `(0, ∞)`,
`a < 0`, the borrower is poorer at `q = β` (`y − a(1 + β) < ȳ + a(1 + β)`), and some
`q₁ ≥ β` with `ȳ + a(1 + q₁) > 0` has `h(q₁) ≥ 0`, then `h(q) = 0` for some `q ∈ (β, q₁]`. -/
theorem ta_binding_exists {β a yH yL q₁ : ℝ} {du : ℝ → ℝ} (hβ : 0 < β) (ha : a < 0)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hcont : ContinuousOn du (Set.Ioi 0))
    (hyL : 0 < yL) (hlt : yL - a * (1 + β) < yH + a * (1 + β)) (hq₁ : β ≤ q₁)
    (hr₁ : 0 < yH + a * (1 + q₁)) (hh₁ : 0 ≤ ta_h β a yH yL du q₁) :
    ∃ q, β < q ∧ q ≤ q₁ ∧ ta_h β a yH yL du q = 0 := by
  have hpoor : ∀ q, β ≤ q → 0 < yL - a * (1 + q) := fun q hq => by nlinarith [hq]
  have hrich : ∀ q, q ≤ q₁ → 0 < yH + a * (1 + q) := fun q hq => by nlinarith [hq]
  have hβneg : ta_h β a yH yL du β < 0 := by
    unfold ta_h
    have := hanti (hpoor β le_rfl) (hlt.trans_le' le_rfl |>.trans' (hpoor β le_rfl)) hlt
    have h' : du (yH + a * (1 + β)) < du (yL - a * (1 + β)) :=
      hanti (hpoor β le_rfl) ((hpoor β le_rfl).trans hlt) hlt
    nlinarith
  have hc : ContinuousOn (ta_h β a yH yL du) (Set.Icc β q₁) := by
    unfold ta_h
    refine (continuousOn_id.mul ?_).sub (continuousOn_const.mul ?_)
    · exact hcont.comp (by fun_prop) fun q hq => hrich q hq.2
    · exact hcont.comp (by fun_prop) fun q hq => hpoor q hq.1
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Icc hq₁ hc ⟨hβneg.le, hh₁⟩
  refine ⟨q, ?_, hq.2, hq0⟩
  rcases hq.1.eq_or_lt with e | e
  · rw [← e] at hq0; linarith
  · exact e

end AKMM.Inequality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §21.2.3: idiosyncratic, uninsurable shocks

AKMM, §21.2.3, pp. 650–652.

* **Huggett with a zero borrowing limit** (p. 650; AKMM §17.4.4): income follows a finite
  Markov chain `P` on states `S` with endowments `e`. `hu_autarky_clearing`: bonds in zero net
  supply and `a′ ≥ 0` force `a′ = 0` for everyone (autarky). `hu_value`, `hu_qstar`: the valuation
  `βE[u′(e′) | i]/u′(eᵢ)` and its maximum `q*`. `hu_kkt_iff`: every agent's Euler inequality at
  the limit, `qu′(eᵢ) ≥ βE[u′(e′) | i]`, holds iff `q ≥ q*`; `hu_price_iff`: some agent is
  unconstrained (Euler equality) iff `q = q*`, the closed form of the book.
  `hu_rate_below_discount`: if the highest-endowment state can move to a poorer one, `q* > β`,
  so the interest rate `1/q* − 1` is below the discount rate.
* **Determinacy** (p. 650): `ui_determinate`: with i.i.d. income and `βR < 1`, Miao's
  Proposition 8.3.1 (Schechtman–Escudero, Clarida, Aiyagari) gives a unique stationary
  distribution of cash on hand, in contrast with the deterministic indeterminacy
  (`dy_indeterminacy_example`).
* **Kesten's moment condition** (p. 651, fn 31): for a finitely supported multiplier `s > 0`
  with `E log s < 0` and `P(s > 1) > 0`, `E s^ζ = 1` has exactly one root `ζ > 0`
  (`ke_moment`, `ke_moment_unique`, `ke_moment_exists`). The Kesten–Goldie tail theorem itself
  is not formalised.
-/

namespace AKMM.Inequality

open Filter Topology MeasureTheory Miao.IncompleteMarkets

/-! ### Huggett with `a = 0` -/

/-- **AKMM, p. 650: "the equilibrium is autarky".** If bonds are in zero net supply
(`Σ mᵢa′ᵢ = 0` over agent types with positive mass) and nobody may borrow (`a′ᵢ ≥ 0`), then
`a′ᵢ = 0` for every type. -/
theorem hu_autarky_clearing {ι : Type*} (s : Finset ι) (m a' : ι → ℝ) (hm : ∀ i ∈ s, 0 < m i)
    (ha : ∀ i ∈ s, 0 ≤ a' i) (hsum : ∑ i ∈ s, m i * a' i = 0) : ∀ i ∈ s, a' i = 0 := by
  intro i hi
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun j hj => mul_nonneg (hm j hj).le (ha j hj)).1
    hsum i hi
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd h' (hm i hi).ne'
  · exact h'

variable {S : Type*} [Fintype S]

/-- AKMM, p. 650: agent `i`'s valuation of the bond at autarky, `βE[u′(e′) | i]/u′(eᵢ)`. -/
noncomputable def hu_value (β : ℝ) (P : S → S → ℝ) (du : ℝ → ℝ) (e : S → ℝ) (i : S) : ℝ :=
  β * (∑ j, P i j * du (e j)) / du (e i)

/-- AKMM, p. 650: the autarky price `q* = maxᵢ βE[u′(e′) | i]/u′(eᵢ)`. -/
noncomputable def hu_qstar [Nonempty S] (β : ℝ) (P : S → S → ℝ) (du : ℝ → ℝ) (e : S → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (hu_value β P du e)

/-- **AKMM, p. 650.** At autarky, every agent's Euler inequality at the borrowing limit,
`qu′(eᵢ) ≥ βE[u′(e′) | i]`, holds iff `q ≥ q*`. -/
theorem hu_kkt_iff [Nonempty S] {β q : ℝ} {P : S → S → ℝ} {du : ℝ → ℝ} {e : S → ℝ}
    (hdu : ∀ i, 0 < du (e i)) :
    (∀ i, β * ∑ j, P i j * du (e j) ≤ q * du (e i)) ↔ hu_qstar β P du e ≤ q := by
  unfold hu_qstar
  rw [Finset.sup'_le_iff]
  refine forall_congr' fun i => ?_
  simp only [Finset.mem_univ, true_implies, hu_value]
  rw [div_le_iff₀ (hdu i)]

/-- **AKMM, p. 650: "a real interest rate determined in closed form based on the Euler equation
for the non-constrained agent".** All agents satisfy their Euler inequality and at least one
(the agent valuing the bond most) satisfies it with equality iff `q = q*`. -/
theorem hu_price_iff [Nonempty S] {β q : ℝ} {P : S → S → ℝ} {du : ℝ → ℝ} {e : S → ℝ}
    (hdu : ∀ i, 0 < du (e i)) :
    ((∀ i, β * ∑ j, P i j * du (e j) ≤ q * du (e i)) ∧
      ∃ i, β * ∑ j, P i j * du (e j) = q * du (e i)) ↔ q = hu_qstar β P du e := by
  constructor
  · rintro ⟨hall, i, hi⟩
    have hle := (hu_kkt_iff hdu).1 hall
    have hv : hu_value β P du e i = q := by
      unfold hu_value; rw [hi]; field_simp [(hdu i).ne']
    have : hu_value β P du e i ≤ hu_qstar β P du e :=
      Finset.le_sup' (hu_value β P du e) (Finset.mem_univ i)
    linarith
  · intro hq
    refine ⟨(hu_kkt_iff hdu).2 hq.ge, ?_⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (hu_value β P du e)
    refine ⟨i, ?_⟩
    have : hu_value β P du e i = q := by rw [← hi]; exact hq.symm
    unfold hu_value at this
    rw [div_eq_iff (hdu i).ne'] at this
    exact this

/-- **AKMM, p. 650 (and §17.4.4): the autarky rate is below the rate of time preference.** If
`P` is a transition matrix, `u′ > 0` strictly decreasing, `iₘ` has the highest endowment and
moves with positive probability to a state with a lower endowment, then `q* > β`, i.e.
`1/q* < 1/β`. -/
theorem hu_rate_below_discount [Nonempty S] {β : ℝ} {P : S → S → ℝ} {du : ℝ → ℝ} {e : S → ℝ}
    (hβ : 0 < β) (hP : ∀ i j, 0 ≤ P i j) (hP1 : ∀ i, ∑ j, P i j = 1)
    (hanti : StrictAntiOn du (Set.Ioi 0)) (hdu : ∀ i, 0 < du (e i)) (he : ∀ i, 0 < e i) (im jl : S)
    (hmax : ∀ j, e j ≤ e im) (hlow : e jl < e im) (hpos : 0 < P im jl) :
    β < hu_qstar β P du e := by
  have hdu_ge : ∀ j, du (e im) ≤ du (e j) := by
    intro j
    rcases (hmax j).eq_or_lt with h | h
    · rw [h]
    · exact (hanti (he j) (he im) h).le
  have hlt : du (e im) < du (e jl) := hanti (he jl) (he im) hlow
  have hsum : du (e im) < ∑ j, P im j * du (e j) := by
    have h1 : ∑ j, P im j * du (e im) = du (e im) := by rw [← Finset.sum_mul, hP1, one_mul]
    rw [← h1]
    apply Finset.sum_lt_sum
    · exact fun j _ => mul_le_mul_of_nonneg_left (hdu_ge j) (hP im j)
    · exact ⟨jl, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hpos⟩
  have hdm : 0 < du (e im) := hdu im
  have hv : β < hu_value β P du e im := by
    unfold hu_value
    rw [lt_div_iff₀ hdm]
    exact mul_lt_mul_of_pos_left hsum hβ
  exact hv.trans_le (Finset.le_sup' (hu_value β P du e) (Finset.mem_univ im))

/-! ### Determinacy of the stationary distribution -/

/-- **AKMM, p. 650: "the presence of uninsurable, idiosyncratic shocks makes the steady-state
distribution of wealth determinate".** For the income fluctuation problem with i.i.d. income
(Miao, §8.3) and `βR < 1`, under Miao's Proposition 8.3.1 hypotheses, cash on hand
`x = Râ + y − rb` has exactly one stationary distribution on `[x_min, x_max]`. -/
theorem ui_determinate {M : SIModel} (S : M.Solution) (hβR : M.β * M.R < 1) {ddu : ℝ → ℝ}
    (hddu : ∀ c, 0 < c → HasDerivAt M.du (ddu c) c) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : ∀ᶠ c in atTop, -c * ddu c / M.du c < γ) (hy : M.ymin < M.ymax) {α : ℝ} (hα : 0 < α)
    (hμ : ∀ a b, M.ymin ≤ a → a ≤ b → b ≤ M.ymax → α * (b - a) ≤ M.law.real (Set.Icc a b)) :
    ∃! lam : Measure (Set.Icc M.xmin S.xmax), IsProbabilityMeasure lam ∧
      SIWC.adjointOp (S.kernel S.xmax) lam = lam := by
  obtain ⟨lam, hp, hinv, huniq, -⟩ := S.proposition_8_3_1 hβR hddu hγ0 hγ hy hα hμ
  exact ⟨lam, ⟨hp, hinv⟩, fun ν hν => huniq ν hν.1 hν.2⟩

/-! ### Kesten's moment condition -/

/-- AKMM, fn 31, p. 651: the moment function `ζ ↦ E s^ζ = Σₖ pₖ sₖ^ζ` of a finitely supported
multiplier. -/
noncomputable def ke_moment {ι : Type*} [Fintype ι] (p s : ι → ℝ) (ζ : ℝ) : ℝ :=
  ∑ k, p k * s k ^ ζ

/-- AKMM, fn 31: `E s^0 = 1`. -/
theorem ke_moment_zero {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp1 : ∑ k, p k = 1) :
    ke_moment p s 0 = 1 := by
  simp [ke_moment, hp1]

/-- AKMM, fn 31: the derivative of the moment function, `Σₖ pₖ sₖ^ζ log sₖ`. -/
theorem ke_moment_hasDerivAt {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hs : ∀ k, 0 < s k)
    (ζ : ℝ) : HasDerivAt (ke_moment p s) (∑ k, p k * (s k ^ ζ * Real.log (s k))) ζ := by
  have h : ∀ k ∈ (Finset.univ : Finset ι), HasDerivAt (fun z => p k * s k ^ z)
      (p k * (s k ^ ζ * Real.log (s k))) ζ :=
    fun k _ => ((Real.hasStrictDerivAt_const_rpow (hs k) ζ).hasDerivAt).const_mul (p k)
  have := HasDerivAt.fun_sum h
  unfold ke_moment
  convert this using 1

/-- **AKMM, fn 31: the root of `E s^ζ = 1` is unique.** If `p > 0`, `s > 0` and some `sₖ ≠ 1`,
there is at most one `ζ > 0` with `E s^ζ = 1` (strict convexity of the moment function). -/
theorem ke_moment_unique {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (k₀ : ι) (hk₀ : s k₀ ≠ 1) {ζ₁ ζ₂ : ℝ}
    (h₁ : 0 < ζ₁) (h₂ : 0 < ζ₂) (hm₁ : ke_moment p s ζ₁ = 1) (hm₂ : ke_moment p s ζ₂ = 1) :
    ζ₁ = ζ₂ := by
  -- each `z ↦ sₖ^z = exp(z log sₖ)` is convex, strictly for `sₖ ≠ 1`
  have hpt : ∀ k, ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      s k ^ (t * z) ≤ (1 - t) + t * s k ^ z ∧
        (s k ≠ 1 → s k ^ (t * z) < (1 - t) + t * s k ^ z) := by
    intro k z t hz ht ht1
    have e1 : Real.log (s k) * (t * z) = (1 - t) • (0 : ℝ) + t • (Real.log (s k) * z) := by
      simp only [smul_eq_mul]; ring
    rw [Real.rpow_def_of_pos (hs k), Real.rpow_def_of_pos (hs k), e1]
    refine ⟨?_, fun hne => ?_⟩
    · have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        (by linarith : (0 : ℝ) ≤ 1 - t) ht.le (by ring)
      simpa using this
    · have hl : Real.log (s k) ≠ 0 := fun h0 => hne (Real.eq_one_of_pos_of_log_eq_zero (hs k) h0)
      have hne' : (0 : ℝ) ≠ Real.log (s k) * z := (mul_ne_zero hl hz.ne').symm
      have := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        hne' (by linarith : (0 : ℝ) < 1 - t) ht (by ring)
      simpa using this
  have hmix : ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      ke_moment p s (t * z) < (1 - t) + t * ke_moment p s z := by
    intro z t hz ht ht1
    have h1 : (1 - t) + t * ke_moment p s z = ∑ k, p k * ((1 - t) + t * s k ^ z) := by
      unfold ke_moment
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1]
    unfold ke_moment
    apply Finset.sum_lt_sum
    · exact fun k _ => mul_le_mul_of_nonneg_left (hpt k z t hz ht ht1).1 (hp k).le
    · exact ⟨k₀, Finset.mem_univ _,
        mul_lt_mul_of_pos_left ((hpt k₀ z t hz ht ht1).2 hk₀) (hp k₀)⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := hmix ζ₂ (ζ₁ / ζ₂) h₂ (div_pos h₁ h₂) ((div_lt_one h₂).2 hlt)
    rw [show ζ₁ / ζ₂ * ζ₂ = ζ₁ by field_simp, hm₁, hm₂] at this
    linarith
  · have := hmix ζ₁ (ζ₂ / ζ₁) h₁ (div_pos h₂ h₁) ((div_lt_one h₁).2 hlt)
    rw [show ζ₂ / ζ₁ * ζ₁ = ζ₂ by field_simp, hm₁, hm₂] at this
    linarith

/-- **AKMM, fn 31: "there exists a `ζ > 0` with `E[s^ζ] = 1`".** If `p > 0`, `s > 0`,
`E log s < 0` and some `sₖ > 1`, the moment condition has a root `ζ > 0`. -/
theorem ke_moment_exists {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (hlog : ∑ k, p k * Real.log (s k) < 0) (k₁ : ι)
    (hk₁ : 1 < s k₁) : ∃ ζ, 0 < ζ ∧ ke_moment p s ζ = 1 := by
  have h0 := ke_moment_zero (s := s) hp1
  -- below one just to the right of zero
  have hd := ke_moment_hasDerivAt (p := p) hs 0
  simp only [Real.rpow_zero, one_mul] at hd
  have hsl := hd.tendsto_slope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx) :
    𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0)
  obtain ⟨ζ₀, hζ₀, hlt⟩ := ((hsl.eventually (gt_mem_nhds hlog)).and self_mem_nhdsWithin).exists
  have hζ₀pos : (0 : ℝ) < ζ₀ := hlt
  have hm₀ : ke_moment p s ζ₀ < 1 := by
    rw [slope_def_field, h0, sub_zero] at hζ₀
    have := (div_lt_iff₀ hζ₀pos).1 hζ₀
    linarith
  -- above one far to the right
  have hl1 : 0 < Real.log (s k₁) := Real.log_pos hk₁
  set ζ₁ := 1 / (p k₁ * Real.log (s k₁)) with hζ₁
  have hζ₁pos : 0 < ζ₁ := div_pos one_pos (mul_pos (hp k₁) hl1)
  have hm₁ : 1 < ke_moment p s ζ₁ := by
    have hk : p k₁ * s k₁ ^ ζ₁ ≤ ke_moment p s ζ₁ := by
      unfold ke_moment
      exact Finset.single_le_sum (f := fun k => p k * s k ^ ζ₁)
        (fun k _ => mul_nonneg (hp k).le (Real.rpow_pos_of_pos (hs k) _).le)
        (Finset.mem_univ k₁)
    have hexp : ζ₁ * Real.log (s k₁) + 1 ≤ s k₁ ^ ζ₁ := by
      rw [Real.rpow_def_of_pos (hs k₁), mul_comm (Real.log _)]
      exact Real.add_one_le_exp _
    have e : p k₁ * (ζ₁ * Real.log (s k₁) + 1) = 1 + p k₁ := by
      have := (hp k₁).ne'
      have := hl1.ne'
      rw [hζ₁]; field_simp
    have := mul_le_mul_of_nonneg_left hexp (hp k₁).le
    linarith [hp k₁]
  have hcont : Continuous (ke_moment p s) :=
    continuous_iff_continuousAt.2 fun z => (ke_moment_hasDerivAt hs z).continuousAt
  obtain ⟨ζ, hζ, hζ1⟩ := intermediate_value_uIcc (a := ζ₀) (b := ζ₁) hcont.continuousOn
    (Set.mem_uIcc.2 (Or.inl ⟨hm₀.le, hm₁.le⟩))
  refine ⟨ζ, ?_, hζ1⟩
  rcases Set.mem_uIcc.1 hζ with h | h
  · exact hζ₀pos.trans_le h.1
  · exact hζ₁pos.trans_le h.1

end AKMM.Inequality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §21.1: Lorenz curves, Gini coefficients and Pareto tails

AKMM, §21.1, pp. 629–631, with footnote 1. The Lorenz curve and the Gini coefficient of a
sorted sample `y₀ ≤ … ≤ y_{n−1}` are Miao's (`Miao.IncompleteMarkets.ay_lorenz`, `ay_gini`,
Chapter 17), whose Gini is twice the area between the diagonal and the Lorenz curve.

* `gi_gini_eq_ratio`: the Gini coefficient is `A/(A + B)` (p. 630).
* `gi_lorenz_le_diag`, `gi_lorenz_convex`: the Lorenz curve lies below the 45-degree line and is
  convex; `gi_lorenz_concentrated`: under complete concentration it is flat at zero up to the last
  point.
* `gi_gini_mem_Icc`, `gi_gini_equal`, `gi_gini_eq_zero_iff`: the Gini lies in `[0, 1]`, is zero
  under perfect equality, and only then; `gi_gini_concentrated_tendsto`: it tends to one when one
  agent holds all income.
* `pa_ccdf`, `pa_log_ccdf`, `pa_log_ccdf_strictAnti`: for the Pareto distribution
  `F(x) = 1 − (x̲/x)^α` of footnote 1, `log(1 − F(x))` is linear in `log x` with slope `−α`.
-/

namespace AKMM.Inequality

open Filter Topology Miao.IncompleteMarkets

/-- **AKMM, p. 630: "The Gini coefficient is computed as the area `A` divided by the area
`A + B`".** With `B` the area under the piecewise-linear Lorenz curve and `A = 1/2 − B` the area
between it and the diagonal, `G = A/(A + B)`. -/
theorem gi_gini_eq_ratio (y : ℕ → ℝ) (n : ℕ) :
    ay_gini y n = (1 / 2 - ∑ i ∈ Finset.range n,
        (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) /
      ((1 / 2 - ∑ i ∈ Finset.range n,
        (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) +
        ∑ i ∈ Finset.range n, (1 / n) * ((ay_lorenz y n i + ay_lorenz y n (i + 1)) / 2)) := by
  rw [ay_gini_eq_area, sub_add_cancel]
  ring

/-- **AKMM, p. 630: "The Lorenz curve is always below the 45-degree line"** (Miao's
`ay_lorenz_le_diag`). -/
theorem gi_lorenz_le_diag {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) {i : ℕ} (hi : i ≤ n) : ay_lorenz y n i ≤ i / n :=
  ay_lorenz_le_diag hsort hT hi

/-- **AKMM, p. 630: the Lorenz curve is convex**: for sorted data its increments
`z_{i+1} − z_i = y_i/Σy` are nondecreasing. -/
theorem gi_lorenz_convex {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) {i : ℕ} (hi : i + 1 < n) :
    ay_lorenz y n (i + 1) - ay_lorenz y n i ≤ ay_lorenz y n (i + 2) - ay_lorenz y n (i + 1) := by
  simp only [ay_lorenz, Finset.sum_range_succ]
  rw [← sub_div, ← sub_div, div_le_div_iff_of_pos_right hT]
  have := hsort i (i + 1) (Nat.le_succ i) hi
  linarith

/-- **AKMM, p. 630: "The most extreme income inequality would be a Lorenz curve that is a flat
line … up until 100, where it jumps to 100".** If only the last of `m + 1` agents has income, the
Lorenz curve is `0` at `i ≤ m` and `1` at `m + 1`. -/
theorem gi_lorenz_concentrated {y : ℕ → ℝ} {m : ℕ} (hy : ∀ j, j < m → y j = 0) (hm : 0 < y m) :
    (∀ i, i ≤ m → ay_lorenz y (m + 1) i = 0) ∧ ay_lorenz y (m + 1) (m + 1) = 1 := by
  have hpre : ∀ i, i ≤ m → ∑ j ∈ Finset.range i, y j = 0 := fun i hi =>
    Finset.sum_eq_zero fun j hj => hy j ((Finset.mem_range.1 hj).trans_le hi)
  have hT : 0 < ∑ j ∈ Finset.range (m + 1), y j := by
    rw [Finset.sum_range_succ, hpre m le_rfl, zero_add]; exact hm
  refine ⟨fun i hi => ?_, ay_lorenz_n hT⟩
  rw [ay_lorenz, hpre i hi, zero_div]

/-- **AKMM, p. 630: the Gini coefficient lies in `[0, 1]`** (Miao's `ay_gini_nonneg`,
`ay_gini_le`) for sorted nonnegative data with positive total. -/
theorem gi_gini_mem_Icc {y : ℕ → ℝ} {n : ℕ} (hy : ∀ j, 0 ≤ y j)
    (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k) (hT : 0 < ∑ j ∈ Finset.range n, y j) :
    ay_gini y n ∈ Set.Icc 0 1 :=
  ⟨ay_gini_nonneg hsort hT, (ay_gini_le hy hT).2⟩

/-- **AKMM, p. 630: "When there is perfect equality, the Gini coefficient is therefore 0"**
(Miao's `ay_gini_equal`). -/
theorem gi_gini_equal {y : ℕ → ℝ} {n : ℕ} {c : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hy : ∀ j, j < n → y j = c) : ay_gini y n = 0 :=
  ay_gini_equal hc hn hy

/-- AKMM, p. 630, the converse: a zero Gini coefficient means perfect equality. For sorted data
with positive total, `G = 0` iff `y_j = (Σy)/n` for every `j < n`. -/
theorem gi_gini_eq_zero_iff {y : ℕ → ℝ} {n : ℕ} (hsort : ∀ j k, j ≤ k → k < n → y j ≤ y k)
    (hT : 0 < ∑ j ∈ Finset.range n, y j) :
    ay_gini y n = 0 ↔ ∀ j, j < n → y j = (∑ k ∈ Finset.range n, y k) / n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hT
    · exact h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set T := ∑ k ∈ Finset.range n, y k with hTd
  constructor
  · intro h0
    have hS : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) =
        ∑ i ∈ Finset.range n, (((2 * i + 1 : ℕ) : ℝ) / n) := by
      have h1 : ∑ i ∈ Finset.range n, (ay_lorenz y n i + ay_lorenz y n (i + 1)) = n := by
        rw [ay_gini] at h0
        field_simp at h0
        linarith
      rw [h1]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ay_sum_odd]
      field_simp
    have hle : ∀ i ∈ Finset.range n, ay_lorenz y n i + ay_lorenz y n (i + 1) ≤
        ((2 * i + 1 : ℕ) : ℝ) / n := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have h1 := ay_lorenz_le_diag hsort hT hi'.le
      have h2 := ay_lorenz_le_diag hsort hT (Nat.succ_le_of_lt hi')
      have e : (((2 * i + 1 : ℕ) : ℝ)) / n = i / n + ((i : ℝ) + 1) / n := by
        push_cast; ring
      rw [e]
      push_cast at h2
      linarith
    have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hS
    have hz : ∀ i, i ≤ n → ay_lorenz y n i = i / n := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp [ay_lorenz]
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k < n := by omega
        have h1 := ay_lorenz_le_diag hsort hT hk.le
        have h2 := ay_lorenz_le_diag hsort hT hi
        have h3 := heq k (Finset.mem_range.2 hk)
        have e : (((2 * k + 1 : ℕ) : ℝ)) / n = k / n + ((k : ℝ) + 1) / n := by
          push_cast; ring
        rw [e] at h3
        push_cast at h2 ⊢
        linarith
    intro j hj
    have h1 := hz (j + 1) hj
    have h2 := hz j hj.le
    simp only [ay_lorenz, Finset.sum_range_succ] at h1 h2
    have e : y j =
        T * ((∑ k ∈ Finset.range j, y k + y j) / T - (∑ k ∈ Finset.range j, y k) / T) := by
      field_simp
      ring
    rw [e, h1, h2]
    push_cast
    field_simp
    ring
  · intro h
    have hc : 0 < T / n := div_pos hT hnpos
    exact ay_gini_equal hc hn h

/-- **AKMM, p. 630: "the Gini coefficient tends to 1 in the extreme case where one agent holds all
income".** With `m + 1` agents of whom one holds everything, `G = 1 − 1/(m + 1)` (Miao's
`ay_gini_concentrated`), which tends to `1`. -/
theorem gi_gini_concentrated_tendsto {y : ℕ → ℕ → ℝ} (hy : ∀ m j, j < m → y m j = 0)
    (hm : ∀ m, 0 < y m m) :
    Tendsto (fun m => ay_gini (y m) (m + 1)) atTop (𝓝 1) := by
  have h : ∀ m, ay_gini (y m) (m + 1) = 1 - 1 / ((m + 1 : ℕ) : ℝ) := fun m =>
    ay_gini_concentrated (hm m) (hy m) rfl
  simp_rw [h]
  exact ay_gini_concentrated_tendsto

/-- AKMM, fn 1, p. 631: the Pareto complementary distribution `1 − F(x) = (x̲/x)^α`. -/
noncomputable def pa_ccdf (α xm x : ℝ) : ℝ := (xm / x) ^ α

/-- **AKMM, p. 631 and fn 1: "a linear relation between the logarithm of `x` and the logarithm
of one minus the cumulative distribution at `x`".** For `x ≥ x̲ > 0`,
`log(1 − F(x)) = α log x̲ − α log x`, with slope `−α` in `log x`. -/
theorem pa_log_ccdf {α xm x : ℝ} (hxm : 0 < xm) (hx : 0 < x) :
    Real.log (pa_ccdf α xm x) = α * Real.log xm - α * Real.log x := by
  unfold pa_ccdf
  rw [Real.log_rpow (div_pos hxm hx), Real.log_div hxm.ne' hx.ne']
  ring

/-- **AKMM, fn 1: "the slope … is negative".** For `α > 0`, `log(1 − F)` is strictly decreasing
in `x > 0`. -/
theorem pa_log_ccdf_strictAnti {α xm : ℝ} (hα : 0 < α) (hxm : 0 < xm) :
    StrictAntiOn (fun x => Real.log (pa_ccdf α xm x)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  simp only
  rw [pa_log_ccdf hxm hx', pa_log_ccdf hxm hy']
  have := Real.log_lt_log hx' hxy
  nlinarith

end AKMM.Inequality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §21.3: why inequality matters for aggregates

AKMM, §21.3, pp. 656–661.

* **Education with a fixed cost** (§21.3.1, p. 657): `ed_educates`: a worker with wealth `W`
  educates iff the cost `F` can be self-financed (`W ≥ F`) and it pays (`w_s − F > w_u`);
  `ed_unconstrained`: with borrowing, wealth is irrelevant; `ed_fraction`: if `w_s − w_u > F` the
  mass educated is the mass with wealth at least `F`; `ed_wealth_matters`: two wealth
  distributions with the same mean educate different fractions.
* **MPCs and TANK** (§21.3.2, pp. 658–659): `mpc_binding`: at a binding borrowing limit
  consumption is cash on hand less the limit, so the MPC is `1`; `tank_mpc`: the hand-to-mouth
  share `γ = (M − m)/(1 − m)` delivers any aggregate MPC `M ∈ [m, 1]`.
* **A consumption externality** (p. 660): `ext_log_output`: with `y = A c^ω k^α`,
  `log y = log A + ω log c + α log k`, so with `ω = 0` output moves one-for-one with TFP and
  with `ω > 0` it also moves with consumption.
-/

namespace AKMM.Inequality

open Filter Topology MeasureTheory

/-- AKMM, p. 657: without borrowing, a worker with wealth `W` chooses education (lifetime income
`w_s − F`) over unskilled work (`w_u`) iff it is affordable and strictly better. -/
def ed_educates (ws wu F W : ℝ) : Prop := F ≤ W ∧ wu < ws - F

/-- An instance of `ed_educates`: `w_s = 3`, `w_u = 1`, `F = 1`, `W = 1`. -/
theorem ed_educates_example : ed_educates 3 1 1 1 := ⟨le_rfl, by norm_num⟩

/-- **AKMM, p. 657: "if `w_s − w_u > F`, it would pay off for the individual to obtain
education"**: with borrowing (no wealth requirement) the choice is independent of `W`. -/
theorem ed_unconstrained (ws wu F : ℝ) : wu < ws - F ↔ F < ws - wu := by
  constructor <;> intro h <;> linarith

/-- **AKMM, p. 657: "the fraction of individuals who would choose education … equals the
fraction of people with wealth above `F`".** If `w_s − w_u > F`, the set of educated wealth
levels is `[F, ∞)`, so for any wealth distribution `μ` the mass educated is `μ[F, ∞)`. -/
theorem ed_fraction {ws wu F : ℝ} (h : F < ws - wu) (μ : Measure ℝ) :
    μ {W | ed_educates ws wu F W} = μ (Set.Ici F) := by
  congr 1
  ext W
  simp only [ed_educates, Set.mem_ofPred_eq, Set.mem_Ici]
  constructor
  · exact fun h' => h'.1
  · exact fun h' => ⟨h', by linarith⟩

/-- **AKMM, p. 657: "the wealth distribution matters for educational attainment".** With
`w_s − w_u > F > 0`, everyone educates when all hold wealth `F`, but only half do when half hold
`0` and half `2F` (the same mean wealth). -/
theorem ed_wealth_matters {ws wu F : ℝ} (hF : 0 < F) (h : F < ws - wu) :
    (Measure.dirac F) {W | ed_educates ws wu F W} = 1 ∧
      ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) + (1 / 2 : ENNReal) • Measure.dirac (2 * F) :
        Measure ℝ) {W | ed_educates ws wu F W} = 1 / 2 := by
  rw [ed_fraction h, ed_fraction h]
  refine ⟨?_, ?_⟩
  · rw [Measure.dirac_apply' _ measurableSet_Ici]
    simp
  · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ measurableSet_Ici, Measure.dirac_apply' _ measurableSet_Ici]
    have h0 : (0 : ℝ) ∉ Set.Ici F := by simp [hF]
    have h2 : 2 * F ∈ Set.Ici F := by simp only [Set.mem_Ici]; linarith
    simp [h0, h2]

/-- **AKMM, p. 658, fn and Figure 21.10: "those who are literally borrowing-constrained have a
marginal propensity of 1".** If near cash on hand `x` the agent is at the limit `a′ = a̲`, so
`c(z) = z − a̲` for `z` near `x`, then `∂c/∂x = 1`. -/
theorem mpc_binding {c : ℝ → ℝ} {x al : ℝ} (h : ∀ᶠ z in 𝓝 x, c z = z - al) :
    HasDerivAt c 1 x :=
  ((hasDerivAt_id x).sub_const al).congr_of_eventuallyEq h

/-- **AKMM, p. 659: TANK.** A fraction `γ` of hand-to-mouth agents (MPC `1`) and `1 − γ` rentiers
(MPC `m < 1`) give the aggregate MPC `γ + (1 − γ)m`; for any target `M ∈ [m, 1]` the share
`γ = (M − m)/(1 − m) ∈ [0, 1]` delivers it ("an aggregate MPC of, say, 0.5"). -/
theorem tank_mpc {m M : ℝ} (hm : m < 1) (hmM : m ≤ M) (hM : M ≤ 1) :
    0 ≤ (M - m) / (1 - m) ∧ (M - m) / (1 - m) ≤ 1 ∧
      (M - m) / (1 - m) * 1 + (1 - (M - m) / (1 - m)) * m = M := by
  have h1 : 0 < 1 - m := sub_pos.2 hm
  refine ⟨div_nonneg (by linarith) h1.le, (div_le_one h1).2 (by linarith), ?_⟩
  field_simp
  ring

/-- **AKMM, p. 660: output with a consumption externality.** For `y = A c^ω k^α` with positive
`A, c, k`: `log y = log A + ω log c + α log k`. With `ω = 0` a one-percent TFP shock raises output
by one percent whatever consumption does; with `ω > 0` the consumption response adds
`ω · Δlog c`. -/
theorem ext_log_output {A c k ω α : ℝ} (hA : 0 < A) (hc : 0 < c) (hk : 0 < k) :
    Real.log (A * c ^ ω * k ^ α) = Real.log A + ω * Real.log c + α * Real.log k := by
  rw [Real.log_mul (mul_pos hA (Real.rpow_pos_of_pos hc ω)).ne'
    (Real.rpow_pos_of_pos hk α).ne', Real.log_mul hA.ne' (Real.rpow_pos_of_pos hc ω).ne',
    Real.log_rpow hc, Real.log_rpow hk]

end AKMM.Inequality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# §21.2.3: Kesten's random growth process `aₜ₊₁ = sₜaₜ + εₜ`

AKMM, §21.2.3, p. 651 and fn 31. Beyond the text (decision 5): the book states Kesten's theorem
without proof. The Kesten–Goldie tail asymptotics `P(A > a) ~ C a^{−ζ}` need the implicit
renewal theorem and are NOT formalised; what is proved is the stationary solution, the
convergence of the law of `aₜ`, and the moment characterisation of the tail index.

The setting is the canonical i.i.d. space `kp_P ν = infinitePi ν` on `ℕ → ℝ × ℝ`, coordinate `n`
being `(sₙ, εₙ)`, for any law `ν` of `(s, ε)` (every i.i.d. sequence has this law). Moments are
`E|s|^κ = ∫⁻ ‖x.1‖ₑ^κ ∂ν`, `E|ε|^κ = ∫⁻ ‖x.2‖ₑ^κ ∂ν`.

* **The stationary solution.** If `E|s|^κ < 1` and `E|ε|^κ < ∞` for some `κ > 0`, the perpetuity
  `A = Σₖ s₀⋯s_{k−1} εₖ` (`kp_perp`) converges absolutely a.s. (`kp_perp_hasSum_ae`) and in `L^κ`
  (`kp_perp_tendsto_Lp`); a.s. `A = ε₀ + s₀A′` with `A′ = A ∘ shift =ᵈ A` independent of
  `(s₀, ε₀)` (`kp_fixed_point`). For any `a₀` the law of `aₜ` (`kp_iter`) converges weakly to the
  law of `A`: `E f(aₜ) → E f(A)` for bounded continuous `f` (`kp_iter_tendsto_law`), because `aₜ`
  has the law of the backward iterate (`kp_iter_identDistrib`), which converges a.s. to `A`
  (`kp_back_tendsto_ae`).
* **Moments.** `E|A|^κ < ∞` when `E|s|^κ < 1`, `E|ε|^κ < ∞` (`kp_lintegral_perp_lt_top`, via
  subadditivity of `x^κ` for `κ ≤ 1` and Minkowski for `κ ≥ 1`, `kp_lintegral_tsum_rpow_le`), with
  the Markov bound `P(|A| ≥ a) ≤ C_κ a^{−κ}` (`kp_tail_bound`); `E A^κ = ∞` when `s, ε ≥ 0`,
  `E s^κ > 1`, `E ε^κ > 0` (`kp_lintegral_abs_eq_top`, `kp_lintegral_perp_eq_top`). Hence
  `sup {κ > 0 : E A^κ < ∞} = ζ` (`kp_tail_index`).
* **Finitely supported shocks.** For `s` finitely supported, not identically `1`, the root `ζ` of
  `E s^ζ = 1` separates `E s^κ < 1` from `E s^κ > 1` (`kp_moment_root`); for finitely supported
  `(s, ε)` with `ε ≥ 0` not a.s. `0` the tail index is the root of `ke_moment_exists`
  (`kp_finite_tail_index`, `kp_finite_tail_index_ke`); the two-point example `s ∈ {1/2, 3/2}`,
  `ε = 1` has tail index `1` (`kp_two_point`, `kp_two_point_ke`).

The moment condition `E s^ζ = 1` is weaker than the conclusion "Pareto tail with exponent `ζ`";
`kp_tail_index` proves exactly the moment-sense content of that conclusion. At `κ = ζ` itself
nothing is claimed.
-/

namespace AKMM.Inequality

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The i.i.d. space and its shift -/

/-- The canonical i.i.d. space for Kesten's process: `Ω = ℕ → ℝ × ℝ`, coordinate `n` being the
pair `(sₙ, εₙ)`, under the product of copies of the law `ν` of `(s, ε)`. -/
noncomputable abbrev kp_P (ν : Measure (ℝ × ℝ)) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => ν

/-- The shift `(ωₙ)ₙ ↦ (ωₙ₊₁)ₙ`. -/
def kp_shift (ω : ℕ → ℝ × ℝ) : ℕ → ℝ × ℝ := fun n => ω (n + 1)

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν]

theorem kp_shift_measurable : Measurable kp_shift :=
  Measurable.of_eval fun n => measurable_pi_apply (n + 1)

/-- The shift preserves the i.i.d. law. -/
theorem kp_shift_mp : MeasurePreserving kp_shift (kp_P ν) (kp_P ν) :=
  ⟨kp_shift_measurable, Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν)
    (f := Nat.succ) Nat.succ_injective⟩

/-- The first pair `ω 0` is independent of the shifted sequence. -/
theorem kp_indep_head_shift : IndepFun (fun ω : ℕ → ℝ × ℝ => ω 0) kp_shift (kp_P ν) := by
  have hI : iIndepFun (fun i (ω : ℕ → ℝ × ℝ) => ω i) (kp_P ν) :=
    iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
  rw [iIndepFun_iff_iIndep] at hI
  have hle : ∀ i, MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ × ℝ)) := fun i => (measurable_pi_apply i).comap_le
  have h := indep_iSup_of_disjoint hle hI (S := {0}) (T := {n | 1 ≤ n})
    (Set.disjoint_left.2 fun a ha hb => by simp_all)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({0} : Set ℕ)) =>
      MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) 0 rfl le_rfl
  · refine Measurable.comap_le ?_
    refine @Measurable.of_eval _ _ _ (⨆ i ∈ {n | 1 ≤ n}, MeasurableSpace.comap
      (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) _ _ fun n => ?_
    exact Measurable.of_comap_le (le_iSup₂_of_le (f := fun i (_ : i ∈ {n : ℕ | 1 ≤ n}) =>
      MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) (n + 1)
      (by simp) le_rfl)

/-- Independence of the first pair and the shift, in integral form. -/
theorem kp_lintegral_head_shift {F : ℝ × ℝ → ℝ≥0∞} {G : (ℕ → ℝ × ℝ) → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ ω, F (ω 0) * G (kp_shift ω) ∂kp_P ν = (∫⁻ x, F x ∂ν) * ∫⁻ ω, G ω ∂kp_P ν := by
  have h := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hF.comp (measurable_pi_apply 0)) (hG.comp kp_shift_measurable)
    ((kp_indep_head_shift (ν := ν)).comp hF hG)
  simp only [Pi.mul_apply, Function.comp_apply] at h
  rw [h, (kp_shift_mp (ν := ν)).lintegral_comp hG,
    (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).lintegral_comp hF]

/-- The moment formula for i.i.d. coordinates: `E[f(X₀)⋯f(X_{k−1}) g(X_k)] = (E f)^k E g`. -/
theorem kp_lintegral_prod_mul {f g : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (k : ℕ) : ∫⁻ ω, (∏ j ∈ Finset.range k, f (ω j)) * g (ω k) ∂kp_P ν =
      (∫⁻ x, f x ∂ν) ^ k * ∫⁻ x, g x ∂ν := by
  induction k with
  | zero =>
    simpa using (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).lintegral_comp hg
  | succ k ih =>
    have e : ∀ ω : ℕ → ℝ × ℝ, (∏ j ∈ Finset.range (k + 1), f (ω j)) * g (ω (k + 1)) =
        f (ω 0) * ((∏ j ∈ Finset.range k, f (kp_shift ω j)) * g (kp_shift ω k)) := by
      intro ω
      rw [Finset.prod_range_succ']
      simp only [kp_shift]
      ring
    simp_rw [e]
    have h2 := kp_lintegral_head_shift (ν := ν)
      (G := fun ω => (∏ j ∈ Finset.range k, f (ω j)) * g (ω k)) hf (by fun_prop)
    rw [h2, ih, pow_succ]
    ring

/-! ### Moments of a series of nonnegative functions -/

/-- Subadditivity of `x ↦ x^κ` for `0 < κ ≤ 1`, for finite sums. -/
theorem kp_rpow_sum_le_sum_rpow {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (x : ℕ → ℝ≥0∞) (n : ℕ) :
    (∑ k ∈ Finset.range n, x k) ^ κ ≤ ∑ k ∈ Finset.range n, x k ^ κ := by
  induction n with
  | zero => simp [ENNReal.zero_rpow_of_pos hκ0]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hκ0.le hκ1).trans (add_le_add ih le_rfl)

/-- Minkowski's inequality in `L^κ`, `κ ≥ 1`, for finite sums of nonnegative functions. -/
theorem kp_lintegral_sum_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {κ : ℝ}
    (hκ : 1 ≤ κ) (T : ℕ → α → ℝ≥0∞) (hT : ∀ k, Measurable (T k)) (n : ℕ) :
    (∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ) ^ (1 / κ) ≤
      ∑ k ∈ Finset.range n, (∫⁻ a, T k a ^ κ ∂μ) ^ (1 / κ) := by
  induction n with
  | zero =>
    have : (0 : ℝ) < κ := by linarith
    simp [ENNReal.zero_rpow_of_pos this, this]
  | succ n ih =>
    simp_rw [Finset.sum_range_succ]
    have hm : Measurable fun a => ∑ k ∈ Finset.range n, T k a :=
      Finset.measurable_sum _ fun k _ => hT k
    exact (ENNReal.lintegral_Lp_add_le hm.aemeasurable (hT n).aemeasurable hκ).trans
      (add_le_add ih le_rfl)

/-- **Geometric moment bounds sum.** If `E Tₖ^κ ≤ rᵏ c` with `r < 1`, then
`E (Σₖ Tₖ)^κ ≤ K c` with `K < ∞` depending only on `r` and `κ` (subadditivity of `x^κ` for
`κ ≤ 1`, Minkowski for `κ ≥ 1`). -/
theorem kp_lintegral_tsum_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {κ : ℝ}
    (hκ : 0 < κ) {r : ℝ≥0∞} (hr : r < 1) : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (T : ℕ → α → ℝ≥0∞) (c : ℝ≥0∞), (∀ k, Measurable (T k)) →
        (∀ k, ∫⁻ a, T k a ^ κ ∂μ ≤ r ^ k * c) → ∫⁻ a, (∑' k, T k a) ^ κ ∂μ ≤ K * c := by
  have hred : ∀ (T : ℕ → α → ℝ≥0∞), (∀ k, Measurable (T k)) →
      ∫⁻ a, (∑' k, T k a) ^ κ ∂μ = ⨆ n, ∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ := by
    intro T hT
    have e : ∀ a, (∑' k, T k a) ^ κ = ⨆ n, (∑ k ∈ Finset.range n, T k a) ^ κ := by
      intro a
      rw [ENNReal.tsum_eq_iSup_nat]
      exact Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
        (ENNReal.monotone_rpow_of_nonneg hκ.le) (ENNReal.zero_rpow_of_pos hκ)
    simp_rw [e]
    refine lintegral_iSup (fun n => (Finset.measurable_sum _ fun k _ => hT k).pow_const κ) ?_
    intro m n hmn a
    exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.range_mono hmn)) hκ.le
  rcases le_total κ 1 with h1 | h1
  · refine ⟨(1 - r)⁻¹, ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hr).ne', fun T c hT hc => ?_⟩
    rw [hred T hT]
    refine iSup_le fun n => ?_
    calc ∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ
        ≤ ∫⁻ a, ∑ k ∈ Finset.range n, T k a ^ κ ∂μ :=
          lintegral_mono fun a => kp_rpow_sum_le_sum_rpow hκ h1 _ n
      _ = ∑ k ∈ Finset.range n, ∫⁻ a, T k a ^ κ ∂μ :=
          lintegral_finsetSum _ fun k _ => (hT k).pow_const κ
      _ ≤ ∑ k ∈ Finset.range n, r ^ k * c := Finset.sum_le_sum fun k _ => hc k
      _ ≤ ∑' k, r ^ k * c := ENNReal.sum_le_tsum _
      _ = (1 - r)⁻¹ * c := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  · set q := r ^ (1 / κ) with hq
    have hq1 : q < 1 := ENNReal.rpow_lt_one hr (by positivity)
    refine ⟨((1 - q)⁻¹) ^ κ, (ENNReal.rpow_lt_top_of_nonneg hκ.le
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hq1).ne')).ne, fun T c hT hc => ?_⟩
    rw [hred T hT]
    refine iSup_le fun n => ?_
    have hb : (∫⁻ a, (∑ k ∈ Finset.range n, T k a) ^ κ ∂μ) ^ (1 / κ) ≤
        (1 - q)⁻¹ * c ^ (1 / κ) := by
      calc _ ≤ ∑ k ∈ Finset.range n, (∫⁻ a, T k a ^ κ ∂μ) ^ (1 / κ) :=
            kp_lintegral_sum_rpow_le h1 T hT n
        _ ≤ ∑ k ∈ Finset.range n, q ^ k * c ^ (1 / κ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          calc _ ≤ (r ^ k * c) ^ (1 / κ) := ENNReal.rpow_le_rpow (hc k) (by positivity)
            _ = q ^ k * c ^ (1 / κ) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hq, ← ENNReal.rpow_natCast,
                ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_comm,
                mul_comm (1 / κ)]
              exact mul_comm _ _
        _ ≤ ∑' k, q ^ k * c ^ (1 / κ) := ENNReal.sum_le_tsum _
        _ = (1 - q)⁻¹ * c ^ (1 / κ) := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    have := ENNReal.rpow_le_rpow hb hκ.le
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hκ.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hκ.le, ← ENNReal.rpow_mul, one_div_mul_cancel hκ.ne',
      ENNReal.rpow_one] at this

/-! ### The perpetuity `A = Σₖ s₀⋯s_{k−1} εₖ` -/

/-- The `k`th term `s₀⋯s_{k−1} εₖ` of the perpetuity (the book's `s₁⋯s_k ε_{k+1}`, with time
indexed from `0`). -/
noncomputable def kp_term (ω : ℕ → ℝ × ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range k, (ω j).1) * (ω k).2

/-- The absolute series `Σₖ |s₀⋯s_{k−1} εₖ|`, in `[0, ∞]`. -/
noncomputable def kp_abs (ω : ℕ → ℝ × ℝ) : ℝ≥0∞ :=
  ∑' k, ‖kp_term ω k‖ₑ

/-- The perpetuity `A = Σₖ s₀⋯s_{k−1} εₖ` (Lean's `tsum`: the sum where the series converges,
`0` elsewhere; it converges almost surely, `kp_perp_hasSum_ae`). -/
noncomputable def kp_perp (ω : ℕ → ℝ × ℝ) : ℝ :=
  ∑' k, kp_term ω k

theorem kp_term_measurable (k : ℕ) : Measurable fun ω : ℕ → ℝ × ℝ => kp_term ω k := by
  unfold kp_term
  fun_prop

theorem kp_abs_measurable : Measurable kp_abs :=
  Measurable.tsum fun k => (kp_term_measurable k).enorm

theorem kp_perp_measurable : Measurable kp_perp :=
  Measurable.tsum fun k => kp_term_measurable k

/-- Where the absolute series is finite, `A` is the sum of the series. -/
theorem kp_hasSum {ω : ℕ → ℝ × ℝ} (h : kp_abs ω ≠ ⊤) : HasSum (kp_term ω) (kp_perp ω) := by
  refine (Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 ?_)).hasSum
  simpa [kp_abs, enorm_eq_nnnorm] using h

/-- `|s₀⋯s_{n−1}|^κ = |s₀|^κ⋯|s_{n−1}|^κ`. -/
theorem kp_enorm_prod_rpow (ω : ℕ → ℝ × ℝ) (n : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖∏ j ∈ Finset.range n, (ω j).1‖ₑ ^ κ = ∏ j ∈ Finset.range n, ‖(ω j).1‖ₑ ^ κ := by
  have hp : ‖∏ j ∈ Finset.range n, (ω j).1‖ₑ = ∏ j ∈ Finset.range n, ‖(ω j).1‖ₑ := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, enorm_mul, ih]
  rw [hp, ENNReal.prod_rpow_of_nonneg hκ]

/-- `|s₀⋯s_{k−1} εₖ|^κ = |s₀|^κ⋯|s_{k−1}|^κ |εₖ|^κ`. -/
theorem kp_enorm_term_rpow (ω : ℕ → ℝ × ℝ) (k : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖kp_term ω k‖ₑ ^ κ = (∏ j ∈ Finset.range k, ‖(ω j).1‖ₑ ^ κ) * ‖(ω k).2‖ₑ ^ κ := by
  rw [kp_term, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hκ, kp_enorm_prod_rpow _ _ hκ]

/-- `E|s₀⋯s_{k−1} εₖ|^κ = (E|s|^κ)^k E|ε|^κ`. -/
theorem kp_lintegral_term {κ : ℝ} (hκ : 0 ≤ κ) (k : ℕ) :
    ∫⁻ ω, ‖kp_term ω k‖ₑ ^ κ ∂kp_P ν =
      (∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ k * ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν := by
  simp_rw [kp_enorm_term_rpow _ _ hκ]
  exact kp_lintegral_prod_mul (f := fun x => ‖x.1‖ₑ ^ κ) (g := fun x => ‖x.2‖ₑ ^ κ)
    (by fun_prop) (by fun_prop) k

/-- `E(Σₖ |s₀⋯s_{k−1} εₖ|)^κ < ∞` when `E|s|^κ < 1` and `E|ε|^κ < ∞`. -/
theorem kp_lintegral_abs_lt_top {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∫⁻ ω, kp_abs ω ^ κ ∂kp_P ν < ⊤ := by
  obtain ⟨K, hK, hb⟩ := kp_lintegral_tsum_rpow_le (μ := kp_P ν) hκ hρ
  exact (hb (fun k ω => ‖kp_term ω k‖ₑ) _ (fun k => (kp_term_measurable k).enorm)
    (fun k => (kp_lintegral_term hκ.le k).le)).trans_lt (ENNReal.mul_lt_top hK.lt_top hm.lt_top)

/-- The absolute series is finite almost surely. -/
theorem kp_abs_ae_lt_top {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∀ᵐ ω ∂kp_P ν, kp_abs ω < ⊤ := by
  have h := ae_lt_top' (kp_abs_measurable.pow_const κ).aemeasurable
    (kp_lintegral_abs_lt_top hκ hρ hm).ne
  filter_upwards [h] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos hκ).1 hω

/-- **AKMM, p. 651 (beyond the text): the perpetuity converges almost surely.** If
`E|s|^κ < 1` and `E|ε|^κ < ∞` for some `κ > 0`, the series `Σₖ s₀⋯s_{k−1} εₖ` converges
absolutely almost surely, with sum `A`. -/
theorem kp_perp_hasSum_ae {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∀ᵐ ω ∂kp_P ν, HasSum (kp_term ω) (kp_perp ω) := by
  filter_upwards [kp_abs_ae_lt_top hκ hρ hm] with ω hω using kp_hasSum hω.ne

/-- **AKMM, p. 651 (beyond the text): the perpetuity converges in `L^κ`.** Under the same
hypotheses, `E|A − Σ_{k<n} s₀⋯s_{k−1} εₖ|^κ → 0`. -/
theorem kp_perp_tendsto_Lp {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) :
    Tendsto (fun n => ∫⁻ ω, ‖kp_perp ω - ∑ k ∈ Finset.range n, kp_term ω k‖ₑ ^ κ ∂kp_P ν)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := kp_lintegral_tsum_rpow_le (μ := kp_P ν) hκ hρ
  have hbound : ∀ n, ∫⁻ ω, ‖kp_perp ω - ∑ k ∈ Finset.range n, kp_term ω k‖ₑ ^ κ ∂kp_P ν ≤
      K * ((∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ n * ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν) := by
    intro n
    have htail := hb (fun k ω => ‖kp_term ω (k + n)‖ₑ) _ (fun k => (kp_term_measurable _).enorm)
      (fun k => by rw [kp_lintegral_term hκ.le, pow_add, mul_assoc])
    refine le_trans (lintegral_mono_ae ?_) htail
    filter_upwards [kp_perp_hasSum_ae hκ hρ hm] with ω hω
    have h' := (hasSum_nat_add_iff' n).2 hω
    rw [← h'.tsum_eq]
    exact ENNReal.rpow_le_rpow enorm_tsum_le_tsum_enorm hκ.le
  have h0 : Tendsto (fun n => K * ((∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ n * ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν)) atTop
      (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := K) (ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) (Or.inr hm)) (Or.inr hK)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le)
    hbound

/-! ### The fixed-point law `A = ε₀ + s₀A′` -/

theorem kp_term_zero (ω : ℕ → ℝ × ℝ) : kp_term ω 0 = (ω 0).2 := by
  simp [kp_term]

theorem kp_term_succ (ω : ℕ → ℝ × ℝ) (k : ℕ) :
    kp_term ω (k + 1) = (ω 0).1 * kp_term (kp_shift ω) k := by
  simp only [kp_term, kp_shift, Finset.prod_range_succ']
  ring

/-- The absolute series satisfies `Σ = |ε₀| + |s₀| Σ′` pathwise, `Σ′` the series of the shift. -/
theorem kp_abs_eq (ω : ℕ → ℝ × ℝ) :
    kp_abs ω = ‖(ω 0).2‖ₑ + ‖(ω 0).1‖ₑ * kp_abs (kp_shift ω) := by
  rw [kp_abs, tsum_eq_zero_add' ENNReal.summable]
  simp_rw [kp_term_succ, enorm_mul, ENNReal.tsum_mul_left, kp_term_zero]
  rfl

/-- **AKMM, p. 651 (beyond the text): the stationary law is a fixed point of
`A ↦ sA + ε`.** Under the hypotheses of `kp_perp_hasSum_ae`, almost surely
`A = ε₀ + s₀A′` where `A′ = A ∘ shift` is the perpetuity of the shifted sequence `(sₙ₊₁, εₙ₊₁)`;
`A′` has the law of `A` and is independent of `(s₀, ε₀)`. So `A =ᵈ sA′ + ε` with `A′ =ᵈ A`
independent of `(s, ε)`. -/
theorem kp_fixed_point {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) :
    (∀ᵐ ω ∂kp_P ν, kp_perp ω = (ω 0).2 + (ω 0).1 * kp_perp (kp_shift ω)) ∧
      IdentDistrib (fun ω => kp_perp (kp_shift ω)) kp_perp (kp_P ν) (kp_P ν) ∧
      IndepFun (fun ω : ℕ → ℝ × ℝ => ω 0) (fun ω => kp_perp (kp_shift ω)) (kp_P ν) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := kp_perp_hasSum_ae hκ hρ hm
    have h' := (kp_shift_mp (ν := ν)).quasiMeasurePreserving.ae h
    filter_upwards [h, h'] with ω hω hω'
    have h1 : HasSum (fun k => kp_term ω (k + 1)) ((ω 0).1 * kp_perp (kp_shift ω)) := by
      simp_rw [kp_term_succ]
      exact hω'.mul_left _
    have h2 : HasSum (kp_term ω) ((ω 0).2 + (ω 0).1 * kp_perp (kp_shift ω)) := by
      refine (hasSum_nat_add_iff' 1).1 ?_
      rw [Finset.sum_range_one, kp_term_zero, add_sub_cancel_left]
      exact h1
    exact hω.unique h2
  · refine ⟨(kp_perp_measurable.comp kp_shift_measurable).aemeasurable,
      kp_perp_measurable.aemeasurable, ?_⟩
    change Measure.map (kp_perp ∘ kp_shift) _ = _
    rw [← Measure.map_map kp_perp_measurable kp_shift_measurable, (kp_shift_mp (ν := ν)).map_eq]
  · exact (kp_indep_head_shift (ν := ν)).comp measurable_id kp_perp_measurable

/-! ### Convergence of the law of `aₜ` -/

/-- Kesten's process `aₜ₊₁ = sₜaₜ + εₜ` from `a₀` (AKMM, p. 651). -/
noncomputable def kp_iter (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) : ℕ → ℝ
  | 0 => a₀
  | t + 1 => (ω t).1 * kp_iter a₀ ω t + (ω t).2

/-- The backward iterate `Σ_{k<t} s₀⋯s_{k−1} εₖ + s₀⋯s_{t−1} a₀`. -/
noncomputable def kp_back (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range t, kp_term ω k + (∏ j ∈ Finset.range t, (ω j).1) * a₀

/-- The index reversal `j ↦ t − 1 − j` on `{0, …, t − 1}`, the identity elsewhere. -/
def kp_rev (t j : ℕ) : ℕ := if j < t then t - 1 - j else j

theorem kp_rev_injective (t : ℕ) : Function.Injective (kp_rev t) := by
  intro i j h
  unfold kp_rev at h
  split_ifs at h <;> omega

/-- Reversing the first `t` coordinates preserves the i.i.d. law. -/
theorem kp_rev_mp (t : ℕ) :
    MeasurePreserving (fun (ω : ℕ → ℝ × ℝ) j => ω (kp_rev t j)) (kp_P ν) (kp_P ν) :=
  ⟨Measurable.of_eval fun _ => measurable_pi_apply _,
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => ν) (kp_rev_injective t)⟩

theorem kp_back_congr {a₀ : ℝ} {ω ω' : ℕ → ℝ × ℝ} {t : ℕ} (h : ∀ j < t, ω j = ω' j) :
    kp_back a₀ ω t = kp_back a₀ ω' t := by
  have hp : ∀ k ≤ t, ∏ j ∈ Finset.range k, (ω j).1 = ∏ j ∈ Finset.range k, (ω' j).1 :=
    fun k hk => Finset.prod_congr rfl fun j hj => by
      rw [h j (by have := Finset.mem_range.1 hj; omega)]
  unfold kp_back
  rw [hp t le_rfl]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < t := Finset.mem_range.1 hk
  unfold kp_term
  rw [hp k hk'.le, h k hk']

theorem kp_back_succ (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) (t : ℕ) :
    kp_back a₀ ω (t + 1) = (ω 0).2 + (ω 0).1 * kp_back a₀ (kp_shift ω) t := by
  unfold kp_back
  rw [Finset.sum_range_succ', Finset.prod_range_succ']
  simp_rw [kp_term_succ, kp_term_zero]
  rw [← Finset.mul_sum]
  simp only [kp_shift]
  ring

/-- The forward iterate is the backward iterate of the time-reversed shocks. -/
theorem kp_iter_eq_back (a₀ : ℝ) (ω : ℕ → ℝ × ℝ) (t : ℕ) :
    kp_iter a₀ ω t = kp_back a₀ (fun j => ω (kp_rev t j)) t := by
  induction t with
  | zero => simp [kp_iter, kp_back]
  | succ t ih =>
    have h0 : kp_rev (t + 1) 0 = t := by simp [kp_rev]
    have hc : kp_back a₀ (kp_shift fun j => ω (kp_rev (t + 1) j)) t =
        kp_back a₀ (fun j => ω (kp_rev t j)) t := by
      refine kp_back_congr fun j hj => ?_
      simp only [kp_shift, kp_rev]
      congr 1
      split_ifs <;> omega
    rw [kp_iter, ih, kp_back_succ, h0, hc]
    ring

theorem kp_back_measurable (a₀ : ℝ) (t : ℕ) : Measurable fun ω => kp_back a₀ ω t := by
  unfold kp_back kp_term
  fun_prop

/-- The forward and backward iterates have the same law. -/
theorem kp_iter_identDistrib (a₀ : ℝ) (t : ℕ) :
    IdentDistrib (fun ω => kp_iter a₀ ω t) (fun ω => kp_back a₀ ω t) (kp_P ν) (kp_P ν) := by
  have e : (fun ω => kp_iter a₀ ω t) =
      (fun ω => kp_back a₀ ω t) ∘ (fun (ω : ℕ → ℝ × ℝ) j => ω (kp_rev t j)) :=
    funext fun ω => kp_iter_eq_back a₀ ω t
  rw [e]
  refine ⟨((kp_back_measurable a₀ t).comp (kp_rev_mp (ν := ν) t).measurable).aemeasurable,
    (kp_back_measurable a₀ t).aemeasurable, ?_⟩
  rw [← Measure.map_map (kp_back_measurable a₀ t) (kp_rev_mp (ν := ν) t).measurable,
    (kp_rev_mp t).map_eq]

/-- `s₀⋯s_{t−1} → 0` almost surely when `E|s|^κ < 1`. -/
theorem kp_prod_tendsto_zero {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1) :
    ∀ᵐ ω ∂kp_P ν, Tendsto (fun t => ∏ j ∈ Finset.range t, (ω j).1) atTop (𝓝 0) := by
  have hmeas : ∀ t, Measurable fun ω : ℕ → ℝ × ℝ => ‖∏ j ∈ Finset.range t, (ω j).1‖ₑ ^ κ :=
    fun t => by fun_prop
  have hint : ∫⁻ ω, ∑' t, ‖∏ j ∈ Finset.range t, (ω j).1‖ₑ ^ κ ∂kp_P ν ≠ ⊤ := by
    rw [lintegral_tsum fun t => (hmeas t).aemeasurable]
    have e : ∀ t, ∫⁻ ω, ‖∏ j ∈ Finset.range t, (ω j).1‖ₑ ^ κ ∂kp_P ν =
        (∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) ^ t := by
      intro t
      have := kp_lintegral_prod_mul (ν := ν) (f := fun x => ‖x.1‖ₑ ^ κ) (g := fun _ => 1)
        (by fun_prop) measurable_const t
      simpa [kp_enorm_prod_rpow _ _ hκ.le] using this
    simp_rw [e, ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ).ne'
  filter_upwards [ae_lt_top' (Measurable.tsum hmeas).aemeasurable hint] with ω hω
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 := ((ENNReal.continuous_rpow_const (y := 1 / κ)).tendsto 0).comp h1
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h2
  refine tendsto_zero_iff_enorm_tendsto_zero.2 ?_
  refine h2.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hκ.ne', ENNReal.rpow_one]

/-- **AKMM, p. 651 (beyond the text): the backward iterates converge almost surely to `A`.** -/
theorem kp_back_tendsto_ae (a₀ : ℝ) {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) :
    ∀ᵐ ω ∂kp_P ν, Tendsto (fun t => kp_back a₀ ω t) atTop (𝓝 (kp_perp ω)) := by
  filter_upwards [kp_perp_hasSum_ae hκ hρ hm, kp_prod_tendsto_zero hκ hρ] with ω h1 h2
  simpa [kp_back] using h1.tendsto_sum_nat.add (h2.mul_const a₀)

/-- **AKMM, p. 651 (beyond the text, corrections 3): the law of `aₜ` converges weakly to the
law of `A` from any `a₀`.** If `E|s|^κ < 1` and `E|ε|^κ < ∞` for some `κ > 0`, then for every
bounded continuous `f`, `E f(aₜ) → E f(A)`. (Convergence in distribution, not in probability.) -/
theorem kp_iter_tendsto_law (a₀ : ℝ) {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun t => ∫ ω, f (kp_iter a₀ ω t) ∂kp_P ν) atTop
      (𝓝 (∫ ω, f (kp_perp ω) ∂kp_P ν)) := by
  have e : ∀ t, ∫ ω, f (kp_iter a₀ ω t) ∂kp_P ν = ∫ ω, f (kp_back a₀ ω t) ∂kp_P ν :=
    fun t => ((kp_iter_identDistrib (ν := ν) a₀ t).comp f.continuous.measurable).integral_eq
  simp_rw [e]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun t =>
    (f.continuous.measurable.comp (kp_back_measurable a₀ t)).aestronglyMeasurable)
    (integrable_const _) (fun t => ae_of_all _ fun ω => f.norm_coe_le_norm _) ?_
  filter_upwards [kp_back_tendsto_ae a₀ hκ hρ hm] with ω hω
  exact (f.continuous.tendsto _).comp hω

/-! ### Moment bounds that fix the tail index -/

/-- **AKMM, p. 651 (beyond the text): moments of `A` of order `κ` are finite when
`E|s|^κ < 1`.** If `E|s|^κ < 1` and `E|ε|^κ < ∞` then `E|A|^κ < ∞` (subadditivity of `x^κ` for
`κ < 1`, Minkowski for `κ ≥ 1`). -/
theorem kp_lintegral_perp_lt_top {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun _ => ENNReal.rpow_le_rpow enorm_tsum_le_tsum_enorm hκ.le)
    (kp_lintegral_abs_lt_top hκ hρ hm)

/-- **AKMM, p. 651 (beyond the text): Pareto-type tail bound.** Under the hypotheses of
`kp_lintegral_perp_lt_top`, `P(|A| ≥ a) ≤ C_κ a^{−κ}` for all `a > 0` (Markov). -/
theorem kp_tail_bound {κ : ℝ} (hκ : 0 < κ) (hρ : ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a →
      kp_P ν {ω | a ≤ |kp_perp ω|} ≤ C * ENNReal.ofReal (a ^ (-κ)) := by
  refine ⟨∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν, (kp_lintegral_perp_lt_top hκ hρ hm).ne,
    fun a ha => ?_⟩
  have hM := mul_meas_ge_le_lintegral₀ (μ := kp_P ν)
    (kp_perp_measurable.enorm.pow_const κ).aemeasurable (ENNReal.ofReal (a ^ κ))
  have hset : {ω | a ≤ |kp_perp ω|} ⊆
      {ω | ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ} := by
    intro ω (hω : a ≤ |kp_perp ω|)
    change ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hκ.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha.le hω hκ.le)
  calc kp_P ν {ω | a ≤ |kp_perp ω|}
      ≤ kp_P ν {ω | ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ} := measure_mono hset
    _ = ENNReal.ofReal (a ^ (-κ)) * (ENNReal.ofReal (a ^ κ) *
          kp_P ν {ω | ENNReal.ofReal (a ^ κ) ≤ ‖kp_perp ω‖ₑ ^ κ}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add ha,
          neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (a ^ (-κ)) * ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν := by gcongr
    _ = _ := mul_comm _ _

/-- **AKMM, p. 651 (beyond the text): moments above the tail index are infinite.** If
`E|s|^κ > 1` and `E|ε|^κ > 0`, then `E(Σₖ |s₀⋯s_{k−1} εₖ|)^κ = ∞`: the series `Σ` satisfies
`Σ ≥ |s₀| Σ′` with `Σ′ =ᵈ Σ` independent of `s₀`, and `E Σ^κ ≥ E|ε|^κ > 0`, so a finite
`E Σ^κ` would give `E Σ^κ ≥ E|s|^κ E Σ^κ > E Σ^κ`. -/
theorem kp_lintegral_abs_eq_top {κ : ℝ} (hκ : 0 < κ) (hρ : 1 < ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ 0) : ∫⁻ ω, kp_abs ω ^ κ ∂kp_P ν = ⊤ := by
  set I := ∫⁻ ω, kp_abs ω ^ κ ∂kp_P ν with hI
  have hge : (∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν) * I ≤ I := by
    have h := kp_lintegral_head_shift (ν := ν) (F := fun x => ‖x.1‖ₑ ^ κ)
      (G := fun ω => kp_abs ω ^ κ) (by fun_prop) (kp_abs_measurable.pow_const κ)
    rw [hI, ← h]
    refine lintegral_mono fun ω => ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hκ.le]
    refine ENNReal.rpow_le_rpow ?_ hκ.le
    rw [kp_abs_eq ω]
    exact le_add_self
  have hpos : I ≠ 0 := by
    have h1 : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≤ I := by
      rw [← (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).lintegral_comp
        (by fun_prop : Measurable fun x : ℝ × ℝ => ‖x.2‖ₑ ^ κ)]
      refine lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ hκ.le
      rw [kp_abs_eq ω]
      exact le_self_add
    exact (lt_of_lt_of_le (pos_iff_ne_zero.2 hm) h1).ne'
  by_contra htop
  have := ENNReal.mul_lt_mul_right hpos htop hρ
  rw [mul_one, mul_comm] at this
  exact absurd hge (not_le.2 this)

/-- With `s, ε ≥ 0` and the series a.s. finite, `|A| = Σₖ s₀⋯s_{k−1} εₖ` almost surely. -/
theorem kp_enorm_perp_ae (hs : ∀ᵐ x ∂ν, 0 ≤ x.1) (he : ∀ᵐ x ∂ν, 0 ≤ x.2)
    (hfin : ∀ᵐ ω ∂kp_P ν, kp_abs ω < ⊤) : ∀ᵐ ω ∂kp_P ν, ‖kp_perp ω‖ₑ = kp_abs ω := by
  have hall : ∀ᵐ ω ∂kp_P ν, ∀ j, 0 ≤ (ω j).1 ∧ 0 ≤ (ω j).2 := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j).quasiMeasurePreserving.ae
      (hs.and he)
  filter_upwards [hall, hfin] with ω hω hf
  have hnn : ∀ k, 0 ≤ kp_term ω k := fun k =>
    mul_nonneg (Finset.prod_nonneg fun j _ => (hω j).1) (hω k).2
  have hsum := kp_hasSum hf.ne
  rw [kp_abs, kp_perp, Real.enorm_eq_ofReal_abs, abs_of_nonneg (tsum_nonneg hnn),
    ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable]
  congr 1
  ext k
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn k)]

/-- **AKMM, p. 651 (beyond the text): `E A^κ = ∞` above the tail index.** If `s, ε ≥ 0`, the
series converges a.s. (some `κ₀ > 0` with `E s^{κ₀} < 1`, `E ε^{κ₀} < ∞`), `E s^κ > 1` and
`E ε^κ > 0`, then `E A^κ = ∞`. -/
theorem kp_lintegral_perp_eq_top {κ κ₀ : ℝ} (hκ : 0 < κ) (hρ : 1 < ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν)
    (hm : ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ 0) (hs : ∀ᵐ x ∂ν, 0 ≤ x.1) (he : ∀ᵐ x ∂ν, 0 ≤ x.2)
    (hκ₀ : 0 < κ₀) (hρ₀ : ∫⁻ x, ‖x.1‖ₑ ^ κ₀ ∂ν < 1) (hm₀ : ∫⁻ x, ‖x.2‖ₑ ^ κ₀ ∂ν ≠ ⊤) :
    ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν = ⊤ := by
  have h : (fun ω => ‖kp_perp ω‖ₑ ^ κ) =ᵐ[kp_P ν] fun ω => kp_abs ω ^ κ := by
    filter_upwards [kp_enorm_perp_ae hs he (kp_abs_ae_lt_top hκ₀ hρ₀ hm₀)] with ω hω
    rw [hω]
  rw [lintegral_congr_ae h]
  exact kp_lintegral_abs_eq_top hκ hρ hm

omit [IsProbabilityMeasure ν] in
/-- If `ε` is not almost surely `0`, `E|ε|^κ > 0`. -/
theorem kp_moment_ne_zero {κ : ℝ} (hκ : 0 < κ) (hε : ¬ ∀ᵐ x ∂ν, x.2 = 0) :
    ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ 0 := by
  intro h0
  rw [lintegral_eq_zero_iff (by fun_prop)] at h0
  refine hε (h0.mono fun x hx => ?_)
  have hx' : ‖x.2‖ₑ ^ κ = 0 := hx
  rcases ENNReal.rpow_eq_zero_iff.1 hx' with h | h
  · exact enorm_eq_zero.1 h.1
  · exact absurd h.2 (not_lt.2 hκ.le)

/-- **AKMM, p. 651 (beyond the text): the tail index of `A` is `ζ` in the moment sense.**
Suppose `s, ε ≥ 0`, `ε` not a.s. `0`, and `ζ > 0` is such that `E s^κ < 1` and `E ε^κ < ∞` for
`0 < κ < ζ` and `E s^κ > 1` for `κ > ζ` (as for the root of `E s^ζ = 1`, `kp_moment_root`).
Then `E A^κ < ∞` for `0 < κ < ζ`, `E A^κ = ∞` for `κ > ζ`, and
`sup {κ > 0 : E A^κ < ∞} = ζ`: the exponent a Pareto tail `P(A > a) ∝ a^{−ζ}` would have. -/
theorem kp_tail_index {ζ : ℝ} (hζ : 0 < ζ)
    (hlow : ∀ κ, 0 < κ → κ < ζ → ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν < 1 ∧ ∫⁻ x, ‖x.2‖ₑ ^ κ ∂ν ≠ ⊤)
    (hhigh : ∀ κ, ζ < κ → 1 < ∫⁻ x, ‖x.1‖ₑ ^ κ ∂ν)
    (hs : ∀ᵐ x ∂ν, 0 ≤ x.1) (he : ∀ᵐ x ∂ν, 0 ≤ x.2) (hε : ¬ ∀ᵐ x ∂ν, x.2 = 0) :
    (∀ κ, 0 < κ → κ < ζ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤) ∧
      (∀ κ, ζ < κ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν = ⊤) ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤} = ζ := by
  have h1 : ∀ κ, 0 < κ → κ < ζ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν < ⊤ := fun κ hκ hκζ =>
    kp_lintegral_perp_lt_top hκ (hlow κ hκ hκζ).1 (hlow κ hκ hκζ).2
  have h2 : ∀ κ, ζ < κ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P ν = ⊤ := by
    intro κ hκ
    have hκ0 : 0 < κ := hζ.trans hκ
    have h0 := hlow (ζ / 2) (by positivity) (by linarith)
    exact kp_lintegral_perp_eq_top hκ0 (hhigh κ hκ) (kp_moment_ne_zero hκ0 hε) hs he
      (by positivity : (0 : ℝ) < ζ / 2) h0.1 h0.2
  refine ⟨h1, h2, ?_⟩
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨ζ / 2, by positivity,
    h1 _ (by positivity) (by linarith)⟩ (fun κ hκ => ?_) (fun w hw => ?_)
  · by_contra hlt
    exact (h2 κ (not_le.1 hlt) ▸ hκ.2).ne rfl
  · refine ⟨(max w 0 + ζ) / 2, ⟨by positivity, h1 _ (by positivity) ?_⟩, ?_⟩
    · have : max w 0 < ζ := max_lt hw hζ
      linarith
    · have : w ≤ max w 0 := le_max_left _ _
      have : max w 0 < ζ := max_lt hw hζ
      linarith

/-! ### Finitely supported shocks: the root `ζ` of `E s^ζ = 1` -/

/-- **AKMM, fn 31: the moment function crosses `1` at its root.** For a finitely supported
`s > 0` (probabilities `pₖ > 0`) not identically `1`, if `ζ > 0` solves `E s^ζ = 1` then
`E s^κ < 1` for `0 < κ < ζ` and `E s^κ > 1` for `κ > ζ` (strict convexity of
`κ ↦ Σₖ pₖ sₖ^κ`, which is `1` at `0` and at `ζ`). -/
theorem kp_moment_root {ι : Type*} [Fintype ι] {p s : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (k₀ : ι) (hk₀ : s k₀ ≠ 1) {ζ : ℝ} (hζ : 0 < ζ)
    (hζ1 : ∑ k, p k * s k ^ ζ = 1) :
    (∀ κ, 0 < κ → κ < ζ → ∑ k, p k * s k ^ κ < 1) ∧ (∀ κ, ζ < κ → 1 < ∑ k, p k * s k ^ κ) := by
  have hpt : ∀ k, ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      s k ^ (t * z) ≤ (1 - t) + t * s k ^ z ∧
        (s k ≠ 1 → s k ^ (t * z) < (1 - t) + t * s k ^ z) := by
    intro k z t hz ht ht1
    have e1 : Real.log (s k) * (t * z) = (1 - t) • (0 : ℝ) + t • (Real.log (s k) * z) := by
      simp only [smul_eq_mul]
      ring
    rw [Real.rpow_def_of_pos (hs k), Real.rpow_def_of_pos (hs k), e1]
    refine ⟨?_, fun hne => ?_⟩
    · have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        (by linarith : (0 : ℝ) ≤ 1 - t) ht.le (by ring)
      simpa using this
    · have hl : Real.log (s k) ≠ 0 := fun h0 =>
        hne (Real.eq_one_of_pos_of_log_eq_zero (hs k) h0)
      have hne' : (0 : ℝ) ≠ Real.log (s k) * z := (mul_ne_zero hl hz.ne').symm
      have := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log (s k) * z))
        hne' (by linarith : (0 : ℝ) < 1 - t) ht (by ring)
      simpa using this
  have hmix : ∀ z t : ℝ, 0 < z → 0 < t → t < 1 →
      ∑ k, p k * s k ^ (t * z) < (1 - t) + t * ∑ k, p k * s k ^ z := by
    intro z t hz ht ht1
    have h1 : (1 - t) + t * ∑ k, p k * s k ^ z = ∑ k, p k * ((1 - t) + t * s k ^ z) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1]
    apply Finset.sum_lt_sum
    · exact fun k _ => mul_le_mul_of_nonneg_left (hpt k z t hz ht ht1).1 (hp k).le
    · exact ⟨k₀, Finset.mem_univ _,
        mul_lt_mul_of_pos_left ((hpt k₀ z t hz ht ht1).2 hk₀) (hp k₀)⟩
  refine ⟨fun κ hκ hκζ => ?_, fun κ hκ => ?_⟩
  · have := hmix ζ (κ / ζ) hζ (div_pos hκ hζ) ((div_lt_one hζ).2 hκζ)
    rw [show κ / ζ * ζ = κ by field_simp, hζ1] at this
    linarith
  · have hκ0 : 0 < κ := hζ.trans hκ
    have := hmix κ (ζ / κ) hκ0 (div_pos hζ hκ0) ((div_lt_one hκ0).2 hκ)
    rw [show ζ / κ * κ = ζ by field_simp, hζ1] at this
    have h2 : 0 < ζ / κ := div_pos hζ hκ0
    nlinarith

/-- The law of a finitely supported pair `(s, ε)`: `(sₖ, eₖ)` with probability `pₖ`. -/
noncomputable def kp_finite {ι : Type*} [Fintype ι] (p s e : ι → ℝ) : Measure (ℝ × ℝ) :=
  ∑ k, ENNReal.ofReal (p k) • Measure.dirac (s k, e k)

theorem kp_finite_lintegral {ι : Type*} [Fintype ι] (p s e : ι → ℝ) (g : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂kp_finite p s e = ∑ k, ENNReal.ofReal (p k) * g (s k, e k) := by
  simp [kp_finite, lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac]

theorem kp_finite_isProb {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (s e : ι → ℝ) : IsProbabilityMeasure (kp_finite p s e) := by
  constructor
  have h := kp_finite_lintegral p s e (fun _ => 1)
  rw [lintegral_one] at h
  rw [h]
  simp only [mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => (hp k).le, hp1, ENNReal.ofReal_one]

theorem kp_finite_ae {ι : Type*} [Fintype ι] {p s e : ι → ℝ} {Q : ℝ × ℝ → Prop}
    (hQ : MeasurableSet {x | Q x}) (h : ∀ k, Q (s k, e k)) : ∀ᵐ x ∂kp_finite p s e, Q x := by
  rw [ae_iff]
  have hc : MeasurableSet {x | ¬ Q x} := hQ.compl
  simp only [kp_finite, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hc, smul_eq_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [Set.indicator, h k]

/-- **AKMM, p. 651 and fn 31 (beyond the text): a finitely supported instance.** Let `(s, ε)` take
the values `(sₖ, eₖ)` with probabilities `pₖ > 0`, `sₖ > 0` not all `1`, `eₖ ≥ 0` not all `0`, and
let `ζ > 0` solve `E s^ζ = 1` (Kesten's moment condition, fn 31). Then the tail index of the
stationary `A` is exactly `ζ`: `E A^κ < ∞` for `0 < κ < ζ`, `E A^κ = ∞` for `κ > ζ`, and
`sup {κ > 0 : E A^κ < ∞} = ζ`. -/
theorem kp_finite_tail_index {ι : Type*} [Fintype ι] {p s e : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (k₀ : ι) (hk₀ : s k₀ ≠ 1) (he : ∀ k, 0 ≤ e k)
    (k₁ : ι) (hk₁ : 0 < e k₁) {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ∑ k, p k * s k ^ ζ = 1) :
    (∀ κ, 0 < κ → κ < ζ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) < ⊤) ∧
      (∀ κ, ζ < κ → ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) = ⊤) ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) < ⊤} = ζ := by
  have := kp_finite_isProb hp hp1 s e
  have hρ : ∀ κ : ℝ, 0 ≤ κ → ∫⁻ x, ‖x.1‖ₑ ^ κ ∂kp_finite p s e =
      ENNReal.ofReal (∑ k, p k * s k ^ κ) := by
    intro κ hκ
    rw [kp_finite_lintegral, ENNReal.ofReal_sum_of_nonneg fun k _ =>
      mul_nonneg (hp k).le (Real.rpow_nonneg (hs k).le _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_mul (hp k).le, Real.enorm_eq_ofReal_abs, abs_of_pos (hs k),
      ENNReal.ofReal_rpow_of_nonneg (hs k).le hκ]
  have hm : ∀ κ : ℝ, 0 ≤ κ → ∫⁻ x, ‖x.2‖ₑ ^ κ ∂kp_finite p s e ≠ ⊤ := by
    intro κ hκ
    rw [kp_finite_lintegral]
    exact ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hκ enorm_ne_top)
  obtain ⟨hlo, hhi⟩ := kp_moment_root hp hp1 hs k₀ hk₀ hζ hζ1
  refine kp_tail_index hζ (fun κ hκ hκζ => ⟨?_, hm κ hκ.le⟩) (fun κ hκ => ?_)
    (kp_finite_ae (measurableSet_le measurable_const measurable_fst) fun k => (hs k).le)
    (kp_finite_ae (measurableSet_le measurable_const measurable_snd) he) ?_
  · rw [hρ κ hκ.le, ENNReal.ofReal_lt_one]
    exact hlo κ hκ hκζ
  · rw [hρ κ (hζ.trans hκ).le, ENNReal.one_lt_ofReal]
    exact hhi κ hκ
  · intro h0
    rw [ae_iff] at h0
    have hpos : 0 < kp_finite p s e {x | ¬ x.2 = 0} := by
      have hc : MeasurableSet {x : ℝ × ℝ | ¬ x.2 = 0} :=
        (measurableSet_eq_fun measurable_snd measurable_const).compl
      simp only [kp_finite, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hc, smul_eq_mul]
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ k₁))
      simp [Set.indicator, hk₁.ne', hp k₁]
    exact hpos.ne' h0

/-- **AKMM, p. 651 (beyond the text): a two-point example.** `s ∈ {1/2, 3/2}` with
probability `1/2` each and `ε = 1`: Kesten's hypotheses hold (`E log s < 0`, `P(s > 1) > 0`),
`ζ = 1` solves `E s^ζ = 1`, and the tail index of `A` is exactly `1`. -/
theorem kp_two_point :
    (∑ k : Fin 2, (1 / 2 : ℝ) * Real.log (![1 / 2, 3 / 2] k) < 0) ∧ (1 : ℝ) < ![1 / 2, 3 / 2] 1 ∧
      ∑ k : Fin 2, (1 / 2 : ℝ) * ![1 / 2, 3 / 2] k ^ (1 : ℝ) = 1 ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P
        (kp_finite (fun _ : Fin 2 => 1 / 2) ![1 / 2, 3 / 2] fun _ => 1) < ⊤} = 1 := by
  have hroot : ∑ k : Fin 2, (1 / 2 : ℝ) * ![1 / 2, 3 / 2] k ^ (1 : ℝ) = 1 := by
    simp [Fin.sum_univ_two]
    norm_num
  refine ⟨?_, by norm_num, hroot, ?_⟩
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← mul_add, ← Real.log_mul (by norm_num) (by norm_num)]
    have : Real.log (1 / 2 * (3 / 2)) < 0 := Real.log_neg (by norm_num) (by norm_num)
    linarith
  · exact (kp_finite_tail_index (fun _ => by norm_num) (by simp)
      (fun k => by fin_cases k <;> norm_num) 0 (by norm_num) (fun _ => zero_le_one) 0 one_pos
      one_pos hroot).2.2

/-- **AKMM, p. 651 and fn 31 (beyond the text): the tail index is the root of
`ke_moment_exists`.** For finitely supported `(s, ε)` with `pₖ > 0`, `sₖ > 0`, `E log s < 0`,
some `sₖ > 1`, and `eₖ ≥ 0` not all `0`, the root `ζ > 0` of `E s^ζ = 1` given by
`ke_moment_exists` is the tail index of `A`: `sup {κ > 0 : E A^κ < ∞} = ζ`. -/
theorem kp_finite_tail_index_ke {ι : Type*} [Fintype ι] {p s e : ι → ℝ} (hp : ∀ k, 0 < p k)
    (hp1 : ∑ k, p k = 1) (hs : ∀ k, 0 < s k) (hlog : ∑ k, p k * Real.log (s k) < 0) (k₁ : ι)
    (hk₁ : 1 < s k₁) (he : ∀ k, 0 ≤ e k) (k₂ : ι) (hk₂ : 0 < e k₂) :
    ∃ ζ, 0 < ζ ∧ ke_moment p s ζ = 1 ∧
      sSup {κ : ℝ | 0 < κ ∧ ∫⁻ ω, ‖kp_perp ω‖ₑ ^ κ ∂kp_P (kp_finite p s e) < ⊤} = ζ := by
  obtain ⟨ζ, hζ, hζ1⟩ := ke_moment_exists hp hp1 hs hlog k₁ hk₁
  exact ⟨ζ, hζ, hζ1, (kp_finite_tail_index hp hp1 hs k₁ hk₁.ne' he k₂ hk₂ hζ hζ1).2.2⟩

/-- AKMM, fn 31: in the two-point example of `kp_two_point` the root of `ke_moment_exists` is
`ζ = 1` (`ke_moment_unique`). -/
theorem kp_two_point_ke {ζ : ℝ} (hζ : 0 < ζ)
    (hζ1 : ke_moment (fun _ : Fin 2 => (1 / 2 : ℝ)) ![1 / 2, 3 / 2] ζ = 1) : ζ = 1 :=
  ke_moment_unique (fun _ => by norm_num) (by simp) (fun k => by fin_cases k <;> norm_num) 0
    (by norm_num) hζ one_pos hζ1 kp_two_point.2.2.1

end AKMM.Inequality

set_option linter.style.longLine false
#print axioms AKMM.Inequality.fs_partial_homog
#print axioms AKMM.Inequality.fs_capital_share_homog
#print axioms AKMM.Inequality.fs_ces
#print axioms AKMM.Inequality.fs_ces_hasDerivAt
#print axioms AKMM.Inequality.fs_ces_capital_share
#print axioms AKMM.Inequality.fs_share
#print axioms AKMM.Inequality.fs_share_strictAntiOn
#print axioms AKMM.Inequality.fs_share_strictMonoOn
#print axioms AKMM.Inequality.fs_theta_pos_iff
#print axioms AKMM.Inequality.fs_cd_capital_share
#print axioms AKMM.Inequality.fs_bgp_ky
#print axioms AKMM.Inequality.fs_steady_ky
#print axioms AKMM.Inequality.fs_ky_strictMonoOn
#print axioms AKMM.Inequality.fs_ky_below
#print axioms AKMM.Inequality.fs_ky_above
#print axioms AKMM.Inequality.fs_ces_symm
#print axioms AKMM.Inequality.wi_ces_hasDerivAt
#print axioms AKMM.Inequality.km_premium
#print axioms AKMM.Inequality.km_premium_eq
#print axioms AKMM.Inequality.km_log_premium
#print axioms AKMM.Inequality.km_premium_strictAnti_supply
#print axioms AKMM.Inequality.km_sbtc_strictMono_iff
#print axioms AKMM.Inequality.km_cd_premium
#print axioms AKMM.Inequality.km_identify
#print axioms AKMM.Inequality.dt_obj
#print axioms AKMM.Inequality.dt_con
#print axioms AKMM.Inequality.dt_term_le
#print axioms AKMM.Inequality.dt_optimal
#print axioms AKMM.Inequality.dt_ratio
#print axioms AKMM.Inequality.dt_foc_iff_ratio
#print axioms AKMM.Inequality.dt_exists
#print axioms AKMM.Inequality.dt_maximiser_ratio
#print axioms AKMM.Inequality.dt_printed_ratio_iff
#print axioms AKMM.Inequality.dt_ratio_strictMono
#print axioms AKMM.Inequality.dt_wage_ratio
#print axioms AKMM.Inequality.dt_premium_closed
#print axioms AKMM.Inequality.dt_log_premium
#print axioms AKMM.Inequality.dt_exponent_pos_iff
#print axioms AKMM.Inequality.dt_rho_gt_two
#print axioms AKMM.Inequality.cs_ex1_wages
#print axioms AKMM.Inequality.cs_ex1_premium_strictMono
#print axioms AKMM.Inequality.cs_ex2_wu
#print axioms AKMM.Inequality.cs_ex2_wu_strictAnti
#print axioms AKMM.Inequality.cs_nest_wu
#print axioms AKMM.Inequality.cs_nest_wu_monotone
#print axioms AKMM.Inequality.cs_ces_nest_premium
#print axioms AKMM.Inequality.cs_ces_nest_strictMono
#print axioms AKMM.Inequality.dy_Optimal
#print axioms AKMM.Inequality.dy_plan_iff
#print axioms AKMM.Inequality.dy_constant_optimal
#print axioms AKMM.Inequality.dy_indeterminacy
#print axioms AKMM.Inequality.dy_log_tangent
#print axioms AKMM.Inequality.dy_indeterminacy_example
#print axioms AKMM.Inequality.dy_mpc
#print axioms AKMM.Inequality.ol_budget_iff
#print axioms AKMM.Inequality.ol_IsIndirect
#print axioms AKMM.Inequality.ol_isIndirect_prod
#print axioms AKMM.Inequality.ol_bellman_reduction
#print axioms AKMM.Inequality.ol_dynastic_utility
#print axioms AKMM.Inequality.ol_indeterminacy
#print axioms AKMM.Inequality.ol_example
#print axioms AKMM.Inequality.hd_constant_beta
#print axioms AKMM.Inequality.hd_unique_beta
#print axioms AKMM.Inequality.hd_strictAnti
#print axioms AKMM.Inequality.hd_tendsto_zero
#print axioms AKMM.Inequality.hd_assets_limit
#print axioms AKMM.Inequality.hd_strictMono
#print axioms AKMM.Inequality.rh_lower_return_iff
#print axioms AKMM.Inequality.pt_gross
#print axioms AKMM.Inequality.pt_hasDerivAt
#print axioms AKMM.Inequality.pt_printed_iff
#print axioms AKMM.Inequality.pt_printed_counterexample
#print axioms AKMM.Inequality.pt_steady_euler
#print axioms AKMM.Inequality.pt_steady_euler_example
#print axioms AKMM.Inequality.pt_g_strictMonoOn
#print axioms AKMM.Inequality.pt_unique
#print axioms AKMM.Inequality.pt_equal_wealth
#print axioms AKMM.Inequality.pt_proportional
#print axioms AKMM.Inequality.ta_q_eq_beta
#print axioms AKMM.Inequality.ta_endow
#print axioms AKMM.Inequality.ta_assets
#print axioms AKMM.Inequality.ta_footnote_26
#print axioms AKMM.Inequality.ta_footnote_26_richer
#print axioms AKMM.Inequality.ta_binding_alloc
#print axioms AKMM.Inequality.ta_binding_kkt
#print axioms AKMM.Inequality.ta_h
#print axioms AKMM.Inequality.ta_binding_strictMono
#print axioms AKMM.Inequality.ta_binding_unique
#print axioms AKMM.Inequality.ta_binding_exists
#print axioms AKMM.Inequality.hu_autarky_clearing
#print axioms AKMM.Inequality.hu_value
#print axioms AKMM.Inequality.hu_qstar
#print axioms AKMM.Inequality.hu_kkt_iff
#print axioms AKMM.Inequality.hu_price_iff
#print axioms AKMM.Inequality.hu_rate_below_discount
#print axioms AKMM.Inequality.ui_determinate
#print axioms AKMM.Inequality.ke_moment
#print axioms AKMM.Inequality.ke_moment_zero
#print axioms AKMM.Inequality.ke_moment_hasDerivAt
#print axioms AKMM.Inequality.ke_moment_unique
#print axioms AKMM.Inequality.ke_moment_exists
#print axioms AKMM.Inequality.gi_gini_eq_ratio
#print axioms AKMM.Inequality.gi_lorenz_le_diag
#print axioms AKMM.Inequality.gi_lorenz_convex
#print axioms AKMM.Inequality.gi_lorenz_concentrated
#print axioms AKMM.Inequality.gi_gini_mem_Icc
#print axioms AKMM.Inequality.gi_gini_equal
#print axioms AKMM.Inequality.gi_gini_eq_zero_iff
#print axioms AKMM.Inequality.gi_gini_concentrated_tendsto
#print axioms AKMM.Inequality.pa_ccdf
#print axioms AKMM.Inequality.pa_log_ccdf
#print axioms AKMM.Inequality.pa_log_ccdf_strictAnti
#print axioms AKMM.Inequality.ed_educates
#print axioms AKMM.Inequality.ed_educates_example
#print axioms AKMM.Inequality.ed_unconstrained
#print axioms AKMM.Inequality.ed_fraction
#print axioms AKMM.Inequality.ed_wealth_matters
#print axioms AKMM.Inequality.mpc_binding
#print axioms AKMM.Inequality.tank_mpc
#print axioms AKMM.Inequality.ext_log_output
#print axioms AKMM.Inequality.kp_P
#print axioms AKMM.Inequality.kp_shift
#print axioms AKMM.Inequality.kp_shift_measurable
#print axioms AKMM.Inequality.kp_shift_mp
#print axioms AKMM.Inequality.kp_indep_head_shift
#print axioms AKMM.Inequality.kp_lintegral_head_shift
#print axioms AKMM.Inequality.kp_lintegral_prod_mul
#print axioms AKMM.Inequality.kp_rpow_sum_le_sum_rpow
#print axioms AKMM.Inequality.kp_lintegral_sum_rpow_le
#print axioms AKMM.Inequality.kp_lintegral_tsum_rpow_le
#print axioms AKMM.Inequality.kp_term
#print axioms AKMM.Inequality.kp_abs
#print axioms AKMM.Inequality.kp_perp
#print axioms AKMM.Inequality.kp_term_measurable
#print axioms AKMM.Inequality.kp_abs_measurable
#print axioms AKMM.Inequality.kp_perp_measurable
#print axioms AKMM.Inequality.kp_hasSum
#print axioms AKMM.Inequality.kp_enorm_prod_rpow
#print axioms AKMM.Inequality.kp_enorm_term_rpow
#print axioms AKMM.Inequality.kp_lintegral_term
#print axioms AKMM.Inequality.kp_lintegral_abs_lt_top
#print axioms AKMM.Inequality.kp_abs_ae_lt_top
#print axioms AKMM.Inequality.kp_perp_hasSum_ae
#print axioms AKMM.Inequality.kp_perp_tendsto_Lp
#print axioms AKMM.Inequality.kp_term_zero
#print axioms AKMM.Inequality.kp_term_succ
#print axioms AKMM.Inequality.kp_abs_eq
#print axioms AKMM.Inequality.kp_fixed_point
#print axioms AKMM.Inequality.kp_iter
#print axioms AKMM.Inequality.kp_back
#print axioms AKMM.Inequality.kp_rev
#print axioms AKMM.Inequality.kp_rev_injective
#print axioms AKMM.Inequality.kp_rev_mp
#print axioms AKMM.Inequality.kp_back_congr
#print axioms AKMM.Inequality.kp_back_succ
#print axioms AKMM.Inequality.kp_iter_eq_back
#print axioms AKMM.Inequality.kp_back_measurable
#print axioms AKMM.Inequality.kp_iter_identDistrib
#print axioms AKMM.Inequality.kp_prod_tendsto_zero
#print axioms AKMM.Inequality.kp_back_tendsto_ae
#print axioms AKMM.Inequality.kp_iter_tendsto_law
#print axioms AKMM.Inequality.kp_lintegral_perp_lt_top
#print axioms AKMM.Inequality.kp_tail_bound
#print axioms AKMM.Inequality.kp_lintegral_abs_eq_top
#print axioms AKMM.Inequality.kp_enorm_perp_ae
#print axioms AKMM.Inequality.kp_lintegral_perp_eq_top
#print axioms AKMM.Inequality.kp_moment_ne_zero
#print axioms AKMM.Inequality.kp_tail_index
#print axioms AKMM.Inequality.kp_moment_root
#print axioms AKMM.Inequality.kp_finite
#print axioms AKMM.Inequality.kp_finite_lintegral
#print axioms AKMM.Inequality.kp_finite_isProb
#print axioms AKMM.Inequality.kp_finite_ae
#print axioms AKMM.Inequality.kp_finite_tail_index
#print axioms AKMM.Inequality.kp_two_point
#print axioms AKMM.Inequality.kp_finite_tail_index_ke
#print axioms AKMM.Inequality.kp_two_point_ke
