/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.Basics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Factor-augmenting technology: measurement and directed choice

AKMM, §25.5.3 (pp. 779–782).

* **The CES production function** (p. 779)
  `y = [(1 − ν)X^θ + ν Z^θ]^{1/θ}`, `X = Ak^αl^{1−α}`, `Z = A_e e`, with `θ = (ε − 1)/ε ≠ 0`
  (`cesY`). Differentiating, the cost shares of a competitive firm are
  `e^{share} = ν(A_e e/y)^θ` (`ces_share_e`) and `l^{share} = (1 − α)(1 − ν)(X/y)^θ`
  (`ces_share_l`).
* **(25.33)–(25.34), corrected**: the technologies are recovered as
  `A_e = (y/e)(e^{share}/ν)^{1/θ}` (`eq_25_34`) and
  `A = y/(k^αl^{1−α}) · (l^{share}/((1 − α)(1 − ν)))^{1/θ}` (`eq_25_33`), with
  `1/θ = ε/(ε − 1)` (`ces_exponent`). The printed formulas omit the CES weights `ν` and
  `1 − ν`; they return `ν^{1/θ}A_e` and `(1 − ν)^{1/θ}A` (`eq_25_34_printed`,
  `eq_25_33_printed`), wrong in level (`eq_25_34_printed_false`) though right in growth rates
  (`eq_25_34_printed_growth`).
* **The technology menu** (p. 782, after Leon-Ledesma and Satchi): with
  `f(A_x x, A_y y) = ((A_x x)^ρ + (A_y y)^ρ)^{1/ρ}`, `ρ < 0` (elasticity below one), and the
  CES frontier `A_x^ω + A_y^ω = 1`, `ω > 0`, the best choice of technology gives the
  reduced form `(x^{ρ'} + y^{ρ'})^{1/ρ'}` with `ρ' = ρω/(ω − ρ)` (`menu_reduced_le`,
  `menu_reduced_attained`): a CES whose elasticity `1/(1 − ρ')` exceeds the short-run elasticity
  `1/(1 − ρ)` and stays below one (`menu_elasticity`). The book states the result for a CES
  frontier without specifying the exponent; `ω > 0` (a frontier bowed out) is the hypothesis
  under which it holds as stated.
-/

namespace AKMM.Sustainability

open Real

/-- AKMM, p. 779: the CES production function `[(1 − ν)X^θ + νZ^θ]^{1/θ}`, `θ = (ε − 1)/ε`. -/
noncomputable def cesY (ν θ X Z : ℝ) : ℝ := ((1 - ν) * X ^ θ + ν * Z ^ θ) ^ (1 / θ)

/-- AKMM, p. 780: the exponent of (25.33)–(25.34): `1/θ = ε/(ε − 1)` for `θ = (ε − 1)/ε`. -/
theorem ces_exponent (ε : ℝ) : 1 / ((ε - 1) / ε) = ε / (ε - 1) := by
  rw [one_div_div]

/-- `y^θ = (1 − ν)X^θ + νZ^θ`. -/
theorem cesY_rpow {ν θ X Z : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X) (hZ : 0 < Z)
    (hθ : θ ≠ 0) : cesY ν θ X Z ^ θ = (1 - ν) * X ^ θ + ν * Z ^ θ := by
  have h1 : 0 < 1 - ν := by linarith
  unfold cesY
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hθ, Real.rpow_one]

/-- AKMM, p. 780: the energy cost share of a competitive firm, `e·(∂y/∂e)/y = ν(A_e e/y)^θ`,
from the derivative of `y` in `e`. -/
theorem ces_share_e {ν θ X Ae e : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X) (hAe : 0 < Ae)
    (he : 0 < e) (hθ : θ ≠ 0) :
    ∃ d, HasDerivAt (fun e => cesY ν θ X (Ae * e)) d e ∧
      e * d / cesY ν θ X (Ae * e) = ν * (Ae * e / cesY ν θ X (Ae * e)) ^ θ := by
  have h1 : 0 < 1 - ν := by linarith
  set S := (1 - ν) * X ^ θ + ν * (Ae * e) ^ θ with hS
  have hSpos : 0 < S := by positivity
  have hin : HasDerivAt (fun e => (1 - ν) * X ^ θ + ν * (Ae ^ θ * e ^ θ))
      (ν * (Ae ^ θ * (θ * e ^ (θ - 1)))) e :=
    (((Real.hasDerivAt_rpow_const (Or.inl he.ne')).const_mul (Ae ^ θ)).const_mul ν).const_add _
  have hfun : (fun e => (1 - ν) * X ^ θ + ν * (Ae ^ θ * e ^ θ)) =ᶠ[nhds e]
      fun e => (1 - ν) * X ^ θ + ν * (Ae * e) ^ θ := by
    filter_upwards [lt_mem_nhds he] with x hx
    rw [Real.mul_rpow hAe.le hx.le]
  have hout := (hin.congr_of_eventuallyEq hfun.symm).rpow_const (p := 1 / θ)
    (Or.inl hSpos.ne')
  refine ⟨_, hout, ?_⟩
  have hy' : cesY ν θ X (Ae * e) = S ^ (1 / θ) := rfl
  have hy0 : 0 < S ^ (1 / θ) := Real.rpow_pos_of_pos hSpos _
  have hyθ : (S ^ (1 / θ)) ^ θ = S := by
    rw [← Real.rpow_mul hSpos.le, one_div_mul_cancel hθ, Real.rpow_one]
  rw [hy', Real.div_rpow (by positivity) hy0.le, hyθ, ← hS, Real.rpow_sub_one hSpos.ne',
    Real.rpow_sub_one he.ne', Real.mul_rpow hAe.le he.le]
  field_simp

/-- AKMM, p. 780: the labour cost share, `l·(∂y/∂l)/y = (1 − α)(1 − ν)(X/y)^θ` with
`X = Ak^αl^{1−α}`. -/
theorem ces_share_l {ν θ α A k Z l : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < A)
    (hk : 0 < k) (hZ : 0 < Z) (hl : 0 < l) (hθ : θ ≠ 0) :
    ∃ d, HasDerivAt (fun l => cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) d l ∧
      l * d / cesY ν θ (A * k ^ α * l ^ (1 - α)) Z =
        (1 - α) * (1 - ν) * (A * k ^ α * l ^ (1 - α) / cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^
          θ := by
  have h1 : 0 < 1 - ν := by linarith
  have hka := Real.rpow_pos_of_pos hk α
  set c := (A * k ^ α) ^ θ with hc
  have hc0 : 0 < c := by positivity
  set X := A * k ^ α * l ^ (1 - α) with hX
  have hXpos : 0 < X := by have := Real.rpow_pos_of_pos hl (1 - α); positivity
  set S := (1 - ν) * X ^ θ + ν * Z ^ θ with hS
  have hSpos : 0 < S := by positivity
  have hXθ : ∀ x : ℝ, 0 < x → (A * k ^ α * x ^ (1 - α)) ^ θ = c * x ^ ((1 - α) * θ) := by
    intro x hx
    have := Real.rpow_pos_of_pos hx (1 - α)
    rw [Real.mul_rpow (by positivity) this.le, ← Real.rpow_mul hx.le]
  have hin : HasDerivAt (fun x => (1 - ν) * (c * x ^ ((1 - α) * θ)) + ν * Z ^ θ)
      ((1 - ν) * (c * ((1 - α) * θ * l ^ ((1 - α) * θ - 1)))) l :=
    (((Real.hasDerivAt_rpow_const (Or.inl hl.ne')).const_mul c).const_mul (1 - ν)).add_const _
  have hfun : (fun x => (1 - ν) * (c * x ^ ((1 - α) * θ)) + ν * Z ^ θ) =ᶠ[nhds l]
      fun x => (1 - ν) * (A * k ^ α * x ^ (1 - α)) ^ θ + ν * Z ^ θ := by
    filter_upwards [lt_mem_nhds hl] with x hx
    rw [hXθ x hx]
  have hS' : (1 - ν) * (A * k ^ α * l ^ (1 - α)) ^ θ + ν * Z ^ θ = S := rfl
  have hout := (hin.congr_of_eventuallyEq hfun.symm).rpow_const (p := 1 / θ)
    (Or.inl (by rw [hS']; exact hSpos.ne'))
  refine ⟨_, hout, ?_⟩
  have hy : cesY ν θ X Z = S ^ (1 / θ) := rfl
  rw [hy, Real.div_rpow hXpos.le (by positivity), ← Real.rpow_mul hSpos.le,
    one_div_mul_cancel hθ, Real.rpow_one, hS']
  have hSθ : S ^ (1 / θ - 1) = S ^ (1 / θ) / S := by rw [Real.rpow_sub_one hSpos.ne']
  have hlθ : l ^ ((1 - α) * θ - 1) = l ^ ((1 - α) * θ) / l := by
    rw [Real.rpow_sub_one hl.ne']
  rw [hSθ, hlθ, hX, hXθ l hl]
  have := Real.rpow_pos_of_pos hSpos (1 / θ)
  field_simp

/-- AKMM, (25.34) corrected, p. 780: from the energy share, `A_e = (y/e)(e^{share}/ν)^{1/θ}`. -/
theorem eq_25_34 {ν θ X Ae e : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X) (hAe : 0 < Ae)
    (he : 0 < e) (hθ : θ ≠ 0) {sh : ℝ}
    (hsh : sh = ν * (Ae * e / cesY ν θ X (Ae * e)) ^ θ) :
    Ae = cesY ν θ X (Ae * e) / e * (sh / ν) ^ (1 / θ) := by
  have h1 : 0 < 1 - ν := by linarith
  have hy : 0 < cesY ν θ X (Ae * e) := by unfold cesY; positivity
  rw [hsh, mul_div_cancel_left₀ _ hν0.ne', ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, (25.33) corrected, p. 780: from the labour share,
`A = y/(k^αl^{1−α}) · (l^{share}/((1 − α)(1 − ν)))^{1/θ}`. -/
theorem eq_25_33 {ν θ α A k Z l : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hα1 : α < 1) (hA : 0 < A)
    (hk : 0 < k) (hZ : 0 < Z) (hl : 0 < l) (hθ : θ ≠ 0) {sh : ℝ}
    (hsh : sh = (1 - α) * (1 - ν) *
      (A * k ^ α * l ^ (1 - α) / cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ) :
    A = cesY ν θ (A * k ^ α * l ^ (1 - α)) Z / (k ^ α * l ^ (1 - α)) *
      (sh / ((1 - α) * (1 - ν))) ^ (1 / θ) := by
  have h1 : 0 < 1 - ν := by linarith
  have h2 : 0 < 1 - α := by linarith
  have hka := Real.rpow_pos_of_pos hk α
  have hla := Real.rpow_pos_of_pos hl (1 - α)
  have hy : 0 < cesY ν θ (A * k ^ α * l ^ (1 - α)) Z := by unfold cesY; positivity
  rw [hsh, mul_div_cancel_left₀ _ (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, (25.34) as printed, p. 780: `(y/e)(e^{share})^{1/θ}` equals `ν^{1/θ}A_e`. -/
theorem eq_25_34_printed {ν θ X Ae e : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hX : 0 < X)
    (hAe : 0 < Ae) (he : 0 < e) (hθ : θ ≠ 0) :
    cesY ν θ X (Ae * e) / e * (ν * (Ae * e / cesY ν θ X (Ae * e)) ^ θ) ^ (1 / θ) =
      ν ^ (1 / θ) * Ae := by
  have h1 : 0 < 1 - ν := by linarith
  have hy : 0 < cesY ν θ X (Ae * e) := by unfold cesY; positivity
  rw [Real.mul_rpow hν0.le (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, (25.33) as printed, p. 780: `y/(k^αl^{1−α}) · (l^{share}/(1 − α))^{1/θ}` equals
`(1 − ν)^{1/θ}A`. -/
theorem eq_25_33_printed {ν θ α A k Z l : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hα1 : α < 1)
    (hA : 0 < A) (hk : 0 < k) (hZ : 0 < Z) (hl : 0 < l) (hθ : θ ≠ 0) :
    cesY ν θ (A * k ^ α * l ^ (1 - α)) Z / (k ^ α * l ^ (1 - α)) *
      ((1 - α) * (1 - ν) * (A * k ^ α * l ^ (1 - α) /
        cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ / (1 - α)) ^ (1 / θ) =
      (1 - ν) ^ (1 / θ) * A := by
  have h1 : 0 < 1 - ν := by linarith
  have h2 : 0 < 1 - α := by linarith
  have hka := Real.rpow_pos_of_pos hk α
  have hla := Real.rpow_pos_of_pos hl (1 - α)
  have hy : 0 < cesY ν θ (A * k ^ α * l ^ (1 - α)) Z := by unfold cesY; positivity
  have hsimp : (1 - α) * (1 - ν) * (A * k ^ α * l ^ (1 - α) /
      cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ / (1 - α) = (1 - ν) * (A * k ^ α * l ^ (1 - α) /
      cesY ν θ (A * k ^ α * l ^ (1 - α)) Z) ^ θ := by field_simp
  rw [hsimp, Real.mul_rpow h1.le (by positivity), ← Real.rpow_mul (by positivity),
    mul_one_div_cancel hθ, Real.rpow_one]
  field_simp

/-- AKMM, p. 780: the printed (25.34) is wrong in levels: with `ε = 2` (`θ = 1/2`) and
`ν = 1/4` it returns `A_e/16`. -/
theorem eq_25_34_printed_false {X Ae e : ℝ} (hX : 0 < X) (hAe : 0 < Ae) (he : 0 < e) :
    cesY (1 / 4) (1 / 2) X (Ae * e) / e *
        ((1 / 4) * (Ae * e / cesY (1 / 4) (1 / 2) X (Ae * e)) ^ (1 / 2 : ℝ)) ^ (1 / (1 / 2) : ℝ) ≠
      Ae := by
  rw [eq_25_34_printed (by norm_num) (by norm_num) hX hAe he (by norm_num)]
  have : (1 / 4 : ℝ) ^ (1 / (1 / 2) : ℝ) = 1 / 16 := by
    rw [show (1 / (1 / 2) : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]; norm_num
  rw [this]
  intro h
  linarith

/-- AKMM, p. 780: the printed formulas are off by constant factors, so they give the right
growth rates: the ratio of the printed `A_e` at two dates is the ratio of the true ones. -/
theorem eq_25_34_printed_growth {ν θ : ℝ} (hν0 : 0 < ν) {a b : ℝ} (hb : 0 < b) :
    ν ^ (1 / θ) * a / (ν ^ (1 / θ) * b) = a / b := by
  have := Real.rpow_pos_of_pos hν0 (1 / θ)
  field_simp

/-- The key inequality of the technology menu: for `q < 0`, `a, b > 0` with `a + b = 1` and
`c, d > 0`, `a^q c + b^q d ≥ (c^r + d^r)^{1−q}` with `r = 1/(1 − q)`, with equality at
`a = c^r/(c^r + d^r)`. -/
theorem menu_key {q a b c d : ℝ} (hq : q < 0) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hc : 0 < c) (hd : 0 < d) :
    (c ^ (1 / (1 - q)) + d ^ (1 / (1 - q))) ^ (1 - q) ≤ a ^ q * c + b ^ q * d := by
  have h1q : 0 < 1 - q := by linarith
  set r := 1 / (1 - q) with hr
  set S := c ^ r + d ^ r with hS
  have hcr := Real.rpow_pos_of_pos hc r
  have hdr := Real.rpow_pos_of_pos hd r
  have hS0 : 0 < S := by positivity
  set a0 := c ^ r / S
  set b0 := d ^ r / S
  have ha0 : 0 < a0 := div_pos hcr hS0
  have hb0 : 0 < b0 := div_pos hdr hS0
  have hab0 : a0 + b0 = 1 := by
    simp only [a0, b0]; rw [← add_div, ← hS, div_self hS0.ne']
  -- `c a0^{q−1} = S^{1−q}` since `r(q − 1) = −1`
  have hrq : r * (q - 1) = -1 := by rw [hr]; field_simp; ring
  have hrq' : r * q + 1 = r := by rw [hr]; field_simp; ring
  have key : ∀ x, 0 < x → x * (x ^ r / S) ^ (q - 1) = S ^ (1 - q) := by
    intro x hx
    have hxr := Real.rpow_pos_of_pos hx r
    rw [Real.div_rpow hxr.le hS0.le, ← Real.rpow_mul hx.le, hrq, Real.rpow_neg_one,
      show (1 : ℝ) - q = -(q - 1) by ring, Real.rpow_neg hS0.le]
    field_simp
  have val : ∀ x, 0 < x → (x ^ r / S) ^ q * x = x ^ r * S ^ (-q) := by
    intro x hx
    have hxr := Real.rpow_pos_of_pos hx r
    rw [Real.div_rpow hxr.le hS0.le, ← Real.rpow_mul hx.le, Real.rpow_neg hS0.le]
    have : x ^ (r * q) * x = x ^ r := by
      rw [← Real.rpow_add_one hx.ne', hrq']
    field_simp
    linarith [this]
  have t1 := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tangent_le_rpow hq.le ha ha0
  have t2 := ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tangent_le_rpow hq.le hb hb0
  have k1 := mul_le_mul_of_nonneg_right t1 hc.le
  have k2 := mul_le_mul_of_nonneg_right t2 hd.le
  have e1 : (a0 ^ q + q * a0 ^ (q - 1) * (a - a0)) * c =
      a0 ^ q * c + q * S ^ (1 - q) * (a - a0) := by rw [← key c hc]; ring
  have e2 : (b0 ^ q + q * b0 ^ (q - 1) * (b - b0)) * d =
      b0 ^ q * d + q * S ^ (1 - q) * (b - b0) := by rw [← key d hd]; ring
  have e3 : a0 ^ q * c + b0 ^ q * d = S ^ (1 - q) := by
    rw [val c hc, val d hd, show (1 - q) = 1 + -q by ring, Real.rpow_add hS0, Real.rpow_one]
    ring
  have hlin : q * S ^ (1 - q) * (a - a0) + q * S ^ (1 - q) * (b - b0) = 0 := by
    have : a - a0 + (b - b0) = 0 := by linarith
    linear_combination (q * S ^ (1 - q)) * this
  nlinarith [k1, k2, e1, e2, e3, hlin]

/-- AKMM, p. 782, the technology menu (Leon-Ledesma–Satchi): for `ρ < 0 < ω`, every technology
on the frontier `A_x^ω + A_y^ω = 1` gives output at most the reduced-form CES
`(x^{ρ'} + y^{ρ'})^{1/ρ'}`, `ρ' = ρω/(ω − ρ)`. -/
theorem menu_reduced_le {ρ ω x y Ax Ay : ℝ} (hρ : ρ < 0) (hω : 0 < ω) (hx : 0 < x) (hy : 0 < y)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hfr : Ax ^ ω + Ay ^ ω = 1) :
    ((Ax * x) ^ ρ + (Ay * y) ^ ρ) ^ (1 / ρ) ≤
      (x ^ (ρ * ω / (ω - ρ)) + y ^ (ρ * ω / (ω - ρ))) ^ (1 / (ρ * ω / (ω - ρ))) := by
  have hωρ : 0 < ω - ρ := by linarith
  set q := ρ / ω with hq
  have hq0 : q < 0 := div_neg_of_neg_of_pos hρ hω
  have hr : 1 / (1 - q) = ω / (ω - ρ) := by rw [hq]; field_simp
  have hcr : ∀ z : ℝ, 0 < z → (z ^ ρ) ^ (1 / (1 - q)) = z ^ (ρ * ω / (ω - ρ)) := by
    intro z hz
    rw [← Real.rpow_mul hz.le, hr]; ring_nf
  have hpow : ∀ A z : ℝ, 0 < A → 0 < z → (A * z) ^ ρ = (A ^ ω) ^ q * z ^ ρ := by
    intro A z hA hz
    rw [Real.mul_rpow hA.le hz.le, ← Real.rpow_mul hA.le, hq]
    congr 2
    field_simp
  have hk := menu_key hq0 (Real.rpow_pos_of_pos hAx ω) (Real.rpow_pos_of_pos hAy ω) hfr
    (Real.rpow_pos_of_pos hx ρ) (Real.rpow_pos_of_pos hy ρ)
  rw [hcr x hx, hcr y hy] at hk
  rw [hpow Ax x hAx hx, hpow Ay y hAy hy]
  set S := x ^ (ρ * ω / (ω - ρ)) + y ^ (ρ * ω / (ω - ρ)) with hS
  have hS0 : 0 < S := by positivity
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) hk (by
    have : 1 / ρ < 0 := one_div_neg.mpr hρ
    linarith)
  rw [← Real.rpow_mul hS0.le] at h2
  have : (1 - q) * (1 / ρ) = 1 / (ρ * ω / (ω - ρ)) := by
    rw [hq]; field_simp
  rw [this] at h2
  exact h2

/-- AKMM, p. 782: the reduced form is attained by the technology
`A_x^ω = x^{ρ'}/(x^{ρ'} + y^{ρ'})`, `A_y^ω = y^{ρ'}/(x^{ρ'} + y^{ρ'})` on the frontier. -/
theorem menu_reduced_attained {ρ ω x y : ℝ} (hρ : ρ < 0) (hω : 0 < ω) (hx : 0 < x)
    (hy : 0 < y) :
    ∃ Ax Ay : ℝ, 0 < Ax ∧ 0 < Ay ∧ Ax ^ ω + Ay ^ ω = 1 ∧
      ((Ax * x) ^ ρ + (Ay * y) ^ ρ) ^ (1 / ρ) =
        (x ^ (ρ * ω / (ω - ρ)) + y ^ (ρ * ω / (ω - ρ))) ^ (1 / (ρ * ω / (ω - ρ))) := by
  have hωρ : 0 < ω - ρ := by linarith
  set ρ' := ρ * ω / (ω - ρ) with hρ'
  set S := x ^ ρ' + y ^ ρ' with hS
  have hxr := Real.rpow_pos_of_pos hx ρ'
  have hyr := Real.rpow_pos_of_pos hy ρ'
  have hS0 : 0 < S := by positivity
  set a0 := x ^ ρ' / S
  set b0 := y ^ ρ' / S
  have ha0 : 0 < a0 := div_pos hxr hS0
  have hb0 : 0 < b0 := div_pos hyr hS0
  refine ⟨a0 ^ (1 / ω), b0 ^ (1 / ω), by positivity, by positivity, ?_, ?_⟩
  · rw [← Real.rpow_mul ha0.le, ← Real.rpow_mul hb0.le, one_div_mul_cancel hω.ne',
      Real.rpow_one, Real.rpow_one]
    simp only [a0, b0]; rw [← add_div, ← hS, div_self hS0.ne']
  · -- `(a0^{1/ω} x)^ρ = a0^{ρ/ω} x^ρ = x^{ρ'} S^{−ρ/ω}`
    have hterm : ∀ z, 0 < z → ((z ^ ρ' / S) ^ (1 / ω) * z) ^ ρ =
        z ^ ρ' * S ^ (-(ρ / ω)) := by
      intro z hz
      have hzr := Real.rpow_pos_of_pos hz ρ'
      have e : ρ' * (ρ / ω) + ρ = ρ' := by rw [hρ']; field_simp; ring
      have hzz : z ^ (ρ' * (ρ / ω)) * z ^ ρ = z ^ ρ' := by rw [← Real.rpow_add hz, e]
      calc ((z ^ ρ' / S) ^ (1 / ω) * z) ^ ρ = (z ^ ρ' / S) ^ (ρ / ω) * z ^ ρ := by
            rw [Real.mul_rpow (by positivity) hz.le, ← Real.rpow_mul (by positivity)]
            congr 2; ring
        _ = z ^ (ρ' * (ρ / ω)) / S ^ (ρ / ω) * z ^ ρ := by
            rw [Real.div_rpow hzr.le hS0.le, ← Real.rpow_mul hz.le]
        _ = (z ^ (ρ' * (ρ / ω)) * z ^ ρ) * S ^ (-(ρ / ω)) := by
            rw [Real.rpow_neg hS0.le]; ring
        _ = z ^ ρ' * S ^ (-(ρ / ω)) := by rw [hzz]
    rw [hterm x hx, hterm y hy, ← add_mul, ← hS, ← Real.rpow_one_add' hS0.le (by
      rw [show 1 + -(ρ / ω) = (ω - ρ) / ω by field_simp; ring]
      exact (div_pos hωρ hω).ne'), ← Real.rpow_mul hS0.le]
    congr 1
    rw [hρ']
    field_simp
    ring

/-- AKMM, p. 782: "a ‘reduced-form’ production function ... with a higher elasticity of
substitution": for `ρ < 0 < ω`, `ρ < ρ' = ρω/(ω − ρ) < 0`, so the long-run elasticity
`1/(1 − ρ')` exceeds the short-run one `1/(1 − ρ)` and is below one. -/
theorem menu_elasticity {ρ ω : ℝ} (hρ : ρ < 0) (hω : 0 < ω) :
    ρ < ρ * ω / (ω - ρ) ∧ ρ * ω / (ω - ρ) < 0 ∧
      1 / (1 - ρ) < 1 / (1 - ρ * ω / (ω - ρ)) ∧ 1 / (1 - ρ * ω / (ω - ρ)) < 1 := by
  have hωρ : 0 < ω - ρ := by linarith
  have h1 : ρ < ρ * ω / (ω - ρ) := by
    rw [lt_div_iff₀ hωρ]; nlinarith
  have h2 : ρ * ω / (ω - ρ) < 0 := div_neg_of_neg_of_pos (by nlinarith) hωρ
  refine ⟨h1, h2, ?_, ?_⟩
  · exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]; linarith

end AKMM.Sustainability
