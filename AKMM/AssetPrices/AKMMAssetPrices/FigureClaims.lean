/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMAssetPrices.MehraPrescott
import Mathlib.Analysis.MeanInequalities

/-!
# Figure 16.4: the equity premium puzzle

AKMM, §16.6, p. 488 and Figure 16.4. The figure plots the (mean riskless rate, equity premium)
pairs of the Mehra–Prescott economy (`MehraPrescott`) for `β ∈ [0, 1]` and `γ ∈ [0, 100]`, keeping
the equilibria with `E[rᶠ] < 4%`, and the text reads off it that "the equity premium is less than
0.1 percent". The growth process is fixed by Table 16.1: `G_{L,H} = 1 + μ ∓ δ` with `μ = 0.0175`,
`δ = 0.0233` and `2φ − 1 = 0.1069` (three moments, three parameters; `mpf_primitives`).

* The premium is an average of conditional covariances (`mpf_premium_cov`, from
  `mpf_cond_cov`): `E[rˢ] − E[rᶠ] = ½ Σᵢ φ(1 − φ)(G_L^{−γ} − G_H^{−γ})(G_H(1 + v_H) −
  G_L(1 + v_L))/(Eᵢ[G^{−γ}]vᵢ)`, for every symmetric chain.
* In the figure's range, `E[rᶠ] < 4%` forces `γ < 5/2` (`mpf_gamma_lt`), by convexity of
  `γ ↦ G^{−γ}` and the harmonic–arithmetic mean inequality.
* **Corrected claim**: on the whole region the equity premium is positive (for `γ > 0`) and below
  `0.17%` (`mpf_premium_bound`, via the scalar steps `mpf_core_*`): the two price–dividend ratios
  differ by less than `0.81%`, both exceed `0.94(1 + v_L)`, and the bond prices exceed `0.955`.
* **The printed bound fails**: at `β = 1`, `γ = 9/4` the equilibrium exists (`ρ(A) < 1`), the
  mean riskless rate is about `3.78%` and the premium about `0.103% > 0.1%`
  (`mpf_counterexample`, `mpf_fig_16_4_printed_false`), with `G^{−9/4}` enclosed to `10⁻⁷` by
  exact rational arithmetic (`mpf_ce_bounds`).

Everything is proved for the whole parametric region, not at grid points; the only numbers are the
text's primitives. Left open: the exact supremum of the premium on the region (between `0.103%`
and `0.17%`).
-/

namespace AKMM.AssetPrices

open Matrix SargentStachurski.StochasticDiscounting

/-- AKMM, (16.26)–(16.27), p. 487: the conditional equity premium in one state. With
transition probabilities `(p, q)`, stochastic discount factor `βbⱼ` (`bⱼ = Gⱼ^{−γ}`) and stock
payoffs `uⱼ = Gⱼ(1 + vⱼ)` priced by `v = βE[bu]`, the expected stock return minus the riskless
rate is `pq(b_L − b_H)(u_H − u_L)/(E[b]·v)`: minus the conditional covariance of the payoff with
the discount factor. -/
theorem mpf_cond_cov {p q β bL bH uL uH v : ℝ} (hpq : p + q = 1) (hβ : β ≠ 0)
    (he : p * bL + q * bH ≠ 0) (hv0 : v ≠ 0) (hv : v = β * (p * bL * uL + q * bH * uH)) :
    p * (uL / v - 1) + q * (uH / v - 1) - (1 / (β * (p * bL + q * bH)) - 1) =
      p * q * (bL - bH) * (uH - uL) / ((p * bL + q * bH) * v) := by
  have hq : q = 1 - p := by linarith
  subst hq
  rw [eq_div_iff (mul_ne_zero he hv0)]
  field_simp
  linear_combination -hv

/-- `G^{1−γ} = G·G^{−γ}`: the weights `Aᵢⱼ = ΠᵢⱼGⱼ^{1−γ}` of p. 486 are growth times the
marginal-utility ratio. -/
theorem mpf_rpow_one_sub {G : ℝ} (hG : 0 < G) (γ : ℝ) : G ^ (1 - γ) = G * G ^ (-γ) := by
  rw [sub_eq_add_neg, Real.rpow_add hG, Real.rpow_one]

/-- AKMM, p. 486: the two scalar equations of `v = βA(1 + v)`. -/
theorem mpf_pd_eqs {φ β γ : ℝ} {G v : Fin 2 → ℝ} (hG : ∀ j, 0 < G j)
    (hv : v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i)) :
    v 0 = β * (φ * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + (1 - φ) * G 1 ^ (-γ) * (G 1 * (1 + v 1))) ∧
      v 1 = β * ((1 - φ) * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + φ * G 1 ^ (-γ) * (G 1 * (1 + v 1)))
      := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, mpA, Matrix.of_apply,
    mpPi, smul_eq_mul, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1)] at h0 h1
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1
  constructor
  · linear_combination h0
  · linear_combination h1

/-- AKMM, p. 487: the bond prices `pᶠᵢ = β Σⱼ ΠᵢⱼGⱼ^{−γ}` (`mp_bond_price`). -/
theorem mpf_bond_eqs (φ β γ : ℝ) (G : Fin 2 → ℝ) :
    mpBond φ β γ G 0 = β * (φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ)) ∧
      mpBond φ β γ G 1 = β * ((1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ)) :=
  mp_bond_price φ β γ G

/-- AKMM, (16.26)–(16.27), p. 487, the equity premium of the Mehra–Prescott economy as an
average of conditional covariances: for any symmetric chain `φ ∈ [0, 1]`, any positive growth
states and any positive price–dividend ratio `v = βA(1 + v)`,
`E[rˢ] − E[rᶠ] = ½ Σᵢ φ(1 − φ)(G_L^{−γ} − G_H^{−γ})(G_H(1 + v_H) − G_L(1 + v_L))/(Eᵢ[G^{−γ}]vᵢ)`.
The sign of the premium is the sign of `(G_L^{−γ} − G_H^{−γ})(G_H(1 + v_H) − G_L(1 + v_L))`. -/
theorem mpf_premium_cov {φ β γ : ℝ} {G v : Fin 2 → ℝ} (hG : ∀ j, 0 < G j) (hβ : 0 < β)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (hv0 : ∀ i, 0 < v i)
    (hv : v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i)) :
    mpEquityPremium φ β γ G (fun i j => G j * (1 + v j) / v i - 1) =
      ∑ i, ![1 / 2, 1 / 2] i * (φ * (1 - φ) * (G 0 ^ (-γ) - G 1 ^ (-γ)) *
        (G 1 * (1 + v 1) - G 0 * (1 + v 0)) / (mpBond φ 1 γ G i * v i)) := by
  obtain ⟨e0, e1⟩ := mpf_pd_eqs hG hv
  obtain ⟨b0, b1⟩ := mpf_bond_eqs φ β γ G
  obtain ⟨c0, c1⟩ := mpf_bond_eqs φ 1 γ G
  have p0 := Real.rpow_pos_of_pos (hG 0) (-γ)
  have p1 := Real.rpow_pos_of_pos (hG 1) (-γ)
  have h1φ : 0 ≤ 1 - φ := by linarith
  have hm := lt_min p0 p1
  have m0 := min_le_left (G 0 ^ (-γ)) (G 1 ^ (-γ))
  have m1 := min_le_right (G 0 ^ (-γ)) (G 1 ^ (-γ))
  have n0 : φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ) ≠ 0 := by
    have : 0 < φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ) := by
      nlinarith [mul_le_mul_of_nonneg_left m0 hφ0, mul_le_mul_of_nonneg_left m1 h1φ]
    exact this.ne'
  have n1 : (1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ) ≠ 0 := by
    have : 0 < (1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ) := by
      nlinarith [mul_le_mul_of_nonneg_left m1 hφ0, mul_le_mul_of_nonneg_left m0 h1φ]
    exact this.ne'
  have k0 := mpf_cond_cov (p := φ) (q := 1 - φ) (by ring) hβ.ne' n0 (hv0 0).ne' e0
  have k1 := mpf_cond_cov (p := 1 - φ) (q := φ) (uL := G 0 * (1 + v 0))
    (uH := G 1 * (1 + v 1)) (by ring) hβ.ne' n1 (hv0 1).ne'
    (by linear_combination e1)
  simp only [mpEquityPremium, mpUncondMean, mpCondMean, Fin.sum_univ_two, mpRf, b0, b1, c0, c1,
    mpPi]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, one_mul]
  linear_combination (1 / 2 : ℝ) * k0 + (1 / 2 : ℝ) * k1

/-- Figure 16.4, step 1 (scalar form): with `G^{−γ}` in the ranges of `γ ∈ [0, 5/2]`, a mean
riskless rate below 4% puts both bond prices above `0.955`. -/
theorem mpf_core_bond {β b0 b1 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb0 : 1 ≤ b0)
    (hb0' : b0 ≤ 10147 / 10000) (hb1 : 9048 / 10000 ≤ b1) (hb1' : b1 ≤ 1)
    (hrf : 1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
      1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1)) < 52 / 25) :
    955 / 1000 < β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) ∧
      β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) ≤
        β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) := by
  have hd : β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) -
      β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) = β * (1069 / 10000 * (b0 - b1)) := by
    ring
  have hx1 : 0 < β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) :=
    mul_pos hβ0 (by linarith)
  have hx0 : 0 < β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) :=
    mul_pos hβ0 (by linarith)
  have hgap : β * (1069 / 10000 * (b0 - b1)) ≤ 118 / 10000 := by nlinarith
  have hgap0 : 0 ≤ β * (1069 / 10000 * (b0 - b1)) := by
    have : 0 ≤ b0 - b1 := by linarith
    positivity
  refine ⟨?_, by linarith⟩
  by_contra h
  rw [not_lt] at h
  have i1 := one_div_le_one_div_of_le hx1 h
  have i0 := one_div_le_one_div_of_le hx0
    (show β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) ≤ 9668 / 10000 by linarith)
  have : (52 / 25 : ℝ) < 1 / (955 / 1000) + 1 / (9668 / 10000) := by norm_num
  linarith

/-- Figure 16.4, step 2 (scalar form): the two values of `1 + v` differ by at most `0.81%`,
from `(w_H − w_L)(1 − β(2φ − 1)a_H) = β(2φ − 1)(a_H − a_L)w_L`. -/
theorem mpf_core_ratio {β b0 b1 w0 w1 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb0 : 1 ≤ b0)
    (hb0' : b0 ≤ 10147 / 10000) (hb1 : 9048 / 10000 ≤ b1) (hb1' : b1 ≤ 1) (hw0 : 0 < w0)
    (hw : (w1 - w0) * (1 - β * (1069 / 10000) * (1301 / 1250) * b1) =
      β * (1069 / 10000) * (1301 / 1250 * b1 - 4971 / 5000 * b0) * w0) :
    w1 - w0 ≤ 81 / 10000 * w0 ∧ -(81 / 10000 * w0) ≤ w1 - w0 := by
  have hD : 8887 / 10000 ≤ 1 - β * (1069 / 10000) * (1301 / 1250) * b1 := by nlinarith
  have hc1 : β * (1301 / 1250 * b1 - 4971 / 5000 * b0) ≤ 466 / 10000 := by
    nlinarith [mul_nonneg hβ0.le (show (0 : ℝ) ≤ 466 / 10000 -
      (1301 / 1250 * b1 - 4971 / 5000 * b0) by linarith)]
  have hc2 : -(671 / 10000) ≤ β * (1301 / 1250 * b1 - 4971 / 5000 * b0) := by
    nlinarith [mul_nonneg hβ0.le (show (0 : ℝ) ≤ 671 / 10000 +
      (1301 / 1250 * b1 - 4971 / 5000 * b0) by linarith)]
  have hDp : (0 : ℝ) < 1 - β * (1069 / 10000) * (1301 / 1250) * b1 := by linarith
  have h2 := mul_le_mul_of_nonneg_left hD (by linarith : (0 : ℝ) ≤ 81 / 10000 * w0)
  constructor
  · by_contra h
    rw [not_le] at h
    have h1 := mul_lt_mul_of_pos_right h hDp
    have h3 := mul_le_mul_of_nonneg_right hc1 hw0.le
    linarith
  · by_contra h
    rw [not_le] at h
    have h1 := mul_lt_mul_of_pos_right h hDp
    have h3 := mul_le_mul_of_nonneg_right hc2 hw0.le
    linarith

/-- Figure 16.4, step 3 (scalar form): a price–dividend ratio `v = β Σⱼ Πᵢⱼbⱼuⱼ` is at least
`0.9417(1 + v_L)` when its bond price exceeds `0.955`. -/
theorem mpf_core_v {β b0 b1 p q x v w0 w1 : ℝ} (hβ0 : 0 < β) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hw0 : 0 < w0) (hwl : -(81 / 10000 * w0) ≤ w1 - w0)
    (hx : x = β * (p * b0 + q * b1)) (hx' : 955 / 1000 < x)
    (hv : v = β * (p * b0 * (4971 / 5000 * w0) + q * b1 * (1301 / 1250 * w1))) :
    9417 / 10000 * w0 ≤ v := by
  have hGw : 4971 / 5000 * (9919 / 10000 * w0) ≤ 1301 / 1250 * w1 := by linarith
  have h1 := mul_le_mul_of_nonneg_left hGw (mul_nonneg hq hb1)
  have h4 := mul_le_mul_of_nonneg_left h1 hβ0.le
  have h5 : 0 ≤ β * (p * b0 * w0) := by positivity
  have h2 : 4971 / 5000 * (9919 / 10000) * w0 * x ≤ v := by
    rw [hv, hx]
    linarith
  have h3 := mul_le_mul_of_nonneg_left hx'.le (by positivity : (0 : ℝ) ≤
    4971 / 5000 * (9919 / 10000) * w0)
  linarith

/-- Figure 16.4, step 4 (scalar form): the bound on one conditional premium. -/
theorem mpf_core_term {β d U e v x w0 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hd : 0 ≤ d)
    (hU0 : 0 ≤ U) (hU : U ≤ 5504 / 100000 * w0) (he : 0 < e) (hv : 0 < v) (hx : x = β * e)
    (hvw : 9417 / 10000 * w0 ≤ v) :
    11069 / 20000 * (1 - 11069 / 20000) * d * U / (e * v) ≤
      11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000) * (1 / x) := by
  have hxe : 11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000) *
      (1 / x) * (e * v) =
      11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000) * v / β := by
    rw [hx]
    field_simp
  rw [div_le_iff₀ (mul_pos he hv), hxe, le_div_iff₀ hβ0]
  have hp : 0 ≤ 11069 / 20000 * (1 - 11069 / 20000) * d := by positivity
  have q1 := mul_le_mul_of_nonneg_left hU hp
  have q2 := mul_le_mul_of_nonneg_left hvw (by positivity : (0 : ℝ) ≤
    11069 / 20000 * (1 - 11069 / 20000) * d * (5504 / 100000) / (9417 / 10000))
  have q3 := mul_le_mul_of_nonneg_left hβ1 (mul_nonneg hp hU0)
  linear_combination q1 + q2 + q3

/-- Figure 16.4 (scalar form): on `γ ∈ [0, 5/2]`, `β ∈ (0, 1]`, with a mean riskless rate below
4%, the equity premium is below `0.17%`, and the stock payoff spread `G_H(1 + v_H) − G_L(1 + v_L)`
is positive. -/
theorem mpf_core {β b0 b1 v0 v1 : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hb0 : 1 ≤ b0)
    (hb0' : b0 ≤ 10147 / 10000) (hb1 : 9048 / 10000 ≤ b1) (hb1' : b1 ≤ 1) (hv0 : 0 < v0)
    (hv1 : 0 < v1)
    (e0 : v0 = β * (11069 / 20000 * b0 * (4971 / 5000 * (1 + v0)) +
      (1 - 11069 / 20000) * b1 * (1301 / 1250 * (1 + v1))))
    (e1 : v1 = β * ((1 - 11069 / 20000) * b0 * (4971 / 5000 * (1 + v0)) +
      11069 / 20000 * b1 * (1301 / 1250 * (1 + v1))))
    (hrf : 1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
      1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1)) < 52 / 25) :
    1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0)) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1)) < 17 / 10000 ∧
    0 < 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) := by
  obtain ⟨hx1', hx10⟩ := mpf_core_bond hβ0 hβ1 hb0 hb0' hb1 hb1' hrf
  have hx0' : 955 / 1000 < β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) := by linarith
  have hw : ((1 + v1) - (1 + v0)) * (1 - β * (1069 / 10000) * (1301 / 1250) * b1) =
      β * (1069 / 10000) * (1301 / 1250 * b1 - 4971 / 5000 * b0) * (1 + v0) := by
    linear_combination e1 - e0
  obtain ⟨hwu, hwl⟩ := mpf_core_ratio hβ0 hβ1 hb0 hb0' hb1 hb1' (by linarith) hw
  have hv0' := mpf_core_v hβ0 (by linarith) (by linarith) (by norm_num) (by norm_num)
    (by linarith) hwl rfl hx0' e0
  have hv1' := mpf_core_v hβ0 (by linarith) (by linarith) (by norm_num) (by norm_num)
    (by linarith) hwl rfl hx1' e1
  have hU : 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) ≤ 5504 / 100000 * (1 + v0) := by
    linarith
  have hU0 : 0 < 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) := by linarith
  have hd : 0 ≤ b0 - b1 := by linarith
  have hT0 := mpf_core_term (e := 11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) hβ0 hβ1 hd
    hU0.le hU (by linarith) hv0 rfl hv0'
  have hT1 := mpf_core_term (e := (1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) hβ0 hβ1 hd
    hU0.le hU (by linarith) hv1 rfl hv1'
  refine ⟨?_, hU0⟩
  set K := 11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) * (5504 / 100000) / (9417 / 10000)
    with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) (by norm_num)) (by norm_num)
  have hKu : K ≤ 11069 / 20000 * (1 - 11069 / 20000) * (1099 / 10000) * (5504 / 100000) /
      (9417 / 10000) := by
    rw [hK]
    gcongr
    linarith
  have hS := mul_le_mul_of_nonneg_left hrf.le hK0
  have : K * (1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1))) +
      K * (1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1))) =
      K * (1 / (β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
        1 / (β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1))) := by ring
  linarith

/-- The growth states of Figure 16.4: `fn5G μ δ` with Table 16.1's `μ = 0.0175`,
`δ = 0.0233`. -/
noncomputable def mpfG : Fin 2 → ℝ := fn5G (7 / 400) (233 / 10000)

/-- The persistence of Figure 16.4: `2φ − 1 = 0.1069` (Table 16.1's autocorrelation). -/
noncomputable def mpfPhi : ℝ := (1 + 1069 / 10000) / 2

/-- AKMM, p. 487, Table 16.1 and fn. 5: the growth process of Figure 16.4. The three
parameters `μ, δ, φ` are chosen by GMM to match three moments (exactly identified): with
`μ = 0.0175`, `δ = 0.0233`, `2φ − 1 = 0.1069`, the mean, standard deviation and autocorrelation
of consumption growth are those of Table 16.1. -/
theorem mpf_primitives :
    fn5Mean ![1 / 2, 1 / 2] mpfG - 1 = 7 / 400 ∧
      fn5Second ![1 / 2, 1 / 2] mpfG - fn5Mean ![1 / 2, 1 / 2] mpfG ^ 2 = (233 / 10000) ^ 2 ∧
      (fn5Cross ![1 / 2, 1 / 2] mpfG (mpPi mpfPhi) - fn5Mean ![1 / 2, 1 / 2] mpfG ^ 2) /
        (fn5Second ![1 / 2, 1 / 2] mpfG - fn5Mean ![1 / 2, 1 / 2] mpfG ^ 2) = 1069 / 10000 := by
  refine ⟨fn5_mean _ _, fn5_var _ _, ?_⟩
  rw [mpfG, fn5_autocorr _ _ mpfPhi (by norm_num), mpfPhi]
  norm_num

/-- The primitives of Figure 16.4: `G_L = 0.9942`, `G_H = 1.0408`, `φ = 0.55345`. -/
theorem mpf_values : mpfG 0 = 4971 / 5000 ∧ mpfG 1 = 1301 / 1250 ∧ mpfPhi = 11069 / 20000 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [mpfG, fn5G, mpfPhi]

/-- `(x^{5/2})² = x⁵`. -/
theorem mpf_sq_rpow {x : ℝ} (hx : 0 < x) : (x ^ (5 / 2 : ℝ)) ^ 2 = x ^ 5 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

/-- For `γ ∈ [0, 5/2]`: `1 ≤ G_L^{−γ} ≤ 1.0147` (`G_L = 0.9942 < 1`). -/
theorem mpf_GL_bounds {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 5 / 2) :
    1 ≤ (4971 / 5000 : ℝ) ^ (-γ) ∧ (4971 / 5000 : ℝ) ^ (-γ) ≤ 10147 / 10000 := by
  refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num)
    (by linarith), le_trans (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
      (show -(5 / 2 : ℝ) ≤ -γ by linarith)) ?_⟩
  have hy := mpf_sq_rpow (show (0 : ℝ) < 4971 / 5000 by norm_num)
  have hyp : 0 < (4971 / 5000 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num)]
  have : (10000 / 10147 : ℝ) ≤ (4971 / 5000 : ℝ) ^ (5 / 2 : ℝ) := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h hyp.le (by norm_num : (2 : ℕ) ≠ 0)
    rw [hy] at this
    norm_num at this
  calc ((4971 / 5000 : ℝ) ^ (5 / 2 : ℝ))⁻¹ ≤ (10000 / 10147 : ℝ)⁻¹ :=
        inv_anti₀ (by norm_num) this
    _ = 10147 / 10000 := by norm_num

/-- For `γ ∈ [0, 5/2]`: `0.9048 ≤ G_H^{−γ} ≤ 1` (`G_H = 1.0408 > 1`). -/
theorem mpf_GH_bounds {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 5 / 2) :
    9048 / 10000 ≤ (1301 / 1250 : ℝ) ^ (-γ) ∧ (1301 / 1250 : ℝ) ^ (-γ) ≤ 1 := by
  refine ⟨le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (show -(5 / 2 : ℝ) ≤ -γ by linarith)),
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)⟩
  have hy := mpf_sq_rpow (show (0 : ℝ) < 1301 / 1250 by norm_num)
  have hyp : 0 < (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num)]
  have : (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) ≤ 10000 / 9048 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
    rw [hy] at this
    norm_num at this
  calc (9048 / 10000 : ℝ) = (10000 / 9048 : ℝ)⁻¹ := by norm_num
    _ ≤ ((1301 / 1250 : ℝ) ^ (5 / 2 : ℝ))⁻¹ := inv_anti₀ hyp this

/-- `γ ↦ x^{−γ}` is convex: on `[5/2, 100]` it lies below the chord (weighted AM–GM). -/
theorem mpf_rpow_convex {x γ : ℝ} (hx : 0 < x) (h0 : 5 / 2 ≤ γ) (h1 : γ ≤ 100) :
    x ^ (-γ) ≤ (100 - γ) / (195 / 2) * x ^ (-(5 / 2) : ℝ) +
      (γ - 5 / 2) / (195 / 2) * x ^ (-100 : ℝ) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (100 - γ) / (195 / 2))
    (w₂ := (γ - 5 / 2) / (195 / 2)) (p₁ := x ^ (-(5 / 2) : ℝ)) (p₂ := x ^ (-100 : ℝ))
    (by apply div_nonneg <;> linarith) (by apply div_nonneg <;> linarith)
    (Real.rpow_pos_of_pos hx _).le (Real.rpow_pos_of_pos hx _).le (by field_simp; ring)
  rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx] at h
  convert h using 2
  field_simp
  ring

/-- The chord endpoints: `G_L^{−5/2} + G_H^{−5/2} ≤ 1.9196` and
`G_L^{−100} + G_H^{−100} ≤ 1.8084`. -/
theorem mpf_far_bounds :
    (4971 / 5000 : ℝ) ^ (-(5 / 2) : ℝ) + (1301 / 1250 : ℝ) ^ (-(5 / 2) : ℝ) ≤ 19196 / 10000 ∧
      (4971 / 5000 : ℝ) ^ (-100 : ℝ) + (1301 / 1250 : ℝ) ^ (-100 : ℝ) ≤ 18084 / 10000 := by
  have hL := (mpf_GL_bounds (γ := 5 / 2) (by norm_num) le_rfl).2
  have hy := mpf_sq_rpow (show (0 : ℝ) < 1301 / 1250 by norm_num)
  have hyp : 0 < (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hH : (1301 / 1250 : ℝ) ^ (-(5 / 2) : ℝ) ≤ 9049 / 10000 := by
    rw [Real.rpow_neg (by norm_num)]
    have : (10000 / 9049 : ℝ) ≤ (1301 / 1250 : ℝ) ^ (5 / 2 : ℝ) := by
      by_contra h
      rw [not_le] at h
      have := pow_lt_pow_left₀ h hyp.le (by norm_num : (2 : ℕ) ≠ 0)
      rw [hy] at this
      norm_num at this
    calc ((1301 / 1250 : ℝ) ^ (5 / 2 : ℝ))⁻¹ ≤ (10000 / 9049 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) this
      _ = 9049 / 10000 := by norm_num
  refine ⟨by linarith, ?_⟩
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
  norm_num

/-- AKMM, (16.27), p. 487: the mean riskless rate `E[rᶠ] = ½ Σᵢ 1/pᶠᵢ − 1`. -/
theorem mpf_rf_mean {φ β γ : ℝ} {G : Fin 2 → ℝ} :
    ∑ i, ![1 / 2, 1 / 2] i * mpRf φ β γ G i =
      (1 / (β * (φ * G 0 ^ (-γ) + (1 - φ) * G 1 ^ (-γ))) +
        1 / (β * ((1 - φ) * G 0 ^ (-γ) + φ * G 1 ^ (-γ)))) / 2 - 1 := by
  obtain ⟨b0, b1⟩ := mpf_bond_eqs φ β γ G
  simp only [Fin.sum_univ_two, mpRf, b0, b1, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- The harmonic–arithmetic mean inequality `4/(x + y) ≤ 1/x + 1/y`. -/
theorem mpf_amhm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 4 / (x + y) ≤ 1 / x + 1 / y := by
  rw [div_add_div _ _ hx.ne' hy.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (x - y)]

/-- AKMM, Figure 16.4, p. 488: the region of the figure. For `β ∈ (0, 1]` and `γ ≤ 100`, a mean
riskless rate below 4% forces `γ < 5/2`: on `[5/2, 100]`, `G_L^{−γ} + G_H^{−γ} ≤ 1.9196` by
convexity, so the mean bond price is at most `0.9598` and `E[rᶠ] ≥ 1/0.9598 − 1 > 4%` (the mean of
`1/pᶠᵢ` is at least `1` over the mean of `pᶠᵢ`). -/
theorem mpf_gamma_lt {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hγ1 : γ ≤ 100)
    (hrf : ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi β γ mpfG i < 1 / 25) : γ < 5 / 2 := by
  obtain ⟨g0, g1, gφ⟩ := mpf_values
  rw [mpf_rf_mean, g0, g1, gφ] at hrf
  by_contra hγ
  rw [not_lt] at hγ
  set b0 := (4971 / 5000 : ℝ) ^ (-γ) with hb0
  set b1 := (1301 / 1250 : ℝ) ^ (-γ) with hb1
  have p0 : 0 < b0 := Real.rpow_pos_of_pos (by norm_num) _
  have p1 : 0 < b1 := Real.rpow_pos_of_pos (by norm_num) _
  have c0 := mpf_rpow_convex (x := 4971 / 5000) (by norm_num) hγ hγ1
  have c1 := mpf_rpow_convex (x := 1301 / 1250) (by norm_num) hγ hγ1
  obtain ⟨f1, f2⟩ := mpf_far_bounds
  have w1 : 0 ≤ (100 - γ) / (195 / 2) := by apply div_nonneg <;> linarith
  have w2 : 0 ≤ (γ - 5 / 2) / (195 / 2) := by apply div_nonneg <;> linarith
  have k1 := mul_le_mul_of_nonneg_left f1 w1
  have k2 := mul_le_mul_of_nonneg_left f2 w2
  have hsum : b0 + b1 ≤ 19196 / 10000 := by
    have : (100 - γ) / (195 / 2) + (γ - 5 / 2) / (195 / 2) = 1 := by field_simp; ring
    nlinarith
  have x0 : 0 < β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) := by positivity
  have x1 : 0 < β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) := by positivity
  have hm := mpf_amhm x0 x1
  have hxy : β * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) +
      β * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) ≤ 19196 / 10000 := by nlinarith
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) (by positivity) hxy
  norm_num at this
  linarith

/-- **AKMM, Figure 16.4, p. 488 (corrected).** In the Mehra–Prescott economy with the growth
process of Table 16.1, for every `β ∈ (0, 1]`, `γ ∈ [0, 100]` and positive price–dividend ratio
`v = βA(1 + v)` with mean riskless rate below 4%, the equity premium is below `0.17%`, and it is
positive when `γ > 0`. (The printed bound `0.1%` fails: `mpf_counterexample`.) -/
theorem mpf_premium_bound {β γ : ℝ} {v : Fin 2 → ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 100) (hv0 : ∀ i, 0 < v i)
    (hv : v = (β • mpA mpfPhi γ mpfG) *ᵥ (fun i => 1 + v i))
    (hrf : ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi β γ mpfG i < 1 / 25) :
    mpEquityPremium mpfPhi β γ mpfG (fun i j => mpfG j * (1 + v j) / v i - 1) < 17 / 10000 ∧
      (0 < γ → 0 < mpEquityPremium mpfPhi β γ mpfG (fun i j => mpfG j * (1 + v j) / v i - 1))
      := by
  have hγ := mpf_gamma_lt hβ0 hβ1 hγ1 hrf
  obtain ⟨g0, g1, gφ⟩ := mpf_values
  have hG : ∀ j, 0 < mpfG j := by
    intro j; fin_cases j <;> simp [g0, g1]
  obtain ⟨e0, e1⟩ := mpf_pd_eqs hG hv
  rw [mpf_premium_cov hG hβ0 (by rw [gφ]; norm_num) (by rw [gφ]; norm_num) hv0 hv]
  obtain ⟨c0, c1⟩ := mpf_bond_eqs mpfPhi 1 γ mpfG
  rw [mpf_rf_mean] at hrf
  simp only [Fin.sum_univ_two, c0, c1, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [g0, g1, gφ] at e0 e1 hrf ⊢
  obtain ⟨l0, l1⟩ := mpf_GL_bounds hγ0 hγ.le
  obtain ⟨h0, h1⟩ := mpf_GH_bounds hγ0 hγ.le
  have hrf' : 1 / (β * (11069 / 20000 * (4971 / 5000 : ℝ) ^ (-γ) +
      (1 - 11069 / 20000) * (1301 / 1250 : ℝ) ^ (-γ))) +
      1 / (β * ((1 - 11069 / 20000) * (4971 / 5000 : ℝ) ^ (-γ) +
        11069 / 20000 * (1301 / 1250 : ℝ) ^ (-γ))) < 52 / 25 := by linarith
  obtain ⟨hlt, hU⟩ := mpf_core hβ0 hβ1 l0 l1 h0 h1 (hv0 0) (hv0 1) e0 e1 hrf'
  refine ⟨by linarith, fun hγp => ?_⟩
  have hb : (1301 / 1250 : ℝ) ^ (-γ) < (4971 / 5000 : ℝ) ^ (-γ) := by
    have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg (x := 4971 / 5000) (z := -γ)
      (by norm_num) (by norm_num) (by linarith)
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := 1301 / 1250) (z := -γ)
      (by norm_num) (by linarith)
    linarith
  have hd : 0 < (4971 / 5000 : ℝ) ^ (-γ) - (1301 / 1250 : ℝ) ^ (-γ) := by linarith
  have p0 : 0 < (4971 / 5000 : ℝ) ^ (-γ) := by linarith
  have p1 : 0 < (1301 / 1250 : ℝ) ^ (-γ) := by linarith
  have q0 := hv0 0
  have q1 := hv0 1
  positivity

/-- `(x^{9/4})⁴ = x⁹`. -/
theorem mpf_pow4_rpow {x : ℝ} (hx : 0 < x) : (x ^ (9 / 4 : ℝ)) ^ 4 = x ^ 9 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  norm_num

/-- Enclosures of `G_L^{−9/4}` and `G_H^{−9/4}` to `10⁻⁷`. -/
theorem mpf_ce_bounds :
    10131740 / 10000000 ≤ (4971 / 5000 : ℝ) ^ (-(9 / 4) : ℝ) ∧
      (4971 / 5000 : ℝ) ^ (-(9 / 4) : ℝ) ≤ 10131741 / 10000000 ∧
      9139524 / 10000000 ≤ (1301 / 1250 : ℝ) ^ (-(9 / 4) : ℝ) ∧
      (1301 / 1250 : ℝ) ^ (-(9 / 4) : ℝ) ≤ 9139525 / 10000000 := by
  have hL := mpf_pow4_rpow (show (0 : ℝ) < 4971 / 5000 by norm_num)
  have hH := mpf_pow4_rpow (show (0 : ℝ) < 1301 / 1250 by norm_num)
  have pL : 0 < (4971 / 5000 : ℝ) ^ (9 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have pH : 0 < (1301 / 1250 : ℝ) ^ (9 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
  have a1 : (4971 / 5000 : ℝ) ^ (9 / 4 : ℝ) ≤ 10000000 / 10131740 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [hL] at this
    norm_num at this
  have a2 : 10000000 / 10131741 ≤ (4971 / 5000 : ℝ) ^ (9 / 4 : ℝ) := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h pL.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [hL] at this
    norm_num at this
  have a3 : (1301 / 1250 : ℝ) ^ (9 / 4 : ℝ) ≤ 10000000 / 9139524 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [hH] at this
    norm_num at this
  have a4 : 10000000 / 9139525 ≤ (1301 / 1250 : ℝ) ^ (9 / 4 : ℝ) := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h pH.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [hH] at this
    norm_num at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (10131740 / 10000000 : ℝ) = (10000000 / 10131740 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := inv_anti₀ pL a1
  · calc ((4971 / 5000 : ℝ) ^ (9 / 4 : ℝ))⁻¹ ≤ (10000000 / 10131741 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) a2
      _ = _ := by norm_num
  · calc (9139524 / 10000000 : ℝ) = (10000000 / 9139524 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := inv_anti₀ pH a3
  · calc ((1301 / 1250 : ℝ) ^ (9 / 4 : ℝ))⁻¹ ≤ (10000000 / 9139525 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) a4
      _ = _ := by norm_num

/-- The counterexample of Figure 16.4 (scalar form): the premium at `γ = 9/4`, `β = 1`
exceeds `0.1%`. -/
theorem mpf_ce_ep {b0 b1 D n0 n1 v0 v1 : ℝ} (l0 : 10131740 / 10000000 ≤ b0)
    (u0 : b0 ≤ 10131741 / 10000000) (l1 : 9139524 / 10000000 ≤ b1)
    (u1 : b1 ≤ 9139525 / 10000000) (hDp : 0 < D)
    (hn0 : n0 = 1 - 1069 / 10000 * (1301 / 1250 * b1))
    (hn1 : n1 = 1 - 1069 / 10000 * (4971 / 5000 * b0))
    (d0l : 87983 / 100000 ≤ n0 - D) (d0u : n0 - D ≤ 87984 / 100000)
    (d1l : 87384 / 100000 ≤ n1 - D) (d1u : n1 - D ≤ 87385 / 100000)
    (w0 : 1 + v0 = n0 / D) (w1 : 1 + v1 = n1 / D) (v0e : v0 = (n0 - D) / D)
    (v1e : v1 = (n1 - D) / D) :
    1 / 1000 < 1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0)) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1)) := by
  have e0p : 0 < 11069 / 20000 * b0 + (1 - 11069 / 20000) * b1 := by linarith
  have e1p : 0 < (1 - 11069 / 20000) * b0 + 11069 / 20000 * b1 := by linarith
  have hX : 1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0) =
      (1301 / 1250 * n1 - 4971 / 5000 * n0) / D := by
    rw [w0, w1]; ring
  have hXv : 1301 / 1250 * n1 - 4971 / 5000 * n0 = 466 / 10000 -
      1069 / 10000 * (4971 / 5000) * (1301 / 1250) * (b0 - b1) := by
    rw [hn0, hn1]; ring
  have hXl : 3562 / 100000 ≤ 1301 / 1250 * n1 - 4971 / 5000 * n0 := by rw [hXv]; linarith
  have t0 : 11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
      ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0) =
      11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * n1 - 4971 / 5000 * n0) /
      ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * (n0 - D)) := by
    rw [hX, v0e]
    field_simp
  have t1 : 11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
      (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1) =
      11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
      (1301 / 1250 * n1 - 4971 / 5000 * n0) /
      (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * (n1 - D)) := by
    rw [hX, v1e]
    field_simp
  rw [t0, t1]
  have hdl : 9922 / 100000 ≤ b0 - b1 := by linarith
  have hnum : 11069 / 20000 * (1 - 11069 / 20000) * (9922 / 100000) * (3562 / 100000) ≤
      11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * n1 - 4971 / 5000 * n0) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul hdl hXl (by norm_num) (by linarith))
      (by norm_num : (0 : ℝ) ≤ 11069 / 20000 * (1 - 11069 / 20000))
    linear_combination this
  have den0 : (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * (n0 - D) ≤
      96887 / 100000 * (87984 / 100000) :=
    mul_le_mul (by linarith) d0u (by linarith) (by norm_num)
  have den1 : ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * (n1 - D) ≤
      95826 / 100000 * (87385 / 100000) :=
    mul_le_mul (by linarith) d1u (by linarith) (by norm_num)
  have f0 := div_le_div₀ (by positivity) hnum (by positivity) den0
  have f1 := div_le_div₀ (by positivity) hnum (by positivity) den1
  have : (1 / 1000 : ℝ) < 1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (9922 / 100000) *
      (3562 / 100000) / (96887 / 100000 * (87984 / 100000))) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (9922 / 100000) * (3562 / 100000) /
      (95826 / 100000 * (87385 / 100000))) := by norm_num
  linarith

/-- The counterexample of Figure 16.4 (scalar form): at `γ = 9/4`, `β = 1`, the vector
`vᵢ = nᵢ/D − 1` (Cramer's rule for `(I − A)(1 + v) = 𝟙`) is positive and solves `v = A(1 + v)`; the
mean riskless rate is below 4% and the equity premium above `0.1%`. -/
theorem mpf_ce_core {b0 b1 D v0 v1 : ℝ} (l0 : 10131740 / 10000000 ≤ b0)
    (u0 : b0 ≤ 10131741 / 10000000) (l1 : 9139524 / 10000000 ≤ b1)
    (u1 : b1 ≤ 9139525 / 10000000)
    (hD : D = 1 - 11069 / 20000 * (4971 / 5000 * b0 + 1301 / 1250 * b1) +
      1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1))
    (hv0 : v0 = (1 - 1069 / 10000 * (1301 / 1250 * b1)) / D - 1)
    (hv1 : v1 = (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1) :
    0 < v0 ∧ 0 < v1 ∧
    v0 = 1 * (11069 / 20000 * b0 * (4971 / 5000 * (1 + v0)) +
      (1 - 11069 / 20000) * b1 * (1301 / 1250 * (1 + v1))) ∧
    v1 = 1 * ((1 - 11069 / 20000) * b0 * (4971 / 5000 * (1 + v0)) +
      11069 / 20000 * b1 * (1301 / 1250 * (1 + v1))) ∧
    1 / (1 * (11069 / 20000 * b0 + (1 - 11069 / 20000) * b1)) +
      1 / (1 * ((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1)) < 52 / 25 ∧
    1 / 1000 < 1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        ((11069 / 20000 * b0 + (1 - 11069 / 20000) * b1) * v0)) +
      1 / 2 * (11069 / 20000 * (1 - 11069 / 20000) * (b0 - b1) *
        (1301 / 1250 * (1 + v1) - 4971 / 5000 * (1 + v0)) /
        (((1 - 11069 / 20000) * b0 + 11069 / 20000 * b1) * v1)) := by
  have pp := mul_le_mul l0 l1 (by norm_num) (by linarith)
  have qq := mul_le_mul u0 u1 (by linarith) (by norm_num)
  have hDl : 18476 / 1000000 ≤ D := by rw [hD]; linarith
  have hDp : 0 < D := by linarith
  set n0 := 1 - 1069 / 10000 * (1301 / 1250 * b1) with hn0
  set n1 := 1 - 1069 / 10000 * (4971 / 5000 * b0) with hn1
  have d0 : n0 - D = 11069 / 20000 * (4971 / 5000 * b0) + (1 - 11069 / 20000) *
      (1301 / 1250 * b1) - 1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1) := by
    rw [hD, hn0]; ring
  have d1 : n1 - D = 11069 / 20000 * (1301 / 1250 * b1) + (1 - 11069 / 20000) *
      (4971 / 5000 * b0) - 1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1) := by
    rw [hD, hn1]; ring
  have d0l : 87983 / 100000 ≤ n0 - D := by rw [d0]; linarith
  have d0u : n0 - D ≤ 87984 / 100000 := by rw [d0]; linarith
  have d1l : 87384 / 100000 ≤ n1 - D := by rw [d1]; linarith
  have d1u : n1 - D ≤ 87385 / 100000 := by rw [d1]; linarith
  have w0 : 1 + v0 = n0 / D := by rw [hv0]; ring
  have w1 : 1 + v1 = n1 / D := by rw [hv1]; ring
  have v0e : v0 = (n0 - D) / D := by rw [hv0]; field_simp
  have v1e : v1 = (n1 - D) / D := by rw [hv1]; field_simp
  have v0p : 0 < v0 := by rw [v0e]; exact div_pos (by linarith) hDp
  have v1p : 0 < v1 := by rw [v1e]; exact div_pos (by linarith) hDp
  have key0 : n0 - D = 11069 / 20000 * b0 * (4971 / 5000 * n0) +
      (1 - 11069 / 20000) * b1 * (1301 / 1250 * n1) := by rw [hD, hn0, hn1]; ring
  have key1 : n1 - D = (1 - 11069 / 20000) * b0 * (4971 / 5000 * n0) +
      11069 / 20000 * b1 * (1301 / 1250 * n1) := by rw [hD, hn0, hn1]; ring
  refine ⟨v0p, v1p, ?_, ?_, ?_, mpf_ce_ep l0 u0 l1 u1 hDp hn0 hn1 d0l d0u d1l d1u w0 w1 v0e v1e⟩
  · rw [w0, w1, v0e, key0]; field_simp
  · rw [w0, w1, v1e, key1]; field_simp
  · rw [one_mul, one_mul]
    have i0 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 968866 / 1000000)
      (show 968866 / 1000000 ≤ 11069 / 20000 * b0 + (1 - 11069 / 20000) * b1 by linarith)
    have i1 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 958259 / 1000000)
      (show 958259 / 1000000 ≤ (1 - 11069 / 20000) * b0 + 11069 / 20000 * b1 by linarith)
    have : 1 / (968866 / 1000000 : ℝ) + 1 / (958259 / 1000000) < 52 / 25 := by norm_num
    linarith

/-- AKMM, p. 486: the two scalar equations give `v = βA(1 + v)`. -/
theorem mpf_pd_of_eqs {φ β γ : ℝ} {G v : Fin 2 → ℝ} (hG : ∀ j, 0 < G j)
    (e0 : v 0 = β * (φ * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + (1 - φ) * G 1 ^ (-γ) *
      (G 1 * (1 + v 1))))
    (e1 : v 1 = β * ((1 - φ) * G 0 ^ (-γ) * (G 0 * (1 + v 0)) + φ * G 1 ^ (-γ) *
      (G 1 * (1 + v 1)))) :
    v = (β • mpA φ γ G) *ᵥ (fun i => 1 + v i) := by
  funext i
  fin_cases i
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, mpA, Matrix.of_apply,
      mpPi, smul_eq_mul, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1), Fin.zero_eta]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination e0
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, mpA, Matrix.of_apply,
      mpPi, smul_eq_mul, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1),
      Fin.mk_one]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination e1

/-- **AKMM, Figure 16.4, p. 488: the printed bound fails.** With the growth process of
Table 16.1, at `β = 1`, `γ = 9/4` (inside the figure's range) the price–dividend ratio
`v = (I − A)⁻¹A𝟙` exists (`ρ(A) < 1`, so by `mp_pd_unique` it is the only solution), the mean
riskless rate is below 4% (about 3.78%) and the equity premium exceeds `0.1%` (about 0.103%). -/
theorem mpf_counterexample :
    ∃ v : Fin 2 → ℝ, specRad ((1 : ℝ) • mpA mpfPhi (9 / 4) mpfG) < 1 ∧ (∀ i, 0 < v i) ∧
      v = ((1 : ℝ) • mpA mpfPhi (9 / 4) mpfG) *ᵥ (fun i => 1 + v i) ∧
      ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi 1 (9 / 4) mpfG i < 1 / 25 ∧
      1 / 1000 < mpEquityPremium mpfPhi 1 (9 / 4) mpfG
        (fun i j => mpfG j * (1 + v j) / v i - 1) := by
  obtain ⟨g0, g1, gφ⟩ := mpf_values
  have hG : ∀ j, 0 < mpfG j := by
    intro j; fin_cases j <;> simp [g0, g1]
  obtain ⟨l0, u0, l1, u1⟩ := mpf_ce_bounds
  set b0 := (4971 / 5000 : ℝ) ^ (-(9 / 4) : ℝ) with hb0
  set b1 := (1301 / 1250 : ℝ) ^ (-(9 / 4) : ℝ) with hb1
  set D := 1 - 11069 / 20000 * (4971 / 5000 * b0 + 1301 / 1250 * b1) +
      1069 / 10000 * (4971 / 5000 * b0) * (1301 / 1250 * b1) with hD
  obtain ⟨p0, p1, e0, e1, hr, hep⟩ := mpf_ce_core (v0 := (1 - 1069 / 10000 * (1301 / 1250 * b1))
    / D - 1) (v1 := (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1) l0 u0 l1 u1 hD rfl rfl
  set v : Fin 2 → ℝ := ![(1 - 1069 / 10000 * (1301 / 1250 * b1)) / D - 1,
    (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1] with hvdef
  have hv0 : ∀ i, 0 < v i := by
    intro i; fin_cases i
    · exact p0
    · exact p1
  have hv : v = ((1 : ℝ) • mpA mpfPhi (9 / 4) mpfG) *ᵥ (fun i => 1 + v i) := by
    apply mpf_pd_of_eqs hG
    · rw [g0, g1, gφ]; exact e0
    · rw [g0, g1, gφ]; exact e1
  refine ⟨v, ?_, hv0, hv, ?_, ?_⟩
  · refine mp_specRad_lt_one (φ := mpfPhi) (γ := 9 / 4) (β := 1) (G := mpfG) (C := 99 / 100)
      (by rw [gφ]; norm_num) (by rw [gφ]; norm_num)
      (by norm_num) hG (by norm_num) (fun i => ?_)
    fin_cases i
    · simp only [Fin.sum_univ_two, mpPi, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1)]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, g0, g1, gφ, Fin.zero_eta]
      rw [← hb0, ← hb1]
      linarith
    · simp only [Fin.sum_univ_two, mpPi, mpf_rpow_one_sub (hG 0), mpf_rpow_one_sub (hG 1)]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, g0, g1, gφ, Fin.mk_one]
      rw [← hb0, ← hb1]
      linarith
  · rw [mpf_rf_mean, g0, g1, gφ]
    linarith
  · rw [mpf_premium_cov hG one_pos (by rw [gφ]; norm_num) (by rw [gφ]; norm_num) hv0 hv]
    obtain ⟨c0, c1⟩ := mpf_bond_eqs mpfPhi 1 (9 / 4) mpfG
    simp only [Fin.sum_univ_two, c0, c1, one_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have hva : v 0 = (1 - 1069 / 10000 * (1301 / 1250 * b1)) / D - 1 := rfl
    have hvb : v 1 = (1 - 1069 / 10000 * (4971 / 5000 * b0)) / D - 1 := rfl
    rw [g0, g1, gφ, ← hb0, ← hb1, hva, hvb]
    linarith

/-- **AKMM, Figure 16.4, p. 488, as printed, is false**: it is not true that every equilibrium
of the figure's range (`β ∈ (0, 1]`, `γ ∈ [0, 100]`) with mean riskless rate below 4% has an equity
premium below `0.1%`. -/
theorem mpf_fig_16_4_printed_false :
    ¬ ∀ (β γ : ℝ) (v : Fin 2 → ℝ), 0 < β → β ≤ 1 → 0 ≤ γ → γ ≤ 100 → (∀ i, 0 < v i) →
      v = (β • mpA mpfPhi γ mpfG) *ᵥ (fun i => 1 + v i) →
      ∑ i, ![1 / 2, 1 / 2] i * mpRf mpfPhi β γ mpfG i < 1 / 25 →
      mpEquityPremium mpfPhi β γ mpfG (fun i j => mpfG j * (1 + v j) / v i - 1) < 1 / 1000 := by
  intro h
  obtain ⟨v, -, hv0, hv, hrf, hep⟩ := mpf_counterexample
  have := h 1 (9 / 4) v one_pos le_rfl (by norm_num) (by norm_num) hv0 hv hrf
  linarith

end AKMM.AssetPrices
