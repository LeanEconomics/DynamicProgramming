/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesian.FSZLB
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Government purchases and welfare

Miao, §19.3, pp. 657–661, (19.62)–(19.65), the optimal crisis purchases, and Exercise 19.5
(p. 669).

* (19.63): the first-order condition `u'(Y − G) = g'(G)` at an optimum (`eq_19_63`); the
  welfare derivative `(u' − ṽ')dY/dG + g' − u'` (`fs_welfare_deriv`), whose first term vanishes
  in the neoclassical model (`fs_welfare_deriv_neoclassical`); without `g` the derivative is
  `−u' < 0` (`fs_welfare_no_g`).
* Without the zero bound the first best `π = Ŷ − ΓĜ = Ĝ = 0` is feasible, minimises (19.64), and
  is implemented by the Taylor rule (`fs_first_best`).
* (19.65): the value of (19.64) in the two-state equilibrium (`eq_19_65`).
* The optimal `Ĝ_L`: the loss is `ξx² + λ_gĜ²` with `x = Ŷ_L − ΓĜ_L` (`fs_loss_reduced`); the
  unique minimiser `Ĝ*_L = −ξ(ϑ_G − Γ)ϑ_r r_L/(ξ(ϑ_G − Γ)² + λ_g)` (`fs_optimal_GL`), positive for
  `r_L < 0` (`fs_optimal_GL_pos`), with `ξ = (κ/(1 − βμ))² + λ_y` (the book prints `γ_y` for
  `λ_y` in `ξ`, see below).
* **Correction (zero output gap).** The level of `Ĝ_L` that eliminates the output gap and the
  deflation is `ϑ_r|r_L|/(ϑ_G − Γ)` (`fs_zero_gap_GL`), not the printed `ϑ_r|r_L|/ϑ_G`; the latter
  keeps `Ŷ_L = 0` but leaves the gap `Γϑ_r r_L/ϑ_G < 0` and deflation (`fs_zero_gap_printed`). The
  optimum lies strictly below the zero-gap level when `λ_g > 0` (`fs_optimal_GL_lt_zero_gap`), as
  in Figure 19.7 (`fs_fig_19_7`; at the printed level the inequality would fail).
* **Corrections (weights).** `λ_y = κ/ε` with `ε` the elasticity of substitution (the book writes
  `κ/θ`, using Woodford's `θ` for `ε`, while `θ` is the Calvo parameter elsewhere; Figure 19.7's
  `θ = 12.77` is `ε`); `λ_g = λ_yΓ(η_g/η_u + 1 − Γ)` (the book prints `Γγ_y` for `Γλ_y`); and
  `η_g = −Ȳg''/g'` (the elasticity with respect to `G/Ȳ`, which is what case B, `η_g = 4η_u`,
  needs). Positivity: `fs_weights_pos`.
* **Exercise 19.5** (19.64) by second-order approximation:
  - a general second-order Taylor lemma (`fs_taylor2`);
  - the flexible-price period utility `u(Y − G) + g(G) − ṽ(Y)` around the efficient steady state
    (`u' = g' = ṽ'`): zero first derivative and second derivative
    `−u'Ȳ(η_u + η_v)[(Ŷ − ΓĜ)² + Γ(η_g/η_u + 1 − Γ)Ĝ²]` along every direction
    (`ex_19_5_flex`, with the `o(s²)` remainder);
  - the price-dispersion index `Δ = θΔ₋₁e^{επ} + (1 − θ)((1 − θe^{(ε−1)π})/(1 − θ))^{ε/(ε−1)}`:
    `Δ = 1`, zero first derivative and second derivative `εθ/(1 − θ)` in `π` at `Δ₋₁ = 1`
    (`ex_19_5_dispersion`), and `Δ − 1 = θ(Δ₋₁ − 1)` at `π = 0` (`fs_dispersion_lin`);
  - the labour cost of dispersion `ṽ(YΔ)`: derivative `ṽ'(Ȳ)Ȳ` in `Δ` (`fs_labor_dispersion`);
  - the discounted dispersion `Σβᵗd_t = c/(1 − βθ)·Σβᵗπ_t²` for `d_t = θd_{t−1} + cπ_t²`
    (`fs_dispersion_sum`);
  - the assembly (`ex_19_5`): the discounted sum of the second-order terms is
    `−(u'Ȳε/(2κ̃))·Σβᵗ[π_t² + λ_y(Ŷ_t − ΓĜ_t)² + λ_gĜ_t²]`, `κ̃ = (1 − θ)(1 − βθ)/θ`, so welfare
    varies inversely with (19.64).
  The approximation argument itself (dropping third-order terms, in particular
  `θ(e^{επ} − 1)(Δ₋₁ − 1)`) is the book's; each step is proved as a precise statement.
-/

namespace Miao.NewKeynesian

open Filter Topology

/-- Miao, (19.63), p. 657: at an optimum of `G ↦ u(Y − G) + g(G)` (output `Y` given),
`u'(Y − G) = g'(G)`. -/
theorem eq_19_63 {u u1 g g1 : ℝ → ℝ} {Y G : ℝ} (hu : HasDerivAt u (u1 (Y - G)) (Y - G))
    (hg : HasDerivAt g (g1 G) G) (hmax : IsLocalMax (fun G' => u (Y - G') + g G') G) :
    u1 (Y - G) = g1 G := by
  have hc : HasDerivAt (fun G' : ℝ => Y - G') (-1) G := by
    simpa using (hasDerivAt_id G).const_sub Y
  have h := (hu.comp (h := fun G' : ℝ => Y - G') G hc).add hg
  have := hmax.hasDerivAt_eq_zero h
  linarith

/-- Miao, p. 657: the welfare effect of government purchases. With `W(G) = u(Y(G) − G) + g(G) −
ṽ(Y(G))`, `dW/dG = (u' − ṽ')dY/dG + g' − u'`, so utility increases iff this is positive. -/
theorem fs_welfare_deriv {u u1 g g1 vt vt1 Ysol : ℝ → ℝ} {G Y' : ℝ}
    (hu : HasDerivAt u (u1 (Ysol G - G)) (Ysol G - G)) (hg : HasDerivAt g (g1 G) G)
    (hv : HasDerivAt vt (vt1 (Ysol G)) (Ysol G)) (hY : HasDerivAt Ysol Y' G) :
    HasDerivAt (fun G' => u (Ysol G' - G') + g G' - vt (Ysol G'))
      ((u1 (Ysol G - G) - vt1 (Ysol G)) * Y' + g1 G - u1 (Ysol G - G)) G := by
  have hC : HasDerivAt (fun G' => Ysol G' - G') (Y' - 1) G := hY.sub (hasDerivAt_id G)
  have h1 := hu.comp (h := fun G' => Ysol G' - G') G hC
  have h2 := hv.comp G hY
  refine ((h1.add hg).sub h2).congr_deriv ?_
  ring

/-- Miao, p. 657: "In the neoclassical model, the first term in the above expression is zero":
with (19.40) `u'(Y − G) = ṽ'(Y)`, `dW/dG = g' − u'`. -/
theorem fs_welfare_deriv_neoclassical {u1 g1 vt1 Ysol : ℝ → ℝ} {G Y' : ℝ}
    (h40 : u1 (Ysol G - G) = vt1 (Ysol G)) :
    (u1 (Ysol G - G) - vt1 (Ysol G)) * Y' + g1 G - u1 (Ysol G - G) = g1 G - u1 (Ysol G - G) := by
  rw [h40]
  ring

/-- Miao, p. 657: without intrinsic value of purchases (`g = 0`), in the neoclassical model
`dW/dG = −u' < 0`: welfare falls with `G`, so optimal purchases are as low as possible. -/
theorem fs_welfare_no_g {u u1 vt vt1 Ysol : ℝ → ℝ} {G Y' : ℝ}
    (hu : HasDerivAt u (u1 (Ysol G - G)) (Ysol G - G))
    (hv : HasDerivAt vt (vt1 (Ysol G)) (Ysol G)) (hY : HasDerivAt Ysol Y' G)
    (h40 : u1 (Ysol G - G) = vt1 (Ysol G)) (hpos : 0 < u1 (Ysol G - G)) :
    HasDerivAt (fun G' => u (Ysol G' - G') + (fun _ => (0 : ℝ)) G' - vt (Ysol G'))
      (-u1 (Ysol G - G)) G ∧ -u1 (Ysol G - G) < 0 := by
  refine ⟨(fs_welfare_deriv (g1 := fun _ => 0) hu (hasDerivAt_const G 0) hv hY).congr_deriv ?_,
    by linarith⟩
  rw [h40]
  ring

/-- The period loss in (19.64): `π² + λ_y(Ŷ − ΓĜ)² + λ_gĜ²`. -/
def fs_loss (lamy lamg Γ infl Y G : ℝ) : ℝ := infl ^ 2 + lamy * (Y - Γ * G) ^ 2 + lamg * G ^ 2

/-- Miao, pp. 658–659: if the zero bound never binds, the first best is feasible: `π_t = 0`,
`Ŷ_t = Ĝ_t = 0`, `i_t = r̄` satisfies (19.48)–(19.50) (it is implemented by the Taylor rule), it
gives zero loss, and every path has nonnegative loss, zero only if `π = Ŷ − ΓĜ = Ĝ = 0`
(`λ_y, λ_g > 0`). -/
theorem fs_first_best {κ β σ Γ φπ φy rb lamy lamg : ℝ} (hy : 0 < lamy) (hg : 0 < lamg) :
    fs_TaylorEqm κ β σ Γ φπ φy rb (fun _ => 0) (fun _ => 0) (fun _ => rb) (fun _ => 0) ∧
      fs_loss lamy lamg Γ 0 0 0 = 0 ∧
      ∀ infl Y G, 0 ≤ fs_loss lamy lamg Γ infl Y G ∧
        (fs_loss lamy lamg Γ infl Y G = 0 → infl = 0 ∧ Y - Γ * G = 0 ∧ G = 0) := by
  refine ⟨fun t => ⟨by simp, by simp, by simp⟩, by simp [fs_loss], fun infl Y G => ⟨?_, ?_⟩⟩
  · unfold fs_loss
    positivity
  · intro h
    unfold fs_loss at h
    have h1 := sq_nonneg infl
    have h2 := mul_nonneg hy.le (sq_nonneg (Y - Γ * G))
    have h3 := mul_nonneg hg.le (sq_nonneg G)
    refine ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith), ?_, ?_⟩
    · have : (Y - Γ * G) ^ 2 = 0 := by
        have : lamy * (Y - Γ * G) ^ 2 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hy.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    · have : G ^ 2 = 0 := by
        have : lamg * G ^ 2 = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hg.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

/-- Miao, (19.65), p. 659: in the two-state equilibrium the loss is `L_L` in the crisis
(probability `μᵗ` at date `t`) and `0` afterwards, so (19.64) equals
`(π_L² + λ_y(Ŷ_L − ΓĜ_L)² + λ_gĜ_L²)/(1 − βμ)`. -/
theorem eq_19_65 {β μ lamy lamg Γ πL YL gL : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1) :
    ∑' t : ℕ, β ^ t * (μ ^ t * fs_loss lamy lamg Γ πL YL gL +
        (1 - μ ^ t) * fs_loss lamy lamg Γ 0 0 0) =
      1 / (1 - β * μ) * fs_loss lamy lamg Γ πL YL gL := by
  have hβμ0 : 0 ≤ β * μ := by positivity
  have hβμ1 : β * μ < 1 := by nlinarith
  have : ∀ t : ℕ, β ^ t * (μ ^ t * fs_loss lamy lamg Γ πL YL gL +
      (1 - μ ^ t) * fs_loss lamy lamg Γ 0 0 0) = fs_loss lamy lamg Γ πL YL gL * (β * μ) ^ t :=
    fun t => by
      simp only [fs_loss]
      rw [mul_pow]
      ring
  simp_rw [this, tsum_mul_left, tsum_geometric_of_lt_one hβμ0 hβμ1]
  ring

/-- `ξ = (κ/(1 − βμ))² + λ_y` (Miao, p. 659, with `λ_y` for the printed `γ_y`). -/
noncomputable def fs_xi (β κ μ lamy : ℝ) : ℝ := (κ / (1 - β * μ)) ^ 2 + lamy

/-- Miao, p. 659: with (19.56) and (19.60), the crisis loss is `ξx² + λ_gĜ_L²` where
`x = Ŷ_L − ΓĜ_L = ϑ_r r_L + (ϑ_G − Γ)Ĝ_L`. -/
theorem fs_loss_reduced {β κ σ μ Γ lamy lamg rL gL YL πL : ℝ}
    (h60 : YL = fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ * gL)
    (h56 : πL = κ / (1 - β * μ) * (YL - Γ * gL)) :
    fs_loss lamy lamg Γ πL YL gL = fs_xi β κ μ lamy *
      (fs_thetaR β κ σ μ * rL + (fs_thetaG β κ σ μ Γ - Γ) * gL) ^ 2 + lamg * gL ^ 2 := by
  rw [h56, h60]
  unfold fs_loss fs_xi
  ring

/-- Miao, p. 659: the optimal crisis purchases. For `ξ > 0`, `λ_g > 0`, the quadratic loss
`F(G) = ξ(ϑ_r r_L + (ϑ_G − Γ)G)² + λ_gG²` has the unique minimiser
`G* = −ξ(ϑ_G − Γ)ϑ_r r_L/(ξ(ϑ_G − Γ)² + λ_g)`; indeed
`F(G) − F(G*) = (ξ(ϑ_G − Γ)² + λ_g)(G − G*)²`. -/
theorem fs_optimal_GL {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg) (G : ℝ) :
    ξ * (tr * rL + (tg - Γ) * G) ^ 2 + lamg * G ^ 2 -
      (ξ * (tr * rL + (tg - Γ) * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL)) ^ 2 +
        lamg * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2) =
      (ξ * (tg - Γ) ^ 2 + lamg) *
        (G - -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 := by
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  field_simp
  ring

/-- Miao, p. 659: the minimiser is unique: `F(G) ≥ F(G*)`, with equality iff `G = G*`. -/
theorem fs_optimal_GL_unique {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg) (G : ℝ) :
    ξ * (tr * rL + (tg - Γ) * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL)) ^ 2 +
        lamg * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 ≤
      ξ * (tr * rL + (tg - Γ) * G) ^ 2 + lamg * G ^ 2 ∧
    (ξ * (tr * rL + (tg - Γ) * G) ^ 2 + lamg * G ^ 2 =
        ξ * (tr * rL + (tg - Γ) * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL)) ^ 2 +
        lamg * (-(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 ↔
      G = -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) := by
  have h := fs_optimal_GL (tr := tr) (tg := tg) (Γ := Γ) (rL := rL) hξ hg G
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  constructor
  · nlinarith [mul_nonneg hd.le (sq_nonneg (G - -(ξ * (tg - Γ) * tr) /
      (ξ * (tg - Γ) ^ 2 + lamg) * rL))]
  · constructor
    · intro he
      have : (ξ * (tg - Γ) ^ 2 + lamg) *
          (G - -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL) ^ 2 = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hd.ne'
      exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    · intro he
      rw [he]

/-- Miao, p. 659: `Ĝ*_L > 0` when `r_L < 0`, `ϑ_r > 0`, `ϑ_G > Γ`, `ξ, λ_g > 0`. -/
theorem fs_optimal_GL_pos {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg) (htr : 0 < tr)
    (htg : Γ < tg) (hr : rL < 0) :
    0 < -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL := by
  have h1 : 0 < ξ * (tg - Γ) * tr := mul_pos (mul_pos hξ (sub_pos.2 htg)) htr
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos h1) hd) hr

/-- **Correction** (Miao, pp. 660–661): the purchases that eliminate the output gap,
`Ĝ_L = ϑ_r|r_L|/(ϑ_G − Γ)` (`r_L < 0`), give `Ŷ_L − ΓĜ_L = 0` and `π_L = 0` in (19.56), (19.60). -/
theorem fs_zero_gap_GL {β κ σ μ Γ rL : ℝ} (htg : fs_thetaG β κ σ μ Γ - Γ ≠ 0) (hr : rL < 0) :
    fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) -
      Γ * (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) = 0 ∧
    κ / (1 - β * μ) * (fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) -
      Γ * (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ))) = 0 := by
  have h0 : fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) -
      Γ * (fs_thetaR β κ σ μ * |rL| / (fs_thetaG β κ σ μ Γ - Γ)) = 0 := by
    rw [abs_of_neg hr]
    field_simp
    ring
  exact ⟨h0, by rw [h0, mul_zero]⟩

/-- **Counterexample to the printed zero-gap level** (Miao, p. 660): at `Ĝ_L = ϑ_r|r_L|/ϑ_G`
output is at its steady state, `Ŷ_L = 0`, but the output gap is `Γϑ_r r_L/ϑ_G < 0` (and so
`π_L < 0`) when `r_L < 0`, `ϑ_r, ϑ_G, Γ > 0`, `βμ < 1`, `κ > 0`. -/
theorem fs_zero_gap_printed {β κ σ μ Γ rL : ℝ} (htr : 0 < fs_thetaR β κ σ μ)
    (htg : 0 < fs_thetaG β κ σ μ Γ) (hΓ : 0 < Γ) (hr : rL < 0) (hκ : 0 < κ)
    (hD : 0 < 1 - β * μ) :
    fs_thetaR β κ σ μ * rL + fs_thetaG β κ σ μ Γ *
        (fs_thetaR β κ σ μ * |rL| / fs_thetaG β κ σ μ Γ) = 0 ∧
      0 - Γ * (fs_thetaR β κ σ μ * |rL| / fs_thetaG β κ σ μ Γ) =
        Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ ∧
      Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ < 0 ∧
      κ / (1 - β * μ) * (Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ) < 0 := by
  have hneg : Γ * fs_thetaR β κ σ μ * rL / fs_thetaG β κ σ μ Γ < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hΓ htr) hr) htg
  refine ⟨?_, ?_, hneg, mul_neg_of_pos_of_neg (div_pos hκ hD) hneg⟩
  · rw [abs_of_neg hr]
    field_simp
    ring
  · rw [abs_of_neg hr]
    field_simp
    ring

/-- Miao, p. 661 and Figure 19.7: with `λ_g > 0` the optimal `Ĝ_L` lies strictly below the
zero-gap level `ϑ_r|r_L|/(ϑ_G − Γ)` (`r_L < 0`, `ϑ_r > 0`, `ϑ_G > Γ`, `ξ > 0`). -/
theorem fs_optimal_GL_lt_zero_gap {ξ tr tg Γ lamg rL : ℝ} (hξ : 0 < ξ) (hg : 0 < lamg)
    (htr : 0 < tr) (htg : Γ < tg) (hr : rL < 0) :
    -(ξ * (tg - Γ) * tr) / (ξ * (tg - Γ) ^ 2 + lamg) * rL < tr * |rL| / (tg - Γ) := by
  rw [abs_of_neg hr]
  have h1 : 0 < tg - Γ := sub_pos.2 htg
  have hd : 0 < ξ * (tg - Γ) ^ 2 + lamg := by positivity
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ hd h1]
  have : 0 < tr * -rL := mul_pos htr (neg_pos.2 hr)
  nlinarith [mul_pos this hg]

/-- Miao, (19.64), p. 658, the weights, corrected: `λ_y = κ/ε > 0` and
`λ_g = λ_yΓ(η_g/η_u + 1 − Γ) > 0` (for `κ, ε, η_u > 0`, `η_g ≥ 0`, `0 < Γ < 1`); also `ξ > 0`. -/
theorem fs_weights_pos {β κ μ ε ηu ηg Γ : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hu : 0 < ηu)
    (hg : 0 ≤ ηg) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) :
    0 < κ / ε ∧ 0 < κ / ε * Γ * (ηg / ηu + 1 - Γ) ∧ 0 < fs_xi β κ μ (κ / ε) := by
  have h1 : 0 < κ / ε := div_pos hκ hε
  have h2 : 0 < ηg / ηu + 1 - Γ := by
    have := div_nonneg hg hu.le
    linarith
  refine ⟨h1, by positivity, ?_⟩
  unfold fs_xi
  positivity

/-- Miao, Figure 19.7 (p. 660) at `μ = 0.903` with the parameters of Figure 19.4, `ε = 12.77`
(`λ_y = κ/ε`) and `η_g = 0` (case A, `λ_g = λ_yΓ(1 − Γ)`): the optimal `Ĝ_L/|r_L|` is in
`(15.3, 15.4)`, the corrected zero-gap level `ϑ_r/(ϑ_G − Γ)` in `(15.4, 15.5)`, and the printed
level `ϑ_r/ϑ_G` in `(12.5, 12.6)`, below the optimum. -/
theorem fs_fig_19_7 :
    (15.3 : ℝ) < fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) * fs_thetaR 0.997 0.00859 0.862 0.903 /
      (fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) ^ 2 +
        0.00859 / 12.77 * 0.425 * (1 - 0.425)) ∧
    fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) * fs_thetaR 0.997 0.00859 0.862 0.903 /
      (fs_xi 0.997 0.00859 0.903 (0.00859 / 12.77) *
        (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) ^ 2 +
        0.00859 / 12.77 * 0.425 * (1 - 0.425)) < 15.4 ∧
    (15.4 : ℝ) < fs_thetaR 0.997 0.00859 0.862 0.903 /
      (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) ∧
    fs_thetaR 0.997 0.00859 0.862 0.903 / (fs_thetaG 0.997 0.00859 0.862 0.903 0.425 - 0.425) <
      15.5 ∧
    (12.5 : ℝ) < fs_thetaR 0.997 0.00859 0.862 0.903 / fs_thetaG 0.997 0.00859 0.862 0.903 0.425 ∧
    fs_thetaR 0.997 0.00859 0.862 0.903 / fs_thetaG 0.997 0.00859 0.862 0.903 0.425 < 12.6 := by
  unfold fs_xi fs_thetaG fs_thetaR fs_h
  norm_num

/-- A second-order Taylor statement: if `φ' = φ₁` near `0` and `φ₁` has derivative `Q` at `0`, then
`φ(s) = φ(0) + φ₁(0)s + Qs²/2 + o(s²)` (used for Exercise 19.5). -/
theorem fs_taylor2 {φ φ1 : ℝ → ℝ} {Q : ℝ} (hφ : ∀ᶠ s in 𝓝 0, HasDerivAt φ (φ1 s) s)
    (h1 : HasDerivAt φ1 Q 0) :
    (fun s => φ s - φ 0 - φ1 0 * s - Q / 2 * s ^ 2) =o[𝓝 0] (fun s => s ^ 2) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hφ
  set B := Metric.ball (0 : ℝ) δ
  have hg : ∀ x ∈ B, HasDerivWithinAt (fun s => φ s - φ 0 - φ1 0 * s - Q / 2 * s ^ 2)
      (φ1 x - φ1 0 - Q * x) B x := by
    intro x hx
    have h2 : HasDerivAt (fun s : ℝ => Q / 2 * s ^ 2) (Q / 2 * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul (Q / 2)
    have := (((hball x hx).sub_const (φ 0)).sub ((hasDerivAt_id x).const_mul (φ1 0))).sub h2
    refine (this.congr_deriv ?_).hasDerivWithinAt
    ring
  have ho : (fun x => φ1 x - φ1 0 - Q * x) =o[𝓝[B] 0] fun x => (x - 0) ^ 1 := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 h1
    simp only [zero_add, smul_eq_mul] at this
    refine (this.congr_left (fun x => by ring)).mono nhdsWithin_le_nhds |>.congr_right ?_
    intro x
    ring
  have := Convex.isLittleO_pow_succ_real (convex_ball 0 δ) (Metric.mem_ball_self hδ) hg ho
  rw [nhdsWithin_eq_nhds.2 (Metric.ball_mem_nhds 0 hδ)] at this
  simpa using this

/-- **Exercise 19.5**, flexible-price part (Miao, (19.64), pp. 658, 669). Let the period utility
be `U(Y, G) = u(Y − G) + g(G) − ṽ(Y)` around a steady state `(Ȳ, Ḡ)` that is efficient and has
optimal purchases: `u'(C̄) = ṽ'(Ȳ)` (subsidy) and `u'(C̄) = g'(Ḡ)` (19.63), `C̄ = Ȳ − Ḡ`. Along
`Y = Ȳ(1 + sŶ)`, `G = Ḡ + sȲĜ`, the first derivative at `s = 0` is zero and the second is
`−u'Ȳ(η_u + η_v)[(Ŷ − ΓĜ)² + Γ(η_g/η_u + 1 − Γ)Ĝ²]`, with `η_g = −Ȳg''/g'`; so
`U = Ū + s²/2·(that) + o(s²)`. -/
theorem ex_19_5_flex {u u1 g g1 vt vt1 : ℝ → ℝ} {Yb Gb u2 g2 vt2 a b ηu ηv ηg : ℝ}
    (hu : ∀ x, HasDerivAt u (u1 x) x) (hg : ∀ x, HasDerivAt g (g1 x) x)
    (hv : ∀ x, HasDerivAt vt (vt1 x) x) (hu1 : HasDerivAt u1 u2 (Yb - Gb))
    (hg1 : HasDerivAt g1 g2 Gb) (hv1 : HasDerivAt vt1 vt2 Yb) (hYb : 0 < Yb)
    (hpos : 0 < u1 (Yb - Gb)) (heff : u1 (Yb - Gb) = vt1 Yb) (hopt : u1 (Yb - Gb) = g1 Gb)
    (hdu : ηu = fs_etaU Yb (u1 (Yb - Gb)) u2) (hdv : ηv = fs_etaV Yb (vt1 Yb) vt2)
    (hdg : ηg = fs_etaU Yb (g1 Gb) g2) (hηu : ηu ≠ 0) (hsum : ηu + ηv ≠ 0) :
    let U : ℝ → ℝ := fun s => u ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) +
      g (Gb + s * (Yb * b)) - vt (Yb + s * (Yb * a))
    let U1 : ℝ → ℝ := fun s =>
      u1 ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) * (Yb * a - Yb * b) +
        g1 (Gb + s * (Yb * b)) * (Yb * b) - vt1 (Yb + s * (Yb * a)) * (Yb * a)
    let Q := -(u1 (Yb - Gb) * Yb * (ηu + ηv)) *
      ((a - fs_Gamma ηu ηv * b) ^ 2 + fs_Gamma ηu ηv * (ηg / ηu + 1 - fs_Gamma ηu ηv) * b ^ 2)
    (∀ s, HasDerivAt U (U1 s) s) ∧ U1 0 = 0 ∧ HasDerivAt U1 Q 0 ∧
      (fun s => U s - U 0 - Q / 2 * s ^ 2) =o[𝓝 0] (fun s => s ^ 2) := by
  intro U U1 Q
  have hl1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Yb + s * (Yb * a)) (Yb * a) s := fun s =>
    (((hasDerivAt_id' s).mul_const (Yb * a)).const_add Yb).congr_deriv (by ring)
  have hlG : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Gb + s * (Yb * b)) (Yb * b) s := fun s =>
    (((hasDerivAt_id' s).mul_const (Yb * b)).const_add Gb).congr_deriv (by ring)
  have hl2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))
      (Yb * a - Yb * b) s := fun s => (hl1 s).sub (hlG s)
  have hU : ∀ s, HasDerivAt U (U1 s) s := by
    intro s
    have h1 := (hu ((Yb + s * (Yb * a)) - (Gb + s * (Yb * b)))).comp
      (h := fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) s (hl2 s)
    have h2 := (hg (Gb + s * (Yb * b))).comp (h := fun s : ℝ => Gb + s * (Yb * b)) s (hlG s)
    have h3 := (hv (Yb + s * (Yb * a))).comp (h := fun s : ℝ => Yb + s * (Yb * a)) s (hl1 s)
    exact (h1.add h2).sub h3
  have hU10 : U1 0 = 0 := by
    simp only [U1, zero_mul, add_zero]
    rw [← heff, ← hopt]
    ring
  have hU1 : HasDerivAt U1 Q 0 := by
    have hu1' : HasDerivAt u1 u2 ((Yb + 0 * (Yb * a)) - (Gb + 0 * (Yb * b))) := by simpa using hu1
    have hg1' : HasDerivAt g1 g2 (Gb + 0 * (Yb * b)) := by simpa using hg1
    have hv1' : HasDerivAt vt1 vt2 (Yb + 0 * (Yb * a)) := by simpa using hv1
    have k1 := (hu1'.comp (h := fun s : ℝ => (Yb + s * (Yb * a)) - (Gb + s * (Yb * b))) 0
      (hl2 0)).mul_const (Yb * a - Yb * b)
    have k2 := (hg1'.comp (h := fun s : ℝ => Gb + s * (Yb * b)) 0 (hlG 0)).mul_const (Yb * b)
    have k3 := (hv1'.comp (h := fun s : ℝ => Yb + s * (Yb * a)) 0 (hl1 0)).mul_const (Yb * a)
    refine ((k1.add k2).sub k3).congr_deriv ?_
    have hvt1 : vt1 Yb ≠ 0 := heff ▸ hpos.ne'
    have hg1n : g1 Gb ≠ 0 := hopt ▸ hpos.ne'
    have e1 : u2 = -(ηu * u1 (Yb - Gb)) / Yb := by
      rw [hdu]
      unfold fs_etaU
      field_simp
    have e2 : vt2 = ηv * u1 (Yb - Gb) / Yb := by
      rw [hdv, heff]
      unfold fs_etaV
      field_simp
    have e3 : g2 = -(ηg * u1 (Yb - Gb)) / Yb := by
      rw [hdg, hopt]
      unfold fs_etaU
      field_simp
    simp only [Q]
    rw [e1, e2, e3]
    have hsq : (a - fs_Gamma ηu ηv * b) ^ 2 + fs_Gamma ηu ηv * (ηg / ηu + 1 - fs_Gamma ηu ηv) *
        b ^ 2 = ((ηu + ηv) * a ^ 2 - 2 * ηu * a * b + (ηu + ηg) * b ^ 2) / (ηu + ηv) := by
      rw [eq_div_iff hsum]
      have hG : fs_Gamma ηu ηv = ηu / (ηu + ηv) := rfl
      rw [hG]
      field_simp
      ring
    rw [hsq]
    field_simp
    ring
  refine ⟨hU, hU10, hU1, ?_⟩
  have := fs_taylor2 (Eventually.of_forall hU) hU1
  rw [hU10] at this
  simpa using this

/-- The price-dispersion index after one period of Calvo pricing, in terms of last period's
dispersion `d` and inflation `π = ln Π` (Miao, (19.13), p. 621):
`Δ = θde^{επ} + (1 − θ)((1 − θe^{(ε−1)π})/(1 − θ))^{ε/(ε−1)}`. -/
noncomputable def fs_disp (θ ε d infl : ℝ) : ℝ :=
  θ * d * Real.exp (ε * infl) +
    (1 - θ) * ((1 - θ * Real.exp ((ε - 1) * infl)) / (1 - θ)) ^ (ε / (ε - 1))

/-- Miao, p. 658: dispersion is linear in last period's dispersion, with slope `θ` at `π = 0`:
`Δ − 1 = θ(Δ₋₁ − 1)`. -/
theorem fs_dispersion_lin {θ ε d : ℝ} (hθ1 : θ < 1) : fs_disp θ ε d 0 - 1 = θ * (d - 1) := by
  have h1 : 1 - θ ≠ 0 := by linarith
  simp [fs_disp, div_self h1]
  ring

/-- **Exercise 19.5**, price dispersion (Miao, p. 658). At `Δ₋₁ = 1`, for `0 < θ < 1`, `ε > 1`,
the dispersion index as a function of `π` has `Δ(0) = 1`, zero first derivative and second
derivative `εθ/(1 − θ)`; hence `Δ = 1 + εθ/(2(1 − θ))·π² + o(π²)`. -/
theorem ex_19_5_dispersion {θ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 1 < ε) :
    let w : ℝ → ℝ := fun infl => (1 - θ * Real.exp ((ε - 1) * infl)) / (1 - θ)
    let w1 : ℝ → ℝ := fun infl => -(θ * ((ε - 1) * Real.exp ((ε - 1) * infl))) / (1 - θ)
    let ψ1 : ℝ → ℝ := fun infl => θ * 1 * (ε * Real.exp (ε * infl)) +
      (1 - θ) * (w1 infl * (ε / (ε - 1)) * w infl ^ (ε / (ε - 1) - 1))
    fs_disp θ ε 1 0 = 1 ∧ (∀ᶠ infl in 𝓝 0, HasDerivAt (fs_disp θ ε 1) (ψ1 infl) infl) ∧ ψ1 0 = 0 ∧
      HasDerivAt ψ1 (ε * θ / (1 - θ)) 0 ∧
      (fun infl => fs_disp θ ε 1 infl - 1 - ε * θ / (1 - θ) / 2 * infl ^ 2) =o[𝓝 0]
        (fun infl => infl ^ 2) := by
  intro w w1 ψ1
  have h1θ : 1 - θ ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  set k := ε / (ε - 1)
  have hw : ∀ infl, HasDerivAt w (w1 infl) infl := fun infl => by
    have := (((hasDerivAt_id' infl).const_mul (ε - 1)).exp.const_mul θ).const_sub 1
    refine (this.div_const (1 - θ)).congr_deriv ?_
    simp only [w1]
    ring
  have hw0 : w 0 = 1 := by simp [w, div_self h1θ]
  have hwc : Continuous w := by
    simp only [w]
    fun_prop
  have hwpos : ∀ᶠ infl in 𝓝 0, 0 < w infl :=
    continuousAt_const.eventually_lt hwc.continuousAt (by rw [hw0]; exact one_pos)
  have hD0 : fs_disp θ ε 1 0 = 1 := by
    simp [fs_disp, div_self h1θ]
  have hderiv : ∀ infl, 0 < w infl → HasDerivAt (fs_disp θ ε 1) (ψ1 infl) infl := by
    intro infl hπ
    have e1 := ((hasDerivAt_id' infl).const_mul ε).exp.const_mul (θ * 1)
    have e2 := ((hw infl).rpow_const (p := k) (Or.inl hπ.ne')).const_mul (1 - θ)
    refine (e1.add e2).congr_deriv ?_
    simp only [ψ1, k]
    ring
  have hψ10 : ψ1 0 = 0 := by
    simp only [ψ1, w1, hw0, Real.one_rpow, mul_zero, Real.exp_zero]
    field_simp
    ring
  have hw1d : HasDerivAt w1 (-(θ * ((ε - 1) * ((ε - 1) * 1))) / (1 - θ)) 0 := by
    have := ((((hasDerivAt_id' (0 : ℝ)).const_mul (ε - 1)).exp.const_mul (ε - 1)).const_mul
      θ).neg.div_const (1 - θ)
    refine this.congr_deriv ?_
    simp
  have hψ1 : HasDerivAt ψ1 (ε * θ / (1 - θ)) 0 := by
    have e1 := (((hasDerivAt_id' (0 : ℝ)).const_mul ε).exp.const_mul ε).const_mul (θ * 1)
    have e2 := (hw 0).rpow_const (p := k - 1) (Or.inl (by rw [hw0]; exact one_ne_zero))
    have e3 := ((hw1d.mul_const k).mul e2).const_mul (1 - θ)
    refine (e1.add e3).congr_deriv ?_
    simp only [w1, hw0, Real.one_rpow, mul_zero, Real.exp_zero, k]
    field_simp
    ring
  have hev : ∀ᶠ infl in 𝓝 0, HasDerivAt (fs_disp θ ε 1) (ψ1 infl) infl := by
    filter_upwards [hwpos] with infl hπ
    exact hderiv infl hπ
  refine ⟨hD0, hev, hψ10, hψ1, ?_⟩
  have := fs_taylor2 hev hψ1
  rw [hψ10, hD0] at this
  simpa using this

/-- Miao, p. 658: the labour cost of dispersion. With `∫ Y_j = YΔ = f(N)`, hours cost
`ṽ(YΔ)`, whose derivative in `Δ` at `Δ = 1` is `ṽ'(Ȳ)Ȳ`; so `ṽ(YΔ) ≈ ṽ(Y) + ṽ'(Ȳ)Ȳ(Δ − 1)`. -/
theorem fs_labor_dispersion {vt vt1 : ℝ → ℝ} {Yb : ℝ} (hv : HasDerivAt vt (vt1 Yb) Yb) :
    HasDerivAt (fun D => vt (Yb * D)) (vt1 Yb * Yb) 1 := by
  have hl : HasDerivAt (fun D : ℝ => Yb * D) Yb 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_mul Yb
  have hv' : HasDerivAt vt (vt1 Yb) (Yb * 1) := by simpa using hv
  exact hv'.comp (h := fun D : ℝ => Yb * D) 1 hl

/-- Miao, p. 658: the discounted dispersion. If `d_0 = cπ_0²`, `d_{t+1} = θd_t + cπ_{t+1}²`
(`0 ≤ θ < 1`, `0 < β < 1`, `π` bounded), then `Σβᵗd_t = c/(1 − βθ)·Σβᵗπ_t²`. -/
theorem fs_dispersion_sum {β θ c : ℝ} {d infl : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hπ : fs_Bdd infl) (hd0 : d 0 = c * infl 0 ^ 2)
    (hd : ∀ t, d (t + 1) = θ * d t + c * infl (t + 1) ^ 2) :
    ∑' t, β ^ t * d t = c / (1 - β * θ) * ∑' t, β ^ t * infl t ^ 2 := by
  obtain ⟨B, hB⟩ := hπ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hπ2 : ∀ t, |infl t ^ 2| ≤ B ^ 2 := fun t => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  have hdB : ∀ t, |d t| ≤ |c| * B ^ 2 / (1 - θ) := by
    have h1 : 0 < 1 - θ := by linarith
    have key : |c| * B ^ 2 ≤ |c| * B ^ 2 / (1 - θ) := by
      rw [le_div_iff₀ h1]
      nlinarith [mul_nonneg (abs_nonneg c) (sq_nonneg B)]
    intro t
    induction t with
    | zero =>
      rw [hd0, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hπ2 0) (abs_nonneg c)).trans key
    | succ n ih =>
      rw [hd n]
      calc |θ * d n + c * infl (n + 1) ^ 2| ≤ |θ * d n| + |c * infl (n + 1) ^ 2| := abs_add_le _ _
        _ ≤ θ * (|c| * B ^ 2 / (1 - θ)) + |c| * B ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg hθ0]
          exact add_le_add (mul_le_mul_of_nonneg_left ih hθ0)
            (mul_le_mul_of_nonneg_left (hπ2 _) (abs_nonneg c))
        _ = |c| * B ^ 2 / (1 - θ) := by
          field_simp
          ring
  have hβa : |(β : ℝ)| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hsd : Summable (fun t => β ^ t * d t) :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right
      (|c| * B ^ 2 / (1 - θ))) (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hdB t) (by positivity))
  have hsp : Summable (fun t => β ^ t * infl t ^ 2) :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right (B ^ 2))
      (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hπ2 t) (by positivity))
  have hsp1 : Summable (fun t => β ^ t * infl (t + 1) ^ 2) :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right (B ^ 2))
      (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hπ2 (t + 1)) (by positivity))
  have eS := hsd.tsum_eq_zero_add
  have eP := hsp.tsum_eq_zero_add
  have hshift : ∀ t, β ^ (t + 1) * d (t + 1) =
      β * θ * (β ^ t * d t) + β * c * (β ^ t * infl (t + 1) ^ 2) := fun t => by
    rw [hd t]
    ring
  have hshiftP : ∀ t, β ^ (t + 1) * infl (t + 1) ^ 2 = β * (β ^ t * infl (t + 1) ^ 2) := fun t => by
    ring
  simp_rw [hshift] at eS
  simp_rw [hshiftP] at eP
  rw [Summable.tsum_add (hsd.mul_left _) (hsp1.mul_left _), tsum_mul_left, tsum_mul_left] at eS
  rw [tsum_mul_left] at eP
  simp only [pow_zero, one_mul] at eS eP
  have hD : 0 < 1 - β * θ := by nlinarith
  rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
  rw [hd0] at eS
  linear_combination eS - c * eP

/-- **Exercise 19.5**, the assembly (Miao, (19.64), p. 658). Let `uY = u'(C̄)Ȳ > 0`,
`Γ = η_u/(η_u + η_v)` (the identity holds for every `Γ`), `κ̃ = (1 − θ)(1 − βθ)/θ`,
`κ = κ̃(η_u + η_v)`, `λ_y = κ/ε` and
`λ_g = λ_yΓ(η_g/η_u + 1 − Γ)`. Let `d_t` (the dispersion term `Δ_t − 1`) follow the second-order
recursion `d_t = θd_{t−1} + εθ/(2(1 − θ))·π_t²`, `d_{−1} = 0` (`ex_19_5_dispersion`,
`fs_dispersion_lin`). Then the discounted sum of the second-order terms of the period utility,
`−uY(η_u + η_v)/2·[(Ŷ_t − ΓĜ_t)² + Γ(η_g/η_u + 1 − Γ)Ĝ_t²]` (`ex_19_5_flex`) minus the labour cost
of dispersion `uY·d_t` (`fs_labor_dispersion`, `u' = ṽ'`), equals
`−(uYε/(2κ̃))·Σβᵗ[π_t² + λ_y(Ŷ_t − ΓĜ_t)² + λ_gĜ_t²]`: welfare varies inversely with (19.64). -/
theorem ex_19_5 {β θ ε ηu ηv ηg uY Γ κt lamy lamg : ℝ} {infl Y G d : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) (hu : 0 < ηu) (hv : 0 < ηv)
    (hπ : fs_Bdd infl) (hY : fs_Bdd Y) (hG : fs_Bdd G)
    (hd0 : d 0 = ε * θ / (2 * (1 - θ)) * infl 0 ^ 2)
    (hd : ∀ t, d (t + 1) = θ * d t + ε * θ / (2 * (1 - θ)) * infl (t + 1) ^ 2)
    (hκt : κt = (1 - θ) * (1 - β * θ) / θ)
    (hly : lamy = κt * (ηu + ηv) / ε) (hlg : lamg = lamy * Γ * (ηg / ηu + 1 - Γ)) :
    ∑' t, β ^ t * (-(uY * (ηu + ηv) / 2) *
        ((Y t - Γ * G t) ^ 2 + Γ * (ηg / ηu + 1 - Γ) * G t ^ 2) - uY * d t) =
      -(uY * ε / (2 * κt)) * ∑' t, β ^ t * fs_loss lamy lamg Γ (infl t) (Y t) (G t) := by
  have hβa : |(β : ℝ)| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hsum : ∀ x : ℕ → ℝ, fs_Bdd x → Summable (fun t => β ^ t * x t) := by
    rintro x ⟨B, hB⟩
    exact Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one hβa).mul_right B)
      (fun t => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ0]
        exact mul_le_mul_of_nonneg_left (hB t) (by positivity))
  have hsq : ∀ x : ℕ → ℝ, fs_Bdd x → fs_Bdd (fun t => x t ^ 2) := by
    rintro x ⟨B, hB⟩
    exact ⟨B ^ 2, fun t => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2⟩
  have hgap : fs_Bdd (fun t => Y t - Γ * G t) := by
    obtain ⟨B1, h1⟩ := hY
    obtain ⟨B2, h2⟩ := hG
    exact ⟨B1 + |Γ| * B2, fun t => (abs_sub _ _).trans (add_le_add (h1 t)
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h2 t) (abs_nonneg _)))⟩
  have sP := (hsum _ (hsq _ hπ)).hasSum
  have sX := (hsum _ (hsq _ hgap)).hasSum
  have sG := (hsum _ (hsq _ hG)).hasSum
  have hdsum := fs_dispersion_sum hβ0 hβ1 hθ0.le hθ1 hπ hd0 hd
  have hdB : fs_Bdd d := by
    obtain ⟨B, hB⟩ := hπ
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    set c := ε * θ / (2 * (1 - θ))
    have hc : 0 ≤ c := by
      have : 0 < 1 - θ := by linarith
      positivity
    have h1 : 0 < 1 - θ := by linarith
    refine ⟨c * B ^ 2 / (1 - θ), fun t => ?_⟩
    have hπ2 : ∀ t, |infl t ^ 2| ≤ B ^ 2 := fun t => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
    have key : c * B ^ 2 ≤ c * B ^ 2 / (1 - θ) := by
      rw [le_div_iff₀ h1]
      nlinarith [mul_nonneg hc (sq_nonneg B)]
    induction t with
    | zero =>
      rw [hd0, abs_mul, abs_of_nonneg hc]
      exact (mul_le_mul_of_nonneg_left (hπ2 0) hc).trans key
    | succ n ih =>
      rw [hd n]
      calc |θ * d n + c * infl (n + 1) ^ 2| ≤ |θ * d n| + |c * infl (n + 1) ^ 2| := abs_add_le _ _
        _ ≤ θ * (c * B ^ 2 / (1 - θ)) + c * B ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos hθ0, abs_of_nonneg hc]
          exact add_le_add (mul_le_mul_of_nonneg_left ih hθ0.le)
            (mul_le_mul_of_nonneg_left (hπ2 _) hc)
        _ = c * B ^ 2 / (1 - θ) := by
          field_simp
          ring
  have sD := (hsum _ hdB).hasSum
  have hL : HasSum (fun t => β ^ t * (-(uY * (ηu + ηv) / 2) *
      ((Y t - Γ * G t) ^ 2 + Γ * (ηg / ηu + 1 - Γ) * G t ^ 2) - uY * d t))
      (-(uY * (ηu + ηv) / 2) * ∑' t, β ^ t * (Y t - Γ * G t) ^ 2 +
        -(uY * (ηu + ηv) / 2) * (Γ * (ηg / ηu + 1 - Γ)) * ∑' t, β ^ t * G t ^ 2 -
        uY * ∑' t, β ^ t * d t) :=
    (((sX.mul_left (-(uY * (ηu + ηv) / 2))).add
      (sG.mul_left (-(uY * (ηu + ηv) / 2) * (Γ * (ηg / ηu + 1 - Γ))))).sub
        (sD.mul_left uY)).congr_fun (fun t => by ring)
  have hR : HasSum (fun t => β ^ t * fs_loss lamy lamg Γ (infl t) (Y t) (G t))
      (∑' t, β ^ t * infl t ^ 2 + lamy * ∑' t, β ^ t * (Y t - Γ * G t) ^ 2 +
        lamg * ∑' t, β ^ t * G t ^ 2) :=
    ((sP.add (sX.mul_left lamy)).add (sG.mul_left lamg)).congr_fun (fun t => by
      simp only [fs_loss]
      ring)
  rw [hL.tsum_eq, hR.tsum_eq, hdsum]
  have h1θ : 0 < 1 - θ := by linarith
  have hD : 0 < 1 - β * θ := by nlinarith
  have hκt0 : 0 < κt := by rw [hκt]; positivity
  have e1 : ε * θ / (2 * (1 - θ)) / (1 - β * θ) = ε / (2 * κt) := by
    rw [hκt]
    field_simp
  have e2 : uY * ε / (2 * κt) * lamy = uY * (ηu + ηv) / 2 := by
    rw [hly]
    field_simp
  rw [hlg]
  linear_combination (-(uY * ∑' t, β ^ t * infl t ^ 2)) * e1 +
    (∑' t, β ^ t * (Y t - Γ * G t) ^ 2) * e2 +
    (Γ * (ηg / ηu + 1 - Γ) * ∑' t, β ^ t * G t ^ 2) * e2

end Miao.NewKeynesian
