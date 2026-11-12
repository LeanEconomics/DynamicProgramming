/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMNominalFrictions.Environment
import AKMMNominalFrictions.Aggregation
import AKMMNominalFrictions.ThreeEquation
import StickyWagesPrices.WageInflation

/-!
# Sticky wages and prices

AKMM, §18.6.1, pp. 556–558, and Appendix 18.A.3, pp. 873–876.

* **Labour aggregation** (18.A.8)–(18.A.9): the labour composite has the same CES structure as
  (18.2), so the cost-minimising demand for type-`i` labour is `(W_i/W)^{−ε} ℓ`, the wage index is
  `W = (∫W_i^{1−ε})^{1/(1−ε)}` and labour income is `W L` (`sw_labour_ces`, from `env_ces`).
* **Wage dispersion**: hours `N = D^W L` with `D^W = ∫ (W_i/W)^{−ε} ≥ 1`, so hours exceed
  effective labour (`sw_hours`, `sw_wage_dispersion_ge_one`).
* **The union's problem**: the derivative of the union's period objective, multiplied by `W^R`,
  is `(1 − ε) u′ w (w^R)^{1−ε} L + ε N^ψ (w^R)^{−ε} L`, and the first-order condition rearranges to
  the book's `∑(βθ^w)^k u′ w (w^R)^{−(ε−1)} L = μ ∑(βθ^w)^k N^ψ (w^R)^{−ε} L`
  (`sw_union_term_deriv`, `sw_union_foc`): here the book's exponents are right.
* **The wage Phillips curve**: with the reset-wage recursion and the Calvo wage index,
  `π^w = βE π^w′ + ξ^w(σĈ + ψN̂ − ŵ)` (Galí's `eq15_iff` with no strategic complementarity,
  `φ = 0`; `sw_wage_pc`), and with `Ĉ = Ŷ`, `N̂ = Ŷ − Â` and (18.13),
  `ξ^w(σĈ + ψN̂ − ŵ) = κ^w x + ξ^w Â − ξ^w ŵ`, `κ^w = ξ^w(σ + ψ)` (`eq_18_24`).
* **The price Phillips curve** (18.23) (`eq_18_23`, from `eq_18_A_4`) and the real-wage identity
  (18.25), exact in logs (`eq_18_25`).
* **Correction (sticky wages only, p. 557)**: with `y = Aℓ`, pricing at marginal cost means
  `P = W_L/A` for the wage `W_L` of the labour bundle, so the real wage is `W_L/P = A`, constant
  only if productivity is (`sw_flexprice_real_wage`, `sw_real_wage_not_constant`); `W/P = 1`
  holds for the book's `W` = the labour cost of one unit of goods.
-/

namespace AKMM.NominalFrictions

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-- **AKMM, (18.A.8)–(18.A.9), p. 874**: on the continuum of unions `i ∈ [0, 1]` with wages
`W_i > 0`, (i) any labour bundle `n_i ≥ 0` costs at least `W L`, `L` the CES composite (18.A.8)
and `W` the wage index (18.A.9); (ii) it costs exactly `W L` iff `n_i = (W_i/W)^{−ε} L`;
(iii) the demand schedule delivers `L`; (iv) labour income is `∫ W_i n_i = W L`
(`env_ces` with wages in place of prices). -/
theorem sw_labour_ces {ε : ℝ} (hε : 1 < ε) {Wi : ℝ → ℝ} (hW : ∀ i, 0 < Wi i)
    (hWi : IntegrableOn (fun i => Wi i ^ (1 - ε)) (Set.Icc 0 1)) {n : ℝ → ℝ}
    (hn : ∀ i, 0 ≤ n i) (hWn : IntegrableOn (fun i => Wi i * n i) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Wi * cesAgg (volume.restrict (Set.Icc 0 1)) ε n
        ≤ ∫ i in Set.Icc 0 1, Wi i * n i ∧
      (∫ i in Set.Icc 0 1, Wi i * n i
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Wi *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε n ↔
        ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          n i = demand (volume.restrict (Set.Icc 0 1)) ε Wi
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε n) i) ∧
      (∀ L : ℝ, 0 ≤ L → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Wi L) = L) ∧
      ∀ L : ℝ, ∫ i in Set.Icc 0 1, Wi i * demand (volume.restrict (Set.Icc 0 1)) ε Wi L i
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Wi * L :=
  env_ces hε hW hWi hn hWn

/-- **AKMM, p. 874**: hours are `N = ∫ n_i = ∫ (W_i/W)^{−ε} L = D^W L`. -/
theorem sw_hours {J : Type*} [MeasurableSpace J] {μ : Measure J} {ε W L : ℝ} {Wi n : J → ℝ}
    (hn : ∀ i, n i = (Wi i / W) ^ (-ε) * L) :
    ∫ i, n i ∂μ = (∫ i, (Wi i / W) ^ (-ε) ∂μ) * L := by
  simp_rw [hn]; rw [integral_mul_const]

/-- **AKMM, p. 874**: wage dispersion `D^W = ∫ (W_i/W)^{−ε} ≥ 1` (`agg_dispersion_ge_one`
with wages), so hours `N = D^W L ≥ L` exceed effective labour for `L ≥ 0`. -/
theorem sw_wage_dispersion_ge_one {J : Type*} [MeasurableSpace J] {μ : Measure J}
    [IsProbabilityMeasure μ] {ε L : ℝ} (hε : 1 < ε) {Wi : J → ℝ} (hW : ∀ i, 0 < Wi i)
    (hWi : Integrable (fun i => Wi i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (Wi i / priceIndex μ ε Wi) ^ (-ε)) μ) (hL : 0 ≤ L) :
    1 ≤ ∫ i, (Wi i / priceIndex μ ε Wi) ^ (-ε) ∂μ ∧
      L ≤ (∫ i, (Wi i / priceIndex μ ε Wi) ^ (-ε) ∂μ) * L := by
  have h := agg_dispersion_ge_one hε hW hWi hD
  exact ⟨h, by nlinarith⟩

/-- **AKMM, p. 875**: the union's period-`τ` objective
`u′(C_τ) (W^R/P_τ)(W^R/W_τ)^{−ε} L_τ − N_τ^ψ (W^R/W_τ)^{−ε} L_τ` has a derivative `d` in `W^R`
with `W^R d = (1 − ε) u′ w_τ (w^R)^{1−ε} L_τ + ε N_τ^ψ (w^R)^{−ε} L_τ`, `w_τ = W_τ/P_τ`,
`w^R = W^R/W_τ`. -/
theorem sw_union_term_deriv {ε up Nψ P W L X : ℝ} (hP : 0 < P) (hW : 0 < W) (hX : 0 < X) :
    ∃ d, HasDerivAt (fun Y => up * (Y / P) * (Y / W) ^ (-ε) * L - Nψ * (Y / W) ^ (-ε) * L) d X ∧
      X * d = (1 - ε) * (up * (W / P) * (X / W) ^ (1 - ε) * L) +
        ε * (Nψ * (X / W) ^ (-ε) * L) := by
  have hq : 0 < X / W := div_pos hX hW
  have h1 : HasDerivAt (fun Y => Y / W) (1 / W) X := by
    simpa using (hasDerivAt_id X).div_const W
  have h2 := h1.rpow_const (p := -ε) (Or.inl hq.ne')
  have h3 : HasDerivAt (fun Y => Y / P) (1 / P) X := by
    simpa using (hasDerivAt_id X).div_const P
  have h := (((h3.const_mul up).mul h2).mul_const L).sub ((h2.const_mul Nψ).mul_const L)
  refine ⟨_, h, ?_⟩
  have a1 : (X / W) ^ (-ε) = (X / W) ^ (-ε - 1) * (X / W) := by
    rw [← Real.rpow_add_one hq.ne']; ring_nf
  have a2 : (X / W) ^ (1 - ε) = (X / W) * (X / W) ^ (-ε) := by
    rw [show 1 - ε = -ε + 1 by ring, Real.rpow_add_one hq.ne']; ring
  rw [a2, a1]
  field_simp
  ring

/-- **AKMM, p. 875 (the union's first-order condition)**: if `∑_k (βθ^w)^k` of the terms of
`sw_union_term_deriv` (times `W^R`) is zero and the two weighted sums converge to `A` and `B`,
then `A = μ B`: `∑(βθ^w)^k u′ w (w^R)^{−(ε−1)} L = ε/(ε − 1) ∑(βθ^w)^k N^ψ (w^R)^{−ε} L`. -/
theorem sw_union_foc {ε : ℝ} (hε : 1 < ε) {a b : ℕ → ℝ} {A B : ℝ} (ha : HasSum a A)
    (hb : HasSum b B) (hfoc : HasSum (fun k => (1 - ε) * a k + ε * b k) 0) :
    A = ε / (ε - 1) * B := by
  have h := ((ha.mul_left (1 - ε)).add (hb.mul_left ε)).unique hfoc
  have hε1 : ε - 1 ≠ 0 := by linarith
  field_simp
  linarith

/-- **AKMM, p. 875 (the wage Phillips curve)**: with the Calvo wage index
`w_{t+1} = θ_w w_t + (1 − θ_w) w^R_{t+1}` (log levels) and `0 < θ_w < 1`, the reset-wage
recursion `w^R_{t+1} = βθ_w E w^R_{t+2} + (1 − βθ_w)(w_{t+1} − µ̂_{t+1})`, with `µ̂ = ŵ − mrs`
the real wage minus the marginal rate of substitution, holds at every date iff
`π^w_{t+1} = β E π^w_{t+2} − ξ^w µ̂_{t+1}`, `ξ^w = (1 − θ_w)(1 − βθ_w)/θ_w` (Galí's `eq15_iff`
at `φ = 0`: the book's union takes `N^ψ` as given). -/
theorem sw_wage_pc {Ω : Type*} (𝔼 : Gali.StickyWagesPrices.ExpectationSystem Ω) {β θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {wR w μhat : ℕ → Ω → ℝ} (hwa : 𝔼.Adapted w)
    (h14 : ∀ t, w (t + 1) = θ • w t + (1 - θ) • wR (t + 1)) :
    (∀ t, wR (t + 1) = (β * θ) • 𝔼.E (t + 1) (wR (t + 2)) +
        (1 - β * θ) • (w (t + 1) - μhat (t + 1))) ↔
      ∀ t, Gali.StickyWagesPrices.WageInflation.wageInfl w t =
        β • 𝔼.E (t + 1) (Gali.StickyWagesPrices.WageInflation.wageInfl w (t + 1)) -
          ((1 - θ) * (1 - β * θ) / θ) • μhat (t + 1) := by
  have h := Gali.StickyWagesPrices.WageInflation.eq15_iff 𝔼 (ε := ε) (φ := 0) (β := β) hθ0 hθ1
    (by simp) hwa h14 (μhat := μhat)
  simp only [mul_zero, add_zero, inv_one, one_smul] at h
  rw [h]
  simp [Gali.StickyWagesPrices.WageInflation.lambdaW]

/-- **AKMM, (18.24), p. 557 and p. 876**: with `Ĉ = Ŷ`, `N̂ = Ŷ − Â` and the gap
`x = Ŷ − (1+ψ)/(σ+ψ) Â`, `σĈ + ψN̂ = (σ + ψ)Ŷ − ψÂ` and
`ξ^w(σĈ + ψN̂ − ŵ) = κ^w x + ξ^w Â − ξ^w ŵ`, `κ^w = ξ^w(σ + ψ)`. -/
theorem eq_18_24 {σ ψ ξw C N Y A w x : ℝ} (hs : σ + ψ ≠ 0) (hC : C = Y) (hN : N = Y - A)
    (hx : x = Y - (1 + ψ) / (σ + ψ) * A) :
    σ * C + ψ * N = (σ + ψ) * Y - ψ * A ∧
      ξw * (σ * C + ψ * N - w) = ξw * (σ + ψ) * x + ξw * A - ξw * w := by
  refine ⟨by rw [hC, hN]; ring, ?_⟩
  rw [hC, hN, hx]
  field_simp
  ring

/-- **AKMM, (18.23), p. 557**: the price Phillips curve
`π_t = βE_tπ_{t+1} + ξ^p(ŵ_t − Â_t)`, `ξ^p = (1 − βθ)(1 − θ)/θ` (`eq_18_A_4` with marginal
cost `ŵ − Â`). -/
theorem eq_18_23 {Ω : Type*} (𝔼 : Gali.BasicNewKeynesianModel.ExpectationSystem Ω) {β θ : ℝ}
    (hθ0 : θ ≠ 0) (hθ1 : θ ≠ 1) {w a pR infl : ℕ → Ω → ℝ}
    (hrec : ResetRecursion 𝔼 β θ (fun s => w s - a s) pR infl)
    (h3 : ∀ s, infl s = ((1 - θ) / θ) • pR s) (t : ℕ) :
    infl t = β • 𝔼.E t (infl (t + 1)) + ((1 - β * θ) * (1 - θ) / θ) • (w t - a t) := by
  rw [eq_18_A_4 𝔼 hθ0 hθ1 hrec h3 t, add_comm]
  congr 2
  ring

/-- **AKMM, (18.25), p. 557**: the log of `w_t = W_t/P_t = (W_{t−1}/P_{t−1})(W_t/W_{t−1})
(P_{t−1}/P_t)`: `log w_t = log w_{t−1} + log(1 + π^w_t) − log(1 + π_t)` (exact). -/
theorem eq_18_25 {W Wm P Pm : ℝ} (hW : 0 < W) (hWm : 0 < Wm) (hP : 0 < P) (hPm : 0 < Pm) :
    Real.log (W / P) = Real.log (Wm / Pm) + Real.log (W / Wm) - Real.log (P / Pm) := by
  rw [Real.log_div hW.ne' hP.ne', Real.log_div hWm.ne' hPm.ne', Real.log_div hW.ne' hWm.ne',
    Real.log_div hP.ne' hPm.ne']
  ring

/-- **AKMM, p. 557 (correction)**: with sticky wages only and `y = Aℓ`, a competitive firm prices
at marginal cost, `P = W_L/A` (`W_L` the wage of the labour bundle); then the real wage is
`W_L/P = A`, while the cost `W = W_L/A` of the labour needed for one unit of goods satisfies
`W/P = 1`. -/
theorem sw_flexprice_real_wage {WL A P : ℝ} (hA : 0 < A) (hWL : 0 < WL) (hP : P = WL / A) :
    WL / P = A ∧ WL / A / P = 1 := by
  rw [hP]
  constructor
  · field_simp
  · field_simp

/-- **AKMM, p. 557 (correction)**: "real wages, which are now constant as `w_t = 1`" fails when
productivity varies: at two dates with `A₁ ≠ A₂`, the marginal-cost real wages differ. -/
theorem sw_real_wage_not_constant {WL₁ WL₂ A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hW₁ : 0 < WL₁) (hW₂ : 0 < WL₂) (hne : A₁ ≠ A₂) :
    WL₁ / (WL₁ / A₁) ≠ WL₂ / (WL₂ / A₂) := by
  rw [(sw_flexprice_real_wage hA₁ hW₁ rfl).1, (sw_flexprice_real_wage hA₂ hW₂ rfl).1]
  exact hne

end AKMM.NominalFrictions
