/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMNominalFrictions.Environment
import AKMMNominalFrictions.NaturalOutput
import DiscretionCommitment.LossAndCostPush
import MonetaryPolicyDesign.Welfare

/-!
# Policy objectives: efficiency, the subsidy and the quadratic loss

AKMM, §18.4.1, pp. 545–547.

* `eff_planner_foc`, `eq_18_19`: the planner's first-order condition and the efficient output
  `Y* = A^{(1+ψ)/(σ+ψ)}`.
* `eff_output_wage`, `eff_output_dispersion`: `Y = (w/A)^{1/(σ+ψ)} Y*` without dispersion and
  `Y = D^{−ψ/(σ+ψ)} (w/A)^{1/(σ+ψ)} Y*` with it (from `nat_output_general`).
* `eff_natural_lt`: with `w/A = 1/µ < 1`, `Y^n = µ^{−1/(σ+ψ)} Y* < Y*`; `eff_dispersion_lowers`:
  dispersion `D > 1` lowers output at a given `w/A`; `eff_marginal_cost_pricing`: pricing at
  nominal marginal cost means `w/A = 1`.
* `eff_welfare_gap`: `x^w = x − log µ/(σ+ψ)`.
* `eff_subsidy`, `eff_subsidy_mem`: the subsidy `τ = 1/ε ∈ (0, 1)` is the unique subsidy with
  flexible-price `w/A = 1`, so that `Y^n = Y*` (`eff_subsidy_natural_eq`).
* (18.20), cited by the book (Woodford 2003): at `α = 0` Galí's second-order approximation of
  period utility around the efficient steady state (`eq_18_20_utility`, from Galí's
  `Welfare.period_utility_normalised`) has gap coefficient `σ + ψ` and dispersion weight `ε`,
  and the welfare loss is `ε/(2λ)` times `π² + (κ/ε) x²` with the book's
  `κ = (1 − θ)(1 − βθ)(σ + ψ)/θ` (`eq_18_20_weight`, `eq_18_20_period`).
-/

namespace AKMM.NominalFrictions

open Asymptotics Filter Topology

/-- AKMM, p. 545: the planner's objective `u(A L) − L^{1+ψ}/(1+ψ)` has derivative
`A (A L)^{−σ} − L^ψ` in `L`. -/
theorem eff_planner_foc {σ ψ A L : ℝ} (hσ : σ ≠ 1) (hψ : 0 < ψ) (hA : 0 < A) (hL : 0 < L) :
    HasDerivAt (fun l => nfU σ ψ (A * l) l) ((A * L) ^ (-σ) * A - L ^ ψ) L := by
  have h := env_labour_foc (C₀ := 0) (w := A) hσ hψ (by positivity) hL
  simpa using h

/-- **AKMM, (18.19), p. 545**: at the planner's optimum (`A (A L)^{−σ} = L^ψ`), efficient output
is `Y* = A L = A^{(1+ψ)/(σ+ψ)}`. -/
theorem eq_18_19 {σ ψ A L : ℝ} (hs : 0 < σ + ψ) (hA : 0 < A) (hL : 0 < L)
    (hfoc : (A * L) ^ (-σ) * A = L ^ ψ) : A * L = A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := nat_output_general (D := 1) (w := A) (Y := A * L) (L := L) hs hA hA one_pos
    (by positivity) hL (by rw [div_one]) hfoc
  rwa [Real.one_rpow, one_mul, div_self hA.ne', Real.one_rpow, one_mul] at h

/-- AKMM, (18.19), p. 545: conversely `Y* = A^{(1+ψ)/(σ+ψ)}` satisfies the first-order
condition (`eq_18_13_solves` with `µ = 1`). -/
theorem eq_18_19_solves {σ ψ A : ℝ} (hs : 0 < σ + ψ) (hA : 0 < A) :
    (A ^ ((1 + ψ) / (σ + ψ))) ^ (-σ) * A = (A ^ ((1 + ψ) / (σ + ψ)) / A) ^ ψ := by
  have h := eq_18_13_solves (mu := 1) hs one_pos hA
  simpa using h

/-- **AKMM, p. 545**: without price dispersion (`Y = A L`), with `C = Y` and (18.6),
`Y = (w/A)^{1/(σ+ψ)} Y*`. -/
theorem eff_output_wage {σ ψ w A Y L : ℝ} (hs : 0 < σ + ψ) (hw : 0 < w) (hA : 0 < A)
    (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L) (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Y = (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := nat_output_general (D := 1) hs hw hA one_pos hY hL (by rw [hprod, div_one]) hlab
  rwa [Real.one_rpow, one_mul] at h

/-- **AKMM, p. 546**: with dispersion (`Y = A L/D`), `C = Y` and (18.6),
`Y = D^{−ψ/(σ+ψ)} (w/A)^{1/(σ+ψ)} Y*`. -/
theorem eff_output_dispersion {σ ψ w A D Y L : ℝ} (hs : 0 < σ + ψ) (hw : 0 < w) (hA : 0 < A)
    (hD : 0 < D) (hY : 0 < Y) (hL : 0 < L) (hprod : Y = A * L / D)
    (hlab : Y ^ (-σ) * w = L ^ ψ) :
    Y = D ^ (-ψ / (σ + ψ)) * (w / A) ^ (1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) :=
  nat_output_general hs hw hA hD hY hL hprod hlab

/-- **AKMM, p. 546**: in the flexible-price economy `w/A = 1/µ < 1`, so natural output
`Y^n = µ^{−1/(σ+ψ)} Y*` is strictly below the efficient level. -/
theorem eff_natural_lt {σ ψ mu A : ℝ} (hs : 0 < σ + ψ) (hmu : 1 < mu) (hA : 0 < A) :
    mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ)) < A ^ ((1 + ψ) / (σ + ψ)) := by
  have h1 : mu ^ (-1 / (σ + ψ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hmu (div_neg_of_neg_of_pos (by norm_num) hs)
  have h2 : 0 < A ^ ((1 + ψ) / (σ + ψ)) := by positivity
  nlinarith

/-- AKMM, p. 546: with `ψ > 0`, at a given `w/A`, dispersion `D > 1` strictly lowers output:
`D^{−ψ/(σ+ψ)} < 1`. -/
theorem eff_dispersion_lowers {σ ψ D : ℝ} (hs : 0 < σ + ψ) (hψ : 0 < ψ) (hD : 1 < D) :
    D ^ (-ψ / (σ + ψ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hD (div_neg_of_neg_of_pos (by linarith) hs)

/-- AKMM, p. 546: "if firms set prices equal to nominal marginal cost we would have
`P_t = P_t w_t/A` or `w_t/A_t = 1`". -/
theorem eff_marginal_cost_pricing {P w A : ℝ} (hP : 0 < P) (hA : 0 < A) :
    P = P * w / A ↔ w / A = 1 := by
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    rw [mul_div_assoc, h, mul_one]

/-- **AKMM, p. 546**: the welfare-relevant gap `x^w = log Y − log Y*` equals
`x − log µ/(σ+ψ)`, with `Y^n = µ^{−1/(σ+ψ)} Y*` (18.13), (18.19). -/
theorem eff_welfare_gap {σ ψ mu A Y : ℝ} (hmu : 0 < mu) (hA : 0 < A) :
    Real.log Y - Real.log (A ^ ((1 + ψ) / (σ + ψ))) =
      nfGap Y (mu ^ (-1 / (σ + ψ)) * A ^ ((1 + ψ) / (σ + ψ))) - Real.log mu / (σ + ψ) := by
  unfold nfGap
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hmu]
  ring

/-- **AKMM, p. 547**: with a production subsidy `τ`, the flexible-price price is the markup over
the subsidised marginal cost, `1 = µ(1 − τ) w/A`; then `w/A = 1` iff `τ = 1/ε`. -/
theorem eff_subsidy {ε τ w A : ℝ} (hε : 1 < ε) (hA : 0 < A)
    (h : 1 = ε / (ε - 1) * ((1 - τ) * w / A)) : w / A = 1 ↔ τ = 1 / ε := by
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  have h' : (ε - 1) * A = ε * ((1 - τ) * w) := by field_simp at h; linarith
  constructor
  · intro hw
    have hw' : w = A := by field_simp at hw; linarith
    rw [hw'] at h'
    have : (ε - 1) = ε * (1 - τ) := by
      have := mul_right_cancel₀ hA.ne' (by linarith : (ε - 1) * A = ε * (1 - τ) * A)
      linarith
    field_simp
    linarith
  · intro hτ
    rw [hτ] at h'
    have : (ε - 1) * A = (ε - 1) * w := by rw [h']; field_simp
    have hw : A = w := mul_left_cancel₀ hε1 this
    rw [hw, div_self (by rw [← hw]; exact hA.ne')]

/-- AKMM, p. 547: the subsidy `τ = 1/ε` lies in `(0, 1)` for `ε > 1`. -/
theorem eff_subsidy_mem {ε : ℝ} (hε : 1 < ε) : 0 < 1 / ε ∧ 1 / ε < 1 :=
  ⟨by positivity, by rw [div_lt_one (by linarith)]; exact hε⟩

/-- AKMM, p. 547: with the subsidy `τ = 1/ε` the flexible-price wage is `w = A`, so the
flexible-price allocation (18.13) with `µ(1 − τ) = 1` is efficient, `Y^n = Y*`. -/
theorem eff_subsidy_natural_eq {σ ψ A Y C L w : ℝ} (hs : 0 < σ + ψ) (hA : 0 < A) (hY : 0 < Y)
    (hL : 0 < L) (hw : w = A) (hC : Y = C) (hprod : Y = A * L) (hlab : C ^ (-σ) * w = L ^ ψ) :
    Y = A ^ ((1 + ψ) / (σ + ψ)) := by
  have h := eq_18_13 (mu := 1) hs one_pos hA hY hL (by rw [hw, div_one]) hC hprod hlab
  simpa using h

/-- **AKMM, (18.20), p. 547 (the weights)**: at `α = 0` (the book's technology (18.3)),
Galí's slope `κ = λ(σ + φ)` with `λ = (1 − θ)(1 − βθ)/θ` is the book's
`κ = (1 − θ)(1 − βθ)(σ + ψ)/θ`, and the relative weight of the output gap in the loss is
`ϑ = κ/ε`. -/
theorem eq_18_20_weight {β θ σ ψ ε : ℝ} :
    Gali.DiscretionCommitment.LossAndCostPush.kappaNK β θ σ ψ 0 ε =
        (1 - θ) * (1 - β * θ) * (σ + ψ) / θ ∧
      Gali.DiscretionCommitment.LossAndCostPush.vartheta β θ σ ψ 0 ε =
        (1 - θ) * (1 - β * θ) * (σ + ψ) / θ / ε := by
  have hk : Gali.DiscretionCommitment.LossAndCostPush.kappaNK β θ σ ψ 0 ε =
      (1 - θ) * (1 - β * θ) * (σ + ψ) / θ := by
    simp only [Gali.DiscretionCommitment.LossAndCostPush.kappaNK,
      Gali.DiscretionCommitment.LossAndCostPush.lambdaNK,
      Gali.DiscretionCommitment.LossAndCostPush.bigTheta,
      Gali.DiscretionCommitment.LossAndCostPush.gapCoeff]
    simp only [sub_zero, add_zero, div_one]
    ring
  refine ⟨hk, ?_⟩
  rw [Gali.DiscretionCommitment.LossAndCostPush.vartheta, hk]

/-- **AKMM, (18.20), p. 547 (the period loss)**: at `α = 0` the second-order welfare loss per
period, `½[(σ + ψ) x² + (ε/λ) π²]`, equals `ε/(2λ)` times the book's `π² + (κ/ε) x²`
(Galí's `periodLoss_eq_scaled`). -/
theorem eq_18_20_period {β θ σ ψ ε : ℝ} (hlam : (1 - θ) * (1 - β * θ) / θ ≠ 0) (hε : ε ≠ 0)
    (x infl : ℝ) :
    ((σ + ψ) * x ^ 2 + ε / ((1 - θ) * (1 - β * θ) / θ) * infl ^ 2) / 2 =
      ε / (2 * ((1 - θ) * (1 - β * θ) / θ)) *
        (infl ^ 2 + (1 - θ) * (1 - β * θ) * (σ + ψ) / θ / ε * x ^ 2) := by
  have hl : Gali.DiscretionCommitment.LossAndCostPush.lambdaNK β θ 0 ε =
      (1 - θ) * (1 - β * θ) / θ := by
    simp [Gali.DiscretionCommitment.LossAndCostPush.lambdaNK,
      Gali.DiscretionCommitment.LossAndCostPush.bigTheta]
  have hg : Gali.DiscretionCommitment.LossAndCostPush.gapCoeff σ ψ 0 = σ + ψ := by
    simp [Gali.DiscretionCommitment.LossAndCostPush.gapCoeff]
  have h := Gali.DiscretionCommitment.LossAndCostPush.periodLoss_eq_scaled (β := β) (θ := θ)
    (σ := σ) (φ := ψ) (α := 0) (ε := ε) (by rw [hl]; exact hlam) hε x infl
  rw [hl, hg, (eq_18_20_weight (β := β) (θ := θ) (σ := σ) (ψ := ψ) (ε := ε)).2] at h
  exact h

/-- **AKMM, (18.20), p. 547 and footnote 11 (the second-order approximation)**: around a steady
state made efficient by the subsidy (`w′(N) N = −u′(C) C`, Galí's condition at `α = 0`), with
first-order log deviations `y, a, z`, a second-order dispersion term `v`, the dispersion
`d = (ε/2) v + O(s³)` and `n = y − a + d`, period utility satisfies
`(U_t − U)/(U_c C) = −½[(σ + ψ)(y − ψ_ya a)² + ε v] + t.i.p. + O(s³)` (Galí's
`Welfare.period_utility_normalised` at `α = 0`). -/
theorem eq_18_20_utility {u w : ℝ → ℝ} {C N σ ψ ε : ℝ} {y n a z d v : ℝ → ℝ}
    (hK : deriv u C * C ≠ 0) (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hψ : iteratedDeriv 2 w N * N = ψ * deriv w N)
    (hEff : deriv w N * N = -(deriv u C * C)) (hden : σ + ψ ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / 2 * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, n s = y s - a s + d s) :
    (fun s => ((u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) -
        (u C + w N)) / (deriv u C * C)
        - (-(1 / 2) * ((σ + ψ) * (y s - (1 + ψ) / (σ + ψ) * a s) ^ 2 + ε * v s) +
          Gali.MonetaryPolicyDesign.Welfare.tip (u C + w N) (deriv u C * C) σ ψ 0 (a s) (z s) /
            (deriv u C * C)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hT : Gali.MonetaryPolicyDesign.Welfare.bigTheta 0 ε = 1 := by
    simp [Gali.MonetaryPolicyDesign.Welfare.bigTheta]
  have h := Gali.MonetaryPolicyDesign.Welfare.period_utility_normalised (α := 0) (ε := ε)
    (y := y) (n := n) (a := a) (z := z) (d := d) (v := v) hK hu hw hσ hψ (by rw [hEff]; ring)
    (by norm_num) (by simpa using hden) hy ha hz hv
    (by rw [hT]; simpa using hd) (fun s => by rw [hn s]; ring)
  have hg : Gali.MonetaryPolicyDesign.Welfare.gapCoeff σ ψ 0 = σ + ψ := by
    simp [Gali.MonetaryPolicyDesign.Welfare.gapCoeff]
  have hp : Gali.MonetaryPolicyDesign.Welfare.psiYA σ ψ 0 = (1 + ψ) / (σ + ψ) := by
    simp [Gali.MonetaryPolicyDesign.Welfare.psiYA]
  rw [hg, hp, hT, div_one] at h
  exact h

end AKMM.NominalFrictions
