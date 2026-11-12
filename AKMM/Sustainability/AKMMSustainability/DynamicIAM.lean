/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMSustainability.StaticIAM
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# The market equilibrium of the dynamic integrated assessment model

AKMM, §25.4.2 (pp. 768–770) and Appendix 25.A (p. 909).

* **Energy services** (25.22), (25.26)–(25.27), for any finite set of energy sources with
  weights `λ_i > 0`, prices `p_i > 0` and `ρ < 1`, `ρ ≠ 0`: at the demands (25.27)
  `e_i = E(Pλ_i/p_i)^{1/(1−ρ)}` with the price index (25.26), the aggregate equals `E`
  (`eq_25_27_index`), spending is `PE` (`eq_25_27_cost`), and the first-order conditions hold
  with multiplier `P`: `p_i = P λ_i E^{1−ρ}e_i^{ρ−1}` (`eq_25_27_foc`). `P` is the least cost of a
  unit of energy services: any inputs delivering `E` cost at least `PE` (`eq_25_26_least_cost`).
  This is the many-input version of Obstfeld–Rogoff's two-good duality (`RealExchangeRate`).
* (25.28): the final-good firm's condition `P = νÃE^{ν−1}` iff `E = (νÃ/P)^{1/(1−ν)}`
  (`eq_25_28`).
* **The saving rate** (p. 770). With the rebate on factor income, the return on saving made at
  `t` is `(1 + Γ_{t+1})r_{t+1}`, and the Euler equation is equivalent to
  `(1 − s_{t+1})/(1 − s_t) = αβ/(s_t(1 − ν))` (`eq_25_29_saving`). The book prints
  `(1 + Γ_t)` in (25.29) and `(1 + s_{t+1})/(1 + s_t)` in the next display; both are wrong
  (`eq_25_29_printed_false`, `eq_25_29_saving_printed_false`). The constant rate
  `s̄ = αβ/(1 − ν)` solves it (`saving_const`) and is the only fixed point in `(0, 1)`
  (`saving_fixed_iff`); every path from below `s̄` leaves `(0, 1)` (`saving_below`); every path
  from above stays in `(s̄, 1)` and converges to `1` (`saving_above`, `saving_above_tendsto`) —
  it is not explosive, but it violates the transversality condition:
  `β^t K_{t+1}/C_t = β^t s_t/(1 − s_t) → ∞` (`saving_above_tvc`, needs `α + ν < 1`). So
  `s̄` is the only solution consistent with optimality, which is the book's claim made precise.
* **Appendix 25.A**: combining the demands gives
  `λ_o/λ_κ = (e_o/e_κ)^{1−ρ}(p_o/p_κ)` (`eq_25_A_ratio`; the book writes `p_{1,t}` for `p_{o,t}`),
  and with `λ_o + λ_c + λ_g = 1` the weights are pinned down by the two ratios
  (`eq_25_A_normalize`).
-/

namespace AKMM.Sustainability

open Real Filter Topology Finset

variable {ι : Type*} [Fintype ι]

/-- AKMM, (25.22), p. 768: the energy-services aggregate `E = (Σ_i λ_i e_i^ρ)^{1/ρ}`. -/
noncomputable def energyAgg (lam : ι → ℝ) (ρ : ℝ) (e : ι → ℝ) : ℝ :=
  (∑ i, lam i * e i ^ ρ) ^ (1 / ρ)

/-- The sum `D = Σ_i λ_i^{1/(1−ρ)} p_i^{ρ/(ρ−1)}`. -/
noncomputable def energyD (lam p : ι → ℝ) (ρ : ℝ) : ℝ :=
  ∑ i, lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1))

/-- AKMM, (25.26), p. 769: the price index of energy services `P = D^{(ρ−1)/ρ}`. -/
noncomputable def energyPrice (lam p : ι → ℝ) (ρ : ℝ) : ℝ := energyD lam p ρ ^ ((ρ - 1) / ρ)

/-- AKMM, (25.27), p. 769: the demand `e_i = E(Pλ_i/p_i)^{1/(1−ρ)}`. -/
noncomputable def energyDemand (lam p : ι → ℝ) (ρ E : ℝ) (i : ι) : ℝ :=
  E * (energyPrice lam p ρ * lam i / p i) ^ (1 / (1 - ρ))

omit [Fintype ι] in
/-- The demand of each input is positive. -/
theorem energyDemand_pos [Fintype ι] [Nonempty ι] {lam p : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (hE : 0 < E) (i : ι) :
    0 < energyDemand lam p ρ E i := by
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have hP : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
  have := hl i; have := hp i
  unfold energyDemand; positivity

/-- `(Pλ_i/p_i)^{ρ/(1−ρ)} λ_i = λ_i^{1/(1−ρ)}p_i^{ρ/(ρ−1)} P^{ρ/(1−ρ)}` and
`P^{ρ/(1−ρ)} = D^{−1}`: the key exponent bookkeeping. -/
theorem energy_term {lam p P D ρ : ℝ} (hl : 0 < lam) (hp : 0 < p) (hD : 0 < D) (hρ1 : ρ < 1)
    (hρ0 : ρ ≠ 0) (hP : P = D ^ ((ρ - 1) / ρ)) :
    lam * ((P * lam / p) ^ (1 / (1 - ρ))) ^ ρ =
      lam ^ (1 / (1 - ρ)) * p ^ (ρ / (ρ - 1)) / D := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  have hρ1' : ρ - 1 ≠ 0 := by linarith
  have hPpos : 0 < P := by rw [hP]; positivity
  rw [← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hp.le,
    Real.mul_rpow hPpos.le hl.le, hP, ← Real.rpow_mul hD.le]
  have e1 : (ρ - 1) / ρ * (1 / (1 - ρ) * ρ) = -1 := by field_simp; ring
  have e2 : p ^ (1 / (1 - ρ) * ρ) = (p ^ (ρ / (ρ - 1)))⁻¹ := by
    rw [← Real.rpow_neg hp.le]; congr 1; field_simp; ring
  have e3 : lam * lam ^ (1 / (1 - ρ) * ρ) = lam ^ (1 / (1 - ρ)) := by
    rw [← Real.rpow_one_add' hl.le (by
      rw [show (1 : ℝ) + 1 / (1 - ρ) * ρ = 1 / (1 - ρ) by field_simp; ring]
      exact one_div_ne_zero h1ρ)]
    congr 1; field_simp; ring
  rw [e1, Real.rpow_neg_one, e2]
  have hpp : 0 < p ^ (ρ / (ρ - 1)) := by positivity
  calc lam * (D⁻¹ * lam ^ (1 / (1 - ρ) * ρ) / (p ^ (ρ / (ρ - 1)))⁻¹)
      = (lam * lam ^ (1 / (1 - ρ) * ρ)) * p ^ (ρ / (ρ - 1)) / D := by field_simp
    _ = _ := by rw [e3]

omit [Fintype ι] in
/-- AKMM, (25.26)–(25.27), p. 769: at the demands (25.27) the aggregate (25.22) equals `E`. -/
theorem eq_25_27_index [Fintype ι] [Nonempty ι] {lam p : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (hE : 0 < E) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) :
    energyAgg lam ρ (energyDemand lam p ρ E) = E := by
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have hsum : ∑ i, lam i * energyDemand lam p ρ E i ^ ρ = E ^ ρ := by
    have : ∀ i, lam i * energyDemand lam p ρ E i ^ ρ =
        E ^ ρ * (lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1)) / energyD lam p ρ) := by
      intro i
      have hPpos : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
      have := hl i; have := hp i
      rw [energyDemand, Real.mul_rpow hE.le (by positivity),
        ← energy_term (hl i) (hp i) hD hρ1 hρ0 rfl]
      unfold energyPrice
      ring
    rw [sum_congr rfl fun i _ => this i, ← mul_sum, ← sum_div]
    rw [show ∑ i, lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1)) = energyD lam p ρ from rfl,
      div_self hD.ne', mul_one]
  rw [energyAgg, hsum, ← Real.rpow_mul hE.le, mul_one_div_cancel hρ0, Real.rpow_one]

omit [Fintype ι] in
/-- AKMM, p. 769: spending on the demands (25.27) is `Σ_i p_i e_i = PE`. -/
theorem eq_25_27_cost [Fintype ι] [Nonempty ι] {lam p : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (hE : 0 < E) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) :
    ∑ i, p i * energyDemand lam p ρ E i = energyPrice lam p ρ * E := by
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  have hρ1' : ρ - 1 ≠ 0 := by linarith
  have hPpos : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
  set P := energyPrice lam p ρ with hP
  -- `p_i (Pλ_i/p_i)^{1/(1−ρ)} = P^{1/(1−ρ)} λ_i^{1/(1−ρ)} p_i^{ρ/(ρ−1)}`
  have hterm : ∀ i, p i * energyDemand lam p ρ E i =
      E * P ^ (1 / (1 - ρ)) * (lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1))) := by
    intro i
    have := hl i; have := hp i
    rw [energyDemand, Real.div_rpow (by positivity) (hp i).le,
      Real.mul_rpow hPpos.le (hl i).le]
    have : p i / p i ^ (1 / (1 - ρ)) = p i ^ (ρ / (ρ - 1)) := by
      rw [← Real.rpow_one_sub' (hp i).le (by
        rw [show (1 : ℝ) - 1 / (1 - ρ) = -ρ / (1 - ρ) by field_simp; ring]
        exact div_ne_zero (neg_ne_zero.mpr hρ0) h1ρ)]
      congr 1; field_simp; ring
    rw [← this]
    field_simp
  rw [sum_congr rfl fun i _ => hterm i, ← mul_sum,
    show ∑ i, lam i ^ (1 / (1 - ρ)) * p i ^ (ρ / (ρ - 1)) = energyD lam p ρ from rfl]
  -- `P^{1/(1−ρ)} D = P`
  have hPD : P ^ (1 / (1 - ρ)) * energyD lam p ρ = P := by
    have hp1 : P ^ (1 / (1 - ρ)) = energyD lam p ρ ^ (-(1 / ρ)) := by
      rw [hP, energyPrice, ← Real.rpow_mul hD.le]; congr 1; field_simp; ring
    rw [hp1, hP, energyPrice, ← Real.rpow_add_one hD.ne']
    congr 1; field_simp; ring
  rw [mul_assoc, hPD]
  ring

/-- AKMM, p. 769: the first-order conditions of the energy-service provider with multiplier
`P`: `p_i = P · ∂E/∂e_i = P λ_i E^{1−ρ} e_i^{ρ−1}` at the demands (25.27). -/
theorem eq_25_27_foc {lam p ρ E P : ℝ} (hl : 0 < lam) (hp : 0 < p) (hE : 0 < E) (hP : 0 < P)
    (hρ1 : ρ < 1) : P * lam * E ^ (1 - ρ) * (E * (P * lam / p) ^ (1 / (1 - ρ))) ^ (ρ - 1) = p := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  rw [Real.mul_rpow hE.le (by positivity), ← Real.rpow_mul (by positivity)]
  have e1 : 1 / (1 - ρ) * (ρ - 1) = -1 := by field_simp; ring
  rw [e1, Real.rpow_neg_one]
  have : E ^ (1 - ρ) * E ^ (ρ - 1) = 1 := by
    rw [← Real.rpow_add hE]; simp
  rw [show P * lam * E ^ (1 - ρ) * (E ^ (ρ - 1) * (P * lam / p)⁻¹) =
    (E ^ (1 - ρ) * E ^ (ρ - 1)) * (P * lam * (P * lam / p)⁻¹) by ring, this, one_mul, inv_div]
  field_simp

omit [Fintype ι] in
/-- AKMM, p. 769, duality ("cost minimization ... delivers that this price index is a CES
function of the different input costs"): any positive inputs `e` delivering at least `E` units
of energy services cost at least `PE`. The proof uses the weights
`ω_i = λ_i e*_i^ρ/E^ρ` and a tangent line of `x ↦ x^ρ` at the weighted mean of `e_i/e*_i`. -/
theorem eq_25_26_least_cost [Fintype ι] [Nonempty ι] {lam p e : ι → ℝ} {ρ E : ℝ}
    (hl : ∀ i, 0 < lam i) (hp : ∀ i, 0 < p i) (he : ∀ i, 0 < e i) (hE : 0 < E) (hρ1 : ρ < 1)
    (hρ0 : ρ ≠ 0) (hdel : E ≤ energyAgg lam ρ e) :
    energyPrice lam p ρ * E ≤ ∑ i, p i * e i := by
  set es := energyDemand lam p ρ E with hes
  have hesp : ∀ i, 0 < es i := energyDemand_pos hl hp hE
  have hD : 0 < energyD lam p ρ := by
    unfold energyD
    exact Finset.sum_pos (fun i _ => by have := hl i; have := hp i; positivity)
      Finset.univ_nonempty
  have hPpos : 0 < energyPrice lam p ρ := by unfold energyPrice; positivity
  set P := energyPrice lam p ρ with hP
  have hidx := eq_25_27_index hl hp hE hρ1 hρ0
  have hcost := eq_25_27_cost hl hp hE hρ1 hρ0
  -- weights and the weighted mean of the ratios
  set ω : ι → ℝ := fun i => lam i * es i ^ ρ / E ^ ρ with hω
  have hsumes : ∑ i, lam i * es i ^ ρ = E ^ ρ := by
    have h := hidx
    rw [energyAgg] at h
    have hpos : 0 < ∑ i, lam i * es i ^ ρ :=
      Finset.sum_pos (fun i _ => by have := hl i; have := hesp i; positivity)
        Finset.univ_nonempty
    calc ∑ i, lam i * es i ^ ρ = ((∑ i, lam i * es i ^ ρ) ^ (1 / ρ)) ^ ρ := by
          rw [← Real.rpow_mul hpos.le, one_div_mul_cancel hρ0, Real.rpow_one]
      _ = E ^ ρ := by rw [h]
  have hω1 : ∑ i, ω i = 1 := by
    rw [hω, ← sum_div, hsumes, div_self (by positivity)]
  set x : ι → ℝ := fun i => e i / es i with hx
  set mbar := ∑ i, ω i * x i with hmbar1
  -- `ω_i x_i = p_i e_i/(PE)` by the first-order conditions
  have hfoc : ∀ i, ω i * x i = p i * e i / (P * E) := by
    intro i
    have hf := eq_25_27_foc (hl i) (hp i) hE hPpos hρ1
    rw [← show es i = E * (P * lam i / p i) ^ (1 / (1 - ρ)) from rfl] at hf
    have := hesp i
    have hes1 : es i ^ ρ = es i ^ (ρ - 1) * es i := by
      rw [Real.rpow_sub_one this.ne']; field_simp
    have hE1 : E ^ (1 - ρ) * E ^ ρ = E := by
      rw [← Real.rpow_add hE]; simp
    have hlam : lam i * es i ^ (ρ - 1) = p i / (P * E ^ (1 - ρ)) := by
      rw [eq_div_iff (by positivity), ← hf]; ring
    calc ω i * x i = lam i * es i ^ (ρ - 1) * e i / E ^ ρ := by
          simp only [hω, hx]; rw [hes1]; field_simp
      _ = p i / (P * E ^ (1 - ρ)) * e i / E ^ ρ := by rw [hlam]
      _ = p i * e i / (P * (E ^ (1 - ρ) * E ^ ρ)) := by field_simp
      _ = p i * e i / (P * E) := by rw [hE1]
  have hmbar : mbar = (∑ i, p i * e i) / (P * E) := by
    rw [hmbar1, sum_congr rfl fun i _ => hfoc i, ← sum_div]
  have hmpos : 0 < mbar := by
    rw [hmbar]
    exact div_pos (Finset.sum_pos (fun i _ => mul_pos (hp i) (he i)) Finset.univ_nonempty)
      (by positivity)
  -- the aggregate relative to `E`: `Σ ω_i x_i^ρ = (energyAgg e / E)^ρ`
  have hagg : ∑ i, ω i * x i ^ ρ = (∑ i, lam i * e i ^ ρ) / E ^ ρ := by
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    have := hesp i; have := he i
    simp only [hω, hx]
    rw [Real.div_rpow (he i).le (hesp i).le]
    field_simp
  have hsumpos : 0 < ∑ i, lam i * e i ^ ρ :=
    Finset.sum_pos (fun i _ => by have := hl i; have := he i; positivity) Finset.univ_nonempty
  have hωpos : ∀ i, 0 ≤ ω i := fun i => by
    have := hl i; have := hesp i; simp only [hω]; positivity
  have hEsum : ∑ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) = mbar ^ ρ := by
    have : ∀ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) =
        ω i * mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (ω i * x i) - ρ * mbar ^ (ρ - 1) * mbar * ω i :=
      fun i => by ring
    rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, sum_add_distrib, ← sum_mul,
      ← mul_sum, ← mul_sum, hω1, ← hmbar1]
    ring
  -- compare `energyAgg e` with `mbar · E`
  have key : energyAgg lam ρ e ≤ mbar * E := by
    rcases lt_or_gt_of_ne hρ0 with hneg | hpos
    · -- `ρ < 0`: `x^ρ` convex, `Σω x^ρ ≥ m̄^ρ`, and `y ↦ y^{1/ρ}` is decreasing
      have hj : mbar ^ ρ ≤ ∑ i, ω i * x i ^ ρ := by
        have : ∑ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) ≤
            ∑ i, ω i * x i ^ ρ := by
          refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hωpos i)
          exact ObstfeldRogoff.RealExchangeRate.CESIndex.ces_tangent_le_rpow hneg.le
            (div_pos (he i) (hesp i)) hmpos
        linarith
      rw [hagg] at hj
      have h2 : ((∑ i, lam i * e i ^ ρ) / E ^ ρ) ^ (1 / ρ) ≤ (mbar ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hj (by
          have : 1 / ρ < 0 := one_div_neg.mpr hneg; linarith)
      rw [← Real.rpow_mul hmpos.le, mul_one_div_cancel hρ0, Real.rpow_one,
        Real.div_rpow hsumpos.le (by positivity), ← Real.rpow_mul hE.le,
        mul_one_div_cancel hρ0, Real.rpow_one, div_le_iff₀ hE] at h2
      exact h2
    · -- `0 < ρ < 1`: `x^ρ` concave, `Σω x^ρ ≤ m̄^ρ`, and `y ↦ y^{1/ρ}` is increasing
      have hj : ∑ i, ω i * x i ^ ρ ≤ mbar ^ ρ := by
        have : ∑ i, ω i * x i ^ ρ ≤
            ∑ i, ω i * (mbar ^ ρ + ρ * mbar ^ (ρ - 1) * (x i - mbar)) := by
          refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hωpos i)
          exact ObstfeldRogoff.RealExchangeRate.CESIndex.ces_rpow_le_tangent hpos.le hρ1.le
            (div_pos (he i) (hesp i)).le hmpos
        linarith
      rw [hagg] at hj
      have h2 : ((∑ i, lam i * e i ^ ρ) / E ^ ρ) ^ (1 / ρ) ≤ (mbar ^ ρ) ^ (1 / ρ) :=
        Real.rpow_le_rpow (by positivity) hj (by positivity)
      rw [← Real.rpow_mul hmpos.le, mul_one_div_cancel hρ0, Real.rpow_one,
        Real.div_rpow hsumpos.le (by positivity), ← Real.rpow_mul hE.le,
        mul_one_div_cancel hρ0, Real.rpow_one, div_le_iff₀ hE] at h2
      exact h2
  rw [hmbar] at key
  have : E ≤ (∑ i, p i * e i) / (P * E) * E := le_trans hdel key
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

/-- AKMM, (25.28), p. 770: the final-good firm's condition `P = νÃE^{ν−1}`, with
`Ã = A L^{1−α−ν}K^α`, holds iff `E = (νÃ/P)^{1/(1−ν)}`. -/
theorem eq_25_28 {ν At P E : ℝ} (hν0 : 0 < ν) (hν1 : ν < 1) (hA : 0 < At) (hP : 0 < P)
    (hE : 0 < E) : P = ν * At * E ^ (ν - 1) ↔ E = (ν * At / P) ^ (1 / (1 - ν)) := by
  have := eq_25_16 hν0 hν1 hA (p := P) (τ := 0) (by simpa using hP) hE
  simp only [add_zero] at this
  rw [eq_comm, this, staticE, add_zero]

/-- AKMM, (25.29) corrected, p. 770: with `C_t = (1 − s_t)(1 + Γ_t)Ŷ_t`,
`K_{t+1} = s_t(1 + Γ_t)Ŷ_t`, `Ŷ = (1 − ν)Y` and `r_{t+1} = αY_{t+1}/K_{t+1}`, the Euler equation
`C_{t+1}/C_t = β(1 + Γ_{t+1})r_{t+1}` is equivalent to
`(1 − s_{t+1})/(1 − s_t) = αβ/(s_t(1 − ν))`. -/
theorem eq_25_29_saving {α β ν s s' Γ Γ' Y Y' : ℝ} (hs : 0 < s) (hs1 : s < 1) (hν : ν < 1)
    (hΓ : 0 < 1 + Γ) (hΓ' : 0 < 1 + Γ') (hY : 0 < Y) (hY' : 0 < Y') :
    (1 - s') * (1 + Γ') * ((1 - ν) * Y') / ((1 - s) * (1 + Γ) * ((1 - ν) * Y)) =
        β * (1 + Γ') * (α * Y' / (s * (1 + Γ) * ((1 - ν) * Y))) ↔
      (1 - s') / (1 - s) = α * β / (s * (1 - ν)) := by
  have h1 : (1 : ℝ) - s ≠ 0 := by linarith
  have h2 : (1 : ℝ) - ν ≠ 0 := by linarith
  set k := (1 + Γ') * Y' / ((1 + Γ) * Y) with hk
  have hk0 : 0 < k := by positivity
  have hL : (1 - s') * (1 + Γ') * ((1 - ν) * Y') / ((1 - s) * (1 + Γ) * ((1 - ν) * Y)) =
      (1 - s') / (1 - s) * k := by
    rw [hk]; field_simp
  have hR : β * (1 + Γ') * (α * Y' / (s * (1 + Γ) * ((1 - ν) * Y))) =
      α * β / (s * (1 - ν)) * k := by
    rw [hk]; field_simp
  rw [hL, hR]
  exact ⟨fun h => mul_right_cancel₀ hk0.ne' h, fun h => by rw [h]⟩

/-- AKMM, p. 770: the display after (25.29), `(1 + s_{t+1})/(1 + s_t) = αβ/(s_t(1 − ν))`, is not
what the Euler equation gives: with `α = β = ν = 1/2`, `s_t = 3/4`, `s_{t+1} = 5/6` the correct
equation holds and the printed one fails. -/
theorem eq_25_29_saving_printed_false :
    (1 - (5 / 6 : ℝ)) / (1 - 3 / 4) = (1 / 2) * (1 / 2) / ((3 / 4) * (1 - 1 / 2)) ∧
      (1 + (5 / 6 : ℝ)) / (1 + 3 / 4) ≠ (1 / 2) * (1 / 2) / ((3 / 4) * (1 - 1 / 2)) := by
  constructor <;> norm_num

/-- AKMM, (25.29) as printed, p. 770: with the rebate rate of date `t`, `(1 + Γ_t)`, in place of
the rebate earned on the return, `(1 + Γ_{t+1})`, the constant saving rate `s̄` does not solve the
Euler equation whenever the rebate changes, `Γ_{t+1} ≠ Γ_t`. -/
theorem eq_25_29_printed_false {α β ν Γ Γ' Y Y' : ℝ} (hab : 0 < α * β) (hν : ν < 1)
    (hs1 : α * β / (1 - ν) < 1) (hΓ : 0 < 1 + Γ) (hΓ' : 0 < 1 + Γ') (hY : 0 < Y) (hY' : 0 < Y')
    (hne : Γ' ≠ Γ) :
    (1 - α * β / (1 - ν)) * (1 + Γ') * ((1 - ν) * Y') /
        ((1 - α * β / (1 - ν)) * (1 + Γ) * ((1 - ν) * Y)) ≠
      β * (1 + Γ) * (α * Y' / (α * β / (1 - ν) * (1 + Γ) * ((1 - ν) * Y))) := by
  have h1ν : 0 < 1 - ν := by linarith
  have hs : 0 < 1 - α * β / (1 - ν) := by linarith
  have hb : β ≠ 0 := right_ne_zero_of_mul hab.ne'
  have ha : α ≠ 0 := left_ne_zero_of_mul hab.ne'
  have hne0 : 1 - ν - α * β ≠ 0 := by
    have := (div_lt_one h1ν).mp hs1; exact (by linarith : (0 : ℝ) < 1 - ν - α * β).ne'
  have hL : (1 - α * β / (1 - ν)) * (1 + Γ') * ((1 - ν) * Y') /
      ((1 - α * β / (1 - ν)) * (1 + Γ) * ((1 - ν) * Y)) = (1 + Γ') / (1 + Γ) * (Y' / Y) := by
    field_simp
  have hR : β * (1 + Γ) * (α * Y' / (α * β / (1 - ν) * (1 + Γ) * ((1 - ν) * Y))) = Y' / Y := by
    field_simp
  rw [hL, hR]
  intro h
  apply hne
  have hYY : 0 < Y' / Y := by positivity
  have : (1 + Γ') / (1 + Γ) = 1 := by
    have := mul_right_cancel₀ hYY.ne' (h.trans (one_mul _).symm)
    exact this
  rw [div_eq_one_iff_eq hΓ.ne'] at this
  linarith

/-- The saving-rate map defined by the corrected equation: `s_{t+1} = 1 − s̄(1 − s_t)/s_t`. -/
noncomputable def savingNext (sbar s : ℝ) : ℝ := 1 - sbar * (1 - s) / s

/-- AKMM, p. 770: the constant `s̄ = αβ/(1 − ν)` solves the difference equation. -/
theorem saving_const {sbar : ℝ} (h0 : 0 < sbar) : savingNext sbar sbar = sbar := by
  unfold savingNext; field_simp; ring

/-- AKMM, p. 770: in `(0, 1)` the only rest point of the difference equation is `s̄` (the other
rest point is `s = 1`, zero consumption). -/
theorem saving_fixed_iff {sbar s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    savingNext sbar s = s ↔ s = sbar := by
  unfold savingNext
  constructor
  · intro h
    have h1 : (s - sbar) * (1 - s) = 0 := by field_simp at h; linarith
    rcases mul_eq_zero.mp h1 with h | h
    · linarith
    · linarith
  · rintro rfl; field_simp; ring

/-- AKMM, p. 770: from above `s̄`, the saving rate stays in `(s̄, 1)` and increases. -/
theorem saving_above {sbar : ℝ} (h0 : 0 < sbar) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : sbar < s 0) (hs01 : s 0 < 1) (t : ℕ) :
    sbar < s t ∧ s t < 1 ∧ s t < s (t + 1) := by
  have hstep : ∀ u, sbar < u → u < 1 →
      sbar < savingNext sbar u ∧ savingNext sbar u < 1 ∧ u < savingNext sbar u := by
    intro u hu hu1
    have hu0 : 0 < u := by linarith
    have hd : savingNext sbar u - u = (u - sbar) * (1 - u) / u := by
      unfold savingNext; field_simp; ring
    have hpos : 0 < (u - sbar) * (1 - u) / u := by
      apply div_pos (mul_pos (by linarith) (by linarith)) hu0
    have hlt : savingNext sbar u < 1 := by
      unfold savingNext
      have : 0 < sbar * (1 - u) / u := div_pos (mul_pos h0 (by linarith)) hu0
      linarith
    exact ⟨by linarith, hlt, by linarith⟩
  have hin : ∀ t, sbar < s t ∧ s t < 1 := by
    intro t
    induction t with
    | zero => exact ⟨hs0, hs01⟩
    | succ n ih =>
      rw [hs n]; exact ⟨(hstep _ ih.1 ih.2).1, (hstep _ ih.1 ih.2).2.1⟩
  refine ⟨(hin t).1, (hin t).2, ?_⟩
  rw [hs t]
  exact (hstep _ (hin t).1 (hin t).2).2.2

/-- AKMM, p. 770: from above `s̄` the saving rate converges to `1` (consumption's share of
income vanishes). -/
theorem saving_above_tendsto {sbar : ℝ} (h0 : 0 < sbar) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : sbar < s 0) (hs01 : s 0 < 1) :
    Tendsto s atTop (𝓝 1) := by
  have hab := saving_above h0 hs hs0 hs01
  have hmono : Monotone s := monotone_nat_of_le_succ fun t => (hab t).2.2.le
  have hbdd : BddAbove (Set.range s) := ⟨1, by rintro _ ⟨t, rfl⟩; exact (hab t).2.1.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ t, s t with hL
  have hL0 : s 0 ≤ L := le_ciSup hbdd 0
  have hL1 : L ≤ 1 := ciSup_le fun t => (hab t).2.1.le
  have hLpos : 0 < L := by linarith
  -- `L` is a rest point of the continuous map, so `L = 1`
  have hcont : ContinuousAt (savingNext sbar) L := by
    unfold savingNext
    exact continuousAt_const.sub ((continuousAt_const.mul (continuousAt_const.sub
      continuousAt_id)).div continuousAt_id hLpos.ne')
  have h1 : Tendsto (fun t => s (t + 1)) atTop (𝓝 L) := hlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun t => s (t + 1)) atTop (𝓝 (savingNext sbar L)) := by
    simp only [hs]; exact hcont.tendsto.comp hlim
  have hfix : savingNext sbar L = L := tendsto_nhds_unique h2 h1
  rcases hL1.lt_or_eq with hlt | heq
  · have := (saving_fixed_iff hLpos hlt).mp hfix
    linarith
  · rw [← heq]; exact hlim

/-- AKMM, p. 770: from below `s̄` the saving rate leaves `(0, 1)` in finite time: the solution
is not an equilibrium. -/
theorem saving_below {sbar : ℝ} (h1 : sbar < 1) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : 0 < s 0) (hs0' : s 0 < sbar) :
    ∃ t, s t ≤ 0 := by
  by_contra hcon
  push Not at hcon
  set δ := (sbar - s 0) * (1 - s 0) with hδ
  have hδ0 : 0 < δ := mul_pos (by linarith) (by linarith)
  -- while positive, the rate falls by at least `δ` each period
  have hdec : ∀ t, s t ≤ s 0 - δ * t := by
    intro t
    induction t with
    | zero => simp
    | succ n ih =>
      have hn0 := hcon n
      have hn1 : s n ≤ s 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hn2 : s n < 1 := by linarith
      rw [hs n]
      have hd : savingNext sbar (s n) - s n = (s n - sbar) * (1 - s n) / s n := by
        unfold savingNext; field_simp; ring
      have hb : (s n - sbar) * (1 - s n) / s n ≤ -δ := by
        rw [div_le_iff₀ hn0]
        have k1 : (s n - sbar) ≤ s 0 - sbar := by linarith
        have k2 : 1 - s 0 ≤ 1 - s n := by linarith
        have k3 : (s n - sbar) * (1 - s n) ≤ (s 0 - sbar) * (1 - s 0) := by nlinarith
        have k4 : -δ * s n ≥ -δ := by nlinarith
        nlinarith
      push_cast
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (s 0 / δ)
  have := hdec n
  have := hcon n
  rw [div_lt_iff₀ hδ0] at hn
  nlinarith

/-- AKMM, p. 770, why the paths from above are ruled out: the transversality term
`β^t u'(C_t)K_{t+1} ∝ β^t K_{t+1}/C_t = β^t s_t/(1 − s_t)` diverges along every path from above
`s̄`. With `s̄ = αβ/(1 − ν)` the condition `s̄ < β` used here is `α + ν < 1`. -/
theorem saving_above_tvc {sbar β : ℝ} (h0 : 0 < sbar) (hβ : sbar < β) {s : ℕ → ℝ}
    (hs : ∀ t, s (t + 1) = savingNext sbar (s t)) (hs0 : sbar < s 0) (hs01 : s 0 < 1) :
    Tendsto (fun t => β ^ t * (s t / (1 - s t))) atTop atTop := by
  have hab := saving_above h0 hs hs0 hs01
  have hlim := saving_above_tendsto h0 hs hs0 hs01
  -- pick `σ ∈ (s̄/β, 1)`, so that `q = s̄/σ < β`
  set σ := (sbar / β + 1) / 2 with hσ
  have hβ0 : 0 < β := by linarith
  have hsb : sbar / β < 1 := (div_lt_one hβ0).mpr hβ
  have hσ1 : σ < 1 := by rw [hσ]; linarith
  have hσ0 : sbar / β < σ := by rw [hσ]; linarith
  have hσpos : 0 < σ := by have : 0 < sbar / β := div_pos h0 hβ0; linarith
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp (hlim.eventually (Ici_mem_nhds hσ1))
  · -- for `t ≥ T0`: `1 − s_{t+1} ≤ (s̄/σ)(1 − s_t)`
    set q := sbar / σ with hq
    have hq0 : 0 < q := div_pos h0 hσpos
    have hqβ : q < β := by
      rw [hq, div_lt_iff₀ hσpos]
      have := (div_lt_iff₀ hβ0).mp hσ0
      linarith
    have hdec : ∀ n, 1 - s (T0 + n) ≤ q ^ n * (1 - s T0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hge : σ ≤ s (T0 + n) := (hT0 (T0 + n) (by omega) : σ ≤ s (T0 + n))
        have hpos : 0 < s (T0 + n) := by linarith
        rw [← add_assoc, hs, savingNext, pow_succ]
        have h1s : 0 ≤ 1 - s (T0 + n) := by linarith [(hab (T0 + n)).2.1]
        have : sbar * (1 - s (T0 + n)) / s (T0 + n) ≤ q * (1 - s (T0 + n)) := by
          rw [hq, div_le_iff₀ hpos]
          have key : sbar * (1 - s (T0 + n)) * σ ≤ sbar * (1 - s (T0 + n)) * s (T0 + n) :=
            mul_le_mul_of_nonneg_left hge (mul_nonneg h0.le h1s)
          calc sbar * (1 - s (T0 + n)) = sbar * (1 - s (T0 + n)) * σ / σ := by field_simp
            _ ≤ sbar * (1 - s (T0 + n)) * s (T0 + n) / σ := by gcongr
            _ = sbar / σ * (1 - s (T0 + n)) * s (T0 + n) := by ring
        have hq0' : 0 ≤ q := hq0.le
        nlinarith
    -- hence `β^t s_t/(1 − s_t) ≥ c (β/q)^{t−T0}` with `β/q > 1`
    have hc : 0 < 1 - s T0 := by linarith [(hab T0).2.1]
    have hgrow : Tendsto (fun n : ℕ => (β / q) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hq0).mpr hqβ)
    have hlow : ∀ n, β ^ T0 * σ / (1 - s T0) * (β / q) ^ n ≤
        β ^ (T0 + n) * (s (T0 + n) / (1 - s (T0 + n))) := by
      intro n
      have h1 := hdec n
      have hpos1 : 0 < 1 - s (T0 + n) := by linarith [(hab (T0 + n)).2.1]
      have hge : σ ≤ s (T0 + n) := (hT0 (T0 + n) (by omega) : σ ≤ s (T0 + n))
      have hqn : 0 < q ^ n := pow_pos hq0 n
      have hs0' : 0 ≤ s (T0 + n) := by linarith
      have hfrac : σ / (q ^ n * (1 - s T0)) ≤ s (T0 + n) / (1 - s (T0 + n)) :=
        div_le_div₀ hs0' hge hpos1 h1
      have hb0 : 0 ≤ β ^ T0 * β ^ n := by positivity
      calc β ^ T0 * σ / (1 - s T0) * (β / q) ^ n
          = β ^ T0 * β ^ n * (σ / (q ^ n * (1 - s T0))) := by rw [div_pow]; field_simp
        _ ≤ β ^ T0 * β ^ n * (s (T0 + n) / (1 - s (T0 + n))) :=
            mul_le_mul_of_nonneg_left hfrac hb0
        _ = β ^ (T0 + n) * (s (T0 + n) / (1 - s (T0 + n))) := by rw [pow_add]
    have hk : 0 < β ^ T0 * σ / (1 - s T0) := by positivity
    have hshift : Tendsto (fun n => β ^ (T0 + n) * (s (T0 + n) / (1 - s (T0 + n)))) atTop atTop :=
      tendsto_atTop_mono hlow (hgrow.const_mul_atTop hk)
    have h2 : Tendsto (fun n => (fun t => β ^ t * (s t / (1 - s t))) (n + T0)) atTop atTop :=
      hshift.congr fun n => by simp only [add_comm T0 n]
    exact (tendsto_add_atTop_iff_nat T0).mp h2

/-- AKMM, Appendix 25.A, p. 909: combining the demands (25.27) for oil and source `κ`,
`λ_o/λ_κ = (e_o/e_κ)^{1−ρ}(p_o/p_κ)` (the book writes `p_{1,t}` for `p_{o,t}`). -/
theorem eq_25_A_ratio {lo lk po pk E P ρ : ℝ} (hlo : 0 < lo) (hlk : 0 < lk) (hpo : 0 < po)
    (hpk : 0 < pk) (hE : 0 < E) (hP : 0 < P) (hρ1 : ρ < 1) :
    lo / lk = ((E * (P * lo / po) ^ (1 / (1 - ρ))) / (E * (P * lk / pk) ^ (1 / (1 - ρ)))) ^
      (1 - ρ) * (po / pk) := by
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := (by linarith : (0 : ℝ) < 1 - ρ).ne'
  rw [mul_div_mul_left _ _ hE.ne', Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
    one_div_mul_cancel h1ρ, Real.rpow_one, Real.rpow_one]
  field_simp

/-- AKMM, Appendix 25.A, p. 909: with `λ_o + λ_c + λ_g = 1` and the ratios `λ_o/λ_c = r_c`,
`λ_o/λ_g = r_g`, the weights are `λ_o = 1/(1 + 1/r_c + 1/r_g)`, `λ_c = λ_o/r_c`,
`λ_g = λ_o/r_g`. -/
theorem eq_25_A_normalize {lo lc lg rc rg : ℝ} (hrc : 0 < rc) (hrg : 0 < rg) (hlc : 0 < lc)
    (hlg : 0 < lg) (hsum : lo + lc + lg = 1) (hc : lo / lc = rc) (hg : lo / lg = rg) :
    lo = 1 / (1 + 1 / rc + 1 / rg) ∧ lc = lo / rc ∧ lg = lo / rg := by
  have hlo : lo ≠ 0 := by rintro rfl; simp at hc; linarith
  have hc' : lc = lo / rc := by rw [← hc]; field_simp
  have hg' : lg = lo / rg := by rw [← hg]; field_simp
  refine ⟨?_, hc', hg'⟩
  rw [hc', hg'] at hsum
  have : lo * (1 + 1 / rc + 1 / rg) = 1 := by linear_combination hsum
  have hpos : 0 < 1 + 1 / rc + 1 / rg := by positivity
  rw [eq_div_iff hpos.ne']
  exact this

end AKMM.Sustainability
