/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMDynamicOptimization.CRRA
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Expected utility and risk aversion

AKMM, §7.2.2, pp. 194–195 (with fn. 7).

* Risk aversion from Jensen's inequality: for concave `u`, `E[u(c)] ≤ u(E[c])` for every finite
  lottery (`risk_averse_jensen`), strictly for strictly concave `u` and a nondegenerate lottery
  (`risk_averse_strict`); with linear `u` the consumer ranks lotteries by `E[c]`
  (`risk_neutral`).
* The coefficients of absolute and relative risk aversion `−u″/u′`, `−cu″/u′` (`ara`, `rra`)
  are invariant to positive affine transformations (fn. 7, `ara_affine`, `rra_affine`); CARA
  `u = −e^{−αc}` has `ara = α` (`ara_cara`); power utility `(c^{1−σ} − 1)/(1 − σ)` (Chapter 4's
  `crra`) has `rra = σ` (`rra_crra`), and so does `log` with `σ = 1` (`rra_log`).
* EIS (p. 195, corrected): along the CRRA Euler equation `d log(c_{t+1}/c_t)/d log R = 1/σ`
  (`eis_crra`, from Chapter 4's Example 4.2); the printed derivative with respect to `R` is
  `1/(σR)`, not `1/σ` (`eis_printed_counterexample`).
-/

namespace AKMM.Uncertainty

open Real AKMM.DynamicOptimization

/-! ### Jensen's inequality -/

/-- **AKMM, p. 194: risk aversion is implied by Jensen's inequality.** For `u` concave on `D`
and a lottery paying `cᵢ ∈ D` with probabilities `πᵢ`, `Σ πᵢu(cᵢ) ≤ u(Σ πᵢcᵢ)`: the consumer
prefers the expected consumption for sure. -/
theorem risk_averse_jensen {ι : Type*} {D : Set ℝ} {u : ℝ → ℝ} (hu : ConcaveOn ℝ D u)
    (s : Finset ι) {p c : ι → ℝ} (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i = 1)
    (hc : ∀ i ∈ s, c i ∈ D) : ∑ i ∈ s, p i * u (c i) ≤ u (∑ i ∈ s, p i * c i) := by
  simpa [smul_eq_mul] using hu.le_map_sum hp0 hp1 hc

/-- AKMM, p. 194: with strictly concave `u`, a lottery with two outcomes of positive probability
that differ is strictly worse than its expected value. -/
theorem risk_averse_strict {ι : Type*} {D : Set ℝ} {u : ℝ → ℝ} (hu : StrictConcaveOn ℝ D u)
    (s : Finset ι) {p c : ι → ℝ} (hp0 : ∀ i ∈ s, 0 < p i) (hp1 : ∑ i ∈ s, p i = 1)
    (hc : ∀ i ∈ s, c i ∈ D) {j k : ι} (hj : j ∈ s) (hk : k ∈ s) (hjk : c j ≠ c k) :
    ∑ i ∈ s, p i * u (c i) < u (∑ i ∈ s, p i * c i) := by
  simpa [smul_eq_mul] using hu.lt_map_sum hp0 hp1 hc ⟨j, hj, k, hk, hjk⟩

/-- AKMM, p. 194: if `u(c) = ac + b` the consumer ranks lotteries by expected consumption
and is risk neutral: `Σ πᵢu(cᵢ) = u(Σ πᵢcᵢ)`. -/
theorem risk_neutral {ι : Type*} (s : Finset ι) {p c : ι → ℝ} (hp1 : ∑ i ∈ s, p i = 1)
    (a b : ℝ) : ∑ i ∈ s, p i * (a * c i + b) = a * (∑ i ∈ s, p i * c i) + b := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The coefficients of risk aversion -/

/-- AKMM, p. 194: the coefficient of absolute risk aversion `−u″(c)/u′(c)`. -/
noncomputable def ara (u : ℝ → ℝ) (c : ℝ) : ℝ := -deriv (deriv u) c / deriv u c

/-- AKMM, p. 194: the coefficient of relative risk aversion `−cu″(c)/u′(c)`. -/
noncomputable def rra (u : ℝ → ℝ) (c : ℝ) : ℝ := -c * deriv (deriv u) c / deriv u c

theorem ar_deriv_affine (u : ℝ → ℝ) (a b : ℝ) :
    deriv (fun x => a * u x + b) = fun x => a * deriv u x := by
  funext x
  rw [deriv_add_const, deriv_const_mul_field']

/-- AKMM, fn. 7, p. 194: the coefficient of absolute risk aversion is invariant to a positive
affine transformation `v = au + b`, `a > 0`. -/
theorem ara_affine (u : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    ara (fun x => a * u x + b) c = ara u c := by
  simp only [ara, ar_deriv_affine]
  rw [show (fun x => a * deriv u x) = fun x => a * deriv u x + 0 by simp, ar_deriv_affine]
  change -(a * deriv (deriv u) c) / (a * deriv u c) = -deriv (deriv u) c / deriv u c
  rw [← mul_neg, mul_div_mul_left _ _ ha.ne']

/-- AKMM, p. 194: so is the coefficient of relative risk aversion. -/
theorem rra_affine (u : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    rra (fun x => a * u x + b) c = rra u c := by
  simp only [rra, ar_deriv_affine]
  rw [show (fun x => a * deriv u x) = fun x => a * deriv u x + 0 by simp, ar_deriv_affine]
  field_simp

/-- **AKMM, p. 194: CARA utility.** For `u(c) = −exp(−αc)` with `α ≠ 0`, the coefficient of
absolute risk aversion is `α` at every `c`. -/
theorem ara_cara {α : ℝ} (hα : α ≠ 0) (c : ℝ) : ara (fun x => -exp (-α * x)) c = α := by
  have h1 : deriv (fun x => -exp (-α * x)) = fun x => α * exp (-α * x) := by
    funext x
    have h := ((hasDerivAt_id' x).const_mul (-α)).exp.neg
    exact h.deriv.trans (by ring)
  have h2 : deriv (fun x => α * exp (-α * x)) = fun x => -α ^ 2 * exp (-α * x) := by
    funext x
    have h := ((hasDerivAt_id' x).const_mul (-α)).exp.const_mul α
    exact h.deriv.trans (by ring)
  simp only [ara, h1, h2]
  field_simp

/-- **AKMM, p. 194: power utility has constant relative risk aversion `σ`.** For
`u(c) = (c^{1−σ} − 1)/(1 − σ)` (`σ ≠ 1`) and `c > 0`, `−cu″(c)/u′(c) = σ`. -/
theorem rra_crra {σ : ℝ} (hσ : σ ≠ 1) {c : ℝ} (hc : 0 < c) : rra (crra σ) c = σ := by
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
  have hd : ∀ x, 0 < x → deriv (crra σ) x = x ^ (-σ) := fun x hx => by
    have h := ((hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')).sub_const 1).div_const
      (1 - σ)
    have e : crra σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) := rfl
    rw [e, h.deriv]
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp
  have hev : deriv (crra σ) =ᶠ[nhds c] fun x => x ^ (-σ) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hc) fun x hx => hd x hx
  have hdd : deriv (deriv (crra σ)) c = -σ * c ^ (-σ - 1) := by
    rw [hev.deriv_eq, (hasDerivAt_rpow_const (p := -σ) (Or.inl hc.ne')).deriv]
  simp only [rra, hdd, hd c hc]
  have hc' : c ^ (-σ - 1) = c ^ (-σ) / c := by
    rw [rpow_sub hc, rpow_one]
  rw [hc']
  have : 0 < c ^ (-σ) := rpow_pos_of_pos hc _
  field_simp

/-- AKMM, p. 194: logarithmic utility (the case `σ = 1`) has relative risk aversion one. -/
theorem rra_log {c : ℝ} (hc : 0 < c) : rra Real.log c = 1 := by
  have hev : deriv Real.log =ᶠ[nhds c] fun x => x⁻¹ :=
    Filter.eventually_of_mem (Ioi_mem_nhds hc) fun x _ => Real.deriv_log x
  have hdd : deriv (deriv Real.log) c = -(c ^ 2)⁻¹ := by
    rw [hev.deriv_eq, deriv_inv]
  simp only [rra, hdd, Real.deriv_log]
  field_simp

/-! ### The elasticity of intertemporal substitution -/

/-- **AKMM, p. 195 (corrected): the EIS of power utility is `1/σ`.** The Euler equation
`c_t^{−σ} = βc_{t+1}^{−σ}R` gives `c_{t+1}/c_t = β^{1/σ}R^{1/σ}`, and, writing `R = eˣ`,
`log(c_{t+1}/c_t)` has derivative `1/σ` with respect to `x = log R` (Chapter 4's Example 4.2). -/
theorem eis_crra {σ β R c0 c1 : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R) (hc0 : 0 < c0)
    (hc1 : 0 < c1) (h : c0 ^ (-σ) = β * c1 ^ (-σ) * R) :
    c1 / c0 = β ^ (1 / σ) * R ^ (1 / σ) ∧
      HasDerivAt (fun x => Real.log (β ^ (1 / σ) * Real.exp x ^ (1 / σ))) (1 / σ) (Real.log R) :=
  ⟨example42_ratio hσ hβ hR hc0 hc1 h, example42_eis hβ _⟩

/-- AKMM, p. 195: the printed `d log[c_{t+1}/c_t]/dR_{t+1} = 1/σ` is false: the derivative of
`log(β^{1/σ}R^{1/σ})` with respect to `R` is `1/(σR)`, which at `σ = 1`, `R = 2` is `1/2`. -/
theorem eis_printed_counterexample {σ β R : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R => Real.log (β ^ (1 / σ) * R ^ (1 / σ))) (1 / (σ * R)) R ∧
      (1 : ℝ) / (1 * 2) ≠ 1 / 1 := by
  refine ⟨?_, by norm_num⟩
  have e : ∀ᶠ x in nhds R, Real.log (β ^ (1 / σ) * x ^ (1 / σ)) =
      Real.log (β ^ (1 / σ)) + 1 / σ * Real.log x := by
    filter_upwards [Ioi_mem_nhds hR] with x hx
    rw [Real.log_mul (rpow_pos_of_pos hβ _).ne' (rpow_pos_of_pos hx _).ne',
      Real.log_rpow hx]
  have hd : HasDerivAt (fun x => Real.log (β ^ (1 / σ)) + 1 / σ * Real.log x)
      (1 / σ * R⁻¹) R := ((Real.hasDerivAt_log hR.ne').const_mul _).const_add _
  refine (hd.congr_of_eventuallyEq e).congr_deriv ?_
  field_simp

end AKMM.Uncertainty
