/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMContinuousTime.GrowthRates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The continuous-time Hamiltonian and the Euler equation

AKMM, §9.2 (pp. 248–250): (9.19)–(9.26), the box on present- versus current-value
Hamiltonians and the box comparing discrete and continuous Euler equations.

* (9.19)–(9.21): the present-value Hamiltonian `H = e^{−ρt}u(c) + μ(ra + w − c)` and its
  derivatives; (9.20) is (9.24) `e^{−ρt}u'(c) = μ`, and (9.21) is (9.25) `rμ + μ̇ = 0`.
* The integration-by-parts step of the heuristic derivation, on a finite horizon
  (`continuousHamiltonian_integration_by_parts`).
* The current-value Hamiltonian `Ĥ = u(c) + μ̂(ra + w − c)` with `μ = e^{−ρt}μ̂`: `H = e^{−ρt}Ĥ`,
  and (9.22)–(9.23) are equivalent to (9.20)–(9.21).
* (9.26): the Euler equation `−(u''(c)c/u'(c))(ċ/c) = r − ρ`, derived from (9.24)–(9.25) by
  the growth-rate trick (9.5); proved for a time-varying `r(t)`, which (9.35) and (9.37) need.
* The coefficient of relative risk aversion is positive, and equals `σ` for CRRA utility
  `u(c) = (c^{1−σ} − 1)/(1 − σ)`.
* The discrete-continuous box: the linearized discrete Euler equation gives
  `−(u''(c_t)c_t/u'(c_t))((c_{t+1} − c_t)/c_t) = (r − ρ)/(1 + r)`, and the exact Euler equation
  gives it up to the Taylor remainder of `u'`, which is `o(c_{t+1} − c_t)`.

These are the first-order conditions as calculus. That they are necessary for optimality is
the Pontryagin maximum principle, not in Mathlib and not formalised; their sufficiency is
`Mangasarian`.
-/

namespace AKMM.ContinuousTime

open Filter Topology

/-- AKMM, (9.19), p. 248: the present-value Hamiltonian
`H(t) = e^{−ρt}u(c) + μ(ra + w − c)`. -/
noncomputable def ctHamiltonian (ρ r w : ℝ) (u : ℝ → ℝ) (t μ a c : ℝ) : ℝ :=
  Real.exp (-ρ * t) * u c + μ * (r * a + w - c)

/-- AKMM, box p. 249: the current-value Hamiltonian `Ĥ(t) = u(c) + μ̂(ra + w − c)`. -/
noncomputable def ctCurrentHamiltonian (r w : ℝ) (u : ℝ → ℝ) (μh a c : ℝ) : ℝ :=
  u c + μh * (r * a + w - c)

/-- AKMM, (9.20) and (9.24), pp. 248–249: `∂H/∂c = e^{−ρt}u'(c) − μ`, so (9.20) is
`e^{−ρt}u'(c(t)) = μ(t)`. -/
theorem eq_9_20 {ρ r w t μ a c u'c : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u u'c c) :
    HasDerivAt (fun x => ctHamiltonian ρ r w u t μ a x) (Real.exp (-ρ * t) * u'c - μ) c ∧
      (Real.exp (-ρ * t) * u'c - μ = 0 ↔ Real.exp (-ρ * t) * u'c = μ) := by
  refine ⟨?_, sub_eq_zero⟩
  have h := (hu.const_mul (Real.exp (-ρ * t))).add
    (((hasDerivAt_id c).const_sub (r * a + w)).const_mul μ)
  change HasDerivAt (fun x => Real.exp (-ρ * t) * u x + μ * (r * a + w - x)) _ c
  convert h using 1
  · funext x
    simp only [Pi.add_apply, id]
  · ring

/-- AKMM, (9.21) and (9.25), pp. 248–249: `∂H/∂a = rμ`, so (9.21) `∂H/∂a + μ̇ = 0` is
`rμ(t) + μ̇(t) = 0`, i.e. `μ̇/μ = −r`. -/
theorem eq_9_21 {ρ r w t μ μdot a c : ℝ} {u : ℝ → ℝ} :
    HasDerivAt (fun x => ctHamiltonian ρ r w u t μ x c) (r * μ) a ∧
      (r * μ + μdot = 0 ↔ μdot = -r * μ) ∧ (μ ≠ 0 → (r * μ + μdot = 0 ↔ μdot / μ = -r)) := by
  refine ⟨?_, by constructor <;> intro h <;> linarith, fun hμ => ?_⟩
  · have h := ((((hasDerivAt_id a).const_mul r).add_const (w - c)).const_mul μ).const_add
      (Real.exp (-ρ * t) * u c)
    change HasDerivAt (fun x => Real.exp (-ρ * t) * u c + μ * (r * x + w - c)) _ a
    convert h using 1
    · funext x
      simp only [id]
      ring
    · ring
  · rw [div_eq_iff hμ]
    constructor <;> intro h <;> linarith

/-- AKMM, p. 248: the integration-by-parts step of the heuristic derivation, on `[0, T]`:
`∫_0^T μȧ = μ(T)a(T) − μ(0)a(0) − ∫_0^T μ̇a`, so the Lagrangian
`∫_0^T e^{−ρt}u(c) + ∫_0^T μ(ra + w − c − ȧ)` equals
`∫_0^T H − [μ(T)a(T) − μ(0)a(0)] + ∫_0^T μ̇a`. -/
theorem continuousHamiltonian_integration_by_parts {ρ r w T : ℝ} {u : ℝ → ℝ}
    {μ μ' a a' c : ℝ → ℝ} (hμ : ∀ t, HasDerivAt μ (μ' t) t) (ha : ∀ t, HasDerivAt a (a' t) t)
    (hμ' : Continuous μ') (ha' : Continuous a')
    (hint1 : IntervalIntegrable (fun t => Real.exp (-ρ * t) * u (c t)) MeasureTheory.volume 0 T)
    (hint2 : IntervalIntegrable (fun t => μ t * (r * a t + w - c t)) MeasureTheory.volume 0 T) :
    (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) +
        ∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t - a' t) =
      (∫ t in (0 : ℝ)..T, ctHamiltonian ρ r w u t (μ t) (a t) (c t)) -
        (μ T * a T - μ 0 * a 0) + ∫ t in (0 : ℝ)..T, μ' t * a t := by
  have hμc : Continuous μ := continuous_iff_continuousAt.mpr fun t => (hμ t).continuousAt
  have hac : Continuous a := continuous_iff_continuousAt.mpr fun t => (ha t).continuousAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := T)
    (fun t _ => hμ t) (fun t _ => ha t) (hμ'.intervalIntegrable 0 T) (ha'.intervalIntegrable 0 T)
  have hint3 : IntervalIntegrable (fun t => μ t * a' t) MeasureTheory.volume 0 T :=
    (hμc.mul ha').intervalIntegrable 0 T
  have hsplit : ∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t - a' t) =
      (∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t)) - ∫ t in (0 : ℝ)..T, μ t * a' t := by
    rw [← intervalIntegral.integral_sub hint2 hint3]
    congr 1
    funext t
    ring
  have hH : ∫ t in (0 : ℝ)..T, ctHamiltonian ρ r w u t (μ t) (a t) (c t) =
      (∫ t in (0 : ℝ)..T, Real.exp (-ρ * t) * u (c t)) +
        ∫ t in (0 : ℝ)..T, μ t * (r * a t + w - c t) := by
    rw [← intervalIntegral.integral_add hint1 hint2]
    rfl
  rw [hsplit, hH, hibp]
  ring

/-- AKMM, box p. 249: with `μ = e^{−ρt}μ̂`, the present-value Hamiltonian is the discounted
current-value Hamiltonian, `H(t) = e^{−ρt}Ĥ(t)`. -/
theorem continuousHamiltonian_present_current (ρ r w : ℝ) (u : ℝ → ℝ) (t μh a c : ℝ) :
    ctHamiltonian ρ r w u t (Real.exp (-ρ * t) * μh) a c =
      Real.exp (-ρ * t) * ctCurrentHamiltonian r w u μh a c := by
  simp only [ctHamiltonian, ctCurrentHamiltonian]
  ring

/-- AKMM, (9.22), p. 249: with `μ = e^{−ρt}μ̂`, `∂H/∂c = e^{−ρt}∂Ĥ/∂c`, so (9.22) `∂Ĥ/∂c = 0`
is equivalent to (9.20). -/
theorem eq_9_22 {ρ r w t μh a c u'c : ℝ} {u : ℝ → ℝ} (hu : HasDerivAt u u'c c) :
    HasDerivAt (fun x => ctCurrentHamiltonian r w u μh a x) (u'c - μh) c ∧
      (Real.exp (-ρ * t) * u'c - Real.exp (-ρ * t) * μh = 0 ↔ u'c - μh = 0) := by
  refine ⟨?_, ?_⟩
  · have h := hu.add (((hasDerivAt_id c).const_sub (r * a + w)).const_mul μh)
    change HasDerivAt (fun x => u x + μh * (r * a + w - x)) _ c
    convert h using 1
    · funext x
      simp only [Pi.add_apply, id]
    · ring
  · rw [← mul_sub, mul_eq_zero]
    simp [(Real.exp_pos _).ne']

/-- AKMM, (9.23), p. 249: with `μ = e^{−ρt}μ̂`, `μ̇ = e^{−ρt}(μ̂' − ρμ̂)`, so
`∂H/∂a + μ̇ = e^{−ρt}(∂Ĥ/∂a + μ̂' − ρμ̂)` and (9.21) is equivalent to (9.23)
`∂Ĥ/∂a + μ̂' − ρμ̂ = 0`. -/
theorem eq_9_23 {ρ r t μh' : ℝ} {μh : ℝ → ℝ} (hμh : HasDerivAt μh μh' t) :
    HasDerivAt (fun s => Real.exp (-ρ * s) * μh s) (Real.exp (-ρ * t) * (μh' - ρ * μh t)) t ∧
      (r * (Real.exp (-ρ * t) * μh t) + Real.exp (-ρ * t) * (μh' - ρ * μh t) = 0 ↔
        r * μh t + μh' - ρ * μh t = 0) := by
  refine ⟨?_, ?_⟩
  · have he : HasDerivAt (fun s => Real.exp (-ρ * s)) (Real.exp (-ρ * t) * -ρ) t := by
      have := ((hasDerivAt_id t).const_mul (-ρ)).exp
      simpa using this
    convert he.mul hμh using 1
    ring
  · rw [show r * (Real.exp (-ρ * t) * μh t) + Real.exp (-ρ * t) * (μh' - ρ * μh t) =
      Real.exp (-ρ * t) * (r * μh t + μh' - ρ * μh t) by ring, mul_eq_zero]
    simp [(Real.exp_pos _).ne']

/-- AKMM, (9.24)–(9.26), p. 249: the continuous-time Euler equation, for a possibly time-varying
interest rate. If `μ(s) = e^{−ρs}u'(c(s))` near `t` (9.24), `r(t)μ(t) + μ̇(t) = 0` (9.25), and
`u'` has derivative `u''(c(t))` at `c(t)`, then `−ρ + (u''(c)/u'(c))ċ = μ̇/μ = −r` (the growth
trick (9.5)) and `−(u''(c)c/u'(c))(ċ/c) = r − ρ`. -/
theorem eq_9_26 {ρ r t cdot μdot u''c : ℝ} {c μ u' : ℝ → ℝ} (hc : HasDerivAt c cdot t)
    (hu' : HasDerivAt u' u''c (c t)) (hμ : μ =ᶠ[𝓝 t] fun s => Real.exp (-ρ * s) * u' (c s))
    (hμd : HasDerivAt μ μdot t) (h925 : r * μ t + μdot = 0) (hpos : u' (c t) ≠ 0)
    (hc0 : c t ≠ 0) :
    μdot = Real.exp (-ρ * t) * (-ρ * u' (c t) + u''c * cdot) ∧
      -ρ + u''c / u' (c t) * cdot = μdot / μ t ∧ μdot / μ t = -r ∧
      -(u''c * c t / u' (c t)) * (cdot / c t) = r - ρ := by
  have he : HasDerivAt (fun s => Real.exp (-ρ * s)) (Real.exp (-ρ * t) * -ρ) t := by
    have := ((hasDerivAt_id t).const_mul (-ρ)).exp
    simpa using this
  have hcomp : HasDerivAt (fun s => Real.exp (-ρ * s) * u' (c s))
      (Real.exp (-ρ * t) * -ρ * u' (c t) + Real.exp (-ρ * t) * (u''c * cdot)) t :=
    he.mul (hu'.comp t hc)
  have hμt : μ t = Real.exp (-ρ * t) * u' (c t) := hμ.eq_of_nhds
  have h1 : μdot = Real.exp (-ρ * t) * (-ρ * u' (c t) + u''c * cdot) := by
    rw [hμd.unique (hcomp.congr_of_eventuallyEq hμ)]
    ring
  have hE := (Real.exp_pos (-ρ * t)).ne'
  have hμ0 : μ t ≠ 0 := by rw [hμt]; exact mul_ne_zero hE hpos
  have h2 : -ρ + u''c / u' (c t) * cdot = μdot / μ t := by
    rw [h1, hμt]
    field_simp
  have h3 : μdot / μ t = -r := by
    rw [div_eq_iff hμ0]
    linarith
  refine ⟨h1, h2, h3, ?_⟩
  have h4 : u''c / u' (c t) * cdot = ρ - r := by linarith
  calc -(u''c * c t / u' (c t)) * (cdot / c t) = -(u''c / u' (c t) * cdot) := by
        field_simp
    _ = r - ρ := by rw [h4]; ring

/-- AKMM, p. 249: the coefficient of relative risk aversion `−u''(c)c/u'(c)` is positive when
`u'' < 0`, `c > 0` and `u' > 0`. -/
theorem continuousHamiltonian_crra_coefficient_pos {c u'c u''c : ℝ} (hc : 0 < c)
    (hu' : 0 < u'c) (hu'' : u''c < 0) : 0 < -(u''c * c / u'c) := by
  have : u''c * c / u'c < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hu'' hc) hu'
  linarith

/-- AKMM, p. 249 (Section 4.2.4): CRRA utility `u(c) = (c^{1−σ} − 1)/(1 − σ)`, `σ ≠ 1`. -/
noncomputable def crraUtility (σ c : ℝ) : ℝ := (c ^ (1 - σ) - 1) / (1 - σ)

/-- AKMM, p. 249: for CRRA utility and `c > 0`, `u'(c) = c^{−σ}` and `u''(c) = −σc^{−σ−1}`. -/
theorem continuousHamiltonian_crra_derivs {σ c : ℝ} (hσ : σ ≠ 1) (hc : 0 < c) :
    HasDerivAt (crraUtility σ) (c ^ (-σ)) c ∧
      HasDerivAt (fun x : ℝ => x ^ (-σ)) (-σ * c ^ (-σ - 1)) c := by
  have h1σ : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  refine ⟨?_, ?_⟩
  · have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hc.ne')).sub_const 1).div_const
      (1 - σ)
    convert h using 1
    · rfl
    · rw [show 1 - σ - 1 = -σ by ring]
      field_simp
  · exact Real.hasDerivAt_rpow_const (Or.inl hc.ne')

/-- AKMM, p. 249: for CRRA utility the coefficient of relative risk aversion is constant,
`−u''(c)c/u'(c) = σ`. -/
theorem continuousHamiltonian_crra_relative_risk_aversion {σ c : ℝ} (hc : 0 < c) :
    -((-σ * c ^ (-σ - 1)) * c / c ^ (-σ)) = σ := by
  have hpos : 0 < c ^ (-σ) := Real.rpow_pos_of_pos hc _
  have hsplit : c ^ (-σ - 1) * c = c ^ (-σ) := by
    rw [Real.rpow_sub_one hc.ne']
    field_simp
  rw [mul_assoc, hsplit]
  field_simp

/-- AKMM, box p. 250: replacing `u'(c_{t+1})` by its first-order expansion
`u'(c_t) + u''(c_t)(c_{t+1} − c_t)` in the Euler equation (9.14) with `β = 1/(1 + ρ)` gives
`−(u''(c_t)c_t/u'(c_t))((c_{t+1} − c_t)/c_t) = (r − ρ)/(1 + r)`. -/
theorem continuousHamiltonian_discrete_euler_linearized {r ρ c dc u'c u''c : ℝ}
    (hρ : 1 + ρ ≠ 0) (hr : 1 + r ≠ 0) (hu' : u'c ≠ 0) (hc : c ≠ 0)
    (heuler : u'c = 1 / (1 + ρ) * (1 + r) * (u'c + u''c * dc)) :
    -(u''c * c / u'c) * (dc / c) = (r - ρ) / (1 + r) := by
  field_simp at heuler ⊢
  linarith

/-- AKMM, box p. 250, with the remainder: if `u'(c_t) = β(1 + r)u'(c_t + Δ)` exactly, with
`β = 1/(1 + ρ)`, then
`−(u''(c_t)c_t/u'(c_t))(Δ/c_t) = (r − ρ)/(1 + r) + E(Δ)/u'(c_t)`, where the Taylor remainder
`E(Δ) = u'(c_t + Δ) − u'(c_t) − u''(c_t)Δ` is `o(Δ)` as `Δ → 0`. -/
theorem continuousHamiltonian_discrete_euler_remainder {r ρ c dc u''c : ℝ} {u' : ℝ → ℝ}
    (hρ : 1 + ρ ≠ 0) (hr : 1 + r ≠ 0) (hu' : u' c ≠ 0) (hc : c ≠ 0)
    (hd : HasDerivAt u' u''c c) (heuler : u' c = 1 / (1 + ρ) * (1 + r) * u' (c + dc)) :
    -(u''c * c / u' c) * (dc / c) =
        (r - ρ) / (1 + r) + (u' (c + dc) - u' c - u''c * dc) / u' c ∧
      (fun x => u' (c + x) - u' c - u''c * x) =o[𝓝 0] fun x => x := by
  refine ⟨?_, ?_⟩
  · have key : u' (c + dc) = (1 + ρ) / (1 + r) * u' c := by
      field_simp at heuler ⊢
      linarith
    rw [key]
    field_simp
    ring
  · have h := hd.isLittleO
    have hc' : Tendsto (fun x : ℝ => c + x) (𝓝 0) (𝓝 c) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_add c
    have := h.comp_tendsto hc'
    refine this.congr (fun x => ?_) (fun x => ?_)
    · simp [smul_eq_mul, mul_comm]
    · simp

end AKMM.ContinuousTime
