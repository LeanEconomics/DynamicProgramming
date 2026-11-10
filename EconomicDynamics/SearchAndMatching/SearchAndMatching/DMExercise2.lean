/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SearchAndMatching.DMMatching
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination

/-!
# Exercise 18.2: the planner's problem with endogenous job destruction

Miao, §18.4, Exercise 18.2, p. 614: "Following a similar analysis in Section 18.1, derive the
social planner's problem for the model in Section 18.2. Study efficiency properties of the
decentralized search equilibrium."

**Formulation.** In the model of §18.2 (Mortensen–Pissarides), let `E_t` be the measure of
matches at the start of period `t` (before the idiosyncratic draw `z ~ G`). The planner chooses
the reservation productivity `z_t` and vacancies `v_t`; matches with `z ≤ z_t` separate, so
employment is `N_t = P(z_t)E_t`, `P = 1 − G`, and `u_t = 1 − N_t`. Output is `AE_tH(z_t)`,
`H(z) = ∫_z^∞ x dG(x)`. With the job-finding rate `f(θ) = θq(θ)`, the planner solves
`max Σ βᵗ(AE_tH(z_t) + bu_t − κv_t)` subject to
`E_{t+1} = (1 − ρ^x)P(z_t)E_t + u_tf(v_t/u_t)`. The Lagrangian, with multiplier `β^{t+1}λ_{t+1}`
on the date-`t` constraint, has date-`t` terms `βᵗ · dm_mpLag(…)`.

* `dm_mp_foc_v`, `dm_mp_foc_z`, `dm_mp_foc_E`: the first-order conditions are the partial
  derivatives of `dm_mpLag` in `v`, `z` and `E`.
* `ex_18_2`: in a steady state, with `H′(z) = zP′(z)` (`G` has a density), the planner's
  conditions give the shadow value of a match `λ = A∫_{z*}^∞(z − z*)dG`, the planner's job
  creation condition `κ/q(θ) = β(1 − ξ(θ))A∫_{z*}^∞(z − z*)dG` and job destruction condition
  `ξθκ = (1 − ξ)(Az* − b) + β(1 − ρ^x)(1 − ξ)A∫_{z*}^∞(z − z*)dG`: the decentralised (18.44),
  (18.45) with `η` replaced by `ξ(θ)`.
* `ex_18_2_efficiency`: a decentralised steady state `(θ, z*)` satisfying (18.44)–(18.45)
  satisfies the planner's steady-state first-order conditions iff `ξ(θ) = η`: the Hosios
  condition again characterises efficiency.
* `dm_mp_exp_dist`: the exponential distribution `G(z) = 1 − e^{−z}` (mean 1, as in §18.2)
  satisfies the density hypothesis, with `P(z) = e^{−z}`, `H(z) = (z + 1)e^{−z}`.

Departure: `G` enters only through `P` and `H` and the density relation `H′ = zP′`; "efficient"
means "satisfies the planner's steady-state first-order conditions".
-/

namespace Miao.SearchAndMatching

/-- Exercise 18.2: the date-`t` terms of the planner's Lagrangian (divided by `βᵗ`):
`AEH(z) + b(1 − P(z)E) − κv + βλ′((1 − ρ^x)P(z)E + (1 − P(z)E)f(v/(1 − P(z)E))) − λE`. -/
noncomputable def dm_mpLag (f P H : ℝ → ℝ) (A b κ β ρx lam lam' E z v : ℝ) : ℝ :=
  A * E * H z + b * (1 - P z * E) - κ * v +
    β * lam' * ((1 - ρx) * P z * E + (1 - P z * E) * f (v / (1 - P z * E))) - lam * E

/-- Exercise 18.2: the derivative of `y ↦ U(y)f(v/U(y))` is `U′(f(θ) − θf′(θ))`, `θ = v/U`. -/
theorem dm_uf_hasDerivAt {f U : ℝ → ℝ} {v x U' f' : ℝ} (hU : HasDerivAt U U' x)
    (hU0 : U x ≠ 0) (hf : HasDerivAt f f' (v / U x)) :
    HasDerivAt (fun y ↦ U y * f (v / U y)) (U' * (f (v / U x) - v / U x * f')) x := by
  have h2 : HasDerivAt (fun y ↦ v / U y) (-(v * U') / U x ^ 2) x := by
    have := (hU.inv hU0).const_mul v
    refine (this.congr_deriv (by field_simp)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun y ↦ by simp [div_eq_mul_inv]
  have h := hU.mul (hf.comp x h2)
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp
  ring

/-- **Exercise 18.2** (Miao, p. 614): the planner's first-order condition for `v`:
`∂/∂v = −κ + βλ′f′(θ)`. -/
theorem dm_mp_foc_v {f P H : ℝ → ℝ} {A b κ β ρx lam lam' E z v f' : ℝ}
    (hu : 1 - P z * E ≠ 0) (hf : HasDerivAt f f' (v / (1 - P z * E))) :
    HasDerivAt (fun x ↦ dm_mpLag f P H A b κ β ρx lam lam' E z x)
      (-κ + β * lam' * f') v := by
  have hd : HasDerivAt (fun x ↦ x / (1 - P z * E)) (1 / (1 - P z * E)) v :=
    (hasDerivAt_id' v).div_const _
  have h := (((hasDerivAt_id' v).const_mul κ).const_sub (A * E * H z + b * (1 - P z * E))).add
    ((((hf.comp v hd).const_mul (1 - P z * E)).const_add ((1 - ρx) * P z * E)).const_mul
      (β * lam')) |>.sub_const (lam * E)
  refine h.congr_deriv ?_
  field_simp

/-- **Exercise 18.2** (Miao, p. 614): the planner's first-order condition for the reservation
productivity `z`: `∂/∂z = AEH′(z) − bP′(z)E + βλ′((1 − ρ^x)P′(z)E − P′(z)E(f(θ) − θf′(θ)))`. -/
theorem dm_mp_foc_z {f P H : ℝ → ℝ} {A b κ β ρx lam lam' E z v f' P' H' : ℝ}
    (hP : HasDerivAt P P' z) (hH : HasDerivAt H H' z) (hu : 1 - P z * E ≠ 0)
    (hf : HasDerivAt f f' (v / (1 - P z * E))) :
    HasDerivAt (fun y ↦ dm_mpLag f P H A b κ β ρx lam lam' E y v)
      (A * E * H' - b * (P' * E) + β * lam' * ((1 - ρx) * P' * E -
        P' * E * (f (v / (1 - P z * E)) - v / (1 - P z * E) * f'))) z := by
  have hU : HasDerivAt (fun y ↦ 1 - P y * E) (-(P' * E)) z := by
    simpa using (hP.mul_const E).const_sub 1
  have hg := dm_uf_hasDerivAt hU hu hf
  have h := ((((hH.const_mul (A * E)).add (hU.const_mul b)).sub_const (κ * v)).add
    ((((hP.const_mul (1 - ρx)).mul_const E).add hg).const_mul (β * lam'))).sub_const (lam * E)
  refine h.congr_deriv ?_
  ring

/-- **Exercise 18.2** (Miao, p. 614): the planner's first-order condition for the stock of matches
`E`: `∂/∂E = AH(z) − bP(z) + βλ′((1 − ρ^x)P(z) − P(z)(f(θ) − θf′(θ))) − λ`. -/
theorem dm_mp_foc_E {f P H : ℝ → ℝ} {A b κ β ρx lam lam' E z v f' : ℝ}
    (hu : 1 - P z * E ≠ 0) (hf : HasDerivAt f f' (v / (1 - P z * E))) :
    HasDerivAt (fun e ↦ dm_mpLag f P H A b κ β ρx lam lam' e z v)
      (A * H z - b * P z + β * lam' * ((1 - ρx) * P z -
        P z * (f (v / (1 - P z * E)) - v / (1 - P z * E) * f')) - lam) E := by
  have hU : HasDerivAt (fun e ↦ 1 - P z * e) (-P z) E := by
    simpa using ((hasDerivAt_id' E).const_mul (P z)).const_sub 1
  have hg := dm_uf_hasDerivAt hU hu hf
  have hid := hasDerivAt_id' E
  have h := (((((hid.const_mul A).mul_const (H z)).add (hU.const_mul b)).sub_const (κ * v)).add
    (((hid.const_mul ((1 - ρx) * P z)).add hg).const_mul (β * lam'))).sub
      (hid.const_mul lam)
  refine h.congr_deriv ?_
  ring

/-- **Exercise 18.2** (Miao, p. 614): **the planner's steady state**. Let `θ = v/u`, with
`f(θ) = θq` and `f′(θ) = q(1 − ξ)` (`q = q(θ) > 0`, `ξ = ξ(θ) < 1`), `H′(z) = zP′(z)` with
`P′(z) ≠ 0`, `E ≠ 0`, and let the three first-order conditions hold with `λ′ = λ`. Then
`λ = A(H(z) − zP(z)) = A∫_z^∞(x − z)dG`, `κ/q = β(1 − ξ)A(H − zP)` (planner's job creation) and
`ξθκ = (1 − ξ)(Az − b) + β(1 − ρ^x)(1 − ξ)A(H − zP)` (planner's job destruction). -/
theorem ex_18_2 {A b κ β ρx lam E z θ q ξ Pz Hz P' : ℝ} (hq : 0 < q)
    (hξ : ξ < 1) (hP' : P' ≠ 0) (hE : E ≠ 0)
    (hv : -κ + β * lam * (q * (1 - ξ)) = 0)
    (hz : A * E * (z * P') - b * (P' * E) + β * lam * ((1 - ρx) * P' * E -
      P' * E * (θ * q - θ * (q * (1 - ξ)))) = 0)
    (hE' : A * Hz - b * Pz + β * lam * ((1 - ρx) * Pz -
      Pz * (θ * q - θ * (q * (1 - ξ)))) - lam = 0) :
    lam = A * (Hz - z * Pz) ∧ κ / q = β * (1 - ξ) * (A * (Hz - z * Pz)) ∧
      ξ * θ * κ = (1 - ξ) * (A * z - b) + β * (1 - ρx) * (1 - ξ) * (A * (Hz - z * Pz)) := by
  have hz' : A * z - b + β * lam * ((1 - ρx) - θ * q * ξ) = 0 := by
    have key : (P' * E) * (A * z - b + β * lam * ((1 - ρx) - θ * q * ξ)) = 0 := by
      linear_combination hz
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (mul_ne_zero hP' hE)
    · exact h
  have hlam : lam = A * (Hz - z * Pz) := by linear_combination (-1 : ℝ) * hE' + Pz * hz'
  have h1 : 0 < 1 - ξ := by linarith
  refine ⟨hlam, ?_, ?_⟩
  · rw [← hlam, div_eq_iff hq.ne']
    linear_combination (-1 : ℝ) * hv
  · rw [← hlam]
    linear_combination (-(1 - ξ)) * hz' + (-(ξ * θ)) * hv

/-- **Exercise 18.2** (Miao, p. 614): **efficiency**. Let the decentralised steady state
`(θ, z*)` satisfy the job creation condition (18.44) `κ/q(θ) = β(1 − η)A∫_{z*}^∞(z − z*)dG` and
the job destruction condition (18.45)
`ηθκ = (1 − η)(Az* − b) + β(1 − ρ^x)(1 − η)A∫_{z*}^∞(z − z*)dG`, with `A∫(z − z*)dG > 0`.
Then it satisfies the planner's steady-state first-order conditions (for some multiplier `λ`)
iff `ξ(θ) = η` (the Hosios condition). -/
theorem ex_18_2_efficiency {A b κ β ρx η E z θ q ξ Pz Hz P' : ℝ} (hβ : 0 < β) (hq : 0 < q)
    (hη1 : η < 1) (hP' : P' ≠ 0) (hE : E ≠ 0) (hI : 0 < A * (Hz - z * Pz))
    (h44 : κ / q = β * (1 - η) * (A * (Hz - z * Pz)))
    (h45 : η * θ * κ = (1 - η) * (A * z - b) + β * (1 - ρx) * (1 - η) * (A * (Hz - z * Pz))) :
    (∃ lam : ℝ, -κ + β * lam * (q * (1 - ξ)) = 0 ∧
      A * E * (z * P') - b * (P' * E) + β * lam * ((1 - ρx) * P' * E -
        P' * E * (θ * q - θ * (q * (1 - ξ)))) = 0 ∧
      A * Hz - b * Pz + β * lam * ((1 - ρx) * Pz -
        Pz * (θ * q - θ * (q * (1 - ξ)))) - lam = 0) ↔ ξ = η := by
  set I := A * (Hz - z * Pz) with hIdef
  have hκ : κ = β * (1 - η) * I * q := by
    rw [div_eq_iff hq.ne'] at h44; exact h44
  constructor
  · rintro ⟨lam, hv, hz, hE'⟩
    have key : (P' * E) * (A * z - b + β * lam * ((1 - ρx) - θ * q * ξ)) = 0 := by
      linear_combination hz
    have hz' := (mul_eq_zero.mp key).resolve_left (mul_ne_zero hP' hE)
    have hlam : lam = I := by
      rw [hIdef]
      linear_combination (-1 : ℝ) * hE' + Pz * hz'
    rw [hlam, hκ] at hv
    have key2 : β * I * q * (ξ - η) = 0 := by linear_combination (-1 : ℝ) * hv
    have hne : β * I * q ≠ 0 := by positivity
    have := (mul_eq_zero.mp key2).resolve_left hne
    linarith
  · rintro rfl
    have hX : (1 - ξ) * (A * z - b + β * (1 - ρx) * I - β * I * θ * q * ξ) = 0 := by
      linear_combination (-1 : ℝ) * h45 + ξ * θ * hκ
    have hX' := (mul_eq_zero.mp hX).resolve_left (by linarith)
    refine ⟨I, ?_, ?_, ?_⟩
    · rw [hκ]; ring
    · linear_combination (P' * E) * hX'
    · rw [hIdef]
      rw [hIdef] at hX'
      linear_combination Pz * hX'

/-- Exercise 18.2: the exponential distribution `G(z) = 1 − e^{−z}` (mean 1) satisfies the
density hypothesis `H′(z) = zP′(z)` with `P(z) = e^{−z}` and `H(z) = ∫_z^∞ x dG = (z + 1)e^{−z}`;
`P(0) = 1` and the mean is `H(0) = 1`. -/
theorem dm_mp_exp_dist (z : ℝ) :
    HasDerivAt (fun x ↦ Real.exp (-x)) (-Real.exp (-z)) z ∧
      HasDerivAt (fun x ↦ (x + 1) * Real.exp (-x)) (z * -Real.exp (-z)) z ∧
      Real.exp (-0) = 1 ∧ (0 + 1) * Real.exp (-0) = 1 := by
  have hP : HasDerivAt (fun x ↦ Real.exp (-x)) (-Real.exp (-z)) z := by
    exact ((hasDerivAt_id' z).neg.exp).congr_deriv (by simp)
  refine ⟨hP, ?_, by simp, by simp⟩
  have h := ((hasDerivAt_id' z).add_const 1).mul hP
  refine h.congr_deriv ?_
  ring

end Miao.SearchAndMatching
