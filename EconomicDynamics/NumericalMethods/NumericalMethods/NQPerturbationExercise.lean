/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NumericalMethods.NQPerturbation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Hansen–Heaton–Li example in closed form (Miao, §11.4, pp. 367–369; Exercise 11.2)

Miao, §11.4: aggregate consumption `ln(C_{t+1}/C_t) = μ_c + x_t + σ_c ε_{c,t+1}`,
`x_{t+1} = φ x_t + σ_x ε_{x,t+1}` with independent standard normal shocks (`nqShock`, the law
of `(ε_c, ε_x)`). We compute the unit-EIS solution (11.6) and complete the first-order
perturbation (Exercise 11.2).

* `nq_gauss_exp_integral`, `nq_shock_exp`: the normal moment generating function.
* `eq_11_6_mgf`: `ln E_t exp[(1 − γ)(v_{t+1} + c_{t+1} − c_t)]` for the guess `v = A x + μ_v`
  (the displayed computation on p. 368).
* `eq_11_6`: the guess (11.6) solves (11.5) for all `x` iff `A = β/(1 − βφ)` and
  `μ_v = β/(1 − β) [μ_c + (1 − γ)/2 ((βσ_x/(1 − βφ))² + σ_c²)]`.
* `nq_gauss_tilt`, `nq_gauss_quad`, `nq_ex_11_2_tilt`: under the tilted measure `Ẽ_t` (density
  `e^{(1−γ)(v_{t+1}(1) + Δc)}/E_t[·]`, `nqTilt`), `ε_x` has mean `(1 − γ) A σ_x`, and the tilted
  expectation of a quadratic `−A_d x'²/2 + B_d x' + μ_d` in `x' = φx + σ_x ε_x` is
  `−A_d((φx + κ)² + σ_x²)/2 + B_d(φx + κ) + μ_d`, `κ = (1 − γ) A σ_x²`.
* `nq_ex_11_2_Q`, `nq_ex_11_2_a`, `nq_ex_11_2_b`: `Q_t(v_{t+1}(1) + Δc) = a x + b`,
  `a = Aφ + 1 = 1/(1 − βφ)`, `b = μ_v/β`.
* `nq_ex_11_2_match` and **`ex_11_2`** (Exercise 11.2): the conjecture
  `v_t'(1) = −A_d x_t²/2 + B_d x_t + μ_d` solves (11.7) for all `x_t` iff
  `A_d = β(1 − β)/((1 − βφ)²(1 − βφ²))`,
  `B_d = −β[(1 − β)μ_v/(β(1 − βφ)) + A_d φ κ]/(1 − βφ)`,
  `μ_d = [−β(1 − β)(μ_v/β)²/2 − βA_d(κ² + σ_x²)/2 + βB_d κ]/(1 − β)`,
  `κ = (1 − γ)βσ_x²/(1 − βφ)`.

**Departures and corrections.** The book uses `ρ` both for the EIS parameter of (11.3) and for
the autocorrelation of `x_t`; we write `φ` for the latter (so the book's `A = β/(1 − βρ)` is
`β/(1 − βφ)`). The book's "`A` and `μ_c` are constants to be determined" should read `μ_v`.
-/

namespace Miao.NumericalMethods

open MeasureTheory Real ProbabilityTheory

/-- Miao, p. 367: the law of the next-period shocks `(ε_c, ε_x)`, independent standard
normals. -/
noncomputable abbrev nqShock : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- The standard normal moment generating function: `E e^{bε} = e^{b²/2}`. -/
theorem nq_gauss_exp_integral (b : ℝ) :
    ∫ e, Real.exp (b * e) ∂(gaussianReal 0 1) = Real.exp (b ^ 2 / 2) := by
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) b
  simp only [mgf, id] at h
  rw [h]
  congr 1
  simp

/-- `E exp(a + b ε_c + c ε_x) = exp(a + (b² + c²)/2)`. -/
theorem nq_shock_exp (a b c : ℝ) :
    ∫ e, Real.exp (a + b * e.1 + c * e.2) ∂nqShock = Real.exp (a + (b ^ 2 + c ^ 2) / 2) := by
  have hfun : (fun e : ℝ × ℝ => Real.exp (a + b * e.1 + c * e.2)) =
      fun e => Real.exp a * (Real.exp (b * e.1) * Real.exp (c * e.2)) := by
    funext e; rw [Real.exp_add, Real.exp_add]; ring
  rw [hfun, integral_const_mul,
    integral_prod_mul (fun x => Real.exp (b * x)) (fun y => Real.exp (c * y)),
    nq_gauss_exp_integral, nq_gauss_exp_integral, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

/-- Miao, p. 368 (the displayed computation): for the guess `v = A x + μ_v`,
`ln E_t exp[(1 − γ)(v_{t+1} + c_{t+1} − c_t)]
  = (1 − γ)[(Aφ + 1)x_t + μ_v + μ_c] + (1 − γ)²/2 [(Aσ_x)² + σ_c²]`,
with `x_{t+1} = φ x_t + σ_x ε_x` and `c_{t+1} − c_t = μ_c + x_t + σ_c ε_c`. -/
theorem eq_11_6_mgf (γ A μv μc σc σx φ x : ℝ) :
    Real.log (∫ e, Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))
      ∂nqShock) =
      (1 - γ) * ((A * φ + 1) * x + μv + μc) + (1 - γ) ^ 2 / 2 * ((A * σx) ^ 2 + σc ^ 2) := by
  have hfun : (fun e : ℝ × ℝ =>
      Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))) =
      fun e => Real.exp ((1 - γ) * ((A * φ + 1) * x + μv + μc) + ((1 - γ) * σc) * e.1 +
        ((1 - γ) * A * σx) * e.2) := by
    funext e; congr 1; ring
  rw [hfun, nq_shock_exp, Real.log_exp]
  ring

/-- Miao, (11.6), p. 368: the guess `v_t = A x_t + μ_v` solves the unit-EIS equation (11.5)
`v_t = β/(1 − γ) ln E_t exp[(1 − γ)(v_{t+1} + c_{t+1} − c_t)]` for every `x_t` iff
`A = β/(1 − βφ)` and `μ_v = β/(1 − β) [μ_c + (1 − γ)/2 ((βσ_x/(1 − βφ))² + σ_c²)]`. -/
theorem eq_11_6 {β γ φ : ℝ} (hβ : β ≠ 1) (hγ : γ ≠ 1) (hβφ : β * φ ≠ 1) (μc σc σx A μv : ℝ) :
    (∀ x, A * x + μv = β / (1 - γ) * Real.log (∫ e, Real.exp ((1 - γ) *
      (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)) ∂nqShock)) ↔
    A = β / (1 - β * φ) ∧
      μv = β / (1 - β) * (μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2)) := by
  have hγ' : 1 - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hβ' : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  have hR : ∀ x, β / (1 - γ) * Real.log (∫ e, Real.exp ((1 - γ) *
      (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)) ∂nqShock) =
      β * ((A * φ + 1) * x + μv + μc) + β * (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2) := by
    intro x
    rw [eq_11_6_mgf]
    field_simp
  simp_rw [hR]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hA : A * (1 - β * φ) = β := by linarith
    have hA' : A = β / (1 - β * φ) := by rw [eq_div_iff hβφ']; exact hA
    refine ⟨hA', ?_⟩
    have hm : μv * (1 - β) = β * (μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2)) := by linarith
    rw [← eq_div_iff hβ'] at hm
    rw [hm, hA']
    field_simp
  · rintro ⟨hA, hμ⟩ x
    have hA1 : A * (1 - β * φ) = β := by rw [hA]; field_simp
    have hσ : (β * σx / (1 - β * φ)) = A * σx := by rw [hA]; ring
    rw [hσ] at hμ
    have hμ1 : μv * (1 - β) = β * (μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2)) := by
      rw [hμ]; field_simp
    linear_combination x * hA1 + hμ1

/-- Exponential tilting of the standard normal:
`E[f(ε) e^{kε}] = e^{k²/2} E_{N(k,1)}[f]`. -/
theorem nq_gauss_tilt (k : ℝ) (f : ℝ → ℝ) :
    ∫ e, f e * Real.exp (k * e) ∂(gaussianReal 0 1) =
      Real.exp (k ^ 2 / 2) * ∫ e, f e ∂(gaussianReal k 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  congr 1
  funext e
  simp only [gaussianPDFReal_def, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
  have : Real.exp (-e ^ 2 / 2) * Real.exp (k * e) =
      Real.exp (k ^ 2 / 2) * Real.exp (-(e - k) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  linear_combination ((√(2 * π))⁻¹ * f e) * this

/-- Quadratic moments of `N(m, 1)`: `E[a y² + b y + c] = a(1 + m²) + b m + c`. -/
theorem nq_gauss_quad (m a b c : ℝ) :
    ∫ y, (a * y ^ 2 + b * y + c) ∂(gaussianReal m 1) = a * (1 + m ^ 2) + b * m + c := by
  have hI2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal m 1) := by
    simpa using (memLp_id_gaussianReal (μ := m) (v := 1) 2).integrable_sq
  have hI1 : Integrable (fun y : ℝ => y) (gaussianReal m 1) := by
    have := MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := m) (v := 1) 1)
    exact this
  have hvar := variance_id_gaussianReal (μ := m) (v := 1)
  rw [variance_eq_sub (memLp_id_gaussianReal 2)] at hvar
  simp only [Pi.pow_apply, id] at hvar
  rw [integral_id_gaussianReal] at hvar
  have h2 : ∫ y, y ^ 2 ∂(gaussianReal m 1) = 1 + m ^ 2 := by
    simp only [NNReal.coe_one] at hvar; linarith
  have e1 : ∫ y, (a * y ^ 2 + b * y + c) ∂(gaussianReal m 1) =
      ∫ y, (a * y ^ 2 + b * y) ∂(gaussianReal m 1) + ∫ _, c ∂(gaussianReal m 1) :=
    integral_add ((hI2.const_mul a).add (hI1.const_mul b)) (integrable_const c)
  have e2 : ∫ y, (a * y ^ 2 + b * y) ∂(gaussianReal m 1) =
      ∫ y, a * y ^ 2 ∂(gaussianReal m 1) + ∫ y, b * y ∂(gaussianReal m 1) :=
    integral_add (hI2.const_mul a) (hI1.const_mul b)
  rw [e1, e2, integral_const_mul, integral_const_mul, h2, integral_id_gaussianReal,
    integral_const]
  simp

/-- Miao, p. 369: the tilted expectation `Ẽ_t[G] = E_t[G e^{c Y}]/E_t[e^{c Y}]`, `c = 1 − γ`,
`Y = v_{t+1}(1) + c_{t+1} − c_t` (the density `V_{t+1}(1)^{1−γ}/E_t V_{t+1}(1)^{1−γ}`). -/
noncomputable def nqTilt (c : ℝ) (Y G : ℝ × ℝ → ℝ) : ℝ :=
  (∫ e, G e * Real.exp (c * Y e) ∂nqShock) / ∫ e, Real.exp (c * Y e) ∂nqShock

/-- Miao, p. 369 (Exercise 11.2, the tilted expectation): with `Y = v_{t+1}(1) + Δc`
for `v(1) = A x + μ_v`, the tilted expectation of `−A_d x'²/2 + B_d x' + μ_d`,
`x' = φx + σ_x ε_x`, is `−A_d((φx + κ)² + σ_x²)/2 + B_d(φx + κ) + μ_d`,
`κ = (1 − γ) A σ_x²` (under `Ẽ_t`, `ε_x ~ N((1 − γ)Aσ_x, 1)`). -/
theorem nq_ex_11_2_tilt (γ A μv μc σc σx φ x Ad Bd μd : ℝ) :
    nqTilt (1 - γ) (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)
      (fun e => -Ad / 2 * (φ * x + σx * e.2) ^ 2 + Bd * (φ * x + σx * e.2) + μd) =
      -Ad / 2 * ((φ * x + (1 - γ) * A * σx ^ 2) ^ 2 + σx ^ 2) +
        Bd * (φ * x + (1 - γ) * A * σx ^ 2) + μd := by
  set a0 : ℝ := (1 - γ) * ((A * φ + 1) * x + μv + μc)
  set b : ℝ := (1 - γ) * σc
  set k : ℝ := (1 - γ) * A * σx
  have hY : ∀ e : ℝ × ℝ, (1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1) =
      a0 + b * e.1 + k * e.2 := fun e => by simp only [a0, b, k]; ring
  set G' : ℝ → ℝ := fun t => -Ad / 2 * (φ * x + σx * t) ^ 2 + Bd * (φ * x + σx * t) + μd
  have hnum : (fun e : ℝ × ℝ => (-Ad / 2 * (φ * x + σx * e.2) ^ 2 + Bd * (φ * x + σx * e.2) + μd)
      * Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))) =
      fun e => (Real.exp a0 * Real.exp (b * e.1)) * (G' e.2 * Real.exp (k * e.2)) := by
    funext e; rw [hY, Real.exp_add, Real.exp_add]; simp only [G']; ring
  have hden : (fun e : ℝ × ℝ =>
      Real.exp ((1 - γ) * (A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1))) =
      fun e => (Real.exp a0 * Real.exp (b * e.1)) * Real.exp (k * e.2) := by
    funext e; rw [hY, Real.exp_add, Real.exp_add]
  unfold nqTilt
  rw [hnum, hden,
    integral_prod_mul (fun s => Real.exp a0 * Real.exp (b * s)) (fun t => G' t * Real.exp (k * t)),
    integral_prod_mul (fun s => Real.exp a0 * Real.exp (b * s)) (fun t => Real.exp (k * t)),
    nq_gauss_tilt k G', nq_gauss_exp_integral k]
  have hG' : ∀ t, G' t = (-Ad / 2 * σx ^ 2) * t ^ 2 + (-Ad * φ * x * σx + Bd * σx) * t +
      (-Ad / 2 * (φ * x) ^ 2 + Bd * φ * x + μd) := fun t => by simp only [G']; ring
  have hM : ∫ t, G' t ∂(gaussianReal k 1) = (-Ad / 2 * σx ^ 2) * (1 + k ^ 2) +
      (-Ad * φ * x * σx + Bd * σx) * k + (-Ad / 2 * (φ * x) ^ 2 + Bd * φ * x + μd) := by
    simp_rw [hG']
    exact nq_gauss_quad k _ _ _
  rw [hM]
  have hE1 : 0 < ∫ s, Real.exp a0 * Real.exp (b * s) ∂(gaussianReal 0 1) := by
    rw [integral_const_mul, nq_gauss_exp_integral]; positivity
  have hE2 : 0 < Real.exp (k ^ 2 / 2) := Real.exp_pos _
  rw [mul_div_mul_left _ _ hE1.ne', mul_div_cancel_left₀ _ hE2.ne']
  simp only [k]
  ring

/-- Miao, p. 369 (Exercise 11.2): at `ρ = 1`, `Q_t(v_{t+1}(1) + c_{t+1} − c_t) = a x_t + b` with
`a = Aφ + 1`, `b = μ_v + μ_c + (1 − γ)/2((Aσ_x)² + σ_c²)`. -/
theorem nq_ex_11_2_Q {γ : ℝ} (hγ : γ ≠ 1) (A μv μc σc σx φ x : ℝ) :
    nqQ nqShock γ (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1) =
      (A * φ + 1) * x + (μv + μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2)) := by
  have hγ' : 1 - γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  rw [nqQ, eq_11_6_mgf]
  field_simp
  ring

/-- Miao, p. 368: with `A = β/(1 − βφ)`, `a = Aφ + 1 = 1/(1 − βφ)` (so `A = β a`). -/
theorem nq_ex_11_2_a {β φ A : ℝ} (hβφ : β * φ ≠ 1) (hA : A = β / (1 - β * φ)) :
    A * φ + 1 = 1 / (1 - β * φ) := by
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  rw [hA]; field_simp; ring

/-- Miao, p. 368: with `μ_v` from (11.6), `b = μ_v + μ_c + (1 − γ)/2((Aσ_x)² + σ_c²) = μ_v/β`. -/
theorem nq_ex_11_2_b {β γ φ A μv μc σc σx : ℝ} (hβ0 : β ≠ 0) (hβ : β ≠ 1)
    (hA : A = β / (1 - β * φ))
    (hμv : μv = β / (1 - β) * (μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2))) :
    μv + μc + (1 - γ) / 2 * ((A * σx) ^ 2 + σc ^ 2) = μv / β := by
  have hβ' : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hσ : A * σx = β * σx / (1 - β * φ) := by rw [hA]; ring
  rw [hσ]
  set K : ℝ := μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2)
  have hK : μv + μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2) = μv + K := by
    simp only [K]; ring
  rw [hK, hμv]
  field_simp
  ring

/-- Miao, (11.7), p. 369 (Exercise 11.2, matching coefficients): for constants `a, b, κ`, the
quadratic `−A_d x²/2 + B_d x + μ_d` satisfies
`−A_d x²/2 + B_d x + μ_d = −β(1 − β)/2 (a x + b)² + β[−A_d((φx + κ)² + σ_x²)/2 + B_d(φx + κ) + μ_d]`
for every `x` iff `A_d = β(1 − β)a²/(1 − βφ²)`, `B_d = −β((1 − β)ab + A_d φ κ)/(1 − βφ)` and
`μ_d = (−β(1 − β)b²/2 − βA_d(κ² + σ_x²)/2 + βB_d κ)/(1 − β)`. -/
theorem nq_ex_11_2_match {β φ a b κ σx Ad Bd μd : ℝ} (hβ : β ≠ 1) (hβφ : β * φ ≠ 1)
    (hβφ2 : β * φ ^ 2 ≠ 1) :
    (∀ x, -Ad / 2 * x ^ 2 + Bd * x + μd = -(β * (1 - β)) / 2 * (a * x + b) ^ 2 +
      β * (-Ad / 2 * ((φ * x + κ) ^ 2 + σx ^ 2) + Bd * (φ * x + κ) + μd)) ↔
    Ad = β * (1 - β) * a ^ 2 / (1 - β * φ ^ 2) ∧
      Bd = -β * ((1 - β) * a * b + Ad * φ * κ) / (1 - β * φ) ∧
      μd = (-β * (1 - β) * b ^ 2 / 2 - β * Ad * (κ ^ 2 + σx ^ 2) / 2 + β * Bd * κ) / (1 - β) := by
  have hβ' : 1 - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  have hβφ2' : 1 - β * φ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ2)
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have hm := h (-1)
    have eA : Ad * (1 - β * φ ^ 2) = β * (1 - β) * a ^ 2 := by
      linear_combination (-1 : ℝ) * h1 + (-1 : ℝ) * hm + 2 * h0
    have eB : Bd * (1 - β * φ) = -β * ((1 - β) * a * b + Ad * φ * κ) := by
      linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * hm
    have eM : μd * (1 - β) =
        -β * (1 - β) * b ^ 2 / 2 - β * Ad * (κ ^ 2 + σx ^ 2) / 2 + β * Bd * κ := by
      linear_combination h0
    refine ⟨?_, ?_, ?_⟩
    · rw [eq_div_iff hβφ2']; exact eA
    · rw [eq_div_iff hβφ']; exact eB
    · rw [eq_div_iff hβ']; exact eM
  · rintro ⟨hA, hB, hM⟩ x
    have eA : Ad * (1 - β * φ ^ 2) = β * (1 - β) * a ^ 2 := by
      rw [hA]; field_simp
    have eB : Bd * (1 - β * φ) = -β * ((1 - β) * a * b + Ad * φ * κ) := by
      rw [hB]; field_simp
    have eM : μd * (1 - β) =
        -β * (1 - β) * b ^ 2 / 2 - β * Ad * (κ ^ 2 + σx ^ 2) / 2 + β * Bd * κ := by
      rw [hM]; field_simp
    linear_combination (-(x ^ 2) / 2) * eA + x * eB + eM

/-- **Exercise 11.2** (Miao, p. 383): completing the solution of §11.4. With the unit-EIS
solution (11.6) (`A = β/(1 − βφ)`, `μ_v` as in `eq_11_6`), the conjecture
`v_t'(1) = −A_d x_t²/2 + B_d x_t + μ_d` solves (11.7),
`v_t'(1) = −β(1 − β)/2 [Q_t(v_{t+1}(1) + Δc)]² + β Ẽ_t v_{t+1}'(1)`, for every `x_t` iff
`A_d = β(1 − β)/((1 − βφ)²(1 − βφ²))`,
`B_d = −β[(1 − β)(1/(1 − βφ))(μ_v/β) + A_d φ κ]/(1 − βφ)`,
`μ_d = [−β(1 − β)(μ_v/β)²/2 − βA_d(κ² + σ_x²)/2 + βB_d κ]/(1 − β)`, with
`κ = (1 − γ)βσ_x²/(1 − βφ)`. The first-order approximation is then
`v_t(ρ) ≃ A x_t + μ_v + (ρ − 1)(−A_d x_t²/2 + B_d x_t + μ_d)`. -/
theorem ex_11_2 {β γ φ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ : γ ≠ 1) (hβφ : β * φ ≠ 1)
    (hβφ2 : β * φ ^ 2 ≠ 1) {A μv : ℝ} (μc σc σx Ad Bd μd : ℝ) (hA : A = β / (1 - β * φ))
    (hμv : μv = β / (1 - β) * (μc + (1 - γ) / 2 * ((β * σx / (1 - β * φ)) ^ 2 + σc ^ 2))) :
    (∀ x, -Ad / 2 * x ^ 2 + Bd * x + μd =
      -(β * (1 - β)) / 2 *
          (nqQ nqShock γ (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)) ^ 2 +
        β * nqTilt (1 - γ) (fun e => A * (φ * x + σx * e.2) + μv + μc + x + σc * e.1)
          (fun e => -Ad / 2 * (φ * x + σx * e.2) ^ 2 + Bd * (φ * x + σx * e.2) + μd)) ↔
    Ad = β * (1 - β) / ((1 - β * φ) ^ 2 * (1 - β * φ ^ 2)) ∧
      Bd = -β * ((1 - β) * (1 / (1 - β * φ)) * (μv / β) +
        Ad * φ * ((1 - γ) * β * σx ^ 2 / (1 - β * φ))) / (1 - β * φ) ∧
      μd = (-β * (1 - β) * (μv / β) ^ 2 / 2 -
        β * Ad * (((1 - γ) * β * σx ^ 2 / (1 - β * φ)) ^ 2 + σx ^ 2) / 2 +
          β * Bd * ((1 - γ) * β * σx ^ 2 / (1 - β * φ))) / (1 - β) := by
  have hβφ' : 1 - β * φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβφ)
  have ha := nq_ex_11_2_a hβφ hA
  have hb := nq_ex_11_2_b hβ0.ne' hβ1.ne hA hμv
  have hκ : (1 - γ) * A * σx ^ 2 = (1 - γ) * β * σx ^ 2 / (1 - β * φ) := by
    rw [hA]; ring
  simp_rw [nq_ex_11_2_Q hγ, nq_ex_11_2_tilt, ha, hb, hκ]
  rw [nq_ex_11_2_match hβ1.ne hβφ hβφ2]
  have hAd : β * (1 - β) * (1 / (1 - β * φ)) ^ 2 / (1 - β * φ ^ 2) =
      β * (1 - β) / ((1 - β * φ) ^ 2 * (1 - β * φ ^ 2)) := by
    field_simp
  rw [hAd]

end Miao.NumericalMethods
