/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFrictionalLaborMarkets.SteadyState
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The log-linearised solution and rigid wages

AKMM, §20.6.1, pp. 607–608, §20.6.4, p. 611, and 20.A.4, pp. 881–882. With Cobb–Douglas
matching (20.23), `θ_t = θ̄e^{θ̂_t}`, `z_t = z̄e^{ẑ_t}`, the job-creation equation (20.16) reads
`llL(θ̂_t) = E[llR(ẑ_{t+1}, θ̂_{t+1})]` (`ll_lhs_eq`, `ll_rhs_eq`), and its log-linearisation is
`Aθ̂_t = E[z̄ẑ_{t+1} + Bθ̂_{t+1}]` (20.25). The coefficients are stated as exact derivatives at the
steady state.

* `eq_20_25`: `A = κθ̄^ηη/((1 − γ)βχ)`, `∂llR/∂ẑ = z̄` and
  `B = (1 − σ)κθ̄^ηη/((1 − γ)χ) − γκθ̄/(1 − γ)`; the printed `+γκθ̄/(1 − γ)` is wrong
  (`eq_20_25_misprint`).
* `ll_undetermined`: the guess `θ̂ = Cẑ` with `E[ẑ_{t+1}] = ρẑ_t` solves (20.25) iff
  `C = ρz̄/(A − ρB)`; `eq_20_26`: with `z̄ = 1` this is
  `(1 − γ)[κθ̄^ηη/χ(1/(ρβ) − (1 − σ)) + κγθ̄]^{−1}`; the printed `B` would give `−κγθ̄`
  (`eq_20_26_printed_B`).
* Comparative statics of the coefficient `llCoeff` (p. 608), for given `θ̄`: it is larger for a
  smaller `κ`, `γ` or `σ` and a larger `χ`, `ρ` or `β` (`ll_cs_kappa` … `ll_cs_sigma`); for a
  smaller `η` only when `θ̄^ηη` increases in `η`, e.g. `θ̄ ≥ 1` (`ll_cs_eta`); with `θ̄ = e^{−4}`
  it fails (`ll_cs_eta_counterexample`).
* `eq_20_A_4_example`: the worked example of 20.A.4 (capital accumulation) as derivatives.
* Rigid wages (§20.6.4): `eq_20_27_deriv`, `eq_20_27`: `θ̂ = [κθ̄^ηη/χ(1/(ρβ) − (1 − σ))]^{−1}ẑ`,
  and `ll_rigid_gt`: the rigid-wage coefficient exceeds the Nash coefficient for `γ ∈ (0, 1)`.

Departures: the book writes `E[z_{t+1}] = ρz_t` for `E[ẑ_{t+1}] = ρẑ_t`; the comparative statics
in `η` need `θ̄^ηη` increasing in `η` (true at the calibrated `θ̄ = 1`).
-/

namespace AKMM.FrictionalLaborMarkets

open Real

/-- `(θ̄e^x)^η = θ̄^η e^{ηx}`. -/
theorem ll_rpow_exp {θb η : ℝ} (hθ : 0 < θb) (x : ℝ) :
    (θb * exp x) ^ η = θb ^ η * exp (η * x) := by
  rw [Real.mul_rpow hθ.le (exp_pos x).le, ← Real.exp_mul, mul_comm x η]

/-- The left side of (20.16) divided by `β`, with Cobb–Douglas matching, in logs:
`κ(θ̄e^x)^η/((1 − γ)βχ)`. -/
noncomputable def llL (κ γ β χ η θb x : ℝ) : ℝ := κ * (θb * exp x) ^ η / ((1 - γ) * β * χ)

/-- The bracket on the right of (20.16), with Cobb–Douglas matching, in logs:
`z̄e^{ẑ} − b + (1 − σ)κ(θ̄e^x)^η/((1 − γ)χ) − γκθ̄e^x/(1 − γ)`. -/
noncomputable def llR (zb b σ γ κ χ η θb zh x : ℝ) : ℝ :=
  zb * exp zh - b + (1 - σ) * κ * (θb * exp x) ^ η / ((1 - γ) * χ) -
    γ * κ * (θb * exp x) / (1 - γ)

/-- AKMM, p. 608: with Cobb–Douglas matching (20.23), `llL` is the left side of (20.16) divided
by `β`. -/
theorem ll_lhs_eq {χ η κ γ β θb : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) (hγ1 : γ < 1)
    (hβ : 0 < β) (hθ : 0 < θb) (x : ℝ) :
    llL κ γ β χ η θb x = jcLHS (cdMatch χ η hχ hη0 hη1) κ γ (θb * exp x) / β := by
  have hp : 0 < θb * exp x := mul_pos hθ (exp_pos x)
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [llL, jcLHS, (eq_20_23 hχ hη0 hη1 hp).2, Real.rpow_neg hp.le]
  have : 0 < (θb * exp x) ^ η := by positivity
  field_simp

/-- AKMM, p. 608: with Cobb–Douglas matching (20.23), `llR` is the bracket of (20.16) (using
`λ_w/λ_f = θ`). -/
theorem ll_rhs_eq {χ η κ γ σ b zb θb : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1)
    (hγ1 : γ < 1) (hθ : 0 < θb) (zh x : ℝ) :
    llR zb b σ γ κ χ η θb zh x =
      jcRHS (cdMatch χ η hχ hη0 hη1) (zb * exp zh) b σ γ κ (θb * exp x) := by
  have hp : 0 < θb * exp x := mul_pos hθ (exp_pos x)
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [llR, jcRHS, match_lamW_eq _ hp, (eq_20_23 hχ hη0 hη1 hp).2, Real.rpow_neg hp.le]
  have : 0 < (θb * exp x) ^ η := by positivity
  field_simp
  ring

/-- AKMM, (20.25), p. 608: the log-linearisation coefficients as exact derivatives at the steady
state: `d llL/dθ̂ = A = κθ̄^ηη/((1 − γ)βχ)`, `∂llR/∂ẑ = z̄` and
`∂llR/∂θ̂ = B = (1 − σ)κθ̄^ηη/((1 − γ)χ) − γκθ̄/(1 − γ)`. -/
theorem eq_20_25 {κ γ β χ η θb zb b σ : ℝ} (hθ : 0 < θb) :
    HasDerivAt (llL κ γ β χ η θb) (κ * θb ^ η * η / ((1 - γ) * β * χ)) 0 ∧
    HasDerivAt (fun zh ↦ llR zb b σ γ κ χ η θb zh 0) zb 0 ∧
    HasDerivAt (llR zb b σ γ κ χ η θb 0)
      ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) 0 := by
  have hpow : ∀ x, (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ
  have hE : HasDerivAt (fun x ↦ θb ^ η * exp (η * x)) (θb ^ η * η) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul η).exp.const_mul (θb ^ η)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have h := hE.const_mul κ |>.div_const ((1 - γ) * β * χ)
    have e : llL κ γ β χ η θb = fun x ↦ κ * (θb ^ η * exp (η * x)) / ((1 - γ) * β * χ) := by
      funext x; rw [llL, hpow]
    rw [e]; refine h.congr_deriv ?_; ring
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul zb).sub_const
      (b - (1 - σ) * κ * (θb * exp 0) ^ η / ((1 - γ) * χ) + γ * κ * (θb * exp 0) / (1 - γ))
    simp only [exp_zero, mul_one] at h ⊢
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun zh ↦ ?_)
    simp only [llR, exp_zero, mul_one]; ring
  · have h1 := (hE.const_mul ((1 - σ) * κ)).div_const ((1 - γ) * χ)
    have h2 := (((hasDerivAt_exp (0 : ℝ)).const_mul θb).const_mul (γ * κ)).div_const (1 - γ)
    have h := (h1.sub h2).const_add (zb * exp 0 - b)
    have e : llR zb b σ γ κ χ η θb 0 = fun x ↦ zb * exp 0 - b +
        ((1 - σ) * κ * (θb ^ η * exp (η * x)) / ((1 - γ) * χ) -
          γ * κ * (θb * exp x) / (1 - γ)) := by
      funext x; rw [llR, hpow]; ring
    rw [e]; refine h.congr_deriv ?_
    simp only [exp_zero, mul_one]; ring

/-- AKMM, (20.25), p. 608, as printed: `B` is printed with `+γκθ̄/(1 − γ)`; it exceeds the
derivative of `eq_20_25` by `2γκθ̄/(1 − γ) > 0`. -/
theorem eq_20_25_misprint {κ γ χ η θb σ : ℝ} (hκ : 0 < κ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θb) :
    (1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) + γ * κ * θb / (1 - γ) ≠
      (1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ) := by
  intro h
  have h1 : 0 < 1 - γ := by linarith
  have : 0 < γ * κ * θb / (1 - γ) := by positivity
  linarith

/-- AKMM, p. 608 (method of undetermined coefficients): with `E[ẑ_{t+1}] = ρẑ_t`, the guess
`θ̂_t = Cẑ_t` solves `Aθ̂_t = E[z̄ẑ_{t+1} + Bθ̂_{t+1}]` for every `ẑ_t` iff `C = ρz̄/(A − ρB)`. -/
theorem ll_undetermined {A B C ρ zb : ℝ} (h : A - ρ * B ≠ 0) :
    (∀ zh : ℝ, A * (C * zh) = zb * (ρ * zh) + B * (C * (ρ * zh))) ↔ C = ρ * zb / (A - ρ * B) := by
  rw [eq_div_iff h]
  constructor
  · intro hz; have := hz 1; linarith
  · intro hc zh; linear_combination zh * hc

/-- The coefficient of (20.26), `(1 − γ)[κθ̄^ηη/χ · (1/(ρβ) − (1 − σ)) + κγθ̄]^{−1}`. -/
noncomputable def llCoeff (κ γ η χ ρ β σ θb : ℝ) : ℝ :=
  (1 - γ) / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + κ * γ * θb)

/-- AKMM, (20.26), p. 608: with `z̄ = 1`, `ρz̄/(A − ρB)` for the coefficients of `eq_20_25` is
the coefficient `llCoeff` of (20.26). -/
theorem eq_20_26 {κ γ β χ η θb ρ σ : ℝ} (hγ1 : γ < 1) (hβ : 0 < β) (hχ : 0 < χ) (hρ : 0 < ρ) :
    ρ * 1 / (κ * θb ^ η * η / ((1 - γ) * β * χ) -
      ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ))) =
      llCoeff κ γ η χ ρ β σ θb := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [llCoeff]
  by_cases hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + κ * γ * θb = 0
  · have e : κ * θb ^ η * η / ((1 - γ) * β * χ) -
        ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) =
        ρ / (1 - γ) * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + κ * γ * θb) := by
      field_simp; ring
    rw [e, hD]; simp
  · field_simp
    ring

/-- AKMM, (20.26), p. 608: with the printed sign of `B` the same computation gives
`(1 − γ)[κθ̄^ηη/χ(1/(ρβ) − (1 − σ)) − κγθ̄]^{−1}`, not (20.26). -/
theorem eq_20_26_printed_B {κ γ β χ η θb ρ σ : ℝ} (hγ1 : γ < 1) (hβ : 0 < β) (hχ : 0 < χ)
    (hρ : 0 < ρ) :
    ρ * 1 / (κ * θb ^ η * η / ((1 - γ) * β * χ) -
      ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) + γ * κ * θb / (1 - γ))) =
      (1 - γ) / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) - κ * γ * θb) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  by_cases hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) - κ * γ * θb = 0
  · have e : κ * θb ^ η * η / ((1 - γ) * β * χ) -
        ρ * ((1 - σ) * (κ * θb ^ η * η) / ((1 - γ) * χ) + γ * κ * θb / (1 - γ)) =
        ρ / (1 - γ) * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) - κ * γ * θb) := by
      field_simp; ring
    rw [e, hD]; simp
  · field_simp
    ring

/-- `1/(ρβ) − (1 − σ) > 0` when `ρ, β ∈ (0, 1]`, `ρβ < 1` and `σ ≥ 0`. -/
theorem ll_gap_pos {ρ β σ : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ) :
    0 < 1 / (ρ * β) - (1 - σ) := by
  have : 1 < 1 / (ρ * β) := by rw [lt_div_iff₀ (by positivity)]; linarith
  linarith

/-- AKMM, p. 608: a smaller `κ` makes the response of `θ` larger (for given `θ̄`). -/
theorem ll_cs_kappa {κ₁ κ₂ γ η χ ρ β σ θb : ℝ} (hκ : 0 < κ₁) (h : κ₁ < κ₂) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ₂ γ η χ ρ β σ θb < llCoeff κ₁ γ η χ ρ β σ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  set D := θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) + γ * θb with hD
  have hDp : 0 < D := by positivity
  have e : ∀ κ, llCoeff κ γ η χ ρ β σ θb = (1 - γ) / (κ * D) := fun κ ↦ by
    rw [llCoeff, hD]; ring_nf
  rw [e, e]
  exact div_lt_div_of_pos_left (by linarith) (by positivity) (by nlinarith)

/-- AKMM, p. 608: a smaller bargaining power `γ` makes the response of `θ` larger. -/
theorem ll_cs_gamma {κ γ₁ γ₂ η χ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ₁) (h : γ₁ < γ₂)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ₂ η χ ρ β σ θb < llCoeff κ γ₁ η χ ρ β σ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  set E := κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) with hE
  have hEp : 0 < E := by positivity
  have hk1 : 0 ≤ κ * γ₁ * θb := mul_nonneg (mul_nonneg hκ.le hγ0) hθ.le
  have hk2 : 0 ≤ κ * γ₂ * θb := mul_nonneg (mul_nonneg hκ.le (hγ0.trans h.le)) hθ.le
  unfold llCoeff
  rw [← hE]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos hκ hθ]

/-- `θ̄^ηη` is strictly increasing in `η > 0` when `θ̄ ≥ 1`. -/
theorem ll_rpow_mul_strictMono {θb η₁ η₂ : ℝ} (hθ : 1 ≤ θb) (hη : 0 < η₁) (h : η₁ < η₂) :
    θb ^ η₁ * η₁ < θb ^ η₂ * η₂ := by
  have h1 : θb ^ η₁ ≤ θb ^ η₂ := Real.rpow_le_rpow_of_exponent_le hθ h.le
  have h0 : 0 < θb ^ η₁ := Real.rpow_pos_of_pos (by linarith) _
  nlinarith

/-- AKMM, p. 608: a smaller `η` makes the response larger, provided `θ̄^ηη` increases in `η`
(here `θ̄ ≥ 1`, as at the calibrated `θ̄ = 1`). -/
theorem ll_cs_eta {κ γ η₁ η₂ χ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η₁) (h : η₁ < η₂) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 1 ≤ θb) :
    llCoeff κ γ η₂ χ ρ β σ θb < llCoeff κ γ η₁ χ ρ β σ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hm := ll_rpow_mul_strictMono hθ hη h
  have hθ0 : 0 < θb := by linarith
  have hp : 0 < θb ^ η₁ := Real.rpow_pos_of_pos hθ0 _
  have hp2 : 0 < θb ^ η₂ := Real.rpow_pos_of_pos hθ0 _
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : κ * θb ^ η₁ * η₁ / χ < κ * θb ^ η₂ * η₂ / χ := by
    apply div_lt_div_of_pos_right _ hχ; nlinarith
  nlinarith

/-- AKMM, p. 608 (counterexample): for small `θ̄` a smaller `η` lowers the response. With
`θ̄ = e^{−4}`, `θ̄^ηη` is larger at `η = 1/2` than at `η = 3/4`, so the coefficient is smaller at
`η = 1/2`. -/
theorem ll_cs_eta_counterexample {κ γ χ ρ β σ : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ) :
    llCoeff κ γ (1 / 2) χ ρ β σ (exp (-4)) < llCoeff κ γ (3 / 4) χ ρ β σ (exp (-4)) := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have e1 : exp (-4) ^ (1 / 2 : ℝ) = exp (-2) := by
    rw [← Real.exp_mul]; norm_num
  have e2 : exp (-4) ^ (3 / 4 : ℝ) = exp (-3) := by
    rw [← Real.exp_mul]; norm_num
  have key : exp (-3) * (3 / 4) < exp (-2) * (1 / 2) := by
    have : exp (-2) = exp (-3) * exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have := Real.exp_one_gt_d9
    have : 0 < exp (-3) := exp_pos _
    nlinarith
  unfold llCoeff
  rw [e1, e2]
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : κ * exp (-3) * (3 / 4) / χ < κ * exp (-2) * (1 / 2) / χ := by
    apply div_lt_div_of_pos_right _ hχ; nlinarith
  nlinarith

/-- AKMM, p. 608: a larger `χ` makes the response larger. -/
theorem ll_cs_chi {κ γ η χ₁ χ₂ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ₁) (h : χ₁ < χ₂) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ η χ₁ ρ β σ θb < llCoeff κ γ η χ₂ ρ β σ θb := by
  have hχ2 : 0 < χ₂ := hχ.trans h
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : κ * θb ^ η * η / χ₂ < κ * θb ^ η * η / χ₁ := div_lt_div_of_pos_left (by positivity) hχ h
  nlinarith

/-- AKMM, p. 608: a larger persistence `ρ` makes the response larger. -/
theorem ll_cs_rho {κ γ η χ ρ₁ ρ₂ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ₁) (h : ρ₁ < ρ₂) (hβ : 0 < β) (hρβ : ρ₂ * β < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ₁ β σ θb < llCoeff κ γ η χ ρ₂ β σ θb := by
  have hg := ll_gap_pos (hρ.trans h) hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : 1 / (ρ₂ * β) < 1 / (ρ₁ * β) :=
    div_lt_div_of_pos_left one_pos (by positivity) (by nlinarith)
  have : 0 < κ * θb ^ η * η / χ := by positivity
  nlinarith

/-- AKMM, p. 608: a larger discount factor `β` makes the response larger. -/
theorem ll_cs_beta {κ γ η χ ρ β₁ β₂ σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β₁) (h : β₁ < β₂) (hρβ : ρ * β₂ < 1)
    (hσ : 0 ≤ σ) (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ β₁ σ θb < llCoeff κ γ η χ ρ β₂ σ θb := by
  have hg := ll_gap_pos hρ (hβ.trans h) hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : 1 / (ρ * β₂) < 1 / (ρ * β₁) :=
    div_lt_div_of_pos_left one_pos (by positivity) (by nlinarith)
  have : 0 < κ * θb ^ η * η / χ := by positivity
  nlinarith

/-- AKMM, p. 608: a smaller separation probability `σ` makes the response larger. -/
theorem ll_cs_sigma {κ γ η χ ρ β σ₁ σ₂ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ₁)
    (h : σ₁ < σ₂) (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ β σ₂ θb < llCoeff κ γ η χ ρ β σ₁ θb := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  unfold llCoeff
  apply div_lt_div_of_pos_left (by linarith) (by positivity)
  have : 0 < κ * θb ^ η * η / χ := by positivity
  nlinarith

/-- AKMM, §20.6.4, p. 611: with a rigid wage `w̄` the job-creation condition is
`κ/λ_f(θ_t) = βE[z_{t+1} − w̄ + (1 − σ)κ/λ_f(θ_{t+1})]`; with Cobb–Douglas matching, in logs,
the derivatives at the steady state are `A_r = κθ̄^ηη/(βχ)` (left side divided by `β`) and
`B_r = (1 − σ)κθ̄^ηη/χ`. -/
theorem eq_20_27_deriv {κ β χ η θb zb wb σ : ℝ} (hθ : 0 < θb) :
    HasDerivAt (fun x ↦ κ * (θb * exp x) ^ η / (β * χ)) (κ * θb ^ η * η / (β * χ)) 0 ∧
    HasDerivAt (fun x ↦ zb - wb + (1 - σ) * κ * (θb * exp x) ^ η / χ)
      ((1 - σ) * (κ * θb ^ η * η / χ)) 0 := by
  have hpow : ∀ x, (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ
  have hE : HasDerivAt (fun x ↦ θb ^ η * exp (η * x)) (θb ^ η * η) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul η).exp.const_mul (θb ^ η)
    simpa using this
  simp only [hpow]
  refine ⟨?_, ?_⟩
  · refine ((hE.const_mul κ).div_const (β * χ)).congr_deriv ?_; ring
  · refine (((hE.const_mul ((1 - σ) * κ)).div_const χ).const_add (zb - wb)).congr_deriv ?_
    ring

/-- AKMM, (20.27), p. 611: with rigid wages, `ρ/(A_r − ρB_r) =
[κθ̄^ηη/χ · (1/(ρβ) − (1 − σ))]^{−1}`. -/
theorem eq_20_27 {κ β χ η θb ρ σ : ℝ} (hβ : 0 < β) (hχ : 0 < χ) (hρ : 0 < ρ) :
    ρ * 1 / (κ * θb ^ η * η / (β * χ) - ρ * ((1 - σ) * (κ * θb ^ η * η / χ))) =
      1 / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ))) := by
  by_cases hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) = 0
  · have e : κ * θb ^ η * η / (β * χ) - ρ * ((1 - σ) * (κ * θb ^ η * η / χ)) =
        ρ * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ))) := by field_simp
    rw [e, hD]; simp
  · field_simp

/-- AKMM, p. 611: comparing (20.26) and (20.27), the rigid-wage response is larger: it is not
multiplied by `1 − γ` and lacks the term `κγθ̄`. -/
theorem ll_rigid_gt {κ γ η χ ρ β σ θb : ℝ} (hκ : 0 < κ) (hγ0 : 0 < γ)
    (hη : 0 < η) (hχ : 0 < χ) (hρ : 0 < ρ) (hβ : 0 < β) (hρβ : ρ * β < 1) (hσ : 0 ≤ σ)
    (hθ : 0 < θb) :
    llCoeff κ γ η χ ρ β σ θb < 1 / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ))) := by
  have hg := ll_gap_pos hρ hβ hρβ hσ
  have hp : 0 < θb ^ η := Real.rpow_pos_of_pos hθ η
  have hE : 0 < κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σ)) := by positivity
  unfold llCoeff
  rw [div_lt_div_iff₀ (by positivity) hE]
  nlinarith [mul_pos (mul_pos hκ hγ0) hθ]

/-- AKMM, 20.A.4, p. 882 (the worked example): log-linearising
`K_{t+1} = K_t^αN_t^{1−α} + (1 − δ)K_t − C_t` at the steady state gives
`K̄k_{t+1} = K̄^αN̄^{1−α}(αk_t + (1 − α)n_t) + (1 − δ)K̄k_t − C̄c_t`: the coefficients are the
derivatives of the right side in the log deviations `k`, `n`, `c` at `0`. -/
theorem eq_20_A_4_example {Kb Nb Cb α δ : ℝ} (hK : 0 < Kb) (hN : 0 < Nb) :
    HasDerivAt (fun k ↦ (Kb * exp k) ^ α * Nb ^ (1 - α) + (1 - δ) * (Kb * exp k) - Cb)
      (Kb ^ α * Nb ^ (1 - α) * α + (1 - δ) * Kb) 0 ∧
    HasDerivAt (fun n ↦ Kb ^ α * (Nb * exp n) ^ (1 - α) + (1 - δ) * Kb - Cb)
      (Kb ^ α * Nb ^ (1 - α) * (1 - α)) 0 ∧
    HasDerivAt (fun c ↦ Kb ^ α * Nb ^ (1 - α) + (1 - δ) * Kb - Cb * exp c) (-Cb) 0 := by
  have hE : ∀ a : ℝ, HasDerivAt (fun x ↦ exp (a * x)) a 0 := fun a ↦ by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).exp
  refine ⟨?_, ?_, ?_⟩
  · have h := ((((hE α).const_mul (Kb ^ α)).mul_const (Nb ^ (1 - α))).add
      (((hasDerivAt_exp (0 : ℝ)).const_mul Kb).const_mul (1 - δ))).sub_const Cb
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun k ↦ ?_)).congr_deriv ?_
    · simp only [ll_rpow_exp hK, Pi.add_apply]
    · simp only [exp_zero]; ring
  · have h := ((((hE (1 - α)).const_mul (Nb ^ (1 - α))).const_mul (Kb ^ α)).add_const
      ((1 - δ) * Kb)).sub_const Cb
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun n ↦ ?_)).congr_deriv ?_
    · simp only [ll_rpow_exp hN]
    · ring
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul Cb).const_sub
      (Kb ^ α * Nb ^ (1 - α) + (1 - δ) * Kb)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c ↦ ?_)).congr_deriv ?_
    · ring
    · simp

end AKMM.FrictionalLaborMarkets
