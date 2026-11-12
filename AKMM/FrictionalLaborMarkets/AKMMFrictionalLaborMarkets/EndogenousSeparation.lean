/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFrictionalLaborMarkets.DMP
import AKMMFrictionalLaborMarkets.LogLinear

/-!
# Endogenous separations

AKMM, §20.7, pp. 611–614, and 20.A.5, pp. 882–883. The matched firm chooses the separation
probability `σ` at maintenance cost `c(σ)`, `c′ < 0`.

* `eq_20_28`: the first-order condition of `σ ↦ −c(σ) + β(1 − σ)E[J′]` is `−c′(σ) = βE[J′]`, and
  with (20.10) it is `−c′(σ) = κ/λ_f(θ)`.
* `es_J_div`, `eq_20_29`: with `σ(z)` and `c(σ(z))`, the equilibrium equations give the job-creation
  equation (20.29).
* With `c(σ) = φσ^{−ξ}` and Cobb–Douglas matching: `es_foc_cd`: (20.28) reads
  `ξφσ^{−ξ−1} = κθ^η/χ`; `eq_20_31`, `eq_20_32`: its solution is exactly log-linear,
  `σ(θ̄e^x) = σ̄e^{−ηx/(ξ+1)}` and `c = c̄e^{ξηx/(ξ+1)}`; `es_ss_foc`: at the steady state
  `κσ̄θ̄^η/χ = ξc̄`.
* `eq_20_A_5_deriv`: the derivatives at the steady state of the bracket of (20.29) in the log
  deviations of `z`, `c`, `σ`, `θ`; `eq_20_A_5_misprint`: the printed first display of 20.A.5,
  with `β` on both sides, is inconsistent with the steady state for `β < 1`.
* `eq_20_A_6`: the undetermined-coefficient equation for `G`; `es_G`: substituting (20.31),
  (20.32) and the steady-state condition, `GΓ = Θ`, so `G = Θ/Γ` when `Γ ≠ 0`.
* `es_std_ratio`: `std(λ̂_w)/std(σ̂) = (1 − η)(1 + ξ)/η` (p. 613).
* `es_rigid_cancel`, `es_rigid_G`: with rigid wages the terms in `ĉ` and `σ̂` cancel exactly and
  `G` is the coefficient of (20.27) (p. 614); `es_nash_no_cancel`: with Nash bargaining they do
  not cancel (for `γ ∈ (0, 1)`, `G ≠ 0`).

Departures: `Γ ≠ 0` is an added hypothesis for `G = Θ/Γ`; the steady-state condition
`κσ̄θ̄^η/χ = ξc̄` used in 20.A.5–20.A.6 is made explicit.
-/

namespace AKMM.FrictionalLaborMarkets

open Real

variable {Z : Type*} [Fintype Z]

/-- AKMM, (20.28), p. 612: the terms of the matched firm's problem that depend on `σ` are
`−c(σ) + β(1 − σ)E[J′]` (using `V = 0`); if `c` has derivative `c′` at `σ`, the first-order
condition is `−c′(σ) = βE[J′]`, which by (20.10) is `−c′(σ) = κ/λ_f(θ)`. -/
theorem eq_20_28 {c : ℝ → ℝ} {c' σ β EJ κ lf : ℝ} (hc : HasDerivAt c c' σ)
    (h10 : κ / lf = β * EJ) :
    HasDerivAt (fun s ↦ -c s + β * ((1 - s) * EJ)) (-c' - β * EJ) σ ∧
      (-c' - β * EJ = 0 ↔ -c' = κ / lf) := by
  refine ⟨?_, ?_⟩
  · have h := hc.neg.add ((((hasDerivAt_const σ (1 : ℝ)).sub (hasDerivAt_id' σ)).mul_const
      EJ).const_mul β)
    refine h.congr_deriv ?_; ring
  · rw [h10]; constructor <;> intro h <;> linarith

/-- AKMM, (20.29), p. 612: with endogenous `σ(z)` and maintenance cost `c(σ(z))`, the equilibrium
equations give `J(z)/(1 − γ) = z − b − c(σ(z)) + (1 − σ(z) − γλ_w(θ(z)))/(1 − γ) · κ/λ_f(θ(z))`. -/
theorem es_J_div (MF : MatchFn) (P : Z → Z → ℝ) {κ β γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w σ cσ J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z - cσ z + β * dmpEx P (fun z' ↦ (1 - σ z) * J z' +
      σ z * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ z) * W z' + σ z * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    J z / (1 - γ) = zv z - b - cσ z +
      (1 - σ z - γ * lamW MF (θ z)) / (1 - γ) * (κ / lamF MF (θ z)) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have hJ := h7 z
  rw [dmp_ex_congr P (g := fun z' ↦ (1 - σ z) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at hJ
  have hw' : ∀ z', W z' - U z' = γ * J z' / (1 - γ) := by
    intro z'
    have := h15 z'
    rw [h9 z'] at this
    rw [eq_div_iff hγ]; linarith
  have e : ∀ z', (1 - σ z) * W z' + σ z * U z' - (lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') = ((1 - σ z - lamW MF (θ z)) * γ / (1 - γ)) * J z' := by
    intro z'
    calc _ = (1 - σ z - lamW MF (θ z)) * (W z' - U z') := by ring
      _ = _ := by rw [hw' z']; ring
  have hsub : dmpEx P (fun z' ↦ (1 - σ z) * W z' + σ z * U z') z -
      dmpEx P (fun z' ↦ lamW MF (θ z) * W z' + (1 - lamW MF (θ z)) * U z') z =
      ((1 - σ z - lamW MF (θ z)) * γ / (1 - γ)) * dmpEx P J z := by
    rw [← dmp_ex_mul, ← dmp_ex_congr P e]
    simp only [dmpEx, ← Finset.sum_sub_distrib, mul_sub]
  have hWU : W z - U z = w z - b + β * (((1 - σ z - lamW MF (θ z)) * γ / (1 - γ)) *
      dmpEx P J z) := by
    rw [← hsub, h11 z, h12 z]; ring
  have hsum : J z / (1 - γ) = J z + (W z - U z) := by
    rw [hw' z]; field_simp; ring
  rw [hsum, hJ, hWU, show κ / lamF MF (θ z) = β * dmpEx P J z from h10]
  field_simp
  ring

/-- AKMM, (20.29), p. 612: the job-creation equation with endogenous separations,
`κ/((1 − γ)λ_f(θ_t)) = βE[z_{t+1} − b − c(σ(z_{t+1})) +
(1 − σ(z_{t+1}) − γλ_w(θ_{t+1}))/(1 − γ) · κ/λ_f(θ_{t+1})]`. -/
theorem eq_20_29 (MF : MatchFn) (P : Z → Z → ℝ) {κ β γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w σ cσ J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z - cσ z + β * dmpEx P (fun z' ↦ (1 - σ z) * J z' +
      σ z * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ z) * W z' + σ z * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    κ / ((1 - γ) * lamF MF (θ z)) = β * dmpEx P (fun z' ↦ zv z' - b - cσ z' +
      (1 - σ z' - γ * lamW MF (θ z')) / (1 - γ) * (κ / lamF MF (θ z'))) z := by
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have e := dmp_ex_congr P (fun z' ↦ (es_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z').symm) z
  rw [e, show (fun z' ↦ J z' / (1 - γ)) = fun z' ↦ (1 - γ)⁻¹ * J z' by
    funext z'; ring, dmp_ex_mul, mul_left_comm, ← h10]
  field_simp

/-- AKMM, p. 612: with `c(σ) = φσ^{−ξ}` (so `c′(σ) = −ξφσ^{−ξ−1}`) and Cobb–Douglas matching
(`κ/λ_f(θ) = κθ^η/χ`), (20.28) reads `ξφσ^{−ξ−1} = κθ^η/χ`. -/
theorem es_foc_cd {φ ξ σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun s ↦ φ * s ^ (-ξ)) (-(ξ * φ * σ ^ (-ξ - 1))) σ := by
  have := (Real.hasDerivAt_rpow_const (p := -ξ) (Or.inl hσ.ne')).const_mul φ
  refine this.congr_deriv ?_; ring

/-- AKMM, (20.31), p. 612: if `σ̄` solves `ξφσ̄^{−ξ−1} = κθ̄^η/χ`, then for every `x`,
`σ = σ̄e^{−ηx/(ξ+1)}` solves the condition at `θ = θ̄e^x`: the log-linear relation
`σ̂ = −(η/(ξ + 1))θ̂` holds exactly. It is the only positive solution. -/
theorem eq_20_31 {φ ξ κ χ η θb σb : ℝ} (hφ : 0 < φ) (hξ : 0 < ξ) (hθ : 0 < θb) (hσ : 0 < σb)
    (hss : ξ * φ * σb ^ (-ξ - 1) = κ * θb ^ η / χ) (x : ℝ) :
    ξ * φ * (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ - 1) = κ * (θb * exp x) ^ η / χ ∧
      ∀ s, 0 < s → ξ * φ * s ^ (-ξ - 1) = κ * (θb * exp x) ^ η / χ →
        s = σb * exp (-(η / (ξ + 1)) * x) := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have e1 : (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ - 1) = σb ^ (-ξ - 1) * exp (η * x) := by
    rw [Real.mul_rpow hσ.le (exp_pos _).le, ← Real.exp_mul]
    congr 2; field_simp; ring
  have e2 : (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ x
  have hmain : ξ * φ * (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ - 1) = κ * (θb * exp x) ^ η / χ := by
    rw [e1, e2, ← mul_assoc, hss]; ring
  refine ⟨hmain, fun s hs h ↦ ?_⟩
  have hp : 0 < σb * exp (-(η / (ξ + 1)) * x) := by positivity
  rw [← hmain] at h
  have hξφ : ξ * φ ≠ 0 := by positivity
  have h' := mul_left_cancel₀ hξφ h
  have hne : (-ξ - 1) ≠ 0 := by linarith
  rw [← Real.rpow_rpow_inv hs.le hne, h', Real.rpow_rpow_inv hp.le hne]

/-- AKMM, (20.32), p. 613: along the solution of `eq_20_31` the maintenance cost is
`c = φσ^{−ξ} = c̄e^{ξηx/(ξ+1)}`, `c̄ = φσ̄^{−ξ}`: `ĉ = (ξη/(ξ + 1))θ̂` exactly. -/
theorem eq_20_32 {φ ξ η σb : ℝ} (hξ : 0 < ξ) (hσ : 0 < σb) (x : ℝ) :
    φ * (σb * exp (-(η / (ξ + 1)) * x)) ^ (-ξ) = φ * σb ^ (-ξ) * exp (ξ * η / (ξ + 1) * x) := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  rw [Real.mul_rpow hσ.le (exp_pos _).le, ← Real.exp_mul,
    show -(η / (ξ + 1)) * x * -ξ = ξ * η / (ξ + 1) * x by ring]
  ring

/-- AKMM, 20.A.5, p. 883 (used implicitly): at the steady state, (20.28) with `c = φσ^{−ξ}`,
`ξφσ̄^{−ξ−1} = κθ̄^η/χ`, gives `κσ̄θ̄^η/χ = ξc̄`, `c̄ = φσ̄^{−ξ}`. -/
theorem es_ss_foc {φ ξ κ χ η θb σb : ℝ} (hσ : 0 < σb)
    (hss : ξ * φ * σb ^ (-ξ - 1) = κ * θb ^ η / χ) :
    κ * σb * θb ^ η / χ = ξ * (φ * σb ^ (-ξ)) := by
  have e : σb ^ (-ξ - 1) = σb ^ (-ξ) / σb := Real.rpow_sub_one hσ.ne' _
  rw [e] at hss
  have : κ * σb * θb ^ η / χ = σb * (κ * θb ^ η / χ) := by ring
  rw [this, ← hss]
  field_simp

/-- AKMM, 20.A.5, p. 882: with Cobb–Douglas matching, the bracket of (20.29) is
`z − c − b + κθ^η/((1 − γ)χ) − κσθ^η/((1 − γ)χ) − γκθ/(1 − γ)` (the first display of 20.A.5,
without the misprinted `β` on the left). -/
theorem es_bracket_cd {χ η : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) {z b c σ γ κ θ : ℝ}
    (hγ1 : γ < 1) (hθ : 0 < θ) :
    z - b - c + (1 - σ - γ * lamW (cdMatch χ η hχ hη0 hη1) θ) / (1 - γ) *
      (κ / lamF (cdMatch χ η hχ hη0 hη1) θ) =
    z - c - b + κ * θ ^ η / ((1 - γ) * χ) - κ * σ * θ ^ η / ((1 - γ) * χ) -
      γ * κ * θ / (1 - γ) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  rw [match_lamW_eq _ hθ, (eq_20_23 hχ hη0 hη1 hθ).2, Real.rpow_neg hθ.le]
  have : 0 < θ ^ η := by positivity
  field_simp
  ring

/-- AKMM, 20.A.5, p. 882: the bracket of (20.29) in log deviations,
`z̄e^{ẑ} − c̄e^{ĉ} − b + κ(θ̄e^{θ̂})^η/((1 − γ)χ) − κσ̄e^{σ̂}(θ̄e^{θ̂})^η/((1 − γ)χ) −
γκθ̄e^{θ̂}/(1 − γ)`. -/
noncomputable def esR (zb cb b σb γ κ χ η θb zh ch sh x : ℝ) : ℝ :=
  zb * exp zh - cb * exp ch - b + κ * (θb * exp x) ^ η / ((1 - γ) * χ) -
    κ * (σb * exp sh) * (θb * exp x) ^ η / ((1 - γ) * χ) - γ * κ * (θb * exp x) / (1 - γ)

/-- AKMM, 20.A.5, p. 882: the derivatives of the bracket at the steady state: `z̄` in `ẑ`, `−c̄` in
`ĉ`, `−κσ̄θ̄^η/((1 − γ)χ)` in `σ̂`, and
`(1 − σ̄)κθ̄^ηη/((1 − γ)χ) − γκθ̄/(1 − γ)` in `θ̂`. -/
theorem eq_20_A_5_deriv {zb cb b σb γ κ χ η θb : ℝ} (hθ : 0 < θb) :
    HasDerivAt (fun zh ↦ esR zb cb b σb γ κ χ η θb zh 0 0 0) zb 0 ∧
    HasDerivAt (fun ch ↦ esR zb cb b σb γ κ χ η θb 0 ch 0 0) (-cb) 0 ∧
    HasDerivAt (fun sh ↦ esR zb cb b σb γ κ χ η θb 0 0 sh 0)
      (-(κ * σb * θb ^ η / ((1 - γ) * χ))) 0 ∧
    HasDerivAt (fun x ↦ esR zb cb b σb γ κ χ η θb 0 0 0 x)
      ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) 0 := by
  have hpow : ∀ x, (θb * exp x) ^ η = θb ^ η * exp (η * x) := ll_rpow_exp hθ
  have hE : HasDerivAt (fun x ↦ exp (η * x)) η 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul η).exp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul zb).add_const
      (-(cb * exp 0) - b + κ * (θb * exp 0) ^ η / ((1 - γ) * χ) -
        κ * (σb * exp 0) * (θb * exp 0) ^ η / ((1 - γ) * χ) - γ * κ * (θb * exp 0) / (1 - γ))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun zh ↦ ?_)).congr_deriv ?_
    · simp only [esR]; ring
    · simp
  · have h := ((hasDerivAt_exp (0 : ℝ)).const_mul cb).neg.add_const
      (zb * exp 0 - b + κ * (θb * exp 0) ^ η / ((1 - γ) * χ) -
        κ * (σb * exp 0) * (θb * exp 0) ^ η / ((1 - γ) * χ) - γ * κ * (θb * exp 0) / (1 - γ))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ch ↦ ?_)).congr_deriv ?_
    · simp only [esR, Pi.neg_apply]; ring
    · simp
  · have h := (((hasDerivAt_exp (0 : ℝ)).const_mul σb).const_mul
      (-(κ * (θb * exp 0) ^ η / ((1 - γ) * χ)))).add_const
      (zb * exp 0 - cb * exp 0 - b + κ * (θb * exp 0) ^ η / ((1 - γ) * χ) -
        γ * κ * (θb * exp 0) / (1 - γ))
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun sh ↦ ?_)).congr_deriv ?_
    · simp only [esR]; ring
    · simp only [exp_zero, mul_one]; ring
  · have h1 := (hE.const_mul (θb ^ η)).const_mul (κ * (1 - σb * exp 0) / ((1 - γ) * χ))
    have h2 := ((hasDerivAt_exp (0 : ℝ)).const_mul θb).const_mul (γ * κ / (1 - γ))
    have h := (h1.sub h2).add_const (zb * exp 0 - cb * exp 0 - b)
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)).congr_deriv ?_
    · simp only [esR, hpow, Pi.sub_apply]; ring
    · simp only [exp_zero, mul_one]; ring

/-- AKMM, 20.A.5, p. 882, as printed: the first display `κθ_t^η/((1 − γ)βχ) = βE[⋯]` has `β` on
both sides. At a steady state of (20.29), where `κθ̄^η/((1 − γ)βχ)` equals the bracket `R̄`, the
printed form would force `R̄ = βR̄`, impossible for `β < 1` since `R̄ > 0`. -/
theorem eq_20_A_5_misprint {κ θη γ β χ R : ℝ} (hκ : 0 < κ) (hθη : 0 < θη) (hγ1 : γ < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hχ : 0 < χ) (hcorrect : κ * θη / ((1 - γ) * β * χ) = R)
    (hprinted : κ * θη / ((1 - γ) * β * χ) = β * R) : False := by
  have h1γ : 0 < 1 - γ := by linarith
  have hR : 0 < R := by rw [← hcorrect]; positivity
  have : (1 - β) * R = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h <;> linarith

/-- AKMM, (20.A.6), p. 883: with `θ̂ = Gẑ`, `σ̂ = Eẑ`, `ĉ = Fẑ` and `E[ẑ_{t+1}] = ρẑ_t`, the
log-linearised (20.29), `Aθ̂_t = E[z̄ẑ′ − c̄ĉ′ − κσ̄θ̄^ησ̂′/((1 − γ)χ) + Bθ̂′]` (coefficients from
`eq_20_A_5_deriv`), holds for all `ẑ_t` iff
`G = llCoeff · (z̄ − c̄F − κσ̄θ̄^ηE/((1 − γ)χ))`. -/
theorem eq_20_A_6 {κ γ β χ η θb ρ σb zb cb E F G : ℝ} (hγ1 : γ < 1) (hβ : 0 < β) (hχ : 0 < χ)
    (hρ : 0 < ρ)
    (hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)) + κ * γ * θb ≠ 0) :
    (∀ zh : ℝ, κ * θb ^ η * η / ((1 - γ) * β * χ) * (G * zh) =
      (zb - cb * F - κ * σb * θb ^ η * E / ((1 - γ) * χ)) * (ρ * zh) +
        ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) * (G * (ρ * zh))) ↔
    G = llCoeff κ γ η χ ρ β σb θb * (zb - cb * F - κ * σb * θb ^ η * E / ((1 - γ) * χ)) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  set X := zb - cb * F - κ * σb * θb ^ η * E / ((1 - γ) * χ)
  have hAB : κ * θb ^ η * η / ((1 - γ) * β * χ) -
      ρ * ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) ≠ 0 := by
    have e : κ * θb ^ η * η / ((1 - γ) * β * χ) -
        ρ * ((1 - σb) * (κ * θb ^ η * η) / ((1 - γ) * χ) - γ * κ * θb / (1 - γ)) =
        ρ / (1 - γ) * (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)) + κ * γ * θb) := by
      field_simp; ring
    rw [e]; exact mul_ne_zero (div_ne_zero hρ.ne' hγ) hD
  have hK := eq_20_26 (κ := κ) (γ := γ) (β := β) (χ := χ) (η := η) (θb := θb) (ρ := ρ)
    (σ := σb) hγ1 hβ hχ hρ
  rw [← hK, ll_undetermined hAB, mul_one, div_mul_eq_mul_div]

/-- AKMM, (20.A.6) and p. 613: substituting `E = −ηG/(ξ + 1)` (20.31), `F = ξηG/(ξ + 1)` (20.32)
and the steady-state condition `κσ̄θ̄^η/χ = ξc̄` into `G = K(z̄ − c̄F − κσ̄θ̄^ηE/((1 − γ)χ))`
gives `GΓ = Θ` with `Θ = Kz̄`, `Γ = 1 + Kc̄(ξη/(ξ + 1))(1 − 1/(1 − γ))`; hence `G = Θ/Γ` when
`Γ ≠ 0`. -/
theorem es_G {K zb cb κ σb θη χ γ ξ η G : ℝ} (hγ1 : γ < 1) (hξ : 0 < ξ)
    (hfoc : κ * σb * θη / χ = ξ * cb)
    (hG : G = K * (zb - cb * (ξ * η / (ξ + 1) * G) -
      κ * σb * θη * (-(η / (ξ + 1)) * G) / ((1 - γ) * χ))) :
    G * (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ))) = K * zb ∧
      (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ)) ≠ 0 →
        G = K * zb / (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ)))) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have key : κ * σb * θη * (-(η / (ξ + 1)) * G) / ((1 - γ) * χ) =
      -(ξ * cb * (η / (ξ + 1)) * G / (1 - γ)) := by
    rw [← hfoc]
    by_cases hχ : χ = 0
    · simp [hχ]
    · field_simp
  rw [key] at hG
  have h1 : G * (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ))) = K * zb := by
    have e : G * (1 + K * cb * (ξ * η / (ξ + 1)) * (1 - 1 / (1 - γ))) =
        G + K * (cb * (ξ * η / (ξ + 1) * G) - ξ * cb * (η / (ξ + 1)) * G / (1 - γ)) := by
      field_simp
    rw [e]
    nth_rewrite 1 [hG]
    ring
  exact ⟨h1, fun hΓ ↦ by rw [eq_div_iff hΓ]; exact h1⟩

/-- AKMM, p. 613: with `λ̂_w = (1 − η)θ̂ = (1 − η)Gẑ` (from `λ_w = χθ^{1−η}`) and
`σ̂ = −(η/(ξ + 1))Gẑ` (20.31), the ratio of standard deviations is
`std(λ̂_w)/std(σ̂) = |(1 − η)G|/|−(η/(ξ + 1))G| = (1 − η)(1 + ξ)/η`. -/
theorem es_std_ratio {η ξ G : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hξ : 0 < ξ) (hG : G ≠ 0) :
    |(1 - η) * G| / |-(η / (ξ + 1)) * G| = (1 - η) * (1 + ξ) / η := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 1 - η),
    abs_of_pos (by positivity : (0 : ℝ) < η / (ξ + 1))]
  have : 0 < |G| := abs_pos.mpr hG
  field_simp
  ring

/-- AKMM, p. 613: with Cobb–Douglas matching `λ_w(θ̄e^x) = λ_w(θ̄)e^{(1−η)x}`: the log deviation
of the job-finding probability is exactly `(1 − η)θ̂`. -/
theorem es_lamW_loglinear {χ η θb : ℝ} (hχ : 0 < χ) (hη0 : 0 < η) (hη1 : η < 1) (hθ : 0 < θb)
    (x : ℝ) :
    lamW (cdMatch χ η hχ hη0 hη1) (θb * exp x) =
      lamW (cdMatch χ η hχ hη0 hη1) θb * exp ((1 - η) * x) := by
  rw [(eq_20_23 hχ hη0 hη1 (mul_pos hθ (exp_pos x))).1, (eq_20_23 hχ hη0 hη1 hθ).1,
    ll_rpow_exp hθ]
  ring

/-- AKMM, §20.7.4, p. 614: with rigid wages the bracket is `z − w̄ − c + (1 − σ)κθ^η/χ`, whose
`ĉ` and `σ̂` terms in the log-linearisation are `−c̄F − κσ̄θ̄^ηE/χ`; with (20.31), (20.32) and the
steady-state condition they cancel exactly. -/
theorem es_rigid_cancel {cb κ σb θη χ ξ η G : ℝ} (hξ : 0 < ξ) (hχ : χ ≠ 0)
    (hfoc : κ * σb * θη / χ = ξ * cb) :
    -(cb * (ξ * η / (ξ + 1) * G)) - κ * σb * θη * (-(η / (ξ + 1)) * G) / χ = 0 := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have : κ * σb * θη = ξ * cb * χ := by field_simp at hfoc; linarith
  rw [this]
  field_simp
  ring

/-- AKMM, §20.7.4, p. 614: hence with rigid wages and endogenous separations the coefficient is
the one of (20.27): if `A_rG = ρ(z̄ − c̄F − κσ̄θ̄^ηE/χ + B_rG)` then
`G = z̄[κθ̄^ηη/χ(1/(ρβ) − (1 − σ̄))]^{−1}`. -/
theorem es_rigid_G {κ β χ η θb ρ σb zb cb ξ G : ℝ} (hβ : 0 < β) (hχ : 0 < χ) (hρ : 0 < ρ)
    (hξ : 0 < ξ) (hfoc : κ * σb * θb ^ η / χ = ξ * cb)
    (hD : κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)) ≠ 0)
    (heq : κ * θb ^ η * η / (β * χ) * G = ρ * (zb - cb * (ξ * η / (ξ + 1) * G) -
      κ * σb * θb ^ η * (-(η / (ξ + 1)) * G) / χ + (1 - σb) * (κ * θb ^ η * η / χ) * G)) :
    G = zb * (1 / (κ * θb ^ η * η / χ * (1 / (ρ * β) - (1 - σb)))) := by
  have hc := es_rigid_cancel (G := G) (η := η) hξ hχ.ne' hfoc
  have e2 : κ * θb ^ η * η / (β * χ) * G =
      ρ * (zb + (1 - σb) * (κ * θb ^ η * η / χ) * G) := by
    rw [heq]; linear_combination ρ * hc
  rw [mul_one_div, eq_div_iff hD]
  field_simp at e2 ⊢
  linarith

/-- AKMM, §20.7.2, p. 613: with Nash bargaining the `ĉ` and `σ̂` terms do not cancel:
`−c̄F − κσ̄θ̄^ηE/((1 − γ)χ) = (γ/(1 − γ))c̄ξηG/(ξ + 1)`, nonzero for `γ ∈ (0, 1)` and
`c̄, η, G ≠ 0`. -/
theorem es_nash_no_cancel {cb κ σb θη χ ξ η G γ : ℝ} (hξ : 0 < ξ) (hχ : χ ≠ 0) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hcb : cb ≠ 0) (hη : η ≠ 0) (hG : G ≠ 0)
    (hfoc : κ * σb * θη / χ = ξ * cb) :
    -(cb * (ξ * η / (ξ + 1) * G)) - κ * σb * θη * (-(η / (ξ + 1)) * G) / ((1 - γ) * χ) =
      γ / (1 - γ) * (cb * ξ * η * G / (ξ + 1)) ∧
    γ / (1 - γ) * (cb * ξ * η * G / (ξ + 1)) ≠ 0 := by
  have hξ1 : (ξ + 1) ≠ 0 := by linarith
  have hγ : (1 - γ) ≠ 0 := by linarith
  have : κ * σb * θη = ξ * cb * χ := by field_simp at hfoc; linarith
  refine ⟨?_, ?_⟩
  · rw [this]; field_simp; ring
  · have : (1 - γ) ≠ 0 := hγ
    have : γ ≠ 0 := hγ0.ne'
    have : ξ ≠ 0 := hξ.ne'
    positivity

end AKMM.FrictionalLaborMarkets
