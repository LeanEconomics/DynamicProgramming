/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMFrictionalLaborMarkets.Matching
import SearchAndMatching.JDBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Market equilibrium under endogenous vacancy creation

AKMM, §20.4.2, pp. 599–602, §20.4.3, pp. 603–604, and Appendices 20.A.1–20.A.2, pp. 879–880.
Productivity `z` follows a Markov chain on a finite set `Z` with transition weights `P z z'`;
the conditional expectation is `dmpEx P f z = Σ_{z'} P z z' f(z')`, and the market tightness
`θ(z)`, the wage `w(z)` and the values `J, V, W, U` are functions of `z`. (The book allows a
general Markov process; the derivations use only the linearity of `E`. A deterministic `z` is
the case `Z = Unit`.)

* `eq_20_10`: (20.8)–(20.9) give `κ/λ_f(θ) = βE[J(z′)]`.
* `eq_20_15`: given the continuation values, a wage `w` maximises the generalised Nash product
  (20.13), over wages with nonnegative surpluses, iff `(1 − γ)(W̃ − U) = γ(J̃ − V)` (by Miao's
  `jd_nash_iff`); `eq_20_A_1`: with positive surpluses the first-order condition of 20.A.1 is
  equivalent to (20.15).
* `dmp_J_div`: from the six equilibrium equations, `J(z)/(1 − γ) = z − b +
  (1 − σ − γλ_w(θ(z)))/(1 − γ) · κ/λ_f(θ(z))`; `eq_20_16`: the job-creation difference equation.
* `eq_20_A_2`: the wage `w = b + γ(z − b) + βE[(1 − γ)λ_w(θ)(W′ − U′)] = b + γ(z − b) + γθκ`.
* `eq_20_18`, `eq_20_19`: the two-equation system in `(θ, S)` with
  `S_t = E_t[W − U + J − V]`.

Departure: the book's Nash problem has no constraint; the maximisation is over wages giving both
parties a nonnegative surplus (where the Nash product is defined).
-/

namespace AKMM.FrictionalLaborMarkets

variable {Z : Type*} [Fintype Z]

/-- The conditional expectation `E[f(z′) | z] = Σ_{z'} P(z, z′) f(z′)`. -/
def dmpEx (P : Z → Z → ℝ) (f : Z → ℝ) (z : Z) : ℝ := ∑ z', P z z' * f z'

/-- Linearity of the conditional expectation: sums. -/
theorem dmp_ex_add (P : Z → Z → ℝ) (f g : Z → ℝ) (z : Z) :
    dmpEx P (fun z' ↦ f z' + g z') z = dmpEx P f z + dmpEx P g z := by
  simp only [dmpEx, mul_add, Finset.sum_add_distrib]

/-- Linearity of the conditional expectation: constant multiples. -/
theorem dmp_ex_mul (P : Z → Z → ℝ) (c : ℝ) (f : Z → ℝ) (z : Z) :
    dmpEx P (fun z' ↦ c * f z') z = c * dmpEx P f z := by
  simp only [dmpEx, Finset.mul_sum]; congr 1; funext z'; ring

/-- The conditional expectation depends only on the values of the integrand. -/
theorem dmp_ex_congr (P : Z → Z → ℝ) {f g : Z → ℝ} (h : ∀ z', f z' = g z') (z : Z) :
    dmpEx P f z = dmpEx P g z := by
  simp only [dmpEx, h]

/-- AKMM, (20.10), p. 600: the vacancy value (20.8) and free entry (20.9) give
`κ/λ_f(θ(z)) = βE[J(z′)]`. -/
theorem eq_20_10 (MF : MatchFn) (P : Z → Z → ℝ) {κ β : ℝ} {θ : Z → ℝ} {J V : Z → ℝ}
    (hθ : ∀ z, 0 < θ z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0) (z : Z) : κ / lamF MF (θ z) = β * dmpEx P J z := by
  have hl := match_lamF_pos MF (hθ z)
  have h := h8 z
  rw [h9 z, dmp_ex_congr P (g := fun z' ↦ lamF MF (θ z) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at h
  rw [div_eq_iff hl.ne']
  linarith

/-- AKMM, (20.13)–(20.15), p. 601: with worker surplus `W̃(w) − U = a + w` and firm surplus
`J̃(w) − V = c − w` (the continuation values do not depend on `w`), a wage with nonnegative
surpluses maximises the generalised Nash product `(W̃ − U)^γ(J̃ − V)^{1−γ}` over all such wages
iff `(1 − γ)(W̃ − U) = γ(J̃ − V)`. -/
theorem eq_20_15 {γ a c w : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hW : 0 ≤ a + w) (hF : 0 ≤ c - w) :
    (∀ w', 0 ≤ a + w' → 0 ≤ c - w' →
      (a + w') ^ γ * (c - w') ^ (1 - γ) ≤ (a + w) ^ γ * (c - w) ^ (1 - γ)) ↔
      (1 - γ) * (a + w) = γ * (c - w) := by
  have h := Miao.SearchAndMatching.jd_nash_iff (a := a) (c := c) (w := w) hγ0 hγ1 one_pos
    (by simpa using hW) hF
  simp only [one_mul, mul_one] at h
  exact h

/-- AKMM, 20.A.1, p. 879: the generalised Nash product `f(w) = (a + w)^γ(c − w)^{1−γ}` has
derivative `γ(a + w)^{γ−1}(c − w)^{1−γ} − (1 − γ)(a + w)^γ(c − w)^{−γ}` (using
`∂W̃/∂w = 1`, `∂J̃/∂w = −1`), and with positive surpluses the first-order condition `f′(w) = 0` is
equivalent to (20.15). -/
theorem eq_20_A_1 {γ a c w : ℝ} (hW : 0 < a + w) (hF : 0 < c - w) :
    HasDerivAt (fun x ↦ (a + x) ^ γ * (c - x) ^ (1 - γ))
      (γ * (a + w) ^ (γ - 1) * (c - w) ^ (1 - γ) - (1 - γ) * (a + w) ^ γ * (c - w) ^ (-γ)) w ∧
    (γ * (a + w) ^ (γ - 1) * (c - w) ^ (1 - γ) - (1 - γ) * (a + w) ^ γ * (c - w) ^ (-γ) = 0 ↔
      (1 - γ) * (a + w) = γ * (c - w)) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun x ↦ (a + x) ^ γ) (1 * γ * (a + w) ^ (γ - 1)) w :=
      ((hasDerivAt_id w).const_add a).rpow_const (Or.inl hW.ne')
    have h2 : HasDerivAt (fun x ↦ (c - x) ^ (1 - γ)) (-1 * (1 - γ) * (c - w) ^ (1 - γ - 1)) w :=
      ((hasDerivAt_id w).const_sub c).rpow_const (Or.inl hF.ne')
    refine (h1.mul h2).congr_deriv ?_
    rw [show 1 - γ - 1 = -γ by ring]; ring
  · have e1 : (a + w) ^ (γ - 1) = (a + w) ^ γ / (a + w) := Real.rpow_sub_one hW.ne' γ
    have e2 : (c - w) ^ (-γ) = (c - w) ^ (1 - γ) / (c - w) := by
      rw [← Real.rpow_sub_one hF.ne']; ring_nf
    have p1 : 0 < (a + w) ^ γ := Real.rpow_pos_of_pos hW γ
    have p2 : 0 < (c - w) ^ (1 - γ) := Real.rpow_pos_of_pos hF _
    rw [e1, e2]
    have key : γ * ((a + w) ^ γ / (a + w)) * (c - w) ^ (1 - γ) -
        (1 - γ) * (a + w) ^ γ * ((c - w) ^ (1 - γ) / (c - w)) =
        ((a + w) ^ γ * (c - w) ^ (1 - γ) / ((a + w) * (c - w))) *
          (γ * (c - w) - (1 - γ) * (a + w)) := by
      field_simp
    rw [key, mul_eq_zero]
    have : (a + w) ^ γ * (c - w) ^ (1 - γ) / ((a + w) * (c - w)) ≠ 0 := by positivity
    constructor
    · rintro (h | h)
      · exact absurd h this
      · linarith
    · intro h; right; linarith

/-- AKMM, (20.16) and (20.42) for the basic model, p. 601: the six equilibrium equations (20.7),
(20.8), (20.9), (20.11), (20.12), (20.15) give `J(z)/(1 − γ) = z − b +
(1 − σ − γλ_w(θ(z)))/(1 − γ) · κ/λ_f(θ(z))`. -/
theorem dmp_J_div (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    J z / (1 - γ) = zv z - b + (1 - σ - γ * lamW MF (θ z)) / (1 - γ) * (κ / lamF MF (θ z)) := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have hJ := h7 z
  rw [dmp_ex_congr P (g := fun z' ↦ (1 - σ) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at hJ
  have hWU : W z - U z = w z - b + β * ((1 - σ - lamW MF (θ z)) * dmpEx P J z * γ / (1 - γ)) := by
    rw [h11 z, h12 z]
    have e : ∀ z', (1 - σ) * W z' + σ * U z' - (lamW MF (θ z) * W z' +
        (1 - lamW MF (θ z)) * U z') = ((1 - σ - lamW MF (θ z)) * γ / (1 - γ)) * J z' := by
      intro z'
      have := h15 z'
      rw [h9 z'] at this
      have hw : W z' - U z' = γ * J z' / (1 - γ) := by
        rw [eq_div_iff hγ]; linarith
      calc _ = (1 - σ - lamW MF (θ z)) * (W z' - U z') := by ring
        _ = _ := by rw [hw]; ring
    have := dmp_ex_congr P e z
    rw [dmp_ex_mul] at this
    have hsub : dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z -
        dmpEx P (fun z' ↦ lamW MF (θ z) * W z' + (1 - lamW MF (θ z)) * U z') z =
        dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z' - (lamW MF (θ z) * W z' +
          (1 - lamW MF (θ z)) * U z')) z := by
      simp only [dmpEx, ← Finset.sum_sub_distrib, mul_sub]
    calc _ = w z - b + β * (dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z -
        dmpEx P (fun z' ↦ lamW MF (θ z) * W z' + (1 - lamW MF (θ z)) * U z') z) := by ring
      _ = _ := by rw [hsub, this]; ring
  have hsum : J z / (1 - γ) = J z + (W z - U z) := by
    have := h15 z
    rw [h9 z] at this
    field_simp; linarith
  rw [hsum, hJ, hWU, show κ / lamF MF (θ z) = β * dmpEx P J z from h10]
  field_simp
  ring

/-- AKMM, (20.16), p. 601: the **job-creation difference equation**
`κ/((1 − γ)λ_f(θ_t)) = βE[z_{t+1} − b + (1 − σ − γλ_w(θ_{t+1}))/(1 − γ) · κ/λ_f(θ_{t+1})]`,
derived from the six equilibrium equations (20.7), (20.8), (20.9), (20.11), (20.12), (20.15). -/
theorem eq_20_16 (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    κ / ((1 - γ) * lamF MF (θ z)) = β * dmpEx P (fun z' ↦ zv z' - b +
      (1 - σ - γ * lamW MF (θ z')) / (1 - γ) * (κ / lamF MF (θ z'))) z := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have e := dmp_ex_congr P (fun z' ↦ (dmp_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z').symm) z
  rw [e, show (fun z' ↦ J z' / (1 - γ)) = fun z' ↦ (1 - γ)⁻¹ * J z' by
    funext z'; ring, dmp_ex_mul, mul_left_comm, ← h10]
  field_simp

/-- AKMM, (20.A.2), p. 879: the equilibrium wage. From (20.7), (20.9), (20.11), (20.12) and
(20.15), `w = b + γ(z − b) + βE[(1 − γ)λ_w(θ)(W(z′) − U(z′))]`, and with (20.10),
`w = b + γ(z − b) + γθκ`. -/
theorem eq_20_A_2 (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    w z = b + γ * (zv z - b) + β * dmpEx P (fun z' ↦ (1 - γ) * lamW MF (θ z) *
      (W z' - U z')) z ∧
    w z = b + γ * (zv z - b) + γ * θ z * κ := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have hJdiv := dmp_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z
  have hJ := h7 z
  rw [dmp_ex_congr P (g := fun z' ↦ (1 - σ) * J z') (fun z' ↦ by rw [h9 z']; ring),
    dmp_ex_mul] at hJ
  have hWU : ∀ z', (1 - γ) * lamW MF (θ z) * (W z' - U z') = lamW MF (θ z) * γ * J z' := by
    intro z'
    have := h15 z'
    rw [h9 z', sub_zero] at this
    linear_combination lamW MF (θ z) * this
  have hE : β * dmpEx P (fun z' ↦ (1 - γ) * lamW MF (θ z) * (W z' - U z')) z =
      γ * θ z * κ := by
    rw [dmp_ex_congr P hWU, show (fun z' ↦ lamW MF (θ z) * γ * J z') =
      fun z' ↦ (lamW MF (θ z) * γ) * J z' from rfl, dmp_ex_mul,
      match_lamW_eq MF (hθ z)]
    have hl := match_lamF_pos MF (hθ z)
    have : β * dmpEx P J z = κ / lamF MF (θ z) := h10.symm
    calc _ = θ z * γ * lamF MF (θ z) * (β * dmpEx P J z) := by ring
      _ = _ := by rw [this]; field_simp
  have hw : w z = b + γ * (zv z - b) + γ * θ z * κ := by
    have hl := match_lamF_pos MF (hθ z)
    have hβJ : β * dmpEx P J z = κ / lamF MF (θ z) := h10.symm
    have hK : lamF MF (θ z) * (κ / lamF MF (θ z)) = κ := by field_simp
    have h1 : J z = (1 - γ) * (zv z - b) + (1 - σ) * (κ / lamF MF (θ z)) -
        γ * θ z * (lamF MF (θ z) * (κ / lamF MF (θ z))) := by
      have := hJdiv
      rw [match_lamW_eq MF (hθ z), div_eq_iff hγ] at this
      rw [this]; field_simp; ring
    rw [hK] at h1
    have h2 : J z = zv z - w z + (1 - σ) * (κ / lamF MF (θ z)) := by
      rw [hJ, ← hβJ]; ring
    linarith
  exact ⟨by rw [hE]; exact hw, hw⟩

/-- AKMM, p. 603: the expected surplus `S(z) = E[W(z′) − U(z′) + J(z′) − V(z′)]`. -/
def dmpSurplus (P : Z → Z → ℝ) (J V W U : Z → ℝ) (z : Z) : ℝ :=
  dmpEx P (fun z' ↦ W z' - U z' + J z' - V z') z

/-- AKMM, (20.18), p. 603: `κ = λ_f(θ)(1 − γ)βS`. -/
theorem eq_20_18 (MF : MatchFn) (P : Z → Z → ℝ) {κ β γ : ℝ} (hγ1 : γ < 1)
    {θ J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0) (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    κ = lamF MF (θ z) * (1 - γ) * β * dmpSurplus P J V W U z := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  have hl := match_lamF_pos MF (hθ z)
  have h10 := eq_20_10 MF P hθ h8 h9 z
  have e : ∀ z', W z' - U z' + J z' - V z' = (1 - γ)⁻¹ * J z' := by
    intro z'
    have := h15 z'
    rw [h9 z'] at this ⊢
    field_simp; linarith
  rw [dmpSurplus, dmp_ex_congr P e, dmp_ex_mul]
  rw [div_eq_iff hl.ne'] at h10
  field_simp
  linarith

/-- AKMM, (20.19), p. 604: `S_t = E_t[z_{t+1} − b + βS_{t+1}(1 − σ − γλ_w(θ_{t+1}))]`. -/
theorem eq_20_19 (MF : MatchFn) (P : Z → Z → ℝ) {κ β σ γ b : ℝ} (hγ1 : γ < 1)
    {zv θ w J V W U : Z → ℝ} (hθ : ∀ z, 0 < θ z)
    (h7 : ∀ z, J z = zv z - w z + β * dmpEx P (fun z' ↦ (1 - σ) * J z' + σ * V z') z)
    (h8 : ∀ z, V z = -κ + β * dmpEx P (fun z' ↦ lamF MF (θ z) * J z' +
      (1 - lamF MF (θ z)) * V z') z)
    (h9 : ∀ z, V z = 0)
    (h11 : ∀ z, W z = w z + β * dmpEx P (fun z' ↦ (1 - σ) * W z' + σ * U z') z)
    (h12 : ∀ z, U z = b + β * dmpEx P (fun z' ↦ lamW MF (θ z) * W z' +
      (1 - lamW MF (θ z)) * U z') z)
    (h15 : ∀ z, (1 - γ) * (W z - U z) = γ * (J z - V z)) (z : Z) :
    dmpSurplus P J V W U z = dmpEx P (fun z' ↦ zv z' - b +
      β * dmpSurplus P J V W U z' * (1 - σ - γ * lamW MF (θ z'))) z := by
  have hγ : (1 - γ) ≠ 0 := by linarith
  refine dmp_ex_congr P (fun z' ↦ ?_) z
  have hJ := dmp_J_div MF P hγ1 hθ h7 h8 h9 h11 h12 h15 z'
  have h18 := eq_20_18 MF P hγ1 hθ h8 h9 h15 z'
  have hl := match_lamF_pos MF (hθ z')
  have e : W z' - U z' + J z' - V z' = J z' / (1 - γ) := by
    have := h15 z'
    rw [h9 z'] at this ⊢
    field_simp; linarith
  rw [e, hJ]
  have hk : κ / lamF MF (θ z') = (1 - γ) * β * dmpSurplus P J V W U z' := by
    rw [div_eq_iff hl.ne', h18]; ring
  rw [hk]
  field_simp

end AKMM.FrictionalLaborMarkets
