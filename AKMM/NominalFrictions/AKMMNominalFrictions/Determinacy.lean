/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.TaylorRuleSystem

/-!
# Determinacy and the Taylor principle

AKMM, §18.3, p. 544, condition (18.18), and Appendix 18.A.2, p. 873 (Bullard–Mitra by the
Jury criterion).

* `det_system`: substituting the rule into the IS curve and the Phillips curve gives the book's
  system `βσ x_{t+1} = (βσ + βφ_x + κ) x_t + (βφ_π − 1) π_t`, `β π_{t+1} = π_t − κ x_t`.
* `det_inverse`, `det_coeff_eq_AT`: the book's inverse and coefficient matrix; the latter is
  Galí's `A_T`. `det_a1`, `det_a0`: the coefficients `a₁ = −tr`, `a₀ = det` of the
  characteristic polynomial `λ² + a₁λ + a₀`.
* `det_jury_iff`: for `σ > 0`, `κ, φ_π, φ_x ≥ 0` and `0 ≤ β ≤ 1` (the book's assumptions), the Jury
  conditions `|a₀| < 1`, `|a₁| < 1 + a₀` hold iff (18.18), `(1 − β)φ_x + κ(φ_π − 1) > 0`;
  `det_roots_iff`: equivalently both roots lie inside the unit circle (Galí's
  `schurStable_iff_roots`).
* `eq_18_18`: the three-equation model has a unique bounded equilibrium iff (18.18)
  (Galí's `determinate_iff_BM`, for `κ > 0`, `0 < β < 1`).
* `det_taylor_sufficient`, `det_taylor_necessary`: `φ_π > 1` suffices; with `φ_x = 0` it is
  necessary.
* **Correction**: `|a₀| < 1` is not automatic as the book says: at `β = 1` with
  `φ_x = φ_π = 0`, `a₀ = 1` (`det_a0_not_automatic`). It does follow from (18.18), so the
  equivalence stands.
-/

namespace AKMM.NominalFrictions

open Gali.BasicNewKeynesianModel Gali.BasicNewKeynesianModel.TaylorRuleSystem

/-- **AKMM, App. 18.A.2, p. 873**: with the IS curve `x_t = x_{t+1} − σ⁻¹(i_t − π_{t+1})`, the
Phillips curve `π_t = κx_t + βπ_{t+1}` and the rule `i_t = φ_π π_t + φ_x x_t` (deterministic,
`π* = 0`, in deviations from the steady state), `βσ x_{t+1} = (βσ + βφ_x + κ) x_t +
(βφ_π − 1) π_t` and `β π_{t+1} = π_t − κ x_t`. -/
theorem det_system {β σ κ φπ φx x x' π π' i : ℝ} (hσ : σ ≠ 0)
    (his : x = x' - σ⁻¹ * (i - π')) (hpc : π = κ * x + β * π') (hrule : i = φπ * π + φx * x) :
    β * σ * x' = (β * σ + β * φx + κ) * x + (β * φπ - 1) * π ∧ β * π' = π - κ * x := by
  have h1 : σ * x' = σ * x + i - π' := by
    rw [his]; field_simp; ring
  refine ⟨?_, by linarith⟩
  rw [hrule] at h1
  linear_combination β * h1 + hpc

/-- AKMM, p. 873: the matrix on the left of the system, `diag(βσ, β)`. -/
def detM0 (β σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![β * σ, 0; 0, β]

/-- AKMM, p. 873: the matrix on the right, `[[βσ + βφ_x + κ, βφ_π − 1], [−κ, 1]]`. -/
def detM1 (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β * σ + β * φx + κ, β * φπ - 1; -κ, 1]

/-- AKMM, p. 873: the printed inverse,
`(1/(β(σ + φ_x + κφ_π))) [[1, 1 − βφ_π], [κ, βσ + βφ_x + κ]]`. -/
noncomputable def detInv (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (β * (σ + φx + κ * φπ))) • !![1, 1 - β * φπ; κ, β * σ + β * φx + κ]

/-- **AKMM, p. 873**: the printed inverse is the inverse of the right-hand matrix
(`β ≠ 0`, `σ + φ_x + κφ_π ≠ 0`). -/
theorem det_inverse {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hS : σ + φx + κ * φπ ≠ 0) :
    detM1 β σ κ φπ φx * detInv β σ κ φπ φx = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [detM1, detInv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- **AKMM, p. 873**: the coefficient matrix multiplying `(x_{t+1}, π_{t+1})`,
`(1/(σ + φ_x + κφ_π)) [[σ, 1 − βφ_π], [κσ, βσ + βφ_x + κ]]`, is `M₁⁻¹ M₀`, and it is Galí's
`A_T`. -/
theorem det_coeff_eq_AT {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hS : σ + φx + κ * φπ ≠ 0) :
    detInv β σ κ φπ φx * detM0 β σ = AT β σ κ φπ φx ∧
      AT β σ κ φπ φx = (1 / (σ + φx + κ * φπ)) •
        !![σ, 1 - β * φπ; κ * σ, β * σ + β * φx + κ] := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [detM0, detInv, AT, omega, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp
    all_goals ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [AT, omega, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul,
        Fin.zero_eta, Fin.mk_one] <;> ring

/-- **AKMM, p. 873**: `a₁ = −(σ + βσ + βφ_x + κ)/(σ + φ_x + κφ_π) = −tr A_T`. -/
theorem det_a1 {β σ κ φπ φx : ℝ} (hS : σ + φx + κ * φπ ≠ 0) :
    -tr2 (AT β σ κ φπ φx) = -((σ + β * σ + β * φx + κ) / (σ + φx + κ * φπ)) := by
  rw [tr2_AT hS]; ring

/-- **AKMM, p. 873**: `a₀ = βσ/(σ + φ_x + κφ_π) = det A_T`. -/
theorem det_a0 {β σ κ φπ φx : ℝ} (hS : σ + φx + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φx) = β * σ / (σ + φx + κ * φπ) := by
  rw [det2_AT hS]; ring

/-- **AKMM, (18.18) and App. 18.A.2, p. 873 (Jury)**: for `σ > 0`, `κ, φ_π, φ_x ≥ 0` and
`0 ≤ β ≤ 1`, the Jury conditions `|a₀| < 1` and `|a₁| < 1 + a₀` hold iff
`(1 − β)φ_x + κ(φ_π − 1) > 0`. -/
theorem det_jury_iff {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    SchurStable (tr2 (AT β σ κ φπ φx)) (det2 (AT β σ κ φπ φx)) ↔
      0 < (1 - β) * φx + κ * (φπ - 1) := by
  have hS : 0 < σ + φx + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  unfold SchurStable
  have hT0 : 0 ≤ (σ * (1 + β) + κ + β * φx) / (σ + φx + κ * φπ) := by positivity
  have hD0 : 0 ≤ σ * β / (σ + φx + κ * φπ) := by positivity
  rw [abs_of_nonneg hD0, abs_of_nonneg hT0, div_lt_one hS,
    show 1 + σ * β / (σ + φx + κ * φπ) = (σ + φx + κ * φπ + σ * β) / (σ + φx + κ * φπ) by
      field_simp, div_lt_div_iff_of_pos_right hS]
  constructor
  · rintro ⟨-, h⟩; nlinarith
  · intro h
    refine ⟨by nlinarith [mul_nonneg hβ0 hφx, mul_nonneg (sub_nonneg.2 hβ1) hσ.le], by nlinarith⟩

/-- **AKMM, p. 873 (correction)**: the book says `|a₀| < 1` "holds as we assume `β ∈ [0, 1]`,
all the parameters are weakly positive and `σ` is strictly positive"; at `β = 1`,
`φ_x = φ_π = 0`, `a₀ = 1`. -/
theorem det_a0_not_automatic {σ κ : ℝ} (hσ : 0 < σ) : det2 (AT 1 σ κ 0 0) = 1 := by
  rw [det_a0 (by simpa using hσ.ne')]; simp [hσ.ne']

/-- **AKMM, App. 18.A.2, p. 873**: under the assumptions of `det_jury_iff`, both roots of the
characteristic polynomial `λ² + a₁λ + a₀` of the coefficient matrix lie strictly inside the
unit circle iff (18.18) (Galí's `schurStable_iff_roots`, `T = −a₁`, `D = a₀`). -/
theorem det_roots_iff {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    (‖root₁ (tr2 (AT β σ κ φπ φx)) (det2 (AT β σ κ φπ φx))‖ < 1 ∧
      ‖root₂ (tr2 (AT β σ κ φπ φx)) (det2 (AT β σ κ φπ φx))‖ < 1) ↔
      0 < (1 - β) * φx + κ * (φπ - 1) :=
  (schurStable_iff_roots _ _).symm.trans (det_jury_iff hσ hκ hβ0 hβ1 hφπ hφx)

/-- **AKMM, (18.18), p. 544**: the three-equation model (in Galí's form
`x_t = A_T E_t x_{t+1} + B_T u_t`, `TaylorRuleSystem.equilibrium_iff_solves`) has a unique
bounded equilibrium for every bounded forcing iff `(1 − β)φ_x + κ(φ_π − 1) > 0`
(Galí's `determinate_iff_BM`, `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_x ≥ 0`). -/
theorem eq_18_18 {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {β σ κ φπ φx : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    𝔼.Determinate (AT β σ κ φπ φx) ↔ 0 < (1 - β) * φx + κ * (φπ - 1) := by
  rw [determinate_iff_BM 𝔼 hσ hκ hβ0 hβ1 hφπ hφx]
  constructor <;> intro h <;> linarith

/-- **AKMM, p. 544**: "`φ_π > 1` is sufficient for this condition to hold". -/
theorem det_taylor_sufficient {β κ φπ φx : ℝ} (hκ : 0 < κ) (hβ1 : β ≤ 1) (hφx : 0 ≤ φx)
    (h : 1 < φπ) : 0 < (1 - β) * φx + κ * (φπ - 1) := by
  have := mul_nonneg (sub_nonneg.2 hβ1) hφx
  nlinarith

/-- **AKMM, p. 544**: "and necessary if `φ_x = 0`". -/
theorem det_taylor_necessary {β κ φπ : ℝ} (hκ : 0 < κ) :
    0 < (1 - β) * 0 + κ * (φπ - 1) ↔ 1 < φπ := by
  rw [mul_zero, zero_add]
  constructor
  · intro h; by_contra hc; push Not at hc; nlinarith
  · intro h; nlinarith

end AKMM.NominalFrictions
