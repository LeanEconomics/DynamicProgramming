/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AKMMUncertainty.LinearSDE
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The recursive structural VAR

AKMM, §14.3.3, pp. 417–419. The structural VAR `AXₜ = FXₜ₋₁ + εₜ` with a lower-triangular `A`
(timing restrictions: the first variable, TFP, does not respond contemporaneously to the others).

* A lower-triangular `A` has `det A = Π aᵢᵢ` (`svar_det`), so it is invertible iff its diagonal
  entries are nonzero (`svar_isUnit_iff`), and then `A⁻¹` is lower triangular
  (`svar_inv_lower`).
* The reduced form `Xₜ = A⁻¹FXₜ₋₁ + A⁻¹εₜ`: the reduced-form innovations are `ηₜ = A⁻¹εₜ` and
  the structural shocks are backed out as `εₜ = Aηₜ` (`svar_reduced_form`).
* **The impulse response** `∂X_{t+s}/∂εₜ = (A⁻¹F)ˢA⁻¹` (`svar_irf`), via AKMM Chapter 7's
  `sde_impulse_response` for the reduced form.
* The recursive restriction: on impact the first variable responds only to its own shock, and
  in general variable `i` responds on impact only to shocks `j ≤ i` (`svar_impact_recursive`).
-/

namespace AKMM.RealBusinessCycles

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

/-- AKMM, p. 418: for a lower-triangular `A`, `det A = Π aᵢᵢ`. -/
theorem svar_det (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) : A.det = ∏ i, A i i :=
  det_of_isLowerTriangular A hA

/-- AKMM, p. 419 ("we invert the A matrix"): a lower-triangular `A` is invertible iff its
diagonal entries are nonzero. -/
theorem svar_isUnit_iff (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) :
    IsUnit A ↔ ∀ i, A i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, svar_det A hA, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp

/-- The inverse of an invertible lower-triangular matrix is lower triangular. -/
theorem svar_inv_lower (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) (hu : IsUnit A) :
    A⁻¹.IsLowerTriangular := by
  have : Invertible A := invertibleOfIsUnitDet A ((isUnit_iff_isUnit_det A).1 hu)
  exact blockTriangular_inv_of_blockTriangular hA

omit [LinearOrder n] in
/-- **AKMM, p. 418: the reduced form.** If `A` is invertible, `AXₜ₊₁ = FXₜ + εₜ₊₁` iff
`Xₜ₊₁ = A⁻¹FXₜ + ηₜ₊₁` with reduced-form innovation `ηₜ₊₁ = A⁻¹εₜ₊₁`; and the structural
shocks are recovered from the innovations as `ε = Aη`. -/
theorem svar_reduced_form (A F : Matrix n n ℝ) (hu : IsUnit A) (x x' e : n → ℝ) :
    (A *ᵥ x' = F *ᵥ x + e ↔ x' = (A⁻¹ * F) *ᵥ x + A⁻¹ *ᵥ e) ∧ A *ᵥ (A⁻¹ *ᵥ e) = e := by
  have hd := (isUnit_iff_isUnit_det A).1 hu
  have h1 : A⁻¹ * A = 1 := nonsing_inv_mul A hd
  have h2 : A * A⁻¹ = 1 := mul_nonsing_inv A hd
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, by rw [mulVec_mulVec, h2, one_mulVec]⟩
  · rw [← mulVec_mulVec, ← mulVec_add, ← h, mulVec_mulVec, h1, one_mulVec]
  · rw [h, mulVec_add, mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      one_mulVec]

omit [LinearOrder n] in
/-- **AKMM, p. 419: the impulse response of the SVAR.** Let `X` and `X′` solve
`AXₜ₊₁ = FXₜ + εₜ₊₁` from the same `X₀`, with structural shocks that differ only by `v` at date
`s + 1`. Then `X′` and `X` agree before `s + 1` and `X′_{s+1+h} − X_{s+1+h} = (A⁻¹F)ʰA⁻¹v`. -/
theorem svar_irf (A F : Matrix n n ℝ) (hu : IsUnit A) {x x' e e' : ℕ → n → ℝ}
    (hx : ∀ t, A *ᵥ x (t + 1) = F *ᵥ x t + e (t + 1))
    (hx' : ∀ t, A *ᵥ x' (t + 1) = F *ᵥ x' t + e' (t + 1)) (h0 : x' 0 = x 0) (s : ℕ)
    (v : n → ℝ) (he : ∀ t, e' t = if t = s + 1 then e t + v else e t) :
    (∀ t ≤ s, x' t = x t) ∧ ∀ h, x' (s + 1 + h) - x (s + 1 + h) = ((A⁻¹ * F) ^ h * A⁻¹) *ᵥ v := by
  refine AKMM.Uncertainty.sde_impulse_response (C := 0) (fun t => ?_) (fun t => ?_) h0 s v he
  · rw [add_zero]; exact ((svar_reduced_form A F hu _ _ _).1).1 (hx t)
  · rw [add_zero]; exact ((svar_reduced_form A F hu _ _ _).1).1 (hx' t)

/-- AKMM, p. 419: with the recursive (lower-triangular) `A`, variable `i` responds on impact
only to structural shocks `j ≤ i`; in particular the first variable (TFP) responds on impact
only to its own shock. -/
theorem svar_impact_recursive (A : Matrix n n ℝ) (hA : A.IsLowerTriangular) (hu : IsUnit A)
    {i j : n} (hij : i < j) : (A⁻¹) i j = 0 :=
  svar_inv_lower A hA hu hij

end AKMM.RealBusinessCycles
