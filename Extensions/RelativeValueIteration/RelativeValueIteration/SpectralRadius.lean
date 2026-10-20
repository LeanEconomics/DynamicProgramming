/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RelativeValueIteration.Example
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The spectral radius of a real matrix

The spectral radius `ρ(A)` of a real square matrix is the largest modulus of a complex eigenvalue
(`specRad`, `mem_spectrum_iff_eigenpair`). Gelfand's formula `‖Aᵏ‖^{1/k} → ρ(A)` for the ℓ∞
operator norm (`tendsto_norm_pow_rpow`) gives, for every `γ > ρ(A)`, a constant `C` with
`‖Aᵏ‖ ≤ Cγᵏ` for all `k` (`exists_norm_pow_le`); conversely `‖Aᵏ‖ ≤ Kαᵏ` for all `k` forces
`ρ(A) ≤ α` (`specRad_le_of_norm_pow_le`). Adapted from the `FiniteStates/ContinuousTime` project.
-/

open Filter Topology Matrix Finset

namespace DPExtensions.RelativeValueIteration

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The complexification of a real matrix. -/
def complexify (A : Matrix X X ℝ) : Matrix X X ℂ := A.map Complex.ofReal

omit [Fintype X] [DecidableEq X] in
theorem complexify_apply (A : Matrix X X ℝ) (i j : X) : complexify A i j = (A i j : ℂ) := rfl

theorem complexify_pow (A : Matrix X X ℝ) (k : ℕ) : complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := X)) A k

omit [DecidableEq X] in
theorem complexify_mul (A B : Matrix X X ℝ) : complexify (A * B) = complexify A * complexify B := by
  classical
  exact map_mul (Complex.ofRealHom.mapMatrix (m := X)) A B

theorem nnnorm_complexify (A : Matrix X X ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix X X ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius: the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix X X ℝ) : ℝ := (spectralRadius ℂ (complexify A)).toReal

omit [DecidableEq X] in
theorem spectralRadius_complexify_ne_top [Nonempty X] (A : Matrix X X ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ := by
  classical
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

omit [Fintype X] [DecidableEq X] in
theorem specRad_nonneg [Fintype X] (A : Matrix X X ℝ) : 0 ≤ specRad A := ENNReal.toReal_nonneg

/-- The spectrum of the complexification is the set of eigenvalues. -/
theorem mem_spectrum_iff_eigenpair (A : Matrix X X ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ ∃ e : X → ℂ, e ≠ 0 ∧ A *ᵥ e = μ • e := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff, Algebra.algebraMap_eq_smul_one]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨e, he, h⟩
    refine ⟨e, he, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
    exact h.symm

/-- **Gelfand's formula** for real matrices: `‖Aᵏ‖^{1/k} → ρ(A)`. -/
theorem tendsto_norm_pow_rpow [Nonempty X] (A : Matrix X X ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix X X ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k => ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- If `ρ(A) < r` then `‖Aᵏ‖ ≤ rᵏ` for all large `k`. -/
theorem eventually_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- For every `γ > ρ(A)` there is `C` with `‖Aᵏ‖ ≤ Cγᵏ` for all `k`. -/
theorem exists_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {γ : ℝ} (hγ : specRad A < γ) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ C * γ ^ k := by
  have hγ0 : 0 < γ := (specRad_nonneg A).trans_lt hγ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_norm_pow_le A hγ)
  refine ⟨1 + ∑ k ∈ range N, ‖A ^ k‖ / γ ^ k, by positivity, fun k => ?_⟩
  rcases lt_or_ge k N with hk | hk
  · have h1 : ‖A ^ k‖ / γ ^ k ≤ ∑ j ∈ range N, ‖A ^ j‖ / γ ^ j :=
      single_le_sum (f := fun j => ‖A ^ j‖ / γ ^ j) (fun j _ => by positivity) (mem_range.2 hk)
    have h2 : ‖A ^ k‖ = ‖A ^ k‖ / γ ^ k * γ ^ k := by field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have h3 := hN k hk
    have h4 : 0 ≤ ∑ j ∈ range N, ‖A ^ j‖ / γ ^ j := sum_nonneg fun j _ => by positivity
    nlinarith [pow_pos hγ0 k]

/-- If `‖Aᵏ‖ ≤ Kαᵏ` for all `k`, then `ρ(A) ≤ α`. -/
theorem specRad_le_of_norm_pow_le [Nonempty X] (A : Matrix X X ℝ) {K α : ℝ} (hK : 0 < K)
    (hα : 0 ≤ α) (h : ∀ k : ℕ, ‖A ^ k‖ ≤ K * α ^ k) : specRad A ≤ α := by
  have hK1 : Tendsto (fun k : ℕ => K ^ (1 / (k : ℝ))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun k : ℕ => 1 / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := K)).rpow h0 (Or.inl hK.ne')
    rwa [Real.rpow_zero] at this
  have hup : Tendsto (fun k : ℕ => K ^ (1 / (k : ℝ)) * α) atTop (𝓝 α) := by
    simpa using hK1.mul_const α
  refine le_of_tendsto_of_tendsto (tendsto_norm_pow_rpow A) hup ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  calc ‖A ^ k‖ ^ (1 / (k : ℝ)) ≤ (K * α ^ k) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (norm_nonneg _) (h k) (by positivity)
    _ = K ^ (1 / (k : ℝ)) * α := by
        rw [Real.mul_rpow hK.le (pow_nonneg hα k), ← Real.rpow_natCast,
          ← Real.rpow_mul hα, mul_one_div_cancel hk'.ne', Real.rpow_one]

end DPExtensions.RelativeValueIteration
