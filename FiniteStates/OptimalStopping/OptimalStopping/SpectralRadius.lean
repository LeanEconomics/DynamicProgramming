/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalStopping.Problem
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# The spectral radius of `L_σ`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, Exercise 4.1.1
(p. 107): `ρ(L_σ) < 1` for every policy `σ` of an optimal stopping problem.

The spectral radius of a real matrix is defined, as in Vol. 1 (1.15), as the
largest modulus of a complex eigenvalue, through Mathlib's `spectralRadius` of
the complexified matrix, and it is bounded by the ℓ∞ operator norm, which is
the largest absolute row sum. Since `L_σ = β(1 − σ)P ≥ 0` has row sums at most
`β`, `ρ(L_σ) ≤ ‖L_σ‖ ≤ β < 1`.
-/

open Finset Matrix

namespace SargentStachurski.OptimalStopping

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The complexification of a real matrix. -/
def complexify (A : Matrix X X ℝ) : Matrix X X ℂ := A.map Complex.ofReal

omit [Fintype X] [DecidableEq X] in
theorem complexify_apply (A : Matrix X X ℝ) (i j : X) : complexify A i j = (A i j : ℂ) := rfl

theorem nnnorm_complexify (A : Matrix X X ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix X X ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius (Vol. 1, (1.15)): the largest modulus of a complex eigenvalue. -/
noncomputable def specRad (A : Matrix X X ℝ) : ℝ := (spectralRadius ℂ (complexify A)).toReal

/-- The ℓ∞ operator norm is bounded by a bound on the row sums of absolute values. -/
theorem norm_le_of_rowsum_abs_le (A : Matrix X X ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, |A i j| ≤ c) : ‖A‖ ≤ c := by
  rw [Matrix.linfty_opNorm_def]
  have : (univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ c.toNNReal := by
    refine Finset.sup_le fun i _ => ?_
    have hi := h i
    exact (NNReal.coe_le_coe (r₁ := ∑ j, ‖A i j‖₊) (r₂ := c.toNNReal)).1
      (by simpa [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal c hc] using hi)
  have h2 := NNReal.coe_le_coe.2 this
  rwa [Real.coe_toNNReal c hc] at h2

/-- `ρ(A) ≤ ‖A‖` (Vol. 1, Lemma 1.2.2 for `k = 1`), for a nonempty state space. -/
theorem specRad_le_norm [Nonempty X] (A : Matrix X X ℝ) : specRad A ≤ ‖A‖ := by
  have := ENNReal.toReal_mono ENNReal.coe_ne_top
    (spectralRadius_le_nnnorm (𝕜 := ℂ) (complexify A))
  rwa [ENNReal.coe_toReal, coe_nnnorm, norm_complexify] at this

namespace StoppingProblem

variable (S : StoppingProblem X)

/-- `‖L_σ‖ ≤ β`: the rows of `L_σ ≥ 0` sum to at most `β`. -/
theorem norm_L_le (σ : Policy X) : ‖S.L σ‖ ≤ S.β :=
  norm_le_of_rowsum_abs_le _ S.β_pos.le fun x => by
    have : ∑ x', |S.L σ x x'| = ∑ x', S.L σ x x' :=
      sum_congr rfl fun x' _ => abs_of_nonneg (S.L_nonneg σ x x')
    rw [this]
    exact S.L_rowsum_le σ x

omit [DecidableEq X] in
/-- Exercise 4.1.1 (p. 107): `ρ(L_σ) < 1` for every policy `σ`. -/
theorem specRad_L_lt_one [Nonempty X] (σ : Policy X) : specRad (S.L σ) < 1 := by
  classical
  exact ((specRad_le_norm _).trans (S.norm_L_le σ)).trans_lt S.β_lt_one

end StoppingProblem

end SargentStachurski.OptimalStopping
