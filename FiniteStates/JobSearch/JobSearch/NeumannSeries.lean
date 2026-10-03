/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import JobSearch.Contractions
import JobSearch.Norms
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The spectral radius and the Neumann series lemma

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.1.4 (pp. 16–19),
with Example 1.2.2 (p. 20), Exercise 1.2.17 (p. 22) and Exercise 1.2.20 (p. 22).

For a real `n × n` matrix `A`, the spectral radius (1.15) is
`ρ(A) = max{|λ| : λ an eigenvalue of A}`, the eigenvalues being complex. Here
`ρ(A)` is Mathlib's `spectralRadius ℂ` of the complexification of `A`, made
real-valued; `mem_spectrum_iff_eigenpair` confirms that the spectrum is the set
of eigenvalues in the book's sense.

* Theorem 1.2.1 (Neumann series lemma): `ρ(A) < 1` implies `I − A` is
  invertible and `(I − A)⁻¹ = ∑ₖ Aᵏ`.
* Lemma 1.2.2: `ρ(B)ᵏ ≤ ‖Bᵏ‖` and `‖Bᵏ‖^{1/k} → ρ(B)` (Gelfand's formula).
  The book quotes this from Bollobás; here the second part is Mathlib's
  `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`, transported to
  real matrices, and the first follows from Mathlib's bound on the spectral
  radius by `‖aᵏ‖^{1/k}`.
* Exercises 1.2.10–1.2.14, 1.2.17 and 1.2.20.

Matrix norms are the ℓ∞ operator norm of `Norms.lean` (`opNorm`, the maximum
absolute row sum), installed as a local instance so that `‖A‖` means `opNorm A`.
Statements about the spectral radius assume `n ≥ 1`, so that the spectrum is
nonempty and `‖I‖ = 1`.
-/

open Filter Topology Matrix

namespace SargentStachurski.JobSearch

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- Under the local ℓ∞ operator norm instance, `‖A‖` is `opNorm A` of `Norms.lean`. -/
theorem opNorm_eq_norm (A : Matrix (Fin n) (Fin n) ℝ) : opNorm A = ‖A‖ := rfl

/-- The complexification of a real matrix, so that complex eigenvalues can be spoken of. -/
def complexify (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  A.map Complex.ofReal

theorem complexify_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    complexify A i j = (A i j : ℂ) := rfl

/-- Complexification is a ring homomorphism, so it commutes with powers. -/
theorem complexify_pow (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k :=
  map_pow (Complex.ofRealHom.mapMatrix (m := Fin n)) A k

theorem complexify_smul (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    complexify (α • A) = (α : ℂ) • complexify A := by
  ext i j
  simp [complexify_apply]

/-- The ℓ∞ operator norm is unchanged by complexification. -/
theorem nnnorm_complexify (A : Matrix (Fin n) (Fin n) ℝ) : ‖complexify A‖₊ = ‖A‖₊ := by
  simp only [Matrix.linfty_opNNNorm_def, complexify_apply, Complex.nnnorm_real]

theorem norm_complexify (A : Matrix (Fin n) (Fin n) ℝ) : ‖complexify A‖ = ‖A‖ :=
  congrArg NNReal.toReal (nnnorm_complexify A)

/-- The spectral radius (1.15), p. 18: the largest modulus of a (complex) eigenvalue of `A`. -/
noncomputable def specRad (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (spectralRadius ℂ (complexify A)).toReal

theorem spectralRadius_complexify_ne_top [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    spectralRadius ℂ (complexify A) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm (complexify A))

theorem specRad_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ specRad A := ENNReal.toReal_nonneg

/-- The spectrum of the complexification is the set of eigenvalues in the book's sense (p. 17):
`λ` is an eigenvalue iff `Ae = λe` for some nonzero complex vector `e`. -/
theorem mem_spectrum_iff_eigenpair (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify A) ↔ ∃ e : Fin n → ℂ, e ≠ 0 ∧ complexify A *ᵥ e = μ • e := by
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

/-- Lemma 1.2.2 (p. 19), second part, Gelfand's formula: `‖Bᵏ‖^{1/k} → ρ(B)`. -/
theorem tendsto_norm_pow_rpow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun k : ℕ => ‖A ^ k‖ ^ (1 / (k : ℝ))) atTop (𝓝 (specRad A)) := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A)
  have h2 := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp h
  refine h2.congr fun k => ?_
  simp only [Function.comp, ← complexify_pow, norm_complexify]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)

/-- Lemma 1.2.2 (p. 19), first part: `ρ(B)ᵏ ≤ ‖Bᵏ‖` for every `k`. -/
theorem specRad_pow_le_norm_pow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    specRad A ^ k ≤ ‖A ^ k‖ := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ (complexify A) m
    rw [nnnorm_one, ENNReal.coe_one, ENNReal.one_rpow, mul_one] at h
    -- raise both sides to the power `m + 1`
    have hexp : (1 / ((m : ℝ) + 1)) * ((m + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    have h' : spectralRadius ℂ (complexify A) ^ (m + 1) ≤ ‖complexify A ^ (m + 1)‖₊ := by
      have := ENNReal.rpow_le_rpow h (Nat.cast_nonneg (m + 1))
      rwa [← ENNReal.rpow_mul, hexp, ENNReal.rpow_one, ENNReal.rpow_natCast] at this
    have h'' := ENNReal.toReal_mono ENNReal.coe_ne_top h'
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm, ← complexify_pow,
      norm_complexify] at h''
    exact h''

/-- If `ρ(A) < r` then `‖Aᵏ‖ ≤ rᵏ` for all large `k`: the quantitative content of Gelfand's
formula used throughout the section. -/
theorem eventually_norm_pow_le [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ}
    (hr : specRad A < r) : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ≤ r ^ k := by
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ ^ (1 / (k : ℝ)) < r :=
    (tendsto_norm_pow_rpow A).eventually (gt_mem_nhds hr)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  have hnn : 0 ≤ ‖A ^ k‖ := norm_nonneg _
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hk.le (Nat.cast_nonneg k)
  rwa [← Real.rpow_mul hnn, one_div_mul_cancel hkr, Real.rpow_one, Real.rpow_natCast] at this

/-- Exercise 1.2.11 (i), p. 19, the "if" direction: `ρ(A) < 1` implies `‖Aᵏ‖ → 0`. -/
theorem tendsto_norm_pow_zero [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (eventually_norm_pow_le A hr1)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr2)

/-- `ρ(A) < 1` implies `Aᵏ → 0`. -/
theorem tendsto_pow_zero [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.2 (tendsto_norm_pow_zero A hρ)

/-- Exercise 1.2.11 (i), p. 19, the "only if" direction: if `‖Bᵏ‖ → 0` then `ρ(B) < 1`. -/
theorem specRad_lt_one_of_tendsto [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Tendsto (fun k : ℕ => ‖A ^ k‖) atTop (𝓝 0)) : specRad A < 1 := by
  by_contra hge
  have hge' : 1 ≤ specRad A := not_lt.1 hge
  have hev : ∀ᶠ k : ℕ in atTop, ‖A ^ k‖ < 1 := h.eventually (gt_mem_nhds one_pos)
  obtain ⟨k, hk⟩ := hev.exists
  have : 1 ≤ ‖A ^ k‖ := (one_le_pow₀ hge').trans (specRad_pow_le_norm_pow A k)
  linarith

/-- Exercise 1.2.11 (ii), p. 19: `ρ(B) > 1` implies `‖Bᵏ‖ → ∞`. -/
theorem tendsto_norm_pow_atTop [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : 1 < specRad A) :
    Tendsto (fun k : ℕ => ‖A ^ k‖) atTop atTop :=
  tendsto_atTop_mono (specRad_pow_le_norm_pow A) (tendsto_pow_atTop_atTop_of_one_lt hρ)

/-- Exercise 1.2.10 (p. 18): `ρ(αB) = |α| ρ(B)`, proved from Gelfand's formula. -/
theorem specRad_smul [NeZero n] (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    specRad (α • A) = |α| * specRad A := by
  have h1 := tendsto_norm_pow_rpow (α • A)
  have h2 := (tendsto_norm_pow_rpow A).const_mul |α|
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [smul_pow, norm_smul, Real.norm_eq_abs, abs_pow,
    Real.mul_rpow (pow_nonneg (abs_nonneg α) k) (norm_nonneg _), one_div,
    Real.pow_rpow_inv_natCast (abs_nonneg α) hk.ne']

/-- Exercise 1.2.12 (p. 19): if `A` and `B` commute then `ρ(AB) ≤ ρ(A) ρ(B)`, via Gelfand's
formula applied to `(AB)ᵏ = AᵏBᵏ`. -/
theorem specRad_mul_le [NeZero n] (A B : Matrix (Fin n) (Fin n) ℝ) (hAB : Commute A B) :
    specRad (A * B) ≤ specRad A * specRad B := by
  refine le_of_tendsto_of_tendsto' (tendsto_norm_pow_rpow (A * B))
    ((tendsto_norm_pow_rpow A).mul (tendsto_norm_pow_rpow B)) fun k => ?_
  rw [hAB.mul_pow, ← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_mul_le _ _) (by positivity)

/-- Exercise 1.2.13 (p. 19): `ρ(A) < 1` implies `∑ₖ Aᵏ` converges. -/
theorem summable_pow [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    Summable fun k : ℕ => A ^ k := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := FiniteDimensional.complete ℝ _
  obtain ⟨r, hr1, hr2⟩ := exists_between hρ
  have hr0 : 0 ≤ r := (specRad_nonneg A).trans hr1.le
  exact Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr2)
    (eventually_norm_pow_le A hr1)

/-- Exercise 1.2.14 (p. 19): when `S = ∑ₖ Aᵏ` exists, `(I − A) S = I`. The informal argument
`I + AS = S` of p. 18 made rigorous: the partial sums telescope, `(I − A) ∑_{k<K} Aᵏ = I − Aᴷ`,
and `Aᴷ → 0` because the series converges. -/
theorem one_sub_mul_tsum (A : Matrix (Fin n) (Fin n) ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (1 - A) * ∑' k : ℕ, A ^ k = 1 := by
  have h1 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ Finset.range K, A ^ k) atTop
      (𝓝 ((1 - A) * ∑' k : ℕ, A ^ k)) :=
    hs.hasSum.tendsto_sum_nat.const_mul (1 - A)
  have h2 : Tendsto (fun K : ℕ => (1 - A) * ∑ k ∈ Finset.range K, A ^ k) atTop (𝓝 1) := by
    simp_rw [mul_neg_geom_sum]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

/-- Exercise 1.2.14 (p. 19), the other side: `S (I − A) = I`. -/
theorem tsum_mul_one_sub (A : Matrix (Fin n) (Fin n) ℝ) (hs : Summable fun k : ℕ => A ^ k) :
    (∑' k : ℕ, A ^ k) * (1 - A) = 1 := by
  have h1 : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, A ^ k) * (1 - A)) atTop
      (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have h2 : Tendsto (fun K : ℕ => (∑ k ∈ Finset.range K, A ^ k) * (1 - A)) atTop (𝓝 1) := by
    simp_rw [geom_sum_mul_neg]
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  exact tendsto_nhds_unique h1 h2

/-- Exercise 1.2.14 (p. 19), conclusion: when `∑ₖ Aᵏ` exists, `I − A` is invertible with
inverse `∑ₖ Aᵏ`. -/
theorem isUnit_one_sub_of_summable (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : Summable fun k : ℕ => A ^ k) : IsUnit (1 - A) :=
  ⟨⟨1 - A, ∑' k : ℕ, A ^ k, one_sub_mul_tsum A hs, tsum_mul_one_sub A hs⟩, rfl⟩

theorem inv_one_sub_of_summable (A : Matrix (Fin n) (Fin n) ℝ)
    (hs : Summable fun k : ℕ => A ^ k) : (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  Matrix.inv_eq_right_inv (one_sub_mul_tsum A hs)

/-- Theorem 1.2.1 (Neumann series lemma, p. 18): if `ρ(A) < 1` then `I − A` is nonsingular and
`(I − A)⁻¹ = ∑ₖ Aᵏ`. -/
theorem neumann_series [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    IsUnit (1 - A) ∧ (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  ⟨isUnit_one_sub_of_summable A (summable_pow A hρ),
    inv_one_sub_of_summable A (summable_pow A hρ)⟩

/-- `(I − A)⁻¹ (I − A) = I` when `ρ(A) < 1`. -/
theorem inv_one_sub_mul [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    (1 - A)⁻¹ * (1 - A) = 1 := by
  rw [(neumann_series A hρ).2]
  exact tsum_mul_one_sub A (summable_pow A hρ)

/-- `(I − A)(I − A)⁻¹ = I` when `ρ(A) < 1`. -/
theorem mul_inv_one_sub [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1) :
    (1 - A) * (1 - A)⁻¹ = 1 := by
  rw [(neumann_series A hρ).2]
  exact one_sub_mul_tsum A (summable_pow A hρ)

/-- The affine map `Tu = Au + b` of Example 1.2.2 (p. 20). -/
def affine (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  A *ᵥ u + b

/-- Example 1.2.2 (p. 20): `u` is a fixed point of `Tu = Au + b` iff `u = Au + b`. -/
theorem isFixedPt_affine_iff (A : Matrix (Fin n) (Fin n) ℝ) (b u : Fin n → ℝ) :
    Function.IsFixedPt (affine A b) u ↔ u = A *ᵥ u + b :=
  ⟨fun h => h.eq.symm, fun h => h.symm⟩

/-- The system `u = Au + b` (p. 18) has the solution `u* = (I − A)⁻¹ b` when `ρ(A) < 1`. -/
theorem isFixedPt_affine_inv [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b : Fin n → ℝ) : Function.IsFixedPt (affine A b) ((1 - A)⁻¹ *ᵥ b) := by
  change A *ᵥ ((1 - A)⁻¹ *ᵥ b) + b = (1 - A)⁻¹ *ᵥ b
  have h2 := mul_inv_one_sub A hρ
  have hAB : A * (1 - A)⁻¹ = (1 - A)⁻¹ - 1 := by
    have h3 : (1 - A) * (1 - A)⁻¹ = (1 - A)⁻¹ - A * (1 - A)⁻¹ := by rw [sub_mul, one_mul]
    rw [h3] at h2
    calc A * (1 - A)⁻¹ = (1 - A)⁻¹ - ((1 - A)⁻¹ - A * (1 - A)⁻¹) := by abel
      _ = (1 - A)⁻¹ - 1 := by rw [h2]
  rw [mulVec_mulVec, hAB, sub_mulVec, one_mulVec]
  abel

/-- Theorem 1.2.1's corollary (p. 18) and Example 1.2.2: when `ρ(A) < 1`, `u = Au + b` has
exactly one solution, `u* = (I − A)⁻¹ b`. -/
theorem affine_fixedPt_unique [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b u : Fin n → ℝ) (hu : Function.IsFixedPt (affine A b) u) : u = (1 - A)⁻¹ *ᵥ b := by
  have hu' : A *ᵥ u + b = u := hu.eq
  have h : (1 - A) *ᵥ u = b := by
    rw [sub_mulVec, one_mulVec]
    calc u - A *ᵥ u = (A *ᵥ u + b) - A *ᵥ u := by rw [hu']
      _ = b := by abel
  rw [← h, mulVec_mulVec, inv_one_sub_mul A hρ, one_mulVec]

/-- Exercise 1.2.17 (p. 22), the formula (1.16): `Tᵏu = Aᵏu + Aᵏ⁻¹b + ⋯ + Ab + b`. -/
theorem affine_iterate (A : Matrix (Fin n) (Fin n) ℝ) (b u : Fin n → ℝ) (k : ℕ) :
    (affine A b)^[k] u = A ^ k *ᵥ u + ∑ i ∈ Finset.range k, A ^ i *ᵥ b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ']
    simp only [affine, mulVec_add, mulVec_mulVec, pow_zero, one_mulVec, Matrix.mulVec_sum,
      ← pow_succ']
    abel

/-- Exercise 1.2.17 (p. 22), continued: the iterates converge to `u* = (I − A)⁻¹ b`, because
`Tᵏu − u* = Aᵏ(u − u*)` and `Aᵏ → 0`. -/
theorem tendsto_affine_iterate [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b u : Fin n → ℝ) :
    Tendsto (fun k : ℕ => (affine A b)^[k] u) atTop (𝓝 ((1 - A)⁻¹ *ᵥ b)) := by
  set u' := (1 - A)⁻¹ *ᵥ b with hu'
  have hfix : Function.IsFixedPt (affine A b) u' := isFixedPt_affine_inv A hρ b
  have hdiff : ∀ k : ℕ, (affine A b)^[k] u - u' = A ^ k *ᵥ (u - u') := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ', ← mulVec_mulVec, ← ih]
      conv_lhs => rw [← hfix.eq]
      simp only [affine, mulVec_sub]
      abel
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm, hdiff]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun k => Matrix.linfty_opNorm_mulVec (A ^ k) (u - u')) ?_
  simpa using (tendsto_norm_pow_zero A hρ).mul_const ‖u - u'‖

/-- Exercise 1.2.17 (p. 22), conclusion: `Tu = Au + b` is globally stable on `ℝⁿ` whenever
`ρ(A) < 1`. -/
theorem globallyStable_affine [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (hρ : specRad A < 1)
    (b : Fin n → ℝ) : GloballyStable (affine A b) :=
  globallyStable_of_tendsto (isFixedPt_affine_inv A hρ b) (tendsto_affine_iterate A hρ b)

/-- Exercise 1.2.20 (p. 22): if `‖A‖ < 1` then `Tu = Au + b` is a contraction of modulus `‖A‖`
on `ℝⁿ`, in the supremum norm. -/
theorem isContractionOn_affine (A : Matrix (Fin n) (Fin n) ℝ) (hA : ‖A‖ < 1) (b : Fin n → ℝ) :
    IsContractionOn (affine A b) Set.univ ‖A‖ := by
  refine ⟨Set.mapsTo_univ _ _, norm_nonneg A, hA, fun u _ v _ => ?_⟩
  simp only [affine]
  rw [add_sub_add_right_eq_sub, ← mulVec_sub]
  exact Matrix.linfty_opNorm_mulVec A (u - v)

/-- The scalar case (1.14), p. 17: `|a| < 1` gives `u* = b/(1 − a) = ∑ₖ aᵏ b`. -/
theorem scalar_neumann {a b : ℝ} (ha : |a| < 1) :
    ∑' k : ℕ, a ^ k * b = b / (1 - a) ∧ b / (1 - a) = a * (b / (1 - a)) + b := by
  have h1 : (1 : ℝ) - a ≠ 0 := by
    have := abs_lt.1 ha
    linarith
  constructor
  · rw [tsum_mul_right, tsum_geometric_of_abs_lt_one ha]
    ring
  · field_simp
    ring

end SargentStachurski.JobSearch
