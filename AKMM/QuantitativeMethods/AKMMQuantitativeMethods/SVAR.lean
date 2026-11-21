/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFMoments
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Interval.Finset.Fin

/-!
# Structural VARs: the reduced form and the identification problem

AKMM, §8.4, (8.4) and (8.7), pp. 222–223, with footnote 4.

The structural system (8.4) is `B₀Yₜ = B₁Yₜ₋₁ + ⋯ + B_JYₜ₋J + εₜ` with `Var(εₜ) = I`. We prove:

* premultiplying by `B₀⁻¹` gives the reduced form (8.7) `Yₜ = A₁Yₜ₋₁ + ⋯ + uₜ` with
  `A_j = B₀⁻¹B_j`, `uₜ = B₀⁻¹εₜ`, and conversely (`eq_8_7`, `eq_8_7_process`);
* the normalisation `Var(εₜ) = I` is without loss of generality (`sv_normalisation`);
* `Var(uₜ) = B₀⁻¹B₀⁻¹'` (`sv_var_u`);
* **non-identification by rotations**: for an orthogonal `F` the rotated model `b F'`, `Fε` has
  the same reduced-form residuals and `bF'(bF')' = bb'` (`sv_rotation`, `sv_rotation_shocks`);
  conversely every `b'` with `b'b'' = bb'` is `bF'` for an orthogonal `F` when `b` is invertible
  (`sv_rotation_converse`); so `Var(u)` does not determine `B₀⁻¹` (`sv_not_identified`);
* **the restriction count** (footnote 4): the symmetric `n × n` matrices form a space of
  dimension `n(n+1)/2` (`sv_finrank_symm`), the unrestricted `B₀` has `n²` entries, and the
  difference is `n(n−1)/2`, `= 1` for `n = 2` (`sv_restriction_count`).
-/

namespace AKMM.QuantitativeMethods

open MeasureTheory Matrix Miao.PartialInformation

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **(8.7)** (AKMM, p. 223): for invertible `B₀`, the structural equation
`B₀y = Σⱼ Bⱼxⱼ + ε` (`xⱼ` the lags) holds iff the reduced form
`y = Σⱼ (B₀⁻¹Bⱼ)xⱼ + B₀⁻¹ε` holds. -/
theorem eq_8_7 {J : Type*} [Fintype J] {B0 : Matrix n n ℝ} (hB0 : IsUnit B0.det)
    (B : J → Matrix n n ℝ) (y ε : n → ℝ) (x : J → n → ℝ) :
    B0 *ᵥ y = ∑ j, B j *ᵥ x j + ε ↔ y = ∑ j, (B0⁻¹ * B j) *ᵥ x j + B0⁻¹ *ᵥ ε := by
  have hl : B0⁻¹ * B0 = 1 := nonsing_inv_mul B0 hB0
  have hr : B0 * B0⁻¹ = 1 := mul_nonsing_inv B0 hB0
  constructor
  · intro h
    have := congrArg (fun v => B0⁻¹ *ᵥ v) h
    simp only [mulVec_mulVec, hl, one_mulVec, mulVec_add, mulVec_sum] at this
    exact this
  · intro h
    rw [h, mulVec_add, mulVec_sum, mulVec_mulVec, hr, one_mulVec]
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hr, Matrix.one_mul]

/-- **(8.4) ⟹ (8.7) along a path** (AKMM, pp. 222–223): if
`B₀Y_{t+J} = Σ_{j<J} B_{j+1}Y_{t+J−1−j} + ε_{t+J}` for all `t`, then
`Y_{t+J} = Σ_j A_{j+1}Y_{t+J−1−j} + u_{t+J}` with `A = B₀⁻¹B`, `u = B₀⁻¹ε`, and conversely. -/
theorem eq_8_7_process {J : ℕ} {B0 : Matrix n n ℝ} (hB0 : IsUnit B0.det)
    (B : Fin J → Matrix n n ℝ) (Y ε : ℕ → n → ℝ) :
    (∀ t, B0 *ᵥ Y (t + J) = ∑ j : Fin J, B j *ᵥ Y (t + J - 1 - j) + ε (t + J)) ↔
      ∀ t, Y (t + J) = ∑ j : Fin J, (B0⁻¹ * B j) *ᵥ Y (t + J - 1 - j) + B0⁻¹ *ᵥ ε (t + J) :=
  forall_congr' fun t => eq_8_7 hB0 B (Y (t + J)) (ε (t + J)) fun j => Y (t + J - 1 - j)

/-- **`Var(uₜ) = B₀⁻¹B₀⁻¹'`** (AKMM, p. 223): if `Var(εₜ) = I` then the reduced-form residual
`uₜ = B₀⁻¹εₜ` has second-moment matrix `B₀⁻¹(B₀⁻¹)'`. -/
theorem sv_var_u {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    (B0 : Matrix n n ℝ) :
    var_mom μ (kf_app B0⁻¹ ε) (kf_app B0⁻¹ ε) = B0⁻¹ * (B0⁻¹)ᵀ := by
  rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hI, Matrix.one_mul]

/-- **Rotations** (AKMM, p. 223): if `bb' = Var(u)` and `F'F = I`, then
`(bF')(bF')' = Var(u)`. -/
theorem sv_rotation {b S F : Matrix n n ℝ} (hb : b * bᵀ = S)
    (hF : F ∈ Matrix.orthogonalGroup n ℝ) : (b * Fᵀ) * (b * Fᵀ)ᵀ = S := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hF
  rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Fᵀ, hF,
    Matrix.one_mul, hb]

/-- **Observational equivalence** (AKMM, p. 223): rotating the structural shocks, `ε' = Fε`
with `F` orthogonal, gives shocks with `Var(ε') = I` and the impact matrix `bF'` produces the same
reduced-form residuals: `(bF')ε' = bε`. -/
theorem sv_rotation_shocks {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) (hI : var_mom μ ε ε = 1)
    {b F : Matrix n n ℝ} (hF : F ∈ Matrix.orthogonalGroup n ℝ) :
    var_mom μ (kf_app F ε) (kf_app F ε) = 1 ∧
      kf_app (b * Fᵀ) (kf_app F ε) = kf_app b ε := by
  have hF' := hF
  rw [Matrix.mem_orthogonalGroup_iff] at hF
  rw [Matrix.mem_orthogonalGroup_iff'] at hF'
  refine ⟨?_, ?_⟩
  · rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hI, Matrix.one_mul, hF]
  · funext ω
    simp only [kf_app, mulVec_mulVec, Matrix.mul_assoc, hF', Matrix.mul_one]

/-- **Every observationally equivalent impact matrix is a rotation** (AKMM, p. 223): if `b` is
invertible and `b'b'' = bb'`, then `b' = bF'` for some orthogonal `F`. -/
theorem sv_rotation_converse {b b' : Matrix n n ℝ} (hb : IsUnit b.det)
    (h : b' * b'ᵀ = b * bᵀ) : ∃ F ∈ Matrix.orthogonalGroup n ℝ, b' = b * Fᵀ := by
  refine ⟨(b⁻¹ * b')ᵀ, ?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff', transpose_transpose, transpose_mul]
    calc b⁻¹ * b' * (b'ᵀ * b⁻¹ᵀ) = b⁻¹ * (b' * b'ᵀ) * b⁻¹ᵀ := by simp only [Matrix.mul_assoc]
      _ = (b⁻¹ * b) * (b⁻¹ * b)ᵀ := by
          rw [h, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul b hb, transpose_one, Matrix.one_mul]
  · rw [transpose_transpose, ← Matrix.mul_assoc, mul_nonsing_inv b hb, Matrix.one_mul]

/-- **`Var(u)` does not identify `B₀⁻¹`** (AKMM, p. 223): the identity and the permutation
`[[0, 1], [1, 0]]` are different impact matrices with the same `bb' = I`. -/
theorem sv_not_identified :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) * (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ =
        !![(0 : ℝ), 1; 1, 0] * (!![(0 : ℝ), 1; 1, 0])ᵀ ∧
      (1 : Matrix (Fin 2) (Fin 2) ℝ) ≠ !![(0 : ℝ), 1; 1, 0] := by
  refine ⟨?_, fun h => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have := congrFun (congrFun h 0) 0
    simp at this

/-- The symmetric `n × n` matrices, `M' = M`. -/
def sv_symm (k : ℕ) : Submodule ℝ (Matrix (Fin k) (Fin k) ℝ) where
  carrier := {M | Mᵀ = M}
  add_mem' := by
    intro a b ha hb
    change (a + b)ᵀ = a + b
    rw [transpose_add]
    exact congrArg₂ (· + ·) ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c M hM
    change (c • M)ᵀ = c • M
    rw [transpose_smul]
    exact congrArg (c • ·) hM

/-- The index set `{(i, j) : i ≤ j}` of the distinct entries of a symmetric matrix. -/
abbrev sv_upper (k : ℕ) := {p : Fin k × Fin k // p.1 ≤ p.2}

/-- `#{(i, j) : i ≤ j} = k(k+1)/2`, as `2·# = k(k+1)`. -/
theorem sv_card_upper (k : ℕ) : 2 * Fintype.card (sv_upper k) = k * (k + 1) := by
  rw [Fintype.card_subtype]
  have hc : (Finset.univ.filter fun p : Fin k × Fin k => p.1 ≤ p.2).card =
      ∑ i : Fin k, (k - i) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun j : Fin k => i ≤ j) = Finset.Ici i := by
      ext j; simp
    rw [this, Fin.card_Ici]
  have h2 : ∑ i ∈ Finset.range k, (k - i) = ∑ i ∈ Finset.range k, (i + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    omega
  rw [hc, Fin.sum_univ_eq_sum_range (fun i => k - i) k, h2, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have h3 := Finset.sum_range_id_mul_two k
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel] at h3
    nlinarith [h3]

/-- The linear map reading off the entries `M_{ij}`, `i ≤ j`. -/
def sv_upperMap (k : ℕ) : sv_symm k →ₗ[ℝ] (sv_upper k → ℝ) where
  toFun M p := (M : Matrix (Fin k) (Fin k) ℝ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sv_upperMap_bijective (k : ℕ) : Function.Bijective (sv_upperMap k) := by
  constructor
  · intro M N h
    apply Subtype.ext
    ext i j
    rcases le_total i j with hij | hij
    · exact congrFun h ⟨(i, j), hij⟩
    · have h1 := congrFun h ⟨(j, i), hij⟩
      simp only [sv_upperMap, LinearMap.coe_mk] at h1
      have hM : (M : Matrix (Fin k) (Fin k) ℝ)ᵀ = M := M.2
      have hN : (N : Matrix (Fin k) (Fin k) ℝ)ᵀ = N := N.2
      rw [← hM, ← hN, transpose_apply, transpose_apply]
      exact h1
  · intro f
    refine ⟨⟨Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else
      f ⟨(j, i), (lt_of_not_ge h).le⟩, ?_⟩, ?_⟩
    · ext i j
      simp only [transpose_apply, of_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · simp [not_le.2 hij, hij.le]
      · rfl
      · simp [not_le.2 hij, hij.le]
    · funext p
      change (if h : p.1.1 ≤ p.1.2 then f ⟨(p.1.1, p.1.2), h⟩ else _) = f p
      rw [dite_eq_left_of_eq_true (eq_true p.2)]

/-- **The distinct entries of `Var(u)`** (AKMM, p. 223 and footnote 4): the symmetric `n × n`
matrices form a space of dimension `n(n+1)/2` (here `2·dim = n(n+1)`). -/
theorem sv_finrank_symm (k : ℕ) : 2 * Module.finrank ℝ (sv_symm k) = k * (k + 1) := by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ (sv_upperMap_bijective k)),
    Module.finrank_fintype_fun_eq_card, sv_card_upper]

/-- **The restriction count** (AKMM, p. 223, footnote 4): `B₀` has `n²` unknowns, `Var(u)`
supplies `n(n+1)/2` equations, so `n² − n(n+1)/2 = n(n−1)/2` restrictions are needed: one for
`n = 2`. -/
theorem sv_restriction_count (k : ℕ) :
    Module.finrank ℝ (Matrix (Fin k) (Fin k) ℝ) = k ^ 2 ∧
      2 * (k ^ 2 - Module.finrank ℝ (sv_symm k)) = k * (k - 1) ∧
      2 ^ 2 - Module.finrank ℝ (sv_symm 2) = 1 := by
  have h := sv_finrank_symm k
  have h2 := sv_finrank_symm 2
  refine ⟨by simp [Module.finrank_matrix, sq], ?_, by norm_num at h2 ⊢; omega⟩
  have hle : Module.finrank ℝ (sv_symm k) ≤ k ^ 2 := by nlinarith
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]
    zify [hle] at h ⊢
    linarith

/-- **The normalisation `Var(εₜ) = I`** (AKMM, p. 222): "it is without loss of generality to
assume that the covariance matrix of `εₜ` is the identity as we can rescale the `B_j`'s". If the
structural shocks are uncorrelated with variances `dᵢ > 0`, then with `S = diag(1/√dᵢ)` the
rescaled shocks `Sε` have `Var(Sε) = I`, and `B₀y = Σⱼ Bⱼxⱼ + ε` iff
`(SB₀)y = Σⱼ (SBⱼ)xⱼ + Sε`. -/
theorem sv_normalisation {ε : Ω → n → ℝ} (hε : kf_L2 μ ε) {d : n → ℝ} (hd : ∀ i, 0 < d i)
    (hD : var_mom μ ε ε = diagonal d) {J : Type*} [Fintype J] (B0 : Matrix n n ℝ)
    (B : J → Matrix n n ℝ) (y e : n → ℝ) (x : J → n → ℝ) :
    var_mom μ (kf_app (diagonal fun i => 1 / Real.sqrt (d i)) ε)
        (kf_app (diagonal fun i => 1 / Real.sqrt (d i)) ε) = 1 ∧
      (B0 *ᵥ y = ∑ j, B j *ᵥ x j + e ↔
        ((diagonal fun i => 1 / Real.sqrt (d i)) * B0) *ᵥ y =
          ∑ j, ((diagonal fun i => 1 / Real.sqrt (d i)) * B j) *ᵥ x j +
            (diagonal fun i => 1 / Real.sqrt (d i)) *ᵥ e) := by
  set S : Matrix n n ℝ := diagonal fun i => 1 / Real.sqrt (d i) with hS
  have hSinv : IsUnit S.det := by
    rw [hS, det_diagonal]
    exact (Finset.prod_pos fun i _ => by
      have := Real.sqrt_pos.2 (hd i); positivity).ne'.isUnit
  refine ⟨?_, ?_⟩
  · rw [kf_mom_app_left hε (kf_L2_app hε _), kf_mom_app_right hε hε, hD, hS,
      diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    have h1 := Real.sqrt_pos.2 (hd i)
    have h2 := Real.mul_self_sqrt (hd i).le
    field_simp
    linarith
  · constructor
    · intro h
      rw [← mulVec_mulVec, h, mulVec_add, mulVec_sum]
      simp only [mulVec_mulVec]
    · intro h
      have hinj : Function.Injective (S *ᵥ ·) := Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det S).2 hSinv)
      apply hinj
      simp only
      rw [mulVec_mulVec, h, mulVec_add, mulVec_sum]
      simp only [mulVec_mulVec]

end AKMM.QuantitativeMethods
