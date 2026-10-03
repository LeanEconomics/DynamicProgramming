/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Constructions

/-!
# Norms on `ℝⁿ` and on matrices

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.1.2–§1.2.1.4
(pp. 13–17): the ℓ¹, weighted ℓ¹ and supremum norms on `ℝⁿ`, the four norm
axioms, equivalence of norms, pointwise versus norm convergence, and matrix
norms with the submultiplicative property.

A norm on `ℝⁿ` is a function `N : (Fin n → ℝ) → ℝ` with the four properties of
p. 13: nonnegativity, positive definiteness, absolute homogeneity and the
triangle inequality. The exercises ask for the axioms to be checked for the
explicit functions, so `IsNorm` packages the four axioms and each exercise
proves them for its function. Mathlib's own normed-group instance on
`Fin n → ℝ` is the supremum norm, and the lemmas of §1.2.1.3 and §1.2.4.2 that
the book states in terms of "any norm" are proved for it.
-/

open Finset

namespace SargentStachurski.JobSearch

/-- The four norm axioms of p. 13 for a function `N` on a real vector space. -/
structure IsNorm {V : Type*} [AddCommGroup V] [Module ℝ V] (N : V → ℝ) : Prop where
  nonneg : ∀ u, 0 ≤ N u
  eq_zero_iff : ∀ u, N u = 0 ↔ u = 0
  smul : ∀ (α : ℝ) u, N (α • u) = |α| * N u
  add_le : ∀ u v, N (u + v) ≤ N u + N v

variable {n : ℕ}

/-- The ℓ¹ norm (1.9), p. 13: `‖u‖₁ = ∑ᵢ |uᵢ|`. -/
def l1Norm (u : Fin n → ℝ) : ℝ := ∑ i, |u i|

/-- The weighted ℓ¹ norm of Exercise 1.2.3, p. 14: `‖u‖_{1,p} = ∑ᵢ |uᵢ| pᵢ`. -/
def weightedL1Norm (p : Fin n → ℝ) (u : Fin n → ℝ) : ℝ := ∑ i, |u i| * p i

/-- The supremum norm of Exercise 1.2.4, p. 14: `‖u‖_∞ = maxᵢ |uᵢ|`. -/
def supNorm (u : Fin n → ℝ) : ℝ := ‖u‖

/-- The ℓ⁰ "norm" of Exercise 1.2.5, p. 14: the number of nonzero coordinates. -/
noncomputable def l0Norm (u : Fin n → ℝ) : ℝ := ∑ i, if u i ≠ 0 then 1 else 0

/-- Exercise 1.2.2 (p. 14): the ℓ¹ norm is a norm. -/
theorem isNorm_l1Norm : IsNorm (l1Norm (n := n)) where
  nonneg u := sum_nonneg fun i _ => abs_nonneg (u i)
  eq_zero_iff u := by
    constructor
    · intro h
      have h0 := (sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (u i)).1 h
      funext i
      exact abs_eq_zero.1 (h0 i (mem_univ i))
    · rintro rfl
      simp [l1Norm]
  smul α u := by
    simp only [l1Norm, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum]
  add_le u v := by
    simp only [l1Norm, Pi.add_apply, ← sum_add_distrib]
    exact sum_le_sum fun i _ => abs_add_le (u i) (v i)

/-- Exercise 1.2.3 (p. 14): with strictly positive weights `p`, the weighted ℓ¹ function is a
norm. The book also asks that `∑ pᵢ = 1`; that normalisation is not needed for the axioms. -/
theorem isNorm_weightedL1Norm {p : Fin n → ℝ} (hp : ∀ i, 0 < p i) :
    IsNorm (weightedL1Norm p) where
  nonneg u := sum_nonneg fun i _ => mul_nonneg (abs_nonneg (u i)) (hp i).le
  eq_zero_iff u := by
    constructor
    · intro h
      have h0 := (sum_eq_zero_iff_of_nonneg
        fun i _ => mul_nonneg (abs_nonneg (u i)) (hp i).le).1 h
      funext i
      have := h0 i (mem_univ i)
      rcases mul_eq_zero.1 this with h1 | h1
      · exact abs_eq_zero.1 h1
      · exact absurd h1 (hp i).ne'
    · rintro rfl
      simp [weightedL1Norm]
  smul α u := by
    simp only [weightedL1Norm, Pi.smul_apply, smul_eq_mul, abs_mul, mul_sum, mul_assoc]
  add_le u v := by
    simp only [weightedL1Norm, Pi.add_apply, ← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (abs_add_le (u i) (v i)) (hp i).le

/-- Exercise 1.2.4 (p. 14): the supremum norm is a norm. It is Mathlib's norm on `Fin n → ℝ`,
so the axioms are Mathlib's. -/
theorem isNorm_supNorm : IsNorm (supNorm (n := n)) where
  nonneg u := norm_nonneg u
  eq_zero_iff u := norm_eq_zero
  smul α u := by simp only [supNorm, norm_smul, Real.norm_eq_abs]
  add_le u v := norm_add_le u v

/-- The supremum norm is the maximum of the coordinate absolute values: `‖u‖ ≤ r ↔ ∀ i, |uᵢ| ≤ r`
for `r ≥ 0` (Exercise 1.2.4, p. 14). -/
theorem supNorm_le_iff {u : Fin n → ℝ} {r : ℝ} (hr : 0 ≤ r) : supNorm u ≤ r ↔ ∀ i, |u i| ≤ r := by
  simp only [supNorm, pi_norm_le_iff_of_nonneg hr, Real.norm_eq_abs]

/-- Each coordinate is bounded by the supremum norm, `|uᵢ| ≤ ‖u‖_∞`. -/
theorem abs_le_supNorm (u : Fin n → ℝ) (i : Fin n) : |u i| ≤ supNorm u := by
  have := norm_le_pi_norm u i
  simpa [supNorm, Real.norm_eq_abs] using this

/-- Exercise 1.2.5 (p. 14): the ℓ⁰ function is not a norm on `ℝⁿ` for `n ≥ 1`, because it fails
absolute homogeneity: `‖2u‖₀ = ‖u‖₀ ≠ 2‖u‖₀` for `u ≠ 0`. -/
theorem not_isNorm_l0Norm (hn : 0 < n) : ¬ IsNorm (l0Norm (n := n)) := by
  intro h
  set u : Fin n → ℝ := fun _ => 1 with hu
  have h1 : l0Norm u = n := by simp [l0Norm, hu]
  have h2 : l0Norm ((2 : ℝ) • u) = n := by simp [l0Norm, hu]
  have h3 := h.smul 2 u
  rw [h2, h1] at h3
  have : (n : ℝ) > 0 := by exact_mod_cast hn
  norm_num at h3
  linarith

/-- Two norms are equivalent, (1.11) p. 15: `M‖u‖ₐ ≤ ‖u‖_b ≤ N‖u‖ₐ` for some `M, N > 0`. -/
def NormEquiv {V : Type*} (Na Nb : V → ℝ) : Prop :=
  ∃ M N : ℝ, 0 < M ∧ 0 < N ∧ ∀ u, M * Na u ≤ Nb u ∧ Nb u ≤ N * Na u

/-- Exercise 1.2.6 (p. 15): equivalence of norms is reflexive. -/
theorem normEquiv_refl {V : Type*} (N : V → ℝ) : NormEquiv N N :=
  ⟨1, 1, one_pos, one_pos, fun u => ⟨by simp, by simp⟩⟩

/-- Exercise 1.2.6 (p. 15): equivalence of norms is symmetric. -/
theorem normEquiv_symm {V : Type*} {Na Nb : V → ℝ} (h : NormEquiv Na Nb) : NormEquiv Nb Na := by
  obtain ⟨M, N, hM, hN, h⟩ := h
  refine ⟨N⁻¹, M⁻¹, inv_pos.2 hN, inv_pos.2 hM, fun u => ⟨?_, ?_⟩⟩
  · rw [inv_mul_le_iff₀ hN]
    exact (h u).2
  · rw [le_inv_mul_iff₀ hM]
    exact (h u).1

/-- Exercise 1.2.6 (p. 15): equivalence of norms is transitive. -/
theorem normEquiv_trans {V : Type*} {Na Nb Nc : V → ℝ} (hab : NormEquiv Na Nb)
    (hbc : NormEquiv Nb Nc) : NormEquiv Na Nc := by
  obtain ⟨M₁, N₁, hM₁, hN₁, h₁⟩ := hab
  obtain ⟨M₂, N₂, hM₂, hN₂, h₂⟩ := hbc
  refine ⟨M₂ * M₁, N₂ * N₁, mul_pos hM₂ hM₁, mul_pos hN₂ hN₁, fun u => ⟨?_, ?_⟩⟩
  · calc M₂ * M₁ * Na u = M₂ * (M₁ * Na u) := by ring
      _ ≤ M₂ * Nb u := mul_le_mul_of_nonneg_left (h₁ u).1 hM₂.le
      _ ≤ Nc u := (h₂ u).1
  · calc Nc u ≤ N₂ * Nb u := (h₂ u).2
      _ ≤ N₂ * (N₁ * Na u) := mul_le_mul_of_nonneg_left (h₁ u).2 hN₂.le
      _ = N₂ * N₁ * Na u := by ring

/-- Exercise 1.2.6 (p. 15), in Mathlib's packaging: `NormEquiv` is an equivalence relation. -/
theorem normEquiv_equivalence (V : Type*) : Equivalence (NormEquiv (V := V)) :=
  ⟨normEquiv_refl, normEquiv_symm, normEquiv_trans⟩

/-- Exercise 1.2.7 (p. 15): if the norms are equivalent, `‖uₘ − u‖ₐ → 0` implies
`‖uₘ − u‖_b → 0`. -/
theorem tendsto_of_normEquiv {V : Type*} [AddCommGroup V] {Na Nb : V → ℝ} (hNa : ∀ v, 0 ≤ Na v)
    (h : NormEquiv Na Nb) {u : ℕ → V} {u₀ : V}
    (hlim : Filter.Tendsto (fun m => Na (u m - u₀)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => Nb (u m - u₀)) Filter.atTop (nhds 0) := by
  obtain ⟨M, N, hM, hN, hMN⟩ := h
  refine squeeze_zero (fun m => ?_) (fun m => (hMN (u m - u₀)).2) ?_
  · exact le_trans (mul_nonneg hM.le (hNa _)) (hMN (u m - u₀)).1
  · simpa using hlim.const_mul N

/-- Exercise 1.2.8 (p. 15): pointwise convergence and norm convergence coincide in `ℝⁿ`, here for
the supremum norm (every other norm is equivalent to it). -/
theorem tendsto_pi_iff_tendsto_supNorm {u : ℕ → Fin n → ℝ} {u₀ : Fin n → ℝ} :
    (∀ i, Filter.Tendsto (fun m => u m i) Filter.atTop (nhds (u₀ i))) ↔
      Filter.Tendsto (fun m => supNorm (u m - u₀)) Filter.atTop (nhds 0) := by
  rw [← tendsto_pi_nhds, tendsto_iff_norm_sub_tendsto_zero]
  rfl

/-- The entrywise supremum norm of a matrix, (1.13) p. 16: `‖B‖_∞ = max_{i,j} |b_{ij}|`.
This is Mathlib's elementwise matrix norm. -/
noncomputable def matrixSupNorm (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  letI := Matrix.normedAddCommGroup (m := Fin n) (n := Fin n) (α := ℝ)
  ‖B‖

/-- The operator norm (1.12), p. 16, computed in the ℓ∞ vector norm: `‖B‖ = max_{‖u‖=1} ‖Bu‖`,
which for the supremum norm on `ℝⁿ` is the maximum absolute row sum. This is Mathlib's
`linfty` operator norm. -/
noncomputable def opNorm (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  ‖B‖

/-- Exercise 1.2.9 (p. 17), first part: the operator norm is submultiplicative. -/
theorem opNorm_mul (A B : Matrix (Fin n) (Fin n) ℝ) : opNorm (A * B) ≤ opNorm A * opNorm B :=
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  Matrix.linfty_opNorm_mul A B

/-- The operator norm bounds `‖Bu‖ ≤ ‖B‖ ‖u‖` in the supremum norm: the defining property of
(1.12), p. 16, used in Exercise 1.2.20. -/
theorem supNorm_mulVec_le (B : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    supNorm (B.mulVec u) ≤ opNorm B * supNorm u :=
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℝ)
  Matrix.linfty_opNorm_mulVec B u

/-- Exercise 1.2.9 (p. 17), second part: the entrywise supremum norm (1.13) is not
submultiplicative. For the `2 × 2` matrix of ones, `‖A‖_∞ = 1` but `‖A²‖_∞ = 2`. -/
theorem not_matrixSupNorm_submultiplicative :
    ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      matrixSupNorm (A * B) ≤ matrixSupNorm A * matrixSupNorm B := by
  let _ := Matrix.normedAddCommGroup (m := Fin 2) (n := Fin 2) (α := ℝ)
  intro h
  set A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun _ _ => 1 with hA
  have hA1 : matrixSupNorm A ≤ 1 := by
    change ‖A‖ ≤ 1
    rw [Matrix.norm_le_iff zero_le_one]
    intro i j
    simp [hA]
  have hAA : (2 : ℝ) ≤ matrixSupNorm (A * A) := by
    change (2 : ℝ) ≤ ‖A * A‖
    have h00 : (A * A) 0 0 = 2 := by
      simp [hA, Matrix.mul_apply]
    have := Matrix.norm_entry_le_entrywise_sup_norm (A * A) (i := 0) (j := 0)
    rw [h00, Real.norm_eq_abs, abs_two] at this
    exact this
  have hnn : 0 ≤ matrixSupNorm A := norm_nonneg A
  have := h A A
  nlinarith

end SargentStachurski.JobSearch
