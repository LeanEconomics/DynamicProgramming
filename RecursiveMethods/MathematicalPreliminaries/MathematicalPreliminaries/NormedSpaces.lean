/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MathematicalPreliminaries.MetricSpaces
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vector spaces and normed vector spaces

SLP §3.1, pp. 43–46, Exercises 3.2 and 3.4.

A set of functions or vectors "with the usual operations" is a vector space exactly when it is a
subspace of the ambient space: it contains `0` and is closed under addition and scalar
multiplication (`IsSubspace`).

* Ex 3.2a–d: `isSubspace_univ`, `isSubspace_line`, `isSubspace_continuousOn`; Ex 3.2e–g:
  `not_isSubspace_circle`, `not_isSubspace_int`, `not_isSubspace_nonneg`.
* `IsNorm` (p. 45) and `IsNorm.isMetric` (p. 46).
* Ex 3.4a–f: `isNorm_euclid`, `isNorm_max`, `isNorm_sum`, `isNorm_ellInf`, `isNorm_sup`,
  `isNorm_l1`.
-/

open Set Finset

namespace StokeyLucasPrescott.MathematicalPreliminaries

/-- A subset of a vector space is a vector space under the inherited operations. -/
def IsSubspace {E : Type*} [AddCommGroup E] [Module ℝ E] (V : Set E) : Prop :=
  (0 : E) ∈ V ∧ (∀ x ∈ V, ∀ y ∈ V, x + y ∈ V) ∧ ∀ (r : ℝ), ∀ x ∈ V, r • x ∈ V

/-- **Ex 3.2a, 3.2c.** `ℝ^l` and the space of all real sequences. -/
theorem isSubspace_univ {E : Type*} [AddCommGroup E] [Module ℝ E] : IsSubspace (Set.univ : Set E) :=
  ⟨trivial, fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩

/-- **Ex 3.2b.** The line `{αz : α ∈ ℝ}` through `z ∈ ℝ²`. -/
theorem isSubspace_line (z : ℝ × ℝ) : IsSubspace {x : ℝ × ℝ | ∃ α : ℝ, x = α • z} :=
  ⟨⟨0, by simp⟩, fun _ ⟨α, hx⟩ _ ⟨β, hy⟩ => ⟨α + β, by rw [hx, hy, add_smul]⟩,
    fun r _ ⟨α, hx⟩ => ⟨r * α, by rw [hx, smul_smul]⟩⟩

/-- **Ex 3.2d.** The continuous functions on `[a, b]`. -/
theorem isSubspace_continuousOn (a b : ℝ) :
    IsSubspace {f : ℝ → ℝ | ContinuousOn f (Icc a b)} :=
  ⟨continuousOn_const, fun _ hf _ hg => hf.add hg, fun _ _ hf => continuousOn_const.mul hf⟩

/-- **Ex 3.2e.** The unit circle in `ℝ²` is not a vector space: it does not contain `0`. -/
theorem not_isSubspace_circle : ¬ IsSubspace {x : ℝ × ℝ | x.1 ^ 2 + x.2 ^ 2 = 1} := by
  rintro ⟨h0, -, -⟩
  simp at h0

/-- **Ex 3.2f.** The integers are not a real vector space: `½ · 1 ∉ ℤ`. -/
theorem not_isSubspace_int : ¬ IsSubspace (Set.range (Int.cast : ℤ → ℝ)) := by
  rintro ⟨-, -, hs⟩
  obtain ⟨n, hn⟩ := hs (1 / 2) 1 ⟨1, by simp⟩
  have h1 : (2 : ℝ) * n = 1 := by rw [hn]; norm_num
  have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast h1
  omega

/-- **Ex 3.2g.** The nonnegative functions on `[a, b]` (`a ≤ b`) are not a vector space:
`(−1) · 1` is negative. -/
theorem not_isSubspace_nonneg {a b : ℝ} (hab : a ≤ b) :
    ¬ IsSubspace {f : ℝ → ℝ | ∀ t ∈ Icc a b, 0 ≤ f t} := by
  rintro ⟨-, -, hs⟩
  have := hs (-1) (fun _ => 1) (fun _ _ => zero_le_one) a ⟨le_rfl, hab⟩
  simp at this
  linarith

/-- A norm in the sense of SLP p. 45. -/
structure IsNorm {E : Type*} [AddCommGroup E] [Module ℝ E] (N : E → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ N x
  eq_zero : ∀ x, N x = 0 ↔ x = 0
  smul : ∀ (r : ℝ) x, N (r • x) = |r| * N x
  triangle : ∀ x y, N (x + y) ≤ N x + N y

/-- **A norm gives a metric** `ρ(x, y) = ‖x − y‖` (SLP p. 46). -/
theorem IsNorm.isMetric {E : Type*} [AddCommGroup E] [Module ℝ E] {N : E → ℝ} (hN : IsNorm N) :
    IsMetric fun x y => N (x - y) where
  nonneg _ _ := hN.nonneg _
  eq_zero x y := by rw [hN.eq_zero, sub_eq_zero]
  symm x y := by
    rw [show y - x = (-1 : ℝ) • (x - y) by simp [neg_sub], hN.smul]
    simp
  triangle x y z := by
    have := hN.triangle (x - y) (y - z)
    rwa [sub_add_sub_cancel] at this

/-- A normed space's own norm is a norm in the book's sense. -/
theorem isNorm_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsNorm fun x : E => ‖x‖ where
  nonneg _ := norm_nonneg _
  eq_zero _ := norm_eq_zero
  smul r x := by rw [norm_smul, Real.norm_eq_abs]
  triangle _ _ := norm_add_le _ _

/-- **Ex 3.4a.** The Euclidean norm `‖x‖ = (∑ xᵢ²)^{1/2}` on `ℝ^l`. -/
theorem isNorm_euclid (l : ℕ) : IsNorm fun x : Fin l → ℝ => Real.sqrt (∑ i, x i ^ 2) := by
  have h : ∀ x : Fin l → ℝ,
      Real.sqrt (∑ i, x i ^ 2) = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin l))‖ := fun x => by
      rw [EuclideanSpace.norm_eq]
      simp [Real.norm_eq_abs, sq_abs]
  simp_rw [h]
  exact ⟨fun _ => norm_nonneg _, fun x => by
      rw [norm_eq_zero]
      exact ⟨fun h0 => WithLp.toLp_injective 2 (by rw [h0, WithLp.toLp_zero]), fun h0 => by
        rw [h0, WithLp.toLp_zero]⟩,
    fun r x => by rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs],
    fun x y => by rw [WithLp.toLp_add]; exact norm_add_le _ _⟩

/-- **Ex 3.4b.** The max norm `‖x‖ = maxᵢ |xᵢ|` on `ℝ^l`: Mathlib's norm on `Fin l → ℝ` is this
maximum (`abs_le_max_norm`, `max_norm_le`). -/
theorem isNorm_max (l : ℕ) : IsNorm fun x : Fin l → ℝ => ‖x‖ := isNorm_norm

theorem abs_le_max_norm {l : ℕ} (x : Fin l → ℝ) (i : Fin l) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_le_pi_norm x i

theorem max_norm_le {l : ℕ} (x : Fin l → ℝ) {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, |x i| ≤ M) :
    ‖x‖ ≤ M :=
  (pi_norm_le_iff_of_nonneg hM).2 fun i => by rw [Real.norm_eq_abs]; exact h i

/-- **Ex 3.4c.** The sum norm `‖x‖ = ∑ᵢ |xᵢ|` on `ℝ^l`. -/
theorem isNorm_sum (l : ℕ) : IsNorm fun x : Fin l → ℝ => ∑ i, |x i| where
  nonneg _ := sum_nonneg fun _ _ => abs_nonneg _
  eq_zero x := by
    constructor
    · intro h
      funext i
      have := (sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 h i (mem_univ i)
      simpa using this
    · rintro rfl
      simp
  smul r x := by simp [abs_mul, mul_sum]
  triangle x y := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun i _ => abs_add_le _ _

/-- The bounded real sequences, `ℓ∞`. -/
def ellInf : Submodule ℝ (ℕ → ℝ) where
  carrier := {x | BddAbove (Set.range fun k => |x k|)}
  add_mem' {x y} hx hy := by
    obtain ⟨M, hM⟩ := hx
    obtain ⟨M', hM'⟩ := hy
    refine ⟨M + M', ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (abs_add_le _ _).trans (add_le_add (hM ⟨k, rfl⟩) (hM' ⟨k, rfl⟩))
  zero_mem' := ⟨0, by rintro _ ⟨k, rfl⟩; simp⟩
  smul_mem' r x hx := by
    obtain ⟨M, hM⟩ := hx
    refine ⟨|r| * M, ?_⟩
    rintro _ ⟨k, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM ⟨k, rfl⟩) (abs_nonneg r)

/-- The sup norm `supₖ |xₖ|` on `ℓ∞`. -/
noncomputable def supNorm (x : ellInf) : ℝ := ⨆ k, |(x : ℕ → ℝ) k|

theorem abs_le_supNorm (x : ellInf) (k : ℕ) : |(x : ℕ → ℝ) k| ≤ supNorm x :=
  le_ciSup x.2 k

theorem supNorm_le (x : ellInf) {M : ℝ} (h : ∀ k, |(x : ℕ → ℝ) k| ≤ M) : supNorm x ≤ M :=
  ciSup_le h

/-- **Ex 3.4d.** `ℓ∞` with `‖x‖ = supₖ |xₖ|`. -/
theorem isNorm_ellInf : IsNorm supNorm where
  nonneg x := (abs_nonneg _).trans (abs_le_supNorm x 0)
  eq_zero x := by
    constructor
    · intro h
      ext k
      have := abs_le_supNorm x k
      rw [h] at this
      simpa using abs_nonpos_iff.1 this
    · rintro rfl
      exact le_antisymm (supNorm_le _ fun k => by simp) ((abs_nonneg _).trans (abs_le_supNorm _ 0))
  smul r x := by
    unfold supNorm
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact (Real.mul_iSup_of_nonneg (abs_nonneg r) _).symm
  triangle x y := supNorm_le _ fun k => by
    simp only [Submodule.coe_add, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (abs_le_supNorm x k) (abs_le_supNorm y k))

/-- **Ex 3.4e.** `C[a, b]` with `‖x‖ = max |x(t)|`; Mathlib's norm is this maximum
(`ContinuousMap.norm_coe_le_norm`, `ContinuousMap.norm_le`). -/
theorem isNorm_sup (a b : ℝ) : IsNorm fun x : C(Icc a b, ℝ) => ‖x‖ := isNorm_norm

/-- **Ex 3.4f.** `C[a, b]` with `‖x‖ = ∫ₐᵇ |x(t)| dt`, for `a < b`. -/
theorem isNorm_l1 {a b : ℝ} (hab : a < b) : IsNorm (l1 hab.le) where
  nonneg := l1_nonneg _
  eq_zero := l1_eq_zero_iff hab
  smul := l1_smul _
  triangle := l1_add_le _

end StokeyLucasPrescott.MathematicalPreliminaries
