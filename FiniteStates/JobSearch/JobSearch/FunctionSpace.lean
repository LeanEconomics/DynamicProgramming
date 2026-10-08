/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The finite-dimensional function space `ℝ^X`

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §1.2.4.2–§1.2.4.3
(pp. 30–32): Lemma 1.2.4 identifying `ℝ^X` with `ℝⁿ`, distributions on a
finite set, expectations as inner products, Exercise 1.2.27 on maximising a
linear functional over the simplex, and cumulative distribution functions and
quantiles on a finite subset of the line with Example 1.2.5 and Exercise 1.2.28.
-/

open Finset

namespace SargentStachurski.JobSearch

variable {X : Type*} [Fintype X]

/-- Lemma 1.2.4 (p. 30): `ℝ^X ∋ u ↔ (u(x₁), …, u(xₙ)) ∈ ℝⁿ` is a one-to-one correspondence,
indeed a linear equivalence, once `X` is enumerated as `x₁, …, xₙ`. -/
noncomputable def toVector : (X → ℝ) ≃ₗ[ℝ] (Fin (Fintype.card X) → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Fintype.equivFin X).symm

theorem toVector_apply (u : X → ℝ) (i : Fin (Fintype.card X)) :
    toVector u i = u ((Fintype.equivFin X).symm i) := rfl

theorem toVector_symm_apply (v : Fin (Fintype.card X) → ℝ) (x : X) :
    toVector.symm v x = v (Fintype.equivFin X x) := rfl

/-- The supremum norm extends to `ℝ^X` through the identification (p. 30): `‖u‖ = ‖(u(xᵢ))ᵢ‖`. -/
theorem norm_toVector (u : X → ℝ) : ‖toVector u‖ = ‖u‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [toVector_apply]
    exact norm_le_pi_norm u _
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro x
    have := norm_le_pi_norm (toVector u) (Fintype.equivFin X x)
    rwa [toVector_apply, Equiv.symm_apply_apply] at this

/-- A distribution on the finite set `X` (p. 31): `φ ∈ ℝ^X₊` with `∑ φ(x) = 1`. -/
structure IsDistribution (φ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ φ x
  sum_eq_one : ∑ x, φ x = 1

/-- `φ` is supported on `S` (p. 31): `φ(x) > 0` implies `x ∈ S`. -/
def SupportedOn (φ : X → ℝ) (S : Set X) : Prop := ∀ x, 0 < φ x → x ∈ S

/-- The expectation `E h(X) = ∑ h(x) φ(x) = ⟨h, φ⟩` (p. 31). -/
def expectation (h φ : X → ℝ) : ℝ := ∑ x, h x * φ x

/-- The point mass at `x₀` is a distribution. -/
theorem isDistribution_pointMass [DecidableEq X] (x₀ : X) :
    IsDistribution (fun x => if x = x₀ then (1 : ℝ) else 0) where
  nonneg x := by split_ifs <;> norm_num
  sum_eq_one := by simp

/-- The expectation under a point mass is the value at the point. -/
theorem expectation_pointMass [DecidableEq X] (h : X → ℝ) (x₀ : X) :
    expectation h (fun x => if x = x₀ then (1 : ℝ) else 0) = h x₀ := by
  simp [expectation]

/-- An expectation is bounded by a pointwise bound. -/
theorem expectation_le {h φ : X → ℝ} (hφ : IsDistribution φ) {M : ℝ} (hM : ∀ x, h x ≤ M) :
    expectation h φ ≤ M := by
  calc expectation h φ ≤ ∑ x, M * φ x :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hM x) (hφ.nonneg x)
    _ = M := by rw [← Finset.mul_sum, hφ.sum_eq_one, mul_one]

/-- A distribution supported where `h` attains its maximum `M` has expectation `M`. -/
theorem expectation_eq_of_supportedOn {h φ : X → ℝ} (hφ : IsDistribution φ) {M : ℝ}
    (hsupp : SupportedOn φ {x | h x = M}) : expectation h φ = M := by
  calc expectation h φ = ∑ x, M * φ x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rcases (hφ.nonneg x).lt_or_eq with hpos | hzero
        · rw [hsupp x hpos]
        · rw [← hzero]
          simp
    _ = M := by rw [← Finset.mul_sum, hφ.sum_eq_one, mul_one]

/-- A distribution not supported where `h` attains its maximum `M` has expectation below `M`. -/
theorem expectation_lt_of_not_supportedOn {h φ : X → ℝ} (hφ : IsDistribution φ) {M : ℝ}
    (hM : ∀ x, h x ≤ M) (hsupp : ¬ SupportedOn φ {x | h x = M}) : expectation h φ < M := by
  simp only [SupportedOn, Set.mem_ofPred_eq, not_forall] at hsupp
  obtain ⟨x₁, hpos, hne⟩ := hsupp
  have hlt : h x₁ < M := lt_of_le_of_ne (hM x₁) hne
  calc expectation h φ < ∑ x, M * φ x := by
        refine Finset.sum_lt_sum (fun x _ => mul_le_mul_of_nonneg_right (hM x) (hφ.nonneg x))
          ⟨x₁, Finset.mem_univ _, ?_⟩
        exact mul_lt_mul_of_pos_right hlt hpos
    _ = M := by rw [← Finset.mul_sum, hφ.sum_eq_one, mul_one]

/-- Exercise 1.2.27 (p. 31): `φ*` maximises `⟨h, φ⟩` over `D(X)` iff `φ*` is supported on
`argmax_x h(x)`. -/
theorem expectation_maximiser_iff [Nonempty X] (h : X → ℝ) {φ' : X → ℝ}
    (hφ' : IsDistribution φ') :
    (∀ φ, IsDistribution φ → expectation h φ ≤ expectation h φ') ↔
      SupportedOn φ' {x | ∀ y, h y ≤ h x} := by
  classical
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_max_image univ h Finset.univ_nonempty
  have hM : ∀ x, h x ≤ h x₀ := fun x => hx₀ x (Finset.mem_univ x)
  have hset : {x | ∀ y, h y ≤ h x} = {x | h x = h x₀} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact le_antisymm (hM x) (hx x₀)
    · intro hx y
      rw [hx]
      exact hM y
  rw [hset]
  constructor
  · intro hmax
    by_contra hnot
    have h1 := expectation_lt_of_not_supportedOn hφ' hM hnot
    have h2 := hmax _ (isDistribution_pointMass x₀)
    rw [expectation_pointMass] at h2
    linarith
  · intro hsupp φ hφ
    rw [expectation_eq_of_supportedOn hφ' hsupp]
    exact expectation_le hφ hM

/-! ### Distributions on a finite subset of the line, CDFs and quantiles (p. 32) -/

/-- A distribution on the finite set `X ⊂ ℝ`, as a function on `ℝ`: nonnegative on `X` and
summing to one over `X`. -/
structure IsDistributionOn (X : Finset ℝ) (φ : ℝ → ℝ) : Prop where
  nonneg : ∀ x ∈ X, 0 ≤ φ x
  sum_eq_one : ∑ x ∈ X, φ x = 1

/-- The cumulative distribution function `Φ(x) = P{X ≤ x} = ∑ 1{x' ≤ x} φ(x')` (p. 32). -/
noncomputable def cdf (X : Finset ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ := ∑ x' ∈ X, if x' ≤ x then φ x' else 0

/-- The CDF is monotone. -/
theorem cdf_mono {X : Finset ℝ} {φ : ℝ → ℝ} (hφ : IsDistributionOn X φ) : Monotone (cdf X φ) := by
  intro x y hxy
  refine Finset.sum_le_sum fun x' hx' => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hxy) h2
  · exact hφ.nonneg x' hx'
  · exact le_rfl

/-- The CDF equals one at the largest point of `X`. -/
theorem cdf_max' {X : Finset ℝ} {φ : ℝ → ℝ} (hX : X.Nonempty) (hφ : IsDistributionOn X φ) :
    cdf X φ (X.max' hX) = 1 := by
  rw [cdf, ← hφ.sum_eq_one]
  exact Finset.sum_congr rfl fun x hx => by simp [Finset.le_max' X x hx]

/-- The set `{x ∈ X : Φ(x) ≥ τ}` whose minimum is the `τ`-quantile. -/
noncomputable def quantileSet (X : Finset ℝ) (φ : ℝ → ℝ) (τ : ℝ) : Finset ℝ :=
  X.filter fun x => τ ≤ cdf X φ x

theorem quantileSet_subset (X : Finset ℝ) (φ : ℝ → ℝ) (τ : ℝ) : quantileSet X φ τ ⊆ X :=
  Finset.filter_subset _ _

theorem mem_quantileSet {X : Finset ℝ} {φ : ℝ → ℝ} {τ x : ℝ} :
    x ∈ quantileSet X φ τ ↔ x ∈ X ∧ τ ≤ cdf X φ x := Finset.mem_filter

/-- For `τ ≤ 1` the quantile set is nonempty: it contains the largest point of `X`. -/
theorem quantileSet_nonempty {X : Finset ℝ} {φ : ℝ → ℝ} (hX : X.Nonempty)
    (hφ : IsDistributionOn X φ) {τ : ℝ} (hτ : τ ≤ 1) : (quantileSet X φ τ).Nonempty :=
  ⟨X.max' hX, mem_quantileSet.2 ⟨Finset.max'_mem X hX, by rw [cdf_max' hX hφ]; exact hτ⟩⟩

/-- The `τ`-quantile (1.24), p. 32: `Q_τ X = min{x ∈ X : Φ(x) ≥ τ}`. -/
noncomputable def quantile (X : Finset ℝ) (φ : ℝ → ℝ) (τ : ℝ)
    (h : (quantileSet X φ τ).Nonempty) : ℝ :=
  (quantileSet X φ τ).min' h

/-- The quantile lies in `X` and its CDF value is at least `τ`. -/
theorem quantile_mem {X : Finset ℝ} {φ : ℝ → ℝ} {τ : ℝ} (h : (quantileSet X φ τ).Nonempty) :
    quantile X φ τ h ∈ X ∧ τ ≤ cdf X φ (quantile X φ τ h) :=
  mem_quantileSet.1 (Finset.min'_mem _ h)

/-- The quantile is the least point of `X` at which the CDF reaches `τ`. -/
theorem quantile_le {X : Finset ℝ} {φ : ℝ → ℝ} {τ : ℝ} (h : (quantileSet X φ τ).Nonempty) {x : ℝ}
    (hx : x ∈ X) (hτ : τ ≤ cdf X φ x) : quantile X φ τ h ≤ x :=
  Finset.min'_le _ _ (mem_quantileSet.2 ⟨hx, hτ⟩)

/-- Example 1.2.5 (p. 32): on `X = {1, 2, 3}` with `φ = (0.5, 0, 0.5)`, the CDF is
`(0.5, 0.5, 1)`. -/
theorem example_1_2_5_cdf :
    let φ : ℝ → ℝ := fun x => if x = 1 then 1 / 2 else if x = 3 then 1 / 2 else 0
    cdf {1, 2, 3} φ 1 = 1 / 2 ∧ cdf {1, 2, 3} φ 2 = 1 / 2 ∧ cdf {1, 2, 3} φ 3 = 1 := by
  intro φ
  simp only [cdf, φ]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- Example 1.2.5 (p. 32), continued: the median is `x₁ = 1`; the `min` in (1.24) selects it
although `2` would be another reasonable median. -/
theorem example_1_2_5_median
    (h : (quantileSet {1, 2, 3} (fun x : ℝ => if x = 1 then 1 / 2 else if x = 3 then 1 / 2
      else (0 : ℝ)) (1 / 2)).Nonempty) :
    quantile {1, 2, 3} (fun x : ℝ => if x = 1 then 1 / 2 else if x = 3 then 1 / 2 else 0)
      (1 / 2) h = 1 := by
  apply le_antisymm
  · refine quantile_le h (by simp) ?_
    simp only [cdf]
    norm_num [Finset.sum_insert, Finset.sum_singleton]
  · refine Finset.le_min' _ _ _ fun y hy => ?_
    have hyX := (quantileSet_subset _ _ _) hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyX
    rcases hyX with rfl | rfl | rfl <;> norm_num

/-- Shifting the distribution by `α`: the support moves to `X + α` and the mass function to
`y ↦ φ(y − α)` (Exercise 1.2.28, p. 32). -/
theorem isDistributionOn_shift {X : Finset ℝ} {φ : ℝ → ℝ} (hφ : IsDistributionOn X φ) (α : ℝ) :
    IsDistributionOn (X.image (· + α)) (fun y => φ (y - α)) where
  nonneg y hy := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    simpa using hφ.nonneg x hx
  sum_eq_one := by
    rw [Finset.sum_image fun _ _ _ _ h => add_right_cancel h]
    simpa using hφ.sum_eq_one

/-- The CDF of the shifted distribution: `Φ_Y(x + α) = Φ_X(x)`. -/
theorem cdf_shift (X : Finset ℝ) (φ : ℝ → ℝ) (α x : ℝ) :
    cdf (X.image (· + α)) (fun y => φ (y - α)) (x + α) = cdf X φ x := by
  unfold cdf
  rw [Finset.sum_image fun _ _ _ _ h => add_right_cancel h]
  refine Finset.sum_congr rfl fun x' _ => ?_
  simp only [add_le_add_iff_right, add_sub_cancel_right]

/-- The quantile set of the shifted distribution is the shifted quantile set. -/
theorem quantileSet_shift (X : Finset ℝ) (φ : ℝ → ℝ) (α τ : ℝ) :
    quantileSet (X.image (· + α)) (fun y => φ (y - α)) τ = (quantileSet X φ τ).image (· + α) := by
  ext y
  simp only [mem_quantileSet, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hτ⟩
    exact ⟨x, ⟨hx, by rwa [cdf_shift] at hτ⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hτ⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [cdf_shift]⟩

/-- Exercise 1.2.28 (p. 32): quantiles are additive over constants, `Q_τ(X + α) = Q_τ(X) + α`. -/
theorem quantile_shift (X : Finset ℝ) (φ : ℝ → ℝ) (α τ : ℝ) (h : (quantileSet X φ τ).Nonempty)
    (h' : (quantileSet (X.image (· + α)) (fun y => φ (y - α)) τ).Nonempty) :
    quantile (X.image (· + α)) (fun y => φ (y - α)) τ h' = quantile X φ τ h + α := by
  apply le_antisymm
  · -- `Q_τ(X) + α` lies in the shifted quantile set
    refine Finset.min'_le _ _ ?_
    rw [quantileSet_shift]
    exact Finset.mem_image.2 ⟨_, Finset.min'_mem _ h, rfl⟩
  · -- every point of the shifted quantile set is `x + α` with `x` in the original one
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rw [quantileSet_shift] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have := Finset.min'_le (quantileSet X φ τ) x hx
    unfold quantile
    linarith

end SargentStachurski.JobSearch
