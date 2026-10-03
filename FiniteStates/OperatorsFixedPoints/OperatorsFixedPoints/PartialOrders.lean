/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.RelClasses
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Basic

/-!
# Partial orders, greatest elements, suprema and infima

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.1 (pp. 51–55).

Partial orders are Mathlib's `PartialOrder`; the pointwise order on `ℝ^X` is
the `Pi` instance; greatest and least elements are `IsGreatest`/`IsLeast`;
suprema and infima are `IsLUB`/`IsGLB`. The exercises of the section are
proved in that vocabulary: Exercises 2.2.1–2.2.17, with the matrix inequalities
of Exercises 2.2.7–2.2.8 that later sections use.
-/

open Finset Set Matrix

namespace SargentStachurski.OperatorsFixedPoints

/-! ### Partially ordered sets (§2.2.1.1) -/

/-- Example 2.2.1 (p. 51): `≤` on `ℝ` is a partial order; antisymmetry says `a ≤ b` and `b ≤ a`
imply `a = b`. -/
theorem real_le_isPartialOrder : IsPartialOrder ℝ (· ≤ ·) := inferInstance

theorem real_le_antisymm {a b : ℝ} (hab : a ≤ b) (hba : b ≤ a) : a = b := le_antisymm hab hba

/-- Exercise 2.2.1 (p. 51): equality is a partial order on any set. -/
theorem eq_isPartialOrder (P : Type*) : IsPartialOrder P (· = ·) where
  refl _ := rfl
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  antisymm _ _ h _ := h

/-- Exercise 2.2.2 (p. 51): set inclusion is a partial order on `℘(M)`. -/
theorem subset_isPartialOrder (M : Type*) : IsPartialOrder (Set M) (· ⊆ ·) := inferInstance

/-- Example 2.2.2 and Exercise 2.2.3 (p. 52): the pointwise order `u ≤ v ↔ ∀ x, u x ≤ v x` is a
partial order on `ℝ^X`. -/
theorem pointwise_isPartialOrder (X : Type*) : IsPartialOrder (X → ℝ) (· ≤ ·) := inferInstance

theorem pointwise_le_def {X : Type*} (u v : X → ℝ) : u ≤ v ↔ ∀ x, u x ≤ v x := Pi.le_def

/-- The strict pointwise relation `u ≪ v` of p. 52: `u(x) < v(x)` for all `x`. -/
def StrictLt {X : Type*} (u v : X → ℝ) : Prop := ∀ x, u x < v x

/-- Exercise 2.2.4 (p. 52): `≪` is not a partial order on `ℝ^X` for nonempty `X`, since it is not
reflexive. -/
theorem not_strictLt_refl {X : Type*} [Nonempty X] (u : X → ℝ) : ¬ StrictLt u u :=
  fun h => lt_irrefl _ (h (Classical.arbitrary X))

theorem strictLt_not_isPartialOrder {X : Type*} [Nonempty X] :
    ¬ IsPartialOrder (X → ℝ) StrictLt :=
  fun h => not_strictLt_refl (fun _ : X => (0 : ℝ)) (h.refl _)

/-- Exercise 2.2.5 (p. 52): limits preserve weak inequalities in `ℝⁿ`: if `a ≤ uₖ ≤ b` for all
`k` and `uₖ → u`, then `a ≤ u ≤ b`. -/
theorem le_of_tendsto_pi {n : ℕ} {a b u : Fin n → ℝ} {u' : ℕ → Fin n → ℝ}
    (hab : ∀ k, a ≤ u' k ∧ u' k ≤ b) (hlim : Filter.Tendsto u' Filter.atTop (nhds u)) :
    a ≤ u ∧ u ≤ b := by
  have hmem : ∀ k, u' k ∈ Icc a b := fun k => hab k
  have := isClosed_Icc.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  exact this

/-- Example 2.2.3 and Exercise 2.2.6 (pp. 52–53): the pointwise order on `n × k` matrices is the
pointwise order on functions on `X = [n] × [k]`. -/
theorem matrix_le_iff_uncurry {m k : Type*} (A B : Matrix m k ℝ) :
    (∀ i j, A i j ≤ B i j) ↔ ∀ p : m × k, A p.1 p.2 ≤ B p.1 p.2 :=
  ⟨fun h p => h p.1 p.2, fun h i j => h (i, j)⟩

/-- A nonnegative matrix preserves `≤` on vectors: the step behind Exercise 2.2.7 (ii) and
Exercise 2.2.27. -/
theorem mulVec_le_mulVec {m k : Type*} [Fintype k] {A : Matrix m k ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {u v : k → ℝ} (huv : u ≤ v) : A *ᵥ u ≤ A *ᵥ v := fun i =>
  sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (hA i j)

/-- Exercise 2.2.7 (i), p. 53: if `B ≥ 0` then `|Bu| ≤ B|u|` pointwise. -/
theorem abs_mulVec_le {m k : Type*} [Fintype k] {B : Matrix m k ℝ} (hB : ∀ i j, 0 ≤ B i j)
    (u : k → ℝ) (i : m) : |(B *ᵥ u) i| ≤ (B *ᵥ fun j => |u j|) i := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, B i j * u j| ≤ ∑ j, |B i j * u j| := abs_sum_le_sum_abs _ _
    _ = ∑ j, B i j * |u j| := sum_congr rfl fun j _ => by
        rw [abs_mul, abs_of_nonneg (hB i j)]

/-- Exercise 2.2.7 (ii), p. 53: if `A ≥ 0` and `uₖ₊₁ ≤ Auₖ` for all `k`, then `uₖ ≤ Aᵏu₀`. -/
theorem le_pow_mulVec_of_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    {u : ℕ → Fin n → ℝ} (h : ∀ k, u (k + 1) ≤ A *ᵥ u k) (k : ℕ) : u k ≤ A ^ k *ᵥ u 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc u (k + 1) ≤ A *ᵥ u k := h k
      _ ≤ A *ᵥ (A ^ k *ᵥ u 0) := mulVec_le_mulVec hA ih
      _ = A ^ (k + 1) *ᵥ u 0 := by rw [Matrix.mulVec_mulVec, pow_succ']

/-- Exercise 2.2.8 (p. 53): if `A ≫ 0`, `u ≤ v` and `u ≠ v`, then `Au ≪ Av`. -/
theorem strictLt_mulVec {m k : Type*} [Fintype k] {A : Matrix m k ℝ} (hA : ∀ i j, 0 < A i j)
    {u v : k → ℝ} (huv : u ≤ v) (hne : u ≠ v) : StrictLt (A *ᵥ u) (A *ᵥ v) := by
  intro i
  obtain ⟨j₀, hj₀⟩ : ∃ j, u j < v j := by
    by_contra hcon
    have hcon' : ∀ j, v j ≤ u j := fun j => le_of_not_gt fun h => hcon ⟨j, h⟩
    exact hne (funext fun j => le_antisymm (huv j) (hcon' j))
  simp only [Matrix.mulVec, dotProduct]
  exact sum_lt_sum (fun j _ => mul_le_mul_of_nonneg_left (huv j) (hA i j).le)
    ⟨j₀, mem_univ _, mul_lt_mul_of_pos_left hj₀ (hA i j₀)⟩

/-- Example 2.2.4 (p. 53): `≤` is a total order on `ℝ` and on `ℕ`. -/
theorem real_le_total (a b : ℝ) : a ≤ b ∨ b ≤ a := le_total a b

theorem nat_le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := le_total a b

/-- Example 2.2.5 (p. 53): the pointwise order on `ℝ²` is not total: `(0, 1)` and `(1, 0)` are
incomparable. -/
theorem pointwise_not_total :
    ¬ ((![0, 1] : Fin 2 → ℝ) ≤ ![1, 0] ∨ (![1, 0] : Fin 2 → ℝ) ≤ ![0, 1]) := by
  rintro (h | h)
  · have := h 1
    norm_num at this
  · have := h 0
    norm_num at this

/-- Exercise 2.2.9 (p. 53): inclusion on `℘({1, 2})` is not total: `{1}` and `{2}` are
incomparable. -/
theorem subset_not_total : ¬ (({0} : Set (Fin 2)) ⊆ {1} ∨ ({1} : Set (Fin 2)) ⊆ {0}) := by
  rintro (h | h)
  · have := h (mem_singleton 0)
    simp at this
  · have := h (mem_singleton 1)
    simp at this

/-! ### Least and greatest elements (§2.2.1.2) -/

/-- Exercise 2.2.10 (p. 54): a subset of a partially ordered set has at most one greatest
element. -/
theorem isGreatest_unique {P : Type*} [PartialOrder P] {A : Set P} {g g' : P} (hg : IsGreatest A g)
    (hg' : IsGreatest A g') : g = g' :=
  hg.unique hg'

/-- Exercise 2.2.10 (p. 54): ... and at most one least element. -/
theorem isLeast_unique {P : Type*} [PartialOrder P] {A : Set P} {l l' : P} (hl : IsLeast A l)
    (hl' : IsLeast A l') : l = l' :=
  hl.unique hl'

/-- Exercise 2.2.11 (p. 54): `⋃ᵢ Aᵢ` is the greatest element of `{Aᵢ}` iff it is one of the
`Aᵢ`. -/
theorem isGreatest_iUnion_iff {M ι : Type*} (A : ι → Set M) :
    IsGreatest (range A) (⋃ i, A i) ↔ (⋃ i, A i) ∈ range A := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, by rintro _ ⟨i, rfl⟩; exact subset_iUnion A i⟩

/-- Exercise 2.2.12 (p. 54): the bounded subsets of `ℝⁿ` (`n ≥ 1`) have no greatest element
under inclusion: a greatest one would contain every singleton, hence be all of `ℝⁿ`, which is
unbounded. -/
theorem not_exists_isGreatest_bounded {n : ℕ} [NeZero n] :
    ¬ ∃ G, IsGreatest {A : Set (Fin n → ℝ) | Bornology.IsBounded A} G := by
  rintro ⟨G, hG, hmax⟩
  have huniv : G = univ := by
    refine eq_univ_of_forall fun x => ?_
    have := hmax (Bornology.isBounded_singleton (x := x))
    exact this (mem_singleton x)
  rw [huniv] at hG
  exact NormedSpace.unbounded_univ ℝ (Fin n → ℝ) hG

/-! ### Suprema and infima (§2.2.1.3) -/

/-- Exercise 2.2.13 (p. 54): a subset has at most one supremum. -/
theorem isLUB_unique {P : Type*} [PartialOrder P] {A : Set P} {s s' : P} (hs : IsLUB A s)
    (hs' : IsLUB A s') : s = s' :=
  hs.unique hs'

/-- Exercise 2.2.14 (i), p. 55: a supremum that belongs to `A` is a greatest element. -/
theorem isGreatest_of_isLUB_mem {P : Type*} [Preorder P] {A : Set P} {a : P} (h : IsLUB A a)
    (ha : a ∈ A) : IsGreatest A a :=
  ⟨ha, h.1⟩

/-- Exercise 2.2.14 (ii), p. 55: a greatest element is the supremum. -/
theorem IsGreatest.isLUB' {P : Type*} [Preorder P] {A : Set P} {a : P} (h : IsGreatest A a) :
    IsLUB A a :=
  h.isLUB

/-- Exercise 2.2.15 (p. 55): a least element is the infimum. -/
theorem IsLeast.isGLB' {P : Type*} [Preorder P] {A : Set P} {l : P} (h : IsLeast A l) :
    IsGLB A l :=
  h.isGLB

/-- Exercise 2.2.16 (p. 55): in `℘(M)`, `⋁ᵢ Aᵢ = ⋃ᵢ Aᵢ`. -/
theorem isLUB_iUnion {M ι : Type*} (A : ι → Set M) : IsLUB (range A) (⋃ i, A i) :=
  isLUB_iSup

/-- Exercise 2.2.16 (p. 55): in `℘(M)`, `⋀ᵢ Aᵢ = ⋂ᵢ Aᵢ`. -/
theorem isGLB_iInter {M ι : Type*} (A : ι → Set M) : IsGLB (range A) (⋂ i, A i) :=
  isGLB_iInf

/-- Exercise 2.2.17 (p. 55): a totally ordered set in which a subset has no supremum. In
`P = (0, 1)` the subset `A = [1/2, 1)` has no upper bound in `P`, hence no supremum. -/
theorem not_exists_isLUB_Ioo :
    ¬ ∃ s : Ioo (0 : ℝ) 1, IsLUB {a : Ioo (0 : ℝ) 1 | 1 / 2 ≤ (a : ℝ)} s := by
  rintro ⟨s, hs, -⟩
  have hs1 : (s : ℝ) < 1 := s.2.2
  -- the point `(s + 1)/2` lies in `A` and exceeds `s`
  have hmem : (1 / 2 : ℝ) ≤ ((s : ℝ) + 1) / 2 := by linarith [s.2.1]
  have hin : ((s : ℝ) + 1) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [s.2.1], by linarith⟩
  have := hs (show (⟨((s : ℝ) + 1) / 2, hin⟩ : Ioo (0 : ℝ) 1) ∈
    {a : Ioo (0 : ℝ) 1 | 1 / 2 ≤ (a : ℝ)} from hmem)
  have h' : ((s : ℝ) + 1) / 2 ≤ s := this
  linarith

end SargentStachurski.OperatorsFixedPoints
