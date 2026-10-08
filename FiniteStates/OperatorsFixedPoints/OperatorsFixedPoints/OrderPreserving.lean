/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.Basics
import OperatorsFixedPoints.PartialOrders
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Order.Basic

/-!
# Order-preserving maps, increasing functions and Blackwell's condition

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.3 (pp. 59–62).

Order-preserving maps are Mathlib's `Monotone`, order-reversing `Antitone`;
for real-valued functions on a partially ordered set the book says
"increasing" and "decreasing". Examples 2.2.8–2.2.10 and Exercises
2.2.25–2.2.32 are proved here, except the spectral-radius half of Exercise
2.2.28, which is in `SpectralRadius`. Blackwell's condition (Lemma 2.2.4):
an order-preserving self-map that discounts constants is a contraction in the
supremum norm.
-/

open Finset Set Filter Topology Matrix

namespace SargentStachurski.OperatorsFixedPoints

/-! ### Order-preserving maps (§2.2.3.1) -/

/-- Example 2.2.8 (p. 60): for `A ≥ 0`, `u ↦ Au + b` is order preserving on `ℝⁿ`. -/
theorem monotone_affine_of_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (b : Fin n → ℝ) : Monotone fun u => A *ᵥ u + b := fun u v huv => by
  change A *ᵥ u + b ≤ A *ᵥ v + b
  exact add_le_add (mulVec_le_mulVec hA huv) le_rfl

/-- Example 2.2.9 (p. 60): integration over `[a, b]` is order preserving on continuous functions
under the pointwise order. -/
theorem integral_mono_of_le {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
  intervalIntegral.integral_mono_on hab (hf.intervalIntegrable_of_Icc hab)
    (hg.intervalIntegrable_of_Icc hab) hfg

/-- Exercise 2.2.25 (p. 60): an order-preserving `F` maps a greatest element to the greatest
element of the image, which is therefore the supremum of the image: `F(⋁ uᵢ) = ⋁ Fuᵢ`. -/
theorem isLUB_image_of_isGreatest {P Q : Type*} [Preorder P] [Preorder Q] {F : P → Q}
    (hF : Monotone F) {s : Set P} {u : P} (hu : IsGreatest s u) : IsLUB (F '' s) (F u) :=
  (hF.map_isGreatest hu).isLUB

/-- Exercise 2.2.25 (p. 60), the infimum half: `F(⋀ uᵢ) = ⋀ Fuᵢ`. -/
theorem isGLB_image_of_isLeast {P Q : Type*} [Preorder P] [Preorder Q] {F : P → Q}
    (hF : Monotone F) {s : Set P} {l : P} (hl : IsLeast s l) : IsGLB (F '' s) (F l) :=
  (hF.map_isLeast hl).isGLB

/-- Exercise 2.2.26 (p. 60): powers of an order-preserving self-map are order preserving. -/
theorem monotone_iterate {P : Type*} [Preorder P] {A : P → P} (hA : Monotone A) (k : ℕ) :
    Monotone A^[k] :=
  hA.iterate k

/-- Exercise 2.2.27 (p. 60): for `A ≥ 0` the map `u ↦ Au` is order preserving. -/
theorem monotone_mulVec_of_nonneg {m k : Type*} [Fintype k] {A : Matrix m k ℝ}
    (hA : ∀ i j, 0 ≤ A i j) : Monotone fun u : k → ℝ => A *ᵥ u := fun _ _ huv =>
  mulVec_le_mulVec hA huv

/-- Products of nonnegative matrices are monotone in each factor. -/
theorem mul_le_mul_of_nonneg {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (hCD : ∀ i j, C i j ≤ D i j) (i j : Fin n) : (A * C) i j ≤ (B * D) i j := by
  simp only [Matrix.mul_apply]
  refine sum_le_sum fun l _ => ?_
  calc A i l * C l j ≤ A i l * D l j := mul_le_mul_of_nonneg_left (hCD l j) (hA i l)
    _ ≤ B i l * D l j := mul_le_mul_of_nonneg_right (hAB i l) ((hC l j).trans (hCD l j))

/-- Powers of a nonnegative matrix are nonnegative. -/
theorem pow_nonneg_entries {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ)
    (i j : Fin n) : 0 ≤ (A ^ k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact sum_nonneg fun l _ => mul_nonneg (hA i l) (ih l j)

/-- Exercise 2.2.28 (p. 60), first part: `0 ≤ A ≤ B` implies `Aᵏ ≤ Bᵏ` for all `k`. -/
theorem pow_le_pow_entries {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) (i j : Fin n) : (A ^ k) i j ≤ (B ^ k) i j := by
  induction k generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ']
    exact mul_le_mul_of_nonneg hA hAB (pow_nonneg_entries hA k) ih i j

/-! ### Increasing and decreasing functions (§2.2.3.2) -/

/-- The increasing functions `iℝ^P` on a partially ordered set (p. 61). -/
def increasingFns (P : Type*) [Preorder P] : Set (P → ℝ) := {h | Monotone h}

/-- Example 2.2.10 (p. 61) on `P = {1, …, n}`: `x ↦ 2x` is increasing. -/
theorem monotone_two_mul {n : ℕ} : Monotone fun x : Fin n => (2 : ℝ) * x := fun x y hxy => by
  have : (x : ℝ) ≤ y := by exact_mod_cast hxy
  linarith

/-- Example 2.2.10 (p. 61): `x ↦ 1{2 ≤ x}` is increasing. -/
theorem monotone_indicator_ge {n : ℕ} :
    Monotone fun x : Fin n => if 2 ≤ (x : ℕ) then (1 : ℝ) else 0 := fun x y hxy => by
  dsimp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans (Fin.le_def.1 hxy)) h2
  · norm_num
  · exact le_rfl

/-- Example 2.2.10 (p. 61): `x ↦ −x` is not increasing on `{1, …, n}` with `n ≥ 2`. -/
theorem not_monotone_neg : ¬ Monotone fun x : Fin 5 => -((x : ℕ) : ℝ) := by
  intro h
  have := h (show (0 : Fin 5) ≤ 1 by decide)
  norm_num at this

/-- Example 2.2.10 (p. 61): `x ↦ 1{x ≤ 2}` is not increasing. -/
theorem not_monotone_indicator_le :
    ¬ Monotone fun x : Fin 5 => if (x : ℕ) ≤ 2 then (1 : ℝ) else 0 := by
  intro h
  have := h (show (2 : Fin 5) ≤ 3 by decide)
  norm_num at this

/-- Exercise 2.2.29 (i), p. 61: `αf + βg` is increasing for `α, β ≥ 0`. -/
theorem monotone_smul_add {P : Type*} [Preorder P] {f g : P → ℝ} (hf : Monotone f)
    (hg : Monotone g) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) : Monotone fun p => α * f p + β * g p :=
  (hf.const_mul hα).add (hg.const_mul hβ)

/-- Exercise 2.2.29 (ii), p. 61: `f ∨ g` and `f ∧ g` are increasing. -/
theorem monotone_sup_inf {P : Type*} [Preorder P] {f g : P → ℝ} (hf : Monotone f)
    (hg : Monotone g) : Monotone (f ⊔ g) ∧ Monotone (f ⊓ g) :=
  ⟨hf.sup hg, hf.inf hg⟩

/-- Exercise 2.2.30 (p. 61): `iℝ^P` is a closed subset of `ℝ^P`. -/
theorem isClosed_increasingFns (P : Type*) [Preorder P] : IsClosed (increasingFns P) := by
  have : increasingFns P = ⋂ (p : P) (q : P) (_ : p ≤ q), {h : P → ℝ | h p ≤ h q} := by
    ext h
    simp only [increasingFns, Set.mem_ofPred_eq, mem_iInter]
    exact ⟨fun hm p q hpq => hm hpq, fun hm p q hpq => hm p q hpq⟩
  rw [this]
  exact isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ =>
    isClosed_le (continuous_apply p) (continuous_apply q)

/-- Exercise 2.2.31 (p. 61): `h ↦ E h(X) = ∑ h(x) φ(x)` is increasing on `ℝ^X` for a
distribution `φ`. -/
theorem monotone_expectation {X : Type*} [Fintype X] {φ : X → ℝ} (hφ : ∀ x, 0 ≤ φ x) :
    Monotone fun h : X → ℝ => ∑ x, h x * φ x := fun _ _ hfg =>
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hfg x) (hφ x)

/-- Exercise 2.2.32 (p. 61): on the totally ordered set `X = {0, …, n − 1}`, every increasing
nonnegative `u` is a nonnegative combination of the increasing indicators `1{x ≥ k}`:
`u(x) = ∑ₖ sₖ 1{x ≥ k}` with `s₀ = u(0)` and `sₖ = u(k) − u(k − 1)`. -/
theorem exists_indicator_decomposition {n : ℕ} {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    ∃ s : ℕ → ℝ, (∀ k, 0 ≤ s k) ∧
      ∀ x < n, u x = ∑ k ∈ range n, s k * (if k ≤ x then 1 else 0) := by
  refine ⟨fun k => if k = 0 then u 0 else u k - u (k - 1), fun k => ?_, fun x hx => ?_⟩
  · dsimp only
    split_ifs with hk
    · exact hu0
    · exact sub_nonneg.2 (hu (Nat.sub_le k 1))
  · -- the sum over `k ≤ x` telescopes to `u x`
    have htel : ∀ m, ∑ k ∈ range (m + 1), (if k = 0 then u 0 else u k - u (k - 1)) = u m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_range_succ, ih]
        have : (if m + 1 = 0 then u 0 else u (m + 1) - u (m + 1 - 1)) = u (m + 1) - u m := by
          simp
        rw [this]
        ring
    have hfilter : (range n).filter (fun k => k ≤ x) = range (x + 1) := by
      ext k
      simp only [mem_filter, Finset.mem_range]
      omega
    calc u x = ∑ k ∈ range (x + 1), (if k = 0 then u 0 else u k - u (k - 1)) := (htel x).symm
      _ = ∑ k ∈ (range n).filter (fun k => k ≤ x), (if k = 0 then u 0 else u k - u (k - 1)) := by
          rw [hfilter]
      _ = ∑ k ∈ range n, (if k = 0 then u 0 else u k - u (k - 1)) * (if k ≤ x then 1 else 0) := by
          rw [sum_filter]
          refine sum_congr rfl fun k _ => ?_
          split_ifs <;> simp

/-! ### Blackwell's condition (§2.2.3.3) -/

/-- Lemma 2.2.4 (Blackwell, p. 62): on `U ⊆ ℝ^X` closed under adding nonnegative constants, an
order-preserving self-map `T` with `T(u + c) ≤ Tu + βc` for all `u ∈ U`, `c ≥ 0` and some
`β ∈ [0, 1)` is a contraction of modulus `β` in the supremum norm. -/
theorem isContractionOn_of_blackwell {X : Type*} [Fintype X] {U : Set (X → ℝ)}
    {T : (X → ℝ) → (X → ℝ)} {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hU : ∀ u ∈ U, ∀ c : ℝ, 0 ≤ c → (u + fun _ : X => c) ∈ U) (hmaps : MapsTo T U U)
    (hmono : ∀ u ∈ U, ∀ v ∈ U, u ≤ v → T u ≤ T v)
    (hdisc : ∀ u ∈ U, ∀ c : ℝ, 0 ≤ c → T (u + fun _ : X => c) ≤ T u + fun _ : X => β * c) :
    IsContractionOn T U β := by
  refine ⟨hmaps, hβ0, hβ1, fun u hu v hv => ?_⟩
  -- `Tu ≤ Tv + β‖u − v‖` pointwise, by monotonicity and discounting
  have key : ∀ u ∈ U, ∀ v ∈ U, ∀ x : X, T u x - T v x ≤ β * ‖u - v‖ := by
    intro u hu v hv x
    have hle : u ≤ v + fun _ : X => ‖u - v‖ := fun y => by
      have := norm_le_pi_norm (u - v) y
      rw [Pi.sub_apply, Real.norm_eq_abs] at this
      simp only [Pi.add_apply]
      linarith [le_abs_self (u y - v y)]
    have h1 := hmono u hu _ (hU v hv ‖u - v‖ (norm_nonneg _)) hle x
    have h2 := hdisc v hv ‖u - v‖ (norm_nonneg _) x
    simp only [Pi.add_apply] at h1 h2
    linarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hβ0 (norm_nonneg _))]
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  refine ⟨key u hu v hv x, ?_⟩
  have := key v hv u hu x
  rwa [norm_sub_rev] at this

end SargentStachurski.OperatorsFixedPoints
