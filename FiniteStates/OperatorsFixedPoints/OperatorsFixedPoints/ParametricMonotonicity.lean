/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.Basics
import OperatorsFixedPoints.PartialOrders
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic

/-!
# Parametric monotonicity

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.2.5 (pp. 64–68).

`T` dominates `S` on `P` if `Su ≤ Tu` for all `u`; this is the pointwise order
on self-maps (Exercise 2.2.37). Proposition 2.2.7: if `T` dominates `S`, is
order preserving and globally stable, then its fixed point dominates every
fixed point of `S`. The ambient space is any partially ordered topological
space in which the order is closed, which covers `M ⊆ ℝⁿ` under the pointwise
order.

Exercise 2.2.38 applies the proposition to the Solow–Swan steady state and
Exercise 2.2.39 to the job-search continuation value: both are proved from
the proposition alone, without the closed forms of Chapter 1. The global
stability of the Solow–Swan map is Chapter 1's Exercise 1.2.26 and enters as a
hypothesis; the contraction property of the continuation-value map is proved
here.
-/

open Filter Topology Function Set Finset Matrix

namespace SargentStachurski.OperatorsFixedPoints

variable {P : Type*}

/-- Example 2.2.12 (p. 65): for `0 ≤ A ≤ B` and `u ≥ 0`, `Au + b ≤ Bu + b`, so `u ↦ Bu + b`
dominates `u ↦ Au + b` on `ℝⁿ₊`. -/
theorem affine_dominates {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : ∀ i j, A i j ≤ B i j)
    (b : Fin n → ℝ) {u : Fin n → ℝ} (hu : 0 ≤ u) : A *ᵥ u + b ≤ B *ᵥ u + b := fun i => by
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  exact add_le_add (sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hu j)) le_rfl

/-- Exercise 2.2.36 (p. 65): if `S ≤ T` are order-preserving self-maps, then `Sᵏ ≤ Tᵏ`. -/
theorem iterate_le_iterate [Preorder P] {S T : P → P} (hS : Monotone S) (hST : S ≤ T) (k : ℕ) :
    S^[k] ≤ T^[k] := by
  intro u
  induction k generalizing u with
  | zero => exact le_rfl
  | succ k ih =>
    rw [iterate_succ_apply, iterate_succ_apply]
    calc S^[k] (S u) ≤ S^[k] (T u) := (hS.iterate k) (hST u)
      _ ≤ T^[k] (T u) := ih (T u)

/-- Exercise 2.2.37 (p. 65): dominance is a partial order on the self-maps of `P`. -/
theorem dominance_isPartialOrder [PartialOrder P] : IsPartialOrder (P → P) (· ≤ ·) :=
  inferInstance

/-- Proposition 2.2.7 (p. 67): if `T` dominates `S`, and `T` is order preserving and globally
stable with fixed point `u_T`, then `u_S ≤ u_T` for every fixed point `u_S` of `S`. The proof is
the book's: `u_S = Su_S ≤ Tu_S`, so by monotonicity `u_S ≤ Tᵏu_S` for all `k`, and the order is
closed under limits. -/
theorem fixedPt_le_of_dominates [PartialOrder P] [TopologicalSpace P] [OrderClosedTopology P]
    {S T : P → P} (hST : S ≤ T) (hT : Monotone T) (hstab : GloballyStable T) {uS uT : P}
    (huS : IsFixedPt S uS) (huT : IsFixedPt T uT) : uS ≤ uT := by
  have hle : ∀ k : ℕ, uS ≤ T^[k] uS := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      calc uS = S uS := huS.eq.symm
        _ ≤ T uS := hST uS
        _ ≤ T (T^[k] uS) := hT ih
        _ = T^[k + 1] uS := (iterate_succ_apply' T k uS).symm
  exact ge_of_tendsto' (hstab.tendsto_iterate huT uS) hle

/-! ### Exercise 2.2.38: the Solow–Swan steady state -/

/-- The Solow–Swan map `g(k) = sAkᵅ + (1 − δ)k` as a self-map of `(0, ∞)`, Exercise 2.2.38
(p. 67), for `s, A > 0`, `α ∈ (0, 1)`, `δ ∈ (0, 1]`. -/
noncomputable def solowMap (s A α δ : ℝ) (hs : 0 < s) (hA : 0 < A) (hδ : δ ≤ 1) :
    Ioi (0 : ℝ) → Ioi (0 : ℝ) := fun k =>
  ⟨s * A * (k : ℝ) ^ α + (1 - δ) * k, by
    have h1 := mul_pos (mul_pos hs hA) (Real.rpow_pos_of_pos k.2 α)
    have h2 : 0 ≤ (1 - δ) * (k : ℝ) := mul_nonneg (by linarith) k.2.le
    exact Set.mem_Ioi.2 (by linarith)⟩

/-- `g` is order preserving on `(0, ∞)` for `α > 0`. -/
theorem solowMap_monotone {s A α δ : ℝ} (hs : 0 < s) (hA : 0 < A) (hα : 0 < α) (hδ : δ ≤ 1) :
    Monotone (solowMap s A α δ hs hA hδ) := by
  intro k k' hkk'
  have hk : (k : ℝ) ≤ k' := hkk'
  change s * A * (k : ℝ) ^ α + (1 - δ) * k ≤ s * A * (k' : ℝ) ^ α + (1 - δ) * k'
  have h1 : (k : ℝ) ^ α ≤ (k' : ℝ) ^ α := Real.rpow_le_rpow k.2.le hk hα.le
  have h2 : (1 - δ) * (k : ℝ) ≤ (1 - δ) * k' := mul_le_mul_of_nonneg_left hk (by linarith)
  nlinarith [mul_pos hs hA]

/-- Exercise 2.2.38 (p. 67): raising `s` or `A`, or lowering `δ`, shifts `g` up everywhere. -/
theorem solowMap_le {s A δ s' A' δ' α : ℝ} (hs : 0 < s) (hA : 0 < A) (hδ : δ ≤ 1) (hs' : 0 < s')
    (hA' : 0 < A') (hδ' : δ' ≤ 1) (hss : s ≤ s') (hAA : A ≤ A') (hδδ : δ' ≤ δ) :
    solowMap s A α δ hs hA hδ ≤ solowMap s' A' α δ' hs' hA' hδ' := by
  intro k
  change s * A * (k : ℝ) ^ α + (1 - δ) * k ≤ s' * A' * (k : ℝ) ^ α + (1 - δ') * k
  have hk := k.2
  have hpow : 0 < (k : ℝ) ^ α := Real.rpow_pos_of_pos hk α
  have h1 : s * A ≤ s' * A' := mul_le_mul hss hAA hA.le hs'.le
  have h2 : (1 - δ) * (k : ℝ) ≤ (1 - δ') * k := mul_le_mul_of_nonneg_right (by linarith) hk.le
  nlinarith

/-- Exercise 2.2.38 (p. 67): the steady state `k*` is increasing in `s` and `A` and decreasing in
`δ`, by Proposition 2.2.7. Global stability of the Solow–Swan map on `(0, ∞)` is Chapter 1's
Exercise 1.2.26 and is a hypothesis here (`hstab`); the closed form for `k*` is not used. -/
theorem solow_fixedPt_le {s A δ s' A' δ' α : ℝ} (hs : 0 < s) (hA : 0 < A) (hδ : δ ≤ 1)
    (hs' : 0 < s') (hA' : 0 < A') (hδ' : δ' ≤ 1) (hα : 0 < α) (hss : s ≤ s') (hAA : A ≤ A')
    (hδδ : δ' ≤ δ) (hstab : GloballyStable (solowMap s' A' α δ' hs' hA' hδ'))
    {k k' : Ioi (0 : ℝ)} (hk : IsFixedPt (solowMap s A α δ hs hA hδ) k)
    (hk' : IsFixedPt (solowMap s' A' α δ' hs' hA' hδ') k') : k ≤ k' :=
  fixedPt_le_of_dominates (solowMap_le hs hA hδ hs' hA' hδ' hss hAA hδδ)
    (solowMap_monotone hs' hA' hα hδ') hstab hk hk'

/-! ### Exercise 2.2.39: the continuation value is increasing in `β` -/

/-- The job-search continuation-value map of Vol. 1 (1.33),
`gᵦ(h) = c + β ∑ max{w/(1 − β), h} φ(w)`, for a finite set of wage offers `W`. -/
noncomputable def contMap {W : Type*} [Fintype W] (wage φ : W → ℝ) (c β : ℝ) (h : ℝ) : ℝ :=
  c + β * ∑ w, max (wage w / (1 - β)) h * φ w

/-- `gᵦ` is order preserving for `β ≥ 0` and `φ ≥ 0`. -/
theorem contMap_monotone {W : Type*} [Fintype W] {wage φ : W → ℝ} (hφ : ∀ w, 0 ≤ φ w) {c β : ℝ}
    (hβ : 0 ≤ β) : Monotone (contMap wage φ c β) := by
  intro h h' hh
  unfold contMap
  have : ∑ w, max (wage w / (1 - β)) h * φ w ≤ ∑ w, max (wage w / (1 - β)) h' * φ w :=
    sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (max_le_max_left _ hh) (hφ w)
  nlinarith

/-- `gᵦ` is a contraction of modulus `β` on `ℝ`, by (1.28) and `∑ φ = 1`. -/
theorem contMap_isContractionOn {W : Type*} [Fintype W] {wage φ : W → ℝ} (hφ : ∀ w, 0 ≤ φ w)
    (hsum : ∑ w, φ w = 1) {c β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsContractionOn (contMap wage φ c β) univ β := by
  refine ⟨mapsTo_univ _ _, hβ0, hβ1, fun h _ h' _ => ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold contMap
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg hβ0, ← sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hβ0
  calc |∑ w, (max (wage w / (1 - β)) h * φ w - max (wage w / (1 - β)) h' * φ w)|
      ≤ ∑ w, |max (wage w / (1 - β)) h * φ w - max (wage w / (1 - β)) h' * φ w| :=
        abs_sum_le_sum_abs _ _
    _ = ∑ w, |max (wage w / (1 - β)) h - max (wage w / (1 - β)) h'| * φ w := by
        refine sum_congr rfl fun w _ => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (hφ w)]
    _ ≤ ∑ w, |h - h'| * φ w :=
        sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (by
          rw [max_comm _ h, max_comm _ h']
          exact abs_max_sub_max_le_abs _ _ _) (hφ w)
    _ = |h - h'| := by rw [← mul_sum, hsum, mul_one]

/-- `β₁ ≤ β₂` shifts `g` up everywhere on `ℝ₊`, for nonnegative wages. -/
theorem contMap_le {W : Type*} [Fintype W] {wage φ : W → ℝ} (hw : ∀ w, 0 ≤ wage w)
    (hφ : ∀ w, 0 ≤ φ w) {c β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : β₂ < 1) (hββ : β₁ ≤ β₂) {h : ℝ}
    (hh : 0 ≤ h) : contMap wage φ c β₁ h ≤ contMap wage φ c β₂ h := by
  unfold contMap
  have h1 : ∀ w, max (wage w / (1 - β₁)) h ≤ max (wage w / (1 - β₂)) h := fun w => by
    have hβ₂' : 0 < 1 - β₂ := by linarith
    exact max_le_max (div_le_div_of_nonneg_left (hw w) hβ₂' (by linarith)) le_rfl
  have h2 : 0 ≤ ∑ w, max (wage w / (1 - β₁)) h * φ w :=
    sum_nonneg fun w _ => mul_nonneg (le_trans hh (le_max_right _ _)) (hφ w)
  have h3 : ∑ w, max (wage w / (1 - β₁)) h * φ w ≤ ∑ w, max (wage w / (1 - β₂)) h * φ w :=
    sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (h1 w) (hφ w)
  nlinarith

/-- Exercise 2.2.39 (p. 67): the continuation value `h*` is increasing in `β`. With `β₁ ≤ β₂`,
`g₁ ≤ g₂` on `ℝ₊`, `g₂` is order preserving and (being a contraction) globally stable, so
Proposition 2.2.7 gives `h₁* ≤ h₂*`. The fixed points are taken in `ℝ₊` (`g` maps into
`[c, ∞)` when `c > 0`, so every fixed point is positive). -/
theorem contMap_fixedPt_le {W : Type*} [Fintype W] {wage φ : W → ℝ} (hw : ∀ w, 0 ≤ wage w)
    (hφ : ∀ w, 0 ≤ φ w) (hsum : ∑ w, φ w = 1) {c β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : β₂ < 1)
    (hββ : β₁ ≤ β₂) {h₁ h₂ : ℝ} (hh₁ : IsFixedPt (contMap wage φ c β₁) h₁)
    (hh₂ : IsFixedPt (contMap wage φ c β₂) h₂) (hh₁0 : 0 ≤ h₁) : h₁ ≤ h₂ := by
  -- Proposition 2.2.7 on the subtype `ℝ₊ = Ici 0` would need `g₂` to map it to itself; the
  -- scalar argument of the proposition is reproduced directly instead.
  have hβ₂0 : 0 ≤ β₂ := hβ₁.trans hββ
  have hstab :=
    (contMap_isContractionOn (wage := wage) (c := c) hφ hsum hβ₂0 hβ₂).globallyStable_univ
  have hmono := contMap_monotone hφ hβ₂0 (W := W) (wage := wage) (c := c)
  -- `h₁ ≤ g₂ᵏ h₁` for all `k`
  have hle : ∀ k : ℕ, h₁ ≤ (contMap wage φ c β₂)^[k] h₁ := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      calc h₁ = contMap wage φ c β₁ h₁ := hh₁.eq.symm
        _ ≤ contMap wage φ c β₂ h₁ := contMap_le hw hφ hβ₁ hβ₂ hββ hh₁0
        _ ≤ contMap wage φ c β₂ ((contMap wage φ c β₂)^[k] h₁) := hmono ih
        _ = (contMap wage φ c β₂)^[k + 1] h₁ := (iterate_succ_apply' _ k h₁).symm
  exact ge_of_tendsto' (hstab.tendsto_iterate hh₂ h₁) hle

end SargentStachurski.OperatorsFixedPoints
