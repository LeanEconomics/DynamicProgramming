/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OperatorsFixedPoints.Basics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# Conjugate maps and local stability

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §2.1.1–§2.1.2
(pp. 42–46).

A dynamical system is a set with a self-map; `(U, T)` and `(Û, T̂)` are
conjugate under a bijection `Φ : U → Û` if `T = Φ⁻¹ ∘ T̂ ∘ Φ`. Conjugacy
transports fixed points (Exercise 2.1.1, Proposition 2.1.1); topological
conjugacy, where `Φ` is a homeomorphism, also transports convergence of
orbits (Exercise 2.1.4), global stability (Proposition 2.1.2) and local
stability (Exercise 2.1.6), and is an equivalence relation (Exercise 2.1.5).

Local stability is defined in `Basics`. Example 2.1.4 treats `g(x) = x²`, and
the one-dimensional derivative criterion that the book sketches on p. 45
(`|g'(x*)| < 1` implies local stability) is proved by the mean value theorem.
The Hartman–Grobman theorem (Theorem 2.1.3) and its Corollary 2.1.4 are
quoted by the book without proof and are not claimed here.
-/

open Filter Topology Function Set Matrix

universe u v w

namespace SargentStachurski.OperatorsFixedPoints

variable {U : Type u} {V : Type v} {W : Type w}

/-- `(U, T)` and `(V, T')` are conjugate under the bijection `Φ` (p. 43): `T = Φ⁻¹ ∘ T' ∘ Φ`. -/
def IsConjugate (T : U → U) (T' : V → V) (Φ : U ≃ V) : Prop :=
  ∀ u, T u = Φ.symm (T' (Φ u))

namespace IsConjugate

variable {T : U → U} {T' : V → V} {Φ : U ≃ V}

/-- Conjugacy as the commuting square `Φ ∘ T = T' ∘ Φ`. -/
theorem comm (h : IsConjugate T T' Φ) (u : U) : Φ (T u) = T' (Φ u) := by
  rw [h u, Equiv.apply_symm_apply]

theorem of_comm (h : ∀ u, Φ (T u) = T' (Φ u)) : IsConjugate T T' Φ := fun u => by
  rw [← h u, Equiv.symm_apply_apply]

/-- Conjugacy is symmetric: `(V, T')` is conjugate to `(U, T)` under `Φ⁻¹`. -/
theorem symm (h : IsConjugate T T' Φ) : IsConjugate T' T Φ.symm :=
  of_comm fun v => by
    rw [h (Φ.symm v), Equiv.apply_symm_apply]

/-- Conjugacy is transitive. -/
theorem trans {T'' : W → W} {Ψ : V ≃ W} (h₁ : IsConjugate T T' Φ) (h₂ : IsConjugate T' T'' Ψ) :
    IsConjugate T T'' (Φ.trans Ψ) :=
  of_comm fun u => by
    simp only [Equiv.trans_apply]
    rw [h₁.comm, h₂.comm]

/-- Conjugacy is reflexive. -/
theorem refl (T : U → U) : IsConjugate T T (Equiv.refl U) := fun _ => rfl

/-- The square commutes for iterates: `Φ ∘ Tᵏ = T'ᵏ ∘ Φ` (the step in the solution to
Exercise 2.1.4). -/
theorem iterate_comm (h : IsConjugate T T' Φ) (k : ℕ) (u : U) : Φ (T^[k] u) = T'^[k] (Φ u) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', iterate_succ_apply', h.comm, ih]

/-- Exercise 2.1.1 (p. 43): `u` is a fixed point of `T` iff `Φu` is a fixed point of `T'`. -/
theorem isFixedPt_iff (h : IsConjugate T T' Φ) (u : U) : IsFixedPt T u ↔ IsFixedPt T' (Φ u) := by
  simp only [IsFixedPt]
  rw [h u, Equiv.symm_apply_eq]

/-- Proposition 2.1.1 (ii), p. 44: `v` is a fixed point of `T'` iff `Φ⁻¹v` is a fixed point of
`T`. -/
theorem isFixedPt_symm_iff (h : IsConjugate T T' Φ) (v : V) :
    IsFixedPt T' v ↔ IsFixedPt T (Φ.symm v) := by
  rw [h.isFixedPt_iff, Equiv.apply_symm_apply]

/-- Exercise 2.1.2 (p. 43): `Φ` restricts to a bijection from `fix(T)` to `fix(T')`. -/
def fixedPointsEquiv (h : IsConjugate T T' Φ) : fixedPoints T ≃ fixedPoints T' where
  toFun u := ⟨Φ u, (h.isFixedPt_iff u).1 u.2⟩
  invFun v := ⟨Φ.symm v, (h.isFixedPt_symm_iff v).1 v.2⟩
  left_inv u := Subtype.ext (Equiv.symm_apply_apply Φ u)
  right_inv v := Subtype.ext (Equiv.apply_symm_apply Φ v)

/-- Proposition 2.1.1 (iii), p. 44: the fixed-point sets have the same cardinality. -/
theorem cardinal_fixedPoints_eq (h : IsConjugate T T' Φ) :
    Cardinal.lift.{v} (Cardinal.mk (fixedPoints T)) =
      Cardinal.lift.{u} (Cardinal.mk (fixedPoints T')) :=
  Cardinal.lift_mk_eq'.2 ⟨h.fixedPointsEquiv⟩

/-- Proposition 2.1.1, "in particular" (p. 44): `T` has a unique fixed point iff `T'` does. -/
theorem existsUnique_fixedPt_iff (h : IsConjugate T T' Φ) :
    (∃! u, IsFixedPt T u) ↔ ∃! v, IsFixedPt T' v := by
  constructor
  · rintro ⟨u, hu, huniq⟩
    refine ⟨Φ u, (h.isFixedPt_iff u).1 hu, fun v hv => ?_⟩
    rw [← huniq (Φ.symm v) ((h.isFixedPt_symm_iff v).1 hv), Equiv.apply_symm_apply]
  · rintro ⟨v, hv, hvuniq⟩
    refine ⟨Φ.symm v, (h.isFixedPt_symm_iff v).1 hv, fun u hu => ?_⟩
    rw [← hvuniq (Φ u) ((h.isFixedPt_iff u).1 hu), Equiv.symm_apply_apply]

end IsConjugate

/-- Example 2.1.1 (p. 43): if `A = P⁻¹ D P` with `P` invertible, then `u ↦ Au` on `ℝⁿ` is
conjugate to `v ↦ Dv` under `Φ = P`. The book takes `D` diagonal (and complex); the conjugacy
needs neither. -/
theorem isConjugate_similar {n : ℕ} (P D : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P.det) :
    IsConjugate (fun u => (P⁻¹ * D * P) *ᵥ u) (fun v => D *ᵥ v)
      ⟨fun u => P *ᵥ u, fun v => P⁻¹ *ᵥ v,
        fun u => by
          change P⁻¹ *ᵥ (P *ᵥ u) = u
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec],
        fun v => by
          change P *ᵥ (P⁻¹ *ᵥ v) = v
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]⟩ :=
  IsConjugate.of_comm fun u => by
    simp only [Equiv.coe_fn_mk]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hP, Matrix.one_mul]

/-! ### Topological conjugacy (§2.1.1.2, p. 44) -/

/-- `(U, T)` and `(V, T')` are topologically conjugate under the homeomorphism `Φ`. -/
def IsTopConjugate [TopologicalSpace U] [TopologicalSpace V] (T : U → U) (T' : V → V)
    (Φ : U ≃ₜ V) : Prop :=
  IsConjugate T T' Φ.toEquiv

namespace IsTopConjugate

variable [TopologicalSpace U] [TopologicalSpace V] [TopologicalSpace W] {T : U → U} {T' : V → V}
  {Φ : U ≃ₜ V}

/-- Exercise 2.1.5 (p. 44): topological conjugacy is reflexive. -/
theorem refl (T : U → U) : IsTopConjugate T T (Homeomorph.refl U) := fun _ => rfl

/-- Exercise 2.1.5 (p. 44): topological conjugacy is symmetric. -/
theorem symm (h : IsTopConjugate T T' Φ) : IsTopConjugate T' T Φ.symm :=
  IsConjugate.symm h

/-- Exercise 2.1.5 (p. 44): topological conjugacy is transitive. -/
theorem trans {T'' : W → W} {Ψ : V ≃ₜ W} (h₁ : IsTopConjugate T T' Φ)
    (h₂ : IsTopConjugate T' T'' Ψ) : IsTopConjugate T T'' (Φ.trans Ψ) :=
  IsConjugate.trans h₁ h₂

/-- Exercise 2.1.4 (p. 44): `Tᵏu → u*` iff `T'ᵏ(Φu) → Φu*`. -/
theorem tendsto_iterate_iff (h : IsTopConjugate T T' Φ) (u u' : U) :
    Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u') ↔
      Tendsto (fun k : ℕ => T'^[k] (Φ u)) atTop (𝓝 (Φ u')) := by
  have : (fun k : ℕ => T'^[k] (Φ u)) = Φ ∘ fun k : ℕ => T^[k] u := by
    funext k
    exact (IsConjugate.iterate_comm h k u).symm
  rw [this, Φ.isInducing.tendsto_nhds_iff]

/-- Proposition 2.1.2 (p. 45): `T` is globally stable on `U` iff `T'` is globally stable on
`V`, and the fixed points correspond under `Φ`. -/
theorem globallyStable_iff (h : IsTopConjugate T T' Φ) : GloballyStable T ↔ GloballyStable T' := by
  constructor
  · rintro ⟨u', hfix, huniq, hlim⟩
    refine ⟨Φ u', (IsConjugate.isFixedPt_iff h u').1 hfix, fun v hv => ?_, fun v => ?_⟩
    · rw [← huniq (Φ.symm v) ((IsConjugate.isFixedPt_symm_iff h v).1 hv),
        Homeomorph.apply_symm_apply]
    · have := (h.tendsto_iterate_iff (Φ.symm v) u').1 (hlim _)
      simpa using this
  · rintro ⟨v', hfix, huniq, hlim⟩
    have h'' : IsTopConjugate T' T Φ.symm := h.symm
    refine ⟨Φ.symm v', (IsConjugate.isFixedPt_symm_iff h v').1 hfix, fun u hu => ?_, fun u => ?_⟩
    · rw [← huniq (Φ u) ((IsConjugate.isFixedPt_iff h u).1 hu), Homeomorph.symm_apply_apply]
    · have := (h''.tendsto_iterate_iff (Φ u) v').1 (hlim _)
      simpa using this

/-- Proposition 2.1.2 (ii), p. 45: the unique fixed points satisfy `û* = Φu*`. -/
theorem fixedPt_map (h : IsTopConjugate T T' Φ) {u' : U} (hu : IsFixedPt T u') :
    IsFixedPt T' (Φ u') :=
  (IsConjugate.isFixedPt_iff h u').1 hu

/-- Exercise 2.1.6 (p. 45): `u*` is locally stable for `(U, T)` iff `Φu*` is locally stable for
`(V, T')`. -/
theorem locallyStable_iff (h : IsTopConjugate T T' Φ) (u' : U) :
    LocallyStable T u' ↔ LocallyStable T' (Φ u') := by
  constructor
  · rintro ⟨O, hO, hu', hconv⟩
    refine ⟨Φ '' O, Φ.isOpenMap O hO, ⟨u', hu', rfl⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (h.tendsto_iterate_iff u u').1 (hconv u hu)
  · rintro ⟨O, hO, hu', hconv⟩
    refine ⟨Φ ⁻¹' O, hO.preimage Φ.continuous, hu', fun u hu => ?_⟩
    exact (h.tendsto_iterate_iff u u').2 (hconv (Φ u) hu)

end IsTopConjugate

/-- Example 2.1.2 (p. 44): `ln : (0, ∞) → ℝ` is a homeomorphism with inverse `exp`. -/
noncomputable def logHomeomorph : Ioi (0 : ℝ) ≃ₜ ℝ :=
  Real.expOrderIso.toHomeomorph.symm

theorem logHomeomorph_apply (u : Ioi (0 : ℝ)) : logHomeomorph u = Real.log u := by
  change Real.expOrderIso.symm u = Real.log u
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext (by rw [Real.coe_expOrderIso_apply, Real.exp_log u.2])

theorem logHomeomorph_symm_apply (y : ℝ) : (logHomeomorph.symm y : ℝ) = Real.exp y := by
  change ((Real.expOrderIso y : Ioi (0 : ℝ)) : ℝ) = Real.exp y
  exact Real.coe_expOrderIso_apply y

/-- Example 2.1.3 (p. 44), one direction: a nonsingular matrix `Φ` acts as a homeomorphism of
`ℝⁿ`. -/
noncomputable def matrixHomeomorph {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℝ) (hΦ : IsUnit Φ.det) :
    (Fin n → ℝ) ≃ₜ (Fin n → ℝ) where
  toFun u := Φ *ᵥ u
  invFun v := Φ⁻¹ *ᵥ v
  left_inv u := by
    change Φ⁻¹ *ᵥ (Φ *ᵥ u) = u
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Φ hΦ, Matrix.one_mulVec]
  right_inv v := by
    change Φ *ᵥ (Φ⁻¹ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Φ hΦ, Matrix.one_mulVec]
  continuous_toFun := (Matrix.mulVecLin Φ).continuous_of_finiteDimensional
  continuous_invFun := (Matrix.mulVecLin Φ⁻¹).continuous_of_finiteDimensional

/-- Example 2.1.3 (p. 44), the other direction: if `u ↦ Φu` is a bijection of `ℝⁿ` then `Φ`
is nonsingular (a singular matrix has a nonzero null vector). -/
theorem det_ne_zero_of_mulVec_injective {n : ℕ} (Φ : Matrix (Fin n) (Fin n) ℝ)
    (h : Injective fun u : Fin n → ℝ => Φ *ᵥ u) :
    Φ.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hΦv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  apply h
  simp only [hΦv, Matrix.mulVec_zero]

/-- Exercise 2.1.3 (p. 44): `Tu = Auᵅ` on `(0, ∞)` is topologically conjugate to
`T̂v = ln A + αv` on `ℝ` under `Φ = ln`. -/
theorem isTopConjugate_power {A α : ℝ} (hA : 0 < A) :
    IsTopConjugate
      (fun u : Ioi (0 : ℝ) => ⟨A * (u : ℝ) ^ α, mul_pos hA (Real.rpow_pos_of_pos u.2 α)⟩)
      (fun v : ℝ => Real.log A + α * v) logHomeomorph :=
  IsConjugate.of_comm fun u => by
    simp only [Homeomorph.coe_toEquiv, logHomeomorph_apply]
    rw [Real.log_mul hA.ne' (Real.rpow_pos_of_pos u.2 α).ne', Real.log_rpow u.2]

/-! ### Local stability (§2.1.2, p. 45) -/

/-- The iterates of `g(x) = x²` are `x^(2ᵏ)`. -/
theorem iterate_sq (x : ℝ) (k : ℕ) : (fun y : ℝ => y ^ 2)^[k] x = x ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', ih, ← pow_mul, pow_succ]

/-- Example 2.1.4 (p. 45): `0` is a locally stable fixed point of `g(x) = x²`, since `|x| < 1`
implies `gᵗ(x) → 0`. -/
theorem locallyStable_sq_zero : LocallyStable (fun y : ℝ => y ^ 2) 0 := by
  refine ⟨Ioo (-1) 1, isOpen_Ioo, by norm_num, fun x hx => ?_⟩
  simp only [iterate_sq]
  have habs : |x| < 1 := abs_lt.2 ⟨hx.1, hx.2⟩
  have h1 : Tendsto (fun k : ℕ => |x| ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg x) habs
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h3 : Tendsto (fun k : ℕ => |x| ^ (2 ^ k)) atTop (𝓝 0) := h1.comp h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs, abs_pow] using h3

/-- Example 2.1.4 (p. 45): `1` is a fixed point of `g(x) = x²` that is not locally stable, since
`gᵗ(x) → ∞` for every `x > 1`. -/
theorem not_locallyStable_sq_one : ¬ LocallyStable (fun y : ℝ => y ^ 2) 1 := by
  rintro ⟨O, hO, h1, hconv⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 1 h1
  set x : ℝ := 1 + ε / 2 with hx
  have hxO : x ∈ O := hball (by
    rw [Metric.mem_ball, Real.dist_eq, hx]
    rw [show (1 + ε / 2 - 1) = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith)
  have hlim := hconv x hxO
  simp only [iterate_sq] at hlim
  have hgt : 1 < x := by rw [hx]; linarith
  have hdiv : Tendsto (fun k : ℕ => x ^ (2 ^ k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact not_tendsto_atTop_of_tendsto_nhds hlim hdiv

/-- The derivative criterion sketched on p. 45: if `g` is differentiable with continuous
derivative at a fixed point `x*` and `|g'(x*)| < 1`, then `x*` is locally stable. The proof is the
one the book describes: near `x*`, `g` is a contraction of modulus `λ ∈ (|g'(x*)|, 1)`, by the
mean value theorem. -/
theorem locallyStable_of_abs_deriv_lt_one {g g' : ℝ → ℝ} {x' : ℝ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hcont : ContinuousAt g' x') (hfix : g x' = x')
    (hlt : |g' x'| < 1) : LocallyStable g x' := by
  obtain ⟨L, hL1, hL2⟩ := exists_between hlt
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL1.le
  -- a ball on which `|g'| ≤ L`
  have hev : ∀ᶠ x in 𝓝 x', |g' x| < L := hcont.abs.eventually (gt_mem_nhds hL1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hbound : ∀ x ∈ Metric.ball x' δ, ‖g' x‖ ≤ L := fun x hx => (hball (Metric.mem_ball.1 hx)).le
  have hderiv : ∀ x ∈ Metric.ball x' δ, HasDerivWithinAt g (g' x) (Metric.ball x' δ) x :=
    fun x _ => (hg x).hasDerivWithinAt
  -- `g` is `L`-Lipschitz on the ball, and fixes `x'`
  have hlip : ∀ x ∈ Metric.ball x' δ, |g x - x'| ≤ L * |x - x'| := by
    intro x hx
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_ball x' δ)
      (Metric.mem_ball_self hδ) hx
    rwa [hfix, Real.norm_eq_abs, Real.norm_eq_abs] at this
  have hmaps : ∀ x ∈ Metric.ball x' δ, g x ∈ Metric.ball x' δ := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx ⊢
    calc |g x - x'| ≤ L * |x - x'| := hlip x hx
      _ ≤ 1 * |x - x'| := mul_le_mul_of_nonneg_right hL2.le (abs_nonneg _)
      _ < δ := by linarith
  have hiter : ∀ x ∈ Metric.ball x' δ, ∀ k : ℕ,
      g^[k] x ∈ Metric.ball x' δ ∧ |g^[k] x - x'| ≤ L ^ k * |x - x'| := by
    intro x hx k
    induction k with
    | zero => exact ⟨by simpa using hx, by simp⟩
    | succ k ih =>
      rw [iterate_succ_apply']
      refine ⟨hmaps _ ih.1, ?_⟩
      calc |g (g^[k] x) - x'| ≤ L * |g^[k] x - x'| := hlip _ ih.1
        _ ≤ L * (L ^ k * |x - x'|) := mul_le_mul_of_nonneg_left ih.2 hL0
        _ = L ^ (k + 1) * |x - x'| := by ring
  refine ⟨Metric.ball x' δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, fun x hx => ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  refine squeeze_zero (fun _ => abs_nonneg _) (fun k => (hiter x hx k).2) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL2).mul_const |x - x'|

end SargentStachurski.OperatorsFixedPoints
