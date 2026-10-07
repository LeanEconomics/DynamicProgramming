/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.OrderTheory
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Conjugate dynamical systems

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.1.1 (pp. 148–151).

* Conjugacy (§5.1.1.1): `F` a bijection with `F ∘ S = Ŝ ∘ F`, i.e. `Function.Semiconj F S Ŝ`.
  **Proposition 5.1.1** (iterates, fixed points, unique fixed points; part (iv) is
  **Exercise 5.1.1**), **Example 5.1.1** (log-linearization) and **Example 5.1.2**
  (diagonalization).
* Topological conjugacy (§5.1.1.2): **Proposition 5.1.2** (global stability transfers) and
  **Example 5.1.3** (`Aᵏx → 0` for all `x` iff every eigenvalue of `A` has modulus below one).
* Order conjugacy (§5.1.1.3): **Exercise 5.1.2** (an equivalence relation) and **Lemma 5.1.3**
  (order stability and strong order stability transfer; **Exercise 5.1.3**).
-/

open Set Function Filter Topology
open scoped Matrix

namespace SargentStachurski.ADPTransformations

/-! ### Conjugacy -/

/-- `v` is the unique fixed point of `S`. -/
def IsUniqueFixed {V : Type*} (S : V → V) (v : V) : Prop := S v = v ∧ ∀ w, S w = w → w = v

/-- `(V, S)` and `(V̂, Ŝ)` are conjugate under the bijection `F` (§5.1.1.1): `F ∘ S = Ŝ ∘ F`. -/
def IsConjugate {V W : Type*} (F : V ≃ W) (S : V → V) (Sh : W → W) : Prop := Semiconj F S Sh

namespace IsConjugate

variable {V W : Type*} {F : V ≃ W} {S : V → V} {Sh : W → W}

/-- The inverse conjugacy: `F⁻¹ ∘ Ŝ = S ∘ F⁻¹`. -/
theorem symm (h : IsConjugate F S Sh) : IsConjugate F.symm Sh S := fun w => by
  apply F.injective
  rw [Equiv.apply_symm_apply, h (F.symm w), Equiv.apply_symm_apply]

/-- **Proposition 5.1.1 (i)** (p. 149): `Sⁿ = F⁻¹ Ŝⁿ F`. -/
theorem iterate (h : IsConjugate F S Sh) (n : ℕ) (v : V) : S^[n] v = F.symm (Sh^[n] (F v)) := by
  rw [← (Semiconj.iterate_right h n) v, Equiv.symm_apply_apply]

/-- **Proposition 5.1.1 (ii)**: `v` is fixed for `S` iff `Fv` is fixed for `Ŝ`. -/
theorem fixed_iff (h : IsConjugate F S Sh) (v : V) : S v = v ↔ Sh (F v) = F v := by
  rw [← h v, F.apply_eq_iff_eq]

/-- **Proposition 5.1.1 (iii)**: `v̂` is fixed for `Ŝ` iff `F⁻¹v̂` is fixed for `S`. -/
theorem fixed_iff_symm (h : IsConjugate F S Sh) (w : W) : Sh w = w ↔ S (F.symm w) = F.symm w :=
  h.symm.fixed_iff w

/-- **Proposition 5.1.1 (iv)** (p. 149) and **Exercise 5.1.1**: `v` is the unique fixed point
of `S` iff `Fv` is the unique fixed point of `Ŝ`. -/
theorem isUniqueFixed_iff (h : IsConjugate F S Sh) (v : V) :
    IsUniqueFixed S v ↔ IsUniqueFixed Sh (F v) := by
  constructor
  · rintro ⟨hv, huniq⟩
    refine ⟨(h.fixed_iff v).1 hv, fun w hw => ?_⟩
    rw [← huniq _ ((h.fixed_iff_symm w).1 hw), Equiv.apply_symm_apply]
  · rintro ⟨hv, huniq⟩
    refine ⟨(h.fixed_iff v).2 hv, fun w hw => F.injective (huniq _ ((h.fixed_iff w).1 hw))⟩

end IsConjugate

/-- **Example 5.1.1** (p. 149): `Sx = ax + b` on `ℝ` is conjugate under `exp` to its
log-linearization `Ŝy = e^b y^a` on `(0, ∞)`. -/
theorem example_5_1_1 (a b : ℝ) :
    IsConjugate Real.expOrderIso.toEquiv (fun x => a * x + b)
      (fun y => ⟨Real.exp b * (y : ℝ) ^ a, mul_pos (Real.exp_pos b) (Real.rpow_pos_of_pos y.2 a)⟩)
      := fun x => by
  apply Subtype.ext
  change Real.exp (a * x + b) = Real.exp b * Real.exp x ^ a
  rw [← Real.exp_mul, ← Real.exp_add, mul_comm x a, add_comm]

/-! ### Diagonalization -/

/-- The coordinate change `x ↦ E⁻¹x` for an invertible matrix `E`. -/
def coordChange {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) :
    (m → ℝ) ≃ (m → ℝ) where
  toFun x := (↑E⁻¹ : Matrix m m ℝ) *ᵥ x
  invFun y := (↑E : Matrix m m ℝ) *ᵥ y
  left_inv x := by dsimp only; rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  right_inv y := by dsimp only; rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

/-- **Example 5.1.2** (p. 149): if `A = EDE⁻¹`, then `(ℝᵐ, A)` and `(ℝᵐ, D)` are conjugate under
`F = E⁻¹`. -/
theorem example_5_1_2 {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) (d : m → ℝ)
    {A : Matrix m m ℝ}
    (hA : A = (↑E : Matrix m m ℝ) * Matrix.diagonal d * (↑E⁻¹ : Matrix m m ℝ)) :
    IsConjugate (coordChange E) (A *ᵥ ·) (Matrix.diagonal d *ᵥ ·) := fun x => by
  change (↑E⁻¹ : Matrix m m ℝ) *ᵥ (A *ᵥ x) = Matrix.diagonal d *ᵥ ((↑E⁻¹ : Matrix m m ℝ) *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Units.inv_mul, Matrix.one_mul]

/-! ### Topological conjugacy -/

/-- `(V, S)` and `(V̂, Ŝ)` are topologically conjugate (§5.1.1.2): conjugate under a
homeomorphism. -/
def IsTopConjugate {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] (F : V ≃ₜ W)
    (S : V → V) (Sh : W → W) : Prop := Semiconj F S Sh

theorem IsTopConjugate.symm {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] {F : V ≃ₜ W}
    {S : V → V} {Sh : W → W} (h : IsTopConjugate F S Sh) : IsTopConjugate F.symm Sh S :=
  IsConjugate.symm (F := F.toEquiv) h

/-- One direction of Proposition 5.1.2. -/
theorem IsTopConjugate.globallyStable {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    {F : V ≃ₜ W} {S : V → V} {Sh : W → W} (h : IsTopConjugate F S Sh) (hS : GloballyStable S) :
    GloballyStable Sh := by
  obtain ⟨u, hu, huniq, hlim⟩ := hS
  have hc : IsConjugate F.toEquiv S Sh := h
  refine ⟨F u, (hc.fixed_iff u).1 hu, fun w hw => ?_, fun w => ?_⟩
  · have := huniq _ ((hc.fixed_iff_symm w).1 hw)
    rw [← this]
    exact (F.apply_symm_apply w).symm
  · have h1 := (F.continuous.tendsto u).comp (hlim (F.symm w))
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [(Semiconj.iterate_right h k) (F.symm w), F.apply_symm_apply]

/-- **Proposition 5.1.2** (p. 150): if `(V, S)` and `(V̂, Ŝ)` are topologically conjugate, `S` is
globally stable iff `Ŝ` is. -/
theorem proposition_5_1_2 {V W : Type*} [TopologicalSpace V] [TopologicalSpace W] {F : V ≃ₜ W}
    {S : V → V} {Sh : W → W} (h : IsTopConjugate F S Sh) : GloballyStable S ↔ GloballyStable Sh :=
  ⟨h.globallyStable, h.symm.globallyStable⟩

/-- `x ↦ E⁻¹x` as a homeomorphism of `ℝᵐ`. -/
def coordHomeo {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) :
    (m → ℝ) ≃ₜ (m → ℝ) where
  toEquiv := coordChange E
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := by
    change Continuous fun y => (↑E : Matrix m m ℝ) *ᵥ y
    exact Continuous.matrix_mulVec continuous_const continuous_id

theorem iterate_diagonal_mulVec {m : Type*} [Fintype m] [DecidableEq m] (d : m → ℝ) (k : ℕ)
    (x : m → ℝ) :
    (Matrix.diagonal d *ᵥ ·)^[k] x = fun i => d i ^ k * x i := by
  induction k with
  | zero => funext i; simp
  | succ k ih =>
    rw [iterate_succ_apply', ih]
    funext i
    rw [Matrix.mulVec_diagonal, pow_succ]
    ring

/-- The diagonal system is globally stable iff every diagonal entry has modulus below one. -/
theorem globallyStable_diagonal_iff {m : Type*} [Fintype m] [DecidableEq m] (d : m → ℝ) :
    GloballyStable (Matrix.diagonal d *ᵥ ·) ↔ ∀ i, |d i| < 1 := by
  constructor
  · rintro ⟨u, hu, -, hlim⟩ i
    -- the fixed point is `0`, and `Dᵏ e_i → 0` forces `|d i| < 1`
    have hu0 : u = 0 := tendsto_nhds_unique (hlim 0)
      (tendsto_const_nhds.congr fun k => (iterate_fixed (Matrix.mulVec_zero _) k).symm)
    have h := tendsto_pi_nhds.1 (hlim (Pi.single i 1)) i
    rw [hu0] at h
    simp only [iterate_diagonal_mulVec, Pi.single_eq_same, mul_one, Pi.zero_apply] at h
    exact tendsto_pow_atTop_nhds_zero_iff.1 h
  · intro hd
    have hlim : ∀ v : m → ℝ, Tendsto (fun k : ℕ => (Matrix.diagonal d *ᵥ ·)^[k] v) atTop (𝓝 0) :=
      fun v => by
        simp only [iterate_diagonal_mulVec]
        refine tendsto_pi_nhds.2 fun i => ?_
        simpa using (tendsto_pow_atTop_nhds_zero_iff.2 (hd i)).mul_const (v i)
    refine ⟨0, Matrix.mulVec_zero _, fun v hv => ?_, hlim⟩
    have hv' : ∀ k : ℕ, (Matrix.diagonal d *ᵥ ·)^[k] v = v := fun k => hv.iterate k
    exact tendsto_nhds_unique (tendsto_const_nhds.congr fun k => (hv' k).symm) (hlim v)

/-- **Example 5.1.3** (p. 150): if `A = EDE⁻¹` with `D = diag(d)`, then `A` is globally stable on
`ℝᵐ` iff every eigenvalue `dᵢ` of `A` has modulus below one; in particular `Aᵏv → 0` for all `v`
iff `|dᵢ| < 1` for all `i`. -/
theorem example_5_1_3 {m : Type*} [Fintype m] [DecidableEq m] (E : (Matrix m m ℝ)ˣ) (d : m → ℝ)
    {A : Matrix m m ℝ}
    (hA : A = (↑E : Matrix m m ℝ) * Matrix.diagonal d * (↑E⁻¹ : Matrix m m ℝ)) :
    (GloballyStable (A *ᵥ ·) ↔ ∀ i, |d i| < 1) ∧
      ((∀ v : m → ℝ, Tendsto (fun k : ℕ => (A *ᵥ ·)^[k] v) atTop (𝓝 0)) ↔ ∀ i, |d i| < 1) := by
  have hc : IsTopConjugate (coordHomeo E) (A *ᵥ ·) (Matrix.diagonal d *ᵥ ·) :=
    example_5_1_2 E d hA
  have h1 := (proposition_5_1_2 hc).trans (globallyStable_diagonal_iff d)
  refine ⟨h1, ⟨fun h => h1.1 ⟨0, Matrix.mulVec_zero _, fun v hv => ?_, h⟩, fun h => ?_⟩⟩
  · exact tendsto_nhds_unique (tendsto_const_nhds.congr fun k => (hv.iterate k).symm) (h v)
  · obtain ⟨u, hu, -, hlim⟩ := h1.2 h
    have hu0 : u = 0 := tendsto_nhds_unique (hlim 0)
      (tendsto_const_nhds.congr fun k => (iterate_fixed (Matrix.mulVec_zero A) k).symm)
    exact fun v => hu0 ▸ hlim v

/-! ### Order conjugacy -/

/-- `(V, S)` and `(V̂, Ŝ)` are order conjugate under `F` (§5.1.1.3): conjugate under an order
isomorphism `F`. -/
def IsOrderConjugate {V W : Type*} [PartialOrder V] [PartialOrder W] (F : V ≃o W) (S : V → V)
    (Sh : W → W) : Prop := Semiconj F S Sh

/-- **Exercise A.1.15**: order isomorphisms preserve `↑`. -/
theorem orderIso_increasesTo {V W : Type*} [PartialOrder V] [PartialOrder W] (F : V ≃o W)
    {f : ℕ → V} {v : V} (h : IncreasesTo f v) : IncreasesTo (F ∘ f) (F v) :=
  ⟨F.monotone.comp h.1, by
    rw [Set.range_comp]; exact (F.isLUB_image' (s := range f)).2 h.2⟩

/-- **Exercise A.1.15**: order isomorphisms preserve `↓`. -/
theorem orderIso_decreasesTo {V W : Type*} [PartialOrder V] [PartialOrder W] (F : V ≃o W)
    {f : ℕ → V} {v : V} (h : DecreasesTo f v) : DecreasesTo (F ∘ f) (F v) :=
  ⟨F.monotone.comp_antitone h.1, by
    rw [Set.range_comp]; exact (F.isGLB_image' (s := range f)).2 h.2⟩

namespace IsOrderConjugate

variable {V W U : Type*} [PartialOrder V] [PartialOrder W] [PartialOrder U]

/-- **Exercise 5.1.2** (p. 151), reflexivity. -/
theorem refl (S : V → V) : IsOrderConjugate (OrderIso.refl V) S S := fun _ => rfl

/-- **Exercise 5.1.2**, symmetry. -/
theorem symm {F : V ≃o W} {S : V → V} {Sh : W → W} (h : IsOrderConjugate F S Sh) :
    IsOrderConjugate F.symm Sh S :=
  IsConjugate.symm (F := F.toEquiv) h

/-- **Exercise 5.1.2**, transitivity. -/
theorem trans {F : V ≃o W} {G : W ≃o U} {S : V → V} {Sh : W → W} {Sk : U → U}
    (h : IsOrderConjugate F S Sh) (h' : IsOrderConjugate G Sh Sk) :
    IsOrderConjugate (F.trans G) S Sk := fun v => by
  change G (F (S v)) = Sk (G (F v))
  rw [h v, h' (F v)]

variable {F : V ≃o W} {S : V → V} {Sh : W → W}

theorem orderStable (h : IsOrderConjugate F S Sh) (hS : OrderStable S) : OrderStable Sh := by
  obtain ⟨u, hu, -, hup, hdown⟩ := hS
  have hc : IsConjugate F.toEquiv S Sh := h
  refine orderStable_of_up_down ((hc.fixed_iff u).1 hu) (fun w hw => ?_) fun w hw => ?_
  · have h1 : F.symm w ≤ S (F.symm w) := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    simpa using F.monotone (hup _ h1)
  · have h1 : S (F.symm w) ≤ F.symm w := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    simpa using F.monotone (hdown _ h1)

theorem stronglyOrderStable (h : IsOrderConjugate F S Sh) (hS : StronglyOrderStable S) :
    StronglyOrderStable Sh := by
  obtain ⟨u, hu, huniq, hup, hdown⟩ := hS
  have hc : IsConjugate F.toEquiv S Sh := h
  have hit : ∀ w : W, (fun n => Sh^[n] w) = F ∘ fun n => S^[n] (F.symm w) := fun w => by
    funext n
    simp only [Function.comp_apply]
    rw [(Semiconj.iterate_right h n) (F.symm w), F.apply_symm_apply]
  refine ⟨F u, (hc.fixed_iff u).1 hu, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [← huniq _ ((hc.fixed_iff_symm w).1 hw)]
    exact (F.apply_symm_apply w).symm
  · have h1 : F.symm w ≤ S (F.symm w) := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    rw [hit]
    exact orderIso_increasesTo F (hup _ h1)
  · have h1 : S (F.symm w) ≤ F.symm w := by
      have := F.symm.monotone hw
      rwa [h.symm w] at this
    rw [hit]
    exact orderIso_decreasesTo F (hdown _ h1)

/-- **Lemma 5.1.3** (p. 151) and **Exercise 5.1.3**: if `(V, S)` and `(V̂, Ŝ)` are order
conjugate, then (i) `S` is order stable iff `Ŝ` is, and (ii) `S` is strongly order stable iff
`Ŝ` is. -/
theorem lemma_5_1_3 (h : IsOrderConjugate F S Sh) :
    (OrderStable S ↔ OrderStable Sh) ∧ (StronglyOrderStable S ↔ StronglyOrderStable Sh) :=
  ⟨⟨h.orderStable, h.symm.orderStable⟩, ⟨h.stronglyOrderStable, h.symm.stronglyOrderStable⟩⟩

end IsOrderConjugate

end SargentStachurski.ADPTransformations
