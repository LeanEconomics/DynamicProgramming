/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDynamicProgramming.MixedStrategies

/-!
# Min-optimality by order duality

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §9.2.3 (pp. 305–306).

The dual of an ADP `A = (V, {T_σ})` is `A^∂ = (V^∂, {T_σ})`, the same operators on the order dual.
Min-greedy policies, the Bellman min-operator, min-stability, min-optimal policies and min-HPI for
`A` are the max-greedy policies, Bellman operator, max-stability, optimal policies and HPI of
`A^∂`.

* Exercise 9.2.7 (i)–(vi), with `A^{∂∂} = A`.
* **Theorem 9.2.11 (min-optimality)**: for min-stable `A`, the min-value function exists, is the
  unique solution of the Bellman min-equation, Bellman's principle of min-optimality holds, a
  min-optimal policy exists, and for finite `Σ` min-HPI terminates at a min-optimal policy.
* For a globally stable RDP `R`, `A_R` is min-stable (the ADP form of Theorem 8.3.7).
-/

open Function Set

namespace SargentStachurski.AbstractDynamicProgramming

namespace ADP

variable {V P : Type*} [PartialOrder V] (A : ADP V P)

/-- The dual ADP `A^∂ = (V^∂, {T_σ})` (p. 305). -/
def dual : ADP Vᵒᵈ P where
  T σ v := OrderDual.toDual (A.T σ (OrderDual.ofDual v))
  exists_greedy v := A.exists_minGreedy (OrderDual.ofDual v)
  exists_minGreedy v := A.exists_greedy (OrderDual.ofDual v)

/-- `A^{∂∂} = A`. -/
theorem dual_dual : A.dual.dual = A := rfl

/-- `σ` is `v`-min-greedy: `T_σ v ≼ T_τ v` for all `τ` (p. 305). -/
def IsMinGreedy (v : V) (σ : P) : Prop := ∀ τ, A.T σ v ≤ A.T τ v

/-- The Bellman min-operator `Tv = ⋀_σ T_σ v` (p. 305). -/
noncomputable def minBellman (v : V) : V := OrderDual.ofDual (A.dual.bellman (OrderDual.toDual v))

/-- `σ` is min-optimal: `v_σ` is the least element of `V_Σ`. -/
def IsMinOptimal (hw : A.WellPosed) (σ : P) : Prop := ∀ τ, A.vσ hw σ ≤ A.vσ hw τ

/-- `A` is min-stable (p. 305): order stable, and the Bellman min-operator has a fixed point. -/
def IsMinStable : Prop := A.IsOrderStable ∧ ∃ v, IsFixedPt A.minBellman v

/-- **Exercise 9.2.7 (i)** (p. 306): `σ` is `v`-min-greedy for `A` iff it is `v`-greedy for
`A^∂`. -/
theorem isMinGreedy_iff (v : V) (σ : P) :
    A.IsMinGreedy v σ ↔ A.dual.IsGreedy (OrderDual.toDual v) σ := Iff.rfl

/-- **Exercise 9.2.7 (ii)** (p. 306): the Bellman min-operator is the least element of
`{T_σ v}`, and `σ` is `v`-min-greedy iff `T_σ v = Tv`. -/
theorem isLeast_minBellman (v : V) : IsLeast (range fun σ => A.T σ v) (A.minBellman v) :=
  ⟨⟨A.dual.greedy (OrderDual.toDual v), rfl⟩, by
    rintro _ ⟨τ, rfl⟩
    exact A.dual.T_le_bellman τ (OrderDual.toDual v)⟩

theorem isMinGreedy_iff_eq (v : V) (σ : P) : A.IsMinGreedy v σ ↔ A.T σ v = A.minBellman v :=
  A.dual.isGreedy_iff (OrderDual.toDual v) σ

/-- **Exercise 9.2.7 (iv)** (p. 306): `A` is order stable iff `A^∂` is. -/
theorem isOrderStable_dual_iff : A.dual.IsOrderStable ↔ A.IsOrderStable :=
  forall_congr' fun σ => orderStable_dual_iff (A.T σ)

/-- Well-posedness transfers to the dual. -/
theorem WellPosed.dual {A : ADP V P} (hw : A.WellPosed) : A.dual.WellPosed := hw

/-- The `σ`-value functions of `A^∂` are those of `A`. -/
theorem dual_vσ {A : ADP V P} (hw : A.WellPosed) (σ : P) :
    OrderDual.ofDual (A.dual.vσ hw.dual σ) = A.vσ hw σ :=
  eq_vσ_of_isFixedPt hw (isFixedPt_vσ (A := A.dual) hw.dual σ)

/-- **Exercise 9.2.7 (v)** (p. 306): `A` is min-stable iff `A^∂` is max-stable. -/
theorem isMinStable_iff : A.IsMinStable ↔ A.dual.IsMaxStable := by
  rw [IsMinStable, IsMaxStable, isOrderStable_dual_iff]
  exact and_congr Iff.rfl ⟨fun ⟨v, hv⟩ => ⟨OrderDual.toDual v, congrArg OrderDual.toDual hv.eq⟩,
    fun ⟨v, hv⟩ => ⟨OrderDual.ofDual v, congrArg OrderDual.ofDual hv.eq⟩⟩

/-- **Exercise 9.2.7 (vi)** (p. 306): `σ` is min-optimal for `A` iff it is (max-)optimal for
`A^∂`. -/
theorem isMinOptimal_iff {A : ADP V P} (hw : A.WellPosed) (σ : P) :
    A.IsMinOptimal hw σ ↔ A.dual.IsOptimal hw.dual σ := by
  refine forall_congr' fun τ => ?_
  rw [← dual_vσ hw σ, ← dual_vσ hw τ]
  rfl

/-- **Theorem 9.2.11 (min-optimality)** (p. 305): if `A` is min-stable, then (i) `V_Σ` has a
least element `v_*`, (ii) `v_*` is the unique solution of the Bellman min-equation, (iii) `A` obeys
Bellman's principle of min-optimality and (iv) a min-optimal policy exists. If moreover `Σ` is
finite, min-HPI (HPI for `A^∂`, whose greedy policies are the min-greedy policies of `A`)
terminates at a min-optimal policy. -/
theorem minOptimality {A : ADP V P} (h : A.IsMinStable) :
    ∃ vmin, IsLeast (range (A.vσ h.1.wellPosed)) vmin ∧
      (∀ v, IsFixedPt A.minBellman v ↔ v = vmin) ∧
      (∀ σ, A.IsMinOptimal h.1.wellPosed σ ↔ A.IsMinGreedy vmin σ) ∧
      ∃ σ, A.IsMinOptimal h.1.wellPosed σ := by
  have hd := (A.isMinStable_iff).1 h
  have hw := h.1.wellPosed
  obtain ⟨w, hgr, hfix, hprin, ⟨σ0, hσ0⟩⟩ := hd.optimality
  have hvd : ∀ σ, A.dual.vσ hd.1.wellPosed σ = OrderDual.toDual (A.vσ hw σ) := fun σ =>
    congrArg OrderDual.toDual (dual_vσ hw σ)
  refine ⟨OrderDual.ofDual w, ⟨?_, ?_⟩, fun v => ?_, fun σ => ?_, σ0, ?_⟩
  · obtain ⟨σ, hσ⟩ := hgr.1
    exact ⟨σ, by rw [← hσ, hvd]; rfl⟩
  · rintro _ ⟨τ, rfl⟩
    have := hgr.2 ⟨τ, rfl⟩
    rw [hvd] at this
    exact this
  · have := hfix (OrderDual.toDual v)
    constructor
    · intro hv
      exact congrArg OrderDual.ofDual (this.1 (congrArg OrderDual.toDual hv.eq))
    · intro hv
      have h2 := (this.2 (congrArg OrderDual.toDual hv))
      exact congrArg OrderDual.ofDual h2.eq
  · rw [isMinOptimal_iff hw, isMinGreedy_iff]
    exact hprin σ
  · exact (isMinOptimal_iff hw σ0).2 hσ0

/-- Theorem 9.2.11, final claim: for finite `Σ`, min-HPI from any `σ₀` reaches a repeated value,
and the returned policy is min-optimal. -/
theorem minHpi_terminates [Finite P] {A : ADP V P} (h : A.IsOrderStable) (σ₀ : P) :
    ∃ k, A.dual.hpiValue h.wellPosed.dual σ₀ (k + 1) = A.dual.hpiValue h.wellPosed.dual σ₀ k ∧
      A.IsMinOptimal h.wellPosed (A.dual.hpiPolicy h.wellPosed.dual σ₀ (k + 1)) := by
  have hd : A.dual.IsOrderStable := (A.isOrderStable_dual_iff).2 h
  obtain ⟨k, hk, -, hopt⟩ := hd.hpi_terminates σ₀
  exact ⟨k, hk, (isMinOptimal_iff h.wellPosed _).2 hopt⟩

/-- Min-HPI chooses min-greedy policies: `σₖ₊₁` is `v_{σₖ}`-min-greedy for `A`. -/
theorem minHpi_isMinGreedy {A : ADP V P} (hw : A.WellPosed) (σ₀ : P) (k : ℕ) :
    A.IsMinGreedy (OrderDual.ofDual (A.dual.hpiValue hw.dual σ₀ k))
      (A.dual.hpiPolicy hw.dual σ₀ (k + 1)) :=
  A.dual.isGreedy_greedy _

end ADP

/-- For a globally stable RDP `R`, the ADP `A_R` is min-stable, so Theorem 9.2.11 applies (the
ADP form of Theorem 8.3.7). -/
theorem RDP.toADP_isMinStable {X A : Type*} [Fintype X] [Fintype A] {R : RDP X A}
    (hR : R.IsGloballyStable) : R.toADP.IsMinStable := by
  have := R.policy_nonempty
  have hs := RDP.toADP_isOrderStable hR
  exact (R.toADP.isMinStable_iff).2 ((R.toADP.isOrderStable_dual_iff).2 hs).isMaxStable

end SargentStachurski.AbstractDynamicProgramming
