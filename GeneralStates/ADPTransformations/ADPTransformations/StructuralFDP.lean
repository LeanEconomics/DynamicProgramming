/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.FactoredDP
import ADPTransformations.StructuralEstimation

/-!
# Structural estimation via transforms

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.3.2 (pp. 176–178).

With `(Fv)(x, a) = ∫ v(x')P(x, a, dx')` (5.28) and `(G_σ g)(x) = r(x, σ(x)) + βg(x, σ(x))`
(5.29), `(bX, F, bG, 𝔾)` is an order-preserving FDP (`seFDP`): a measurable greatest `G_σ g`
exists by Exercise 4.2.4. Its subordinate ADP is the post-action model (4.20) of §4.2.3
(`seFDP_sub`); its primary ADP is the discrete choice model
`(T_σ v)(x) = r(x, σ(x)) + β ∫ v(x')P(x, σ(x), dx')`, whose Bellman operator is
`(Tv)(x) = max_a {r(x, a) + β ∫ v(x')P(x, a, dx')}` (`seFDP_primary_bellman`).

`section_5_3_2`: by Proposition 4.2.4 and Theorem 5.2.13 the fundamental optimality properties
hold for the discrete choice model, its optimal policies are optimal for the post-action model,
and a policy is optimal as soon as `σ(x) ∈ argmax_a {r(x, a) + βg*(x, a)}`, `g*` the post-action
value function.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPTransformations

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Finite A] [Nonempty A]

/-- The FDP `(bX, F, bG, 𝔾)` of §5.3.2. -/
noncomputable def seFDP (r : BM (X × A)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (P : Kernel (X × A) X) [IsMarkovKernel P] : FDP (BM X) (BM (X × A)) (SEPolicy X A) where
  F := expectOp P
  G := (postActionEU r β hβ0 hβ1 P).H
  greatest g := by
    have := Fintype.ofFinite A
    let : LinearOrder A := LinearOrder.lift' (Fintype.equivFin A) (Fintype.equivFin A).injective
    exact ⟨_, (postActionEU r β hβ0 hβ1 P).H_le_greedy g⟩
  nonempty := ⟨⟨fun _ => Classical.arbitrary A, measurable_const⟩⟩

variable (r : BM (X × A)) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : Kernel (X × A) X)
  [IsMarkovKernel P]

theorem seFDP_isOrderPreserving : (seFDP r β hβ0 hβ1 P).IsOrderPreserving :=
  ⟨(isCEOperator_expectOp P).1, (postActionEU r β hβ0 hβ1 P).H_mono⟩

theorem seFDP_monotonic : (seFDP r β hβ0 hβ1 P).Monotonic :=
  Or.inl (seFDP_isOrderPreserving r hβ0 hβ1 P)

/-- The subordinate ADP of `(bX, F, bG, 𝔾)` is the post-action model `(bG, 𝕋̂_SE)` (4.20). -/
theorem seFDP_sub : (seFDP r β hβ0 hβ1 P).sub (seFDP_monotonic r hβ0 hβ1 P) =
    (postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P) := rfl

/-- The primary ADP is the discrete choice model
`(T_σ v)(x) = r(x, σ(x)) + β ∫ v(x')P(x, σ(x), dx')`. -/
theorem seFDP_primary_T (σ : SEPolicy X A) (v : BM X) (x : X) :
    (((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).T σ v).toFun x =
      r.toFun (x, σ.1 x) + β * ∫ x', v.toFun x' ∂(P (x, σ.1 x)) := rfl

/-- The Bellman operator of the discrete choice model:
`(Tv)(x) = max_a {r(x, a) + β ∫ v(x')P(x, a, dx')}`. -/
theorem seFDP_primary_bellman [Fintype A] (v : BM X) (x : X) :
    (((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).bellman v).toFun x =
      Finset.univ.sup' Finset.univ_nonempty fun a =>
        r.toFun (x, a) + β * ∫ x', v.toFun x' ∂(P (x, a)) := by
  rw [FDP.primary_bellman]
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun a _ => ?_)
  · exact Finset.le_sup' (fun a => r.toFun (x, a) + β * ∫ x', v.toFun x' ∂(P (x, a)))
      (Finset.mem_univ (((seFDP r β hβ0 hβ1 P).gsel (expectOp P v)).1 x))
  · exact (seFDP r β hβ0 hβ1 P).G_le_Gsup ⟨fun _ => a, measurable_const⟩ (expectOp P v) x

/-- §5.3.2 (p. 177): for the discrete choice model `(bX, 𝕋_SE)`, the fundamental optimality
properties hold; its optimal policies are optimal for the post-action model `(bG, 𝕋̂_SE)`; and if
`g*` is the post-action value function, any measurable `σ` with
`σ(x) ∈ argmax_a {r(x, a) + βg*(x, a)}` at every `x` is optimal. -/
theorem section_5_3_2 [Nonempty X] :
    ∃ (hw : ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).WellPosed)
      (hw' : ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).WellPosed),
      ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).FundamentalOptimality hw ∧
      (∀ σ, ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).IsOptimal hw σ →
        ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).IsOptimal hw' σ) ∧
      ∀ gstar σ, ((postActionEU r β hβ0 hβ1 P).adp (isCEOperator_expectOp P)).IsValueFunction
          gstar →
        (∀ x a, r.toFun (x, a) + β * gstar.toFun (x, a) ≤
          r.toFun (x, σ.1 x) + β * gstar.toFun (x, σ.1 x)) →
        ((seFDP r β hβ0 hβ1 P).primary (seFDP_monotonic r hβ0 hβ1 P)).IsOptimal hw σ := by
  obtain ⟨hw', hfo', -⟩ := proposition_4_2_4 r hβ0 hβ1 P
  have h := seFDP_monotonic r hβ0 hβ1 P
  have hP := seFDP_isOrderPreserving r hβ0 hβ1 P
  have hw : ((seFDP r β hβ0 hβ1 P).primary h).WellPosed := (FDP.lemma_5_2_12 h).1.1 hw'
  have key := FDP.theorem_5_2_13 h hP hw hw'
  have hfo := key.1.2 hfo'
  obtain ⟨-, hii, hiii⟩ := key.2 hfo
  refine ⟨hw, hw', hfo, hiii, fun gstar σ hg hσ => hii gstar σ hg ?_⟩
  refine le_antisymm ((seFDP r β hβ0 hβ1 P).G_le_Gsup σ gstar) fun x => ?_
  exact hσ x _

end SargentStachurski.ADPTransformations
