/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.BoundedMeasurable
import ADPsOnPospaces.Pospace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# MDPs with a countable state space

Sargent and Stachurski, *Dynamic Programming*, Volume 2, **Exercise 3.2.1** (p. 106).

The MDP `(Γ, r, β, P)` of §1.2.1.1 with state and action spaces that need not be finite, finite
nonempty feasible sets `Γ(x)`, a reward bounded on the feasible pairs and transition
probabilities `P(x, a, ·)` summing to one. The value space is `bX`, the bounded functions on `X`,
which are all measurable for the discrete σ-algebra.

* (i) `(bX, 𝕋_MDP)` is an ADP, with `T_σ v = r_σ + βP_σ v`;
* (ii) the fundamental optimality properties hold; and
* (iii) VFI, OPI and HPI all converge.

The proof applies Theorem 3.1.5 on the Banach lattice `bX` (the ADP is regular because the
feasible sets are finite), then Theorem 3.1.2.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- An MDP with general (countable) state and action spaces (Exercise 3.2.1): finite nonempty
feasible sets, a reward bounded on the feasible pairs, and summable transition probabilities. -/
structure CountableMDP (X A : Type*) where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward -/
  r : X → A → ℝ
  r_bdd : ∃ C, ∀ x, ∀ a ∈ Γ x, |r x a| ≤ C
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x, ∀ a ∈ Γ x, ∀ x', 0 ≤ P x a x'
  P_sum : ∀ x, ∀ a ∈ Γ x, HasSum (P x a) 1

namespace CountableMDP

variable {X A : Type*} (M : CountableMDP X A)

/-- The feasible policies. -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

theorem nonempty_policy : Nonempty M.Policy := by
  choose f hf using fun x => M.Γ_nonempty x
  exact ⟨⟨f, hf⟩⟩

theorem summable_mul {x : X} {a : A} (ha : a ∈ M.Γ x) {v : X → ℝ} {C : ℝ}
    (hv : ∀ y, |v y| ≤ C) : Summable fun x' => v x' * M.P x a x' := by
  refine Summable.of_norm_bounded ((M.P_sum x a ha).summable.mul_left C) fun x' => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (M.P_nonneg x a ha x')]
  exact mul_le_mul_of_nonneg_right (hv x') (M.P_nonneg x a ha x')

/-- `|∑_{x'} v(x')P(x, a, x')| ≤ C` when `|v| ≤ C`. -/
theorem abs_tsum_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v : X → ℝ} {C : ℝ}
    (hv : ∀ y, |v y| ≤ C) : |∑' x', v x' * M.P x a x'| ≤ C := by
  have hC : HasSum (fun x' => C * M.P x a x') C := by
    simpa using (M.P_sum x a ha).mul_left C
  have hnC : HasSum (fun x' => -C * M.P x a x') (-C) := by
    simpa using (M.P_sum x a ha).mul_left (-C)
  refine abs_le.2 ⟨?_, ?_⟩
  · rw [← hnC.tsum_eq]
    exact hnC.summable.tsum_le_tsum (fun x' => mul_le_mul_of_nonneg_right
      (abs_le.1 (hv x')).1 (M.P_nonneg x a ha x')) (M.summable_mul ha hv)
  · rw [← hC.tsum_eq]
    exact (M.summable_mul ha hv).tsum_le_tsum (fun x' => mul_le_mul_of_nonneg_right
      (abs_le.1 (hv x')).2 (M.P_nonneg x a ha x')) hC.summable

/-- The value of action `a` at `x` given a bounded `v`. -/
noncomputable def Q (v : X → ℝ) (x : X) (a : A) : ℝ :=
  M.r x a + M.β * ∑' x', v x' * M.P x a x'

theorem Q_mono {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {C D : ℝ}
    (hv : ∀ y, |v y| ≤ C) (hw : ∀ y, |w y| ≤ D) (h : ∀ y, v y ≤ w y) :
    M.Q v x a ≤ M.Q w x a :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_left ((M.summable_mul ha hv).tsum_le_tsum
    (fun x' => mul_le_mul_of_nonneg_right (h x') (M.P_nonneg x a ha x'))
    (M.summable_mul ha hw)) M.β_nonneg)

theorem abs_Q_sub_le {x : X} {a : A} (ha : a ∈ M.Γ x) {v w : X → ℝ} {C D c : ℝ}
    (hv : ∀ y, |v y| ≤ C) (hw : ∀ y, |w y| ≤ D) (h : ∀ y, |v y - w y| ≤ c) :
    |M.Q v x a - M.Q w x a| ≤ M.β * c := by
  simp only [Q, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ M.β_nonneg
  rw [← (M.summable_mul ha hv).tsum_sub (M.summable_mul ha hw)]
  simpa only [← sub_mul] using M.abs_tsum_le ha h

variable [MeasurableSpace X] [DiscreteMeasurableSpace X]

/-- The policy operator `T_σ v = r_σ + βP_σ v` on `bX`. -/
noncomputable def Tσ (σ : M.Policy) (v : BM X) : BM X :=
  ⟨fun x => M.Q v.toFun x (σ.1 x), Measurable.of_discrete, by
    obtain ⟨C, hC⟩ := M.r_bdd
    refine ⟨C + M.β * ‖v‖, fun x => (abs_add_le _ _).trans (add_le_add (hC x _ (σ.2 x)) ?_)⟩
    rw [abs_mul, abs_of_nonneg M.β_nonneg]
    exact mul_le_mul_of_nonneg_left (M.abs_tsum_le (σ.2 x) (BM.abs_le_norm v)) M.β_nonneg⟩

/-- **Exercise 3.2.1 (i)**: `(bX, 𝕋_MDP)` is an ADP. -/
noncomputable def adp : ADP (BM X) M.Policy where
  T := M.Tσ
  mono σ v w h x := M.Q_mono (σ.2 x) (BM.abs_le_norm v) (BM.abs_le_norm w) h
  nonempty := M.nonempty_policy

/-- Each `T_σ` is a contraction of modulus `β` for the supremum norm. -/
theorem adp_contraction (σ : M.Policy) (v w : BM X) :
    dist (M.adp.T σ v) (M.adp.T σ w) ≤ M.β * dist v w :=
  BM.dist_le (mul_nonneg M.β_nonneg dist_nonneg) fun x =>
    M.abs_Q_sub_le (σ.2 x) (BM.abs_le_norm v) (BM.abs_le_norm w) (BM.abs_sub_le_dist v w)

/-- The ADP is regular: the feasible sets are finite. -/
theorem adp_regular : M.adp.Regular := fun v => by
  choose f hf hmax using fun x => Finset.exists_max_image (M.Γ x) (M.Q v.toFun x)
    (M.Γ_nonempty x)
  exact ⟨⟨f, hf⟩, fun τ x => hmax x _ (τ.2 x)⟩

/-- The ADP is globally stable (Banach's theorem). -/
theorem adp_isGloballyStable : M.adp.IsGloballyStable :=
  ADP.isGloballyStable_of_contraction ⟨0⟩ M.β_nonneg M.β_lt_one M.adp_contraction

/-- **Exercise 3.2.1** (p. 106): (ii) the fundamental optimality properties hold for `(bX, 𝕋_MDP)`
and (iii) VFI, OPI and HPI all converge. -/
theorem exercise_3_2_1 :
    M.adp.FundamentalOptimality M.adp_isGloballyStable.wellPosed ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧
          M.adp.HPIConverges M.adp_isGloballyStable.wellPosed g vstar := by
  obtain ⟨hFO, -⟩ := ADP.theorem_3_1_5 BM.isSupNonexpansive M.β_nonneg M.β_lt_one
    M.adp_contraction ⟨isClosed_univ, fun v _ => M.adp_regular v, mapsTo_univ _ _⟩
    univ_nonempty
  obtain ⟨vstar, -, -, -, hvG, hb⟩ := hFO.exists_vstar
  exact ADP.theorem_3_1_2 M.adp_regular M.adp_isGloballyStable
    ((M.adp.solvesBellman_iff hvG).1 hb)

end CountableMDP

end SargentStachurski.ADPsOnPospaces
