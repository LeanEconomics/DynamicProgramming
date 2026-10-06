/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveDecisionProcesses.Contracting

/-!
# Eventually contracting RDPs

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §8.2.2 (pp. 270–272) and
Exercise 8.1.16 (p. 260).

`R` is eventually contracting (8.34) if `|B(x, a, v) − B(x, a, w)| ≤ ∑ |v(x') − w(x')| L(x, a, x')`
for some `L ≥ 0` with `ρ(L_σ) < 1` for every feasible `σ`, where `L_σ(x, x') = L(x, σ(x), x')`.

* Proposition 8.2.4: with `V` closed (and nonempty), an eventually contracting RDP is globally
  stable, via Proposition 6.1.6 and Theorem 6.1.5.
* §8.2.2.2: the MDP with state-dependent discounting is eventually contracting when
  `ρ(L_σ) < 1` for `L(x, a, x') = β(x, a, x')P(x, a, x')`, completing the proof of
  Proposition 6.2.2: Theorem 8.1.1 applies.
* Exercise 8.2.8: optimal firm exit with state-dependent discounting, `B(x, a, v) = s` on exit and
  `π(x) + β(x)(Qv)(x)` otherwise, is globally stable when `β(x)Q(x, x') ≤ L(x, x')` with
  `ρ(L) < 1`; its Bellman equation is `v = max{s, π + βQv}`.
* Exercise 8.1.16: under the conditions of Proposition 6.2.2, state-dependent discounting gives
  a bounded RDP, with `v₂ = w*` and `v₁ = −w*` for the value function `w*` of the same problem with
  rewards `|r|`.
-/

open Finset Matrix Filter Topology Function Set

namespace SargentStachurski.RecursiveDecisionProcesses

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RDP

variable {X A : Type*} [Fintype X] [Fintype A] (R : RDP X A)

/-- The matrix `L_σ(x, x') = L(x, σ(x), x')`. -/
def Lσ (L : X → A → X → ℝ) (σ : X → A) : Matrix X X ℝ := Matrix.of fun x x' => L x (σ x) x'

/-- `R` is eventually contracting (8.34) with dominating kernel `L ≥ 0`. -/
def IsEventuallyContracting (L : X → A → X → ℝ) : Prop :=
  (∀ x a x', 0 ≤ L x a x') ∧
    (∀ x, ∀ a ∈ R.Γ x, ∀ v ∈ R.V, ∀ w ∈ R.V,
      |R.B x a v - R.B x a w| ≤ ∑ x', |v x' - w x'| * L x a x') ∧
    ∀ σ, R.IsFeasible σ → specRad (Lσ L σ) < 1

/-- **Proposition 8.2.4** (p. 271): an eventually contracting RDP with `V` closed and nonempty is
globally stable, so Theorem 8.1.1 applies. -/
theorem IsEventuallyContracting.isGloballyStable {R : RDP X A} {L : X → A → X → ℝ}
    (h : R.IsEventuallyContracting L) (hV : IsClosed R.V) (hne : R.V.Nonempty) :
    R.IsGloballyStable := by
  intro σ hσ
  rcases isEmpty_or_nonempty X with hX | hX
  · obtain ⟨u, hu⟩ := hne
    refine ⟨u, hu, Subsingleton.elim _ _, fun v _ _ => Subsingleton.elim _ _, fun v _ => ?_⟩
    have hk : ∀ k, (R.Tσ σ)^[k] v = u := fun k => Subsingleton.elim _ _
    simp only [hk]
    exact tendsto_const_nhds
  obtain ⟨u, hu, hfix, huniq, hconv⟩ := globallyStable_of_abs_sub_le hV hne (R.Tσ_mapsTo hσ)
    (fun x x' => h.1 x (σ x) x') (h.2.2 σ hσ) fun v hv w hw x => by
      refine (h.2.1 x _ (hσ x) v hv w hw).trans_eq ?_
      simp only [mulVec, dotProduct]
      exact sum_congr rfl fun _ _ => mul_comm _ _
  exact ⟨u, hu, hfix, huniq, hconv⟩

end RDP

/-! ### State-dependent discounting (§8.2.2.2) -/

namespace MDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : MDP X A)

/-- §8.2.2.2 (p. 272): the RDP of an MDP with state-dependent discounting is eventually
contracting with `L(x, a, x') = β(x, a, x')P(x, a, x')` whenever every `ρ(L_σ) < 1`. -/
theorem withDiscount_isEventuallyContracting {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x')
    (hρ : ∀ σ, (M.withDiscount β hβ).IsFeasible σ →
      specRad (RDP.Lσ (fun x a x' => β x a x' * M.P x a x') σ) < 1) :
    (M.withDiscount β hβ).IsEventuallyContracting fun x a x' => β x a x' * M.P x a x' := by
  refine ⟨fun x a x' => mul_nonneg (hβ x a x') (M.P_nonneg x a x'), fun x a _ v _ w _ => ?_, hρ⟩
  change |M.r x a + ∑ x', v x' * β x a x' * M.P x a x' -
    (M.r x a + ∑ x', w x' * β x a x' * M.P x a x')| ≤ _
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => le_of_eq ?_)
  rw [← sub_mul, ← sub_mul, abs_mul, abs_mul, abs_of_nonneg (hβ x a x'),
    abs_of_nonneg (M.P_nonneg x a x')]
  ring

/-- **Proposition 6.2.2** via Proposition 8.2.4 (p. 272): under `ρ(L_σ) < 1` for every `σ`, the
MDP with state-dependent discounting is globally stable, so Theorem 8.1.1 applies. -/
theorem withDiscount_isGloballyStable {β : X → A → X → ℝ} (hβ : ∀ x a x', 0 ≤ β x a x')
    (hρ : ∀ σ, (M.withDiscount β hβ).IsFeasible σ →
      specRad (RDP.Lσ (fun x a x' => β x a x' * M.P x a x') σ) < 1) :
    (M.withDiscount β hβ).IsGloballyStable :=
  (M.withDiscount_isEventuallyContracting hβ hρ).isGloballyStable isClosed_univ ⟨0, mem_univ _⟩

/-- The same MDP with rewards `|r|`. -/
def absReward : MDP X A := { M with r := fun x a => |M.r x a| }

/-- **Exercise 8.1.16** (p. 260): under the conditions of Proposition 6.2.2 the state-dependent
discounting RDP is bounded, by `v₁ = −w*` and `v₂ = w*`, where `w*` is the value function of the
problem with rewards `|r|`. -/
theorem withDiscount_isBoundedBy [DecidableEq X] [DecidableEq A] {β : X → A → X → ℝ}
    (hβ : ∀ x a x', 0 ≤ β x a x')
    (hρ : ∀ σ, (M.withDiscount β hβ).IsFeasible σ →
      specRad (RDP.Lσ (fun x a x' => β x a x' * M.P x a x') σ) < 1) :
    (M.withDiscount β hβ).IsBoundedBy (-(M.absReward.withDiscount β hβ).vstar)
      (M.absReward.withDiscount β hβ).vstar := by
  set Rb := M.absReward.withDiscount β hβ with hRb
  have hGS : Rb.IsGloballyStable := M.absReward.withDiscount_isGloballyStable hβ hρ
  have hw := hGS.wellPosed
  obtain ⟨-, hfix⟩ := RDP.vstar_spec hw hGS.comparable
  -- `w* ≥ 0`: it dominates `v_σ`, the limit of `T_σᵏ 0 ≥ 0`
  have hnonneg : 0 ≤ Rb.vstar := by
    obtain ⟨σ, hσ⟩ := Rb.policy_nonempty
    have hk : ∀ k, 0 ≤ (Rb.Tσ σ)^[k] 0 := by
      intro k
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        rw [iterate_succ_apply']
        intro x
        change 0 ≤ |M.r x (σ x)| + ∑ x', _ * β x (σ x) x' * M.P x (σ x) x'
        exact add_nonneg (abs_nonneg _) (sum_nonneg fun x' _ =>
          mul_nonneg (mul_nonneg (ih x') (hβ _ _ _)) (M.P_nonneg _ _ _))
    have hlim := RDP.tendsto_iterate_Tσ hGS hσ (mem_univ (0 : X → ℝ))
    intro x
    exact (ge_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hk k x).trans
      (Rb.vσ_le_vstar hσ x)
  have hB : ∀ x a, a ∈ M.Γ x → |M.r x a| + ∑ x', Rb.vstar x' * β x a x' * M.P x a x' ≤
      Rb.vstar x := fun x a ha => by
    have := Rb.B_le_T Rb.vstar (x := x) ha
    rw [hfix.eq] at this
    exact this
  have hS : ∀ x a, 0 ≤ ∑ x', Rb.vstar x' * β x a x' * M.P x a x' := fun x a =>
    sum_nonneg fun x' _ => mul_nonneg (mul_nonneg (hnonneg x') (hβ _ _ _)) (M.P_nonneg _ _ _)
  refine ⟨fun x => by
    have := hnonneg x
    simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
    linarith,
    fun _ _ => mem_univ _, fun x a ha => ⟨?_, ?_⟩⟩
  · change -Rb.vstar x ≤ M.r x a + ∑ x', (-Rb.vstar) x' * β x a x' * M.P x a x'
    have e : ∑ x', (-Rb.vstar) x' * β x a x' * M.P x a x' =
        -∑ x', Rb.vstar x' * β x a x' * M.P x a x' := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun x' _ => by simp only [Pi.neg_apply]; ring
    rw [e]
    have := hB x a ha
    have := neg_abs_le (M.r x a)
    linarith
  · change M.r x a + ∑ x', Rb.vstar x' * β x a x' * M.P x a x' ≤ Rb.vstar x
    have := hB x a ha
    have := le_abs_self (M.r x a)
    linarith

end MDP

/-! ### Optimal firm exit with state-dependent discounting (Exercise 8.2.8) -/

variable {X : Type*} [Fintype X]

/-- The firm exit RDP of Exercise 8.2.8: `Γ(x) = {exit, stay}`, `V = ℝ^X` and
`B(x, a, v) = s` on exit, `π(x) + β(x) ∑ v(x')Q(x, x')` on staying, with `β ≥ 0` and `Q` Markov.
-/
def firmExit (s : ℝ) (π β : X → ℝ) (hβ : ∀ x, 0 ≤ β x) {Q : Matrix X X ℝ} (hQ : IsMarkov Q) :
    RDP X Bool where
  Γ := fun _ => univ
  Γ_nonempty := fun _ => univ_nonempty
  V := univ
  B := fun x a v => bif a then s else π x + β x * (Q *ᵥ v) x
  mono := fun x a _ _ _ _ _ hvw => by
    cases a
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hQ.mulVec_le_mulVec hvw x) (hβ x))
    · exact le_rfl
  consistent := fun _ _ _ _ => mem_univ _

/-- Exercise 8.2.8 (p. 271): the Bellman equation is `v(x) = max{s, π(x) + β(x)(Qv)(x)}`. -/
theorem firmExit_T (s : ℝ) (π β : X → ℝ) (hβ : ∀ x, 0 ≤ β x) {Q : Matrix X X ℝ}
    (hQ : IsMarkov Q) (v : X → ℝ) (x : X) :
    (firmExit s π β hβ hQ).T v x = max s (π x + β x * (Q *ᵥ v) x) := by
  refine le_antisymm (Finset.sup'_le _ _ fun a _ => ?_) (max_le ?_ ?_)
  · cases a
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact (firmExit s π β hβ hQ).B_le_T v (a := true) (mem_univ _)
  · exact (firmExit s π β hβ hQ).B_le_T v (a := false) (mem_univ _)

/-- **Exercise 8.2.8** (p. 271): if `β(x)Q(x, x') ≤ L(x, x')` with `ρ(L) < 1`, the firm exit RDP is
eventually contracting (with `L` not depending on the action), hence globally stable. -/
theorem firmExit_isGloballyStable (s : ℝ) (π β : X → ℝ) (hβ : ∀ x, 0 ≤ β x) {Q : Matrix X X ℝ}
    (hQ : IsMarkov Q) {L : Matrix X X ℝ} (hρ : specRad L < 1)
    (hL : ∀ x x', β x * Q x x' ≤ L x x') : (firmExit s π β hβ hQ).IsGloballyStable := by
  have hL0 : ∀ x x', 0 ≤ L x x' := fun x x' =>
    (mul_nonneg (hβ x) (hQ.nonneg x x')).trans (hL x x')
  refine RDP.IsEventuallyContracting.isGloballyStable (L := fun x _ x' => L x x')
    ⟨fun x _ x' => hL0 x x', fun x a _ v _ w _ => ?_, fun σ _ => ?_⟩ isClosed_univ
    ⟨0, mem_univ _⟩
  · cases a
    · change |π x + β x * (Q *ᵥ v) x - (π x + β x * (Q *ᵥ w) x)| ≤ _
      rw [add_sub_add_left_eq_sub, ← mul_sub, mulVec_apply_eq, mulVec_apply_eq,
        ← sum_sub_distrib, abs_mul, abs_of_nonneg (hβ x)]
      refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (hβ x)).trans ?_
      rw [Finset.mul_sum]
      refine sum_le_sum fun x' _ => ?_
      change β x * |v x' * Q x x' - w x' * Q x x'| ≤ |v x' - w x'| * L x x'
      rw [← sub_mul, abs_mul, abs_of_nonneg (hQ.nonneg x x')]
      calc β x * (|v x' - w x'| * Q x x') = |v x' - w x'| * (β x * Q x x') := by ring
        _ ≤ |v x' - w x'| * L x x' := mul_le_mul_of_nonneg_left (hL x x') (abs_nonneg _)
    · change |s - s| ≤ _
      rw [sub_self, abs_zero]
      exact sum_nonneg fun x' _ => mul_nonneg (abs_nonneg _) (hL0 x x')
  · have : RDP.Lσ (fun x (_ : Bool) x' => L x x') σ = L := by
      ext x x'
      rfl
    rw [this]
    exact hρ

end SargentStachurski.RecursiveDecisionProcesses
