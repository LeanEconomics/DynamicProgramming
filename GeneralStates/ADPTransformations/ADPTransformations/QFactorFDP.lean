/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.FactoredDP
import ADPTransformations.MDPQFactors

/-!
# Q-factors as a factored dynamic program

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.3.1 (pp. 174–176).

With `(Fv)(x, a) = r(x, a) + β ∑_{x'} v(x')P(x, a, x')` (5.27) and `(G_σ f)(x) = f(x, σ(x))`,
the finite MDP and its Q-factor model are the primary and subordinate ADPs of one
order-preserving FDP (`qfdp_primary`, `qfdp_sub`).

* **Proposition 5.3.1**: `v*(x) = max_{a ∈ Γ(x)} q*(x, a)` and `q* = r + βPv*`; MDP-optimal
  policies are Q-optimal; `σ` is MDP-optimal when it maximizes `q*(x, ·)` at every state.
* **Proposition 5.3.2**: if no state is isolated under `P` and `β > 0`, Q-optimal policies are
  MDP-optimal. The book allows `β ∈ [0, 1)` for MDPs; at `β = 0` the claim fails
  (`proposition_5_3_2_needs_beta_pos`).
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

namespace FiniteMDP

variable {X A : Type*} [Fintype X] (M : FiniteMDP X A)

/-- The Q-factor FDP `(ℝ^X, F, ℝ^G, 𝔾)` of a finite MDP (§5.3.1). -/
def qfdp : FDP (X → ℝ) (M.G → ℝ) M.Policy where
  F v p := M.Q v p.1.1 p.1.2
  G σ f x := f (M.pairOf σ x)
  greatest f := by
    obtain ⟨σ, hσ⟩ := M.exists_qgreedy f
    exact ⟨σ, fun τ x => hσ x (τ.1 x) (τ.2 x)⟩
  nonempty := M.nonempty_policy

theorem qfdp_isOrderPreserving : M.qfdp.IsOrderPreserving :=
  ⟨fun _ _ h p => M.Q_mono p.2 h, fun _ _ _ h _ => h _⟩

theorem qfdp_monotonic : M.qfdp.Monotonic := Or.inl M.qfdp_isOrderPreserving

/-- The primary ADP of the Q-factor FDP is the MDP ADP. -/
theorem qfdp_primary : M.qfdp.primary M.qfdp_monotonic = M.adp := rfl

/-- The subordinate ADP of the Q-factor FDP is the Q-factor ADP (3.6). -/
theorem qfdp_sub : M.qfdp.sub M.qfdp_monotonic = M.qadp := rfl

/-- `Gq` picks the maximum of `q(x, ·)` over `Γ(x)`. -/
theorem le_Gsup (q : M.G → ℝ) (x : X) (a : A) (ha : a ∈ M.Γ x) :
    q ⟨(x, a), ha⟩ ≤ M.qfdp.Gsup q x := by
  classical
  let σ₀ := M.qfdp.gsel q
  let τ : M.Policy := ⟨Function.update σ₀.1 x a, fun y => by
    rcases eq_or_ne y x with rfl | hy
    · rw [Function.update_self]; exact ha
    · rw [Function.update_of_ne hy]; exact σ₀.2 y⟩
  have h := M.qfdp.G_le_Gsup τ q x
  have hτ : M.pairOf τ x = ⟨(x, a), ha⟩ := Subtype.ext (by simp [pairOf, τ])
  change q (M.pairOf τ x) ≤ _ at h
  rwa [hτ] at h

theorem Gsup_eq_sup (q : M.G → ℝ) (x : X) :
    M.qfdp.Gsup q x = (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach)
      (fun a => q ⟨(x, a.1), a.2⟩) := by
  refine le_antisymm ?_ (Finset.sup'_le _ _ fun a _ => M.le_Gsup q x a.1 a.2)
  exact Finset.le_sup' (fun a : M.Γ x => q ⟨(x, a.1), a.2⟩)
    (Finset.mem_attach _ ⟨(M.qfdp.gsel q).1 x, (M.qfdp.gsel q).2 x⟩)

/-- **Proposition 5.3.1** (p. 175): for the MDP and its Q-factor model, (i)
`v*(x) = max_{a ∈ Γ(x)} q*(x, a)` and `q*(x, a) = r(x, a) + β ∑_{x'} v*(x')P(x, a, x')`, (ii)
MDP-optimal policies are Q-optimal, and (iii) `σ` is MDP-optimal whenever
`q*(x, σ(x)) = max_{a ∈ Γ(x)} q*(x, a)` at every `x`. -/
theorem proposition_5_3_1 :
    (∀ v q, M.adp.IsValueFunction v → M.qadp.IsValueFunction q →
      (∀ x, v x = (M.Γ x).attach.sup' ((M.Γ_nonempty x).attach) (fun a => q ⟨(x, a.1), a.2⟩)) ∧
      ∀ x a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ = M.r x a + M.β * ∑ x', v x' * M.P x a x') ∧
    (∀ σ, M.adp.IsOptimal M.adp_wellPosed σ →
      M.qadp.IsOptimal M.qadp_isGloballyStable.wellPosed σ) ∧
    ∀ q σ, M.qadp.IsValueFunction q → (∀ x a (ha : a ∈ M.Γ x), q ⟨(x, a), ha⟩ ≤
      q (M.pairOf σ x)) → M.adp.IsOptimal M.adp_wellPosed σ := by
  have hfo : M.adp.FundamentalOptimality M.adp_wellPosed := M.section_3_2_1_1.1
  obtain ⟨hi, hii, hiii⟩ := (FDP.theorem_5_2_13 M.qfdp_monotonic M.qfdp_isOrderPreserving
    M.adp_wellPosed M.qadp_isGloballyStable.wellPosed).2 hfo
  refine ⟨fun v q hv hq => ?_, hiii, fun q σ hq hσ => hii q σ hq ?_⟩
  · obtain ⟨e1, e2⟩ := hi v q hv hq
    refine ⟨fun x => ?_, fun x a ha => ?_⟩
    · rw [e1, ← M.Gsup_eq_sup]
    · rw [e2]
      rfl
  · funext x
    exact le_antisymm (M.qfdp.G_le_Gsup σ q x) (by
      rw [M.Gsup_eq_sup]
      exact Finset.sup'_le _ _ fun a _ => hσ x a.1 a.2)

/-- With `β > 0` and no isolated state, `F` in (5.27) is strictly order preserving
(Example A.1.12). -/
theorem qfdp_F_strictMono (hβ : 0 < M.β) (hiso : ∀ x', ∃ p : M.G, 0 < M.P p.1.1 p.1.2 x') :
    StrictMono M.qfdp.F := by
  intro u v huv
  refine lt_of_le_of_ne (M.qfdp_isOrderPreserving.1 huv.le) fun heq => ?_
  obtain ⟨x', hx'⟩ : ∃ x', u x' < v x' := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact huv.ne (le_antisymm huv.le hcon)
  obtain ⟨p, hp⟩ := hiso x'
  have h := congrFun heq p
  change M.Q u p.1.1 p.1.2 = M.Q v p.1.1 p.1.2 at h
  have hlt : ∑ y, u y * M.P p.1.1 p.1.2 y < ∑ y, v y * M.P p.1.1 p.1.2 y :=
    Finset.sum_lt_sum (fun y _ => mul_le_mul_of_nonneg_right (huv.le y) (M.P_nonneg _ _ p.2 y))
      ⟨x', Finset.mem_univ _, mul_lt_mul_of_pos_right hx' hp⟩
  simp only [Q] at h
  linarith [mul_lt_mul_of_pos_left hlt hβ]

/-- **Proposition 5.3.2** (p. 176): if `β > 0` and no state is isolated under `P` (every `x'` has
`P(x, a, x') > 0` for some feasible `(x, a)`), every Q-optimal policy is MDP-optimal. -/
theorem proposition_5_3_2 (hβ : 0 < M.β) (hiso : ∀ x', ∃ p : M.G, 0 < M.P p.1.1 p.1.2 x')
    (σ : M.Policy) (hσ : M.qadp.IsOptimal M.qadp_isGloballyStable.wellPosed σ) :
    M.adp.IsOptimal M.adp_wellPosed σ :=
  (FDP.proposition_5_2_14 M.qfdp_monotonic M.qfdp_isOrderPreserving
    (M.qfdp_F_strictMono hβ hiso) M.adp_wellPosed M.qadp_isGloballyStable.wellPosed
    M.exercise_3_2_6.1).2 σ hσ

end FiniteMDP

/-- A one-state MDP with actions `Bool`, `r(·, b) = 1` if `b` else `0`, `β = 0`. -/
def zeroDiscountMDP : FiniteMDP Unit Bool where
  Γ _ := Finset.univ
  Γ_nonempty _ := Finset.univ_nonempty
  r _ b := if b then 1 else 0
  β := 0
  β_nonneg := le_rfl
  β_lt_one := zero_lt_one
  P _ _ _ := 1
  P_nonneg _ _ _ _ := zero_le_one
  P_sum _ _ _ := by simp

/-- **Proposition 5.3.2 needs `β > 0`.** For `zeroDiscountMDP` (`β = 0`, no isolated state), the
policy choosing `false` is optimal for the Q-factor model, since `S_σ q = r` for every `σ`, but
not for the MDP, whose `true` policy earns `1 > 0`. -/
theorem proposition_5_3_2_needs_beta_pos :
    (∀ x', ∃ p : zeroDiscountMDP.G, 0 < zeroDiscountMDP.P p.1.1 p.1.2 x') ∧
      zeroDiscountMDP.qadp.IsOptimal zeroDiscountMDP.qadp_isGloballyStable.wellPosed
        ⟨fun _ => false, fun _ => Finset.mem_univ _⟩ ∧
      ¬ zeroDiscountMDP.adp.IsOptimal zeroDiscountMDP.adp_wellPosed
        ⟨fun _ => false, fun _ => Finset.mem_univ _⟩ := by
  have hrq : ∀ σ : zeroDiscountMDP.Policy,
      zeroDiscountMDP.qadp.vσ zeroDiscountMDP.qadp_isGloballyStable.wellPosed σ =
        fun p => zeroDiscountMDP.r p.1.1 p.1.2 := fun σ => by
    refine (ADP.eq_vσ zeroDiscountMDP.qadp_isGloballyStable.wellPosed (funext fun p => ?_)).symm
    simp [FiniteMDP.qadp, FiniteMDP.Sσ, zeroDiscountMDP]
  have hrv : ∀ σ : zeroDiscountMDP.Policy, zeroDiscountMDP.adp.vσ zeroDiscountMDP.adp_wellPosed σ =
      fun x => zeroDiscountMDP.r x (σ.1 x) := fun σ => by
    refine (ADP.eq_vσ zeroDiscountMDP.adp_wellPosed (funext fun x => ?_)).symm
    simp [FiniteMDP.adp, FiniteMDP.Tσ, FiniteMDP.Q, zeroDiscountMDP]
  refine ⟨fun _ => ⟨⟨((), true), Finset.mem_univ _⟩, by simp [zeroDiscountMDP]⟩, ?_, ?_⟩
  · refine ⟨⟨_, ADP.T_vσ _ _⟩, ?_⟩
    rintro _ ⟨τ, hτ⟩
    rw [ADP.eq_vσ zeroDiscountMDP.qadp_isGloballyStable.wellPosed hτ]
    exact le_of_eq ((hrq τ).trans (hrq _).symm)
  · rintro ⟨-, hup⟩
    have h := hup ⟨⟨fun _ => true, fun _ => Finset.mem_univ _⟩,
      ADP.T_vσ zeroDiscountMDP.adp_wellPosed _⟩
    have e1 := hrv ⟨fun _ => true, fun _ => Finset.mem_univ _⟩
    have e2 := hrv ⟨fun _ => false, fun _ => Finset.mem_univ _⟩
    have h2 := (le_of_eq e1.symm).trans (h.trans (le_of_eq e2))
    have := h2 ()
    simp only [zeroDiscountMDP, ite_true] at this
    norm_num at this

end SargentStachurski.ADPTransformations
