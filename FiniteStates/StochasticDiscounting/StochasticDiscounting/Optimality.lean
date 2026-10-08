/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StochasticDiscounting.SDMDP

/-!
# Optimality with state-dependent discounting

Sargent and Stachurski, *Dynamic Programming*, Volume 1, §6.2.1.3–§6.2.1.4
(pp. 194–195).

The Bellman operator (6.21) maximises the action value over `Γ(x)`; a policy is
`v`-greedy if it attains the maximum, equivalently `T_σ v = Tv`; the value
function is `v* = ⋁_σ v_σ` and a policy is optimal if `v_σ = v*`.

**Proposition 6.2.2.** Under Assumption 6.2.1, (i) `v*` is the unique solution of
the Bellman equation, (ii) a policy is optimal iff it is `v*`-greedy, and (iii) an
optimal policy exists. The book defers the proof to §8.2.2. The proof here uses
only that each `T_σ` is order preserving and globally stable (Lemma 6.2.1,
Exercise 6.2.2), not a contraction property of `T`: `v* ≤ Tv*` since
`v_σ = T_σ v_σ ≤ T_σ v* ≤ Tv*`; for a `v*`-greedy `σ`, `v* ≤ T_σ v*` gives
`v* ≤ v_σ`, so `v_σ = v*` and `Tv* = T_σ v* = v*`. Uniqueness: a fixed point `v̄`
is `v_σ` for its greedy `σ`, so `v̄ ≤ v*`, and `T_σ v̄ ≤ v̄` for every `σ` gives
`v_σ ≤ v̄`.

**Algorithms** (§6.2.1.4): the HPI improvement and termination steps of
Algorithm 6.1, OPI with `m = 1` as VFI and `T_σᵐv → v_σ`. The convergence of
VFI, OPI and HPI under Assumption 6.2.1 alone is Chapter 8's; here VFI converges
under the stronger condition of Exercise 6.2.3, `βP ≤ L` with `ρ(L) < 1`, because
`T` then satisfies (6.13) and Proposition 6.1.6 applies.
-/

open Finset Matrix Filter Topology Function

namespace SargentStachurski.StochasticDiscounting

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- If `Tu ≤ u`, `T` is order preserving and `Tᵏu → u'`, then `u' ≤ u`: the dual of
`le_fixedPt_of_le_apply`. -/
theorem fixedPt_le_of_apply_le {X : Type*} {T : (X → ℝ) → (X → ℝ)} (hT : Monotone T)
    {u u' : X → ℝ} (hu : T u ≤ u) (hlim : Tendsto (fun k : ℕ => T^[k] u) atTop (𝓝 u')) :
    u' ≤ u := by
  have hle : ∀ k : ℕ, T^[k] u ≤ u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iterate_succ_apply']
      exact (hT ih).trans hu
  intro x
  exact le_of_tendsto' (tendsto_pi_nhds.1 hlim x) fun k => hle k x

namespace SDMDP

variable {X A : Type*} [Fintype X] [Fintype A] (M : SDMDP X A)

/-! ### The Bellman operator (6.21) and greedy policies -/

/-- The Bellman operator (6.21):
`(Tv)(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v(x')β(x, a, x')P(x, a, x')}`. -/
noncomputable def T (v : X → ℝ) : X → ℝ := fun x => (M.Γ x).sup' (M.Γ_nonempty x) (M.B v x)

theorem T_apply (v : X → ℝ) (x : X) :
    M.T v x = (M.Γ x).sup' (M.Γ_nonempty x) fun a =>
      M.r x a + ∑ x', v x' * M.β x a x' * M.P x a x' := rfl

theorem B_le_T (v : X → ℝ) {x : X} {a : A} (ha : a ∈ M.Γ x) : M.B v x a ≤ M.T v x :=
  Finset.le_sup' (M.B v x) ha

/-- `T_σ v ≤ Tv` for every feasible policy. -/
theorem Tσ_le_T (σ : M.Policy) (v : X → ℝ) : M.Tσ σ.1 v ≤ M.T v := fun x => M.B_le_T v (σ.2 x)

/-- `T` is order preserving. -/
theorem T_monotone : Monotone M.T := fun _ _ hvv' x =>
  Finset.sup'_mono_fun fun a _ => M.B_mono hvv' x a

/-- A `v`-greedy policy (p. 194): feasible, and `σ(x)` maximises the right-hand side of (6.21). -/
def IsGreedy (v : X → ℝ) (σ : X → A) : Prop :=
  M.IsFeasible σ ∧ ∀ x, ∀ a ∈ M.Γ x, M.B v x a ≤ M.B v x (σ x)

/-- A `v`-greedy policy, chosen by maximising the action value in each state. -/
noncomputable def greedy (v : X → ℝ) : X → A := fun x =>
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose

theorem greedy_mem (v : X → ℝ) (x : X) : M.greedy v x ∈ M.Γ x :=
  ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.1

/-- A `v`-greedy policy exists. -/
theorem isGreedy_greedy (v : X → ℝ) : M.IsGreedy v (M.greedy v) :=
  ⟨M.greedy_mem v, fun x a ha =>
    ((M.Γ x).exists_max_image (M.B v x) (M.Γ_nonempty x)).choose_spec.2 a ha⟩

/-- The greedy policy as an element of `Σ`. -/
noncomputable def greedyPolicy (v : X → ℝ) : M.Policy := ⟨M.greedy v, M.greedy_mem v⟩

/-- A feasible `σ` is `v`-greedy iff `T_σ v = Tv` (p. 194). -/
theorem isGreedy_iff_Tσ_eq_T (v : X → ℝ) (σ : M.Policy) :
    M.IsGreedy v σ.1 ↔ M.Tσ σ.1 v = M.T v := by
  constructor
  · rintro ⟨-, h⟩
    funext x
    exact le_antisymm (M.B_le_T v (σ.2 x)) (Finset.sup'_le _ _ fun a ha => h x a ha)
  · intro h
    refine ⟨σ.2, fun x a ha => ?_⟩
    have := congrFun h x
    rw [Tσ] at this
    rw [this]
    exact M.B_le_T v ha

theorem Tσ_eq_T_of_isGreedy {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) : M.Tσ σ v = M.T v :=
  (M.isGreedy_iff_Tσ_eq_T v ⟨σ, hσ.1⟩).1 hσ

/-! ### The value function and Proposition 6.2.2 -/

variable [DecidableEq X] [DecidableEq A] [Nonempty X]

/-- The value function `v* = ⋁_{σ ∈ Σ} v_σ` (p. 194). -/
noncomputable def vstar : X → ℝ := fun x =>
  univ.sup' (univ_nonempty_iff.2 M.policy_nonempty) fun σ : M.Policy => M.vσ σ.1 x

omit [Nonempty X] in
theorem vσ_le_vstar (σ : M.Policy) : M.vσ σ.1 ≤ M.vstar := fun x =>
  Finset.le_sup' (fun σ : M.Policy => M.vσ σ.1 x) (mem_univ σ)

/-- An optimal policy (p. 194): a feasible `σ` with `v_σ = v*`. -/
def IsOptimal (σ : X → A) : Prop := M.IsFeasible σ ∧ M.vσ σ = M.vstar

/-- `v* ≤ Tv*`: for each `σ`, `v_σ = T_σ v_σ ≤ T_σ v* ≤ Tv*`. -/
theorem vstar_le_T_vstar (hM : M.SpectralCondition) : M.vstar ≤ M.T M.vstar := by
  intro x
  refine Finset.sup'_le _ _ fun σ _ => ?_
  calc M.vσ σ.1 x = M.Tσ σ.1 (M.vσ σ.1) x := by rw [(M.isFixedPt_vσ (hM σ.1 σ.2)).eq]
    _ ≤ M.Tσ σ.1 M.vstar x := M.Tσ_monotone σ.1 (M.vσ_le_vstar σ) x
    _ ≤ M.T M.vstar x := M.Tσ_le_T σ M.vstar x

/-- A `v*`-greedy policy is optimal: `v* ≤ T_σ v*` gives `v* ≤ v_σ` by global stability of
`T_σ`. -/
theorem vσ_eq_vstar_of_isGreedy (hM : M.SpectralCondition) {σ : X → A}
    (hσ : M.IsGreedy M.vstar σ) : M.vσ σ = M.vstar := by
  have h2 : M.vstar ≤ M.Tσ σ M.vstar := by
    rw [M.Tσ_eq_T_of_isGreedy hσ]
    exact M.vstar_le_T_vstar hM
  exact le_antisymm (M.vσ_le_vstar ⟨σ, hσ.1⟩)
    (le_fixedPt_of_le_apply (M.Tσ_monotone σ) h2 (M.tendsto_iterate_Tσ (hM σ hσ.1) _))

/-- **Proposition 6.2.2 (i)**, existence half (p. 194): under Assumption 6.2.1, `v*` solves the
Bellman equation. -/
theorem isFixedPt_T_vstar (hM : M.SpectralCondition) : IsFixedPt M.T M.vstar := by
  set σ := M.greedy M.vstar with hσdef
  have hσ : M.IsGreedy M.vstar σ := M.isGreedy_greedy M.vstar
  have h4 := M.vσ_eq_vstar_of_isGreedy hM hσ
  change M.T M.vstar = M.vstar
  calc M.T M.vstar = M.Tσ σ M.vstar := (M.Tσ_eq_T_of_isGreedy hσ).symm
    _ = M.Tσ σ (M.vσ σ) := by rw [h4]
    _ = M.vσ σ := (M.isFixedPt_vσ (hM σ hσ.1)).eq
    _ = M.vstar := h4

/-- **Proposition 6.2.2 (i)**, uniqueness half: `v*` is the only solution of the Bellman equation
in `ℝ^X`. -/
theorem eq_vstar_of_isFixedPt (hM : M.SpectralCondition) {v : X → ℝ} (hv : IsFixedPt M.T v) :
    v = M.vstar := by
  -- `v* ≤ v`: `T_σ v ≤ Tv = v` gives `v_σ ≤ v` for every `σ`
  have hle : ∀ σ : M.Policy, M.vσ σ.1 ≤ v := fun σ =>
    fixedPt_le_of_apply_le (M.Tσ_monotone σ.1) ((M.Tσ_le_T σ v).trans_eq hv.eq)
      (M.tendsto_iterate_Tσ (hM σ.1 σ.2) v)
  have h1 : M.vstar ≤ v := fun x => Finset.sup'_le _ _ fun σ _ => hle σ x
  -- `v ≤ v*`: `v` is the value of its own greedy policy
  have hσ := M.isGreedy_greedy v
  have hfix : IsFixedPt (M.Tσ (M.greedy v)) v := by
    rw [IsFixedPt, M.Tσ_eq_T_of_isGreedy hσ]
    exact hv
  have h2 : v ≤ M.vstar := by
    rw [M.eq_vσ_of_isFixedPt (hM _ hσ.1) hfix]
    exact M.vσ_le_vstar ⟨_, hσ.1⟩
  exact le_antisymm h2 h1

/-- The Bellman equation (6.15):
`v*(x) = max_{a ∈ Γ(x)} {r(x, a) + ∑ v*(x')β(x, a, x')P(x, a, x')}`. -/
theorem bellman_equation (hM : M.SpectralCondition) (x : X) :
    M.vstar x = (M.Γ x).sup' (M.Γ_nonempty x) fun a =>
      M.r x a + ∑ x', M.vstar x' * M.β x a x' * M.P x a x' :=
  (congrFun (M.isFixedPt_T_vstar hM).eq x).symm

omit [Nonempty X] in
/-- Optimality is `v_σ ≥ v_σ'` for every feasible `σ'`. -/
theorem isOptimal_iff (σ : X → A) :
    M.IsOptimal σ ↔ M.IsFeasible σ ∧ ∀ (σ' : M.Policy) (x : X), M.vσ σ'.1 x ≤ M.vσ σ x := by
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, fun σ' x => ?_⟩
    rw [h]
    exact M.vσ_le_vstar σ' x
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, funext fun x => le_antisymm (M.vσ_le_vstar ⟨σ, hσ⟩ x) ?_⟩
    exact Finset.sup'_le _ _ fun σ' _ => h σ' x

/-- **Proposition 6.2.2 (ii)** (p. 194): a policy is optimal iff it is `v*`-greedy. -/
theorem isOptimal_iff_isGreedy (hM : M.SpectralCondition) (σ : X → A) :
    M.IsOptimal σ ↔ M.IsGreedy M.vstar σ := by
  constructor
  · rintro ⟨hσ, h⟩
    rw [M.isGreedy_iff_Tσ_eq_T M.vstar ⟨σ, hσ⟩]
    -- `T_σ v* = T_σ v_σ = v_σ = v* = Tv*`
    rw [← h, (M.isFixedPt_vσ (hM σ hσ)).eq, h, (M.isFixedPt_T_vstar hM).eq]
  · intro h
    exact ⟨h.1, M.vσ_eq_vstar_of_isGreedy hM h⟩

/-- **Proposition 6.2.2 (iii)** (p. 195): an optimal policy exists, namely any `v*`-greedy one. -/
theorem isOptimal_greedy_vstar (hM : M.SpectralCondition) : M.IsOptimal (M.greedy M.vstar) :=
  (M.isOptimal_iff_isGreedy hM _).2 (M.isGreedy_greedy _)

theorem exists_isOptimal (hM : M.SpectralCondition) : ∃ σ : X → A, M.IsOptimal σ :=
  ⟨_, M.isOptimal_greedy_vstar hM⟩

/-! ### Algorithms (§6.2.1.4) -/

omit [DecidableEq A] [Nonempty X] in
/-- Algorithm 6.1, line 5: the HPI value update is `v_{k+1} = (I − L_{σₖ})⁻¹ r_{σₖ} = v_{σₖ}`. -/
theorem hpi_update_eq_vσ (σ : X → A) : (1 - M.Lσ σ)⁻¹ *ᵥ M.rσ σ = M.vσ σ := by
  classical
  exact rfl

omit [DecidableEq A] in
/-- HPI (Algorithm 6.1), the improvement step: if `σ'` is `v_σ`-greedy then `v_σ ≤ v_σ'`. -/
theorem vσ_le_vσ_of_isGreedy (hM : M.SpectralCondition) {σ : X → A} (hσ : M.IsFeasible σ)
    {σ' : X → A} (hσ' : M.IsGreedy (M.vσ σ) σ') : M.vσ σ ≤ M.vσ σ' := by
  classical
  have h : M.vσ σ ≤ M.Tσ σ' (M.vσ σ) := by
    rw [M.Tσ_eq_T_of_isGreedy hσ']
    calc M.vσ σ = M.Tσ σ (M.vσ σ) := (M.isFixedPt_vσ (hM σ hσ)).eq.symm
      _ ≤ M.T (M.vσ σ) := M.Tσ_le_T ⟨σ, hσ⟩ _
  exact le_fixedPt_of_le_apply (M.Tσ_monotone σ') h (M.tendsto_iterate_Tσ (hM σ' hσ'.1) _)

/-- HPI (Algorithm 6.1), the termination criterion (line 6): if `σ'` is `v_σ`-greedy and
`v_σ' = v_σ`, then `σ'` is optimal. -/
theorem isOptimal_of_hpi_fixed (hM : M.SpectralCondition) {σ σ' : X → A}
    (hσ' : M.IsGreedy (M.vσ σ) σ') (heq : M.vσ σ' = M.vσ σ) : M.IsOptimal σ' := by
  have hfix : IsFixedPt M.T (M.vσ σ) := by
    rw [IsFixedPt, ← M.Tσ_eq_T_of_isGreedy hσ', ← heq]
    exact (M.isFixedPt_vσ (hM σ' hσ'.1)).eq
  refine ⟨hσ'.1, ?_⟩
  rw [heq]
  exact M.eq_vstar_of_isFixedPt hM hfix

omit [DecidableEq X] [DecidableEq A] [Nonempty X] in
/-- OPI with `m = 1` is VFI (p. 195): for a `v`-greedy `σ`, `T_σ v = Tv`. -/
theorem opi_one_step_eq_vfi {v : X → ℝ} {σ : X → A} (hσ : M.IsGreedy v σ) :
    (M.Tσ σ)^[1] v = M.T v := by
  rw [iterate_one]
  exact M.Tσ_eq_T_of_isGreedy hσ

omit [DecidableEq A] in
/-- OPI approximates HPI as `m → ∞`: `T_σᵐ v → v_σ` (p. 195). -/
theorem tendsto_opi_inner {σ : X → A} (hρ : specRad (M.Lσ σ) < 1) (v : X → ℝ) :
    Tendsto (fun m : ℕ => (M.Tσ σ)^[m] v) atTop (𝓝 (M.vσ σ)) :=
  M.tendsto_iterate_Tσ hρ v

/-! ### Value function iteration under a dominating discount operator -/

omit [DecidableEq X] [DecidableEq A] [Nonempty X] in
/-- Under the condition (6.20) of Exercise 6.2.3, `T` satisfies (6.13): `|Tv − Tw| ≤ L|v − w|`. -/
theorem abs_T_sub_le_of_dominated {L : Matrix X X ℝ}
    (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x') (v w : X → ℝ) (x : X) :
    |M.T v x - M.T w x| ≤ (L *ᵥ fun y => |v y - w y|) x := by
  rw [T_apply, T_apply]
  refine (abs_sup'_sub_sup'_le _ _ _).trans (Finset.sup'_le _ _ fun a ha => ?_)
  rw [add_sub_add_left_eq_sub, ← sum_sub_distrib]
  calc |∑ x', (v x' * M.β x a x' * M.P x a x' - w x' * M.β x a x' * M.P x a x')|
      ≤ ∑ x', |v x' - w x'| * (M.β x a x' * M.P x a x') := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => le_of_eq ?_)
        rw [show v x' * M.β x a x' * M.P x a x' - w x' * M.β x a x' * M.P x a x' =
          (v x' - w x') * (M.β x a x' * M.P x a x') by ring, abs_mul,
          abs_of_nonneg (mul_nonneg (M.β_nonneg x a x') (M.P_nonneg x a x'))]
    _ ≤ ∑ x', |v x' - w x'| * L x x' := sum_le_sum fun x' _ =>
        mul_le_mul_of_nonneg_left (hdom x a x' ha) (abs_nonneg _)
    _ = (L *ᵥ fun y => |v y - w y|) x := by
        simp only [mulVec, dotProduct]
        exact sum_congr rfl fun x' _ => mul_comm _ _

omit [DecidableEq X] [DecidableEq A] in
/-- Value function iteration under (6.20): `T` is globally stable on `ℝ^X`, by
Proposition 6.1.6 and Theorem 6.1.5. -/
theorem globallyStable_T_of_dominated {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x') :
    GloballyStable M.T := by
  classical
  obtain ⟨k, hk, hc⟩ := exists_isContractionOn_iterate_of_abs_sub_le
    (Set.mapsTo_univ M.T Set.univ) hL hρ fun v _ w _ x => M.abs_T_sub_le_of_dominated hdom v w x
  exact globallyStable_of_iterate_contraction_univ hk hc

/-- Value function iteration under (6.20): `Tᵏv → v*` for every `v`. -/
theorem tendsto_iterate_T_of_dominated {L : Matrix X X ℝ} (hL : ∀ x x', 0 ≤ L x x')
    (hρ : specRad L < 1) (hdom : ∀ x a x', a ∈ M.Γ x → M.β x a x' * M.P x a x' ≤ L x x')
    (v : X → ℝ) : Tendsto (fun k : ℕ => M.T^[k] v) atTop (𝓝 M.vstar) := by
  obtain ⟨u', hu', -, hconv⟩ := M.globallyStable_T_of_dominated hL hρ hdom
  rw [M.eq_vstar_of_isFixedPt (M.spectralCondition_of_dominated hρ hdom) hu'] at hconv
  exact hconv v

end SDMDP

end SargentStachurski.StochasticDiscounting
