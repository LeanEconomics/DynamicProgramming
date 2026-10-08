/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonotonePolicies.Topkis
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Order.Field

/-!
# Monotone optimal policies in finite dynamic programs

Topkis (1998); Stokey and Lucas (1989, Ch. 9); Hopenhayn and Prescott (1992).

A finite dynamic program (`FDP`) has finite states `X`, finite feasible action sets `Γ(x)`,
reward `r(x, a)`, discount `β ∈ [0, 1)` and transition probabilities `P(x, a, ·)`. We prove the
optimality theory we need from scratch (the Bellman operator is a `β`-contraction; a policy is
optimal iff it is greedy for `v*`), and then:

* `optimal_monotone`: if the feasible sets are ascending and
  `Q(x, a) = r(x, a) + β E[v*(x') | x, a]` has increasing differences, the greatest optimal
  policy is increasing in the state; `optimal_le_of_strict`: with strictly increasing
  differences every optimal policy is.
* `vstar_monotone`: `v*` is increasing when `r` is increasing in `x`, `Γ` expands with `x` and
  `P(x, a, ·)` increases with `x` in first-order stochastic dominance.
* `id_Q_of_actionKernel`, `id_Q_of_continuation`: two sufficient conditions for increasing
  differences of `Q` — the next state depends on the action only, or the expected continuation
  of an increasing function has increasing differences (then `v*` must be increasing).
* `monotoneKernel_comp`: under an increasing policy and a kernel that is FOSD-increasing in the
  action, the induced state chain is monotone, the hypothesis of Hopenhayn and Prescott's
  stationary-distribution theorem.
-/

open Finset Filter Topology

namespace DPExtensions.MonotonePolicies

variable (X A : Type*) [Fintype X] in
/-- A finite dynamic program. -/
structure FDP where
  /-- the feasible actions -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward -/
  r : X → A → ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x a y, 0 ≤ P x a y
  P_sum : ∀ x a, ∑ y, P x a y = 1

/-- A kernel is monotone if it maps increasing functions to increasing functions (the rows
increase in first-order stochastic dominance). -/
def MonotoneKernel {X Y : Type*} [Preorder X] [Preorder Y] [Fintype Y] (K : X → Y → ℝ) : Prop :=
  ∀ v : Y → ℝ, Monotone v → Monotone fun x => ∑ y, v y * K x y

namespace FDP

variable {X A : Type*} [Fintype X] (M : FDP X A)

/-- The action value `Q_v(x, a) = r(x, a) + β ∑_y v(y)P(x, a, y)`. -/
noncomputable def Q (v : X → ℝ) (x : X) (a : A) : ℝ := M.r x a + M.β * ∑ y, v y * M.P x a y

/-- The Bellman operator. -/
noncomputable def T (v : X → ℝ) (x : X) : ℝ := (M.Γ x).sup' (M.Γ_nonempty x) (M.Q v x)

/-- The policy operator of `σ : X → A`. -/
noncomputable def Tσ (σ : X → A) (v : X → ℝ) (x : X) : ℝ := M.Q v x (σ x)

/-- Feasible policies. -/
def IsPolicy (σ : X → A) : Prop := ∀ x, σ x ∈ M.Γ x

theorem abs_sum_sub_le (v w : X → ℝ) (x : X) (a : A) :
    |∑ y, v y * M.P x a y - ∑ y, w y * M.P x a y| ≤ ‖v - w‖ := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y, |v y * M.P x a y - w y * M.P x a y| = ∑ y, |v y - w y| * M.P x a y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (M.P_nonneg x a y)]
    _ ≤ ∑ y, ‖v - w‖ * M.P x a y := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right ?_ (M.P_nonneg x a y)
        have := norm_le_pi_norm (v - w) y
        rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    _ = ‖v - w‖ := by rw [← Finset.mul_sum, M.P_sum, mul_one]

theorem abs_Q_sub_le (v w : X → ℝ) (x : X) (a : A) :
    |M.Q v x a - M.Q w x a| ≤ M.β * ‖v - w‖ := by
  simp only [Q, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg M.β_nonneg]
  exact mul_le_mul_of_nonneg_left (M.abs_sum_sub_le v w x a) M.β_nonneg

theorem norm_T_sub_le (v w : X → ℝ) : ‖M.T v - M.T w‖ ≤ M.β * ‖v - w‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun x => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun a ha => ?_)
    have h1 := (abs_sub_le_iff.1 (M.abs_Q_sub_le v w x a)).1
    have h2 := Finset.le_sup' (M.Q w x) ha
    simp only [T]
    linarith
  · refine sub_le_iff_le_add.2 (Finset.sup'_le _ _ fun a ha => ?_)
    have h1 := (abs_sub_le_iff.1 (M.abs_Q_sub_le v w x a)).2
    have h2 := Finset.le_sup' (M.Q v x) ha
    simp only [T]
    linarith

theorem norm_Tσ_sub_le (σ : X → A) (v w : X → ℝ) : ‖M.Tσ σ v - M.Tσ σ w‖ ≤ M.β * ‖v - w‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg M.β_nonneg (norm_nonneg _))).2 fun x => by
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact M.abs_Q_sub_le v w x (σ x)

theorem contracting_T : ContractingWith ⟨M.β, M.β_nonneg⟩ M.T :=
  ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_T_sub_le v w⟩

theorem contracting_Tσ (σ : X → A) : ContractingWith ⟨M.β, M.β_nonneg⟩ (M.Tσ σ) :=
  ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.norm_Tσ_sub_le σ v w⟩

/-- The value function: the fixed point of `T`. -/
noncomputable def vstar : X → ℝ := ContractingWith.fixedPoint M.T M.contracting_T

/-- The value of the policy `σ`: the fixed point of `T_σ`. -/
noncomputable def vσ (σ : X → A) : X → ℝ := ContractingWith.fixedPoint (M.Tσ σ) (M.contracting_Tσ σ)

theorem T_vstar : M.T M.vstar = M.vstar := ContractingWith.fixedPoint_isFixedPt _

theorem Tσ_vσ (σ : X → A) : M.Tσ σ (M.vσ σ) = M.vσ σ := ContractingWith.fixedPoint_isFixedPt _

theorem Q_mono {v w : X → ℝ} (h : v ≤ w) (x : X) (a : A) : M.Q v x a ≤ M.Q w x a := by
  simp only [Q]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_)
    M.β_nonneg)
  exact mul_le_mul_of_nonneg_right (h y) (M.P_nonneg x a y)

theorem T_mono : Monotone M.T := fun _ w h x =>
  Finset.sup'_le _ _ fun a ha => (M.Q_mono h x a).trans (Finset.le_sup' (M.Q w x) ha)

theorem Tσ_le_T {σ : X → A} (hσ : M.IsPolicy σ) (v : X → ℝ) : M.Tσ σ v ≤ M.T v := fun x =>
  Finset.le_sup' (M.Q v x) (hσ x)

/-- If `v ≤ Tv` then `v ≤ v*`. -/
theorem le_vstar_of_le_T {v : X → ℝ} (h : v ≤ M.T v) : v ≤ M.vstar := by
  have hit : ∀ n, v ≤ M.T^[n] v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact h.trans (M.T_mono ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint M.contracting_T v) hit

theorem vσ_le_vstar {σ : X → A} (hσ : M.IsPolicy σ) : M.vσ σ ≤ M.vstar :=
  M.le_vstar_of_le_T (by
    have := M.Tσ_le_T hσ (M.vσ σ)
    rwa [M.Tσ_vσ] at this)

/-- `σ` is greedy for `v` when it picks a maximizer of `Q_v(x, ·)` at every state. -/
def IsGreedy (σ : X → A) (v : X → ℝ) : Prop := ∀ x, σ x ∈ argmaxSet M.Γ (M.Q v) x

theorem IsGreedy.isPolicy {σ : X → A} {v : X → ℝ} (h : M.IsGreedy σ v) : M.IsPolicy σ :=
  fun x => (mem_argmaxSet.1 (h x)).1

theorem Tσ_eq_T_of_greedy {σ : X → A} {v : X → ℝ} (h : M.IsGreedy σ v) : M.Tσ σ v = M.T v :=
  funext fun x => le_antisymm (Finset.le_sup' (M.Q v x) (mem_argmaxSet.1 (h x)).1)
    (Finset.sup'_le _ _ fun b hb => (mem_argmaxSet.1 (h x)).2 b hb)

theorem vσ_eq_vstar_of_greedy {σ : X → A} (h : M.IsGreedy σ M.vstar) : M.vσ σ = M.vstar := by
  have hfix : Function.IsFixedPt (M.Tσ σ) M.vstar := by
    unfold Function.IsFixedPt
    rw [M.Tσ_eq_T_of_greedy h, M.T_vstar]
  exact (ContractingWith.fixedPoint_unique (M.contracting_Tσ σ) hfix).symm

/-- A policy is optimal if its value dominates that of every feasible policy. -/
def IsOptimal (σ : X → A) : Prop := M.IsPolicy σ ∧ ∀ τ, M.IsPolicy τ → M.vσ τ ≤ M.vσ σ

/-- Greedy policies for `v*` are optimal. -/
theorem greedy_optimal {σ : X → A} (h : M.IsGreedy σ M.vstar) : M.IsOptimal σ :=
  ⟨h.isPolicy, fun τ hτ => by rw [M.vσ_eq_vstar_of_greedy h]; exact M.vσ_le_vstar hτ⟩

/-- A greedy policy for `v*` exists. -/
theorem exists_greedy : ∃ σ, M.IsGreedy σ M.vstar := by
  classical
  refine ⟨fun x => (argmaxSet_nonempty M.Γ_nonempty (M.Q M.vstar) x).choose, fun x => ?_⟩
  exact (argmaxSet_nonempty M.Γ_nonempty (M.Q M.vstar) x).choose_spec

/-- Optimal policies are greedy for `v*`. -/
theorem optimal_greedy {σ : X → A} (h : M.IsOptimal σ) : M.IsGreedy σ M.vstar := by
  obtain ⟨σ', hσ'⟩ := M.exists_greedy
  have hv : M.vσ σ = M.vstar := le_antisymm (M.vσ_le_vstar h.1)
    (by rw [← M.vσ_eq_vstar_of_greedy hσ']; exact h.2 σ' hσ'.isPolicy)
  have hT : M.Tσ σ M.vstar = M.T M.vstar := by
    rw [← hv, M.Tσ_vσ, hv, M.T_vstar]
  intro x
  refine mem_argmaxSet.2 ⟨h.1 x, fun b hb => ?_⟩
  have := congrFun hT x
  simp only [Tσ, T] at this
  rw [this]
  exact Finset.le_sup' (M.Q M.vstar x) hb

/-! ### Monotone optimal policies -/

variable [Preorder X] [LinearOrder A]

/-- **Monotone optimal policy**: with `Γ` ascending and `Q_{v*}` having increasing differences,
the greatest optimal policy `x ↦ max argmax Q_{v*}(x, ·)` is optimal and increasing. -/
theorem optimal_monotone (hΓ : Ascending M.Γ) (hQ : IncreasingDifferences (M.Q M.vstar)) :
    M.IsOptimal (gmax M.Γ_nonempty (M.Q M.vstar)) ∧ Monotone (gmax M.Γ_nonempty (M.Q M.vstar)) :=
  ⟨M.greedy_optimal fun x => gmax_mem _ _ x, topkis_gmax M.Γ_nonempty hΓ hQ⟩

/-- The least optimal policy is also optimal and increasing. -/
theorem optimal_monotone_least (hΓ : Ascending M.Γ) (hQ : IncreasingDifferences (M.Q M.vstar)) :
    M.IsOptimal (lmax M.Γ_nonempty (M.Q M.vstar)) ∧ Monotone (lmax M.Γ_nonempty (M.Q M.vstar)) :=
  ⟨M.greedy_optimal fun x => lmax_mem _ _ x, topkis_lmax M.Γ_nonempty hΓ hQ⟩

/-- With strictly increasing differences every optimal policy is increasing on strictly ordered
states. -/
theorem optimal_le_of_strict (hΓ : Ascending M.Γ)
    (hQ : StrictIncreasingDifferences (M.Q M.vstar)) {σ : X → A} (hσ : M.IsOptimal σ)
    {x x' : X} (hx : x < x') : σ x ≤ σ x' :=
  topkis_strict hΓ hQ hx (M.optimal_greedy hσ x) (M.optimal_greedy hσ x')

/-- If the next state depends on the action only, `Q_v` has increasing differences whenever `r`
does, for every continuation value `v`. -/
theorem id_Q_of_actionKernel (hr : IncreasingDifferences M.r)
    (hP : ∀ x x' a, M.P x a = M.P x' a) (v : X → ℝ) : IncreasingDifferences (M.Q v) := by
  intro x x' hx a a' ha
  have h := hr hx ha
  simp only [Q, hP x' x]
  linarith

/-- If the expected continuation of every increasing function has increasing differences, then
`Q_v` has increasing differences for increasing `v` whenever `r` does. -/
theorem id_Q_of_continuation (hr : IncreasingDifferences M.r)
    (hP : ∀ v : X → ℝ, Monotone v → IncreasingDifferences fun x a => ∑ y, v y * M.P x a y)
    {v : X → ℝ} (hv : Monotone v) : IncreasingDifferences (M.Q v) := by
  intro x x' hx a a' ha
  have h1 := hr hx ha
  have h2 := hP v hv hx ha
  simp only [Q]
  nlinarith [M.β_nonneg]

omit [LinearOrder A] in
/-- **Monotone value function**: if `r` is increasing in the state, `Γ` expands with the state
and `P(x, a, ·)` is FOSD-increasing in `x`, then `v*` is increasing. -/
theorem vstar_monotone (hr : ∀ a, Monotone fun x => M.r x a)
    (hΓ : ∀ ⦃x x' : X⦄, x ≤ x' → M.Γ x ⊆ M.Γ x')
    (hP : ∀ a, MonotoneKernel fun x y => M.P x a y) : Monotone M.vstar := by
  have hT : ∀ v : X → ℝ, Monotone v → Monotone (M.T v) := by
    intro v hv x x' hx
    refine Finset.sup'_le _ _ fun a ha => ?_
    refine le_trans ?_ (Finset.le_sup' (M.Q v x') (hΓ hx ha))
    simp only [Q]
    exact add_le_add (hr a hx) (mul_le_mul_of_nonneg_left (hP a v hv hx) M.β_nonneg)
  have hit : ∀ n, Monotone (M.T^[n] 0) := by
    intro n
    induction n with
    | zero => exact monotone_const
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hT _ ih
  have hlim := ContractingWith.tendsto_iterate_fixedPoint M.contracting_T 0
  intro x x' hx
  exact le_of_tendsto_of_tendsto' ((continuous_apply x).continuousAt.tendsto.comp hlim)
    ((continuous_apply x').continuousAt.tendsto.comp hlim) fun n => hit n hx

/-- **The general monotone policy theorem**: `r` with increasing differences, increasing in
the state; `Γ` ascending and expanding; `P` FOSD-increasing in the state, with increasing
differences of the expected continuation of increasing functions. Then the greatest optimal
policy is increasing. -/
theorem optimal_monotone_of_primitives (hrid : IncreasingDifferences M.r)
    (hr : ∀ a, Monotone fun x => M.r x a) (hΓ : Ascending M.Γ)
    (hΓe : ∀ ⦃x x' : X⦄, x ≤ x' → M.Γ x ⊆ M.Γ x')
    (hP : ∀ a, MonotoneKernel fun x y => M.P x a y)
    (hPid : ∀ v : X → ℝ, Monotone v → IncreasingDifferences fun x a => ∑ y, v y * M.P x a y) :
    M.IsOptimal (gmax M.Γ_nonempty (M.Q M.vstar)) ∧ Monotone (gmax M.Γ_nonempty (M.Q M.vstar)) :=
  M.optimal_monotone hΓ (M.id_Q_of_continuation hrid hPid (M.vstar_monotone hr hΓe hP))

end FDP

/-- **The state chain under a monotone policy is monotone**: if `σ` is increasing and the
action kernel `K(a, ·)` is FOSD-increasing in `a`, then `x ↦ K(σ(x), ·)` is a monotone
kernel. -/
theorem monotoneKernel_comp {X A Y : Type*} [Preorder X] [Preorder A] [Preorder Y] [Fintype Y]
    {K : A → Y → ℝ} (hK : MonotoneKernel K) {σ : X → A} (hσ : Monotone σ) :
    MonotoneKernel fun x y => K (σ x) y :=
  fun v hv _ _ hx => hK v hv (hσ hx)

end DPExtensions.MonotonePolicies
