import Mathlib.Analysis.Convex.Function
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Order.Field
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Topkis's monotonicity theorem

Topkis (1978), "Minimizing a submodular function on a lattice"; Topkis (1998), *Supermodularity
and Complementarity*; Milgrom and Shannon (1994).

Let the state (or parameter) `x` range over a preorder and the action `a` over a linear order,
with finite feasible sets `Γ(x)` that are **ascending** in the strong set order:
`x ≤ x'`, `a ∈ Γ(x)`, `a' ∈ Γ(x')` give `min a a' ∈ Γ(x)` and `max a a' ∈ Γ(x')`. If the
objective `f(x, a)` has **increasing differences** — `f(x, a') − f(x, a)` is increasing in `x`
for `a ≤ a'` — then:

* `argmax_strongSetOrder`: the argmax sets are ascending in the strong set order;
* `topkis_gmax`, `topkis_lmax`: the greatest and the least maximizers are increasing in `x`;
* `topkis_strict`: with strictly increasing differences every selection from the argmax is
  increasing.

Increasing differences hold for `u(m(x) − g(a))` with `u` concave and `m`, `g` increasing
(`increasingDifferences_concave`: consumption is the residual of a budget), for objectives that
do not mix `x` and `a` (`increasingDifferences_of_sep`), for products of increasing functions
(`increasingDifferences_mul`), and are preserved by sums (`IncreasingDifferences.add`).
-/

open Finset

namespace DPExtensions.MonotonePolicies

variable {X A : Type*} [Preorder X] [LinearOrder A]

/-- `f` has increasing differences: `f(x, a') − f(x, a)` is increasing in `x` for `a ≤ a'`. -/
def IncreasingDifferences (f : X → A → ℝ) : Prop :=
  ∀ ⦃x x' : X⦄, x ≤ x' → ∀ ⦃a a' : A⦄, a ≤ a' → f x a' - f x a ≤ f x' a' - f x' a

/-- `f` has strictly increasing differences. -/
def StrictIncreasingDifferences (f : X → A → ℝ) : Prop :=
  ∀ ⦃x x' : X⦄, x < x' → ∀ ⦃a a' : A⦄, a < a' → f x a' - f x a < f x' a' - f x' a

/-- `Γ` is ascending in the strong set order. -/
def Ascending (Γ : X → Finset A) : Prop :=
  ∀ ⦃x x' : X⦄, x ≤ x' → ∀ a ∈ Γ x, ∀ a' ∈ Γ x', min a a' ∈ Γ x ∧ max a a' ∈ Γ x'

theorem IncreasingDifferences.add {f g : X → A → ℝ} (hf : IncreasingDifferences f)
    (hg : IncreasingDifferences g) : IncreasingDifferences fun x a => f x a + g x a :=
  fun _ _ hx _ _ ha => by linarith [hf hx ha, hg hx ha]

theorem IncreasingDifferences.const_mul {f : X → A → ℝ} (hf : IncreasingDifferences f) {c : ℝ}
    (hc : 0 ≤ c) : IncreasingDifferences fun x a => c * f x a :=
  fun _ _ hx _ _ ha => by nlinarith [hf hx ha]

/-- An objective that does not mix `x` and `a` has increasing differences. -/
theorem increasingDifferences_of_sep (g : X → ℝ) (h : A → ℝ) :
    IncreasingDifferences fun x a => g x + h a :=
  fun _ _ _ _ _ _ => by linarith

/-- `φ(x)ψ(a)` with `φ`, `ψ` increasing has increasing differences. -/
theorem increasingDifferences_mul {φ : X → ℝ} {ψ : A → ℝ} (hφ : Monotone φ) (hψ : Monotone ψ) :
    IncreasingDifferences fun x a => φ x * ψ a := fun _ _ hx _ _ ha => by
  nlinarith [hφ hx, hψ ha]

/-- For concave `u`, increments shrink: `s ≤ t` and `d ≥ 0` give
`u(t + d) − u(t) ≤ u(s + d) − u(s)`. -/
theorem concave_increment {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) {s t d : ℝ} (hst : s ≤ t)
    (hd : 0 ≤ d) : u (t + d) - u t ≤ u (s + d) - u s := by
  rcases eq_or_lt_of_le hd with h0 | hd'
  · subst h0
    simp
  have hden : 0 < t + d - s := by linarith
  set l := d / (t + d - s) with hl
  have hl0 : 0 ≤ l := div_nonneg hd hden.le
  have hl1 : l ≤ 1 := (div_le_one hden).2 (by linarith)
  have e1 : (1 - l) * s + l * (t + d) = s + d := by
    rw [hl]
    field_simp
    ring
  have e2 : l * s + (1 - l) * (t + d) = t := by
    rw [hl]
    field_simp
    ring
  have h1 := hu.2 (Set.mem_univ s) (Set.mem_univ (t + d)) (by linarith : 0 ≤ 1 - l) hl0
    (by ring : 1 - l + l = 1)
  have h2 := hu.2 (Set.mem_univ s) (Set.mem_univ (t + d)) hl0 (by linarith : 0 ≤ 1 - l)
    (by ring : l + (1 - l) = 1)
  simp only [smul_eq_mul] at h1 h2
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- **Budget-residual objectives**: `u(m(x) − g(a))` with `u` concave and `m`, `g` increasing has
increasing differences. With `m` cash on hand and `g(a)` saving, more cash makes saving more
attractive at the margin. -/
theorem increasingDifferences_concave {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) {m : X → ℝ}
    {g : A → ℝ} (hm : Monotone m) (hg : Monotone g) :
    IncreasingDifferences fun x a => u (m x - g a) := by
  intro x x' hx a a' ha
  have h := concave_increment hu (s := m x - g a') (t := m x' - g a') (d := g a' - g a)
    (by linarith [hm hx]) (by linarith [hg ha])
  have e1 : m x' - g a' + (g a' - g a) = m x' - g a := by ring
  have e2 : m x - g a' + (g a' - g a) = m x - g a := by ring
  rw [e1, e2] at h
  linarith

/-- The maximizers of `f(x, ·)` on `Γ(x)`. -/
noncomputable def argmaxSet (Γ : X → Finset A) (f : X → A → ℝ) (x : X) : Finset A :=
  (Γ x).filter fun a => ∀ b ∈ Γ x, f x b ≤ f x a

omit [Preorder X] [LinearOrder A] in
theorem mem_argmaxSet {Γ : X → Finset A} {f : X → A → ℝ} {x : X} {a : A} :
    a ∈ argmaxSet Γ f x ↔ a ∈ Γ x ∧ ∀ b ∈ Γ x, f x b ≤ f x a := by
  unfold argmaxSet
  exact mem_filter

omit [Preorder X] [LinearOrder A] in
theorem argmaxSet_nonempty {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ)
    (x : X) : (argmaxSet Γ f x).Nonempty := by
  obtain ⟨a, ha, hmax⟩ := (Γ x).exists_max_image (f x) (hΓ x)
  exact ⟨a, mem_argmaxSet.2 ⟨ha, hmax⟩⟩

/-- **Topkis**: the argmax sets are ascending in the strong set order. -/
theorem argmax_strongSetOrder {Γ : X → Finset A} (hΓ : Ascending Γ) {f : X → A → ℝ}
    (hf : IncreasingDifferences f) {x x' : X} (hx : x ≤ x') {a a' : A}
    (ha : a ∈ argmaxSet Γ f x) (ha' : a' ∈ argmaxSet Γ f x') :
    min a a' ∈ argmaxSet Γ f x ∧ max a a' ∈ argmaxSet Γ f x' := by
  rw [mem_argmaxSet] at ha ha'
  rcases le_total a a' with h | h
  · rw [min_eq_left h, max_eq_right h]
    exact ⟨mem_argmaxSet.2 ha, mem_argmaxSet.2 ha'⟩
  · rw [min_eq_right h, max_eq_left h]
    obtain ⟨h1, h2⟩ := hΓ hx a ha.1 a' ha'.1
    rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    have i1 := ha.2 a' h1
    have i2 := ha'.2 a h2
    have i3 := hf hx h
    refine ⟨mem_argmaxSet.2 ⟨h1, fun b hb => ?_⟩, mem_argmaxSet.2 ⟨h2, fun b hb => ?_⟩⟩
    · linarith [ha.2 b hb]
    · linarith [ha'.2 b hb]

/-- The greatest maximizer. -/
noncomputable def gmax {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    A :=
  (argmaxSet Γ f x).max' (argmaxSet_nonempty hΓ f x)

/-- The least maximizer. -/
noncomputable def lmax {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    A :=
  (argmaxSet Γ f x).min' (argmaxSet_nonempty hΓ f x)

omit [Preorder X] in
theorem gmax_mem {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    gmax hΓ f x ∈ argmaxSet Γ f x :=
  max'_mem _ _

omit [Preorder X] in
theorem lmax_mem {Γ : X → Finset A} (hΓ : ∀ x, (Γ x).Nonempty) (f : X → A → ℝ) (x : X) :
    lmax hΓ f x ∈ argmaxSet Γ f x :=
  min'_mem _ _

/-- **Topkis's theorem**: the greatest maximizer is increasing. -/
theorem topkis_gmax {Γ : X → Finset A} (hne : ∀ x, (Γ x).Nonempty) (hΓ : Ascending Γ)
    {f : X → A → ℝ} (hf : IncreasingDifferences f) : Monotone (gmax hne f) := by
  intro x x' hx
  have h := (argmax_strongSetOrder hΓ hf hx (gmax_mem hne f x) (gmax_mem hne f x')).2
  exact (le_max_left _ _).trans (le_max' _ _ h)

/-- **Topkis's theorem**: the least maximizer is increasing. -/
theorem topkis_lmax {Γ : X → Finset A} (hne : ∀ x, (Γ x).Nonempty) (hΓ : Ascending Γ)
    {f : X → A → ℝ} (hf : IncreasingDifferences f) : Monotone (lmax hne f) := by
  intro x x' hx
  have h := (argmax_strongSetOrder hΓ hf hx (lmax_mem hne f x) (lmax_mem hne f x')).1
  exact (min'_le _ _ h).trans (min_le_right _ _)

/-- With strictly increasing differences every maximizer at `x` lies below every maximizer at
`x' > x`. -/
theorem topkis_strict {Γ : X → Finset A} (hΓ : Ascending Γ) {f : X → A → ℝ}
    (hf : StrictIncreasingDifferences f) {x x' : X} (hx : x < x') {a a' : A}
    (ha : a ∈ argmaxSet Γ f x) (ha' : a' ∈ argmaxSet Γ f x') : a ≤ a' := by
  by_contra h
  push Not at h
  rw [mem_argmaxSet] at ha ha'
  obtain ⟨h1, h2⟩ := hΓ hx.le a ha.1 a' ha'.1
  rw [min_eq_right h.le] at h1
  rw [max_eq_left h.le] at h2
  linarith [ha.2 a' h1, ha'.2 a h2, hf hx h]

end DPExtensions.MonotonePolicies

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Saving rises with wealth and income

A household with assets on a finite grid `ι` (asset level `level(a)`) and income state `z ∈ Z`
has cash on hand `m(a, z) = R·level(a) + y(z)`, chooses next-period assets `a'` with
`level(a') ≤ m(a, z)` and consumes `m(a, z) − level(a')`, with utility `u` concave. Income is
i.i.d. with distribution `π`. This is the household problem of Bewley–Huggett–Aiyagari models
on a grid.

* `SavingsModel.savings_monotone`: for any concave `u`, any `β ∈ [0, 1)`, `R ≥ 0`, increasing
  asset levels and income, the greatest optimal saving rule is increasing in assets and in
  income (in the product order) — no differentiability, interiority or monotonicity of the value
  function is needed, since next period's state depends on today's state only through the
  choice `a'`.
* `SavingsModel.chain_monotone`: under that rule the household's state `(a, z)` follows a
  monotone Markov chain, the input to the stationary-distribution theory of Hopenhayn and
  Prescott (1992).
-/

open Finset

namespace DPExtensions.MonotonePolicies

variable (ι Z : Type*) [Fintype ι] [Fintype Z] in
/-- A savings problem with i.i.d. income on an asset grid. -/
structure SavingsModel where
  /-- the asset level at each grid point -/
  level : ι → ℝ
  /-- the gross return -/
  R : ℝ
  R_nonneg : 0 ≤ R
  /-- income in each income state -/
  y : Z → ℝ
  /-- the period utility -/
  u : ℝ → ℝ
  u_concave : ConcaveOn ℝ Set.univ u
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the income distribution -/
  π : Z → ℝ
  π_nonneg : ∀ z, 0 ≤ π z
  π_sum : ∑ z, π z = 1
  /-- a grid point affordable in every state (the borrowing limit) -/
  a₀ : ι
  a₀_feasible : ∀ a z, level a₀ ≤ R * level a + y z

namespace SavingsModel

variable {ι Z : Type*} [Fintype ι] [Fintype Z] [DecidableEq ι] (S : SavingsModel ι Z)

/-- Cash on hand. -/
def cash (x : ι × Z) : ℝ := S.R * S.level x.1 + S.y x.2

/-- The next-state kernel given the choice `a'`: assets `a'`, income drawn from `π`. -/
def K (a : ι) (x' : ι × Z) : ℝ := if x'.1 = a then S.π x'.2 else 0

theorem K_sum (a : ι) : ∑ x', S.K a x' = 1 := by
  rw [Fintype.sum_prod_type]
  simp [K, S.π_sum]

/-- The savings problem as a finite dynamic program. -/
noncomputable def toFDP : FDP (ι × Z) ι where
  Γ x := univ.filter fun a => S.level a ≤ S.cash x
  Γ_nonempty x := ⟨S.a₀, mem_filter.2 ⟨mem_univ _, S.a₀_feasible x.1 x.2⟩⟩
  r x a := S.u (S.cash x - S.level a)
  β := S.β
  β_nonneg := S.β_nonneg
  β_lt_one := S.β_lt_one
  P _ a x' := S.K a x'
  P_nonneg _ a x' := by
    simp only [K]
    split_ifs
    · exact S.π_nonneg _
    · exact le_rfl
  P_sum _ a := S.K_sum a

theorem sum_mul_K (v : ι × Z → ℝ) (a : ι) : ∑ x', v x' * S.K a x' = ∑ z, v (a, z) * S.π z := by
  rw [Fintype.sum_prod_type]
  simp [K, mul_ite]

variable [LinearOrder ι] [Preorder Z]

omit [Fintype ι] [DecidableEq ι] in
theorem cash_monotone (hl : Monotone S.level) (hy : Monotone S.y) : Monotone S.cash :=
  fun _ _ hx => add_le_add (mul_le_mul_of_nonneg_left (hl hx.1) S.R_nonneg) (hy hx.2)

/-- The budget sets are ascending in the strong set order. -/
theorem ascending (hl : Monotone S.level) (hy : Monotone S.y) : Ascending S.toFDP.Γ := by
  intro x x' hx a ha a' ha'
  simp only [toFDP, mem_filter, mem_univ, true_and] at ha ha' ⊢
  refine ⟨(hl (min_le_left a a')).trans ha, ?_⟩
  rw [hl.map_max]
  exact max_le (ha.trans (S.cash_monotone hl hy hx)) ha'

/-- **Saving rises with wealth and income**: the greatest optimal saving rule is optimal and
increasing in `(a, z)`. -/
theorem savings_monotone (hl : Monotone S.level) (hy : Monotone S.y) :
    S.toFDP.IsOptimal (gmax S.toFDP.Γ_nonempty (S.toFDP.Q S.toFDP.vstar)) ∧
      Monotone (gmax S.toFDP.Γ_nonempty (S.toFDP.Q S.toFDP.vstar)) :=
  S.toFDP.optimal_monotone (S.ascending hl hy)
    (S.toFDP.id_Q_of_actionKernel
      (increasingDifferences_concave S.u_concave (S.cash_monotone hl hy) hl)
      (fun _ _ _ => rfl) _)

/-- The next-state kernel is FOSD-increasing in the saving choice. -/
theorem K_monotone : MonotoneKernel S.K := by
  intro v hv a a' ha
  simp only [S.sum_mul_K]
  exact Finset.sum_le_sum fun z _ =>
    mul_le_mul_of_nonneg_right (hv (Prod.mk_le_mk.2 ⟨ha, le_rfl⟩)) (S.π_nonneg z)

/-- **The household's state follows a monotone Markov chain** under the greatest optimal saving
rule. -/
theorem chain_monotone (hl : Monotone S.level) (hy : Monotone S.y) :
    MonotoneKernel fun x x' =>
      S.toFDP.P x (gmax S.toFDP.Γ_nonempty (S.toFDP.Q S.toFDP.vstar) x) x' :=
  monotoneKernel_comp S.K_monotone (S.savings_monotone hl hy).2

end SavingsModel

end DPExtensions.MonotonePolicies

set_option linter.style.longLine false
#print axioms DPExtensions.MonotonePolicies.IncreasingDifferences
#print axioms DPExtensions.MonotonePolicies.StrictIncreasingDifferences
#print axioms DPExtensions.MonotonePolicies.Ascending
#print axioms DPExtensions.MonotonePolicies.IncreasingDifferences.add
#print axioms DPExtensions.MonotonePolicies.IncreasingDifferences.const_mul
#print axioms DPExtensions.MonotonePolicies.increasingDifferences_of_sep
#print axioms DPExtensions.MonotonePolicies.increasingDifferences_mul
#print axioms DPExtensions.MonotonePolicies.concave_increment
#print axioms DPExtensions.MonotonePolicies.increasingDifferences_concave
#print axioms DPExtensions.MonotonePolicies.argmaxSet
#print axioms DPExtensions.MonotonePolicies.mem_argmaxSet
#print axioms DPExtensions.MonotonePolicies.argmaxSet_nonempty
#print axioms DPExtensions.MonotonePolicies.argmax_strongSetOrder
#print axioms DPExtensions.MonotonePolicies.gmax
#print axioms DPExtensions.MonotonePolicies.lmax
#print axioms DPExtensions.MonotonePolicies.gmax_mem
#print axioms DPExtensions.MonotonePolicies.lmax_mem
#print axioms DPExtensions.MonotonePolicies.topkis_gmax
#print axioms DPExtensions.MonotonePolicies.topkis_lmax
#print axioms DPExtensions.MonotonePolicies.topkis_strict
#print axioms DPExtensions.MonotonePolicies.FDP
#print axioms DPExtensions.MonotonePolicies.FDP.mk
#print axioms DPExtensions.MonotonePolicies.FDP.Γ
#print axioms DPExtensions.MonotonePolicies.FDP.Γ_nonempty
#print axioms DPExtensions.MonotonePolicies.FDP.r
#print axioms DPExtensions.MonotonePolicies.FDP.β
#print axioms DPExtensions.MonotonePolicies.FDP.β_nonneg
#print axioms DPExtensions.MonotonePolicies.FDP.β_lt_one
#print axioms DPExtensions.MonotonePolicies.FDP.P
#print axioms DPExtensions.MonotonePolicies.FDP.P_nonneg
#print axioms DPExtensions.MonotonePolicies.FDP.P_sum
#print axioms DPExtensions.MonotonePolicies.MonotoneKernel
#print axioms DPExtensions.MonotonePolicies.FDP.Q
#print axioms DPExtensions.MonotonePolicies.FDP.T
#print axioms DPExtensions.MonotonePolicies.FDP.Tσ
#print axioms DPExtensions.MonotonePolicies.FDP.IsPolicy
#print axioms DPExtensions.MonotonePolicies.FDP.abs_sum_sub_le
#print axioms DPExtensions.MonotonePolicies.FDP.abs_Q_sub_le
#print axioms DPExtensions.MonotonePolicies.FDP.norm_T_sub_le
#print axioms DPExtensions.MonotonePolicies.FDP.norm_Tσ_sub_le
#print axioms DPExtensions.MonotonePolicies.FDP.contracting_T
#print axioms DPExtensions.MonotonePolicies.FDP.contracting_Tσ
#print axioms DPExtensions.MonotonePolicies.FDP.vstar
#print axioms DPExtensions.MonotonePolicies.FDP.vσ
#print axioms DPExtensions.MonotonePolicies.FDP.T_vstar
#print axioms DPExtensions.MonotonePolicies.FDP.Tσ_vσ
#print axioms DPExtensions.MonotonePolicies.FDP.Q_mono
#print axioms DPExtensions.MonotonePolicies.FDP.T_mono
#print axioms DPExtensions.MonotonePolicies.FDP.Tσ_le_T
#print axioms DPExtensions.MonotonePolicies.FDP.le_vstar_of_le_T
#print axioms DPExtensions.MonotonePolicies.FDP.vσ_le_vstar
#print axioms DPExtensions.MonotonePolicies.FDP.IsGreedy
#print axioms DPExtensions.MonotonePolicies.FDP.IsGreedy.isPolicy
#print axioms DPExtensions.MonotonePolicies.FDP.Tσ_eq_T_of_greedy
#print axioms DPExtensions.MonotonePolicies.FDP.vσ_eq_vstar_of_greedy
#print axioms DPExtensions.MonotonePolicies.FDP.IsOptimal
#print axioms DPExtensions.MonotonePolicies.FDP.greedy_optimal
#print axioms DPExtensions.MonotonePolicies.FDP.exists_greedy
#print axioms DPExtensions.MonotonePolicies.FDP.optimal_greedy
#print axioms DPExtensions.MonotonePolicies.FDP.optimal_monotone
#print axioms DPExtensions.MonotonePolicies.FDP.optimal_monotone_least
#print axioms DPExtensions.MonotonePolicies.FDP.optimal_le_of_strict
#print axioms DPExtensions.MonotonePolicies.FDP.id_Q_of_actionKernel
#print axioms DPExtensions.MonotonePolicies.FDP.id_Q_of_continuation
#print axioms DPExtensions.MonotonePolicies.FDP.vstar_monotone
#print axioms DPExtensions.MonotonePolicies.FDP.optimal_monotone_of_primitives
#print axioms DPExtensions.MonotonePolicies.monotoneKernel_comp
#print axioms DPExtensions.MonotonePolicies.SavingsModel
#print axioms DPExtensions.MonotonePolicies.SavingsModel.mk
#print axioms DPExtensions.MonotonePolicies.SavingsModel.level
#print axioms DPExtensions.MonotonePolicies.SavingsModel.R
#print axioms DPExtensions.MonotonePolicies.SavingsModel.R_nonneg
#print axioms DPExtensions.MonotonePolicies.SavingsModel.y
#print axioms DPExtensions.MonotonePolicies.SavingsModel.u
#print axioms DPExtensions.MonotonePolicies.SavingsModel.u_concave
#print axioms DPExtensions.MonotonePolicies.SavingsModel.β
#print axioms DPExtensions.MonotonePolicies.SavingsModel.β_nonneg
#print axioms DPExtensions.MonotonePolicies.SavingsModel.β_lt_one
#print axioms DPExtensions.MonotonePolicies.SavingsModel.π
#print axioms DPExtensions.MonotonePolicies.SavingsModel.π_nonneg
#print axioms DPExtensions.MonotonePolicies.SavingsModel.π_sum
#print axioms DPExtensions.MonotonePolicies.SavingsModel.a₀
#print axioms DPExtensions.MonotonePolicies.SavingsModel.a₀_feasible
#print axioms DPExtensions.MonotonePolicies.SavingsModel.cash
#print axioms DPExtensions.MonotonePolicies.SavingsModel.K
#print axioms DPExtensions.MonotonePolicies.SavingsModel.K_sum
#print axioms DPExtensions.MonotonePolicies.SavingsModel.toFDP
#print axioms DPExtensions.MonotonePolicies.SavingsModel.sum_mul_K
#print axioms DPExtensions.MonotonePolicies.SavingsModel.cash_monotone
#print axioms DPExtensions.MonotonePolicies.SavingsModel.ascending
#print axioms DPExtensions.MonotonePolicies.SavingsModel.savings_monotone
#print axioms DPExtensions.MonotonePolicies.SavingsModel.K_monotone
#print axioms DPExtensions.MonotonePolicies.SavingsModel.chain_monotone
