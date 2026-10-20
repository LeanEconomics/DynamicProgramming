/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectEnvelope

/-!
# Existence of the planner's value and policy, (1) and (8)

SLP §18.1, pp. 543 and 546. The planner's functional equation (1),
`v(k) = max_{0 ≤ y ≤ f(k)} {U[f(k) − y] + β v(y)}`, and that of the pseudo-economy (8) (the same
with discount factor `β̂ = (1 − θ)β`) are solved "by Chapter 4 methods" in the book. This module
carries out those methods for a generic discount factor `b ∈ [0, 1)` on `K = [0, k̄]`
(`PlannerHyp`: `U` continuous, nondecreasing and strictly concave on `[0, ∞)`; `f` continuous and
concave on `K` with `0 ≤ f ≤ k̄` there, so that `[0, f(k)] ⊆ K`).

* `plannerOp`, `plannerOp_contracting` (Theorem 4.6): the Bellman operator acts on the Banach
  space `ℝ →ᵇ ℝ` of bounded continuous functions and is a `b`-contraction. (A function on `ℝ`
  is used for convenience: `k` and `c` are clamped to `K`, and only values on `K` matter. The
  supremum over `y ∈ [0, f(k)]` is written as one over `s ∈ [0, 1]`, `y = s f(k)`, so that the
  Theorem of the Maximum reduces to `IsCompact.continuous_sSup`.)
* `plannerValue`, `plannerValue_solves`: its fixed point `v` is continuous and bounded and solves
  (1) on `K` (`SolvesPlanner`).
* `plannerValue_concave` (Theorem 4.8): `v` is concave on `K` (`T` preserves concavity, and the
  fixed point is the limit of `Tⁿ0`).
* `plannerPolicy`, `plannerPolicy_spec`, `plannerPolicy_unique` (Theorem 4.8): the maximum is
  attained at a unique `g(k) ∈ [0, f(k)]` (strict concavity of `U`), and
  `v(k) = U[f(k) − g(k)] + b v(g(k))`.
* `plannerPolicy_continuousOn` (Theorem 4.8, Theorem of the Maximum): `g` is continuous on `K`
  (its graph is closed and `K` is compact).
* `planner_envelope` (§18.1 (10), Theorem 4.11): at `k ∈ (0, k̄)` with `g(k) < f(k)`, `U`
  differentiable at `f(k) − g(k)` and `f` at `k`, `v′(k) = f′(k) U′[f(k) − g(k)]`.
* `planner_foc` (§18.1 (9)): at an interior choice `0 < g(k) < f(k)` with `v` differentiable at
  `g(k)`, `U′[f(k) − g(k)] = b v′(g(k))`.
* `planner_euler`: if `0 < g(k) < f(k)` and `g(g(k)) < f(g(k))`, the Euler equation
  `U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]` holds.

Interiority of the policy is a hypothesis, as in SLP Theorem 4.11. With `U` differentiable on
`[0, ∞)` (which the book's Assumption 18.1 requires), `U′(0)` is finite, so the usual Inada
argument for interiority is not available.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set BoundedContinuousFunction

/-- **Hypotheses for the planner's problem** (1)/(8) on `K = [0, k̄]` with discount factor `b`. -/
structure PlannerHyp (U f : ℝ → ℝ) (b kbar : ℝ) : Prop where
  b_nonneg : 0 ≤ b
  b_lt_one : b < 1
  kbar_nonneg : 0 ≤ kbar
  U_cont : ContinuousOn U (Ici 0)
  U_mono : MonotoneOn U (Ici 0)
  U_strictConcave : StrictConcaveOn ℝ (Ici 0) U
  f_cont : ContinuousOn f (Icc 0 kbar)
  f_concave : ConcaveOn ℝ (Icc 0 kbar) f
  f_nonneg : ∀ k ∈ Icc 0 kbar, 0 ≤ f k
  f_le : ∀ k ∈ Icc 0 kbar, f k ≤ kbar

/-- `v` solves the planner's functional equation (1) (discount factor `b`) on `K = [0, k̄]`. -/
def SolvesPlanner (U f : ℝ → ℝ) (b kbar : ℝ) (v : ℝ → ℝ) : Prop :=
  ∀ k ∈ Icc 0 kbar, v k = sSup ((fun y => U (f k - y) + b * v y) '' Icc 0 (f k))

/-- The nearest point of `[0, k̄]`. -/
noncomputable def clampK (kbar x : ℝ) : ℝ := max 0 (min kbar x)

/-- `clampK` maps into `[0, k̄]`. -/
theorem clampK_mem {kbar : ℝ} (h : 0 ≤ kbar) (x : ℝ) : clampK kbar x ∈ Icc 0 kbar :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- `clampK` is the identity on `[0, k̄]`. -/
theorem clampK_of_mem {kbar x : ℝ} (hx : x ∈ Icc 0 kbar) : clampK kbar x = x := by
  simp only [clampK, min_eq_right hx.2, max_eq_right hx.1]

/-- `clampK` is continuous. -/
theorem continuous_clampK (kbar : ℝ) : Continuous (clampK kbar) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- `U ∘ clampK` is continuous. -/
theorem PlannerHyp.continuous_U {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    Continuous fun c => U (clampK kbar c) :=
  (P.U_cont.mono Icc_subset_Ici_self).comp_continuous (continuous_clampK kbar)
    (clampK_mem P.kbar_nonneg)

/-- `f ∘ clampK` is continuous. -/
theorem PlannerHyp.continuous_f {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    Continuous fun k => f (clampK kbar k) :=
  P.f_cont.comp_continuous (continuous_clampK kbar) (clampK_mem P.kbar_nonneg)

/-- `U` is bounded on `[0, k̄]`. -/
theorem PlannerHyp.exists_bound {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ∃ C, 0 ≤ C ∧ ∀ c, |U (clampK kbar c)| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (P.U_cont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) kbar ⊆ Ici 0))
  refine ⟨max C 0, le_max_right _ _, fun c => ?_⟩
  have := hC _ (clampK_mem P.kbar_nonneg c)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- A bound for `|U|` on `[0, k̄]`. -/
noncomputable def PlannerHyp.UB {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) : ℝ :=
  Classical.choose P.exists_bound

/-- The bound `PlannerHyp.UB`. -/
theorem PlannerHyp.UB_spec {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    0 ≤ P.UB ∧ ∀ c, |U (clampK kbar c)| ≤ P.UB :=
  Classical.choose_spec P.exists_bound

/-- The maximand of (1), written with `y = s f(k)`, `s ∈ [0, 1]`, and clamped to `K`. -/
noncomputable def plannerG (U f : ℝ → ℝ) (b kbar : ℝ) (v : ℝ → ℝ) (k s : ℝ) : ℝ :=
  U (clampK kbar (f (clampK kbar k) - s * f (clampK kbar k))) + b * v (s * f (clampK kbar k))

/-- The maximand is jointly continuous for continuous `v`. -/
theorem PlannerHyp.continuous_plannerG {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hv : Continuous v) :
    Continuous fun p : ℝ × ℝ => plannerG U f b kbar v p.1 p.2 := by
  have hf : Continuous fun p : ℝ × ℝ => f (clampK kbar p.1) :=
    P.continuous_f.comp continuous_fst
  exact (P.continuous_U.comp (hf.sub (continuous_snd.mul hf))).add
    (continuous_const.mul (hv.comp (continuous_snd.mul hf)))

/-- The maximand is bounded by `UB + b ‖v‖`. -/
theorem PlannerHyp.abs_plannerG_le {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) (k s : ℝ) : |plannerG U f b kbar v k s| ≤ P.UB + b * ‖v‖ := by
  have h1 := P.UB_spec.2 (f (clampK kbar k) - s * f (clampK kbar k))
  have h2 : |v (s * f (clampK kbar k))| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact v.norm_coe_le_norm _
  have h3 := mul_le_mul_of_nonneg_left h2 P.b_nonneg
  calc |plannerG U f b kbar v k s|
      ≤ |U (clampK kbar (f (clampK kbar k) - s * f (clampK kbar k)))| +
          |b * v (s * f (clampK kbar k))| := abs_add_le _ _
    _ ≤ P.UB + b * ‖v‖ := by rw [abs_mul, abs_of_nonneg P.b_nonneg]; linarith

/-- The image of the maximand over `s ∈ [0, 1]` is bounded above. -/
theorem PlannerHyp.bddAbove_plannerG {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) (k : ℝ) : BddAbove (plannerG U f b kbar v k '' Icc 0 1) :=
  ⟨P.UB + b * ‖v‖, by rintro _ ⟨s, -, rfl⟩; exact (abs_le.1 (P.abs_plannerG_le v k s)).2⟩

/-- **The Bellman operator of (1)** on `ℝ →ᵇ ℝ`:
`(Tv)(k) = sup_{s ∈ [0, 1]} {U[f(k) − s f(k)] + b v(s f(k))}` (clamped to `K`). -/
noncomputable def plannerOp {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  ofNormedAddCommGroup (fun k => sSup (plannerG U f b kbar v k '' Icc 0 1))
    (isCompact_Icc.continuous_sSup (P.continuous_plannerG v.continuous)) (P.UB + b * ‖v‖)
    (fun k => by
      rw [Real.norm_eq_abs, abs_le]
      have hne : (plannerG U f b kbar v k '' Icc 0 1).Nonempty :=
        ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      constructor
      · exact (abs_le.1 (P.abs_plannerG_le v k 0)).1.trans
          (le_csSup (P.bddAbove_plannerG v k) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
      · exact csSup_le hne (by
          rintro _ ⟨s, -, rfl⟩
          exact (abs_le.1 (P.abs_plannerG_le v k s)).2))

/-- On `K`, the maximand over `s ∈ [0, 1]` has the same values as the maximand of (1) over
`y ∈ [0, f(k)]`. -/
theorem PlannerHyp.image_plannerG {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ → ℝ) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerG U f b kbar v k '' Icc 0 1 = (fun y => U (f k - y) + b * v y) '' Icc 0 (f k) := by
  have hf0 := P.f_nonneg k hk
  calc plannerG U f b kbar v k '' Icc 0 1
      = ((fun y => U (f k - y) + b * v y) ∘ fun s => s * f k) '' Icc 0 1 := by
        refine image_congr fun s hs => ?_
        have hc : f k - s * f k ∈ Icc 0 kbar := by
          constructor
          · nlinarith [hs.2]
          · nlinarith [hs.1, P.f_le k hk]
        simp only [plannerG, Function.comp, clampK_of_mem hk, clampK_of_mem hc]
    _ = (fun y => U (f k - y) + b * v y) '' ((fun s => s * f k) '' Icc 0 1) := image_comp _ _ _
    _ = (fun y => U (f k - y) + b * v y) '' Icc 0 (f k) := by
        rw [image_mul_right_Icc zero_le_one hf0, zero_mul, one_mul]

/-- On `K`, `(Tv)(k) = sup_{0 ≤ y ≤ f(k)} {U[f(k) − y] + b v(y)}`. -/
theorem PlannerHyp.plannerOp_apply {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerOp P v k = sSup ((fun y => U (f k - y) + b * v y) '' Icc 0 (f k)) := by
  rw [← P.image_plannerG v hk]
  rfl

/-- **`T` is a `b`-contraction** of `ℝ →ᵇ ℝ` (Theorem 4.6, with Blackwell's conditions replaced by
the direct estimate). -/
theorem PlannerHyp.plannerOp_contracting {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ContractingWith (Real.toNNReal b) (plannerOp P) := by
  refine ⟨Real.toNNReal_lt_one.2 P.b_lt_one, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  rw [Real.coe_toNNReal _ P.b_nonneg]
  have hD : 0 ≤ b * dist v w := mul_nonneg P.b_nonneg dist_nonneg
  have key : ∀ (v w : ℝ →ᵇ ℝ) (k : ℝ), plannerOp P v k ≤ plannerOp P w k + b * dist v w := by
    intro v w k
    have hne : (plannerG U f b kbar v k '' Icc 0 1).Nonempty :=
      ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    change sSup (plannerG U f b kbar v k '' Icc 0 1) ≤
      sSup (plannerG U f b kbar w k '' Icc 0 1) + b * dist v w
    refine csSup_le hne ?_
    rintro _ ⟨s, hs, rfl⟩
    have h1 := le_csSup (P.bddAbove_plannerG w k) ⟨s, hs, rfl⟩
    have h2 : v (s * f (clampK kbar k)) ≤ w (s * f (clampK kbar k)) + dist v w := by
      have := (abs_le.1 (Real.dist_eq _ _ ▸ dist_coe_le_dist (f := v) (g := w)
        (s * f (clampK kbar k)))).2
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 P.b_nonneg
    have e : plannerG U f b kbar v k s = plannerG U f b kbar w k s +
        b * (v (s * f (clampK kbar k)) - w (s * f (clampK kbar k))) := by
      simp only [plannerG]
      ring
    rw [e]
    linarith
  refine (dist_le hD).2 fun k => ?_
  rw [Real.dist_eq, abs_le]
  constructor
  · have := key w v k
    rw [dist_comm] at this
    linarith
  · have := key v w k
    linarith

/-- **The planner's value function**: the fixed point of `T`. -/
noncomputable def plannerValue {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ℝ →ᵇ ℝ :=
  ContractingWith.fixedPoint (plannerOp P) P.plannerOp_contracting

/-- `Tv = v` for the planner's value function. -/
theorem PlannerHyp.plannerValue_fixed {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    plannerOp P (plannerValue P) = plannerValue P :=
  ContractingWith.fixedPoint_isFixedPt (f := plannerOp P) P.plannerOp_contracting

/-- **Existence for (1)** (Theorem 4.6): the planner's value function is continuous and bounded
and solves the functional equation (1) on `K`. -/
theorem PlannerHyp.plannerValue_solves {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    SolvesPlanner U f b kbar (plannerValue P) := by
  intro k hk
  rw [← P.plannerOp_apply _ hk, P.plannerValue_fixed]

/-- The maximand of (1) is continuous on `[0, f(k)]`. -/
theorem PlannerHyp.continuousOn_maximand {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hv : Continuous v) (k : ℝ) :
    ContinuousOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) := by
  refine ContinuousOn.add ?_ (continuous_const.mul hv).continuousOn
  refine P.U_cont.comp (continuous_const.sub continuous_id).continuousOn fun y hy => ?_
  exact mem_Ici.2 (sub_nonneg.2 hy.2)

/-- **The maximum is attained** on `[0, f(k)]` and equals `(Tv)(k)`. -/
theorem PlannerHyp.exists_max {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (v : ℝ →ᵇ ℝ) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    ∃ y ∈ Icc 0 (f k), IsMaxOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) y ∧
      plannerOp P v k = U (f k - y) + b * v y := by
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, P.f_nonneg k hk⟩
    (P.continuousOn_maximand v.continuous k)
  refine ⟨y, hy, hmax, ?_⟩
  rw [P.plannerOp_apply v hk]
  exact IsGreatest.csSup_eq ⟨mem_image_of_mem _ hy, by rintro _ ⟨z, hz, rfl⟩; exact hmax hz⟩

/-- **`T` preserves concavity on `K`** (proof of Theorem 4.8). -/
theorem PlannerHyp.plannerOp_concave {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ →ᵇ ℝ} (hv : ConcaveOn ℝ (Icc 0 kbar) v) :
    ConcaveOn ℝ (Icc 0 kbar) (plannerOp P v) := by
  refine ⟨convex_Icc 0 kbar, fun k hk k' hk' a a' ha ha' haa => ?_⟩
  obtain ⟨y, hy, -, hTy⟩ := P.exists_max v hk
  obtain ⟨y', hy', -, hTy'⟩ := P.exists_max v hk'
  have hkθ : a • k + a' • k' ∈ Icc 0 kbar := (convex_Icc 0 kbar) hk hk' ha ha' haa
  have hfθ := P.f_concave.2 hk hk' ha ha' haa
  simp only [smul_eq_mul] at hfθ hkθ ⊢
  set kθ := a * k + a' * k' with hkθdef
  set yθ := a * y + a' * y' with hyθ
  have hyK : y ∈ Icc 0 kbar := ⟨hy.1, hy.2.trans (P.f_le k hk)⟩
  have hyK' : y' ∈ Icc 0 kbar := ⟨hy'.1, hy'.2.trans (P.f_le k' hk')⟩
  have hyθf : yθ ∈ Icc 0 (f kθ) := by
    constructor
    · have := hy.1
      have := hy'.1
      positivity
    · have h1 := mul_le_mul_of_nonneg_left hy.2 ha
      have h2 := mul_le_mul_of_nonneg_left hy'.2 ha'
      linarith
  have hc : 0 ≤ f k - y := by linarith [hy.2]
  have hc' : 0 ≤ f k' - y' := by linarith [hy'.2]
  have hcθ : a * (f k - y) + a' * (f k' - y') ≤ f kθ - yθ := by linarith
  have hcθ0 : 0 ≤ a * (f k - y) + a' * (f k' - y') := by positivity
  have hU1 : U (a * (f k - y) + a' * (f k' - y')) ≤ U (f kθ - yθ) :=
    P.U_mono (mem_Ici.2 hcθ0) (mem_Ici.2 (hcθ0.trans hcθ)) hcθ
  have hU2 := P.U_strictConcave.concaveOn.2 (mem_Ici.2 hc) (mem_Ici.2 hc') ha ha' haa
  have hv2 := hv.2 hyK hyK' ha ha' haa
  simp only [smul_eq_mul] at hU2 hv2
  have hv3 := mul_le_mul_of_nonneg_left hv2 P.b_nonneg
  have hle : U (f kθ - yθ) + b * v yθ ≤ plannerOp P v kθ := by
    rw [P.plannerOp_apply v hkθ]
    refine le_csSup ?_ ⟨yθ, hyθf, rfl⟩
    rw [← P.image_plannerG v hkθ]
    exact P.bddAbove_plannerG v kθ
  rw [hTy, hTy']
  nlinarith

/-- **The value function is concave on `K`** (Theorem 4.8). -/
theorem PlannerHyp.plannerValue_concave {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) :
    ConcaveOn ℝ (Icc 0 kbar) (plannerValue P) := by
  have hit : ∀ n : ℕ, ConcaveOn ℝ (Icc 0 kbar) ((plannerOp P)^[n] 0) := by
    intro n
    induction n with
    | zero => exact concaveOn_const 0 (convex_Icc 0 kbar)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact P.plannerOp_concave ih
  have hlim := P.plannerOp_contracting.tendsto_iterate_fixedPoint 0
  have hpt : ∀ x, Tendsto (fun n => ((plannerOp P)^[n] 0 : ℝ →ᵇ ℝ) x) atTop
      (𝓝 (plannerValue P x)) := fun x =>
    ((continuous_eval_const x).tendsto _).comp hlim
  refine ⟨convex_Icc 0 kbar, fun x hx y hy a a' ha ha' haa => ?_⟩
  exact le_of_tendsto_of_tendsto' (((hpt x).const_smul a).add ((hpt y).const_smul a'))
    (hpt (a • x + a' • y)) fun n => (hit n).2 hx hy ha ha' haa

/-- **Uniqueness of the maximiser** (Theorem 4.8): for `v` concave on `K`, two maximisers of
`U[f(k) − y] + b v(y)` on `[0, f(k)]` coincide (strict concavity of `U`). -/
theorem PlannerHyp.max_unique {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hv : ConcaveOn ℝ (Icc 0 kbar) v) {k : ℝ} (hk : k ∈ Icc 0 kbar) {y y' : ℝ}
    (hy : y ∈ Icc 0 (f k)) (hy' : y' ∈ Icc 0 (f k))
    (hmax : IsMaxOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) y)
    (hmax' : IsMaxOn (fun y => U (f k - y) + b * v y) (Icc 0 (f k)) y') : y = y' := by
  by_contra hne
  have hm : (1 / 2 : ℝ) * y + (1 / 2) * y' ∈ Icc 0 (f k) :=
    ⟨by linarith [hy.1, hy'.1], by linarith [hy.2, hy'.2]⟩
  have hc : 0 ≤ f k - y := by linarith [hy.2]
  have hc' : 0 ≤ f k - y' := by linarith [hy'.2]
  have hcne : f k - y ≠ f k - y' := fun h => hne (by linarith)
  have hU := P.U_strictConcave.2 (mem_Ici.2 hc) (mem_Ici.2 hc') hcne (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hyK : y ∈ Icc 0 kbar := ⟨hy.1, hy.2.trans (P.f_le k hk)⟩
  have hyK' : y' ∈ Icc 0 kbar := ⟨hy'.1, hy'.2.trans (P.f_le k hk)⟩
  have hv2 := hv.2 hyK hyK' (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at hU hv2
  have e : (1 / 2 : ℝ) * (f k - y) + 1 / 2 * (f k - y') = f k - (1 / 2 * y + 1 / 2 * y') := by
    ring
  rw [e] at hU
  have h1 : U (f k - y') + b * v y' ≤ U (f k - y) + b * v y := hmax hy'
  have h2 : U (f k - (1 / 2 * y + 1 / 2 * y')) + b * v (1 / 2 * y + 1 / 2 * y') ≤
      U (f k - y) + b * v y := hmax hm
  have h3 := mul_le_mul_of_nonneg_left hv2 P.b_nonneg
  have h4 : U (f k - y) + b * v y ≤ U (f k - y') + b * v y' := hmax' hy
  linarith

/-- **The planner's policy** `g(k)`: a maximiser in (1) (unique by `PlannerHyp.max_unique`). -/
noncomputable def plannerPolicy {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar) (k : ℝ) :
    ℝ :=
  Classical.epsilon fun y => y ∈ Icc 0 (f k) ∧
    IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) y

/-- **The policy attains the maximum in (1)**: for `k ∈ K`, `g(k) ∈ [0, f(k)]` maximises
`U[f(k) − y] + b v(y)` there, and `v(k) = U[f(k) − g(k)] + b v(g(k))`. -/
theorem PlannerHyp.plannerPolicy_spec {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerPolicy P k ∈ Icc 0 (f k) ∧
      IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) (plannerPolicy P k) ∧
      plannerValue P k = U (f k - plannerPolicy P k) + b * plannerValue P (plannerPolicy P k) := by
  obtain ⟨y, hy, hmax, -⟩ := P.exists_max (plannerValue P) hk
  have hspec : plannerPolicy P k ∈ Icc 0 (f k) ∧
      IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) (plannerPolicy P k) :=
    Classical.epsilon_spec (p := fun y => y ∈ Icc 0 (f k) ∧
      IsMaxOn (fun y => U (f k - y) + b * plannerValue P y) (Icc 0 (f k)) y) ⟨y, hy, hmax⟩
  refine ⟨hspec.1, hspec.2, ?_⟩
  obtain ⟨y₁, hy₁, hmax₁, hT⟩ := P.exists_max (plannerValue P) hk
  rw [P.plannerValue_fixed] at hT
  rw [hT, P.max_unique P.plannerValue_concave hk hy₁ hspec.1 hmax₁ hspec.2]

/-- **The policy is the unique maximiser** in (1): `y ∈ [0, f(k)]` attains the value `v(k)` iff
`y = g(k)`. -/
theorem PlannerHyp.plannerPolicy_unique {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) {y : ℝ} (hy : y ∈ Icc 0 (f k)) :
    U (f k - y) + b * plannerValue P y = plannerValue P k ↔ y = plannerPolicy P k := by
  obtain ⟨hg, hgmax, hgv⟩ := P.plannerPolicy_spec hk
  constructor
  · intro hyv
    refine P.max_unique P.plannerValue_concave hk hy hg (fun z hz => ?_) hgmax
    change U (f k - z) + b * plannerValue P z ≤ U (f k - y) + b * plannerValue P y
    rw [hyv, hgv]
    exact hgmax hz
  · rintro rfl
    exact hgv.symm

/-- The policy maps `K` into `K` with nonnegative consumption. -/
theorem PlannerHyp.plannerPolicy_mem {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    plannerPolicy P k ∈ Icc 0 kbar ∧ 0 ≤ f k - plannerPolicy P k := by
  have h := (P.plannerPolicy_spec hk).1
  exact ⟨⟨h.1, h.2.trans (P.f_le k hk)⟩, by linarith [h.2]⟩

/-- **The policy is continuous on `K`** (Theorem 4.8; Theorem of the Maximum for a
single-valued policy). The graph of `g` on `K × K` is
`{(k, y) : y ≤ f(k), U[f(k) − y] + b v(y) = v(k)}` (by uniqueness of the maximiser), which is
closed; a map into the compact space `K` with closed graph is continuous. -/
theorem PlannerHyp.plannerPolicy_continuousOn {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) : ContinuousOn (plannerPolicy P) (Icc 0 kbar) := by
  set gK : Icc 0 kbar → Icc 0 kbar := fun k => ⟨plannerPolicy P k, (P.plannerPolicy_mem k.2).1⟩
    with hgK
  have hfK : Continuous fun k : Icc 0 kbar => f k :=
    P.f_cont.comp_continuous continuous_subtype_val fun k => k.2
  set S : Set (Icc 0 kbar × Icc 0 kbar) := {p | (p.2 : ℝ) ≤ f p.1 ∧
    U (clampK kbar (f p.1 - p.2)) + b * plannerValue P p.2 = plannerValue P p.1} with hS
  have hSc : IsClosed S := by
    refine IsClosed.inter (isClosed_le (continuous_subtype_val.comp continuous_snd)
      (hfK.comp continuous_fst)) (isClosed_eq ?_ ?_)
    · exact (P.continuous_U.comp ((hfK.comp continuous_fst).sub
        (continuous_subtype_val.comp continuous_snd))).add (continuous_const.mul
        ((plannerValue P).continuous.comp (continuous_subtype_val.comp continuous_snd)))
    · exact (plannerValue P).continuous.comp (continuous_subtype_val.comp continuous_fst)
  have hgraph : Function.graph gK = S := by
    ext ⟨k, y⟩
    change gK k = y ↔ (y : ℝ) ≤ f k ∧
      U (clampK kbar (f k - y)) + b * plannerValue P y = plannerValue P k
    have hyc : ∀ hy : (y : ℝ) ≤ f k, clampK kbar (f k - y) = f k - y := fun hy =>
      clampK_of_mem ⟨by linarith, by linarith [y.2.1, P.f_le k k.2]⟩
    constructor
    · intro h
      have hy : (y : ℝ) = plannerPolicy P k := by rw [← h]
      obtain ⟨hg, -, hgv⟩ := P.plannerPolicy_spec k.2
      refine ⟨hy ▸ hg.2, ?_⟩
      rw [hyc (hy ▸ hg.2), hy, hgv]
    · rintro ⟨hy, hv⟩
      rw [hyc hy] at hv
      exact Subtype.ext ((P.plannerPolicy_unique k.2 ⟨y.2.1, hy⟩).1 hv).symm
  have hc : Continuous gK := continuous_of_isClosed_graph (hgraph ▸ hSc)
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hc

/-- **The envelope condition §18.1 (10)** (Benveniste–Scheinkman, Theorem 4.11). At
`k ∈ (0, k̄)` with positive consumption `f(k) − g(k) > 0`, `U` differentiable at `f(k) − g(k)`
and `f` differentiable at `k`, the planner's value function is differentiable at `k` with
`v′(k) = f′(k) U′[f(k) − g(k)]`. -/
theorem PlannerHyp.planner_envelope {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioo 0 kbar) (hc : plannerPolicy P k < f k)
    (hUd : DifferentiableAt ℝ U (f k - plannerPolicy P k)) (hfd : DifferentiableAt ℝ f k) :
    HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - plannerPolicy P k)) k := by
  have hkK : k ∈ Icc 0 kbar := Ioo_subset_Icc_self hk
  set y := plannerPolicy P k with hy
  obtain ⟨hyf, -, hv⟩ := P.plannerPolicy_spec hkK
  set Wf : ℝ → ℝ := fun z => U (f z - y) + b * plannerValue P y with hWf
  have hWd : HasDerivAt Wf (deriv f k * deriv U (f k - y)) k := by
    have := (hUd.hasDerivAt.comp k (hfd.hasDerivAt.sub_const y)).add_const
      (b * plannerValue P y)
    rw [mul_comm (deriv U _)] at this
    exact this
  have hle : ∀ᶠ z in 𝓝 k, Wf z ≤ plannerValue P z := by
    have hfc : ContinuousAt (fun z => f z - y) k := hfd.continuousAt.sub continuousAt_const
    filter_upwards [Ioo_mem_nhds hk.1 hk.2, hfc.eventually (Ioi_mem_nhds (sub_pos.2 hc))]
      with z hz hfz
    have hzK : z ∈ Icc 0 kbar := Ioo_subset_Icc_self hz
    have hyz : y ∈ Icc 0 (f z) := ⟨hyf.1, by have : 0 < f z - y := hfz; linarith⟩
    obtain ⟨y', hy', hmax, hT⟩ := P.exists_max (plannerValue P) hzK
    rw [P.plannerValue_fixed] at hT
    rw [hT]
    exact hmax hyz
  exact hasDerivAt_of_concave_of_le P.plannerValue_concave (Icc_mem_nhds hk.1 hk.2) hle hv.symm
    hWd

/-- **The first-order condition §18.1 (9).** At `k ∈ K` with an interior choice
`0 < g(k) < f(k)`, `U` differentiable at `f(k) − g(k)` and `v` differentiable at `g(k)`:
`U′[f(k) − g(k)] = b v′(g(k))`. -/
theorem PlannerHyp.planner_foc {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) (h0 : 0 < plannerPolicy P k) (h1 : plannerPolicy P k < f k)
    (hUd : DifferentiableAt ℝ U (f k - plannerPolicy P k))
    (hvd : DifferentiableAt ℝ (plannerValue P) (plannerPolicy P k)) :
    deriv U (f k - plannerPolicy P k) = b * deriv (plannerValue P) (plannerPolicy P k) := by
  set y := plannerPolicy P k with hy
  obtain ⟨-, hmax, -⟩ := P.plannerPolicy_spec hk
  have hloc : IsLocalMax (fun z => U (f k - z) + b * plannerValue P z) y := by
    filter_upwards [Ioo_mem_nhds h0 h1] with z hz
    exact hmax ⟨hz.1.le, hz.2.le⟩
  have hd1 : HasDerivAt (fun z => U (f k - z)) (deriv U (f k - y) * -1) y :=
    hUd.hasDerivAt.comp y ((hasDerivAt_id y).const_sub (f k))
  have hd := hd1.add (hvd.hasDerivAt.const_mul b)
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **The planner's Euler equation**, from (9) and (10). Let `k ∈ K` with an interior choice
`0 < g(k) < f(k)` and positive consumption next period, `g(g(k)) < f(g(k))`; let `U` be
differentiable at both consumptions and `f` at `g(k)`. Then
`U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]`. -/
theorem PlannerHyp.planner_euler {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) (h0 : 0 < plannerPolicy P k) (h1 : plannerPolicy P k < f k)
    (h2 : plannerPolicy P (plannerPolicy P k) < f (plannerPolicy P k))
    (hUd1 : DifferentiableAt ℝ U (f k - plannerPolicy P k))
    (hUd2 : DifferentiableAt ℝ U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)))
    (hfd : DifferentiableAt ℝ f (plannerPolicy P k)) :
    deriv U (f k - plannerPolicy P k) = b * deriv f (plannerPolicy P k) *
      deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)) := by
  have hgI : plannerPolicy P k ∈ Ioo 0 kbar := ⟨h0, h1.trans_le (P.f_le k hk)⟩
  have henv := P.planner_envelope hgI h2 hUd2 hfd
  rw [P.planner_foc hk h0 h1 hUd1 henv.differentiableAt, henv.deriv]
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions
