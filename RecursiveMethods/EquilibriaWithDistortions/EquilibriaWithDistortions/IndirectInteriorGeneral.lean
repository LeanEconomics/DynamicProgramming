/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectInteriorExample

/-!
# Interiority on all of `K`, and uniqueness of the bounded solution of (1) and (8)

SLP §18.1, pp. 543–546. `IndirectInterior` proves the constructed planner's policy interior on
`(0, k̄]` when `U′(0+) = ∞` and `f(0) = 0`. Here the two other cases are treated, `f(0) > 0`
with `U′(0+) = ∞`, and `U′(0)` finite, with interiority on all of `K = [0, k̄]`; and the bounded
solution of (1) and (8) is shown to be unique.

**Uniqueness of the bounded solution of (1) and (8)** (pp. 543, 546).

* `PlannerHyp.solvesPlanner_unique`: every `v` bounded on `K` solving (1) on `K` (any discount
  factor `b ∈ [0, 1)`) equals `plannerValue` on `K`; no continuity is assumed.
  `PlannerHyp.solvesPseudoPlanner_unique` is the case of (8), `b = (1 − θ)β`.
  `PlannerHyp.solvesPlanner_policy`: every such `v` has the constructed policy as its unique
  maximiser.
* `PlannerHyp.plannerOp_fixedPoint_unique`: the fixed point of `plannerOp` in `ℝ →ᵇ ℝ` is unique
  (Banach). `PlannerHyp.solvesPlanner_not_unique_off_K`: a solution of (1) is determined only on
  `K`, since (1) at `k ∈ K` uses `v` only on `[0, f(k)] ⊆ K`.

**Positive saving** (`g > 0`).

* `PlannerHyp.plannerPolicy_pos_of_slope`: if `f(0) > 0`, `f` is nondecreasing on `K`,
  `f(y) ≥ f(0) + m y` for small `y > 0` with `b m > 1` (e.g. `b f′(0) > 1`, or `f′(0+) = ∞`;
  `eventually_add_mul_le_of_hasDerivAt`), `U` is differentiable on `(0, ∞)`, and consumption at
  `k = 0` is positive, then `g > 0` on all of `K`.
* `PlannerHyp.plannerPolicy_eq_zero_of_const`: with a constant technology, `g ≡ 0` on `K`.

**Positive consumption** (`g < f`) with a finite `U′(0)`.

* `PlannerHyp.U_sub_le_of_hasDerivWithinAt`: a finite right derivative `μ = U′(0)` is a
  Lipschitz constant of `U` on `[0, ∞)`.
* `PlannerHyp.plannerOp_lipschitz`, `PlannerHyp.plannerValue_lipschitz`: if `f` is `φ`-Lipschitz
  on `R = [r, k̄]` with `f(R) ⊆ [r, ∞)` and `b φ ≤ 1`, then `v` is `μ φ`-Lipschitz on `R`.
* `PlannerHyp.plannerPolicy_lt_of_lipschitz`: if moreover `b φ < 1` and `r < f` on `K`, then
  `g < f` on `K`. This is the condition `U′(0) > b · Lip(v|_R)` with the explicit bound
  `Lip(v|_R) ≤ U′(0) φ` from the Bellman equation.

**Interiority on all of `K`.**

* `PosOutputInadaHyp`, `PosOutputInadaHyp.policy_interior`: `f(0) > 0`, `U′(0+) = ∞` and the slope
  condition give `0 < g < f` on `K`, including `k = 0`.
* `FiniteMarginalHyp`, `FiniteMarginalHyp.policy_interior`: `U′(0) ∈ (0, ∞)`, the slope condition
  and the Lipschitz condition give `0 < g < f` on `K`.

**Exercise 18.1 and the equilibrium on all of `K`** (pp. 543–546).

* `PlannerHyp.planner_euler_on_K`, `PlannerHyp.planner_tvc_on_K`: for a policy interior on `K`,
  the Euler equation holds on `K` and the transversality condition `β′ᵗ a f′(k_t) U′(c_t) k_t → 0`
  holds from every `k ∈ K`, including `k = 0`: consumption is continuous and positive on the
  compact `K`, hence bounded below, so `U′(c_t)` is bounded even if `U′(0+) = ∞`.
* `ex_18_1_on_K`, `indirect_equilibrium_on_K`: Exercise 18.1 and the recursive competitive
  equilibrium of the taxed economy on all of `K`, with uniqueness of the bounded solution of (1),
  resp. (8), for a policy interior on `K`, `U` differentiable on `(0, ∞)` only, and no continuity
  of `U′` or `f′`. Applied in `PosOutputInadaHyp.ex_18_1`,
  `PosOutputInadaHyp.indirect_equilibrium`, `FiniteMarginalHyp.ex_18_1`,
  `FiniteMarginalHyp.indirect_equilibrium`.

**Correction.** `f(0) > 0` together with `U′(0+) = ∞` does not give interiority: with a constant
technology the planner never saves (`PlannerHyp.plannerPolicy_eq_zero_of_const`,
`inada_const_counterexample`). The slope condition `b m > 1` at `0` is added. With a finite
`U′(0)`, corners of both kinds occur without the added conditions: `g ≡ 0`
(`finite_const_counterexample`) and `g = f` on `[0, 1/1000]` in an economy satisfying everything
but the Lipschitz condition (`corner_counterexample`). Economies satisfying `PosOutputInadaHyp`
and `FiniteMarginalHyp` are in `IndirectInteriorGeneralExample`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set BoundedContinuousFunction

/-! ### Uniqueness of the bounded solution of (1) and (8) -/

/-- **The contraction estimate on `K`.** If `v` and `w` are bounded on `K = [0, k̄]` and
`v ≤ w + D` on `K`, then on `K` the right side of (1) for `v` is at most that for `w` plus
`b D`. Only values on `[0, f(k)] ⊆ K` enter. -/
theorem PlannerHyp.sSup_le_sSup_add {U f : ℝ → ℝ} {b kbar M D : ℝ} (P : PlannerHyp U f b kbar)
    {v w : ℝ → ℝ} (hwb : ∀ y ∈ Icc 0 kbar, |w y| ≤ M) (hD : ∀ y ∈ Icc 0 kbar, v y ≤ w y + D)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    sSup ((fun y => U (f k - y) + b * v y) '' Icc 0 (f k)) ≤
      sSup ((fun y => U (f k - y) + b * w y) '' Icc 0 (f k)) + b * D := by
  have hf0 := P.f_nonneg k hk
  have hne : ((fun y => U (f k - y) + b * v y) '' Icc 0 (f k)).Nonempty :=
    ⟨_, 0, ⟨le_rfl, hf0⟩, rfl⟩
  have hbdd : BddAbove ((fun y => U (f k - y) + b * w y) '' Icc 0 (f k)) := by
    refine ⟨U (f k) + b * M, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hU : U (f k - y) ≤ U (f k) :=
      P.U_mono (mem_Ici.2 (by linarith [hy.2])) (mem_Ici.2 hf0) (by linarith [hy.1])
    have hw := mul_le_mul_of_nonneg_left
      (abs_le.1 (hwb y ⟨hy.1, hy.2.trans (P.f_le k hk)⟩)).2 P.b_nonneg
    simp only
    linarith
  refine csSup_le hne ?_
  rintro _ ⟨y, hy, rfl⟩
  have h1 := le_csSup hbdd ⟨y, hy, rfl⟩
  have h2 := mul_le_mul_of_nonneg_left (hD y ⟨hy.1, hy.2.trans (P.f_le k hk)⟩) P.b_nonneg
  simp only at h1 ⊢
  linarith

/-- **Uniqueness of the bounded solution of (1)** (Theorem 4.6, on `K`). Every function `v`
bounded on `K = [0, k̄]` that solves the planner's functional equation (1) on `K` (with any
discount factor `b ∈ [0, 1)`, so also (8) with `b = (1 − θ)β`) equals the constructed
`plannerValue` on `K`. No continuity of `v` is assumed. The proof is the contraction estimate
`|v − w| ≤ b sup_K |v − w|`, iterated, on `K` itself: a fixed point of `plannerOp` on `ℝ →ᵇ ℝ`
is unique there (`PlannerHyp.plannerOp_fixedPoint_unique`), but a solution of (1) is only a
function on `K` (`PlannerHyp.solvesPlanner_not_unique_off_K`). -/
theorem PlannerHyp.solvesPlanner_unique {U f : ℝ → ℝ} {b kbar M : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hvb : ∀ k ∈ Icc 0 kbar, |v k| ≤ M) (hv : SolvesPlanner U f b kbar v) :
    ∀ k ∈ Icc 0 kbar, v k = plannerValue P k := by
  set w : ℝ → ℝ := ⇑(plannerValue P) with hwdef
  have hw : SolvesPlanner U f b kbar w := P.plannerValue_solves
  have hwb : ∀ k ∈ Icc 0 kbar, |w k| ≤ ‖plannerValue P‖ := fun k _ => by
    rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
  set D₀ := M + ‖plannerValue P‖ with hD₀
  have hit : ∀ n : ℕ, ∀ k ∈ Icc 0 kbar, |v k - w k| ≤ b ^ n * D₀ := by
    intro n
    induction n with
    | zero =>
      intro k hk
      have h1 := abs_sub (v k) (w k)
      have := hvb k hk
      have := hwb k hk
      simp only [pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro k hk
      have h1 := P.sSup_le_sSup_add (v := v) (w := w) (D := b ^ n * D₀) hwb
        (fun y hy => by linarith [(abs_le.1 (ih y hy)).2]) hk
      have h2 := P.sSup_le_sSup_add (v := w) (w := v) (D := b ^ n * D₀) hvb
        (fun y hy => by linarith [(abs_le.1 (ih y hy)).1]) hk
      rw [← hv k hk, ← hw k hk] at h1
      rw [← hv k hk, ← hw k hk] at h2
      rw [abs_le, pow_succ]
      constructor <;> nlinarith
  intro k hk
  have hlim : Tendsto (fun n : ℕ => b ^ n * D₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one P.b_nonneg P.b_lt_one).mul_const D₀
  have h0 : |v k - w k| ≤ 0 := ge_of_tendsto' hlim fun n => hit n k hk
  have := abs_nonpos_iff.1 h0
  linarith

/-- **Uniqueness of the bounded solution of (8)**, the pseudo-planner's functional equation
with discount factor `β̂ = (1 − θ)β` (p. 546): the case `b = (1 − θ)β` of
`PlannerHyp.solvesPlanner_unique`. -/
theorem PlannerHyp.solvesPseudoPlanner_unique {U f : ℝ → ℝ} {β θ kbar M : ℝ}
    (P : PlannerHyp U f ((1 - θ) * β) kbar) {w : ℝ → ℝ} (hwb : ∀ k ∈ Icc 0 kbar, |w k| ≤ M)
    (hw : SolvesPlanner U f ((1 - θ) * β) kbar w) :
    ∀ k ∈ Icc 0 kbar, w k = plannerValue P k :=
  P.solvesPlanner_unique hwb hw

/-- **The bounded continuous solution on `ℝ`** of the operator form of (1): every fixed point of
`plannerOp` in `ℝ →ᵇ ℝ` is `plannerValue` (Banach's fixed-point theorem). -/
theorem PlannerHyp.plannerOp_fixedPoint_unique {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) {w : ℝ →ᵇ ℝ} (hw : plannerOp P w = w) : w = plannerValue P :=
  ContractingWith.fixedPoint_unique (f := plannerOp P) P.plannerOp_contracting hw

/-- **A bounded solution of (1) is unique only on `K`.** Changing `plannerValue` off `K` keeps a
bounded solution of (1) on `K`, since (1) at `k ∈ K` evaluates `v` only on `[0, f(k)] ⊆ K`. -/
theorem PlannerHyp.solvesPlanner_not_unique_off_K {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) :
    ∃ v : ℝ → ℝ, (∀ k, |v k| ≤ ‖plannerValue P‖ + 1) ∧ SolvesPlanner U f b kbar v ∧
      ∀ k ∉ Icc 0 kbar, v k ≠ plannerValue P k := by
  classical
  refine ⟨fun x => if x ∈ Icc 0 kbar then plannerValue P x else plannerValue P x + 1,
    fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have h := (plannerValue P).norm_coe_le_norm k
    rw [Real.norm_eq_abs] at h
    dsimp only
    split_ifs
    · linarith
    · have := abs_add_le (plannerValue P k) 1
      rw [abs_one] at this
      linarith
  · simp only [hk, ite_true]
    rw [P.plannerValue_solves k hk]
    refine congrArg sSup (image_congr fun y hy => ?_)
    have hyK : y ∈ Icc 0 kbar := ⟨hy.1, hy.2.trans (P.f_le k hk)⟩
    simp only [hyK, ite_true]
  · simp only [hk, ite_false]
    linarith

/-- **Every bounded solution of (1) has the constructed policy.** If `v` is bounded on `K` and
solves (1) there, then at `k ∈ K` a choice `y ∈ [0, f(k)]` attains `v(k)` iff `y = g(k)`. -/
theorem PlannerHyp.solvesPlanner_policy {U f : ℝ → ℝ} {b kbar M : ℝ} (P : PlannerHyp U f b kbar)
    {v : ℝ → ℝ} (hvb : ∀ k ∈ Icc 0 kbar, |v k| ≤ M) (hv : SolvesPlanner U f b kbar v)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) {y : ℝ} (hy : y ∈ Icc 0 (f k)) :
    U (f k - y) + b * v y = v k ↔ y = plannerPolicy P k := by
  have hyK : y ∈ Icc 0 kbar := ⟨hy.1, hy.2.trans (P.f_le k hk)⟩
  rw [P.solvesPlanner_unique hvb hv y hyK, P.solvesPlanner_unique hvb hv k hk]
  exact P.plannerPolicy_unique hk hy

/-! ### Auxiliary facts, and positive saving when `f(0) > 0` -/

/-- **A finite `U′(0)` is a Lipschitz constant.** Under `PlannerHyp`, if `U` has right
derivative `μ` at `0`, then `U(c) − U(c′) ≤ μ (c − c′)` for `0 ≤ c′ ≤ c` (concavity: secant
slopes decrease, and those from `0` tend to `μ`). -/
theorem PlannerHyp.U_sub_le_of_hasDerivWithinAt {U f : ℝ → ℝ} {b kbar μ : ℝ}
    (P : PlannerHyp U f b kbar) (hμ : HasDerivWithinAt U μ (Ici 0) 0) {c c' : ℝ} (hc' : 0 ≤ c')
    (hcc : c' ≤ c) : U c - U c' ≤ μ * (c - c') := by
  have hcv := P.U_strictConcave.concaveOn
  rcases eq_or_lt_of_le hcc with rfl | hlt
  · simp
  have h0 : ∀ s, 0 < s → U s - U 0 ≤ μ * s := by
    intro s hs
    have := hcv.slope_le_of_hasDerivWithinAt (mem_Ici.2 le_rfl) (mem_Ici.2 hs.le) hs hμ
    rw [slope_def_field, sub_zero, div_le_iff₀ hs] at this
    linarith
  rcases eq_or_lt_of_le hc' with rfl | hpos
  · simpa using h0 c hlt
  · have h1 := hcv.slope_anti_adjacent (mem_Ici.2 le_rfl) (mem_Ici.2 (hpos.trans hlt).le) hpos
      hlt
    have h2 : (U c' - U 0) / (c' - 0) ≤ μ := by
      rw [sub_zero, div_le_iff₀ hpos]; linarith [h0 c' hpos]
    have h3 := h1.trans h2
    rw [div_le_iff₀ (sub_pos.2 hlt)] at h3
    linarith

/-- Under `PlannerHyp`, `U′(c) > 0` wherever `U` is differentiable at `c ≥ 0` (strict concavity
and monotonicity). -/
theorem PlannerHyp.deriv_U_pos_of_differentiableAt {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) {c : ℝ} (hc : 0 ≤ c) (hUd : DifferentiableAt ℝ U c) :
    0 < deriv U c := by
  have h := P.U_strictConcave.slope_lt_deriv (mem_Ici.2 hc) (mem_Ici.2 (by linarith : 0 ≤ c + 1))
    (by linarith) hUd
  rw [slope_def_field] at h
  have hm := P.U_mono (mem_Ici.2 hc) (mem_Ici.2 (by linarith)) (by linarith : c ≤ c + 1)
  have e : c + 1 - c = 1 := by ring
  rw [e, div_one] at h
  linarith

/-- Under `PlannerHyp`, `U′` is nonincreasing on `(0, ∞)` where `U` is differentiable. -/
theorem PlannerHyp.deriv_U_anti {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    deriv U d ≤ deriv U c :=
  (P.U_strictConcave.concaveOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
    (fun x hx => hUd x hx) (mem_Ioi.2 hc) (mem_Ioi.2 (hc.trans_le hcd)) hcd

/-- **A lower slope at `0` from a derivative**: if `f′(0) = d > m`, then `f(0) + m y ≤ f(y)` for
all small `y > 0`. -/
theorem eventually_add_mul_le_of_hasDerivAt {f : ℝ → ℝ} {d m : ℝ} (hf : HasDerivAt f d 0)
    (hm : m < d) : ∀ᶠ y in 𝓝[>] 0, f 0 + m * y ≤ f y := by
  have hev := hf.tendsto_slope_zero_right.eventually (lt_mem_nhds hm)
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hy0
  simp only [smul_eq_mul, zero_add] at hy
  rw [mem_Ioi] at hy0
  have h2 := mul_lt_mul_of_pos_right hy hy0
  rw [inv_mul_eq_div, div_mul_cancel₀ _ hy0.ne'] at h2
  linarith

/-- `y ↦ m y` maps `𝓝[>] 0` into itself for `m > 0`. -/
theorem tendsto_const_mul_nhdsGT_zero {m : ℝ} (hm : 0 < m) :
    Tendsto (fun y : ℝ => m * y) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun y : ℝ => m * y) (𝓝 0) (𝓝 (m * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy using mul_pos hm hy

/-- `y ↦ −y` maps `𝓝[>] 0` into `𝓝[<] 0`. -/
theorem tendsto_neg_nhdsGT_zero' : Tendsto (fun y : ℝ => -y) (𝓝[>] 0) (𝓝[<] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun y : ℝ => -y) (𝓝 0) (𝓝 (-0)) := continuous_neg.tendsto 0
    rw [neg_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy using neg_lt_zero.2 (mem_Ioi.1 hy)

/-- **Positive saving when `f(0) > 0`.** Under `PlannerHyp` with `b > 0`, let `U` be
differentiable on `(0, ∞)`, `f` nondecreasing on `K`, and let `f` rise at `0` faster than `1/b`:
`f(y) ≥ f(0) + m y` for small `y > 0`, with `b m > 1` (e.g. `b f′(0) > 1`, or `f′(0+) = ∞`).
If consumption at `k = 0` is positive, `g(0) < f(0)`, then `g(k) > 0` on all of `K`.
(Saving `y` at `k` instead of `0` costs `U(f(k)) − U(f(k) − y) ≈ U′(f(k)) y`; it gains at least
`b [U(c₀ + m y) − U(c₀)] ≈ b m U′(c₀) y`, with `c₀ = f(0) − g(0) ≤ f(k)` the consumption at `0`,
by repeating at `y` the choice made at `0`. Since `U′(f(k)) ≤ U′(c₀) < b m U′(c₀)`, saving
nothing is not optimal.) -/
theorem PlannerHyp.plannerPolicy_pos_of_slope {U f : ℝ → ℝ} {b kbar m : ℝ}
    (P : PlannerHyp U f b kbar) (hb : 0 < b) (hm : 1 < b * m)
    (hfm : ∀ᶠ y in 𝓝[>] 0, f 0 + m * y ≤ f y) (hfmono : MonotoneOn f (Icc 0 kbar))
    (hc0 : plannerPolicy P 0 < f 0) (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) : 0 < plannerPolicy P k := by
  set g := plannerPolicy P with hgdef
  set v : ℝ → ℝ := ⇑(plannerValue P) with hvdef
  have h0K : (0 : ℝ) ∈ Icc 0 kbar := ⟨le_rfl, P.kbar_nonneg⟩
  set z := g 0 with hz
  set c₀ := f 0 - z with hc₀
  have hc₀0 : 0 < c₀ := sub_pos.2 hc0
  obtain ⟨hz0, -, hv0⟩ := P.plannerPolicy_spec h0K
  have hf0k : f 0 ≤ f k := hfmono h0K hk hk.1
  have hfk : 0 < f k := by linarith [hz0.1]
  have hm0 : 0 < m := by
    by_contra h
    push Not at h
    nlinarith [P.b_lt_one]
  -- the gain: repeat at `y` the choice made at `0`
  have hgain : ∀ y ∈ Icc 0 kbar, U (f y - z) - U c₀ ≤ v y - v 0 := by
    intro y hy
    obtain ⟨-, hmy, -⟩ := P.plannerPolicy_spec hy
    obtain ⟨-, -, hvy⟩ := P.plannerPolicy_spec hy
    have hzy : z ∈ Icc 0 (f y) := ⟨hz0.1, hz0.2.trans (hfmono h0K hy hy.1)⟩
    have h1 := isMaxOn_iff.1 hmy z hzy
    change U (f y - z) + b * v z ≤ U (f y - g y) + b * v (g y) at h1
    change v y = U (f y - g y) + b * v (g y) at hvy
    change v 0 = U (f 0 - z) + b * v z at hv0
    rw [hc₀]
    linarith
  by_contra hle
  push Not at hle
  have hgk : g k = 0 := le_antisymm hle (P.plannerPolicy_spec hk).1.1
  obtain ⟨-, hmax, -⟩ := P.plannerPolicy_spec hk
  -- the eventual inequality between difference quotients
  have hev : ∀ᶠ y in 𝓝[>] 0, b * m * ((m * y)⁻¹ * (U (c₀ + m * y) - U c₀)) ≤
      (-y)⁻¹ * (U (f k + -y) - U (f k)) := by
    filter_upwards [hfm, Ioo_mem_nhdsGT hfk] with y hfy hy
    have hyK : y ∈ Icc 0 kbar := ⟨hy.1.le, hy.2.le.trans (P.f_le k hk)⟩
    have hopt := isMaxOn_iff.1 hmax y ⟨hy.1.le, hy.2.le⟩
    change U (f k - y) + b * v y ≤ U (f k - g k) + b * v (g k) at hopt
    rw [hgk, sub_zero] at hopt
    have h1 := hgain y hyK
    have h2 : U (c₀ + m * y) ≤ U (f y - z) :=
      P.U_mono (mem_Ici.2 (by have := mul_pos hm0 hy.1; linarith))
        (mem_Ici.2 (by have := mul_pos hm0 hy.1; linarith)) (by rw [hc₀]; linarith)
    have h3 : b * (U (c₀ + m * y) - U c₀) ≤ U (f k) - U (f k - y) := by
      have := mul_le_mul_of_nonneg_left (show U (c₀ + m * y) - U c₀ ≤ v y - v 0 by linarith)
        hb.le
      linarith
    have e1 : b * m * ((m * y)⁻¹ * (U (c₀ + m * y) - U c₀)) =
        (b * (U (c₀ + m * y) - U c₀)) / y := by
      field_simp
    have e2 : (-y)⁻¹ * (U (f k + -y) - U (f k)) = (U (f k) - U (f k - y)) / y := by
      rw [inv_neg, ← sub_eq_add_neg, div_eq_inv_mul]
      ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right h3 hy.1.le
  have hL : Tendsto (fun y => b * m * ((m * y)⁻¹ * (U (c₀ + m * y) - U c₀))) (𝓝[>] 0)
      (𝓝 (b * m * deriv U c₀)) := by
    refine Tendsto.congr (fun y => ?_) (((hUd c₀ hc₀0).hasDerivAt.tendsto_slope_zero_right.comp
      (tendsto_const_mul_nhdsGT_zero hm0)).const_mul (b * m))
    simp only [Function.comp, smul_eq_mul]
  have hR : Tendsto (fun y => (-y)⁻¹ * (U (f k + -y) - U (f k))) (𝓝[>] 0)
      (𝓝 (deriv U (f k))) := by
    refine Tendsto.congr (fun y => ?_) ((hUd (f k) hfk).hasDerivAt.tendsto_slope_zero_left.comp
      tendsto_neg_nhdsGT_zero')
    simp only [Function.comp, smul_eq_mul]
  have hlim := le_of_tendsto_of_tendsto hL hR hev
  have hanti := P.deriv_U_anti hUd hc₀0 (show c₀ ≤ f k by rw [hc₀]; linarith [hz0.1])
  have hd := P.deriv_U_pos_of_differentiableAt hc₀0.le (hUd c₀ hc₀0)
  have := mul_lt_mul_of_pos_right hm hd
  linarith

/-! ### Positive consumption when marginal utility at zero is finite -/

/-- The right side of (1) at `k ∈ K` is at least the value of any feasible choice. -/
theorem PlannerHyp.le_plannerOp {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (w : ℝ →ᵇ ℝ) {k : ℝ} (hk : k ∈ Icc 0 kbar) {y : ℝ} (hy : y ∈ Icc 0 (f k)) :
    U (f k - y) + b * w y ≤ plannerOp P w k := by
  rw [P.plannerOp_apply w hk]
  refine le_csSup ?_ ⟨y, hy, rfl⟩
  rw [← P.image_plannerG w hk]
  exact P.bddAbove_plannerG w k

/-- **`T` preserves a Lipschitz bound on `R = [r, k̄]`.** Let `U(c) − U(c′) ≤ μ (c − c′)` for
`0 ≤ c′ ≤ c`, let `f` be `φ`-Lipschitz on `R` with `f(R) ⊆ [r, ∞)`, and `b φ ≤ 1`. If
`w(k) − w(k′) ≤ μ φ |k − k′|` on `R`, the same holds for `Tw`. (At `k` take the maximiser `y`; at
`k′` take `y` if feasible, else save all of `f(k′)`; in the second case the loss is split
between consumption, at rate `μ`, and saving, at rate `b μ φ ≤ μ`.) -/
theorem PlannerHyp.plannerOp_lipschitz {U f : ℝ → ℝ} {b kbar μ φ r : ℝ}
    (P : PlannerHyp U f b kbar) (hμ0 : 0 ≤ μ)
    (hUL : ∀ c c', 0 ≤ c' → c' ≤ c → U c - U c' ≤ μ * (c - c'))
    (hφ0 : 0 ≤ φ) (hbφ : b * φ ≤ 1) (hr0 : 0 ≤ r) (hfr : ∀ k ∈ Icc r kbar, r ≤ f k)
    (hfL : ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar, |f k - f k'| ≤ φ * |k - k'|)
    {w : ℝ →ᵇ ℝ} (hw : ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar, w k - w k' ≤ μ * φ * |k - k'|) :
    ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar,
      plannerOp P w k - plannerOp P w k' ≤ μ * φ * |k - k'| := by
  intro k hk k' hk'
  have hkK : k ∈ Icc 0 kbar := ⟨hr0.trans hk.1, hk.2⟩
  have hkK' : k' ∈ Icc 0 kbar := ⟨hr0.trans hk'.1, hk'.2⟩
  obtain ⟨y, hy, -, hTy⟩ := P.exists_max w hkK
  have hfLk := hfL k hk k' hk'
  have hμf : μ * |f k - f k'| ≤ μ * φ * |k - k'| := by
    have := mul_le_mul_of_nonneg_left hfLk hμ0
    linarith
  rw [hTy]
  rcases le_or_gt y (f k') with hyk | hyk
  · have h1 := P.le_plannerOp w hkK' ⟨hy.1, hyk⟩
    rcases le_or_gt (f k') (f k) with hff | hff
    · have h2 := hUL (f k - y) (f k' - y) (by linarith) (by linarith)
      have h3 : μ * (f k - y - (f k' - y)) ≤ μ * |f k - f k'| := by
        rw [abs_of_nonneg (by linarith)]
        exact le_of_eq (by ring)
      linarith
    · have h2 : U (f k - y) ≤ U (f k' - y) :=
        P.U_mono (mem_Ici.2 (by linarith [hy.2])) (mem_Ici.2 (by linarith)) (by linarith)
      have := mul_nonneg (mul_nonneg hμ0 hφ0) (abs_nonneg (k - k'))
      linarith
  · have h1 := P.le_plannerOp w hkK' ⟨P.f_nonneg k' hkK', le_rfl⟩
    rw [sub_self] at h1
    have hfk'R : f k' ∈ Icc r kbar := ⟨hfr k' hk', P.f_le k' hkK'⟩
    have hyR : y ∈ Icc r kbar := ⟨(hfr k' hk').trans hyk.le, hy.2.trans (P.f_le k hkK)⟩
    have h2 := hw y hyR (f k') hfk'R
    rw [abs_of_pos (sub_pos.2 hyk)] at h2
    have h3 := hUL (f k - y) 0 le_rfl (by linarith [hy.2])
    have h4 : b * (μ * φ * (y - f k')) ≤ μ * (y - f k') := by
      have := mul_le_mul_of_nonneg_left hbφ (mul_nonneg hμ0 (sub_pos.2 hyk).le)
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left h2 P.b_nonneg
    have h6 : μ * (f k - f k') ≤ μ * |f k - f k'| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hμ0
    nlinarith

/-- **The value function is Lipschitz on `R = [r, k̄]`** with constant `μ φ`, under the
hypotheses of `PlannerHyp.plannerOp_lipschitz` (`T` preserves the bound, and `v = lim Tⁿ0`). -/
theorem PlannerHyp.plannerValue_lipschitz {U f : ℝ → ℝ} {b kbar μ φ r : ℝ}
    (P : PlannerHyp U f b kbar) (hμ0 : 0 ≤ μ)
    (hUL : ∀ c c', 0 ≤ c' → c' ≤ c → U c - U c' ≤ μ * (c - c'))
    (hφ0 : 0 ≤ φ) (hbφ : b * φ ≤ 1) (hr0 : 0 ≤ r) (hfr : ∀ k ∈ Icc r kbar, r ≤ f k)
    (hfL : ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar, |f k - f k'| ≤ φ * |k - k'|) :
    ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar,
      plannerValue P k - plannerValue P k' ≤ μ * φ * |k - k'| := by
  have hit : ∀ n : ℕ, ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar,
      ((plannerOp P)^[n] 0 : ℝ →ᵇ ℝ) k - ((plannerOp P)^[n] 0 : ℝ →ᵇ ℝ) k' ≤
        μ * φ * |k - k'| := by
    intro n
    induction n with
    | zero =>
      intro k _ k' _
      simp only [Function.iterate_zero, id, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
        sub_self]
      exact mul_nonneg (mul_nonneg hμ0 hφ0) (abs_nonneg _)
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact P.plannerOp_lipschitz hμ0 hUL hφ0 hbφ hr0 hfr hfL ih
  have hlim := P.plannerOp_contracting.tendsto_iterate_fixedPoint 0
  have hpt : ∀ x, Tendsto (fun n => ((plannerOp P)^[n] 0 : ℝ →ᵇ ℝ) x) atTop
      (𝓝 (plannerValue P x)) := fun x =>
    ((continuous_eval_const x).tendsto _).comp hlim
  intro k hk k' hk'
  exact le_of_tendsto' ((hpt k).sub (hpt k')) fun n => hit n k hk k' hk'

/-- **Positive consumption with a finite `U′(0)`.** Under `PlannerHyp`, let `U` have right
derivative `μ > 0` at `0` (finite marginal utility at zero consumption), and let `f` be
`φ`-Lipschitz on `R = [r, k̄]` with `b φ < 1`, where `0 ≤ r < f(k)` for every `k ∈ K`. Then
`g(k) < f(k)` on `K`. (Saving all of `f(k)` puts next period's capital in `R`, where the value
function is `μ φ`-Lipschitz; consuming `ε` instead gains `≈ μ ε` today and loses at most
`b μ φ ε` tomorrow.) The condition is `U′(0) > b · Lip(v|_R)` with the explicit bound
`Lip(v|_R) ≤ U′(0) φ`; it is needed (`corner_counterexample`). -/
theorem PlannerHyp.plannerPolicy_lt_of_lipschitz {U f : ℝ → ℝ} {b kbar μ φ r : ℝ}
    (P : PlannerHyp U f b kbar) (hμ : HasDerivWithinAt U μ (Ici 0) 0) (hμ0 : 0 < μ)
    (hφ0 : 0 ≤ φ) (hbφ : b * φ < 1) (hr0 : 0 ≤ r) (hfr : ∀ k ∈ Icc 0 kbar, r < f k)
    (hfL : ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar, |f k - f k'| ≤ φ * |k - k'|)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) : plannerPolicy P k < f k := by
  set v : ℝ → ℝ := ⇑(plannerValue P) with hvdef
  have hUL : ∀ c c', 0 ≤ c' → c' ≤ c → U c - U c' ≤ μ * (c - c') := fun c c' hc' hcc =>
    P.U_sub_le_of_hasDerivWithinAt hμ hc' hcc
  have hfr' : ∀ k ∈ Icc r kbar, r ≤ f k := fun k hk => (hfr k ⟨hr0.trans hk.1, hk.2⟩).le
  have hLip := P.plannerValue_lipschitz hμ0.le hUL hφ0 hbφ.le hr0 hfr' hfL
  obtain ⟨hg, hmax, -⟩ := P.plannerPolicy_spec hk
  by_contra hge
  push Not at hge
  have heq : plannerPolicy P k = f k := le_antisymm hg.2 hge
  set Y := f k with hY
  have hYr : r < Y := hfr k hk
  have hYR : Y ∈ Icc r kbar := ⟨hYr.le, P.f_le k hk⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), slope U 0 ε ≤ b * μ * φ := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hYr)] with ε hε
    have hopt := isMaxOn_iff.1 hmax (Y - ε) ⟨by linarith [hε.2], by linarith [hε.1]⟩
    rw [heq] at hopt
    change U (Y - (Y - ε)) + b * v (Y - ε) ≤ U (Y - Y) + b * v Y at hopt
    rw [sub_sub_cancel, sub_self] at hopt
    have hL := hLip Y hYR (Y - ε) ⟨by linarith [hε.2], by linarith [hε.1, hYR.2]⟩
    rw [sub_sub_cancel, abs_of_pos hε.1] at hL
    have hL' := mul_le_mul_of_nonneg_left hL P.b_nonneg
    rw [slope_def_field, sub_zero, div_le_iff₀ hε.1]
    change U ε - U 0 ≤ b * μ * φ * ε
    nlinarith
  have hlim : Tendsto (slope U 0) (𝓝[>] 0) (𝓝 μ) := by
    exact (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).1
      (hμ.mono Ioi_subset_Ici_self)
  have hle := le_of_tendsto hlim hev
  have : b * μ * φ < μ := by nlinarith
  linarith

/-! ### Exercise 18.1 and the equilibrium on all of `K` -/

/-- **The planner's Euler equation on all of `K`** for a policy interior on `K`, with `U`
differentiable on `(0, ∞)` and `f` on `K`:
`U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]` for every `k ∈ [0, k̄]`. -/
theorem PlannerHyp.planner_euler_on_K {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    deriv U (f k - plannerPolicy P k) = b * deriv f (plannerPolicy P k) *
      deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)) := by
  have hgk := (P.plannerPolicy_mem hk).1
  exact P.planner_euler hk (hint k hk).1 (hint k hk).2 (hint _ hgk).2
    (hUd _ (sub_pos.2 (hint k hk).2)) (hUd _ (sub_pos.2 (hint _ hgk).2)) (hfd _ hgk)

/-- **Transversality on all of `K`, including `k = 0`.** If the policy is interior on `K`, `U` is
differentiable on `(0, ∞)`, and `f` is concave on `[0, ∞)` and differentiable on `K` with
`f′ ≥ 0` there, then for every `β′ ∈ [0, 1)`, constant `a` and `k ∈ K`,
`β′ᵗ (a f′(k_t)) U′(c_t) k_t → 0` along `k_t = gᵗ(k)`. Consumption `f − g` is continuous and
positive on the compact `K`, so it is bounded below by some `c_min > 0`; hence
`0 ≤ U′(c_t) ≤ U′(c_min)`, `0 ≤ f′(k_t) ≤ f′(0)` and `k_t ≤ k̄`. No bound on `U′` near `0` is
needed. -/
theorem PlannerHyp.planner_tvc_on_K {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k)
    (β' a : ℝ) (hβ0 : 0 ≤ β') (hβ1 : β' < 1) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    Tendsto (fun t => β' ^ t * (a * deriv f ((plannerPolicy P)^[t] k)) *
      deriv U (f ((plannerPolicy P)^[t] k) - plannerPolicy P ((plannerPolicy P)^[t] k)) *
        (plannerPolicy P)^[t] k) atTop (𝓝 0) := by
  set g := plannerPolicy P with hg
  have h0K : (0 : ℝ) ∈ Icc 0 kbar := ⟨le_rfl, P.kbar_nonneg⟩
  have hgK : ∀ k ∈ Icc 0 kbar, g k ∈ Icc 0 kbar := fun k hk => (P.plannerPolicy_mem hk).1
  have hcont : ContinuousOn (fun k => f k - g k) (Icc 0 kbar) :=
    P.f_cont.sub P.plannerPolicy_continuousOn
  obtain ⟨k₀, hk₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, h0K⟩ hcont
  set cmin := f k₀ - g k₀ with hcmindef
  have hcmin : 0 < cmin := sub_pos.2 (hint k₀ hk₀).2
  have hfanti : ∀ k ∈ Icc 0 kbar, deriv f k ≤ deriv f 0 := fun k hk =>
    (hf.subset Icc_subset_Ici_self (convex_Icc 0 kbar)).antitoneOn_deriv hfd h0K hk hk.1
  have hkt := iterate_mem hgK hk
  refine (tvc_of_bounded (M := |a| * (deriv f 0 * deriv U cmin * kbar)) hβ0 hβ1
    (z := fun t => a * (deriv f (g^[t] k) * deriv U (f (g^[t] k) - g (g^[t] k)) * g^[t] k))
    fun t => ?_).congr fun t => by ring
  have hk' := hkt t
  have hct : cmin ≤ f (g^[t] k) - g (g^[t] k) := isMinOn_iff.1 hmin _ hk'
  have hU1 := P.deriv_U_anti hUd hcmin hct
  have hU0 : 0 ≤ deriv U (f (g^[t] k) - g (g^[t] k)) := P.deriv_U_nonneg (hcmin.trans_le hct)
  have hf1 := hfanti _ hk'
  have hf0 := hf' _ hk'
  have hUc0 : 0 ≤ deriv U cmin := hU0.trans hU1
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hf0 hU0) hk'.1)]
  have h1 := mul_le_mul hf1 hU1 hU0 (hf' 0 h0K)
  exact mul_le_mul h1 hk'.2 hk'.1 (mul_nonneg (hf' 0 h0K) hUc0)

/-- **Exercise 18.1 on all of `K = [0, k̄]`** for a constructed policy interior on `K` (pp.
543–544). Let `P : PlannerHyp U f β k̄` with `β > 0`, let `g` be interior on `K`, `U`
differentiable on `(0, ∞)` and bounded by `B₀` on `[0, ∞)`, and `f` concave on `[0, ∞)` and
differentiable on `K` with `f′ ≥ 0` there. Then:
(i) `v` solves (1) on `K` and is its only solution bounded on `K`; `g` is continuous on `K` and
the unique maximiser in (1);
(ii) the Euler equation holds on `K`, and the transversality condition
`βᵗ U′(c_t) f′(k_t) k_t → 0` holds from every `k ∈ K`, including `k = 0`;
(iii) (2) has a bounded solution `V` on `[0, ∞) × K`, unique among bounded solutions, with
`V(k, k; g) = v(k)`, the maximal value of the planner's problem, and `G(k, k; g) = g(k)`;
(iv) on `(0, k̄)`, `V₁(k, k; g) = v′(k) = f′(k) U′[f(k) − g(k)]`.
Compared with `ex_18_1_interior`, the aggregate state space is all of `K`; compared with
`ex_18_1_constructed`, `U` need not be differentiable at `0` and `U′`, `f′` need not be
continuous. Interiority on `K` is proved under `PosOutputInadaHyp` and `FiniteMarginalHyp`. -/
theorem ex_18_1_on_K {U f : ℝ → ℝ} {β B₀ kbar : ℝ} (P : PlannerHyp U f β kbar) (hβ0 : 0 < β)
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k) :
    SolvesPlanner U f β kbar (plannerValue P) ∧
      (∀ v : ℝ → ℝ, ∀ M', (∀ k ∈ Icc 0 kbar, |v k| ≤ M') → SolvesPlanner U f β kbar v →
        ∀ k ∈ Icc 0 kbar, v k = plannerValue P k) ∧
      ContinuousOn (plannerPolicy P) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerPolicy P k ∈ Icc 0 (f k) ∧ ∀ y ∈ Icc 0 (f k),
        U (f k - y) + β * plannerValue P y = plannerValue P k ↔ y = plannerPolicy P k) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) =
        β * deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)) *
          deriv f (plannerPolicy P k)) ∧
      (∀ k ∈ Icc 0 kbar, Tendsto (fun t => β ^ t *
        deriv U (f ((plannerPolicy P)^[t] k) - plannerPolicy P ((plannerPolicy P)^[t] k)) *
          deriv f ((plannerPolicy P)^[t] k) * (plannerPolicy P)^[t] k) atTop (𝓝 0)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy P) V β
          (Icc 0 kbar) ∧
        (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V' x k| ≤ M') →
          SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy P) V' β
            (Icc 0 kbar) → ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, V' x k = V x k) ∧
        (∀ k ∈ Icc 0 kbar, V k k = plannerValue P k ∧
          IsGreatest (plannerValues U f β k) (V k k) ∧
          ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
            (U (f k + (k - k) * deriv f k - y) + β * V y (plannerPolicy P k) = V k k ↔
              y = plannerPolicy P k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => V x k) (deriv (plannerValue P) k) k ∧
          HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - plannerPolicy P k)) k := by
  set g := plannerPolicy P with hg
  set K := Icc 0 kbar with hKdef
  have h0K : (0 : ℝ) ∈ K := ⟨le_rfl, P.kbar_nonneg⟩
  have hgK : ∀ k ∈ K, g k ∈ K := fun k hk => (P.plannerPolicy_mem hk).1
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1
  have hc : ∀ k ∈ K, 0 ≤ f k - g k := fun k hk => (sub_pos.2 (hint k hk).2).le
  have hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k := by
    intro k hk
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1 (hfd k hk)
    have := P.f_nonneg 0 h0K
    nlinarith
  have hUdK : ∀ k ∈ K, DifferentiableAt ℝ U (f k - g k) := fun k hk =>
    hUd _ (sub_pos.2 (hint k hk).2)
  have hU'K : ∀ k ∈ K, 0 ≤ deriv U (f k - g k) := fun k hk =>
    P.deriv_U_nonneg (sub_pos.2 (hint k hk).2)
  have heul' : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k) := fun k hk => by
    rw [P.planner_euler_on_K hint hUd hfd hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0) := fun k hk =>
    (P.planner_tvc_on_K hint hUd hf hfd hf' β 1 hβ0.le P.b_lt_one hk).congr fun t => by ring
  obtain ⟨V, M, hVb, hsol, huniq, hall⟩ := ex_18_1_full_pathwise P.U_strictConcave P.U_mono hβ0
    P.b_lt_one hUdK hU'K hUb hf hgK hK0 hfd hf' hw hc heul' htvc'
  have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
    rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
  have hpol : ∀ k ∈ K, plannerValue P k = U (f k - g k) + β * plannerValue P (g k) :=
    fun k hk => (P.plannerPolicy_spec hk).2.2
  have hdp := ex_18_1_dp_pathwise P.U_strictConcave hβ0 P.b_lt_one hUdK hU'K hUb hgK hK0 hf' hw
    hc heul' htvc' hvb hpol hVb hsol
  refine ⟨P.plannerValue_solves, fun v M' hvb' hv => P.solvesPlanner_unique hvb' hv,
    P.plannerPolicy_continuousOn,
    fun k hk => ⟨(P.plannerPolicy_spec hk).1, fun y hy => P.plannerPolicy_unique hk hy⟩, heul',
    htvc', V, M, hVb, hsol, huniq, fun k hk => ⟨(hdp k hk).1, (hall k hk).1, (hall k hk).2⟩,
    fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Icc_self hk
  have hv' := P.planner_envelope hk (hint k hkK).2 (hUdK k hkK) (hfd k hkK)
  refine ⟨?_, hv'⟩
  rw [hv'.deriv]
  have hopt := ((hall k hkK).2 (g k) ⟨(hgK k hkK).1, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : (fun k => f k - k * deriv f k) k + deriv f k * k - g k = f k - g k := by
    simp only; ring
  have e' : f k + (k - k) * deriv f k - g k = f k - g k := by ring
  rw [e'] at hopt
  exact bellman_envelope hβ0.le P.b_lt_one P.U_strictConcave.concaveOn hUb hVb hgK hw hf' hsol
    hk.1 hkK (hgK k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) (by rw [e]; exact hopt)
    (by rw [e]; exact (hUdK k hkK).hasDerivAt)

/-- **The indirect equilibrium on all of `K = [0, k̄]`** for a pseudo-planner's policy interior
on `K` (p. 546). Tax `θ ∈ [0, 1)` on capital income, rebated; `β < 1`;
`P : PlannerHyp U f ((1 − θ)β) k̄` with `(1 − θ)β > 0`; `U`, `f` as in `ex_18_1_on_K`. Then:
(i) `w` solves (8) on `K` and is its only solution bounded on `K`; `ĥ` is continuous; and on `K`,
`w(k)` is the value of the path of `ĥ` in the pseudo-economy, the maximal value of its sequence
problem; (ii) (9) `U′[f(k) − ĥ(k)] = β̂ w′(ĥ(k))` on `K` and (10)
`w′(k) = f′(k) U′[f(k) − ĥ(k)]` on `(0, k̄)`; the individual's transversality condition
`βᵗ (1 − θ) f′(k_t) U′(c_t) k_t → 0` holds from every `k ∈ K`, including `k = 0`; (iii) (3)
with `h = ĥ` has a bounded solution `W` on `[0, ∞) × K`, unique among bounded solutions,
`W(k, k; ĥ)` is the value of following `ĥ`, and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice
(a recursive competitive equilibrium on `K`); (iv) `φ(k) = W₁(k, k; ĥ) = (1 − θ) w′(k)` on
`(0, k̄)`. -/
theorem indirect_equilibrium_on_K {U f : ℝ → ℝ} {β θ B₀ kbar : ℝ}
    (P : PlannerHyp U f ((1 - θ) * β) kbar) (hb : 0 < (1 - θ) * β) (hβ1 : β < 1)
    (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k) :
    SolvesPlanner U f ((1 - θ) * β) kbar (plannerValue P) ∧
      (∀ w : ℝ → ℝ, ∀ M', (∀ k ∈ Icc 0 kbar, |w k| ≤ M') →
        SolvesPlanner U f ((1 - θ) * β) kbar w → ∀ k ∈ Icc 0 kbar, w k = plannerValue P k) ∧
      ContinuousOn (plannerPolicy P) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar,
        plannerValue P k = pathValue U f (plannerPolicy P) ((1 - θ) * β) k ∧
          IsGreatest (plannerValues U f ((1 - θ) * β) k) (plannerValue P k)) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) =
        (1 - θ) * β * deriv (plannerValue P) (plannerPolicy P k)) ∧
      (∀ k ∈ Ioo 0 kbar, HasDerivAt (plannerValue P)
        (deriv f k * deriv U (f k - plannerPolicy P k)) k) ∧
      (∀ k ∈ Icc 0 kbar, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f ((plannerPolicy P)^[t] k)) *
        deriv U (f ((plannerPolicy P)^[t] k) - plannerPolicy P ((plannerPolicy P)^[t] k)) *
          (plannerPolicy P)^[t] k) atTop (𝓝 0)) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) (plannerPolicy P) W β (Icc 0 kbar) ∧
        (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W' x k| ≤ M') →
          SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
            (fun k => (1 - θ) * deriv f k) (plannerPolicy P) W' β (Icc 0 kbar) →
            ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, W' x k = W x k) ∧
        (∀ k ∈ Icc 0 kbar, W k k = pathValue U f (plannerPolicy P) β k ∧
          ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
            (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (plannerPolicy P k) =
              W k k ↔ y = plannerPolicy P k)) ∧
        ∀ k ∈ Ioo 0 kbar,
          HasDerivAt (fun x => W x k) ((1 - θ) * deriv (plannerValue P) k) k := by
  set h := plannerPolicy P with hh
  set K := Icc 0 kbar with hKdef
  have h0K : (0 : ℝ) ∈ K := ⟨le_rfl, P.kbar_nonneg⟩
  have hβ0 : 0 < β := by
    by_contra hb'
    push Not at hb'
    have : (1 - θ) * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hb'
    linarith
  have hhK : ∀ k ∈ K, h k ∈ K := fun k hk => (P.plannerPolicy_mem hk).1
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1
  have hc : ∀ k ∈ K, 0 ≤ f k - h k := fun k hk => (sub_pos.2 (hint k hk).2).le
  have hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k := by
    intro k hk
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1 (hfd k hk)
    have := P.f_nonneg 0 h0K
    have := mul_nonneg (mul_nonneg hθ0 hk.1) (hf' k hk)
    nlinarith
  have hUdK : ∀ k ∈ K, DifferentiableAt ℝ U (f k - h k) := fun k hk =>
    hUd _ (sub_pos.2 (hint k hk).2)
  have hU'K : ∀ k ∈ K, 0 ≤ deriv U (f k - h k) := fun k hk =>
    P.deriv_U_nonneg (sub_pos.2 (hint k hk).2)
  have heul' : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k) := fun k hk => by
    rw [P.planner_euler_on_K hint hUd hfd hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0) := fun k hk =>
    P.planner_tvc_on_K hint hUd hf hfd hf' β (1 - θ) hβ0.le hβ1 hk
  obtain ⟨W, M, hWb, hsol, huniq, hall⟩ := indirect_equilibrium_full_pathwise P.U_strictConcave
    P.U_mono hβ0 hβ1 hθ0 hθ hUdK hU'K hUb hf hhK hK0 hfd hf' hw hc heul' htvc'
  have h10 : ∀ k ∈ Ioo 0 kbar,
      HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - h k)) k := fun k hk =>
    P.planner_envelope hk (hint k (Ioo_subset_Icc_self hk)).2 (hUdK k (Ioo_subset_Icc_self hk))
      (hfd k (Ioo_subset_Icc_self hk))
  have h9 : ∀ k ∈ K, deriv U (f k - h k) = (1 - θ) * β * deriv (plannerValue P) (h k) := by
    intro k hk
    have hhI : h k ∈ Ioo 0 kbar := ⟨(hint k hk).1, (hint k hk).2.trans_le (P.f_le k hk)⟩
    exact P.planner_foc hk (hint k hk).1 (hint k hk).2 (hUdK k hk) (h10 _ hhI).differentiableAt
  have hval : ∀ k ∈ K, plannerValue P k = pathValue U f h ((1 - θ) * β) k := by
    intro k hk
    have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
      rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
    have hs := policyValue_hasSum P.b_nonneg P.b_lt_one hhK hvb (fun k hk => hUb _ (hc k hk))
      (fun k hk => (P.plannerPolicy_spec hk).2.2) hk
    exact hs.tsum_eq.symm
  refine ⟨P.plannerValue_solves, fun w M' hwb hw' => P.solvesPlanner_unique hwb hw',
    P.plannerPolicy_continuousOn, fun k hk => ⟨hval k hk, (hval k hk) ▸ (hall k hk).1⟩, h9, h10,
    htvc', W, M, hWb, hsol, huniq, fun k hk => ⟨(hall k hk).2.1, (hall k hk).2.2⟩,
    fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Icc_self hk
  have hopt := ((hall k hkK).2.2 (h k) ⟨(hhK k hkK).1, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : f k + (1 - θ) * (k - k) * deriv f k - h k = f k - h k := by ring
  obtain ⟨h5, -⟩ := eq_18_1_4_5 hβ0.le hβ1 hθ P.U_strictConcave.concaveOn hUb hhK hf' hw hWb hsol
    hk.1 hkK (hint k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) hopt
    (by rw [e]; exact hUdK k hkK)
  rw [(h10 k hk).deriv]
  rw [e] at h5
  convert h5 using 1
  ring

/-! ### Primitive conditions for interiority on all of `K` -/

/-- **Primitive hypotheses for an interior policy on all of `K`: `f(0) > 0` and `U′(0+) = ∞`.**
`PlannerHyp`, `b > 0`, the Inada condition `(U(c) − U(0))/c → ∞` as `c → 0+`, `U` differentiable
on `(0, ∞)`, positive output at zero capital `f(0) > 0`, `f` nondecreasing on `K`, and a slope
condition at `0`: `f(y) ≥ f(0) + m y` for small `y > 0` with `b m > 1` (e.g. `b f′(0) > 1`, or
`f′(0+) = ∞`). The slope condition is needed: with a constant technology the policy is `0`
(`inada_const_counterexample`). -/
structure PosOutputInadaHyp (U f : ℝ → ℝ) (b kbar : ℝ) : Prop where
  planner : PlannerHyp U f b kbar
  b_pos : 0 < b
  U_inada : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop
  U_diff : ∀ c, 0 < c → DifferentiableAt ℝ U c
  f_zero_pos : 0 < f 0
  f_mono : MonotoneOn f (Icc 0 kbar)
  f_slope : ∃ m, 1 < b * m ∧ ∀ᶠ y in 𝓝[>] 0, f 0 + m * y ≤ f y

/-- **Interiority on all of `K`** under `PosOutputInadaHyp`: `0 < g(k) < f(k)` for every
`k ∈ [0, k̄]`, including `k = 0` (contrast `InteriorHyp.not_interior_zero` when `f(0) = 0`).
Positive consumption is `PlannerHyp.plannerPolicy_lt_of_inada` (`f > 0` on `K`); positive saving
is `PlannerHyp.plannerPolicy_pos_of_slope`. -/
theorem PosOutputInadaHyp.policy_interior {U f : ℝ → ℝ} {b kbar : ℝ}
    (I : PosOutputInadaHyp U f b kbar) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k := by
  have h0K : (0 : ℝ) ∈ Icc 0 kbar := ⟨le_rfl, I.planner.kbar_nonneg⟩
  have hlt : ∀ k ∈ Icc 0 kbar, plannerPolicy I.planner k < f k := fun k hk =>
    I.planner.plannerPolicy_lt_of_inada I.U_inada hk
      (I.f_zero_pos.trans_le (I.f_mono h0K hk hk.1))
  obtain ⟨m, hm, hfm⟩ := I.f_slope
  exact ⟨I.planner.plannerPolicy_pos_of_slope I.b_pos hm hfm I.f_mono (hlt 0 h0K) I.U_diff hk,
    hlt k hk⟩

/-- **Primitive hypotheses for an interior policy on all of `K`: finite `U′(0)`.** `PlannerHyp`,
`b > 0`, `U` with finite positive right derivative `U′(0) = μ` at `0` and differentiable on
`(0, ∞)`, `f` nondecreasing on `K` with the slope condition at `0` of `PosOutputInadaHyp`
(`b m > 1`), and a bound on the return to saving out of output: for some `0 ≤ r < f(0)`, `f` is
`φ`-Lipschitz on `[r, k̄]` with `b φ < 1`. (Saving everything puts next period's capital in
`[f(0), k̄] ⊆ [r, k̄]`, where the value function is `μ φ`-Lipschitz, so the condition is
`U′(0) > b μ φ ≥ b · Lip(v)`.) Both conditions are needed: without the first the policy can be
`0` (`inada_const_counterexample`), without the second it can be `f`
(`corner_counterexample`). -/
structure FiniteMarginalHyp (U f : ℝ → ℝ) (b kbar : ℝ) : Prop where
  planner : PlannerHyp U f b kbar
  b_pos : 0 < b
  U_deriv_zero : ∃ μ, 0 < μ ∧ HasDerivWithinAt U μ (Ici 0) 0
  U_diff : ∀ c, 0 < c → DifferentiableAt ℝ U c
  f_mono : MonotoneOn f (Icc 0 kbar)
  f_slope : ∃ m, 1 < b * m ∧ ∀ᶠ y in 𝓝[>] 0, f 0 + m * y ≤ f y
  f_lip : ∃ r φ, 0 ≤ r ∧ r < f 0 ∧ 0 ≤ φ ∧ b * φ < 1 ∧
    ∀ k ∈ Icc r kbar, ∀ k' ∈ Icc r kbar, |f k - f k'| ≤ φ * |k - k'|

/-- **Interiority on all of `K`** under `FiniteMarginalHyp`: `0 < g(k) < f(k)` for every
`k ∈ [0, k̄]` (`PlannerHyp.plannerPolicy_lt_of_lipschitz`,
`PlannerHyp.plannerPolicy_pos_of_slope`). -/
theorem FiniteMarginalHyp.policy_interior {U f : ℝ → ℝ} {b kbar : ℝ}
    (I : FiniteMarginalHyp U f b kbar) {k : ℝ} (hk : k ∈ Icc 0 kbar) :
    0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k := by
  have h0K : (0 : ℝ) ∈ Icc 0 kbar := ⟨le_rfl, I.planner.kbar_nonneg⟩
  obtain ⟨μ, hμ0, hμ⟩ := I.U_deriv_zero
  obtain ⟨r, φ, hr0, hr, hφ0, hbφ, hfL⟩ := I.f_lip
  have hlt : ∀ k ∈ Icc 0 kbar, plannerPolicy I.planner k < f k := fun k hk =>
    I.planner.plannerPolicy_lt_of_lipschitz hμ hμ0 hφ0 hbφ hr0
      (fun k hk => hr.trans_le (I.f_mono h0K hk hk.1)) hfL hk
  obtain ⟨m, hm, hfm⟩ := I.f_slope
  exact ⟨I.planner.plannerPolicy_pos_of_slope I.b_pos hm hfm I.f_mono (hlt 0 h0K) I.U_diff hk,
    hlt k hk⟩

/-- **Exercise 18.1 on all of `K` when `f(0) > 0` and `U′(0+) = ∞`** (pp. 543–544): under
`PosOutputInadaHyp`, with `U` bounded on `[0, ∞)` and `f` concave on `[0, ∞)` and differentiable
on `K` with `f′ ≥ 0`, the constructed policy is interior on `K` and the conclusions of
`ex_18_1_on_K` hold, including the transversality condition from `k = 0`. -/
theorem PosOutputInadaHyp.ex_18_1 {U f : ℝ → ℝ} {β B₀ kbar : ℝ} (I : PosOutputInadaHyp U f β kbar)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Icc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f β kbar (plannerValue I.planner) ∧
      (∀ v : ℝ → ℝ, ∀ M', (∀ k ∈ Icc 0 kbar, |v k| ≤ M') → SolvesPlanner U f β kbar v →
        ∀ k ∈ Icc 0 kbar, v k = plannerValue I.planner k) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerPolicy I.planner k ∈ Icc 0 (f k) ∧ ∀ y ∈ Icc 0 (f k),
        U (f k - y) + β * plannerValue I.planner y = plannerValue I.planner k ↔ y =
          plannerPolicy I.planner k) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        β * deriv U (f (plannerPolicy I.planner k) -
          plannerPolicy I.planner (plannerPolicy I.planner k)) *
          deriv f (plannerPolicy I.planner k)) ∧
      (∀ k ∈ Icc 0 kbar, Tendsto (fun t => β ^ t *
        deriv U (f ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          deriv f ((plannerPolicy I.planner)^[t] k) *
            (plannerPolicy I.planner)^[t] k) atTop (𝓝 0)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V β
          (Icc 0 kbar) ∧
        (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V' x k| ≤ M') →
          SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V' β
            (Icc 0 kbar) → ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, V' x k = V x k) ∧
        (∀ k ∈ Icc 0 kbar, V k k = plannerValue I.planner k ∧
          IsGreatest (plannerValues U f β k) (V k k) ∧
          ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
            (U (f k + (k - k) * deriv f k - y) + β * V y (plannerPolicy I.planner k) = V k k ↔
              y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => V x k) (deriv (plannerValue I.planner) k) k ∧
          HasDerivAt (plannerValue I.planner) (deriv f k * deriv U (f k -
            plannerPolicy I.planner k)) k :=
  ⟨fun _ hk => I.policy_interior hk,
    ex_18_1_on_K I.planner I.b_pos (fun _ hk => I.policy_interior hk) I.U_diff hUb hf hfd hf'⟩

/-- **The indirect equilibrium on all of `K` when `f(0) > 0` and `U′(0+) = ∞`** (p. 546):
under `PosOutputInadaHyp` for `β̂ = (1 − θ)β`, the pseudo-planner's policy is interior on `K`
and the conclusions of `indirect_equilibrium_on_K` hold. -/
theorem PosOutputInadaHyp.indirect_equilibrium {U f : ℝ → ℝ} {β θ B₀ kbar : ℝ}
    (I : PosOutputInadaHyp U f ((1 - θ) * β) kbar) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Icc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f ((1 - θ) * β) kbar (plannerValue I.planner) ∧
      (∀ w : ℝ → ℝ, ∀ M', (∀ k ∈ Icc 0 kbar, |w k| ≤ M') →
      SolvesPlanner U f ((1 - θ) * β) kbar w → ∀ k ∈ Icc 0 kbar, w k = plannerValue I.planner k) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar,
        plannerValue I.planner k = pathValue U f (plannerPolicy I.planner) ((1 - θ) * β) k ∧
          IsGreatest (plannerValues U f ((1 - θ) * β) k) (plannerValue I.planner k)) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        (1 - θ) * β * deriv (plannerValue I.planner) (plannerPolicy I.planner k)) ∧
      (∀ k ∈ Ioo 0 kbar, HasDerivAt (plannerValue I.planner)
        (deriv f k * deriv U (f k - plannerPolicy I.planner k)) k) ∧
      (∀ k ∈ Icc 0 kbar, Tendsto (fun t => β ^ t * ((1 - θ) *
        deriv f ((plannerPolicy I.planner)^[t] k)) *
        deriv U (f ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          (plannerPolicy I.planner)^[t] k) atTop (𝓝 0)) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W β (Icc 0 kbar) ∧
        (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W' x k| ≤ M') →
          SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
            (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W' β (Icc 0 kbar) →
            ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, W' x k = W x k) ∧
        (∀ k ∈ Icc 0 kbar, W k k = pathValue U f (plannerPolicy I.planner) β k ∧
          ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
            (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (plannerPolicy I.planner k) =
              W k k ↔ y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar,
          HasDerivAt (fun x => W x k) ((1 - θ) * deriv (plannerValue I.planner) k) k :=
  ⟨fun _ hk => I.policy_interior hk, indirect_equilibrium_on_K I.planner I.b_pos hβ1 hθ0 hθ
    (fun _ hk => I.policy_interior hk) I.U_diff hUb hf hfd hf'⟩

/-- **Exercise 18.1 on all of `K` with a finite `U′(0)`** (pp. 543–544): under
`FiniteMarginalHyp`, with `U` bounded on `[0, ∞)` and `f` concave on `[0, ∞)` and differentiable
on `K` with `f′ ≥ 0`, the constructed policy is interior on `K` and the conclusions of
`ex_18_1_on_K` hold. -/
theorem FiniteMarginalHyp.ex_18_1 {U f : ℝ → ℝ} {β B₀ kbar : ℝ} (I : FiniteMarginalHyp U f β kbar)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Icc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f β kbar (plannerValue I.planner) ∧
      (∀ v : ℝ → ℝ, ∀ M', (∀ k ∈ Icc 0 kbar, |v k| ≤ M') → SolvesPlanner U f β kbar v →
        ∀ k ∈ Icc 0 kbar, v k = plannerValue I.planner k) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerPolicy I.planner k ∈ Icc 0 (f k) ∧ ∀ y ∈ Icc 0 (f k),
        U (f k - y) + β * plannerValue I.planner y = plannerValue I.planner k ↔ y =
          plannerPolicy I.planner k) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        β * deriv U (f (plannerPolicy I.planner k) -
          plannerPolicy I.planner (plannerPolicy I.planner k)) *
          deriv f (plannerPolicy I.planner k)) ∧
      (∀ k ∈ Icc 0 kbar, Tendsto (fun t => β ^ t *
        deriv U (f ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          deriv f ((plannerPolicy I.planner)^[t] k) *
            (plannerPolicy I.planner)^[t] k) atTop (𝓝 0)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V β
          (Icc 0 kbar) ∧
        (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |V' x k| ≤ M') →
          SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V' β
            (Icc 0 kbar) → ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, V' x k = V x k) ∧
        (∀ k ∈ Icc 0 kbar, V k k = plannerValue I.planner k ∧
          IsGreatest (plannerValues U f β k) (V k k) ∧
          ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
            (U (f k + (k - k) * deriv f k - y) + β * V y (plannerPolicy I.planner k) = V k k ↔
              y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => V x k) (deriv (plannerValue I.planner) k) k ∧
          HasDerivAt (plannerValue I.planner) (deriv f k * deriv U (f k -
            plannerPolicy I.planner k)) k :=
  ⟨fun _ hk => I.policy_interior hk,
    ex_18_1_on_K I.planner I.b_pos (fun _ hk => I.policy_interior hk) I.U_diff hUb hf hfd hf'⟩

/-- **The indirect equilibrium on all of `K` with a finite `U′(0)`** (p. 546): under
`FiniteMarginalHyp` for `β̂ = (1 − θ)β`, the pseudo-planner's policy is interior on `K` and the
conclusions of `indirect_equilibrium_on_K` hold. -/
theorem FiniteMarginalHyp.indirect_equilibrium {U f : ℝ → ℝ} {β θ B₀ kbar : ℝ}
    (I : FiniteMarginalHyp U f ((1 - θ) * β) kbar) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Icc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f ((1 - θ) * β) kbar (plannerValue I.planner) ∧
      (∀ w : ℝ → ℝ, ∀ M', (∀ k ∈ Icc 0 kbar, |w k| ≤ M') →
      SolvesPlanner U f ((1 - θ) * β) kbar w → ∀ k ∈ Icc 0 kbar, w k = plannerValue I.planner k) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar,
        plannerValue I.planner k = pathValue U f (plannerPolicy I.planner) ((1 - θ) * β) k ∧
          IsGreatest (plannerValues U f ((1 - θ) * β) k) (plannerValue I.planner k)) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        (1 - θ) * β * deriv (plannerValue I.planner) (plannerPolicy I.planner k)) ∧
      (∀ k ∈ Ioo 0 kbar, HasDerivAt (plannerValue I.planner)
        (deriv f k * deriv U (f k - plannerPolicy I.planner k)) k) ∧
      (∀ k ∈ Icc 0 kbar, Tendsto (fun t => β ^ t * ((1 - θ) *
        deriv f ((plannerPolicy I.planner)^[t] k)) *
        deriv U (f ((plannerPolicy I.planner)^[t] k) -
          plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          (plannerPolicy I.planner)^[t] k) atTop (𝓝 0)) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W β (Icc 0 kbar) ∧
        (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W' x k| ≤ M') →
          SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
            (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W' β (Icc 0 kbar) →
            ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, W' x k = W x k) ∧
        (∀ k ∈ Icc 0 kbar, W k k = pathValue U f (plannerPolicy I.planner) β k ∧
          ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
            (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (plannerPolicy I.planner k) =
              W k k ↔ y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar,
          HasDerivAt (fun x => W x k) ((1 - θ) * deriv (plannerValue I.planner) k) k :=
  ⟨fun _ hk => I.policy_interior hk, indirect_equilibrium_on_K I.planner I.b_pos hβ1 hθ0 hθ
    (fun _ hk => I.policy_interior hk) I.U_diff hUb hf hfd hf'⟩

/-! ### A constant technology: the policy is zero -/

/-- **With a constant technology the planner never saves.** Under `PlannerHyp`, if `f ≡ a` on
`K`, then `v` is constant on `K` and `g(k) = 0` for every `k ∈ K`, whatever `U` (Inada or not). -/
theorem PlannerHyp.plannerPolicy_eq_zero_of_const {U f : ℝ → ℝ} {b kbar a : ℝ}
    (P : PlannerHyp U f b kbar) (hfa : ∀ k ∈ Icc 0 kbar, f k = a) {k : ℝ}
    (hk : k ∈ Icc 0 kbar) : plannerPolicy P k = 0 := by
  have h0K : (0 : ℝ) ∈ Icc 0 kbar := ⟨le_rfl, P.kbar_nonneg⟩
  have hconst : ∀ k ∈ Icc 0 kbar, plannerValue P k = plannerValue P 0 := by
    intro k hk
    have h1 := P.plannerValue_solves k hk
    have h2 := P.plannerValue_solves 0 h0K
    rw [hfa k hk] at h1
    rw [hfa 0 h0K] at h2
    rw [h1, h2]
  obtain ⟨hg, hmax, hv⟩ := P.plannerPolicy_spec hk
  have hgK : plannerPolicy P k ∈ Icc 0 kbar := (P.plannerPolicy_mem hk).1
  have hf0 := P.f_nonneg k hk
  have h1 := isMaxOn_iff.1 hmax 0 ⟨le_rfl, hf0⟩
  change U (f k - 0) + b * plannerValue P 0 ≤
    U (f k - plannerPolicy P k) + b * plannerValue P (plannerPolicy P k) at h1
  have h2 : U (f k - plannerPolicy P k) ≤ U (f k - 0) :=
    P.U_mono (mem_Ici.2 (by linarith [hg.2])) (mem_Ici.2 (by linarith)) (by linarith [hg.1])
  rw [hconst _ hgK] at h1 hv
  have := (P.plannerPolicy_unique hk ⟨le_rfl, hf0⟩).1 (by linarith)
  exact this.symm

end StokeyLucasPrescott.EquilibriaWithDistortions
