/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectInteriorDP

/-!
# Interiority of the constructed planner's policy, §18.1

SLP §18.1, pp. 543–546. `ex_18_1_constructed` and `indirect_equilibrium_constructed` assume that
the policy `g` constructed in `IndirectExistence` is interior, `0 < g(k) < f(k)` on `K = [0, k̄]`,
and that `U′` and `f′` are continuous on `[0, k̄]`. With `U` differentiable on `[0, ∞)`, `U′(0)`
is finite and the Inada argument is unavailable. Here `U` is only continuous on `[0, ∞)`
(`PlannerHyp` asks no more), which allows `U′(0+) = ∞` with `U` bounded, e.g.
`U(c) = 1 − e^{−√c}` (`IndirectInteriorExample`).

* `InteriorHyp`: `PlannerHyp`, `b > 0`, the Inada condition `(U(c) − U(0))/c → ∞` as `c → 0+`,
  `f(0) = 0` and `f > 0` on `(0, k̄]`.
* `PlannerHyp.plannerPolicy_lt_of_inada` (route (i)): `g(k) < f(k)` wherever `f(k) > 0`.
* `PlannerHyp.plannerPolicy_pos_of_inada` (route (ii)): `g(k) > 0` on `(0, k̄]`. Only
  `U′(0+) = ∞`, `f(0) = 0` and concavity are used; no condition on `f′(0)` is needed, because a
  zero saving leaves zero consumption from the next period on.
* `InteriorHyp.policy_interior`, `InteriorHyp.policy_mapsTo`: `0 < g(k) < f(k)` on `(0, k̄]`,
  which `g` maps into itself. `InteriorHyp.not_interior_zero` (route (iii)): `g(0) = 0`, so
  interiority on all of `K` is impossible; the statements are made on `(0, k̄]`.
* `InteriorHyp.planner_euler_interior`: the Euler equation on `(0, k̄]`.
* `InteriorHyp.tvc_bound`, `InteriorHyp.planner_tvc`: the transversality condition
  `β′ᵗ a f′(k_t) U′(c_t) k_t → 0` for every `β′ ∈ [0, 1)`, from `v′(k) k ≤ v(k) − v(0)` (concavity
  and the envelope condition). This replaces the bound on `U′` from its continuity on `[0, k̄]`.
* `ex_18_1_interior`, `indirect_equilibrium_interior`: Exercise 18.1 and the indirect equilibrium
  of the pseudo-economy (`β̂ = (1 − θ)β`) with the planner constructed, interiority proved rather
  than assumed, `U` differentiable on `(0, ∞)` only, and no continuity of `U′` or `f′`; the
  aggregate state space is `(0, k̄]`.

The dynamic-programming steps are `ex_18_1_full_pathwise` and
`indirect_equilibrium_full_pathwise` (`IndirectInteriorDP`), which need `U` differentiable only
along the path.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set

/-- **The Inada condition in `ε`–`δ` form.** If `(U(c) − U(0))/c → ∞` as `c → 0+`, then for
every `L` there is `δ > 0` with `L c < U(c) − U(0)` for `0 < c < δ`. -/
theorem inada_exists_delta {U : ℝ → ℝ} (hI : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop)
    (L : ℝ) : ∃ δ > 0, ∀ c, 0 < c → c < δ → L * c < U c - U 0 := by
  have h := tendsto_atTop.1 hI (L + 1)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hδc⟩ := h
  refine ⟨δ, hδ, fun c hc hcδ => ?_⟩
  have h1 := hδc (by rw [Real.dist_eq, sub_zero, abs_of_pos hc]; exact hcδ) (mem_Ioi.2 hc)
  rw [le_div_iff₀ hc] at h1
  nlinarith

/-- **Positive consumption** (route (i)). Under `PlannerHyp`, if `U′(0+) = ∞` in the form
`(U(c) − U(0))/c → ∞` as `c → 0+`, then at every `k ∈ K` with `f(k) > 0` the planner consumes a
positive amount: `g(k) < f(k)`. (Saving everything loses `U(ε) − U(0)` against a gain in `b v` of
at most `4 b ‖v‖ ε / f(k)`, by concavity of `v`.) -/
theorem PlannerHyp.plannerPolicy_lt_of_inada {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) (hI : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop)
    {k : ℝ} (hk : k ∈ Icc 0 kbar) (hfk : 0 < f k) : plannerPolicy P k < f k := by
  set v := plannerValue P with hvdef
  set y₀ := f k with hy₀
  obtain ⟨hg, hmax, -⟩ := P.plannerPolicy_spec hk
  by_contra hge
  push Not at hge
  have heq : plannerPolicy P k = y₀ := le_antisymm hg.2 hge
  set Mv := ‖v‖ with hMvdef
  have hMv : ∀ x, |v x| ≤ Mv := fun x => by
    rw [← Real.norm_eq_abs]; exact v.norm_coe_le_norm x
  have hMv0 : 0 ≤ Mv := norm_nonneg _
  have hy₀K : y₀ ≤ kbar := P.f_le k hk
  obtain ⟨δ, hδ, hδc⟩ := inada_exists_delta hI (b * (4 * Mv / y₀))
  set ε := min (y₀ / 2) (δ / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ y₀ / 2 := min_le_left _ _
  have hε2 : ε < δ := (min_le_right _ _).trans_lt (by linarith)
  have hU := hδc ε hε0 hε2
  have hm := isMaxOn_iff.1 hmax (y₀ - ε) ⟨by linarith, by linarith⟩
  rw [heq] at hm
  simp only [hy₀, sub_sub_cancel, sub_self] at hm
  -- concavity of `v` between `0` and `y₀`
  change U ε + b * v (y₀ - ε) ≤ U 0 + b * v y₀ at hm
  have hcv := P.plannerValue_concave.2 (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar)
    (⟨hfk.le, hy₀K⟩ : y₀ ∈ Icc 0 kbar) (by positivity : 0 ≤ ε / y₀)
    (div_nonneg (by linarith) hfk.le : 0 ≤ (y₀ - ε) / y₀) (by field_simp; ring)
  have hpt : (ε / y₀) • (0 : ℝ) + ((y₀ - ε) / y₀) • y₀ = y₀ - ε := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hpt] at hcv
  simp only [smul_eq_mul] at hcv
  have hcv' : ε * v 0 + (y₀ - ε) * v y₀ ≤ y₀ * v (y₀ - ε) := by
    have := mul_le_mul_of_nonneg_left hcv hfk.le
    have e : y₀ * (ε / y₀ * v 0 + (y₀ - ε) / y₀ * v y₀) = ε * v 0 + (y₀ - ε) * v y₀ := by
      field_simp
    linarith
  have hb1 := abs_le.1 (hMv 0)
  have hb2 := abs_le.1 (hMv (y₀ - ε))
  have hD : y₀ * (v y₀ - v (y₀ - ε)) ≤ 4 * ε * Mv := by
    rcases le_or_gt (v y₀ - v (y₀ - ε)) 0 with h | h
    · nlinarith
    · nlinarith
  have hbD := mul_le_mul_of_nonneg_left hD P.b_nonneg
  have e2 : b * (4 * Mv / y₀) * ε * y₀ = b * (4 * ε * Mv) := by field_simp
  have h3 : b * (4 * Mv / y₀) * ε * y₀ < (U ε - U 0) * y₀ := mul_lt_mul_of_pos_right hU hfk
  nlinarith

/-- **`k = 0` is degenerate when `f(0) = 0`**: `g(0) = 0`, and `v(0) = U(0) + b v(0)`. -/
theorem PlannerHyp.plannerPolicy_zero {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (hf0 : f 0 = 0) : plannerPolicy P 0 = 0 ∧
      plannerValue P 0 = U 0 + b * plannerValue P 0 := by
  obtain ⟨hg, -, hv⟩ := P.plannerPolicy_spec (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar)
  rw [hf0] at hg hv
  have h0 : plannerPolicy P 0 = 0 := le_antisymm hg.2 hg.1
  rw [h0, sub_zero] at hv
  exact ⟨h0, hv⟩

/-- **Positive saving** (route (ii)). Under `PlannerHyp`, with `b > 0`, `U′(0+) = ∞`
(`(U(c) − U(0))/c → ∞` as `c → 0+`), `f(0) = 0` and `f > 0` on `(0, k̄]`, the planner saves a
positive amount at every `k ∈ (0, k̄]`: `g(k) > 0`. (Saving nothing leaves zero capital, hence
zero consumption, from the next period on; saving `y` gains at least `b [U(f(y)) − U(0)]`, which
is of larger order than `y` since `f(y) ≥ (f(k)/k) y` by concavity, while the loss today is
`O(y)` by concavity of `U`.) No condition on `f′(0)` is needed. -/
theorem PlannerHyp.plannerPolicy_pos_of_inada {U f : ℝ → ℝ} {b kbar : ℝ}
    (P : PlannerHyp U f b kbar) (hb : 0 < b)
    (hI : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop) (hf0 : f 0 = 0)
    (hfpos : ∀ k ∈ Ioc 0 kbar, 0 < f k) {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    0 < plannerPolicy P k := by
  have hkK : k ∈ Icc 0 kbar := Ioc_subset_Icc_self hk
  set v := plannerValue P with hvdef
  set c := f k with hcdef
  have hc : 0 < c := hfpos k hk
  obtain ⟨hg, hmax, -⟩ := P.plannerPolicy_spec hkK
  by_contra hle
  push Not at hle
  have heq : plannerPolicy P k = 0 := le_antisymm hle hg.1
  have hv0 : v 0 = U 0 + b * v 0 := (P.plannerPolicy_zero hf0).2
  -- `v(y) ≥ U(f(y)) + b v(0)`: consume everything at `y`
  have hvy : ∀ y ∈ Icc 0 kbar, U (f y) + b * v 0 ≤ v y := by
    intro y hy
    obtain ⟨-, hmy, hvy⟩ := P.plannerPolicy_spec hy
    have := isMaxOn_iff.1 hmy 0 ⟨le_rfl, P.f_nonneg y hy⟩
    simp only [sub_zero] at this
    change U (f y) + b * v 0 ≤ U (f y - plannerPolicy P y) + b * v (plannerPolicy P y) at this
    change v y = U (f y - plannerPolicy P y) + b * v (plannerPolicy P y) at hvy
    linarith
  -- the bound on `U(c) − U(c − y)` from concavity
  set D := 2 * (U c - U 0) / c with hDdef
  have hU0c : U 0 ≤ U c := P.U_mono (mem_Ici.2 le_rfl) (mem_Ici.2 hc.le) hc.le
  have hD0 : 0 ≤ D := by positivity
  have hUc : ∀ y, 0 < y → y ≤ c / 2 → U c - U (c - y) ≤ D * y := by
    intro y hy hyc
    have hcv := P.U_strictConcave.concaveOn.2 (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0)
      (mem_Ici.2 hc.le) (div_nonneg hy.le hc.le : 0 ≤ y / c)
      (div_nonneg (by linarith) hc.le : 0 ≤ (c - y) / c) (by field_simp; ring)
    have hpt : (y / c) • (0 : ℝ) + ((c - y) / c) • c = c - y := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt] at hcv
    simp only [smul_eq_mul] at hcv
    have hcv' : y * U 0 + (c - y) * U c ≤ c * U (c - y) := by
      have := mul_le_mul_of_nonneg_left hcv hc.le
      have e : c * (y / c * U 0 + (c - y) / c * U c) = y * U 0 + (c - y) * U c := by
        field_simp
      linarith
    have hmono : U (c - y) ≤ U c :=
      P.U_mono (mem_Ici.2 (by linarith)) (mem_Ici.2 hc.le) (by linarith)
    have e2 : D * y * c = 2 * y * (U c - U 0) := by rw [hDdef]; field_simp
    nlinarith
  -- `f(y) ≥ m y` on `[0, k]`, `m = f(k)/k`
  set m := c / k with hmdef
  have hm0 : 0 < m := div_pos hc hk.1
  have hfy : ∀ y, 0 ≤ y → y ≤ k → m * y ≤ f y := by
    intro y hy hyk
    have hk0 : k ≠ 0 := hk.1.ne'
    have hcv := P.f_concave.2 (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar) hkK
      (div_nonneg (by linarith) hk.1.le : 0 ≤ (k - y) / k) (div_nonneg hy hk.1.le : 0 ≤ y / k)
      (by field_simp; ring)
    have hpt : ((k - y) / k) • (0 : ℝ) + (y / k) • k = y := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [hpt, hf0] at hcv
    simp only [smul_eq_mul, mul_zero, zero_add] at hcv
    have e : m * y = y / k * f k := by rw [hmdef, hcdef]; field_simp
    linarith
  -- the Inada condition at `f(y)` for small `y`
  set L := (D + 1) / (b * m) with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hLm : b * L * m = D + 1 := by rw [hLdef]; field_simp
  obtain ⟨δ, hδ, hδc⟩ := inada_exists_delta hI L
  obtain ⟨δ', hδ', hδ'c⟩ := Metric.continuousWithinAt_iff.1
    (P.f_cont 0 ⟨le_rfl, P.kbar_nonneg⟩) δ hδ
  set y := min (min (c / 2) k) (δ' / 2) with hydef
  have hy0 : 0 < y := lt_min (lt_min (by linarith) hk.1) (by linarith)
  have hyc : y ≤ c / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hyk : y ≤ k := (min_le_left _ _).trans (min_le_right _ _)
  have hyδ : y < δ' := (min_le_right _ _).trans_lt (by linarith)
  have hyK : y ∈ Icc 0 kbar := ⟨hy0.le, hyk.trans hk.2⟩
  have hfy0 : 0 < f y := hfpos y ⟨hy0, hyk.trans hk.2⟩
  have hfyδ : f y < δ := by
    have := hδ'c hyK (by rw [Real.dist_eq, sub_zero, abs_of_pos hy0]; exact hyδ)
    rw [Real.dist_eq, hf0, sub_zero, abs_of_pos hfy0] at this
    exact this
  have hIn := hδc (f y) hfy0 hfyδ
  -- optimality of `g(k) = 0` against saving `y`
  have hopt := isMaxOn_iff.1 hmax y ⟨hy0.le, by linarith⟩
  rw [heq] at hopt
  change U (c - y) + b * v y ≤ U (c - 0) + b * v 0 at hopt
  rw [sub_zero] at hopt
  have h1 := hvy y hyK
  have h2 := hUc y hy0 hyc
  have h3 : L * (m * y) ≤ L * f y := mul_le_mul_of_nonneg_left (hfy y hy0.le hyk) hL0
  -- `b (U(f y) − U 0) ≤ D y` but `b (U(f y) − U 0) > (D + 1) y`
  have h4 : b * (U (f y) - U 0) ≤ D * y := by nlinarith
  have h5 : (D + 1) * y < b * (U (f y) - U 0) := by
    have := mul_lt_mul_of_pos_left hIn hb
    nlinarith
  linarith

/-- Under `PlannerHyp`, `U′(c) ≥ 0` for every `c > 0` (`U` is nondecreasing on `[0, ∞)`). -/
theorem PlannerHyp.deriv_U_nonneg {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    {c : ℝ} (hc : 0 < c) : 0 ≤ deriv U c := by
  rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hc)]
  exact P.U_mono.derivWithin_nonneg

/-- **Primitive hypotheses for an interior planner's policy**: `PlannerHyp` (with `U` only
continuous on `[0, ∞)`, so `U′(0+) = ∞` is allowed), a positive discount factor, the Inada
condition `(U(c) − U(0))/c → ∞` as `c → 0+`, `f(0) = 0`, and `f > 0` on `(0, k̄]`. -/
structure InteriorHyp (U f : ℝ → ℝ) (b kbar : ℝ) : Prop where
  planner : PlannerHyp U f b kbar
  b_pos : 0 < b
  U_inada : Tendsto (fun c => (U c - U 0) / c) (𝓝[>] 0) atTop
  f_zero : f 0 = 0
  f_pos : ∀ k ∈ Ioc 0 kbar, 0 < f k

/-- **Interiority of the constructed policy on `(0, k̄]`**: `0 < g(k) < f(k)`. -/
theorem InteriorHyp.policy_interior {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k :=
  ⟨I.planner.plannerPolicy_pos_of_inada I.b_pos I.U_inada I.f_zero I.f_pos hk,
    I.planner.plannerPolicy_lt_of_inada I.U_inada (Ioc_subset_Icc_self hk) (I.f_pos k hk)⟩

/-- The policy maps `(0, k̄]` into `(0, k̄)`. -/
theorem InteriorHyp.policy_mem_Ioo {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    plannerPolicy I.planner k ∈ Ioo 0 kbar :=
  ⟨(I.policy_interior hk).1,
    (I.policy_interior hk).2.trans_le (I.planner.f_le k (Ioc_subset_Icc_self hk))⟩

/-- The policy maps `(0, k̄]` into itself. -/
theorem InteriorHyp.policy_mapsTo {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    plannerPolicy I.planner k ∈ Ioc 0 kbar :=
  Ioo_subset_Ioc_self (I.policy_mem_Ioo hk)

/-- **Interiority on all of `K` is impossible** under `InteriorHyp`: `g(0) = 0` and consumption
at `k = 0` is `0` (route (iii): the interior statements are made on `(0, k̄]`). -/
theorem InteriorHyp.not_interior_zero {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar) :
    plannerPolicy I.planner 0 = 0 ∧ f 0 - plannerPolicy I.planner 0 = 0 ∧
      ¬ ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy I.planner k := by
  have h0 := (I.planner.plannerPolicy_zero I.f_zero).1
  refine ⟨h0, by rw [h0, I.f_zero, sub_zero], fun h => ?_⟩
  have := h 0 ⟨le_rfl, I.planner.kbar_nonneg⟩
  rw [h0] at this
  exact lt_irrefl _ this

/-- **The planner's Euler equation on `(0, k̄]`** under `InteriorHyp`, with `U` differentiable on
`(0, ∞)` and `f` on `(0, k̄]`:
`U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]`. -/
theorem InteriorHyp.planner_euler_interior {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k) {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    deriv U (f k - plannerPolicy I.planner k) = b * deriv f (plannerPolicy I.planner k) *
      deriv U (f (plannerPolicy I.planner k) -
        plannerPolicy I.planner (plannerPolicy I.planner k)) := by
  have hi := I.policy_interior hk
  have hgk := I.policy_mapsTo hk
  have hi2 := I.policy_interior hgk
  exact I.planner.planner_euler (Ioc_subset_Icc_self hk) hi.1 hi.2 hi2.2
    (hUd _ (sub_pos.2 hi.2)) (hUd _ (sub_pos.2 hi2.2)) (hfd _ hgk)

/-- **The bound behind the transversality condition.** For `k ∈ (0, k̄]`,
`f′(k) U′[f(k) − g(k)] k ≥ 0`, and for `k < k̄` it is at most `2 ‖v‖`: by the envelope
condition it is `v′(k) k`, and `v′(k) k ≤ v(k) − v(0)` by concavity of `v`. No bound on `U′`
near `0` is used. -/
theorem InteriorHyp.tvc_bound {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k)
    {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    0 ≤ deriv f k * deriv U (f k - plannerPolicy I.planner k) * k ∧
      (k < kbar → deriv f k * deriv U (f k - plannerPolicy I.planner k) * k ≤
        2 * ‖plannerValue I.planner‖) := by
  set P := I.planner with hP
  have hi := I.policy_interior hk
  refine ⟨mul_nonneg (mul_nonneg (hf' k hk) (P.deriv_U_nonneg (sub_pos.2 hi.2))) hk.1.le,
    fun hkb => ?_⟩
  have hkI : k ∈ Ioo 0 kbar := ⟨hk.1, hkb⟩
  have henv := P.planner_envelope hkI hi.2 (hUd _ (sub_pos.2 hi.2)) (hfd k hk)
  have hsl := P.plannerValue_concave.le_slope_of_hasDerivAt
    (⟨le_rfl, P.kbar_nonneg⟩ : (0 : ℝ) ∈ Icc 0 kbar) (Ioc_subset_Icc_self hk) hk.1 henv
  rw [slope_def_field, sub_zero, le_div_iff₀ hk.1] at hsl
  have h1 := abs_le.1 (by rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k :
    |plannerValue P k| ≤ ‖plannerValue P‖)
  have h2 := abs_le.1 (by rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm 0 :
    |plannerValue P 0| ≤ ‖plannerValue P‖)
  linarith

/-- **Transversality for the constructed policy** under `InteriorHyp`: for every `β′ ∈ [0, 1)`,
constant `a` and `k ∈ (0, k̄]`, `β′ᵗ (a f′(k_t)) U′(c_t) k_t → 0` along `k_t = gᵗ(k)`. This
replaces the continuity of `U′` on `[0, k̄]` used by `PlannerHyp.planner_euler_tvc`, which fails
when `U′(0+) = ∞`. -/
theorem InteriorHyp.planner_tvc {U f : ℝ → ℝ} {b kbar : ℝ} (I : InteriorHyp U f b kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k)
    (β' a : ℝ) (hβ0 : 0 ≤ β') (hβ1 : β' < 1) {k : ℝ} (hk : k ∈ Ioc 0 kbar) :
    Tendsto (fun t => β' ^ t * (a * deriv f ((plannerPolicy I.planner)^[t] k)) *
      deriv U (f ((plannerPolicy I.planner)^[t] k) -
        plannerPolicy I.planner ((plannerPolicy I.planner)^[t] k)) *
          (plannerPolicy I.planner)^[t] k) atTop (𝓝 0) := by
  set g := plannerPolicy I.planner with hg
  set Z : ℝ → ℝ := fun k => deriv f k * deriv U (f k - g k) * k with hZ
  set Mv := ‖plannerValue I.planner‖ with hMv
  have hMv0 : 0 ≤ Mv := norm_nonneg _
  have hkt := iterate_mem (fun k hk => I.policy_mapsTo hk) hk
  have hZb : ∀ k ∈ Ioc 0 kbar, |Z k| ≤ 2 * Mv + |Z kbar| := by
    intro k hk
    obtain ⟨h0, h1⟩ := I.tvc_bound hUd hfd hf' hk
    rcases lt_or_eq_of_le hk.2 with hlt | heq
    · rw [abs_of_nonneg h0]
      have := h1 hlt
      have := abs_nonneg (Z kbar)
      linarith
    · rw [heq]
      linarith
  refine (tvc_of_bounded (M := |a| * (2 * Mv + |Z kbar|)) hβ0 hβ1
    (z := fun t => a * Z (g^[t] k)) fun t => ?_).congr fun t => by simp only [hZ]; ring
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hZb _ (hkt t)) (abs_nonneg a)

/-- **Exercise 18.1 with the planner constructed and interior** (pp. 543–544). Let
`I : InteriorHyp U f β k̄`, `U` differentiable on `(0, ∞)` and bounded by `B₀` on `[0, ∞)`, `f`
concave on `[0, ∞)`, differentiable with `f′ ≥ 0` on `(0, k̄]`. Then:
(0) the constructed policy `g` is interior on `(0, k̄]`;
(i) `v` solves (1) on `K`, `g` is continuous on `K` and the unique maximiser in (1);
(ii) `g` satisfies the Euler equation on `(0, k̄]`;
(iii) (2) has a bounded solution `V` on `[0, ∞) × (0, k̄]`, unique among bounded solutions, with
`V(k, k; g) = v(k)`, the maximal value of the planner's problem, and `G(k, k; g) = g(k)`;
(iv) on `(0, k̄)`, `V₁(k, k; g) = v′(k) = f′(k) U′[f(k) − g(k)]`.
Compared with `ex_18_1_constructed`, interiority is proved, and `U` need not be differentiable at
`0` and `U′`, `f′` need not be continuous; the aggregate state space is `(0, k̄]`, since `k = 0` is
degenerate (`InteriorHyp.not_interior_zero`). -/
theorem ex_18_1_interior {U f : ℝ → ℝ} {β B₀ kbar : ℝ} (I : InteriorHyp U f β kbar)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Ioc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f β kbar (plannerValue I.planner) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerPolicy I.planner k ∈ Icc 0 (f k) ∧ ∀ y ∈ Icc 0 (f k),
        U (f k - y) + β * plannerValue I.planner y = plannerValue I.planner k ↔
          y = plannerPolicy I.planner k) ∧
      (∀ k ∈ Ioc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        β * deriv U (f (plannerPolicy I.planner k) -
          plannerPolicy I.planner (plannerPolicy I.planner k)) *
            deriv f (plannerPolicy I.planner k)) ∧
      ∃ V : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |V x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V β
          (Ioc 0 kbar) ∧
        (∀ V' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |V' x k| ≤ M') →
          SolvesBellman U (fun k => f k - k * deriv f k) (deriv f) (plannerPolicy I.planner) V'
            β (Ioc 0 kbar) → ∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, V' x k = V x k) ∧
        (∀ k ∈ Ioc 0 kbar, V k k = plannerValue I.planner k ∧
          IsGreatest (plannerValues U f β k) (V k k) ∧
          ∀ y ∈ feasY (fun k => f k - k * deriv f k) (deriv f) k k,
            (U (f k + (k - k) * deriv f k - y) + β * V y (plannerPolicy I.planner k) = V k k ↔
              y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => V x k) (deriv (plannerValue I.planner) k) k ∧
          HasDerivAt (plannerValue I.planner)
            (deriv f k * deriv U (f k - plannerPolicy I.planner k)) k := by
  set P := I.planner with hP
  set g := plannerPolicy P with hg
  set K := Ioc 0 kbar with hKdef
  have hβ0 := I.b_pos
  have hint : ∀ k ∈ K, 0 < g k ∧ g k < f k := fun k hk => I.policy_interior hk
  have hgK : ∀ k ∈ K, g k ∈ K := fun k hk => I.policy_mapsTo hk
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1.le
  have hc : ∀ k ∈ K, 0 ≤ f k - g k := fun k hk => (sub_pos.2 (hint k hk).2).le
  have hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k := by
    intro k hk
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1.le (hfd k hk)
    rw [I.f_zero] at this
    linarith
  have hUdK : ∀ k ∈ K, DifferentiableAt ℝ U (f k - g k) := fun k hk =>
    hUd _ (sub_pos.2 (hint k hk).2)
  have hU'K : ∀ k ∈ K, 0 ≤ deriv U (f k - g k) := fun k hk =>
    P.deriv_U_nonneg (sub_pos.2 (hint k hk).2)
  have heul' : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k) := fun k hk => by
    rw [I.planner_euler_interior hUd hfd hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0) := fun k hk =>
    (I.planner_tvc hUd hfd hf' β 1 hβ0.le P.b_lt_one hk).congr fun t => by ring
  obtain ⟨V, M, hVb, hsol, huniq, hall⟩ := ex_18_1_full_pathwise P.U_strictConcave P.U_mono hβ0
    P.b_lt_one hUdK hU'K hUb hf hgK hK0 hfd hf' hw hc heul' htvc'
  have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
    rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
  have hpol : ∀ k ∈ K, plannerValue P k = U (f k - g k) + β * plannerValue P (g k) :=
    fun k hk => (P.plannerPolicy_spec (Ioc_subset_Icc_self hk)).2.2
  have hdp := ex_18_1_dp_pathwise P.U_strictConcave hβ0 P.b_lt_one hUdK hU'K hUb hgK hK0 hf' hw
    hc heul' htvc' hvb hpol hVb hsol
  refine ⟨hint, P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨(P.plannerPolicy_spec hk).1, fun y hy => P.plannerPolicy_unique hk hy⟩, heul',
    V, M, hVb, hsol, huniq, fun k hk => ⟨(hdp k hk).1, (hall k hk).1, (hall k hk).2⟩,
    fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Ioc_self hk
  have hv' := P.planner_envelope hk (hint k hkK).2 (hUdK k hkK) (hfd k hkK)
  refine ⟨?_, hv'⟩
  rw [hv'.deriv]
  have hopt := ((hall k hkK).2 (g k) ⟨(hgK k hkK).1.le, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : (fun k => f k - k * deriv f k) k + deriv f k * k - g k = f k - g k := by
    simp only; ring
  have e' : f k + (k - k) * deriv f k - g k = f k - g k := by ring
  rw [e'] at hopt
  exact bellman_envelope hβ0.le P.b_lt_one P.U_strictConcave.concaveOn hUb hVb hgK hw hf' hsol
    hk.1 hkK (hgK k hkK).1.le (by rw [e]; exact sub_pos.2 (hint k hkK).2) (by rw [e]; exact hopt)
    (by rw [e]; exact (hUdK k hkK).hasDerivAt)

/-- **The indirect equilibrium with the pseudo-planner constructed and interior** (p. 546). Tax
`θ ∈ [0, 1)` on capital income, rebated; `β < 1`; `I : InteriorHyp U f ((1 − θ)β) k̄`; `U`, `f`
as in `ex_18_1_interior`. Then: (0) `ĥ` is interior on `(0, k̄]`; (i) `w` solves (8) on `K`, `ĥ` is
continuous, and on `(0, k̄]` `w(k)` is the value of the path of `ĥ` in the pseudo-economy, the
maximal value of its sequence problem; (ii) (9) `U′[f(k) − ĥ(k)] = β̂ w′(ĥ(k))` on `(0, k̄]` and
(10) `w′(k) = f′(k) U′[f(k) − ĥ(k)]` on `(0, k̄)`; (iii) (3) with `h = ĥ` has a bounded solution
`W` on `[0, ∞) × (0, k̄]`, unique among bounded solutions, `W(k, k; ĥ)` is the value of following
`ĥ`, and `H(k, k; ĥ) = ĥ(k)` is the unique optimal choice (a recursive competitive equilibrium);
(iv) `φ(k) = W₁(k, k; ĥ) = (1 − θ) w′(k)` on `(0, k̄)`. Interiority is not assumed, unlike
`indirect_equilibrium_constructed`. -/
theorem indirect_equilibrium_interior {U f : ℝ → ℝ} {β θ B₀ kbar : ℝ}
    (I : InteriorHyp U f ((1 - θ) * β) kbar) (hβ1 : β < 1) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (hUd : ∀ c, 0 < c → DifferentiableAt ℝ U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Ioc 0 kbar, DifferentiableAt ℝ f k)
    (hf' : ∀ k ∈ Ioc 0 kbar, 0 ≤ deriv f k) :
    (∀ k ∈ Ioc 0 kbar, 0 < plannerPolicy I.planner k ∧ plannerPolicy I.planner k < f k) ∧
      SolvesPlanner U f ((1 - θ) * β) kbar (plannerValue I.planner) ∧
      ContinuousOn (plannerPolicy I.planner) (Icc 0 kbar) ∧
      (∀ k ∈ Ioc 0 kbar,
        plannerValue I.planner k = pathValue U f (plannerPolicy I.planner) ((1 - θ) * β) k ∧
          IsGreatest (plannerValues U f ((1 - θ) * β) k) (plannerValue I.planner k)) ∧
      (∀ k ∈ Ioc 0 kbar, deriv U (f k - plannerPolicy I.planner k) =
        (1 - θ) * β * deriv (plannerValue I.planner) (plannerPolicy I.planner k)) ∧
      (∀ k ∈ Ioo 0 kbar, HasDerivAt (plannerValue I.planner)
        (deriv f k * deriv U (f k - plannerPolicy I.planner k)) k) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |W x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W β (Ioc 0 kbar) ∧
        (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, |W' x k| ≤ M') →
          SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
            (fun k => (1 - θ) * deriv f k) (plannerPolicy I.planner) W' β (Ioc 0 kbar) →
            ∀ x, 0 ≤ x → ∀ k ∈ Ioc 0 kbar, W' x k = W x k) ∧
        (∀ k ∈ Ioc 0 kbar, W k k = pathValue U f (plannerPolicy I.planner) β k ∧
          ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
            (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (plannerPolicy I.planner k) =
              W k k ↔ y = plannerPolicy I.planner k)) ∧
        ∀ k ∈ Ioo 0 kbar,
          HasDerivAt (fun x => W x k) ((1 - θ) * deriv (plannerValue I.planner) k) k := by
  set P := I.planner with hP
  set h := plannerPolicy P with hh
  set K := Ioc 0 kbar with hKdef
  have hβ0 : 0 < β := by
    have := I.b_pos
    by_contra hb
    push Not at hb
    have : (1 - θ) * β ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hb
    linarith
  have hint : ∀ k ∈ K, 0 < h k ∧ h k < f k := fun k hk => I.policy_interior hk
  have hhK : ∀ k ∈ K, h k ∈ K := fun k hk => I.policy_mapsTo hk
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1.le
  have hc : ∀ k ∈ K, 0 ≤ f k - h k := fun k hk => (sub_pos.2 (hint k hk).2).le
  have hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k := by
    intro k hk
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1.le (hfd k hk)
    rw [I.f_zero] at this
    have := mul_nonneg (mul_nonneg hθ0 hk.1.le) (hf' k hk)
    nlinarith
  have hUdK : ∀ k ∈ K, DifferentiableAt ℝ U (f k - h k) := fun k hk =>
    hUd _ (sub_pos.2 (hint k hk).2)
  have hU'K : ∀ k ∈ K, 0 ≤ deriv U (f k - h k) := fun k hk =>
    P.deriv_U_nonneg (sub_pos.2 (hint k hk).2)
  have heul' : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k) := fun k hk => by
    rw [I.planner_euler_interior hUd hfd hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0) := fun k hk =>
    I.planner_tvc hUd hfd hf' β (1 - θ) hβ0.le hβ1 hk
  obtain ⟨W, M, hWb, hsol, huniq, hall⟩ := indirect_equilibrium_full_pathwise P.U_strictConcave
    P.U_mono hβ0 hβ1 hθ0 hθ hUdK hU'K hUb hf hhK hK0 hfd hf' hw hc heul' htvc'
  -- the envelope condition (10) for `w`
  have h10 : ∀ k ∈ Ioo 0 kbar,
      HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - h k)) k := fun k hk =>
    P.planner_envelope hk (hint k (Ioo_subset_Ioc_self hk)).2 (hUdK k (Ioo_subset_Ioc_self hk))
      (hfd k (Ioo_subset_Ioc_self hk))
  -- the first-order condition (9)
  have h9 : ∀ k ∈ K, deriv U (f k - h k) = (1 - θ) * β * deriv (plannerValue P) (h k) := by
    intro k hk
    exact P.planner_foc (Ioc_subset_Icc_self hk) (hint k hk).1 (hint k hk).2 (hUdK k hk)
      (h10 _ (I.policy_mem_Ioo hk)).differentiableAt
  -- `w` is the value of the path of `ĥ`
  have hval : ∀ k ∈ K, plannerValue P k = pathValue U f h ((1 - θ) * β) k := by
    intro k hk
    have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
      rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
    have hs := policyValue_hasSum P.b_nonneg P.b_lt_one hhK hvb (fun k hk => hUb _ (hc k hk))
      (fun k hk => (P.plannerPolicy_spec (Ioc_subset_Icc_self hk)).2.2) hk
    exact hs.tsum_eq.symm
  refine ⟨hint, P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨hval k hk, (hval k hk) ▸ (hall k hk).1⟩, h9, h10, W, M, hWb, hsol, huniq,
    fun k hk => ⟨(hall k hk).2.1, (hall k hk).2.2⟩, fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Ioc_self hk
  have hopt := ((hall k hkK).2.2 (h k) ⟨(hhK k hkK).1.le, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : f k + (1 - θ) * (k - k) * deriv f k - h k = f k - h k := by ring
  obtain ⟨h5, -⟩ := eq_18_1_4_5 hβ0.le hβ1 hθ P.U_strictConcave.concaveOn hUb hhK hf' hw hWb hsol
    hk.1 hkK (hint k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) hopt
    (by rw [e]; exact hUdK k hkK)
  rw [(h10 k hk).deriv]
  rw [e] at h5
  convert h5 using 1
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions
