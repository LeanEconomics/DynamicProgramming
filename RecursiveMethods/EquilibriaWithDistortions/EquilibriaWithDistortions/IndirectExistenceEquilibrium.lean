/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.IndirectExistence

/-!
# Exercise 18.1 and the indirect equilibrium with the planner constructed

SLP §18.1, pp. 543–546. `ex_18_1_full` and `indirect_equilibrium_full` (in `IndirectBellman`)
take the planner's policy `g` (resp. the pseudo-planner's `ĥ`) as an input satisfying the Euler
equation and the transversality condition. Here `g` and `ĥ` are the policies constructed in
`IndirectExistence` from the functional equations (1) and (8), and those hypotheses are
discharged, on `K = [0, k̄]`, for `U` bounded and `C¹`, `f` concave and `C¹` with `0 ≤ f ≤ k̄`
on `K`, and an interior policy (`0 < g(k) < f(k)` on `K`, as in SLP Theorem 4.11).

* `plannerHyp_of_differentiable`: the hypotheses `PlannerHyp` from differentiability of `U` with
  `U′ ≥ 0` and of `f`.
* `planner_euler_tvc`: the constructed policy satisfies the Euler equation everywhere on `K` and
  the transversality condition `bᵗ U′(c_t) f′(k_t) k_t → 0` (bounded paths), and also the
  individual's transversality condition with any discount factor in `[0, 1)`.
* **Exercise 18.1 with the planner constructed** (`ex_18_1_constructed`): the planner's value `v`
  solves (1), its policy `g` is continuous and the unique maximiser, `g` satisfies the Euler
  equation; the bounded solution `V` of (2) exists and is unique, `V(k, k; g) = v(k)`, which is
  the maximal value of the planner's sequence problem; `G(k, k; g) = g(k)`; and
  `V₁(k, k; g) = v′(k)` on `(0, k̄)`.
* **The indirect equilibrium with the pseudo-planner constructed**
  (`indirect_equilibrium_constructed`, p. 546): `w` solves (8) and is the value of `ĥ` in the
  pseudo-economy, (9) `U′[f(k) − ĥ(k)] = β̂ w′(ĥ(k))` on `K` and (10)
  `w′(k) = f′(k) U′[f(k) − ĥ(k)]` on `(0, k̄)` hold, the bounded solution `W` of (3) exists and is
  unique, `H(k, k; ĥ) = ĥ(k)` (a recursive competitive equilibrium), and the book's identification
  `φ(k) = W₁(k, k; ĥ) = (1 − θ) w′(k)` holds on `(0, k̄)`.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Filter Topology Set

/-- **`PlannerHyp` from differentiability.** If `0 ≤ b < 1`, `0 ≤ k̄`, `U` is strictly concave and
differentiable on `[0, ∞)` with `U′ ≥ 0`, and `f` is concave on `[0, ∞)`, differentiable on
`K = [0, k̄]` with `0 ≤ f ≤ k̄` there, then `PlannerHyp U f b k̄` holds. -/
theorem plannerHyp_of_differentiable {U f : ℝ → ℝ} {b kbar : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hkbar : 0 ≤ kbar) (hU : StrictConcaveOn ℝ (Ici 0) U)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c)
    (hf : ConcaveOn ℝ (Ici 0) f) (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k)
    (hf0 : ∀ k ∈ Icc 0 kbar, 0 ≤ f k) (hfle : ∀ k ∈ Icc 0 kbar, f k ≤ kbar) :
    PlannerHyp U f b kbar where
  b_nonneg := hb0
  b_lt_one := hb1
  kbar_nonneg := hkbar
  U_cont := fun c hc => (hUd c hc).continuousAt.continuousWithinAt
  U_mono := monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun c hc => (hUd c hc).continuousAt.continuousWithinAt)
      (fun c hc => (hUd c (interior_subset hc)).differentiableWithinAt)
      fun c hc => hU' c (interior_subset hc)
  U_strictConcave := hU
  f_cont := fun k hk => (hfd k hk).continuousAt.continuousWithinAt
  f_concave := hf.subset Icc_subset_Ici_self (convex_Icc 0 kbar)
  f_nonneg := hf0
  f_le := hfle

/-- **Euler equation and transversality for the constructed policy.** Let `P : PlannerHyp U f b k̄`,
`U` differentiable on `[0, ∞)` with `U′` continuous on `[0, k̄]`, `f` differentiable on `K` with
`f′` continuous on `K`, and let the policy `g` be interior on `K` (`0 < g(k) < f(k)`). Then for
every `k ∈ K`: the Euler equation `U′[f(k) − g(k)] = b f′(g(k)) U′[f(g(k)) − g(g(k))]` holds, and
for every `β' ∈ [0, 1)` and constant `a`, `β'ᵗ (a f′(k_t)) U′(c_t) k_t → 0` along `k_t = gᵗ(k)`. -/
theorem PlannerHyp.planner_euler_tvc {U f : ℝ → ℝ} {b kbar : ℝ} (P : PlannerHyp U f b kbar)
    (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c) (hUc' : ContinuousOn (deriv U) (Icc 0 kbar))
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hfc' : ContinuousOn (deriv f) (Icc 0 kbar))
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k) :
    (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) = b * deriv f (plannerPolicy P k) *
      deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k))) ∧
    ∀ β' a : ℝ, 0 ≤ β' → β' < 1 → ∀ k ∈ Icc 0 kbar,
      Tendsto (fun t => β' ^ t * (a * deriv f ((plannerPolicy P)^[t] k)) *
        deriv U (f ((plannerPolicy P)^[t] k) - plannerPolicy P ((plannerPolicy P)^[t] k)) *
          (plannerPolicy P)^[t] k) atTop (𝓝 0) := by
  set g := plannerPolicy P with hg
  have hgK : ∀ k ∈ Icc 0 kbar, g k ∈ Icc 0 kbar := fun k hk => (P.plannerPolicy_mem hk).1
  refine ⟨fun k hk => ?_, fun β' a hβ0 hβ1 k hk => ?_⟩
  · have hgk := hgK k hk
    exact P.planner_euler hk (hint k hk).1 (hint k hk).2 (hint _ hgk).2
      (hUd _ (sub_pos.2 (hint k hk).2).le) (hUd _ (sub_pos.2 (hint _ hgk).2).le) (hfd _ hgk)
  · obtain ⟨MU, hMU⟩ := isCompact_Icc.exists_bound_of_continuousOn hUc'
    obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc'
    have hkt := iterate_mem hgK hk
    refine (tvc_of_bounded (M := |a| * Mf * MU * kbar) hβ0 hβ1 (z := fun t =>
      a * deriv f (g^[t] k) * deriv U (f (g^[t] k) - g (g^[t] k)) * g^[t] k)
      fun t => ?_).congr fun t => by ring
    have hk' := hkt t
    have hc : f (g^[t] k) - g (g^[t] k) ∈ Icc 0 kbar :=
      ⟨(P.plannerPolicy_mem hk').2, by linarith [(hgK _ hk').1, P.f_le _ hk']⟩
    have h1 := hMf _ hk'
    have h2 := hMU _ hc
    rw [Real.norm_eq_abs] at h1 h2
    have h3 : |g^[t] k| ≤ kbar := by rw [abs_of_nonneg hk'.1]; exact hk'.2
    simp only [abs_mul]
    have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans h1
    have hMU0 : 0 ≤ MU := (abs_nonneg _).trans h2
    gcongr

/-- **Exercise 18.1 with the planner constructed** (pp. 543–544). Let `0 < β < 1`, `0 ≤ k̄`;
`U` strictly concave, differentiable with `U′ ≥ 0` and bounded by `B₀` on `[0, ∞)`, with `U′`
continuous on `[0, k̄]`; `f` concave on `[0, ∞)`, differentiable on `K = [0, k̄]` with `f′ ≥ 0`
and `f′` continuous there, and `0 ≤ f ≤ k̄` on `K`. Let `v = plannerValue P` and
`g = plannerPolicy P` be the solution of the planner's functional equation (1) constructed in
`IndirectExistence`, and suppose `g` is interior on `K`. Then:
(i) `v` solves (1) on `K`, `g` is continuous on `K` and is the unique maximiser in (1);
(ii) `g` satisfies the planner's Euler equation on `K`;
(iii) the individual's functional equation (2) has a bounded solution `V`, unique among bounded
solutions, with `V(k, k; g) = v(k)`, the maximal value of the planner's sequence problem, and
`G(k, k; g) = g(k)` the unique optimal choice at `(k, k)`;
(iv) on `(0, k̄)`, `V₁(k, k; g) = v′(k) = f′(k) U′[f(k) − g(k)]`. -/
theorem ex_18_1_constructed {U f : ℝ → ℝ} {β B₀ kbar : ℝ} (P : PlannerHyp U f β kbar)
    (hβ0 : 0 < β) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hUc' : ContinuousOn (deriv U) (Icc 0 kbar)) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k)
    (hfc' : ContinuousOn (deriv f) (Icc 0 kbar))
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k) :
    SolvesPlanner U f β kbar (plannerValue P) ∧
      ContinuousOn (plannerPolicy P) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerPolicy P k ∈ Icc 0 (f k) ∧ ∀ y ∈ Icc 0 (f k),
        U (f k - y) + β * plannerValue P y = plannerValue P k ↔ y = plannerPolicy P k) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) =
        β * deriv U (f (plannerPolicy P k) - plannerPolicy P (plannerPolicy P k)) *
          deriv f (plannerPolicy P k)) ∧
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
  have hgK : ∀ k ∈ K, g k ∈ K := fun k hk => (P.plannerPolicy_mem hk).1
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1
  have hc : ∀ k ∈ K, 0 ≤ f k - g k := fun k hk => (P.plannerPolicy_mem hk).2
  have hw : ∀ k ∈ K, 0 ≤ f k - k * deriv f k := by
    intro k hk
    have h0K : (0 : ℝ) ∈ K := ⟨le_rfl, P.kbar_nonneg⟩
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1 (hfd k hk)
    have := P.f_nonneg 0 h0K
    nlinarith
  obtain ⟨heul, htvc⟩ := P.planner_euler_tvc hUd hUc' hfd hfc' hint
  have heul' : ∀ k ∈ K, deriv U (f k - g k) =
      β * deriv U (f (g k) - g (g k)) * deriv f (g k) := fun k hk => by
    rw [heul k hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * deriv U (f (g^[t] k) - g (g^[t] k)) *
      deriv f (g^[t] k) * g^[t] k) atTop (𝓝 0) := fun k hk =>
    (htvc β 1 hβ0.le P.b_lt_one k hk).congr fun t => by ring
  obtain ⟨V, M, hVb, hsol, huniq, hall⟩ := ex_18_1_full P.U_strictConcave hβ0 P.b_lt_one hUd hU'
    hUb hf hgK hK0 hfd hf' hw hc heul' htvc'
  have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
    rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
  have hpol : ∀ k ∈ K, plannerValue P k = U (f k - g k) + β * plannerValue P (g k) :=
    fun k hk => (P.plannerPolicy_spec hk).2.2
  have hdp := ex_18_1_dp P.U_strictConcave hβ0 P.b_lt_one hUd hU' hUb hgK hK0 hf' hw hc heul'
    htvc' hvb hpol hVb hsol
  refine ⟨P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨(P.plannerPolicy_spec hk).1, fun y hy => P.plannerPolicy_unique hk hy⟩, heul',
    V, M, hVb, hsol, huniq, fun k hk => ⟨(hdp k hk).1, (hall k hk).1, (hall k hk).2⟩,
    fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Icc_self hk
  have hv' := P.planner_envelope hk (hint k hkK).2 (hUd _ (hc k hkK)) (hfd k hkK)
  refine ⟨?_, hv'⟩
  rw [hv'.deriv]
  have hopt := ((hall k hkK).2 (g k) ⟨(hgK k hkK).1, by have := hc k hkK; simp only; linarith⟩).2
    rfl
  have e : (fun k => f k - k * deriv f k) k + deriv f k * k - g k = f k - g k := by
    simp only; ring
  have e' : f k + (k - k) * deriv f k - g k = f k - g k := by ring
  rw [e'] at hopt
  have := bellman_envelope hβ0.le P.b_lt_one P.U_strictConcave.concaveOn hUb hVb hgK hw hf' hsol
    hk.1 hkK (hgK k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) (by rw [e]; exact hopt)
    (by rw [e]; exact (hUd _ (hc k hkK)).hasDerivAt)
  exact this

/-- **The indirect equilibrium with the pseudo-planner constructed** (p. 546). Tax `θ ∈ [0, 1)`
on capital income, rebated; `0 < β < 1`. With the hypotheses of `ex_18_1_constructed` on `U`
and `f`, let `w = plannerValue P` and `ĥ = plannerPolicy P` solve the pseudo-economy's functional
equation (8) with discount factor `β̂ = (1 − θ)β`, and let `ĥ` be interior on `K`. Then:
(i) `w` solves (8) on `K`, `ĥ` is continuous on `K`, and `w(k)` is the value of the path of `ĥ`
in the pseudo-economy, which is the maximal value of the pseudo-planner's sequence problem;
(ii) (9) `U′[f(k) − ĥ(k)] = β̂ w′(ĥ(k))` on `K` and (10) `w′(k) = f′(k) U′[f(k) − ĥ(k)]` on
`(0, k̄)`;
(iii) the functional equation (3) with `h = ĥ` has a bounded solution `W`, unique among bounded
solutions, `W(k, k; ĥ)` is the individual's value of following `ĥ`, and `H(k, k; ĥ) = ĥ(k)` is
the unique optimal choice at `(k, k)` (a recursive competitive equilibrium);
(iv) `φ(k) = W₁(k, k; ĥ) = (1 − θ) w′(k)` on `(0, k̄)`, the book's identification. -/
theorem indirect_equilibrium_constructed {U f : ℝ → ℝ} {β θ B₀ kbar : ℝ}
    (P : PlannerHyp U f ((1 - θ) * β) kbar) (hβ0 : 0 < β) (hβ1 : β < 1) (hθ0 : 0 ≤ θ)
    (hθ : θ < 1) (hUd : ∀ c, 0 ≤ c → DifferentiableAt ℝ U c)
    (hU' : ∀ c, 0 ≤ c → 0 ≤ deriv U c) (hUb : ∀ c, 0 ≤ c → |U c| ≤ B₀)
    (hUc' : ContinuousOn (deriv U) (Icc 0 kbar)) (hf : ConcaveOn ℝ (Ici 0) f)
    (hfd : ∀ k ∈ Icc 0 kbar, DifferentiableAt ℝ f k) (hf' : ∀ k ∈ Icc 0 kbar, 0 ≤ deriv f k)
    (hfc' : ContinuousOn (deriv f) (Icc 0 kbar))
    (hint : ∀ k ∈ Icc 0 kbar, 0 < plannerPolicy P k ∧ plannerPolicy P k < f k) :
    SolvesPlanner U f ((1 - θ) * β) kbar (plannerValue P) ∧
      ContinuousOn (plannerPolicy P) (Icc 0 kbar) ∧
      (∀ k ∈ Icc 0 kbar, plannerValue P k = pathValue U f (plannerPolicy P) ((1 - θ) * β) k ∧
        IsGreatest (plannerValues U f ((1 - θ) * β) k) (plannerValue P k)) ∧
      (∀ k ∈ Icc 0 kbar, deriv U (f k - plannerPolicy P k) =
        (1 - θ) * β * deriv (plannerValue P) (plannerPolicy P k)) ∧
      (∀ k ∈ Ioo 0 kbar,
        HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - plannerPolicy P k)) k) ∧
      ∃ W : ℝ → ℝ → ℝ, ∃ M, (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W x k| ≤ M) ∧
        SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
          (fun k => (1 - θ) * deriv f k) (plannerPolicy P) W β (Icc 0 kbar) ∧
        (∀ W' : ℝ → ℝ → ℝ, ∀ M', (∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, |W' x k| ≤ M') →
          SolvesBellman U (fun k => f k - (1 - θ) * k * deriv f k)
            (fun k => (1 - θ) * deriv f k) (plannerPolicy P) W' β (Icc 0 kbar) →
            ∀ x, 0 ≤ x → ∀ k ∈ Icc 0 kbar, W' x k = W x k) ∧
        (∀ k ∈ Icc 0 kbar, W k k = pathValue U f (plannerPolicy P) β k ∧
          ∀ y ∈ feasY (fun k => f k - (1 - θ) * k * deriv f k) (fun k => (1 - θ) * deriv f k) k k,
            (U (f k + (1 - θ) * (k - k) * deriv f k - y) + β * W y (plannerPolicy P k) = W k k ↔
              y = plannerPolicy P k)) ∧
        ∀ k ∈ Ioo 0 kbar, HasDerivAt (fun x => W x k) ((1 - θ) * deriv (plannerValue P) k) k := by
  set h := plannerPolicy P with hh
  set K := Icc 0 kbar with hKdef
  have hhK : ∀ k ∈ K, h k ∈ K := fun k hk => (P.plannerPolicy_mem hk).1
  have hK0 : ∀ k ∈ K, 0 ≤ k := fun k hk => hk.1
  have hc : ∀ k ∈ K, 0 ≤ f k - h k := fun k hk => (P.plannerPolicy_mem hk).2
  have hw : ∀ k ∈ K, 0 ≤ f k - (1 - θ) * k * deriv f k := by
    intro k hk
    have h0K : (0 : ℝ) ∈ K := ⟨le_rfl, P.kbar_nonneg⟩
    have := concave_le_tangent hf (le_refl (0 : ℝ)) hk.1 (hfd k hk)
    have := P.f_nonneg 0 h0K
    have := mul_nonneg (mul_nonneg hθ0 hk.1) (hf' k hk)
    nlinarith
  obtain ⟨heul, htvc⟩ := P.planner_euler_tvc hUd hUc' hfd hfc' hint
  have heul' : ∀ k ∈ K, deriv U (f k - h k) =
      (1 - θ) * β * deriv U (f (h k) - h (h k)) * deriv f (h k) := fun k hk => by
    rw [heul k hk]; ring
  have htvc' : ∀ k ∈ K, Tendsto (fun t => β ^ t * ((1 - θ) * deriv f (h^[t] k)) *
      deriv U (f (h^[t] k) - h (h^[t] k)) * h^[t] k) atTop (𝓝 0) := fun k hk =>
    htvc β (1 - θ) hβ0.le hβ1 k hk
  obtain ⟨W, M, hWb, hsol, huniq, hall⟩ := indirect_equilibrium_full P.U_strictConcave hβ0 hβ1
    hθ0 hθ hUd hU' hUb hf hhK hK0 hfd hf' hw hc heul' htvc'
  -- the envelope condition (10) for `w`
  have h10 : ∀ k ∈ Ioo 0 kbar,
      HasDerivAt (plannerValue P) (deriv f k * deriv U (f k - h k)) k := fun k hk =>
    P.planner_envelope hk (hint k (Ioo_subset_Icc_self hk)).2
      (hUd _ (hc k (Ioo_subset_Icc_self hk))) (hfd k (Ioo_subset_Icc_self hk))
  -- the first-order condition (9)
  have h9 : ∀ k ∈ K, deriv U (f k - h k) = (1 - θ) * β * deriv (plannerValue P) (h k) := by
    intro k hk
    have hhI : h k ∈ Ioo 0 kbar := ⟨(hint k hk).1, (hint k hk).2.trans_le (P.f_le k hk)⟩
    exact P.planner_foc hk (hint k hk).1 (hint k hk).2 (hUd _ (hc k hk))
      (h10 _ hhI).differentiableAt
  -- `w` is the value of the path of `ĥ`
  have hval : ∀ k ∈ K, plannerValue P k = pathValue U f h ((1 - θ) * β) k := by
    intro k hk
    have hvb : ∀ k ∈ K, |plannerValue P k| ≤ ‖plannerValue P‖ := fun k _ => by
      rw [← Real.norm_eq_abs]; exact (plannerValue P).norm_coe_le_norm k
    have hs := policyValue_hasSum P.b_nonneg P.b_lt_one hhK hvb (fun k hk => hUb _ (hc k hk))
      (fun k hk => (P.plannerPolicy_spec hk).2.2) hk
    exact hs.tsum_eq.symm
  refine ⟨P.plannerValue_solves, P.plannerPolicy_continuousOn,
    fun k hk => ⟨hval k hk, (hval k hk) ▸ (hall k hk).1⟩, h9, h10, W, M, hWb, hsol, huniq,
    fun k hk => ⟨(hall k hk).2.1, (hall k hk).2.2⟩, fun k hk => ?_⟩
  have hkK : k ∈ K := Ioo_subset_Icc_self hk
  have hopt := ((hall k hkK).2.2 (h k) ⟨(hhK k hkK).1, by
    have := hc k hkK; simp only; linarith⟩).2 rfl
  have e : f k + (1 - θ) * (k - k) * deriv f k - h k = f k - h k := by ring
  obtain ⟨h5, -⟩ := eq_18_1_4_5 hβ0.le hβ1 hθ P.U_strictConcave.concaveOn hUb hhK hf' hw hWb hsol
    hk.1 hkK (hint k hkK).1 (by rw [e]; exact sub_pos.2 (hint k hkK).2) hopt
    (by rw [e]; exact hUd _ (hc k hkK))
  rw [(h10 k hk).deriv]
  rw [e] at h5
  convert h5 using 1
  ring

end StokeyLucasPrescott.EquilibriaWithDistortions
