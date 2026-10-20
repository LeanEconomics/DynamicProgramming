# Corrections and conventions

Places where a Lean statement differs from the book or the solutions manual (Irigoyen,
Rossi-Hansberg and Wright): a claim corrected, a hypothesis made explicit, a gap in a proof closed,
or a convention chosen. Every false claim below is refuted in Lean, by a counterexample or a proof
of inconsistency. The last section lists what is not proved.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Assumptions 18.1b and 18.2, pp. 547, 554 | `U` is `C²` on `[0, ∞)`, and `U′(c) → ∞` as `c → 0`. | Inconsistent: a `C¹` function on `[0, ∞)` has a finite one-sided derivative at `0`, which is the limit of `U′` (`assumption_18_2_contradiction`, `Assumption18_1.not_inada`). For §18.3, `U` and `f` are read as continuous on `[0, ∞)` and `C²` on `(0, ∞)` (`GlobalModel`); then `f′(0) < ∞` in Assumption 18.2 is no longer redundant. |
| p. 549 | From (6) and Assumption 18.1, `P(0) < 0`, `P(1) > 0` and `lim P = −∞`, so `P` has a root `λ* ∈ (0, 1)` and one above `1`. | The signs need `U″(c*) < 0` and `f″(k*) < 0`, which strict concavity does not give: `strictConcave_deriv2_zero_counterexample` is a `C²`, strictly increasing, strictly concave `U` with `U″ = 0` at a prescribed point. In the economy `f(k) = 9 − 8e^{−k}`, `β = θ = 1/2`, that `U` satisfies Assumption 18.1 and gives `P(0) = 0` (`note_18_2B_model_counterexample`). In general `U″(c*) = 0` gives `F₁* = F₃* = 0` and `P(λ) = F₂* λ` (`charPoly_degenerate_U`), and `f″(k*) = 0` gives `P(1) = 0` (`charPoly_degenerate_f`). Both inequalities are added (`LocalHyp`, `Assumption18_1.localHyp`), and the claims are proved under them (`LocalHyp.charPoly_roots`). |
| Exercise 18.4(a), p. 552 | `T` is monotone on `D_λ(I_ε)`. | False: for every `λ ∈ (0, 1]` and every admissible `ε`, two members `h′ ≤ h` of `D_λ(I_ε)` have `(Th)(k* + ε) < (Th′)(k* + ε)` (`ex_18_4a_counterexample`). In the economy `f(k) = 9 − 8e^{−k}`, `β = θ = 1/2`, `U(c) = 1 − e^{−c}`, which satisfies every hypothesis of the local analysis (`exModel_localHyp`), this happens for every `λ ∈ (λ*, 1)` and an `ε` as in Proposition 18.2 (`ex_18_4a_model_counterexample`). True on the nondecreasing members, which `T` maps into themselves (`ex_18_4a`, `ex_18_4a_mapsTo`); the manual restricts to these without saying so. |
| Exercise 18.4(b), p. 552 | The iterates of `T` from the constants `h_ ≡ k* − ε` and `h̄ ≡ k* + ε` converge to fixed points (by Theorem 17.7 on `D_λ(I_ε)`). | The constants are not in `D_λ(I_ε)`, since they miss `h(k*) = k*` (`ex_18_4b_const_not_mem`), so the manual's argument does not apply. Corrected (`ex_18_4b`): on the set `E` of nondecreasing `λ`-Lipschitz maps of `I_ε` into itself (`Elam`), with `ε` chosen so that also `m₁ + m₂ ≤ 1`, `T` maps `E` into itself and is monotone there; the iterates from `k* − ε` increase, those from `k* + ε` decrease, and both converge uniformly, at a geometric rate, to the fixed point of Proposition 18.3, which is the only fixed point in `E`. |
| (7) and Exercise 18.5, p. 556 | For each `h ∈ F` and `k ∈ K`, `(Th)(k)` is "the `y` solving" (7). | (7) can have no solution: if `ψ(ψ(0)) ≤ k*`, the member `h = min{ψ, k*}` of `F` makes the right side infinite on `[0, ψ(0))` at `k = 0` (`GlobalModel.ex_18_5_counterexample_of`); `modelE` (`U = √`) has `ψ(ψ(0)) ≤ k*` (`ex_18_5_counterexample`). `T` is defined as a crossing point, with `(Th)(k) = ψ(k)` when the right side is `+∞` on `[0, ψ(k))` (`eulerCross`, `GlobalModel.Tval`). Then `T` is well defined (`GlobalModel.ex_18_5_wellDefined`) and maps `F` into `F` (`GlobalModel.ex_18_5`). The convention adds no fixed points with zero consumption (`GlobalModel.IsInF.Tval_lt_psi_of_fixed`), so the fixed points are exactly the solutions of (1) (`GlobalModel.isFixedPt_iff_euler`). |
| p. 558 | `h̄(k) = min{ψ(k), k*}` for `k ≤ k*` and `min{k, ψ(k) − [ψ(k*) − k*]}` for `k > k*` is the maximal element of `F`. | `h̄` bounds `F` from above but is not in `F`: `ψ − h̄` is not nondecreasing (`GlobalModel.not_isInF_hbar`, `GlobalModel.hbar_not_mem_F`). The greatest element is `ū(k) = ψ(k) − max_{0 ≤ j ≤ k} [ψ(j) − min{ψ(j), max(j, k*)}]` (`GlobalModel.up`, `GlobalModel.isGreatest_up`), which is `min{ψ(k), k*}` for `k ≤ k*` (`GlobalModel.up_eq_of_le_kstar`) and `ψ(k) − max_{k* ≤ j ≤ k} [ψ(j) − j]` for `k ≥ k*` (`GlobalModel.up_eq_of_kstar_le`). Theorem 17.7 is applied from `ū` (`GlobalModel.least_greatest_equilibria`). |
| Exercise 18.8, p. 560 | With Assumptions 18.1d–e and 18.2 for each shock, (9) defines `T` on `F` and `T : F → F`. | False twice. (i) In `stochJ`, two states with technologies `modelHigh` (`ψ(0) = 10`) and `modelE` (`ψ(0) = 1/50`), moving to the high state for sure, each satisfying the assumptions with `U = √`, (9) has no solution for `h ≡ 0` at `k = 0` in the low state: the agent wants to save nothing (`ex_18_8_counterexample`, `stochJ_crossState_fails`; the mechanism is `StochModel.no_solution_of_crossState_fails`). (ii) `h = ψ` is in `F`, the right side of (9) is `+∞` for it, and (9) has no solution anywhere (`StochModel.no_solution_at_psi`). Corrected: in Kuhn–Tucker form `T` is well defined with no extra assumption (`StochModel.ex_18_8_spec_KT`) and maps `F` into `F` (`StochModel.ex_18_8`); under the cross-state condition `U′(ψ_i(0)) < β(1 − θ) Σ_j π_ij f′_j(0) U′(ψ_j(0))` (`StochModel.CrossState`), which for one shock is Assumption 18.1d, the zero-saving corner cannot occur: `(Th)_i(k)` is the unique solution of (9) with positive consumption, or (9) has no such solution, the right side is `+∞` on `[0, ψ_i(k))` and `(Th)_i(k) = ψ_i(k)` (`StochModel.ex_18_8_spec`). |
| p. 560 | In the stochastic case, existence of a fixed point "follows from Schauder's Theorem". | Schauder's theorem proves nothing here: with the convention of (7), `Tψ = ψ` (`StochModel.Ts_psi`), the fixed point with zero consumption forever. Every fixed point lies between the least fixed point and `ψ` (`StochModel.stoch_least_greatest`). A non-degenerate equilibrium is proved when some `h̄ ∈ F` with `h̄ < ψ` satisfies `T h̄ ≤ h̄` (`StochModel.lfp_equilibrium_of_super`), in particular when all states share one technology (`StochModel.exists_nondegenerate_equilibrium_identical`). |
| Exercise 18.2 (manual p. 285) | Substitute `β̂ = (1 − α − θ)/(1 − α)`. | The factor `β` is missing; with the manual's value the first-order condition fails whenever `β < 1` (`ex_18_2_manual_counterexample`). The book's `β̂ = β(1 − α − θ)/(1 − α)` is correct (`ex_18_2_foc`, `ex_18_2`). |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| (2), p. 544 | The domain and constraint set of the individual's problem are not stated; (2) is said to have a unique solution. | `x_t ≥ 0` and `c_t ≥ 0`, with `x₀` given (`IndivFeasible`, `feasY`). As sequence problems, values are sums assumed to exist (`HasSum`). The functional equations (2) and (3) are solved for `U` bounded on `[0, ∞)` (`exists_bellman_solution`, `bellman_unique`, `ex_18_1_full`, `indirect_equilibrium_full`); no continuity is needed. |
| Exercise 18.1, p. 544 | `g` is the planner's optimal policy. | `g` and the planner's value are inputs, with the planner's Euler equation and transversality condition as hypotheses (`ex_18_1`, `ex_18_1_full`), as in the manual. `f′(k_t) ≥ 0`, `U′ ≥ 0` and strict concavity of `U` are needed for sufficiency and uniqueness. |
| p. 546 and Exercise 18.2 (manual) | A solution of (6)–(7) gives an equilibrium; the manual says the transversality conditions "coincide". | The identification `h = ĥ` needs the individual's transversality condition, with his own discount factor: `βᵗ (1 − θ) f′(k_t) U′(c_t) k_t → 0`. It implies the pseudo-planner's condition with `β̂ᵗ` (`tvc_indiv_imp_pseudo`) but not conversely (`tvc_pseudo_not_imp_indiv_counterexample`). `indirect_equilibrium` and `ex_18_2` assume it; it holds along bounded paths (`tvc_of_bounded`). |
| Exercise 18.2, p. 547 | `θ ∈ (0, 1)`; nothing is said about `α`. | `α + θ < 1` is needed: otherwise `β̂ ≤ 0` (`ex_18_2_requires_sum_lt_one`). `ex_18_2` assumes `α < 1` and `α + θ ≤ 1`. |
| Proposition 18.1, pp. 548–549 | "Part (d) of Assumption 18.1 implies" a unique `k*`. | Uniqueness uses (d); existence uses (e) as well (`Assumption18_1.euler_kbar_lt`), and dividing by `U′` uses `U′ > 0` (`Assumption18_1.deriv_U_pos`). `prop_18_1` assumes that `g` maps `K` into itself, which the book takes as implicit in (4). |
| Propositions 18.2–18.4, pp. 550–554 | Assumption 18.1 and the `H` of (7). | The proofs use only `LocalHyp` (the hypotheses at `k*`, including `U″(c*) < 0` and `f″(k*) < 0`) and the properties of `H` collected in `LocalSolution`. They hold for every such `H`; `exists_localSolution` constructs one. |
| p. 553 | The fixed point is unique among functions with stationary point `k*` and a Lipschitz constant `λ ∈ (λ*, 1)`. | Unique in `D_λ(I_ε)` for the given `λ` and `ε` (`prop_18_3_fixedPoint`). |
| p. 548 | A competitive equilibrium is a `g` satisfying (4). | The Euler equation is taken as the definition, as in the book. For the local solutions of §18.2 the transversality condition holds because the paths are bounded (`tvc_of_bounded`). |
| Stochastic extension, pp. 558–559 | Assumptions 18.1d–e and 18.2 "modified in the obvious way to hold for each `ξ_j`". | Each state has a `GlobalModel` with common `β`, `θ` and `U` (`StochModel`). The equation form of Exercise 18.8 also needs `StochModel.CrossState` (see above). |
| Exercise 18.9, p. 560 | How must the assumptions or arguments be modified when `Ξ` is a closed bounded interval? | `Ξ` is any nonempty compact metric space with its Borel σ-algebra. Each shock has a `GlobalModel` with common `β`, `θ`, `U`, and `k̄(ξ) ≤ B`; `ψ(k, ξ)` and `f′(k, ξ)` are jointly continuous; the transition is Feller (`ContModel`). `F` is replaced by `F₊`: `h` jointly continuous with `0 ≤ h < ψ` and the monotonicity of (3) (`ContModel.IsInFc`). With a continuum, zero consumption on a null set need not make the integral in (9) infinite, so the Inada argument for a finite `Ξ` breaks; `F₊` excludes it. The equation form needs an integral cross-state condition (`ContModel.CrossState`, `ContModel.ex_18_9_spec`). |

## Gaps in proofs closed

| Where | Book | Lean |
| --- | --- | --- |
| Exercise 18.1 (manual pp. 284–285) | The individual's Euler equation and transversality condition hold along `x_t = k_t`, hence `x = k` is his optimum. | Uses sufficiency of these conditions for a problem whose return varies with `t`, a non-stationary Theorem 4.15, and uniqueness of the optimum. Both are proved (`euler_telescope`, `euler_partial_sum_le`, `euler_tvc_optimal`, `euler_tvc_unique`). |
| p. 544 | "The unique solution of (2)" exists, and `V(k, k; g) = v(k)`. | The Bellman operator is a `β`-contraction on bounded functions (`bellLp_contracting`), so the bounded solution exists and is unique (`exists_bellman_solution`, `bellman_unique`); it is the supremum of the sequence-problem values (`bellman_isLUB`); the planner's path is optimal in the planner's problem (`planner_optimal`), and `V(k, k; g)` is its value (`dp_diagonal`, `ex_18_1_full`). |
| (1), p. 543; (8)–(10), p. 546 | `v`, `g` and `w`, `ĥ` exist by Chapter 4. | For bounded `U` on `K = [0, k̄]` the Bellman operator is a contraction (`PlannerHyp.plannerOp_contracting`) preserving concavity (`PlannerHyp.plannerOp_concave`); its fixed point is concave with a unique, continuous maximiser (`PlannerHyp.plannerValue_concave`, `PlannerHyp.plannerPolicy_unique`, `PlannerHyp.plannerPolicy_continuousOn`), and the envelope, first-order and Euler conditions hold (`PlannerHyp.planner_envelope`, `PlannerHyp.planner_foc`, `PlannerHyp.planner_euler`). Used in `ex_18_1_constructed` and `indirect_equilibrium_constructed`. |
| (4)–(7), pp. 545–546 | The first-order and envelope conditions of (3), and hence (6)–(7). | `W(·, k)` is concave (`bellman_concave`), so the Benveniste–Scheinkman argument applies (`hasDerivAt_of_concave_of_le`); (4) is `bellman_foc`, (5) is `bellman_envelope`, and (6)–(7) follow on the diagonal (`bellman_diagonal`, `eq_18_1_6_7`, `eq_18_1_6_7_of_equilibrium`). |
| p. 551 | Schauder's theorem applies to `T` on `D_λ(I_ε)` once `T` is continuous. | `D_λ(I_ε)` is convex, bounded and totally bounded (`convex_DC`, `isBounded_DC`, `totallyBounded_DC`) and `T` is continuous on it (`continuousOn_TC`); Schauder gives a fixed point solving (4) with Proposition 18.2's own `ε` (`prop_18_2_schauder`), and with Proposition 18.3's `ε` it is the contraction fixed point (`prop_18_2_schauder_eq_contraction`). |
| Proof of Proposition 18.3, p. 552 | Choose `m̂₂ > H₂*` with `m̂₂(1 + λ*) < δ`; then `M₂(1 + λ) ≤ δ`. | Does not follow, since `λ > λ*` (`prop_18_3_printed_step_counterexample`). The fix replaces `λ*` by `λ`: `H₂*(1 + λ) < 1` (`LocalHyp.H2s_mul_lt_one`), used in `local_constants`. The book's `λ* < F₁*/F₃*` (p. 549) is the trivial half of `λ* < F₁*/F₃* < λ₂` (`charPoly_F1_div_F3`, `LocalHyp.one_lt_F1s_div_F3s`). |
| Exercise 18.3 (manual p. 286) | `\|h_n²(k) − h²(k)\| ≤ λ \|h_n(k) − h(k)\|`. | False: on `[−1, 1]`, `h(k) = −λk` and `h_c(k) = −λk + c·max(k, 0)` at `k = −1` (`ex_18_3_manual_counterexample`). The correct bound is `(1 + λ)‖h_n − h‖` (`Top_sub_le`), which gives Exercise 18.3 (`ex_18_3`). |
| p. 549 | The Implicit Function Theorem gives `H`. | `H` is constructed with the intermediate value theorem, with the Lipschitz bounds the proofs use (`exists_localSolution`); it is strictly differentiable with the book's partial derivatives and `C¹` near `(k*, k*)` (`LocalSolution.hasStrictFDerivAt`, `hasDerivAt_H_left`, `hasDerivAt_H_right`, `LocalSolution.contDiffAt`). |
| Proposition 18.4, p. 554 | "It follows immediately" that `Th` is strictly increasing for nondecreasing `h`. | Proved from the monotonicity of `F` in each argument (`Top_strictMonoOn`, `prop_18_4`). |
| Proof of Proposition 18.5, p. 557 | `\|ψ(k′) − ψ(k)\| ≤ A \|k′ − k\|` with `A = f′(0)`. | False: `ψ′ = (1 − θ) f′ − θ k f″`, and `−θ k f″` is not controlled by `f′(0)`; in `modelL`, `ψ(1) − ψ(9/10) > f′(0)/10` (`prop_18_5_bound_counterexample`). The proposition is true: `\|h(k′) − h(k)\| ≤ \|ψ(k′) − ψ(k)\|` and uniform continuity of `ψ` on `K` (`GlobalModel.prop_18_5`). |
| Exercise 18.5 (manual pp. 287–289) | `Th` is continuous "by the Implicit Function Theorem"; `RHS(y) → ∞` as `y → 0`. | The Implicit Function Theorem does not apply, since `h` is only continuous. Continuity follows from `0 ≤ (Th)(k₂) − (Th)(k₁) ≤ ψ(k₂) − ψ(k₁)` for `k₁ ≤ k₂` (`GlobalModel.IsInF.Tval_mono`, `GlobalModel.IsInF.Tval_sub_le`), which is Figure 18.2. The limit claim is false for `h = h_` in every model (`GlobalModel.manual_rhs_limit_counterexample`); only `RHS(0) > LHS(0)` is needed (`GlobalModel.IsInF.eulerBelow_zero`). |
| Exercise 18.6 (manual pp. 289–290) | Pointwise convergence from an implicit function `q` of `x = g(k)`. | The step evaluates `h` at `k` instead of at the unknown `y`, and uses the Implicit Function Theorem for a non-differentiable `h`. The proof here is a monotone crossing argument with `h` evaluated at `y` (`eventually_abs_eulerCross_sub_le`, `GlobalModel.eventually_abs_Tval_sub_le`); the uniform step is the manual's (`GlobalModel.ex_18_6`). |
| p. 558 | Proposition 18.5 and Exercise 18.6 verify Schauder's hypotheses. | `F` is compact by Arzelà–Ascoli (`totallyBounded_of_equicontinuous`, `GlobalModel.F_isCompact`), and Schauder's theorem for compact convex sets applies (`GlobalModel.exists_equilibrium`). |
| p. 560 | Equicontinuity, continuity, monotonicity and the extreme elements "parallel" the deterministic case. | Proved: `StochModel.Ts_equicontinuous`, `StochModel.Ts_tendsto_uniform` (pointwise convergence within `F` gives uniform convergence of `T`), `StochModel.ex_18_8_mono`, `StochModel.stoch_least_greatest`. The least fixed point is the limit of `Tⁿ0`, by monotone iteration carried out directly (`StochModel.tendsto_Tsit`, `StochModel.tendstoUniformly_Tsit`, `StochModel.Ts_lfp`). |

**Existence with finitely many shocks (p. 560).** Schauder's theorem on `F` gives only the
degenerate `ψ`, but an equilibrium with positive consumption exists for every finite set of
technologies and every transition matrix, with no cross-state, closeness or anchor condition. An
auxiliary planner with the concave technology `Φ_j(k) = θ f_j(0) + (1 − θ) f_j(k) ≤ ψ_j` has
positive consumption `c` and satisfies the Euler inequality with the after-tax return
(`StochModel.pc_pos`, `StochModel.pc_euler`); the set `{h ∈ F : ψ − h ≥ c}` contains `0` and is
invariant (`StochModel.IsInFs.Ts_floor`), so the least fixed point `lim Tⁿ0` keeps consumption at
least `c` (`StochModel.lfp_lt_psi`). It solves (9) in Kuhn–Tucker form
(`StochModel.exists_nondegenerate_equilibrium_KT`), and as an equation under the cross-state
condition (`StochModel.exists_nondegenerate_equilibrium`).
The same holds for a continuum of shocks (Exercise 18.9), for every compact `Ξ`, Feller `κ` and
technologies: the planner's consumption is bounded below by a positive constant on `K × Ξ`
(`ContModel.exists_pc_lb`), the floor is invariant (`ContModel.IsInFc.Tc_floor`), and the least
fixed point of `Tc` keeps consumption bounded away from zero (`ContModel.consFloor`,
`ContModel.ex_18_9_borel_existence`; in `F₊` under strong Feller, `ContModel.ex_18_9_existence`).
A sufficient steady-state condition for the floor is `ContModel.consFloor_of_uniformAnchor`.

**Interior planner policies (§18.1).** The corollaries of Exercise 18.1 and (8)–(10) assumed
`0 < g(k) < f(k)`. Interiority holds on `(0, k̄]` when `U′(0+) = ∞` and `f(0) = 0`
(`InteriorHyp.policy_interior`). With `f(0) > 0` and `U′(0+) = ∞` it can fail: under a constant
technology the planner never saves (*Lean*: `PlannerHyp.plannerPolicy_eq_zero_of_const`,
`inada_const_counterexample`). With a slope condition at `0` (`f(y) ≥ f(0) + m y`, `b m > 1`) it
holds on all of `K` (`PosOutputInadaHyp.policy_interior`). With `U′(0) = μ` finite it holds on
`K` under the slope condition and a Lipschitz condition on `f` near the bottom of `K`
(`FiniteMarginalHyp.policy_interior`, via `PlannerHyp.plannerValue_lipschitz`); both are needed
(*Lean*: `finite_const_counterexample`, `corner_counterexample`, where `g = f` on `[0, 1/1000]`).
Exercise 18.1 and the equilibrium then hold on `K` (`ex_18_1_on_K`, `indirect_equilibrium_on_K`),
with the transversality condition at `k = 0` from a positive minimum of consumption on `K`. The
bounded solution of (1), and of (8), is unique on `K` (`PlannerHyp.solvesPlanner_unique`,
`PlannerHyp.solvesPseudoPlanner_unique`); off `K` it is not determined
(`PlannerHyp.solvesPlanner_not_unique_off_K`).

## Conventions

* `U` and `f` are functions `ℝ → ℝ`. In Assumption 18.1 (`Assumption18_1`) they are `C²` on all of
  `ℝ`, with the book's properties imposed on `[0, ∞)`; a `C²` function on `[0, ∞)` extends to one
  on `ℝ`, so nothing is lost. In §18.3 (`GlobalModel`) they are continuous on `[0, ∞)` and `C²` on
  `(0, ∞)`, and the derivatives are fields `GlobalModel.U'` and `GlobalModel.f'`, with `f′(0)` the
  finite limit `A`.
* §18.1 poses the individual's and the planner's problems as sequence problems. The functional
  equations (2) and (3) are posed on `DPState`, the set `{(x, k) : x ≥ 0, k ∈ K}`, in the Banach
  space of bounded functions, with `A(k) + B(k) x − y` for consumption (`SolvesBellman`).
* Exercise 18.2 is read additively: capital income is taxed at `α + θ`, which gives the book's
  `β̂`. Under the sequential reading (the `θ`-tax levied on capital income net of the `α`-tax) the
  budget is `(1 − α) f(k) + (1 − α)(1 − θ)(x − k) f′(k)` (`ex_18_2_sequential_budget`) and the
  discount factor is `β(1 − θ)` (`ex_18_2_sequential_euler`), which differs from the book's when
  `α, θ > 0` (`ex_18_2_sequential_ne`).
* The operator (8) is defined on all functions (`Top`); only its values on `I_ε`, for `h` mapping
  `I_ε` into itself, are used. `C(I_ε)` is `C(Jint ks ε, ℝ)` with the sup metric, and functions on
  `I_ε` are extended to `ℝ` by `Set.IccExtend` (`extendC`, `TC`).
* (7) and (9) are read in the extended reals: the right side is `+∞` where some next-period
  consumption is zero (`GlobalModel.Zd`, `StochModel.Zs`), and `T` is the crossing point
  `eulerCross`, the supremum of the `y ∈ [0, ψ(k))` where the left side is below the right side.
* Equicontinuity is uniform equicontinuity, as on p. 520 (`UniformEquicontinuous`);
  `GlobalModel.prop_18_5'` is Proposition 18.5 in the book's `ε`–`δ` form. `F` is a subset of
  `Icc 0 kbar →ᵇ ℝ` (`GlobalModel.F`); `GlobalModel.IsInF` is the same condition on functions
  `ℝ → ℝ`.
* The book's "`ψ′(k) > (1 − θ) f′(k)` for all `k ∈ K`" (p. 555) is an equality at `k = 0`.
  Nothing here uses derivatives of `ψ`; the difference-quotient inequality
  `ψ(b) − ψ(a) > (1 − θ)(b − a) f′(b)` for `0 ≤ a < b` (`GlobalModel.psi_sub_gt`) replaces it.
* In the stochastic extension the shocks are a finite type `ι` with transition matrix
  `StochModel.π`, and `K = [0, B]` with `B = max_j k̄_j` (`StochModel.B_eq`, `StochModel.kbar_le`).
  Members of `F` are functions `ι → ℝ → ℝ`, continuous in `k` for each shock.
* The vertical-axis label `k̂` in Figure 18.1 is read as `k̄`, the level at which `ψ` meets the
  45° line (`GlobalModel.psi_kbar`). "Proposition 6" on p. 560 is read as Proposition 18.5;
  Chapter 18 has no Proposition 6.
* Figures 18.1 and 18.2 are not formalised as pictures; the facts they show are (see the
  [source map](source-map.md)). The concrete economies (`exF`, `exU`, `ratModel`, `modelE`,
  `modelL`, `modelHigh`, `stochJ`) are not in the book.

## Not proved

* **Continuity in the shock in Exercise 18.9 under a plain Feller transition.** The least fixed
  point exists for every `ContModel` and is Borel in `ξ` (`ContModel.ex_18_9_borel_existence`);
  continuity in `ξ`, so that it lies in `F₊`, is proved under the strong Feller property
  (`ContModel.ex_18_9_existence`). Under plain Feller the limit is only lower semicontinuous in
  `ξ`; whether it can fail to be continuous is open.
* **A model with `f″(k*) = 0`.** Only the algebraic consequence `P(1) = 0` is proved
  (`charPoly_degenerate_f`). The case `U″(c*) = 0` has a model satisfying Assumption 18.1
  (`note_18_2B_model_counterexample`).
* **Interiority at `k = 0` when `f(0) = 0` and `U′(0)` is finite.** No interiority result is
  proved; the Lipschitz condition of `FiniteMarginalHyp` conflicts with the slope condition near
  `0`, and corners there seem typical (`corner_counterexample` shows the mechanism). The slope and
  Lipschitz conditions are sufficient; each is shown necessary only by one counterexample.
* **Unbounded utility in the functional equations.** The dynamic-programming results of §18.1
  (`bellman_isLUB`, `exists_bellman_solution`, `ex_18_1_dp`, `ex_18_1_full`,
  `indirect_equilibrium_dp`, `indirect_equilibrium_full`) assume `U` bounded on `[0, ∞)`. The
  sequence-problem versions (`ex_18_1`, `indirect_equilibrium`, `ex_18_2`) do not.
* **The envelope condition at the boundary.** (5) and (10) are proved only at interior states
  (`x > 0` in `bellman_envelope`, `k ∈ (0, k̄)` in `PlannerHyp.planner_envelope`), and (4) only at
  an interior optimum (`bellman_foc`).
* **The chapter introduction and §18.4** (bibliographic notes) are not formalised.
