# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 18, pp. 542–560 (pp. 561–562 are back-matter). Equation numbers restart in each
section, as in the book. Lean names are relative to `StokeyLucasPrescott.EquilibriaWithDistortions`.
Where the Lean statement departs from the book, see [corrections](corrections.md).

## Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 542–543 | Overview: endogenous state variables; three methods (indirect, local, global) | Not formalised (overview) |

## §18.1 An indirect approach

| Source | Claim | Lean |
| --- | --- | --- |
| (1), p. 543 | The planner's functional equation `v(k) = max_y {U[f(k) − y] + β v(y)}` and its policy `g` | `policyValue_hasSum` (a bounded `v` satisfying (1) along `g` is the value of the path of `g`), `planner_optimal`, `plannerValues` (that path, with the Euler equation and transversality condition, is optimal). Existence, bounded `U`, `K = [0, k̄]`: `PlannerHyp`, `plannerOp`, `PlannerHyp.plannerOp_contracting`, `plannerValue`, `PlannerHyp.plannerValue_solves`, `PlannerHyp.plannerValue_concave`, `plannerPolicy`, `PlannerHyp.plannerPolicy_spec`, `PlannerHyp.plannerPolicy_unique`, `PlannerHyp.plannerPolicy_continuousOn`, `PlannerHyp.planner_foc`, `PlannerHyp.planner_envelope`, `PlannerHyp.planner_euler`, `PlannerHyp.planner_euler_tvc` |
| pp. 543–544 | With equal capital the planner's allocation is the competitive equilibrium (§16.1) | Not restated; Exercise 18.1 is the form used |
| (2), p. 544 | The individual's problem `V(x, k; g)` with policy `G(x, k; g)` | Sequence form: `IndivFeasible`, `consPath`, `indivValues`. Functional equation, bounded `U`: `DPState`, `feasY`, `SolvesBellman`, `bellOp`, `bellOp_abs_le`, `bellOp_sub_le`, `bellLp`, `bellLp_contracting`, `exists_bellman_solution`, `bellman_isLUB`, `bellman_unique` |
| p. 544, manual pp. 284–285 | Euler equation and transversality condition suffice for the individual's optimum (Theorem 4.15 for a time-varying return) | `concave_le_tangent`, `strictConcave_lt_tangent`, `euler_telescope`, `euler_partial_sum_le`, `euler_tvc_optimal`, `euler_tvc_strict`, `euler_tvc_gap`, `euler_tvc_unique`, `euler_tvc_isGreatest`, `tvc_of_bounded` |
| Exercise 18.1, p. 544 | `V(k, k; g) = v(k)` and `G(k, k; g) = g(k)` | `ex_18_1` (sequence problem), `dp_diagonal`, `ex_18_1_dp`, `ex_18_1_full` (functional equation, with existence), `ex_18_1_foc_envelope`; `v` and `g` constructed: `ex_18_1_constructed` (interior `g` assumed) |
| pp. 544–545 | Capital-income tax with lump-sum rebate: income `f(k) + (1 − θ)(x − k) f′(k)` | `budget_rebate` |
| (3), p. 545 | The taxed individual's problem `W(x, k; g)` | `SolvesBellman` with `A(k) = f(k) − (1 − θ) k f′(k)`, `B(k) = (1 − θ) f′(k)` |
| p. 545 | Recursive competitive equilibrium: `H(k, k; h) = h(k)` | The conclusion of `indirect_equilibrium_dp` and `indirect_equilibrium_full` |
| (4)–(5), p. 545 | First-order and envelope conditions for (3) | `hasDerivAt_of_concave_of_le` (Benveniste–Scheinkman), `bellman_concave`, `bellman_foc` (4), `bellman_envelope` (5), `eq_18_1_4_5`; interior optimum and `x > 0` assumed |
| (6)–(7), p. 546 | `U′[f(k) − h(k)] = β φ[h(k)]`, `φ(k) = (1 − θ) f′(k) U′[f(k) − h(k)]` | The conclusion of `pseudo_economy_solves_6_7`; from (4)–(5): `bellman_diagonal`, `eq_18_1_6_7`, `eq_18_1_6_7_of_equilibrium` |
| (8)–(10), p. 546 | The pseudo-economy with `β̂ = (1 − θ)β`; its first-order and envelope conditions | (9)–(10) are the hypotheses of `pseudo_economy_solves_6_7`; the pseudo-planner's problem with existence: `indirect_equilibrium_full`; `w` and `ĥ` constructed: `indirect_equilibrium_constructed` (interior `ĥ` assumed) |
| p. 546 | `φ = (1 − θ) w′`, `h = ĥ` solve (6)–(7) and give an equilibrium | `pseudo_economy_solves_6_7`, `indirect_equilibrium`, `tvc_indiv_imp_pseudo`, `tvc_pseudo_not_imp_indiv_counterexample`, `indirect_equilibrium_dp`, `indirect_equilibrium_full` |
| pp. 546–547 | Without a rebate there is no alternative to a direct attack | Not formalised (remark) |
| Exercise 18.2, p. 547 | Taxes `θ` on capital income (rebated) and `α` on all income (thrown away) act like `F = (1 − α) f` with `β̂ = β(1 − α − θ)/(1 − α)` | `ex_18_2_budget`, `ex_18_2_foc`, `ex_18_2`, `ex_18_2_requires_sum_lt_one`, `ex_18_2_manual_counterexample`, `ex_18_2_sequential_budget`, `ex_18_2_sequential_euler`, `ex_18_2_sequential_ne` |

## §18.2 A local approach based on first-order conditions

| Source | Claim | Lean |
| --- | --- | --- |
| p. 547 | After-tax income `ψ(k) = f(k) − θ k f′(k)` | `psi`, `continuous_psi`, `hasDerivAt_psi`, `dpsi`, `dpsi_star` |
| (1)–(2), p. 547 | Equilibrium conditions in `(g, φ)` | Enter through (3), which eliminates `φ` |
| Assumption 18.1, pp. 547–548 | (a) `β ∈ (0, 1)`; (b) `U`; (c) `θ ∈ (0, 1)`; (d) `f`, `f(0) > 0`, `lim f′ > 1/[β(1 − θ)]`; (e) `k̄` | `Assumption18_1`, `Assumption18_1.tendsto_deriv_f_zero` |
| p. 548 | Consequences of Assumption 18.1 | `Assumption18_1.deriv_U_pos`, `Assumption18_1.deriv_U_strictAnti`, `Assumption18_1.deriv_f_pos`, `Assumption18_1.deriv_f_strictAnti`, `Assumption18_1.psi_kbar`, `Assumption18_1.le_psi`, `Assumption18_1.psi_gt_mul`, `Assumption18_1.euler_kbar_lt` |
| (3)–(4), p. 548 | `F(x, y, z)`; an equilibrium is `g` with `F[k, g(k), g²(k)] = 0` | `Feq`, `Feq_diag` |
| Proposition 18.1, (5), pp. 548–549 | A continuous solution of (4) has exactly one fixed point, the `k*` with `β(1 − θ) f′(k*) = 1` | `Assumption18_1.exists_unique_kstar`, `prop_18_1` (with `brouwer`) |
| p. 549 | Restriction to functions with stationary point `k*` | Built into `Dlam` |
| (6a)–(6c), p. 549 | `F₁*`, `F₂*`, `F₃*` | `F1f`, `F2f`, `F3f`, `hasDerivAt_Feq_x`, `hasDerivAt_Feq_y`, `hasDerivAt_Feq_z`, `cstar`, `F1s`, `F2s`, `F3s`, `F1f_star`, `F2f_star`, `F3f_star` |
| p. 549 | `P(λ) = F₁* + F₂* λ + F₃* λ²`: `P(0) < 0`, `P(1) > 0`, roots `λ* ∈ (0, 1)` and `λ₂ > 1`; `P(F₁*/F₃*) > 0` | `charPoly`, `charDisc`, `charPoly_one`, `lamStar`, `lamTwo`, `LocalHyp`, `Assumption18_1.localHyp`, `LocalHyp.charPoly_zero_neg`, `LocalHyp.charPoly_one_pos`, `LocalHyp.charPoly_roots`, `LocalHyp.charPoly_pos`, `charPoly_F1_div_F3`, `LocalHyp.one_lt_F1s_div_F3s`; the degenerate cases `strictConcave_deriv2_zero_counterexample`, `charPoly_degenerate_U`, `charPoly_degenerate_f` |
| p. 549 | `F₂* > 0`, `H₁* = −F₁*/F₂* > 0`, `H₂* = −F₃*/F₂* > 0` | `LocalHyp.F1s_neg`, `LocalHyp.F2s_pos`, `LocalHyp.F3s_neg`, `LocalHyp.H1s_pos`, `LocalHyp.H2s_pos`, `LocalHyp.H_sum_lt_one`, `LocalHyp.H_lt_lam`, `LocalHyp.H2s_mul_lt_one` |
| (7), p. 549 | The Implicit Function Theorem gives a `C¹` `H` on `I × I` with `F[x, H(x, z), z] = 0`, `H(k*, k*) = k*` | `Jint`, `clampI`, `root_sep`, `root_exists`, `implicitRoot`, `LocalHyp.exists_cube`, `LocalSolution`, `exists_localSolution`; smoothness: `bivImplicit`, `eventuallyEq_bivImplicit`, `Hderiv`, `LocalSolution.hasStrictFDerivAt`, `LocalSolution.hasStrictFDerivAt_center`, `hasDerivAt_H_left`, `hasDerivAt_H_right`, `LocalSolution.contDiffAt`, `LocalSolution.eventually_contDiffAt` |
| (8), p. 550 | `(Th)(k) = H[k, h²(k)]`; its fixed points solve (4) | `Top`, `extendC`, `TC`, `extendC_TC`; (4) for the fixed point in `prop_18_3_fixedPoint` |
| p. 550 | `I_ε`, `D_λ(I_ε)`; members map `I_ε` into itself | `Jint`, `Dlam`, `Dlam_mapsTo`, `DC`, `mem_DC_iff`, `isClosed_DC` |
| Proposition 18.2, pp. 550–551 | For `λ ∈ (λ*, 1)` some `ε` has `T(D_λ(I_ε)) ⊆ D_λ(I_ε)` | `HBound`, `local_constants`, `Top_lipschitz`, `Top_mem_Dlam`, `prop_18_2` |
| p. 551 | Three routes: Schauder, Theorem 17.7, contraction | Schauder: `convex_DC`, `isBounded_DC`, `totallyBounded_DC`, `continuousOn_TC`, `localSchauder_fixedPoint_of_mapsTo`, `prop_18_2_schauder`, `prop_18_2_schauder_eq_contraction`. Theorem 17.7: Exercise 18.4. Contraction: Proposition 18.3 |
| Exercise 18.3, p. 551 | `T` is continuous on `D_λ(I_ε)` | `Top_sub_le`, `ex_18_3`, `ex_18_3_continuous`, `ex_18_3_manual_counterexample` |
| Exercise 18.4(a), p. 552 | `T` is monotone on `D_λ(I_ε)` | `ex184H`, `ex184H'`, `ex_18_4a_counterexample`, `ex_18_4a_model_counterexample`; corrected: `ex_18_4a`, `ex_18_4a_mapsTo` |
| Exercise 18.4(b), p. 552 | `Tⁿ` of the constants `k* ∓ ε` converge to fixed points | `ex_18_4b_const_not_mem`; corrected: `Elam`, `ex_18_4b` |
| Proposition 18.3, pp. 552–553 | For `λ ∈ (λ*, 1)` some `ε` makes `T` a contraction on `D_λ(I_ε)` | `TC_mapsTo`, `TC_dist_le`, `TC_contractingWith`, `prop_18_3`, `prop_18_3_contractingWith`, `prop_18_3_printed_step_counterexample` |
| p. 553 | A unique fixed point `g ∈ D_λ(I_ε)`, solving (4); `\|gᵗ(k) − k*\| ≤ λᵗ \|k − k*\|` | `eq_of_fixed`, `exists_fixedPoint_of_bounds`, `prop_18_3_fixedPoint` |
| Proposition 18.4, pp. 553–554 | The fixed point is strictly increasing | `Top_strictMonoOn`, `const_mem_DC`, `prop_18_4` |
| after p. 553 (not in the book) | `g′(k*) = λ*`, the stable root | `LocalHyp.lamStar_eq`, `hasDerivAt_fixedPoint_lamStar`, `prop_18_3_deriv` |
| (not in the book) | An economy satisfying Assumption 18.1 | `exF`, `exU`, `exU_admissible`, `psi_exF`, `exModel_assumption`, `exModel_localHyp`, `flatU`, `note_18_2B_model_counterexample` |

## §18.3 A global approach based on first-order conditions

| Source | Claim | Lean |
| --- | --- | --- |
| (1), p. 554 | The equilibrium condition, (4) written out | `GlobalModel.isFixedPt_iff_euler` |
| Assumption 18.2, p. 554 | `f′(0) = A < ∞` and `lim_{c→0} U′(c) = ∞` | `assumption_18_2_contradiction`, `Assumption18_1.not_inada`; read as `GlobalModel` |
| pp. 554–555 | `K = [0, k̄]`, `k*`, and the consequences of Assumptions 18.1–18.2 | `GlobalModel.exists_kstar`, `GlobalModel.kstar_unique`, `GlobalModel.kstar_mem`, `GlobalModel.f'_pos`, `GlobalModel.f'_strictAntiOn`, `GlobalModel.U'_pos`, `GlobalModel.U'_strictAntiOn`, `GlobalModel.isMarginalUtility`, `GlobalModel.psi_strictMonoOn`, `GlobalModel.psi_zero`, `GlobalModel.psi_kbar`, `GlobalModel.psi_le_kbar` |
| (2)–(6), p. 555 | The set `F` | `GlobalModel.IsInF`, `GlobalModel.F`, `GlobalModel.toBCF`, `GlobalModel.ext`, `GlobalModel.toBCF_mem_F` |
| p. 555 | `ψ′ > (1 − θ) f′`; `ψ′ > 1/β > 1` on `[0, k*]`; `ψ(k*) > k*` | `GlobalModel.psi_sub_gt`, `GlobalModel.sub_lt_psi_sub`, `GlobalModel.lt_psi_of_le_kstar` |
| Figure 18.1, pp. 555–556 | Every `h ∈ F` lies in the regions A and B | `GlobalModel.bnd`, `GlobalModel.IsInF.le_bnd`, `GlobalModel.IsInF.low_le`, `GlobalModel.IsInF.le_up` |
| p. 556 | `F` is nonempty, closed, bounded and convex | `GlobalModel.F_nonempty`, `GlobalModel.F_isClosed`, `GlobalModel.F_isBounded`, `GlobalModel.F_convex` |
| (7), p. 556 | `(Th)(k)` is the `y` solving `U′[ψ(k) − y] = β(1 − θ) f′(y) U′[ψ(y) − h(y)]` | `IsMarginalUtility`, `IsEulerRHS`, `eulerSet`, `eulerCross`, `GlobalModel.Zd`, `GlobalModel.Rd`, `GlobalModel.Tval`, `GlobalModel.T`, `GlobalModel.T_apply` |
| Exercise 18.5, p. 556 | `T` is well defined and `T : F → F` | `eulerCross_spec`, `eulerCross_unique`, `GlobalModel.IsInF.isEulerRHS`, `GlobalModel.IsInF.eulerBelow_zero`, `GlobalModel.IsInF.Tval_spec`, `GlobalModel.ex_18_5_wellDefined`, `GlobalModel.IsInF.le_Tval`, `GlobalModel.IsInF.Tval_le`, `GlobalModel.IsInF.isInF_Tval`, `GlobalModel.ex_18_5`; counterexamples: `GlobalModel.hE`, `GlobalModel.isInF_hE`, `GlobalModel.ex_18_5_counterexample_of`, `modelE`, `ex_18_5_counterexample`, `GlobalModel.manual_rhs_limit_counterexample` |
| Figure 18.2, p. 557 | The crossing point rises with `k`, by less than `ψ` does | `eulerCross_mono`, `eulerCross_le_add_sub`, `GlobalModel.IsInF.Tval_mono`, `GlobalModel.IsInF.Tval_sub_le`, `GlobalModel.IsInF.abs_Tval_sub_le` |
| Proposition 18.5, p. 557 | `F` is equicontinuous | `GlobalModel.IsInF.abs_sub_le`, `GlobalModel.prop_18_5`, `GlobalModel.prop_18_5'`, `modelL`, `prop_18_5_bound_counterexample` |
| Exercise 18.6, p. 558 | `T` is continuous | `RHSConvergesAt`, `eventually_abs_eulerCross_sub_le`, `GlobalModel.eventually_abs_Tval_sub_le`, `GlobalModel.ex_18_6` |
| p. 558 | By Schauder's theorem, `T` has a fixed point in `F` | `GlobalModel.T_equicontinuous`, `GlobalModel.F_isCompact` (with `totallyBounded_of_equicontinuous`), `GlobalModel.exists_equilibrium` (with `schauder`), `GlobalModel.IsInF.Tval_lt_psi_of_fixed`, `GlobalModel.isFixedPt_iff_euler` |
| Exercise 18.7, p. 558 | `T` is monotone | `eulerCross_mono_rhs`, `GlobalModel.ex_18_7` |
| p. 558 | The minimal element `h_` and maximal element `h̄` of `F` | `GlobalModel.low`, `GlobalModel.isInF_low`, `GlobalModel.isLeast_low`; `GlobalModel.hbar`, `GlobalModel.not_isInF_hbar`, `GlobalModel.hbar_not_mem_F`; the greatest element: `GlobalModel.runSup`, `GlobalModel.gap`, `GlobalModel.up`, `GlobalModel.isInF_up`, `GlobalModel.isGreatest_up`, `GlobalModel.up_eq_of_le_kstar`, `GlobalModel.up_eq_of_kstar_le` |
| p. 558 | `lim Tⁿh_`, `lim Tⁿh̄` are fixed points; if they agree, the fixed point is unique | `GlobalModel.monotone_iterate_low`, `GlobalModel.antitone_iterate_up`, `GlobalModel.least_greatest_equilibria` (with `corollary_17_7`), `GlobalModel.unique_equilibrium_of_tendsto` |
| (not in the book) | Models satisfying Assumptions 18.1–18.2 | `sqrt_inada`, `ratModel`, `ratTech_psi_sub`, `modelE`, `modelE_psi_psi_le`, `modelL`, `fL`, `psiL`, `kbarL` |

## §18.3 The stochastic extension

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 558–559 | Shocks `ξ_j` with transition matrix `Π`; Assumptions 18.1d–e and 18.2 for each `ξ_j`; `k̄ = max_j k̄_j`; `ψ(k, ξ_j)` | `StochModel`, `StochModel.B_eq`, `StochModel.kbar_le`, `StochModel.psi_le_B` |
| (8), p. 559 | An equilibrium `g : K × Ξ → K` | `StochModel.Zs`, `StochModel.Rs`; the conclusion of `StochModel.lfp_equilibrium_of_super` |
| p. 559 | `F ⊆ C(K × Ξ)`: `0 ≤ h_j ≤ ψ_j`, `h_j` and `ψ_j − h_j` nondecreasing | `StochModel.IsInFs`, `StochModel.isInFs_zero`, `StochModel.isInFs_psi` |
| (9), p. 559 | The operator `T` | `StochModel.Ts`, `StochModel.TsOp`, `StochModel.Ts_mem_Icc` |
| Exercise 18.8, p. 560 | `T` is well defined and `T : F → F` | `modelHigh`, `stochJ`, `stochJ_crossState_fails`, `ex_18_8_counterexample`, `StochModel.no_solution_of_crossState_fails`, `StochModel.Ts_psi`, `StochModel.no_solution_at_psi`; corrected: `StochModel.ex_18_8_spec_KT`, `StochModel.IsInFs.Ts_mono`, `StochModel.ex_18_8`, `StochModel.CrossState`, `StochModel.ex_18_8_spec` |
| p. 560 | Equicontinuity, as in "Proposition 6" (Proposition 18.5) | `StochModel.IsInFs.abs_sub_le`, `StochModel.IsInFs.abs_Ts_sub_le`, `StochModel.Ts_equicontinuous` |
| p. 560 | Continuity of `T`, as in Exercise 18.6 | `StochModel.rhsConvergesAt_of_tendsto`, `StochModel.Ts_tendsto`, `StochModel.Ts_tendsto_uniform` |
| p. 560 | Existence of a fixed point by Schauder's theorem | `StochModel.Ts_psi` (the degenerate fixed point `ψ`); non-degenerate: `StochModel.lfp_equilibrium_of_super`, `StochModel.identical_tech_fixed`, `StochModel.crossState_of_identical`, `StochModel.exists_nondegenerate_equilibrium_identical`. For different technologies: not proved |
| p. 560 | Monotonicity, as in Exercise 18.7 | `StochModel.ex_18_8_mono` |
| p. 560 | Minimal and maximal elements of `F` | `StochModel.Tsit`, `StochModel.Tsit_le_succ`, `StochModel.Tsit_le_of_super`, `StochModel.tendsto_Tsit`, `StochModel.tendstoUniformly_Tsit`, `StochModel.lfp`, `StochModel.isInFs_lfp`, `StochModel.Ts_lfp`, `StochModel.lfp_le_of_super`, `StochModel.stoch_least_greatest` |
| Exercise 18.9, p. 560 | Modify the assumptions or arguments for `Ξ` a closed bounded interval | `ContModel`, `ContModel.IsInFc`, `ContModel.G`, `ContModel.Rc`, `ContModel.Tc`, `ContModel.IsInFc.isEulerRHS`, `ContModel.ex_18_9_spec_KT`, `ContModel.CrossState`, `ContModel.ex_18_9_spec`, `ContModel.ex_18_9`, `ContModel.ex_18_9_mono`. A fixed point: not proved |

## §18.4 Bibliographic notes

| Source | Claim | Lean |
| --- | --- | --- |
| p. 560 | Sources: Becker (1985), Lucas and Stokey (1987), Coleman (1987), Bizer and Judd (1989), Blume (1982), Duffie et al. (1988) | Not formalised |

## Results from Chapter 17

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 17.3, p. 517 | Brouwer's fixed-point theorem | `no_C1_retraction`, `brouwer_closedBall`, `brouwer`, `theorem_17_3` (module `Brouwer`, carried) |
| Theorem 17.4, p. 520 | Schauder's theorem in `C(X)` | `schauder`, `schauder_closed`, `totallyBounded_of_equicontinuous`, `theorem_17_4` (carried) |
| Lemma 17.6, Theorem 17.7 and Corollary, pp. 526–529 | Fixed points of monotone operators | `lemma_17_6`, `theorem_17_7`, `corollary_17_7`, `corollary_17_7_unique` (carried) |
