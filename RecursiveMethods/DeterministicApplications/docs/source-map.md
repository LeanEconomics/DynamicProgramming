# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 5, pp. 103–128. Lean names are relative to
`StokeyLucasPrescott.DeterministicApplications`. Where the Lean statement departs from the book,
see [corrections](corrections.md).

## Carried over from Chapters 3–4

| Source | Claim | Lean |
| --- | --- | --- |
| Chapter 3 | Theorem 3.2 and corollaries, hemi-continuity, the Theorem of the Maximum, interior points | `Contraction`, `Correspondences`, `Maximum`, `InteriorPoints` |
| Chapter 4 | Lemma 4.1, Theorems 4.2–4.15, sufficient conditions for Assumption 4.2 | `ExtendedReals`, `Principle`, `Assumption42`, `BoundedReturns`, `Concavity`, `Envelope`, `ValueDifferentiability`, `ConstantReturns`, `ConstantReturnsDP`, `UnboundedReturns`, `EulerEquations` (see the [Chapter 4 source map](../../DeterministicDP/docs/source-map.md)) |
| pp. 93–95 | The unit-elastic growth model, here with `0 < α ≤ 1` | `PosR`, `logΓ`, `logF`, `coefB`, `coefC`, `affineLog`, `logPolicy`, `αβ_lt_one`, `coefB_pos`, `coefC_neg`, `logPolicy_mem`, `log_objective_le`, `log_opT_affine`, `log_iterate`, `log_assumption41`, `log_capital_le`, `logF_le`, `log_assumption42`, `log_vstar`, `log_policy_optimal` |

## §5.1 The one-sector model of optimal growth

| Source | Claim | Lean |
| --- | --- | --- |
| (U1)–(U3), (T1)–(T3), pp. 103–104 | The model on `X = [0, x̄]` | `GrowthHyp`, `growthΓ`, `growthF`, `growth_f_nonneg`, `continuous_growth_f` |
| Ex 5.1a–b, p. 104 | Assumptions 4.3–4.6 hold; a unique bounded continuous `v`, equal to `v*`, strictly increasing; `G` nonempty and u.h.c. | `growth_assumption43`, `growth_assumption44`, `growth_a45`, `growth_a46`, `growth_assumption41`, `growth_assumption42`, `ex_5_1ab` |
| Ex 5.1c, p. 104 | With (U4), (T4): Assumptions 4.7–4.8, `v` strictly concave, `g` continuous | `growth_a47`, `growth_a48`, `ex_5_1c`, `ex_5_1c_weak_counterexample`, `growthF_concave`, `bellman_concave_growth`, `growth_concave`, `chord_step`, `growth_strictConcave`, `ex_5_1c_weak` |
| Ex 5.1d, pp. 104–105 | `v′(x) = U′(f(x) − g(x))f′(x)`; interior policies under an Inada condition | `liftR`, `liftR_of_mem`, `concaveOn_liftR`, `ex_5_1d`, `eventually_slope_ge`, `slope_le_chord`, `ex_5_1d_interior` |
| Ex 5.1e, p. 105 | `g(x, β)` increasing in `β` | `concave_exchange`, `growthF_increasingDiff`, `bellman_sub_monotone`, `discounted_value_monotone`, `policy_le_of_discount_le`, `ex_5_1e` |

## §5.2–5.4 Cake eating, linear utility, technical progress

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 5.2a, p. 105 | `f(k) = k` satisfies (T1), (T3)–(T5), not (T2); any `x̄` defines `X` | `ex_5_2a_technology`, `ex_5_2a_not_T2`, `ex_5_2a`, `cake_path_le` |
| Ex 5.2b, p. 105 | `U = ln`: `v` in closed form, `g(x) = βx` | `cake_logΓ`, `cake_logF`, `cake_policy`, `ex_5_2b`, `ex_5_2b_policy` |
| Ex 5.2c, p. 105 | The general case | `ex_5_2c`, `ex_5_2c_interior`, `ex_5_2c_deriv` |
| Ex 5.3a, p. 105 | `U(c) = c`: what Section 5.1 still gives | `ex_5_3a`, `ex_5_3a_strict`, `ex_5_3a_corner` |
| Ex 5.3b, p. 105 | `v` near `k*` | `kstar_le_xbar`, `kstar_le_f`, `linear_value_le`, `linear_value_eq`, `ex_5_3b` |
| Ex 5.3c, p. 105 | The optimal policy `min{f(k), k*}` | `linearPolicy`, `ex_5_3c` |
| §5.4, pp. 105–107 | Renormalizing by `(1 + λ)ᵗ` | `renormU`, `renormF`, `renorm_budget`, `renorm_capital`, `renorm_power_utility`, `renorm_log_utility`, `renorm_consumption` |
| Ex 5.4, p. 107 | The renormalized problem satisfies Section 5.1's hypotheses | `renormU_hyp`, `renormU_strictConcave`, `renormF_hyp`, `renormF_concave`, `ex_5_4`, `ex_5_4_analysis`, `power_utility` |

## §5.5–5.6 Tree cutting and learning by doing

| Source | Claim | Lean |
| --- | --- | --- |
| §5.5, p. 107 | Cutting times as optimal stopping | `cutPayoff`, `stopSet`, `cutPayoff_succ`, `first_entry_optimal`, `never_entry_strictMono` |
| Ex 5.5a, p. 107 | No replanting: cut once `h(k)/k ≤ 1 + r` | `ratio_invariant`, `ex_5_5a`, `treeValue`, `treeValue_fe`, `le_treeValue` |
| Ex 5.5b, p. 107 | Replanting: the Faustmann rule | `rotationValue`, `faustmann_identity`, `faustmann_fe`, `antitone_invariant`, `ex_5_5b` |
| §5.6, pp. 107–108 | Learning by doing with a general return | `ExpStock`, `LBDHyp`, `lbdΓ`, `lbdF`, `lbd_γ_le`, `lbd_assumption43`, `lbd_assumption44`, `lbd_exists`, `lbd_not_a46`, `lbd_not_a47`, `lbd_argmax_pos`, `lbd_strictMono`, `lbd_policy_exceeds`, `unique_interior_max` |
| Ex 5.6a, p. 108 | The monopolist | `LBDModel`, `LBDModel.c_lt_γ`, `LBDModel.c_nonneg`, `LBDModel.φ'_nonpos`, `LBDModel.exists_small`, `monopoly_hyp`, `ex_5_6a` |
| Ex 5.6b, p. 108 | The planner | `surplus`, `surplus_hasDerivAt`, `surplus_continuousOn`, `surplus_continuousOn_Ici`, `ex_5_6b_surplus`, `planner_hyp`, `lbd_value_le`, `ex_5_6b` |
| Ex 5.6c, pp. 108–109 | Efficient output exceeds competitive output; the competitive path | `ex_5_6c`, `competitive_output_mono`, `competitive_path` |
| Ex 5.6d, p. 109 | A nonrenewable resource | `resourceF`, `resource_hyp`, `resource_assumption44`, `ex_5_6d` |

## §5.7–5.8 Human capital

| Source | Claim | Lean |
| --- | --- | --- |
| §5.7, pp. 109–110 | The operator and its maximum | `HumanHyp`, `humanΓ`, `humanT`, `humanObj`, `humanM`, `humanA`, `humanArgmax`, `HumanHyp.I_nonempty`, `HumanHyp.obj_cont`, `HumanHyp.bddAbove`, `HumanHyp.exists_max`, `HumanHyp.le_M`, `humanT_linear` |
| Ex 5.7a, p. 110 | `Tⁿv₀ = aₙk`, `a₁ = 1`, `aₙ` increasing; bounded iff `λ ≤ r` | `ex_5_7a_iterate`, `ex_5_7a_one`, `humanM_strictMono`, `ex_5_7a_strictMono`, `humanA_nonneg`, `humanM_le`, `humanM_ge`, `slope_bound`, `ex_5_7a_bounded_iff` |
| Ex 5.7b, p. 110 | The life-cycle profile | `growth_factor_mono`, `ex_5_7b_last`, `ex_5_7b_profile`, `ex_5_7b_corners`, `ex_5_7b_single_peaked` |
| §5.8, pp. 111–112 | A weighted contraction | `WeightedHyp`, `SolvesFE`, `wobj`, `WeightedHyp.ρ_pos`, `continuousOn_wobj`, `abs_wobj_le`, `bound_wmaxValue`, `wbellman`, `exists_wbellman_argmax`, `wbellman_contraction`, `solvesFE_iff`, `weighted_exists_unique` |
| Ex 5.8a, p. 112 | A unique continuous solution | `human_assumption43`, `HCGrowthHyp`, `hcF`, `hcW`, `concave_linear_bound`, `hc_weighted`, `ex_5_8a` |
| Ex 5.8b, p. 112 | `v(k) = Ak^{ασ}`, `g(k) = θk` | `rpow_le_one_add`, `hcObj`, `hcPhi`, `ex_5_8b` |

## §5.9–5.10 Investment

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 5.9a, p. 112 | Linear costs: jump to the target | `investG`, `investH`, `invest_fe`, `invest_telescope`, `invest_partialSum_le`, `invest_plan_tendsto`, `exists_max_sublinear`, `invest_euler` |
| Ex 5.9a, p. 113 | Bounds on investment | `clamp_maximizes`, `bounded_policy`, `intervalΓ`, `intervalΓ_assumption43`, `bellman_concave_of_concaveF`, `fixed_concave_of_concaveF`, `concaveOn_liftR_of_concave`, `exists_bound_Icc_prod`, `investF`, `boundedΓ`, `bounded_assumption43`, `bounded_assumption44`, `ex_5_9a_bounds` |
| Ex 5.9b, p. 113 | Convex adjustment costs | `adjF`, `fullΓ`, `full_assumption43`, `mem_fullΓ`, `adj_assumption44`, `adj_a47`, `full_a48`, `AdjHyp`, `AdjHyp.h43`, `AdjHyp.h44`, `ex_5_9b`, `ex_5_9b_mono`, `ex_5_9b_slope`, `ex_5_9b_envelope`, `ex_5_9b_foc`, `ex_5_9b_euler`, `ex_5_9b_steady` |
| Ex 5.9c, p. 113 | Short-run profits | `profitPi`, `profitPi_eq`, `labor_demand_exists`, `labor_demand_unique`, `profitPi_zero`, `profitPi_mono`, `profitPi_concave`, `profitPi_strictConcave`, `profitPi_deriv` |
| §5.10, pp. 113–114 | Constant returns: Assumptions 4.10–4.11 | `CapStock`, `isCone_Ici`, `crsΓ`, `crsH`, `CRSInvHyp`, `CRSInvHyp.β_lt`, `crs_assumption410`, `crs_F_bound`, `crs_assumption411` |
| Ex 5.10a–c, p. 114 | `v*` homogeneous; every solution with a growth bound is `v*`; `v(k) = Ak` | `ex_5_10a`, `satisfiesFE_of_solvesFE`, `solvesFE_rescale`, `ex_5_10b`, `ex_5_10c` |

## §5.11–5.13 Recursive preferences

| Source | Claim | Lean |
| --- | --- | --- |
| §5.11, pp. 114–115 | `L`, the shift and truncations | `seqSet`, `Seq`, `convex_seqSet`, `shiftSeq`, `continuous_shiftSeq`, `continuous_head`, `abs_apply_le_norm`, `zeroSeq`, `shiftSeq_zero`, `trunc`, `trunc_apply`, `head_trunc`, `shiftSeq_trunc_zero`, `shiftSeq_trunc_succ` |
| Ex 5.11a, c, p. 115 | `T` a contraction; `û = Σ βᵗU(c_t)` | `opTU`, `opTU_contraction`, `ex_5_11c`, `ex_5_11a` |
| Ex 5.11b, p. 115 | `S` complete; continuity under truncation fails | `ex_5_11b_complete`, `eventuallyZero`, `ex_5_11b_counterexample` |
| Ex 5.11d, p. 116 | Aggregators (W1)–(W5) | `AggHyp`, `opTW`, `opTW_apply`, `opTW_contraction`, `ex_5_11d`, `ex_5_11d_mono`, `monotoneOn_of_concave_nonneg`, `ex_5_11d_concave` |
| Ex 5.11e, p. 116 | Marginal rates of substitution | `bump`, `shiftSeq_bump_zero`, `shiftSeq_bump_succ`, `head_bump_zero`, `head_bump_succ`, `ex_5_11e` |
| §5.12, p. 116 | The consumer's budget | `Wealth`, `spend`, `budgetΓ`, `nextWealth`, `vext`, `vext_of_nonneg`, `continuous_vext`, `abs_vext_le`, `continuous_spend`, `spend_nonneg`, `le_div_of_spend`, `norm_le_of_budget`, `budget_compact`, `zero_mem_budget`, `budget_lhc`, `budget_uhc` |
| Ex 5.12a, p. 117 | The sequence problem and (2) | `planCost`, `spend_le_bound`, `summable_planCost`, `planCost_nonneg`, `planCost_eq`, `Feasible5`, `feasible_head`, `feasible_shift`, `utility_le_value`, `consSeq`, `consSeq_head`, `shiftSeq_consSeq`, `consPolicy`, `consPolicy_spec`, `policyNext`, `policyPlan`, `exists_plan_near`, `ex_5_12a`, `wealthPath`, `ex_5_12a_optimal`, `ex_5_12a_necessary` |
| Ex 5.12b, p. 117 | A unique solution, concave, with continuous demand | `ConsHyp`, `consObj`, `continuous_consObj`, `abs_consObj_le`, `consMax_le`, `consT`, `exists_consT_argmax`, `consT_contraction`, `ex_5_12b`, `ex_5_12b_concave`, `ex_5_12b_demand`, `ConsHyp.smul`, `spend_smul`, `scaleW`, `ex_5_12b_homogeneous` |
| Ex 5.12c, p. 117 | Envelope, intratemporal and Euler conditions | `spend_add_smul_single`, `concaveOn_vext`, `ex_5_12c_envelope`, `ex_5_12c_intratemporal`, `ex_5_12c_euler` |
| Ex 5.12d, p. 117 | A monotone transformation of `W` | `ex_5_12d`, `ex_5_12d_not_aggregator` |
| §5.13, pp. 117–118 | The Pareto problem | `isLHC_of_approx`, `cst`, `cst_nonneg`, `cst_le`, `ParetoHyp`, `oneSeq`, `shiftSeq_one`, `utility_one`, `I2`, `paretoΦ`, `paretoObj`, `continuous_cst`, `pareto_top_mem`, `pareto_compact`, `pareto_uhc`, `pareto_lhc`, `continuous_paretoObj`, `abs_paretoObj_le`, `paretoT`, `exists_paretoT_argmax`, `paretoT_contraction` |
| Ex 5.13a, p. 118 | `T` a contraction | `ex_5_13a` |
| Ex 5.13b, p. 118 | `v = v*`, the Pareto frontier | `oneMinus`, `shiftSeq_oneMinus`, `head_oneMinus`, `head_eq_cst`, `utility_zero`, `utility_range`, `oneMinus_le`, `pareto_le_value`, `paretoPol`, `paretoPlan`, `paretoPlan_le`, `shiftSeq_paretoPlan`, `head_paretoPlan`, `ex_5_13b` |

## §5.14–5.16 Inventories and pricing

| Source | Claim | Lean |
| --- | --- | --- |
| §5.14, pp. 118–119 | The functional equation (1) | `Stock`, `sext`, `sext_of_nonneg`, `continuous_sext`, `abs_sext_le`, `leftover`, `orderVal`, `ordSup`, `InvHyp`, `InvHyp.p_pos`, `orderVal_le`, `bddAbove_ordSup`, `horizon`, `horizon_pos`, `orderVal_beyond`, `ordSup_eq`, `invRHS`, `continuous_invRHS`, `abs_invRHS_le`, `invT`, `invT_apply`, `ordSup_mono`, `ordSup_add_const`, `invT_contraction` |
| Ex 5.14a, p. 119 | A unique `v ∈ C(ℝ₊)`; an optimal policy exists | `ex_5_14a`, `ex_5_14a_policy` |
| Ex 5.14b, p. 120 | `Y_n` and its maximizer `N`; how `N` varies with `β`, `c₀` and `p` | `rn`, `Yn`, `one_sub_pow_pos`, `Yn_eq`, `tendsto_Yn`, `ex_5_14b`, `argmax_Yn_indep_p`, `argmax_Yn_mono_c0`, `pow_ratio_strictMono`, `argmax_Yn_mono_beta` |
| Ex 5.14c, p. 120 | `A ∈ (0, 1)` | `ex_5_14c` |
| Ex 5.14d, pp. 120–121 | `w` solves (2), (3), (5); continuous, bounded, piecewise linear; its derivatives and kinks | `SSHyp`, `Aind`, `cellW`, `wSS`, `SSHyp.A_pos`, `SSHyp.A_lt`, `cross_iff`, `cross_one`, `cross_zero`, `wSS_cell`, `wSS_low`, `wSS_two`, `wSS_one_two`, `wSS_three_left`, `wSS_three_right`, `wSS_five`, `wSS_six`, `continuous_cellW`, `continuousOn_wSS_cell`, `continuousOn_wSS`, `wSS_bounds`, `cross_eq`, `wSS_left_piece`, `wSS_right_piece`, `wSS_deriv_low`, `wSS_deriv_left`, `wSS_deriv_right`, `not_differentiableAt_of_kink`, `wSS_kink_one`, `wSS_kink_int`, `wSS_kink_A` |
| Ex 5.14e, p. 121 | Orders are beaten by orders to an integer | `phiSS`, `phi_cell_convex`, `ex_5_14e` |
| Ex 5.14f–g, pp. 121–122 | The value of ordering up to `n`; `max (r_n + βⁿY_N) = Y_N` | `wSS_int`, `ex_5_14f`, `ex_5_14g` |
| Ex 5.14h, p. 122 | `w` satisfies (1), so `w = v`; the (s, S) policy | `key_ineq`, `wBCF`, `sext_wBCF`, `orderVal_wBCF`, `order_le`, `order_int`, `ex_5_14h`, `ex_5_14_value`, `ex_5_14_policy` |
| §5.15, p. 122 | Continuous time: revenue from a stock | `Srev`, `CTHyp`, `Srev_integral`, `Srev_add`, `exp_neg_lt_one` |
| Ex 5.15a, p. 123 | `Y*` well defined, attained at a unique `τ*` | `Gcyc`, `Gcyc_geometric`, `Gcyc_eq`, `Gcyc_le`, `Ystar`, `bddAbove_Gcyc`, `Gcyc_le_Ystar`, `continuousOn_Gcyc`, `ex_5_15a`, `Ncyc`, `Ncyc_strictMono`, `hasDerivAt_hcyc`, `Gcyc_argmax_unique` |
| Ex 5.15b, p. 123 | `w` satisfies the functional equation; the optimal policy | `wCT`, `Vval`, `cycle_le`, `Vval_le`, `Vval_attain`, `ex_5_15b`, `ex_5_15b_unique` |
| §5.16, pp. 123–124 | The operator on `D` | `Dtri`, `DPt`, `Prob`, `convex_Dtri`, `priceQ`, `priceQ_mem`, `leftPt`, `rightPt`, `sellerObj`, `sellerObj_apply`, `continuous_priceQ`, `continuous_sellerObj`, `prob_lhc`, `prob_uhc`, `abs_sellerObj_le`, `sellerT`, `exists_sellerT_argmax`, `sellerT_contraction` |
| Ex 5.16a, p. 124 | A unique fixed point, homogeneous of degree one | `ex_5_16a`, `scalePt`, `ex_5_16a_hom` |
| Ex 5.16b, p. 124 | `w` strictly increasing and weakly convex, `w(1) = 1/(1 − β)` | `topPt`, `diagPt`, `wSel`, `fe_seller`, `v_ge`, `ex_5_16b_one`, `v_eq_w`, `IsConvexD`, `v_convex`, `ex_5_16b_convex`, `v_mono`, `ex_5_16b_strictMono` |
| Ex 5.16c, p. 125 | `g(a) = a` on `[â, 1]`, `â = 1/(2 − β)` | `ex_5_16c` |

## §5.17 A consumption–savings problem

| Source | Claim | Lean |
| --- | --- | --- |
| p. 126 | The model; `U'` and its inverse above `I` | `CSHyp`, `CSHyp.rho_pos`, `CSHyp.super_le`, `CSHyp.super_lt`, `CSHyp.U'_pos`, `CSHyp.U'_lt`, `CSHyp.U'_le`, `cI`, `CSHyp.cI_nonempty`, `CSHyp.cI_mem`, `cI_le`, `CSHyp.cI_pos`, `CSHyp.cI_of_le`, `CSHyp.cI_eq`, `CSHyp.cI_U'`, `CSHyp.cI_anti`, `CSHyp.cI_gt`, `CSHyp.cI_strictAnti`, `CSHyp.le_cI`, `CSHyp.continuousAt_cI`, `CSHyp.U'_cI` |
| pp. 126–127 | The wealth a multiplier exhausts, and its plan | `wealth`, `CSHyp.exists_K`, `CSHyp.wealth_term_eq_zero`, `CSHyp.wealth_eq_sum`, `CSHyp.summable_wealth`, `CSHyp.wealth_nonneg`, `CSHyp.wealth_shift`, `CSHyp.wealth_of_ge`, `CSHyp.wealth_ge`, `CSHyp.wealth_anti`, `CSHyp.wealth_strictAnti`, `CSHyp.wealth_pos`, `CSHyp.lt_of_wealth_pos`, `CSHyp.continuousAt_wealth`, `CSHyp.exists_wealth_eq`, `planμ`, `consμ`, `planμ_zero`, `consμ_zero`, `div_pow_succ`, `CSHyp.planμ_succ`, `CSHyp.consμ_eq`, `CSHyp.planμ_nonneg`, `CSHyp.consμ_ge`, `planμ_tail`, `consμ_tail`, `CSHyp.exists_plan_zero`, `CSHyp.euler_step` |
| pp. 126–128 | Optimality and uniqueness of the plans, by summation by parts | `abel_bound`, `CSWealth`, `csΓ`, `csF`, `consOf`, `CSHyp.consOf_nonneg`, `CSHyp.csF_eq`, `CSHyp.assumption41`, `CSHyp.assumption42`, `planN`, `wealthN`, `CSHyp.planN_feasible`, `CSHyp.consOf_planN`, `valμ`, `CSHyp.summable_val`, `CSHyp.partialSum_planN`, `CSHyp.tendsto_plan`, `CSHyp.plan_total`, `gapAt`, `CSHyp.gapAt_nonneg`, `CSHyp.value_bound`, `CSHyp.total_le`, `CSHyp.total_le_tangent`, `CSHyp.eq_planN_of_cons`, `CSHyp.total_lt`, `CSHyp.vstar_eq`, `CSHyp.vstar_le_tangent`, `CSHyp.optimal_iff`, `CSHyp.vstar_real` |
| Ex 5.17a, p. 126 | The sequence problem and (FE); `v*` well defined and satisfies (FE); optimal plans satisfy it | `ex_5_17a` |
| pp. 126–127 | `v`, `g` and `c₀` on `ℝ₊` | `CSHyp.planN_eq`, `CSHyp.planμ_eq_of_wealth`, `CSHyp.consμ_eq_of_wealth`, `CSHyp.valμ_eq_of_wealth`, `muOf`, `CSHyp.muOf_spec`, `vR`, `gR`, `cR`, `CSHyp.vR_wealth`, `CSHyp.gR_wealth`, `CSHyp.cR_wealth`, `CSHyp.vstar_wealth`, `CSHyp.cR_ge`, `CSHyp.cR_pos`, `CSHyp.gR_nonneg`, `CSHyp.gR_eq`, `CSHyp.cR_eq`, `CSHyp.cR_zero`, `CSHyp.muOf_lt`, `CSHyp.cR_strictMono`, `CSHyp.cR_surj`, `CSHyp.continuousWithinAt_cR`, `CSHyp.continuousOn_cR`, `CSHyp.continuousOn_gR`, `CSHyp.continuousOn_marg` |
| pp. 127–128 | `v` is `C¹`, strictly increasing and strictly concave | `CSHyp.vR_le_tangent`, `CSHyp.hasDerivWithinAt_vR`, `CSHyp.hasDerivAt_vR`, `CSHyp.deriv_vR`, `CSHyp.continuousOn_vR`, `CSHyp.vR_strictMono`, `CSHyp.vR_strictConcave` |
| Ex 5.17b, p. 127 | `m₁ > 0` well defined; on `[0, m₁]`, `g = 0`, `v = U(I + x) + βU(I)/(1 − β)`, `v′ = U′(I + x)` | `m1`, `CSHyp.rhoU_pos`, `CSHyp.rhoU_lt`, `ex_5_17b_m1`, `CSHyp.m1_pos`, `CSHyp.wealth_rhoU`, `CSHyp.muOf_ge`, `CSHyp.gR_eq_zero`, `CSHyp.gR_pos`, `CSHyp.vR_eq_low`, `ex_5_17b` |
| Ex 5.17c, p. 127 | `h` from (2): continuous, strictly increasing, `h(y) → m₁` | `hfun`, `CSHyp.U'_cR`, `CSHyp.gR_def`, `CSHyp.hfun_zero`, `CSHyp.hfun_nonneg`, `CSHyp.gR_hfun`, `CSHyp.euler_hfun`, `CSHyp.hfun_strictMono`, `CSHyp.continuousOn_hfun`, `ex_5_17c` |
| Ex 5.17d, p. 128 | `m₂ > m₁`; `g`, `v` on `(m₁, m₂]`; (5) | `CSHyp.gR_mono`, `CSHyp.gR_strictMono`, `m2`, `CSHyp.continuousOn_vR'`, `ex_5_17d` |
| Ex 5.17e, p. 128 | `v`, `v′` continuous at `m₁` | `ex_5_17e` |
| Ex 5.17f, p. 128 | The induction covers `ℝ₊` | `mSeq`, `CSHyp.mSeq_succ`, `CSHyp.mSeq_strictMono`, `CSHyp.tendsto_mSeq`, `ex_5_17f` |
| Ex 5.17g, p. 128 | `v` satisfies (1) and `v = v*` | `CSHyp.vR_attained`, `ex_5_17g`, `ex_5_17g_hint_fails` |
| Ex 5.17h, p. 128 | The unique optimal plan `x_{t+1} = g(x_t)`; `0 ≤ g(x′) − g(x) < x′ − x` | `CSHyp.gR_planμ`, `ex_5_17h_plan`, `ex_5_17h_slope`, `ex_5_17h_slope_le_one`, `ex_5_17h_book_bound_fails` |
| Corrections | `m₁` need not exist; the counterexample to 5.17h | `hasDerivAt_cexp`, `ex_5_17b_m1_fails`, `ceU`, `ceU'`, `hasDerivAt_ce1`, `hasDerivAt_ce2`, `ceU'_low`, `ceU'_high`, `hasDerivAt_ceU`, `ceU'_strictAnti`, `ceU'_pos`, `continuousAt_ceU'`, `ceHyp`, `ex_5_17h_counterexample` |
