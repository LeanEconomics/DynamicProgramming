# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 16, pp. 475–500. Equation numbers restart in each section, as in the book. Lean
names are relative to `StokeyLucasPrescott.EquilibriumApplications`; names from the carried
Chapter 6 modules carry the prefix `GrowthCertaintyDD`. Where the Lean statement departs from the
book, see [corrections](corrections.md).

## Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 475 | Overview: planning problems as economies of identical consumers and constant-returns firms; Theorems 15.3 and 15.4 relate symmetric competitive equilibria and symmetric Pareto optima; plan of §§16.1–16.7 | Not formalised (overview). The averaging argument behind "symmetric Pareto optimum = planner's solution" is `gc_symmetric_paretoOptimal_iff` |

## §16.1 A one-sector model of growth under certainty

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 476–477 | Commodity space `ℓ∞`; `X = ℓ∞⁺`; `u(x) = Σ_t βᵗ U(x_t)`; `Y = {y ≥ 0 : ∃ k ≥ 0, k₀ = k̂, k_{t+1} + y_t ≤ f(k_t)}`; the restrictions on `β`, `U`, `f` | `gcX`, `mem_gcX`, `gcU`, `gcY`, `GrowthCertaintyHyp`, `gcKmax`, `gc_f_nonneg`, `gc_f_pos`, `gc_lt_f_of_lt_kbar`, `gc_f_le_kmax`, `gc_kmax_pos`, `gc_capital_le`, `gc_output_le` |
| p. 476 | `f(k) = F(k, 1) + (1 − δ)k` with `F ≥ 0` is bounded, `δ ∈ (0, 1]` | `gc_bounded_forces_full_depreciation`, `gc_bounded_counterexample`; replaced by `f(k̄) = k̄`, `f(k) < k` for `k > k̄` (`GrowthCertaintyHyp`) |
| p. 477 | Since `f` is bounded, `f(k̄) = k̄` for some `k̄ > 0` | `gc_kbar_counterexample` |
| p. 477 | The planner's problem `max_{x ∈ X ∩ Y} u(x)` gives the symmetric Pareto optimum | `gc_symmetric_paretoOptimal_iff`, `gc_aggTech_unit`, `gc_paretoOptimal_of_max` |
| Exercise 16.1(a), p. 477 | Exactly one symmetric Pareto optimum; what Theorem 15.3 implies for symmetric equilibria | `gc_summable`, `gc_utility_mono`, `gc_utility_lt`, `gc_exists_optimum`, `gc_optimum_unique`, `gc_localNonsatiation`, `ex_16_1a` |
| Exercise 16.1(b), p. 477 | Assumptions 15.1–15.5; what Theorem 15.4 implies for existence | `gc_convex_X`, `gc_utility_concave`, `gc_utility_strict_midpoint`, `gc_convex_Y`, `gc_interior_nonempty`, `gc_interior_ge`, `ex_16_1b_assumptions`, `gc_supporting_nonneg`, `gc_abs_le_of_nonneg`, `gc_one_pos`, `ex_16_1b_cheaper`, `ex_16_1b`; the manual's steps: `gcEval`, `ex_16_1b_manual_cheaper_counterexample`, `ex_16_1b_manual_interior_counterexample` |
| Exercise 16.1(c), p. 477 | Assumptions 15.6–15.7; what Theorem 15.6 implies for prices `p ∈ ℓ₁` | `gc_seqTruncClosed_Y`, `ex_16_1c_assumptions`, `ex_16_1c` |
| p. 477 | `p·x ≤ p·x⁰`; `1/(1 + r_t) = p_{t+1}/p_t`; the budget constraint in interest-rate form | `gc_price_pos`, `gcRate`, `gc_rate_spec`, `gc_discount_prod`, `gc_budget_iff` |
| Exercise 16.1(d), p. 478 | `r_t` in terms of marginal rates of substitution and transformation; relative prices are unique | `gcU_sub_of_eq_off_pair`, `gc_consumer_foc`, `gc_firm_foc`, `ex_16_1d`, `ex_16_1d_unique` (interior allocation assumed) |
| pp. 478–479 | Sequential spot markets; the functions `(g, q, ψ, h, Ω, ω)`; in equilibrium `a = ψ(k, k)`, `z = k` | The arguments of `GcRecursiveEq` |
| (1), p. 479 | The firm's equation `ψ(k, z) = max_{0 ≤ z′ ≤ f(z)} {f(z) − z′ + q(k) ψ[g(k), z′]}` | `GcFirmData`, `gcDisc`, `gcZc`, `gcFirmObj`, `gcFirmT`, `gcFirmT_ge`, `gcFirmT_attained`, `gcFirmT_continuous`, `gcFirmTB`, `GcFirmBellman` |
| (2), p. 479 | The household's equation `Ω(k, a) = max_{0 ≤ a′ ≤ a/q(k)} {U[a − q(k)a′] + β Ω[g(k), a′]}` | `GcHouseholdData`, `gcAc`, `gcHhObj`, `gcHhT`, `gcHhT_ge`, `gcHhT_attained`, `gcHhT_continuous`, `gcHhTB`, `GcHouseholdBellman` |
| (R1)–(R4), pp. 479–480 | Recursive competitive equilibrium | `GcRecursiveEq` |
| p. 480 | Walras' law: `q(k) = {ψ(k, k) − [f(k) − g(k)]}/ψ[g(k), g(k)]`, so `c = f(k) − g(k)` | `gc_firm_value_walras` |
| (3), p. 480 | The planner's equation `v(k) = max_{0 ≤ k′ ≤ f(k)} {U[f(k) − k′] + β v(k′)}`, its policy `g`, `c(k) = f(k) − g(k)` | Properties used: `GrowthCertaintyPlanner`, `gc_planner_dUc_pos`, `gc_planner_dUc_continuousOn`, `gc_planner_steady_state`. Derived from (3): `GrowthCertaintyDD.GrowthDyn`, `GrowthCertaintyDD.Setting61`, `GrowthCertaintyDD.exists_setting61`, `GrowthCertaintyDD.gpol`, `gc_policy_ge_of_le_kstar`, `gc_planner_of_bellman`, `gc_hyp_of_dyn` |
| (4), p. 480 | `q(k) = β f′(k) U′(c[g(k)])/U′[c(k)]` | As printed: `gcQPrinted`, `gc_eq4_typo_counterexample`. Corrected: `gcQ`, `gcGK`, `gcQK`, `gc_planner_q_pos`, `gc_planner_household_foc`, `gc_planner_q_mul_df` |
| Exercise 16.1(e), pp. 480–481 | A unique bounded continuous `ψ` satisfying (1), with a single-valued continuous policy `h` | `gcGK_iterate`, `gc_planner_prod_q`, `gc_planner_firmData`, `gc_firmBellman_unique`, `gcFirmT_sub_le`, `gc_firmTB_iterate_dist`, `gc_firmTB_contracting`, `gc_firmBellman_of_fixed`, `ex_16_1e_firm_exists`, `gcFirmT_concave`, `gc_firm_fixed_concave`, `gc_firm_strictConcave`, `gc_firm_policy_unique`, `gcFirmPolicy`, `gcFirmPolicy_spec`, `gc_argmax_continuous`, `gc_firm_policy_continuous`, `ex_16_1e_firm`; (1) is not a contraction: `ex_16_1e_not_contraction`, `gcLogG`, `gcLogC`, `gcLogDU`, `gcLogDF`, `gc_logCD_q_gt_one` |
| Exercise 16.1(e), p. 481 | A unique bounded continuous `Ω` satisfying (2), with a single-valued continuous policy `ω` | `gc_planner_hhData`, `gcHhT_sub_le`, `gc_hhTB_contracting`, `gc_hhBellman_unique`, `gc_hhBellman_of_fixed`, `gcHhT_concave`, `gc_hh_fixed_concave`, `gc_hh_policy_unique`, `gcHhPolicy`, `gcHhPolicy_spec`, `gc_hh_policy_continuous`, `ex_16_1e_household` |
| Exercise 16.1(f), p. 481 | If firms use `h` and households use `ω`, (R3) and (R4) hold | `gc_telescope_le`, `gc_nonpos_of_partial_le`, `gc_concave_le_tangent`, `GcFirmFeasible`, `gcFirmV`, `gc_firm_value_ge`, `gcFirmPath`, `gc_firm_value_eq`, `gc_firm_euler_optimal`, `ex_16_1f_R3`, `GcHhFeasible`, `gcHhV`, `gc_hh_value_ge`, `gcHhPath`, `gc_hh_value_eq`, `gcHhCand`, `gc_hh_euler_optimal`, `ex_16_1f_R4`, `ex_16_1f` |
| Exercise 16.1(g), p. 481 | (e) and (f) make `(x⁰, y⁰)` the equilibrium allocation with sequential trading | `gcKPath`, `ex_16_1g`, `ex_16_1g_planner`; with `g` the policy of (3): `ex_16_1efg`, `ex_16_1efg_exists` |
| p. 481 | The spot-market equilibrium has the allocation of the date-0 equilibrium, and its interpretation is closer to experience | The allocation: `ex_16_1g_planner`; the remark is not formalised |
| (not in the book) | An economy satisfying the restrictions of §16.1, with `k̂ > k̄` | `gcRatio`, `gcRatio_strictConcave`, `gcRatio_strictMono`, `gcRatio_continuousOn`, `gcRatio_mem_Icc`, `gc_example_hyp` |

## §16.2 A many-sector model of stochastic growth

| Source | Claim | Lean |
| --- | --- | --- |
| p. 481 | The growth models of §§10.1–10.3 and "Section 13.1" have a market interpretation | Not formalised (remark; "13.1" read as §13.3) |
| p. 481 (§10.3, pp. 290–292) | The technology `Φ` with (a)–(c), `Γ`, `F`, the Bellman equation of §10.3, the policy `g` and the plans `π*`, `γ*` of Exercise 10.3b | `MsTech`, `msBeg`. The §10.3 dynamic program is not reproduced; the optimality of `γ*` is a hypothesis of `ex_16_2b` |
| pp. 481–482 | `S^M`; `C`, the positive orthant; `u`; `Y` for given `x̂` | `LinftyTimeState` (carried), `msC`, `msU`, `ManySectorHyp`, `msOne`, `msY`, `ms_aggTech_unit` (one good, `M = 1`) |
| Exercise 16.2(a), p. 482 | `(C, u, Y)` satisfy Assumptions 15.1–15.7 and 15.8′–15.9′ | Consumer: `ms_convex_C`, `ms_U_concave`, `ms_assumption15_2`, `ms_U_continuous`, `ms_C_timeTrunc`, `ms_C_periodTrunc`, `ms_tendsto_U_timeTrunc`, `ms_assumption15_7`, `msU_periodTrunc`, `ms_tendsto_U_periodTrunc`, `ms_assumption15_9'`, `ex_16_2a_consumer`. Technology: `ms_Y_sub_C`, `ms_convex_Y`, `MsFreeDisposal`, `ms_Y_timeTrunc`, `ms_Y_periodTrunc`, `MsPositiveProduction`, `ms_interior_Y`, `ex_16_2a`. Counterexamples: `msPhiEps`, `msPhiEps_tech`, `ex_16_2a_trunc_counterexample`, `msPhiZero`, `msPhiZero_tech`, `ex_16_2a_interior_counterexample`. With `M` goods: `msMUnif`, `msMμ`, `msM_ae_iff`, `msMEU`, `msMU`, `ManySectorMHyp`, `msM_eu_continuous`, `msM_eu_trunc_tendsto`, `ex_16_2a_consumer_M`, `MsMTech`, `msMY`, `MsMFreeDisposal`, `MsMPositiveProduction`, `ex_16_2a_M` |
| Exercise 16.2(b), p. 482 | `(γ*, γ*, ν)` is a competitive equilibrium with `ν(c) = Σ_t ∫ Σ_m p_{tm} c_{tm} dμ^t` | `ms_U_lt_add_one`, `ms_supporting_nonneg`, `ms_abs_le_of_nonneg`, `ms_one_pos`, `ms_interior_ge`, `ms_zero_mem_C`, `ms_linfty_bounds`, `ms_paretoOptimal`, `ex_16_2b` (with `theorem_15_4`, `remark_cheaper_point`, `theorem_15_9`); with `M` goods: `msM_price_form`, `ex_16_2b_M` |
| pp. 482–483 | Pricing securities by letting the consumer trade away from the equilibrium; one-period security `f`, its price `q(x, z)`, `c(x, z)` | The data of `MsSecData` and `MsFellerData` |
| (1), p. 483 | `w(A, x, z) = max_{δ, b} {U[c(x, z) + δ] + β ∫ w[b f(z′), g(x, z), z′] Q(z, dz′)}` with `δ + q b = A`, `c + δ ≥ 0`, `b ≥ B` | Finite shocks: `MsSecData`, `msSecDom`, `msSecObj`, `MsSecBellman`. Feller: `MsFellerData`, `msFE`, `msFObj`, `MsFellerBellman` |
| Exercise 16.2(c), p. 483 | A unique bounded continuous `w` satisfies (1) | Finite shocks: `ms_sec_next_mem`, `ms_secBellman_unique`, `msSecT`, `msSecT_attained`, `msSecT_continuous`, `msSecTB`, `ms_secTB_contracting`, `ms_secBellman_of_fixed`, `ex_16_2c`, `ex_16_2c_domain_counterexample`. Feller transition on a compact shock space: `msFE_continuous`, `ms_fellerBellman_unique`, `msFellerT`, `msFellerTB`, `ms_fellerTB_contracting`, `ms_fellerBellman_of_fixed`, `ex_16_2c_feller`. General measurable shock space and return: `MsGenData`, `msGE`, `MsGBellman`, `msGE_continuous`, `msG_sSup_eq_iSup`, `msGT_measurable`, `msG_contracting`, `msG_exists`, `msG_bellman_unique`, `msG_solution_concave`, `ex_16_2c_general` |
| Exercise 16.2(d), p. 483 | If `c(x̂, ẑ) > 0`, `w(·, x̂, ẑ)` is differentiable and `w₁(0, x̂, ẑ) = U′[c(x̂, ẑ)]` | `ms_bs_envelope`, `MsSecConcave`, `msSecT_concave`, `ms_sec_fixed_concave`, `ex_16_2d`, `ex_16_2d_iff`, `ex_16_2d_counterexample`; at the equilibrium price: `ms_sec_super_step`, `ms_sec_supergradient`, `ex_16_2d_converse`, `ex_16_2d_equilibrium` (finite shocks); general shock space: `msGE_hasDerivAt`, `ex_16_2d_general`, `msG_super_step`, `msG_supergradient`, `ex_16_2d_converse_general`, `ex_16_2d_equilibrium_general` |
| p. 483 | The first-order condition for (1); in equilibrium `A = b = 0` | `ms_sec_foc` |
| (2), p. 483 | `U′[c(x, z)] q(x, z) = β ∫ U′(c[g(x, z), z′]) f(z′) Q(z, dz′)` | `ex_16_2_eq2` (finite shocks), `msG_foc`, `ex_16_2_eq2_general` (general shock space); a hypothesis of `ex_16_2e` and `ex_16_2f` |
| Exercise 16.2(e), p. 484 | The price of a riskless claim and of a bond paying one unit on `E` | `ex_16_2e` |
| Exercise 16.2(f), p. 484 | Lottery tickets with independent components `z = (z₁, z₂)` | `ex_16_2f` |
| Exercise 16.2(g), (3), p. 484 | `U′[c] q = β ∫ U′(c[g, z′]) {f[g, z′] + q[g, z′]} Q(z, dz′)` for a multi-period asset | `ex_16_2g` (finite shocks), `ex_16_2g_general` (general shock space); (3) for a general kernel: `MsEq3` |
| Exercise 16.2(h), p. 484 | The price of `f = Σ_i f_i` | `ms_eq3_unique`, `ms_eq3_sum`, `ex_16_2h`, `ex_16_2h_bubble_counterexample` |
| pp. 484–485 | (h) is a version of the Modigliani–Miller theorem | `ex_16_2h` |
| (3′), p. 485 | `U′(c_t) q_t = β E_t[U′(c_{t+1})(f_{t+1} + q_{t+1})]`; with `U′` constant, `β = 1` and no dividend, `q_t = E_t q_{t+1}` | `ms_martingale_prices` |
| p. 485 | `w_{t+1} = β U′(c_{t+1})(f_{t+1} + q_{t+1}) − U′(c_t) q_t`; `W_t = Σ_{s ≤ t} w_s` is a martingale | `ms_martingale_increment` (one-step form). The path-space martingale is not formalised |
| p. 485 | Discussion of stock prices, smooth consumption, short periods and dividend dates | Not formalised (remark) |

## §16.3 An economy with sustained growth

| Source | Claim | Lean |
| --- | --- | --- |
| p. 485 | Bounded commodity spaces cannot model unbounded growth of consumption | Not formalised (motivation); `sgHalfPath_not_bdd` |
| (1), p. 486 | `k_{t+1} + y_t ≤ γᵗ k_tᵅ`, `γ > 1`, `0 < α < 1`, `k₀ > 0` | `SGFeasible` |
| p. 486 | The path `k_{t+1} = y_t = ½ γᵗ k_tᵅ` is feasible, and neither `y` nor `k` is in `ℓ∞` | `sgHalfPath`, `sgHalfPath_feasible`, `sgHalfPath_not_bdd` |
| p. 486 | `S_θ` with `‖x‖_θ = sup_t \|θ⁻ᵗ x_t\|` is a normed linear space | `sgSθ`, `sgNormθ`, `sgOfBdd`, `sgOfBdd_mem`, `exists_sgOfBdd`, `sgOfBdd_injective`, `sgOfBdd_add`, `sgOfBdd_smul`, `norm_eq_sgNormθ`, `sgConst`, `norm_sgConst_le` |
| p. 486 | `Y = {y : (1) holds for some k ≥ 0}` | As printed: `sgTechPrinted`, `sgTechPrinted_not_subset`. Corrected: `sgTech`, `sgTechθ`, `sgTechθ_nonneg` |
| Exercise 16.3(a), p. 486 | For which `θ` is `Y ⊆ S_θ`? | `sgThetaHat`, `sgThetaHat_pos`, `one_lt_sgThetaHat`, `sgThetaHat_rpow`, `sg_upper_bound`, `sg_witness`, `sg_pow_unbounded`, `ex_16_3a` |
| Exercise 16.3(b), p. 486 | For which of these `θ` does `Y` have an interior point? | `ex_16_3b` |
| p. 486 | `θ` is the unique value with `Y ⊆ S_θ` and `int Y ≠ ∅` | `ex_16_3_theta_unique` |
| Exercise 16.3(c), p. 486 | With `X = S_θ⁺` and `U` continuous and bounded, `u` is continuous in `‖·‖_θ` | `sgUtility`, `sgSθplus`, `ex_16_3c` |
| p. 486 | CRRA `U(x) = (x^{1−σ} − 1)/(1 − σ)` is unbounded above if `σ ≤ 1` and below if `σ ≥ 1` | `sgCRRA`, `sgCRRA_of_ne`, `sgCRRA_one`, `sgCRRA_continuousOn`, `sgCRRA_strictMonoOn`, `sgCRRA_concaveOn`, `sgCRRA_tendsto_atTop`, `sgCRRA_not_bddAbove`, `sgCRRA_not_bddBelow` |
| Exercise 16.3(d), p. 487 | For `X = {x ∈ S_θ : inf_t \|θ⁻ᵗ x_t\| ≥ a}` and CRRA `U` with `βθ^{1−σ} < 1`, `u` is bounded and continuous on `X` | As printed: `sgXPrinted`, `ex_16_3d_printed_not_nonneg`, `ex_16_3d_counterexample`, `ex_16_3d_counterexample_half`. Corrected: `sgXa`, `mem_sgXa_iff`, `sgCRRA_scale`, `sgConstK`, `sgUtility_split`, `ex_16_3d_summable`, `sgUtility_eq_on_sgXa`, `ex_16_3d_bounded_on_balls`, `ex_16_3d_continuousOn`, `ex_16_3d_bounded_of_one_lt` |
| p. 487 | `X` is unnatural; "with luck" its lower bound does not bind | The hypothesis `x_t ≥ a′θᵗ`, `a′ > a`, of `ex_16_3e_ii` and `ex_16_3e_ii_direct` |
| Exercise 16.3(e)(i), p. 487 | A competitive equilibrium `(x, y, p)` has `x = y` and is Pareto optimal | `sgX`, `sgU`, `sgY`, `sg_feasible_unit`, `sg_aggTech_unit`, `sg_utility_lt_add_const`, `sg_localNonsatiation`, `sg_paretoOptimal_iff`, `ex_16_3e_i` |
| Exercise 16.3(e)(ii), p. 487 | A Pareto optimum `x` has a price `p` with `(x, x, p)` a competitive equilibrium | `sg_convex_sgXa`, `sg_utility_concave`, `sg_assumption15_2`, `sg_convex_sgTechθ`, `sg_support_nonneg`, `sg_support_one_pos`, `ex_16_3e_ii`; with inner-product prices: `sgCRRA_hasDerivAt`, `sgCRRA_tangent`, `sgPriceWeight`, `sg_price_summable`, `sgPriceDual`, `sgPriceDual_eq_inner`, `ex_16_3e_ii_direct` |

## §16.4 Industry investment under uncertainty

| Source | Claim | Lean |
| --- | --- | --- |
| p. 487 | The aim: equilibrium iff surplus maximisation, then a synthetic consumer | Not formalised (overview) |
| pp. 487–488 (§10.4, pp. 292–295) | Inverse demand `D`, surplus `U(q, z) = ∫₀^q D(v, z) dv`, adjustment cost `c`, interest rate `r` | `IndustryDemand`, `surplusFn`, `D_le_bar`, `D_pos`, `surplusFn_continuous`, `surplusFn_le`, `surplusFn_abs_le`, `surplusFn_lipschitz`, `IndustryCost`, `IndustryCost.convexOn`, `IndustryCost.persp_mono`, `IndustryCost.persp_convex` |
| p. 488 | Constant returns: one representative firm | `industryTech_smul`; Exercise 16.4a below |
| p. 488 | The commodity space `L` of pairs `(q_t, I_t)`, `q_t, I_t ∈ L∞(Z^t, 𝒵^t, μ^t)` | `IndustryShocks`, `IndustryAdapted`, `IndustryBdd`; as a normed space: `IndustrySpace`, `indQ`, `indI`, `indMk` |
| (1), pp. 488–489 | The production set `Y` | `IndustryTech`, `industry_witness_pos`, `industryH`, `industryH_spec`, `industryH_ge`, `industryH_mono`, `industryH_persp_mono`, `industryCap`, `industryCap_pos`, `industryCap_meas`, `industryCap_le`, `industryTech_of_cap`, `industryTech_combo`, `industryTech_convex` |
| (I1)–(I3), p. 489 | Industry equilibrium | `industryPV`, `industryPV_add`, `industryPV_sub`, `industryPV_const_mul`, `industryPV_mono`, `industryProfit`, `IndustryEquilibrium` |
| (I4), p. 489 | Surplus-maximising allocation | `industrySurplus`, `IndustrySurplusMax` |
| Exercise 16.4(a), p. 489 | Both definitions for `J` identical firms | `indAgg`, `IndustryEquilibriumJ`, `IndustrySurplusMaxJ`, `industryTech_add`, `industryTech_sum`, `industryTech_split`, `ex_16_4a_surplus`, `ex_16_4a_equilibrium` |
| Exercise 16.4(b), p. 490 | An industry equilibrium allocation is surplus maximising | `surplusFn_le`, `industry_surplus_bdd`, `industry_profit_bdd`, `ex_16_4b` |
| p. 490 | With §10.4, at most one industry equilibrium | Not proved (the uniqueness of the surplus maximum of §10.4 is not in this project) |
| Exercise 16.4(c), p. 490 | A surplus maximum with `p_t = D(q_t, z_t)` is an industry equilibrium | `industryPV_tendsto`, `ex_16_4c` |
| pp. 490–491 | (c) needs no Hahn–Banach; the synthetic consumer `u(q, I) = E Σ (1 + r)⁻ᵗ [U(q_t, z_t) − I_t]` on `X = L₊` | `indX`, `indU`, `indY` |
| Exercise 16.4(d), p. 491 | `(X, u)` satisfies Assumptions 15.1–15.3 and `Y` satisfies 15.4–15.5 | `ind_utility_concave`, `industry_interior`, `ex_16_4d` |
| p. 491 | Surplus-maximising allocations are Pareto optimal | `indParetoOptimal_of_surplusMax` |
| Exercise 16.4(e), p. 491 | Theorems 15.3–15.6 give (b) and (c) | `indPriceDual`, `ind_localNonsatiation`, `ex_16_4e_competitiveEq`, `ex_16_4e_b`, `ex_16_4e_c`; Assumption 15.8′ fails: `indLinftyMeasure`, `indFiltration`, `indLinftyTech`, `indLinftyPlan`, `indLinftyPlan_mem`, `indNullSeq`, `industry_trunc_not_mem`, `industry_not_assumption15_8'` |

## §16.5 Truncation: a generalization

| Source | Claim | Lean |
| --- | --- | --- |
| p. 491 | Truncate to a point other than zero when `0 ∉ Xᵢ` | `seqTruncTo`, `seqTruncTo_apply`, `seqTruncTo_zero` |
| (1), p. 491 | `ψ(x) = lim_T φ(xᵀ)` (Lemma 15.5) | `seqRegularPart`, `lemma_15_5` (carried) |
| Exercise 16.5(a), (2), p. 492 | `lim_T φ(x₁, …, x_T, a_{T+1}, …) − ψ(x) = φ(a) − ψ(a)` | `apply_seqTruncTo`, `tendsto_apply_seqTruncTo`, `ex_16_5a` |
| Assumption 16.1, p. 492 | (a)–(d) for an allocation `[(aᵢ), (bⱼ)]` | `Assumption16_1`, `assumption16_1_zero_iff`, `assumption16_1_not_assumption15_6` |
| (3)–(4), p. 492 | The standing hypotheses | Hypotheses of `ex_16_5b`–`ex_16_5e` |
| Exercise 16.5(b), pp. 492–493 | `ψ(x) + [φ(aᵢ) − ψ(aᵢ)] ≥ φ(xᵢ⁰)` and `ψ(y) + [φ(bⱼ) − ψ(bⱼ)] ≤ φ(yⱼ⁰)` | `truncation_step_consumer`, `truncation_step_firm`, `ex_16_5b` |
| Exercise 16.5(c), p. 493 | `φ − ψ` agrees on `Σᵢ xᵢ⁰` and `Σᵢ aᵢ`, and on `Σⱼ yⱼ⁰` and `Σⱼ bⱼ` | `truncation_chi_le`, `truncation_sum_chi_eq`, `ex_16_5c` |
| Exercise 16.5(d), p. 493 | `φ(xᵢ⁰) = ψ(xᵢ⁰) + [φ(aᵢ) − ψ(aᵢ)]`, and likewise for firms | `ex_16_5d` |
| Exercise 16.5(e), p. 493 | (3) and (4) hold for `ψ` | `ex_16_5e` |
| p. 491 | A strengthening of Theorem 15.6 | `theorem_16_5_competitiveEq`, `theorem_15_6_of_ex_16_5e` |

## §16.6 A peculiar example

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 493–494 | One household, `X = ℓ∞⁺`, `u(x) = Σ_t 2⁻ᵗ[1 − exp(−x_t 2ᵗ)]`, `Y = {y : y_t ≤ 2⁻ᵗ}` | `pecW`, `pecTerm`, `pecUfun`, `pecX`, `pecU`, `pecY`, `pecStar`, `pecStar_mem_pecX`, `pecStar_mem_pecY`, `pec_aggTech` |
| p. 494 | `u` is bounded, continuous, strictly increasing and strictly concave | `pecTerm_nonneg`, `pecTerm_lt`, `continuous_pecTerm`, `pecTerm_strictMono`, `pecTerm_concave`, `hasSum_pecUfun`, `pecUfun_le`, `pecUfun_lt`, `pecUfun_update`, `pec_assumption15_2`, `pec_assumption15_3`, `pec_not_lipschitz` |
| p. 494 | The unique Pareto optimum is `x* = y* = (½, ¼, …)` | `pecU_pecStar`, `pec_feasible_iff`, `pecU_le_of_mem`, `pec_paretoOptimal_iff`, `pec_nonsatiated`, `pec_localNonsatiation` |
| Exercise 16.6(a), p. 494 | Assumptions 15.1–15.7 hold | `pec_assumption15_1`, `pec_assumption15_2`, `pec_assumption15_3`, `pec_assumption15_4`, `pec_assumption15_5`, `pec_assumption15_6`, `pecU_seqTrunc`, `pec_assumption15_7`, `ex_16_6a`; the manual's steps: `pec_manual_uniform_delta_counterexample`, `pec_manual_tail_offbyone` |
| (1)–(2), p. 494 | Theorem 15.4 gives a supporting `φ ≠ 0` | `pec_supporting_exists` |
| (3), p. 494 | `ψ(x) = lim_T φ(xᵀ)` also supports (Theorem 15.6) | `seqRegularPart`, `pec_regular_supports` |
| p. 494 | If `φ(x*) ≠ 0`, `(x*, y*, φ)` is a competitive equilibrium (the Remark) | `remark_cheaper_point`; the hypothesis never holds: `pec_phi_star_eq_zero`, `pec_no_cheaper_point` |
| p. 495 | Marginal utilities at `x*` all equal `e⁻¹`, so `p = (c, c, …)` is a natural candidate | `pecTerm_pecW`, `pecUfun_pecW` |
| Exercise 16.6(b), p. 495 | `p = (c, c, …)` is not a continuous linear functional on `ℓ∞` | `pec_const_price_not_dual`, `ex_16_6b` |
| Exercise 16.6(c), p. 495 | Every `φ` satisfying (1)–(2) has `ψ = 0` | `pec_add_single_mem`, `pecU_star_two_single`, `pec_transfer_gain`, `pec_seqRegularPart_add_single`, `pec_price_nonneg`, `pec_price_not_lt`, `ex_16_6c`; the manual's step: `pec_equal_transfer_lowers_utility` |
| Exercise 16.6(d), p. 495 | In `ℓ₁`, `Y` has empty interior, and `(x*, y*, p)` with `p = (c, c, …)` is a competitive equilibrium | `pecL1`, `pecX1`, `pecU1`, `pecY1`, `pecStar1`, `pecPrice1`, `pec_aggTech1`, `ex_16_6d_interior`, `pecL1_not_finiteDimensional`, `ex_16_6d_not_assumption15_5`, `pec_term_le_linear`, `pec_ell1_sum_ge`, `ex_16_6d_competitiveEq`, `ex_16_6d` |
| (not in the book) | Every supporting `φ` vanishes on finitely supported sequences and at `x*`; there is no competitive equilibrium in `ℓ∞` | `pec_phi_seqC00`, `pec_tendsto_seqTrunc_star`, `pec_not_competitiveEq`, `pec_no_competitiveEq`, `pec_real_conclusion` |

## §16.7 An economy with many consumers

| Source | Claim | Lean |
| --- | --- | --- |
| p. 495 | A deterministic many-agent system generalising §5.13 | Not formalised (overview) |
| pp. 495–496 (§5.11, pp. 114–116) | Aggregators `Wᵢ` with (W1)–(W5); `uᵢ` the fixed point of `T_{Wᵢ}` (Exercise 5.11d), bounded, continuous, increasing, concave, with the tail bound `\|uᵢ(c) − uᵢ(cⁿ)\| ≤ βᵢⁿ ‖uᵢ‖` | `IsAggregator`, `IsAggregatorFixedPoint` (carried), `ManyConsumersAggregator`, `mc_utility_concave`, `mc_utility_mono`, `mc_utility_zero`, `mc_utility_strict`; continuity for coordinatewise convergence: `mc_seqTrunc_tendsto`, `mc_utility_tendsto_coord`. Existence of `uᵢ` is a hypothesis |
| p. 496 | `S^l`, `C = S^l₊`; `C` and `uᵢ` satisfy Assumptions 15.1–15.3, 15.6–15.7 | `mcCons`, `mc_assumptions` |
| p. 496 | (T1)–(T7) and `M = {κ : (0, κ) ∈ Φ(κ)}` | `ManyConsumersTech`, `mcM`, `ManyConsumersTech.zero_mem` |
| p. 496 | `Y(k̂)`, the consumption sequences feasible from `k̂` | `mcProdSet`, `mcProdSet_subset_cons`; with unbounded capital paths: `mcProdSetUnb`, `mcProdSet_subset_unb` |
| Exercise 16.7(a), p. 497 | `Y(k̂)` is closed and convex and satisfies Assumption 15.6; an interior point if `k̂ ∈ int M` | `ex_16_7a_convex`, `mcProdSet_combo`, `zero_mem_mcProdSet`, `mcProdSet_disposal`, `ex_16_7a_trunc`, `ex_16_7a_interior`. Not closed: `mcExPhi`, `mcExPhi_tech`, `mcExCn_mem`, `mcExCn_tendsto`, `mcExC_not_mem`, `ex_16_7a_counterexample`. Closed for unbounded paths: `ManyConsumersTech.isCompact_image`, `ManyConsumersTech.isClosed_graph`, `mcReach`, `mcReach_spec`, `ex_16_7a_closed`, `ex_16_7a_unb`, `mcExC_mem_unb`. Closed under (T8): `MCCapitalBound`, `mcExPhi_not_capitalBound`, `mc_path_bound`, `mcProdSetUnb_eq`, `ex_16_7a_closed_of_bound` |
| p. 497 | With (W1)–(W5), (T1)–(T7) and `k̂ ∈ int M`, Theorems 15.3, 15.4 and 15.6 apply, and Pareto optima are the competitive equilibrium allocations | `mc_aggTech_unit`, `mc_assumptions`, `mc_localNonsatiation`, `mc_welfare`, `mc_nonsatiation_counterexample`, `mc_supporting_nonneg`, `mc_competitiveEq_of_pos` |
| p. 497 | Allocations feasible from `k̂` | `mcFeasible`, `mcFeasible_zero`, `mc_feasible_iff` |
| (1), p. 497 | The utility possibility set `U(k̂)` | `mcUtilSet`, `mcUtilSet_nonempty`, `mc_utility_bounds`, `mcUtilSet_subset_Icc`, `mcUtilSet_bddAbove` |
| (2), p. 497 | `Δᴵ` and the support function `v(κ, θ) = sup_{z ∈ U(κ)} Σᵢ θᵢ zᵢ` | `mcSimplex`, `mcSupport`, `mc_eq2` |
| Exercise 16.7(b), p. 497 | An allocation is Pareto optimal iff it attains the supremum in (2) | `mcUtilHull`, `convex_mcUtilHull`, `ex_16_7b_onlyIf`, `ex_16_7b_if`, `ex_16_7b_counterexample` |
| (3), p. 498 | `v(κ, θ) = sup Σᵢ θᵢ Wᵢ(γᵢ, z′ᵢ)` over `z′ ∈ U(κ′)`, `(Σᵢ γᵢ, κ′) ∈ Φ(κ)` | `mcSeqCons`, `mc_eq3_set`, `mc_eq3` |
| Exercise 16.7(c), p. 498 | `z ∈ U(κ)` iff `v(κ, θ) ≥ θ·z` for all `θ ∈ Δᴵ` | `ex_16_7c_onlyIf`, `mc_exists_simplex_separating`, `mc_isClosed_lowerHull`, `mc_mem_of_forall_support`, `mcUtilSet_comprehensive`, `ex_16_7c`, `mcEx_strict`, `ex_16_7c_counterexample`; under (T8): `mcUtilSet_isClosed`, `ex_16_7c_of_bound` |
| (4), p. 498 | `v` solves the functional equation (4) | `mcSupport_admissible`, `mc_eq4`, `mc_eq4_of_bound` |
| p. 498 | The space `F` and the operator `T` | `MCInF`, `mcUpper`, `mcConstraint`, `mcObjective`, `mcOperator`, `mcSupportType`, `MCAdmissible`, `mcOperator_supportType`, `mcOperator_admissible` |
| Exercise 16.7(d), p. 499 | Computing `Tf` maximises a continuous function over a compact convex set | `mcConstraint_nonempty`, `ex_16_7d_compact`, `mcObjective_continuousOn`, `ex_16_7d_exists_max`, `ex_16_7d_convex`, `mcObjective_concave`, `mcExFd`, `ex_16_7d_counterexample` |
| Exercise 16.7(e), p. 499 | `T : F → F` | `mcOperator_nonneg`, `mcOperator_bdd`, `mcExFe`, `mcExFe_inF`, `ex_16_7e_counterexample`; corrected: `mcSimplex_isCompact`, `mc_uniform_of_tendsto`, `mcObjective_tendsto`, `mcConstraint_uhc`, `mcConstraint_lhc`, `mcOperator_tendsto`, `mcOperator_continuousOn`, `ex_16_7e` |
| Exercise 16.7(f), p. 499 | `T` is a contraction of modulus `β = maxᵢ βᵢ`, by Blackwell's conditions; the hint `𝒰ᵃ = B` | `mcOperator_mono`, `mcUpper_isCompact`, `convex_mcUpper`, `ex_16_7f_hint`, `mcOperator_discount`, `ex_16_7f`; counterexamples on `F`: `mcExG`, `mcExG_inF`, `ex_16_7f_hint_counterexample`, `ex_16_7f_counterexample` |
| p. 499 | Draw `𝒰` and `𝒰ᵃ` for `I = 2` | Not formalised (a drawing) |
| p. 499 | A unique `v ∈ F` solves (4) | `mcSupportType_of_tendsto`, `ex_16_7f_exists_fixed`, `ex_16_7f_unique`, `mc_exists_beta`, `ex_16_7e_fixed`; under (T8) the support function is in `F`: `mcSupport_inF` |
| Exercise 16.7(g), p. 499 | The policy correspondence of (4) is upper hemicontinuous and convex-valued | `mcPolicy`, `mcPolicy_value`, `mcPolicy_nonempty`, `mcSupport_concave`, `ex_16_7g_convex_of_concave`, `ex_16_7g`, `ex_16_7g_uhc`, `ex_16_7g_support` |
| p. 499 | Do allocations generated by the policy solve (2)? "Try it!" | `mc_support_unique_fixed`, `mc_support_unique_fixed_of_bound` |
| (not in the book) | A technology and an aggregator for the counterexamples | `mcBox`, `mcBox_tech`, `mcEx_mem_interior`, `mcExW`, `mcExW_agg`, `mcExU`, `mcExU_fixed`, `mcExW2`, `mcExU2` |

## §16.8 Bibliographic notes

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 499–500 | Sources: Prescott and Mehra (1980), Kydland and Prescott (1982), Long and Plosser (1983), Lucas (1978), Brock (1982), Modigliani and Miller (1958), Hirshleifer (1966), Samuelson (1965), Fama (1965), Mehra and Prescott (1985), Lucas and Prescott (1971), Prescott and Rios-Rull (1988), Gilles, Marshall and Sonstelie (1987), Lucas and Stokey (1984), and others | Not formalised |

## Results from earlier chapters

| Source | Claim | Lean |
| --- | --- | --- |
| §15.2, p. 452 | Economies, feasibility, Pareto optima, competitive equilibria | `Feasible`, `ParetoOptimal`, `CompetitiveEq`, `LocalNonsatiation`, `aggTech` (module `Economy`, carried) |
| Assumptions 15.1–15.5, p. 455 | Convexity, continuity, interior point | `Assumption15_1`, `Assumption15_2`, `Assumption15_3`, `Assumption15_4`, `Assumption15_5` (carried) |
| Theorem 15.3, p. 453 | The First Welfare Theorem | `theorem_15_3` (carried) |
| Theorem 15.4 and Remark, pp. 455–457 | The Second Welfare Theorem; a cheaper point gives an equilibrium | `SupportsAllocation`, `theorem_15_4`, `remark_cheaper_point` (carried) |
| Lemma 15.5, p. 464 | The regular part `ψ` of `φ` | `seqTrunc`, `seqRegularPart`, `lemma_15_5` (carried) |
| Assumptions 15.6–15.7, p. 465 | Truncation | `Assumption15_6`, `Assumption15_7` (carried) |
| Theorem 15.6, p. 466 | `ψ` supports | `theorem_15_6`, `theorem_15_6_competitiveEq` (carried) |
| Exercise 15.10 | Aggregators and their fixed points | `IsAggregator`, `IsAggregatorFixedPoint` (carried) |
| Lemma 15.7, Theorem 15.8 | Prices on `L∞` | `lemma_15_7`, `theorem_15_8` (carried) |
| (8), Assumptions 15.8′–15.9′, Theorem 15.9, p. 470 | Time and uncertainty combined | `LinftyTimeState`, `Assumption15_8'`, `Assumption15_9'`, `theorem_15_9` (carried) |
| Theorems 3.2, 3.6, 3.8 | Contraction mapping theorem; Theorem of the Maximum | `GrowthCertaintyDD.theorem_3_2`, `GrowthCertaintyDD.theorem_3_6`, `GrowthCertaintyDD.theorem_3_8` (carried) |
| Theorems 4.2–4.10, 4.15 | Principle of Optimality, bounded returns, concavity, Benveniste–Scheinkman, Euler equations | `GrowthCertaintyDD.theorem_4_2` … `GrowthCertaintyDD.theorem_4_10`, `GrowthCertaintyDD.theorem_4_15` (carried) |
| Exercise 5.1 | The one-sector growth model: value, policy, interiority | `GrowthCertaintyDD.ex_5_1ab`, `GrowthCertaintyDD.ex_5_1c`, `GrowthCertaintyDD.ex_5_1d`, `GrowthCertaintyDD.ex_5_1d_interior` (carried) |
| §6.1, Exercise 6.1, Proposition 6.1 | First-order and envelope conditions; monotone convergence of the policy to `k*` | `GrowthCertaintyDD.GrowthDyn`, `GrowthCertaintyDD.ex_6_1a`, `GrowthCertaintyDD.ex_6_1b`, `GrowthCertaintyDD.prop_6_1`, `GrowthCertaintyDD.Setting61`, `GrowthCertaintyDD.exists_setting61` (carried) |
