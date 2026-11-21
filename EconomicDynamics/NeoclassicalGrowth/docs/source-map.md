# Source map: Miao Chapter 14

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 14,
Neoclassical Growth Models, pp. 455–508. Lean names are relative to `Miao.NeoclassicalGrowth`.
Calibration, Dynare runs, impulse-response figures and data comparisons are recorded as not
formalised. Departures from the book are in [corrections](corrections.md).

## Introduction and §14.1

### Introduction (p. 455)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 455 | History of growth theory (Solow–Swan, Ramsey, Cass–Koopmans, Brock–Mirman, Kydland–Prescott) | Not formalised: no mathematical content |

### §14.1.1 A basic Ramsey model: primitives

| Source | Claim | Lean |
| --- | --- | --- |
| (14.1), p. 456 | Utility `∑ βᵗgₙᵗu(c_t, n_t)` | `rmPlanGain`, `RMPlanNFI`, `rm_planner_nfi_of_optimal` |
| p. 456 | `lim_{c→0} u(c, ·) = ∞` (corrected to `u_c → ∞`) | `rm_inada_u_misprint`, `rm_log_inada` |
| p. 457 | `F` homogeneous of degree one, `lim_{K→∞} F(K, 1) = 0` (corrected to `F₁ → 0`), `lim_{K→0} F₁ = ∞` | `rm_inada_F_misprint`, `rm_cd_inada_zero`, `rm_cd_inada_top` |
| p. 457, footnote 1 | Labour-augmenting vs other technical progress | Not formalised: remark, no derivation in the text |
| (14.2), p. 458 | `gₙk_{t+1} = (1 − δ)k_t + i_t` | `rm_clear_percapita`, `rmPlanC` |
| p. 459 | Constant returns: `Π = 0` (Euler's theorem) | `rm_euler_homogeneous`, `rm_zero_profit` |
| p. 459 | Partial derivatives homogeneous of degree zero (used for detrending) | `rm_partial1_homog_zero`, `rm_partial2_homog_zero` |
| (14.5), p. 459 | KPR utility `c^{1−σ}v(n)/(1 − σ)`: marginal utilities and their scaling | `rmKprU`, `rmKprUc`, `rmKprUn`, `rm_kpr_hasDerivAt_c`, `rm_kpr_hasDerivAt_n`, `rm_kpr_uc_scale`, `rm_kpr_un_scale`, `rm_kpr_mrs_scale` |
| (14.6), p. 459 | `ln c + v(n)` | `rm_log_hasDerivAt_c`, `rm_log_uc_scale`, `rm_log_mrs_scale` |
| p. 459 | KPR (1988): (14.5)–(14.6) are necessary for balanced growth | Not formalised: cited result, not derived in the text (sufficiency is `rm_detrend_planner`, `rm_balanced_growth`) |

### §14.1.1 Arrow–Debreu equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| p. 458 | Household first-order conditions (`c_t`, `n_t`, `k_{t+1}`) | `RMADFOC` |
| p. 458 | Transversality `lim q_t⁰k_{t+1} = 0` | `rm_ad_tvc_iff` |
| (14.3), p. 458 | Firm's first-order conditions `F_K = R^k`, `AF_N = w` | `eq_14_3`, `RMFirmFOC` |
| (14.4), p. 459 | Market clearing | `RMClear`, `rm_clear_percapita` |
| pp. 459–460 | The equilibrium system and its detrended form (Euler corrected) | `rm_ad_euler`, `rm_detrend_planner`, `rm_detrend_prices`, `rm_detrend_euler_misprint` |

### §14.1.1 Households own capital

| Source | Claim | Lean |
| --- | --- | --- |
| (14.7)–(14.8), p. 461 | Euler equation and labour condition | `RMHHFOC`, `rm_ad_euler` |
| (14.9), p. 461 | Transversality condition | `rm_ad_tvc_iff` |
| p. 461 | The system is identical to the Arrow–Debreu one | `rm_ad_euler`, `rm_ad_of_hh`, `rm_ad_tvc_iff` |

### §14.1.1 Firms own capital

| Source | Claim | Lean |
| --- | --- | --- |
| (14.10), p. 462 | Firm's accumulation equation | `rm_firm_capital_foc` (in its objective) |
| (14.11), p. 462 | `V_t = D_t + βu_c(c_{t+1})/u_c(c_t) V_{t+1}` | `eq_14_11` |
| (14.12), p. 462 | Forward solution | `eq_14_12`, `rm_value_partial` |
| (14.13), pp. 462–463 | No-bubble condition derived from the household's TVC | `eq_14_13` |
| p. 463 | Pricing kernel `M_{t,t+j} = βʲu_c(c_{t+j})/u_c(c_t)` | `rmKernel`, `rm_kernel_zero`, `rm_kernel_mul` |
| (14.14), p. 463 | `Q_t = 1`, `Q_t = M_{t,t+1}[F_K + (1 − δ)Q_{t+1}]` | `rm_firm_capital_foc` |
| p. 463 | (14.7) and (14.14) are equivalent; same allocations | `eq_14_14_iff_eq_14_7` |
| pp. 463–464 | Stock return `V_{t+1}/(V_t − D_t) = R^k_{t+1} + 1 − δ` | `rm_stock_return` |

### §14.1.1 Social planner's problem

| Source | Claim | Lean |
| --- | --- | --- |
| p. 464 | Planner's problem; per-capita resource constraint | `rmPlanC`, `RMPlanFeasible`, `RMPlanNFI`, `rm_planner_resource`, `rm_planner_nfi_of_optimal` |
| p. 464 | Planner's Euler equation | `rm_planner_euler` |
| p. 464 | Planner's intratemporal condition (corrected: factor `A_t`) | `rm_planner_intratemporal`, `rm_planner_intratemporal_misprint` |
| p. 464 | Resource constraint, TVC (14.9) | `RMPlannerFOC`, `rm_ad_tvc_iff` |
| p. 465 | Detrended planner's system | `RMDetrendedFOC`, `rm_detrend_planner` |
| p. 465 | Competitive allocations are Pareto optimal | `rm_ce_planner` |
| p. 465 | The optimum is supported by prices in each arrangement | `rm_planner_ce` |
| p. 464, footnote 2 | Other arrangements | Not formalised: reference |

### §14.1.1 Recursive competitive equilibrium

| Source | Claim | Lean |
| --- | --- | --- |
| (14.15)–(14.16), p. 466 | Price functions, household's Bellman problem, law of motion | `rm_rce_sequential` (hypotheses) |
| pp. 466–467 | RCE conditions (i)–(iii) generate a sequential equilibrium | `rm_rce_sequential` |
| p. 467 | Converse and the choice of state variables | Not formalised: informal remark |

### §14.1.1 Steady state, phase diagram, saddle path (derivations around pp. 459, 465)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 459, 465 | Steady state of the detrended system; modified golden rule | `rm_steady_state_iff`, `rm_FK_ratio`, `rm_mgr_pos` |
| p. 465 | Existence and uniqueness of the steady-state capital–labour ratio | `rm_steady_ratio_exists_unique` |
| — | Comparative statics of the steady state in `β, δ, g_a, σ` | `rm_steady_ratio_anti`, `rm_cs_beta`, `rm_cs_delta`, `rm_cs_ga`, `rm_cs_sigma` |
| p. 459 | Balanced growth: `Y, K, I, C` grow at `g_ag_n`, `w` at `g_a`, `R^k` constant | `rm_balanced_growth` |
| — | Worked example: log utility, Cobb–Douglas | `rmCD`, `rmCDK`, `rmCDN`, `rm_cd_FK_hasDerivAt`, `rm_cd_FN_hasDerivAt`, `rm_cd_homog`, `rm_cd_FK_strictAnti`, `rm_cd_chi_pos`, `rm_cd_log_steady` |
| — | Phase diagram: `Δc̃ = 0` and `Δk̃ = 0` loci | `rm_phase_c`, `rm_phase_k` |
| — | Linearisation of the detrended system | `rm_lin_taylor`, `rm_lin_reduced` |
| — | Eigenvalues `0 < λ₁ < 1 < λ₂` | `rm_lin_trace_det`, `rm_lin_roots` |
| — | Saddle path: unique, convergent, upward sloping, monotone; others unbounded | `rm_lin_saddle`, `rm_lin_saddle_monotone` |

### §14.1.2 Incorporating fiscal policy

| Source | Claim | Lean |
| --- | --- | --- |
| (14.17), p. 468 | Household problem; first-order conditions | `RMTaxes`, `RMFiscalPath`, `RMFiscalEq`, `rm_fiscal_euler`, `rm_fiscal_labour` |
| p. 468 | Firm's problem `V_t = max (1 − τᵈ)D_t + βΛ_{t+1}/Λ_t V_{t+1}` | `rm_fiscal_value_recursion` |
| (14.18)–(14.20), pp. 468–469 | Dividends, accumulation, `Q = 1 − τᵈ`, the capital condition | `eq_14_20`, `RMFiscalEq` |
| p. 469 | Government budget constraint (corrected) and resource constraint | `rmGovBudget`, `rm_gov_budget_misprint`, `rm_walras` |
| Proposition 14.1.1, p. 469 | `V_t − (1 − τᵈ_t)D_t = (1 − τᵈ_t)K_{t+1}` | `proposition_14_1_1` |
| Proof of Prop. 14.1.1, pp. 469–470 | One-step identity (corrected), forward sum (corrected), ex-dividend value | `rm_prop_14_1_1_step`, `rm_prop_14_1_1_misprint`, `rm_prop_14_1_1_sum`, `rm_prop_14_1_1_exdiv` |
| (14.21), p. 470 | Permanent `τᵈ`: capital condition free of `τᵈ` | `eq_14_21` |
| p. 470 | Distribution tax changes `Q` and equity value but not the allocation | `rm_distribution_tax_neutral` |
| p. 470 | With other distortionary taxes balancing the budget, `τᵈ` is distortionary | Not formalised: informal remark (depends on which tax adjusts) |
| pp. 470–471 | `D_t < 0`, capital gains taxes, Poterba–Summers, Gourio–Miao | Not formalised: verbal discussion of other models and empirical work |
| — | Temporary changes in `τᵈ` distort investment | `rm_temporary_distribution_tax`, `rm_temporary_distribution_tax_distorts` |
| p. 471 | Lump-sum taxes as the residual; Ricardian equivalence | `rm_walras`, `rm_ricardian` |
| p. 471 | Without lump-sum taxes there may be many equilibria | Not formalised: informal remark |

### Exercises 14.1–14.2 (p. 507)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 14.1 | §14.1.2 in Arrow–Debreu and household-capital form; same allocation | `RMFiscalAlloc`, `RMHKPath`, `RMHKEq`, `RMADPath`, `RMADEq`, `ex_14_1_firm`, `ex_14_1_hk`, `ex_14_1_ad`, `ex_14_1` |
| Exercise 14.2 | Steady state of §14.1.2 | `rmConstPath`, `ex_14_2`, `rm_fiscal_eq_example`, `ex_14_2_mgr`, `ex_14_2_value`, `ex_14_2_corporate_tax`, `ex_14_2_cd` |

## §14.2 and §14.3.1

### §14.2 The planner's problem and its first-order conditions (pp. 471–472)

| Source | Claim | Lean |
| --- | --- | --- |
| (14.22), p. 472 | Period utility `ln C + χ ln(1 − N)`; expected discounted utility | `rb_u`, `rb_value` |
| (14.23), p. 472 | Cobb–Douglas output; marginal products; `R_k = αY/K`, `w = (1 − α)Y/N`; Euler's theorem; concavity | `rb_Y`, `rb_MPK`, `rb_MPL`, `rb_MPK_eq`, `rb_MPL_eq`, `rb_euler_thm`, `rb_Y_pos`, `rb_MPK_pos`, `rb_MPL_pos`, `rb_cd_tangent`, `rb_cd_tangent'`, `rb_hasDerivAt_Y_K`, `rb_hasDerivAt_Y_N` |
| (14.23)–(14.24), p. 472 | Feasible allocations (investment eliminated) | `rb_IsFeasible` |
| (14.25), p. 472 | `ln z_t = ρ ln z_{t−1} + σε_t`, iterated | `rb_lnz`, `eq_14_25_iter` |
| (14.27), p. 472 | Intratemporal condition; necessary and sufficient for the static labour choice | `eq_14_27`, `rb_static`, `rb_labour_suff`, `rb_labour_nec`, `rb_hasDerivAt_static`, `rb_log_tangent`, `rb_u_tangent` |
| (14.26), p. 472 | Euler equation from the one-step variation in `K_{t+1}` (finite successor distribution): necessary and sufficient | `rb_node`, `eq_14_26_node`, `rb_euler_node_suff`, `rb_euler_node_nec` |
| (14.26), p. 472 | Euler equation with Mathlib's conditional expectation | `rb_A`, `eq_14_26` |
| p. 472 | "The usual transversality condition also holds" | `rb_TVC` |
| p. 472 | (14.26), (14.27) and transversality are sufficient for optimality | `rb_telescope`, `rb_integral_euler`, `rb_suff_core`, `rb_planner_pointwise`, `rb_planner_suff`, `rb_planner_optimal` |
| p. 472 (with `δ = 1`) | A concrete optimal plan (Long–Plosser): non-vacuity of the hypotheses | `rb_bmN`, `rb_bmK`, `rb_bmC`, `rb_bmN_mem`, `rb_bmK_pos`, `rb_bm_solution` |
| p. 482 | Solow residual `SR_t = ln Y_t − α ln K_t − (1 − α) ln N_t = ln z_t` | `rb_solow_residual` |

### §14.2 Decentralised equilibrium (p. 472, with pp. 460–461)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 472 | Firm: marginal-product prices maximise profit, zero profit; conversely | `rb_profit`, `rb_firm_optimal`, `rb_firm_foc` |
| p. 460 | Household budget, Euler equation, labour supply (14.36) | `rb_IsHHFeasible`, `rb_HHEuler`, `rb_household_pointwise` |
| p. 460 | Household's conditions plus transversality are sufficient for its optimum | `rb_household_suff`, `rb_household_optimal` |
| pp. 460–461 | Sequential competitive equilibrium | `rb_IsSCE` |
| p. 472 | `R_kt = αz_tK_t^{α−1}N_t^{1−α}`, `w_t = (1 − α)z_tK_t^αN_t^{−α}`; equilibrium iff planner's conditions | `rb_sce_iff` |
| p. 472 | "Pareto optimality and decentralized competitive equilibrium still applies" | `rb_sce_optimal` (first welfare theorem), `rb_sce_iff` (`←`, second), `rb_bm_sce` |

### §14.2 Steady state and calibration (pp. 473–474)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 473 | Steady-state Euler equation iff `K/N = (α/(1/β − (1 − δ)))^{1/(1−α)}` | `rb_rk`, `rb_kn`, `rb_rk_pos`, `rb_kn_pos`, `rb_kn_pow`, `rb_MPK_ratio`, `rb_MPL_ratio`, `rb_Y_ratio`, `rb_MPK_kn`, `rb_ss_euler`, `rb_ss_KN` |
| p. 473 | Factor prices `R_k = αY/K = α(K/N)^{α−1}`, `w = (1 − α)(K/N)^α` | `rb_ss_prices` |
| p. 473 | `I = δK = δ(K/N)N`, `Y = (K/N)^αN`, `C` from (14.23); great ratios | `rb_ss_IY_levels`, `rb_sc`, `rb_sc_pos`, `rb_sc_lt_one`, `rb_ss_ratios` |
| (14.28), p. 473 | `χ = (1 − α)(K/N)^α(1 − N)/C`; closed form | `eq_14_28`, `rb_ss_chi` |
| p. 473 | One-to-one mapping between `χ` and `N` | `rb_ssN`, `rb_ss_N_iff`, `rb_ss_N_mem`, `rb_ss_chi_strictAnti` |
| p. 473 | Existence and uniqueness of the steady state | `rb_ss_exists_unique` |
| p. 474 | Calibration: `χ` at `α = 0.33`, `β = 0.99`, `δ = 0.025`, `N = 0.33` | `rb_calib_chi`, `rb_calib_chi_ne` |
| (14.29)–(14.30), p. 474 | OLS estimation of `ρ`, `σ` | Not formalised: empirical |

### §14.2 Log-linearised system (pp. 474–480)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 474 | Log deviations; total differentiation along `Xe^{sX̂}` | `rb_hasDerivAt_exp_mul`, `rb_Y_exp`, `rb_MPK_exp`, `rb_MPL_exp`, `rb_hasDerivAt_log_one_sub` |
| p. 475 | (14.27) in logs, total differentiation | `rb_zeta`, `eq_14_27_loglin` |
| (14.31), p. 475 | `N̂ = (ẑ + αK̂ − Ĉ)/(α + ζ)` | `eq_14_31` |
| p. 475 | Total differentiation of the resource constraint; solving for `K̂_{t+1}` | `rb_resource_loglin`, `rb_resource_solved` |
| (14.32), p. 475 | `K̂_{t+1}` in `K̂_t`, `ẑ_t`, `Ĉ_t` | `rb_p`, `rb_g`, `rb_q`, `eq_14_32` |
| p. 476 | Total differentiation of the Euler equation; the linearised equation | `rb_euler_loglin`, `rb_euler_loglin_eq` |
| (14.33), p. 476 | Euler equation with (14.31) substituted | `rb_a`, `rb_b`, `rb_c`, `eq_14_33_det`, `eq_14_33` |
| (14.34), p. 476 | Deterministic phase-diagram system (second line corrected) | `eq_14_34_K`, `eq_14_34_C`, `eq_14_34_printed_false` |
| p. 477 | Isocline `ΔĈ = 0`, downward sloping; `Ĉ` falls to its right | `rb_coeff_pos`, `rb_b_eq`, `rb_c_eq`, `rb_isocline_C`, `rb_isocline_C_sign` |
| (14.35), p. 477 | Isocline `ΔK̂ = 0`, upward sloping; `K̂` falls above it | `eq_14_35`, `eq_14_35_sign` |
| pp. 477–478 | Saddle: eigenvalues `0 < λ₁ < 1 < λ₂` | `rb_m21`, `rb_m22`, `rb_det_system`, `rb_det_M`, `rb_char_one_neg`, `rb_lam1`, `rb_lam2`, `rb_saddle_roots`, `rb_saddle_eigen` |
| p. 478 | Unique `Ĉ₀` on the saddle path; convergence (deterministic) | `rb_left_eig`, `rb_saddle_det` |
| pp. 476–478 | Stochastic system with (14.25): unique stable solution (Blanchard–Kahn) | `rb_W2`, `rb_P2`, `rb_R2`, `rb_split2`, `rb_G2`, `rb_IsLinRBC`, `rb_Wrbc`, `rb_Grbc`, `rb_matAct_W2`, `rb_matAct_G2`, `rb_bk_iff`, `rb_saddle_stoch` |
| (14.36), p. 478 | Labour supply; log-linearised `ζN̂ = −Ĉ + ŵ` | `eq_14_36_loglin` |
| (14.37), p. 478 | Labour demand `ŵ = ẑ + αK̂ − αN̂` | `eq_14_37` |
| p. 478, Figure 14.2 | Intersection; slopes and shifts | `rb_labour_market`, `rb_labour_slopes` |
| p. 478 | `Ŷ = αK̂ + (1 − α)N̂ + ẑ`, `R̂_k = Ŷ − K̂` | `rb_output_loglin`, `rb_rental_loglin` |
| p. 479 | Stock return `R̂^s = R̂_k` (corrected) | `rb_stock_return_loglin`, `rb_stock_return_printed_false` |
| p. 480 | Risk-free rate `r̂^f_{t+1} = E_tĈ_{t+1} − Ĉ_t` | `rb_riskfree_loglin`, `rb_riskfree_eq`, `rb_riskfree_E` |
| p. 480 | Investment from the resource constraint | `rb_investment_loglin` |

### §14.2 Business cycle statistics and TFP shocks (pp. 480–487)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 480–483, Table 14.1 | Data, HP filter, model moments | Not formalised: computational/empirical |
| p. 484 | Permanent shock: new steady state `K̂* = Ĉ* = ẑ/(1 − α)`; hours unchanged; levels scale with `z̄^{1/(1−α)}` | `rb_permanent_ss`, `rb_ss_permanent` |
| p. 484, Figure 14.3 | Both isoclines shift up | `rb_permanent_shift` |
| p. 484 | Saddle path to the new steady state; capital and consumption rise, interest rate up, investment up | `rb_permanent_path` |
| p. 484, Figure 14.4 | Wage rises, hours ambiguous (given `Ĉ₀ > 0`) | `rb_labour_market`, `rb_labour_slopes`, `rb_consumption_channel` (comparative statics only) |
| pp. 484–485 | Temporary shock: sizes of impact responses | Not formalised: relies on numerical comparison of saddle paths (Figures 14.5–14.6) |
| pp. 485–486, Figures 14.5–14.6 | Persistence and impulse responses | Not formalised: computational |

### §14.3.1 Various utility functions (pp. 487–493)

| Source | Claim | Lean |
| --- | --- | --- |
| (14.38), p. 488 | KPR utility, of the form (14.5) | `rb_u38`, `rb_u38_kpr` |
| (14.39), p. 488 | KPR utility, of the form (14.6) | `rb_u39`, `rb_u39_kpr` |
| p. 489 | `γ = 1` reduces (14.38) to (14.22) (corrected) | `rb_u38_limit`, `rb_u38_printed_no_limit` |
| p. 489 | `u_c`, `u_n`, MRS of (14.38); "we still obtain `χ = 1.75`" | `rb_u38_uc`, `rb_u38_un`, `rb_u38_mrs`, `rb_u38_intratemporal` |
| pp. 459, 488 | KPR class compatible with balanced growth | `rb_u38_homog`, `rb_u38_bgp`, `rb_u39_mrs` |
| p. 488 | `1/ν` is the Frisch elasticity | `rb_u39_frisch` |
| p. 489 | `ν = 0`: indivisible labour (Hansen–Rogerson lotteries) | `rb_lottery` |
| p. 489, Figure 14.7 | Larger consumption response: smaller hours and output, larger wage response | `rb_consumption_channel` |
| p. 489, Figure 14.8 | Indivisible labour: larger hours response, smaller wage response | `rb_u39_supply_loglin`, `rb_nu_responses` |
| p. 489 | Impulse responses for different `γ`, `ν` | Not formalised: computational |
| (14.40), pp. 489–490 | GHH utility: `G′(n) = w`, no wealth effect on labour supply | `rb_ghh_mrs`, `rb_ghh_hours` |
| p. 488 | GHH outside the KPR class | `rb_ghh_not_kpr` |
| pp. 490–492 | Habit formation: marginal utility `Λ_t` | `rb_habit_mu` |
| pp. 492–493, Figure 14.9 | Habit impulse responses | Not formalised: computational |

## §14.3.2–§14.3.4 and Exercises 14.3–14.7

### Infrastructure (`RXCopied`, `RXTree`)

| Source | Claim | Lean |
| --- | --- | --- |
| §8.6.2 (copied) | Partial derivatives, chain rule, Euler's theorem for homogeneous functions | `rx_HasPartials`, `rx_HasPartials.comp`, `rx_euler_homog` |
| §13.1 (as used in §14.3) | Event tree, conditional expectation `Eₜ`, linearity, taking out what is known; deterministic and coin trees | `RXTree`, `rx_detTree`, `rx_coinTree`, `rx_E`, `rx_Es`, `rx_E_eq_Es`, `rx_E_det`, `rx_E_coin`, `rx_E_add`, `rx_E_const`, `rx_E_mul_left`, `rx_Es_add`, `rx_Es_mul_left`, `rx_Es_const` |
| — | `Eₜ[M_{t,t+n}x_{t+n}]`, forward iteration and limit of a pricing recursion | `rx_pv`, `rx_pv_one`, `rx_pv_add`, `rx_pv_sum`, `rx_pv_iterate`, `rx_pv_limit` |
| — | First-order condition of a node problem; homogeneous ⇒ derivative = average | `rx_node_foc`, `rx_homog_hasDerivAt` |

### §14.3 introduction (p. 493)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 493 | Extensions on the preference and technology sides | Not formalised (expository) |

### §14.3.2 Capacity utilization (`RXCapacity`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 493 | `δ(u) = δ₀u^{δ₁}`, `δ′`, increasing and convex; `Y = z(Ku)^α N^{1−α}` | `rx_dep`, `rx_dep_hasDerivAt`, `rx_dep_strictMonoOn`, `rx_dep_strictConvexOn`, `rx_cuY`, `rx_cuY_hasDerivAt_K`, `rx_cuY_hasDerivAt_u` |
| p. 493 | Planner: `u′(Cₜ) = βEₜu′(C_{t+1})(1 − δ(u_{t+1}) + αY_{t+1}/K_{t+1})` | `rx_cu_planner_euler` |
| p. 493 | Planner: `δ′(uₜ) = αYₜ/(Kₜuₜ)` | `rx_cu_planner_util` |
| p. 494 | Firm: `R_{kt} = αYₜ/(Kₜuₜ)` (and the wage) | `rx_cu_firm_foc` |
| p. 494, (14.41) | Household: `δ′(uₜ) = R_{kt}` | `eq_14_41` |
| p. 494 | Household Euler equation; decentralised = planner conditions | `rx_cu_household_euler`, `rx_cu_decentralised_eq_planner` |
| p. 493 | Utilization responds to TFP shocks (amplification) | `rx_cu_util_closed`, `rx_cu_util_increasing`, `rx_cu_amplification` |
| p. 494 | Calibration: `u = 1` pins down `δ₀δ₁`, then `δ₁`; `δ₀ = 0.025`, `β = 0.99` gives `δ₁ = 139/99` | `rx_cu_calibration`, `rx_cu_calibration_value` |

### §14.3.3 Capital adjustment costs (`RXAdjustment`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 495, (14.42) | `K_{t+1} = (1 − δ)Kₜ + Φ(Iₜ, Kₜ)`, `Φ_I > 0`, `Φ_II < 0` | hypotheses of `rx_uzawa_euler`; `rx_HasPartials.fst`, `rx_HasPartials.snd` |
| p. 495, (14.43) | `Φ = ϕ(I/K)K`: homogeneity, partials, `Φ_II = ϕ″/K < 0` | `rx_Phi`, `rx_Phi_homog`, `rx_Phi_partials`, `rx_Phi_II` |
| p. 495 | Normalisations give `I/K = δ`, `Q = 1` in steady state; `κ` does not affect it | `rx_Phi_steady`, `eq_14_43_steady`, `rx_kappa_neg` |
| p. 495 | A concrete `ϕ` with the normalisations | `rx_phiQuad`, `rx_phiQuad_normalised`, `rx_phiQuad_K` |
| p. 495, (14.44)–(14.45) | Planner's conditions `Ct`, `Nt`, `It`, `K_{t+1}` | `eq_14_45_N`, `rx_invest_foc`, `eq_14_45_K` (via `rx_inverse_partials`, `rx_uzawa_euler`, `rx_labour_foc`) |
| p. 496, (14.46) | Decentralisation 1: household conditions | `rx_dec1_labour`, `rx_invest_foc`, `rx_dec1_euler` |
| p. 497, (14.47) | Firm: `R_k = zF_K`, `w = zF_N` | `eq_14_47_foc` |
| p. 497 | Decentralisation 2: household's share and bond conditions | `rx_dec2_shares`, `rx_dec2_bonds` |
| p. 498, (14.48)–(14.49) | Firm's investment and capital conditions | `eq_14_48`, `eq_14_49` |
| p. 498 | No adjustment costs (`Φ = I`): `Q = 1` | `rx_no_adjustment_Q` |
| p. 498 | Capital supply/demand interpretation | Not formalised (interpretation) |
| pp. 499–500 | Decentralisation 3: capital producers, households | `rx_dec3_producer`, `rx_dec3_euler`, `rx_producer_profit` |
| p. 508, Ex 14.5 | The three decentralisations and the planner | `ex_14_5_dec1`, `ex_14_5_dec2`, `ex_14_5_budgets`, `ex_14_5_dec3_iff`, `rx_Es_pos`, `ex_14_5_dec3_counterexample`, `rx_Phi_K_pos`, `ex_14_5_dec3_corrected` |

### Proposition 14.3.1 and returns (`RXHayashi`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 498, Prop 14.3.1 = Ex 14.4 | `Qₜ = Pₜ/K_{t+1}` | `rx_div`, `rx_sdf`, `rx_hayashi_step`, `proposition_14_3_1` |
| p. 498 | `Pₜ = Eₜ[βΛ_{t+1}V_{t+1}/Λₜ]`, `V = D + P` | `rx_P_recursion` |
| p. 498, Prop 14.3.1 | `Qₜ = ∂Pₜ/∂K_{t+1}` (value homogeneous of degree one) | `rx_firmFeasible`, `rx_divPlan`, `rx_firmValue`, `rx_scale`, `rx_scale_feasible`, `rx_div_scale`, `rx_firmValue_homog`, `rx_pv_smul`, `rx_truncValue_homog`, `proposition_14_3_1_marginal` |
| p. 499 | `D_{t+1} = R_{k,t+1}K_{t+1} − I_{t+1}`; stock return = investment return | `rx_dividend_eq`, `rx_stock_return` |

### Investment adjustment costs (`RXInvestment`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 500, (14.50)–(14.51) | Firm's conditions with `G(Iₜ, I_{t−1})` | `eq_14_50`, `eq_14_51` |
| p. 500 | Eberly–Rebelo–Vincent: marginal Q may be replaced by average Q in the log-linear system | Not formalised (cited result, not derived) |
| p. 500, (14.52) | `G = (1 − S(I/I₋))I`: partials; `I/K = δ`, `Q = 1`, `κ` does not affect the steady state | `rx_G52`, `rx_G52_d1`, `rx_G52_d2`, `rx_G52_steady`, `rx_G52_diag`, `eq_14_52_steady`, `rx_g1`, `rx_g2`, `rx_g52_derivs` |
| p. 508, Ex 14.6 | Log-linearised investment dynamics, (14.43) | `rx_hasDerivAt_exp`, `rx_hasDerivAt_exp1`, `rx_ratio_path`, `rx_hasDerivAt_rate`, `ex_14_6_invest_43`, `ex_14_6_invest_43_solved`, `ex_14_6_capital_43`, `ex_14_6_Q_43`, `ex_14_6_Q_43_solved` |
| p. 508, Ex 14.6 | Log-linearised investment dynamics, (14.52) | `ex_14_6_invest_52`, `ex_14_6_invest_52_solved`, `ex_14_6_Q_52`, `ex_14_6_capital_52` |
| p. 508, Ex 14.6 | "Discuss the differences" | `ex_14_6_differences` |

### §14.3.4 Stochastic trends (`RXTrend`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 501 | Deterministic trend `Y = zK^α(AN)^{1−α}` | Not formalised (definition only, no derivation) |
| p. 501 | `ln zₜ = μ_z + ln z_{t−1} + σεₜ`, `z_{−1} = 1` | `rx_lnz_walk` |
| p. 501 | Detrended system (all six equations) | `rx_trend_scale`, `rx_detrend_euler`, `rx_detrend_labour`, `rx_detrend_resource`, `rx_detrend_output`, `rx_detrend_capital`, `rx_detrend_rental`, `rx_detrend_wage` |
| p. 502 | Transforming back; impulse responses of original variables | `rx_detrend_back` |
| p. 501 | Steady state of the detrended system: existence and uniqueness | `rx_trend_exp_G`, `rx_trendSS`, `rx_trR`, `rx_trk`, `rx_try`, `rx_tri`, `rx_trc`, `rx_trN`, `rx_rpow_kN`, `rx_trk_pow`, `rx_trend_steady_unique`, `rx_trend_steady_exists` |
| pp. 501–503, Fig 14.10 | Calibration, Dynare impulse responses, "hours rise by less" | Not formalised (computational/numerical) |
| p. 503 | Investment-specific shocks: `Qₜ = 1/vₜ` and the Euler equation; price falls with `v` | `rx_linear_partials`, `rx_ist_foc`, `rx_ist_price` |
| p. 505 | Government spending: steady-state `K/N` independent of `Ḡ` | `rx_gov_kn` |
| pp. 503–507, Figs 14.11–14.13 | Impulse responses to investment-specific, government and preference shocks, and their discussion | Not formalised (computational/numerical) |

### Exercises 14.3–14.7

| Source | Claim | Lean |
| --- | --- | --- |
| p. 507, Ex 14.3 | Capacity-utilization steady state (mathematical content); Dynare part | `ex_14_3_utilization`, `ex_14_3_utilization_exists`, `ex_14_3_u_eq_one`, `ex_14_3_capital_labour`; Dynare: not formalised (computational) |
| p. 508, Ex 14.4 | Prove Proposition 14.3.1 | `proposition_14_3_1`, `proposition_14_3_1_marginal` |
| p. 508, Ex 14.5 | Three decentralisations give the same allocation | `ex_14_5_dec1`, `ex_14_5_dec2`, `ex_14_5_budgets`; false for decentralisation 3: `ex_14_5_dec3_iff`, `ex_14_5_dec3_counterexample`, corrected `ex_14_5_dec3_corrected` |
| p. 508, Ex 14.6 | Log-linearised investment dynamics under risk neutrality | see `RXInvestment` above |
| p. 508, Ex 14.7 | Two calibrated models, IRFs for several `κ` | Mathematical content: steady states independent of `κ` (`eq_14_43_steady`, `eq_14_52_steady`) and linearised systems (Ex 14.6); Dynare: not formalised (computational) |
