# Source map: Miao Chapter 16

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 16, Overlapping
Generations Models, pp. 529–557. Lean names are relative to `Miao.OverlappingGenerations`. The
exchange economy of §16.1 is `OXEconomy` (with preferences `OXPrefs`); the Diamond economy of
§16.2–16.3 is stated through `OPIsDiamondEqm` and `OPIsBubbleEqm`. Departures from the book are in
[corrections](corrections.md).

## Introduction and §16.1

### Setting (pp. 529–531)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 529 | Introduction (descriptive: OLG heterogeneity, inefficiency, fiat money, bubbles) | Not formalised (no claims beyond those of §16.1) |
| p. 530 | Preferences `u(c_t^t) + βu(c_{t+1}^t)`, `β ∈ (0, 1]`, `u' > 0`, `u'' < 0`, `u'(0+) = ∞`; a concrete (log) instance | `OXPrefs`, `OXPrefs.ox_U`, `ox_logPrefs`, `ox_logPrefs_spec` |
| p. 530 | Consequences of `u'' < 0` used below: tangent inequality, monotonicity, chord bound, FOC on a budget line, sufficiency of the Euler equation | `OXPrefs.ox_tangent`, `OXPrefs.ox_tangent_strict`, `OXPrefs.ox_u_strictMonoOn`, `OXPrefs.ox_u_lt`, `OXPrefs.ox_du_lt`, `OXPrefs.ox_chord`, `OXPrefs.ox_eventually_pos`, `OXPrefs.ox_foc`, `OXPrefs.ox_line_optimal`, `OXPrefs.ox_line_optimal_strict` |
| pp. 530–531 | The economy: `N_t = g_nN_{t−1}`, `M_t = g_mM_{t−1}`, endowments, transfers; a concrete instance | `OXEconomy`, `ox_exampleEconomy`, `ox_exampleEconomy_spec`, `OXEconomy.ox_N`, `OXEconomy.ox_M`, `OXEconomy.ox_τ`, `OXEconomy.ox_EU`, `OXEconomy.ox_N_pos`, `OXEconomy.ox_M_pos`, `OXEconomy.ox_N_succ`, `OXEconomy.ox_M_succ` |
| (16.1)–(16.2), p. 531 | Budget constraints of the young (value of money `q_t = 1/p_t`), and their price form | `OXEconomy.ox_Budget`, `OXEconomy.eq_16_1_16_2`, `OXEconomy.ox_budget_line` |
| p. 531 | Budget of the initial old; they consume their resources | `OXEconomy.ox_oldBudget`, `OXEconomy.ox_OldOptimal`, `OXEconomy.ox_oldOptimal_iff`, `OXEconomy.ox_oldBudget_eq` |
| p. 531, (16.3) | Optimality, (monetary / nonmonetary) equilibrium with market clearing | `OXEconomy.ox_Optimal`, `OXEconomy.ox_optimal_binds`, `OXEconomy.ox_IsEquilibrium`, `OXEconomy.ox_IsMonetary`, `OXEconomy.ox_IsNonmonetary` |
| p. 531 | With `p_t = ∞` autarky is an equilibrium (the nonmonetary equilibrium), and the only one | `OXEconomy.ox_autarky_isEquilibrium`, `OXEconomy.ox_nonmonetary_autarky` |
| (16.4), p. 531 | Euler equation `u'(c_t^t)/(βu'(c_{t+1}^t)) = p_t/p_{t+1} = R_{t+1}` | `OXEconomy.eq_16_4` |
| (16.5), p. 531 | `R_aut = u'(e₁)/(βu'(e₂))`, the implicit rate of autarky | `OXEconomy.ox_Raut`, `OXEconomy.eq_16_5` |
| p. 532 | `m̂_t = M_t/(N_tp_t)`; `c_t^t = e₁ − m̂_t`, `c_{t+1}^t = e₂ + g_nm̂_{t+1}`, `m̂_t > 0` | `OXEconomy.ox_mhat`, `OXEconomy.ox_mhat_eq`, `OXEconomy.ox_old_resources`, `OXEconomy.ox_monetary_alloc` |
| (16.6), p. 532 | `u'(e₁ − m̂_t)/(βu'(e₂ + g_nm̂_{t+1})) = R_{t+1} > R_aut` | `OXEconomy.eq_16_6`, `OXEconomy.ox_Raut_lt` |
| pp. 531–532 | The equilibrium difference equation in saving: monetary equilibria are exactly the solutions of the saving equation in `(0, e₁)` | `OXEconomy.ox_EulerRel`, `OXEconomy.ox_qOf`, `OXEconomy.ox_mhat_qOf`, `OXEconomy.ox_ofSaving_isMonetary`, `OXEconomy.ox_monetary_eulerRel` |

### A special case and multiple equilibria (pp. 532–536)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 532 | `z_t = m_tp_t/p_{t+1}`: the ray to a point of the offer curve has slope `R_{t+1}` | `OXEconomy.ox_offer_z` |
| p. 532 | The offer curve lies to the left of `e₁` | `OXEconomy.ox_offer_lt_e1` |
| pp. 532–534 | Euler equation `u'(e₁ − m_t) = βu'(m_tR_{t+1} + e₂)R_{t+1}` and `z_t = m_{t+1}` in equilibrium (`g_n = g_m = 1`) | `OXEconomy.ox_offer_equilibrium` |
| p. 533 | `dm_t/dR_{t+1}` by implicit differentiation | `OXPrefs.ox_offer_slope_m`, `OXPrefs.ox_offer_slope_m_eq` |
| p. 533 | `dz_t/dR_{t+1} = (m u''(c₁) − βu'(c₂)R)/(u''(c₁) + βR²u''(c₂)) > 0` | `OXPrefs.ox_offer_slope_z`, `OXPrefs.ox_offer_slope_z_pos` |
| pp. 533–534 | `dm_t/dR_{t+1} < 0` iff `βu'(c₂)(γ(c₂)z/c₂ − 1) > 0`; backward bending needs `γ(c₂) > 1`; `γ ≤ 1` gives an upward-sloping curve | `OXPrefs.ox_offer_backward_iff`, `OXPrefs.ox_offer_backward_necessary`, `OXPrefs.ox_offer_upward` |
| p. 534 | Nonmonetary steady state at the origin (zero saving iff `R = R_aut`); slope of the offer curve at the origin is `R_aut` | `OXEconomy.ox_offer_origin`, `OXEconomy.ox_offer_slope_origin` |
| p. 534 | Monetary steady states on the 45° line; one exists iff the slope at the origin is below one | `OXEconomy.ox_offer_steady_iff`, `OXEconomy.ox_offer_steady_exists_iff` |
| p. 534 | "A monetary steady state is unstable iff `|dm_{t+1}/dm_t| > 1`" (corrected) | `ox_fixed_unstable`, `ox_fixed_stable`, `ox_unstable_counterexample` |
| p. 535 | Paths to the left of `m*` converge to the nonmonetary steady state; to the right they exceed `e₁` (Figure 16.2) | Proved for the log economy: `OXEconomy.example_16_1_1_left`, `OXEconomy.example_16_1_1_right` |
| p. 535 | Inflation tends to the inverse of the slope at the origin (minus one) | `OXEconomy.ox_R_tendsto_Raut`, `OXEconomy.example_16_1_1_explosive` |
| p. 535 | Locally stable monetary steady state (`|f'| < 1`); indeterminacy | `ox_fixed_stable`, `OXEconomy.ox_indeterminacy` |
| pp. 535–536 | Two-period cycles (Figure 16.4) | `OXEconomy.ox_two_cycle` |
| Figures 16.1–16.4 | Plots | Not formalised beyond the statements above (no concrete backward-bending economy is constructed) |

### Example 16.1.1 (p. 536)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 536 | Hypotheses (log utility, `β = 1`, `e₁ > e₂`) are satisfiable | `OXEconomy.ox_exampleEconomy_log` |
| p. 536 | Log saving equation is linear in `1/m̂_t`; all solutions; construction; vanishing balances | `OXEconomy.ox_log_Raut`, `OXEconomy.ox_log_eulerRel`, `OXEconomy.ox_log_fixed`, `OXEconomy.ox_log_paths`, `OXEconomy.ox_log_construct`, `OXEconomy.ox_log_tendsto` |
| p. 536 | `p_te₁ − M = p_{t+1}e₂ + M` | `OXEconomy.example_16_1_1_diffeq` |
| p. 536 | General solution `p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` (with `c ≥ 0`); every `c ≥ 0` is an equilibrium; `c = 0` stationary | `OXEconomy.example_16_1_1_general`, `OXEconomy.example_16_1_1_construct` |
| pp. 536–537 | `c > 0`: `p_t → ∞`, money worthless in the limit, allocation tends to autarky | `OXEconomy.example_16_1_1_explosive` |
| p. 537 | "We cannot rule out this explosive solution" | `OXEconomy.example_16_1_1_construct` (every `c > 0` is an equilibrium) |

### Example 16.1.2 (p. 537)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 537 | High-interest-rate equilibrium `p_t = 1`, `c = 1/2`, `R = 1` | `OXEconomy.example_16_1_2_high` |
| p. 537 | Low-interest-rate equilibrium: `p_t/p_{t+1} = R_aut < 1`, prices explode, autarky optimal for every generation at those prices, autarky an equilibrium, infinite present value of endowments, autarky not Pareto optimal | `OXEconomy.example_16_1_2_low` |
| p. 537 | (Correction) the price system with valued money is not an equilibrium | `OXEconomy.example_16_1_2_not_monetary` |

### Existence and efficiency (pp. 537–544)

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 16.1.1, p. 537 | Monetary equilibrium exists iff `R_autg_m < g_n` | `OXEconomy.proposition_16_1_1` |
| (16.7), p. 538 | `R_{t+1} = g_nm̂_{t+1}/(g_mm̂_t)` | `OXEconomy.eq_16_7` |
| (16.8), p. 538 | `m̂_{t+1}/m̂_t = R_{t+1}g_m/g_n > R_autg_m/g_n` | `OXEconomy.eq_16_8` |
| p. 538 | Necessity (both cases) | `OXEconomy.proposition_16_1_1_necessity` |
| p. 538 | Limit step `R_∞ = g_n/g_m` | `OXEconomy.proposition_16_1_1_limit` |
| p. 538 | Sufficiency: unique `m̂ > 0` with `u'(e₁ − m̂)/(βu'(e₂ + g_nm̂)) = g_n/g_m`; the constant path is an equilibrium, the unique one with constant balances; its rate is `g_n/g_m` | `OXEconomy.proposition_16_1_1_root`, `OXEconomy.ox_eulerRel_const_iff`, `OXEconomy.proposition_16_1_1_sufficiency`, `OXEconomy.proposition_16_1_1_unique_stationary`, `OXEconomy.ox_stationary_R` |
| Definition 16.1.1, (16.9), p. 538 | Feasibility; (16.3) ⇔ (16.9) | `OXEconomy.ox_Feasible`, `OXEconomy.definition_16_1_1` |
| Definition 16.1.2, p. 539 | Pareto optimality | `OXEconomy.ox_ParetoOptimal` |
| Definition 16.1.3, p. 539 | Stationary allocation | `OXEconomy.ox_IsStationary` |
| Proposition 16.1.2, p. 539 | Autarky optimal iff `R_aut ≥ g_n` | `OXEconomy.proposition_16_1_2` |
| (16.10), p. 539 | `ε_t = e₁ − c̃_t^t ≥ 0` (and nondecreasing) | `OXEconomy.eq_16_10`, `OXEconomy.ox_feasible_old` |
| (16.11), p. 540 | The indifference-curve expansion; `c̃_{t+2}^{t+1} − e₂ ≥ ε_{t+1}[R_aut + f(ε_{t+1})]` | `OXEconomy.eq_16_11` (tangent form, strict for `ε ≠ 0`) |
| p. 540 | `ε_{t+k}` grows geometrically, contradiction | `OXEconomy.ox_eps_geometric`, `OXEconomy.ox_stationary_optimal` |
| pp. 540–541 | Necessity: the transfer scheme, `f'(0) = −u'(e₁) + βg_nu'(e₂) > 0` | `OXEconomy.proposition_16_1_2_transfer`, `OXEconomy.ox_stationary_not_optimal` |
| pp. 539–541 | The criterion for any feasible stationary allocation | `OXEconomy.ox_stationary_optimal_iff` |
| p. 541 | "With `g_m = 1`, a monetary equilibrium exists iff autarky is inefficient" | `OXEconomy.proposition_16_1_1`, `OXEconomy.proposition_16_1_2` |
| Proposition 16.1.3, p. 541 | Given `R_autg_m < g_n`, the stationary monetary equilibrium is optimal iff `g_m ≤ 1` | `OXEconomy.proposition_16_1_3` |
| (16.12), p. 541 | Feasible stationary allocations `c₁ + c₂/g_n = e₁ + e₂/g_n` | `OXEconomy.eq_16_12` |
| (16.13), p. 542 | `c₁ + (g_m/g_n)c₂ ≤ e₁ + (g_m/g_n)e₂ + (g_m − 1)m̂` | `OXEconomy.eq_16_13` |
| p. 542, Figure 16.5 | Budget line flatter than feasibility line; the initial old gain | `OXEconomy.proposition_16_1_3_steps` |
| p. 542 | Sufficiency via `u'(c₁)/(βu'(c₂)) = g_n/g_m ≥ g_n` | `OXEconomy.proposition_16_1_3` |
| pp. 542–543 | Balasko–Shell criterion; equivalence with `∑ 1/p_t = ∞` | `OXEconomy.ox_balasko_shell_prod`, `OXEconomy.ox_balasko_shell_equiv`; the general theorem is cited by the book and not formalised; for stationary allocations: `OXEconomy.ox_balasko_shell_stationary` |
| pp. 543–544 | Compensating transfers `δ_t = δ₀∏R_{s+1}` | `OXEconomy.ox_balasko_shell_transfers` |
| p. 544 | Finite-horizon failure of the scheme; generalisation to production | Not formalised (informal remarks) |

### Exercises (p. 556)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 16.1(a) | The nonmonetary equilibrium | `OXEconomy.ex_16_1_a` |
| Exercise 16.1(b) | Stationary monetary equilibria: existence, values, ranking | `OXEconomy.ex_16_1_b_exists`, `OXEconomy.ex_16_1_b_values`, `OXEconomy.ex_16_1_b_rank`, `OXEconomy.ex_16_1_b_autarky` |
| Exercise 16.1(c) | All monetary equilibria and their limiting rates of return | `OXEconomy.ex_16_1_c`, `OXEconomy.ex_16_1_c_exist` |
| Exercise 16.2 | The economy with a tree | `OXPrefs.ox_TreeBudget`, `OXPrefs.ox_TreeOptimal`, `OXPrefs.ox_TreeEquilibrium`, `OXPrefs.ox_tree_binds`, `OXPrefs.ox_tree_price_pos`, `OXPrefs.ox_tree_foc` |
| Exercise 16.2(a) | Equilibria with valued fiat money: none | `OXPrefs.ex_16_2_a` |
| Exercise 16.2(b) | Nonmonetary equilibria: the unique constant tree price `a*` | `ox_astar`, `OXPrefs.ox_astar_spec`, `OXPrefs.ex_16_2_b_exists`, `OXPrefs.ex_16_2_b_unique` |

## §16.2–§16.3 and Exercises 16.3–16.9

### §16.2 Production economies (pp. 544–551)

### The Diamond model (`OPHousehold`, `OPDiamond`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 544 | `f(k) = F(k, 1)`, `f′ > 0`, `f″ < 0`, `f(0) = 0`, Inada | hypotheses `hconc : StrictConcaveOn ℝ (Set.Ici 0) f`, `hf0`, `hfd`, `hfp`, `hinf`; `op_fp_strictAnti` |
| p. 545 | The young agent's problem and the Euler equation `u′(w − s) = βu′(Rs)R` | `op_lifetime_hasDerivAt`, `op_euler_necessary`, `op_euler_sufficient`, `op_euler_sufficient_strict`, `op_concave_tangent`, `op_strictConcave_tangent` |
| p. 545 | "Solving yields a saving function `s_t = s(w_t, R_{t+1})`" | `op_saving_exists`, `op_saving_unique`, `op_inada_small` |
| p. 545 | `0 < s_w < 1`: saving increases with the wage | `op_saving_wage_mono`, `op_saving_sw` |
| p. 545 | CRRA below one: the substitution effect dominates, saving rises with `R` | `ex_16_3_mono_lt`, `ex_16_3_anti_gt`, `ex_16_3_gamma_one` |
| (16.14), p. 545 | `w = f(k) − kf′(k)` | `opWage`, `eq_16_14`, `op_F_hasDerivAt_N` |
| (16.15), p. 545 | `R = 1 + f′(k)` | `opRate`, `eq_16_15`, `op_F_hasDerivAt_K` |
| — | Factor payments exhaust output | `op_euler_identity` |
| p. 546 | `K_{t+1} = N_ts_t`, `K_t = k_tN_t` give `g_nk_{t+1} = s(w_t, R_{t+1})` | `op_capital_market` |
| (16.16), p. 546 | The equilibrium law of motion | `OPIsDiamondEqm`, `eq_16_16`, `op_diamondEqm_iff` |
| p. 546 | `dk_{t+1}/dk_t = −s_wkf″(k_t)/(g_n − s_Rf″(k_{t+1}))` | `op_G_slope`, `op_wage_hasDerivAt` |
| p. 546 | The numerator is positive (the wage rises with `k`); `s_R > 0` makes the denominator positive | `op_G_slope_pos`, `op_wage_pos`, `op_wage_strictMono` |
| p. 546 | With `s_R > 0`, `k_{t+1} = G(k_t)` with `G` increasing | `op_temporary_eqm`, `op_S_antitone`, `op_G_exists`, `op_G_strictMono` |
| p. 546 | `G(0) = 0` | `op_G_tendsto_zero`, `op_G_lt_wage`, `op_wage_lt`, `op_wage_tendsto_zero` |
| p. 546 | `lim G(k)/k = 0` via `g_nk_{t+1}/k_t ≤ w_t/k_t` (corrected) | `op_G_div_tendsto_zero`, `op_wage_div_eq`, `op_f_div_tendsto_zero`, `op_wage_div_tendsto_zero` |
| p. 547 | The graph of `G` eventually falls below the diagonal | `op_G_eventually_below` |
| p. 547 | `G′(0) > 1`: positive steady states exist; "an odd number" (corrected) | `op_exists_fixed`, `op_above_diag_of_deriv`, `op_ivt_up`, `op_ivt_down`; counterexample `opOddG`, `op_oddG_props`, `op_oddG_fixed`, `op_odd_counterexample`, `op_strictMonoOn_max`, `op_strictMonoOn_min`, `op_sqrt_strictMonoOn`, `op_three_sqrt_div_tendsto`, `op_sqrt_four`, `op_sqrt_nine` |
| p. 547 | `G′(0) < 1`: "an even number, possibly zero" (corrected) | `op_below_diag_of_deriv`; counterexample `opEvenG`, `op_evenG_props`, `op_evenG_fixed`, `op_even_counterexample`; an economy with zero positive steady states: `ex_16_5_b_none` |
| p. 547, Figure 16.9 | `s_R < 0`: `k_{t+1}` may not be unique (self-fulfilling prophecies) | Not formalised (an illustration with no specific economy) |
| Figures 16.6–16.8 | Configurations of steady states | Not formalised (plots); content in the rows above |
| p. 549 | Stability condition `G′(k*) = −s_wk*f″(k*)/(g_n − s_Rf″(k*)) < 1` | `op_G_slope_steady`, `op_local_stability` |
| p. 549 | The Diamond conditions; a unique steady state `k_D` (corrected) | `op_diamond_conditions`, `op_diamond_conditions_printed`, `op_slope_lt_one`, `op_least_fixed`, `op_fixed_below` |
| Figure 16.10 | A unique positive, stable steady state | `op_fixed_signs`, `op_global_convergence` |

### Dynamic efficiency (`OPEfficiency`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 549–550 | The aggregate resource constraint per worker | `op_resource_per_worker` |
| (16.17), p. 550 | `c_y + g_n⁻¹c_o = f(k) − (g_n − 1)k` | `eq_16_17` |
| pp. 550–551 | The planner's Lagrangian and first-order conditions (corrected) | `opLagrangian`, `op_planner_lagrangian`, `op_planner_foc`, `op_planner_foc_printed` |
| p. 551 | `λ₀ = 0 ⇒ θ = 0`: the golden rule `f′(k_G) = g_n − 1` | `op_planner_golden_rule`, `op_golden_rule_exists`, `op_golden_rule_unique` |
| p. 551 | The golden rule maximises consumption per worker | `op_golden_rule_max`, `op_golden_rule_strict` |
| p. 551 | `k* > k_G`: dynamically inefficient; reducing capital to `k_G` makes everyone better off | `OPFeasible`, `OPParetoDominates`, `op_steady_feasible`, `op_dynamic_inefficiency` |
| p. 551 | `k* ≤ k_G` is necessary for efficiency | `op_dynamic_inefficiency` (contrapositive) |
| p. 551 | Cass (1972), Balasko–Shell (1980) criterion `Σ g_n⁻ᵗ ∏ R_{s+1} = ∞` | Not formalised in general (cited, not proved, in the text) |
| p. 551 | Corollary: a steady state is Pareto optimal iff `k* ≤ k_G` iff `f′(k*) ≥ g_n − 1` | `op_cass_steady_state`, `op_cass_corollary`; optimality for `k* < k_G`: `op_pareto_optimal_of_lt_golden`; non-optimality for `k* > k_G`: `op_dynamic_inefficiency`; `k* = k_G`: not formalised |

### §16.3 Asset price bubbles (pp. 551–556) (`OPBubbles`)

| Source | Claim | Lean |
| --- | --- | --- |
| (16.18), p. 552 | `g_n(k_{t+1} + b_{t+1}) = s(w_t, R_{t+1})` | `eq_16_18` |
| (16.19), p. 552 | `g_nb_{t+1} = R_tb_t` | `eq_16_19` |
| p. 552 | The bubble equilibrium; `B_t > 0` | `OPIsBubbleEqm`, `op_bubble_pos`, `op_bubble_k_law` |
| p. 552 | `b_t = 0` reduces to (16.16) | `op_bubble_zero` |
| pp. 552–553 | Bubbly steady state: `R(k) = g_n`, `k = k_G`, `b*` from the first equation (`g_b` misprint) | `op_bubbly_steady`, `op_bubbly_steady_golden` |
| p. 553 | The locus `Δk_t = 0`: `b = [s(w(k), R(k)) − g_nk]/R(k)` | `opKLocus`, `op_k_locus` |
| p. 553 | It crosses the axis at `0` and `k_D` | `op_kLocus_zero_iff` |
| p. 553 | `∂b/∂k = (−s_wkf″ + s_Rf″ − g_n)/R²(k)` at `0`, `k_D` (corrected) | `op_kLocus_hasDerivAt`, `op_kLocus_slope_printed` |
| p. 553 | Under the Diamond conditions `db/dk(0) > 0`, `db/dk(k_D) < 0` | `op_kLocus_slope_neg`, `op_S_vs_G`, `op_kLocus_pos`, `op_kLocus_neg` |
| p. 554 | `k_{t+1} > k_t ⟺ b_t < [s(w(k_t), R(k_t)) − g_nk_t]/R(k_t)` | `op_k_increase_iff`, `op_k_decrease_iff`, `op_k_stationary_iff` |
| p. 554 | `b_{t+1} − b_t = (R_t/g_n − 1)b_t`; `Δb = 0` at `k_G`; `b_{t+1} > b_t ⟺ k_t < k_G` | `op_b_diff`, `op_b_increase_iff`, `op_b_stationary_iff` |
| p. 554 | A bubbly steady state exists iff `k_G < k_D` iff `R_D < g_n` | `op_bubbly_exists_iff` |
| p. 555 | The bubbly steady state is a saddle; a unique `b₁` on the saddle path | `ex_16_9_roots`, `ex_16_9_saddle` (for the linearised system) |
| p. 555 | `b₁ < b(k₁)`: convergence to the Diamond steady state | Not formalised (global nonlinear dynamics read off Figure 16.13) |
| Figures 16.11–16.13 | Loci, vector fields, phase diagram | Not formalised (plots); content in the rows above |
| pp. 555–556 | Tirole, Weil, Santos–Woodford, Kocherlakota, Miao–Wang | Not formalised (literature survey) |

### Exercises 16.3–16.9 (pp. 556–558) (`OPExercises`, `OPExercisesCES`)

| Source | Claim | Lean |
| --- | --- | --- |
| — | Cobb–Douglas `f = Ak^α`, its wage, steady state and convergence of `k_{t+1} = ck_t^α` | `opCD`, `opCDfp`, `op_cd_hasDerivAt`, `op_cd_wage`, `op_rpow_eq_mul`, `opKstarCD`, `op_kstarCD_pos`, `op_cd_steady_iff`, `op_cd_converge` |
| — | Log saving with second-period income | `opLogSaving`, `op_log_saving` |
| Ex 16.3 | CRRA: the saving function, its properties in `γ`, the law of motion | `opCRRASaving`, `op_crra_hasDerivAt`, `op_crra_strictConcave`, `ex_16_3_euler`, `ex_16_3_optimal`, `ex_16_3_mono_lt`, `ex_16_3_anti_gt`, `ex_16_3_gamma_one`, `ex_16_3_law` |
| Ex 16.4 | Log and `k^α`: the law of motion and the steady state | `ex_16_4_law`, `ex_16_4_steady`, `ex_16_4_converge`, `ex_16_4_mpk`, `ex_16_4_inefficient`, `ex_16_4_efficient` |
| Ex 16.5 | CES: derivative, wage, law of motion | `opCESbase`, `opCES`, `opCESfp`, `opCESwage`, `op_ces_base_pos`, `ex_16_5_hasDerivAt`, `ex_16_5_wage`, `ex_16_5_law`, `op_ces_wage_continuousOn` |
| Ex 16.5(a) | `σ ≥ 1`: a positive steady state exists | `ex_16_5_a` (`σ > 1`), `ex_16_5_a_cobbDouglas` (`σ = 1`) |
| Ex 16.5(b) | `σ < 1`: law of motion, existence/uniqueness/stability; no positive steady state for small `A` | `opCESM`, `op_ces_wage_le_small`, `op_ces_wage_le_large`, `ex_16_5_b_bound`, `ex_16_5_b_none`, `ex_16_5_b_collapse`, `ex_16_5_b_two`; stability of the two steady states for large `A`: not formalised |
| Ex 16.6 | Depreciation: the law of motion; `δ = 1` | `OPIsDiamondEqmDep`, `ex_16_6_rate`, `ex_16_6_full`, `ex_16_6_log` |
| Ex 16.7(a) | Government spending: the law of motion | `ex_16_7_a` |
| Ex 16.7(b) | Permanent increase `G_L → G_H` | `ex_16_7_b`, `ex_16_7_bc_path`; the drawing: not formalised |
| Ex 16.7(c) | Temporary increase | `ex_16_7_bc_path`; the drawing: not formalised |
| Ex 16.8(a)(i) | PAYG: law of motion | `ex_16_8_a_i` |
| Ex 16.8(a)(ii) | PAYG lowers capital | `ex_16_8_a_ii` |
| Ex 16.8(a)(iii) | Welfare under dynamic efficiency/inefficiency | `opPAYGWelfare`, `ex_16_8_a_iii`, `ex_16_8_a_iii_resources` |
| Ex 16.8(b) | Fully funded: law of motion, no effect on capital or welfare | `ex_16_8_b` (with `ex_16_4_law`); "explain the intuition": not formalised |
| Ex 16.9 | Linearise the §16.3 system; stability of the bubbly steady state | `opLinM11`, `opLinM12`, `opLinM21`, `ex_16_9_linearization`, `ex_16_9_roots`, `ex_16_9_saddle` (with Chapter 1's `cp22`, `lamLo`, `lamHi`, `kSaddle`, `saddle22_iff`, `sHi_zero_iff`) |
