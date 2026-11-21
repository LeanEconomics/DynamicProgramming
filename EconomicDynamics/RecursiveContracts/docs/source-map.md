# Source map: Miao Chapter 22

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 22, Recursive
Contracts, pp. 773–801. Lean names are relative to `Miao.RecursiveContracts`. Page references are
the draft's running heads. Limited commitment is a Markov endowment economy with the promised value
as state (`lc_BellmanAt`), hidden action a continuum-of-outputs model on an interval
(`ha_principalValue`), hidden information the finite-state model `HIModel`. Departures from the book
are in [corrections](corrections.md).

## Introduction, §22.1 Limited Commitment and Exercises 22.1–22.2

### Introduction (pp. 773–774)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 773–774 | Hidden action, hidden information, limited commitment; promised values as state | not formalised: discursive, no claims |

### §22.1 The model (pp. 774–775) — `LCAutarky`, `LCSequence`, `LCLagrangian`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 774 | Markov endowments on `{θ₁, …, θₙ}`, transition `π(θⱼ|θᵢ)` | `lc_condExp`, `lc_IsStochastic`, `lc_condExp_abs_le`, `lc_condExp_iter_abs_le`, `lc_condExp_iter_linear`, `lc_exists_bound` |
| p. 775 | Autarky value `U_d(y_t) = E_t Σ β^{s-t} u(y_s)`: convergence, recursion, uniqueness | `lc_autarky`, `lc_autarky_summable`, `lc_autarky_recursion`, `lc_autarky_unique` |
| p. 775 | Without incentive problems the principal fully insures the agent (constant consumption) | `lc_first_best` |
| p. 775 | Contracts on the event tree, conditional expectations, discounted values | `lc_ext`, `lc_treeExp`, `lc_treeValue`, `lc_treeExp_abs_le`, `lc_treeValue_summable`, `lc_treeValue_recursion`, `lc_treeExp_state`, `lc_BddPlan`, `lc_principalValue` |
| (22.1), p. 775 | Incentive constraint; autarky satisfies it with equality | `lc_IC`, `eq_22_1` |
| (22.2), p. 775 | Participation constraint; with `v₀ ≥ U_d(y₀)` it implies (22.1) at date 0 | `lc_PK`, `eq_22_2` |

### §22.1.1 Dynamic programming (pp. 776–778) — `LCSequence`, `LCBellman`, `LCInstances`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 776 | Writing the problem recursively with the promised value as state: date-0 choices of a feasible plan satisfy (22.3)–(22.4), the principal's value satisfies the one-step recursion, continuations are feasible | `eq_22_3`, `eq_22_4`, `lc_principal_recursion`, `lc_continuation_feasible` |
| p. 776 | Bellman equation with (22.3)–(22.4) | `lc_feasible`, `lc_obj`, `lc_valueSet`, `lc_BellmanAt`, `lc_Bellman`, `lc_Optimal`, `lc_BellmanAt.lc_obj_le`, `lc_BellmanAt.lc_exists_optimal` |
| p. 776 | The Bellman equation has solutions (log utility) | `lc_absorbP`, `lc_absorbP_of_le`, `lc_exp_ge_tangent`, `lc_absorbing_bellman`, `lc_bellman_one_state` |
| p. 776 | The constraint set is convex | `lc_feasible_convex` |
| p. 776 | `P` is concave in `v` (the Bellman operator preserves concavity); `P` decreasing in `v` | `lc_bellman_concave`, `lc_bellman_antitone` |
| p. 776 | The Lagrangian | `lc_lagrangian` |
| (22.5), p. 776 | FOC for `c`: `u'(c) = 1/μ` | `eq_22_5` |
| (22.6), p. 776 | FOC for `wⱼ`, with `λⱼ ≥ 0` and complementary slackness | `eq_22_6`, `lc_sum_update` |
| p. 777 | `μ > 0`, so promise keeping binds | `eq_22_5`, `eq_22_7`, `lc_promise_keeping_binds` |
| (22.7), p. 777 | Envelope condition `P₂(θᵢ, v) = −μ` | `eq_22_7` |
| (22.8), p. 777 | `u'(c) = −1/P_v(θᵢ, v)` | `eq_22_8`, `lc_inv_hasDerivAt` |
| (22.9), p. 777 | `P_v(θⱼ, wⱼ) = P_v(θᵢ, v) − λⱼ/(βπ(θⱼ|θᵢ))` | `eq_22_9` |
| p. 777 | States with `λᵢ > 0`: `wᵢ = U_d(θᵢ)`, `cᵢ = f₁(θᵢ)` depends on `θᵢ` only (amnesia); consumption rises | `lc_binding_case` |
| p. 777 | States with `λᵢ = 0`: consumption unchanged; `wᵢ = v` | `lc_slack_case`; `wᵢ = v` only i.i.d.: `lc_iid_promised_value` (false in general: `lc_promise_decrease_counterexample`) |
| p. 778 | Optimal contract: `c = max{f₁(y), f₂(y, v)}`, consumption never falls, rises only when the incentive constraint binds | `lc_optimal_contract` |
| p. 778 | `w = max{U_d(y), v}`; promised values never decrease; the boundary `y^d(v)` | i.i.d.: `lc_iid_value_shift`, `lc_iid_promised_value`, `lc_iid_full_insurance`; Markov counterexample `lc_promise_decrease_counterexample` |
| p. 778 | Consumption constant while the constraint is slack, increasing when it binds; it settles down | `lc_consumption_eventually_constant`, `lc_iid_full_insurance` |
| p. 778 | "A numerical method is often needed" | not formalised: computational remark |

### §22.1.2 The Lagrangian method (pp. 778–780) — `LCLagrangian`

| Source | Claim | Lean |
| --- | --- | --- |
| (22.10), p. 779 | Cumulative multipliers `μ_t = μ_{t-1} + α_t`, `μ_{-1} = 0` | `lc_cumMult`, `eq_22_10`, `lc_incr`, `lc_cumMult_incr` |
| p. 779 | Rewriting the Lagrangian: `Σ β^t α_t E_t Σ β^{s-t} u(c_s) = Σ β^t μ_t u(c_t)` | `lc_triangle_swap`, `lc_lagrangian_rewrite_finite`, `lc_lagrangian_rewrite` |
| p. 779 | FOC `u'(c_t) = 1/(μ_t + φ)`; `−(μ_t + φ) = P_v(y_t, v_t)` | `lc_lagrangian_foc`, `lc_multiplier_value_derivative` |
| pp. 779–780 | Complementary slackness; these conditions with (22.10) characterise the optimal contract | `lc_detU`, `lc_detPrincipal`, `lc_detFeasible`, `lc_lagrangian_sufficiency` |
| p. 780 | Parameterised expectations (Marcet–Marimon, Kehoe–Perri) | not formalised: numerical method |

### §22.1.3 The alternative characterisation (pp. 780–781) — `LCBellman`, `LCZhang`, `LCExercise221`

| Source | Claim | Lean |
| --- | --- | --- |
| (22.11), p. 780 | `c_t = max{c_{t-1}, h(y_t)}`; consumption rises iff the incentive constraint binds, then `c_t = h(y_t)` | Markov, from §22.1.1: `eq_22_11`, `lc_optimal_contract`; deterministic: `ex_22_1c` |
| p. 780 | `d_i(τ)`: constant consumption making the constraints at `0` and `τ` bind | deterministic dates `τ`: `lc_d_markov`, `lc_autarky_split`; deterministic model: `lc_d_tau`; general stopping times not formalised |
| p. 781 | `h(θᵢ) = inf_{τ ≥ 1} dᵢ(τ)` | `lc_B`, `lc_S`, `lc_A`, `lc_m`, `lc_h_isGLB` |
| p. 781 | `c₀` from the binding participation constraint is unique; `c₀(U_d(θᵢ), θᵢ) = h(θᵢ)`; `c₀ > h` when `v₀ > U_d` | `lc_zpath`, `lc_zpath_abs_le`, `lc_c0_strictMono`, `lc_c0_gt_h` |
| p. 781 | (22.11) with `c₀` gives the optimal consumption process (Zhang) | deterministic: `lc_zhang_identity`, `ex_22_1c`; stochastic not formalised |
| p. 781 | Zhang's numerical method is more efficient | not formalised: computational |
| — | Discounted sums and block lemmas used above | `lc_detValue`, `lc_summable_geom`, `lc_detValue_abs_le`, `lc_detValue_split`, `lc_detValue_succ`, `lc_detValue_split0`, `lc_detValue_sub`, `lc_detValue_mono`, `lc_detValue_const`, `lc_detValue_shift`, `lc_B_add`, `lc_S_add`, `lc_B_mul`, `lc_B_nonneg`, `lc_B_ge_one`, `lc_B_mul_le`, `lc_S_abs_le`, `lc_A_abs_le`, `lc_A_bddBelow`, `lc_m_le_A`, `lc_m_abs_le`, `lc_m_le_x`, `lc_S_ge_m`, `lc_A_tendsto`, `lc_exists_low`, `lc_block_le`, `lc_block_eq`, `lc_tail_le`, `lc_tail_eq`, `lc_run`, `lc_run_succ`, `lc_run_ge`, `lc_run_mono`, `lc_run_add`, `lc_run_eq_first`, `lc_run_abs_le`, `lc_g_strictMono` |

### Exercises (pp. 797–798) — `LCExercise221`, `LCExercise222`

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 22.1, p. 797 | Deterministic problem with autarky outside option | `lc_detFeasible`, `lc_detPrincipal`, `lc_optimal_of_marginal` |
| Ex 22.1(a), p. 797 | Decreasing endowments: `u(c_t) = (1 − β) U_d(y₀)` | `ex_22_1a` |
| Ex 22.1(b), p. 797 | Increasing endowments: autarky | `ex_22_1b` |
| Ex 22.1(c), p. 798 | `c_t = max{c_{t-1}, h(y_t)}`, `c₀ = h(y₀)`, `h = u⁻¹(min_τ …)` | `ex_22_1c` (with `inf`); `lc_ex_22_1c_min_not_attained`, `lc_h_depends_on_future` |
| Ex 22.2(a), p. 798 | Bellman equation for AR(1) log income | `lc_BellmanAt` for a discretisation; autarky value `ex_22_2a` |
| Ex 22.2(b)–(c), p. 798 | Matlab solution, plot, root of `P(v, 1) = 0` | not formalised: computational |

## §22.2 Hidden Action

### §22.2

### The model, pp. 781–783

| Source | Claim | Lean |
| --- | --- | --- |
| p. 782 | `dπ(y^0; a) = f(y_0 | a_0) dy_0`, `dπ(y^{t+1}; a) = f(y_{t+1} | a(y^t)) dπ(y^t; a) dy_{t+1}` | `ha_histDensity`, `ha_histDensity_succ`, `ha_histDensity_nonneg` |
| p. 782 | For a fixed action, output is i.i.d. over time | `ha_histDensity_iid` |
| p. 782 | The principal's objective `∑ β^t ∫ v(y_t − c(y^t)) dπ(y^t; a)` | `ha_seqPrincipalValue` |
| (22.12), p. 782 | Incentive constraint of the sequence problem | `ha_seqAgentValue`, `ha_seqIC` |
| (22.13), p. 783 | Participation constraint | `ha_seqPC` |
| p. 783 | `f(y | a)` twice continuously differentiable in `a`: a concrete family where differentiation under the integral holds | `ha_linearDensity_hasDerivAt` |
| p. 783 | First-order approach validity (Rogerson 1985b) | not formalised: assumed by the book, cited result |
| p. 783 | The principal's Bellman equation `P(v) = max ∫ [(y − c) + β P(w)] f(y | a(v)) dy` | `ha_principalValue`, `ha_IsPrincipalValue`, `ha_principalValue_le` |
| (22.14), p. 783 | Recursive incentive constraint | `ha_agentValue`, `ha_IC` |
| (22.15), p. 783 | Promise keeping | `ha_PK` |
| p. 783 | Spear–Srivastava: the recursive problem is equivalent to the sequence problem | not formalised: cited result, not proved in the text |

### First-order conditions, pp. 784–785

| Source | Claim | Lean |
| --- | --- | --- |
| (22.16), p. 784 | The first-order condition replacing (22.14); necessary for an interior effort satisfying (22.14) | `ha_FOA`, `eq_22_16` |
| p. 784 | `P` concave and decreasing; strictly concave if differentiable (Spear–Srivastava) | not formalised: cited result; used as hypotheses (`StrictAnti dP`, `Antitone P`) |
| p. 784 | The Lagrangian `L` | `ha_pointLagr` (its integrand), the objective of `eq_22_18` |
| (22.17), p. 784 | `1/φ′(c(v, y)) = λ(v) + μ(v) f_a/f` | `eq_22_17` |
| (22.18), p. 785 | First-order condition in effort | `eq_22_18` |
| (22.19), p. 785 | First-order condition in `w` | `eq_22_19` |
| (22.20), p. 785 | `P′(w(v, y)) = −1/φ′(c(v, y))` | `eq_22_20` |

### Proposition 22.2.1, p. 785

| Source | Claim | Lean |
| --- | --- | --- |
| p. 785 | Envelope condition `P′(v) = −λ(v)` | `ha_envelope`, `ha_envelope_condition` |
| p. 785 | `∫ f_a(y | a) dy = 0` | `ha_integral_fa_eq_zero` |
| (22.21), p. 785 | `P′(v) = −∫ f(y | a(v)) / φ′(c(v, y)) dy` | `eq_22_21` |
| p. 785 | Mean value theorem for integration | `ha_integral_mean_value` |
| (22.22), p. 785 | `P′(v) = −1/φ′(c(v, ŷ(v)))` | `eq_22_22` |
| Proposition 22.2.1, p. 785 | For every `v` some `ŷ(v)` has `v = w(v, ŷ(v))` | `proposition_22_2_1` |
| p. 786 | At `ŷ(v)` the time-`t+1` contract equals the time-`t` contract | `proposition_22_2_1` (`w(v, ŷ(v)) = v`, so the schedules `c(w(v, ŷ), ·)`, `w(w(v, ŷ), ·)` are `c(v, ·)`, `w(v, ·)`) |

### Proposition 22.2.2, pp. 786–787

| Source | Claim | Lean |
| --- | --- | --- |
| p. 786 | Differentiated (22.20): `P″(w) w_y = φ″(c)/φ′(c)² c_y` | `ha_eq_22_20_deriv` |
| p. 786 | `c_y` and `w_y` have the same sign | `ha_cy_pos_iff_wy_pos` |
| p. 786 | `μ ≤ 0` and (22.17) give `c_y ≤ 0` (concavity of `φ`) | `ha_eq_22_17_deriv`; derivative-free in the proof of `ha_mu_pos` |
| p. 786 | `E[f_a/f] = ∫ f_a = 0` | `ha_expect_lr`, `ha_integral_fa_eq_zero` |
| p. 786 | `E[g f_a/f] = Cov(g, f_a/f) + E[g] E[f_a/f]` | `ha_expect`, `ha_cov`, `ha_expect_mul_eq_cov_add`, `ha_cov_lr_eq` |
| p. 786 | By MLRC and monotonicity of `g`, the covariance is nonnegative | `ha_sign_change`, `ha_mlrc_integral_nonneg`, `ha_cov_lr_nonneg` |
| p. 787 | `∫ y f_a > 0` contradicts `∫ y f_a = 0` (MLRC) | `ha_mlrc_integral_pos` |
| Proposition 22.2.2, p. 786 | `μ(v) > 0` | `ha_mu_pos` |
| Proposition 22.2.2, p. 786 | `μ(v) > 0`, `c_y > 0`, `w_y > 0` (corrected) | `proposition_22_2_2`; counterexample `ha_cy_eq_zero_of_ry_zero`, `ha_flat_mlrc_density` |
| p. 787 | `c(v, ·)`, `w(v, ·)` increasing in output | `ha_c_strictMonoOn`, `ha_w_strictMonoOn` |
| p. 787 | `c(v, ŷ(v))` is the first-best income for `λ(v)` | `ha_first_best_income` |
| p. 787 | `y > ŷ(v)`: paid more than first-best and promised more (corrected `w > v`) | `ha_contract_dynamics` |

### Proposition 22.2.3 and its implications, p. 787

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 22.2.3, p. 787 | Inverse Euler equation (corrected density `f(y′ | a(w(v, y)))`) | `proposition_22_2_3`; counterexample to the printed form `ha_proposition_22_2_3_printed_false` |
| p. 787 | `φ′(c(v, y)) = (∫ …)⁻¹` | `ha_inverse_euler_inv` |
| pp. 785–787 | `P′(v_t)` is a martingale (the step shared by the proofs) | `ha_marginal_value_martingale` |
| p. 787 | Jensen: `φ′(c(v, y)) < E φ′(c(w(v, y), y′))` | `ha_inv_expect_inv_le`, `ha_inv_expect_inv_lt`, `ha_jensen`, `ha_jensen_strict`, `ha_jensen_strict_of_mu_pos` |
| p. 787 | The agent would not borrow at gross interest `1/β` | `ha_tangent_lt`, `ha_no_borrow` |
| p. 787 | The agent would wish to save (Rogerson 1985a) | `ha_wants_to_save`, `ha_rogerson_save` |
| p. 788 | Phelan–Townsend lotteries and computation | not formalised: discussion of the literature, no claims derived |

There are no Chapter 22 exercises for §22.2.

## §22.3 Hidden Information and Exercises 22.3–22.4

### §22.3 The model (pp. 788–789)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 788 | Income `θ₁ < ⋯ < θₙ` iid with `Pr(yₜ = θᵢ) = πᵢ`, private information, risk-neutral principal, common `β ∈ (0, 1)` | `HIModel` (fields `N`, `θ`, `prob`, `β`, `u`, `θ_strictMono`, `prob_pos`, `prob_sum`, `β_pos`, `β_lt_one`, `u_cont`, `u_strictMono`, `u_strictConcave`, `u_bddAbove`, `u_not_bddBelow`) |
| p. 788, Assumption 22.3.1 | `u' > 0`, `u'' < 0`, `sup u < ∞`, `inf u = −∞`, `u' → ∞` at `a`, DARA | `assumption_22_3_1`; instance `hi_cara_assumption_22_3_1`; `hi_modelOfAssumption` |
| p. 788 | CARA example utility used for instances | `hi_cara`, `hi_cara_strictMono`, `hi_cara_strictConcave`, `hi_cara_sSup`, `hi_cara_not_bddBelow`, `hi_caraModel`, `hi_exampleModel`, `hi_exampleModel_N` |
| p. 788 | Revelation principle: restrict to truth-telling contracts | Not formalised (descriptive; the model is stated for truth-telling contracts) |
| p. 789, (22.23) | Bellman equation `P(v) = max Σ πᵢ [−cᵢ + βP(wᵢ)]` | `hi_principalValue`, `hi_vals`, `hi_T`; fixed point `hi_P_fixed` |
| p. 789, (22.24) | Incentive constraints `Cᵢⱼ ≥ 0` | `hi_C`, `hi_IC`, `hi_LocalIC` |
| p. 789, (22.25) | Promise keeping | `hi_agentValue`, `hi_Feasible` |
| p. 789 | `vmax = sup u/(1 − β)` | `hi_ubar`, `hi_vmax`, `hi_u_lt_ubar`, `hi_lt_vmax_iff`, `hi_agentValue_lt_vmax` |
| p. 789 | Constant contract `b(v)`: incentive compatible, delivers `v`, lower bound `−b/(1 − β)` | `hi_Bfun`, `hi_Bfun_strictMono`, `hi_Bfun_bounds`, `hi_Bfun_surj`, `hi_b`, `hi_b_spec`, `hi_const_feasible`, `hi_const_value`, `hi_L` |
| p. 789 | First-best contract `c*(v) − θᵢ`, upper bound | `hi_u_surj`, `hi_uinv`, `hi_u_uinv`, `hi_cstar`, `hi_cstar_spec`, `hi_θbar`, `hi_U`, `hi_U_eq_sum`, `hi_principal_le_U`, `hi_sum_const` |
| p. 789, (22.26) | `−b(v)/(1 − β) ≤ P(v) ≤ Σ πᵢ [θᵢ − c*(v)]/(1 − β)` | `eq_22_26`, `hi_P_InF`, `hi_L_InF` |
| p. 790, Figure 22.1 | The value function and its bounds | Not formalised: figure |

### §22.3.1 Characterizations (pp. 790–796)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 790, Lemma 22.3.1 | Incentive constraints imply `cᵢ₋₁ ≥ cᵢ`, `wᵢ₋₁ ≤ wᵢ` | `lemma_22_3_1`, `hi_local_mono`, `hi_pair_mono`, `hi_C_add_C`, `hi_strict_decreasing_increments`, `hi_decreasing_increments` |
| p. 791, Lemma 22.3.2 | Local downward and upward constraints imply all constraints | `lemma_22_3_2`, `hi_down_step`, `hi_up_step` |
| p. 791, Proposition 22.3.1 | Unique `P` solving (22.23), decreasing, concave | `proposition_22_3_1`, `proposition_22_3_1_concave`, `hi_P`, `hi_Pk`, `hi_Pk_InF`, `hi_Pk_succ_abs`, `hi_Pk_cauchy`, `hi_Pk_tendsto`, `hi_P_abs_sub`, `hi_P_fixed`, `hi_fixed_unique` |
| p. 792 | `F` with the sup metric; the gap between the bounds is bounded | `hi_InF`, `hi_b_le_cstar`, `hi_U_sub_L_le`, `hi_InF_abs_sub` |
| p. 792 | Blackwell: `T` is a contraction | `hi_vals_nonempty`, `hi_vals_bddAbove`, `hi_le_T`, `hi_T_le_add`, `hi_T_abs_le` |
| p. 792 | `T` maps decreasing functions to decreasing functions | `hi_T_antitoneOn`, `hi_b_mono`, `hi_L_antitoneOn`, `hi_Pk_antitoneOn` |
| p. 792 | Averaged contract `w* = δw⁰ + (1 − δ)w¹`, `u(θᵢ + c*ᵢ) = δu(θᵢ + c⁰ᵢ) + (1 − δ)u(θᵢ + c¹ᵢ)`; `c*ᵢ ≤ δc⁰ᵢ + (1 − δ)c¹ᵢ`; delivers `δv⁰ + (1 − δ)v¹`; principal gets at least the average | `hi_exists_mix`, `hi_mix_c_le`, `hi_mix_agentValue`, `hi_mix_principal_ge` |
| p. 792 | `C*ᵢ,ᵢ₋₁ = δC⁰ᵢ,ᵢ₋₁ + (1 − δ)C¹ᵢ,ᵢ₋₁ + [⋯]`; DARA makes the bracket nonnegative | `hi_mix_C_eq`, `hi_dara_ratio_mono`, `hi_dara_ce`, `hi_mix_downward` |
| pp. 792–793 | Repair: mean-preserving decrease in the spread of `w`; binding downward and `cᵢ ≤ cᵢ₋₁` give the upward constraints | `hi_spread_reduction`, `hi_reduce`, `hi_reduce_mean`, `hi_upperMass`, `hi_upperMass_bounds`, `hi_upward_of_binding` |
| pp. 792–793 | Weak spread reduction and increment adjustment (concave `f`) | `hi_incr_le_on_concave`, `hi_slope_anti_concave`, `hi_spread_reduction_weak`, `hi_reduce_incr`, `hi_adjust_increments` |
| p. 793 | Repair of the transfers when `w*ᵢ = w*ᵢ₋₁`: pool them at equal expected utility | `hi_pool`, `hi_pool_cost`, `hi_tangent`, `hi_deriv_strictAnti`, `hi_steps` |
| pp. 792–793 | Any relaxed contract (local downward constraints, monotone `w`) repairs to an IC contract with binding downward constraints, same promised value, weakly higher principal value | `hi_repair`, `hi_mix_repair` |
| p. 793 | `T` maps concave functions to concave functions | `hi_T_concaveOn` |
| p. 793 | `P = lim Pₖ` is concave (starting from `P₀ = L`, which is concave) | `proposition_22_3_1_concave`, `hi_Pk_concaveOn`, `hi_L_concaveOn`, `hi_concaveOn_of_tendsto` |
| p. 793 | Strict concavity of `TP` from strict concavity of `P` | Not formalised (needs optimal contracts to exist; see corrections) |
| p. 793 | Uniqueness of the optimal contract | Not formalised (needs strict concavity of `TP`) |
| pp. 793–794 | Continuous differentiability (Benveniste–Scheinkman) | Not formalised |
| p. 794, Assumption 22.3.2 | `P` strictly concave | `assumption_22_3_2` |
| p. 794, Proposition 22.3.2 | Local downward constraints bind, local upward constraints slack | Under Assumption 22.3.1 alone (concavity): an optimal contract with binding downward constraints exists whenever one exists, `hi_proposition_22_3_2_concave`; under Assumption 22.3.2: `proposition_22_3_2`, `hi_Optimal`, `hi_incr_le_on`, `hi_slope_strict_anti`, `hi_spread_reduction`, `hi_sum_mul_left` |
| p. 795, Proposition 22.3.3 | Coinsurance inequalities | `proposition_22_3_3`, `hi_sum_ite` |
| p. 795, (22.27)–(22.29) | First-order and envelope conditions | `hi_FOC`, `hi_θsucc` (stated as hypotheses) |
| p. 795, (22.30) | `Σ πᵢ P'(wᵢ) = P'(v)` (martingale) | `eq_22_30`; without multipliers `hi_martingale_of_shift` |
| p. 796 | Raising every `wᵢ` preserves incentive compatibility; envelope argument | `hi_C_shift`, `hi_agentValue_shift`, `hi_martingale_of_shift` |

### §22.3.2 Long-run poverty (pp. 796–797)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 796, Lemma 22.3.3 | `w₁ < v < wₙ` | `lemma_22_3_3`, `hi_strictAntiOn_deriv`; `n ≥ 2` needed: `hi_lemma_22_3_3_one_state` |
| p. 796, Proposition 22.3.4 | `vₜ → −∞` almost surely | `proposition_22_3_4`, `hi_vseq`, `hi_vseq_congr`, `hi_vseq_lt`, `hi_filt`, `hi_filt_meas`, `hi_tuple_sm_aux`, `hi_tuple_sm`, `hi_tuple_int`, `hi_Fseq`, `hi_vseq_eq_Fseq`, `hi_poverty_martingale` |
| p. 797 | `P'(vₜ)` a nonpositive martingale converges; a finite negative limit contradicts Lemma 22.3.3 | `hi_poverty_martingale` (with Mathlib `Submartingale.ae_tendsto_limitProcess`), `hi_poverty_det` |
| p. 797 | Non-vacuity of the hypotheses | `hi_poverty_example`, `hi_exampleModel_vmax`, `hi_exampleW` |
| p. 797 | Heuristic: spreading cost `≈ −½ε²P''(w̄)`, `P'' → 0` at `−∞`, `→ −∞` at `vmax` | Not formalised (heuristic discussion) |

### §22.4 Exercises 22.3–22.4 (pp. 798–799)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 798, Exercise 22.3 | As `β → 1`, `P(v)` converges to the first best | Upper half `ex_22_3_upper`; per-period bounds independent of `β`: `hi_normalized_bounds`; the limit itself not formalised (see corrections) |
| p. 799, Exercise 22.4 | CARA: form of the optimal contract and of `P` | `ex_22_4` (corrected, `A = 0`), `ex_22_4_value`, `hi_cara_shift`, `hi_cara_vmax`, `hi_cara_scale_feasible`, `hi_cara_b_shift`, `hi_cara_cstar_shift`, `hi_scaleFn`, `hi_scaleFn_InF`, `hi_pv_scaleFn`, `hi_T_scaleFn`, `hi_cara_P_scale`, `hi_cara_P_hasDerivAt`, `hi_cara_pv_scale`, `hi_cara_optimal_scale`, `hi_optimal_value` |
| p. 799, Exercise 22.4 | The printed form with `A = Σ πᵢ/aᵢ` | Promise keeping forces `A = 0`: `hi_ex_22_4_A_eq_zero`; counterexample `ex_22_4_printed_inconsistent` |
| pp. 797–798, Exercises 22.1–22.2 | §22.1 exercises | Out of scope here (other agent) |
