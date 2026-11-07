# Source map: Miao Chapter 8

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 8,
Applications, pp. 231–290. Lean names are relative to `Miao.Applications`; the models
of §8.3.1, §8.3.2 and §8.5 have their own structures (`cd1_Params`, `SIModel`, `INModel`).
Departures from the book are in [corrections](corrections.md).

## §8.1, §8.2, §8.4 and Exercises 8.1–8.2

### §8.1 Option exercise (`ODBasic`, `ODOption`, `ODWaiting`, `ODRisk`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 231 | i.i.d. payoffs `z ~ F` on `[0, B]`, `B > I`; Bellman equation `V(z) = max(β∫V dF, z − I)` | `od_OptionBellman`, `od_optΦ` |
| p. 231 | It is the Bellman equation of the stopping problem of §5.2.2 | `od_option_bellman_iff_stopping` (Chapter 5 `optionExercise`) |
| p. 231 | "There exists a unique solution `V`" (via the Contraction Mapping Theorem on the continuation value) | `od_option_exists_unique`, `od_optΦ_exists_unique`, `od_optΦ_lipschitz`, `od_option_cont_fixed`, `od_option_fixed_bellman`, `od_option_integral_eq`, `od_scalar_fixed`, `od_lipschitz_stop`, `od_abs_integral_sub_le`, `od_integrable_of_continuous`, `od_integrable_sub` |
| p. 231, Figure 8.1 | `V` is increasing and convex | `od_option_mono_convex` |
| p. 232 | `V(z) = z − I` for `z > z*`, `β∫V dF` for `z ≤ z*` | `od_option_threshold` |
| p. 232 | A unique threshold `z*`: invest iff the payoff exceeds `z*` | `od_option_threshold_unique_set` |
| p. 232 | The chain `V(z*) = β∫V dF = z* − I = β∫_0^{z*}(z* − I)dF + β∫_{z*}^B(z′ − I)dF = β∫_0^B(z* − I)dF + β∫_{z*}^B(z′ − z*)dF` | `od_option_at_threshold`, `od_setIntegral_Ioi_eq`, `od_integral_max_eq` |
| p. 232 | Threshold equation `z* − I = β/(1 − β)∫_{z*}^B(z′ − z*)dF` | `od_option_threshold_eq` |
| p. 233 | "A unique solution in `(0, B)`" (corrected: in `[I, B)`; in `(0, B)` when `I > 0`) | `od_option_threshold_root_unique`, `od_threshψ`, `od_threshψ_strictMono`, `od_optΦ_fixed_nonneg` |
| p. 233 | "`z* > I`" (corrected: iff `F(z > I) > 0`) | `od_option_threshold_gt_iff`; counterexample `od_option_threshold_dirac` |
| p. 233 | NPV rule: projects with positive NPV `z − I ≤ z* − I` are forgone | `od_option_npv` |
| p. 233 | `λ = F(z*)`, `Pr(N = j) = (1 − λ)λʲ` | `od_waitLam`, `od_waitEvent`, `od_waitEvent_eq`, `od_waitLam_mem`, `od_wait_prob`, `od_wait_total` |
| p. 233 | `E[N] = 1/(1 − λ)` (corrected: `λ/(1 − λ)`; `1/(1 − λ)` is `E[N + 1]`) | `od_wait_mean`, `od_wait_mean_dates`; misprint `od_wait_mean_misprint` |
| p. 233 | The mean waiting time increases with `z*` | `od_wait_mean_mono` |
| p. 233 | Second-order stochastic dominance with equal means | `od_Riskier` |
| pp. 233–234 | A riskier project is preferred (higher option value) and investment is delayed (higher threshold) | `od_option_riskier`, `od_integral_max_riskier`, `od_min_concave`, `od_fixed_le_of_le` |
| p. 234 | McCall's Bellman equation `V(w) = max(c + β∫V dF, w/(1 − β))` | `od_McCallBellman`, `od_mccall_bellman_iff_stopping` (Chapter 5 `jobSearch`), `od_mccall_iff_firing` |
| p. 234 | (Its unique solution, reservation wage and reservation-wage equation; the book only writes the equation) | `od_mccall_exists_unique`, `od_mccall_reservation` |
| pp. 233–234 | Remarks on asset substitution, risk vs uncertainty (Chapter 20) | No formal content |

### §8.2 Discrete choice (`ODDCSetting`, `ODDCTrigger`, `ODDCSolution`, `ODDCExamples`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 234 | The Bellman equation with exponential utilization increments | `od_DCBellman`, `od_dcp`, `od_dcE`, `od_dcM`, `od_dcR` |
| p. 234 | The book's integrals `∫_s^∞ V(s′)λe^{−λ(s′ − s)}ds′` | `od_dcE_book` |
| p. 235 | Existence of a solution ("dynamic programming theory with bounded reward") | `od_dc_exists`, `od_dcT`, `od_dcT_apply`, `od_dcT_contraction`, `od_dcE_continuous`, `od_dcE_mono`, `od_dcE_mono'`, `od_dcE_add_const`, `od_dcE_const`, `od_dcE_abs_le`, `od_dcE_abs_sub_le`, `od_dcE_integrable`, `od_dcp_pos`, `od_dcp_continuous`, `od_dcp_integrable`, `od_dcp_integral` |
| p. 235 | Uniqueness on `[0, ∞)` | `od_dc_unique` |
| p. 235, Figure 8.2 | `V` is decreasing and continuous | `od_dc_antitone`, `od_dcE_antitoneOn` |
| p. 235 | Never optimal to replace at `s = 0` | `od_dc_no_replace_zero` |
| p. 235 | The replacement value is constant | `od_dcR` (no state argument) |
| p. 235 | `s*` the smallest indifference point; maintain below, replace above (single crossing) | `od_dc_trigger`, `od_dcM_strictAntiOn` |
| p. 235 | Existence of `s*` (assumed in the book) | `od_dc_trigger_exists`; counterexamples `od_dc_no_trigger`, `od_dc_example_no_trigger` |
| (8.1), p. 235 | `V′(s) = −c′(s) + λc(s) + λ(1 − β)V(s)` on `(0, s*)` | `eq_8_1`, `od_dcE_hasDerivAt`, `od_dcM_hasDerivAt` |
| (8.2), p. 236 | `V(0) = −c(0) + β∫V λe^{−λs′}`, `V(s*) = −(P_b − P_s) + V(0)`, `V(s*) = −c(s*) + βV(s*)`, hence `V(s*) = −c(s*)/(1 − β)`, `V(0) = (P_b − P_s) − c(s*)/(1 − β)` | `eq_8_2` |
| p. 236 | The solution formula for `V` (corrected) | `od_dc_solution`, `od_dc_solution_book`, `od_dc_eq_M`; misprint `od_dc_solution_misprint`, `od_dc_example_misprint` |
| p. 236 | `s*` solves `P_b − P_s = ∫_0^{s*} c′(z)/(1 − β)[1 − βe^{−λ(1 − β)z}]dz`, uniquely | `od_dc_trigger_eq`, `od_dc_trigger_eq_unique`, `od_dcH`, `od_dcH_strictMonoOn`, `od_deriv_nonneg_of_monotoneOn` |
| pp. 236–237 | Replace whenever `s > s*`; the regenerative structure | `od_dc_trigger` (the policy); regeneration is the Bellman equation itself (replacement restarts at `s = 0`) |
| pp. 235–236 | A cost function satisfying all the assumptions | `od_dcArctan`, `od_dcArctan_apply`, `od_dcArctan_props` |

### §8.4 Consumption/portfolio choice (`ODPortfolio`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 260 | Budget constraint, wealth, `π_j = P_jψ_j/(W − C)`, `B/(W − C) = 1 − ∑π_j` | `od_portfolio_bond_share` |
| (8.17), p. 260 | `W_{t+1} = ∑(P′ + D′)ψ + R^f B = ∑R_jPψ + R^f B = R_w(W − C)`; `R_j`, `R_w` | `eq_8_17`, `od_Rw` |
| p. 261 | The Bellman equation's objective | `od_portObj` |
| p. 261 | First-order conditions for `C_t` and `π_jt` | `od_portfolio_foc`, `od_hasDerivAt_integral_fintype` |
| p. 261 | Envelope condition | `od_portfolio_envelope` |
| p. 261 | `u′(C_t) = βE[u′(C_{t+1})R_w] = V_t′(W_t)`, `0 = E[u′(C_{t+1})(R_j − R^f)]`, and the Euler equations for `R^f` and `R_j` | `od_portfolio_euler` |
| pp. 261–262 | Testable restrictions; equilibrium (Chapter 13) | No formal content |

### Exercises

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 8.1, p. 288 | McCall with Markov offers: Bellman equation, unique solution, value iteration | `od_MarkovSearchBellman`, `ex_8_1`, `od_msT`, `od_msT_apply`, `od_msT_contraction`, `od_ms_abs_integral_le`, `od_ms_integrable` |
| Ex 8.1, p. 288 | Characterisation: `V = max(Ψ, wage/(1 − β))`, accept iff `wage(w) ≥ (1 − β)Ψ(w)` | `ex_8_1_policy` |
| Ex 8.1, p. 288 | Monotone `V` and `Ψ` for monotone `Q` and wage | `ex_8_1_mono` |
| Ex 8.1, p. 288 | The i.i.d. case is McCall's rule | `ex_8_1_iid` |
| Ex 8.2, p. 288 | Firing with probability `α`: Bellman equations | `od_FiringBellman`, `od_firingΦ`, `od_firing_D_pos`, `od_firing_integrable`, `od_firingΦ_lipschitz`, `od_firing_fixed` |
| Ex 8.2, p. 288 | `E(w) = (w + αβU)/(1 − β + αβ)`; existence and uniqueness | `ex_8_2_E`, `ex_8_2` |
| Ex 8.2, p. 288 | Reservation wage `w̄ = (1 − β)U` and its equation, unique root | `ex_8_2_reservation`, `ex_8_2_reservation_eq`, `ex_8_2_root_unique`, `od_firingψ`, `od_firingψ_strictMono` |
| Ex 8.2, p. 288 | `w̄` decreases with `α` | `ex_8_2_alpha` |

## §8.3 (introduction), §8.3.1 and Exercise 8.8

### §8.3 Consumption and saving, pp. 237–240

| Source | Claim | Lean |
| --- | --- | --- |
| p. 237 | The usual conditions on `u` (`u′ > 0`, `u′′ < 0`, Inada) | `cd_Utility`, `cd_Utility.cd_tangent`, `cd_Utility.cd_tangent_strict`, `cd_Utility.cd_u_strictMono`, `cd_Utility.cd_u_strictConcave` |
| p. 237 | `u′` maps `(0, ∞)` onto `(0, ∞)`; `(u′)⁻¹` decreasing and continuous | `cd_Utility.cd_du_surj`, `cd_Utility.cd_duInv`, `cd_Utility.cd_duInv_pos`, `cd_Utility.cd_du_duInv`, `cd_Utility.cd_duInv_du`, `cd_Utility.cd_du_inj`, `cd_Utility.cd_duInv_anti`, `cd_Utility.cd_duInv_cont` |
| (8.3), p. 237 | The budget constraint | `cd_Budget` |
| (8.4), p. 237 | `c_t ≥ 0`, `a_{t+1} ≥ −b` | hypotheses of `theorem_8_3_1`; `cd_Feasible` (p. 239 variables) |
| p. 237 | Present value of bounded labour income is finite | `cd_summable_pv` |
| (8.5), p. 237 | The no-Ponzi-game condition | `cd_NoPonzi` |
| (8.6), p. 238 | The present-value budget identity | `eq_8_6` |
| p. 238 | Rolling over debt `a_{T+1} = R^T a_1 < 0` violates (8.5) | `cd_rollover` |
| Theorem 8.3.1, p. 238 | `a_{t+1} ≥ −b` ⇒ (8.5) (the limit exists and is `≥ 0`) | `theorem_8_3_1`, `theorem_8_3_1_noPonzi`, `cd_tendsto_div_pow` |
| p. 238 (proof) | `Ra_0 + ∑ y_t/Rᵗ ≥ ∑ c_t/Rᵗ` | `theorem_8_3_1_pv` |
| Theorem 8.3.1 (converse), pp. 238–239 | (8.5) ⇒ `a_t ≥ −y_min/r` a.s. (corrected hypothesis) | `theorem_8_3_1_converse`, `theorem_8_3_1_converse_counterexample` |
| p. 239 (proof) | `a_{t+n} ≤ −y_min/r + (rε/2)(1 + … + R^{n−1}) − Rⁿε`, so `a_{t+n}/Rⁿ < −ε/2` (corrected) | `cd_converse_path`, `cd_telescope` |
| p. 239 | `b > y_min/r` ⇒ the borrowing constraint never binds | `cd_natural_debt_nonbinding` |
| p. 239 | Change of variables `â_t = a_t + b`, `x_t = Ra_t + y_t + b` | `cd_IsPath`, `cd_change_of_variables` |
| (8.7), p. 239 | The Euler inequality, derived from optimality | `cd_Euler`, `eq_8_7`, `cd_perturb_feasible`, `cd_perturb_partial` |
| (8.8), p. 239 | The transversality condition | `cd_TVC`, `cd_TVCs`, `cd_TVCs_of_TVC` |
| p. 240 | (8.7)–(8.8) are sufficient for optimality | `eq_8_7_8_8_sufficient`, `cd_sufficient`, `cd_sum_le`, `cd_partial_le` |
| p. 240 | Optimal plans maximise the value among summable plans; equal values | `cd_tendsto_partial`, `cd_tsum_le_of_optimal`, `cd_tsum_eq_of_optimal` |
| p. 240 | The stochastic Bellman equation; i.i.d. case; existence and properties of `V` | Not formalised: the book assumes them ("Here, we simply assume …"); for deterministic income Case 1 proves them, below |
| p. 240 | `c(x)` strictly increasing (from the envelope condition and concavity) | `cd1_Params.c_strictMono` (Case 1) |

### §8.3.1 Deterministic income, Case 1 (`βR < 1`), pp. 240–245

| Source | Claim | Lean |
| --- | --- | --- |
| (8.9), p. 240 | The Bellman equation, maximum attained at `â(x)` | `eq_8_9`, `cd1_Params.V`, `cd1_Params.cpol`, `cd1_Params.C`, `cd1_Params.Xp`, `cd1_Params.kOf`, `cd1_Params.zOf`, `cd1_Params.kz_spec` |
| p. 241 | The Euler map `φ(c) = (u′)⁻¹(βRu′(c))`, `φ(c) > c`, increasing, continuous | `cd1_Params.phi`, `cd1_Params.phi_pos`, `cd1_Params.du_phi`, `cd1_Params.lt_phi`, `cd1_Params.phi_strictMono`, `cd1_Params.phi_cont`, `cd1_Params.phi_mapsTo`, `cd1_Params.iter_pos`, `cd1_Params.iter_lt_succ`, `cd1_Params.le_iter`, `cd1_Params.iter_strictMono`, `cd1_Params.iter_cont`, `cd1_Params.du_iter`, `cd1_Params.iter_unbounded` |
| (8.10), p. 241 | Unique `x*_0 > y − rb` with `u′(x*_0) = βRu′(y − rb)` | `eq_8_10`, `cd1_Params.xstar0`, `cd1_Params.w`, `cd1_Params.w_pos` |
| (8.11), p. 241 | For `x ∈ [x*_{−1}, x*_0]`, exhaust the limit at once; optimal | `eq_8_11` |
| p. 242 | `V_0(x) = u(x) + β/(1−β) u(y − rb)` | `cd1_Params.V0_value` |
| p. 242 | `V_0` satisfies (8.9) ("deterministic version of Theorem 7.1.1") and `V_0′ = u′` | `eq_8_9`, `cd1_Params.V_envelope` |
| (8.12), p. 242 | `h_0` from the Euler equation; `h_0` continuous, increasing; `h_0(x*_{−1}) = x*_0` | `eq_8_12`, `cd1_Params.X`, `cd1_Params.X_zero`, `cd1_Params.X_succ`, `cd1_Params.X_strictMono`, `cd1_Params.X_cont`, `cd1_Params.xstar_zero` |
| pp. 243–244 | The induction: intervals, maps `h_s`, policies `g_s, f_s`, values `V_s`; agreement at `x*_s` | `cd1_Params.xstar`, `cd1_Params.xstar_eq`, `cd1_Params.X_succ_w`, `cd1_Params.w_le_X`, `cd1_Params.iter_le_X`, `cd1_Params.X_lt_succ`, `cd1_Params.pc`, `cd1_Params.px`, `cd1_Params.ys`, `cd1_Params.plan_saving` |
| (8.13), p. 244 | `h_t` from the Euler equation | `eq_8_13` |
| p. 244 | `x*_{t+1} > x*_t` | `cd1_Params.xstar_strictMono`, `cd1_Params.w_lt_xstar` |
| p. 245 | The intervals cover `[y − rb, ∞)` | `cd1_Params.xstar_tendsto`, `cd1_Params.exists_kz` |
| (8.14), pp. 244–245 | The constructed plan is feasible, satisfies (8.7) and TVC, and is optimal | `eq_8_14`, `cd1_Params.plan_feasible`, `cd1_Params.plan_euler`, `cd1_Params.plan_tvcs`, `cd1_Params.C_optimal`, `cd1_Params.C_feasible`, `cd1_Params.C_euler`, `cd1_Params.C_TVCs` |
| p. 245 | Not exhausted in periods `0..t`, exhausted from `t + 1` on | `cd1_Params.plan_binding`, `cd1_Params.plan_eventually`, `cd1_Params.C_eventually` |
| p. 245 | `V_{t+1}(x) = u(f_{t+1}(x)) + βV_t(h_t⁻¹(x))` | `cd1_Params.plan_value`, `cd1_Params.plan_summable`, `cd1_Params.summable_of_eventually`, `cd1_Params.C_summable`, `eq_8_9` |
| pp. 243, 245 | `V_s` strictly increasing, strictly concave | `cd1_Params.V_strictMono`, `cd1_Params.V_strictConcave`, `cd1_Params.Xp_diff` |
| pp. 243, 245 | Envelope condition `V′(x) = u′(c(x))` | `cd1_Params.V_envelope` (via `theorem_4_10`) |
| p. 245 | `V` satisfies (8.9) on `[y − rb, ∞)` | `eq_8_9`, `cd1_Params.Xp_zero`, `cd1_Params.Xp_one`, `cd1_Params.w_le_Xp`, `cd1_Params.cpol_pos`, `cd1_Params.cpol_le` |
| p. 245 | The policy-generated sequences are optimal | `cd1_Params.policy_path_optimal`, `cd1_Params.shift_optimal`, `cd1_Params.shift_eq`, `cd_shift_feasible`, `cd_shift_euler`, `cd_shift_TVCs`, `cd_optimal_unique` |
| p. 245 | `c_t, a_{t+1}, x_t` decrease until `T`, then `c_t = x_t = y − rb`, `a_{t+1} = −b` | `cd1_Params.plan_dynamics`, `cd1_Params.plan_binding` |
| p. 241 | `βR < 1` with `R > 1` gives `β < 1` | `cd1_Params.β_lt_one`, `cd1_Params.R_pos`, `cd1_Params.βR_pos` |

### §8.3.1 Case 2 (`βR > 1`), p. 246

| Source | Claim | Lean |
| --- | --- | --- |
| p. 246 | The borrowing constraint never binds | `cd2_never_binding`, `cd2_w_le_x` |
| p. 246 | `c_t < c_{t+1}` | `cd2_c_strictMono` |
| p. 246 | `lim c_t = ∞` | `cd2_c_tendsto` |
| p. 246 | `lim x_t = lim â_{t+1} = ∞` | `cd2_x_tendsto`, `cd2_s_tendsto` |

### §8.3.1 Case 3 (`βR = 1`), pp. 246–249

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 246–247 | `c_t ≤ c_{t+1}`, strictly only if `â_{t+1} = 0` | `cd3_monotone` |
| p. 247 | The annuity value `A_t` (corrected) and the printed formula | `cd3_A`, `cd3_Abook`, `cd3_summable`, `cd3_A_bdd` |
| p. 247 | Chamberlain–Wilson: `lim c_t = sup_t A_t` (corrected: `a₀ = −b`) | `cd3_chamberlain_wilson`, `cd3_chamberlain_wilson_counterexample`, `cd3_Abook_counterexample` |
| p. 247 | `c* ≤ A*` (corrected: constrained at some date) | `cd3_upper`, `cd3_le_A_of_constrained`, `cd3_budget_ge`, `cd_budget_iter`, `cd3_geom_tendsto` |
| pp. 247–248 | `c* ≥ A*`: the improving deviation | `cd3_lower` |
| Example 8.3.1, p. 248 | Present value, annuity value `c̄` | `example_8_3_1_pv`, `example_8_3_1_annuity`, `cd_cbar`, `cd_cbar_eq`, `cd_cbar_bounds`, `cd_y1` |
| Example 8.3.1, p. 248 | Savings `a_{t+1}` (corrected) | `example_8_3_1_savings`, `example_8_3_1_savings_misprint`, `cd_a1` |
| Example 8.3.1, p. 248 | Consuming `c̄` satisfies the Euler equation, optimal; footnote 1 | `example_8_3_1`, `cd_x1` |
| Example 8.3.2, p. 249 | `c_0 = y_l`, `a_1 = 0`, then Example 8.3.1; constrained in the first period only | `example_8_3_2`, `cd_y2`, `cd_c2`, `cd_x2` |
| p. 249 | Constant income: `c_t = y + ra₀`, `a_{t+1} = a₀` is optimal | `cd3_constant_income` |

### Exercise 8.8, p. 289

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 8.8 | The problem with the natural borrowing constraint (no-Ponzi) | `cd8_Feasible`, `cd8_Optimal`, `cd8_W`, `cd8_g`, `cd8_c`, `cd8_a`, `cd8_a_budget`, `cd_crraUtility`, `cd_crraUtility_u`, `cd_crraUtility_du`, `cd_rpow_neg_strictAnti` |
| Exercise 8.8 | Feasibility requires `W > 0` | `ex_8_8_W_pos` |
| Exercise 8.8 | Derive the optimal policy: `c_t = (1 − q)Wgᵗ`, optimal | `ex_8_8`, `cd8_marginal`, `cd8_g_pos`, `cd8_g_rpow` |
| Exercise 8.8 | The policy in feedback form `c_t = (1 − q)(Ra_t + h_t)` | `ex_8_8_policy` |
| Exercise 8.8 | Conditions for a finite value: `βR^{1−γ} < 1` (automatic if `γ > 1`), value formula | `ex_8_8_q_lt_one`, `ex_8_8_gamma_gt_one`, `ex_8_8_value` |
| Exercise 8.8 | `βR^{1−γ} ≥ 1`, `γ < 1`: infinite value | `ex_8_8_infinite` |
| Exercise 8.8 | Cases `βR > 1`, `βR < 1`, `βR = 1` | `ex_8_8_cases` |

## §8.3.2 (stochastic income) and Exercises 8.9–8.11

### §8.3, the model in cash on hand (pp. 237–240)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 237, 249 | The problem with iid income, `u′ > 0`, `u′′ < 0`, Inada, `b < y_min/r` | `SIModel`, `SIModel.law`, `SIModel.r`, `SIModel.xmin`, `SIModel.xmin_pos'` |
| p. 239 | `x_t = Ra_t + y_t + b`, `â_{t+1} = a_{t+1} + b`: `c_t + â_{t+1} = x_t`, `x_{t+1} = R(x_t − c_t) + y_{t+1} − rb`, `â_{t+1} ≥ 0` | `si_cash_on_hand`, `SIModel.next`, `M.next_ge`, `M.next_sub`, `M.next_ymin`, `M.next_ymax_sub`, `M.ae_next` |
| p. 240 | The Bellman equation in cash on hand; `V` strictly increasing, strictly concave, `C¹`, envelope `V′(x) = u′(c(x))` (assumed by the book) | `SIModel.Solution`, `S.cons`, `S.W`, `S.D`, `S.bellman'`, `S.bellman_le'` |
| p. 240 (tools) | `V′` strictly decreasing and `≥ 0`; mean value bounds for `u`, `V`; `W`, `D` bounds; `D` strictly decreasing, continuous; integrability | `S.dV_strictAnti`, `S.dV_nonneg`, `M.tangent_u`, `S.tangent_V`, `S.V_contOn`, `M.integrable_comp`, `S.integrable_V`, `S.integrable_dV`, `S.W_sub_bounds`, `S.D_le`, `S.D_nonneg`, `S.D_strictAnti`, `S.D_continuousOn`, `si_integral_pos` |
| p. 240 | Consumption is interior (Inada) | `S.cons_pos`, `S.cons_eq` |
| (8.7), p. 239 | Euler inequality `u′(c_t) ≥ βR E_t u′(c_{t+1})`, equality if `â_{t+1} > 0`, derived from the Bellman equation | `S.euler_le`, `S.euler_ge`, `S.euler`, `S.eq_8_7`, `S.D_eq`, `S.dV_pos`, `S.D_pos` |
| (8.8), p. 239 | Transversality condition | Not formalised (§8.3 introduction; not used in §8.3.2) |

### §8.3.2, Lemmas 8.3.1–8.3.2 (pp. 249–251)

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 8.3.1, p. 249 | `c` strictly increasing; `0 ≤ â(x′) − â(x) < x′ − x`, equality iff `â(x′) = â(x) = 0` | `S.lemma_8_3_1`, `S.sav_lt_of_pos`, `S.sav_lt_of_zero` |
| p. 250 | Where the constraint does not bind, `c` and `â` strictly increasing with slope `< 1`; holds for any `βR` | `S.sav_strictMono_of_pos` |
| (consequences) | `â`, `c` monotone, `1`-Lipschitz, continuous | `S.sav_mono`, `S.cons_mono`, `S.sav_sub_bounds`, `S.cons_sub_bounds`, `S.sav_lipschitz`, `S.continuousOn_sav`, `S.continuousOn_cons` |
| p. 251, proof | The constraint binds iff `u′(x) ≥ βR E V′(y − rb)`; with `βR < 1` it binds at `x_min` | `S.sav_eq_zero_iff`, `S.sav_xmin` |
| Lemma 8.3.2, p. 251 | `βR < 1`: `x̂ > x_min`, `â = 0` on `[x_min, x̂]`, `â > 0` above, `x̂` unique root of `u′(x̂) = βR E V′(y − rb)` | `S.lemma_8_3_2` |

### §8.3.2, Case 1 `βR < 1`: Lemma 8.3.3, Exercise 8.9 (pp. 252–254, 289)

| Source | Claim | Lean |
| --- | --- | --- |
| Footnote 2, p. 253 | `−cu′′/u′ ≤ γ` on `(c₀, ∞)` ⇒ `u′(c)/u′(c₀) ≥ (c₀/c)^γ` | `M.footnote_2`, `M.footnote_2_mono`, `M.du_le_rpow`, `SIModel.si_one_add_rpow_le` |
| p. 252, proof | `â` bounded: `x* = RK + y_max − rb` | `S.lemma_8_3_3` (first case) |
| p. 253 | `â` unbounded ⇒ `c(x) → ∞` | `S.cons_unbounded`, `S.sav_eventually_gt` |
| p. 253 | `c(y_max − rb + Râ) = c(y_min − rb + Râ) + y_max − y_min` | FALSE: `S.eq_8_16_identity_false`; true `≤`: `S.cons_high_le` |
| (8.16), p. 253 | `1 ≤ E V′(x′)/V′(M) ≤ (1 + (y_max − y_min)/c(m))^γ` | `S.eq_8_16`, `S.D_le_low`, `S.high_le_D` |
| Lemma 8.3.3, p. 252 | `βR < 1`, RRA `< γ` for large `c`: `x_t > x*` ⇒ `x_{t+1} < x_t` | `S.lemma_8_3_3`, `S.lemma_8_3_3_all` |
| p. 254 | `x_max`, the smallest critical value; long-run interval `[x_min, x_max]` | `S.fixHigh`, `S.xmax`, `S.continuousOn_gap`, `S.mapsTo_Icc` |
| Exercise 8.9, p. 289 | `x_max > x_min`; `x_max` the largest solution of `Râ(x) + y_max − rb = x` | `S.ex_8_9` |

### §8.3.2, Proposition 8.3.1 (pp. 254–256)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 255 | The transition function `P` on `[x_min, x_max]` | `S.kmap`, `S.continuous_kmap`, `S.continuous_kmap_y`, `S.kernel`, `S.kernel_eq`, `S.kernel_apply`, `S.isMarkovKernel_kernel`, `S.markovOpR_kernel` |
| p. 255 | `P` is monotone and Feller | `S.kmap_mono`, `S.isMonotoneTF_kernel`, `S.isFeller_kernel` |
| p. 255 | `φₙ(x, y)`; increasing in `y` (and `x`) | `S.phi`, `S.phi_zero`, `S.phi_succ`, `S.phi_ge`, `S.phi_succ_ge`, `S.phi_mono`, `S.phi_mem`, `S.continuousOn_phi` |
| p. 255, displays | `Pⁿ(x, [φₙ(x, y_max − δ), φₙ(x, y_max)]) ≥ αⁿδⁿ`, `Pⁿ(x, [φₙ(x, y_min), φₙ(x, y_min + δ)]) ≥ αⁿδⁿ` | `S.kpow_ge`, `S.kpow_ge_real`, `S.si_kpow_succ_ge_pow`, `S.si_clamp_mem` |
| p. 256 | `φₙ(x_min, y_max)` "strictly increasing" | Corrected (nondecreasing): `S.phi_high_monotone`; failure of strictness: `S.phi_two_eq_one` |
| p. 256, "a similar argument applies to `x₀ = x_max`" | With income `y_min`, cash on hand falls to `x_min` | `S.next_low_lt`, `S.next_low_le`, `S.phi_low_tendsto` |
| p. 255–256 | Mixing condition `Pᴺ(x_min, [x̄, x_max]) ≥ ε`, `Pᴺ(x_max, [x_min, x̄]) ≥ ε` | `S.mixing` |
| Proposition 8.3.1, p. 254 | Unique stable stationary distribution on `[x_min, x_max]` (via Theorems 3.3.5–3.3.6 = SLP 12.12) | `S.proposition_8_3_1`, `SIWC.theorem_12_12_real` |
| Proposition 8.3.1, p. 255 | Continuity of the stationary distribution in `R` and `b` | Not formalised (see corrections, item 5) |
| p. 256, `ξ > x̄` with `x̄ = lim φₙ(x_min, Ey)` | The book's choice of `x̄` | Not formalised (a different `x̄` is used; corrections, item 4) |

### §8.3.2, Case 2 `βR > 1` (pp. 256–258)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 257 | `M_t = βᵗRᵗu′(c_t)` is a supermartingale (one-step inequality) | `S.eq_8_7` |
| p. 257 | Supermartingale Convergence Theorem on the path space | Not formalised |
| p. 257 | `M_t` convergent, `βR > 1` ⇒ `u′(c_t) → 0`, `c_t → ∞`, `x_t → ∞` | `M.supermartingale_limit` |
| Proposition 8.3.2 (i), p. 257 | `lim â(x) = ∞` | `S.proposition_8_3_2_i` |
| p. 258 | `c(x) → ∞` ("similar argument") | `S.cons_unbounded_gt` |
| Proposition 8.3.2 (ii), p. 257 | RRA `< γ` for large `c`: `x_t > x̃` ⇒ `x_{t+1} > x_t` | `S.proposition_8_3_2_ii`, `S.proposition_8_3_2_ii_all` |

### §8.3.2, Case 3 `βR = 1` (pp. 258–259)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 258 | If `x_t` converges, the budget constraint and continuity of `â` force `y_t` to converge | `S.limit_of_converge` |
| p. 258 | `y_t` near `y_min` and near `y_max` infinitely often ⇒ `x_t` does not converge (corrected) | `S.not_converge` |
| p. 258 | Almost-sure statements (Chamberlain–Wilson, `c_t → ∞` a.s.) | Not formalised (path space) |
| p. 259 | `Râ(x) + y_min − rb ≤ x ≤ Râ(x) + y_max − rb` where the constraint does not bind | `S.sotomayor_bounds` |
| p. 259 | `x > Râ(x) + y_min − rb` ⇒ `x_{t+1} < x_t` with positive probability | `S.sotomayor_fall` |
| Lemma 8.3.4, p. 259 | No `x̃` with `x = Râ(x) + y_min − rb` for all `x > x̃` | `S.lemma_8_3_4` |

### Exercises 8.10–8.11 (pp. 289–290)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 8.10, p. 289 | Levhari–Mirman–Zilcha: characterise the CARA policies with `0 ≤ c ≤ x` | Not formalised (see corrections, item 9) |
| Exercise 8.11, p. 289 | The model with AR(1) income; the value `V(x, y) = −Āe^{−ᾱ(x + ρy/(R − ρ))}` and saving `s̄(x + κy) − κy` solve the Bellman equation, uniquely maximised | `si_arLaw`, `si_arLaw_ae`, `si_arV`, `si_arSav`, `si_arObj`, `si_arObj_eq`, `ex_8_11` |
| Exercise 8.11 | Explicit consumption `c = (1 − 1/R)(x + ρy/(R − ρ)) − L̄/(γR)`, `L̄ = R ln(βRM̄)/(R − 1)` | `ex_8_11_consumption`, `si_caraLbar_eq` |
| Exercise 8.11, `ρ = 0` | `x_{t+1} = x_t + L̄/γ + ε_{t+1}` | `ex_8_11_rho_zero`, `si_arSav_zero_continuous` |
| Exercise 8.11, `ρ = 0` | No stationary distribution (when `L̄/γ + ε` is not a.s. `0`) | `ex_8_11_no_stationary`, `si_no_stationary`, `si_iidKernel`, `si_iidKernel_apply`, `si_isMarkovKernel_iidKernel` |
| Exercise 8.11, `ρ = 0` | Counterexample to the claim as stated (degenerate `ε`, `βR = 1`) | `ex_8_11_counterexample` |

## §8.5 Inventory and Exercises 8.3–8.7

### Setting (pp. 262–264)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 262, (8.18)–(8.19) | Primitives `β`, `c`, `p`, `L`, demand distribution `ϕ` | `INModel`, `INModel.Assumption851` |
| p. 262 | Ordering cost `C(d) = c·1_{d>0} + pd` | `in_fix`, `INModel.TT` |
| p. 263, (8.20) | Change of variables `y_t = x_t + d_t`; cost-minimisation form | `eq_8_20` |
| p. 263 | `L(y) = βEΦ(y − z)` (convex when `Φ` is) | `in_L_convex` |
| Assumption 8.5.1, p. 263 | `L ≥ 0` convex and coercive (corrected) | `INModel.Assumption851`, `in_Coercive`, `INModel.assumption_8_5_1_counterexample` |
| p. 263, (8.21) | Bellman equation, Bellman operator `T` | `INModel.T`, `INModel.TT`, `INModel.TT_eq` |
| p. 264 | `f_n = Tⁿf₀`, `f₀ = 0` | `INModel.fn`, `INModel.fn_zero`, `INModel.fn_succ` |
| Figure 8.5, p. 264 | One-period problem: (s, S) form | `INModel.fig_8_5`, `INModel.G_one` |

### Finite-horizon problem (pp. 265–270)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 265, (8.22) | The `n`-period problem; its "order / do not order" form | `INModel.fn_succ`, `INModel.eq_8_22_split` |
| p. 265 | `G_n(y) = L(y) + py + βEf_{n−1}(y − z)`; `S_n` the smallest minimiser | `INModel.G`, `INModel.Gf`, `INModel.G_succ`, `INModel.Sn`, `INModel.Sn_isLeast`, `in_Sbar`, `in_Sbar_isLeast` |
| p. 265, (8.23) | `G_n(s_n) = c + G_n(S_n)`, `s_n < S_n` (for `c > 0`) | `INModel.eq_8_23`, `INModel.sn`, `INModel.sn_isLeast`, `in_sbar`, `in_sbar_isLeast`, `in_ss_eq`, `in_ss_lt_of_pos` |
| p. 265 | If ordering to `y` is optimal, `y` minimises `G_n` beyond `x` | `lemma_8_5_2`, `in_ss_gt` |
| Definition 8.5.1, p. 266, (8.24)–(8.25) | c-convexity; (8.25) ⇒ (8.24) for differentiable `h` | `in_CConvex`, `in_CConvexDiff`, `definition_8_5_1` |
| Lemma 8.5.1, p. 266 | `c + h(y) − h(x) − (y − x)h′(u) ≥ 0`, `y > x > u` | `lemma_8_5_1` |
| p. 266–267, (i) | Convex ⇒ 0-convex; c-convex ⇒ c′-convex for `c′ ≥ c` | `in_cconvex_zero_of_convexOn`, `in_cconvex_mono`, `in_cconvex_affine` |
| p. 266, (ii) | Translates are c-convex | `in_cconvex_comp_add` |
| p. 267, (iii) | `αf + γg` is `(αc + γb)`-convex | `in_cconvex_add_smul` |
| Figure 8.6, pp. 267–268 | No "not order / order / not order" pattern | `fig_8_6`, `in_cconvex_local_max` |
| Lemma 8.5.2, p. 268 | The (s, S) policy is optimal | `lemma_8_5_2`, `in_ss_value`, `in_ss_policy_value`, `in_ss_key`, `in_ss_le`, `in_ssPolicy`, `INModel.lemma_8_5_2_fn`, `INModel.T_eq`, `INModel.T_attained` |
| p. 269 | `G_n` is decreasing on `(−∞, s_n)` | `in_ss_strictAnti` |
| Lemma 8.5.3, pp. 269–270 | `G_n` is c-convex for all `n ≥ 1` | `INModel.lemma_8_5_3`, `INModel.good_fn`, `INModel.good_T`, `in_ss_cconvex_max`, `in_cconvex_integral`, `INModel.Gf_cconvex` |
| p. 270, (8.26) | `f_n(x) = −px + G_n(s_n)` for `x ≤ s_n`, `−px + G_n(x)` for `x > s_n`; `f_n` continuous | `INModel.eq_8_26`, `INModel.fn_eq`, `INModel.good_fn` |
| Assumption 8.5.2, p. 270 | `L` differentiable | `INModel.Assumption852` |
| p. 270, (8.27)(i) | Derivative of `f_n` off `s_n`, one-sided derivatives at `s_n` | `INModel.eq_8_27` |
| p. 270, (ii) | `G_n` differentiable (false with atoms) | `INModel.eq_8_27_ii_counterexample`; the positive version for a demand density is not formalised (not needed: all proofs are derivative-free) |
| Lemma 8.5.4, p. 270; **Exercise 8.3** | `S_1 ≤ S_n` (hint: `G_n` decreasing on `(−∞, S_1]`) | `INModel.lemma_8_5_4`, `INModel.ex_8_3`, `INModel.G_one_strictAnti` |
| Lemma 8.5.5, p. 271 | `S_n ≤ M`; `G_n(x + a) − G_n(x) ≥ L(x + a) − L(x) − c` | `INModel.lemma_8_5_5`, `INModel.eq_p271`, `INModel.Gf_diff` |
| Lemma 8.5.6, p. 272 | `2s_1 − S_1 < s_n` (`c > 0`; `≤` for `c ≥ 0`); slope bound | `INModel.lemma_8_5_6`, `INModel.lemma_8_5_6_le`, `INModel.lemma_8_5_6_slope`, `INModel.lemma_8_5_6_counterexample` |

### Infinite-horizon problem (pp. 272–276)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 272 | `f = lim f_n`, `G(x) = px + L(x) + βEf(x − z)` | `INModel.f`, `INModel.Glim` |
| p. 273–274 | Contraction estimate on `[−A, B]` and its iteration | `INModel.diff_bound`, `INModel.partial_bound`, `INModel.fn_le_bound`, `INModel.tail_bound`, `INModel.G_tail_bound`, `INModel.fn_left` |
| Proposition 8.5.1, p. 272 | `f_n ↑ f`, `G_n ↑ G`, uniformly on finite intervals; `f`, `G` continuous | `INModel.proposition_8_5_1`, `INModel.fn_tendsto`, `INModel.fn_mono`, `INModel.G_mono`, `INModel.good_f` |
| Proposition 8.5.2, p. 274 | `f` satisfies (8.21) | `INModel.proposition_8_5_2`, `INModel.f_le_TT` |
| Proposition 8.5.3, p. 275; **Exercise 8.4** | Convergent subsequences; limit points of `S_n` minimise `G`; unique minimiser ⇒ convergence; `G` c-convex; `G(s) = c + G(S)`; infinite-horizon (s, S) policy | `INModel.proposition_8_5_3`, `INModel.ex_8_4`, `INModel.ex_8_4_policy`, `INModel.ex_8_4_lt`, `INModel.Glim_ge_of_le`, `INModel.Glim_cconvex`, `INModel.in_IsLimitPoint` |
| Proposition 8.5.4, p. 275 | Uniqueness of the solution of (8.21) (proof omitted in the book) | `INModel.proposition_8_5_4`, `INModel.P_of_bellman`, `INModel.dominate`, `INModel.L_mono_right` |
| p. 275 | Law of motion of `{x_t}` under the (s, S) policy | `in_invKernel`, `ex_8_5_transition` |
| p. 276 | Stationary distribution via Theorem 3.3.1 / Condition M | `ex_8_5`, `ex_8_5_minorization` (with `MinorizationFor`, `proposition_3_3_1_forward`, `theorem_3_3_1_invariant` copied in `INMPStrong`) |

### Exercises 8.3–8.7, p. 288

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 3 | Prove Lemma 8.5.4 | `INModel.ex_8_3`, `INModel.lemma_8_5_4` |
| Exercise 4 | Prove Proposition 8.5.3 | `INModel.ex_8_4`, `INModel.proposition_8_5_3`, `INModel.ex_8_4_policy`, `INModel.ex_8_4_lt` |
| Exercise 5 | `{x_t}` is Markov; transition function; unique stationary distribution (under `ϕ(z > S − s) > 0`) | `ex_8_5_markov`, `ex_8_5_transition`, `in_invKernel_isMarkov`, `ex_8_5_absorbing`, `in_invKernelX`, `ex_8_5_transitionX`, `ex_8_5_minorization`, `ex_8_5`, `ex_8_5_counterexample` |
| Exercise 6 | Exponential demand: characterize `s` and `S` | `INModel.ex_8_6`, `INModel.Glim_decomp` (stated with `Ez = ∫ z dϕ`; the exponential mean `1/λ` is not computed) |
| Exercise 7 | `c = 0`: `s = S`, `p(1 − β) + L′(s) = 0` | `INModel.ex_8_7`, `INModel.ex_8_7_H`, `in_sbar_eq_of_zero` |

## §8.6 Investment and Exercises 8.12–8.14

### §8.6.1 Neoclassical theory (`IVNeoclassical`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 276 | The rental firm's problem reduces to static profit maximisation (partial and convergent sums) | `iv_static_reduction` |
| p. 276 | `F₁(K, L) = R_k`, `F₂(K, L) = w` at an interior maximum | `iv_rental_foc` |
| p. 277, (8.28)–(8.29) | The first-order conditions `Qₜ = 1`, `Qₜ = β(1 − δ + F₁)`, by perturbing `K_{t+1}` | `eq_8_29_foc` |
| p. 277 | `F₁(K_{t+1}, L_{t+1}) = r + δ` | `iv_F1_eq_r_add_delta` |
| p. 277 | With `R_k = r + δ` the two problems give identical solutions (summation-by-parts identity; comparison of plans) | `iv_ownedObj`, `iv_rentalObj`, `iv_owned_partialSum`, `iv_owned_le_of_rental` |
| p. 277 | `π(K) = max_L F(K, L) − wL` and the envelope condition `π′(K) = F₁(K, L)` | `iv_envelope_profit` |
| p. 277 | Cobb–Douglas: optimal labour and its first-order condition | `iv_cd`, `iv_cdLabour`, `iv_cdLabour_eq`, `iv_cd_foc`, `iv_cd_max` |
| p. 277 | `π(K) = K^{α_k/(1−α_l)} (α_l/w)^{α_l/(1−α_l)} (1 − α_l) = A K^{α_k/(1−α_l)}` | `iv_cdA`, `iv_cd_profit` |
| p. 277 | The envelope condition for Cobb–Douglas | `iv_cd_envelope` |
| p. 277 | CRS ⇒ `π = AK`; IRS ⇒ `π` convex; DRS ⇒ `π` concave | `iv_cd_crs`, `iv_cd_convex`, `iv_cd_concave` |

### §8.6.2 Q theory (`IVQTheory`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 278 | Partial derivatives of the adjustment cost | `iv_HasPartials`, `iv_HasPartials.comp` |
| p. 278 | Assumptions `Ψ₁ > 0`, `Ψ₁₁ < 0`, `Ψ ≥ 0`, `Ψ(0, ·) = 0` (inconsistent) | `iv_psi_assumptions_inconsistent` |
| p. 278, (8.30)–(8.31) | First-order conditions, by perturbing `K_{t+1}` | `eq_8_30_8_31` |
| p. 278, (8.32) | The transversality condition | hypothesis `h832` of `iv_hayashi`, `iv_q_optimal` |
| p. 279 | (8.30): investment increases with `Q` (for `Ψ₁₁ > 0`; decreases for the printed `Ψ₁₁ < 0`) | `iv_invest_mono`, `iv_invest_anti_of_concave` |
| p. 279, (8.33) | Forward iteration of (8.31) and the present-value formula for `Q` | `iv_Q_iterate`, `iv_tail_shift`, `eq_8_33` |
| p. 279 | `lim βᵀ(1 − δ)ᵀQ_{T+1} = 0` "follows from" (8.32): false in general, true for nonnegative investment and `Q ≥ 0` | `iv_tvc_not_implies`, `iv_tvc_implies` |
| pp. 278–279 | Sufficiency of (8.30)–(8.32) for concave `π(K) − I − Ψ(I, K)` (not stated in the book) | `iv_qReward`, `iv_qReward_hasFDerivAt`, `iv_q_sufficient`, `iv_q_optimal` |
| p. 280 | Linear homogeneity: `Ψ₂ = (Ψ − IΨ₁)/K` (Euler's theorem) | `iv_euler_homog` |
| p. 280 | `QₜK_{t+1} = β[AK_{t+1} − Ψ − I_{t+1}] + βK_{t+2}Q_{t+1}` | `iv_hayashi_step` |
| p. 280 | Iterating forward with (8.32): `QₜK_{t+1} = Σ_{j≥1} βʲ[π(K_{t+j}) − I_{t+j} − Ψ]` (Hayashi) | `iv_hayashi_iterate`, `iv_hayashi` |
| p. 280 | Marginal Q equals average Q | `iv_marginal_eq_average` |
| p. 280, (8.34) | Uzawa's formulation; "both formulations deliver similar results" | `ex_8_14_equiv`, `ex_8_14_Q_same` (see Exercise 14) |

### §8.6.3 Augmented adjustment costs (`IVAugmented`, `IVExample861`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 281 | The cost function `C(I, K)` and the firm's objective | `iv_C`, `iv_C_eq_objective` |
| p. 281, (8.35) | `V = max{Vⁱ, Vᵇ, Vˢ}` | `iv_R`, `eq_8_35` |
| p. 282, (8.36) | Optimal investment solves (8.36) (corrected: `φ(K)` only for `I ≠ 0`) | `eq_8_36`, `iv_phi_eq`, `iv_eq_8_36_misprint` |
| p. 282 | First-order Taylor approximation; `ψ(Q, K)` | `eq_8_37_taylor`, `iv_g` |
| p. 282, (8.37) | Marginal Q at zero investment | `iv_q_monotone` (the function `βE[V₁((1 − δ)K, z′) | z]`) |
| p. 283, footnote 8 | `Q = βE[V₁((1 − δ)K + I*, z′) | z]` at an optimal `I*` | `iv_footnote_8` |
| p. 283, (8.38)–(8.40) | The three regimes without fixed costs (sufficiency, necessity) | `iv_g_le_buy`, `iv_g_le_sell`, `iv_concave_max`, `eq_8_38`, `eq_8_39`, `eq_8_40`, `iv_static_necessary` |
| p. 283 | Optimal investment is weakly increasing in `Q` | `iv_static_mono` |
| p. 283, (8.41)–(8.42) | The boundaries `Kᵇ(z)`, `Kˢ(z)`; `Kᵇ(z)` increases with `z` (concave `V`, `V₁` increasing in `z′`, monotone `P`) | `iv_q_monotone`, `iv_boundary_mono` |
| pp. 283–284 | Buy, sell and inaction regions; Figure 8.8 | `iv_buy_region`, `iv_sell_region`, `iv_inaction_region`, `iv_boundaries_ordered` |
| p. 284 | `p_s = 0`: (8.42) cannot hold; investment fully irreversible | `iv_irreversible_no_sell_boundary`, `iv_irreversible` |
| p. 284, Figure 8.7 | The reward to investing (no fixed cost) | Not formalised (figure; its content is Example 8.6.1) |
| p. 285, Example 8.6.1 | No fixed cost: `I*` and profits in the three regimes | `iv_psi861`, `example_8_6_1_buy`, `example_8_6_1_inaction`, `example_8_6_1_sell` |
| pp. 285–286, Example 8.6.1 | Fixed cost: the investment policy (corrected thresholds `p_b + √(2φ)`, `p_s − √(2φ)`) | `iv_gφ`, `example_8_6_1_fixed_buy`, `example_8_6_1_fixed_inaction`, `example_8_6_1_fixed_sell`, `example_8_6_1_misprint` |
| p. 286 | (8.38)–(8.40) still necessary with fixed costs, not sufficient | `iv_fixed_foc_necessary`, `iv_fixed_foc_not_sufficient` |
| p. 286, Figure 8.9, (8.43)–(8.45) | The investment rule with fixed costs, `Q₁`, `Q₂` | `eq_8_43`, `eq_8_44`, `eq_8_45`, `example_8_6_1_Q2` |
| p. 287, (8.46)–(8.47) | Boundaries as `Vⁱ = Vᵇ`, `Vⁱ = Vˢ`, equivalently `ϕ = 0` | `eq_8_46_8_47` |
| p. 287 | "The firm will buy if `K < Kᵇ(z)`, sell if `K > Kˢ(z)`" and the boundaries increase in `z`, with fixed costs | Not formalised (stated as intuitive, not derived, in the book) |
| p. 287 | Fixed costs widen the inaction region | `iv_fixed_widens` |
| p. 287 | Lumpiness: investment jumps at `Q₂` | `eq_8_43`, `eq_8_44` (at `Q > Q₂` the optimal `I*` solves (8.43), bounded away from 0 since `g(I*) > φ`) |

### Exercises 8.12–8.14 (`IVExercises`, `IVUzawa`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 289, Ex 12 | The Bellman equation; scaling and linear homogeneity of its (unique) solution | `iv_bellRHS`, `iv_SolvesBellman`, `ex_8_12_scaling`, `ex_8_12_homog` |
| p. 289, Ex 12 | (8.30) and (8.31) from the Bellman equation; marginal `Q = βV′(K′)` | `ex_8_12_foc`, `ex_8_12_envelope` |
| p. 289, Ex 12 | Hayashi's result from the Bellman equation | `ex_8_12_hayashi` |
| p. 290, Ex 13 | `Ψ = I²/(2K)`: homogeneity, partial derivatives, concavity of the reward | `iv_psi13`, `iv_psi13_hom`, `iv_psi13_partials`, `iv_concave13` |
| p. 290, Ex 13 | The investment rate `i = r + δ − √D` and the stationary Q equation | `iv_i13`, `ex_8_13_quadratic` |
| p. 290, Ex 13 | The candidate satisfies (8.29)–(8.32) | `ex_8_13_foc`, `ex_8_13_tvc` |
| p. 290, Ex 13 | Value of the firm `(1 + r)(1 + i)K₀` and optimality of the policy | `ex_8_13_value`, `ex_8_13` |
| p. 290, Ex 13 | Conditions for a finite value: `D > 0`; infinite value if `D < 0` | `ex_8_13`, `ex_8_13_unbounded` |
| p. 290, Ex 14 | First-order conditions of Uzawa's model are sufficient (with transversality) | `ex_8_14_sufficient`, `ex_8_14_optimal` |
| p. 290, Ex 14 | The optimal investment policy `Φ₁(I, K) = 1/Q`, increasing in `Q` | `ex_8_14_invest_mono` |
| p. 290, Ex 14 | Q theory: forward iteration and present value of `Q` | `ex_8_14_Q_iterate`, `ex_8_14_Q_pv` |
| p. 290, Ex 14 | Hayashi's result in Uzawa's framework | `ex_8_14_hayashi_step`, `ex_8_14_hayashi` |
| p. 280 / Ex 14 | Equivalence with the (8.29) formulation, `Ψ(X, K) = G(X, K) − X`, and `Q`'s agree | `ex_8_14_equiv`, `ex_8_14_Q_same` |
