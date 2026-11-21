# Source map: Miao Chapter 10

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 10, Control
under Partial Information, pp. 327–346. Lean names are relative to `Miao.PartialInformation`. The
Kalman filter of §10.1.1 is the general time-varying system `KFSystem`, proved in its
linear-projection (second-moment) reading; the hidden Markov chain and control problems of
§10.1.2–10.2 are finite (`HMPOMDP`). Departures from the book are in [corrections](corrections.md).

## §10.1.1 (Kalman filter), §10.3 (LQ control) and Exercises 10.1–10.5

### §10.1.1 The state-space system and the Kalman filter

| Source | Claim | Lean |
| --- | --- | --- |
| (10.1)–(10.2), pp. 327–328 | `x_{t+1} = A_tx_t + B_tu_t + C_tε_{t+1}`, `y_t = G_tx_t + H_{t−1}u_{t−1} + D_tε_t`, `x₀ ∼ (x̄₀, Σ₀)` | `KFSystem`, `KFSystem.inp` (hypotheses `hx`, `hy` of `KFSystem.kf_moments`) |
| (10.3)–(10.4), p. 328 | The econometric form with exogenous `z_t` | `ex_10_5` (Exercise 10.5) |
| p. 328 | Notation `x̂_{t\|s}`, `Σ_{t\|t}`, `Σ_{t\|t−1}`, `Ω_{t\|t−1}` | `KFSystem.xpred`, `KFSystem.xfilt`, `KFSystem.Spred`, `KFSystem.Sfilt`, `KFSystem.Om`, `KFSystem.err`, `var_mom`, `kf_mean`, `kf_L2`, `kf_app` |
| pp. 328–329 | Conditional covariances equal unconditional ones; `x_t\|F_t ∼ N(x̂_{t\|t}, Σ_{t\|t})` etc. | Not formalised (Gaussian reading); the second moments: `KFSystem.kf_moments`, `KFSystem.kf_filt_moments`, `KFSystem.eq_10_8` |
| (10.7), p. 329 | `x̂_{t\|t} = x̂_{t\|t−1} + K_t(y_t − ŷ_{t\|t−1})`, innovation `a_t` | `KFSystem.xfilt`, `KFSystem.innov` |
| (10.8), p. 330 | `Ω_{t\|t−1} = Ea_ta_t' = GΣG' + DD' + GCD' + DC'G'` | `kf_Om`, `KFSystem.eq_10_8`, `KFSystem.kf_innov_eq` |
| (10.9), p. 330 | `E(x_t − x̂_{t\|t−1})ε_t' = C_t` (corrected: `C_{t−1}`, `0` at `t = 0`) | `KFSystem.eq_10_9`, `KFSystem.Cl`; counterexample `kf_cross_book_false` (with `kf_twoPoint`, `kf_twoPoint_prob`, `kf_twoPoint_integral`) |
| (10.10), p. 330 | The optimal gain `K_t = (ΣG' + CD')Ω⁻¹` minimises `E(x_t − x̂_{t\|t})'(x_t − x̂_{t\|t})` | `kf_gain`, `eq_10_10`, `KFSystem.eq_10_10_random`, `kf_trace_sandwich`, `kf_diag_sandwich` |
| p. 330 | Intuition for `K_t` | No formal content |
| p. 330 | `x̂_{t+1\|t} = A_tx̂_{t\|t}`(+`B_tu_t`), `ŷ_{t+1\|t} = G_{t+1}x̂_{t+1\|t} + H_tu_t` | `KFSystem.xpred_succ`, `KFSystem.innov` |
| p. 330 | `Σ_{t+1\|t} = A_tΣ_{t\|t}A_t' + C_tC_t'` | `KFSystem.Spred`, `KFSystem.kf_err_succ`, `KFSystem.kf_moments` |
| (10.11), p. 331 | `Σ_{t\|t}` for a general gain (the derivation via (10.7) and the cross terms) | `kf_joseph`, `kf_joseph_expand`, `KFSystem.eq_10_11`, `KFSystem.kf_step`, `KFSystem.kf_filt_err` |
| p. 331 | First-order condition `∂tr Σ_{t\|t}/∂K = 0` (corrected) | `kf_trace_perturb`, `eq_10_10_foc` |
| p. 332 | Substituting: `Σ_{t\|t} = (I − KG)Σ_{t\|t−1} − KDC'` | `kf_filtCov`, `eq_10_11_gain`, `kf_filtCov_eq`, `kf_joseph_complete`, `KFSystem.kf_filt_moments` |
| (10.12), p. 332 | Projection theorem: `x̂_{t\|t} = x̂_{t\|t−1} + Cov(x_t, y_t\|y^{t−1})Var(y_t\|y^{t−1})⁻¹a_t` | `KFSystem.eq_10_12`, `KFSystem.kf_err_orth`, `KFSystem.kf_filt_orth`, `KFSystem.kf_innov_orth`, `KFSystem.kf_shock_innov`, `KFSystem.kf_wsum`, `KFSystem.kf_wsum_moments`, `KFSystem.kf_innov_L2` |
| p. 332 | `Cov(x_t, y_t\|y^{t−1}) = ΣG' + CD'`, `Var(y_t\|y^{t−1}) = Ω` | `kf_Mx`, `KFSystem.eq_10_8` |
| Step 1, p. 332 | Initialisation `Σ_{0\|−1} = Σ₀`, `x̂_{0\|−1} = x̄₀` | `KFSystem.Spred`, `KFSystem.xpred` |
| Step 1, p. 332 | Stationary initialisation `x̂₀ = Ax̂₀`, `Σ₀ = AΣ₀A' + Q`, `vec Σ₀ = (I − A⊗A)⁻¹vec Q` | `kf_step1_mean`, `kf_step1_cov` |
| Step 2–3, pp. 332–333 | The recursions for `Ω`, `K`, `x̂_{t\|t}`, `Σ_{t\|t}`, `Σ_{t+1\|t}`, `x̂_{t+1\|t}` | `KFSystem.Om`, `KFSystem.K`, `KFSystem.xfilt`, `KFSystem.Sfilt`, `KFSystem.Spred`, `KFSystem.xpred` |
| p. 333 | Fully recursive form `x̂_{t+1\|t} = A_tx̂_{t\|t−1} + B_tu_t + A_tK_ta_t` | `KFSystem.kf_pred_recursive` |
| p. 333 | `a_t` independent `N(0, Ω_{t\|t−1})` (second-moment version: mean zero, covariance `Ω`, uncorrelated) | `KFSystem.kf_innov_L2`, `KFSystem.eq_10_8`, `KFSystem.kf_innov_orth` |
| p. 333 | Riccati equation for `Σ_{t+1\|t}` | `kf_riccati_pred`, `KFSystem.kf_riccati_Spred` |
| p. 333 | `x̂_{t+1\|t+1} = A_tx̂_{t\|t} + B_tu_t + K_{t+1}a_{t+1}` and the `Σ_{t+1\|t+1}` recursion | `KFSystem.kf_filt_recursive`, `KFSystem.kf_riccati_Sfilt` |
| pp. 333–334 | Time-homogeneous case; the stationary filter `Σ_t → Σ`, `K_t → K` | `KFSystem.const`, `kf_dual`, `kf_dual_T`, `kf_const_Spred`, `kf_steadyGain`, `kf_steady_state`, `kf_steady_fixed` |
| — | Control-freeness of the error (used on p. 344) | `KFSystem.kf_err_control_free`, `KFSystem.err_zero` |
| — | Second-moment calculus | `kf_L2_app`, `kf_L2_add`, `kf_L2_sub`, `kf_L2_const`, `kf_L2_zero`, `kf_mom_transpose`, `kf_mom_app_left`, `kf_mom_app_right`, `kf_mom_add_left`, `kf_mom_add_right`, `kf_mom_sub_left`, `kf_mom_sub_right`, `kf_mom_lin2`, `kf_mom_lin_sub`, `kf_mom_const_left`, `kf_mom_const_right`, `kf_mom_self_psd`, `kf_mean_app`, `kf_mean_add`, `kf_mean_sub`, `kf_mean_const`, `kf_app_add`, `kf_app_sub`, `kf_app_app`, `kf_app_sub_mat`, `kf_app_zero_mat`, `kf_Om_transpose`, `kf_Mx_transpose` |

### Examples 10.1.1–10.1.4

| Source | Claim | Lean |
| --- | --- | --- |
| Example 10.1.1, p. 329 | Labor income: the state-space form with `x_t = (α, β, z_t)'`, `G_t = [1 t 1]` (corrected shock date) | `example_10_1_1`, `kf_laborG`; misprint `example_10_1_1_misprint` |
| pp. 334–336 | The scalar filter (`a, c, d`): Riccati map, gain, innovation variance, convergence | `kf_scalarSys`, `kf_scalarRic`, `kf_scalarRoot`, `kf_scalar_filter`, `kf_scalar_dualT`, `kf_scalar_xpred`, `kf_scalar_tendsto`, `kf_scalarRic_nonneg`, `kf_scalar_CD`, `kf_scalar_DD`, `kf_inv_fin_one` |
| Example 10.1.2, p. 334 | Muth: `K_t = Σ/(Σ + R)`, `Σ_{t+1} = (Σ(R + Q) + QR)/(Σ + R)`, `Σ_t → Σ`, `K_t → K`, `x̂_{t+1\|t} = (1 − K)x̂_{t\|t−1} + Ky_t` | `example_10_1_2`, `example_10_1_2_adaptive` |
| Example 10.1.2, pp. 334–335 | `Q = 0`: `m_t`, `K_t = σ_t/(σ_t + R)`, `σ_t = σ_{t−1}R/(σ_{t−1} + R)`, innovation form, `K²(σ + R) = Kσ` | `example_10_1_2_constant`, `kf_scalar_xpred` |
| Example 10.1.3, pp. 335–336 | Productivity growth: the stationary filter, `K`, `Σ` (closed form), `Ea² = Σ + σ_v²`, `K²(Σ + σ_v²) = KΣ` | `example_10_1_3`, `example_10_1_3_filter` |
| Example 10.1.4, pp. 336–337 | The log-likelihood `−(n_yT/2)ln 2π − ½∑ln\|Ω_t\| − ½∑a_t'Ω_t⁻¹a_t` | `example_10_1_4`, `kf_gaussDens`, `kf_logDens` |

### §10.3 Linear-quadratic control under partial information

| Source | Claim | Lean |
| --- | --- | --- |
| p. 343 | The LQ problem with `y_t = Gx_t + v_t` observed | `LSProblem` (Chapter 9), `KFSystem` |
| p. 343, (10.17) | Full information: `V = −½x'Px + const`, `u = −Fx` | `LSProblem.eq_9_16_9_17` (Chapter 9) |
| pp. 343–344 | Partial information: same `P` (9.12), `u_t = −Fx̂_{t\|t}` with the same `F` (9.17) | `kf_certainty_equivalence`, `kf_filt_T`, `kf_filtProblem`, `kf_piObj` |
| p. 344 | `Δ_t = x_t − x̂_{t\|t} = Ax_{t−1} + η_t − Ax̂_{t−1\|t−1} − Ka_t`, independent of `u_t` | `KFSystem.kf_Delta_succ`, `KFSystem.kf_err_control_free` |
| p. 344 | `E_t[x'Qx + u'Ru + 2x'Su] = x̂'Qx̂ + u'Ru + 2x̂'Su + …` | `kf_expected_loss`, `kf_loss_expand` |
| p. 344 | `E_t x̂'_{t+1\|t+1}Px̂_{t+1\|t+1} = (Ax̂ + Bu)'P(Ax̂ + Bu) + …` | `kf_expected_cont`, `KFSystem.kf_filt_recursive` |
| pp. 344–345 | The Bellman equation in `x̂_{t\|t}` is the full-information problem | `kf_certainty_equivalence` |

### Exercises 10.1–10.5 (p. 345)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 10.1 | State-space form of `y_t = μ + ε_t + bε_{t−1}` | `ex_10_1` |
| Exercise 10.2 | Kalman filter with unknown `ρ`: not linear in `(ρ, z)`; the filter conditional on `ρ` | `ex_10_2_nonlinear`, `ex_10_2` |
| Exercise 10.3 | `x_t = θ`, `y_t = θ + v_t`: the filter in closed form and its long run | `ex_10_3`, `ex_10_3_mse` |
| Exercise 10.4 | The filter for `y_{t+1} = Gx_t + Hu_t + Dε_{t+1}`; the second form | `ex_10_4`, `ex_10_4_gain`, `ex_10_4_err`, `ex_10_4_equiv`, `kf_ex4Dual`, `kf_ex4Sig`, `kf_ex4Gain`, `kf_ex4Est`, `kf_ex4_TF`, `kf_mom_two` |
| Exercise 10.5 | The filter for (10.3)–(10.4) | `ex_10_5` |

## §10.1.2–§10.2 and Exercise 10.6

### The hidden-chain probability model (`HMFilter`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 338–339 | Joint probability of state and signal paths `μ₀(x₀)f(x₀,y₀)∏ P(xₛ,xₛ₊₁)f(xₛ₊₁,yₛ₊₁)` | `hm_weight`, `hm_weight_snoc`, `hm_weight_nonneg` |
| pp. 338–339 | `Pr(x_t = i, yᵗ)`, `Pr(yᵗ)`, `π_t(i | yᵗ)`, `Pr(x_{t+1} = i, yᵗ)`, `π_{t+1}(i | yᵗ)` | `hm_joint`, `hm_lik`, `hm_post`, `hm_predJoint`, `hm_pred`, `hm_lik_eq`, `hm_joint_zero`, `hm_joint_nonneg` |
| p. 339 | Prediction `Pr(x_{t+1} = i, yᵗ) = Σⱼ pⱼᵢ Pr(x_t = j, yᵗ)` | `hm_predJoint_eq`, `hm_predJoint_sum` |
| p. 338 | Bayes numerator `Pr(x_{t+1} = i, yᵗ⁺¹) = f(i, y) Pr(x_{t+1} = i, yᵗ)` | `hm_joint_snoc`, `hm_joint_forward` |
| p. 339 | `π_{t+1}(eᵢ | yᵗ) = Σⱼ pⱼᵢ π_t(eⱼ | yᵗ)` | `hm_pred_eq` |
| p. 340 | `π_{t+1}(eᵢ | yᵗ⁺¹) = f(eᵢ,y)π_{t+1}(eᵢ | yᵗ)/Σⱼ f(eⱼ,y)π_{t+1}(eⱼ | yᵗ)` | `hm_post_update` |
| §10.1.2 ("the likelihood") | `Pr(yᵗ⁺¹) = Pr(yᵗ) Σⱼ f(eⱼ,y)π_{t+1}(eⱼ | yᵗ)` | `hm_lik_snoc` |
| pp. 337–338 | The model is a probability: `Pr(yᵗ)` sums to one; the filter is a probability vector | `hm_lik_sum`, `hm_post_sum`, `hm_post_nonneg`, `hm_sum_snoc`, `hm_sum_fin_one` |
| p. 337 | The states are a Markov chain with `pᵢⱼ = Pr(x_{t+1} = eⱼ | x_t = eᵢ)` | `hm_stateLaw`, `hm_pairLaw`, `hm_margLaw`, `hm_markov` |

### §10.1.2 Hidden Markov chain (`HMChain`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 337 | Unit-vector states; `E[x_{t+1} | x_t] = P′x_t` (10.13) | `hm_e`, `hm_condE`, `hm_transpose_mulVec_e`, `hm_condE_id`, `eq_10_13` |
| (10.13), p. 337 | `v_{t+1}` is a martingale difference | `hm_condE_mds`, `eq_10_13_mds` |
| p. 337 | `x x′ = diag(x)`; expansion of `x_{t+1}x′_{t+1}` and of `v_{t+1}v′_{t+1}` | `hm_unit_outer`, `hm_vv_expansion` |
| p. 338 | `E[v_{t+1}v′_{t+1} | x_t] = diag(P′x_t) − P′diag(x_t)P` | `hm_condE_cov`, `eq_10_13_cov` |
| (10.14), p. 338 | `E[y_t | x_t] = Q′x_t`, `E[w_t | x_t] = 0` | `eq_10_14`, `eq_10_14_mds` |
| p. 338 | `E[w_t w′_t | x_t] = diag(Q′x_t) − Q′diag(x_t)Q` (book: `u_t`) | `eq_10_14_cov` |
| p. 338 | Bayes' rule, first line: `Pr(x_t = eᵢ, y_t | yᵗ⁻¹) = Σₛ qᵢⱼpₛᵢπ_{t−1}(eₛ)` | `hm_bayes_joint` |
| p. 338 | `π_t(eᵢ | yᵗ⁻¹, y_t = ξⱼ) = Σₛ qᵢⱼpₛᵢπ_{t−1}(eₛ)/ΣᵢΣₛ qᵢⱼpₛᵢπ_{t−1}(eₛ)` | `hm_bayes` |
| p. 339 | `π₀(eᵢ | y₀ = ξⱼ) = qᵢⱼπᵢ^{ss}/Σᵢ qᵢⱼπᵢ^{ss}` | `hm_bayes_initial` |
| p. 339 | With the stationary prior every `x_t` has law `π^{ss}` | `hm_margLaw_succ`, `hm_stationary_marg` |

### §10.1.3 Hidden Markov-switching model (`HMSwitching`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 339 | Prediction `π_t(eᵢ | yᵗ⁻¹) = Σⱼ pⱼᵢπ_{t−1}(eⱼ | yᵗ⁻¹)` | `hm_hamilton_predict` |
| p. 340 | Updating `π_t(eᵢ | yᵗ) = f(eᵢ,y_t)π_t(eᵢ | yᵗ⁻¹)/Σⱼ f(eⱼ,y_t)π_t(eⱼ | yᵗ⁻¹)` | `hm_hamilton_update` |
| p. 339 | `Δln C_t = κ(x_t) + ε_t`, `ε ~ N(0,σ²)`: `f(x,·)` is the law/density of `κ(x) + ε` | `hm_switch_law`, `hm_switchDensity`, `hm_switch_density` |
| p. 340 | The predictive density of `y_t` integrates to one | `hm_switch_predictive` |
| p. 340 | Two-regime update in log-odds form | `hm_switch_logodds` |
| p. 340 | Stationary prior of a two-state chain | `hm_two_state_stationary` |

### §10.2 Control problems (`HMControl`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 340 | Assumptions (i)–(iii), rewards, terminal reward | `HMPOMDP` |
| p. 340 | `Pr(x_{t+1}, y_{t+1} | x_t, yᵗ, uᵗ) = Pr(y_{t+1} | x_{t+1}, u_t)Pr(x_{t+1} | x_t, u_t)` | `hm_at`, `hm_at_sum` |
| p. 340 | Expected total reward `E[Σ βᵗr(x_t,u_t,t) + βᵀR(x_T)]` of a history-dependent policy | `hm_pre`, `hm_cw`, `hm_rew`, `hm_J`, `hm_J_zero`, `hm_cw_mass`, `hm_cw_cons_sum`, `hm_cw_decomp`, `hm_rew_cons`, `hm_shift`, `hm_sum_cons`, `hm_pre_cons_succ`, `hm_pre_zero` |
| p. 340 | Conditioning on the first period | `hm_J_succ` |
| p. 341 | Posterior recursion `P_{t+1}(x_{t+1}) = Σ P_t(x_t)Pr(x_{t+1},y_{t+1} | x_t,u_t)/ΣΣ` | `hm_nextM`, `hm_py`, `hm_bayesNext`, `hm_posterior_one_step` |
| p. 341 | Bellman equation in beliefs, `V(P, T) = Σ P(x)R(x)` | `hm_V`, `hm_obj`, `hm_V_succ`, `hm_bookV`, `hm_bellman`, `hm_bellman_terminal` |
| p. 341 | The belief is a sufficient statistic: `V(P,t)` is the optimum over all policies and the belief policy attains it | `hm_J_le_V`, `hm_J_beliefPol`, `hm_value_isGreatest`, `hm_greedy`, `hm_greedy_spec`, `hm_beliefPol`, `hm_shift_beliefPol`, `hm_V_smul`, `hm_py_mul_V`, `hm_sup'_mul`, `hm_nextM_nonneg`, `hm_nextM_smul`, `hm_bayesNext_smul` |
| p. 341 | For the linear Gaussian model the posterior is Gaussian | `hm_gauss_bayes` (scalar) |

### Example 10.2.1 and Exercise 10.6 (`HMKalman`, `HMGuvenen`)

| Source | Claim | Lean |
| --- | --- | --- |
| Example 10.2.1, p. 342 | Bellman equation in `(s_t, y_t, x̂_{t|t−1})` with (10.15), `V_{T+1} = 0` | `hm_gV`, `hm_bookGV`, `example_10_2_1`, `example_10_2_1_terminal` |
| (10.16), p. 342 | `x̂_{t+1|t} = Ax̂_{t|t−1} + AK_t(y_t − G_tx̂_{t|t−1})` | `eq_10_16` |
| Example 10.2.1, p. 342 | `y_{t+1} | yᵗ ~ N(x̂_{t+1|t}, Ω_{t+1|t})` | `ex_10_6_a_predictive`, `hm_gauss_predict`, `hm_gauss_marginal` |
| Ex. 10.6(a) | State space of Example 10.1.1 with `α = β = 0`: `CC′`, `DD′`, `CD′` | `ex_10_6_a_shocks` |
| Ex. 10.6(a) | Kalman filter: (10.8), (10.10), (10.11) and the optimal gain, scalar | `hm_kOmega`, `hm_kGain`, `hm_kMSE`, `hm_mse_eq`, `hm_mse_min`, `hm_mse_le` |
| Ex. 10.6(a) | `Ω_t = Σ_t + σ_v²`, `K_t = Σ_t/(Σ_t + σ_v²)`, `Σ_{t|t} = Σ_tσ_v²/(Σ_t + σ_v²)` | `ex_10_6_a_gain` |
| Ex. 10.6(a) | Riccati equation for `Σ_{t+1|t}` | `hm_kSig`, `hm_kK`, `hm_kOm`, `hm_kSig_nonneg`, `ex_10_6_a_riccati` |
| Ex. 10.6(a) | `x̂_{t+1|t} = ρx̂_{t|t−1} + ρK_t(y_t − x̂_{t|t−1})` | `ex_10_6_a_recursion` |
| Ex. 10.6(a) | Gaussian reading: posterior `N(x̂ + K(y − x̂), Σσ_v²/(Σ + σ_v²))` | `hm_gauss_bayes`, `hm_gauss_marginal` |
| Ex. 10.6(b) | `T = 1`, CARA, `s_{t+1} ≥ 0`: `V₁ = u(W)`, `V₀` and the saving rule `max(0, ·)` | `hm_cara`, `ex_10_6_b_terminal`, `ex_10_6_b`, `hm_terminal`, `hm_f`, `hm_f_tangent`, `hm_exp_tangent`, `hm_f_min_nonneg` |
| Ex. 10.6(c) | Any `T` (terminal constraint only): exponential value, weights `a_k`, factors `φ_k`, saving rule | `ex_10_6_c`, `ex_10_6_c_policy`, `hm_step`, `hm_closed`, `hm_a`, `hm_a_pos`, `hm_a_inv`, `hm_phi`, `hm_phi_succ`, `hm_N`, `hm_N_props`, `hm_phi_props`, `hm_int_closed`, `hm_obj_eq`, `hm_f_min` |
| Ex. 10.6(d) | Bellman equation with `x̂_{t|t}` as state, same value | `hm_gVf`, `ex_10_6_d` |
