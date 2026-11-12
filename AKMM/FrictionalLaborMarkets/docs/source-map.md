# Source map: AKMM Chapter 20

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 20, Frictional labor markets (T. Mukoyama and A. Şahin), pp. 593–625, and
Appendix 20.A, pp. 879–887. Page references are the draft's running heads. Lean names are relative
to `AKMM.FrictionalLaborMarkets`; names prefixed `Miao.` or `SargentStachurski.` are imported from
the dependencies. Departures from the book are in [corrections](corrections.md).

## §20.1–20.2 Introduction and labor market facts

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 593–594 | Theories of unemployment, search frictions | not formalised: narrative |
| pp. 594–595, Figs. 20.1–20.2 | U.S. unemployment and vacancy rates (CPS, JOLTS) | not formalised: data, figure claim |

## §20.3 A simple model of unemployment (`Lake`)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.1), p. 595 | `u_{t+1} = (1 − λ)u_t + σ(1 − u_t)` | `lakeNext`, `eq_20_1` |
| (20.2), p. 596 | Unique steady state `ū = σ/(λ + σ)`; decreasing in `λ`, increasing in `σ` | `eq_20_2`, `lake_ubar_anti_lam`, `lake_ubar_mono_sigma` |
| p. 596 | `u_{t+1} − u_t = (1 − λ − σ)(u_t − u_{t−1})`; `|1 − λ − σ| ∈ (0, 1)` (corrected to `[0, 1)`) | `lake_diff`, `lake_abs_lt_one`, `lake_abs_eq_zero_example` |
| p. 596 | Cauchy, converges to `ū`; `u_{t+1} − ū = (1 − λ − σ)(u_t − ū)` | `lake_gap`, `lake_closed_form`, `lake_tendsto`, `lake_cauchy`, `lake_isContraction`, `lake_globallyStable` (Sargent–Stachurski `IsContractionOn`, `GloballyStable`; Miao `jd_affine_sol`, `jd_affine_tendsto`) |
| p. 596 | `λ = 0.45`, `σ = 0.034`: `ū ≈ 7.0%`, `7.2%` after six months | not formalised: calibrated numbers |
| p. 596 | Expected duration `D = Σ(k + 1)λ(1 − λ)ᵏ = 1/λ` | `lake_duration_series` |
| p. 597 | Recursive `D = λ + (1 − λ)(1 + D)`, `D = 1/λ` | `lake_duration_recursion` |

## §20.4.1 The matching function (`Matching`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 597 | `M` increasing, CRS, `M ≤ u`, `M ≤ v` | `MatchFn`, `MatchFn.Bounded` (instance `skewMatch`, `skewMatch_bounded`); Miao's matching functions `MatchFn.ofMiao` |
| (20.3), p. 598 | `M(u, v)/u = λ_w(θ) = M(1, θ)`, `M(u, v)/v = λ_f(θ) = M(1/θ, 1)` | `lamW`, `lamF`, `eq_20_3`, `match_rate_worker`, `match_rate_firm` |
| p. 598 | `λ_w` increasing; `λ_w = θλ_f` | `match_lamW_strictMonoOn`, `match_lamF_strictAntiOn`, `match_lamW_eq`, `match_lamW_pos`, `match_lamF_pos`, `match_lamW_le_one`, `match_lamF_le_one` |
| (20.4), p. 598 | Law of motion | `eq_20_4` |
| (20.5)–(20.6), p. 598 | Steady state for constant `v`: `M(ū, v) + σū = σ` (printed `M(v, ū)`) | `eq_20_5`, `eq_20_6`, `eq_20_6_misprint` |
| pp. 598–599 | Unique `ū`; existence | `match_bc_strictMonoOn`, `match_ubar_unique`, `match_ubar_exists` |
| p. 599 | (20.6) negative relationship between `v` and `ū` (Beveridge curve) | `match_beveridge_anti` |
| p. 599, Figs. 20.3–20.4 | Beveridge curve in U.S. data | not formalised: data, figure claim |

## §20.4.2 Market equilibrium (`DMP`, `SteadyState`)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.7)–(20.12), pp. 599–600 | Bellman equations, free entry | hypotheses of `eq_20_16` (expectation `dmpEx`, `dmp_ex_add`, `dmp_ex_mul`, `dmp_ex_congr`) |
| (20.10), p. 600 | `κ/λ_f(θ) = βE[J(z′)]` | `eq_20_10` |
| (20.13)–(20.15), p. 601 | Generalised Nash bargaining ⇒ `(1 − γ)(W̃ − U) = γ(J̃ − V)` | `eq_20_15` (via Miao `jd_nash_iff`) |
| 20.A.1, p. 879 | First-order condition of the Nash product | `eq_20_A_1` |
| (20.16), p. 601 | Job-creation difference equation from the six equations | `dmp_J_div`, `eq_20_16` |
| 20.A.2, p. 879 | `w = b + γ(z − b) + βE[(1 − γ)λ_w(W′ − U′)] = b + γ(z − b) + γθκ` | `eq_20_A_2` |
| (20.17), p. 601 | Steady state; multiplied by `λ_f`, the right side is decreasing ⇒ uniqueness | `jcLHS`, `jcRHS`, `jcPhi`, `ss_phi_eq`, `eq_20_17`, `ss_phi_strictAntiOn`, `ss_unique` |
| p. 601 | Existence of `θ̄` (implicit) | `ss_exists`, `ss_exists_of_tendsto`, `ss_cd_lamF_limits`, `ss_cd_existsUnique` |
| p. 602, Fig. 20.5 | `z` falls ⇒ `θ̄` falls, `v` smaller, `u` larger | `ss_theta_mono_z`, `ss_ubar_strictAntiOn`, `ss_vbar_strictMonoOn` |
| p. 602, fn. 6 | `(1 − σ)η − γλ_w > 0` ⇒ right side of (20.16) increasing in `θ_{t+1}`, `θ_{t+1}` increasing in `θ_t` | `fn6_lhs_hasDerivAt`, `fn6_rhs_hasDerivAt`, `fn6_rhs_strictMonoOn`, `ss_lhs_strictMonoOn`, `fn6_next_strictMono` |
| p. 602, fn. 6 | "Satisfied when the period is short" | not formalised: informal |
| p. 602, fn. 7 | `dθ_{t+1}/dθ_t > 1` at `θ̄`; paths with `θ_0 ≠ θ̄` diverge | `fn7_slope`, `fn7_slope_eq`, `fn7_slope_gt_one`, `fn7_step_above`, `fn7_step_below`, `fn7_diverge_above`, `fn7_diverge_below` |
| p. 602, Fig. 20.6 | After a permanent fall in `z`, `θ` jumps at once, `u` then converges | `fn7_jump` (jump); convergence of `u` is (20.4) with constant `θ`: `lake_tendsto` |

## §20.4.3 Efficiency (`DMP`, `Efficiency`)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.18), p. 603 | `κ = λ_f(θ)(1 − γ)βS` | `dmpSurplus`, `eq_20_18` |
| (20.19), p. 604 | `S_t = E_t[z − b + βS_{t+1}(1 − σ − γλ_w)]` | `eq_20_19` |
| p. 604 | One-period planner `κ = M₂β(Ez − b)`; (20.20) | `eq_20_20` |
| (20.21), p. 604 | Elasticity `η(u, v)` | `matchElast`, `match_M2`, `match_elast_eq` |
| (20.22), p. 605 | Opportunity-cost condition | `eq_20_22` |
| p. 605 | Cobb–Douglas, `η = γ` satisfies both | `hosios_cd`, `hosios_cd_partials` |
| 20.A.3, p. 880 | Planner's problem, Lagrangian; FOC in `θ_t` (20.A.1) | `planner_foc_theta` |
| (20.A.2), p. 881 | FOC in `u_{t+1}` (leading `β` misprinted) | `planner_foc_u`, `eq_20_A_2_misprint` |
| (20.A.3), p. 881 | Substituting (20.A.1) | `eq_20_A_3` |
| (20.A.4)–(20.A.5), p. 881 | Coincidence iff `M₂ = (1 − γ)λ_f`, `M₁ = γλ_w`; Euler ⇒ `η = γ` suffices | `match_euler`, `hosios_node`, `hosios`, `hosios_necessary` |
| p. 881 | Non-CRS matching: Hosios not sufficient | `hosios_nonCRS`, `hosios_nonCRS_example` |
| p. 603, fn. 8 | Fukui–Mukoyama, on-the-job search | not formalised: citation |

## §20.5 Labor market facts, once again

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 605–607, Figs. 20.7–20.10 | Gross flows among E, U, N | not formalised: data, figure claims |

## §20.6 The unemployment volatility puzzle (`Matching`, `LogLinear`)

| Source | Claim | Lean |
| --- | --- | --- |
| (20.23), p. 608 | Cobb–Douglas; `λ_w = χθ^{1−η}`, `λ_f = χθ^{−η}`; elasticity of `λ_f` is `η` | `cdMatch`, `eq_20_23`, `cd_lamF_hasDerivAt`, `cd_not_bounded` |
| (20.24), p. 608 | AR(1) productivity | used as `E[ẑ_{t+1}] = ρẑ_t` in `ll_undetermined` |
| (20.25), p. 608 | Log-linearisation, `A`, `B` (sign of `B` misprinted) | `ll_rpow_exp`, `llL`, `llR`, `ll_lhs_eq`, `ll_rhs_eq`, `eq_20_25`, `eq_20_25_misprint` |
| p. 608 | Undetermined coefficients `C = ρ/(A − ρB)` | `ll_undetermined` |
| (20.26), p. 608 | Closed form | `llCoeff`, `eq_20_26`, `eq_20_26_printed_B` |
| p. 608 | Response larger for smaller `κ`, `γ`, `η`, `σ`, larger `χ`, `ρ`, `β` | `ll_gap_pos`, `ll_cs_kappa`, `ll_cs_gamma`, `ll_cs_eta` (needs `θ̄ ≥ 1`), `ll_rpow_mul_strictMono`, `ll_cs_eta_counterexample`, `ll_cs_chi`, `ll_cs_rho`, `ll_cs_beta`, `ll_cs_sigma` |
| 20.A.4, pp. 881–882 | Method of log-linearisation, capital-accumulation example | `eq_20_A_4_example` |
| §20.6.2, Table 20.1, pp. 609 | Calibration (Shimer, Hagedorn–Manovskii) | not formalised: calibrated numbers |
| §20.6.3, Tables 20.2–20.3, pp. 609–610 | U.S. statistics, simulated moments, volatility puzzle | not formalised: data and simulation |
| p. 611 | Rigid-wage job creation `κ/λ_f(θ_t) = βE[z − w̄ + (1 − σ)κ/λ_f(θ_{t+1})]` | `eq_20_48` (with `y = z`, `w̃ = w̄`) |
| (20.27), p. 611 | Log-linearised rigid-wage solution | `eq_20_27_deriv`, `eq_20_27` |
| p. 611 | Comparison of (20.26) and (20.27) | `ll_rigid_gt` |
| Table 20.4, p. 611 | Rigid-wage simulation | not formalised: simulation |

## §20.7 Endogenous separations (`EndogenousSeparation`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 612 | FOC for `σ`; (20.28) `−c′(σ) = κ/λ_f(θ)` | `eq_20_28` |
| (20.29), p. 612 | Job creation with endogenous separation | `es_J_div`, `eq_20_29` |
| p. 612 | `c(σ) = φσ^{−ξ}` | `es_foc_cd` |
| (20.30)–(20.32), pp. 612–613 | `σ̂ = −ηGẑ/(ξ + 1)`, `ĉ = ξηGẑ/(ξ + 1)` (exact) | `eq_20_31`, `eq_20_32` |
| p. 613, 20.A.5–20.A.6, pp. 882–883 | `G = Θ/Γ` | `es_ss_foc`, `es_bracket_cd`, `esR`, `eq_20_A_5_deriv`, `eq_20_A_5_misprint`, `eq_20_A_6`, `es_G` |
| p. 613 | `std(λ̂_w)/std(σ̂) = (1 − η)(1 + ξ)/η` | `es_lamW_loglinear`, `es_std_ratio` |
| p. 613 | `ξ = 1.6` from Krusell et al. (2017); Table 20.5 | not formalised: calibration and simulation |
| p. 614 | Rigid wages: `ĉ`, `σ̂` terms cancel exactly; result identical to (20.27) | `es_rigid_cancel`, `es_rigid_G`; with Nash bargaining they do not cancel: `es_nash_no_cancel` |
| Table 20.6, p. 614 | Simulation | not formalised: simulation |

## §20.8 Labor market frictions and the neoclassical growth model (`NGM`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 615 | Firm capital FOC, `r(X) = αz(K/(1 − u))^{α−1}` | `ngm_rental` |
| p. 616 | `y(X) = (1 − α)z(K/(1 − u))^α` | `ngm_y` |
| (20.33)–(20.35), p. 616 | Family problem | not formalised as a dynamic program; the FOCs are used in `eq_20_36`, `ngm_arrow_foc` |
| (20.36), p. 616; 20.A.6, pp. 883–884 | Arrow-security price | `eq_20_36`, `ngm_arrow_foc` |
| (20.37)–(20.40), pp. 616–617; 20.A.7, pp. 884–886 | Asset values of `J`, `V`, `W`, `U` | `ngm_asset_value` |
| (20.38), (20.41) | Free entry, Nash bargaining | hypotheses of `eq_20_42` (cf. `eq_20_10`, `eq_20_15`) |
| (20.42), p. 617 | `J/(1 − γ)` recursion | `eq_20_42` |
| (20.43), p. 617 | Job creation | `eq_20_43` |
| (20.44), p. 618 | Wage | `eq_20_44` |
| (20.45), p. 618 | Dividend | `ngmDividend`, `eq_20_45`, `ngm_resource` |
| p. 618 | Computation of the fixed point `(Q, Ω, w, d, θ)` | not formalised: algorithm; existence not claimed by the book |
| Tables 20.7–20.10, pp. 618–620 | Simulated statistics | not formalised: simulation |
| p. 619 | `w̃ = max{w̄, y}` "to maintain a positive profit" (should be `min`) | `ngm_rigid_max_profit`, `ngm_rigid_min_profit` |
| (20.46)–(20.47), p. 619 | Rigid-wage family problem and job value | (20.46) as for (20.33); (20.47) is a hypothesis of `eq_20_48` |
| (20.48), p. 619 | Rigid-wage job creation | `eq_20_48` |
| (20.49), p. 620 | Dividend with `w̃` | `ngmDividend` |
| 20.A.8, p. 887 | `ū = σ/(χ + σ)`, `r̄`, `K̄` (exponent misprinted), `ȳ`, `b = 0.4ȳ`, `κ` (misprinted), `w̄`, `d̄` | `ngm_calib_u`, `ngm_calib_r`, `ngm_calib_K`, `ngm_calib_K_misprint`, `ngm_y`, `ngm_calib_kappa`, `ngm_calib_kappa_misprint`, `ngm_calib_w`; `b = 0.4ȳ`, `α = 0.4`, `δ = 0.004`: not formalised (calibrated numbers) |

## §20.9 Heterogeneity of jobs and frictional wage dispersion (`McCall`, `MeanPreserving`, `Diamond`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 621 | Diamond paradox: all firms offer the reservation wage; it is a NE, and the unique one | `DiamondWorker`, `diamondAccept`, `diamondProfit`, `DiamondNE`, `diamond_profit_acc`, `diamond_profit_rej`, `diamond_ne`, `diamond_unique`, `diamond_paradox`, `diamond_paradox_example` |
| (20.50)–(20.52), p. 621 | Bellman equations (Miao's Exercise 8.2) | `Miao.Applications.od_FiringBellman`; `mc_exists_unique` |
| (20.51), p. 621 | `(1 − β)U = b + β∫max{W − U, 0}dF` | `eq_20_51` |
| (20.53), p. 622 | `W(w) = (w + βσU)/(1 − β(1 − σ))` | `eq_20_53`, `mc_D_pos` |
| p. 622 | `W` increasing, `W(0) < U`; reservation wage | `mc_W_strictMono`, `mc_U_pos`, `mc_W0_lt`, `mc_reservation` |
| p. 622 | `w_u` large so that `W(w_u) > U` | assumption; with it `mc_reservation` gives the threshold |
| (20.54)–(20.55), p. 622 | Reservation-wage equation | `eq_20_55`, `mc_root_unique`, `mcI`, `mcG`, `mc_G_eq` |
| p. 622 | `λ = 1 − F(w*)` decreasing in `w*` | `mc_lambda_antitone` |
| p. 622 | `∂G/∂β < 0`, `∂G/∂σ > 0`, `∂G/∂b < 0`, Leibniz, `∂G/∂w* > 0` | `mc_G_partials`, `mc_pointwise`, `mc_I_hasDerivAt`, `mc_G_w` |
| p. 622 | `w*` increasing in `β`, `b`, decreasing in `σ` | `mc_cs_beta`, `mc_coef_strictMono`, `mc_cs_b`, `mc_cs_sigma` (Miao `ex_8_2_alpha`) |
| p. 623 | Shift of offers by `ε`: `d(w* + ε)/dε ∈ (0, 1)` | `mc_shift_eq`, `mc_shift_bounds`, `mc_shift_deriv` |
| p. 623 | Mean-preserving spread (definition) | `SargentStachurski.AdditionalApplications.IsMPS`; `mps_mean` |
| (20.56), p. 623 | MPS ⇔ `∫_0^x G ≥ ∫_0^x F` (MWG) | `mps_ibp`, `eq_20_56_of_mps` (⇒); `eq_20_56_not_sufficient` (⇐ needs equal means); the converse with equal means (Rothschild–Stiglitz): not formalised, cited |
| (20.57)–(20.58), p. 624 | Rewriting, integration by parts, left side increasing | `eq_20_57`, `mps_ibp`, `eq_20_58`, `eq_20_58_strictMono` |
| p. 624 | `w*` rises with dispersion | `mc_mps_reservation` (via Sargent–Stachurski `integral_max_le_of_isMPS`) |
| p. 624 | Mean accepted wage `w^M`, `ρ = b/w^M`, `Mm = w^M/w*` formula | `mm_formula`, `mm_formula_of_bellman` |
| p. 625 | Back-of-the-envelope `Mm = 1.031` | `mm_back_of_envelope` (the formula gives `> 1.04`) |
| p. 625 | Frictional wage dispersion puzzle, on-the-job search remark | not formalised: discussion |
