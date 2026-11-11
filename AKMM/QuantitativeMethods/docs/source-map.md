# Source map: AKMM Chapter 8

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 8, Empirical strategies and quantitative macroeconomics, pp. 217–238, and
Appendix 8.A, p. 842. Page references are the draft's running heads. Lean names are relative to
`AKMM.QuantitativeMethods`. Departures from the book are in [corrections](corrections.md).

Following the project's decision 7, the algebra of the chapter is formalised; data, estimates,
calibrated numbers, simulations and claims read off figures are listed as not formalised.

Reused from dependencies. Miao `PartialInformation` (`Miao.PartialInformation`): the
second-moment calculus of square-integrable random vectors (`kf_L2`, `kf_app`, `var_mom`,
`kf_mean`, `kf_mom_app_left`, `kf_mom_app_right`, `kf_mom_add_left`, `kf_mom_sub_left`,
`kf_mom_add_right`, `kf_mom_transpose`, `kf_L2_app`, `kf_L2_add`, `kf_L2_sub`), the Kalman system
and filter (`KFSystem`, `KFSystem.const`, `KFSystem.Om`, `KFSystem.Spred`, `KFSystem.xpred`,
`KFSystem.innov`, `KFSystem.kf_innov_L2`, `KFSystem.eq_10_8`, `kf_Om`), the Gaussian density and
log-likelihood (`kf_gaussDens`, `example_10_1_4`) and the stationary initialisation
(`kf_step1_cov`, `kf_step1_mean`, `ls_Stable`, `var_lyapSol`). Miao `RationalExpectations`
(`Miao.RationalExpectations`): `var_impulse_response`, `var_ma_shift`. Miao
`StructuralEstimation` (`Miao.StructuralEstimation`): `ml_profileLikelihood`,
`ml_invariance_profile`. Miao `NeoclassicalGrowth` (`Miao.NeoclassicalGrowth`): `rb_u39_frisch`.
Mathlib: the LDL decomposition (`LDL.lower`, `LDL.diag`, `LDL.lower_conj_diag`), block-triangular
inverses, the orthogonal group, the inverse function theorem
(`HasStrictDerivAt.to_localInverse`), conditional expectation, independence. Not used: Miao
`DifferenceEquations` (the companion-form and VAR impulse-response results needed here come from
`RationalExpectations`).

## §8.1 Introduction (pp. 217–218)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 217–218 | The four strategies; causal effects from equilibrium data | not formalised: narrative |

## §8.2 The identification challenge (pp. 218–220) — `StaticModel`, `Identification`

| Source | Claim | Lean |
| --- | --- | --- |
| (8.1), p. 218 | `U = log c − ℓ^{1+ψ}/(1+ψ) + γη log G` | `sm_utility` |
| p. 218 | The planner's problem `max U` s.t. `c + G = Aℓ` | `sm_planner_optimal`, `sm_planner_unique`, `sm_star_feasible`, `sm_lstar`, `sm_cstar`, `sm_Gstar`, `sm_rpow_tangent` |
| p. 218 | First-order conditions `A/c = ℓ^ψ`, `G = γηc` | `sm_foc_iff`, `sm_lstar_rpow`, `sm_lstar_rpow_psi`, `sm_lstar_pos`, `sm_eq_rpow_inv_iff` |
| (8.2)–(8.3), pp. 218–219 | Eliminating `c = y − G`, `ℓ = y/A` gives the supply curve and the fiscal rule | `eq_8_2_8_3` |
| p. 219, Fig. 8.1 | The two conditions define the equilibrium in `(G, y)` | `sm_equilibrium_unique`, `sm_ystar`, `sm_ystar_eq` |
| p. 219 | (8.2) depends on `G/y` through wealth effects; more `G` raises labour | `sm_supply_slope` (positive slope); explanation not formalised: narrative |
| p. 219 | `G` increases if `y` or `η` increase | `sm_fiscal_rule_monotone` |
| p. 219 | The multiplier is the slope of the supply curve | `sm_supply_slope`, `sm_supply_poly_iff` |
| p. 219 | The multiplier as `(dy/dη)/(dG/dη)` | `sm_multiplier_eta` |
| p. 219 | The empirical relation of `y` and `G` reveals neither slope | `id_ols_slope` (log-linear system of §8.4) |
| Box, p. 220 | Peak multiplier (Blanchard–Perotti) and cumulative multiplier (Mountford–Uhlig) | `vl_peakMult`, `vl_cumMult`, `vl_peak_multiplier_prop`, `vl_cum_multiplier_prop` |
| Box fn. a, p. 220 | State dependence, first-order approximations | not formalised: narrative |

## §8.3 Natural experiments (pp. 220–222) — `Identification`, `VARLP`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 220 | A variable `z` correlated with `G` but not with `A` identifies the effect | `id_iv` |
| p. 220, Fig. 8.2 | Ramey's news series, multipliers near 1 and 0.7 | not formalised: data and estimates |
| Box, p. 221 | Local projection: regress `y_{t+h}` on `z_t` for each `h` | `vl_lp_exogenous` (and `vl_lp_estimand`) |
| p. 221, fn. 1 | Narrative approach, Romer–Romer | not formalised: narrative |
| pp. 221–222 | Nakamura–Steinsson regional multiplier 1.5; regional vs national multipliers | not formalised: estimates and narrative |

## §8.4 Structural VARs (pp. 222–225) — `SVAR`, `Cholesky`, `Identification`, `StaticModel`

| Source | Claim | Lean |
| --- | --- | --- |
| (8.4), p. 222 | `B₀Yₜ = B₁Yₜ₋₁ + ⋯ + B_JYₜ₋J + εₜ` | `eq_8_7`, `eq_8_7_process` (the structural side) |
| p. 222 | `Var(εₜ) = I` without loss of generality by rescaling the `B_j` | `sv_normalisation` |
| fn. 2, p. 222 | Meaning of "structural" | not formalised: narrative |
| (8.5)–(8.6), pp. 222–223 | The log-linearised system with `χ = (1/(1+ψ))(Ḡ/ȳ)/(1 − Ḡ/ȳ)` | `eq_8_5`, `eq_8_5_log`, `eq_8_6`, `sm_chi` |
| p. 223 | `G` is correlated with `A` (endogeneity) | `id_solution`, `id_impact`, `id_G_correlated_with_A`, `id_mom_obs` |
| fn. 3, p. 223 | Logs to levels: multiply by `ȳ/Ḡ` | `fn_3`, `eq_8_5` |
| (8.7), p. 223 | The reduced form `A_j = B₀⁻¹B_j`, `uₜ = B₀⁻¹εₜ` | `eq_8_7`, `eq_8_7_process` |
| p. 223 | `Var(uₜ) = B₀⁻¹B₀⁻¹'` | `sv_var_u` |
| p. 223 | Rotations `bF'` with `F'F = I` give the same `Var(u)` | `sv_rotation`, `sv_rotation_shocks`, `sv_rotation_converse`, `sv_not_identified` |
| p. 223, fn. 4 | `n(n+1)/2` distinct values; `n² − n(n+1)/2` restrictions | `sv_symm`, `sv_upper`, `sv_card_upper`, `sv_upperMap`, `sv_upperMap_bijective`, `sv_finrank_symm`, `sv_restriction_count` |
| p. 223 | `n = 2` needs one restriction; the coefficient `1` on `ŷ` identifies | `sv_restriction_count`, `id_restriction_identifies` |
| (8.8)–(8.9), pp. 223–224 | With `ĝ = Ĝ − ŷ`: `ŷ = χĝ + Â`, `ĝ = η̂/(1+γ)` | `eq_8_8_8_9` |
| p. 224 | `ĝ` is exogenous, so no endogeneity in (8.8) | `id_g_exogenous` |
| Box, p. 224 | Recursive identification; Cholesky `LL' = M` | `ch_exists`, `ch_unique`, `ch_lower_apply`, `ch_lower_mul_diag` |
| Box, p. 224 | With variables ordered recursively, the Cholesky factor of `Var(u)` is `B₀⁻¹` | `ch_recursive_identification` (with the sign normalisation), `ch_sign_counterexample`, `ch_fiscal_example` |
| p. 224 | Timing restrictions restrict only impact effects; Blanchard–Perotti | not formalised: narrative and estimates (zero restrictions are the recursive case above) |
| fn. 5, p. 224 | Blanchard–Perotti's multiplier definition | `vl_peakMult` |
| pp. 224–225 | External instruments, sign restrictions (Uhlig), long-run restrictions (Blanchard–Quah) | not formalised: narrative |
| Box, p. 225 | `z` ordered first in a recursive VAR | not formalised: narrative (covered by `ch_recursive_identification`, `vl_lp_exogenous`) |
| p. 225 | The invertibility assumption; overfitting | not formalised: narrative |

## §8.5 VARs and local projections (pp. 225–228) — `VARLP`, `Cholesky`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 226 | The local projection `y_{i,t+h} = β_{i,h}y_{1,t} + Σ A_{i,j}y_{t−j} + ε` | `vl_lp_estimand`, `vl_lp_exists`, `vl_col` |
| p. 226 | VAR(1) impulse responses `A₁ʰ`, identity on impact | `vl_var1_irf` |
| p. 226 | The companion form for `J = 2`, `𝒜 = [[A₁, A₂], [I, 0]]` | `vl_companion`, `vl_stack`, `vl_load`, `vl_companion_rec`, `vl_companion_two` |
| p. 226 | The upper-left block of `𝒜ʰ` gives the IRFs | `vl_companion_irf` |
| p. 226 | The LP estimand `E[y_{i,t+h} | y_{1,t} = 1, past] − E[⋯ | 0, past]` | `vl_lp_estimand` (linear projection), `vl_mom_resid` |
| p. 226 | The VAR estimand conditions on `y_t = e₁` | `vl_var_estimand`, `vl_var_exists` |
| p. 226 | The two estimate different things | `vl_lp_differs` |
| p. 226 | VAR(1): the representation of `y_{t+h}` and `y_t` | `vl_var1_estimands` |
| p. 227, fn. 6 | Plagborg-Møller–Wolf: LP = VAR IRFs weighted by `L_{·,1}/L₁₁` | `fn_6`, `ch_first_column` |
| p. 227 | LP flexible, VAR extrapolates; bias–variance trade-off | not formalised: narrative |
| p. 228, Fig. 8.3 | Monte Carlo; MSE 0.0047 vs 0.0027 | not formalised: simulation |
| p. 227 | Li–Plagborg-Møller–Wolf; Olea et al. coverage | not formalised: cited simulation findings |

## §8.6 A model of fiscal policy (pp. 228–231) — `FiscalModel`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 228–229 | Models as laboratories; omitted channels; fn. 7 | not formalised: narrative |
| (8.10), p. 229 | `yₜ = Aₜkₜᵅℓₜ^{1−α}` | `fm_IsEquilibrium` |
| (8.11), p. 229 | `yₜ = cₜ + kₜ₊₁ − (1−δ)kₜ + Gₜ` | `eq_8_11` |
| p. 229 | Household budget, `Tₜ = Gₜ` | `fm_budget_resource` (book's `K_t` read as `k_t`) |
| p. 230 | Lump-sum taxes do not distort | not formalised: narrative |
| (8.12)–(8.13), p. 230 | AR(1) processes with unit mean | `eq_8_12_mean` |
| (8.14), p. 230 | The Euler equation | `fm_IsEquilibrium` (stated, not re-derived; from Chapter 7) |
| (8.15), p. 230 | `w/c = ℓ^ψ` | `eq_8_15` |
| (8.16)–(8.17), p. 230 | `r = αy/k`, `w = (1−α)y/ℓ` | `eq_8_16_8_17` |
| (8.18), p. 230 | `γη/G = 1/c` | `eq_8_18` |
| p. 230 | The government's problem has the planner's first-order condition | not formalised: cited (Chapter 15); the planner's condition is `eq_8_18` |
| p. 230 | Equilibrium: processes satisfying (8.10)–(8.18) | `fm_IsEquilibrium`, `fm_steady_isEquilibrium` |
| p. 231, fn. 8 | Linear approximation around the steady state | steady state: `appendix_8A_1`; linearisation not formalised (numerical) |
| §8.6.2, p. 231 | With investment fixed, the multiplier is between zero and one | `fm_fixed_investment_multiplier`; static model: `sm_multiplier_mem_Ioo`, `sm_multiplier_formula` |
| §8.6.2, p. 231 | Investing less; the multiplier increases with persistence | figure claim, deferred (Fig. 8.4, right) |

## §8.7 Structural estimation (pp. 231–234) — `StaticLikelihood`, `KalmanLikelihood`

| Source | Claim | Lean |
| --- | --- | --- |
| (8.19)–(8.20), p. 232 | `A = y(1 − G/y)^{1/(1+ψ)}`, `η = (G/y)/(γ(1 − G/y))` | `eq_8_19_8_20`, `sl_bijection` |
| p. 232 | `Prob(G, y | ψ, γ) = p_A(A)p_η(η)` | `sl_likelihood_discrete` (discrete shocks); for densities corrected: `sl_jacobian`, `sl_jacobian_depends_on_psi` |
| p. 232 | The sample likelihood is the product | `sl_loglik` |
| p. 232 | ML and Bayesian estimation | not formalised: narrative (general ML in Miao `StructuralEstimation`) |
| p. 232 | Differentiate (8.2) at the estimates to get the multiplier | `sl_multiplier_mle`, `appendix_8A_2_steady` |
| p. 232 | (8.3) makes `G/y` independent of `A`, so `G/y` reveals fiscal shocks | `sm_ystar_eq`, `id_g_exogenous` |
| p. 232 | Mis-specification of the fiscal rule; unobserved states and filtering | not formalised: narrative |
| (8.21)–(8.22), p. 233 | `X̂ₜ₊₁ = AX̂ₜ + Bεₜ₊₁`, `Ŷₜ = CX̂ₜ` | `kl_system`, `kl_model` |
| p. 233 | `Yₜ` given the past has mean `CX_{t|t−1}`, covariance `CP_{t|t−1}C'` | `kl_innovations`, `kl_Om` (second-moment version) |
| p. 233 | `X_t ∼ N(X_{t|t−1}, P_{t|t−1})` | not formalised: Gaussian reading |
| p. 233 | `Prob({Yₜ}) = ∏ N(Yₜ | CX_{t|t−1}, CP_{t|t−1}C')` | `kl_chain_rule`, `kl_likelihood`, `kl_normal` |
| fn. 9, p. 233 | Initial state from the invariant distribution | `fn_9` |
| pp. 233–234 | Non-linear and non-Gaussian methods | not formalised: narrative |
| Box, pp. 233–234 | Limited-information estimation, GMM, impulse-response matching | not formalised: narrative |

## §8.8 Calibration (pp. 234–238) — `FiscalModel`, `StaticModel`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 234 | Calibration as a strategy | not formalised: narrative |
| p. 234 | The multiplier is larger if labour supply is more elastic | `sm_multiplier_antitone_psi` (static model) |
| p. 234 | `α ≈ 1/3`, `I/K = 0.076`, `δ = 0.019`; fn. 10 | not formalised: data and calibrated numbers |
| p. 235 | `β = (1 + αȳ/k̄ − δ)⁻¹` | `fm_beta_calibration` |
| p. 235, fn. 11 | `k/y = 3.3 × 4` gives `β = 0.994` | not formalised: calibrated number (the formula gives 0.99379) |
| p. 235 | The Frisch elasticity is exactly `1/ψ` | `fm_frisch` |
| p. 235, fn. 12 | Tax-based elasticities about 1/2 (Chetty) | not formalised: data |
| p. 235 | `dℓ/dc = −(1/ψ)ℓ/c` | `fm_dl_dc` |
| p. 235 | Change in annual earnings `−$2.30 = −(4/ψ)(wℓ/c)(r/(1+r))$100` | `fm_lottery` |
| p. 235 | `r = 1%`, `wℓ/c = 1.2` give `ψ = 2.1` | not formalised: calibrated number (the formula gives 2.07) |
| p. 236 | In steady state (8.18) is `γ = Ḡ/c̄`; `γ = 0.3` | `fm_gamma_calibration`; the value is data |
| p. 236 | Linearisation removes precautionary motives; TFP shocks irrelevant | not formalised: narrative |
| p. 236 | The linear solution scales with the shock, so its size does not matter | `fm_multiplier_scale` |
| p. 236, Fig. 8.4 | Impulse responses; cumulative multiplier near zero; multiplier rising in `ρ_η` and as `ψ` falls | figure claims, deferred |
| Box, p. 237 | Model validation | not formalised: narrative |
| pp. 237–238, fn. 14 | Wealth effects cannot explain large multipliers; Keynesian channels; principles of calibration | not formalised: narrative |

## §8.9 Taking stock (p. 238)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 238 | Choice among the methods | not formalised: narrative |

## Appendix 8.A.1 Steady state of the model (p. 842) — `FiscalModel`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 842 | `Ā = η̄ = 1` | `eq_8_12_mean` |
| p. 842 | `r̄ = 1/β − 1 + δ`, `ȳ/k̄ = r̄/α`, `k̄/ℓ̄ = (ȳ/k̄)^{1/(α−1)}`, `ȳ/ℓ̄ = (r̄/α)^{α/(α−1)}` | `appendix_8A_1`, `appendix_8A_1_ratios`, `fm_r`, `fm_kl`, `fm_r_pos`, `fm_kl_props`, `fm_cd_ratio` |
| p. 842 | `w̄ = (1−α)ȳ/ℓ̄`, `c̄ = w̄ℓ̄^{−ψ}` | `appendix_8A_1` |
| p. 842 | `Ḡ = (η̄c̄γ)^{−γ₁}` (misprint) | `appendix_8A_1` (`Ḡ = γc̄`), `appendix_8A_1_printed_G` |
| p. 842 | Resource constraint; one equation in `ℓ̄` | `appendix_8A_1`, `fm_l`, `fm_steady_exists`, `fm_IsSteady`, `fm_Params` |

## Appendix 8.A.2 The fiscal multiplier in the static model (p. 842) — `StaticModel`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 842 | At `η̄ = 1`, `Ḡ/ȳ = γ/(1+γ)` | `appendix_8A_2_steady` |
| p. 842 | The total derivative of (8.2) and its solution for `dy` | `appendix_8A_2_total_differential`, `sm_supply_dA`, `sm_supply_slope` |
| p. 842 | The multiplier `(1+χ)⁻¹χȳ/Ḡ` | `sm_multiplier_formula`, `appendix_8A_2_total_differential` |
| p. 842 | It is the coefficient on `Ĝ` in (8.5) scaled by `ȳ/Ḡ` | `fn_3`, `eq_8_5` |
