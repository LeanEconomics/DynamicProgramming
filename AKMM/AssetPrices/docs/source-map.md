# Source map: AKMM Chapter 16

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 16, Asset prices (Monika Piazzesi and Martin Schneider), pp. 467–492; the
chapter has no appendix. Page references are the draft's running heads. Lean names are relative to
`AKMM.AssetPrices`. Departures from the book are in [corrections](corrections.md).

Reused from dependencies. Miao `CompleteMarkets` (`Miao.CompleteMarkets`): Stiemke's lemma
`rd_stiemke` (the fundamental theorems); the finite expectations `bp_E`, `bp_Cov`, `bp_Var` and
their lemmas (`bp_E_add`, `bp_E_const`, `bp_Cov_eq_dev`, `bp_Cov_comm`), `eq_13_30` (the SDF
pricing identities); `bp_integral_exp_gaussian`, `bp_euler_gaussian` (the lognormal model); cited
for the infinite-horizon versions: `theorem_13_3_1` (First Welfare Theorem on the event tree),
`theorem_13_5_1_if` (equivalence of equilibria with debt constraints), `rd_ponzi_arb` (Ponzi
schemes are arbitrages). Miao `RecursiveUtility` (`Miao.RecursiveUtility`): `eq_20_33` (the
Epstein–Zin riskless rate). Sargent–Stachurski `StochasticDiscounting`
(`SargentStachurski.StochasticDiscounting`): `specRad`, `IsPDRatio`, `isPDRatio_iff`,
`pdRatio_eq_tsum` (Exercise 6.3.6), `specRad_le_of_rowsum_le`. Obstfeld–Rogoff
`InternationalFinancialMarkets`: `Spanning.spans_iff_rank`, `Spanning.not_spans_of_card_lt`.

## §16.1–16.2 Introduction and background (pp. 467–469)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 467–468 | Why multiple assets; asset prices discipline preferences (fn. 1) | not formalised: narrative |
| p. 468 | Participation rates, portfolio heterogeneity, pension systems | not formalised: data |
| p. 468, Fig. 16.1 | Price–cash-flow ratios of housing and stocks, 1930–2023 | not formalised: data (figure) |

## §16.3 Dynamic stochastic endowment economy (pp. 469–473) — `Endowment`, `Equilibrium`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 469 | Event tree, histories, endowments, expected utility, power utility, EZ separates `γ` and `1/σ` | definitions; power utility marginal `tp_crra_marginal`; EZ in `EpsteinZin` |
| p. 470 | Feasible allocation; planner problem `U_λ(y)` | `enFeasible`, `enPlannerOpt`, `en_plannerValue`, `en_plannerValue_eq`, `en_plannerValue_ge` |
| (16.1), p. 470 | `λᵢ∂Uᵢ/∂cᵢ,ₜ(ωᵗ) = μₜ(ωᵗ)`, independent of `i` | `eq_16_1_pair`, `eq_16_1` |
| (16.2), p. 470 | Envelope: `∂U_λ(y)/∂yₜ(ωᵗ) = μₜ(ωᵗ)` | `eq_16_2` (with `en_line_deriv`) |
| (16.3), p. 470 | Agents' MRS = planner's MRS | `eq_16_3` |
| p. 470 | Arrow–Debreu budget set | `enBudgetAD` |
| (16.4), p. 471 | `∂Uᵢ/∂cᵢ,ₜ(ωᵗ) = αᵢp⁰ₜ(ωᵗ)`; `αᵢ > 0` when the budget binds | `eq_16_4_pair`, `eq_16_4`, `eq_16_4_pos` |
| (16.5), p. 471 | MRS = price ratio | `eq_16_5` |
| p. 471 | Arrow–Debreu equilibrium | `eqAD` (two-period form) |
| (16.6)–(16.7), p. 471 | With `λᵢ = 1/αᵢ` the conditions coincide (`μ = p⁰`) | `en_weights_match` |
| p. 471 | First Welfare Theorem: AD allocation = planner allocation, Pareto optimal | `en_fwt_planner`, `en_fwt_pareto`, `en_concave_le_fderiv` (concave case; corrections 10); Miao `theorem_13_3_1` (infinite tree) |
| (16.8), p. 471 | Sequential budget set | `tpBudget`/`eq_16_10` (two periods), `euBudget` (finite tree) |
| p. 472 | Sequential-markets equilibrium; zero net supply; positive supply of bonds | `eqSeq` (zero net supply); positive supply not formalised (variant of the definition) |
| p. 472 | Complete markets: every payoff stream is generated | `tp_complete_iff_rank` (two periods), `dt_statePrices_unique` (one-step, tree) |
| p. 472 | Three results with complete markets: (i) AD = sequential | `eq_seq_to_ad`, `eq_ad_to_seq` (two periods; corrections 11) |
| p. 472 | (ii) First Welfare Theorem | `en_fwt_planner`, `en_fwt_pareto` |
| p. 472 | (iii) a representative agent exists | `eq_repAgent` |
| p. 473 | Without complete markets the three results are lost; agents disagree on state prices | `ex2_disagreement` (illustration) |

## §16.4 Asset trading with two periods (pp. 473–482) — `TwoPeriod`, `Examples`, `Portfolio`, `SDF`, `Equilibrium`

| Source | Claim | Lean |
| --- | --- | --- |
| (16.9)–(16.10), p. 473 | The agent's problem and budget set | `tpBudget`, `tpBudgetPos`, `eq_16_10` |
| p. 473 | Budget equations bind with strictly increasing `U` | `tpBudgetBind` (binding form) |
| p. 473 | Arbitrage (two verbal forms) | `tpArbitrageBook`, `tp_isArbitrage_iff_book` |
| (16.11), p. 474 | `W = [−pᵀ; D]`; arbitrage `Wθ ≥ 0`, `Wθ ≠ 0`; arbitrage-free conditions | `tpW`, `tp_W_none`, `tp_W_some`, `tpIsArbitrage`, `tpNoArbitrage`, `tpArbitrageFree`, `tp_noArbitrage_iff_free` |
| p. 474 | Attainable set `M`; arbitrage ⇔ nonzero nonnegative element of `M` | `tpAttainable`, `tp_noArbitrage_iff_attainable` |
| p. 474 | No arbitrage ⇒ Arrow-security prices are strictly positive | `tp_arrow_price_pos` |
| p. 474 | Law of one price | `tp_law_of_one_price`, `tp_loop_assets` |
| (16.12), p. 474 | `pⁿ = Σ_ω dⁿ(ω)q(ω)` | `tpStatePrices`, `eq_16_12` |
| (16.13), pp. 474–475 | `q̂ = (1, q)` orthogonal to `M` | `tpQhat`, `tp_qhat_orth`, `eq_16_13` |
| p. 475 | FTAP: no arbitrage ⇔ state prices `q ≫ 0` | `tp_ftap` (corrections 4) |
| p. 475 | State prices ⇒ no arbitrage ("given asset prices `q`" sic) | `tp_noArbitrage_of_statePrices` (corrections 8) |
| p. 475 | State prices unique iff `rank D = S` | `tp_statePrices_unique_iff_rank`, `tp_rank_iff_transpose_injective` |
| p. 475 | `N = S`: `q = (Dᵀ)⁻¹p`; `N > S`: an invertible `S × S` block | `tp_statePrices_inverse`, `tp_statePrices_block` |
| p. 475 | `N < S`: incomplete, many state prices | `ex2_incomplete`, `ex2_statePrices_iff` |
| fn. 3, p. 475; Fig. 16.2 | Separating `M` and `K` | `tp_ftap` via `rd_stiemke` (corrections 4); figure not formalised |
| p. 476 | Example 1: rank 2, `q = (Dᵀ)⁻¹p` | `ex1D`, `ex1p`, `ex1q`, `ex1_complete`, `ex1_statePrices_formula`, `ex1_statePrices_eq` |
| p. 476 | Example 1: arbitrage restrictions; positive prices; `δ₁pᵇ > pˢ > δ₂pᵇ` | `ex1_noArbitrage_iff`, `ex1_returns_iff`, `ex1_prices_pos` |
| p. 477 | Example 1: `θ = D⁻¹x`, value `pᵀD⁻¹x`, positive on `x ≥ 0`, `x ≠ 0` | `ex1θ`, `ex1_value`, `ex1_value_pos` (corrections 8) |
| pp. 477–478 | Example 2: incomplete; no arbitrage iff `pˢ > 0`; `q(1) ∈ (0, .5)`, `q(2) = 2 − 4q(1)` | `ex2D`, `ex2_incomplete`, `ex2_noArbitrage_iff`, `ex2_statePrices_iff` |
| p. 477 | Optimum ⇒ no arbitrage | `tp_noArbitrage_of_optimal` |
| p. 477 | No arbitrage + continuous `U` ⇒ optimum (compact budget set) | `tp_budgetPos_isCompact`, `tp_endowment_mem`, `tp_exists_optimal`, `tp_exists_optimal_iff`, `tp_no_optimal_without_nonneg` (corrections 3) |
| p. 477 | The single budget constraint in state prices | `tp_budget_single` |
| (16.14), p. 478 | Budget set in state prices with the span restriction | `tpBudgetQ`, `eq_16_14`, `eq_16_14_counterexample` (corrections 2) |
| p. 478; Fig. 16.3 | Span restriction shrinks the budget set (bond-only example) | `eq_16_14_counterexample`; figure not formalised |
| p. 479 | Lagrangian FOCs: `ψᵢpⁿ = Σ_ω ηᵢ(ω)dⁿ(ω)` | `tp_portfolio_foc`, `tp_clm_apply` |
| (16.15), p. 479 | Subjective state prices `qᵢ = (∂U/∂c₁)/(∂U/∂c₀)` satisfy LoOP | `eq_16_15` |
| p. 479 | Power utility: `qᵢ(ω) = βπ(ω)(c₁/c₀)^{−γ}`; risk neutral `βπ(ω)` | `tp_crra_marginal`, `tp_crra_statePrice`, `tp_riskNeutral_statePrice` |
| pp. 479–480 | Disagreement on state prices, agreement on asset prices; example `(1/4, 1)`, `(1/3, 2/3)` | `ex2_disagreement` |
| p. 480 | Complete markets: agreement on state prices; sequential = AD budget set | `tp_agreement_complete`, `tp_budget_complete`, `eq_budgetPos_complete` |
| p. 480 | SDF `M = q/π`; `pⁿ = E[dⁿM]`; `1 = E[RⁿM]` | `sdfM`, `sdf_mul_M`, `sdf_price`, `sdf_return` |
| p. 480 | Power utility `M = β(c₁/c₀)^{−γ}`; risk neutral `M = β` | `tp_crra_statePrice`, `eq_16_16` |
| (16.16), p. 480 | Risk-neutral pricing `pᵇ = E[M] = β`, `pⁿ = E[dⁿ]/R_f` | `eq_16_16`, `sdf_bond` |
| p. 481 | Risk adjustment `pⁿ = E[dⁿ]/R_f − (−Cov(dⁿ, M))` | `sdf_risk_adjustment` |
| p. 481 | Only systematic risk matters; insurance assets | follows from `sdf_risk_adjustment`; narrative not formalised |
| (16.17), p. 481 | Risk premium | `eq_16_17`, `eq_16_17_printed_counterexample` (corrections 1) |
| (16.18), pp. 481–482 | `π* = q/Σq` positive, sums to one; `Σq = pᵇ = 1/R_f`; `pⁿ = E*[dⁿ]/R_f` | `riskNeutral`, `riskNeutral_pos`, `riskNeutral_sum`, `sdf_bond`, `eq_16_18` |
| p. 482 | `π*` unique if complete, otherwise possibly many | `riskNeutral_unique_of_complete`, `riskNeutral_unique_iff` (corrections 7) |
| p. 482 | Wall Street practice (backing out `π*`) | not formalised: narrative |
| p. 482 | Representative agent: `c = y`, `θ = 0`, same prices, `U_λ = Σλᵢ Uᵢ`, `λᵢ = 1/αᵢ` | `eq_planner_bound`, `eq_repAgent` |
| p. 482 | `q(ω) = (∂U_λ/∂y₁(ω))/(∂U_λ/∂y₀)` | `eq_repAgent_statePrice` |

## §16.5 Dynamic asset trading (pp. 482–485) — `DynamicTree`, `Euler`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 482 | Payoffs generated by a trading strategy | `DTree`, `dtTwoPeriod`, `dtPrev`, `dtPayoff`, `dtPayoffLin` |
| p. 483 | Arbitrage; attainable set | `dtNoArbitrage`, `dt_sum_parent`, `dt_value_payoff` |
| p. 483 | Complete markets (dynamic) | one-step form in `dt_statePrices_unique` |
| p. 483 | One-step state prices; dynamic law of one price | `dt_ftap` |
| p. 483 | Dynamic FTAP | `dt_ftap_deflator`, `dt_ftap`, `dtDeflatorAux`, `dtDeflator`, `dt_deflator_pos`, `dt_deflator_parent` (finite tree; corrections 12) |
| p. 483 | Infinite-horizon FTAP | not formalised: Ponzi schemes and bubbles (Miao `rd_ponzi_arb`, Theorems 13.4.1–13.4.2) |
| p. 483 | Optimum ⇒ no arbitrage; continuity + no arbitrage ⇒ optimum | `eu_noArbitrage` (interior, differentiable); existence on the tree not formalised (the two-period proof `tp_exists_optimal` is the model) |
| p. 484 | FOCs for consumption and asset holdings | `euBudget`, `eu_foc` |
| (16.19), p. 484 | Subjective state prices; `M = q/π` | `eq_16_19`, `sdfM` |
| (16.20), p. 484 | Expected power utility; its marginal utility | `eu_crra_partial` |
| (16.21), p. 484 | State price with power utility | `eq_16_21` (corrections 5) |
| p. 484 | Complete markets: unique state prices and SDF | `dt_statePrices_unique` |
| (16.22)–(16.23), p. 484 | Returns; `Eₜ[MR] = 1` | `eq_16_23` |
| p. 485 | `Eₜ[M]Eₜ[R] + Covₜ = 1`; conditional premium | `eu_conditional_premium` |

## §16.6 The equity premium and risk-free rate puzzles (pp. 485–488) — `MehraPrescott`, `FigureClaims`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 485 | Single agent, zero-net-supply assets, `c = y`, `θ = 0` | `eq_repAgent` (aggregation result) |
| p. 485 | Lucas tree formulation | not formalised: an equivalent description of the same equilibrium |
| p. 486 | Symmetric chain, stationary `(1/2, 1/2)` | `mpPi`, `mp_stationary_iff` |
| (16.24), p. 486 | `vₜ = Eₜ[βG^{1−γ}(1 + vₜ₊₁)]` | `mp_pd_step` |
| p. 486 | `v = βA(1 + v)`, `v = (I − βA)⁻¹βA𝟙` | `mpA`, `mp_pd_unique`, `mp_specRad_lt_one` |
| fn. 4, p. 486 | Recursive substitution series | `mp_pd_series` |
| (16.25), p. 486 | `rˢᵢⱼ = Gⱼ(1 + vⱼ)/vᵢ − 1` | `eq_16_25` (corrections 8) |
| (16.26), p. 487 | Conditional and unconditional expected returns | `mpCondMean`, `mpUncondMean` |
| p. 487 | Bond price `pᶠᵢ = Σⱼ ΠᵢⱼβGⱼ^{−γ}` | `mpBond`, `mp_bond_price` |
| (16.27), p. 487 | `rᶠᵢ = 1/pᶠᵢ − 1`; its mean; equity premium | `mpRf`, `mpEquityPremium` |
| p. 487 | `G_L = 1 + μ − δ`, `G_H = 1 + μ + δ`; `μ` mean, `δ` variance, `φ` persistence | `fn5G`, `fn5_mean`, `fn5_var`, `fn5_autocorr` |
| fn. 5, p. 487 | Moments of `G`: mean, variance, autocorrelation | `fn5Mean`, `fn5Second`, `fn5Cross`, `fn5_mean`, `fn5_var`, `fn5_autocorr` |
| p. 487, Table 16.1 | Sample moments; GMM estimates of `μ, δ, φ` | not formalised: data |
| p. 487, Table 16.1 | The figure's growth process: `μ = 0.0175`, `δ = 0.0233`, `2φ − 1 = 0.1069` (exactly identified) | `mpfG`, `mpfPhi`, `mpf_primitives`, `mpf_values` |
| (16.26)–(16.27), p. 487 | Equity premium = average of conditional covariances with the SDF | `mpf_cond_cov`, `mpf_premium_cov`, `mpf_rf_mean` |
| p. 488, Fig. 16.4 | Region of the figure: `β ∈ [0,1]`, `γ ∈ [0,100]`, `E[rᶠ] < 4%` forces `γ < 5/2` | `mpf_gamma_lt` (via `mpf_rpow_convex`, `mpf_far_bounds`, `mpf_amhm`) |
| p. 488, Fig. 16.4 | Equity premium < 0.1% for `rᶠ < 4%` | false as printed: `mpf_counterexample`, `mpf_fig_16_4_printed_false` (`β = 1`, `γ = 9/4`: `rᶠ ≈ 3.78%`, premium ≈ 0.103%; via `mpf_ce_bounds`, `mpf_ce_core`, `mpf_ce_ep`, `mpf_pd_of_eqs`); corrected: premium positive (`γ > 0`) and < 0.17% on the whole region, `mpf_premium_bound` (via `mpf_core`, `mpf_core_bond`, `mpf_core_ratio`, `mpf_core_v`, `mpf_core_term`, `mpf_GL_bounds`, `mpf_GH_bounds`) (corrections 15) |
| p. 488 | "the equity premium and the risk-free rate are both positive" | premium: `mpf_premium_bound` (positive for `γ > 0` on the plotted region); riskless rate not formalised (narrative) |

## §16.7 Lognormal model (pp. 488–490) — `Lognormal`, `EpsteinZin`

| Source | Claim | Lean |
| --- | --- | --- |
| (16.28), p. 488 | `g ~ N(μ_g, σ_g²)`; `log M = log β − γg` | hypothesis `HasLaw g (gaussianReal μ v)` |
| (16.29), p. 488 | `pᶠ = βe^{−γμ_g + γ²σ_g²/2}`, `rᶠ = −log β + γμ_g − γ²σ_g²/2` | `eq_16_29`, `lgRf` |
| pp. 488–489 | Smoothing and precautionary motives | `lg_rf_growth`, `lg_rf_precautionary` |
| p. 489 | Smoothing dominates (rᶠ increasing in `γ`) iff `γ < μ_g/σ_g²`; Table 16.1 threshold | `lg_rf_mono_iff`, `lg_rf_strictMonoOn`, `lg_rf_strictAntiOn`, `lg_threshold_table` |
| p. 489 | Equity Euler equation; expected log return | `lg_equity_euler` |
| (16.30), p. 489 | `Eₜrˢ − rᶠ + σᵣ²/2 = γCovₜ(g, rˢ)` | `eq_16_30` (corrections 8, 14) |
| p. 489 | Jensen term `log EₜRˢ = Eₜrˢ + σᵣ²/2` | `lg_jensen` |
| p. 490 | CCAPM interpretation; CAPM comparison | not formalised: narrative |
| p. 490 | `σ_cσ_r = 0.0043`; `γ = 16` needed | `lg_sd_product`, `lg_gamma_bound`, `lg_gamma_16_short` (corrections 6) |
| p. 490 | With such `γ`, `rᶠ` exceeds 1% | `lg_rf_high` |
| p. 490 | Epstein–Zin separates the riskless rate (EIS) from the premium (risk aversion) | `ez_rf_smoothing`, `lg_power_smoothing`, `ez_power_case`, `ez_premium_weights` (via Miao `eq_20_33`) |

## §16.8 The excess volatility puzzle (pp. 490–492) — `IidGrowth`

| Source | Claim | Lean |
| --- | --- | --- |
| (16.31), p. 490 | iid growth ⇒ constant price–dividend ratio; series | `iid_pd_const`, `iid_pd_unique`, `iid_pd_solves`, `eq_16_31`, `iid_lognormal_pd` (corrections 13) |
| (16.32), p. 490 | `rˢ = g + log((1 + v)/v)`; return volatility = growth volatility | `eq_16_32`, `iid_return_var` |
| p. 491, Fig. 16.5, Table 16.2 | Dividend yield and excess returns; return-forecasting regressions | not formalised: data |
| pp. 491–492 | Three approaches (time-varying moments, beliefs, preference shocks) | not formalised: narrative (the role of `Covₜ` is `eu_conditional_premium`) |
