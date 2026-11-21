# Source map: AKMM Chapter 18

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 18, Nominal frictions and business cycles (Alisdair McKay and Morten
Ravn), pp. 533–560, and Appendix 18.A, pp. 871–876. Page references are the draft's running
heads. Lean names are relative to `AKMM.NominalFrictions` unless qualified. Departures from the
book are in [corrections](corrections.md). The chapter has no numbered theorems; equations run
(18.1)–(18.27) and (18.A.1)–(18.A.10).

## §18.1 Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 533 | Great Depression, Keynesian ideas, Hume (1752), aims of the chapter | not formalised: narrative |

## §18.2 Empirical evidence on price rigidity (`Duration`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 534 | Expected time between price changes `∑(1 − θ)θᵗ t = θ/(1 − θ)` | corrected: `dur_printed_sum`, `dur_printed_weights_sum`, `dur_printed_weights_ne_one`, `dur_pmf_sum`, `dur_mean`, `dur_printed_eq_mean_sub_one`, `dur_printed_ne_mean` (correction 1) |
| pp. 533–535 | BLS CPI micro data; mean/median durations 6.2/3.4, 8.0/6.9, 10.1/8.3 months; sales, substitutions; 11.5% median change; Eichenbaum–Jaimovich–Rebelo; Boivin–Giannoni–Mihov | not formalised: data and empirical discussion |

## §18.3 The New Keynesian model

### Environment and decision problems (`Environment`, `ResetPrice`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 536, (18.1) | Preferences | `nfU` |
| p. 536, (18.2)–(18.4), p. 537 | CES aggregator, cost minimisation, price index, demand | `env_ces` (Galí's `unitInterval_expenditure_minimisation`) |
| p. 537, footnote 4 | `P` is the derivative of the cost function | `env_cost_deriv` |
| p. 537 | Price elasticity of demand is `ε` | `env_demand_elasticity` |
| p. 536, (18.3) | Real marginal cost `w/A` | `env_marginal_cost` |
| p. 537 | Cashless limit; money in the utility function gives the same equilibrium (footnote 5) | not formalised: remark (cites Chapter 17) |
| p. 538 | Real budget constraint | `env_real_budget` |
| p. 538, (18.5) | Euler equation | `env_euler_foc`, `eq_18_5` (perfect foresight), `eq_18_5_stochastic` (Miao's `eq_19_3`) |
| p. 538, (18.6) | Labour supply condition | `env_labour_foc`, `eq_18_6` |
| p. 538 | `p_{t+1} = p_t/(1 + π_{t+1})` | `env_relprice_law` |
| p. 539 | Real profits `(p − w/A) p^{−ε} Y` | `env_profit` |
| p. 539 | Bellman equation `V(p, S)`; the bracket is marginal profit | `rpBracket`, `rp_bracket_deriv`; the envelope condition `RPEnvelope` (instance `rp_series_envelope`) |
| p. 539, App. 18.A.1 p. 871 | Combining envelope and FOC: the sum condition | corrected: `rpDefl`, `rpTerm`, `rp_iterate`, `rp_series`, `rp_term_succ` (correction 2) |
| p. 539 | The rearranged condition | corrected: `rp_term_eq`, `rp_foc_rearranged` |
| p. 540, (18.7) | `p^R = p^N/p^D` with the `p^N`, `p^D` recursions | corrected: `rpN`, `rpD`, `eq_18_7`, `rp_pN_rec`, `rp_pD_rec`, `rp_defl_const_rpow`, `rp_constant_correct`, `rp_constant_printed`, `rp_printed_ne_iff` |
| p. 539 | Firms are more forward looking when prices are stickier; respond to future costs | not formalised: interpretation (the weights `(βθ)^k` are explicit in `rpTerm`) |

### Market clearing and aggregation (`Aggregation`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 540, (18.8) | `Y = C`, labour and bond market clearing | used as hypotheses (`eq_18_13`, `eq_18_A_5_exact`) |
| p. 540, (18.9) | Calvo price index | `eq_18_9` (Miao's `eq_19_13`) |
| p. 541 | `p^R = [(1 − θ(1 + π)^{ε−1})/(1 − θ)]^{1/(1−ε)}` | `agg_index_relative`, `agg_reset_relprice` |
| p. 541, (18.10) | Inflation from the reset price | `eq_18_10` |
| p. 541, (18.11) | `Y = AL/D` | `eq_18_11` |
| p. 541 | `D ≥ 1`; `D = 1` iff no dispersion; then `Y = AL` | `agg_dispersion_ge_one`, `agg_dispersion_eq_one_iff` (Galí, `α = 0`), `agg_flex_output` |
| p. 541, (18.12) | Dispersion recursion | `eq_18_12` (Miao's `eq_19_17`, `α = 0`) |
| p. 542 | State variables `A_t`, `D_{t−1}`; definition of equilibrium | not formalised: definitions collecting the equations above |

### Flexible prices, output gap, rules (`NaturalOutput`, `ThreeEquation`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 542, footnote 7 | Static profit maximisation gives the markup `µ = ε/(ε − 1)` | `nat_markup_foc`, `nat_markup_max`, `nat_markup_gt_one` |
| p. 542 | `w^n/A = 1/µ` | `nat_wage` |
| p. 542, (18.13) | Natural output | `nat_output_general`, `eq_18_13`, `eq_18_13_solves` |
| p. 542, (18.14) | Output gap | `nfGap` |
| p. 543 | Rule `i = ī + φ_π(π − π*) + φ_x x`, `ī = (1 + π*)/β − 1` | `nat_rule_intercept` |
| p. 543, footnote 8 | Quarterly rescaling `0.5 → 0.125` | `nat_quarterly_rule` |
| p. 543 | Taylor (1993) coefficients 1.5, 0.5 describe the Fed 1987–92 | not formalised: data |
| p. 543, (18.15), footnote 9 | IS curve; `x = Ŷ − (1+ψ)/(σ+ψ)Â` | `nat_gap_loglinear`, `eq_18_15_exact`, `eq_18_15` |
| p. 543 | The natural rate `r^n` | corrected: `eq_18_15_exact`, `rn_printed_iff` (correction 3) |
| p. 544, (18.16) | NKPC with `κ = (1 − θ)(1 − βθ)(σ + ψ)/θ` | `nfKappa`, `eq_18_16` |
| p. 544 | `κ` larger if prices more flexible or marginal cost more sensitive | `nk_kappa_pos`, `nk_kappa_antitone`, `nk_kappa_mono_sens` |
| p. 544, (18.17) | Rule with shock | corrected: `rule_18_17_no_steady_state` (correction 4) |
| pp. 544–545 | Nominal demand and real output (classical dichotomy fails; solving (18.16) forward) | not formalised: qualitative discussion |

### Determinacy (`Determinacy`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 544, (18.18) | Unique equilibrium iff `(1 − β)φ_x + κ(φ_π − 1) > 0` | `eq_18_18` (Galí's `determinate_iff_BM`) |
| p. 544 | `φ_π > 1` sufficient; necessary if `φ_x = 0` | `det_taylor_sufficient`, `det_taylor_necessary` |
| p. 544 | Indeterminacy with an unresponsive rate (intuition) | covered by `eq_18_18`; narrative not formalised |
| App. 18.A.2, p. 873 | The system after substituting the rule | `det_system` |
| p. 873 | Matrix form, inverse, coefficient matrix | `detM0`, `detM1`, `detInv`, `det_inverse`, `det_coeff_eq_AT` |
| p. 873 | `a₁`, `a₀` | `det_a1`, `det_a0` |
| p. 873 | Jury: `|a₀| < 1`, `|a₁| < 1 + a₀` ⇔ (18.18) | `det_jury_iff`, `det_roots_iff` (Galí's `schurStable_iff_roots`) |
| p. 873 | `|a₀| < 1` always holds | corrected: `det_a0_not_automatic` (correction 5) |
| p. 873 | Deterministic without loss of generality (certainty equivalence) | not formalised separately: `eq_18_18` is for general expectation systems |

## §18.4 Monetary policy strategies

### §18.4.1 Policy objectives (`Efficiency`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 545, (18.19) | Planner's FOC and `Y* = A^{(1+ψ)/(σ+ψ)}` | `eff_planner_foc`, `eq_18_19`, `eq_18_19_solves` |
| p. 545 | `Y = (w/A)^{1/(σ+ψ)} Y*` without dispersion | `eff_output_wage` |
| p. 546 | `Y^n < Y*` since `w/A = 1/µ < 1`; pricing at marginal cost gives `w/A = 1` | `eff_natural_lt`, `eff_marginal_cost_pricing` |
| p. 546 | Nominal rigidities move markups (narrative) | not formalised: qualitative |
| p. 546 | `Y = D^{−ψ/(σ+ψ)}(w/A)^{1/(σ+ψ)} Y*` | `eff_output_dispersion`, `eff_dispersion_lowers` |
| p. 546, footnote 10 | Calvo vs menu-cost dispersion | not formalised: remark |
| p. 546 | `x^w = x − log µ/(σ+ψ)` | `eff_welfare_gap` |
| pp. 546–547 | Phillips, Friedman–Phelps, long-run vertical curve | not formalised: history |
| p. 547 | Subsidy `τ = 1/ε ∈ (0, 1)` undoes the monopoly distortion | `eff_subsidy`, `eff_subsidy_mem`, `eff_subsidy_natural_eq` |
| p. 547, (18.20), footnote 11 | Second-order welfare approximation | `eq_18_20_utility` (Galí's `Welfare.period_utility_normalised`, `α = 0`), `eq_18_20_weight`, `eq_18_20_period` (Galí's `periodLoss_eq_scaled`) |

### §18.4.2–18.4.4 (`Policy`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 547 | Divine coincidence | `pol_divine_coincidence` (Galí's `divine_coincidence`) |
| pp. 547–548 | Productivity shocks move `Y^n` and `Y*` in equal proportions | `eq_18_13`, `eq_18_19` (`Y^n/Y* = µ^{−1/(σ+ψ)}` constant: `eff_natural_lt`) |
| p. 548, (18.21) | Cost-push shocks break the divine coincidence | `pol_costpush_iterate`, `pol_costpush_breaks` |
| p. 548 | Elasticity shocks yield (18.21) (Steinsson 2003); Blanchard–Galí wage frictions | not formalised: cited derivations |
| p. 548, (18.22) | Flexible inflation targeting loss resembles (18.20) | `pol_loss_22_eq_20` |
| p. 548 | Price-level targeting rule | `pol_price_level_rule` (Galí's Exercise 4.6, `determinate_of_pos`); the book makes no formal claim |
| p. 549 | Discretion: steady state from date 1, `π₀ = κx₀ + η₀`, optimal `x₀` | `pol_discretion_date0` |
| p. 549, footnote 12 | No endogenous state to first order (`D̂ ≈ 0`) | `nk_dispersion_hat_zero` |
| pp. 549–550 | Commitment path: less inflation and a smaller output fall at date 0, negative afterwards | `polShock`, `pol_shock_ar1`, `pol_shock_bound`, `pol_commitment_path`, `pol_commitment_date0` (Galí's `impulse_rho0`, `commit_coef_lt`) |
| p. 550 | Commitment better than discretion | `pol_commitment_better` (Galí's `commitment_lt_discretion`) |
| p. 550 | Time inconsistency | `pol_time_inconsistent` |
| p. 550 | Price level: jumps and stays under discretion; returns under commitment | `pol_discretion_price_level`, `pol_commitment_price_level` |
| p. 549, Figure 18.1 | Simulated responses (`β = 0.99`, `κ = 0.2`, `ε = 3`) | not formalised: figure and simulation (the qualitative claims are above) |

## §18.5 Aggregate evidence of nominal rigidity

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 550–552, Figure 18.2, footnotes 13–15 | Monetary policy shocks (Kuttner, GSS, Romer–Romer), IRFs, model comparison, price puzzle, calibration | not formalised: data, figure, simulation |
| p. 552 | CEE (2005) estimates, contract length 2.5 quarters | not formalised: estimated model and its numbers |
| p. 553 | GG rewrite with the expectational error `ζ_t` | `gg_rewrite` (`Estimation`) |
| p. 553, footnote 16 | Lagged instruments are orthogonal to `ζ_t` | `gg_lie`, `gg_orthogonal`, `gg_cov_zero`; sign: `gg_expand` (correction 6) |
| p. 554 | `mc = w/(∂Y/∂L) = s_L/α_L`; log mc = log labour share | `gg_mpl`, `gg_marginal_cost`, `gg_log_mc` |
| p. 554 | GG GMM estimates (`1 − θ ∈ [0.085, 0.171]`), hybrid NKPC estimates, MPS (2014) | not formalised: estimation results |
| p. 555, Figure 18.3, footnotes 17–18 | Labour share–inflation correlations, CEE vs single-equation approaches | not formalised: data, figure |

## §18.6 Sticky wages and other extensions

### §18.6.1 Sticky wages (`StickyWages`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 555–556 | Motivation (Keynes, Kahn 1997, Taylor contracts, insurance) | not formalised: narrative |
| p. 557 | Sticky wages only: `P = W`, real wage `w = 1` | corrected: `sw_flexprice_real_wage`, `sw_real_wage_not_constant` (correction 7) |
| p. 557 | Same Phillips curve as with sticky prices (sticky wages only) | not formalised: asserted without derivation |
| p. 557, (18.23) | Price Phillips curve | `eq_18_23` |
| p. 557, (18.24) | Wage Phillips curve, `κ^w = ξ^w(σ + ψ)` | `sw_wage_pc` (Galí's `eq15_iff`, `φ = 0`), `eq_18_24` |
| p. 557, (18.25) | Real-wage identity | `eq_18_25` |
| pp. 557–558, footnotes 21–22, Figure 18.2 | Interpretation, simulation with doubled frequencies | not formalised: discussion, simulation |
| App. 18.A.3, p. 873, (18.A.7) | Preferences over hours `N` | `nfU` (with `N` for `L`) |
| p. 874, (18.A.8)–(18.A.9) | Labour composite, demand `(W_i/W)^{−ε}ℓ`, wage index, labour income `WL` | `sw_labour_ces` |
| p. 874 | `N = D^W L`, `D^W ≥ 1` | `sw_hours`, `sw_wage_dispersion_ge_one` |
| p. 875 | The union's objective and first-order condition | `sw_union_term_deriv`, `sw_union_foc` |
| p. 875, (18.A.10) | Log-linear union condition and its recursive form | `ResetRecursion` / `eq_18_A_4` apply verbatim with `σĈ + ψN̂ − ŵ` for marginal cost; levels form in `sw_wage_pc` |
| p. 875 | `π^w = (1 − θ_w)/θ_w · ŵ^R`; `ξ^w` | `eq_18_A_3` (with `θ_w`), `sw_wage_pc` |
| p. 876 | `σĈ + ψN̂ = (σ + ψ)Ŷ − ψÂ`; wage PC in the gap | `eq_18_24` |
| p. 876 | Price PC with `ξ^p` | `eq_18_23` |

### §18.6.2 Other extensions (`Extensions`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 558, (18.26) | Habit term as level plus change | `ext_habit` |
| pp. 558–559, footnote 23 | Habits and gradual adjustment; HANK | not formalised: qualitative |
| p. 559, (18.27) | Cobb–Douglas with capital | `ext_labour_elasticity` |
| p. 559 | Investment sensitivity without adjustment costs | not formalised: qualitative |
| p. 559, footnote 24 | `ξ(δ) = δ` gives `Q = 1` | corrected: `ext_adj_foc`, `ext_tobin_q`, `ext_adj_steady`, `ext_q_one_iff`, `ext_q_counterexample` (correction 8) |
| p. 560 | Labour elasticity `1 − α`; `1/(1 − α)` units of labour | corrected: `ext_labour_elasticity`, `ext_labour_requirement_pct`, `ext_labour_requirement_units`, `ext_units_printed_false` (correction 9) |
| p. 560 | Variable capacity utilisation; medium-scale models (CEE, Smets–Wouters) | not formalised: estimated models and qualitative discussion |

## Appendix 18.A.1 (`ResetPrice`, `ThreeEquation`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 871 | Envelope condition, FOC `V_p = 0` | `RPEnvelope`, `rp_series_envelope`, `rp_iterate`, `rp_series` |
| p. 871 | The combined and rearranged conditions | corrected: `rp_term_eq`, `rp_foc_rearranged` (correction 2) |
| p. 871, (18.A.1) | Log-linear present-value condition | hypothesis of `eq_18_A_2` (with `p̂^R_{t,τ} = p̂^R_t − (P̂_τ − P̂_t)`) |
| p. 871, (18.A.2) | Recursive reset price | `eq_18_A_2` (perfect foresight), `ResetRecursion`; concrete nonzero instance satisfying all hypotheses of `eq_18_A_4`, `eq_18_16`, `eq_18_23`: `reset_recursion_instance` |
| p. 872, (18.A.3) | `π = (1 − θ)/θ · p̂^R` | `eq_18_A_3`, `eq_18_A_3_exact` |
| p. 872, (18.A.4) | NKPC in marginal cost | `eq_18_A_4` |
| p. 872 | `D̂_t = −ε(1 − θ)p̂^R + θεπ + θD̂_{t−1}`, `D̂ = θD̂_{t−1}`, `D̂ = 0` | `eq_18_A_dispersion`, `nk_dispersion_hat_rec`, `nk_dispersion_hat_zero` |
| p. 872, (18.A.5)–(18.A.6) | `ŵ − Â = (σ + ψ)(Ŷ − Ŷ^n)` | `eq_18_A_5_exact` (exact, with the term `ψ log D`), `nat_gap_loglinear` |
| p. 872 | Plug into (18.A.4) to obtain (18.16) | `eq_18_16` |

## Dependencies used

Galí (MonetaryEconomics): `BasicNewKeynesianModel` (`PriceDuration`, `CES`, `PriceDispersion`,
`Expectations`, `Determinacy`, `TaylorRuleSystem`), `MonetaryPolicyDesign` (`Welfare`,
`OptimalPolicy`, `Ex4_6`), `DiscretionCommitment` (`LossAndCostPush`, `Commitment`,
`CommitmentVsDiscretion`), `StickyWagesPrices` (`WageInflation`). Miao (EconomicDynamics):
`NewKeynesian` (`NKHouseholds`, `NKEquilibrium`). The Woodford packages `StabilizationWelfare`
and `GainsFromCommitment` are declared but not imported: Galí's results cover (18.20) and the
commitment comparison in the book's setting.
