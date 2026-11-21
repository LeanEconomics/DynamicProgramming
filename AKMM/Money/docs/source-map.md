# Source map: AKMM Chapter 17

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 17, Money (A. Hornstein and P. Krusell), pp. 493–531; the chapter has no
appendix. Page references are the draft's running heads. Lean names are relative to
`AKMM.Money`. Departures from the book are in [corrections](corrections.md).

## §17.1 Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 493–496 | Theories of and with money, Wallace's dictum, Friedman's dictum, chapter plan | not formalised: narrative |
| p. 496 | "Asset pricing, as discussed in Chapter 15" | not formalised: cross-reference (it is Chapter 16; corrections, item 3) |

## §17.2.1 The endowment economy (`OLGDemand`, `OLGEquilibrium`)

| Source | Claim | Lean |
| --- | --- | --- |
| (17.1), p. 497 | The young's problem | `olgUtil`, `olgFeasible`, `olgOptimal`; in money units `olgMoneyUtil`, `olgMoneyFeasible`, `olgMoneyOptimal`, `olg_moneyUtil_eq` |
| (17.2), p. 497 | Budget set in consumption, `c_y ≤ ω_y` | `eq_17_2` |
| p. 498 | Interior solution `c_y = (ω_y + ω_o/R)/2`, `c_o = (ω_yR + ω_o)/2`; valid iff `R ≥ ω_o/ω_y` | `olg_interior_cons`, `olg_interior_iff` |
| (17.3), p. 498 | Money demand `max{(ω_y − ω_o/R)/2, 0}`, the unique optimum | `olgDemand`, `eq_17_3`, `olg_demand_eq_max`, `olg_util_sub_le`, `olg_demand_feasible`, `olg_demand_marginal`, `olg_moneyOptimal_iff_pos` |
| (17.4), p. 498, fn. 4 | Market clearing; with `p ≡ 0` the stock is passed on | `olgIsEquilibrium`, `olg_moneyOptimal_zero_zero`, `olg_nonmonetary_exists` |
| p. 498 | Money valued at all dates or at none | `olg_moneyOptimal_zero_pos`, `olg_step_iff`, `eq_17_5` |
| (17.5), p. 498 | `p_{m,t+1} = ω_op_{m,t}/(ω_y − 2Mp_{m,t})` | `eq_17_5`, `eq_17_5_div` |
| p. 498 | Constant solution `p̄_m = (ω_y − ω_o)/(2M)`, positive iff `ω_y > ω_o` | `olg_stationary`, `olg_map_fixed_iff` |
| p. 499, Fig. 17.2 | Domain `p < p̃_m = ω_y/(2M)`; map increasing; steady states `0`, `p̄_m`; slopes `ω_o/ω_y`, `ω_y/ω_o`; case (ii) slope at origin `≥ 1` | `olgMap`, `olg_map_domain`, `olg_map_strictMonoOn`, `olg_map_fixed_iff`, `olg_map_hasDerivAt`, `olg_map_slopes` |
| p. 499 | `p_{m,0} > p̄_m` not an equilibrium; `p_{m,0} < p̄_m` decreasing to zero | `olg_continuum`, `olg_decreasing_to_zero` |
| p. 499 | Classification: continuum `p_{m,0} ∈ [0, p̄_m]` if `ω_y > ω_o`; only `p ≡ 0` if `ω_y ≤ ω_o` | `olg_classification`, `olg_closed_form_step`, `olg_continuum`, `olg_unique_given_p0`, `olg_no_monetary` |
| p. 499 | Real form `m_{t+1} = ω_om_t/(ω_y − 2m_t)`; nominal stock irrelevant | `eq_17_5_real`, `olg_nominal_neutral` |
| Figure 17.1, Figure 17.2 | Budget set and phase diagram | figure; content covered by the rows above |

## §17.2.2 Welfare comparisons (`OLGWelfare`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 500 | Efficiency iff the long-run return is `≥ 1`; `ω_y ≤ ω_o` gives efficiency | `olg_miao_autarky_pareto_iff` (via Miao, Prop. 16.1.2) |
| p. 500 | Stationary monetary equilibrium efficient | `olg_miao_stationary_pareto` (via Miao, Prop. 16.1.3) |
| p. 500 | Non-stationary and non-monetary equilibria inefficient; long-run return `ω_o/ω_y` vs `1` | `olg_stationary_dominates`, `olg_return_limit` |
| p. 500 | Stationary equilibrium Pareto-improves autarky; utility `2 log((ω_y + ω_o)/2) > log ω_y + log ω_o` | `olg_stationary_welfare`, `olg_monetary_improves_autarky` |
| p. 500 | Smoothed allocation would hurt the initial old when `ω_y < ω_o` | `olg_smoothing_hurts_old` |
| p. 500 ("exercise") | Non-stationary monetary equilibria improve on autarky; equilibria ranked by `p_{m,0}` for all generations; higher return is better | `olg_monetary_improves_autarky`, `olg_ranking`, `olgIndirect`, `olg_indirect_eq`, `olg_indirect_strictMonoOn`, `olgCohortUtil`, `olg_cohort_util_eq`, `olg_return_strictMonoOn` |
| — | Model check: the book's economy is Miao's Samuelson economy | `olgMiao`, `olg_miao_paths` |

## §17.2.3 Extensions (`OLGMoneyGrowth`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 500–501, fn. 6 | Neoclassical OLG with capital; condition for inefficiency; capital and money coexist | not formalised: asserted, left as an exercise |
| p. 501 | Money growth `1 + µ`: stationary return `1/(1 + µ)`, lower real value of money | `mgStock`, `mgIsEquilibrium`, `mgStock_pos`, `mgStock_succ`, `mg_step_iff`, `mg_stationary_iff`, `mg_return`, `mg_value_strictAntiOn` |
| p. 501 | "the same type of equilibrium characterization" for non-stationary paths | difference equation only (`mg_step_iff`); the classification is not proved |
| p. 501 | Seigniorage, bonds, open-market operations, Ricardian equivalence | not formalised: verbal |

## §17.3.1 Fiat money has no value (`Dynastic`)

| Source | Claim | Lean |
| --- | --- | --- |
| (17.6)–(17.10), pp. 502 | Preferences, technology, budgets | used as hypotheses of the rows below |
| (17.11), p. 502 | Budget in total wealth `â` | `eq_17_11` |
| p. 502 | Bond-return mismatch gives unbounded consumption | `dyn_unbounded` |
| (17.12), p. 503 | No-arbitrage `q_t = p_{m,t}/p_{m,t+1} = p_{m,t}/(p_{m,t+1}(1 + i_t))` | `eq_17_12`, `eq_17_12_prices` |
| (17.13), p. 503 | Compact budget | `eq_17_13` |
| p. 503 | `i_t > 0` ⇒ money not valued | `dyn_no_value_of_pos_rate` |
| (17.14), p. 503 | TVC ⇒ `p_{m,0} lim M_T ≤ 0`; money valued only if it vanishes | `eq_17_14`, `dyn_printed_product`, `dyn_tvc_money_vanishes`, `dyn_no_valued_money` |
| (17.15), p. 503 | Fisher equation | `eq_17_15` |

## §17.3.2 Reduced-form liquidity (`CashInAdvance`, `TransactionCosts`, `MoneyInUtility`)

| Source | Claim | Lean |
| --- | --- | --- |
| (17.16)–(17.19), p. 504 | CIA constraint and budget in real balances | `eq_17_19` |
| (17.20)–(17.23), p. 504 | First-order conditions | hypotheses of the rows below (taken as given, as in the book) |
| pp. 504–505 | Stationary equilibrium: `q = β`, `p_m = c/M`, `q(1 + i) = 1`, `µ > 0` | `eq_17_24`, `cia_stationary_growth` |
| (17.24), p. 505 | `u₂/u₁ = zλ/(λ + µ) = βz` | `eq_17_24` |
| p. 505 | The CIA must bind (else TVC fails) | `cia_must_bind` |
| p. 505 | MRS `βz` below MRT `z`; leisure higher, consumption lower | `cia_mrs_lt_mrt`, `cia_log_consumption`, `cia_log_compare` |
| p. 505, p. 512 | Money growth `γ`: tax `(1 − γ)p_mM`, return `1/γ`; Friedman rule `γ = β` optimal, TVC holds, `i = 0` | `cia_stationary_growth`, `cia_friedman_rule` |
| p. 505 | "money will always be valued" (not demonstrated), velocity 1 | not formalised: verbal |
| pp. 506–509, Figs. 17.3–17.4 | Quantity theory in the data | not formalised: data and figures |
| (17.25), p. 510 | `ψ(x) = κx^η`, homogeneity of degree one | `tcPsi`, `tc_cost_homogeneous`, `tc_psi_hasDerivAt` |
| (17.26)–(17.28), p. 510 | FOCs and their combination | `eq_17_28`, `tc_fisher_lhs` |
| (17.29), p. 510 | `M_{t+1} = P_tc_t((1/(κη))i/(1 + i))^{−1/(1+η)}`; interest-elastic, proportional to consumption | `tcDemand`, `eq_17_29`, `tc_demand_homogeneous`, `tc_demand_elasticity`, `tc_log_demand`, `tc_demand_strictAntiOn` |
| (17.30)–(17.34), p. 511 | MIU preferences and FOCs | hypotheses of `eq_17_35` |
| (17.35), p. 511 | `u₂/u₁ = i/(1 + i)` | `eq_17_35` |
| p. 511 | Homothetic `u` ⇒ `m/c` a function of `i/(1 + i)` | `miu_homothetic_partials`, `miu_homothetic_mrs`, `miu_homothetic_demand`, `miu_ces_crs` |
| p. 512 | Friedman rule optimal in TC/MIU only with satiation | not formalised: verbal (cf. Galí's `no_planner_optimum_isoelastic`) |

## §17.3.3 Policy and indeterminacy (`Hyperinflation`, `InterestRules`, `CashlessLimit`, `GovernmentBudget`, `FiscalMonetary`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 512 | Stationary equilibria and the quantity theory | `eq_17_24`, `mg_return` |
| p. 512, fn. 10 | Non-monetary equilibria only with bounded utility/costs | not formalised: verbal |
| (17.36)–(17.37), p. 513 | Binding-CIA Euler equation, money growth `γ` | `eq_17_36`, `eq_17_37` |
| (17.38), p. 513 | `γm_t = βm_{t+1}u′(m_{t+1})` | `eq_17_38`, `hypIsPath` |
| p. 513 | Steady states `u′(m̄) = γ/β` and `0` | `hyp_steady_iff` |
| p. 513 | Every `m₀ ∈ (0, m̄)` gives a path converging to zero | `hyp_step_exists`, `hyp_tendsto_zero`, `hyp_exists_path`; all paths with `m u′(m)` increasing: `hyp_all_paths` (corrections, added hypothesis 1) |
| fn. 11, p. 513 | `m̄` unstable; stability at `0` iff `u′(0) > γ/β`; CIA binds along the paths | `hyp_above_increasing`, `hyp_local_stable`, `hyp_local_unstable`, `hyp_return_lt` |
| fn. 12, p. 513 | Log utility: unique path | `hyp_log_unique` |
| p. 513 | Obstfeld (1984) local indeterminacy under MIU | not formalised: cited only |
| p. 514 | "inflation equals the inverse of the money growth rate" | `mg_return` (corrections, item 1) |
| pp. 514–515 (box) | Interest-rate rules: VARs, Goodfriend, Taylor | not formalised: history |
| p. 515 | CIA peg: `q_t = β`, `p_{m,t}/p_{m,t+1} = β(1 + i_t)`, `u′(c_{t+1}) = 1 + i_t` | `pegIsEquilibrium`, `peg_pins` |
| p. 515 | `p_{m,0}` indeterminate, `c₀ = min(p_{m,0}M₀, c₀*)`, real indeterminacy | `peg_c0`, `peg_exists`, `peg_real_indeterminacy` |
| (17.39)–(17.40), pp. 515–516 | Rule `i = φ(P/P̃)`, target, difference equation | `ruleMap`, `eq_17_40`, `rule_target` |
| p. 516 | Linearisation slope `1 + φ′(1)/(1 + ĩ)` | `rule_map_hasDerivAt`, `rule_local_bound` |
| p. 516 | `φ′(1) > 0` ⇒ unique bounded solution | `rule_determinate`, `rule_phi_pos_determinate` |
| p. 516 | "`φ′(1) < 0` ⇒ indeterminacy" | corrected: `rule_indeterminate`, `rule_phi_neg_indeterminate`, `rule_phi_very_neg_determinate`, `rule_printed_counterexample` (corrections, item 4) |
| fn. 14–15, p. 516 | Bounded paths; knife edge `φ′(1) = 0` | `rule_determinate`; `rule_knife_edge` (affine rule) |
| p. 516, fn. 16 | Exogenous `r_t` justified with separable MIU | not formalised: verbal |
| pp. 516–517 | Interest on money | not formalised: verbal |
| p. 517 | Euler equation and money demand under MIU | `eq_17_35` |
| p. 518 | CES index `h`, partial derivatives | `clH`, `clh`, `clh1`, `clh2`, `clTheta`, `clH_pos`, `cl_h_eq_composite`, `cl_h_hasDerivAt_c`, `cl_h_hasDerivAt_m` |
| (17.41), p. 518 | Money demand; unit elasticity in `c`, constant elasticity in `i/(1 + i)`, `M/P → 0` as `ω → 0` | `clDemand`, `eq_17_41`, `cl_demand_homogeneous`, `cl_demand_elasticity`, `cl_demand_strictAnti`, `cl_demand_tendsto_zero` |
| p. 518 | Linearised Euler equation in logs | not formalised: displayed approximation only; its coefficients are the elasticities below |
| fn. 17, p. 519 | `(i/(1 + i))m₁/c = (u₁₂m₁/u₁)/(u₂₁c/u₂)` | `cl_footnote_17` |
| fn. 18, p. 519 | `u₁₁c/u₁` and `u₁₂m₁/u₁` decompositions; limits `η_{u₁,c} → −f″c/f′`, `η_{u₁,m₁} → 0` | `cl_h1_hasDerivAt_c`, `cl_h1_hasDerivAt_m`, `cl_footnote_18_identities` (corrected), `cl_h2_mul`, `cl_weight_tendsto`, `cl_footnote_18_limits` |
| p. 519 | Money-supply rule would send `P → ∞` | not formalised: verbal |
| (17.42), p. 519 | Flow budget | `gb_flow_real` |
| (17.43), p. 520, fn. 19 | Present-value budget (with corrected discounting) | `gb_iterate`, `eq_17_43`, `gb_printed_discount` |
| (17.44), p. 520 | Budget in total liabilities, arbitrage seigniorage `i/(1 + i)` | `eq_17_44` |
| p. 521 | Laffer curve of `f(i)i/(1 + i)` | `lf_increasing_part`, `lf_interior_max`, `lf_counterexample`, `lf_tc_no_max` |
| p. 521 | Stationary budget `ḡ + r̄d̄/(1 + r̄) = τ̄ + c̄f(ī)ī/(1 + ī)` | `gb_stationary` |
| p. 521 | Higher `d̄` ⇒ higher `ī` and inflation; Sargent–Wallace | `ua_stationary`, `ua_dynamic` |
| p. 522 | `i = 0` budget | `gb_zero_rate`, `gb_zero_rate_printed` (corrections, item 5) |
| p. 522 | Irrelevance of open-market operations | `gb_omo_irrelevance` |
| p. 522, fn. 22 | Fiscal backstop eliminates hyperinflations | `fb_backstop`, `fb_stationary` |
| (17.45)–(17.46), p. 523 | Tax rule, PV of surpluses, unique `P₀` (needs `B₀ > 0`) | `eq_17_45`, `eq_17_46`, `ftpl_price_level`, `ftpl_unique`, `ftpl_none` |
| pp. 523–524 | Monetary versus fiscal dominance, FTPL debate | not formalised: verbal |

## §17.4 Multiple currencies (`KarekenWallace`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 524 | Two-currency problem | `kwUtil`, `kwFeasible`, `kwOptimal`, `kwIsEquilibrium`, `kw_optimal_comm` |
| p. 524 | Low-return currency not held; a currency is valued at all dates or none | `kw_dominated`, `kw_zero_pos`, `kw_pos_zero`, `kw_structure` |
| p. 525 | Both valued ⇒ equal returns, `e` constant; problem reduces to (17.3) | `kw_structure`, `kw_e_constant`, `kw_equal_returns_util`, `kw_optimal_iff` |
| p. 525 | `e` indeterminate; one-currency equilibria (`e = 0`) | `kw_indeterminate`, `kw_unvalued` |
| p. 525 | Modified demand with transfers | `kw_modified_demand` |
| p. 526, fn. 23 | Limit `p_bM = (ω_y − γ_aω_o)/(1 + γ_a)`; `eM_a/M → 1` (Gresham); `e = 0` limit higher | `kw_limit_formula`, `kw_limit_eq_mg`, `kw_gresham`, `kw_limit_lower`; existence and convergence of the path: not formalised (proof cited to Kareken–Wallace) |
| §17.4.2, p. 526 | Lucas (1982): unique exchange rate | not formalised: verbal, no model given |
| pp. 526–527 (box) | PPP, UIP, Swiss franc | not formalised: discussion and data |
| §17.4.3, pp. 527–528 | Crypto-currency | not formalised: narrative |

## §17.5 Missing assets (`MissingAssets`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 528 | Autarky; the high agent values the bond most, others constrained | `ma_valuation_high_gt_low`, `ma_low_constrained` |
| p. 529 | `1/q = (1/β)/(π_{hi|hi} + π_{lo|hi}u′(ω_lo)/u′(ω_hi)) < 1/β` | `ma_autarky_price` |
| p. 529 | Negative autarky rate | `ma_negative_rate_iff`, `ma_negative_rate_example` |
| p. 529 | Money as the riskless asset at `q = 1`; `m = ∫g dΓ` determines `P` | `ma_price_level` (via Miao's `bw_fiat_quantity_theory`); existence of the stationary distribution not re-proved here (Miao Ch. 17, `IncompleteMarkets`) |
| p. 529, fn. 24 | Townsend turnpike; non-stationary monetary equilibria | not formalised: verbal |

## §17.6 Money as a medium of exchange

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 530–531 | Kiyotaki–Wright (1989), Lagos–Wright (2005) | not formalised: described without equations |
