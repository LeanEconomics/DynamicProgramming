# Source map: AKMM Chapter 21

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 21, Inequality (Per Krusell and José-Víctor Ríos-Rull), pp. 627–662. The
chapter has no appendix. Page references are the draft's running heads. Lean names are relative to
`AKMM.Inequality` unless qualified. Departures from the book are in
[corrections](corrections.md).

## §21.1 Introduction and data

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 627–630 | Why inequality matters; plan of the chapter | not formalised: narrative |
| Figure 21.1, Table 21.1, Figures 21.3–21.9 | U.S. income, earnings, wealth, consumption and hours distributions; portfolios and returns; trends; skill premium | not formalised: data, facts and figures |

## §21.1 Lorenz curves, Gini coefficients and Pareto tails (`Distribution`)

The Lorenz curve and Gini coefficient are Miao's (Chapter 17, `Miao.IncompleteMarkets.ay_lorenz`,
`ay_gini`), reused.

| Source | Claim | Lean |
| --- | --- | --- |
| p. 630, Figure 21.2 | Lorenz curve: share of income of the poorest `x`%; convex, below the diagonal | `ay_lorenz` (Miao), `gi_lorenz_le_diag`, `gi_lorenz_convex` |
| p. 630 | The most extreme inequality: flat at zero, jumping to 100 | `gi_lorenz_concentrated` |
| p. 630 | Gini `= A/(A + B)` | `ay_gini` (Miao), `gi_gini_eq_ratio` |
| p. 630 | Perfect equality gives `0` | `gi_gini_equal`; converse `gi_gini_eq_zero_iff`; range `gi_gini_mem_Icc` |
| p. 630 | Tends to `1` when one agent holds all income | `gi_gini_concentrated_tendsto` |
| p. 631, fn 1 | Pareto: `1 − F(x) = (x̲/x)^α`; `log(1 − F)` linear in `log x` with slope `−α < 0` | `pa_ccdf`, `pa_log_ccdf`, `pa_log_ccdf_strictAnti` |
| pp. 630–636, fn 2–7 | Table 21.1, Figures 21.1, 21.3–21.9, Ginis 0.83/0.66/0.68 | not formalised: data |

## §21.2.1 The labor share and the capital–output ratio (`FactorShares`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 636 | Cobb–Douglas shares are `α`, `1 − α`, time-invariant | `fs_cd_capital_share` |
| p. 637 | `r k/y = A_k F₁(A_k k, A_h h) k/F = F₁(1, x)/F(1, x)`, `x = A_h h/(A_k k)`, by homogeneity | `fs_partial_homog`, `fs_capital_share_homog` |
| fn 8, p. 637 | The CES function | `fs_ces`, `fs_ces_hasDerivAt` |
| p. 637 | CES share `1/(1 + ((1 − α)/α)^{1/ρ} x^{(ρ−1)/ρ})` | `fs_ces_capital_share`, `fs_share` |
| p. 637 | `ρ > 1`: a fall in `x` raises the capital share (and the reverse for `ρ < 1`) | `fs_share_strictAntiOn`, `fs_share_strictMonoOn`, `fs_theta_pos_iff` |
| p. 637 | Investment-specific technical change, Karabarbounis–Neiman; market power, monopsony, unions | not formalised: narrative and empirical |
| p. 637 | BGP: `sy = (δ + g)k ⇒ k/y = s/(δ + g)` | `fs_bgp_ky`; the Solow steady state (Solow1956 `existsUnique_steadyState`) `fs_steady_ky` |
| fn 10, p. 637 | Piketty's "second fundamental law" | not formalised: cited |
| p. 638 | `k/F(k, h)` increasing in `k`; `k/y` rises (falls) toward its steady state from below (above) | `fs_ky_strictMonoOn`, `fs_ky_below`, `fs_ky_above` |
| p. 638 | Broad wealth, land, housing, firm values | not formalised: narrative |

## §21.2.2 Wage inequality (`WageInequality`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 638 | Relative wage `w_s/w_u = F_s/F_u`; under `F(k, G(A_u u, A_s s))`, `k` does not affect relative wages | `km_premium_eq` (the premium involves only `G`) |
| p. 639 | `log(w_s/w_u) = −(1/ρ)log(s/u) + ((ρ − 1)/ρ)log(A_s/A_u) + c` | `wi_ces_hasDerivAt`, `fs_ces_symm`, `km_premium`, `km_premium_eq`, `km_log_premium` |
| p. 639 | The premium falls with relative supply | `km_premium_strictAnti_supply` |
| p. 639 | SBTC raises the premium iff `ρ > 1`; Cobb–Douglas: no effect | `km_sbtc_strictMono_iff`, `km_cd_premium` |
| p. 639 | Regression `log(w_s/w_u) = −β₁log(s/u) + β₂t + c`; `β̂₁` gives `ρ`, then `β̂₂` gives `γ` | `km_identify` |
| p. 639, fn 13–14 | CPS data, `ρ ≈ 1.4`, 10% per year | not formalised: empirical |
| p. 640 | Directed technology problem | `dt_obj`, `dt_con` |
| p. 640 | First-order condition `A_s/A_u = (λ/(1 − λ))(s/u)^{σ/(φ−σ)}` | corrected: `dt_ratio`, `dt_term_le`, `dt_optimal`, `dt_foc_iff_ratio`, `dt_exists`, `dt_maximiser_ratio`; printed form `dt_printed_ratio_iff` (corrections 1) |
| p. 640 | `σ ∈ (0, 1)`: higher `s/u` attracts R&D | `dt_ratio_strictMono` |
| p. 640 | `log(w_s/w_u) ∝ ((σ − φ(1 − σ))/(φ − σ)) log(s/u)` | `dt_wage_ratio`, `dt_premium_closed`, `dt_log_premium` |
| p. 640 | Increasing in `s/u` iff `ρ − 1 = σ/(1 − σ) > φ`; then `ρ > 2` | `dt_exponent_pos_iff`, `dt_rho_gt_two` |
| p. 641 | `F = u + s^ν k^{1−ν}`: `k` raises `w_s`, `w_u = 1` | `cs_ex1_wages`, `cs_ex1_premium_strictMono` |
| p. 641 | Both nests CES: the premium rises with `k` iff the elasticity in `F` exceeds that in `G` | `cs_ces_nest_premium`, `cs_ces_nest_strictMono` |
| p. 641 | `F(s, G(k, u))`, e.g. `s^ν(k + u)^{1−ν}`: `w_u` can fall with `k` | `cs_ex2_wu`, `cs_ex2_wu_strictAnti` |
| p. 641 | This cannot happen under `F(u, G(k, s))` | `cs_nest_wu`, `cs_nest_wu_monotone` |
| fn 16, p. 641; Greenwood–Yorukoglu | Estimated elasticities; human capital and adaptation | not formalised: empirical and cited |
| pp. 641–644 | Human capital (Roy, Mincer, Ben-Porath), task-based models, search frictions, compensating differentials, monopsony and unions | not formalised: cited models and narrative without derivations |

## §21.2.3 Wealth inequality: deterministic models (`Dynastic`, `Distortions`)

Consumer `i`'s problem is Chapter 11's deterministic problem (11.12) (`AKMM.Consumption.cd_Optimal`)
with `Aₜ = (1 + r − δ)aₜ` and income `εᵢw` (`dy_Optimal`, `dy_plan_iff`); necessity and
sufficiency of the Euler equation are Chapter 11's `eq_11_13` and `cd_optimal_of_euler`.

| Source | Claim | Lean |
| --- | --- | --- |
| p. 644, fn 20 | Steady states only; out-of-steady-state dynamics | not formalised: scope remark |
| p. 645, fn 21 | The dynastic problem with no-Ponzi condition | `dy_Optimal`, `dy_plan_iff` |
| p. 645 | `β(1 + r − δ) = 1` makes constant consumption optimal | `dy_constant_optimal` |
| p. 645 | Any wealth distribution with `cᵢ = (r − δ)aᵢ + εᵢw ≥ 0` is a steady state | `dy_indeterminacy` (with `cᵢ > 0`), `dy_indeterminacy_example`, `dy_log_tangent` |
| p. 645 | Marginal propensity `r − δ` | `dy_mpc` |
| pp. 645–646, fn 22 | Fully insurable idiosyncratic shocks: indeterminacy again; Chatterjee (1994) | not formalised: verbal, cited |
| p. 646 | OLG without bequests: determinate distribution | not formalised: verbal |
| p. 646 | Altruistic Bellman equation and budget | `ol_budget_iff` |
| p. 646 | `u(R) = max U(c_y, c_o)` s.t. `c_y + c_o/(1 + r − δ) = R` | `ol_IsIndirect`, `ol_isIndirect_prod` (instance) |
| p. 646 | The altruistic problem is the dynastic problem with `ε̂ = ε_y + ε_o/(1 + r − δ)` | `ol_bellman_reduction`, `ol_dynastic_utility` (Obstfeld–Rogoff `utility_eq_tsum_iff`) |
| p. 646 | Steady-state wealth distribution indeterminate | `ol_indeterminacy`, `ol_example` |
| pp. 646–647, fn 23 | Warm glow; non-standard, welfare theorems fail; relative curvature of `V̂` | not formalised: verbal |
| p. 647 | Heterogeneous `βᵢ`: the most patient has constant consumption, `β_{i*}(1 + r − δ) = 1` | `hd_constant_beta`, `hd_unique_beta`, `hd_strictMono` |
| p. 647 | Other consumers' consumption converges to zero | `hd_strictAnti`, `hd_tendsto_zero` |
| p. 647 | Their wealth satisfies `0 = (r − δ)aᵢ + εᵢw` in the limit | `hd_assets_limit` |
| p. 647, fn 24 | Inequality is chosen; large number of each type | not formalised: verbal |
| p. 647 | Progressive tax: gross capital income `a(1 + (r − δ)(1 − τ(a)))` | `pt_gross` |
| fn 25, p. 648 | Gross return `1 + (r − δ)(1 − τ(a) − τ′(a)/a)` | corrected: `pt_hasDerivAt`; printed form `pt_printed_iff`, `pt_printed_counterexample` (corrections 2) |
| fn 25, p. 648 | In steady state `β` times the return equals 1 | `pt_steady_euler`, `pt_steady_euler_example` |
| pp. 647–648 | `τ′ > 0` increasing ⇒ the Euler equation cannot hold for different `a`; `aᵢ = aᵢ′` | `pt_g_strictMonoOn`, `pt_unique`, `pt_equal_wealth` (savers, `a ≥ 0`: departures 4) |
| p. 648 | Proportional taxes do not act differentially | `pt_proportional` |
| p. 648 | Hubmer et al. (2018), Reagan's tax cuts | not formalised: empirical |
| p. 648 | Two agents, alternating endowments: `q = β`, full smoothing | `ta_q_eq_beta` |
| fn 26, p. 648 | With `a₀ = 0`, A is richer and consumes more forever | `ta_endow`, `ta_assets`, `ta_footnote_26`, `ta_footnote_26_richer` |
| p. 648 | Binding limit `a`: `qu′(ȳ + a(1 + q)) = βu′(y − a(1 + q))`, one equation in one unknown | `ta_binding_alloc`, `ta_binding_kkt`, `ta_h`, `ta_binding_strictMono`, `ta_binding_unique`, `ta_binding_exists` |
| p. 648 | "consumers are worse off" | not formalised: verbal welfare remark |
| fn 27, p. 648 | First-period rate differs with `a₀ = 0` | not formalised: remark without derivation |
| p. 648 | Investment loans vs consumption loans | not formalised: verbal |
| p. 649 | Permanently different returns `rᵢ`: the highest-return agent holds all capital, others' consumption vanishes | `rh_lower_return_iff` with `hd_tendsto_zero`, `hd_assets_limit` (applied with `R = Rᵢ`) |
| p. 649, fn 28 | Closing the model with `Σrᵢaᵢ = r̄Σaᵢ` | not formalised: verbal |
| p. 649 | Quadrini (2000) entrepreneurs | not formalised: cited |

## §21.2.3 Wealth inequality: uninsurable shocks, random growth, quantitative models, welfare (`Uninsurable`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 650, fn 29 | Imrohoroğlu (1989), Aiyagari (1994), Huggett (1993) | not formalised: cited |
| p. 650 | Uninsurable shocks make the steady-state wealth distribution determinate | `ui_determinate` (Miao's Proposition 8.3.1, `SIModel.Solution.proposition_8_3_1`: i.i.d. income, `βR < 1`); contrast `dy_indeterminacy_example` |
| p. 650 | Huggett budget `cₜ + qₜaₜ₊₁ = εₜ + aₜ`, `aₜ₊₁ ≥ a`; assets sum to zero | `hu_autarky_clearing` (zero net supply) |
| p. 650 | Mean-reverting `ε`: some borrow, some lend | not formalised: verbal |
| p. 650 (AKMM §17.4.4) | `a = 0`: autarky, rate in closed form from the unconstrained agent's Euler equation | `hu_autarky_clearing`, `hu_value`, `hu_qstar`, `hu_kkt_iff`, `hu_price_iff` (departures 8) |
| p. 650 | The risk-free rate is below the discount rate | `hu_rate_below_discount` (autarky); Huggett in general: Chapter 11's `hg_rate_below_cm` |
| p. 650 | Unequal wealth reflects risk sharing; natural limit gives the most inequality; the interest rate is key | not formalised: verbal |
| p. 650 | Aiyagari: more risk or risk aversion raises steady-state capital | not formalised: cited (Chapter 11) |
| pp. 650–651 | AR(1) earnings under-predict top wealth; Castañeda et al. (2003) | not formalised: quantitative |
| p. 651, fn 30 | Random discount factors and returns spread the distribution; time-consistent random discounting | not formalised: verbal |
| p. 651 | Kesten: `aₜ₊₁ = sₜaₜ + εₜ` has a Pareto right tail `P(A > a) ∝ a^{−ζ}` | not formalised: Kesten–Goldie implicit renewal theorem, beyond the text (decision 5); see corrections 3 |
| fn 31, p. 651 | `ζ > 0` with `E s^ζ = 1` | special case: for finitely supported `s > 0` with `E log s < 0` and `P(s > 1) > 0` the root exists and is unique: `ke_moment`, `ke_moment_zero`, `ke_moment_hasDerivAt`, `ke_moment_exists`, `ke_moment_unique` |
| pp. 651–652, fn 32–33 | CRRA saving is approximately linear at high wealth (Hubmer et al.); Pareto earnings give Pareto wealth | not formalised: cited |
| p. 652 | Welfare: random discount factors versus random returns | not formalised: verbal |
| p. 652 | Hours worked, Domeij–Floden, Pijoan-Mas | not formalised: verbal |
| pp. 652–653 | Why are so many so poor; consumption floors, informal sharing, garnishment | not formalised: verbal |
| pp. 653–654 | Quantitative analysis: Ginis 0.37/0.67, MPCs 0.17/0.78, superstar, stochastic `β`, random returns | not formalised: calibrated and quantitative results |
| pp. 654–655, fn 35–41 | Welfare comparisons: transitions, social welfare functions, veil of ignorance, contracts, Lucas critique | not formalised: narrative (fn 35 is Chapter 6's golden-rule comparison) |

## §21.3 Reasons why inequality matters for aggregates (`Channels`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 656–657, fn 42–43 | Incentives, redistribution, innovation | not formalised: narrative |
| p. 657 | Education with fixed cost `F`, no borrowing: educate iff `W ≥ F` and `w_s − w_u > F` | `ed_educates`, `ed_educates_example`, `ed_unconstrained` |
| p. 657 | Fraction educated = fraction with wealth above `F`; the wealth distribution matters | `ed_fraction`, `ed_wealth_matters` |
| p. 657, fn 44 | Trapped dynasties, development traps, Galor–Tsiddon | not formalised: verbal, no model given |
| p. 658 | Borrowing-constrained consumers have MPC `1` (Figure 21.10) | `mpc_binding` |
| pp. 658–659 | TANK: shares chosen to give an aggregate MPC of, say, 0.5 | `tank_mpc` |
| pp. 658–660, fn 45–48 | Computational approaches (Krusell–Smith, sequence space), linearity and certainty equivalence, wealthy hand-to-mouth | not formalised: computation and narrative |
| p. 660 | `y = Âₜkₜ^α`, `Âₜ = Aₜcₜ^ω`: output demand-determined; with `ω = 0` a 1% TFP shock moves output 1% | `ext_log_output` |
| p. 660, Figure 21.11 | Impact responses (0.3%, 1.1%) | not formalised: figure claim, deferred (simulation) |
| pp. 660–662 | Policy targeting high-MPC households; distributional welfare | not formalised: narrative |
