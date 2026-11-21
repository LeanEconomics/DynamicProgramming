# Source map: AKMM Chapter 6

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 6, Welfare, pp. 159–186, and Appendix 6.A, pp. 838–839. Page references
are the draft's running heads. Lean names are relative to `AKMM.Welfare`. Departures from the book
are in [corrections](corrections.md).

Reused from dependencies. AKMM `CompetitiveEquilibrium` (`AKMM.CompetitiveEquilibrium`): the
date-0 problem `ADBudget`, `ADOptimal`, `ad_foc_multiplier`, `ad_foc_sufficient`,
`ce_tsum_perturb`, `ce_log_tangent`; the OG sequential equilibrium `IsOGEndowEquilibrium`,
`OGSavingOpt`, `og_autarky`; the Arrow–Debreu prices `seqPrice`, `seqPrice_succ`,
`seqPrice_pos`. Miao `OverlappingGenerations` (`Miao.OverlappingGenerations`):
`op_concave_tangent`, `op_strictConcave_tangent` and `op_cass_steady_state`. SLP
`ParetoOptimaEquilibria` and Miao `CompleteMarkets` are not used: SLP's Theorem 15.3 has no
endowments or ownership shares and uses utility functions on a normed space with equality
feasibility, Miao's Theorem 13.3.1 lives on an event tree; the book's Theorem 6.1 (preference
relations, endowments, shares, inequality feasibility) and its dynastic and OG versions are proved
directly in the book's setting. The Second Welfare Theorem, which the book mentions but does not
state, is SLP's `theorem_15_4` and Miao's `theorem_13_3_2`.

## Introduction and §6.1, the First Welfare Theorem (pp. 159–164) — `FirstWelfare`, `Dynastic`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 159–160 | Invisible hand, Pareto optimality as a minimal criterion | not formalised: narrative |
| (6.1), p. 160 | Feasibility `Σ xᵢ ≤ Σ yⱼ + Σ ωᵢ` | `fwFeasible` |
| p. 160 | Consumption sets, preference orderings, production sets, shares `Σᵢ θᵢⱼ = 1` | `fwFeasible`, `fwStrict`, hypotheses of `theorem_6_1` |
| p. 160, fn. 2 | Local nonsatiation | `fwLNS` |
| p. 160–161 | Competitive equilibrium (1)–(3) | `fwCompEq` (`fwCompEqT` with transfers) |
| p. 161 | Pareto optimality | `fwParetoOptimal` |
| p. 161, proof | `px̃ᵢ ≥ px⋆ᵢ` by LNS, `px̃ĩ > px⋆ĩ` | `fw_value_ge`, `fw_value_gt`, `fw_value_sum` |
| Theorem 6.1, p. 161 | First Welfare Theorem | `theorem_6_1` (needs `p ≥ 0`: corrections, item 1); `theorem_6_1_counterexample`, `fw_price_nonneg`; instance `theorem_6_1_instance` |
| p. 162 | Static model `x ∈ ℝ³₊`, prices `(1, r, w)`; leisure, intermediate goods | not formalised: mapping narrative (covered by `theorem_6_1` with `G` the goods) |
| p. 162 | Endowment economies: `Yⱼ = {0}` | `theorem_6_1` with `Y = {0}`, `theorem_6_1_instance` |
| p. 162 | `T < ∞` dates: more goods | `theorem_6_1` with `G` = goods × dates |
| p. 162 | Infinite horizon: FWT when the value `p · x` is finite | `fwt_dynastic`, `dy_value_summable`, `dy_lns`, `dyCompEq`, `dyFeasible`, `dyParetoOptimal` |
| pp. 162–164, Fig. 6.1 | Edgeworth-box intuition, marginal rates | not formalised: figure and narrative |

## §6.2, tracing out the Pareto frontier (pp. 164–167) — `Dynastic`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 164 | Planner solutions are Pareto optimal | `negishi_planner_pareto`, `dyPlannerOptimal` |
| p. 165 | Lagrangian, `βᵗu′(c_{i,t}) = λᵢpₜ` | `eq_6_2` (via Chapter 5's `ad_foc_multiplier`) |
| (6.2), p. 165 | `c_{i,t} = (u′)⁻¹(β^{−t}λᵢpₜ)` | `eq_6_2` |
| p. 166 | Planner FOC `µᵢβᵗu′(c_{i,t}) = ψₜ` | `dy_planner_foc` |
| (6.3), p. 166 | `c_{i,t} = (u′)⁻¹(β^{−t}ψₜ/µᵢ)` | `eq_6_3` |
| p. 166 | Same allocation for `µᵢ = 1/λᵢ`, `ψₜ = pₜ` | `negishi_coincide` |
| p. 166 | Clearing forces `ψₜ = pₜ` | `negishi_psi_eq_p` |
| p. 166 | The CE is optimal for the planner with Negishi weights, hence Pareto optimal | `negishi_ce_solves_planner`, `negishi_fwt` |
| p. 166 | Varying the weights traces out the frontier | `negishi_planner_pareto` (every weight vector) |
| p. 166 | Second Welfare Theorem | not formalised: mentioned, not stated (SLP `theorem_15_4`, Miao `theorem_13_3_2`) |
| pp. 166–167 | Interpretation of weights | not formalised: narrative |

## §6.3.1, taxes (pp. 167–168) — `FirstWelfare`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 167, fn. 3 | Lump-sum taxes keep equilibria optimal | `fwt_lump_sum` |
| p. 167 | Proportional labour tax with inelastic labour acts as a lump-sum tax | `tax_inelastic_labour` |
| p. 167 | With valued leisure the MRS differs from the MRT by `1 − τ` | `tax_labour_wedge` |
| pp. 167–168, fn. 4 | Capital tax in the Euler equation; where the proof fails | not formalised: narrative (the wedge is the same algebra as `tax_labour_wedge`) |

## §6.3.2, externalities (pp. 168–169) — `Externality`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 168 | Consumer and firm conditions | hypotheses of `ext_equilibrium_hours` |
| p. 169 | Equilibrium hours `1 − α = Bℓ^{1+1/θ}`, unique, independent of `A` | `ext_equilibrium_hours`, `ext_equilibrium_hours_unique` |
| p. 169 | Planner FOCs and `(1 − α)/(1 − A′k^αℓ^{1−α}) = Bℓ^{1+1/θ}` | `ext_planner_hours` |
| p. 169 | Not optimal unless `A′ = 0` | `ext_not_optimal`; too much work if `A′ < 0`: `ext_overwork` |
| fn. 5, fn. 6 | Income and substitution effects; own-TFP effect | not formalised: remarks |
| fn. 7, p. 169 | Profits positive and unbounded when others produce less | `ext_fn7` |
| p. 169 | Endogenous production sets; climate | not formalised: narrative |

## §6.3.3, borrowing constraints (pp. 170–171) — `Borrowing`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 170 | Endowments alternate `2ω/3`, `ω/3` | `brEndow`, `brEndow_spec` |
| p. 170 | Unrestricted CE: `pₜ = βᵗ`, gross rate `1/β`, `c₁`, `c₂` | `borrow_unrestricted`, `brCons_spec`, `borrow_endow_value` |
| p. 170 | Problem with `a_{t+1} ≥ 0` | `nbCons`, `nbFeasible`, `nbOptimal`, `nbEquilibrium` |
| pp. 170–171 | Kuhn–Tucker: `qₜu′(cₜ) ≥ βu′(c_{t+1})` | `borrow_euler_ineq` (necessity), `borrow_autarky_optimal` (sufficiency) |
| p. 171, fn. 8 | No borrowing means autarky | `borrow_autarky` |
| p. 171, fn. 9 | `qₜ = 2β`, and `qₜ > 2β` also equilibria | `borrow_equilibrium_iff`, `borrow_endow_log_summable` |
| p. 171 | Lower rate than unrestricted; negative iff `β > 1/2` | `borrow_interest_rate` |
| p. 171 | The allocation is not optimal | `borrow_autarky_not_optimal` |
| p. 171 | Consumption possibility set | `borrow_possibility_set` (corrected), `borrow_possibility_set_printed_counterexample` |
| p. 171 | Pecuniary externalities | not formalised: narrative |

## §6.3.4, lack of commitment (p. 172)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 172 | Default, punishment, forward references | not formalised: narrative |

## §6.3.5, market power (pp. 172–175) — `MarketPower`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 173 | CES utility, budget | the measure `μ` on goods, `∫ c^{1−1/ε}` |
| (6.4), p. 173 | The two forms of the FOC | `eq_6_4`, `ds_rpow_ratio` |
| p. 173 | `∫ p(i)c(i) di = λC` | `ds_expenditure` |
| p. 173 | `P = λ = (∫ p^{1−ε})^{1/(1−ε)}`, homogeneous of degree one | `ds_price_index`, `ds_price_index_homogeneous`; "increasing in all prices" not formalised (remark) |
| p. 174 | Demand `c(i) = C(p(i)/P)^{−ε}` | `ds_demand` |
| p. 174 | Monopolistically competitive equilibrium (definition) | formalised through its conditions: `dsProfit`, `ds_revenue`, `ds_symmetric_wage`, `ds_equilibrium_condition` |
| pp. 174–175 | Firm optimum for `ε > 1`, markup `µ = ε/(ε − 1)`, profits `(µ − 1)(w/A)c` | `ds_firm_optimum` |
| fn. 10 | No optimum for `ε < 1` (unbounded) and `ε = 1` (supremum = revenue) | `ds_no_max_lt_one`, `ds_no_max_eq_one` |
| p. 175 | Symmetry, `P = 1`, `w = A(1 − 1/ε)` | `ds_symmetric_wage` |
| p. 175 | `A(1 − 1/ε) = Cv′(C/A)`, unique for convex `v` | `ds_equilibrium_condition`, `ds_rhs_strictMono`, `ds_unique` |
| p. 175 | Planner `A = Cv′(C/A)`; output and hours too low | `ds_planner_foc`, `ds_underproduction` |

## §6.3.6, quantifying welfare losses (pp. 175–176) — `WelfareMeasures`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 176 | `u(c_l, ℓ_l) > u(c_d, ℓ_d)` | not formalised: depends on the unspecified tax economies |
| p. 176 | A `∆ > 0` with `u(c_l(1 − ∆), ℓ_l) = u(c_d, ℓ_d)` exists | `welfare_cev_static` (unique in `(0, 1)`) |
| p. 176 | Alternative definitions of `∆` | not formalised: remarks |
| p. 176 | Dynamic `∆`: unique uniform percentage cut | `welfare_cev_dynamic_log` (log utility; corrections, item 13) |

## §6.4.1, OG endowment economy (pp. 176–180) — `OGEndowment`, `BalaskoShell`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 177 | Sequential equilibrium | Chapter 5's `IsOGEndowEquilibrium 0 Real.log 1` |
| (6.5)–(6.6), p. 177 | Young's optimum; saving `(ω_y − qₜω_o)/2` | `eq_6_5_6_6`, `og_log_consumption` |
| p. 177 | Unique equilibrium: autarky, `qₜ = ω_y/ω_o` | `og_log_equilibrium_iff` |
| p. 178 | `(3, 1)`: `q = 3`, net rate `−67%`, `(2, 2)` dominates | `og_example_3_1`, `og_stationary_improvement` |
| p. 178 | `(1, 3)`: `q = 1/3`, `(2, 2)` hurts the initial old, no improvement exists | `og_example_1_3` |
| p. 178 | The proof of the FWT goes through when the present value is finite | `og_fwt_value` (`pₜω_{y,t} → 0`), `og_fwt_finite_value`, `ogADEquilibrium`, `og_ad_of_seq`, `ogFeasible`, `ogDominates`, `ogParetoOptimal` |
| pp. 178–179 | Balasko–Shell: optimal iff `Σ 1/pₜ = ∞` | `BalaskoShell`: general theorem `bs_balasko_shell` under the curvature conditions `bsCurvBelow` (not linear) and `bsCurvAbove` (not kinked); sufficiency `bs_sufficiency`, necessity `bs_necessity` with the explicit transfers `bsTransfer`, `bs_necessity_transfers`; instances: log utility, endowments in `[m, M]` (`bs_log_curv_below`, `bs_log_curv_above`, `bs_log_ad`, `bs_log`, `bs_log_equilibrium`), CRRA (`bsCRRA`, `bsCRRAU`, `bsCRRAPrice`, `bs_crra_equilibrium`, `bs_crra_curv_below`, `bs_crra_curv_above`, `bs_crra`, with `bs_crra_mono`, `bs_crra_tangent`, `bs_crra_hasDerivAt`, `bs_quad_upper`, `bs_quad_lower`, `bs_rpow_gap_lower`, `bs_rpow_gap_upper`, `bs_mono_of_deriv`); the stationary case `og_balasko_shell_stationary_log` (with `og_stationary_ad`, `og_seqPrice_const`, `og_logU_mono`) recovered as `bs_stationary_log` (corrections, item 15) |
| p. 179 | `Σ 3^{−t} = 3/2`, `Σ 3ᵗ = ∞`, `Σ 1 = ∞` | `og_balasko_shell_sums` |
| p. 179 | `(2, 2)` is optimal although the proof cannot be used | `og_example_2_2`, `og_equal_endowments_optimal` |
| p. 179 | Optimal iff limit net rate `≥ 0` | false: `og_limit_rate_one_counterexample`; corrected `og_limit_rate_gt_one`, `og_limit_rate_lt_one_log` (corrections, item 3) |
| fn. 11 | With growth `g`: optimal iff limit rate `≥ g` | not formalised (growing economy; same boundary problem) |
| p. 179 | Finite horizon: no inefficiency | `theorem_6_1` (a finite economy) |
| p. 179 | Pay-as-you-go transfers improve suboptimal equilibria; stopping hurts | `og_stationary_improvement`, `og_limit_rate_lt_one_log`; `og_finite_transfers_hurt` |
| pp. 179–180, Figs. 6.2–6.3 | Stationary and non-stationary alternatives to `(2, 2)`, growing transfers | `og_equal_endowments_optimal` |
| p. 180 | Gross rate above one: "even harder" | `og_fwt_value` (`og_example_1_3`) |
| p. 176 | Random death and new entrants | not formalised: remark |

## §6.4.2, intertemporal production (pp. 180–183) — `OGProduction`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 180–181 | Storage with return `χ`; saving iff `χ > 1/3` | `storage_saving` (at `q = 1/χ`; corrections, item 4), `storage_printed_counterexample` |
| p. 181 | Equilibrium autarky with active storage | `stEqAlloc`, `stEqAlloc_feasible`, `stFeasible`, `stParetoOptimal` |
| p. 181 | Optimal iff `χ > 1`; `χ = 1` improved by social security | `storage_optimal_iff`, `storage_optimal`, `storage_not_optimal` |
| p. 181 | Balasko–Shell on the storage allocation as a new endowment | not formalised: remark (superseded by `storage_optimal_iff`) |
| pp. 181–182 | Budgets, `sₜ = h(wₜ, r_{t+1}, w_{t+1})`, law of motion | `diamond_law_of_motion` (the saving function itself: Chapter 5's `IsOGGrowthEquilibrium`) |
| Theorem 6.2, p. 182, fn. 12 | Cass (1972): efficient iff `Σₜ ∏_{s=1}^t R_s = ∞` | `theorem_6_2`, `theorem_6_2_efficient`, `theorem_6_2_inefficient`, `dePath`, `deCons`, `deEfficient`; instances `theorem_6_2_instance_efficient`, `theorem_6_2_instance_inefficient`, `de_quadratic_expansion` (corrections, item 10) |
| p. 182 | `∏_{s=1}^t R_s = 1/pₜ` | `theorem_6_2_prices` |
| p. 182, fn. 13 | Steady state efficient iff `R ≥ 1`; growth version | `theorem_A5`, `theorem_A5_cass`; growth version not formalised |
| pp. 182–183, fn. 14 | Reducing saving: the two cases | `theorem_A5_inefficient`, `theorem_A5_efficient` |
| p. 183 | Conclusion: asymptotic net rate non-negative | see corrections, item 3 |

## §6.4.3, the warm-glow model (p. 183) — `WarmGlow`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 183 | `u′(c̄) = A` | `warmglow_consumption` |
| p. 183 | `k_{t+1} = (1 − δ)kₜ + F(kₜ, 1) − c̄` | `warmglow_law_of_motion`, `warmglow_steady_iff` |
| p. 183 | Two positive steady states | `warmglow_two_steady_states`, `warmglow_sign` (needs `c̄ < max φ`: corrections, item 7), `warmglow_no_steady_state`, `warmglow_instance` |
| p. 183 | Lower unstable, upper stable; convergence from high `k₀` | `warmglow_stable`, `warmglow_lower_unstable`, `warmglow_slopes` |
| p. 183 | Slope `1 + F₁ − δ < 1` at `k̄`; dynamically inefficient | `warmglow_slopes`, `warmglow_inefficient` |
| fn. 15 | Pareto welfare with warm glow | not formalised: remark |

## §6.5, optimal government policy (pp. 184–186) — `WelfareMeasures`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 184 | Ramsey analysis, Pigou, Coase, antitrust, patents | not formalised: narrative |
| §6.5.1, pp. 184–185 | Transfers in the borrowing example; the "chicken model" | `borrow_autarky_not_optimal` (the transfer to the unrestricted allocation); the rest narrative |
| §6.5.2, pp. 185–186 | Utilitarian weights; veil of ignorance gives `c_A = c_B` | `veil_equal_split`, `veil_optimum_equal` |

## Appendix 6.A (pp. 838–839) — `OGProduction`, `GoldenRule`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 838 | `f(k) = F(k, ω_y + ω_o) + 1 − δ` | corrected to `+ (1 − δ)k`: `appendix_6A_printed_f` (corrections, item 5) |
| Theorem .5, p. 838 | Steady state efficient iff `f′(k⋆) ≥ 1` | `theorem_A5` |
| p. 838, (i) | `R⋆ < 1`: permanent increase in consumption | `theorem_A5_inefficient` |
| p. 839, (ii) | `R⋆ ≥ 1`: deficits grow, `c_∞ < c⋆` | `theorem_A5_efficient` (corrections, item 6) |
| Fig. .1 | `c⋆ = f(k⋆) − k⋆` peaks at the golden rule `k^G`; efficient (`f′ ≥ 1`) left of `k^G`, inefficient (`f′ < 1`) right | `GoldenRule`: `figure_A1` (`goldenrule_max`, `goldenrule_increasing`, `goldenrule_decreasing`, `goldenrule_slope`, `goldenrule_slope_iff`, `goldenrule_efficient_iff`); instance `figure_A1_instance`, `figure_A1_instance_regions` (corrections, item 16) |
