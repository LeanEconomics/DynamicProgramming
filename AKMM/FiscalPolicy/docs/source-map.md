# Source map: AKMM Chapter 15

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 15, Government and public policies (M. Azzimonti, J. Heathcote and
K. Storesletten), pp. 439–466, and Appendix 15.A, pp. 868–870. Page references are the draft's
running heads. Lean names are relative to `AKMM.FiscalPolicy`. Departures from the book are in
[corrections](corrections.md).

## §15.1 Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 439–440, Figure 15.1 | Three rationales for government; spending across countries | not formalised: narrative and data |

## §15.2 Public finance: the data and debt dynamics (`DebtDynamics`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 440–446, Figures 15.2–15.5, App. 15.A.1 | Revenues, outlays, tax categories, deficits, debt, spending by function | not formalised: data |
| (15.1), p. 441; p. 443 | `G + T + iB_{t−1} = Rev + B_t − B_{t−1}` gives `B_t = B_{t−1}(1 + i_t) + D_t` | `dd_nominal_debt` |
| p. 443 | `b_t = b_{t−1}(1 + i_t)/((1 + γ_t)(1 + π_t)) + d_t` | `dd_ratio_nominal` |
| p. 444 | `b_t = b_{t−1}(1 + r_t)/(1 + γ_t) + d_t` with `1 + r = (1 + i)/(1 + π)` | `dd_ratio_real`; constant rates via Cochrane's `debt_gdp_discrete`: `dd_ratio_const` |
| p. 444 | With `d_t = 0` the ratio rises iff `r_t > γ_t` | `dd_zero_deficit_rises_iff` |
| (15.2), p. 444 | `b_t > b_{t−1}` iff `d_t > (γ_t − r_t)b_{t−1}/(1 + γ_t)` | `eq_15_2` |
| p. 444 (box) | For `γ > r` any deficit is consistent with a stable ratio: `b* = d(1 + γ)/(γ − r)` exists, is unique and is globally stable | `ddStationary`, `dd_stationary_iff`, `dd_sub_stationary`, `dd_tendsto_stationary` |
| p. 444 (box) | When `γ − r` changes sign, a deficit makes the ratio explode | `dd_tendsto_atTop` |
| p. 444 (box) | Largest deficit at `b = 1` is about 1%; 3% deficit gives `b* = 3.09` | `dd_box_threshold`, `dd_box_309` |
| p. 444 (box) | CBO projections, actual deficits | not formalised: data |

## §15.3 Distortionary taxes: Definition 15.1 and first-order conditions (`DistortionaryTaxes`)

| Source | Claim | Lean |
| --- | --- | --- |
| (15.3), p. 446 | Resource constraint | `dtResource` |
| (15.4), p. 446 | Government budget constraint | `dtGovBudget` |
| (15.5), p. 446 | Household budget constraint | `dtBudget`, `dtFeasible` |
| p. 446 | A policy `{τ_c, τ_k, τ_ℓ, G, T}` | `DTPolicy` |
| Definition 15.1, p. 446 | Competitive equilibrium given a policy | `definition_15_1` (with `dtHHOptimal`, `dtFirmOptimal`); non-vacuity: `dt_example_ce` |
| p. 446 | Markets clear (implied by the budgets and constant returns) | `dt_resource_of_budgets` |
| (15.6), p. 446 | Household Euler equation with taxes | `eq_15_6` (from `dt_tsum_two_point`, `dt_local_max`, `dt_curve_hasDerivAt`) |
| p. 446 | Household labour condition `−u₂ = ((1 − τ_ℓ)/(1 + τ_c))wu₁` | `dt_labour_foc` |
| p. 447 | Firms: `w = f₂`, `r = f₁` | `dt_firm_foc` |
| p. 447 | Planner's Euler equation | `dt_planner_euler` (with `dtPlannerOptimal`, `dt_planner_local_max`) |
| (15.7), p. 447 | Planner's labour condition `−u₂ = f₂u₁` | `eq_15_7` |
| p. 447 | Without taxes the household's Euler equation is the planner's | `dt_no_tax_euler` |
| p. 447 | After-tax gross return `((1 + τ_{c,t})/(1 + τ_{c,t+1}))[1 + (1 − τ_k)(r − δ)]` depressed by `τ_k` and by rising `τ_c` | the factor appears in `eq_15_6`; the comparative statement is narrative and not stated separately |

## §15.3.1 Long-run distortions (`LongRun`)

| Source | Claim | Lean |
| --- | --- | --- |
| (15.8), p. 447 | Steady-state Euler equation `1 = β[1 + (1 − τ_k)(r − δ)]` | `eq_15_8` |
| (15.9), p. 448 | Steady-state labour condition | `eq_15_9` |
| (15.10), p. 448 | `w = f₂(k, ℓ)`, `r = f₁(k, ℓ)`; Cobb–Douglas partials | `lr_cd_hasDerivAt_k`, `lr_cd_hasDerivAt_l` |
| p. 448 | A higher `τ_k` raises `r` | `lrRent`, `lr_rent_iff`, `lr_rent_strictMonoOn` |
| (15.11), p. 448 | `k/ℓ = (α(1 − τ_k)/(ρ + δ(1 − τ_k)))^{1/(1−α)}`, `ρ = (1 − β)/β` | `eq_15_11` (with `lrRho`, `lrS`, `lrRatio`, `lr_s_eq`) |
| p. 448 | A higher `τ_k` lowers `k/ℓ` and `w`; `τ_ℓ`, `τ_c` do not affect `r`, `w` | `lr_s_strictAntiOn`, `lr_ratio_strictAntiOn`, `lr_wage_strictAntiOn`; `lrRent`, `lrWage` depend on `τ_k` only |
| p. 448 | Effect of `τ_ℓ` on hours ambiguous in general (income vs substitution) | narrative; GHH (no income effect) and App. 15.A.2 (offsetting effects) are formalised |
| p. 448 | GHH utility `log(c − ℓ^{1+1/φ}/(1 + 1/φ))`; consumption drops out of the hours condition | `ghhU`, `ghhV`, `ghh_partials` |
| (15.12), p. 448 | `ℓ = ((1 − τ_ℓ)/(1 + τ_c))^φw^φ` | `eq_15_12`, `ghhHours` |
| p. 448 | Hours fall with `τ_ℓ`, `τ_c`, and with `τ_k` via `w` | `lr_hours_strictAntiOn_labour`, `lr_hours_strictAntiOn_cons`, `lr_hours_strictAntiOn_capital` |

## §15.3.2 Tax incidence (`Incidence`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 449, fn. 2 | Under GHH the representative-agent steady state equals the worker–capitalist one at the aggregate level | `incSSCore`, `incRASteady`, `incWKSteady`, `inc_wk_iff_ra` |
| p. 449 | `ℓ = ((1 − τ_ℓ)/(1 + τ_c))(1 − α)(k/ℓ)^α)^φ` | `inc_hours_ratio` |
| (15.13), p. 449 | `y = (k/ℓ)^αℓ = ((1 − τ_ℓ)(1 − α)/(1 + τ_c))^φ(α(1 − τ_k)/(ρ + δ(1 − τ_k)))^{α(1+φ)/(1−α)}` | `eq_15_13`, `incOutput` |
| p. 449 | Output decreasing in each tax rate | `inc_output_lt`, `inc_output_strictAntiOn_labour`, `inc_output_strictAntiOn_cons`, `inc_output_strictAntiOn_capital` |
| p. 449 | `c_w = ((1 − τ_ℓ)/(1 + τ_c))wℓ = ((1 − τ_ℓ)/(1 + τ_c))(1 − α)y` | `inc_cw` |
| p. 449 | `c_k = ((1 − τ_k)/(1 + τ_c))(r − δ)k = (ρ/(1 + τ_c))(α(1 − τ_k)/(ρ + (1 − τ_k)δ))y` | `inc_ck`, `inc_ratio_eq` |
| p. 449 | Which taxes depress whose consumption directly and indirectly | narrative, read off `inc_cw`, `inc_ck` and the monotonicity of output |

## §15.3.2–15.3.3 Budget locus, excess cost, tax reform (`ExcessCost`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 450 | `gy = τ_ℓwℓ + τ_k(r − δ)k = τ_ℓ(1 − α)y + τ_kρα/(ρ + (1 − τ_k)δ)·y` | `inc_budget_rhs`, `incBud` |
| (15.14), p. 450 | `τ_ℓ = (g − τ_kρα/(ρ + (1 − τ_k)δ))/(1 − α)` | `eq_15_14`, `incTauL`; along it `(1 − τ_ℓ)(1 − α) = 1 − g − (ρ + δ)s`: `inc_m_eq`, `incM` |
| p. 450 | "as `τ_k → 1`, consumption of both types converges to zero" | `inc_cons_tendsto_zero` |
| p. 450, Figure 15.6 | Panels A–C: `τ_ℓ`, `c_w`, `c_k` as functions of `τ_k`; `c_k` maximal at `τ_k = 0`; `c_w` hump-shaped | figure claims, deferred (the closed forms are `incTauL`, `inc_cw`, `inc_ck`) |
| p. 450 | `c_w − ℓ^{1+1/φ}/(1 + 1/φ) = (1 − α)(1 − τ_ℓ)y/(1 + φ) = c_w/(1 + φ)` | `inc_flow_utility` |
| p. 451 | Definition of the excess cost of taxation | `incExcessCost` (with `inc_output_eq`) |
| p. 451 | "the excess cost of taxation is always positive" | `inc_excess_cost_pos`, analytic, all parameters (with `inc_core_ineq`, `inc_wage_le`, `inc_cd_tangent`, `inc_disutil_tangent`, `inc_ec_core`) |
| p. 451 | "the excess cost of taxation is increasing and convex in the capital tax rate"; p. 451 "minimized when `τ_k = 0`" | false in general: `inc_excess_cost_not_min_at_zero`; at the book's parameters not proved (Figure 15.6 only); see corrections |
| p. 451 | At `τ_k = 0.2` the excess cost is about 50 cents per dollar | not formalised: calibrated number (value ≈ 0.48 with irrational exponents) |
| p. 451 | `τ_ℓ = .2529` at `τ_k = .25`; `τ_ℓ = .2985` at `τ_k = 0` | `inc_tau_l_025`, `inc_tau_l_0` |
| pp. 451–453, fns. 3–5, Figure 15.7 | The tax-reform transition (`T − 1` Euler equations); RA vs worker–capitalist transitions differ | not formalised: numerical simulation |

## §15.3.4 The Laffer curve (`Laffer`)

| Source | Claim | Lean |
| --- | --- | --- |
| fn. 6, p. 454 | Revenue `τ_ℓ(1 − α)y + τ_kρα/(ρ + (1 − τ_k)δ)·y` with `y` from (15.13) | `lafRevenue`, `laf_bud_eq`, `laf_revenue_eq` |
| fn. 6, p. 454 | The first-order condition in `τ_ℓ` gives `τ_ℓ = (1 − τ_k(ρφ/(1 − α))α/(ρ + (1 − τ_k)δ))/(1 + φ)` | `footnote_6` (global maximiser over `τ_ℓ ≤ 1`, via `laf_amgm`, `laf_amgm_eq`) |
| p. 453 | Revenue-maximising pair with `τ_ℓ, τ_k ≥ 0` is `τ_ℓ = 1/(1 + φ)`, `τ_k = 0` | `laf_isMaxOn` (with `laf_bound`, `laf_value_at_max`, `laf_s0`) |
| fn. 6, p. 454 | "tax revenue is declining in `τ_k` at `τ_k = 0`" | global form: `laf_lt_of_pos` (every `τ_k > 0` gives strictly less than the maximum) |
| p. 454 | Higher `φ`, lower revenue-maximising labour tax | `laf_rate_strictAntiOn` |
| p. 454, Figure 15.8 | Revenue hump-shaped in `τ_ℓ`: zero at `0` and `1`; hours and output zero at `τ_ℓ = 1` | `laf_hump`, `laf_hours_zero`; the plotted curve is a figure (deferred) |

## §15.3.5 Theories of G (`TheoriesOfG`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 454 | Utility `u(c, g)` with `u₂ > 0`, `u₂₂ ≤ 0` | assumptions, not used beyond differentiability |
| p. 454 | First best: `u₁(c, g) = u₂(c, g)` | `tg_first_best` |
| p. 454 | With distortionary taxes, deadweight losses also matter | narrative |
| p. 455 | `f(k, k_g, ℓ) = Ak^αℓ^{1−α}k_g^θ`; `k_{g,t+1} = i_{g,t} + (1 − δ_g)k_{g,t}` | `tgF`, `tgLaw` |
| p. 455 | `θ > 0` gives increasing returns | `tg_homogeneous`, `tg_crs_private`, `tg_irs` |
| p. 455 | Estimates of `θ` from 0.05 to 0.39 | not formalised: empirical |
| p. 455 | With non-distortionary finance, `f_k − δ = f_g − δ_g` | `tg_net_returns_equal` (the split of a given saving between private and public capital) |

## §15.4 Ricardian equivalence (`Ricardian`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 455 | Household flow budgets; government `B₀ = T₀`, `τ₁ = (1 + r₁)B₀` | `ricFlow`, `ricBudgetSet`, `ricGov` |
| p. 455 | Present-value budget; `b₀` drops out | `ric_pv_iff` |
| p. 455 | Tax and transfer terms sum to zero | `ric_taxes_cancel` |
| p. 456 | Optimal allocation identical to that with `T₀ = τ₁ = B₀ = 0` (printed `B₁`) | `ric_budgetSet_eq`, `ric_optimal_iff` (any utility); correction 2 |
| p. 456 | Saving rises by exactly `T₀`, matching the bonds and paying the tax | `ric_saving`, `ric_market_clears` |
| p. 456 | With hours fixed: Obstfeld–Rogoff's neutrality | `ric_obstfeld_rogoff` (imports `LifeCycleFiscalPolicy`) |
| p. 456 | Extension to infinite horizon (Barro 1974); conditions (lump-sum, no credit constraints, same households) | not formalised: cited; the infinite-horizon Ricardian results are in the dependencies (`LifeCycleFiscalPolicy.RicardianEquivalence`, `NeoclassicalGrowth.rm_ricardian`) |

## §15.5–15.5.1 Ramsey taxation, the primal approach (`Ramsey`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 456–457 | Feasible and optimal tax plans; dual vs primal approach | narrative; the primal approach is formalised |
| (15.15), p. 457 | `w_t = A_t` | built into `rmCE` |
| pp. 457–458 | Household and government budgets; tax plan `(τ₀, τ₁, τ_{b,1})` | `rmCE` |
| (15.16), p. 458 | Household first-order conditions | `rmCE` (as in the book, p. 459, a competitive equilibrium is characterised by these conditions) |
| (15.17), p. 459 | Resource constraint | `rmRC` |
| (15.18), p. 459 | Lifetime budget after substituting the first-order conditions; implementability condition | `eq_15_18`, `rmIC` |
| p. 459 | Any allocation satisfying RC and IC is implementable by some tax plan (and conversely) | `rm_primal` |
| p. 459 | The government budget follows by Walras' law | `rm_walras` |
| pp. 459–460 | Lagrangian; the four first-order conditions | `rmLagrangian`, `rm_foc_c0`, `rm_foc_l0`, `rm_foc_c1`, `rm_foc_l1` (the printed expressions are the partial derivatives) |
| p. 460 | Six equations in six unknowns | narrative |
| p. 460 | Separable CRRA: `u_{cc}c = −σu_c`, `u_{ℓℓ}ℓ = u_ℓ/φ`, cross terms vanish | `rmU`, `rmUc`, `rmUl`, `rm_crra_derivs` |
| p. 460 | Simplified first-order conditions | `rm_crra_focs` |
| p. 460 | `β(1 + r)u_{c,1} = u_{c,0}` | `rm_crra_euler` |
| p. 460 | `u_{c,t}A_t(1 + µ − µσ)/(1 + µ + µ/φ) = −u_{ℓ,t}` | `rm_crra_labour` |
| p. 461 | `τ_{b,1} = 0`, `τ₀ = τ₁ = µ(σ + 1/φ)/(1 + µ + µ/φ)` | `rm_ramsey_taxes` (interiority `1 + µ + µ/φ ≠ 0`, `1 + µ − µσ ≠ 0` explicit) |
| p. 461 | The tax is positive if `g₀` or `g₁` is positive | `rm_tax_pos` (sign of `τ` = sign of the PV of spending); `µ ≠ 0` always and `µ > 0` if `1 + µ + µ/φ > 0` or `σ ≥ 1`: `rm_mu_pos` |
| p. 461 | Tax smoothing intuition (convex distortions); Chamley–Judd, Barro, Lucas–Stokey | narrative / cited |

## §15.5.2 Time consistency (`TimeConsistency`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 461 | `β(1 + r) = 1` gives `c₀ = c₁` in the Ramsey allocation | `tc_cons_equal` |
| p. 461 | `A₀ > A₁` gives `A₀ℓ₀ > A₁ℓ₁` | `tc_output_order` |
| p. 461 | The household saves in period 0 | `tc_saves` |
| p. 461 | At date 1 the planner would set `τ₁ = 0` and tax wealth income, which is then lump-sum (wealth `b₀`, printed `b₁`) | `tc_ce_on_line`, `tc_household_line`, `tc_foc_on_line`; correction 3 |
| p. 461 | The Ramsey plan is time inconsistent | `tc_time_inconsistent` (strictly worse date-1 utility when `τ₁ ≠ 0`) |
| pp. 461–462 | Debt default, political economy, commitment institutions, time-consistent policy literature | narrative / cited |

## §15.6 Debt and pensions with overlapping generations (`OLGPensions`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 462 | Young share `(1 + n)/(2 + n)` | `olg_young_share` |
| p. 462 | `p_t = (1 + n)τ_py_t` | `olg_pension` |
| p. 462 | Budget in ratios `g + (1 + r)b_{t−1}/((1 + n)(1 + γ)) = τ_t + b_t` | `olg_budget_ratio` |
| (15.19)–(15.21), p. 462 | Flow budgets and the lifetime budget | `eq_15_21` |
| (15.22), p. 463 | Euler equation | `eq_15_22`; log utility: `olg_log_consumption` |
| (15.23)–(15.24), p. 463 | Pension debt with `b_{p,t} = τ_py_t`, `1 + r_p = (1 + n)(1 + γ)` gives the same budgets | `olg_payg_eq_debt` |
| p. 463 | PV of income rises with `τ_p` iff `(1 + n)(1 + γ) > 1 + r` (printed "iff `γ + n > r`") | `olgPV`, `olg_pv_hasDerivAt`, `olg_pv_increasing_iff`; the printed approximate criterion: `olg_pv_approx_false` (correction 4) |
| p. 463 | If `r > n + γ` the pension is a tax on the young; initial old gain | `olg_payg_tax_on_young`, `olg_payg_pareto` (first component) |
| p. 463 | If `r < n + γ` introducing PAYG is Pareto improving (dynamic inefficiency) | `olgBudgetSet`, `olg_payg_pareto` |
| p. 463 | Tax holiday: `B_t = gY_t`, repaid at `t + 1` | `olg_holiday_taxes` |
| p. 463 | Holiday raises PV for generation `t`, lowers it for `t + 1`; `C_t` rises, `C_{t+2}` falls | `olg_holiday_aggregate` (log utility) |
| fn. 10, p. 463 | Effect on `C_{t+1}` ambiguous | not formalised (an ambiguity claim) |
| p. 464 (box) | US pension debt, demographics, secular stagnation | not formalised: data |

## §15.7 Taxes and transfers as instruments for redistribution (`Progressivity`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 464, Figure 15.9 | Pre- vs post-government income; average net tax rates (CBO) | not formalised: data |
| (15.25), p. 465 | `y − T(y) = λy^{1−τ}` | `hsvT`, `hsv_hasDerivAt` |
| p. 465 | `0 < τ < 1`: `T′ > T/y`; `τ < 0`: `T′ < T/y`; `τ = 0`: `T′ = T/y = 1 − λ` | `hsv_marginal_sub_average`, `eq_15_25` (progressive iff `τ > 0`) |
| pp. 465–466 | Static model: `log c − ℓ^{1+1/φ}/(1 + 1/φ)`, `c_i = λ(w_iℓ_i)^{1−τ}`, `Y = ∫c + G` | `hsvObj`; the household optimum `hsv_hours_optimal` (unique, global) |
| (15.26), p. 466 | `log ℓ_i = log(1 − τ)/(1 + 1/φ)` | `eq_15_26`, `hsvHours` |
| (15.27), p. 466 | `log c_i = log λ + (1 − τ)log(1 − τ)/(1 + 1/φ) + (1 − τ)log w_i` | `eq_15_27` |
| p. 466 | Hours fall with `τ`, independent of `w_i`, vanish as `τ → 1` | `hsv_hours_strictAntiOn`, `hsv_hours_tendsto`; `hsvHours` does not depend on `w` |
| p. 466 | `Var(log c) = (1 − τ)²Var(log w)` | `hsv_var_log_c` |
| p. 466 | Efficiency–redistribution trade-off; government budget constraint on `(τ, λ, G)` | narrative |

## Appendix 15.A (`Progressivity`)

| Source | Claim | Lean |
| --- | --- | --- |
| §15.A.1, pp. 868–869 | Data sources for Figures 15.1–15.5 | not formalised: data |
| §15.A.2, p. 869 | With `u = ln c − ℓ^{1+1/φ}/(1 + 1/φ)` and hand-to-mouth workers, `ℓ = 1` | `app_15_A_2` (global optimum), `app_15_A_2_foc` (first-order condition); correction 5 |
| §15.A.2, p. 869, Figure 15.A.1 | The tax-reform transition with wealth effects | not formalised: numerical simulation (corrections 6–7 on its description) |
