# Source map: AKMM Chapter 13

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 13, Growth (T. Boppart and P. J. Klenow), pp. 369–404, and Appendix 13.A,
pp. 850–862. Page references are the draft's running heads. Lean names are relative to
`AKMM.Growth`. Departures from the book are in [corrections](corrections.md).

## §13.1–13.2 Motivation and empirical patterns (`Accounting`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 369–372, Figures 13.1–13.3, 13.A.1–13.A.4, fn. 1–2 | Long-run U.S. growth, regional and country convergence patterns, world income distribution | not formalised: empirical facts |
| p. 372, (13.1)–(13.2) | `Y/L = (K/Y)^{α/(1−α)}(H/L)A` from `Y = K^α(AH)^{1−α}` | `eq_13_2` (auxiliary `accounting_ratio_pow`) |
| p. 373, (13.3) | Growth accounting in log differences | `eq_13_3_log`, `eq_13_3` |
| pp. 373–374, Tables 13.1–13.2, fn. 3–8, Figure 13.A.5, 13.A.7 | U.S. growth accounting and 2019 development accounting | not formalised: data |

## §13.3 Neoclassical growth with investment-specific technical change (`ISTCModel`, `ISTCBGP`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 374–376, Figures 13.4–13.5, fn. 9–10 | Relative price of investment over time and across countries | not formalised: data |
| p. 376, (13.4) | Household problem with CRRA utility, budget, nPg | the budget in wealth units `istc_budget_reduced`; FOCs `eq_13_A_7`; sufficiency for the planner `istc_optimal` (household problem not separately verified, see departures) |
| p. 377 | `P_x(t) = e^{−γ_x t}/A_x` falls at rate `γ_x` | `istc_price_hasDerivAt` |
| p. 377, (13.5) and equilibrium item 3 | `P_x r = R − δP_x + Ṗ_x` ⇔ `r = RA_x e^{γ_x t} − δ − γ_x` | `eq_13_5` |
| p. 377, (13.6)–(13.7) | Firm problem | `istc_firm_optimal` (zero profits, optimality at the factor prices) |
| p. 850, (13.A.1)–(13.A.2) | Rental rate and wage as marginal products | `eq_13_A_1`, `eq_13_A_2` (auxiliary `istc_rpow_ratio`) |
| p. 850, (13.A.3) | The interest rate | `eq_13_A_3`; in per-capita wealth `istc_return_reduced`, `istc_reduced_hasDerivAt` |
| p. 850, (13.A.4)–(13.A.7), (13.9) | Hamiltonian FOCs give the Euler equation | `eq_13_A_7`; converse `istc_costate_of_euler` |
| p. 850, (13.A.6), (13.A.8), (13.10) | Budget plus asset-market clearing give capital accumulation | `eq_13_A_8`, `eq_13_10`; per-capita form `istc_output_reduced`, `istc_budget_reduced` |
| p. 851, (13.A.9)–(13.A.10) | Walras's law | `istc_walras` |
| p. 851, (13.A.11), (13.11) | Terminal condition from the TVC and asset-market clearing | `eq_13_A_11` |
| p. 851, (13.A.12) | Planner's FOCs give the same Euler equation | `istc_planner_euler` |
| p. 378, (13.8), fn. 11 | Boundedness condition (`istcBound`) ensures bounded utility | corrected: `istc_bgp_utility_integrable` (needs also `ρ > n`), counterexample `istc_bgp_utility_unbounded`; forms `istc_bound_eq`, `istc_bgp_utility_eq` |
| p. 378 | The standard candidate (`K` at rate `γ_y + n`) is not a BGP when `γ_x > 0` | `istc_standard_candidate_fails` |
| pp. 378–379 | `g_K = γ_x/(1−α) + γ_y + n`, `g_c = αγ_x/(1−α) + γ_y`; right sides of (13.9)–(13.10) constant on the BGP | `istcGK`, `istcGc`, `istc_gK_eq`, `istc_bgp_rhs_9`, `istc_bgp_rhs_10` |
| p. 379, (13.12)–(13.13) | Detrended system | `eq_13_12`, `eq_13_13` (auxiliary `istc_detrend_exp`) |
| p. 379, (13.14)–(13.15) | The unique stationary point | `istcKStar`, `istcCStar`, `eq_13_14`, `eq_13_15`, `istc_steady_pos`, `istc_steady_unique`, `istc_mpk_star`, `istcD`, `istc_D_eq`, `istc_D_pos`, `istc_D_sub_gK` |
| p. 379, fn. 13 | Detrended terminal condition, fulfilled on the BGP by (13.8) | `istc_tvc_detrended`, `istc_bgp_tvc_iff` (auxiliary `istc_exp_tendsto_zero_iff`) |
| p. 379 | Capital-augmenting change in Cobb–Douglas is labour-augmenting raised to `α/(1−α)` | `istc_labour_augmenting` |
| p. 379 | Cobb–Douglas is needed for a BGP with `γ_x > 0` (Uzawa) | not formalised: cited, no proof given |

## §13.3 Balanced-growth predictions and transitions (`ISTCPredictions`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 380, fn. 14 | `s* = α(g_K + δ)/(σg_c + γ_x + δ + ρ)`, from `c̃* = (1 − s*)k̃*^α(A_y h)^{1−α}` | `istcSStar`, `istc_footnote_14`, `istc_saving_rate_bgp` (auxiliaries `istc_cd_eq`, `istc_mpk_formula`) |
| p. 380, (13.16) | Golden-rule capital maximises (13.15) | `istcKGold`, `istcSteadyC`, `eq_13_16` |
| p. 380 | `s_gold = α` | `istc_golden_saving` |
| p. 380 | (13.8) ensures `k̃* < k̃^{gold}` | `istc_below_golden_iff` (an iff) |
| p. 380 | Wage grows at `g_c`; `r* = σg_c + ρ`; `R` falls at `γ_x` | `istc_wage_bgp`, `istc_r_star`, `istc_rental_bgp`; output `istc_output_bgp` |
| p. 380, fn. 16 | Nominal `K/Y` constant, `= s*/(g_K + δ)` | `istc_nominal_KY` |
| p. 380, fn. 17 | GDP-deflator growth `(Ṗ_x/P_x)^{s*}(Ṗ_c/P_c)^{1−s*} = −(1 − s*)γ_x` | corrected: `istc_deflator` (`−s*γ_x`), `istc_real_KY_growth`; `istc_deflator_printed_false` |
| p. 380 | Real `K/Y` grows at `(1 − s*)γ_x` | `istc_real_KY_growth` |
| p. 381 | Starting below `k̃*`, `k̃` rises to `k̃*` | for `σ = α`: `istc_closed_form_path`, `istc_closed_form_converges`; general `σ`: local, `ISTCLinear` |
| p. 381 | `σ = α`: `c̃ = k̃(δ(1−α) + γ_x(1−α) − αn + ρ)/(αA_x)` globally consistent with (13.12)–(13.13) | `istcPhi`, `istc_closed_form_rhs`, `istc_closed_form`, `istc_closed_form_rate` |
| pp. 381–382 | Open economy, aggregation (fn. 19), structural change, energy | not formalised: narrative |

## App. 13.A.3 Linearisation (`ISTCLinear`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 851, (13.A.13) | Linearised system in deviations | `istcFc`, `istcFk`, `istc_F_eq` |
| p. 851, (13.A.14) | The Jacobian at the steady state | `eq_13_A_14` |
| p. 852, (13.A.15) | Characteristic equation | `eq_13_A_15` |
| p. 852 | RHS positive, second zero positive under (13.8): one negative, one positive real root | `istc_saddle`, `istc_eigenvalues` |
| p. 852 | Explicit stable root | `istc_stable_root` |
| p. 852 | Speed `−z`, half-life `ln(1/2)/z` | `istc_half_life` |
| p. 852, fn. 21 | Calibration `n = .01`, `γ_x = .013`, `γ_y = .014`, `α = 1/3`, `σ = 1`, `ρ = .03` gives a half-life of about 5.5 years | not formalised: calibrated number (and `δ` is not stated; see corrections) |

## §13.3 Optimality (`ISTCOptimality`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 377–378, (13.4), App. 13.A.1–13.A.2 | The FOCs (13.A.4)–(13.A.7) and TVC solve the problem; the planner's system is the equilibrium system | sufficiency: `istc_optimal` (via Ch. 9's `mangasarian_catching_up`), in wealth units `istc_capital_to_wealth`; utilities `istc_crra_concave`, `istc_log_concave`; tangent bound `istc_rpow_tangent`; necessity not formalised (no Pontryagin principle in Mathlib) |
| p. 379 | The BGP from `K(0) = k̃*` is the solution | `istc_bgp_optimal` |
| p. 381 | The `σ = α` closed-form transition solves the problem from any `k̃(0)` | `istc_closed_form_optimal` |
| p. 381 | Transitions for general `σ` | not formalised globally (local saddle in `ISTCLinear`) |

## §13.4 Confronting the model with the data (`Accounting`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 382–383 | Convergence evidence, Japan, cross-country `A_x`, Table 13.A.1, fn. 21–22 | not formalised: data and narrative |
| p. 383, (13.17) | Nominal development accounting | `eq_13_17` |
| p. 383 | Nominal `K/Y` on the BGP `= α/(ασγ_x/(1−α) + γ_x + σγ_y + δ + ρ)`, independent of `h`, `A_y`, `A_x` | `istc_nominal_KY` |
| p. 383, fn. 23 | Rental-rate ratio `0.2^{−(1−α)/α}`, `= 25` at `α = 1/3` | `accounting_footnote_23`, `accounting_footnote_23_value` |
| p. 384 | `γ_y = 0.0207 − αγ_x/(1−α) = 0.014`, investment-specific share ≈ 31% | `accounting_us_decomposition` |
| p. 384, Table 13.A.2 | Nominal U.S. growth accounting | not formalised: data |

## §13.5 The AK model (`AKGrowth`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 385, (13.18) | Planner's problem; per-capita form | `ak_capital_to_percapita` |
| p. 385 | Bounded utility iff `σ(A − δ − n) > A − δ − ρ` | `ak_bounded_iff`, `ak_tvc` |
| p. 385, (13.19) | Euler equation from the Hamiltonian | `akG`, `eq_13_19` |
| p. 385, (13.20) | Transversality condition | `eq_13_20`, `ak_tvc` |
| p. 385 | Closed-form policy, `K̇/K = n + (A − δ − ρ)/σ`, no transition dynamics | `ak_policy`, optimality `ak_optimal` |
| p. 385 | Can be decentralised | `ak_decentralized` (household optimum via Ch. 9's `mangasarian_consumption_saving`) |
| p. 385, fn. 24 | The closed form of `K`; TVC forces `Ξ = 0`, so the solution is unique | `ak_footnote_24_general`, `ak_footnote_24_unique`; printed ODE lacks `/K(t)`: `ak_footnote_24_printed_false` |
| p. 385, fn. 25 | Growth decreasing in a capital-income tax | `ak_footnote_25` |
| pp. 385–386, fn. 26–28, App. 13.A.4 | Human capital, Bils–Klenow, Jones–Manuelli, Rebelo | not formalised: narrative and cited models without derivations |

## §13.5.1 Expanding varieties: decentralised equilibrium (`Romer`, `RomerDynamics`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 386, (13.21) | Aggregate production; CRS in `L_y` and machines | stated in `eq_13_23`, `eq_13_24`, `eq_13_35` (symmetric allocation, see departures) |
| p. 387, fn. 29 | Love of variety | `romer_footnote_29` |
| p. 387, (13.22)–(13.24) | Final producer's FOCs | `eq_13_23`, `eq_13_24` |
| p. 387, (13.25) | Monopolist's problem | `eq_13_33` (global optimum) |
| p. 388, (13.26)–(13.30), fn. 30–31 | R&D technology, patent value, household | used as hypotheses (`eq_13_41`–`eq_13_43`, `romer_footnote_33_tvc_fails`) |
| p. 389, (13.31) | Utility bounded/TVC iff `ρ > (1 − σ)g` | `romer_tvc_iff` |
| p. 389, (13.32) | `L_r > 0` iff `ρ < (1 − φ)ηL` | `romer_Lr_star` |
| p. 389, (13.33), fn. 32 | `x = (A(1−φ)/ψ)^{1/φ}L_y`, price `ψ/(1−φ)`, Lerner rule | `romerX`, `romerXMon`, `eq_13_33`, `romer_footnote_32` |
| p. 389, (13.34) | Profits | `eq_13_34` |
| p. 389, (13.35)–(13.36) | Output and wage | `eq_13_35`, `eq_13_36` (auxiliary `romer_X_identity`) |
| p. 390, (13.37) | Consumption | `eq_13_37` |
| p. 390, (13.38)–(13.40) | Euler; free entry; constant firm value | `eq_13_40` (Euler as hypothesis of `eq_13_43`) |
| p. 390, (13.41) | `r = η(1−φ)L_y` | `eq_13_41` |
| p. 390, (13.42) | `Ṅ/N = η(L − L_y)` | `eq_13_42` |
| p. 390, (13.43) | ODE in `L_y` | `eq_13_43` |
| p. 390, (13.44) | `L_y* = (σL + ρ/η)/(1 − φ + σ)` | `romerLyStar`, `eq_13_44` |
| p. 391, fn. 33 | Unique equilibrium path, no transitional dynamics | `romer_footnote_33_solution`, `romer_footnote_33_above`, `romer_footnote_33_below`, `romer_footnote_33_tvc_fails`, `romer_footnote_33` |
| p. 391, fn. 34 | Corner excluded by (13.32) | corrected: `romer_footnote_34`; `romer_footnote_34_printed_false` |
| p. 391 | `L_r*` | `romer_Lr_star` |
| p. 391, (13.45)–(13.46) | `r*`, `g` | `eq_13_45`, `eq_13_46` |
| p. 391 | TVC ensured by (13.31) | `romer_tvc_iff` |
| p. 391, fn. 35 | Growth decreasing in `ρ`, `σ`; increasing in `L`; `L_r*/L` increasing in `L` | `romer_comparative_statics`, `romer_research_share_mono` |
| p. 391 | Bigger countries grow faster — not in the data | not formalised: empirical |
| p. 392, (13.52) | `π*/r*` constant | `eq_13_52` |
| p. 392 | Profit taxes, a lower markup, expiring patents lower growth | `romer_theta_growth_mono`, `romer_markup_interest` (taxes and markups; patent expiry not formalised: no model given) |
| p. 853, App. 13.A.5 | Equilibrium definition; Walras | the conditions are the hypotheses above; not formalised as a separate definition |

## §13.5.1 Expanding varieties: planner and policy (`RomerPlanner`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 391, (13.47)–(13.48) | Planner's problem | `romer_planner_optimal` |
| p. 392, (13.49) | `(1 − σ)ηL < ρ < ηL` | hypotheses of `romer_planner_optimal` |
| p. 853, (13.A.16) | Static FOC; `x = (A/ψ)^{1/φ}L_y` | `eq_13_A_16` |
| p. 853, (13.A.17) | Collapsed constraint | `eq_13_A_17` |
| p. 853–854, (13.A.18)–(13.A.21) | FOCs give the Euler equation | `eq_13_A_21` |
| p. 854 | `L_y^{SP}`, `g^{SP}` | `romer_planner_Ly`, `eq_13_50` |
| p. 392, (13.50)–(13.51) | `g^{SP} = (ηL − ρ)/σ`; `x` | `eq_13_50`, `eq_13_51` |
| p. 392 | No transitional dynamics for the planner | `romer_planner_optimal` (optimal from every `N(0)`) |
| p. 392 | Machines too low by `(1−φ)^φ` | corrected: `romer_machine_ratio` (`(1−φ)^{1/φ}`), `romer_machine_ratio_printed_false` |
| p. 392 | Subsidy `1 − τ = (1−φ)^{−1}` | corrected: `romer_subsidy` (`τ = φ`) |
| p. 392 | Subsidy alone does not restore efficiency | `romer_subsidy_not_efficient` |
| p. 392 | Decentralised growth generally too low | `romer_planner_growth_gt` (always, under (13.49)) |
| p. 392 | Physical capital can be added | not formalised: no model given |

## §13.5.1 Semi-endogenous growth (`Jones`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 393, (13.53) | `Ṅ = ηN^εL_r`, population growth | hypotheses of `eq_13_56`, `eq_13_59` |
| p. 393 | `ρ − n > n/(1−ε)` bounds the household problem | `jones_r_star` (TVC) |
| p. 393 | `L_y`, `L_r` grow at `n` on a BGP | used in `eq_13_56` (`L_y = L_{y0}e^{nt}`) |
| p. 393, (13.54) | `V = π/(r* − n)` | `eq_13_54`, `jones_value_unique` |
| p. 393, (13.55) | Free entry | `eq_13_55` |
| p. 393, (13.56) | (13.55) for all `t` iff `Ṅ/N = n/(1−ε)` | `eq_13_56`, `eq_13_56_converse` |
| p. 393 | `r* = ρ + σn/(1−ε)`; TVC fulfilled | `jones_r_star` |
| p. 394 | Growth depends on `n`, `ε` only; no growth with `n = 0` | `jones_no_growth` |
| p. 394, (13.59) | Unique balanced-growth `N(t)`; `N = (η(1−ε)L_r/n)^{1/(1−ε)}` | `eq_13_59`, `jones_N_unique` |
| p. 394 | Transitional dynamics when `N` is off this level; slow if `ε` near 1 (fn. 37) | not formalised: no convergence result stated |
| p. 394, (13.60) | Output per worker; level effects | `eq_13_60`, `jones_level_effect` |
| p. 394, fn. 36, (13.57)–(13.58), App. 13.A.7 | Planner's problem and its BGP `Ṅ/N = n/(1−ε)`; growth efficient | `eq_13_A_24`, `jones_planner_lambda_growth` ((13.A.23)), `jones_planner_bgp`; `jones_planner_A25_alone_insufficient` |
| pp. 394–395 | Variety evidence | not formalised: empirical |

## §13.5.2 Quality ladders: decentralised equilibrium (`QualityLadders`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 395–398, Figures 13.6–13.11 | Business-dynamism facts (exit, reallocation, size–age, entry and exit shares) | not formalised: data |
| p. 398, (13.61) | Production with qualities; resource and research constraints | stated in `eq_13_62`, `eq_13_65`, `quality_aggregates` |
| p. 399, Figure 13.12 | Ladders `q = λ^m q_0`; Poisson innovation rate `z = ηZ/q` | `quality_single_ladder` |
| p. 400, (13.62)–(13.63) | Wage; intermediate demand | `eq_13_62`, `eq_13_63` |
| p. 400, (13.64), fn. 40 | Drastic innovations | `eq_13_64` |
| p. 400, (13.65) | Monopoly price `ψq/(1−φ)`, quantity, profit `π̄q` | `qlPiBar`, `eq_13_65` |
| p. 401 | `Y = (A/(1−φ))X^{(1−φ)/φ}QL`; `X(t) = ψ^{1−1/φ}(A(1−φ))^{1/φ}QL` | `quality_aggregates` |
| p. 401 | Research FOC `(η/q)λV = 1`; same `V/q` on all lines | `quality_research_foc`, `quality_V_over_q` |
| p. 401, fn. 41 | Arrow replacement effect | `quality_arrow_replacement` (fn. 41's extension not formalised: no model given) |
| p. 401–402 | Value of the leader, discounted at `r + z` | `quality_value` |
| p. 402 | Household Euler, TVC | the Euler equation is the hypothesis of `eq_13_66`; household optimality as in `ak_decentralized` (not separately verified) |
| p. 402 | Unique decentralised equilibrium, no transitional dynamics | not formalised: the book gives no argument (the BGP is characterised in `eq_13_66`) |
| p. 402–403 | `r* = σg* + ρ`; `V/q = 1/(λη)`; constant `z*`; `r* + z* = ληπ̄` | hypotheses and conclusion of `eq_13_66` |
| p. 403 | `Q̇/Q = E[q̇/q] = (λ−1)z*` by Uhlig's law of large numbers | departure: `Q` defined by the mean-field ODE; single-ladder expectation `quality_single_ladder` |
| p. 403, (13.66) | `g*`, `r*`, `z*` | `eq_13_66` |
| p. 403 | Growth increasing in `λ`, `η`, `L`; decreasing in `ρ`, `σ`, `ψ` | `quality_comparative_statics`, `quality_growth_mono_lambda`, `quality_growth_anti_psi` |
| p. 861, App. 13.A.9 | Quality-weighted substitutes; Bertrand; (13.A.26) | `eq_13_A_26` |
| p. 861 | Drastic iff `1/(1−φ) ≤ λ^{φ/(1−φ)}` | `eq_13_64` |
| p. 861, (13.A.27) | Limit-pricing markup | `qlMarkupProfit`, `eq_13_A_27` |

## §13.5.2 Quality ladders: planner (`QualityPlanner`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 861 | `x^{SP} = (A/ψ)^{1/φ}L > x^{DE}` | `quality_planner_static` |
| p. 862 | `X^{SP}`; `Y^{SP} > Y^{DE}`; `X^{SP} = (1−φ)Y^{SP}`; `φY = C + Z` | `quality_planner_aggregates` |
| p. 862 | `Q̇ = (λ−1)η(φY^{SP} − C)` (AK form) | hypothesis of `eq_13_A_28` |
| p. 862 | Hamiltonian with `e^{ρt}` | corrected: `quality_planner_hamiltonian_sign` |
| p. 404, p. 862, (13.A.28) | `g^{SP}`; optimal | `eq_13_A_28` |
| p. 862 | `g^{SP}` increasing in `λ`, `η`, `L`, decreasing in `ρ`, `σ` | `quality_planner_comparative_statics` |
| p. 862, reason 2 | "SP use intermediates more intensively `(1−φ)^{1/φ} > 1`" | corrected: `romer_machine_ratio` (`x^{SP}/x^{DE} = (1−φ)^{−1/φ} > 1`), `quality_planner_static` |
| p. 404, p. 862 | Three forces; `g^{SP}` could be higher or lower than `g^{DE}` | `quality_sp_vs_de_ambiguous` (both cases); the decomposition into three forces is narrative |
| p. 404 | Calibrations find `g^{SP} ≫ g^{DE}` | not formalised: cited quantitative results |

## §13.6 Conclusion

| Source | Claim | Lean |
| --- | --- | --- |
| p. 404 | Conclusion | not formalised: narrative |
