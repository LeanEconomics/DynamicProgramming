# Source map: AKMM Chapter 12

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 12, Labor supply (R. Rogerson and G. L. Violante), pp. 325–367, and
Appendix 12.A, p. 849. Page references are the draft's running heads. Lean names are relative to
`AKMM.LaborSupply`. Departures from the book are in [corrections](corrections.md).

## §12.1–12.2 Introduction and facts

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 325–331, Tables 12.1–12.3, Figures 12.1–12.5 | Hours across countries, over time, across groups; intensive/extensive decompositions | not formalised: empirical facts |

## §12.3.1 The benchmark static model (`Static`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 332 | `U = u(c) − v(ℓ)`, `u = c^{1−σ}/(1 − σ)`, `v = ψℓ^{1+1/γ}/(1 + 1/γ)`; budget `c = wℓ + I` | `crraU`, `disutil`, `stObj`; derivatives `st_crraU_hasDerivAt`, `st_disutil_hasDerivAt`, `st_obj_hasDerivAt` |
| p. 332 | "the individual will always choose `ℓ > 0`" | `eq_12_1` (unique interior maximiser; beats `ℓ = 0` when `I > 0`) |
| p. 332, (12.1) | `ψℓ^{1/γ}/(wℓ + I)^{−σ} = w` | `eq_12_1`, `st_foc_form`, `st_foc_strictMono`, `st_deriv_factor` |
| p. 333 | Implicit differentiation of (12.1) | `st_path_identity`, `st_path_poly` (departure: differentiability of `ℓ` assumed, see corrections) |
| p. 333, (12.2) | `ε_{ℓ,I} = −σs_I/(1/γ + σ(1 − s_I))` | `eq_12_2` |
| p. 333, (12.3) | `ε^M = (1 − σ(1 − s_I))/(1/γ + σ(1 − s_I))` | `eq_12_3` |
| p. 333 | Income elasticity negative when `s_I > 0` | `st_signs` |
| p. 333, fn. 2 | `ℓ₂ = −σ(1 − s_I)/[1/γ + σ(1 − s_I)]` | corrected: `st_footnote_2`; counterexample `st_footnote_2_printed_false` |
| p. 334 | `I = 0`: `ε^M = (1 − σ)/(1/γ + σ)`, sign by `σ ≶ 1` | `st_zero_income_signs` |
| p. 334 | `σ = 1`: effects offset, each increasing in `γ` | `st_effects_mono_gamma` |
| p. 334 | Substitution effect `ℓ₁ − ℓℓ₂`; Slutsky `ε^H = ε^M − ((1 − s_I)/s_I)ε_{ℓ,I}` | `st_substitution_effect`, `st_slutsky` |
| p. 334, (12.4) | `ε^H = 1/(1/γ + σ(1 − s_I))`, utility held constant | `eq_12_4`, `st_compensated_utility` |
| p. 334 | Hicksian positive and `≥` Marshallian | `st_signs` |
| pp. 334–335 | `1 − τ` acts as a wage change; `T` as non-labour income | `st_tax_as_wage` |
| p. 335 | Budget-neutral `T = τwℓ`: Hicksian elasticity relevant | `st_balanced_budget`, `st_balanced_budget_hicks_iff` (see corrections) |
| — | The path hypotheses are satisfiable (explicit solution at `ψ = γ = σ = 1`) | `stExplicit`, `st_explicit_foc`, `st_explicit_path` |
| p. 335 | Prescott (2004) | see §12.6.1 |

## §12.3.2 Richer static models (`StaticExtensions`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 335, fn. 3–4 | Concave home technology, home capital (Greenwood et al.) | not formalised: remarks and narrative |
| p. 336 | First-order conditions `u′g₁w = v′`, `u′g₂A = v′` | `hp_focs` (Fermat's rule, `ext_foc_of_max`) |
| p. 336, (12.5) | `g₂/g₁ = w/A` | `eq_12_5` |
| p. 336 | CES: `g₂/g₁ = ((1 − θ)/θ)(c_h/c_m)^{η−1}` | `cesG`, `hp_ces_partials` |
| p. 336, (12.6) | `ℓ_h/ℓ_m = ((1 − θ)/θ)^{1/(η−1)}(w/A)^{η/(η−1)}` | corrected: `eq_12_6`; `eq_12_6_printed_false` |
| p. 336 | `0 < η < 1`: exponent negative, ratio decreasing in `w/A` | `hp_ratio_decreasing` |
| p. 337 | Unitary household, budget `c = w_fℓ_f + w_mℓ_m + I` | `hh_focs` |
| p. 338 | FOCs; higher earnings of one member lower the other's hours | `hh_focs`, `hh_cross_wage` |
| p. 338 | `v′(ℓ_f)/v′(ℓ_m) = w_f/w_m`, `ℓ_f/ℓ_m = (w_f/w_m)^γ` | `hh_relative_hours` |
| p. 338 | Specialisation; gender wage gap (Attanasio et al.) | not formalised: narrative |
| p. 338 | Added-worker effect: lower `ℓ_m` raises `ℓ_f` | `hh_added_worker`, `st_income_decreasing` |
| p. 339 | `Ũ = u(c) + ṽ(l)`, `ṽ(l) = l^{1−1/γ}/(1 − 1/γ)` | `lt_vtilde_hasDerivAt` |
| p. 339 | High non-labour income: `ℓ = 0` optimal | `lt_corner` |
| p. 339 | Benchmark `ℓv′/v` constant | `lt_benchmark_elasticity` |
| p. 339 | `−ℓṽ′(ℓ̄ − ℓ)/ṽ(ℓ̄ − ℓ)` → `−∞` as `ℓ → ℓ̄` | `lt_elasticity`; corrected: `lt_elasticity_limits` |
| pp. 339–340 | Leisure technologies `Σ(A_jl_j)^{1−δ}/(1 − δ)`, Aguiar et al. | not formalised: narrative and empirical |

## §12.3.3 Dynamic labour supply: a first look (`StaticExtensions`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 340 | Two-period problem, lifetime budget | FOCs taken as hypotheses in `tp_frisch` |
| p. 340, fn. 7 | No borrowing: two static problems | not formalised: remark |
| p. 341 | FOCs; `(ℓ₁/ℓ₂)^{1/γ} = w₁/w₂`, `log ℓ₁ − log ℓ₂ = γ(log w₁ − log w₂)` | `tp_frisch` |
| p. 341, fn. 8 | `log ℓ_t = γ/ψ + γ log w_t + γ(1 − σ) log c_t` | corrected: `footnote_8`; `footnote_8_printed_false` |

## §12.4 Dynamic models and §12.4.1 elasticities (`Dynamic`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 342, (12.7) | Life-cycle problem with borrowing limit and no-Ponzi condition | `DynFeasible` (deterministic; see corrections) |
| p. 342, (12.8) | Separable utility | `crraU`, `disutil` (`Static`) |
| p. 342, (12.9)–(12.11) | Net non-labour income, `c = (1 − τ)wℓ + I`, full income | `eq_12_9_to_12_11` |
| pp. 342–343 | Two-stage budgeting: given `a_{t+1}`, period `t` solves the static problem | `dyn_two_stage` |
| p. 343, fn. 9 | Euler equation, Chapter 4 | not formalised: cross-reference |
| p. 343, (12.12) | `d log c/d log w = (1 − s_I)(1 + d log ℓ/d log w)` | `eq_12_12` |
| p. 343, (12.13) | `c^{−σ}w(1 − τ) = ψℓ^{1/γ}` | `eq_12_13` |
| p. 343, (12.14) | `σ d log c/d log w + (1/γ) d log ℓ/d log w = 1` | `eq_12_14` |
| p. 343, (12.15) | Dynamic Marshallian elasticity | `eq_12_15`, `eq_12_15_path` |
| p. 344 | Compensation `dI/dw = (1 − τ)ℓ` | corrected sign: `eq_12_17`; `dyn_compensation_sign` |
| p. 344, (12.16) | Slutsky equation | `eq_12_16` |
| p. 344 | `ε_{ℓ,I} = −σs_I/(1/γ + σ(1 − s_I))` | `eq_12_2` (at the net wage) |
| p. 344, (12.17) | Hicksian elasticity; positive; `≥ ε^M`, equality as `σ → 0` | `eq_12_17`, `st_signs`, `dyn_ordering_sigma_zero` |
| p. 344, fn. 10 | Rebated revenues: Hicksian relevant | `st_balanced_budget` |
| pp. 344–345 | Permanent vs temporary changes | not formalised: narrative |
| p. 345, (12.18)–(12.21) | Frisch elasticity `U_ℓ/(ℓU_ℓℓ − ℓU_ℓc²/U_cc)` | `eq_12_21`, `frischF` |
| p. 345 | (12.8): `ε^F = γ` | `dyn_frisch_separable`, `dyn_frisch_separable_path` (through `eq_12_21`) |
| p. 345 | `ε^F ≥ ε^H ≥ ε^M`, "equality when `σ → ∞`" | `dyn_ordering`; corrected: `dyn_ordering_sigma_zero`, `dyn_ordering_sigma_infty` |
| p. 345, (12.22) | GHH utility; `ε^F = γ` | `dyn_ghh_partials` (uses Miao's `rb_ghh_mrs`), `dyn_frisch_ghh` |
| p. 346 | GHH: zero income effect, `ε^M = ε^H = ε^F = γ` | `dyn_ghh_no_income_effect` |
| p. 346 | Cobb–Douglas: `ε^F = ((1 − ℓ)/ℓ)(1 − (1 − ψ)(1 − σ))/σ` | `dyn_cd_partials`, `dyn_frisch_cd` |
| p. 346 | Power leisure: `ε^F = ((1 − ℓ)/ℓ)(1/γ)` | `dyn_frisch_leisure` |
| p. 346 | More hours, less responsive | `dyn_frisch_decreasing_hours` |
| p. 346 | Constrained individuals: temporary wage affects `λ` | not formalised: qualitative remark |
| p. 346, (12.23) | Euler equation; `d log(ℓ_{t+1}/ℓ_t)/d log(w_{t+1}/w_t) = γ`; time-varying taxes | `eq_12_23` |

## §12.4.2 Estimation of the Frisch elasticity (`Estimation`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 347 | Estimating `σ` (consumption, asset pricing); fn. 11 | not formalised: narrative |
| p. 347, (12.24) | `log c = −(1/σ) log λ` | `eq_12_24` |
| p. 347, (12.25) | `log ℓ = const + γ log w + γ log λ` | `eq_12_25` |
| p. 347 | OLS bias from `Cov(log w, log λ) < 0` | not formalised: econometric argument |
| p. 348, (12.26) | First differences | `eq_12_26` |
| p. 348, (12.27) | Euler equation with borrowing multiplier, in logs | `eq_12_27` |
| p. 348, (12.28) | Log-normal: `log E[λ′] = E[log λ′] + Var/2`; `Var(log λ′) = Var(ξ)` | `eq_12_28` (Gaussian law) |
| p. 348 | First-order approximation of `log(λ − φ)` around `φ = 0` | `fe_log_approx` (exact form, two-sided bounds, derivative) |
| p. 348, (12.29) | `Δ log ℓ = γΔ log w + γ(ξ − φ/λ − ½Var)` | `eq_12_29` (exact, with `log(1 − φ/λ)` and the constant) |
| pp. 348–349 | MaCurdy IV, measurement error, weak instruments | not formalised: econometric narrative |
| p. 349, (12.30)–(12.31) | Expected wage growth | `eq_12_31` |
| p. 349 | Pistaferri 0.7; Domeij–Floden; Low | not formalised: empirical and qualitative |
| p. 349 | `Δ log ℓ = γΔ log w − γσΔ log c` | `fe_consumption_data` |
| pp. 349–350 | Altonji, Fehr–Goette, Bianchi et al. (0.4) | not formalised: empirical |
| p. 350, (12.32) | GHH static problem with re-optimisation cost | `frV` |
| p. 351, (12.33) | `ℓ* = (w/ψ)^γ`, `c* = wℓ*` | `eq_12_33`, `fr_opt_facts`, `fr_rpow_tangent` |
| p. 351 | `U(c*, ℓ*) = −log(1 + γ) − γ log ψ + (1 + γ) log w` | `fr_value` |
| p. 351 | Decomposition; first bracket `log(1 + ε(1 + γ))` | `eq_12_34` |
| p. 351, (12.34) | `(1 + γ) log(1 + ε) − log(1 + ε(1 + γ))` | `eq_12_34`, `fr_gain_pos`, `fr_gain_strictMono` |
| p. 351, (12.35) | `≃ ½γ(1 + γ)ε²` | `eq_12_35` (explicit cubic error bound) |
| p. 352 | `ε_min = (2Δ/(γ(1 + γ)))^{1/2}`; `Δ log ℓ* > (2Δγ/(1 + γ))^{1/2}` | `fr_threshold` |

## §12.5 Labour supply and balanced growth; Appendix 12.A (`BalancedGrowth`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 352 | Balanced growth in Chapter 13; Figure 12.1 hours stable | not formalised: empirical |
| p. 352, (12.36) | Planner, Cobb–Douglas, `Z_{t+1} = Z_t(1 + g)` | `bgF`, `bgMPK`, `bgMPL`, `bg_homog` |
| p. 353, (12.37) | KPR utility | corrected: `kprU`, `kprUC`, `kprUl`, `kpr_partials`, `kpr_mrs`; printed form fails: `eq_12_37_printed_not_bgp` |
| p. 353, (12.37) "if" | Balanced growth with constant hours | `eq_12_37_if`, `kpr_homog` |
| p. 353 | Static: wage has no effect on hours | `kpr_static_hours` |
| p. 353 | Postwar U.S. an exception | not formalised: empirical |
| p. 849, (12.A.1) | Euler equation with `κ = K/Z` constant | `bg_homog` (`MPK = α(L/κ)^{1−α}`), `eq_12_37_if` (corrected: factor `α`) |
| p. 849, (12.A.2) | `U_CC C/U_C = σ`; candidate forms | corrected sign: `eq_12_A_2` (via `theorem_4A_4` of AKMM Ch. 4) |
| p. 849, (12.A.3) | Intratemporal condition forces `v²` constant | `kpr_candidate_deriv`, `eq_12_A_3` (also `σ′ = 0`) |
| p. 849 | "The derivation for the log case is similar" | `eq_12_A_3_log` (forces `v¹` constant) |
| p. 849 | "if and only if belong to the class (12.37)" | `eq_12_37_if`, `eq_12_37_only_if`, `eq_12_37_only_if_instance` (class stated in corrections) |

## §12.6 Labour supply across countries and over time (`TaxesCycles`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 353 | `log C − ψL^{1+1/γ}/(1 + 1/γ)` accounts for much of the variation | not formalised: empirical claim |
| p. 354, (12.38) | Household problem with `τ_c`, `τ_ℓ`, transfers; resource constraint; fn. 12 | intratemporal conditions as hypotheses of `eq_12_39` |
| p. 354, (12.39) | `L* = [(1 − τ)(1 − α)/(χψ)]^{γ/(1+γ)}`, `τ = (τ_ℓ + τ_c)/(1 + τ_c)` | `eq_12_39`, `bg_mpl_eq` |
| p. 354, fn. 13 | Sources of variation in `χ` | not formalised: narrative |
| p. 354 | Data: 25.9 vs 16.5 hours, ratio 1.57; Prescott's `τ`, `χ` | not formalised: data (inputs of `eq_12_39_us_italy`) |
| pp. 354–355 | `γ = 1` gives a U.S./Italy ratio of 1.42 | corrected: `eq_12_39_us_italy` (`≈ 1.19`; `1.42` is the `γ → ∞` limit) |
| p. 355 | Permanent taxes: Marshallian or Hicksian; `σ = 1` | `st_tax_as_wage`, `st_balanced_budget` |
| p. 355 | Bick et al.: hours fall with development | not formalised: empirical |
| p. 355 | Subsistence `log(C − C̄)`: long hours at low wages; income/substitution ratio decreasing to `1` | `ti_subsistence`, `ti_subsistence_marshallian`, `ti_effect_ratio` |
| p. 355, fn. 14 | Feasibility of `C > C̄` | hypothesis `C > C̄` |
| p. 355 | `σ > 1`: income effect always larger; hours decline at a constant rate (Boppart–Krusell) | `ti_sigma_gt_one`, `ti_effect_ratio` |
| p. 356 | Ohanian et al.; open issue | not formalised: narrative |
| p. 356, (12.40) | `log L_t = const − (γ/(1 + γ)) log(C_t/Y_t)` | `eq_12_40` |
| p. 356 | Infinite Frisch: coefficient `1`; `γ = 1`: half | `ti_cycle_coefficient` |
| p. 356 | No capital, closed economy: `C = Y`, hours invariant to productivity | `ti_no_capital` |
| pp. 356–357 | Labour wedge; Shimer; Chapter 14, 20 | not formalised: narrative |

## §12.7 Dynamic returns to labour supply (`TaxesCycles`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 357 | Problem with `w_t = (1 + κΣ_{j<t}ℓ_j)w₀` | `ikWage`, `ikEarnings` |
| p. 357 | Return to work = wage + human-capital term | `ik_marginal_earnings` |
| p. 357, (12.41) | First-order condition | `eq_12_41` (perfect foresight) |
| p. 357, Figure 12.6 | Human-capital term `H_t = κw₀Σ_{j=1}^{T−t}R^{−j}ℓ_{t+j}` and return to work `w_t + H_t` | `ikfHC`, `ikfReturn` (`HumanCapitalProfiles`) |
| p. 358, Figure 12.6 | Backward induction: `H_T = 0`, `H_t = R^{−1}(κw₀ℓ_{t+1} + H_{t+1})`; wage rises by `κw₀ℓ_t` | `ikf_hc_last`, `ikf_hc_succ`, `ikf_hc_diff`, `ikf_wage_succ`, `ikf_hc_nonneg`, `ikf_geom` |
| p. 358, Figure 12.6 | Wage never falls; return to work above the wage, equal to it at the end | `ikf_wage_step`, `ikf_return_vs_wage` (see corrections: the plotted late fall of the wage is not in the model) |
| p. 358 | "the human capital term is high early on, but it declines with age" | corrected: `ikf_hc_antitone`, `ikf_hc_step_le_one` (`R ≤ 1`), `ikf_hc_step_peak` (declining phase of hours, any `R`), `ikf_hc_const_hours` ("as clear from the sum"); fails for `R > 1`: `ikf_hc_rises` |
| p. 358, Figure 12.6 | Hours over the life cycle | `ikf_return_pos`, `ikf_hours_up`, `ikf_hours_up_strict`, `ikf_hours_down`, `ikf_hours_down_strict`; instances `ikf_instance_up`, `ikf_instance_down` |
| p. 358 | "hours are relatively flat while wages grow steeply"; return to work "much flatter" | `ikf_flat` (`R = β = 1`: hours and return constant, wage linear up, `H` linear down to 0), `ikf_instance_flat` |
| p. 358 | Naive estimate of `γ` from current wages understates it | `ikf_naive_gamma`, `ikf_flat_naive` (estimate `0` at `R = β = 1`) |
| p. 358, Figure 12.6 | Hump in hours, fall of wages and hours late in life, magnitudes of the curves | not formalised: calibrated features of the plotted curves (see corrections) |
| p. 358 | Bias of naive estimates; Frisch 0.4 to 2.0; ranking of elasticities | not formalised: quantitative claims from estimates |

## §12.8 Intensive and extensive margins (`IndivisibleLabor`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 359 | Micro vs aggregate elasticities | not formalised: narrative |
| pp. 359–360 | Divisible economy: planner gives everyone `(c, ℓ)`; aggregate Frisch `γ` | `dyn_frisch_separable`, `tp_frisch` |
| p. 360 | Indivisible: equal consumption optimal | `il_full_insurance` |
| p. 360 | Lottery problem `max eU(c, ℓ̄) + (1 − e)U(c, 0)`, `c = Aℓ̄e` | `il_planner` |
| pp. 360–361 | `= u(c) − ψ̃e − v(0)`, `ψ̃ = v(ℓ̄) − v(0)` | corrected (`ψ̃ = ψ(v(ℓ̄) − v(0))`): `il_lottery` |
| p. 361 | Infinite aggregate Frisch elasticity | `il_frisch_infinite` |
| p. 361 | Individual vs aggregate supply; two takeaways | not formalised: narrative |
| p. 361 | Selling employment probabilities; earnings `eℓ̄w` | not formalised: narrative (the planner's problem is `il_planner`) |
| pp. 361–362 | Ljungqvist–Sargent: no discounting, `r = 0`, wage `A`; `∫e = e*`, `c = c*`, indifference over timing | `il_lagrange_suff`, `il_ljungqvist_sargent` (finite version) |
| p. 362, fn. 16 | `e* = 1`: small wage changes leave `e` unchanged | `il_frisch_infinite` (last conjunct) |
| p. 363 | Heterogeneous `ψ`; `ψ*(e)` with `F(ψ*) = e` | hypotheses of `il_vtilde_deriv` |
| p. 363 | `ṽ(e) = ∫₀^{ψ*(e)} ψf(ψ)dψ`, nonlinear; Frisch depends on `f` | `il_vtilde_deriv`, `il_vtilde_convex`, `il_vtilde_uniform`, `il_hetero_frisch` |
| p. 363 | Dynamic version with iid draws | not formalised: remark |
| pp. 363–365, (12.42)–(12.43) | Chang–Kim: model, estimates 0.41, 0.78, 1.08, about 2 | not formalised: simulation |
| p. 365, (12.44) | `ℓ_e = max(0, ℓ − ℓ_f)` | `effHours` |
| pp. 365–366 | Fixed cost: low hours suboptimal; `ℓ_e = ℓ^θ`: 25 + 25 vs 50 | `il_small_hours`, `il_concentrate` |
| p. 366 | Large `ℓ_f` or `θ`: planner's allocation looks indivisible | not formalised: qualitative claim |
| pp. 366–367 | Rogerson–Wallenius: threshold `z*`, `ℓ = 0` below, increasing above | `il_rw_threshold`, `il_rw_life_cycle`, `il_lagrange_suff` (finite version) |
| p. 367 | Quantitative results (20% fall, intensive share 60% / 5%), Erosa et al. 1.75 | not formalised: simulation |
