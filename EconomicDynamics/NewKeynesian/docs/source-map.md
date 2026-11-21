# Source map: Miao Chapter 19

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 19, Dynamic New
Keynesian Models, pp. 615–670. Lean names are relative to `Miao.NewKeynesian`. The chapter has no
numbered results; its derivations are located by equation number and page. Log-linearisation is
formalised as differentiation along paths through the steady state, and second-order approximations
as Taylor statements with explicit or o(·) remainders. The medium-scale model of §19.4 and Exercise
6 are listed only. Departures from the book are in [corrections](corrections.md).

## Introduction and §19.1 (the basic DNK model), Exercise 19.1

### Introduction and the start of §19.1 (pp. 615–616)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 615–616 | History of the DNK approach; MIU, CIA and OLG approaches to money | Not formalised (verbal) |

### §19.1.1 Households (pp. 616–618)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.1), p. 617 | The separable utility; `u₁ = C^{−γ}`, `u₂ = −χN^ν`, `u₃ = m^{−ϕ}`, second derivatives | `nk_u`, `nk_hasDerivAt_pow_div`, `nk_u_C`, `nk_u_N`, `nk_u_m`, `nk_u_CC`, `nk_u_NN`, `nk_u_mm` |
| p. 617 | `u₁ > 0`, `u₂ < 0`, `u₃ > 0`, `u₁₁, u₂₂, u₃₃ < 0` | `nk_u_signs` |
| p. 617 | A satiation level `m*` with `u₃ ≤ 0` beyond it (corrected: fails for (19.1)) | `nk_u_no_satiation` |
| p. 618 | First-order conditions and transversality | Hypotheses of `eq_19_2`–`eq_19_4` (the conditions are listed, not derived, in the book); transversality not used |
| (19.2), p. 618 | `χN^ν/C^{−γ} = W/P` | `eq_19_2` |
| (19.3), p. 618 | The consumption Euler equation | `eq_19_3` |
| (19.4), p. 618 | The money demand equation | `eq_19_4` |
| p. 622 | (19.4) determines the money supply (needs `i_t > 0`) | `nk_money_supply`, `nk_money_demand_pos_rate` |

### §19.1.2 Final goods firms (pp. 618–619)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.5), p. 618 | The Dixit–Stiglitz aggregator | `nk_aggY` |
| (19.6), p. 619 | The first-order condition gives the demand curve | `eq_19_6_foc` |
| (19.6), p. 619 | The demand curve solves the profit maximisation problem | `eq_19_6`, `nk_rpow_tangent`, `nk_demand_agg`, `nk_demand_cost`, `nk_demand_rpow` |
| (19.7), p. 619 | Zero profit gives the price index | `nk_priceIndex`, `eq_19_7`, `nk_priceIndex_rpow`, `nk_priceIndex_pos`, `nk_integral_rpow_pos` |

### §19.1.3 Intermediate goods firms (pp. 619–621)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.8), p. 619 | Technology; the labour requirement | `nk_labor_req` |
| pp. 619–620 | Real total cost; real marginal cost is its derivative and the Lagrange multiplier | `nk_TC`, `nk_MC_deriv`, `nk_MC_lagrange` |
| (19.9), p. 620 | Average real marginal cost | `nk_MCavg` |
| (19.10), p. 620 | `MC^j = MC(Y/Y^j)^{−α/(1−α)} = MC(P^j/P)^{εα/(α−1)}` | `nk_MC_ratio`, `eq_19_10` |
| p. 620 | Firms with higher prices have lower marginal costs | `nk_MC_antitone` |
| p. 621 | The Calvo objective and its first-order condition | `nk_calvo_term_deriv`, `nk_calvo_foc` |
| (19.11), p. 621 | The optimal reset price | `eq_19_11` |
| (19.12), p. 621 | Marginal cost of a firm that reset at `t` | `eq_19_12` |
| (19.13), p. 621 | Price-index dynamics (law of large numbers) | `eq_19_13`, `nk_calvo_avg` |

### §19.1.4 Central bank (pp. 621–622)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.14), p. 621 | The Taylor rule | `nk_taylorRule` |
| p. 622 | Money supply from (19.4) | `nk_money_supply` |
| p. 622 | Money-supply rules and the Ramsey problem as alternatives | Not formalised (verbal) |

### §19.1.5 Sticky price equilibrium (pp. 622–623)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.15), p. 622 | Aggregate labour | `nk_dispersion`, `eq_19_15` |
| (19.16), p. 622 | Aggregate output with price dispersion | `eq_19_16` |
| (19.17), p. 622 | Dispersion dynamics | `eq_19_17` |
| p. 623 | The equilibrium: (19.2)–(19.4), (19.11), (19.13), (19.14), (19.16), (19.17), `C = Y` | The listed theorems; the zero-inflation steady state satisfies them: `nk_steady_state`, `nk_reset_constant` |

### §19.1.6 Flexible price equilibrium (p. 623)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 623 | `θ → 0`: `P*/P = μMC^j` | `nk_flex_reset` |
| p. 623 | Symmetry: `MC^j = 1/μ`, `Y^j = Y`; `W/P = (1/μ)(1 − α)AN^{−α}` | `nk_flex_symmetric`, `nk_flex_wage` |
| (19.18), p. 623 | Natural output, unique, determined by productivity | `eq_19_18` |

### §19.1.7 The log-linearised system (pp. 624–630)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 624 | Log-linearisation as a first-order perturbation | `nk_path_deriv`, `nk_rpow_path` |
| (19.19), p. 624 | `q_t = θπ_t/(1 − θ)` | `eq_19_19` |
| p. 624 | The log-linearised (19.11) | `nk_loglin_reset_terms` |
| (19.20), p. 624 | Simplifying | `eq_19_20`, `nk_pv`, `nk_summable_geom`, `nk_tsum_geom_smul` |
| (19.21)–(19.22), p. 624 | Log-linear (19.12); `b = εα/(1 − α)` | `eq_19_21`, `nk_b` |
| p. 625 | Plugging (19.21) into (19.20) | `nk_reset_plugged` |
| p. 625 | The recursive form of `P̂*_t` and of `q_t` | `nk_reset_recursive`, `nk_pv_rec`, `nk_q_recursive` |
| p. 625 | `π_t = βE_tπ_{t+1} + ((1 − βθ)(1 − θ)/(θ(1 + b)))MĈ_t` | `nk_pc_mc` |
| p. 625 | `MĈ` from (19.9); log-linear (19.2) | `nk_loglin_MC`, `nk_loglin_19_2` |
| (19.23), p. 625 | `MĈ = νN̂ + γŶ + (α/(1 − α))Ŷ − (1/(1 − α))Â` | `eq_19_23` |
| pp. 625–626 | Total differential of (19.16); dispersion drops out to first order | `nk_loglin_19_16`, `nk_loglin_19_17`, `nk_loglin_dispersion`, `nk_dispersion_zero`, `nk_loglin_output` |
| p. 626 | `MĈ = ((ν + α + γ(1 − α))/(1 − α))(Ŷ − Ŷ^f)`; log-linear (19.18) | `nk_mc_gap`, `nk_loglin_19_18` |
| (19.24), p. 626 | The New Keynesian Phillips curve | `eq_19_24` |
| (19.25), p. 626 | The slope κ, both forms; `κ > 0` | `nk_kappa`, `eq_19_25`, `nk_kappa_pos` |
| (19.26), p. 626 | Log-linear Euler equation | `eq_19_26`, `nk_loglin_euler` |
| (19.27), p. 626–627 | The natural rate and its log-linear form | `nk_loglin_natural_rate`, `eq_19_27` |
| (19.28), p. 627 | The intertemporal IS curve | `eq_19_28` |
| (19.29), p. 627 | The log-linear Taylor rule | `eq_19_29` |
| p. 627 | (19.24), (19.28), (19.29) as a system | `nk_dnkSystem`, `nk_dnk_iff` |
| Figure 19.1, pp. 627–628 | Monetary shock: output gap and inflation fall, the real rate rises more than the nominal rate | `nk_fig_19_1`, `nk_irfLam`, `nk_irfLam_pos`, `nk_irf_solves` (magnitudes not formalised: computational) |
| Figure 19.2, p. 628 | Natural-rate shock: gap, inflation and the nominal rate rise, the real rate by less than one-for-one | `nk_fig_19_2` (magnitudes not formalised: computational) |
| pp. 628–630 | Transmission channels, Pigou effect, nonseparable utility | Not formalised (verbal/empirical) |

### Exercise 19.1 (p. 668) and condition (19.31) (p. 635)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 1 | Unique stable equilibrium iff (19.31) (for `φ_π, φ_y ≥ 0`) | `nk_dnkDeterminate`, `ex_19_1`, `ex_19_1_suff`, `ex_19_1_nec`, `nk_pair_stable`, `nk_pair_adapted`, `nk_rule_regular` |
| Ex 1 | The exact condition for `φ_y ≥ 0` and any `φ_π` (corrected) | `ex_19_1_exact`, `ex_19_1_not_necessary` |
| Ex 1 | With the structural κ of (19.25) | `ex_19_1_structural` |

## §19.2 Monetary Policy Design and Exercise 19.2

### §19.2.1 Efficient allocation (`MPEfficient`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 630 | Planner's problem: CES aggregate `Y = (∫Y_j^{(ε−1)/ε}dj)^{ε/(ε−1)}`, `Y_j = AN_j^{1−α}`, `N = ∫N_j` | `mpCES`, `mp_firm_term`, `mp_ces_const`, `mp_q_bounds`, `mp_integrable_rpow` |
| p. 631 | "`Y^j = Y = C`, `N^j = N` for all `j`": the symmetric allocation maximises output, uniquely (a.e.) | `mp_ces_le`, `mp_ces_symmetric`, `mp_ces_lt` |
| p. 631 | Efficient allocation: `−u_N/u_C = (1 − α)AN^{−α} = MPN` | `mpU`, `mp_hasDerivAt_uC`, `mp_hasDerivAt_uN`, `mp_hasDerivAt_mpn`, `mp_planner_foc` |
| p. 631 | Efficient output `Y^e` is (19.18) with `μ = 1` | `mpYout`, `mp_mrs_iff_log`, `mp_mrs_output` |
| p. 631 | Employment subsidy `τ = 1/ε` makes `W/P = MPN` (and only it) | `mp_subsidy` |
| p. 631, fn. 6 | A household subsidy must be `1/(ε − 1)` | `mp_subsidy_household` |
| p. 631 | With the subsidy the flexible-price equilibrium is efficient | `mp_flex_subsidy_efficient` |
| p. 634 | Distortion `Φ`: `−u_N/u_C = MPN(1 − Φ)`, `Φ = 1 − 1/((1 − τ)μ)`; `Φ = 0` iff `τ = 1/ε` | `mp_distortion` |
| p. 634 | `ŷ^f_t = (1 + ν)a_t/(γ(1 − α) + ν + α)` | `mp_yf_loglinear` |
| p. 634 | `x* = Φ(1 − α)/(γ(1 − α) + ν + α)` is `ln(Y^e/Y^f)` to first order | `mpXstar`, `mp_xstar_first_order` |
| p. 631 | Staggered prices: relative-price distortion; the goal of policy is equal relative prices | qualitative (see `mp_dispersion_zero_inflation`) |

### §19.2.2 Quadratic approximation to utility

### The Taylor expansion and (19.30) (`MPQuadratic`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 632 | `(C_t − C)/C ≃ ĉ_t + ĉ_t²/2` (likewise for `N`) | `mp_taylor_exp` (remainder `≤ |ĉ|³`) |
| p. 632 | Taylor expansion of `u` in levels; with (19.1), `u_CC C/u_C = −γ`, `u_NN N/u_N = ν` | `mp_uCC`, `mp_uNN` |
| p. 632 | "Keeping terms up to second order": the expansion equals (19.30) plus explicit cubic and quartic terms | `mp_eq_19_30_truncation` |
| p. 632 | Exact form of `(u_t − u)/(u_C C)` | `mp_util_exact`, `mp_exp_quad_bound` |
| p. 632, (19.30) | `(u_t − u)/(u_C C) = ĉ + (1 − γ)ĉ²/2 + (u_N N/u_C C)(n̂ + (1 + ν)n̂²/2)` up to a cubic remainder; little-o form | `eq_19_30`, `eq_19_30_littleO` |

### Step 1: labour and price dispersion (`MPDispersion`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 633 | `n_t = (y_t − a_t)/(1 − α) + ln Δ_t` from (19.16); in deviations `n̂ = (ŷ − a)/(1 − α) + Δ̂` | `mp_labor_log`, `mp_labor_dev` |
| p. 633 | By (19.13) and (19.17), `Δ_t = θΠ_t^{ε/(1−α)}Δ_{t−1} + (1 − θ)((1 − θΠ_t^{ε−1})/(1 − θ))^{ε/((1−α)(ε−1))}` | `mpG`, `mp_dispersion_recursion` |
| p. 633 | Exact form in `δ = Δ − 1` | `mpH`, `mp_dispersion_delta` |
| p. 633 | "`Δ̂_t = 0` up to first order"; second-order coefficient `K = (1 − α + αε)εθ/(2(1 − α)²(1 − θ))` | `mpHd`, `mpK`, `mp_G_zero`, `mp_hasDerivAt_G`, `mp_G_pos_near`, `mp_h_zero`, `mp_hd_zero`, `mp_hasDerivAt_h`, `mp_hasDerivAt_hd`, `mp_peano2`, `mp_h_expansion` |
| p. 633 | Second-order law `Δ̂_t = θΔ̂_{t−1} + Kπ_t²` (remainder `o(π²)` plus a third-order cross term) | `mp_dispersion_second_order`, `mp_log_dev` |
| p. 633 | `∑βᵗΔ̂_t = εθ/(2(1 − α)Θ(1 − θ)(1 − θβ))∑βᵗπ_t²`, `Δ̂_{−1} = 0`, `Θ = (1 − α)/(1 − α + αε)` | `mpTheta`, `mp_K_Theta`, `mp_disp_bounded`, `mp_dispersion_sum` |
| p. 635 | Zero inflation removes the relative-price distortion | `mp_dispersion_zero_inflation` |

### Steps 2–3 (`MPQuadratic`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 633 | Step 2: substituting Step 1 into (19.30) | `mp_step2_subst` |
| p. 634 | `u_N N/(u_C C) = −(1 − α)(1 − Φ)` from `MPN = (1 − α)Y/N`, `Y = C` | `mp_step2_phi` |
| p. 634 | Small-distortion step (neglecting `Φ ×` second-order terms) | `mp_step2_small` |
| p. 634 | Completing the square: `−½(γ + (ν + α)/(1 − α))(x_t − x*)² − (1 − α)Δ̂_t + t.i.p.` | `mpLambdaBar`, `mpTip`, `mp_step2_square` |
| p. 635 | Step 3: `W = −(Ω/2)E∑βᵗ[λ(x_t − x*)² + π_t²] + t.i.p.`, `Ω`, `λ` | `mpOmega`, `mpLam`, `mp_step3`, `mp_omega_pos`, `mp_lam_pos` |
| p. 635 | No distortion: `Φ = 0` gives `x* = 0`; distortions affect `x*` only, not `λ` | `mp_xstar_zero_iff` (`mpLam` does not involve `Φ`) |

### §19.2.3 Commitment versus discretion (`MPPolicy`, `MPTaylorRule`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 635 | Strict inflation targeting `π = 0` (hence `x = 0`) is optimal | `mp_strict_targeting`, `mp_strict_targeting_pi_zero` |
| p. 635 | Hence `i_t = r^n_t` | `mp_strict_targeting_rate`, `mp_zero_eqm_iff` |
| p. 635, (19.31) | Implemented by a Taylor rule when `κ(φ_π − 1) + (1 − β)φ_y > 0` | `mpRuleEqm`, `mp_rule_eqm_iff`, `mp_rule_eqm_rn_iff`, `mpImplements`, `eq_19_31` |
| pp. 635–636 | Yun (2005): optimality with no inherited dispersion, convergence otherwise | not formalised: cited result, no derivation in the text |
| p. 636, (19.32) | With cost-push shocks, `π = 0` does not give `x = 0` | `mp_cost_push_tradeoff` |
| p. 636, (19.33), (19.34) | First-order conditions of the commitment problem; `μ_{x0} = 0` | `eq_19_33`, `eq_19_34` (from `eq_9_25`, `eq_9_26`) |
| p. 636 | `μ_{x,t+1} = aμ_{xt} − (a/β)(κx*/(1 − βa) + u_t/(1 − βaρ_u))`, `a` the smaller root of (9.29) | `mp_commit_rule` (via `eq_9_28`, `eq_9_29`, `ex942_unique_bounded`), `mp_beta_rule`, `mp_root_identity` |
| p. 637 | `x_t = ax_{t−1} − (aκ/λ)u_t/(1 − βaρ_u)` | `mp_commit_x_law` |
| p. 637 | `π_t = aπ_{t−1} + a(u_t − u_{t−1})/(1 − βaρ_u)` | `mp_commit_pi_law` |
| p. 637 | Initial values `x_0`, `π_0` | `mp_commit_initial` |
| p. 637 | The price level is stationary, `p_t = ap_{t−1} + au_t/(1 − βaρ_u)` (corrected) | `mp_price_level`, `mp_price_level_stationary`; counterexample `mp_price_level_printed_false` |
| p. 637, (19.35) | Timeless perspective: `π_t = −(λ/κ)(x_t − x_{t−1})` | `eq_19_35` |
| p. 637 | `(1 + β + κ²/λ)x_t = βE_tx_{t+1} + x_{t−1} − (κ/λ)u_t` | `mp_timeless_euler` |
| p. 637 | Solution `x_t = ax_{t−1} − κu_t/(λ(1 + β(1 − ρ − a)) + κ²)` | `mp_timeless_solves`, `mp_timeless_unique` |
| p. 638 | "The same as that under optimal commitment" | `mp_timeless_coeff` |
| p. 638 | `π_t = (λ/κ)(1 − a)x_{t−1} + λu_t/(λ(1 + β(1 − ρ_u − a)) + κ²)` | `mp_timeless_pi` |
| p. 638 | Under precommitment `π_0 = −(λ/κ)(x_0 − x*)` | `mp_commit_pi0` |
| p. 638 | If `x_{−1} = x*` the timeless solution is the commitment solution | `mp_timeless_vs_commitment` (iff, for `a ≠ 0`) |
| p. 638 | The timeless rule may be dominated by discretion for some `x_{−1}` (Dennis 2010) | not formalised: cited result, no derivation in the text |
| p. 638 | Discretionary inflation `π_t = θ∑ⱼβʲθʲ(κx* + E_tu_{t+j}) = λκx*/(κ² + λ − βλ) + …` (corrected) | `mp_discretion_inflation`, `mp_ex951pi_closed` (via `ex951_forward`, `ex951_series`); counterexample `mp_discretion_printed_false` |
| p. 638 | Inflation bias when `x* > 0` | `mp_inflation_bias` |
| pp. 638–639 | Discretion chooses higher inflation at all times than commitment | `mp_a_lt_theta`, `mp_discretion_above_commitment` (no shocks; via `cp_commitment_vs_discretion`) |
| p. 639 | The gap is larger following a positive cost-push shock | `mp_gap_algebra`, `mp_discretion_gap_impact` |
| pp. 639–640, Fig. 19.3 | Qualitative impulse responses (signs, persistence) | `mp_fig_19_3_commitment`, `mp_fig_19_3_discretion`; plotted numbers not formalised: computational |

### Exercise 19.2 (`MPTaylorRule`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 669, Ex. 19.2 | The Taylor rule (19.29) without shock implements the optimal policy iff (19.31) (corrected: intercept `r^n_t`) | `ex_19_2`, `mp_ex_19_2_instance` |
| p. 669, Ex. 19.2 | As printed (intercept `−ln β`) | counterexample `mp_printed_rule_fails`, `mpDetSystem`, `mp_printed_rule_counterexample` |

## §19.3 Fiscal Stimulus and Exercises 19.3–19.5

### A neoclassical model and monopolistic competition (pp. 640–643, module `FSNeoclassical`)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.36)–(19.38) | Preferences, technology, resource constraint | hypotheses of the theorems below |
| (19.40), p. 641 | `ṽ(Y) = v(f⁻¹(Y))`, `ṽ'(Y) = v'(f⁻¹Y)/f'(f⁻¹Y)` (inverse differentiable) | `fs_vtilde`, `fs_vtilde_hasDerivAt` |
| (19.39) ⟹ (19.40) | Competitive equilibrium gives `u'(Y − G) = ṽ'(Y)` | `eq_19_40` |
| p. 641 | `η_u = −Ȳu''/u'`, `η_v = Ȳṽ''/ṽ'`, `Γ = η_u/(η_u + η_v)` | `fs_etaU`, `fs_etaV`, `fs_Gamma` |
| p. 641 | `ṽ'' = (v''f' − v'f'')/f'³ > 0` (so `η_v > 0`) | `fs_vtilde_deriv2`, `fs_vtilde_deriv2_pos` |
| (19.41), p. 641 | Steady-state multiplier `dY/dG = η_u/(η_u + η_v)` | `fs_multiplier_formula`, `eq_19_41` |
| p. 641 | "positive, but less than one" | `eq_19_41`, `fs_Gamma_pos`, `fs_Gamma_lt_one`; counterexample to the printed `v'' < 0`: `fs_eq_19_41_vpp_neg` |
| p. 642 | Markup `μ = ε/(ε − 1)` from profit maximisation | `fs_markup_foc` |
| (19.42), p. 642 | Real marginal cost `1/μ`, `P = μW/f'(N)` | `eq_19_42` |
| (19.43), p. 643 | `u'(Y − G) = μṽ'(Y)` | `eq_19_43` |
| p. 643 | "the fiscal multiplier is still given by (19.41)" (also the wage-markup wedge) | `eq_19_41` (general wedge `μ > 0`) |
| p. 643 | An endogenous wedge (sticky prices) raises the multiplier | `fs_endogenous_wedge` |
| p. 642 | Dixit–Stiglitz aggregate and price index (19.7) | Not formalised here (§19.1, prefix NK) |

### A DNK model (pp. 643–647, module `FSDNK`)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.44), p. 644 | Euler equation; steady state `r̄ = −ln β` | `eq_19_44` |
| p. 644 | `r_t = r̄` for all `t` ⟹ `C_t = C̄`, multiplier one | `fs_constant_real_rate` |
| (19.45), pp. 644–645 | Cost minimisation with `Kf(N/K)`: first-order conditions | `fs_costmin_foc` |
| p. 645 | Common labour/capital ratio, equal to aggregate hours | `fs_ratio_strictMonoOn`, `fs_common_ratio`, `fs_ratio_eq_hours` |
| (19.46), p. 645 | `MC = W/(Pf'(N))` | `eq_19_46` |
| (19.47), p. 645 | `ṽ'(Y)/u'(Y − G) = MC` | `eq_19_47` |
| p. 645 | Log-linearised reset price `P̂*_t = (1 − βθ)Σθᵏβᵏ(P̂_{t+k} + MĈ_{t+k})` | Starting point (it is (19.20) of §19.1 with `MC_{t+k\|t} = MC_{t+k}`; prefix NK) |
| p. 646 | Its recursive form; the recursion for `q_t` | `fs_reset_recursive`, `fs_q_recursive` |
| p. 646 | With (19.19): `π_t = βπ_{t+1} + (1 − βθ)(1 − θ)MĈ_t/θ` | `fs_nkpc` |
| p. 646 | `MĈ_t = (η_u + η_v)(Ŷ_t − ΓĜ_t)` (corrected) | `fs_mc_loglin` |
| (19.48), p. 646 | `π_t = κΣβʲ(Ŷ_{t+j} − ΓĜ_{t+j})`, `κ > 0`, unique bounded solution | `fs_Bdd`, `fs_forward_hasSum`, `fs_forward_exists`, `eq_19_48`, `fs_kappa_pos` |
| (19.49) | The Taylor rule | `fs_TaylorEqm` |
| (19.50), p. 646 | Log-linearised Euler equation, `σ = 1/η_u` | `fs_euler_loglin`, `eq_19_50` |
| (19.51)–(19.52), p. 647 | The conjecture is an equilibrium iff the coefficients are (19.52) | `fs_psi`, `fs_gammaY`, `eq_19_52` |
| p. 647 | `ψ > 0` | `fs_psi_pos` |
| p. 647 | "One can check that `γ_y < 1`" (and `γ_y > 0`) | `fs_gammaY_lt_one`, `fs_gammaY_pos` |
| p. 647 | `γ_y < Γ` for any large enough `φ_y` | `fs_gammaY_lt_Gamma_iff` |

### Zero interest rate lower bound (pp. 648–654, module `FSZLB`)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.53), p. 648 | Generalises (19.50) (`Δ_t = 0`) | `eq_19_53` |
| p. 648 | `r^net < 0`: the zero bound rules out the zero-inflation steady state | `fs_zlb_no_steady_state` |
| (19.54), p. 649 | `i_t = max(r̄ + φ_ππ_t + φ_yŶ_t, 0)` | in `eq_19_54_branches` |
| (19.55), p. 650 | Determinacy condition; `h(μ) = (1 − μ)(1 − βμ) − κσμ` | `fs_h`, `ex_19_3` |
| p. 650 | Holds for `0 ≤ μ < μ̄`, `μ̄ ∈ (0, 1)` unique (corrected) | `fs_h_strictAntiOn`, `fs_mubar_exists`, `eq_19_55_iff`, `eq_19_55_fails_at_mubar` |
| (19.56), p. 650 | `π_L = κ(Ŷ_L − ΓĜ_L)/(1 − βμ)` | `eq_19_56` |
| (19.57), p. 650 | `(1 − μ)(Ŷ_L − Ĝ_L) = σ(−i_L + μπ_L + r_L)` | `eq_19_57` |
| (19.58), p. 650 | `Ŷ_L = ϑ_r(r_L − i_L) + ϑ_GĜ_L` | `fs_thetaR`, `fs_thetaG`, `eq_19_58` |
| (19.59), p. 650 | `ϑ_r > 0`, `ϑ_G > 1` | `eq_19_59`, `fs_thetaG_zero` |
| p. 650 | The branch of (19.54) and `Ĝ_c`; `i_L = 0` iff `Ĝ_L ≤ Ĝ_c` (corrected) | `fs_Gc`, `eq_19_54_branches` |
| p. 650 | `Ĝ_c > 0` iff `r_L` negative enough (corrected) | `fs_Gc_pos_iff` |
| (19.60), p. 650 | `Ŷ_L = ϑ_r r_L + ϑ_GĜ_L` | `eq_19_60` |
| p. 651 | Above `Ĝ_c`: the solution "left as an exercise"; multiplier `γ_y` at `ρ = μ` (p. 652) | `fs_taylor_branch` |
| p. 652, Figure 19.4 | `Ĝ_c = 0.136`, `γ_y = 0.324` at the stated parameters | `fs_fig_19_4_Gc`, `fs_fig_19_4_gammaY` (in `FSDuration`); the plot itself not formalised |
| p. 652 | `dY_L/dG_L = ϑ_G > 1` for `μ > 0` | `eq_19_60`, `eq_19_59` |
| pp. 652–654, Figure 19.5 | `ϑ_G`, `ϑ_r` increasing in `μ`, unbounded as `μ ↑ μ̄` | `fs_thetaG_strictMonoOn`, `fs_thetaR_strictMonoOn`, `fs_thetaG_tendsto_atTop`, `fs_thetaR_tendsto_atTop` |

### Duration of fiscal stimulus (pp. 654–656, module `FSDuration`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 655 | Crisis output `ϑ_r r_L + ϑ_GĜ_L + ϑ_ππ_S + ϑ_C(Ŷ_S − Ĝ_L)` | `fs_thetaPi`, `fs_thetaC`, `fs_crisis_three_state` |
| p. 655 | `ϑ_π, ϑ_C > 0` | `fs_thetaPi_pos` |
| p. 655 | `ϑ_π ≡ (1 − μ)λϑ_r`, `ϑ_C ≡ σ⁻¹ϑ_π` (corrected) | `fs_thetaC_eq_printed`, `fs_thetaPi_printed`, `fs_thetaPi_printed_ne` |
| p. 655 | `Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L` | `ex_19_4_transitional` |
| (19.61), p. 655 | The multiplier `ϑ_G + ϑ_πγ_π + ϑ_C(γ_y − 1)` | `fs_mult61`, `eq_19_61` |
| p. 655 | "the contribution of the final term is necessarily negative" | `fs_eq_19_61_last_neg` |
| p. 656 | Multiplier below `ϑ_G` for an aggressive rule, `λ > 0` | `fs_eq_19_61_lt_thetaG` |
| p. 656, Figure 19.6 | `λ = 0`: nearly 2.3; `λ = 0.8`: below one; `λ = 0.91`: negative | `fs_eq_19_61_lambda_zero`, `fs_fig_19_6_lambda_zero`, `fs_fig_19_6_point_eight`, `fs_fig_19_6_point_nine_one`; "steadily falls" in `λ` not formalised (plot) |

### Government purchases and welfare (pp. 657–661, module `FSWelfare`)

| Source | Claim | Lean |
| --- | --- | --- |
| (19.62)–(19.63), p. 657 | Optimal purchases: `u'(Y − G) = g'(G)` | `eq_19_63` |
| p. 657 | Welfare derivative `(u' − ṽ')dY/dG + g' − u'`; first term zero in the neoclassical model | `fs_welfare_deriv`, `fs_welfare_deriv_neoclassical` |
| p. 657 | Without intrinsic value, optimal `G` is zero (welfare decreasing in `G`) | `fs_welfare_no_g` |
| pp. 657–659 | Without the zero bound: price stability, zero gap, `Ĝ = 0` optimal, implemented by the Taylor rule | `fs_loss`, `fs_first_best` |
| (19.64), p. 658 | The quadratic loss; `λ_y`, `λ_g > 0` (corrected) | `fs_loss`, `fs_weights_pos`, `ex_19_5` |
| (19.65), p. 659 | Its value in the two-state equilibrium | `eq_19_65` |
| p. 659 | Minimisation subject to (19.56), (19.60): unique linear solution `Ĝ_L`, `> 0`; `ξ > 0` | `fs_xi`, `fs_loss_reduced`, `fs_optimal_GL`, `fs_optimal_GL_unique`, `fs_optimal_GL_pos`, `fs_weights_pos` |
| pp. 660–661 | Zero-output-gap level of `Ĝ_L/\|r_L\|` (corrected) | `fs_zero_gap_GL`, `fs_zero_gap_printed` |
| p. 661, Figure 19.7 | Optimum below the zero-gap level; numbers at `μ = 0.903` | `fs_optimal_GL_lt_zero_gap`, `fs_fig_19_7`; the curves over `μ` and the case-B comparison are not formalised (plots) |

### Exercises 19.3–19.5 (p. 669)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 19.3 | With `i_t = 0`, (19.48) and (19.53) have a unique bounded solution iff (19.55) | `fs_zlbSys`, `fs_zlb_sum_form`, `fs_trivE`, `fs_zlbM`, `fs_zlb_hom_iff`, `fs_zlbM_tr_det`, `ex_19_3`, `ex_19_3_solution` |
| Ex 19.4 | `Ŷ_S = γ_yĜ_L`, `π_S = γ_πĜ_L`, the coefficients, and the multiplier (19.61) | `ex_19_4_transitional`, `ex_19_4`, `eq_19_61` |
| Ex 19.5 | (19.64) by second-order approximation | `fs_taylor2`, `ex_19_5_flex`, `fs_disp`, `ex_19_5_dispersion`, `fs_dispersion_lin`, `fs_labor_dispersion`, `fs_dispersion_sum`, `ex_19_5` |

### Out of scope

§19.4 (A Medium-Scale DSGE Model, pp. 661–668) and Exercise 19.6: other work, not formalised
here. The Matlab code `Chapter19_3.m` and the plots of Figures 19.4–19.7 are computational.
