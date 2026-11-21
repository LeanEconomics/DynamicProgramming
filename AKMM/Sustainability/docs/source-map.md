# Source map: AKMM Chapter 25

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 25, Sustainability (J. Hassler, P. Krusell and C. Olovsson), pp. 749–784,
and Appendix 25.A, p. 909. Page references are the draft's running heads. Lean names are
relative to `AKMM.Sustainability`. Departures from the book are in
[corrections](corrections.md).

## §25.1–25.2 Introduction; the economy and the environment

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 749–753, Figures 25.1–25.2, fn. 1–2 | Sustainability, property rights, the structure of IAMs | not formalised: narrative |

## §25.3.1 The climate system (`Climate`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 753–754 | Greenhouse effect, feedbacks, forcing | not formalised: climate-science narrative |
| p. 754, (25.1) | `dT/dt = σ(f − κT)`: solution, uniqueness from `T₀` | `climateT`, `eq_25_1`, `eq_25_1_unique` (reuses `ContinuousTime` `eq_exp_of_hasDerivAt`) |
| p. 754 | Constant `f`: the temperature reaches the steady state `f/κ` | `eq_25_1_tendsto`, `eq_25_1_steady` |
| p. 754, (25.2)–(25.3) | Arrhenius forcing; steady-state temperature for a given `S` | `forcing`, `steadyTemp`, `eq_25_3` |
| p. 754 | `η/κ` is the ECS: long-run warming from a doubling of CO₂ | `climate_ecs`, `climate_ecs_doubling` |
| p. 754, fn. 3; IPCC ranges for the ECS | Shares of forcing, IPCC ECS intervals | not formalised: data |
| p. 755, (25.4)–(25.5) | For a given `S` the steady state is (25.3) | `twoBoxStep`, `eq_25_4_steady_iff` |
| p. 755 | Convergence to the steady state (slower when `σ₃ ≪ σ₁`) | convergence and stability: `climate_dev_tendsto`, `climate_twoBox_tendsto`, `twoBoxMatrix`, `climate_twoBox_isStable` (reuses `DifferenceEquations` `isStableMatrix_iff_tendsto`); the speed comparison is quantitative, not formalised |

## §25.3.2 The carbon cycle (`CarbonCycle`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 755, (25.6)–(25.8) | Three-reservoir carbon cycle | corrected: `CarbonFlows`, `carbonLin`, `carbonStep`, `eq_25_6_total`; as printed: `carbonStepPrinted`, `eq_25_6_printed_total`, `eq_25_6_printed_false` |
| p. 755 | Mass balance without emissions; invariant distribution | `carbonMatrix`, `carbonMatrix_mulVec`, `carbon_isMarkov` (reuses `OperatorsFixedPoints` `IsMarkov`), `carbon_exists_invariant`, `carbon_invariant_iff`, `carbon_invariant_unique`, `carbonTotal` |
| p. 755, fn. 4–5 | Folini et al. parameters, initial stocks, CO₂/C = 3.67 | not formalised: calibration |
| p. 756 | Linearity of the carbon cycle; reduced form | `carbonPath`, `carbonPulse`, `carbonResponse`, `carbon_superposition` |
| p. 756, (25.9), fn. 6 | `S_t − S₀ = Σ(1 − d_s)E_{t−s}` | `excessCarbon`, `eq_25_9` |
| p. 756, (25.10) | GHKT kernel; `φ_L` stays forever | `ghktKernel`, `eq_25_10_tendsto`, `ghktKernel_mem_Icc`, `ghktKernel_antitone` |
| p. 756 | "the share that leaves the atmosphere within a period [is] `1 − φ₀`" | corrected: `eq_25_10_within_period`, `eq_25_10_within_period_printed_false` |
| p. 756 | Decadal calibration `φ_L = 0.2`, `φ₀ = 0.393`, `φ = 0.0228` | not formalised: calibration |
| p. 770 | `∂S_{t+j}/∂e_t = 1 − d_j`, from (25.9) | `excessCarbon_pulse` |
| p. 771, (25.32) | `Σ_j β^j(1 − d_j)` for the kernel (25.10) | `ghktKernel_hasSum` |

## §25.3.3–25.3.4 Carbon budget and fossil supply

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 756–758, Figure 25.3, fn. 7–9 | `T_t ≈ σ_CCR Σ E_s`; IPCC CCR range; carbon budget (650 GtC, 850 GtC, 85 years) | not formalised: an empirical approximation (the constant CCR is a finding about Earth-system models, not a theorem of (25.4)–(25.8)) and calibrated arithmetic |
| pp. 758–759, Figure 25.4, Table 25.1 | Oil, coal and gas reserves and resources converted to warming | not formalised: data and arithmetic (numeric errata in [corrections](corrections.md), item 11) |

## §25.3.5 Damages (`Damages`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 759–762, Figure 25.5, fn. 10–11 | Stern Review, bottom-up and top-down studies, meta-studies | not formalised: empirical discussion |
| p. 763 | `D(T) = 1 − 1/(1 + 0.00267T²)` | `nordhausD`, `nordhausD_eq` |
| p. 763 | Locally `≈ 0.024(T/3)²` | `nordhausD_approx`, `nordhausD_coefficient` |
| p. 763, fn. 12 | Convex near 0, not globally; `D → 1` | `nordhausD_convexOn`, `nordhausD_not_convexOn`, `nordhausD_tendsto` |
| p. 763 | Weitzman's polynomial, damages in other model parts, `e^{−γS}` approximates Nordhaus | not formalised: narrative / numerical approximation |
| p. 763 | Adaptation: `argmin_a (T − a)^x/x + a = T − 1` for `T ≥ 1`, reduced damage `T + (1 − x)/x` | `adaptCost`, `adaptation_optimal`, `adaptation_unique`; the case `T < 1`: `adaptation_low_T` |
| p. 764 | Discounting (`β = 0.985` vs Stern's `0.999`) | not formalised: calibration and philosophy |

## §25.4.1 A static one-region model (`StaticIAM`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 765, (25.11)–(25.15) | Production, the firm's problem, damages, consumption | `staticE`, `staticW` |
| p. 765, (25.16) | FOC, unique `E = (νA/(p + τ))^{1/(1−ν)}`, decreasing in `τ` | `eq_25_16`, `staticE_pos`, `static_firm_optimal`, `staticE_strictAnti`; auxiliary `static_mp_strictAnti`, `static_lt_staticE_iff`, `staticE_continuousOn` |
| p. 766, (25.17)–(25.18) | Planner's problem and FOC; a unique optimum | `eq_25_18_exists`, `eq_25_17`, `eq_25_17_unique` |
| p. 766 | Laissez-faire emissions too high | `static_laissez_faire_excess` |
| p. 766 | Pigou: `τ = 2γE*` implements `E*` | `static_pigou` |
| p. 766, fn. 15 | `τ = 0` maximises the private economy; small taxes cost little | `staticPrivate`, `static_private_max`, `static_private_hasDerivAt`, `static_private_deriv_zero` (the "concave around zero" remark is not formalised) |
| p. 767, (25.19) | Cap at `E*`: unique permit price `λ = 2γE*` | `CapEquilibrium`, `eq_25_19`, `static_cap_exists` |
| p. 767 | Non-binding and binding caps | `static_cap_nonbinding`, `static_cap_binding` |
| p. 767, fn. 16 | Weitzman (1974) under uncertainty | not formalised: cited result |
| p. 767 | Two firms: planner's FOC, unique optimum, tax and aggregate cap implement it, equal marginal products | corrected (coal cost `p`): `staticW2`, `static_two_exists`, `static_two_optimal`, `static_two_unique`, `static_two_pigou`, `static_two_cap` |

## §25.4.2 A fully dynamic IAM (`DynamicIAM`, `CakeEating`, `LogGrowth`, `OptimalTax`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 767–769, (25.20)–(25.25), fn. 17–20 | Two-region model, energy aggregate, resource constraint, oil stock, government budget | `energyAgg`; the planner's economy `GHKT`, `GHKTAssumptions`, `GHKT.carbon`, `GHKT.output`, `GHKT.cons`, `GHKT.Feasible` |
| p. 769 | Oil owner: `e_{o,t} = (1 − β)R_t` | `oil_owner_overtake`, `oil_owner_optimal` (with `cakePath`, `cake_policy`) |
| p. 769, (25.26) | CES price index of energy services | `energyD`, `energyPrice`, `eq_25_26_least_cost` (duality) |
| p. 769, (25.27) | Input demands | `energyDemand`, `energyDemand_pos`, `energy_term`, `eq_25_27_index`, `eq_25_27_cost`, `eq_25_27_foc` |
| p. 770, (25.28) | Energy demand of the final-good firm | `eq_25_28` |
| p. 770, (25.29) and next display | Euler equation and the saving-rate difference equation | corrected: `eq_25_29_saving`; as printed: `eq_25_29_printed_false`, `eq_25_29_saving_printed_false` |
| p. 770 | "only one non-explosive solution: `s_t = αβ/(1 − ν)`" | `savingNext`, `saving_const`, `saving_fixed_iff`, `saving_below`, `saving_above`, `saving_above_tendsto`, `saving_above_tvc` |
| p. 770 | Sequential equilibrium; solves "in under a second" | not formalised: computational remark |
| p. 770 | The planner's problem | `ghkt_optimal` (optimality of `GHKT.optK` with constant energy), `ghkt_opt_saving`, `ghkt_opt_cons`, `ghkt_opt_feasible`, `ghkt_opt_summable`, `ghkt_overtake`; auxiliary `ghkt_log_output`, `ghkt_psi`, `GHKT.Psi`, `GHKT.PsiN`, `ghkt_sum_interchange`; the log/Cobb–Douglas decomposition `lgPhi`, `lg_phi_le`, `lg_identity`, `lg_compare`, `lg_linear_bound`, `lg_tendsto_linear`, `lg_summable_linear` |
| p. 770, (25.30) | Marginal externality | `ghkt_tax_of_proportional` (log utility, `C/Y` constant), with `excessCarbon_pulse` for `∂S_{t+j}/∂e_t` |
| p. 771, (25.31) | `(∂F/∂S)/Y = −γ` | `eq_25_31` |
| p. 771, (25.32) | The optimal tax `τ_t = Y_t Σ_j β^jγ(1 − d_j)` | `eq_25_32`; with the kernel (25.10): `eq_25_32_ghkt`; concrete economy: `coalEconomy`, `ghkt_coal_assumptions`, `ghkt_coal_opt`, `ghkt_coal_optimal`, `ghkt_coal_pigou` |
| p. 771 | Comparative statics in the "three d's" | immediate from `eq_25_32_ghkt`; not stated separately |
| pp. 771–772, Figure 25.6, fn. 21 | Simulations: $25/tCO₂, temperature paths | not formalised: calibrated simulations |
| App. 25.A, p. 909 | Calibration values | not formalised: calibrated numbers |
| App. 25.A, p. 909 | `λ_o/λ_κ = (e_o/e_κ)^{1−ρ}(p_o/p_κ)` | `eq_25_A_ratio` |
| App. 25.A, p. 909 | Normalisation `λ_o + λ_c + λ_g = 1` pins down the weights | `eq_25_A_normalize` |

## §25.5.1 Data

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 773–775, Figures 25.7–25.9, fn. 22–24 | Energy use and resource prices | not formalised: data |

## §25.5.2 Basic theory (`CakeEating`, `DasguptaHeal`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 775–776, fn. 25 | Literature | not formalised: narrative |
| pp. 775–776, fn. 26 | Cake eating: `c_t = (1 − β)R_t = (1 − β)β^t R₀` | `cakePath`, `cake_partial_sum`, `cake_hasSum`, `cake_policy`, `cake_overtake`, `cake_optimal`, `cake_unique`, `cake_slp` (reuses SLP `ex_5_2b_policy`), `sust_hasSum_le_of_partial` |
| p. 776 | Utility is bounded; consumption falls | `cake_utility_hasSum`, `cake_decreasing` |
| p. 776 | Market: `p̂_{t+1}/p̂_t = βc_t/c_{t+1}`, constant `p̂`, market = planner | `cake_market_foc`, `hotelling_price_max`, `hotelling_price_const`, `cake_market_equilibrium` |
| p. 776 | Spot price grows at the real interest rate (Hotelling rule) | `hotelling_rule` |
| p. 777 | Positive Hotelling rent | `hotelling_rent_pos` |
| p. 777 | Dasgupta–Heal: `e_t = (1 − β)β^tR₀`, `k_{t+1} = αβy_t` | `dhOut`, `dhK`, `dh_saving`, `dh_feasible`, `dh_optimal`, `dh_summable`; auxiliary `dh_log_out`, `dh_log_cake`, `dh_log_k_bound` |
| p. 777 | `g = γ_z g^αβ^ν = (γ_zβ^ν)^{1/(1−α)}` | `dh_growth_rec`, `dh_bgp`, `dh_growth_tendsto` |
| p. 777 | `1 + r = g/β`; `r > 0` iff `g > β` | `dh_interest`, `dh_interest_tendsto`, `dh_interest_pos_iff` |
| p. 777 | `p_t = νy_t/e_t` grows at `1 + r` | `dh_hotelling` |
| p. 778 | Hotelling with extraction costs | `hotelling_cost_indifference`, `hotelling_cost_rule` |
| p. 778 | Empirical assessment of the Hotelling rule, volatility | not formalised: empirical discussion |

## §25.5.3 Complementarity and technical change (`Leontief`, `FactorTechnology`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 779 | Leontief economy; `Ak_t^α = e_t` at all dates | `leontiefY`, `leontiefC`, `LeontiefFeasible`, `leontief_feasible_exists`, `leontief_no_idle_capital`, `leontief_optimal_no_idle`, `leontief_no_waste`, `leontief_optimal_tight`; at `t = 0`: `leontief_e0_infeasible` |
| p. 779 | `e` first increases and then falls | the fall: `leontief_eventually_declines`; the rise when the resource is abundant: `leontief_policy_step`, `leontief_abundant` (reuses SLP `log_policy_optimal`); the hump for finite `R` is not formalised (the book argues "without fully solving the model") |
| p. 779 | CES production with factor-augmenting technologies; `ε = 0` is Leontief | `cesY`, `cesY_rpow`; the Leontief limit is not formalised |
| p. 779, fn. 27 | Solow growth accounting | not formalised: cited from Chapter 2 |
| p. 780, (25.33)–(25.34) | Backing out `A_t`, `A_{et}` from shares | corrected: `ces_share_e`, `ces_share_l`, `ces_exponent`, `eq_25_33`, `eq_25_34`; as printed: `eq_25_33_printed`, `eq_25_34_printed`, `eq_25_34_printed_false`, `eq_25_34_printed_growth` |
| pp. 780–781, Figures 25.10–25.11, fn. 28–29 | U.S. fossil energy, shares and measured technologies | not formalised: data |
| pp. 781–782 | Endogenous directed technology (Romer, Aghion–Howitt) | not formalised: narrative |
| p. 782, (25.35) | Technology menu; reduced-form CES with higher elasticity | `menu_key`, `menu_reduced_le`, `menu_reduced_attained`, `menu_elasticity` |
| pp. 782–783 | Taking stock | not formalised: narrative |

## Auxiliary (`Basics`)

| Source | Claim | Lean |
| --- | --- | --- |
| — | Tangent-line bounds for `log` and powers | `sust_log_le_tangent`, `sust_log_lt_tangent`, `sust_tangent_le_rpow`, `sust_tangent_lt_rpow`, `sust_rpow_lt_tangent` (with `ces_rpow_le_tangent`, `ces_tangent_le_rpow` from `RealExchangeRate`) |
