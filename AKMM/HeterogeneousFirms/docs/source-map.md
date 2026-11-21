# Source map: AKMM Chapter 22

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 22, Heterogeneous firms (T. Mukoyama), pp. 663–692, and Appendix 22.A,
pp. 888–896. Page references are the draft's running heads. Lean names are relative to
`AKMM.HeterogeneousFirms`. Departures from the book are in [corrections](corrections.md).

## §22.1 Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 663 | Motivation | not formalised: narrative |

## §22.2 A simple model (`SimpleModel`, `Lognormal`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 664 | Decreasing returns needed; with constant returns the most productive firm takes over | not formalised: narrative |
| p. 664 | Two-stage cost minimisation under CRS: `xᵢ = mᵢx*`, cost `cmᵢ` | `twostage_cost`, `twostage_profit_le`, `twostage_profit_eq` |
| p. 664, (22.1) | The scale problem `max amᵞ − cm` | `eq_22_1`, `simpleScale`, `simple_scale_pos`, `simple_scale_rpow`, `simple_scale_eq` |
| p. 664, (22.2) | First-order condition `am^{γ−1} = c/γ` | `eq_22_2` |
| p. 664 | `yᵢ = (c/γ)mᵢ` | `simple_output_eq` |
| p. 664–665, (22.3)–(22.5) | `Y = (c/γ)M` | `eq_22_3`, `simple_M_eq` |
| p. 665, (22.6) | `A = (∫ a^{1/(1−γ)})^{1−γ}`; `A = (c/γ)M^{1−γ}` | `aggTFP`, `simple_A_eq` |
| p. 665, (22.7) | `M = F(X)` and `Y = AF(X)^γ` | `eq_22_7`, `eq_22_7_M` |
| p. 665 | Inputs are allocated efficiently; misallocation could be corrected by reallocation | `simple_planner`, `simple_planner_A` |
| p. 665, fn. 2 | Cobb–Douglas: unit cost `(r/α)^α(w/(1−α))^{1−α}`, factor prices | `cobbDouglas_unit_cost`, `simple_footnote_2` |
| p. 665 | Lognormal `a`: mean `e^ν` | `lognormal_mean` |
| p. 665, (22.8); App. 22.A.1, p. 888 | `A = exp(ν + γσ²/(2(1−γ)))` | `eq_22_8` |
| p. 665 | Dispersion raises `A` at fixed mean | `lognormal_A_strictMono`; general distributions `aggTFP_ge_mean` |

## §22.3 Firm heterogeneity in the data (`Misallocation`)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 666–671, Figures 22.1–22.8, fn. 4–8; App. 22.A.2, Figures 22.A.1–22.A.3 | BDS size distributions, job flows, entry and exit, concentration, markups | not formalised: data |
| p. 669, (22.9) | Job creation and destruction rates | `jobCreation`, `jobDestruction`, `jobflows_net` |
| p. 676, fn. 14 | In a steady state JC = JD | `jobflows_steady` |

## §22.4 Reallocation and misallocation (`Misallocation`, `Lognormal`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 671 | FHK decomposition of `ΔĀ` | `fhk_decomposition` |
| p. 672 | Without share changes, entry or exit, only within growth | `fhk_within_only` |
| p. 672 | FHK's 45%/55% split | not formalised: data |
| p. 672, (22.10) | `A` with output wedges; `Y = AF(X)^γ` | `wedgeTFP`, `eq_22_10`, `wedge_scale_eq` |
| p. 672 | (22.10) equals (22.6) when `τ ≡ 0` | `wedgeTFP_one` |
| App. 22.A.3, p. 889 | Linear combinations of a bivariate normal | `bivariate_mgf` |
| p. 672, (22.11); App. 22.A.3, pp. 889–892 | `A = exp(ν_a + γ(σ_a² − σ_τ²)/(2(1−γ)))` | `eq_22_11`, `wedge_exponent` |
| p. 673, fn. 9 | `ρ` and `ν_τ` do not matter in this case | `wedge_A_indep` |
| p. 673 | Dispersion in `1 − τ` lowers `A`; (22.11) = (22.8) at `σ_τ = 0` | `wedge_A_strictAnti`; for general distributions `wedge_A_le` |
| p. 673 | Size-dependent policies, regulations | not formalised: narrative |

## §22.5 Hopenhayn–Rogerson (`HopenhaynRogerson`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 673, (22.12) | Flow profit with firing tax | `HRFirm`, `hrLag`, `hrProfit` |
| p. 674, (22.13) | The firm's Bellman equation | `hrT`, `hr_bellman_existsUnique` (contraction `hr_T_sub_le`, `hr_T_dist_le`, `hr_max_sub_le`), `hrValue`, `hr_value_spec` |
| p. 674, (22.14) | Free entry `Wᵉ = c_e + κ`, `Wᵉ = ∫(W(a,0) + c_f)dν` | `hrEntry` |
| p. 675 | Block recursivity: `Wᵉ` depends on `w` only; free entry pins `w` | `hrEntry` (a function of `w`), `hr_fixed_compare`, `hr_value_wage_gap`, `hr_value_lipschitz`, `hr_entry_strictAnti`, `hr_entry_continuous`, `hr_free_entry_unique`, `hr_free_entry_exists` |
| p. 675 | Given `M`, the stationary distribution; `Lᵈ`, `Π`, `R` functions of `M` | `HRStationary`, `hr_stationary_zero`, `hr_stationary_existsUnique`, `hr_stationary_nonneg`, `hr_stationary_linear`, `hr_aggregate_linear` |
| p. 675, (22.15) | Labour supply condition; `M` from `Lᵈ = Lˢ` | `eq_22_15`, `hr_entry_mass` |
| p. 674, fn. 11 | Steady-state interest rate `1/β` | `hr_footnote_11` |
| p. 675–676, Table 22.1, fn. 12–13 | Calibration and firing-tax results | not formalised: calibrated numbers |
| p. 676 | Effect of `τ` on `L` ambiguous; labour productivity falls; JC falls | not formalised: quantitative results |
| p. 677, Table 22.2, fn. 15–16 | Entry-barrier results | not formalised: calibrated numbers |
| p. 677 | Higher `κ` lowers the wage | `hr_entry_barrier_wage`; the three productivity channels are quantitative, not formalised |

## §22.6.1 Monopolistic competition (`MonopolisticCompetition`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 678, (22.16) | Dixit–Stiglitz aggregate | imported `Miao.NewKeynesian.nk_aggY` |
| p. 678, (22.17) | FOC `pᵢ = λyᵢ^{−1/σ}Y^{1/σ}`, `∫pᵢyᵢ = λY`, `λ = P` the price index | `eq_22_17` (from `Miao.NewKeynesian.eq_19_6_foc`, `eq_19_7`); cost minimisation `Miao.NewKeynesian.eq_19_6` |
| p. 678, (22.18) | Inverse demand with `P = 1` | `eq_22_18` |
| p. 678, (22.19) | The monopolist's problem | `eq_22_19`, `mc_revenue_eq` |
| p. 679 | `Y = (c/γ)(σ/(σ−1))M` | `mc_output_eq` |
| p. 679 | Modified `A`; `Y = AM^γ` | `mcTFP`, `mc_aggregate`, `mc_scale_form`, `mc_aggregate_eq` |
| p. 679 | Constant (and some increasing) returns can be accommodated | the hypothesis `γ(σ−1)/σ < 1` of `eq_22_19`, `mc_aggregate` |
| p. 679, (22.20) | First-order condition | `eq_22_20` |
| p. 679, (22.21)–(22.22) | Marginal cost; markup `σ/(σ−1)` | `eq_22_22` |
| p. 679 | De Loecker et al.; three research paths | not formalised: narrative |

## §22.6.2 Oligopoly (`Oligopoly`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 680, (22.23) | Sector CES aggregate | `sectorOutput`, `sectorOutput_rpow` |
| p. 680, (22.24) | Within-sector inverse demand; sector price index | `eq_22_24` |
| p. 680, (22.25) | `pᵢyᵢ = Σ p̂ᵢⱼqᵢⱼ` | `eq_22_25` |
| p. 680, (22.26) | Brand production | the marginal cost `MC` in `eq_22_27` |
| p. 680, (22.27) | Pricing `p̂ = ε/(ε−1)·M` | `eq_22_27` |
| p. 681, (22.28) | `ε(s) = ((1−s)/η + s/σ)^{−1}` | `cournotElas`, `eq_22_28` |
| p. 681, (22.29) | Sales share | `eq_22_29` |
| p. 681 | `ε ∈ [σ, η]`, `ε(0) = η`, decreasing, `ε(1) = σ` | `cournot_endpoints`, `cournot_strictAntiOn`, `cournot_mem_Icc` |
| p. 681 | Symmetric firms; `J = 1` is (22.22); markup falls with `J`; `ε → η` | `cournot_symmetric`, `cournot_symmetric_one`, `cournot_symmetric_mono`, `cournot_symmetric_tendsto`, `markup_strictAnti` |
| p. 681; App. 22.A.4, pp. 892–893 | Bertrand: `ε(s) = η(1−s) + σs` and the same pricing rule | `bertrandElas`, `bertrand_demand_form`, `bertrand_demand_deriv`, `eq_22_A_4`, `bertrand_ratio` (corrected; printed value false: `bertrand_ratio_printed_false`), `bertrand_markup` |
| p. 681 | "The intuition is similar" | `cournot_le_bertrand`, `markup_cournot_ge` (Cournot markups are higher) |

## §22.7 Business cycles and heterogeneous firms (`Granularity`, `GranularLimits`, `Hulten`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 682 | GDP growth is the share-weighted average of firm growth | `granular_growth` |
| p. 682, (22.30) | `σ_Y = σ√(Σ(yᵢ/Y)²)` | `eq_22_30` (shocks uncorrelated with unit variance) |
| p. 682 | Equal sizes: `σ_Y = σ/√N`; `1/√10⁶ = 0.001` | `granular_equal_sizes`, `granular_million`; equal sizes minimise `Σsᵢ²`: `granular_herfindahl_ge` |
| p. 682, fn. 17–18 | Firm volatility 10–20%; Gabaix's estimates | not formalised: data (fn. 18 see corrections) |
| p. 682, §22.7.1, fn. 19 | Aggregate shocks in Hopenhayn–Rogerson; its cyclical performance | not formalised: quantitative, narrative |
| p. 683 | The `1/√N` calculation assumes (i) finite variance, (ii) no input-output networks | (i): see corrections, item 12 (`gabaix_iid_sqrt_tendsto`, `gabaix_iid_infinite_variance`); (ii): `hulten` |
| p. 683, (22.31) | Hulten's theorem with Domar weights | `hulten` |
| p. 683 | Intuition: envelope theorem; sales over value added | `hulten` (lower-bound envelope argument) |
| p. 684, (22.32) | Two-sector example: `Y = a₁(a₂K)^{1−γ}L^γ`, elasticities `1`, `1−γ` | `eq_22_32` |
| p. 684 | Intermediate price, value added `V₂ = (1−γ)Y`, `V₁ = γY`, Domar weights `1`, `1−γ` | `hulten_example_prices` |
| pp. 684–685, (22.33), Figure 22.9, fn. 20 | Pareto firm sizes in the data | not formalised: data |
| p. 685 | Gabaix: under Zipf `σ_Y log N →ᵈ v_ζσ` (convergence in distribution, i.i.d. Pareto sizes) | not formalised: beyond the text (stable-law limit theorem; Mathlib has no generalised CLT, decision 5). The parts that need no stable laws are formalised beyond the text in `GranularLimits` (next rows; corrections, departure 8) |
| p. 682, (22.30), beyond the text | `σ_Y = σ√(ΣSᵢ²)/ΣSᵢ` for the first `N` firms | `gabaixVol`, `gabaixVol_eq_shares`, `gabaix_sqrt_mul_vol` |
| p. 682, beyond the text | i.i.d. sizes with `E[S²] < ∞`: `√N σ_Y → σ√(E[S²])/E[S]` a.s.; `σ_Y → 0` | `gabaix_iid_sqrt_tendsto` (strong law of large numbers), `gabaix_iid_vol_tendsto_zero` |
| p. 684, (22.33), beyond the text | Pareto moments: `E[Sⁿ] = ζtⁿ/(ζ−n)` for `n < ζ`, infinite for `n ≥ ζ` | `gabaix_pareto_density_pow`, `gabaix_pareto_moment`, `gabaix_pareto_not_integrable_pow` |
| p. 685, beyond the text | i.i.d. Pareto sizes, `ζ > 2`: `√N σ_Y → σ(ζ−1)/√(ζ(ζ−2))` a.s. | `gabaix_pareto_iid` |
| p. 685, beyond the text | i.i.d. sizes with `E[S] < ∞ = E[S²]`, e.g. Pareto `1 < ζ ≤ 2`: `√N σ_Y → ∞` a.s. | `gabaix_iid_infinite_variance`, `gabaix_pareto_iid_fat` |
| p. 685, beyond the text | Deterministic rank-size rule `Sₖ = k^{−1/ζ}`; sum–integral comparison | `gabaixRank`, `gabaix_sum_rpow_bounds`, `gabaix_sum_rpow_tendsto`, `gabaix_harmonic_div_log_tendsto` |
| p. 685, beyond the text | Zipf `ζ = 1`: `σ_Y ∝ 1/log N`, `log N · σ_Y → σπ/√6` | `gabaix_zipf_log_tendsto` |
| p. 685, beyond the text | `1 < ζ < 2`: `N^{1−1/ζ}σ_Y → σ(1−1/ζ)√(Σk^{−2/ζ})`; slower than `1/√N` | `gabaix_rank_mid_tendsto`, `gabaix_rank_mid_sqrt_tendsto_atTop` |
| p. 685, beyond the text | `ζ = 2`: `√(N/log N) σ_Y → σ/2` | `gabaix_rank_two_tendsto` |
| p. 685, beyond the text | `ζ > 2`: `√N σ_Y → σ(ζ−1)/√(ζ(ζ−2))` (the `1/√N` law) | `gabaix_rank_thin_tendsto` |
| p. 685, beyond the text | Largest-firm bound `σ_Y ≥ σ maxSᵢ/ΣSᵢ` (pathwise; a.s. for i.i.d. Pareto, any `ζ`, in particular `ζ = 1`); `σ_Y ≤ σ`; Zipf: `σ_Y ≥ σ/(1 + log N)` | `gabaix_vol_ge_share`, `gabaix_pareto_vol_ge_share`, `gabaix_vol_le`, `gabaix_zipf_vol_ge` |
| p. 685 | `1/log 10⁶ ≈ 0.072`; Gabaix's coefficient 0.12 | not formalised: numerical illustration |
| pp. 685–686 | Production networks, Baqaee–Farhi | not formalised: cited |
| App. 22.A.5, p. 894 | The economy: preferences, technologies, market clearing | `hultenNet`, `hultenTech`, `hultenCons`, `hultenUtil`, `hultenGoods`, `hulten_goods_apply` |
| App. 22.A.5, p. 895, (22.A.5) | Consumer's first-order condition, `λ = 1` | hypothesis `hU` of `hulten` |
| App. 22.A.5, p. 895, (22.A.6) | `Y = Σpc = U(c)` (Euler) | `eq_22_A_6` |
| App. 22.A.5, p. 895 | First welfare theorem: the equilibrium solves the planner's problem | imported `StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_3`, used in `hulten` |
| App. 22.A.5, pp. 895–896, (22.A.7)–(22.A.8) | Envelope theorem `dU/daᵢ = μᵢyᵢ/aᵢ`, `μᵢ = pᵢ`; the theorem | `hulten` (with differentiability of the planner's value as a hypothesis); all hypotheses hold in a one-sector economy: `hultenOnePrice`, `hulten_one_price_apply`, `hulten_one_sector` |

## §22.8 Endogenous productivity: Klette–Kortum (`KletteKortum`, `FirmSize`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 686, (22.34) | Preferences; generations perfect substitutes | the objective of `eq_22_36` (the leading generation) |
| p. 687, (22.35)–(22.36) | Equal expenditure shares | `eq_22_36` |
| p. 687 | `C = E exp ∫(log q − log p)`, `PC = E` | `kk_price_index` |
| p. 687, (22.37) | Normalisation `P = 1` | `eq_22_37` |
| p. 688 | Intertemporal problem; Euler equation | `eq_22_38` (Euler along the balanced path) |
| p. 688, (22.38) | `1/(1+r) = β/(1+γ)` | `eq_22_38` |
| p. 688, (22.39) | Limit price `λw` | `kk_limit_price_iff` (from `AKMM.Growth.eq_13_A_26`), `eq_22_39` |
| p. 688, (22.40) | `π = (1 − 1/λ)C` | `eq_22_40` |
| p. 689 | `w₀ = 1` | `kk_wage_normalisation` |
| p. 689, (22.41) | Bellman equation; four scenarios give `1 + η − μ` | `eq_22_41` |
| p. 689, (22.42) | Detrended Bellman equation | `eq_22_42` |
| p. 689, (22.43) | First-order condition `R'(η) = βv` | `eq_22_43` (sufficient for convex `R`) |
| p. 689, (22.44)–(22.46) | Free entry, `μ = η + ν`, labour market | `kk_equilibrium` (corrected entry labour `c_eν`; printed form differs: `kk_labour_printed_false`) |
| p. 690 | Four unknowns, four equations | `kk_equilibrium` (unique `(C₀, μ)` given `η`) |
| p. 690 | Growth rate `μ log λ` | `kk_growth` |
| p. 691 | Gibrat's law, `η − μ = −ν` | `kk_gibrat` |
| p. 691 | Counterfactual predictions; no Pareto tail | not formalised: narrative |
| p. 691–692 | Pareto stationary density, `ζ = −log(1−δ)/log(1+g) > 0` | `pareto_stationary`, `pareto_zeta_pos` |
| p. 692 | `ζ` small when `δ` small or `g` large | `pareto_zeta_mono` |
| p. 692 | New products `ξ`: firm growth `ξ − ν` | `kk_gibrat_xi` |
| p. 691, fn. 21, 23–25 | Literature | not formalised: cited |
| App. 22.A.6, p. 896 | Binomial gains and losses | `binomP`, `binomP_eq_zero`, `binomP_sum`, `fsdT`, `fsd_T_sum`, `fsd_T_eq` |
| App. 22.A.6, p. 896 | `M_{1,t+1}` and `M_{k,t+1}`: from below, stay, from above | `fsd_from_below` (corrected inner bound), `fsd_below_zero` (outer bound), `fsd_stay`, `fsd_from_above` (the `M₁` equation is the case `k = 1`) |
| App. 22.A.6, p. 896 | The printed inner bound `⌊k/2 − h⌋` | counterexample `fsd_printed_bound_false` |
| App. 22.A.6, p. 896 | Look for a stationary `{M_k}`; numerical solution | not formalised: no claim made (the book proposes a computation) |
