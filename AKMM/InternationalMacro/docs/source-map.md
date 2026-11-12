# Source map: AKMM Chapter 23

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 23, International Macroeconomics (Giancarlo Corsetti, Luca Dedola and
Simon Lloyd), pp. 693–728 (no appendix). Page references are the draft's running heads. Lean
names are relative to `AKMM.InternationalMacro`. Departures from the book are in
[corrections](corrections.md).

Reused from dependencies. Obstfeld–Rogoff `RealExchangeRate` (`ObstfeldRogoff.RealExchangeRate.CESIndex`):
`cesIndex` (the Armington aggregator (23.2)), `cesPrice`, `cesDenom`, `cesDemandT`, `cesDemandN`,
`cesIndex_demand`, `cesIndex_le_div_price` (duality), `cesPrice_rpow_one_sub`, `cesPrice_pos`,
`cesDenom_pos`, `cesPrice_strictMonoOn`, `cesPrice_logDeriv_at_one`. Obstfeld–Rogoff
`StickyPriceModels`: `blocPriceIndex` (the CPI (23.4)), `blocPriceIndex_pos`, `blocPriceIndex_rpow`,
`cesDemand` (the demand `(p/P)^{−φ}C` of (23.3)), `cesDemand_pos`, `hasDerivAt_log_bloc`
(log-linearised CPI), `log_demand_exact`. Obstfeld–Rogoff `IntertemporalTrade`
(`Stability`): `zeta`, `zetaStar`, `hasDerivAt_netImports`, `marshall_lerner`. Obstfeld–Rogoff
`SmallOpenEconomyDynamics` (`StochasticConsumption`): `quadMU`, `hall_martingale`,
`hall_condExp_future`. Miao `CompleteMarkets` (`Miao.CompleteMarkets`): the event tree `BPTree`,
`bp_condExp`, `bp_condExp_succ`, `bp_condExp_sub_fun`, `bp_markovTree`, `bp_markovPr`,
`bp_detTree`. Not used: Obstfeld–Rogoff `InternationalFinancialMarkets` (its global risk sharing
and planner results are for one-good economies; AKMM's (23.12)–(23.13) involve the real exchange
rate of Armington CPIs and are derived directly from the Euler equations on Miao's tree).

## §23.1 Introduction and national accounting (pp. 693–696) — `Accounting`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 694 | `Y = C + I + G + NX` (Chapter 1) | hypothesis of `accounting_saving` |
| p. 695 | `S = Y − G − C = I + NX` | `accounting_saving` |
| p. 694, fn 4 | `CA = NX + NFI + NUT`; `CA ≃ NX` when `NFI`, `NUT` small | `accounting_ca_sub_nx` |
| pp. 694–695 | `CA + FA + KA = 0`; `CA ≃ −FA` | `accounting_ca_add_fa` |
| p. 695 | Trade deficits are financed by capital inflows; deficit = saving below investment | `accounting_deficit_financed` |
| pp. 694–696, Fig 23.1, fns 2–3, 5–7 | BOP data, global imbalances, small vs large economies | not formalised: data and narrative |
| §23.1.2, pp. 695–696 | GDP per capita, population, country groups | not formalised: data |

## §23.2 International business-cycle facts (pp. 696–705)

| Source | Claim | Lean |
| --- | --- | --- |
| Facts 1–7, Tables 23.1–23.2, Fig 23.2 | Business-cycle moments around the world | not formalised: data |
| pp. 699–700 | Feldstein–Horioka, home-bias, consumption-correlation puzzles | not formalised: empirical discussion |
| p. 701 | LOOP `P_i = 𝓔P*_i`; PPP `P = 𝓔P*`; `Q = 𝓔P*/P`; PPP iff `Q = 1` | `accounting_ppp_iff` |
| p. 701 | LOOP plus identical baskets implies PPP | `ppp_same_basket`, `ppp_iff_same_basket` |
| p. 702 | `Δq = Δe + π* − π`; relative PPP iff `Δe = π − π*` | `accounting_rer_log_change`, `accounting_relative_ppp_iff` |
| pp. 702–704, Figs 23.3–23.4, fns 13–14 | Exchange-rate disconnect, Meese–Rogoff, PPP, Backus–Smith, Mussa puzzles | not formalised: empirical discussion |
| p. 703 | Terms of trade `T = P_F/(P*_H𝓔)` | definition (`pF / pH` with `𝓔 = 1`) |
| §23.2.3, Fig 23.5 | SVAR evidence on productivity shocks | not formalised: empirical results |

## §23.3.1 Preferences and technology (pp. 705–708) — `Armington`, `Substitutes`, `PPP`

| Source | Claim | Lean |
| --- | --- | --- |
| (23.1) | Expected utility with CRRA `u` | used in `env_crra`, `eq_23_13`, `eq_23_16` |
| (23.2) | Armington aggregator | `CESIndex.cesIndex` (imported) |
| (23.3), (23.4) | Demands and CPI from expenditure minimisation | `eq_23_3_spending`, `eq_23_3_index`, `eq_23_3_cost_min`, `eq_23_4_least_cost`, `armington_demand_eq` |
| (23.4), (23.5) | CPI homogeneous; `P = p_H P(1, T)` | `armington_price_homog` |
| fn 15 | Substitutes/complements via the cross partial (corrected) | `subst_hasDerivAt_x`, `subst_hasDerivAt_xy`, `subst_cross_partial_pos`, `subst_gross_substitutes`, `subst_gross_complements`, `substDemandH_eq`, `substSum_pos` |
| p. 707 | Market clearing `Y_H = c_H + c*_H`, `Y_F = c_F + c*_F` | `ss_walras`; hypotheses of `nx_identity`, `eq_23_15` |
| (23.6) | Relative demand `1/T = (a/(1−a))^{1/φ}(c_H/c_F)^{−1/φ}` (both countries) | `eq_23_6` |
| (23.7), (23.8) | `Q = P*/P`; `Q^{1−φ} = (a*_H + a*_F T^{1−φ})/(a_H + a_F T^{1−φ})` | `eq_23_8`, `eq_23_8_rpow` |
| p. 707 | PPP only with LOOP and identical baskets | `ppp_iff_same_basket` |
| p. 708 | `a_H > 1/2`: positive `Q`–`T` co-movement; `a_H = 1/2`: PPP | `ppp_strictMonoOn`, `ppp_strictAntiOn`, `ppp_strictMonoOn_iff`, `ppp_symmetric`, `ppp_ratio_lt`, `ppp_at_one` |
| p. 708 | Perfect `Q`–`T` correlation; non-traded goods break it | `eq_23_8` (Q a function of T); remedy not formalised: narrative |
| fns 16–17 | Notation; other sources of PPP deviations | not formalised: narrative |

## §23.3.2 Financial markets (pp. 708–714) — `RiskSharing`, `Envelope`, `NetExports`, `BondEconomy`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 709 | Budget with Arrow–Debreu securities; Euler (23.9) | hypotheses `heuler` (see correction 11) |
| p. 709, (23.10) | Riskless return `1/R = βEₜ[u′(C′)]/u′(C)`, home and foreign | `eq_23_10`, `rs_condExp_one` |
| p. 709 | `R_t ≥ 1` (corrected: only `R > 0`) | `rs_return_pos`, `rs_return_lt_one` |
| (23.11) | Real UIP | `eq_23_11` |
| (23.12) | State-by-state risk sharing | `eq_23_12` |
| p. 710 | `κ₀` constant over time | `rs_kappa_const` |
| (23.13) | `Q = κ₀(C/C*)^σ` | `eq_23_13` |
| fn 21 | Correlation of relative consumption and RER is one | `tot_cm_backus_smith` |
| p. 711 | Complete markets are first best; closed-form solution procedure | not formalised: narrative |
| (23.14) | Trade balance (sign corrected) | `eq_23_14_sign`, `nx_identity` |
| (23.15) | Balanced trade iff `C = (p_H/P)Y_H` | `eq_23_15` |
| p. 711 | `(p_H/P)^{1−φ} = 1/(a_H + (1−a_H)T^{1−φ})` | `ppp_relPrice` |
| p. 711, fns 23–24 | Autarky solved period by period; interest rates clear saving markets | not formalised: narrative |
| (23.16) | `W = χ*/χ = (C/C*)^σ/Q`; constant `= 1/κ₀` under complete markets | `eq_23_16`, `rs_wealth_const` |
| Box, p. 712 | Maximum utility `u(Y/P)`; `dV/dY = u′(Y/P)/P = χ`; `χ` decreasing | `env_value`, `env_hasDerivAt`, `env_chi_strictAntiOn`, `env_crra` |
| Box, p. 712 | Dynamic interpretation of `χ` | not formalised: narrative |
| p. 713 | Bond-economy budget; trade balance `(QB − B₋)/P`; `ca = tb + iQB/P` | `accounting_bond_trade_balance`, `accounting_bond_current_account` |
| (23.17) | Bond Euler equation | hypotheses `he`, `hes` of `eq_23_18` |
| (23.18) | Real UIP in the bond economy | `eq_23_18` |
| (23.19) | Covariance form (corrected) | `eq_23_19`, `bondCov`, `eq_23_19_printed_counterexample`, `bondCoinTree`, `bondCoinTree_condExp` |
| (23.20) | Wedge `ε = χ′/χ − χ*′/χ*`; `Eₜ[ε] = 0` | `eq_23_20`, `bond_wedge_mean_zero` |
| fn 25 | Borrowing constraint not binding | not formalised: assumption of the approximation |

## §23.3.3 Solving the model (pp. 714–715) — `SteadyState`, `LogLinear`, `BondEconomy`, `UnitRoot`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 714 | Symmetric non-stochastic steady state `Q = T = 1`: existence | `ss_exists`, `ss_cm_exists`, `ss_excess_eq`, `ss_equilibrium_iff`, `ss_demand_one`, `ss_walras`, `ssExcess`, `ssExcessF` |
| p. 714 | Uniqueness (added): unique for `φ ≥ 1/2`; multiple equilibria for `a = 9/10`, `φ = 1/4` | `ss_unique`, `ss_multiple` |
| (23.21) | `Q̂ = (2a_H − 1)T̂` (exact derivative) | `eq_23_21`, `loglin_rer`, `loglinP`, `loglinP_pos`, `loglinP_zero`, `loglinP_hasDerivAt` |
| (23.22) | `Ŵ = σ(Ĉ − Ĉ*) − Q̂` (exact in logs) | `eq_23_22` |
| p. 714 | `Eₜ[Ŵ_{t+1} − Ŵ_t] = Eₜ[ε̂] = 0` (sign corrected) | `bond_wealth_loglin` |
| pp. 714–715 | Linearised relative wealth is non-stationary (unit root, `βR = 1`) | `unitroot_hall_form`, `unitroot_martingale`, `unitroot_forecast`, `unitroot_innovation` |
| p. 715 | Debt-elastic discounting restores stationarity | `unitroot_uzawa_contrast` (forecast recursion); Uzawa model not formalised |
| p. 715, fn 26 | The nonlinear model drifts around zero but is stationary | not formalised: no proof given (survey: high difficulty) |
| p. 715, fn 27 | Continuum of countries; Uzawa preferences; holding costs | not formalised: narrative |

## §23.3.4 Relative demand and relative supply (pp. 715–718) — `LogLinear`, `TermsOfTrade`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 715 | `Ŷ_H + Ŷ*_F = Ĉ + Ĉ*` for any market structure | `loglin_world`, `loglin_DH`, `loglin_DF`, `loglinDH`, `loglinDF` |
| (23.23) | Relative demand (exact derivative) | `eq_23_23`, `loglin_demand`, `loglin_log_weighted`, `loglin_hasDerivAt_of_log`, `loglin_exp_ray` |
| (23.24) | Wealth and substitution channels | `eq_23_24`, `loglin_coef_eq` |
| fn 28 | The `T̂` coefficient is positive and increasing in `φ` | `fn_28` |
| p. 716 | Only substitution with `Ŵ = 0` or `a_H = 1/2` | `tot_no_home_bias` |
| p. 716 | Relative supply `Ŷ_H − Ŷ*_F` | hypotheses `hclear` |
| (23.25) | Autarky wealth gap (exact derivative) | `eq_23_25`, `loglin_autarky_cons` |
| (23.26) | Autarky relative demand `[1 − 2a(1 − φ)]T̂` | `eq_23_26`, `eq_23_26_of_24_25` |
| p. 717 | Coefficient positive if `a_H = 1/2`; negative iff `φ < 1 − 1/(2a_H)` | `tot_rd_coefficient` |
| p. 717, Fig 23.6 | Slopes of RD and RD′ (corrected) | `tot_rd_slope` |
| p. 717 | With strong complementarity: TOT improve, RER appreciates, relative consumption rises (Backus–Smith) | `tot_fa_backus_smith` |
| fn 30 | `a_H → 1`: `Q̂ = (Ŷ_H − Ŷ*_F)/(2φ − 1)` | `fn_30` |
| (23.27) | Bond-economy wealth gap (exact derivative; scaling corrected) | `eq_23_27`, `loglin_bond_cons`, `loglinBondCons`, `loglin_bond_printed` |
| p. 718 | Intertemporal trade attenuates or magnifies wealth effects | not formalised: narrative (dynamic bond economy) |

## §23.3.5 Transmission (pp. 718–720) — `TermsOfTrade`, `NetExports`

| Source | Claim | Lean |
| --- | --- | --- |
| (23.28) | Complete-markets TOT (relative supply corrected) | `eq_23_28`, `tot_cm_denom_pos` |
| p. 718 | TOT worsen and RER depreciates after a home boom | `tot_cm_worsen` |
| p. 718 | Coefficient vanishes as `φ → ∞`, largest as `φ → 0` | `tot_cm_coef_strictAntiOn`, `tot_cm_tendsto_atTop`, `tot_cm_tendsto_zero`, `tot_cm_coef_lt` |
| (23.29) | Autarky TOT (relative supply corrected) | `eq_23_29`, `tot_fa_degenerate` |
| p. 719 | TOT worsen iff `φ > 1 − 1/(2a_H)` | `tot_fa_worsen_iff`, `tot_fa_threshold` |
| p. 719 | Cole–Obstfeld: identical at `σ = φ = 1` | `tot_cole_obstfeld` |
| fn 31 | Value of relative output constant at `σ = φ = 1` | `fn_31` |
| p. 719 | Net exports `Ŷ_H − (1 − a)T̂ − Ĉ` | `nx_loglin`, `nx_identity` |
| (23.30) | Notional asset accumulation under complete markets | `eq_23_30` |
| (23.31) | Net exports positive after TOT worsening iff `φ > 1/σ + (1/(2a))(1 − 1/σ)` | `eq_23_31` |
| p. 720 | `σ = 1`: gross substitutability `φ > 1` | `nx_log_utility` |
| p. 720, fn 32 | GE counterpart of Marshall–Lerner | `nx_marshall_lerner`, `nx_imports_hasDerivAt`, `nxImportsHome`, `nxImportsForeign`, `nx_ml_limit` |
| p. 720 | Economics of the deficit with `φ < 1`; bond-economy analog | not formalised: narrative |

## §23.4 The production economy (pp. 720–722) — `Production`

| Source | Claim | Lean |
| --- | --- | --- |
| (23.32) | Preferences with labour disutility | definitions (used in `eq_23_33`) |
| (23.33) | Labour supply (exact in logs) | `eq_23_33` |
| (23.34) | Production function (exact in logs) | `eq_23_34` |
| (23.35) | AR(1) productivity | not formalised: used only in the numerical exercises |
| (23.36) | Labour demand (corrected), zero profits | `prod_labour_demand`, `prod_profit`, `eq_23_36_printed_counterexample`, `eq_23_36_log`, `prod_relPrice_loglin` |
| (23.37) | Relative supply | `eq_23_37` |
| p. 722 | CM slope negative and independent of openness | `prod_cm_slope` |
| (23.38) | Autarky relative supply | `eq_23_38` |
| p. 722 | Slope sign `σ ≷ 1`; independent of TOT at `σ = 1` | `prod_fa_slope_sign` |
| p. 722 | Global output `(1 + η)/(1 − α + η + ασ)(Ẑ + Ẑ*)` | `prod_global_output` |
| fn 33 | Heathcote–Perri | not formalised: citation |

## §23.5–§23.6 (pp. 722–728)

| Source | Claim | Lean |
| --- | --- | --- |
| §23.5, Fig 23.7, fns 34–38 | Calibrated impulse responses (`φ = 1.5, 0.3, 3`; AR(1)/AR(2) productivity; Uzawa bond economy) and the qualitative claims read off them | not formalised: calibrated simulations; figure claims deferred |
| §23.6, fns 39–40 | Richer frameworks (NOEM, dominant currency, capital, non-tradables, firm dynamics) | not formalised: narrative |
