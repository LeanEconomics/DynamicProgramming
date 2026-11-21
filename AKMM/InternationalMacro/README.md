# AKMM Chapter 23: International Macroeconomics, in Lean

This is the `AKMM/InternationalMacro` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 23 (by Giancarlo Corsetti, Luca Dedola and Simon Lloyd) of Marina Azzimonti, Per Krusell,
Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 693–728,
cited by the draft's pages. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 23 builds the two-country Armington model of international business cycles: national
accounts, CES demands and the CPI, the real exchange rate and the terms of trade, three
financial-market structures (complete markets, financial autarky, a single bond), the
log-linearised relative demand–relative supply framework, the equilibrium terms of trade, the
general-equilibrium Marshall–Lerner condition, and the production economy. Every numbered
equation the text derives is proved; each log-linear equation is an exact derivative at the
symmetric steady state; the risk-sharing and UIP results are proved on Miao's event tree from the
Euler equations; the unit root of the linearised bond economy is Hall's martingale theorem; the
symmetric steady state is shown to exist and, for `φ ≥ 1/2`, to be the unique autarky
equilibrium, while strong complementarity admits a second equilibrium. Not formalised: data,
stylised facts and the empirical discussion (§23.1.2, §23.2), the calibrated impulse responses of
§23.5 and the narrative of §23.6. The project depends on Obstfeld–Rogoff's `RealExchangeRate` (the
CES index and duality), `StickyPriceModels` (the bloc CPI, CES demand and their log-derivatives),
`IntertemporalTrade` (Marshall–Lerner) and `SmallOpenEconomyDynamics` (Hall's martingale), and on
Miao's `CompleteMarkets` (the event tree). Twelve printed errors are corrected, with Lean
counterexamples to footnote 15's cross-partial criterion, `R ≥ 1`, the covariance form (23.19) and
the labour demand (23.36), as recorded in [corrections](docs/corrections.md); every book item is
located in the [source map](docs/source-map.md). The library contains **133 theorems**.

* **National accounts** (§23.1.1, §23.2.2): `S = I + NX`, `CA ≃ NX`, `CA ≃ −FA` with exact gaps
  (`accounting_saving`, `accounting_ca_sub_nx`, `accounting_ca_add_fa`,
  `accounting_deficit_financed`); `Δq = Δe + π* − π` and relative PPP
  (`accounting_rer_log_change`, `accounting_relative_ppp_iff`); the bond-economy trade balance and
  current account (`accounting_bond_trade_balance`, `accounting_bond_current_account`).
* **Armington demands and the CPI** (§23.3.1): (23.3)–(23.4) by expenditure minimisation
  (`eq_23_3_spending`, `eq_23_3_index`, `eq_23_3_cost_min`, `eq_23_4_least_cost`,
  `armington_price_homog`); (23.6) (`eq_23_6`); footnote 15 corrected
  (`subst_cross_partial_pos`, `subst_gross_substitutes`, `subst_gross_complements`).
* **The real exchange rate and PPP** (§23.3.1): (23.8) (`eq_23_8`, `eq_23_8_rpow`); PPP iff
  identical baskets (`ppp_iff_same_basket`); `Q` increasing in `T` iff home bias
  (`ppp_strictMonoOn_iff`, `ppp_symmetric`); `(p_H/P)^{1−φ}` (`ppp_relPrice`).
* **Complete markets** (§23.3.2): (23.10)–(23.13) (`eq_23_10`, `eq_23_11`, `eq_23_12`,
  `rs_kappa_const`, `eq_23_13`); `R > 0` but not `R ≥ 1` (`rs_return_pos`, `rs_return_lt_one`);
  (23.16) (`eq_23_16`, `rs_wealth_const`).
* **The marginal utility of income** (box, p. 712): `env_value`, `env_hasDerivAt`,
  `env_chi_strictAntiOn`, `env_crra`.
* **The bond economy** (§23.3.2–23.3.3): (23.18)–(23.20) with the corrected covariance form
  (`eq_23_18`, `eq_23_19`, `eq_23_19_printed_counterexample`, `eq_23_20`, `bond_wedge_mean_zero`);
  the linearised wedge and wealth gap (`bond_wealth_loglin`); the unit root
  (`unitroot_martingale`, `unitroot_forecast`, `unitroot_innovation`, `unitroot_uzawa_contrast`).
* **The steady state** (p. 714): existence (`ss_exists`, `ss_cm_exists`, `ss_walras`), uniqueness
  for `φ ≥ 1/2` (`ss_unique`) and multiple equilibria for `a = 9/10`, `φ = 1/4` (`ss_multiple`).
* **The log-linear system** (§23.3.3–23.3.4): (23.21)–(23.27) as exact derivatives (`eq_23_21`,
  `eq_23_22`, `eq_23_23`, `loglin_world`, `eq_23_24`, `fn_28`, `eq_23_25`, `eq_23_26`,
  `eq_23_27`).
* **Equilibrium terms of trade** (§23.3.5): (23.28)–(23.29) with signs and limits (`eq_23_28`,
  `tot_cm_worsen`, `tot_cm_tendsto_atTop`, `tot_cm_tendsto_zero`, `eq_23_29`,
  `tot_fa_worsen_iff`); Cole–Obstfeld (`tot_cole_obstfeld`, `fn_31`); Figure 23.6 corrected
  (`tot_rd_slope`); Backus–Smith patterns (`tot_cm_backus_smith`, `tot_fa_backus_smith`);
  footnote 30 (`fn_30`).
* **Net exports and Marshall–Lerner** (§23.3.5): (23.14)–(23.15) (`eq_23_14_sign`, `eq_23_15`,
  `nx_identity`, `nx_loglin`); (23.30)–(23.31) (`eq_23_30`, `eq_23_31`, `nx_log_utility`); the
  classic condition for Armington imports (`nx_marshall_lerner`, `nx_ml_limit`).
* **The production economy** (§23.4): (23.33)–(23.38) (`eq_23_33`, `eq_23_34`,
  `prod_labour_demand`, `eq_23_36_printed_counterexample`, `eq_23_37`, `prod_cm_slope`,
  `eq_23_38`, `prod_fa_slope_sign`) and global output (`prod_global_output`).

All names are in the namespace `AKMM.InternationalMacro`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Accounting](AKMMInternationalMacro/Accounting.lean) | 9 | National accounts, RER decomposition, bond-economy current account (AKMM §23.1.1, §23.2.2, pp. 694–702, 713) |
| [Armington](AKMMInternationalMacro/Armington.lean) | 7 | (23.2)–(23.6): CES demands, the CPI and duality (AKMM §23.3.1, pp. 706–707) |
| [Substitutes](AKMMInternationalMacro/Substitutes.lean) | 7 | Footnote 15 corrected: the cross partial and gross substitutes (AKMM p. 706) |
| [PPP](AKMMInternationalMacro/PPP.lean) | 11 | (23.7)–(23.8), PPP and home bias (AKMM §23.3.1, pp. 707–708, 711) |
| [Envelope](AKMMInternationalMacro/Envelope.lean) | 4 | The multiplier as the marginal utility of income (AKMM box, p. 712) |
| [SteadyState](AKMMInternationalMacro/SteadyState.lean) | 8 | The symmetric steady state: existence, uniqueness, multiplicity (AKMM p. 714) |
| [LogLinear](AKMMInternationalMacro/LogLinear.lean) | 24 | (23.21)–(23.27) as exact derivatives (AKMM §23.3.3–23.3.4, pp. 714–718) |
| [TermsOfTrade](AKMMInternationalMacro/TermsOfTrade.lean) | 19 | (23.28)–(23.29), Cole–Obstfeld, Figure 23.6, fns 21, 30, 31 (AKMM pp. 716–719) |
| [NetExports](AKMMInternationalMacro/NetExports.lean) | 10 | (23.14)–(23.15), (23.30)–(23.31), Marshall–Lerner (AKMM pp. 711, 719–720) |
| [Production](AKMMInternationalMacro/Production.lean) | 12 | (23.32)–(23.38) and global output (AKMM §23.4, pp. 720–722) |
| [RiskSharing](AKMMInternationalMacro/RiskSharing.lean) | 10 | (23.9)–(23.13), (23.16): complete markets on the event tree (AKMM pp. 708–712) |
| [BondEconomy](AKMMInternationalMacro/BondEconomy.lean) | 7 | (23.17)–(23.20) and the linearised wedge (AKMM pp. 713–714) |
| [UnitRoot](AKMMInternationalMacro/UnitRoot.lean) | 5 | The linearised bond economy is a martingale (AKMM pp. 714–715) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
