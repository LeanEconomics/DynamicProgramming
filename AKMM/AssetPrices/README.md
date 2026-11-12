# AKMM Chapter 16: Asset Prices, in Lean

This is the `AKMM/AssetPrices` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 16 (Asset prices, by Monika Piazzesi and Martin Schneider) of Marina Azzimonti, Per
Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), cited by
the draft's pages. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 16 studies economies with many assets: the planner and Arrow–Debreu conditions of an
endowment economy and the First Welfare Theorem, sequential trading, two-period no-arbitrage
theory (the fundamental theorem of asset pricing, state prices, the law of one price), optimal
portfolios and subjective state prices, the stochastic discount factor and risk-neutral pricing,
the representative agent, dynamic trading and Euler equations, the Mehra–Prescott equity premium,
the lognormal consumption CAPM and the excess volatility of stock prices. Every numbered equation
(16.1)–(16.32) and every derivation and precise claim of the text is proved; the chapter has no
numbered theorems. The fundamental theorems are proved from Stiemke's lemma, both for two periods
and on a finite event tree, and the existence of an optimal portfolio under no arbitrage is
proved by compactness of the budget set. Not formalised: the data, Tables 16.1–16.2, Figures
16.1–16.5 (the claim read off Figure 16.4 is deferred), the narrative, and the infinite-horizon
versions of the sequential-trading results (cited from Miao). The project depends on Miao's
`CompleteMarkets` (Stiemke's lemma, finite expectations, Gaussian integrals) and
`RecursiveUtility` (the Epstein–Zin riskless rate), on Sargent and Stachurski's
`StochasticDiscounting` (price–dividend ratios and the spectral radius) and on Obstfeld and
Rogoff's `InternationalFinancialMarkets` (spanning). Eight printed errors are corrected, with Lean
counterexamples to (16.17), to the budget-set identity (16.14) and to the existence claim without
a consumption bound, as recorded in [corrections](docs/corrections.md); every book item is located
in the [source map](docs/source-map.md). The library contains **131 theorems**.

* **Endowment economy** (§16.3): the planner's conditions (16.1) and (16.3), the envelope
  theorem (16.2) (`eq_16_1`, `eq_16_2`, `eq_16_3`); the Arrow–Debreu conditions (16.4)–(16.5)
  (`eq_16_4`, `eq_16_5`); the weights `λᵢ = 1/αᵢ` (`en_weights_match`) and the First Welfare
  Theorem for concave utilities (`en_fwt_planner`, `en_fwt_pareto`).
* **Two-period no arbitrage** (§16.4): the arbitrage definitions (`tp_isArbitrage_iff_book`,
  `tp_noArbitrage_iff_free`); the **fundamental theorem** (`tp_ftap`); positivity of Arrow prices,
  the law of one price and (16.12)–(16.13) (`tp_arrow_price_pos`, `tp_law_of_one_price`,
  `eq_16_12`, `eq_16_13`); uniqueness of state prices iff `rank D = S`
  (`tp_statePrices_unique_iff_rank`); Examples 1–2 (`ex1_noArbitrage_iff`, `ex1_value_pos`,
  `ex2_statePrices_iff`, `ex2_disagreement`).
* **Optimal portfolios** (§16.4): optimum ⇒ no arbitrage (`tp_noArbitrage_of_optimal`); no
  arbitrage ⇒ an optimum exists, by compactness (`tp_budgetPos_isCompact`, `tp_exists_optimal`,
  `tp_no_optimal_without_nonneg`); (16.14), corrected (`eq_16_14`, `eq_16_14_counterexample`,
  `tp_budget_complete`); the first-order conditions and (16.15) (`tp_portfolio_foc`, `eq_16_15`);
  agreement under complete markets (`tp_agreement_complete`).
* **The SDF** (§16.4): `p = E[dM]`, `1 = E[RM]` (`sdf_price`, `sdf_return`); (16.16)–(16.18)
  (`eq_16_16`, `eq_16_17`, `eq_16_17_printed_counterexample`, `eq_16_18`); risk-neutral
  probabilities (`riskNeutral_sum`, `riskNeutral_unique_iff`).
* **Equilibrium and the representative agent** (§16.3–16.4): sequential = Arrow–Debreu equilibrium
  under complete markets (`eq_seq_to_ad`, `eq_ad_to_seq`); the representative agent
  (`eq_repAgent`, `eq_repAgent_statePrice`).
* **Dynamic trading** (§16.5): the **dynamic fundamental theorem** on a finite event tree
  (`dt_ftap_deflator`, `dt_ftap`, `dt_statePrices_unique`); the Euler equations (16.19)–(16.23)
  and the conditional premium (`eu_foc`, `eq_16_19`, `eq_16_21`, `eq_16_23`,
  `eu_conditional_premium`).
* **Mehra–Prescott** (§16.6): the stationary distribution (`mp_stationary_iff`); the unique
  price–dividend ratio `(I − βA)⁻¹βA𝟙` (`mp_pd_unique`, `mp_pd_series`); returns and the moments
  of fn. 5 (`eq_16_25`, `fn5_autocorr`).
* **Lognormal model** (§16.7): (16.29)–(16.30) (`eq_16_29`, `eq_16_30`); the riskless rate rises
  with `γ` iff `γ < μ_g/σ_g²` (`lg_rf_mono_iff`); `γ ≥ 16.36` from Table 16.1
  (`lg_gamma_bound`); Epstein–Zin separation (`ez_rf_smoothing`, `ez_power_case`).
* **Excess volatility** (§16.8): the constant price–dividend ratio (16.31) and (16.32)
  (`iid_pd_unique`, `eq_16_31`, `iid_lognormal_pd`, `iid_return_var`).

All names are in the namespace `AKMM.AssetPrices`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [TwoPeriod](AKMMAssetPrices/TwoPeriod.lean) | 18 | Arbitrage, state prices and the fundamental theorem (§16.4, pp. 473–476) |
| [Examples](AKMMAssetPrices/Examples.lean) | 12 | Examples 1 and 2 (§16.4, pp. 476–480) |
| [Portfolio](AKMMAssetPrices/Portfolio.lean) | 18 | Optimal portfolios, (16.14) and subjective state prices (§16.4, pp. 477–480) |
| [SDF](AKMMAssetPrices/SDF.lean) | 13 | The stochastic discount factor, (16.16)–(16.18) (§16.4, pp. 480–482) |
| [Endowment](AKMMAssetPrices/Endowment.lean) | 15 | Planner, Arrow–Debreu and the First Welfare Theorem (§16.3, pp. 469–471) |
| [Equilibrium](AKMMAssetPrices/Equilibrium.lean) | 6 | Sequential = Arrow–Debreu equilibrium; the representative agent (pp. 472, 482) |
| [DynamicTree](AKMMAssetPrices/DynamicTree.lean) | 7 | The dynamic fundamental theorem on a finite tree (§16.5, pp. 482–483) |
| [Euler](AKMMAssetPrices/Euler.lean) | 7 | First-order conditions and (16.19)–(16.23) (§16.5, pp. 483–485) |
| [MehraPrescott](AKMMAssetPrices/MehraPrescott.lean) | 10 | The two-state equity premium model (§16.6, pp. 485–488) |
| [Lognormal](AKMMAssetPrices/Lognormal.lean) | 14 | (16.29)–(16.30) and the numbers of p. 490 (§16.7, pp. 488–490) |
| [IidGrowth](AKMMAssetPrices/IidGrowth.lean) | 7 | The constant price–dividend ratio (16.31)–(16.32) (§16.8, pp. 490–492) |
| [EpsteinZin](AKMMAssetPrices/EpsteinZin.lean) | 4 | Epstein–Zin separates the riskless rate from risk aversion (p. 490) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
