# AKMM Chapter 17: Money, in Lean

This is the `AKMM/Money` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 17 (Money, by A. Hornstein and P. Krusell) of Marina Azzimonti, Per Krusell, Alisdair
McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of December 2025), pp. 493–531. The chapter
has no appendix. Pages are cited by the draft's running heads. Run the commands below from this
directory. [Return to the library index](../../README.md).

Chapter 17 studies fiat money:
- money in the Samuelson overlapping-generations economy, with the full classification of its
  equilibria and their welfare ranking;
- why money has no value in dynastic models;
- cash-in-advance, transactions-cost and money-in-utility models, with the Friedman rule;
- hyperinflations, interest-rate pegs and rules, and the cashless limit;
- the consolidated government budget: seigniorage, unpleasant arithmetic, open-market operations
  and the fiscal theory of the price level;
- Kareken–Wallace exchange-rate indeterminacy, and fiat money in the Huggett economy.

Every numbered equation the chapter derives, (17.2)–(17.46), and every precise claim are proved
in the book's setting, including the welfare results the text leaves as an exercise. All proofs
are analytic.

Seven printed errors are corrected:
- inflation under money growth;
- the indexing of (17.14) and (17.43);
- the condition for indeterminacy under (17.40);
- the discount factor of the `i = 0` budget;
- footnote 18;
- a chapter cross-reference.

Four claims need added hypotheses:
- the hyperinflation paths need `m u′(m)` increasing;
- the Laffer maximum needs a condition such as `f(i)i → 0`;
- the fiscal theory needs `τ̃ > g̃`;
- the knife-edge case of footnote 15 is proved only for an affine rule.

Not formalised:
- the data and figures;
- Kiyotaki–Wright (described without equations);
- the existence and convergence of the Kareken–Wallace path with growing stocks (proof cited);
- the extensions with capital.

The corrections are recorded in [corrections](docs/corrections.md), and every book item is
located in the [source map](docs/source-map.md). The library contains **169 theorems**.

* **OLG money** (§17.2.1):
  - the young's problem and the demand (17.3) as the unique optimum (`eq_17_2`, `eq_17_3`);
  - equilibrium as (17.5) (`eq_17_5`), with the explicit classification of all equilibria
    (`olg_classification`): the continuum `p_{m,0} ∈ [0, p̄_m]` when `ω_y > ω_o`
    (`olg_continuum`), and only `p ≡ 0` otherwise (`olg_no_monetary`);
  - convergence to zero below `p̄_m` (`olg_decreasing_to_zero`);
  - the map of Figure 17.2 (`olg_map_slopes`, `olg_map_domain`).
* **Welfare** (§17.2.2):
  - the ranking of equilibria by `p_{m,0}` for every cohort (`olg_ranking`), and the improvement
    on autarky (`olg_monetary_improves_autarky`);
  - Pareto results via Miao Ch. 16 (`olg_miao_stationary_pareto`, `olg_miao_autarky_pareto_iff`);
  - the model check against Miao's economy (`olg_miao_paths`).
* **Money growth** (§17.2.3): the stationary equilibrium, return `1/(1 + µ)` and inflation
  `1 + µ` (`mg_stationary_iff`, `mg_return`, `mg_value_strictAntiOn`).
* **Dynastic models** (§17.3.1):
  - (17.11)–(17.15) (`eq_17_11`, `eq_17_12`, `eq_17_13`, `eq_17_14`, `eq_17_15`);
  - money is not valued unless the stock vanishes (`dyn_no_valued_money`).
* **Reduced-form money** (§17.3.2):
  - the CIA model: (17.24), a binding constraint, and the Friedman rule (`eq_17_24`,
    `cia_must_bind`, `cia_friedman_rule`);
  - transactions costs: (17.28)–(17.29) and the elasticities (`eq_17_29`,
    `tc_demand_elasticity`);
  - money in utility: (17.35) and homothetic demand (`eq_17_35`, `miu_homothetic_mrs`).
* **Hyperinflation** (§17.3.3): (17.36)–(17.38) and the convergent paths (`hyp_exists_path`,
  `hyp_all_paths`), footnotes 11–12 (`hyp_local_stable`, `hyp_log_unique`).
* **Pegs and rules** (§17.3.3):
  - CIA peg real indeterminacy (`peg_pins`, `peg_exists`, `peg_real_indeterminacy`);
  - (17.40) and the corrected determinacy conditions (`eq_17_40`, `rule_determinate`,
    `rule_indeterminate`, `rule_printed_counterexample`).
* **Cashless limit** (§17.3.3): (17.41) (`eq_17_41`), footnotes 17–18 with the limits of the
  elasticities (`cl_footnote_18_identities`, `cl_footnote_18_limits`).
* **Government budget** (§17.3.3):
  - (17.42)–(17.44) (`gb_flow_real`, `eq_17_43`, `eq_17_44`);
  - the stationary budget (`gb_stationary`) and open-market irrelevance (`gb_omo_irrelevance`);
  - the Laffer curve (`lf_interior_max`, `lf_counterexample`);
  - unpleasant arithmetic (`ua_stationary`, `ua_dynamic`);
  - the fiscal backstop (`fb_backstop`);
  - the FTPL (17.45)–(17.46) (`ftpl_price_level`, `ftpl_unique`, `ftpl_none`).
* **Kareken–Wallace** (§17.4.1):
  - equal returns or one currency unvalued (`kw_structure`);
  - `e` constant and indeterminate (`kw_e_constant`, `kw_indeterminate`);
  - the limit and Gresham's law (`kw_limit_formula`, `kw_gresham`).
* **Missing assets** (§17.5): the Huggett autarky rate `1/q < 1/β` (`ma_autarky_price`) and the
  price level with fiat money (`ma_price_level`).

All names are in the namespace `AKMM.Money`. The project imports:
- [EconomicDynamics/OverlappingGenerations](../../EconomicDynamics/OverlappingGenerations/README.md)
  (Miao Ch. 16: `ox_log_paths`, `ox_log_construct`, Propositions 16.1.2–16.1.3);
- [EconomicDynamics/IncompleteMarkets](../../EconomicDynamics/IncompleteMarkets/README.md)
  (Miao Ch. 17: `bw_fiat_quantity_theory`);
- from [MonetaryEconomics](https://github.com/LeanEconomics/MonetaryEconomics):
  Gali/ClassicalMonetaryModel (the CES composite of Galí Ch. 2), Cochrane/Monetarism
  (`unpleasant_tradeoff`) and Cochrane/TwoPeriodModel (`lastDay_existsUnique`, `lastDay_none`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [OLGDemand](AKMMMoney/OLGDemand.lean) | 8 | The young's problem (17.1)–(17.3) (AKMM §17.2.1, pp. 496–498) |
| [OLGEquilibrium](AKMMMoney/OLGEquilibrium.lean) | 22 | (17.4)–(17.5), the classification of equilibria, Figure 17.2 (pp. 498–499) |
| [OLGWelfare](AKMMMoney/OLGWelfare.lean) | 13 | Welfare ranking and Pareto results, link with Miao Ch. 16 (§17.2.2, p. 500) |
| [OLGMoneyGrowth](AKMMMoney/OLGMoneyGrowth.lean) | 6 | Money growth in the OLG economy (§17.2.3, p. 501) |
| [Dynastic](AKMMMoney/Dynastic.lean) | 11 | (17.11)–(17.15): fiat money has no value (§17.3.1, pp. 501–503) |
| [CashInAdvance](AKMMMoney/CashInAdvance.lean) | 8 | (17.19)–(17.24), the binding CIA, the Friedman rule (§17.3.2, pp. 504–505) |
| [TransactionCosts](AKMMMoney/TransactionCosts.lean) | 9 | (17.25)–(17.29) and money-demand elasticities (pp. 509–510) |
| [MoneyInUtility](AKMMMoney/MoneyInUtility.lean) | 5 | (17.35) and homothetic money demand (p. 511) |
| [Hyperinflation](AKMMMoney/Hyperinflation.lean) | 13 | (17.36)–(17.38), footnotes 11–12 (§17.3.3, pp. 512–513) |
| [InterestRules](AKMMMoney/InterestRules.lean) | 15 | The CIA peg, (17.39)–(17.40), footnote 15 (pp. 515–516) |
| [CashlessLimit](AKMMMoney/CashlessLimit.lean) | 16 | (17.41), footnotes 17–18 (pp. 517–519) |
| [GovernmentBudget](AKMMMoney/GovernmentBudget.lean) | 9 | (17.42)–(17.44), the `i = 0` budget, open-market irrelevance (pp. 519–522) |
| [FiscalMonetary](AKMMMoney/FiscalMonetary.lean) | 13 | Laffer curve, unpleasant arithmetic, backstop, (17.45)–(17.46) (pp. 520–523) |
| [KarekenWallace](AKMMMoney/KarekenWallace.lean) | 15 | Two currencies, exchange-rate indeterminacy, Gresham's law (§17.4.1, pp. 524–526) |
| [MissingAssets](AKMMMoney/MissingAssets.lean) | 6 | The Huggett autarky rate and fiat money (§17.5, pp. 528–529) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
