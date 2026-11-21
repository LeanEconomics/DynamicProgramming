# AKMM Chapter 2: A Framework for Macroeconomics, in Lean

This is the `AKMM/Framework` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 2 of Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama,
*Macroeconomics* (draft of December 2025), cited by the draft's pages. Run the commands below from
this directory. [Return to the library index](../../README.md).

Chapter 2 builds Solow's framework step by step: growth accounting in continuous time, the
accumulation equation and its balanced paths, the detrended Solow system, and the preferences
that rationalise a constant saving rate and constant (or steadily falling) hours. Every derivation
of the text is proved: growth accounting (2.1)–(2.3), the accumulation equation (2.4) and the
balanced capital–output ratio, the detrended system with its steady state, balanced growth and
convergence, the Euler equation, CRRA utility (2.5) and its logarithmic limit, the "if" directions
for King–Plosser–Rebelo and Boppart–Krusell preferences, and the aggregation exercise of the box
on pp. 49–50. Not formalised: the data and figures, calibrated numbers, Uzawa's theorem and the
"only if" characterisations of balanced-growth preferences (cited or proved elsewhere in the
book). The project depends on Miao's `EconomicDynamics/NeoclassicalGrowth` (Euler's theorem for
homogeneous functions, the KPR scaling lemmas) and on EconomicGrowth's `DiscreteTime` Solow library
(the detrended map, its steady state and convergence). Two printed errors on p. 64 are corrected
and one notational point on p. 52 is checked, as recorded in [corrections](docs/corrections.md);
every book item is located in the [source map](docs/source-map.md). The library contains
**55 theorems**, all new.

* **Growth accounting** (§2.1.4): per-capita output and the firm's first-order conditions
  (`ga_per_capita`, `ga_profit_foc`); Solow's equation (2.1) in continuous time, with zero
  profits from Miao's Euler theorem (`eq_2_1`); the Hicks-neutral and labour-augmenting cases
  (`eq_2_2`, `eq_2_3`), the intermediate identities of the (2.3) derivation
  (`ga_labour_augmenting_partials`); Cobb–Douglas shares (`ga_cobbDouglas_share`).
* **The dynamic system** (§2.1.5): (2.4) in ratio form (`eq_2_4_ratio_form`); balanced paths
  and `K/Y = s/(γ + δ)` (`DynBalancedPath`, `dyn_capital_output_ratio`,
  `dyn_balanced_of_initial_ratio`); detrending onto EconomicGrowth's Solow map
  (`dyn_detrend_step`, `dyn_detrended_path`); the unique constant solution
  (`dyn_steady_existsUnique`), balanced growth from it (`dyn_balanced_growth_from_steady`) and
  convergence of `k̃` and of `K/Y` (`dyn_convergence`).
* **The aggregation box** (pp. 49–50): with proportional isoquants the frontier is linear
  (`agg_frontier_bound`, `agg_frontier_attained`), the relative price is pinned by technology
  (`agg_price_implied`), and output in good-1 units is a price-independent aggregate production
  function (`agg_aggregate_production`).
* **Saving** (§2.1.8): the Euler equation (`pref_euler_equation`); CRRA (2.5), constant
  consumption growth at a constant interest rate (`eq_2_5_hasDerivAt`, `pref_crra_mu_ratio`,
  `pref_crra_euler_iff`, `pref_crra_constant_growth`); the `σ → 1` limit `log c`
  (`pref_crra_log_limit`).
* **Hours** (§2.1.8): KPR preferences as Miao's (14.5) (`ls_kpr_eq_rm`), constant hours on a
  balanced path (`ls_kpr_balanced_growth`); Boppart–Krusell preferences with hours falling at
  `(1 + γ)^{−ν}` (`ls_bk_balanced_growth`), the `ν = 0` case (`ls_bk_nu_zero`), the production
  side (`ls_bk_production`); the p. 64 corrections (`ls_p64_output_growth_correction`,
  `ls_bk_hours_marginal_sign`, `ls_bk_decreasing_g_counterexample`).

All names are in the namespace `AKMM.Framework`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [GrowthAccounting](AKMMFramework/GrowthAccounting.lean) | 14 | Growth accounting (2.1)–(2.3) in continuous time, Cobb–Douglas shares (AKMM §2.1.4, §2.1.6, pp. 50–52, 58) |
| [DynamicSystem](AKMMFramework/DynamicSystem.lean) | 12 | Accumulation (2.4), balanced paths, the detrended Solow map, steady state and convergence (AKMM §2.1.5, pp. 52–57) |
| [Aggregation](AKMMFramework/Aggregation.lean) | 5 | The aggregate production function with proportional isoquants (AKMM box, pp. 49–50) |
| [Preferences](AKMMFramework/Preferences.lean) | 7 | The Euler equation, CRRA utility (2.5) and its log limit (AKMM §2.1.8, pp. 62–63) |
| [LabourSupply](AKMMFramework/LabourSupply.lean) | 17 | KPR and Boppart–Krusell preferences on balanced paths, the p. 64 corrections (AKMM §2.1.8, pp. 63–65) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
