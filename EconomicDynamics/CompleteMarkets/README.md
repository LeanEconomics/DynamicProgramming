# Miao Chapter 13: Complete Markets Exchange Economies, in Lean

This is the `EconomicDynamics/CompleteMarkets` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 13 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 13 studies exchange economies with complete markets on an event tree: Pareto optima,
Arrow–Debreu equilibrium with time-0 trading and the welfare theorems, Radner equilibrium with
sequential trading under debt, borrowing and short-sale constraints, no-arbitrage and state
prices, complete markets and the equivalence of the two equilibrium concepts, asset price
bubbles, the recursive formulation and asset pricing. Every numbered assumption, definition,
proposition, theorem and example, the derivations of the text and Exercises 1–10 are proved,
except the Hahn–Banach/Yosida–Hewitt proof outline of the Second Welfare Theorem (proved instead
from first-order conditions), the necessity of the transversality conditions in Exercise 4, the
convergence step of the Negishi algorithm and the uniqueness of the price in Exercise 7. Several
theorems are false as printed and are proved in corrected form with Lean counterexamples. The
corrections are recorded in [corrections](docs/corrections.md), and every book item is located in
the [source map](docs/source-map.md). The library contains **427 theorems**, all new.

* **Pareto optima and time-0 trading** (§13.1–13.3): Proposition 13.2.1 by separation
  (`proposition_13_2_1`), risk sharing — consumption depends only on the aggregate endowment
  (`po_risk_sharing`, `example_13_3_1`); Arrow–Debreu equilibrium and its first-order conditions
  (`po_ADEquilibrium`, `eq_13_6` … `eq_13_10`); the First Welfare Theorem (`theorem_13_3_1`); the
  Second Welfare Theorem is false with the economy's own endowments and holds with transfers
  (`theorem_13_3_2`, `theorem_13_3_2_counterexample`); Exercises 1–2 (`ex_13_1`, `ex_13_2`).
* **Sequential trading** (§13.4): Ponzi schemes are arbitrages (`rd_ponzi_arb`); Theorem 13.4.1;
  Theorem 13.4.2 by Stiemke's lemma, false under borrowing constraints when payoffs vanish
  (`theorem_13_4_2`, `theorem_13_4_2_BC_counterexample`); the printed definition of complete
  markets always holds with positive prices, so Theorem 13.4.3 and Exercise 8 are proved with the
  rank condition (`rd_completePrinted_of_pos`, `theorem_13_4_3`, `theorem_13_4_3_counterexample`,
  `ex_13_8_counterexample`); (13.23) needs the conditional transversality condition
  (`eq_13_23_counterexample`).
* **Equivalence of equilibria** (§13.5): Theorem 13.5.1 is false as printed and holds with the
  replicating strategies (`theorem_13_5_1_if`, `theorem_13_5_1_counterexample`,
  `theorem_13_5_1_onlyIf`); Example 13.5.1 (Magill–Quinzii); Assumption 13.5.1 fails as printed
  for discounted expected utility (`assumption_13_5_1_printed_fails`, `assumption_13_5_1`).
* **Bubbles** (§13.6): fundamental value and bubble, `0 ≤ b_t ≤ p_t` rather than `0 < b_t`
  (`eq_13_6_bubble_bounds`, `eq_13_6_bubble_pos_counterexample`); Theorem 13.6.1 with a concrete
  instance (`theorem_13_6_1`, `theorem_13_6_1_instance`); Kocherlakota's and Werner's examples
  (`example_13_6_1`, `example_13_6_2`).
* **Recursive formulation and asset pricing** (§13.7–13.8): Definition 13.7.1 with an instance;
  the Euler pricing equation, Hansen–Jagannathan bound and CAPM, whose printed beta is wrong
  (`bp_hansen_jagannathan`, `bp_capm`, `bp_capm_book_beta_counterexample`); the lognormal
  CCAPM and the risk-free rate (`eq_13_35`), (13.36) missing `σ_c` (`eq_13_36_counterexample`);
  Exercises 5–7, 9, 10.

All names are in the namespace `Miao.CompleteMarkets`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [POEventTree](CompleteMarkets/POEventTree.lean) | 14 | Uncertainty, preferences and endowments |
| [POPareto](CompleteMarkets/POPareto.lean) | 21 | Pareto optimum |
| [POTimeZero](CompleteMarkets/POTimeZero.lean) | 30 | Time 0 trading |
| [POExercises](CompleteMarkets/POExercises.lean) | 4 | Exercises 13.1 and 13.2 |
| [RDTree](CompleteMarkets/RDTree.lean) | 39 | The event tree, date sums and discounted expected utility |
| [RDSecurities](CompleteMarkets/RDSecurities.lean) | 19 | Sequential trading: securities, budgets, portfolio constraints and arbitrage |
| [RDStiemke](CompleteMarkets/RDStiemke.lean) | 3 | Stiemke's lemma |
| [RDStatePrices](CompleteMarkets/RDStatePrices.lean) | 17 | No one-period arbitrage and state prices |
| [RDComplete](CompleteMarkets/RDComplete.lean) | 15 | Complete markets, Theorem 13.4.3 and Exercise 13.8 |
| [RDRadner](CompleteMarkets/RDRadner.lean) | 28 | Radner equilibrium, the transversality condition and natural debt limits |
| [RDEuler](CompleteMarkets/RDEuler.lean) | 14 | First-order conditions of the sequential problem |
| [RDEx134](CompleteMarkets/RDEx134.lean) | 16 | Exercise 13.4: first-order and transversality conditions |
| [RDImpatience](CompleteMarkets/RDImpatience.lean) | 6 | Assumption 13.5.1: uniform lower bound on impatience |
| [RDEquivalence](CompleteMarkets/RDEquivalence.lean) | 7 | Equivalence of equilibria: Theorem 13.5.1 |
| [RDCounter](CompleteMarkets/RDCounter.lean) | 14 | A bubble on one branch, a Ponzi scheme on the other |
| [RDExample](CompleteMarkets/RDExample.lean) | 22 | Example 13.5.1 (Magill and Quinzii) |
| [BPTree](CompleteMarkets/BPTree.lean) | 31 | The event tree of §§13.6–13.8 |
| [BPBubbles](CompleteMarkets/BPBubbles.lean) | 13 | Fundamental values and bubbles |
| [BPNoBubble](CompleteMarkets/BPNoBubble.lean) | 11 | No bubbles on assets in positive supply (Theorem 13.6.1) |
| [BPKocherlakota2008](CompleteMarkets/BPKocherlakota2008.lean) | 5 | Bubbles and debt limits (Kocherlakota 2008, Exercise 13.7) |
| [BPDeterministic](CompleteMarkets/BPDeterministic.lean) | 10 | Deterministic Radner economies with one stock |
| [BPKocherlakota](CompleteMarkets/BPKocherlakota.lean) | 25 | Bubbles on assets in zero supply (Kocherlakota 1992) |
| [BPWerner](CompleteMarkets/BPWerner.lean) | 10 | A bubble on an asset in positive supply (Werner 2012) |
| [BPRecursive](CompleteMarkets/BPRecursive.lean) | 3 | Recursive competitive equilibrium with debt constraints |
| [BPAssetPricing](CompleteMarkets/BPAssetPricing.lean) | 30 | Asset pricing with a stochastic discount factor |
| [BPLognormal](CompleteMarkets/BPLognormal.lean) | 16 | The lognormal CCAPM: the riskfree rate and the equity premium |
| [BPExpUtility](CompleteMarkets/BPExpUtility.lean) | 4 | The static CCAPM with exponential utility (Exercise 13.10) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
