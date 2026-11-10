# Miao Chapter 17: Incomplete Markets Models, in Lean

This is the `EconomicDynamics/IncompleteMarkets` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 17 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 17 studies heterogeneous-agent economies with uninsurable idiosyncratic risk: Aiyagari's
production economy, Huggett's and Bewley's endowment economies with a risk-free bond or fiat
money, interest on currency and seigniorage, and economies with aggregate shocks solved by the
Krusell–Smith method. Every numbered definition and proposition (Definitions 17.1.1, 17.2.1 and
17.3.1, Propositions 17.2.1–17.2.3), the derivations of the text and the mathematical content of
Exercises 4–6 are proved; the computer codes, numerical examples and figures (Example 17.1.1,
Exercises 1–3, the Krusell–Smith simulation) are not formalised, nor are the existence results
the book cites (Miao 2006, Kubler–Schmedders). The continuity and divergence of aggregate asset
supply, which the book asserts, are hypotheses of the existence theorem, with a concrete
instance. The corrections are recorded in [corrections](docs/corrections.md), and every book
item is located in the [source map](docs/source-map.md). The library contains **645 theorems**;
494 of them are carried over from Chapters 3 and 5–8 and from Stokey–Lucas–Prescott.

* **The Aiyagari economy** (§17.1): the household problem in assets and in cash on hand, reduced
  to Chapter 8's income fluctuation problem (`eq_17_4`, `ay_bellmanCoh_of_SI`); stationary
  distributions (`eq_17_7`, `ay_stationary_exists`); **Definition 17.1.1** with a concrete
  equilibrium (`definition_17_1_1`, `ay_exampleEqm`); existence by the crossing argument
  (`ay_existence`, `ay_existence_example`); every stationary distribution has `β(1 + r) < 1`, proved
  by an Euler–variance argument (`ay_beta_R_lt_one`, `ay_r_lt_rho`), so capital exceeds the
  complete-markets level (`ay_overaccumulation`); footnote 2 counts `A` twice
  (`ay_saving_rate_misprint`) and complete concentration gives a finite-sample Gini of `1 − 1/n`
  (`ay_gini_concentrated`); Exercise 4 (`ex_17_4`).
* **Endowment economies** (§17.2): **Definition 17.2.1** and **Proposition 17.2.1**
  (`definition_17_2_1`, `proposition_17_2_1`), fiat money and the quantity theory
  (`bw_fiat_quantity_theory`), interest on currency and **Propositions 17.2.2–17.2.3**
  (`proposition_17_2_2`, `proposition_17_2_3_rates`, `proposition_17_2_3_lt`), seigniorage
  (`bw_seign_mbar`, `bw_seign_comparative_statics`).
* **Aggregate shocks** (§17.3): **Definition 17.3.1**, whose printed law of motion is not a
  probability measure (`bw_book_law_not_prob`, `bw_law_isProb`), with a concrete recursive
  equilibrium (`bw_recEqm_example`); the Krusell–Smith law of motion and its consistency
  (`eq_17_12`, `bw_ks_fixed_point_of_exact`); Exercises 5–6 (`ex_17_5`, `ex_17_6_b`).

All names are in the namespace `Miao.IncompleteMarkets`. The copied modules come from
[EconomicDynamics/Applications](../Applications/README.md) (which carries Chapters 3, 5–7 and the
Stokey–Lucas–Prescott weak-convergence chain `SIWC*`, namespace `Miao.IncompleteMarkets.SIWC`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SLPCorrespondences](IncompleteMarkets/SLPCorrespondences.lean) | 2 | Correspondences (copied) |
| [SLPTransitionFunctions](IncompleteMarkets/SLPTransitionFunctions.lean) | 0 | `markovOpR`, `IsFeller` (copied) |
| [SLPMaximum](IncompleteMarkets/SLPMaximum.lean) | 14 | Theorem of the Maximum (copied) |
| [SLPSelection](IncompleteMarkets/SLPSelection.lean) | 8 | Measurable selection (copied) |
| [SLPEnvelope](IncompleteMarkets/SLPEnvelope.lean) | 2 | Benveniste–Scheinkman (copied) |
| [SLPLemma95](IncompleteMarkets/SLPLemma95.lean) | 11 | SLP Lemmas 9.5, 9.5′ (copied) |
| [OCSetting](IncompleteMarkets/OCSetting.lean) | 5 | §6.4: the model, (6.28)–(6.29), Assumptions 6.4.1–6.4.14 (from Chapter 6) |
| [OCLemma641](IncompleteMarkets/OCLemma641.lean) | 10 | Lemma 6.4.1 (from Chapter 6) |
| [OCExistence](IncompleteMarkets/OCExistence.lean) | 18 | Theorem 6.4.1, measurable selection (from Chapter 6) |
| [OCMonotone](IncompleteMarkets/OCMonotone.lean) | 1 | Theorem 6.4.2 (from Chapter 6) |
| [OCConcave](IncompleteMarkets/OCConcave.lean) | 13 | Theorem 6.4.3 (corrected) (from Chapter 6) |
| [OCDiffTools](IncompleteMarkets/OCDiffTools.lean) | 3 | Differentiating concave integrals (from Chapter 6) |
| [OCDifferentiable](IncompleteMarkets/OCDifferentiable.lean) | 12 | Theorem 6.4.4, (6.31)–(6.33), Euler equations (from Chapter 6) |
| [OCMaxPrinciple](IncompleteMarkets/OCMaxPrinciple.lean) | 5 | §6.5: (6.34)–(6.39), Theorem 6.5.1 (from Chapter 6) |
| [OCMaxPrincipleLinks](IncompleteMarkets/OCMaxPrincipleLinks.lean) | 9 | `μ_t = ∂V_t/∂x`, (6.40) (from Chapter 6) |
| [CSModel](IncompleteMarkets/CSModel.lean) | 19 | §6.6.2: the model, cash on hand, Theorem 6.4.1 applies (from Chapter 6) |
| [CSProperties](IncompleteMarkets/CSProperties.lean) | 13 | Monotonicity and concavity of `v_n`, the policies (from Chapter 6) |
| [CSDifferentiable](IncompleteMarkets/CSDifferentiable.lean) | 23 | Differentiability, FOC, comparisons in `n` and income (from Chapter 6) |
| [CSExercises](IncompleteMarkets/CSExercises.lean) | 13 | Exercises 5–7, 10 (from Chapter 6) |
| [CSDeterministic](IncompleteMarkets/CSDeterministic.lean) | 4 | Exercise 8 (from Chapter 6) |
| [EUTools](IncompleteMarkets/EUTools.lean) | 6 | Tools (supergradients, the limit step, inequality (7.38)) (from Chapter 7) |
| [EUEuler](IncompleteMarkets/EUEuler.lean) | 14 | The Euler class, Euler equations and transversality conditions (from Chapter 7) |
| [EUEulerSufficiency](IncompleteMarkets/EUEulerSufficiency.lean) | 4 | Theorem 7.5.2, sufficiency of the Euler and transversality conditions (from Chapter 7) |
| [EUPhelps](IncompleteMarkets/EUPhelps.lean) | 19 | Example 7.5.1 (Phelps 1962; Levhari–Srinivasan 1969) (from Chapter 7) |
| [CDUtility](IncompleteMarkets/CDUtility.lean) | 14 | The utility function of the consumption–saving problem (from Chapter 8) |
| [CDBudget](IncompleteMarkets/CDBudget.lean) | 13 | The consumption–saving problem: budget, no-Ponzi condition, natural debt limit (from Chapter 8) |
| [SIModel](IncompleteMarkets/SIModel.lean) | 21 | §8.3.2: the income-fluctuation problem with iid income, in cash on hand (from Chapter 8) |
| [SIEuler](IncompleteMarkets/SIEuler.lean) | 11 | §8.3.2: interior consumption and the Euler inequality from the Bellman equation (from Chapter 8) |
| [SIPolicies](IncompleteMarkets/SIPolicies.lean) | 14 | §8.3.2: Lemmas 8.3.1 and 8.3.2 (the consumption and saving policies) (from Chapter 8) |
| [SIBounded](IncompleteMarkets/SIBounded.lean) | 18 | §8.3.2, Case 1 (`βR < 1`): Lemma 8.3.3, `x_max` and Exercise 8.9 (from Chapter 8) |
| [SIWCTransitionFunctions](IncompleteMarkets/SIWCTransitionFunctions.lean) | 19 | Transition functions (copied) |
| [SIWCWeakBasics](IncompleteMarkets/SIWCWeakBasics.lean) | 10 | Weak convergence: basic tools (copied) |
| [SIWCPortmanteau](IncompleteMarkets/SIWCPortmanteau.lean) | 9 | Characterizations of weak convergence (copied) |
| [SIWCDetermining](IncompleteMarkets/SIWCDetermining.lean) | 10 | Convergence-determining families and uniqueness (copied) |
| [SIWCDistributionFunctions](IncompleteMarkets/SIWCDistributionFunctions.lean) | 14 | Distribution functions on `ℝˡ` (copied) |
| [SIWCDistributionConvergence](IncompleteMarkets/SIWCDistributionConvergence.lean) | 14 | Weak convergence of distribution functions (copied) |
| [SIWCHelly](IncompleteMarkets/SIWCHelly.lean) | 16 | Support, Helly's theorem and tightness (SLP §12.3, pp. 371–375) (copied) |
| [SIWCFellerInvariant](IncompleteMarkets/SIWCFellerInvariant.lean) | 17 | The Feller property and existence of invariant measures (SLP §12.4, pp. 375–378) (copied) |
| [SIWCMonotoneProcesses](IncompleteMarkets/SIWCMonotoneProcesses.lean) | 26 | Monotone Markov processes (SLP §12.4, pp. 378–383) (copied) |
| [SIWCRealIntervals](IncompleteMarkets/SIWCRealIntervals.lean) | 13 | Theorem 12.12 on real intervals and on rectangles (copied) |
| [SIStationary](IncompleteMarkets/SIStationary.lean) | 27 | §8.3.2, Case 1: Proposition 8.3.1 (a unique stable stationary distribution) (from Chapter 8) |
| [AYHousehold](IncompleteMarkets/AYHousehold.lean) | 14 | §17.1.1: the income fluctuation problem of the Aiyagari model |
| [AYIncomeFluct](IncompleteMarkets/AYIncomeFluct.lean) | 5 | §17.1.1 with iid shocks: the cash-on-hand process, `Ea(r, w)` and `r < 1/β − 1` |
| [AYFirm](IncompleteMarkets/AYFirm.lean) | 18 | §17.1.2: production, the firm's first-order conditions and capital demand |
| [AYEquilibrium](IncompleteMarkets/AYEquilibrium.lean) | 5 | §17.1.3: stationary recursive competitive equilibrium (Definition 17.1.1) |
| [AYExistence](IncompleteMarkets/AYExistence.lean) | 5 | §17.1.3: existence of a stationary equilibrium by the crossing argument (Figure 17.1) |
| [AYComputation](IncompleteMarkets/AYComputation.lean) | 18 | §17.1.4: the computation algorithm and the Lorenz curve and Gini coefficient |
| [AYLeisure](IncompleteMarkets/AYLeisure.lean) | 4 | Exercise 17.4: the Aiyagari model with endogenous leisure |
| [BWHousehold](IncompleteMarkets/BWHousehold.lean) | 14 | §17.2.1: the Huggett endowment economy, Definition 17.2.1 and Proposition 17.2.1 |
| [BWMoney](IncompleteMarkets/BWMoney.lean) | 21 | §17.2.2–17.2.3: fiat money, interest on currency, Propositions 17.2.2 and 17.2.3 (i) |
| [BWExamples](IncompleteMarkets/BWExamples.lean) | 12 | A concrete endowment economy with valued fiat money (instances for §17.2) |
| [BWRate](IncompleteMarkets/BWRate.lean) | 7 | Proposition 17.2.3: the equilibrium rate is below the rate of time preference |
| [BWSeigniorage](IncompleteMarkets/BWSeigniorage.lean) | 7 | §17.2.4: seigniorage |
| [BWAggregate](IncompleteMarkets/BWAggregate.lean) | 8 | §17.3.1: recursive competitive equilibrium with aggregate shocks (Definition 17.3.1) |
| [BWKrusellSmith](IncompleteMarkets/BWKrusellSmith.lean) | 6 | §17.3.2: the Krusell–Smith method; Exercise 17.5 |
| [BWImrohoroglu](IncompleteMarkets/BWImrohoroglu.lean) | 7 | Exercise 17.6 (Imrohoroglu 1992): the mathematical content |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
