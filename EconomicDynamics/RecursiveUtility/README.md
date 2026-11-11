# Miao Chapter 20: Recursive Utility, in Lean

This is the `EconomicDynamics/RecursiveUtility` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 20 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 20 studies preferences beyond time-additive expected utility: Koopmans' recursive
utility and its construction, Epstein–Zin and Chew–Dekel preferences, ambiguity aversion
(maxmin, variational, divergence and smooth ambiguity), the temporal resolution of uncertainty,
concavity, risk aversion and pricing kernels, portfolio choice and asset pricing with recursive
utility (the Campbell–Shiller approximation and long-run risk), and Pareto optimality. Every
numbered definition, theorem, lemma, proposition and example (Definitions 20.1.1, 20.2.1–20.2.4,
20.3.1–20.3.2, 20.5.1; Theorems 20.1.1–20.1.2, 20.2.1; Lemmas 20.3.1, 20.5.1–20.5.2;
Propositions 20.3.1–20.3.2, 20.5.1–20.5.2; Examples 20.1.1–20.1.2, 20.3.1–20.3.3), the
derivations of the text and Exercises 1–3 and 5–7 are proved; the Matlab exercises (4, 7(b)) and
numerical calibrations are not formalised. The corrections are recorded in
[corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **902 theorems**; 389 of them are
Sargent–Stachurski's recursive decision processes and Chapter 7's weighted norms, copied.

* **Koopmans utility** (§20.1): the axioms and dynamic consistency, where "any recursive
  representation satisfies (K1)–(K3)" needs a strictly increasing aggregator
  (`ku_K1_counterexample`, `definition_20_1_1`); Examples 20.1.1–20.1.2; **Theorems 20.1.1–20.1.2**
  by contraction and weighted norms (`theorem_20_1_1`, `theorem_20_1_2`), with (W5) unsatisfiable
  as printed (`ku_W5_misprint`).
* **Epstein–Zin and Chew–Dekel** (§20.2.1): dynamic utility and certainty equivalents
  (`definition_20_2_1` … `definition_20_2_3`), (20.3) with its existence and homotheticity
  (`eq_20_3`, `ku_ez_markov_homogeneous`), the Allais paradox and Chew–Dekel preferences
  (`ku_allais_paradox`, `eq_20_6`); Exercise 1, where "strictly concave" is false
  (`ex_20_1_not_strict`).
* **Ambiguity aversion** (§20.2.2): maxmin and rectangularity (`aa_rectangular_recursion`,
  `aa_nonrectangular_counterexample`), variational and divergence utility, the multiplier
  preferences as risk-sensitive utility (`aa_multiplier_isLeast`), smooth ambiguity
  (`eq_20_16` … `eq_20_19`).
* **Temporal resolution** (§20.2.3): **Theorem 20.2.1** (`theorem_20_2_1`); Epstein–Zin agents
  prefer early resolution iff `γ ≥ ρ` (`ex_20_3`).
* **Properties** (§20.3): concavity, **Lemma 20.3.1** and **Proposition 20.3.1** (comparative
  risk aversion), utility gradients and **Proposition 20.3.2**, pricing kernels for Epstein–Zin,
  smooth ambiguity and multiple priors (`example_20_3_1` … `example_20_3_3`); "risk averse" as
  defined can never hold (`aa_riskAverse_never`).
* **Asset pricing** (§20.4): the Epstein–Zin Bellman equation and stochastic discount factor
  (`eq_20_22` … `eq_20_31`), the lognormal and Campbell–Shiller formulas (`eq_20_32` … `eq_20_45`),
  Bansal–Yaron long-run risk (`eq_20_46` … `eq_20_56`, `pa_by_matching_equity`), with the consol formulas and the sign of
  the volatility price corrected (`pa_consol_lambda_one_counterexample`, `pa_by_lam_w_not_pos`).
* **Pareto optimality** (§20.5): **Lemmas 20.5.1–20.5.2** for the comprehensive utility set and
  **Propositions 20.5.1–20.5.2** with positive weights (`lemma_20_5_1_counterexample`,
  `proposition_20_5_2_counterexample`), the Dumas–Wang–Uppal duality (`pa_dwu_duality`);
  Exercises 5–7 (`ex_20_5`, `ex_20_6_euler`, `ex_20_7`).

All names are in the namespace `Miao.RecursiveUtility`; the `SS*` modules are copied from
[FiniteStates/RecursiveDecisionProcesses](../../FiniteStates/RecursiveDecisionProcesses/README.md)
(namespace `Miao.RecursiveUtility.SS`), and `KUWeighted` from
[EconomicDynamics/InfiniteHorizonDP](../InfiniteHorizonDP/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SSBasics](RecursiveUtility/SSBasics.lean) | 18 | Markov matrices, contractions and Banach's theorem, Prop 2.2.7, Blackwell's condition, Lemma 2.2.2 (restated) (Sargent–Stachurski, copied) |
| [SSSpectralRadius](RecursiveUtility/SSSpectralRadius.lean) | 29 | `ρ(A)`, Gelfand's formula, the Neumann series, Ex 2.2.28 (restated) (Sargent–Stachurski, copied) |
| [SSResolvent](RecursiveUtility/SSResolvent.lean) | 11 | The resolvent series (restated) (Sargent–Stachurski, copied) |
| [SSPerronFrobenius](RecursiveUtility/SSPerronFrobenius.lean) | 20 | Thm 2.3.1, nonnegative case; Lemmas 2.3.2–2.3.3 (restated) (Sargent–Stachurski, copied) |
| [SSIrreducible](RecursiveUtility/SSIrreducible.lean) | 10 | Thm 2.3.1, irreducible case (restated) (Sargent–Stachurski, copied) |
| [SSLinearValuation](RecursiveUtility/SSLinearValuation.lean) | 25 | Thm 6.1.1, `ρ(βP) = β`, Lemma 6.1.4, Thm 6.1.5, Example 6.1.2, Prop 6.1.6 (restated) (Sargent–Stachurski, copied) |
| [SSOrderFixedPoints](RecursiveUtility/SSOrderFixedPoints.lean) | 15 | Global stability on a set, conjugacy, Thm 7.1.1, Thm 7.1.3 (restated) (Sargent–Stachurski, copied) |
| [SSPowerAffine](RecursiveUtility/SSPowerAffine.lean) | 27 | Ex 7.1.7–7.1.8, Thm 7.1.4 (restated) (Sargent–Stachurski, copied) |
| [SSCertaintyEquivalents](RecursiveUtility/SSCertaintyEquivalents.lean) | 33 | Entropic, Kreps–Porteus and quantile operators (restated) (Sargent–Stachurski, copied) |
| [SSKoopmans](RecursiveUtility/SSKoopmans.lean) | 29 | Aggregators and Koopmans operators (restated) (Sargent–Stachurski, copied) |
| [SSEpsteinZin](RecursiveUtility/SSEpsteinZin.lean) | 13 | Epstein–Zin Koopmans operators, Prop 7.2.3, Prop 7.3.5 (restated) (Sargent–Stachurski, copied) |
| [SSRDP](RecursiveUtility/SSRDP.lean) | 29 | §8.1.1–8.1.3.2, (8.1)–(8.18), Ex 8.1.6–8.1.11, Algorithms 8.1–8.2 (Sargent–Stachurski, copied) |
| [SSOptimality](RecursiveUtility/SSOptimality.lean) | 26 | Thm 8.1.1, Thm 8.1.2, §8.1.3.5, Ex 8.1.12–8.1.13, Prop 8.1.3, Ex 8.1.18 (Sargent–Stachurski, copied) |
| [SSExamples](RecursiveUtility/SSExamples.lean) | 12 | Examples 8.1.1–8.1.8, 8.1.14, Ex 8.1.1–8.1.5 (Sargent–Stachurski, copied) |
| [SSContracting](RecursiveUtility/SSContracting.lean) | 26 | §8.2.1, Props 8.2.1, 8.2.3, 8.3.1, Cor 8.2.2, Examples 8.1.12–8.1.13, 8.1.15–8.1.16, 8.2.1, Ex 8.1.14–8.1.15, 8.2.1–8.2.7, 8.3.1 (Sargent–Stachurski, copied) |
| [SSEventuallyContracting](RecursiveUtility/SSEventuallyContracting.lean) | 6 | §8.2.2, Prop 8.2.4, Prop 6.2.2, Ex 8.1.16, 8.2.8 (Sargent–Stachurski, copied) |
| [SSConcaveRDP](RecursiveUtility/SSConcaveRDP.lean) | 9 | §8.2.3, Prop 8.2.5, Ex 8.2.9–8.2.11 (Sargent–Stachurski, copied) |
| [SSAdversarial](RecursiveUtility/SSAdversarial.lean) | 26 | §8.3.2–8.3.3, Props 8.3.2, 8.3.4, Lemma 8.3.3, Example 8.3.1, Ex 8.3.3–8.3.4, (8.50)–(8.51) (Sargent–Stachurski, copied) |
| [KUWeighted](RecursiveUtility/KUWeighted.lean) | 25 | The weighted space `C_ϕ(S)` and the Weighted Contraction Mapping Theorem (copied) |
| [KUIntro](RecursiveUtility/KUIntro.lean) | 7 | The introduction to Chapter 20: limits of time-additive expected utility |
| [KUKoopmans](RecursiveUtility/KUKoopmans.lean) | 30 | Koopmans's utility (§20.1.1) |
| [KUConstruction](RecursiveUtility/KUConstruction.lean) | 33 | Construction of recursive utility (§20.1.2): Theorems 20.1.1 and 20.1.2 |
| [KUConstructionExamples](RecursiveUtility/KUConstructionExamples.lean) | 15 | Examples for §20.1.2 |
| [KUStochastic](RecursiveUtility/KUStochastic.lean) | 14 | Recursive utility under uncertainty (§20.2, Definitions 20.2.1–20.2.3) |
| [KUEpsteinZin](RecursiveUtility/KUEpsteinZin.lean) | 21 | Epstein–Zin preferences (§20.2.1, (20.3)–(20.5)) |
| [KUChewDekel](RecursiveUtility/KUChewDekel.lean) | 28 | The Chew–Dekel risk aggregator (§20.2.1, (20.6)) |
| [KUExercise](RecursiveUtility/KUExercise.lean) | 14 | Exercise 20.1: Epstein–Zin utility with a finite horizon |
| [AABasics](RecursiveUtility/AABasics.lean) | 13 | Finite-state setting for §20.2.2–§20.3 |
| [AALimits](RecursiveUtility/AALimits.lean) | 4 | Limits of log-exponential certainty equivalents |
| [AAMaxmin](RecursiveUtility/AAMaxmin.lean) | 22 | Maxmin expected utility and recursive multiple priors |
| [AAVariational](RecursiveUtility/AAVariational.lean) | 20 | Variational, divergence and multiplier utility |
| [AADivergence](RecursiveUtility/AADivergence.lean) | 12 | Recursive divergence utility |
| [AASmoothAmbiguity](RecursiveUtility/AASmoothAmbiguity.lean) | 30 | Smooth ambiguity utility |
| [AAResolution](RecursiveUtility/AAResolution.lean) | 23 | Temporal resolution of uncertainty |
| [AAConcavity](RecursiveUtility/AAConcavity.lean) | 14 | Concavity of recursive utility |
| [AARiskAversion](RecursiveUtility/AARiskAversion.lean) | 11 | Comparative risk aversion |
| [AAGradients](RecursiveUtility/AAGradients.lean) | 12 | Utility gradients and pricing kernels |
| [AAPricing](RecursiveUtility/AAPricing.lean) | 16 | Pricing kernels: Examples 20.3.1–20.3.3 and Exercise 20.2 |
| [PAEpsteinZin](RecursiveUtility/PAEpsteinZin.lean) | 13 | The Epstein–Zin recursion on one node of an event tree |
| [PAPortfolio](RecursiveUtility/PAPortfolio.lean) | 23 | Portfolio choice with Epstein–Zin utility: optimality and equilibrium |
| [PALogNormal](RecursiveUtility/PALogNormal.lean) | 15 | The log-linear (lognormal) approximation of Campbell |
| [PACampbellShiller](RecursiveUtility/PACampbellShiller.lean) | 13 | The Campbell–Shiller approximation and the return decomposition |
| [PAVolatilityPuzzles](RecursiveUtility/PAVolatilityPuzzles.lean) | 18 | Equity volatility and equity premium puzzles with a simple long-run risk process |
| [PAGaussianShocks](RecursiveUtility/PAGaussianShocks.lean) | 6 | Lognormal Euler equations with IID standard normal shocks |
| [PALongRunRisk](RecursiveUtility/PALongRunRisk.lean) | 15 | The Bansal–Yaron long-run risk model |
| [PALongRunRiskPricing](RecursiveUtility/PALongRunRiskPricing.lean) | 35 | The Bansal–Yaron model: pricing kernel, risk premia and the riskfree rate |
| [PAPareto](RecursiveUtility/PAPareto.lean) | 14 | Pareto optimality with recursive utility: the utility possibility set |
| [PALucasStokey](RecursiveUtility/PALucasStokey.lean) | 7 | Recursive Pareto problems: the Lucas–Stokey and Dumas–Wang–Uppal approaches |
| [PAWeil](RecursiveUtility/PAWeil.lean) | 7 | Exercise 20.5: precautionary saving with Weil (1993) preferences |
| [PAExercises](RecursiveUtility/PAExercises.lean) | 8 | Exercises 20.6 and 20.7: first-order conditions for recursive Pareto problems |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
