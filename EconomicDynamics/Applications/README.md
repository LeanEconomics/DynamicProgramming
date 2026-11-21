# Miao Chapter 8: Applications, in Lean

This is the `EconomicDynamics/Applications` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 8 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 8 applies the dynamic programming of Chapters 6 and 7 to option exercise and job search,
discrete choice (machine replacement), consumption and saving with deterministic and stochastic
income, consumption/portfolio choice, inventory control with a fixed ordering cost, and
investment with adjustment costs. Every numbered result (Theorem 8.3.1, Lemmas 8.3.1–8.3.4 and
8.5.1–8.5.6, Propositions 8.3.1–8.3.2 and 8.5.1–8.5.4, Assumptions 8.5.1–8.5.2, Definition
8.5.1, Examples 8.3.1–8.3.2 and 8.6.1), the derivations of the text and Exercises 1–9 and 11–14
are proved, except the continuity of the stationary distribution of Proposition 8.3.1 in
`(R, b)`, which the book's assumptions do not give, the almost-sure path statements of §8.3.2,
the "intuitive" fixed-cost claims of p. 287, and parts of Exercises 5, 6 and 13. Exercise 10
(characterise the Levhari–Mirman–Zilcha model with CARA utility) has no definite statement and
is not formalised. The corrections are recorded in [corrections](docs/corrections.md), and every
book item is located in the [source map](docs/source-map.md). The library contains
**1325 theorems**; 731 of them are carried over from Chapters 3, 5, 6 and 7 and from
Stokey–Lucas–Prescott.

* **Option exercise and job search** (§8.1): the Bellman equation as Chapter 5's stopping
  problem, its unique solution and threshold (`od_option_exists_unique`, `od_option_threshold`);
  `z* > I` only when offers can exceed `I` (`od_option_threshold_gt_iff`,
  `od_option_threshold_dirac`); the mean waiting time is `λ/(1 − λ)`, not `1/(1 − λ)`
  (`od_wait_mean`, `od_wait_mean_misprint`); more risk delays investment (`od_option_riskier`);
  McCall's reservation wage (`od_mccall_reservation`); Exercises 1–2 (`ex_8_1`, `ex_8_2_alpha`).
* **Discrete choice** (§8.2): existence, uniqueness and monotonicity of the value
  (`od_dc_exists`, `od_dc_unique`, `od_dc_antitone`), (8.1)–(8.2) (`eq_8_1`, `eq_8_2`); the
  trigger need not exist (`od_dc_example_no_trigger`) and the printed solution formula is false
  (`od_dc_example_misprint`, `od_dc_solution`).
* **Consumption and saving, deterministic income** (§8.3, §8.3.1): Theorem 8.3.1, whose converse
  is false under the stated hypothesis (`theorem_8_3_1`, `theorem_8_3_1_converse`,
  `theorem_8_3_1_converse_counterexample`); (8.7)–(8.8) and their sufficiency (`eq_8_7`,
  `eq_8_7_8_8_sufficient`); the three cases `βR < 1`, `> 1`, `= 1` (`cd1_Params.eq_8_9`,
  `cd2_c_tendsto`, `cd3_chamberlain_wilson`, with the counterexample
  `cd3_chamberlain_wilson_counterexample`); Examples 8.3.1–8.3.2 and Exercise 8.8
  (`example_8_3_1`, `example_8_3_2`, `ex_8_8`).
* **Consumption and saving, stochastic income** (§8.3.2): Lemmas 8.3.1–8.3.4
  (`SIModel.Solution.lemma_8_3_1` … `lemma_8_3_4`); the unique globally stable stationary
  distribution of Proposition 8.3.1 by SLP Theorem 12.12 (`SIModel.Solution.proposition_8_3_1`);
  Proposition 8.3.2; the false identity of p. 253 (`SIModel.Solution.eq_8_16_identity_false`);
  Exercises 9 and 11, with "no stationary distribution" false for degenerate shocks
  (`ex_8_11_counterexample`).
* **Consumption/portfolio choice** (§8.4): (8.17), the first-order and envelope conditions and
  the Euler equations (`eq_8_17`, `od_portfolio_euler`).
* **Inventory** (§8.5): c-convexity and Lemmas 8.5.1–8.5.6, the (s, S) policy in finite and
  infinite horizon (`lemma_8_5_2`, `proposition_8_5_1` … `proposition_8_5_4`); Assumption
  8.5.1 is too weak (`assumption_8_5_1_counterexample`), Lemma 8.5.6 fails for `c = 0`
  (`lemma_8_5_6_counterexample`), (8.27)(ii) fails with atoms
  (`eq_8_27_ii_counterexample`); Exercises 3–7, with the stationary distribution of the
  inventory process (`ex_8_3`, `ex_8_4`, `ex_8_5`, `ex_8_6`, `ex_8_7`).
* **Investment** (§8.6): the neoclassical firm (`iv_owned_partialSum`), Q theory and Hayashi's
  marginal = average Q (`eq_8_33`, `iv_hayashi`), whose printed assumptions on `Ψ` are
  inconsistent (`iv_psi_assumptions_inconsistent`); augmented adjustment costs and Example 8.6.1
  with corrected thresholds `p_b + √(2φ)` (`eq_8_38`, `iv_buy_region`, `example_8_6_1_misprint`);
  Exercises 12–14 (`ex_8_12_hayashi`, `ex_8_13`, `ex_8_14_hayashi`).

All names are in the namespace `Miao.Applications`. The `MDP*` modules are copied from
[EconomicDynamics/MarkovDecisionProcesses](../MarkovDecisionProcesses/README.md); the `PO*`,
`OC*` and `CS*` modules from [EconomicDynamics/FiniteHorizonDP](../FiniteHorizonDP/README.md);
the `IH*`, `BR*`, `EU*` and `EX*` modules from
[EconomicDynamics/InfiniteHorizonDP](../InfiniteHorizonDP/README.md) (which copied `SLP*`,
`BRContraction` and `IHExtendedReals` from Stokey–Lucas–Prescott); the `INMP*` modules from
[EconomicDynamics/MarkovProcesses](../MarkovProcesses/README.md); and the `SIWC*` modules
(namespace `Miao.Applications.SIWC`) from
[RecursiveMethods/ConvergenceApplications](../../RecursiveMethods/ConvergenceApplications/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MDPHistoryTools](Applications/MDPHistoryTools.lean) | 6 | Histories (copied) |
| [MDPBasics](Applications/MDPBasics.lean) | 8 | The model (5.1) (copied) |
| [MDPHistories](Applications/MDPHistories.lean) | 12 | Finite histories (copied) |
| [MDPObjective](Applications/MDPObjective.lean) | 22 | Objectives and values (copied) |
| [MDPSimulation](Applications/MDPSimulation.lean) | 8 | Transport between models (copied) |
| [MDPKernelTools](Applications/MDPKernelTools.lean) | 4 | Kernel builders (copied) |
| [MDPOptimalStopping](Applications/MDPOptimalStopping.lean) | 29 | Stopping as an MDP (copied) |
| [MDPStoppingExamples](Applications/MDPStoppingExamples.lean) | 14 | Stopping examples (copied) |
| [POHistory](Applications/POHistory.lean) | 23 | Problems from date `t`, plans from a history, continuation plans, (6.12)–(6.14) (from Chapter 6) |
| [POPrinciple](Applications/POPrinciple.lean) | 18 | Assumption 6.3.1, Lemma 6.3.1, Theorem 6.3.1 (from Chapter 6) |
| [POVerification](Applications/POVerification.lean) | 10 | Plans generated by `G_t`, Theorem 6.3.2 (from Chapter 6) |
| [SLPCorrespondences](Applications/SLPCorrespondences.lean) | 2 | Correspondences (copied) |
| [SLPTransitionFunctions](Applications/SLPTransitionFunctions.lean) | 0 | `markovOpR`, `IsFeller` (copied) |
| [SLPMaximum](Applications/SLPMaximum.lean) | 14 | Theorem of the Maximum (copied) |
| [SLPSelection](Applications/SLPSelection.lean) | 8 | Measurable selection (copied) |
| [SLPEnvelope](Applications/SLPEnvelope.lean) | 2 | Benveniste–Scheinkman (copied) |
| [SLPLemma95](Applications/SLPLemma95.lean) | 11 | SLP Lemmas 9.5, 9.5′ (copied) |
| [OCSetting](Applications/OCSetting.lean) | 5 | §6.4: the model, (6.28)–(6.29), Assumptions 6.4.1–6.4.14 (from Chapter 6) |
| [OCLemma641](Applications/OCLemma641.lean) | 10 | Lemma 6.4.1 (from Chapter 6) |
| [OCExistence](Applications/OCExistence.lean) | 18 | Theorem 6.4.1, measurable selection (from Chapter 6) |
| [OCMonotone](Applications/OCMonotone.lean) | 1 | Theorem 6.4.2 (from Chapter 6) |
| [OCConcave](Applications/OCConcave.lean) | 13 | Theorem 6.4.3 (corrected) (from Chapter 6) |
| [OCDiffTools](Applications/OCDiffTools.lean) | 3 | Differentiating concave integrals (from Chapter 6) |
| [OCDifferentiable](Applications/OCDifferentiable.lean) | 12 | Theorem 6.4.4, (6.31)–(6.33), Euler equations (from Chapter 6) |
| [OCMaxPrinciple](Applications/OCMaxPrinciple.lean) | 5 | §6.5: (6.34)–(6.39), Theorem 6.5.1 (from Chapter 6) |
| [OCMaxPrincipleLinks](Applications/OCMaxPrincipleLinks.lean) | 9 | `μ_t = ∂V_t/∂x`, (6.40) (from Chapter 6) |
| [CSModel](Applications/CSModel.lean) | 19 | §6.6.2: the model, cash on hand, Theorem 6.4.1 applies (from Chapter 6) |
| [CSProperties](Applications/CSProperties.lean) | 13 | Monotonicity and concavity of `v_n`, the policies (from Chapter 6) |
| [CSDifferentiable](Applications/CSDifferentiable.lean) | 23 | Differentiability, FOC, comparisons in `n` and income (from Chapter 6) |
| [CSExercises](Applications/CSExercises.lean) | 13 | Exercises 5–7, 10 (from Chapter 6) |
| [CSDeterministic](Applications/CSDeterministic.lean) | 4 | Exercise 8 (from Chapter 6) |
| [CSCARA](Applications/CSCARA.lean) | 8 | Exercises 9–10 (CARA) (from Chapter 6) |
| [IHExtendedReals](Applications/IHExtendedReals.lean) | 9 | ExtendedReals from RecursiveMethods/DeterministicDP (copied) |
| [IHEInt](Applications/IHEInt.lean) | 14 | The extended integral `ih_eint` and its monotone/dominated convergence theorems (from Chapter 7) |
| [IHLemma711](Applications/IHLemma711.lean) | 19 | Assumption 7.1.1, Lemma 7.1.1 (from Chapter 7) |
| [IHBellman](Applications/IHBellman.lean) | 6 | Assumption 7.1.2, Theorem 7.1.1, the definitions of p. 197 (from Chapter 7) |
| [IHVerification](Applications/IHVerification.lean) | 12 | Theorem 7.1.2, Corollary 7.1.1 (from Chapter 7) |
| [BRContraction](Applications/BRContraction.lean) | 8 | Contraction, BoundedReturns, BoundedMonotone from RecursiveMethods/StochasticDP (copied) |
| [BRSetting](Applications/BRSetting.lean) | 21 | Assumptions 7.2.1–7.2.3, the operator (7.16), Theorem 7.2.1 (from Chapter 7) |
| [EUTools](Applications/EUTools.lean) | 6 | Tools (supergradients, the limit step, inequality (7.38)) (from Chapter 7) |
| [EUEuler](Applications/EUEuler.lean) | 14 | The Euler class, Euler equations and transversality conditions (from Chapter 7) |
| [EUEulerSufficiency](Applications/EUEulerSufficiency.lean) | 4 | Theorem 7.5.2, sufficiency of the Euler and transversality conditions (from Chapter 7) |
| [EUPhelps](Applications/EUPhelps.lean) | 19 | Example 7.5.1 (Phelps 1962; Levhari–Srinivasan 1969) (from Chapter 7) |
| [EXCARA](Applications/EXCARA.lean) | 11 | Exercise 7.7, the limit policies and the Bellman equation of the limit (from Chapter 7) |
| [CDUtility](Applications/CDUtility.lean) | 14 | The utility function of the consumption–saving problem |
| [CDBudget](Applications/CDBudget.lean) | 13 | The consumption–saving problem: budget, no-Ponzi condition, natural debt limit |
| [CDEuler](Applications/CDEuler.lean) | 12 | The Euler inequality (8.7) and the transversality condition (8.8) |
| [CDCase1](Applications/CDCase1.lean) | 47 | Deterministic income, Case 1 (`βR < 1`): critical levels and the optimal plans |
| [CDCase1Value](Applications/CDCase1Value.lean) | 25 | Deterministic income, Case 1 (`βR < 1`): the value function and the policies |
| [CDCase2](Applications/CDCase2.lean) | 6 | Deterministic income, Case 2 (`βR > 1`) |
| [CDCase3](Applications/CDCase3.lean) | 12 | Deterministic income, Case 3 (`βR = 1`): Chamberlain and Wilson |
| [CDExamples](Applications/CDExamples.lean) | 8 | Examples 8.3.1 and 8.3.2 (Ljungqvist and Sargent) |
| [CDExercise88](Applications/CDExercise88.lean) | 12 | Exercise 8.8: CRRA consumption–saving with the natural borrowing constraint |
| [SIModel](Applications/SIModel.lean) | 21 | §8.3.2: the income-fluctuation problem with iid income, in cash on hand |
| [SIEuler](Applications/SIEuler.lean) | 11 | §8.3.2: interior consumption and the Euler inequality from the Bellman equation |
| [SIPolicies](Applications/SIPolicies.lean) | 14 | §8.3.2: Lemmas 8.3.1 and 8.3.2 (the consumption and saving policies) |
| [SIBounded](Applications/SIBounded.lean) | 18 | §8.3.2, Case 1 (`βR < 1`): Lemma 8.3.3, `x_max` and Exercise 8.9 |
| [SIWCTransitionFunctions](Applications/SIWCTransitionFunctions.lean) | 19 | Transition functions (copied) |
| [SIWCWeakBasics](Applications/SIWCWeakBasics.lean) | 10 | Weak convergence: basic tools (copied) |
| [SIWCPortmanteau](Applications/SIWCPortmanteau.lean) | 9 | Characterizations of weak convergence (copied) |
| [SIWCDetermining](Applications/SIWCDetermining.lean) | 10 | Convergence-determining families and uniqueness (copied) |
| [SIWCDistributionFunctions](Applications/SIWCDistributionFunctions.lean) | 14 | Distribution functions on `ℝˡ` (copied) |
| [SIWCDistributionConvergence](Applications/SIWCDistributionConvergence.lean) | 14 | Weak convergence of distribution functions (copied) |
| [SIWCHelly](Applications/SIWCHelly.lean) | 16 | Support, Helly's theorem and tightness (SLP §12.3, pp. 371–375) (copied) |
| [SIWCFellerInvariant](Applications/SIWCFellerInvariant.lean) | 17 | The Feller property and existence of invariant measures (SLP §12.4, pp. 375–378) (copied) |
| [SIWCMonotoneProcesses](Applications/SIWCMonotoneProcesses.lean) | 26 | Monotone Markov processes (SLP §12.4, pp. 378–383) (copied) |
| [SIWCRealIntervals](Applications/SIWCRealIntervals.lean) | 13 | Theorem 12.12 on real intervals and on rectangles (copied) |
| [SIStationary](Applications/SIStationary.lean) | 27 | §8.3.2, Case 1: Proposition 8.3.1 (a unique stable stationary distribution) |
| [SIGrowth](Applications/SIGrowth.lean) | 10 | §8.3.2, Cases 2 and 3 (`βR > 1`, `βR = 1`): Proposition 8.3.2 and Lemma 8.3.4 |
| [SICARA](Applications/SICARA.lean) | 12 | Exercise 8.11: the Schechtman–Escudero CARA model with AR(1) income |
| [INCConvex](Applications/INCConvex.lean) | 10 | c-convexity (Scarf's K-convexity): Definition 8.5.1 and Lemma 8.5.1 |
| [INSsPolicy](Applications/INSsPolicy.lean) | 21 | The (s, S) policy for a c-convex function: Lemma 8.5.2 |
| [INModel](Applications/INModel.lean) | 29 | The inventory model of §8.5: setting, Bellman operator, finite-horizon problems |
| [INFinite](Applications/INFinite.lean) | 18 | Finite-horizon inventory problems: bounds on `s_n`, `S_n` (Lemmas 8.5.4–8.5.6) |
| [INInfinite](Applications/INInfinite.lean) | 27 | The infinite-horizon inventory problem: Propositions 8.5.1–8.5.3 |
| [INUnique](Applications/INUnique.lean) | 4 | Uniqueness for the inventory Bellman equation: Proposition 8.5.4 |
| [INExercises](Applications/INExercises.lean) | 8 | Inventory: counterexamples and Exercises 8.6–8.7 |
| [INMPTransitionFunctions](Applications/INMPTransitionFunctions.lean) | 19 | Transition functions (copied) |
| [INMPTotalVariation](Applications/INMPTotalVariation.lean) | 15 | The total variation norm (copied) |
| [INMPTVConvergence](Applications/INMPTVConvergence.lean) | 12 | Characterizations of strong convergence (copied) |
| [INMPConditionM](Applications/INMPConditionM.lean) | 12 | Condition M and geometric convergence (copied) |
| [INMPKernels](Applications/INMPKernels.lean) | 13 | Stochastic kernels, `n`-step transitions and the operators `T`, `T*` (copied) |
| [INMPStrong](Applications/INMPStrong.lean) | 22 | Strong convergence: total variation, Condition M and the Minorization Condition (copied) |
| [INMarkov](Applications/INMarkov.lean) | 15 | The inventory process under the (s, S) policy: Exercise 8.5 |
| [ODBasic](Applications/ODBasic.lean) | 6 | Tools for optimal stopping with i.i.d. offers |
| [ODOption](Applications/ODOption.lean) | 20 | Option exercise: the Bellman equation and the investment threshold |
| [ODWaiting](Applications/ODWaiting.lean) | 8 | Option exercise: the waiting time until investment |
| [ODRisk](Applications/ODRisk.lean) | 3 | Option exercise: an increase in risk delays investment |
| [ODMcCall](Applications/ODMcCall.lean) | 15 | McCall's job search model, with and without job loss |
| [ODMarkovSearch](Applications/ODMarkovSearch.lean) | 8 | McCall's job search model with Markov wage offers |
| [ODDCSetting](Applications/ODDCSetting.lean) | 19 | Discrete choice: the Bellman equation of Rust's replacement problem |
| [ODDCTrigger](Applications/ODDCTrigger.lean) | 6 | Discrete choice: the replacement trigger and the boundary conditions (8.2) |
| [ODDCSolution](Applications/ODDCSolution.lean) | 11 | Discrete choice: the free boundary problem (8.1) and its solution |
| [ODDCExamples](Applications/ODDCExamples.lean) | 4 | Discrete choice: two concrete replacement problems |
| [ODPortfolio](Applications/ODPortfolio.lean) | 6 | Consumption/portfolio choice: the budget constraint (8.17) and the Euler equations |
| [IVNeoclassical](Applications/IVNeoclassical.lean) | 15 | §8.6.1 Neoclassical theory of investment |
| [IVQTheory](Applications/IVQTheory.lean) | 18 | §8.6.2 Q theory of investment |
| [IVUzawa](Applications/IVUzawa.lean) | 9 | Uzawa's adjustment costs (8.34) and Exercise 8.14 |
| [IVExercises](Applications/IVExercises.lean) | 14 | Exercises 8.12 and 8.13 (Q theory) |
| [IVAugmented](Applications/IVAugmented.lean) | 28 | §8.6.3 Augmented adjustment costs |
| [IVExample861](Applications/IVExample861.lean) | 10 | Example 8.6.1 (static investment with fixed and transactions costs) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
