# Miao Chapter 7: Infinite-Horizon Dynamic Programming, in Lean

This is the `EconomicDynamics/InfiniteHorizonDP` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 7 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 7 extends Chapter 6 to an infinite horizon: the principle of optimality and the
transversality condition (7.4), bounded rewards and the contraction mapping argument, optimal
control with monotone, concave and differentiable value functions, unbounded rewards through
weighted norms, the maximum principle with transversality conditions, and Euler equations with
the necessity and sufficiency of the transversality condition. Every numbered result
(Assumptions 7.1.1–7.1.2, 7.2.1–7.2.3 and 7.3.1–7.3.5, Lemma 7.1.1, Theorems 7.1.1–7.1.3, 7.2.1–7.2.2,
7.3.1–7.3.6, 7.4.1 and 7.5.1–7.5.2, Corollary 7.1.1, Examples 7.1.1, 7.3.1–7.3.2 and 7.5.1), the
derivations of the text and Exercises 1–8 and 10 are proved, except the stochastic necessity of
the Euler equation (7.34), whose proof the book only outlines, the `C¹` part of Theorem 7.3.4
(differentiability at the point is proved) and the case `y > 0` of Exercise 8. Exercise 9 is not
formalised: the Levhari–Mirman–Zilcha policy has no closed form beyond one period. The
corrections are recorded in [corrections](docs/corrections.md), and every book item is located
in the [source map](docs/source-map.md). The library contains **876 theorems**; 442 of them are
carried over from Chapters 5 and 6 and from Stokey–Lucas–Prescott.

* **The principle of optimality** (§7.1): the integrals are extended integrals (`ih_eint`);
  Lemma 7.1.1 in the three cases of its proof (`lemma_7_1_1`); the Bellman equation (7.2) under
  a jointly measurable Assumption 7.1.2(b) (`theorem_7_1_1`); verification under the
  transversality condition (7.4) and Corollary 7.1.1 (`theorem_7_1_2`, `corollary_7_1_1`); the
  borrowing example, where (7.4) fails with `βⁿV̂*(sₙ) = Rs₀`, not `s₀`
  (`ih_borrow_tvc_misprint`); Example 7.1.1, whose printed constant has `β` for `αβ`
  (`example_7_1_1`, `example_7_1_1_value_misprint`); Theorem 7.1.3, which holds only almost
  surely and whose proof needs (7.4), proved directly without it (`theorem_7_1_3`,
  `theorem_7_1_3_counterexample`, `theorem_7_1_3_proof_gap`).
* **Bounded rewards** (§7.2): the operator (7.16) and Theorem 7.2.1 (`eq_7_16`,
  `theorem_7_2_1`); optimal stationary plans by measurable selection (`p205`); value iteration
  and the finite-horizon limit (`theorem_7_2_2`, `eq_7_17`).
* **Optimal control with bounded rewards** (§7.3.1): the control model as a stationary MDP
  (`theorem_7_3_1`); monotonicity (`theorem_7_3_2`); concavity, false without Assumption 6.4.11
  and with `G` not single-valued as printed (`theorem_7_3_3`, `theorem_7_3_3_counterexample`,
  `theorem_7_3_3_policy_counterexample`); the envelope condition in `ℝⁿ` (`theorem_7_3_4`,
  `eq_7_22`); convergence of the policies, with the remark of p. 211 off by one
  (`theorem_7_3_5`, `p211`).
* **Unbounded rewards** (§7.3.2): the weighted space and Theorem 7.3.6 (`theorem_7_3_6`,
  `ex_7_1`); the AK model, with no fixed point when `βA^γ ≥ 1` (`example_7_3_1`,
  `example_7_3_1_no_fixedPoint`); Duran's approach (`eq_7_28`, `ex_7_2`); Example 7.3.2, whose middle
  step is false, with a corrected weight (`example_7_3_2_counterexample`, `example_7_3_2`,
  `ex_7_3`); the log AK model, where (7.27) never holds (`wn_log_ak_7_27_never`).
* **The maximum principle** (§7.4): sufficiency with transversality (`theorem_7_4_1`); the
  remark that the sign of `μ*` is not needed for linear `φ` is false
  (`remark_7_4_1_counterexample`, `remark_7_4_1_affine`).
* **Euler equations and transversality** (§7.5): the Euler equations (`eq_7_34`,
  `theorem_7_5_1_euler`); Kamihigashi's necessity theorem, whose shifted plan is infeasible as
  printed (`theorem_7_5_1`, `theorem_7_5_1_shift_infeasible`); sufficiency (`theorem_7_5_2`);
  Example 7.5.1 (`example_7_5_1`).
* **Exercises** (§7.6): the Ramsey state space (`ex_7_4`), stochastic log growth (`ex_7_5`,
  `ex_7_5_value`), the value-function approach to Example 7.5.1 (`ex_7_6`), the limits of the
  Chapter 6 exercises, whose numbers are off by one (`ex_7_7_limit`, `ex_7_7_ponzi`,
  `ex_7_8_finite`, `ex_7_8_limit`), and (7.4) versus (7.35) (`ex_7_10`, `ex_7_10_tvc_fails`).

All names are in the namespace `Miao.InfiniteHorizonDP`. The `MDP*` modules are copied from
[EconomicDynamics/MarkovDecisionProcesses](../MarkovDecisionProcesses/README.md); the `PO*`,
`OC*` and `CS*` modules from [EconomicDynamics/FiniteHorizonDP](../FiniteHorizonDP/README.md);
the `SLP*` modules, `BRContraction` and `BRInteriorPoints` from
[RecursiveMethods/StochasticDP](../../RecursiveMethods/StochasticDP/README.md); and
`IHExtendedReals`, `IHDetPrinciple` and `IHLogCopy` from
[RecursiveMethods/DeterministicDP](../../RecursiveMethods/DeterministicDP/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MDPHistoryTools](InfiniteHorizonDP/MDPHistoryTools.lean) | 6 | Histories (copied) |
| [MDPBasics](InfiniteHorizonDP/MDPBasics.lean) | 8 | The model (5.1) (copied) |
| [MDPHistories](InfiniteHorizonDP/MDPHistories.lean) | 12 | Finite histories (copied) |
| [MDPObjective](InfiniteHorizonDP/MDPObjective.lean) | 22 | Objectives and values (copied) |
| [MDPSimulation](InfiniteHorizonDP/MDPSimulation.lean) | 8 | Transport between models (copied) |
| [MDPKernelTools](InfiniteHorizonDP/MDPKernelTools.lean) | 4 | Kernel builders (copied) |
| [POHistory](InfiniteHorizonDP/POHistory.lean) | 23 | Problems from date `t`, plans from a history, continuation plans, (6.12)–(6.14) (from Chapter 6) |
| [POPrinciple](InfiniteHorizonDP/POPrinciple.lean) | 18 | Assumption 6.3.1, Lemma 6.3.1, Theorem 6.3.1 (from Chapter 6) |
| [POVerification](InfiniteHorizonDP/POVerification.lean) | 10 | Plans generated by `G_t`, Theorem 6.3.2 (from Chapter 6) |
| [POConverse](InfiniteHorizonDP/POConverse.lean) | 3 | Theorem 6.3.3 (almost surely) (from Chapter 6) |
| [POCounterexample](InfiniteHorizonDP/POCounterexample.lean) | 6 | Theorem 6.3.3 fails everywhere (from Chapter 6) |
| [PODeterministic](InfiniteHorizonDP/PODeterministic.lean) | 17 | Exercise 1: the deterministic case (from Chapter 6) |
| [POMotivating](InfiniteHorizonDP/POMotivating.lean) | 32 | §6.1: (6.3)–(6.8), the Bellman equation, time consistency (from Chapter 6) |
| [POStochasticGrowth](InfiniteHorizonDP/POStochasticGrowth.lean) | 5 | Exercise 2: the value function and policies (from Chapter 6) |
| [SLPCorrespondences](InfiniteHorizonDP/SLPCorrespondences.lean) | 2 | Correspondences (copied) |
| [SLPTransitionFunctions](InfiniteHorizonDP/SLPTransitionFunctions.lean) | 0 | `markovOpR`, `IsFeller` (copied) |
| [SLPMaximum](InfiniteHorizonDP/SLPMaximum.lean) | 14 | Theorem of the Maximum (copied) |
| [SLPSelection](InfiniteHorizonDP/SLPSelection.lean) | 8 | Measurable selection (copied) |
| [SLPEnvelope](InfiniteHorizonDP/SLPEnvelope.lean) | 2 | Benveniste–Scheinkman (copied) |
| [SLPLemma95](InfiniteHorizonDP/SLPLemma95.lean) | 11 | SLP Lemmas 9.5, 9.5′ (copied) |
| [OCSetting](InfiniteHorizonDP/OCSetting.lean) | 5 | §6.4: the model, (6.28)–(6.29), Assumptions 6.4.1–6.4.14 (from Chapter 6) |
| [OCLemma641](InfiniteHorizonDP/OCLemma641.lean) | 10 | Lemma 6.4.1 (from Chapter 6) |
| [OCExistence](InfiniteHorizonDP/OCExistence.lean) | 18 | Theorem 6.4.1, measurable selection (from Chapter 6) |
| [OCMonotone](InfiniteHorizonDP/OCMonotone.lean) | 1 | Theorem 6.4.2 (from Chapter 6) |
| [OCConcave](InfiniteHorizonDP/OCConcave.lean) | 13 | Theorem 6.4.3 (corrected) (from Chapter 6) |
| [OCConcaveExample](InfiniteHorizonDP/OCConcaveExample.lean) | 5 | Theorem 6.4.3: `G_t` not single-valued (from Chapter 6) |
| [OCDiffTools](InfiniteHorizonDP/OCDiffTools.lean) | 3 | Differentiating concave integrals (from Chapter 6) |
| [OCDifferentiable](InfiniteHorizonDP/OCDifferentiable.lean) | 12 | Theorem 6.4.4, (6.31)–(6.33), Euler equations (from Chapter 6) |
| [OCMaxPrinciple](InfiniteHorizonDP/OCMaxPrinciple.lean) | 5 | §6.5: (6.34)–(6.39), Theorem 6.5.1 (from Chapter 6) |
| [OCMaxPrincipleLinks](InfiniteHorizonDP/OCMaxPrincipleLinks.lean) | 9 | `μ_t = ∂V_t/∂x`, (6.40) (from Chapter 6) |
| [MDPOptimalControl](InfiniteHorizonDP/MDPOptimalControl.lean) | 20 | §5.2.4: control as an MDP (copied) |
| [CSModel](InfiniteHorizonDP/CSModel.lean) | 19 | §6.6.2: the model, cash on hand, Theorem 6.4.1 applies (from Chapter 6) |
| [CSProperties](InfiniteHorizonDP/CSProperties.lean) | 13 | Monotonicity and concavity of `v_n`, the policies (from Chapter 6) |
| [CSDifferentiable](InfiniteHorizonDP/CSDifferentiable.lean) | 23 | Differentiability, FOC, comparisons in `n` and income (from Chapter 6) |
| [CSExercises](InfiniteHorizonDP/CSExercises.lean) | 13 | Exercises 5–7, 10 (from Chapter 6) |
| [CSDeterministic](InfiniteHorizonDP/CSDeterministic.lean) | 4 | Exercise 8 (from Chapter 6) |
| [CSCARA](InfiniteHorizonDP/CSCARA.lean) | 8 | Exercises 9–10 (CARA) (from Chapter 6) |
| [IHExtendedReals](InfiniteHorizonDP/IHExtendedReals.lean) | 9 | ExtendedReals from RecursiveMethods/DeterministicDP (copied) |
| [IHDetPrinciple](InfiniteHorizonDP/IHDetPrinciple.lean) | 20 | Principle, SLP §4.1 from RecursiveMethods/DeterministicDP (copied) |
| [IHEInt](InfiniteHorizonDP/IHEInt.lean) | 14 | The extended integral `ih_eint` and its monotone/dominated convergence theorems |
| [IHLemma711](InfiniteHorizonDP/IHLemma711.lean) | 19 | Assumption 7.1.1, Lemma 7.1.1 |
| [IHBellman](InfiniteHorizonDP/IHBellman.lean) | 6 | Assumption 7.1.2, Theorem 7.1.1, the definitions of p. 197 |
| [IHVerification](InfiniteHorizonDP/IHVerification.lean) | 12 | Theorem 7.1.2, Corollary 7.1.1 |
| [IHConverse](InfiniteHorizonDP/IHConverse.lean) | 14 | Theorem 7.1.3 (corrected) and its counterexample |
| [IHBorrowing](InfiniteHorizonDP/IHBorrowing.lean) | 12 | The borrowing example, pp. 198–199; the gap in the proof of Theorem 7.1.3 |
| [IHLogCopy](InfiniteHorizonDP/IHLogCopy.lean) | 10 | Assumption42, LogGrowth from RecursiveMethods/DeterministicDP (copied) |
| [IHExample711](InfiniteHorizonDP/IHExample711.lean) | 15 | Deterministic Corollary 7.1.1 and Example 7.1.1 |
| [BRContraction](InfiniteHorizonDP/BRContraction.lean) | 8 | Contraction, BoundedReturns, BoundedMonotone from RecursiveMethods/StochasticDP (copied) |
| [BRSetting](InfiniteHorizonDP/BRSetting.lean) | 21 | Assumptions 7.2.1–7.2.3, the operator (7.16), Theorem 7.2.1 |
| [BROptimal](InfiniteHorizonDP/BROptimal.lean) | 12 | P. 205 (value function, optimal plans, measurable selection), Theorem 7.2.2, (7.17), (7.18), p. 206 notation |
| [BRControl](InfiniteHorizonDP/BRControl.lean) | 22 | The control model as an MDP, Assumption 7.3.1, (7.19), (7.20), Theorem 7.3.1 |
| [BRMonotone](InfiniteHorizonDP/BRMonotone.lean) | 6 | Assumption 7.3.2, Theorem 7.3.2 |
| [BRConcave](InfiniteHorizonDP/BRConcave.lean) | 15 | Assumption 7.3.3, Theorem 7.3.3 (corrected) and its affine version, the policy function, p. 209 |
| [BRConcaveExamples](InfiniteHorizonDP/BRConcaveExamples.lean) | 11 | Counterexamples to Theorem 7.3.3 as printed |
| [BRInteriorPoints](InfiniteHorizonDP/BRInteriorPoints.lean) | 3 | InteriorPoints from RecursiveMethods/StochasticDP (copied) |
| [BRDifferentiable](InfiniteHorizonDP/BRDifferentiable.lean) | 5 | Assumptions 7.3.4–7.3.5, (7.21), Theorem 7.3.4 in `ℝⁿ`, (7.22) |
| [BRPolicyConvergence](InfiniteHorizonDP/BRPolicyConvergence.lean) | 4 | Theorem 7.3.5 and the remark of p. 211 |
| [EUTools](InfiniteHorizonDP/EUTools.lean) | 6 | Tools (supergradients, the limit step, inequality (7.38)) |
| [EUMaxPrinciple](InfiniteHorizonDP/EUMaxPrinciple.lean) | 14 | The infinite-horizon Maximum Principle and the transversality condition |
| [EUMaxPrincipleRemark](InfiniteHorizonDP/EUMaxPrincipleRemark.lean) | 3 | The remark after Theorem 7.4.1 (linear `φ` and the sign of `μ*`) |
| [EUEuler](InfiniteHorizonDP/EUEuler.lean) | 14 | The Euler class, Euler equations and transversality conditions |
| [EUEulerSufficiency](InfiniteHorizonDP/EUEulerSufficiency.lean) | 4 | Theorem 7.5.2, sufficiency of the Euler and transversality conditions |
| [EUKamihigashi](InfiniteHorizonDP/EUKamihigashi.lean) | 11 | Theorem 7.5.1 (Kamihigashi), necessity of the transversality condition |
| [EUPhelps](InfiniteHorizonDP/EUPhelps.lean) | 19 | Example 7.5.1 (Phelps 1962; Levhari–Srinivasan 1969) |
| [WNSpace](InfiniteHorizonDP/WNSpace.lean) | 19 | The weighted space `C_ϕ(S)` and Exercise 7.1 |
| [WNWeighted](InfiniteHorizonDP/WNWeighted.lean) | 6 | The Weighted Contraction Mapping Theorem (Theorem 7.3.6) |
| [WNAKModel](InfiniteHorizonDP/WNAKModel.lean) | 15 | Example 7.3.1: the deterministic AK model with `u = C^γ` |
| [WNDuran](InfiniteHorizonDP/WNDuran.lean) | 10 | Duran's weighted-norm approach: (7.24)–(7.28) and Exercise 7.2 |
| [WNGrowth](InfiniteHorizonDP/WNGrowth.lean) | 21 | Example 7.3.2, Exercise 7.3 and the log AK model |
| [EXRamsey](InfiniteHorizonDP/EXRamsey.lean) | 12 | Exercise 7.4 |
| [EXPhelps](InfiniteHorizonDP/EXPhelps.lean) | 13 | Exercise 7.6 (Bellman equation, constants), Exercise 7.8 (finite horizon, limit) |
| [EXPhelpsMDP](InfiniteHorizonDP/EXPhelpsMDP.lean) | 32 | Exercise 7.6 verified by Theorem 7.1.2 / Corollary 7.1.1; Exercise 7.10, (7.4) for all plans |
| [EXPhelpsTVC](InfiniteHorizonDP/EXPhelpsTVC.lean) | 5 | Exercise 7.10, (7.4) versus (7.35) |
| [EXLogGrowth](InfiniteHorizonDP/EXLogGrowth.lean) | 12 | Exercise 7.5 |
| [EXCARA](InfiniteHorizonDP/EXCARA.lean) | 11 | Exercise 7.7, the limit policies and the Bellman equation of the limit |
| [EXCARAMDP](InfiniteHorizonDP/EXCARAMDP.lean) | 19 | Exercise 7.7, optimality on `Π̂` and the Ponzi counterexample |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
