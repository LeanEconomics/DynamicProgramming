# Miao Chapter 6: Finite-Horizon Dynamic Programming, in Lean

This is the `EconomicDynamics/FiniteHorizonDP` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 6 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 6 solves finite-horizon problems by backward induction: a motivating growth example, the
measurability problem, the principle of optimality in the Markov decision model of Chapter 5,
optimal control with continuity, monotonicity, concavity and differentiability of the value
functions, the maximum principle, and two applications, the secretary problem and
consumption–saving. Every numbered result (Assumptions 6.3.1 and 6.4.1–6.4.14, Lemmas 6.3.1 and
6.4.1, Theorems 6.3.1–6.3.3, 6.4.1–6.4.4 and 6.5.1, Proposition 6.6.1), the derivations of the
text and Exercises 1–10 are proved, except Theorem 6.4.4 beyond one dimension, Souslin's
non-Borel projection, the large-`N` limits of Exercises 3–4 and a closed form for Exercise 10
beyond one period. The corrections are recorded in
[corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **570 theorems**; 166 of them are
carried over from Chapter 5 and from Stokey–Lucas–Prescott.

* **The motivating example** (§6.1): the solution (6.3) of the Euler equation is the unique
  solution (`eq_6_3`, `eq_6_3_unique`), the value function (6.5)–(6.6) (`eq_6_5_6_6`), the Bellman
  equation as a maximisation (`po61_bellman`) and time consistency (`time_consistency_6_1`); the
  printed `C_{T−1}` in (6.8) is wrong (`eq_6_8_misprint`).
* **Measurability** (§6.2): the two-step argument (`two_step_6_2`); the printed projection
  identity is false (`proj_identity_6_2_misprint`), and `V₁*` is measurable exactly when the
  projection is (`blackwell_6_2`).
* **The principle of optimality** (§6.3): Lemma 6.3.1, Theorem 6.3.1 with jointly measurable
  ε-plans (`lemma_6_3_1`, `theorem_6_3_1`), the verification Theorem 6.3.2 (`theorem_6_3_2`), and
  Theorem 6.3.3, which holds only almost surely (`theorem_6_3_3`,
  `theorem_6_3_3_counterexample`); the deterministic case (Exercise 1) and the stochastic growth
  model (Exercise 2, `ex_6_2_policies`, `ex_6_2_optimal`).
* **Optimal control** (§6.4): Lemma 6.4.1, false for unbounded rewards with countable shocks
  (`lemma_6_4_1_countable_counterexample`); existence and measurable selection
  (`theorem_6_4_1_compact`, `theorem_6_4_1_selection`); the Bellman solution is the value of the
  decision problem and generated plans are optimal (`p175`, `p175_control`); monotonicity
  (`theorem_6_4_2`); concavity, with `G_t` not single-valued as printed (`theorem_6_4_3`,
  `theorem_6_4_3_counterexample`); the envelope and first-order conditions under corrected
  hypotheses (`theorem_6_4_4`, `euler_equations`).
* **The maximum principle** (§6.5): sufficiency (`theorem_6_5_1`), the multipliers as derivatives
  of the value functions (`maxPrinciple_of_dp`), and the corrected terminal condition of (6.40)
  (`eq_6_40_terminal`, `eq_6_40_terminal_misprint`).
* **The secretary problem** (§6.6.1): the Bellman equations and the optimal rule, which rejects
  `τ − 1` candidates, not `τ` (`prop_6_6_1`, `prop_6_6_1_misprint`), `τ(4) = 2`
  (`sec_tau_four`), `τ(N)/N → 1/e` (`sec_tau_limit`); Exercises 3–4 (`ex_6_3_rank2`,
  `ex_6_4_threshold`).
* **Consumption–saving** (§6.6.2): the properties of the policies, proved directly because
  Assumption 6.4.10 fails for `u(x − s)` (`CSModel.not_assumption6410`), with saving and the
  horizon effects only weakly monotone (`not_strictMonoOn_sav`, `exists_cons_succ_eq`) and the
  income comparison as printed (`cons_ge_low`, `cons_le_high`); Markov income, Phelps, CRRA,
  CARA and Levhari–Mirman–Zilcha (`ex_6_6` … `ex_6_10`).

All names are in the namespace `Miao.FiniteHorizonDP`. The `MDP*` modules are copied from
[EconomicDynamics/MarkovDecisionProcesses](../MarkovDecisionProcesses/README.md), and the `SLP*`
modules from [RecursiveMethods/StochasticDP](../../RecursiveMethods/StochasticDP/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MDPHistoryTools](FiniteHorizonDP/MDPHistoryTools.lean) | 6 | Histories (copied) |
| [MDPBasics](FiniteHorizonDP/MDPBasics.lean) | 8 | The model (5.1) (copied) |
| [MDPHistories](FiniteHorizonDP/MDPHistories.lean) | 12 | Finite histories (copied) |
| [MDPObjective](FiniteHorizonDP/MDPObjective.lean) | 22 | Objectives and values (copied) |
| [MDPSimulation](FiniteHorizonDP/MDPSimulation.lean) | 8 | Transport between models (copied) |
| [MDPKernelTools](FiniteHorizonDP/MDPKernelTools.lean) | 4 | Kernel builders (copied) |
| [MDPOptimalStopping](FiniteHorizonDP/MDPOptimalStopping.lean) | 29 | Stopping as an MDP (copied) |
| [MDPStoppingExamples](FiniteHorizonDP/MDPStoppingExamples.lean) | 14 | Stopping examples (copied) |
| [MDPSecretary](FiniteHorizonDP/MDPSecretary.lean) | 6 | The secretary model (copied) |
| [POHistory](FiniteHorizonDP/POHistory.lean) | 23 | Problems from date `t`, plans from a history, continuation plans, (6.12)–(6.14) |
| [POPrinciple](FiniteHorizonDP/POPrinciple.lean) | 18 | Assumption 6.3.1, Lemma 6.3.1, Theorem 6.3.1 |
| [POVerification](FiniteHorizonDP/POVerification.lean) | 10 | Plans generated by `G_t`, Theorem 6.3.2 |
| [POConverse](FiniteHorizonDP/POConverse.lean) | 3 | Theorem 6.3.3 (almost surely) |
| [POCounterexample](FiniteHorizonDP/POCounterexample.lean) | 6 | Theorem 6.3.3 fails everywhere |
| [PODeterministic](FiniteHorizonDP/PODeterministic.lean) | 17 | Exercise 1: the deterministic case |
| [POMotivating](FiniteHorizonDP/POMotivating.lean) | 32 | §6.1: (6.3)–(6.8), the Bellman equation, time consistency |
| [POMeasurability](FiniteHorizonDP/POMeasurability.lean) | 10 | §6.2: the two-step argument, projections |
| [POStochasticGrowth](FiniteHorizonDP/POStochasticGrowth.lean) | 5 | Exercise 2: the value function and policies |
| [POStochasticGrowthMDP](FiniteHorizonDP/POStochasticGrowthMDP.lean) | 8 | Exercise 2: optimality in the MDP |
| [SecretaryBellman](FiniteHorizonDP/SecretaryBellman.lean) | 20 | §6.6.1: (6.41)–(6.43), thresholds, the closed form |
| [SecretaryMDP](FiniteHorizonDP/SecretaryMDP.lean) | 23 | Proposition 6.6.1 and the MDP values |
| [SecretaryAsymptotic](FiniteHorizonDP/SecretaryAsymptotic.lean) | 6 | `τ(N)/N → 1/e` |
| [SecretaryExercises](FiniteHorizonDP/SecretaryExercises.lean) | 24 | Exercises 3–4 |
| [SecretaryTwoMDP](FiniteHorizonDP/SecretaryTwoMDP.lean) | 18 | Exercise 3 as an MDP |
| [SLPCorrespondences](FiniteHorizonDP/SLPCorrespondences.lean) | 2 | Correspondences (copied) |
| [SLPTransitionFunctions](FiniteHorizonDP/SLPTransitionFunctions.lean) | 0 | `markovOpR`, `IsFeller` (copied) |
| [SLPMaximum](FiniteHorizonDP/SLPMaximum.lean) | 14 | Theorem of the Maximum (copied) |
| [SLPSelection](FiniteHorizonDP/SLPSelection.lean) | 8 | Measurable selection (copied) |
| [SLPEnvelope](FiniteHorizonDP/SLPEnvelope.lean) | 2 | Benveniste–Scheinkman (copied) |
| [SLPLemma95](FiniteHorizonDP/SLPLemma95.lean) | 11 | SLP Lemmas 9.5, 9.5′ (copied) |
| [OCSetting](FiniteHorizonDP/OCSetting.lean) | 5 | §6.4: the model, (6.28)–(6.29), Assumptions 6.4.1–6.4.14 |
| [OCLemma641](FiniteHorizonDP/OCLemma641.lean) | 10 | Lemma 6.4.1 |
| [OCExistence](FiniteHorizonDP/OCExistence.lean) | 18 | Theorem 6.4.1, measurable selection |
| [OCMonotone](FiniteHorizonDP/OCMonotone.lean) | 1 | Theorem 6.4.2 |
| [OCConcave](FiniteHorizonDP/OCConcave.lean) | 13 | Theorem 6.4.3 (corrected) |
| [OCConcaveExample](FiniteHorizonDP/OCConcaveExample.lean) | 5 | Theorem 6.4.3: `G_t` not single-valued |
| [OCDiffTools](FiniteHorizonDP/OCDiffTools.lean) | 3 | Differentiating concave integrals |
| [OCDifferentiable](FiniteHorizonDP/OCDifferentiable.lean) | 12 | Theorem 6.4.4, (6.31)–(6.33), Euler equations |
| [OCMaxPrinciple](FiniteHorizonDP/OCMaxPrinciple.lean) | 5 | §6.5: (6.34)–(6.39), Theorem 6.5.1 |
| [OCMaxPrincipleLinks](FiniteHorizonDP/OCMaxPrincipleLinks.lean) | 9 | `μ_t = ∂V_t/∂x`, (6.40) |
| [MDPOptimalControl](FiniteHorizonDP/MDPOptimalControl.lean) | 20 | §5.2.4: control as an MDP (copied) |
| [OCBridge](FiniteHorizonDP/OCBridge.lean) | 20 | p. 175: Theorem 6.3.2 applied to §6.4 |
| [CSModel](FiniteHorizonDP/CSModel.lean) | 19 | §6.6.2: the model, cash on hand, Theorem 6.4.1 applies |
| [CSProperties](FiniteHorizonDP/CSProperties.lean) | 13 | Monotonicity and concavity of `v_n`, the policies |
| [CSDifferentiable](FiniteHorizonDP/CSDifferentiable.lean) | 23 | Differentiability, FOC, comparisons in `n` and income |
| [CSExercises](FiniteHorizonDP/CSExercises.lean) | 13 | Exercises 5–7, 10 |
| [CSDeterministic](FiniteHorizonDP/CSDeterministic.lean) | 4 | Exercise 8 |
| [CSCARA](FiniteHorizonDP/CSCARA.lean) | 8 | Exercises 9–10 (CARA) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
