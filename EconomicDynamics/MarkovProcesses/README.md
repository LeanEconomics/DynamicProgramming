# Miao Chapter 3: Markov Processes, in Lean

This is the `EconomicDynamics/MarkovProcesses` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 3 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 3 studies Markov chains (finite and countable), general Markov processes and their
construction, and strong and weak convergence to invariant distributions. Every numbered result
is proved, except the limits in Theorem 3.1.5(b)–(c) for countable chains (they need the renewal
theorem), the converse of Proposition 3.3.1 beyond countable spaces, and the integral form of the
ergodic decomposition in Theorem 3.3.4; so are Exercises 1–6. The corrections are recorded in
[corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **470 theorems**; 194 of them are copied
from Stokey–Lucas–Prescott Chapters 8, 11 and 12 and from Meyn–Tweedie.

* **Markov chains** (§3.1): classes, recurrence and periods (`theorem_3_1_1a`, `theorem_3_1_2`);
  convergence to the unique stationary distribution (`theorem_3_1_3`, `theorem_3_1_4`); countable
  chains, the transient, null and positive recurrent cases and `π_j = 1/E[τ_j]`
  (`theorem_3_1_5a`, `theorem_3_1_5c`). Example 3.1.2 does have a stationary distribution
  (`example_3_1_2_stationary`), and two claims about countable chains fail
  (`theorem_3_1_1b_countable_counterexample`, `theorem_3_1_4_countable_counterexample`).
* **General Markov processes** (§3.2): kernels and their products (`theorem_3_2_1`), Kolmogorov
  extension on standard Borel spaces (`theorem_3_2_2`), the Markov process from `μ₀` and `P`
  (`theorem_3_2_3`), Ionescu Tulcea (`theorem_3_2_4`), and the operators `T`, `T*` (`ex_3_4`).
* **Strong convergence** (§3.3.1): Condition M gives a unique invariant distribution and geometric
  convergence in total variation (`theorem_3_3_1`); the converse of Proposition 3.3.1 fails with
  the same `N` (`proposition_3_3_1_counterexample`).
* **Weak convergence** (§3.3.2): Prohorov, whose "only if" is false as printed
  (`theorem_3_3_2`, `theorem_3_3_2_counterexample`), Krylov–Bogolubov (`theorem_3_3_3`), ergodic
  measures as extreme points (`theorem_3_3_4_extreme`), monotone processes (`theorem_3_3_5`) and
  dependence on parameters (`theorem_3_3_6`).

All names are in the namespace `Miao.MarkovProcesses`. Modules named `…SLP…` are copied from
[RecursiveMethods](../../RecursiveMethods/StrongConvergence/README.md) Chapters 8, 11 and 12, and
`ChainNumberTheory` from Meyn–Tweedie.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ChainNumberTheory](MarkovProcesses/ChainNumberTheory.lean) | 11 | Period arithmetic (copied from Meyn–Tweedie) |
| [ChainBasics](MarkovProcesses/ChainBasics.lean) | 20 | Definition 3.0.1, stochastic matrices, accessibility |
| [ChainClasses](MarkovProcesses/ChainClasses.lean) | 13 | Classes, recurrence, Theorems 3.1.1–3.1.2 |
| [ChainStationary](MarkovProcesses/ChainStationary.lean) | 39 | Theorems 3.1.3–3.1.4, stationary distributions of finite chains |
| [ChainExamples](MarkovProcesses/ChainExamples.lean) | 26 | Examples 3.1.1–3.1.3 and 3.1.6 |
| [ChainExercises](MarkovProcesses/ChainExercises.lean) | 10 | Exercises 1, 3, 6 |
| [ChainCountable](MarkovProcesses/ChainCountable.lean) | 34 | Countable chains: first passage, recurrence |
| [ChainProcess](MarkovProcesses/ChainProcess.lean) | 5 | Chains on path space |
| [ChainCountableStationary](MarkovProcesses/ChainCountableStationary.lean) | 25 | Theorem 3.1.5 |
| [ChainCountableExamples](MarkovProcesses/ChainCountableExamples.lean) | 16 | Examples 3.1.4–3.1.5 |
| [GeneralSLPTransitionFunctions](MarkovProcesses/GeneralSLPTransitionFunctions.lean) | 19 | Transition functions, `T`, `T*` (copied from SLP Ch 8) |
| [GeneralKernels](MarkovProcesses/GeneralKernels.lean) | 13 | Definition 3.2.1, Theorem 3.2.1, Definition 3.2.2, Exercise 4 |
| [GeneralExtension](MarkovProcesses/GeneralExtension.lean) | 20 | Theorems 3.2.2–3.2.5, Exercise 2 |
| [ConvergenceSLPTotalVariation](MarkovProcesses/ConvergenceSLPTotalVariation.lean) | 15 | Total variation (copied from SLP Ch 11) |
| [ConvergenceSLPTVConvergence](MarkovProcesses/ConvergenceSLPTVConvergence.lean) | 12 | Convergence in total variation (copied) |
| [ConvergenceSLPConditionM](MarkovProcesses/ConvergenceSLPConditionM.lean) | 12 | Condition M (copied) |
| [ConvergenceStrong](MarkovProcesses/ConvergenceStrong.lean) | 22 | Theorem 3.3.1, Proposition 3.3.1, Examples 3.3.1–3.3.3 |
| [ConvergenceExercises](MarkovProcesses/ConvergenceExercises.lean) | 5 | Exercise 5 |
| [ConvergenceSLPWeakBasics](MarkovProcesses/ConvergenceSLPWeakBasics.lean) | 10 | Weak convergence (copied from SLP Ch 12) |
| [ConvergenceSLPPortmanteau](MarkovProcesses/ConvergenceSLPPortmanteau.lean) | 9 | Portmanteau (copied) |
| [ConvergenceSLPDetermining](MarkovProcesses/ConvergenceSLPDetermining.lean) | 10 | Determining classes (copied) |
| [ConvergenceSLPDistributionFunctions](MarkovProcesses/ConvergenceSLPDistributionFunctions.lean) | 14 | Distribution functions (copied) |
| [ConvergenceSLPDistributionConvergence](MarkovProcesses/ConvergenceSLPDistributionConvergence.lean) | 14 | Convergence of distribution functions (copied) |
| [ConvergenceSLPHelly](MarkovProcesses/ConvergenceSLPHelly.lean) | 16 | Helly's theorem (copied) |
| [ConvergenceSLPFellerInvariant](MarkovProcesses/ConvergenceSLPFellerInvariant.lean) | 17 | Feller processes and invariant measures (copied) |
| [ConvergenceWeak](MarkovProcesses/ConvergenceWeak.lean) | 9 | Definitions 3.3.2–3.3.4, Theorems 3.3.2–3.3.3, Corollary 3.3.1 |
| [ConvergenceErgodic](MarkovProcesses/ConvergenceErgodic.lean) | 14 | Definition 3.3.5, Theorem 3.3.4 |
| [ConvergenceSLPMonotoneProcesses](MarkovProcesses/ConvergenceSLPMonotoneProcesses.lean) | 26 | Monotone processes, SLP Theorem 12.12 (copied) |
| [ConvergenceSLPParameters](MarkovProcesses/ConvergenceSLPParameters.lean) | 9 | Dependence on parameters, SLP Theorem 12.13 (copied) |
| [ConvergenceMonotone](MarkovProcesses/ConvergenceMonotone.lean) | 5 | Definition 3.3.6, Theorems 3.3.5–3.3.6 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
