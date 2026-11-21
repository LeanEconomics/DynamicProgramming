# Miao Chapter 9: Linear-Quadratic Models, in Lean

This is the `EconomicDynamics/LinearQuadratic` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 9 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 9 studies linear-quadratic control: the controlled linear state-space system, the
finite-horizon problem and the Riccati recursion, infinite-horizon limits, optimal policy under
commitment and under discretion in models with forward-looking variables, and robust control.
Every numbered result (Assumption 9.1.1, Definitions 9.1.1–9.1.4 and 9.5.1, Propositions 9.2.1
and 9.3.1–9.3.2, Examples 9.4.1–9.4.2 and 9.5.1), the derivations of the text and Exercises 1–5
are proved, except the derivation of the filter (9.3) (Chapter 10), convergence of the iteration
for the discretionary equilibrium (the book does not prove it either), strong duality for the
multiplier of the constraint problem, and the realness of the complex QZ coefficients in the
recursive commitment form. The corrections are recorded in [corrections](docs/corrections.md),
and every book item is located in the [source map](docs/source-map.md). The library contains
**855 theorems**; 496 of them are carried over from Chapters 1–2 and from Sargent–Stachurski.

* **The state-space system** (§9.1): stable matrices by the spectral radius (`ls_stable_iff_specRad`),
  stabilizability, controllability, observability and detectability (`definition_9_1_2_iff`,
  `definition_9_1_3_iff`, `controllable_stabilizable`), where "for any `r > 0`" holds only for
  `r ≥ n` (`ls_controllable_not_reach_one`, `ls_observable_not_two_outputs`); the error equation
  below (9.3) is misprinted (`eq_9_3_error`, `eq_9_3_misprint`).
* **Finite horizon** (§9.2): Proposition 9.2.1 with the Riccati recursion and certainty
  equivalence (`LSFinProblem.proposition_9_2_1`, `LSFinProblem.certainty_equivalence`).
* **Infinite-horizon limits** (§9.3): Propositions 9.3.1–9.3.2, with the existence of the
  Riccati fixed point (`LSProblem.proposition_9_3_1`, `LSProblem.proposition_9_3_2`,
  `ls_riccati_main`), the value function and policy (`eq_9_16_9_17`, `ls_verification`); `P(s)`
  increases only weakly (`ls_P_mono_not_strict`) and the bound of p. 300 has the wrong
  remainder (`ls_P_le_policy_misprint`); Exercises 1, 2 and Hall's problem, whose Riccati
  equation has two solutions (`ex_9_1`, `ex_9_2`, `ex_9_4_two_solutions`).
* **Commitment** (§9.4): the Lagrangian first-order conditions, the saddle path by Klein's
  method and time inconsistency (`eq_foc_9_4`, `cp_saddle_path`, `cp_time_inconsistency`); the
  New Keynesian Examples 9.4.1–9.4.2, whose printed `5 × 5` system has a wrong row
  (`example_9_4_2_system`, `example_9_4_2_printed_row_false`, `ex942_solution`).
* **Discretion** (§9.5): Markov perfect equilibrium (`definition_9_5_1`); the derivation steps,
  with (9.36) and the Step 2 formulas corrected (`eq_9_37`, `eq_9_36_false`, `eq_step2`); a fixed
  point is an equilibrium (`cp_mpe_of_fixed_point`); Example 9.5.1 and commitment versus
  discretion (`example_9_5_1`, `cp_commitment_vs_discretion`).
* **Robust control** (§9.6): likelihood ratios, the martingale and entropy
  (`rc_martingale`, `rc_entropy_decomp`); the multiplier and constraint problems
  (`rc_lagrange`, `rc_breakdown`); the Gibbs worst case, whose first-order condition is
  misprinted (`eq_9_47_9_48`, `eq_9_47_misprint`); the operator `D(P)` and (9.51)–(9.55) for the
  standard normal shock, with the multivariate Gaussian integral proved (`eq_9_51_9_55_std`,
  `rc_gaussian_std`); relative entropy of normals (`eq_9_56`) and modified certainty
  equivalence (`rc_modified_ce`); Exercises 3 and 5 (`ex_9_3`, `ex_9_5`).

All names are in the namespace `Miao.LinearQuadratic`. The modules `DeterministicBasics` …
`Singular` are copied from [EconomicDynamics/DifferenceEquations](../DifferenceEquations/README.md)
by way of [EconomicDynamics/RationalExpectations](../RationalExpectations/README.md), which `Basics`
… `KleinSimplified` come from; the `SS*` modules are copied from
[GeneralStates/AbstractDecisionProcesses](../../GeneralStates/AbstractDecisionProcesses/README.md)
into the namespace `Miao.LinearQuadratic.SS`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DeterministicBasics](LinearQuadratic/DeterministicBasics.lean) | 3 | Definitions of Chapter 1 (from Chapter 1) |
| [Triangular](LinearQuadratic/Triangular.lean) | 14 | Powers of triangular matrices (from Chapter 1) |
| [Spectral](LinearQuadratic/Spectral.lean) | 16 | Stable and unstable subspaces (copied) |
| [RealSplitting](LinearQuadratic/RealSplitting.lean) | 24 | The real splitting `E_s ⊕ E_u` and its dimension (copied) |
| [Dichotomy](LinearQuadratic/Dichotomy.lean) | 16 | Projections and geometric bounds (copied) |
| [LinearSystems](LinearQuadratic/LinearSystems.lean) | 28 | §1.4: stable matrices, regularity, the steady state (1.21) (from Chapter 1) |
| [QZ](LinearQuadratic/QZ.lean) | 27 | Definition 1.4.6, Theorem 1.4.4 (generalized Schur form) (from Chapter 1) |
| [Singular](LinearQuadratic/Singular.lean) | 48 | §1.4.2: Theorem 1.4.5 (Klein), the Cagan example, augmentation (from Chapter 1) |
| [Basics](LinearQuadratic/Basics.lean) | 8 | `CondExpSystem`, adapted and stable processes, the system (2.11) (from Chapter 2) |
| [CondExpL1](LinearQuadratic/CondExpL1.lean) | 13 | The `L¹` conditional expectations as a `CondExpSystem` (from Chapter 2) |
| [VARMoments](LinearQuadratic/VARMoments.lean) | 43 | §2.1: means, the Lyapunov equation, autocovariances, impulse responses; white noise (from Chapter 2) |
| [KleinMartingales](LinearQuadratic/KleinMartingales.lean) | 6 | Definitions 2.3.2 and 2.3.4 (from Chapter 2) |
| [StochasticKlein](LinearQuadratic/StochasticKlein.lean) | 67 | §2.3.2: the stochastic Klein theorem (from Chapter 2) |
| [KleinSimplified](LinearQuadratic/KleinSimplified.lean) | 8 | The simplified Klein form (from Chapter 2) |
| [SSBasics](LinearQuadratic/SSBasics.lean) | 18 | Restated: Markov matrices, contractions, global stability, Blackwell (Sargent–Stachurski, copied) |
| [SSSpectralRadius](LinearQuadratic/SSSpectralRadius.lean) | 29 | Restated: spectral radius, Gelfand's formula, Neumann series (Sargent–Stachurski, copied) |
| [SSOrderTheory](LinearQuadratic/SSOrderTheory.lean) | 17 | Lemma A.1.5, Thm A.5.2, Lemmas A.5.3–A.5.5, Thm A.5.6, Lemma A.5.19 (Sargent–Stachurski, copied) |
| [SSADP](LinearQuadratic/SSADP.lean) | 25 | §2.1, Lemmas 2.1.1–2.1.3, Prop 2.1.4, Thms 2.1.5, 2.1.7, Ex 2.1.1 (Sargent–Stachurski, copied) |
| [SSAlgorithms](LinearQuadratic/SSAlgorithms.lean) | 26 | §2.2.1–2.2.2, Lemmas 2.2.1–2.2.4, Thms 2.2.6–2.2.8, Ex 2.2.1–2.2.2 (Sargent–Stachurski, copied) |
| [SSMinimization](LinearQuadratic/SSMinimization.lean) | 17 | §2.2.3, Ex 2.2.3–2.2.6, Thm 2.2.9, Cor 2.2.10 (Sargent–Stachurski, copied) |
| [SSLQAlgebra](LinearQuadratic/SSLQAlgebra.lean) | 19 | §2.3.5.1–2.3.5.2, Lemma 2.3.3, Ex 2.3.13–2.3.14, 2.3.16–2.3.17 (Sargent–Stachurski, copied) |
| [SSLQControl](LinearQuadratic/SSLQControl.lean) | 24 | §2.3.5.3–2.3.5.8, Lemmas 2.3.5–2.3.9, Ex 2.3.15, Example 2.3.1 (Sargent–Stachurski, copied) |
| [LSStability](LinearQuadratic/LSStability.lean) | 12 | Stable matrices and asymptotic tools for Chapter 9 |
| [LSRiccati](LinearQuadratic/LSRiccati.lean) | 19 | The LQ problem, the Riccati operator and completing the square |
| [LSFiniteHorizon](LinearQuadratic/LSFiniteHorizon.lean) | 19 | Finite-horizon LQ problems: Proposition 9.2.1 |
| [LSStateSpace](LinearQuadratic/LSStateSpace.lean) | 20 | The controlled linear state-space system (Miao §9.1) |
| [LSRiccatiConvergence](LinearQuadratic/LSRiccatiConvergence.lean) | 27 | Convergence of the Riccati iteration (the undiscounted core of Propositions 9.3.1–9.3.2) |
| [LSInfiniteHorizon](LinearQuadratic/LSInfiniteHorizon.lean) | 28 | Infinite-horizon limits: Propositions 9.3.1 and 9.3.2 |
| [LSInfiniteLimits](LinearQuadratic/LSInfiniteLimits.lean) | 11 | Limits, the side condition and the numerical methods of §9.3 |
| [LSExercises](LinearQuadratic/LSExercises.lean) | 6 | Exercises 9.1 and 9.2 |
| [LSHall](LinearQuadratic/LSHall.lean) | 13 | Exercise 9.4: Hall's consumption problem |
| [CPRamsey](LinearQuadratic/CPRamsey.lean) | 12 | Optimal policy under commitment: the Ramsey problem and its first-order conditions |
| [CPSaddlePath](LinearQuadratic/CPSaddlePath.lean) | 7 | Optimal policy under commitment: the saddle path and time inconsistency |
| [CPNKCommitment](LinearQuadratic/CPNKCommitment.lean) | 25 | The New Keynesian model under commitment: Examples 9.4.1 and 9.4.2 |
| [CPDiscretion](LinearQuadratic/CPDiscretion.lean) | 27 | Optimal discretionary policy: Markov perfect equilibrium in linear rules |
| [CPNKDiscretion](LinearQuadratic/CPNKDiscretion.lean) | 9 | The New Keynesian model under discretion: Example 9.5.1, and commitment versus discretion |
| [RCEntropy](LinearQuadratic/RCEntropy.lean) | 36 | Belief distortions and entropy |
| [RCProblems](LinearQuadratic/RCProblems.lean) | 10 | The constraint and multiplier problems |
| [RCGibbs](LinearQuadratic/RCGibbs.lean) | 10 | The worst-case distortion and the risk-sensitive operator |
| [RCRobustLQ](LinearQuadratic/RCRobustLQ.lean) | 24 | The linear-quadratic robust control problem |
| [RCNormal](LinearQuadratic/RCNormal.lean) | 15 | The worst-case normal distribution and relative entropy of normals |
| [RCExercise3](LinearQuadratic/RCExercise3.lean) | 11 | Exercise 9.3: the multiplier problem as `θ → ∞` |
| [RCHall](LinearQuadratic/RCHall.lean) | 11 | Exercise 9.5: the robust consumption rule |
| [RCGaussianStd](LinearQuadratic/RCGaussianStd.lean) | 7 | The standard normal shock satisfies the Gaussian identity |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
