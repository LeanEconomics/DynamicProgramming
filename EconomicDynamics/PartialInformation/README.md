# Miao Chapter 10: Control under Partial Information, in Lean

This is the `EconomicDynamics/PartialInformation` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 10 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 10 studies filtering and control when the state is not observed: the Kalman filter for
linear state-space systems, filters for hidden Markov chains and Markov-switching models, control
problems with the belief as the state, and linear-quadratic control under partial information.
Every example (Examples 10.1.1–10.1.4 and 10.2.1), the derivations of the text and Exercises 1–6
are proved. The Kalman filter is proved as recursive linear least-squares projection on an
arbitrary probability space, from second moments alone; the statements that conditional laws
are Gaussian and that innovations are independent (the Gaussian reading) are not formalised,
nor is the filter for the non-linear state of Exercise 2 (the filter conditional on `ρ` is).
The corrections are recorded in [corrections](docs/corrections.md), and every book item is
located in the [source map](docs/source-map.md). The library contains **682 theorems**; 476 of
them are carried over from Chapters 1, 2 and 9 and from Sargent–Stachurski.

* **The Kalman filter** (§10.1.1): the time-varying system and filter (`KFSystem`), the gain as
  the unique minimiser of the error covariance (`eq_10_10`), the Joseph form and the filtered
  covariance (`KFSystem.eq_10_11`, `eq_10_11_gain`), the projection theorem and orthogonality of
  the innovations (`KFSystem.eq_10_12`, `KFSystem.kf_innov_orth`); the cross moment (10.9) is
  `C_{t−1}`, not `C_t`, which changes (10.8)–(10.11) and the Riccati equations
  (`KFSystem.eq_10_9`, `kf_cross_book_false`); the stationary filter by duality with Chapter 9's
  regulator (`kf_dual_T`, `kf_steady_state`); Examples 10.1.1–10.1.4 (`example_10_1_1` …
  `example_10_1_4`, `example_10_1_1_misprint`).
* **Hidden Markov chains** (§10.1.2–10.1.3): the state-space form (10.13)–(10.14)
  (`eq_10_13`, `eq_10_14_cov`), Bayes' rule and the likelihood (`hm_bayes`, `hm_lik_snoc`), the
  Hamilton filter with its misprinted update corrected (`hm_hamilton_predict`,
  `hm_hamilton_update`).
* **Control problems** (§10.2): the Bellman equation in beliefs, with the belief proved a
  sufficient statistic (`hm_bellman`, `hm_J_le_V`, `hm_J_beliefPol`, `hm_value_isGreatest`);
  Guvenen's life-cycle model (`example_10_2_1`, `eq_10_16`).
* **Linear-quadratic control** (§10.3): certainty equivalence with the filtered state — the same
  Riccati solution and gain as with full information (`kf_certainty_equivalence`, `kf_filt_T`).
* **Exercises**: `ex_10_1` … `ex_10_5`, and Exercise 6 (`ex_10_6_a_recursion`, `ex_10_6_b`,
  `ex_10_6_c`, `ex_10_6_d`).

All names are in the namespace `Miao.PartialInformation`. The `LS*` modules are copied from
[EconomicDynamics/LinearQuadratic](../LinearQuadratic/README.md), which carries the Chapter 1–2
modules and the Sargent–Stachurski `SS*` chain (namespace `Miao.PartialInformation.SS`).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DeterministicBasics](PartialInformation/DeterministicBasics.lean) | 3 | Definitions of Chapter 1 (from Chapter 1) |
| [Triangular](PartialInformation/Triangular.lean) | 14 | Powers of triangular matrices (from Chapter 1) |
| [Spectral](PartialInformation/Spectral.lean) | 16 | Stable and unstable subspaces (copied) |
| [RealSplitting](PartialInformation/RealSplitting.lean) | 24 | The real splitting `E_s ⊕ E_u` and its dimension (copied) |
| [Dichotomy](PartialInformation/Dichotomy.lean) | 16 | Projections and geometric bounds (copied) |
| [LinearSystems](PartialInformation/LinearSystems.lean) | 28 | §1.4: stable matrices, regularity, the steady state (1.21) (from Chapter 1) |
| [Basics](PartialInformation/Basics.lean) | 8 | `CondExpSystem`, adapted and stable processes, the system (2.11) (from Chapter 2) |
| [CondExpL1](PartialInformation/CondExpL1.lean) | 13 | The `L¹` conditional expectations as a `CondExpSystem` (from Chapter 2) |
| [VARMoments](PartialInformation/VARMoments.lean) | 43 | §2.1: means, the Lyapunov equation, autocovariances, impulse responses; white noise (from Chapter 2) |
| [SSBasics](PartialInformation/SSBasics.lean) | 18 | Restated: Markov matrices, contractions, global stability, Blackwell (Sargent–Stachurski, copied) |
| [SSSpectralRadius](PartialInformation/SSSpectralRadius.lean) | 29 | Restated: spectral radius, Gelfand's formula, Neumann series (Sargent–Stachurski, copied) |
| [SSOrderTheory](PartialInformation/SSOrderTheory.lean) | 17 | Lemma A.1.5, Thm A.5.2, Lemmas A.5.3–A.5.5, Thm A.5.6, Lemma A.5.19 (Sargent–Stachurski, copied) |
| [SSADP](PartialInformation/SSADP.lean) | 25 | §2.1, Lemmas 2.1.1–2.1.3, Prop 2.1.4, Thms 2.1.5, 2.1.7, Ex 2.1.1 (Sargent–Stachurski, copied) |
| [SSAlgorithms](PartialInformation/SSAlgorithms.lean) | 26 | §2.2.1–2.2.2, Lemmas 2.2.1–2.2.4, Thms 2.2.6–2.2.8, Ex 2.2.1–2.2.2 (Sargent–Stachurski, copied) |
| [SSMinimization](PartialInformation/SSMinimization.lean) | 17 | §2.2.3, Ex 2.2.3–2.2.6, Thm 2.2.9, Cor 2.2.10 (Sargent–Stachurski, copied) |
| [SSLQAlgebra](PartialInformation/SSLQAlgebra.lean) | 19 | §2.3.5.1–2.3.5.2, Lemma 2.3.3, Ex 2.3.13–2.3.14, 2.3.16–2.3.17 (Sargent–Stachurski, copied) |
| [SSLQControl](PartialInformation/SSLQControl.lean) | 24 | §2.3.5.3–2.3.5.8, Lemmas 2.3.5–2.3.9, Ex 2.3.15, Example 2.3.1 (Sargent–Stachurski, copied) |
| [LSStability](PartialInformation/LSStability.lean) | 12 | Stable matrices and asymptotic tools for Chapter 9 (from Chapter 9) |
| [LSRiccati](PartialInformation/LSRiccati.lean) | 19 | The LQ problem, the Riccati operator and completing the square (from Chapter 9) |
| [LSFiniteHorizon](PartialInformation/LSFiniteHorizon.lean) | 19 | Finite-horizon LQ problems: Proposition 9.2.1 (from Chapter 9) |
| [LSStateSpace](PartialInformation/LSStateSpace.lean) | 20 | The controlled linear state-space system (Miao §9.1) (from Chapter 9) |
| [LSRiccatiConvergence](PartialInformation/LSRiccatiConvergence.lean) | 27 | Convergence of the Riccati iteration (the undiscounted core of Propositions 9.3.1–9.3.2) (from Chapter 9) |
| [LSInfiniteHorizon](PartialInformation/LSInfiniteHorizon.lean) | 28 | Infinite-horizon limits: Propositions 9.3.1 and 9.3.2 (from Chapter 9) |
| [LSInfiniteLimits](PartialInformation/LSInfiniteLimits.lean) | 11 | Limits, the side condition and the numerical methods of §9.3 (from Chapter 9) |
| [KFMoments](PartialInformation/KFMoments.lean) | 26 | Second moments of square-integrable random vectors |
| [KFAlgebra](PartialInformation/KFAlgebra.lean) | 12 | The Kalman filter: the covariance algebra of one updating step |
| [KFFilter](PartialInformation/KFFilter.lean) | 27 | The Kalman filter |
| [KFSteady](PartialInformation/KFSteady.lean) | 6 | The stationary Kalman filter |
| [KFExamples](PartialInformation/KFExamples.lean) | 16 | Examples 10.1.1–10.1.4 |
| [KFLQ](PartialInformation/KFLQ.lean) | 6 | Linear-quadratic control under partial information |
| [KFExercises](PartialInformation/KFExercises.lean) | 12 | Exercises 10.1–10.5 |
| [HMFilter](PartialInformation/HMFilter.lean) | 19 | Filtering a hidden finite-state Markov chain |
| [HMChain](PartialInformation/HMChain.lean) | 17 | Hidden Markov chain |
| [HMSwitching](PartialInformation/HMSwitching.lean) | 7 | Hidden Markov-switching model (the Hamilton filter) |
| [HMControl](PartialInformation/HMControl.lean) | 25 | Control under partial information: the belief state |
| [HMKalman](PartialInformation/HMKalman.lean) | 13 | The scalar Kalman filter of Exercise 10.6(a) and the recursion (10.16) |
| [HMGuvenen](PartialInformation/HMGuvenen.lean) | 20 | Life-cycle saving with learning: Example 10.2.1 and Exercise 10.6(b)–(d) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
