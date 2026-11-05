# Miao Chapter 2: Stochastic Difference Equations, in Lean

This is the `EconomicDynamics/RationalExpectations` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 2 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 2 adds shocks and conditional expectations to Chapter 1: moments of a VAR, scalar
rational expectations models and bubbles, and the three solution methods for linear rational
expectations systems — Blanchard–Kahn, Klein and Sims — followed by the perturbation method for
nonlinear models. Every numbered result (Definitions 2.1.1 and 2.3.1–2.3.4, Lemma 2.3.1,
Assumptions 2.3.1–2.3.2, Theorem 2.3.1, Corollary 2.3.1), every derivation in the text and
Exercises 1–2 are proved; Exercise 3 and §2.5 are about the Dynare software. The corrections are
recorded in [corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **726 theorems**; 220 of them are the
Chapter 1 library, carried over.

* **Conditional expectations.** The linear theory needs only that `E_t` is linear, does not raise
  the `L¹` norm, and satisfies the law of iterated expectations (`CondExpSystem`). Mathlib's
  conditional expectations on `L¹(Ω, F, Pr)` given a filtration are an instance, over `ℝ` and
  `ℂ` (`condExpSystemL1_real`, `condExpSystemL1_complex`), and Definition 2.3.1's stability is
  then exactly `max_j E|x_j| < M` (`l1_isStableProc_iff`).
* **VAR moments** (§2.1): the unique solution of the Lyapunov equation and the autocovariances
  (`lyap_unique`, `var_autocov`); the claim of a unique stationary distribution is false
  (`stationary_law_not_unique`), and a white noise need not be a martingale difference
  (`whiteNoise_not_mds`).
* **Scalar models** (§2.2): the fundamental solution, bubbles and transversality (`eq_2_3_unique`,
  `eq_2_5_rules_out_bubbles`); the Blanchard–Watson bubble (`example_2_2_1_bubble`); the
  second-order equations, where (2.10) needs `a₀ ≠ λ₁` (`eq_2_10_indeterminate`); undetermined
  coefficients agree with lag operators (`uc_eq_lag_solution`).
* **Blanchard–Kahn** (§2.3.1): the stochastic Theorem 1.4.2 and Corollary 1.4.1
  (`theorem_1_4_2_stoch`, `corollary_1_4_1_stoch`) and certainty equivalence
  (`certainty_equivalence`); the New Keynesian model with an exogenous rate rule is indeterminate
  (`example_2_3_1_indeterminate`), and the Taylor principle `δ > 1` holds only for `δ ≥ 0`
  (`ex_2_2_a_taylor_principle`, `ex_2_2_a_printed_false`).
* **Klein** (§2.3.2): the stochastic theorem with prediction errors, real for real data
  (`klein_stochastic`, `klein_stochastic_real`), the simplified policy form
  (`klein_simplified_form`), and the LQ first-order system (`lq_system_iff`); (2.17) repeats the
  misprint of (1.37) (`eq_2_17_printed_false`).
* **Sims** (§2.3.3): Lemma 2.3.1 and Theorem 2.3.1, sufficiency in general and necessity for a
  rich filtration (`theorem_2_3_1`, `theorem_2_3_1_necessity_false`); Corollary 2.3.1 holds for
  the pair `(y, η)` but not for `y` (`corollary_2_3_1`, `corollary_2_3_1_printed_false`);
  sunspot solutions (`sunspot_solution`); the thin SVD built from the spectral theorem
  (`exists_thinSVD`). The printed (2.22) and `Θ₁` are corrected (`eq_2_22`, `theta_1_printed_false`).
* **Perturbation** (§2.4, the book's scalar case): the first- and second-order conditions of
  Schmitt-Grohé and Uribe (`eq_F_sigma`, `eq_2_31`, `eq_F_xx`, `eq_F_sigma_sigma`,
  `eq_F_sigma_x`), when `g_σ = h_σ = 0` is forced (`theorem_g_sigma_zero`, `g_sigma_not_forced`),
  and the summary claim (`summary_uncertainty`); misprints in `F_xx` and `F_σσ`
  (`eq_F_xx_printed_false`, `eq_F_sigma_sigma_printed_false`).

All names are in the namespace `Miao.RationalExpectations`. The modules `DeterministicBasics`,
`Triangular`, `Spectral`, `RealSplitting`, `Dichotomy`, `LinearSystems`, `BlockSplit`,
`Nonsingular`, `QZ` and `Singular` are copied from
[EconomicDynamics/DifferenceEquations](../DifferenceEquations/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| DeterministicBasics … Singular | 220 | The Chapter 1 library (copied) |
| [Basics](RationalExpectations/Basics.lean) | 8 | `CondExpSystem`, adapted and stable processes, the system (2.11) |
| [CondExpL1](RationalExpectations/CondExpL1.lean) | 13 | The `L¹` conditional expectations as a `CondExpSystem` |
| [VARMoments](RationalExpectations/VARMoments.lean) | 43 | §2.1: means, the Lyapunov equation, autocovariances, impulse responses; white noise |
| [VARExamples](RationalExpectations/VARExamples.lean) | 21 | Counterexamples on infinite products: stationary laws, white noise |
| [ScalarRE](RationalExpectations/ScalarRE.lean) | 59 | §2.2: lag operators, (2.3)–(2.10), Example 2.2.1, undetermined coefficients |
| [Exercise1](RationalExpectations/Exercise1.lean) | 11 | Exercise 1: the stochastic Cagan model |
| [BKStable](RationalExpectations/BKStable.lean) | 43 | §2.3: stable processes, (2.12), the jump-only system |
| [StochasticBK](RationalExpectations/StochasticBK.lean) | 35 | §2.3.1: Blanchard–Kahn, Corollary 1.4.1, Theorem 1.4.3, certainty equivalence |
| [NewKeynesian](RationalExpectations/NewKeynesian.lean) | 34 | Example 2.3.1 and Exercise 2 |
| [KleinMartingales](RationalExpectations/KleinMartingales.lean) | 6 | Definitions 2.3.2 and 2.3.4 |
| [StochasticKlein](RationalExpectations/StochasticKlein.lean) | 67 | §2.3.2: the stochastic Klein theorem |
| [KleinSimplified](RationalExpectations/KleinSimplified.lean) | 8 | The simplified Klein form |
| [LQKlein](RationalExpectations/LQKlein.lean) | 12 | The LQ example |
| [Sims](RationalExpectations/Sims.lean) | 57 | §2.3.3: Lemma 2.3.1, Assumptions 2.3.1–2.3.2, Theorem 2.3.1 |
| [SimsSVD](RationalExpectations/SimsSVD.lean) | 22 | The SVD conditions, Corollary 2.3.1, sunspots |
| [SimsExample](RationalExpectations/SimsExample.lean) | 6 | (2.19) and Example 2.3.2 |
| [ThinSVD](RationalExpectations/ThinSVD.lean) | 8 | Existence of the thin SVD |
| [Perturbation](RationalExpectations/Perturbation.lean) | 24 | §2.4: the model, `F`, its derivatives |
| [PerturbationSystem](RationalExpectations/PerturbationSystem.lean) | 22 | The first- and second-order systems |
| [PerturbationExamples](RationalExpectations/PerturbationExamples.lean) | 7 | Counterexamples to the printed displays |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
