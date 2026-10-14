# SLP Chapter 6: Deterministic Dynamics, in Lean

This is the `RecursiveMethods/DeterministicDynamics` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 6 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 6 studies the dynamics of optimal policies: global stability through Liapounov functions,
and local stability through linear approximation. Every numbered result (Proposition 6.1,
Theorems 6.1 and 6.3–6.9, Lemmas 6.2 and 6.7) is proved, including Theorems 6.1, 6.5 and 6.6,
which the book cites without proof. So is every exercise (6.1–6.10), except the open-ended parts
6.10e–f. The corrections are recorded in [corrections](docs/corrections.md). The library contains
**598 theorems**; 230 of them are the Chapter 3–5 library, carried over.

* **The one-sector growth model** (§6.1).
  * Interior maxima, the Euler equation and `v′(k) = U′(f(k) − g(k))f′(k)` (`ex_6_1a`); `g`
    strictly increasing (`ex_6_1b`); and monotone convergence to `k*` from every `k₀ > 0`
    (`prop_6_1`).
  * The Cobb–Douglas problem of Exercise 6.2, for every concave solution of the functional
    equation (`ex_6_2`, `ex_6_2_fixed`).
* **Global stability** (§6.2).
  * Boldrin and Montrucchio: every `C²` map of a compact interval is the optimal policy of some
    problem (`theorem_6_1`).
  * The logistic map, with its two-cycle and a three-cycle at `sin²(π/7)` (`ex_6_3b_three_cycle`).
  * Lemma 6.2 without its hypothesis (a) (`lemma_6_2`), and the value loss as a Liapounov
    function.
  * Exercise 6.4: the book's sufficient condition is wrong, and the correct one is
    `βbd ≥ (1 + β)²c²/4` (`ex_6_4`, `ex_6_4_book_condition_fails`).
* **Linear systems and local stability** (§6.3).
  * Stable subspaces as sums of generalized eigenspaces, in place of the Jordan form
    (`tendsto_iff_mem_stable`), and Theorems 6.3–6.5.
  * The stable manifold theorem (Theorem 6.6), proved in full: real splitting, an exponential
    dichotomy and a Lyapunov–Perron contraction in weighted sequence spaces (`theorem_6_6`). Only
    strict differentiability at `x̄` is needed, and `A` may be singular.
* **Euler equations** (§6.4).
  * The linearized Euler system: `A` nonsingular (`ex_6_5`), roots in pairs `λ, (βλ)⁻¹`
    (`lemma_6_7`), and the scalar case (`ex_6_6`).
  * The linear-quadratic problem: a unique optimal plan that converges (`theorem_6_8`), with the
    stable-subspace dimension count and a telescoping argument for the nonsingularity of `B₂₁`.
  * The nonlinear problem (`theorem_6_9`): the Euler map by the inverse function theorem, a point
    on the stable manifold with any prescribed `x₀`, and sufficiency and uniqueness by strict
    concavity. The book's rank argument has a gap; it is closed with a negative-definite
    second-order form.
* **Applications** (Exercises 6.7–6.10).
  * Cobb–Douglas dynamics: `k*` unstable for the book's parameters (`ex_6_7d`); optimal two-cycles
    (`ex_6_7e`). The book's cycle `(0.29, 0.18)` is not a cycle (`ex_6_7f_book_box`); the true
    cycle is near `(0.484, 0.088)` (`ex_6_7f`) and is saddle-path stable (`ex_6_7g`).
  * The firm with adjustment costs: a unique steady state and monotone convergence (`ex_6_8`), and
    saddle roots (`ex_6_8c`).
  * A constant-returns industry: `v` unbounded on `ℝ₊` (`crs_unbounded`); on `[0, K]` a strictly
    concave `v` and a nondecreasing `g` (`ex_6_9a`, `argmax_mono`). There is at most one
    stationary point, and possibly none (`ex_6_9c_counterexample`).
  * A consumer with recursive preferences: stationary wealth (`ex_6_10a_if`, `ex_6_10a_only_if`),
    the additive case (`ex_6_10c_eq`, `ex_6_10c_ne`) and the Euler equation (`ex_6_10d`).

All names are in the namespace `StokeyLucasPrescott.DeterministicDynamics`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

The modules `ExtendedReals`, `Principle`, `Assumption42`, `Contraction`, `Correspondences`,
`Maximum`, `BoundedReturns`, `Concavity`, `Envelope`, `InteriorPoints`,
`ValueDifferentiability`, `EulerEquations`, `OneSectorGrowth`, `WeakConcavity`,
`GrowthDifferentiability`, `GrowthDiscount`, `ConvexInvestment`, `AdjustmentCosts`,
`RecursivePreferences` and `ConsumerRecursive` are carried over from the Chapter 5 project
(`RecursiveMethods/DeterministicApplications`), so that the project is self-contained.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ExtendedReals](DeterministicDynamics/ExtendedReals.lean) | 9 | Suprema and limits in `R̄` (from Chapter 4) |
| [Principle](DeterministicDynamics/Principle.lean) | 20 | Lemma 4.1, Theorems 4.2–4.5 (from Chapter 4) |
| [Assumption42](DeterministicDynamics/Assumption42.lean) | 13 | When Assumption 4.2 holds (from Chapter 4) |
| [Contraction](DeterministicDynamics/Contraction.lean) | 8 | Theorem 3.2 and corollaries (from Chapter 3) |
| [Correspondences](DeterministicDynamics/Correspondences.lean) | 2 | Hemi-continuity (from Chapter 3) |
| [Maximum](DeterministicDynamics/Maximum.lean) | 14 | Theorem 3.6; Lemma 3.7 and Theorem 3.8 (from Chapter 3) |
| [BoundedReturns](DeterministicDynamics/BoundedReturns.lean) | 15 | Theorems 4.6–4.7 (from Chapter 4) |
| [Concavity](DeterministicDynamics/Concavity.lean) | 7 | Theorems 4.8–4.9 (from Chapter 4) |
| [Envelope](DeterministicDynamics/Envelope.lean) | 2 | Theorem 4.10 (from Chapter 4) |
| [InteriorPoints](DeterministicDynamics/InteriorPoints.lean) | 3 | Interior points of l.h.c. correspondences (from Chapter 3) |
| [ValueDifferentiability](DeterministicDynamics/ValueDifferentiability.lean) | 6 | Theorem 4.11 (from Chapter 4) |
| [EulerEquations](DeterministicDynamics/EulerEquations.lean) | 7 | Theorem 4.15 (from Chapter 4) |
| [OneSectorGrowth](DeterministicDynamics/OneSectorGrowth.lean) | 13 | Exercise 5.1a–c (from Chapter 5) |
| [WeakConcavity](DeterministicDynamics/WeakConcavity.lean) | 6 | Exercise 5.1c, weakly concave `f` (from Chapter 5) |
| [GrowthDifferentiability](DeterministicDynamics/GrowthDifferentiability.lean) | 6 | Exercise 5.1d (from Chapter 5) |
| [GrowthDiscount](DeterministicDynamics/GrowthDiscount.lean) | 6 | Exercise 5.1e (from Chapter 5) |
| [ConvexInvestment](DeterministicDynamics/ConvexInvestment.lean) | 11 | Exercise 5.9a (from Chapter 5) |
| [AdjustmentCosts](DeterministicDynamics/AdjustmentCosts.lean) | 27 | Exercise 5.9 (from Chapter 5) |
| [RecursivePreferences](DeterministicDynamics/RecursivePreferences.lean) | 26 | Exercise 5.11 (from Chapter 5) |
| [ConsumerRecursive](DeterministicDynamics/ConsumerRecursive.lean) | 29 | Exercise 5.12b–d (from Chapter 5) |
| [GrowthStability](DeterministicDynamics/GrowthStability.lean) | 31 | §6.1: Exercise 6.1 and the Proposition |
| [BoldrinMontrucchio](DeterministicDynamics/BoldrinMontrucchio.lean) | 14 | Theorem 6.1 |
| [LogisticMap](DeterministicDynamics/LogisticMap.lean) | 5 | Exercise 6.3 |
| [Liapounov](DeterministicDynamics/Liapounov.lean) | 15 | Lemma 6.2, the value loss, Exercise 6.4 |
| [LinearSystems](DeterministicDynamics/LinearSystems.lean) | 25 | Stable subspaces, Theorems 6.3–6.4 |
| [LocalStability](DeterministicDynamics/LocalStability.lean) | 4 | Theorem 6.5 |
| [EulerLinear](DeterministicDynamics/EulerLinear.lean) | 8 | The linearized Euler system, Exercise 6.5, Lemma 6.7 |
| [EulerScalar](DeterministicDynamics/EulerScalar.lean) | 3 | Exercise 6.6, the growth model's roots |
| [CobbDouglas](DeterministicDynamics/CobbDouglas.lean) | 12 | Exercise 6.7b–d |
| [CobbDouglasConcave](DeterministicDynamics/CobbDouglasConcave.lean) | 4 | Concavity of the Cobb–Douglas return |
| [TwoCycle](DeterministicDynamics/TwoCycle.lean) | 13 | Exercise 6.7e |
| [CycleNumerics](DeterministicDynamics/CycleNumerics.lean) | 15 | Exercise 6.7f–g |
| [LinearQuadratic](DeterministicDynamics/LinearQuadratic.lean) | 18 | The linear-quadratic problem: sufficiency and uniqueness |
| [LQStability](DeterministicDynamics/LQStability.lean) | 18 | Theorem 6.8 |
| [FirmDynamics](DeterministicDynamics/FirmDynamics.lean) | 14 | Exercise 6.8 |
| [CobbDouglasDP](DeterministicDynamics/CobbDouglasDP.lean) | 24 | Exercises 6.2 and 6.7a |
| [ConsumerDynamics](DeterministicDynamics/ConsumerDynamics.lean) | 13 | Exercise 6.10 |
| [RealSplitting](DeterministicDynamics/RealSplitting.lean) | 24 | Real stable and unstable subspaces |
| [Dichotomy](DeterministicDynamics/Dichotomy.lean) | 32 | The exponential dichotomy |
| [LyapunovPerron](DeterministicDynamics/LyapunovPerron.lean) | 14 | The Lyapunov–Perron fixed point |
| [StableManifold](DeterministicDynamics/StableManifold.lean) | 6 | Theorem 6.6 |
| [EulerMap](DeterministicDynamics/EulerMap.lean) | 8 | The Euler map by the inverse function theorem |
| [NonlinearEuler](DeterministicDynamics/NonlinearEuler.lean) | 3 | Convergent Euler paths from every `x₀` near `x̄` |
| [Theorem69](DeterministicDynamics/Theorem69.lean) | 3 | Theorem 6.9 |
| [CRSIndustry](DeterministicDynamics/CRSIndustry.lean) | 28 | Exercise 6.9b–e |
| [CRSIndustryDP](DeterministicDynamics/CRSIndustryDP.lean) | 14 | Exercise 6.9a, the counterexample to 6.9c |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
