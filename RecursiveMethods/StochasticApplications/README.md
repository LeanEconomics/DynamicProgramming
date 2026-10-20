# SLP Chapter 10: Applications of Stochastic Dynamic Programming, in Lean

This is the `RecursiveMethods/StochasticApplications` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 10 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 10 applies the stochastic dynamic programming of Chapter 9 to ten economic models. The
exercises with a mathematical claim are formalised, with these exceptions:

* 10.2c.

The claims that rest on first-order conditions (10.4d–f, 10.5d, and the strict parts of 10.5e
and 10.5g) are proved with differentiability hypotheses; the slope claim of 10.4d, the strict
claim of 10.4e and the claim on `N` in 10.5g are false (Lean counterexamples) and corrected.

Exercises that ask only for a formulation or an interpretation are also not formalised: 10.4a,
the sequence form in 10.5b, 10.6f–g, 10.7i, 10.8d, 10.9, 10.10i and 10.11.

Twelve claims or arguments are corrected, nine of them with Lean counterexamples; see
[corrections](docs/corrections.md). The library contains **609 theorems**, of which 370 are in the
Chapter 10 modules. The others are the Chapter 9 machinery that Chapter 10 uses, carried from
`RecursiveMethods/StochasticDP`.

* **Optimal growth** (§§10.1–10.3).
  * The one-sector model under any Feller transition (10.1a–c, f). `v` is strictly concave even
    when `f` is only weakly concave, although Assumption 9.10 then fails.
  * With i.i.d. shocks the policy depends on output only (10.1d), and Benveniste–Scheinkman
    gives the derivatives (10.1e).
  * **The policy need not be strictly increasing.** A Lean counterexample saves nothing at low
    output.
  * Two capital goods (10.2), reduced to the one-sector model (10.2d). **With weakly concave `f`,
    `v` is not strictly concave and the policy is not unique** (Lean counterexample).
  * Many goods (10.3). **The book's strict conclusions fail** (Lean counterexample).
* **Industry investment** (§10.4).
  * Returns are unbounded below, and the book's restricted constraint set violates
    Assumptions 9.9 and 9.11 (all three shown in Lean). A truncation argument (`UpperBounded`)
    recovers existence, uniqueness and the solution of the unrestricted problem (2).
  * `v` is strictly increasing in both arguments and strictly concave. The policy is a
    continuous function, interior to `Γ`, nondecreasing in capacity (by a Topkis argument), and
    independent of the shock when shocks are i.i.d. `v_x = U_x − c(a) + a c′(a)` with `a = g/x`.
  * `g` strictly increasing in `x` with `g/x` strictly decreasing, and nondecreasing in `z`; its
    slope can exceed one. Every optimal capacity path converges, with i.i.d. shocks to the same
    limit from every `x₀`, positive under a condition on `U_x` near `0`.
* **Production and inventories** (§10.5).
  * Convex costs re-expressed as concave output (10.5a).
  * The unique bounded continuous solution of (2), shown not to depend on the current shock.
    It is strictly increasing and strictly concave, with unique continuous policies `(Y, N)`
    and `v′(x) = U′(x − Y(x))` (10.5c).
  * Storage weakly rises and production weakly falls with the stock (10.5e, again by Topkis),
    and the sign argument of 10.5f. Consumption is strictly increasing (10.5d), storage strictly
    rises unless zero, and production falls strictly when storage is positive (10.5e, 10.5g).
* **Asset prices** (§10.6). The consumer's problem, the envelope condition and the Euler
  equation (the latter differentiated under the integral sign), the equilibrium pricing
  condition, and its unique positive solution `p* = Σ βⁿMⁿh / U′`.
* **Search** (§§10.7–10.8).
  * The reservation wage `w*`, with its equations (3)–(6), its uniqueness, and its comparative
    statics in `θ` and `β`.
  * The law of motion of the wage distribution, and its limits (2)–(6).
* **Job matching** (§10.10).
  * Beta posteriors computed through the Beta integral, with the properties (d)–(e) of `π`.
  * The unique value function and its monotonicity in `(n, k)`.
  * The limit `max{p/(1 − β), v(0, 0)}` along `k_n/n → p`, and the threshold policy
    `k ≥ jₙ` with `jₙ` nondecreasing.

All names are in the namespace `StokeyLucasPrescott.StochasticApplications`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Correspondences](StochasticApplications/Correspondences.lean) | 2 | Hemicontinuity (Chapter 3) |
| [Contraction](StochasticApplications/Contraction.lean) | 8 | Contraction Mapping Theorem (Chapter 3) |
| [Maximum](StochasticApplications/Maximum.lean) | 14 | Theorem of the Maximum, Theorem 3.8 (Chapter 3) |
| [Envelope](StochasticApplications/Envelope.lean) | 2 | Benveniste–Scheinkman, Theorem 4.10 (Chapter 4) |
| [Selection](StochasticApplications/Selection.lean) | 8 | Measurable Selection Theorem 7.6 (Chapter 7) |
| [TransitionFunctions](StochasticApplications/TransitionFunctions.lean) | 19 | Markov operators, the Feller property (Chapter 8) |
| [StochasticKernels](StochasticApplications/StochasticKernels.lean) | 11 | Stochastic kernels (Chapter 8) |
| [Histories](StochasticApplications/Histories.lean) | 18 | The history measures `μᵗ` (Chapter 8) |
| [Plans](StochasticApplications/Plans.lean) | 17 | Plans and `v*` (Chapter 9) |
| [Theorem92](StochasticApplications/Theorem92.lean) | 13 | Theorem 9.2 |
| [Lemma93](StochasticApplications/Lemma93.lean) | 33 | Lemma 9.3 |
| [Theorem94](StochasticApplications/Theorem94.lean) | 10 | Theorem 9.4 (corrected) |
| [Lemma95](StochasticApplications/Lemma95.lean) | 11 | Lemma 9.5 |
| [BoundedReturns](StochasticApplications/BoundedReturns.lean) | 18 | Theorem 9.6 |
| [BoundedOptimal](StochasticApplications/BoundedOptimal.lean) | 9 | The fixed point is `v*` |
| [BoundedMonotone](StochasticApplications/BoundedMonotone.lean) | 8 | Theorems 9.7, 9.11 |
| [InteriorPoints](StochasticApplications/InteriorPoints.lean) | 3 | Interior points (Chapter 3) |
| [BoundedConcave](StochasticApplications/BoundedConcave.lean) | 10 | Theorem 9.8 |
| [BoundedPolicy](StochasticApplications/BoundedPolicy.lean) | 11 | Theorems 9.9–9.10 |
| [HistMarginals](StochasticApplications/HistMarginals.lean) | 5 | Marginals of the history measures |
| [PolicyKernels](StochasticApplications/PolicyKernels.lean) | 9 | Theorems 9.13–9.14 |
| [OneSectorGrowth](StochasticApplications/OneSectorGrowth.lean) | 27 | Exercise 10.1a–c |
| [GrowthPolicy](StochasticApplications/GrowthPolicy.lean) | 22 | Exercise 10.1d–f (corrected) |
| [TwoCapital](StochasticApplications/TwoCapital.lean) | 25 | Exercise 10.2a–b (corrected) |
| [TwoCapitalReduction](StochasticApplications/TwoCapitalReduction.lean) | 10 | Exercise 10.2d |
| [ManyGoods](StochasticApplications/ManyGoods.lean) | 15 | Exercise 10.3 (corrected) |
| [BetaPosterior](StochasticApplications/BetaPosterior.lean) | 13 | Exercise 10.10a–e |
| [AssetPricing](StochasticApplications/AssetPricing.lean) | 13 | Exercise 10.6e |
| [AssetConsumer](StochasticApplications/AssetConsumer.lean) | 26 | Exercise 10.6a–d |
| [SearchModel](StochasticApplications/SearchModel.lean) | 14 | Exercise 10.7a–c |
| [SearchReservation](StochasticApplications/SearchReservation.lean) | 19 | Exercise 10.7d–h |
| [SearchDynamics](StochasticApplications/SearchDynamics.lean) | 12 | Exercise 10.8a–c |
| [JobMatching](StochasticApplications/JobMatching.lean) | 14 | Exercise 10.10f–h |
| [UpperBounded](StochasticApplications/UpperBounded.lean) | 6 | Returns bounded above: the truncation argument |
| [IndustryInvestment](StochasticApplications/IndustryInvestment.lean) | 19 | §10.4: the model, Assumptions 9.7, 9.9, 9.11 fail |
| [IndustryInvestmentResults](StochasticApplications/IndustryInvestmentResults.lean) | 23 | Exercise 10.4b–d, f |
| [IndustryInvestmentFOC](StochasticApplications/IndustryInvestmentFOC.lean) | 39 | Exercises 10.4d–f by first-order conditions; two counterexamples |
| [Inventory](StochasticApplications/Inventory.lean) | 15 | §10.5: the model, Exercises 10.5a, 10.5f |
| [InventoryResults](StochasticApplications/InventoryResults.lean) | 16 | Exercise 10.5b–c |
| [InventoryPolicy](StochasticApplications/InventoryPolicy.lean) | 6 | Exercise 10.5e |
| [InventoryFOC](StochasticApplications/InventoryFOC.lean) | 24 | Exercises 10.5c–e, g by first-order conditions |
| [InventoryCounterexample](StochasticApplications/InventoryCounterexample.lean) | 12 | Counterexamples to Exercise 10.5g |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
