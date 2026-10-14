# SLP Chapter 5: Applications of Dynamic Programming under Certainty, in Lean

This is the `RecursiveMethods/DeterministicApplications` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 5 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 5 applies the theory of Chapter 4 to seventeen problems. Every exercise (5.1–5.17) is
formalised here. Open-ended parts ("under what assumptions…?") are answered with sufficient
conditions, and the corrections are recorded in [corrections](docs/corrections.md). The library
contains **679 theorems**; 137 of them are the Chapter 3–4 library, carried over.

* **Optimal growth** (§5.1–5.4).
  * The one-sector model: Theorems 4.6–4.8 apply, `v` is strictly concave and the policy is
    continuous (`ex_5_1ab`, `ex_5_1c`). Exercise 5.1c's claim that Assumption 4.7 holds is false
    for a weakly concave `f`, but its conclusions still hold, by a separate argument
    (`ex_5_1c_weak`).
  * Differentiability and interior policies under an Inada condition (`ex_5_1d`), and saving that
    rises with `β` by a lattice argument (`ex_5_1e`).
  * Cake eating (`ex_5_2b`: `g(x) = βx` for log utility); linear utility, where the policy jumps
    to `k*` (`ex_5_3c`); and technical progress, reduced to Section 5.1 by renormalizing
    (`ex_5_4`).
* **Trees and learning** (§5.5–5.6).
  * Tree cutting: optimal stopping rules without replanting, and with Faustmann replanting
    (`ex_5_5a`, `ex_5_5b`).
  * Learning by doing: monopolist and planner, efficient output above the competitive output,
    and a nonrenewable resource (`ex_5_6a`–`ex_5_6d`).
* **Human capital** (§5.7–5.8).
  * The life-cycle worker: `Tⁿ0 = aₙk`, bounded iff `λ ≤ r`, and a single-peaked profile
    (`ex_5_7a_bounded_iff`, `ex_5_7b_profile`).
  * Growth with human capital, solved by a weighted contraction in the growth class
    `|v| ≤ C(1 + k)` (`ex_5_8a`, `ex_5_8b`).
* **Investment** (§5.9–5.10).
  * Linear costs, where the firm jumps to a target (`invest_fe`); bounds on investment; and
    convex adjustment costs, where capital adjusts gradually (`ex_5_9b_slope`), with the Euler
    equation and the short-run profit function (`ex_5_9b_euler`, `profitPi_deriv`).
  * Constant returns: `v(k) = Ak` and `g(k) = θk` (`ex_5_10c`).
* **Recursive preferences** (§5.11–5.13).
  * The space `C(L)`, its completeness, and a counterexample to continuity under truncation
    (`ex_5_11b_counterexample`).
  * Aggregators: monotonicity, concavity and marginal rates of substitution (`ex_5_11d`,
    `ex_5_11e`).
  * The consumer, with demand, envelope and Euler conditions (`ex_5_12b`, `ex_5_12c_euler`), and
    the principle of optimality for `u_W` (`ex_5_12a`).
  * The two-agent Pareto frontier (`ex_5_13a`, `ex_5_13b`).
* **Inventories and pricing** (§5.14–5.16).
  * The (s, S) inventory problem, solved in full: `Y_N`, with `N` rising in `β` and `c₀` and
    independent of `p`; the piecewise linear `w`, its kinks, `w = v`, and the policy `s = 1 + A`,
    `S = N` (`ex_5_14_value`, `ex_5_14_policy`).
  * Its continuous-time version, with a unique optimal cycle (`ex_5_15b_unique`).
  * A seller with unknown demand: `v` is homogeneous and convex, and charging the lower bound is
    optimal exactly when `A/B ≥ 1/(2 − β)` (`ex_5_16c`).
* **Consumption and savings** (§5.17): every optimal plan is written down at once. Its multiplier
  `μ` sets `c_t = max{I, (U')⁻¹(μ/(Rβ)ᵗ)}`, and a summation-by-parts argument gives optimality,
  uniqueness and the supergradient inequality (`value_bound`).
  * `v` is `C¹`, strictly increasing and strictly concave, with `v'(x) = U'(I + x − g(x)/R)`.
  * The book's interval induction becomes global objects: `m₁`, `h` and `m_n → ∞`
    (`ex_5_17b`–`ex_5_17h`).
  * Three corrections are Lean-verified: `m₁` needs a condition such as `U' → 0`; the hint to
    5.17g fails for `R < 1`; and `g(x') − g(x) < x' − x` fails for some `R > 1`
    (`ex_5_17h_counterexample`).

All names are in the namespace `StokeyLucasPrescott.DeterministicApplications`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

The modules `ExtendedReals`, `Principle`, `Assumption42`, `Contraction`, `Correspondences`,
`Maximum`, `BoundedReturns`, `Concavity`, `Envelope`, `InteriorPoints`,
`ValueDifferentiability`, `ConstantReturns`, `ConstantReturnsDP`, `UnboundedReturns` and
`EulerEquations` are carried over from the Chapter 4 project (`RecursiveMethods/DeterministicDP`),
so that the project is self-contained. `LogModel` is Chapter 4's unit-elastic growth model
extended to `α = 1`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ExtendedReals](DeterministicApplications/ExtendedReals.lean) | 9 | Suprema and limits in `R̄` (from Chapter 4) |
| [Principle](DeterministicApplications/Principle.lean) | 20 | Lemma 4.1, Theorems 4.2–4.5 (from Chapter 4) |
| [Assumption42](DeterministicApplications/Assumption42.lean) | 13 | When Assumption 4.2 holds (from Chapter 4) |
| [Contraction](DeterministicApplications/Contraction.lean) | 8 | Theorem 3.2 and corollaries (from Chapter 3) |
| [Correspondences](DeterministicApplications/Correspondences.lean) | 2 | Hemi-continuity (from Chapter 3) |
| [Maximum](DeterministicApplications/Maximum.lean) | 14 | Theorem 3.6; Lemma 3.7 and Theorem 3.8 for unique maximizers (from Chapter 3) |
| [BoundedReturns](DeterministicApplications/BoundedReturns.lean) | 15 | Theorems 4.6–4.7 (from Chapter 4) |
| [Concavity](DeterministicApplications/Concavity.lean) | 7 | Theorems 4.8–4.9 (from Chapter 4) |
| [Envelope](DeterministicApplications/Envelope.lean) | 2 | Theorem 4.10, Exercise 4.5 (from Chapter 4) |
| [InteriorPoints](DeterministicApplications/InteriorPoints.lean) | 3 | Interior points of l.h.c. correspondences (from Chapter 3) |
| [ValueDifferentiability](DeterministicApplications/ValueDifferentiability.lean) | 6 | Theorem 4.11 (from Chapter 4) |
| [ConstantReturns](DeterministicApplications/ConstantReturns.lean) | 10 | `H(X)`, Theorem 4.12 (from Chapter 4) |
| [ConstantReturnsDP](DeterministicApplications/ConstantReturnsDP.lean) | 16 | Theorem 4.13 (from Chapter 4) |
| [UnboundedReturns](DeterministicApplications/UnboundedReturns.lean) | 5 | Theorem 4.14 (from Chapter 4) |
| [EulerEquations](DeterministicApplications/EulerEquations.lean) | 7 | Theorem 4.15 (from Chapter 4) |
| [LogModel](DeterministicApplications/LogModel.lean) | 13 | The unit-elastic growth model with `0 < α ≤ 1` |
| [OneSectorGrowth](DeterministicApplications/OneSectorGrowth.lean) | 13 | §5.1: Exercise 5.1a–c |
| [WeakConcavity](DeterministicApplications/WeakConcavity.lean) | 6 | Exercise 5.1c with a weakly concave technology |
| [GrowthDifferentiability](DeterministicApplications/GrowthDifferentiability.lean) | 6 | Exercise 5.1d |
| [GrowthDiscount](DeterministicApplications/GrowthDiscount.lean) | 6 | Exercise 5.1e |
| [CakeEating](DeterministicApplications/CakeEating.lean) | 12 | §5.2: Exercise 5.2 |
| [LinearUtility](DeterministicApplications/LinearUtility.lean) | 9 | §5.3: Exercise 5.3 |
| [TechProgress](DeterministicApplications/TechProgress.lean) | 12 | §5.4: Exercise 5.4 |
| [TreeCutting](DeterministicApplications/TreeCutting.lean) | 11 | §5.5: Exercise 5.5 |
| [LearningByDoing](DeterministicApplications/LearningByDoing.lean) | 10 | §5.6: learning by doing with a general return |
| [LearningSurplus](DeterministicApplications/LearningSurplus.lean) | 19 | Exercise 5.6a–d |
| [HumanCapital](DeterministicApplications/HumanCapital.lean) | 20 | §5.7: Exercise 5.7 |
| [WeightedBellman](DeterministicApplications/WeightedBellman.lean) | 8 | The functional equation with a weighted bound |
| [HumanCapitalGrowth](DeterministicApplications/HumanCapitalGrowth.lean) | 6 | §5.8: Exercise 5.8 |
| [ConvexInvestment](DeterministicApplications/ConvexInvestment.lean) | 11 | §5.9: Exercise 5.9a |
| [AdjustmentCosts](DeterministicApplications/AdjustmentCosts.lean) | 27 | Exercise 5.9a with bounds, 5.9b–c |
| [CRSInvestment](DeterministicApplications/CRSInvestment.lean) | 10 | §5.10: Exercise 5.10 |
| [RecursivePreferences](DeterministicApplications/RecursivePreferences.lean) | 26 | §5.11: Exercise 5.11 |
| [ConsumerRecursive](DeterministicApplications/ConsumerRecursive.lean) | 29 | §5.12: Exercise 5.12b–d |
| [ConsumerPrinciple](DeterministicApplications/ConsumerPrinciple.lean) | 14 | Exercise 5.12a |
| [Pareto](DeterministicApplications/Pareto.lean) | 26 | §5.13: Exercise 5.13 |
| [Inventory](DeterministicApplications/Inventory.lean) | 26 | §5.14: Exercise 5.14a–c |
| [InventorySolution](DeterministicApplications/InventorySolution.lean) | 17 | Exercise 5.14d: the value function |
| [InventoryVerify](DeterministicApplications/InventoryVerify.lean) | 23 | Exercise 5.14d–h: verification and the (s, S) policy |
| [ContinuousInventory](DeterministicApplications/ContinuousInventory.lean) | 18 | §5.15: Exercise 5.15 |
| [UnknownDemand](DeterministicApplications/UnknownDemand.lean) | 21 | §5.16: Exercise 5.16 |
| [ConsumptionSavings](DeterministicApplications/ConsumptionSavings.lean) | 65 | §5.17: the optimal plans, Exercise 5.17a |
| [ConsumptionSavingsPolicy](DeterministicApplications/ConsumptionSavingsPolicy.lean) | 64 | Exercise 5.17b–h |
| [ConsumptionSavingsCounterexample](DeterministicApplications/ConsumptionSavingsCounterexample.lean) | 14 | Three corrections to §5.17 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
