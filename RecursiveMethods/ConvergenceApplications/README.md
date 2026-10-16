# SLP Chapter 13: Applications of Convergence Results for Markov Processes, in Lean

This is the `RecursiveMethods/ConvergenceApplications` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 13 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 13 applies the convergence theorems of Chapters 11 and 12 to eight economic models. It has
no numbered lemmas or theorems: its content is Exercises 13.1–13.8 (37 lettered parts). Every part
is formalised, and each one is proved or refuted. Where the book is wrong there is a Lean
counterexample, together with a corrected statement that is proved. One corrected claim, that the
labour demand of §13.8 is strictly decreasing where it is positive, is left open; the book's own
claim is refuted. See [corrections](docs/corrections.md).

The library contains **1145 theorems**. Of these, 664 are in the Chapter 13 modules and the rest in
the machinery carried from Chapters 8–12.

* **§13.1 Discrete (s, S) inventories.** The functional equations solved in closed form, the
  optimal order size characterised (and shown not to exist when `c₁ = 0`), and the manual's
  stopping rule refuted. The chain's ergodic set, transient states and aperiodicity are proved.
  Condition M holds on `{0, …, S}` and the invariant distribution is computed; the manual's is not
  a distribution. Convergence holds from every initial distribution on `ℕ`, but not uniformly.
* **§13.2 Continuous (s, S) process.** The transition function, which is not Feller. Exercise
  13.2b is false without a condition on demand (a period-2 counterexample). With `μ([S, ∞)) > 0`
  Theorem 11.12 applies on `[0, S]`.
* **§13.3 Stochastic growth in output.** Existence of `x̄` fails under the stated assumptions.
  Exercises 13.3a–c are proved, and 13.3b's `0 < g(x)` is refuted by a model meeting every
  assumption. Exercises 13.3d–e and Assumption 12.1 are proved, giving a unique invariant
  distribution with global weak convergence.
* **§13.4 Industry investment.** The fixed points `x̲`, `x̄` need an extra hypothesis. Exercises
  13.4a–c are proved, including global convergence on `(0, ∞) × Z`.
* **§13.5 A pure currency economy.** The household problem: `v` strictly concave and `C¹`, the
  policy continuous and monotone. Exercises 13.5d and 13.5e are false (corner solutions with no
  spending or with spending everything), and the manual's step in (f) fails. Corrected statements
  are proved. Theorem 12.12 applies to the optimal policy, and the stationary price level is
  unique.
* **§13.6 Linear utility, currency.** Explicit value function, ergodic set `{iy}` (under a
  condition the book omits), geometric invariant distribution and price level.
* **§13.7 Linear utility, credit.** Explicit solution. Exercise 13.7b is false: `T*ⁿΨ₀ ⇒ δ₀`,
  which is invariant; what fails is market clearing in the limit. The manual's "not Feller" is
  wrong. The equilibrium price is proportional to `y`.
* **§13.8 Search equilibrium.** (F1) and (F2) are inconsistent. Exercises 13.8a–g are proved,
  including uniqueness of the invariant measure under (6) for every `θ > 0` and continuity of
  demand by Theorem 12.13. The hint to (d) and the claim that demand is strictly decreasing are
  refuted.

All names are in the namespace `StokeyLucasPrescott.ConvergenceApplications`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [DiscreteInventory](ConvergenceApplications/DiscreteInventory.lean) | 83 | §13.1, Exercise 13.1 |
| [ContinuousInventory](ConvergenceApplications/ContinuousInventory.lean) | 40 | §13.2, Exercise 13.2 |
| [GrowthOutput](ConvergenceApplications/GrowthOutput.lean) | 54 | §13.3, `x̄`; Exercises 13.3a–c |
| [GrowthConvergence](ConvergenceApplications/GrowthConvergence.lean) | 55 | Exercises 13.3d–e; the convergence argument; `f(0) = 0` |
| [IndustryConvergence](ConvergenceApplications/IndustryConvergence.lean) | 76 | §13.4, Exercise 13.4 |
| [CurrencyMarkov](ConvergenceApplications/CurrencyMarkov.lean) | 20 | Exercises 13.5i–j for an abstract policy |
| [CurrencyEconomy](ConvergenceApplications/CurrencyEconomy.lean) | 31 | Exercises 13.5a–c, f, h |
| [CurrencyStationary](ConvergenceApplications/CurrencyStationary.lean) | 8 | Exercises 13.5i–j for the optimal policy |
| [CurrencyEnvelope](ConvergenceApplications/CurrencyEnvelope.lean) | 25 | Exercise 13.5b: differentiability |
| [CurrencyPolicy](ConvergenceApplications/CurrencyPolicy.lean) | 15 | Exercises 13.5d, e, g |
| [CurrencyCounterexample](ConvergenceApplications/CurrencyCounterexample.lean) | 15 | `U = z(1 − e^{−c})`: Exercises 13.5d–e false |
| [LinearCurrency](ConvergenceApplications/LinearCurrency.lean) | 40 | §13.6, Exercise 13.6 |
| [CreditEconomy](ConvergenceApplications/CreditEconomy.lean) | 27 | §13.7, Exercise 13.7 |
| [SearchValue](ConvergenceApplications/SearchValue.lean) | 66 | §13.8, Exercises 13.8a–c |
| [SearchInvariant](ConvergenceApplications/SearchInvariant.lean) | 56 | Exercises 13.8d, f |
| [SearchLeavers](ConvergenceApplications/SearchLeavers.lean) | 12 | Exercise 13.8e |
| [SearchDemand](ConvergenceApplications/SearchDemand.lean) | 28 | Exercises 13.8g–h |
| [RealIntervals](ConvergenceApplications/RealIntervals.lean) | 13 | Theorem 12.12 on real intervals and rectangles |

Carried machinery (481 theorems):

* `TransitionFunctions`, `WeakBasics`, `Portmanteau`, `Determining`, `DistributionFunctions`,
  `DistributionConvergence`, `Helly`, `FellerInvariant`, `MonotoneProcesses`, `Parameters`:
  Chapters 8 and 12, from `WeakConvergence`.
* `ConvergenceConcepts`, `TotalVariation`, `TVConvergence`, `Doeblin`, `ConditionM`: Chapter 11,
  from `StrongConvergence`.
* `Contraction`, `Correspondences`, `Maximum`, `Selection`, `InteriorPoints`, `Envelope`,
  `StochasticKernels`, `Histories`, `Plans`, `Theorem92`, `Lemma93`, `Theorem94`, `Lemma95`,
  `HistMarginals`, `BoundedReturns`, `BoundedOptimal`, `BoundedMonotone`, `BoundedConcave`,
  `BoundedPolicy`, `PolicyKernels`, `OneSectorGrowth`, `GrowthPolicy`: Chapters 3, 4, 9 and 10,
  from `StochasticApplications`.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
