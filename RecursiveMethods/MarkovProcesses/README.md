# SLP Chapter 8: Markov Processes, in Lean

This is the `RecursiveMethods/MarkovProcesses` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 8 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 8 develops the transition functions and Markov processes used for stochastic dynamic
programming. The book's transition functions and stochastic kernels are stated as given and
identified with Mathlib's Markov kernels. Every numbered result (Theorems 8.1–8.9 and their
corollaries) and every exercise (8.1–8.11) is formalised. The corrections are recorded in
[corrections](docs/corrections.md). The library contains **71 theorems**.

* **Transition functions** (§8.1).
  * The Markov operator `T` and its adjoint `T*`: Theorems 8.1–8.3 by the book's proofs (indicators, simple functions, increasing limits), with Exercises 8.1–8.3.
  * The `n`-step transitions (Exercise 8.4), and the Feller and monotonicity properties.
* **Spaces of sequences** (§8.2).
  * The measures `μᵗ(z₀, ·)` on finite histories (Exercise 8.5).
  * The measure `μ^∞(z₀, ·)` on infinite paths, Mathlib's Ionescu-Tulcea measure. Its finite-dimensional distributions are proved to be the `μᵗ` (`pathMeasure_marginal`), and they determine it.
  * Stochastic processes, and the canonical process.
  * The Markov property with stationary transitions, stated as a factorization of the joint law (Exercise 8.6a–b). The book's conditional probabilities given null events are replaced by this.
  * Stationarity under i.i.d. shocks (Exercise 8.6c), and coin tossing (Exercise 8.7).
* **Iterated integrals** (§8.3).
  * Stochastic kernels, Theorems 8.4–8.8, and the product measure, Tonelli and Fubini theorems (Exercise 8.9).
  * A history splits at its first or at its last date, `Q × μᵗ⁻¹ = μᵗ = μᵗ⁻¹ × Q` (Exercise 8.8). Chapter 9 uses both splittings.
* **Stochastic difference equations** (§8.4).
  * Theorem 8.9, and the Feller property for continuous laws of motion on separable spaces (Exercise 8.10).
  * Second-order processes as first-order processes (Exercise 8.11).

All names are in the namespace `StokeyLucasPrescott.MarkovProcesses`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [TransitionFunctions](MarkovProcesses/TransitionFunctions.lean) | 19 | §8.1: Theorems 8.1–8.3, Exercises 8.1–8.4 |
| [StochasticKernels](MarkovProcesses/StochasticKernels.lean) | 11 | §8.3: Theorems 8.4–8.7, Exercise 8.9 |
| [Histories](MarkovProcesses/Histories.lean) | 18 | `μᵗ`, Theorem 8.8, Exercises 8.5 and 8.8 |
| [MarkovChains](MarkovProcesses/MarkovChains.lean) | 18 | `μ^∞`, stochastic and Markov processes, Exercises 8.6–8.7 |
| [DifferenceEquations](MarkovProcesses/DifferenceEquations.lean) | 5 | §8.4: Theorem 8.9, Exercises 8.10–8.11 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
