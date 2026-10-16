# SLP Chapter 12: Weak Convergence of Markov Processes, in Lean

This is the `RecursiveMethods/WeakConvergence` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 12 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 12 studies weak convergence of probability measures and of the distributions of Markov
processes. It covers characterisations of weak convergence, distribution functions on `ℝˡ`,
Helly's theorem, invariant measures of Feller and monotone processes, and continuity of the
invariant measure in a parameter.

Every numbered result and every exercise is formalised. Helly's theorem (Theorem 12.9) and its
first corollary are false as printed, and so is Exercise 12.6a for `l ≥ 2`. Each is proved in
corrected form, with Lean counterexamples to the printed versions. The book's countable-additivity
argument for Theorem 12.7b is invalid for `l ≥ 2` and is replaced by a full construction of
multivariate Stieltjes measures. See [corrections](docs/corrections.md). The library contains
**202 theorems**.

* **Characterisations of weak convergence** (§12.1).
  * Exercises 12.1–12.2, Lemmas 12.1–12.2.
  * Theorem 12.3, the portmanteau theorem: weak convergence, `limsup` on closed sets, `liminf` on
    open sets, and convergence on sets with null boundary.
  * Theorems 12.4–12.5 and the corollary: convergence-determining classes, finite intersections of
    balls.
  * Theorem 12.6 and corollaries: measures agreeing on closed sets, or on integrals of continuous
    functions, are equal.
* **Distribution functions** (§12.2).
  * Theorem 12.7a: (D1)–(D3), through the product expansion of the indicator of a box.
  * Theorem 12.7b, existence and uniqueness. Vertex sums are additive under cuts, hence additive
    on box partitions (Mathlib's `BoxIntegral`). The boxes form a semiring, the content is
    countably subadditive by a compactness argument, and Carathéodory gives the measure.
  * Theorem 12.7c and Exercise 12.3.
* **Weak convergence of distribution functions** (§12.3).
  * Theorem 12.8 and Exercises 12.4–12.5.
  * The support of a measure, which exists on second-countable spaces.
  * Helly's theorem, corrected, through Prokhorov's theorem; Corollary 1, Exercise 12.6 and
    Corollary 2.
* **Monotone Markov processes** (§12.4).
  * Exercise 12.7: three equivalent forms of the Feller property.
  * Exercise 12.8: the cycle `s ↦ 1 − s`.
  * Theorem 12.10: a Feller process on a compact space has an invariant measure.
  * Dominance (Exercises 12.9–12.11), and the convergence of monotone sequences of measures.
  * Exercises 12.12–12.14, Assumption 12.1 and Lemma 12.11.
  * Theorem 12.12: uniqueness and global stability for monotone Feller processes with mixing.
  * Exercise 12.13: an explicit band example in which two ergodic sets coexist.
* **Parameters and a loose end** (§§12.5–12.6).
  * Theorem 12.13: the invariant measure is weakly continuous in the parameter.
  * Lemma 12.14: `T` preserves continuity, monotonicity and concavity, with a simpler proof of the
    key limit.

All names are in the namespace `StokeyLucasPrescott.WeakConvergence`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [TransitionFunctions](WeakConvergence/TransitionFunctions.lean) | 19 | Markov operators and `T*` (Chapter 8) |
| [WeakBasics](WeakConvergence/WeakBasics.lean) | 10 | Exercises 12.1–12.2, weak convergence, Lemmas 12.1–12.2 |
| [Portmanteau](WeakConvergence/Portmanteau.lean) | 9 | Theorem 12.3 |
| [Determining](WeakConvergence/Determining.lean) | 10 | Theorems 12.4–12.6 and corollaries |
| [DistributionFunctions](WeakConvergence/DistributionFunctions.lean) | 14 | Theorem 12.7a, uniqueness in 12.7b, Theorem 12.7c, Exercise 12.3 |
| [DistributionConvergence](WeakConvergence/DistributionConvergence.lean) | 14 | Theorem 12.8, Exercises 12.4–12.5 |
| [MultivariateStieltjes](WeakConvergence/MultivariateStieltjes.lean) | 26 | Existence in Theorem 12.7b |
| [Helly](WeakConvergence/Helly.lean) | 16 | Support, tightness, Theorem 12.9 and corollaries, Exercise 12.6 |
| [FellerInvariant](WeakConvergence/FellerInvariant.lean) | 17 | Exercises 12.7–12.8, Theorem 12.10 |
| [MonotoneProcesses](WeakConvergence/MonotoneProcesses.lean) | 26 | Dominance, Exercises 12.9–12.12 and 12.14, Lemma 12.11, Theorem 12.12 |
| [BandExample](WeakConvergence/BandExample.lean) | 32 | Exercise 12.13 |
| [Parameters](WeakConvergence/Parameters.lean) | 9 | Theorem 12.13, Lemma 12.14 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
