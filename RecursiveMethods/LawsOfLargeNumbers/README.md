# SLP Chapter 14: Laws of Large Numbers, in Lean

This is the `RecursiveMethods/LawsOfLargeNumbers` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 14 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 14 moves from distributions to sample paths. It proves laws of large numbers for
uncorrelated and martingale-difference sequences, and then Breiman's strong law for Markov
processes: on a compact state space with the Feller property, if the Cesàro averages of `T*ⁿλ₀`
converge weakly to a unique `λ*`, then `(1/N) Σ f(sₙ) → ∫ f dλ*` almost surely.

Every numbered result and every exercise is formalised. That includes the two theorems the book
states without proof, Theorem 14.10 (minimum norm duality) and Theorem 14.14 (the Riesz
representation theorem). Pages 422–423 are missing from the scan used, and Theorem 14.5 is
reconstructed in the form in which the book uses it. One lemma is false as stated (Lemma 14.8);
it is proved with the missing hypothesis, and a counterexample to the printed statement is given.
See [corrections](docs/corrections.md). The library contains **143 theorems**.

* **Modes of convergence** (§14.1). Convergence a.e. and in probability; Lemmas 14.1–14.3
  (Borel–Cantelli); a.e. convergence implies convergence in probability. Exercise 14.1: the
  sliding indicators converge in probability but at no point, and a subsequence converges a.e.
  Exercise 14.2: summable deviations beyond thresholds `εₙ → 0` give a.e. convergence, and
  convergence in probability gives an a.e. convergent subsequence.
* **Uncorrelated variables** (§14.1). Chebyshev's inequality; Theorem 14.4 (the weak law);
  Theorem 14.5 (the strong law), by the method of subsequences along the squares.
* **Martingale differences** (§14.1). Theorem 14.6: the conditional-mean differences
  `fₖ − E(fₖ | 𝒜ₖ₋₁)` are uncorrelated, so Theorem 14.5 applies.
* **Functional analysis** (§14.2). Theorem 14.10 (minimum norm duality), from Hahn–Banach on the
  quotient `X/M`; Lemma 14.11; Exercise 14.3; Lemma 14.12; Lemma 14.13 (the Norms Ergodic Lemma).
* **The Markov operator on `C(S)`** (§14.2). Exercise 14.4; Assumption 14.3; Lemma 14.9, the
  uniform convergence of `(1/M) Σ_{m=1}^M Tᵐf` to `∫ f dλ*`.
* **Theorem 14.14** (Riesz). Every continuous linear functional on `C(S)`, `S` compact metric,
  is `f ↦ ∫ f dν` for a unique signed measure `ν`. The functional is split into positive parts
  (`Λ⁺f = sup{Λg : 0 ≤ g ≤ f}`), and each is represented by Mathlib's Riesz–Markov–Kakutani theorem.
* **Sample paths** (§14.2). The path measure `μ(s₀, ·)` by Ionescu-Tulcea; the Markov property;
  the law of `sₙ` is `T*ⁿδ_{s₀}`. Lemma 14.8 by Theorem 14.6, and Theorem 14.7 from Lemmas 14.8
  and 14.9.

All names are in the namespace `StokeyLucasPrescott.LawsOfLargeNumbers`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ModesOfConvergence](LawsOfLargeNumbers/ModesOfConvergence.lean) | 10 | Lemmas 14.1–14.3, Exercise 14.2 |
| [SlidingIndicators](LawsOfLargeNumbers/SlidingIndicators.lean) | 15 | Exercise 14.1 |
| [Uncorrelated](LawsOfLargeNumbers/Uncorrelated.lean) | 19 | Chebyshev; Theorems 14.4–14.5 |
| [MartingaleLaw](LawsOfLargeNumbers/MartingaleLaw.lean) | 7 | Theorem 14.6 |
| [NormsErgodic](LawsOfLargeNumbers/NormsErgodic.lean) | 12 | Theorem 14.10, Lemma 14.11, Exercise 14.3, Lemmas 14.12–14.13 |
| [TransitionFunctions](LawsOfLargeNumbers/TransitionFunctions.lean) | 19 | Markov operators and `T*` (Chapter 8) |
| [MarkovOperator](LawsOfLargeNumbers/MarkovOperator.lean) | 12 | Exercise 14.4, Assumption 14.3, Lemma 14.9 from a representation of `C(S)*` |
| [Riesz](LawsOfLargeNumbers/Riesz.lean) | 26 | Theorem 14.14 |
| [MarkovPaths](LawsOfLargeNumbers/MarkovPaths.lean) | 17 | Path measure, Markov property, Lemma 14.8 |
| [MarkovSLLN](LawsOfLargeNumbers/MarkovSLLN.lean) | 6 | Lemma 14.9, Theorem 14.7 |

`TransitionFunctions` is copied from the Chapter 12 project (`WeakConvergence`).

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
