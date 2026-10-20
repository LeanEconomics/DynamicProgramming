# SLP Chapter 11: Strong Convergence of Markov Processes, in Lean

This is the `RecursiveMethods/StrongConvergence` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 11 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 11 studies when the distributions of a Markov process converge. It covers finite chains
first, then arbitrary state spaces in the total variation norm.

Every numbered result and every exercise is formalised. The book states Theorems 11.9b–c and
11.10b–c (Cesàro convergence under Doeblin's condition) without proof, referring to Doob (1953)
and Neveu (1965). They are proved here by a self-contained argument; see the last item below.

Five gaps in the book's arguments are closed and two definitions are corrected; see
[corrections](docs/corrections.md). The library contains **314 theorems**.

* **Finite chains** (§11.1).
  * Theorem 11.1: ergodic sets and transient states, and convergence of the averages
    `(1/n) Σ Πᵏ` to `Q`, whose rows are the invariant distributions.
  * Exercise 11.1: the block form of `Q`, with the absorption probabilities.
  * Theorem 11.2, through a maximum principle for `Π`-harmonic functions.
  * Lemma 11.3 and Theorem 11.4. The book leaves "cyclically moving subsets" undefined, and its
    converse assumes convergence rather than the stated hypothesis. Here three conditions are
    proved equivalent, using aperiodicity: a positive column in some `Πᴺ`; a unique ergodic set
    without cyclically moving subsets; and convergence of `p₀Πⁿ`. Convergence is geometric.
  * Examples 1–7, including the non-convergent periodic chain and the shift with no invariant
    distribution.
* **Convergence concepts** (§11.2). Setwise, weak and strong convergence. Exercise 11.2, by the
  layer-cake formula. The halving example converges weakly but setwise to nothing.
* **Total variation** (§11.3).
  * The total variation norm on signed measures (Exercise 11.3).
  * Lemma 11.5, for measures of equal mass.
  * Theorems 11.6–11.7: three equivalent forms of strong convergence.
  * Lemma 11.8: completeness, with the limit–sum exchange the book leaves unjustified.
* **Sufficient conditions** (§11.4).
  * Doeblin's Condition D and Condition M, with Exercises 11.4a–j and 11.5a–c. The three
    non-examples come from one lemma about injective deterministic maps.
  * Ergodic sets under Condition D (Theorems 11.9a, 11.10a). The book's existence argument
    takes the intersection of a decreasing chain of invariant sets, which need not be ergodic;
    a corrected argument is used.
  * Lemma 11.11: `T*ᴺ` is a contraction under Condition M.
  * Theorem 11.12: geometric convergence to the unique invariant measure, and the converse.
  * Theorems 11.9b–c and 11.10b–c, which the book does not prove. Under Condition D, the
    Cesàro averages `(1/N) Σ_{n=1}^{N} T*ⁿλ₀` converge in total variation to an invariant
    measure. Each of the `M` ergodic sets carries exactly one invariant measure, and every
    invariant measure is a convex combination of these. The proof has five steps:
    * Doeblin's condition makes the averages uniformly absolutely continuous with respect to
      `Σⱼ 2^{-j-1}φPʲ`.
    * A limit along an ultrafilter is then an invariant measure on each ergodic set.
    * Uniqueness on an ergodic set follows from the Hahn decomposition.
    * Von Neumann's mean ergodic theorem in `L²(π)` handles measures with bounded density, and
      Lebesgue decompositions with respect to `φ` extend this to all measures on an ergodic set.
    * The transient set is absorbed, through a maximum argument for harmonic functions.

All names are in the namespace `StokeyLucasPrescott.StrongConvergence`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [FiniteChains](StrongConvergence/FiniteChains.lean) | 24 | Consequents, transient and recurrent states, ergodic sets; Theorem 11.1a |
| [FiniteAverages](StrongConvergence/FiniteAverages.lean) | 18 | Theorem 11.1b–c |
| [FiniteErgodic](StrongConvergence/FiniteErgodic.lean) | 6 | Maximum principle; Theorem 11.2 |
| [FiniteBlockForm](StrongConvergence/FiniteBlockForm.lean) | 16 | Decay of transient mass; Exercise 11.1 |
| [NumericalSemigroup](StrongConvergence/NumericalSemigroup.lean) | 4 | Additively closed sets with gcd 1 |
| [FiniteConvergence](StrongConvergence/FiniteConvergence.lean) | 24 | Lemma 11.3, Theorem 11.4 |
| [FiniteExamples](StrongConvergence/FiniteExamples.lean) | 27 | Examples 1–5 |
| [TransitionFunctions](StrongConvergence/TransitionFunctions.lean) | 19 | Markov operators and `T*` (Chapter 8) |
| [ConvergenceConcepts](StrongConvergence/ConvergenceConcepts.lean) | 6 | §11.2, Exercise 11.2, the halving example |
| [TotalVariation](StrongConvergence/TotalVariation.lean) | 15 | The total variation norm, Exercise 11.3, Lemma 11.5 |
| [TVConvergence](StrongConvergence/TVConvergence.lean) | 13 | Theorems 11.6–11.7, Lemma 11.8 |
| [Doeblin](StrongConvergence/Doeblin.lean) | 25 | Conditions D and M, Exercises 11.4–11.5 |
| [DoeblinErgodic](StrongConvergence/DoeblinErgodic.lean) | 16 | Ergodic sets; Theorems 11.9a, 11.10a |
| [InfiniteExamples](StrongConvergence/InfiniteExamples.lean) | 2 | Examples 6–7 |
| [ConditionM](StrongConvergence/ConditionM.lean) | 11 | Lemma 11.11, Theorem 11.12 |
| [CesaroAverages](StrongConvergence/CesaroAverages.lean) | 24 | Cesàro averages of `T*ⁿλ` and their Cauchy property |
| [ErgodicMeasures](StrongConvergence/ErgodicMeasures.lean) | 7 | Reachability; uniqueness of the invariant measure on an ergodic set |
| [MeanErgodicL2](StrongConvergence/MeanErgodicL2.lean) | 16 | The Markov operator on `L²(π)`; bounded densities |
| [DoeblinExistence](StrongConvergence/DoeblinExistence.lean) | 25 | Uniform integrability; invariant measures as ultrafilter limits |
| [DoeblinCesaro](StrongConvergence/DoeblinCesaro.lean) | 16 | Absorption; Theorems 11.9b–c, 11.10b–c |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
