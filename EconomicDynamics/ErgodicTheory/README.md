# Miao Chapter 4: Ergodic Theory and Stationary Processes, in Lean

This is the `EconomicDynamics/ErgodicTheory` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 4 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 4 proves Birkhoff's ergodic theorem and applies it to stationary processes and to
stationary Markov processes. Every numbered result is proved except Theorem 4.2.4, a central limit
theorem that needs a martingale CLT; so are Exercises 1–6, and Exercise 7 in part. The
corrections are recorded in [corrections](docs/corrections.md), and every book item is located in
the [source map](docs/source-map.md). The library contains **244 theorems**; 145 of them are the
Meyn–Tweedie path-space and Birkhoff library, carried over.

* **Ergodic theorem** (§4.1): Birkhoff's theorem a.s. and in `L¹`, with the limit `E[f | I]`
  (`theorem_4_1_1`, `theorem_4_1_1_L1`), and the maximal ergodic theorem (`lemma_4_1_1`).
* **Stationary processes** (§4.2): stationarity as invariance of the path law under the shift
  (`isStationary_iff_measurePreserving`, `stationary_representation`), the strong law
  (`theorem_4_2_1`), the characterizations of ergodicity (`theorem_4_2_2`), and mixing implies
  ergodic (`theorem_4_2_3`). The book's shift-invariant sets do not form a σ-algebra
  (`shiftInvariant_compl_counterexample`).
* **Stationary Markov processes** (§4.3): the stationary chain (`ex_4_3`), invariant events
  (`lemma_4_3_1`), ergodic invariant distributions as the extreme points of the invariant set
  (`theorem_4_3_1`), the strong law (`theorem_4_3_2`) and mutual singularity of distinct ergodic
  measures (`ex_4_6_markov`).
* **Exercises**: Exercise 4 is false as printed (`ex_4_4_counterexample`); Exercise 7 is reduced
  to mixing and proved for characters (`ex_4_7_charFun`).

All names are in the namespace `Miao.ErgodicTheory`. The modules `BirkhoffErgodic`, `PathSpace`,
`Kernels`, `MarkovProperty` and `InvariantEvents` are copied from
[StochasticStability/LimitTheorems](../../StochasticStability/LimitTheorems/README.md) and its
prerequisites.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [BirkhoffErgodic](ErgodicTheory/BirkhoffErgodic.lean) | 47 | Birkhoff's theorem (copied) |
| [PathSpace](ErgodicTheory/PathSpace.lean) | 23 | Path space and the shift (copied) |
| [Kernels](ErgodicTheory/Kernels.lean) | 32 | Kernels and path measures (copied) |
| [MarkovProperty](ErgodicTheory/MarkovProperty.lean) | 22 | The Markov property (copied) |
| [InvariantEvents](ErgodicTheory/InvariantEvents.lean) | 21 | Invariant events and Lévy's upward theorem (copied) |
| [ErgodicTheorem](ErgodicTheory/ErgodicTheorem.lean) | 36 | §4.1, Exercises 1–2 |
| [StationaryProcesses](ErgodicTheory/StationaryProcesses.lean) | 25 | §4.2: stationarity, ergodicity, the strong law, mixing |
| [StationaryErgodicity](ErgodicTheory/StationaryErgodicity.lean) | 6 | Theorem 4.2.2 |
| [StationaryMarkov](ErgodicTheory/StationaryMarkov.lean) | 20 | §4.3, Exercises 3, 5, 6 |
| [ConditionalIndependence](ErgodicTheory/ConditionalIndependence.lean) | 7 | Exercise 4 |
| [GaussianMixing](ErgodicTheory/GaussianMixing.lean) | 5 | Exercise 7 (partial) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
