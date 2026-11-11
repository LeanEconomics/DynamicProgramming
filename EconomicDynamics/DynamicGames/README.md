# Miao Chapter 21: Dynamic Games, in Lean

This is the `EconomicDynamics/DynamicGames` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 21 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 21 develops "dynamic programming squared": the Abreu–Pearce–Stacchetti method for
repeated games with perfect and imperfect public monitoring, dynamic stochastic games and Markov
perfect equilibrium, the Great Fish War, and credible government policies. Every numbered
assumption, definition, lemma, proposition, theorem and example (Assumption 21.1.1, Definitions
21.1.1–21.1.8, 21.2.1, 21.4.1–21.4.5, Lemmas 21.1.1–21.1.4, 21.4.1–21.4.3, Propositions
21.1.1–21.1.3, 21.4.1–21.4.3, Theorems 21.1.1–21.1.3, 21.4.1, Examples 21.1.1–21.1.2,
21.4.1–21.4.6), the derivations of the text and Exercises 1–6 are proved, except that the
Judd–Yeltekin–Conklin operator preserves compactness (Mathlib v4.34.0 lacks Carathéodory's
theorem), the claim on p. 755 that the stochastic-game value set is the maximal fixed point of
`B` (its continuation values are history-dependent; the text gives no proof), and the exact lowest
discount factor in Exercise 6(f). The corrections are recorded in
[corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **306 theorems**, all new.

* **Repeated games with perfect monitoring** (§21.1.1–21.1.4): subgame perfection and the
  one-shot deviation principle (`definition_21_1_1`, `proposition_21_1_1`); admissibility and the
  operator `B`, self-generation, factorization `V = B(V)`, `V` as the maximal fixed point and its
  compactness (`lemma_21_1_2`, `theorem_21_1_1`, `theorem_21_1_2`, `proposition_21_1_2`);
  monotonicity, compactness and convergence of the iteration in Hausdorff distance
  (`lemma_21_1_3`, `lemma_21_1_4`, `theorem_21_1_3_hausdorff`); the prisoner's dilemma
  (`example_21_1_1`); simple strategies, whose characterisation is misprinted twice
  (`proposition_21_1_3`, `rg_proposition_21_1_3_misprint_restart`,
  `rg_proposition_21_1_3_misprint_own`); Exercises 1–2.
* **Imperfect public monitoring** (§21.1.5): perfect public equilibrium with self-generation and
  factorization (`dg_IsPPE`, `dg_factorization_ppe`); the noisy prisoner's dilemma, whose discount
  condition is misprinted (`example_21_1_2`, `example_21_1_2_printed_false`).
* **Dynamic stochastic games** (§21.2): Markov perfect equilibrium and its coupled Bellman
  equations (`definition_21_2_1_bellman_iff`).
* **The Great Fish War** (§21.3): the Markov perfect equilibrium in closed form and its optimality
  against all feasible plans (`dg_fish_mpe_closed_form`, `dg_fish_mpe`), overfishing relative to the
  cooperative solution (`dg_fish_overfishing`), the Stackelberg follower's rule corrected
  (`dg_fish_follower_printed_false`); Exercise 3 (`ex_21_3`).
* **Credible government policies** (§21.4): Barro–Gordon and the discrete example
  (`example_21_4_1_time_inconsistent`, `example_21_4_2`); the APS value set, where "largest fixed
  point" holds only among bounded sets (`theorem_21_4_1`, `cg_theorem_21_4_1_unbounded`); the best and
  worst SPE values, with Propositions 21.4.1–21.4.2 corrected (`proposition_21_4_1`,
  `cg_proposition_21_4_1_counterexample`, `cg_proposition_21_4_2_counterexample`); recursive
  strategies, trigger and stick-and-carrot (`cg_recursive_spe`, `example_21_4_5`,
  `example_21_4_6`, with counterexamples); Exercises 4–6.

All names are in the namespace `Miao.DynamicGames`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [RGStageGame](DynamicGames/RGStageGame.lean) | 19 | The repeated game: stage game, histories, strategies, discounted payoffs |
| [RGOneShot](DynamicGames/RGOneShot.lean) | 9 | Subgame perfection and the one-shot deviation principle |
| [RGPayoffSet](DynamicGames/RGPayoffSet.lean) | 10 | The equilibrium payoff set and the APS operator `B` |
| [RGPrisoners](DynamicGames/RGPrisoners.lean) | 7 | Example 21.1.1: the repeated prisoner's dilemma |
| [RGMaximal](DynamicGames/RGMaximal.lean) | 14 | `V` is the maximal fixed point of `B` in the feasible payoff set |
| [RGCompact](DynamicGames/RGCompact.lean) | 6 | Compactness: Proposition 21.1.2, Lemma 21.1.4, Exercises 21.1–21.2 |
| [RGComputation](DynamicGames/RGComputation.lean) | 11 | Computing `V` by iterating `B` |
| [RGSimple](DynamicGames/RGSimple.lean) | 21 | Simple strategies |
| [DGPublicMonitoring](DynamicGames/DGPublicMonitoring.lean) | 25 | Repeated games with imperfect public monitoring |
| [DGNoisyPD](DynamicGames/DGNoisyPD.lean) | 14 | Example 21.1.2: the noisy prisoner's dilemma |
| [DGStochasticGames](DynamicGames/DGStochasticGames.lean) | 10 | Dynamic stochastic games and Markov perfect equilibrium |
| [DGFishProblem](DynamicGames/DGFishProblem.lean) | 15 | The log fishing problem behind the Great Fish War |
| [DGFishWar](DynamicGames/DGFishWar.lean) | 18 | The Great Fish War |
| [CGOnePeriod](DynamicGames/CGOnePeriod.lean) | 9 | Credible government policies: the one-period economy |
| [CGRepeated](DynamicGames/CGRepeated.lean) | 29 | The infinitely repeated economy |
| [CGRecursive](DynamicGames/CGRecursive.lean) | 11 | Recursive strategies |
| [CGValueSet](DynamicGames/CGValueSet.lean) | 18 | The equilibrium value set |
| [CGBestWorst](DynamicGames/CGBestWorst.lean) | 20 | The best and the worst SPE values |
| [CGStokeyExample](DynamicGames/CGStokeyExample.lean) | 20 | Stokey's discrete monetary policy economy, repeated |
| [CGBarroGordon](DynamicGames/CGBarroGordon.lean) | 7 | The repeated Barro–Gordon economy |
| [CGExercise216](DynamicGames/CGExercise216.lean) | 13 | Exercise 21.6: a two-action credible-policy economy |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
