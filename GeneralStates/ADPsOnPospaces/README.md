# ADPs on pospaces in Lean

This is the `GeneralStates/ADPsOnPospaces/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/ADPsOnPospaces` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 3, "ADPs on Pospaces" (pp. 98–122), together with the
Appendix A results the chapter uses. Every exercise is included (Exercises 3.2.1–3.2.7 and
Exercise A.2.1). The library contains **434 theorems** and audits every declaration, including
structure constructors and projections.

* **ADPs on pospaces** (§3.1.1): globally stable ADPs are strongly order stable (Lemma 3.1.1,
  with Lemma A.5.18); **Theorem 3.1.2** (a fixed point of `T` gives optimality and convergence of
  VFI, OPI and HPI), **Corollary 3.1.3** (finite ADPs) and **Theorem 3.1.4** (order bounded ADPs
  on countably Dedekind complete spaces).
* **Metric ADPs** (§3.1.2): sup-nonexpansive metrics, Lemma A.5.21 and **Theorem 3.1.5**, which
  needs `V₀ ≠ ∅` (a counterexample shows it fails for `V₀ = ∅`).
* **Minimization** (§3.1.3): min-OPI and min-HPI, the dual transfer of global stability, and
  **Theorems 3.1.6–3.1.8**. Theorem 3.1.7 is proved under inf-nonexpansiveness, which its proof
  needs and which sup-nonexpansiveness does not imply (a three-point example).
* **Nonstationary policies** (§3.1.4): Assumption 3.1.1, **Lemma 3.1.9** and **Theorem 3.1.10**
  (every policy plan is weakly dominated by a stationary policy).
* **Bounded measurable functions as a Banach lattice**: `bX` built as a type with the supremum
  norm, complete, with a lattice norm and a closed order, countably Dedekind complete, and
  sup- and inf-nonexpansive (Proposition A.5.23, Corollary A.5.17).
* **MDPs and Q-factors** (§3.2.1): the finite MDP via Corollary 3.1.3, the countable MDP of
  Exercise 3.2.1 on `bX`, and the Q-factor model (Exercises 3.2.2–3.2.6). The "only if" of
  Exercise 3.2.3 fails at unreachable states (counterexample).
* **Optimal savings** (§3.2.2): **Proposition 3.2.1** via Theorem 3.1.4 (given Lemma 1.3.2 (i)),
  Remark 3.2.1, **Exercise 3.2.7** (a measurable greedy policy for continuous `v`, the largest
  maximizer, and continuity of `Tv`) and **Proposition 3.2.2** (the weakly continuous case).
* **No-discount optimal stopping** (§3.2.3): Exercise A.2.1, Lemmas 3.2.3–3.2.8,
  **Proposition 3.2.5** and **Theorem 3.2.9**, with stopping-time probabilities expressed through
  the killed kernel `K_E` and a drift criterion for Assumption 3.2.1.
* **Sequential analysis** (§3.2.4): the Bayesian belief kernel on `[0, 1]`, beliefs as a
  martingale, the conditional variance (3.32)–(3.33), **Lemma 3.2.11**, **Lemma 3.2.12** in drift
  form and **Proposition 3.2.10**. The book's state space `(0, 1)` is not invariant
  (counterexample).

The main entry points are `ADP.theorem_3_1_2`, `ADP.corollary_3_1_3`, `ADP.theorem_3_1_4`,
`ADP.theorem_3_1_5`, `ADP.theorem_3_1_6`, `ADP.theorem_3_1_7`, `ADP.theorem_3_1_8`,
`ADP.theorem_3_1_10`, `FiniteMDP.section_3_2_1_1`, `CountableMDP.exercise_3_2_1`,
`FiniteMDP.exercise_3_2_6`, `OptimalSavings.proposition_3_2_1`, `OptimalSavings.exercise_3_2_7`,
`OptimalSavings.proposition_3_2_2`, `NoDiscountStopping.theorem_3_2_9` and
`SeqAnalysis.proposition_3_2_10`, all in the namespace `SargentStachurski.ADPsOnPospaces`.

The order theory and ADP theory of Chapter 2 and the models of Chapter 1 are restated here, since
each chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records:

* the nonempty `V₀` that Theorem 3.1.5 needs;
* the inf-nonexpansiveness the proof of Theorem 3.1.7 needs;
* the reachability that the "only if" of Exercise 3.2.3 needs;
* the belief space `[0, 1]` in place of `(0, 1)`;
* the operator form of the stopping-time objects;
* what is not formalised: Lemma 1.3.2, Theorem A.3.9, and the strong Markov property behind
  (3.13).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](ADPsOnPospaces/Basics.lean) | 18 | Restated: contractions, global stability, Blackwell |
| [SupContraction](ADPsOnPospaces/SupContraction.lean) | 15 | Restated: `bX` as a set, sup-distance contractions |
| [ContractingDP](ADPsOnPospaces/ContractingDP.lean) | 31 | Restated: the Chapter 1 optimality template |
| [MarkovOperator](ADPsOnPospaces/MarkovOperator.lean) | 11 | Restated: Markov operators of stochastic kernels |
| [NeumannSeries](ADPsOnPospaces/NeumannSeries.lean) | 11 | Restated: `v ↦ r + βLv` and its Neumann series |
| [FiniteMDP](ADPsOnPospaces/FiniteMDP.lean) | 19 | Restated: §1.2.1, Theorems 1.2.1–1.2.2 |
| [OptimalSavings](ADPsOnPospaces/OptimalSavings.lean) | 13 | Restated: §1.3, Lemma 1.3.1 |
| [SequentialAnalysis](ADPsOnPospaces/SequentialAnalysis.lean) | 6 | Restated: §1.4, Bayes' rule, (1.58) |
| [OrderTheory](ADPsOnPospaces/OrderTheory.lean) | 17 | Restated: Appendix A order theory |
| [ADP](ADPsOnPospaces/ADP.lean) | 25 | Restated: §2.1 |
| [Algorithms](ADPsOnPospaces/Algorithms.lean) | 26 | Restated: §2.2.1–2.2.2 |
| [Minimization](ADPsOnPospaces/Minimization.lean) | 17 | Restated: §2.2.3 |
| [BXOrder](ADPsOnPospaces/BXOrder.lean) | 4 | Restated: monotone limits in `bX` |
| [SavingsADP](ADPsOnPospaces/SavingsADP.lean) | 9 | Restated: §2.3.2 |
| [MDPADP](ADPsOnPospaces/MDPADP.lean) | 18 | Restated: §2.3.3 |
| [Pospace](ADPsOnPospaces/Pospace.lean) | 13 | §3.1.1, Lemma A.5.18, Lemma 3.1.1, Thm 3.1.2, Cor 3.1.3, Thm 3.1.4 |
| [MetricADP](ADPsOnPospaces/MetricADP.lean) | 7 | §3.1.2, (A.22), Lemma A.5.21, Thm 3.1.5 |
| [MinPospace](ADPsOnPospaces/MinPospace.lean) | 13 | §3.1.3, Thms 3.1.6–3.1.8 |
| [Nonstationary](ADPsOnPospaces/Nonstationary.lean) | 9 | §3.1.4, Assumption 3.1.1, Lemma 3.1.9, Thm 3.1.10 |
| [BoundedMeasurable](ADPsOnPospaces/BoundedMeasurable.lean) | 31 | `bX` as a Banach lattice, Prop A.5.23, Cor A.5.17 |
| [MDPQFactors](ADPsOnPospaces/MDPQFactors.lean) | 14 | §3.2.1, Ex 3.2.2–3.2.6 |
| [CountableMDP](ADPsOnPospaces/CountableMDP.lean) | 9 | Ex 3.2.1 |
| [SavingsPospace](ADPsOnPospaces/SavingsPospace.lean) | 17 | §3.2.2, Props 3.2.1–3.2.2, Remark 3.2.1, Ex 3.2.7 |
| [NoDiscountStopping](ADPsOnPospaces/NoDiscountStopping.lean) | 52 | §3.2.3, Ex A.2.1, Lemmas 3.2.3–3.2.8, Prop 3.2.5, Thm 3.2.9 |
| [SequentialRevisited](ADPsOnPospaces/SequentialRevisited.lean) | 29 | §3.2.4, Lemmas 3.2.11–3.2.12, Prop 3.2.10 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
