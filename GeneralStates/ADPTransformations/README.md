# ADP transformations in Lean

This is the `GeneralStates/ADPTransformations/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/ADPTransformations` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 5, "ADP Transformations" (pp. 147–182), together with the
Appendix A results the chapter uses. Every exercise is included (Exercises 5.1.1–5.1.11, 5.2.1–5.2.2
and 5.3.1–5.3.2). The library contains **587 theorems** and audits every declaration, including
structure constructors and projections.

* **Conjugacy** (§5.1.1): conjugate, topologically conjugate and order conjugate dynamical systems;
  **Propositions 5.1.1–5.1.2**, **Lemma 5.1.3**, **Examples 5.1.1–5.1.3** (log-linearization,
  diagonalization, and stability of `A` read off its eigenvalues) and **Exercises 5.1.1–5.1.3**.
* **Isomorphic ADPs** (§5.1.2): **Lemma 5.1.4**, **Theorems 5.1.5–5.1.7** (greedy policies,
  regularity, well-posedness, order stability, optimal policies, Bellman operators, value
  functions and VFI/OPI/HPI transfer), **Example 5.1.4**, and the anti-isomorphic case,
  **Exercise 5.1.6** and **Theorems 5.1.8–5.1.10**.
* **Epstein–Zin optimality** (§5.1.3): **Exercises 5.1.9–5.1.11**, **Lemmas 5.1.11–5.1.12** and
  **Proposition 5.1.13**. The fundamental optimality properties hold, and VFI, OPI and HPI
  converge, with no irreducibility assumption. The convexity and concavity of the aggregator are
  proved from its derivative. The min-results go through a reflection of the order interval.
* **Strong semiconjugacy** (§5.2.1): **Exercise 5.2.1**, **Lemmas 5.2.1–5.2.2** and
  **Theorems 5.2.3–5.2.4**. With the book's one-sided order continuity, Lemma 5.2.2 (ii) and
  Theorems 5.2.3–5.2.4 are false (`SemiconjCounterexample`), so the proofs here also use
  decreasing limits. Also the firm entry model: **Lemmas 5.2.5, 5.2.6 and 5.2.8** and
  **Proposition 5.2.7**.
* **Factored dynamic programs** (§5.2.2–5.2.3): **Lemmas 5.2.9–5.2.12**, **Theorem 5.2.13**,
  **Proposition 5.2.14**, **Lemmas 5.2.15–5.2.17**, **Exercise 5.2.2** and **Theorem 5.2.18**. The
  order-reversing case reduces to the order-preserving one by dualizing `V̂`.
* **Applications** (§5.3): Q-factors (**Propositions 5.3.1–5.3.2**); structural estimation via
  post-action values (§5.3.2); Epstein–Zin savings with iid endowments (**Exercises
  5.3.1–5.3.2**, Algorithm 5.1).

The main entry points are `IsConjugate.isUniqueFixed_iff`, `proposition_5_1_2`, `example_5_1_3`,
`IsOrderConjugate.lemma_5_1_3`, `ADP.theorem_5_1_5` … `ADP.theorem_5_1_10`,
`EZModel.proposition_5_1_13`, `IsStronglySemiconj.lemma_5_2_2_ii`,
`IsStronglySemiconj.theorem_5_2_3`, `SemiconjCounterexample.theorem_5_2_3_fails`,
`FirmEntry.proposition_5_2_7`, `FDP.theorem_5_2_13`, `FDP.proposition_5_2_14`,
`FDP.theorem_5_2_18`, `FiniteMDP.proposition_5_3_1`, `FiniteMDP.proposition_5_3_2`,
`section_5_3_2` and `EZSavings.section_5_3_3`, all in the namespace
`SargentStachurski.ADPTransformations`.

The Banach lattice theory of Chapter 4, the pospace theory and finite MDPs of Chapter 3, and the
ADP theory of Chapter 2 are restated here, since each chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records:

* Lemma 5.2.2 (ii) and Theorems 5.2.3 and 5.2.4 fail under the book's order continuity, which
  only covers increasing sequences. The counterexample uses two countable posets in which every
  increasing sequence is eventually constant; the corrected statements also ask for decreasing
  limits.
* Proposition 5.3.2 needs `β > 0`, while the book's MDPs allow `β = 0`; a one-state counterexample
  is given.
* The min-half of Lemma 5.1.11 does not follow from Exercise 2.2.6 alone. It is proved by
  reflecting the order interval.
* Weaker hypotheses that suffice: any bounds `c₁ < r^α < c₂`, `β ≥ 0` in the firm entry model, and
  no monotonicity for Lemma 5.2.12 (i).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](ADPTransformations/Basics.lean) | 18 | Restated: contractions, global stability |
| [SupContraction](ADPTransformations/SupContraction.lean) | 15 | Restated: `bX` as a set of functions |
| [ContractingDP](ADPTransformations/ContractingDP.lean) | 31 | Restated: the Chapter 1 optimality template |
| [MarkovOperator](ADPTransformations/MarkovOperator.lean) | 11 | Restated: Markov operators |
| [NeumannSeries](ADPTransformations/NeumannSeries.lean) | 11 | Restated: `v ↦ r + βLv` |
| [FiniteMDP](ADPTransformations/FiniteMDP.lean) | 19 | Restated: §1.2, finite MDPs |
| [OrderTheory](ADPTransformations/OrderTheory.lean) | 17 | Restated: Appendix A order theory |
| [ADP](ADPTransformations/ADP.lean) | 25 | Restated: §2.1 |
| [Algorithms](ADPTransformations/Algorithms.lean) | 26 | Restated: §2.2 |
| [Minimization](ADPTransformations/Minimization.lean) | 17 | Restated: §2.2.3, the dual ADP |
| [MDPADP](ADPTransformations/MDPADP.lean) | 18 | Restated: §2.3.3, the MDP ADP |
| [Pospace](ADPTransformations/Pospace.lean) | 13 | Restated: §3.1.1 |
| [MetricADP](ADPTransformations/MetricADP.lean) | 7 | Restated: §3.1.2 |
| [MinPospace](ADPTransformations/MinPospace.lean) | 13 | Restated: §3.1.3, min-algorithms |
| [BoundedMeasurable](ADPTransformations/BoundedMeasurable.lean) | 31 | Restated: `bX` as a Banach lattice |
| [MDPQFactors](ADPTransformations/MDPQFactors.lean) | 14 | Restated: §3.2.1, Q-factors |
| [BanachLattice](ADPTransformations/BanachLattice.lean) | 14 | Restated: §4.1.1 |
| [OrderContraction](ADPTransformations/OrderContraction.lean) | 19 | Restated: §4.1.2 |
| [DuTheorem](ADPTransformations/DuTheorem.lean) | 18 | Restated: §4.1.3, Du's theorem |
| [BMOperators](ADPTransformations/BMOperators.lean) | 10 | Restated: operators on `bX` |
| [StructuralEstimation](ADPTransformations/StructuralEstimation.lean) | 18 | Restated: §4.2.3, post-action values |
| [Conjugacy](ADPTransformations/Conjugacy.lean) | 21 | §5.1.1, Props 5.1.1–5.1.2, Lemma 5.1.3, Examples 5.1.1–5.1.3, Ex 5.1.1–5.1.3 |
| [IsomorphicADPs](ADPTransformations/IsomorphicADPs.lean) | 40 | §5.1.2, Lemma 5.1.4, Thms 5.1.5–5.1.10, Example 5.1.4, Ex 5.1.4–5.1.8 |
| [Semiconjugacy](ADPTransformations/Semiconjugacy.lean) | 17 | §5.2.1.1–2, Ex 5.2.1, Lemmas 5.2.1–5.2.2, Thms 5.2.3–5.2.4 |
| [FactoredDP](ADPTransformations/FactoredDP.lean) | 26 | §5.2.2–5.2.3, Lemmas 5.2.9–5.2.17, Thms 5.2.13, 5.2.18, Prop 5.2.14, Ex 5.2.2 |
| [QFactorFDP](ADPTransformations/QFactorFDP.lean) | 10 | §5.3.1, Props 5.3.1–5.3.2 |
| [StructuralFDP](ADPTransformations/StructuralFDP.lean) | 6 | §5.3.2 |
| [EZScalar](ADPTransformations/EZScalar.lean) | 10 | The aggregator: monotone, convex/concave (Ex 5.1.10) |
| [DuReflection](ADPTransformations/DuReflection.lean) | 7 | Du's theorem for minimization |
| [EpsteinZin](ADPTransformations/EpsteinZin.lean) | 37 | §5.1.3, Ex 5.1.9–5.1.11, Lemmas 5.1.11–5.1.12, Prop 5.1.13 |
| [EZSavings](ADPTransformations/EZSavings.lean) | 13 | §5.3.3, Ex 5.3.1–5.3.2, Algorithm 5.1 |
| [FirmEntry](ADPTransformations/FirmEntry.lean) | 18 | §5.2.1.3, Lemmas 5.2.5–5.2.8, Prop 5.2.7 |
| [SemiconjCounterexample](ADPTransformations/SemiconjCounterexample.lean) | 17 | Lemma 5.2.2 (ii) and Thms 5.2.3–5.2.4 fail as stated |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
