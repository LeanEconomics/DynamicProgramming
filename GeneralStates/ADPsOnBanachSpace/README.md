# ADPs on Banach space in Lean

This is the `GeneralStates/ADPsOnBanachSpace/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/ADPsOnBanachSpace` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 4, "ADPs on Banach Space" (pp. 123–146), together with the
Appendix A results the chapter uses. Every exercise is included (Exercises 4.1.1–4.1.4,
4.2.1–4.2.5 and A.4.2). The library contains **387 theorems** and audits every declaration,
including structure constructors and projections.

A Banach lattice is, in Mathlib's terms, a complete normed space with a lattice order and a solid
(lattice) norm. The concrete Banach lattices used are `bX` (bounded measurable functions, built as
a type of its own), `L¹(ψ)` and `ℝⁿ` with the supremum norm.

* **Contractions and Blackwell's condition** (§4.1.1): **Theorem 4.1.1** (eventually contracting
  maps are globally stable, with geometric rate), normalized order units and
  **Proposition A.5.23**, **Lemma 4.1.2**, **Theorem 4.1.3**, certainty equivalent operators and
  **Exercises 4.1.1** (Harrison–Kreps) and **4.1.2**.
* **Order contractions** (§4.1.2): discount operators (**Exercise 4.1.3**), the spectral radius in
  Gelfand's form (**Exercise A.4.2**), **Examples 4.1.1–4.1.2**, **Theorem 4.1.4**,
  **Exercise 4.1.4** and **Theorems 4.1.5–4.1.8**, for any value space isometrically and
  order-embedded in the lattice.
* **Concavity and convexity** (§4.1.3): **Theorem 4.1.10 (Du)**, which the book cites, proved
  here for Banach lattices; **Lemma 4.1.9** and **Theorem 4.1.11**.
* **Firm valuation** (§4.2.1): **Proposition 4.2.1** on `bX`, the extension to integrable profits
  in `L¹(ψ)` built on the Markov operator of a stationary distribution, and state-dependent
  discounting (**Proposition 4.2.2**, **Exercise 4.2.1**).
* **A real option problem** (§4.2.2): `q = (I − K)⁻¹π`, **Exercises 4.2.2–4.2.3**, the Bellman
  equation (4.18) and **Proposition 4.2.3**. The constant term in (4.17) is misprinted.
* **Structural estimation** (§4.2.3): measurable greedy policies (**Exercise 4.2.4**),
  **Exercise 4.2.5**, **Propositions 4.2.4–4.2.6** and the risk-sensitive certainty equivalent.

The main entry points are `theorem_4_1_1`, `BanachLattice.theorem_4_1_3`,
`BanachLattice.theorem_4_1_4`, `BanachLattice.theorem_4_1_6`, `BanachLattice.theorem_4_1_7`,
`BanachLattice.theorem_4_1_8`, `BanachLattice.theorem_4_1_10`, `BanachLattice.theorem_4_1_11`,
`FirmProblem.proposition_4_2_1`, `FirmL1.optimality`, `FirmSD.proposition_4_2_2`,
`RealOption.proposition_4_2_3`, `proposition_4_2_4`, `FiniteSE.proposition_4_2_5` and
`PostAction.proposition_4_2_6`, all in the namespace `SargentStachurski.ADPsOnBanachSpace`.

The pospace and metric ADP theory of Chapter 3, the ADP theory of Chapter 2 and the firm model of
Chapter 1 are restated here, since each chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records:

* the misprinted constant term in (4.17), which should be `−c + K(σq)`;
* the nonempty `V₀` that semi-regularity needs (as in Theorem 3.1.5);
* the weaker hypotheses that suffice: closure under `v ↦ v + κe` in place of "increasing", any
  complete value space, and stationarity alone for the Markov operator on `L¹`;
* the forms used: Gelfand's formula for the spectral radius, and a.e. statements in `L¹`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](ADPsOnBanachSpace/Basics.lean) | 18 | Restated: contractions, global stability |
| [SupContraction](ADPsOnBanachSpace/SupContraction.lean) | 15 | Restated: `bX` as a set of functions |
| [ContractingDP](ADPsOnBanachSpace/ContractingDP.lean) | 31 | Restated: the Chapter 1 optimality template |
| [MarkovOperator](ADPsOnBanachSpace/MarkovOperator.lean) | 11 | Restated: Markov operators |
| [NeumannSeries](ADPsOnBanachSpace/NeumannSeries.lean) | 11 | Restated: `v ↦ r + βLv` |
| [FirmProblem](ADPsOnBanachSpace/FirmProblem.lean) | 20 | Restated: §1.1.1, the firm problem |
| [OrderTheory](ADPsOnBanachSpace/OrderTheory.lean) | 17 | Restated: Appendix A order theory |
| [ADP](ADPsOnBanachSpace/ADP.lean) | 25 | Restated: §2.1 |
| [Algorithms](ADPsOnBanachSpace/Algorithms.lean) | 26 | Restated: §2.2 |
| [Pospace](ADPsOnBanachSpace/Pospace.lean) | 13 | Restated: §3.1.1 |
| [MetricADP](ADPsOnBanachSpace/MetricADP.lean) | 7 | Restated: §3.1.2, Theorem 3.1.5 |
| [BoundedMeasurable](ADPsOnBanachSpace/BoundedMeasurable.lean) | 31 | Restated: `bX` as a Banach lattice |
| [BanachLattice](ADPsOnBanachSpace/BanachLattice.lean) | 14 | §4.1.1, Thm 4.1.1, Prop A.5.23, Lemma 4.1.2, Thm 4.1.3, Ex 4.1.2 |
| [OrderContraction](ADPsOnBanachSpace/OrderContraction.lean) | 19 | §4.1.2, Ex 4.1.3–4.1.4, A.4.2, Examples 4.1.1–4.1.2, Thms 4.1.4–4.1.8 |
| [DuTheorem](ADPsOnBanachSpace/DuTheorem.lean) | 18 | §4.1.3, Lemma 4.1.9, Thms 4.1.10–4.1.11 |
| [BMOperators](ADPsOnBanachSpace/BMOperators.lean) | 10 | Operators on `bX`, Ex 4.1.1 |
| [FirmBanach](ADPsOnBanachSpace/FirmBanach.lean) | 16 | §4.2.1.1, §4.2.1.3, Props 4.2.1–4.2.2, Ex 4.2.1 |
| [StructuralEstimation](ADPsOnBanachSpace/StructuralEstimation.lean) | 18 | §4.2.3.1, §4.2.3.3–4, Ex 4.2.4–4.2.5, Props 4.2.4, 4.2.6 |
| [FiniteSE](ADPsOnBanachSpace/FiniteSE.lean) | 12 | §4.2.3.2, Prop 4.2.5 |
| [L1Operators](ADPsOnBanachSpace/L1Operators.lean) | 16 | Operators on `L¹(ψ)`, Lemma A.5.32 (bound) |
| [L1Applications](ADPsOnBanachSpace/L1Applications.lean) | 39 | §4.2.1.2, §4.2.2, Ex 4.2.2–4.2.3, Prop 4.2.3 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
