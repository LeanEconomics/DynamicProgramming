# Linear decision processes in Lean

This is the `GeneralStates/LinearDecisionProcesses/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/LinearDecisionProcesses` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 6, "Linear Decision Processes" (pp. 184–206), together with
the Appendix A results the chapter uses. Every exercise is included (Exercises 6.1.1 and 6.2.1).
The library contains **309 theorems** and audits every declaration, including structure
constructors and projections.

* **Feller properties** (§6.1.1): weak and strong Feller kernels; **Example 6.1.1**;
  **Lemma 6.1.1**, with Scheffé's lemma proved along the way; **Example 6.1.2** (change of
  variables on any group with a translation-invariant measure).
* **LDPs** (§6.1.2): `(Γ, r, K)` with `K = βP` as an additive ADP on `bX`; lifetime values
  `v_σ = ∑_t K_σ^t r_σ` (6.6); **Examples 6.1.3–6.1.6**. Example 6.1.6 shows the risk-sensitive
  policy operator is not affine.
* **Optimality** (§6.1.3):
  * **Proposition 6.1.2** (finite LDPs). Regularity is proved by pasting finitely many policies
    into one measurable policy.
  * **Proposition 6.1.3** (Feller LDPs).
  * Greedy policies are the pointwise maximizers (6.8), and the Bellman operator is (6.9).
* **Exogenous discounting** (§6.1.4): **Lemma 6.1.4** (as a sum over paths for finite `Z`),
  **Lemma 6.1.5**, **Exercise 6.1.1** and **Proposition 6.1.6**.
* **General-state MDPs** (§6.1.5): **Proposition 6.1.7** and **Example 6.1.8** (optimal savings with
  a continuous income density is a strong Feller MDP).
* **Applications** (§6.2): natural resource management (**Proposition 6.2.1**), stochastic rates of
  return (§6.2.2) and mortality (**Exercise 6.2.1**).
* **Appendix A**: **Exercise A.3.1** and **Theorem A.3.3** for interval correspondences
  `[g(x), h(x)]`, with the largest maximizer as an upper semicontinuous, hence Borel, selection.

The main entry points are `LDP.lifetime_value`, `LDP.proposition_6_1_2`, `LDP.proposition_6_1_3`,
`LDP.implications`, `lemma_6_1_1`, `example_6_1_2`, `Exo.lemma_6_1_4`,
`BanachLattice.lemma_6_1_5`, `Exo.exercise_6_1_1`, `LDP.proposition_6_1_6`, `proposition_6_1_7`,
`Savings.example_6_1_8`, `ResourceModel.proposition_6_2_1`, `ReturnsModel.section_6_2_2`,
`ReturnsModel.exercise_6_2_1` and `hasMaxSelections_Icc`, all in the namespace
`SargentStachurski.LinearDecisionProcesses`.

The Banach lattice theory of Chapter 4 and the ADP theory of Chapters 2–3 are restated here,
since each chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records:

* the discount operators in the proofs of Propositions 6.1.6 and 6.1.7, and in the solution to
  Exercise 6.2.1, take a supremum over actions. That need not be Borel measurable, so the
  operators need not map `bX` into itself; measurable operators that dominate `K_σ` replace them;
* Theorem A.3.3 (Berge's theorem with a measurable selection) is cited by the book. Here it is a
  hypothesis of the general results and a theorem for the interval correspondences that every
  application uses;
* "regularity is obvious in the finite case" (Proposition 6.1.2) needs a pasting argument, which is
  proved.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](LinearDecisionProcesses/Basics.lean) | 18 | Restated: contractions, global stability |
| [SupContraction](LinearDecisionProcesses/SupContraction.lean) | 15 | Restated: `bX` as a set of functions |
| [MarkovOperator](LinearDecisionProcesses/MarkovOperator.lean) | 11 | Restated: Markov operators |
| [OrderTheory](LinearDecisionProcesses/OrderTheory.lean) | 17 | Restated: Appendix A order theory |
| [ADP](LinearDecisionProcesses/ADP.lean) | 25 | Restated: §2.1 |
| [Algorithms](LinearDecisionProcesses/Algorithms.lean) | 26 | Restated: §2.2 |
| [Pospace](LinearDecisionProcesses/Pospace.lean) | 13 | Restated: §3.1.1 |
| [MetricADP](LinearDecisionProcesses/MetricADP.lean) | 7 | Restated: §3.1.2 |
| [BoundedMeasurable](LinearDecisionProcesses/BoundedMeasurable.lean) | 31 | Restated: `bX` as a Banach lattice |
| [BanachLattice](LinearDecisionProcesses/BanachLattice.lean) | 14 | Restated: §4.1.1 |
| [OrderContraction](LinearDecisionProcesses/OrderContraction.lean) | 19 | Restated: §4.1.2, Thms 4.1.4–4.1.8 |
| [BMOperators](LinearDecisionProcesses/BMOperators.lean) | 10 | Restated: operators on `bX` |
| [Correspondences](LinearDecisionProcesses/Correspondences.lean) | 13 | §A.3.1.3, Ex A.3.1, Thm A.3.3 for intervals |
| [LDP](LinearDecisionProcesses/LDP.lean) | 16 | §6.1.2, (6.4)–(6.7), Examples 6.1.4, 6.1.6 |
| [LDPOptimality](LinearDecisionProcesses/LDPOptimality.lean) | 13 | §6.1.3, Props 6.1.2–6.1.3, (6.8)–(6.9) |
| [Feller](LinearDecisionProcesses/Feller.lean) | 8 | §6.1.1, Example 6.1.1, Lemma 6.1.1, Example 6.1.2 |
| [ExogenousDiscount](LinearDecisionProcesses/ExogenousDiscount.lean) | 9 | §6.1.4.1, Lemmas 6.1.4–6.1.5, Ex 6.1.1 |
| [ExogenousLDP](LinearDecisionProcesses/ExogenousLDP.lean) | 10 | §6.1.4.2, Prop 6.1.6 |
| [GeneralMDP](LinearDecisionProcesses/GeneralMDP.lean) | 6 | §6.1.5, Example 6.1.3, Prop 6.1.7 |
| [NaturalResource](LinearDecisionProcesses/NaturalResource.lean) | 7 | §6.2.1, Prop 6.2.1 |
| [StochasticReturns](LinearDecisionProcesses/StochasticReturns.lean) | 17 | §6.2.2, Ex 6.2.1 |
| [SavingsFeller](LinearDecisionProcesses/SavingsFeller.lean) | 4 | Examples 6.1.5 and 6.1.8 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
