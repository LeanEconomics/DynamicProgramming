# Recursive decision processes in Lean

This is the `GeneralStates/RecursiveDecisionProcesses/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/RecursiveDecisionProcesses` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 7, "Recursive Decision Processes" (pp. 207–245), together with
the Appendix A results the chapter uses. Every exercise is included (Exercises 7.1.1–7.1.5,
7.2.1–7.2.6 and 7.3.1–7.3.4). The library contains **392 theorems** and audits every declaration,
including structure constructors and projections.

* **RDPs** (§7.1): `(Γ, V, B)` with monotonicity (7.2) and consistency (7.3), the generated ADP
  and its greedy policies (7.10), and the Bellman operator (7.11).
  * Examples: finite MDPs (**Exercise 7.1.1**), firm valuation (7.4), firm valuation with
    unbounded profits (**Exercise 7.1.2**), savings, savings with Kreps–Porteus expectations
    (**Exercise 7.1.3**), modified rewards (7.7) and risk-sensitive MDPs (**Exercise 7.1.4**).
  * LDPs are RDPs (7.9). Isomorphic RDPs (**Exercise 7.1.5**).
  * **Lemmas 7.1.1** (finite actions) and **7.1.2** (continuous actions).
* **Bounded contractions** (§7.2.1): **Propositions 7.2.1** and **7.2.2**, by Theorem 4.1.3.
* **Weighted contractions** (§7.2.2): `bℓX` as `bX` through `v = ℓh` (Theorem A.5.24,
  Exercises A.5.22, A.5.24, A.5.25); **Lemma 7.2.3** and **Propositions 7.2.4** and **7.2.5**.
* **Properties of solutions** (§7.2.3): **Lemma A.2.6**, **Exercise 7.2.1**, and
  **Propositions 7.2.6–7.2.8**: monotone and concave value functions, and a unique, continuous
  optimal policy.
* **Certainty equivalents** (§7.2.4): risk measures and certainty equivalents
  (**Exercise 7.2.5**), coherence of `𝔼` and of the pessimistic certainty equivalent, the entropic
  certainty equivalent and its continuity (**Example 7.2.1**, **Exercise 7.2.6**), and a
  counterexample to cash invariance of Kreps–Porteus expectations.
* **MDPs with certainty equivalents** (§7.2.5): **Proposition 7.2.10**.
* **Applications** (§7.3):
  * optimal savings with utility unbounded above (**Exercises 7.3.1–7.3.2**, with
    **Exercises 7.2.2–7.2.4**);
  * irreversible investment, risk-neutral, risk-averse and ambiguity-averse
    (**Propositions 7.3.1–7.3.2**, **Exercise 7.3.3**, **Example 7.3.1**, §7.3.3.2);
  * Kreps–Porteus versus risk sensitivity (§7.3.4, **Exercise 7.3.4**).

The main entry points are `RDP.lemma_7_1_1`, `RDP.lemma_7_1_2`, `RDP.exercise_7_1_5`,
`BRDP.proposition_7_2_1`, `BRDP.proposition_7_2_2`, `WRDP.proposition_7_2_4`,
`WRDP.proposition_7_2_5`, `WRDP.proposition_7_2_6`, `WRDP.proposition_7_2_7`,
`WRDP.proposition_7_2_8`, `proposition_7_2_10`, `SavingsU.section_7_3_1`,
`SavingsU.exercise_7_2_4`, `Investment.proposition_7_3_1`, `Investment.proposition_7_3_2`,
`Investment.section_7_3_3` and `exercise_7_3_4`, all in the namespace
`SargentStachurski.RecursiveDecisionProcesses`.

The ADP and Banach lattice theory of Chapters 2–4 and the LDP theory of Chapter 6 are restated
here, since each chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records:

* Assumption 7.2.1 says `B` is bounded; with Blackwell's condition that can only hold for each
  fixed `v`, which is what the proofs use;
* Lemma 7.1.1 needs `x ↦ B(x, a, v)` and `{x : a ∈ Γ(x)}` measurable, which the definition of an
  RDP does not give;
* Exercise 7.1.2 needs `|π| ≤ ηℓ + δ`, not only the upper bound in (7.5);
* the solution to Exercise 7.3.4 takes the bounded positive `v`, whose logarithms need not be
  bounded; the value space must be bounded away from `0`;
* the weight function (7.25) can fall below `1`; the formalisation uses its properties, which the
  same construction with `u + 1` has;
* `Γ(k, z) = [0, θf(k, z)]` needs `θf ≥ 0` to be nonempty.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](RecursiveDecisionProcesses/Basics.lean) | 18 | Restated: contractions, global stability |
| [SupContraction](RecursiveDecisionProcesses/SupContraction.lean) | 15 | Restated: `bX` as a set of functions |
| [MarkovOperator](RecursiveDecisionProcesses/MarkovOperator.lean) | 11 | Restated: Markov operators |
| [OrderTheory](RecursiveDecisionProcesses/OrderTheory.lean) | 17 | Restated: Appendix A order theory |
| [ADP](RecursiveDecisionProcesses/ADP.lean) | 25 | Restated: §2.1 |
| [Algorithms](RecursiveDecisionProcesses/Algorithms.lean) | 26 | Restated: §2.2 |
| [Pospace](RecursiveDecisionProcesses/Pospace.lean) | 13 | Restated: §3.1.1 |
| [MetricADP](RecursiveDecisionProcesses/MetricADP.lean) | 7 | Restated: §3.1.2 |
| [BoundedMeasurable](RecursiveDecisionProcesses/BoundedMeasurable.lean) | 31 | Restated: `bX` as a Banach lattice |
| [BanachLattice](RecursiveDecisionProcesses/BanachLattice.lean) | 14 | Restated: §4.1.1, Theorem 4.1.3 |
| [OrderContraction](RecursiveDecisionProcesses/OrderContraction.lean) | 19 | Restated: §4.1.2 |
| [BMOperators](RecursiveDecisionProcesses/BMOperators.lean) | 10 | Restated: operators on `bX` |
| [Correspondences](RecursiveDecisionProcesses/Correspondences.lean) | 13 | Restated: Ex A.3.1, Thm A.3.3 for intervals |
| [LDP](RecursiveDecisionProcesses/LDP.lean) | 16 | Restated: §6.1.2 |
| [LDPOptimality](RecursiveDecisionProcesses/LDPOptimality.lean) | 13 | Restated: §6.1.3, `bcX` |
| [Feller](RecursiveDecisionProcesses/Feller.lean) | 8 | Restated: shock kernels, Scheffé's lemma |
| [GeneralMDP](RecursiveDecisionProcesses/GeneralMDP.lean) | 6 | Restated: §6.1.5 |
| [SavingsFeller](RecursiveDecisionProcesses/SavingsFeller.lean) | 4 | Restated: Examples 6.1.5, 6.1.8 |
| [UniqueMax](RecursiveDecisionProcesses/UniqueMax.lean) | 2 | Finite argmax selections; Thm A.3.3, last claim, for intervals |
| [RDP](RecursiveDecisionProcesses/RDP.lean) | 11 | §7.1.1.1, §7.1.2.2, Lemmas 7.1.1–7.1.2, Ex 7.1.5 |
| [BoundedRDP](RecursiveDecisionProcesses/BoundedRDP.lean) | 7 | §7.2.1, Props 7.2.1–7.2.2 |
| [WeightedRDP](RecursiveDecisionProcesses/WeightedRDP.lean) | 19 | §A.5.3.5, §7.2.2, Lemma 7.2.3, Props 7.2.4–7.2.5 |
| [SolutionProperties](RecursiveDecisionProcesses/SolutionProperties.lean) | 11 | Lemma A.2.6, §7.2.3, Ex 7.2.1, Props 7.2.6–7.2.8 |
| [CertaintyEquivalents](RecursiveDecisionProcesses/CertaintyEquivalents.lean) | 22 | §7.2.4, Ex 7.2.5, Example 7.2.1, Ex 7.2.6 |
| [CEMDP](RecursiveDecisionProcesses/CEMDP.lean) | 8 | §7.2.5, Prop 7.2.10 |
| [RDPExamples](RecursiveDecisionProcesses/RDPExamples.lean) | 11 | §7.1.1.2–7.1.1.8, (7.9), Exs 7.1.1–7.1.4 |
| [UnboundedSavings](RecursiveDecisionProcesses/UnboundedSavings.lean) | 19 | §7.3.1, Exs 7.3.1–7.3.2, Exs 7.2.2–7.2.4 |
| [IrreversibleInvestment](RecursiveDecisionProcesses/IrreversibleInvestment.lean) | 10 | §7.3.2–7.3.3, Props 7.3.1–7.3.2, Ex 7.3.3, Example 7.3.1 |
| [KrepsPorteus](RecursiveDecisionProcesses/KrepsPorteus.lean) | 6 | §7.3.4, Ex 7.3.4 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
