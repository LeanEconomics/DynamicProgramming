# Abstract decision processes in Lean

This is the `GeneralStates/AbstractDecisionProcesses/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/AbstractDecisionProcesses`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 2, "Abstract Decision Processes" (pp. 58–97),
together with the Appendix A order theory the chapter uses. Every provable exercise is
included (Exercises 2.1.1, 2.2.1–2.2.6, 2.3.1–2.3.11 and 2.3.13–2.3.17). The library
contains **351 theorems** and audits every declaration, including structure constructors
and projections.

* **Order theory** (Appendix A): order stability and strong order stability, both self-dual
  (Lemma A.1.5); chain complete posets, with **Knaster–Tarski** proved by Zorn's lemma
  (Theorem A.5.2), Lemma A.5.3, and order intervals of `ℝ^X` (Lemma A.5.4); countable Dedekind
  completeness of `ℝ^X` and of `bX` (Example A.5.2, Corollary A.5.17) and its duality;
  order continuity and **Tarski–Kantorovich** (Theorem A.5.6); Lemma A.5.19.
* **Abstract dynamic programs** (§2.1): ADPs `(V, 𝕋)` on an arbitrary poset; greedy policies,
  `V_G`, the Bellman operator as a supremum (Lemma 2.1.1), `V_U`, `V_Σ` (Lemma 2.1.2), the value
  function, Bellman's principle and the fundamental optimality properties (Lemma 2.1.3,
  **Proposition 2.1.4**, **Theorem 2.1.5**, Corollary 2.1.6, **Theorem 2.1.7**).
* **Algorithms** (§2.2): the Howard and optimistic operators for every greedy selector,
  Lemmas 2.2.1–2.2.4 and Corollary 2.2.5; **Theorem 2.2.6** (finite ADPs, HPI in finitely many
  steps), **Theorem 2.2.7** (chain complete spaces) and **Theorem 2.2.8** (order bounded, order
  continuous, countably Dedekind complete).
* **Minimization** (§2.2.3): the dual ADP and the whole dictionary of Exercise 2.2.4 between
  min-objects of `A` and max-objects of `A^∂`; **Theorem 2.2.9** and Corollary 2.2.10.
* **Applications** (§2.3): the firm problem, optimal savings and finite MDPs as ADPs with their
  regularity, order boundedness and order continuity, and **Proposition 2.3.1**; the MDP on the
  chain complete `V̂` (Exercise 2.3.10); distributional dynamic programming with stochastic
  dominance (**Proposition 2.3.2**) and the Wasserstein contraction (Exercise 2.3.11); LQ control
  with the Loewner order, the Riccati map (Lemma 2.3.3, Exercises 2.3.13–2.3.17), the lifetime
  cost matrix `P_F` (Lemma 2.3.5), strong order stability (Lemma 2.3.6), Lemmas 2.3.7–2.3.9, the
  optimality results of §2.3.5.8 and Example 2.3.1.

The main entry points are `ChainComplete.exists_fixedPt`, `tarski_kantorovich`,
`ADP.fundamentalOptimality_iff`, `ADP.fundamentalOptimality_iff_exists_fixed`,
`ADP.fundamentalOptimality_of_chainComplete`, `ADP.fundamentalOptimality_of_finite`,
`ADP.convergence_of_chainComplete`, `ADP.convergence_of_dedekind`,
`ADP.minFundamentalOptimality_iff_exists_fixed`, `FirmProblem.adp_optimality`,
`OptimalSavings.adp_optimality`, `FiniteMDP.proposition_2_3_1`, `FiniteMDP.exercise_2_3_10`,
`DDP.Dσℋ_mono`, `DDP.W1_contraction`, `LQProblem.gain_isMinimizer`,
`LQProblem.IsStable.globallyStable`, `LQProblem.riccati_tfae` and `LQProblem.optimality`, all in
the namespace `SargentStachurski.AbstractDecisionProcesses`.

The Chapter 1 models (the firm problem, finite MDPs, optimal savings) with their supporting
contraction theory, and the Volume 1 facts about Markov matrices, contractions and spectral
radii, are restated here, since each chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records the hypotheses left implicit
(a stable control matrix for the LQ ADP, regularity of the savings ADP), the results that hold
more generally than stated, and what is not formalised (Lemma 2.3.4, completeness of the
Wasserstein space, and the well-posedness of the distributional ADP).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](AbstractDecisionProcesses/Basics.lean) | 18 | Restated: Markov matrices, contractions, global stability, Blackwell |
| [SpectralRadius](AbstractDecisionProcesses/SpectralRadius.lean) | 29 | Restated: spectral radius, Gelfand's formula, Neumann series |
| [SupContraction](AbstractDecisionProcesses/SupContraction.lean) | 15 | Restated: `bX`, sup-distance contractions, Lemma A.5.19 on `bX` |
| [ContractingDP](AbstractDecisionProcesses/ContractingDP.lean) | 31 | Restated: the Chapter 1 optimality template |
| [MarkovOperator](AbstractDecisionProcesses/MarkovOperator.lean) | 11 | Restated: Markov operators on `bX` |
| [NeumannSeries](AbstractDecisionProcesses/NeumannSeries.lean) | 11 | Restated: `v ↦ r + βLv` and its Neumann series |
| [FirmProblem](AbstractDecisionProcesses/FirmProblem.lean) | 20 | Restated: §1.1.1, Theorem 1.1.1 |
| [FiniteMDP](AbstractDecisionProcesses/FiniteMDP.lean) | 19 | Restated: §1.2.1, Theorems 1.2.1–1.2.2 |
| [OptimalSavings](AbstractDecisionProcesses/OptimalSavings.lean) | 13 | Restated: §1.3.1–1.3.2, Lemma 1.3.1 |
| [OrderTheory](AbstractDecisionProcesses/OrderTheory.lean) | 17 | Lemma A.1.5, Thm A.5.2, Lemmas A.5.3–A.5.5, Thm A.5.6, Lemma A.5.19 |
| [ADP](AbstractDecisionProcesses/ADP.lean) | 25 | §2.1, Lemmas 2.1.1–2.1.3, Prop 2.1.4, Thms 2.1.5, 2.1.7, Ex 2.1.1 |
| [Algorithms](AbstractDecisionProcesses/Algorithms.lean) | 26 | §2.2.1–2.2.2, Lemmas 2.2.1–2.2.4, Thms 2.2.6–2.2.8, Ex 2.2.1–2.2.2 |
| [Minimization](AbstractDecisionProcesses/Minimization.lean) | 17 | §2.2.3, Ex 2.2.3–2.2.6, Thm 2.2.9, Cor 2.2.10 |
| [BXOrder](AbstractDecisionProcesses/BXOrder.lean) | 4 | Lemma A.1.3 and Cor A.5.17 in `bX`, monotone convergence |
| [FirmADP](AbstractDecisionProcesses/FirmADP.lean) | 9 | §2.3.1, Ex 2.3.1–2.3.3 |
| [SavingsADP](AbstractDecisionProcesses/SavingsADP.lean) | 9 | §2.3.2, (2.14)–(2.15), Ex 2.3.4–2.3.5 |
| [MDPADP](AbstractDecisionProcesses/MDPADP.lean) | 18 | §2.3.3, Ex 2.3.6–2.3.10, Prop 2.3.1 |
| [LQAlgebra](AbstractDecisionProcesses/LQAlgebra.lean) | 19 | §2.3.5.1–2.3.5.2, Lemma 2.3.3, Ex 2.3.13–2.3.14, 2.3.16–2.3.17 |
| [LQControl](AbstractDecisionProcesses/LQControl.lean) | 24 | §2.3.5.3–2.3.5.8, Lemmas 2.3.5–2.3.9, Ex 2.3.15, Example 2.3.1 |
| [DistributionalDP](AbstractDecisionProcesses/DistributionalDP.lean) | 16 | §2.3.4, (2.21)–(2.23), Prop 2.3.2, Ex 2.3.11 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
