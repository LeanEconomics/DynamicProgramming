# Approximation and learning in Lean

This is the `GeneralStates/ApproximationAndLearning/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/ApproximationAndLearning` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 9, "Approximation and Learning" (pp. 295–321). Every
exercise is included (Exercises 9.1.1, 9.2.1 and 9.2.2). The library contains **421 theorems**
and audits every declaration, including structure constructors and projections.

* **Approximation methods** (§9.1.1): kernel averagers (9.2)–(9.3), nonexpansive and order
  preserving on `bX` (**Lemmas 9.1.1** and **9.1.6**, **Remark 9.1.2**); Gaussian kernels
  (**Example 9.1.1**); hat functions and piecewise linear interpolation, which interpolates, is
  affine between grid points and is the unique such function (**Example 9.1.2**); least squares
  with a full column rank design (p. 299).
* **Error bounds** (§9.1.2): the consequences of **Assumption 9.1.1**, **Lemma 9.1.2**, the
  termination of fitted value iteration (Algorithm 9.1), **Theorems 9.1.3** and **9.1.4**, and
  **Proposition 9.1.5**.
* **Stochastic approximation** (§9.1.3): damped iteration (**Lemma 9.1.7**); the asset pricing
  example (**Exercise 9.1.1**, `v* = (I − K)⁻¹Kd`, unbiased sampling, the noise bounds of
  footnote 1); the Robbins–Siegmund lemma and the **Robbins–Monro theorem** (Theorem 9.1.8)
  for contractions of a real Hilbert space, proved with the martingale convergence theorem.
* **Q-learning** (§9.2.1): the Q-factor Bellman operator (9.17), a contraction with fixed point
  `q*`; unbiased single-sample estimates and the update (9.18).
* **Risk-sensitive Q-learning** (§9.2.2): the order-reversing FDP (9.20)–(9.21)
  (**Exercise 9.2.1**), the primary Bellman equation (9.19) and the subordinate equation (9.22),
  optimality of the argmin policy by Theorem 5.2.18, and the contraction of `T̂_σ` for the
  log-metric (**Exercise 9.2.2**, Remark 9.2.1).
* **Policy-based methods** (§9.2.3): **Theorem 9.2.2** (optimality at one state implies
  optimality, under irreducibility), with a counterexample without irreducibility.

The main entry points are `ADP.assumption_9_1_1`, `ADP.lemma_9_1_2`, `ADP.theorem_9_1_3`,
`ADP.theorem_9_1_4`, `ADP.proposition_9_1_5`, `KernelAverager.lemma_9_1_1`,
`KernelAverager.lemma_9_1_6`, `example_9_1_2_unique`, `least_squares`, `lemma_9_1_7`,
`AssetPricing.exercise_9_1_1`, `robbins_siegmund`, `robbins_monro`, `FiniteMDP.section_9_2_1`,
`FiniteMDP.exercise_9_2_1`, `FiniteMDP.section_9_2_2_3`, `FiniteMDP.exercise_9_2_2` and
`FiniteMDP.theorem_9_2_2`, all in the namespace `SargentStachurski.ApproximationAndLearning`.

The ADP, finite MDP, Q-factor and FDP theory of Chapters 1–5 is restated here, since each
chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records:

* Lemma 9.1.7 needs `Θ` convex for the damped map to be a self-map of `Θ`;
* Theorem 9.1.8 does not say for which norm `T` is a contraction, and the noise can carry the
  iterates out of a proper subset `Θ`; it is proved here for contractions of a Hilbert space,
  where order preservation is not needed; the applications in the book (asset pricing,
  Q-learning) use supremum-norm contractions and rest on Tsitsiklis (1994), which is cited;
* Proposition 9.1.5 does not need `L` nonexpansive;
* Theorem 9.2.2 needs irreducibility (counterexample) and `β > 0`.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](ApproximationAndLearning/Basics.lean) | 18 | Restated: contractions, global stability |
| [SupContraction](ApproximationAndLearning/SupContraction.lean) | 15 | Restated: `bX` as a set of functions |
| [ContractingDP](ApproximationAndLearning/ContractingDP.lean) | 31 | Restated: §1.1–1.2 optimality template |
| [FiniteMDP](ApproximationAndLearning/FiniteMDP.lean) | 19 | Restated: §1.2.1, finite MDPs |
| [OrderTheory](ApproximationAndLearning/OrderTheory.lean) | 17 | Restated: Appendix A order theory |
| [ADP](ApproximationAndLearning/ADP.lean) | 25 | Restated: §2.1 |
| [Algorithms](ApproximationAndLearning/Algorithms.lean) | 26 | Restated: §2.2 |
| [Minimization](ApproximationAndLearning/Minimization.lean) | 17 | Restated: §2.2.3 |
| [MDPADP](ApproximationAndLearning/MDPADP.lean) | 18 | Restated: §2.3.3 |
| [Pospace](ApproximationAndLearning/Pospace.lean) | 13 | Restated: §3.1.1 |
| [MetricADP](ApproximationAndLearning/MetricADP.lean) | 7 | Restated: §3.1.2, Theorem 3.1.5 |
| [MinPospace](ApproximationAndLearning/MinPospace.lean) | 13 | Restated: §3.1.3 |
| [BoundedMeasurable](ApproximationAndLearning/BoundedMeasurable.lean) | 31 | Restated: `bX` as a Banach lattice |
| [MDPQFactors](ApproximationAndLearning/MDPQFactors.lean) | 14 | Restated: §3.2.1, Q-factors |
| [Conjugacy](ApproximationAndLearning/Conjugacy.lean) | 21 | Restated: §5.1.1 |
| [Semiconjugacy](ApproximationAndLearning/Semiconjugacy.lean) | 17 | Restated: §5.2.1 |
| [FactoredDP](ApproximationAndLearning/FactoredDP.lean) | 26 | Restated: §5.2.2–5.2.3, Theorems 5.2.13 and 5.2.18 |
| [QFactorFDP](ApproximationAndLearning/QFactorFDP.lean) | 10 | Restated: §5.3.1, Proposition 5.3.1 |
| [FittedVI](ApproximationAndLearning/FittedVI.lean) | 13 | §9.1.2, Assumption 9.1.1, Lemma 9.1.2, Thms 9.1.3–9.1.4, Prop 9.1.5 |
| [KernelAverager](ApproximationAndLearning/KernelAverager.lean) | 22 | §9.1.1, Lemmas 9.1.1, 9.1.6, Examples 9.1.1–9.1.2, least squares |
| [DampedIteration](ApproximationAndLearning/DampedIteration.lean) | 13 | §9.1.3.1, Lemma 9.1.7, §9.1.3.4, Ex 9.1.1 |
| [QLearning](ApproximationAndLearning/QLearning.lean) | 8 | §9.2.1 |
| [PolicyGradient](ApproximationAndLearning/PolicyGradient.lean) | 4 | §9.2.3.3, Theorem 9.2.2 |
| [RiskSensitiveQ](ApproximationAndLearning/RiskSensitiveQ.lean) | 21 | §9.2.2, Exs 9.2.1–9.2.2 |
| [RobbinsMonro](ApproximationAndLearning/RobbinsMonro.lean) | 2 | §9.1.3.2–9.1.3.3, Robbins–Siegmund, Theorem 9.1.8 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
