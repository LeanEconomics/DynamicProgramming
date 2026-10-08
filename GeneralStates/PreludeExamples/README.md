# Prelude: examples of dynamic programs in Lean

This is the `GeneralStates/PreludeExamples/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/PreludeExamples`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 1, "Prelude: Examples of Dynamic Programs"
(pp. 1–56), including every provable exercise (Exercises 1.1.1–1.1.3, 1.2.1–1.2.6
and 1.3.1–1.3.3). The library contains **153 theorems** and audits every
declaration, including structure constructors and projections.

* **Bounded measurable functions** (Appendix A): `bX` is closed under uniform limits, and a
  `β`-contraction for the supremum distance on a set of bounded functions closed under uniform
  limits is globally stable (Banach's theorem, re-proved here). Markov operators of stochastic
  kernels and the Neumann series `(I − βL)⁻¹r = ∑ₜ βᵗLᵗr`.
* **Contracting dynamic programs**: one abstract proof of the book's optimality template
  (§1.1.1.4): `v* = sup_σ v_σ` is the unique fixed point of the Bellman operator, optimal
  policies are the `v*`-greedy ones, VFI converges, HPI terminates when policies are finite,
  and OPI converges from every starting point when policy operators shift constants by `β`.
* **The firm problem** (§1.1): valuation (1.2)–(1.3) and Exercise 1.1.1, the policy and
  Bellman operators, Exercises 1.1.2–1.1.3, **Theorem 1.1.1** and Remark 1.1.2.
* **Beyond risk neutrality** (§1.1.3): the entropic certainty equivalent lies below the mean
  and equals `m − γσ²/2` exactly for normal payoffs; value-at-risk; the recursive
  risk-adjusted firm (1.14), whose well-posedness the book leaves open, satisfies
  Theorem 1.1.1 for every order preserving, constant-shifting aggregator, entropic risk
  included; the mean-variance aggregator is not order preserving.
* **Finite MDPs** (§1.2.1): Exercises 1.2.1–1.2.4 (with `v_σ = (I − βP_σ)⁻¹r_σ`),
  **Theorems 1.2.1–1.2.2**, **Lemma 1.2.3** and **Proposition 1.2.4** (the LP
  characterisation), and cash management.
* **Continuous time** (§1.2.2): uniformization, Exercises 1.2.5–1.2.6 (the HJB equation), and
  service rate control.
* **Optimal savings** (§1.3): Exercise 1.3.1, **Lemma 1.3.1** with the Neumann series (1.44),
  Exercise 1.3.2, and the DP results (i)–(iii) given greedy policies; the CRRA solution with
  Exercise 1.3.3, `η` (1.55), the Bellman equation (1.54) and consumption growth.
* **Sequential analysis** (§1.4): Bayes updating, the martingale property of beliefs and the
  Bellman operator (1.58).

The main entry points are `IsSupContraction.globallyStable`, `ContractingDP.optimality`,
`ContractingDP.hpi_terminates`, `ContractingDP.tendsto_opi`, `affineOp_hasSum`,
`FirmProblem.theorem_1_1_1`, `FirmProblem.riskAdjusted_optimality`,
`isShiftMonotone_entropicOp`, `FiniteMDP.theorem_1_2_1`, `FiniteMDP.theorem_1_2_2`,
`FiniteMDP.lp_solution`, `CTMDP.vσ_eq_uniformize`, `CTMDP.bellman_iff_hjb`,
`OptimalSavings.Tσ_globallyStable`, `OptimalSavings.dp_results`, `crra_bellman_le` and
`integral_bayesUpdate_mul_predDensity`, all in the namespace
`SargentStachurski.PreludeExamples`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records the uniformization rate that
must be positive, the service rate example's rate that is a maximum only for capacity at
least two, the hypotheses left implicit, and what is not formalised (the probabilistic
identification of lifetime values, Lemma 1.3.2 and Theorem 1.4.1, which the book proves in
later chapters).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SupContraction](PreludeExamples/SupContraction.lean) | 15 | `bX`, sup-distance contractions, Banach's theorem, Lemma A.5.19, Cor A.5.13 |
| [ContractingDP](PreludeExamples/ContractingDP.lean) | 31 | Optimality template of §1.1.1.4, VFI, HPI, OPI, Lemma 1.2.3 |
| [MarkovOperator](PreludeExamples/MarkovOperator.lean) | 11 | Markov operators of stochastic kernels on `bX` (§A.5.4) |
| [NeumannSeries](PreludeExamples/NeumannSeries.lean) | 11 | `v ↦ r + βLv`, global stability and the Neumann series (Thm A.4.10) |
| [FirmProblem](PreludeExamples/FirmProblem.lean) | 20 | §1.1.1, (1.2)–(1.9), Ex 1.1.1–1.1.3, Thm 1.1.1, Remark 1.1.2 |
| [RiskAdjusted](PreludeExamples/RiskAdjusted.lean) | 7 | §1.1.3, entropic CE, VaR, (1.14), mean-variance |
| [FiniteMDP](PreludeExamples/FiniteMDP.lean) | 19 | §1.2.1, Ex 1.2.1–1.2.4, Thms 1.2.1–1.2.2, Lemma 1.2.3, Prop 1.2.4 |
| [CashManagement](PreludeExamples/CashManagement.lean) | 1 | §1.2.1.5, (1.24)–(1.26) |
| [Uniformization](PreludeExamples/Uniformization.lean) | 12 | §1.2.2, (1.28)–(1.33), Ex 1.2.5–1.2.6, service rate control |
| [OptimalSavings](PreludeExamples/OptimalSavings.lean) | 13 | §1.3.1–1.3.2, Ex 1.3.1–1.3.2, Lemma 1.3.1, DP results |
| [CRRA](PreludeExamples/CRRA.lean) | 7 | §1.3.2.3, Ex 1.3.3, (1.52)–(1.55) |
| [SequentialAnalysis](PreludeExamples/SequentialAnalysis.lean) | 6 | §1.4, (1.56)–(1.58) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
