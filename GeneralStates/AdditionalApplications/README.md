# Additional applications in Lean

This is the `GeneralStates/AdditionalApplications/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd GeneralStates/AdditionalApplications` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 2: *General States*, Chapter 8, "Additional Applications" (pp. 247–293), together with
the Appendix A results the chapter uses. Every exercise that is provable as stated, or after a
recorded correction, is included; Exercise 8.1.8 is computational, and the exercises of §8.3.4
depend on results that fail as printed (see below). The library contains **771 theorems** and
audits every declaration, including structure constructors and projections.

* **Job search** (§8.1):
  * Markov offers on `L¹(φ)`, with the iid model as a special case: the policy operators (8.19),
    greedy policies and the Bellman operator (**Exercises 8.1.14–8.1.17**), **Proposition 8.1.2**
    by Theorem 4.1.8, the invariant interval `[0, v̄]` (**Exercises 8.1.18–8.1.20**), and the iid
    case (**Exercises 8.1.1–8.1.3**, **Proposition 8.1.1**).
  * Bounded offers (**Exercises 8.1.4–8.1.5**), with a counterexample to the claim that policy
    operators preserve `bcW`.
  * Continuation values and the reservation wage (**Exercises 8.1.6–8.1.7**, §8.1.2.1), the FDP of
    §8.1.2.2 via Theorem 5.2.13, and parametric monotonicity (**Example 8.1.1**,
    **Exercises 8.1.9–8.1.13**): in `c`, in `β`, the mean first passage time, first order
    stochastic dominance and mean-preserving spreads.
  * Persistent and transient wage components (**Exercises 8.1.21–8.1.24**).
* **Extensions** (§8.2):
  * nonlinear discounting (**Exercises 8.2.1–8.2.4**) and Kreps–Porteus expectations
    (**Exercise 8.2.5**, §8.2.2) via Du's theorem, with power means;
  * job search with learning (**Exercises 8.2.6–8.2.11**, **Proposition 8.2.1**): the reservation
    wage operator `T̂`, and monotone likelihood ratios imply first order stochastic dominance
    (**Proposition A.5.34**);
  * job search with separation (**Exercises 8.2.12–8.2.13**, **Proposition 8.2.2**).
* **More applications** (§8.3):
  * Coase meets Bellman (§8.3.1): negative discounting (**Exercises 8.3.1–8.3.3**,
    **Lemmas 8.3.3–8.3.5**, **Theorem 8.3.6**) and the production chain (**Definition 8.3.1**,
    **Propositions 8.3.1–8.3.2**), for every cost function and transaction cost;
  * optimal harvests by factorization (**Exercise 8.3.4**, §8.3.2.2);
  * the stochastic growth model (**Exercises 8.3.5–8.3.8**, **Proposition 8.3.7**,
    **Lemma 8.3.8**), the envelope condition (**Proposition 8.3.9**, **Corollary 8.3.10**) by the
    differentiable sandwich of Clausen and Strub (2020), and the Euler equation and
    Coleman–Reffett operator (**Exercises 8.3.9–8.3.10**, the comparison step of
    **Exercise 8.3.12**).

The main entry points are `JobSearch.proposition_8_1_1`, `JobSearch.proposition_8_1_2`,
`JobSearchFDP.section_8_1_2_2`, `exercise_8_1_11`, `exercise_8_1_13`,
`PersistentSearch.section_8_1_3_3`, `NLDiscount.exercise_8_2_4`, `KPSearch.section_8_2_2`,
`LearningSearch.proposition_8_2_1`, `TwoDensities.proposition_A_5_34`,
`Separation.proposition_8_2_2`, `NegDiscount.theorem_8_3_6`, `ProductionChain.proposition_8_3_1`,
`ProductionChain.proposition_8_3_2`, `Harvest.section_8_3_2_2`, `Growth.proposition_8_3_7`,
`Growth.lemma_8_3_8`, `Growth.proposition_8_3_9`, `Growth.corollary_8_3_10` and
`Growth.exercise_8_3_10`, all in the namespace `SargentStachurski.AdditionalApplications`.

The ADP, Banach lattice, transformation, LDP and RDP theory of Chapters 2–7 is restated here,
since each chapter project is self-contained.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records, among others:

* Exercise 8.1.4: policy operators with discontinuous `σ` do not map `bcW` into itself;
* Exercise 8.3.6 is false for discontinuous `v ∈ bX`, and the growth ADP is not regular on `bX`,
  so the OPI and HPI claims of Proposition 8.3.7 are not covered;
* Proposition 8.3.9 (i): the greedy policy need not be interior (`v = 0` consumes everything);
* §8.3.4: the space `V𝒞` is not contained in `bcℝ₊` and `M⁻¹σ = ∫₀^y u'(σ(x)) dx` can diverge,
  so Lemma 8.3.11, Propositions 8.3.12–8.3.13 and Exercise 8.3.11 are not established as stated;
* (8.53): the threshold `η` exists only for large `x̂`; a weaker condition, satisfied in every
  production chain, makes Propositions 8.3.1–8.3.2 unconditional;
* the solution to Exercise 8.3.5 uses the tangent inequality in the wrong direction.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](AdditionalApplications/Basics.lean) | 18 | Restated: contractions, global stability |
| [SupContraction](AdditionalApplications/SupContraction.lean) | 15 | Restated: `bX` as a set of functions |
| [MarkovOperator](AdditionalApplications/MarkovOperator.lean) | 11 | Restated: Markov operators |
| [OrderTheory](AdditionalApplications/OrderTheory.lean) | 17 | Restated: Appendix A order theory |
| [ADP](AdditionalApplications/ADP.lean) | 25 | Restated: §2.1 |
| [Algorithms](AdditionalApplications/Algorithms.lean) | 26 | Restated: §2.2 |
| [Pospace](AdditionalApplications/Pospace.lean) | 13 | Restated: §3.1.1 |
| [MetricADP](AdditionalApplications/MetricADP.lean) | 7 | Restated: §3.1.2 |
| [BoundedMeasurable](AdditionalApplications/BoundedMeasurable.lean) | 31 | Restated: `bX` as a Banach lattice |
| [BanachLattice](AdditionalApplications/BanachLattice.lean) | 14 | Restated: §4.1.1, Theorem 4.1.3 |
| [OrderContraction](AdditionalApplications/OrderContraction.lean) | 19 | Restated: §4.1.2, Theorem 4.1.8 |
| [BMOperators](AdditionalApplications/BMOperators.lean) | 10 | Restated: operators on `bX` |
| [Correspondences](AdditionalApplications/Correspondences.lean) | 13 | Restated: Ex A.3.1, Thm A.3.3 for intervals |
| [LDP](AdditionalApplications/LDP.lean) | 16 | Restated: §6.1.2 |
| [LDPOptimality](AdditionalApplications/LDPOptimality.lean) | 13 | Restated: §6.1.3, `bcX` |
| [Feller](AdditionalApplications/Feller.lean) | 8 | Restated: shock kernels, Scheffé's lemma |
| [UniqueMax](AdditionalApplications/UniqueMax.lean) | 2 | Restated: argmax selections, Thm A.3.3, last claim |
| [RDP](AdditionalApplications/RDP.lean) | 11 | Restated: §7.1 |
| [BoundedRDP](AdditionalApplications/BoundedRDP.lean) | 7 | Restated: §7.2.1, Props 7.2.1–7.2.2 |
| [WeightedRDP](AdditionalApplications/WeightedRDP.lean) | 19 | Restated: §7.2.2 |
| [SolutionProperties](AdditionalApplications/SolutionProperties.lean) | 11 | Restated: §7.2.3, Lemma A.2.6 |
| [Minimization](AdditionalApplications/Minimization.lean) | 17 | Restated: §2.2.3, Corollary 2.2.10 |
| [MinPospace](AdditionalApplications/MinPospace.lean) | 13 | Restated: §3.1.3 |
| [Conjugacy](AdditionalApplications/Conjugacy.lean) | 21 | Restated: §5.1.1 |
| [Semiconjugacy](AdditionalApplications/Semiconjugacy.lean) | 17 | Restated: §5.2.1 |
| [FactoredDP](AdditionalApplications/FactoredDP.lean) | 26 | Restated: §5.2.2–5.2.3, Theorem 5.2.13 |
| [DuTheorem](AdditionalApplications/DuTheorem.lean) | 18 | Restated: §4.1.3, Theorems 4.1.10–4.1.11 |
| [L1Operators](AdditionalApplications/L1Operators.lean) | 16 | Restated: Markov and multiplication operators on `L¹(ψ)` |
| [JobSearchL1](AdditionalApplications/JobSearchL1.lean) | 43 | §8.1.1, §8.1.3.1, Exs 8.1.1–8.1.3, 8.1.14–8.1.20, Props 8.1.1–8.1.2 |
| [JobSearchBounded](AdditionalApplications/JobSearchBounded.lean) | 5 | §8.1.1.2, Exs 8.1.4–8.1.5 |
| [ContinuationValues](AdditionalApplications/ContinuationValues.lean) | 26 | §8.1.2, Exs 8.1.6–8.1.7, 8.1.9–8.1.13, Example 8.1.1 |
| [PersistentTransient](AdditionalApplications/PersistentTransient.lean) | 36 | §8.1.3.3, Exs 8.1.21–8.1.24 |
| [PowerMean](AdditionalApplications/PowerMean.lean) | 18 | Kreps–Porteus power means: monotone, homogeneous, concave or convex |
| [NonlinearSearch](AdditionalApplications/NonlinearSearch.lean) | 40 | §8.2.1–8.2.2, Exs 8.2.1–8.2.5 |
| [JobSeparation](AdditionalApplications/JobSeparation.lean) | 13 | §8.2.4, Exs 8.2.12–8.2.13, Prop 8.2.2 |
| [JobLearning](AdditionalApplications/JobLearning.lean) | 58 | §8.2.3, Exs 8.2.6–8.2.11, Prop 8.2.1, Prop A.5.34 |
| [NegativeDiscounting](AdditionalApplications/NegativeDiscounting.lean) | 42 | §8.3.1, Exs 8.3.1–8.3.3, Lemmas 8.3.3–8.3.5, Thm 8.3.6, Def 8.3.1, Props 8.3.1–8.3.2 |
| [OptimalHarvest](AdditionalApplications/OptimalHarvest.lean) | 13 | §8.3.2, Ex 8.3.4 |
| [GrowthEuler](AdditionalApplications/GrowthEuler.lean) | 43 | §8.3.3, Exs 8.3.5–8.3.10, Prop 8.3.7, Lemma 8.3.8, Prop 8.3.9, Cor 8.3.10 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
