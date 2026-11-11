# Miao Chapter 12: Structural Estimation, in Lean

This is the `EconomicDynamics/StructuralEstimation` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 12 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 12 studies the estimation of dynamic models: the generalized method of moments, maximum
likelihood, and the simulation-based methods (simulated method of moments, simulated maximum
likelihood, indirect inference). Every numbered assumption, theorem, lemma and example
(Assumptions 12.1.1–12.1.10, Theorems 12.1.1–12.1.2, Lemma 12.1.1, Examples 12.1.1, 12.2.1 and
12.3.1–12.3.3), the derivations of the text and the mathematical content of Exercises 1–4 are
proved, with these limits: Lemma 12.1.1, a central limit theorem the book cites, does not follow
from its stated assumptions and enters Theorem 12.1.2 as a hypothesis, proved for i.i.d. data;
the χ² limits of the J, LR, Wald and LM statistics are not formalised; the general asymptotics of
maximum likelihood and the simulation estimators are proved in the exercise models (Bernoulli,
exponential, a location model) rather than in general. The corrections are recorded in
[corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **402 theorems**; 221 of them are carried
over from Chapters 4, 7 and 8.

* **GMM** (§12.1): the estimator exists (`gm_exists_estimator`); **Theorem 12.1.1** (consistency)
  from a uniform law of large numbers proved from Birkhoff's theorem (`theorem_12_1_1`,
  `gm_ulln`); **Theorem 12.1.2** (asymptotic normality) with the CLT as a hypothesis that holds
  for i.i.d. data (`theorem_12_1_2`, `lemma_12_1_1_iid`), checked on a concrete model
  (`gm_ex_theorem_12_1_2`); (12.3) is false for vector moments and holds row by row
  (`eq_12_3_counterexample`, `eq_12_3`); efficient weighting in the Loewner order
  (`gm_efficiency`), the long-run variance (`gm_longRunVar_limit`), HAC kernels, the J statistic
  algebra (`eq_12_4_algebra`); Example 12.1.1 (`example_12_1_1`).
* **Maximum likelihood** (§12.2): the information matrix equality and the Cramér–Rao bound
  (`ml_information_matrix_equality`, `ml_cramer_rao`), invariance (`ml_invariance_profile`), the
  job-search likelihood of Example 12.2.1, which identifies θ only through the reservation wage
  (`example_12_2_1`).
* **Simulation-based methods** (§12.3): the simulated method of moments and its `(1 + 1/S)`
  variance factor (`eq_12_5`, `ml_smm_variance_factor`, `ml_smm_optimal_weight`), simulated ML's
  bias for fixed `S` (`ml_sml_log_bias_strict`), indirect inference (`eq_12_7_optimal`); Example
  12.3.3's MLE is `N/ΣDᵢ`, not `ΣDᵢ/N` (`example_12_3_3`, `example_12_3_3_book_false`), and
  indirect inference equals SMM only in the mean parametrisation (`example_12_3_3_hazard_ne`).
* **Exercises**: the Bernoulli and exponential MLEs with consistency and asymptotic normality by
  Mathlib's strong law, central limit theorem and Slutsky theorem (`ex_12_1`, `ex_12_1_asymptotic`,
  `ex_12_2`, `ex_12_2_asymptotic`); the job-search content of Exercises 3–4.

All names are in the namespace `Miao.StructuralEstimation`. The Chapter 4 modules are copied from
[EconomicDynamics/ErgodicTheory](../ErgodicTheory/README.md); `MLBRContraction`, `MLODBasic` and
`MLODMcCall` from [EconomicDynamics/Applications](../Applications/README.md) (via
[EconomicDynamics/InfiniteHorizonDP](../InfiniteHorizonDP/README.md)).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [BirkhoffErgodic](StructuralEstimation/BirkhoffErgodic.lean) | 47 | Birkhoff's theorem (copied) |
| [PathSpace](StructuralEstimation/PathSpace.lean) | 23 | Path space and the shift (copied) |
| [Kernels](StructuralEstimation/Kernels.lean) | 32 | Kernels and path measures (copied) |
| [MarkovProperty](StructuralEstimation/MarkovProperty.lean) | 22 | The Markov property (copied) |
| [ErgodicTheorem](StructuralEstimation/ErgodicTheorem.lean) | 36 | §4.1, Exercises 1–2 (from Chapter 4) |
| [StationaryProcesses](StructuralEstimation/StationaryProcesses.lean) | 25 | §4.2: stationarity, ergodicity, the strong law, mixing (from Chapter 4) |
| [StationaryErgodicity](StructuralEstimation/StationaryErgodicity.lean) | 6 | Theorem 4.2.2 (from Chapter 4) |
| [GMBasic](StructuralEstimation/GMBasic.lean) | 6 | The GMM set-up (Miao, Chapter 12 introduction and §12.1, pp. 385–388) |
| [GMULLN](StructuralEstimation/GMULLN.lean) | 12 | The uniform law of large numbers behind Theorem 12.1.1 (Miao, §12.1, pp. 388–390) |
| [GMConsistency](StructuralEstimation/GMConsistency.lean) | 11 | Consistency of GMM: Theorem 12.1.1 (Miao, §12.1, pp. 388–390) |
| [GMAlgebra](StructuralEstimation/GMAlgebra.lean) | 28 | The deterministic algebra of GMM (Miao, §12.1, pp. 388–395) |
| [GMProbability](StructuralEstimation/GMProbability.lean) | 14 | Probability tools for the asymptotics of GMM (Miao, §12.1, pp. 390–392) |
| [GMNormality](StructuralEstimation/GMNormality.lean) | 5 | Asymptotic normality of GMM: Theorem 12.1.2 (Miao, §12.1, pp. 390–392) |
| [GMLemma1211](StructuralEstimation/GMLemma1211.lean) | 4 | Lemma 12.1.1: the central limit theorem for `√T g_T(θ₀)` (Miao, §12.1, p. 391) |
| [GMLongRun](StructuralEstimation/GMLongRun.lean) | 14 | The long-run covariance matrix and HAC estimators (Miao, §12.1, pp. 391–395) |
| [GMEuler](StructuralEstimation/GMEuler.lean) | 4 | Example 12.1.1: Euler-equation moment conditions (Miao, §12.1, pp. 388–389) |
| [GMExamples](StructuralEstimation/GMExamples.lean) | 16 | A concrete instance of the GMM assumptions (Miao, §12.1, pp. 387–391) |
| [MLBRContraction](StructuralEstimation/MLBRContraction.lean) | 8 | The Contraction Mapping Theorem and Blackwell's conditions (copied) |
| [MLODBasic](StructuralEstimation/MLODBasic.lean) | 8 | Tools for optimal stopping with i.i.d. offers (copied) |
| [MLODMcCall](StructuralEstimation/MLODMcCall.lean) | 14 | McCall's job search model, with and without job loss (copied) |
| [MLLikelihood](StructuralEstimation/MLLikelihood.lean) | 10 | Maximum likelihood: likelihood, score, information matrix equality, Cramér–Rao |
| [MLExponential](StructuralEstimation/MLExponential.lean) | 8 | Moments of the exponential distribution |
| [MLExercises](StructuralEstimation/MLExercises.lean) | 14 | Exercises 12.1 and 12.2: coin tossing and exponential maximum likelihood |
| [MLJobSearch](StructuralEstimation/MLJobSearch.lean) | 8 | The job search likelihood (Examples 12.2.1, 12.3.1; Exercises 12.3–12.4) |
| [MLSandwich](StructuralEstimation/MLSandwich.lean) | 3 | Sandwich covariance matrices and the optimal weighting matrix |
| [MLSimulatedMoments](StructuralEstimation/MLSimulatedMoments.lean) | 11 | The simulated method of moments (§12.3.1) |
| [MLIndirectInference](StructuralEstimation/MLIndirectInference.lean) | 13 | Simulated maximum likelihood and indirect inference (§§12.3.2–12.3.3) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
