# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 14, pp. 414–437. Lean names are relative to `StokeyLucasPrescott.LawsOfLargeNumbers`.
Where the Lean statement departs from the book, see [corrections](corrections.md).

## Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 415 | Convergence a.e. and in probability | `ConvAE`, `ConvInProb` |
| p. 415 | The sequence space `(S^∞, 𝒮^∞, μ(s₀, ·))` and `σₙ` | `pathM`, `trajKernel`, `isProbabilityMeasure_pathM` |
| (2), p. 415 | `E f(σₙ) = ∫ f dλₙ`, `λₙ = T*ⁿδ_{s₀}` | `law_coord`, `intro_2` |
| (3), p. 416 | Compactness and Feller are not enough | `feller_compact_not_enough` |

## §14.1 Definitions and preliminaries

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 14.1, p. 417 | `fₙ → f` a.e. iff `μ(\|fₙ − f\| ≤ ε for all n ≥ m) → 1` | `lemma_14_1`, `measurableSet_dev` |
| (2), p. 418 | `lim sup Aₙ`; `μ(Aₙ i.o.) = lim μ(⋃_{n≥m} Aₙ)` | `limsupSet`, `mem_limsupSet`, `measure_limsupSet` |
| Lemma 14.2, p. 418 | `fₙ → f` a.e. iff `μ(\|fₙ − f\| > ε i.o.) = 0` | `lemma_14_2` |
| Lemma 14.3, p. 419 | Borel–Cantelli | `measure_limsupSet_eq_zero`, `lemma_14_3` |
| p. 420 | a.e. convergence implies convergence in probability | `ConvAE.convInProb` |
| Exercise 14.1, p. 420 | The sliding indicators | `tri`, `row`, `pos`, `slideSet`, `sliding`, `unitLeb`, `row_one_zero`, `ex_14_1a`, `ex_14_1b`, `ex_14_1c` |
| Exercise 14.2, p. 420 | Thresholds `εₙ → 0`; a.e. convergent subsequences | `ex_14_2a`, `ex_14_2b` |
| (3), p. 421 | Chebyshev's inequality | `chebyshev` |
| p. 421 | Uncorrelated sequences; (4) | `Uncorrelated`, `centered`, `integral_centered`, `integral_centered_mul` |
| (6), p. 422 | The variance of a sum | `integral_sq_sum`, `integral_sq_sum_le` |
| Theorem 14.4, p. 421 | The weak law | `avgDev`, `theorem_14_4` |
| Theorem 14.5, p. 422 | The strong law | `partialDev`, `squares_convAE`, `gapSq`, `integral_gapSq_le`, `gaps_convAE`, `theorem_14_5` |
| Theorem 14.6, p. 424 | The strong law for martingale differences | `mgDiff`, `condExp_diff_ae_eq_zero`, `integral_mgDiff_mul`, `uncorrelated_diff`, `theorem_14_6` |

## §14.2 A strong law for Markov processes

| Source | Claim | Lean |
| --- | --- | --- |
| Assumptions 14.1–14.2, p. 425 | `S` compact; `T` Feller | `[CompactSpace S]`, `IsFeller` |
| Assumption 14.3, p. 425 | Cesàro averages converge weakly to a unique `λ*` | `Assumption14_3`, `assumption14_3_unique` |
| Theorem 14.7, p. 425 | Breiman's strong law | `theorem_14_7`, `abs_sum_sub_shift_le` |
| Lemma 14.8, p. 427 | `(1/N) Σ_{n=m+1}^N [f(σₙ) − (Tᵐf)(σ_{n−m})] → 0` a.s. | `lemma_14_8`, `lemma_14_8_shift`, `mg_avg_tendsto`, `lemma_14_8_counterexample` |
| pp. 429–430 | The Markov property | `markov_property`, `measurable_coord_piLE` |
| Lemma 14.9, p. 427 | `(1/M) Σ_{m=1}^M Tᵐf → ∫ f dλ*` uniformly | `lemma_14_9`, `lemma_14_9_of_repr`, `integral_cesaroOp_tendsto`, `markovCLM_pow_apply` |
| p. 431 | Duals, operator norms | `StrongDual` (Mathlib), `X →L[ℝ] X` |
| Theorem 14.10, p. 432 | Minimum norm duality | `norm_quotient_mk`, `theorem_14_10` |
| Lemma 14.11, p. 432 | Weak limits of `TX` lie in its closure | `mem_closure_of_weak`, `lemma_14_11` |
| Exercise 14.3, pp. 432–433 | `Tᵏ`, `Hₙ` linear with norm `≤ 1` | `ex_14_3a`, `cesaroOp`, `ex_14_3b` |
| Lemma 14.12, p. 433 | `‖Hₙx‖ → 0` on the closure of `(T − I)X` | `cesaroOp_sub_one`, `lemma_14_12` |
| Lemma 14.13, p. 434 | The Norms Ergodic Lemma | `cesaroOp_sub_mem_range`, `cesaroOp_fixed`, `lemma_14_13` |
| Exercise 14.4, p. 435 | `T` linear on `C(S)`, `‖T‖ = 1`, constants fixed | `markovBCF`, `markovCLM`, `markovCLM_const`, `ex_14_4` |
| Theorem 14.14, p. 435 | Riesz representation | `rieszPosSup`, `rieszPosPart`, `functional_jordanDecomposition`, `exists_measure_of_positive`, `sIntegral`, `theorem_14_14_exists`, `theorem_14_14_unique`, `theorem_14_14`, `theorem_14_14_prob` |
