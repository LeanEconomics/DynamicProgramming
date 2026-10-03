# Operators and fixed points in Lean

This is the `FiniteStates/OperatorsFixedPoints/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/OperatorsFixedPoints`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 2, "Operators and Fixed Points" (pp. 42–80),
including every provable exercise (Exercises 2.1.1–2.1.7, 2.2.1–2.2.39,
2.3.1–2.3.14). The library contains **235 theorems** and audits every
declaration, including structure constructors and projections.

* **The Perron–Frobenius theorem for nonnegative matrices** (Theorem 2.3.1),
  which the book quotes from Meyer (2000), is proved from scratch: `ρ(A)` is an
  eigenvalue of every `A ≥ 0` with nonnegative, nonzero left and right
  eigenvectors. The proof goes through the resolvent `(tI − A)⁻¹ = ∑ t^{−(k+1)}Aᵏ`,
  which is nonnegative for `t > ρ(A)`, dominates the complex resolvent entrywise,
  and must blow up as `t ↓ ρ(A)` because otherwise a Neumann perturbation would
  remove every eigenvalue of modulus `ρ(A)` from the spectrum; normalising to the
  simplex and passing to a limit gives the eigenvector. Its consequences follow:
  `ρ(A)` lies between the smallest and largest row sums and column sums
  (Lemma 2.3.2), every Markov matrix has `ρ(P) = 1` and a stationary distribution
  (Exercise 2.3.2), and the local spectral radius `‖Aᵏh‖^{1/k} → ρ(A)` for
  `h ≫ 0` (Lemma 2.3.3, which the book cites from Krasnosel'skii et al.).
* **Conjugacy and stability** (§2.1): conjugate systems share fixed points, their
  cardinality, orbit convergence, global and local stability (Proposition 2.1.1,
  2.1.2, Exercises 2.1.1–2.1.6); `ln` conjugates `Auᵅ` to an affine map; the
  derivative criterion `|g'(x*)| < 1` for local stability; convergence rates,
  with the error ratio of a differentiable map converging to `|T'(u*)|`
  (Exercise 2.1.7); the Newton map (2.2) and its fixed points.
* **Order** (§2.2): partial orders, greatest elements, suprema (Exercises
  2.2.1–2.2.17); the pointwise order on `ℝ^X`, sublattices, Lemma 2.2.1, the key
  estimate `|max f − max g| ≤ max |f − g|` (Lemma 2.2.2) and the upper envelope
  of contractions (Lemma 2.2.3); order-preserving maps and Blackwell's condition
  (Lemma 2.2.4); first-order stochastic dominance with Lemma 2.2.5 (the converse
  by Abel summation), Lemma 2.2.6 and quantiles (Exercise 2.2.35); parametric
  monotonicity (Proposition 2.2.7) applied to the Solow–Swan steady state and the
  job-search continuation value (Exercises 2.2.38–2.2.39).
* **The lake model** (§2.3.2): the workforce grows at `g = b − d`, `ρ(A) = 1 + g`,
  `1ᵀ` is a left eigenvector and the normalised right eigenvector is (2.14),
  uniquely (Exercises 2.3.4–2.3.7).
* **Linear operators** (§2.3.3): matrices and linear operators on `ℝ^X`
  correspond one-to-one (Theorem 2.3.4, Lemma 2.3.5), kernel and product-space
  operators, positive operators are the order-preserving ones, Markov operators
  are the Markov matrices and preserve distributions (Lemma 2.3.6, Exercises
  2.3.8–2.3.14).

The main entry points are `perron_frobenius`, `perron_frobenius_left`,
`IsMarkov.exists_stationary`, `tendsto_norm_pow_mulVec_rpow`,
`IsTopConjugate.globallyStable_iff`, `locallyStable_of_abs_deriv_lt_one`,
`tendsto_error_ratio`, `isContractionOn_upperEnvelope`, `isContractionOn_of_blackwell`,
`fosd_of_ccdf_le`, `fixedPt_le_of_dominates`, `LakeModel.eq_xbar_of_eigen` and
`isMarkovOp_iff_vecMulOp_distribution`, all in the namespace
`SargentStachurski.OperatorsFixedPoints`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (Exercise 2.2.12 needs `n ≥ 1`, Exercise 2.1.7
needs only a continuous first derivative), the hypotheses the book leaves
implicit, and what is not formalised: the Hartman–Grobman theorem and its
corollary, the quadratic convergence of Newton's method, and the irreducible and
positive cases of Perron–Frobenius with the convergence (2.11), which the plan
proves with Chapter 6.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](OperatorsFixedPoints/Basics.lean) | 12 | Global stability (p. 22), contractions (1.17), Banach's theorem from Mathlib's `ContractingWith`, local stability (p. 45) |
| [Conjugacy](OperatorsFixedPoints/Conjugacy.lean) | 26 | Conjugate maps (p. 43), Ex 2.1.1–2.1.2, Prop 2.1.1, Examples 2.1.1–2.1.3; topological conjugacy, Ex 2.1.3–2.1.6, Prop 2.1.2; Example 2.1.4 (`x²`); the derivative criterion for local stability |
| [ConvergenceRates](OperatorsFixedPoints/ConvergenceRates.lean) | 7 | Rates of convergence (p. 46), Example 2.1.5, Ex 2.1.7 (error ratio → `|T'(u*)|`); the Newton map (2.2) and its fixed points |
| [PartialOrders](OperatorsFixedPoints/PartialOrders.lean) | 29 | Partial orders, Examples 2.2.1–2.2.5, Ex 2.2.1–2.2.17; `|Bu| ≤ B|u|`, `uₖ ≤ Aᵏu₀`, `A ≫ 0 ⇒ Au ≪ Av` (Ex 2.2.7–2.2.8) |
| [PointwiseOrder](OperatorsFixedPoints/PointwiseOrder.lean) | 29 | Suprema and infima in `ℝ^X`, sublattices, Examples 2.2.6–2.2.7, Ex 2.2.18–2.2.24; Lemma 2.2.1, (2.3), Lemma 2.2.2, Lemma 2.2.3 (upper envelope of contractions) |
| [OrderPreserving](OperatorsFixedPoints/OrderPreserving.lean) | 19 | Order-preserving maps, Examples 2.2.8–2.2.10, Ex 2.2.25–2.2.32, Lemma 2.2.4 (Blackwell) |
| [StochasticDominance](OperatorsFixedPoints/StochasticDominance.lean) | 17 | (2.9), Example 2.2.11, Ex 2.2.33–2.2.35, Lemma 2.2.5 (both directions), Lemma 2.2.6 |
| [ParametricMonotonicity](OperatorsFixedPoints/ParametricMonotonicity.lean) | 11 | Dominance, Example 2.2.12, Ex 2.2.36–2.2.37, Prop 2.2.7, Ex 2.2.38 (Solow–Swan), Ex 2.2.39 (continuation value) |
| [SpectralRadius](OperatorsFixedPoints/SpectralRadius.lean) | 27 | Spectral radius (1.15), Gelfand's formula, the Neumann series, `ρ(Aᵀ) = ρ(A)`, Ex 2.2.28 second half (`0 ≤ A ≤ B ⇒ ρ(A) ≤ ρ(B)`), row-sum norm facts |
| [LinearOperators](OperatorsFixedPoints/LinearOperators.lean) | 13 | Thm 2.3.4, Lemma 2.3.5, kernel (2.16) and product-space (2.17) operators, positive operators (2.18), Example 2.3.1, Lemma 2.3.6, Markov operators, (2.19), Ex 2.3.8–2.3.14 |
| [Resolvent](OperatorsFixedPoints/Resolvent.lean) | 11 | The resolvent series `∑ z^{−(k+1)}Mᵏ` entrywise: telescoping, summability, two-sided inverse of `zI − M`, nonnegativity for `A ≥ 0` |
| [PerronFrobenius](OperatorsFixedPoints/PerronFrobenius.lean) | 10 | Thm 2.3.1 for `A ≥ 0`: maximal-modulus eigenvalue, resolvent domination, unboundedness near `ρ(A)`, compactness of the simplex, right and left eigenvectors |
| [NonnegativeMatrices](OperatorsFixedPoints/NonnegativeMatrices.lean) | 12 | Lemma 2.3.2 (Ex 2.3.1), Lemma 2.3.3 (local spectral radius), Markov matrices: Ex 2.3.2 (i)–(iii), Ex 2.3.3 |
| [LakeModel](OperatorsFixedPoints/LakeModel.lean) | 12 | (2.13), Ex 2.3.4–2.3.7, (2.14) and its uniqueness |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
