# SLP Chapter 3: Mathematical Preliminaries, in Lean

This is the `RecursiveMethods/MathematicalPreliminaries` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 3 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 3 assembles the tools for the functional equations of dynamic programming: metric and
normed spaces, completeness, the contraction mapping theorem, Blackwell's sufficient conditions,
correspondences and the Theorem of the Maximum. Every numbered result (Theorems 3.1–3.8,
Lemma 3.7, Corollaries 1–2) and every exercise (3.1–3.16) is formalised here. The library
contains **192 theorems**.

* **Metric and normed spaces** (§3.1, Ex 3.2–3.5): the book's axioms are stated for an arbitrary
  distance function (`IsMetric`, `IsNorm`, `Converges`, `IsCauchy`, `IsCompleteFor`). The library
  covers each example space of Exercises 3.2–3.4, including the integers, the rationals,
  `ℝˡ` under three norms, `ℓ∞`, `C[a, b]` under the sup and `L¹` norms, and `ρ = f(|x − y|)` for
  concave `f`. It also covers the basic facts about limits and Cauchy sequences.
* **Completeness** (Theorem 3.1, Ex 3.6): `C(X)` is complete, proved by the book's three steps
  (`theorem_3_1`). Every space of Ex 3.6a is classified as complete or not. In particular,
  `C[a, b]` with the `L¹` norm is not complete (`not_isComplete_l1`). Closed subsets of complete
  spaces are complete (`isComplete_subset`).
* **Spaces of differentiable functions** (Ex 3.7): `C¹[a, b]` with `max |f| + max |f′|` is a
  Banach space (`ex_3_7a`), but `max |f|` alone is not complete (`ex_3_7b`). On `C^k`, the
  weighted norm `∑ αᵢ max |f⁽ⁱ⁾|` is complete when every `αᵢ > 0` (`isComplete_ckNorm`). The
  book's converse is false: on `C²[a, b]`, `max |f| + max |f″|` is complete
  (`ex_3_7c_counterexample`), by an interpolation inequality (`interpolation`).
* **The Contraction Mapping Theorem** (§3.2): Theorem 3.2 with the book's proof (`theorem_3_2`),
  Exercises 3.8–3.9, Corollary 1 and the N-stage Corollary 2. Exercise 3.10 solves
  `x′ = f(x)` by Picard iteration on `C[0, τ]` (`ex_3_10b`, `ex_3_10c`).
* **Blackwell's sufficient conditions** (Theorem 3.3): `theorem_3_3`, and the growth model's
  Bellman operator as the book's example (`bellmanOp_contraction`). The method of successive
  approximations from the chapter's introduction, including Ex 3.1, is in `Successive`.
* **Correspondences** (§3.3, Ex 3.11–3.15): lower and upper hemi-continuity, closure under
  projections, unions, intersections, composition and products, and Theorems 3.4 and 3.5. The
  intersection of convex-valued l.h.c. correspondences is l.h.c. when the interiors meet
  (`isLHC_inter_of_interior`). The library also covers continuity of the correspondences defined
  by constraints (Ex 3.13–3.14), including the production possibility set (`ex_3_13c`).
* **The Theorem of the Maximum** (Theorem 3.6): `theorem_3_6`. With convex values and strict
  concavity it also proves continuity of the maximizer, Lemma 3.7 and Theorem 3.8, the
  convergence of maximizers under uniform convergence of objectives. The three examples of
  Ex 3.16 show where `G` fails to be l.h.c.

All names are in the namespace `StokeyLucasPrescott.MathematicalPreliminaries`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [IntervalFunctions](MathematicalPreliminaries/IntervalFunctions.lean) | 13 | `C[a, b]`, the continuous extension, the `L¹` norm |
| [MetricSpaces](MathematicalPreliminaries/MetricSpaces.lean) | 12 | Metrics, convergence, Cauchy sequences; Ex 3.3, 3.5 |
| [NormedSpaces](MathematicalPreliminaries/NormedSpaces.lean) | 18 | Vector subspaces and norms; Ex 3.2, 3.4 |
| [Completeness](MathematicalPreliminaries/Completeness.lean) | 22 | Theorem 3.1; Ex 3.6 |
| [L1Incomplete](MathematicalPreliminaries/L1Incomplete.lean) | 16 | Ex 3.6a: `C[a, b]` with the `L¹` norm is not complete |
| [Contraction](MathematicalPreliminaries/Contraction.lean) | 8 | Theorem 3.2, Corollaries 1–2; Ex 3.8–3.9 |
| [Blackwell](MathematicalPreliminaries/Blackwell.lean) | 12 | Theorem 3.3; the growth model's operator |
| [Successive](MathematicalPreliminaries/Successive.lean) | 4 | Successive approximations; Ex 3.1 |
| [Correspondences](MathematicalPreliminaries/Correspondences.lean) | 18 | Hemi-continuity; Theorems 3.4–3.5; Ex 3.11, 3.12, 3.15 |
| [ConvexCorrespondences](MathematicalPreliminaries/ConvexCorrespondences.lean) | 4 | Ex 3.12d: intersections of convex-valued l.h.c. correspondences |
| [Maximum](MathematicalPreliminaries/Maximum.lean) | 15 | Theorem 3.6, Lemma 3.7, Theorem 3.8 |
| [MaximumExamples](MathematicalPreliminaries/MaximumExamples.lean) | 12 | Ex 3.16 |
| [ConstraintSets](MathematicalPreliminaries/ConstraintSets.lean) | 14 | Ex 3.13–3.14 |
| [Picard](MathematicalPreliminaries/Picard.lean) | 4 | Ex 3.10: a differential equation by contraction |
| [SmoothFunctions](MathematicalPreliminaries/SmoothFunctions.lean) | 20 | Ex 3.7: `C¹` and `C^k` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
