# Miao Chapter 1: Deterministic Difference Equations, in Lean

This is the `EconomicDynamics/DifferenceEquations` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 1 of Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), cited by the
pages of the author's draft of 21 April 2013. Run the commands below from this directory.
[Return to the library index](../../README.md).

Chapter 1 solves deterministic linear difference equations: scalar first- and second-order
equations, lag operators, and first-order systems `Ax_{t+1} = Bx_t + Cz_t`, nonsingular
(Blanchard–Kahn) and singular (Klein), followed by phase diagrams and a short look at nonlinear
dynamics. Every numbered result (Theorems 1.4.1–1.4.5, Corollary 1.4.1, the assumptions and
definitions) is proved, including the generalized Schur decomposition (Theorem 1.4.4), which the
book cites without proof and which Mathlib does not have. So is every derivation in the text and
Exercises 1–2; Exercises 3–4 and §1.7 are about the Dynare software. The corrections are recorded
in [corrections](docs/corrections.md), and every book item is located in the
[source map](docs/source-map.md). The library contains **439 theorems**.

* **Scalar equations** (§1.1).
  * The general, backward and forward solutions, transversality, and bubbles (`eq_1_3`, `eq_1_4`,
    `eq_1_8`, `eq_1_9_every_solution`). The book's claim (1.5) that bounded forcing gives a limit
    when `|b| < 1` is false (`eq_1_5_counterexample`), and so is its account of `b = −1`
    (`eq_1_5_b_neg_one_counterexample`).
  * Adaptive versus rational expectations, and an announced dividend tax
    (`example_1_1_1_unique_bdd`, `example_1_1_2_decreasing`).
* **Lag operators** (§1.2): `(1 − λLⁿ)⁻¹`, `(1 − λLⁿ)⁻²` and `(I − ALⁿ)⁻¹` as the unique bounded
  inverses on two-sided sequences, for every integer `n` (`lag_inverse_geom`,
  `lag_inverse_geom_sq`, `lag_matrix_formula`).
* **Second-order equations** (§1.3): distinct, repeated and complex roots, and the saddle-path
  solution as the unique bounded solution for each `x₀` (`case1_saddle`, `case2_general`,
  `case3_general`).
* **Nonsingular systems** (§1.4.1).
  * Theorem 1.4.1 in both directions (`theorem_1_4_1`); the book asserts the converse.
  * Blanchard–Kahn (`theorem_1_4_2`) with a real block-diagonalizing `P` in place of the Jordan
    form, which exists whenever no eigenvalue lies on the unit circle (`exists_real_block_split`);
    Corollary 1.4.1 and the stable manifold (`corollary_1_4_1`, `finrank_stableArm`).
  * Theorem 1.4.3 as printed is false, since a nonsingular system always has a solution
    (`theorem_1_4_3_printed_gt_false`); its stable-solution versions are proved, with the rank
    condition the second half needs (`theorem_1_4_3_gt`, `theorem_1_4_3_lt_exists`,
    `theorem_1_4_3_lt_counterexample`).
* **Singular systems** (§1.4.2).
  * The complex generalized Schur form, with the stable pairs first, by induction on the dimension
    (`theorem_1_4_4`, `theorem_1_4_4_stable`).
  * Klein's theorem: a unique stable solution, real for real data (`theorem_1_4_5`,
    `theorem_1_4_5_real`). The printed forward solution (1.37) has `T₂₂⁻¹` in the wrong place
    (`eq_1_37`, `eq_1_37_printed_false`).
* **Phase diagrams and nonlinear systems** (§1.5–1.6).
  * The phase-diagram system has a saddle only when `(2 + a)(2 − d) > bc`
    (`phase_saddle_iff`, `phase_counterexample`).
  * The optimal-growth linearization is a saddle (`example_1_6_1_roots`); the logistic map's
    two-cycle `(5 ± √5)/8` (`logistic_two_cycle`).
* **Exercises** (§1.8): the Cagan model, with no bounded solution when money grows
  (`ex_1_1a_rho_one_bdd_iff`), and the Dornbusch model, whose discrete-time saddle needs
  `θ(2δ + (2γ + δ)/β) < 4` (`ex_1_2b_iff`), with overshooting (`ex_1_2d_overshoot`) and an
  announced money increase (`ex_1_2e_jump_shape`).

All names are in the namespace `Miao.DifferenceEquations`. Two coordinate conventions are used for
partitioned systems: the nonsingular theorems index `x = (k, y)` by a sum type `κ ⊕ υ`, the
singular ones by `Fin (n_k + n_y)`, since the QZ form is built on `Fin n`. The modules `Spectral`,
`RealSplitting` and `Dichotomy`, and the triangular-matrix lemmas in `Triangular`, are copied from
[RecursiveMethods/DeterministicDynamics](../../RecursiveMethods/DeterministicDynamics/README.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](DifferenceEquations/Basics.lean) | 3 | The system (1.20), Assumptions 1.4.1–1.4.2, Definitions 1.4.1–1.4.5 |
| [Scalar](DifferenceEquations/Scalar.lean) | 61 | §1.1: scalar first-order equations, Examples 1.1.1–1.1.2 |
| [LagOperators](DifferenceEquations/LagOperators.lean) | 20 | §1.2: the lag operator and the scalar expansions |
| [SecondOrder](DifferenceEquations/SecondOrder.lean) | 36 | §1.3: second-order equations, the three cases, (1.19) |
| [Triangular](DifferenceEquations/Triangular.lean) | 14 | Powers of triangular matrices (copied and extended) |
| [Spectral](DifferenceEquations/Spectral.lean) | 16 | Stable and unstable subspaces (copied) |
| [RealSplitting](DifferenceEquations/RealSplitting.lean) | 24 | The real splitting `E_s ⊕ E_u` and its dimension (copied) |
| [Dichotomy](DifferenceEquations/Dichotomy.lean) | 16 | Projections and geometric bounds (copied) |
| [LinearSystems](DifferenceEquations/LinearSystems.lean) | 28 | §1.4: stable matrices, regularity, the steady state (1.21) |
| [LagMatrix](DifferenceEquations/LagMatrix.lean) | 4 | §1.2: `(I − ALⁿ)⁻¹ = Σ AʲL^{nj}` |
| [BlockSplit](DifferenceEquations/BlockSplit.lean) | 9 | The real block split replacing the Jordan form, and its existence |
| [Nonsingular](DifferenceEquations/Nonsingular.lean) | 35 | §1.4.1: Theorems 1.4.1–1.4.2, Corollary 1.4.1, the stable manifold |
| [Indeterminacy](DifferenceEquations/Indeterminacy.lean) | 8 | Theorem 1.4.3, corrected, and the unit-root remark |
| [QZ](DifferenceEquations/QZ.lean) | 27 | Definition 1.4.6, Theorem 1.4.4 (generalized Schur form) |
| [Singular](DifferenceEquations/Singular.lean) | 48 | §1.4.2: Theorem 1.4.5 (Klein), the Cagan example, augmentation |
| [PhaseDiagram](DifferenceEquations/PhaseDiagram.lean) | 39 | §1.5, and a 2×2 saddle toolkit |
| [Nonlinear](DifferenceEquations/Nonlinear.lean) | 16 | §1.6: optimal growth, periodic points, the logistic map |
| [Exercises](DifferenceEquations/Exercises.lean) | 35 | §1.8: Exercises 1 (Cagan) and 2 (Dornbusch) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
