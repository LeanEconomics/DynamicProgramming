# SLP Chapter 4: Dynamic Programming under Certainty, in Lean

This is the `RecursiveMethods/DeterministicDP` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 4 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 4 connects the sequence problem `sup Σ βᵗF(x_t, x_{t+1})` with the functional equation
`v(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]`. It then studies the functional equation for bounded,
constant-returns and unbounded return functions, and finishes with Euler equations. Every
numbered result (Lemma 4.1, Theorems 4.2–4.15) and every exercise (4.1–4.9) is formalised here.
The open-ended Exercise 4.8c–d is answered with theorems that give sufficient conditions. The
library contains **212 theorems**.

* **The Principle of Optimality** (§4.1): values lie in the extended reals (`EReal`), as in the
  book.
  * The supremum function satisfies the functional equation (`theorem_4_2`).
  * A solution with `βⁿv(xₙ) → 0` is the supremum function (`theorem_4_3`, with Exercise 4.3).
  * Optimal plans satisfy `v*(x_t) = F(x_t, x_{t+1}) + βv*(x_{t+1})` (`theorem_4_4`), and plans
    that satisfy it with `limsup βᵗv*(x_t) ≤ 0` are optimal (`theorem_4_5`).
  * Sufficient conditions for the sequence problem to be well defined, and Exercises 4.1–4.2.
  * The book's two consumption examples: an extraneous solution of (FE), and a plan satisfying
    (9) that is not optimal.
* **Bounded returns** (§4.2): the operator `T` on bounded continuous functions.
  * `T` has a unique fixed point, which equals `v*`, and its policy correspondence generates
    optimal plans (`theorem_4_6`, `fixedPoint_eq_vstar`, `policy_plan_optimal`).
  * Monotonicity of `v` (`theorem_4_7`), and strict concavity of `v` with a continuous policy
    function (`theorem_4_8`).
  * Convergence of the approximate policy functions (`theorem_4_9`) and policy iteration
    (Exercise 4.4).
  * Benveniste–Scheinkman (`theorem_4_10`), differentiability of `v` (`theorem_4_11`) and the
    slope of the savings policy (Exercise 4.5).
* **Constant returns to scale** (§4.3): the space `H(X)` of homogeneous functions is complete
  (Exercise 4.7a).
  * Blackwell's conditions for homogeneous functions (`theorem_4_12`), and the fixed point,
    homogeneous policy and `v = v*` (`theorem_4_13`, Exercise 4.6).
  * Homogeneous quasi-concave functions (Exercise 4.8), including a counterexample to 4.8a as
    printed.
* **Unbounded returns** (§4.4): iterating `T` down from an upper bound (`theorem_4_14`).
  * The unit-elastic growth model: `Tⁿv̂` in closed form, `v*`, and optimality of `αβk^α`.
  * The quadratic investment model: the recursions (6)–(8), their limits, `v*`, and the optimal
    linear policy.
* **Euler equations** (§4.5): the Euler and transversality conditions are sufficient
  (`theorem_4_15`).
  * Exercise 4.9 for both models. Theorem 4.15 itself does not cover the quadratic model, so a
    general sufficiency result (`euler_sufficient`) is used there.

All names are in the namespace `StokeyLucasPrescott.DeterministicDP`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

The modules `Contraction`, `Correspondences`, `Maximum` and `InteriorPoints` carry over results
of Chapter 3 (`RecursiveMethods/MathematicalPreliminaries`), so that the project is
self-contained. `Maximum` generalises Lemma 3.7 and Theorem 3.8 from strictly concave objectives
to objectives with a unique maximizer.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [ExtendedReals](DeterministicDP/ExtendedReals.lean) | 9 | Suprema and limits in `R̄`; the book's three-case description of a supremum |
| [Principle](DeterministicDP/Principle.lean) | 20 | §4.1: Lemma 4.1, Theorems 4.2–4.5, Exercise 4.3, `G*` |
| [Assumption42](DeterministicDP/Assumption42.lean) | 13 | p. 69: when Assumption 4.2 holds; Exercises 4.1–4.2 |
| [ConsumptionExamples](DeterministicDP/ConsumptionExamples.lean) | 15 | pp. 74–77: why (8) and (11) are needed |
| [Contraction](DeterministicDP/Contraction.lean) | 8 | Theorem 3.2 and corollaries (from Chapter 3) |
| [Correspondences](DeterministicDP/Correspondences.lean) | 2 | Hemi-continuity (from Chapter 3) |
| [Maximum](DeterministicDP/Maximum.lean) | 14 | Theorem 3.6; Lemma 3.7 and Theorem 3.8 for unique maximizers |
| [BoundedReturns](DeterministicDP/BoundedReturns.lean) | 15 | Assumptions 4.3–4.6, Theorems 4.6–4.7, `v = v*` |
| [Concavity](DeterministicDP/Concavity.lean) | 7 | Assumptions 4.7–4.8, Theorems 4.8–4.9 |
| [PolicyIteration](DeterministicDP/PolicyIteration.lean) | 15 | Exercise 4.4 |
| [Envelope](DeterministicDP/Envelope.lean) | 2 | Theorem 4.10 (Benveniste–Scheinkman), Exercise 4.5 |
| [InteriorPoints](DeterministicDP/InteriorPoints.lean) | 3 | Interior points of convex-valued l.h.c. correspondences (from Chapter 3) |
| [ValueDifferentiability](DeterministicDP/ValueDifferentiability.lean) | 6 | Theorem 4.11 |
| [ConstantReturns](DeterministicDP/ConstantReturns.lean) | 10 | `H(X)`, Exercise 4.7a, Theorem 4.12 |
| [ConstantReturnsDP](DeterministicDP/ConstantReturnsDP.lean) | 16 | Assumptions 4.10–4.11, Exercises 4.6–4.7b, Theorem 4.13 |
| [QuasiConcavity](DeterministicDP/QuasiConcavity.lean) | 4 | Exercise 4.8a–b |
| [CRSConcavity](DeterministicDP/CRSConcavity.lean) | 3 | Exercise 4.8c–d |
| [UnboundedReturns](DeterministicDP/UnboundedReturns.lean) | 5 | Theorem 4.14 |
| [LogGrowth](DeterministicDP/LogGrowth.lean) | 13 | pp. 93–95: the unit-elastic growth model |
| [QuadraticInvestment](DeterministicDP/QuadraticInvestment.lean) | 14 | pp. 95–97: the quadratic investment model |
| [EulerEquations](DeterministicDP/EulerEquations.lean) | 7 | §4.5: Theorem 4.15; the envelope route to the Euler equations |
| [EulerExamples](DeterministicDP/EulerExamples.lean) | 11 | Exercise 4.9 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
