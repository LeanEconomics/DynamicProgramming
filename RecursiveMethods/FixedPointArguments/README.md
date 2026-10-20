# SLP Chapter 17: Fixed-Point Arguments, in Lean

This is the `RecursiveMethods/FixedPointArguments` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 17 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 17 studies systems in which each agent optimises but the system as a whole does not, so
that equilibria cannot be found from a planner's problem. Its example is an overlapping-generations
economy with fiat money and Markov productivity shocks. A stationary equilibrium with valued money
corresponds to a strictly positive fixed point of `(Tf)(x) = ∫ φ[x′ ζ⁻¹(f(x′))] π(x, dx′)`, where
`ζ(l) = l H′(l)` and `φ(y) = y V′(y)`. The chapter applies four fixed-point results to this
operator in turn: the Contraction Mapping Theorem, in logarithms (§17.2); Brouwer's theorem, with
finitely many states (§17.3); Schauder's theorem (§17.4); and monotone iteration (§17.5). §17.6
repeats the four for Lucas's (1972) islands model, in which the young see the real and monetary
shocks only through the price.

Every numbered result, assumption and exercise is formalised: Lemmas 17.1, 17.2, 17.5 and 17.6,
Theorems 17.3, 17.4 and 17.7 with its Corollary, Assumptions 17.1–17.6, Propositions 1–8 and
Exercises 17.1–17.14. That includes the two theorems the book states without proof. Mathlib has
neither, and both are proved here from scratch. Brouwer's theorem (Theorem 17.3) follows Rogers's
analytic version of Milnor's proof: there is no C¹ retraction of the ball onto its sphere, by the
change of variables formula and a volume that is a polynomial in `t`; Stone–Weierstrass C¹
approximation then gives the continuous case on the ball, and a nearest-point retraction the case
of a compact convex set. Schauder's theorem (Theorem 17.4) is proved from Brouwer's by Schauder
projections onto finite nets, and in the book's form on `C(X)` through the half of Arzelà–Ascoli
that the proof needs, proved by hand for a totally bounded `X`. Several claims are false as stated.
Each is refuted in Lean, by a counterexample or a proof of inconsistency, and a corrected statement
is proved: Assumption 17.2 contradicts Assumption 17.1, so Propositions 2 and 6 are vacuous as
stated (both are proved under a repaired pair of assumptions); Exercises 17.2a and 17.4a (`Tf`
need not be bounded); Exercise 17.5a (continuity gives only local existence); the uniqueness claim
of Proposition 5 (the zero function is a second fixed point, also in an economy where the two
iterations meet) and the corresponding claims of Exercise 17.7 and Propositions 6 and 7;
Exercise 17.12 (the conditional law of `θ` given `z` has a density proportional to `θ`, not a
uniform one); Exercise 17.8a in part; the "only if" of Exercise 17.14a; the claims on pp. 515 and
530 that relative risk aversion is strictly positive, and on p. 541 that Assumption 17.2 is a
strengthening of Assumption 17.4; and the inference on p. 533 that an equilibrium price is a
function of `x/θ`. Proposition 8 omits Assumption 17.6; without it a step of the proof fails, and
the corrected statement adds it. Several steps of the printed proofs and of the solutions manual
are also wrong; the results they support are true and are proved. Two things are left open:
Proposition 8 under Assumption 17.5 alone, and whether a price that reveals more than `x/θ` can be
an equilibrium. The islands economy's equilibrium conditions, the chapter introduction and the
bibliographic notes (§17.7) are not formalised. See [corrections](docs/corrections.md). The
library contains **441 theorems**. Of these, 20 are in the five modules that prove the Brouwer and
Schauder theorems.

* **The overlapping-generations model** (§17.1). Assumption 17.1; Exercise 17.1 (the young agent's
  problem has a unique interior solution, characterised by its first-order condition); the
  stationary equilibrium (1)–(2) and its reduction to (3) and (4), in both directions;
  Proposition 1 for serially independent shocks; `ζ⁻¹` and the change of variable (8) to a fixed
  point of (9).
* **The contraction route** (§17.2). The operator (1) and its logarithmic version (3);
  Exercises 17.2 and 17.4, corrected to compact `X`; Lemmas 17.1 and 17.2; Exercise 17.3;
  Assumption 17.2, its inconsistency with Assumption 17.1, and a repair satisfied by
  `V(y) = y^{1−σ}/(1 − σ)`; Proposition 2 under the repair, with the uniqueness step that needs
  `ε_k → 0`.
* **Brouwer's theorem** (§17.3, Theorem 17.3). No C¹ retraction of the closed ball onto its
  sphere; C¹ approximation by Stone–Weierstrass; Brouwer for the unit ball of a finite-dimensional
  inner product space, for a compact convex set in any finite-dimensional normed space, and in the
  book's form.
* **Brouwer applied** (§17.3). Finite-state operators with a stochastic matrix; logarithms do not
  help; Proposition 3, and the zero solution it must exclude.
* **Schauder's theorem** (§17.4, Theorem 17.4). Approximate fixed points through Schauder
  projections; Schauder for compact convex sets in a normed space, and for closed convex sets with
  relatively compact image in a Banach space; total boundedness of bounded equicontinuous families
  on a totally bounded space; Theorem 17.4 for `C(X)`, `X` a bounded subset of `ℝˡ`.
* **Schauder applied** (§17.4). Exercise 17.5 (Peano-type existence, corrected, and the equation
  `x′ = √x`); the total-variation norm and Assumption 17.3; Lemma 17.5 and Exercise 17.6;
  Proposition 4; Exercise 17.7, corrected to a fixed point bounded away from zero.
* **Monotone operators** (§17.5). Lemma 17.6, Theorem 17.7 and its Corollary on any totally
  bounded state space, with the bracketing of all fixed points between the least and greatest
  ones; the general application to operators `∫ G[x, x′, f(x′)] π(x, dx′)` with `G` nondecreasing
  in `f`.
* **The OLG model by monotone iteration** (§17.5). Assumption 17.4; Proposition 5, refuted as
  stated in a concrete economy and corrected to uniqueness among fixed points bounded away from
  zero; the comparisons of Assumptions 17.2 and 17.4 on pp. 515, 530 and 541.
* **Partially observed shocks: information** (§17.6). Assumption 17.5; the density of
  `z = x/θ`; the conditional law of `θ` given `z` (Exercise 17.8, corrected); Exercise 17.10 in
  an example with uniform shocks; Assumption 17.6 and the corrected Exercise 17.12; the p. 533
  inference.
* **Partially observed shocks: fixed points** (§17.6). The operator (4) for any law of
  `(θ′, z′)`; Proposition 6 (Exercise 17.9) by contraction in logarithms; Proposition 7 by
  Schauder (Exercises 17.11 and 17.13, (6a)–(6b) and (7) with the correct weights, and a direct
  Lipschitz bound for Step 4); finite `Z` by Brouwer; monotonicity of `T`; Proposition 8 under
  Assumption 17.6 and Exercise 17.14.

All names are in the namespace `StokeyLucasPrescott.FixedPointArguments`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [OLGModel](FixedPointArguments/OLGModel.lean) | 63 | Assumption 17.1, Exercise 17.1, §17.1 (1)–(9), Proposition 1 |
| [OLGContraction](FixedPointArguments/OLGContraction.lean) | 25 | §17.2 (1), (3), Exercises 17.2 and 17.4, Lemmas 17.1–17.2 |
| [OLGProposition2](FixedPointArguments/OLGProposition2.lean) | 24 | Exercise 17.3, Assumption 17.2 and its repair, Proposition 2 |
| [BrouwerRetraction](FixedPointArguments/BrouwerRetraction.lean) | 4 | No C¹ retraction of the ball onto the sphere |
| [BrouwerBall](FixedPointArguments/BrouwerBall.lean) | 4 | C¹ approximation; Brouwer for the closed unit ball |
| [Brouwer](FixedPointArguments/Brouwer.lean) | 5 | Brouwer for compact convex sets; Theorem 17.3 |
| [BrouwerApplication](FixedPointArguments/BrouwerApplication.lean) | 31 | `ζ`, `φ`, `ζ⁻¹`, the bounds of Propositions 2–4; §17.3, Proposition 3 |
| [Schauder](FixedPointArguments/Schauder.lean) | 5 | Schauder for compact convex sets and for relatively compact images |
| [SchauderBoundedContinuous](FixedPointArguments/SchauderBoundedContinuous.lean) | 2 | Arzelà–Ascoli (one half); Theorem 17.4 |
| [SchauderAppODE](FixedPointArguments/SchauderAppODE.lean) | 10 | Exercise 17.5 |
| [SchauderApplication](FixedPointArguments/SchauderApplication.lean) | 18 | Assumption 17.3, Lemma 17.5, Exercises 17.6–17.7, Proposition 4 |
| [MonotoneOperators](FixedPointArguments/MonotoneOperators.lean) | 18 | Lemma 17.6, Theorem 17.7 and its Corollary |
| [MonotoneKernel](FixedPointArguments/MonotoneKernel.lean) | 11 | Assumption 17.3, Lemma 17.5, Exercise 17.6 for §17.5; the general application (p. 529) |
| [MonotoneOLG](FixedPointArguments/MonotoneOLG.lean) | 36 | Assumption 17.4, `ε_K` and `B`, Proposition 5 |
| [MonotoneOLGExamples](FixedPointArguments/MonotoneOLGExamples.lean) | 13 | An economy refuting Proposition 5 as stated |
| [MonotoneRRA](FixedPointArguments/MonotoneRRA.lean) | 20 | Relative risk aversion: pp. 515, 530, 541; Assumptions 17.2 and 17.4 compared |
| [ShocksModel](FixedPointArguments/ShocksModel.lean) | 52 | Assumptions 17.5–17.6, Exercises 17.8, 17.10, 17.12, p. 533 |
| [ShocksContraction](FixedPointArguments/ShocksContraction.lean) | 32 | §17.6 (4), Exercise 17.9, Proposition 6 |
| [ShocksSchauder](FixedPointArguments/ShocksSchauder.lean) | 29 | (6a)–(7), Exercises 17.11 and 17.13, Proposition 7, finite `Z` |
| [ShocksMonotone](FixedPointArguments/ShocksMonotone.lean) | 39 | Monotonicity, Exercise 17.14, Proposition 8 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
