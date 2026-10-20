# SLP Chapter 18: Equilibria in Systems with Distortions, in Lean

This is the `RecursiveMethods/EquilibriaWithDistortions` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It covers
Chapter 18 of Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (1989). Run
the commands below from this directory. [Return to the library index](../../README.md).

Chapter 18 studies a one-sector growth model with a flat tax `θ` on capital income, in which the
competitive equilibrium is not Pareto optimal. It gives three methods. If the tax proceeds are
rebated, the equilibrium solves the planning problem of a pseudo-economy with discount factor
`(1 − θ)β`, and Chapter 4 applies (§18.1). If they are thrown away, the Euler equation
`U′[ψ(k) − g(k)] = β(1 − θ) f′[g(k)] U′{ψ[g(k)] − g[g(k)]}`, with `ψ(k) = f(k) − θ k f′(k)`, is
attacked directly: near the steady state `k*` by the Contraction Mapping Theorem (§18.2), and on
all of `[0, k̄]` by Schauder's theorem and the monotone iteration of Theorem 17.7 (§18.3), with a
short extension to Markov shocks.

Every numbered result, assumption and exercise is formalised: Assumptions 18.1–18.2, Propositions
18.1–18.5 and Exercises 18.1–18.9. Several claims are false as stated. Each is refuted in Lean, by
a counterexample or a proof of inconsistency, and a corrected statement is proved: Assumptions 18.1
and 18.2 contradict each other; the sign claims that locate `λ*` (p. 549) fail for an economy
satisfying Assumption 18.1; Exercise 18.4a (`T` is not monotone on `D_λ(I_ε)`) and Exercise 18.4b
(its starting points are not in `D_λ(I_ε)`); Exercise 18.5 (the equation (7) need not have a
solution); the maximal element `h̄` of p. 558 (it is not in `F`); Exercise 18.8 (the stochastic
operator is not well defined); and the claim that Schauder's theorem gives a stochastic equilibrium
(it gives the degenerate fixed point `ψ`). Two printed proof steps and several steps of the
solutions manual are also wrong; the results they support are true and are proved. The book's
appeal to Schauder for a stochastic equilibrium is replaced by monotone iteration with a planner's
consumption floor, which gives an equilibrium with positive consumption for any technologies,
with finitely many shocks and with a continuum (Exercise 18.9). The bibliographic notes (§18.4)
are not formalised. See [corrections](docs/corrections.md). The library contains **718 theorems**.
Of these, 680 are in the Chapter 18 modules and 38 in the fixed-point theorems carried
from Chapter 17.

* **The indirect approach** (§18.1). Sufficiency of the Euler equation and the transversality
  condition for the individual's concave problem with time-varying prices (a non-stationary
  Theorem 4.15), and uniqueness of the optimum. Exercise 18.1 as a sequence problem and for the
  bounded solution of the functional equation (2), which exists and is unique by a contraction on
  `ℓ∞`. The budget with a rebated tax and (3); the pseudo-economy (8)–(10) solves (6)–(7) and gives
  an equilibrium once the individual's transversality condition holds. The planner's `v`, `g` and
  the pseudo-planner's `w`, `ĥ` are constructed for bounded `U`, are unique, and are proved
  interior on `(0, k̄]` when `U′(0+) = ∞` and `f(0) = 0`, and on `K` under a slope condition at `0`; the first-order and envelope conditions (4)–(7) are derived
  from (3). Exercise 18.2, with the condition `α + θ < 1` and both readings of the two taxes.
* **The local approach: set-up** (§18.2). Assumption 18.1 and its consequences; the unique `k*`
  of (5); Proposition 18.1, by Brouwer's theorem; `F` of (3) and its partial derivatives
  (6a)–(6c); the characteristic polynomial `P` with roots `λ* ∈ (0, 1)` and `λ₂ > 1`, under the
  added hypotheses `U″(c*) < 0` and `f″(k*) < 0`. A concrete economy, `f(k) = 9 − 8e^{−k}`,
  satisfies all of them.
* **The implicit function `H`** (§18.2 (7)). A solution of `F[x, H(x, z), z] = 0` near
  `(k*, k*)` with the Lipschitz bounds the proofs need, built with the intermediate value theorem;
  it is `C¹` with `H₁* = −F₁*/F₂*`, `H₂* = −F₃*/F₂*`, by Mathlib's implicit function theorem.
* **The local contraction** (§18.2). Propositions 18.2–18.4, Exercise 18.3, the Schauder route of
  p. 551, Exercise 18.4 in a corrected form, local stability `|gᵗ(k) − k*| ≤ λᵗ |k − k*|`, and the slope `g′(k*) = λ*` of
  the local equilibrium, proved without assuming that `g` is differentiable.
* **The global approach** (§18.3). Assumption 18.2 in a consistent reading; the set `F` of (2)–(6)
  and Proposition 18.5; its least element `h_` and its greatest element, which is not the book's
  `h̄`; the operator `T` of (7), defined as the crossing point of the two sides of the Euler
  equation; Exercises 18.5–18.7; existence of an equilibrium by Schauder's theorem; the least and
  greatest equilibria by Theorem 17.7 and its Corollary. Concrete models with `U(c) = √c` refute
  the solvability of (7) and the Lipschitz bound in the proof of Proposition 18.5.
* **Shocks** (§18.3, pp. 558–560). Finitely many shocks: Exercise 18.8 refuted and corrected
  (Kuhn–Tucker form; equation form under a cross-state condition); `T` monotone and continuous
  with `T(F)` equicontinuous; the least fixed point, and the greatest fixed point `ψ`, which has
  zero consumption; a non-degenerate equilibrium for any technologies, from the consumption of an
  auxiliary planner. Exercise 18.9: a compact metric shock space with a Feller transition, on
  which `T` is well defined and monotone, and has a least fixed point with consumption bounded
  away from zero (continuous in the shock under the strong Feller property).

All names are in the namespace `StokeyLucasPrescott.EquilibriaWithDistortions`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [IndirectApproach](EquilibriaWithDistortions/IndirectApproach.lean) | 23 | Euler + transversality sufficiency, Exercise 18.1, (3), (6)–(10), Exercise 18.2 |
| [IndirectDP](EquilibriaWithDistortions/IndirectDP.lean) | 8 | The functional equations (2)–(3), bounded case; Exercise 18.1 literally |
| [IndirectBellman](EquilibriaWithDistortions/IndirectBellman.lean) | 9 | Existence of the bounded solution of (2)–(3); the planner's problem (1) |
| [IndirectEnvelope](EquilibriaWithDistortions/IndirectEnvelope.lean) | 10 | First-order and envelope conditions (4)–(7) from (3) |
| [IndirectExistence](EquilibriaWithDistortions/IndirectExistence.lean) | 27 | Existence of `v` and `g` in (1): value, policy, (9)–(10), Euler equation |
| [IndirectExistenceEquilibrium](EquilibriaWithDistortions/IndirectExistenceEquilibrium.lean) | 4 | Exercise 18.1 and the equilibrium (8)–(10) with constructed policies |
| [IndirectInteriorDP](EquilibriaWithDistortions/IndirectInteriorDP.lean) | 6 | (2)–(3) and the planner's problem with `U′` used only along the path |
| [IndirectInterior](EquilibriaWithDistortions/IndirectInterior.lean) | 14 | Interior policies under `U′(0+) = ∞`, `f(0) = 0`; Exercise 18.1 and (8)–(10) without interiority |
| [IndirectInteriorExample](EquilibriaWithDistortions/IndirectInteriorExample.lean) | 13 | `U = 1 − e^{−√c}`, `f = √k`: an economy satisfying them |
| [IndirectInteriorGeneral](EquilibriaWithDistortions/IndirectInteriorGeneral.lean) | 28 | Interiority on all of `K` (`f(0) > 0`, or `U′(0)` finite); uniqueness of (1) and (8) |
| [IndirectInteriorGeneralExample](EquilibriaWithDistortions/IndirectInteriorGeneralExample.lean) | 33 | Economies satisfying them; three counterexamples |
| [LocalApproach](EquilibriaWithDistortions/LocalApproach.lean) | 48 | Assumption 18.1, (3)–(6), Proposition 18.1, `P(λ)` and `λ*` |
| [LocalImplicit](EquilibriaWithDistortions/LocalImplicit.lean) | 13 | §18.2 (7): the local solution `H` |
| [LocalSmooth](EquilibriaWithDistortions/LocalSmooth.lean) | 21 | `H` is `C¹`; `g′(k*) = λ*` |
| [LocalContraction](EquilibriaWithDistortions/LocalContraction.lean) | 32 | (8), Propositions 18.2–18.4, Exercises 18.3–18.4 |
| [LocalSchauder](EquilibriaWithDistortions/LocalSchauder.lean) | 8 | The Schauder route of p. 551 |
| [LocalExample](EquilibriaWithDistortions/LocalExample.lean) | 14 | An economy satisfying Assumption 18.1; two counterexamples in it |
| [GlobalApproach](EquilibriaWithDistortions/GlobalApproach.lean) | 71 | Assumption 18.2, `F`, Proposition 18.5, least and greatest elements |
| [GlobalCrossing](EquilibriaWithDistortions/GlobalCrossing.lean) | 19 | The crossing point behind (7) and (9) |
| [GlobalOperator](EquilibriaWithDistortions/GlobalOperator.lean) | 30 | (7), Exercises 18.5–18.7, existence, least and greatest equilibria |
| [GlobalExamples](EquilibriaWithDistortions/GlobalExamples.lean) | 30 | Models with `U = √`; counterexamples to Exercise 18.5 and Proposition 18.5's proof |
| [GlobalStochastic](EquilibriaWithDistortions/GlobalStochastic.lean) | 22 | (8)–(9), Exercise 18.8 |
| [GlobalStochasticEquilibrium](EquilibriaWithDistortions/GlobalStochasticEquilibrium.lean) | 20 | Continuity, equicontinuity, least fixed point, non-degenerate equilibria |
| [GlobalStochasticNondegenerate](EquilibriaWithDistortions/GlobalStochasticNondegenerate.lean) | 52 | A non-degenerate stochastic equilibrium for any technologies (planner's floor) |
| [GlobalContinuum](EquilibriaWithDistortions/GlobalContinuum.lean) | 14 | Exercise 18.9 |
| [GlobalContinuumFixed](EquilibriaWithDistortions/GlobalContinuumFixed.lean) | 52 | Exercise 18.9: monotone iteration, the least fixed point given a consumption floor |
| [GlobalContinuumFloor](EquilibriaWithDistortions/GlobalContinuumFloor.lean) | 59 | Exercise 18.9: the floor for any technologies; existence |

Carried from the Chapter 17 project `FixedPointArguments` (38 theorems), identical except for the
namespace:

* `BrouwerRetraction`, `BrouwerBall`, `Brouwer` (13): Theorem 17.3 (Brouwer), used in
  Proposition 18.1.
* `Schauder`, `SchauderBoundedContinuous` (7): Theorem 17.4 (Schauder), used for the Schauder route
  of p. 551 and for the existence of an equilibrium in §18.3.
* `MonotoneOperators` (18): Lemma 17.6, Theorem 17.7 and its Corollary, used for the least and
  greatest equilibria in §18.3.

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits
each named declaration's axioms: only `propext`, `Classical.choice` and `Quot.sound` are allowed.
Warnings fail the check.
