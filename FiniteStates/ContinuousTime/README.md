# Continuous time in Lean

This is the `FiniteStates/ContinuousTime/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/ContinuousTime`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 10, "Continuous Time" (pp. 308–341), including
every provable exercise (Exercises 10.1.1–10.1.20 and 10.2.1–10.2.3). The library
contains **269 theorems** and audits every declaration, including structure
constructors and projections.

* **Exponentials** (§10.1.1): the scalar IVP `u̇ = ru` with existence and uniqueness
  (Example 10.1.1); the memoryless property of `Exp(θ)` (Exercise 10.1.1) and its converse,
  Lemma 10.1.1, by Cauchy's functional equation for a monotone function; the matrix
  exponential with Lemma 10.1.2 (i)–(vii) and Exercises 10.1.2–10.1.6. Lemma 10.1.2 (iv)
  holds in the forward direction; the converse is false, and the library proves
  counterexamples, one of them a real `2 × 2` matrix.
* **Flows** (§10.1.2): the semigroup property; **Proposition 10.1.3** with uniqueness of
  the solution of `u̇ = Au`, its row-vector form (Exercise 10.1.7), `e^{tD}` for diagonal
  `D` (Exercise 10.1.8) and (10.15).
* **Spectral bound** (§10.1.2.4): the spectral mapping theorem `σ(e^A) = e^{σ(A)}`, proved
  through invariant eigenspaces; `s(A)`, **Lemma 10.1.4** (`e^{s(A)} = ρ(e^A)`,
  `τs(A) = s(τA)`, `s(A) = lim (1/k) ln ‖e^{kA}‖`, Exercises 10.1.9–10.1.11) and
  **Theorem 10.1.5** in full, all four statements equivalent, for every square matrix
  (Exercise 10.1.12 included). The book cites Engel and Nagel for the proof.
* **Semigroups** (§10.1.2.5): `C₀`-semigroups, Example 10.1.3 and **Proposition 10.1.6**
  (every `C₀`-semigroup on `ℝ^X` is `e^{tA}`, with `A` the derivative at zero), proved by
  the integral-of-the-semigroup argument, where the book cites Engel and Nagel.
* **Markov semigroups** (§10.1.3): intensity matrices (Example 10.1.4), Exercises
  10.1.13–10.1.19, **Proposition 10.1.7** (`Q` is an intensity matrix iff `(e^{tQ})` is
  Markov iff it preserves distributions), Chapman–Kolmogorov, the backward and forward
  equations and **Proposition 10.1.8**.
* **Jump chains** (§10.1.4): the intensity matrix `λ(Π − I)` (10.31) and its inverse
  construction (§10.1.4.4); **Lemma 10.1.11** and the analytic part of
  **Proposition 10.1.9** (a continuous solution of the integrated backward equation is
  `e^{tQ}`); the inventory jump matrix (Exercise 10.1.20).
* **Valuation** (§10.2.1): **Proposition 10.2.1** (lifetime value `∫₀^∞ e^{tA}h dt` is
  finite, satisfies (10.39), equals `−A⁻¹h`, `A⁻¹ ≤ 0`, and `h + (I + A)w` is order stable),
  Exercise 10.2.1 and **Proposition 10.2.3** (constant discounting: `s(Q − δI) = −δ`,
  `(δI − Q)⁻¹ ≥ 0` and `v = (δI − Q)⁻¹h`).
* **Continuous-time MDPs** (§10.2.2–§10.2.4): `C = (Γ, δ, r, Q)`, the `σ`-value functions
  (10.48)–(10.49), policy operators (10.51) forming an order stable ADP, Exercise 10.2.2,
  the Bellman operator (10.53), **Theorem 10.2.4** (the value function is the unique
  solution of the HJB equation (10.52), Bellman's principle of optimality, an optimal
  policy exists, and continuous-time HPI stops at an optimal policy), and job search with
  Exercise 10.2.3.

The main entry points are `eq_exp_of_memoryless`, `ivp_unique`, `spectrum_complexify_exp`,
`stability_tfae`, `IsC0Semigroup.exists_eq_exp`, `intensity_tfae`, `eq_exp_of_backward`,
`eq_exp_of_integrated`, `orderStable_valuation`, `constant_discounting`,
`CTMDP.optimality` and `jobSearch_optimality`, all in the namespace
`SargentStachurski.ContinuousTime`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records the converse of
Lemma 10.1.2 (iv) that fails, the hypotheses the book leaves implicit and what is not
formalised (the probabilistic construction of continuous-time Markov chains).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](ContinuousTime/Basics.lean) | 18 | Markov matrices, contractions and Banach's theorem, Prop 2.2.7, Blackwell's condition, Lemma 2.2.2 (restated) |
| [SpectralRadius](ContinuousTime/SpectralRadius.lean) | 29 | `ρ(A)`, Gelfand's formula, the Neumann series, Ex 2.2.28 (restated) |
| [Resolvent](ContinuousTime/Resolvent.lean) | 11 | The resolvent series (restated) |
| [PerronFrobenius](ContinuousTime/PerronFrobenius.lean) | 20 | Thm 2.3.1, nonnegative case (restated) |
| [Irreducible](ContinuousTime/Irreducible.lean) | 10 | Thm 2.3.1, irreducible case (restated) |
| [LinearValuation](ContinuousTime/LinearValuation.lean) | 25 | Thm 6.1.1, `ρ(βP) = β`, Thm 6.1.5, Example 6.1.2, Prop 6.1.6 (restated) |
| [OrderFixedPoints](ContinuousTime/OrderFixedPoints.lean) | 15 | Global stability on a set, conjugacy, Thm 7.1.1, Thm 7.1.3 (restated) |
| [OrderStability](ContinuousTime/OrderStability.lean) | 5 | §9.1.1, Ex 9.1.1, Lemmas 9.1.1–9.1.2 (restated) |
| [ADP](ContinuousTime/ADP.lean) | 22 | ADPs, Props 9.2.1, 9.2.5, Thm 9.2.4 (restated) |
| [Exponential](ContinuousTime/Exponential.lean) | 22 | §10.1.1, Example 10.1.1, Lemmas 10.1.1–10.1.2, Ex 10.1.1–10.1.6 |
| [Flows](ContinuousTime/Flows.lean) | 11 | §10.1.2.1–10.1.2.3, Prop 10.1.3, Ex 10.1.7–10.1.8, (10.15) |
| [SpectralBound](ContinuousTime/SpectralBound.lean) | 15 | §10.1.2.4, spectral mapping, Lemma 10.1.2 (iv) converse refuted, Lemma 10.1.4, Thm 10.1.5, Ex 10.1.9–10.1.12 |
| [Semigroups](ContinuousTime/Semigroups.lean) | 10 | §10.1.2.5, Example 10.1.3, Prop 10.1.6 |
| [MarkovSemigroups](ContinuousTime/MarkovSemigroups.lean) | 16 | §10.1.3, Example 10.1.4, Props 10.1.7–10.1.8, Ex 10.1.13–10.1.19 |
| [JumpChains](ContinuousTime/JumpChains.lean) | 7 | §10.1.4, (10.31), Lemma 10.1.11, Prop 10.1.9 (analytic part), Ex 10.1.20 |
| [Valuation](ContinuousTime/Valuation.lean) | 12 | §10.2.1, Props 10.2.1 and 10.2.3, Ex 10.2.1 |
| [CTMDP](ContinuousTime/CTMDP.lean) | 21 | §10.2.2–10.2.4, Thm 10.2.4, Ex 10.2.2–10.2.3 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
