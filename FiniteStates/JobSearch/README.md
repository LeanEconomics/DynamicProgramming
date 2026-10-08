# Job search, contractions and the Bellman equation in Lean

This is the `FiniteStates/JobSearch/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/JobSearch` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 1, "Introduction" (pp. 1–41), including
every provable exercise (Exercises 1.1.2–1.3.3; 1.1.1 is a discussion question).
The library contains **201 theorems** and audits **279 declarations**, including
structure constructors and projections.

* **Banach's fixed-point theorem** (Theorem 1.2.3) is proved along the book's own
  route through Exercises 1.2.19 and 1.2.21–1.2.23, for a contraction on a
  nonempty closed subset of any complete normed group, with the rate (1.18) and
  global stability; Exercise 1.2.24 (damped iteration) and the `ℝ^X` restatement
  of p. 31 follow.
* **The Neumann series lemma** (Theorem 1.2.1): `ρ(A) < 1` implies `I − A` is
  invertible with inverse `∑ₖ Aᵏ`. The spectral radius is Mathlib's, on the
  complexification, and `mem_spectrum_iff_eigenpair` shows it is the book's
  `max{|λ|}` over eigenvalues. Lemma 1.2.2 (`ρ(B)ᵏ ≤ ‖Bᵏ‖` and Gelfand's formula),
  which the book quotes from Bollobás, is proved from Mathlib's Gelfand formula;
  Exercises 1.2.10–1.2.14, 1.2.17 (the affine map is globally stable) and 1.2.20.
* **Solow–Swan** (Exercises 1.2.25–1.2.26): the map `g(k) = sAkᵅ + (1 − δ)k` is
  not a contraction on `(0, ∞)` for any modulus, yet is globally stable with
  fixed point `k* = (sA/δ)^{1/(1−α)}`, by monotone convergence.
* **Finite-horizon job search** for every horizon (Exercise 1.1.3): the value with
  `j` periods remaining is the larger of stopping and continuing, the worker
  accepts iff the offer is at least the reservation wage, and the reservation wage
  rises with unemployment compensation at every horizon (p. 7).
* **The Bellman operator** `T` is a contraction of modulus `β` (Proposition 1.3.1),
  so `v*` exists and is the unique solution of the Bellman equation (1.25) in all
  of `ℝ^W`, value function iteration converges at rate `βᵏ`, and the `v*`-greedy
  policy is `1{w ≥ w*}` with `w* = (1 − β)h*`, (1.30). The scalar map `g` of
  (1.33) is a contraction with unique fixed point `h*` (Exercise 1.3.2), and `h*`
  and `w*` are increasing in `c`.
* **The function space** `ℝ^X`: Lemma 1.2.4 as a norm-preserving linear
  equivalence, maximising a linear functional over the simplex (Exercise 1.2.27),
  CDFs and quantiles on a finite subset of the line with Example 1.2.5 and the
  shift rule of Exercise 1.2.28.

The main entry points are `IsContractionOn.banach`, `neumann_series`,
`Solow.globallyStable_g`, `Model.value_succ_eq_stopValue_iff`,
`Model.isContractionOn_T`, `Model.bellman_equation`, `Model.tendsto_iterate_T`,
`Model.isGreedy_vstar_iff`, `Model.tendsto_iterate_g` and
`Model.hstar_le_hstar_of_c_le`, all in the namespace `SargentStachurski.JobSearch`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (most notably, Exercise 1.2.18 needs the
invariant set nonempty), the hypotheses the book leaves implicit, and what is
not formalised. The principle of optimality for the infinite-horizon problem,
which the book states on p. 12 and proves only in later chapters, is not claimed.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Lattice](JobSearch/Lattice.lean) | 11 | `a ∨ b`, `a ∧ b`, `|a|`; Ex 1.2.1; the bound (1.28) and Ex 1.3.1; pointwise operations (1.20)–(1.21) |
| [FixedPoints](JobSearch/FixedPoints.lean) | 9 | Fixed points, global stability (p. 22), Examples 1.2.3–1.2.4, Ex 1.2.15, 1.2.16, 1.2.18 (with the missing nonemptiness hypothesis) |
| [Contractions](JobSearch/Contractions.lean) | 18 | Contractions (1.17); Ex 1.2.19, 1.2.21–1.2.23; Theorem 1.2.3 (Banach) with the rate (1.18) and global stability; Ex 1.2.24 damped iteration; the `ℝ^X` restatement (p. 31) |
| [Norms](JobSearch/Norms.lean) | 15 | Norm axioms (p. 13); ℓ¹, weighted ℓ¹, sup norms are norms (Ex 1.2.2–1.2.4); ℓ⁰ is not (Ex 1.2.5); equivalence of norms (1.11), Ex 1.2.6–1.2.8; operator norm (1.12) submultiplicative, entrywise norm (1.13) not (Ex 1.2.9) |
| [NeumannSeries](JobSearch/NeumannSeries.lean) | 34 | Spectral radius (1.15) and eigenvalues; Lemma 1.2.2 (Gelfand); Theorem 1.2.1; Ex 1.2.10–1.2.14; the affine map `Au + b`: Example 1.2.2, Ex 1.2.17 (formula (1.16), global stability), Ex 1.2.20; the scalar case (1.14) |
| [SuccessiveApproximation](JobSearch/SuccessiveApproximation.lean) | 23 | Successive approximation (p. 24); Solow–Swan (1.19): Ex 1.2.25 (not a contraction), Ex 1.2.26 (`k*`, monotone bracketing, global stability) |
| [FunctionSpace](JobSearch/FunctionSpace.lean) | 22 | Lemma 1.2.4 (`ℝ^X ≃ ℝⁿ`, norm preserving); distributions, expectations, Ex 1.2.27; CDF, quantile (1.24), Example 1.2.5, Ex 1.2.28 |
| [Model](JobSearch/Model.lean) | 10 | The McCall model (Assumption 1.1.1); the expectation `E h = ∑ h(w) φ(w)`: constants, monotone, additive, 1-Lipschitz in the sup norm |
| [FiniteHorizon](JobSearch/FiniteHorizon.lean) | 21 | Backward induction for every horizon: (1.2)–(1.5), reservation wages (1.4) and Ex 1.1.2, Ex 1.1.3, accept iff `w ≥ w*ⱼ`, reservation wage increasing in `c` (p. 7) |
| [BellmanOperator](JobSearch/BellmanOperator.lean) | 22 | (1.7); Bellman operator (1.27); Prop 1.3.1; `v*` exists and is unique, Bellman equation (1.25); VFI converges at rate `βᵏ` (§1.3.2.1); `h*` (1.26); greedy policies (1.29); reservation wage (1.30) |
| [ContinuationValue](JobSearch/ContinuationValue.lean) | 16 | The map `g` (1.33); `h*` solves (1.32); Ex 1.3.2 (`g` a contraction, unique fixed point, iterates converge); Ex 1.3.3; (1.34); `h*` and `w*` increasing in `c` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
