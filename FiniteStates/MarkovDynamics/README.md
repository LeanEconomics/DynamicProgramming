# Markov dynamics in Lean

This is the `FiniteStates/MarkovDynamics/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/MarkovDynamics` from
the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 3, "Markov Dynamics" (pp. 81–104), including
every provable exercise (Exercises 3.1.1–3.1.4, 3.1.6–3.1.7, 3.1.12, 3.2.1–3.2.6,
3.2.8, 3.3.1, 3.3.3–3.3.5). The library contains **145 theorems** and audits
every declaration, including structure constructors and projections.

* **Markov chains through their transition matrix** (§3.1.1): `Pᵏ(x, x')` is the
  total probability of the paths of length `k` from `x` to `x'`, (3.2), with the
  law of total probability of Exercise 3.1.2; marginal distributions follow
  `ψₜ = ψ₀Pᵗ`, (3.3)–(3.5); expectations are `⟨ψ₀Pᵗ, h⟩` (Exercise 3.1.4);
  Lemma 3.1.1 characterises irreducibility. The S–s inventory chain has the
  invariant state space `{0, …, S + s}` (Exercise 3.1.1), a Markov transition
  matrix built from the geometric demand distribution, and is irreducible
  (Exercise 3.1.3).
* **Global stability on `D(X)`** (§3.1.2): the day labourer's stationary
  distribution `(β, α)/(α + β)` is unique (Exercise 3.1.6) and `ψPᵗ → ψ*` in
  closed form. For any Markov matrix `P ≫ 0`, `ψ ↦ ψP` is globally stable on the
  distributions (Exercise 3.1.7), proved by Dobrushin's ℓ¹ contraction
  `‖dP‖₁ ≤ (1 − nε)‖d‖₁` rather than by Perron–Frobenius.
* **Tauchen's discretisation** (§3.1.3): rows sum to one for any distribution
  function (Exercise 3.1.12), the matrix is Markov, and it is monotone
  increasing when `ρ ≥ 0` (Exercise 3.2.2), via the counter-CDF criterion of
  Vol. 1, Lemma 2.2.5 (ii), re-proved here by Abel summation.
* **Conditional expectations** (§3.2.1): `Ph` and `Pᵏh`, Exercise 3.2.1, the law
  of iterated expectations (3.15); monotone Markov operators and their
  characterisation by invariance of the increasing functions (Exercises
  3.2.3–3.2.5).
* **Geometric sums** (§3.2.2): Lemma 3.2.1, `v = ∑ (βP)ᵗh = (I − βP)⁻¹h`, summed
  directly in the supremum norm with `I − βP` invertible because `u = βPu` forces
  `u = 0`; the firm's value with `β = 1/(1 + r)`; the value is increasing when the
  reward is increasing and `P` monotone (Exercise 3.2.6); the CRRA consumption
  value on a Tauchen chain is increasing in the state (Exercise 3.2.8).
* **Job search with Markov wages** (§3.3): the Bellman operator is an
  order-preserving `β`-contraction on `ℝ^W₊` (Exercise 3.3.1), so `v*` exists,
  is unique, and value function iteration converges; `v*` is increasing when
  `P` is monotone increasing (Lemma 3.3.1); the continuation value `h*` solves
  the recursion of Exercise 3.3.3 and is the unique fixed point of the
  `β`-contraction `Q` (Exercise 3.3.4). With separation, (3.25)–(3.26) reduce to
  (3.27)–(3.28), whose operator is an upper envelope of two contractions, so the
  pair `(v_u*, v_e*)` exists uniquely and is computable by iteration
  (Exercise 3.3.5).

The main entry points are `pow_apply_eq_sum_paths`, `IsMarkov.irreducible_iff`,
`Inventory.irreducible_P`, `DayLaborer.tendsto_vecMul_pow`,
`globallyStable_of_pos`, `Tauchen.isMarkov_P`, `Tauchen.monotoneIncreasing_P`,
`iterated_expectations`, `monotoneIncreasing_iff`, `IsMarkov.lifetimeValue_eq_inv`,
`IsMarkov.monotone_lifetimeValue`, `MarkovJobSearch.isContractionOn_T`,
`MarkovJobSearch.monotone_vstar`, `MarkovJobSearch.isContractionOn_Q` and
`MarkovJobSearch.system_unique`, all in the namespace
`SargentStachurski.MarkovDynamics`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (the inventory chain's irreducibility proof uses
`s < S`, as in the book's calibration), the hypotheses the book leaves implicit,
and what is not formalised: the ergodic theorem (Theorem 3.1.2), which the book
cites from Brémaud, the Gaussian Exercises 3.1.10–3.1.11, and the computational
exercises.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](MarkovDynamics/Basics.lean) | 12 | Markov matrices, distributions, `Pf ≤ Pg`, `|Ph| ≤ ‖h‖`; global stability and contractions with Banach's theorem (Chapter 1 facts, restated) |
| [MarkovChains](MarkovDynamics/MarkovChains.lean) | 11 | Path probabilities, (3.2), Ex 3.1.2, (3.3)–(3.6), Ex 3.1.4, stationary distributions, irreducibility, Lemma 3.1.1 |
| [Inventory](MarkovDynamics/Inventory.lean) | 20 | S–s dynamics (p. 83): Ex 3.1.1, the transition matrix as a `tsum` over demands, Markov, Ex 3.1.3 (irreducible) |
| [PositiveChains](MarkovDynamics/PositiveChains.lean) | 11 | ℓ¹ norm, Dobrushin's estimate, Ex 3.1.7 for every `P ≫ 0`: unique stationary distribution and `ψPᵗ → ψ*`; the `GloballyStable` form on `D(X)` |
| [DayLaborer](MarkovDynamics/DayLaborer.lean) | 12 | (3.8), Ex 3.1.6 (`ψ*` and uniqueness), `ψPᵗ → ψ*` in closed form, Ex 3.1.7 applied, Ex 3.2.3 (monotone iff `α + β ≤ 1`) |
| [ConditionalExpectations](MarkovDynamics/ConditionalExpectations.lean) | 8 | (3.12)–(3.14), Ex 3.2.1, (3.15), monotone Markov operators, Ex 3.2.4–3.2.5 |
| [Tauchen](MarkovDynamics/Tauchen.lean) | 17 | Tauchen's rules (i)–(iii), Ex 3.1.12, Markov, tail sums, Abel summation and Lemma 2.2.5 (ii) on `Fin n`, Ex 3.2.2 |
| [GeometricSums](MarkovDynamics/GeometricSums.lean) | 15 | (3.16)–(3.18), Lemma 3.2.1, (3.19) firm value, Ex 3.2.6, (3.20)–(3.22) consumption value, Ex 3.2.8 |
| [JobSearch](MarkovDynamics/JobSearch.lean) | 39 | (3.23), Ex 3.3.1, `v*`, VFI, greedy policies, Lemma 3.3.1, `h*`, Ex 3.3.3, (3.24) and Ex 3.3.4; separation (3.25)–(3.28), Ex 3.3.5 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
