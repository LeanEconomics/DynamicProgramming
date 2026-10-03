# Stochastic discounting in Lean

This is the `FiniteStates/StochasticDiscounting/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/StochasticDiscounting`
from the repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 6, "Stochastic Discounting" (pp. 182–212),
including every provable exercise (Exercises 6.1.1–6.1.5, 6.2.1–6.2.4,
6.3.1–6.3.7, 6.3.9), together with the parts of the Perron–Frobenius theorem
(Theorem 2.3.1, p. 69) that the Chapter 2 project deferred to this chapter.
The library contains **263 theorems** and audits every declaration, including
structure constructors and projections.

* **Perron–Frobenius, completed** (Theorem 2.3.1): the spectral radius,
  Gelfand's formula, the Neumann series and the nonnegative case are restated
  for a matrix indexed by any finite type (Chapter 6 needs product state spaces).
  New here: for irreducible `A`, `ρ(A) > 0`, the right and left eigenvectors are
  everywhere positive and unique up to scale, and `ρ(A)` is the only eigenvalue
  with a nonnegative eigenvector; an irreducible Markov matrix has exactly one
  stationary distribution and it is everywhere positive (Exercise 2.3.2 (iv));
  and for `A ≫ 0`, `ρ(A)⁻ᵗ Aᵗ(x, x') → e(x)ε(x')` with `⟨ε, e⟩ = 1`, (2.11), by
  conjugating to a positive Markov matrix and Dobrushin's ℓ¹ contraction.
* **Valuation** (§6.1.1–§6.1.2): the discount operator `L(x, x') = b(x, x')P(x, x')`;
  Theorem 6.1.1, `∑ₜ Lᵗh = (I − L)⁻¹h` is the unique solution of `v = h + Lv` when
  `ρ(L) < 1`; firm valuation with state-dependent interest rates (Exercises
  6.1.1–6.1.2, the latter needing nonnegative profits); Lemma 6.1.2,
  `ρ(L) = lim ℓₜ^{1/t}` with `ℓₜ = max_x E_x[β₁⋯βₜ]` and `ρ(L) < 1` iff some
  `ℓₜ < 1`; Exercise 6.1.3 with the stationary distribution of an irreducible
  chain; Lemma 6.1.3, `ρ(L) = ρ(L_Z)` when discounting depends on one component
  of the state; Lemma 6.1.4, `ρ(L) < 1` is necessary and sufficient for a unique
  positive solution when `h ≫ 0`.
* **Eventual contractions** (§6.1.3): Theorem 6.1.5, an eventual contraction on a
  closed set is globally stable (Exercise 6.1.4); Exercise 6.1.5 on changing the
  norm; Example 6.1.2 on affine maps; Proposition 6.1.6, `|Tv − Tw| ≤ L|v − w|`
  with `ρ(L) < 1` makes `T` eventually contracting; Proposition 6.1.7, the
  generalised Blackwell condition.
* **MDPs with state-dependent discounting** (§6.2.1): `T_σ v = r_σ + L_σ v` with
  `L_σ(x, x') = β(x, σ(x), x')P(x, σ(x), x')`; Lemma 6.2.1, `v_σ = (I − L_σ)⁻¹r_σ`;
  Exercises 6.2.1–6.2.3; Proposition 6.2.2 under Assumption 6.2.1, proved here
  from the global stability of each `T_σ` alone: `v*` is the unique solution of
  the Bellman equation, optimal iff `v*`-greedy, and an optimal policy exists;
  the HPI improvement and termination steps of Algorithm 6.1; OPI; convergence of
  value function iteration under a dominating discount operator (6.20).
* **Exogenous discounting** (§6.2.1.5): Proposition 6.2.3 (Exercise 6.2.4),
  `ρ(L_Z) < 1` for `L_Z(z, z') = β(z)Q(z, z')` gives all of Proposition 6.2.2; and
  value function iteration converges in this model, because `|Tv − Tw|` is
  bounded by `L_Z` applied to the column maxima of `|v − w|`.
* **Inventory management revisited** (§6.2.2): the model of §5.2.1 with
  `β(Zₜ)`, its action value in the kernel form (6.26) and the shock form (6.25),
  and its optimality theory under the spectral radius test of Listing 6.1.
* **Asset pricing** (§6.3): Markov pricing (6.32), the Arrow–Debreu operator,
  the ex-dividend price `(I − A)⁻¹Ad = ∑_{k≥1}Aᵏd` and the cum-dividend price
  `∑_{k≥0}Aᵏd` (Exercises 6.3.1–6.3.4, the forward sum representation),
  price-dividend ratios with random growth (Exercises 6.3.5–6.3.6), the Lucas
  SDF with Gaussian shocks via the moment generating function (Exercise 6.3.7),
  and the Harrison–Kreps operator as a contraction on `ℝ^X₊` by Lemma 2.2.2 and
  by Blackwell's condition (Exercise 6.3.9).

The main entry points are `tendsto_pow_of_pos` (Theorem 2.3.1, positive case),
`IsMarkov.exists_unique_stationary_of_irreducible`, `inv_mulVec_eq_tsum`
(Theorem 6.1.1), `specRad_lt_one_iff_exists_norm_pow_mulVec_one_lt`
(Lemma 6.1.2), `specRad_productDiscountOp` (Lemma 6.1.3),
`specRad_lt_one_iff_existsUnique_pos` (Lemma 6.1.4),
`globallyStable_of_iterate_contraction` (Theorem 6.1.5),
`globallyStable_of_blackwell`, `SDMDP.isFixedPt_T_vstar`,
`SDMDP.isOptimal_iff_isGreedy`, `Exogenous.spectralCondition`,
`Exogenous.tendsto_iterate_T`, `exDivPrice_eq_tsum` and `existsUnique_hk_price`,
all in the namespace `SargentStachurski.StochasticDiscounting`.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement (Exercise 6.1.2 is false without `π ≥ 0`;
Proposition 6.2.3's hint needs Lemma 6.1.3 in a more general form), the
hypotheses the book leaves implicit, and what is not formalised: the
probabilistic form of the expectations in (6.3), (6.6) and (6.19), which are
taken in their operator form, the convergence of VFI, OPI and HPI under
Assumption 6.2.1 alone (Chapter 8), and the economics of §6.3.1.1–§6.3.1.3.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](StochasticDiscounting/Basics.lean) | 18 | Markov matrices, contractions and Banach's theorem, Prop 2.2.7, Blackwell's condition, Lemma 2.2.2 (restated Chapter 1–5 facts) |
| [SpectralRadius](StochasticDiscounting/SpectralRadius.lean) | 29 | `ρ(A)` on a general finite type, Gelfand's formula, the Neumann series, `ρ(Aᵀ) = ρ(A)`, Ex 2.2.28, row-sum norms |
| [Resolvent](StochasticDiscounting/Resolvent.lean) | 11 | The resolvent series entry by entry |
| [PerronFrobenius](StochasticDiscounting/PerronFrobenius.lean) | 20 | Thm 2.3.1, nonnegative case; Lemma 2.3.2; the local spectral radius (Lemma 2.3.3); Ex 2.3.2 (ii)–(iii), Ex 2.3.3 |
| [Irreducible](StochasticDiscounting/Irreducible.lean) | 10 | Thm 2.3.1, irreducible case: `ρ(A) > 0`, positive and unique eigenvectors; Ex 2.3.2 (iv) |
| [PositiveMatrices](StochasticDiscounting/PositiveMatrices.lean) | 19 | Dobrushin's estimate (Ex 3.1.7), rows of `Pᵗ` converge, the conjugate Markov matrix, Thm 2.3.1 (2.11) |
| [Valuation](StochasticDiscounting/Valuation.lean) | 32 | (6.4)–(6.7), Thm 6.1.1, Ex 6.1.1–6.1.3, Lemma 6.1.2 (6.10), Lemma 6.1.3, Lemma 6.1.4 |
| [EventualContraction](StochasticDiscounting/EventualContraction.lean) | 16 | Thm 6.1.5 (Ex 6.1.4), Ex 6.1.5, Example 6.1.2, Prop 6.1.6, Prop 6.1.7 |
| [SDMDP](StochasticDiscounting/SDMDP.lean) | 22 | The model, (6.16)–(6.18), Assumption 6.2.1, Lemma 6.2.1, Ex 6.2.1–6.2.3 |
| [Optimality](StochasticDiscounting/Optimality.lean) | 27 | (6.21), greedy policies, `v*`, Prop 6.2.2, Algorithm 6.1 steps, OPI, VFI under (6.20) |
| [ExogenousDiscounting](StochasticDiscounting/ExogenousDiscounting.lean) | 18 | (6.22)–(6.23), Prop 6.2.3 (Ex 6.2.4), convergent VFI |
| [Inventory](StochasticDiscounting/Inventory.lean) | 14 | §6.2.2: (6.24)–(6.26), the spectral radius test of Listing 6.1 |
| [AssetPricing](StochasticDiscounting/AssetPricing.lean) | 17 | (6.27), (6.32)–(6.37), (6.39)–(6.41), Ex 6.3.1–6.3.7, Remark 6.3.1 |
| [HarrisonKreps](StochasticDiscounting/HarrisonKreps.lean) | 10 | (6.42)–(6.43), the contraction on `ℝ^X₊`, Ex 6.3.9 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
