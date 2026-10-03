# Job search, contractions and the Bellman equation in Lean

This is the `FiniteStates/JobSearch/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd FiniteStates/JobSearch` from the
repository root. [Return to the library index](../../README.md).

A checked formalisation of Sargent and Stachurski, *Dynamic Programming*,
Volume 1: *Finite States*, Chapter 1, "Introduction" (pp. 1–41), including
the provable exercises. Work in progress: the library map below lists the
modules written so far.

See the [source map](docs/source-map.md) for the correspondence with the book,
result by result. [Corrections](docs/corrections.md) records where a printed
claim needs a changed statement, the hypotheses the book leaves implicit, and
what is not formalised.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Lattice](JobSearch/Lattice.lean) | 11 | `a ∨ b`, `a ∧ b`, `|a|`; Ex 1.2.1; the bound (1.28) and Ex 1.3.1; pointwise operations (1.20)–(1.21) |
| [FixedPoints](JobSearch/FixedPoints.lean) | 9 | Fixed points, global stability (p. 22), Examples 1.2.3–1.2.4, Ex 1.2.15, 1.2.16, 1.2.18 (with the missing nonemptiness hypothesis) |
| [Contractions](JobSearch/Contractions.lean) | 18 | Contractions (1.17); Ex 1.2.19, 1.2.21–1.2.23; Theorem 1.2.3 (Banach) with the rate (1.18) and global stability; Ex 1.2.24 damped iteration; the `ℝ^X` restatement (p. 31) |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
