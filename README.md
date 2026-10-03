# Dynamic Programming in Lean

Checked dynamic programming, following Sargent and Stachurski, *Dynamic
Programming*, Volume 1: *Finite States* and Volume 2: *General States*. Each
folder is an independent Lean/Mathlib project for one chapter, with precise
statements, a source map to the book's results and pages, and reproducible
proof checks. Volume 1 projects live under `FiniteStates/`, Volume 2 under
`GeneralStates/`.

| Project | Chapter | Checked results | Start here |
| --- | --- | --- | --- |
| [FiniteStates/JobSearch](FiniteStates/JobSearch/README.md) | I.1 Introduction | 201 theorems: Banach's theorem by the book's route, the Neumann series lemma from the spectral radius with Gelfand's formula, the Solow–Swan map globally stable without being a contraction, finite-horizon reservation wages at every horizon, the Bellman operator as a `β`-contraction with value function iteration, the continuation-value map, quantiles on a finite set | [Chapter overview](FiniteStates/JobSearch/README.md) |

## Scope

The plan is in [PROPOSAL-SargentStachurski.md](PROPOSAL-SargentStachurski.md):
nineteen chapter projects built one at a time, in book order. Volume 1 works
on a finite state space, where value functions are vectors and the Bellman
operator acts on `ℝ^X`; Volume 2 moves to general state spaces, bounded
functions, Banach spaces and partially ordered sets.

Where the book argues from a figure, the Lean statement is a theorem with
explicit hypotheses. Where the book leaves a hypothesis implicit, it is
stated. Where the book's claim is false or imprecise as printed, the corrected
statement is proved and the change is recorded in that project's
`docs/corrections.md`. The provable exercises are formalised; computational
exercises and code listings are not.

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3.12+. Each project
pins Lean and Mathlib `v4.34.0`, and its Lake manifest pins transitive
dependencies. From the repository root:

```sh
cd FiniteStates/JobSearch
lake exe cache get
python scripts/verify.py
```

The verifier builds the complete project, freshly recompiles every contributed
proof without importing its compiled project module, and audits each named
declaration's transitive axioms. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Warnings, failed proofs, or placeholder axioms fail
the check. Every file carries the Apache 2.0 header that Mathlib's header linter
checks. GitHub Actions runs every project independently on pushes and pull
requests. The generated `verification/verification.json` records source hashes
and axiom lists. Proof checking happens in Lean's kernel; the JSON is a record
of a run.

The layout follows
[LeanEconomics/InternationalEconomics](https://github.com/LeanEconomics/InternationalEconomics).
Each project is self-contained: a lemma needed by more than one chapter is
copied into each project that uses it, rather than shared through a
cross-project dependency.

## Development and provenance

These contributions are developed with **Claude Code** (Anthropic), under the
direction of Robert Kirkby. The books are cited by result, equation and page
number and are not reproduced; see each project's `THIRD_PARTY_NOTICES.md`.

## License

Apache License 2.0; see [LICENSE](LICENSE).
