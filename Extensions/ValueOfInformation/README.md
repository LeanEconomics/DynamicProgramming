# The value of information in Lean

This is the `Extensions/ValueOfInformation/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/ValueOfInformation` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*, whose learning models (job
search with learning, Volume 2, Chapter 8) take the signal structure as given. When is one source
of information better than another for **every** decision maker? Blackwell's theorem answers it:
exactly when the other is a garbling of it. The library contains **19 theorems**.

* **Garbling never helps** (`value_garble_le`): for experiments `P`, Markov matrices `M` and every
  decision problem, `V_u(PM) ≤ V_u(P)`. Values are written with unnormalized posteriors, so signals
  of probability zero need no special treatment. The general form for sublinear functions of the
  posteriors (`sublinear_garble_le`) says that the posteriors of `P` are a mean-preserving spread of
  those of `PM`. Information has nonnegative value (`value_noInfo_le`), and no experiment beats
  observing the state (`value_le_perfect`).
* **Blackwell's converse** (`blackwell_converse`, `blackwell`): if `P` is at least as valuable as
  `Q` in every decision problem, then `Q` is a garbling of `P`. The proof separates `Q`'s
  posteriors from the compact convex set of garblings of `P`; the separating functional is itself
  a decision problem.
* **Binary signals** (`binExp_garble`, `value_mono_accuracy`, `value_strict`): a less accurate
  binary signal is a garbling of a more accurate one, so accuracy is valuable in every decision
  problem, strictly so when guessing the state.

All names are in the namespace `DPExtensions.ValueOfInformation`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Blackwell](ValueOfInformation/Blackwell.lean) | 9 | Experiments, garblings, decision values; sufficiency |
| [Converse](ValueOfInformation/Converse.lean) | 4 | The converse by separating hyperplanes; Blackwell's equivalence |
| [BinarySignals](ValueOfInformation/BinarySignals.lean) | 6 | Accuracy and the Blackwell order for binary signals |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
