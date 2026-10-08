# Monotone policies in Lean

This is the `Extensions/MonotonePolicies/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/MonotonePolicies` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*: when is the optimal policy
monotone in the state? The answer, Topkis's theorem on complementarities, is the standard route to
"saving rises with wealth", cutoff rules for investment and exit, and monotone Markov dynamics in
heterogeneous-agent models. The library contains **48 theorems**.

* **Topkis's theorem**: with feasible sets ascending in the strong set order and an objective
  with increasing differences, the argmax is ascending, and the greatest and the least maximizers
  are increasing; with strictly increasing differences every maximizer is (`topkis_gmax`,
  `topkis_lmax`, `topkis_strict`). Increasing differences of `u(m(x) − g(a))` for concave `u`
  (`increasingDifferences_concave`), and its closure properties.
* **Monotone optimal policies in finite dynamic programs**: the optimality theory (contraction,
  greedy ⇔ optimal) is proved from scratch; the greatest and least optimal policies are increasing
  when `Q_{v*}` has increasing differences (`FDP.optimal_monotone`); `v*` is increasing under
  monotone primitives (`FDP.vstar_monotone`); sufficient conditions from primitives
  (`FDP.id_Q_of_actionKernel`, `FDP.optimal_monotone_of_primitives`); monotone policies induce
  monotone state chains (`monotoneKernel_comp`).
* **The savings problem**: on an asset grid with i.i.d. income and any concave utility, the
  greatest optimal saving rule is increasing in assets and income, and the household's state
  follows a monotone Markov chain (`SavingsModel.savings_monotone`,
  `SavingsModel.chain_monotone`).

All names are in the namespace `DPExtensions.MonotonePolicies`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md):

* actions range over a linear order and feasible sets are finite (a lattice of actions is not
  needed for the economic applications here);
* the dynamic program has finitely many states.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Topkis](MonotonePolicies/Topkis.lean) | 14 | Increasing differences, the strong set order, Topkis's theorem |
| [MonotoneDP](MonotonePolicies/MonotoneDP.lean) | 27 | Finite dynamic programs, monotone optimal policies and value functions |
| [Savings](MonotonePolicies/Savings.lean) | 7 | Saving rises with wealth and income; the monotone wealth chain |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
