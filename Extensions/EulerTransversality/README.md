# Euler equations and transversality in Lean

This is the `Extensions/EulerTransversality/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/EulerTransversality` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*, which uses the Euler equation
of the growth model (Volume 2, Chapter 8) but never the transversality condition. When does a
path that satisfies the Euler equation solve the problem? The library contains **10 theorems**.

* **Sufficiency from supergradients**: in any real vector space, if `F` has supergradients
  `(p_t, q_t)` along a path, the Euler equation `q_t + βp_{t+1} = 0` gives a finite-horizon bound
  (`finite_horizon_bound`), and with `p_t(x_t) ≥ 0` and the transversality condition
  `β^tp_t(x*_t) → 0` the path is catching-up optimal and has the largest value whenever values are
  finite (`euler_tvc_sufficient`). No differentiability, interiority or boundedness is needed.
* **The growth model**: Euler plus transversality is sufficient (`growth_sufficient`); the
  modified-golden-rule steady state is optimal (`steady_state_optimal`); the transversality
  condition is necessary for `β < 1` and `f(0) ≥ 0`, by Kamihigashi's rescaling argument
  (`growth_tvc_necessary`); so an Euler path is optimal iff it satisfies transversality
  (`optimal_iff_tvc`).
* **The Euler equation alone is not enough**: with `u(c) = c` and `f(k) = k/β`, the path that
  never consumes satisfies the Euler equation, violates transversality, and is beaten by consuming
  everything at once (`euler_not_sufficient`).

All names are in the namespace `DPExtensions.EulerTransversality`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Sufficiency](EulerTransversality/Sufficiency.lean) | 3 | Supergradients, Euler and transversality imply optimality |
| [GrowthModel](EulerTransversality/GrowthModel.lean) | 6 | Tangent lines; sufficiency, steady state, necessity, characterization |
| [Counterexample](EulerTransversality/Counterexample.lean) | 1 | An Euler path that is not optimal |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
