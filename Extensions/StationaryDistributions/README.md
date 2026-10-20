# Stationary distributions of monotone economies in Lean

This is the `Extensions/StationaryDistributions/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/StationaryDistributions` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*: when does a heterogeneous-agent
economy have a unique stationary distribution, does it converge to it, and how does it move when
policies change? The answer for monotone economies is Hopenhayn and Prescott (1992), proved here
on a finite grid. The library contains **41 theorems**.

* **First-order stochastic dominance on a grid**: summation by parts (`abel`); FOSD and
  expectations of monotone functions (`sum_mul_antitone_le`, `sum_mul_monotone_le`); monotone
  kernels preserve FOSD (`push_mono`) and shrink the Kolmogorov distance
  (`abs_cdf_push_sub_le`).
* **Hopenhayn–Prescott**: a monotone kernel has a least stationary distribution, the limit of
  `δ₀Pᵗ`, with no irreducibility or aperiodicity (`exists_least_stationary`). Under monotone
  mixing, `m` steps contract the Kolmogorov distance by `1 − ε` (`contraction`), so the stationary
  distribution is unique (`stationary_unique`) and globally stable (`global_stability`). FOSD-higher
  kernels have FOSD-higher stationary distributions (`stationary_mono`).
* **Saving rules and aggregate assets**: with i.i.d. income, the asset chain of an increasing
  saving rule is monotone, and a pointwise higher saving rule gives an FOSD-higher stationary asset
  distribution and higher aggregate assets (`aggregate_assets_mono`). With
  `Extensions/MonotonePolicies` (saving rises with wealth) this is the chain from the household
  problem to monotone aggregate capital supply.

All names are in the namespace `DPExtensions.StationaryDistributions`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md): the state
space is a finite grid `{0, …, n}` rather than a compact ordered space.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [CDF](StationaryDistributions/CDF.lean) | 14 | Distributions, kernels, summation by parts, FOSD, monotone kernels |
| [HopenhaynPrescott](StationaryDistributions/HopenhaynPrescott.lean) | 22 | Existence, uniqueness, global stability, comparative statics |
| [PolicyChains](StationaryDistributions/PolicyChains.lean) | 5 | Asset chains of saving rules; aggregate assets rise with the saving rule |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
