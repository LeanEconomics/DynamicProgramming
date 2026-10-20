# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book. Results are
listed by their source in the literature. Lean names are relative to
`DPExtensions.StationaryDistributions`. Where the Lean statement departs from the published one,
see [departures from the sources](corrections.md).

## Distributions and stochastic dominance on a grid

| Source | Claim | Lean |
| --- | --- | --- |
| — (standard) | Cumulative distribution functions; summation by parts | `cdf`, `cdf_zero`, `cdf_succ`, `cdf_sub`, `abel`, `cdf_nonneg`, `cdf_mono`, `cdf_le_one` |
| — (standard) | Distributions, kernels, the next-period distribution | `IsDist`, `IsKernel`, `push`, `cdf_push`, `push_isDist` |
| Hadar and Russell (1969); Hanoch and Levy (1969) | FOSD orders expectations of monotone functions | `Dominated`, `sum_mul_antitone_le`, `sum_mul_monotone_le` |
| Daley (1968); Hopenhayn and Prescott (1992) | Monotone kernels preserve FOSD; FOSD-higher rows push distributions up | `IsMonotone`, `push_mono`, `push_le_of_le` |
| Bhattacharya and Lee (1988) | A monotone kernel shrinks the Kolmogorov distance | `abs_cdf_push_sub_le`, `nonexpansive`, `kdist`, `le_kdist`, `kdist_le` |

## Hopenhayn and Prescott (1992)

| Source | Claim | Lean |
| --- | --- | --- |
| — | `m`-step kernels and iterates | `kpow`, `iter`, `IsStationary`, `cdf_congr`, `push_congr`, `eq_cdf_sub`, `eq_of_cdf_eq`, `cdf_kpow_zero`, `kpow_isKernel`, `kpow_isMonotone`, `iter_eq_push_kpow`, `iter_add`, `iter_isDist`, `iter_stationary` |
| Hopenhayn and Prescott (1992) | A monotone kernel has a least stationary distribution, the limit of `δ₀Pᵗ` | `bottom`, `cdf_bottom`, `bottom_isDist`, `bottom_le`, `exists_least_stationary` |
| Hopenhayn and Prescott (1992); Bhattacharya and Lee (1988); Kamihigashi and Stachurski (2014) | Under monotone mixing, `Pᵐ` contracts the Kolmogorov distance; uniqueness; global stability | `MonotoneMixing`, `contraction`, `stationary_unique`, `global_stability` |
| Hopenhayn and Prescott (1992) | Monotone comparative statics of stationary distributions | `stationary_mono` |

## Saving rules and aggregate assets

| Source | Claim | Lean |
| --- | --- | --- |
| Huggett (1993); Aiyagari (1994) | The asset chain of a saving rule with i.i.d. income | `policyKernel`, `cdf_policyKernel`, `policyKernel_isKernel` |
| Hopenhayn and Prescott (1992) | Increasing rules give monotone chains; higher rules give FOSD-higher rows and stationary distributions, and higher aggregate assets | `policyKernel_isMonotone`, `policyKernel_le`, `aggregate_assets_mono` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Hopenhayn and Prescott (1992) | Compact metric state spaces with a closed order, weak convergence, the greatest stationary distribution | Finite grids only here; the greatest stationary distribution follows symmetrically from the top point mass. |
| Kamihigashi and Stachurski (2014) | Order mixing on unbounded spaces | Out of scope. |
| Aiyagari (1994) | Existence of general equilibrium from monotone aggregate supply | Needs continuity in the interest rate; see the LeanEconomics programme. |
