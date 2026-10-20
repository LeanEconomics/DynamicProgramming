# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book. Results are
listed by their source in the literature. Lean names are relative to
`DPExtensions.MonotonePolicies`. Where the Lean statement departs from the published one, see
[departures from the sources](corrections.md).

## Topkis's theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Topkis (1978); Topkis (1998); Milgrom and Shannon (1994) | Increasing differences; the strong set order | `IncreasingDifferences`, `StrictIncreasingDifferences`, `Ascending` |
| Topkis (1998) | Closure of increasing differences under sums and positive scaling; separable and product objectives | `IncreasingDifferences.add`, `IncreasingDifferences.const_mul`, `increasingDifferences_of_sep`, `increasingDifferences_mul` |
| — (standard) | Concave increments shrink; `u(m(x) − g(a))` has increasing differences for concave `u` | `concave_increment`, `increasingDifferences_concave` |
| Topkis (1978, 1998) | The argmax is ascending; greatest and least maximizers are increasing; under strict increasing differences every maximizer is | `argmaxSet`, `mem_argmaxSet`, `argmaxSet_nonempty`, `argmax_strongSetOrder`, `gmax`, `lmax`, `gmax_mem`, `lmax_mem`, `topkis_gmax`, `topkis_lmax`, `topkis_strict` |

## Finite dynamic programs

| Source | Claim | Lean |
| --- | --- | --- |
| Bellman (1957); Blackwell (1965) | The Bellman and policy operators are `β`-contractions; `v*`, `v_σ`; `v_σ ≤ v*`; greedy ⇔ optimal | `FDP`, `FDP.Q`, `FDP.T`, `FDP.Tσ`, `FDP.IsPolicy`, `FDP.abs_sum_sub_le`, `FDP.abs_Q_sub_le`, `FDP.norm_T_sub_le`, `FDP.norm_Tσ_sub_le`, `FDP.contracting_T`, `FDP.contracting_Tσ`, `FDP.vstar`, `FDP.vσ`, `FDP.T_vstar`, `FDP.Tσ_vσ`, `FDP.Q_mono`, `FDP.T_mono`, `FDP.Tσ_le_T`, `FDP.le_vstar_of_le_T`, `FDP.vσ_le_vstar`, `FDP.IsGreedy`, `FDP.IsGreedy.isPolicy`, `FDP.Tσ_eq_T_of_greedy`, `FDP.vσ_eq_vstar_of_greedy`, `FDP.IsOptimal`, `FDP.greedy_optimal`, `FDP.exists_greedy`, `FDP.optimal_greedy` |
| Topkis (1998); Stokey and Lucas (1989, Ch. 9) | Monotone optimal policies | `FDP.optimal_monotone`, `FDP.optimal_monotone_least`, `FDP.optimal_le_of_strict`, `FDP.id_Q_of_actionKernel`, `FDP.id_Q_of_continuation`, `FDP.optimal_monotone_of_primitives` |
| Stokey and Lucas (1989, Ch. 9) | The value function is increasing under monotone primitives | `FDP.vstar_monotone` |
| Hopenhayn and Prescott (1992) | Monotone kernels; a monotone policy induces a monotone chain | `MonotoneKernel`, `monotoneKernel_comp` |

## The savings problem

| Source | Claim | Lean |
| --- | --- | --- |
| Huggett (1993); Aiyagari (1994) (household problem on a grid) | Saving rises with assets and income for any concave utility | `SavingsModel`, `SavingsModel.cash`, `SavingsModel.K`, `SavingsModel.K_sum`, `SavingsModel.toFDP`, `SavingsModel.sum_mul_K`, `SavingsModel.cash_monotone`, `SavingsModel.ascending`, `SavingsModel.savings_monotone` |
| Hopenhayn and Prescott (1992) | The household's state follows a monotone Markov chain | `SavingsModel.K_monotone`, `SavingsModel.chain_monotone` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Topkis (1998) | Lattices of actions, quasi-supermodularity and the single-crossing property (Milgrom and Shannon, 1994) | The applications need a linear order of actions. |
| Stokey and Lucas (1989, Ch. 9) | General state spaces, concavity of the value function | Finite states only here. |
| — | Consumption increasing in cash on hand (normality) | Needs concavity of the value function. |
