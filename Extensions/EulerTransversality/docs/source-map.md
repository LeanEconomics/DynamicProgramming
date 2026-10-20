# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book. Results are
listed by their source in the literature. Lean names are relative to
`DPExtensions.EulerTransversality`. Where the Lean statement departs from the published one, see
[departures from the sources](corrections.md).

## Sufficiency

| Source | Claim | Lean |
| --- | --- | --- |
| — | Partial values, feasible paths, catching-up optimality | `partialValue`, `partialValue_succ`, `Feasible`, `CatchingUp` |
| Stokey and Lucas (1989), Thm 4.15; Ekeland and Scheinkman (1986) | Euler equation and transversality are sufficient | `finite_horizon_bound`, `euler_tvc_sufficient` |

## The growth model

| Source | Claim | Lean |
| --- | --- | --- |
| — (standard) | A concave function lies below its tangent line | `concave_tangent` |
| Cass (1965); Koopmans (1965) | The one-sector growth model | `GrowthModel`, `GrowthModel.G`, `GrowthModel.F`, `GrowthModel.c`, `GrowthModel.c_nonneg` |
| Stokey and Lucas (1989), Thm 4.15 | Euler and transversality are sufficient | `GrowthModel.growth_sufficient` |
| Cass (1965); Koopmans (1965) | The modified-golden-rule steady state is optimal | `GrowthModel.steady_state_optimal` |
| Kamihigashi (2001) | The transversality condition is necessary | `GrowthModel.growth_tvc_necessary` |
| — | An Euler path is optimal iff it satisfies transversality | `GrowthModel.optimal_iff_tvc` |
| — (standard example) | The Euler equation alone is not sufficient | `linearModel`, `hoarding`, `euler_not_sufficient` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Kamihigashi (2001, 2003) | Necessity with unbounded-below utility (e.g. `log`) and in stochastic problems | Here `u(0)` is finite and the problem is deterministic. |
| Stokey and Lucas (1989), Ch. 4 | Necessity of the Euler equation at interior optima | Standard; not needed for the characterization of Euler paths. |
