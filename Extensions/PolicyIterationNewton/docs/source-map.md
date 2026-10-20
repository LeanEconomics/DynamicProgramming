# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book (Volume 1, §5.1,
proves the Newton identity and finite termination). Results are listed by their source in the
literature. Lean names are relative to `DPExtensions.PolicyIterationNewton`. Where the Lean
statement departs from the published one, see [departures from the sources](corrections.md).

## The framework

| Source | Claim | Lean |
| --- | --- | --- |
| Howard (1960); Puterman and Brumelle (1979) | Policies with a greedy selector; operators, contractions, fixed points | `PolicyModel`, `PolicyModel.Pv`, `PolicyModel.Tσ`, `PolicyModel.T`, `PolicyModel.Tσ_le_T`, `PolicyModel.Pv_sub`, `PolicyModel.abs_Pv_le`, `PolicyModel.Pv_mono`, `PolicyModel.Tσ_mono`, `PolicyModel.norm_Tσ_sub_le`, `PolicyModel.norm_T_sub_le`, `PolicyModel.contracting_T`, `PolicyModel.contracting_Tσ`, `PolicyModel.vstar`, `PolicyModel.vσ`, `PolicyModel.T_vstar`, `PolicyModel.Tσ_vσ`, `PolicyModel.le_vσ_of_le`, `PolicyModel.vσ_le_vstar`, `PolicyModel.vσ_greedy_vstar` |
| Howard (1960) | Policy improvement | `PolicyModel.le_vσ_greedy` |
| Puterman and Brumelle (1979) | Policy iteration is Newton's method for `Tv − v` | `PolicyModel.newton_identity` |

## Rates

| Source | Claim | Lean |
| --- | --- | --- |
| Puterman and Brumelle (1979) | Policy iteration values increase and converge at least linearly | `PolicyModel.piPolicy`, `PolicyModel.piValue`, `PolicyModel.piValue_succ`, `PolicyModel.le_T_vσ`, `PolicyModel.piValue_mono`, `PolicyModel.linear_rate`, `PolicyModel.error_le_geometric`, `PolicyModel.pi_converges` |
| Puterman and Brumelle (1979) | The error bound in terms of greedy transitions; quadratic convergence | `PolicyModel.abs_Pv_diff_le`, `PolicyModel.pb_bound`, `PolicyModel.quadratic_rate` |
| Santos and Rust (2004) | Superlinear convergence | `PolicyModel.superlinear_rate` |
| — | Exact termination when greedy policies near `v*` are optimal | `PolicyModel.pi_terminates`, `PolicyModel.exists_pi_terminates` |

## Finite MDPs

| Source | Claim | Lean |
| --- | --- | --- |
| — (standard) | Finite MDPs as policy models | `FiniteMDP`, `FiniteMDP.Pol`, `FiniteMDP.Q`, `FiniteMDP.greedyAct`, `FiniteMDP.greedyAct_mem`, `FiniteMDP.greedyAct_max`, `FiniteMDP.toPolicyModel`, `FiniteMDP.Tσ_eq`, `FiniteMDP.vstar_eq`, `FiniteMDP.abs_Q_sub_le` |
| — | The optimality gap; greedy policies near `v*` are optimal; an explicit bound on the number of iterations | `FiniteMDP.exists_gap`, `FiniteMDP.greedy_optimal_of_near`, `FiniteMDP.pi_terminates_finite`, `FiniteMDP.exists_pi_terminates_finite` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Ye (2011); Hansen, Miltersen and Zwick (2013) | Policy iteration is strongly polynomial for a fixed discount factor | The combinatorial argument through occupation measures is beyond this project. |
| Santos and Rust (2004) | General (continuous) state spaces | Finite states only here. |
