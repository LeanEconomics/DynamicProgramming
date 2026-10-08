# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book. Results are
listed by their source in the literature. Bray (2019a) is "Strong convergence and dynamic
economic models", *Quantitative Economics* 10, 43–65; Bray (2019b) is "Markov decision processes
with exogenous variables", *Management Science* 65, 4598–4606. Lean names are relative to
`DPExtensions.RelativeValueIteration`. Where the Lean statement departs from the published one,
see [departures from the sources](corrections.md).

## The span seminorm

| Source | Claim | Lean |
| --- | --- | --- |
| Seneta (1981) | The span seminorm; the Dobrushin bound `∑pd − ∑qd ≤ (1 − ∑min(p, q))·sp(d)` | `sp`, `sub_le_sp`, `abs_sub_le_sp`, `sp_nonneg`, `sp_le`, `sp_add_const`, `sp_neg`, `le_sup'_sp`, `inf'_le_sp`, `dobrushin` |

## MDPs and relative value iteration

| Source | Claim | Lean |
| --- | --- | --- |
| — | Finite MDPs, Bellman and policy operators, greedy policies | `MDP`, `MDP.Q`, `MDP.T`, `MDP.Tσ`, `MDP.IsGreedy`, `MDP.IsPolicy`, `MDP.exists_greedyAct`, `MDP.exists_greedy`, `MDP.Q_le_T`, `MDP.Tσ_eq_T_of_greedy`, `MDP.Tσ_le_T`, `MDP.Q_sub_Q` |
| White (1963); Bray (2019a), Prop 1 | Constant shifts and greedy policies | `MDP.Q_add_const`, `MDP.T_add_const`, `MDP.Tσ_add_const`, `MDP.isGreedy_add_const_iff`, `MDP.T_iterate_add_const` |
| Bray (2019a), Lemma 4 | Relative value iteration is value iteration up to a constant | `MDP.rel`, `MDP.rel_add_const`, `MDP.relT_iterate` |
| Seneta (1981); Puterman (2005) | The span contraction | `MDP.sp_T_sub_le`, `MDP.dobrushin_le_one`, `MDP.alpha_nonneg`, `MDP.sp_T_iterate_sub_le` |
| — (standard) | The discounted problem: contractions, `v*`, `v_σ`, monotone comparisons | `MDP.abs_Q_sub_le`, `MDP.norm_T_sub_le`, `MDP.norm_Tσ_sub_le`, `MDP.T_mono`, `MDP.Tσ_mono`, `MDP.contracting_T`, `MDP.contracting_Tσ`, `MDP.vstar`, `MDP.vσ`, `MDP.T_vstar`, `MDP.Tσ_vσ`, `MDP.le_vσ_of_le`, `MDP.le_vstar_of_le`, `MDP.vstar_le_of_T_le`, `MDP.vσ_le_vstar` |
| Morton and Wecker (1977); Bray (2019a), Prop 3 | Strong convergence: relative values converge faster than levels | `MDP.sp_iterate_sub_vstar`, `MDP.rel_converges` |
| MacQueen (1966); Porteus (1971) | The policy error bound `β/(1 − β)·sp(Tv − v)` | `MDP.policy_error` |
| Bray (2019a), Prop 2 | The stopping rule yields `ε`-optimal policies after finitely many steps | `MDP.relIter`, `MDP.relIter_succ`, `MDP.sp_T_relIter_sub`, `MDP.stopping_rule`, `MDP.stopping_rule_sup`, `MDP.sp_relIter_succ_sub_le`, `MDP.stopping_eventually` |

## Average reward

| Source | Claim | Lean |
| --- | --- | --- |
| White (1963); Puterman (2005) | Relative value iteration converges to a solution of the average-reward optimality equation | `MDP.white` |
| — (standard) | The gain is the optimal long-run average reward, attained by the greedy policy, and unique | `MDP.Tσ_iterate_add_const`, `MDP.T_iterate_of_poisson`, `MDP.Tσ_iterate_le_T_iterate`, `MDP.norm_bound`, `MDP.avg_upper`, `MDP.avg_greedy`, `MDP.avg_tendsto`, `MDP.gain_unique` |

## Endogenous value iteration

| Source | Claim | Lean |
| --- | --- | --- |
| Bray (2019b), §2 | MDPs with exogenous variables | `ExoMDP`, `ExoMDP.toMDP`, `ExoMDP.lift`, `ExoMDP.Fxc`, `ExoMDP.sum_P_mul` |
| Bray (2019b), Prop 1 | Exogenous shifts do not affect policies; the endogenizing operator | `ExoMDP.Q_add_lift`, `ExoMDP.T_add_lift`, `ExoMDP.isGreedy_add_lift_iff`, `ExoMDP.mean`, `ExoMDP.endo`, `ExoMDP.endo_decomp`, `ExoMDP.mean_add_lift`, `ExoMDP.endo_add_lift`, `ExoMDP.isGreedy_endo_iff`, `ExoMDP.endoT_iterate`, `ExoMDP.endo_sub` |
| Bray (2019b), Prop 4 | Endogenous value iteration converges at least as fast as relative value iteration | `ExoMDP.spy`, `ExoMDP.sp_le_spy`, `ExoMDP.spy_nonneg`, `ExoMDP.spy_le_sp`, `ExoMDP.abs_endo_le_sp`, `ExoMDP.abs_endo_le`, `ExoMDP.alphaY_nonneg`, `ExoMDP.spy_T_sub_le`, `ExoMDP.endoCoeff_le`, `ExoMDP.spy_T_iterate_sub_le`, `ExoMDP.endo_converges` |
| Bray (2019b), Prop 2 | The endogenous value function identifies the value and policy functions | `ExoMDP.vstar_recover`, `ExoMDP.mean_unique`, `ExoMDP.optimal_of_greedy_endo` |
| Bray (2019b), Prop 3 | Endogenous value iteration yields `ε`-optimal policies | `ExoMDP.endo_policy_error` |
| Bray (2019b), Cor 3 | A non-ergodic exogenous variable voids relative value iteration's speed-up but not endogenous value iteration's | `swapModel`, `swap_T`, `swap_dobrushin_ge`, `sp_bool_unit`, `swap_sp_iterate`, `swap_sp_vstar`, `swap_endo_exact`, `relative_slow_endogenous_exact` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Morton and Wecker (1977); Bray (2019a), Prop 3; Bray (2019b), Props 4–5 | Asymptotic rates `O⁺(βⁿσ(F(p*))ⁿ)` in terms of spectral subradii | Needs the Jordan form and an envelope-theorem argument; the Dobrushin rates proved here are non-asymptotic upper bounds. |
| Bray (2019a), §4; Bray (2019b) | Relative and endogenous policy iteration; simulation-based evaluation | Out of scope. |
| — | The vanishing-discount limit `(1 − β)v*_β → g` | Not needed for White's theorem. |
