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

## Relative and endogenous policy iteration

| Source | Claim | Lean |
| --- | --- | --- |
| Howard (1960); Puterman (2005), §6.4 | Policy improvement; policy iteration terminates at an optimal policy | `MDP.pi_improve`, `MDP.eq_vstar_of_T_eq`, `MDP.vσ_eq_vstar_of_stall`, `MDP.pi_mono`, `MDP.pi_terminates` |
| Bray (2019a), §4.1 | Relative policy iteration produces the same policies as policy iteration | `MDP.isGreedy_rel_iff`, `MDP.relPI_terminates` |
| Bray (2019a), Prop 4 | Relative policy iteration returns an `ε`-optimal policy after finitely many iterations | `MDP.pi_residual_le`, `MDP.relPI_stopping`, `MDP.relPI_bray` |
| — | A policy greedy for `w` is within `β/(1 − β)·sp(Λ(Tw − w))` of optimal | `ExoMDP.exoMDP`, `ExoMDP.exists_exo_solution`, `ExoMDP.policy_error_endo` |
| Bray (2019b), §5 and Prop 3 | Endogenous policy iteration produces the same policies as policy iteration and returns an `ε`-optimal policy after finitely many iterations | `ExoMDP.endoPI_terminates`, `ExoMDP.endo_T_endo_sub`, `ExoMDP.endoPI_stopping`, `ExoMDP.endoPI_bray` |

## Asymptotic eigenvalue rates

| Source | Claim | Lean |
| --- | --- | --- |
| Gelfand (1941) | Spectral radius of a real matrix (of its complexification); `‖Aᵏ‖^{1/k} → ρ(A)`; `‖Aᵏ‖ ≤ Cγᵏ` for `γ > ρ(A)`; conversely such bounds bound `ρ(A)` | `complexify`, `complexify_apply`, `complexify_pow`, `complexify_mul`, `nnnorm_complexify`, `norm_complexify`, `specRad`, `spectralRadius_complexify_ne_top`, `specRad_nonneg`, `mem_spectrum_iff_eigenpair`, `tendsto_norm_pow_rpow`, `eventually_norm_pow_le`, `exists_norm_pow_le`, `specRad_le_of_norm_pow_le` |
| Morton and Wecker (1977); Bray (2019a) | The subradius `λ(Q)` is the largest modulus of an eigenvalue other than `1`; a stochastic matrix has no Jordan block at `1` | `deltaMat`, `IsStochastic`, `subradius`, `deltaMat_mulVec`, `cdelta_mulVec`, `mulVec_const`, `cmulVec_const`, `norm_cmulVec_le`, `no_jordan_one`, `complexify_deltaQ_mulVec`, `mem_spectrum_deltaQ_iff`, `spectralRadius_deltaQ` |
| Morton and Wecker (1977) | The subradius governs the span: `sp(Qᵏd) ≤ Cγᵏ sp(d)` for `γ > λ(Q)` | `sp_deltaMat_mulVec`, `norm_deltaMat_mulVec_le`, `sp_le_two_norm`, `deltaQ_pow_mulVec`, `sp_pow_mulVec_le` |
| Seneta (1981) | The subradius is at most the Dobrushin coefficient | `subradius_le_dobrushin`, `MDP.subradius_policy_le` |
| Morton (1971); Bray (2019a), Prop 5 | Relative policy evaluation converges at rate `βλ(P_σ)` | `sp_mul_le`, `MDP.Pmat`, `MDP.Pmat_isStochastic`, `MDP.Tσ_sub`, `MDP.Tσ_iterate_sub`, `MDP.sp_policy_eval_le` |
| Morton and Wecker (1977); Bray (2019a), Prop 3 | With a unique optimal policy, value iteration eventually uses it, and relative values converge at rate `βλ(P_{σ*})` | `MDP.eventually_T_eq_Tσ`, `MDP.norm_iterate_sub_vstar_le`, `MDP.eventually_linear`, `MDP.relative_asymptotic_rate`, `MDP.rel_asymptotic_rate` |
| — (complement to Bray (2019a), Prop 3) | Value levels converge no faster than `β` | `MDP.level_rate_lower` |
| Bray (2019b), Prop 4 | Endogenous values converge at rate `βρ(ΛP_{σ*})`, endogenous policy evaluation at rate `βρ(ΛP_σ)`, and `ρ(ΛF) ≤ λ(F)` | `ExoMDP.endo_idem`, `ExoMDP.endo_lift`, `ExoMDP.PreservesLift`, `ExoMDP.endo_mulVec_endo`, `ExoMDP.spy_le_two_norm_endo`, `ExoMDP.norm_endo_le`, `ExoMDP.spy_mul_le`, `ExoMDP.lamMat`, `ExoMDP.lamMat_mulVec`, `ExoMDP.endoRadius`, `ExoMDP.PreservesLift.pow`, `ExoMDP.lamF_pow_endo`, `ExoMDP.spy_pow_mulVec_le`, `ExoMDP.endoRadius_le_subradius`, `ExoMDP.Pmat_preservesLift`, `ExoMDP.endo_policy_eval_le`, `ExoMDP.endo_asymptotic_rate`, `ExoMDP.endo_values_asymptotic_rate`, `ExoMDP.endoRadius_policy_le` |

## When endogenous value iteration is strictly faster

| Source | Claim | Lean |
| --- | --- | --- |
| — (standard) | Spectral radii from eigenvalue bounds; spectra and spectral radii; powers of stochastic matrices are stochastic | `specRad_le_of_eigen`, `norm_le_specRad`, `specRad_mono_of_spectrum`, `IsStochastic.pow` |
| Puterman (2005), App. A | A chain that is not ergodic (a non-constant fixed vector, or an eigenvalue `μ ≠ 1` with `|μ| = 1`) has subradius at least one | `one_le_subradius_of_nonergodic` |
| Horn and Johnson (2013), §5.1 | Vector norms on `ℂ^Y`: sup, `ℓ¹` and `ℓ²` | `IsVecNorm`, `IsVecNorm.zero`, `IsVecNorm.nonneg`, `IsVecNorm.pos`, `IsVecNorm.sum_le`, `IsVecNorm.smul_real`, `IsVecNorm.sup_norm`, `IsVecNorm.l1_norm`, `IsVecNorm.l2_norm` |
| Horn and Johnson (2013), §5.6 | The largest singular value is the `ℓ²` operator norm; real `ℓ²` bounds extend to complex vectors | `norm_apply_le_singularValues_zero`, `sum_sq_mulVec_le_singularValues`, `sum_sq_norm_cmulVec_le` |
| Bray (2019b), §3 | The exogenous and endogenous transition matrices `F_x`, `F_y(σ, x)`, the demeaning matrix `Ω`, and `P_σ` in terms of them | `ExoMDP.omegaMat`, `ExoMDP.comega_mulVec`, `ExoMDP.clamMat_mulVec`, `ExoMDP.FxMat`, `ExoMDP.FxMat_isStochastic`, `ExoMDP.FyMat`, `ExoMDP.FyMat_isStochastic`, `ExoMDP.Pmat_apply`, `ExoMDP.cPmat_mulVec_lift`, `ExoMDP.clamP_mulVec` |
| Bray (2019b), Lemma 6 | `σ(F) = ρ(Δ_i F)` | The definition `subradius`, characterized by `spectralRadius_deltaQ` |
| Bray (2019b), Lemma 7 | `σ(F) = ρ(ΩF)` for every stochastic `F` | `ExoMDP.omega_mulVec`, `ExoMDP.omega_mulVec_const`, `ExoMDP.omega_mulVec_add_const`, `ExoMDP.norm_omega_mulVec_le`, `ExoMDP.sp_omega_mulVec`, `ExoMDP.omegaF_pow_mulVec_omega`, `ExoMDP.specRad_omega_eq_subradius` |
| Bray (2019b), Lemma 4 | Every eigenvalue of `Δ_X F_x` is an eigenvalue of `ΔF(p)`, so `σ(F_x) ≤ σ(F(p))` | `ExoMDP.spectrum_exo_subset`, `ExoMDP.subradius_FxMat_le` |
| Bray (2019b), Prop 5 | `ρ(ΛF(p)) ≤ max_x ‖ΩF_y(p, x)‖`; endogenous iteration is strictly faster when `σ(F_x)` exceeds this bound | `ExoMDP.endoRadius_le_of_vecNorm`, `ExoMDP.endoRadius_lt_subradius_of_vecNorm`, `ExoMDP.endo_strictly_faster`, `ExoMDP.endo_eval_strictly_faster` |
| Bray (2019b), Cor 2(a), (b) | The bound under the Frobenius norm and the largest singular value | `ExoMDP.endoRadius_le_l2`, `ExoMDP.endoRadius_le_frobenius`, `ExoMDP.endoRadius_le_singularValue` |
| Bray (2019b), Cor 2(c) | The bound under the maximum absolute row sum norm | `ExoMDP.endoRadius_le_rowSum` |
| Bray (2019b), Cor 2(d) | The bound under the maximum absolute column sum norm | `ExoMDP.endoRadius_le_colSum` |
| Bray (2019b), Cor 2(e); Hajnal (1958) | The bound under the Hajnal seminorm | `ExoMDP.spy_Pmat_mulVec_le`, `ExoMDP.endoRadius_le_hajnal` |
| Bray (2019b), Cor 3; Hajnal (1958) | Non-ergodic `F_x` and scrambling `F_y(p, x)`: endogenous iteration is strictly faster | `ExoMDP.exists_hajnal_lt_one`, `ExoMDP.endoRadius_lt_of_nonergodic_scrambling` |
| Bray (2019b), Cor 4 | If `F_y(p, x) = F_y(p)` for all `x`, endogenous iteration is strictly faster when `σ(F_x) > σ(F_y(p))` | `ExoMDP.Pmat_pow_mulVec_of_Fy_const`, `ExoMDP.endoRadius_le_subradius_Fy`, `ExoMDP.endoRadius_lt_of_Fy_const` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Bray (2019a), Props 6–9 | Bias and variance of simulation-based policy evaluation | Out of scope. |
| Bray (2019a), §4.3–4.4 | Policy evaluation by forward simulation and by solving linear systems | Out of scope; iterative evaluation is covered by `sp_policy_eval_le` and `endo_policy_eval_le`. |
| — | The vanishing-discount limit `(1 − β)v*_β → g` | Not needed for White's theorem. |
