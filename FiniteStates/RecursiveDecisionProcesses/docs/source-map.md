# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 8, "Recursive Decision Processes" (pp. 247–291). Result, equation and
exercise numbers are the book's; page numbers are book pages. Lean names are
relative to `SargentStachurski.RecursiveDecisionProcesses`. Where the Lean statement
adds a hypothesis the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## Earlier-chapter facts restated

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, Ch. 1–3 | Markov matrices, contractions, Banach's theorem, Prop 2.2.7, Blackwell's condition, Lemma 2.2.2 | `IsMarkov`, `IsDistribution`, `GloballyStable`, `IsContractionOn`, `IsContractionOn.exists_fixedPt`, `isContractionOn_of_blackwell`, `abs_sup'_sub_sup'_le` |
| Vol. 1, (1.15), Thm 1.2.1, Ex 2.2.28 | Spectral radius, Gelfand, Neumann series, monotonicity | `specRad`, `tendsto_norm_pow_zero`, `neumann_series`, `specRad_le_of_le` |
| Vol. 1, Thm 2.3.1 | Perron–Frobenius, nonnegative and irreducible cases | `perron_frobenius`, `Irreducible`, `Irreducible.exists_pos_eigenvector` |
| Vol. 1, Thm 6.1.1, Thm 6.1.5, Example 6.1.2, Prop 6.1.6 | Linear valuation, eventual contractions, affine maps | `inv_mulVec_eq_tsum`, `specRad_smul_isMarkov`, `globallyStable_of_iterate_contraction`, `affineOp`, `isFixedPt_affineOp_inv`, `globallyStable_of_abs_sub_le` |
| Vol. 1, p. 45, Thm 7.1.1, Thm 7.1.3 | Conjugacy, Knaster–Tarski, Du | `GloballyStableOn`, `globallyStableOn_iff_of_conj`, `knaster_tarski`, `du_concave`, `du_convex`, `exists_delta_of_lt` |
| Vol. 1, Ex 7.1.7–7.1.8, Thm 7.1.4 | `F(t) = (h + t^{1/θ})^θ`, the map `G` | `posCone`, `powF`, `concaveOn_powF`, `powG`, `powG_mapsTo`, `powG_monotoneOn`, `globallyStableOn_powG` |
| Vol. 1, §7.3.1 | Entropic, Kreps–Porteus and quantile certainty equivalents | `entR`, `entR_add_const`, `isCertEquiv_entR`, `kpR`, `kpR_pos`, `isCertEquiv_kpR`, `concaveOn_kpR`, `quantR`, `isCertEquiv_quantR`, `quantR_add_const` |
| Vol. 1, (7.23), Prop 7.2.3 | Epstein–Zin Koopmans operators | `ezK`, `ezK_mapsTo`, `ezB`, `powMap_ezK`, `irreducible_ezB`, `globallyStableOn_ez` |

## §8.1 Definition and properties (pp. 247–263)

| Book | Claim | Lean |
| --- | --- | --- |
| (8.1)–(8.3), p. 247 | An RDP `(Γ, V, B)`: monotone (8.2), consistent (8.3) | `RDP`, `RDP.IsFeasible`, `RDP.Policy`, `RDP.defaultPolicy`, `RDP.policy_nonempty` |
| Example 8.1.1, (8.4), p. 248 | MDPs as RDPs | `MDP`, `kernelAt`, `isMarkov_kernelAt`, `MDP.toRDP`, `MDP.toRDP_B`, `MDP.toRDP_Tσ` |
| Example 8.1.2, p. 248 | Cake eating | `cakeEating` |
| Example 8.1.3, (8.5)–(8.6), Ex 8.1.1, p. 249 | Optimal stopping | `stopping`, `stopping_T` |
| Example 8.1.4, (8.7), Ex 8.1.2, pp. 249–250 | The Stokey–Lucas form is an MDP | `stokeyLucas`, `stokeyLucas_B` |
| Example 8.1.5, (8.8), Ex 8.1.3, p. 250 | State-dependent discounting | `MDP.withDiscount` |
| Example 8.1.6, (8.9), Ex 8.1.4, p. 250 | Risk-sensitive preferences, any `θ ≠ 0` | `MDP.riskSensitive`, `MDP.riskSensitive_B` |
| Example 8.1.7, (8.10), Ex 8.1.5, p. 250 | Epstein–Zin preferences on `(0, ∞)^X` | `ezAgg_monotoneOn`, `MDP.epsteinZin`, `MDP.epsteinZin_B` |
| Example 8.1.8, p. 251 | Shortest paths | `pathRDP` |
| (8.12), Ex 8.1.6, p. 251 | Policy operators are order-preserving self-maps of `V` | `RDP.Tσ`, `RDP.Tσ_apply`, `RDP.Tσ_mapsTo`, `RDP.Tσ_monotoneOn` |
| §8.1.2.2, pp. 252–253 | `σ`-value functions, well-posedness, global stability | `RDP.WellPosed`, `RDP.IsGloballyStable`, `RDP.IsGloballyStable.wellPosed`, `RDP.vσ`, `RDP.vσ_spec`, `RDP.vσ_mem`, `RDP.isFixedPt_vσ`, `RDP.eq_vσ_of_isFixedPt`, `RDP.tendsto_iterate_Tσ` |
| Examples 8.1.9–8.1.13, 8.1.15–8.1.16 | Stopping and MDP RDPs are globally stable; `v_σ = (I − βP_σ)⁻¹r_σ` | `stopping_isGloballyStable`, `MDP.isGloballyStable`, `MDP.vσ_eq`, `MDP.withDiscount_isGloballyStable` |
| Example 8.1.14, p. 252 | A positive-cost two-cycle is ill-posed | `pathRDP_not_wellPosed` |
| §8.1.2.3, p. 253 | Continuity | `RDP.IsContinuous` |
| (8.13), Ex 8.1.7, p. 254 | Greedy policies; `{T_σ v}` has least and greatest elements | `RDP.IsGreedy`, `RDP.greedy`, `RDP.greedy_mem`, `RDP.isGreedy_greedy`, `RDP.greedyPolicy`, `RDP.isGreatest_Tσ`, `RDP.antiGreedy`, `RDP.isLeast_Tσ` |
| Ex 8.1.8, p. 254 | `T = ⋁ T_σ`; greedy iff `T_σ v = Tv`; `T` an order-preserving self-map | `RDP.T`, `RDP.B_le_T`, `RDP.Tσ_le_T`, `RDP.T_apply_eq_sup'`, `RDP.isGreedy_iff_Tσ_eq_T`, `RDP.Tσ_eq_T_of_isGreedy`, `RDP.T_mapsTo`, `RDP.T_monotoneOn` |
| Ex 8.1.9, (8.14)–(8.15), p. 255 | Iterates of `T` and `T_σ` | `RDP.iterate_T_succ`, `RDP.iterate_Tσ_succ`, `RDP.iterate_T_mono`, `RDP.iterate_Tσ_mono` |
| Algorithms 8.1–8.2, (8.17)–(8.18), Ex 8.1.10, pp. 255–256 | HPI, OPI, the Howard operator; OPI with `m = 1` is VFI | `RDP.howard`, `RDP.opiW`, `RDP.hpiPolicy`, `RDP.hpiValue`, `RDP.hpiValue_succ`, `RDP.opiValue`, `RDP.opiValue_one` |
| (8.19), p. 257 | Value function, optimal policies, Bellman's principle | `RDP.vstar`, `RDP.vσ_le_vstar`, `RDP.IsOptimal`, `RDP.PrincipleOfOptimality` |
| Thm 8.1.1, p. 257 | Optimality for globally stable RDPs, (i)–(v) | `RDP.Comparable`, `RDP.vσ_le_of_Tσ_le`, `RDP.le_vσ_of_le_Tσ`, `RDP.IsGloballyStable.comparable`, `RDP.vσ_le_vσ_greedy`, `RDP.eq_vσ_greedy_of_isFixedPt`, `RDP.vσ_le_of_isFixedPt`, `RDP.hpiValue_mono`, `RDP.exists_hpiValue_succ_eq`, `RDP.isFixedPt_T_hpiValue`, `RDP.vstar_spec`, `RDP.eq_vstar_of_isFixedPt` (i), `RDP.principleOfOptimality` (ii), `RDP.exists_isOptimal` (iii), `RDP.hpi_terminates` (iv), `RDP.tendsto_iterate_T_vσ`, `RDP.opiValue_spec`, `RDP.opi_converges` (v), `RDP.optimality_of_globallyStable` |
| Examples 8.1.18–8.1.19, p. 258 | Stopping and MDPs as special cases | `stopping_isGloballyStable`, `MDP.isGloballyStable` with `RDP.optimality_of_globallyStable` |
| §8.1.3.5, Ex 8.1.11, pp. 258–259 | Nonstationary policies do no better than `v*` | `RDP.nonstationary_le`, `RDP.nonstationary_le_vstar` |
| §8.1.3.6, (8.20), Ex 8.1.12–8.1.13, p. 259 | Bounded RDPs; restriction to `[v₁, v₂]`; `v_σ ∈ [v₁, v₂]` | `RDP.IsBoundedBy`, `RDP.Tσ_mapsTo_Icc`, `RDP.restrictIcc`, `RDP.exists_fixedPt_Icc`, `RDP.vσ_mem_Icc` |
| Ex 8.1.14–8.1.15, p. 260 | MDP and stopping RDPs are bounded | `MDP.isBoundedBy`, `stopping_isBoundedBy`, `RDP.SatisfiesBlackwell.isBoundedBy` |
| Ex 8.1.16, p. 260 | State-dependent discounting is bounded under Prop 6.2.2 | `MDP.absReward`, `MDP.withDiscount_isBoundedBy` |
| Ex 8.1.17, p. 260 | Shortest paths: (8.20) with `v₁ = 0`, `v₂ = C` | `maxCost`, `maxCostToGo`, `maxCost_apply_d`, `iterate_maxCost_d`, `iterate_maxCost_stable`, `maxCost_maxCostToGo`, `maxCostToGo_nonneg`, `maxCostToGo_d`, `pathRDP_isBoundedBy` |
| Thm 8.1.2, p. 260 | Optimality for well-posed bounded RDPs, (i)–(iv) | `RDP.comparable_of_bounded`, `RDP.optimality_of_bounded` |
| (8.21), Prop 8.1.3, Ex 8.1.18, p. 261 | Topologically conjugate RDPs | `continuousOn_comp_pi`, `RDP.isGloballyStable_iff_of_conj` |
| (8.22)–(8.25), Ex 8.1.19, Lemma 8.1.5, Prop 8.1.4, pp. 261–263 | Epstein–Zin RDPs are globally stable under irreducibility | `IsMarkov.exists_pos`, `MDP.ezB_kernelAt_nonneg`, `MDP.ezB_kernelAt_row`, `MDP.epsteinZinHat`, `MDP.epsteinZinHat_Tσ`, `MDP.epsteinZin_Tσ`, `MDP.epsteinZin_B_eq_conj` (Ex 8.1.19), `MDP.epsteinZinHat_isGloballyStable` (Lemma 8.1.5), `MDP.epsteinZin_isGloballyStable` (Prop 8.1.4) |
| Example 8.1.17, p. 254 | The Epstein–Zin Bellman operator | `RDP.T` of `MDP.epsteinZin` with `MDP.epsteinZin_B` |

## §8.2 Types of RDPs (pp. 263–274)

| Book | Claim | Lean |
| --- | --- | --- |
| (8.26), p. 263 | Contracting RDPs | `RDP.IsContracting` |
| Example 8.2.1, p. 263 | Optimal stopping is contracting | `stopping_satisfiesBlackwell`, `stopping_isContracting` |
| Ex 8.2.1, p. 263 | Every MDP is contracting | `MDP.satisfiesBlackwell`, `MDP.isContracting` |
| Ex 8.2.2, p. 263 | Contracting RDPs are continuous | `RDP.IsContracting.isContinuous` |
| Prop 8.2.1, p. 263 | `T` and all `T_σ` are contractions of modulus `β` | `RDP.IsContracting.isContractionOn_Tσ`, `RDP.IsContracting.isContractionOn_T` |
| Cor 8.2.2, p. 264 | Contracting with `V` closed implies globally stable | `RDP.IsContracting.isGloballyStable` |
| Prop 8.2.3, (8.28)–(8.31), p. 264 | `‖v* − v_σ‖ ≤ 2β/(1 − β)‖v_k − v_{k−1}‖` | `RDP.IsContracting.norm_vstar_sub_vσ_le` |
| §8.2.1.3, Ex 8.2.3, p. 265 | Blackwell's condition implies contraction | `RDP.SatisfiesBlackwell`, `RDP.SatisfiesBlackwell.isContracting` |
| Ex 8.2.4, p. 265 | State-dependent discounting with `β ≤ b < 1` is contracting | `MDP.withDiscount_satisfiesBlackwell`, `MDP.withDiscount_isContracting` |
| Ex 8.2.5, p. 265 | Optimal savings satisfies Blackwell's condition | `savings_satisfiesBlackwell` |
| §8.2.1.4, Ex 8.2.6, p. 266 | Job search with quantile preferences is contracting | `quantileJobSearch`, `quantileJobSearch_isContracting` |
| §8.2.1.5, (8.32)–(8.33), Ex 8.2.7, pp. 267–270 | Optimal default is contracting | `optimalDefault`, `optimalDefault_isContracting` |
| (8.34), Prop 8.2.4, p. 271 | Eventually contracting RDPs are globally stable | `RDP.Lσ`, `RDP.IsEventuallyContracting`, `RDP.IsEventuallyContracting.isGloballyStable` |
| Ex 8.2.8, p. 271 | Firm exit with state-dependent interest rates | `firmExit`, `firmExit_T`, `firmExit_isGloballyStable` |
| §8.2.2.2, (8.35), p. 272 | Proof of Prop 6.2.2 | `MDP.withDiscount_isEventuallyContracting`, `MDP.withDiscount_isGloballyStable` |
| (8.36)–(8.39), p. 272 | Convex and concave RDPs | `RDP.IsConvexRDP`, `RDP.IsConcaveRDP` |
| Ex 8.2.9, (8.40)–(8.41), p. 273 | Strict bounds give `δ` | `RDP.exists_delta_convex`, `RDP.exists_delta_concave` |
| Prop 8.2.5, p. 273 | Convex and concave RDPs are globally stable | `RDP.concaveOn_Tσ`, `RDP.convexOn_Tσ`, `RDP.IsConcaveRDP.isGloballyStable`, `RDP.IsConvexRDP.isGloballyStable` |
| (8.42), Ex 8.2.10–8.2.11, p. 274 | MDPs on `V̂` are convex and concave | `MDP.isBoundedBy_eps`, `MDP.toRDP_B_combo`, `MDP.restrict_isConvex_isConcave` |

## §8.3 Further applications (pp. 274–289)

| Book | Claim | Lean |
| --- | --- | --- |
| Prop 8.3.1, p. 275 | Risk-sensitive RDPs are contracting | `MDP.riskSensitive_isContracting`, `MDP.riskSensitive_isGloballyStable` |
| Ex 8.3.1, p. 275 | Quantile RDPs are globally stable | `MDP.quantile`, `MDP.quantile_isContracting`, `MDP.quantile_isGloballyStable` |
| §8.3.1.2, p. 275 | Risk-sensitive job search | `riskSensitiveJobSearch`, `riskSensitiveJobSearch_isContracting` |
| (8.43), §8.3.2.1, p. 276 | Adversarial aggregator `B̂ = inf_d B` and conditions (a)–(d) | `advB`, `AdvConditions`, `AdvConditions.lower_mem`, `AdvConditions.bddBelow`, `AdvConditions.le_advB`, `AdvConditions.advB_le`, `AdvConditions.advB_mono`, `AdvConditions.advB_mem` (8.44), `adversarialRDP` |
| Ex 8.3.3, p. 279 | `inf (f + g) ≥ inf f + inf g` | `iInf_add_iInf_le` |
| Prop 8.3.2, (8.45), p. 278 | The adversarial RDP is concave | `adversarialRDP_isConcaveRDP`, `adversarialRDP_isGloballyStable` |
| (8.46)–(8.47), Ex 8.3.4, Lemma 8.3.3, pp. 279–280 | The perturbed MDP | `PerturbedMDP`, `PerturbedMDP.Bd`, `PerturbedMDP.v₁`, `PerturbedMDP.v₂`, `PerturbedMDP.Bd_const`, `PerturbedMDP.advConditions` (Ex 8.3.4), `PerturbedMDP.isConcaveRDP` (Lemma 8.3.3) |
| (8.48)–(8.49), Prop 8.3.4, p. 281 | Robust control is a concave RDP | `add_mul_iInf`, `robustMDP`, `robustMDP_advB`, `robustMDP_isConcaveRDP` |
| Example 8.3.1, p. 281 | Robust job search | `bddBelow_sum_mul_dist`, `robustJobSearch`, `robustJobSearch_isContracting` |
| (8.50), §8.3.3.2, p. 282 | Penalties are absorbed into the reward | `penalty_absorbed` |
| (8.51), p. 283 | The variational formula for KL divergence | `klDiv`, `AbsCont`, `sum_exp_mul_pos`, `sum_mul_sub_klDiv_le`, `gibbs`, `isDistribution_gibbs`, `absCont_gibbs`, `sum_mul_sub_klDiv_gibbs`, `klDuality` |
| §8.3.3.3, p. 283 | KL-penalised robust control is risk sensitivity | `entropic_isLeast`, `MDP.riskSensitive_B_eq_robust` |
| (8.52), Ex 8.3.5, pp. 283–284 | Smooth ambiguity; ambiguity neutrality gives Epstein–Zin | `smoothB`, `smoothB_neutral`, `sum_dist_mul_pos`, `SmoothAmbiguity`, `SmoothAmbiguity.B` |
| Ex 8.3.6, (8.53), p. 284 | `v₁ ≤ B(v₁) ≤ B(v₂) < v₂` | `SmoothAmbiguity.v₁`, `SmoothAmbiguity.v₂`, `SmoothAmbiguity.B_const`, `SmoothAmbiguity.v₁_le_B`, `SmoothAmbiguity.B_lt_v₂`, `SmoothAmbiguity.B_monotoneOn` |
| Ex 8.3.7, p. 284 | `R = (Γ, [v₁, v₂], B)` is an RDP | `SmoothAmbiguity.B_mem`, `SmoothAmbiguity.toRDP` |
| (8.54), Ex 8.3.8, p. 285 | The transformed RDP `R̂` | `SmoothAmbiguity.ξ`, `SmoothAmbiguity.ζ`, `SmoothAmbiguity.g`, `SmoothAmbiguity.Bhat`, `SmoothAmbiguity.w₁`, `SmoothAmbiguity.w₂`, `SmoothAmbiguity.Bhat_monotoneOn`, `SmoothAmbiguity.Bhat_mem`, `SmoothAmbiguity.toRDPHat`, `SmoothAmbiguity.Bhat_bounds` |
| Ex 8.3.9, p. 285 | `R` and `R̂` are conjugate under `φ(t) = t^κ` | `SmoothAmbiguity.Bhat_pow`, `SmoothAmbiguity.B_eq_conj`, `SmoothAmbiguity.pow_mem`, `SmoothAmbiguity.pow_inv_mem` |
| Lemma 8.3.6, p. 285 | `B̂(x, a, ·)` is concave | `SmoothAmbiguity.concaveOn_psi`, `SmoothAmbiguity.concaveOn_Bhat` |
| Prop 8.3.5, p. 285 | The smooth ambiguity RDP is globally stable | `SmoothAmbiguity.toRDPHat_isConcaveRDP`, `SmoothAmbiguity.toRDP_isGloballyStable` |
| §8.3.5, p. 286 | Min-value function, min-greedy policies, min-Bellman operator | `RDP.neg`, `RDP.neg_Tσ`, `RDP.isGloballyStable_neg_iff`, `RDP.WellPosed.neg`, `RDP.neg_vσ`, `RDP.IsMinGreedy`, `RDP.isMinGreedy_iff`, `RDP.Tmin`, `RDP.neg_T`, `RDP.iterate_neg_T`, `RDP.vmin`, `RDP.IsMinOptimal`, `RDP.neg_vstar`, `RDP.isMinOptimal_iff` |
| Thm 8.3.7, p. 286 | Min-optimality (i)–(iv); min-VFI | `RDP.minHpi_isMinGreedy`, `RDP.minOptimality`, `RDP.tendsto_iterate_Tmin` |
| (8.55)–(8.56), Prop 8.3.8, p. 287 | Shortest paths: concave and globally stable | `pathRDP_minOptimal` with `β = 1` |
| (8.57), Ex 8.3.10, Prop 8.3.9, pp. 288–289 | Negative discount rates | `maxCostToGo`, `pathRDP_isBoundedBy`, `pathRDP_minOptimal` with `β > 1` |
