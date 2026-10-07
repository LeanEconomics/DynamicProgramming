# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 1, "Prelude: Examples of Dynamic Programs" (pp. 1–56). Result, equation and
exercise numbers are the book's; page numbers are book pages. Lean names are relative to
`SargentStachurski.PreludeExamples`. Where the Lean statement adds a hypothesis the book
leaves implicit, or departs from the printed statement, see [corrections](corrections.md).

## Appendix A facts used in Chapter 1

| Book | Claim | Lean |
| --- | --- | --- |
| §A.4.2.4 | Bounded measurable functions `bX` | `IsBdd`, `bX`, `const_mem_bX`, `isUniformlyClosed_bX`, `IsBdd.add`, `IsBdd.sub`, `IsBdd.exists_dist` |
| §A.2.2.2 | Contractions; Banach's theorem; global stability | `IsSupContraction`, `IsUniformlyClosed`, `IsSupContraction.iterate`, `IsSupContraction.eq_of_isFixedPt`, `IsSupContraction.exists_limit`, `IsSupContraction.globallyStable` |
| Lemma A.5.19, p. 380 | Order preserving and globally stable implies order stable | `le_of_le_map_of_tendsto`, `le_of_map_le_of_tendsto` |
| p. 8 | `|α ∨ x − α ∨ y| ≤ |x − y|` | `abs_max_sub_max_le` |
| Cor A.5.13, p. 377 | `|sup f − sup g| ≤ sup |f − g|` | `abs_ciSup_sub_ciSup_le` |
| §A.5.4, Lemma A.5.30 | Markov operators; `‖P‖ = 1` | `markovOp`, `integrable_of_mem_bX`, `measurable_markovOp`, `abs_markovOp_le`, `markovOp_mem_bX`, `markovOp_mono`, `markovOp_const`, `markovOp_add`, `markovOp_sub`, `markovOp_smul`, `markovOp_sub_const`, `abs_markovOp_sub_le` |
| Thm A.4.10, Cor A.4.11, p. 367 | Neumann series and global stability of `v ↦ r + βLv` | `IsMarkovLike`, `isMarkovLike_markovOp`, `IsMarkovLike.sub`, `IsMarkovLike.abs_sub_le`, `IsMarkovLike.iterate_mem`, `IsMarkovLike.abs_iterate_le`, `affineOp`, `affineOp_mapsTo`, `affineOp_mono`, `affineOp_contraction`, `affineOp_globallyStable`, `affineOp_iterate_zero`, `affineOp_hasSum` |

## The optimality template (§1.1.1.4, pp. 9–10)

| Book | Claim | Lean |
| --- | --- | --- |
| §1.1.1.2 | Policy operators, `σ`-value functions | `ContractingDP`, `ContractingDP.globallyStable`, `ContractingDP.vσ`, `ContractingDP.vσ_mem`, `ContractingDP.T_vσ`, `ContractingDP.eq_vσ`, `ContractingDP.tendsto_vσ`, `ContractingDP.le_vσ`, `ContractingDP.vσ_le` |
| (1.8), §1.1.1.3, Ex 1.1.3 | Greedy policies, the Bellman operator, `Tv = T_σ v` iff greedy | `ContractingDP.IsGreedy`, `ContractingDP.nonempty_policy`, `ContractingDP.greedy`, `ContractingDP.isGreedy_greedy`, `ContractingDP.bellman`, `ContractingDP.bellman_mapsTo`, `ContractingDP.T_le_bellman`, `ContractingDP.isGreedy_iff`, `ContractingDP.bellman_eq_iSup`, `ContractingDP.bellman_mono` |
| §1.1.1.3 | `T` is a `β`-contraction; VFI | `ContractingDP.bellman_contraction`, `ContractingDP.bellman_globallyStable`, `ContractingDP.vstar`, `ContractingDP.vstar_mem`, `ContractingDP.bellman_vstar`, `ContractingDP.eq_vstar`, `ContractingDP.tendsto_bellman_iterate` |
| Proof of Thm 1.1.1 | `v* = sup_σ v_σ` is the fixed point; optimal iff `v*`-greedy | `ContractingDP.vσ_le_vstar`, `ContractingDP.vσ_eq_vstar_iff`, `ContractingDP.IsOptimal`, `ContractingDP.isOptimal_iff`, `ContractingDP.optimality` |
| Lemma 1.2.3 | `Tv ≤ v ⟹ v* ≤ v` | `ContractingDP.vstar_le_of_bellman_le`, `ContractingDP.le_vstar_of_le_bellman` |
| Algorithms 1.2–1.3, Thm 1.2.2 | HPI and OPI | `ContractingDP.hpiPolicy`, `ContractingDP.vσ_hpi_le_succ`, `ContractingDP.vσ_hpi_eq_vstar`, `ContractingDP.hpi_terminates`, `ContractingDP.opi`, `ContractingDP.opi_step`, `ContractingDP.tendsto_opi` |

## §1.1 A firm problem (pp. 2–18)

| Book | Claim | Lean |
| --- | --- | --- |
| §1.1.1.1, (1.2) | Valuation `v = π + βPv` | `FirmProblem`, `FirmProblem.isMarkovLike_P`, `FirmProblem.valOp`, `FirmProblem.valOp_mapsTo`, `FirmProblem.valOp_contraction`, `FirmProblem.valuation_globallyStable`, `FirmProblem.value`, `FirmProblem.value_mem` |
| (1.3), Ex 1.1.1, p. 4 | `v = (I − βP)⁻¹π` solves the recursion | `FirmProblem.value_eq`, `FirmProblem.value_hasSum` |
| §1.1.1.2, (1.4)–(1.5) | Policies and policy operators, contractions | `FirmPolicy`, `FirmProblem.Tσ`, `FirmProblem.Tσ_eq`, `FirmProblem.Tσ_mapsTo`, `FirmProblem.Tσ_mono`, `FirmProblem.Tσ_contraction`, `FirmProblem.toDP` |
| Ex 1.1.2, p. 6 | `v*` is well defined | `FirmProblem.abs_vσ_le` |
| Thm 1.1.1, (1.6)–(1.8), p. 6 | Bellman equation, optimal policies, greedy characterisation | `FirmProblem.IsGreedy`, `FirmProblem.isGreedy_iff`, `FirmProblem.theorem_1_1_1` |
| Ex 1.1.3, (1.9), p. 8 | `Tv = s ∨ (π + βPv)`; greedy iff `Tv = T_σ v` | `FirmProblem.Tσ_le_max`, `FirmProblem.Tσ_sellPolicy`, `FirmProblem.measurable_sellPolicy`, `FirmProblem.bellman_eq`, `FirmProblem.isGreedy_iff_bellman` |
| Remark 1.1.2, p. 7 | Selling at ties is optimal | `FirmProblem.sellPolicy_optimal` |
| §1.1.3.4, p. 15–16 | Entropic certainty equivalent; below the mean; exact for normal payoffs | `entropicCE`, `entropicCE_le_integral`, `entropicCE_gaussianReal` |
| §1.1.3.4, p. 16 | Value-at-risk | `valueAtRisk`, `valueAtRisk_anti` |
| §1.1.3.6, (1.14), p. 18 | Recursive risk adjustment is well defined; Theorem 1.1.1 for it | `IsShiftMonotone`, `IsShiftMonotone.abs_sub_le`, `FirmProblem.TσK`, `FirmProblem.toDPK`, `FirmProblem.riskAdjusted_optimality` |
| §1.1.3.6, p. 18 | The entropic aggregator | `entropicOp`, `isShiftMonotone_entropicOp` |
| §1.1.3.3, §1.1.3.6 | The mean-variance aggregator is not order preserving | `meanVariance`, `meanVariance_not_monotone` |

## §1.2 Finite MDPs (pp. 19–35)

| Book | Claim | Lean |
| --- | --- | --- |
| §1.2.1.1, (1.15)–(1.16), (1.18) | Finite MDPs, policies, `P_σ`, `r_σ`, policy operators | `FiniteMDP`, `FiniteMDP.Policy`, `FiniteMDP.Q`, `FiniteMDP.Tσ`, `FiniteMDP.Pσ`, `FiniteMDP.rσ`, `FiniteMDP.Tσ_eq_mulVec`, `FiniteMDP.isBdd_of_finite`, `FiniteMDP.abs_sum_sub_le`, `FiniteMDP.Q_mono`, `FiniteMDP.abs_Q_sub_le`, `FiniteMDP.Q_sub_const`, `FiniteMDP.toDP`, `FiniteMDP.finite_policy` |
| Ex 1.2.1, (1.17), p. 21 | `T_σ` is a contraction with fixed point `(I − βP_σ)⁻¹r_σ = ∑(βP_σ)ᵗr_σ` | `FiniteMDP.abs_Pσ_mulVec_le`, `FiniteMDP.vσ_eq_inv`, `FiniteMDP.vσ_hasSum` |
| Ex 1.2.2, p. 21 | `T_σ[−M, M] ⊆ [−M, M]`, `|v_σ| ≤ M` | `FiniteMDP.abs_vσ_le` |
| (1.19)–(1.20), Ex 1.2.3, p. 22 | Bellman operator; contraction | `FiniteMDP.bellman_eq`, `FiniteMDP.bellman_contraction` |
| (1.21), Ex 1.2.4, p. 22 | Greedy policies | `FiniteMDP.exists_greedy`, `FiniteMDP.IsGreedy`, `FiniteMDP.isGreedy_iff` |
| Thm 1.2.1, p. 22 | Optimality | `FiniteMDP.theorem_1_2_1` |
| Thm 1.2.2, p. 24 | VFI, OPI and HPI converge; HPI in finitely many steps | `FiniteMDP.theorem_1_2_2` |
| Lemma 1.2.3, p. 25 | `v ∈ V_D ⟹ v* ≤ v` | `FiniteMDP.vstar_le` |
| Prop 1.2.4, (1.23), p. 25 | `v*` uniquely solves the LP | `FiniteMDP.IsLPFeasible`, `FiniteMDP.lp_solution` |
| §1.2.1.5, (1.24)–(1.26), p. 26 | Cash management | `CashManagement`, `CashManagement.Ξ`, `CashManagement.next`, `CashManagement.profit`, `CashManagement.toMDP`, `CashManagement.optimality` |
| §1.2.2.1, (1.28), p. 29 | Continuous-time MDPs, `v_σ = (δI − Q_σ)⁻¹r_σ` | `CTMDP`, `CTMDP.Qσ`, `CTMDP.rσ`, `CTMDP.vσ` |
| §1.2.2.2, (1.29)–(1.31), Ex 1.2.5, p. 30 | Uniformization | `CTMDP.uniformize`, `CTMDP.sub_Qσ_eq`, `CTMDP.vσ_eq_uniformize` |
| §1.2.2.3, (1.32)–(1.33), Ex 1.2.6, p. 31 | HJB equation; greedy policies | `CTMDP.Q_uniformize`, `sup'_div_add`, `CTMDP.bellman_iff_hjb`, `CTMDP.isGreedy_uniformize_iff` |
| §1.2.2.4, p. 32 | Service rate control | `queueRate`, `queueQ`, `sum_fin_ite_val_eq`, `queueQ_diag`, `serviceRate`, `abs_queueQ_diag_le`, `abs_queueQ_diag_interior`, `abs_queueQ_diag_capacity_one`, `serviceRateMDP`, `serviceRate_optimality` |

## §1.3 Optimal savings (pp. 36–49)

| Book | Claim | Lean |
| --- | --- | --- |
| §1.3.1, Assumption 1.3.1, (1.42) | The model, feasible policies, policy operators | `OptimalSavings`, `SavingsPolicy`, `OptimalSavings.cont`, `OptimalSavings.Pσ`, `OptimalSavings.rσ`, `OptimalSavings.Tσ`, `OptimalSavings.integrable_comp`, `OptimalSavings.abs_cont_le`, `OptimalSavings.isMarkovLike_Pσ`, `OptimalSavings.rσ_mem` |
| Ex 1.3.1, p. 38 | `T_σV ⊆ V` | `OptimalSavings.Tσ_mapsTo` |
| Lemma 1.3.1, (1.44), (1.47), p. 38 | Global stability; Neumann series; limits | `OptimalSavings.Tσ_globallyStable`, `OptimalSavings.vσ_hasSum` |
| (1.48), p. 40 | `v*` well defined | `OptimalSavings.abs_fixedPoint_le` |
| (1.49)–(1.51) | Greedy policies, Bellman operator | `OptimalSavings.objective`, `OptimalSavings.bellmanOp`, `OptimalSavings.bddAbove_objective`, `OptimalSavings.IsGreedy` |
| Ex 1.3.2, p. 42 | `T` is a contraction | `OptimalSavings.bellmanOp_contraction` |
| §1.3.2.2, p. 42 (and §2.3.2) | DP results given greedy policies | `OptimalSavings.toDP`, `OptimalSavings.isGreedy_iff`, `OptimalSavings.bellman_eq`, `OptimalSavings.dp_results` |
| (1.52), p. 43 | CRRA utility; concavity | `crra`, `rpow_sub_one_div_le`, `crra_le_tangent` |
| Ex 1.3.3, p. 43 | Lifetime values bounded above | `crraPath`, `crra_lifetime_bound` |
| (1.53)–(1.55), p. 44 | `η`, the Bellman equation, `v* = η^{−γ}u` | `crraEta`, `crraEta_spec`, `crra_value`, `crra_bellman_le` |
| p. 45 | Consumption growth `(βR)^{1/γ}` | `crra_growth` |

## §1.4 Sequential analysis (pp. 49–53)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.56)–(1.57), p. 51 | Bayes' rule, predictive density | `predDensity`, `bayesUpdate`, `bayesUpdate_mem_Icc`, `bayesUpdate_mul_predDensity`, `integral_predDensity` |
| §1.4.1 | Beliefs are a martingale | `integral_bayesUpdate_mul_predDensity` |
| (1.58), p. 51 | The Bellman operator | `seqBellman`, `seqBellman_mono`, `seqBellman_mem` |
