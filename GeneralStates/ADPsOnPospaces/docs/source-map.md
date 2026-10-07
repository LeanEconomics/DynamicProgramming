# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 3, "ADPs on Pospaces" (pp. 98–122), with the Appendix A results the chapter uses.
Result, equation and exercise numbers are the book's; page numbers are book pages. Lean names
are relative to `SargentStachurski.ADPsOnPospaces`. Where the Lean statement adds a hypothesis
the book leaves implicit, or departs from the printed statement, see
[corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 (`FiniteStates/ContinuousTime`) | `GloballyStable`, contractions |
| `SupContraction`, `ContractingDP`, `MarkovOperator`, `NeumannSeries`, `FiniteMDP`, `OptimalSavings`, `SequentialAnalysis` | Volume 2, Chapter 1 (`GeneralStates/PreludeExamples`) | `bX` as a set of functions, Markov operators, the finite MDP, optimal savings, Bayes' rule and (1.58) |
| `OrderTheory`, `ADP`, `Algorithms`, `Minimization`, `BXOrder`, `SavingsADP`, `MDPADP` | Volume 2, Chapter 2 (`GeneralStates/AbstractDecisionProcesses`) | ADPs, the fundamental optimality properties, VFI/OPI/HPI, the dual ADP, the savings and MDP ADPs |

## Appendix A facts used in Chapter 3

| Book | Claim | Lean |
| --- | --- | --- |
| Lemma A.5.18, p. 380 | A net converging to an upper bound has it as supremum | `isLUB_of_tendsto_of_le`, `isGLB_of_tendsto_of_le` |
| §A.5.3.2, (A.22) | Sup-nonexpansive metrics; the infimum version | `IsSupNonexpansive`, `IsInfNonexpansive`, `isInfNonexpansive_iff`, `isSupNonexpansive_real`, `isSupNonexpansive_pi` |
| Lemma A.5.21, p. 381 | `T` inherits the common contraction modulus | `ADP.lemma_A_5_21` |
| Exercise A.2.1, p. 346 | Asymptotically contracting with a fixed point implies globally stable | `exercise_A_2_1` |
| §A.4.2.4, §A.5.3.3 | `bX` with the supremum norm is a Banach lattice | `BM`, `BM.ext`, `BM.bddAbove`, `BM.const`, `BM.toFun_injective`, `BM.zero`, `BM.add`, `BM.neg`, `BM.sub`, `BM.smulReal`, `BM.nsmul`, `BM.zsmul`, `BM.addCommGroup`, `BM.supNorm`, `BM.abs_le_supNorm`, `BM.supNorm_le`, `BM.supNorm_nonneg`, `BM.normedAddCommGroup`, `BM.norm_def`, `BM.abs_le_norm`, `BM.norm_le`, `BM.abs_sub_le_dist`, `BM.dist_le`, `BM.module`, `BM.normedSpace`, `BM.lattice`, `BM.le_def`, `BM.isOrderedAddMonoid`, `BM.hasSolidNorm`, `BM.completeSpace` |
| Cor A.5.17, p. 379 | `bX` is countably Dedekind complete | `BM.countablyDedekindComplete` |
| Prop A.5.23, p. 382 | With the order unit `𝟙`, the norm of `bX` is sup-nonexpansive (and inf-nonexpansive) | `BM.isSupNonexpansive`, `BM.isInfNonexpansive` |
| Lemma 1.3.1 on `bX` | Uniform and norm convergence; transfer of global stability | `BM.mem_bX`, `BM.tendsto_of_tendstoUniformly`, `BM.tendstoUniformly_of_tendsto`, `BM.globallyStable_of_bX` |

## §3.1 Adding topology (pp. 98–105)

| Book | Claim | Lean |
| --- | --- | --- |
| §3.1.1, p. 99 | Globally stable ADPs; well-posedness | `ADP.IsGloballyStable`, `ADP.IsGloballyStable.wellPosed`, `ADP.IsGloballyStable.tendsto_vσ` |
| Lemma 3.1.1, p. 99 | Globally stable implies strongly order stable | `ADP.IsGloballyStable.isStronglyOrderStable`, `ADP.IsGloballyStable.isOrderStable` |
| Thm 3.1.2, p. 99 | A fixed point of `T` gives (i)–(ii) | `ADP.monotone_iterate_of_le`, `ADP.Regular.bellman_monotone`, `ADP.Regular.iterate_T_le_bellman`, `ADP.theorem_3_1_2` |
| Cor 3.1.3, p. 100 | Finite ADPs | `ADP.corollary_3_1_3` |
| Thm 3.1.4, p. 100 | Order bounded, countably Dedekind complete | `ADP.bellman_iterate_le_of_bound`, `ADP.theorem_3_1_4` |
| §3.1.2, p. 101 | Semi-regularity; geometric convergence of VFI | `ADP.IsSemiRegular`, `ADP.VFIGeometric`, `ADP.isGloballyStable_of_contraction` |
| Thm 3.1.5, p. 101 | Contracting policy operators | `ADP.theorem_3_1_5`, `ADP.theorem_3_1_5_needs_nonempty` |
| §3.1.3 | Min-selectors, min-OPI, min-HPI and their dual forms | `ADP.IsMinSelector`, `ADP.MinOPIConverges`, `ADP.MinHPIConverges`, `ADP.isMinSelector_iff`, `ADP.dual_opt_iterate`, `ADP.dual_howard_iterate`, `ADP.minOPIConverges_iff`, `ADP.minHPIConverges_iff`, `ADP.min_of_dual`, `ADP.IsGloballyStable.dual` |
| Thm 3.1.6, p. 102 | Min-version of Theorem 3.1.2 | `ADP.theorem_3_1_6` |
| Thm 3.1.7, p. 102 | Min-version of Theorem 3.1.5 | `ADP.theorem_3_1_7`, `vShapeOrder`, `vShapeDist`, `vShapeDist_metric`, `vShape_isLUB`, `vShape_sup_not_inf` |
| Thm 3.1.8, p. 102 | Min-version of Theorem 3.1.4 | `ADP.theorem_3_1_8` |
| §3.1.4, (3.2) | Policy plans and their lifetime values | `ADP.planComp`, `ADP.planComp_succ`, `ADP.planComp_mono`, `ADP.planValue` |
| Assumption 3.1.1, p. 103 | Common contraction modulus, bounded one-step moves | `ADP.Assumption311`, `ADP.Assumption311.dist_planComp` |
| Lemma 3.1.9, p. 104 | (i) the limit (3.2) exists and is independent of `v`; (ii) global stability; (iii) a solution of `v = ⋁ T_σ v` | `ADP.Assumption311.exists_planValue`, `ADP.Assumption311.tendsto_planValue`, `ADP.Assumption311.planValue_eq`, `ADP.Assumption311.continuous_globallyStable`, `ADP.Assumption311.exists_solvesBellman` |
| Thm 3.1.10, p. 105 | Optimality; stationary policies dominate plans | `ADP.theorem_3_1_10` |

## §3.2.1 Discrete MDPs and Q-factors (pp. 105–108)

| Book | Claim | Lean |
| --- | --- | --- |
| §3.2.1.1, p. 106 | The finite MDP via Corollary 3.1.3; HPI in finitely many steps | `globallyStable_of_supContraction`, `FiniteMDP.adp_isGloballyStable`, `FiniteMDP.section_3_2_1_1` |
| Ex 3.2.1, p. 106 | Countable MDP on `bX`: (i) ADP, (ii) optimality, (iii) convergence | `CountableMDP`, `CountableMDP.Policy`, `CountableMDP.nonempty_policy`, `CountableMDP.summable_mul`, `CountableMDP.abs_tsum_le`, `CountableMDP.Q`, `CountableMDP.Q_mono`, `CountableMDP.abs_Q_sub_le`, `CountableMDP.Tσ`, `CountableMDP.adp`, `CountableMDP.adp_contraction`, `CountableMDP.adp_regular`, `CountableMDP.adp_isGloballyStable`, `CountableMDP.exercise_3_2_1` |
| (3.4)–(3.6), Ex 3.2.2, p. 107 | Q-factor policy operators; `(ℝ^G, 𝕊)` is an ADP | `FiniteMDP.G`, `FiniteMDP.finite_G`, `FiniteMDP.pairOf`, `FiniteMDP.Sσ`, `FiniteMDP.Sσ_mono`, `FiniteMDP.qadp` |
| Ex 3.2.3, p. 107 | Greedy iff `σ(x) ∈ argmax q(x, ·)` | `FiniteMDP.exercise_3_2_3`, `FiniteMDP.exercise_3_2_3_converse`, `exercise_3_2_3_converse_fails`, `FiniteMDP.exists_qgreedy`, `FiniteMDP.qadp_regular` |
| Ex 3.2.4, (3.7), p. 107 | The Q-factor Bellman operator | `FiniteMDP.exercise_3_2_4` |
| Ex 3.2.5, p. 108 | `S_σ` is a `β`-contraction | `FiniteMDP.exercise_3_2_5`, `FiniteMDP.qadp_isGloballyStable` |
| Ex 3.2.6, p. 108 | Optimality; VFI, OPI, HPI; HPI finite | `FiniteMDP.exercise_3_2_6` |

## §3.2.2 Optimal savings (pp. 108–109)

| Book | Claim | Lean |
| --- | --- | --- |
| (3.8) | The savings ADP on the Banach lattice `bℝ₊` | `OptimalSavings.TBM`, `OptimalSavings.adpBM`, `OptimalSavings.adpBM_isGloballyStable`, `OptimalSavings.adpBM_orderBounded`, `OptimalSavings.adpBM_contraction` |
| (3.9)–(3.10), p. 109 | The Bellman equation and greedy policies | `OptimalSavings.adpBM_isGreedy_iff`, `OptimalSavings.adpBM_bellman_apply` |
| Prop 3.2.1, p. 108 | Strongly continuous case, via Theorem 3.1.4 | `OptimalSavings.proposition_3_2_1` |
| Remark 3.2.1, p. 108 | Via Theorem 3.1.5 | `OptimalSavings.remark_3_2_1` |
| Ex 3.2.7, p. 109 | Greedy policies for `v ∈ bcℝ₊`; `T` maps `bcℝ₊` into itself | `OptimalSavings.continuous_cont`, `OptimalSavings.continuous_objective`, `OptimalSavings.argmaxSet`, `OptimalSavings.argmaxSet_nonempty`, `OptimalSavings.isClosed_argmaxSet`, `OptimalSavings.greedyBM`, `OptimalSavings.greedyBM_mem`, `OptimalSavings.isClosed_le_greedyBM`, `OptimalSavings.greedyPolicy`, `OptimalSavings.continuous_bellmanOp`, `OptimalSavings.exercise_3_2_7` |
| Prop 3.2.2, p. 109 | Weakly continuous case, via Theorem 3.1.5 with `V₀ = bcℝ₊` | `OptimalSavings.isClosed_bc`, `OptimalSavings.proposition_3_2_2` |

## §3.2.3 No-discount optimal stopping (pp. 110–116)

| Book | Claim | Lean |
| --- | --- | --- |
| §3.2.3.1–3.2.3.3, (3.14), (3.16) | The problem, `Ē`, policies `σ ≥ σ̄` | `NoDiscountStopping`, `NoDiscountStopping.Ebar`, `NoDiscountStopping.measurableSet_Ebar`, `NoDiscountStopping.Policy`, `NoDiscountStopping.barPolicy` |
| (3.18)–(3.20) | Policy operators `T_E g = h_E + K_E g` | `NoDiscountStopping.Pop`, `NoDiscountStopping.K`, `NoDiscountStopping.hcost`, `NoDiscountStopping.T`, `NoDiscountStopping.K_apply_mem`, `NoDiscountStopping.K_apply_notMem`, `NoDiscountStopping.T_apply_mem`, `NoDiscountStopping.T_apply_notMem` |
| (3.20) | `K_E` is linear and positive | `NoDiscountStopping.K_add`, `NoDiscountStopping.K_smul`, `NoDiscountStopping.K_sub`, `NoDiscountStopping.K_mono`, `NoDiscountStopping.K_nonneg`, `NoDiscountStopping.K_const_le`, `NoDiscountStopping.K_zero`, `NoDiscountStopping.K_sum`, `NoDiscountStopping.iterate_K_mono`, `NoDiscountStopping.iterate_K_nonneg`, `NoDiscountStopping.iterate_K_smul`, `NoDiscountStopping.iterate_K_sub` |
| (3.17) | `ℙ_x{τ_E ≥ n} = (K_Eⁿ𝟙)(x) ≤ ℙ_x{τ̄ ≥ n}` | `NoDiscountStopping.surv`, `NoDiscountStopping.surv_nonneg`, `NoDiscountStopping.surv_succ_le`, `NoDiscountStopping.surv_anti`, `NoDiscountStopping.K_le_of_subset`, `NoDiscountStopping.surv_le_surv_bar` |
| Assumption 3.2.1, p. 112 | `sup_x 𝔼_x τ̄ < ∞` | `NoDiscountStopping.Assumption321`, `NoDiscountStopping.assumption321_of_drift` |
| (3.13), Lemma 3.2.3, p. 112 | The `σ`-loss function is finite and bounded | `NoDiscountStopping.iterate_T_zero`, `NoDiscountStopping.sum_apply`, `NoDiscountStopping.hcost_nonneg`, `NoDiscountStopping.norm_hcost_le`, `NoDiscountStopping.sum_surv_le`, `NoDiscountStopping.norm_iterate_T_zero_le`, `NoDiscountStopping.lossFn`, `NoDiscountStopping.tendsto_lossFn`, `NoDiscountStopping.lossFn_hasSum`, `NoDiscountStopping.lossFn_nonneg`, `NoDiscountStopping.lemma_3_2_3` |
| Lemma 3.2.4, p. 112 | `T_E g_E = g_E` | `NoDiscountStopping.dist_T_le`, `NoDiscountStopping.lemma_3_2_4` |
| Lemma 3.2.6, p. 114 | `‖K_Eⁿ f‖ ≤ ‖f‖ sup_x ℙ_x{τ_E ≥ n}` | `NoDiscountStopping.abs_iterate_K_le`, `NoDiscountStopping.lemma_3_2_6` |
| Lemma 3.2.7, (3.22)–(3.23), p. 115 | `sup_x ℙ_x{τ_E ≥ n} → 0` | `NoDiscountStopping.lemma_3_2_7` |
| Lemma 3.2.8, p. 116 | `T_E` is asymptotically contracting | `NoDiscountStopping.iterate_T_sub`, `NoDiscountStopping.lemma_3_2_8` |
| Prop 3.2.5, p. 114 | Every `T_E` is globally stable on `bX₊` | `NoDiscountStopping.proposition_3_2_5_bX`, `NoDiscountStopping.Pop_nonneg`, `NoDiscountStopping.T_nonneg`, `NoDiscountStopping.T_mono`, `NoDiscountStopping.adp`, `NoDiscountStopping.proposition_3_2_5` |
| §3.2.3.5, (3.11) | Min-greedy policies; min-regularity; the Bellman min-operator | `NoDiscountStopping.minGreedy`, `NoDiscountStopping.T_minGreedy_apply`, `NoDiscountStopping.isMinGreedy_minGreedy`, `NoDiscountStopping.adp_minRegular` |
| (3.24), §3.2.3.7 | `g▿* = inf_σ g_σ` is the min-value function | `NoDiscountStopping.vσ_eq_lossFn` |
| Thm 3.2.9, p. 116 | Min-optimality and convergence | `NoDiscountStopping.countablyDedekindComplete_nonneg`, `NoDiscountStopping.theorem_3_2_9` |

## §3.2.4 Sequential analysis revisited (pp. 117–121)

| Book | Claim | Lean |
| --- | --- | --- |
| §3.2.4.1, (3.26), (3.30) | The belief kernel | `Belief`, `SeqAnalysis`, `SeqAnalysis.psi_nonneg`, `SeqAnalysis.measurable_psi`, `SeqAnalysis.integrable_psi`, `SeqAnalysis.Q`, `SeqAnalysis.measurable_density`, `SeqAnalysis.isMarkov_Q`, `SeqAnalysis.kappa`, `SeqAnalysis.measurable_kappa`, `SeqAnalysis.P`, `SeqAnalysis.isMarkov_P`, `SeqAnalysis.P_apply`, `SeqAnalysis.integral_P`, `kappa_hits_zero` |
| (3.27)–(3.28), (3.25) | The stopping reduction; agreement with (1.58) | `SeqAnalysis.exitCost`, `SeqAnalysis.stopping`, `SeqAnalysis.minBellman_eq_seqBellman` |
| p. 120 | Triangular discrimination | `SeqAnalysis.triDisc`, `SeqAnalysis.triDisc_integrand_nonneg`, `SeqAnalysis.triDisc_integrand_le`, `SeqAnalysis.integrable_triDisc`, `SeqAnalysis.triDisc_nonneg` |
| Lemma 3.2.11, p. 120 | `Δ(f₀, f₁) > 0` for distinct densities | `SeqAnalysis.lemma_3_2_11` |
| p. 120, (3.32)–(3.33) | Beliefs are a martingale; conditional variance bound | `SeqAnalysis.measurable_val`, `SeqAnalysis.integral_P_id`, `SeqAnalysis.integrable_bounded_mul_psi`, `SeqAnalysis.measurable_bayes`, `SeqAnalysis.abs_bayes_le`, `SeqAnalysis.integral_P_sq`, `SeqAnalysis.variance_ge` |
| Lemma 3.2.12, p. 120 | `𝔼_π τ < 1/δ`, in drift form | `SeqAnalysis.W`, `SeqAnalysis.W_nonneg`, `SeqAnalysis.markovOp_W`, `SeqAnalysis.lemma_3_2_12` |
| Prop 3.2.10, p. 119 | Assumption 3.2.1 holds; min-optimality and convergence | `SeqAnalysis.bounds_of_notMem_Ebar`, `SeqAnalysis.assumption321`, `SeqAnalysis.proposition_3_2_10` |
