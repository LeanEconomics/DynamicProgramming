# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 2, "Abstract Decision Processes" (pp. 58–97), with the Appendix A results the
chapter uses. Result, equation and exercise numbers are the book's; page numbers are book
pages. Lean names are relative to `SargentStachurski.AbstractDecisionProcesses`. Where the Lean
statement adds a hypothesis the book leaves implicit, or departs from the printed statement,
see [corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 (`FiniteStates/ContinuousTime`) | `GloballyStable`, Markov matrices, contractions, Blackwell's condition |
| `SpectralRadius` | Volume 1, Chapter 10 | `specRad`, Gelfand's formula, geometric decay of matrix powers (stable LQ controls) |
| `SupContraction`, `ContractingDP`, `MarkovOperator`, `NeumannSeries` | Volume 2, Chapter 1 (`GeneralStates/PreludeExamples`) | `bX`, Banach's theorem on `bX`, Markov operators, `v ↦ r + βLv` |
| `FirmProblem`, `FiniteMDP`, `OptimalSavings` | Volume 2, Chapter 1 | The models of §1.1, §1.2.1 and §1.3 recast as ADPs in §2.3 |

## Appendix A order theory used in Chapter 2

| Book | Claim | Lean |
| --- | --- | --- |
| §A.1.2.10 | Order stability and strong order stability | `OrderStable`, `IncreasesTo`, `DecreasesTo`, `StronglyOrderStable`, `orderStable_of_up_down`, `StronglyOrderStable.orderStable` |
| Lemma A.1.5, p. 337 | Order stability is self-dual | `dualMap`, `dualMap_iterate`, `orderStable_dual_iff`, `stronglyOrderStable_dual_iff` |
| §A.5.1.1, Thm A.5.2, p. 369 | Chain completeness; Knaster–Tarski | `ChainComplete`, `ChainComplete.exists_least`, `ChainComplete.exists_fixedPt_ge`, `ChainComplete.exists_fixedPt_le`, `ChainComplete.exists_fixedPt` |
| Lemma A.5.3, p. 370 | One fixed point in a chain complete space gives order stability | `ChainComplete.orderStable` |
| Example A.5.1, Lemma A.5.4, p. 369 | Order intervals of `ℝ^X` are chain complete | `chainComplete_Icc` |
| §A.5.1.2, Example A.5.2, Ex A.5.5 | Countable Dedekind completeness; `ℝ^X`; duality | `CountablyDedekindComplete`, `countablyDedekindComplete_of_conditionallyCompleteLattice`, `CountablyDedekindComplete.dual` |
| §A.5.1.3, Lemma A.5.5, p. 372 | Order continuity implies order preservation | `OrderContinuous`, `OrderContinuous.monotone` |
| Thm A.5.6, p. 372 | Tarski–Kantorovich | `isLUB_range_succ_iff`, `tarski_kantorovich` |
| Lemma A.5.19, p. 380 | Globally stable and order preserving implies strongly order stable (closed order) | `stronglyOrderStable_of_globallyStable` |
| Lemma A.1.3, Cor A.5.17, p. 379 | Monotone limits in `bX`; `bX` is countably Dedekind complete | `isLUB_of_tendsto_bX`, `tendsto_of_isLUB_bX`, `countablyDedekindComplete_bX` |
| Lemma A.5.33 | Monotone convergence for Markov operators | `tendsto_markovOp` |

## §2.1 Abstract dynamic programs (pp. 58–67)

| Book | Claim | Lean |
| --- | --- | --- |
| Definition 2.1.1 | ADPs `(V, 𝕋)` | `ADP` |
| Definition 2.1.2, (2.1)–(2.2) | Greedy policies, `V_G` | `ADP.IsGreedy`, `ADP.VG` |
| §2.1.1.2 | Well-posed, finite, regular, (strongly) order stable | `ADP.WellPosed`, `ADP.IsFinite`, `ADP.Regular`, `ADP.regular_iff`, `ADP.IsOrderStable`, `ADP.IsStronglyOrderStable`, `ADP.IsStronglyOrderStable.isOrderStable`, `ADP.IsOrderStable.wellPosed` |
| Definitions 2.1.3–2.1.4, (2.3) | The Bellman equation and operator | `ADP.IsBellmanValue`, `ADP.SolvesBellman`, `ADP.greedy`, `ADP.isGreedy_greedy`, `ADP.bellman`, `ADP.isGreedy_of_isBellmanValue`, `ADP.solvesBellman_iff` |
| Lemma 2.1.1, p. 63 | `T` is the supremum, order preserving; `T_σ v = Tv` iff greedy | `ADP.isBellmanValue_bellman`, `ADP.bellman_mono`, `ADP.T_le_bellman`, `ADP.isGreedy_iff` |
| Definition 2.1.5, Lemma 2.1.2, p. 64 | `V_U`, `V_Σ`; `V_Σ ∩ V_G ⊆ V_U` | `ADP.VU`, `ADP.VSig`, `ADP.VSig_inter_VG_subset`, `ADP.vσ`, `ADP.T_vσ`, `ADP.eq_vσ`, `ADP.VSig_eq_range` |
| §2.1.2.1, p. 64 | Optimal policies and the value function | `ADP.IsOptimal`, `ADP.IsValueFunction`, `ADP.IsOptimal.isValueFunction`, `ADP.isOptimal_of_isValueFunction`, `ADP.isOptimal_iff` |
| Definitions 2.1.6–2.1.7, (2.5) | Bellman's principle; fundamental optimality properties (B1)–(B3) | `ADP.BellmanPrinciple`, `ADP.FundamentalOptimality` |
| Lemma 2.1.3, p. 65 | (i) and (ii) | `ADP.bellmanPrinciple_of_solves`, `ADP.exists_solves_iff` |
| Prop 2.1.4, p. 66 | Fundamental optimality iff `v*` is the unique Bellman solution in `V_G` | `ADP.fundamentalOptimality_iff` |
| Ex 2.1.1, p. 66 | Optimal iff `Tv_σ = v_σ` | `ADP.isOptimal_iff_solvesBellman` |
| Thm 2.1.5, p. 66 | A fixed point of `T` iff the fundamental optimality properties | `ADP.fundamentalOptimality_iff_exists_fixed` |
| Cor 2.1.6, p. 67 | The order stable case | `ADP.IsOrderStable.fundamentalOptimality` |
| Thm 2.1.7, p. 67 | Regular, well-posed, chain complete | `ADP.WellPosed.isOrderStable`, `ADP.fundamentalOptimality_of_chainComplete` |

## §2.2 Algorithms and minimization (pp. 67–78)

| Book | Claim | Lean |
| --- | --- | --- |
| §2.2.1.1, Definition 2.2.1, (2.6) | Greedy selectors; Howard and optimistic operators | `ADP.IsSelector`, `ADP.Regular.isSelector_greedy`, `ADP.IsSelector.T_eq`, `ADP.howard`, `ADP.opt`, `ADP.mem_VU_iff` |
| Lemma 2.2.1, p. 69 | (L1)–(L3) | `ADP.bellman_eq_of_howard_eq`, `ADP.mapsTo_VU`, `ADP.bellman_le_opt`, `ADP.iterate_mono_of_le` |
| (2.8)–(2.9), p. 70 | The comparison chains | `ADP.bellman_le_of_le`, `ADP.chain_2_9` |
| Lemma 2.2.2, Remark 2.2.1, p. 70 | `Tⁿv ≼ Wⁿv`, `Tⁿv ≼ Hⁿv`, all increasing | `ADP.iterates_of_mem_VU` |
| Definition 2.2.2 | Convergence of VFI, OPI, HPI | `ADP.VFIConverges`, `ADP.OPIConverges`, `ADP.HPIConverges` |
| Ex 2.2.1, p. 71 | OPI convergence implies VFI convergence | `ADP.opt_one`, `ADP.OPIConverges.vfi` |
| Lemma 2.2.3, p. 71 | `V_U` lies below `v*` | `ADP.IsOrderStable.le_vσ`, `ADP.IsOrderStable.vσ_le`, `ADP.le_vstar_of_mem_VU` |
| Lemma 2.2.4, Cor 2.2.5, p. 71 | Iterates below `v*`; VFI implies OPI and HPI | `ADP.iterates_le_vstar`, `ADP.increasesTo_of_squeeze`, `ADP.VFIConverges.opi_hpi` |
| Thm 2.2.6, p. 72 | Finite ADPs; HPI in finitely many steps | `ADP.VU_nonempty`, `ADP.IsFinite.VSig_finite`, `ADP.exists_succ_eq_of_finite`, `ADP.fundamentalOptimality_of_finite`, `ADP.FundamentalOptimality.exists_vstar` |
| Thm 2.2.7, p. 72 | Chain complete spaces | `ADP.convergence_of_chainComplete` |
| §2.2.2.3, Ex 2.2.2, Thm 2.2.8, p. 73 | Order bounded, order continuous, countably Dedekind complete | `ADP.OrderBounded`, `ADP.IsOrderContinuous`, `ADP.le_of_orderBounded`, `ADP.convergence_of_dedekind` |
| §2.2.3.1 | Min-greedy policies, `T▿`, min-optimality, (B1')–(B3') | `ADP.IsMinGreedy`, `ADP.VGmin`, `ADP.MinRegular`, `ADP.MinOrderBounded`, `ADP.IsMinBellmanValue`, `ADP.SolvesMinBellman`, `ADP.IsMinValueFunction`, `ADP.IsMinOptimal`, `ADP.MinBellmanPrinciple`, `ADP.MinFundamentalOptimality`, `ADP.VD`, `ADP.MinVFIConverges` |
| §2.2.3.2, Ex 2.2.3, p. 77 | The dual ADP; self-duality | `ADP.dual`, `ADP.dual_dual` |
| Ex 2.2.4, p. 77 | The min/max dictionary, (i)–(ix) | `ADP.isMinGreedy_iff`, `ADP.minRegular_iff`, `ADP.minOrderBounded_iff`, `ADP.isMinBellmanValue_iff`, `ADP.dual_opt_howard`, `ADP.isMinValueFunction_iff`, `ADP.isMinOptimal_iff`, `ADP.VGmin_eq`, `ADP.dual_VSig`, `ADP.WellPosed.dual`, `ADP.dual_vσ` |
| Ex 2.2.5–2.2.6, p. 77–78 | Bellman's principle and fundamental optimality under duality; min-VFI | `ADP.minBellmanPrinciple_iff`, `ADP.minFundamentalOptimality_iff`, `ADP.minVFIConverges_iff` |
| Thm 2.2.9, Cor 2.2.10, p. 78 | The minimization versions of Thm 2.1.5 and Cor 2.1.6 | `ADP.minFundamentalOptimality_iff_exists_fixed`, `ADP.IsOrderStable.minFundamentalOptimality` |

## §2.3.1–2.3.3 Firm valuation, optimal savings, finite MDPs (pp. 79–84)

| Book | Claim | Lean |
| --- | --- | --- |
| §2.3.1, (2.12), Ex 2.3.1 | The firm ADP `(bX, 𝕋_FV)`; order preserving self-maps | `FirmProblem.adp`, `FirmProblem.exercise_2_3_1`, `FirmProblem.adp_wellPosed`, `FirmProblem.adp_isOrderStable` |
| (2.13), p. 80 | Greedy policies; regularity; `T = (1.9)` | `FirmProblem.adp_isGreedy_iff`, `FirmProblem.adp_regular`, `FirmProblem.adp_bellman_apply` |
| Ex 2.3.2–2.3.3, p. 80 | Order continuity; order boundedness | `FirmProblem.adp_isOrderContinuous`, `FirmProblem.adp_orderBounded` |
| §2.3.1 with Thm 2.2.8 | Optimality and convergence | `FirmProblem.adp_optimality` |
| §2.3.2, (1.42) | The savings ADP `(bℝ₊, 𝕋_OS)` | `consumeAll`, `OptimalSavings.adp`, `OptimalSavings.adp_wellPosed`, `OptimalSavings.adp_isOrderStable` |
| (2.14)–(2.15), p. 81 | Greedy policies are those of (1.49); regularity is Lemma 1.3.2 (i); `T = (1.51)` | `OptimalSavings.adp_isGreedy_iff`, `OptimalSavings.adp_regular_iff`, `OptimalSavings.adp_bellman_apply` |
| Ex 2.3.4–2.3.5, p. 82 | `u ∈ V_U` for `u ≥ 0`; order bounded and order continuous | `OptimalSavings.exercise_2_3_4`, `OptimalSavings.adp_orderBounded`, `OptimalSavings.adp_isOrderContinuous` |
| §2.3.2 with Thm 2.2.8 | Optimality and convergence | `OptimalSavings.adp_optimality` |
| §2.3.3.1, (2.16), p. 82 | The MDP ADP `(ℝ^X, 𝕋_MDP)` | `isLUB_of_tendsto_subtype`, `isGLB_of_tendsto_subtype`, `FiniteMDP.nonempty_policy`, `FiniteMDP.adp`, `FiniteMDP.adp_wellPosed`, `FiniteMDP.adp_isOrderStable`, `FiniteMDP.adp_isOrderContinuous` |
| Ex 2.3.6–2.3.9, p. 82–83 | Order bounded; (2.17) greedy; Bellman operator (2.18); regular | `FiniteMDP.rbar`, `FiniteMDP.abs_r_le_rbar`, `FiniteMDP.adp_orderBounded`, `FiniteMDP.exercise_2_3_7`, `FiniteMDP.adp_bellman_apply`, `FiniteMDP.adp_regular` |
| Prop 2.3.1, p. 83 | Optimality; VFI, OPI, HPI converge; HPI finite | `FiniteMDP.proposition_2_3_1` |
| Ex 2.3.10, p. 84 | On `V̂ = [−M, M]`, strongly order stable; Thm 2.2.7 applies | `FiniteMDP.Vhat`, `FiniteMDP.mem_Vhat_iff`, `FiniteMDP.Tσ_mapsTo_Vhat`, `FiniteMDP.adpHat`, `FiniteMDP.vσ_mem_Vhat`, `FiniteMDP.adpHat_isStronglyOrderStable`, `FiniteMDP.adpHat_regular`, `FiniteMDP.exercise_2_3_10` |

## §2.3.4 Distributional dynamic programming (pp. 84–89)

| Book | Claim | Lean |
| --- | --- | --- |
| §A.5.5 | First order stochastic dominance, a partial order on distributions | `FOSD`, `FOSD.refl`, `FOSD.trans`, `FOSD.antisymm` |
| §2.3.4.1 | `ℋ` and the order `⊴`; the model | `DistValue`, `distOrder`, `DDP`, `DDPPolicy`, `DDP.Pσ`, `DDP.isMarkov_Pσ`, `DDP.rσ`, `DDP.measurable_rσ` |
| (2.21)–(2.22) | The distributional policy operator | `DDP.Dσ`, `DDP.measurable_affine`, `DDP.measurable_affine_x`, `DDP.Dσ_apply` |
| (2.23), p. 85 | `D_σ` on test functions | `DDP.integral_Dσ`, `DDP.integral_Dσ'`, `DDP.comp_moment` |
| Prop 2.3.2, p. 85 | `D_σ` maps `ℋ` to itself and is order preserving | `DDP.Dσℋ`, `DDP.Dσℋ_coe`, `DDP.Dσℋ_mono`, `DDP.ddpADP` |
| §2.3.4.2, Ex 2.3.11, p. 87 | `W₁`; `D_σ` is a `β`-contraction | `DDP.integrable_of_lipschitz`, `DDP.lipschitz_contraction`, `DDP.W1`, `DDP.W1_contraction` |

## §2.3.5 LQ control (pp. 88–96)

| Book | Claim | Lean |
| --- | --- | --- |
| §2.3.5.1–2.3.5.2 | The problem; the Loewner order on `𝒫`; (2.26) | `LQProblem`, `psdCone`, `LQProblem.gainDen`, `LQProblem.cost`, `LQProblem.posSemidef_iff_real`, `LQProblem.posDef_iff_real`, `LQProblem.posSemidef_transpose_mul_mul`, `LQProblem.gainDen_posDef`, `LQProblem.dotProduct_mulVec_comm_of_symm`, `LQProblem.mulVec_dotProduct`, `LQProblem.dotProduct_transpose_mul_mul`, `LQProblem.quad_add` |
| (2.27)–(2.28), Ex 2.3.13–2.3.14, p. 90 | The Riccati and gain maps; `R(P) = T_{F(P)}P`; `R` maps `𝒫` to itself | `LQProblem.riccati`, `LQProblem.gain`, `LQProblem.gainDen_mul_gain`, `LQProblem.riccati_eq_TF`, `LQProblem.riccati_posSemidef` |
| Lemma 2.3.3, p. 91 | `F(P)x` is the unique minimizer | `LQProblem.cost_gain_add`, `LQProblem.gain_isMinimizer` |
| Example 2.3.1, (2.31), p. 91–92 | Scalar lifetime costs; `F = −0.6` beats `F = −0.9` | `LQProblem.scalar_lifetimeCost`, `LQProblem.scalar_compare` |
| §2.3.5.3, Ex 2.3.15, p. 92 | Stable control matrices; `xₜ → 0` | `LQProblem.closedLoop`, `LQProblem.IsStable`, `LQProblem.IsStable.entry_decay`, `LQProblem.IsStable.tendsto_entry`, `LQProblem.IsStable.tendsto_state` |
| (2.32), Ex 2.3.16, p. 93 | `T_F`; order preserving self-maps of `𝒫` | `LQProblem.TF`, `LQProblem.TF_eq`, `LQProblem.TF_expand`, `LQProblem.TF_posSemidef`, `LQProblem.TF_transpose`, `LQProblem.TF_mono`, `LQProblem.TFpsd` |
| Lemma 2.3.5, (2.30), (2.35), p. 93 | `T_F` globally stable with fixed point `P_F`; `xᵀP_F x = ℓ_F(x)` | `LQProblem.costMat`, `LQProblem.discCost`, `LQProblem.transpose_mul_mul_apply`, `LQProblem.tendsto_transpose_mul_mul_zero`, `LQProblem.TF_iterate`, `LQProblem.PF`, `LQProblem.IsStable.hasSum_PF`, `LQProblem.IsStable.tendsto_TF_iterate`, `LQProblem.tendsto_TF`, `LQProblem.IsStable.TF_PF`, `LQProblem.IsStable.eq_PF`, `LQProblem.IsStable.PF_posSemidef`, `LQProblem.TFpsd_iterate`, `LQProblem.IsStable.globallyStable`, `LQProblem.IsStable.hasSum_cost` |
| §2.3.5.4, Lemma 2.3.6, p. 93 | The LQ ADP; strong order stability | `LQProblem.StablePolicy`, `LQProblem.adp`, `LQProblem.adp_isStronglyOrderStable` |
| Ex 2.3.17, p. 94 | `F = F(P)` iff `T_F P ≼ T_G P` for all `G` | `LQProblem.gain_iff_TF_le` |
| Lemmas 2.3.7–2.3.8, p. 94 | `F(P)` is min-greedy on `𝒫_S`; `T▿ = R` there | `LQProblem.PS`, `LQProblem.eq_of_dotProduct_mulVec_eq`, `LQProblem.gain_isMinGreedy`, `LQProblem.isMinBellmanValue_riccati` |
| Lemma 2.3.9, p. 95 | Riccati, Bellman min-equation and (2.26) agree on `𝒫_S` | `LQProblem.riccati_tfae` |
| §2.3.5.8, (2.38), p. 95 | Optimality given a stabilising Riccati solution | `LQProblem.optimality` |
