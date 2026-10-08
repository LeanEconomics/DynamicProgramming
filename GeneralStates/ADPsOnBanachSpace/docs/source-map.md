# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 4, "ADPs on Banach Space" (pp. 123–146), with the Appendix A results the chapter uses.
Result, equation and exercise numbers are the book's; page numbers are book pages. Lean names
are relative to `SargentStachurski.ADPsOnBanachSpace`. Where the Lean statement adds a hypothesis
the book leaves implicit, or departs from the printed statement, see
[corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 | `GloballyStable`, contractions |
| `SupContraction`, `ContractingDP`, `MarkovOperator`, `NeumannSeries`, `FirmProblem` | Volume 2, Chapter 1 | `bX` as a set, Markov operators, the firm problem |
| `OrderTheory`, `ADP`, `Algorithms` | Volume 2, Chapter 2 | ADPs, optimality, VFI/OPI/HPI |
| `Pospace`, `MetricADP`, `BoundedMeasurable` | Volume 2, Chapter 3 | Theorems 3.1.2–3.1.5, Corollary 3.1.3, `bX` as a Banach lattice (`BM`) |

## §4.1.1 Contractions (pp. 124–126)

| Book | Claim | Lean |
| --- | --- | --- |
| Thm 4.1.1, Thm A.2.8, p. 124 | Eventually contracting maps are globally stable, `𝕆(βᵐ)` | `pow_div_le_geometric`, `theorem_4_1_1` |
| §A.5.3.4 | Normalized order units | `BanachLattice.IsNormalizedOrderUnit`, `BanachLattice.IsNormalizedOrderUnit.smul_mono`, `BanachLattice.IsNormalizedOrderUnit.le_add`, `BanachLattice.IsNormalizedOrderUnit.norm_sub_le` |
| Prop A.5.23, p. 382 | The norm is sup-nonexpansive (also inf-nonexpansive; also on subsets) | `BanachLattice.isSupNonexpansive`, `BanachLattice.isInfNonexpansive`, `BanachLattice.isSupNonexpansive_subtype` |
| Lemma 4.1.2, (4.3), p. 125 | Blackwell's condition gives a contraction | `BanachLattice.lemma_4_1_2`, `BanachLattice.lemma_4_1_2_subtype` |
| Thm 4.1.3, (4.4), p. 125 | Optimality for Blackwell ADPs | `BanachLattice.theorem_4_1_3`, `BanachLattice.theorem_4_1_3_univ` |
| p. 126, Ex 4.1.2 | Certainty equivalent operators; `T_σ = r_σ + βM_σ` | `BanachLattice.IsCertaintyEquivalent`, `BanachLattice.exercise_4_1_2`, `BanachLattice.exercise_4_1_2_subtype` |
| Ex 4.1.1, p. 125 | Harrison–Kreps: contraction of modulus `β` on `bX` | `BM.posSMulMono`, `BM.one_apply`, `BM.isNormalizedOrderUnit_one`, `sup'_add_const`, `harrisonKreps`, `exercise_4_1_1` |

## §4.1.2 Order contractions (pp. 126–131)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 127 | Discount operators | `BanachLattice.IsDiscountOperator`, `BanachLattice.IsDiscountOperator.iterate_nonneg`, `BanachLattice.IsDiscountOperator.iterate_mono` |
| Ex 4.1.3, p. 127 | `‖Dⁿh‖ ≤ λ‖h‖` on `E₊` | `BanachLattice.IsDiscountOperator.exercise_4_1_3` |
| §A.4.3, (A.20), Ex A.4.2 | Spectral radius (Gelfand form); `ρ(A) < 1 ⟹ ‖Aᵏ‖ < 1`; `ρ(A) ≤ ‖A‖` | `BanachLattice.specRad`, `BanachLattice.exercise_A_4_2`, `BanachLattice.specRad_le_norm` |
| §A.5.2.2 | Positive operators | `BanachLattice.IsPositiveOp`, `BanachLattice.IsPositiveOp.mono`, `BanachLattice.IsPositiveOp.abs_le`, `BanachLattice.IsPositiveOp.iterate` |
| Example 4.1.1, p. 127 | Positive operators with `ρ < 1` are discount operators | `BanachLattice.example_4_1_1` |
| (4.6), p. 127 | Order contractions, on a value space embedded in `E` | `BanachLattice.IsIsoOrderEmbedding`, `BanachLattice.IsOrderContraction`, `BanachLattice.IsOrderContraction.iterate` |
| Thm 4.1.4, p. 127 | Order contractions are globally stable, `𝕆(βᵐ)` | `BanachLattice.theorem_4_1_4` |
| Example 4.1.2, (4.7), p. 128 | `|Sv − Sw| ≤ |Dv − Dw|` | `BanachLattice.example_4_1_2` |
| Ex 4.1.4, (4.8), p. 128 | `S(v + h) ≤ Sv + Dh` | `BanachLattice.exercise_4_1_4` |
| Thm 4.1.5, p. 128 | Finite order contracting ADPs | `BanachLattice.theorem_4_1_5` |
| Thm 4.1.6, (4.9), p. 129 | Common modulus `D`, semi-regular on `V₀` | `BanachLattice.bellman_orderContraction`, `BanachLattice.theorem_4_1_6` |
| (4.1), Thm 4.1.7, p. 130 | Additive ADPs, finite, `ρ(K_σ) < 1` | `BanachLattice.IsAdditive`, `BanachLattice.IsAdditive.abs_sub`, `BanachLattice.theorem_4_1_7` |
| Thm 4.1.8, p. 130 | Additive ADPs with `K_σ ≤ D` | `BanachLattice.theorem_4_1_8` |

## §4.1.3 Concavity and convexity (pp. 131–132)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 131 | Du's conditions; global stability on `[a, b]` | `BanachLattice.GloballyStableOn`, `BanachLattice.DuConditions`, `BanachLattice.abs_sub_le_of_mem_Icc`, `BanachLattice.norm_sub_le_of_mem_Icc`, `BanachLattice.iterate_mem_Icc` |
| Lemma 4.1.9, p. 131 | Interior conditions imply Du's conditions | `BanachLattice.lemma_4_1_9_concave`, `BanachLattice.lemma_4_1_9_convex`, `BanachLattice.lemma_4_1_9` |
| Thm 4.1.10 (Du), p. 131 | Du's conditions give global stability | `BanachLattice.du_concave`, `BanachLattice.neg_mem_Icc_iff'`, `BanachLattice.iterate_reflect`, `BanachLattice.globallyStableOn_of_reflect`, `BanachLattice.du_convex`, `BanachLattice.theorem_4_1_10`, `BanachLattice.extendIcc`, `BanachLattice.extendIcc_apply`, `BanachLattice.extendIcc_iterate`, `BanachLattice.globallyStable_of_extendIcc`, `BanachLattice.theorem_4_1_10_subtype` |
| Thm 4.1.11, p. 132 | Optimality on `[a, b]` under (a), (b) or (c) | `BanachLattice.countablyDedekindComplete_Icc`, `BanachLattice.theorem_4_1_11` |

## §4.2.1 Firm valuation (pp. 133–137)

| Book | Claim | Lean |
| --- | --- | --- |
| §A.5.4.2 on `bX` | The Markov and multiplication operators on `bX` | `BM.markovLin`, `BM.markovCLM`, `BM.markovCLM_apply`, `BM.markovCLM_isPositive`, `BM.markovCLM_const`, `BM.mulLin`, `BM.mulCLM`, `BM.mulCLM_apply`, `BM.mulCLM_isPositive` |
| (4.10)–(4.11), (4.13) | The firm ADP on `bX`; greedy policies; Bellman equation | `isIsoOrderEmbedding_id`, `FirmProblem.TBM`, `FirmProblem.adpBM`, `FirmProblem.sellBM`, `FirmProblem.sellBM_isGreedy`, `FirmProblem.adpBM_regular`, `FirmProblem.adpBM_bellman_apply`, `FirmProblem.blackwell` |
| Prop 4.2.1, p. 133 | Optimality and convergence | `FirmProblem.proposition_4_2_1` |
| §A.5.4.4, Lemma A.5.32 | Stationary distributions; the Markov operator on `L¹(ψ)`, `‖P‖ ≤ 1` | `L1.ae_ae_of_stationary`, `L1.lintegral_stationary`, `L1.markovFun`, `L1.lintegral_markov_le`, `L1.memLp_markovFun`, `L1.ae_integrable`, `L1.markovFun_congr`, `L1.markovLin`, `L1.markovLin_apply`, `L1.markovLin_norm_le`, `L1.markovCLM`, `L1.markovCLM_norm_le`, `L1.markovCLM_coeFn`, `L1.markovCLM_isPositive` |
| | Multiplication operators on `L¹(ψ)` | `L1.memLp_mul`, `L1.mulLin`, `L1.mulLin_apply`, `L1.mulCLM`, `L1.mulCLM_coeFn`, `L1.mulCLM_isPositive`, `L1.mulCLM_le_self` |
| §4.2.1.2, p. 135 | The firm in `L¹(ψ)`: regular, `K_σ ≤ βP`, `ρ(βP) < 1`; Theorem 4.1.8 | `polInd`, `polCont`, `measurable_polInd`, `measurable_polCont`, `abs_polInd_le`, `abs_polCont_le`, `polCont_nonneg`, `polCont_le_one`, `polInd_nonneg`, `isIsoOrderEmbedding_id_L1`, `FirmL1`, `FirmL1.Pop`, `FirmL1.sconst`, `FirmL1.D`, `FirmL1.rσ`, `FirmL1.Kσ`, `FirmL1.D_isPositive`, `FirmL1.Kσ_isPositive`, `FirmL1.Kσ_le_D`, `FirmL1.specRad_D_lt_one`, `FirmL1.adp`, `FirmL1.T_coeFn`, `FirmL1.sell`, `FirmL1.T_sell_coeFn`, `FirmL1.sell_isGreedy`, `FirmL1.adp_regular`, `FirmL1.adp_bellman_coeFn`, `FirmL1.isAdditive`, `FirmL1.optimality` |
| §4.2.1.3, (4.14)–(4.15) | State-dependent discounting | `FirmSD`, `FirmSD.K`, `FirmSD.K_apply`, `FirmSD.K_isPositive`, `FirmSD.cont`, `FirmSD.rσ`, `FirmSD.Kσ`, `FirmSD.T`, `FirmSD.T_apply`, `FirmSD.adp`, `FirmSD.sell`, `FirmSD.T_sell_apply`, `FirmSD.sell_isGreedy`, `FirmSD.adp_regular`, `FirmSD.adp_bellman_apply`, `FirmSD.isAdditive`, `FirmSD.Kσ_le_K` |
| Assumption 4.2.1, Prop 4.2.2, Ex 4.2.1, p. 136 | `ρ(K) < 1` gives optimality and convergence | `FirmSD.proposition_4_2_2` |

## §4.2.2 A real option problem (pp. 137–140)

| Book | Claim | Lean |
| --- | --- | --- |
| Assumption 4.2.2, §4.2.2.1 | The model; the discount operator `K` | `RealOption`, `RealOption.abs_βf_le`, `RealOption.K`, `RealOption.K_isPositive` |
| Assumption 4.2.3, p. 138 | `q = (I − K)⁻¹π` | `iterate_affine_sub`, `RealOption.exists_q`, `RealOption.q`, `RealOption.q_eq` |
| (4.16) | Policy operators | `RealOption.rσ`, `RealOption.Kσ`, `RealOption.adp`, `RealOption.T_eq`, `RealOption.Kσ_isPositive`, `RealOption.Kσ_le_K`, `RealOption.isAdditive`, `RealOption.isDiscountOperator`, `RealOption.isGloballyStable` |
| Ex 4.2.2, (4.17), p. 139 | Well-posedness and lifetime values | `RealOption.iterate_T_zero`, `RealOption.exercise_4_2_2`, `RealOption.eq_4_17_misprint` |
| Ex 4.2.3, (4.18)–(4.19), p. 139 | `𝟙{q ≥ v}` is greedy; `Tv = −c + K(q ∨ v)` | `RealOption.launch`, `RealOption.mix_coeFn`, `RealOption.mix_launch`, `RealOption.exercise_4_2_3`, `RealOption.adp_regular`, `RealOption.adp_bellman` |
| Prop 4.2.3, p. 140 | Optimality and convergence | `RealOption.proposition_4_2_3` |

## §4.2.3 Structural estimation (pp. 140–146)

| Book | Claim | Lean |
| --- | --- | --- |
| Ex 4.2.4, (4.22), p. 142 | A Borel measurable argmax selection | `argmaxSet`, `argmaxSet_nonempty`, `argmaxSel`, `argmaxSel_max`, `measurable_argmaxSel` |
| §4.2.3.3, (4.26)–(4.28) | Post-action ADPs with a certainty equivalent `M` | `SEPolicy`, `IsCEOperator`, `PostAction`, `PostAction.H`, `PostAction.H_mono`, `PostAction.H_shift`, `PostAction.adp`, `PostAction.blackwell`, `PostAction.greedySE`, `PostAction.H_le_greedy`, `PostAction.greedySE_isGreedy`, `PostAction.adp_regular`, `PostAction.adp_bellman` |
| Prop 4.2.6, p. 145 | Optimality for every certainty equivalent | `PostAction.proposition_4_2_6` |
| (4.20)–(4.21), §4.2.3.1 | The expected-utility model; Bellman equation | `expectOp`, `integrable_BM`, `isCEOperator_expectOp`, `postActionEU`, `bellman_EU` |
| Ex 4.2.5, p. 142 | `T̂_σ` is a contraction of modulus `β` | `exercise_4_2_5` |
| Prop 4.2.4, p. 143 | Optimality and convergence | `proposition_4_2_4` |
| §4.2.3.4, p. 145 | The risk-sensitive certainty equivalent | `riskSensitive`, `isCEOperator_riskSensitive`, `riskSensitive_optimality` |
| §4.2.3.2, (4.23)–(4.25) | Finite model with state-dependent discounting | `hasSolidNorm_pi`, `FiniteSE`, `FiniteSE.Klin`, `FiniteSE.K`, `FiniteSE.K_apply`, `FiniteSE.K_isPositive`, `FiniteSE.rhat`, `FiniteSE.adp`, `FiniteSE.adp_T_apply`, `FiniteSE.isGreedy_of_argmax`, `FiniteSE.exists_argmax`, `FiniteSE.adp_regular`, `FiniteSE.adp_bellman_apply`, `FiniteSE.isIsoOrderEmbedding_id`, `FiniteSE.isAdditive` |
| Prop 4.2.5, p. 144 | `ρ(K_σ) < 1`: optimality, convergence, HPI finite; constant `β < 1` | `FiniteSE.proposition_4_2_5`, `FiniteSE.specRad_lt_one_of_le` |
