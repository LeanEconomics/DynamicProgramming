# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 6, "Linear Decision Processes" (pp. 184–206), with the Appendix A results the chapter
uses. Result, equation and exercise numbers are the book's; page numbers are book pages. Lean
names are relative to `SargentStachurski.LinearDecisionProcesses`. Where the Lean statement adds a
hypothesis the book leaves implicit, or departs from the printed statement, see
[corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 | `GloballyStable`, contractions |
| `SupContraction`, `MarkovOperator` | Volume 2, Chapter 1 | `bX` as a set, Markov operators |
| `OrderTheory`, `ADP`, `Algorithms` | Volume 2, Chapter 2 | ADPs, optimality, VFI/OPI/HPI |
| `Pospace`, `MetricADP`, `BoundedMeasurable` | Volume 2, Chapter 3 | Global stability, semi-regularity, `bX` as a Banach lattice (`BM`) |
| `BanachLattice`, `OrderContraction`, `BMOperators` | Volume 2, Chapter 4 | Spectral radius, discount operators, Theorems 4.1.4–4.1.8 |

## Appendix A used in Chapter 6

| Book | Claim | Lean |
| --- | --- | --- |
| §A.3.1.3 | Lower/upper hemicontinuous, continuous correspondences | `IsLHC`, `IsUHC`, `IsContinuousCorr` |
| Ex A.3.1, p. 350 | `[g(x), h(x)]` is compact-valued and continuous | `clamp_mem`, `clamp_eq`, `exists_subseq_Icc`, `exercise_A_3_1` |
| Thm A.3.3, p. 351 | Maximum theorem with a measurable selection (stated) | `HasMaxSelections` |
| Thm A.3.3 for `[g(x), h(x)]` | Proved: the largest maximizer is upper semicontinuous, hence Borel; the maximum is continuous | `IccMax.argmax`, `IccMax.sel`, `IccMax.continuousOn_section`, `IccMax.argmax_nonempty`, `IccMax.isClosed_argmax`, `IccMax.sel_mem`, `IccMax.isClosed_le_sel`, `IccMax.exists_param`, `IccMax.continuous_max`, `IccMax.measurable_sel`, `hasMaxSelections_Icc` |
| Scheffé's lemma, p. 365 | For densities | `scheffe` |

## §6.1.1 Feller properties (pp. 185–187)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 185 | Weak and strong Feller kernels | `LDP.IsWeakFeller`, `LDP.IsStrongFeller`, `LDP.IsStrongFeller.isWeakFeller` |
| Example 6.1.1, p. 186 | Shock-driven kernels are weak Feller | `measurable_section`, `shockKernel`, `shockKernel_apply`, `shockKernel_isMarkov`, `integral_shockKernel`, `example_6_1_1` |
| Lemma 6.1.1, (6.1), p. 187 | A continuous density kernel gives a strong Feller kernel | `lemma_6_1_1` |
| Example 6.1.2, (6.2), p. 187 | `β(x) ∫ h(g(x, a) + w)φ(w) dw` is strong Feller | `example_6_1_2` |

## §6.1.2 LDPs (pp. 187–192)

| Book | Claim | Lean |
| --- | --- | --- |
| §6.1.2.1, (6.3)–(6.4) | LDPs, feasible policies, policy operators | `LDP`, `LDP.Policy`, `LDP.nonempty_policy`, `LDP.measurable_graph`, `LDP.along`, `LDP.rσ`, `LDP.βσ`, `LDP.Pσ`, `LDP.K`, `LDP.K_apply`, `LDP.T_apply` |
| §6.1.2.2 | `T_σ = r_σ + K_σ`, `K_σ` positive, `(bX, 𝕋_LDP)` an ADP | `LDP.K_isPositive`, `LDP.norm_K_le`, `LDP.adp`, `LDP.isAdditive` |
| Example 6.1.3, p. 190 | A finite MDP is an LDP, `|∫ v dK| ≤ β‖v‖` | `ofMDP`, `ofMDP_T_apply`, `example_6_1_3` |
| Example 6.1.4, p. 190 | Firm valuation with state-dependent discounting | `LDP.firm`, `LDP.firm_T_apply` |
| Example 6.1.5, p. 191 | Optimal savings as an LDP | `Savings.measurable_next`, `Savings.P`, `Savings.reward`, `Savings.ldp`, `Savings.example_6_1_5` |
| Example 6.1.6, p. 191 | The risk-sensitive operator is not affine | `example_6_1_6` |
| (6.5)–(6.6), p. 191 | `v_σ = ∑_t K_σ^t r_σ` when `ρ(K_σ) < 1` | `LDP.iterate_T_zero`, `LDP.globallyStable_T`, `LDP.lifetime_value` |

## §6.1.3 Optimality results (pp. 192–194)

| Book | Claim | Lean |
| --- | --- | --- |
| Prop 6.1.2, p. 192 | Finite LDPs with `ρ(K_σ) < 1` | `argmaxSet`, `argmaxSet_nonempty`, `argmaxSel`, `argmaxSel_max`, `measurable_argmaxSel`, `LDP.regular_of_isFinite`, `LDP.proposition_6_1_2` |
| Assumption 6.1.1, Prop 6.1.3, p. 192 | Feller LDPs: optimality, `v* ∈ bcX`, geometric VFI; OPI and HPI under strong Feller | `LDP.G`, `LDP.bc`, `LDP.isClosed_bc`, `LDP.zero_mem_bc`, `LDP.continuousOn_obj`, `LDP.greedy_of_continuousOn`, `LDP.proposition_6_1_3` |
| (6.7), §6.1.3.2 | Greedy policies | `LDP.obj`, `LDP.T_apply_obj`, `LDP.isGreedy_iff`, `LDP.isGreedy_of_argmax`, `LDP.argmax_of_isGreedy` |
| (6.8)–(6.9), p. 193 | Argmax policies and the Bellman operator (strong Feller; weak Feller on `bcX`) | `LDP.implications`, `LDP.implications_bc` |

## §6.1.4 Exogenous discount processes (pp. 194–197)

| Book | Claim | Lean |
| --- | --- | --- |
| (6.10) | `(K_Q h)(z) = β(z) ∑_{z'} h(z')Q(z, z')` | `hasSolidNorm_pi`, `Exo.KLin`, `Exo.K`, `Exo.K_apply`, `Exo.K_isPositive` |
| Lemma 6.1.4, p. 194 | `(K_Qⁿh)(z) = 𝔼_z β₀ ⋯ β_{n−1} h(Z_n)` (finite `Z`, path sums) | `Exo.pathExp`, `Exo.pathExp_succ`, `Exo.lemma_6_1_4` |
| Lemma 6.1.5, p. 195 | `ρ(K) < 1` iff `‖Kⁿh‖ ≤ λ‖h‖` | `BanachLattice.lemma_6_1_5` |
| Ex 6.1.1, p. 195 | `q = (I − K_Q)⁻¹h` | `BanachLattice.iterate_affine_zero`, `BanachLattice.exercise_6_1_1`, `Exo.exercise_6_1_1` |
| §6.1.4.2, Assumption 6.1.2 | Product state space, continuity slice by slice | `continuousOn_of_slices` |
| Prop 6.1.6, p. 196 | Optimality under exogenous discounting | `LDP.supY`, `LDP.bddAbove_slice`, `LDP.le_supY`, `LDP.abs_supY_le`, `LDP.abs_supY_sub_le`, `LDP.Dexo`, `LDP.supY_lift`, `LDP.Dexo_iterate`, `LDP.Dexo_isDiscountOperator`, `LDP.K_le_Dexo`, `LDP.proposition_6_1_6` |

## §6.1.5 Markov decision processes (pp. 197–199)

| Book | Claim | Lean |
| --- | --- | --- |
| (6.12)–(6.13) | MDPs as LDPs with `K = βP` | `ofMDP`, `ofMDP_T_apply` |
| Prop 6.1.7, p. 198 | Feller MDPs | `Dsup`, `abs_iSup_sub_le`, `Dsup_isDiscountOperator`, `K_le_Dsup`, `proposition_6_1_7` |
| Example 6.1.8, p. 198 | Optimal savings with a continuous density is strong Feller | `Savings.densityMeasure`, `Savings.densityMeasure_isProbability`, `Savings.example_6_1_8` |
| (6.14)–(6.15) | Argmax policies and the Bellman operator for MDPs | `LDP.implications`, `LDP.implications_bc` applied to `ofMDP` |

## §6.2 Applications (pp. 199–206)

| Book | Claim | Lean |
| --- | --- | --- |
| §6.2.1 | Natural resource model; the kernel of a stochastic matrix | `rowPMF`, `finiteKernel`, `finiteKernel_isMarkov`, `integral_finiteKernel`, `ResourceModel`, `ResourceModel.measurable_next`, `ResourceModel.R`, `ResourceModel.Qk`, `ResourceModel.R_isMarkov`, `ResourceModel.Qk_isMarkov`, `ResourceModel.ldp`, `ResourceModel.integral_P` |
| Prop 6.2.1, p. 200 | Optimality, `v* ∈ bcX`, geometric VFI | `ResourceModel.proposition_6_2_1` |
| §6.2.2 | Stochastic rates of return; mixture kernels | `mixKernel`, `mixKernel_isMarkov`, `integral_mixKernel`, `ReturnsModel`, `ReturnsModel.measurable_zproj`, `ReturnsModel.reward`, `ReturnsModel.measurable_income`, `ReturnsModel.next`, `ReturnsModel.measurable_next`, `ReturnsModel.finiteKernel_comap_isMarkov`, `ReturnsModel.P`, `ReturnsModel.P_isMarkov`, `ReturnsModel.integral_P`, `ReturnsModel.ldp`, `ReturnsModel.obj_apply`, `ReturnsModel.weakFeller` |
| p. 205 | Proposition 6.1.7 applies; the Bellman operator | `ReturnsModel.section_6_2_2` |
| Ex 6.2.1, p. 205 | Mortality: Proposition 6.1.3 applies | `ReturnsModel.measurable_zprojT`, `ReturnsModel.nextT`, `ReturnsModel.measurable_nextT`, `ReturnsModel.finiteKernel_comapT_isMarkov`, `ReturnsModel.PT`, `ReturnsModel.PT_isMarkov`, `ReturnsModel.integral_PT`, `ReturnsModel.ldpT`, `ReturnsModel.exercise_6_2_1` |
