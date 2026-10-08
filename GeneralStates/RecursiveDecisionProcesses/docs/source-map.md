# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 7, "Recursive Decision Processes" (pp. 207–245), with the Appendix A results the chapter
uses. Result, equation and exercise numbers are the book's; page numbers are book pages. Lean
names are relative to `SargentStachurski.RecursiveDecisionProcesses`. Where the Lean statement adds
a hypothesis the book leaves implicit, or departs from the printed statement, see
[corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 | `GloballyStable`, contractions |
| `SupContraction`, `MarkovOperator` | Volume 2, Chapter 1 | `bX` as a set, Markov operators |
| `OrderTheory`, `ADP`, `Algorithms` | Volume 2, Chapter 2 | ADPs, optimality, VFI/OPI/HPI, Theorem 2.2.6 |
| `Pospace`, `MetricADP`, `BoundedMeasurable` | Volume 2, Chapter 3 | Lemma 3.1.1, semi-regularity, `bX` as a Banach lattice (`BM`) |
| `BanachLattice`, `OrderContraction`, `BMOperators` | Volume 2, Chapter 4 | Theorem 4.1.3, Lemma 4.1.2, the order unit `𝟙` |
| `Correspondences`, `LDP`, `LDPOptimality`, `Feller`, `GeneralMDP`, `SavingsFeller` | Volume 2, Chapter 6 | Theorem A.3.3 for intervals, LDPs, `bcX`, shock kernels, Scheffé's lemma, Example 6.1.5 |

## Appendix A used in Chapter 7

| Book | Claim | Lean |
| --- | --- | --- |
| Lemma A.2.6, p. 346 | A closed invariant set contains the limit of the iterates | `lemma_A_2_6`, `ADP.VFIGeometric.tendsto` |
| Thm A.3.3, last claim, p. 351 | A unique maximizer is continuous (stated; proved for `[g(x), h(x)]`) | `HasContinuousUniqueMax`, `hasContinuousUniqueMax_Icc` |
| §A.5.3.5, p. 382 | Weighted supremum norm, `bℓX`, `bℓcX` | `wnorm`, `bl`, `blPlus`, `wevB`, `wevB_mem`, `wev`, `wev_mem`, `ofBl`, `wev_ofBl`, `wev_le_iff`, `posCone`, `isClosed_posCone`, `add_mem_posCone`, `bcPlus`, `isClosed_bcPlus`, `zero_mem_bcPlus` |
| Ex A.5.22, p. 383 | `bX ⊆ bℓX` | `exercise_A_5_22` |
| Ex A.5.24, p. 383 | Convergence in `bℓX` is pointwise | `exercise_A_5_24` |
| Thm A.5.24, p. 383 | `bℓX` is a Banach lattice (by transport from `bX`) | `norm_eq_wnorm`, `wev_le_iff` |
| Ex A.5.25, p. 383 | `ℓ` is a normalized order unit of `bℓX` | `exercise_A_5_25` |
| Scheffé's lemma, p. 365 | General form | `scheffe_general` |

## §7.1 Introduction (pp. 207–217)

| Book | Claim | Lean |
| --- | --- | --- |
| §7.1.1.1, (7.2)–(7.3) | RDPs, feasible policies | `FeasiblePolicy`, `RDP`, `RDP.Policy`, `RDP.ev_injective`, `RDP.nonempty_Γ` |
| §7.1.1.2, Ex 7.1.1, p. 209 | Finite MDPs; the Bellman equation is (1.19) | `mdpAgg`, `exercise_7_1_1`, `finiteMDP`, `finiteMDP_bellman` |
| §7.1.1.3, (7.4), p. 209 | Firm valuation; the Bellman equation of Theorem 1.1.1 | `firmAgg`, `firmRDP`, `firmRDP_bellman` |
| §7.1.1.4, (7.5), Ex 7.1.2, p. 210 | Firm valuation with unbounded profits on `bℓX` | `exists_wevB_eq`, `exercise_7_1_2`, `firmWeighted` |
| §7.1.1.5, p. 210 | Optimal savings | `savings_B` (with `LDP.toRDP` and Example 6.1.5) |
| §7.1.1.6, (7.6), Ex 7.1.3, p. 211 | Savings with Kreps–Porteus expectations | `KPValues`, `kpCont`, `kpAgg`, `kpCont_mono`, `kpCont_const`, `exercise_7_1_3`, `kpSavings` |
| §7.1.1.7, (7.7), p. 212 | MDPs with modified rewards | `modifiedMDP` |
| §7.1.1.8, (7.8), Ex 7.1.4, p. 212 | Risk-sensitive preferences | `rsAgg`, `exercise_7_1_4`, `riskSensitiveMDP` |
| §7.1.2.1, (7.9), p. 213 | LDPs are RDPs | `LDP.toRDP`, `LDP.toRDP_T` |
| §7.1.2.2, (7.10)–(7.11), p. 213 | The generated ADP; greedy policies; the Bellman operator | `RDP.T`, `RDP.ev_T`, `RDP.adp`, `RDP.ev_adp_T`, `RDP.isGreedy_iff`, `RDP.IsArgmax`, `RDP.isGreedy_of_isArgmax`, `RDP.bellman_of_isArgmax`, `RDP.isGreedy_iff_isArgmax` |
| Ex 7.1.5, (7.12), p. 214 | Isomorphic RDPs | `RDP.exercise_7_1_5` |
| Lemma 7.1.1, (7.16)–(7.17), p. 216 | Finite actions | `exists_measurable_argmax`, `RDP.lemma_7_1_1` |
| Lemma 7.1.2, (7.18)–(7.19), p. 217 | Continuous actions | `RDP.lemma_7_1_2` |

## §7.2.1 Bounded contractions (pp. 218–220)

| Book | Claim | Lean |
| --- | --- | --- |
| §7.2.1.1, Assumption 7.2.1 | The framework; `(Γ, bX, B)` is an RDP; Blackwell's condition | `BRDP`, `BRDP.toRDP`, `BRDP.toRDP_T_apply`, `BRDP.IsBlackwell`, `BRDP.T_blackwell` |
| Prop 7.2.1, p. 219 | Finite actions | `BRDP.regular_of_finite`, `BRDP.proposition_7_2_1`, `BRDP.proposition_7_2_1_finite` |
| Assumptions 7.2.2–7.2.3, Prop 7.2.2, p. 220 | The continuous case | `BRDP.greedy_of_continuous`, `BRDP.proposition_7_2_2` |

## §7.2.2 Weighted contractions (pp. 220–223)

| Book | Claim | Lean |
| --- | --- | --- |
| §7.2.2.1, Assumption 7.2.4, Lemma 7.2.3, p. 221 | The framework, (U1)–(U2); `(Γ, bℓX₊, B)` is an RDP | `WRDP`, `WRDP.toRDP`, `WRDP.toRDP_T_apply`, `WRDP.IsBlackwell`, `WRDP.T_blackwell` |
| Assumption 7.2.5, Prop 7.2.4, p. 222 | Finite actions | `WRDP.regular_of_finite`, `WRDP.proposition_7_2_4`, `WRDP.proposition_7_2_4_finite` |
| Assumptions 7.2.6–7.2.7, Prop 7.2.5, p. 222 | The continuous case | `WRDP.greedy_of_continuous`, `WRDP.proposition_7_2_5` |

## §7.2.3 Properties of solutions (pp. 223–225)

| Book | Claim | Lean |
| --- | --- | --- |
| Setting of Prop 7.2.5 | Its hypotheses, and `v*` lies in every closed invariant subset | `WRDP.ContinuousCase`, `WRDP.ContinuousCase.prop`, `WRDP.ContinuousCase.vstar_mem`, `coneZero`, `wev_coneZero` |
| Ex 7.2.1, p. 223 | `ibℓcX₊` is closed | `exercise_7_2_1` |
| Assumption 7.2.8, Prop 7.2.6, p. 224 | Monotone values | `WRDP.proposition_7_2_6` |
| Assumption 7.2.9, Prop 7.2.7, p. 224 | Concave values | `WRDP.isClosed_concave`, `WRDP.feasibleOn`, `WRDP.proposition_7_2_7` |
| Assumption 7.2.10, Prop 7.2.8, p. 225 | Unique, continuous optimal policy | `eq_of_isMax_of_strictConcaveOn`, `WRDP.proposition_7_2_8` |

## §7.2.4 Certainty equivalents (pp. 225–230)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 226 | `L∞`, risk measures (R1)–(R2), certainty equivalents (C1)–(C2) | `IsLInf`, `IsLInf.add_const`, `IsLInf.const_mul`, `IsLInf.add`, `isLInf_const`, `IsLInf.integrable`, `IsRiskMeasure`, `IsCertEquiv` |
| Ex 7.2.5, p. 226 | `ℰ` is a certainty equivalent iff `−ℰ` is a risk measure; convex combinations | `exercise_7_2_5_i`, `exercise_7_2_5_ii` |
| pp. 226–227 | Convex and coherent risk measures; concave and coherent certainty equivalents; superadditivity | `IsConvexRisk`, `IsConcaveCE`, `IsPosHomogeneous`, `IsCoherentRisk`, `IsCoherentCE`, `isCoherentRisk_neg_iff`, `IsCoherentCE.superadditive` |
| p. 228 | `𝔼` and the pessimistic certainty equivalent are coherent | `meanCE`, `meanCE_isCoherent`, `pessCE`, `mem_pess_iff`, `pess_nonempty`, `pess_bddAbove`, `ae_pess_le`, `le_pess`, `pessCE_isCoherent` |
| (7.21), p. 229 | The entropic certainty equivalent | `entropicCE`, `integrable_exp`, `integral_exp_pos'`, `entropicCE_isCertEquiv` |
| p. 229 | The Kreps–Porteus expectation fails cash invariance | `kpExp`, `kpExp_not_cash_invariant` |
| §7.2.4.3, Example 7.2.1, p. 229 | Continuity; `𝔼` is continuous | `IsContinuousCE`, `example_7_2_1` |
| Ex 7.2.6, p. 230 | `ℰ_γ` is continuous | `exercise_7_2_6` |

## §7.2.5 MDPs with certainty equivalents (pp. 230–231)

| Book | Claim | Lean |
| --- | --- | --- |
| (7.23)–(7.24) | The aggregator `B_ℰ`; `(Γ, bX, B_ℰ)` is an RDP; Blackwell's condition with `λ = β` | `ceAgg`, `isLInf_comp`, `IsCertEquiv.abs_sub_le`, `ceBRDP`, `ceBRDP_isBlackwell` |
| p. 230 | The measurability assumption holds for `𝔼` and `ℰ^θ` | `measurable_integral_comp`, `measurable_meanCE_comp`, `measurable_entropicCE_comp` |
| Assumption 7.2.11, Prop 7.2.10, p. 231 | Optimality with a continuous certainty equivalent | `continuousOn_ce`, `proposition_7_2_10` |

## §7.3 Applications (pp. 232–244)

| Book | Claim | Lean |
| --- | --- | --- |
| §7.3.1, (7.25) | Optimal savings with utility unbounded above | `SavingsU`, `SavingsU.B`, `SavingsU.δ_pos`, `SavingsU.integrable_v`, `SavingsU.integral_ℓ_le`, `SavingsU.integral_ℓ_feasible_le`, `SavingsU.wrdp` |
| Ex 7.3.1, p. 232 | (U1) with `λ = β/δ`, and (U2) | `SavingsU.exercise_7_3_1` |
| Ex 7.3.2, p. 232 | Assumption 7.2.7 | `SavingsU.integral_shift_density`, `SavingsU.integrable_shift_density`, `SavingsU.continuous_integral_ℓ`, `SavingsU.exercise_7_3_2`, `SavingsU.hasMaxSelections`, `SavingsU.continuousCase` |
| p. 232 | Proposition 7.2.5 applies; VFI, OPI and HPI converge | `SavingsU.section_7_3_1` |
| Ex 7.2.2, p. 224 | Assumption 7.2.8 for savings; `v*` increasing | `SavingsU.exercise_7_2_2`, `SavingsU.vstar_monotone` |
| Ex 7.2.3, p. 224 | `v*` increasing and concave | `SavingsU.convex_feasibleOn`, `SavingsU.integral_concave`, `SavingsU.exercise_7_2_3` |
| Ex 7.2.4, p. 225 | Unique, continuous optimal policy | `SavingsU.exercise_7_2_4` |
| §7.3.2.1, Assumption 7.3.1 | Irreversible investment | `Investment`, `Investment.Γ`, `Investment.r`, `Investment.next`, `Investment.measurable_r`, `Investment.r_bdd`, `Investment.measurable_next`, `Investment.exists_policy`, `Investment.hasMaxSelections`, `Investment.meanRDP` |
| Prop 7.3.1, Ex 7.3.3, p. 234 | Risk-neutral investment | `Investment.proposition_7_3_1` |
| §7.3.2.2, (7.26), Prop 7.3.2, p. 237 | Investment with a continuous certainty equivalent | `Investment.IsMeasurableCE`, `Investment.rdp`, `Investment.rdp_B`, `Investment.proposition_7_3_2` |
| Example 7.3.1, p. 237 | The entropic case | `Investment.entropicRDP`, `Investment.example_7_3_1` |
| §7.3.3.2, p. 240 | The risk-sensitive form of the robust firm problem | `Investment.section_7_3_3` |
| §7.3.4, (7.28), p. 243 | The risk-sensitive MDP; Proposition 7.2.10 applies | `rsRDP`, `rsRDP_B`, `section_7_3_4` |
| §7.3.4, p. 243 | The multiplicative Kreps–Porteus RDP; taking logs | `PosValues`, `PosValues.pos`, `PosValues.abs_log_le`, `PosValues.log`, `PosValues.exp`, `mkpAgg`, `mkpAgg_eq_exp`, `mkpRDP` |
| Ex 7.3.4, p. 244 | The two RDPs are isomorphic | `exercise_7_3_4` |
