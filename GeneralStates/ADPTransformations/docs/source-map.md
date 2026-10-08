# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 2: *General States*,
Chapter 5, "ADP Transformations" (pp. 147–182), with the Appendix A results the chapter uses.
Result, equation and exercise numbers are the book's; page numbers are book pages. Lean names
are relative to `SargentStachurski.ADPTransformations`. Where the Lean statement adds a hypothesis
the book leaves implicit, or departs from the printed statement, see
[corrections](corrections.md).

## Restated from earlier chapter projects

Each chapter project is self-contained. These modules are copied, with the namespace renamed,
from the projects named; their source maps give the book correspondence.

| Module | From | Used for |
| --- | --- | --- |
| `Basics` | Volume 1, Chapter 10 | `GloballyStable`, contractions |
| `SupContraction`, `ContractingDP`, `MarkovOperator`, `NeumannSeries` | Volume 2, Chapter 1 | `bX` as a set, Markov operators |
| `OrderTheory`, `ADP`, `Algorithms` | Volume 2, Chapter 2 | ADPs, optimality, VFI/OPI/HPI |
| `Minimization`, `FiniteMDP`, `MDPADP`, `Pospace`, `MetricADP`, `MinPospace`, `BoundedMeasurable`, `MDPQFactors` | Volume 2, Chapter 3 | Min-ADPs, finite MDPs, Q-factors, `bX` as a Banach lattice (`BM`) |
| `BanachLattice`, `OrderContraction`, `DuTheorem`, `BMOperators`, `StructuralEstimation` | Volume 2, Chapter 4 | Order contractions, Du's theorem, post-action values |

## §5.1.1 Background concepts (pp. 148–151)

| Book | Claim | Lean |
| --- | --- | --- |
| §5.1.1.1 | Conjugate dynamical systems; unique fixed points | `IsConjugate`, `IsUniqueFixed`, `IsConjugate.symm` |
| Prop 5.1.1 (i)–(iii), p. 149 | `Sⁿ = F⁻¹ŜⁿF`; fixed points correspond | `IsConjugate.iterate`, `IsConjugate.fixed_iff`, `IsConjugate.fixed_iff_symm` |
| Prop 5.1.1 (iv), Ex 5.1.1 | Unique fixed points correspond | `IsConjugate.isUniqueFixed_iff` |
| Example 5.1.1, p. 149 | Log-linearization | `example_5_1_1` |
| Example 5.1.2, p. 149 | Diagonalization `A = EDE⁻¹` | `coordChange`, `example_5_1_2` |
| §5.1.1.2, Prop 5.1.2, p. 150 | Topological conjugacy preserves global stability | `IsTopConjugate`, `IsTopConjugate.symm`, `IsTopConjugate.globallyStable`, `proposition_5_1_2` |
| Example 5.1.3, p. 150 | `A` globally stable iff all eigenvalues in the unit disc | `coordHomeo`, `iterate_diagonal_mulVec`, `globallyStable_diagonal_iff`, `example_5_1_3` |
| §5.1.1.3 | Order conjugacy | `IsOrderConjugate` |
| Ex 5.1.2, p. 151 | Order conjugacy is an equivalence relation | `IsOrderConjugate.refl`, `IsOrderConjugate.symm`, `IsOrderConjugate.trans` |
| Ex A.1.15 | Order isomorphisms preserve `↑`, `↓` | `orderIso_increasesTo`, `orderIso_decreasesTo` |
| Lemma 5.1.3, Ex 5.1.3, p. 151 | (Strong) order stability transfers | `IsOrderConjugate.orderStable`, `IsOrderConjugate.stronglyOrderStable`, `IsOrderConjugate.lemma_5_1_3` |

## §5.1.2 Isomorphic ADPs (pp. 151–157)

| Book | Claim | Lean |
| --- | --- | --- |
| §5.1.2.1, (5.1) | Isomorphic ADPs | `ADP.IsIsomorphic`, `ADP.IsIsomorphic.T_apply`, `ADP.IsIsomorphic.range_T` |
| Example 5.1.4, p. 152 | `F v = exp ∘ v` links (5.2) and (5.3) | `ADP.savingsAdd`, `ADP.savingsMul`, `ADP.expPi`, `ADP.example_5_1_4` |
| Lemma 5.1.4, Ex 5.1.4, p. 152 | Isomorphism is an equivalence relation | `ADP.IsIsomorphic.refl`, `ADP.IsIsomorphic.symm`, `ADP.IsIsomorphic.trans` |
| Thm 5.1.5 (i)–(v), p. 153 | Greedy, regular, well-posed, order stable, optimal transfer | `ADP.IsIsomorphic.isGreedy_iff`, `ADP.IsIsomorphic.mem_VG_iff`, `ADP.IsIsomorphic.regular_iff`, `ADP.IsIsomorphic.wellPosed_iff`, `ADP.IsIsomorphic.vσ_eq`, `ADP.IsIsomorphic.VSig_eq`, `ADP.IsIsomorphic.isOptimal_iff`, `ADP.IsIsomorphic.orderStable_iff`, `ADP.IsIsomorphic.stronglyOrderStable_iff`, `ADP.theorem_5_1_5` |
| Thm 5.1.6 (i)–(iii), (5.4), p. 153 | `F ∘ T = T̂ ∘ F`, `v̂* = Fv*`, fundamental optimality transfers | `ADP.IsIsomorphic.isBellmanValue_iff`, `ADP.IsIsomorphic.solvesBellman_iff`, `ADP.IsIsomorphic.bellman_eq`, `ADP.IsIsomorphic.bellman_semiconj`, `ADP.IsIsomorphic.isValueFunction_iff`, `ADP.IsIsomorphic.bellmanPrinciple`, `ADP.IsIsomorphic.fundamentalOptimality`, `ADP.IsIsomorphic.fundamentalOptimality_iff`, `ADP.theorem_5_1_6` |
| Thm 5.1.7, (5.5)–(5.6), Ex 5.1.5, p. 154 | `F ∘ W = Ŵ ∘ F`, `F ∘ H = Ĥ ∘ F`; VFI, OPI, HPI transfer | `ADP.IsIsomorphic.mem_VU_iff`, `ADP.IsIsomorphic.isSelector_iff`, `ADP.IsIsomorphic.opt_eq`, `ADP.IsIsomorphic.howard_eq`, `ADP.IsIsomorphic.vfiConverges`, `ADP.IsIsomorphic.opiConverges`, `ADP.IsIsomorphic.hpiConverges`, `ADP.theorem_5_1_7` |
| §5.1.2.3 | Anti-isomorphic ADPs | `ADP.IsAntiIsomorphic`, `ADP.IsAntiIsomorphic.iso`, `ADP.IsAntiIsomorphic.orderStable_iff`, `ADP.IsAntiIsomorphic.minSelector_iff` |
| Ex 5.1.6, p. 155 | Anti-isomorphic iff isomorphic to the dual | `ADP.exercise_5_1_6` |
| Thm 5.1.8, p. 155 | Max-greedy/regular/optimal is min-greedy/regular/optimal | `ADP.theorem_5_1_8` |
| Thm 5.1.9, (5.7), Ex 5.1.7, p. 156 | `F ∘ T = T̂▿ ∘ F`, `v̂▿* = Fv*`, max- iff min-optimality | `ADP.theorem_5_1_9` |
| Thm 5.1.10, (5.8)–(5.9), Ex 5.1.8, p. 156 | Max-VFI/OPI/HPI iff min-VFI/OPI/HPI | `ADP.theorem_5_1_10` |

## §5.1.3 Epstein–Zin optimality (pp. 157–160)

| Book | Claim | Lean |
| --- | --- | --- |
| (5.10)–(5.11) | The Epstein–Zin model and policy operators | `EZModel`, `EZModel.θ`, `EZModel.θ_ne`, `EZModel.Policy`, `EZModel.nonempty_policy`, `EZModel.finite_policy`, `EZModel.Lσ`, `EZModel.Tσ` |
| p. 158, (5.12) | `m₁, m₂`, `v₁ = m₁ ∧ m₂`, `v₂ = m₁ ∨ m₂`, `V̂ = [v₁, v₂]`, `V` | `EZModel.c₂_pos`, `EZModel.lo`, `EZModel.hi`, `EZModel.lo_pos`, `EZModel.hi_pos`, `EZModel.lo_lt_hi`, `EZModel.a`, `EZModel.b`, `EZModel.a_le_b`, `EZModel.V` |
| (5.13) | The auxiliary policy operators `T̂_σ` | `EZModel.Pσ`, `EZModel.Pσ_const`, `EZModel.Pσ_mono`, `EZModel.Pσ_combo`, `EZModel.Pσ_mem`, `EZModel.Pσ_pos`, `EZModel.That`, `EZModel.rα_pos`, `EZModel.That_le`, `EZModel.That_mem`, `EZModel.adpHat` |
| Ex 5.1.9, p. 158 | `v₁ ≪ T̂_σ v₁`, `T̂_σ v₂ ≪ v₂` | `EZModel.lo_lt_f_hi`, `EZModel.exercise_5_1_9` |
| Ex 5.1.10, p. 158, sol. p. 405 | The aggregator `f(t) = ((1−β)c + βt^{1/θ})^θ`: monotone, convex for `0 < θ ≤ 1`, concave for `θ < 0` or `1 ≤ θ` | `EZ.f`, `EZ.g`, `EZ.f'`, `EZ.g_pos`, `EZ.f_monotoneOn`, `EZ.f_rpow`, `EZ.hasDerivAt_f`, `EZ.deriv_f`, `EZ.f'_inner_pos`, `EZ.continuousOn_f`, `EZ.differentiableOn_f`, `EZ.convexOn_f`, `EZ.concaveOn_f`, `EZModel.exercise_5_1_10` |
| Lemma 5.1.11, p. 158 | Max- and min-optimality and convergence for `(V̂, 𝕋̂_EZ)` | `hasSolidNorm_pi`, `exists_eps_mul_le`, `EZModel.adpHat_isFinite`, `EZModel.exists_extremal`, `EZModel.adpHat_regular`, `EZModel.adpHat_minRegular`, `EZModel.duConditions`, `EZModel.adpHat_isOrderStable`, `EZModel.lemma_5_1_11` |
| Lemma 5.1.11 (ii), via Thm 4.1.11 | Du's theorem for minimization (reflection of `[a, b]`) | `BanachLattice.neg_mem_Icc_neg`, `BanachLattice.neg_mem_Icc_of_neg`, `BanachLattice.negIcc`, `ADP.reflect`, `BanachLattice.reflect_isAntiIsomorphic`, `BanachLattice.reflect_isFinite`, `BanachLattice.extendIcc_reflect`, `BanachLattice.duConditions_reflect`, `BanachLattice.theorem_4_1_11_min` |
| Ex 5.1.11, p. 159 | `F ∘ T_σ = T̂_σ ∘ F` | `EZModel.exercise_5_1_11`, `EZModel.Tσ_mem`, `EZModel.Φ_T` |
| Lemma 5.1.12, p. 159 | Isomorphic if `ν > 0`, anti-isomorphic if `ν < 0` | `EZModel.Φ`, `EZModel.Ψ`, `EZModel.Φ_Ψ`, `EZModel.Ψ_Φ`, `EZModel.isoPos`, `EZModel.isoNeg`, `EZModel.adp`, `EZModel.lemma_5_1_12_i`, `EZModel.lemma_5_1_12_ii` |
| Prop 5.1.13, p. 159 | Fundamental optimality, VFI, OPI, HPI for `(V, 𝕋_EZ)` | `EZModel.adp_isOrderStable`, `EZModel.proposition_5_1_13` |

## §5.2.1 Strong semiconjugacy (pp. 160–166)

| Book | Claim | Lean |
| --- | --- | --- |
| (5.14) | Strong semiconjugacy | `IsStronglySemiconj`, `IsStronglySemiconj.swap`, `IsStronglySemiconj.iterate_succ` |
| Ex 5.2.1, p. 161 | (5.14) implies (5.15) | `IsStronglySemiconj.exercise_5_2_1` |
| Lemma 5.2.1, p. 161 | Fixed points and unique fixed points transfer | `IsStronglySemiconj.fixed_F`, `IsStronglySemiconj.fixed_G`, `IsStronglySemiconj.isUniqueFixed`, `IsStronglySemiconj.existsUnique_iff` |
| Lemma 5.2.2 (i), p. 162 | Order stability transfers | `IsStronglySemiconj.orderStable_mono`, `IsStronglySemiconj.orderStable_anti`, `IsStronglySemiconj.lemma_5_2_2_i` |
| Lemma 5.2.2 (ii), p. 162 | Strong order stability transfers (limits in both directions) | `OrderContinuousDown`, `AntiContinuousUp`, `AntiContinuousDown`, `IsStronglySemiconj.increasesTo_of_succ`, `IsStronglySemiconj.decreasesTo_of_succ`, `IsStronglySemiconj.stronglyOrderStable_mono`, `IsStronglySemiconj.stronglyOrderStable_anti`, `IsStronglySemiconj.lemma_5_2_2_ii` |
| Thm 5.2.3, (5.16), p. 163 | Order-preserving case | `IsStronglySemiconj.theorem_5_2_3` |
| Thm 5.2.4, (5.17), p. 163 | Order-reversing case | `IsStronglySemiconj.theorem_5_2_4` |
| Lemma 5.2.2 (ii), Thms 5.2.3–5.2.4 as printed | Counterexample with one-sided order continuity | `orderContinuous_of_stabilizes`, `SemiconjCounterexample.Fork`, `SemiconjCounterexample.Fork.a`, `SemiconjCounterexample.Fork.bot₁`, `SemiconjCounterexample.Fork.bot₂`, `SemiconjCounterexample.Fork.le`, `SemiconjCounterexample.Fork.le_refl'`, `SemiconjCounterexample.Fork.le_trans'`, `SemiconjCounterexample.Fork.le_antisymm'`, `SemiconjCounterexample.forkOrder`, `SemiconjCounterexample.Chain`, `SemiconjCounterexample.shift`, `SemiconjCounterexample.Fmap`, `SemiconjCounterexample.Gmap`, `SemiconjCounterexample.Smap`, `SemiconjCounterexample.le_a_iff`, `SemiconjCounterexample.isStronglySemiconj`, `SemiconjCounterexample.Fmap_mono`, `SemiconjCounterexample.Gmap_mono`, `SemiconjCounterexample.chain_stabilizes`, `SemiconjCounterexample.rank`, `SemiconjCounterexample.rank_strictMono`, `SemiconjCounterexample.fork_stabilizes`, `SemiconjCounterexample.iterate_shift`, `SemiconjCounterexample.shift_stronglyOrderStable`, `SemiconjCounterexample.iterate_Smap`, `SemiconjCounterexample.Smap_not_stronglyOrderStable`, `SemiconjCounterexample.theorem_5_2_3_fails`, `SemiconjCounterexample.theorem_5_2_4_fails` |
| §5.2.1.3, (5.18) | The firm entry model; `S`, `T`, `F`, `G` | `FirmEntry`, `FirmEntry.integrable_section`, `FirmEntry.F`, `FirmEntry.G`, `FirmEntry.S`, `FirmEntry.T`, `FirmEntry.S_apply`, `FirmEntry.T_apply`, `FirmEntry.F_mono`, `FirmEntry.G_mono` |
| Assumption 5.2.1, Lemma 5.2.5, p. 165 | `T` is strongly order stable | `FirmEntry.K`, `FirmEntry.K_isPositive`, `FirmEntry.abs_T_sub_le`, `FirmEntry.DiscountCondition`, `FirmEntry.K_isDiscountOperator`, `FirmEntry.lemma_5_2_5` |
| Lemma 5.2.6, p. 165 | Strongly semiconjugate under order-preserving `F, G` | `FirmEntry.lemma_5_2_6` |
| Lemma A.1.3 (in `bX`), Lemma 5.2.8, p. 166 | `G` is order continuous (both directions) | `BM.tendsto_of_isLUB`, `BM.tendsto_of_isGLB`, `BM.isLUB_of_tendsto`, `BM.isGLB_of_tendsto`, `BM.tendsto_markov`, `FirmEntry.tendsto_G`, `FirmEntry.lemma_5_2_8` |
| Prop 5.2.7, p. 166 | Unique solution of (5.18) and `GTⁿw ↑ v̄` | `FirmEntry.proposition_5_2_7` |

## §5.2.2–5.2.3 Factored dynamic programs (pp. 166–174)

| Book | Claim | Lean |
| --- | --- | --- |
| §5.2.2.1 | FDPs, primary and subordinate ADPs, `G = ⋁_σ G_σ` (5.19) | `FDP`, `FDP.IsOrderPreserving`, `FDP.IsOrderReversing`, `FDP.Monotonic`, `FDP.gsel`, `FDP.Gsup`, `FDP.G_le_Gsup`, `FDP.isGreatest_Gsup`, `FDP.primary`, `FDP.sub` |
| Lemma 5.2.9, Lemma 5.2.15 | `T = G ∘ F`; greedy iff `G_σFv = GFv` | `FDP.primary_regular`, `FDP.primary_bellman`, `FDP.lemma_5_2_9` |
| Lemma 5.2.10, p. 168 | `T̂ = F ∘ G`; `G_σ v̂ = Gv̂` gives greedy | `FDP.sub_isGreedy_of_eq`, `FDP.sub_regular`, `FDP.sub_bellman`, `FDP.lemma_5_2_10` |
| Lemma 5.2.11, (5.20)–(5.21) | `(V, T)` and `(V̂, T̂)` strongly semiconjugate | `FDP.policy_semiconj`, `FDP.lemma_5_2_11` |
| Lemma 5.2.12, (5.22), Ex 5.2.2, (5.25) | Well-posedness and order stability transfer; `v̂_σ = Fv_σ`, `v_σ = G_σ v̂_σ` | `FDP.lemma_5_2_12` |
| Thm 5.2.13, (5.23), p. 169 | Fundamental optimality, primary iff subordinate | `FDP.sub_isValueFunction`, `FDP.primary_isValueFunction`, `FDP.fo_sub_of_primary`, `FDP.fo_primary_of_sub`, `FDP.theorem_5_2_13` |
| Prop 5.2.14, p. 171 | Converse under strict monotonicity of `F` | `FDP.proposition_5_2_14` |
| §5.2.3 | Order-reversing FDPs as order-preserving FDPs over `V̂^∂` | `FDP.dualize`, `FDP.dualize_isOrderPreserving`, `FDP.dualize_monotonic`, `FDP.dualize_primary`, `FDP.dualize_sub`, `FDP.dualize_Gsup` |
| Lemma 5.2.16, p. 172 | `T̂▿ = F ∘ G`; min-greedy policies | `FDP.lemma_5_2_16` |
| Lemma 5.2.17, (5.24), p. 172 | `(V, T)` and `(V̂, T̂▿)` strongly semiconjugate | `FDP.lemma_5_2_17` |
| Thm 5.2.18, (5.26), p. 173 | Max-optimality of the primary iff min-optimality of the subordinate | `FDP.theorem_5_2_18` |

## §5.3 Applications (pp. 174–181)

| Book | Claim | Lean |
| --- | --- | --- |
| §5.3.1, (5.27) | The Q-factor FDP; primary = MDP, subordinate = Q-factor model | `FiniteMDP.qfdp`, `FiniteMDP.qfdp_isOrderPreserving`, `FiniteMDP.qfdp_monotonic`, `FiniteMDP.qfdp_primary`, `FiniteMDP.qfdp_sub`, `FiniteMDP.le_Gsup`, `FiniteMDP.Gsup_eq_sup` |
| Prop 5.3.1, p. 175 | `v* = max_a q*`, `q* = r + βPv*`, optimal policies | `FiniteMDP.proposition_5_3_1` |
| Example A.1.12, Prop 5.3.2, p. 176 | No isolated point: Q-optimal implies MDP-optimal (`β > 0`) | `FiniteMDP.qfdp_F_strictMono`, `FiniteMDP.proposition_5_3_2`, `zeroDiscountMDP`, `proposition_5_3_2_needs_beta_pos` |
| §5.3.2, (5.28)–(5.30) | Structural estimation as an FDP | `seFDP`, `seFDP_isOrderPreserving`, `seFDP_monotonic`, `seFDP_sub`, `seFDP_primary_T`, `seFDP_primary_bellman`, `section_5_3_2` |
| §5.3.3, (5.31)–(5.33) | Epstein–Zin savings as an FDP | `powerSum_pos`, `powerMean_mono`, `aggr_mono`, `EZSavings`, `EZSavings.toEZ`, `EZSavings.Fraw`, `EZSavings.Graw`, `EZSavings.Pσ_eq`, `EZSavings.Vhat`, `EZSavings.Fraw_pos`, `EZSavings.Graw_mem`, `EZSavings.fdp`, `EZSavings.Vhat_pos`, `EZSavings.fdp_isOrderPreserving`, `EZSavings.fdp_monotonic` |
| Ex 5.3.1, (5.34), p. 179 | The primary ADP is the Epstein–Zin ADP | `EZSavings.exercise_5_3_1`, `EZSavings.primary_isIsomorphic` |
| Ex 5.3.2, (5.35), p. 180 | The subordinate policy operators | `EZSavings.exercise_5_3_2` |
| pp. 180–181, Algorithm 5.1 | Optimality via the subordinate ADP; HPI terminates | `EZSavings.section_5_3_3` |
