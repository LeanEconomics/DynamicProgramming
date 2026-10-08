# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 9, "Abstract Dynamic Programming" (pp. 292–307), and Appendix B.4
(pp. 349–351). Result, equation and exercise numbers are the book's; page numbers
are book pages. Lean names are relative to `SargentStachurski.AbstractDynamicProgramming`.
Where the Lean statement adds a hypothesis the book leaves implicit, see
[corrections](corrections.md).

## Earlier-chapter facts restated

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, Ch. 1–3, 6 | Markov matrices, contractions, Banach, spectral radius, affine maps | `IsMarkov`, `IsContractionOn`, `specRad`, `affineOp`, `globallyStable_affineOp`, `isFixedPt_affineOp_inv`, `specRad_smul_isMarkov` |
| Vol. 1, Thm 7.1.1 | Knaster–Tarski | `knaster_tarski` |
| Vol. 1, §8.1 | RDPs, policy operators, greedy policies, `v*`, HPI, OPI | `RDP`, `RDP.Tσ`, `RDP.T`, `RDP.greedy`, `RDP.antiGreedy`, `RDP.vσ`, `RDP.vstar`, `RDP.IsOptimal`, `RDP.opiW`, `RDP.opiValue` |
| Vol. 1, §8.1.3.6, Ex 8.1.12–8.1.13 | Bounded RDPs and the reduced RDP | `RDP.IsBoundedBy`, `RDP.Tσ_mapsTo_Icc`, `RDP.restrictIcc`, `RDP.vσ_mem_Icc`, `RDP.restrictIcc_wellPosed` |
| Vol. 1, (8.26), Prop 8.2.1, Cor 8.2.2 | Contracting RDPs | `RDP.IsContracting`, `RDP.IsContracting.isContractionOn_Tσ`, `RDP.IsContracting.isContractionOn_T`, `RDP.IsContracting.isGloballyStable`, `globallyStableOn_of_isContractionOn` |
| Vol. 1, §5.1.1, Example 8.1.1 | MDPs and their RDPs | `MDP`, `MDP.Pσ`, `MDP.rσ`, `MDP.toRDP`, `MDP.toRDP_Tσ`, `MDP.toRDP_isGloballyStable` |

## §9.1 Abstract dynamic programs (pp. 292–296)

| Book | Claim | Lean |
| --- | --- | --- |
| §9.1.1.1, p. 293 | Upward, downward and order stability | `OrderStable`, `orderStable_of_up_down` |
| Ex 9.1.1, p. 293 | `Tv = r + Av` with `A ≥ 0`, `ρ(A) < 1` is order stable | `orderStable_affineOp` |
| Lemma 9.1.1, p. 293 | Order-preserving globally stable maps are order stable | `orderStable_of_globallyStable`, `orderStable_restrict` |
| Lemma 9.1.2, p. 294 | Order stability on `V` iff on `V^∂` | `orderStable_dual_iff` |
| §9.1.2.2, p. 295 | ADPs, policies, greedy policies | `ADP`, `ADP.IsGreedy`, `ADP.greedy`, `ADP.isGreedy_greedy` |
| Example 9.1.1, p. 295 | RDPs generate ADPs | `RDP.toADP`, `RDP.toADP_T`, `RDP.toADP_wellPosed`, `RDP.toADP_vσ` |
| Example 9.1.2, p. 295 | MDPs generate ADPs | `MDP.toADP` |
| Example 9.1.3, (9.1)–(9.2), p. 296 | Q-factor ADP | `MDP.qOp`, `MDP.qGreedy`, `MDP.qMinGreedy`, `MDP.qOp_mono`, `MDP.qADP` |
| Example 9.1.4, (9.3)–(9.4), p. 296 | Risk-sensitive Q-factor ADP | `entropic_mono`, `MDP.rsqOp`, `MDP.rsqOp_mono`, `MDP.rsqADP` |

## §9.2 Optimality (pp. 297–306) and §B.4 (pp. 349–351)

| Book | Claim | Lean |
| --- | --- | --- |
| §9.2.1.1, p. 297 | Well-posedness, `σ`-value functions | `ADP.WellPosed`, `ADP.vσ`, `ADP.isFixedPt_vσ`, `ADP.eq_vσ_of_isFixedPt` |
| Example 9.2.1, p. 297 | MDP values `(I − βP_σ)⁻¹r_σ` | `MDP.toADP_vσ` |
| (9.5), Ex 9.2.1, pp. 297–298 | Bellman operator; greedy iff `T_σ v = Tv`; `T` order preserving | `ADP.bellman`, `ADP.T_le_bellman`, `ADP.isGreatest_bellman`, `ADP.isGreedy_iff`, `ADP.monotone_bellman`, `RDP.toADP_bellman` |
| p. 298 | Howard operator and HPI | `ADP.howard`, `ADP.hpiPolicy`, `ADP.hpiValue`, `ADP.hpiValue_succ` |
| §9.2.1.3, p. 298 | Finite, order stable, max-stable ADPs | `ADP.IsOrderStable`, `ADP.IsMaxStable`, `ADP.IsOrderStable.wellPosed`, `ADP.IsOrderStable.le_vσ`, `ADP.IsOrderStable.vσ_le` |
| Lemma B.4.1, p. 349 | (i) `v ∈ V_u ⇒ v ≼ Hv`; (ii) `Tv_σ = v_σ ⇒ v_σ = v*`; (iii) `Hv = v ⇒ v = v*`; (iv)–(v) HPI | `ADP.IsOrderStable.le_howard`, `ADP.IsOrderStable.isOptimal_of_isFixedPt`, `ADP.IsOrderStable.isFixedPt_of_howard`, `ADP.IsOrderStable.howard_fixed`, `ADP.IsOrderStable.hpiValue_le_succ`, `ADP.IsOrderStable.exists_hpiValue_succ_eq`, `ADP.IsOrderStable.hpi_terminates` |
| Prop 9.2.1, p. 299 | Finite and order stable implies max-stable | `ADP.IsOrderStable.isMaxStable` |
| Cor 9.2.2, p. 299 | `A_R` is max-stable for globally stable `R` | `RDP.toADP_isOrderStable`, `RDP.toADP_isMaxStable` |
| Ex 9.2.2, p. 299 | The Q-factor ADP is max-stable | `MDP.qOp_isContractionOn`, `MDP.qADP_isMaxStable` |
| Prop 9.2.3, p. 299 | On an order interval, well-posed iff order stable | `RDP.toADP_wellPosed_iff` |
| Ex 9.2.3, p. 300 | `V_Σ ⊆ V_u` | `ADP.Vu`, `ADP.vσ_mem_Vu` |
| p. 300 | Value function, optimal policies | `ADP.IsOptimal` |
| Thm 9.2.4, p. 300 | Max-optimality, (i)–(v) | `ADP.IsOrderStable.maxOptimality` |
| Prop 9.2.5, p. 300 | Max-stable ADPs, (i)–(iv) | `ADP.IsMaxStable.optimality` |
| §9.2.1.6, Ex 9.2.4–9.2.5, (9.6), p. 301 | Mixed strategies | `RDP.IsMixed`, `RDP.Mixed`, `RDP.Tmix`, `RDP.dirac`, `RDP.isMixed_dirac`, `RDP.Tmix_dirac`, `RDP.Tmix_le_T`, `RDP.Tmin_le_Tmix`, `RDP.Tmix_le_Tmix_of_supported` (Ex 9.2.4), `RDP.isGreatest_Tmix` (Ex 9.2.5), `RDP.Tmix_monotoneOn`, `RDP.mixedADP`, `RDP.mixedADP_bellman` |
| Ex 9.2.6, p. 301; p. 302 | Mixed operators are contractions; `v̂* = v*` | `RDP.IsContracting.isContractionOn_Tmix`, `RDP.mixed_value_eq_vstar` |
| §9.2.2.1, p. 302 | Translating Theorem 9.2.4 to RDPs | `RDP.le_vσ_of_le_Tσ`, `RDP.vσ_le_of_Tσ_le`, `RDP.optimality_of_orderStable` |
| Lemma 9.2.6, p. 302 | `Tᵏv → v*` for `v ∈ V_Σ` | `RDP.tendsto_iterate_T_vσ` |
| Lemma 9.2.7, p. 302 | `W_m V_u ⊆ V_u`, `Tv ≼ W_m v ≼ Tᵐv` | `RDP.iterate_Tσ_le_iterate_T`, `RDP.opiW_spec` |
| Lemma 9.2.8, p. 303 | `Tᵏv ≼ W_mᵏv` | `RDP.iterate_T_le_opi` |
| Lemma 9.2.9, p. 303 | A repeated OPI value is `v*` | `RDP.opi_stop` |
| Lemma 9.2.10, p. 303 | Greedy policies eventually optimal | `RDP.eventually_optimal` |
| Thm 8.1.1, p. 304 | Proof via ADPs | `RDP.optimality_of_globallyStable` |
| Thm 8.1.2, p. 304 | Proof via ADPs | `RDP.optimality_of_bounded` |
| §9.2.3, p. 305 | Min-greedy, Bellman min-operator, min-optimal, min-stable; the dual ADP | `ADP.dual`, `ADP.dual_dual`, `ADP.IsMinGreedy`, `ADP.minBellman`, `ADP.IsMinOptimal`, `ADP.IsMinStable` |
| Ex 9.2.7, p. 306 | Duality dictionary (i)–(vi) | `ADP.isMinGreedy_iff` (i), `ADP.isLeast_minBellman`, `ADP.isMinGreedy_iff_eq` (ii), `ADP.minHpi_isMinGreedy` (iii), `ADP.isOrderStable_dual_iff` (iv), `ADP.isMinStable_iff`, `ADP.WellPosed.dual`, `ADP.dual_vσ` (v), `ADP.isMinOptimal_iff` (vi) |
| Thm 9.2.11, p. 305 | Min-optimality | `ADP.minOptimality`, `ADP.minHpi_terminates`, `RDP.toADP_isMinStable` |
