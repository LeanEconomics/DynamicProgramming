# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 9, pp. 199–228. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.HarrisRecurrence`; names from Mathlib are marked as such. Names
marked "carried" are in the modules copied from the Chapter 1–6 and 8 projects (see the
[README](../README.md)). "`ψ`-irreducible" is `IsMaximalIrreducibility P ψ` throughout, and
`B⁺(X)` is the class of measurable sets of positive `ψ`-measure. Every place where the Lean
statement departs from the book is listed in [corrections](corrections.md).

## Chapter 9 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 199 | The event `{Φ ∈ A i.o.} = ⋂_N ⋃_{k ≥ N} {Φₖ ∈ A}` is `F`-measurable; it is `{η_A = ∞}` | `ioSet`, `ioSet_eq_iInter`, `measurableSet_ioSet`, `mem_ioSet_iff_occTime`; `ioSet_mono`, `shift_mem_ioSet_iff`, `ioSet_subset_firstReturn` |
| (9.1), p. 199 | `Q(x, A) = P_x{Φ ∈ A i.o.}` | `harrisQ`, `harrisQ_eq_occTime` (`= P_x(η_A = ∞)`), `measurable_harrisQ`, `harrisQ_le_one`, `harrisQ_mono` |
| p. 199 | `Q(x, A) ≤ L(x, A)` | `harrisQ_le_hitProb` |
| (9.2), p. 199 | By the strong Markov property, `Q(x, A) = E_x[P_{Φ_{τ_A}}{Φ ∈ A i.o.}; τ_A < ∞] = ∫_A U_A(x, dy) Q(y, A)` | `harrisQ_eq_firstReturn`, `harrisQ_eq_tabooPotKernel`, from `setLIntegral_firstReturn_eq_tabooPotKernel` (the law of `Φ_{τ_A}` on `{τ_A < ∞}` is `U_A(x, ·)`; `tabooPotKernel`, carried) and the strong Markov property for shift-invariant events, `pathKernel_inter_ne_top_of_shiftInvariant` (`IsShiftInvariant`, `isShiftInvariant_ioSet`); also `harrisQ_eq_lintegral_pow`, `pathKernel_shiftInvariant_eq_pow`, `harrisQ_ge_stopping` |
| p. 199 | `A` is Harris recurrent if `Q(x, A) = P_x(η_A = ∞) = 1` for `x ∈ A`; `Φ` is Harris if it is ψ-irreducible and every set in `B⁺(X)` is Harris recurrent | `IsHarrisRecurrentSet`, `IsHarris` (`ψ` maximal) |
| p. 200 | When `Φ` is Harris and `A ∈ B⁺(X)`, `Q(x, A) = 1` for every `x` | `theorem_9_1_4` |
| p. 200 | A Harris recurrent set is recurrent | `IsHarrisRecurrentSet.isRecurrentSet`; for chains, `IsHarris.isRecurrentChain`; `potKernel_eq_top_of_harrisQ_pos`, `harrisQ_eq_zero_of_potKernel_ne_top` |
| p. 200 | Harris recurrence is equivalent to `L(x, A) ≡ 1` on `A` | `proposition_9_1_1` |
| Theorem 9.0.1, (9.3), p. 200 | A recurrent chain has `X = H ∪ N` with `H` absorbing and non-empty, every subset of `H` in `B⁺(X)` Harris recurrent, and `N` ψ-null and transient | `theorem_9_0_1` (countably generated `X`), from `theorem_9_1_5` |
| p. 200 | On a countable space `N` is empty, so recurrent chains are Harris | `isHarris_of_countable` (irreducible, recurrent for counting measure; `IsIrreducibleChain`, carried) |
| p. 200 | `Φ → ∞` if the path visits each compact set only finitely often | `tendsToInfty` |
| Theorem 9.0.2, p. 200 | A ψ-irreducible T-chain is Harris iff `P_x{Φ → ∞} = 0` for every `x` | `theorem_9_0_2` (`IsTChain`, carried), from `theorem_9_2_2_ii` |
| pp. 199–200 | The overview of the chapter | Not formalised (informal) |

## §9.1.1 Harris properties of sets

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 9.1.1, p. 201 | If `L(x, A) ≡ 1` on `A`, then `Q(x, A) = L(x, A)` for every `x`, and `A` is Harris recurrent | `proposition_9_1_1` |
| p. 201 | Proof: `P_x(τ_A(k + 1) < ∞) = ∫_A U_A(x, dy) P_y(τ_A(k) < ∞) = 1` on `A`, `P_x(η_A ≥ k) = P_x(τ_A(k) < ∞)`, and `Q(x, A) = lim_k P_x(η_A ≥ k)` | The induction is on `P_x(η_A ≥ k)`: `pathKernel_occTime_ge_succ` (`P_x(η_A ≥ k + 1) = E_x[P_{Φ_{τ_A}}(η_A ≥ k); τ_A < ∞]`), `setOf_occTime_eq_top`, `measurableSet_le_occTime`; `le_occTime_of_returnTimeK`, `le_occTimeN_of_returnTimeK` (`returnTimeK`, carried) |
| p. 201 | The strong law: `P_0(lim n⁻¹Φₙ = β) = 1` for random walk with mean `β ≠ 0` | `ae_tendsto_partialSum`, from Mathlib's `ProbabilityTheory.strong_law_ae`, with the path law of the recursion `pathKernel_recursion` (under Mathlib's `Measure.infinitePi`) and `harrisQ_recursion` |
| (9.4)–(9.5), p. 202 | `P_0(lim sup Cₙ) = 0` for `Cₙ = {\|n⁻¹Φₙ − β\| > β/2}`, so `P_0(lim sup {Φₙ = 0}) = 0`, i.e. `Q(0, 0) = 0` | `eventually_abs_gt_of_tendsto_div`, `randomWalk_int_harrisQ_eq_zero` (`Q(x, {y}) = 0` for all `x, y`) |
| Proposition 9.1.2, p. 202 | Random walk on `ℤ` with `β = Σ wΓ(w) > 0` is transient | `proposition_9_1_2` (every `β ≠ 0`, integrable increments: `Q(x, {x}) = 0`, `L(x, {x}) < 1` and `x` is a transient state; `randomWalkKernel`, `IsTransientState`, carried), `proposition_9_1_2_chain` (an irreducible walk is a transient chain for counting measure) |
| Theorem 9.1.3 (i), (9.6), p. 202 | If `D ⇝ A`, then `{Φ ∈ D i.o.} ⊆ {Φ ∈ A i.o.}` a.s. `[P_*]`, so `Q(y, D) ≤ Q(y, A)` | `theorem_9_1_3_ae` (for every initial law `μ`, under `pathMeasure P μ`, carried), `theorem_9_1_3_i`, both with the weaker hypothesis `P_y(σ_A < ∞) ≥ δ > 0` on `D` (`hitProbZero`, carried); with the book's hypothesis `D ⇝ A` (`UnifAccessible`, carried): `theorem_9_1_3_i_unifAccessible`; `hitProb_le_hitProbZero` |
| (9.7)–(9.10), pp. 202–203 | `P(⋃_{i ≥ n} Eᵢ \| 𝓕ₙ^Φ) → 1{lim sup Eᵢ}` by the martingale convergence theorem, and `P_*(⋃_{i ≥ n} Eᵢ \| 𝓕ₙ^Φ) = L(Φₙ, A)` | With the complementary events `Hₖ = {Φⱼ ∉ A for j ≥ k}` (`noVisitFrom`, `noVisitFrom_eq_preimage`, `measurableSet_noVisitFrom`, `noVisitFrom_mono`, `exists_noVisitFrom_of_notMem_ioSet`), Lévy's upward theorem (Mathlib's `MeasureTheory.Integrable.tendsto_ae_condExp`) for `P_μ(Hₖ \| 𝓕ₙ^Φ)` and the Markov property `P_μ(Hₙ \| 𝓕ₙ^Φ) = P_{Φₙ}(σ_A = ∞)`, in the proof of `theorem_9_1_3_ae` (`natFilt`, carried) |
| Theorem 9.1.3 (ii), p. 202 | If `X ⇝ A`, `Q(x, A) ≡ 1` and `A` is Harris recurrent | `theorem_9_1_3_ii` (`P_x(σ_A < ∞) ≥ δ > 0` for every `x`) |
| Theorem 9.1.4, p. 203 | If `Φ` is Harris, `Q(x, B) = 1` for every `x` and `B ∈ B⁺(X)` | `theorem_9_1_4` (countably generated `X`) |
| p. 203 | Proof: an increasing cover by petite sets `Cₙ ∈ B⁺(X)` (Proposition 5.5.5), `Cₙ ⇝ B` (Lemma 5.5.1) and Theorem 9.1.3 (i) | `proposition_5_5_5_iii_cover` (carried); `IsPetite.unifAccessible` (Lemma 5.5.1 for petite sets, through `lintegral_pow_hitProb_le`); `theorem_9_1_3_i_unifAccessible` |

## §9.1.2 Harris recurrent chains

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 203–204 | Appending points `xᵢ` with `P'(xᵢ, xᵢ₊₁) = βᵢ`, `P'(xᵢ, α) = 1 − βᵢ` and `0 < ∏ βᵢ < 1` to a Harris chain gives a recurrent chain that is not Harris | The general construction is not formalised. An instance, with the escape path `eₖ` of `TopologicalExamples` as the appended points and jumps to the law `ν` in place of a point `α`: `cex_recurrent_not_harris` (recurrent, not Harris) |
| p. 204 | `D^∞ = {y : L(y, D) = 1}` contains a Harris recurrent `D` and is absorbing | `harrisInfty`, `harrisInfty_absorbing`; `le_hitProb_of_kernel` |
| p. 204 | `D` is maximal absorbing if `D = D^∞`; `H` is maximal Harris if it is maximal absorbing and `Φ` restricted to `H` is Harris | `IsMaximalHarrisSet` (`H` measurable, non-empty, absorbing, `H^∞ = H`, and `Q(x, A) = 1` for `x ∈ H`, `A ∈ B⁺(X)`; `IsAbsorbing`, carried) |
| Theorem 9.1.5, (9.11), p. 204 | A recurrent chain has `X = H ∪ N` with `H` a non-empty maximal Harris set and `N` transient | `theorem_9_1_5` (countably generated `X`; also `ψ(N) = 0`) |
| pp. 204–205 | Proof: `H = {Q(·, C) = 1}` for a petite `C ∈ B⁺(X)`; if `H = ∅`, `C₁ = {x ∈ C : L(x, C) < 1} ∈ B⁺(X)` by Propositions 4.2.3 and 9.1.1, and Proposition 8.3.1 (iii) contradicts recurrence; `N` is transient by Proposition 8.3.7; Theorem 9.1.3 makes `Φ` restricted to `H` Harris | In the proof of `theorem_9_1_5`: `exists_petite_pos`, `prob_eq_one_of_lintegral_eq_one` (`H` absorbing), `harrisQ_ge_stopping` (`H` maximal), `psi_pos_hitProb_lt_one` (`C₁ ∈ B⁺(X)`; `proposition_4_2_3_ii`, carried), `proposition_8_3_1_iii`, `proposition_4_2_3_i`, `proposition_8_3_7` (carried) |
| Theorem 9.1.6, p. 205 | An aperiodic ψ-irreducible chain is Harris iff each skeleton is | `theorem_9_1_6` (countably generated `X`; `IsAperiodic`, carried) |
| p. 205 | Proof: `mτ_A^m ≥ τ_A`; conversely the skeleton is recurrent by "Proposition 8.2.6", has a Harris set `H_m`, and `mτ_H^m ≤ τ_H + m` | `pathKernel_map_skeleton` (the law of `(Φ_{mn})ₙ` is the path measure of `Pᵐ`), `harrisQ_skeleton_le` (`Qₘ ≤ Q`), `isHarris_of_skeleton` (no aperiodicity needed). The converse uses Theorem 8.2.6 (`theorem_8_2_6_ii`, carried), which is what "Proposition 8.2.6" refers to, and `proposition_4_2_3_ii` |

## §9.1.3 A hitting time criterion for Harris recurrence

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 9.1.7 (i), p. 205 | If some petite `C` is recurrent, `Φ` is recurrent, and `C ∩ N` is uniformly transient for the `N` of (9.11) | `proposition_9_1_7_i` (`C ≠ ∅`; countably generated `X`; for every maximal Harris set `H`, `N = Hᶜ`); `isUniformlyTransient_of_escape`, `IsPetiteSet.exists_pow_absorbing_ge`, `ae_stays_of_absorbing` |
| Proposition 9.1.7 (ii), p. 205 | If a petite `C` has `L(x, C) ≡ 1` on `X`, `Φ` is Harris | `proposition_9_1_7_ii` |
| Theorem 9.1.8, p. 206 | If `C` is petite and `V` is unbounded off petite sets with (V1), `Φ` is Harris | `theorem_9_1_8` (countably generated `X`; `V : X → ℝ≥0` measurable, every `{V ≤ n}` petite; `drift`, `IsPetite`, carried) |
| p. 206 | Proof: `L(x, C ∪ C_V(n)) ≡ 1` from Theorem 8.4.3 and Proposition 9.1.7 | `lemma_8_4_3_hitProb`, `proposition_5_5_5_ii` (carried) and `proposition_9_1_7_ii`, in the proof of `theorem_9_1_8` |

## §9.2.1 Evanescence and transience

| Source | Claim | Lean |
| --- | --- | --- |
| p. 206 | Stability on topological spaces is described on compact and open sets | Not formalised (informal) |
| p. 206 | By Lindelöf's theorem `{Φ → ∞} = ⋂ₙ {Φ ∈ Oₙ i.o.}ᶜ` for open precompact `Oₙ`, so `{Φ → ∞} ∈ F` | `tendsToInfty_eq_iInter` (for a compact exhaustion `Kₙ`), `measurableSet_tendsToInfty`; `isShiftInvariant_tendsToInfty` |
| p. 206 | `Φ` is non-evanescent if `P_x{Φ → ∞} = 0` for each `x` | `IsNonEvanescent`; `pathKernel_tendsToInfty_eq_zero` (`Q(y, K) = 1` for a compact `K` gives `P_y{Φ → ∞} = 0`) |
| Theorem 9.2.1, (9.12), p. 207 | For a T-chain and a transient `A`, `P_x({Φ → ∞} ∪ {Φ enters A⁰}) = 1`, `A⁰ = {y : L(y, A) = 0}`; so a non-evanescent T-chain does not have `X` transient | `theorem_9_2_1` (with `{Φ ∈ A⁰ i.o.}`; `noHitSet`, carried), `theorem_9_2_1_enters` (the book's form), `theorem_9_2_1_not_transient` |
| p. 207 | Proof: `Ā` is a countable union of uniformly transient `Aᵢ` (Proposition 8.3.2) | `IsTransientSet.exists_cover_hitSet`, `hitSet_subset_iUnion`, `hitProb_le_tsum` |
| (9.13), p. 207 | `K_a(x, Aᵢ) ≥ T(x, Aᵢ) ≥ j⁻¹` on `Oᵢⱼ`, a finite subcover of a compact `C`, and `L(x, A⁰) > 1/M` on `O_M` with Theorem 9.1.3 | `sampledKernel_le_hitProbZero` (the corrected (5.45), `K_a(x, B) ≤ P_x(σ_B < ∞)`, through `hitProbZero_eq_exists`; `sampledKernel`, carried), `ioSet_union`, `ioSet_biUnion_range`, and `theorem_9_1_3_ae` with the first hitting time, in the proof of `theorem_9_2_1` |

## §9.2.2 Non-evanescence and recurrence

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 9.2.2, (9.14), p. 207 | For a ψ-irreducible T-chain, `X = H ∪ N` with `H` empty or a maximal Harris set, `N` transient, and `L(x, H) = 1 − P_x{Φ → ∞}` | `theorem_9_2_2`; (9.14) for a maximal Harris set: `hitProb_maximalHarris_eq`; in the transient case `P_x{Φ → ∞} = 1`: `pathKernel_tendsToInfty_of_transient`; `exists_compact_pos` |
| Theorem 9.2.2 (i), p. 207 | The chain is recurrent iff `P_x{Φ → ∞} < 1` for some `x` | `theorem_9_2_2_i` |
| Theorem 9.2.2 (ii), p. 207 | The chain is Harris iff it is non-evanescent | `theorem_9_2_2_ii`, `theorem_9_0_2` |
| p. 208 | Proof: Theorem 9.1.5 in the recurrent case and Theorem 8.3.4 otherwise; (9.14) from (9.12) with `H = N⁰` | In the proof of `theorem_9_2_2` (`theorem_8_3_4`, carried) |

## §9.3.1 Classifying states through neighbourhoods

| Source | Claim | Lean |
| --- | --- | --- |
| p. 208 | Uses of "recurrence" vary across the literature | Not formalised (remark) |
| p. 208 | `x*` is topologically recurrent if `U(x*, O) = ∞` for all neighbourhoods `O`, and topologically transient otherwise; topologically Harris recurrent if `Q(x*, O) = 1` for all neighbourhoods `O` | `IsTopRecurrent`, `IsTopTransient`, `IsTopHarrisRecurrent` (open neighbourhoods); `IsTopHarrisRecurrent.isTopRecurrent` |
| Proposition 9.3.1, p. 208 | `x*` is topologically Harris recurrent iff `L(x*, O) = 1` for all neighbourhoods `O` | `proposition_9_3_1` (`T₁`, first countable) |
| (9.15)–(9.21), p. 209 | Induction on the `j`-th return `τ_O(j)`, with `q = U_O(x*, {x*})` and a countable neighbourhood basis `O_d ↓ {x*}` | In the proof of `proposition_9_3_1`, with the induction on `P_{x*}(η_O ≥ j) = 1` for every open `O ∋ x*`, the strong Markov property at `τ_O` (`strong_markov_lintegral`, carried) and a countable neighbourhood basis; `occTime_le_shift_of_firstReturn` (from `occTime_split` and `occTime_mono`), `measurableSet_stoppedField_stoppedState` |

## §9.3.2 Solidarity of recurrence for T-chains

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 9.3.2, p. 209 | If `T(x*, B) > 0`, some neighbourhood `O` of `x*` has `O ⇝ᵃ B`, "and hence from Lemma 5.5.1, `O ⇝ B`" | `lemma_9_3_2` (`O` open, `O ⇝ᵃ B`, and `P_y(σ_B < ∞) ≥ δ > 0` on `O`; `IsContinuousComponent`, `IsSamplingDist`, `SampledAccessible`, carried). The step "`O ⇝ B`" needs `a(0) = 0`: `lemma_9_3_2_counterexample` (`toTrueKernel`, carried; `boolIdKernel`) |
| p. 210 | Proof: `inf_O L(·, B) ≥ inf_O K_a(·, B) ≥ inf_O T(·, B)` "as in (5.45)" | `L ≥ K_a` needs `a(0) = 0` (`lemma_5_5_1_counterexample`, carried); `sampledKernel_le_hitProbZero` is used instead |
| Theorem 9.3.3, p. 210 | For a ψ-irreducible T-chain and a reachable `x*`, `Φ` is recurrent iff `x*` is topologically recurrent | `theorem_9_3_3` (`IsReachable`, carried); `exists_open_uniformlyTransient`, `isTopTransient_of_transient` |
| (9.22)–(9.23), p. 210 | On `[0, 1] ∪ {2}`, a T-chain for which `{0}` is topologically recurrent but not topologically Harris recurrent | Not formalised. The phenomenon, for a ψ-irreducible T-chain: `cex_isTopRecurrent`, `cex_not_isTopHarrisRecurrent` (`cexKernel`, `cex_isTChain`, `cex_isMaximalIrreducibility`) |
| (9.24), pp. 210–211 | On `{0, ±1, ±2, …, ±∞}`, a Feller chain for which `−∞` is topologically recurrent but not topologically Harris recurrent | Not formalised |
| Proposition 9.3.4 (i), p. 211 | For a T-chain, a topologically recurrent `x*` has `Q(x*, O) > 0` for every neighbourhood `O` | `proposition_9_3_4_i` (a continuous component `T` of `K_a` with `T(x*, X) > 0`) |
| (9.25)–(9.29), pp. 211–212 | `T(x*, [O^∞]ᶜ) > 0`, `Dₙ = {Pᵧ(η_O < n) > n⁻¹}`, `P_x(τ_{Dₙ} ≤ m) > δ/2m` on `O_δ`, and `O_δ` is uniformly transient | `exists_uniformlyTransient_nhds_of_infty`, with the first hitting time: `P_x(σ_{Dₙ} ≤ m) ≥ ε` on `O_δ`; `isUniformlyTransient_of_occTime_ge` ((8.35)), `occTime_le_add_shift`, `stoppedState_firstHit_mem` |
| Proposition 9.3.4 (ii), p. 211 | If `P(x*, ·) ≅ T(x*, ·)`, a topologically recurrent `x*` is topologically Harris recurrent; in particular for strong Feller chains | `proposition_9_3_4_ii` (`P(x*, ·) ≪ T(x*, ·)` suffices), `proposition_9_3_4_strongFeller` (`IsStrongFeller`, carried) |
| p. 212 | The examples (9.22) and (9.24) show that the second conclusion fails for weak Feller chains and chains with only a strong Feller component; this behaviour is due to the lack of irreducibility and is excluded for ψ-irreducible T-chains by Theorem 9.3.6 | The examples are not formalised. The claim that irreducibility excludes the behaviour is false: `theorem_9_3_6_counterexample` |
| Theorem 9.3.5, p. 212 | For any chain, `X = R ∪ N` with `R` the topologically Harris recurrent states and `N` transient | `theorem_9_3_5` (`T₁`, second countable; `N = Rᶜ`) |
| p. 212 | The sets `Dₙ(j)` need not be open, and topologically recurrent states can lie in the transient part, as in (9.22) | Shown for a ψ-irreducible T-chain by `theorem_9_3_6_counterexample` |
| Theorem 9.3.6, p. 213 | For a ψ-irreducible T-chain, `X = H ∪ N` with `H` "non-empty or" a maximal Harris set and `N` transient; `R ⊆ H`; every state in `N` is topologically transient | The last claim is false: `theorem_9_3_6_counterexample` (`CexSpace = ℕ∞ ⊕ ℕ`, `cexKernel`, `cexStar`, `cexNu`). Corrected: `theorem_9_3_6` (`H` empty or a maximal Harris set; every `x* ∈ N` has an open `O ∋ x*` with `O ∩ N` uniformly transient, and is topologically transient when `T(x*, H) = 0`); `IsTopHarrisRecurrent.pathKernel_tendsToInfty` |
| p. 213 | Proof: `R ⊆ H` by (9.14) and maximality; `N_H = {T(·, H) > 0}` and `N_E = {T(·, H) = 0}`; `O_δ = {T(·, H) > δ}` is uniformly transient by (8.35) | `O_δ` may meet `H`; `O_δ ∩ N` is uniformly transient, in the proof of `theorem_9_3_6` |
| p. 213 | The trivial example `P(x, {0}) = 1` on `[0, 1]`: a `δ₀`-irreducible strong Feller chain with `R = {0}` and `H = [0, 1]` | `example_9_3_6` (on `ℝ`; `toZeroKernel`, `ae_toZero`, `toZero_harrisQ`) |

## §9.4.1 A drift criterion for non-evanescence

| Source | Claim | Lean |
| --- | --- | --- |
| p. 213 | `V` is coercive if `V(x) → ∞` as `x → ∞`: the sublevel sets `{V ≤ r}` are precompact | `IsCoercive` (`V : X → ℝ≥0`, every `closure {V ≤ r}` compact) |
| p. 214 | Coercive functions behave like norms; for irreducible T-chains they are unbounded off petite sets | Not formalised (remark) |
| Theorem 9.4.1, p. 214 | (V1) for a coercive `V` and a compact `C` makes `Φ` non-evanescent | `theorem_9_4_1` (no irreducibility) |
| (9.30), p. 214 | If `P_x{Φ → ∞} > 0`, conditioning at time `M` gives `P_μ({σ_C = ∞} ∩ {Φ → ∞}) > 0` for `μ = Pᴹ(x, ·)` | `pathKernel_shift_preimage` (`P_x(θⁿΦ ∈ E) = ∫ Pⁿ(x, dy) P_y(E)`), in the proof of `theorem_9_4_1` |
| p. 214 | `Mᵢ = V(Φᵢ)1{σ_C ≥ i}` is a positive supermartingale and converges a.s. to a finite `M_∞` | `killedV`, `killedVE`, `avoidSet`, `measurableSet_natFilt_avoidSet`, `setLIntegral_killedVE_succ_le`, `lintegral_killedVE_le`, `integrable_killedV`, `supermartingale_killedV` (Mathlib's `MeasureTheory.Supermartingale` for `natFilt`, carried), `ae_tendsto_killedV` (Mathlib's `MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`), `ae_bddAbove_of_avoid` |
| p. 214 | The chain on `ℝ₊` with `P(0, {1}) = 1` and `P(x, {x}) = 1` for `x > 0` satisfies (V1) with `V(x) = x` and `C = {0}`, is non-evanescent, and does not reach `C` | `example_9_4_1` (on `ℝ`, with `V(x) = \|x\|`; `L(x, {0}) = 0` for every `x`); `exampleMap941`, `deterministic_pow_apply`, `ae_orbit_deterministic` |
| p. 214 | If `Φ` is ψ-irreducible and (V1) holds for a petite `C`, both `C` and `Φ` are Harris | `theorem_9_1_8`; for T-chains with a coercive `V` and a compact `C`: `isHarris_of_coercive` (`C` Harris recurrent when `ψ(C) > 0`) |

## §9.4.2 A converse theorem for Feller chains

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 9.4.2, (9.31), p. 215 | For a weak Feller chain and a compact `C` with `σ_C < ∞` a.s. `[P_*]`, there are a compact `C₀ ⊇ C` and a coercive `V`, bounded on compacta, with `ΔV ≤ 0` on `C₀ᶜ` | `theorem_9_4_2` (`IsWeakFeller`, carried; `P_x(σ_C < ∞) = 1` for every `x`; `V` measurable) |
| (9.32)–(9.34), p. 215 | `Vₙ(x) = P_x(σ_{Dₙ} < σ_{A₀})` satisfies `∫ P(x, dy)Vₙ(y) = Vₙ(x)` off `A₀ ∪ Dₙ` and `Vₙ = 1` on `Dₙ` | `beforeEvent`, `measurableSet_beforeEvent`, `shift_one_mem_beforeEvent`, `subset_beforeEvent_zero`, `beforeEvent_first_step` |
| (9.35)–(9.39), pp. 215–216 | `V = Σᵢ V_{nᵢ}`, with `mᵢ` and `nᵢ` chosen by uniform convergence on compacta of upper semicontinuous functions (Proposition 6.1.1), so that `V ≤ k + 1` on `A_k` | In the proof of `theorem_9_4_2`, through the complementary lower semicontinuous functions: `lsc_exists_le`, `lsc_forall_lt` and Dini's argument `exists_index_lt_of_lsc`; `one_sub_le_of_one_sub_lt` |
| p. 216 | A δ₀-irreducible recurrent T-chain on `ℝ₊` with rational states `rₙ` for which no continuous coercive `V` satisfies (V1), while a discontinuous one does | Not formalised |

## §9.4.3 Non-evanescence of random walk

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 9.4.3, p. 216 | For `s > 0` and `B ⊆ {−s + tw > 0}`, `E[log(−s + tW); B] ≤ P(B)(log s − 2) + (t/s)E[W; B]` | `lemma_9_4_3` (`W` and `log(−s + tW)` integrable on `B`) |
| Lemma 9.4.4, (9.40)–(9.41), p. 217 | For finite variance, `lim_{x → −∞} x²[−Γ(−∞, t₁ + sx) log(u₁ − u₂x) + Γ(−∞, t₂ + sx)(log(v₁ − v₂x) − c)] ≤ 0`, and the reflected limit as `x → ∞` | `lemma_9_4_4_i`, `lemma_9_4_4_ii`, with `lim sup`: for every `ε > 0` the expression is eventually `≤ ε`; `tendsto_sq_mul_lowerTail` |
| Proposition 9.4.5, p. 217 | Random walk on `ℝ₊` with `β = 0` and `E(W²) < ∞` is non-evanescent | `proposition_9_4_5`, for the unrestricted walk on `ℝ` (`randomWalkKernel`, carried) |
| (9.42)–(9.43), pp. 217–218 | `V(x) = log(1 + \|x\|)` off `[−R, R]`, `0` on it; `V₁, …, V₅` bounded by Lemmas 8.5.2, 8.5.3, 9.4.3 and 9.4.4 | `V(x) = log(1 + \|x\|)` on all of `ℝ` (`isCoercive_log_one_add_abs`, `integrable_log_one_add_abs`); the drift bound `randomWalk_log_drift`, `randomWalk_log_drift_abs`, `lintegral_log_one_add_abs_le`, from a pointwise bound with `log_one_add_le` (carried) |

## §9.5.1 Linear models and the stochastic comparison technique

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 218–219 | Increment analysis linearises the motion of the chain; stochastic comparison classifies chains through return times | Not formalised (informal) |
| (9.44), p. 219 | `P_x(τ_C ≥ n) ≤ P'_x(τ_C ≥ n)` for `x ∈ Cᶜ` and all `n` | The hypothesis `hcomp` of `comparison_harris` and `comparison_transient`; `hitProb_le_of_comparison` (`L'(x, C) ≤ L(x, C)`), `pathKernel_firstReturn_top_eq_iInf` |
| p. 219 | If `C` is petite and `P'_x(τ_C ≥ n) → 0` off `C`, `Φ` is Harris | `comparison_harris` (`C` petite for `Φ` only) |
| p. 219 | If `Φ` has `L(x, C) < 1 − ε` on `D ⊆ Cᶜ` with `φ(D) > 0`, then `Φ'` is transient | `comparison_transient` (`C, D ∈ B⁺(X)` for `Φ'`, through `theorem_8_3_6_ii`, carried) |
| Proposition 9.5.1, p. 219 | Random walk on `ℝ₊` with `β > 0` is transient | `proposition_9_5_1` (integrable increments): `Q(x, [0, c]) = 0` for all `x, c`, and transience for every maximal `ψ` (`halfLineWalkKernel`, carried); `halfLine_harrisQ_eq_zero` |
| (9.45), pp. 219–220 | Discretisation `Γ_h`, the claim that the discretised walk is stochastically smaller, and `β_h ≥ β − h` | Replaced by the pathwise bound `Φₙ ≥ x + W₁ + ⋯ + Wₙ` and the strong law (`halfLine_harrisQ_eq_zero`) |
| Proposition 9.5.2, p. 220 | If `W` is symmetric with a density positive on `[−R, R]` and zero elsewhere, the scalar linear model is Harris iff `\|α\| ≤ 1` | `proposition_9_5_2_full` (`Γ ≪ Leb\|[−R,R]`, `Leb\|[−R,R] ≪ Γ`, `Γ` symmetric; Harris for some maximal `ψ`; `ar1Kernel`, carried). With irreducibility and the T-chain property as hypotheses and bounded mean-zero noise: `proposition_9_5_2`; `proposition_9_5_2_necessity` (bounded noise only), `proposition_9_5_2_sufficiency` (mean zero, finite variance) |
| p. 220 | Proof: "the linear model is … a `μ^Leb`-irreducible chain on `ℝ` with all compact sets petite" | False for `\|α\| < 1`: `proposition_9_5_2_not_leb_irreducible`. Irreducibility for `Leb\|[−R/2, R/2]` when `\|α\| ≤ 1`: `ar1_isPhiIrreducible`, from `ar1_kernel_pos`, `ar1_pow_pos`; the T-chain property: `ar1_isTChain`; `ar1_noise_support`, `ar1_integral_eq_zero` |
| p. 220 | Proof for `α > 1`, `α < −1`, `0 < α ≤ 1` and `−1 ≤ α ≤ 0` by comparison with random walk | Necessity: `\|Xₙ\| ≥ \|x\|` from far away and Theorem 9.1.4, in `proposition_9_5_2_necessity`. Sufficiency: `V(x) = log(1 + \|x\|)` with `ar1_log_drift_contract` for `\|α\| < 1` and `randomWalk_log_drift_abs` for `\|α\| = 1`, Theorem 9.4.1 and Theorem 9.2.2 (ii), in `proposition_9_5_2_sufficiency` |
| p. 221 | Points (i)–(ii): the difficulties of comparison arguments on the whole line | Not formalised (remarks) |

## §9.5.2 Unrestricted random walk and SETAR models

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 9.5.3, p. 221 | An irreducible random walk on `ℝ` with non-zero mean is transient | `proposition_9_5_3` (integrable increments; for every maximal `ψ`); `randomWalk_real_evanescent` (`P_x{Φ → ∞} = 1`), `randomWalk_real_harrisQ_eq_zero`, `eventually_gt_of_tendsto_div_pos`, `isTransientChain_of_harrisQ_lt_one` |
| p. 221 | Proof by comparison with the walk on the half line | Replaced by the strong law along the path (`ae_tendsto_partialSum`) |
| p. 221 | The walk is non-evanescent when `β = 0` and the variance is finite | `proposition_9_4_5` |
| p. 221 | The SETAR model `Xₙ = φ(j) + θ(j)Xₙ₋₁ + Wₙ(j)` for `Xₙ₋₁ ∈ Rⱼ = (r_{j−1}, rⱼ]` | `setarKernel`, `setarStep` (carried; regime `1` is `0 : Fin (m + 1)`, regime `M` is `Fin.last m`); beyond `±ρ`, `ρ = 1 + Σ\|rᵢ\|`, the chain is in an end regime: `setarBound`, `one_le_setarBound`, `abs_lt_setarBound`, `setarRegime_of_gt`, `setarRegime_of_lt`, `setarStep_of_gt`, `setarStep_of_lt` |
| (9.46)–(9.51), p. 222 | The exterior of the parameter space | The six regions, as hypotheses of `proposition_9_5_4_46`, `proposition_9_5_4_47`, `proposition_9_5_4_48`, `proposition_9_5_4_49`, `proposition_9_5_4_50`, `proposition_9_5_4_51`, and the disjunction `hext` of `proposition_9_5_4` |
| (SETAR3), p. 222 | Finite variances in the two end regimes | Not assumed |
| Proposition 9.5.4, p. 222 | Under (SETAR1)–(SETAR3) the chain is transient in the exterior of the parameter space | `proposition_9_5_4` ((SETAR2) as `Γⱼ ≪ volume` and `volume ≪ Γⱼ`; zero-mean integrable noise in the end regimes; transient for Lebesgue measure, by `proposition_6_3_6`, carried) |
| p. 222 | (9.47): comparison with the last linear model; (9.46) by symmetry | `proposition_9_5_4_47`, `proposition_9_5_4_46` (geometric escape; only integrable noise in the end regime is used), with `escape_of_lower_recursion`, `ae_bdd_weighted_sum`, `exists_measure_pos_forall_le`, `hitProb_recursion_lt_one`, `setar_transient_of_escape` |
| p. 222 | (9.50): the same argument for the two-step chain | `proposition_9_5_4_50` (the signed path `(−1)ⁿXₙ` satisfies a linear lower recursion with multipliers `\|θ(M)\|`, `\|θ(1)\|`) |
| p. 222 | (9.48), (9.49): random walk with drift away from the thresholds (§8.5) | `proposition_9_5_4_48`, `proposition_9_5_4_49` (only `θ(1) = 1`, `φ(1) < 0`, resp. `θ(M) = 1`, `φ(M) > 0`, and the mean-zero noise of that regime are used); `ae_bdd_partialSum_of_neg` |
| (9.52)–(9.56), pp. 222–224 | (9.51) by Theorem 8.4.2 with a piecewise test function, which needs (SETAR3) | Replaced by a pathwise argument: `proposition_9_5_4_51`, with the strong law for two-step blocks `ae_tendsto_blockSum` (from Mathlib's `ProbabilityTheory.strong_law_ae`) and `exists_bdd_of_eventually_nonpos`; `measurable_noise`, `setar_noise_lintegral_ne_top`, `setar_integrable_noise`, `setar_integral_noise` |
| p. 222 | "as in the proof of Theorem 9.5.2" | Proposition 9.5.2 is meant |

## §9.5.3 General chains with bounded increments

| Source | Claim | Lean |
| --- | --- | --- |
| (9.57), p. 224 | The increment `W_x = Φ₁ − Φ₀` given `Φ₀ = x`, with law `Γ_x` | `Φ₁ − x` under `P(x, ·)`, for a kernel on `ℝ≥0` |
| pp. 224–225 | The mean drift `m(x) = E_x[W_x]` and the second moment `v(x) = E_x[W_x²]` | `meanDrift`, `incrementVar`, `incrementVar_nonneg` |
| (9.58), p. 225 | Bounded increments: `Γ_x[−R, R] = 1` | `HasBoundedIncrements`; `integrable_of_boundedIncrement` |
| p. 225 | The standing assumption: enough weight on the negative half line for a `δ₀`-irreducible T-chain with `v` bounded from zero | Replaced by explicit hypotheses: a maximal irreducibility measure `ψ`, petite sets `[0, c]` (Theorem 9.5.5 (i)), tails `(c, ∞)` in `B⁺(X)` (Theorem 9.5.5 (ii)) |
| Theorem 9.5.5 (i), (9.59), p. 225 | `m(x) ≤ θv(x)/2x` for `x > x₀` with `θ < 1` makes `Φ` recurrent | `theorem_9_5_5_i` (Harris recurrent) |
| (9.61)–(9.63), pp. 225–226 | `V(x) = log(1 + x)` and the Taylor expansion of (9.62) | `integral_log_le`, from `log_one_add_le_quadratic` and `le_quadratic_of_deriv2_le`; Theorem 9.1.8 (`theorem_9_1_8`) |
| Theorem 9.5.5 (ii), (9.60), p. 225 | `m(x) ≥ θv(x)/2x` for `x > x₀` with `θ > 1` makes `Φ` transient | `theorem_9_5_5_ii` |
| (9.64)–(9.67), p. 226 | `V(x) = 1 − (1 + x)^{−α}` with `α < θ − 1` and the expansion (9.67); "in order to use Theorem 9.1.8" | `α = (θ − 1)/2`; `integral_rpow_neg_le`, from `rpow_neg_le_quadratic`; the conclusion is from Theorem 8.4.2 (`theorem_8_4_2`, carried), not Theorem 9.1.8 |
| p. 226 | `[0, x]` and `[x, ∞)` are in `B⁺(X)` "with the assumption of positive mean" | The hypothesis `0 < ψ(c, ∞)` for every `c` of `theorem_9_5_5_ii` |
| p. 226 | The balance between `m(x)` and `v(x)`; positive drift with recurrence; weakening the bounded range assumption | Not formalised (remarks); the weakening is Theorem 9.5.6 |
| Theorem 9.5.6 (i), (9.68), p. 227 | If `sup_x E_x[\|W_x\|^{2+ε}] < ∞` and `m(x) ≤ v(x)/2x + O(x^{−1−δ})`, `Φ` is recurrent | `theorem_9_5_6_i` (Harris recurrent; `HasMomentBound`; `v(x) ≥ v₀ > 0` for large `x`; petite sets `[0, c]`; `K` of either sign); `V(x) = log log(x + e)`: `loglogCoeff`, `loglogCoeff_mul_bounds`, `loglog_step_le`, `integrable_loglog`, `integral_loglog_le` |
| Theorem 9.5.6 (ii), (9.69), p. 227 | If `sup_x E_x[\|W_x\|^{2+ε}] < ∞` and `m(x) ≥ θv(x)/2x` with `θ > 1`, `Φ` is transient | `theorem_9_5_6_ii` (`v(x) ≥ v₀ > 0` for large `x`; tails `(c, ∞)` in `B⁺(X)`); `V(x) = 1 − (1 + x)^{−α}`, `α = min((θ − 1)/2, ε/2)`: `rpow_neg_step_le`, `integral_rpow_neg_le_of_moment`, `transient_of_rpow_drift`; the moments and tails: `abs_le_one_add_rpow`, `integrable_incr`, `integrable_incr_sq`, `incrTail`, `measurableSet_incrTail`, `setIntegral_sq_tail_le`, `measure_tail_le` |
| p. 227 | The bounds on the spread of `Γ_x` may be artifacts; no drift proof of recurrence of the zero-mean walk is known | Not formalised (remark) |
| p. 227 | The chain on `ℤ₊` with `P(x, x + 1) = 1 − c/x`, `P(x, 0) = c/x` and `P(0, 1) = 1` | `cxKernel` (`0 ≤ c ≤ 1`), `cxLaw`, `isMarkovKernel_cxKernel`, `cx_lintegral_succ`, `cx_integral_succ` |
| p. 227 | `P_0(τ₀ > n) = ∏_{x=1}^{n} [1 − c/x]`, so the chain is recurrent | The product stops at `n − 1`: `cx_tail_zero` (`tailProb`, carried), `cx_tailProb`; the printed product fails: `cx_tail_book_counterexample`. Recurrence: `cx_recurrent` (`L(0, 0) = 1`, `U(0, 0) = ∞`, for `0 < c ≤ 1`), `cx_prod_tendsto_zero` |
| p. 227 | `m(x) = −c + 1 − c/x` and `v(x) = cx + 1 − c/x` | `cx_mean`, `cx_var` |
| p. 227 | `2xm(x) − v(x) = (2 − 3c)x² − (c + 1)x + c`, positive for `c < 2/3`, so Theorem 9.5.6 would make the chain transient | Corrected: `cx_identity` (`x(2xm(x) − v(x)) = (2 − 3c)x² − (2c + 1)x + c`); the printed identity fails with either left side: `cx_identity_book_counterexample`. (9.69) holds for `c < 2/3`: `cx_drift_condition` |
| p. 227 | `E_x[\|W_x\|^{2+ε}] = x^{2+ε}c/x + 1 − c/x > x^{1+ε}`, violating the moment bound | The exact value: `cx_moment`; the inequality fails: `cx_moment_book_counterexample`; the moment bound fails: `cx_moment_unbounded` |

## §9.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| p. 228 | Harris; Orey's proof of Theorem 9.1.3; Tuominen, Jain and Jamison; Spitzer; Khas'minskii; Meyn and Tweedie on Theorem 9.2.2; Rosenblatt, Tuominen and Tweedie; Lamperti; Mertens et al.; the term "coercive"; Beneš; Petruccelli et al. and Chan et al. on SETAR; Kersting | Not formalised (commentary) |
