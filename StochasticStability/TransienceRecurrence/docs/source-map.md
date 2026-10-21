# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 8, pp. 171–198. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.TransienceRecurrence`; names from Mathlib are marked as such.
Names marked "carried" are in the modules copied from the Chapter 1–6 projects (see the
[README](../README.md)). "`ψ`-irreducible" is `IsMaximalIrreducibility P ψ` throughout, and
`B⁺(X)` is the class of measurable sets of positive `ψ`-measure. Every place where the Lean
statement departs from the book is listed in [corrections](corrections.md).

## Chapter 8 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 171 | The occupation time `η_A = Σ_{n ≥ 1} 1{Φₙ ∈ A}` | `occTime` (carried); its truncation `η_A^N = Σ_{n=1}^N 1{Φₙ ∈ A}`: `occTimeN`, `occTimeN_le`, `measurable_occTimeN` |
| p. 171 | `A` is uniformly transient if `E_x[η_A] ≤ M < ∞` for `x ∈ A`, and recurrent if `E_x[η_A] = ∞` for `x ∈ A` | `IsUniformlyTransient` (`A` measurable, `U(x, A) ≤ M ≠ ∞` on `A`), `IsRecurrentSet`; `isUniformlyTransient_empty`, `IsUniformlyTransient.mono`, `IsUniformlyTransient.union` |
| Theorem 8.0.1, p. 172 | A `ψ`-irreducible chain is either recurrent (every set in `B⁺(X)` is recurrent) or transient (`X` has a countable cover by uniformly transient sets), and then every petite set is uniformly transient | `theorem_8_0_1`, from `theorem_8_3_4` and `theorem_8_3_5`; no countable generation |
| (8.1), p. 172 | The (possibly extended valued) drift `ΔV(x) = ∫ P(x, dy) V(y) − V(x)` of a non-negative measurable `V` | `drift` (`V : X → [0, ∞]`, values in `EReal`), `drift_nonpos_iff`, `drift_nonneg_iff`; the real drift of a bounded `V`: `driftR` |
| Theorem 8.0.2 (i), (8.2)–(8.3), p. 172 | `Φ` is transient iff there are a bounded `V ≥ 0` and `C ∈ B⁺(X)` with `ΔV ≥ 0` on `Cᶜ` and `D = {V > sup_C V} ∈ B⁺(X)` | `theorem_8_0_2_i`, from `isTransientChain_of_drift` |
| Theorem 8.0.2 (ii), (8.4), p. 172 | `Φ` is recurrent if there are a petite `C` and a `V` unbounded off petite sets with `ΔV ≤ 0` on `Cᶜ` | `theorem_8_0_2_ii` (`V : X → ℝ≥0` measurable; `IsPetite`, carried) |
| p. 173 | A converse to Theorem 8.0.2 (ii) holds for ψ-irreducible Feller chains (§9.4.2); whether it holds in general is unknown | Not formalised (forward reference) |
| p. 173 | `τ_A = inf{k ≥ 1 : Φₖ ∈ A}` and `L(x, A) = P_x(τ_A < ∞)`; for an atom `L(α, α) = 1` iff `α` is recurrent | `firstReturn`, `hitProb` (carried); `IsAtom.potKernel_eq_top_iff` |
| p. 173 | If `L(x, A) = 1` for `x ∈ A`, then `η_A = ∞` a.s. when `Φ₀ ∈ A`, and hence `A` is recurrent | The expectation form, `U(x, A) = ∞` on `A`: `proposition_8_3_1_ii`. The almost-sure form is Harris recurrence (Chapter 9) and is not formalised |
| pp. 171–173 | The overview of the chapter; Lyapunov, Khas'minskii and Foster | Not formalised (informal) |

## §8.1.1 The countable recurrence/transience dichotomy

| Source | Claim | Lean |
| --- | --- | --- |
| p. 173 | The state `α` is transient if `E_α[η_α] < ∞` and recurrent if `E_α[η_α] = ∞` | `IsTransientState`, `IsRecurrentState` (`U(α, {α}) ≠ ∞`, resp. `= ∞`) |
| (8.5), p. 173 | `E_x[η_y] = U(x, y)` | `potKernel_eq_lintegral_occTime` (carried, for every measurable set) |
| Proposition 8.1.1, (8.6), p. 173 | For an irreducible chain on a countable space, either `U(x, y) = ∞` for all `x, y` or `U(x, y) < ∞` for all `x, y` | `proposition_8_1_1` (`IsIrreducibleChain`, carried); (8.6) as `potKernel_singleton_ge`: `Pʳ(u, x) U(x, y) Pˢ(y, v) ≤ U(u, v)` |
| p. 174 | A chain is transient (recurrent) if every state is transient (recurrent) | Stated as the two alternatives of `theorem_8_1_2`. They agree with the general definitions of §8.2.3 for counting measure: `isRecurrentChain_count_iff`, `isTransientChain_count_iff` |
| Theorem 8.1.2, p. 174 | An irreducible chain is transient or recurrent | `theorem_8_1_2` |
| (8.7), p. 174 | The first-entrance decomposition `Pⁿ(x, α) = P_x(τ_α = n) + Σ_{j=1}^{n−1} P_x(τ_α = j) Pⁿ⁻ʲ(α, α)` | `firstEntrance_countable` (with `n + 1` for `n`) |
| (8.8)–(8.11), p. 174 | The generating functions `U^{(z)}(x, α)`, `L^{(z)}(x, α)` for `\|z\| < 1` and the identities `U^{(z)} = L^{(z)} + L^{(z)}U^{(z)}(α, α)`, `U^{(z)}(α, α) = L^{(z)}/(1 − L^{(z)})` | Not formalised (proof device). Proposition 8.1.3 is proved without them |
| Proposition 8.1.3, p. 174 | `U(x, x) = ∞` iff `L(x, x) = 1` | `proposition_8_1_3`, the case `α = {x}` of `IsAtom.potKernel_eq_top_iff`, which uses Proposition 8.3.1 (ii)–(iii) (`isAtom_singleton`, carried) |
| Proposition 8.1.4, p. 175 | For an irreducible chain, either `L(x, y) = 1` for all `x, y`, or `L(x, x) < 1` for all `x` | `proposition_8_1_4`; `one_sub_hitProb_ge_taboo` (`1 − L(x, A) ≥ ∫_E _APⁿ⁺¹(x, dz)(1 − L(z, A))` for `E ⊆ Aᶜ`), `potKernel_eq_zero_of_lastExit` |
| p. 175 | Recurrent countable chains are Harris recurrent | `hitProb_eq_one_of_recurrent` (`L(x, A) = 1` for every `x` and every non-empty `A`) |

## §8.1.2 Specific models: evaluating transience and recurrence

| Source | Claim | Lean |
| --- | --- | --- |
| p. 175 | For the forward recurrence time chain, `₁Pⁿ⁻¹(n, 1) = 1` for `n > 1`, so `L(1, 1) = 1` and the chain is recurrent when `p` is proper | `fwdRecKernel` (carried; the book's state `1` is `0`), `fwdRec_hitProb_zero` (`L(j, 0) = 1` for every `j`), `fwdRec_isRecurrentState_zero`; every state is recurrent when the chain is irreducible: `fwdRec_isRecurrentState` |
| p. 175 | The renewal sequence `u(n) = Σ_{k ≥ 0} P(Z_k = n)` of a renewal process with increment law `p` | `renewalPow` (`p^{∗k}`, with `p^{∗0} = δ₀`), `renewalSeq` |
| p. 175 | The renewal equation `u(n) = 1 + u ∗ p(n)` | False for `n ≥ 1`: `renewal_equation_counterexample` (`p = δ₁`). Corrected: `renewal_equation` (`u = δ₀ + u ∗ p`; `sampleConv`, `diracDist`, carried) |
| (8.12), p. 176 | `U(z) = [1 − P(z)]⁻¹` | `genFun`, `genFun_sampleConv`, `genFun_renewalSeq` (for every `z ∈ [0, ∞]`, in `[0, ∞]`) |
| p. 176 | A renewal process with proper `p` is recurrent: `U(1) = ∞` | `renewalSeq_genFun_one` |
| p. 176 | The renewal equation is (8.11) for the renewal chain of return times to `α` | Not formalised (remark) |
| p. 176 | The simple random walk on `ℤ₊`: `P(0, 0) = p`, `P(x, x − 1) = p`, `P(x, x + 1) = q`, `p + q = 1` | `srwInc p q` (`pδ₋₁ + qδ₁`) with `rwhlMatrix` (carried); `tsum_srwInc`, `srwInc_range`, `window_one`, `rwMean_srwInc` (mean `q − p`) |
| p. 176 | `L(0, 0) = p + qL(1, 0)` and `L(1, 0) = p + qL(2, 0)` | `srw_hitProb_zero_eq`, `srw_hitProb_one_eq` |
| p. 176 | Skip-free to the left: `L(2, 0) = L(2, 1) L(1, 0)` | `hitProb_passage` (any chain on `ℤ₊` that never jumps down by more than one, `L(x + 1, 0) = L(x + 1, x) L(x, 0)` for `x ≥ 1`), `srw_skipFree_down` |
| p. 176 | Translation invariance: `L(j, j − 1) = L(1, 0)` | `srw_hitProb_translate` |
| (8.13), p. 176 | `L(1, 0) = p + q[L(1, 0)]²`, so `L(1, 0) = 1` or `p/q` | `srw_quadratic`, `srw_hitProb_one_root` (`q ≠ 0`) |
| p. 176 | `L(1, 0) = 1` and `L(0, 0) = 1` if `p ≥ q` | `srw_hitProb_zero` |
| p. 176 | Random walk on `ℤ`; the laws of large numbers are outside the scope of the book | `randomWalkKernel Γ` (carried), `Γ` a probability on `ℤ`; `randomWalk_pow_eq_infinitePi` (`Pⁿ(0, A) = P(W₁ + ⋯ + Wₙ ∈ A)` under Mathlib's `Measure.infinitePi`; `law_orbit`, carried) |
| (8.14), p. 176 | The weak law of large numbers: `Pⁿ(0, A(εn)) → 1`, `A(k) = {\|y\| ≤ k}`, when `Γ` has mean zero | `randomWalk_wlln` (`Γ` with integrable identity and mean `0`): `Pⁿ(0, {\|y\| ≤ an}) ≥ ½` for large `n`, which is what the proof uses. Proved from Mathlib's strong law `ProbabilityTheory.strong_law_ae` and Mathlib's `MeasureTheory.tendstoInMeasure_of_tendsto_ae` |
| Theorem 8.1.5, p. 176 | An irreducible random walk on `ℤ` whose increments have mean zero is recurrent | `theorem_8_1_5` (integrable increments with mean `0`, no bound on the range; recurrent for counting measure) |
| (8.15), p. 177 | `Σ_{m=1}^N Pᵐ(x, 0) ≤ Σ_{j=0}^N Pʲ(0, 0)` | `sum_pow_le_sum_pow_zero` (any chain with measurable singletons) |
| p. 177 | Symmetry: `Σ_{m ≤ N} Pᵐ(x, 0) = Σ_{m ≤ N} Pᵐ(0, −x)` | `randomWalk_pow_translate` |
| (8.16)–(8.17), p. 177 | `Σ_{m ≤ N} Pᵐ(0, 0) ≥ [2aN + 1]⁻¹ Σ_{j ≤ N} Pʲ(0, A(aj))`, whose `lim inf` is `(2a)⁻¹`, for every `a > 0` | In the proof of `theorem_8_1_5`, in finite form: if `U(0, 0) < ∞`, then with `a = 1/(8(1 + U(0, 0)))`, `M = ⌈aN⌉` and `N` large, `(N − k₀)/2 ≤ Σ_{n ≤ N} Pⁿ(0, [−M, M]) ≤ (2M + 1)(1 + U(0, 0))`, a contradiction |

## §8.2.1 Transience and recurrence for individual sets

| Source | Claim | Lean |
| --- | --- | --- |
| p. 177 | `_APⁿ(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)`, with `_AP⁰(x, A) = 0` | `tabooProb` (carried); as a measure in `B`, `tabooKernel P hA (n − 1) x` (carried); `map_restrict_le_firstReturn`, `setLIntegral_le_firstReturn` |
| (8.18), p. 178 | The first-entrance decomposition `Pⁿ(x, B) = _APⁿ(x, B) + Σ_{j=1}^{n−1} ∫_A _APʲ(x, dw) Pⁿ⁻ʲ(w, B)` | `firstEntrance_decomposition` (with `n + 1` for `n`; an equality for all measurable `A`, `B`), from `pathKernel_inter_shift` (the Markov property at a fixed time) |
| (8.19), p. 178 | The last-exit decomposition `Pⁿ(x, B) = _APⁿ(x, B) + Σ_{j=1}^{n−1} ∫_A Pʲ(x, dw) _APⁿ⁻ʲ(w, B)` | `lastExit_decomposition` (with `n + 1` for `n`; an equality), by decomposing the path over its last visit to `A` |
| p. 178 | The last-exit time is not a stopping time | The proof of `lastExit_decomposition` uses the Markov property at the fixed times `j + 1` only |
| (8.20)–(8.21), p. 178 | The generating functions `U^{(z)}(x, B)` and `U_A^{(z)}(x, B)`, `\|z\| < 1` | Not formalised (proof device); `U_A = Σ_{n ≥ 1} _APⁿ` is `tabooPotKernel` (carried) |
| (8.22)–(8.23), p. 178 | `U(x, A) = Σ_{n ≥ 1} Pⁿ(x, A) = E_x[η_A]` | `potKernel_apply`, `potKernel_eq_lintegral_occTime` (carried); `lintegral_occTimeN`, `iSup_lintegral_occTimeN` (`sup_N E_x[η_A^N] = U(x, A)`), `sum_pow_le_potKernel` |
| (8.24), p. 178 | `L(x, A) = Σ_{n ≥ 1} _APⁿ(x, A)` | `hitProb_eq_tsum` (carried) |
| (8.25), p. 179 | `U^{(z)}(x, B) = U_A^{(z)}(x, B) + ∫_A U_A^{(z)}(x, dw) U^{(z)}(w, B)` | At `z = 1`: `potKernel_firstEntrance` (an equality in `[0, ∞]`). With `A = B`, from the strong Markov property at `τ_A`: `potKernel_eq_firstReturn` (`U(x, A) = E_x[1 + U(Φ_{τ_A}, A); τ_A < ∞]`), `lintegral_shiftAt_firstReturn` |
| (8.26), p. 179 | `U^{(z)}(x, B) = U_A^{(z)}(x, B) + ∫_A U^{(z)}(x, dw) U_A^{(z)}(w, B)` | At `z = 1`: `potKernel_lastExit` (an equality); the form used for Proposition 8.1.4 and Theorem 8.3.6: `potKernel_eq_zero_of_lastExit` |

## §8.2.2 The recurrence/transience dichotomy: chains with an atom

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 8.2.1 (i), (8.27), p. 179 | If `Φ` is `ψ`-irreducible with an atom `α ∈ B⁺(X)` and `α` is recurrent, every set in `B⁺(X)` is recurrent | `theorem_8_2_1_i` (`U(x, A) = ∞` for every `x` and `A ∈ B⁺(X)`; `IsAtom`, carried); `IsAtom.pow_succ_eq`, `IsAtom.potKernel_eq` |
| p. 179 | For an atom, transience is equivalent to `L(α, α) < 1`, as in Proposition 8.1.3 | `IsAtom.potKernel_eq_top_iff`; `IsAtom.isRecurrentSet_or_isUniformlyTransient` |
| Theorem 8.2.1 (ii), p. 179 | If `α` is transient, `X` has a countable cover by uniformly transient sets; by (8.26), `U(x, α) ≤ [1 − L(α, α)]⁻¹` | `theorem_8_2_1_ii`; the bound: `IsAtom.isUniformlyTransient` (`U(x, α) ≤ (1 − L(a, α))⁻¹` for every `x`, by Proposition 8.3.1 (iii)) |
| p. 179 | The cover `α(j) = {y : Σ_{n=1}^j Pⁿ(y, α) > j⁻¹}`, with `U(x, α) ≥ j⁻² U(x, α(j))` | The cover of Proposition 8.3.2, `Ā(m) = {Σ_{n=1}^m Pⁿ(·, A) ≥ m⁻¹}` (`hitSetLevel`, carried): `isTransientChain_of_uniformlyTransient`, `proposition_8_3_2_cover` |
| p. 180 | `A` is transient if it can be covered by countably many uniformly transient sets | `IsTransientSet`; `IsUniformlyTransient.isTransientSet`, `IsTransientSet.mono`, `isTransientSet_iUnion` |

## §8.2.3 The general recurrence/transience dichotomy

| Source | Claim | Lean |
| --- | --- | --- |
| p. 180 | `Φ` is recurrent if it is ψ-irreducible and `U(x, A) ≡ ∞` for every `x` and `A ∈ B⁺(X)`; transient if it is ψ-irreducible and `X` is transient | `IsRecurrentChain P ψ`, `IsTransientChain P ψ` (`ψ` maximal); `IsTransientChain.not_isRecurrentChain` (not both) |
| Proposition 8.2.2, p. 180 | If `Φ` is ψ-irreducible and strongly aperiodic, either `Φ` and `Φ̌` are both recurrent or both transient | `Minorization.proposition_8_2_2` (a minorization on `C ∈ B⁺(X)`, through the atom `α̌`), `proposition_8_2_2_stronglyAperiodic` (the book's statement, with the `ν₁`-small set in `B⁺(X)`), `Minorization.proposition_8_2_2_general` (every minorization); `Minorization`, `Minorization.splitKernel`, `Minorization.checkAlpha` (carried) |
| (8.28), p. 180 | `Σₙ ∫ δ_x*(dyᵢ) P̌ⁿ(yᵢ, B) = Σₙ Pⁿ(x, B)` | `Minorization.potKernel_split`; `Minorization.splitKernel_pow_checkAlpha`, `Minorization.potKernel_checkAlpha`, `Minorization.split_checkAlpha` (`ψ*(α̌) = δψ(C)`) |
| p. 181 | If `Φ̌` is recurrent, so is `Φ`; if `Φ̌` is transient, so is `Φ` | `Minorization.isRecurrentChain_of_split`, `Minorization.isUniformlyTransient_C` (a uniformly transient `α̌` makes `C` uniformly transient). The converse direction, for every minorization: `Minorization.isRecurrentChain_split_of_isRecurrentChain` |
| Lemma 8.2.3, p. 181 | `Σ_{n ≥ 1} K_{a_ε}ⁿ = ((1 − ε)/ε) Σ_{n ≥ 0} Pⁿ` for `0 < ε < 1` | `lemma_8_2_3` (`resolvent`, carried); `resolventPowCoeff`, `resolvent_pow_eq`, `tsum_resolventPowCoeff`, `tsum_choose_mul_pow`, `tsum_pow_eq` |
| p. 181 | Proof: generating functions `A_ε(z)`, `B(z) = Σₙ A_ε(z)ⁿ` and uniqueness of power series | Replaced by a direct computation of the coefficients: `K_{a_ε}ⁿ⁺¹ = Σ_k (1 − ε)ⁿ⁺¹ εᵏ C(n + k, k) Pᵏ` and `Σₙ C(n + k, k) rⁿ = (1 − r)^{−(k+1)}` in `[0, ∞]` |
| Proposition 8.2.4, p. 181 | `Φ` is transient (recurrent) iff each `K_{a_ε}`-chain is | `proposition_8_2_4` (each `0 < ε < 1`); `isMaximalIrreducibility_resolvent`, `exists_pow_pos_of_resolvent_pow_pos` |
| Theorem 8.2.5, p. 181 | A ψ-irreducible chain is recurrent or transient: the `K_{a_ε}`-chain is strongly aperiodic, Proposition 8.2.2 classifies it, and Proposition 8.2.4 passes the classification to `Φ` | `theorem_8_2_5` (countably generated `X`), through `theorem_5_2_3_resolvent` (carried), `Minorization.proposition_8_2_2` and `proposition_8_2_4`; it does not use Theorem 8.3.4 |
| Theorem 8.2.6, p. 182 | For a ψ-irreducible aperiodic chain, `Φ` is transient (recurrent) iff one, and then every, `m`-skeleton is | `theorem_8_2_6_i`, `theorem_8_2_6_ii` (countably generated `X`; `IsAperiodic`, carried). The skeletons are ψ-irreducible by `proposition_5_4_5_iii` (carried); in (ii) a skeleton is classified by Theorem 8.3.4, where the book uses Theorem 8.2.5 |
| (8.29), p. 182 | `Σ_{j ≥ 1} Pʲ(x, A) = Σ_{r=1}^m ∫ Pʳ(x, dy) Σ_j P^{jm}(y, A) ≤ mM` if `U_m(·, A) ≤ M` on `A` | The bound is `m(2 + M)`. `potKernel_le_skeleton` (`U(x, A) ≤ m(1 + M)` when `U_m(y, A) ≤ M` for every `y`), `potKernel_skeleton_le` (`U_m ≤ U`), `isTransientSet_of_skeleton`, `isTransientSet_skeleton` |
| (8.30), p. 182 | A recurrent skeleton makes `Φ` recurrent | In the proof of `theorem_8_2_6_ii`, from `potKernel_skeleton_le` |
| p. 182 | A strengthening to Harris recurrence needs the techniques of Chapter 9 | Not formalised (forward reference) |

## §8.3.1 Transience of sets

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 8.3.1 (i), (8.32), p. 183 | If `U(x, A) ≤ M` for `x ∈ A`, then `U(x, A) ≤ 1 + M` for every `x` | `proposition_8_3_1_i`; the sharper `U(x, A) ≤ L(x, A)(1 + M)`: `potKernel_le_hitProb_mul`; `IsUniformlyTransient.exists_bound` |
| Proposition 8.3.1 (ii), p. 183 | If `L(x, A) = 1` for `x ∈ A`, `A` is recurrent; if `Φ` is ψ-irreducible, `A ∈ B⁺(X)` and `U(x, A) ≡ ∞` | `proposition_8_3_1_ii`. The second part needs `A ≠ ∅`: `proposition_8_3_1_ii_counterexample`; corrected: `proposition_8_3_1_ii_irreducible` (`proposition_4_2_3_i`, carried); `potKernel_eq_top_of_hitProb_pos` |
| Proposition 8.3.1 (iii), p. 183 | If `L(x, A) ≤ ε < 1` for `x ∈ A`, then `U(x, A) ≤ 1/[1 − ε]` for every `x` | `proposition_8_3_1_iii`, through the truncated sums: `lintegral_occTimeN_le_hitProb`, `le_div_of_le_add_mul` |
| Proposition 8.3.1 (iv), (8.31), (8.35), p. 183 | If `P_x(τ_A(m) < ∞) ≤ ε < 1` for `x ∈ A`, then `U(x, A) ≤ m/[1 − ε]` on `A` and `U(x, A) ≤ 1 + m/[1 − ε]` everywhere | `proposition_8_3_1_iv` (`returnTimeK`, carried) |
| (8.33)–(8.34), p. 184 | `P_x(η_A ≥ m(k + 1)) ≤ εᵏ⁺¹` by induction | Replaced by the pathwise bound `η_A^N ≤ k + η_A^N ∘ θ^{τ_A(k)}` (`occTimeN_le_returnTimeK`) and the strong Markov property at `τ_A(k)` (`lintegral_shiftAt_returnTimeK`, `lintegral_occTimeN_le_returnTimeK`); `returnTimeK_succ_eq_add`, `returnTimeK_succ_eq_top`, `le_returnTimeK`, `returnTimeK_mem`, `stoppedState_returnTimeK_mem`, `hittingAfter_succ_eq_top_iff`, `hittingAfter_succ_of_firstReturn_shift` |
| Proposition 8.3.2, p. 184 | If `A` is uniformly transient and `B ⇝ᵃ A`, `B` is uniformly transient; hence a uniformly transient `A` has a countable covering by uniformly transient sets | `proposition_8_3_2` (`SampledAccessible`, `lemma_5_5_2_iii`, carried). The second sentence is trivial as printed (`A` covers itself); what the proof gives is the covering of `Ā = {L(·, A) > 0}` by the sets `Ā(m)`: `proposition_8_3_2_cover`, `sampledAccessible_hitSetLevel` (`hitSet`, `hitSetLevel`, carried) |
| p. 184 | (Consequence used later) a `φ`-irreducible chain with a uniformly transient set of positive `φ`-measure is transient | `isTransientSet_univ_of_uniformlyTransient`, `isTransientChain_of_uniformlyTransient`, `IsTransientChain.exists_uniformlyTransient` |
| Proposition 8.3.3, p. 184 | If `Dᶜ` is absorbing and `L(x, Dᶜ) > 0` for `x ∈ D`, then `D` is transient, covered by `B(m) = {y ∈ D : Pᵐ(y, Dᶜ) ≥ m⁻¹}` | `proposition_8_3_3` (`IsAbsorbing`, carried; the sets are indexed from `m + 1`); `pathKernel_coord_inter_shift`, `IsAbsorbing.pow_mono` |

## §8.3.2 Identifying transient sets for ψ-irreducible chains

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 8.3.4, p. 185 | A ψ-irreducible chain is recurrent or transient, proved without the atom | `theorem_8_3_4` (no countable generation); `isRecurrentChain_or_isTransientChain` (exactly one holds) |
| (8.36), p. 185 | `U(x*, A) ≥ ∫ Pᵐ(x*, dw) U(w, A)`, so `A* = {U(·, A) = ∞}` is ψ-null | `lintegral_pow_potKernel_le`, `potKernel_eq_top_of_pow_pos`; in the proof of `theorem_8_3_4` |
| (8.37), p. 185 | Some `A_r = {y ∈ A : U(y, A) ≤ r}` lies in `B⁺(X)`, and `U(y, A_r) ≤ 1 + r` | In the proof of `theorem_8_3_4`, with `proposition_8_3_1_i` |
| (8.38), p. 185 | The sets `A_r(M) = {Σ_{m=0}^M Pᵐ(·, A_r) > M⁻¹}` are uniformly transient and cover `X` | The cover used is `Ā_r(m)` of Proposition 8.3.2: `isTransientSet_univ_of_uniformlyTransient` |
| Theorem 8.3.5, p. 186 | If `Φ` is ψ-irreducible and transient, every petite set is uniformly transient | `theorem_8_3_5` (no irreducibility: `X` transient suffices) |
| Theorem 8.3.6 (i), p. 186 | `Φ` is recurrent if some petite `C` has `L(x, C) ≡ 1` on `C`; `C ∈ B⁺(X)` follows | False for `C = ∅`: `theorem_8_3_6_i_counterexample`. Corrected: `theorem_8_3_6_i` (`C` non-empty); `hitProb_mono` |
| Theorem 8.3.6 (ii), p. 186 | `Φ` is transient iff there are `C, D ∈ B⁺(X)` with `L(x, C) < 1` for `x ∈ D` | `theorem_8_3_6_ii`; `hitProb_inter_absorbing`, `firstReturn_eq_top_iff`, `measurableSet_natFilt_le_firstReturn`, `potKernel_eq_zero_of_lastExit` |
| p. 186 | Converse: for a petite `C ∈ B⁺(X)`, `D = {y ∈ Cᶜ : L(y, C) < 1}` lies in `B⁺(X)` | `IsTransientChain.exists_compl_hitProb_lt_one`, with a uniformly transient `C ∈ B⁺(X)` (`IsTransientChain.exists_uniformlyTransient`) in place of a petite one; `theorem_8_3_6_ii` itself takes `D = {L(·, C) < 1}` |
| Proposition 8.3.7, p. 186 | Every ψ-null set is transient | `proposition_8_3_7`, from `proposition_4_2_3_ii` (carried) and `proposition_8_3_3` |
| Proposition 8.3.8, p. 187 | There are `D₁, …, D_d` with `P(x, Dᵢ₊₁) = 1` on `Dᵢ` and `N = (⋃ Dᵢ)ᶜ` ψ-null and transient | `proposition_8_3_8` (countably generated `X`; the cycle `IsCycle`, indexed by Mathlib's `ZMod d`, and `exists_isPeriod`, carried) |
| p. 187 | The exceptional sets need not be empty | Not formalised (remark) |

## §8.4.1 A drift criterion for transience

| Source | Claim | Lean |
| --- | --- | --- |
| p. 187 | `σ_C = 0` on `C` and `σ_C = τ_C` on `Cᶜ` | `firstHit` (carried); `hitProbZero P C x = P_x(σ_C < ∞)`, `hitProbZero_of_mem`, `hitProbZero_of_notMem`, `hitProbZero_le_one`, `measurable_hitProbZero` |
| Proposition 8.4.1, (8.39)–(8.40), p. 187 | `h*(x) = P_x(σ_C < ∞)` is the pointwise minimal non-negative solution of `∫ P(x, dy) h(y) ≤ h(x)` on `Cᶜ`, `h ≥ 1` on `C`, and satisfies (8.39) with equality | `proposition_8_4_1` (`h : X → [0, ∞]`) |
| p. 188 | `ΔV` is well defined if `V` is bounded; `C_V(r) = {V ≤ r}` | `driftR`; the sublevel sets are written `{x \| V x ≤ r}` |
| Theorem 8.4.2, (8.41), p. 188 | `Φ` is transient iff there are a bounded `V : X → ℝ₊` and `r ≥ 0` with `C_V(r)`, `C_V(r)ᶜ ∈ B⁺(X)` and `ΔV > 0` on `C_V(r)ᶜ` | `theorem_8_4_2`, with `ΔV ≥ 0` on `C_V(r)ᶜ` |
| p. 188 | Proof: `h_V = [M − V]/[M − r]` on `D`, `1` on `C`, solves (8.39), so `L(x, C) < 1` on `D` and Theorem 8.3.6 applies | `isTransientChain_of_drift` (for any `C ∈ B⁺(X)` with `V ≤ r` on `C` and `{V > r} ∈ B⁺(X)`) |
| p. 189 | Converse: `V(x) = 1 − P_x(σ_C < ∞)` for a petite `C ∈ B⁺(X)` with `{y ∈ Cᶜ : L(y, C) < ε} ∈ B⁺(X)` | `drift_one_sub_hitProbZero` (`ΔV = 0` off `C`), with the set of `IsTransientChain.exists_compl_hitProb_lt_one` |

## §8.4.2 A drift criterion for recurrence

| Source | Claim | Lean |
| --- | --- | --- |
| (V1), (8.42), p. 189 | A positive `V` and a set `C` with `ΔV ≤ 0` on `Cᶜ` | The hypothesis `∀ x ∉ C, drift P V x ≤ 0` with `V : X → ℝ≥0` |
| p. 189 | `V : X → ℝ₊` is unbounded off petite sets if every `C_V(n)` is petite | The hypothesis `∀ n : ℕ, IsPetite P {x \| V x ≤ n}` |
| (8.43), p. 189 | For an irreducible chain it suffices that each `C_V(n)` lies in a finite union of petite sets `Cⱼ` | `unboundedOffPetite_of_cover` (countably generated `X`; `proposition_5_5_5_ii`, carried); `isPetite_of_subset` |
| Theorem 8.4.3, p. 190 | If `Φ` is ψ-irreducible, `C` is petite and `V` is unbounded off petite sets with (V1), then `L(x, C) ≡ 1` and `Φ` is recurrent | `theorem_8_4_3`: recurrence as stated, and `L(x, C) ≡ 1` when `C ∈ B⁺(X)`. `L ≡ 1` fails for `C = ∅`: `theorem_8_4_3_counterexample`. For `C ∈ B⁺(X)`, without petiteness of `C`: `lemma_8_4_3_hitProb` |
| (8.44)–(8.50), p. 190 | Proof by contradiction from transience, through the kernel `P̃` that is absorbed in `C` | Replaced by a direct argument with the killed kernel `P I_{Cᶜ}`: `killedKernel`, `lintegral_killedKernel_pow_le` (the analogue of (8.45) and (8.48)), `killedKernel_pow_succ_apply_self`, `killedKernel_pow_univ`, `sum_tabooKernel_add_killed` (the analogue of (8.46)), `lintegral_killedKernel_hitProb`, `IsPetite.hitProb_ge` |

## §8.4.3 Random walks with bounded range

| Source | Claim | Lean |
| --- | --- | --- |
| p. 191 | On a countable space finite sets are petite | `isPetite_of_finite` (a finite set whose points all lead to one state) |
| p. 191 | Random walk on `ℤ` with `Γ(x) = 0` for `\|x\| > r`; the mean drift `β = Σ_w Γ(w) w` | `rwMatrix` with `matKernel` (carried); `window`, `rwMean`, `eq_zero_of_notMem_window`, `tsum_eq_sum_window`, `ne_top_of_tsum_eq_one`, `sum_window_toReal`, `sum_window_affine`, `sum_window_ofReal`, `lintegral_rw`, `lintegral_rw_window`, `integral_eq_sum_of_lintegral` |
| Proposition 8.4.4, p. 191 | An irreducible random walk on `ℤ` with bounded range and mean zero is recurrent (`V(x) = \|x\|`, `C = {−r, …, r}`) | `proposition_8_4_4` (recurrent for counting measure); `sum_window_abs` |
| Proposition 8.4.5, (8.51)–(8.53), p. 191 | With non-zero mean it is transient: `V(x) = 1 − ρˣ` for `x ≥ 0`, `0` elsewhere, with `Σ_w Γ(w) ρʷ = 1`, `ρ < 1` | `proposition_8_4_5` (transient for counting measure), with `V(x) = (1 − sˣ)⁺` and `s ≠ 1` for either sign of the mean, through `theorem_8_4_2` |
| p. 192 | `β(s) = Σ_w Γ(w)sʷ → ∞` as `s → 0`, `β(1) = 1` and `β′(1) = β > 0`, so a root `ρ < 1` exists; irreducibility gives `Γ(w) > 0` for some `w < 0` | `exists_root_of_mean_pos`, `exists_root_of_mean_ne_zero` (a negative mean by reflection `s ↦ s⁻¹`), `rw_charges_both_sides`. The book cites "Proposition 8.4.2" for the transience step; Theorem 8.4.2 is meant |
| Proposition 8.4.6, p. 192 | The bounded-range walk on `ℤ₊` is recurrent iff `β ≤ 0` | Needs `Γ(−∞, 0) > 0`: `proposition_8_4_6_counterexample` (`Γ = δ₀`; `diracInc`, `tsum_diracInc`). Corrected: `proposition_8_4_6` (for every maximal `ψ`; `rwhlMatrix`, carried); `rwhl_exists_maximal`, `rwhl_isPhiIrreducible_dirac`, `rwhl_pos_zero`, `rwhl_pow_up`, `lintegral_rwhl`, `lintegral_rwhl_window`, `rwhlMatrix_eq_tsum` |
| p. 192 | Proof, `β > 0`: stochastic comparison with the unrestricted walk; `β ≤ 0`: `V(x) = x` | Transience by the drift argument on `ℤ₊` with `V(x) = 1 − ρˣ` (`isTransientChain_of_drift`); recurrence by `theorem_8_4_3` |
| p. 192 | Stochastic comparison (§9.5.1); Theorem 8.1.5 appears difficult to prove by drift methods | Not formalised (remarks) |

## §8.5.1 Recurrence when β is negative

| Source | Claim | Lean |
| --- | --- | --- |
| p. 193 | The walk on `ℝ₊`, `Φₙ = [Φₙ₋₁ + Wₙ]⁺`, with increment law `Γ` of finite mean `β` | `halfLineWalkKernel Γ` (carried) on `ℝ≥0`; `lintegral_halfLine`, `integral_halfLine` |
| p. 193 | The application to queueing and storage models | Not formalised (remark) |
| Proposition 8.5.1, p. 193 | If `β < 0` the walk is recurrent | `proposition_8_5_1` (integrable increments; for every maximal `ψ`, which exists by `halfLine_neg_pos_of_mean_neg` and `halfLine_maximal`, carried) |
| (8.54)–(8.55), p. 193 | `∫ P(x, dy)V(y) ≤ V(x) − ε` off `C = [0, x₀]`, with `V(x) = x` | `halfLine_drift_neg` |
| p. 193 | The chain is `δ₀`-irreducible and compact sets are small | `proposition_4_3_1` (carried); `halfLine_isSmallSet_Iic` (carried), `halfLine_isPetite_Iic` (`Γ(−∞, 0) > 0`) |

## §8.5.2 Recurrence when β is zero

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 8.5.2, p. 194 | For `s > 0` and `A ⊆ {s + tw > 0}`, `E[log(s + tW); A] ≤ Γ(A) log s + (t/s)E[W; A] − (t²/2s²)E[W²; A ∩ {tW < 0}]` | `lemma_8_5_2` (`W` and `W²` integrable; `log(s + tW)` integrable on `A`) |
| p. 194 | `log(1 + x) ≤ x − (x²/2)1{x < 0}` for `x > −1` | `log_one_add_le` |
| Lemma 8.5.3, (8.56)–(8.57), p. 194 | For finite variance, `−xE[W; W < t − sx] → 0` and `xE[W; W > t + sx] → 0`; if `E[W] = 0`, also `−xE[W; W > t − sx] → 0` and `xE[W; W < t + sx] → 0` | `lemma_8_5_3_i`, `lemma_8_5_3_ii` (`W`, `W²` integrable); `tendsto_setIntegral_zero`, `tendsto_mul_setIntegral_abs_zero` |
| Proposition 8.5.4, p. 195 | If `β = 0` and `0 < E[W²] < ∞`, the walk is recurrent | `proposition_8_5_4` (for every maximal `ψ`, which exists by `halfLine_neg_pos_of_mean_zero` and `halfLine_maximal`, carried); `integrable_of_integrable_sq` |
| (8.58)–(8.61), p. 195 | `V(x) = log(1 + x)` for `x > R`, `0` on `[0, R]`; `U₁(x)` and `U₂(x)`, with `U₁ = o(x⁻²)` | `V(x) = log(1 + x)` on all of `ℝ₊`, `C = [0, x₁]`; the estimate is `E[W; W > −x] ≤ E[W²; W ≤ −x]/x`, in the proof of `proposition_8_5_4`; `isPetite_of_subset` |

## §8.5.3 Transience of skip-free random walk when β is positive

| Source | Claim | Lean |
| --- | --- | --- |
| p. 195 | For `β > 0` and unbounded range, transience follows from the strong law (Proposition 9.1.2) | Not formalised (forward reference) |
| Proposition 8.5.5, p. 195 | The walk on `ℤ₊` skip-free to the right (`Γ(x) = 0` for `x > 1`) with `β > 0` is transient | `proposition_8_5_5` (`Σₙ n aₙ < 1`, `aⱼ = Γ(1 − j)`), `proposition_8_5_5_mean` (`β = Σ_w wΓ(w) > 0`, with `w ↦ wΓ(w)` summable), both with `Γ(−∞, 0) > 0` and for every maximal `ψ`; `skipFree_mean_lt_one`, `skipFree_one_pos` |
| p. 196 | Without loss of generality `Γ(−∞, 0) > 0`: otherwise the chain is not irreducible and "transient in every meaning of the word" | Not irreducible: `rwhl_not_irreducible_of_nonneg`. Hence neither transient nor recurrent in the sense of §8.2.3: `rwhl_not_transient_of_nonneg`. The hypothesis is kept |
| (8.62), p. 196 | A bounded non-constant solution of `Σ_y P(x, y)V(y) = V(x)`, `x ≥ 1` | `skipFreeV`, `lintegral_skipFreeV`, `skipFreeV_le`, `one_le_skipFreeV` (`V(0) = 0`, `V ≥ 1` on `x ≥ 1`) |
| (8.63), p. 196 | `V(x) = Γ(−x + 1)V(1) + ⋯ + Γ(1)V(1 + x)` | `skipFree_harmonic`, by comparing coefficients of formal power series over `[0, ∞]` (Mathlib's `PowerSeries`) |
| (8.64)–(8.67), p. 196 | The generating functions `V*(z)`, `Γ*(z)`, the expansion (8.65) and `V(x) = Γ(1)V(1) Σ_{m<x} bₘ` | Replaced: `bₘ` is the renewal sequence of `cⱼ = Σ_{n>j} aₙ` (`renewalSeq`, `skipFreeTail`, `skipFreeTail_add`, `skipFree_tsum_a`, `skipFree_tsum_reindex`), and `V(x) = Σ_{m<x} bₘ` is normalised by `Γ(1)V(1) = 1` |
| (8.68)–(8.69), p. 197 | `B(z) = 1 − Σ_j zʲ Σ_{n>j} aₙ`, and `Σ bⱼ = [1 − Σ n aₙ]⁻¹ = β⁻¹ < ∞` by Abel's theorem | `tsum_renewalSeq_skipFree` (`Σₘ bₘ = (1 − Σₙ n aₙ)⁻¹`), from `genFun_renewalSeq` at `z = 1`, where every term is non-negative; `tsum_skipFreeTail` (`Σⱼ cⱼ = Σₙ n aₙ`). No Abel theorem is used |

## §8.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 197–198 | Sources of the chapter; inessential sets; Orey, Nummelin, Tuominen; skeletons; Foster's drift conditions; Chung and Ornstein; Guo and Petrucelli; stronger recurrence for negative mean (Chapter 11); the drift operator as a generator | Not formalised (commentary) |
