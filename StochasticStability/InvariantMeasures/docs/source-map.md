# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 10, pp. 229–255. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.InvariantMeasures`; names from Mathlib are marked as such. Names
marked "carried" are in the modules copied from the Chapter 1–6, 8 and 9 projects (see the
[README](../README.md)). "`ψ`-irreducible" is `IsMaximalIrreducibility P ψ` unless stated
otherwise, and `B⁺(X)` is the class of measurable sets of positive `ψ`-measure. `μP` is
`P ∘ₘ μ`. Every place where the Lean statement departs from the book is listed in
[corrections](corrections.md).

## Chapter 10 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 229 | The omission of transient potential theory; the motivation for invariant measures | Not formalised (informal) |
| (10.1), p. 229 | A σ-finite `π` with `π(A) = ∫ π(dx) P(x, A)` is invariant | `IsInvariant` (`μP = μ`, no σ-finiteness), `IsInvariantMeasure` (adds `SigmaFinite`); set-wise: `isInvariant_iff` |
| Theorem 10.0.1, (10.2), p. 230 | A recurrent chain has an invariant measure `π`, unique up to constant multiples, with `π(B) = ∫_A π(dw) E_w[Σ_{n=1}^{τ_A} 1{Φₙ ∈ B}]` for `A ∈ B⁺(X)` | `theorem_10_0_1` (countably generated `X`; nonzero `π`, unique among subinvariant measures up to a finite constant; (10.2) for `A ∈ B⁺(X)` with `π(A) < ∞`) |
| Theorem 10.0.1, p. 230 | `π` is finite if `sup_{x ∈ C} E_x[τ_C] < ∞` for a petite `C` | Needs `C ≠ ∅`: `theorem_10_0_1_counterexample` (`heavyRenewal`). Corrected: `theorem_10_0_1_finite` (non-empty petite `C`) |
| p. 230 | Proof: Theorems 10.2.1, 10.4.9 and 10.4.10 | `theorem_10_4_4`, `theorem_10_4_9_path` and `theorem_10_4_10_ii`, in the proofs of `theorem_10_0_1` and `theorem_10_0_1_finite` |
| p. 230 | A finite invariant measure normalises to a stationary probability; infinite mass is harder to interpret | Not formalised (remark); the normalisation is in the proof of `isPositive_iff_invMeasure_univ` |
| p. 230 | `Φ` is positive if it is ψ-irreducible with an invariant probability, and null otherwise | `IsPositive`, `IsNull` (both include that `ψ` is maximal); `isPositive_or_isNull`, `IsPositive.not_isNull` |

## §10.1.1 Invariant measures

| Source | Claim | Lean |
| --- | --- | --- |
| p. 230 | Stationary processes; a chain started at a point is not stationary | Not formalised (informal) |
| (10.3), p. 231 | Iterating, `π(A) = ∫ π(dx) Pⁿ(x, A) = P_π(Φₙ ∈ A)` | `IsInvariant.pow` (`μPⁿ = μ`), `IsInvariant.map_coord` (under `P_π` every `Φₙ` has law `π`; `pathMeasure`, carried) |
| p. 231 | `Φ` is stationary iff the law of `Φₙ` does not vary with time | `IsInvariant.map_shift` (the shifted chain `θⁿΦ` has law `P_π`; `shift`, carried), `isInvariant_iff_map_shift` (stationarity under `P_π` iff `π` invariant) |
| Proposition 10.1.1, p. 231 | A positive chain is recurrent | `proposition_10_1_1` |
| p. 231 | Proof: a cover by uniformly transient sets `Aⱼ` with `U(x, Aⱼ) ≤ Mⱼ` (Theorem 8.3.4) and `kπ(Aⱼ) ≤ Mⱼ` | `theorem_8_3_4` (carried), `IsInvariant.measure_eq_zero_of_uniformlyTransient` (`IsUniformlyTransient`, carried), `lintegral_potKernel`, `lintegral_potKernel_of_isInvariant` (`∫ π(dx) U(x, A) = Σ_{n ≥ 1} π(A)`) |
| p. 231 | Positive Harris chains: Harris recurrent and positive | `IsPositiveHarris` (`IsHarris`, carried), `IsPositiveHarris.isPositive` |
| (10.4), p. 232 | If `μPⁿ(A) → γ_μ(A)` for every `A`, then `γ_μ` is invariant, since setwise convergence gives convergence of integrals of bounded measurable functions | `isInvariant_of_tendsto` (`μ` a probability), `tendsto_lintegral_of_setwise` (measurable `0 ≤ f ≤ 1`, through Mathlib's layer-cake formula and dominated convergence) |
| p. 232 | With a unique invariant probability, the limit does not depend on `μ` | Not stated separately; it follows from `isInvariant_of_tendsto` and `eq_stationaryDist` |
| p. 232 | The linear model as an example of this route | §10.5.4 below |

## §10.1.2 Subinvariant measures

| Source | Claim | Lean |
| --- | --- | --- |
| (10.5), p. 232 | A σ-finite `μ` with `μ(A) ≥ ∫ μ(dx) P(x, A)` is subinvariant | `IsSubinvariant` (`μP ≤ μ`), `IsSubinvariantMeasure` (adds `SigmaFinite`); `isSubinvariant_iff`; `IsInvariant.isSubinvariant`, `IsInvariantMeasure.isSubinvariantMeasure`, `IsInvariant.smul`, `IsSubinvariant.smul`, `IsInvariant.add` |
| (10.6), pp. 232–233 | `μ(B) ≥ ∫ μ(dw) Pⁿ(w, B)`, hence `μ(B) ≥ ∫ μ(dw) K_a(w, B)` for a sampling distribution `a` | `IsSubinvariant.pow`, `sampledKernel_comp_apply` (`μK_a(A) = Σₙ a(n) μPⁿ(A)`; `sampledKernel`, carried), `IsSubinvariant.sampledKernel` (every `a` with `Σ a ≤ 1`), `IsSubinvariant.resolvent`; for invariant measures `IsInvariant.sampledKernel`, `IsInvariant.resolvent` |
| Proposition 10.1.2 (i), p. 233 | For a ψ-irreducible chain and `μ` with (10.5) and `μ(A) < ∞` for one `A ∈ B⁺(X)`, `μ` is σ-finite, hence subinvariant | `proposition_10_1_2_i`, `proposition_10_1_2_i'` (`ψ` any irreducibility measure, `IsPhiIrreducible`, carried) |
| p. 233 | Proof: `A*(j) = {K_{a_{1/2}}(y, A) > j⁻¹}` cover `X` and `μ(A*(j)) ≤ jμ(A)` | `resolventLevel` (with `(j + 1)⁻¹`), `measurableSet_resolventLevel`, `iUnion_resolventLevel`, `measure_resolventLevel_le` (`resolventHalf`, carried) |
| Proposition 10.1.2 (ii), p. 233 | `μ ≻ ψ` | Needs `μ ≠ 0`: `proposition_10_1_2_ii_counterexample`. Corrected: `proposition_10_1_2_ii` (`ψ ≪ μ` for every nonzero `μ` with `μP ≤ μ`; the finiteness hypothesis is not needed); `IsSubinvariant.pos_of_pos` (a nonzero subinvariant `μ` charges every set of `B⁺(X)`) |
| Proposition 10.1.2 (iii), (10.7), p. 233 | Petite sets have finite `μ`-measure: `μ(B) ≥ μ(C) ν_a(B)` | `proposition_10_1_2_iii` (`IsPetite`, `smul_le_comp_of_le_on`, carried); for subinvariant measures `IsSubinvariantMeasure.measure_lt_top_of_petite`, `IsSubinvariantMeasure.exists_finite_pos`, `exists_finite_pos_of_sigmaFinite`, and for atoms `IsSubinvariantMeasure.measure_atom_lt_top` |
| Proposition 10.1.2 (iv), (10.8), p. 233 | If `μ(X) < ∞`, `μ` is invariant | `proposition_10_1_2_iv` (no irreducibility), `comp_apply_univ` (`μP(X) = μ(X)`), `IsSubinvariant.isInvariantMeasure_of_finite` |
| Proposition 10.1.3, p. 233 | A transient chain has a strictly subinvariant measure | `proposition_10_1_3` (`U(x, ·)` is σ-finite, subinvariant and not invariant, for every `x`; `IsTransientChain`, `potKernel`, carried) |
| (10.9), p. 234 | `U(x, A) = P(x, A) + ∫ U(x, dy) P(y, A)` | `potKernel_comp_add`, `isSubinvariant_potKernel` |
| p. 234 | Recurrent chains are where subinvariant measures are less obvious | Not formalised (remark) |

## §10.2 The existence of π: chains with atoms

| Source | Claim | Lean |
| --- | --- | --- |
| p. 234 | One atom suffices; countable spaces as a special case; the split chain for general spaces | Not formalised (informal); the countable case is `proposition_10_2_3`, the split chain is §10.4.1 |
| Theorem 10.2.1 (i), (10.10), p. 234 | For a ψ-irreducible chain with an accessible atom `α`, `μ°_α(A) = U_α(α, A) = Σ_{n ≥ 1} _αPⁿ(α, A)` is subinvariant, and invariant iff `Φ` is recurrent | `atomMeasure` (for a point `a ∈ α`; `tabooPotKernel`, carried), `theorem_10_2_1_i` (`IsAccessibleAtom`, carried; σ-finite); `IsAtom.tabooKernel_eq`, `IsAtom.tabooPotKernel_eq` (independence of the point), `atomMeasure_eq_comp` |
| (10.11), p. 235 | `∫ μ°_α(dy) P(y, A) = μ°_α(α) P(α, A) + ∫_{αᶜ} Σₙ _αPⁿ(α, dy) P(y, A) ≤ μ°_α(A)`, with equality iff `L(α, α) = 1`, i.e. iff `Φ` is recurrent (Proposition 8.3.1) | `atomTail`, `atomMeasure_eq` (`μ°_α = P(a, ·) + S`), `comp_atomMeasure` (`μ°_αP = L(a, α) P(a, ·) + S`), `comp_restrict_atom`, `tabooKernel_succ_eq'`, `atomMeasure_self` (`μ°_α(α) = L(a, α)`), `isSubinvariant_atomMeasure`, `isInvariant_atomMeasure`; `IsAccessibleAtom.isRecurrentChain_iff` (recurrent iff `L(a, α) = 1`, through `theorem_8_2_1_i`, carried) |
| Theorem 10.2.1 (ii), p. 234 | `μ ≥ μ°_α` for every subinvariant `μ` with `μ(α) = 1`; for recurrent `Φ`, `μ°_α` is the unique such measure | `theorem_10_2_1_ii` (any atom, no irreducibility), `theorem_10_2_1_ii_unique` (no σ-finiteness of `μ`); up to scaling `theorem_10_2_1_ii_smul` (`0 < μ(α) < ∞`), `IsSubinvariantMeasure.eq_smul_atomMeasure` (every subinvariant measure) |
| p. 235 | Proof of uniqueness: a set `A` with `μ(A) > μ°_α(A)` and `Pⁿ(w, α) > 0` on `A` | `eq_of_le_of_lintegral_le` with `f = K_{a_{1/2}}(·, α)`, in the proof of `theorem_10_2_1_ii_unique` |
| Theorem 10.2.1 (iii), (10.12), pp. 234–235 | `μ°_α` is finite iff `E_α[τ_α] < ∞`, and then invariant; `μ°_α(X) = Σ_{n ≥ 1} P_α(τ_α ≥ n)` | `theorem_10_2_1_iii` (any atom), `atomMeasure_univ`, `meanReturnTime` (`E_x[τ_A]` in `[0, ∞]`), `meanReturnTime_eq_tabooPotKernel` (`E_x[τ_A] = Σ_{n ≥ 1} P_x(τ_A ≥ n) = U_A(x, X)`), `coe_eq_tsum_le`, `one_le_atomMeasure_univ` |
| p. 236 | `π` denotes the unique invariant measure, normalised when finite | `invMeasure` (recurrent chains), `stationaryDist` (positive chains) |
| (10.13), p. 236 | `μ°_α(A) = E_α[Σ_{n=1}^{τ_α} 1{Φₙ ∈ A}]` for recurrent chains | `tabooPotKernel_eq_lintegral` (`U_A(x, B) = E_x[Σ_{n=1}^{τ_A} 1{Φₙ ∈ B}]`, for every measurable `A` and every chain) |
| Theorem 10.2.2, (10.14), p. 236 | Kac's theorem: for an atom `α ∈ B⁺(X)`, `Φ` is positive iff `E_α[τ_α] < ∞`, and `π(α) = E_α[τ_α]⁻¹` | `theorem_10_2_2` (every invariant probability `π`) |
| p. 236 | Proof: `π(α) = μ°_α(α)/μ°_α(X) = U_α(α, α)/U_α(α, X)` | In the proof of `theorem_10_2_2`, with `IsSubinvariantMeasure.eq_smul_atomMeasure`, `theorem_10_2_1_iii` and `proposition_10_1_1` |
| Proposition 10.2.3, p. 236 | For a positive recurrent irreducible chain on a countable space, `π(x) = E_x[τ_x]⁻¹`, unique up to constant multiples | `proposition_10_2_3` (positive, with `ψ{x} > 0` for every `x`; measurable singletons), `proposition_10_2_3_unique` (one invariant probability); `isAtom_singleton` (carried) |

## §10.3.1 Renewal chains

| Source | Claim | Lean |
| --- | --- | --- |
| (10.15), p. 236 | The forward recurrence time chain `V⁺`: `P(1, j) = p(j)`, `P(j, j − 1) = 1` for `j > 1` | `fwdRecKernel` (carried; on `ℤ₊`, renewal state `0`, from `0` to `n − 1` with probability `p(n)`), `fwdRec_zero_singleton`, `fwdRec_succ` |
| p. 237 | The chain is always recurrent (§8.1.2) | The renewal state is recurrent for every `p`: `fwdRec_isRecurrentState_zero` (carried). With unbounded support the chain is irreducible and recurrent for counting measure: `fwdRec_isIrreducibleChain`, `fwdRec_isRecurrentChain` (`isRecurrentChain_count_iff`, `fwdRec_isRecurrentState`, carried); `fwdRec_isAccessibleAtom` |
| p. 237 | `_1Pⁿ(1, j) = p(j + n − 1)` for `j ≤ n`, and zero otherwise | The formula holds for every `j`: `fwdRec_tabooKernel` (in the shifted indexing, `_0Pᵐ⁺¹(0, j) = p(j + m + 1)`; `tabooKernel`, carried). The restriction to `j ≤ n` is false: `fwdRec_tabooKernel_counterexample` (`p = δ₂`, the book's `n = 1`, `j = 2`) |
| (10.16), p. 237 | The minimal invariant measure is `π(j) = U₁(1, j) = Σ_{n ≥ j} p(n)` | `fwdRecInv` (`π(j) = Σ_{n > j} p(n)`, shifted to `ℤ₊`), `fwdRecInv_singleton`, `sigmaFinite_fwdRecInv`, `fwdRecInv_eq_atomMeasure` (`π = U₀(0, ·)`, from `isInvariant_fwdRecInv` and the uniqueness `theorem_10_2_1_ii_unique`) |
| (10.17), p. 237 | `Σⱼ π(j) = Σₙ n p(n)`: `π` is finite iff `p` has finite mean | `fwdRecInv_univ`, `fwdRec_isPositive_iff` (with unbounded support), `tsum_indicator_Iio` |
| p. 237 | The formula can also be found by solving the invariant equations | `isInvariant_fwdRecInv` (direct verification, `p(0) = 0`) |
| (10.18), p. 237 | Periodicity of `p`, the span `[N_p]`, Lemma D.7.4, and aperiodicity of `V⁺` when `d = 1` | Not formalised |
| (10.19), p. 237 | The linked chain `V* = (V⁺₁, V⁺₂)` of two independent copies | `linkedFwdRec` (`fwdRecKernel p ∥ₖ fwdRecKernel p`, Mathlib's `Kernel.parallelComp`) |
| p. 237 | `V*` is ψ-irreducible when `p` has period `1` | Not formalised |
| pp. 237–238 | `π*(i, j) = π(i)π(j)` is invariant for `V*` and `π*(X*) = [π(X)]²`, so `V*` is positive Harris when `Σ k p(k) < ∞` | `isInvariant_parallelComp` (`π ⊗ σ` is invariant for `P ∥ₖ Q`), `isInvariant_linkedFwdRec`, `linkedFwdRec_univ`. The positive Harris property, which needs the ψ-irreducibility of `V*`, is not formalised |
| p. 238 | These conditions are used in Part III | Not formalised (remark) |

## §10.3.2 The number in an M/G/1 queue

| Source | Claim | Lean |
| --- | --- | --- |
| p. 238 | `N*` on `ℤ₊` with the matrix of rows `q₀ q₁ q₂ …`, `qᵢ = P(Z = i − 1)` | `mg1Matrix`, `mg1Kernel`, `isTransitionMatrix_mg1` (`matKernel`, `IsTransitionMatrix`, carried) |
| p. 238 | `N*` is ψ-irreducible if `q₀ > 0`, irreducible if also `q₀ + q₁ < 1` | Taken as hypotheses: `q(0) ≠ 0` and a maximal irreducibility measure `ψ` in `proposition_10_3_1` |
| (10.20), p. 238 | `π(j) = Σ_{k ≤ j+1} π(k) q_{j+1−k}`; with `q̄ⱼ = Σ_{n > j} qₙ`, the system `π(1)q₀ = π(0)q̄₀`, `π(2)q₀ = π(0)q̄₁ + π(1)q̄₁`, … | `qTail` (`q̄(m) = Σ_{n ≥ m} q(n)`, the book's `q̄_{m−1}`), `qTail_zero`, `qTail_eq`, `qTail_le_one`, `q_zero_add_qTail_one`; `mg1_row_tail_zero`, `mg1_row_tail_succ`, `mg1_col_tail`, `mg1_cut_of_invariant` (the system, for an invariant probability); `pointMeasure`, `isInvariant_matKernel_pointMeasure_iff` |
| p. 238 | The invariant measure is always unique, whether the chain is transient or recurrent | `mg1_invariant_unique` (two solutions of the invariant equations, finite on points and equal at `0`, are equal; `q(0) > 0`, no irreducibility), `mg1_invariant_unique_smul` (uniqueness up to constant multiples), `mg1_col_split` (the `j`-th equation isolates `π(j + 1) q(0)`). The solution with `π(0) = 1` is built recursively: `mg1Seq`, `mg1Seq_succ`, `mg1Seq_zero`, `mg1Seq_cut`, `mg1Seq_ne_top` |
| p. 238 | The mean increment `β = Σ_{j ≥ 0} q̄ⱼ − 1` | `mg1Mean` (`Σⱼ j q(j)`, the book's `β + 1`), `tsum_qTail_succ`, `mg1Mean_eq` |
| (10.21), pp. 238–239 | Summing the system: `(1 − q̄₀) Σ_{j ≥ 1} π(j) = (β + 1)π(0) + (β + 1 − q̄₀) Σ_{j ≥ 1} π(j)`; positivity forces `β < 0`, and `π(0) = −β` makes `π` finite | `mg1_sum_cut`, `tsum_sum_range_lt`, `tsum_qTail_shift`, `mg1_zero_pos`, `mg1_invariant_prob_zero` (`π(0) = 1 − Σⱼ j q(j)`); conversely `sum_sum_range_lt_le`, `mg1Seq_partial_le`, `mg1Seq_tsum_le` (`Σ_{k ≥ 1} π(k) ≤ β'/(1 − β')`), `isInvariant_mg1Seq` |
| Proposition 10.3.1, p. 239 | `N*` is positive iff `β = Σ j qⱼ < 1` | `proposition_10_3_1` (`Σⱼ j q(j) < 1`; see corrections for the two definitions of `β`) |
| p. 239 | The same direct calculation works for skip-free chains | Not formalised (remark) |

## §10.3.3 The number in a GI/M/1 queue

| Source | Claim | Lean |
| --- | --- | --- |
| p. 239 | `N` on `ℤ₊` with `P(i, j) = p_{i+1−j}` for `1 ≤ j ≤ i + 1` and `P(i, 0) = Σ_{k > i} p_k`, `pᵢ = P(Z = 1 − i)` | `gim1Matrix`, `gim1Kernel`, `isTransitionMatrix_gim1`, `tsum_indicator_Ioi` |
| p. 239 | `N` is ψ-irreducible if `p₀ + p₁ < 1`, irreducible if also `p₀ > 0`; `α = {0}` | Taken as hypotheses: `p(0) > 0` and a maximal irreducibility measure `ψ` in `proposition_10_3_2` |
| (10.22), p. 239 | The last-exit decomposition over the last visit to `[k]`: `_αPⁿ(α, k + 1) = Σ_r _αPʳ(α, k) _{[k]}P^{n−r}(k, k + 1)` | Through the GI/M/1 chain as a ladder chain with one-point rungs, `Λₖ(x, ·) = p(k) δ₀`: `gim1Lam`, `gim1LamStar`, `gim1LadderKernel`, `rungEmb`, `measurable_rungEmb`, `gim1_map_rungEmb_apply`, `gim1Ladder_eq_map` (the ladder version moves as the GI/M/1 chain embedded by `i ↦ (i, 0)`), `rungEmb_preimage_rung_zero`; taboo probabilities transfer along the embedding (`tabooKernel_map_of_comp`, `tabooPotKernel_map_of_comp`, `tabooKernel_eq_of_eq`, `gim1_tabooPot_map`), and the decomposition is the ladder chain's (10.45) (`ladderS_succ`) |
| (10.23), p. 239 | Translation invariance: `_{[k]}Pʳ(k, j) = _αPʳ(α, j − k)` | Used in the form of the column identity `Σᵢ sⁱ P(i, j + 1) = sʲ g(s)`: `gim1_col_succ`, with `gim1Gen` (`g(s) = Σⱼ p(j) sʲ`) |
| (10.24), p. 240 | `μ°_α(k + 1) = μ°_α(k) μ°_α(1)`, so `μ°_α(k) = s_αᵏ` | `gim1Alpha` (`s_α = μ°_α(1)`), `atomMeasure_gim1_eq`, `gim1_ladS` (`S(y, ·) = s_α δ₀`), `gim1_ladS_pow`, `gim1_minimal_geom` (`μ°_α(k) = s_αᵏ` for `k ≥ 1`, through `ladderS_eq_pow`); for any root `s < 1` of (10.25), `μ(k) = sᵏ` is invariant: `isInvariant_gim1_geom` |
| (10.25), p. 240 | `s_α` solves `s = Σⱼ pⱼ sʲ` (the invariant equation at `1`), is its smallest solution, and lies in `(0, 1)` iff `Σ j pⱼ > 1`; otherwise `s_α = 1` | `gim1Alpha_root`; minimality `gim1Alpha_le_of_root` (`s_α ≤ s` whenever `Σⱼ p(j) sʲ ≤ s`, from `ladS_minimal`), `const_pow_univ`; `gim1Alpha_le_one`, `gim1Alpha_pos` (`p(0) > 0`), `gim1Alpha_lt_one_of_mean` (`Σ j p(j) > 1`), `gim1Alpha_eq_one_of_mean_le` (`Σ j p(j) ≤ 1`, ψ-irreducible, `p(0) > 0`). Without the minimal root: `gim1_col_zero` (`(1 − s) Σᵢ sⁱ P(i, 0) + g(s) = 1`), `gim1_col_zero_eq`, `one_sub_mul_geom_add`, `exists_gim1_root` (a root in `(0, 1)` when `p(0) > 0` and `Σ j p(j) > 1`, by the intermediate value theorem) |
| p. 240 | One verifies directly that `μ°_α` solves all the invariant equations; if `Σ j pⱼ = 1`, the chain is recurrent (§9.1), `μ ≡ 1` is the invariant measure and `1 = Σⱼ Σ_{n > j} pₙ` | `isInvariant_gim1_geom`; `isInvariant_gim1_one` (`μ ≡ 1` invariant iff `Σ j p(j) = 1`), `isSubinvariant_gim1_one` (subinvariant iff `≤ 1`), `gim1_col_zero_one` (`Σᵢ P(i, 0) = Σ j p(j)`). For `Σ j p(j) = 1`, recurrence follows from `μ°_α(α) = 1` (`IsAccessibleAtom.isRecurrentChain_iff`, `gim1_minimal_geom`, `gim1Alpha_eq_one_of_mean_le`) in `proposition_10_3_2_mean_one`, without §9.1 |
| Proposition 10.3.2, p. 241 | The unique subinvariant measure is `μ_α(k) = s_αᵏ`, `s_α` the minimal solution of (10.25) in `(0, 1]`; `N` is positive iff `Σ j pⱼ > 1` | `proposition_10_3_2` (positive iff `Σ j p(j) > 1`); `proposition_10_3_2_unique` (for a positive chain every subinvariant measure is a finite multiple of `sᵏ`, for any root `s ∈ (0, 1)`); `proposition_10_3_2_mean_one` (for `Σ j p(j) = 1`, `p(0) > 0` and `{0}` an accessible atom: the chain is recurrent, `μ°_α ≡ 1`, and every subinvariant measure is a multiple of `μ ≡ 1`) |
| p. 241 | Theorem 10.2.1 motivates the trial solution; `s_α` is the expected number of visits to `k + 1` from `k`, for any `k` | `gim1Alpha` is defined as `μ°_α(1) = U_α(0, {1})`, the case `k = 0`; the statement for every `k` is not formalised (remark) |
| p. 239, p. 241 | Measures on `ℤ₊` given by weights | `pointMeasure`, `pointMeasure_singleton`, `pointMeasure_univ`, `matKernel_comp_pointMeasure_singleton`, `isInvariant_matKernel_pointMeasure_iff`, `isSubinvariant_matKernel_pointMeasure_iff`, `tsum_split` |

## §10.4.1 Invariant measures for recurrent chains

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 10.4.1 (i), (10.26), p. 241 | For a strongly aperiodic chain, if `π̌` is invariant for `Φ̌`, then `π(A) = π̌(A₀ ∪ A₁)` is invariant for `Φ` and `π̌ = π*` | `proposition_10_4_1_i` (every minorization `M : Minorization P`, carried; `π = π̌ ∘ fst⁻¹`; `Minorization.splitKernel`, `Minorization.split`, carried) |
| Proposition 10.4.1 (ii), p. 241 | If `μ` is subinvariant (invariant) for `Φ`, so is `μ*` for `Φ̌` | `proposition_10_4_1_ii` (every minorization), `sigmaFinite_split` |
| pp. 241–242 | Proof by (5.5)–(5.7) and (5.10) | The carried splitting identities of `Splitting` and `SplitMarginal`, in the proofs |
| Proposition 10.4.2, p. 242 | A recurrent strongly aperiodic chain has a unique (up to constant multiples) subinvariant measure, which is invariant | `proposition_10_4_2` (a minorization on `C ∈ B⁺(X)`; nonzero invariant `π` with `π(C) < ∞`, and `μ = cπ` with `c < ∞` for every subinvariant `μ`) |
| p. 242 | Proof: `Φ̌` is recurrent (Proposition 8.2.2), Theorem 10.2.1 for `Φ̌`, and Proposition 10.4.1 | `Minorization.isRecurrentChain_split_of_isRecurrentChain`, `Minorization.theorem_5_1_3_ii` (the atom `α̌` is accessible), `theorem_10_2_1_i`, `IsSubinvariantMeasure.eq_smul_atomMeasure` and `proposition_10_4_1_i`, in the proof of `proposition_10_4_2` |
| Theorem 10.4.3, p. 242 | For `ε ∈ (0, 1)`, `π` is invariant for `K_{a_ε}` iff it is invariant for `P` | `theorem_10_4_3` (σ-finite `π`; `resolvent`, carried); `lintegral_sampledKernel`, `comp_sampledKernel_comp_apply`, `eq_of_eq_on_finite` |
| Theorem 10.4.4, p. 242 | A recurrent chain has a unique (up to constant multiples) subinvariant measure, which is invariant | `theorem_10_4_4` (countably generated `X`), `IsRecurrentChain.isInvariant_of_isSubinvariantMeasure`, `IsRecurrentChain.exists_eq_smul`; `invMeasure`, `isInvariantMeasure_invMeasure`, `invMeasure_ne_zero`, `eq_smul_invMeasure` |
| pp. 242–243 | Proof: `K_{a_ε}` is strongly aperiodic (Theorem 5.2.3) and recurrent (Theorem 8.2.4); Proposition 10.4.2 and Theorem 10.4.3 | With `ε = 1/2`: `theorem_5_2_3_resolvent`, `proposition_8_2_4` (carried), `proposition_10_4_2`, `theorem_10_4_3`, `IsSubinvariant.resolvent`, in the proof of `theorem_10_4_4` |
| Theorem 10.4.5, p. 243 | For a ψ-irreducible aperiodic chain, `π` is invariant for the `m`-skeleton iff it is invariant for `Φ`; `Φ` is positive iff each `m`-skeleton is | `theorem_10_4_5` (recurrent chains, σ-finite `π`, `m ≥ 1`; `IsAperiodic`, carried), `theorem_10_4_5_positive` (positive iff every, iff some, `m`-skeleton is positive; no recurrence assumed) |
| p. 243 | Proof: the average `m⁻¹ Σ_{k < m} πₘPᵏ` and the uniqueness of `πₘ` for `Pᵐ` | By uniqueness for the recurrent skeleton `Pᵐ` (`theorem_8_2_6_ii`, carried; `IsRecurrentChain.exists_eq_smul`), in the proof of `theorem_10_4_5`; `proposition_5_4_5_iii` (carried) for the irreducibility of the skeletons in `theorem_10_4_5_positive` |

## §10.4.2 Minimal subinvariant measures

| Source | Claim | Lean |
| --- | --- | --- |
| p. 243 | No irreducibility is needed in this section | The module `MinimalInvariant` assumes none |
| (10.27), p. 243 | `μ°_A(B) = ∫_A μ(dy) U_A(y, B)` for `0 < μ(A) < ∞` | `minimalMeasure` (every measurable `A` and measure `μ`), `minimalMeasure_apply`, `minimalMeasure_self` (`μ°_A(A) = ∫_A μ(dy) L(y, A)`), `minimalMeasure_self_le` |
| p. 243 | The taboo measures `μ_APⁿ` | `tabooSeq`, `tabooSeq_zero`, `tabooSeq_succ`, `tabooKernel_succ_eq` (`tabooKernel`, carried), `tabooPotKernel_comp`, `tabooPotKernel_comp_eq` (`ρU_A = ρP + Σₙ ρ_APⁿ⁺²`); `indKernel_comp_eq_restrict`, `kernelSum_comp`, `comp_measureSum`, `comp_restrict_finsetSum` |
| Proposition 10.4.6, p. 243 | `μ°_A` is subinvariant and `μ ≥ μ°_A` | `proposition_10_4_6`, `proposition_10_4_6_minimal` (every subinvariant `μ`, every measurable `A`) |
| p. 244 | Proof: induction on `μ(B) ≥ ∫_A μ(dw) Σ_{m ≤ n} _APᵐ(w, B)`, then the subinvariance of `μ°_A` | In the proofs; `comp_tabooPotKernel_comp` (`(ρU_A)P = (ρU_A restricted to A)P + Σₙ ρ_APⁿ⁺²`) |
| p. 244 | `Ā = {x : L(x, A) > 0}` | Its complement `Āᶜ = {L(·, A) = 0}` is `noHitSet` (carried) |
| Theorem 10.4.7 (i), (10.28)–(10.29), pp. 244–245 | If `L(x, A) ≡ 1` for `μ`-almost all `x ∈ A`, then `μ(B) = μ°_A(B)` for `B ⊆ A` | `theorem_10_4_7_i` (`μ` subinvariant, `μ(A) < ∞`; `μ°_A` and `μ` agree on `A`), `minimalMeasure_self_eq`, `eq_of_add_eq_of_le` |
| Theorem 10.4.7 (ii), (10.30), p. 245 | `μ°_A` is invariant, and `μ°_A(Āᶜ) = 0` "by definition" | `theorem_10_4_7_ii`; invariance from `comp_tabooPotKernel_comp` and (10.29); `μ°_A(Āᶜ) = 0` by a mass argument, with `prob_noHitSet_inter_compl` |
| p. 245 | Proof of (i) by contradiction, through the resolvent and "Proposition 10.4.3" | Not needed; (10.28) proves (i). The citation is to Theorem 10.4.3 |
| p. 245 | The process on `A` with law `U_A(x, B) = P_x{Φ_{τ_A} ∈ B}`; a subinvariant measure restricted to a Harris recurrent `A` is invariant for it | The identity `U_A(x, ·) = P_x(Φ_{τ_A} ∈ ·; τ_A < ∞)` is `setLIntegral_firstReturn_eq_tabooPotKernel` (carried); the invariance for the process on `A` is (10.29), `theorem_10_4_7_i`. The process on `A` is not built as a chain |
| Proposition 10.4.8, p. 245 | If `ν` is an invariant probability supported on `A` with `∫_A ν(dx) U_A(x, B) = ν(B)` for `B ⊆ A`, then `ν°(B) = ∫_A ν(dx) U_A(x, B)` is invariant | `proposition_10_4_8` (any measure `ν`, not necessarily a probability or supported on `A`) |
| p. 235, p. 244 | The uniqueness device in the proof of Theorem 10.2.1 (ii) | `eq_of_le_of_lintegral_le` (`μ₀ ≤ μ`, `∫ f dμ ≤ ∫ f dμ₀ < ∞`, `0 < f < ∞` force `μ = μ₀`) |

## §10.4.3 The structure of π for recurrent chains

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 10.4.9, (10.31), p. 246 | For a recurrent chain, `π ≅ ψ`, and for `A ∈ B⁺(X)`, `π(B) = ∫_A π(dy) U_A(y, B) = ∫_A π(dy) E_y[Σ_{k=1}^{τ_A} 1{Φₖ ∈ B}] = ∫_A π(dy) E_y[Σ_{k=0}^{τ_A−1} 1{Φₖ ∈ B}]` | `theorem_10_4_9_equiv` (nonzero invariant `π`), `theorem_10_4_9` (`π = π°_A` for `A ∈ B⁺(X)` with `π(A) < ∞`), `theorem_10_4_9_path`, `theorem_10_4_9_path'` (countably generated `X`) |
| p. 246 | Proof: `π = π°_A` for a Harris recurrent `A` by Theorem 10.4.7 | `ae_hitProb_eq_one` (`L(·, A) = 1` `π`-a.e., from the Harris decomposition `theorem_9_1_5` and `harrisQ_le_hitProb`, carried), `theorem_10_4_7_ii` and `IsRecurrentChain.exists_eq_smul`, in the proof of `theorem_10_4_9` |
| p. 246 | The third equality by (10.29): `∫_A π(dy) E_y[1{Φ_{τ_A} ∈ B}] = ∫_A π(dy) E_y[1{Φ₀ ∈ B}]` | `sum_before_return_add` (the pathwise identity), `le_firstReturn_add_two_iff`, in the proof of `theorem_10_4_9_path'` |
| p. 246 | Proof of `π ≅ ψ`: `ψ ≪ π` by Proposition 10.1.2; if `ψ(B) = 0`, `B⁰ ∈ B⁺(X)` and `π(B) = ∫_{B⁰} π(dy) U_{B⁰}(y, B) = 0` | `proposition_10_1_2_ii`; `π°_{B⁰}` with `B⁰ = noHitSet P B`, `tabooPotKernel_eq_zero_of_hitProb`, `tabooPotKernel_le_potKernel` and uniqueness, in the proof of `theorem_10_4_9_equiv` |
| p. 246 | `π(B)` is proportional to the time spent in `B` between visits to `A`; for an atom `α`, (10.31) reduces to `μ°_α` | The interpretation is not formalised; the reduction is `minimalMeasure_atom` (`μ°_A = μ(α) μ°_α` for `A = α`) |
| p. 246 | These concepts are used in Chapter 13 and Chapter 11 | Not formalised (remark) |
| Theorem 10.4.10 (i), (10.32), pp. 246–247 | For a ψ-irreducible chain and a subinvariant `μ`, `Φ` is positive iff `∫_A μ(dy) E_y[τ_A] < ∞` for one, and then every, set with `μ(A) > 0` | `theorem_10_4_10_i` (`μ ≠ 0`, measurable `A`; countably generated `X`); the halves `theorem_10_4_10_i_of_exists` (no countable generation) and `theorem_10_4_10_i_forall` |
| p. 247 | Proof: `μ°_A(X) = ∫_A μ(dy) E_y[τ_A]` | `minimalMeasure_univ`, `one_le_meanReturnTime`, `hitProb_eq_one_of_meanReturnTime_ne_top` |
| Theorem 10.4.10 (ii), (10.33)–(10.34), p. 247 | If `sup_{y ∈ C} E_y[τ_C] < ∞` for a petite `C ∈ B⁺(X)`, `μ` is finite and `Φ` positive; positive Harris if also `E_x[τ_C] < ∞` for every `x` | `theorem_10_4_10_ii` |
| p. 247 | Proof: `μ(C) < ∞` (Proposition 10.1.2) and "the criterion in Theorem 9.1.7" | `proposition_10_1_2_iii`; the criterion is Proposition 9.1.7 (`proposition_9_1_7_ii`, carried) |
| p. 230, p. 236 | The invariant probability of a positive chain | `IsPositive.invariant_prob_unique`, `stationaryDist`, `isProbabilityMeasure_stationaryDist`, `isInvariant_stationaryDist`, `eq_stationaryDist`, `IsPositive.eq_smul_stationaryDist` |
| p. 230 | A recurrent chain is positive iff `π` is finite | `isPositive_iff_invMeasure_univ` |
| p. 230 | The finiteness criterion of Theorem 10.0.1 from Theorem 10.4.10 | `theorem_10_0_1_finite`, through `theorem_8_3_6_i` (carried: for non-empty `C`, `L(·, C) ≡ 1` on `C` gives `C ∈ B⁺(X)`) and `theorem_10_4_10_ii` |
| p. 247 | Drift conditions for (10.33)–(10.34) in Chapter 11 | Not formalised (remark) |

## §10.5.1 Random walk

| Source | Claim | Lean |
| --- | --- | --- |
| p. 247 | The constructive approach gives or interprets invariant measures for models | Not formalised (informal) |
| (10.35), pp. 247–248 | By Fubini and translation invariance, Lebesgue measure is invariant for random walk on `ℝ`, transient or recurrent | `isInvariant_randomWalk` (every right-invariant s-finite measure on an additive group, every increment law; `randomWalkKernel`, carried), `isInvariant_volume_randomWalk` (Mathlib's `volume` on `ℝ`) |
| Proposition 10.5.1, p. 248 | Random walk on `ℝ` is never positive recurrent | `proposition_10_5_1` (no hypothesis on `Γ`, every `ψ`), by `IsPositive.eq_smul_stationaryDist` |
| p. 248 | With mean zero the walk is null recurrent (§9.5) | `randomWalk_null_recurrent` (ψ-irreducible, spread-out increments with mean zero and finite variance: recurrent by `proposition_6_3_2`, `proposition_9_4_5` and `theorem_9_2_2_ii`, carried, and null by `proposition_10_5_1`; `IsNull`) |
| Proposition 10.5.2, p. 248 | For spread-out `Γ` with mean zero and finite variance, `A` bounded with `μ^{Leb}(A) > 0`, `Φ₀` uniform on `A`, and bounded `B, C` with `μ^{Leb}(C) > 0`: `E[N_A(B)]/E[N_A(C)] = μ^{Leb}(B)/μ^{Leb}(C)` | `proposition_10_5_2` (a recurrent walk, `0 < μ^{Leb}(A) < ∞`: `E[N_A(B)] = ∫ uniform_A(dy) U_A(y, B) = μ^{Leb}(B)/μ^{Leb}(A)`; `uniformOn`), `proposition_10_5_2_ratio` (in `[0, ∞]`), `proposition_10_5_2_spreadOut` (the book's hypotheses, with a maximal irreducibility measure `ψ`; `IsSpreadOut`, carried) |
| p. 248 | Proof: non-evanescence by Proposition 9.4.5, hence recurrence; `π = μ^{Leb}/π(A)` and (10.31) | `proposition_6_3_2`, `theorem_9_2_2_ii`, `proposition_9_4_5` (carried), in the proof of `proposition_10_5_2_spreadOut`; `theorem_10_4_9`, `theorem_10_4_9_equiv`, in the proof of `proposition_10_5_2` |

## §10.5.2 Forward recurrence time chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 248 | The forward recurrence time `δ`-skeleton `V⁺_δ` of §3.5 | `fwdSkelKernel` (carried; increment law on `[0, ∞)`, not concentrated at `0`, `δ ≥ 0`); `fwdSkelKernel_apply_eq_tsum`, `fwdSkelKernel_Iic_zero` (`V⁺_δ` lives on `(0, ∞)`) |
| p. 248 | `F[y, ∞) dy ≤ U_{[0, δ]}(x, dy) ≤ F[y − δ, ∞) dy`, and the normalised sandwich for `π_δ` | Not formalised |
| p. 248 | `V⁺_δ` is the two-step chain of `V⁺_{δ/2}`, so `π_δ = π_{δ/2}`; letting `δ/2ⁿ → 0` gives (10.36) | Not formalised; (10.36) is verified directly for every `δ` |
| (10.36), p. 248 | `π_δ(dy) = m⁻¹ F[y, ∞) dy`, `m = ∫ t F(dt)`, a probability when `m < ∞` | `fwdSkelInv` (`F[y, ∞) dy` on `(0, ∞)`, unnormalised), `isInvariant_fwdSkelInv` (every `δ ≥ 0`), `fwdSkelInv_univ` (total mass `m`), `isProbabilityMeasure_fwdSkelInv_normalised` |
| p. 249 | "By direct integration" (10.36) is invariant | `tsum_straddle` (exactly one renewal interval straddles `s > 0`), `tsum_prod_straddle`, `convPow_prod_apply`, `measurable_partialSum_pair`, `fwdSkel_core`, `lintegral_shift_window`, `prod_apply_window`, `prod_apply_straddle`, `measurable_tail_Ici`, `measurable_shift_measure`, `ite_of_cond`, `ite_of_not_cond` |
| p. 249 | `F[y, ∞) dy` is the expected time in `dy` per excursion from `{0}` | Not formalised (remark) |

## §10.5.3 Ladder chains and GI/G/1 queues

| Source | Claim | Lean |
| --- | --- | --- |
| (10.37), p. 249 | The ladder chain on `ℤ₊ × X`: `P(i, x; j × A) = Λ_{i−j+1}(x, A)` for `1 ≤ j ≤ i + 1`, `0` for `j > i + 1`, `Λ*ᵢ(x, A)` for `j = 0` | `ladderChainKernel` (carried; rungs in `ℝ`), `eq_3_40_zero`, `eq_3_40_mid`, `eq_3_40_up` (carried); `rung`, `aboveRung`, `measurableSet_rung`, `measurableSet_aboveRung`, `rung_zero_compl` |
| p. 249 | General rungs; matrix methods for finite rungs | Not formalised (remark); the rungs are `ℝ` |
| p. 249 | Standing assumption: positive Harris with `ψ([0]) > 0`; `π₀` the invariant probability of the process on `[0]` | Replaced by recurrence, `ψ([0]) > 0` and `π([0]) < ∞` in `theorem_10_5_3`; `π₀` is `π` restricted to `[0]`, seen on `ℝ` (`setLIntegral_rung_zero`) |
| Theorem 10.5.3, (10.38)–(10.40), pp. 249–250 | `π(k × A) = ∫ π₀(dy) Sᵏ(y, A)`, `Sᵏ = S Sᵏ⁻¹`, for the minimal solution `S` of `S(y, B) = Σₖ ∫ Sᵏ(y, dz) Λₖ(z, B)` | `theorem_10_5_3`, `ladS`, `ladS_eq` (10.40), `ladS_minimal`, `ladderS_eq_pow` (10.39) |
| (10.41)–(10.43), p. 250 | By (10.31), `π(k × A) = ∫_{[0]} π₀(dy) U_{[0]}(0, y; k × A)`; `S^{(k)}(y, A) = U_{[0]}(0, y; k × A)` | `theorem_10_4_9` with `A = [0]`, in the proof of `theorem_10_5_3`; `ladderS`, `ladderS_apply`, `ladderS_apply_measure`, `ladderS_apply_eq_tsum`; `ext_nat_prod`, `lintegral_nat_prod`, `map_snd_restrict_rung_apply` |
| (10.44), p. 250 | Translation invariance above level `0`: `U_{[n]}(n, y; (n + k) × B) = U_{[0]}(0, y; k × B)` | `ladL` (the chain killed at levels `≤ k`), `rungShift`, `measurable_rungShift`, `ladder_translate_iter`, `ladL_translate`, `ladL_pow_translate` (`ladderChainKernel_translate`, carried) |
| p. 250 | The taboo probabilities `_{[0]}Pⁿ` | `tabooKernel_rung_zero`, `tabooKernel_eq_ladQ_pow` (off `[0]` they are the powers of `Q = ladL Λ Λ* 0`), `tabooKernel_restrict_rung`, `indKernel_congr`, `indKernel_comp_indKernel_comp`, `comp_finset_sum_measure`, `comp_pow_comp` |
| (10.45), p. 250 | The last-exit decomposition over visits to `[k]`, with the skip-free property: the last visit to `[k]` before `(k + 1) × X` is at level `k` | `restrict_pow_comp_decomp` (for a general kernel and set), `ladder_apply_aboveRung_succ`, `ladL_apply_of_lt`, `ladL_pow_succ_apply_of_lt`, `ladL_pow_apply_rung`, `ladQ_pow_succ_decomp`, `ladderS_succ` (`S^{(k+1)} = S^{(k)}S` for `k ≥ 1`) |
| (10.46), p. 250 | `_{[0]}Pⁿ(0, x; 1 × B) = Σ_{k ≥ 1} ∫ _{[0]}Pⁿ⁻¹(0, x; k × dy) Λₖ(y, B)` | `ladQ_apply_rung_one`, `ladQ_pow_succ_succ_rung_one`, `ladQ_pow_succ_restrict_rung_zero`, `ladS_eq` |
| (10.47), p. 250 | The partial sums `S_N(x; k × B)` | `ladSN`, `ladSN_apply`, `measurable_ladSN`, `ladderS_apply_eq_iSup` |
| (10.48)–(10.49), pp. 250–251 | `S_{N−1}(x; k + 1 × B) ≤ ∫ S_{N−1}(x; k × dy) S_{N−1}(y; 1 × B)`; `S_N(x; 1 × B) = Λ₀(x, B) + Σ_{k ≥ 1} ∫ S_{N−1}(x; k × dy) Λₖ(y, B)` | `ladSN_succ_le`, `ladSN_succ_one`, `sum_sum_range_lt_le_finite` |
| (10.50)–(10.51), p. 251 | By induction `S_N ≤ S*` for every solution `S*`, so `S` is minimal | `ladS_minimal` (every `S*` with `S* ≥ Σₖ S*ᵏ Λₖ`) |
| p. 251 | Theorem 10.5.3 generalises (10.24)–(10.25), where the rungs were singletons | Used in that direction: (10.24)–(10.25) are proved from the ladder chain results with one-point rungs (`gim1LadderKernel`, `gim1_minimal_geom`, `gim1Alpha_le_of_root`) |
| p. 251 | For the GI/G/1 queue, `Φₙ = (Nₙ, Rₙ)` is a ladder chain (§3.5) | `gig1Ladder`, `gig1Lambda`, `gig1LambdaStar` (carried), `gig1Ladder_eq` |
| p. 251 | The process on `[0]` is i.i.d. with the service law `H`, hence positive Harris with invariant probability `H` | `gig1_entrance` (`P(z, 0 × A) = P(z, [0]) H(A)`), `tabooPotKernel_rung_zero_of_entrance` (`U_{[0]}(z, 0 × A) = L(z, [0]) H(A)`); in the proof of `theorem_10_5_4_eq`, `π₀ = π([0]) H` |
| Theorem 10.5.4, (10.52)–(10.53), p. 252 | The GI/G/1 ladder chain has an invariant probability iff `π(k × A) = ∫ H(dy) Sᵏ(y, A)` is finite, and then `π` normalised is the unique invariant probability | `theorem_10_5_4` (recurrent, `ψ([0]) > 0`), `theorem_10_5_4_invariant` (finite `π̃` is invariant, no irreducibility), `theorem_10_5_4_eq` (every invariant probability is `π([0]) π̃`); `gig1Tilde`, `gig1Tilde_apply_prod`, `measure_univ_nat_prod` |
| p. 252 | Proof: `π` is the minimal subinvariant measure, "and the result is then obvious" | Sufficiency through Proposition 10.4.8 for `ν = δ₀ ⊗ H` (`gig1Bottom`, `gig1Bottom_restrict`, `gig1_minimal_apply`, `proposition_10_4_8`), with the finiteness of `π̃` giving a sure return to `[0]` from `H`-almost every point; the form of `π` through `theorem_10_5_3` |

## §10.5.4 Linear state space models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 252 | The route through (10.4); Chapter 12 | Not formalised (remark) |
| p. 252 | Under (LSS1)–(LSS2), `X_k = Fᵏx₀ + Σ_{i<k} Fⁱ G W_{k−i} ∼ Fᵏx₀ + Σ_{i<k} Fⁱ G Wᵢ`, and `Pᵏg(x₀) = E[g(Fᵏx₀ + Σ_{i<k} Fⁱ G Wᵢ)]` | Not formalised. The model is `lssMatrixKernel` (carried); `lssMatrixKernel_comp` (`μP = (μ ⊗ Γ) ∘ step⁻¹`) |
| pp. 252–253 | Under (LSS5), `Fⁱ → 0` geometrically (Lemma 6.3.4), and with `E|W| < ∞` the series `X_∞ = Σᵢ Fⁱ G Wᵢ` converges absolutely with `E|X_∞| ≤ E|W| Σ ‖Fⁱ G‖` | `IsStableMatrix`, `isStableMatrix_geometric` (carried); `lssTerm`, `lssSeries`, `measurable_lssSeries`, `norm_mulVec_le`, `ae_summable_lssSeries` (almost sure absolute convergence under `Γ^{⊗ℕ}`) |
| p. 253 | `lim_k Pᵏg(x₀) = E[g(X_∞)]` by dominated convergence | Not formalised |
| p. 253 | `π_∞`, the law of `X_∞`, is an invariant probability (through the Feller property and bounded continuous `g`) | `lssLimitLaw`, `isProbabilityMeasure_lssLimitLaw`, `isInvariant_lssLimitLaw`, by the identity `X_∞(v, W₀, W₁, …) = G v + F X_∞(W₀, W₁, …)` (`lssSeries_cons`, `consSeq`, `measurable_consSeq`, `prod_map_consSeq`) and the independence of the head and tail of an i.i.d. sequence (`iIndep_coords'`, `seqShift`, `measurable_seqShift`, `infinitePi_map_seqShift`, `indepFun_head_seqShift`, `infinitePi_map_head_tail'`) |
| p. 253 | In the Gaussian case (LSS3), `π = N(0, Σ)` with `Σ = Σₖ Fᵏ G Gᵀ (Fᵀ)ᵏ`, the controllability grammian (4.17) | The scalar case: `isInvariant_ar1_gaussian_stable` (`N(0, σ²/(1 − α²))` for `\|α\| < 1`; Mathlib's `gaussianReal`), `isInvariant_ar1_gaussian` (`N(0, v)` with `v = α²v + σ²`), `ar1Kernel_comp` (`ar1Kernel`, carried). The multivariate Gaussian form is not formalised |
| (10.54), p. 253 | Under (LCM3) `π` has the Gaussian density (10.54); otherwise `π` is concentrated on the controllable subspace and singular | Not formalised |

## §10.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 253–255 | Other approaches to positivity; Doob, Orey, Derman, Vere-Jones, Nummelin, Athreya and Ney, Kac, Harris; the kernels `U^{(r)}` and the limit `π_r` with (10.55)–(10.57) (Arjas and Nummelin); Tweedie; non-irreducible chains; queues; operator-geometric forms (Neuts); Snyders on the linear model | Not formalised (commentary) |
