# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. Three of the claims below are
refuted in Lean by a counterexample, and for each of them a corrected statement is proved. For the
other entries the table says why no counterexample is given. The last section lists what is not
formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Proposition 10.1.2 (ii), p. 233 | For a ψ-irreducible chain, a measure `μ` with `μP ≤ μ` and `μ(A) < ∞` for some `A ∈ B⁺(X)` satisfies `μ ≻ ψ`. The proof: "if `B ∈ B⁺(X)` we have `μ(B) > 0`". | The zero measure satisfies every hypothesis, with `μ(A) = 0 < ∞`, and `ψ ≪ 0` fails because `ψ ≠ 0` (`proposition_10_1_2_ii_counterexample`, for any chain and any nonzero `ψ`). The proof's step `μ(B) > 0` uses `μ ≠ 0`. With `μ ≠ 0` the conclusion holds, and the finiteness hypothesis is then not needed: `ψ ≪ μ` for every nonzero `μ` with `μP ≤ μ` (`proposition_10_1_2_ii`; `IsSubinvariant.pos_of_pos`). |
| Theorem 10.0.1, p. 230 | The invariant measure `π` of a recurrent chain is finite if there is a petite set `C` with `sup_{x ∈ C} E_x[τ_C] < ∞`. | The empty set is petite and `sup_{x ∈ ∅} E_x[τ_∅] = 0`, so as printed every recurrent chain would be positive. The renewal law `heavyRenewal`, `p(2^{k+1}) = 2^{−(k+1)}` for `k ≥ 0`, is a probability with `p(0) = 0`, unbounded support and infinite mean (`isProbabilityMeasure_heavyRenewal`, `heavyRenewal_zero`, `heavyRenewal_supp`, `heavyRenewal_mean`). Its forward recurrence time chain is recurrent, `∅` is petite with the bound `0`, its invariant measure `fwdRecInv` has infinite mass, and the chain is not positive (`theorem_10_0_1_counterexample`). For a non-empty petite `C` the bound gives `L(·, C) ≡ 1` on `C`, hence `C ∈ B⁺(X)` (Theorem 8.3.6, `theorem_8_3_6_i`, carried), and Theorem 10.4.10 (ii) applies: `π` is finite (`theorem_10_0_1_finite`). |
| The forward recurrence time chain, p. 237 | "By construction we have that `_1Pⁿ(1, j) = p(j + n − 1)`, `j ≤ n`, and zero otherwise." | The formula holds for every `j`: from the renewal state the chain jumps to `j + n − 1` with probability `p(j + n − 1)` and then moves down deterministically, reaching `j` at time `n` without returning to `1` before (`fwdRec_tabooKernel`, in the shifted indexing `_0Pᵐ⁺¹(0, j) = p(j + m + 1)` for every `j`). The restriction is false: for `p = δ₂` and the book's `n = 1`, `j = 2`, `_1P¹(1, 2) = P(1, 2) = p(2) = 1`, not `0` (`fwdRec_tabooKernel_counterexample`, here `m = 0`, `j = 1`). The conclusion drawn from it, (10.16), `π(j) = Σ_{n ≥ 1} _1Pⁿ(1, j) = Σ_{n ≥ j} p(n)`, needs the formula for every `n`, including `n < j`, and is right (`fwdRecInv`, `fwdRecInv_eq_atomMeasure`). |
| Theorem 10.4.7 (ii), p. 245 | `μ°_A` is invariant, and "it follows by definition that `μ°_A(Āᶜ) = 0`". | It does not follow from the definition alone, which says nothing about `Āᶜ = {L(·, A) = 0}`; it needs the hypothesis `L(x, A) = 1` for `μ`-almost every `x ∈ A`. The proof here is a mass argument. The masses `bₙ = μ_APⁿ⁺¹(Aᶜ)` tend to `0`, because `μ°_A(A) = μ(A) < ∞` (`minimalMeasure_self_eq`); from a point of `Āᶜ` the chain moves into `Āᶜ ∩ Aᶜ` with probability one (`prob_noHitSet_inter_compl`), so `μ_APⁿ⁺¹(Āᶜ ∩ Aᶜ)` is nondecreasing in `n`; being bounded by `bₙ`, it is `0` (`theorem_10_4_7_ii`). The claim is true, so there is no counterexample. |
| Proposition 10.4.1, p. 241 | Stated for a strongly aperiodic chain and its split chain. | The proof uses only the splitting identities (5.5)–(5.7) and (5.10), which hold for every minorization `M : Minorization P` (carried). Both parts are proved for every minorization (`proposition_10_4_1_i`, `proposition_10_4_1_ii`). The book's statement is a special case, so there is no counterexample. |
| Proposition 10.4.2, p. 242 | A recurrent strongly aperiodic chain has a unique (up to constant multiples) subinvariant measure, which is invariant. | Stated for a minorization on a set `C`, the proof needs `C ∈ B⁺(X)`, as Proposition 8.2.2 does: the split atom `α̌ = C₁` must be accessible for Theorem 10.2.1 to apply to the split chain (`Minorization.theorem_5_1_3_ii`, carried). `proposition_10_4_2` assumes `0 < ψ(C)`. The conclusion holds for every recurrent chain on a countably generated space (Theorem 10.4.4), so there is no counterexample. |
| Theorem 10.4.3, p. 242 | For `ε ∈ (0, 1)`, a measure `π` is invariant for `K_{a_ε}` iff it is invariant for `P`; the proof computes `πP = (1 − ε)ε⁻¹(Σₖ εᵏπPᵏ − π)`. | The chain of equalities subtracts `π`, which needs finite values; in the book this is covered by the definition of an invariant measure, which includes σ-finiteness. `IsInvariant` here has no σ-finiteness, and `theorem_10_4_3` assumes `SigmaFinite π`; the equality is checked on sets of finite `π`-measure (`eq_of_eq_on_finite`). No counterexample is given for measures that are not σ-finite. |
| Theorem 10.4.10 (i), p. 246 | For a ψ-irreducible chain and any subinvariant `μ`, `Φ` is positive iff `∫_A μ(dy) E_y[τ_A] < ∞` for one, and then every, set with `μ(A) > 0`. | For `μ = 0` there is no set with `μ(A) > 0`, so the right side fails for a positive chain; the equivalence needs `μ ≠ 0` (`theorem_10_4_10_i`). The sufficiency half needs no such hypothesis (`theorem_10_4_10_i_of_exists`), nor does the necessity half for every `A` (`theorem_10_4_10_i_forall`). "Every set with `μ(A) > 0`" is read for measurable `A`; for a positive chain such sets lie in `B⁺(X)`, because `μ` is a multiple of `π ≅ ψ`. The failure at `μ = 0` is immediate, so no separate counterexample is stated. |
| Proposition 10.3.1, p. 239 | "The chain `N*` is positive if and only if the increment distribution satisfies `β = Σ j qⱼ < 1`", while p. 238 defines `β = Σ_{j ≥ 0} q̄ⱼ − 1`, the mean increment, and the proof concludes `β < 0`. | The two definitions differ by `1`: `Σⱼ j q(j) = Σ_{m ≥ 1} q̄(m)` is the book's `β + 1` (`tsum_qTail_succ`, `mg1Mean_eq`). With the second definition the condition is `β < 0`; both say `Σⱼ j q(j) < 1`, which is the form proved (`proposition_10_3_1`, with `mg1Mean`). An invariant probability has `π(0) = 1 − Σⱼ j q(j)`, the book's `π(0) = −β` (`mg1_invariant_prob_zero`). The proposition is true in either reading, so there is no counterexample. |
| Proposition 10.4.8, p. 245 | "Suppose that `ν` is an invariant probability measure supported on the set `A` with `∫_A ν(dx) U_A(x, B) = ν(B)` for `B ⊆ A`." | The proof, the calculation (10.30), uses only the displayed identity. `proposition_10_4_8` holds for every measure `ν`, neither a probability nor supported on `A`; only `ν` restricted to `A` enters `ν°`. The book's statement is a special case, so there is no counterexample. |
| Citations, pp. 242, 245, 247 | The proof of Theorem 10.4.4 cites "Theorem 8.2.4"; the proof of Theorem 10.4.7 cites "Proposition 10.4.3"; the proof of Theorem 10.4.10 cites "the criterion in Theorem 9.1.7". | Proposition 8.2.4 (`proposition_8_2_4`, carried), Theorem 10.4.3 (`theorem_10_4_3`) and Proposition 9.1.7 (`proposition_9_1_7_ii`, carried) are meant. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| The whole chapter | `B(X)` is countably generated, the standing assumption on a general state space. | Assumed (Mathlib's `MeasurableSpace.CountablyGenerated`) only for Theorem 10.4.4 and what depends on it, since the proof uses the small sets of Theorem 5.2.2 through `theorem_5_2_3_resolvent` (carried): `theorem_10_4_4`, `IsRecurrentChain.isInvariant_of_isSubinvariantMeasure`, `IsRecurrentChain.exists_eq_smul`, `invMeasure` and its lemmas, `theorem_10_4_5`, `theorem_10_4_5_positive`, `theorem_10_4_9_equiv`, `ae_hitProb_eq_one`, `theorem_10_4_9`, `theorem_10_4_9_path`, `theorem_10_4_9_path'`, `theorem_10_0_1`, `theorem_10_4_10_i`, `theorem_10_4_10_i_forall`, `theorem_10_4_10_ii`, `theorem_10_0_1_finite`, `IsPositive.invariant_prob_unique`, `eq_stationaryDist`, `IsPositive.eq_smul_stationaryDist` and `isPositive_iff_invMeasure_univ`. §§10.1–10.2, §10.4.2, Propositions 10.4.1–10.4.2, Theorem 10.4.3, `theorem_10_4_10_i_of_exists` and the definition `stationaryDist` do not assume it. The models live on `ℕ`, `ℝ`, `ℕ × ℕ`, `ℕ × ℝ` and `ℝⁿ`, which are countably generated. |
| Theorem 10.4.5, p. 243 | For a ψ-irreducible aperiodic chain, `π` is invariant for the `m`-skeleton iff it is invariant for `Φ`. | The proof uses the uniqueness of the invariant measure of the `m`-skeleton, which is Theorem 10.4.4 for `Pᵐ` and needs `Pᵐ`, and hence `Φ`, to be recurrent. `theorem_10_4_5` assumes recurrence, a σ-finite `π` and `m ≥ 1`. The positivity statement needs no recurrence, since positive chains are recurrent (`theorem_10_4_5_positive`). |
| (10.2), (10.31), pp. 230, 246 | For every `A ∈ B⁺(X)`. | For `A ∈ B⁺(X)` with `π(A) < ∞` (`theorem_10_0_1`, `theorem_10_4_9`, `theorem_10_4_9_path`, `theorem_10_4_9_path'`), the standing assumption `0 < μ(A) < ∞` of §10.4.2, on which Theorem 10.4.7 rests. Such sets exist, since `π` is σ-finite and equivalent to `ψ`. |
| Proposition 10.1.2, p. 233 | `Φ` is ψ-irreducible. | Any irreducibility measure `ψ` (`IsPhiIrreducible`, carried), not necessarily maximal. Part (iv) needs no irreducibility. |
| Theorem 10.2.1, p. 234 | `Φ` is ψ-irreducible and `α` is an accessible atom. | (i) and the uniqueness in (ii) take an accessible atom (`IsAccessibleAtom`, carried, which includes a maximal `ψ` with `ψ(α) > 0`). The minimality in (ii) and part (iii) hold for any atom (`theorem_10_2_1_ii`, `theorem_10_2_1_iii`). The measure `μ°_α` is defined from a point `a ∈ α` (`atomMeasure`); it does not depend on the point (`IsAtom.tabooPotKernel_eq`). |
| Proposition 10.2.3, p. 236 | A positive recurrent irreducible chain on a countable space. | A countable space with measurable singletons and a positive chain whose maximal irreducibility measure charges every point (`proposition_10_2_3`, `proposition_10_2_3_unique`). |
| The forward recurrence time chain, §10.3.1, p. 236 | A renewal distribution `p` on `{1, 2, …}`, with states `{1, 2, …}`. | `p` is a probability on `ℤ₊` with `p(0) = 0`, and the states are `ℤ₊` with renewal state `0`, the book's `1` (`fwdRecKernel`, carried). The formula (10.16) becomes `π(j) = Σ_{n > j} p(n)` (`fwdRecInv`). Where the general theory is used (irreducibility, recurrence of the chain, positivity, `fwdRecInv_eq_atomMeasure`), `p` has unbounded support, without which the states above the support are not reached and the chain is not irreducible for counting measure. The invariance of `π` (`isInvariant_fwdRecInv`) and of `π ⊗ π` for the linked chain (`isInvariant_linkedFwdRec`) need only `p(0) = 0`. |
| The M/G/1 queue, §10.3.2, p. 238 | `N*` is ψ-irreducible if `q₀ > 0` and irreducible if also `q₀ + q₁ < 1`, "and we shall assume this to be the case". | `proposition_10_3_1` assumes `q(0) ≠ 0` and takes a maximal irreducibility measure `ψ` as a hypothesis. The computations (`mg1_cut_of_invariant`, `mg1_invariant_prob_zero`, `isInvariant_mg1Seq`) need only `q(0) ≠ 0`, and so does the uniqueness of p. 238 (`mg1_invariant_unique`, `mg1_invariant_unique_smul`), which is stated for invariant measures finite on points. |
| The GI/M/1 queue, §10.3.3, p. 239 | `N` is ψ-irreducible if `p₀ + p₁ < 1` and irreducible if also `p₀ > 0`; "assume these inequalities hold". | `proposition_10_3_2` assumes `p(0) > 0` and takes a maximal irreducibility measure `ψ` as a hypothesis; `proposition_10_3_2_unique` assumes the chain positive and `s ∈ (0, 1)` a root of (10.25). The recurrent case `proposition_10_3_2_mean_one` assumes `p(0) > 0` and that `{0}` is an accessible atom (`IsAccessibleAtom`, carried); `gim1Alpha_eq_one_of_mean_le` assumes `p(0) > 0` and a maximal irreducibility measure. The invariance statements `isInvariant_gim1_geom` and `isInvariant_gim1_one`, (10.24) (`gim1_minimal_geom`) and the minimality of `s_α` (`gim1Alpha_root`, `gim1Alpha_le_of_root`) need no irreducibility. |
| (10.4), p. 232 | `Pμ(Xₙ ∈ A) → γ_μ(A)` for all `A`, for any starting distribution `μ`. | `μ` is a probability and the convergence is setwise on measurable sets (`isInvariant_of_tendsto`). |
| Proposition 10.5.2, p. 248 | Random walk on `ℝ` with spread-out increments of mean zero and finite variance; `A`, `B`, `C` bounded, `μ^{Leb}(A) > 0`, `μ^{Leb}(C) > 0`. | `proposition_10_5_2` assumes the walk recurrent and `0 < μ^{Leb}(A) < ∞` in place of boundedness; `B` is any measurable set, and the ratio form (`proposition_10_5_2_ratio`) is read in `[0, ∞]`. `proposition_10_5_2_spreadOut` takes the book's conditions on `Γ` and assumes the chain ψ-irreducible for a maximal `ψ`, as the book does implicitly; recurrence then follows from Propositions 6.3.2 and 9.4.5 and Theorem 9.2.2. |
| §10.5.2, p. 248 | The renewal process on `ℝ₊` of §3.5. | The increment law `Γ` lives on `[0, ∞)` and is not concentrated at `0`, and `δ ≥ 0` (`isInvariant_fwdSkelInv`); the normalisation needs `m = ∫ t Γ(dt) < ∞` (`isProbabilityMeasure_fwdSkelInv_normalised`). |
| Theorem 10.5.3, p. 249 | The ladder chain (10.37) with rungs a general space `X`, positive Harris with `ψ([0]) > 0`; `π₀` is the invariant probability of the process on `[0]`. | The rungs are `ℝ` (`ladderChainKernel Λ Λ*` on `ℕ × ℝ`, carried), and the kernel is a Markov kernel. `theorem_10_5_3` is stated for a recurrent chain with `ψ([0]) > 0` and an invariant measure `π` with `π([0]) < ∞`; `π₀` is `π` restricted to `[0]` and seen on `ℝ`. The kernel identities (10.39), (10.40), (10.44)–(10.51) need no irreducibility. |
| Theorem 10.5.4, p. 252 | The GI/G/1 ladder chain, under the standing assumption of §10.5.3 (positive Harris, `ψ([0]) > 0`). | `H` is a probability and `G` is s-finite, and the ladder kernel is a Markov kernel (an instance argument; it is one when service and interarrival times are nonnegative and services are not concentrated at `0`, `isMarkovKernel_gig1Ladder_of_pos`, carried). The direction "`π̃` finite ⇒ `π̃` invariant" needs no irreducibility (`theorem_10_5_4_invariant`); the converse and the form of `π` assume recurrence and `ψ([0]) > 0` (`theorem_10_5_4_eq`, `theorem_10_5_4`). |
| §10.5.4, pp. 252–253 | (LSS1)–(LSS2), the eigenvalue condition (LSS5), and "`W` has a finite mean". | `Γ` is a probability on `ℝᵖ`, `F` satisfies (LSS5) (`IsStableMatrix`, carried), and `E‖W‖ < ∞` is `∫⁻ ‖v‖ₑ dΓ ≠ ∞` (`ae_summable_lssSeries`, `isInvariant_lssLimitLaw`). |
| §10.5.4, p. 253 | The Gaussian case (LSS3). | For the scalar model with `N(0, σ²)` noise and `|α| < 1` (`isInvariant_ar1_gaussian_stable`); for any `α`, `N(0, v)` is invariant when `v = α²v + σ²` (`isInvariant_ar1_gaussian`). Variances are in `ℝ≥0`, as in Mathlib's `gaussianReal`. |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 10.2.1 (ii), p. 235 | Uniqueness: if `μ ≠ μ°_α`, a set `A` with `μ(A) > μ°_α(A)` and `Pⁿ(w, α) > 0` for all `w ∈ A` gives `1 = μ(α) > μ°_α(α) = 1`. | Such a set needs an extra exhaustion step. The proof compares `∫ μ(dx) K_{a_{1/2}}(x, α)` with `∫ μ°_α(dx) K_{a_{1/2}}(x, α)`, both at most `μ(α) = 1`, through `eq_of_le_of_lintegral_le` (`μ₀ ≤ μ`, `∫ f dμ ≤ ∫ f dμ₀ < ∞`, `0 < f < ∞` force `μ = μ₀`); this needs no σ-finiteness of `μ` (`theorem_10_2_1_ii_unique`). |
| (10.16), p. 237 | `π(j) = U₁(1, j) = Σ_{n ≥ j} p(n)` from `_1Pⁿ(1, j) = p(j + n − 1)`. | `π` is shown invariant directly (`isInvariant_fwdRecInv`), and `π = U₀(0, ·)` follows from the uniqueness in Theorem 10.2.1 (`fwdRecInv_eq_atomMeasure`, through `theorem_10_2_1_ii_unique`), which the book mentions as the alternative. The taboo formula itself is proved separately, for every `j` (`fwdRec_tabooKernel`). |
| Proposition 10.3.1, (10.21), pp. 238–239 | "Formally summing" the system (10.20). | Necessity: summing the cut equations of an invariant probability (`mg1_sum_cut`) gives `π(0) = 1 − Σⱼ j q(j)` (`mg1_invariant_prob_zero`). Sufficiency: the solution `mg1Seq` of the cut equations with `π(0) = 1`, built recursively, has partial sums bounded by `β'/(1 − β')`, `β' = Σⱼ j q(j)` (`mg1Seq_partial_le`, `mg1Seq_tsum_le`), and the cut equations imply the invariant equations (`isInvariant_mg1Seq`). |
| Proposition 10.3.2, (10.22)–(10.25), pp. 239–241 | `μ°_α(k) = s_αᵏ` from the last-exit decomposition (10.22) and translation invariance (10.23), with `s_α` the minimal root of (10.25), "and one can then verify directly" the invariant equations. | Both routes are formalised. The book's: (10.22)–(10.23) are not proved for the GI/M/1 chain itself; it is realised as a ladder chain with one-point rungs (`gim1LadderKernel`, `gim1Ladder_eq_map`, `tabooKernel_map_of_comp`), whose last-exit decomposition (`ladderS_succ`, `ladderS_eq_pow`) gives `μ°_α(k) = s_αᵏ` (`gim1_minimal_geom`), and whose minimality result `ladS_minimal` makes `s_α` the minimal root of (10.25) (`gim1Alpha_root`, `gim1Alpha_le_of_root`). The direct verification: if `s < 1` solves (10.25), `sᵏ` is invariant (`isInvariant_gim1_geom`, through `gim1_col_succ` and `gim1_col_zero`), and a root in `(0, 1)` exists when `p(0) > 0` and `Σ j p(j) > 1` (`exists_gim1_root`). If `Σ j p(j) ≤ 1`, `μ ≡ 1` is subinvariant (`isSubinvariant_gim1_one`) with infinite mass, so by uniqueness (`IsPositive.eq_smul_stationaryDist`) the chain is not positive (`proposition_10_3_2`), and then `s_α = 1` (`gim1Alpha_eq_one_of_mean_le`). For `Σ j p(j) = 1` the recurrence comes from `μ°_α(α) = 1` rather than from §9.1 (`proposition_10_3_2_mean_one`). |
| Theorem 10.4.5, p. 243 | `π = m⁻¹ Σ_{k < m} πₘPᵏ` is invariant for `P`, and the uniqueness of `πₘ` for `Pᵐ` gives `πₘ = π`. | The `m`-skeleton is recurrent (`theorem_8_2_6_ii`, carried); `πₘ` and the invariant measure of `P` are both subinvariant for `Pᵐ`, so `πₘ` is a multiple of the latter (`IsRecurrentChain.exists_eq_smul` for `Pᵐ`), hence invariant for `P` (`theorem_10_4_5`). |
| Theorem 10.4.7 (i), pp. 244–245 | (10.28), and then a second proof of (i) by contradiction through the resolvent. | (10.28) alone, which needs only `μ(A) < ∞` (`theorem_10_4_7_i`). |
| Theorem 10.4.9, p. 246 | `π = π°_A` "for any Harris recurrent set `A`" by Theorem 10.4.7. | For every `A ∈ B⁺(X)` with `π(A) < ∞`: `L(·, A) = 1` holds `π`-almost everywhere, because the Harris decomposition (`theorem_9_1_5`, carried) leaves a `ψ`-null, hence `π`-null, set (`ae_hitProb_eq_one`); Theorem 10.4.7 makes `π°_A` invariant, and uniqueness and `π°_A(A) = π(A)` give `π°_A = π` (`theorem_10_4_9`). |
| Proposition 10.5.1, p. 248 | No finite invariant measure, from Theorem 10.4.9. | Lebesgue measure is σ-finite and invariant (`isInvariant_volume_randomWalk`); for a positive chain it would be a finite multiple of `stationaryDist` (`IsPositive.eq_smul_stationaryDist`), and so finite (`proposition_10_5_1`). |
| (10.36), pp. 248–249 | The sandwich `F[y, ∞) dy ≤ U_{[0, δ]}(x, dy) ≤ F[y − δ, ∞) dy`, the uniqueness argument along `δ/2ⁿ`, and then "by direct integration". | Direct integration only. Exactly one renewal interval straddles each `s > 0` (`tsum_straddle`, `tsum_prod_straddle`), which gives `P^δ(x, A)` as a series (`fwdSkelKernel_apply_eq_tsum`) and the core identity `∫_{(0, δ]} F[x, ∞) P^δ(x, B) dx = ∫_{[0, δ)} Γ(B + r) dr = ∫_B Γ[y, y + δ) dy` (`fwdSkel_core`, `lintegral_shift_window`), from which `F[y, ∞) dy` is invariant for every `δ ≥ 0` (`isInvariant_fwdSkelInv`). |
| Theorem 10.5.4, p. 252 | "`π` is the minimal subinvariant measure ... and the result is then obvious." | Sufficiency through Proposition 10.4.8 with `ν = δ₀ ⊗ H` on the bottom rung (`gig1Bottom`): every entrance to `[0]` has the law `H` (`gig1_entrance`, `tabooPotKernel_rung_zero_of_entrance`), and finiteness of `π̃` gives `E_{(0, y)}[τ_{[0]}] < ∞`, hence a sure return, for `H`-almost every `y`; so `ν°` is invariant and equals `π̃` (`gig1_minimal_apply`, `theorem_10_5_4_invariant`). The form of `π` follows from Theorem 10.5.3 with `π₀ = π([0]) H` (`theorem_10_5_4_eq`). |
| §10.5.4, pp. 252–253 | `Pᵏg(x₀) → E[g(X_∞)]` by dominated convergence, then `π_∞(Pg) = π_∞(g)` for bounded continuous `g` through the Feller property. | The identity `X_∞(v, W₀, W₁, …) = G v + F X_∞(W₀, W₁, …)` on the event of absolute convergence (`lssSeries_cons`), together with the independence of `W₀` and `(W₁, W₂, …)` under `Γ^{⊗ℕ}` (`infinitePi_map_head_tail'`), shows `π_∞P = π_∞` (`isInvariant_lssLimitLaw`). No limit and no Feller property are used. |

## Conventions

* Transition laws are Mathlib's kernels, and `Pⁿ` is the kernel power. `μP` is `P ∘ₘ μ`, so
  `IsInvariant P μ` is `P ∘ₘ μ = μ` and `IsSubinvariant P μ` is `P ∘ₘ μ ≤ μ`, both without
  σ-finiteness; `IsInvariantMeasure` and `IsSubinvariantMeasure` add `SigmaFinite μ`, as the book's
  definitions do. Measures and kernels take values in `[0, ∞]` (`ℝ≥0∞`), so "`μ(A) < ∞`" is
  `μ A ≠ ∞` and "`c` finite" is `c ≠ ∞`.
* "`Φ` is ψ-irreducible" is `IsMaximalIrreducibility P ψ` (carried) in `IsPositive`, `IsNull`,
  `IsRecurrentChain` and `IsAccessibleAtom`; Proposition 10.1.2 uses `IsPhiIrreducible P ψ`.
  `A ∈ B⁺(X)` is `MeasurableSet A ∧ 0 < ψ A`. A positive chain is `IsPositive P ψ`, a null chain
  `IsNull P ψ`, a positive Harris chain `IsPositiveHarris P ψ`.
* `E_x[τ_A]` is `meanReturnTime P A x`, the integral of the first return time `τ_A ≥ 1`
  (`firstReturn`, carried) under `P_x`, with `τ_A = ∞` counted as `∞`. `U_A` is
  `tabooPotKernel P hA`, `_APⁿ` is `tabooKernel P hA`, `L(x, A)` is `hitProb P A x`, `U` is
  `potKernel P`, `K_a` is `sampledKernel P a`, `K_{a_ε}` is `resolvent P ε`, and
  `Āᶜ = {L(·, A) = 0}` is `noHitSet P A` (all carried).
* `μ°_A` of (10.27) is `minimalMeasure P hA μ = U_A ∘ₘ μ|_A`, for every measurable `A`. `μ°_α` of
  (10.10) is `atomMeasure P hα a = U_α(a, ·)`, for a point `a ∈ α`. `invMeasure P h` is a chosen
  nonzero invariant measure of a recurrent chain, and `stationaryDist P h` the invariant
  probability of a positive chain.
* The split chain of a minorization `M : Minorization P` (carried) is `M.splitKernel` on `X × Bool`,
  `μ*` is `M.split μ`, and `π̌(A₀ ∪ A₁)` in (10.26) is the marginal `π̌ ∘ Prod.fst⁻¹`. The
  `m`-skeleton is `P ^ m`.
* `ℤ₊` is `ℕ`. A measure on `ℕ` given by weights `m` is `pointMeasure m = Σₓ m(x) δₓ`, and
  transition matrices are `matKernel` of an `IsTransitionMatrix` (carried). The forward recurrence
  time chain is `fwdRecKernel p` (carried) with renewal state `0`; the linked chain is
  `linkedFwdRec p`. The M/G/1 and GI/M/1 chains are defined directly from the matrices on
  pp. 238–239, `mg1Matrix q` and `gim1Matrix p`, with weights `q, p : ℕ → ℝ≥0∞`; the book's
  `q̄_j = Σ_{n > j} qₙ` is `qTail q (j + 1)`, and `Σⱼ j q(j)` is `mg1Mean q`.
* The ladder chain is `ladderChainKernel Λ Λ*` on `ℕ × ℝ` (carried); `[k] = {k} × ℝ` is `rung k`
  and the levels above `k` are `aboveRung k`. `S^{(k)}` is `ladderS Λ Λ* k`, `S = S^{(1)}` is
  `ladS Λ Λ*`, `Q` is the chain killed at `[0]`, `ladL Λ Λ* 0`, and the partial sums of (10.47)
  are `ladSN`. Mathlib's kernel composition `η ∘ₖ κ` is "first `κ`, then `η`", so the book's
  `S^{(k)}S` is `ladS Λ Λ* ∘ₖ ladderS Λ Λ* k` and `Σₖ SᵏΛₖ` is
  `Kernel.sum fun k => Λ k ∘ₖ (ladS Λ Λ* ^ k)`. `π₀` is `(π.restrict (rung 0)).map Prod.snd`. For the GI/G/1 queue the ladder chain is
  `gig1Ladder H G` (carried) and `π̃` of (10.52) is `gig1Tilde H G`.
* Random walk on `ℝ` is `randomWalkKernel Γ`, Lebesgue measure is Mathlib's `volume`, and the
  uniform distribution on `A` is `uniformOn A`. The forward recurrence time `δ`-skeleton is
  `fwdSkelKernel Γ δ` (carried), with `F[y, ∞) = Γ[y, ∞)`, and `F[y, ∞) dy` on `(0, ∞)` is
  `fwdSkelInv Γ`. The scalar linear model is `ar1Kernel Γ α` and the linear state space model is
  `lssMatrixKernel Γ F G` (carried); `X_∞` is `lssSeries F G` on the noise path space
  `(ℕ → ℝᵖ, Measure.infinitePi)`, and `π_∞` is `lssLimitLaw Γ F G`.
* The carried modules are copied from `HarrisRecurrence` and `PseudoAtoms` without change apart
  from the namespace and the rename of `isProbabilityMeasure_convPow` in `SpecificKernels` (see
  the [README](../README.md)). The corrections they contain belong to Chapters 1–6, 8 and 9, are
  recorded in their module docstrings and in those projects, and are not repeated here.

## Not formalised

* **The guess of (10.36)** (p. 248): the sandwich `F[y, ∞) dy ≤ U_{[0, δ]}(x, dy) ≤ F[y − δ, ∞) dy`,
  its normalised form, and the uniqueness argument through `V⁺_δ` as the two-step chain of
  `V⁺_{δ/2}` along `δ/2ⁿ`. (10.36) itself is verified directly.
* **The convergence `Pᵏg(x₀) → E[g(X_∞)]`** for the linear model (pp. 252–253), and the
  representation of `X_k` in law that precedes it. The invariance of `π_∞` is proved by a direct
  identity.
* **The aperiodicity remarks** (10.18) (p. 237), with Lemma D.7.4, and the ψ-irreducibility and
  positive Harris property of the linked chain `V*` (pp. 237–238), which need them. The product
  invariant measure and its total mass are proved.
* **The multivariate Gaussian case of §10.5.4** (p. 253): `π = N(0, Σ)` with the controllability
  grammian, the density (10.54) under (LCM3), and the singular case. The scalar Gaussian case is
  proved.
* **§10.6**, the commentary (pp. 253–255), including the kernels `U^{(r)}` and (10.55)–(10.57).
* **Informal remarks.** The opening of the chapter on transient chains (p. 229); stationary
  processes (p. 230); the interpretation of an infinite invariant measure (p. 230); the remark that
  the limit in (10.4) does not depend on `μ` when the invariant probability is unique (p. 232),
  which follows from `isInvariant_of_tendsto` and `eq_stationaryDist`; the skip-free remark after
  Proposition 10.3.1 (p. 239); the interpretation of `s_α` as the mean number of visits to `k + 1`
  from `k` for every `k` (p. 241), where `gim1Alpha` is the case `k = 0`; the process on `A` as a
  chain (p. 245); the interpretation of (10.31) (p. 246); the interpretation of `F[y, ∞) dy`
  (p. 249); the remark on general rungs (p. 249); and the forward references to Chapters 11–13
  and 19.
