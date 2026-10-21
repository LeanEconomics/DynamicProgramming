# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. Five of the claims below are
refuted in Lean by a counterexample, and for each of them a corrected statement is proved. For the
other entries the table says why no counterexample is given. The last section lists what is not
formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Proposition 8.3.1 (ii), p. 183 | If `L(x, A) = 1` for all `x ∈ A`, then `A` is recurrent. If `Φ` is ψ-irreducible, then `A ∈ B⁺(X)` and `U(x, A) ≡ ∞`. | The first sentence is proved (`proposition_8_3_1_ii`). The second fails for `A = ∅`: the hypothesis holds vacuously, but `ψ(∅) = 0` (`proposition_8_3_1_ii_counterexample`). For non-empty `A` it holds (`proposition_8_3_1_ii_irreducible`). |
| Theorem 8.3.6 (i), p. 186 | `Φ` is recurrent if there is a petite set `C` with `L(x, C) ≡ 1` for `x ∈ C`; "we do not assume that `C` is in `B⁺(X)`, but this follows also". | The empty set is petite and satisfies the hypothesis vacuously, so as stated the theorem would make every ψ-irreducible chain recurrent. The random walk on `ℤ₊` with `Γ = ⅓δ₋₁ + ⅔δ₁` (mean `⅓ > 0`) is ψ-irreducible and not recurrent (`theorem_8_3_6_i_counterexample`). For non-empty `C` the theorem holds, and `C ∈ B⁺(X)` (`theorem_8_3_6_i`). |
| Theorem 8.4.3, p. 190 | If `C` is petite and `V` is unbounded off petite sets with `ΔV ≤ 0` on `Cᶜ` (V1), then `L(x, C) ≡ 1` and `Φ` is recurrent. The proof assumes "without loss of generality" that `C ∈ B⁺(X)`, replacing `C` by `C ∪ C_V(n)`. | The enlargement proves `L ≡ 1` only for the enlarged set. The claim `L(x, C) ≡ 1` fails for `C = ∅`: on the one-point space with the identity kernel and `V = 0`, `∅` is petite, every `C_V(n)` is petite, (V1) holds, and `L(x, ∅) = 0` (`theorem_8_4_3_counterexample`). It holds for `C ∈ B⁺(X)`, and petiteness of `C` is not needed for it (`lemma_8_4_3_hitProb`). The recurrence conclusion holds as stated (`theorem_8_4_3`, `theorem_8_0_2_ii`). |
| Proposition 8.4.6, p. 192 | If the increment law `Γ` on `ℤ` has bounded range and mean `β`, the random walk on `ℤ₊` is recurrent iff `β ≤ 0`. | For `Γ = δ₀` the mean is `0`, but the walk never moves, `{0}` and `{1}` are disjoint absorbing sets, and the walk is ψ-irreducible for no `ψ ≠ 0`, so it is not recurrent for any `ψ` (`proposition_8_4_6_counterexample`). Without `Γ(−∞, 0) > 0` the walk on `ℤ₊` is never irreducible. With `Γ(w) > 0` for some `w < 0` the statement holds for every maximal irreducibility measure (`proposition_8_4_6`), and one exists (`rwhl_exists_maximal`). |
| The renewal equation, p. 175 | `u(n) := Σ_{k ≥ 0} P(Z_k = n) = 1 + u ∗ p(n)`. | This holds only at `n = 0`. For `p = δ₁` the renewal times are `Z_k = k`, so `u ≡ 1`, but `1 + u ∗ p(1) = 2` (`renewal_equation_counterexample`). The equation is `u = δ₀ + u ∗ p` (`renewal_equation`), which is what (8.12), `U(z) = [1 − P(z)]⁻¹`, encodes (`genFun_renewalSeq`). |
| Theorem 8.4.2, (8.41), p. 188 | `Φ` is transient iff there are a bounded `V : X → ℝ₊` and `r ≥ 0` with `C_V(r)`, `C_V(r)ᶜ ∈ B⁺(X)` and `ΔV(x) > 0` for `x ∈ C_V(r)ᶜ`. | The sufficiency proof uses only `ΔV ≥ 0`. For the converse the book's function `V(x) = 1 − P_x(σ_C < ∞)` has `ΔV = 0` off `C` (Proposition 8.4.1; `drift_one_sub_hitProbZero`), so the converse it proves is the one with `ΔV ≥ 0`, and Proposition 8.4.5, the book's own application, uses `ΔV = 0` (8.51). `theorem_8_4_2` is proved with `ΔV ≥ 0`, the form of Theorem 8.0.2 (i) (`theorem_8_0_2_i`). The strict form of the converse is neither proved nor refuted here, so there is no counterexample. |
| Proposition 8.2.2, p. 180 | If `Φ` is ψ-irreducible and strongly aperiodic, then `Φ` and `Φ̌` are both recurrent or both transient. The proof uses the accessible atom `α̌` of the split chain. | `α̌` is accessible only when the small set of the minorization lies in `B⁺(X)` (Theorem 5.1.3 (ii)), which the statement does not assume. The book's proof is formalised with that hypothesis added (`Minorization.proposition_8_2_2`, `proposition_8_2_2_stronglyAperiodic`). The conclusion holds for every minorization, by a different argument that uses Theorem 8.3.4 (`Minorization.proposition_8_2_2_general`), so there is no counterexample. |
| Proposition 8.3.2, p. 184 | "Hence if `A` is uniformly transient, there is a countable covering of `A` by uniformly transient sets." | As printed this is trivial: `A` covers itself. The proof shows that `Ā = {x : L(x, A) > 0}`, the set from which `A` is accessible, is covered by the uniformly transient sets `Ā(m)`; this is what is proved (`proposition_8_3_2_cover`) and what Theorems 8.3.4 and 8.2.1 use. The printed statement is true, so there is no counterexample. |
| (8.29), proof of Theorem 8.2.6 (i), p. 182 | If `Σⱼ P^{jm}(x, A) ≤ M` for `x ∈ A`, then `Σ_{j ≥ 1} Pʲ(x, A) = Σ_{r=1}^m ∫ Pʳ(x, dy) Σⱼ P^{jm}(y, A) ≤ mM`. | The inner sum includes `j = 0`, and `M` bounds the skeleton's `U_m(·, A)` only on `A`; by Proposition 8.3.1 (i) it is at most `1 + M` elsewhere, so the bound is `m(2 + M)`. `potKernel_le_skeleton` takes the bound `M` on all of `X` and gives `m(1 + M)`. The conclusion, that `A` is uniformly transient for `Φ`, is unaffected, so there is no counterexample. |
| Theorem 8.3.5, p. 186 | If `Φ` is ψ-irreducible and transient, every petite set is uniformly transient. | No irreducibility is needed: if `X` is covered by uniformly transient sets, the petite measure of `C` charges one of them, `B`, and `C ⇝ᵃ B` gives `C` uniformly transient by Proposition 8.3.2 (`theorem_8_3_5`). The theorem is true, so there is no counterexample. |
| Proposition 8.5.4, (8.58), p. 195 | The test function is `V(x) = log(1 + x)` for `x > R` and `0` on `[0, R]`, with `R` chosen large. | The cut-off is not needed: `V(x) = log(1 + x)` on all of `ℝ₊` satisfies (V1) off `C = [0, x₁]` for a large `x₁` (`proposition_8_5_4`). The theorem is true, so there is no counterexample. |
| Proposition 8.5.5, p. 196 | "We can assume without loss of generality that `Γ(−∞, 0) > 0`": if `Γ[0, ∞) = 1` the chain is not irreducible, "and it is transient in every meaning of the word". | Transience in the sense of §8.2.3 requires ψ-irreducibility. If `Γ[0, ∞) = 1` every irreducibility measure is `0` (`rwhl_not_irreducible_of_nonneg`), so the walk is neither transient nor recurrent for any `ψ` (`rwhl_not_transient_of_nonneg`). So the conclusion fails for every such `Γ`, for instance `δ₁`, which is skip-free with `β = 1`. The book's proof sets these walks aside, and the hypothesis `Γ(−∞, 0) > 0` is kept (`proposition_8_5_5`, `proposition_8_5_5_mean`); the point is recorded as a missing hypothesis rather than as a separate counterexample. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| The whole chapter | `B(X)` is countably generated, the standing assumption on a general state space. | Assumed (Mathlib's `MeasurableSpace.CountablyGenerated`) only where it is used: Theorem 8.2.5 (the minorization for the resolvent, `theorem_5_2_3_resolvent`), Theorem 8.2.6 (ψ-irreducibility of the skeletons, `proposition_5_4_5_iii`), Proposition 8.3.8 (the cycles, `exists_isPeriod`) and (8.43) (finite unions of petite sets, `proposition_5_5_5_ii`). No other result assumes it; in particular Theorems 8.0.1, 8.0.2, 8.3.4–8.3.6 and 8.4.3 do not. |
| Lemma 8.5.2, p. 194 | `E[log(s + tW)I{W ∈ A}] ≤ ⋯` for any `A ⊆ {s + tw > 0}`. | The left side is defined only if `log(s + tW)` is integrable on `A`; `lemma_8_5_2` assumes this, and that `W` and `W²` are integrable, since the right side contains `E[W; A]` and `E[W²; ⋯]`. |
| Theorem 8.1.5, (8.14), §8.5, pp. 176, 193–197 | `Γ` has mean zero; `β` is "well defined and finite"; `W` has finite variance; `β = Σ_w wΓ(w) > 0`. | Moments are stated as integrability: `w ↦ w` integrable for `Γ` with integral `0` (`theorem_8_1_5`, `randomWalk_wlln`), `w ↦ w` integrable (`proposition_8_5_1`), `w ↦ w²` integrable (`lemma_8_5_3_i`, `lemma_8_5_3_ii`, `proposition_8_5_4`), and `w ↦ wΓ(w)` summable (`proposition_8_5_5_mean`). `proposition_8_5_5` is stated with `Σₙ n Γ(1 − n) < 1`, which `skipFree_mean_lt_one` derives from `β > 0`. |
| Propositions 8.4.4–8.4.6, pp. 191–192 | `Γ` has bounded range: `Γ(x) = 0` for `\|x\| > r`. | The range is an explicit `r` with `Γ(w) = 0` for `\|w\| > r`, and the mean is the finite sum `rwMean Γ r = Σ_{\|w\| ≤ r} Γ(w) w`. The walk on `ℤ` is irreducible in the sense of `IsIrreducibleChain`, and recurrence and transience are for counting measure (`proposition_8_4_4`, `proposition_8_4_5`); Proposition 8.4.6 holds for every maximal irreducibility measure. |
| Propositions 8.5.1, 8.5.4, 8.5.5, pp. 193–195 | "Clearly the chain is `δ₀`-irreducible." | The conclusion is stated for every maximal irreducibility measure `ψ`, taken as a hypothesis. One exists when `Γ(−∞, 0) > 0` (`halfLine_maximal`, `rwhl_exists_maximal`), which follows from `β < 0` (`halfLine_neg_pos_of_mean_neg`) and from `β = 0` with `E[W²] > 0` (`halfLine_neg_pos_of_mean_zero`). |
| Proposition 8.1.1, Theorem 8.1.2, Proposition 8.1.4, pp. 173–175 | `X` is countable and `Φ` is irreducible. | `X` is countable with measurable singletons, and irreducibility is `IsIrreducibleChain` (carried). Proposition 8.1.3 and (8.15) need only measurable singletons (`proposition_8_1_3`, `sum_pow_le_sum_pow_zero`). |
| Proposition 8.4.1, p. 187 | The minimal non-negative solution of (8.39). | The solutions range over `h : X → [0, ∞]`. |
| (V1), Theorems 8.0.2 (ii) and 8.4.3, pp. 172, 189–190 | A positive function `V`. | `V : X → ℝ≥0`, measurable; non-negativity suffices. Theorem 8.0.2 (i) and Theorem 8.4.2 take a bounded measurable `V : X → ℝ` with `V ≥ 0`, and `sup_C V` is the real `sSup` of `V(C)`. |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Proposition 8.3.1, pp. 183–184 | (i) from (8.25) as `z ↑ 1`; (ii) and (iii) from the last-exit decomposition (8.26) with `U^{(z)}`; (iv) by the induction (8.34) on `P_x(η_A ≥ km)`. | The first-entrance equation `U(x, A) = E_x[1 + U(Φ_{τ_A}, A); τ_A < ∞]` comes from the strong Markov property at `τ_A` (`potKernel_eq_firstReturn`). (i) follows directly, with the sharper `U(x, A) ≤ L(x, A)(1 + M)`. (ii): `m = inf_A U(·, A)` satisfies `1 + m ≤ m`, so `m = ∞`. (iii) and (iv) bound the truncated occupation times `η_A^N`, whose expectations are finite and play the role of `U^{(z)}`: at the first return (`lintegral_occTimeN_le_hitProb`) and at the `k`-th return, through the pathwise bound `η_A^N ≤ k + η_A^N ∘ θ^{τ_A(k)}` (`occTimeN_le_returnTimeK`). |
| (8.18), (8.19), (8.25), (8.26), pp. 178–179 | The decompositions are summed with weights `zⁿ` to give (8.25)–(8.26). | Both decompositions are proved as equalities on path space, from the Markov property at fixed times (`firstEntrance_decomposition`, `lastExit_decomposition`), and summed directly at `z = 1`, where every term is non-negative (`potKernel_firstEntrance`, `potKernel_lastExit`). |
| Proposition 8.1.3 and atoms, pp. 174–175, 179 | From (8.10)–(8.11) as `z ↑ 1`. | For an atom, `L(a, α) = 1` gives `U = ∞` by Proposition 8.3.1 (ii), and `L(a, α) < 1` gives `U(x, α) ≤ (1 − L(a, α))⁻¹` by Proposition 8.3.1 (iii), since `L(·, α)` is constant on `α` (`IsAtom.potKernel_eq_top_iff`, `IsAtom.isUniformlyTransient`). Proposition 8.1.3 is the case of a singleton. |
| Theorem 8.2.1 (ii), pp. 179–180 | The cover `α(j)` with `U(x, α) ≥ j⁻² U(x, α(j))`. | The cover `Ā(m)` of Proposition 8.3.2 (`isTransientChain_of_uniformlyTransient`). |
| Lemma 8.2.3, p. 181 | Generating functions and uniqueness of power series. | The coefficients are computed directly: `K_{a_ε}ⁿ⁺¹ = Σ_k (1 − ε)ⁿ⁺¹ εᵏ C(n + k, k) Pᵏ` (`resolvent_pow_eq`) and `Σₙ C(n + k, k) rⁿ = (1 − r)^{−(k+1)}` in `[0, ∞]` (`tsum_choose_mul_pow`). |
| Theorem 8.3.4, p. 185 | The sets `A_r(M)` of (8.38) cover `X`. | Once `A_r ∈ B⁺(X)` is uniformly transient, `X` is covered by the sets `Ā_r(m)` of Proposition 8.3.2 (`isTransientSet_univ_of_uniformlyTransient`). |
| Theorem 8.3.5, p. 186 | Proposition 5.5.5 (iii): a petite `C` satisfies `C ⇝ᵃ B` for every `B ∈ B⁺(X)`. | The petite measure of `C` charges one of the covering uniformly transient sets (`theorem_8_3_5`), so neither Proposition 5.5.5 (iii) nor irreducibility is used. |
| Theorem 8.3.6 (ii), converse, p. 186 | A petite `C ∈ B⁺(X)` with `D = {y ∈ Cᶜ : L(y, C) < 1}` non-empty, which needs the existence of small sets (Theorem 5.2.2). | `C` is a uniformly transient set in `B⁺(X)`, which every transient chain has (`IsTransientChain.exists_uniformlyTransient`), and `D = {L(·, C) < 1}` (`theorem_8_3_6_ii`); no countable generation is needed. The form with `D ⊆ Cᶜ`, used for Theorem 8.4.2, is `IsTransientChain.exists_compl_hitProb_lt_one`. |
| Theorem 8.2.6 (ii), p. 182 | A skeleton is classified by Theorem 8.2.5. | By Theorem 8.3.4 (`theorem_8_2_6_ii`). |
| Theorem 8.4.3, (8.44)–(8.50), p. 190 | By contradiction from transience, through the kernel `P̃` absorbed in `C` and the uniform transience of `C_V(M)`. | Direct, for `C ∈ B⁺(X)`. For the killed kernel `P I_{Cᶜ}` (`killedKernel`), (V1) gives `∫ (P I_{Cᶜ})ⁿ(x, dy) V(y) ≤ V(x)` (`lintegral_killedKernel_pow_le`). A petite `C_V(M)` reaches `C` with probability at least some `δ > 0` (`IsPetite.hitProb_ge`), so if `L(x, C) < 1` the tail `P_x(n < τ_C < ∞)` (`lintegral_killedKernel_hitProb`), which tends to `0`, would be bounded below (`lemma_8_4_3_hitProb`). Recurrence then follows from Proposition 8.3.1 (ii) and Theorems 8.3.4–8.3.5, with `C ∪ C_V(n)` in `B⁺(X)` (`theorem_8_4_3`). |
| Propositions 8.4.5 and 8.4.6, p. 192 | Proposition 8.4.5 for `β < 0` "by symmetry"; transience in Proposition 8.4.6 by stochastic comparison with the walk on `ℤ`. | One test function `V(x) = (1 − sˣ)⁺` serves both signs of the mean in Proposition 8.4.5, the root `s` of (8.53) for `β < 0` coming from the case `β > 0` by `s ↦ s⁻¹` (`exists_root_of_mean_ne_zero`). Transience in Proposition 8.4.6 is proved on `ℤ₊` itself by the drift argument with `V(x) = 1 − ρˣ`, which has `ΔV = 0` for `x > r` (`isTransientChain_of_drift`). |
| Theorem 8.1.5, (8.14)–(8.17), pp. 176–177 | The weak law of large numbers is quoted without proof; (8.16)–(8.17) take `lim inf` as `N → ∞`. | (8.14) is derived from Mathlib's strong law (Mathlib's `ProbabilityTheory.strong_law_ae`) through convergence in measure (Mathlib's `MeasureTheory.tendstoInMeasure_of_tendsto_ae`), in the form `Pⁿ(0, {\|y\| ≤ an}) ≥ ½` for large `n` (`randomWalk_wlln`). The `lim inf` argument is replaced by a finite one: if `U(0, 0) < ∞`, then for `a = 1/(8(1 + U(0, 0)))`, `M = ⌈aN⌉` and large `N`, `(N − k₀)/2 ≤ Σ_{n ≤ N} Pⁿ(0, [−M, M]) ≤ (2M + 1)(1 + U(0, 0))`, which is impossible (`theorem_8_1_5`). |
| Proposition 8.5.4, (8.59)–(8.61), p. 195 | `U₁(x) = o(x⁻²)` by Lemma 8.5.3. | The explicit bound `E[W; W > −x] = −E[W; W ≤ −x] ≤ E[W²; W ≤ −x]/x`, with `V(x) = log(1 + x)` on all of `ℝ₊` (`proposition_8_5_4`). |
| Proposition 8.5.5, (8.63)–(8.69), pp. 196–197 | The generating functions `V*(z)` and `Γ*(z)` for `0 < z < 1`, the analytic expansion (8.65), and Abel's theorem for `Σ bⱼ = [1 − Σ n aₙ]⁻¹`. | `bₘ` is the renewal sequence of the defective sequence `cⱼ = Σ_{n>j} aₙ`, and `V(x) = Σ_{m<x} bₘ` (`skipFreeV`). (8.63) is proved by comparing coefficients of formal power series over `[0, ∞]` (Mathlib's `PowerSeries`; `skipFree_harmonic`), so no convergence is needed, and `Σₘ bₘ = (1 − Σₙ n aₙ)⁻¹` is (8.12) at `z = 1` (`tsum_renewalSeq_skipFree`), where every term is non-negative, so no Abel theorem is needed. Transience then follows from the drift argument (`isTransientChain_of_drift`). |

## Conventions

* Transition laws are Mathlib's kernels, and `Pⁿ` is the kernel power. `P_x` is the carried
  `pathKernel P x` on `ℕ → X`, `θⁿ` is `shift n`, and `𝓕ₙ^Φ` is `natFilt n`. `U` is the carried
  `potKernel P = Σ_{n ≥ 1} Pⁿ`, `η_A` is `occTime A`, `τ_A` is `firstReturn A`, `σ_A` is
  `firstHit A`, `τ_A(k)` is `returnTimeK A k`, and `L(x, A)` is `hitProb P A x`.
  `_APⁿ(x, B) = P_x(Φₙ ∈ B, τ_A ≥ n)` is `tabooProb P A n x B`; as a kernel, `_APⁿ⁺¹` is
  `tabooKernel P hA n`, and `U_A` is `tabooPotKernel P hA`. `K_a` is `sampledKernel P a`,
  `K_{a_ε}` is `resolvent P ε` with `a_ε(n) = (1 − ε)εⁿ`, `K_{a_{1/2}}` is `resolventHalf`, and `B ⇝ᵃ A` is
  `SampledAccessible P a B A`. All of these are carried.
* `U`, `L`, occupation times and generating functions take values in `[0, ∞]` (`ℝ≥0∞`), so
  "`U(x, A) < ∞`" is `U(x, A) ≠ ∞`, and the generating functions `genFun` are defined for every
  `z ∈ [0, ∞]`.
* "`Φ` is ψ-irreducible" is `IsMaximalIrreducibility P ψ` (carried): `ψ ≠ 0` is a maximal
  irreducibility measure, as in the book's convention. `IsRecurrentChain P ψ` and
  `IsTransientChain P ψ` include it, and `A ∈ B⁺(X)` is `MeasurableSet A ∧ 0 < ψ A`. Absorbing sets,
  petite sets, small sets, atoms and cycles are the carried `IsAbsorbing`, `IsPetite`, `IsSmallSet`,
  `IsAtom` and `IsCycle`; aperiodicity is `IsAperiodic`.
* On a countable space, irreducibility is the carried `IsIrreducibleChain`, and the recurrence and
  transience of §8.2.3 are taken for counting measure (Mathlib's `Measure.count`), which is then a
  maximal irreducibility measure (`isMaximalIrreducibility_count`, carried). States are classified
  through `U(x, {y})`.
* The split chain of a minorization `M : Minorization P` (carried) is `M.splitKernel` on
  `X × Bool`, the split atom `α̌ = C₁` is `M.checkAlpha`, and the split measure `ψ*` is `M.split ψ`.
* The drift (8.1) is `drift P V`, for `V : X → [0, ∞]`, with values in `EReal`; the drift of a
  bounded real `V` is `driftR P V`. The killed kernel `P I_{Cᶜ}` is `killedKernel P hC`.
* The random walks on `ℤ` and `ℤ₊` with bounded range are `matKernel (rwMatrix Γ)` and
  `matKernel (rwhlMatrix Γ)` (carried), with `Γ : ℤ → [0, ∞]` summing to `1`; `ℤ₊` is `ℕ`. The walk
  on `ℤ` of Theorem 8.1.5 is `randomWalkKernel Γ` for a probability measure `Γ` on `ℤ`, and the walk
  on `ℝ₊` is `halfLineWalkKernel Γ` on `ℝ≥0` for a probability measure `Γ` on `ℝ` (carried).
* The forward recurrence time chain is the carried `fwdRecKernel p` on `ℕ`, whose state `0` is the
  book's state `1`.
* The renewal sequence `u` and the convolution powers `p^{∗k}` are `renewalSeq p` and
  `renewalPow p k`, with `p^{∗0} = δ₀` (`diracDist 0`, carried) and convolution `sampleConv`
  (carried).
* The carried modules are copied from `TopologyContinuity` without change apart from the
  namespace. The corrections they contain belong to Chapters 1–6, are recorded in their module
  docstrings and in those projects, and are not repeated here.

## Not formalised

* **The generating-function identities in `z`**: (8.8)–(8.11) and (8.20)–(8.26) for `|z| < 1`.
  They are proof devices; the forms at `z = 1` are proved (`potKernel_firstEntrance`,
  `potKernel_lastExit`, and (8.22), (8.24) through the carried `potKernel_apply` and
  `hitProb_eq_tsum`), and the results derived from them are proved by the arguments above.
* **The almost-sure statement of p. 173**, that `L(x, A) = 1` on `A` gives `η_A = ∞` almost surely
  from `A`. This is Harris recurrence, the subject of Chapter 9; the expectation form is
  Proposition 8.3.1 (ii).
* **Forward references**: the converse of Theorem 8.0.2 (ii) for Feller chains (§9.4.2, p. 173);
  Harris recurrence for general chains (pp. 175, 182); stochastic comparison (§9.5.1, p. 192);
  transience of random walk with `β > 0` and unbounded range (Proposition 9.1.2, p. 195); and the
  stronger recurrence for negative mean (Chapter 11, p. 198).
* **Proof devices replaced by other arguments**: the generating functions `V*(z)`, `Γ*(z)`, the
  analytic expansion (8.65) and Abel's theorem in Proposition 8.5.5; the kernel `P̃` and the
  contradiction argument (8.44)–(8.50) in Theorem 8.4.3; the cut-off test function (8.58) and the
  estimates (8.59)–(8.61) in Proposition 8.5.4; the covers `α(j)` of Theorem 8.2.1 and `A_r(M)`
  of (8.38); see "Proofs that differ from the book" above.
* **§8.6**, the commentary (pp. 197–198).
* **Informal remarks.** The overview of the chapter and its history (pp. 171–173); the
  identification of the renewal equation with (8.11) (p. 176); the remark that exceptional sets
  need not be empty (p. 187); the motivation for petite sets and test functions (pp. 189, 191);
  the remark that Theorem 8.1.5 appears difficult to prove by drift methods (p. 192); the
  application to queueing and storage models (p. 193).
