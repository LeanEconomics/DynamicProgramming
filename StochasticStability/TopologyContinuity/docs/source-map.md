# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 6, pp. 123–145. Equation numbers and assumption labels are the book's. Lean
names are relative to `MeynTweedie.TopologyContinuity`; names from Mathlib are marked as such.
Names marked "carried" are in the modules copied from the Chapter 1–5 projects (see the
[README](../README.md)). Each result states the topological hypotheses it uses; they are listed in
[corrections](corrections.md), together with every place where the Lean statement departs from the
book.

## Chapter 6 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 123 | `X` is a locally compact, separable, metrizable space with its Borel σ-field | Not assumed globally: `X` carries a topology and a σ-algebra containing the open sets (`OpensMeasurableSpace`, or `BorelSpace` where stated), and each result adds what it uses; see [corrections](corrections.md) |
| p. 123 | Lower semicontinuity: `liminf_{y→x} h(y) ≥ h(x)`; the indicator of an open set is lower semicontinuous | Mathlib's `LowerSemicontinuous`; `lowerSemicontinuous_indicator_of_isOpen`, `lowerSemicontinuous_const_mul`, `lowerSemicontinuous_of_seq`, `le_liminf_seq_of_lsc` |
| p. 124, (i) | `P` is (weak) Feller if `P(·, O)` is lower semicontinuous for every open `O` | `IsWeakFeller` |
| p. 124, (ii) | A continuous component of `K_a`: a substochastic `T` with `K_a(x, A) ≥ T(x, A)` and `T(·, A)` lower semicontinuous for every `A ∈ B(X)` | `IsContinuousComponent` (`IsSubstochasticKernel`, `sampledKernel`, carried) |
| p. 124, (iii) | `Φ` is a T-chain if some `K_a` has a continuous component `T` with `T(x, X) > 0` for all `x` | `IsTChain` (`a` a sampling distribution, `IsSamplingDist`, carried) |
| Theorem 6.0.1, p. 124 | (i) A T-chain with `L(x, O) > 0` for all `x` and all open `O` is ψ-irreducible; (ii) if every compact set is petite then `Φ` is a T-chain, and conversely every compact set is petite for a ψ-irreducible T-chain; (iii) a ψ-irreducible Feller chain with `supp ψ` of non-empty interior is a ψ-irreducible T-chain | `theorem_6_0_1` (on a locally compact second-countable metrizable space; (i) for non-empty open `O`) |
| (6.1)–(6.2), p. 124 | The chain on `[0, 1]` with `P(n⁻¹, (n + 1)⁻¹) = 1 − αₙ`, `P(n⁻¹, 0) = αₙ`, and `P(x, 1) = 1` for `x ≠ n⁻¹` | `recipKernel` on `ℝ`, with the points `recipSet` and the laws `recipStep`; `recipKernel_apply_recip`, `recipKernel_apply_of_notMem`, `isMarkovKernel_recipKernel`, `recip_injective`, `zero_notMem_recipSet` |
| pp. 124–125 | The chain is irreducible if every `αₙ > 0`; the Feller property fails at `0` | `recipKernel_not_weakFeller_irreducible` (not weak Feller for any `α`; `δ₀`-irreducible when every `αₙ > 0`) |
| pp. 124–125 | It fails to visit most open sets; it is unstable if `Σ αₙ < ∞`; every continuous component property fails if `αₙ → 0` | Not formalised (informal) |

## §6.1.1 Weak and strong Feller chains

| Source | Claim | Lean |
| --- | --- | --- |
| (6.3), p. 125 | `Ph(x) = ∫ P(x, dy) h(y)` | The Bochner integral `∫ y, h y ∂P x`, or the lower integral for `h ≥ 0` |
| p. 125 | `P` is strong Feller if it maps all bounded measurable functions to `C(X)` | `IsStrongFeller` |
| Proposition 6.1.1 (i), p. 125 | `P` is weak Feller iff `P` maps `C(X)` to `C(X)`; `P` is strong Feller iff `P I_A` is lower semicontinuous for every `A ∈ B(X)` | `proposition_6_1_1_i_weak` (pseudo-metrizable space), `proposition_6_1_1_i_strong` (first-countable space); `IsStrongFeller.isWeakFeller` |
| p. 126 | Proof of (i): `f_N = N⁻¹ Σ I_{O_k} ↑ f`, and Theorem D.4.1 | Replaced by Fatou's lemma for lower semicontinuous integrands: `lintegral_ofReal_le_liminf`, `lintegral_le_liminf_of_lsc`, `IsWeakFeller.lowerSemicontinuous_lintegral` (first-countable space). The strong part: `continuous_apply_of_lsc`, `continuous_integral_of_nonneg` (the layer-cake formula) |
| Proposition 6.1.1 (ii), p. 125 | For a weak Feller chain, a closed `C` and a non-decreasing `m : ℤ₊ → ℤ₊`, `Eₓ[m(τ_C)]` is lower semicontinuous; hence so are `Pₓ{τ_C ≥ n}`, `Eₓ[τ_C]` and `Eₓ[r^{τ_C}]`, `r > 1` | `proposition_6_1_1_ii` (`m : ℕ → ℝ≥0` non-decreasing, `m(∞) = sup m`), `proposition_6_1_1_ii_tail`, `proposition_6_1_1_ii_mean`, `proposition_6_1_1_ii_geom` (`r ≥ 1`); `tailProb`, `extendSup`, `expectReturn`; `firstReturn` (carried) |
| p. 126 | `Eₓ[m(τ_C)] = Σᵢ Δm(i) Pₓ{τ_C ≥ i}` for `m(0) = 0` | `expectReturn_eq_tsum` (with the term `m(0)`), from `extendSup_eq_tsum` and `sum_increments_eq`; `withTop_le_iff_not_succ_le` |
| p. 126 | `Pₓ{τ_C ≥ k} = (P I_{Cᶜ})^{k−1}(x, X)`, approximated by `(P I_{fᵢ})^{k−1}(x, X)` with continuous `fᵢ ↑ I_{Cᶜ}` | `tailProb_succ` (the first-step recursion), `tailProb_zero`, `tailProb_one`. The approximation is not needed: by induction on `k`, `IsWeakFeller.lowerSemicontinuous_lintegral` applies to the lower semicontinuous integrand `y ↦ 1_{Cᶜ}(y) P_y(τ_C ≥ k + 1)` |
| Proposition 6.1.1 (iii), p. 125 | For a weak Feller chain and open `O`, `Pₓ{τ_O ≤ n}`, `K_a(x, O)` and `L(x, O)` are lower semicontinuous | `proposition_6_1_1_iii` (first-countable space; `K_a` for every `a`); `hitWithin`, `hitWithin_zero`, `hitWithin_succ`, `hitWithin_le_one`, `hitProb_eq_iSup_hitWithin`, `measurableSet_firstReturn_le`; `hitProb` (carried). The book omits the proof |
| p. 125, used p. 132 | `Pⁿ` and `K_a` inherit the Feller property; `K_a(·, C)` is upper semicontinuous for compact `C` | `IsWeakFeller.pow`, `IsWeakFeller.lsc_sampledKernel`, `IsWeakFeller.isWeakFeller_sampledKernel`; for every closed set: `usc_of_lsc_compl`, `IsWeakFeller.usc_pow_closed`, `IsWeakFeller.usc_sampledKernel_closed` |
| Proposition 6.1.2, p. 127 | NSS(F), with `F` smooth on an open `X ⊆ ℝⁿ`, is weak Feller | `proposition_6_1_2` (state space a second-countable real normed space; also `Ph` continuous for bounded continuous `h`); `nssKernel` (carried) |
| (6.4), p. 127 | Proof: `x ↦ F(x, w)` is continuous, so `Ph(x) = ∫ Γ(dw) h ∘ F(x, w)` is continuous by dominated convergence | `isWeakFeller_recursionKernel`: every random recursion with `x ↦ F(x, w)` continuous for each `w` is weak Feller, on any first-countable space (Fatou's lemma in place of dominated convergence); `recursionKernel` (carried) |
| p. 127 | NSS(F) is weak Feller because CM(F) is continuous in the state; Chapter 7 exploits this | Not formalised (remark and forward reference) |
| Proposition 6.1.3, p. 127 | The unrestricted random walk is weak Feller, and strong Feller iff `Γ ≪ μ_Leb` | `proposition_6_1_3`; `randomWalkKernel` (carried) |
| (6.5)–(6.6), pp. 127–128 | `Ph(x) = ∫ h(y + x) Γ(dy)`; with a density, `Ph = γ ∗ h` is continuous by Lemma D.4.3 | Lemma D.4.3 is replaced by the continuity of translation in measure: `translateMap`, `lsc_translate_of_finite`, `lsc_translate` (`t ↦ ν{w : t + w ∈ B}` is lower semicontinuous for finite `ν ≪ μ`, `μ` a Haar measure on a finite-dimensional space), from Mathlib's `tendsto_measure_symmDiff_preimage_nhds_zero` |
| (6.7), p. 128 | If the walk is strong Feller and `Γ(B) = δ > 0`, then `P(x, B) ≥ δ/2` near `0` | In the proof of `proposition_6_1_3` |
| p. 128 | `∫ μ_Leb(dy) Γ(A − y) = μ_Leb(A)` by Fubini and translation invariance; hence `μ_Leb(B) ≥ δ μ_Leb(O)/2` and `μ_Leb ≫ Γ` | `lintegral_translate_volume`; the conclusion is the converse half of `proposition_6_1_3` |

## §6.1.2 Strong Feller chains and open set irreducibility

| Source | Claim | Lean |
| --- | --- | --- |
| p. 128, (i) | `x` is reachable if `Σₙ Pⁿ(y, O) > 0` for every `y` and every open `O ∋ x` | `IsReachable`, with the sum over `n ≥ 1`: `U(y, O) > 0` (`potKernel`, carried) |
| p. 128, (ii) | `Φ` is open set irreducible if every point is reachable | `IsOpenSetIrreducible` |
| Lemma 6.1.4, p. 129 | If `Φ` is ψ-irreducible, `x*` is reachable iff `x* ∈ supp ψ` | `lemma_6_1_4` (`ψ` a maximal irreducibility measure; `supp ψ` is Mathlib's `Measure.support`). False for the zero measure, which is an irreducibility measure: `lemma_6_1_4_counterexample` |
| p. 129 | On a countable space with the discrete topology, open set irreducibility is irreducibility | `isOpenSetIrreducible_iff_irreducible` (discrete topology, measurable singletons, non-empty `X`; countability is not needed); `IsIrreducibleChain` (carried) |
| p. 129 | Open set irreducibility and ψ-irreducibility both say that "large" sets are reached from everywhere | Not formalised (remark) |
| Proposition 6.1.5, p. 129 | A strong Feller chain with a reachable point `x*` is ψ-irreducible with `ψ = P(x*, ·)` | `proposition_6_1_5` |
| (6.8), p. 129 | `P^{n+1}(y, A) ≥ ∫_O Pⁿ(y, dz) P(z, A) > 0` | In the proof of `proposition_6_1_5` |
| Proposition 6.1.6, p. 129 | An open set irreducible strong Feller chain is ψ-irreducible | `proposition_6_1_6` (non-empty `X`; a nonzero irreducibility measure) |
| p. 129 | Propositions 6.1.5–6.1.6 hold for T-chains; the T-chain route and the e-chain route | Propositions 6.2.1–6.2.2 below; the comparison is not formalised (remark) |

## §6.2.1 T-chains and open set irreducibility

| Source | Claim | Lean |
| --- | --- | --- |
| p. 130 | Every random walk is weak Feller, and a walk with increments concentrated on the rationals is not ψ-irreducible | `randomWalk_rational_weakFeller_not_irreducible` (weak Feller, and irreducible for no nonzero measure), with `randomWalk_rational` (carried) |
| p. 130 | Such a walk enters every open set | Not formalised. It needs a condition on `Γ`: for `Γ = δ₀` the walk never moves |
| p. 130 | T-chains include virtually all models; `T` may ignore discontinuities of `P` | Not formalised (remark) |
| Proposition 6.2.1, p. 130 | A T-chain with a reachable point `x*` is ψ-irreducible with `ψ = T(x*, ·)` | `proposition_6_2_1` (for any continuous component `T` of any `K_a`; non-triviality is not needed) |
| p. 130 | Proof: `K_{a_ε ∗ a}(y, A) ≥ ∫_O K_{a_ε}(y, dw) T(w, A) > 0`, by "Proposition 5.5.2" | `hitProb_pos_of_pow_sampled` (if `Pⁿ⁺¹(y, ·)` charges `{K_a(·, A) > 0}` then `L(y, A) > 0`). The book's reference is to Lemma 5.5.2 |
| Proposition 6.2.2, p. 130 | An open set irreducible T-chain is a ψ-irreducible T-chain | `proposition_6_2_2` (non-empty `X`; a nonzero irreducibility measure) |

## §6.2.2 T-chains and petite sets

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 6.2.3, p. 131 | If an open `ν_a`-petite set `A` exists, `K_a` has a continuous component non-trivial on `A`, namely `T(x, B) = I_A(x) ν(B)` | `proposition_6_2_3`; `IsPetiteSet` (carried) |
| Proposition 6.2.4, p. 131 | If every `x` has `aₓ` and a continuous component `Tₓ` of `K_{aₓ}` non-trivial at `x`, then `Φ` is a T-chain | `proposition_6_2_4` (second-countable space) |
| p. 131 | Proof: Lindelöf's Theorem D.3.1 gives a countable cover by the open sets `{Tᵢ(·, X) > 0}`; `T = Σ 2⁻ᵏ Tₖ`, `a = Σ 2⁻ᵏ aₖ` | Lindelöf through second countability. `mixKernel`, `mixKernel_apply`, `mixSampling`, `sampledKernel_mixSampling`, `isSamplingDist_mixSampling` (weights `2^{−(k+1)}`, `k ≥ 0`) |
| Theorem 6.2.5 (i), p. 131 | If every compact set is petite, `Φ` is a T-chain | `theorem_6_2_5_i` (locally compact second-countable space); `IsPetite` (carried) |
| p. 131 | Proof: "since `X` is σ-compact", there is a countable cover by open petite sets | Local compactness: the interior of a compact neighbourhood of `x` is an open petite set containing `x`, and Propositions 6.2.3–6.2.4 apply |
| Theorem 6.2.5 (ii), p. 131 | If `Φ` is a ψ-irreducible T-chain, every compact set is petite; so is every compact set of an open set irreducible T-chain | `theorem_6_2_5_ii` (for any nonzero irreducibility measure; Hausdorff space, countably generated σ-algebra), `theorem_6_2_5_ii_openSet` |
| pp. 131–132 | Proof: `K_{a∗a_ε}(x, A) ≥ T K_{a_ε}(x, A) > 0` with `A ∈ B⁺(X)` petite, bounded below on compact sets, and Proposition 5.2.4 | `lsc_lintegral_of_lsc_sets` (`T(·, f)` is lower semicontinuous for measurable `f ≥ 0`); a small set from `theorem_5_2_2`, `lemma_5_5_2_i`, and Proposition 5.5.4 (i) for petite sets in place of Proposition 5.2.4 (`proposition_5_5_4_i`, `proposition_5_5_3`, carried) |
| Proposition 6.2.6, p. 132 | For a ψ-irreducible T-chain, `K_b(x, B) ≥ s(x) ψ_b(B)` with `s` continuous and everywhere positive and `ψ_b` maximal | `proposition_6_2_6` (pseudo-metrizable space, countably generated σ-algebra), from `proposition_5_5_5_iii` (carried) |
| p. 132 | Proof: `T(·, s)` is positive and lower semicontinuous, so it dominates an everywhere positive continuous function | `exists_continuous_pos_le_of_lsc` (`s(x) = inf_y (min(h(y), 1) + d(x, y))`), with `lsc_lintegral_of_lsc_sets` |

## §6.2.3 Feller chains, petite sets, and T-chains

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 6.2.7, p. 132 | For a ψ-irreducible Feller chain, the closure of every petite set is petite | `lemma_6_2_7` (pseudo-metrizable space, Borel σ-algebra, countably generated) |
| pp. 132–133 | Proof: `A` is petite iff `K_a(x, C) ≥ δ` on `A` for a compact petite `C` (inner regularity by compact sets); `K_a(·, C)` is upper semicontinuous, so the bound extends to `Ā` | A closed small set `D` in place of the compact `C`: inner regularity by closed sets of a finite measure on a pseudo-metrizable space, applied to a small set from `theorem_5_2_2`, after `proposition_5_5_5_i` (carried) makes the minorizing measure maximal. Then `IsWeakFeller.usc_sampledKernel_closed` and `proposition_5_5_4_i` (carried) |
| Proposition 6.2.8 (i), p. 133 | For a ψ-irreducible Feller chain with an open petite `A`, `ψ(A) > 0`, all compact sets are petite | `proposition_6_2_8_i` (metrizable space; any irreducibility measure with `ψ(A) > 0`). `K_{a_{1/2}}(·, A)` is lower semicontinuous and positive, so it has a positive minimum on a compact set; `resolventHalf`, `proposition_4_2_1` (carried) |
| Proposition 6.2.8 (ii), p. 133 | The same if `supp ψ` has non-empty interior | `proposition_6_2_8_ii` (metrizable, locally compact, countably generated) |
| p. 133 | Proof: `A_k = closure{K_{a_ε}(x, A) ≥ 1/k} ∩ supp ψ` are petite; `supp ψ` is of the second category, so some `A_k` contains an open set | The closed sets `closure{K_{a_{1/2}}(x, A) ≥ 1/(k + 1)}` are petite by Lemma 6.2.7 and cover `X`; the Baire category theorem (Mathlib's `BaireSpace.of_t2Space_locallyCompactSpace`, `dense_iUnion_interior_of_closed`) gives an open subset of one of them inside the interior of `supp ψ`, which has positive `ψ`-measure |
| Theorem 6.2.9, p. 133 | A ψ-irreducible weak Feller chain with `supp ψ` of non-empty interior is a T-chain, "as a corollary of Proposition 6.2.8 (ii) and Proposition 6.2.5 (ii)" | `theorem_6_2_9` (locally compact, second-countable, metrizable), from `proposition_6_2_8_ii` and Theorem 6.2.5 (i) (`theorem_6_2_5_i`); the book's reference should be to Theorem 6.2.5 (i) |
| p. 133 | An open cover by petite sets would make every ψ-irreducible Feller chain a T-chain; this is not the case | `feller_not_tChain_counterexample` below |
| p. 133 | `X = [0, 1]`, `0 < \|α\| < 1`, `P(x, {0}) = 1 − P(x, {αx}) = x` for `x > 0`, `P(0, {0}) = 1`: the chain is Feller and `δ₀`-irreducible but not a T-chain | `feller_not_tChain_counterexample` for `α = 1/2`, on `ℝ` with `P(x, {0}) = min(\|x\|, 1)` (see [corrections](corrections.md)); `jumpKernel`, `jumpProb`, `jumpProb_mem`, `continuous_jumpProb`, `jumpKernel_apply`, `isMarkovKernel_jumpKernel`, `lintegral_jumpKernel`, `integral_jumpKernel`, `jumpKernel_pow_succ_apply`, `jumpKernel_pow_zero_zero`, `jumpKernel_isWeakFeller` |
| p. 133 | `lim_{x→0} Pₓ(τ_{0} ≥ n) = 1`, so no open petite set contains `0` | Replaced by `jumpKernel_half_pow_le` (`Pⁿ(x, {0}) ≤ n\|x\|`). A continuous component `T` of `K_a` has `T(0, {0}) = T(0, X) > 0`, since `0` is absorbing, so `K_a(x, {0}) ≥ T(x, {0})` is bounded below near `0`; but `K_a(2⁻ʲ, {0}) → 0` |

## §6.3.1 Random walks

| Source | Claim | Lean |
| --- | --- | --- |
| p. 134 | For most irreducible examples `supp ψ` has non-empty interior | Not formalised (remark) |
| Proposition 6.3.1, p. 134 | Random walk on a half line with `Γ(−∞, 0) > 0` is a ψ-irreducible T-chain | `proposition_6_3_1` (`δ₀`-irreducible), from `proposition_4_3_1`, `halfLine_isSmall_of_isCompact` (carried), `IsSmall.isPetite` and `theorem_6_2_5_i`; `halfLineWalkKernel` (carried) |
| p. 134 | The storage model with state-dependent release rule `r(x)` is a `δ₀`-irreducible T-chain when `R(x) < ∞` | Not formalised (the model is not constructed here) |
| Proposition 6.3.2, p. 134 | The unrestricted random walk is a T-chain iff it is spread out | `proposition_6_3_2`; `IsSpreadOut`, `convPow` (carried); `isProbabilityMeasure_convPow`, `randomWalkKernel_pow_apply'` (`Pⁿ(y, A) = Γ^{n∗}(A − y)`) |
| p. 134 | Proof, "if": `P^M(x, A) ≥ ∫_{A−x} γ(y) dy =: T(x, A)` is strong Feller and non-trivial | The component `η μ_Leb\|_E(A − x)`, from `exists_lebesgue_minorant` (carried), lower semicontinuous by `lsc_translate` |
| (6.9)–(6.10), pp. 134–135 | Proof, "only if": a Lebesgue-null `A` with `Γ^{n∗}(A) = 1` for every `n` gives `μ_Leb(A) ≥ δ μ_Leb(O) > 0` | In the proof of `proposition_6_3_2`, with `lintegral_translate_volume` |

## §6.3.2 Linear models as T-chains

| Source | Claim | Lean |
| --- | --- | --- |
| (6.11), p. 135 | `X_m = F^m X₀ + Σ_{i<m} Fⁱ G W_{m−i}` | `lss_position_split` (the form used in Proposition 6.3.5); the law of `Xₘ` is `lss_pow_eq` (carried) |
| (LSS4), p. 135 | `Γ` is nonsingular with respect to Lebesgue measure, with a non-trivial density | `¬ Γ ⟂ₘ volume` |
| Proposition 6.3.3, p. 136 | Under (LCM3) and (LSS4), the `n`-skeleton has an everywhere non-trivial continuous component, so `X` is a T-chain | `proposition_6_3_3` (any noise dimension `p`; component of `K_{δₙ} = Pⁿ`, `diracDist n`); `lssMatrixKernel`, `IsControllable` (carried) |
| (6.12)–(6.13), p. 136 | `Pⁿf(x₀) ≥ T f(x₀) = ∫ f(Fⁿx₀ + Cₙw) γ(w₁) ⋯ γ(wₙ) dw`, `T(x, X) = (∫ γ)ⁿ > 0` | In the proof of `proposition_6_3_3`: `T(x, A) = ν{v : Fⁿx + v ∈ A}` with `ν` the law of `Cₙ(W₁, …, Wₙ)` for the absolutely continuous part of `Γ`; `pi_mono_fin` |
| pp. 136–137 | Proof for scalar `W`: change of variables `vₙ = Cₙwₙ` with `\|Cₙ\| ≠ 0`, then Lemma D.4.3 and dominated convergence | Replaced: `ν` is absolutely continuous because `Cₙ` is onto (`range_ctrbMap_eq_top`, carried), and `lsc_translate` gives lower semicontinuity. No determinant is needed, so `p` is arbitrary |
| p. 137 | ARMA and its variations are T-chains when the noise is rich enough, since they have controllable realizations (Proposition 4.4.2) | For AR(k): `arKernel_isTChain`, from `proposition_4_4_2` and `arKernel_eq_lssMatrixKernel` (carried). ARMA is not formalised |
| p. 137 | A T-chain is obtained in general by restricting to a controllable subspace | Not formalised |

## §6.3.3 Linear models as ψ-irreducible T-chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 137 | The controllable Gaussian model is strong Feller, by (4.18), and so a ψ-irreducible T-chain with `T = P` | Not formalised ((4.18) is not formalised as a density) |
| (LSS5), p. 137 | The eigenvalues of `F` lie in the open unit disk | `IsStableMatrix` (the spectral radius of `F` as a complex matrix is less than `1`; its spectrum is the set of eigenvalues by Mathlib's `Matrix.mem_spectrum_iff_isRoot_charpoly`) |
| Lemma 6.3.4, (6.14), p. 137 | `log ρ(F) = lim n⁻¹ log ‖Fⁿ‖` for any matrix norm | `lemma_6_3_4` (`‖aᵏ‖^{1/k} → ρ(a)` in a complex Banach algebra, Gelfand's formula, Mathlib's `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`); `lemma_6_3_4_log` (the log form, for `ρ > 0`), `log_rpow_one_div` |
| (6.15), p. 137 | For `ρ₁ < ρ(F) < ρ₂` there is `c > 1` with `c⁻¹ ρ₁ⁿ ≤ ‖Fⁿ‖ ≤ c ρ₂ⁿ` | `lemma_6_3_4_bounds` (`0 ≤ ρ₁`, `c ≥ 1`), `lemma_6_3_4_upper`. False for `ρ₁ < 0`: `lemma_6_3_4_bounds_counterexample` |
| p. 137 | Under (LSS5), `Fⁿ → 0` geometrically | `isStableMatrix_geometric` (`‖Fᵏx‖ ≤ C rᵏ ‖x‖`, `r < 1`) |
| Proposition 6.3.5, p. 138 | Under (LSS4), (LSS5) and controllability, LSS(F, G) is a ψ-irreducible T-chain and every compact set is small | `proposition_6_3_5` (a nonzero irreducibility measure; every compact set is `IsSmall`) |
| p. 138 | Proof: `x* = Σ Fᵏ G w` with `w ∈ supp Γ`; `P^N(x₀, O) ≥ Γ(w + εB)^N > 0` uniformly on bounded sets, so `x*` is reachable and Proposition 6.2.1 applies | `lss_uniform_reach`, `lss_position_split`, `proposition_6_2_1`; `Γ.support` is Mathlib's `Measure.support` |
| p. 138 | Proof: a small `C` with `T(x*, C) > 0` (Theorem 5.2.2) makes a neighbourhood `O` of `x*` small, and every bounded set reaches `O` uniformly (Proposition 5.2.4) | In the proof of `proposition_6_3_5`, with `proposition_5_2_4_ii` and `proposition_5_2_4_i` (carried) |

## §6.3.4 The first-order SETAR model

| Source | Claim | Lean |
| --- | --- | --- |
| p. 138 | (SETAR1): `Xₙ = φ(j) + θ(j)Xₙ₋₁ + Wₙ(j)` for `Xₙ₋₁ ∈ Rⱼ = (r_{j−1}, rⱼ]`, with independent noise sequences | `setarKernel`, `setarRegime`, `setarKernel_apply'` (carried; `M = m + 1` regimes, independent regime noises) |
| (SETAR2), p. 139 | Each `W(j)` has a density positive on the whole real line | `Γⱼ ≪ μ_Leb` and `μ_Leb ≪ Γⱼ` |
| p. 139 | The model is not Feller, because of discontinuities at the thresholds | `setar_not_continuous` (carried: the SETAR map need not be continuous) |
| Proposition 6.3.6, p. 139 | Under (SETAR1)–(SETAR2), the SETAR model is a `μ_Leb`-irreducible T-chain | `proposition_6_3_6` (also: `μ_Leb` is a maximal irreducibility measure and every compact set is small; the thresholds need not be ordered) |
| p. 139 | Proof: near `rᵢ`, `Tᵢ(x, ·) = min(P'(rᵢ, ·), P(rᵢ, ·), P(x, ·))` is a continuous component; combine by Proposition 6.2.4 | Replaced by a one-step uniform reach: `x ↦ Γⱼ{w : φ(j) + θ(j)x + w ∈ C}` is lower semicontinuous (`lsc_translate`) and positive for a small `C ∈ B⁺(X)` (`theorem_5_2_2`), so a compact `K` reaches `C` in one step with probability bounded below, `K` is small (`proposition_5_2_4_i`), and Theorem 6.2.5 (i) applies |
| p. 139 | Weaker support conditions suffice | Not formalised (informal) |

## §6.4.1 e-Chains and dynamical systems

| Source | Claim | Lean |
| --- | --- | --- |
| p. 139 | `P` induces a map on `M`, the probability measures on `B(X)` | `pushPM` (`μ ↦ μP`), `pushPM_dirac` (`δₓP = P(x, ·)`), `integral_comp_measure` (`∫ f d(μP) = ∫ Pf dμ`) |
| p. 140 | Weak convergence: `∫ f dμₖ → ∫ f dμ∞` for every `f ∈ C(X)` | Mathlib's topology on `ProbabilityMeasure X` |
| (6.16), p. 140 | `d_m(μ, ν) = Σₖ \|∫ fₖ dμ − ∫ fₖ dν\| 2⁻ᵏ` for an appropriate `{fₖ} ⊂ C_c(X)` | `dmDist` (for a given sequence `fs` of bounded continuous functions), `term_le_dmDist`, `dm_terms_le` (for `‖fⱼ‖ ≤ 1`) |
| Proposition 6.4.1, p. 140 | `(P, M, d_m)` is a dynamical system iff `P` is weak Feller | `proposition_6_4_1` (`μ ↦ μP` is continuous in the topology of weak convergence; pseudo-metrizable space) |
| p. 140 | `P` is equicontinuous, and `Φ` an e-chain, if `{Pᵏf}` is equicontinuous on compact sets for each `f ∈ C_c(X)` | `IsEChain` |
| Proposition 6.4.2, (6.17), p. 141 | A Feller chain with `Pⁿ(x, ·) → π` weakly for every `x` is an e-chain | False: `proposition_6_4_2_counterexample`. Corrected: `proposition_6_4_2_corrected` (uniform convergence on compact sets to a continuous limit; pseudo-metrizable space) |
| p. 141 | Proof: the limit is continuous, so Ascoli's Theorem D.4.2 gives equicontinuity | Needs uniform convergence: `equicontinuousOn_of_tendstoUniformlyOn`. The counterexample, the doubling chain `jumpKernel 2`: `jumpKernel_two_pow_zero_eq_one`, `eq_dirac_of_apply_zero`, `jumpKernel_two_pow_one_ge`, `tentAtOne`, `continuous_tentAtOne`, `hasCompactSupport_tentAtOne`, `powPM` |
| p. 141 | Chains with good limiting behaviour are forced to be e-chains | Not formalised (remark; it rests on Proposition 6.4.2) |
| p. 141 | Lyapunov stability: `lim_{ν→μ} sup_k d_m(νPᵏ, μPᵏ) = 0` | `IsLyapunovStable`; `orbitPM` |
| Proposition 6.4.3, p. 141 | `Φ` is an e-chain iff `(P, M, d_m)` is stable in the sense of Lyapunov; "the proof is routine and we omit it" | `proposition_6_4_3` (locally compact second-countable Hausdorff space; `fⱼ` compactly supported, `‖fⱼ‖ ≤ 1`, approximating every compactly supported `f` with `‖f‖ ≤ 1`). The "if" direction without compact supports or local compactness: `proposition_6_4_3_of_lyapunov`. The proof: `eventually_forall_abs_integral_sub_lt` (a partition of unity), `exists_isCompact_measureReal_compl_lt`, `eventually_dist_lt_of_eChain` |

## §6.4.2 e-Chains and tightness

| Source | Claim | Lean |
| --- | --- | --- |
| (6.18), p. 141 | An invariant probability is a stationary point of `(P, M, d_m)` | Not formalised (definition used from Chapter 10) |
| p. 141 | Lagrange stability: every orbit `{μPᵏ}` is precompact in `M` | `IsLagrangeStable`; `orbitPM` |
| p. 142 | Bounded in probability: for each `x` and `ε > 0` a compact `C` with `liminf_k Pₓ{Φₖ ∈ C} ≥ 1 − ε` | `IsBoundedInProbability` |
| p. 142 | Boundedness in probability is tightness of `{Pᵏ(x, ·)}`; tight is precompact in `(M, d_m)` | `isTight_orbit_of_boundedInProbability` (every orbit `{μPᵏ}` is tight, for every initial law `μ`); Prokhorov's theorem from Mathlib (`isCompact_closure_of_isTightMeasureSet`, `isTightMeasureSet_of_isCompact_closure`) |
| Proposition 6.4.4, p. 142 | `Φ` is bounded in probability iff `(P, M, d_m)` is Lagrange stable | `proposition_6_4_4` (complete separable locally compact metric space) |
| p. 142 | `\|f\|_c = Σₖ 2⁻ᵏ sup_{C_k} \|f\|`; `d_c` gives uniform convergence on compact sets; for weak Feller `P`, `(P, C(X), d_c)` is a dynamical system | `C(X, ℝ)` with Mathlib's compact-open topology; `orbitCM` (the orbit `k ↦ Pᵏf` of a bounded continuous `f`) |
| p. 142 | By Ascoli's Theorem D.4.2, `(P, C(X), d_c)` is Lagrange stable iff every orbit is uniformly bounded and equicontinuous on compact sets | Mathlib's `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` for one direction; the converse half of Ascoli: `eventually_forall_dist_lt_of_isCompact` |
| Proposition 6.4.5, p. 142 | If `Φ` is bounded in probability, it is an e-chain iff `(P, C(X), d_c)` is Lagrange stable | `proposition_6_4_5` (weak Feller; metrizable, locally compact). Equicontinuity for every bounded continuous `f`: `eventually_dist_lt_of_eChain_bounded`, with `integral_bump_bounds`, `abs_integral_tail_le` |
| p. 142 | For weak Feller chains, the four stability notions pair up | Propositions 6.4.3–6.4.5; the summary is not stated separately |

## §6.4.3 Examples of e-chains

| Source | Claim | Lean |
| --- | --- | --- |
| (6.19), p. 143 | `X_{n+1}(x) − X_{n+1}(y) = α^{n+1}(x − y)` for the same noise path | `controlMap_ar1_sub`; `controlMap` (carried) |
| Proposition 6.4.6, p. 143 | The simple linear model with `\|α\| ≤ 1` is an e-chain | `proposition_6_4_6` (`{Pᵏf}` is equicontinuous on all of `ℝ`); `ar1Kernel` (carried) |
| p. 143 | The random walk on `ℝ` is an e-chain (`α = 1`) | `randomWalk_isEChain` |
| p. 143 | It is difficult to find a natural Feller chain that is not an e-chain | The doubling chain of `proposition_6_4_2_counterexample` is one |
| (6.20), pp. 143–144 | The multiplicative random walk `X_{k+1} = Xₖ W_{k+1}` on `ℝ₊` is Feller but not an e-chain; with `{0}` made open it is an e-chain | Not formalised (the book gives a sketch that uses Section 10.5.4) |
| p. 144 | Such pathologies are typical of non-e Feller chains | Not formalised (remark) |

## §6.5 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 144–145 | History of Feller chains, e-chains, continuous components and T-chains; random walks on groups and semigroups; Athreya and Pantula on the linear model; Chan et al. on SETAR; positive densities | Not formalised (commentary) |
