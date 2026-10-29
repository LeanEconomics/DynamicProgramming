# Corrections and conventions

This file lists the places where a Lean statement differs from the book: a claim corrected, a
hypothesis made explicit, a proof replaced, or a convention chosen. Two claims are false as
printed. Each is refuted in Lean by a counterexample of this project, and a corrected statement is
proved: Theorem 17.1.7 and Theorem 17.3.2. Further entries concern proofs. The split-skeleton proof
of Theorem 17.3.2 needs an aperiodicity that the theorem does not assume, and a Lean counterexample
shows that the step fails without it; the theorem itself holds for every Harris chain and is proved
by another route. The statement of Theorem 17.3.1 is garbled, and a step of its proof is wrong for
consecutive cycle sums. The argument of Proposition 17.1.6 does not reach the CLT, whose transfer is
proved separately. The book's statements are paraphrased. The last section lists what is not
formalised.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 17.1.7, p. 427 | For a chain with an invariant probability `π`, (i) positive Harris recurrence, (ii) the LLN for every `f ∈ L¹(π)` from every state, and (iii) `P_x`-triviality of the invariant σ-field `Σ` for every `x`, are equivalent. | (iii) does not imply (i). `theorem_17_1_7_counterexample` is the identity chain on `Bool` (`Kernel.id`, Mathlib) with the invariant probability `δ_true`: each `P_x` is a point mass on path space, so every event has `P_x`-probability `0` or `1`, but the chain is irreducible for no nonzero measure and so is not positive Harris. The book's proof of (iii) ⇒ (i) asserts that `Q(·, A)` is constant, which needs triviality under mixtures of the `P_x` as well. The equivalence is proved with (iii) read as "every invariant event has `P_μ`-probability `0` or `1` for every initial law `μ`", the condition of Proposition 17.1.4 (`theorem_17_1_7`, a `List.TFAE`, Mathlib). |
| Theorem 17.3.2, p. 436 | For a chain with a σ-finite invariant measure `π`, (i) the ratio limit `Sₙ(f)/Sₙ(g) → π(f)/π(g)` from every state, (ii) `P_x`-triviality of `Σ` for every `x`, and (iii) Harris recurrence, are equivalent; (i) ⇔ (ii) by the Chacon–Ornstein theorem. | (ii) implies neither (i) nor (iii). `theorem_17_3_2_counterexample` is the same identity chain on `Bool` with `π = δ_true`: (ii) holds, the ratio limit fails from `false` and the chain is not Harris. Irreducibility does not rescue the statement: `theorem_17_3_2_counterexample_irreducible` is the walk on `ℤ` with steps `+1` and `−1` of probabilities `¾` and `¼` (`biasedKernel`). It is `ψ`-irreducible with counting measure invariant, its bounded harmonic functions are constant (`biased_harmonic_const`), so (ii) holds by Proposition 17.1.4, but it is transient (`biased_isTransientChain`), so it is not Harris and (i) fails. The equivalence is proved for recurrent chains (`theorem_17_3_2_tfae`); recurrence is used only for (ii) ⇒ (iii). (i) ⇔ (iii) needs no irreducibility hypothesis (`theorem_17_3_2_i_iff_iii`). |
| Theorem 17.3.2, proof of (iii) ⇒ (i), p. 436, with §17.3.1, p. 433 | (iii) ⇒ (i) follows from the decomposition (17.24) for the split `m`-skeleton, which §17.3.1 constructs for an aperiodic chain. | Theorem 17.3.2 assumes only Harris recurrence, and without aperiodicity the `m`-skeleton need not be Harris, so the split skeleton need not reach `α̌`. `skeleton_isHarris_counterexample` is the flip chain on `Bool` (period `2`): it is positive Harris, but its `2`-skeleton `P² = I` is irreducible for no nonzero measure. The book's route is formalised for aperiodic chains (`theorem_17_3_2_skeleton`, through `exists_skeleton_split`) and for a Harris `m`-skeleton with a minorization (`theorem_17_3_2_general`). The theorem itself holds for every Harris chain and every nonzero σ-finite invariant `π`, finite or not: `theorem_17_3_2_harris` proves it by Hopf's maximal-lemma argument on `P_π` (see below). |
| Theorem 17.3.1, p. 435 | The cycle sums with indices `0 ≤ j ≤ m − 2` and `j ≥ m` are independent "for any `m ≥ 2`"; each `sᵢ(f)` has the law (17.22). Proof: given `s₀(f), …, sₙ(f)`, every `s_{n+j}(f)`, `j ≥ 1`, has the common law, so the sequence is stationary and one-dependent. | The printed statement uses `m` both for the skeleton and for an index, and the variable `i` for the index `j`. What the proof proves and §17.3.4 uses is that the cycle sums are stationary and one-dependent, with common law (17.22) for every `j ≥ 0` (the proof says `n ≥ 1`), so that the even and the odd cycle sums are each i.i.d.; that is `theorem_17_3_1_general` (`skel_isStationarySeq`, `skel_isOneDependent`, `skel_map_cycles`). The conditional claim of the proof holds for `j ≥ 2` only: `sₙ(f)` and `s_{n+1}(f)` both depend on the block that follows the visit at `σ_α̌(n + 1)` (MT (17.21)), so consecutive cycle sums are in general dependent. The induction formalised is `skel_regeneration`. No counterexample is stated in Lean. For `m = 1` the cycle sums are i.i.d. (`theorem_17_3_1`). |
| Proposition 17.1.6, p. 426; proof of Theorem 17.4.4, p. 447 | If the LLN, the CLT or the LIL holds under one initial law, it holds under every initial law; "the proof for the CLT and LIL being identical". Theorem 17.4.4 reduces to `Φ₀ ∼ π` by "an obvious generalization" of the proposition. | The proof shows that `x ↦ P_x(E)` is harmonic for a shift-invariant event `E`. The LLN and the LIL are such events (`isShiftInvariant_llnSet`, `isShiftInvariant_hasLIL`), and `proposition_17_1_6` covers them for every Harris chain. A CLT or an FCLT is a statement about laws, not an event, and the argument does not apply. The claims are true and are proved by other means: for the CLT by comparing characteristic functions, `tendstoInDistribution_pathKernel_of_stationary` (aperiodic chains, Theorem 13.3.3, carried) and `tendstoInDistribution_pathKernel_of_stationary_periodic` (every period, phase averages, Theorem 13.3.4 (i), carried); for the FCLT by `tendstoInDistribution_pathMeasure_of_stationary`. There is no counterexample. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorems 17.1.5, 17.1.7, Propositions 17.1.6, 17.4.1, Theorems 17.2.1 (Harris form), 17.4.5 | A general state space. | `MeasurableSpace.CountablyGenerated X` (Mathlib) where Theorem 9.1.4 (carried) is used, as in the earlier chapters. |
| Proposition 17.1.6, p. 426 | `Φ` positive Harris. | Harris recurrence suffices; the statement is for shift-invariant events (`proposition_17_1_6`, `proposition_17_1_6_measure`). |
| Theorem 17.0.1, p. 422 | (ii)–(iv) for a `V`-uniformly ergodic chain. | Aperiodicity and (V4) for a petite set with `V ≥ 1` measurable and finite (`theorem_17_0_1`, `theorem_17_0_1_iv`). This is `V`-uniform ergodicity by Theorem 16.0.1; the Chapter 16 modules are not carried. The same reading is used in Lemma 17.5.1 and Theorem 17.5.4. |
| Theorem 17.2.1, p. 428 | A Harris chain with an invariant measure `π` and an atom `α ∈ B⁺(X)`. | `theorem_17_2_1` needs only a recurrent atom and an initial law from which it is reached a.s., with `π` the atom's invariant measure `μ°_α`. The Harris form `theorem_17_2_1_harris` takes `π` with `0 < π(α) < ∞`, which fixes the multiple of `μ°_α`. |
| Theorem 17.2.2, (17.14), p. 430 | A Harris chain with (17.14); the CLT and the LIL when `γ_g² > 0`. | (17.14) is stated under the cycle law `ρ`: `E_ρ[s(|g|)²] < ∞` and `E_ρ[(σ_α + 1)²] < ∞`. The CLT and the LIL hold under every initial law from which the recurrent atom is reached a.s. (`theorem_17_2_2`, `theorem_17_2_2_lil`), hence from every state of a Harris chain with an accessible atom (`theorem_17_2_2_harris`, `theorem_17_2_2_harris_lil`). `γ_g² = 0` is allowed. |
| Proposition 17.3.4, p. 438; Proposition 17.3.5, p. 438 | (DBL1)–(DBL2), with the T-chain property of Proposition 7.4.1. | `ψ`-irreducibility and the petiteness of compact sets of `θ` (`proposition_17_3_4_dbl`), and `ψ`-irreducibility of `Φ = (θ, Y)` (`proposition_17_3_5`), are hypotheses; the book takes them from Proposition 7.4.1, which belongs to the `NonlinearStateSpace` project and is not carried. (DBL2) is used only through `E log(1 + |Z|) < ∞` and `E log(1 + |W|) < ∞`, the latter implied by the book's `E W² < ∞`. |
| (17.27), p. 438 | `∫ log|x| π_θ(dx) < 0`. | Stated in the extended sense `∫ log⁺|x| dπ_θ < ∞` and `∫ log⁺|x| dπ_θ < ∫ log⁻|x| dπ_θ`, which allows `∫ log|x| dπ_θ = −∞` (`proposition_17_3_5`), with `π_θ = thetaLaw` (the invariant probability of `θ` whenever `θ` is Harris, `eq_thetaLaw_of_isInvariant`). Mathlib's `Real.log 0 = 0` makes an atom of `π_θ` at `0` count as `log 0 = 0`, so the remark that `E_π|θ| < 1` implies (17.27) is proved under `π_θ{0} = 0` (`condition_17_27_of_integral_abs_lt_one`). With `log 0 = −∞`, as in the book, the remark holds without this condition; this is a consequence of the convention, not an error of the book. |
| Theorem 17.3.6, p. 441 | `Φ` ergodic, a split `m`-skeleton, (17.31); the CLT and LIL when `γ_g² > 0`. | "Ergodic" is positive Harris and aperiodic (`theorem_17_3_6_skeleton`, `theorem_17_3_6_lil_skeleton`). The general forms assume what the splitting uses: a minorization of `Pᵐ` on `C` with `ψ(C) > 0`, the `m`-skeleton Harris, and (17.31) under `P̌_{ν*}` (`theorem_17_3_6_general`, `theorem_17_3_6_lil_general`). `γ_g² = 0` is allowed. |
| Theorem 17.4.3, p. 446 | `Φ` positive Harris, `π(|ĝ|) < ∞`. | An invariant probability suffices (`theorem_17_4_3`). |
| Theorems 17.4.4 and 17.4.5, pp. 447–448 | `g` centred, `π(ĝ²) < ∞`, `γ_g² > 0`; the conclusion "a.s. [`P_*`]". | `ĝ − Pĝ = g − c` for any constant `c` (then `c = π(g)` when `g ∈ L¹(π)`); the conclusion is convergence in distribution under every initial law (`theorem_17_4_4`) and every `P_x` (`theorem_17_4_4_initial_state`). The CLT forms that do not go through the FCLT take `ĝ, Pĝ ∈ L²(π)`, which follows from `π(ĝ²) < ∞` (`memLp_kernelInt_of_memLp`), and allow `γ_g² = 0`. |
| CLT moment condition, p. 450 | "`Φ` ergodic", (V3) with `f ≥ 1`, `V` finite, `C` petite, `π(V²) < ∞`. | The variance statements of Theorem 17.5.3 use `ψ`-irreducibility and aperiodicity only (`theorem_17_5_3`); the CLT, the degenerate case and the LIL take positive Harris and aperiodic (`theorem_17_5_3_clt`, `theorem_17_5_3_degenerate`, `theorem_17_5_3_lil_skeleton`). `V : X → [0, ∞]` is measurable and finite, and `|g| ≤ f` for measurable real `g`. |
| Lemma 17.5.1, p. 450 | A `V`-uniformly ergodic chain; `V' = (1 − √(1 − β))⁻¹√V`. | (V4) for a petite set and `V ≥ 1` finite, on a `ψ`-irreducible aperiodic chain with an invariant probability; the conclusion has `V' = (1 − ρ')⁻¹√V` for some `ρ' < 1` (`lemma_17_5_1`). |
| Lemma 17.5.2 (ii), p. 451 | The proof splits on a sublevel set of `V`, so that the split skeleton is `f^{(m)}`-regular. | Every minorization of a skeleton on a set of positive `ψ`-measure satisfies (17.53); the cost of reaching `α̌` is bounded through a set in `B⁺(X)` (`lemma_17_5_2_ii`, `Minorization.exists_tabooPotFn_le`). |
| Theorem 17.5.4, p. 453 | `g² < V`. | `g² ≤ V` (`theorem_17_5_4`), a weaker hypothesis. |
| Proposition 17.6.1, p. 454 | Mean `β < 0` and a finite fifth moment. | The increment is integrable with `∫ w dΓ < 0` and `∫ |w|ˡ dΓ < ∞` for `l ≤ 5` (`proposition_17_6_1`). The CLT and LIL are stated for every invariant probability and include `γ² = 0`. |
| Theorem 17.6.2, p. 456 | (LSS1)–(LSS2), (LSS5), (LSS4) and (LCM3); `E[W] = 0`. | `ψ`-irreducibility, aperiodicity and the petiteness of compact sets are hypotheses (`theorem_17_6_2`, `theorem_17_6_2_vector`); the book takes all three from Proposition 6.3.5. `lss_irreducible_petite` derives the first and the third from (LCM3), (LSS4) and (LSS5); aperiodicity is not derived. The disturbance is centred with finite second moments (`HasCentredSecondMoments`). |
| Theorem 17.7.2 and Lemma 17.7.3, pp. 460–461 | `C ∈ B⁺(X)`, with the finiteness of `V*` from the `f`-regularity of `C` (remark before (17.60)). | `C` is `f`-regular with `ψ(C) > 0` (`theorem_17_7_2`, `lemma_17_7_3`, and the periodic forms). In the aperiodic case Lemma 17.7.3 (iii) holds at every `x` with `V*(x) < ∞`; in general on a non-empty full absorbing set `X_f ⊆ {V* < ∞}` (`lemma_17_7_3_periodic`). |
| Theorem D.6.4, p. 563 | A square-integrable martingale `(Mₙ, 𝓕ₙ)` with (D.8) and (D.9). | `Mₙ = Σ_{k<n} Dₖ` with `Dₖ` `𝓕ₖ₊₁`-measurable, square integrable and `E[Dₖ | 𝓕ₖ] = 0`, so `M₀ = 0`; a nonzero `M₀` changes `n^{−1/2}mₙ` by `n^{−1/2}M₀ → 0` (`theorem_D_6_4`). `C[0, 1]` carries a Borel σ-algebra passed as instance hypotheses (`borelSpace_borel_C01` shows they are satisfiable). |
| Standard Brownian motion, App. D.6.2, p. 563 | (ii) `B(t) − B(s)` is independent of `{B(r) : r ≤ s}`. | Independence of every finite family of earlier values (`indepFun_brownian_increment`), through zero covariance in a Gaussian vector. |

## Proofs that differ from the book

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 17.1.2, p. 424 | The strong law for stationary sequences, cited from Doob [99]. | Birkhoff's pointwise ergodic theorem is proved for a measure-preserving map of a finite measure space (Garsia's maximal ergodic lemma, `maximal_ergodic`; `ae_tendsto_birkhoffLimit`, `ae_tendsto_birkhoffAverage_of_ergodic`), without limsup arguments, and applied to the shift on `P_π` (`pathSum_eq_birkhoffSum`, `theorem_17_1_2`). |
| Theorem 17.3.2, p. 436 | (i) ⇔ (ii) by the Chacon–Ornstein theorem; (iii) ⇒ (i) through the split `m`-skeleton. | No Chacon–Ornstein theorem and no splitting. The maximal ergodic lemma holds for the shift on the stationary path measure `P_π` even when `π` is infinite (`measurePreserving_shift_one_of_isInvariant`); with the zero–one law of a Harris chain (`harris_dichotomy`, from Theorem 17.1.5 and Proposition 17.1.6) it shows that `Sₙ(g)` is bounded above when `π(g) < 0` (`ae_bddAbove_pathSum_of_integral_neg`), which gives the ratio limit directly, Hopf's argument (`theorem_17_3_2_harris`). (ii) ⇔ (iii) for recurrent chains goes through the maximal Harris set of Theorem 9.1.5 (`theorem_17_3_2_iii_ii`, `theorem_17_3_2_ii_iii`). |
| Proposition 17.3.5, pp. 438–440 | Tightness of the laws of `Y` from `π_θ × δ_y` by (17.30), then the Feller property and Theorem 12.1.2. | The same estimates ((17.29) and the root test) show that the stationary series `Y₀ = Σⱼ (θ₋₁ ⋯ θ₋ⱼ)W₋ⱼ` of (17.28) converges a.s. (`ae_summable_yTerm`), and its law with `θ₀` is an invariant probability (`dblStationaryLaw`, `isInvariant_recursionKernel_map`). The backward LLN (17.26) is Birkhoff's theorem for the one-sided Bernoulli shift of the past innovations (`theorem_17_26`). |
| Proposition 17.4.1, p. 443 | The difference `h` of two solutions is harmonic, and Theorem 14.3.6 gives `h = π(h)` a.e. | `h(Φₖ)` is a stationary martingale bounded in `L¹(P_π)`; it converges a.s., the LLN identifies the limit as `π(h)`, and stationarity gives `h(Φ₀) = π(h)` (`proposition_17_4_1`). |
| Theorem 17.4.5 and Theorem 17.5.3, the CLT, pp. 448, 453 | The CLT as a consequence of the FCLT (Theorem 17.4.4), and in Theorem 17.5.3 from Theorem 17.3.6 through Lemma 17.5.2. | Besides the FCLT route (`theorem_17_4_5_clt_harris`), the CLT is proved directly: McLeish's martingale-difference CLT (`martingale_clt`, without complex logarithms) for `Mₙ(g)` under `P_π` (`theorem_17_4_5_clt_stationary`), then the transfer to every `P_x` by characteristic functions (`theorem_17_4_5_clt`, aperiodic; `theorem_17_4_5_clt_periodic`, every period). Theorem 17.5.3 takes its CLT from this route and needs no cycle moments (`theorem_17_5_3_clt`). |
| The LIL of Theorems 17.0.1 (iv), 17.5.3, 17.5.4, Proposition 17.6.1, Theorem 17.6.2, pp. 422, 452–456 | From Theorem 17.3.6 for a split `m`-skeleton, with (17.53). | Both routes are formalised. The book's: `lemma_17_5_2_ii` and `theorem_17_3_6_lil_general` (`theorem_17_5_3_lil_skeleton`, `theorem_17_5_4_lil_skeleton`, `theorem_17_0_1_iv_lil_skeleton`). A second route without minorization or aperiodicity: Stout's LIL for martingale differences (`hasLIL_martingale`) applied to `Mₙ(g)` and transferred by Proposition 17.1.6 (`hasLIL_pathSum_poisson`; `theorem_17_5_3_lil_poisson`, `theorem_17_5_4_lil_poisson`, `theorem_17_0_1_iv_lil_poisson`, `proposition_17_6_1_lil_poisson`, `theorem_17_6_2_lil_poisson`). |
| Theorem 17.5.4, the degenerate case, p. 454 | `Mₙ(g)` is `L²`-bounded by Theorem 15.0.1 and converges by the martingale convergence theorem. | If `π(ĝ² − (Pĝ)²) = 0` the martingale increments vanish `P_π`-a.s., so `n^{−1/2}Sₙ(ḡ) → 0` `P_π`-a.s. by (17.44), and Proposition 17.1.6 carries this shift-invariant event to every state (`tendsto_zero_of_poissonVariance_eq_zero`). The same argument proves the a.s. convergence that the book leaves to the reader for Theorem 17.5.3 (`theorem_17_5_3_degenerate`). |
| Theorem 17.6.2, pp. 455–456 | `γ_c² = Σ R(k) = D(0)` through the spectral density. | The solution of Poisson's equation for `g(x) = cᵀx` is `ĝ(x) = cᵀ(I − F)⁻¹x` (`lss_poissonSeries`), and `γ_c² = π(ĝ² − (Pĝ)²) = E[ĝ(GW)²]` (`lss_variance_integral`, `theorem_17_6_2_vector`). The vector CLT mentioned after the proof is derived by the Cramér–Wold theorem (`theorem_17_6_2_vector_clt_vec`), not from a vector-valued Theorem D.6.4. |
| Theorem 17.7.1, pp. 459–460 | The split chain `G_α̌(x, g)` in the strongly aperiodic case, and the resolvent in general. | Aperiodic case: the series `Σₙ (Pⁿg(x) − Pⁿg(x₀))` converges by the bound `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ A(V(x) + V(y)) + B` (Theorem 14.3.4, `tsum_fNorm_le_of_driftV3`, carried) and telescopes by the `f`-Norm Ergodic Theorem (`theorem_17_7_1`). The general case is the book's, through the resolvent `K_{a_{1/2}}` (`theorem_17_7_1_periodic`). |
| Theorem 17.7.2 and Lemma 17.7.3 (iii), periodic case, pp. 460–461 | Theorem 14.3.6 and the `d`-skeleton. | Theorem 14.3.6 (i) (carried) is turned into Cesàro convergence of `Pᵏ(x, ·)`, `π = d⁻¹ Σ_{r<d} π_{i+r}`, which is all the proofs need (`exists_full_tendsto_cesaro`, `theorem_17_7_2_periodic`, `lemma_17_7_3_periodic`). |
| Theorem 17.4.2, p. 445 | (V3) for `K_{a_ε}` with the petite sets `Cₙ = {K_{a_ε}(·, C) ≥ 1/n}` for some `n`. | `ε = 1/2` and `1/n = (4b + 1)⁻¹` explicitly (`driftV3_resolvent_half`, `isPetite_resolvent_half_level`); (17.40) and (17.42) are proved for every `ε` (`resolvent_eq_dirac_add_comp`, `isPoissonSolution_of_resolvent`). |
| The i.i.d. LIL, used on pp. 432 and 443 | Cited. | The Hartman–Wintner LIL is proved (`hasLIL_iid`). The upper half is the truncation argument with an exponential maximal inequality along geometric blocks (`lil_upper`); the lower half uses Mathlib's CLT on independent sub-blocks and the second Borel–Cantelli lemma, in the spirit of de Acosta (1983), instead of Kolmogorov's lower exponential bound (`lil_lower_normalized`). |
| The one-dependent CLT and LIL, pp. 441–443 | The blocks (17.36); "from which it can be shown" that the limit is `N(0, σ̄²)`; the LIL "can easily" be shown in the same way. | The big-block sums are within `L²`-distance `O(m^{−1/2})` of the partial sums uniformly in `n` (`tendsto_of_approx`, `IsOneDependent.tendstoInDistribution`). The LIL applies the i.i.d. LIL to the blocks and to the separating terms and lets the block length grow (`hasLIL_oneDependent`, `hasLIL_of_approx`). |
| Theorem D.6.4, p. 563 | A consequence of Theorem 4.1 of Hall and Heyde [151]. | Proved: the increments are truncated at `√(εn)`, recentred and stopped when the conditional-variance clock leaves a band (`locInc`); a fourth-moment bound and Doob's inequality give Billingsley's modulus condition (`modulus_condition_mPath`); (D.8) and (D.9), with Lenglart's inequality (`measureReal_sum_ge_le_lenglart`), make the localisation negligible; the finite-dimensional laws come from a martingale-array CLT (`martingale_array_clt`, `array_fidiLin_polygonal_of_tendstoInMeasure`); and tightness with converging finite-dimensional laws gives weak convergence (`tendstoInDistribution_of_tight_of_fidiLin`, Prokhorov's theorem in Mathlib). |
| Standard Brownian motion, App. D.6.2, p. 563 | Defined by its properties; existence assumed. | Constructed by the Lévy–Ciesielski series `B(t) = Σ_m ξ_m S_m(t)` of Schauder functions (`levyPath`), with a.s. uniform convergence from a fourth-moment bound and the first Borel–Cantelli lemma in expectation instead of the Kolmogorov–Chentsov theorem or Gaussian tail bounds; Wiener measure is its law (`wienerMeasure`). |

## Conventions

* Transition laws are Mathlib's kernels and `Pⁿ` is the kernel power. The chain lives on the path
  space `ℕ → X` with laws `P_x = pathKernel P x` and `P_μ = pathMeasure P μ`, the shift
  `shift k`, and the natural filtration `natFilt` (carried). Forcing functions `g` are real and
  measurable; test functions `f`, `V` and the drift constants take values in `[0, ∞]`.
* "a.s. [`P_*`]" is `P_x`-a.s. for every `x`, and where stated `P_μ`-a.s. for every initial law.
  "Ergodic" (p. 316) is positive Harris and aperiodic.
* The CLT is stated as `n^{−1/2}Sₙ(ḡ) ⇒ Z` with `Z ∼ N(0, γ_g²)` (`gaussianReal 0 γ_g²`,
  Mathlib). For `γ_g² > 0` this is the book's `(nγ_g²)^{−1/2}Sₙ(ḡ) ⇒ N(0, 1)`; for `γ_g² = 0` it
  says `n^{−1/2}Sₙ(ḡ) ⇒ 0`, which the book excludes from its definition. Where the book assumes
  `γ_g² > 0` only to define the CLT or the LIL, the Lean theorems drop the assumption.
* The LIL is the `ε`-form `HasLIL s γ` with `γ ≥ 0`: for every `ε > 0`, eventually
  `sₙ ≤ (γ + ε)√(2n log log n)` and frequently `sₙ ≥ (γ − ε)√(2n log log n)`, and the same for
  `−sₙ`. For `γ > 0` it is the book's statement with limits `±1` after dividing by
  `√(2γ²n log log n)` (`HasLIL.limsup_eq`, `HasLIL.liminf_eq`); for `γ = 0` it says
  `Sₙ(ḡ) = o(√(n log log n))`.
* Poisson's equation is `ĝ − Pĝ = g − c` (`IsPoissonSolution`) with any constant `c` and a
  real-valued `ĝ`, so solutions are finite by type. `γ_g² = π(ĝ² − (Pĝ)²)` is written out, and
  (17.3) is `asymptoticVariance P π g`.
* `V`-uniform ergodicity enters as aperiodicity and (V4) for a petite set with `V ≥ 1` finite. By
  Theorem 16.0.1 this is equivalent, but the Chapter 16 project is not carried.
* `C[0, 1]` is `C(unitInterval, ℝ)` with the sup norm; statements that need its Borel σ-algebra
  take `[MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]`. Convergence in
  distribution is Mathlib's `TendstoInDistribution`. The interpolations (17.45), (17.47) and (D.7)
  are `polygonal n`.
* The hypothesis `∫ g dπ ≠ 0` of Theorems 17.2.1 and 17.3.2 (i) is the book's, and the module
  docstrings of `LLNApplications`, `SplitLimitTheorems` and `GapsChaconOrnstein` state it so. The
  PDF text layer drops the negation stroke and reads `∫ g dπ = 0`, which is not a misprint: the
  printed page has `≠`, and the Lean statements agree with it.
* The random-index step `HasLIL.comp_index` assumes that the indices grow by at most one per step,
  as the number of completed cycles does. `not_hasLIL_lilAlternating_two_mul` shows that this
  hypothesis cannot be replaced by `Tₙ/n → c` alone (the indices `Tₙ = 2n` see only the even
  terms of an alternating sequence). This concerns the design of the Lean tool, not a claim of
  the book.
* The carried modules are copied from the earlier projects without change apart from the namespace
  and the imports (see the [README](../README.md)). The corrections they contain belong to
  Chapters 1–15, are recorded in their module docstrings and in those projects, and are not
  repeated here. `GapsBilinear` contains an unchanged copy of Proposition 11.4.2 from the
  `DriftRegularity` project.

## Not formalised

* **Proposition 17.3.5** (p. 438): the aperiodicity of `Φ = (θ, Y)`, which the book takes from
  Proposition 7.4.1 under (7.24); the tightness bound (17.30) itself; the simulation remarks and
  the value `∫ log|x| dπ_θ ≈ −0.3` (p. 440).
* **Theorem 17.6.2** (pp. 455–456): the LIL for `cᵀXₖ` when the state has dimension `n > 1` (the
  scalar model has it, `theorem_17_6_2_lil_poisson`); the moving-average representation of the
  stationary `Yₖ`; the spectral density `D(ω)` for `ω ≠ 0`; the aperiodicity of the model, which
  is a hypothesis. `V`-uniform ergodicity is proved for `V = 1 + xᵀMx`, which is equivalent to the
  book's `|x|² + 1` (`dotProduct_self_le_quadForm`, `quadForm_le`).
* **Lemma 17.7.3 (iii)** (p. 461): the second limit `E_x[V*(Φₖ)1{τ_C > k}] → 0`, with (17.63);
  Theorem 17.7.2 does not use it.
* **The atom solution of Poisson's equation** (17.38) (p. 444), and the identity (17.52) by the
  book's computation (pp. 449–450); the atom form of the variance in Proposition 17.6.1 (p. 455).
  The equality of the cycle variance with `π(ĝ² − (Pĝ)²)` is proved for split skeletons under the
  CLT moment condition (`skelCLTVariance_eq_poissonVariance`).
* **Theorem D.6.3 (i)** for `p ≥ 1` not an even integer; the infinite-horizon form of (ii), which
  follows from the finite-horizon bound `measureReal_exists_ge_le` by monotone convergence.
  **Theorems D.6.1–D.6.2** are Mathlib's martingale convergence theorem and are not restated.
* **The `V`-uniform models of Chapter 16** named on p. 454: the Chapter 16 modules are not
  carried, so their CLT and LIL are not stated, although `theorem_17_0_1` applies to each.
* **§17.7**, the commentary (pp. 456–459): the history, the second-edition notes, the uses of
  Poisson's equation (i)–(vi) and the sensitivity formula (17.58). Theorems 17.7.1–17.7.2 and
  Lemma 17.7.3, which sit in the commentary, are formalised.
* **Informal remarks.** The aims of the chapter (pp. 421–423); the size of the set `F_X` (p. 424);
  the examples `Q{A}` and the limit average as invariant variables (p. 425); the rephrasing of
  Theorem 8.4.2 and the extension to unbounded harmonic functions (p. 426); the difference between
  the stationary variance and `γ_g²` (p. 430); the counterexamples of Chung [71] (p. 430); the
  remark that `ĝ` finite at one point is finite on a full absorbing set (p. 443); the use of
  Theorem 14.3.7 for `π(V²) < ∞` (p. 450); the Comparison Theorem bound `π(g) ≤ η` (p. 460), which
  is not stated separately; and the name "invariance principle" (p. 563).
