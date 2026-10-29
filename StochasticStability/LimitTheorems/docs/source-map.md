# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University Press,
2009): Chapter 17, pp. 421–461, and the parts of Appendix D that it uses (§D.6, pp. 561–563).
Equation numbers are the book's. Lean names are relative to `MeynTweedie.LimitTheorems`; names from
Mathlib are marked as such. Names marked "carried" are in the modules copied from the earlier
projects (see the [README](../README.md)). `P_x` is `pathKernel P x` and `P_μ` is
`pathMeasure P μ` (carried), the laws of the chain on the path space `ℕ → X`. The sums (17.1)
`Sₙ(g) = Σ_{k=1}^n g(Φₖ)` are `pathSum g n`. `ψ` is a maximal irreducibility measure
(`IsMaximalIrreducibility P ψ`, carried), and `B⁺(X)` is `{B : ψ(B) > 0}`. Harris and positive
Harris chains are `IsHarris P ψ` and `IsPositiveHarris P ψ`, aperiodicity is `IsAperiodic P ψ`, an
invariant probability is `IsInvariant P π` with `IsProbabilityMeasure π`, and a σ-finite invariant
measure is `IsInvariantMeasure P π` (all carried). (V3) is `DriftV3 P V f b C` and (V4) is
`DriftV4 P V ρ b C` (carried). A CLT is Mathlib's `TendstoInDistribution` towards a variable `Z`
with `HasLaw Z (gaussianReal 0 γ²)` (Mathlib), and the LIL is `HasLIL s γ` (`IIDLIL`). A solution
`ĝ` of Poisson's equation `ĝ − Pĝ = g − c` is `IsPoissonSolution P g ĝ c`, and `Pĝ` is
`kernelInt P ĝ`. `C[0, 1]` is `C(unitInterval, ℝ)` (Mathlib) with the sup norm, and the law of
standard Brownian motion on it is `wienerMeasure`. Every place where the Lean statement departs from
the book is listed in [corrections](corrections.md).

## Chapter 17 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| (17.1), p. 421 | The partial sums `Sₙ(g) = Σ_{k=1}^n g(Φₖ)` | `pathSum g n`; `pathSum_eq_birkhoffSum` |
| p. 421 | The four kinds of limit theorems (martingales, LLN, CLT, LIL) and the role of the autocovariances | Not formalised (informal) |
| (17.2), p. 422 | The LLN: `(1/n) Sₙ(g) → π(g)` almost surely from every initial condition | `lln_of_harris`, `lln_of_harris_measure`; the event is `llnSet g c` |
| p. 422 | The CLT: for some `0 < γ_g² < ∞`, `(nγ_g²)^{−1/2} Sₙ(ḡ)` converges in distribution to `N(0, 1)` under every `P_x`, `ḡ = g − π(g)` | Stated as `n^{−1/2} Sₙ(ḡ) ⇒ N(0, γ_g²)` (`TendstoInDistribution`, Mathlib), which also covers `γ_g² = 0`; see corrections |
| p. 422 | The LIL: the lim inf and lim sup of `(2γ_g² n log log n)^{−1/2} Sₙ(ḡ)` are `−1` and `+1` almost surely from every initial condition | `HasLIL` (the `ε`-form with constant `γ_g ≥ 0`, `lilScale n = √(2 n log log n)`), `LILBound`; `HasLIL.limsup_eq`, `HasLIL.liminf_eq` give the `limsup`/`liminf` form; see corrections |
| Theorem 17.0.1 (i), p. 422 | A positive Harris chain obeys the LLN for every `g ∈ L¹(π)` | `theorem_17_0_1` (first conjunct), from `lln_of_harris` |
| Theorem 17.0.1 (ii), (17.3)–(17.4), p. 422 | For a `V`-uniformly ergodic chain and `g² ≤ V`, the series `γ_g² = E_π[ḡ(Φ₀)²] + 2 Σ_{k≥1} E_π[ḡ(Φ₀)ḡ(Φₖ)]` is well defined, non-negative and finite, and equals `lim (1/n) E_π[Sₙ(ḡ)²]` | `theorem_17_0_1` (second conjunct; `V`-uniform ergodicity as aperiodicity and (V4) for a petite set; the autocovariances are absolutely summable); `asymptoticVariance P π g` is (17.3) |
| Theorem 17.0.1 (iii), p. 422 | If moreover `γ_g² = 0`, `n^{−1/2} Sₙ(ḡ) → 0` almost surely from every initial condition | `theorem_17_0_1` (last clause) |
| Theorem 17.0.1 (iv), p. 422 | If `γ_g² > 0`, the CLT and the LIL hold | CLT: `theorem_17_0_1_iv`. LIL: `theorem_17_0_1_iv_lil_poisson` (martingale route, no minorization), `theorem_17_0_1_iv_lil_skeleton` (the book's route, through a split `m`-skeleton), `theorem_17_0_1_iv_lil` (one-step minorization and (17.31)); all include `γ_g² = 0` |
| p. 423 | Proof: the LLN by Theorem 17.1.7; the CLT and LIL by Theorem 17.3.6; the variance by Lemma 17.5.2 and Theorem 17.5.3 | In the proofs of `theorem_17_0_1` and `theorem_17_0_1_iv` (by `theorem_17_5_4`, with the CLT from the martingale route, `theorem_17_4_5_clt`); see corrections |
| p. 423 | The LLN and CLT in more general contexts, and the functional CLT for `f`-regular chains | §17.4 below |

## §17.1.1 Invariant random variables and events

| Source | Claim | Lean |
| --- | --- | --- |
| (17.5), p. 423 | `Y` is `P_μ`-invariant if `θᵏY = Y` `P_μ`-a.s. for every `k`; `P_μ`-invariant events form a σ-field `Σ_μ` | `IsPathInvariant P μ Y` (events through `1_A`) |
| p. 423 | For `μ = π`, `Σ_π` is the invariant σ-field of ergodic theory | Not stated separately; Birkhoff's theorem is proved for strictly invariant sets (`BirkhoffErgodic`) |
| (17.6), p. 423 | `h_Y(x) = E_x[Y]` | `expectFn P Y` |
| (17.7), p. 423 | `h_Y(Φₖ) = E[θᵏY | 𝓕ₖ^Φ] = E[Y | 𝓕ₖ^Φ]` | `condExp_eq_expectFn` (for `P_μ`-invariant integrable `Y`) |
| Lemma 17.1.1, p. 423 | For an invariant probability `π` and a `P_π`-invariant `Y` with `E_π|Y| < ∞`, `Y = h_Y(Φ₀)` `P_π`-a.s. | `lemma_17_1_1` |
| p. 424 | Proof: `h_Y(Φₖ)` is a convergent martingale and stationary | `tendsto_expectFn_coord` (Lévy's upward theorem, Mathlib) in the proof of `lemma_17_1_1` |
| p. 424 | `E[X | Σ_π] = X_∞(Φ₀)` is a function of `Φ₀` | `theorem_17_1_2_condExp` |
| Theorem 17.1.2, p. 424 | For an invariant probability `π` and `X ∈ L¹(P_π)`, there is `F_X` of full `π`-measure with `(1/N) Σ_{k=1}^N θᵏX → X_∞(x)` `P_x`-a.s. for `x ∈ F_X` | `theorem_17_1_2` (no irreducibility) |
| p. 424 | Proof: the strong law for stationary sequences (Doob [99]) | Birkhoff's pointwise ergodic theorem, proved here: `ae_tendsto_birkhoffLimit`, `maximal_ergodic`, `birkhoffLimit`, `setIntegral_birkhoffLimit`, `ae_tendsto_birkhoffAverage_of_ergodic`; `measurePreserving_shift` |
| p. 424 | The set `F_X` may be small and depends on `X`; Harris chains resolve this | Not formalised (remark); see Theorem 17.1.7 |

## §17.1.2 Harmonic functions

| Source | Claim | Lean |
| --- | --- | --- |
| p. 425 | `Y` is invariant if it is `P_μ`-invariant for every `μ`; the invariant events form `Σ` | `IsInvariantRV P Y` |
| p. 425 | Examples: `Q{A}` and the limit average of `1{Φₖ ∈ A}` are invariant | Not stated separately |
| (17.8), p. 425 | `h` is harmonic if `Ph = h`; equivalently `h(Φₖ)` is a martingale under every initial law | `IsHarmonic P h`; `IsHarmonic.martingale`, `IsHarmonic.integral_pow` |
| p. 425 | `x ↦ Q(x, A)` is harmonic | Not stated separately; `isHarmonic_pathKernel_shiftInvariant` (`x ↦ P_x(E)` is harmonic for every shift-invariant `E`) |
| Theorem 17.1.3, p. 425 | (i) For bounded invariant `Y`, `h_Y` is harmonic and `Y = lim h_Y(Φₖ)` a.s. from every initial law; (ii) for bounded harmonic `h`, `H = limsup h(Φₖ)` is invariant with `h_H = h` | `theorem_17_1_3_i`, `theorem_17_1_3_ii` (`harmonicLimit h`, `harmonicLimit_shift`) |
| Proposition 17.1.4, p. 426 | All bounded harmonic functions are constant iff `Σ_μ` and `Σ` are `P_μ`-trivial for every `μ` | `proposition_17_1_4` |
| Theorem 17.1.5, p. 426 | For a Harris chain the bounded harmonic functions are constant | `theorem_17_1_5` (countably generated `σ`-algebra) |
| p. 426 | A rephrasing of the transience criterion Theorem 8.4.2; extensions beyond bounded functions | Not formalised (remarks); Proposition 17.4.1 below is such an extension |
| Proposition 17.1.6, p. 426 | For a positive Harris chain, if the LLN, the CLT or the LIL holds under one initial law, it holds under every initial law | `proposition_17_1_6`, `proposition_17_1_6_measure` (Harris; every shift-invariant event, which covers the LLN and the LIL); the CLT: `tendstoInDistribution_pathKernel_of_stationary_periodic`, `tendstoInDistribution_pathMeasure_of_stationary`, `tendstoInDistribution_pathKernel_of_stationary`; see corrections |
| pp. 426–427 | Proof: `x ↦ P_x{LLN}` is harmonic | `isHarmonic_pathKernel_shiftInvariant`, `isShiftInvariant_llnSet`, `measurableSet_llnSet` |

## §17.1.3 The LLN for positive Harris chains

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 17.1.7, p. 427 | For a chain with an invariant probability: (i) positive Harris; (ii) the LLN for every `f ∈ L¹(π)` from every state; (iii) `Σ` is `P_x`-trivial for every `x`; are equivalent | False as printed: `theorem_17_1_7_counterexample` ((iii) does not give (i)). Corrected: `theorem_17_1_7` (a `List.TFAE`, Mathlib, with (iii) for every initial law); see corrections |
| pp. 427–428 | Proof: (i) ⇒ (ii) by Theorem 17.1.2 and Proposition 17.1.6; (ii) ⇒ (iii) by Theorem 17.1.3; (iii) ⇒ (i) since `Q(·, A)` is constant | `ergodic_pathMeasure` (every strictly invariant event is `P_π`-trivial), `lln_of_harris`, in the proof of `theorem_17_1_7` |

## §17.2 Ergodic theorems for chains possessing an atom

| Source | Claim | Lean |
| --- | --- | --- |
| p. 428 | The visit times `σ_α(k)` to the atom | `renewalTime α j`, `renewalTime_lt_succ`, `renewalTime_add_one`; `hitNat`, `restart` |
| (17.9), p. 428 | `sⱼ(f)`, the sum of `f(Φᵢ)` over the `j`-th excursion between visits | `cycleSum α f (cycle α (j + 1))` (`cycle`, `excursion`); `sum_range_renewalTime` |
| p. 428 | By the strong Markov property the `sⱼ(f)` are i.i.d. | `map_cycles_eq_infinitePi` (the whole excursions are i.i.d. with law `cycleLaw P α a`), `lintegral_mul_restart`, `pathMeasure_cycles_box`; `iIndepFun_cycles`, `identDistrib_cycles` |
| (17.10), p. 428 | `E_α[s₁(f)] = E_α[Σ_{i=1}^{τ_α} f(Φᵢ)] = ∫ f dμ`, `μ` invariant by Theorem 10.0.1 | `lintegral_cycleSumE`, `integral_cycleSum`, `integrable_cycleSum`; `μ` is `atomMeasure P hα a` (carried) |
| p. 428 | The LLN, CLT and LIL follow from the i.i.d. theorems for the `sⱼ(f)` | `tendsto_cycle_average`, `ae_cycles_of_ae_infinitePi` |
| Theorem 17.2.1, p. 428 | For a Harris chain with an invariant measure `π` and an atom in `B⁺(X)`, `Sₙ(f)/Sₙ(g) → π(f)/π(g)` from every state, for `f, g ∈ L¹(π)` with `∫ g dπ ≠ 0` | `theorem_17_2_1` (any recurrent atom and any initial law from which it is reached a.s.), `theorem_17_2_1_harris` (the book's setting, with `0 < π(α) < ∞`) |
| (17.11)–(17.12), p. 429 | `ℓₙ`, the number of visits by time `n`, and the sandwich between cycle sums | `cycleCount α n`, `cycleCount_eq`; `tendsto_renewal_average`, `tendsto_of_renewal_sandwich` |
| (17.13), p. 430 | With an atom, `γ_g² = π(α) E_α[(Σ_{k=1}^{τ_α} ḡ(Φₖ))²]` | `theorem_17_2_2_variance` (`cltVariance P α a g`), with `π = μ°_α/μ°_α(X)` and `π(α) = 1/m` |
| p. 430 | The stationary variance `∫ ḡ² dπ` differs from `γ_g²` unless the chain is i.i.d. | Not formalised (remark) |
| (17.14), p. 430 | The CLT moment condition for `α`: `E_α[s₀(|g|)²] < ∞` and `E_α[s₀(1)²] < ∞` | The hypotheses `hg2` and `hL2` of `theorem_17_2_2` (under the cycle law `ρ`) |
| Theorem 17.2.2, p. 430 | For a Harris chain with (17.14), the chain is positive Harris, `γ_g² < ∞`, and if `γ_g² > 0` the CLT and the LIL hold | CLT: `theorem_17_2_2`, `theorem_17_2_2_harris`; LIL: `theorem_17_2_2_lil`, `theorem_17_2_2_harris_lil`; positivity and (17.13): `theorem_17_2_2_variance`; `γ_g² = 0` included |
| (17.15), p. 430 | `|Σ_{i≤n} ḡ(Φᵢ) − Σ_{j<ℓₙ} sⱼ(ḡ)| ≤ s_{ℓₙ}(|g|)` | `abs_pathSum_sub_le` |
| (17.16)–(17.17), p. 431 | `s_{ℓₙ}(|g|)/√n → 0`, so the chain sum and the cycle sum differ by `o(√n)` a.s. | `tendsto_term_div_of_tendsto_average`, `tendsto_pathSum_sub_cycles`; `ae_tendsto_sq_div_of_identDistrib` |
| (17.18), p. 431 | `ℓₙ/n → π(α)` | `tendsto_cycleCount_div` (`ℓₙ/n → 1/m`, `m = E_a[τ_α]`, `cycleMeanLength`) |
| (17.19)–(17.20), p. 431 | Kolmogorov's inequality replaces `ℓₙ` by `⌊π(α)n⌋` in probability | `tendstoInMeasure_anscombe`, `kolmogorov_ineq`, `kolmogorov_ineq_shift` |
| p. 432 | The CLT for i.i.d. sequences finishes the proof | Mathlib's i.i.d. CLT (`tendstoInDistribution_inv_sqrt_mul_sum_sub`), in the proof of `theorem_17_2_2` |
| p. 432 | The LIL: the i.i.d. LIL for the `sⱼ(g)` and `log log ℓₙ / log log n → 1` | `hasLIL_iid` (Hartman–Wintner, proved here), `HasLIL.comp_index` (random index), `tendsto_lilScale_div`, `cycleCount_succ_le`, in the proof of `theorem_17_2_2_lil` |

## §17.3.1 Splitting general Harris chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 433 | For an aperiodic chain some skeleton has a minorization on `C ∈ B⁺(X)` (Proposition 5.4.5), so the `m`-skeleton can be split | `exists_skeleton_split` (with the `m`-skeleton Harris, through Theorem 9.1.6, carried); without aperiodicity: `skeleton_isHarris_counterexample`; see corrections |
| (17.21), p. 433 | The joint conditional law of the level `Yₙ` and the next block given `Φ_{nm} = x`, through the density `r(x, y)` of `ν` against `Pᵐ(x, ·)` | `skelDensity` (capped at `1`, `setLIntegral_skelDensity`), `blockKernel`, `blockW`, `blockW_comp_splitK`, `skelKernel`, `skelInit` |
| pp. 433–434 | Integrating out the block gives the split kernel of the skeleton; Bayes' rule | `blockW_map_last`, `skel_map_skelState` (the skeleton states form the split chain of `Pᵐ`) |
| p. 434 | The whole chain lives on the same space as the split skeleton | `skel_map_recover`, `pathMeasure_map_blockify`, `pathMeasure_map_lump` |
| p. 434 | Given `Yₙ = 1`, past and future after the next block are independent, the future with law `P̌_{ν*}`; `α̌ = C × {1}` behaves like an atom | `skel_regeneration`, `skel_box`, `pathMeasure_map_skelFresh`, `pathKernel_map_skelFresh_shift`, `lintegral_mul_skelRestart`; `skelAtom M`, `skelFresh`, `skelFreshLaw M` |
| p. 434 | The entrance times `σ_α̌(k)` and hitting times `τ_α̌(k)`; the cycle sums `sᵢ(f)` and the block sums `Zⱼ(f)` | `renewalTime (skelAtom M) j`; `skelCycle M f j`, `skelCycle_eq`, `skelPreSum M f` |
| Theorem 17.3.1, p. 435 | Two index sets of cycle sums are independent; each `sᵢ(f)` has the law (17.22) | Garbled as printed; formalised as proved: `theorem_17_3_1_general` (stationary and one-dependent cycle sums, common law (17.22), even and odd cycle sums each i.i.d.; `skel_isStationarySeq`, `skel_isOneDependent`, `skel_map_cycles`, `skel_map_cycle`); for `m = 1`, `theorem_17_3_1` (i.i.d.); see corrections |
| (17.22), p. 435 | The common law is that of `Σ_{k=0}^{σ_α̌ m + m − 1} f(Φₖ) = Σ_{k≤σ_α̌} Zₖ(f)` under `P̌_{ν*}` | `skel_map_cycle`, with `skelPreSum` under `skelFreshLaw` |
| (17.23), p. 435 | `Ě[sᵢ(f)] = δ⁻¹ π(C)⁻¹ m ∫ f dπ` | `theorem_17_3_1_general_mean` (a Harris `m`-skeleton, `0 < π(C) < ∞`), `lintegral_blockMeanE_split`, `blockMeanE`; for `m = 1`, `theorem_17_3_1` |
| p. 435 | Proof: the conditional law of `s_{n+j}` given `s₀, …, sₙ` is the common law for `j ≥ 1`, so the sequence is stationary and one-dependent | `skel_regeneration`; the claim holds for `j ≥ 2` only, see corrections |
| (17.24), p. 435 | `ℓₙ` and the decomposition of `Sₙ(f)` into an initial piece, complete cycles and a final piece | `sum_range_renewal_eq`, `abs_skelPartialSum_sub_le`; `skelCount M`, `skelBound M`, `countBelow` |

## §17.3.2 The LLN for general Harris chains

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 17.3.2, p. 436 | For a chain with a σ-finite invariant measure `π`: (i) `Sₙ(f)/Sₙ(g) → π(f)/π(g)` from every state, for `f, g ∈ L¹(π)` with `∫ g dπ ≠ 0`; (ii) `Σ` is `P_x`-trivial for all `x`; (iii) Harris recurrence; are equivalent | False as printed ((ii) does not give (iii)): `theorem_17_3_2_counterexample` (identity chain on `Bool`), `theorem_17_3_2_counterexample_irreducible` (transient walk on `ℤ`). Corrected: `theorem_17_3_2_tfae` (a `List.TFAE`, Mathlib, for a recurrent chain; `HasRatioLimit P π` is (i)); see corrections |
| p. 436 | Proof of (i) ⇒ (iii): `P_x{f(Φᵢ) > 0 i.o.} = 1` | `theorem_17_3_2_i_iii`, `hitProb_eq_one_of_hasRatioLimit`, `theorem_17_3_2_i_iff_iii` (no irreducibility assumed) |
| p. 436 | Proof of (i) ⇔ (ii) by the Chacon–Ornstein theorem | `theorem_17_3_2_iii_ii` and `theorem_17_3_2_ii_iii` (recurrent chains, through the maximal Harris set of Theorem 9.1.5, carried), with (i) ⇔ (iii); no Chacon–Ornstein theorem |
| p. 436 | Proof of (iii) ⇒ (i) through the split skeleton, (17.24), and the strong law for the even and odd cycle sums | `theorem_17_3_2_harris`, `theorem_17_3_2_harris_measure` (every Harris chain, by Hopf's maximal-lemma argument: `measurePreserving_shift_one_of_isInvariant`, `harris_dichotomy`, `ae_bddAbove_pathSum_of_integral_neg`, `ratio_lln_of_harris_nonneg`). The book's route: `theorem_17_3_2_skeleton` (aperiodic Harris chains), `theorem_17_3_2_general` (a Harris `m`-skeleton with a minorization), `theorem_17_3_2` (`m = 1`), with `IsOneDependent.ae_tendsto_average`; see corrections |
| p. 436 | The theorem covers null recurrent chains; with `g ≡ 1` the positive case gives Theorem 17.2.1 | `theorem_17_3_2_harris` (σ-finite `π`, finite or not); `theorem_17_3_2_positive` (positive Harris) |

## §17.3.3 Applications of the LLN

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 17.3.3, p. 437 | For a positive Harris chain and `π(|g|) < ∞`, `(1/n) max_{1≤k≤n} |g(Φₖ)| → 0` a.s. from every state | `theorem_17_3_3` |
| (17.25), p. 437 | Equivalently `g(Φₙ)/n → 0` | `tendsto_iSup_div_of_tendsto_term` in the proof |
| p. 437 | The parameter process of the bilinear model (DBL1)–(DBL2) is a Feller T-chain, positive Harris by Proposition 11.4.2 | `dblKernel_map_fst` (the parameter process is the AR(1) model `ar1Kernel`, carried), `proposition_11_4_2` (copied into `GapsBilinear`); the T-chain property is a hypothesis |
| Proposition 17.3.4, p. 438 | `θ` is positive Harris, and `(1/N) Σ f(θₖ) → π_θ(f)` from every state whenever `π_θ(f⁺) < ∞` | `proposition_17_3_4_dbl`, `proposition_17_3_4_dbl_thetaLaw` (the book's setting, `π_θ` is `thetaLaw`); `proposition_17_3_4` (any positive Harris chain, the case `π(f⁻) = ∞`) |
| (17.26), p. 438 | The backward LLN `(1/N) Σ f(θ₋ₖ) → π_θ(f)` for the two-sided stationary process | `theorem_17_26`, `theorem_17_26_integrable` (through `thetaSeries`, `thetaSeries_cons`, `ae_summable_thetaSeries` and the Bernoulli shift `infinitePi_seqShift_ergodic`, `ae_tendsto_birkhoffAverage_seqShift`) |
| p. 438 | `E_π|θ| < 1` implies (17.27) by Jensen's inequality | `condition_17_27_of_integral_abs_lt_one` (with `π_θ{0} = 0`); see corrections |
| Proposition 17.3.5, (17.27), p. 438 | If `∫ log|x| π_θ(dx) < 0`, the joint process `Φ = (θ, Y)` is positive recurrent and aperiodic | `proposition_17_3_5` (an invariant probability `dblStationaryLaw` with first marginal `π_θ`; positive and recurrent when `Φ` is `ψ`-irreducible; (17.27) in an extended sense); aperiodicity not formalised; see corrections |
| (17.28), p. 439 | `Y_{k+1}` as a sum of products of the `θᵢ` times the `Wⱼ` | `yTerm`, `ySeries`, `yTerm_succ`, `ySeries_cons` (the stationary output) |
| (17.29), p. 439 | `(1/n) log Π θ₋ᵢ² → 2 ∫ log|x| dπ_θ < 0` | `theorem_17_26` for `log|x|`, in the proof of `ae_summable_yTerm`; `abs_prod_le_exp_sum_log` |
| (17.30), p. 439 | Tightness bounds for `Y` from `π_θ × δ_y` | Not formalised: replaced by the convergence of the stationary series (`ae_summable_yTerm`, the root test of p. 440); see corrections |
| p. 440 | The root test: `Σ ρ^{−ℓ} Π²` converges a.s. | `ae_summable_yTerm`, `exists_truncation_neg` |
| p. 440 | Explosive sample paths under (17.27), the simulation with `σ_z = 0.2`, `σ_w = 0.1`, `α = 0.99`, and `∫ log|x| dπ_θ ≈ −0.3` | Not formalised (simulation) |

## §17.3.4 The CLT and LIL for Harris chains

| Source | Claim | Lean |
| --- | --- | --- |
| (17.31), p. 441 | The CLT moment condition for the split chain: `α̌` is reached a.s. from every state, `Ě_{ν*}[(Σ_{n≤σ_α̌} Zₙ(|g|))²] < ∞` and `Ě_{ν*}[σ_α̌²] < ∞` | The hypotheses of `theorem_17_3_6_general` (the reachability through the `m`-skeleton being Harris) and of `theorem_17_3_6` (`m = 1`) |
| (17.32), p. 441 | `γ_g² = m⁻¹π̌(α̌)Ě[s₁(g)²] + 2m⁻¹π̌(α̌)Ě[s₁(g)s₂(g)]`, `π̌(α̌) = δπ(C)` | `skelCLTVariance M π g`, `skelCLTVariance_nonneg`; for `m = 1`, `atomMean_split_eq` |
| Theorem 17.3.6, p. 441 | For an ergodic chain with (17.31), `0 ≤ γ_g² < ∞`, and if `γ_g² > 0` the CLT and the LIL hold | CLT: `theorem_17_3_6_skeleton` (the book's hypotheses), `theorem_17_3_6_general`, `theorem_17_3_6` (`m = 1`). LIL: `theorem_17_3_6_lil_skeleton`, `theorem_17_3_6_lil_general`, `theorem_17_3_6_lil` (`m = 1`). `γ_g² = 0` included |
| (17.33), p. 441 | `n^{−1/2}(Sₙ(ḡ) − Σ_{j<ℓₙ} sⱼ(ḡ)) → 0` a.s. | `skel_ae_tendsto_pathSum_sub_cycles`, `skel_ae_tendsto_last_sq` |
| (17.34), p. 441 | `ℓₙ/n → π̌(α̌)/m` | `skel_ae_tendsto_count_div`, `tendsto_countBelow_div` |
| (17.35), p. 441 | Kolmogorov's inequality, by stationarity and one-dependence, replaces `ℓₙ` by `⌊m⁻¹π̌(α̌)n⌋` | `IsOneDependent.tendstoInMeasure_randomIndex` (Kolmogorov's inequality for the even and odd terms) |
| (17.36), p. 442 | The blocks `ηⱼ` of `m − 1` cycle sums separated by single sums | `bigBlock`, `sum_range_eq_bigBlock`, `IsOneDependent.iIndepFun_bigBlock`, `IsStationarySeq.identDistrib_bigBlock` |
| p. 442 | `σ_m² = (m − 1)Ě[s₁²] + 2(m − 2)Ě[s₁s₂]`; the i.i.d. CLT for the blocks; `m → ∞` gives `N(0, σ̄²)` with `σ̄² = Ě[s₁²] + 2Ě[s₁s₂]` | `IsOneDependent.integral_sq_sum`, `IsOneDependent.tendsto_charFun_bigBlock`, `oneDepVariance`, `IsOneDependent.tendstoInDistribution` (the CLT for stationary one-dependent sequences), `tendsto_of_approx`, `IsOneDependent.integral_sq_sub_bigBlock_le` |
| pp. 442–443 | The LIL by the same blocking and the i.i.d. LIL | `hasLIL_oneDependent` (the LIL for stationary one-dependent sequences), `HasLIL.comp_index`, `countBelow_succ_le`, in the proof of `theorem_17_3_6_lil_general` |

## §17.4.1 Poisson's equation

| Source | Claim | Lean |
| --- | --- | --- |
| (17.37), p. 443 | Poisson's equation `ĝ − Pĝ = g − π(g)` with forcing function `g` | `IsPoissonSolution P g ĝ c` (any constant `c`), `kernelInt` |
| p. 443 | Finite-valued solutions; if `ĝ(x₀)` is finite, the set where `ĝ` is finite is full and absorbing | Solutions are real-valued by type; the remark is not formalised |
| p. 443 | The difference of two solutions is harmonic | In the proof of `proposition_17_4_1` |
| Proposition 17.4.1, p. 443 | For a positive Harris chain, two solutions with `π(|ĝ| + |ĝ•|) < ∞` differ by a constant `π`-a.e. | `proposition_17_4_1` (a different proof; see corrections) |
| (17.38), p. 444 | With an atom, `ĝ = G_α(·, g) = E_x[Σ_{k=0}^{σ_α} g(Φₖ)]` solves Poisson's equation | Not formalised for an atom; the analogue for an `f`-regular set is Lemma 17.7.3 (ii) below |
| p. 444 | (V3) and Poisson's equation; for aperiodic `f`-regular chains `Σ |Pᵏg − π(g)| ≤ R(V + 1)` | `poissonSeries_abs_bound`, through the `f`-Norm Ergodic Theorem (carried) |
| (17.39), p. 445 | `ĝ = Σₖ (Pᵏg − π(g))` | `poissonSeries P π g` |
| Theorem 17.4.2, p. 445 | For a `ψ`-irreducible chain with (V3), `V` finite, `f ≥ 1`, `C` petite and `π(V) < ∞`, there is `R` with a solution `|ĝ| ≤ R(V + 1)` for every `|g| ≤ f` | `theorem_17_4_2_periodic` (every period), `theorem_17_4_2` (aperiodic, the series (17.39)) |
| (17.40), p. 445 | `K_{a_ε} = εK_{a_ε}P + (1 − ε)I` | `resolvent_eq_dirac_add_comp`, `integral_resolvent_eq` (`resolvent P ε`, every `ε`) |
| p. 445 | (V3) for the resolvent with a scaled `V` and the petite sets `Cₙ = {K(·, C) ≥ 1/n}` | `driftV3_resolvent_half` (`ε = 1/2`, `4V`, `1/n = (4b + 1)⁻¹`), `lintegral_resolvent_half_add_le`, `half_le_lintegral_resolvent_half`, `isPetite_resolvent_half_level`, `resolvent_half_irreducible_aperiodic`, `resolvent_half_hypotheses` |
| (17.41)–(17.42), pp. 445–446 | A solution `ĝ_ε` for `K_{a_ε}` gives `ĝ = ε(1 − ε)⁻¹K_{a_ε}ĝ_ε` for `P` | `isPoissonSolution_of_resolvent` (every `ε`), `exists_poisson_of_resolvent_half` |
| p. 446 | `Sₙ(g)` is a martingale plus a telescoping sum | `theorem_17_4_3` |
| (17.43), p. 446 | `Mₙ(g) = Σ_{k=1}^n [ĝ(Φₖ) − Pĝ(Φₖ₋₁)]` | `poissonMart P ĝ n` |
| Theorem 17.4.3, (17.44), p. 446 | For a positive Harris chain and `π(|ĝ|) < ∞`, `Sₙ(g) = Mₙ(g) + Pĝ(Φ₀) − Pĝ(Φₙ)` and `Mₙ(g)` is a `P_π`-martingale | `theorem_17_4_3` (an invariant probability suffices) |

## §17.4.2 The functional CLT for Markov chains

| Source | Claim | Lean |
| --- | --- | --- |
| (17.45), p. 447 | The interpolated partial-sum process `sₙ(t)` | `sumPath g n`, built from `polygonal` (`PathSpaceC01`); `polygonal_apply_floor` |
| Theorem 17.4.4, (17.46), p. 447 | For a positive Harris chain and a solution with `π(ĝ²) < ∞` and `γ_g² = π(ĝ² − (Pĝ)²) > 0`, `(nγ_g²)^{−1/2} sₙ ⇒ B`, standard Brownian motion on `[0, 1]`, from every initial condition | `theorem_17_4_4` (every initial law), `theorem_17_4_4_initial_state` (every `P_x`), `theorem_17_4_4_stationary` (`P_π`); `wienerMeasure` |
| p. 447 | Proof: by an extension of Proposition 17.1.6 it is enough to take `Φ₀ ∼ π` | `tendstoInDistribution_pathMeasure_of_stationary` (through Theorem 13.3.4 (i), carried; no aperiodicity), `pathMeasure_map_shift`, `integral_shift_eq`; see corrections |
| (17.47), p. 447 | `mₙ(t)`, the interpolated martingale | `polygonal n` applied to `poissonMart` |
| (17.48), p. 447 | `(nγ_g²)^{−1/2}|sₙ(t) − mₙ(t)| ≤ (nγ_g²)^{−1/2}(|Pĝ(Φ₀)| + max_{k≤n} |Pĝ(Φₖ)|)` | `norm_sumPath_sub_polygonal_poissonMart_le` |
| p. 447 | Jensen: `π((Pĝ)²) < ∞`; by Theorem 17.3.3, `n^{−1} max (Pĝ(Φₖ))² → 0` | `memLp_kernelInt_of_memLp`, `ae_eventually_abs_le_sqrt` |
| p. 448 | (D.8) for `Mₙ(g)`: the conditional variances are `Pĝ² − (Pĝ)²`, and the LLN | `condExp_sq_poisson_increment`, `condVar_poisson_tendsto`, `ae_tendsto_avg_condExp_shift` |
| p. 448 | (D.9) for `Mₙ(g)` by the LLN | `lindeberg_poisson` |
| Theorem 17.4.5, p. 448 | Under the conditions of Theorem 17.4.4 the CLT holds with (17.46), and `(nγ_g²)^{−1/2} max_{k≤n} Sₖ(g) ⇒ max_t B(t)` | `theorem_17_4_5_max`, `theorem_17_4_5_endpoint`, `theorem_17_4_5_clt_harris` (from the FCLT); the CLT directly: `theorem_17_4_5_clt_stationary` (`P_π`), `theorem_17_4_5_clt` (aperiodic), `theorem_17_4_5_clt_periodic`, `theorem_17_4_5_clt_initial` (every period); `continuous_eval_one_C01`, `continuous_supPath`, `supPath_polygonal` |

## §17.4.3 The representations of `γ_g²`

| Source | Claim | Lean |
| --- | --- | --- |
| (17.49), p. 448 | `γ_g² = π(ĝ² − (ĝ − g)²) = 2π(ĝḡ) − π(ḡ²)` | `poisson_variance_eq`, `integral_sq_poissonMart_increment` |
| (17.50), p. 448 | With the series (17.39), `γ_g² = π(ḡ²) + 2π(Σ_{k≥1} ḡPᵏḡ)`, hence (17.3) when sum and integral commute | Under the CLT moment condition: (17.56) in `theorem_17_5_3`, which proves the interchange |
| (17.51), p. 449 | The atom form of the variance | (17.13), `theorem_17_2_2_variance` |
| (17.52), pp. 449–450 | The atom form equals `E_π[2ĝ(Φ₀)ḡ(Φ₀) − ḡ²(Φ₀)]` for `ĝ = G_α(·, g)` | Not formalised by this computation. The identity of the cycle variance with `π(ĝ² − (Pĝ)²)` is proved for split skeletons under the CLT moment condition (`skelCLTVariance_eq_poissonVariance`, and for `m = 1` in the proofs of `theorem_17_5_3_lil`, `theorem_17_0_1_iv_lil`), by uniqueness of limits in distribution (`eq_of_tendstoInDistribution_gaussianReal`) |

## §17.5 Criteria for the CLT and the LIL

| Source | Claim | Lean |
| --- | --- | --- |
| p. 450 | The CLT moment condition on `V, f`: `Φ` ergodic, (V3) with `f ≥ 1`, `V` finite and `C` petite, and `π(V²) < ∞` | The hypotheses of `theorem_17_5_3` (with "ergodic" as aperiodicity, or positive Harris and aperiodicity where Harris recurrence is used); see corrections |
| p. 450 | `π(V²) < ∞` from Theorem 14.3.7 | Not used: `π(V²) < ∞` is a hypothesis |
| Lemma 17.5.1, p. 450 | A `V`-uniformly ergodic chain satisfies the CLT moment condition with `V' = (1 − √(1 − β))⁻¹√V` and `f = √V` | `lemma_17_5_1` ((V4) for a petite set in place of `V`-uniform ergodicity; `V' = (1 − ρ')⁻¹√V`) |
| Lemma 17.5.2 (i), p. 451 | Poisson's equation has a solution `|ĝ| ≤ R(V + 1)` for every `|g| ≤ f` | `lemma_17_5_2_i` (`ĝ = poissonSeries`, with `g, ĝ, Pĝ ∈ L²(π)`) |
| Lemma 17.5.2 (ii), (17.53), p. 451 | The split skeleton satisfies `Ě_α̌[(Σ_{ℓ<τ_α̌} Z_ℓ(f))²] < ∞`, hence (17.31) for `|g| ≤ f` | `lemma_17_5_2_ii` (every minorization of a skeleton on a set in `B⁺(X)`) |
| p. 451 | `f^{(m)}`-regularity of the split skeleton and `Ě_{xᵢ}[Σ_{k≤τ_α̌} Zₖ(f)] ≤ R₀R₁(V(x) + 1)` | `blockMeanE_le` (`R₁`), `lintegral_skelPreSumE_pathKernel_le`, `cycleSumE_le_sumBefore` |
| (17.54)–(17.55), pp. 451–452 | Second moments from `π(V²) < ∞` and `π(f²) < ∞` | `lintegral_sq_skelPreSumE_ne_top`, `lintegral_cycleSumE_skelFreshLaw`, `sq_skelPreSumE_le` |
| p. 452 | The final Markov property computation | In the proof of `lintegral_sq_skelPreSumE_ne_top` |
| Theorem 17.5.3, (17.56), p. 452 | Under the CLT moment condition and `|g| ≤ f`, `γ_g² = π(ĝ² − (Pĝ)²)` is well defined, non-negative and finite, equals `lim (1/n)E_π[Sₙ(ḡ)²]` and the absolutely convergent autocovariance series; if `γ_g² > 0` the CLT and LIL hold | `theorem_17_5_3` (variance), `theorem_17_5_3_clt` (CLT); LIL: `theorem_17_5_3_lil_poisson`, `theorem_17_5_3_lil_skeleton`, `theorem_17_5_3_lil` (one-step minorization); `tendsto_variance_poisson` |
| pp. 452–453 | Proof: `E_π[(Sₙ − Mₙ)²] ≤ 4π(ĝ²)`, `E_π[Mₙ²] = nγ_g²`, and absolute summability by the `f`-Norm Ergodic Theorem | `integral_sq_sum_of_martingale`, `poisson_increment_props`, `poissonSeries_abs_bound`, `integral_coord_zero_mul` |
| p. 453 | If `γ_g² = 0`, `n^{−1/2}Sₙ(ḡ) → 0` in distribution (left to the reader) | `theorem_17_5_3_degenerate` (almost surely, from every state), `tendsto_zero_of_poissonVariance_eq_zero` |
| Theorem 17.5.4, p. 453 | For a `V`-uniformly ergodic chain and `g² < V`, the conclusions of Theorem 17.5.3 hold, and `γ_g² = 0` gives `n^{−1/2}Sₙ(ḡ) → 0` a.s. | `theorem_17_5_4`, `theorem_17_5_4_clt`; LIL: `theorem_17_5_4_lil_poisson`, `theorem_17_5_4_lil_skeleton`; `g² ≤ V`; see corrections |
| p. 454 | Proof: `Mₙ(g)` converges by the martingale convergence theorem | Replaced by `tendsto_zero_of_poissonVariance_eq_zero` (the increments vanish `P_π`-a.s.; Proposition 17.1.6) |

## §17.6 Applications

| Source | Claim | Lean |
| --- | --- | --- |
| p. 454 | `V`-uniform models of Chapter 16 satisfy the CLT and LIL when the variance is positive | Not formalised for the Chapter 16 models (the Chapter 16 modules are not carried); `isPositiveHarris_of_driftV4` and `theorem_17_0_1` apply to any chain with (V4) |
| p. 454 | Random walk on a half line with negative mean and finite fifth moment: (V3) with `f = |x| + 1`, `V = cx²` from (14.29), and `V²`-regularity by Proposition 14.4.1 | `halfLine_cltMoment` (`halfLineWalkKernel Γ`, carried) |
| Proposition 17.6.1, p. 454 | The walk is positive Harris and the CLT and LIL hold for `{Φₖ}` | `proposition_17_6_1` (positive Harris, aperiodic, finite fourth moment of `π`), `proposition_17_6_1_clt`, `proposition_17_6_1_lil_poisson` |
| p. 455 | `γ² = Σ_{k∈ℤ} E_π[Φ̄ₖΦ̄₀]`, or the atom form (17.13) with `α = {0}` | `proposition_17_6_1_variance` (the autocovariance form and `π(ĝ² − (Pĝ)²)`); the atom form is not formalised |
| p. 455 | The linear state space model with `E[W] = 0`; the stationary version `Yₖ = Σ_ℓ h_ℓ W_{k−ℓ}` with `h_ℓ = cᵀF^ℓG` | `lssMatrixKernel Γ F G` (carried), `HasCentredSecondMoments Γ`; the moving-average representation is not formalised |
| (17.57), p. 455 | `γ_c² = Σ_{k∈ℤ} R(k)`, `R(k) = E_π[YₖY₀]` | `asymptoticVariance` (the series (17.3)) in `theorem_17_6_2_vector` |
| pp. 455–456 | The spectral density `D(ω) = H(e^{iω})Σ_W H(e^{iω})*` and its inversion | Not formalised; the variance is computed through Poisson's equation (`lss_poissonSeries`), which agrees with `D(0)` |
| Theorem 17.6.2, p. 456 | Under (LSS5), (LSS4) and (LCM3) the model is `V`-uniformly ergodic for `V = |x|² + 1`, `γ_c² = cᵀ(I − F)⁻¹GΣ_WGᵀ(I − Fᵀ)⁻¹c`, and the CLT and LIL hold for `Yₖ = cᵀXₖ` when `γ_c² > 0` | `theorem_17_6_2_vector` ((V4) for `V = 1 + xᵀMx`, `lss_driftV4`, `lyapunov_equation`; `lssLongRunCov`), `theorem_17_6_2_vector_clt`; scalar model: `theorem_17_6_2`, `theorem_17_6_2_clt`, `theorem_17_6_2_lil_poisson` (`ar1Kernel`, carried); `lss_irreducible_petite`; the LIL for `n > 1` is not formalised; see corrections |
| p. 456 | Proof: (V4) with `V = 1 + xᵀMx` (12.34); a `ψ`-irreducible aperiodic T-chain by Proposition 6.3.5 | `lss_driftV4`, `lyapunovMatrix`, `quadForm_lyapunov_mulVec`; `lss_irreducible_petite` (irreducibility and petite compact sets); aperiodicity is a hypothesis |
| p. 456 | A vector-valued CLT `n^{−1/2} Σ Xₖ ⇒ N(0, Σ)` | `theorem_17_6_2_vector_clt_vec` (Cramér–Wold, Mathlib's `multivariateGaussian`) |

## §17.7 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 456–459 | History: Doob, Athreya and Ney, Orey, Chung, Cogburn, Nummelin and Niemi, Neveu, Duflo, Maigret, Hall and Heyde, Kurtz, Bhattacharya, Glynn and Meyn, Brandt et al., Daley; the second-edition notes and the uses of Poisson's equation (i)–(vi) | Not formalised (commentary) |
| (17.58), p. 459 | The sensitivity formula of perturbation theory | Not formalised (commentary) |
| Theorem 17.7.1, p. 459 | For a `ψ`-irreducible chain with (V3), `V` finite, `f ≥ 1` and `C` petite, without `π(V) < ∞`, there is `B` with a solution `|ĝ| ≤ B(V + 1)` for every `|g| ≤ f` | `theorem_17_7_1_periodic` (every period, through the resolvent as in the book), `theorem_17_7_1` (aperiodic; a different proof, see corrections) |
| (17.59), p. 460 | The invariance equation `Ph = h − g + η` | `IsPoissonSolution P g h η` |
| p. 460 | `π(g) ≤ η` by the Comparison Theorem for nonnegative `g, h` | Not stated separately (the Comparison Theorem is carried) |
| (17.60), p. 460 | `V*(x) = G_C(x, f) = E_x[Σ_{k=0}^{σ_C} f(Φₖ)]` | `gKernelFn P C f` (carried) |
| Theorem 17.7.2, p. 460 | For a `ψ`-irreducible positive recurrent chain, `f ≥ 1` with `π(f) < ∞` and `C ∈ B⁺(X)`, `V*` is finite on a full absorbing set, and every solution of (17.59) with `g ∈ L∞_f`, `h ∈ L∞_{V*}` has `π(g) = η` | `theorem_17_7_2_periodic` (every period), `theorem_17_7_2` (aperiodic); `C` is `f`-regular; see corrections |
| Lemma 17.7.3, (17.61)–(17.62), pp. 460–461 | (i) `V*` finite on a full absorbing `X_f`; (ii) `PV* = V* − f*` with `f* = f − 1_C U_C(·, f)` of mean zero; (iii) `k⁻¹E_x[V*(Φₖ)] → 0` and `E_x[V*(Φₖ)1{τ_C > k}] → 0` on `X_f` | `lemma_17_7_3_periodic` (every period), `lemma_17_7_3` (aperiodic, (iii) at every `x` with `V*(x) < ∞`); `lintegral_pow_add_sum`, `tendsto_pow_gKernelFn_div_of_cesaro`; the second limit of (iii) is not formalised |
| (17.63), p. 461 | `V*(Φₘ)` as a conditional expectation on `{τ_C ≥ m}` | Not formalised (it serves only the second limit of Lemma 17.7.3 (iii)) |

## Appendix D.6 Some martingale theory

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem D.6.1, p. 561 | An `L¹`-bounded supermartingale converges a.s. | Mathlib's martingale convergence theorem (`Submartingale.ae_tendsto_limitProcess`), used in `InvariantFields`; not restated |
| Theorem D.6.2, p. 561 | A positive supermartingale converges a.s. | Not restated (Mathlib) |
| Theorem D.6.3 (i), p. 562 | Kolmogorov's inequality `P{max_{k≤n} |Mₖ| ≥ c} ≤ c^{−p}E|Mₙ|^p` for a martingale and `p ≥ 1` | `measureReal_sup_abs_ge_le` (even `p`), `measureReal_sup_abs_ge_le_sq` (`p = 2`); `kolmogorov_ineq`, `kolmogorov_ineq_shift` (sums of independent centred variables, `p = 2`) |
| Theorem D.6.3 (ii), p. 562 | `P{sup_k Mₖ ≥ c} ≤ c⁻¹E[M₀]` for a positive supermartingale | `measureReal_exists_ge_le` (Ville's inequality, over `k ≤ N` for every `N`) |
| (D.7), p. 562 | The interpolated martingale `mₙ(t)` | `polygonal n M` (`PathSpaceC01`) |
| p. 562 | `C[0, 1]` with the uniform norm is complete and separable; convergence in distribution of `mₙ` is weak convergence of the laws | `C(unitInterval, ℝ)` (Mathlib) with `[BorelSpace C(unitInterval, ℝ)]` hypotheses (`borelSpace_borel_C01`); `TendstoInDistribution` (Mathlib); `borel_le_of_measurable_eval`, `ext_of_fidiLin` |
| p. 563 | Standard Brownian motion: `B(0) = 0`, (i) continuous paths, (ii) independent increments, (iii) `B(t) − B(s) ∼ N(0, |t − s|)` | Constructed: `brownian`, `levyPath` (Lévy–Ciesielski), `wienerMeasure`; (i) `continuous_brownian`, `brownian_zero`; (ii) `indepFun_brownian_increment` (finite families of earlier times); (iii) `gaussSeq_map_brownian_sub`; `isGaussianProcess_brownian`, `covariance_brownian`, `eq_wienerMeasure_of_fidiLin` |
| Theorem D.6.4, (D.8)–(D.9), p. 563 | A square-integrable martingale with `(1/n) Σ E[(ΔMₖ)² | 𝓕ₖ₋₁] → γ² ∈ (0, ∞)` (D.8) and the conditional Lindeberg condition (D.9) has `(γ²n)^{−1/2}mₙ ⇒ B` | `theorem_D_6_4` (`M₀ = 0`); `martingale_fclt_lindeberg_one`; under uniformly integrable squares, `theorem_D_6_4_of_unifSqIntegrable`, `theorem_D_6_4_identDistrib`; with the squares themselves, `martingale_fclt` |
| p. 563 | "A consequence of Theorem 4.1 of [151]" | Proved here (`MartingaleFCLTGeneral`, `MartingaleFCLTGeneralTools`, `MartingaleFCLT`, `MartingaleArrayCLT`, `MartingaleUI`, `TightnessC01`, `WeakConvergenceC01`) |
