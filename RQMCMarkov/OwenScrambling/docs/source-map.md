# Source map

Robert Kirkby, "Simulating a Markov chain: MC, QMC, RQMC", VFI Toolkit discourse, topic 687,
post #2 (28 October 2026),
<https://discourse.vfitoolkit.com/t/simulating-a-markov-chain-mc-qmc-rqmc/687>. For Owen
scrambling the post cites Loh, "On the asymptotic distribution of scrambled net quadrature",
*Annals of Statistics* (2003), doi 10.1214/aos/1059655914. The results on scrambled nets behind
the claim are those of Owen: "Randomly permuted `(t,m,s)`-nets and `(t,s)`-sequences", in *Monte
Carlo and Quasi-Monte Carlo Methods in Scientific Computing*, Lecture Notes in Statistics 106
(1995; "Owen 1995"); "Monte Carlo variance of scrambled net quadrature", *SIAM Journal on
Numerical Analysis* (1997; "Owen 1997a"); and "Scrambled net variance for integrals of smooth
functions", *Annals of Statistics* (1997; "Owen 1997b"). The module docstrings also cite
Niederreiter (1992) for `(t,m,s)`-nets and the Hammersley set, and Basu and Mukherjee,
"Asymptotic normality of scrambled geometric net quadrature" (2017), arXiv 1705.03181.

**On the citation of Loh (2003).** Loh's full text was not available to the formalisation. His
hypotheses are described here, and in the module docstring of `LohCLT`, from the summary in
Basu and Mukherjee (2017): a scrambled `(0,m,s)`-net in base `b`, an integrand whose mixed
partial derivative `∂ˢf/∂x₁⋯∂x_s` satisfies a Hölder condition, and a lower bound on the
variance; the proof is by Stein's method.

The post is cited by paragraph as in the [PointSets source map](../../PointSets/docs/source-map.md):
"#2 ¶6" is the sixth paragraph of post #2. Each claim is quoted by a few words at most and
otherwise paraphrased. The "Reading" is the precise statement that the Lean results prove;
"Partial" marks a result proved only in part. Lean names are relative to
`RQMCMarkov.OwenScrambling`; names from Mathlib are marked as such, and names from `PointSets`
modules that are not carried here are marked `PointSets`.

Notation: `U[0,1)` is `uniformIco` and `U[0,1)^s` is `uniformCube s`. In one dimension the net is
`{k/bᵐ}`, `n = bᵐ`, the Owen tree is `T : OwenTree b m`, the scrambled net is `owenNet T r` (depth
`m`) or `deepNet T r` (depth `m + d`), and `σₙ² = stratVar n f`. In `s` dimensions the digit
points are `d : Fin n → Fin s → Fin D → Fin b`, a nested scramble is `ρ : Scramble b D`, the
scrambled point is `scrambledPoint`, the estimator's law is `scrambledLaw f d`, the gain
coefficients are `Γ_ℓ = gainCoeff b d ℓ` and the Haar components `σ²_ℓ = haarVar (cellAvg f) ℓ`.
Every place where a Lean statement departs from the post or the papers is listed in
[corrections](corrections.md).

## Post #2: Owen scrambling and the CLT

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| #2 ¶1 | RQMC points satisfy (i) each point marginally uniform and (ii) the set low-discrepancy | For scrambled nets: (i) every scrambled point is `U[0,1)^s`, whatever the digit point; (ii) every scramble maps a `(t,m,s)`-net to a `(t,m,s)`-net | (i) `mixLaw_scrambledPoint` (`ScrambleDefs`), `hasLaw_owenNet` (`Owen1DScramble`); (ii) `isNet_scrambledPoint` (`ScrambleDefs`); in one dimension, exactly one point per cell, `owenNet_mem_stratum` (`Owen1DScramble`) |
| #2 ¶4 | Owen scrambling is a "nested uniform scramble" of a digital net | Each digit of each coordinate is permuted by a permutation attached to the node of its prefix, all independent and uniform; nested: points of one `b`-adic interval go to one `b`-adic interval. One dimension at depth `m` and at every depth `m + d`; `s` dimensions on `D` digits plus uniform remainders | `OwenTree`, `owenWord`, `wordPrefix_owenWord_eq`, `owenWord_injective`, `owenCell`, `owenNet` (`Owen1DScramble`); `netWord`, `deepNet`, `deepNet_eq` (`Owen1DDeep`); `Scramble`, `scramble`, `agree_scramble_iff`, `scramble_bijective`, `scrambledPoint`, `mixLaw` (`ScrambleDefs`). Partial: the infinite-depth scramble is identified only in one dimension (`hasLaw_deepNetSorted`); see corrections |
| #2 ¶4 | Owen scrambling is "more powerful" than the random diagonal shift in base 2, but costlier | The digital shift is the nested scramble with one translation per level; it lacks Owen's pair law, on which the variance formula rests. The cost is not formalised | `digitShiftScramble`, `scramble_digitShiftScramble`, `digitShift_ne_pair_law` (`LohCLT`); `card_scramble_pair` (`ScrambleDefs`) |
| #2 ¶6 | Under MC the estimates are asymptotically normal | `√n (X̄ₙ − μ) ⇒ N(0, σ²)` for i.i.d. draws, from Mathlib's CLT | `tendstoInDistribution_sampleMean_iid` (`MonteCarlo`, carried) |
| #2 ¶6 | A randomly-shifted lattice and a digital random shift are not normal | One dimension: the random shift has the uniform limit `n (μ̂ₙ − μ) ⇒ (f(1) − f(0)) (U − 1/2)` and no normal limit; for `f(x) = x` the digitally shifted error is `U[−1/2, 1/2)` | `owenNet_normal_and_shift_not_normal` (`Owen1DCLT`); `tendstoInDistribution_scaled_error`, `not_tendstoInDistribution_scaled_error_gaussian` (`ShiftLimit`, carried); `hasLaw_scaled_error_digitalShift_id` (`PointSets`, `DigitalShift`) |
| #2 ¶6 | With a digital net and Owen scrambling "a standard CLT applies" and the limit is normal (Loh 2003) | `(μ̂ − μ)/√Var(μ̂) ⇒ N(0,1)` as `n = bᵐ → ∞`. One dimension: for measurable `f`, `C¹` and not constant on `[0,1]`, at depth `m` and at every depth. `s` dimensions: for additive `f = Σⱼ gⱼ(xⱼ)` with `C¹` coordinates, one not constant, and `(0,m,s)`-nets. Two dimensions: for `a x₀ x₁ + g₀(x₀) + g₁(x₁)` with `a ≠ 0` and `C¹` `g_j`. False at the scale `√n` and for degenerate or discontinuous `f` | `tendstoInDistribution_owenNet`, `owenNet_normal_and_shift_not_normal` (`Owen1DCLT`); `tendstoInDistribution_deepNet` (`Owen1DDeep`); `tendstoInDistribution_scrambledLaw_addFn`, `tendstoInDistribution_scrambledLaw_hammersley` (`LohCLT`); `tendstoInDistribution_scrambledLaw_bilinAdd`, `tendstoInDistribution_scrambledLaw_prodFn_hammersley` (`LohGeneralCLT`). Partial: general smooth non-additive `f` in `s ≥ 2` is not formalised. Counterexamples: `not_tendstoInDistribution_sqrt_scaled_error`, `not_tendstoInDistribution_stepFn` (`LohCLT`), `not_tendstoInDistribution_owenNet_const` (`Owen1DCLT`), `not_tendstoInDistribution_owenNet_indicator` (`Owen1DCounterexample`); see corrections |
| #2 ¶7 | RQMC "can mess with" the asymptotic properties, except Owen scrambling with a digital net | As in #2 ¶6: normal after normalising by the true standard deviation, not at the MC scale | As in #2 ¶6; `tendsto_scrambledLaw_sqrt_error_ge` (`LohCLT`) |
| #2 ¶7 | RQMC has faster rates than MC | For scrambled nets: never worse than MC by more than `(b/(b−1))^{s−1}` or `e`, `o(1/n)` for every `f ∈ L²`, `n⁻³` for `C¹` `f` in one dimension and additive `f`, `n⁻³ log n` for `s = 2` with an interaction | `variance_scrambledLaw_le`, `variance_scrambledLaw_le_exp_one` (`ScrambleVariance`); `tendsto_pow_mul_variance_scrambledLaw` (`ScrambleAsymptotic`); `tendsto_cube_mul_variance_owenNet` (`Owen1DCLT`); `tendsto_cube_mul_variance_scrambledLaw_addFn` (`LohCLT`); `variance_scrambledLaw_two_asymp` (`LohVariance`) |
| #2 ¶8 | The codes use Sobol + Owen scrambling and Matlab's `MatousekAffineOwen`; RQMC is not normal "except when Owen nested scrambling is used" | Empirical; the Sobol sequence in several dimensions and the affine scramble are not defined | Not formalised |

## Owen (1995): uniformity and net preservation

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| Owen 1995 | The nested scramble preserves and reflects common prefixes and permutes the strings | For every scramble, two strings share `k` leading digits exactly when their images do; the scramble is a bijection | `agree_scramble_iff`, `scramble_injective`, `scramble_bijective`, `commonPrefix_scramble` (`ScrambleDefs`); `wordPrefix_owenWord_eq`, `owenWord_injective`, `owenWordEquiv` (`Owen1DScramble`) |
| Owen 1995 | Each scrambled point is uniform on `[0,1)^s` | Under the uniform scramble each string goes to each string with probability `b^{-D}`, so with uniform remainders each scrambled point is `U[0,1)^s` for every digit point | `card_scramble_fiber_eq`, `card_scramble_fiber_mul`, `sum_map_digitPoint_scramble`, `mixLaw_scrambledPoint` (`ScrambleDefs`); `card_filter_owenCell`, `hasLaw_owenNet` (`Owen1DScramble`) |
| Owen 1995 | The scrambled estimator is unbiased | `E[μ̂] = ∫ f` for any digit points and measurable `f ∈ L²` | `integral_scrambledLaw` (`ScrambleVariance`); `integral_sampleMean_owenNet` (`Owen1DScramble`) |
| Owen 1995 | A scrambled `(t,m,s)`-net is a `(t,m,s)`-net | For EVERY scramble, not only almost surely, and all remainders in `[0,1)`, when the digit points have `D ≥ m − t` digits | `IsNet`, `elemBox`, `boxIndex`, `mem_elemBox_iff`, `isNet_scrambledPoint` (`ScrambleDefs`) |
| Owen 1995 | Scrambled `(t,s)`-sequences | — | Not formalised |

## Owen (1997a): the variance of scrambled net quadrature

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| Owen 1997a | The pair law: the joint law of two scrambled points depends only on their common leading digits | Two strings with exactly `k` common leading digits go to a pair uniform on the pairs with exactly `k` common leading digits; coordinatewise in `s` dimensions; for the real points with remainders | `commonPrefix`, `pairKernel`, `card_scramble_pair` (`ScrambleDefs`); `scrambleVec`, `card_scrambleVec_pair`, `prod_pairKernel_eq_sum` (`ScrambleHaar`); `mixLaw_scrambledPoint_pair_eq` (`ScrambleVariance`) |
| Owen 1997a | The base-`b` Haar (nested ANOVA) decomposition of `f` | On the digit grid: averaging and detail kernels, Haar kernels `haarKernel ℓ`, components `σ²_ℓ ≥ 0` adding to the mean square; `Var f = σ²_{>D} + Σ_{ℓ≠0} σ²_ℓ`, with the within-cell part `σ²_{>D}` | `agreeKernel`, `detailKernel`, `haarKernel`, `sum_haarKernel`, `haarVar`, `haarVar_nonneg`, `sum_haarVar`, `haarVar_zero` (`ScrambleHaar`); `cellAvg`, `cellResVar`, `cellResVar_nonneg`, `variance_eq_cellResVar_add` (`ScrambleVariance`) |
| Owen 1997a | Owen's variance formula with gain coefficients | `E[(Σᵢ F(σ dᵢ))²] = n Σ_ℓ Γ_ℓ σ²_ℓ`; `Var(μ̂) = n⁻¹ (σ²_{>D} + Σ_{ℓ≠0} Γ_ℓ σ²_ℓ)` for any digit points, `Γ_0 = n` | `gainWeight`, `pairKernel_eq_sum`, `gainCoeff`, `gainCoeff_zero`, `sum_sq_sum_scrambleVec` (`ScrambleHaar`); `variance_scrambledLaw` (`ScrambleVariance`) |
| Owen 1997a | The gain coefficients of a `(0,m,s)`-net | `Γ_ℓ = G(p, (m − \|κ\|)₊)` with `p` active coordinates; closed form; `Γ_ℓ = 0` when `Σⱼ ℓⱼ ≤ m` | `card_agree_net`, `gainSeq`, `gainCoeff_net`, `gainSeq_eq_altSum`, `gainSeq_eq_zero`, `gainCoeff_net_eq_zero` (`ScrambleGain`) |
| Owen 1997a | `Var(μ̂) ≤ (b/(b−1))^{s−1} σ²/n` for `(0,m,s)`-nets, at most `e σ²/n` when `b ≥ s` | `0 ≤ Γ_ℓ ≤ (b/(b−1))^{s−1}` for `s ≤ b + 1`; the variance bounds for measurable `f ∈ L²`; the `e` bound for `s ≤ b`. The bound needs `s ≤ b + 1` | `gainSeq_mem_Icc`, `gainCoeff_net_mem_Icc` (`ScrambleGain`); `variance_scrambledLaw_le`, `variance_scrambledLaw_le_exp_one` (`ScrambleVariance`); `variance_scrambledLaw_hammersley_le` (`LohCLT`); `gainSeq_two_four_two` (`ScrambleGain`); see corrections. In one dimension the bound is `1`: `variance_sampleMean_owenNet_le_mc` (`Owen1DScramble`) |
| Owen 1997a | Bounds for `(t,m,s)`-nets with `t > 0` | — | Not formalised |
| Owen 1997a | `Var(μ̂) = o(1/n)` for every square-integrable `f` | For sequences of `(0,m,s)`-nets with `1 ≤ s ≤ b + 1` and measurable `f ∈ L²`, `n Var(μ̂) → 0`. Proved through exactness on step functions and their density in `L²` rather than the infinite Haar expansion | `card_box_net_of_le`, `stepFn`, `sampleMean_stepFn_scrambledPoint`, `variance_scrambledLaw_sub_of_exact`, `exists_stepFn_approx`, `tendsto_pow_mul_variance_scrambledLaw` (`ScrambleAsymptotic`); `tendsto_variance_scrambledLaw_hammersley` (`LohCLT`) |

## Owen (1997b): smooth integrands

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| Owen 1997b | For smooth `f`, `Var(μ̂) = O(n⁻³ (log n)^{s−1})` | Partial: `s = 2` only, with a matching lower bound. For `f` Lipschitz with bounded mixed differences, `n³ Var(μ̂) ≤ 4 L² + 64 M² b² (m + 1)`; with a non-zero strict mixed derivative at a point, `n³ Var(μ̂) ≥ c m` eventually, so `Var(μ̂) ≍ n⁻³ log n`. For `f = x₀ x₁`, explicit bounds for every `m` | `mixDiff`, `haarProj_cellAvg_eq`, `haarVar_cellAvg_le`, `haarVar_cellAvg_ge`, `gainCoeff_lvec2`, `pow_mul_variance_scrambledLaw_two_le`, `pow_mul_variance_scrambledLaw_two_ge`, `variance_scrambledLaw_two_asymp`, `variance_scrambledLaw_two_asymp_of_deriv`, `prodFn`, `variance_scrambledLaw_prodFn` (`LohVariance`). General `s` is not formalised |
| Owen 1997b | (The rate in one dimension and for additive `f`) | `n³ Var(μ̂) → (1/12) ∫₀¹ f'²` for `C¹` `f` in one dimension; `Var ≤ K²/(12 n³)` for `K`-Lipschitz `f`; `n³ Var(μ̂) → Σⱼ (1/12) ∫₀¹ gⱼ'²` for additive `f`, with no `log n` factor | `tendsto_cube_mul_stratVar` (`Owen1DVariance`); `tendsto_cube_mul_variance_owenNet` (`Owen1DCLT`); `variance_sampleMean_owenNet_le_lipschitz` (`Owen1DScramble`); `variance_scrambledLaw_addFn`, `tendsto_cube_mul_variance_scrambledLaw_addFn` (`LohCLT`) |

## Loh (2003): the CLT

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| Loh 2003 | For a scrambled `(0,m,s)`-net and a smooth integrand (hypotheses as summarised by Basu and Mukherjee 2017), `(μ̂ − μ)/√Var(μ̂) ⇒ N(0,1)` as `m → ∞` | One dimension, base `b ≥ 2`: for measurable `f`, `C¹` and not constant on `[0,1]`, at depth `m` and for the genuine scramble at any depths | `tendstoInDistribution_owenNet` (`Owen1DCLT`); `tendstoInDistribution_deepNet` (`Owen1DDeep`) |
| Loh 2003 | (The same, `s ≥ 2`) | Partial: additive `f = Σⱼ gⱼ(xⱼ)`, each `gⱼ` measurable and `C¹` on `[0,1]`, one not constant, any sequence of `(0,m,s)`-nets, every `s`; the CLT also holds given every fixed sequence of scrambles. Non-additive `f`: for `s = 2` and `f = a x₀ x₁ + g₀(x₀) + g₁(x₁)`, `a ≠ 0`, `g_j` `C¹`, any sequence of `(0,m,2)`-nets in base `b ≥ 2`, by conditioning on the scramble of coordinate `0` only (almost all of the variance comes from the scramble, so conditioning on all of it fails). General smooth `f` and `s ≥ 3` are not formalised | `injective_coord_net`, `addFn`, `addTerm`, `sum_addTerm`, `abs_addTerm_le`, `tendstoInDistribution_scrambledEstimate_addFn`, `tendsto_avg_of_forall`, `tendstoInDistribution_scrambledLaw_addFn`, `tendstoInDistribution_scrambledLaw_hammersley` (`LohCLT`); the obstruction: `avg_variance_scrambledEstimate`, `tendsto_avg_variance_given_scramble_div` (`LohVariance`); `nodeTerm`, `prodS_eq_sum_nodeTerm`, `integral_scrambledEstimate_prodFn` (`LohGeneralProd`); `tendsto_unifAvg_cexp_nodeSum` (`LohGeneralFinite`); `condVar`, `unifAvg_abs_condVar_sub_le`, `unifAvg_levelVar_mul` (`LohGeneralConc`); `unifAvg_condVar_ge`, `tendsto_unifAvg_cexp_prodS`, `tendstoInDistribution_scrambledLaw_of_condMean`, `tendstoInDistribution_scrambledLaw_bilinAdd`, `tendstoInDistribution_scrambledLaw_prodFn`, `tendstoInDistribution_scrambledLaw_prodFn_hammersley` (`LohGeneralCLT`) |
| Loh 2003 | (A lower bound on the variance) | `σₙ > 0` for large `n` when `f` is `C¹` and not constant (one dimension), and for additive `f` with one coordinate not constant; `n³ Var(μ̂) ≥ c m` for `s = 2` and smooth `f` with a non-zero mixed derivative | `integral_sq_deriv_pos`, `eventually_stratVar_pos` (`Owen1DVariance`); `pow_mul_variance_scrambledLaw_two_ge` (`LohVariance`) |
| Loh 2003 | (The proof, by Stein's method) | Replaced, where the CLT is proved, by a conditional Lyapunov CLT with a concentrating conditional variance in the non-additive case (`LohGeneralFinite`, `LohGeneralConc`), and otherwise by a bounded Lindeberg CLT for triangular arrays, proved from scratch by characteristic functions and Lévy's continuity theorem (Mathlib's `ProbabilityMeasure.tendsto_iff_tendsto_charFun`), applied to independent stratified sampling | `norm_prod_sub_prod_le`, `norm_charFun_sub_le_of_abs_le`, `tendstoInDistribution_sum_of_bounded` (`Owen1DLindeberg`); `cellTerm`, `tendstoInDistribution_stratified`, `tendstoInDistribution_stratified_all_n` (`Owen1DCLT`). Stein's method is not formalised |
| Loh 2003, as cited in #2 ¶6 | (The normalisation and the integrand) | The limit is at the scale `√Var(μ̂) = o(n^{-1/2})`, not `√n`, and needs a smooth non-degenerate `f` | `not_tendstoInDistribution_sqrt_scaled_error`, `not_tendstoInDistribution_stepFn` (`LohCLT`); `not_tendstoInDistribution_owenNet_const` (`Owen1DCLT`); `not_tendstoInDistribution_owenNet_indicator` (`Owen1DCounterexample`); see corrections |

## Supporting results

| Source | Claim | Reading | Lean |
| --- | --- | --- | --- |
| (Background) | In one dimension a scrambled net is stratified sampling | Relabelled by cell, the scrambled `{k/bᵐ}` has exactly the law of one independent uniform point per cell, for any random tree independent of the remainders at depth `m`, and for a uniform tree at every depth `m + d` | `stratPoints`, `stratifiedLaw`, `hasLaw_owenRemainder`, `owenNetSorted_eq_stratPoints`, `hasLaw_owenNetSorted`, `map_sampleMean_owenNet`, `variance_sampleMean_owenNet` (`Owen1DScramble`); `card_filter_deepKey_eq`, `sum_measure_preimage_digitShift`, `hasLaw_deepRemainder`, `hasLaw_deepNetSorted`, `variance_deepNet_eq_stratVar` (`Owen1DDeep`) |
| Niederreiter 1992 | The Hammersley set `{(i/bᵐ, φ_b(i))}` is a `(0,m,2)`-net in base `b` | Every base `b ≥ 2` and every `m` | `revDigits`, `hammersleyDigits`, `eq_of_agree_of_agree_rev`, `isNet_hammersley` (`ScrambleHammersley`) |
| Niederreiter 1992 | `(0,m,s)`-nets with `m ≥ 2` exist only for `s ≤ b + 1` | Used to explain the hypothesis `s ≤ b + 1`; not proved | — |
