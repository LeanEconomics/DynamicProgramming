# Corrections and conventions

This file lists the places where a Lean statement differs from post #2 of the discourse thread
"Simulating a Markov chain: MC, QMC, RQMC" (topic 687), or from the results it cites: a claim
corrected, a claim made precise, a hypothesis made explicit, or a convention chosen. The post's
claim is unqualified: with a digital net and Owen scrambling "a standard CLT applies". Two parts
of it are false as stated. Each is refuted in Lean, and a corrected statement is proved: the scale
of the CLT, and the class of integrands. These correct the post's wording, not Loh (2003), who
normalises by the standard deviation and assumes a smooth integrand. A technical note concerns
Owen's gain bound. Further claims are true under one reading and the reading is fixed and proved.
The post is paraphrased and cited by paragraph as in the [source map](source-map.md). The last
section lists what is not formalised.

## Claims corrected

| Where | Post | Lean |
| --- | --- | --- |
| 1. The scale, #2 ¶6 and ¶7 | Under MC the estimates are asymptotically normal; with a digital net and Owen scrambling "a standard CLT applies", and Owen scrambling is the exception that does not "mess with" the asymptotic properties of the estimator. | The "standard" CLT of MC is at the scale `√n`: `√n (X̄ₙ − μ) ⇒ N(0, σ²)` (`tendstoInDistribution_sampleMean_iid`). For scrambled nets there is no CLT at that scale. For every sequence of `(0,m,s)`-nets in base `b` with `1 ≤ s ≤ b + 1` and every measurable `f ∈ L²`, `Var(μ̂) = o(1/n)` (`tendsto_pow_mul_variance_scrambledLaw`), so by Chebyshev `P(\|√n (μ̂ − μ)\| ≥ ε) → 0` for every `ε > 0` (`tendsto_scrambledLaw_sqrt_error_ge`), and `√n (μ̂ − μ)` does not converge in distribution to any `N(m₀, v)` with `v ≠ 0` (`not_tendstoInDistribution_sqrt_scaled_error`). The corrected claim: the error divided by its own standard deviation `√Var(μ̂) = o(n^{-1/2})` is asymptotically `N(0,1)`. This is proved in one dimension for `C¹` non-constant `f` (`tendstoInDistribution_owenNet`, `tendstoInDistribution_deepNet`), where `σₙ ~ n^{-3/2} (∫₀¹ f'²/12)^{1/2}` (`tendsto_cube_mul_variance_owenNet`), and in every dimension for additive `f` (`tendstoInDistribution_scrambledLaw_addFn`), where `n³ Var(μ̂) → Σⱼ (1/12) ∫₀¹ gⱼ'²` (`tendsto_cube_mul_variance_scrambledLaw_addFn`). For `s = 2` and smooth non-additive `f` the normalisation is of order `n^{-3/2} √(log n)` (`variance_scrambledLaw_two_asymp`), but the CLT itself is not formalised there. |
| 2. The integrand, #2 ¶6 and ¶8 | "A standard CLT applies", with no condition on the integrand; the codes show normality "when Owen nested scrambling is used". | False for degenerate and for discontinuous integrands. (a) For constant `f` the scrambled net is exact for every realisation (`owenNet_exact_of_const`), `σₙ = 0` (`stratVar_const`), and the normalised error is identically `0`, which has no normal limit with positive variance (`not_tendstoInDistribution_owenNet_const`). (b) For `f = 1_{[0,1/3)}` and the base-`2` net, the variance is non-degenerate, `σₙ² ≥ (2/9)/n²` (`stratVar_indicator_third_ge`), but only the cell containing `1/3` is random, the normalised error is bounded by `3` for every realisation (`abs_normalised_error_indicator_le`), and it has no normal limit (`not_tendstoInDistribution_owenNet_indicator`). (c) In any dimension a scrambled `(0,m,s)`-net integrates a bounded step function on elementary cubes of level `R` exactly once `sR ≤ m`, for every scramble (`sampleMean_stepFn_scrambledPoint`, `scrambledLaw_stepFn_ne_eq_zero`), so for every normalisation `c_m` the normalised error has no normal limit (`not_tendstoInDistribution_stepFn`). The corrected claim assumes `f` measurable, `C¹` and not constant on `[0,1]` in one dimension (`tendstoInDistribution_owenNet`), or additive with such coordinates in `s` dimensions (`tendstoInDistribution_scrambledLaw_addFn`). Loh (2003) assumes a smooth integrand, so these are corrections of the post's wording, not of Loh. |

## Technical note

This concerns Owen's (1997a) bound, not the post.

| Where | Source | Lean |
| --- | --- | --- |
| 3. Owen's gain bound | For scrambled `(0,m,s)`-nets the gain coefficients satisfy `0 ≤ Γ_ℓ ≤ (b/(b−1))^{s−1}`, so `Var(μ̂) ≤ (b/(b−1))^{s−1} σ²/n`. | Proved for `s ≤ b + 1` (`gainCoeff_net_mem_Icc`, `variance_scrambledLaw_le`), and `Var(μ̂) ≤ e σ²/n` for `s ≤ b` (`variance_scrambledLaw_le_exp_one`). The gain coefficient of a component with `p` active coordinates is a value `G(p, L)` of a recursion (`gainCoeff_net`, `gainSeq`), and the bound `0 ≤ G(p, L) ≤ (b/(b−1))^{p−1}` holds for `1 ≤ p ≤ b + 1` (`gainSeq_mem_Icc`). It is not a property of the recursion alone: in base `2`, `G(4, 2) = −4` (`gainSeq_two_four_two`). This does not contradict Owen, since `(0,m,s)`-nets with `m ≥ 2` exist only for `s ≤ b + 1` (Niederreiter 1992), so no `(0,m,4)`-net in base `2` has such a component. The hypothesis `s ≤ b + 1` is stated in every theorem that uses the bound, including `o(1/n)` (`tendsto_pow_mul_variance_scrambledLaw`). |

## Claims made precise

| Where | Post | Lean |
| --- | --- | --- |
| 4. What the one-dimensional CLT needs, #2 ¶4 and ¶6 | Owen scrambling is a "nested uniform scramble", and with it a CLT applies. | In one dimension the law identity `hasLaw_owenNetSorted` and the CLT `tendstoInDistribution_owenNet` hold for ANY random tree independent of the remainders, not only the uniform one: what matters is that the scramble permutes the cells (`owenWord_injective`, `owenCell`) independently of the remainders. So the estimator law is the same for every random cell permutation independent of the remainders (`map_sampleMean_owenNet`, `identDistrib_sampleMean_owenNet`). The uniformity of the tree gives only the marginal uniformity of each point, requirement (i) of posts #1–#2 (`card_filter_owenCell`, `hasLaw_owenNet`). The exception is the genuine scramble to depth `m + d`: there the uniformity of the tree is what makes the scrambled zero digits below level `m` uniform and independent of the top (`card_filter_deepKey_eq`), and `hasLaw_deepNetSorted` and `tendstoInDistribution_deepNet` assume it. |
| 5. Nested uniform scrambling, #2 ¶4 | Owen's scramble permutes all base-`b` digits of every coordinate. | One dimension: `Owen1DScramble` scrambles the first `m` digits of `{k/bᵐ}` and completes each point by an independent `U[0,1)` remainder (`owenNet`). `Owen1DDeep` scrambles all `m + d` digits with a uniform tree of depth `m + d` (`deepNet`) and gives the same law for every `d` (`hasLaw_deepNetSorted`), so the depth-`m` model is exact, and the law is also that of the scramble of all digits in the projective sense (every finite-depth truncation with a uniform remainder has it). `s` dimensions: the scramble acts on `D` digits (`Scramble b D`, `scramble`) and is completed by independent `U[0,1)^s` remainders (`scrambledPoint`). For points whose `D`-digit prefixes are distinct in each coordinate, as for a `(0,m,s)`-net with `D ≥ m` (`injective_coord_net`), the full scramble should have the same law; this identification is not formalised in `s ≥ 2`. |
| 6. Digital nets, #2 ¶4 and ¶6 | A digital net, such as the Sobol sequence, with Owen scrambling. | A `(t,m,s)`-net in base `b ≥ 2`: `bᵐ` points with exactly `bᵗ` in every elementary box of volume `b^{t−m}` (`IsNet`). Net preservation (`isNet_scrambledPoint`), uniformity (`mixLaw_scrambledPoint`), unbiasedness (`integral_scrambledLaw`), the pair law and Owen's variance formula (`variance_scrambledLaw`) hold for every `t` or every point set. The bounds, `o(1/n)` and the CLTs are for `t = 0`, the case of Loh (2003). The one-dimensional net `{k/bᵐ}` is a `(0,m,1)`-net, and the Hammersley set a `(0,m,2)`-net in every base (`isNet_hammersley`). The post's Sobol points have `t > 0` in general once `s ≥ 3`. |
| 7. Normal under scrambling, not under shifting, #2 ¶6 | A digital random shift is not normal; Owen scrambling is. | In one dimension, for the same measurable `C¹` non-constant `f`, the scrambled net is asymptotically normal while the randomly shifted lattice has the uniform limit `n (μ̂ₙ − μ) ⇒ (f(1) − f(0)) (U − 1/2)` and no normal limit (`owenNet_normal_and_shift_not_normal`). The random shift is labelled `(i + U)/n`, the common-shift labelling of `ShiftLimit`. The digital shift is the nested scramble with the same translation at every node of a level (`digitShiftScramble`, `scramble_digitShiftScramble`); it lacks Owen's pair law (`digitShift_ne_pair_law`), the property on which the variance formula rests. Its non-normality for `f(x) = x` in one dimension is proved in `PointSets` (`DigitalShift`, not carried). |
| 8. Owen's rates, #2 ¶7 | Theory tells us that RQMC has faster rates than MC. | For scrambled nets: never worse than MC by more than `(b/(b−1))^{s−1}` (`variance_scrambledLaw_le`) or `e` (`variance_scrambledLaw_le_exp_one`), never worse than MC at all in one dimension (`variance_sampleMean_owenNet_le_mc`), `o(1/n)` for every `f ∈ L²` (`tendsto_pow_mul_variance_scrambledLaw`), `n⁻³` exactly for `C¹` `f` in one dimension and for additive `f` (`tendsto_cube_mul_variance_owenNet`, `tendsto_cube_mul_variance_scrambledLaw_addFn`), and `n⁻³ log n` for smooth `f` with an interaction in two dimensions (`variance_scrambledLaw_two_asymp`, `variance_scrambledLaw_prodFn`). |

## Hypotheses made explicit

| Where | Source | Lean |
| --- | --- | --- |
| Base and size | Base `b`, `n = bᵐ` points. | `1 < b` (some structural lemmas need only `0 < b` or `b ≠ 0`). The limits are along `m → ∞`, with `n = bᵐ`. |
| Smoothness, one dimension | A smooth integrand. | `f` measurable and `C¹` on `[0,1]`: `HasDerivWithinAt f (f' x) [0,1] x` for every `x ∈ [0,1]`, with `f'` continuous on `[0,1]`, as in `ShiftLimit`. `variance_owenNet_eq_stratVar` needs only `f` continuous on `[0,1]`. The variance bounds take `f ∈ L²(U[0,1))` or `LipschitzWith K f` on all of `ℝ`. |
| Non-degeneracy | Not stated. | `∃ x ∈ [0,1], f x ≠ f 0`; for `C¹` `f` it gives `∫₀¹ f'² > 0` and `σₙ > 0` for large `n` (`integral_sq_deriv_pos`, `eventually_stratVar_pos`). For additive `f`, at least one `gⱼ` not constant. |
| Independence, one dimension | The scramble and the digits below it are independent. | The tree `T` and the remainders `R ~ U[0,1)^n` are independent (`IndepFun`), both measurable; `R` has the law `uniformCube (bᵐ)`. The tree is uniform (`uniformOn univ`) for `hasLaw_owenNet`, `hasLaw_deepNetSorted` and `tendstoInDistribution_deepNet`, and of any law otherwise. The indicator counterexample holds for any trees and needs only the law of `R`. |
| The `s`-dimensional estimator | Independent uniform scrambles of the coordinates. | The law `scrambledLaw f d` on `ℝ`: the mixture `mixLaw` over the uniform scrambles `ρ : Fin s → Scramble b D` of the law under the remainders `remLaw s n`, i.i.d. `U[0,1)^s`. `f` is measurable and in `L²(U[0,1)^s)`. Variances are of this law. The CLT statements carry an instance `IsProbabilityMeasure (scrambledLaw f (d m))`, which holds (`isProbabilityMeasure_scrambledLaw`). |
| Digit points | A `(0,m,s)`-net. | Digit points `d : Fin n → Fin s → Fin D → Fin b` whose points `digitPoint (d i j) 0` form a net (`IsNet b 0 m`). The bounds take `m ≤ D`; the sequences of nets in `o(1/n)`, the CLTs and `LohVariance` take `D = m` and `n = bᵐ`. |
| Dimension | `s` dimensions. | `1 ≤ s ≤ b + 1` for the bounds, `o(1/n)` and the `√n` correction; `s ≤ b` for the `e` bound. The additive CLT has no bound on `s`, but `(0,m,s)`-nets with `m ≥ 2` exist only for `s ≤ b + 1`. |
| Smoothness, two dimensions (`LohVariance`) | Owen's (1997b) smooth integrands. | With `mixDiff f x x' = f(x₀,x₁) − f(x₀,x'₁) − f(x'₀,x₁) + f(x'₀,x'₁)`: `\|mixDiff f x x'\| ≤ M \|Δx₀\| \|Δx₁\|` on `[0,1)²`; `f` `L`-Lipschitz in the `ℓ¹` distance on `[0,1)²`; and a strict mixed derivative `g₀ ≠ 0` at some `xc ∈ [0,1)²`. The `_of_deriv` form takes `∂f/∂x₁` and `∂²f/∂x₀∂x₁` existing (`HasDerivAt`) at every point of `ℝ²`, the latter continuous on `[0,1]²` and non-zero at a point of `[0,1)²`, and `f` Lipschitz on the cube. |
| The Lindeberg CLT | A triangular array. | For each `n`, `L n` terms on a probability space `(Ωₙ, Pₙ)`, almost everywhere measurable, mutually independent (`iIndepFun`), centred, with `\|X n i\| ≤ δₙ` almost surely, `δₙ → 0`, and `Σᵢ E[(X n i)²] → v`. The limit is a random variable with law `gaussianReal 0 v` on another probability space. |
| "Normal" | Asymptotically normal. | Convergence in distribution (`TendstoInDistribution`, Mathlib) to a random variable with law `gaussianReal 0 1`. "No normal limit" means no convergence to `gaussianReal m₀ v` with `v ≠ 0`; a degenerate normal is not excluded, and at the scale `√n` the limit is the point mass at `0`. |
| Loh's hypotheses | Loh (2003). | Described from the summary in Basu and Mukherjee (2017): a scrambled `(0,m,s)`-net, an integrand whose mixed partial `∂ˢf/∂x₁⋯∂x_s` satisfies a Hölder condition, and a lower bound on the variance. Loh's full text was not consulted for this formalisation. The Lean CLTs replace them by `C¹` coordinates of an additive `f`, under which the variance is computed exactly. |

## Conventions

* Digits are most significant first. A word or string `w : Fin D → Fin b` has the cell index
  `Σ_k w_k b^{D−1−k}` (`digitEquiv`, `cellVal`), and the point with remainder `u` is
  `(cell + u)/b^D` (`digitPoint`).
* A one-dimensional Owen tree `OwenTree b m` and an `s`-dimensional nested scramble
  `Scramble b D` are finite types of node permutations; "uniform" is the uniform law on them
  (`uniformOn univ` in one dimension, the average in `mixLaw` in `s` dimensions).
* The one-dimensional scrambled net is relabelled by cell (`owenNetSorted`, `deepNetSorted`) to
  compare it with `stratifiedLaw n`; the estimator does not change (`sampleMean_owenNet`).
* `stratVar n f = n⁻² Σᵢ Var_{u ~ U[0,1)} f((i + u)/n)` is the variance of the stratified and of
  the scrambled estimator; the one-dimensional CLTs normalise by `√(stratVar n f)`.
* The base-`b` Haar components are `haarVar (cellAvg f) ℓ` for `ℓ : Fin s → Fin (D + 1)`, and the
  within-cell part is `cellResVar b D f`. The gain coefficients `gainCoeff b d ℓ` are those of
  the point set `d`.
* Uniform laws, sample means and variances are those of `PointSets`: `uniformIco`,
  `uniformCube s`, `sampleMean`, and Mathlib's `Var[·; ·]`.

## Not formalised

* **Loh's CLT for non-additive integrands in `s ≥ 2` dimensions.** For smooth non-additive `f` in
  two dimensions the average conditional variance given the scramble is `n⁻¹ σ²_{>D}`
  (`avg_variance_scrambledEstimate`) and is a vanishing share of `Var(μ̂)`
  (`tendsto_avg_variance_given_scramble_div`). By the law of total variance almost all of the
  variance is the fluctuation of `E[μ̂ | ρ]` under the nested scramble alone, where the points are
  dependent. So the Lindeberg argument conditional on the scramble, which proves the additive
  case, cannot give the general CLT, and conditioning on the top levels does not split the points
  into independent blocks once `s ≥ 2`. The general case needs Loh's Stein-method argument.
* **The order `(log n)^{s−1}` for general `s`**: Owen's (1997b) `Var = O(n⁻³ (log n)^{s−1})` is
  proved, with a matching lower bound, for `s = 2` only.
* **Nets with `t > 0`**: Owen's `(t,m,s)` bounds, and `o(1/n)` and the CLT for them.
* **The infinite-depth scramble in `s ≥ 2` dimensions**: the identification of the finite-depth
  scramble with uniform remainders with the scramble of all digits (done in one dimension,
  `hasLaw_deepNetSorted`).
* **Other constructions**: the Sobol sequence in several dimensions, Matlab's
  `MatousekAffineOwen` scramble and other linear scrambles, and the scrambling of sequences
  (as opposed to nets of `bᵐ` points).
* **Empirical claims**: what the codes show (#2 ¶8).
