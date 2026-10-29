# Corrections and conventions

This file lists the places where a Lean statement differs from posts #1–#2 of the discourse
thread "Simulating a Markov chain: MC, QMC, RQMC" (topic 687): a claim corrected, a claim made
precise, a hypothesis made explicit, or a convention chosen. Three claims are false as stated.
Each is refuted in Lean by a counterexample of this project, and a corrected statement is proved:
requirement (i) as a condition for unbiasedness, "much lower variance than MC" for the shifted
lattice, and "at least as fast as QMC" on a given integrand. Three further claims are true under
one reading and false or incomplete under another; the reading is fixed and proved. The posts are
paraphrased and cited by paragraph as in the [source map](source-map.md). The last section lists
what is not formalised.

## Claims corrected

| Where | Posts | Lean |
| --- | --- | --- |
| 1. Requirement (i), #1 ¶9 and #2 ¶1, with stratification, #2 ¶3 | RQMC points must satisfy (i), each point marginally uniform, and the RQMC estimator is then unbiased. Stratification is presented as an RQMC method. | (i) is sufficient (`integral_sampleMean_of_hasLaw_uniformCube`) but not necessary, and stratification violates it: for `n ≥ 2` the point `(i + V)/n`, `V ~ U[0,1)`, is uniform on its stratum and not on `[0,1)` (`not_hasLaw_stratumMap`), yet the stratified estimator is unbiased (`integral_sampleMean_stratified`). The exact condition is that the marginal laws average to the target law, `Σᵢ law(zᵢ) = n • μ`. It implies unbiasedness for every integrable `f`, with no assumption on the joint law (`integral_sampleMean_of_sum_map_eq`). Conversely, unbiasedness for every indicator `1_A` implies it (`sum_map_eq_of_integral_sampleMean_indicator`). So it is equivalent to unbiasedness for all bounded measurable `f`. Stratified points satisfy it (`sum_map_stratumMap`, `sum_map_stratified`). A random relabelling of a stratified set would restore (i) without changing the estimator; this remark is not formalised. |
| 2. Low variance, #1 ¶9 and #2 ¶8 | RQMC gives "an unbiased and low-variance estimator"; the codes show that "RQMC is much lower variance than the MC". | True for independent stratification, for every `f ∈ L²` and every `n` (`variance_stratified_le_mc`; in any dimension `variance_sampleMean_partition_le`; for independent points whose laws average to `μ`, `variance_sampleMean_le_of_sum_map_eq`). False for the randomly shifted lattice, which is the common-shift rule (`sampleMean_fract_lattice`). For each `n ≥ 2`, the sawtooth `f(x) = fract (n x)` takes the value `U` at every shifted point (`fract_natCast_mul_stratumMap`). So the estimator is `U`, with variance `1/12 = Var(f)` (`variance_commonShift_sawtooth`), `n` times the MC variance `1/(12 n)` (`mc_variance_lt_commonShift_sawtooth`). The gain of a shifted lattice depends on the smoothness of `f`: the variance is at most `K²/(12 n²)` for `K`-Lipschitz `f` (`variance_commonShift_le_lipschitz`), and the sawtooth has `K = n`. For a fixed `f` the rates of the posts hold as `n → ∞`; they do not hold uniformly in `f`. |
| 3. Speed relative to QMC, #1 ¶8 and #2 ¶7 | RQMC converges "at least as fast as QMC", and has the same rates as QMC in most situations. | True for the worst-case (Koksma) bounds and rates, with a factor `2`: for every shift `u`, `D*ₙ(fract (x + u)) ≤ 2 D*ₙ(x)` (`starDiscrepancy_shiftMod_le`), so the error of every shifted estimate and the RMSE of the randomly shifted estimator are at most `2 V(f) D*ₙ(x)` (`abs_shiftedError_le`, `sqrt_integral_sq_shiftedError_le`). False for the error on a given integrand. The one-point midpoint rule `{1/2}` integrates `f(x) = x` exactly, while its random shift `fract (1/2 + U)` has mean squared error `1/12` (`shiftedMidpoint_counterexample`). The posts' "faster than QMC in a few situations" is not formalised as an integrand-level statement. |

## Claims made precise

| Where | Posts | Lean |
| --- | --- | --- |
| 4. Two stratified randomizations, #2 ¶8 | The codes apply "the same random shift to all" strata rather than one shift for each; "both are valid". | "Valid" is read as unbiased, and both are unbiased (`integral_sampleMean_stratified`, `integral_sampleMean_commonShift`). They are not equally good. With independent shifts the variance is at most `σ²/n` for every `f ∈ L²` (`variance_stratified_le_mc`) and at most `K²/(12 n³)` for `K`-Lipschitz `f` (`variance_stratified_le_lipschitz`). With a common shift the Lipschitz bound is `K²/(12 n²)` (`variance_commonShift_le_lipschitz`). Both rates are attained by `f(x) = x`, with variances `1/(12 n³)` and `1/(12 n²)` (`variance_stratified_id`, `variance_commonShift_id`). So for `n ≥ 2` the common shift is strictly worse, by the factor `n` (`variance_stratified_id_lt_commonShift_id`). It can even lose to MC (correction 2). |
| 5. The shifted lattice limit, #2 ¶6 | The limit law of a randomly-shifted lattice rule is "usually a spline", not a normal distribution (L'Ecuyer, Munger and Tuffin 2010). | Read in one dimension for the lattice `{i/n}` (generator `1`) and `f` that is `C¹` on `[0,1]`. Then `n (μ̂ₙ − μ) → (f(1) − f(0)) (U − 1/2)`, almost surely in the labelling `(i + U)/n` (`ae_tendsto_scaled_error`) and in distribution for the lattice labelling (`tendstoInDistribution_scaled_error_lattice`). The limit is *exactly* uniform on `[−\|c\|/2, \|c\|/2]`, a degree-0 spline, whenever `c = f(1) − f(0) ≠ 0` (`map_mul_sub_half_uniformIco`). When `f(1) = f(0)` it is the point mass at `0`. Then the error is `o(1/n)` and a finer scale is needed, which is not formalised. In every case the scaled error has no normal limit with positive variance, at the scale `n` (`not_tendstoInDistribution_scaled_error_gaussian`, `not_tendstoInDistribution_scaled_error_lattice_gaussian`) or at the MC scale `√n` (`not_tendstoInDistribution_sqrt_scaled_error_gaussian`, because `√n (μ̂ₙ − μ) → 0` almost surely, `ae_tendsto_sqrt_scaled_error`). For `f(x) = x` the scaled error is `U[−1/2, 1/2)` at every `n` (`hasLaw_scaled_error_id`, `hasLaw_scaled_error_id_lattice`). The higher-dimensional splines of L'Ecuyer, Munger and Tuffin are not formalised. |
| 6. Digital shift versus random shift, #2 ¶6 | With a digital net and a digital random shift the estimator is not normal; "in one dimension it is equivalent to a randomly-shifted lattice". | Read for the van der Corput sequence, the one-dimensional Sobol sequence. For `n = 2^m` its first `n` points are the lattice `{k/2^m}` (`image_vanDerCorput_digit`). For every `u ∈ [0,1)` the digitally shifted set and the randomly shifted set are equal (`image_digitalShift_eq_image_shiftMod_vanDerCorput`), so the estimators agree pointwise and in law (`qmcEstimate_digitalShift_eq_shiftMod_vanDerCorput`, `map_qmcEstimate_digitalShift_eq_shiftMod`). For every prefix `n ≤ 2^m` the equivalence holds in law but not pointwise. A measure-preserving permutation `ψ` of the dyadic cells moves the digitally shifted set at `u` onto the randomly shifted set at `ψ(u)` (`exists_measurePreserving_digitalShift_prefix`, `qmcEstimate_digitalShift_prefix_eq`, `map_qmcEstimate_digitalShift_prefix_eq`). The equivalence is not a property of every dyadic point set. For `{0, 1/8, 1/4}` with `m = 3` and `f = 1_{(−∞, 1/2)}`, the digitally shifted estimate is never `2/3`, while the randomly shifted one is `2/3` with probability at least `1/8` (`digitalShift_ne_shiftMod_counterexample`). The first three van der Corput points `{0, 1/2, 1/4}` give no counterexample (`map_digitalShift_three_eq`). Non-normality is proved for `f(x) = x` and `n = 2^m`, where the scaled error is `U[−1/2, 1/2)` (`hasLaw_scaled_error_digitalShift_id`, `scaled_error_digitalShift_ne_gaussianReal`). |

## Readings chosen

| Where | Posts | Lean |
| --- | --- | --- |
| #1 ¶7 | A low-discrepancy set has discrepancy falling faster than `n^{-1/2}`. | The discrepancy is the star discrepancy `D*ₙ` (`starDiscrepancy`). No `n`-point set in `[0,1)` has `D*ₙ < 1/(2n)` (`inv_two_mul_le_starDiscrepancy`), so the rate is at most `1/n`, which the midpoint rule attains (`starDiscrepancy_midpointRule`). The `n^{-1/2}` of random points is read as the MC RMSE `σ/√n` (`rmse_sampleMean_iid`). The discrepancy of random points is not formalised. |
| #1 ¶8 | QMC "will have a non-zero error". | The QMC error is deterministic and can be zero: the midpoint rule integrates `f(x) = x` exactly (`shiftedMidpoint_counterexample`, first conjunct). |
| #1 ¶10 | All of this "extends trivially" to `s` dimensions. | Unbiasedness (`integral_sampleMean_of_hasLaw_uniformCube`, `integral_sampleMean_shiftMod1`) and stratification by a partition into cells of equal measure (`variance_sampleMean_partition_le`) are proved in every dimension. Discrepancy, Koksma's inequality, the van der Corput sequence, the limit laws and the digital shift are one-dimensional. |
| #2 ¶4 | A "random diagonal shift in base 2". | The random digital shift: the first `m` binary digits of each point are XORed with those of one `U ~ U[0,1)` (`digitalShift`, `floor_two_pow_mul_digitalShift`). It is defined for points with at most `m` digits, such as the first `2^m` van der Corput points; for other points it is an `m`-digit implementation. |

## Hypotheses made explicit

| Where | Posts | Lean |
| --- | --- | --- |
| Point sets (#1 ¶7) | A set of `n` points in `[0,1)`. | The first `n` terms of a sequence `x : ℕ → ℝ`, with `InUnitIco x n` (every `xᵢ ∈ [0,1)`), so that sequences and finite sets share one type (`Discrepancy`). The random estimators of `MonteCarlo` and `Unbiased` use `x : Fin n → E`. |
| Star discrepancy (#1 ¶7) | "Some measure of discrepancy". | `D*ₙ = sup_{t ∈ [0,1]} \|#{i < n : xᵢ < t}/n − t\|`, with the half-open count (`starDiscrepancy`). The closed count `#{xᵢ ≤ t}` is bounded by the same `D*ₙ` (`countAtMost_div_sub_le_starDiscrepancy`). |
| MC (#1 ¶5) | `n` independent `U(0,1)` draws. | Draws with a common law `μ` (`HasLaw`, Mathlib), mutually independent (`iIndepFun`, Mathlib). Unbiasedness needs neither independence nor a common law, only averaged marginals. The variance results take `f ∈ L²(μ)` and the means take `f` integrable. The CLT takes an i.i.d. sequence and states the normal limit through a random variable `Z ~ N(0, σ²)` on another probability space. |
| Koksma (#1 ¶7) | Not stated in the posts. | `f` of bounded variation on `[0,1]` (`BoundedVariationOn`, Mathlib), `V(f) = (eVariationOn f [0,1]).toReal` (`totalVariation`), at least one point (`0 < n`). For `n = 0` the estimate is `0` and `D*₀ = 1`, and the inequality fails for a constant `f ≠ 0`. The `C¹` form asks for a derivative `HasDerivAt` at every point of `[0,1]`, two-sided at the end points, with `f'` interval integrable (`koksma_hasDerivAt`). |
| Stratification (#2 ¶3) | Intervals `[0, 1/3]`, `[1/3, 2/3]`, `[2/3, 1]`. | Half-open strata `[i/n, (i+1)/n)` (`stratum`), which partition `[0,1)`; the end points are a null set. The Lipschitz bounds take `f : ℝ → ℝ` with `LipschitzWith K f` on all of `ℝ` (Mathlib). |
| Limit laws (#2 ¶6) | A randomly-shifted lattice rule, `n → ∞`. | `f` is `C¹` on `[0,1]`: `HasDerivWithinAt f (f' x) [0,1] x` for every `x ∈ [0,1]`, with `f'` continuous on `[0,1]`. The random statements also take `f` measurable. "Not normal" means no convergence in distribution to `gaussianReal m v` (Mathlib) with `v ≠ 0`. A degenerate normal is not excluded, and at the scale `√n` the limit is the point mass at `0`. |
| Random shift (#2 ¶4, ¶8) | A random shift of a QMC set. | `fract (xᵢ + U)` with one `U ~ U[0,1)` (`shiftMod`); in `s` dimensions, coordinatewise (`shiftMod1`). The doubling bound holds for every shift `u ∈ ℝ` (`starDiscrepancy_shiftMod_le`). Unbiasedness holds for any points, in or out of `[0,1)`, and `f` interval integrable on `[0,1]` (`integral_qmcEstimate_shiftMod`). |
| Digital shift (#2 ¶4, ¶6) | A random digital shift of a digital net. | The `m`-digit digital shift with the terminating binary expansion of `u` (`digitalShift`). The non-terminating expansion gives `digitalShiftUpper`; the two differ on the dyadic grid, even by leaving `[0,1)` (`digitalShift_expansion_ambiguity`), but agree almost surely (`digitalShiftUpper_ae_eq`). The equalities in law take `f` measurable and `n ≤ 2^m`. |

## Conventions

* The uniform law is Lebesgue measure restricted to `[0,1)`, `uniformIco = volume.restrict
  (Ico 0 1)`, and on `[0,1)^s` it is the product `uniformCube s` on `Fin s → ℝ`. Points live in
  `ℝ` and `Fin s → ℝ` rather than in a subtype, so that shifts and affine maps are ordinary real
  functions.
* Integrals over `[0,1]` are interval integrals `∫ t in 0..1, f t`;
  `integral_uniformIco_eq_intervalIntegral` identifies them with `∫ f dU[0,1)`.
* Variances are Mathlib's `Var[f; μ]` (`ProbabilityTheory.variance`); the root-mean-square
  error is `√E[(μ̂ − μ)²]`.
* The van der Corput sequence starts at `φ(0) = 0`, with `φ(k) = (k mod 2)/2 + φ(⌊k/2⌋)/2`
  (`vanDerCorput`). `log` is the natural logarithm and `⌊log₂ n⌋` is `Nat.log 2 n` (Mathlib).
* The shifted lattice is studied in two labellings with the same point set,
  `{fract (i/n + U)}` and `{(i + fract (n U))/n}` (`sampleMean_fract_lattice`). The common-shift
  labelling `(i + U)/n` has the same law for every `n` and converges almost surely; the lattice
  labelling converges in distribution.

## Not formalised

* **Owen scrambling**: Loh's (2003) CLT for scrambled nets, Owen's (1997) variance theory, and
  the scrambles of the posts' codes (Owen's nested uniform scramble, Matlab's
  `MatousekAffineOwen`).
* **Several dimensions**: the `s`-dimensional star discrepancy, the Koksma–Hlawka inequality, the
  Sobol sequence and digital nets in `s` dimensions, rank-1 lattices other than `{i/n}`, and the
  spline limits of L'Ecuyer, Munger and Tuffin (2010) beyond one dimension.
* **Pseudo-random generators** (#1 PPS), for which the post claims no theorem.
* **Empirical claims**: the simulation studies (#1 ¶9) and what the codes show (#2 ¶8).
* **Informal remarks**: the MEP motivation (#1 ¶1–¶3), the variance of QMC (#1 ¶8), the
  structure of the three approaches (#2 ¶2), and the comparison with quadrature (#2 PS).
* **The inverse-CDF transformation** to other laws (#1 ¶10): the results hold for a general `f`
  and, for MC, a general law `μ`, but the transformation is not constructed.
* **Finer points**: the discrepancy `O(n^{-1/2})` of random points; the sharpness of the constant
  `1` in Koksma's inequality; the equality `V(f) = ∫₀¹ |f'|` (only `≤` is proved,
  `totalVariation_le_integral_abs_deriv`); the scale finer than `n` when `f(1) = f(0)`; a limit
  theorem for a general `C¹ f` under the digital shift; and the remark that the lattice labelling
  does not converge almost surely, since `fract (n U)` is equidistributed for irrational `U`
  (Weyl).
