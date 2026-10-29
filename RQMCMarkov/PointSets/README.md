# MC, QMC and RQMC for uniform point sets, in Lean

This is the `RQMCMarkov/PointSets` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It
formalises the mathematical claims of posts #1–#2 of Robert Kirkby, "Simulating a Markov chain:
MC, QMC, RQMC", VFI Toolkit discourse, topic 687 (October 2026),
<https://discourse.vfitoolkit.com/t/simulating-a-markov-chain-mc-qmc-rqmc/687>, together with the
results from the literature that the posts rely on: L'Ecuyer's tutorial *Randomized Quasi-Monte
Carlo: An Introduction for Practitioners* (MCQMC 2016), L'Ecuyer, Munger and Tuffin (2010) on the
error distribution of randomly shifted lattice rules, and Loh (2003) and Owen (1997) on scrambled
nets. It is the first project of the plan in [PROPOSAL-RQMCMarkov.md](../../PROPOSAL-RQMCMarkov.md)
(§1). Post #3, on Markov chains, is not covered here. Run the commands below from this directory.
[Return to the library index](../../README.md).

The posts estimate `μ = ∫₀¹ f` from `n` points. Monte Carlo (MC) averages `f` over `n` independent
uniform draws. Quasi-Monte Carlo (QMC) averages over a deterministic set of points that is spread
out evenly, a *low-discrepancy* set. Randomized QMC (RQMC) randomizes a QMC set so that (i) each
point is marginally uniform and (ii) the set stays low-discrepancy. Post #2 describes three
randomizations: stratification with one random point per stratum, a random shift of a lattice
rule, and a random digital shift or Owen scrambling of a digital net (the Sobol sequence). It
also describes the limit laws: MC is asymptotically normal, a shifted lattice is "usually a
spline", a digital shift is not normal, and Owen scrambling satisfies a CLT. Everything here is
one-dimensional unless stated otherwise. The base-2 van der Corput sequence is the
one-dimensional Sobol sequence, and the lattice rule is `{i/n}`, the rank-1 lattice with
generator `1`. The library contains **231 theorems** in 11 modules. All of them are the
project's own; no modules are carried from other projects.

## What is proved

* **Monte Carlo** (`MonteCarlo`). For i.i.d. draws with law `μ` and `f ∈ L²(μ)`, the sample mean
  is unbiased (`integral_sampleMean_iid`). Its variance is `σ²/n` (`variance_sampleMean_iid`) and
  its root-mean-square error is `σ/√n` (`rmse_sampleMean_iid`). The CLT
  `√n (X̄ₙ − μ) ⇒ N(0, σ²)` is `tendstoInDistribution_sampleMean_iid`, a restatement of Mathlib's
  CLT. Post #1's unlucky draw (all `n` draws below `1/10`) has probability `(1/10)ⁿ > 0`
  (`measure_all_draws_lt_tenth`). So for every `n` the MC estimate of `1/2` misses by more than
  `2/5` with positive probability, and MC has no worst-case error bound
  (`measure_sampleMean_far_pos`).
* **Unbiasedness** (`Unbiased`). Requirement (i) gives an unbiased estimator in any dimension `s`,
  with no assumption on the joint law (`integral_sampleMean_of_hasLaw_uniformCube`). A random
  shift modulo 1 of any fixed point set satisfies (i) (`measurePreserving_shiftMod1`,
  `integral_sampleMean_shiftMod1`). But (i) is not the exact condition. The exact condition is
  that the marginal laws *average* to the uniform law, `Σᵢ law(zᵢ) = n · U[0,1)^s`. It gives
  unbiasedness for every integrable `f` (`integral_sampleMean_of_sum_map_eq`), and it follows from
  unbiasedness for indicator functions (`sum_map_eq_of_integral_sampleMean_indicator`).
  Stratified points satisfy it (`sum_map_stratified`) but not (i) (`not_hasLaw_stratumMap`).
  Requirement (i) alone does not reduce the variance: `n` copies of one uniform point satisfy
  (i) and have the variance of a single draw (`variance_sampleMean_const`).
* **Stratification** (`Stratified`). One point `(i + Vᵢ)/n` in each stratum `[i/n, (i+1)/n)`.
  This is post #2's "midpoint plus `U(−1/6, 1/6)`" (`stratumMap_eq_midpoint_add`,
  `midpoint_shift_mem`). With independent `Vᵢ` the variance is at most the MC variance for every
  `f ∈ L²` (`variance_stratified_le_mc`); in any dimension, for a partition into cells of equal
  measure, this is `variance_sampleMean_partition_le`. For `K`-Lipschitz `f` the variance is at
  most `K²/(12 n³)`, of order `n⁻³` (`variance_stratified_le_lipschitz`). With one common shift
  `Vᵢ = U` the estimator is still unbiased (`integral_sampleMean_commonShift`), but the bound
  is only `K²/(12 n²)`, of order `n⁻²` (`variance_commonShift_le_lipschitz`). Both rates are
  attained by `f(x) = x`: the variances are `1/(12 n³)` and `1/(12 n²)`
  (`variance_stratified_id`, `variance_commonShift_id`,
  `variance_stratified_id_lt_commonShift_id`).
* **Star discrepancy and the midpoint rule** (`Discrepancy`). The star discrepancy is
  `D*ₙ = sup_{t ∈ [0,1]} |#{i < n : xᵢ < t}/n − t|` (`starDiscrepancy`). Every `n`-point set in
  `[0,1)` has `D*ₙ ≥ 1/(2n)` (`inv_two_mul_le_starDiscrepancy`), so no point set does better than
  order `1/n`. The midpoint rule `{(2i + 1)/(2n)}` attains this: `D*ₙ = 1/(2n)` exactly
  (`starDiscrepancy_midpointRule`), so it is optimal (`starDiscrepancy_midpointRule_le`). Post
  #2's set `{1/6, 1/2, 5/6}` is the case `n = 3`, with `D*₃ = 1/6`
  (`starDiscrepancy_midpointRule_three`).
* **Koksma's inequality** (`Koksma`). For `f` of bounded variation on `[0,1]` and `n ≥ 1` points
  in `[0,1)`, `|(1/n) Σᵢ f(xᵢ) − ∫₀¹ f| ≤ V(f) D*ₙ` (`koksma_boundedVariationOn`), with the
  constant `1` of Koksma (1942). It is proved first for monotone `f` by the layer-cake formula on
  both sides (`koksma_monotone`) and then through the Jordan decomposition. The `C¹` form, with
  `∫₀¹ |f'|` in place of `V(f)`, is `koksma_hasDerivAt`.
* **The van der Corput sequence** (`VanDerCorput`). Any `2^m` consecutive terms put exactly one
  point in each dyadic interval of length `2^{-m}` (`card_vanDerCorput_mem_dyadic`). Hence
  `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n` (`starDiscrepancy_vanDerCorput_le`), and `D*ₙ ≤ 2 (log n + 1)/n`. By
  Koksma, the QMC error for `f` of bounded variation is at most `V(f) · 2 (log n + 1)/n`
  (`abs_qmcError_vanDerCorput_le`). So `√n · |QMC error| → 0`: the error is `o(n^{-1/2})`,
  smaller than the MC error `σ/√n` (`tendsto_sqrt_mul_qmcError_vanDerCorput`).
* **The random shift** (`ShiftedQMC`). For every shift `u`, `D*ₙ(fract (x + u)) ≤ 2 D*ₙ(x)`
  (`starDiscrepancy_shiftMod_le`). So every shifted estimate has error at most `2 V(f) D*ₙ(x)`
  (`abs_shiftedError_le`), and the RMSE of the randomly shifted estimator is at most
  `2 V(f) D*ₙ(x)` (`sqrt_integral_sq_shiftedError_le`). For the shifted van der Corput sequence
  this gives RMSE at most `4 V(f) (log n + 1)/n` and `√n · RMSE → 0`
  (`tendsto_sqrt_mul_rmse_vanDerCorput`). This is "RQMC at least as fast as QMC" for the
  worst-case bounds, with a factor `2`. It fails for a given integrand
  (`shiftedMidpoint_counterexample`, see the corrections).
* **The random-shift limit law** (`ShiftLimit`, `ShiftLimitLattice`). The randomly shifted
  lattice `{fract (i/n + U)}` is the common-shift stratified rule, as a point set
  (`sampleMean_fract_lattice`). For `f` that is `C¹` on `[0,1]`,
  `n (μ̂ₙ − μ) → (f(1) − f(0)) (U − 1/2)`. The convergence is almost sure with the labelling
  `(i + U)/n` (`ae_tendsto_scaled_error`) and in distribution for the lattice
  (`tendstoInDistribution_scaled_error_lattice`). For `f(x) = x` the scaled error is exactly
  `U[−1/2, 1/2)` at every `n` (`hasLaw_scaled_error_id`, `hasLaw_scaled_error_id_lattice`). The
  limit law is uniform on `[−|c|/2, |c|/2]`, `c = f(1) − f(0)`, when `c ≠ 0`
  (`map_mul_sub_half_uniformIco`), and the point mass at `0` when `c = 0`. It is provably not
  normal. At the scale `n` the scaled error converges to no normal law with positive variance
  (`not_tendstoInDistribution_scaled_error_gaussian`,
  `not_tendstoInDistribution_scaled_error_lattice_gaussian`). At the MC scale `√n` it tends to
  `0` almost surely, so again no such normal limit exists
  (`not_tendstoInDistribution_sqrt_scaled_error_gaussian`).
* **The digital shift** (`DigitalShift`, `DigitalShiftPrefix`). The base-2 digital shift XORs the
  first `m` binary digits (`digitalShift`, `floor_two_pow_mul_digitalShift`). Each shifted point
  is uniform (`measurePreserving_digitalShift`), so the estimator is unbiased
  (`integral_qmcEstimate_digitalShiftSeq`). For `n = 2^m` the first `n` van der Corput points
  are the lattice `{k/2^m}` (`image_vanDerCorput_digit`). For every `u ∈ [0,1)`, their digital
  shift and their random shift are the same point set
  (`image_digitalShift_eq_image_shiftMod_vanDerCorput`).
  For every prefix `n ≤ 2^m` the two randomizations have the same law: a measure-preserving
  permutation of the dyadic cells carries one onto the other
  (`exists_measurePreserving_digitalShift_prefix`, `map_qmcEstimate_digitalShift_prefix_eq`). For
  other point sets the equivalence can fail. For the three points `{0, 1/8, 1/4}` the two
  estimator laws differ (`digitalShift_ne_shiftMod_counterexample`). For `f(x) = x` and
  `n = 2^m`, the scaled error of the digitally shifted estimator is `U[−1/2, 1/2)`, which is not
  normal (`hasLaw_scaled_error_digitalShift_id`, `scaled_error_digitalShift_ne_gaussianReal`).

## Corrections

Three claims of the posts are false as stated. Each is refuted in Lean, and a corrected
statement is proved.

* Requirement (i) is sufficient for unbiasedness but not necessary. Stratified points, post #2's
  first RQMC method, violate it (`not_hasLaw_stratumMap`) but are unbiased. The exact condition
  is averaged marginals (`integral_sampleMean_of_sum_map_eq`,
  `sum_map_eq_of_integral_sampleMean_indicator`).
* "RQMC is much lower variance than the MC" holds for independent stratification and every
  `f ∈ L²`. It fails for the shifted lattice: for the sawtooth `f(x) = fract (n x)` its variance is
  `n` times the MC variance (`mc_variance_lt_commonShift_sawtooth`).
* "RQMC converges at least as fast as QMC" holds for the worst-case bounds and rates, up to a
  factor `2`. It fails for a given integrand: the midpoint rule integrates `f(x) = x` exactly, but
  its random shift has mean squared error `1/12` (`shiftedMidpoint_counterexample`).

Three more claims are made precise. Both stratified shifts are "valid", that is, unbiased, but
their rates differ (`n⁻³` against `n⁻²`; `variance_stratified_id_lt_commonShift_id`). The
"spline" limit is exactly uniform when `f(1) ≠ f(0)` and a point mass otherwise. The
one-dimensional equivalence of the digital and the random shift holds for van der Corput prefixes
of length `n ≤ 2^m`, but not for every point set (`digitalShift_ne_shiftMod_counterexample`). See
[corrections](docs/corrections.md), which also lists the hypotheses made explicit.

## What is not formalised

* **Owen scrambling.** Loh's (2003) CLT for nested uniform scrambling and Owen's (1997) variance
  bounds for scrambled nets, as well as Matlab's `MatousekAffineOwen` scramble. The posts'
  contrast between scrambling (normal) and shifting (not normal) is proved here on the shifting
  side only.
* **Several dimensions.** The `s`-dimensional star discrepancy, the Koksma–Hlawka inequality, the
  Sobol sequence and digital nets in `s` dimensions, and lattice rules other than `{i/n}`.
  Unbiasedness (`integral_sampleMean_of_hasLaw_uniformCube`, `integral_sampleMean_shiftMod1`) and
  stratification by a partition (`variance_sampleMean_partition_le`) are proved in every
  dimension.
* **Pseudo-random generators** (post #1, PPS), for which the post claims no theorem; the
  simulation evidence of the posts and their codes; the comparison with quadrature (post #2, PS);
  the transformation from uniforms to other laws, which the results cover through a general `f`
  but do not construct.
* The limit theorem for a general `C¹ f` under the digital shift (proved for `f(x) = x`), the
  scale finer than `n` when `f(1) = f(0)`, and the remark that the lattice labelling does not
  converge almost surely (Weyl).
* The sharpness of the constant `1` in Koksma's inequality, and the equality `V(f) = ∫₀¹ |f'|`
  (only `≤` is proved, `totalVariation_le_integral_abs_deriv`).

All names are in the namespace `RQMCMarkov.PointSets`. See the [source map](docs/source-map.md)
and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MonteCarlo](PointSets/MonteCarlo.lean) | 16 | Post #1: the uniform laws on `[0,1)` and `[0,1)^s`, the sample mean, unbiasedness and variance for independent points whose laws average to `μ`, MC unbiasedness, variance `σ²/n`, RMSE `σ/√n`, the CLT, the unlucky draw and the absence of a worst-case bound |
| [Unbiased](PointSets/Unbiased.lean) | 22 | Requirement (i) and unbiasedness in `s` dimensions, the shift modulo 1 preserves the uniform law, strata and stratum maps, stratified points are unbiased but not marginally uniform, averaged marginals are necessary, requirement (i) alone does not reduce variance |
| [Stratified](PointSets/Stratified.lean) | 21 | Post #2: midpoint plus shift, exact variance of independent stratification, at most the MC variance, `K²/(12 n³)` for Lipschitz `f`, the common shift and `K²/(12 n²)`, both attained by `f(x) = x`, proportional allocation for a partition in any dimension |
| [Discrepancy](PointSets/Discrepancy.lean) | 21 | Counting functions, local and star discrepancy, `0 ≤ D*ₙ ≤ 1`, the lower bound `D*ₙ ≥ 1/(2n)`, the midpoint rule with `D*ₙ = 1/(2n)` and its optimality, post #2's `{1/6, 1/2, 5/6}` |
| [Koksma](PointSets/Koksma.lean) | 21 | Upper sets, the layer-cake formula on both sides, Koksma's inequality for monotone functions, differences of monotone functions and functions of bounded variation, the `C¹` form and `V(f) ≤ ∫₀¹ \|f'\|` |
| [VanDerCorput](PointSets/VanDerCorput.lean) | 22 | The base-2 radical inverse, its digit recursion, the net property for consecutive blocks, the counting error `⌊log₂ n⌋ + 1`, `D*ₙ ≤ (⌊log₂ n⌋ + 1)/n` and `2 (log n + 1)/n`, the QMC error `o(n^{-1/2})` |
| [ShiftedQMC](PointSets/ShiftedQMC.lean) | 16 | The random shift modulo 1 of a sequence, unbiasedness, `D*ₙ` at most doubled by every shift, Koksma for every shift, MSE and RMSE bounds, the shifted van der Corput sequence beats MC, the counterexample on a given integrand |
| [ShiftLimit](PointSets/ShiftLimit.lean) | 18 | Post #2's limit law for the common-shift labelling: `f(x) = x` exactly uniform for every `n`, the error on one cell, pointwise, almost sure and distributional convergence of `n (μ̂ₙ − μ)`, the uniform limit law, no normal limit at the scales `n` and `√n` |
| [ShiftLimitLattice](PointSets/ShiftLimitLattice.lean) | 9 | The shifted lattice `{fract (i/n + U)}` as the common-shift rule, `fract (n U)` uniform, the limit theorems for the lattice labelling, the sawtooth on which the shifted lattice loses to MC |
| [DigitalShift](PointSets/DigitalShift.lean) | 44 | The base-2 digital shift and the dyadic expansion ambiguity, dyadic cell permutations, marginal uniformity and unbiasedness, the first `2^m` van der Corput points as the lattice `{k/2^m}`, digital and random shift as the same point set, the scaled error for `f(x) = x`, the counterexample `{0, 1/8, 1/4}`, the first three points |
| [DigitalShiftPrefix](PointSets/DigitalShiftPrefix.lean) | 21 | Cell indices of van der Corput prefixes and their low-digit recursion, XOR and addition digit by digit, the cell bijection, digital and random shift equal in law for every prefix `n ≤ 2^m` |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (255 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
