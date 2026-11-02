# Owen scrambling and Loh's CLT for scrambled nets, in Lean

This is the `RQMCMarkov/OwenScrambling` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming). It
formalises one claim of post #2 of Robert Kirkby, "Simulating a Markov chain: MC, QMC, RQMC",
VFI Toolkit discourse, topic 687 (October 2026),
<https://discourse.vfitoolkit.com/t/simulating-a-markov-chain-mc-qmc-rqmc/687>: with a digital net
and nested uniform scrambling (Owen scrambling) "a standard CLT applies" and the estimator is
asymptotically normal (Loh 2003). It also formalises the results on scrambled nets that the claim
rests on: Owen (1995) on uniformity and net preservation, Owen (1997a) on the variance of
scrambled net quadrature, and Owen (1997b) on its order for smooth integrands. It is the stretch
goal of the first project of the plan in [PROPOSAL-RQMCMarkov.md](../../PROPOSAL-RQMCMarkov.md)
(§1). The rest of posts #1–#2 is covered by [RQMCMarkov/PointSets](../PointSets/README.md), and
post #3 by [RQMCMarkov/MarkovDriving](../MarkovDriving/README.md). Run the commands below from
this directory. [Return to the library index](../../README.md).

A *digital net* in base `b` is a set of `n = bᵐ` points of `[0,1)^s`. A `(t,m,s)`-net puts
exactly `bᵗ` points in every `b`-adic elementary box of volume `b^{t−m}` (`IsNet`). Owen's
*nested uniform scramble* permutes the base-`b` digits of each coordinate. Digit `k` is permuted
by a permutation attached to the node of the `b`-ary tree given by the `k` digits before it; all
these permutations are independent and uniform, and the coordinates are scrambled independently.
The estimator of `μ = ∫ f` is `μ̂ = n⁻¹ Σᵢ f(Xᵢ)` over the scrambled points `Xᵢ`. In one dimension
the net is `{k/bᵐ : k < bᵐ}`, with one point in each cell `[k/bᵐ, (k+1)/bᵐ)`; base `2` is the
post's Sobol case. In `s` dimensions the scramble acts on `D` digits and the points are completed
by independent uniform remainders.

The library contains **424 theorems** (516 audited declarations) in 19 modules. Fourteen modules
(326 theorems) are new. Five are carried from [RQMCMarkov/PointSets](../PointSets/README.md), with
the namespace and imports renamed and otherwise unchanged: `MonteCarlo`, `Unbiased`,
`Stratified`, `ShiftLimit` and `Discrepancy` (98 theorems).

## The main theorem: in one dimension the scrambled net is stratified sampling

Relabel the scrambled points of `{k/bᵐ}` by the cell they land in. The result has *exactly* the
law of independent stratified sampling, one independent uniform point in each of the `n = bᵐ`
cells (`hasLaw_owenNetSorted`). This holds for the genuine scramble at every depth: scrambling
all `m + d` digits of each point with a uniform tree and adding a uniform remainder below them
gives the same law for every `d` (`hasLaw_deepNetSorted`). So the one-dimensional scrambled net
reduces to independent stratified sampling, and the post's randomizations have these limit laws:

| Randomization of the net | Scaled error | Limit law | Lean |
| --- | --- | --- | --- |
| Owen scramble, depth `m` or any depth `m + d` | `(μ̂ − μ)/σₙ`, with `σₙ ~ n^{-3/2} (∫₀¹ f'²/12)^{1/2}` | `N(0,1)`, for measurable `f`, `C¹` and not constant on `[0,1]` | `tendstoInDistribution_owenNet`, `tendstoInDistribution_deepNet`, `tendsto_cube_mul_variance_owenNet` |
| Random shift, labelled `(i + U)/n` | `n (μ̂ − μ)` | `(f(1) − f(0)) (U − 1/2)`, uniform and not normal | `owenNet_normal_and_shift_not_normal` |
| Random digital shift, `f(x) = x` | `n (μ̂ − μ)` | `U[−1/2, 1/2)` at every `n = 2ᵐ`, not normal | `hasLaw_scaled_error_digitalShift_id` in `PointSets` (not carried) |

## What is proved

### One dimension

* **The scramble** (`Owen1DScramble`). An Owen tree `T : OwenTree b m` gives one permutation of
  `Fin b` for each node, and `owenWord` permutes each digit of a word by the permutation of its
  prefix. The scramble is nested (`wordPrefix_owenWord_eq`) and permutes the cells
  (`owenWord_injective`, `owenCell`). Under a uniform tree each net point lands in each cell with
  probability `b^{-m}` (`card_filter_owenCell`), so each scrambled point is `U[0,1)`
  (`hasLaw_owenNet`, requirement (i) of posts #1–#2). The key fact is `hasLaw_owenNetSorted`:
  relabelled by cell, the scrambled net has the law `stratifiedLaw (bᵐ)`. It uses only that the
  cell permutation is independent of the remainders. Hence the estimator is unbiased
  (`integral_sampleMean_owenNet`), its variance is `n⁻² Σᵢ Var(f | cell i)`
  (`variance_sampleMean_owenNet`), never above the MC variance
  (`variance_sampleMean_owenNet_le_mc`), and at most `K²/(12 n³)` for `K`-Lipschitz `f`
  (`variance_sampleMean_owenNet_le_lipschitz`).
* **The genuine scramble at every depth** (`Owen1DDeep`). `Owen1DScramble` scrambles the first
  `m` digits and models the digits below by independent uniform remainders. `Owen1DDeep` removes
  this modelling step. The point `k/bᵐ` has `m + d` digits, the last `d` of them zero
  (`netWord`); a uniform tree of depth `m + d` scrambles all of them (`deepNet`). Distinct net
  points sit below distinct nodes at every level `≥ m`, so their scrambled zero digits are uniform
  and independent of the top of the tree (`card_filter_deepKey_eq`). Relabelled by cell, the
  scrambled net again has the law `stratifiedLaw (bᵐ)` for every `d` (`hasLaw_deepNetSorted`). The
  law does not depend on the depth, so it is also the law of the scramble of all digits in the
  projective sense. The variance is the same (`variance_deepNet_eq_stratVar`). Unlike
  `hasLaw_owenNetSorted`, this uses the uniformity of the tree.
* **A Lindeberg CLT** (`Owen1DLindeberg`). Mathlib's CLT is for i.i.d. sequences. The stratified
  estimator is a sum of independent, not identically distributed terms whose number grows with
  `n`. `tendstoInDistribution_sum_of_bounded` proves the CLT for such triangular arrays from
  scratch, by characteristic functions and Lévy's continuity theorem: if for each `n` the terms
  `X n i` are independent, centred, bounded by `δₙ → 0` almost surely, and `Σᵢ E[(X n i)²] → v`,
  then `Σᵢ X n i ⇒ N(0, v)`.
* **The exact variance rate** (`Owen1DVariance`). For `f` `C¹` on `[0,1]`, the stratified
  variance satisfies `n³ σₙ² → (1/12) ∫₀¹ f'²` (`tendsto_cube_mul_stratVar`), so the RMSE is of
  order `n^{-3/2}`; for the scrambled net this is `tendsto_cube_mul_variance_owenNet`. If `f` is
  not constant the limit is positive (`integral_sq_deriv_pos`, `eventually_stratVar_pos`).
* **The CLT** (`Owen1DCLT`, `Owen1DDeep`). For measurable `f`, `C¹` and not constant on `[0,1]`,
  independent stratified sampling with any number `N → ∞` of cells satisfies
  `(μ̂ − μ)/σ ⇒ N(0,1)` (`tendstoInDistribution_stratified`). Post #2's claim in one dimension is
  `tendstoInDistribution_owenNet`: the scrambled net, normalised by its own standard deviation
  (`variance_owenNet_eq_stratVar`), is asymptotically `N(0,1)` as `n = bᵐ → ∞`. The same holds
  for the genuine scramble with any depths `m + D m` (`tendstoInDistribution_deepNet`).
  `owenNet_normal_and_shift_not_normal` proves the post's contrast for one `f`: the scrambled net
  is asymptotically normal, while the randomly shifted lattice has the uniform limit of
  `ShiftLimit` and no normal limit.

### Several dimensions

* **Owen's structural facts** (`ScrambleDefs`). Digit strings and their cells, the elementary
  boxes `elemBox` and `(t,m,s)`-nets `IsNet`. A nested scramble `ρ : Scramble b D` permutes the
  `D` digits of one coordinate, and `scrambledPoint` scrambles each coordinate and adds the
  remainders. The scramble is nested (`agree_scramble_iff`) and bijective
  (`scramble_bijective`). Every scramble maps a `(t,m,s)`-net to a `(t,m,s)`-net
  (`isNet_scrambledPoint`, Owen 1995). Under the uniform scramble every scrambled point is
  `U[0,1)^s`, whatever the digit point (`mixLaw_scrambledPoint`, Owen 1995), so the estimator is
  unbiased for any point set (`integral_scrambledLaw`). The pair law: two strings with exactly `k`
  common leading digits are sent to a pair uniform on the pairs with exactly `k` common leading
  digits (`card_scramble_pair`, Owen 1997a); in `s` dimensions this is `card_scrambleVec_pair`,
  and for the real points `mixLaw_scrambledPoint_pair_eq`.
* **Owen's variance formula** (`ScrambleHaar`, `ScrambleVariance`). The base-`b` Haar kernels
  `haarKernel ℓ` split the mean square of a grid function into components `haarVar F ℓ ≥ 0`
  (`sum_haarVar`, Parseval). Averaged over the scrambles, `E[(Σᵢ F(σ dᵢ))²] = n Σ_ℓ Γ_ℓ σ²_ℓ`
  with Owen's gain coefficients `Γ_ℓ = gainCoeff b d ℓ` (`sum_sq_sum_scrambleVec`). With the
  decomposition `Var f = σ²_{>D} + Σ_{ℓ≠0} σ²_ℓ` (`variance_eq_cellResVar_add`) this gives
  `Var(μ̂) = n⁻¹ (σ²_{>D} + Σ_{ℓ≠0} Γ_ℓ σ²_ℓ)` for any digit points (`variance_scrambledLaw`).
* **The gain coefficients and Owen's bounds** (`ScrambleGain`, `ScrambleVariance`). For a
  `(0,m,s)`-net, `Γ_ℓ` depends only on the number of active coordinates and the total resolution
  (`gainCoeff_net`), with a closed form (`gainSeq_eq_altSum`). Components with `Σⱼ ℓⱼ ≤ m` are
  integrated exactly (`gainCoeff_net_eq_zero`), and `0 ≤ Γ_ℓ ≤ (b/(b−1))^{s−1}` for `s ≤ b + 1`
  (`gainCoeff_net_mem_Icc`). Hence `Var(μ̂) ≤ (b/(b−1))^{s−1} σ²/n` for every measurable
  `f ∈ L²` when `s ≤ b + 1` (`variance_scrambledLaw_le`), and `Var(μ̂) ≤ e σ²/n` when `s ≤ b`
  (`variance_scrambledLaw_le_exp_one`): scrambled nets never lose more than a factor `e` to MC.
* **`Var = o(1/n)`** (`ScrambleAsymptotic`, Owen 1997a). Scrambled `(0,m,s)`-nets integrate step
  functions on elementary cubes of level `R` exactly once `sR ≤ m`, for every scramble
  (`sampleMean_stepFn_scrambledPoint`). Such step functions are dense in `L²`
  (`exists_stepFn_approx`). With Owen's bound this gives `n Var(μ̂) → 0` for every measurable
  `f ∈ L²` and `1 ≤ s ≤ b + 1` (`tendsto_pow_mul_variance_scrambledLaw`).
* **Hammersley nets** (`ScrambleHammersley`). `{(i/bᵐ, φ_b(i))}` is a `(0,m,2)`-net in every base
  `b ≥ 2` (`isNet_hammersley`), so the hypotheses can be met in two dimensions. The bounds, the
  `o(1/n)` rate and the additive CLT are instantiated for it
  (`variance_scrambledLaw_hammersley_le`, `tendsto_variance_scrambledLaw_hammersley`,
  `tendstoInDistribution_scrambledLaw_hammersley`).
* **Loh's CLT for additive integrands** (`LohCLT`). For `f(x) = Σⱼ gⱼ(xⱼ)` with each `gⱼ`
  measurable and `C¹` on `[0,1]`, at least one not constant, and any sequence of `(0,m,s)`-nets,
  `(μ̂ − μ)/√Var(μ̂) ⇒ N(0,1)` in every dimension `s`
  (`tendstoInDistribution_scrambledLaw_addFn`). In each coordinate a `(0,m,s)`-net visits every
  cell of length `b^{-m}` exactly once (`injective_coord_net`), so given the scramble the error is
  a sum of independent bounded terms. The bounded Lindeberg CLT then holds for every fixed
  sequence of scrambles (`tendstoInDistribution_scrambledEstimate_addFn`), and passes to the
  mixture. The variance is `Σⱼ σ²ₙ(gⱼ)` (`variance_scrambledLaw_addFn`), and
  `n³ Var(μ̂) → Σⱼ (1/12) ∫₀¹ gⱼ'²` (`tendsto_cube_mul_variance_scrambledLaw_addFn`).
* **The order `n⁻³ log n` in two dimensions** (`LohVariance`, Owen 1997b for `s = 2`). For
  scrambled `(0,m,2)`-nets and `f` Lipschitz with bounded mixed differences and a non-zero
  mixed derivative at some point, `c m ≤ n³ Var(μ̂) ≤ C (m + 1)` for large `m`, that is
  `Var(μ̂) ≍ n⁻³ log n` (`variance_scrambledLaw_two_asymp`). The same holds for `f` with a
  continuous mixed partial derivative `∂²f/∂x₀∂x₁`, non-zero somewhere
  (`variance_scrambledLaw_two_asymp_of_deriv`). For `f = x₀ x₁` the bounds are explicit for every
  `m` (`variance_scrambledLaw_prodFn`). Additive integrands have order `n⁻³` instead: the `log n`
  comes from the interaction. For these smooth non-additive `f`, the remainders carry a vanishing
  share of the variance (`tendsto_avg_variance_given_scramble_div`; see below).
* **The digital shift as a degenerate scramble** (`LohCLT`). The random digital shift is the
  nested scramble with the same translation at every node of a level (`digitShiftScramble`,
  `scramble_digitShiftScramble`). It does not have Owen's pair law: in base `2` with two digits,
  no digital shift sends `(00, 10)` to `(00, 11)`, while a positive fraction of nested scrambles
  does (`digitShift_ne_pair_law`).

## Corrections

Two parts of post #2's unqualified wording are false. Each is refuted in Lean, and a corrected
statement is proved. They correct the post, not Loh (2003), who normalises by the standard
deviation and assumes a smooth integrand.

* There is no CLT at the Monte Carlo scale `√n`. For scrambled `(0,m,s)`-nets and every
  measurable `f ∈ L²`, `√n (μ̂ − μ) → 0` in probability (`tendsto_scrambledLaw_sqrt_error_ge`), so
  it has no normal limit with positive variance (`not_tendstoInDistribution_sqrt_scaled_error`).
  Normality holds only after dividing by the true standard deviation, which is `o(n^{-1/2})`.
* The integrand must be smooth and non-degenerate. A constant `f` is integrated exactly, so the
  normalised error is `0` (`owenNet_exact_of_const`, `not_tendstoInDistribution_owenNet_const`).
  For `f = 1_{[0,1/3)}` in base `2` the variance is positive but the normalised error is bounded
  by `3` and has no normal limit (`not_tendstoInDistribution_owenNet_indicator`). In any dimension
  step functions on elementary cubes are integrated exactly once `m ≥ sR`
  (`scrambledLaw_stepFn_ne_eq_zero`), so no normalisation gives a normal limit
  (`not_tendstoInDistribution_stepFn`).

A technical point concerns Owen's bound, not the post: `0 ≤ Γ_ℓ ≤ (b/(b−1))^{s−1}` needs
`s ≤ b + 1`. In base `2` the gain sequence has the value `−4` for four active coordinates
(`gainSeq_two_four_two`). This does not contradict Owen, since `(0,m,4)`-nets in base `2` do not
exist for `m ≥ 2`. Several claims are made precise. The one-dimensional law identity and CLT hold
for any random cell permutation independent of the remainders; the uniformity of the tree only
gives the marginal uniformity of each point, except for the deep scramble, which needs it. See
[corrections](docs/corrections.md), which also lists the hypotheses made explicit.

## What is not formalised

* **Loh's CLT for non-additive integrands in `s ≥ 2` dimensions.** For smooth non-additive `f`
  in two dimensions, almost all of `Var(μ̂)` comes from the scramble itself, not from the
  remainders (`tendsto_avg_variance_given_scramble_div`). Under the scramble the points are
  dependent, so a Lindeberg argument conditional on the scramble, which proves the additive case,
  cannot give the general CLT. Conditioning on the top levels of the trees does not split the
  points into independent blocks once `s ≥ 2`. The general case needs Loh's Stein-method argument
  for dependent sums.
* **The variance order for general `s`.** Owen's (1997b) `Var = O(n⁻³ (log n)^{s−1})` for smooth
  `f` is proved for `s = 2` only, in both directions; general `s` needs `s`-fold mixed
  differences.
* **Nets with `t > 0`.** The gain bounds, `o(1/n)`, and the CLT are for `(0,m,s)`-nets; only
  uniformity, unbiasedness, the variance formula and net preservation are proved for any point set
  or any `t`. The post's Sobol points have `t > 0` in general once `s ≥ 3`.
* **The infinite-depth scramble in `s ≥ 2` dimensions.** In `s` dimensions the scramble acts on
  `D` digits plus uniform remainders; that this has the law of the scramble of all digits is not
  formalised. In one dimension it is (`hasLaw_deepNetSorted`).
* **The Sobol sequence** in several dimensions, the post's codes, and Matlab's
  `MatousekAffineOwen` scramble; the empirical claims of the post (#2 ¶8).

All names are in the namespace `RQMCMarkov.OwenScrambling`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [MonteCarlo](OwenScrambling/MonteCarlo.lean) | 16 | Carried from `PointSets`: the uniform laws on `[0,1)` and `[0,1)^s`, the sample mean, MC unbiasedness, variance `σ²/n`, RMSE and CLT |
| [Unbiased](OwenScrambling/Unbiased.lean) | 22 | Carried from `PointSets`: marginally uniform points are unbiased in `s` dimensions, the shift modulo 1, strata and stratum maps `(i + u)/n` |
| [Stratified](OwenScrambling/Stratified.lean) | 21 | Carried from `PointSets`: exact variance of independent stratification, at most the MC variance, `K²/(12 n³)` for Lipschitz `f` |
| [ShiftLimit](OwenScrambling/ShiftLimit.lean) | 18 | Carried from `PointSets`: the random-shift limit `n (μ̂ₙ − μ) → (f(1) − f(0)) (U − 1/2)`, uniform and not normal |
| [Discrepancy](OwenScrambling/Discrepancy.lean) | 21 | Carried from `PointSets`: counting functions, local and star discrepancy, the midpoint rule; not used by the other modules |
| [Owen1DScramble](OwenScrambling/Owen1DScramble.lean) | 34 | Digit words, Owen trees and the nested scramble of `{k/bᵐ}` at depth `m`, nestedness, cell permutations, each point uniform, the scrambled net relabelled by cell is independent stratified sampling, unbiasedness, variance, at most MC, `K²/(12 n³)` |
| [Owen1DDeep](OwenScrambling/Owen1DDeep.lean) | 24 | The genuine scramble to any depth `m + d`, words of length `m + d`, scrambled zero digits uniform and independent of the top of the tree, the same stratified law at every depth, the CLT for the genuine scramble |
| [Owen1DLindeberg](OwenScrambling/Owen1DLindeberg.lean) | 4 | Differences of products of numbers of norm at most `1`, the second-order expansion of a bounded centred characteristic function, the Lindeberg CLT for bounded independent triangular arrays |
| [Owen1DVariance](OwenScrambling/Owen1DVariance.lean) | 10 | The stratified variance `stratVar`, cell estimates by the mean value theorem, `n³ σₙ² → (1/12) ∫₀¹ f'²`, positivity for non-constant `f`, the constant case |
| [Owen1DCLT](OwenScrambling/Owen1DCLT.lean) | 17 | The CLT for independent stratified sampling with any number of cells, the CLT for the Owen-scrambled net, its variance and rate, the constant counterexample, the contrast with the random shift |
| [Owen1DCounterexample](OwenScrambling/Owen1DCounterexample.lean) | 10 | Bounded variables have no normal limit, the indicator of `[0,1/3)` in base `2`: positive variance, normalised error bounded by `3`, no normal limit |
| [ScrambleDefs](OwenScrambling/ScrambleDefs.lean) | 52 | Digit strings, prefixes and cells, elementary boxes and `(t,m,s)`-nets, nested scrambles and scrambled points, a scrambled net is a net, each scrambled point uniform, the pair law, mixture laws |
| [ScrambleHaar](OwenScrambling/ScrambleHaar.lean) | 30 | Cell-averaging and detail kernels, the base-`b` Haar kernels and variance components, Parseval, the pair law in `s` dimensions as a Haar expansion, gain coefficients, the second moment of a scrambled sum |
| [ScrambleGain](OwenScrambling/ScrambleGain.lean) | 28 | Box counts of `(0,m,s)`-nets, the gain sequence and its closed form, the gain coefficients of a scrambled `(0,m,s)`-net, exactness for low resolutions, Owen's bound for `s ≤ b + 1`, the counterexample `G(4, 2) = −4` in base `2` |
| [ScrambleVariance](OwenScrambling/ScrambleVariance.lean) | 29 | Cell averages and remainders, the law of the scrambled estimator, unbiasedness for any point set, the ANOVA–Haar decomposition, the real-point pair law, Owen's variance formula, the bounds `(b/(b−1))^{s−1} σ²/n` and `e σ²/n` |
| [ScrambleAsymptotic](OwenScrambling/ScrambleAsymptotic.lean) | 14 | Box counts, step functions integrated exactly, subtracting an exactly integrated function, density of step functions in `L²`, `Var = o(1/n)` |
| [ScrambleHammersley](OwenScrambling/ScrambleHammersley.lean) | 2 | Reversed digits, the Hammersley point set as a `(0,m,2)`-net in every base |
| [LohCLT](OwenScrambling/LohCLT.lean) | 33 | No CLT at the scale `√n`, `(0,m,s)`-nets have distinct coordinate cells, Loh's CLT for additive integrands in every dimension (for every fixed sequence of scrambles and for the mixture), the additive variance and rate, no CLT for step functions, Hammersley instances, the digital shift without Owen's pair law |
| [LohVariance](OwenScrambling/LohVariance.lean) | 39 | Haar projections as averages of mixed differences, upper and lower bounds on the Haar components, the gain of the critical components, `Var ≍ n⁻³ log n` for `s = 2`, also from a continuous mixed partial derivative, the product `x₀ x₁`, the share of the variance given the scramble |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library and freshly recompiles every contributed proof. It also audits each
named declaration's axioms (516 declarations): only `propext`, `Classical.choice` and `Quot.sound`
are allowed. Warnings fail the check.
