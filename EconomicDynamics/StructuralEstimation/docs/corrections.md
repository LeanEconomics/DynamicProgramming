# Corrections and departures: Miao Chapter 12

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 12, Structural
Estimation, pp. 385–410. Lean names are relative to `Miao.StructuralEstimation`. Every book item is
located in the [source map](source-map.md).

## Introduction and §12.1 (GMM)

### Set-up and consistency

1. **Indexing.** The sample is `x₀, …, x_{T−1}` (the book's `t = 1, …, T`), and
   `g(θ) = E h(x₀, θ)`; for a stationary process `E h(x_t, θ)` does not depend on `t`
   (`gm_integral_comp_eq`).
2. **Assumption 12.1.7, p. 389.** `E[sup_{θ∈Θ} ‖h(x_t, θ)‖] < ∞` presupposes that the supremum
   over an uncountable `Θ` is measurable. It is stated as the existence of an integrable
   measurable envelope `D(x) ≥ ‖h(x, θ)‖` on `Θ` (`Assumption_12_1_7`); when the supremum is
   measurable and integrable it is such an envelope (`assumption_12_1_7_of_sup`).
3. **Assumption 12.1.2, p. 387.** Its second half (finiteness and continuity of `E h(x_t, θ)`)
   follows from the first half and Assumption 12.1.7 by dominated convergence
   (`gm_integrable_moment`, `gm_continuousOn_popMoment`); measurability of `h(·, θ)` is made
   explicit.
4. **Assumption 12.1.4, p. 388.** Theorem 12.1.1 uses only `W > 0` and `W_T → W` in probability
   (entrywise); positive semidefiniteness of `W_T` is not needed there (`theorem_12_1_1`).
   It is used (as symmetry of `W_T`) for the first-order condition (12.2).
5. **Theorem 12.1.1, p. 389.** The proof the book refers to (Hall 2005) needs the uniform law of
   large numbers `sup_Θ ‖g_T − g‖ → 0`, which is proved here from Birkhoff's ergodic theorem
   (`gm_ulln`); consistency is then proved for every minimiser, without measurability of
   `θ̂_T` (`theorem_12_1_1`); `theorem_12_1_1_ae` is the strong-consistency version when
   `W_T → W` almost surely.

### The first-order condition and the expansion

6. **(12.2), p. 388.** The gradient of `g'Wg` is `(∂g/∂θ)'(W + W')g`; (12.2) as printed holds
   for symmetric `W_T` (as positive semidefinite matrices are) (`eq_12_2`), at a local
   minimiser, i.e. when `θ̂_T` is interior.
7. **(12.3), p. 390, is false for vector-valued moments.** There need not be one
   `θ̄_T = λθ₀ + (1 − λ)θ̂_T` with `g_T(θ̂_T) = g_T(θ₀) + ∂g_T(θ̄_T)(θ̂_T − θ₀)`: for
   `g(θ) = (cos θ, sin θ)`, `θ₀ = 0`, `θ̂ = 2π` no `λ ∈ [0, 1]` works
   (`eq_12_3_counterexample`, with `gm_circle_hasDerivAt`). The correct statement uses a
   separate point `θ̄_{T,i}` on the segment for each moment `i` (`eq_12_3`), so `Ḡ_T` has rows
   evaluated at different points; this is what `theorem_12_1_2` uses.
8. **Typos, p. 390.** `√T(θ − θ₀)` should read `√T(θ̂_T − θ₀)` (also in Theorem 12.1.2), and
   `∂g_T(x_t, θ̄_T)/∂θ` should read `∂g_T(θ̄_T)/∂θ`. The derivation of
   `√T(θ̂_T − θ₀) = −M_T √T g_T(θ₀)` also needs `Ĝ'W_TḠ` invertible (`gm_linearization`,
   `gm_linearization_sqrt`); in Theorem 12.1.2 this holds with probability tending to one.

### Asymptotic normality

9. **Lemma 12.1.1, p. 391, does not follow from Assumptions 12.1.1, 12.1.5 and 12.1.9.**
   Stationarity, ergodicity and a finite positive definite long-run variance do not imply a
   central limit theorem (Herrndorf 1983 gives stationary ergodic counterexamples with finite
   long-run variance); a CLT needs additional dependence conditions (martingale differences,
   mixing, Gordin's condition). The lemma is cited in the book; here its conclusion is the
   explicit hypothesis `hclt` of `theorem_12_1_2`, and it is proved for i.i.d. data, with
   `S = E[hh']`, from Mathlib's central limit theorem by the Cramér–Wold device
   (`lemma_12_1_1_iid`). No formal counterexample is given: Herrndorf's construction is beyond
   the scope of this formalisation.
10. **Theorem 12.1.2, p. 391, missing hypotheses.** (a) the rank condition (`G₀x = 0 ⇒ x = 0`,
    so `G₀'WG₀` is invertible, `gm_posDef_GWG`) is added; (b) the estimator is assumed to be a
    measurable function (a random variable); (c) of Assumption 12.1.8(i) only
    differentiability of `h(x, ·)` on a ball `B(θ₀, r) ⊆ Θ` is used (continuity of `∂h/∂θ` is
    not needed), of Assumption 12.1.10(i) only continuity of `E ∂h/∂θ` at `θ₀`; Assumption
    12.1.10(ii) is used on the ball `B(θ₀, r)`. The limit is stated as `−MZ` with
    `Z ~ N(0, S)`, and `−MZ ~ N(0, MSM')` (`gm_map_multivariateGaussian`); `S` positive
    semidefinite suffices.
11. **Efficiency, p. 392.** "the most efficient one in the class of all asymptotically normal
    estimators" overstates the result: what holds (and is proved, `gm_efficiency`) is that
    `W = S⁻¹` minimises the asymptotic variance `(G'WG)⁻¹G'WSWG(G'WG)⁻¹` over all positive
    definite `W`, in the Loewner order, i.e. among GMM estimators based on the given moment
    conditions; the variance is then `(G₀'S⁻¹G₀)⁻¹` (`gm_efficient_var`,
    `theorem_12_1_2_efficient`).

### Long-run variance, HAC and the J test

12. **The long-run variance, p. 392.** The finite-`T` identity
    `Var(√T g_T)_{il} = Γ₀ + Σ_{j=1}^{T−1} ((T−j)/T)(Γ_j + Γ_j')` is proved for stationary
    processes with square-integrable moments (`gm_longRunVar`, from the Toeplitz identity
    `gm_toeplitz_sum_Ico`). The passage to the limit `Γ₀ + Σ_{i≥1}(Γ_i + Γ_i')` needs a
    summability condition, which the book omits; it is proved under absolute summability of the
    autocovariances (`gm_longRunVar_limit`).
13. **Table 12.1, p. 393.** "`a_i = i/b_T + 1`" is `a_i = i/(b_T + 1)` (`gm_kernelArg`); the
    text refers to "Table ??". The Parzen kernel is continuous (`gm_continuous_parzen`); both
    Bartlett and Parzen weights lie in `[0, 1]`.
14. **Two-step GMM, p. 394.** The displayed `Γ̂_j` carries a stray `)^{−1}` and uses
    `h(x_{t+j}, ·)` where p. 393 uses `h(x_{t−j}, ·)`; `gm_sampleAutocov` follows p. 393.
15. **(12.4), p. 394.** The J statistic weights by `Ŝ_T⁻¹`, not `Ŝ_T` (`gm_J`). The algebra
    behind the `χ²(q − k)` limit is proved (`eq_12_4_algebra`, `gm_resid_proj`: the efficient
    residual moment is `(I − P)z` for a symmetric idempotent `P` of trace `k`); the limit law is
    cited (Hansen 1982) and not formalised (Mathlib has no `χ²` distribution).

### Instance

16. **Non-vacuity.** All assumptions of Theorems 12.1.1 and 12.1.2, including the CLT
    hypothesis, are verified in a degenerate location model (`gm_ex_theorem_12_1_1`,
    `gm_ex_theorem_12_1_2`); the CLT hypothesis is also verified non-degenerately for i.i.d.
    data (`lemma_12_1_1_iid`).

## §§12.2–12.3 and Exercises 12.1–12.4

### Errors in the book

17. **Example 12.3.3, p. 405**: the exponential duration model with hazard `β` has log-likelihood
   `N ln β − β ∑ Dᵢ`, maximised at `β̂_T = N/∑ᵢ Dᵢ = 1/D̄`, not at `∑ᵢ Dᵢ/N` as printed
   (`example_12_3_3`; `example_12_3_3_book_false`: for one duration `D = 2` the printed value
   `β = 2` has lower log-likelihood than `β = 1/2`). The book's conclusion ("the auxiliary
   parameter is estimated as the average duration") holds for the mean-duration parametrisation
   `λ = 1/β`, whose ML estimator is `D̄` (`example_12_3_3_mean`, by invariance).
18. **Example 12.3.3, p. 406, "indirect inference turns out to be the same as SMM"**: true with the
   mean-duration parametrisation, where the criterion is exactly the SMM criterion of (12.5)
   with `m(D) = D` (`example_12_3_3_ii_eq_smm`). With the hazard parametrisation it fails for
   `S ≥ 2`, since the average of the simulated hazards `1/D̄ˢ` is not `1/` the average mean
   (`example_12_3_3_hazard_ne`: means `1, 3` against data mean `2` match, hazards do not).
19. **`β̂_ST(θ)`, p. 405**: defined as `∑ₛ β̂ˢ_T(θ)`; it must be the average
   `(1/S)∑ₛ β̂ˢ_T(θ)` (the sum is `S` times the common value when the `β̂ˢ_T` agree)
   (`ml_iiAverage`, `ml_ii_average_correction`).
20. **Example 12.2.1, p. 397**: with acceptance iff `w ≥ w*`, the rejection probability is
   `F((−∞, w*))`, the left limit of the distribution function, not `F(w*)`; they agree when `F`
   has no atom at `w*` (`example_12_2_1_duration`, `ml_reject_prob_eq_cdf`). Example 12.3.1
   writes acceptance as `wₜ > w*`; `ml_firstPassage_iid` covers any acceptance set.
21. **Invariance, p. 398**: no differentiability of `c` is needed: `c(θ̂)` maximises the profile
   likelihood `γ ↦ sup {L(θ) : c(θ) = γ}` for every function `c` (`ml_invariance_profile`;
   `ml_invariance` for a reparametrisation).
22. **The likelihood of Example 12.2.1 identifies `θ = (c, β)` only through `w*(θ)`**
   (`example_12_2_1`, part 2): the durations do not identify `c` and `β` separately; the book
   does not say so. With `c` known (Exercise 12.3) `β` moves the likelihood through the
   reservation wage, which is nondecreasing in `β` (`ml_resWage_mono_beta`) and strictly
   increasing when offers above it have positive expected surplus
   (`ml_resWage_strictMono_beta`).

### Departures in the formalisation

23. **Information matrix equality and Cramér–Rao bound, p. 398**: stated in the book for a vector
   parameter and a general density without conditions; proved for a scalar parameter and a model
   on a finite sample space, where `∑ₓ p(x, θ) = 1` can be differentiated twice under the sum
   (`ml_score_mean_zero`, `ml_information_matrix_equality`, `ml_cramer_rao`). The Cramér–Rao bound
   is the finite-sample bound for unbiased estimators; its attainment is shown for one coin toss
   (`ml_cramer_rao_bernoulli`) and asymptotically for the coin-tossing MLE
   (`ex_12_1_asymptotic`: limit variance `p(1 − p) = I(p)⁻¹`).
24. **Asymptotic properties of ML, p. 397**: listed "without explicitly stating relevant
   conditions and proofs". Proved in full for the models of Exercises 12.1 and 12.2 from
   Mathlib's strong law (`strong_law_ae_real`) and central limit theorem
   (`tendstoInDistribution_inv_sqrt_mul_sum_sub`), with the delta method via Mathlib's Slutsky
   theorem for the exponential MLE (`ex_12_1_consistent`, `ex_12_1_asymptotic`,
   `ex_12_2_consistent`, `ex_12_2_asymptotic`). No cited limit theorem is taken as a hypothesis.
25. **Hypothesis tests, pp. 398–399**: the asymptotic `χ²` equivalence of the LR, Wald and LM
   tests is not formalised; `ml_gaussian_tests_equal` proves that the three statistics coincide
   exactly (`T(x̄ − μ₀)²/σ²`) in the Gaussian location model with known variance. In the LM
   statistic `I` is the information of the whole sample (`T/σ²`).
26. **SMM asymptotics, p. 402**: "using results for GMM" (the GMM limit theory of §12.1 belongs
    to another part). The algebra is proved in general: the factor `1 + 1/S`
    (`ml_smm_variance_factor`), the optimal weighting matrix and its optimality in the
    positive-semidefinite order (`ml_smm_optimal_weight`, via `ml_sandwich_inv` and
    `ml_sandwich_optimal`), and the `S → ∞` limit (`ml_smm_Q_tendsto`). Consistency, the exact
    variance `(1 + 1/S)σ²` and asymptotic normality are proved for the location model
    `xₜ = θ₀ + ωₜ`, `xₜˢ(θ) = θ + ωₜˢ`, `m(x) = x` (`ml_smm_location_consistent`,
    `ml_smm_location_variance`, `ml_smm_location_asymptotic`); in the last, the i.i.d. property
    of `ξₜ = ωₜ − (1/S)∑ₛ ωₜˢ` across `t` is a hypothesis (it follows from joint independence of
    all shocks).
27. **SML, p. 403**: the inconsistency for fixed `S` is formalised through its mechanism, the
    downward bias `E ln f̃ ≤ ln f` of the simulated log-likelihood (`ml_sml_log_bias`), strict for
    a two-point simulator (`ml_sml_log_bias_strict`); the limit theory with `√T/S → 0` is not
    formalised.
28. **Binding function, p. 407**: the derivative formula is proved from the first-order condition
    by the chain rule for Fréchet derivatives on general normed spaces, assuming `b` and `∂ψ_∞/∂β`
    differentiable (`ml_binding_derivative`, `ml_binding_derivative_J`); `J₀` is taken to be
    `−∂²ψ_∞/∂β∂β′` (the book defines it as the probability limit of the sample Hessian, which
    also needs `ψ_T` normalised by `1/T`).
29. **(12.7) and the optimal `W*`, p. 407**: the asymptotic normality (12.7) is stated in the book
    without proof and is not formalised; the variance algebra is proved (`ml_ii_Q`,
    `eq_12_7_optimal`), with `J₀` symmetric invertible and `I₀ − K₀` positive semidefinite
    invertible.
30. **Exercise 12.3**: the lognormal offer distribution is not concentrated on a bounded
    interval, as the copied McCall model (`MLODMcCall`) requires; the mathematical content
    (likelihood, dependence on `β`) is proved for offers on `[0, B]`. Simulation, plotting and
    estimation in Exercises 12.3–12.4 are computational and not formalised.
31. **McCall model**: copied from `EconomicDynamics/Applications` (`ODBasic`, `ODMcCall`, two
    lemmas of `ODOption`, and `BRContraction`), names prefixed `ml_`; the equivalence with the
    stopping problem of Exercise 5.1 (`od_mccall_bellman_iff_stopping`, which needs the MDP
    modules) is omitted.
