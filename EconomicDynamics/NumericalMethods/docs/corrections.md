# Corrections and departures: Miao Chapter 11

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 11, Numerical
Methods, pp. 347–384. Lean names are relative to `Miao.NumericalMethods`. Every book item is located
in the [source map](source-map.md).

## §11.1, §11.2, §11.4, Exercise 11.2

### §11.1 Numerical Integration

1. **"≃" made precise.** The book writes the quadrature formulas with "≃". We prove equality on
   the class where the rules are exact: an `n`-point Gaussian rule is exact for polynomials of
   degree `≤ 2n − 1` (`nq_gauss_exact`; Legendre on `[a, b]` `nq_legendre_interval_exact`,
   Chebyshev `nq_chebyshev_exact`, Hermite normal expectations
   `nq_normal_expectation_gauss_hermite`, product rules `nq_prod_gauss_exact`), and no `n`-point
   rule is exact for all polynomials of degree `2n` (`nq_gauss_not_exact_two_mul`). The change of
   variables formulas (Legendre, Hermite, Laguerre) are proved as exact identities
   (`nq_legendre_change_of_variables`, `nq_normal_expectation_hermite`,
   `nq_laguerre_present_value`).
2. **Gauss–Chebyshev indexing and the improper integral.** The nodes are indexed
   `i = 0, …, n − 1` (`nqChebNode n i = cos((2i + 1)π/(2n))`), the book's `i = 1, …, n` shifted by
   one. The improper integral over `(−1, 1)` is the Bochner integral over `[−1, 1]`, with
   `(1 − x²)^{−1/2}` written `(√(1 − x²))⁻¹` (`nq_chebyshev_substitution`).
3. **"Probabilities `wᵢ`".** That a Gaussian rule for a density is a discrete distribution needs
   the weights to be nonnegative, which the book does not prove; it holds for distinct nodes and a
   nonnegative weight (`nq_gauss_weights_nonneg`, `nq_gauss_probability`).

### §11.2 Discretizing AR(1) Processes

4. **Tauchen's intervals are misprinted.** The book prints `I₂ = [z_min + h/2, z_min + h)`,
   `I_{N−1} = [z_min + (N − 1)h/2, z_min + Nh/2)` and `I_N = [z_min + Nh/2, ∞)` with
   `h = (z_max − z_min)/(N − 1)`. Tauchen's cut points are the midpoints of consecutive grid points,
   `c_j = z_min + (2j − 1)h/2` (`nqTauchenCut`, `nq_tauchen_cut_midpoint`), so
   `I₂ = [z_min + h/2, z_min + 3h/2)` and `I_N = [z_max − h/2, ∞)`. The printed upper endpoint of
   `I₂` is not a cut point (`nq_tauchen_printed_I2_upper`, `N ≥ 2`) and the printed lower endpoint
   of `I_N` is not the last cut point for `N ≥ 4` (`nq_tauchen_printed_IN_lower`). The transition
   matrix is stochastic for any nondecreasing cut points (`nq_tauchen_stochastic`). Intervals are
   indexed `0, …, N − 1` (`nqCell`).
5. **Tauchen–Hussey weights: a spurious sum.** The book prints
   `π̃_{ij} = π^{−1/2} ∑_{j=1}^N wⱼ f(zʲ|zⁱ)/f(zʲ|0)`; the sum over `j` must be dropped:
   `π̃_{ij} = π^{−1/2} wⱼ f(zʲ|zⁱ)/f(zʲ|0)` (`nqTHTilde`), which is what makes
   `E[v(z')|zⁱ] = ∑ⱼ π̃_{ij} v(zʲ)` (`nq_th_exact`, when the Gauss–Hermite rule is exact for the
   transformed integrand).
6. **Row sums.** "We may have `∑ⱼ π̃_{ij} ≠ 1`" is confirmed: with the two-point Gauss–Hermite
   rule (`nq_hermite_two_point`) and `zⁱ = σ`, the row sum is `e^{−ρ²/2} cosh ρ < 1` for every
   `ρ ≠ 0` (`nq_th_rowsum_lt_one`). The row sum is the Gauss–Hermite approximation of an integral
   equal to one (`nq_th_rowsum_integral`); its convergence to one as `N → ∞` is not formalised.
7. **No Rouwenhorst method in this draft.** The draft's §11.2 presents Tauchen (1986) and
   Tauchen–Hussey (1991); it contains no Rouwenhorst method, so there is nothing to formalise.
8. **`μ = 0` and the stationary law.** As in the book ("without loss of generality, we set
   `μ = 0`"), the Tauchen and Tauchen–Hussey constructions use `μ = 0`. "Unconditional mean and
   standard deviation" are proved as the unique stationary mean and variance
   (`nq_ar1_mean_fixed`, `nq_ar1_variance_fixed`) and by the stationarity of
   `N(μ, σ²/(1 − ρ²))` under (11.1) (`nq_ar1_stationary_law`).

### §11.4 Perturbation Methods and Exercise 11.2

9. **`ρ` has two meanings.** The book uses `ρ` both for the EIS parameter in (11.3) and for the
   autocorrelation of `x_t` (`x_{t+1} = ρx_t + σ_x ε_{x,t+1}`, `A = β/(1 − βρ)`). We write `φ`
   for the autocorrelation; the book's `A = β/(1 − βρ)` is `A = β/(1 − βφ)` (`eq_11_6`).
10. **`μ_v`, not `μ_c`.** Below (11.6) the book says "`A` and `μ_c` are constants to be
    determined"; the unknowns are `A` and `μ_v` (`μ_c` is a parameter) (`eq_11_6`).
11. **The limit at `ρ = 1`.** At `ρ = 1`, (11.4) has the indeterminate form `0/0`; (11.5) is its
    limit as `ρ → 1`, which holds for every `β` (`eq_11_5`).
12. **The derivation of (11.7).** The book differentiates `0 = F(v_t(ρ), v_{t+1}(ρ), ρ)` twice in
    `ρ`. We differentiate the equivalent identity `s v(s) = ln((1 − β) + β e^{s q(s)})`,
    `s = 1 − ρ`, `q(s) = Q_t(v_{t+1}(1 − s) + c_{t+1} − c_t)`, twice at `s = 0`, assuming (as the
    book does) that `v` and `q` are twice differentiable (`eq_11_7_s`); (11.7) follows given
    `q'(0) = −Ẽ_t v_{t+1}'(1)` (`eq_11_7`). That `q'(0)` is a tilted expectation is proved for
    families `Y₀ + sY₁` under an integrable dominating function (`nq_Q_hasDerivAt`). The book's
    tilting density `V_{t+1}(1)^{1−γ}/E_t[V_{t+1}(1)^{1−γ}]` equals
    `e^{(1−γ)Y₀}/E_t e^{(1−γ)Y₀}` with `Y₀ = ln(V_{t+1}(1)/C_t)` because `C_t` is known at `t`.
13. **Exercise 11.2, explicit solution.** Matching coefficients in (11.7) for the conjecture
    `v_t'(1) = −A_d x_t²/2 + B_d x_t + μ_d` requires `βφ ≠ 1`, `βφ² ≠ 1`, `β ≠ 1` and gives
    `A_d = β(1 − β)/((1 − βφ)²(1 − βφ²))`, `B_d = −β[(1 − β)μ_v/(β(1 − βφ)) + A_d φ κ]/(1 − βφ)`,
    `μ_d = [−β(1 − β)(μ_v/β)²/2 − βA_d(κ² + σ_x²)/2 + βB_d κ]/(1 − β)`,
    `κ = (1 − γ)βσ_x²/(1 − βφ)` (`ex_11_2`); under `Ẽ_t`, `ε_x` is `N((1 − γ)Aσ_x, 1)`
    (`nq_ex_11_2_tilt`).
14. **Expectations.** `E_t` is an integral over a probability space (for (11.4) and (11.7)) or
    over `nqShock`, the law of the independent standard normal shocks (for (11.6) and
    Exercise 11.2).

## §11.3 Interpolation and Exercise 11.1

### §11.3.1 Orthogonal polynomials

15. **Definition 11.3.1, the induced norm.** The book writes `‖f‖_w = ⟨f, f⟩_w`. This is not a
   norm: it is not absolutely homogeneous (`ni_inner_self_not_homogeneous`: for `w = 1` on
   `(0, 1)`, `⟨2, 2⟩_w = 4 ≠ 2⟨1, 1⟩_w`). The norm is `‖f‖_w = √⟨f, f⟩_w` (`ni_wnorm`), which is
   absolutely homogeneous (`ni_wnorm_smul`) and satisfies the triangle inequality
   (`ni_wnorm_add_le`, via Cauchy–Schwarz `ni_inner_sq_le`).
16. **Definition 11.3.1, the domain.** The definition is stated for a bounded `[a, b]` and
   positivity on `[a, b]`, but the book then uses it for the Chebyshev weight `(1 − x²)^{−1/2}`
   (not defined, or infinite, at `±1`) and on `[0, ∞)` and `ℝ` (Laguerre, Hermite).
   `ni_IsWeightingFunction w s` asks for positivity and integrability on a set `s`; the instances
   are `(−1, 1)` (`definition_11_3_1`, `ni_chebWeight_isWeighting`), `(0, ∞)`
   (`ni_laguerre_weight`) and `ℝ` (`ni_hermite_weight`).
17. **Orthogonality of the classical families.** The book only names the weights; the
   orthogonality is proved from the Rodrigues formulas (`ni_legendre_orthogonal`,
   `ni_laguerre_orthogonal`, `ni_hermite_orthogonal`, Chebyshev `ni_cheb_orthogonal`). The
   Hermite polynomials of the book are the physicists' ones (`e^{−x²}`), not Mathlib's
   probabilists' `Polynomial.hermite`.
18. **Extrema of `Tₙ`.** "`Tₙ` has `n + 1` extrema" is read as extrema of `Tₙ` restricted to
   `[−1, 1]` (the endpoints `±1` are extrema only relative to `[−1, 1]`), for `n ≥ 1`
   (`ni_cheb_isLocalExtrOn_iff`, `ni_cheb_localMax_eq_one`, `ni_cheb_localMin_eq_neg_one`).
19. **Indexing in the coefficient formula.** The nodes are written `{x₁, x₂, …, x_k}` on p. 359;
   there are `n` of them, `x₁, …, xₙ` (`ni_chebNode`).
20. **Theorem 11.3.1 is false as printed** ("for all `n`"): for `f(x) = x²` and `k = 3`, the
   right side is `0` (`f''' = 0`) but `‖f − I₁f‖∞ ≥ 1/2` (the interpolant at the roots of `T₂` is
   the constant `1/2`) (`theorem_11_3_1_counterexample`; for `n = 0` the printed `dₖ/nᵏ` is not
   even defined). The bound holds for `n ≥ k` (`theorem_11_3_1`), as in Rivlin's statement
   (Jackson's theorem needs `n ≥ k`). Two further departures: `f` is assumed `C^k` on `ℝ` rather
   than on `[−1, 1]` (any `C^k` function on `[−1, 1]` extends; the extension theorem is not
   formalised), and the constant `dₖ` we obtain depends on `k` only (the book's "there is some
   `dₖ`" after fixing `f` is weaker). The proof is complete: Lebesgue inequality
   (`ni_lebesgue_inequality`), the logarithmic Lebesgue constant of the Chebyshev nodes with the
   non-sharp constant `4π(1 + ln(n + 1))` (`ni_lebesgueFn_le`; Rivlin's sharp
   `(2/π) ln(n + 1) + 1` is not needed since `dₖ` is free), and Jackson's theorem
   (`ni_jackson_lipschitz`, `ni_jackson_Ck`).
21. **"Does not necessarily converge" (p. 360)** is proved in the strong form: there is a
   continuous `f` on `[−1, 1]` whose interpolants at the uniform nodes do not converge uniformly
   (`ni_uniform_interp_not_convergent`, by the uniform boundedness principle and
   `‖Iₙ‖ ≥ 2^N/(4N²)`, `ni_uniformInterp_norm_ge`). The specific Runge function is not used.
22. **(11.2), p. 360.** "The difference is bounded by the sum of the dropped terms `cₖ`" holds
   with absolute values `∑ |cₖ|` (`ni_chebTruncation_bound`); the indices "`k = m + 1, …, cₙ`"
   mean `k = m + 1, …, n`.

### §11.3.2 Splines

23. **Order versus degree.** A spline of order `k` is a polynomial "of order at most `k − 1`" on
   each subinterval; the intended meaning (order 2 = linear, order 4 = cubic) is *degree* at most
   `k − 1` (`ni_IsSpline`).
24. **Cubic splines.** The book counts conditions but does not state existence or uniqueness;
    we prove that each of the two end conditions determines a unique cubic spline for all data:
    natural and Hermite (clamped) for every `n ≥ 1` (`ni_natural_spline_existsUnique`,
    `ni_clamped_spline_existsUnique`), not-a-knot for `n ≥ 3`
    (`ni_notAKnot_spline_existsUnique`). For `n = 2` the two not-a-knot conditions coincide and
    the spline is not unique (`ni_notAKnot_not_unique_two`: `t(t − 1)(t − 2)` on nodes
    `0, 1, 2`); for `n = 1` the condition is not meaningful. Conditions (i) and (iii) are stated
    on the pieces (the one-sided limits at a node are the values of the adjacent pieces).
25. **The order-2 B-spline formula (p. 362) has its numerators swapped.** The book prints
    `(ξⱼ₊₁ − x)/(ξⱼ₊₁ − ξⱼ)` on `[ξⱼ, ξⱼ₊₁]` and `(x − ξⱼ₊₁)/(ξⱼ₊₂ − ξⱼ₊₁)` on `[ξⱼ₊₁, ξⱼ₊₂]`;
    the recursion gives `(x − ξⱼ)/(ξⱼ₊₁ − ξⱼ)` and `(ξⱼ₊₂ − x)/(ξⱼ₊₂ − ξⱼ₊₁)` (on half-open
    intervals) (`ni_bspline_two`; `ni_bspline_two_book_formula_false`: knots `ξₘ = m`, `j = 0`,
    `x = 1/4` give `1/4`, the printed formula `3/4`).
26. **B-spline support.** `Bⱼₖ` vanishes outside the half-open `[ξⱼ, ξⱼ₊ₖ)` (stronger than the
    printed closed interval) for any monotone knot sequence (`ni_bspline_support`); the
    convention `0/0 = 0` handles repeated knots. The book's knot vector is `ni_bookKnots`.

### §11.3.3 Multidimensional approximation

27. **Tensor products.** The `d`-fold Kronecker product is indexed by multi-indices
    (`ni_tensorMatrix`); the stacking of the book's example is the lexicographic order with the
    first variable fastest (`ni_tensor_example_Φ`, via `finProdFinEquiv`).

### Exercise 11.1

28. The exercise is computational (CompEcon); only its mathematical content is formalised: the
    regularity of the two functions (`ex_11_1_f1_not_differentiable`, `ex_11_1_f1_continuous`,
    `ex_11_1_f2_smooth`) and the well-posedness of the four approximants (`ex_11_1`, for any
    degree `N ≥ 3`, in particular `5` and `20`, with `N + 1` uniform nodes).

## §11.5, §11.6 and Exercise 11.3

### §11.5

29. **Collocation needs point evaluation.** The book obtains `R(xᵢ; c) = 0` from
   `⟨R, pᵢ⟩ = 0` with `pᵢ` the indicator of `{xᵢ}`. Under an integral inner product this is
   false: the indicator of a point is zero almost everywhere, so `⟨R, pᵢ⟩ = 0` for every `R` and
   the conditions say nothing (`np_collocation_integral_degenerate`). True: with a discrete
   (quadrature) inner product whose nodes contain the collocation points, with nonzero weights,
   `Pᵢ(c) = wᵢR(xᵢ; c)`, so the projection conditions are exactly collocation
   (`np_collocation_proj`, `np_collocation_iff`).
30. **Footnote 7 holds for orthogonal polynomials, not for arbitrary basis functions.** "The
   `(n+1)`-th basis function has degree `n` leading polynomial term and hence exactly `n` roots"
   is false as a general statement: `X² + 1` has degree 2 and no real roots
   (`np_footnote7_counterexample`). For the Chebyshev basis it is true: `T_n` has degree `n` and
   `n` distinct real roots, the Chebyshev nodes (`np_footnote7_chebyshev`).
31. **Index typo in the least squares directions.** The book prints `pᵢ(x) = ∂R(x; c)/∂cⱼ`; the
   intended direction is `∂R/∂cᵢ` (`np_ls_hasFDerivAt`, `np_ls_foc`).
32. **Least squares projection conditions are only first-order conditions.** The book says the
   least squares projection conditions are "equivalent to" `min_c ⟨R, R⟩`. True: a minimiser
   satisfies them (`np_ls_foc`), and when the residual is affine in `c` they are equivalent to
   minimisation (`np_ls_affine_iff`; for `F(f) = f − h` they coincide with Galerkin,
   `np_galerkin_iff_ls`). False in general: for `R(c) = c² − 1` the conditions hold at `c = 0`,
   which is not a minimiser (`np_ls_not_sufficient`).

### §11.6

33. **"The truncated problem can approximate the original problem arbitrarily closely"** (p. 377)
   is not a precise statement (no metric or rate is given) and is not formalised as such. What is
   proved is the standard bound behind it: if two Bellman operators are `β`-contractions within
   `ε` of each other uniformly, their value functions are within `ε/(1 − β)`
   (`np_fixedPt_perturbation`).
34. **Value function interpolation converges for averaging interpolants.** The book says only
   "keep iterating until convergence" (p. 380). We prove that with an interpolant of the form
   `V̂(k', s) = ∑_m w_m(k')V(k_m, s)`, `w_m ≥ 0`, `∑_m w_m = 1` on `[k_min, k_max]` (e.g. linear
   interpolation, `np_linWeights_averager`), and period utility bounded above on the choice
   interval, the fitted Bellman operator is a `β`-contraction with a unique fixed point to which
   the iteration converges (`FittedGrid.np_fitted_contraction`, `FittedGrid.np_fitted_converges`).
   Convergence for non-averaging interpolants (cubic splines, Chebyshev) is not claimed.
35. **Discretised problem (11.10) taken literally.** (11.10) maximises over all `k' ∈ K` without
   the positivity of consumption from (11.9); we follow (11.10) with `u` an arbitrary real
   function (infeasible choices can be penalised through `u`) (`GrowthGrid.toMDP`).
36. **Puterman–Brumelle.** Formalised as the identity that the policy-iteration update is the
   Newton step `V − (I − βP_g)⁻¹(V − BV)` with `I − βP_g` the Jacobian of `(I − B)` along the
   `V`-greedy rule `g` (`GrowthGrid.np_pfi_newton`); the quadratic convergence rate is cited, not
   formalised.
37. **Euler equation (11.8) and the envelope condition (11.14) are derived under explicit
   differentiability hypotheses.** The book states (11.8) and that "`m` is the derivative of the
   value function" without derivation. We derive them from the Bellman equation, assuming the
   value function is differentiable in capital and that `k' ↦ E[V(k', z')|z]` is differentiable
   with derivative `E[V_K(k', z')|z]` (differentiation under the integral); the conditional law of
   `z'` is an arbitrary family of measures (`eq_11_8`, `eq_11_14_envelope`, `np_envelope`).
   The inequality `m ≥ 0` in (11.14) is proved directly for `f = zk^α + (1 − δ)k` from
   `h = u'(c) − e` with `e ≥ 0` (`eq_11_14_pos`), not from monotonicity of `V`.
38. **PEA.** The equivalence of the PEA system with the Kuhn–Tucker conditions needs `u'`
    strictly decreasing with an inverse on the positive reals, `e > 0`, and positive consumption
    when the constraint binds, `f(k, z) > (1 − δ)k` (`np_pea_kkt`, `np_pea_kkt_unique`).

### Exercise 11.3

39. **Euler equations derived under the same differentiability hypotheses as in item 37**, with
    `γ ≠ 1` (the case `γ = 1` is the log limit, not the printed formula) and an interior optimum
    `K' > 0`, `0 < N < 1`, `C > 0` (`ex_11_3_euler`). The steady-state ratio
    `K/N = (α/(1/β − 1 + δ))^{1/(1−α)}` is for `z = 1` (`ex_11_3_steady_state`).
