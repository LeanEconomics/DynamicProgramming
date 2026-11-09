# Source map: Miao Chapter 11

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 11, Numerical
Methods, pp. 347–384. Lean names are relative to `Miao.NumericalMethods`. Only the theorems of the
chapter are formalised; algorithmic descriptions, toolbox calls and numerical output are recorded as
not formalised. The §11.5–11.6 names are in `Miao.NumericalMethods.NP`. Departures from the book are
in [corrections](corrections.md).

## §11.1, §11.2, §11.4 and Exercise 11.2

### §11.1 Numerical Integration

### §11.1.1 Gaussian quadrature (pp. 347–349)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 347 | Numerical methods for `∫_D f(x) dx` (Judd 1998); the CompEcon toolbox | Not formalised: algorithmic/computational |
| p. 348 | Quadrature: `∫ₐᵇ f ≃ ∑ wᵢ f(xᵢ)` | `nqQuad` |
| p. 348 | Newton–Cotes methods are an example | Not formalised: named only, no claim |
| p. 348 | The `2n` conditions `∫ xᵏ w(x) dx = ∑ wᵢ xᵢᵏ`, `k = 0, …, 2n − 1` | `nqIsGaussRule` |
| p. 348 | The rule then integrates `f w` exactly when `f` is a polynomial (degree `≤ 2n − 1`) | `nq_quad_exact_of_moments`, `nq_gauss_exact` |
| p. 348 | `2n` is the most `n` nodes can achieve (implicit in "2n conditions") | `nq_gauss_not_exact_two_mul` |
| p. 348 | For a density `w`, the rule is a discrete random variable with mass points `xᵢ` and probabilities `wᵢ` | `nq_gauss_weights_nonneg`, `nq_gauss_probability` |
| pp. 348–349 | Computing nodes and weights requires solving `2n` nonlinear equations; CompEcon routines | Not formalised: algorithmic/computational |
| p. 349 | Gauss–Legendre: weight `1` on `[−1, 1]`; change of variables to `[a, b]` | `nq_legendre_change_of_variables`, `nq_legendre_interval_exact` |
| p. 349 | Gauss–Legendre rules (instances) | `nq_legendre_one_point`, `nq_legendre_two_point` |
| p. 349 | "and hence infinite intervals" | Not formalised: no transformation is given |
| p. 349 | Gauss–Chebyshev: `∫₋₁¹ f(x)(1 − x²)^{−1/2} dx ≃ (π/n) ∑ f(xᵢ)`, `xᵢ = cos((2i − 1)π/(2n))` | `nqChebNode`, `nq_chebyshev_exact`, `nq_chebyshev_isGaussRule` |
| p. 349 | (ingredients) substitution `x = cos θ`; `∫₀^π cos kθ = 0`, `∑ᵢ cos kθᵢ = 0` for `1 ≤ k ≤ 2n − 1`; exactness on `Tₖ` | `nq_chebyshev_substitution`, `nq_chebyshev_integrableOn`, `nq_integral_cos_nat_mul`, `nq_cheb_sum_cos`, `nq_chebyshev_T_exact`, `nq_chebyshev_exact_theta` |
| p. 349 | Gauss–Hermite: `∫ f(x) e^{−x²} dx ≃ ∑ wᵢ f(xᵢ)` (instances, moments) | `nq_hermite_one_point`, `nq_hermite_two_point`, `nq_integral_exp_neg_sq`, `nq_integral_sq_mul_exp_neg_sq`, `nq_integral_odd_eq_zero`, `nq_integrable_pow_mul_exp_neg_sq` |
| p. 349 | `E f(Y) = π^{−1/2} ∑ wᵢ f(√2 σ xᵢ + μ)` for `Y ~ N(μ, σ²)` | `nq_normal_expectation_hermite` (exact change of variables), `nq_normal_expectation_gauss_hermite` (exact for degree `≤ 2n − 1`) |
| p. 349 | Gauss–Laguerre `∫₀^∞ e^{−x} f(x) dx ≃ ∑ wᵢ f(xᵢ)`; present values `∫ₐ^∞ e^{−ry} f(y) dy = (e^{−ra}/r) ∫₀^∞ e^{−x} f(x/r + a) dx` | `nq_laguerre_present_value` (with `nq_integral_Ioi_shift`) |

### §11.1.2 Multidimensional quadrature (p. 350)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 350 | The product rule `∑_{i₁} ⋯ ∑_{i_d} w¹_{i₁} ⋯ w^d_{i_d} f(x¹_{i₁}, …, x^d_{i_d})` | `nqProdQuad`, `nq_prodQuad_prod` |
| p. 350 | With `W(x) = ∏ⱼ wⱼ(xⱼ)`, Gaussian product quadrature computes `∫ f W` | `nq_prod_gauss_exact` (exact on `∏ⱼ pⱼ(xⱼ)`, `deg pⱼ ≤ 2nⱼ − 1`) |
| p. 350 | Change of variables to any interval | Not formalised separately (one-dimensional: `nq_legendre_change_of_variables`) |
| p. 350 | Curse of dimensionality | `nq_prodQuad_card` (`∏ⱼ nⱼ` nodes) |
| p. 350 | Nonproduct approaches (Judd 1998) | Not formalised: reference only |

### §11.2 Discretizing AR(1) Processes (pp. 350–354)

| Source | Claim | Lean |
| --- | --- | --- |
| (11.1), pp. 350–351 | `μ` is the unconditional mean | `nq_ar1_mean_fixed` |
| p. 351 | `σ_z = σ/√(1 − ρ²)` is the unconditional standard deviation | `nq_ar1_variance_fixed`, `nq_ar1_stationary_law` |
| p. 351 | "Making `N` larger, the approximation becomes more accurate" | Not formalised: no precise statement in the text |
| p. 351, Step 1 | `N` equally spaced points from `z_min = −mσ_z` to `z_max = mσ_z` | `nqTauchenGrid`, `nq_tauchen_grid_first`, `nq_tauchen_grid_last`, `nq_tauchen_grid_step`, `nq_tauchen_grid_symm` |
| p. 351, Step 1 | "In practice, setting `m = 3` or `4` is sufficient" | Not formalised: algorithmic/computational |
| p. 351, Step 2 | The `N` intervals `I₁, …, I_N` | `nqCell`, `nq_cell_eq`, `nq_cell_measurable`, `nqTauchenCut`, `nq_tauchen_cut_midpoint`, `nq_tauchen_cut_monotone`; printed endpoints: `nq_tauchen_printed_I2_upper`, `nq_tauchen_printed_IN_lower` (correction 1) |
| p. 351, Step 3 | `π_{ij} = Pr(z_{t+1} ∈ I_j \| z_t = zⁱ)`, computed from (11.1) | `nqTauchenProb`, `nq_tauchen_law`, `nq_tauchen_prob_eq` |
| p. 351 | `(π_{ij})` is a transition matrix | `nq_tauchen_stochastic`, `nq_cells_sum_one` |
| p. 352 | Tauchen–Hussey: `E[v(z')\|z] = ∫ v(z') f(z'\|z) dz'`, Gauss–Hermite with `√2σxⱼ + ρz` | `nqCondDens`, `nq_th_conditional_expectation` |
| p. 352 | "this approximation depends continuously on `z`" | No formal content |
| p. 352 | The transformation `∫ v f(·\|z) = ∫ v (f(·\|z)/f(·\|0)) f(·\|0)` | `nq_th_change_of_measure`, `nq_th_ratio` |
| p. 352 | `E[v(z')\|zⁱ] ≃ ∑ⱼ π̃_{ij} v(zʲ)`, `zʲ = √2σxⱼ`, `π̃_{ij} = π^{−1/2} wⱼ f(zʲ\|zⁱ)/f(zʲ\|0)` | `nqTHTilde`, `nq_th_exact` (correction 2) |
| p. 352 | "we may have `∑ⱼ π̃_{ij} ≠ 1`" | `nq_th_rowsum_lt_one` |
| p. 352 | The normalised `π_{ij} = π̃_{ij}/∑ⱼ π̃_{ij}` | `nq_normalize_stochastic`, `nq_th_normalized_stochastic` |
| p. 353 | "this is not the Gauss–Hermite approximation of the integral" | No formal content |
| p. 353 | As `N` grows, `∑ⱼ π̃_{ij}` converges to one | `nq_th_rowsum_integral` (the row sum is the Gauss–Hermite approximation of an integral equal to `1`); the convergence itself is not formalised (needs the convergence theory of Gaussian quadrature) |
| p. 353, Steps 1–3 | Simulating a Markov chain by the cumulative distribution `Π^c_{ij}` and uniform draws | `nq_sim_interval_volume` (state `j` drawn with probability `π_{ij}`), `nq_sim_unique` (each draw in `(0, 1]` selects one state); the procedure itself not formalised: algorithmic/computational |
| footnotes 2–4 | Matlab codes `markovappr.m`, `tauch_hussey.m`, `gauss_herm.m`, `markovsimul.m` | Not formalised: algorithmic/computational |
| (task brief) | Rouwenhorst method | Not in this draft of the text: nothing to formalise |

### §11.4 Perturbation Methods (pp. 366–370)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 366–367 | Perturbation idea: implicit function theorem and Taylor expansion | No formal content beyond the example |
| (11.3), p. 367 | Recursive utility and `R_t(V_{t+1}) = (E_t V_{t+1}^{1−γ})^{1/(1−γ)}` | `nqCertEquiv` |
| p. 367 | Consumption growth and `x_t` dynamics, independent standard normal shocks | `nqShock` |
| (11.4), p. 368 | `v_t = (1 − ρ)^{−1} ln((1 − β) + β exp[(1 − ρ)Q_t(v_{t+1} + c_{t+1} − c_t)])` | `nqQ`, `eq_11_4` |
| (11.5), p. 368 | When `ρ = 1`, `v_t = βQ_t(v_{t+1} + c_{t+1} − c_t)` | `eq_11_5` (limit `ρ → 1`); also `eq_11_7_s` (first conclusion) |
| (11.6), p. 368 | The guess `v_t = A x_t + μ_v` | `eq_11_6` |
| p. 368 | `ln E_t exp[(1 − γ)(v_{t+1} + c_{t+1} − c_t)] = (1 − γ)[(Aρ + 1)x_t + μ_v + μ_c] + (1 − γ)²/2[(Aσ_x)² + σ_c²]` | `eq_11_6_mgf` (with `nq_gauss_exp_integral`, `nq_shock_exp`) |
| p. 368 | Matching coefficients: `A = β/(1 − βρ)`, `μ_v = β/(1 − β)[μ_c + (1 − γ)/2((βσ_x/(1 − βρ))² + σ_c²)]` | `eq_11_6` |
| p. 369 | `v_t(ρ) ≃ v_t(1) + (ρ − 1)v_t'(1)` | `nq_pert_taylor_first_order` |
| p. 369 | `0 = F(v_t(ρ), v_{t+1}(ρ), ρ)`; differentiate in `ρ`; at `ρ = 1`, `v_t(1)`, `v_{t+1}(1)` satisfy (11.5) | `eq_11_7_s` (first conclusion), with `nq_h_hasDerivAt`, `nq_h'_hasDerivAt_zero` |
| (11.7), p. 369 | `v_t'(1) = −β(1 − β)/2 [Q_t(v_{t+1}(1) + c_{t+1} − c_t)]² + β Ẽ_t v_{t+1}'(1)` | `eq_11_7_s`, `eq_11_7` |
| p. 369 | `Ẽ_t` is the expectation under the density `V_{t+1}(1)^{1−γ}/E_t[V_{t+1}(1)^{1−γ}]` | `nq_Q_hasDerivAt`, `nqTilt` |
| p. 369 | The conjecture `v_t'(1) = −A_d x_t²/2 + B_d x_t + μ_d`; matching coefficients determines `A_d, B_d, μ_d` | `ex_11_2` |

### Exercise 11.2 (p. 383)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 11.2 | Complete the solution for the example in §11.4 | `ex_11_2`; ingredients `nq_ex_11_2_Q`, `nq_ex_11_2_a`, `nq_ex_11_2_b`, `nq_gauss_tilt`, `nq_gauss_quad`, `nq_ex_11_2_tilt`, `nq_ex_11_2_match` |

## §11.3 Interpolation and Exercise 11.1

### §11.3 Interpolation (pp. 354–356)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 354 | Local (Taylor/perturbation), `Lᵖ` and interpolation approaches; regression between them | Not formalised: descriptive overview, no claim |
| p. 354 | The interpolant `f̂(x) = ∑ⱼ cⱼ φⱼ(x)` | `ni_fhat` |
| p. 355 | Spectral vs finite element bases | Not formalised: descriptive |
| p. 355 | The interpolation equation `Φc = y`, `Φᵢⱼ = φⱼ(xᵢ)` | `ni_interpMatrix`, `ni_interp_eq_iff` |
| p. 355 | Least squares: `c = (Φ'Φ)⁻¹Φ'y` minimises `∑ᵢ (f(xᵢ) − ∑ⱼ cⱼφⱼ(xᵢ))²` | `ni_ssr`, `ni_normal_equations`, `ni_leastSquares_optimal` |
| p. 356 | Equivalent to the interpolation equation if `m = n` and `Φ` invertible | `ni_leastSquares_eq_interp` |
| p. 356 | Derivative data may also be used | Not formalised: remark, no claim |

### §11.3.1 Orthogonal Polynomials (pp. 356–360)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 356 | Monomial basis: `Φ` is the Vandermonde matrix | `ni_monomial`, `ni_monomial_interpMatrix` |
| p. 356 | (implicit) Vandermonde invertible iff nodes distinct; unique interpolant; Lagrange form | `ni_monomial_interp_unique`, `ni_monomial_interp_existsUnique`, `ni_poly_interp_unique` |
| p. 356 | Monomial interpolation is ill-conditioned (large rounding error) | Not formalised: qualitative numerical claim |
| p. 356 | The monomials are not mutually orthogonal | `ni_monomials_not_orthogonal` |
| Definition 11.3.1, p. 356 | Weighting function, inner product `⟨f, g⟩_w`, mutual orthogonality | `ni_IsWeightingFunction`, `ni_inner`, `ni_Orthogonal`, `definition_11_3_1` |
| p. 356 | Properties of the inner product | `ni_inner_comm`, `ni_inner_add_left`, `ni_inner_smul_left`, `ni_inner_self_nonneg`, `ni_inner_sq_le` |
| p. 356 | The induced norm and metric (corrected to `√⟨f, f⟩_w`) | `ni_wnorm`, `ni_wnorm_smul`, `ni_wnorm_add_le`, `ni_inner_self_not_homogeneous` |
| p. 357 | Legendre polynomials by Rodrigues' formula, `P₀ = 1` | `ni_legendreGen`, `ni_legendre`, `ni_legendre_eval_eq_iteratedDeriv`, `ni_legendre_zero`, `ni_legendre_natDegree_le`, `ni_iteratedDeriv_eval` |
| p. 357 | Legendre: weight `1` on `[−1, 1]` (orthogonality) | `ni_poly_parts`, `ni_legendreGen_iterate_root`, `ni_legendre_parts`, `ni_legendre_orthogonal_low`, `ni_legendre_orthogonal` |
| p. 357 | The transformation `z = 2(x − a)/(b − a) − 1` to `[a, b]` | `ni_affine_maps_Icc`, `ni_legendre_shifted_orthogonal` |
| p. 357 | Chebyshev: `T₀ = 1`, `T₁ = x`, `T₂ = 2x² − 1`, `Tₙ = 2xTₙ₋₁ − Tₙ₋₂` | `ni_cheb_recursion` |
| p. 357 | Chebyshev weight `(1 − x²)^{−1/2}` (orthogonality, norms) | `ni_chebWeight`, `ni_chebWeight_eq`, `ni_chebWeight_isWeighting`, `ni_inner_cheb_eq`, `ni_cheb_orthogonal`, `ni_cheb_norms` |
| p. 357 | `Tₙ(x) = cos(n arccos x)` | `ni_cheb_cos`, `ni_cheb_arccos` |
| p. 357 | Laguerre polynomials by Rodrigues' formula, `L₀ = 1`, weight `e^{−x}` on `[0, ∞)` | `ni_lagOp`, `ni_hasDerivAt_poly_mul_exp_neg`, `ni_iteratedDeriv_poly_mul_exp_neg`, `ni_laguerre`, `ni_laguerre_eval_eq_rodrigues`, `ni_laguerre_zero`, `ni_lagOp_natDegree_le`, `ni_laguerre_natDegree_le`, `ni_laguerre_weight`, `ni_integrableOn_pow_mul_exp_neg`, `ni_integrableOn_poly_mul_exp_neg`, `ni_tendsto_poly_mul_exp_neg`, `ni_integral_lagOp`, `ni_lagOp_iterate_eval_zero`, `ni_laguerre_parts`, `ni_laguerre_orthogonal_low`, `ni_laguerre_orthogonal` |
| p. 357 | Laguerre polynomials approximate functions of time | Not formalised: remark on use |
| p. 357 | Hermite polynomials by Rodrigues' formula, `H₀ = 1`, weight `e^{−x²}` on `ℝ` | `ni_hermOp`, `ni_hasDerivAt_poly_mul_exp_neg_sq`, `ni_iteratedDeriv_poly_mul_exp_neg_sq`, `ni_hermite`, `ni_hermite_eval_eq_rodrigues`, `ni_hermite_zero`, `ni_hermOp_natDegree_le`, `ni_hermite_natDegree_le`, `ni_hermite_weight`, `ni_integrable_pow_mul_exp_neg_sq`, `ni_integrable_poly_mul_exp_neg_sq`, `ni_tendsto_pow_mul_exp_neg_sq`, `ni_tendsto_poly_mul_exp_neg_sq`, `ni_integral_hermOp`, `ni_hermite_parts`, `ni_hermite_orthogonal_low`, `ni_hermite_orthogonal` |
| p. 357 | Hermite polynomials approximate functions of normal variables | Not formalised: remark on use |
| p. 357 | The roots of `Tₙ` are `xₖ = cos(π(2k − 1)/(2n))`, `k = 1, …, n` | `ni_chebNode`, `ni_chebNode_succ`, `ni_cheb_roots`, `ni_chebNode_injOn` |
| p. 358 | `Tₙ` has `n + 1` extrema at `cos(πk/n)`; `Tₙ = 1` at maxima, `−1` at minima | `ni_cheb_extrema_value`, `ni_cheb_extrema_injOn`, `ni_cheb_abs_le_one`, `ni_cheb_not_locally_const`, `ni_cheb_localExtr_value`, `ni_cheb_isLocalExtrOn_iff`, `ni_cheb_localMax_eq_one`, `ni_cheb_localMin_eq_neg_one` |
| p. 358, Figure 11.1 | Chebyshev basis functions up to degree 9 | Not formalised: figure |
| p. 358 | Discrete orthogonality `∑ₖ Tᵢ(xₖ)Tⱼ(xₖ) = 0, m/2, m` | `ni_cheb_discrete_orthogonality` |
| p. 359 | Basis `φⱼ = Tⱼ₋₁`, nodes the roots of `Tₙ`; `Φ'Φ = diag(n, n/2, …, n/2)` | `ni_chebPhi`, `ni_chebGramDiag`, `ni_chebPhi_gram`, `ni_chebGramDiag_ne_zero`, `ni_chebGram_isUnit`, `ni_sum_fin_succ` |
| p. 359 | The coefficients `cⱼ` (both forms) | `ni_chebData`, `ni_chebCoeff`, `ni_chebCoeff_eq`, `ni_chebCoeff_eq_ratio` |
| p. 359 | The Chebyshev interpolant `I_{n−1}^f` matches `f` at the `n` roots of `Tₙ` | `ni_chebInterpolant`, `ni_chebInterpolant_nodes` |
| Theorem 11.3.1, p. 359 | The degree-`n` Chebyshev interpolant `Iₙf` | `ni_chebInterp`, `ni_chebInterp_spec`, `ni_chebInterp_eq_coeff_form` |
| Theorem 11.3.1, p. 359 | Chebyshev Interpolation Theorem (corrected: `n ≥ k`) | `theorem_11_3_1` |
| Theorem 11.3.1, p. 359 | As printed ("for all `n`") the bound is false | `ni_Theorem_11_3_1_bound`, `theorem_11_3_1_counterexample` |
| Theorem 11.3.1 (proof) | Lebesgue inequality | `ni_lebesgueFn`, `ni_lebesgue_inequality` |
| Theorem 11.3.1 (proof) | Lebesgue constant of the Chebyshev nodes `≤ 4π(1 + ln(n + 1))` | `ni_chebAngle`, `ni_chebAngle_mem`, `ni_cheb_deriv_cos`, `ni_cheb_deriv_node`, `ni_basis_mul_eq`, `ni_sin_le_two_sin_half`, `ni_basis_abs_le`, `ni_harmonic_le`, `ni_harmonic_sum_le`, `ni_lebesgueFn_le` |
| Theorem 11.3.1 (proof) | Jackson kernel | `ni_cheb_expand`, `ni_dirPoly`, `ni_fejPoly`, `ni_jackPoly`, `ni_jackK`, `ni_dir`, `ni_fej`, `ni_dirPoly_eval`, `ni_fejPoly_eval`, `ni_jackK_eq`, `ni_jackK_nonneg`, `ni_jackK_continuous`, `ni_jackK_even`, `ni_jackK_periodic`, `ni_jackPoly_natDegree`, `ni_dir_identity`, `ni_fej_identity`, `ni_fej_abs_le`, `ni_fej_ge`, `ni_one_sub_cos_ge`, `ni_fej_le`, `ni_jackK_mass_ge`, `ni_jackK_moment_le` |
| Theorem 11.3.1 (proof) | Jackson's theorem (Lipschitz, then `C^k`) | `ni_conv_poly`, `ni_jacksonC`, `ni_jacksonC_pos`, `ni_jackson_lipschitz`, `ni_supNorm`, `ni_le_supNorm`, `ni_supNorm_nonneg`, `ni_supNorm_le`, `ni_antideriv`, `ni_antideriv_derivative`, `ni_antideriv_natDegree`, `ni_jackson_Ck` |
| p. 360 | Interpolation at uniformly spaced nodes does not necessarily converge | `ni_prod_odd_ge`, `ni_prod_dist_eq`, `ni_uniform_basis_lower`, `ni_uniform_lebesgue_lower`, `ni_uniformGrid_mem`, `ni_uniformInterp`, `ni_uniformInterp_apply`, `ni_uniformInterp_eq_interpolate`, `ni_linSpline_abs_le`, `ni_uniformInterp_norm_ge`, `ni_uniform_interp_not_convergent` |
| p. 360 | The Chebyshev interpolant is extremely useful whenever the function is smooth | `theorem_11_3_1` (quantitative form) |
| (11.2), p. 360 | The truncation error is bounded by the sum of the dropped `|cₖ|` | `ni_chebTruncation_bound` |
| p. 360 | The truncated series is dominated by `c_{m+1}T_m` and almost the minimax polynomial | Not formalised: heuristic (depends on unquantified coefficient decay) |
| p. 360 | Chebyshev regression algorithm (Judd 1998) | Not formalised: algorithmic/computational |

### §11.3.2 Splines (pp. 360–363)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 361 | Spline of order `k` | `ni_IsSpline` |
| p. 361 | A spline of order 2 is piecewise linear | `ni_spline_two_piecewise_linear` |
| p. 361 | (linear spline interpolation, used in Exercise 11.1) existence and uniqueness | `ni_node_interval`, `ni_affine_eq`, `ni_linear_spline_unique`, `ni_slope`, `ni_linSpline`, `ni_linSpline_piece`, `ni_linear_spline_exists` |
| p. 361 | Cubic spline (i)–(iii): pieces, interpolation, continuity of `φ, φ', φ''` | `ni_cub`, `ni_cub1`, `ni_cub2`, `ni_cub3`, `ni_hasDerivAt_cub`, `ni_hasDerivAt_cub1`, `ni_hasDerivAt_cub2`, `ni_piece`, `ni_CubicInterp`, `ni_CubicSmooth` |
| p. 361 | `4n − 2` conditions for `4n` coefficients | `ni_cubic_condition_count` |
| p. 361 | Two end conditions determine the spline (reduction to the homogeneous problem) | `ni_splineL`, `ni_splineTarget`, `ni_splineL_eq_iff`, `ni_spline_existsUnique_of_homogeneous`, `ni_cub_taylor`, `ni_moment`, `ni_moment_facts`, `ni_moments_zero`, `ni_moment_interior` |
| p. 361 | Natural spline `φ''(x₀) = φ''(xₙ) = 0` | `ni_naturalE`, `ni_natural_homogeneous`, `ni_natural_spline_existsUnique` |
| p. 361 | Hermite (clamped) spline `φ'(x₀) = f'(x₀)`, `φ'(xₙ) = f'(xₙ)` | `ni_clampedE`, `ni_clamped_homogeneous`, `ni_clamped_spline_existsUnique` |
| p. 361 | Not-a-knot end condition | `ni_notAKnotE`, `ni_notAKnot_row`, `ni_notAKnot_end`, `ni_notAKnot_homogeneous`, `ni_notAKnot_spline_existsUnique`, `ni_notAKnot_not_unique_two` |
| p. 361 | Cubic splines approximate functions with kinks; Matlab spline toolbox defaults | Not formalised: qualitative/computational |
| p. 361 | pp-form of a spline piece | `ni_ppForm_exists` |
| p. 362 | B-splines: `Bⱼ₁` and the Cox–de Boor recursion | `ni_Bdeg`, `ni_bspline`, `ni_bspline_one`, `ni_bspline_recursion` |
| p. 362 | The knot sequence `ξ₁ = ⋯ = ξₖ = x₀ < ⋯`, `ξₖ₊ᵢ = xᵢ` | `ni_bookKnots`, `ni_bookKnots_monotone`, `ni_bookKnots_breaks` |
| p. 362 | `Bⱼₖ` is nonnegative, zero outside `[ξⱼ, ξⱼ₊ₖ]`, piecewise polynomial of degree `k − 1` | `ni_Bdeg_support`, `ni_bspline_support`, `ni_Bdeg_nonneg`, `ni_bspline_nonneg`, `ni_Bdeg_zero_on`, `ni_Bdeg_piecewise_poly`, `ni_bspline_piecewise_poly` |
| p. 362 | B-form `φ = ∑ Bⱼₖ aⱼ` (de Boor points) | `ni_bform_piecewise_poly` |
| p. 362 | Every spline has a unique B-form (de Boor 1978) | Not formalised: cited theorem (Curry–Schoenberg), not proved in the book |
| p. 362 | Order-2 B-splines are tent functions (formula corrected) | `ni_bspline_two`, `ni_bspline_two_book_formula_false` |
| pp. 362–364, Figures 11.2–11.3 | Linear and cubic B-splines on uniform breaks | Not formalised: figures |
| p. 363 | Schumaker's shape-preserving quadratic spline (Judd 1998); `schumaker.m` | Not formalised: construction cited, no property stated in the book |

### §11.3.3 Multidimensional Approximation (pp. 364–366)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 364 | Tensor-product basis `φ_{j₁⋯j_d} = ∏ φᵢⱼᵢ(xᵢ)` | `ni_tensorBasis` |
| p. 365 | On the tensor grid, `Φ = Φ_d ⊗ ⋯ ⊗ Φ₁` | `ni_tensorMatrix`, `ni_tensor_interpMatrix` |
| p. 365 | If each `Φᵢ` is invertible, `c = (Φ_d⁻¹ ⊗ ⋯ ⊗ Φ₁⁻¹)y` | `ni_tensorMatrix_mul`, `ni_tensorMatrix_one`, `ni_tensor_inverse`, `ni_tensor_coeff` |
| p. 365 | Least squares when nodes exceed the degree | `ni_leastSquares_optimal` (general) |
| pp. 365–366 | Miranda–Fackler example: `φ(x)`, `Φ₁`, `Φ₂`, `Φ = Φ₂ ⊗ Φ₁`, `X` | `ni_tensor_example_basis`, `ni_tensor_example_Φ₁`, `ni_tensor_example_Φ₂`, `ni_tensor_example_Φ`, `ni_tensor_example_X`, `ni_tensor_example_invertible` |
| p. 366 | Curse of dimensionality: `n = ∏ nᵢ` grid points | `ni_tensor_card` |
| p. 366 | Complete polynomial bases (Judd 1998) | Not formalised: recommendation by reference, no claim |

### Exercise 11.1 (p. 383)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 11.1 | Use the CompEcon toolbox to compute and plot the approximants and errors | Not formalised: algorithmic/computational |
| Exercise 11.1 | `|x|^{0.6}` is continuous but not differentiable at `0`; `(1 + 2x²)^{−1}` is `C^∞` | `ex_11_1_f1_not_differentiable`, `ex_11_1_f1_continuous`, `ex_11_1_f2_smooth` |
| Exercise 11.1 (a)–(d) | The four approximants are well defined (existence/uniqueness) on the uniform grid and Chebyshev nodes | `ni_uniformGrid`, `ni_uniformGrid_strictMono`, `ni_uniformGrid_ends`, `ex_11_1` |

## §11.5, §11.6 and Exercise 11.3

### §11.5 Projection methods

| Source | Claim | Lean |
| --- | --- | --- |
| p. 370 | Approximation `f̂(x; c) = ∑ⱼ cⱼφⱼ(x)` | `np_approx` |
| p. 371, Steps 1–5 | Residual `R(x; c) = F̂(f̂(·; c))`, projections `Pᵢ(c) = ⟨R, pᵢ⟩`; choosing basis, degree, iterating | `np_residual`, `np_proj`; the steps themselves: not formalised (algorithmic) |
| p. 371 | Collocation directions; `Pᵢ(c) = 0 ⇔ R(xᵢ; c) = 0` | `np_collocDir`, `np_quadIP`, `np_collocation_proj`, `np_collocation_iff`; under an integral inner product the conditions are vacuous (correction 1): `np_collocation_integral_degenerate` |
| p. 372 | Orthogonal collocation at the `n` roots of `T_n` | `np_chebNode`, `np_footnote7_chebyshev` |
| p. 372 | "Chebyshev interpolation theorem ... forces `R` close to zero"; "best possible points" | not formalised here (§11.3, Chebyshev interpolation theorem, other part) |
| Footnote 7, p. 372 | The `(n+1)`-th basis function has degree `n` and exactly `n` roots | Chebyshev basis: `np_footnote7_chebyshev`; false in general (correction 2): `np_footnote7_counterexample` |
| p. 372 | Least squares directions `∂R/∂cᵢ` (printed `∂cⱼ`, correction 3); gradient of `⟨R, R⟩` | `np_ls_hasFDerivAt` |
| p. 372 | "Equivalent to `min_c ⟨R, R⟩`" | necessary: `np_ls_foc`; equivalent for affine residuals: `np_ls_affine_iff`; not sufficient in general (correction 4): `np_ls_not_sufficient` |
| p. 372 | Galerkin: `⟨R, φᵢ⟩ = 0` | `np_galerkin_iff_orthogonal` (`R ⊥ span φ`); Galerkin = least squares for `F(f) = f − h`: `np_galerkin_iff_ls` |
| p. 373 | Method of moments `pᵢ = x^{i−1}` | `np_momentDir`; with quadrature at `n` distinct nodes it is collocation: `np_moments_iff_collocation` |
| p. 373 | Collocation is fastest; quadrature used for inner products | not formalised (computational) |
| p. 373 | Quadrature-based projections are weighted collocation methods | `np_quadrature_proj_eq`, `np_quadrature_proj_congr`, `np_quadrature_iff_collocation`, `np_galerkin_quadrature_iff_collocation` |
| p. 373 (and §11.3) | Regression with as many nodes as coefficients is interpolation | `np_regression_iff_interpolation`; Chebyshev case: `np_cheb_discrete_orth`, `np_cheb_basis_det_ne_zero`, `np_cheb_regression_iff_collocation`, `np_cheb_sum_T`, `np_cheb_not_dvd` |
| pp. 372–373 | Orthogonal collocation and Galerkin with Gauss–Chebyshev quadrature coincide | `np_cheb_galerkin_iff_collocation` |
| p. 373 | Root finding, initial guesses | not formalised (algorithmic) |
| pp. 373–374, (11.8) | Growth model; Euler equation (11.8) | derived from (11.9): `eq_11_8` (with `np_envelope`) |
| p. 374 | Functional equation `F(g) = 0` with `I(k, z, ε)` | `np_growthI`, `np_growthF`, `np_growthF_iff_euler`; CRRA inverse marginal utility: `np_crra_inverse` |
| p. 374 | Gauss–Hermite approximation `∫ I e^{−ε²/2}/√(2π) dε ≈ π^{−1/2} ∑ I(√2εⱼ)wⱼ` | exact change of variables: `np_gaussHermite_change`; the quadrature error itself belongs to §11.4 (other part) |
| pp. 374–375 | Truncation `[k_m, k_M] × [z_m, z_M]`, `z_{m,M} = exp(∓4σ/√(1 − ρ²))` | `np_ar1_stationary_variance`, `np_z_bounds`; "must contain the steady state": a choice, no formal content |
| p. 375 | Chebyshev weight `w(k, z)`, tensor basis `φ_ij` | `np_normalize_mem_Icc`; orthogonality of the tensor basis on `[−1, 1]²`: `np_cheb_tensor_orthogonal` |
| p. 375 | Residual `R(k, z; c)` with Gauss–Hermite | `np_growth_residual_eq_F` (equals `F(ĝ)` when the rule is exact) |
| pp. 375–376 | Orthogonal collocation performs well; checking stability; finite elements | not formalised (computational / remarks) |

### §11.6 Numerical dynamic programming

| Source | Claim | Lean |
| --- | --- | --- |
| p. 376 | Discrete vs smooth approximation, references | no formal content |
| (11.9), p. 377 | Bellman equation of the growth model | used as hypothesis in `eq_11_8`; existence of its solution is Chapter 7 material, not repeated |
| p. 377 | Truncation: "the truncated problem can approximate the original problem arbitrarily closely" | vague as stated (correction 5); supporting perturbation bound `np_fixedPt_perturbation` |
| p. 377 | Grid `K`, Tauchen discretisation | `GrowthGrid`; the Tauchen construction: not formalised here (algorithmic; discretisation of AR(1) belongs to another part) |
| (11.10), p. 378 | Discretised Bellman equation | `GrowthGrid.toMDP`, `GrowthGrid.reward`, `GrowthGrid.trans`, `GrowthGrid.trans_rowsum`, `GrowthGrid.trans_nonneg`, `GrowthGrid.isFeasible`, `GrowthGrid.eq_11_10`, `GrowthGrid.eq_11_10_unique`; instance `np_growthGridExample`, `np_growthGridExample_vstar` |
| (11.11), p. 378 | Bellman operator `B` | `GrowthGrid.B_apply`, `GrowthGrid.eq_11_11` |
| p. 378 | Contraction mapping theorem: unique fixed point | `GrowthGrid.np_bellman_contraction`, `GrowthGrid.eq_11_10_unique` |
| p. 378 | `Vₙ = BⁿV₀ → V` at a geometric rate | `GrowthGrid.np_vfi_tendsto`, `GrowthGrid.np_vfi_geometric`; a-posteriori stopping bound `np_vfi_aposteriori` |
| p. 378 | `V₀ = 0` is backward induction on the finite-horizon problem | `GrowthGrid.np_vfi_backward_induction`, `MDP.np_horizonValue`, `MDP.np_horizonValue_const`, `MDP.np_iterate_T_zero_eq_max` |
| (11.12), p. 379 | Policy evaluation linear system | `GrowthGrid.eq_11_12`, `GrowthGrid.eq_11_12_unique`, `GrowthGrid.eq_11_12_inv` |
| p. 379 | Policy improvement step | `GrowthGrid.np_pfi_improvement`, `MDP.np_hpi`, `MDP.np_hpi_feasible`, `MDP.np_hpi_mono` |
| p. 379 | Stop when `gₙ = gₙ₋₁` (or `Vₙ = Vₙ₋₁`); the result satisfies (11.10) and is optimal | `GrowthGrid.np_pfi_stop_policy`, `GrowthGrid.np_pfi_stop_value`, `GrowthGrid.np_vstar_ge` |
| p. 379 | Termination of policy iteration (implicit in "until the first iteration") | `MDP.np_hpi_terminates`, `GrowthGrid.np_pfi_terminates` |
| p. 379 | "Much faster"; quadratic convergence | not formalised (performance claim, cited) |
| p. 379 | Puterman–Brumelle: policy iteration is Newton–Kantorovich for `(I − B)V` | `GrowthGrid.np_pfi_newton` (the Newton-step identity) |
| p. 379 | Modified policy iteration: `B̂`, fixed point `V₀ = B̂V₀`, iterate | `GrowthGrid.np_mpi` |
| pp. 379–380 | Multigrid method | not formalised (algorithmic) |
| p. 380, Steps 1–4 | Value function interpolation | `FittedGrid`, `FittedGrid.cont`, `FittedGrid.obj`, `FittedGrid.fittedBellman`, `FittedGrid.cont_mono`, `FittedGrid.cont_add_const`, `FittedGrid.cont_le_norm`, `FittedGrid.bddAbove_obj`, `FittedGrid.np_fitted_contraction`, `FittedGrid.np_fitted_converges` (convergence, correction 6); linear interpolation qualifies: `np_linWeights`, `np_linWeights_averager`; instance `np_fittedGridExample`, `np_fittedGridExample_contraction` |
| pp. 380–381 | Fewer grid points, faster; slow convergence remains | not formalised (performance) |
| p. 381 | Projection on the value function, residual `R = V̂ − BV̂` | `np_residual_bound`, `np_residual_zero_iff`, `GrowthGrid.np_value_projection` |
| p. 381 | PEA (Marcet, den Haan–Marcet, Christiano–Fisher), occasionally binding constraints | no formal content |
| (11.13), p. 382 | Irreversibility constraint; first-order (Kuhn–Tucker) conditions | `np_irreversible_kkt` |
| (11.14), p. 382 | `m(k', z'; g, h)`, `m ≥ 0`, "`m` is the derivative of the value function" | `eq_11_14_envelope`, `eq_11_14_pos` |
| p. 382 | The conditions with the TVC are sufficient for optimality | not formalised (cited without proof; stochastic sufficiency theorem outside this section) |
| pp. 382–383 | PEA rewriting: `g = max{(1 − δ)k, f − (u')⁻¹(e)}`, `h = u'(f − g) − e`, `F(e) = 0` | `np_pea_kkt`, `np_pea_kkt_unique` |
| p. 383 | `e` is smoother; PEA faster and more accurate | not formalised (informal/performance) |

### Exercise 11.3 (p. 384)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 11.3 | Utility `U(C, N) = (C^θ(1 − N)^{1−θ})^{1−γ}/(1 − γ)`, resource constraint | `np_ex3U`, `np_ex3F`, `np_ex3X`, `np_ex3X_pos` |
| Ex 11.3 | Marginal utilities and products | `ex_11_3_UC`, `ex_11_3_FK`, `ex_11_3_FN`, `ex_11_3_total_N` |
| Ex 11.3 | Bellman equation ⇒ intratemporal condition, capital FOC, envelope, Euler equation | `ex_11_3_euler` (with `np_envelope`) |
| Ex 11.3 | Deterministic steady state | `ex_11_3_steady_state` |
| Ex 11.3 (a)–(e) | Solve by VFI, PFI, interpolation, Euler and value projection in Matlab | not formalised (computational); the methods' theorems are in §11.5–§11.6 above |
