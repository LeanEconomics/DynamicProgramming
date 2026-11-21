# Source map: AKMM Chapter 10

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 10, Computational tools, pp. 261–283 (no appendix). Page references are
the draft's running heads. Lean names are relative to `AKMM.ComputationalTools`. Departures from
the book are in [corrections](corrections.md).

Reused from dependencies. Miao `NumericalMethods` (`Miao.NumericalMethods`):
`nq_ar1_variance_fixed` (the AR(1) variance), `ni_natural_spline_existsUnique` with `ni_CubicInterp`,
`ni_CubicSmooth`, `ni_cub2`, `ni_piece` (cubic splines), `ni_poly_interp_unique` (polynomial
interpolation); cited, not restated: `nq_tauchen_stochastic` (Gaussian Tauchen),
`FittedGrid.np_fitted_converges` (fitted VFI). Miao `RationalExpectations`
(`Miao.RationalExpectations`): `CondExpSystem`, `sre_IsAdapted`, `sre_IsBounded`, `sre_iter`,
`eq_2_3_unique`, `sre_fwd_ar1`. Miao `DifferenceEquations` (`Miao.DifferenceEquations`):
`IsRealBlockSplit`, `IsStableSeq`, `IsSolution`, `theorem_1_4_2`. Sargent–Stachurski `JobSearch`
(`SargentStachurski.JobSearch`): `IsContractionOn`, `IsContractionOn.banach_pi`. Not used: Miao
`NeoclassicalGrowth` (its log-linearised RBC model is Miao's parametrisation, without AKMM's
`θ`; the AKMM system is derived here), SLP `DeterministicDP` and `StochasticDP` (the general
Bellman theory on continuous state spaces; the chapter's VFI is on a grid, and the continuous
cake-eating problem is solved in closed form here).

## Chapter introduction (p. 261)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 261 | Lucas (1980) quotation; computational tools as the backbone of macroeconomics | narrative |
| p. 261 | Building blocks combined in §10.5; §10.6 self-contained | narrative |
| p. 261, fn. 1 | Numerical Recipes, QuantEcon, Judd (1998), Miranda–Fackler (2002) | citations |

## §10.1 Approximating a function (pp. 261–263) — `Interpolation`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 261 | A polynomial `ax² + bx + c` is stored by three numbers; value functions need approximation | narrative |
| p. 262 | Grid points `x₁ = x̲`, `x_n = x̄`, equally spaced or denser where needed | narrative (grids appear in `tauchenGrid`, `rwGrid`, `cakeGrid`) |
| p. 262, steps 1–2 | Linear interpolation formula | `linInterp`, `linInterp_left`, `linInterp_right` |
| p. 262 | The line connecting `(xᵢ, f(xᵢ))` and `(x_{i+1}, f(x_{i+1}))` | `linInterp_unique` |
| p. 262 | Uses only local information | `linInterp` (depends only on the two neighbouring values) |
| p. 262 | (i) Error can be large if `f` is highly nonlinear | `linInterp_error`, `linInterp_error_h` (error `≤ M h²/8` with `|f″| ≤ M`) |
| p. 262 | (ii) Not differentiable at the grid points | `kink`, `linInterp_kink_not_differentiable` (when the slopes differ), `linInterp_kink_differentiable_of_eq` (correction 7) |
| pp. 262–263 | Cubic splines: `C²`, determined by `f(xᵢ)` plus boundary conditions; global dependence | `cubic_spline_existsUnique` (natural end conditions, Miao `ni_natural_spline_existsUnique`); global dependence: narrative |
| Figure 10.1 | Linear interpolation | not formalised: figure |
| (10.1), p. 263 | `f̂(x) = ∑ aᵢφᵢ(x)`; `m = n`: generically unique `aᵢ` | `eq_10_1_unique_iff`, `eq_10_1_poly` |
| p. 263 | `m ≥ n`: regression; Chebyshev polynomials efficient; global information | not formalised: method description (Chebyshev interpolation is Miao `NumericalMethods` Theorem 11.3.1, not restated) |
| p. 263, fn. 2 | Codes in Numerical Recipes | citation |

## §10.2 Root finding and §10.2.1 Bisection (pp. 263–265) — `Bisection`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 264 | Brute-force grid search "always works" for large `n`, but is slow | not formalised: informal claim about speed |
| p. 264, step 1 | Bracketing: `sign f(a) ≠ sign f(b)` and `f` continuous give a root in `[a, b]` | `bisect_bracket_root` |
| p. 264, step 2 | The bisection step; `sign(f c) = sign(f a)` test | `bisectStep`, `bisect`, `bisectStep_cases`, `bisect_sign_eq_iff` |
| p. 264 | The solution stays in the bracket | `bisect_bracket`, `bisect_mem`, `bisect_mono` |
| p. 264 | "does not require differentiability"; "always finds one of the solutions provided that the function is continuous" | `bisect_converges` (continuity only) |
| p. 264–265 | Each iteration cuts the interval in half; ends after finitely many steps | `bisect_length`, `bisect_terminates` |
| p. 265 | How many iterations are needed for a tolerance | `bisect_iteration_count` |
| p. 265 | Ends even when no solution exists (discontinuous `f`); check `f(a) ≈ 0` | `bisectJump`, `bisect_discontinuous_no_root`; `bisect_converges` (`f(a_k) → 0`) |
| p. 265 | `10⁻³` on `[0, 1]`: 1000 grid evaluations against 10 bisection steps, `(1/2)¹⁰ = 1/1024` | `bisect_ten_steps` (the grid-search count is not formalised: counting evaluations) |
| Figure 10.2 | Bisection illustrated | not formalised: figure |

## §10.2.2 Newton–Raphson (pp. 265–266) and §10.3.2–10.3.3 Newton's method (pp. 267–269) — `Newton`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 265 | Linear approximation `f(x) ≈ f(x₀) + f′(x₀)(x − x₀)` | `eq_10_2` (its root) |
| (10.2), p. 265 | `x̂ = x₀ − f(x₀)/f′(x₀)` | `newtonStep`, `eq_10_2` |
| p. 265 | If `f` is linear, `x̂` is the solution in one step | `newton_affine_exact` |
| pp. 265–266, steps 1–3 | Iterate `x_{i+1} = x_i − f(x_i)/f′(x_i)` until `|f(x_i)| < ε` | `newtonStep` (the stopping rule is algorithmic) |
| p. 266 | "much faster than bisection" when `x₀` is close to the solution | `newton_local_quadratic`, `newton_converges` (local quadratic convergence for `C²` `f`, `f′(x*) ≠ 0`; the comparison of speeds is not formalised) |
| p. 266 | May fail to find a solution if `f` is not well behaved | not formalised: informal |
| p. 266 | Central difference `f′(x) ≈ (f(x+h) − f(x−h))/(2h)`; smaller `h` better in principle | `central_difference_tendsto`, `central_difference_quadratic` |
| p. 266 | Machine epsilon `≈ 10⁻¹⁶`, `h ≈ 10⁻⁵` | not formalised: floating-point advice |
| p. 267 | Quadratic approximation of `F` | `eq_10_3` |
| (10.3), p. 268 | `x̂ = x₀ − F′(x₀)/F″(x₀)` from the first-order condition of the quadratic model | `newtonOptStep`, `eq_10_3`, `eq_10_3_max` |
| p. 268 | If `F` is quadratic, `x̂` is the solution in one step | `newtonOpt_quadratic_exact` |
| p. 268, steps 1–3 | Iterate until `|x_{i+1} − x_i| < ε` | `newtonOptStep` (stopping rule algorithmic) |
| p. 268 | Faster than golden section near quadratic `F`; not guaranteed to find the maximum | not formalised: informal |
| p. 269, §10.3.3 | Newton for `max F` is Newton–Raphson on `F′ = 0` | `newtonOpt_eq_newtonStep_deriv` |
| Figures 10.3, 10.5 | Constructing `x₁` | not formalised: figures |

## §10.3.1 Golden-section search (pp. 266–267) and §10.3.3 (p. 269) — `GoldenSection`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 266 | Multi-dimensional optimisation one dimension at a time | not formalised: algorithmic remark |
| p. 266, step 1 | Bracket `a < b < c`, `F(a) < F(b)`, `F(c) < F(b)`: a local maximum lies between `a` and `c` | `GoldenBracket`, `GoldenBracket.IsBracket`, `golden_bracket_max` |
| p. 266 | Otherwise a corner solution is likely | not formalised: heuristic |
| p. 267, step 2 | The step with `(b − x)/(b − a) = ω*`, `ω* = (3 − √5)/2 ≈ 0.38197` | `omegaStar`, `goldenStep`, `golden_omega_sq`, `golden_omega_eq_sq`, `golden_omega_bounds`, `golden_omega_pos`, `golden_omega_lt_half` |
| p. 267 | `(1 − ω*)/ω* ≈ 1.61803` is the golden ratio | `golden_ratio_eq` |
| p. 267 | From `(c − b)/(c − a) = ω*`, each step removes the fraction `ω*` | `GoldenBracket.IsGolden`, `goldenStep_spec` |
| p. 267 | Remaining bracket after `n` steps has length `(1 − ω*)ⁿ(c − b)` | corrected to `(1 − ω*)ⁿ(c − a)`: `golden_length`, `golden_printed_length_counterexample` (correction 2) |
| p. 267 | No differentiability needed; ends in a pre-set number of iterations | `golden_terminates`, `golden_iterate_max` (continuity only) |
| p. 267, fn. 3 | The result is guaranteed only with this `ω*` | `golden_two_lengths`, `golden_fn3_unique` |
| p. 269, §10.3.3 | Removes "about one-third" of the interval per step, as against half for bisection | `golden_removed_fraction` (correction 3) |
| p. 269 | Golden section needs no differentiability and always maximises; Newton when smooth | not formalised: practical advice |
| Figure 10.4 | Golden section illustrated | not formalised: figure |

## Example 1 (pp. 269–270) — `LabourLeisure`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 269 | `max u(c, ℓ)` s.t. `c = f(ℓ) + x`, `u = ln c − (ω/γ)ℓ^γ`, `f(ℓ) = ℓ^α` | `ex1Obj` |
| (10.4), p. 270 | Maximise `ln(ℓ^α + x) − (ω/γ)ℓ^γ` | `ex1Obj`, `ex1_root_isMax` |
| (10.5), p. 270 | or solve `αℓ^{α−1}/(ℓ^α + x) − ωℓ^{γ−1} = 0` | `ex1Foc`, `eq_10_5`, `ex1_foc_strictAnti` |
| p. 270 | `α = 1/3`, `x = 0.5`, `ω = 1`, `γ = 2`: optimal `ℓ ∈ [0, 1]` by bisection, Newton, golden section | `ex1_unique_root` (a unique root, in `(1/8, 1)`, the maximiser), `ex1_cbrt_eighth`; the MATLAB codes are not formalised |

## §10.4 Discretising an AR(1) process and §10.4.1 Tauchen (pp. 270–271) — `Discretization`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 270 | Representing an AR(1) by a Markov chain with similar persistence and volatility | narrative |
| p. 270 | `z_{t+1} = ρz_t + ε_{t+1}`, `σ_z² = σ_ε²/(1 − ρ²)` | `ar1_uncond_var` (via Miao `nq_ar1_variance_fixed`) |
| p. 270, step 1 | Equally spaced grid, spacing `ω`, `z̄¹ = −mσ_z`, `z̄ᴺ = mσ_z`; `m = 3` covers three standard deviations | `tauchenGrid`, `tauchenGrid_last` (the "three standard deviations" remark is narrative) |
| p. 271, step 2 | The transition probabilities `π_{ij}` | corrected interior entries: `tauchenUpper`, `tauchenLower`, `tauchen_lower_succ`, `tauchenProb`; printed: `tauchenPrinted`, `tauchen_printed_neg`, `tauchen_printed_row_sum`, `tauchenCauchyCdf`, `tauchenCauchyCdf_strictMono` (correction 5) |
| p. 271 | `π_{ij}` is the probability the AR(1) assigns to `[z̄ʲ − ω/2, z̄ʲ + ω/2]`; the end points take the tails | `tauchen_stochastic` (rows are probability vectors, any distribution function `F`); Gaussian cells as measurable sets: Miao `nq_tauchen_stochastic` |

## §10.4.2 The Rouwenhorst method (p. 271) — `Rouwenhorst`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 271 | Tauchen can be inaccurate for `ρ` near 1; Rouwenhorst has better approximation properties | not formalised: empirical claim |
| p. 271 | Equally spaced grid from `z̄₁ = −mσ_z` to `z̄_N = mσ_z` | `rwGrid`, `rwGrid_ends` |
| p. 271, step 1 | `Π₂ = [p, 1 − p; 1 − p, p]` | `rouwenhorst_two` |
| p. 271, step 2 | The recursion for `Π_N` (printed weights `p, 1 − p, p, 1 − p`) | corrected weights `p, 1 − p, 1 − p, p`: `rouwenhorst`, `rouwenhorst_row_zero`, `rouwenhorst_eq_coeff` (row generating polynomials `rwLow`, `rwHigh`, `rwRow`, `rw_coeff_linear_mul`); printed: `rouwenhorstPrinted`, `rouwenhorst_printed_counterexample` (correction 4) |
| p. 271 | Divide interior rows by two "so that the elements in each row are equal to one" (sum to one) | `rouwenhorst_nonneg`, `rouwenhorst_row_sum` (`rwRow_natDegree_le`, `rw_sum_coeff_pow`) |
| p. 271 | `p = (1 + ρ)/2`, `m = √(N − 1)`: the unconditional mean and variance equal those of the AR(1) | `rouwenhorst_matches_ar1` (also the autocorrelation `ρ`); `rouwenhorst_cond_mean_index`, `rouwenhorst_cond_mean`, `rouwenhorst_invariant`, `rw_binomial_rows`, `rw_binomial_moments`, `rouwenhorst_stationary_mean`, `rouwenhorst_stationary_var`, `rouwenhorst_stationary_autocov`, `rw_sum_coeff_mul_index` |
| p. 271 | The method uses only the mean and variance | not formalised: informal |
| p. 271 | The invariant distribution converges to a normal as `N → ∞` | not formalised: cited (de Moivre–Laplace); the invariant law is proved binomial (`rouwenhorst_invariant`) |
| p. 271, fn. 4 | Kopecky and Suen (2010) | citation |
| Example 2, p. 272 | Tauchen and Rouwenhorst for `y′ = 0.95y + ε`, `σ = 0.2`, 10 states | not formalised: MATLAB computation |

## §10.5 Value-function iteration (pp. 272–276) — `ValueIteration`, `CakeEating`

| Source | Claim | Lean |
| --- | --- | --- |
| (10.6), p. 272 | `V(k) = max_{k′} {F(k, k′) + βV(k′)}` | on a grid: `GridDP`, `GridDP.T`, `GridDP.vfi`; cake eating: `cake_bellman` |
| (10.7), p. 272 | The mapping `T` | `GridDP.T`, `GridDP.cont` |
| p. 272 | VFI relies on the contraction mapping theorem; `V_i → V` from any `V₀` | `GridDP.contraction` (Sargent–Stachurski `IsContractionOn`), `GridDP.cont_sub_le`, `GridDP.sup'_sub_le`, `GridDP.vfi`; continuous cake: `cake_bellman_step`, `cake_bellman_unique` |
| p. 272, steps 1–4 | The algorithm (grid, `V₀`, maximise, repeat) | `GridDP.T` (grid search); interpolation off the grid: Miao `NumericalMethods` `FittedGrid.np_fitted_converges` (not restated) |
| p. 272 | "can be slow, especially when `β` is close to one" | `GridDP.vfi` (rate `βⁱ`); the speed remark is informal |
| §10.5.1, p. 273 | Cake eating `∑βᵗ√c_t`, `a_{t+1} = a_t − c_t`, Bellman equation | `cakeV`, `cakeRhs`, `cake_bellman` (closed form `√(a/(1 − β²))`, policy `β²a`), `cake_cauchy_schwarz`, `cake_policy_unique`, `cake_path_value` |
| p. 273, steps 1–3 | Grid on `[0, a₀]`, `V₀ = 0`, choices on the grid (`a_n ≤ a_j`) | `cakeGrid` |
| p. 273 | "the properties of a contraction mapping ensure the value function is concave" | `cake_concave` (from the closed form) |
| p. 273, step 4 | Stop when `max_j |V_{i+1}(a_j) − V_i(a_j)| < ε` | `GridDP.stopping_rule` (error `≤ βε/(1 − β)`) |
| p. 273 | Off-grid choice by interpolation, root finding or optimisation; grid search when concavity is not obvious | not formalised: algorithmic advice |
| Example 3, p. 274 | `β = 0.98`, `a₀ = 10`, simulate 100 periods | `cakeGrid_vfi` (convergence of VFI on the grid); the simulation and plots are not formalised |
| §10.5.2, pp. 273–274 | Stochastic cake, `a_{t+1} = a_t − c_t + z_t`, two-state Markov `z` | `stochCakeGrid` (a `GridDP`, so `GridDP.vfi` applies) |
| (10.8)–(10.11), pp. 274–275 | Stochastic growth with labour; recursive planner problem | `GridDP` covers the discretised problem; see `Linearization` for the first-order conditions |
| (10.12), p. 275 | The static labour choice `H(z, K, K′)` | `labour_foc_unique` (in `Linearization`) |
| Example 4, pp. 275–276 | Two-state growth model, grid search and golden section, HP-filtered statistics | not formalised: MATLAB computation and simulation |
| p. 275, fn. 5 | Welfare theorems: planner = competitive equilibrium | not formalised: cited (Chapter 5) |

## §10.6 Solving a dynamic model with linearisation (pp. 276–278) — `Linearization`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 276–277 | Global versus local methods, perturbation, curse of dimensionality, certainty equivalence, Dynare | narrative (certainty equivalence: `eq_10_17` takes expectations of a linear equation) |
| p. 277 | Predetermined and jump variables; "solving the model" | narrative; formalised in `BlanchardKahn` |
| (10.13), p. 277 | Euler equation | `loglin_euler` (its log-linearisation, deterministic as in fn. 7) |
| (10.14), p. 277 | Labour-supply condition | `loglin_labour`, `eq_10_15` |
| (10.12), p. 275 | Static labour choice `H(z, K, K′)` | `labourFoc`, `labour_foc_unique` (at most one root of the first-order condition) |
| p. 277 | Log-linearised (10.9) | `rbc_output_exp`, `loglin_exp_deriv`, `loglin_resource` |
| p. 277 | Log-linearised (10.13) | `loglin_euler` |
| (10.15), p. 277 | `h_t = θ(z_t + αk_t − c_t)`, `θ = (1 − H̄)/(H̄(1 − α) + α)` | `theta`, `eq_10_15` |
| p. 277, fn. 7 | Ignoring the expectation operator (certainty equivalence) | `loglin_euler` (deterministic expansion); `eq_10_17` |
| (10.16), p. 277 | Eliminating `h_t` from the resource constraint | `eq_10_16` |
| (10.17), p. 278 | The Euler equation with `E_t[z_{t+1}] = ρz_t` | corrected: `eq_10_17`; printed coefficient: `eq_10_17_printed_counterexample` (correction 6) |
| (10.27), pp. 280–281 | `B`, `A`, `E` of the growth model | `rbcB`, `rbcA`, `rbcE` (corrected), `eq_10_27` |

## §10.6.1 The Blanchard–Kahn condition (pp. 278–283) — `BlanchardKahn`

| Source | Claim | Lean |
| --- | --- | --- |
| (10.18)–(10.19), p. 278 | `y_t = φy_{t+1}` is `y_{t+1} = λy_t`, `λ = 1/φ` | `eq_10_19` |
| p. 278 | `y_{t+T} = λᵀy_t` | `bk_scalar_iterate` |
| (10.20), p. 278 | `λ > 1`: unique non-explosive solution `y_t = 0` | `eq_10_20` |
| p. 278 | `λ ≤ 1`: indeterminacy | `bk_scalar_indeterminate` |
| (10.21)–(10.22), p. 279 | `E_t[y_{t+1}] = λy_t + z_t`, `z_{t+1} = ρz_t + ε_{t+1}` | hypotheses `h21`, `h22` over Miao's `CondExpSystem` |
| p. 279 | `E_t[y_{t+2}] = λ²[y_t + (1/λ)(1 + ρ/λ)z_t]`; `E_t[y_{t+T}] = λᵀy_t + (1 − (ρ/λ)ᵀ)/(λ − ρ)·λᵀz_t` | `bk_forecast`, `bk_forecast_book` |
| (10.23), p. 279 | `λ > 1`: `lim E_t[y_{t+T}]` finite iff `y_t = −z_t/(λ − ρ)`, the unique solution | `eq_10_23`; uniqueness among bounded adapted solutions: `eq_10_23_unique` (Miao `eq_2_3_unique`, `sre_fwd_ar1`) |
| p. 279, fn. 8 | `λ ≤ 1`: `λᵀy_t + (λᵀ − ρᵀ)/(λ − ρ)z_t` remains finite; indeterminacy | `bk_fn8`, `bk_indeterminate` |
| (10.24)–(10.25), p. 280 | Guess `y_t = Az_t`; `A = −1/(λ − ρ)`; verify | `eq_10_25`, `eq_10_24_verify` |
| (10.26), p. 280 | `B[x_{t+1}; E_t y_{t+1}] = A[x_t; y_t] + Ea_t` | `eq_10_27` (the growth model, in `Linearization`) |
| p. 280, fns. 9–10 | Not all models fit (10.26); common `ρ` | narrative |
| (10.27), p. 281 | The growth model's `B`, `A`, `E` | `rbcB`, `rbcA`, `rbcE`, `eq_10_27` (correction 6) |
| (10.28), p. 281 | `F = B⁻¹A`, `G = B⁻¹E` | `eq_10_30` (hypothesis `w′ = Fw + Ga`) |
| (10.29), p. 281 | `F = HJH⁻¹`, `J` diagonal, real distinct eigenvalues ordered by modulus | `eq_10_30` (hypothesis `F = HJH⁻¹`) |
| p. 281 | BK: unique non-explosive solution if `h = m` | `bk_condition` (Miao `theorem_1_4_2`, real block split, `H̃₂₂` invertible) |
| p. 281, fn. 11 | QZ when `B` is singular | not formalised here: cited (Miao `DifferenceEquations` Theorem 1.4.4–1.4.5) |
| p. 282 | Intuition: expanding and contracting directions | narrative |
| (10.30)–(10.31), p. 282 | `H⁻¹[x_{t+1}; E_t y_{t+1}] = JH⁻¹[x_t; y_t] + H⁻¹Ga_t`; partition | `eq_10_30` |
| p. 282 | `E_t[ỹ_{t+1}] = J₂ỹ_t + Γ₂a_t` solved by `ỹ_t = ΛΓ₂a_t`, `Λ = diag(−1/(λᵢ − ρ))` | `bk_tilde_solution` (and `eq_10_23` componentwise) |
| p. 283 | `y_t = −H̃₂₂⁻¹H̃₂₁x_t + H̃₂₂⁻¹ΛΓ₂a_t` | `bk_y_solution` |
| p. 283 | `x_{t+1} = (F₁₁ − F₁₂H̃₂₂⁻¹H̃₂₁)x_t + (G₁ + F₁₂H̃₂₂⁻¹ΛΓ₂)a_t` | `bk_x_solution` |
| Example 5, p. 283 | `J(1,1) = 0.9537`, `J(2,2) = 1.0592`; `c = 0.5691k + 0.3920z` etc.; IRFs, HP statistics | not formalised: numerical output (checked numerically in the survey, correction 6) |
