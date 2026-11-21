# Source map

Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), Chapter 2, "Stochastic
Difference Equations". Page numbers are those of the author's draft of 21 April 2013, pp. 45–83.
Lean names are relative to `Miao.RationalExpectations`. Where the Lean statement departs from the
book, see [corrections](corrections.md).

## Carried over from Chapter 1

| Source | Claim | Lean |
| --- | --- | --- |
| Chapter 1 | Definitions, stable matrices, the real block split, deterministic Blanchard–Kahn, the QZ form, deterministic Klein | `DeterministicBasics`, `Triangular`, `Spectral`, `RealSplitting`, `Dichotomy`, `LinearSystems`, `BlockSplit`, `Nonsingular`, `QZ`, `Singular` (see the [Chapter 1 source map](../../DifferenceEquations/docs/source-map.md)) |

## The probability setting (pp. 45, 52)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 45 | `E_t`, the conditional expectation given `F_t`: linear, `L¹`-contractive, iterated expectations | `CondExpSystem`, `CondExpSystem.tower_le_apply`, `CondExpSystem.tower_ge_apply`, `CondExpSystem.idem`, `CondExpSystem.norm_apply_le` |
| p. 45 | The conditional expectations of `L¹(Ω, F, Pr)` given a filtration form such a system, over `ℝ` and `ℂ` | `condExpSystemL1`, `condExpSystemL1_real`, `condExpSystemL1_complex`, `condExpL1_norm_apply_le`, `condExpL1_tower_le`, `condExpL1_tower_ge`, `condExpSystemL1_ae_eq` |
| p. 45 | Adapted processes | `IsAdaptedV`, `condExpL1_eq_self_iff`, `condExpL1_eq_self_iff_exists`, `condExpL1_isAdaptedV_iff` |
| Definition 2.3.1, p. 52 | Stable process: `max_j E|X_{t,j}| < M` | `IsStableProc`, `l1_norm_eq_integral_abs`, `l1_isStableProc_iff`, `bkS_isStableProc_iff` |

## §2.1 First-order linear systems (pp. 45–48)

| Source | Claim | Lean |
| --- | --- | --- |
| (2.1)–(2.2), pp. 45–46 | `z_{t+1} = Φz_t + Σε_{t+1}`, `E_tε_{t+1} = 0`, `E_tε_{t+1}ε′_{t+1} = I` | `var_Model`, `var_ShockMDS`, `var_Model.z_memLp`, `var_Model.z_meas` |
| Examples 2.1.1–2.1.3, p. 46 | AR(1) with a mean, ARMA(1,1), VAR(2) in the form (2.1) | `example_2_1_1`, `example_2_1_2`, `example_2_1_3` |
| Definition 2.1.1, p. 47 | Covariance stationarity (corrected for vectors) | `var_IsCovStationary`, `definition_2_1_1_not_symmetric` |
| p. 47 | Means: `μ_{t+1} = Φμ_t`, `μ_t → 0` | `var_mean_rec`, `var_mean_eq`, `var_mean_tendsto_zero` |
| p. 47 | The discrete Lyapunov equation: its unique solution and successive iteration | `var_lyapMap`, `var_lyapSol`, `lyap_fixed`, `lyap_unique`, `lyap_iterate_tendsto`, `var_mom_rec`, `var_mom_tendsto` |
| p. 47 | `C_z(j) = ΦʲC_z(0)`; stationary moments | `var_autocov`, `var_stationary_moments`, `var_stationary_of_initial` |
| p. 47 | "`{z_t}` has a unique stationary distribution" (corrected) | `stationary_law_not_unique` |
| pp. 47–48 | Moving-average form and the impulse response `ΦʲΣ` | `var_ma_shift`, `var_ma`, `var_ma_initial_tendsto`, `var_impulse_response` |

## §2.2 Scalar linear rational expectations models (pp. 48–52)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 48 | The lag-operator rule `LʲE_tX_{t+i} = E_tX_{t+i−j}`, `L⁻ʲX_t = E_tX_{t+j}` | `sre_lagInv`, `sre_lag`, `sre_lagE`, `sre_lagE_self`, `sre_lagInv_zero`, `sre_lagInv_lagInv`, `sre_lag_lag`, `sre_lag_form` |
| (2.3), p. 49 | The fundamental solution, the unique stable solution | `eq_2_3`, `eq_2_3_unique`, `sre_fwd`, `sre_fwd_rec`, `sre_fwd_adapted`, `sre_fwd_bound` |
| (2.4), p. 49 | Bubbles; every solution is fundamental plus bubble | `eq_2_4_of_particular`, `eq_2_4`, `eq_2_4_every` |
| (2.5), p. 49 | Transversality rules out bubbles | `sre_Transversality`, `eq_2_5_of_bounded`, `eq_2_5_rules_out_bubbles`, `eq_2_5_bubble_fails` |
| Example 2.2.1, pp. 49–50 | Blanchard–Watson: the fundamental price `d_t/(R − ρ)` and the bursting bubble | `example_2_2_1_Ed`, `example_2_2_1_fundamental`, `example_2_2_1_general`, `example_2_2_1_bubble`, `example_2_2_1_coin`, `example_2_2_1_bubble_L1` |
| (2.6)–(2.9), p. 50 | The second-order equation: solution and uniqueness | `sre_second`, `eq_2_9`, `eq_2_6_solution`, `eq_2_6_unique` |
| (2.10), p. 51 | The equation with `E_{t−1}x_t`: reduction and solution (corrected) | `eq_2_10_reduce`, `sre_sol210`, `eq_2_10_solution`, `eq_2_10_unique`, `eq_2_10_indeterminate` |
| §2.2.2, pp. 51–52 | Undetermined coefficients: the matching conditions, the stable root, agreement with the lag-operator solution | `uc_iff`, `uc_sufficient`, `uc_necessary`, `uc_denominator_ne_zero`, `uc_stable_root`, `uc_eq_lag_solution` |

## §2.3 Multivariate linear rational expectations models (pp. 52–64)

| Source | Claim | Lean |
| --- | --- | --- |
| (2.11), p. 52 | `AE_tx_{t+1} = Bx_t + Cz_t`; with `A` nonsingular | `IsRESolution`, `eq_2_11_iff`, `bkS_regular_of_det` |
| p. 52 | Stability under `E_t`, shifts, matrices; summability of forward sums | `bkS_stable_Evec`, `bkS_stable_shift`, `bkS_stable_matAct`, `bkS_stable_add`, `bkS_summable_geom`, `bkS_geom_decay` |

### §2.3.1 Blanchard and Kahn (pp. 53–55)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 53 | Predetermined in the sense of Blanchard and Kahn | `IsPredeterminedBK` |
| (2.12), p. 54 | Forward solution for `u_t` | `bkS_fwd`, `eq_2_12`, `bkS_fwd_adapted`, `bkS_fwd_rec`, `bkS_fwd_bound`, `bkS_fwd_unique`, `bkS_u_eq_fwd`, `bkS_policy` |
| p. 53 | Theorem 1.4.2 "still applies": a unique stable solution | `theorem_1_4_2_stoch`, `bkS_exists`, `bkS_unique`, `bkS_k0_adapted` |
| p. 53 | Corollary 1.4.1 | `corollary_1_4_1_stoch`, `bkS_shift` |
| p. 54 | The certainty equivalence principle | `bkS_trivial`, `certainty_equivalence`, `certainty_equivalence_fwd`, `theorem_1_4_2_of_stoch`, `bkS_Evec_ar`, `certainty_equivalence_ar`, `certainty_equivalence_ar_det` |
| p. 54 | Theorem 1.4.3 "also applies" (corrected) | `theorem_1_4_3_gt_stoch`, `theorem_1_4_3_lt_stoch`, `theorem_1_4_3_lt_exists_stoch` |
| — | A jump-only system has a unique stable solution | `bkS_jump_unique` |
| Example 2.3.1, pp. 54–55 | The New Keynesian model with an exogenous rate rule: (2.16), `W`, one unstable eigenvalue, indeterminacy | `eq_2_16`, `eq_2_16_W`, `nk_lam`, `example_2_3_1_eigen`, `nk_saddle_split`, `nk_saddle_eig`, `nk_saddle_unstable`, `example_2_3_1_split`, `example_2_3_1_indeterminate`, `example_2_3_1_indeterminate_det` |

### §2.3.2 Klein (pp. 55–58)

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 2.3.2, p. 55 | Martingale, martingale difference | `IsMartingaleProc`, `IsMartingaleDiffProc`, `IsMartingaleProc.diff` |
| Definition 2.3.3, p. 56 | White noise; white noise is stable; (2.2) gives a white noise; a white noise need not satisfy (2.2) | `var_IsWhiteNoise`, `var_integral_abs_le_sqrt`, `whiteNoise_stable`, `whiteNoise_stable_L1`, `mds_whiteNoise`, `whiteNoise_example`, `whiteNoise_not_mds`, `vex_wn_adapted` |
| p. 56 | A martingale difference need not be stable; uniformly bounded ones are | `example_mdiff_not_stable`, `klM_truncSystem`, `isStableProc_of_uniformly_bounded` |
| Definition 2.3.4, p. 56 | Predetermined with prediction error; `ξ = 0` is Blanchard–Kahn | `IsPredeterminedKlein`, `isPredeterminedKlein_zero_iff`, `predError_isMartingaleDiff` |
| (2.17), p. 56 | Forward solution for `u_t` (corrected) | `eq_2_17`, `eq_2_17_solution`, `eq_2_17_printed_false` |
| pp. 56–57 | `E_ts_{t+1}`, `ξ_{t+1}`, `s_{t+1}`, `k_{t+1}` | `eq_klein_Es`, `eq_klein_xi`, `eq_klein_s`, `eq_klein_k`, `klS_isRESolution_iff`, `klS_blocks_iff`, `klS_core_blocks`, `klS_core` |
| p. 57 | The stochastic Klein theorem; real data | `klein_stochastic`, `klein_stochastic_real` |
| p. 57 | The simplified form `y_t = A_ykk_t + A_yzz_t`, `k_{t+1} = A_kkk_t + A_kzz_t + ξ_{t+1}` | `klein_simplified_form`, `klS_sylvester_exists`, `klS_Ez_of_2_1` |
| pp. 57–58 | The LQ problem: the predetermined state and the first-order conditions as (2.11) | `lq_predError`, `lq_predetermined`, `lqPeriod`, `lq_variation_u`, `lq_variation_x`, `lqLeft`, `lqRight`, `lq_system_iff` |
| p. 58 | "First-order conditions and transversality are necessary and sufficient" | Not formalised (linear-quadratic control is Chapter 9) |

### §2.3.3 Sims (pp. 58–64)

| Source | Claim | Lean |
| --- | --- | --- |
| (2.19)–(2.20), p. 58 | The Sims form; `C = 0` by a change of variables; appending `z` | `IsSims19Solution`, `isSims19_zero_iff`, `eq_2_19_const`, `eq_2_19_const_singular`, `eq_2_19_append` |
| pp. 58–59 | The setting and the ordered QZ form; (2.21) | `IsSimsSolution`, `IsSimsShock`, `IsSimsQZ`, `isSimsQZ_of_regular`, `eq_2_21` |
| (2.22)–(2.23), pp. 59–60 | Forward solution (corrected), `u_t = 0`, `Z₂ᴴy₀ = 0` | `eq_2_22`, `eq_2_22_expect`, `eq_2_22_printed_false`, `sims_u_eq_zero`, `sims_Z2_y0`, `eq_2_23` |
| Lemma 2.3.1, p. 60 | Solvability of (2.23) | `lemma_2_3_1`, `lemma_2_3_1_sims`, `lemma_2_3_1_random` |
| Assumptions 2.3.1–2.3.2, pp. 60–61 | Existence and uniqueness conditions | `SimsAssumption1`, `SimsAssumption2`, `simsAssumption2_iff_ker`, `assumption_2_3_1_nu_gt_m` |
| (2.24), p. 61 | The reduced system and `Θ₁`, `Θ₂` (corrected) | `eq_2_24`, `simsKmat_mul_Pm`, `simsGmat`, `simsHmat`, `simsKmat`, `simsTheta1`, `simsTheta2`, `theta_1_printed_false` |
| Theorem 2.3.1, p. 61 | Assumptions 2.3.1–2.3.2 are necessary and sufficient (corrected) | `theorem_2_3_1_theta`, `theorem_2_3_1_existence`, `theorem_2_3_1_uniqueness`, `theorem_2_3_1_sufficiency`, `theorem_2_3_1_necessity_1`, `theorem_2_3_1_necessity_2`, `theorem_2_3_1`, `SimsRich`, `simsRich_trunc`, `theorem_2_3_1_necessity_false` |
| (2.25), p. 62 | The SVD of `Q₂.Π` and the column-space test (corrected) | `IsThinSVD`, `colspace_iff`, `colspace_iff_thin`, `colspace_printed_false`; existence of the SVD, with `r = rank`: `exists_thinSVD`, `svdE_mul_eigen`, `svdE_cols`, `colspace_iff_svd` |
| p. 62 | `Λ` and `Ξ` when `m = r` | `lambda_formula`, `lambda_formula_svd`, `xi_formula`, `svd_injective_iff` |
| Corollary 2.3.1, p. 62 | Uniqueness iff `m = r` (corrected) | `SimsYUnique`, `SimsPairUnique`, `simsY_unique_iff`, `corollary_2_3_1`, `corollary_2_3_1_rank`, `corollary_2_3_1_printed_false` |
| p. 62 | Lubik–Schorfheide: `m > r` gives infinitely many solutions | `lubik_schorfheide`, `lubik_schorfheide_rank` |
| (2.26), pp. 63–64 | Sunspots and `Θ₃` | `eq_2_26`, `eq_2_26_svd`, `xi_residual`, `eq_sunspot_identity`, `sunspot_term_simplified`, `simsTheta3`, `sunspot_solution`, `sunspot_existence` |
| Example 2.3.2, p. 64 | The New Keynesian model in the Sims form | `IsNKSolution`, `ex232Γ₀`, `ex232Γ₁`, `ex232Ψ`, `ex232Pm`, `example_2_3_2_rows`, `example_2_3_2` |

## §2.4 Nonlinear rational expectations models (pp. 64–69)

The scalar case (`n_x = n_y = 1`), as in the book, with a finite mean-zero shock.

| Source | Claim | Lean |
| --- | --- | --- |
| (2.27)–(2.28), pp. 64–65 | The linearized system around the deterministic steady state, in the form (2.11) | `eq_2_28_differential`, `eq_2_28` |
| (2.29)–(2.30), pp. 66–67 | The policy functions, the perturbation `σ`, the function `F`; `F ≡ 0` makes every partial derivative vanish | `IsFiniteShock`, `IsPertSolution`, `pertP`, `pertDx`, `pertDs`, `pertPsi`, `pertPhi`, `pertF`, `pertF_contDiff`, `pertF_Dx`, `pertF_Ds`, `pert_partials_vanish`, `pert_F_partials_zero` |
| p. 67 | `ȳ = g(x̄, 0)`, `x̄ = h(x̄, 0)` (an assumption, corrected) | `eq_steady_state`, `steady_state_printed_false` |
| p. 67 | `F_σ(x̄, 0)` and `g_σ = h_σ = 0` | `eq_F_sigma_E`, `eq_F_sigma`, `g_sigma_system`, `pert_hom2_unique`, `theorem_g_sigma_zero`, `g_sigma_not_forced` |
| (2.31)–(2.33), p. 68 | `F_x(x̄, 0) = 0` and the linear system for `g_x`, `h_x` | `eq_F_x`, `eq_F_x_zero`, `eq_2_31`, `eq_2_32`, `eq_2_33`, `eq_2_31_of_2_33` |
| p. 68 | `F_xx(x̄, 0) = 0`, linear in `g_xx`, `h_xx` (corrected) | `eq_F_xx`, `eq_F_xx_linear`, `g_xx_unique`, `pertFxxPrinted`, `eq_F_xx_printed`, `eq_F_xx_printed_false` |
| p. 69 | `F_σσ(x̄, 0) = 0`, linear in `g_σσ`, `h_σσ` (corrected) | `eq_F_sigma_sigma`, `eq_F_sigma_sigma_linear`, `g_sigma_sigma_unique`, `pertFssPrinted`, `eq_F_sigma_sigma_printed`, `eq_F_sigma_sigma_printed_false` |
| p. 69 | `F_σx(x̄, 0) = 0` and `g_σx = h_σx = 0` | `eq_F_sigma_x`, `g_sigma_x_system`, `theorem_g_sigma_x_zero`, `g_sigma_x_not_forced` |
| p. 69 | Uncertainty enters the second-order solution only through `½g_σσσ²`, `½h_σσσ²` | `pertTaylor2`, `pertTaylor2_sigma`, `summary_uncertainty` |
| p. 66 | The vector case; that the Taylor polynomial approximates `g`, `h` | Not formalised (the scalar case is the book's; only the algebraic claim is proved) |

## §2.5 Numerical solutions using Dynare (pp. 69–82)

Software instructions; not formalised.

## §2.6 Exercises (pp. 82–83)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 1 | The stochastic Cagan model: a unique stable solution `p_t = m_t/(1 + α(1 − ρ))` | `ex1_IsSol`, `ex_1_iff`, `ex_1_b_gt_one`, `ex_1_unique`, `ex_1_solution`, `ex_1_solution_eq_fwd`, `ex_1`, `ex_1_solution_iff`, `ex_1_rho_one_martingale`, `ex_1_rho_one_growth`, `ex_1_rho_one` |
| Ex 1, `ρ = 1` | `m` unbounded in `L¹` | Not formalised (random-walk moment estimates) |
| Ex 2(a) | The Taylor principle `δ > 1` (corrected) | `nkTaylorEqm`, `nkDeterminate`, `nk_taylor_iff`, `ex_2_2_a`, `ex_2_2_a_taylor_principle`, `ex_2_2_a_printed_false` |
| Ex 2(b) | The Taylor rule: determinacy conditions | `nk_eig2`, `nkBothOut`, `nk_out_of_bothOut`, `nk_root_of_not_bothOut`, `nk_eigvec2`, `nk_jump2_unique`, `nk_jump2_nonunique`, `ex_2_2_suff`, `ex_2_2_nec`, `ex_2_2_b_exact`, `ex_2_2_b` |
| Ex 3 | Dynare | Not formalised (software) |
