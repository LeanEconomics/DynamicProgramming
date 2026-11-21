# Source map

Jianjun Miao, *Economic Dynamics in Discrete Time* (MIT Press, 2014), Chapter 1, "Deterministic
Difference Equations". Page numbers are those of the author's draft of 21 April 2013, pp. 5–43.
Lean names are relative to `Miao.DifferenceEquations`. Where the Lean statement departs from the
book, see [corrections](corrections.md).

## Definitions used throughout (§1.4, pp. 15–18)

| Source | Claim | Lean |
| --- | --- | --- |
| (1.20), p. 15 | The system `Ax_{t+1} = Bx_t + Cz_t` | `IsSolution` |
| Assumption 1.4.1, p. 15 | Regularity: `det(Aα − B) ≠ 0` for some `α` | `IsRegular` |
| Assumption 1.4.2, p. 16 | `z_t = z̄` for `t ≥ T` | `EventuallyConst` |
| Definition 1.4.1, p. 16 | Steady state of a sequence | `IsSteadyStateOf` |
| Definition 1.4.2, p. 17 | Stable sequence (bounded in the max norm) | `IsStableSeq`, `isStableSeq_iff_bddAbove` |
| Definitions 1.4.3–1.4.4, p. 17 | Asymptotic and global stability, the basin | `IsAsympStable`, `basin`, `IsGloballyStable`, `isAsympStable_iff_basin`, `isGloballyStable_iff_basin` |
| Definition 1.4.5, p. 18 | Stable eigenvalue and stable matrix | `IsStableMatrix` |

## §1.1 Scalar first-order linear equations (pp. 5–10)

| Source | Claim | Lean |
| --- | --- | --- |
| (1.1) | `x_{t+1} = bx_t + cz_t` | `IsScalarSol` |
| (1.2), p. 6 | Steady state `x̄ = c/(1 − b)`; none for `b = 1`, `c ≠ 0` | `eq_1_2_steady_state`, `eq_1_2_no_steady_state_of_b_one` |
| (1.3), p. 6 | General solution `(x₀ − x̄)bᵗ + x̄` | `eq_1_3` |
| p. 6 | `|b| < 1`: globally asymptotically stable | `eq_1_3_globallyStable`, `eq_1_3_tendsto` |
| p. 6 | `|b| > 1`: explodes unless `x₀ = x̄`; the only stable solution is `x̄` | `eq_1_3_diverges`, `eq_1_3_bdd_iff` |
| (1.4), p. 6 | Backward-looking solution | `eq_1_4` |
| (1.5), p. 7 | Limit for `|b| < 1` and bounded `z` (corrected) | `eq_1_5_counterexample`, `eq_1_5_tendsto`, `eq_1_5_bdd`, `eq_1_5_sub_tendsto` |
| p. 7 | `|b| = 1` (corrected for `b = −1`) | `eq_1_5_b_one_formula`, `eq_1_5_b_one_tendsto_iff`, `eq_1_5_b_one_limit_sub`, `eq_1_5_b_neg_one_counterexample`, `eq_1_5_b_neg_one_unique` |
| (1.6), p. 7 | Forward substitution for every `T` | `eq_1_6` |
| (1.7), p. 7 | Transversality condition | `eq_1_7_of_bdd`, `eq_1_8_transversality` |
| (1.8), p. 7 | Forward-looking solution for `|b| > 1`: a bounded solution satisfying (1.7), the unique one | `fwdSol`, `eq_1_8_summable`, `eq_1_8_isScalarSol`, `eq_1_8_bdd`, `eq_1_8_unique_of_transversality`, `eq_1_8_unique_bdd`, `eq_1_8`, `eq_1_8_others_diverge` |
| p. 8 | For `|b| < 1` the sum (1.8) need not converge | `eq_1_8_not_summable` |
| (1.9), p. 8 | Fundamental solution plus bubble; every solution has this form; stable bubbles for `|b| < 1` | `eq_1_9`, `eq_1_9_every_solution`, `eq_1_9_bubble_stable` |
| Example 1.1.1, pp. 8–9 | Adaptive expectations: the recursion, the backward solution, convergence; rational expectations: the forward solution and the unique bounded price | `example_1_1_1_recursion`, `example_1_1_1_backward`, `example_1_1_1_tendsto_iff`, `example_1_1_1_abs_a_lt_one_iff`, `example_1_1_1_forward`, `example_1_1_1_forward_limit`, `example_1_1_1_isScalarSol`, `example_1_1_1_bubbles`, `example_1_1_1_unique_bdd` |
| Example 1.1.2, pp. 9–10 | Dividend taxes: `p_T`, `p₀`, the drop at time 0, the decline until `T` | `divTax`, `taxPath`, `sum_div_pow_eq`, `example_1_1_2_p0_forward`, `example_1_1_2_pT`, `example_1_1_2_p0`, `example_1_1_2_solves`, `example_1_1_2_unique`, `example_1_1_2_drop`, `example_1_1_2_decreasing`, `example_1_1_2_const` |
| Figure 1.1 | Numerical illustration | Not formalised (a plot) |

## §1.2 Lag operators (pp. 10–12)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 11 | The lag operator `L`, `Lⁿ`, `Lⁿc = c` | `lagOp`, `lagOp_lagOp`, `lagOp_zero`, `lagOp_iterate`, `lagOp_neg_lagOp`, `lagOp_const` |
| p. 11 | `1/(1 − λLⁿ) = Σ λʲL^{nj}` for `|λ| < 1`, on bounded sequences | `BddZSeq`, `oneSubLag`, `geomLagSum`, `lag_inverse_geom`, `lag_scalar_geom` |
| p. 11 | `1/(1 − λLⁿ)² = Σ (j + 1)λʲL^{nj}` | `geomLagSum2`, `lag_inverse_geom_sq`, `lag_scalar_geom_sq` |
| p. 11–12 | `(I − ALⁿ)⁻¹ = Σ AʲL^{nj}` when all eigenvalues of `A` are inside the unit circle, for every integer `n` | `lagSeries`, `lagSeries_summable`, `lagSeries_rec`, `lagSeries_unique`, `lag_matrix_formula` |

## §1.3 Scalar second-order linear equations (pp. 12–15)

| Source | Claim | Lean |
| --- | --- | --- |
| (1.13)–(1.15), p. 12 | The equation, characteristic roots, factorization, superposition | `IsSecondOrderSol`, `IsHomSol`, `char_roots_iff`, `char_roots_exist`, `eq_1_15`, `superposition`, `sub_isHomSol`, `hom_factor`, `sol_factor` |
| Case 1, (1.17), p. 13 | General solution; sink; source; indeterminacy | `eq_1_17`, `eq_1_17_general`, `case1_sink`, `case1_sink_bdd`, `case1_sink_indeterminate`, `case1_source`, `case1_source_not_tendsto` |
| (1.18), pp. 13–14 | The saddle-path solution, the unique bounded solution for each `x₀` | `saddlePath`, `case1_saddle_eq`, `case1_saddle_isSol`, `case1_saddle_bdd`, `case1_saddle_unique`, `case1_saddle` |
| Case 2, p. 14 | Repeated root: `(c₁ + tc₂)λᵗ`, the book's verification, stability | `case2_solution`, `case2_verification`, `case2_general`, `case2_general_counterexample`, `case2_stable_iff` |
| Case 3, pp. 14–15 | Complex roots: the real form `rᵗ(A cos θt + B sin θt)`, damped and explosive oscillations | `case3_roots`, `case3_complex_form`, `case3_conj_real`, `case3_real_form`, `case3_solution`, `case3_general`, `case3_damped_form`, `case3_damped`, `case3_explosive` |
| p. 12 | The formal particular solution `cz_t/((L⁻¹ − λ₁)(L⁻¹ − λ₂))` | Notation only; its content is `case1_saddle` |
| p. 15 | "`θ/2π` is the frequency" | Not formalised (descriptive) |
| (1.19), p. 15 | The second-order equation as a first-order system | `eq_1_19`, `eq_1_19_of_system` |

## §1.4 First-order linear systems (pp. 15–17)

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 1.4.5, p. 18 | A real matrix is stable iff its characteristic roots are inside the unit circle iff `Aᵗv → 0` for all `v`; then the decay is geometric | `isStableMatrix_iff_roots`, `isStableMatrix_iff_tendsto`, `HasGeomDecay`, `hasGeomDecay_of_isStableMatrix`, `isStableMatrix_inv` |
| Footnote 2, p. 17 | `A` nonsingular implies regularity | `footnote_2`, `isRegular_of_isUnit_det` |
| p. 16 | The scalar example `a = b = 0` violates Assumption 1.4.1 and has no solution | `example_scalar_not_regular`, `example_scalar_no_solution` |
| p. 16 | A non-regular pair has no solution for generic `z` (corrected) | `remark_nonregular_no_solution`, `remark_nonregular_counterexample` |
| (1.21), p. 16 | The steady state `x̄ = (A − B)⁻¹Cz̄` | `eq_1_21`, `eq_1_21_solution`, `eq_1_21_steadyState`, `isSteadyStateOf_of_not_mem_range` |
| — | Stable and unstable subspaces, the real splitting and its dimension, the exponential dichotomy (copied from `RecursiveMethods/DeterministicDynamics`) | `stableSubspace`, `unstableSubspace`, `cplx`, `cplxEnd`, `stableR`, `unstableR`, `finrank_stableR`, `projS`, `projU`, `stable_bound` |

## §1.4.1 Nonsingular systems (pp. 17–23)

| Source | Claim | Lean |
| --- | --- | --- |
| (1.22), p. 17 | The system `x_{t+1} = Wx_t + A⁻¹Cz_t`; a unique solution for each `x₀` | `eq_1_22`, `exists_sol_rec`, `exists_unique_solution` |
| (1.24)–(1.25), p. 18 | The transformed system and the backward solution | `eq_1_24`, `eq_1_25` |
| Theorem 1.4.1, p. 18 | Convergence to `x̄` from every `x₀` iff all eigenvalues of `W` are stable (both directions) | `theorem_1_4_1`, `xbar_eq`, `isUnit_sub_det` |
| p. 19 | The block form `J = diag(J_s, J_u)` (a real block split in place of the Jordan form), its existence | `IsRealBlockSplit`, `exists_real_block_split`, `split_rec_inl`, `split_rec_inr` |
| (1.29), p. 21 | Forward solution for `u_t` | `forwardU`, `forwardU_rec`, `forwardU_bounded`, `forwardU_unique`, `eq_1_29` |
| (1.30)–(1.33), pp. 21–22 | `s_t`, `u_t`, `y_t` and the recursion for `k_t` | `eq_1_30`, `eq_1_31`, `eq_1_32`, `eq_1_33` |
| p. 22 | `R_ks` nonsingular with `R_ks⁻¹ = P_sk − P_sy P_uy⁻¹ P_uk`; the order and rank conditions | `rks_inv`, `puy_inv_of_rks`, `bk_order_iff` |
| Theorem 1.4.2, p. 20 | Blanchard–Kahn: a unique stable solution for every `k₀` and every stable `z` | `theorem_1_4_2`, `bk_exists`, `bk_unique` |
| Corollary 1.4.1, p. 22 | The stable solution converges to `x̄` | `corollary_1_4_1`, `IsRealBlockSplit.isUnit_one_sub` |
| (1.34), pp. 22–23 | The stable manifold, of dimension `n_k` (corrected for forcing) | `eq_1_34`, `stable_initial_iff`, `stableArm`, `stableArm_iff`, `finrank_stableArm`, `stable_initial_translate` |
| p. 23 | Eigenvalues on the unit circle | `remark_unit_root` |
| Theorem 1.4.3, p. 23 | `n_u > n_y`: no solution; `n_u < n_y`: infinitely many (corrected) | `theorem_1_4_3_gt`, `theorem_1_4_3_lt`, `theorem_1_4_3_lt_exists`, `theorem_1_4_3_printed_gt_false`, `theorem_1_4_3_printed_lt`, `theorem_1_4_3_lt_counterexample` |

## §1.4.2 Singular systems (pp. 24–27)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 24 | The Cagan model: `A` singular, the pair regular, its generalized eigenvalues | `caganA`, `caganB`, `caganC`, `example_cagan_iff`, `example_cagan_det`, `example_cagan_regular`, `example_cagan_genEigenvalues`, `example_cagan_genEigenvalues_zero` |
| Definition 1.4.6, p. 24 | Generalized eigenvalue and eigenvector; `λ(A, B)` | `IsGenEigenvector`, `IsGenEigenvalue`, `genEigenvalues`, `isGenEigenvalue_iff_det` |
| Theorem 1.4.4, pp. 24–25 | Complex generalized Schur (QZ) form, items 1–5 (item 5 for any scale-invariant ordering predicate; stable pairs first) | `theorem_1_4_4`, `theorem_1_4_4_stable`, `ScaleInvariant`, `diag_ne_zero_of_regular`, `genEigenvalues_eq_diag`; construction: `exists_eigenPair`, `exists_unitary_col`, `deflate`, `det_of_col_zero`, `blockOne`, `assemble_upper`, `exists_qz_ordered` |
| p. 25 | `s_ii = 0` is an infinite, unstable eigenvalue | the stability predicate `‖t_ii‖ < ‖s_ii‖` in `theorem_1_4_4_stable` |
| Theorem 1.4.5, p. 25 | Klein: a unique stable solution for every `k₀` and every stable `z` | `theorem_1_4_5`, `klein_core`, `isSolution_iff_transformed` |
| (1.36), p. 26 | The triangular block system | `eq_1_36` |
| p. 26 | `S₁₁`, `T₂₂` invertible | `det_S11_ne_zero`, `det_T22_ne_zero` |
| (1.37), p. 26 | Forward solution for `u_t` (corrected) | `eq_1_37`, `fwdSum`, `fwdSum_rec`, `eq_fwdSum`, `eq_1_37_printed_false`, `summable_Mu` |
| (1.38), p. 26 | Backward solution for `s_t`; `s₀ = Z₁₁⁻¹(k₀ − Z₁₂u₀)` | `eq_1_38`, `eq_s0`, `summable_Ms`, `isStableSeq_of_rec` |
| (1.39)–(1.40), p. 26 | Recovering `k_t` and `y_t` | `eq_1_39_40` |
| — | With real data the stable solution is real | `theorem_1_4_5_real` |
| p. 27 | The corollary "similar to Corollary 1.4.1" | `corollary_1_4_1_singular`, `det_sub_ne_zero`, `klein_homog` |
| p. 27 | Augmenting the system with `z_{t+1} = Φz_t`; then `u_t = 0` | `remark_augmented`, `remark_u_eq_zero` |
| — | Powers of triangular matrices with diagonal inside the unit circle (copied from `RecursiveMethods/DeterministicDynamics`, plus summability) | `triangular_tendsto_iff`, `summable_norm_pow_of_triangular`, `tendsto_norm_mclm_pow`, `mclm` |

## §1.5 Phase diagrams (pp. 27–28)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 27 | The system in levels and in differences | `IsPhaseSol`, `phaseIter`, `phase_tilde`, `phase_delta` |
| p. 28 | The isoclines `Δx_t = 0`, `Δy_t = 0` and the directions of motion | `phase_isocline_x`, `phase_isocline_y` |
| p. 28 | The steady state | `phase_steady_state`, `phase_dev` |
| p. 28 | "A convergent saddle path ... all other paths diverge" (corrected) | `phase_cp_one`, `phase_cp_neg_one`, `phase_roots`, `phase_lamLo_iff`, `phase_saddle`, `phase_saddle_slope`, `phase_saddle_iff`, `phase_counterexample` |
| — | The 2×2 saddle toolkit used in §1.5, §1.6 and §1.8 | `IsSol22`, `cp22`, `disc22`, `lamLo`, `lamHi`, `sVar`, `kSaddle`, `roots22_lt`, `lamLo_gt_neg_one_iff`, `abs_lamLo_lt_one_iff`, `saddle22`, `saddle22_tendsto`, `saddle22_unique`, `saddle22_unbounded`, `saddle22_iff`, `saddle22_only_zero` |
| Figures 1.2–1.4 | Isoclines and phase diagram | Not formalised (plots); their content is the rows above |

## §1.6 Nonlinear systems (pp. 28–32)

| Source | Claim | Lean |
| --- | --- | --- |
| (1.41)–(1.42), p. 29 | Steady state and first-order approximation | Stated for Example 1.6.1 as partial derivatives (`example_1_6_1_linearization`) |
| Example 1.6.1, pp. 30–31 | Optimal growth: steady state, the linearized system and its reduced form, trace and determinant, `0 < λ₁ < 1 < λ₂` | `example_1_6_1_steady`, `example_1_6_1_linearization`, `example_1_6_1_matrix`, `example_1_6_1_reduced`, `example_1_6_1_trace_det`, `example_1_6_1_roots`, `example_1_6_1_saddle` |
| Definition 1.6.1, p. 31 | Periodic point of period `p`, `p`-cycle | `definition_1_6_1`, `definition_1_6_1_cycle` |
| p. 32 | The logistic map `4x − 4x²`: `f²`, fixed points of `f` and `f²`, the two-cycle, its decimals | `logistic`, `logistic_two`, `logistic_fixed_iff`, `logistic_two_fixed_iff`, `logistic_two_cycle`, `logistic_two_cycle_decimals` |
| Figure 1.5 | `f` and `f²` | Not formalised (a plot) |

## §1.7 Numerical solutions using Dynare (pp. 32–41)

Software instructions; not formalised. The steady-state and Euler conditions of the example are
those of Example 1.6.1 with labour, and the Blanchard–Kahn count it checks is Theorem 1.4.2.

## §1.8 Exercises (pp. 41–43)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 1(a) | Cagan: a unique stable solution and its formula (`ρ < 1`; `ρ = 1` corrected) | `IsCagan`, `cagan_isScalarSol`, `cagan_b_gt_one`, `ex_1_1a`, `ex_1_1a_forward`, `ex_1_1a_rho_one_bdd_iff`, `ex_1_1a_rho_one` |
| Ex 1(b) | An announced money increase: the price path | `cagan_money`, `cagan_path`, `ex_1_1b_solves`, `cagan_path_const`, `ex_1_1b_unique`, `ex_1_1b_shape` |
| Ex 2 | The Dornbusch model reduced to a 2×2 system | `IsDornbusch`, `IsDorn2`, `ex_1_2_reduce`, `pbarD`, `ebarD`, `dM11`, `dLo`, `dHi`, `dK`, `dornIter`, `dornIter_sol` |
| Ex 2(a) | Steady state | `ex_1_2a` |
| Ex 2(b) | A unique stable solution, and when | `ex_1_2_dev_step`, `ex_1_2_dev`, `dorn_cp_one`, `dorn_cp_neg_one`, `dorn_h1`, `dorn_hm`, `dorn_tendsto`, `ex_1_2b_iff`, `ex_1_2b_unique`, `ex_1_2b_counterexample` |
| Ex 2(c) | Phase diagram (isoclines) | `ex_1_2c` |
| Ex 2(d) | Unexpected permanent increase: jump and overshooting | `pbarD_sub`, `ebarD_sub`, `dK_neg`, `ex_1_2d_path`, `ex_1_2d_unique`, `ex_1_2d_overshoot`, `ex_1_2d_monotone` |
| Ex 2(e) | Announced increase | `dorn_announce_core`, `dornJump`, `ex_1_2e_jump`, `ex_1_2e_exists`, `ex_1_2e_jump_shape` |
| Ex 3–4 | Dynare experiments | Not formalised (software) |
