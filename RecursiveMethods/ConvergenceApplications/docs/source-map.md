# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 13, pp. 389–413. Chapter 13 has no numbered lemmas or theorems; its content is
Exercises 13.1–13.8. Lean names are relative to `StokeyLucasPrescott.ConvergenceApplications`.
Where the Lean statement departs from the book, see [corrections](corrections.md).

## §13.1 A discrete-space (s, S) inventory problem

| Source | Claim | Lean |
| --- | --- | --- |
| (1)–(2), p. 390 | The functional equations | `discGamma`, `discB2`, `DiscEq1`, `DiscEq2`, `orderCost` |
| Exercise 13.1a, p. 390 | Solutions of (1); a finite optimal `S`, characterised | `ex_13_1a_eq1`, `ex_13_1a_eq2_iff`, `orderCost_fixedPoint_iff`, `exists_isMinOn_orderCost`, `orderCost_isMaxOn_iff_isMinOn`, `stopping_isMaxOn`, `exists_stopping_index`, `ex_13_1a`, `ex_13_1a_c1_zero`, `ex_13_1a_manual_counterexample` |
| Exercise 13.1b, p. 390 | Transition matrix; ergodic and transient sets; no cyclic subsets | `restock`, `discKernel`, `isMarkov_discKernel`, `ex_13_1b_closed`, `ex_13_1b_communicate`, `ex_13_1b_minimal`, `ex_13_1b_transient`, `ex_13_1b_not_cyclic`, `ex_13_1b_theta_one` |
| Exercise 13.1c, p. 390 | Unique invariant distribution, convergence, its form | `discKernelE`, `ex_13_1c_conditionM`, `discPi`, `discPi_invariant`, `ex_13_1c_weights`, `ex_13_1c`, `ex_13_1c_nat`, `ex_13_1c_nat_convergence`, `ex_13_1c_nat_not_uniform`, `ex_13_1c_not_conditionM_nat`, `ex_13_1c_note_counterexample`, `manualPi`, `ex_13_1c_manual_mass`, `ex_13_1c_manual_not_invariant` |

## §13.2 A continuous-state (s, S) process

| Source | Claim | Lean |
| --- | --- | --- |
| (1), p. 391 | The law of motion and its kernel | `invLaw`, `invKernel`, `invKernel_apply` |
| Exercise 13.2a, p. 391 | Interval formulas; a transition function; Feller? | `ex_13_2a_markov`, `ex_13_2a_Icc_of_lt`, `ex_13_2a_Icc_of_le`, `ex_13_2a_zero_of_lt`, `ex_13_2a_zero_of_le`, `measure_eq_of_intervals`, `ex_13_2a_determined`, `ex_13_2a_not_feller` |
| Exercise 13.2b, p. 391 | `Pᴺ(x, {0}) ≥ ε` on `[0, S]` | `ex_13_2b_counterexample`, `ex_13_2b_counterexample_conditionM`, `ex_13_2b_not_convergent`, `ex_13_2b`, `ex_13_2b_of_density`, `ex_13_2b_conditionMFor`, `ex_13_2b_conditionM`, `ex_13_2b_invariant` |
| p. 391 | Why `s < z̄`; `(S, ∞)` transient | `ex_13_2_zero_unreachable`, `ex_13_2_zero_unreachable_kpow`, `ex_13_2b_fails_of_zbar_le_s`, `ex_13_2_not_transient`, `ex_13_2_invariant_null_above` |

## §13.3 The one-sector model of optimal growth

| Source | Claim | Lean |
| --- | --- | --- |
| p. 392 | `x̄ = z̄f(x̄)`: unique, but need not exist | `xbar_unique`, `noXbarF`, `noXbarF_T2`, `modifiedT2_of_concave`, `xbar_counterexample` |
| (1), p. 392 | The functional equation in output | `OutputHyp`, `outNext`, `outObj`, `outT`, `outT_contraction`, `SolvesOut`, `outT_eq_iff` |
| Exercise 13.3a, p. 392 | Unique `v`, strictly increasing and strictly concave | `ex_13_3a_exists`, `outT_strictMono`, `out_concave`, `out_flat_step`, `out_strictConcave`, `ex_13_3a` |
| Exercise 13.3b, p. 392 | The policy function | `out_uniqueArgmax`, `outPolicy`, `ex_13_3b`, `out_consumption_strictMono`, `ex_13_3b_counterexample`, `ex_13_3b_not_strictMono` |
| Exercise 13.3c, p. 392 | `v′(x) = U′(x − g(x))` | `ex_13_3c`, `ex_13_3c_continuous` |
| Exercise 13.3d, p. 393 | `P` monotone | `GrowthLaw`, `growthP`, `growthP_apply`, `isMarkovKernel_growthP`, `ex_13_3d`, `growthP_isFeller`, `growth_exists_invariant` |
| (3a)–(3b), p. 394 | Lower bounds along shock runs | `growthPhi`, `growth_kpow_Ioc`, `ShockZ3`, `growth_3a`, `growth_3b` |
| pp. 393–394 | `x*`, the case `x = 0` | `zstar`, `GrowthEuler`, `growth_xstar_exists`, `growth_xi`, `growth_euler_xi`, `growth_xstar_between`, `growth_case_zero` |
| Exercise 13.3e, p. 394 | The case `x = x̄` | `growth_theta`, `growth_euler_theta`, `ex_13_3e` |
| pp. 393–394 | Unique `λ*`, global weak convergence | `growth_invariant_unique`, `outPolicyR`, `growth_optimal_invariant_unique` |
| pp. 394–395 | `f(0) = 0` | `growth_f_zero`, `growth_f_zero_not_unique`, `growth_invariant_interval` |

## §13.4 Industry investment under uncertainty

| Source | Claim | Lean |
| --- | --- | --- |
| (2), p. 395 | Mixing; `Q` stable | `IndustryMixing`, `industryMixing_Ici`, `industryMixing_Iic`, `industry_shock_stable` |
| p. 396 | `x̲`, `x̄`, `X̂` | `IndustryPolicy`, `IndustryPolicy.fixedPoint_unique`, `IndustryPolicy.xlo_le_xhi`, `exists_fixedPoint`, `industry_exists_xlo_xhi`, `industry_no_fixedPoint_half`, `industry_no_fixedPoint_above`, `industry_Xhat_invariant`; the §10.4 policy: `indPolicyFn`, `indPolicyFn_props`, `indPolicyFn_industryPolicy`, `indPolicyFn_ind0` |
| Exercise 13.4a, p. 396 | `P̂` monotone and Feller | `indKernel`, `indKernel_apply`, `ex_13_4_transition`, `ex_13_4a_monotone`, `ex_13_4a_feller` |
| Exercise 13.4b, p. 396 | Assumption 12.1 on `Ŝ` | `industry_Q_high_pos`, `industry_Q_low_pos`, `indKernel_highRun`, `indKernel_lowRun`, `ex_13_4b_rect`, `ex_13_4b`, `ex_13_4b_stable` |
| Exercise 13.4c, p. 397 | `T*ⁿλ ⇒ λ*` on all of `S` | `ex_13_4c_path_bounds`, `ex_13_4c_gap`, `ex_13_4c_squeeze_path`, `ex_13_4c_remark_counterexample`, `ex_13_4c_rect_all`, `ex_13_4c_degenerate_no_assumption`, `indSKernel`, `ex_13_4c`, `ex_13_4c_unique` |

## §13.5 Equilibrium in a pure currency economy

| Source | Claim | Lean |
| --- | --- | --- |
| (1), p. 398 | The household problem | `ex_13_5a` |
| Exercise 13.5a, p. 398 | Unique bounded continuous `v` | `ex_13_5a` |
| Exercise 13.5b, p. 398 | `v(·, z)` strictly increasing, strictly concave, `C¹` | `cash_strictMono`, `cash_concave`, `cash_flat_step`, `cash_strictConcave`, `cash_envelope_pos`, `cash_envelope_corner`, `cash_jump_le`, `cashW_hasDerivAt`, `ex_13_5b_deriv`, `ex_13_5b_C1` |
| Exercise 13.5c, p. 399 | `g` continuous | `cash_uniqueArgmax`, `ex_13_5c` |
| Exercise 13.5d, p. 399 | `g(·, z) = y` on `[0, φ(z)]`, strictly increasing beyond | `cash_spend_all`, `cash_spend_all_necessary`, `ex_13_5d_counterexample`, `ex_13_5d_counterexample_uniform`, `ex_13_5d_corrected` |
| Exercise 13.5e, p. 400 | `c(·, z)` strictly increasing | `cashPolicy_mono`, `cashCons_mono`, `ex_13_5e_counterexample`, `ex_13_5e_corrected` |
| Exercise 13.5f, p. 400 | `m̄` with `g(m̄, z̲) = m̄` | `ex_13_5f`, `ex_13_5f_mbar_eq_y` |
| Exercise 13.5g, p. 400 | `φ(z̄) ≥ y` | `cashW_deriv_le`, `ex_13_5g` |
| Exercise 13.5h, p. 400 | `g(m, ·)` nonincreasing | `CurrencyIncreasingDiff`, `ex_13_5h` |
| Exercise 13.5i, p. 400 | Theorem 12.12 applies | `CurrencyDensity`, `currencyIidKernel`, `CurrencyPolicy`, `currencyPolicy_of_book`, `ex_13_5i`, `cash_down`, `ex_13_5ij_economy` |
| Exercise 13.5j, (2), p. 400 | `∫ m dλ* = ∫∫ g dμ dλ*`; the price level | `ex_13_5j`, `ex_13_5j_price_unique` |
| p. 399 | The example `U = z(1 − e^{−c})` | `currencyCex_hyp`, `currencyCex_diffHyp`, `currencyCex_increasingDiff`, `currencyUniform` |

## §13.6 A pure currency economy with linear utility

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 13.6a, p. 401 | `v = max{ζ, z}m + A` and its policy | `maxInt`, `exists_unique_cutoff`, `currencyValue`, `currencyPolicy`, `SatisfiesCurrencyBellman`, `currency_bellman`, `ex_13_6a`, `ex_13_6a_unique` |
| Exercise 13.6b, p. 402 | The ergodic set `{iy}` | `cutoffKernel`, `currencyKernel`, `currencyLattice`, `IsKernelErgodicSet`, `ex_13_6b`, `ex_13_6b_density`, `ex_13_6b_counterexample` |
| Exercise 13.6c, p. 402 | `πᵢ = δ(1 − δ)^{i−1}` | `currencyInvariant`, `currencyInvariant_invariant`, `currencyInvariant_mean`, `cutoffKernel_conditionM`, `ex_13_6c` |

## §13.7 A pure credit economy with linear utility

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 13.7a, p. 403 | Solve (2); policy (3) | `ex_13_7a_cutoff`, `ex_13_7a_counterexample`, `creditValue`, `creditPolicy`, `SatisfiesCreditBellman`, `ex_13_7a` |
| Exercise 13.7b, p. 403 | `T*ⁿΨ₀` and invariant measures | `creditKernel`, `ex_13_7b`, `ex_13_7b_counterexample`, `ex_13_7b_corrected`, `ex_13_7b_feller` |
| Exercise 13.7c, p. 403 | Equilibrium with a constant price | `MarketClears`, `marketClears_iterate_iff`, `CreditEqm`, `ex_13_7c`, `ex_13_7c_betaR`, `ex_13_7c_betaR_counterexample`, `ex_13_7c_exists`, `ex_13_7c_unique`, `ex_13_7c_scaling`, `ex_13_7c_counterexample` |

## §13.8 An equilibrium search economy

| Source | Claim | Lean |
| --- | --- | --- |
| (F1)–(F2), p. 405 | Primitives | `SearchPrimitives`, `ex_13_8_F1F2_inconsistent` |
| Exercise 13.8a, p. 408 | Unique bounded continuous `v`, bounds, monotonicity | `searchRHS`, `ex_13_8a_contraction`, `searchV`, `ex_13_8a` |
| Exercises 13.8b–c, p. 409 | The law of motion `g`, monotone, 1-Lipschitz, continuous | `searchCutoff`, `searchGC`, `searchGA`, `searchG`, `ex_13_8b`, `ex_13_8b_unique`, `ex_13_8c` |
| Exercise 13.8d, p. 410 | Unique invariant measure under (6) | `searchKernel`, `searchP`, `ex_13_8d_process`, `searchW`, `SearchAssumption6`, `searchNoCaseB`, `searchThetaBar`, `ex_13_8d_seven_iff`, `ex_13_8d_seven`, `ex_13_8d_noCaseC`, `ex_13_8d_hint_counterexample`, `ex_13_8d_hint_counterexample_concrete`, `ex_13_8d_hint_corrected`, `ex_13_8d`, `ex_13_8d_large`, `ex_13_8d_delta` |
| Exercise 13.8e, p. 411 | Exogenous leavers | `searchGLeave`, `searchLeave_unique`, `ex_13_8e` |
| Exercise 13.8f, p. 411 | `D(0) = x̄`, `D = 0` for large `θ` | `searchD`, `ex_13_8f_zero`, `ex_13_8f_zero_measure`, `ex_13_8f_large` |
| Exercise 13.8g, p. 411 | `D` continuous (Theorem 12.13) | `ex_13_8g_jointCont`, `ex_13_8g`, `ex_13_8g_existence` |
| Exercise 13.8h, p. 412 | `D` nonincreasing; strictly? | `searchG_theta_anti`, `ex_13_8h`, `ex_13_8h_antitoneOn`, `ex_13_8h_counterexample`, `ex_13_8h_counterexample_concrete`, `ex_13_8h_zero`, `searchCutoffs_theta_strict` |

## Supporting modules

| Module | Source |
| --- | --- |
| `RealIntervals` | Theorem 12.12 transported to real intervals and rectangles in `ℝ × ℝ` (`transportK`, `theorem_12_12_of_orderIso`, `theorem_12_12_real`, `theorem_12_12_prod`) |
| `TransitionFunctions` … `Parameters` | Chapters 8 and 12, copied from `WeakConvergence` |
| `ConvergenceConcepts` … `ConditionM` | Chapter 11, copied from `StrongConvergence` |
| `Contraction` … `GrowthPolicy` | Chapters 3, 4, 9 and 10, copied from `StochasticApplications` |
