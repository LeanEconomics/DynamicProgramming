# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 15, pp. 441–474. Lean names are relative to
`StokeyLucasPrescott.ParetoOptimaEquilibria`. Where the Lean statement departs from the book, see
[corrections](corrections.md).

## Introduction

| Source | Claim | Lean |
| --- | --- | --- |
| Figures 15.1–15.2, pp. 442–444 | The one-person economy: tangency and separation of `A` and `Y` | Not formalised (heuristic; the general results are Theorems 15.3 and 15.4) |
| p. 444 | Convex upper contour sets need concavity of `U` | `intro_concavity_counterexample` (quasi-concavity suffices) |

## §15.1 Dual spaces

| Source | Claim | Lean |
| --- | --- | --- |
| p. 445 | Linear functionals; continuity (sequential); boundedness | `SeqContAt`, `continuous_iff_seqContAt` |
| (1), p. 445 | The dual norm: infimum of bounds, supremum over the unit sphere | `dual_norm_eq` |
| Theorem 15.1, p. 446 | (a) continuous at one point, continuous everywhere; (b) continuous iff bounded | `theorem_15_1a`, `theorem_15_1b` |
| pp. 446–447 | The dual space `S*` | `StrongDual ℝ S` (Mathlib) |
| Exercise 15.1, p. 447 | `S*` is complete | `ex_15_1` |
| Example 1, p. 447 | `(ℝⁿ)* = ℝⁿ` by `y ↦ (x ↦ y · x)` | `example_15_1` |
| Example 2, (2), pp. 447–448 | `ℓ_p* = ℓ_q`, `1 < p < ∞` | `pairEllP`, `norm_pairEllP_le`, `sum_rpow_le_of_dual_ellP`, `exists_preimage_pairEllP`, `norm_pairEllP`, `dualEllP`, `example_15_2` |
| Exercise 15.2(a), p. 448 | `ℓ₂* = ℓ₂` | `ellTwoSp`, `pairTwo`, `pairTwo_eq_toDual`, `norm_pairTwo`, `pairTwo_surjective`, `dualEllTwo`, `ex_15_2a` |
| Exercise 15.2(b), p. 448 | `ℓ₁* = ℓ∞` | `ellOneSp`, `ellInfSp`, `pairInfOne`, `norm_pairInfOne_le`, `norm_pairInfOne`, `pairInfOne_surjective`, `dualEllOne`, `ex_15_2b` |
| Exercise 15.3, p. 448 | Each `y ∈ ℓ₁` gives a continuous linear functional on `ℓ∞` | `pairOneInf`, `summable_mul_of_one_inf`, `norm_pairOneInf_le`, `ex_15_3`, `ex_15_3_manual_counterexample` |
| p. 448 | `ℓ∞*` contains functionals not of this form | `exists_seq_functional_at_infinity`, `seqRegularPart_eq_zero_of_seqC00`; and §15.3 below |
| Example 3, p. 448 | `c₀` | `cZero`, `mem_cZero` |
| Exercise 15.4, p. 448 | `c₀` is a normed space; `c₀* = ℓ₁` | `isClosed_cZero`, `ex_15_4a`, `signTrunc`, `pairOneCZero`, `norm_pairOneCZero`, `tendsto_trunc_cZero`, `pairOneCZero_surjective`, `dualCZero`, `ex_15_4b` |
| Example 4, (3), pp. 448–449 | `L_p(Z, 𝒵, μ)`, equivalence classes, the essential supremum norm | `MeasureTheory.Lp` (Mathlib) |
| pp. 449–450 | `L_p* = L_q`, `1 < p < ∞` | `dualSignedMeasure`, `hasSum_indicatorConstLp`, `dualSignedMeasure_ac`, `dualDensity`, `setIntegral_dualDensity`, `dualDensity_simpleFunc`, `signedApprox`, `eLpNorm_dualDensity_le`, `pairLqLp`, `pairLqLp_injective`, `exists_preimage_pairLqLp`, `norm_pairLqLp`, `dualLp`, `example_15_4` |
| p. 449 | `L₁* = L∞` | `pairLinfL1`, `pairLinfL1_injective`, `exists_preimage_pairLinfL1`, `norm_pairLinfL1`, `dualL1`, `l1_dual_sigmaFinite`, `infAtom`, `l1_dual_counterexample`, `l1_dual_pairing_counterexample` |
| Exercise 15.5, p. 450 | (a) `f ∈ L₁` gives `x ↦ ∫ f x dμ` in `L∞*`; (b) it is `x ↦ ∫ x dν`, `ν ≪ μ` | `pairL1Linf`, `abs_pairL1Linf_le`, `ex_15_5a`, `ex_15_5b` |
| p. 450 | `Z = ℕ`, `μ{n} > 0`: `L∞(Z, 𝒵, μ) = ℓ∞` | `ellInfToLinf`, `norm_ellInfToLinf`, `ellInfToLinf_surjective`, `example_15_4_linf_nat`, `positive_measure_counterexample` |
| Theorem 15.2, pp. 450–451 | Geometric Hahn–Banach theorem | `theorem_15_2_interior`, `theorem_15_2_finiteDimensional`, `theorem_15_2`, `BookTheorem15_2`, `theorem_15_2_counterexample`, `theorem_15_2_counterexample_finiteDimensional` |
| p. 451 | The space `Σ βᵗ \|xₜ\| < ∞` and the box `B = {\|xₜ\| ≤ 1}` | `weightToEllOne`, `dist_weightToEllOne`, `weightToEllOne_surjective`, `ex156Box`, `weightToEllOne_mem_ex156Box_iff`, `convex_ex156Box` |
| Exercise 15.6, p. 451 | `θ` is not interior to `B` | `ex_15_6`, `ex_15_6_zero_notMem_interior`, `interior_ex156Box` |
| p. 451 | Only `φ = 0` is `≤ 0` on `B`; Theorem 15.2 fails for `A = {θ}` | `eq_zero_of_le_zero_on_ex156Box`, `ex_15_6_no_separation` |

## §15.2 The First and Second Welfare Theorems

| Source | Claim | Lean |
| --- | --- | --- |
| p. 452 | Economy, aggregate technology, feasible allocations | `Feasible`, `aggTech` |
| p. 452 | Pareto optimality | `ParetoOptimal` |
| pp. 452–453 | Competitive equilibrium (E1)–(E3) | `CompetitiveEq` |
| Theorem 15.3, p. 453 | First Welfare Theorem | `LocalNonsatiation`, `theorem_15_3` |
| (1)–(2), pp. 453–454 | Steps of the proof | `ce_cost_le_of_utility_le`, `ce_cost_lt_of_utility_lt` |
| Assumptions 15.1–15.5, p. 455 | Convexity, semistrict quasi-concavity, continuity, convex technology, interior point | `Assumption15_1`, `Assumption15_2`, `Assumption15_3`, `Assumption15_4`, `Assumption15_5` |
| Theorem 15.4, (3)–(4), p. 455 | Second Welfare Theorem | `SupportsAllocation`, `theorem_15_4` |
| Proof of Theorem 15.4, step 1, p. 455 | `Aᵢ`, `Åᵢ` convex | `quasiconcave_real_of_semistrict`, `quasiconcave_of_assumptions`, `convex_weaklyPreferred`, `convex_strictlyPreferred`, `assumption15_2_convex_counterexample` |
| Proof of Theorem 15.4, step 2, p. 455 | `A = Åₕ + Σ_{i≠h} Aᵢ` is convex and misses `Y`; separation | `preferredSum`, `convex_preferredSum`, `preferredSum_nonempty`, `preferredSum_disjoint`, `exists_dual_nonneg_of_zero_notMem`, `exists_separating_of_finiteDimensional`, `exists_separating_of_interior`, `exists_separating_of_assumption15_5` |
| Proof of Theorem 15.4, steps 3–4, p. 456 | Extension to `Σᵢ Aᵢ`; (3) and (4) | `weaklyPreferred_subset_closure`, `le_of_weaklyPreferred`, `continuity_closure_counterexample` |
| Remark, pp. 456–458 | A cheaper point for every consumer gives a competitive equilibrium | `remark_cheaper_point` |
| Figure 15.3, pp. 457–458 | A Pareto optimum supported by a price but not a competitive equilibrium | `fig153X`, `fig153U`, `fig153Y`, `fig153x`, `fig153y`, `fig153φ`, `fig153_assumptions`, `fig153_paretoOptimal`, `fig153_supported`, `fig153_not_competitiveEq` |

## §15.3 Issues in the choice of a commodity space

| Source | Claim | Lean |
| --- | --- | --- |
| p. 458 | Under 15.1–15.5 the competitive equilibrium and Pareto-optimal allocations coincide | `paretoOptimal_not_ce_counterexample`, `ce_not_paretoOptimal_counterexample`; corrected: `exists_better_of_localNonsatiation`, `welfare_theorems_corrected` |
| p. 459 | Static models: `S = ℝᴷ`, every price is `p · x` | `example_15_1` (the equivalence of norms on `ℝᴷ` is not restated) |
| Exercise 15.7, p. 460 | (a) the positive orthant of `ℓ_p`, `1 ≤ p < ∞`, has empty interior; (b) that of `ℓ∞` does not | `lpPosOrthant`, `ex_15_7a`, `ex_15_7b` |
| (1), pp. 460–461 | The economy `X = ℓ∞⁺`, `u(x) = inf_t x_t`, `Y = {0 ≤ y_t ≤ 1 + 1/t}` | `ex158X`, `ex158U`, `ex158Y` |
| Exercise 15.8, p. 460 | The economy satisfies Assumptions 15.1–15.5 | `abs_ex158U_sub_le`, `half_mem_interior_ex158Y`, `ex_15_8` |
| (2)–(3), p. 460 | `x⁰ = y⁰ = (1 + 1/t)` is Pareto optimal and supported by some `φ ≠ 0` | `ex158x0`, `ex158_paretoOptimal`, `ex158_nonsatiated`, `ex158_exists_price` |
| (4), p. 461 | No supporting `φ` has the form `Σ_t p_t x_t` | `ex158_price_vanishes_single`, `ex158_no_inner_product` |
| (5), p. 461 | The weighted norm `Σ_t βᵗ \|x_t\|` | `weightedDist` |
| Exercise 15.9, p. 462 | `inf_t x_t` is not continuous in the norm (5) | `ex_15_9` |
| p. 462 | In the norm (5) the positive orthant, hence `Y`, has no interior point | `weighted_orthant_no_interior`, `weighted_no_interior_of_subset_orthant` |
| p. 462 | Stochastic models: `S = L∞`; the example re-read with state probabilities `βᵗ(1 − β)` | `hasSum_state_probabilities`, `example_15_4_linf_nat` |

## §15.4 Inner product representations of prices

| Source | Claim | Lean |
| --- | --- | --- |
| p. 463 | `S = X × X × …` with `‖x‖_s = sup_t ‖x_t‖`; the truncation `xᵀ` | `BddSeq`, `seqTrunc`, `norm_seqTrunc_le`, `seqTrunc_eq_sum_single`, `seqC00` |
| Lemma 15.5, (1)–(2), pp. 463–464 | `ψ(x) = lim_T φ(xᵀ) = Σ_t ψ_t(x_t)` is a continuous linear functional | `coordFunctional`, `sum_abs_coordFunctional_le`, `seqRegularPart`, `hasSum_seqRegularPart`, `tendsto_apply_seqTrunc`, `norm_seqRegularPart_le`, `seqRegularPart_eq_of_mem_seqC00`, `seqRegularPart_seqRegularPart`, `lemma_15_5` |
| (3), p. 464 | `X = ℝᴷ`: `ψ(x) = Σ_t Σ_k p_{tk} x_{tk}` | `seqRegularPart_real`, `seqRegularPart_euclid` |
| Assumption 15.6, p. 465 | Truncations far out are feasible | `SeqTruncClosed`, `Assumption15_6` |
| Assumption 15.7, p. 465 | Distant consumption matters little | `SeqTailInsensitive`, `Assumption15_7`, `SeqTailInsensitive.of_tendsto`, `SeqTailInsensitive.of_liminf` |
| Exercise 15.10(a), p. 465 | `C × C × …` satisfies 15.1 and 15.6 | `seqSet`, `convex_seqSet`, `seqTrunc_mem_seqSet`, `ex_15_10a` |
| Exercise 15.10(b), p. 465 | `Σ_t βᵗ U(x_t)` satisfies 15.2, 15.3, 15.7 | `SeqSemistrictQC`, `assumption15_2_iff_seq`, `discountedUtility`, `ex_15_10b_tail`, `ex_15_10b_continuousOn`, `discountedUtility_concave`, `ex_15_10b`, `ex_15_10b_counterexample` |
| Exercise 15.10(c), p. 465 | The fixed point `u_W` of an aggregator satisfies 15.2, 15.3, 15.7 | `IsAggregator`, `IsAggregatorFixedPoint`, `seqShift`, `ex_15_10c_tail`, `seq_monotoneOn_of_concave_nonneg`, `ex_15_10c`, `ex_15_10c_counterexample` |
| Exercise 15.11(a), p. 465 | `inf_t x_t` violates 15.7 | `infUtility`, `ex_15_11a` |
| Exercise 15.11(b), p. 465 | 15.7 iff `u(x) = lim_T u(xᵀ)` | `ex_15_11b_if`, `ex_15_11b_liminf`, `tailDist`, `tailPenalizedUtility`, `ex_15_11b_counterexample`, `oddDrop`, `oscillatingUtility`, `ex_15_11b_manual_counterexample` |
| Theorem 15.6, (4)–(5), p. 466 | `ψ` satisfies (4) and (5) | `theorem_15_6`, `theorem_15_6_counterexample` |
| (6)–(7), pp. 466–467 | Steps 1–3 of the proof | `seq_tendsto_segment`, `seq_support_step1_consumer`, `seq_support_step1_firm`, `seq_support_step2` |
| p. 467 | With Theorem 15.4: a supporting `ψ` without weight at infinity; with the Remark, an equilibrium | `theorem_15_6_of_supporting`, `theorem_15_6_competitiveEq`, `seqRegularPart_ne_zero_of_cheaper` |
| p. 468 | Truncation over an event `x^A = x · 1_{Z∖A}`; `A_n ↓ 0` | `linftyRestrict`, `linftyTrunc`, `LinftyNullSeq` |
| Lemma 15.7, p. 468 | `ψ(x) = lim_n φ(x^{A_n}) = ∫ p x dμ`, `p ∈ L₁` | `linftyRestrictNorm`, `linftyRestrictNorm_add_le`, `linftyTailInf`, `linftyTailSup`, `IsLinftyTailSeq`, `exists_isLinftyTailSeq`, `IsLinftyTailSeq.limitDual`, `IsLinftyTailSeq.abs_linftyTruncLimit_restrict_le`, `IsLinftyTailSeq.limitSignedMeasure`, `linfty_dual_eq_zero`, `lemma_15_7` |
| Assumptions 15.8–15.9, p. 468 | Truncations over small events are feasible and matter little | `Assumption15_8`, `Assumption15_9` |
| Exercise 15.12, p. 469 | Expected utility satisfies 15.2, 15.3, 15.9 | `linftyExpectedUtility`, `ex_15_12_assumption15_3`, `ex_15_12_assumption15_9`, `ex_15_12_assumption15_2`, `ex_15_12`, `ex_15_12_counterexample` |
| Theorem 15.8, p. 469 | The `L₁` part `ψ` satisfies (4) and (5) | `supportsAllocation_of_limit_bounds`, `theorem_15_8`, `theorem_15_8_inner_product` |
| (8), pp. 469–470 | `S = X₀ × X₁ × …` with `‖x‖_s = sup_t ‖x_t‖_t`; Lemma 15.5 and Assumptions 15.6–15.7 there | `LinftyTimeState`, `linftyTimeTrunc`, `linftyTSSingle`, `linftyCoordDual`, `sum_abs_linftyCoordDual_le`, `Assumption15_6_timeState`, `Assumption15_7_timeState` (for `X_t = L∞(μ^t)`) |
| p. 470 | Truncating period `t` on an event | `linftyPeriodTrunc` |
| Assumptions 15.8′–15.9′, p. 470 | 15.8–15.9 period by period | `Assumption15_8'`, `Assumption15_9'` |
| Theorem 15.9, (9), p. 470 | A supporting `ν(x) = Σ_t ∫ p_t x_t dμ^t`, `p_t ∈ L₁(μ^t)` | `theorem_15_9` |
| (10)–(11), step 1, p. 470 | `ψ` satisfies (4) and (5) on this space | Not stated: the proof here does not pass through `ψ` |
| (12), step 2, p. 471 | `ν_t` from Lemma 15.7; `ν = Σ_t ν_t` | `linftySumDual`, `norm_linftySumDual_le`, `exists_linftyTimeState_decomposition` |
| (13)–(14), step 3, pp. 471–472 | The bounds for consumers and firms | `linftyTS_consumer_bound`, `linftyTS_firm_bound` |
| Steps 4–5, p. 473 | (4) and (5) for `ν`; the form (9) | `supportsAllocation_of_limit_bounds`, `theorem_15_9` |

## §15.5 Bibliographic notes

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 473–474 | Sources; Mackey continuity and Assumptions 15.6–15.7 | Not formalised |
