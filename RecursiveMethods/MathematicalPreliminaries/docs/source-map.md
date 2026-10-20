# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 3, pp. 39–65. Lean names are relative to
`StokeyLucasPrescott.MathematicalPreliminaries`. Where the Lean statement departs from the book,
see [corrections](corrections.md).

## Introduction: successive approximations (pp. 39–43)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 41 | The lifetime utility `w₀` of a feasible policy `g₀` | `policyValue` |
| Ex 3.1, p. 41 | `w₀(k) = U[f(k) − g₀(k)] + βw₀[g₀(k)]` | `exercise_3_1` |
| (4), p. 41 | Starting from `v₀ = w₀`, `v₁ ≥ v₀` | `policyValue_le_bellmanOp` |
| pp. 41–42 | The successive approximations then increase | `iterate_mono` |
| p. 40, "(Why?)" | A limit independent of the initial guess is the only solution of (1) | `fixedPoint_eq_limit` |

## §3.1 Metric spaces and normed vector spaces

| Source | Claim | Lean |
| --- | --- | --- |
| p. 43–44 | Vector spaces; a set of functions or vectors with the usual operations is one exactly when it is a subspace | `IsSubspace` |
| Ex 3.2a, 3.2c, p. 44 | `ℝˡ` and the space of all real sequences | `isSubspace_univ` |
| Ex 3.2b, p. 44 | A line through the origin in `ℝ²` | `isSubspace_line` |
| Ex 3.2d, p. 44 | The continuous functions on `[a, b]` | `isSubspace_continuousOn` |
| Ex 3.2e–g, p. 44 | The unit circle, the integers and the nonnegative functions are not vector spaces | `not_isSubspace_circle`, `not_isSubspace_int`, `not_isSubspace_nonneg` |
| p. 44 | Metric spaces | `IsMetric`, `IsMetric.self` |
| Ex 3.3a–b, p. 45 | The integers with `|x − y|` and with the discrete metric | `isMetric_int`, `isMetric_discrete` |
| Ex 3.3c–d, p. 45 | Continuous strictly increasing functions on `[a, b]` with the sup and `L¹` distances | `StrictIncr`, `isMetric_sup_strictMono`, `isMetric_l1_strictMono` |
| Ex 3.3e, p. 45 | The rationals | `isMetric_rat` |
| Ex 3.3f, p. 45 | `ρ(x, y) = f(|x − y|)` for strictly increasing, strictly concave `f` with `f(0) = 0` | `concave_subadditive`, `isMetric_comp` |
| p. 45 | Normed vector spaces | `IsNorm`, `isNorm_norm` |
| p. 46 | A norm gives a metric | `IsNorm.isMetric` |
| Ex 3.4a–c, p. 45 | `ℝˡ` with the Euclidean, max and sum norms | `isNorm_euclid`, `isNorm_max`, `abs_le_max_norm`, `max_norm_le`, `isNorm_sum` |
| Ex 3.4d, p. 45 | `ℓ∞` | `ellInf`, `supNorm`, `abs_le_supNorm`, `supNorm_le`, `isNorm_ellInf` |
| Ex 3.4e, p. 45 | `C[a, b]` with the sup norm | `isNorm_sup` |
| Ex 3.4f, p. 45 | `C[a, b]` with `∫ₐᵇ |x(t)| dt` | `ext`, `continuous_ext`, `ext_of_mem`, `ext_add`, `ext_smul`, `ext_sub`, `l1`, `l1_nonneg`, `l1_zero`, `integral_pos_of_pos`, `l1_eq_zero_iff`, `l1_add_le`, `l1_smul`, `l1_neg`, `l1_le_norm`, `isNorm_l1` |
| (1)–(2), p. 46 | Convergence and the Cauchy criterion | `Converges`, `IsCauchy` |
| Ex 3.5a–d, p. 46 | Limits are unique; convergent sequences are Cauchy; Cauchy sequences are bounded; `xₙ → x` iff every subsequence converges to `x` | `limit_unique`, `IsCauchy.of_converges`, `IsCauchy.bounded`, `converges_iff_subseq` |
| p. 47 | Complete metric spaces; `ℝ` is complete (Fact) | `IsCompleteFor`, `isCompleteFor_of_completeSpace` |
| Ex 3.6a, p. 47 | The spaces of Ex 3.3a–b and 3.4a–e are complete | `isComplete_of_eventually_const`, `isComplete_int`, `isComplete_discrete`, `isComplete_of_equiv_max`, `sum_abs_le_card_mul_max`, `max_le_sum_abs`, `isComplete_sum`, `isComplete_max`, `isComplete_euclid`, `isComplete_ellInf`, `isComplete_sup` |
| Ex 3.6a, p. 47 | The spaces of Ex 3.3c–e are not complete | `ramp`, `ramp_strictMono`, `norm_ramp_le`, `norm_ramp_tendsto`, `isCauchy_of_tendsto_zero`, `not_isComplete_sup_strictMono`, `not_isComplete_l1_strictMono`, `not_isComplete_rat` |
| Ex 3.6a, p. 47 | The space of Ex 3.4f is not complete | `integral_abs_ge`, `stepRamp`, `stepRamp_apply`, `stepRamp_nonneg`, `stepRamp_le_one`, `stepRamp_mono`, `stepRamp_left`, `stepRamp_right`, `rampIntegral`, `ext_stepRamp_mono`, `l1_stepRamp_sub`, `rampIntegral_mono`, `rampIntegral_le`, `isCauchy_stepRamp`, `away_of_ne`, `limit_eq_zero_left`, `limit_eq_one_right`, `not_isComplete_l1` |
| Ex 3.6a, p. 47 | Ex 3.3c is complete with "nondecreasing" in place of "strictly increasing" | `isComplete_sup_monotone` |
| Ex 3.6b, p. 47 | A closed subset of a complete space is complete | `IsClosedFor`, `isComplete_subset` |
| Theorem 3.1, pp. 47–49 | `C(X)` with the sup norm is complete | `theorem_3_1` |
| Ex 3.7a, p. 49 | `C¹[a, b]` with `max |f| + max |f′|` is a Banach space | `IsCk`, `ckSub`, `ckNorm`, `ext_zero`, `isCk_iff_integral`, `isClosed_ckSub`, `norm_le_ckNorm`, `ckNorm_le`, `ex_3_7a` |
| Ex 3.7b, p. 49 | `C¹[a, b]` with `max |f|` is not complete; the example sequence is not Cauchy in the norm of (a) | `restrictC`, `ext_restrictC`, `mk1`, `isNorm_sup_C1`, `sqrtSeq`, `sqrtSeq'`, `sqrtSeq_pos`, `continuous_sqrtSeq`, `continuous_sqrtSeq'`, `hasDerivAt_sqrtSeq`, `abs_sqrt_sub_abs_le`, `ex_3_7b` |
| Ex 3.7c, p. 49 | `C^k[a, b]` with `∑ αᵢ max |f⁽ⁱ⁾|` is complete iff every `αᵢ > 0` | "if": `isNorm_ckNorm`, `isComplete_ckNorm`; "only if" refuted: `abs_ext_le`, `interpolation`, `ex_3_7c_counterexample`; `α₀ = 0`: `not_isNorm_of_alpha0` |

## §3.2 The Contraction Mapping Theorem

| Source | Claim | Lean |
| --- | --- | --- |
| p. 50 | Contraction mappings | `IsContraction` |
| Ex 3.8, p. 50 | A contraction is uniformly continuous | `IsContraction.uniformContinuous` |
| Theorem 3.2, pp. 50–52 | A contraction on a complete space has exactly one fixed point `v`, and `ρ(Tⁿv₀, v) ≤ βⁿρ(v₀, v)` | `dist_iterate_succ_le`, `dist_iterate_le`, `cauchySeq_iterate`, `theorem_3_2` |
| Corollary 1, p. 52 | The fixed point lies in a closed `S'` with `T(S') ⊆ S'`, and in `S''` when `T(S') ⊆ S'' ⊆ S'` | `corollary_1` |
| Ex 3.9, p. 53 | `ρ(Tⁿv₀, v) ≤ ρ(Tⁿv₀, Tⁿ⁺¹v₀)/(1 − β)` | `dist_fixedPoint_le` |
| Corollary 2, p. 53 | The N-stage contraction theorem | `corollary_2` |
| Ex 3.10a, pp. 53–54 | `(Tv)(s) = c + ∫₀ˢ f(v(z)) dz` maps `C[0, t]` into itself | `picardFn`, `continuous_picardFn`, `picard`, `picard_apply` |
| Ex 3.10b, p. 54 | `T` is a contraction on `C[0, τ]` for some `τ > 0` | `ex_3_10b` |
| Ex 3.10c, p. 54 | The fixed point is differentiable and is the unique solution of the differential equation on `[0, τ]` | `ex_3_10c` |
| Theorem 3.3, p. 54 | Blackwell's sufficient conditions for a contraction | `IsBdd`, `supDist`, `bddAbove_absDiff`, `abs_le_supDist`, `supDist_le`, `supDist_nonneg`, `theorem_3_3` |
| pp. 54–55 | The growth model's operator satisfies monotonicity and discounting | `bellmanOp`, `bddAbove_bellman`, `le_bellmanOp`, `bellmanOp_bdd`, `bellmanOp_mono`, `ciSup_add_const`, `bellmanOp_add_const`, `bellmanOp_contraction` |

## §3.3 The Theorem of the Maximum

| Source | Claim | Lean |
| --- | --- | --- |
| (1)–(2), p. 56 | `h(x) = max_{y ∈ Γ(x)} f(x, y)`, `G(x)` the maximizers | `maxValue`, `argmax` |
| p. 56 | Lower and upper hemi-continuity | `IsLHC`, `IsUHC`, `IsCompactValued` |
| p. 57 | `Γ(X̂)`; the graph `A` (p. 60) | `image`, `graph` |
| Ex 3.11a, p. 57 | A single-valued u.h.c. correspondence is continuous | `continuousAt_of_isUHC_singleton`, `isUHC_singleton_of_continuousAt` |
| Ex 3.11b–f, pp. 57–58 | Projections, unions, intersections, compositions and products of u.h.c. correspondences | `isUHC_proj`, `isUHC_union`, `isUHC_inter`, `isUHC_comp`, `isUHC_pi` |
| Ex 3.11g, p. 58 | `Γ(K)` is compact for compact `K` | `isCompact_image` |
| Ex 3.12a–c, e–f, pp. 58–59 | The same for l.h.c. correspondences | `continuousAt_of_isLHC_singleton`, `isLHC_proj`, `isLHC_union`, `isLHC_comp`, `isLHC_pi` |
| Ex 3.12d, p. 59 | An intersection of l.h.c. correspondences need not be l.h.c. | `not_isLHC_inter` |
| Ex 3.12d, p. 59 | It is l.h.c. if both are convex-valued and `int φ(x) ∩ int ψ(x) ≠ ∅` | `dual_apply_eq_sum`, `vertex`, `no_separation`, `eventually_mem_of_mem_interior`, `isLHC_inter_of_interior` |
| Ex 3.13a–b, p. 59 | `[0, x]` and `[0, f(x)]` are continuous | `isLHC_Icc`, `isUHC_Icc`, `ex_3_13a`, `ex_3_13b` |
| Ex 3.13c, p. 59 | The production possibility correspondence is continuous | `Orthant`, `budget`, `allocGraph`, `budget_eq`, `allocGraph_nonempty`, `isUHC_allocGraph`, `isLHC_allocGraph`, `ex_3_13c` |
| Ex 3.14a, p. 60 | `{y : H(x, y) ≥ 0}` for monotone `H` | `superlevel`, `isLHC_superlevel`, `isUHC_superlevel`, `ex_3_14a` |
| Ex 3.14b, p. 60 | `{y : H(x, y) ≥ 0}` for concave `H` with a Slater point | `ex_3_14b` |
| Ex 3.14c, p. 60 | `H = 1 − max{|x|, |y|}`: where `Γ` fails to be l.h.c. | `ex_3_14c` |
| Theorem 3.4, p. 60 | A closed graph with bounded images of bounded sets gives a compact-valued u.h.c. correspondence | `theorem_3_4` |
| p. 60 | Boundedness is needed in Theorem 3.4 | `closedGraph_not_uhc` |
| Ex 3.15, p. 61 | The graph of a compact-valued u.h.c. correspondence on a compact `X` is compact | `isCompact_graph` |
| Theorem 3.5, p. 61 | A convex graph with locally bounded selections gives a correspondence l.h.c. at interior points | `theorem_3_5` |
| Theorem 3.6, p. 62 | The Theorem of the Maximum | `continuousOn_section`, `exists_argmax`, `le_maxValue`, `tendsto_f_graph`, `theorem_3_6` |
| Ex 3.16a, p. 62 | `f(x, y) = xy²` on `[−1, 1]`: `G` is u.h.c. but not l.h.c. at `0` | `isLHC_const`, `isUHC_const`, `not_isLHC_of_eventually`, `ex_3_16a` |
| Ex 3.16b, p. 62 | `f = max{2 − (y − 1)², x + 1 − (y − 2)²}` on `[0, 4]`: `G` fails to be l.h.c. exactly at `x = 1` | `f316b`, `continuous_f316b`, `argmax_316b`, `ex_3_16b` |
| Ex 3.16c, p. 63 | `f = cos y` on `[−x, x]`: `G` fails to be l.h.c. exactly at `x = 2πk`, `k ≥ 1` | `NNR`, `gamma316c`, `tendsto_val`, `gamma316c_continuous`, `argmax_316c`, `not_tendsto_of_far`, `ex_3_16c` |
| p. 63 | With convex values and strict concavity, `G` is single-valued and continuous | `ArgmaxSetup`, `ArgmaxSetup.argmax_unique`, `argmaxFn`, `ArgmaxSetup.argmaxFn_mem`, `ArgmaxSetup.argmax_eq`, `ArgmaxSetup.lt_of_ne`, `ArgmaxSetup.continuous_argmaxFn` |
| Lemma 3.7, pp. 63–64 | Near-maximal values are attained near `g(x)`, uniformly when `X` is compact | `ArgmaxSetup.lemma_3_7`, `ArgmaxSetup.lemma_3_7_uniform` |
| Theorem 3.8, pp. 64–65 | If `fₙ → f` uniformly, `gₙ → g` pointwise, and uniformly when `X` is compact | `shortfall_lt`, `theorem_3_8`, `theorem_3_8_uniform` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Ex 3.16a–c | "Graph `G(x)`" | Diagrams; the facts they illustrate are proved. |
| Figures 3.1–3.2, p. 51, p. 57 | Illustrations | No formal content beyond the definitions. |
| §3.4 | Bibliographic notes | No mathematical content. |
