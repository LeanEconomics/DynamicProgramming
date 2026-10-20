# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 4, pp. 66–102. Lean names are relative to `StokeyLucasPrescott.DeterministicDP`.
Where the Lean statement departs from the book, see [corrections](corrections.md).

## Introduction and §4.1 The Principle of Optimality

| Source | Claim | Lean |
| --- | --- | --- |
| (SP), (FE), p. 66 | The sequence problem and the functional equation | `Feasible`, `partialSum`, `total`, `vstar`, `SatisfiesFE` |
| Ex 4.1a, p. 66 | The one-sector growth model is a sequence problem | `ex_4_1a` |
| Ex 4.1b, p. 66 | So is the many-sector growth model | `consSet`, `ex_4_1b` |
| Assumptions 4.1–4.2, p. 69 | `Γ(x)` nonempty; partial sums converge in `R̄` | `Assumption41`, `Assumption42`, `tendsto_total`, `feasible_nonempty` |
| p. 69 | Assumption 4.2 holds if `Σ βᵗF⁺ < ∞` or `Σ βᵗF⁻ < ∞`; if `F` is bounded above or below with `β < 1`; if `F ≤ cθᵗ`, `θ < 1/β` | `tendsto_of_summable_pos`, `tendsto_of_summable_neg`, `assumption42_of_summable_pos`, `assumption42_of_summable_neg`, `summable_max_of_le_geometric`, `assumption42_of_bddAbove`, `assumption42_of_bddBelow`, `assumption42_of_geometric` |
| Ex 4.2a, p. 69 | Assumption 4.2 on `ℝˡ₊` with `‖y‖ ≤ θ‖x‖` and `F` concave and monotone | `Orthant`, `orthCombo`, `orthZero`, `orthOne`, `norm_le_geometric`, `ex_4_2a` |
| Ex 4.2b, p. 69 | Assumption 4.2 with `F(y, 0) ≤ θF(x, 0)` | `ex_4_2b` |
| (2)–(7), pp. 70–71 | The supremum function and solutions of (FE) described by cases | `addIso`, `addIso_apply`, `mulIso`, `mulIso_apply`, `le_of_forall_coe_lt_le`, `eq_biSup_iff` |
| Lemma 4.1, p. 71 | `u(x) = F(x₀, x₁) + βu(x′)` | `tail`, `tail_mem`, `tail_tail`, `consPlan`, `consPlan_mem`, `tail_consPlan`, `partialSum_succ`, `partialSum_succ'`, `continuous_add_mul`, `lemma_4_1` |
| Theorem 4.2, p. 71 | `v*` satisfies (FE) | `add_mul_biSup`, `theorem_4_2` |
| Theorem 4.3, pp. 72–74 | A solution of (FE) with (8) is `v*` | `coe_mul_add`, `le_of_le_add_limsup`, `le_of_add_le_liminf`, `total_le_of_FE`, `div_lt_of_lt_add_mul`, `theorem_4_3` |
| pp. 74–75 | Unrestricted borrowing: `v* ≡ +∞`, and `v(x) = x` is an extraneous solution violating (8) | `consF`, `partialSum_consF`, `monotone_partialSum_consF`, `borrowΓ`, `borrow_assumption41`, `borrow_assumption42`, `borrow_vstar`, `borrow_identity_FE`, `borrow_identity_not_8` |
| Ex 4.3a, p. 75 | `limsup βⁿv(xₙ) ≤ 0` implies `v ≤ v*` | `ex_4_3a` |
| Ex 4.3b, p. 75 | With dominating plans along which `βⁿv(x′ₙ) → 0`, `v = v*` | `ex_4_3b` |
| Theorem 4.4, p. 75 | Optimal plans satisfy (9) (with `β > 0`; a counterexample for `β = 0`) | `theorem_4_4`, `theorem_4_4_beta_zero` |
| Theorem 4.5, p. 76 | Plans satisfying (9) and (11) are optimal | `theorem_4_5` |
| pp. 76–77 | No borrowing: `v*(x) = x`; every plan satisfies (9), but hoarding violates (11) and is not optimal | `NNR`, `saveΓ`, `saveF`, `save_partialSum`, `save_assumption41`, `save_assumption42`, `save_vstar`, `save_all_satisfy_9`, `hoard`, `hoard_mem`, `save_hoard_total`, `save_hoard_not_11` |
| p. 77 | The optimal policy correspondence `G*` | `Gstar`, `optimal_generated_by_Gstar`, `generated_by_Gstar_optimal` |

## §4.2 Bounded returns

| Source | Claim | Lean |
| --- | --- | --- |
| Assumptions 4.3–4.4, p. 78 | `Γ` nonempty, compact-valued, continuous; `F` bounded and continuous, `0 < β < 1` | `Assumption43`, `Assumption44` |
| (2)–(3), pp. 78–79 | The operator `T` and the policy correspondence `G` | `obj`, `continuousOn_obj`, `bound_maxValue`, `bellman`, `bellman_apply`, `exists_bellman_argmax` |
| Theorem 3.3 (used), p. 79 | `T` is monotone and discounts | `bellman_mono`, `bellman_add_const`, `blackwell`, `bellman_contraction` |
| Theorem 4.6, p. 79 | Unique fixed point in `C(X)`, (4), `G` compact-valued and u.h.c. | `theorem_4_6` |
| pp. 79–80 | The fixed point is `v*` (Theorem 4.3) and `G` generates optimal plans (Theorem 4.5) | `curryF`, `assumption42_of_44`, `satisfiesFE_of_fixed`, `tendsto_bounded_discount`, `fixedPoint_eq_vstar`, `policy_plan_optimal` |
| Assumptions 4.5–4.6, Theorem 4.7, p. 80 | `v` is strictly increasing | `theorem_4_7` |
| Assumptions 4.7–4.8, Theorem 4.8, p. 81 | `v` is strictly concave and `G` is a continuous function | `cmb`, `cmb_self`, `IsConcaveS`, `IsStrictConcaveS`, `Assumption47`, `Assumption48`, `isClosed_concave`, `bellman_maps_concave`, `bellman_concave`, `argmax_unique_of_strictConcave`, `theorem_4_8` |
| Theorem 4.9, p. 82 | The policy functions of `Tⁿv₀` converge, uniformly if `X` is compact | `theorem_4_9` |
| Ex 4.4a, pp. 82–83 | Countable `X`, finite `Γ(x)`: `T` on `B(X)` | `DiscreteSetup`, `maxD`, `exists_maxD`, `le_maxD`, `bellmanD`, `bellmanD_apply`, `bellmanD_mono`, `bellmanD_add_const`, `bellmanD_contraction`, `ex_4_4a` |
| Ex 4.4b, p. 83 | `T_h` has a unique fixed point | `policyOp`, `policyOp_apply`, `policyOp_mono`, `policyOp_contraction`, `ex_4_4b` |
| Ex 4.4c, p. 83 | Policy iteration converges | `policyOp_le_bellmanD`, `isClosed_ge`, `isClosed_le'`, `ex_4_4c` |
| Theorem 4.10, p. 84 | Benveniste and Scheinkman | `theorem_4_10` |
| Assumption 4.9, Theorem 4.11, p. 85 | Differentiability of the value function | `liftS`, `liftS_of_mem`, `IsStrictConcaveS.isConcaveS`, `concaveOn_liftS`, `convex_image_Γ`, `eventually_mem_Γ`, `theorem_4_11` |
| Ex 4.5, p. 86 | `0 < g(x′) − g(x) < f(x′) − f(x)` | `ex_4_5` |

## §4.3 Constant returns to scale

| Source | Claim | Lean |
| --- | --- | --- |
| Assumptions 4.10–4.11, p. 88 | Conical, growth-bounded `Γ`; homogeneous `F` with `|F| ≤ B(‖x‖ + ‖y‖)` | `IsCone`, `csmul`, `Assumption410`, `Assumption411` |
| Ex 4.6a, p. 88 | `‖x_t‖ ≤ αᵗ‖x₀‖` | `ex_4_6a` |
| Ex 4.6b, p. 88 | Assumptions 4.1–4.2 hold | `abs_term_le`, `ex_4_6b` |
| Ex 4.6c, p. 88 | `v*` is homogeneous with `|v*(x)| ≤ c‖x‖` | `ex_4_6c`, `ex_4_6c_hom` |
| (1), p. 89 | The space `H(X)` and its norm | `InH`, `hnorm`, `hnorm_nonneg`, `bddAbove_sphere`, `abs_le_hnorm`, `hnorm_le`, `inH_sub`, `inH_add`, `inH_smul`, `hnorm_sub_le` |
| Ex 4.7a, p. 89 | `H(X)` is a complete normed vector space | `ex_4_7a_norm`, `ex_4_7a_complete` |
| Ex 4.7b, p. 89 | `T : H(X) → H(X)` | `crs`, `continuousOn_obj'`, `exists_crs_argmax`, `eq_zero_of_mem_zero`, `ex_4_7b` |
| pp. 89–90 | `v*` is the only solution in `H(X)` | `satisfiesFE_crs`, `crs_fixed_eq_vstar` |
| Theorem 4.12, p. 90 | Blackwell's conditions with `(f + a)(x) = f(x) + a‖x‖` | `theorem_4_12` |
| Theorem 4.13, pp. 90–91 | Unique fixed point, (3), `G` homogeneous, compact-valued and u.h.c. | `crs_mono`, `crs_disc`, `crs_contraction`, `theorem_4_13` |
| Ex 4.8a, p. 91 | Homogeneous and quasi-concave implies concave | `IsQuasiConcaveS`, `IsStrictQuasiConcaveS`, `cmb_eq_csmul_cmb`, `ex_4_8a`, `ex_4_8a_counterexample` |
| Ex 4.8b, p. 91 | Strict quasi-concavity gives strict concavity across non-proportional points | `ex_4_8b` |
| Ex 4.8c, p. 92 | When is `v` strictly quasi-concave? | `NonProp`, `ConcaveGraph`, `crs_concave`, `ex_4_8c` |
| Ex 4.8d, p. 92 | When is `v` differentiable? | `ex_4_8d` |

## §4.4 Unbounded returns

| Source | Claim | Lean |
| --- | --- | --- |
| p. 92 | `T` on all functions `X → R̄` is monotone | `opT`, `satisfiesFE_iff_opT`, `opT_mono` |
| Theorem 4.14, pp. 92–93 | Iterating down from an upper bound gives `v*` | `iterate_antitone`, `limitFn`, `tendsto_iterate`, `theorem_4_14` |
| pp. 93–95 | The unit-elastic growth model: Assumptions 4.1–4.2, (4), `v̂`, `Tⁿv̂`, `v = v*`, `g(k) = αβk^α` optimal | `PosR`, `logΓ`, `logF`, `coefB`, `coefC`, `affineLog`, `logPolicy`, `αβ_lt_one`, `coefB_pos`, `coefC_neg`, `logPolicy_mem`, `log_objective_le`, `log_opT_affine`, `log_iterate`, `log_assumption41`, `log_capital_le`, `logF_le`, `log_assumption42`, `log_vstar`, `log_policy_optimal` |
| pp. 95–97 | The quadratic investment model: (6)–(8), `βₙ → β ∈ (b, b + c)`, `αₙ → α`, `γₙ → γ`, `v = v*`, the linear policy optimal | `tendsto_zero_of_le_contract`, `tendsto_linear_recursion`, `quadF`, `quadΓ`, `quadFn`, `nextQ`, `nextP`, `nextR`, `quad_objective`, `quad_opT`, `quadF_le`, `qs`, `ps`, `rs`, `qs_nonneg`, `nextQ_mono`, `nextQ_lt`, `qs_mono`, `tendsto_qs`, `quad_iterate`, `tendsto_ps_rs`, `quad_vstar`, `quad_policy_optimal` |

## §4.5 Euler equations

| Source | Claim | Lean |
| --- | --- | --- |
| (2)–(3), p. 98 | Euler equations and transversality | `Fx`, `Fy`, `apply_eq_Fx_add_Fy` |
| Theorem 4.15, pp. 98–99 | Sufficiency of the Euler and transversality conditions | `concave_le_fderiv`, `euler_telescope`, `le_of_le_add_tendsto_zero`, `euler_sufficient`, `theorem_4_15` |
| Ex 4.9a, p. 99 | `g(k) = αβk^α` is optimal (Theorem 4.15) | `egΓ`, `egF`, `egD`, `egF_hasFDerivAt`, `egFx`, `egFy`, `egF_concave`, `eg_pos`, `eg_assumption42`, `ex_4_9a` |
| Ex 4.9b, p. 100 | The linear investment policy is optimal | `qF`, `qD`, `qFx`, `qFy`, `qF_le`, `ex_4_9b` |
| (4)–(5), p. 100 | The first-order and envelope conditions give the Euler equations | `euler_of_envelope` |

## Carried over from Chapter 3

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 3.2, Corollaries 1–2, Ex 3.8–3.9 | The Contraction Mapping Theorem | `IsContraction`, `IsContraction.uniformContinuous`, `dist_iterate_succ_le`, `dist_iterate_le`, `cauchySeq_iterate`, `theorem_3_2`, `dist_fixedPoint_le`, `corollary_1`, `corollary_2` |
| p. 56, Ex 3.11a, Ex 3.15 | Hemi-continuity | `IsLHC`, `IsUHC`, `graph`, `continuousAt_of_isUHC_singleton`, `isCompact_graph` |
| Theorem 3.6, Lemma 3.7, Theorem 3.8 | The Theorem of the Maximum (Lemma 3.7 and Theorem 3.8 for unique maximizers) | `maxValue`, `argmax`, `continuousOn_section`, `exists_argmax`, `le_maxValue`, `tendsto_f_graph`, `theorem_3_6`, `UniqueArgmax`, `argmaxFn`, `UniqueArgmax.argmaxFn_mem`, `UniqueArgmax.argmax_eq`, `UniqueArgmax.lt_of_ne`, `UniqueArgmax.continuous_argmaxFn`, `UniqueArgmax.lemma_3_7`, `UniqueArgmax.lemma_3_7_uniform`, `shortfall_lt`, `theorem_3_8`, `theorem_3_8_uniform` |
| Ex 3.12d (proof) | Interior points of convex-valued l.h.c. correspondences | `dual_apply_eq_sum`, `vertex`, `no_separation`, `eventually_mem_of_mem_interior` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Figures 4.1–4.2, pp. 85–86 | Illustrations | The facts they illustrate are proved (`theorem_4_10`, `ex_4_5`). |
| §4.6 | Bibliographic notes | No mathematical content. |
