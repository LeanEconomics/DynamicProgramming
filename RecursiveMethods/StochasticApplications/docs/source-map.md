# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 10, pp. 288–315. Lean names are relative to
`StokeyLucasPrescott.StochasticApplications`. Where the Lean statement departs from the book, see
[corrections](corrections.md).

The models are stated in the framework of Chapter 9 (`Model`, `BoundedDP`, `bellman`, `policy`),
whose modules are carried from `RecursiveMethods/StochasticDP`; the source map of that project
covers them.

## §10.1 The one-sector model of optimal growth

| Source | Claim | Lean |
| --- | --- | --- |
| (U1)–(U5), (T1)–(T5), (Z1)–(Z3), pp. 288–289 | The hypotheses; (2) in the first formulation | `GrowthHyp`, `growthΓ`, `growthF`, `growthModel`, `growth_boundedDP`, `exists_measurableSelection_Icc` |
| Ex 10.1a, p. 289 | The sequence problem is well defined | `ex_10_1a` |
| Ex 10.1b, p. 289 | Unique bounded continuous `v`; `G` u.h.c.; `v = v*`; optimal plans | `ex_10_1b` |
| Ex 10.1c, p. 289 | `v(·, z)` strictly increasing and strictly concave; `g` continuous | `growth_strictMono`, `growth_concave`, `growth_flat_step`, `growth_strictConcave`, `growth_argmax_unique`, `ex_10_1c` |
| Ex 10.1d, p. 289 | With i.i.d. shocks `g(x, z) = h[z f(x)]`, `g` and `c` increasing (corrected) | `outΓ`, `outH`, `outH_uniqueArgmax`, `growth_argmax_eq_out`, `ex_10_1d`, `ex_10_1d_counterexample`, `ex_10_1d_not_strictMono` |
| Ex 10.1e, p. 289 | `v_x = U′(c) z f′(x)`, `v_z = U′(c) f(x)` | `hasDerivAt_of_concaveOn_of_le`, `growth_hasDerivAt_x`, `growth_concave_z`, `growth_hasDerivAt_z`, `ex_10_1e` |
| Ex 10.1f, p. 290 | Markov shocks (Z3): (a)–(c) unchanged, `v` increasing in `z` | `growth_bellman_mono_z`, `ex_10_1f` |

## §10.2 Optimal growth with two capital goods

| Source | Claim | Lean |
| --- | --- | --- |
| p. 290 | The model | `twoX`, `TwoHyp`, `twoΓ`, `twoF`, `twoModel`, `two_boundedDP` |
| Ex 10.2a, p. 290 | The sustainable stocks form a compact set | `ex_10_2a` |
| Ex 10.2b, p. 290 | Unique `v`, strictly increasing, strictly concave, differentiable; `g` continuous (corrected) | `two_strictMono`, `ex_10_2b`, `ex_10_2b_diff`, `ex_10_2b_counterexample` |
| Ex 10.2c, p. 290 | `g` strictly increasing under complementarity | Not formalised |
| Ex 10.2d, p. 290 | Reduction to one endogenous state | `twoφ`, `continuous_twoφ`, `twoφ_attain`, `twoφ_hyp`, `twoφ_concave`, `ex_10_2d` |

## §10.3 Optimal growth with many goods

| Source | Claim | Lean |
| --- | --- | --- |
| (a)–(c), p. 291 | The technology `Φ`; `Γ`, `A`, `F` | `TechHyp`, `manyΓ`, `manyF`, `manyModel`, `manyF_spec` |
| Ex 10.3a, p. 291 | `Γ`, `A`, `F` satisfy Assumptions 9.6–9.11 (corrected) | `many_boundedDP`, `manyF_mono`, `manyF_concave`, `ex_10_3a`, `ex_10_3a_counterexample` |
| Ex 10.3b, p. 292 | Optimal consumption and capital plans | `ManyFeasible`, `manyUtility`, `exists_gammaStar`, `ex_10_3b` |

## §10.4 Industry investment under uncertainty

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 292–295 | The model; (2′) with `Γ(x) = [(1 − δ′)x, max{M, x}]` | `IndHyp`, `indΓ`, `indF`, `indModel`, `IndHyp.upperDP` |
| Manual pp. 177–178 | `F` bounded; Assumptions 9.9 and 9.11 hold for (2′) (corrected) | `ind_F_unbounded`, `ind_Γ_not_mono`, `ind_Γ_not_convex` |
| — | Returns bounded above: truncation | `UpperDP`, `truncModel`, `truncT`, `trunc_bellman_argmax`, `truncT_mapsTo`, `upper_fixed` |
| Ex 10.4a, p. 294 | The sequence problem | Not formalised (interpretive) |
| Ex 10.4b, p. 295 | Unique bounded continuous `v ≥ 0` solving (2′); it solves (2) | `ind_rhs_le`, `ind_rhs_neg`, `ex_10_4b` |
| Ex 10.4c, p. 295 | `v` strictly increasing, strictly concave in `x`; `g` continuous and interior; `v(·, z)` differentiable | `ind_strictMono_x`, `ind_strictMono_z`, `ind_strictConcave`, `ind_continuousOn_objG`, `ind_max`, `ind_policy`, `ind_hasDerivAt_x`, `ex_10_4c` |
| Ex 10.4d, p. 295 | `g` increasing in `x` (weak form) | `ind_cost_submod`, `ex_10_4d` |
| Ex 10.4e, pp. 295–296 | `g` increasing in `z` | Not formalised (see corrections) |
| Ex 10.4f, p. 296 | i.i.d. shocks: `g` independent of `z`; the capacity path converges | `ind_mem_policy_iff`, `ex_10_4f`, `ex_10_4f_monotone`, `ex_10_4f_tendsto` |

## §10.5 Production and inventory accumulation

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 297–298 | The model, with `n ≤ N̄` | `InvHyp`, `invΓ`, `invφ`, `invF`, `invModel`, `exists_N_big`, `InvHyp.upperDP` |
| Ex 10.5a, p. 298 | Strictly convex cost and linear output ≡ linear cost and strictly concave output | `mul_le_of_convexOn`, `ex_10_5a` |
| Ex 10.5b, p. 299 | The current shock does not appear in (2) | `inv_indep` (the sequence problem is not formalised) |
| Ex 10.5c, p. 299 | Unique bounded continuous `v`; strictly increasing and concave; `Y`, `N` continuous; `v′(x) = U′[x − Y(x)]` | `inv_bounds`, `inv_max`, `inv_solves_2`, `inv_strictMono`, `inv_F_cmb`, `inv_E_cmb`, `inv_strictConcave`, `inv_policy`, `inv_hasDerivAt`, `ex_10_5c` |
| Ex 10.5d, p. 299 | Consumption strictly increasing | Not formalised (first-order conditions) |
| Ex 10.5e, pp. 299–300 | More storage, less production at higher `x` (weak form) | `concave_four`, `concave_sum_submod`, `U_sub_submod`, `ex_10_5e` |
| Ex 10.5f, p. 300 | (5) and (6) contradict each other | `ex_10_5f` |
| Ex 10.5g, p. 300 | `N(x) > 0`; `N` strictly decreasing | Weak monotonicity in `ex_10_5e`; the rest not formalised |

## §10.6 Asset prices in an exchange economy

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 300–302 | The consumer's problem | `assetX`, `AssetHyp`, `assetΓ`, `assetF`, `assetModel`, `asset_boundedDP` |
| Ex 10.6a–b, p. 302 | `vᵖ` exists, is unique, increasing and concave; `Gᵖ` | `asset_concave`, `ex_10_6ab` |
| Ex 10.6c, pp. 302–303 | The envelope condition (1) and the Euler equation (2) | `ex_10_6c_deriv`, `ex_10_6c_euler` |
| Ex 10.6d, p. 303 | Equilibrium conditions (3)–(5) | `ex_10_6d` |
| Ex 10.6e, p. 304 | (6) has a unique positive solution | `fellerOp`, `priceT`, `priceT_contraction`, `ex_10_6e_general`, `ex_10_6e` |
| Ex 10.6f–g, p. 304 | Interpretation | Not formalised |

## §10.7 A search model

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 10.7a, p. 305 | The law of motion | `searchφ`, `searchModel`, `ex_10_7a` |
| Ex 10.7b–c, pp. 305–306 | The functional equation (1) and its unique solution | `search_boundedDP`, `search_bellman_indep`, `search_bellman_eq_max`, `ex_10_7c` |
| Ex 10.7d–e, p. 306 | The reservation wage, (3)–(4) | `SearchSol`, `searchSol_of_fixed`, `ex_10_7d`, `ex_10_7e` |
| Ex 10.7f–g, pp. 306–307 | (5)–(6), uniqueness of `w*` | `cdfF`, `ex_10_7f`, `resΨ`, `resΨ_strictMono`, `ex_10_7g`, `ex_10_7g_unique` |
| Ex 10.7h, p. 307 | Comparative statics in `θ` and `β` | `ex_10_7h_θ`, `ex_10_7h_β` |
| Ex 10.7i, p. 307 | The effect of the variance of offers | Not formalised (open-ended) |

## §10.8 Dynamics of the search model

| Source | Claim | Lean |
| --- | --- | --- |
| (1a)–(1b), p. 308 | The transition function `P` and the laws `λₜ` | `searchP`, `searchP_adjoint`, `searchLaw` |
| Ex 10.8a, p. 309 | (2) and its limit (3) | `tendsto_affine_rec`, `ex_10_8a` |
| Ex 10.8b, p. 309 | (4)–(5) | `ex_10_8b_zero`, `ex_10_8b` |
| Ex 10.8c, p. 309 | (6) | `ex_10_8c` |
| Ex 10.8d, p. 310 | Interpretation | Not formalised |

## §10.9 Variations on the search model

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 10.9a–e, pp. 310–311 | Reformulate the functional equation | Not formalised (no claim to prove) |

## §10.10 A model of job matching

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 10.10a–b, p. 312 | Beta posteriors | `integral_beta_kernel`, `postDensity`, `ex_10_10a`, `ex_10_10b` |
| Ex 10.10c, p. 312 | `π(n, k) = (α + k)/(α + β + n)` | `postMean`, `betaπ`, `ex_10_10c` |
| Ex 10.10d–e, p. 313 | Properties of `π` | `PiProps`, `ex_10_10d`, `betaπ_tendsto`, `ex_10_10e`, `betaπ_window` |
| Ex 10.10f, p. 313 | Unique `v ∈ S` solving (1) | `jobT`, `jobT_contraction`, `ex_10_10f` |
| Ex 10.10g, p. 314 | Monotonicity of `v`; the limit | `jobMono`, `ex_10_10g`, `ex_10_10g_limit`, `ex_10_10g_beta` |
| Ex 10.10h, p. 314 | The threshold policy `k ≥ jₙ` | `jobG`, `ex_10_10h` |
| Ex 10.10i, p. 314 | Average wage by seniority | Not formalised |

## §10.11 Job matching and unemployment

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 10.11a–b, pp. 314–315 | Reformulate and interpret | Not formalised (no claim to prove) |
