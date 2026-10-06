# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 7, "Nonlinear Valuation" (pp. 213–245). Result, equation and exercise
numbers are the book's; page numbers are book pages. Lean names are relative to
`SargentStachurski.NonlinearValuation`. Where the Lean statement adds a hypothesis
the book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## Earlier-chapter facts restated

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, Ch. 1–3 | Markov matrices, contractions, Banach's theorem, Prop 2.2.7, Blackwell's condition, Lemma 2.2.2 | `IsMarkov`, `IsDistribution`, `GloballyStable`, `IsContractionOn`, `IsContractionOn.globallyStable_univ`, `fixedPt_le_of_le`, `le_fixedPt_of_le_apply`, `isContractionOn_of_blackwell`, `abs_sup'_sub_sup'_le` |
| Vol. 1, (1.15), Thm 1.2.1, Ex 2.2.28 | Spectral radius, Gelfand, Neumann series, monotonicity | `specRad`, `tendsto_norm_pow_rpow`, `tendsto_norm_pow_zero`, `neumann_series`, `specRad_le_of_le`, `pow_nonneg_entries` |
| Vol. 1, Thm 2.3.1, Lemmas 2.3.2–2.3.3 | Perron–Frobenius, nonnegative and irreducible cases; local spectral radius | `perron_frobenius`, `perron_frobenius_left`, `tendsto_norm_pow_mulVec_rpow`, `Irreducible`, `Irreducible.specRad_pos`, `Irreducible.exists_pos_eigenvector`, `Irreducible.exists_pos_left_eigenvector`, `IsMarkov.exists_unique_stationary_of_irreducible` |
| Vol. 1, Thm 6.1.1, Lemma 6.1.4 | `v = h + Lv` is solved by `(I − L)⁻¹h = ∑ Lᵗh` when `ρ(L) < 1`; necessity for positive solutions | `inv_mulVec_eq_tsum`, `inv_mulVec_eq_add`, `eq_add_mulVec_iff`, `specRad_smul_isMarkov`, `specRad_lt_one_iff_existsUnique_pos` |
| Vol. 1, Thm 6.1.5, Example 6.1.2, Prop 6.1.6 | Eventual contractions; affine maps | `globallyStable_of_iterate_contraction`, `affineOp`, `globallyStable_affineOp`, `isFixedPt_affineOp_inv`, `exists_isContractionOn_iterate_of_abs_sub_le` |
| Vol. 1, p. 45 | Topological conjugacy preserves global stability | `GloballyStableOn`, `GloballyStableOn.of_conj`, `globallyStableOn_iff_of_conj`, `globallyStableOn_univ_iff`, `GloballyStableOn.existsUnique` |

## §7.1 Beyond contraction maps (pp. 213–219)

| Book | Claim | Lean |
| --- | --- | --- |
| Thm 7.1.1, p. 214 | Knaster–Tarski: least and greatest fixed points `a ≤ b`, `Tᵏv₁ ≤ a ≤ b ≤ Tᵏv₂` | `iterate_le_iterate_of_monotoneOn`, `knaster_tarski` |
| Ex 7.1.1, p. 214 | A continuum of fixed points when `v₁ ≠ v₂` | `exists_continuum_fixedPts` |
| Prop 7.1.2, p. 214 | Increasing concave `g` with `a < g(a)`, `g(b) ≤ b` around every point is globally stable on `(0, ∞)` | `exists_fixedPt_tendsto_of_concave`, `globallyStableOn_of_concave` |
| Ex 7.1.2, p. 216 | The Solow–Swan map satisfies Prop 7.1.2 | `solowSwan`, `globallyStableOn_solowSwan` |
| Ex 7.1.3, p. 216 | `a < g(a)` cannot be dropped | `not_globallyStableOn_id` |
| Ex 7.1.4, p. 216 | `sf(k) + (1 − δ)k` is globally stable under the Inada conditions | `globallyStableOn_solow_inada` |
| Ex 7.1.5, p. 216 | The Fajgelbaum et al. law of motion is globally stable | `fajgelbaum`, `concaveOn_inv_inv_add`, `globallyStableOn_fajgelbaum` |
| p. 216 | Convex and concave self-maps of `ℝ^X` | Mathlib's `ConvexOn`, `ConcaveOn` |
| Thm 7.1.3, p. 217 | Du: global stability under (i)–(iv) | `du_concave` (ii), `du_concave_of_lt` (i), `du_convex` (iv), `du_convex_of_lt` (iii), `exists_delta_of_lt`, `neg_mem_Icc_iff`, `globallyStableOn_of_reflect` |
| Ex 7.1.6, p. 217 | Composites of order-preserving concave maps are concave | `concaveOn_comp` |
| (7.1)–(7.2), p. 218 | `v = [h + (Av)^{1/θ}]^θ` on `V = (0, ∞)^X` | `posCone`, `convex_posCone`, `powG`, `powG_apply`, `Irreducible.exists_pos_row`, `mulVec_pos_of_row`, `Irreducible.of_pos_mul` |
| Ex 7.1.7, p. 218 | `F(t) = (h + t^{1/θ})^θ` is increasing, convex for `θ ∈ (0, 1]`, concave otherwise | `powF`, `powF_pos`, `powF_monotoneOn`, `hasDerivAt_powF`, `continuousOn_powF`, `differentiableOn_powF`, `convexOn_powF`, `concaveOn_powF` |
| Ex 7.1.8, p. 219 | `G` is an order-preserving self-map of `V`, convex or concave | `powG_mapsTo`, `powG_monotoneOn`, `convexOn_powG`, `concaveOn_powG` |
| Thm 7.1.4, p. 218 | `ρ(A)^{1/θ} < 1` iff `G` is globally stable on `V`; no fixed point otherwise | `specRad_rpow_lt_one_of_isFixedPt`, `not_isFixedPt_powG`, `scalar_bounds`, `powG_smul_eigen`, `exists_thresholds`, `globallyStableOn_powG_Icc`, `exists_interval`, `globallyStableOn_powG`, `globallyStableOn_powG_iff` |
| Ex 7.1.9, (7.3), p. 219 | A unique positive Markov solution of (7.3) iff `ρ(A)^ψ < 1` | `kleinmanA`, `IsKleinmanSol`, `isKleinmanSol_iff`, `existsUnique_kleinmanSol_iff` |

## §7.2 Recursive preferences (pp. 219–232)

| Book | Claim | Lean |
| --- | --- | --- |
| (7.5)–(7.6), p. 220 | Under `Vₜ = v(Xₜ)`, `v = r + βPv`, solved by `(I − βP)⁻¹r` | `timeAdditive_solution` |
| Ex 7.2.1, p. 220 | `v*(Xₜ)` obeys (7.5) | `timeAdditive_solution` (operator form) |
| §7.2.2.2, p. 223 | The entropic risk-adjusted expectation `E_θ` | `entExp`, `entR_eq_entExp` |
| Ex 7.2.2, p. 223 | `E_θ[ξ + c] = E_θ[ξ] + c` | `entExp_add_const` |
| Ex 7.2.3, (7.9), p. 223 | Gaussian `ξ`: `E_θ[ξ] = Eξ + θ Var ξ/2` | `entExp_gaussian` |
| Lemma 7.2.1, p. 224 | `E_θ ≤ E` for `θ < 0`, `≥` for `θ > 0`, strict iff `Var ξ > 0` | `exp_mean_le`, `mul_mean_le_log`, `entExp_le_mean`, `mean_le_entExp`, `entExp_ne_mean`, `entExp_eq_mean` |
| (7.8), (7.10), Prop 7.2.2, p. 224 | `K_θ` is globally stable for `β < 1` | `koopmans_additive_entR`, `globallyStable_riskSensitive` |
| Ex 7.2.4, (7.11), p. 225 | `v(x) = ax + b` solves the Gaussian AR(1) case | `integral_exp_add_mul_gaussian`, `riskSensitive_gaussian` |
| Ex 7.2.6, p. 225 | IID consumption: a one-dimensional equation and its solution | `riskSensitive_iid`, `riskSensitive_iid_unique` |
| (7.12)–(7.14), p. 227–228 | The Epstein–Zin Koopmans operator | `ezK`, `ezK_eq_koopmans`, `ezK_apply_ez` |
| Ex 7.2.7, p. 228 | `K` is a self-map of `V` | `ezK_mapsTo` |
| (7.15), Ex 7.2.8, p. 230 | `K̂v = (h + β(Pv)^{1/θ})^θ`; `v` fixed for `K` iff `v^γ` fixed for `K̂` | `powMap`, `powMap_ezK`, `powMap_inv`, `powMap_inv'` |
| Lemma 7.2.4, p. 230 | `Φv = v^γ` is a homeomorphism conjugating `K` and `K̂` | `powMap_mapsTo`, `continuousOn_powMap`, `powMap_ezK` |
| Prop 7.2.3, p. 228 | `P` irreducible and `h ≫ 0` give global stability | `globallyStableOn_ez` |
| Ex 7.2.9, p. 232 | `F'(t) → ∞` as `t ↓ 0` for the parameters of Figure 7.5 | `ez_deriv_tendsto_atTop` |

## §7.3 General representations (pp. 232–243)

| Book | Claim | Lean |
| --- | --- | --- |
| §7.3.1.1, p. 232 | Certainty equivalent operators | `IsCertEquiv` |
| Example 7.3.1, p. 232 | Conditional expectation is a certainty equivalent | `IsMarkov.isCertEquiv` |
| Ex 7.3.1, p. 233 | The linear certainty equivalents are exactly the Markov matrices | `isCertEquiv_mulVec_iff` |
| Example 7.3.2, Ex 7.3.2, p. 233 | The entropic certainty equivalent | `entR`, `isCertEquiv_entR`, `IsMarkov.mulVec_pos` |
| (7.16), Example 7.3.3, Ex 7.3.3, p. 233 | The Kreps–Porteus certainty equivalent | `kpR`, `kpR_pos`, `isCertEquiv_kpR` |
| Ex 7.3.4, p. 233 | The quantile certainty equivalent | `condCdf`, `quantR`, `isLeast_quantR`, `isCertEquiv_quantR` |
| Ex 7.3.5, p. 233 | `R0 = 0`, `Rv ≥ 0` for `v ≥ 0` | `IsCertEquiv.zero_and_nonneg` |
| Ex 7.3.6, p. 234 | Convex combinations of certainty equivalents | `IsCertEquiv.convex_comb` |
| §7.3.1.2, p. 234 | Positive homogeneity, super-/subadditivity, constant-subadditivity | `PosHomogeneous`, `Superadditive`, `Subadditive`, `ConstSubadditive` |
| Example 7.3.4, p. 234 | `R = P` has all three properties | `mulVec_properties` |
| Example 7.3.5, p. 234 | Kreps–Porteus: subadditive for `γ ≥ 1`, superadditive for `γ ≤ 1` | `posHomogeneous_kpR`, `sum_rpow_normalize`, `sum_rpow_add_le`, `le_sum_rpow_add`, `convexOn_rpow_of_neg`, `subadditive_kpR`, `superadditive_kpR`, `smul_mem_posCone` |
| Ex 7.3.7, p. 234 | The quantile operator is constant-subadditive | `quantR_add_const`, `constSubadditive_quantR` |
| Ex 7.3.8, p. 234 | The entropic operator is constant-subadditive | `entR_add_const`, `constSubadditive_entR` |
| Ex 7.3.9, p. 234 | Constant-subadditive implies nonexpansive | `nonexpansive_of_constSubadditive` |
| Example 7.3.6, (7.17), Ex 7.3.10, p. 235 | The entropic operator is concave for `θ < 0` | `log_sum_exp_le`, `concaveOn_entR` |
| Ex 7.3.11, p. 235 | Subadditive and homogeneous implies convex; superadditive implies concave | `convexOn_of_subadditive`, `concaveOn_of_superadditive` |
| Lemma 7.3.1, p. 235 | `R_γ` convex for `γ ≥ 1`, concave for `γ ≤ 1` | `convexOn_kpR`, `concaveOn_kpR` |
| §7.3.1.3, Ex 7.3.12–7.3.13, pp. 235–236 | Monotone increasing entropic and Kreps–Porteus operators | `MonotoneKernel`, `MonotoneKernel.antitone`, `monotone_entR`, `monotone_kpR` |
| §7.3.1.4, p. 236 | Aggregators: Leontief, Uzawa, CES, additive, CES–Uzawa | `IsAggregator`, `leontief`, `uzawa`, `cesAgg`, `additive`, `cesUzawa`, `additive_eq_uzawa`, `additive_eq_cesAgg`, `isAggregator_leontief`, `isAggregator_uzawa`, `isAggregator_additive`, `isAggregator_cesUzawa`, `isAggregator_cesAgg` |
| (7.18), p. 236 | Koopmans operators are order-preserving self-maps | `koopmans`, `koopmans_mapsTo_monotoneOn` |
| Examples 7.3.7–7.3.8, Remark 7.3.1, p. 237 | Risk-sensitive, Epstein–Zin and time additive operators as `A ∘ R` | `koopmans_additive_entR`, `koopmans_cesAgg_kpR`, `koopmans_additive_mulVec`, `ezK_eq_koopmans` |
| Ex 7.3.14, p. 237 | EIS `= 1/(1 − α)` for the CES aggregator | `ces_eis` |
| Example 7.3.9, Ex 7.3.15, p. 238 | Time additive lifetime value and finite-horizon convergence | `iterate_additive_eq`, `additive_lifetimeValue` |
| Example 7.3.10, p. 238 | Risk-sensitive lifetime value | `globallyStable_riskSensitive` |
| Lemma 7.3.2, p. 239 | Increasing lifetime values | `monotone_of_globallyStableOn`, `monotone_koopmans_fixedPt` |
| Ex 7.3.16, p. 239 | Epstein–Zin lifetime utility is increasing | `monotone_ez_lifetimeValue` |
| (7.19), Ex 7.3.17, p. 240 | Blackwell aggregators; additive and Leontief | `IsBlackwellAgg`, `isBlackwellAgg_additive`, `isBlackwellAgg_leontief` |
| Prop 7.3.3, p. 240 | Blackwell aggregator and constant-subadditive `R` give a contraction | `isContractionOn_koopmans`, `globallyStable_koopmans` |
| Ex 7.3.18, p. 240 | `A_MIN ∘ R` is globally stable | `globallyStable_leontief` |
| (7.20), §7.3.2.3, Ex 7.3.19, p. 241 | Quantile preferences | `globallyStable_quantile`, `globallyStable_leontief_quantile` |
| (7.21)–(7.22), §7.3.3.1, pp. 241–242 | Uzawa aggregation with conditional expectations | `koopmans_uzawa_mulVec`, `uzawa_lifetimeValue`, `uzawa_no_pos_fixedPt` |
| Ex 7.3.20, p. 242 | `L = bP` is irreducible | `irreducible_uzawa` |
| Prop 7.3.4, p. 242 | Stability via concavity on `[0, v̄]` | `nonnegCone`, `globallyStableOn_uzawa_concave` |
| (7.23)–(7.24), Ex 7.3.21–7.3.22, Prop 7.3.5, p. 243 | Epstein–Zin with state-dependent discounting: stable iff `ρ(B)^{α/γ} < 1` | `ezK`, `ezK_mapsTo`, `ezB`, `powMap_ezK`, `irreducible_ezB`, `globallyStableOn_ezK_iff` |
