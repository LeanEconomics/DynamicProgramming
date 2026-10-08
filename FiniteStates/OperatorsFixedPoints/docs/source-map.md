# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 2, "Operators and Fixed Points" (pp. 42–80). Result, equation and
exercise numbers are the book's; page numbers are book pages. Lean names are
relative to `SargentStachurski.OperatorsFixedPoints`. Where the Lean statement
adds a hypothesis the book leaves implicit, or departs from the printed claim,
see [corrections](corrections.md).

## Chapter 1 facts restated (Basics, SpectralRadius)

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, p. 22 | Global stability | `GloballyStable`, `globallyStable_of_tendsto`, `GloballyStable.tendsto_iterate`, `GloballyStable.exists_fixedPt`, `GloballyStable.fixedPt_unique` |
| Vol. 1, (1.17), Ex 1.2.19 | Contraction on `U`; at most one fixed point | `IsContractionOn`, `IsContractionOn.fixedPt_unique` |
| Vol. 1, (1.18), Thm 1.2.3 | Rate, convergence, existence (via Mathlib's `ContractingWith`), global stability | `IsContractionOn.norm_iterate_sub_fixedPt_le`, `IsContractionOn.tendsto_iterate_fixedPt`, `IsContractionOn.exists_fixedPt`, `IsContractionOn.globallyStable`, `IsContractionOn.globallyStable_univ` |
| Vol. 1, (1.15), Lemma 1.2.2 | Spectral radius; eigenvalues; Gelfand's formula; `‖Aᵏ‖ ≤ rᵏ` eventually | `complexify`, `specRad`, `mem_spectrum_iff_eigenpair`, `tendsto_norm_pow_rpow`, `eventually_norm_pow_le`, `eventually_abs_entry_pow_le` |
| Vol. 1, Thm 1.2.1 | Neumann series | `tendsto_norm_pow_zero`, `summable_pow`, `one_sub_mul_tsum`, `tsum_mul_one_sub`, `neumann_series` |
| — | `ρ(Aᵀ) = ρ(A)`; `ρ(A) ≤ ‖A‖`; eigenvalues bounded by `ρ(A)`; `‖A‖ = c = ρ(A)` for `A ≥ 0` with constant row (column) sums | `specRad_transpose`, `specRad_le_norm`, `norm_le_specRad_of_mem_spectrum`, `norm_eq_of_rowsum_eq`, `specRad_eq_of_rowsum_eq`, `specRad_eq_of_colsum_eq` |

## §2.1.1 Conjugate maps (pp. 42–44)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 43 | Conjugacy `T = Φ⁻¹ ∘ T̂ ∘ Φ`; commuting square | `IsConjugate`, `IsConjugate.comm`, `IsConjugate.of_comm`, `IsConjugate.iterate_comm` |
| p. 43 | Conjugacy is symmetric, transitive, reflexive | `IsConjugate.symm`, `IsConjugate.trans`, `IsConjugate.refl` |
| Example 2.1.1, p. 43 | `A = P⁻¹DP` makes `u ↦ Au` conjugate to `v ↦ Dv` | `isConjugate_similar` |
| Ex 2.1.1, p. 43 | `u ∈ fix(T) ↔ Φu ∈ fix(T̂)` | `IsConjugate.isFixedPt_iff` |
| Ex 2.1.2, p. 43 | `Φ` is a bijection `fix(T) → fix(T̂)` | `IsConjugate.fixedPointsEquiv` |
| Prop 2.1.1, p. 44 | (ii) `v ∈ fix(T̂) ↔ Φ⁻¹v ∈ fix(T)`; (iii) same cardinality; unique fixed point iff | `IsConjugate.isFixedPt_symm_iff`, `IsConjugate.cardinal_fixedPoints_eq`, `IsConjugate.existsUnique_fixedPt_iff` |
| Example 2.1.2, p. 44 | `ln : (0, ∞) → ℝ` is a homeomorphism | `logHomeomorph`, `logHomeomorph_apply`, `logHomeomorph_symm_apply` |
| Example 2.1.3, p. 44 | `u ↦ Φu` is a homeomorphism of `ℝⁿ` iff `Φ` is nonsingular | `matrixHomeomorph`, `det_ne_zero_of_mulVec_injective` |
| p. 44 | Topological conjugacy | `IsTopConjugate` |
| Ex 2.1.3, p. 44 | `Auᵅ` on `(0, ∞)` is conjugate to `ln A + αv` under `ln` | `isTopConjugate_power` |
| Ex 2.1.4, p. 44 | `Tᵏu → u*` iff `T̂ᵏΦu → Φu*` | `IsTopConjugate.tendsto_iterate_iff` |
| Ex 2.1.5, p. 44 | Topological conjugacy is an equivalence relation | `IsTopConjugate.refl`, `IsTopConjugate.symm`, `IsTopConjugate.trans` |
| Prop 2.1.2, p. 45 | `T` globally stable iff `T̂` is; `û* = Φu*` | `IsTopConjugate.globallyStable_iff`, `IsTopConjugate.fixedPt_map` |

## §2.1.2 Local stability (pp. 45–46)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 45 | Local stability | `LocallyStable`, `GloballyStable.locallyStable` |
| Ex 2.1.6, p. 45 | Local stability is preserved by topological conjugacy | `IsTopConjugate.locallyStable_iff` |
| Example 2.1.4, p. 45 | `g(x) = x²`: `0` locally stable, `1` not | `iterate_sq`, `locallyStable_sq_zero`, `not_locallyStable_sq_one` |
| p. 45 | `|g'(x*)| < 1` implies local stability (one dimension) | `locallyStable_of_abs_deriv_lt_one` |

## §2.1.3 Rates of convergence and §2.1.4 Newton's method (pp. 46–51)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 46 | Rate at least `q`; linear; quadratic | `ConvergesAtRateAtLeast`, `ConvergesLinearly`, `ConvergesQuadratically` |
| Example 2.1.5, p. 46 | Contraction orbits converge at least linearly | `IsContractionOn.convergesAtRateAtLeast`, `IsContractionOn.convergesLinearly` |
| Ex 2.1.7, p. 47 | `eₖ₊₁/eₖ → |T'(u*)|`; linear when `0 < |T'(u*)| < 1` | `error_ratio_near`, `tendsto_error_ratio`, `convergesLinearly_of_abs_deriv_lt_one` |
| (2.2), pp. 47–48 | Newton map `Qu = (Tu − T'(u)u)/(1 − T'(u))` as the fixed point of the linearisation | `newtonMap`, `newtonMap_fixedPt_linearisation` |
| p. 48 | `fix(Q) = fix(T)` where `T'(u) ≠ 1` | `isFixedPt_newtonMap_iff` |

## §2.2.1 Partial orders (pp. 51–55)

| Book | Claim | Lean |
| --- | --- | --- |
| Example 2.2.1, p. 51 | `≤` on `ℝ` is a partial order | `real_le_isPartialOrder`, `real_le_antisymm` |
| Ex 2.2.1, p. 51 | Equality is a partial order | `eq_isPartialOrder` |
| Ex 2.2.2, p. 51 | Inclusion is a partial order on `℘(M)` | `subset_isPartialOrder` |
| Example 2.2.2, Ex 2.2.3, p. 52 | Pointwise order on `ℝ^X` is a partial order | `pointwise_isPartialOrder`, `pointwise_le_def` |
| p. 52, Ex 2.2.4 | `u ≪ v`; not a partial order | `StrictLt`, `not_strictLt_refl`, `strictLt_not_isPartialOrder` |
| Ex 2.2.5, p. 52 | Limits preserve `a ≤ uₖ ≤ b` | `le_of_tendsto_pi` |
| Example 2.2.3, Ex 2.2.6, pp. 52–53 | Matrices as functions on `[n] × [k]` | `matrix_le_iff_uncurry` |
| Ex 2.2.7, p. 53 | (i) `|Bu| ≤ B|u|`; (ii) `uₖ₊₁ ≤ Auₖ ⇒ uₖ ≤ Aᵏu₀` | `mulVec_le_mulVec`, `abs_mulVec_le`, `le_pow_mulVec_of_le` |
| Ex 2.2.8, p. 53 | `A ≫ 0`, `u ≤ v`, `u ≠ v ⇒ Au ≪ Av` | `strictLt_mulVec` |
| Example 2.2.4, p. 53 | `ℝ`, `ℕ` are totally ordered | `real_le_total`, `nat_le_total` |
| Example 2.2.5, p. 53 | Pointwise order on `ℝ²` not total | `pointwise_not_total` |
| Ex 2.2.9, p. 53 | Inclusion on `℘({1, 2})` not total | `subset_not_total` |
| Ex 2.2.10, p. 54 | Greatest and least elements are unique | `isGreatest_unique`, `isLeast_unique` |
| Ex 2.2.11, p. 54 | `⋃ Aᵢ` greatest iff it is some `Aᵢ` | `isGreatest_iUnion_iff` |
| Ex 2.2.12, p. 54 | Bounded subsets of `ℝⁿ` have no greatest element | `not_exists_isGreatest_bounded` |
| Ex 2.2.13, p. 54 | Suprema are unique | `isLUB_unique` |
| Ex 2.2.14, p. 55 | Supremum in `A` is greatest; greatest is supremum | `isGreatest_of_isLUB_mem`, `IsGreatest.isLUB'` |
| Ex 2.2.15, p. 55 | Least element is the infimum | `IsLeast.isGLB'` |
| Ex 2.2.16, p. 55 | `⋁ Aᵢ = ⋃ Aᵢ`, `⋀ Aᵢ = ⋂ Aᵢ` in `℘(M)` | `isLUB_iUnion`, `isGLB_iInter` |
| Ex 2.2.17, p. 55 | A subset of a totally ordered set with no supremum | `not_exists_isLUB_Ioo` |

## §2.2.2 The pointwise order on `ℝ^X` (pp. 55–59)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 56, Ex 2.2.18 | `u ∧ v`, `u ∨ v` are the infimum and supremum of `{u, v}` | `isGLB_pair_pointwise`, `isLUB_pair_pointwise` |
| p. 56, Example 2.2.6 | Sublattices; `{f ≥ 0}`, `{f ≫ 0}`, `{|f| ≤ 1}` | `IsSublattice`, `isSublattice_nonneg`, `isSublattice_pos`, `isSublattice_abs_le_one` |
| Ex 2.2.19, p. 56 | Finite suprema and infima are pointwise | `sup'_apply_pointwise`, `inf'_apply_pointwise`, `isLUB_sup'_image`, `isGLB_inf'_image` |
| Ex 2.2.20, p. 56 | Sublattices contain finite suprema and infima | `IsSublattice.sup'_mem`, `IsSublattice.inf'_mem` |
| Example 2.2.7, Ex 2.2.21, p. 57 | Greatest element of a finite family iff the pointwise max belongs to it | `isGreatest_of_sup'_mem`, `not_exists_isGreatest_of_sup'_notMem` |
| Ex 2.2.22, p. 57 | `[a₁, a₂] ∩ [b₁, b₂] = [a₁ ∨ b₁, a₂ ∧ b₂]` in a sublattice | `Icc_inter_Icc_sublattice` |
| Lemma 2.2.1, p. 58 | (i) `|f + g| ≤ |f| + |g|`; (ii) `(f ∧ g) + h`, `(f ∨ g) + h`; (iii) distributivity; (iv) `|f ∧ h − g ∧ h| ≤ |f − g|`; (v) `|f ∨ h − g ∨ h| ≤ |f − g|` | `abs_add_le_pointwise`, `inf_add_pointwise`, `sup_add_pointwise`, `sup_inf_pointwise`, `inf_sup_pointwise`, `abs_inf_sub_inf_le_pointwise`, `abs_sup_sub_sup_le_pointwise` |
| (2.3), p. 58 | `(f + g) ∧ h ≤ f ∧ h + g ∧ h` on `ℝ^X₊` | `min_add_le_min_add_min`, `inf_add_le_pointwise` |
| Ex 2.2.23, p. 58 | `|a ∧ c − b ∧ c| ≤ |a − b| ∧ c` | `abs_min_sub_min_le_min` |
| Lemma 2.2.2, p. 58 | `|max f − max g| ≤ max |f − g|` | `abs_sup'_sub_sup'_le` |
| Ex 2.2.24, p. 59 | `|min f − min g| ≤ max |f − g|` | `abs_inf'_sub_inf'_le` |
| p. 59, Lemma 2.2.3 | Upper envelope of self-maps; of contractions is a contraction | `upperEnvelope`, `upperEnvelope_mapsTo`, `isContractionOn_upperEnvelope` |

## §2.2.3 Order-preserving maps (pp. 59–62)

| Book | Claim | Lean |
| --- | --- | --- |
| Example 2.2.8, p. 60 | `u ↦ Au + b` order preserving for `A ≥ 0` | `monotone_affine_of_nonneg` |
| Example 2.2.9, p. 60 | Integration is order preserving | `integral_mono_of_le` |
| Ex 2.2.25, p. 60 | `F(⋁ uᵢ) = ⋁ Fuᵢ`, `F(⋀ uᵢ) = ⋀ Fuᵢ` for a greatest/least element | `isLUB_image_of_isGreatest`, `isGLB_image_of_isLeast` |
| Ex 2.2.26, p. 60 | Powers of order-preserving maps are order preserving | `monotone_iterate` |
| Ex 2.2.27, p. 60 | `u ↦ Au` order preserving for `A ≥ 0` | `monotone_mulVec_of_nonneg` |
| Ex 2.2.28, p. 60 | `0 ≤ A ≤ B ⇒ Aᵏ ≤ Bᵏ` and `ρ(A) ≤ ρ(B)` | `mul_le_mul_of_nonneg`, `pow_nonneg_entries`, `pow_le_pow_entries`; `specRad_le_of_le` (in `SpectralRadius`) |
| p. 61, Example 2.2.10 | Increasing functions `iℝ^P`; `2x`, `1{2 ≤ x}` increasing; `−x`, `1{x ≤ 2}` not | `increasingFns`, `monotone_two_mul`, `monotone_indicator_ge`, `not_monotone_neg`, `not_monotone_indicator_le` |
| Ex 2.2.29, p. 61 | `αf + βg`, `f ∨ g`, `f ∧ g` increasing | `monotone_smul_add`, `monotone_sup_inf` |
| Ex 2.2.30, p. 61 | `iℝ^P` is closed | `isClosed_increasingFns` |
| Ex 2.2.31, p. 61 | `h ↦ E h(X)` is increasing | `monotone_expectation` |
| Ex 2.2.32, p. 61 | Increasing nonnegative `u` on `{0, …, n − 1}` is a nonnegative combination of upper indicators | `exists_indicator_decomposition` |
| Lemma 2.2.4, p. 62 | Blackwell's condition | `isContractionOn_of_blackwell` |

## §2.2.4 Stochastic dominance (pp. 62–64)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.9), p. 62 | `φ ≼_F ψ` | `IsDistribution`, `FOSD` |
| Example 2.2.11, p. 63 | `X ≤ Y` pointwise implies the law of `Y` dominates the law of `X` | `law`, `law_isDistribution`, `sum_mul_law`, `fosd_law_of_le` |
| Ex 2.2.33, p. 64 | On `{1, 2}`: `φ ≼_F ψ ↔ ψ(1) ≤ φ(1) ↔ φ(2) ≤ ψ(2)` | `fosd_fin_two_iff` |
| Ex 2.2.34, p. 64 | `≼_F` is transitive | `fosd_trans` |
| p. 64, Lemma 2.2.5 | Counter-CDF `G_φ`; (i) `φ ≼_F ψ ⇒ G_φ ≤ G_ψ`; (ii) converse on a totally ordered set | `ccdf`, `monotone_upper_indicator`, `sum_upper_indicator_mul`, `ccdf_le_of_fosd`, `sum_mul_nonneg_of_tails_nonneg`, `ccdf_sub`, `ccdf_reindex`, `fosd_of_ccdf_le` |
| Lemma 2.2.6, p. 64 | `≼_F` is a partial order | `fosd_refl`, `eq_of_ccdf_eq`, `fosd_antisymm` |
| Ex 2.2.35, p. 64 | `φ ≼_F ψ ⇒ Q_τ(X) ≤ Q_τ(Y)` | `cdf`, `cdf_le_of_fosd`, `quantileSet`, `quantile`, `quantile_le_of_fosd` |

## §2.2.5 Parametric monotonicity (pp. 64–68)

| Book | Claim | Lean |
| --- | --- | --- |
| Example 2.2.12, p. 65 | `Bu + b` dominates `Au + b` for `0 ≤ A ≤ B` on `ℝⁿ₊` | `affine_dominates` |
| Ex 2.2.36, p. 65 | `S ≤ T` order preserving `⇒ Sᵏ ≤ Tᵏ` | `iterate_le_iterate` |
| Ex 2.2.37, p. 65 | Dominance is a partial order | `dominance_isPartialOrder` |
| Prop 2.2.7, p. 67 | `S ≤ T`, `T` order preserving and globally stable `⇒ u_S ≤ u_T` | `fixedPt_le_of_dominates` |
| Ex 2.2.38, p. 67 | Solow–Swan `k*` increasing in `s`, `A`, decreasing in `δ` | `solowMap`, `solowMap_monotone`, `solowMap_le`, `solow_fixedPt_le` |
| Ex 2.2.39, p. 67 | Continuation value `h*` increasing in `β` | `contMap`, `contMap_monotone`, `contMap_isContractionOn`, `contMap_le`, `contMap_fixedPt_le` |

## §2.3.1 Nonnegative matrices (pp. 69–71)

| Book | Claim | Lean |
| --- | --- | --- |
| Thm 2.3.1, p. 69 | Perron–Frobenius for `A ≥ 0`: `ρ(A)` is an eigenvalue with right eigenvector `e ≥ 0`, `e ≠ 0` | `perron_frobenius` |
| Thm 2.3.1, p. 69 | Left eigenvector `ε ≥ 0`, `ε ≠ 0` | `perron_frobenius_left` |
| proof | Maximal-modulus eigenvalue exists; real resolvent is a two-sided inverse; dominates the complex resolvent; bounded resolvent would exclude `μ` from the spectrum; hence unbounded; the simplex is compact | `exists_mem_spectrum_norm_eq`, `eventually_norm_entry_pow_complexify_le`, `smul_one_sub_mul_res_real`, `norm_res_complexify_le`, `norm_le_card_mul_of_entry_norm_le`, `notMem_spectrum_of_res_bounded`, `exists_res_entry_gt`, `isCompact_simplex` |
| proof | Resolvent series entrywise (Vol. 1, Thm 1.2.1 at the level of entries) | `resPartial`, `res`, `res_apply`, `smul_one_sub_mul_resPartial`, `resPartial_mul_smul_one_sub`, `resPartial_apply`, `summable_res_entry`, `tendsto_resPartial_apply`, `tendsto_inv_pow_mul_apply`, `smul_one_sub_mul_res`, `res_mul_smul_one_sub`, `res_nonneg`, `inv_le_res_diag` |
| Lemma 2.3.2, Ex 2.3.1, p. 70 | `ρ(A)` between the smallest and largest row sums and column sums | `le_specRad_of_colsum_ge`, `specRad_le_of_colsum_le`, `le_specRad_of_rowsum_ge`, `specRad_le_of_rowsum_le` |
| Lemma 2.3.3, p. 70 | `‖Aᵏh‖^{1/k} → ρ(A)` for `h ≫ 0` | `tendsto_rpow_one_div_natCast`, `norm_pow_mul_le_norm_mulVec`, `tendsto_norm_pow_mulVec_rpow` |
| p. 71, Ex 2.3.2 | Markov matrices; (i) products; powers; (ii) `ρ(P) = 1`; (iii) stationary distribution exists | `IsMarkov`, `IsMarkov.mul`, `IsMarkov.pow`, `IsMarkov.specRad_eq_one`, `IsMarkov.exists_stationary` |
| Ex 2.3.3, p. 71 | No `h` with `Ph ≥ h + ε` | `IsMarkov.not_mulVec_ge_add` |

## §2.3.2 The lake model (pp. 71–75)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.13), p. 72 | The matrix `A`; `A ≥ 0` | `LakeModel`, `LakeModel.A`, `LakeModel.A_nonneg` |
| Ex 2.3.4, p. 73 | `nₜ₊₁ = (1 + g)nₜ` with `g = b − d` | `LakeModel.g`, `LakeModel.sum_mulVec` |
| Ex 2.3.5, p. 73 | `ρ(A) = 1 + g` | `LakeModel.colsum`, `LakeModel.specRad_A` |
| Ex 2.3.6, p. 73 | `1ᵀ` is a left eigenvector | `LakeModel.one_vecMul` |
| Ex 2.3.7, (2.14), pp. 73–74 | `x̄ = (ū, ē)` is the right eigenvector with `1ᵀx̄ = 1`, uniquely | `LakeModel.ubar`, `LakeModel.xbar`, `LakeModel.xbar_sum`, `LakeModel.A_mulVec_xbar`, `LakeModel.eq_xbar_of_eigen` |

## §2.3.3 Linear operators (pp. 75–80)

| Book | Claim | Lean |
| --- | --- | --- |
| (2.15), Thm 2.3.4, p. 76 | Matrices act linearly; every linear operator on `ℝⁿ` is a matrix | `mulVec_linear`, `exists_matrix_of_linear` |
| Lemma 2.3.5, p. 77 | Matrices ↔ linear operators ↔ functions on `X × X` | `matrixLinearEquiv`, `matrixLinearEquiv_apply`, `matrixFunEquiv` |
| (2.16), Ex 2.3.8, p. 77 | Kernel operator `(Lu)(x) = ∑ L(x, x')u(x')` is linear | `kernelOp`, `kernelOp_eq_mulVec`, `kernelOp_linear` |
| (2.17), Ex 2.3.9, p. 78 | Product-space operator is linear | `productOp`, `productOp_linear` |
| (2.18), p. 79 | Positive operators | `IsPositiveOp` |
| Example 2.3.1, p. 79 | Product-space operator positive when `Q ≥ 0` | `isPositiveOp_productOp` |
| Lemma 2.3.6, Ex 2.3.10, p. 79 | `u ↦ Au` positive iff `A ≥ 0` | `isPositiveOp_mulVec_iff` |
| Ex 2.3.11, p. 79 | Positive iff order preserving | `isPositiveOp_iff_monotone` |
| p. 79, Ex 2.3.12, p. 80 | Markov operators; `u ↦ Pu` Markov iff `P` is a Markov matrix | `IsMarkovOp`, `isMarkovOp_mulVec_iff` |
| Ex 2.3.13, p. 80 | Markov matrices map `h ≫ 0` to `Ph ≫ 0` | `mulVec_pos_of_markov` |
| (2.19), Ex 2.3.14, p. 80 | `φ ↦ φP`; Markov iff it preserves distributions | `vecMulOp`, `vecMulOp_eq_vecMul`, `isMarkovOp_iff_vecMulOp_distribution` |
