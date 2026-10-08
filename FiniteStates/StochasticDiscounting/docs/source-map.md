# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 6, "Stochastic Discounting" (pp. 182–212), together with the parts of
Theorem 2.3.1 (p. 69) deferred from the Chapter 2 project. Result, equation and
exercise numbers are the book's; page numbers are book pages. Lean names are
relative to `SargentStachurski.StochasticDiscounting`. Where the Lean statement
adds a hypothesis the book leaves implicit, or departs from the printed claim,
see [corrections](corrections.md).

## Earlier-chapter facts restated on a general finite type

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, p. 71, Ex 2.3.2, (3.12), Ex 3.2.1 | Markov matrices, products, powers, `(Ph)(x)`, order preservation, `P𝟙 = 𝟙`, `|Ph| ≤ ‖h‖` | `IsMarkov`, `IsMarkov.mul`, `IsMarkov.pow`, `IsDistribution`, `mulVec_apply_eq`, `IsMarkov.mulVec_le_mulVec`, `IsMarkov.mulVec_const`, `IsMarkov.abs_mulVec_le`, `IsMarkov.norm_mulVec_le`, `IsMarkov.abs_mulVec_sub_le` |
| Vol. 1, (1.17), Thm 1.2.3, Prop 2.2.7, Lemma 2.2.4, Lemma 2.2.2 | Contractions and Banach's theorem; ordered fixed points; Blackwell's condition; `|max f − max g| ≤ max|f − g|` | `GloballyStable`, `IsContractionOn`, `IsContractionOn.fixedPt_unique`, `IsContractionOn.norm_iterate_sub_fixedPt_le`, `IsContractionOn.tendsto_iterate_fixedPt`, `IsContractionOn.exists_fixedPt`, `IsContractionOn.globallyStable_univ`, `fixedPt_le_of_le`, `le_fixedPt_of_le_apply`, `fixedPt_le_of_apply_le`, `isContractionOn_of_blackwell`, `abs_sup'_sub_sup'_le` |
| Vol. 1, (1.15), Lemma 1.2.2, Thm 1.2.1, Ex 2.2.28 | The spectral radius, Gelfand's formula, `‖Aᵏ‖ → 0`, the Neumann series, `ρ(Aᵀ) = ρ(A)`, `0 ≤ A ≤ B ⇒ Aᵏ ≤ Bᵏ, ρ(A) ≤ ρ(B)`, `ρ(A) ≤ ‖A‖`, row-sum characterisations | `complexify`, `specRad`, `tendsto_norm_pow_rpow`, `eventually_norm_pow_le`, `tendsto_norm_pow_zero`, `summable_pow`, `neumann_series`, `specRad_transpose`, `pow_nonneg_entries`, `pow_le_pow_entries`, `specRad_le_of_le`, `specRad_le_norm`, `norm_le_specRad_of_mem_spectrum`, `specRad_eq_of_rowsum_eq`, `specRad_eq_of_colsum_eq`, `norm_eq_of_rowsum_eq`, `norm_le_of_rowsum_abs_le`, `rowsum_abs_le_norm`, `abs_entry_le_norm`, `eventually_abs_entry_pow_le` |
| Vol. 1, Thm 2.3.1, p. 69, nonnegative case | `ρ(A)` is an eigenvalue with nonnegative nonzero right and left eigenvectors | `res`, `smul_one_sub_mul_res`, `res_mul_smul_one_sub`, `exists_mem_spectrum_norm_eq`, `notMem_spectrum_of_res_bounded`, `exists_res_entry_gt`, `isCompact_simplex`, `perron_frobenius`, `perron_frobenius_left` |
| Vol. 1, Lemma 2.3.2, Lemma 2.3.3, Ex 2.3.2 (ii)–(iii), Ex 2.3.3 | Row- and column-sum bounds on `ρ(A)`; the local spectral radius `‖Aᵏh‖^{1/k} → ρ(A)` for `h ≫ 0`; `ρ(P) = 1`; a stationary distribution exists; no `h` with `Ph ≥ h + ε` | `le_specRad_of_colsum_ge`, `specRad_le_of_colsum_le`, `le_specRad_of_rowsum_ge`, `specRad_le_of_rowsum_le`, `norm_pow_mul_le_norm_mulVec`, `tendsto_norm_pow_mulVec_rpow`, `IsMarkov.specRad_eq_one`, `IsMarkov.exists_stationary`, `IsMarkov.not_mulVec_ge_add` |

## Theorem 2.3.1, the deferred parts (p. 69)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 69 | Irreducibility: `∑_{k≥1} Aᵏ ≫ 0` | `Irreducible`, `irreducible_of_pos`, `Irreducible.transpose` |
| Thm 2.3.1, irreducible | A nonnegative nonzero eigenvector is everywhere positive with positive eigenvalue; `ρ(A) > 0`; the right and left eigenvectors are everywhere positive | `pow_mulVec_eq_of_mulVec_eq`, `Irreducible.pos_of_mulVec_eq_smul`, `Irreducible.specRad_pos`, `Irreducible.exists_pos_eigenvector`, `Irreducible.exists_pos_left_eigenvector` |
| Thm 2.3.1, irreducible, uniqueness | `ρ(A)` is the only eigenvalue with a nonnegative eigenvector; nonnegative eigenvectors for `ρ(A)` are proportional | `Irreducible.eq_specRad_of_mulVec_eq_smul`, `Irreducible.exists_eq_smul_of_mulVec_eq_smul` |
| Ex 2.3.2 (iv), p. 71 | An irreducible Markov matrix has a unique stationary distribution, everywhere positive | `IsMarkov.exists_unique_stationary_of_irreducible` |
| Vol. 1, Ex 3.1.7, p. 89 | Dobrushin's estimate; for a Markov `P ≫ 0`, `ψPᵗ → ψ*` for every distribution, `ψ*` the unique stationary distribution; rows of `Pᵗ` converge to `ψ* ≫ 0` | `l1`, `norm_le_l1`, `l1_vecMul_le`, `l1_vecMul_pow_le`, `IsMarkov.tendsto_vecMul_pow_of_pos`, `IsMarkov.tendsto_pow_apply_of_pos` |
| Thm 2.3.1, (2.11) | For `A ≫ 0`, with `⟨ε, e⟩ = 1`, `ρ(A)⁻ᵗAᵗ → eεᵀ` | `conjMarkov`, `isMarkov_conjMarkov`, `conjMarkov_pow_apply`, `tendsto_pow_of_pos` |

## §6.1.1 Valuation (pp. 182–186)

| Book | Claim | Lean |
| --- | --- | --- |
| (6.2), (6.4), p. 184–185 | The discount factor process and the discount operator `L(x, x') = b(x, x')P(x, x')` | `discountOp`, `discountOp_apply`, `discountOp_nonneg` |
| (6.6)–(6.7), p. 185 | `E_x[β₁⋯βₜ h(Xₜ)] = (Lᵗh)(x)`, in operator form the recursion `Lᵗ⁺¹h = Lᵗ(Lh)` | `pow_succ_mulVec` |
| Thm 6.1.1, (6.5), p. 185 | If `ρ(L) < 1`, `v = ∑ₜ Lᵗh` is finite and equals `(I − L)⁻¹h`, the unique solution of `v = h + Lv` | `summable_pow_apply`, `summable_pow_mulVec`, `mulVec_tsum_pow_mulVec`, `tsum_pow_mulVec_eq`, `eq_of_eq_add_mulVec`, `inv_mulVec_eq_add`, `inv_mulVec_eq_tsum`, `eq_add_mulVec_iff`, `discountOp_value` |
| p. 185 | With `b ≡ β ∈ (0, 1)`, `L = βP`, `ρ(L) = β < 1`: Lemma 3.2.1 | `discountOp_const`, `specRad_smul_isMarkov`, `specRad_discountOp_const_lt_one` |
| Ex 6.1.1, (6.9), p. 186 | Firm valuation with `rₜ = r(Xₜ)`: finite when `ρ(L) < 1`, computed as `(I − L)⁻¹π` | `firmDiscountOp`, `firmValue_eq`, `firmDiscountOp_mulVec` |
| Ex 6.1.2, p. 186 | `v` is increasing when `P` is monotone, `π` increasing (and nonnegative), `r` decreasing | `MonotoneKernel`, `monotone_firmValue` |

## §6.1.2 Testing the spectral radius condition (pp. 186–189)

| Book | Claim | Lean |
| --- | --- | --- |
| Lemma 6.1.2, (6.10), p. 186 | `ρ(L) = lim ℓₜ^{1/t}` with `ℓₜ = max_x E_x[β₁⋯βₜ] = ‖Lᵗ𝟙‖_∞` | `pow_mulVec_one_nonneg`, `sup'_pow_mulVec_one_eq_norm`, `tendsto_sup'_pow_mulVec_one_rpow`, `tendsto_norm_pow_mulVec_rpow'` |
| Lemma 6.1.2, p. 187 | `ρ(L) < 1` iff `ℓₜ < 1` for some `t` | `norm_pow_eq_norm_pow_mulVec_one`, `specRad_le_norm_pow_rpow`, `specRad_lt_one_iff_exists_norm_pow_mulVec_one_lt` |
| Ex 6.1.3, (6.11), p. 187 | For irreducible `P` with stationary `ψ*`, `ρ(L) = lim (E_{ψ*}[β₁⋯βₜ])^{1/t}` | `tendsto_dotProduct_pow_mulVec_one_rpow` |
| Lemma 6.1.3, p. 188 | On `X = Y × Z` with `L = b(z, z')Q(z, z')R(y, y')`, `ρ(L) = ρ(L_Z)` | `productDiscountOp`, `productDiscountOp_mulVec_comp_snd`, `productDiscountOp_pow_mulVec_one`, `norm_comp_snd`, `specRad_productDiscountOp`, `specRad_productDiscountOp_isMarkov` |
| Lemma 6.1.4, p. 189 | For positive linear `L` and `h ≫ 0`: `ρ(L) < 1` iff `v = h + Lv` has a unique solution in `(0, ∞)^X` | `specRad_lt_one_iff_existsUnique_pos` |

## §6.1.3 Fixed-point results (pp. 189–192)

| Book | Claim | Lean |
| --- | --- | --- |
| Thm 6.1.5, Ex 6.1.4, p. 190 | An eventual contraction on a closed `U` is globally stable | `globallyStable_of_iterate_contraction`, `globallyStable_of_iterate_contraction_univ` |
| Example 6.1.2, p. 190 | `Tu = Au + b` with `ρ(A) < 1` is eventually contracting, globally stable, with fixed point `(I − A)⁻¹b` | `affineOp`, `affineOp_iterate_sub`, `exists_isContractionOn_iterate_affineOp`, `globallyStable_affineOp`, `isFixedPt_affineOp_inv` |
| Ex 6.1.5, p. 190 | If `Tᵏ` contracts under `‖·‖ₐ` then some `Tˡ` contracts under `‖·‖_b` | `exists_iterate_contraction_of_norm_equiv` |
| Prop 6.1.6, (6.13)–(6.14), p. 191 | `|Tv − Tw| ≤ L|v − w|` with `L ≥ 0`, `ρ(L) < 1` ⇒ `T` is eventually contracting | `mulVec_le_mulVec_of_nonneg`, `norm_abs_fun`, `norm_le_norm_of_abs_le_fun`, `abs_iterate_sub_le_pow_mulVec`, `exists_isContractionOn_iterate_of_abs_sub_le`, `globallyStable_of_abs_sub_le` |
| Prop 6.1.7, p. 191 | The generalised Blackwell condition `T(v + c) ≤ Tv + Lc` ⇒ (6.13) ⇒ eventually contracting | `abs_sub_le_of_blackwell`, `exists_isContractionOn_iterate_of_blackwell`, `globallyStable_of_blackwell` |

## §6.2.1 MDPs with state-dependent discounting (pp. 192–196)

| Book | Claim | Lean |
| --- | --- | --- |
| §6.2.1.1, (6.15), p. 192 | The model `(Γ, β, r, P)` with `β : G × X → ℝ₊`; the Bellman equation | `SDMDP`, `SDMDP.Feasible`, `SDMDP.IsFeasible`, `SDMDP.Policy`, `SDMDP.policy_nonempty`, `SDMDP.B`, `SDMDP.bellman_equation` |
| (6.16)–(6.17), p. 193 | `T_σ v = r_σ + L_σ v`, `L_σ(x, x') = β(x, σ(x), x')P(x, σ(x), x')`; `T_σ` is order preserving | `SDMDP.Pσ`, `SDMDP.isMarkov_Pσ`, `SDMDP.Lσ`, `SDMDP.Lσ_nonneg`, `SDMDP.Lσ_eq_discountOp`, `SDMDP.rσ`, `SDMDP.Tσ`, `SDMDP.Tσ_eq`, `SDMDP.B_mono`, `SDMDP.Tσ_monotone` |
| Assumption 6.2.1, p. 193 | `ρ(L_σ) < 1` for all `σ ∈ Σ` | `SDMDP.SpectralCondition` |
| p. 193 | `sup β < 1` implies Assumption 6.2.1 | `SDMDP.spectralCondition_of_le` |
| Lemma 6.2.1, (6.18), p. 193 | `I − L_σ` invertible; `T_σ` has the unique fixed point `v_σ = (I − L_σ)⁻¹r_σ` | `SDMDP.vσ`, `SDMDP.vσ_eq_inv`, `SDMDP.isUnit_one_sub_Lσ`, `SDMDP.isFixedPt_vσ`, `SDMDP.eq_vσ_of_isFixedPt`, `SDMDP.existsUnique_fixedPt_Tσ` |
| Ex 6.2.1, (6.19), p. 194 | `v_σ = E_x[∑ₜ β₁⋯βₜ r_σ(Xₜ)]`, in operator form `∑ₜ L_σᵗ r_σ`; finite-horizon values | `SDMDP.vσ_eq_tsum`, `SDMDP.iterate_Tσ_eq` |
| Ex 6.2.2, p. 194 | `T_σ` is globally stable on `ℝ^X` | `SDMDP.Tσ_eq_affineOp`, `SDMDP.globallyStable_Tσ`, `SDMDP.tendsto_iterate_Tσ` |
| Ex 6.2.3, (6.20), p. 194 | `βP ≤ L` on `G × X` with `ρ(L) < 1` implies Assumption 6.2.1 | `SDMDP.spectralCondition_of_dominated` |
| (6.21), p. 194 | The Bellman operator; `v`-greedy iff `T_σ v = Tv`; `v* = ⋁_σ v_σ`; optimal policies | `SDMDP.T`, `SDMDP.T_apply`, `SDMDP.B_le_T`, `SDMDP.Tσ_le_T`, `SDMDP.T_monotone`, `SDMDP.IsGreedy`, `SDMDP.greedy`, `SDMDP.isGreedy_greedy`, `SDMDP.greedyPolicy`, `SDMDP.isGreedy_iff_Tσ_eq_T`, `SDMDP.Tσ_eq_T_of_isGreedy`, `SDMDP.vstar`, `SDMDP.vσ_le_vstar`, `SDMDP.IsOptimal`, `SDMDP.isOptimal_iff` |
| Prop 6.2.2, pp. 194–195 | (i) `v*` the unique solution of the Bellman equation; (ii) optimal iff `v*`-greedy; (iii) an optimal policy exists | `SDMDP.vstar_le_T_vstar`, `SDMDP.vσ_eq_vstar_of_isGreedy`, `SDMDP.isFixedPt_T_vstar`, `SDMDP.eq_vstar_of_isFixedPt`, `SDMDP.isOptimal_iff_isGreedy`, `SDMDP.isOptimal_greedy_vstar`, `SDMDP.exists_isOptimal` |
| Algorithm 6.1, p. 195 | HPI: the update `(I − L_σ)⁻¹r_σ`, the improvement step `v_σ ≤ v_σ'`, termination gives an optimal policy | `SDMDP.hpi_update_eq_vσ`, `SDMDP.vσ_le_vσ_of_isGreedy`, `SDMDP.isOptimal_of_hpi_fixed` |
| §6.2.1.4, p. 195 | OPI with `m = 1` is VFI; `T_σᵐv → v_σ` | `SDMDP.opi_one_step_eq_vfi`, `SDMDP.tendsto_opi_inner` |
| §6.2.1.4, p. 195 | VFI converges (under (6.20); the book proves it in Chapter 8 under Assumption 6.2.1) | `SDMDP.abs_T_sub_le_of_dominated`, `SDMDP.globallyStable_T_of_dominated`, `SDMDP.tendsto_iterate_T_of_dominated` |
| §6.2.1.5, (6.22)–(6.23), pp. 195–196 | The exogenous discount model, its Bellman equation and greedy policies, as an MDP with `P = Q(z, z')R(y, a, y')` | `Exogenous`, `Exogenous.toSDMDP`, `Exogenous.bellman_equation`, `Exogenous.isOptimal_iff_isGreedy` |
| Prop 6.2.3, Ex 6.2.4, p. 196 | `ρ(L_Z) < 1` for `L_Z = β(z)Q(z, z')` gives all of Prop 6.2.2 | `Exogenous.LZ`, `Exogenous.Lσ_eq`, `Exogenous.specRad_Lσ`, `Exogenous.spectralCondition`, `Exogenous.eq_vstar_of_isFixedPt`, `Exogenous.exists_isOptimal` |
| §6.2.1.5 | Value function iteration converges in the exogenous discount model | `Exogenous.colMax`, `Exogenous.abs_T_sub_le`, `Exogenous.colMax_iterate_sub_le`, `Exogenous.norm_iterate_T_sub_le`, `Exogenous.exists_isContractionOn_iterate_T`, `Exogenous.globallyStable_T`, `Exogenous.tendsto_iterate_T` |

## §6.2.2 Inventory management revisited (pp. 197–199)

| Book | Claim | Lean |
| --- | --- | --- |
| (6.24), p. 198 | The inventory model of §5.2.1: update `f`, geometric demand `φ`, reward (5.8), kernel `R(y, a, y') = P{f(y, a, D) = y'}` | `inventoryNext`, `geomPmf`, `tsum_geomPmf`, `inventoryKernel`, `inventoryKernel_nonneg`, `inventoryKernel_rowsum`, `expectedRevenue`, `inventoryReward` |
| p. 198 | The model with `βₜ = β(Zₜ)` as an exogenous discount model; feasible orders `a ≤ K − y` | `inventorySDD`, `inventorySDD_mem_Γ` |
| (6.25)–(6.26), p. 198 | The action value in shock form and kernel form | `sum_mul_inventoryKernel`, `inventorySDD_B_apply`, `inventorySDD_B_apply'` |
| p. 198, Listing 6.1 | With `L(z, z') = β(z)Q(z, z')`, all the standard optimality results hold when `ρ(L) < 1` | `inventorySDD_LZ`, `inventorySDD_optimality`, `inventorySDD_bellman` |

## §6.3 Asset pricing (pp. 199–211)

| Book | Claim | Lean |
| --- | --- | --- |
| (6.27), p. 201 | Risk-neutral pricing `Πₜ = E_t βGₜ₊₁` in Markov form | `markovPrice_const` |
| (6.32), p. 205 | Markov pricing `π(x) = ∑ m(x, x')g(x, x')P(x, x')` | `markovPrice` |
| (6.35), Remark 6.3.1, p. 205–206 | The Arrow–Debreu discount operator `A = mP`; `Aᵏg` values a payoff `k` periods ahead | `adOp`, `adOp_apply`, `markovPrice_eq_adOp_mulVec` |
| (6.33)–(6.35), p. 205–206 | Ex-dividend pricing `π = Aπ + Ad`; `π* = (I − A)⁻¹Ad = ∑_{k≥1}Aᵏd` is the unique solution when `ρ(A) < 1` | `IsExDivPrice`, `exDivPrice`, `eq_exDivPrice_of_isExDivPrice`, `exDivPrice_eq_tsum` |
| Ex 6.3.1, p. 206 | `ρ(A) < 1` is necessary and sufficient for a unique positive solution when `m, d ≫ 0` | `adOp_mulVec_pos`, `specRad_lt_one_iff_existsUnique_pos_exDivPrice` |
| Ex 6.3.2, p. 206 | Risk-neutral case `m ≡ β`: `ρ(A) = β`, so `β < 1` | `specRad_adOp_const` |
| Ex 6.3.3, p. 206 | `π*` solves (6.33)–(6.34) | `isExDivPrice_exDivPrice` |
| Ex 6.3.4, (6.37), p. 206 | Cum-dividend pricing `π = d + Aπ`, `π = (I − A)⁻¹d` | `IsCumDivPrice`, `cumDivPrice`, `isCumDivPrice_iff`, `cumDivPrice_eq_add_exDivPrice` |
| §6.3.1.6, p. 206 | The forward sum `π = ∑ₜ Aᵗd` | `cumDivPrice_eq_tsum` |
| Ex 6.3.5, (6.38), p. 207 | `Vₜ = E_t[Mₜ₊₁ exp(κ)(1 + Vₜ₊₁)]`, in finite form | `price_dividend_ratio` |
| (6.39)–(6.40), p. 207–208 | The price-dividend equation and its operator | `pdOp`, `IsPDRatio` |
| Ex 6.3.6, (6.41), p. 208 | The unique solution `v* = (I − A)⁻¹A𝟙 = ∑_{t≥1}Aᵗ𝟙` when `ρ(A) < 1` | `isPDRatio_iff`, `pdRatio_eq_tsum` |
| Ex 6.3.7, p. 208 | `A(x, x') = β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)P(x, x')` with Gaussian shocks | `integral_exp_add_mul_gaussian`, `lucas_growth_factor` |
| (6.42)–(6.43), pp. 209–210 | The Harrison–Kreps equilibrium condition and operator; fixed points are equilibrium prices | `hkOp`, `hkOp_apply`, `isFixedPt_hkOp_iff` |
| pp. 210–211 | `T` is a self-map of `ℝ^X₊` and a contraction of modulus `β`; (6.42) has a unique solution in `ℝ^X₊`, found by successive approximation | `nonnegFns`, `isClosed_nonnegFns`, `hkOp_mapsTo`, `abs_hkOp_sub_le`, `isContractionOn_hkOp`, `existsUnique_hk_price` |
| Ex 6.3.9, p. 211 | Contractivity by Blackwell's condition | `hkOp_monotone`, `hkOp_add_const`, `isContractionOn_hkOp_univ` |
