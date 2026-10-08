# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 1, "Introduction" (pp. 1–41). Result, equation and exercise numbers
are the book's; page numbers are book pages. Lean names are relative to
`SargentStachurski.JobSearch`. Where the Lean statement adds a hypothesis the
book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## §1.2.1.1 Real and complex vectors (pp. 12–13) and §1.2.4.1 Pointwise operations (pp. 29–30)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 12 | `|a| := a ∨ (−a)` | `abs_eq_max_neg'` |
| Ex 1.2.1, p. 13 | `α ∨ (s + t) ≤ s + α ∨ t` for `s ≥ 0` | `max_add_le_add_max` |
| (1.20), p. 29 | `(αu + βv)(x) = αu(x) + βv(x)`, `(uv)(x) = u(x)v(x)` | `smul_add_smul_apply`, `mul_apply'` |
| (1.21), p. 29 | `|u|(x)`, `(u ∨ v)(x)`, `(u ∧ v)(x)` pointwise | `abs_apply'`, `sup_apply'`, `inf_apply'` |
| (1.28), Ex 1.3.1, p. 34 | `|α ∨ x − α ∨ y| ≤ |x − y|`, via Ex 1.2.1 | `max_le_abs_sub_add_max`, `abs_max_sub_max_le` |
| (1.29), p. 35 | `x ↦ α ∨ x` is order preserving | `max_le_max_of_le` |

## §1.2.2.1 Fixed points and §1.2.2.2 Global stability (pp. 20–22)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 20 | Fixed point `Tu* = u*` | Mathlib's `Function.IsFixedPt` |
| Ex 1.2.3, p. 20 | Every point is fixed by the identity | `isFixedPt_id` |
| Ex 1.2.4, p. 20 | `u ↦ u + 1` on `ℕ` has no fixed point | `not_isFixedPt_succ` |
| Ex 1.2.15, p. 21 | Eventually constant iterates give the unique fixed point | `isFixedPt_of_iterate_eventually_const`, `eq_of_isFixedPt_of_iterate_eventually_const` |
| Ex 1.2.16, p. 21 | A limit of iterates where `T` is continuous is a fixed point | `isFixedPt_of_tendsto_iterate` |
| p. 22 | Global stability | `GloballyStable`, `GloballyStable.exists_unique`, `globallyStable_of_tendsto` |
| p. 22 | Invariant set | Mathlib's `Set.MapsTo`; `iterate_mem_of_mapsTo` |
| Ex 1.2.18, p. 22 | The fixed point lies in every closed invariant `C` | `GloballyStable.fixedPt_mem_of_isClosed` (`C` nonempty added) |

## §1.2.2.3 Banach's fixed-point theorem (pp. 22–23) and the function-space restatement (p. 31)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.17), p. 22 | Contraction of modulus `λ` on `U` | `IsContractionOn` |
| Ex 1.2.19, p. 22 | A contraction is continuous and has at most one fixed point in `U` | `IsContractionOn.continuousOn`, `IsContractionOn.fixedPt_unique` |
| Ex 1.2.21, p. 23 | `‖uₘ − uₖ‖ ≤ ∑_{i=m}^{k−1} λⁱ‖u₀ − u₁‖` | `IsContractionOn.norm_iterate_sub_iterate_succ_le`, `IsContractionOn.norm_iterate_sub_iterate_le_sum` |
| Ex 1.2.22, p. 23 | `(uₘ)` is Cauchy; the solution's closed-form bound | `IsContractionOn.cauchySeq_iterate`, `IsContractionOn.norm_iterate_sub_iterate_le` |
| Ex 1.2.23, p. 23 | The limit lies in the closed set `U` | `IsContractionOn.limit_mem` |
| Proof of Thm 1.2.3, p. 23 | The limit is a fixed point (Ex 1.2.16 + Ex 1.2.19) | `IsContractionOn.isFixedPt_of_tendsto` |
| (1.18), p. 23 | `‖Tᵏu − u*‖ ≤ λᵏ‖u − u*‖` | `IsContractionOn.norm_iterate_sub_fixedPt_le`, `IsContractionOn.tendsto_iterate_fixedPt` |
| Thm 1.2.3, p. 23 | Banach: existence, uniqueness, rate | `IsContractionOn.exists_fixedPt`, `IsContractionOn.banach` |
| Thm 1.2.3, p. 23 | "in particular `T` is globally stable on `U`" | `IsContractionOn.globallyStable` |
| Ex 1.2.24, p. 23 | Damped iteration `(1 − α)u + αTu` converges for `0 < α ≤ 1` | `isContractionOn_damped`, `isFixedPt_damped_iff`, `tendsto_damped_iterate` |
| p. 31 | Banach on `ℝ^X`, `X` finite, sup norm | `IsContractionOn.banach_pi` |

## §1.2.1.2 Norms, §1.2.1.3 Equivalence of norms, §1.2.1.4 Matrix norms (pp. 13–17)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 13 | The four norm axioms | `IsNorm` |
| (1.9), Ex 1.2.2, p. 14 | ℓ¹ norm is a norm | `l1Norm`, `isNorm_l1Norm` |
| Ex 1.2.3, p. 14 | Weighted ℓ¹ with positive weights is a norm | `weightedL1Norm`, `isNorm_weightedL1Norm` |
| Ex 1.2.4, p. 14 | Supremum norm is a norm; `‖u‖_∞ = maxᵢ |uᵢ|` | `supNorm`, `isNorm_supNorm`, `supNorm_le_iff`, `abs_le_supNorm` |
| Ex 1.2.5, p. 14 | ℓ⁰ is not a norm | `l0Norm`, `not_isNorm_l0Norm` |
| (1.11), Ex 1.2.6, p. 15 | Norm equivalence is an equivalence relation | `NormEquiv`, `normEquiv_refl`, `normEquiv_symm`, `normEquiv_trans`, `normEquiv_equivalence` |
| Ex 1.2.7, p. 15 | Equivalent norms give the same convergent sequences | `tendsto_of_normEquiv` |
| Ex 1.2.8, p. 15 | Pointwise convergence ⇔ norm convergence in `ℝⁿ` | `tendsto_pi_iff_tendsto_supNorm` |
| (1.12), p. 16 | Operator norm `max_{‖u‖=1} ‖Bu‖`, here in the sup norm | `opNorm`, `supNorm_mulVec_le` |
| (1.13), p. 16 | Entrywise supremum norm | `matrixSupNorm` |
| Ex 1.2.9, p. 17 | Operator norm submultiplicative; entrywise norm not | `opNorm_mul`, `not_matrixSupNorm_submultiplicative` |

## §1.2.1.4 Matrices and Neumann series (pp. 16–19), with Example 1.2.2 and Exercises 1.2.17, 1.2.20

| Book | Claim | Lean |
| --- | --- | --- |
| p. 17 | Eigenvalue `λ ∈ ℂ` with eigenvector `e ≠ 0`, `Ae = λe` | `complexify`, `mem_spectrum_iff_eigenpair` |
| (1.14), p. 17 | Scalar case: `|a| < 1 ⇒ u* = b/(1 − a) = ∑ aᵏb` | `scalar_neumann` |
| (1.15), p. 18 | Spectral radius `ρ(A) = max{|λ|}` | `specRad`, `specRad_nonneg` |
| Thm 1.2.1, p. 18 | Neumann series lemma | `neumann_series`, `inv_one_sub_mul`, `mul_inv_one_sub` |
| p. 18 | `u = Au + b` has the unique solution `(I − A)⁻¹b` | `isFixedPt_affine_inv`, `affine_fixedPt_unique` |
| Ex 1.2.10, p. 18 | `ρ(αB) = |α| ρ(B)` | `specRad_smul` |
| Lemma 1.2.2, p. 19 | `ρ(B)ᵏ ≤ ‖Bᵏ‖`; Gelfand's formula `‖Bᵏ‖^{1/k} → ρ(B)` | `specRad_pow_le_norm_pow`, `tendsto_norm_pow_rpow`, `eventually_norm_pow_le` |
| Ex 1.2.11, p. 19 | `‖Bᵏ‖ → 0 ⇔ ρ(B) < 1`; `ρ(B) > 1 ⇒ ‖Bᵏ‖ → ∞` | `tendsto_norm_pow_zero`, `tendsto_pow_zero`, `specRad_lt_one_of_tendsto`, `tendsto_norm_pow_atTop` |
| Ex 1.2.12, p. 19 | Commuting `A, B`: `ρ(AB) ≤ ρ(A)ρ(B)` | `specRad_mul_le` |
| Ex 1.2.13, p. 19 | `ρ(A) < 1 ⇒ ∑ Aᵏ` converges | `summable_pow` |
| Ex 1.2.14, p. 19 | `∑ Aᵏ` exists `⇒ (I − A)⁻¹ = ∑ Aᵏ` | `one_sub_mul_tsum`, `tsum_mul_one_sub`, `isUnit_one_sub_of_summable`, `inv_one_sub_of_summable` |
| Ex 1.2.2, p. 20 | Fixed points of `Tu = Au + b` | `affine`, `isFixedPt_affine_iff` |
| Ex 1.2.17, (1.16), p. 22 | `Tᵏu = Aᵏu + Aᵏ⁻¹b + ⋯ + b`; globally stable when `ρ(A) < 1` | `affine_iterate`, `tendsto_affine_iterate`, `globallyStable_affine` |
| Ex 1.2.20, p. 22 | `‖A‖ < 1 ⇒ T` is a contraction of modulus `‖A‖` | `isContractionOn_affine`, `opNorm_eq_norm` |

## §1.2.3 Successive approximation (pp. 24–28)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 24 | Iterates of a globally stable map converge to its fixed point | `GloballyStable.tendsto_iterate` |
| (1.19), p. 27 | Solow–Swan map `g(k) = sAkᵅ + (1 − δ)k` | `Solow`, `Solow.g` |
| Ex 1.2.25, p. 27 | `g` maps `(0, ∞)` to itself but is not a contraction | `Solow.g_pos`, `Solow.mapsTo_g`, `Solow.not_isContractionOn_g` |
| Ex 1.2.26, p. 27 | `k* = (sA/δ)^{1/(1−α)}` is the unique fixed point | `Solow.kstar`, `Solow.isFixedPt_kstar`, `Solow.eq_kstar_of_isFixedPt` |
| Ex 1.2.26 (i), (ii) | `k ≤ k* ⇒ k ≤ g(k) ≤ k*`; `k* ≤ k ⇒ k* ≤ g(k) ≤ k` | `Solow.le_g_le_of_le_kstar`, `Solow.kstar_le_g_le_of_kstar_le` |
| Ex 1.2.26, "(Why?)" | `g` is globally stable on `(0, ∞)` | `Solow.tendsto_iterate_kstar`, `Solow.globallyStable_g` |

## §1.2.4.2 Functions versus vectors and §1.2.4.3 Distributions (pp. 30–32)

| Book | Claim | Lean |
| --- | --- | --- |
| Lemma 1.2.4, (1.23), p. 30 | `ℝ^X ↔ ℝⁿ` one-to-one | `toVector`, `toVector_apply`, `toVector_symm_apply` |
| p. 30 | Norms extend to `ℝ^X` via the identification | `norm_toVector` |
| p. 31 | `D(X)`; supported on `X₀`; `E h(X) = ⟨h, φ⟩` | `IsDistribution`, `SupportedOn`, `expectation`, `isDistribution_pointMass`, `expectation_pointMass`, `expectation_le` |
| Ex 1.2.27, p. 31 | `φ*` maximises `⟨h, φ⟩` over `D(X)` iff supported on `argmax h` | `expectation_maximiser_iff` (with `expectation_eq_of_supportedOn`, `expectation_lt_of_not_supportedOn`) |
| p. 32 | CDF `Φ(x) = ∑ 1{x' ≤ x} φ(x')` | `IsDistributionOn`, `cdf`, `cdf_mono`, `cdf_max'` |
| (1.24), p. 32 | `τ`-quantile `min{x ∈ X : Φ(x) ≥ τ}`; median | `quantileSet`, `quantileSet_nonempty`, `quantile`, `quantile_mem`, `quantile_le` |
| Ex 1.2.5, p. 32 | `Φ = (0.5, 0.5, 1)`, median `x₁` | `example_1_2_5_cdf`, `example_1_2_5_median` |
| Ex 1.2.28, p. 32 | `Q_τ(X + α) = Q_τ(X) + α` | `isDistributionOn_shift`, `cdf_shift`, `quantileSet_shift`, `quantile_shift` |

## §1.1.1 Finite-horizon job search (pp. 3–10) and Assumption 1.1.1 (p. 11)

| Book | Claim | Lean |
| --- | --- | --- |
| pp. 3–4, Assumption 1.1.1 | Finite `W ⊂ ℝ₊`, `φ ∈ D(W)`, `c > 0`, `β ∈ (0, 1)` | `Model` |
| p. 31 | `E h(W) = ∑ h(w) φ(w)` | `Model.E`, `Model.E_const`, `Model.E_mono`, `Model.E_add`, `Model.E_mul`, `Model.abs_E_sub_E_le` |
| (1.2), p. 4 | `v₂(w) = max{c, w}`; `h₁ = c + β ∑ v₂(w')φ(w')` | `Model.value_zero`, `Model.contValue_zero` |
| p. 4 | Stopping value `w + βw`; accept iff `w + βw ≥ h₁` | `Model.stopValue`, `Model.annuity`, `Model.contValue_le_stopValue_iff` |
| (1.3), p. 6 | `v₁(w) = max{w + βw, h₁}` | `Model.value_one` |
| (1.4), p. 6 | `w₁* = h₁/(1 + β)`; accept iff `w ≥ w₁*` | `Model.resWage_one`, `Model.value_succ_eq_stopValue_iff`, `Model.value_succ_eq_contValue_iff` |
| p. 7 | Higher `c` raises `h₁` and `w₁*` | `Model.contValue_le_contValue_of_c_le`, `Model.resWage_le_resWage_of_c_le` (every horizon) |
| (1.5), p. 7 | `v₀(w) = max{w + βw + β²w, c + β ∑ v₁(w')φ(w')}` | `Model.value_two` |
| Ex 1.1.2, p. 10 | `w₀* = h₀/(1 + β + β²)` | `Model.resWage_two` |
| Ex 1.1.3, p. 10 | `T` periods: value and reservation wage at every horizon | `Model.value`, `Model.resWage`, `Model.value_succ`, `Model.value_zero_eq_wage_iff`, `Model.resWage_pos` |

## §1.1.2 Infinite horizon (pp. 10–12) and §1.3.1 Values and policies (pp. 32–36)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.7), p. 11 | `w + βw + β²w + ⋯ = w/(1 − β)` | `Model.tsum_geometric_wage`, `Model.stop` |
| (1.8) = (1.25), p. 11, p. 33 | Bellman equation `v*(w) = max{w/(1 − β), c + β ∑ v*(w')φ(w')}` | `Model.bellman_equation` |
| (1.26), p. 33 | `h* = c + β ∑ v*(w')φ(w')`; accept iff `w/(1 − β) ≥ h*` | `Model.hstar`, `Model.hstar_le_stop_iff` |
| (1.27), p. 33 | Bellman operator `T` on `V = ℝ^W₊` | `Model.T`, `V`, `V_nonempty`, `isClosed_V`, `Model.mapsTo_T` |
| Prop 1.3.1, p. 33 | `T` is a contraction of modulus `β` on `V` | `Model.abs_T_sub_T_le`, `Model.norm_T_sub_T_le`, `Model.isContractionOn_T`, `Model.isContractionOn_T_univ` |
| p. 33 | `Tᵏv → v*` for every `v ∈ V` | `Model.vstar`, `Model.isFixedPt_vstar`, `Model.tendsto_iterate_T`, `Model.norm_iterate_T_sub_vstar_le`, `Model.globallyStable_T` |
| p. 33 | `v*` is the unique solution of the Bellman equation | `Model.eq_vstar_of_isFixedPt`, `Model.existsUnique_fixedPt` |
| p. 35 | Policies `σ : W → {0, 1}` | `Model.Policy` |
| (1.29), p. 35 | `v`-greedy policy | `Model.IsGreedy`, `Model.exists_isGreedy` |
| (1.30), p. 36 | `σ*(w) = 1{w ≥ w*}`, `w* = (1 − β)h*` | `Model.reservationWage`, `Model.isGreedy_vstar_iff` |

## §1.3.2 Computation (pp. 36–41)

| Book | Claim | Lean |
| --- | --- | --- |
| Algorithm 1.1, p. 37 | Value function iteration converges | `Model.tendsto_iterate_T`, `Model.norm_iterate_T_sub_vstar_le` |
| p. 39 | `v*(w) = max{w/(1 − β), h*}` | `Model.vstar_eq_max` |
| (1.32), p. 40 | `h* = c + β ∑ max{w'/(1 − β), h*} φ(w')` | `Model.isFixedPt_g_hstar` |
| (1.33), p. 40 | The map `g : ℝ₊ → ℝ₊` | `Model.g`, `Model.g_nonneg`, `Model.mapsTo_g` |
| Ex 1.3.2, p. 40 | `g` is a contraction; `h*` its unique fixed point in `ℝ₊`; iterates converge | `Model.abs_g_sub_g_le`, `Model.isContractionOn_g`, `Model.isContractionOn_g_univ`, `Model.hstar_nonneg`, `Model.eq_hstar_of_isFixedPt_g`, `Model.tendsto_iterate_g`, `Model.abs_iterate_g_sub_hstar_le` |
| Ex 1.3.3, p. 41 | `v*` from `h*` agrees with VFI | `Model.vstar_eq_max_hstar` |
| (1.34), p. 41 | `σ*` is `v*`-greedy iff `σ*(w) = 1{w/(1 − β) ≥ h*}` | `Model.isGreedy_vstar_iff_hstar` |
| p. 7, infinite horizon | Higher `c` raises `h*` and `w*` | `Model.g_mono`, `Model.g_le_g_of_c_le`, `Model.hstar_le_hstar_of_c_le`, `Model.reservationWage_le_of_c_le` |
