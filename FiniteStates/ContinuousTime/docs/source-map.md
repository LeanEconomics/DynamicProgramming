# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 10, "Continuous Time" (pp. 308–341). Result, equation and exercise numbers
are the book's; page numbers are book pages. Lean names are relative to
`SargentStachurski.ContinuousTime`. Where the Lean statement adds a hypothesis the
book leaves implicit, or departs from the printed statement, see
[corrections](corrections.md).

Derivatives and integrals of matrix-valued functions are taken entry by entry, as the
book specifies (p. 312), so derivative statements are made for each entry `(x, y)`.

## Earlier-chapter facts restated

| Book | Claim | Lean |
| --- | --- | --- |
| Vol. 1, Ch. 1–3, 6 | Markov matrices, distributions, contractions, spectral radius, affine maps | `IsMarkov`, `IsDistribution`, `IsContractionOn`, `specRad`, `specRad_le_norm`, `complexify`, `affineOp`, `globallyStable_affineOp`, `isFixedPt_affineOp_inv`, `specRad_smul_isMarkov` |
| Vol. 1, Thm 7.1.1 | Knaster–Tarski | `knaster_tarski` |
| Vol. 1, §9.1.1 | Order stability | `OrderStable`, `orderStable_of_up_down`, `orderStable_of_globallyStable`, `orderStable_restrict`, `orderStable_affineOp`, `orderStable_dual_iff` |
| Vol. 1, §9.1.2, §9.2.1 | ADPs, greedy policies, Bellman and Howard operators, HPI, Thm 9.2.4, Prop 9.2.5 | `ADP`, `ADP.greedy`, `ADP.bellman`, `ADP.vσ`, `ADP.hpiPolicy`, `ADP.hpiValue`, `ADP.IsOrderStable`, `ADP.IsOrderStable.hpi_terminates`, `ADP.IsOrderStable.maxOptimality`, `ADP.IsMaxStable.optimality` |

## §10.1 Continuous-time Markov chains (pp. 308–329)

| Book | Claim | Lean |
| --- | --- | --- |
| Example 10.1.1, (10.1)–(10.2), p. 309 | `u_t = e^{rt}u₀` is the unique solution of `u̇ = ru` | `hasDerivAt_exp_mul`, `eq_exp_of_hasDerivAt` |
| Ex 10.1.1, (10.4), p. 310 | `Exp(θ)` is memoryless | `exp_memoryless` |
| Lemma 10.1.1, (10.5), p. 310 | A memoryless counter CDF is exponential, and conversely | `add_nsmul_of_additive`, `eq_exp_of_memoryless` ((ii) ⇒ (i)), `exp_counter_properties` ((i) ⇒ (ii)) |
| Ex 10.1.2, p. 311 | The partial sums of (10.6) are bounded by `e^{‖A‖}` | `norm_one_le`, `norm_pow_le_pow`, `norm_partialSum_exp_le`, `norm_exp_le` |
| Lemma 10.1.2 (i), Ex 10.1.3, pp. 311–312 | `e^{PDP⁻¹} = Pe^DP⁻¹` | `exp_conj_eq` |
| Lemma 10.1.2 (ii), p. 311 | `e^{A+B} = e^Ae^B` for commuting `A, B` | `exp_add_eq` |
| Lemma 10.1.2 (iii), p. 311 | `e^{mA} = (e^A)^m` | `exp_natCast_smul` |
| Lemma 10.1.2 (iv), p. 311 | `λ` eigenvalue of `A` ⇒ `e^λ` eigenvalue of `e^A`; the converse fails | `exp_mulVec_of_eigen`, `exp_mulVec_of_eigen_real`, `exp_eigenvalue_converse_false`, `exp_eigenvalue_converse_false_real` |
| Lemma 10.1.2 (v), Ex 10.1.4, (10.7), pp. 311–312 | `d/dt e^{tA} = Ae^{tA} = e^{tA}A` | `hasDerivAt_exp_smul`, `hasDerivAt_exp_smul'`, `exp_smul_mul_comm`, `hasDerivAt_exp_smul_entry`, `hasDerivAt_exp_neg_smul_entry` |
| Lemma 10.1.2 (vi), p. 311 | `e^{Aᵀ} = (e^A)ᵀ` | `exp_transpose_eq` |
| Lemma 10.1.2 (vii), Ex 10.1.6, (10.8), pp. 311–312 | `e^{tA} − e^{sA} = ∫_s^t e^{τA}A dτ` | `continuous_exp_smul`, `exp_smul_sub_eq_integral` |
| Ex 10.1.5, p. 312 | `e^A` is invertible with inverse `e^{−A}` | `exp_mul_exp_neg` |
| §10.1.2.1, p. 312 | Semigroup property | `exp_smul_semigroup`, `exp_smul_mul_exp_neg_smul` |
| Prop 10.1.3, (10.10), p. 313 | `u_t = e^{tA}u₀` is the unique solution of `u̇ = Au` | `mulVecCLM`, `entryCLM`, `hasDerivAt_mulVec_of_entry`, `hasDerivAt_exp_smul_mulVec`, `ivp_unique` |
| Ex 10.1.7, p. 314 | `φ̇ = φP` has the unique solution `φ_t = φ₀e^{tP}` | `ivp_unique_row` |
| Ex 10.1.8, p. 314 | `e^{tD} = diag(e^{tλᵢ})` | `exp_smul_diagonal` |
| (10.15), p. 315 | `e^{tλ} → 0` iff `Re λ < 0` | `tendsto_exp_mul_zero_iff` |
| (10.16), p. 315 | Spectral bound `s(A)` | `spectralBound`, `spectrum_nonempty`, `re_spectrum_finite`, `re_le_spectralBound`, `exists_re_eq_spectralBound` |
| §10.1.2.4, p. 316 | Spectral mapping `σ(e^A) = e^{σ(A)}` | `complexify_exp`, `complexify_smul`, `spectrum_complexify_exp` |
| Lemma 10.1.4, (10.17), Ex 10.1.9–10.1.11, p. 316 | `τs(A) = s(τA)`; `e^{s(A)} = ρ(e^A) = lim ‖e^{kA}‖^{1/k}` | `spectralBound_smul`, `specRad_exp`, `norm_exp_pos`, `tendsto_log_norm_exp` |
| Thm 10.1.5, Ex 10.1.12, pp. 316–317 | (i) `s(A) < 0`, (ii) `‖e^{tA}‖ → 0`, (iii) `‖e^{tA}‖ ≤ Me^{−ωt}`, (iv) `∫₀^∞ ‖e^{tA}u₀‖^p dt < ∞` are equivalent | `exp_smul_add`, `exists_exp_bound`, `stability_tfae` |
| §10.1.2.5, p. 317 | `C₀`-semigroups | `IsC0Semigroup` |
| Example 10.1.3, p. 317 | `(e^{tA})` is a `C₀`-semigroup | `isC0Semigroup_exp` |
| Prop 10.1.6, p. 318 | Every `C₀`-semigroup on `ℝ^X` is `e^{tA}`, with `A` its generator | `hasDerivAt_mul_entry`, `IsC0Semigroup.continuousOn_entry`, `IsC0Semigroup.intervalIntegrable_entry`, `IsC0Semigroup.V`, `IsC0Semigroup.hasDerivAt_V`, `IsC0Semigroup.tendsto_V_div`, `IsC0Semigroup.exists_V_isUnit`, `IsC0Semigroup.mul_V`, `IsC0Semigroup.hasDerivAt_entry`, `IsC0Semigroup.exists_eq_exp` |
| (10.20), Example 10.1.4, p. 319 | Intensity matrices | `IsIntensity`, `isIntensity_example` |
| Prop 10.1.7, Ex 10.1.16–10.1.17, pp. 319–320 | `Q` intensity ⇔ `e^{tQ}` Markov for `t ≥ 0` ⇔ `e^{tQ}` preserves distributions | `intensity_tfae` |
| Ex 10.1.13, p. 320 | `P_t1 = 1` | `exp_smul_one`, `exp_smul_mulVec_one` |
| Ex 10.1.14, p. 320 | `K = I + Q/θ` is stochastic and `Q = θ(K − I)` | `intensityBound`, `intensityJump`, `intensityJump_spec` |
| Ex 10.1.15, p. 320 | `P_t ≥ 0` | `exp_nonneg_of_nonneg`, `exp_smul_nonneg` |
| Ex 10.1.18, p. 321 | `(P_h − I)/h` is an intensity matrix | `isIntensity_of_isMarkov` |
| Ex 10.1.19, (10.27)–(10.28), p. 321 | `P_h(x, x') = hQ(x, x') + o(h)` | `exp_smul_entry_isLittleO` |
| (10.29), p. 321 | Chapman–Kolmogorov | `chapman_kolmogorov` |
| §10.1.3.3, pp. 321–322 | Kolmogorov backward and forward equations | `kolmogorov_backward`, `kolmogorov_forward` |
| Prop 10.1.8, p. 322 | A solution of either equation with `P₀ = I` is `e^{tQ}` | `hasDerivWithinAt_mul_entry`, `eq_one_of_deriv_zero`, `eq_exp_of_backward`, `eq_exp_of_forward` |
| (10.31), p. 324 | `Q = λ(Π − I)` is an intensity matrix | `jumpIntensity`, `isIntensity_jumpIntensity` |
| (10.32), (10.35)–(10.36), p. 325 | The integrated backward equation in both forms | `integral_backward_eq`, `hasDerivWithinAt_integral_Ici` |
| Lemma 10.1.11, p. 325 | (10.32) gives `P₀ = I` and `Ṗ_t = QP_t` | `backward_of_integrated` |
| Prop 10.1.9, p. 324 | Analytic part: (10.32) forces `P_t = e^{tQ}` | `eq_exp_of_integrated` |
| (10.37), Ex 10.1.20, p. 326 | The inventory jump matrix is stochastic | `inventoryJump`, `isMarkov_inventoryJump` |
| §10.1.4.4, p. 327 | From an intensity matrix to a jump chain | `intensityJumpChain`, `intensityJumpChain_spec` |

## §10.2 Continuous-time Markov decision processes (pp. 329–339)

| Book | Claim | Lean |
| --- | --- | --- |
| (10.38), p. 329 | Lifetime value `v = ∫₀^∞ K_th dt` | `continuous_exp_smul_mulVec`, `mulVecLinCLM`, `projCLM`, `lifetimeValue` |
| Prop 10.2.1 (i), (10.39), p. 329 | The integral is finite and `v = ∫₀^t K_τh dτ + K_tv` | `integrableOn_exp_mulVec`, `lifetimeValue_eq_integral_add` |
| Prop 10.2.1 (ii), p. 329 | `A` is invertible and `v = −A⁻¹h` | `isUnit_of_spectralBound_neg`, `mulVec_lifetimeValue`, `lifetimeValue_eq` |
| Prop 10.2.1 (iii), p. 329 | `A⁻¹ ≤ 0` | `inv_nonpos`, `neg_inv_mulVec_nonneg` |
| Prop 10.2.1 (iv), (10.40), p. 330 | `Uw = h + (I + A)w` is order stable with fixed point `v` | `orderStable_valuation` |
| Ex 10.2.1, p. 332 | Path discount factors | `pathDiscount_properties` |
| Prop 10.2.3, (10.44)–(10.46), p. 333 | Constant discounting | `exp_smul_sub_smul_one`, `constant_discounting` |
| §10.2.2.1, (10.47), p. 334 | Continuous-time MDPs, feasible policies | `CTMDP`, `CTMDP.Policy`, `CTMDP.nonempty_policy` |
| §10.2.2.2, (10.48)–(10.49), p. 335 | `Q_σ`, `r_σ`, `v_σ = (δI − Q_σ)⁻¹r_σ` | `CTMDP.Qσ`, `CTMDP.rσ`, `CTMDP.isIntensity_Qσ`, `CTMDP.vσ`, `CTMDP.vσ_eq_integral`, `CTMDP.vσ_eq` |
| (10.50), p. 335 | `v`-greedy policies | `CTMDP.flow`, `CTMDP.IsGreedy`, `CTMDP.exists_greedy`, `CTMDP.exists_minGreedy` |
| Algorithm 10.2, p. 336 | Continuous-time HPI | `CTMDP.hpiPolicy`, `CTMDP.hpiPolicy_eq` |
| (10.51), §10.2.2.5, p. 336 | Policy operators; the order stable ADP | `CTMDP.Tσ`, `CTMDP.Tσ_apply`, `CTMDP.orderStable_Tσ`, `CTMDP.toADP`, `CTMDP.isOrderStable_toADP`, `CTMDP.toADP_vσ` |
| Ex 10.2.2, p. 336 | (10.50) iff greedy for the ADP | `CTMDP.isGreedy_iff`, `CTMDP.isGreedy_greedy` |
| (10.52)–(10.53), p. 337 | HJB equation; the Bellman operator | `CTMDP.IsHJB`, `CTMDP.bellman_apply`, `CTMDP.isFixedPt_bellman_iff` |
| Thm 10.2.4, p. 337 | (i) `v*` uniquely solves the HJB equation; (ii) Bellman's principle; (iii) an optimal policy exists; HPI terminates | `CTMDP.optimality` |
| §10.2.4, p. 338 | Job search: `λ`, `Π`, `Q = λ(Π − I)`, `r` | `jsJump`, `jsRate`, `jsRate_nonneg`, `jsJump_isMarkov`, `jobSearch` |
| Ex 10.2.3, p. 339 | `Π` is a stochastic kernel | `jsJump_stochastic` |
| p. 339 | `Q_σ` is an intensity matrix; Theorem 10.2.4 applies | `jobSearch_Qσ`, `jobSearch_optimality` |
