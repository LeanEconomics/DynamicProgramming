# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University Press,
2009): Chapter 15, pp. 362–391. Equation numbers are the book's. Lean names are relative to
`MeynTweedie.GeometricErgodicity`; names from Mathlib are marked as such. Names marked "carried" are
in the modules copied from the Chapter 14 project `FErgodicity` (see the [README](../README.md)).
"Positive" is `IsPositive P ψ` (carried): `ψ`-irreducible with an invariant probability, which is
the book's "positive recurrent" by Proposition 10.1.1. `ψ` is a maximal irreducibility measure
(`IsMaximalIrreducibility P ψ`, carried) and `B⁺(X)` is `{B : ψ(B) > 0}`. `μP` is `P ∘ₘ μ`.
`‖μ − ν‖_f` is `fNorm f μ ν` (carried). `rᵗ` for `t ∈ ℕ ∪ {∞}` is `tpow r t`, `E_x[r^{τ_A}]` is
`kendallMoment P A r x`, `E_x[Σ_{k<τ_B} f(Φ_k) rᵏ]` is `geomSum P B r f x`,
`U_B^{(r)}(x, f) = E_x[Σ_{k=1}^{τ_B} f(Φ_k) rᵏ]` is `geomTaboo P B r f x`, and
`G_B^{(r)}(x, f) = E_x[Σ_{k=0}^{σ_B} f(Φ_k) rᵏ]` is `geomG P B r f x`. (V4) is `DriftV4 P V ρ b C`
with `ρ = 1 − β`. `τ_C(n)` is `returnTimeK C n` (carried), `f^{(m)}` is `fSkel P m f` (carried), and
the split chain of `M : Minorization P` (carried) has kernel `M.splitKernel`, atom `M.checkAlpha`
(`α̌`) and split initial laws `M.splitK x` (`x*`). Every place where the Lean statement departs from
the book is listed in [corrections](corrections.md).

## Chapter 15 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 362 | For many models `‖Pⁿ(x, ·) − π‖_f = o(ρⁿ)` with `ρ < 1` essentially independent of `x`; the geometric context is the most useful of the book | Not formalised (informal) |
| Theorem 15.0.1, p. 362 | Standing hypothesis: `Φ` is `ψ`-irreducible and aperiodic | `IsMaximalIrreducibility P ψ` and `IsAperiodic P ψ` (carried) in `theorem_15_0_1` and `theorem_15_0_1_consequences`; the state space is countably generated |
| Theorem 15.0.1 (i), (15.1), p. 362 | `Φ` is positive recurrent with invariant probability `π`, and a `ν`-petite `C ∈ B⁺(X)` has `|Pⁿ(x, C) − P^∞(C)| ≤ M_C ρ_Cⁿ` for `x ∈ C`, with `ρ_C < 1` and `P^∞(C) > 0` | `IsLocallyGeomErgodic P ψ`: `IsPositive P ψ` and a petite `C` with `ψ(C) > 0`, `0 ≤ ρ < 1` and a limit `p > 0` |
| Theorem 15.0.1 (ii), (15.2), p. 362 | Some petite `C` and `κ > 1` have `sup_{x ∈ C} E_x[κ^{τ_C}] < ∞` | `HasKendallPetite P`: a petite, **non-empty** Kendall set (`IsKendall`, `IsKendallSet`, `kendallMoment`). As printed it holds for `C = ∅` and every chain (`theorem_15_0_1_counterexample`); see corrections |
| Theorem 15.0.1 (iii), (15.3), p. 363 | A petite `C`, `b < ∞`, `β > 0` and `V ≥ 1` finite at some `x₀` with `ΔV ≤ −βV + b 1_C` | `HasDriftV4 P`: a measurable `V ≥ 1` with `V(x₀) ≠ ∞` and `DriftV4 P V ρ b C` for a petite `C`, `ρ < 1` and `b ≠ ∞` |
| p. 362 | (i), (ii) and (iii) are equivalent | `theorem_15_0_1` (a `List.TFAE`, Mathlib) |
| p. 363 | `S_V = {V < ∞}` is absorbing and full for any solution `V` of (15.3) | `theorem_15_0_1_consequences` (first two conclusions), from `lemma_15_2_2_i` |
| (15.4), p. 363 | `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_V ≤ R V(x)` for `x ∈ S_V`, with `r > 1` and `R < ∞` | `theorem_15_0_1_consequences` (for every `x`, trivially off `S_V`; it also gives positivity and `π(V) < ∞`); `geometric_ergodic_of_driftV4` |
| p. 363 | Proof: (i) ⇔ (ii) by Theorem 15.4.3; (ii) ⇔ (iii) by Theorems 15.2.6 and 15.2.4; (15.4) by Theorem 15.4.1, with the bound from Theorem 15.3.3 | (ii) ⇒ (iii): `hasDriftV4_of_hasKendallPetite` (Theorem 15.2.4 with `f = 1`; `IsKendall.isFKendall_one`). (iii) ⇒ (ii): `hasKendallPetite_of_hasDriftV4` (a sublevel set of `V` in `B⁺(X)`, `exists_kendall_sublevel`). (iii) ⇒ (i): `isLocallyGeomErgodic_of_hasDriftV4` (`geometric_ergodic_of_driftV4` with the test function `1_D`, `ofReal_abs_measureReal_sub_le_fNorm`). (i) ⇒ (ii): `hasKendallPetite_of_isLocallyGeomErgodic` (`exists_concentrated_minorization`, then `hasKendallPetite_of_split_local`, the argument of Theorem 15.4.3; `fSkel_one_const`, and `hasKendallPetite_of_isFGeomRegularOn` with `geomSum_empty_one`, which rules out `C = ∅`). (15.4): `geometric_ergodic_of_driftV4` |
| p. 363 | The same `V` appears on both sides of (15.4), and `r` does not depend on the initial state | The form of `theorem_15_0_1_consequences`; the operator-norm consequences are in Chapter 16 (not formalised here) |
| (15.5)–(15.6), p. 363 | `‖Pⁿ(x, ·) − π‖_f ≤ M_x r⁻ⁿ` for some `r > 1` is equivalent to `Σₙ r̄ⁿ ‖Pⁿ(x, ·) − π‖_f ≤ M̄_x` for some `r̄ > 1` | Not formalised (remark); the results are stated in the summed form (15.6) |
| (15.7), p. 363 | `f`-geometric ergodicity: `f ≥ 1`, positive Harris with `π(f) < ∞` and `Σ_{n ≥ 1} r_fⁿ ‖Pⁿ(x, ·) − π‖_f < ∞` for all `x`; geometric ergodicity for `f ≡ 1` | No separate definition. The hypotheses of `theorem_15_4_2_univ` (with an invariant probability in place of positive Harris recurrence), and the conclusions of `theorem_15_0_1_consequences`, `theorem_15_4_1` and `theorem_15_4_3` |
| p. 364 | The pattern of the chapter: atoms, then aperiodic chains through the splitting | Not formalised (informal) |

## §15.1.1 Using the regenerative decomposition

| Source | Claim | Lean |
| --- | --- | --- |
| p. 364 | A positive Harris chain with an accessible atom `α ∈ B⁺(X)` | `IsAccessibleAtom P ψ α` (carried) with an invariant probability `π`; `atom_rep_of_invariant` (`π = π(α) μ°_α` and `L(a, α) = 1`; `atomMeasure`, carried) |
| (15.8), p. 364 | `Σₙ ‖Pⁿ(x, ·) − π‖_f rⁿ` is bounded by three sums from the Regenerative Decomposition (13.48) | `tsum_fNorm_le_geom_atom` (from the `f`-norm decomposition `fNorm_comp_pow_succ_le`, carried) |
| (15.9), p. 364 | `Σₙ ∫ _αPⁿ(x, dw) f(w) rⁿ ≤ E_x[Σ_{n=1}^{τ_α} f(Φₙ) rⁿ]` | `tsum_pow_lintegral_tabooKernel` (an equality, `= U_α^{(r)}(x, f)`; `tabooKernel`, carried), `tsum_pow_lintegral_tabooSeq` (from an initial law) |
| (15.10)–(15.11), pp. 364–365 | The tail term is at most `r/(r − 1) E_α[Σ_{n=1}^{τ_α} f(Φₙ) rⁿ]`; the convolution term factors | In the proof of `tsum_fNorm_le_geom_atom`, with `tsum_sum_range_mul` (carried) |
| (15.12), p. 365 | `U_α^{(r)}(x, f) = E_x[Σ_{n=1}^{τ_α} f(Φₙ) rⁿ]`, possibly infinite for `r ≥ 1` | `geomTaboo`, `measurable_geomTaboo`, `geomTaboo_one` (`r = 1` gives `tabooPotFn`, carried), `geomTaboo_mono_r`, `geomTaboo_mono_f`, `geomTaboo_const_mul` |
| p. 365 | `Σₙ |a_x ∗ u − π(α)| rⁿ ≤ E_x[r^{τ_α}] Σₙ |u(n) − π(α)| rⁿ + r/(r − 1) E_x[r^{τ_α}]` | `geometric_delayed_bound` (carried); `tsum_entryLaw_mul_pow_le`, `summable_entryLaw_mul_pow` (`Σₙ a_λ(n) rⁿ ≤ E_λ[r^{τ_α}]`; `entryLaw`, carried) |
| pp. 365–366 | What is needed: a geometrically ergodic atom and `U_α^{(r)}(α, f)`, `U_α^{(r)}(x, f)` finite | Not formalised (informal); the conditions are the hypotheses of `tsum_fNorm_le_geom_atom` |

## §15.1.2 Kendall's renewal theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 15.1.1, (15.13)–(15.14), p. 366 | Kendall's Theorem: for an ergodic renewal sequence, (i) `Σ |u(n) − u(∞)| zⁿ` converges for `|z| < r₀`, (ii) `U(z)` extends analytically to `|z| < r₀` except for a simple pole at `1`, and (iii) `P(z)` converges for `|z| < κ`, are equivalent | `theorem_15_1_1` (carried, `KendallTheorem`, a `List.TFAE`; an aperiodic increment law, `IsIncrementLaw`, `IsAperiodicLaw`, carried; (ii) as `U(z) = F(z)/(1 − z)` with `F` analytic on `|z| < r₀` and `F(1) ≠ 0`) |
| (15.15)–(15.16), pp. 366–367 | `F(z) = (1 − z) U(z)` and `F(z) = (1 − z)(1 − P(z))⁻¹`; Cauchy's inequality; Lemma D.7.2 | Carried, in `KendallTheorem`: `genFunC_seqDiff`, `one_sub_mul_genFunC_renewalTail`, `exists_summable_of_differentiableOn`, `summable_abs_sub_of_seqDiff`, `summable_seqDiff_of_abs_sub` |
| p. 367 | For aperiodic `p`, `z = 1` is the only root of `P(z) = 1` on the unit circle, and it is simple | `genFunC_incr_ne_one`, `genFunC_renewalTail_ne_zero` (carried) |
| p. 368 | A coupling proof of one direction; the classical analytic proof is given | Not formalised (remark) |

## §15.1.3 The geometric ergodic theorem for atoms

| Source | Claim | Lean |
| --- | --- | --- |
| p. 368 | Geometrically ergodic atoms: `Σₙ r_αⁿ |Pⁿ(α, α) − π(α)| < ∞` for some `r_α > 1` | `IsGeomErgodicAtom P π α` |
| p. 368 | Kendall atoms of rate `κ`: `E_α[κ^{τ_α}] < ∞`; `f`-Kendall atoms: `sup_{x ∈ α} E_x[Σ_{n<τ_α} f(Φₙ) κⁿ] < ∞` | `IsKendall P α κ` and `IsFKendall P f α κ` for an atom `α` (`IsAtom`, carried); `kendallMoment_eq_tsum`, `tsum_pow_tabooKernel_le_kendallMoment`, `hitProb_eq_one_of_kendallMoment_ne_top`, `IsAtom.geomTaboo_const` |
| p. 368 | If `f` is bounded on `α`, `α` is `f`-Kendall iff `U_α^{(κ)}(α, f) < ∞`; `U_α^{(κ)}(α, f) ≥ E_α[κ^{τ_α}]` for `f ≥ 1` | `geomTaboo_le_geomSum_add`, `geomSum_le_add_geomTaboo`; `kendallMoment_le_geomTaboo`, `geomTaboo_one_le_kendallMoment` |
| Proposition 15.1.2, p. 369 | For a `ψ`-irreducible aperiodic chain with an accessible Kendall atom, `|Pⁿ(α, α) − π(α)| ≤ R r_α⁻ⁿ` | `proposition_15_1_2` (an invariant probability `π` assumed; `ρ = r_α⁻¹`); the renewal part is `kendall_geometric_bound` (carried) |
| Proposition 15.1.3, (15.17), p. 369 | For an `f`-Kendall atom `α ∈ B⁺(X)` of rate `κ`, `S_f^κ = {U_α^{(κ)}(·, f) < ∞}` is full and absorbing | `proposition_15_1_3` (`φ`-irreducible, `α` non-empty, `f ≥ 1`); `isAbsorbing_geomTaboo_finite` |
| p. 369 | Proof: `∫ P(x, dy) U_α^{(κ)}(y, B) = κ⁻¹ U_α^{(κ)}(x, B) + P(x, α) U_α^{(κ)}(α, B)`, integrated against `f`; then Proposition 4.2.3 | False as printed: `proposition_15_1_3_counterexample` (the one-point space). Corrected: `proposition_15_1_3_identity`, `P U_α^{(κ)}(·, f) + Pf = κ⁻¹ U_α^{(κ)}(·, f) + P(·, α) U_α^{(κ)}(α, f)`; `proposition_4_2_3_i` (carried) |
| Theorem 15.1.4, (15.18), p. 369 | For a `ψ`-irreducible chain with invariant `π` and an `f`-Kendall atom `α ∈ B⁺(X)` of rate `κ`, `X = S^κ ∪ N` with `S^κ` full absorbing and `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R U_α^{(κ)}(x, f)` on `S^κ` | False without aperiodicity: `theorem_15_1_4_counterexample` (the flip chain, `flipKernel`, `flipKernel_apply`, `isMarkovKernel_flipKernel`, `flipKernel_pow`, `flipPi`, `isProbabilityMeasure_flipPi`, `isInvariant_flipPi`, `half_le_fNorm_flip`). Corrected: `theorem_15_1_4` (aperiodic, `f ≥ 1`; the sum over `n ≥ 1`, for every `x`) |
| p. 369 | Proof: Proposition 15.1.3 for (15.9), (15.10) and the second term of (15.11); Kendall's Theorem as in Proposition 15.1.2 for the first; `r = min(κ, r_α)` | `tsum_fNorm_le_geom_atom` (through `kendall_geometric_of_moment`, carried), `proposition_15_1_3` |
| Theorem 15.1.5, (15.19), p. 370 | For a `ψ`-irreducible chain with invariant `π` and a geometrically ergodic atom `α ∈ B⁺(X)`, `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ ≤ R E_x[κ^{τ_α}]` on a full absorbing `S^κ` | `theorem_15_1_5` (the sum over `n ≥ 1`, in `‖·‖_1`, for every `x`; aperiodicity is not assumed) |
| p. 369 | The proof of Theorem 15.1.5 follows the steps of Theorem 15.1.4 and is omitted | Proved: `isAperiodicLaw_of_tendsto_pos` (aperiodicity of the return-time law from `Pⁿ(α, α) → π(α) > 0`), `kendall_moment_of_geometric` (carried, Kendall's Theorem (i) ⇒ (iii)), `tsum_fNorm_le_geom_atom` with `f = 1` |

## §15.1.4 Some geometrically ergodic chains on countable spaces

| Source | Claim | Lean |
| --- | --- | --- |
| p. 370 | Forward recurrence time chain: `E_1[r^{τ_1}] = Σₙ rⁿ p(n)` | `fwdRec_kendallMoment` (`fwdRecKernel`, carried; the renewal state is `0`, `p(0) = 0`), `fwdRec_isKendall_iff` |
| p. 370 | The chain is geometrically ergodic iff `p` has geometrically decreasing tails | `fwdRec_tails_of_isGeomErgodicAtom` (through Theorem 15.1.5) and `fwdRec_geomErgodic_of_tails` (through Theorem 15.1.4, for an aperiodic chain); `p` has unbounded support, so the chain is irreducible on `ℕ` (`fwdRec_isAccessibleAtom`, carried) |
| p. 370 | The duality between geometric tails and geometric rates recurs for many models | Not formalised (informal) |
| (15.20), p. 370 | `P(0, j) = γ_j`, `P(j, j) = β_j`, `P(j, 0) = 1 − β_j` for `j ∈ ℤ₊` | `nonGeomKernel` (`nonGeomMeas`; the last two rows for `j ≥ 1`), `nonGeomKernel_zero`, `nonGeomKernel_pos`, `isMarkovKernel_nonGeomKernel`; see corrections |
| p. 370 | `E_0[τ_0] = Σ_j γ_j [1 + (1 − β_j)⁻¹]` | Corrected: `nonGeom_meanReturnTime_zero` (`1 + Σ_{j ≥ 1} γ_j (1 − β_j)⁻¹`); `nonGeom_meanReturnTime_pos` (`E_j[τ_0] = (1 − β_j)⁻¹`, `j ≥ 1`) |
| (15.21), p. 370 | With `γ_j > 0` the chain is ergodic iff `Σ_j γ_j (1 − β_j)⁻¹ < ∞` | `nonGeom_isIrreducibleChain`, `nonGeom_isPositive_iff` (`γ_j > 0`, `β_j < 1` for `j ≥ 1`) |
| pp. 370–371 | `E_0[r^{τ_0}] ≥ r Σ_j γ_j E_j[r^{τ_0}]` and `P_j(τ_0 > n) = β_jⁿ`; if `β_j → 1` the chain is not geometrically ergodic, whatever `γ` | `nonGeom_tabooKernel_pos`, `nonGeom_tabooKernel_univ_pos`, `nonGeom_tabooKernel_zero_ge`, `nonGeom_kendallMoment_eq_top` (`E_0[r^{τ_0}] = ∞` for every `r > 1`), `nonGeom_not_geomErgodic` |
| p. 371 | No simple way to ensure the best rate for a particular state | Not formalised (informal) |
| p. 371 | The `3 × 3` matrix, with `π(0) = π(2) = 1/4`, `π(1) = 1/2` | `rateMatrix`, `rateMatrix_nonneg`, `rateMatrix_rowSum`, `rateKernel`, `isMarkovKernel_rateKernel`, `ratePi`, `ratePi_singleton`, `isInvariant_ratePi`; the powers: `rateKernel_pow_singleton`, `rateMatrix_pow_nonneg`, `rateMatrix_pow_row_zero`, `rateMatrix_pow_col_two`, `rateMatrix_pow_row_one` |
| p. 371 | The generating functions `U^{(z)}(0, 0)`, `U^{(z)}(1, 1)`, `U^{(z)}(2, 2)` | `U^{(z)}(1, 1)` as printed is wrong: `rateKernel_U11_counterexample` (`P²(1, 1) = 9/16`); the correct one, `1 + z/(2(1 − z)) + z/(4 − z)`, follows from `rateKernel_state_one` |
| p. 371 | The best rates for states `0` and `2` are `0`; the rate for state `1` is at least `ρ₁ > 1/4` | `rateKernel_pow_zero_two` (`Pⁿ(0, 0) = π(0)`, `Pⁿ(2, 2) = π(2)` for `n ≥ 1`). Corrected: `rateKernel_state_one` (`Pⁿ(1, 1) − π(1) = 4⁻ⁿ` for `n ≥ 1`; the rate `1/4` works and no smaller one does) |
| pp. 371–372 | Teugels' `(N + 1)`-state matrix: being symmetric, it has `π(k) = (N + 1)⁻¹` | `isInvariant_uniform_of_symm` (every symmetric transition matrix on a finite space; `matKernel`, `IsTransitionMatrix`, carried) |
| p. 372 | Its eigenvalues are `λ_k = β_{N+2−k} − α_{N+2−k}`, `Pᵐ(k, k) − (N + 1)⁻¹ = Σ_j s(k, j) λ_jᵐ`, and there are `N` different best rates | Not formalised (quoted from [384]) |
| p. 372 | A common rate is the most that can be said | Not formalised (informal) |

## §15.2.1 `f`-Kendall sets and `f`-geometrically regular sets

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 372–373 | The splitting route; the extension of Kendall atoms to sets | Not formalised (informal) |
| p. 373 | Kendall sets: `sup_{x ∈ A} E_x[κ^{τ_A}] < ∞` for some `κ > 1` | `IsKendall P A κ`, `IsKendallSet P A`; `kendallMoment`, `measurable_kendallMoment`, `kendallMoment_mono_r`, `kendallMoment_eq_one_add`, `kendallMoment_le_one_add` |
| (15.22), p. 373 | `f`-Kendall sets: `sup_{x ∈ A} E_x[Σ_{k<τ_A} f(Φ_k) κᵏ] < ∞` | `IsFKendall P f A κ`, `IsFKendallSet P f A`; `geomSum`, `measurable_geomSum`, `geomSum_one`, `geomSum_mono_r`, `geomSum_mono_f`, `geomSum_anti_set`, `geomSum_const_mul`, `le_geomSum`; `fKendall_bounds`, `IsFKendall.isKendall` (`f ≥ 1`) |
| p. 373 | `f`-geometrically regular sets: for each `B ∈ B⁺(X)` some `r > 1` has `sup_{x ∈ A} E_x[Σ_{k<τ_B} f(Φ_k) rᵏ] < ∞` | `IsFGeomRegularSet P ψ f A`; `IsFGeomRegularSet.subset`, `IsFGeomRegularSet.mono`, `IsFGeomRegularSet.of_le_const_mul` |
| p. 373 | An `f`-geometrically regular set is `f`-regular | `IsFGeomRegularSet.isFRegularSet`, `fSumReturn_le_geomSum` (`IsFRegularSet`, `fSumReturn`, carried) |
| (15.23), p. 373 | `U_C^{(r)}(x, B) = E_x[Σ_{k=1}^{τ_C} 1_B(Φ_k) rᵏ]` | `geomTaboo P C r (B.indicator 1) x` |
| Theorem 15.2.1, p. 373 | For a `ψ`-irreducible chain, `C` is a petite `f`-Kendall set iff `C` is `f`-geometrically regular and `C ∈ B⁺(X)` | False as stated: `theorem_15_2_1_counterexample` (`C = ∅`). Corrected: `theorem_15_2_1` (`C` non-empty, `f ≥ 1`); `theorem_15_2_1_bound` (the bound `U_B^{(r)}(x, f) ≤ U_C^{(κ)}(x, f) + K E_x[κ^{τ_C}] + K` for every `x`) |
| p. 373 | Proof of (ii) ⇒ (i): a geometrically regular set is regular, hence petite by Proposition 11.3.8; of `C ∈ B⁺(X)`: a Kendall set is Harris recurrent, then Proposition 9.1.1 | `theorem_14_2_4` (carried) in the proof of `theorem_15_2_1` |
| p. 374 | `M(r) = sup_C E_x[r^{τ_C}] ≤ M(κ)^ε` by Jensen's inequality, so `M(r) → 1` as `r ↓ 1` | Replaced by `tpow_le_one_add` (`rᵗ ≤ 1 + (r − 1)/(κ − 1) κᵗ`), `exists_rate`; `seqOneLt`, `one_lt_seqOneLt`, `seqOneLt_ne_top`, `tendsto_seqOneLt`, `tendsto_seqOneLt_pow`, `exists_pow_mul_lt_one` |
| p. 374 (used throughout) | Powers `rᵗ` of hitting times, with `r^∞ = ∞`; the strong Markov property for geometrically weighted sums | `tpow`, `tpow_top`, `tpow_coe`, `tpow_some`, `one_le_tpow`, `tpow_mono`, `tpow_mono_left`, `tpow_add`, `tpow_sq`, `pow_eq_one_add_sum`, `tpow_eq_one_add`, `tsum_eq_top_of_one_le`, `measurable_tpow_comp`, `tsum_indicator_pow_le_tpow`; `measurable_sumBefore_geom`, `measurable_sumBefore_geomTaboo`, `measurable_sumBefore_geomG`, `sumBefore_top_eq`, `tpow_le_sumBefore_geomTaboo`, `sumBefore_geom_le_add`, `sumBefore_geomTaboo_le`; `lintegral_weight_shiftAt`, `sumBefore_le_shift_weighted`, `lintegral_sumBefore_le_weighted`, `geom_shift_weight`, `geomTaboo_shift_weight`, `geomTaboo_le_stopping`, `geomSum_le_stopping`, `setLIntegral_tpow_mul_le`, and the bounds through an intermediate set `A`, `U_B^{(r)}(x, f) ≤ U_A^{(r)}(x, f) + (sup_A U_B^{(r)}) E_x[r^{τ_A}]` (`geomTaboo_le_add_mul`, `geomSum_le_add_mul`) |
| (15.24), p. 374 | `E_x[r^{τ_C(n)}] ≤ M(r)ⁿ⁻¹ U^{(r)}(x)` by the strong Markov property | `lintegral_tpow_returnTimeK_le`, `lintegral_tpow_returnTimeK_le_pow`; `lintegral_tpow_shiftAt`, `returnTimeK_add_eq`, `returnTimeK_succ_eq'`, `returnTimeK_le_succ`, `returnTimeK_mono`, `hittingAfter_succ_eq_add`, `le_hittingAfter_iff'`, `succ_le_of_lt_withTop` |
| p. 374 | The sample-path bound `Σ_{i=1}^{τ_B} rⁱ f(Φᵢ) ≤ Σₙ Σ_{j=τ_C(n)+1}^{τ_C(n+1)} rʲ f(Φⱼ) 1{τ_B > τ_C(n)}` | `sumBefore_le_tsum_returnTimeK`, `sumBefore_min_returnTimeK_le`, `firstReturn_eq_add_shift_of_lt`, `sumBefore_add_eq`, `sumBefore_le_of_le_at` |
| (15.25)–(15.26), p. 374 | `U_B^{(r)}(x, f) ≤ M_f(r) Σₙ E_x[1{τ_B > τ_C(n)} r^{τ_C(n)}]`; `xy ≤ γⁿx² + γ⁻ⁿy²` | `geomTaboo_trials` (the trials bound); `le_mul_sq_add_inv`; `measurableSet_lt_inter_eq`, `measurableSet_lt_stopping` |
| (15.27), pp. 374–375 | `P_x(τ_C(n) < τ_B) ≤ Rρⁿ`; for petite `C`, `P_x(τ_C(m₀) < τ_B) ≤ c < 1` and the strong Markov property | `measure_returnTimeK_lt_le`, `measure_returnTimeK_lt_le_pow`, `measure_returnTimeK_lt_anti`; `exists_returnTimeK_lt_le_half` (for petite `C` and `B ∈ B⁺(X)`, `P_y(τ_C(m) < τ_B) ≤ 1/2` for every `y`, from the bounded expected number of visits `lintegral_sumBefore_indicator_le`, carried, `natCast_le_sumBefore_indicator` and Markov's inequality); `natCast_le_sum_indicator_of_returnTimeK` |
| p. 375 | The rate `r` may depend on `B` | Not formalised (remark); the rate in `IsFGeomRegularSet` depends on `B` |

## §15.2.2 The geometric drift condition

| Source | Claim | Lean |
| --- | --- | --- |
| p. 375 | Drift inequalities as the route through skeletons and splitting, and as verifiable conditions | Not formalised (informal) |
| (V4), (15.28), p. 376 | `V : X → [1, ∞]`, `C` measurable, `β > 0`, `b < ∞`, `ΔV ≤ −βV + b 1_C` | `DriftV4 P V ρ b C` (`PV ≤ ρV + b 1_C` with `ρ = 1 − β`; `V ≥ 1`, `ρ < 1` and `b ≠ ∞` assumed where used); `DriftV4.le_add`, `DriftV4.mono`, `DriftV4.mono_set` |
| p. 376 | (V4) is (V3) with `f = βV` | `DriftV4.driftV3`, `DriftV4.driftV3_scaled` (`DriftV3`, carried) |
| Lemma 15.2.2 (i), p. 376 | For a `ψ`-irreducible chain, `{V < ∞}` is empty or absorbing and full | `lemma_15_2_2_i` (`ρ ≤ 1`, `b ≠ ∞`; full for every irreducibility measure) |
| Lemma 15.2.2 (ii), p. 376 | If (15.28) holds for a petite `C`, `V` is unbounded off petite sets | `lemma_15_2_2_ii` (`IsUnboundedOffPetite`) |
| p. 376 | Proof: `PV ≤ V + b`, Proposition 4.2.3; (V2) for `V/(1 − β)`, then Lemma 11.3.7 | (i): (V4) as (V3) (`DriftV4.driftV3`) and Lemma 14.2.1 (`isAbsorbing_finite_of_driftV3`, `lemma_14_2_1`, carried); `DriftV4.le_add`. (ii): `DriftV4.driftV2_scaled`, `theorem_11_3_4`, `isPetite_meanHitTime_le` (carried) |
| (15.29), p. 376 | `G_C^{(r)} = I + I_{Cᶜ} U_C^{(r)}`, `G_C^{(r)}(x, B) = E_x[Σ_{k=0}^{σ_C} 1_B(Φ_k) rᵏ]` | `geomG`, `geomG_eq`, `geomG_of_mem`, `le_geomG`, `geomG_le`, `measurable_geomG`, `geomG_one` (`gKernelFn`, carried), `geomG_mono_r`, `geomG_mono_f` |
| Lemma 15.2.3, (15.30), p. 376 | `P G_C^{(r)} = r⁻¹ G_C^{(r)} − r⁻¹ I + r⁻¹ I_C U_C^{(r)}`, so `ΔG_C^{(r)} ≤ −βG_C^{(r)} + r⁻¹ I_C U_C^{(r)}` with `β = 1 − r⁻¹` | `lemma_15_2_3` (as `r P G_C^{(r)} + f = G_C^{(r)} + 1_C U_C^{(r)}`, for every `r ∈ (0, ∞)`) |
| (15.31), p. 377 | `U_C^{(r)} = rP + rP I_{Cᶜ} U_C^{(r)}` | `geomTaboo_eq` (`U_C^{(r)}(x, f) = r ∫ P(x, dy) G_C^{(r)}(y, f)`) |
| Theorem 15.2.4, p. 377 | For a `ψ`-irreducible chain with an `f`-Kendall `C ∈ B⁺(X)`, `V = G_C^{(κ)}(·, f) ≥ f` solves (V4) | `theorem_15_2_4` (`f ≥ 1`; `V ≤ M` on `C`; neither `ψ`-irreducibility nor `C ∈ B⁺(X)` is used) |

## §15.2.3 Other solutions of the drift inequalities

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 15.2.5, (15.32), p. 377 | Under (V4), for `r ∈ (1, (1 − β)⁻¹)` there is `ε > 0` with `E_x[Σ_{k<τ_B} V(Φ_k) rᵏ] ≤ ε⁻¹ r⁻¹ V(x) + ε⁻¹ b E_x[Σ_{k<τ_B} 1_C(Φ_k) rᵏ]`, and for `B = C` the bound (15.32) | `theorem_15_2_5` (`ε = r⁻¹ − ρ`; every measurable `B`); `geomSum_indicator_le` (`E_x[Σ_{k<τ_C} 1_C(Φ_k) rᵏ] ≤ 1_C(x)`), `sumBefore_indicator_firstReturn_le` |
| pp. 377–378 | Proof: `Z_k = rᵏ V(Φ_k)` and Proposition 11.3.2 | `geom_comparison` (the multiplied form, for every stopping time; `comparison_theorem`, carried) |
| Theorem 15.2.6, p. 378 | For a `ψ`-irreducible chain with (V4) for a petite `C`, a set on which `V` is bounded is `V`-geometrically regular | `theorem_15_2_6` (`V ≥ 1`, `ρ < 1`, `b ≠ ∞`; `A` measurable) |
| (15.33)–(15.34), pp. 378–379 | `D = {V ≤ (M + b)/(r⁻¹ − ρ)}` contains `A`, is in `B⁺(X)`, satisfies (V4) and is `V`-Kendall | `exists_kendall_sublevel` (`V` finite somewhere; `D` petite, in `B⁺(X)`, with (V4) and `E_x[Σ_{k<τ_D} V(Φ_k) sᵏ] ≤ d V(x)`); `exists_sublevel_pos`, `exists_one_lt_mul_lt_one`, `lt_inv_of_mul_lt_one` |
| p. 379 | `D` is petite by Lemma 15.2.2 (ii), hence `V`-geometrically regular by Theorem 15.2.1; subsets inherit this | `lemma_15_2_2_ii` in the proof of `exists_kendall_sublevel`; `theorem_15_2_1` and `IsFGeomRegularSet.subset` in the proof of `theorem_15_2_6` |
| Theorem 15.2.7, p. 379 | From an `f`-Kendall `C ∈ B⁺(X)`, some `V ≥ f` has increasing `V`-geometrically regular sets `C_V(i)` whose union is full | False as stated: `theorem_15_2_7_counterexample` (the forward recurrence time chain of `heavyRenewal`, carried; `geomSum_univ_one`). Corrected: `theorem_15_2_7` (`C` petite and non-empty, `f ≥ 1`; `V = G_C^{(κ)}(·, f)`, `C_V(n) = {V ≤ n}`, union `{V < ∞}` full and absorbing) |
| Lemma 15.2.8, (15.35), p. 379 | (V4) holds with a petite set iff `V` is unbounded off petite sets and `PV ≤ λV + L`, `λ < 1`, `L < ∞` | `lemma_15_2_8` (`V ≥ 1`) |
| p. 379 | For a `ψ`-irreducible T-chain, (15.35) with a coercive `V` gives (V4) and `V`-geometric ergodicity | Not formalised (remark); `lemma_15_2_8` with petite compact sets is used for the models of §15.5 |
| pp. 379–380 | Larger `V` gives larger bounds; Section 16.2.2 | Not formalised (informal, forward reference) |
| Lemma 15.2.9, p. 380 | (V4) for `V` and a petite set gives (V4) for `√V` and a petite set | `lemma_15_2_9` (`V ≥ 1`); `lintegral_rpow_half_le` (Jensen's inequality for `√`). The bound of the proof is replaced; see corrections |

## §15.3.1 `f`-Geometric regularity of chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 380 | The two aspects of `f`-geometric regularity needed for the convergence theorems | Not formalised (informal) |
| (15.36), p. 381 | `Φ` is `f`-geometrically regular: a petite `C` and `κ > 1` with `E_x[Σ_{k<τ_C} f(Φ_k) κᵏ]` finite for all `x` and bounded on `C` | `IsFGeomRegularChain P f`; `IsFGeomRegularOn P f S` (finite on `S`: the chain restricted to `S`), `IsFGeomRegularOn.mono`, `IsFGeomRegularOn.of_le_const_mul` |
| p. 381 | For `κ = 1` this is `f`-regularity; boundedness on `C` gives the `f`-geometric regularity of `C` by Theorem 15.2.1 | Not stated separately (remark); `theorem_15_2_1` |
| Proposition 15.3.1, (15.37), p. 381 | Under (15.36), for each `B ∈ B⁺(X)` some `r > 1` and `c(B) < ∞` have `U_B^{(r)}(x, f) ≤ c(B) U_C^{(r)}(x, f)` | `proposition_15_3_1` (for a petite `C` that is `f`-Kendall of rate `κ`, `f ≥ 1`; the right side has `U_C^{(κ)}`; see corrections) |
| Proposition 15.3.2, p. 381 | One petite `f`-Kendall set gives `X = S_f ∪ N` with `S_f` full and absorbing and `Φ` `f`-geometrically regular on `S_f` | `proposition_15_3_2` (`C` non-empty, `f ≥ 1`; `S_f = {G_C^{(κ)}(·, f) < ∞}`, and the chain is also `G_C^{(κ)}(·, f)`-geometrically regular there) |
| (15.38), p. 381 | Proof: `V(x) ≤ E_x[Σ_{n<τ_C} V(Φₙ) κⁿ] ≤ ε⁻¹ κ⁻¹ V(x) + ε⁻¹ c 1_C(x)` | `theorem_15_2_4`, `theorem_15_2_5`, `lemma_15_2_2_i` in the proof of `proposition_15_3_2` |
| Theorem 15.3.3, p. 382 | (V4) for a petite set with `V` everywhere finite makes `Φ` `V`-geometrically regular with `U_B^{(r)}(x, V) ≤ c(B) V(x)`; conversely an `f`-geometrically regular chain has an everywhere finite `V ≥ f` solving (V4) for a petite set | `theorem_15_3_3` (`V ≥ 1` finite at one point; `V`-geometric regularity on `{V < ∞}`, and the bound for every `x`), `theorem_15_3_3_converse` (`f ≥ 1`; `V = G_C^{(κ)}(·, f)`) |
| p. 382 | Proof: a petite `D` on which `V` is bounded, as in Theorem 15.2.6, and Proposition 15.3.1 | `exists_kendall_sublevel`, `theorem_15_2_1_bound` in the proof of `theorem_15_3_3` |

## §15.3.2 Connections between `Φ` and `Φⁿ`

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 15.3.4 (i), (15.39), p. 382 | For a `ψ`-irreducible aperiodic chain, (V4) with a petite `C` gives (V4) for every `n`-skeleton with a set petite for it | `theorem_15_3_4_i` (`V ≥ 1`, `ρ < 1`, `b ≠ ∞`; the set is small for `Pᵐ`, `IsSmall`, carried) |
| p. 382 | Proof: `PⁿV ≤ ρⁿV + b Σ_{i<n} Pⁱ 1_C ≤ ρⁿV + bm 1_{C′} + ε` by Lemma 14.2.8 | `DriftV4.iterate`, `lemma_14_2_8` (carried); `DriftV4.pow_le` (`PⁱV ≤ V + bi`) |
| Theorem 15.3.4 (ii), p. 382 | An `f`-geometrically regular `C` is `f`-geometrically regular for every `Pⁿ` | `theorem_15_3_4_ii` (`C ∈ B⁺(X)`, `f ≥ 1`); `skeleton_geomRegular_of_set` |
| p. 383 | Proof: (V4) for `G_C^{(r)}(·, f)` and Theorem 15.2.6 for the skeleton | `skeleton_geomRegular_of_set` (`theorem_15_3_4_i`, then `theorem_15_2_6` for the skeleton); `IsPetite.of_skeleton` (a set petite for a skeleton is petite for the chain) |
| Theorem 15.3.5, p. 383 | An `f`-geometrically regular aperiodic chain has `f`-geometrically regular skeletons | `theorem_15_3_5` (`f ≥ 1`); `skeleton_geomRegular_of_chain`, `exists_point_of_ne_zero` |
| (14.22), p. 383 | `g^{(m)} = Σ_{i<m} Pⁱg` | `fSkel` (carried); `fSkel_le_of_driftV4` (`f^{(m)} ≤ m (1 + bm) V` under (V4), for `f ≤ V`) |
| Theorem 15.3.6, p. 383 | For a `ψ`-irreducible aperiodic chain, `C ∈ B⁺(X)` is `f`-geometrically regular iff it is `f^{(m)}`-geometrically regular for one, and then every, `m`-skeleton | `theorem_15_3_6` (`f ≥ 1`); `IsFGeomRegularSet.of_skeleton` |
| p. 383 | Proof: by the Markov property the skeleton sums dominate `r⁻ᵐ E_x[Σ_{j<τ_B} rʲ f(Φⱼ)]`; conversely (V4) for `V^{(m)}` and Theorem 15.3.3 | `geomSum_le_skeleton`, `exists_one_lt_pow_le`, in `IsFGeomRegularSet.of_skeleton`; `skeleton_geomRegular_of_set` |
| Theorem 15.3.7, p. 383 | `Φ` is `f`-geometrically regular iff each `m`-skeleton is `f^{(m)}`-geometrically regular | `theorem_15_3_7` (`f ≥ 1`); `isFGeomRegularChain_of_skeleton` (one skeleton suffices), `IsFGeomRegularOn.of_skeleton` (on a set `S`) |

## §15.4 `f`-Geometric ergodicity for general chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 384 | The route: atoms, strongly aperiodic chains, then a strongly aperiodic skeleton | Not formalised (informal) |
| Theorem 15.4.1, p. 384 | For a `ψ`-irreducible aperiodic chain with an `f`-Kendall petite `C`, there are `κ > 1` and a full absorbing `S_f^κ` on which `E_x[Σ_{k<τ_C} f(Φ_k) κᵏ] < ∞`, and `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖_f ≤ R E_x[Σ_{k=0}^{τ_C} f(Φ_k) κᵏ]` there | `theorem_15_4_1` (`C` non-empty, `f ≥ 1`; `S_f^κ = {G_C^{(κ)}(·, f) < ∞}`; the bound with `G_C^{(κ)}(x, f)`, for every `x`; it also gives positivity and `π(f) < ∞`); see corrections |
| (15.40), p. 384 | `V(x) = E_x[Σ_{k=0}^{σ_C} f(Φ_k) κᵏ] ≥ f(x)` solves (V4), is bounded on `C`, and `{V < ∞}` is absorbing, full and contains `C` | `theorem_15_2_4`, `lemma_15_2_2_i` in the proof of `theorem_15_4_1` |
| p. 384 | Proof (i): `C` contains an accessible atom; Theorem 15.1.4, (15.18) and (15.37) | Not used: the proof goes through (iii) directly. The atom case is `theorem_15_1_4` |
| (15.41), pp. 384–385 | Proof (ii), strongly aperiodic: `E_x[Σ_{k=1}^{τ_C} V(Φ_k) rᵏ] ≤ c V(x)`; in the split chain `α̌` is `V̌`-Kendall, and step (i) gives `V`-geometric ergodicity | `Minorization.tsum_fNorm_le_geom` (a minorization on `C ∈ B⁺(X)` with `ν(C) > 0` and `U_C^{(r₀)}(·, f)` bounded on `C`); `Minorization.geomTaboo_split_le`, `Minorization.measure_returnTimeK_one_lt_le`, `Minorization.lintegral_pathKernel_split`, `Minorization.lintegral_geomTaboo_split`, `Minorization.lintegral_kendallMoment_split`, `geomTaboo_trials`, `tsum_fNorm_le_geom_atom` |
| (15.42), p. 385 | Proof (iii): `C` is `ν_m`-small with `ν_m(Cᶜ) = 0`; the skeleton satisfies `E_x[Σ_{k=1}^{τ_C^m} V(Φ_k) rᵏ] ≤ d V(x)` | `geometric_ergodic_of_driftV4`: `exists_skeleton_minorization` (carried), `Minorization.restrict` (to a set where `V` is bounded), `eventually_measure_inter_sublevel_pos`, `measure_inter_of_compl_null`, `theorem_15_3_4_i`, `theorem_15_3_3` for the skeleton |
| (15.43), pp. 385–386 | `‖Pⁿ⁺¹(x, ·) − π‖_V ≤ (1 + b) ‖Pⁿ(x, ·) − π‖_V`, then `k = nm + i` | Replaced by Lemma 14.3.2 (i) with `V^{(m)}` (`lemma_14_3_2_i_measure`, carried) and `V^{(m)} ≤ m (1 + bm) V` (`fSkel_le_of_driftV4`); `tsum_eq_tsum_sum_block` (carried) |
| p. 386 | Care is needed for the converse: the inequalities of the Regenerative Decomposition go one way | Not formalised (remark) |
| Theorem 15.4.2, p. 386 | An `f`-geometrically ergodic chain is `f`-geometrically regular on a full absorbing set | `theorem_15_4_2` (`ψ`-irreducible, aperiodic, an invariant probability, `f ≥ 1`, `π(f) < ∞`, the sums finite on a full measurable set), `theorem_15_4_2_univ` (the sums finite everywhere, (15.7)) |
| (15.44), p. 386 | `Pⁿ(α, f) − π(f) ≥ (u − π(α)) ∗ t_f(n) + π(α) Σ_{j > n} t_f(j)`, from the last-exit decomposition (8.19) | False as printed: `eq_15_44_counterexample` (the flip chain at `n = 1`). Corrected: `atom_tail_le` (`π(α) Σ_{j > n} t_j ≤ ‖Pⁿ⁺¹(a, ·) − π‖_f + Σ_{k ≤ n} |u(k) − π(α)| t_{n−k}`); `IsAtom.lintegral_pow_succ_eq` (`Pⁿ⁺¹(a, f) = Σ_{k ≤ n} u(k) t_{n−k}`), `lintegral_le_add_fNorm` |
| (15.45)–(15.46), pp. 386–387 | Truncate, multiply by `sⁿ`, sum to `N`; `d(s) = Σ sⁿ |u(n) − π(α)|`; Fubini; if `α` were not `f`-Kendall, the right side would tend to `∞` | `tsum_pow_mul_eq_add` (`Σⱼ sʲ g_j = Σⱼ g_j + (s − 1) Σₙ sⁿ Σ_{j > n} g_j`); the truncation and a direct bound replace the contradiction in the proof of `theorem_15_4_2_atom` |
| p. 387 | With an accessible atom: `α` is `f`-Kendall of some rate `s`, and Proposition 15.3.2 gives a full absorbing `S` | `theorem_15_4_2_atom` (`U_α^{(s)}(a, f) < ∞` for some `s > 1`, and `{U_α^{(s)}(·, f) < ∞}` full and absorbing), `theorem_15_4_2_atom_regular` (with `f` bounded on `α`: `α` is `f`-Kendall, and `f`-geometric regularity on a full absorbing set) |
| p. 387 | Without an atom: `Σ rⁿ |P^{nm}(x, f) − π(f)| < ∞` for every skeleton; the same for the split chain; the first part, then Theorem 15.3.7 | Incomplete (see corrections). Proved by another route: `atom_geomTaboo_ne_top` (the atom argument with the test functions `1_α` and `f`), `atom_tail_le_tsub`, `tsub_lintegral_le_fNorm`, `tsub_lintegral_le`, `lintegral_tsub_le`, `sum_tsub_le_sum_tsub`, `tsub_le_ofReal_abs`, `ofReal_abs_le_tsub_add_tsub`, `Minorization.splitKernel_pow_succ_checkAlpha`, `Minorization.lintegral_splitKernel_pow_succ`, `Minorization.lintegral_splitK_fst`, `lintegral_lintegral_pow`, `lintegral_fSkel_pow`, `tsum_ne_top_of_succ`, `IsAtom.driftV4_geomG`, `Minorization.driftV4_of_split_drift`, `theorem_15_3_3`, `IsFGeomRegularOn.of_skeleton`, `proposition_15_3_2` |
| p. 387 | Geometric ergodicity need not imply `f`-geometric ergodicity even with `π(f) < ∞`; the example (16.24) | Not formalised (forward reference) |
| Theorem 15.4.3, (15.47), p. 387 | For an aperiodic positive Harris chain and a `ν`-small `C ∈ B⁺(X)` with `ν(C) > 0` and `|∫_C ν_C(dx) (Pⁿ(x, C) − P^∞(C))| ≤ M_C ρ_Cⁿ`, the chain is geometrically ergodic on a full absorbing set | `theorem_15_4_3` (positivity suffices; `IsSmallSet P m ν C`, carried; no condition on the limit `p`; `Σₙ rⁿ ‖Pⁿ(x, ·) − π‖ ≤ R W(x)` on `{W < ∞}` for every invariant probability) |
| p. 388 | Proof: as in Theorem 13.3.5 the split atom of the skeleton is geometrically ergodic; then step (iii) of Theorem 15.4.1 | `hasKendallPetite_of_split_local`: `Minorization.atomRenewal_split_succ`, `Minorization.isKendall_split_of_local` (the split atom is Kendall, by Theorem 15.1.5), `Minorization.driftV4_of_isKendall_split` (`x ↦ ∫ Ǧ dx*` solves (V4)), `hasKendallPetite_of_isFGeomRegularOn`; then `hasDriftV4_of_hasKendallPetite`, `geometric_ergodic_of_driftV4` |
| p. 388 | (15.47) is implied by (15.1), which closes the circle of Theorem 15.0.1 | `hasKendallPetite_of_isLocallyGeomErgodic` (with `exists_concentrated_minorization`) |

## §15.5.1 Bernoulli random walk

| Source | Claim | Lean |
| --- | --- | --- |
| p. 388 | `P(x, x + 1) = p`, `P(x, x − 1) = 1 − p` for `x > 0`, `P(0, 0) = 1 − p` | `bernoulliWalk p` (`reflectedWalkKernel (bernoulliStep p)`, carried), `bernoulliStep`, `isProbabilityMeasure_bernoulliStep`, `isMarkovKernel_bernoulliWalk`, `lintegral_bernoulliWalk`, `bernoulliWalk_singleton`, `bernoulliWalk_isIrreducibleChain` (`0 < p < 1`) |
| (15.48), p. 388 | The first-passage generating functions `A_x(z) = A₁(z)ˣ` are analytic for `z < 2/√(p(1 − p))`, so `p < 1/2` gives geometric ergodicity | Not formalised. The same conclusion is `bernoulliWalk_geometricErgodic` |
| p. 388 | For `V(x) = zˣ`, `ΔV(x) = zˣ[(1 − p)z⁻¹ + pz − 1] = −βV(x)` for `x > 0` and `z` close to `1` when `p < 1/2` | `bernoulliWalk_driftV4` (`PV = (pz + (1 − p)/z) V` off `0`), `bernoulli_rate_lt_one` |
| p. 388 | The walk is geometrically ergodic for `p < 1/2` | `bernoulliWalk_geometricErgodic` (`0 < p < 1/2`; `V`-geometric ergodicity with `V(x) = zˣ`, through `theorem_15_0_1_consequences`) |
| p. 389 | Random walks on a half line with exponentially decreasing right tails; Section 16.1.3 | Not formalised (forward reference) |

## §15.5.2 Autoregressive and bilinear models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 389 | Autoregressive models converge geometrically without exponential innovations | Not formalised (informal) |
| (15.49), p. 389 | For `Xₙ = αXₙ₋₁ + Wₙ` and `V(x) = |x| + 1`, `E_x[V(X₁)] ≤ |α| V(x) + E|W| + 1` | `ar1_eq_15_49` (`ar1Kernel`, carried); `ar1Kernel_eq_bilinearKernel` |
| p. 389 | With an everywhere positive density of `W`, `E|W| < ∞` and `|α| < 1`, the simple linear model is geometrically ergodic | `ar1_geometricErgodic` (`ψ`-irreducibility, aperiodicity and petite compact sets assumed in place of the density) |
| (15.50), p. 389 | `X_{k+1} = θX_k + bW_{k+1}X_k + W_{k+1}` | `bilinearKernel Γ θ b` (carried) |
| (15.51)–(15.52), p. 390 | `E[|X_{k+1}| | X_k = x] ≤ E|θ + bW| |x| + E|W|`, so `V(x) = |x| + 1` solves (V4) when `E|θ + bW| < 1`; the chain is then `V`-geometrically ergodic | `bilinear_eq_15_51`; `bilinear_le_mul_add` (for `V(x) = |x|ᵏ + 1` under `E|W|ᵏ < ∞`, `E|θ + bW|ᵏ < 1`, `k ≥ 1`; `pow_affine_le`, `bilinear_lintegral_pow_le`, carried), `isUnboundedOffPetite_enorm_pow`, `bilinear_geometricErgodic` (`ψ`-irreducibility, aperiodicity and petite compact sets assumed; `k = 1` is (15.52)) |
| p. 390 | Under this condition the chain is irreducible and aperiodic | Not formalised; hypotheses of `bilinear_geometricErgodic` |
| p. 390 | With `θ² + b²σ_w² < 1`, `V(x) = x²` solves (V4); `Σₙ rⁿ |∫ Pⁿ(x, dy) y² − ∫ π(dy) y²| < c (x² + 1)` | `bilinear_variance_convergence` (centred `W` with finite variance; `V(x) = x² + 1`; `bilinear_condition_14_32`, carried) |

## §15.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 390–391 | History: Kendall, Vere-Jones, Teugels, Nummelin and Tweedie, Nummelin and Tuominen, Chan, Meyn and Tweedie, Popov, Feigin and Tweedie; bounds on rates; the second-printing note and the commentary for the second edition | Not formalised (commentary) |
