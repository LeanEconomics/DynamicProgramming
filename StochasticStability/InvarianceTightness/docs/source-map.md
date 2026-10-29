# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 12, pp. 288–310, with Lemma D.5.3 and Proposition D.5.6 of Appendix D as the
chapter uses them. Equation numbers and assumption labels are the book's. Lean names are relative
to `MeynTweedie.InvarianceTightness`; names from Mathlib are marked as such. Names marked
"carried" are in the modules copied from the Chapter 1–10 projects (see the
[README](../README.md)). "Feller" in the chapter is the weak Feller property, `IsWeakFeller P`
(carried): `P(·, O)` is lower semicontinuous for every open `O`. `P̄ⁿ` is `cesaroKernel P n`, `K_ε`
is `resolvent P ε` (carried), and `μP` is `P ∘ₘ μ`. Every place where the Lean statement departs
from the book is listed in [corrections](corrections.md).

## Chapter 12 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 288 | Positive Harris chains settle to `π`; a limiting measure for `Pⁿ` may generate an invariant measure (10.4); chains on topological spaces without ψ-irreducibility | Not formalised (informal) |
| (12.1), p. 288 | `{μₖ}` is tight if for each `ε > 0` some compact `C` has `liminf_k μₖ(C) ≥ 1 − ε` | Used in this form inside `IsBoundedInProbabilityOnAverage`; for probabilities it is tightness in Mathlib's sense, `IsTightMeasureSet` (Mathlib): `isTightMeasureSet_range_of_liminf` |
| (12.2), p. 288 | `Φ` is bounded in probability on average if `{P̄ᵏ(x, ·)}` is tight for each `x`, with `P̄ᵏ = k⁻¹ Σ_{i=1}^{k} Pⁱ` | `cesaroKernel` (the sampled kernel of `uniformDist`, carried), `cesaroKernel_apply_eq`, `cesaroKernel_apply`, `lintegral_cesaroKernel`, `integral_cesaroKernel`, `isMarkovKernel_cesaroKernel` (`n ≥ 1`), `cesaroKernel_univ_le`, `IsBoundedInProbabilityOnAverage`; `IsBoundedInProbability.onAverage` (boundedness in probability, `IsBoundedInProbability`, carried, implies it) |
| Theorem 12.0.1 (i), p. 289 | A weak Feller chain bounded in probability on average has an invariant probability | `theorem_12_0_1_i` (`X` nonempty) |
| Theorem 12.0.1 (ii), p. 289 | For an e-chain bounded in probability on average there is a weak Feller transition function `Π` with every `Π(x, ·)` invariant and `P̄ⁿ(x, f) → Π(x, f)` for bounded continuous `f` | `theorem_12_0_1_ii` (`Π = eChainLimit he`; `IsEChain`, carried; the averages `P̄ⁿ⁺¹`) |
| p. 289 | Proof: Theorem 12.1.2 and §12.4 | `theorem_12_1_2_ii`; `theorem_12_4_1_i`, `theorem_12_4_1_iii`, `continuous_integral_eChainLimit` (by Dini's theorem) and `tendsto_integral_bcf_of_cc` (vague convergence without loss of mass is weak convergence), in the proof of `theorem_12_0_1_ii` |
| p. 289 | Overview: weak convergence as a construction, (V2) and e-chains, Neveu's kernels, (V1) and σ-finite invariant measures | Not formalised (informal); the results are `theorem_12_4_5`, the module `GeneralizedSampling` and `theorem_12_3_3` |

## §12.1.1 Weak and vague convergence

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 12.1.1, p. 289 | A chain bounded in probability on average is non-evanescent | `proposition_12_1_1` (`IsNonEvanescent`, carried) |
| (12.3), p. 289 | `P_x{⋃_{j ≥ n} {Φⱼ ∈ C}} ≥ Pⁿ(x, C)` | `inequality_12_3` (`pathKernel`, carried) |
| pp. 289–290 | Proof: an evanescent chain has `limsup_n P_x{⋃_{j ≥ n} {Φⱼ ∈ C}} ≤ 1 − ε` for every compact `C` | In the proof of `proposition_12_1_1`: the Cesàro means are eventually at most `P_x{Φⱼ ∈ C for some j ≥ N}` (`liminf_cesaro_le`; `ioSet`, carried) |
| p. 290 | Tightness gives weak limits (Billingsley); Fatou gives subinvariance; convergence in the weak topology of §D.5 | Not formalised (informal); the limits used are vague limits (`vagueLimit`) and, for Proposition 12.1.4, Mathlib's weak convergence of probability measures |

## §12.1.2 Feller chains and invariant probability measures

| Source | Claim | Lean |
| --- | --- | --- |
| p. 290 | The resolvent `K_{a_ε} = (1 − ε) Σₖ εᵏ Pᵏ` | `resolvent` (carried), `integral_resolvent`, `lintegral_resolvent`, `resolvent_univ_le` |
| Theorem 12.1.2 (i), (12.4)–(12.5), p. 290 | For a weak Feller chain without an invariant probability, `P̄ⁿ(x, C) → 0` and `K_{a_ε}(x, C) → 0` as `ε ↑ 1`, uniformly in `x`, for compact `C` | `theorem_12_1_2_i` (for every `ε > 0`, eventually `P̄ⁿ(x, C) ≤ ε` for all `x`), `theorem_12_1_2_i_resolvent`, `tendsto_resolvent_bound` |
| Theorem 12.1.2 (ii), p. 290 | A weak Feller chain bounded in probability on average has an invariant probability | `theorem_12_1_2_ii` (`X` nonempty) |
| p. 290 | Proof: the open sets `A_k = {P̄ᵏ f > δ}`, points `xᵢ ∈ A_{Nᵢ}`, `λᵢ = P̄^{Nᵢ}(xᵢ, ·)` | In the proof of `theorem_12_1_2_i`, with `exists_cc_indicator_le` (a function of `C_c(X)` above `1_C`) and `measureReal_le_integral_of_indicator_le` |
| Proposition D.5.6, p. 290 | The sub-probabilities are sequentially compact for vague convergence | Replaced by ultrafilter limits: `vagueFunctional` (the positive functional `f ↦ lim_U ∫ f dμᵢ` on `C_c(X)`), `vagueLimit` (its Riesz–Markov–Kakutani measure, Mathlib), `tendsto_integral_vagueLimit`, `vagueLimit_univ_le`, `isFiniteMeasure_vagueLimit`, `exists_tendsto_integral` |
| (12.6), p. 291 | `∫ f dλ∞ ≥ liminf ∫ f dλᵢ ≥ δ > 0` | In the proof of `exists_isInvariant_of_vague` |
| (12.7), (D.6), p. 291 | `∫ g dλ∞ ≥ ∫ Pg dλ∞` for `g ∈ C_c(X)`, `g ≥ 0`, by the telescoping bound and (D.6) | `abs_integral_kfunR_cesaro_sub_le` (`|∫ Pg dP̄ⁿ(x) − ∫ g dP̄ⁿ(x)| ≤ 2‖g‖/n`), `abs_integral_kfunR_resolvent_sub_le`, `sum_Icc_succ_sub_sum_Icc`, `integral_kfunR_pow`, `integral_vagueLimit_le` ((D.6) for bounded continuous `g ≥ 0`), `exists_cutoff_seq`, `cutoff_eventually_eq_one`, `kfunR_add_const`; `exists_isInvariant_of_vague` (Foguel's argument) |
| p. 291 | By regularity of finite measures, `λ∞ ≥ λ∞P` forces `λ∞ = λ∞P` | `isInvariant_of_integral_le` (a finite `ν` with `∫ Pg dν ≤ ∫ g dν` for every nonnegative `g ∈ C_c(X)` is invariant) |
| p. 291 | Proof of (ii): `P̄ʲ(x, C) > 1 − ε` for large `j`, so (12.4) fails | In the proof of `theorem_12_1_2_ii`; the general form is `exists_isInvariant_of_frequently` (`P̄ⁿ(x, C) ≥ δ > 0` infinitely often, for one `x` and one compact `C`) |
| Proposition 12.1.3, (12.8), p. 291 | For a weak Feller chain and a coercive `V` with `liminf_k E_x[V(Φₖ)] < ∞` for one `x`, an invariant probability exists | False as stated: `proposition_12_1_3_counterexample` (`LiminfCounterexample`). Corrected: `proposition_12_1_3` (`liminf_n n⁻¹ Σ_{k=1}^{n} E_x[V(Φₖ)] < ∞`), `proposition_12_1_3_of_eventually_le` (`E_x[V(Φₖ)] ≤ M` for all large `k`); `half_le_measure_closure_sublevel` (`IsCoercive`, carried) |
| p. 291 | The condition (12.8) is weaker than that of Lemma D.5.3 | The Lemma D.5.3 form is `proposition_12_1_3_of_eventually_le`; the counterexample shows that the weaker condition does not suffice |
| p. 291 | The two drawbacks: no uniqueness, no convergence of `P̄ⁿ(x, ·)` in general | Not formalised (remark) |
| Proposition 12.1.4, (12.9), p. 292 | For a weak Feller chain bounded in probability on average with a unique invariant probability `π`, `P̄ⁿ(x, ·) → π` weakly | `proposition_12_1_4` (uniqueness among invariant probabilities; `cesaroPM`, the averages `P̄ⁿ⁺¹(x, ·)` as elements of Mathlib's `ProbabilityMeasure`), `kfunBCF`, `kfunBCF_apply` |
| p. 292 | Proof: weak sequential compactness and invariance of the limits | Prokhorov's theorem (`isCompact_closure_of_isTightMeasureSet`, Mathlib) with `isTightMeasureSet_range_of_liminf`; invariance of cluster points from `abs_integral_kfunR_cesaro_sub_le`, in the proof of `proposition_12_1_4` |
| p. 292 | Comparison with Proposition 6.4.2 | Not formalised (remark) |
| §§12.2–12.3 | The deterministic successor chain on `ℕ`, used for counterexamples | `succKernel`, `isMarkovKernel_succKernel`, `succKernel_pow_apply` |

## §12.1.2 The counterexample to Proposition 12.1.3

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 12.1.3, p. 291 | (12.8) with `Pᵏ` | `proposition_12_1_3_counterexample`: the deterministic chain `liminfCexKernel` of the map `liminfCexMap` on `ℕ × ℕ∞` is weak Feller (`continuous_liminfCexMap`, `isWeakFeller_liminfCexKernel`), `V(k, m) = k` is coercive (`isCoercive_liminfCex`), `liminf_k E_{(0,0)}[V(Φₖ)] = 0`, and no probability is invariant (`liminfCex_no_invariant`) |
| Chapter 6 | The standing hypothesis: `X` is a locally compact separable metric space | `nat_prod_enat_standing` (`ℕ × ℕ∞` is Hausdorff, locally compact, σ-compact, second countable and metrizable), `borelSpace_nat_prod_enat` |
| p. 291 | The finite `liminf` along the orbit of `(0, 0)` | The loops: `liminfCexMap_iterate_loop` (`Tʲ(0, m) = (j, m)` for `j ≤ m`), `exists_iterate_liminfCexMap` (the orbit of `(0, 0)` reaches `(0, m)` at some time `n ≥ m`), `liminfCexKernel_pow_apply` |

## §12.2 Generalized sampling and invariant measures

| Source | Claim | Lean |
| --- | --- | --- |
| p. 292 | The resolvent equation; randomized first entrance times include `τ_A` and times independent of `Φ` | Not formalised (informal) |
| (12.10)–(12.11), pp. 292–293 | `τ_h` with `P_x{τ_h = k | τ_h ≥ k, F^Φ_∞} = h(Φₖ)` | Not formalised as a random time; the kernels are defined by (12.14) |
| (12.12), p. 292 | `P_x{τ_h ≥ k | F^Φ_∞} = ∏_{i=1}^{k−1} (1 − h(Φᵢ))` | `iterate_killOp_one_eq` (`(P I_w)ⁿ 1 (x) = E_x[∏_{i=1}^{n} w(Φᵢ)]`; for `w = 1 − h` this is `P_x(τ_h > n)`) |
| p. 293 | `h = 1_B` gives `τ_B`; `h = ½ 1_B` flips a fair coin on each visit to `B`; the Athreya–Ney randomized stopping time | Not formalised as random times; for kernels, `genPotKernel_indicator` |
| p. 293 | The bivariate chain `Ψₖ = (Φₖ, Yₖ)` with `Yₖ` i.i.d. uniform on `[0, 1]` and independent of `Φ`, `A_h = {(x, u) : h(x) ≥ u}`, and `τ_h` a stopping time for `Ψ` | The path law `P_x ⊗ (uniform)^ℕ` (`Measure.infinitePi`, Mathlib, of `volume` on the unit interval) and the event `{Ψₖ ∈ A_h i.o.}` appear in the statement of `theorem_12_2_2_i`; `iIndepSet_preimage_of_iIndepFun`, `volume_unitInterval_le`. The bivariate chain as a Markov chain and `τ_h` as its stopping time are not formalised |
| (12.13), p. 293 | `U_h(x, B) = E_x[Σ_{k=1}^{τ_h} 1_B(Φₖ)]` | Not formalised; `U_h` is defined by (12.14) |
| (12.14), pp. 293–294 | `U_h = Σₖ P(I_{1−h}P)ᵏ` | `genPotKernel` (`Σₖ (P I_{1−h})ᵏ P`), `killKernel` (`P I_{1−h}`), `killOp`, `geomOp`, `lintegral_genPotKernel`, `lintegral_genPotKernel_eq_tsum`, `lintegral_killKernel`, `lintegral_killKernel_pow`, `isSFiniteKernel_genPotKernel`, `isFiniteKernel_killKernel`; `geomOp_eq`, `geomOp_eq'`, `geomOp_add`, `geomOp_le` (minimality), `killOp_add`, `killOp_weight_add`, `killOp_tsum`, `killOp_finsetSum`, `killOp_mono`, `iterate_killOp_add`, `iterate_killOp_kfun` |
| p. 294 | For `h ≡ 0`, `h = 1_B` and `h ≡ 1`: `U_h = U`, `U_B`, `P` | `genPotKernel_zero` (`potKernel`, carried), `genPotKernel_indicator` (`tabooPotKernel`, carried), `genPotKernel_one` |
| p. 294 | For `h ≡ ½`, `τ_h` is independent of `Φ` and the kernel is a geometric sampling of `P` | Not formalised |
| Theorem 12.2.1, p. 294 | For `g ≤ h ≤ 1`: `U_g = U_h + U_h I_{h−g} U_g = U_h + U_g I_{h−g} U_h` | `theorem_12_2_1` (measurable `0 ≤ g ≤ h ≤ 1`; in Mathlib's order of composition `U_h I_{h−g} U_g` is `genPotKernel P g ∘ₖ genPotDensity P h (h - g)`), `geomOp_resolvent` (the operator form) |
| (12.15)–(12.16), pp. 294–295 | Proof by the strong Markov property of `Ψ` | Replaced by Neveu's operator argument from the series and the minimality `geomOp_le`, in the proof of `geomOp_resolvent` |
| (12.17), p. 295 | `P_h = U_h I_h` is a Markov transition function when `τ_h < ∞` a.s.: `P_h(x, X) = U_h(x, h) = Σₖ P_x{τ_h = k}` | `genPotDensity` (`U_h I_w`), `lintegral_genPotDensity`, `balayage` (`P_h`), `balayage_univ` (`P_h(x, X) = L(x, h)`), `isMarkovKernel_balayage` (`L ≡ 1`), `sum_iterate_killOp_add` (`P_x(τ_h ≤ n) + P_x(τ_h > n) = 1` in operator form), `kfun_add_killOp_one` |
| p. 296 | Finiteness of `τ_h` as the analogue of Harris recurrence | Not formalised (remark) |
| p. 296 | `L(x, h) = U_h(x, h)`, `Q(x, h) = P_x{Σ_{k ≥ 1} h(Φₖ) = ∞}`; `L(x, 1_B) = L(x, B)`, `Q(x, 1_B) = Q(x, B)` | `genL`, `genQ`, `genL_indicator` (`hitProb`, carried), `genQ_indicator` (`harrisQ`, carried); `genL_le_one`, `genL_mono`, `genL_add_iInf` (`L(x, h) = 1 − inf_n (P I_{1−h})ⁿ 1 (x)`) |
| Theorem 12.2.2 (i), p. 296 | `P_x{Ψₖ ∈ A_h i.o.} = Q(x, h)` | `theorem_12_2_2_i` (path law `P_x ⊗ (uniform)^ℕ`) |
| Theorem 12.2.2 (ii), p. 296 | `P_x{τ_h < ∞} = L(x, h)`, hence `L(x, h) ≥ Q(x, h)` | `theorem_12_2_2_ii` (`L ≥ Q`); `genL_add_lintegral_iInf` (`L(x, h) = 1 − E_x[∏_{i ≥ 1} (1 − h(Φᵢ))]`, the path form of `P_x{τ_h < ∞} = L(x, h)`) |
| Theorem 12.2.2 (iii), p. 296 | If `h ≤ ε < 1`, then `L(x, h) = 1` iff `Q(x, h) = 1` | `theorem_12_2_2_iii` (a real `e < 1` with `h ≤ e`) |
| p. 296 | Proof: the conditional Borel–Cantelli lemma; `1 − L(x, h) ≥ δ(1 − ε)^N` | (i) by the two Borel–Cantelli lemmas of Mathlib (`measure_limsup_atTop_eq_zero`, `measure_limsup_eq_one`) conditionally on the path of `Φ`. (iii) by product bounds in place of the bivariate chain: `iInf_prod_one_sub_eq_zero`, `iInf_prod_one_sub_pos`, `one_sub_le_ofReal_exp`, `prod_one_sub_le_ofReal_exp`, `exp_neg_div_le_one_sub`, `ofReal_exp_le_prod_one_sub` |
| Theorem 12.2.3, p. 296 | Standing hypothesis `Q(x, h) = 1` for all `x` | `L(x, h) = 1` for all `x` in `theorem_12_2_3_i` (implied by `Q ≡ 1`, `theorem_12_2_2_ii`); none in `theorem_12_2_3_ii` |
| Theorem 12.2.3 (i), p. 297 | A σ-finite subinvariant `μ` is invariant with `μ(A) = ∫ μ(dx) h(x) U_h(x, A)` | False as stated: `theorem_12_2_3_i_counterexample` (`succKernel`, `Measure.count`, Mathlib, `h ≡ 1`). Corrected: `theorem_12_2_3_i` (`∫ h dμ < ∞`, no σ-finiteness; `genPotKernel P h ∘ₘ μ.withDensity h = μ`); `lintegral_mul_genPot_le` (`μI_hU_h ≤ μ`), `lintegral_mul_genL`, `lintegral_genPotKernel_comp_withDensity`, `IsSubinvariant.lintegral_kfun_le`, `lintegral_eq_mul_add_one_sub_mul`, `iterate_killOp_le_pow`, `measurable_iterate_killKfun` |
| (12.18), p. 297 | Proof: `μ ⊗ uniform` is invariant for `Ψ`, and Theorem 10.4.7 applies to `A_h` | Replaced by test-function computations; the last step is `eq_of_le_of_lintegral_le` (carried) with the function `K_{1/2}(·, h)` |
| Theorem 12.2.3 (ii), p. 297 | If `ν` is finite with `ν(B) = νU_hI_h(B)` for `B ⊆ A`, then `μ = νU_h` is invariant, and the sets `C_ε = {K_{a_{1/2}}(·, h) > ε}` cover `X` and have finite `μ`-measure | `theorem_12_2_3_ii` (`νP_h = ν`; `ε μ{K_{1/2}(·, h) ≥ ε} ≤ ν(X)`; the sets cover `X` when `L > 0` everywhere); `resolventH` (`K_{1/2}(x, h)`), `resolventH_pos`, `resolventH_le_one` |
| p. 297 | Proof: `ν(X) = μ(h) = μK_{a_{1/2}}(h) ≥ εμ(C_ε)` | In the proof of `theorem_12_2_3_ii`, by Markov's inequality (`mul_meas_ge_le_lintegral`, Mathlib) |

## §12.3.1 The smoothed chain on a compact set

| Source | Claim | Lean |
| --- | --- | --- |
| p. 298 | An analogue of Chapter 10; the "process on `A`"; "Theorem 10.4.8" supplies `ν` | Not formalised (informal). The citation is Proposition 10.4.8 (`proposition_10_4_8`, carried); its role is played by `theorem_12_2_3_ii` |
| (12.19), p. 298 | A compact `C` with `L(x, C) ≡ 1` | The hypothesis `∀ x, hitProb P C x = 1` of `theorem_12_3_2` |
| p. 298 | By Proposition 9.1.1, (12.19) gives infinitely many visits to `C`, hence non-evanescence | Not stated separately; `proposition_9_1_1` (carried) is used in the proof of `theorem_12_4_3_iii` |
| p. 298 | The sampled chain `P_C = U_C I_C` is not Feller in general | Not formalised (remark) |
| (12.20), p. 298 | A continuous `h` with `1_O ≤ h ≤ 1_N` | A compactly supported continuous `h` with `1_C ≤ h ≤ 1` (`exists_cc_indicator_le`), in the proof of `theorem_12_3_2` |
| p. 298 | `P_h` is a transition kernel, since `Q(·, h) ≡ 1`, with `P_h(x, N̄) = 1` | `isMarkovKernel_balayage`; `isBoundedInProbabilityOnAverage_of_forall` (a transition kernel `R` with `R(x, K) = 1` for every `x` and a compact `K` is bounded in probability on average), `pow_apply_eq_one_of_forall` |
| Proposition 12.3.1, p. 298 | For weak Feller `P` and continuous `0 ≤ h ≤ 1` with `Q(x, h) ≡ 1`, `P_h` is weak Feller | `proposition_12_3_1` (every continuous `h`; no condition on `Q`) |
| p. 299 | Proof: `(P I_{1−h})ⁿ P I_h` preserves positive lower semicontinuous functions; then `L ± f` | `lowerSemicontinuous_mul_of_continuous`, `IsWeakFeller.lsc_killOp`. The `L ± f` step is not needed: `IsWeakFeller` is stated through open sets (Proposition 6.1.1, `proposition_6_1_1_i_weak`, carried) |
| Theorem 12.3.2, p. 299 | A weak Feller chain with (12.19) has an invariant measure finite on compact sets | `theorem_12_3_2` (`X` nonempty; the measure is nonzero) |
| p. 299 | Proof: an invariant probability `ν` for `P_h` (Theorem 12.1.2), `μ = νU_h` (Theorem 12.2.3), `K_{a_{1/2}}(·, h)` continuous and positive | `theorem_12_1_2_ii`, `theorem_12_2_3_ii`, `genL_mono`, `genL_indicator`, in the proof of `theorem_12_3_2` |

## §12.3.2 Drift criteria for the existence of invariant measures

| Source | Claim | Lean |
| --- | --- | --- |
| p. 299 | The test functions of Harris recurrence and regularity also serve Feller chains | Not formalised (informal) |
| Theorem 12.3.3, p. 299 | A weak Feller chain satisfying (V1) with a compact `C` has an invariant measure finite on compact sets | False without coercivity: `theorem_12_3_3_counterexample` (`succKernel`, `V ≡ 0`, `C = ∅`). Corrected: `theorem_12_3_3` (`V : X → ℝ≥0` measurable and coercive, `∫ V dP(x) ≤ V(x)` for `x ∉ C`; `X` nonempty; the measure is nonzero) |
| p. 299 | Proof: if `L(·, C) ≡ 1`, Theorem 12.3.2; otherwise the supermartingale `V(Φₖ) 1{τ_C > k}` of Theorem 9.4.1 gives `P_x{limsup V(Φₖ) < ∞} > 0`, and Theorem 12.1.2 | `theorem_12_3_2`; `ae_bddAbove_of_avoid` (carried), `hitProbZero_of_notMem` (carried), `le_cesaroKernel_of_forall`, `exists_isInvariant_of_frequently`, in the proof of `theorem_12_3_3` |
| Theorem 12.3.4, p. 299 | A weak Feller chain satisfying (V2) with a compact `C` and `V(x₀) < ∞` has an invariant probability | `theorem_12_3_4` ((V2) as `∫ V dP(x) + 1 ≤ V(x) + b 1_C(x)` in `[0, ∞]`, `b` finite) |
| (12.21), p. 300 | Iterating (V2): `liminf_n n⁻¹ Σ_{k ≤ n} Pᵏ(x₀, C) ≥ b⁻¹` | `lintegral_pow_add_le_of_V2` (`PⁿV(x) + n ≤ V(x) + b Σ_{k<n} Pᵏ(x, C)`), `eventually_le_cesaroKernel_of_V2` (`P̄ⁿ(x₀, C) ≥ (2b)⁻¹` for large `n`), `V2_coe_ne_zero` (`b ≠ 0`), `sum_range_succ_eq_add_sum_Icc` |
| p. 300 | Theorem 12.3.4 follows from Theorem 12.1.2 (i) | `exists_isInvariant_of_frequently`, in the proof of `theorem_12_3_4` |

## §12.4.1 Existence of an invariant measure for e-chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 300 | Weak limits depend on `x` unless the invariant measure is unique | Not formalised (remark) |
| (12.22), p. 300 | If `Pᵏf(x) → Πf(x)` for every `f ∈ C(X)` with `Π` a weak Feller transition function, then, as in Proposition 6.4.2, `Φ` is an e-chain | False as stated, by the counterexample to Proposition 6.4.2 (`proposition_6_4_2_counterexample`, carried; `jumpKernel`, carried); see corrections. The corrected form of Proposition 6.4.2 is `proposition_6_4_2_corrected` (carried) |
| Theorem 12.4.1 (i), (12.23), p. 300 | For an e-chain there is a substochastic kernel `Π` with `P̄ᵏ(x, ·) → Π(x, ·)` vaguely | `theorem_12_4_1_i` (`Π = eChainLimit he`, `Π(x, X) ≤ 1`), `isFiniteKernel_eChainLimit` |
| Theorem 12.4.1 (i), (12.24), p. 300 | `K_{a_ε}(x, ·) → Π(x, ·)` vaguely as `ε ↑ 1` | `theorem_12_4_1_resolvent` (`EChainCriteria`) |
| Theorem 12.4.1 (ii), (12.25), p. 300 | `PʲΠᵏPˡ = Π` for `j, k, ℓ ∈ ℤ₊`, and every `Π(x, ·)` is invariant with `Π(x, X) ≤ 1` | `theorem_12_4_1_ii` (`k ≥ 1`), `isInvariant_eChainLimit`, `kernel_comp_eChainLimit` (`ΠP = Π` in Mathlib's order, `P ∘ₖ Π`), `eChainLimit_comp_kernel`, `eChainLimit_comp_self` |
| Theorem 12.4.1 (iii), p. 300 | `Φ` is bounded in probability on average iff `Π(x, X) = 1` for all `x` | `theorem_12_4_1_iii`, `ofReal_integral_le_univ` |
| (12.26), p. 301 | Ascoli's theorem and a diagonal argument over a dense `{fₙ} ⊂ C_c(X)` | `cesaroFun` (`P̄ⁿ f`), `abs_cesaroFun_le`, `measurable_cesaroFun`, `cesaroFun_sub`, `eventually_abs_cesaroFun_sub_le` (equicontinuity of the Cesàro averages, from `eventually_dist_lt_of_eChain`, carried), `exists_dense_cc`, `exists_subseq_tendsto_cesaroFun` (pointwise convergence along a subsequence, for every `f ∈ C_c(X)` and every `x`) |
| p. 301 | Each vague limit point `ν` of `P̄^{kᵢ}(x, ·)` has `∫ fₙ dν = gₙ(x)`, so it is unique; a kernel `Π` exists along `{kᵢ}` | `CesaroConverges`, `limMeasure`, `limMeasure_univ_le`, `isFiniteMeasure_limMeasure`, `tendsto_limMeasure`, `measurable_integral_limMeasure`, `measurable_integral_limMeasure_bcf`, `measurable_limMeasure`, `limKernel`, `limKernel_apply`, `isFiniteKernel_limKernel`, `ext_of_integral_cc`, `integral_cutoff_tendsto`; `eChainSubseq`, `cesaroConverges_eChainSubseq`, `tendsto_eChainSubseq`, `eChainLimit` |
| p. 301 | `Πf` is continuous by equicontinuity | `continuous_kfunR_of_eChain`, `continuous_integral_limMeasure` |
| p. 301 | `PʲΠ = Π` by dominated convergence, and `ΠP = Π` by (D.6) | `integral_cesaroFun_kernel`, `integral_limMeasure_kernel`, `isInvariant_limMeasure`, `integral_limMeasure_limMeasure` |
| p. 301 | A different subsequence gives the same limit, by symmetry | `limMeasure_eq`, `integral_cc_eq_of_nonneg` |
| p. 301 | (iii) from (i) and Proposition D.5.6 | In the proof of `theorem_12_4_1_iii` |
| p. 301 | The proof of (12.24) "being similar" | From Cesàro to Abel means: `tsum_pow_succ_mul_eq` (summation by parts), `tendsto_abel_of_cesaro`, `tendsto_toReal_nhdsLT_one`, `sum_Icc_one_eq_sum_range`, in the proof of `theorem_12_4_1_resolvent` |

## §12.4.2 Hitting time and drift criteria for stability of e-chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 302 | An analogue of the regularity results of Chapter 11 | Not formalised (informal) |
| Proposition 12.4.2, p. 302 | For compact `C` and `x ∈ C`, `liminf_{ε↑1} K_{a_ε}(x, C) ≥ (sup_{y ∈ C} E_y[τ_C])⁻¹` | `proposition_12_4_2` (every measurable `C`, every `x ∈ C` and every `ε < 1`; `meanReturnTime`, carried), `proposition_12_4_2_liminf` (the book's form) |
| (12.27), p. 302 | `inf_C K_{a_ε}(·, C) ≥ (1 − ε) + inf_C E_y[ε^{τ_C}] inf_C K_{a_ε}(·, C)`, by the strong Markov property at `τ_C` | `discOcc` (`Σₘ εᵐ 1_C(Φₘ)`), `measurable_discOcc`, `lintegral_discOcc`, `discOcc_ge`, `discAt` (`ε^τ`), `discAt_of_eq`, `measurable_discAt`, `resolvent_apply_eq_mul`; `strong_markov_lintegral_mul` (carried), in the proof of `proposition_12_4_2` |
| p. 302 | Jensen's inequality `E[ε^{τ_C}] ≥ ε^{E[τ_C]}` | Replaced by Bernoulli's inequality, `one_le_pow_add_mul_one_sub` (`1 ≤ εⁿ + n(1 − ε)`) |
| p. 303 | Compact sets as test sets for stability | Not formalised (remark) |
| Theorem 12.4.3 (i), p. 303 | `max_x Π(x, X)` exists and is `0` or `1` | `theorem_12_4_3_i` (`X` nonempty); `eChainMass` (`u = Π(·, X)`), `eChainMass_le_one`, `measurable_eChainMass`, `eChainLimit_comp_measure` (`π = πΠ` for invariant probabilities), `integral_comp_measure_finite` |
| Theorem 12.4.3 (ii), (12.28)–(12.29), pp. 303–304 | If `min_x Π(x, X)` exists it is `0` or `1`; `S_ρ` is closed and absorbing, `Π(x, S_ρᶜ) = 0` on `S_ρ`, and `Π(x, {Π(·, X) < 1}) = 0` | `theorem_12_4_3_ii`; `lintegral_eChainMass` (`Pu = u`), `lintegral_pow_eChainMass`, `lowerSemicontinuous_eChainMass`, `regular_eChainLimit`, `eChainLimit_open_le` ((D.6) for open sets), `eChainLimit_lt_one_null` ((12.29)) |
| Theorem 12.4.3 (iii), (12.30), p. 304 | If a compact `C` has `P_x{τ_C < ∞} ≡ 1`, then `min_x Π(x, X)` exists and is attained on `C` | `theorem_12_4_3_iii` (`C` nonempty); (12.30) from `proposition_9_1_1` (carried), the martingale `u(Φₖ)` through `ae_tendsto_killedV` (carried), and Fatou's lemma (`lintegral_liminf_le`, Mathlib), in the proof |
| Theorem 12.4.3 (iv), p. 304 | For compact `C`, `inf_{x ∈ C} Π(x, X) ≥ (sup_{x ∈ C} E_x[τ_C])⁻¹` | `theorem_12_4_3_iv` (from `proposition_12_4_2` and `theorem_12_4_1_resolvent`) |
| Proposition 12.4.4, p. 304 | An e-chain with `P_x{τ_C < ∞} ≡ 1` and `sup_{x ∈ C} E_x[τ_C] < ∞` for a compact `C` is bounded in probability on average | `proposition_12_4_4`, `nonempty_of_hitProb` |
| Theorem 12.4.5, p. 304 | An e-chain satisfying (V2) for a compact `C` and an everywhere finite `V` is bounded in probability on average | `theorem_12_4_5` ((V2) in `[0, ∞]`, `b` finite) |
| pp. 304–305 | Proof: Theorem 11.3.4 gives `E_x[τ_C] ≤ V(x)` off `C`; `Π(x, X) ≥ b⁻¹` as in Theorem 12.3.4; Theorem 12.4.3 (iii) and (ii) | `meanReturnTime_le_of_V2` (`E_x[τ_C] ≤ V(x) + b 1_C(x)` for every `x`, proved directly), `hitProb_eq_one_of_meanReturnTime_ne_top` (carried), `eventually_le_cesaroKernel_of_V2`, `theorem_12_4_1_i` with `exists_cc_indicator_le`, `theorem_12_4_3_iii`, `theorem_12_4_3_ii`, in the proof of `theorem_12_4_5` |

## §12.5 Establishing boundedness in probability

| Source | Claim | Lean |
| --- | --- | --- |
| p. 305 | Boundedness in probability as the key condition | Not formalised (informal) |
| Lemma D.5.3 (i), p. 559 | A sequence of probabilities is tight iff there is a coercive `V` with `limsup_k νₖ(V) < ∞` | `lemma_D_5_3_i` (with `sup_n ∫ V dνₙ < ∞`), `lemma_D_5_3_i_necessity` (`∫ V dνₙ ≤ 2`, with `V = Σⱼ 2ʲ 1_{Lⱼᶜ}`), `isTightMeasureSet_range_of_lintegral_le` (sufficiency) |
| Lemma D.5.3 (ii), p. 559 | Coercive `Vₓ` with `limsup_k E_x[Vₓ(Φₖ)] < ∞` for every `x` make the chain bounded in probability | `lemma_D_5_3_ii`, `isBoundedInProbability_of_lintegral_le` (one `V`) |

## §12.5.1 Linear state space models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 305 | The conditions of Proposition 6.3.5 give boundedness in probability; the model is an e-chain under (LSS5) (Chapter 7) | Not formalised (remark); the model is `lssMatrixKernel` (carried) |
| Proposition 12.5.1, p. 305 | Under (LSS1)–(LSS2) and (LSS5) the model is bounded in probability; with (LSS4) and (LCM3) it is positive Harris | `proposition_12_5_1_i` (`IsStableMatrix`, carried; `E‖W‖ < ∞`), `proposition_12_5_1_ii` ((LSS4) as `¬ Γ ⟂ₘ volume`, (LCM3) as `IsControllable`, carried; `IsPositiveHarris`, carried) |
| (12.31)–(12.34), pp. 305–306 | `M = I + Σᵢ F'ⁱFⁱ`, `|Fx|²_M ≤ α|x|²_M`, `V(x) = |x − m|²_M`, `E[V(X_{k+1}) | X₀, …, Xₖ] ≤ αV(Xₖ) + E|G(W − EW)|²_M` | Not used. The proof takes `V(x) = ‖x‖` and the closed form: `lintegral_enorm_lssMatrix_pow_le` (`E_x‖Φₖ‖ ≤ ‖Fᵏx‖ + Σ_{j<k} C rʲ E‖GW‖`), `lintegral_enorm_mulVec_ne_top`, `isStableMatrix_geometric` and `lssMatrixKernel_pow_apply` (carried), `isCoercive_nnnorm` |
| p. 306 | A geometric drift with a coercive `V` gives boundedness in probability, by Lemma D.5.3 | `isBoundedInProbability_of_drift`, `lintegral_pow_le_of_drift` (`PᵏV ≤ αᵏV + β Σ_{j<k} αʲ`) |
| p. 306 | (12.34) gives (V2); under (LSS4) and (LCM3) compact sets are petite (Proposition 6.3.5), and Theorem 11.3.11 gives regularity and positive Harris recurrence | The (V2) remark is not formalised. The positive Harris part uses `proposition_6_3_5`, `theorem_9_2_2_ii`, `proposition_4_2_2_maximal` (carried), `proposition_12_1_1` and `theorem_12_1_2_ii`, in the proof of `proposition_12_5_1_ii`, in place of Theorem 11.3.11 |
| p. 306 | The deterministic core `x_{k+1} = Fxₖ` is globally exponentially stable | Not formalised (remark); the geometric bound is `isStableMatrix_geometric` (carried) |

## §12.5.2 Bilinear models

| Source | Claim | Lean |
| --- | --- | --- |
| (12.35), p. 306 | The simple bilinear model `X_{k+1} = θXₖ + bW_{k+1}Xₖ + W_{k+1}` | `bilinearKernel` (carried) |
| (12.36)–(12.37), p. 306 | `E[|X_{k+1}| | Xₖ = x] ≤ E|θ + bW| |x| + E|W|`, so `Φ` is bounded in probability when `E|θ + bW| < 1` | `bilinear_isBoundedInProbability` (`E|θ + bW| < 1` and `E|W| < ∞`; the zero mean of `W` is not used) |
| p. 306 | (12.36) gives (V2) | Not formalised (remark) |

## §12.5.3 Adaptive control models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 307 | The closed loop system (2.25) is a Feller chain | `sacStep`, `sacKernel`, `sacGaussianKernel` (carried). The weak Feller property is proved for the chain restricted to its state space `sacSpace` (carried): `isWeakFeller_restrict_sacKernel`, through `restrictKernel_sacKernel_eq` (a random recursion on the state space, `sacStepX`; `restrictKernel`, `recursionKernel`, carried) |
| (12.38), p. 307 | Initial conditions with `θ̃ₖ = θₖ − E[θₖ | Yᵏ]` and `Σₖ = E[θ̃ₖ² | Yᵏ]` | `IsKalmanLaw` (given `(Σ, Y)`, `θ̃ ~ N(0, Σ)`; `gaussianReal`, Mathlib). It holds at every time from a Kalman initial law: `kalman_step_map` (one step of the filter, by characteristic functions: `strongDual_prod_apply`, `integral_cexp_gaussianReal`), `lintegral_sacGaussian_comp_of_isKalmanLaw`, `IsKalmanLaw.comp`, `isKalmanLaw_sacGaussian_pow`. For a general noise law it is the hypothesis `hcond` of `proposition_12_5_2` |
| p. 307 | For example `y₀ = θ̃₀ = Σ₀ = 0` | Outside the state space `Σ ≥ σ_z²`. The initial law used is `sacKalmanInit` (`Σ₀ = σ_z²`, `Y₀ = 0`, `θ̃₀ ~ N(0, σ_z²)`), with `sacKalmanInit_spec` |
| (12.39), p. 307 | `E[Y²_{k+1} | Yᵏ] = ΣₖYₖ² + σ_w²` | `IsKalmanLaw.lintegral_sq` (`E[g(Σ, Y) θ̃²] = E[g(Σ, Y) Σ]` for measurable `g ≥ 0`), `lintegral_sacKernel_sigma_mul_sq` (one step of `ΣY²`) |
| Proposition 12.5.2, p. 307 | Under (SAC1)–(SAC2), (12.38) and `σ_z² < 1`, `limsup_k E[|Φₖ|²] < ∞`, so the distributions are tight and `Φ` is positive recurrent | `proposition_12_5_2` (`sup_k E[Σₖ² + θ̃ₖ² + Yₖ²] < ∞`, for a noise law with `E W = 0`, `E W² = σ_w²`, `|α| < 1`, `σ_z, σ_w ≠ 0`, an initial law on the state space with `E Y₀² < ∞`, and `hcond`), `proposition_12_5_2_tight`, `proposition_12_5_2_kalman` (the Gaussian model from a Kalman initial law; `integral_sq_gaussianReal`, `sacGaussian_noise_moments`), `proposition_12_5_2_positive` |
| p. 307 | `Σₖ` lies between `σ_z²` and `σ_z²/(1 − α²)`; `limsup_k E[θₖ²] = σ_z²/(1 − α²)`; it suffices to bound `E[Yₖ²]` | `sacKernel_pow_comp_compl` (every `μPᵏ` lives on `[σ_z², σ_z²/(1 − α²)] × ℝ²`). The parameter `θₖ` is not a coordinate of the state; `E[θ̃ₖ²] = E[Σₖ]` is bounded through `hcond` with `g ≡ 1`, in the proof of `proposition_12_5_2` |
| (12.40), p. 307 | `E[Y²_{k+1}Σ_{k+1} | Yᵏ] = σ_z²Yₖ²Σₖ + σ_w²σ_z² + α²σ_w²Σₖ` | `sac_identity_12_40` (the algebraic identity), `sac_moment_step_12_40` (the bound on `E[Σ_{k+1}Y²_{k+1}]` after averaging) |
| (12.41), p. 307 | `Σ E[Y²_{k+1}] ≤ E[Y²_{k+1}Σ_{k+1}] ≤ (σ_w²σ_z² + α²σ_w²Σ̄)/(1 − σ_z²) + σ_z^{2k} E[Y₀²Σ₀]` | `sac_moment_bound_12_41` (`E[ΣₖYₖ²] ≤ σ_z^{2k} E[Σ₀Y₀²] + (σ_w²σ_z² + α²σ_w²Σ̄) Σ_{j<k} σ_z^{2j}`), `pow_zero_comp` |
| p. 307 | "Since `Φ` has the Feller property it follows from Proposition 12.1.3 that an invariant probability exists. Hence from Theorem 7.4.3 the chain is positive recurrent" | `proposition_12_5_2_positive` (`|α| < 1`, `α ≠ 0`, `σ_z ≠ 0`, `σ_w ≠ 0`, `σ_z² < 1`): the restricted chain is a T-chain, positive (`IsPositive`, carried), recurrent (`IsRecurrentChain`, carried) and aperiodic (`IsAperiodic`, carried). The invariant probability comes from `theorem_12_1_2_i` and the tightness of the laws from `sacKalmanInit`, not from Proposition 12.1.3; positivity from Proposition 7.4.3 (`proposition_7_4_3`, carried) and recurrence from `proposition_10_1_1` (carried) |
| p. 308 | The conditional mean of `Yₖ²` converges geometrically (Chapter 16) | Not formalised (forward reference) |
| p. 308 | (12.40) does not give (V2); for `σ_z² ≥ 1`, `E[Yₖ²] → ∞`; (12.39) holds only for restricted initial conditions | Not formalised (remarks) |

## §12.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 308–309 | Foguel, Beneš, Stettner, Krengel; Lin and Foguel on Theorem 12.3.2; Rosenblatt's use of `P_h`; Neveu and the resolvent equation; the balayage operator; Brunel and Revuz; Foster's proof of the sufficiency of (V2); whether Theorem 12.3.4 gives boundedness in probability; Jamison, Sine and Rosenblatt on e-chains; the linear, bilinear and adaptive control models in the literature | Not formalised (commentary) |
