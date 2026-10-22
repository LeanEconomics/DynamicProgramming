# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 14, pp. 336–361. Equation numbers are the book's. Lean names are relative to
`MeynTweedie.FErgodicity`; names from Mathlib are marked as such. Names marked "carried" are in the
modules copied from the Chapter 13 project `Ergodicity` (see the [README](../README.md)).
"Positive" is `IsPositive P ψ` (carried): `ψ`-irreducible with an invariant probability, which is
the book's "positive recurrent" by Proposition 10.1.1. `ψ` is a maximal irreducibility measure
(`IsMaximalIrreducibility P ψ`, carried) and `B⁺(X)` is `{B : ψ(B) > 0}`. `μP` is `P ∘ₘ μ`.
`‖μ − ν‖_f` is `fNorm f μ ν`, `E_x[Σ_{k<τ_B} f(Φ_k)]` is `fSumReturn P B f x`,
`G_B(x, f) = E_x[Σ_{k=0}^{σ_B} f(Φ_k)]` is `gKernelFn P B f x` (carried), and
`U_B(x, f) = E_x[Σ_{k=1}^{τ_B} f(Φ_k)]` is `tabooPotFn P B f x` (carried). `f^{(m)}` is
`fSkel P m f`, and (V3) is `DriftV3 P V f b C`. In §14.5, `μ ∗ U` is `renMeas Γ μ`,
`ρ ∗ g(t)` is `convAt ρ g t`, `sup_{|g| ≤ f} |ρ₁ ∗ g(t) − ρ₂ ∗ g(t)|` is `convSupDiff f ρ₁ ρ₂ t`,
`β` is `renMean Γ` and `Γₑ` is `eqLaw Γ`. Every place where the Lean statement departs from the
book is listed in [corrections](corrections.md).

## Chapter 14 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 336 | Bounded `f` is unsatisfactory: costs, buffer levels, storage penalties; the aim is (14.1) for `f : X → [1, ∞)` | Not formalised (informal). (14.1) follows from (14.4) by `tendsto_integral_of_tendsto_fNorm` |
| p. 336 | The `f`-norm `‖ν‖_f = sup_{|g| ≤ f} |ν(g)|` | `fNorm` (for the signed measure `μ − ν`, valued in `[0, ∞]`, over measurable `g : X → ℝ` with `|g| ≤ f` integrable for both measures, `IsFTest`), `integrable_of_ofReal_abs_le`, `enorm_le_of_ofReal_abs_le`, `enorm_integral_le_lintegral`, `ofReal_abs_integral_le_lintegral`, `ofReal_abs_integral_sub_le_fNorm`, `fNorm_le` |
| p. 336 (used throughout) | Properties of the `f`-norm | `fNorm_comm`, `fNorm_self`, `fNorm_mono`, `ofReal_abs_sub_le`, `fNorm_triangle` (when the middle measure has `ν(f) < ∞`), `fNorm_le_add`, `fNorm_le_of_add_eq`, `fNorm_add_add_le`, `fNorm_finsetSum_le`, `fNorm_smul_le`, `fNorm_smul_sum_le`, `fNorm_add_left_le`, `fNorm_add_cancel_le`; `fNorm_one` (`f ≡ 1` gives `tvNorm`, carried), `ofReal_tvNorm_le_fNorm` |
| pp. 349–351 (used) | Transport by maps and kernels; the `f`-norm averaged over initial laws | `fNorm_map_le`, `fNorm_comp_le` (`‖μQ − νQ‖_f ≤ ‖μ − ν‖_{Qf}`), `isFTest_comp`, `integral_comp_kernel_of_integrable`, `lintegral_comp_kernel`, `integral_integral_sub`, `fNorm_comp_le_lintegral`, `fNorm_comp_pow_le_lintegral`, `fNorm_pow_le_lintegral` |
| Theorem 14.0.1, p. 336 | Standing hypothesis: `Φ` is `ψ`-irreducible and aperiodic, and `f ≥ 1` | `IsMaximalIrreducibility P ψ` and `IsAperiodic P ψ` (carried), a measurable `f : X → [0, ∞]` with `1 ≤ f`, in `theorem_14_0_1` and `theorem_14_0_1_consequences`; the state space is countably generated |
| Theorem 14.0.1 (i), p. 336 | The chain is positive recurrent with invariant probability `π` and `π(f) < ∞` | The first condition of `theorem_14_0_1`: an invariant probability `π` with `π(f) < ∞` (positivity, since the chain is `ψ`-irreducible) |
| Theorem 14.0.1 (ii), (14.2), p. 337 | Some petite `C` has `sup_{x ∈ C} E_x[Σ_{n<τ_C} f(Φₙ)] < ∞` | The second condition of `theorem_14_0_1`, for a **non-empty** petite set (`IsPetite`, carried). As printed it holds for `C = ∅` and every chain (`theorem_14_2_4_counterexample`); see corrections |
| Theorem 14.0.1 (iii), (14.3), p. 337 | A petite `C`, `V : X → [0, ∞]` with `V(x₀) < ∞` and `ΔV ≤ −f + b 1_C` | The third condition of `theorem_14_0_1`: `DriftV3 P V f b C` for a measurable `V`, `b ≠ ∞` and some `x₀` with `V(x₀) ≠ ∞` |
| p. 337 | `S_V = {V < ∞}` is absorbing and full | `theorem_14_0_1_consequences` (first two conclusions), from `lemma_14_2_1` |
| p. 337 | Any sublevel set of `V` satisfies (14.2) | False as stated: `theorem_14_0_1_counterexample` (`toFalseKernel`, carried, with `f ≡ 1`). Corrected: every sublevel set `{V ≤ ℓ}`, `ℓ < ∞`, is `f`-regular (`theorem_14_0_1_consequences`, `theorem_14_2_6_sublevel`), which is (14.2) for the sublevel sets in `B⁺(X)` by `theorem_14_2_4` |
| (14.4), p. 337 | `‖Pⁿ(x, ·) − π‖_f → 0` for `x ∈ S_V` | `theorem_14_0_1_consequences`; `tendsto_fNorm_of_driftV3` (from every probability `λ` with `λ(V) < ∞`) |
| (14.5), p. 337 | If `π(V) < ∞`, `Σₙ ‖Pⁿ(x, ·) − π‖_f ≤ B_f (V(x) + 1)` for `x ∈ S_V` | `theorem_14_0_1_consequences` (for every `x`, the sum over `n ≥ 0`); `tsum_fNorm_le_of_driftV3`, `fNorm_pow_le_lintegral` |
| p. 337 | Proof: (i) ⇔ (ii) from "Theorem 14.1.1" and Theorem 14.2.11; (ii) ⇔ (iii) from Theorems 14.2.3 and 14.2.4; sublevel sets by Theorem 14.2.3; the limits from Theorems 14.3.3–14.3.5 | (i) ⇒ (ii): `exists_fRegularSet_pos` (Theorem 14.2.11) and `theorem_14_2_4`. (ii) ⇒ (iii): `driftV3_gKernelFn`, `tabooPotFn_le`. (iii) ⇒ (i): `isPositive_of_driftV3` (a sublevel set of `V` in `B⁺(X)` is `f`-regular, hence regular, so the chain is positive by `isPositive_of_isRegularSet`, carried; `π(f) ≤ b π(C)` by `lintegral_le_of_driftV3`). The limits: `tendsto_fNorm_of_driftV3`, `tsum_fNorm_le_of_driftV3`. "Theorem 14.1.1" is Proposition 14.1.1 |
| p. 337 | The pattern of the chapter; Theorem 13.0.1 as the case `f ≡ 1` | Not formalised (informal) |
| p. 337 | If `|g| ≤ c(f + 1)`, `E_x[g(Φ_k)] → ∫ g dπ` for `V(x) < ∞` | `tendsto_integral_of_tendsto_fNorm` (for `|g| ≤ f`, when `μₙ(f)`, `ν(f)` are finite); the multiple `c(f + 1)` is not stated separately |
| p. 337 | `f`-ergodicity: `f ≥ 1`, positive Harris with `π`, `π(f) < ∞`, `‖Pᵏ(x, ·) − π‖_f → 0` for every `x` | `IsFErgodic P ψ f π` |
| p. 338 | The `f`-Norm Ergodic Theorem adds `π(f) < ∞` to the Aperiodic Ergodic Theorem; `V` finite everywhere gives `f`-ergodicity without restriction | Not formalised (informal); the second remark is `theorem_14_0_1_consequences` with `S_V = X` |

## §14.1.1 `f`-Regularity for chains with atoms

| Source | Claim | Lean |
| --- | --- | --- |
| p. 338 | A single accessible atom suffices; the first term of the Regenerative Decomposition is the hard one | Not formalised (informal) |
| (14.6), p. 338 | For an atom of a positive Harris chain and `|g| ≤ f`, `|E_λ[g(Φₙ)] − π(g)| ≤ λ_αPⁿ(f) + |a_λ ∗ u − π(α)| ∗ t_f (n) + π(α) Σ_{j > n} t_f(j)` | `fNorm_comp_pow_succ_le` (as a bound on `‖λPⁿ⁺¹ − π‖_f`, for every measurable `f ≥ 0`, bounded or not, when `π = π(α) μ°_α`; `atomMeasure`, `entryLaw`, `atomRenewal`, `tabooKernel`, `tabooSeq`, carried); `add_eq_add_of_measureReal_sub_eq`, `ofReal_add_ofReal_neg`, `fNorm_le_of_add_eq` |
| (14.7), p. 338 | `Σₙ t_f(n) = E_α[Σ_{j=1}^{τ_α} f(Φ_j)]` | `tsum_lintegral_tabooKernel` (`Σ_j T_j(f) = U_α(a, f)`); `lintegral_eq_atom` (`π(f) = π(α) U_α(a, f)`), `IsAtom.tabooPotFn_eq`, `tabooPotFn_ne_top_of_rep` |
| (14.8), p. 338 | `∫ λ(dx) _αPⁿ(x, dw) f(w) = E_λ[f(Φₙ) I(τ_α ≥ n)]` | The term is `∫ f d(tabooSeq P hα λ n)` (carried); the path form is not stated separately |
| (14.9), p. 339 | `Σₙ ∫ λ(dx) _αPⁿ(x, dw) f(w) = E_λ[Σ_{j=1}^{τ_α} f(Φ_j)]` | `tsum_lintegral_tabooSeq` (`= ∫ λ(dx) U_α(x, f)`), `lintegral_tabooPotKernel` |
| p. 339 | Only the sum of these terms appears tractable | Not formalised (informal) |
| p. 339 | `f`-regular sets, measures and chains; `f`-regular states | `IsFRegularSet`, `IsFRegularMeasure`, `IsFRegularChain`, `IsFRegularState`, `IsFRegularOn`; `fSumReturn`, `measurable_fSumReturn`, `measurable_sumBefore_firstReturn`, `fSumReturn_one` (`= E_x[τ_B]` for `f ≡ 1`), `meanReturnTime_le_fSumReturn`, `le_fSumReturn`, `le_sumBefore_firstReturn`, `fSumReturn_mono`, `fSumReturn_anti_set`, `firstReturn_anti`; `IsFRegularSet.subset`, `IsFRegularSet.mono`, `IsFRegularSet.union`, `IsFRegularSet.isFRegularState`, `IsFRegularSet.isRegularSet` (for `f ≥ 1`), `IsFRegularSet.exists_le`, `isFRegularMeasure_dirac_iff` |
| p. 339 | The dependence on all of `B⁺(X)` is illusory | Theorem 14.2.4 below |
| Proposition 14.1.1, (14.10), p. 339 | A recurrent chain with invariant `π` and a set `C` with `π(C) < ∞` and (14.10) is positive recurrent with `π(f) < ∞` | False as stated: `proposition_14_1_1_counterexample` (`C = ∅`; the forward recurrence time chain of `heavyRenewal`, carried, with `f ≡ 1`). Corrected: `proposition_14_1_1` (`C` non-empty, `π ≠ 0`, `f ≥ 1`; it also gives `ψ(C) > 0` and `π(f) ≤ π(C) M`) |
| p. 340 | Proof: `C` is Harris recurrent, so `C ∈ B⁺(X)` by Proposition 9.1.1; `π(f) = ∫_C π(dy) E_y[Σ_{n<τ_C} f(Φₙ)]` from Theorem 10.4.9 | `lintegral_eq_fSumReturn`, `lintegral_eq_tabooPotFn` (Theorem 10.4.9 for functions, through `sumBefore_firstReturn_add`, `fSumReturn_add_tabooPotFn`, `lintegral_tabooPotKernel`, `measurable_tabooPotFn`), in the proof of `proposition_14_1_1` |
| Proposition 14.1.2 (i), p. 340 | For a positive recurrent chain with `π(f) < ∞` and an atom `α ∈ B⁺(X)`, `C` is `f`-regular iff `sup_{x ∈ C} E_x[Σ_{k=0}^{σ_α} f(Φ_k)] < ∞` | `proposition_14_1_2_i` (`f` finite at one point of `α`), `isFRegularState_iff_atom` (`x` is `f`-regular iff `G_α(x, f) < ∞`) |
| Proposition 14.1.2 (ii), p. 340 | Increasing `f`-regular sets `S_f(n)` whose union is full and absorbing | `proposition_14_1_2_ii` (`S_f(n) = {G_α(·, f) ≤ n}`) |
| (14.11), p. 340 | `G_α(x, f) = E_x[Σ_{k=0}^{σ_α} f(Φ_k)]` | `gKernelFn P α f` (carried, (11.21)) |
| p. 340 | By Theorem 11.3.5, `P G_α ≤ G_α + c` with `c = π(f)/π(α)`; `{G_α < ∞}` is absorbing, hence full by Proposition 4.2.3 | `atom_driftV3` ((V3) for `G_α(·, f)` with `b = U_α(a, f)`, through `driftV3_gKernelFn` and `lintegral_eq_atom`), `lemma_14_2_1` |
| pp. 340–341 | `G_α(x, f) ≤ E_x[Σ_{k<τ_B} f(Φ_k)] + sup_B G_α(·, f)` for a sublevel set `B` with `π(B) > 0`; `E_α[Σ_{k=1}^{τ_B} f(Φ_k)] < ∞` for `B ∈ B⁺(X)` by Theorem 10.4.9 | `gKernelFn_le_fSumReturn_add`, `exists_sublevel_pos_atom`. The "if" direction is proved from (V3) for `G_α(·, f)` and Theorem 14.2.3 (i) (`theorem_14_2_3_i_fRegular`, `isFRegularState_of_driftV3`), since `α` is petite |
| (14.12), p. 341 | `E_x[Σ_{k=0}^{τ_B} f(Φ_k)] ≤ E_x[Σ_{k=0}^{σ_α} f(Φ_k)] + E_α[Σ_{k=1}^{τ_B} f(Φ_k)]`, from `τ_B ≤ σ_α + θ^{σ_α} τ_B` | The strong Markov bound `fSumReturn_le_stopping`, `lintegral_sumBefore_le_stopping`, `sumBefore_add_le_of_shift`, `firstReturn_le_add_shift`, `firstHit_le_add_shift`, `firstHit_add_one_le_add_shift`, `fSumReturn_le_add_of_forall_le`, `IsAtom.tabooPotFn_le_gKernelFn`; `tsum_indicator_lt_add`, `sumBefore_eq_tsum`, `sumBefore_of_eq`, `sumBefore_of_eq'`, `sumBefore_le_top` |

## §14.1.2 `f`-Ergodicity for chains with atoms

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 14.1.3 (i), p. 341 | For a positive Harris aperiodic chain with an atom `α ∈ B⁺(X)` and `π(f) < ∞`, the `f`-regular states form a full absorbing set `S_f` and `‖Pᵏ(x, ·) − π‖_f → 0` for `x ∈ S_f` | `theorem_14_1_3_i` (`f` finite valued) |
| Theorem 14.1.3 (ii), p. 341 | An `f`-regular chain is `f`-ergodic | `theorem_14_1_3_ii`; `IsFRegularChain.lintegral_ne_top` (an `f`-regular chain has `π(f) < ∞`) |
| Theorem 14.1.3 (iii), (14.13), p. 341 | `Σ_{n ≥ 1} ∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ M_f (λ(G_α(·, f)) + µ(G_α(·, f)))` for `f`-regular `λ`, `μ` | `theorem_14_1_3_iii` (for all probabilities `λ`, `μ`; the right side is finite for `f`-regular ones, `lintegral_gKernelFn_ne_top_of_isFRegularMeasure`) |
| p. 341 | Proof of (i)–(ii): the three terms of (14.6) tend to `0`; the atom is ergodic | `tendsto_fNorm_of_ergodic_atom`; `proposition_13_2_4_i` and `IsHarris.hitProb_eq_one` (carried) |
| (14.14)–(14.15), p. 342 | Proof of (iii): by the triangle inequality one initial law is `δ_α`; the summed first form of the Regenerative Decomposition | `fNorm_comp_pow_succ_le_atom` (`‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖_f ≤ λ_αPⁿ⁺¹(f) + Σ_{k ≤ n} |a_λ ∗ u(k) − u(k)| T_{n−k}(f)`), `tsum_fNorm_comp_le_atom` (the sum is at most `E_λ[Σ_{k=1}^{τ_α} f] + E_λ[τ_α] Var(u) U_α(a, f)`; `renewalVar`, carried), `tsum_sum_range_mul`, `tsum_lintegral_le_lintegral_tsum`, `IsAtom.mul_lintegral_pow_le`; `fNorm_triangle` |
| p. 342 | `E_λ[τ_α] Var(u)` by (13.72); `E_x[τ_α] ≤ E_x[Σ_{n=1}^{τ_α} f(Φₙ)] ≤ M G_α(x, f)` | `abs_sub_realConv_summable` (carried) in the proof of `tsum_fNorm_comp_le_atom`; `meanReturnTime_le_tabooPotFn`, `IsAtom.tabooPotFn_le_gKernelFn` |
| p. 342 | For an accessible atom the move to `f`-norm is easy; the countable case | Not formalised (informal) |
| Theorem 14.1.4, p. 342 | For an irreducible positive Harris aperiodic chain on a countable space with `π(f) < ∞`, `‖Pᵏ(x, ·) − π‖_f → 0` and `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f < ∞` for all `x`, `y` | `theorem_14_1_4` (`ψ{x} > 0` for every `x`, `f` finite valued) |
| pp. 342–343 | Why the split skeleton does not work directly; Chapter 11 as the model | Not formalised (informal) |

## §14.2.1 The drift characterization of `f`-regularity

| Source | Claim | Lean |
| --- | --- | --- |
| (V3), (14.16), p. 343 | `ΔV(x) ≤ −f(x) + b 1_C(x)` for `f : X → [1, ∞)`, `b < ∞`, `V : X → [0, ∞]` | `DriftV3 P V f b C` (`PV + f ≤ V + b 1_C`, with `b ≠ ∞` assumed where used); `DriftV3.driftV2` ((V3) implies (V2) for `f ≥ 1`; `DriftV2`, carried), `DriftV3.le_add`, `DriftV3.mono` |
| (14.17), p. 343 | `f + PV ≤ V` off `C` and `f + PV ≤ b` on `C` | `driftV3_of_bounds` |
| Lemma 14.2.1, p. 343 | For a `ψ`-irreducible chain and (14.16) with `V` finite at `x₀`, `S_f = {V < ∞}` is absorbing and full | `lemma_14_2_1` (`b < ∞`), `isAbsorbing_finite_of_driftV3`; `proposition_4_2_3_i` (carried) |
| Theorem 14.2.2, p. 344 | The Comparison Theorem: `PV ≤ V − f + s` gives `Σ_{k ≤ N} E_x[f(Φ_k)] ≤ V(x) + Σ_{k ≤ N} E_x[s(Φ_k)]` and `E_x[Σ_{k<τ} f(Φ_k)] ≤ V(x) + E_x[Σ_{k<τ} s(Φ_k)]` | `theorem_14_2_2` (measurable `V`, `f`, `s : X → [0, ∞]`; any stopping time `τ`) |
| p. 344 | Proof: Proposition 11.3.2 with `f_k = f`, `s_k = s` | `comparison_theorem_pathKernel` (carried), `lintegral_coord_eq_pow`, `lintegral_sumBefore_const` |
| p. 344 | The second bound is the crucial one | Not formalised (remark) |
| (14.18), p. 344 | `G_C(x, f) = E_x[Σ_{k=0}^{σ_C} f(Φ_k)]` | `gKernelFn P C f` (carried); `measurable_gKernelFn`, `gKernelFn_of_mem`, `gKernelFn_le`, `gKernelFn_le_two_mul`, `tabooPotFn_le`, `tabooPotFn_indicator_le`, `sumBefore_indicator_succ_le` |
| Theorem 14.2.3 (i), p. 344 | Under (V3) for a petite `C`, every `B ∈ B⁺(X)` has `c(B) < ∞` with `E_x[Σ_{k<τ_B} f(Φ_k)] ≤ V(x) + c(B)`; a set on which `V` is bounded is `f`-regular | `theorem_14_2_3_i`, `theorem_14_2_3_i_fRegular`, `isFRegularState_of_driftV3` |
| Theorem 14.2.3 (ii), p. 344 | An `f`-regular `C ∈ B⁺(X)` is petite, and `V = G_C(·, f)` satisfies (V3) and is bounded on every `f`-regular set | `theorem_14_2_3_ii` (`f ≥ 1`) |
| pp. 344–345 | Proof of (i): the Comparison Theorem, Lemma 11.3.10 and `1_C ≤ ψ_a(B)⁻¹ K_a(·, B)` (11.27), with `m_a < ∞` from Proposition 5.5.6 | `lintegral_sumBefore_indicator_le` (the occupation bound `E_x[Σ_{k<τ_B} 1_C(Φ_k)] ≤ c`, from the proof of Theorem 11.3.11), `comparison_theorem_pathKernel` (carried), in the proof of `theorem_14_2_3_i` |
| p. 345 | Proof of (ii): `C` is regular, hence petite by Proposition 11.3.8; (V3) for `G_C(·, f)` by Theorem 11.3.5 | `IsFRegularSet.isRegularSet`, `proposition_11_3_8` (carried), `driftV3_gKernelFn` (if `U_C(·, f) ≤ b` on `C`, `G_C(·, f)` solves (V3); Theorem 11.3.5 (i)) |
| p. 350 (from Theorem 14.2.3 (i)) | Under (V3) for a petite set, every `λ` with `λ(V) < ∞` is `f`-regular | `isFRegularMeasure_of_driftV3` |

## §14.2.2 `f`-Regular sets

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 14.2.4, (14.19), p. 345 | For a `ψ`-irreducible chain, `C` is petite with `sup_{x ∈ C} E_x[Σ_{k<τ_C} f(Φ_k)] < ∞` iff `C` is `f`-regular and `C ∈ B⁺(X)` | False as stated: `theorem_14_2_4_counterexample` (`C = ∅`). Corrected: `theorem_14_2_4` (`C` non-empty, `f ≥ 1`) |
| pp. 345–346 | Proof: (V3) for `G_C(·, f)` by Theorem 11.3.5, then Theorem 14.2.3; `C` is Harris recurrent, so in `B⁺(X)` by Proposition 9.1.1; conversely Proposition 11.3.8 | `driftV3_gKernelFn`, `theorem_14_2_3_i_fRegular`; `ψ(C) > 0` from `theorem_11_3_14` (carried) through `meanReturnTime_le_fSumReturn`; `proposition_11_3_8` (carried) |
| Theorem 14.2.5, (14.20), p. 346 | From an `f`-regular `C ∈ B⁺(X)`, increasing `f`-regular sets whose union `S_f` is full and absorbing, with `Φ` `f`-regular on `S_f` and `X = S_f ∪ N` | `theorem_14_2_5` (`S_f(n) = {G_C(·, f) ≤ n}`, `f ≥ 1`) |
| p. 346 | Proof: Theorem 14.2.3 (ii) and Lemma 14.2.1 | `theorem_14_2_3_ii`, `lemma_14_2_1`, `theorem_14_2_3_i_fRegular`, `IsFRegularSet.exists_le`, in the proof of `theorem_14_2_5` |
| Theorem 14.2.6, p. 346 | The chain is `f`-regular iff (V3) holds for an everywhere finite `V`, and every sublevel set of `V` is then `f`-regular | `theorem_14_2_6` (a petite set and a finite `b`; `f ≥ 1`), `theorem_14_2_6_sublevel`, `IsFRegularChain.exists_pos` |
| Theorem 14.2.7, p. 346 | The chain is `f`-regular iff some petite `C` has `E_x[Σ_{k<τ_C} f(Φ_k)]` finite for every `x` and bounded on `C` | `theorem_14_2_7` (`f ≥ 1`) |

## §14.2.3 `f`-Regularity and `m`-skeletons

| Source | Claim | Lean |
| --- | --- | --- |
| (14.21), p. 347 | `PᵐV ≤ V − Σ_{i<m} Pⁱf + b Σ_{i<m} Pⁱ1_C` | `driftV3_iterate` |
| (14.22), p. 347 | `g^{(m)} = Σ_{i<m} Pⁱg` | `fSkel`, `measurable_fSkel`, `lintegral_pow_le_fSkel`, `le_fSkel`, `one_le_fSkel`, `fSkel_one`, `lintegral_fSkel` (`π(f^{(m)}) = m π(f)`) |
| Lemma 14.2.8, p. 347 | For an aperiodic chain, a petite `C`, `ε > 0` and `m ≥ 1`, a petite `C_ε` with `1_C^{(m)} ≤ m 1_{C_ε} + ε` | `lemma_14_2_8` (`C_ε` is small for the `m`-skeleton; `IsSmall`, carried) |
| p. 347 | Proof: aperiodicity (5.40) and "petite sets are small, proven in Proposition 5.5.7" give `P^{km−i}(x, ·) ≥ 1_C(x) ν` for `0 ≤ i < m` | `exists_forall_large_minorization` (one `ν` and a minorization of `Pᵗ` on `C` for every large `t`, the proof of Theorem 5.5.7 at all large times; `theorem_5_5_7`, carried). The result cited is Theorem 5.5.7 |
| Theorem 14.2.9, p. 347 | For a `ψ`-irreducible aperiodic chain, `C ∈ B⁺(X)` is `f`-regular iff it is `f^{(m)}`-regular for one, and then every, `m`-skeleton | `theorem_14_2_9` (`f ≥ 1`); `IsFRegularSet.of_skeleton`, `IsFRegularSet.skeleton` |
| p. 348 | Proof: by the Markov property, the skeleton sums dominate `E_x[Σ_{j<τ_B} f(Φ_j)]`; conversely (V3) for `Pᵐ` with `½ f^{(m)}` by Lemma 14.2.8 | `fSumReturn_le_skeleton` (`τ_B ≤ m τ_B^{(m)}`), `measurableSet_natFilt_lt_firstReturn_skeleton`, `tsum_eq_tsum_sum_block`; `driftV3_skeleton`, `fSumReturn_const_mul`, `IsFRegularSet.of_half` |
| Theorem 14.2.10, p. 348 | For a `ψ`-irreducible aperiodic chain, `Φ` is `f`-regular iff each `m`-skeleton is `f^{(m)}`-regular | `theorem_14_2_10` (`f ≥ 1`); `isFRegularChain_of_skeleton` (one skeleton suffices) |
| p. 348 | Some skeleton is strongly aperiodic and can be split | `exists_skeleton_minorization` (carried) |
| Theorem 14.2.11, p. 348 | For a positive recurrent chain with `π(f) < ∞`, `f`-regular sets `S_f(n)` whose union is full | `theorem_14_2_11_of_isPositive` (every positive chain); `theorem_14_2_11` (aperiodic), `Minorization.exists_fRegular_cover` (a minorization on a set in `B⁺(X)`), `exists_fRegularSet_pos` |
| p. 348 | Proof: Proposition 14.1.2 for the split `m`-skeleton, the proof of Proposition 11.1.3, and Theorem 14.2.9 | For aperiodic chains: `Minorization.exists_fRegular_cover` (the sets `{x : Ě_{x*}[G_{α̌}(·, f̌)] ≤ n}`, by `proposition_14_1_2_ii` for the split chain), `exists_skeleton_minorization` (carried), `IsFRegularSet.of_skeleton`. The split skeleton exists only for aperiodic chains. The general case goes through the lazy chain `K = ½ (I + P)` (`lazyKernel`, carried): `isAperiodic_lazyKernel`, `half_le_lazyKernel`, `fSumReturn_le_lazy`, `sumBefore_firstHit_add_one_indicator`, `gKernelFn_indicator_eq`, `fSumReturn_eq_add_lintegral_gKernelFn`, `gKernelFn_indicator_of_notMem` |

## §14.3.1 The aperiodic `f`-ergodic theorem

| Source | Claim | Lean |
| --- | --- | --- |
| p. 349 | The strongly aperiodic case is an easy consequence of the atom case | Not formalised (informal) |
| Proposition 14.3.1, p. 349 | Standing hypothesis: `Φ` is strongly aperiodic and positive recurrent, and `f ≥ 1` | A minorization `M : Minorization P` (carried) on `C` with `ψ(C) > 0` and `ν(C) > 0`, and `IsPositive P ψ`; such a chain is aperiodic (`isAperiodic_of_minorization`) |
| Proposition 14.3.1 (i), p. 349 | If `π(f) = ∞`, `Pᵏ(x, f) → ∞` for every `x` | `proposition_14_3_1_i` |
| Proposition 14.3.1 (ii), p. 349 | If `π(f) < ∞`, almost every state is `f`-regular and `‖Pᵏ(x, ·) − π‖_f → 0` for every `f`-regular `x` | `proposition_14_3_1_ii`; `Minorization.tendsto_fNorm` (from every probability `λ` with `E_λ[Σ_{k<τ_R} f(Φ_k)] < ∞` for one `R ∈ B⁺(X)`) |
| Proposition 14.3.1 (iii), p. 349 | An `f`-regular chain is `f`-ergodic | `proposition_14_3_1_iii` |
| p. 349 | Proof of (i): `lim inf Pᵏ(x, f) ≥ π(m ∧ f)` on the maximal Harris set, then Fatou's lemma | `tendsto_lintegral_top_of_isPositive` (total variation convergence off a `ψ`-null set, `tendsto_tvNorm_of_isPositive`, carried, and Fatou's lemma from a time `n₀` with `P^{n₀}(x, ·)` charging that set) |
| p. 349 | Proof of (ii): "obvious using the split chain" | `Minorization.fSumReturn_split`, `Minorization.fSumReturn_splitK` (return sums of the split chain from `λ*` are those of `Φ` from `λ`), `Minorization.lintegral_split_comp_fst`, `Minorization.split_positive`, `Minorization.exists_tabooPotFn_le`, `tabooPotFn_eq_of_kernel_eq`, `exists_mem_ne_top_of_lintegral`, `fNorm_map_le`; `split_comp_pow_map_fst` (carried) |
| p. 349 | For aperiodic chains some skeleton is strongly aperiodic; apply "Theorem 14.3.1" to it | `exists_skeleton_minorization` (carried). "Theorem 14.3.1" is Proposition 14.3.1 |
| Lemma 14.3.2 (i), p. 349 | `‖Pⁿ(x, ·) − π‖_f ≤ ‖P^{km}(x, ·) − π‖_{f^{(m)}}` for `n = km + i`, `0 ≤ i < m` | `lemma_14_3_2_i`, `lemma_14_3_2_i_measure` (from an initial law) |
| Lemma 14.3.2 (ii), p. 349 | `‖P^{km}(x, ·) − π‖_{f^{(m)}} → 0` gives `‖Pᵏ(x, ·) − π‖_f → 0` | `lemma_14_3_2_ii` |
| Lemma 14.3.2 (iii), p. 349 | An `f^{(m)}`-ergodic skeleton makes `Φ` `f`-ergodic | `lemma_14_3_2_iii` (`ψ`-irreducible, `f ≥ 1`) |
| p. 350 | Proof: `|Pⁿ(x, g) − π(g)| = |P^{km}(x, Pⁱg) − π(Pⁱg)|` | `fNorm_comp_le` in the proof of `lemma_14_3_2_i` |
| Theorem 14.3.3 (i), p. 350 | For a positive recurrent aperiodic chain, `π(f) = ∞` gives `Pᵏ(x, f) → ∞` for every `x` | `theorem_14_3_3_i`, `tendsto_lintegral_top_of_isPositive` |
| Theorem 14.3.3 (ii), p. 350 | If `π(f) < ∞`, the `f`-regular states form a full absorbing set `S_f`, and `‖Pᵏ(x, ·) − π‖_f → 0` for `x ∈ S_f` | `theorem_14_3_3_ii` (`f ≥ 1`); `exists_fRegular_driftV3` (the `f`-regular states are `{G_C(·, f) < ∞}` for an `f`-regular `C ∈ B⁺(X)`) |
| Theorem 14.3.3 (iii), p. 350 | An `f`-regular chain is `f`-ergodic; an `f`-ergodic chain is `f`-regular on a full absorbing set | `theorem_14_3_3_iii`, `theorem_14_3_3_iii_converse` |
| p. 350 | Proof: the skeleton is strongly aperiodic and the sets `S_f(n)` are `f^{(m)}`-regular; Proposition 14.3.1 and Lemma 14.3.2 | `tendsto_fNorm_of_driftV3` (the skeleton drift `driftV3_skeleton`, Theorem 14.2.3 (i) for the skeleton, the split skeleton `Minorization.tendsto_fNorm` and `lemma_14_3_2_i_measure`), applied to `V = G_C(·, f)` |
| p. 350 | An `f`-ergodic chain need not be `f`-regular, already for `f = 1` | Not formalised (remark) |

## §14.3.2 Sums of transition probabilities

| Source | Claim | Lean |
| --- | --- | --- |
| (14.23), p. 350 | `Σₙ ‖Pⁿ(x, ·) − π‖_f` | Sums of `fNorm` in `[0, ∞]` (`tsum`, Mathlib) |
| p. 350 | Under (V3) for a petite set, `λ(V) < ∞` makes `λ` `f`-regular | `isFRegularMeasure_of_driftV3` |
| Theorem 14.3.4, (14.24), p. 350 | For an aperiodic positive Harris chain with `π(f) < ∞` and an `f`-regular `C ∈ B⁺(X)`, `Σ_{n ≥ 1} ∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖_f ≤ M_f (λ(V) + μ(V) + 1)` with `V = G_C(·, f)` | `theorem_14_3_4` (positivity suffices; for all probabilities `λ`, `μ`, finite for `f`-regular ones by `lintegral_gKernelFn_ne_top`) |
| p. 351 | Proof: the split chain with the `f`-regular `C₀ ∪ C₁`, `λ*(Ǧ) = λ(G)`, (13.57); the general case by Lemma 14.3.2 and a skeleton | `Minorization.tsum_fNorm_le` (the strongly aperiodic case, pointwise); `tsum_fNorm_le_of_driftV3` (the skeleton, `driftV3_skeleton`, `driftV3_iterate`, `tsum_eq_tsum_sum_block`, `fNorm_comp_le`), `theorem_14_2_3_ii`, `lintegral_lintegral_affine`, `tsum_lintegral_le_lintegral_tsum` |
| Theorem 14.3.5, (14.25), p. 351 | For an aperiodic positive Harris chain with `f`-regular `π`, `π(f) < ∞` and `Σₙ ‖λPⁿ − π‖_f ≤ B_f (λ(V) + 1)` for `f`-regular `λ` | `theorem_14_3_5` (positivity suffices; the sum over `n ≥ 0`, for every probability `λ`); `fNorm_comp_pow_le_lintegral`, `lintegral_dirac_le` |
| Theorem 14.3.6 (i), (14.26), p. 351 | For a positive recurrent chain with `π(f) < ∞`, a full `S_f`, a cycle `{Dᵢ}` in `S_f` and probabilities `πᵢ` with `‖P^{nd+r}(x, ·) − π_r‖_f → 0` for `x ∈ D_r` | `theorem_14_3_6_i` (convergence on `Dᵢ ∩ S_f` to `π_{i+r}`, `πᵢ = d π(· ∩ Dᵢ)`, `cycleInv`, carried), `theorem_14_3_6_i_cycle` (the cycle inside a measurable full absorbing `S_f`), `theorem_14_3_6_i_book` (the labelling of (14.26), with `π_r = d π(· ∩ D_{2r})`); `f ≥ 1` |
| Theorem 14.3.6 (ii), (14.27), p. 351 | For an `f`-regular chain, `‖d⁻¹ Σ_r P^{nd+r}(x, ·) − π‖_f → 0` for all `x` | `theorem_14_3_6_ii_all` (every `x`; `r` runs over `0 ≤ r < d`), `theorem_14_3_6_ii` (every `x` in the cycle `⋃ Dᵢ`) |
| p. 351 | Theorem 14.3.6 is stated without proof | (i): `IsCycle.absorbKernel_isPositiveHarris` (the chain moving by `Pᵈ` on `Dᵢ` and jumping to `πᵢ` off it is positive Harris and aperiodic; `absorbKernel`, carried), `IsCycle.fRegular_absorbKernel` (Theorem 14.3.3 for it), `absorbKernel_maximalHarris` (carried, the maximal Harris set), `exists_absorbing_subset`, `IsCycle.inter_absorbing`, `cycleInv_inter_of_null`. (ii) on the cycle: `IsCycle.fSumReturn_skeleton_le`, `fSumReturn_eq_add_tabooPotFn`, `sumBefore_firstReturn_eq_add`, `tabooPotFn_absorbKernel_of_mem`, `fSumReturn_absorbKernel_of_mem`, `fNorm_smul_sum_le`. (ii) for every `x`: `IsCycle.isFRegularState_absorbKernel`, `exists_mixture_bound`, `IsCycle.exists_mixture_set`, `tendsto_of_tendsto_mul_add`, `tendsto_tsum_of_le`, and the first-entrance decomposition `pow_succ_eq_firstEntrance` (carried) |

## §14.3.3 A criterion for finiteness of `π(f)`

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 14.3.7, p. 352 | For a positive recurrent chain with `π` and finite-valued `V`, `f`, `s ≥ 0` with `PV ≤ V − f + s`, `π(f) ≤ π(s)` | `theorem_14_3_7` (any finite invariant measure `π`; measurable `V`, `f`, any `s`; `V < ∞` `π`-a.e.); `lintegral_le_of_driftV3` (the case `s = b 1_C`: `π(f) ≤ b π(C)`) |
| p. 352 | Proof: the Comparison Theorem and the ergodic theorems, `π(f) = lim N⁻¹ Σ_{k ≤ N} E_x[f(Φ_k)] ≤ π(s)` | Replaced by truncation: `min(PV, n) + f 1_{V ≤ n} ≤ min(V, n) + s`, integrated against `π`, in the proof of `theorem_14_3_7` |
| p. 352 | The criterion for `π(X) < ∞` in Theorem 11.0.1 is a special case | Not formalised (remark) |

## §14.4.1 Random walk on `ℝ₊` and storage models

| Source | Claim | Lean |
| --- | --- | --- |
| p. 352 | `Φₙ = [Φₙ₋₁ + Wₙ]⁺` with negative mean and finite absolute moment of order `k` | `halfLineWalkKernel Γ` (carried) on `ℝ≥0`; the moments are `Integrable (fun w => |w| ^ l) Γ` (Mathlib) for `l ≤ k + 1` |
| (14.28), p. 352 | `ΔV(x) ≤ k xᵏ⁻¹ ∫ y Γ(dy) + c σ^{(k)} xᵏ⁻² + d` for `V(x) = xᵏ` | `integral_max_add_pow_le` (for `x ≥ 1`); `integral_add_pow` (the binomial expansion), `max_add_pow_le`, `max_add_pow_le_two_pow`, `abs_integral_pow_le`, `integrable_pow_of_abs`, `integrable_max_add_pow`, `lintegral_halfLine_pow`, `halfLine_drift_pow` |
| Proposition 14.4.1, p. 352 | With mean `β < 0` and finite `(k + 1)`-st moment the walk is `|x|ᵏ`-regular, and `π` has finite `k`-th moment | `proposition_14_4_1` (`ψ`-irreducible, aperiodic, positive Harris and `f_k`-regular for `f_k(x) = xᵏ + 1`; every invariant probability has `∫ xᵏ dπ < ∞`) |
| Proposition 14.4.1 (i), p. 353 | `∫ λ(dx) ‖Pⁿ(x, ·) − π‖_{f_k} → 0` for every `λ` with `∫ λ(dx) x^{k+1} < ∞` | `proposition_14_4_1_i_integrated`; `proposition_14_4_1` gives the pointwise limit for every `x` and `‖λPⁿ − π‖_{f_k} → 0` |
| Proposition 14.4.1 (ii), p. 353 | `Σₙ ∫ λ(dx) ‖Pⁿ(x, ·) − π‖_{f_{k−1}} ≤ B_f (1 + ∫ xᵏ λ(dx))` for every `λ` | `proposition_14_4_1` (for `k ≥ 1`) |
| (14.29), p. 353 | `P V_{i+1} ≤ V_{i+1} − c₀ f_i + d₀ 1_C` for `0 ≤ i ≤ k`, `C` compact | `halfLine_drift_14_29` (`C = [0, X₀]`) |
| p. 353 | Proof: (i) from the `f`-Norm Ergodic Theorem; (ii) by Theorem 14.3.7 and (14.29) for `i = k − 1` | `theorem_14_0_1_consequences`, `tendsto_fNorm_of_driftV3`, `lintegral_le_of_driftV3`, `theorem_14_2_6` in the proof of `proposition_14_4_1`; (i) in integrated form by `measurable_fNorm_kernel`, `tendsto_lintegral_of_le_of_tendsto`, `tendsto_lintegral_of_tendsto_fNorm` and `lintegral_pow_le_of_drift` |
| p. 353 | The invariant measure has moments one degree lower than the increments; Moran dam and queueing models | Not formalised (informal) |

## §14.4.2 Bilinear models

| Source | Claim | Lean |
| --- | --- | --- |
| (14.30), p. 353 | `Xₖ₊₁ = θXₖ + bWₖ₊₁Xₖ + Wₖ₊₁`, `E[W] = 0` | `bilinearKernel Γ θ b` (carried) |
| (14.31), p. 353 | `E[X²ₖ₊₁ | Xₖ = x] ≤ (θ² + b² E[W²]) x² + (2bx + 1) E[W²]` | `bilinear_moment_two` (`E|θ + bW|² = θ² + b² E W²` for centred `W`); the drift is `bilinear_driftV3`, from `bilinear_lintegral_pow_le` (Minkowski: `E|θx + bxW + W|ᵏ ≤ (‖θ + bW‖_k |x| + ‖W‖_k)ᵏ`) and `bilinear_real_drift` |
| (14.32), p. 354 | (V3) with `f = 1 + δV`, `V(x) = x²`, when `θ² + b² E[W²] < 1` | `bilinear_condition_14_32` (the case `k = 2` of the condition `E|θ + bW|ᵏ < 1` of `proposition_14_4_2`) |
| p. 354 | For a T-chain, (14.32) gives positive Harris recurrence and a second order stationary model | Not formalised (informal); the T-chain step is replaced by hypotheses of `proposition_14_4_2` |
| Proposition 14.4.2, (14.33), p. 354 | Under (SBL1), (SBL2) and `E[Wₙᵏ] < ∞`, the model is positive Harris, `∫ xᵏ π(dx) < ∞` and `‖Pⁿ(x, ·) − π‖_{xᵏ} → 0` | False as stated: `proposition_14_4_2_counterexample` (`W` uniform on `(−1, 1)`, `uniformPM1`, with `θ = 2`, `b = 0`; `uniformPM1_eq`, `isProbabilityMeasure_uniformPM1`, `ae_uniformPM1_mem`). Corrected: `proposition_14_4_2` (`E|W|ᵏ < ∞` and `E|θ + bW|ᵏ < 1`; `ψ`-irreducibility, aperiodicity and petite compact sets assumed; convergence in `‖·‖_{|x|ᵏ+1}`) |
| p. 354 | A geometric rate in the next chapter | Not formalised (forward reference) |

## §14.5 A key renewal theorem

| Source | Claim | Lean |
| --- | --- | --- |
| p. 354 | `Zₙ = Σ_{i ≤ n} Yᵢ` with i.i.d. `Yᵢ ~ Γ` on `ℝ₊` and `Y₀ ~ Γ₀`; the renewal measure `U = Σₙ Γ^{n∗}` | `renMeas Γ μ` (`μ ∗ U`, the expected number of epochs `resEpoch x Y`, carried, in a set, for `x ~ μ` and increments `incr Γ`); `renMeas_apply`, `renMeas_dirac_apply`, `measurable_renMeas_dirac`, `measurable_renMeas_dirac_fun`, `renMeas_eq_lintegral`, `renMeas_eq_bind`, `lintegral_renMeas`, `renMeas_eq_map_prod`, `sFinite_renMeas`, `incr_map_partialSum` (`Y₀ + ⋯ + Y_{m−1}` has law `Γ^{m∗}`; `convPow`, carried), `renMeas_add`, `renMeas_dirac_add`, `renMeas_dirac_eq_map`, `renMeas_map_add_apply`, `renMeas_mono_smul` |
| p. 354 (used) | `U[0, t] < ∞` | `renMeas_dirac_Iic_le` (`δ_x ∗ U(−∞, t] ≤ e^{t−x}/(1 − φ)`, `φ = ∫ e^{−y} Γ(dy)`), `renMeas_Iic_le`, `lintegral_exp_neg_partialSum`, `exp_moment_lt_one`, `renMeas_Iic_zero` |
| (14.34), p. 354 | `Γ₀ ∗ U ∗ f(t) → β⁻¹ ∫₀^∞ f(s) ds` | `convAt` (`ρ ∗ g(t) = ∫ g(t − u) ρ(du)`); for Lipschitz `g` with compact support and `Γ₀ = δ₁`, `tendsto_convAt_of_lipschitz`; uniform forms in Theorem 14.5.2 below |
| Theorem 14.5.1, (14.35), p. 354 | Blackwell's Renewal Theorem: for `Γ` with finite mean `β`, not concentrated on a lattice `nh`, and any `Γ₀`, `Γ₀ ∗ U[a + t, b + t] → β⁻¹ (b − a)` | `theorem_14_5_1` (`Γ` on `[0, ∞)` with `Γ(0, ∞) > 0`, `IsNonLattice`, `renMean Γ ≠ ∞`; any first-epoch probability on `ℝ`; `a ≤ b`); `theorem_14_5_1_spreadOut` (spread-out `Γ`, from (14.40)) |
| p. 355 | Proof: taken from Feller ([115], p. 360) | Proved: the maximum principle `eventually_sub_le_of_harmonic`, `tendsto_sub_of_harmonic`, `continuous_of_unifCont`; support points `IsSupportPoint`, `measure_not_isSupportPoint`; the closed subgroup `tendsto_sub_of_isNonLattice` (`AddSubgroup.dense_or_cyclic`, Mathlib); the epoch laws `epochLaw`, `epochLaw_zero`, `epochLaw_succ`, `isProbabilityMeasure_epochLaw`, `secondLaw_Iic_zero`, `epochLaw_Iic_zero`, `secondLaw_Icc_ge`, `epochLaw_Icc_ge`, `epochLaw_charges`; `exists_window_bound` (`sup_t δ₁ ∗ U[t, t + l] < ∞`), `integrable_comp_sub_renMeas`, `integrable_comp_sub_prob`, `convAt_renMeas_eq_integral`, `convAt_eq_iterate`, `tendsto_convAt_of_lipschitz`; trapezoids `trap`, `trap_nonneg`, `trap_le_one`, `abs_trap_le`, `trap_of_neg`, `trap_of_gt`, `trap_eq_one`, `abs_trap_sub_le`, `continuous_trap`, `integrable_trap`, `integral_trap_ge`, `integral_trap_le`; `blackwell_dirac` (first epoch `1`) |
| p. 355 | The general Key Renewal Theorem: (14.34) for bounded non-negative directly Riemann integrable `f` (Feller, p. 361) | Not formalised (quoted) |
| p. 355 | In the limit `U` approximates normalised Lebesgue measure | Not formalised (informal) |
| Theorem 14.5.2 (i), (14.36)–(14.39), p. 355 | For spread-out `Γ` with finite mean and any `Γ₀`, `sup_{|g| ≤ f} |Γ₀ ∗ U ∗ g(t) − β⁻¹ ∫ g| → 0` for `f ≥ 0` bounded, integrable, with `f(t) → 0` | `theorem_14_5_2_i` (`Γ₀` on `(0, ∞)`; `f` measurable and vanishing on `(−∞, 0)`; `IsSpreadOut`, carried) |
| Theorem 14.5.2 (ii), (14.40), p. 355 | For a bounded interval `[a, b]`, `sup_{B ⊆ [a, b]} |Γ₀ ∗ U(t + B) − β⁻¹ μ_Leb(B)| → 0` | `theorem_14_5_2_ii` (Borel `B`) |
| Theorem 14.5.2 (iii), p. 355 | For absolutely continuous `Γ₀`, (14.36) holds for `f` satisfying only (14.37)–(14.38) | `theorem_14_5_2_iii` (`Γ₀ ≪ μ_Leb` on `(0, ∞)`); see corrections for the proof |
| pp. 355–356 | The trade-offs against Blackwell's theorem; the analogy with total variation | Not formalised (informal) |
| p. 356 | The forward recurrence time `V⁺(t)` and its `δ`-skeleton `V⁺_δ` with kernel `P^{nδ}`; `[0, δ]` is small (Proposition 5.3.3) and `V⁺_δ` is aperiodic (Proposition 5.4.7) | `fwdSkelKernel Γ δ` and `fwdTimeCts` (carried); `proposition_5_3_3`, `proposition_5_4_7` (carried). `fwdChain` moves by `P^δ` on `(0, ∞)` and restarts from `unifδ δ` off it: `isProbabilityMeasure_unifδ`, `isMarkovKernel_fwdChain`, `fwdSkelKernel_compl_Ioi`, `fwdChain_pow_of_pos`, `exists_pow_Ioo_pos`, `pow_add_apply_eq_lintegral`, `isPhiIrreducible_fwdChain` (the `ψ`-irreducibility the book leaves implicit) |
| p. 356 | (V2) holds with `V(x) = x`, so the chain is regular (Theorem 11.3.15), and `Γ₀` with finite mean is regular (Theorem 11.3.12) | `driftV2_fwdChain` (`V(x) = x/δ + 1`, `fwdV`, `measurable_fwdV`, `fwdV_le`, `C = (0, δ]`), `lintegral_fwdSkelKernel_le`, `ofReal_fwdTimeCts_le`, `fwdSkelInv_Iic_zero`; `fwdChain_structure` (positive, aperiodic, and initial laws of finite mean on `(0, ∞)` are regular, for small `δ`) |
| (14.41), p. 356 | `Σₙ ‖Γ₁P^{nδ} − Γ₂P^{nδ}‖ < ∞` for `Γ₁`, `Γ₂` with finite mean, from Theorem 13.4.4 | `tsum_tvNorm_fwdSkel_ne_top` (`theorem_13_4_4`, carried) |
| Proposition 14.5.3, (14.42), p. 356 | `‖Γ₁ ∗ U − Γ₂ ∗ U‖ < ∞` | `proposition_14_5_3` (finite `σ₁`, `σ₂` with `Γ₁ ∗ U + σ₂ = Γ₂ ∗ U + σ₁`; `Γ₁`, `Γ₂` on `(0, ∞)` with finite means) |
| (14.43), p. 356 | `Γ₀ ∗ U(A) = Γ₀Pˢ ∗ U(A − s)` for `A ⊆ [t, ∞)`, `s ∈ [0, t)`, by the Markov property at `s` | `renMeas_eq_lintegral_skeleton` (at `s = nδ`, for `A ⊆ (nδ, ∞)`), `tsum_indicator_resEpoch_eq` (pathwise); `lintegral_regeneration` (carried) |
| (14.44), p. 356 | Slab by slab, `‖Γ₁ ∗ U − Γ₂ ∗ U‖ ≤ U[0, δ) Σₙ ‖Γ₁P^{nδ} − Γ₂P^{nδ}‖` | `renMeas_restrict_slab`, `slab`, `iUnion_slab`, `pairwise_disjoint_slab`, `renMeas_dirac_preimage_slab_le`, `exists_jordan`, `comp_pow_Iic_zero`, in the proof of `proposition_14_5_3` |
| Proposition 14.5.4, (14.45), p. 357 | For spread-out `Γ` with finite mean and `Γ₁`, `Γ₂` with finite means, `sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) − Γ₂ ∗ U ∗ g(t)| → 0` for `f` with (14.37)–(14.39) | `proposition_14_5_4_renewal` (`f` vanishing on `(−∞, 0)`; (14.38) not needed); `proposition_14_5_4` (for any `ρ₁`, `ρ₂` with `ρ₁ + σ₂ = ρ₂ + σ₁`, `σᵢ` finite) |
| (14.46)–(14.47), p. 357 | The tail beyond `T` and the bound `ε ‖Γ₁ ∗ U − Γ₂ ∗ U‖ + εd` | `convSupDiff`, `convSupDiff_le` (`sup_{|g| ≤ f} |ρ₁ ∗ g(t) − ρ₂ ∗ g(t)| ≤ ∫ f(t − u) (σ₁ + σ₂)(du)`), then dominated convergence for `σ₁ + σ₂` in the proof of `proposition_14_5_4` |
| p. 357 | `Γₑ[0, t] = β⁻¹ ∫₀ᵗ Γ(u, ∞) du` (10.36) and `Γₑ ∗ U = β⁻¹ μ_Leb` | `eqLaw` (`Γₑ`, from `fwdSkelInv`, carried), `renMean` (`β`), `eqLaw_Iic_zero`, `renMeas_eqLaw` (on `(0, ∞)`), with `renMeas_stationary`, `eq_mul_of_add_monotone`, `renMeas_eqLaw_eq_smul`, `secondLaw`, `prod_map_second_tail`, `renMeas_eq_add` (the renewal equation `μ ∗ U = μ + (μ ∗ Γ) ∗ U`); `convAt_eqLaw` (`Γₑ ∗ U ∗ g(t) = β⁻¹ ∫_{s<t} g(s) ds`) |
| p. 357 | `Γₑ` is regular iff `Γ` has a finite second moment | Not formalised (informal) |
| Proposition 14.5.5, p. 357 | For spread-out `Γ` with finite mean and any `Γ₁`, `Γ₂`, the limit (14.45) for `f` with (14.37)–(14.39) | `proposition_14_5_5` (`Γ₁`, `Γ₂` on `(0, ∞)`, no moment condition; `f ≥ 0` vanishing on `(−∞, 0)`); `convSupDiff_triangle`, `convSupDiff_comm` |
| (14.48), p. 358 | The truncation `Γᵛ`: `|Γ₁ ∗ U ∗ g(t) − Γ₁ᵛ ∗ U ∗ g(t)| ≤ ‖Γ₁ − Γ₁ᵛ‖ sup_x U ∗ f(x)` | `truncLaw` (`μ(0, w]⁻¹ μ|_{(0, w]}`), `add_eq_truncLaw`, `convSupDiff_truncLaw_le`, `tendsto_trunc_error`, `truncLaw_props` |
| (14.49), p. 358 | `sup_x U ∗ f(x) < ∞`, from (14.47) with `Γ₁ = δ₀` and `Γₑᵛ` | `exists_renConv_bound` (`sup_{v > 0, t} δ_v ∗ U ∗ f(t) < ∞`, with first epochs `δ_v`, `v > 0`); `renConv`, `renConv_shift`, `renConv_le_Iic`, `convAt_eq_toReal`, `exists_eqLaw_Ioc_pos` |
| p. 358 | Theorem 14.5.2 "(b)" is a simple consequence of "(a)" | `theorem_14_5_2_ii_of_i` (with reflected test functions; see corrections). "(a)", "(b)", "(c)" are (i), (ii), (iii) |
| (14.50), p. 358 | Without (14.39): the set `A_ε(t) = {u ∈ [0, T] : f(t − u) ≥ ε}` has `(Γ₁ + Γ₂) ∗ U(A_ε(t)) → 0` | `tendsto_lintegral_sub_of_ac` (for a finite `σ ≪ μ_Leb`, `∫ f(t − u)⁺ σ(du) → 0`; the measure-theoretic step cited to [152], p. 125) |
| p. 358 | If `Γ₁ + Γ₂ ≪ μ_Leb` then `(Γ₁ + Γ₂) ∗ U ≪ μ_Leb` ([115], p. 146) | `renMeas_absolutelyContinuous` (for every increment law `Γ`) |
| p. 358 | Proposition 14.5.4 holds without (14.39) for `Γ₁`, `Γ₂` with densities | `proposition_14_5_4_ac` (finite means, `f` bounded, integrable, vanishing on `(−∞, 0)`); `exists_coupling_le` |
| p. 358 | Theorem 14.5.2 "(c)" follows by the truncation argument of Proposition 14.5.5 | Replaced (see corrections): `theorem_14_5_2_iii` by smoothing, `smoothFn`, `smoothBound`, `convAt_renMeas_eq_smooth` (`Γ₀ ∗ U ∗ g(t) = δ₁ ∗ U ∗ (Γ₀ ⋆ g)(t + 1)`), `tendsto_lintegral_sub_of_ac` and `theorem_14_5_2_i` |

## §14.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 359–360 | The literature on `f`-norm convergence and `f`-regularity; the converse to Proposition 14.1.1 (called "Theorem 14.1.1"); moments; the Markovian approach to renewal theory; Stone's decomposition `U = U_f + U_c`; rates of convergence through (V3) | Not formalised (commentary) |
| p. 360 | Commentary for the second edition: queueing networks, MaxWeight, Markov decision processes, polynomial rates | Not formalised (commentary) |
| (V4′), (14.51), p. 360 | The drift `ΔV ≤ −β V^ε + b 1_C` of Jarner and Roberts, `V : X → [1, ∞]` | The case `ε = ½`, written `PV + β V^{1/2} ≤ V + b 1_C`, is the hypothesis of `proposition_14_6_1`; general `ε` is not formalised |
| p. 361 | For the GI/M/1 queue with finite `n`-th moment, (V4′) holds with `V(x) = 1 + xⁿ` and `ε = 1 − n⁻¹` | Not formalised (informal) |
| Proposition 14.6.1, (14.52), p. 361 | For a `ψ`-irreducible aperiodic chain with (V4′), `ε = ½`, `C` petite and `V(x₀) < ∞`, `Σₙ ‖Pⁿ(x, ·) − π‖ ≤ B₁ V(x)^{1/2}` for `x ∈ S_V` | `proposition_14_6_1` (every `x`; `V ≥ 1`, `0 < β < ∞`, `b < ∞`) |
| p. 361 | Proof: Jensen's inequality, concavity of the square root, Foster's criterion for `U = 2β⁻¹ V^{1/2}`, and `π(V^{1/2}) ≤ β⁻¹ b π(C)` by the Comparison Theorem | `lintegral_sqrt_le`, `sqrt_add_half_le`, `rpow_half_eq_ofReal_sqrt`; the first two conclusions of `proposition_14_6_1` (`DriftV2` for `U`, and the bound on `π(V^{1/2})` through `lintegral_le_of_driftV3`); then `theorem_14_0_1_consequences` with `f ≡ 1` and `fNorm_one` |

## Measurability of the `f`-norm in the initial state

The book integrates `x ↦ ‖Pⁿ(x, ·) − π‖_f` against initial laws throughout, for instance in (14.13),
(14.24) and Proposition 14.4.1, without comment.

| Source | Claim | Lean |
| --- | --- | --- |
| (used throughout) | `x ↦ ‖κ(x, ·) − ν‖_f` is measurable | `measurable_fNorm_kernel` (countably generated space, finite kernel, `f` finite valued with `κ(x, f) < ∞` and `ν(f) < ∞`); `fSigned`, `fNorm_le_ofReal_fSigned` (a Hahn decomposition of `fμ − fν`), `ofReal_abs_fSigned_le_fNorm`, `abs_fSigned_sub_le`, `setLIntegral_le_of_withDensity_le`, `ofReal_abs_setIntegral_sub_le`, `toReal_setLIntegral_compl`, `abs_toReal_setLIntegral_sub_le`, `fNormAlgebra`, `countable_fNormAlgebra`, `measureDense_fNormAlgebra`, `fNorm_eq_iSup_fNormAlgebra` |
| Proposition 14.4.1 (i), p. 353 (used) | Dominated convergence for the integrated limit | `tendsto_lintegral_of_le_of_tendsto` (if `0 ≤ Fₙ ≤ hₙ`, `Fₙ → 0`, `hₙ → h` and `∫ hₙ → ∫ h < ∞`, then `∫ Fₙ → 0`), `tendsto_lintegral_of_tendsto_fNorm`, `lintegral_pow_le_of_drift` |
