# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University
Press, 2009): Chapter 13, pp. 313–335, with the renewal results of §14.5 (pp. 354–358), §15.1
(pp. 364–371) and Appendix D.7 (pp. 563–565). Equation numbers are the book's. Lean names are
relative to `MeynTweedie.Ergodicity`; names from Mathlib are marked as such. Names marked
"carried" are in the modules copied from the Chapter 1–11 projects (see the
[README](../README.md)). "Positive" is `IsPositive P ψ` (carried): `ψ`-irreducible with an
invariant probability, which is the book's "positive recurrent" by Proposition 10.1.1. Harris and
positive Harris chains are `IsHarris P ψ` and `IsPositiveHarris P ψ` (carried). `μP` is `P ∘ₘ μ`,
`‖μ − ν‖` is `tvNorm μ ν`, and `sup_A |μ(A) − ν(A)|` is `tvSup μ ν`. For a measurable `α`,
`tabooKernel P hα n x` (carried) is `_αPⁿ⁺¹(x, ·)`, and `tabooSeq P hα λ n` (carried) is
`λ _αPⁿ⁺¹`. Sequences on `ℤ₊` are `ℕ → ℝ`, and `a ∗ b` is `realConv a b`. Every place where the
Lean statement departs from the book is listed in [corrections](corrections.md).

## Chapter 13 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 313 | Part III: convergence to a stationary regime; (10.4); Chapter 12 | Not formalised (informal) |
| Theorem 13.0.1, p. 313 | Standing hypothesis: `Φ` is an aperiodic Harris chain with invariant measure `π` | `IsHarris P ψ` and `IsAperiodic P ψ` (carried) in `theorem_13_0_1` and `theorem_13_0_1_full`; the state space is countably generated |
| Theorem 13.0.1 (i), p. 313 | The chain is positive Harris: the unique invariant measure `π` is finite | `IsPositive P ψ`, the first condition of `theorem_13_0_1_full`; `theorem_13_0_1_finite` (for a nonzero invariant measure `π`, `π(X) < ∞` iff the chain is positive; `IsInvariantMeasure`, carried) |
| Theorem 13.0.1 (ii), (13.1), p. 313 | A `ν`-small set `C ∈ B⁺(X)` and `P^∞(C) > 0` with `Pⁿ(x, C) → P^∞(C)` for all `x ∈ C` | The second condition of `theorem_13_0_1` and `theorem_13_0_1_full` (`IsSmallSet`, carried) |
| Theorem 13.0.1 (iii), (13.2), p. 314 | A regular set in `B⁺(X)`; equivalently a petite set `C` with `sup_{x ∈ C} E_x[τ_C] < ∞` | Two conditions of `theorem_13_0_1_full`: a regular set `R` with `ψ(R) > 0` (`IsRegularSet`, carried), and a non-empty petite set with (13.2) (`IsPetite`, `meanReturnTime`, carried). The petite set must be non-empty: `theorem_11_3_14_counterexample` (carried); see corrections |
| Theorem 13.0.1 (iv), (13.3), p. 314 | A petite set `C`, `b < ∞` and `V ≥ 0` finite at some `x₀` with `ΔV ≤ −1 + b 1_C` | The last condition of `theorem_13_0_1_full`: `DriftV2 P V b C` (carried) for a measurable `V : X → [0, ∞]` finite somewhere; `driftV2_iff_drift` (carried) is the form `ΔV ≤ −1 + b 1_C` |
| (13.4), p. 314 | Any of these is equivalent to a unique invariant probability `π` with `sup_A |Pⁿ(x, A) − π(A)| → 0` for every `x` | The third condition of `theorem_13_0_1` and `theorem_13_0_1_full` (with `tvSup`); uniqueness is that of the invariant probability of a positive chain (`stationaryDist`, carried) |
| (13.5), p. 314 | For regular initial distributions `λ`, `μ`, `Σₙ ∫∫ λ(dx) μ(dy) sup_A |Pⁿ(x, A) − Pⁿ(y, A)| < ∞` | `theorem_13_0_1_sum` (for `‖·‖`, which is twice the supremum; positivity and aperiodicity suffice; `IsRegularMeasure`, carried) |
| p. 314 | Proof: (i), (iii) and (iv) are Theorem 11.0.1; (13.4) from Theorem 13.3.3; (13.4) gives (ii) by dominated convergence; (ii) gives (13.4) by Theorem 13.3.5; (13.5) from Theorem 13.4.4 | `isPositive_tfae_regular` (Theorems 11.1.4 and 11.3.14: positivity, a regular set in `B⁺(X)`, (13.2) on a non-empty petite set and (V2) on a petite set are equivalent for a `ψ`-irreducible chain; `theorem_11_3_14`, `isPositive_of_isRegularSet`, `exists_regularSet_of_isPositive`, carried); (i) ⇒ (13.4) by `theorem_13_3_3_sup`; (13.4) ⇒ (ii) with a small set from `theorem_5_2_2` (carried); (ii) ⇒ (i) by `theorem_13_3_5_positive` after dominated convergence (`tendsto_lintegral_of_dominated_convergence`, Mathlib); (13.5) by `theorem_13_4_4`. In the proofs of `theorem_13_0_1`, `theorem_13_0_1_full` and `theorem_13_0_1_sum` |
| p. 314 | Four ideas for Part III | Not formalised (informal) |
| (13.6), p. 314 | The countable space limit `|Pⁿ(x, y) − π(y)| → 0` | A consequence of (13.8), below |
| (13.7), p. 315 | `‖μ‖ = sup_{|f| ≤ 1} |μ(f)| = sup_A μ(A) − inf_A μ(A)` | `tvNorm` (`sup` over measurable `f : X → ℝ` with `|f| ≤ 1` of `|μ(f) − ν(f)|`, for the signed measure `μ − ν`), `tvValues`, `tvNorm_eq_sup_sub_inf` (through the Hahn decomposition, `IsHahnDecomposition` and `exists_isHahnDecomposition`, Mathlib), `signedValues`, `tvNorm_le_hahn`, `sub_signedValues_le_tvNorm` |
| p. 315 | Properties of the norm used in the chapter | `tvNorm_nonneg`, `tvNorm_comm`, `tvNorm_self`, `tvNorm_triangle`, `abs_integral_sub_le_tvNorm`, `tvNorm_le`, `abs_integral_sub_le_mul_tvNorm`, `tvNorm_le_add_measureReal`, `tvNorm_le_of_sub_eq`, `abs_measureReal_sub_le_tvNorm`, `tvNorm_add_le`, `tvNorm_smul_le`, `tvNorm_finsetSum_le` |
| (13.8), p. 315 | `‖Pⁿ(x, ·) − π‖ = 2 sup_A |Pⁿ(x, A) − π(A)|` | `tvNorm_eq_two_mul_tvSup` (measures of equal mass), `two_mul_abs_sub_le_tvNorm`, `abs_sub_le_tvSup`, `tendsto_tvNorm_iff_tvSup` |
| p. 315 | On a countable space (13.8) gives (13.6), uniformly in the end point | `abs_singleton_sub_le_tvNorm`; `tvNorm_eq_tsum` (`‖μ − ν‖ = Σ_y |μ{y} − ν{y}|`) |
| p. 315 | Total variation convergence implies weak convergence | `tendsto_integral_of_tendsto_tvNorm` (convergence of `μₙ(f)` for every bounded measurable `f`) |
| pp. 315–316 | Independence of initial distributions; the role of renewal theory and splitting; the term "ergodic" | Not formalised (informal) |

## §13.1.1 First-entrance last-exit decompositions

| Source | Claim | Lean |
| --- | --- | --- |
| (13.9), p. 317 | `Pⁿ(x, y) = _αPⁿ(x, y) + Σ_{j=1}^{n−1} Σ_{k=1}^{j} _αPᵏ(x, α) P^{j−k}(α, α) _αP^{n−j}(α, y)` | The atom form for `α = {α}`: `IsAtom.comp_pow_succ_firstEntrance` with `IsAtom.pow_succ_lastExit`, through `lintegral_comp_pow_succ_atom_toReal` (`isAtom_singleton`, carried) |
| (13.10)–(13.12), p. 317 | `a_x(n) = P_x(τ_α = n)`, `u(n) = P_α(Φₙ = α)`, `t_y(n) = _αPⁿ(α, y)` | `entryLaw P hα (Measure.dirac x)`, `atomRenewal P {α} α`, `lastExitSeq P hα α (1_{y})`; `entryLaw_zero`, `entryLaw_succ`, `entryLaw_nonneg`, `entryLaw_dirac_succ`, `atomRenewal_zero`, `atomRenewal_nonneg`, `atomRenewal_le_one`, `lastExitSeq_zero`, `lastExitSeq_succ`, `lastExitSeq_nonneg`, `lastExitSeq_indicator_succ` |
| (13.13), p. 317 | `π(y) = π(α) Σ_{j ≥ 1} t_y(j)`, from (10.10) | `lintegral_eq_tsum_lastExitSeq` with `f = 1_{y}`, under `π = π(α) μ°_α` (`eq_smul_atomMeasure_of_accessible`; `atomMeasure`, carried) |
| (13.14)–(13.15), p. 317 | `Pⁿ(x, α) = a_x ∗ u (n)`, `Pⁿ(α, y) = u ∗ t_y (n)` | `comp_pow_succ_atom_toReal` (`λ = δ_x`), `lintegral_pow_succ_atom_toReal` (`f = 1_{y}`), for `n ≥ 1` |
| (13.16), p. 317 | `Pⁿ(x, y) = _αPⁿ(x, y) + a_x ∗ u ∗ t_y (n)` | `lintegral_comp_pow_succ_atom_toReal` (`λ = δ_x`, `f = 1_{y}`) |
| Proposition 13.1.1, (13.17), p. 318 | For a positive Harris chain on a countable space and any `x, y, α`, `|Pⁿ(x, y) − π(y)| ≤ _αPⁿ(x, y) + |a_x ∗ u − π(α)| ∗ t_y (n) + π(α) Σ_{j > n} t_y(j)` | False as stated: `proposition_13_1_1_counterexample` (`oscKernel`, `α = 0` with `ψ{0} = 0`). Corrected: `proposition_13_1_1` (`ψ{α} > 0`; positivity and measurable singletons suffice) |
| (13.18), p. 318 | Proof: (13.16) and the representation (13.13) | `regenerative_decomposition_48` with `λ = δ_x` and `f = 1_{y}`, in the proof of `proposition_13_1_1` |

## §13.1.2 Solidarity from one ergodic state

| Source | Claim | Lean |
| --- | --- | --- |
| (13.19)–(13.21), p. 318 | If `u(n) → π(α)` and `Σ_j a_x(j) = P_x(τ_α < ∞) = 1`, then `a_x ∗ u (n) → π(α)` by Lemma D.7.1 | `tendsto_realConv_entryLaw_atomRenewal`; `hasSum_entryLaw` (`Σₙ a_λ(n) = ∫ λ(dx) L(x, α)`) |
| (13.22), p. 319 | `α ∈ B⁺(X)` is an ergodic atom if `Pⁿ(α, α) → π(α)` | `IsErgodicAtom P π α`; accessibility is a separate hypothesis where it is used (`IsAccessibleAtom`, carried) |
| p. 319 | For a positive Harris chain an atom can be ergodic only if the chain is aperiodic | `isAperiodic_of_isErgodicAtom` (for a positive chain and an accessible atom) |
| Theorem 13.1.2, (13.23), p. 319 | A positive Harris chain on a countable space with an ergodic atom has `‖Pⁿ(x, ·) − π‖ → 0` for every `x` | `theorem_13_1_2`, `theorem_13_1_2_tsum` (`Σ_y |Pⁿ(x, y) − π(y)| → 0`) |
| (13.24)–(13.27), p. 319 | Proof: the norm is `Σ_y |Pⁿ(x, y) − π(y)|`; the three terms of (13.17) tend to `0`; `Σ_y _αPⁿ(x, y) = P_x(τ_α ≥ n)` | `tvNorm_eq_tsum`, `tsum_tabooKernel_singleton` ((13.27)); the theorem is derived from the general-space form `theorem_13_3_1_i` |
| p. 320 | The approach extends to general spaces through the split skeleton | Not formalised (informal); the general results are in §§13.2.3–13.3 |

## §13.2.1 Coupling renewal processes

| Source | Claim | Lean |
| --- | --- | --- |
| p. 320 | The return times `τ_α(n)` to a recurrent atom form a renewal process | Not formalised as a process; the renewal sequence of an atom is `atomRenewal_eq_realRenewalSeq` (`u` is the renewal sequence of the return-time law `p = a_{δ_a}`), `isIncrementLaw_entryLaw`, `renewalTail_entryLaw` |
| p. 320 | Increment law `p`, delays `a`, `b`, `Sₙ` with law `a ∗ p^{n∗}` | `IsIncrementLaw` (`p ≥ 0`, `p(0) = 0`, `Σ p = 1`), `IsIncrementLaw.isDelayLaw`, `deltaSeq`, `realConvPow` (`p^{∗k}`), `realConvPow_zero`, `realConvPow_succ`, `realConvPow_eq_zero_of_lt`; delays are `IsDelayLaw` or a nonnegative `a` with `HasSum a 1` (Mathlib) |
| p. 320 | `u(n) = Σ_j p^{j∗}(n)`, `u(0) = 1`, `u(−1) = 0` | `realRenewalSeq` (the coefficients of `(1 − P)⁻¹`, `mk_realRenewalSeq`), `realRenewalSeq_eq_sum_realConvPow`, `realRenewalSeq_zero`, `realRenewalSeq_nonneg`, `realRenewalSeq_le_one`; `u(−1) = 0` is the convention of `seqDiff` |
| p. 320 | The renewal indicators `Z(n)` and `P_a(Z(n) = 1) = a ∗ u (n)` | `delayedRenewal a p` (`a ∗ u`) is the definition; the indicator process is not formalised |
| (8.12), p. 367 (used in §13.2) | The renewal equation `u = δ₀ + p ∗ u` | `realRenewalSeq_eq`, `realRenewalSeq_succ`, `one_sub_mul_mk_realRenewalSeq`, `mk_realRenewalSeq_mul_one_sub`, `realRenewalSeq_eq_realConv_of_pos` |
| p. 321 | Two independent renewal processes on one probability space; the coupling time `T_ab` | Not formalised as random variables; the coupling is expressed through the linked forward recurrence time chain `V*` (`linkedFwdRec`, carried, (10.19)) started from `a ⊗ b` |
| (13.28), p. 321 | `m_p = Σ j p(j)` | `incrMean` (`0` when the series diverges), `one_le_incrMean`, `hasSum_renewalTail` (`Σ_n tail(n) = m_p`), `sum_range_renewalTail`, `tendsto_sum_renewalTail_atTop`, `summable_renewalTail_iff`; `renewalTail` (`Σ_{j > n} p(j)`), `renewalTail_eq_tsum`, `renewalTail_nonneg`, `renewalTail_le_one`, `renewalTail_zero`, `renewalTail_succ`, `tendsto_renewalTail`, `mk_renewalTail` |
| p. 321 | Aperiodicity of `p` | `IsAperiodicLaw` (the only common divisor of `{n : p(n) > 0}` is `1`), `exists_pos_incr` |
| Proposition 13.2.1, (13.29), p. 321 | For aperiodic `p` with `m_p < ∞` and proper delays `a`, `b`, `P(T_ab < ∞) = 1` | `proposition_13_2_1` (`V*` from `a ⊗ b` reaches `(0, 0)` almost surely, for probability measures `a`, `b` on `ℕ`), `linked_hitProb_eq_one` (from every state) |
| (13.30), p. 321 | `T_ab = τ_{1,1} + 1` and `P(T_ab > n) = P_{a×b}(τ_{1,1} ≥ n)` | Not formalised (`T_ab` is not constructed) |
| p. 321 | Proof: `V*` is `δ_{1,1}`-irreducible and positive Harris (§10.3.1) | Proved directly: `linked_isPhiIrreducible` (`V*` reaches `(0, 0)` from every state), `eventually_realRenewalSeq_pos` (`u(n) > 0` for large `n`, by Lemma D.7.4), `linkedInv_spec` (the invariant probability `π* = m_p⁻² (π ⊗ π)`, `linkedInv`), the support of `V⁺` (`fwdRecSupport`, `fwdRecSupport_absorbing`, `zero_mem_fwdRecSupport`, `fwdRec_pow_compl_support`) and escape probabilities (`tendsto_tabooKernel_univ_sub`, `one_sub_hitProb_le_lintegral`, `mul_one_sub_hitProb_le`), in the proof of `linked_hitProb_eq_one` |
| Theorem 13.2.2, (13.31), p. 322 | For aperiodic `p` with `m_p < ∞` and proper `a`, `b`, `|a ∗ u (n) − b ∗ u (n)| → 0` | `theorem_13_2_2` (no hypothesis on `m_p`) |
| (13.32)–(13.33), p. 322 | Proof: the coupled process `Z_ab` and `|a ∗ u (n) − b ∗ u (n)| ≤ P(T_ab > n)` | Replaced by the analytic proof of the renewal theorem, below. The special case `a = δ₀`, `b = δ₁` of (13.33) is `abs_sub_realRenewalSeq_le` (`|u(n + 1) − u(n)| ≤ P_{(0,1)}(τ_{(0,0)} ≥ n + 1)`) |
| p. 322 | Theorem 13.2.2 holds without `m_p < ∞` (§18.1.1) | `theorem_13_2_2`, `renewal_theorem_of_not_summable` (`u(n) → 0` when `m_p = ∞`) |
| pp. 320–323 (replacing the coupling proof) | The renewal theorem `u(n) → m_p⁻¹` | `renewal_theorem` (both cases; `m_p⁻¹ = 0` when the mean is infinite), `renewal_theorem_of_summable`, `renewal_theorem_of_not_summable`, by the proof of Erdős, Feller and Pollard: `realRenewalSeq_split`, `sum_Ico_incr_le_tail`, `limit_mem_unit`, `tendsto_shift_of_limsup`, `tendsto_shift_of_liminf`, `exists_shift_closure` (with Lemma D.7.4), `exists_subseq_tendsto_of_frequently`, `realRenewalSeq_isBoundedUnder_le`, `realRenewalSeq_isBoundedUnder_ge`, `limsup_mul_sum_renewalTail_le`, `one_le_liminf_mul_incrMean`; `realConv_renewalTail_renewal` (`Σ_{i ≤ n} tail(i) u(n − i) = 1`) |
| (13.20) for delays, p. 318 | `a ∗ u (n) → (Σ a) m_p⁻¹` | `delayedRenewal_tendsto` (summable `a ≥ 0`), `delayedRenewal_tendsto_of_hasSum` |

## §13.2.2 Convergence of the renewal function

| Source | Claim | Lean |
| --- | --- | --- |
| (13.34), p. 322 | The equilibrium law `e(n) = m_p⁻¹ Σ_{j > n} p(j)` | `equilibriumLaw`, `equilibriumLaw_nonneg`, `equilibriumLaw_hasSum` (`e` is a probability when `m_p < ∞`) |
| p. 322 | `e` is the invariant probability of `V⁺` (10.16) | `e` is `m_p⁻¹` times the invariant measure `fwdRecInv` (carried) of (10.16); the identification is not stated separately |
| (13.35), p. 323 | `e ∗ u (n) = m_p⁻¹` for every `n` | `realConv_equilibriumLaw_renewal` |
| (13.36), p. 323 | `|u(n) − m_p⁻¹| = |P_{δ₀}(Z(n) = 1) − P_e(Z(n) = 1)|` | Not stated separately (the process `Z` is not formalised); its content is (13.35) |
| Theorem 13.2.3, (13.37), p. 323 | For aperiodic `p` with `m_p < ∞`, `|a ∗ u (n) − m_p⁻¹| → 0` | `theorem_13_2_3` |
| Proposition 13.2.4 (i), p. 323 | For a positive recurrent aperiodic chain every atom in `B⁺(X)` is ergodic | `proposition_13_2_4_i`; `tendsto_atomRenewal_of_aperiodicLaw` (`Pⁿ(α, α) → π(α)` from the renewal theorem with `m_p = E_α[τ_α] = π(α)⁻¹`), `isAperiodicLaw_entryLaw` (the return-time law of an accessible atom of an aperiodic chain is aperiodic), `dvd_of_atomRenewal_pos`, `IsAccessibleAtom.exists_isSmallSet` (an accessible atom is `Pᵐ(a, ·)`-small), `incrMean_entryLaw` |
| Proposition 13.2.4 (ii), (13.38), p. 323 | For a positive recurrent aperiodic chain on a countable space, `‖Pⁿ(x, ·) − π‖ → 0` for every `x` | False as stated: `proposition_13_2_4_ii_counterexample` (`leakKernel`). Corrected: `proposition_13_2_4_ii` (positive Harris), `proposition_13_2_4_ii_of_reach` (positive, from every `x` with `L(x, α) = 1` for an accessible state `α`) |
| p. 323 | Proof: Proposition 10.2.2 and Theorem 13.2.3; then Theorem 13.1.2 | (i): `meanReturnTime_ne_top_of_rep` and `measure_atom_mul_meanReturnTime` (`π(α) E_a[τ_α] = 1`), then the renewal theorem. (ii): `proposition_13_2_4_ii_of_reach` from (i) and `tendsto_tvNorm_of_ergodic_atom`; `proposition_13_2_4_ii` from Theorem 13.3.3 (`theorem_13_3_3_dirac`) |
| p. 323 | The result rests on the equivalence of positivity and regularity | Not formalised (remark) |

## §13.2.3 The regenerative decomposition for chains with atoms

| Source | Claim | Lean |
| --- | --- | --- |
| (13.39), p. 324 | The first-entrance last-exit decomposition through any set `A` | The first-entrance half for any measurable `A`, as an identity of measures: `pow_succ_eq_firstEntrance`; the last-exit half is used only on atoms (`IsAtom.pow_succ_lastExit`); `firstEntrance_decomposition`, `lastExit_decomposition` (carried) |
| (13.40), p. 324 | On an atom: `Pⁿ(x, B) = _αPⁿ(x, B) + Σ_{j=1}^{n−1} Σ_{k=1}^{j} _αPᵏ(x, α) P^{j−k}(α, α) _αP^{n−j}(α, B)` | `IsAtom.pow_succ_firstEntrance`, `IsAtom.comp_pow_succ_firstEntrance`, `IsAtom.pow_succ_lastExit`; `tabooKernel_apply_le_one`, `tabooKernel_le_pow`, `tabooSeq_apply_le`, `tabooSeq_univ_add_sum` |
| (13.41), p. 324 | `E_λ[f(Φₙ)] = ∫ λ(dx) ∫ Pⁿ(x, dy) f(y)` | The integral `∫⁻ f d(λPⁿ)` against `(P ^ n) ∘ₘ λ` throughout |
| (13.42)–(13.43), p. 324 | `a_λ(n) = P_λ(τ_α = n)`; `t_f(n) = ∫ _αPⁿ(α, dy) f(y) = E_α[f(Φₙ) 1{τ_α ≥ n}]` | `entryLaw P hα λ`, `lastExitSeq P hα a f` (`a ∈ α`, measurable `f ≥ 0`); `lastExitSeq_le`, `summable_lastExitSeq`, `tabooSeq_univ_toReal` (`P_λ(τ_α ≥ n + 1) = λ(X) − Σ_{k ≤ n} a_λ(k)`), `lintegral_hitProb_eq_tsum` |
| (13.44), p. 324 | `∫ λ(dx) Pⁿ(x, α) = a_λ ∗ u (n)` | `comp_pow_succ_atom_toReal` (`n ≥ 1`) |
| (13.45), p. 324 | `∫ Pⁿ(α, dy) f(y) = u ∗ t_f (n)` | `lintegral_pow_succ_atom_toReal` (`n ≥ 1`; bounded `f`), `realConv_lastExitSeq_succ` |
| (13.46), p. 325 | `∫ λ(dx) ∫ Pⁿ(x, dw) f(w) = ∫ λ(dx) ∫ _αPⁿ(x, dw) f(w) + a_λ ∗ u ∗ t_f (n)` | `lintegral_comp_pow_succ_atom_toReal` (`n ≥ 1`) |
| Theorem 13.2.5, (13.47)–(13.48), p. 325 | For an accessible atom of a positive Harris chain, any probability `λ` and `f ≥ 0`, the Regenerative Decompositions | `theorem_13_2_5` (positivity suffices; bounded `f`); the general forms `regenerative_decomposition_47` and `regenerative_decomposition_48` need only `π = π(α) μ°_α` |
| (13.49), p. 325 | The decomposition behind (13.48) | `regenerative_identity_48` (as an identity); `abs_realConv_le_of_nonneg`, `realConv_const_left`, `toReal_ofReal_sub_ofReal_neg`, `toReal_ofReal_add_ofReal_neg` |
| (13.50), p. 325 | `∫ π(dw) f(w) = π(α) Σ_{j ≥ 1} t_f(j)`, from (10.31) | `lintegral_eq_tsum_lastExitSeq`; `eq_smul_atomMeasure_of_accessible` (`π = π(α) μ°_α` for an accessible atom of a recurrent chain, from Theorem 10.2.1 (ii), `theorem_10_2_1_ii_smul`, carried), `measure_atom_ne_zero_of_rep`, `measure_atom_toReal_of_rep`, `meanReturnTime_ne_top_of_rep`, `lintegral_tabooKernel_ne_top`, `lintegral_tabooSeq_ne_top`, `lintegral_pow_ne_top`, `hasSum_tabooKernel_univ`, `summable_tabooKernel_univ` |
| (E1)–(E3), (13.51)–(13.52), pp. 325–326 | For bounded `f` the three terms of (13.48) tend to `0` when the atom is ergodic and `λ` reaches it almost surely | `tendsto_tvNorm_of_ergodic_atom`; `hasSum_entryLaw` ((13.52)); `IsHarris.hitProb_eq_one` and `IsHarris.lintegral_hitProb_eq` (every state and every initial law reach a set in `B⁺(X)` almost surely) |
| p. 326 | Unbounded `f` and `f`-regularity (Chapter 14) | Not formalised (forward reference) |

## §13.3.1 Strongly aperiodic chains

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 13.3.1, (13.53), p. 326 | A positive Harris, strongly aperiodic chain has `‖λPⁿ − π‖ → 0` for every initial `λ` | False as stated: `theorem_13_3_1_counterexample` (`oscKernel`; `IsStronglyAperiodic`, carried). Corrected: `theorem_13_3_1_ii` (a minorization `M : Minorization P`, carried, on `C` with `ψ(C) > 0` and `ν(C) > 0`) |
| Theorem 13.3.1 (i), pp. 326–327 | With an accessible ergodic atom | `theorem_13_3_1_i`, `theorem_13_3_1_i_aperiodic` (aperiodic, with an accessible atom) |
| (13.54)–(13.56), pp. 326–327 | The three terms of (13.48), uniformly over `|f| ≤ 1` | `tvNorm_comp_pow_succ_le` (`‖λPⁿ⁺¹ − π‖ ≤ P_λ(τ_α ≥ n + 1) + Σ_{k ≤ n} |a_λ ∗ u (n − k) − π(α)| t₁(k + 1) + π(α) Σ_{j > n + 1} t₁(j)`), `tendsto_tvNorm_of_ergodic_atom` |
| Theorem 13.3.1 (ii), p. 327 | The split chain is strongly aperiodic (Proposition 5.5.6 (ii)) and positive Harris (Proposition 10.4.2), so `α̌` is ergodic by Proposition 13.2.4 | What is used is that `α̌` is reached almost surely from every state of `X̌` (`Minorization.hitProb_checkAlpha_eq_one`, by the escape function: `Minorization.escapeFn`, `Minorization.escape_first_step`, `Minorization.measurable_escapeFn`, `Minorization.escapeFn_le_one`, `Minorization.escape_eq_lintegral_baseK`, `Minorization.lintegral_P_escapeFn`, `Minorization.lintegral_splitProb`, `Minorization.lintegral_pow_escapeFn`, `Minorization.lintegral_ν_escapeFn_eq_zero`, `Minorization.tendsto_tabooKernel_univ`) and that its return-time law is aperiodic (`Minorization.isAperiodicLaw_entryLaw_checkAlpha`, which uses `ν(C) > 0`); the split invariant probability is `proposition_10_4_1_ii` (carried) |
| (13.57), p. 327 | `‖λPⁿ − π‖ ≤ ‖λ*P̌ⁿ − π̌‖` | `split_comp_pow_map_fst` (the marginal of `λ*P̌ⁿ` is `λPⁿ`), `tvNorm_le_split`, `tvNorm_map_le` |

## §13.3.2 The ergodic theorem for ψ-irreducible chains

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 13.3.2, (13.58), pp. 327–328 | If `π` is invariant, `‖λPⁿ − π‖` is non-increasing | `proposition_13_3_2` (`Antitone`, Mathlib); `tvNorm_comp_le` (`‖μP − νP‖ ≤ ‖μ − ν‖`), `integral_comp_kernel` |
| Theorem 13.3.3, (13.59), p. 328 | A positive Harris aperiodic chain has `‖λPⁿ − π‖ → 0` for every initial `λ` | `theorem_13_3_3`; `theorem_13_3_3_dirac` (from a state), `theorem_13_3_3_sup` ((13.4)) |
| (13.60), p. 328 | Proof: some skeleton is strongly aperiodic and positive Harris (Theorem 10.4.5), then (13.58) | `exists_skeleton_minorization` (a skeleton with a minorization on `C ∈ B⁺(X)` with `ν(C) > 0`, from Proposition 5.4.5 (iii), `proposition_5_4_5_iii`, carried), `exists_minorization_of_le`; `theorem_9_1_6` and `theorem_10_4_5_positive` (carried), `theorem_13_3_1_ii`, `proposition_13_3_2`, in the proof of `theorem_13_3_3` |
| Theorem 13.3.4 (i), (13.61), p. 328 | A positive Harris chain of period `d` has `‖d⁻¹ Σ_{r<d} λP^{nd+r} − π‖ → 0` | `theorem_13_3_4_i` (`IsPeriod`, carried) |
| Theorem 13.3.4 (ii), (13.62), p. 328 | For a positive recurrent chain of period `d` the same holds for every `λ` with `λ(N) = 0`, for a `π`-null `N` | `theorem_13_3_4_ii` (`N` is `ψ`-null) |
| p. 329 | Proof: the chain restricted to each cyclic set is aperiodic and positive Harris for the `d`-skeleton (§5.4.3); (ii) from Theorem 9.1.5 | Chains agreeing on an absorbing set: `absorbKernel`, `absorbKernel_of_mem`, `absorbKernel_of_notMem`, `isMarkovKernel_absorbKernel`, `absorbKernel_pow_of_mem`, `comp_absorbKernel_pow`, `comp_congr_of_compl_eq_zero`, `comp_compl_eq_zero`, `pow_compl_eq_zero_of_absorbing`, `tabooKernel_compl_eq_zero_of_absorbing`, `tabooKernel_absorbKernel_of_mem`, `hitProb_absorbKernel_of_mem`. Cycles (`IsCycle`, carried): `IsCycle.pow_d_compl_eq_zero`, `IsCycle.pow_compl_eq_zero`, `IsCycle.comp_pow_restrict_le`, `IsCycle.comp_pow_restrict`, `IsCycle.measure_le`, `IsCycle.measure_eq`, `IsCycle.measure_mul_eq_one` (`π(Dᵢ) = 1/d`), `cycleInv`, `cycleInv_compl`, `IsCycle.isProbabilityMeasure_cycleInv`, `IsCycle.comp_pow_cycleInv`, `IsCycle.isInvariant_pow_cycleInv`, `IsCycle.hitProb_pow_eq_one`, `IsCycle.tendsto_tvNorm_pow_mul`. Phase averages: `phaseAvg`, `phaseAvg_add`, `phaseAvg_smul`, `phaseAvg_zero`, `phaseAvg_finsetSum`, `phaseAvg_shift`, `phaseAvg_univ`, `isFiniteMeasure_phaseAvg`, `comp_zero_measure`, `sum_range_add_zmod`, `IsCycle.sum_restrict`, `IsCycle.sum_restrict_of_compl`, `IsCycle.tvNorm_pow_add_le`, `IsCycle.eq_smul_sum_cycleInv`, `IsCycle.tvNorm_phaseAvg_le`, `IsCycle.tendsto_phaseAvg_of_class`, `IsCycle.tendsto_phaseAvg_of_class_finite`, `IsCycle.tendsto_phaseAvg_of_union`, `IsCycle.tendsto_compl_iUnion`. For (ii): `absorbKernel_maximalHarris` (`theorem_9_1_5`, `IsMaximalHarrisSet`, carried) |
| p. 328 | The aperiodic case for positive chains that are not Harris | `tendsto_tvNorm_of_isPositive` (off a `ψ`-null set) |
| Theorem 13.3.5, (13.63)–(13.64), p. 329 | For a `ψ`-irreducible aperiodic chain with a `ν`-small `C ∈ B⁺(X)` and `∫_C ν_C(dx)(Pⁿ(x, C) − P^∞(C)) → 0`, `P^∞(C) > 0`, the chain is positive and `‖λPⁿ − π‖ → 0` for every `λ` not charging a `ψ`-null set | `theorem_13_3_5_positive` (positivity), `theorem_13_3_5_null` (the book's form), `theorem_13_3_5` (for Harris chains: every `λ`, and `P^∞(C) = π(C)`); `ν(C) > 0` is assumed, `ν_C = ν(C)⁻¹ ν|_C` |
| (13.63), p. 329 | (13.63) is ensured by (13.1) by dominated convergence | In the proof of `theorem_13_0_1` |
| (13.65), p. 329 | Proof: through the split `m`-skeleton, `δ⁻¹(P̌ⁿ(α̌, α̌) − δP^∞(C)) → 0`, so `α̌` is ergodic | `isPositive_of_tendsto_split_skeleton` (the renewal sequence of `α̌` converges to `δc > 0`, so `α̌` is recurrent with a return time of finite mean, and Kac's theorem, `theorem_10_2_2`, carried, makes the chain positive) |

## §13.4.1 A stronger coupling theorem

| Source | Claim | Lean |
| --- | --- | --- |
| Proposition 13.4.1, (13.66), p. 329 | For aperiodic `p` with `m_p < ∞` and `a`, `b` with finite means, `Σₙ |a ∗ u (n) − b ∗ u (n)| < ∞` | `proposition_13_4_1` (with the bound `(m_a + m_b) Var(u)`; `IsDelayLaw`) |
| (13.67), p. 330 | `Σₙ |a ∗ u (n) − b ∗ u (n)| ≤ Σₙ P(T_ab > n) = E[T_ab]` | Not formalised (`T_ab` is not constructed) |
| p. 330 | `V*` is positive recurrent with invariant probability `e*(i, j) = e(i)e(j)` | `linkedInv`, `linkedInv_spec`, `linkedInv_zero_one_pos` (`π*{(0, 1)} > 0` when `p(n₀) > 0` for some `n₀ ≥ 2`); `isInvariant_linkedFwdRec` (carried) |
| (13.68), p. 330 | `E_{i,j}[τ_{1,1}] < ∞` from states with `e*(i, j) > 0`, as in Proposition 11.1.1 | `linked_meanReturnTime_ne_top` (`E_{(0,1)}[τ_{(0,0)}] < ∞`); `tabooKernel_add_succ`, `mul_meanReturnTime_le` (`_αPᵏ⁺¹(x, {y}) E_y[τ_α] ≤ E_x[τ_α]`), `meanReturnTime_eq_tsum`, `linkedFwdRec_pow_atom` |
| p. 330 | `δ₀ ∗ u (n) = u(n)`, `δ₁ ∗ u (n) = u(n − 1)` | The two coordinates of `V*` from `(0, 1)`: `fwdRec_pow_apply_zero` (`Pⁿ(i, 0) = u(n − i)`), `linkedFwdRec_pow`, `linkedFwdRec_pow_apply` |
| (13.69), p. 330 | `Var(u) = Σₙ |u(n) − u(n − 1)| ≤ E_{1,2}[τ_{1,1}] + 1 < ∞` | `summable_seqDiff_realRenewalSeq`, from `abs_sub_realRenewalSeq_le` and `linked_meanReturnTime_ne_top`; `renewalVar p` is `Var(u)` |
| p. 321, §10.3.1 (used here) | The forward recurrence time chain of an increment law | `lawMeasure` (`Σₙ p(n) δₙ`), `lawMeasure_singleton`, `lawMeasure_zero`, `isProbabilityMeasure_lawMeasure`, `lintegral_lawMeasure`; `fwdRec_tabooKernel_pos`, `fwdRec_tabooKernel_zero`, `fwdRec_entryLaw` (the return time to `0` has law `p`), `fwdRec_atomRenewal` (`Pⁿ(0, 0) = u(n)`); `isMarkovKernel_linkedFwdRec`; `realRenewalSeq_add_ge` (`u(m + n) ≥ u(m) u(n)`), `le_realRenewalSeq` (`u(n) ≥ p(n)`) (`fwdRecKernel`, carried) |
| (13.70), p. 331 | `ā ∗ w (n) ≥ |u(n) − a ∗ u (n)|`, with `ā(k) = Σ_{j>k} a(j)` and `w(k) = |u(k) − u(k − 1)|` | `realConv_renewalTail_seqDiff_eq` (`ā ∗ Δv = v − a ∗ v`), `seqDiff_renewalTail_eq`, `renewalTail_nonneg_of_delay`, `renewalTail_eq_tsum_of_delay`; `seqDiff`, `seqDiff_zero`, `seqDiff_succ`, `sum_range_seqDiff` |
| (13.71)–(13.72), p. 331 | `Σₙ |u(n) − a ∗ u (n)| ≤ (Σ ā)(Σ w) = m_a Var(u)` | `abs_sub_realConv_summable`, `hasSum_renewalTail_of_delay` (`Σ ā = m_a`), `hasSum_realConv_of_nonneg` |
| (13.73), p. 331 | `Σₙ |a ∗ u (n) − m_p⁻¹| < ∞` when `e` has finite mean | `proposition_13_4_1` with `b = e`, in the proof of `proposition_13_4_2` |
| p. 331 | `m_e < ∞` iff `s_p = Σ n² p(n) < ∞`; `m_e = (s_p − m_p)/(2m_p)` | `summable_mul_equilibriumLaw_iff`, `hasSum_mul_equilibriumLaw`, `hasSum_mul_renewalTail` (`Σ_k k p̄(k) = (s_p − m_p)/2`), `sum_range_mul_renewalTail` |
| Proposition 13.4.2, (13.74), p. 332 | For aperiodic `p` with `s_p < ∞`, `Σₙ |u(n) − m_p⁻¹| ≤ Var(u)(s_p − m_p)/(2m_p) < ∞` | `proposition_13_4_2` |

## §13.4.2 General chains with atoms

| Source | Claim | Lean |
| --- | --- | --- |
| p. 332 | A probability `μ` is regular if `E_μ[τ_B] < ∞` for every `B ∈ B⁺(X)` | `IsRegularMeasure` (carried, Chapter 11); `IsRegularChain` (carried); `IsRegularChain.isRegularMeasure_dirac` (in a regular chain every state is regular) |
| Theorem 13.4.3, (13.75), p. 332 | For an aperiodic positive Harris chain with an atom `α ∈ B⁺(X)` and regular `λ`, `μ`, `Σₙ ∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` | `theorem_13_4_3` (positive and aperiodic; the integral of the sum in `[0, ∞]`, `n ≥ 1`) |
| (13.76), p. 332 | If `Φ` is regular, `Σₙ ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` for every `x`, `y` | `theorem_13_4_3_regular`, `theorem_13_4_3_states` (every state regular) |
| (13.77)–(13.79), p. 332 | By the triangle inequality it suffices to take `μ = δ_α`; the summed first decomposition (13.47) gives `E_λ[τ_α]` and a product | `tvNorm_comp_pow_succ_le_atom` (the total variation form of (13.47)), `summable_tvNorm_atom` (`Σₙ ‖λPⁿ⁺¹ − Pⁿ⁺¹(α, ·)‖ ≤ E_λ[τ_α](1 + Var(u) E_α[τ_α])`), `tsum_ofReal_tvNorm_le`; (13.78) is `lintegral_meanReturnTime_eq_tsum`; `lintegral_hitProb_eq_one_of_lintegral_meanReturnTime` (`E_λ[τ_α] < ∞` forces `P_λ(τ_α < ∞) = 1`) |
| p. 333 | `Σₙ _αPⁿ(α, X) = E_α[τ_α] < ∞`, since accessible atoms are regular (Theorems 11.1.4, 11.1.2) | `meanReturnTime_ne_top_of_rep` (from `π = π(α) μ°_α`), `meanReturnTime_eq_tsum` |
| (13.80), p. 333 | `Σₙ ∫ λ(dx) |a_x ∗ u (n) − u(n)| ≤ E_λ[τ_α] Var(u)`, from (13.71) | `entryLaw_mean`, `hasSum_renewalTail_entryLaw`, `isIncrementLaw_entryLaw_of`, `abs_sub_realConv_summable`, in the proof of `summable_tvNorm_atom` |

## §13.4.3 General aperiodic chains

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 13.4.4, (13.81), p. 333 | For an aperiodic positive Harris chain and regular `λ`, `μ`, `Σₙ ∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ < ∞` | `theorem_13_4_4` (positive and aperiodic), `theorem_13_4_4_states` (regular states `x`, `y`), `theorem_13_4_4_regular` (a regular chain) |
| p. 333 | Proof, strongly aperiodic case: the split measures are regular (Theorem 11.3.12), and (13.57) | `Minorization.lintegral_meanReturnTime_split` (`Ě_{λ*}[τ_{A × {0,1}}] = E_λ[τ_A]`), `Minorization.lintegral_meanReturnTime_checkAlpha_ne_top` (`Ě_{λ*}[τ_{α̌}] < ∞` for regular `λ`; `theorem_10_2_2`, `theorem_11_3_11_ii`, `proposition_11_3_13`, `theorem_11_3_4`, `regV`, `meanReturnTime_le_add_of_forall_le`, carried), `tsum_ofReal_tvNorm_comp_le`, `lintegral_lintegral_le_of_le_add`, `exists_tsum_tvNorm_le_split` |
| p. 333 | Proof, general aperiodic case: Proposition 13.3.2 and a skeleton, "as in the proof of Theorem 13.2.5" | `IsRegularMeasure.pow` (a regular `λ` is regular for every skeleton `Pᵐ`, through `theorem_11_3_12_ii`, `theorem_11_3_12_i`, `theorem_5_2_2` and `theorem_10_4_5_positive`, carried; not stated in the book), `tsum_comp_div`, `tsum_ofReal_tvNorm_le_skeleton` (Proposition 13.3.2 for sums), `exists_tsum_tvNorm_le`. The citation is to the proof of Theorem 13.3.3 |
| Theorem 13.4.5, (13.82)–(13.83), p. 333 | For an aperiodic positive Harris chain with an accessible atom and `E_α[τ_α²] < ∞`, `Σₙ ‖λPⁿ − π‖ < ∞` for regular `λ` | `theorem_13_4_5` (positive and aperiodic; `E_a[τ_α²] < ∞` for `a ∈ α`, through `firstReturn` and `pathKernel`, carried) |
| p. 333 | Proof: `π` is regular when (13.82) holds, as in Proposition 13.4.2, and Theorem 13.4.4 | `lintegral_meanReturnTime_ne_top_of_sq` (`E_π[τ_α] < ∞`), `tsum_tsum_add_succ`, `tsum_mul_tabooKernel_le`, `setLIntegral_compl_meanReturnTime`; then `summable_tvNorm_atom` from `λ` and from `π` and the triangle inequality, in the proof of `theorem_13_4_5` |

## §13.5 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 334–335 | Kolmogorov, Feller and Chung on the countable case; Harris and Orey; coupling from Doeblin to Pitman; Nummelin; the first-entrance last-exit decomposition; the term "ergodic"; no examples; coupling proofs of the ergodic theorem | Not formalised (commentary) |

## §14.5 A key renewal theorem

The book's results are for a renewal measure on `ℝ₊`. The forms proved here are for renewal
sequences on `ℤ₊`, where direct Riemann integrability reduces to summability and spread-out
increments reduce to aperiodicity.

| Source | Claim | Lean |
| --- | --- | --- |
| (14.34), p. 354 | `Γ₀ ∗ U ∗ f (t) → β⁻¹ ∫ f` | `key_renewal_theorem` (`u ∗ b (n) → m_p⁻¹ Σ b` for `Σ |b| < ∞`), `delayed_key_renewal_theorem` (`a ∗ u ∗ b`); `tendsto_realConv_of_summable_abs` |
| Theorem 14.5.1, (14.35), p. 354 | Blackwell's theorem: `Γ₀ ∗ U[a + t, b + t] → β⁻¹(b − a)` for a non-lattice `Γ` with finite mean | `blackwell_renewal_theorem` (the expected number of renewals in `[n, n + h)` tends to `h/m_p`, for aperiodic `p`, with no finite-mean hypothesis) |
| Theorem 14.5.2 (i), (14.36)–(14.39), p. 355 | The Uniform Key Renewal Theorem for spread-out `Γ` with finite mean and `f` bounded, integrable, tending to `0` | `uniform_key_renewal_theorem` (summable `f ≥ 0`, uniformly over `|g| ≤ f`) |
| Theorem 14.5.2 (ii)–(iii), (14.40), p. 355 | Bounded Borel sets; absolutely continuous `Γ₀` | Not formalised (continuous time) |
| (14.41), Proposition 14.5.3, (14.42)–(14.44), p. 356 | Theorem 13.4.4 for the forward recurrence time `δ`-skeleton; `‖Γ₁ ∗ U − Γ₂ ∗ U‖ < ∞` | Not formalised (continuous time). The discrete analogue of (14.42) is Proposition 13.4.1 (`proposition_13_4_1`) |
| Proposition 14.5.4, (14.45)–(14.47), p. 357 | `sup_{|g| ≤ f} |Γ₁ ∗ U ∗ g(t) − Γ₂ ∗ U ∗ g(t)| → 0` for delays of finite mean | Not formalised separately; its discrete form is contained in `uniform_key_renewal_two_delays` |
| p. 357 | `Γ_e` is regular iff `Γ` has a finite second moment | Not formalised (continuous time); compare `summable_mul_equilibriumLaw_iff` |
| Proposition 14.5.5, p. 357 | The same for any two delays | `uniform_key_renewal_two_delays` (discrete form) |
| (14.48)–(14.50), p. 358 | Truncation, and the proof of Theorem 14.5.2 (iii) | Not formalised (continuous time); the discrete forms are proved directly from the renewal theorem and Lemma D.7.1 |

## §§15.1.1–15.1.2 Geometric properties and Kendall's renewal theorem

| Source | Claim | Lean |
| --- | --- | --- |
| (15.8)–(15.12), pp. 364–365 | The regenerative decomposition multiplied by `rⁿ` and summed; `U_α^{(r)}(x, f)` | Not formalised (Chapter 15 Markov chain development) |
| p. 365 | `Σₙ |a_x ∗ u (n) − π(α)| rⁿ ≤ E_x[r^{τ_α}] Σₙ |u(n) − π(α)| rⁿ + (r/(r − 1)) E_x[r^{τ_α}]` | `geometric_delayed_bound` (for a delay law `a`, any `v` and `c ≥ 0`) |
| Theorem 15.1.1, (15.13)–(15.14), p. 366 | For an ergodic renewal sequence, (i) `Σ |u(n) − u(∞)| zⁿ` converges for `|z| < r₀`, `r₀ > 1`; (ii) `U(z)` extends analytically to `|z| < r₀` except for a simple pole at `z = 1`; (iii) `P(z)` converges for `|z| < κ`, `κ > 1`; are equivalent | `theorem_15_1_1` (`List.TFAE`, Mathlib; an aperiodic increment law; (ii) as `U(z) = F(z)/(1 − z)` on the unit disc with `F` analytic on `|z| < r₀` and `F(1) ≠ 0`); `kendall_extension_of_geometric` ((i) ⇒ (ii)), `kendall_geometric_of_extension` ((ii) ⇒ (i)), `kendall_moment_of_geometric` ((i) ⇒ (iii), without aperiodicity), `kendall_geometric_of_moment` ((iii) ⇒ (i)); `kendall_genFunC_sub_pole`; `summable_mean_of_geometric` (each condition forces `m_p < ∞`) |
| (15.15), p. 366 | `F(z) = Σ (u(n) − u(n − 1)) zⁿ = (1 − z) U(z)` | `genFunC_seqDiff`, `oneSubXSeq`, `realConv_oneSubXSeq`, `summable_oneSubXSeq`, `genFunC_oneSubXSeq`, `genFunC_sub`, `abs_seqDiff_realRenewalSeq_le`, `hasSum_seqDiff` |
| p. 367 | Uniqueness of the Taylor expansion and Cauchy's inequality give `Σ |u(n) − u(n − 1)| rⁿ < ∞` | `exists_summable_of_differentiableOn`; `genSeries` (`FormalMultilinearSeries.ofScalars`, Mathlib), `genSeries_sum`, `norm_genSeries`, `le_radius_genSeries`, `one_le_radius_genSeries`, `summable_of_lt_radius_genSeries`, `hasFPowerSeriesOnBall_genFunC`, `differentiableOn_genFunC` |
| p. 367 | By Lemma D.7.2, `Σ |u(∞) − u(n)| rⁿ < ∞` | `summable_abs_sub_of_seqDiff`, and the converse `summable_seqDiff_of_abs_sub` |
| p. 367 | For aperiodic `p`, `P(z) = 1` on the closed unit disc only at `z = 1`, a simple root | `genFunC_incr_ne_one`, `genFunC_renewalTail_ne_zero` (`R(z) = (1 − P(z))/(1 − z)` has no zero on `|z| ≤ 1` when `m_p < ∞`) |
| (8.12), (15.16), p. 367 | `U(z) = (1 − P(z))⁻¹` on the unit disc and `F(z) = (1 − z)(1 − P(z))⁻¹` | `renewal_genFunC`, `one_sub_genFunC_ne_zero`, `renewal_genFunC_mul`, `delayedRenewal_genFunC`; `realConv_renewalTail_seqDiff` (`tail ∗ Δu = δ₀`), `seqDiff_renewalTail`, `one_sub_mul_genFunC_renewalTail`, `summable_deltaSeq` |
| pp. 367–368 | (iii) ⇒ (ii) by the roots of `P(z) = 1` in a larger disc; (ii) ⇒ (iii) by `P(z) = [F(z) − 1 + z]/F(z)` | Replaced by inversion: `geometric_inverse` (if `a ∗ b = δ₀`, `a` is geometrically summable, `b` is bounded and `A(z) ≠ 0` on the closed unit disc, then `b` is geometrically summable), applied to `tail ∗ Δu = δ₀` in both directions |
| p. 368 | A coupling proof of one direction | Not formalised (remark) |
| §15.1.3, p. 368 | Geometrically ergodic atoms, Kendall atoms, `f`-Kendall atoms | Not formalised (Chapter 15) |
| Proposition 15.1.2, p. 369 | For an accessible Kendall atom, `|Pⁿ(α, α) − π(α)| ≤ R r_α⁻ⁿ` | The renewal content: `kendall_geometric_bound` (`|u(n) − m_p⁻¹| ≤ R ρⁿ`, `ρ < 1`, for an aperiodic increment law with a geometric moment). The statement for the atom is not formalised |
| Proposition 15.1.3, Theorems 15.1.4–15.1.5, (15.17)–(15.19), pp. 369–370 | `S_f^κ` is full and absorbing; the geometric ergodic theorem for chains with a Kendall atom | Not formalised (Chapter 15) |
| §15.1.4, (15.20)–(15.21), pp. 370–371 | Forward recurrence time chains, a non-geometrically ergodic chain, different rates of convergence | Not formalised (Chapter 15) |

## Appendix D.7 Some results on sequences and numbers

| Source | Claim | Lean |
| --- | --- | --- |
| p. 563 | The convolution `a ∗ b (n) = Σ_{j ≤ n} a(j) b(n − j)` | `realConv`, `realConv_eq_sum_range`, `realConv_eq_coeff`, `mk_realConv` (the coefficients of a product of power series), `realConv_comm`, `realConv_assoc`, `realConv_nonneg`, `realConv_add_left`, `realConv_add_right`, `realConv_sub_left`, `realConv_sub_right`, `realConv_smul_left`, `realConv_smul_right`, `realConv_one_right`, `realConv_mono_right`, `abs_realConv_le`, `realConv_deltaSeq_left`, `realConv_deltaSeq_right`, `mk_deltaSeq`, `X_dvd_mk_of_zero` |
| Lemma D.7.1, (D.10)–(D.11), p. 564 | For nonnegative `a`, `b` with `b(n) → b(∞) < ∞` and `Σ a < ∞`, `a ∗ b (n) → b(∞) Σ a` | `lemma_D_7_1` (no sign condition on `b`), `tendsto_realConv_of_summable_abs` (`Σ |a| < ∞`, no sign condition on either) |
| Lemma D.7.2 (i), p. 564 | For `c ≥ 0` and `r > 1`, `Σₙ (Σ_{m ≥ n} c(m)) rⁿ ≤ r/(r − 1) Σ c(m) rᵐ`; the two series converge or diverge together | `lemma_D_7_2_i` (with the convergence of the tail series), `lemma_D_7_2_i_converse` (the other direction, for summable `c`), `tailSum_partial_identity`, `tailSum_succ` |
| Lemma D.7.2 (ii), p. 564 | For `a, b ≥ 0` and `r ≥ 0`, `Σ a ∗ b (n) rⁿ = (Σ a(n) rⁿ)(Σ b(n) rⁿ)` | `lemma_D_7_2_ii` (when both series converge), `realConv_mul_pow` |
| Lemma D.7.3, p. 565 | `am + bn = gcd(m, n)` for some integers `a`, `b` | `lemma_D_7_3` |
| Lemma D.7.4, p. 565 | An additively closed `N ⊆ ℤ₊` with g.c.d. `d` contains `nd` for all large `n` | `lemma_D_7_4_gcd` (with a positive element; the g.c.d. by its universal property), `natAddClosed_eventually_mem` (the case `d = 1`), `natAddClosed_succ_mul_mem`, `natAddClosed_mul_mem_zero`, `natAddClosed_add_mem_of_zero`, `natAddClosed_gcd_witness`; the same lemma in the vocabulary of Chapter 5 is `lemma_D_7_4` (carried) |
