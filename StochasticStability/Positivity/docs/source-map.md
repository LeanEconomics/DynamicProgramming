# Source map

Meyn and Tweedie, *Markov Chains and Stochastic Stability*, 2nd edition (Cambridge University Press,
2009): Chapter 18, pp. 462–481. Equation numbers are the book's. Lean names are relative to
`MeynTweedie.Positivity`; names from Mathlib are marked as such. Names marked "carried" are in the
modules copied from the earlier projects (see the [README](../README.md)). `P_x` is
`pathKernel P x` and `P_μ` is `pathMeasure P μ` (carried). `ψ` is a maximal irreducibility measure
(`IsMaximalIrreducibility P ψ`, carried) and `B⁺(X)` is `{B : ψ(B) > 0}`. Positive and null chains
are `IsPositive P ψ` and `IsNull P ψ` (carried): `ψ`-irreducible with, respectively without, an
invariant probability. Harris and positive Harris chains are `IsHarris P ψ` and
`IsPositiveHarris P ψ`, aperiodicity is `IsAperiodic P ψ`, an invariant measure is
`IsInvariant P π` and a σ-finite one `IsInvariantMeasure P π` (all carried). `‖μ − ν‖` is
`tvNorm μ ν` (carried), `sup_{|f| ≤ 1} |μ(f) − ν(f)|`, which is at most `2`. `U(x, A)` is
`potKernel P x A` and `L(x, A)` is `hitProb P A x` (carried). For an increment law `p`, `a ∗ u` is
`delayedRenewal a p`, `p̄(n) = Σ_{j > n} p(j)` is `renewalTail p` and the convolution of sequences
is `realConv` (carried). On a topological space, reachable states, T-chains, e-chains, weak Feller
chains and non-evanescence are `IsReachable P x₀`, `IsTChain P`, `IsEChain P`, `IsWeakFeller P` and
`IsNonEvanescent P`; boundedness in probability is `IsBoundedInProbability P` and on average
`IsBoundedInProbabilityOnAverage P` (all carried). `P̄ₙ = n⁻¹ Σ_{i=1}^n Pⁱ` is `cesaroKernel P n`
and the limit kernel `Π` of Theorem 12.4.1 is `eChainLimit he` (carried). Weak convergence
`μₖ →w μ` is stated as `∫ f dμₖ → ∫ f dμ` for every bounded continuous `f : X →ᵇ ℝ` (Mathlib).
Every place where the Lean statement departs from the book is listed in
[corrections](corrections.md).

## Chapter 18 introduction

| Source | Claim | Lean |
| --- | --- | --- |
| p. 462 | The aims: limit theorems for chains that are not positive Harris, a version of the Aperiodic Ergodic Theorem for every Harris chain, and the positive/null dichotomy through `Pⁿ` | Not formalised (informal) |
| Theorem 18.0.1, (18.1), p. 462 | For an aperiodic Harris chain and initial laws `λ`, `μ`, `∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ → 0` | `theorem_18_0_1` (first conjunct), from `theorem_18_1_2` |
| Theorem 18.0.1, (18.2), p. 462 | For a null chain with invariant `π`, `sup_A λPⁿ(A)/(π(A) + ε) → 0` for every `ε > 0` | `theorem_18_0_1` (second conjunct, under the theorem's standing hypothesis that the chain is aperiodic and Harris, with `π ≠ 0`), from `theorem_18_1_3`; see corrections |
| p. 462 | Proof: (18.1) is Theorem 18.1.2 and (18.2) is Theorem 18.1.3 | In the proof of `theorem_18_0_1` |
| p. 463 | For an irreducible countable chain, either `lim sup Pⁿ(x, y) > 0` for all `x, y` or `Pⁿ(x, y) → 0` for all `x, y` | `positive_or_null_states`, `theorem_18_2_1_positive`, `theorem_18_2_1_null` |
| (18.3), p. 463 | The positive/null dichotomy is that of `lim sup Pⁿ(x, C)` for petite sets `C` | `theorem_18_2_2_i`, `theorem_18_2_2_ii` (`IsPositiveSet`, `IsNullSet`) |
| p. 463 | For T-chains, positivity is characterised by (18.3) for compact sets and for the neighbourhoods of `x*`; similarly for e-chains | `IsBoundedInProbability.isPositiveHarris`, `proposition_18_3_3`, `proposition_18_4_2` |
| Theorem 18.0.2 (i), (18.4), p. 463 | For a T-chain with a reachable `x*`: (a) positive Harris, (b) bounded in probability, (c) non-evanescent and `x*` positive, are equivalent; then if aperiodic, `‖Pᵏ(x, ·) − π‖ → 0` for every `x` | `theorem_18_0_2_i` (`x*` positive is `IsTopPositive`; (18.4) for every invariant probability) |
| Theorem 18.0.2 (ii), (18.5), pp. 463–464 | For an e-chain with a reachable `x*`: (a) a unique invariant probability `π` with `P̄ₖ(x, f) → π(f)` and the weak LLN for bounded continuous `f`, (b) bounded in probability on average, (c) non-evanescent and `x*` positive, are equivalent; then if `x*` is aperiodic, `Pᵏ(x, ·) →w π` | `theorem_18_0_2_ii`, with (c) in the Cesàro form `IsCesaroPositive`; see corrections |
| p. 464 | Proof: (i) from Theorem 18.3.2 and Proposition 18.3.3; (ii) from Proposition 18.4.2 and Theorem 18.4.4 | In the proofs of `theorem_18_0_2_i` and `theorem_18_0_2_ii`; the weak LLN in (ii) (a) comes from Theorem 18.5.1 (i) (`theorem_18_5_1_i`); see corrections |
| p. 464 | Global convergence from local properties; the LLN for e-chains to come | Not formalised (informal) |

## §18.1 Null recurrent chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 464 | Orey's theorem subsumes part of the ergodic theorem; the method is coupling and the Regenerative Decomposition | Not formalised (informal) |
| p. 464 | Without a finite mean, independent copies of a renewal process need not couple. The simple symmetric random walk on `ℤ²` is recurrent, so its return times to the origin form a proper renewal sequence; two independent copies form a transient random walk on `ℤ⁴`, so their coupling time is infinite with positive probability (Spitzer [369], §8) | `independent_coupling_fails` (`L(u, u) = 1` for the walk on `ℤ²`, `L((u, u), (u, u)) < 1` for the two copies), `ssrw2_isRecurrentState`, `ssrw4_isTransientState`, `matKernel_ssrw4` (the two copies are independent), `matKernel_ssrw4_pow`; proved through the 45° rotation (`rot`, `ssrw2_eq_prodMat`, `matPow_ssrw2`) and `P²ⁿ(0, 0) = C(2n, n)/4ⁿ` on `ℤ` (`matPow_ssrw1_even`, `centralC_sq_le`, `centralC_sq_ge`) |

## §18.1.1 Coupling renewal processes for null chains

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 464–465 | Two sequences of increments with delays `a`, `b`; the second sequence equals the first where `S_j > M` and is an independent draw conditioned on `[0, M]` otherwise, so `S_j` and `S'_j` have the same law | `ornsteinWeight`, `ornsteinLaw p M` (for the lazy law, see p. 467 below), `ornsteinLaw_map_fst`, `ornsteinLaw_map_snd`, `ornsteinLaw_map_swap`, `isProbabilityMeasure_ornsteinLaw` |
| p. 465 | `W_j = S_j − S'_j` are identically distributed, bounded by `M`, symmetric, of mean zero | `diffLaw p M`, `diffLaw_abs_gt`, `diffLaw_map_neg`, `integrable_diffLaw`, `integral_diffLaw` |
| p. 465 | `Φ*ₙ = Σ_{j ≤ n} W_j` is a random walk, and the coupling time `T_ab` is its return time `T*_ab` to `0` | `pairKernel` (the chain of the two sequences of renewal epochs), `pairKernel_map_fst`, `pairKernel_map_snd` (`lazyRenewalKernel`), `pairKernel_map_diff` (the difference is the random walk with increment law `Γ`), `pairDiag`, `coupledBy`; `pathKernel_map_lump`, `pathKernel_lump_apply` |
| p. 465 | A random walk with bounded increments is recurrent if it is `ψ`-irreducible (Proposition 8.4.4), so then `T*_ab < ∞` a.s. | `hitProb_diffWalk_eq_one` (through Theorem 8.1.5, `theorem_8_1_5`, carried), `pairKernel_firstHit_ne_top` |
| p. 465 | The increments may live on a sublattice, so irreducibility needs an argument | Not formalised (remark); the argument is `isIrreducibleChain_diffWalk` below |
| Theorem 18.1.1, (18.6)–(18.7), p. 465 | For proper `a`, `b`, `p` on `ℤ₊` with `p` aperiodic, `|a ∗ u − b ∗ u|(n) → 0` and `|a ∗ u − b ∗ u| ∗ p̄(n) → 0` | `theorem_18_1_1_i` (18.6), `theorem_18_1_1_ii` (18.7); `p` is `IsIncrementLaw p` (`p(0) = 0`) with `IsAperiodicLaw p` |
| p. 466, (18.8) | A level `M` with `g.c.d.{n − m : m < n ≤ M, p(m), p(n) > 0} = 1`; then `Φ*` is irreducible and `P(T_ab < ∞) = 1`, which gives (18.6) | `exists_aperiodic_level` (with the lazy law, the gcd of `{n ≤ M : p(n) > 0}`), `isIrreducibleChain_diffWalk`, `pairKernel_firstHit_ne_top`, `tendsto_pathMeasure_coupledBy_compl`; (18.6) itself is proved through Theorem 13.2.2 (`theorem_13_2_2`, carried); see corrections |
| p. 466 | The backward recurrence (age) chains couple at `T_ab`; decomposition over the value of `T_ab` | `ageEvent` (the age `V⁻(n) = n − k`), `pathKernel_age_fst_eq_snd`, `mem_ageEvent_shift_iff`, `pathMeasure_age_inter_coupledBy`, `sum_age_diff_coupledBy_le` |
| (18.9), p. 466 | `sup_A |P(V⁻_a(n) ∈ A) − P(V⁻_b(n) ∈ A)| ≤ P(T_ab > n)` | `sum_abs_age_sub_le` (`Σ_k |…| ≤ 2 P(T_ab > n)`, the same bound for the sum over points) |
| (18.10), p. 466 | The left side of (18.9) is `½ |a ∗ u − b ∗ u| ∗ p̄(n)` | `pathMeasure_fst_ageEvent`, `pathMeasure_snd_ageEvent` (`P(V⁻(n) = n − k) = (a ∗ u)(k) p̄(n − k)`), `pathKernel_ageEvent` |
| p. 467 | The modified law `p⁰(0) = p > 0`, `p⁰(j) = (1 − p)p(j)` for `j ≥ 1`, which satisfies (18.8) | `lazyLaw` (`p = ½`), `lazyLaw_zero`, `lazyLaw_of_ne`, `isProbabilityMeasure_lazyLaw` |
| (18.11)–(18.12), p. 467 | (18.6)–(18.7) for `p⁰`, and `p̄⁰ = (1 − p)p̄`, `u⁰ = (1 − p)⁻¹u` | Not stated separately: the coupling is run with the lazy law from the start. `lazyLaw_Ioi` is `p̄⁰ = ½ p̄`, and `tsum_lazyRenewalKernel_pow` (`Σⱼ Rʲ(t, {k}) = 2u(k − t)`, through `lazyPot_eq`) is `u⁰ = 2u` |
| p. 467 | Remark: since `Σ p̄(n) = ∞` in the null case, (18.7) does not follow from Lemma D.7.1 | `tendsto_realConv_abs_sub_delayedRenewal_incr`: Lemma D.7.1 (`lemma_D_7_1`, carried) gives the companion with the summable `p` in place of `p̄` |

## §18.1.2 Orey's convergence theorem

| Source | Claim | Lean |
| --- | --- | --- |
| p. 467 | In the null case no limiting distribution exists, since there is no finite invariant measure | `IsNull.measure_univ_eq_top`; otherwise not formalised (informal) |
| Theorem 18.1.2, (18.13), p. 467 | For an aperiodic Harris chain and initial laws `λ`, `μ`, `∫∫ λ(dx) μ(dy) ‖Pⁿ(x, ·) − Pⁿ(y, ·)‖ → 0` | `theorem_18_1_2` (a `[0, ∞]`-valued double integral, no measurability of the integrand needed); `theorem_18_1_2_measures` (`‖λPⁿ − μPⁿ‖ → 0`), `theorem_18_1_2_dirac` (two states) |
| (18.14), p. 467 | At an atom, `‖Pⁿ(x, ·) − Pⁿ(α, ·)‖ ≤ P_x(τ_α ≥ n) + |a_x ∗ u − u|(n) + |a_x ∗ u − u| ∗ p̄(n)` with `p̄(n) = P_α(τ_α > n)` | `tvNorm_comp_pow_succ_sub_atom_le`, for an initial law `λ`, in the form `‖λPⁿ⁺¹ − Pⁿ⁺¹(a, ·)‖ ≤ 2(P_λ(τ_α ≥ n + 1) + |a_λ ∗ u − u| ∗ t₁(n + 1))`, `t₁(m + 1) = p̄(m)` (`realConv_lastExitSeq_one_succ`); from the Regenerative Decomposition (`regenerative_decomposition_47`, carried) |
| p. 467 | The two convolution terms tend to `0` by Theorem 18.1.1 and the first by Harris recurrence | `tendsto_tvNorm_sub_atom` (any atom reached a.s. from `a` and from `λ`, with aperiodic return-time law; no finite mean), through `theorem_18_1_1_ii` |
| p. 468 | From two states by the triangle inequality, and to initial laws by dominated convergence | `theorem_18_1_2_dirac`, `theorem_18_1_2`; `tendsto_lintegral_of_le_const` |
| p. 468 | Strongly aperiodic chains through the split chain; general aperiodic chains by the contraction of the total variation norm | `tvNorm_comp_pow_add_le`, in the proof of `theorem_18_1_2_measures` (`exists_skeleton_minorization`, carried) |
| Theorem 18.1.3, (18.15), p. 468 | For an aperiodic null recurrent chain with invariant `π`, `sup_A λPⁿ(A)/(π(A) + ε) → 0` for every initial law `λ` and `ε > 0` | False as printed: `theorem_18_1_3_counterexample` (`NullNotHarris`). Corrected: `theorem_18_1_3` (aperiodic Harris null chains, `π ≠ 0` invariant, no σ-finiteness); the core is `tendsto_iSup_div_of_measure_univ_eq_top` (a subinvariant `π` with `π(X) = ∞`); see corrections |
| (18.16)–(18.18), p. 468 | Proof by contradiction: (18.17) from (18.13), made uniform on a set of large `π`-measure by Egorov's theorem and `π(X) = ∞` | In the proof of `tendsto_iSup_div_of_measure_univ_eq_top`, with the increasing sets `D_N` on which (18.17) holds from stage `N` on in place of Egorov's theorem; `IsNull.measure_univ_eq_top`, `IsNull.measure_univ_eq_top_of_subinvariant` |
| (18.19), p. 468 | `π(B_k) ≥ π(D)[δ(π(B_k) + ε) − εδ/2]`, so `π(D) ≤ δ⁻¹` | `measure_mul_le_of_forall_le` (the integral step), `jain_arith` (the contradiction) |
| p. 469 | The two theorems: the laws merge, and they move to sets of small `π`-measure | Not formalised (informal) |

## §18.2.1 Countable spaces

| Source | Claim | Lean |
| --- | --- | --- |
| p. 469 | The classical classification of irreducible chains through `Pⁿ` rather than `π` | Not formalised (informal) |
| (18.20)–(18.21), p. 469 | `lim sup Pⁿ(x, y) > 0` implies `E_x(η_y) = U(x, y) = ∞` | `potKernel_eq_top_of_limsup_pos` (for every measurable set) |
| (18.22), p. 469 | Because of cyclic behaviour, `lim inf Pⁿ(x, y)` may be `0` | Not formalised (remark) |
| p. 470 | A state `α` is null if `Pⁿ(α, α) → 0` and positive if `lim sup Pⁿ(α, α) > 0` | `IsNullState`, `IsPositiveState`; `IsNullState.not_isPositiveState` |
| (18.23), p. 470 | For `Pʳ(w, x) > 0` and `Pˢ(y, z) > 0`, `lim sup P^{r+s+n}(w, z) > Pʳ(w, x)[lim sup Pⁿ(x, y)]Pˢ(y, z)` | False as printed (strict): `eq_18_23_counterexample` (the one-point chain). Corrected: `limsup_pow_add_ge` (non-strict, for all `r`, `s`); see corrections |
| p. 470 | For an irreducible chain, all states are positive or all are null | `positive_or_null_states` |
| p. 470 | For a positive recurrent chain, `π(y) = Σ_x π(x)Pⁿ(x, y)` and dominated convergence exclude a null state | In the proof of `theorem_18_2_1` (through `theorem_18_2_1_positive`) |
| Theorem 18.2.1, p. 470 | An irreducible chain on a countable space is positive recurrent iff some state is positive; then `P^{nd+r}(x, y) → dπ(y) > 0` for some `d ≥ 1` and `0 ≤ r(x, y) < d`; and when it is null, `Pⁿ(x, y) → 0` | `theorem_18_2_1`, `theorem_18_2_1_positive` (`d` the period, `π = stationaryDist`, carried), `theorem_18_2_1_null` |
| p. 470 | Proof: transient chains by Proposition 8.1.1; null recurrent chains by Theorem 18.1.3; positive chains by the Aperiodic Ergodic Theorem on the cyclic classes | `theorem_18_2_1_null` through `IsNull.tendsto_pow_of_isPetite` and `isPetite_singleton`, for every period; `theorem_18_2_1_positive` through the convergence on cycle classes (carried); see corrections |
| p. 470 | Why the elementary result waited until the limits through the periodic classes were known | Not formalised (informal) |

## §18.2.2 General spaces

| Source | Claim | Lean |
| --- | --- | --- |
| p. 471 | A set `A` is null if `Pⁿ(x, A) → 0` for all `x ∈ A`, and positive if `lim sup Pⁿ(x, A) > 0` for all `x ∈ A` | `IsNullSet`, `IsPositiveSet`; `IsNullSet.not_isPositiveSet` |
| Theorem 18.2.2 (i), p. 471 | A `ψ`-irreducible chain is positive recurrent iff every `B ∈ B⁺(X)` is positive | `theorem_18_2_2_i`; the positive half is `IsPositive.isPositiveSet` |
| Theorem 18.2.2 (ii), p. 471 | If the chain is null, every petite set is null, and `X` is a countable union of null sets | `theorem_18_2_2_ii`; `IsNull.tendsto_pow_of_isPetite` (`Pⁿ(x, C) → 0` for every `x`, not only `x ∈ C`) |
| p. 471 | Proof of (ii): petite sets of a transient chain are uniformly transient (Theorem 8.3.5); for a null recurrent chain, `π` is finite on petite sets (Proposition 10.1.2) and Theorem 18.1.3 applies | Transient case: `IsUniformlyTransient.tendsto_pow`, `theorem_8_3_5` (carried). Recurrent case, for every period and with no Harris hypothesis: `IsPetite.isUniformlyTransient_inter_compl`, `absorbKernel_isHarris_of_maximalHarris`, `tendsto_pow_of_firstEntrance`, `tendsto_pow_of_isHarris_of_isNull`, `IsCycle.absorbKernel_isHarris_isAperiodic`, `tendsto_of_forall_mul_add`; see corrections |
| p. 471 | Proof of (i): `P^{nd+r}(x, A) → dπ(A ∩ D_r)` on `D₀ ∩ H`, and `L(x, D₀ ∩ H) > 0` | `IsPositive.isPositiveSet`, through the phase averages of Theorem 13.3.4 (ii) (`theorem_13_3_4_ii`, carried) |

## §18.3.1 T-chains bounded in probability

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 471–472 | Bounded in probability chains have finite subinvariant measures (Chapter 12), so positivity is to be expected | Not formalised (informal) |
| p. 472 | On a countable space the continuous component properties always hold | `isTChain_of_discreteTopology` |
| Proposition 18.3.1, (18.24), p. 472 | An irreducible chain on a countable space is positive Harris iff it is bounded in probability | `proposition_18_3_1` (discrete topology); `isPositiveHarris_iff_isPositive_of_countable` |
| p. 472 | A state `x*` is reachable if `U(y, O) > 0` for every `y` and every open `O ∋ x*` | `IsReachable` (carried) |
| Theorem 18.3.2, p. 472 | A T-chain with a reachable state is positive Harris iff it is bounded in probability | `theorem_18_3_2`; `IsBoundedInProbability.isPositiveHarris`, `IsPositiveHarris.isBoundedInProbability` |
| p. 472 | Proof: `ψ`-irreducibility (Proposition 6.2.1); bounded in probability gives non-evanescence (Proposition 12.1.1) and Harris recurrence (Theorem 9.2.2); compact sets are petite and some compact set is not null, so Theorem 18.2.2 applies | `exists_isMaximalIrreducibility_of_isReachable` (`proposition_6_2_1`, carried), `proposition_12_1_1`, `theorem_9_2_2_ii`, `theorem_6_2_5_ii` (carried), `IsNull.tendsto_pow_of_isPetite`, in the proof of `IsBoundedInProbability.isPositiveHarris` |
| (18.25), p. 472 | For a positive Harris chain, `P^{nd+r−j}(x, C) → π_r(C_r) > 1 − ε` on `D_j`, and the chain leaves `N = X \ ⋃ D_j` | `IsPositiveHarris.isBoundedInProbability` (no T-chain property; one compact set for all classes, Fatou's lemma off the classes), `eventually_of_forall_mul_add` |

## §18.3.2 Positive and null states for T-chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 473 | `x*` is null if `Pⁿ(x*, O) → 0` for some neighbourhood `O`, and positive if `lim sup Pⁿ(x*, O) > 0` for all neighbourhoods | `IsTopNull`, `IsTopPositive` (open neighbourhoods) |
| p. 473 | This completes the series begun with Theorem 9.3.3 | Not formalised (informal) |
| Proposition 18.3.3, p. 473 | For a T-chain with a reachable `x*`, the chain is positive recurrent iff `x*` is positive | `proposition_18_3_3`; `isTopNull_iff_isNull` (`x*` is null iff the chain is) |
| p. 473 | Proof: a precompact open neighbourhood of `x*` is petite; a reachable state lies in the support of `π` | `exists_isOpen_isPetite_nhds`, in the proof of `proposition_18_3_3` |

## §18.4.1 Reachability and positivity

| Source | Claim | Lean |
| --- | --- | --- |
| p. 473 | For e-chains a reachable state takes over the role of `ψ`-irreducibility | Not formalised (informal) |
| p. 474 | For a non-evanescent e-chain, a reachable state exists iff `Π(x, X)` does not depend on `x` | One direction: `eChainLimit_eq_of_isReachable` (`Π(y, ·) = Π(x*, ·)`). The converse is formalised under boundedness in probability on average (`theorem_18_4_4_i`); in general it is not formalised |
| Lemma 18.4.1, p. 474 | For a Feller chain with a reachable `x*` and a precompact neighbourhood `O` of `x*`, `{Φ → ∞} = {Φ ∈ O i.o.}ᶜ` a.s. [`P_*`] | `lemma_18_4_1` (weak Feller, `O` open with compact closure, `P_μ`-a.s. for every initial law) |
| p. 474 | Proof: `L(·, O)` is lower semicontinuous (Proposition 6.1.1) and positive, then Theorem 9.1.3 | `IsReachable.hitProb_pos`, `proposition_6_1_1_iii`, `theorem_9_1_3_ae` (carried), in the proof of `lemma_18_4_1` |
| Proposition 18.4.2, p. 474 | For a non-evanescent e-chain with a reachable `x*`: (i) a unique invariant probability `π` with `P̄ₖ(x, ·) →w π`; (ii) bounded in probability on average; (iii) `x*` positive; are equivalent | `proposition_18_4_2` ((i) ⇔ (ii), (ii) ⇔ (iii)) with (iii) in the Cesàro form `IsCesaroPositive`, which implies the book's form (`IsCesaroPositive.isTopPositive`); see corrections |
| pp. 474–475 | Proof: `Π(Φₖ, f)` is a bounded martingale, its limit is `Π(x*, f)` by Lemma 18.4.1, so all `Π(y, ·)` coincide | `harmonic_eq_of_isReachable`, `eChainLimit_eq_of_isReachable`; `IsEChain.isWeakFeller` |
| p. 475 | (iii) ⇒ (i): positivity gives `Π(x*, X) > 0`, then Theorem 12.4.3 | `IsCesaroPositive.eChainMass_pos`, `theorem_12_4_3_i` (carried); see corrections |
| p. 475 | A reachable state lies in the support of `π`, so its neighbourhoods are charged | `IsReachable.measure_pos` |

## §18.4.2 Aperiodicity and convergence

| Source | Claim | Lean |
| --- | --- | --- |
| p. 475 | Limits of `Pⁿ` itself are hard to find for weak Feller chains without the e-chain condition | Not formalised (informal) |
| p. 475 | A recurrent state `x` is aperiodic if `Pᵏ(x, O) > 0` for every open `O ∋ x` and all large `k`, justified by Lemma D.7.4 | `IsTopAperiodic` (recurrence not required); the justification is not formalised |
| Proposition 18.4.3, (18.26), p. 475 | For an e-chain bounded in probability on average with `x*` reachable and aperiodic, and `π = Π(x*, ·)`, `Pᵏ(y, ·) →w π` for every `y ∈ supp π` | `proposition_18_4_3`; the core is `tendsto_pow_cc_of_mem_support` |
| p. 476 | Proof: `∫ |Pᵏf| dπ` decreases; an equicontinuous subsequence converges to a continuous `g` | `IsEChain.equicontinuousAt`, `exists_subseq_tendsto_of_equicontinuousAt`, `integral_comp_kernel_of_bdd` |
| (18.27), p. 476 | `∫ Pˡg dπ = ∫ f dπ` and `∫ |Pˡg| dπ = v` for all `ℓ` | In the proof of `tendsto_pow_cc_of_mem_support` |
| (18.28), p. 476 | `g` cannot change sign on `supp π`: aperiodicity gives one `ℓ` with `Pˡ(y, O₊) > 0` and `Pˡ(y, O₋) > 0` near `x*` | `sign_of_integral_abs_eq`, `exists_pow_pos_of_eChainLimit_pos`, `abs_integral_lt_integral_abs`, `setLIntegral_pos_of_pos` |
| p. 476 | So `g ≡ 0` on `supp π` when `∫ f dπ = 0`, and (18.26) holds | `tendsto_pow_cc_of_mem_support` (run for `Pᵏf − π(f)`, every `f ∈ C_c(X)`), `proposition_18_4_3`; see corrections |
| Theorem 18.4.4 (i), p. 476 | An e-chain bounded in probability on average has a unique invariant probability iff it has a reachable state | `theorem_18_4_4_i` |
| Theorem 18.4.4 (ii), (18.29), p. 477 | With an aperiodic reachable state, `Pᵏ(x, ·) →w π` for every `x`; conversely, if this holds for all `x`, every state of `supp π` is reachable and aperiodic | `theorem_18_4_4_ii`, `theorem_18_4_4_ii_converse` (also topologically recurrent, `IsTopRecurrent`, carried) |
| p. 477 | Proof: the open set `O_ε ⊇ supp π`, `P̄_N(x, O_ε) → 1`, and Fatou's lemma | In the proof of `theorem_18_4_4_ii` |

## §18.5 The LLN for e-chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 477 | A sample-path version of Proposition 18.4.2 | Not formalised (informal) |
| (18.30), p. 477 | The occupation probabilities `μ̃ₙ{A} = n⁻¹ Σ_{k=1}^n 1{Φₖ ∈ A}`, probability-valued random variables | `occMeasure ω N`, `isProbabilityMeasure_occMeasure`, `integral_occMeasure`; `integral_occAvg` (`E_x[μ̃_N(g)] = P̄_N(x, g)`) |
| pp. 477–478 | Theorem 17.1.2 gives convergence from `π`-almost every state; the laws below remove the null set for continuous bounded functions | Not formalised (remark; Chapter 17 is not carried) |
| Theorem 18.5.1 (i), p. 478 | For an e-chain bounded in probability on average with a reachable state, a unique invariant probability `π` exists, and `∫ f dμ̃ₖ → ∫ f dπ` in probability from every initial state, for `f ∈ C(X)` | `theorem_18_5_1_i` (bounded continuous `f`, in `P_x`-probability for every `x`); the core is `tendsto_occAvg_inProb` |
| Theorem 18.5.1 (ii), (18.31), p. 478 | If from every initial state the occupation probabilities are a.s. tight, then `μ̃ₖ →w π` a.s. [`P_*`] | `theorem_18_5_1_ii` (tightness in an eventual form; see corrections); the pathwise core is `tendsto_occAvg_of_tight` |
| (18.32), p. 478 | `P̄_k f → ∫ f dπ` uniformly on compacts, so `|N⁻¹ Σ P̄_M f(Φₖ) − ∫ f dπ| ≤ ε + N⁻¹ Σ 1{Φᵢ ∈ Cᶜ}` | `eventually_forall_abs_cesaroIter_sub_le` (for `f ∈ C_c(X)`), used in (ii); (i) is proved without (18.32); see corrections |
| (18.33), p. 478 | The averages of `f` and of `P̄_M f` along the path differ by an a.s. vanishing term | `abs_occAvg_sub_le`, `tendsto_mdRemainder` |
| p. 478 | The telescoping identity through the differences `Pⁱf(Φ_{k−i}) − P^{i+1}f(Φ_{k−i−1})` | `sum_sub_sum_kfunR_eq`, `sum_sub_sum_iterFun_eq`, `abs_sum_sub_sum_iterFun_le`; `iterFun`, `mdTerm`, `mdSum` |
| (18.34), p. 479 | `|N⁻¹ Σ f(Φₖ) − ∫ f dπ|` is bounded by the martingale terms, `|N⁻¹ Σ P̄_M f(Φₖ) − ∫ f dπ|` and `2M/N` | `abs_sum_sub_sum_cesaroIter_le`, `cesaroIter_eq_cesaroFun` (`cesaroIter P f M = P̄_M f`) |
| p. 479 | Bounded martingale differences obey the strong law (Theorem 5.2 of Chapter 4 of Doob [99]) | Proved here: `ae_tendsto_mdSum_div` (Chebyshev along the squares and Borel–Cantelli), with `integral_mul_mdTerm`, `integral_mdSum_sq_le`, `measure_abs_mdSum_ge_le`, `tendsto_measure_abs_mdSum_div` |
| p. 479 | Proof of (i): Markov's inequality and boundedness in probability on average | `tendsto_occAvg_inProb` (through `integral_occAvg`, `continuous_cesaroIter`, `tendsto_measureReal_of_ae_tendsto`); see corrections |
| pp. 479–480 | Proof of (ii): the strong law along a tight path, a dense sequence in `C_c(X)` (Proposition D.5.1), vague and then weak convergence | `tendsto_occAvg_of_tight`, `tendsto_occAvg_cc_of_dense`, `exists_dense_cc` (carried), `tendsto_occAvg_bcf_of_cc` |
| Theorem 18.5.2, (18.35), p. 480 | If a coercive `V` and a compact `C` satisfy (V4), the chain is bounded in probability and the occupation probabilities are a.s. tight from every initial state; so for an e-chain with a reachable state, `μ̃ₖ →w π` a.s. [`P_*`] | `theorem_18_5_2` (any measurable `C`; `V : X → ℝ≥0` measurable and coercive, `IsCoercive`, carried; (V4) is `DriftV4 P V ρ b C`, carried, with `ρ < 1`, `b < ∞`), `theorem_18_5_2_bounded`; see corrections |
| p. 480 | "For a proof see [259]" | Proved here: `kfunR_sqrt_le_of_drift`, `integral_coord_le_of_drift`, `ae_tendsto_mdSum_sqrt_div`, `ae_tendsto_mdSum_div_of_sq`, `tight_of_tendsto_mdSum_sqrt`, `tight_of_eventually_tight` |

## §18.6 Commentary

| Source | Claim | Lean |
| --- | --- | --- |
| p. 480 | History: Orey, Jamison and Orey, Ornstein, Berbee, Nummelin, Jain, Meyn, Tuominen and Tweedie, Feller, Jamison | Not formalised (commentary) |
| p. 480 | Analogues of Theorem 18.3.2 and Proposition 18.3.3 for chains that are not irreducible [277] | Not formalised (commentary) |
| pp. 480–481 | Without a reachable state: the classes `E_x = {y : Π(y, ·) = Π(x, ·)}` are closed, their complement is transient, and Theorem 18.4.4 extends [281] | Not formalised (commentary) |
| (18.36), p. 481 | The random limit `π̃{A} = lim Π(Φₖ, A)`, and Theorem 18.5.1 with `π̃` in place of `π` when no reachable state exists | Not formalised (commentary) |
