# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 12, pp. 352–388. Lean names are relative to `StokeyLucasPrescott.WeakConvergence`.
Where the Lean statement departs from the book, see [corrections](corrections.md).

## §12.1 Characterizations of weak convergence

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 12.1, p. 354 | Relatively open and closed subsets of a Borel `S ⊆ ℝˡ` | `ex_12_1` |
| p. 354 | `λₙ ⇒ λ` | `ConvWeak` |
| Exercise 12.2, p. 355 | `ρ(s, A)` is continuous; `ρ(s, A) = 0` iff `s ∈ Ā` | `ex_12_2` |
| Lemma 12.1, pp. 355–356 | Closed sets are decreasing limits of continuous `fₙ` | `bump`, `continuous_bump`, `bump_mem`, `bump_eq_one`, `bump_antitone`, `tendsto_bump`, `lemma_12_1` |
| Lemma 12.2, pp. 356–358 | Integrals approximated by sums of measures of closed sets | `count_bounds`, `lemma_12_2` |
| Theorem 12.3, pp. 358–360 | Weak convergence ⇔ `limsup λₙ(F) ≤ λ(F)` ⇔ `liminf λₙ(G) ≥ λ(G)` ⇔ `λₙ(A) → λ(A)` on `λ`-continuity sets | `LimsupLe`, `LiminfGe`, `tendsto_of_limsup_liminf`, `limsup_closed_of_weak`, `limsup_integral_of_closed`, `weak_of_limsup_closed`, `liminf_open_of_limsup_closed`, `limsup_closed_of_liminf_open`, `tendsto_of_null_frontier`, `limsup_closed_of_null_frontier`, `theorem_12_3` |
| Theorem 12.4, pp. 360–361 | A π-system covering open sets by countable unions is convergence-determining | `tendsto_finite_union`, `theorem_12_4` |
| Theorem 12.5, pp. 361–362 | Small neighbourhoods in a π-system | `theorem_12_5` |
| Corollary, p. 362 | Finite intersections of balls with null boundary | `ballInters`, `frontier_iInter_fin_subset`, `theorem_12_5_cor` |
| p. 362 | Convergence-determining classes; they determine measures | `IsConvDetermining`, `IsConvDetermining.eq` |
| Theorem 12.6, pp. 363–364 | Agreement on a class approximating closed sets | `theorem_12_6` |
| Corollaries 1–2, p. 364 | Agreement on closed sets, or on integrals of `C(S)` | `theorem_12_6_cor1`, `theorem_12_6_cor2`, `convWeak_unique` |

## §12.2 Distribution functions

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 364–365 | `F(x) = λ((−∞, x])`; continuity from above and below | `distFun`, `box`, `vertex`, `vertexSum`, `diag`, `ContFromAbove`, `ContFromBelow` |
| Exercise 12.3, p. 365 | Continuous from above and below implies continuous | `ex_12_3` |
| Theorem 12.7a, pp. 365–366 | (D1)–(D3) | `Iic_eq_pi`, `box_indicator_eq`, `measurableSet_box`, `vertexSum_eq`, `distFun_mono`, `contFromAbove_distFun`, `theorem_12_7a` |
| Theorem 12.7b, uniqueness, pp. 366–369 | `F` determines `λ` | `generateFrom_Iic_pi`, `distFun_injective` |
| Theorem 12.7b, existence, pp. 366–369 | Every `F` satisfying (D1)–(D3) is a distribution function | `vertexSum_eq_erase`, `vertexSum_split`, `boxContent`, `boxes`, `isSetSemiring_boxes`, `boxFun`, `stieltjesContent`, `stieltjesContent_box`, `tendsto_shift`, `tendsto_vertexSum_upper`, `tendsto_vertexSum_lower`, `exists_open_cover`, `exists_compact_inner`, `isSigmaSubadditive`, `Iic_eq_iUnion_box`, `borel_eq_generateFrom_boxes`, `tendsto_vertexSum_Iic`, `theorem_12_7b` |
| Theorem 12.7c, p. 369 | Continuity from below at `x` iff `λ(∂(−∞, x]) = 0` | `lowerOpen`, `frontier_Iic_eq`, `lowerOpen_subset`, `tendsto_distFun_below`, `theorem_12_7c` |

## §12.3 Weak convergence of distribution functions

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 12.8, pp. 369–370 | `λₙ ⇒ λ` iff `Fₙ(x) → F(x)` at continuity points of `F` | `nullCoord`, `countable_nullCoord_compl`, `dense_nullCoord`, `continuousAt_distFun`, `frontier_null_of_continuousAt`, `box_inter`, `box_eq_empty`, `theorem_12_8` |
| Exercise 12.4, p. 371 | Weak convergence on `S` iff of the extensions to `ℝˡ` | `ex_12_4` |
| Exercise 12.5a, p. 371 | Convergence on the sets `[a, x]` suffices on `[a, b]` | `ex_12_5a` |
| Exercise 12.5b, p. 371 | Integrals of continuous nondecreasing functions determine `λ` | `ramp`, `continuous_ramp`, `ramp_mem`, `monotone_ramp`, `tendsto_ramp`, `ex_12_5b` |
| pp. 371–372 | The support | `IsSupport`, `support_inter`, `exists_support` |
| Theorem 12.9, pp. 372–373 | Helly's theorem | `concentrated_iff`, `theorem_12_9`; counterexamples `distFun_dirac`, `not_convWeak_escape`, `theorem_12_9_false_hyp`, `theorem_12_9_false_concl` |
| Corollary 1, p. 374 | Helly, measure form | `exists_convWeak_subseq_of_tight`, `measure_eq_one_of_convWeak`, `theorem_12_9_cor1` |
| Exercise 12.6, p. 374 | (a) a weaker condition; (b) tightness on `ℝˡ`; (c) on `S ⊆ ℝˡ` | `ex_12_6a`, `ex_12_6a_false`, `ex_12_6b`, `ex_12_6c` |
| Corollary 2, p. 375 | Monotone sequences converge | `theorem_12_9_cor2` |

## §12.4 Monotone Markov processes

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 375–376 | The Feller property | `IsFeller`, `bcf_abs_le_norm`, `convWeak_dirac`, `adjointOp_dirac`, `integral_markovOpR`, `fellerBCF`, `fellerBCF_apply` |
| Exercise 12.7, p. 376 | Three equivalent forms of the Feller property | `ex_12_7` |
| Exercise 12.8, p. 376 | `sₜ₊₁ = 1 − sₜ` | `flipKernel`, `isMarkovKernel_flipKernel`, `adjointOp_flip`, `adjointOp_flip_dirac`, `iterate_flip_dirac`, `symm_ne_self`, `ex_12_8a`, `ex_12_8b`, `ex_12_8c` |
| Theorem 12.10, pp. 376–378 | Compact `S` and Feller give an invariant measure | `isProbabilityMeasure_iterate`, `invariant_of_convWeak`, `theorem_12_10` |
| p. 378 | Monotone transition functions; dominance | `IsMonotoneTF`, `Dominates`, `Dominates.trans`, `Dominates.real_le` |
| Exercise 12.9, p. 379 | (a) dominance orders `F`; (b) the converse on `ℝ`; (c) not on `ℝ²` | `ex_12_9a`, `ex_12_9a_subtype`, `measure_lower_le`, `ex_12_9b`, `real_half_dirac`, `ex_12_9c` |
| Exercise 12.10, p. 379 | Squeezing between dominance-ordered sequences | `distFun_map_val`, `ex_12_10` |
| Exercise 12.11, p. 379 | Monotone `P` ⇔ `T*` preserves dominance ⇔ `P(s, ·)` increasing in `s` | `ex_12_11`, `markovOpR_kpow_zero`, `markovOpR_kpow_add`, `isMonotoneTF_kpow`, `iterate_dirac`, `dominates_iterate` |
| pp. 379–380 | Monotone sequences of measures converge | `IccBot`, `IccTop`, `IccBot_le`, `le_IccTop`, `dominates_dirac_bot_top`, `exists_subtype_measure`, `map_val_Icc`, `convWeak_of_dominance_mono` |
| Exercise 12.12, p. 380 | `T*ⁿδ_a` increases, `T*ⁿδ_b` decreases, both to invariant measures | `ex_12_12` |
| Exercise 12.13, pp. 380–381 | Monotone and Feller with two ergodic sets | `clamp01`, `lowEnd`, `highEnd`, `bandPt`, `unif`, `bandKernel`, `bandKernel_apply`, `isMarkovKernel_bandKernel`, `ex_12_13a`, `kpow_eq_one_of_invariant`, `bandKernel_leave`, `ex_12_13b`, `ex_12_13c` |
| Assumption 12.1, p. 381 | The mixing condition | `Assumption12_1` |
| Exercise 12.14, p. 381 | Assumption 12.1 holds from every starting point | `ex_12_14` |
| Lemma 12.11, p. 382 | `εf(c) + (1 − ε)f(a) ≤ Tᴺf ≤ εf(c) + (1 − ε)f(b)` | `lemma_12_11` |
| Theorem 12.12, pp. 382–383 | Unique, globally stable invariant measure | `theorem_12_12` |

## §12.5 Dependence on a parameter

| Source | Claim | Lean |
| --- | --- | --- |
| Theorem 12.13, pp. 384–385 | `θ ↦ μ_θ` is weakly continuous | `tendsto_uniform_markovOp`, `theorem_12_13` |

## §12.6 A loose end

| Source | Claim | Lean |
| --- | --- | --- |
| Lemma 12.14, pp. 386–388 | `T` preserves boundedness and continuity; monotonicity and concavity in `y` | `tendsto_integral_abs_sub`, `lemma_12_14_cont`, `lemma_12_14_mono`, `integral_lt_integral_of_lt`, `lemma_12_14_strictMono`, `lemma_12_14_concave`, `lemma_12_14_strictConcave` |
