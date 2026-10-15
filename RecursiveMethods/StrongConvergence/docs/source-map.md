# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 11, pp. 316–351. Lean names are relative to `StokeyLucasPrescott.StrongConvergence`.
Where the Lean statement departs from the book, see [corrections](corrections.md).

## §11.1 Markov chains

| Source | Claim | Lean |
| --- | --- | --- |
| p. 320 | `Δ`, Markov matrices, `pΠ ∈ Δ` | `simplex`, `Matrix.rowStochastic` (Mathlib), `simplex_vecMul`, `pow_mem_rowStochastic` |
| pp. 321–322 | Ergodic sets, invariant distributions, transient states | `IsClosedSet`, `IsErgodic`, `IsInvariantDist`, `IsTransient` |
| Example 1, pp. 321–322 | `Πⁿ → [1/2 1/2; 1/2 1/2]` | `ex1`, `ex1_pow`, `ex1_pow_234`, `ex1_tendsto`, `ex1_ergodic` |
| Example 2, pp. 322–323 | One transient state | `ex2`, `ex2_pow`, `ex2_tendsto`, `ex2_ergodic` |
| Example 3, pp. 323–324 | Cyclically moving subsets | `ex3`, `ex3_pow_even`, `ex3_pow_odd`, `ex3_even_odd`, `ex3_not_tendsto`, `ex3_cesaro`, `ex3_ergodic` |
| Example 4, p. 324 | Two ergodic sets | `ex4`, `ex4_tendsto`, `ex4_ergodic`, `IsInvariantDist.convex` |
| Example 5, p. 325 | Two absorbing states and a transient state | `ex5`, `ex5_pow`, `ex5_tendsto`, `ex5_ergodic` |
| Theorem 11.1a, p. 326 | `S` = ergodic sets ⊔ transient set | `Cons`, `IsRecurrent`, `consSet`, `exists_ergodic_subset`, `IsErgodic.eq_consSet`, `IsRecurrent.isErgodic`, `isTransient_iff_not_isRecurrent`, `theorem_11_1a` |
| Theorem 11.1b–c, pp. 326–328 | `(1/n) Σ Πᵏ → Q`; rows of `Q` invariant; invariant `r = rQ` | `cesaro`, `limit_mul`, `theorem_11_1b`, `theorem_11_1c` |
| Exercise 11.1, p. 330 | The block form of `Q` | `recSet`, `mass`, `tendsto_tail`, `ex_11_1` |
| Theorem 11.2, pp. 330–331 | Unique ergodic set iff some state is reached from all | `harmonic_const`, `exists_ergodic_reach`, `theorem_11_2` |
| p. 331 | `‖x‖_Δ = Σ \|xⱼ\|` | `l1` |
| Lemma 11.3, p. 332 | `p ↦ pΠ` contracts with modulus `1 − ε` | `epsMin`, `epsSum`, `lemma_11_3`, `l1_pow_le` |
| Theorem 11.4, pp. 332–333 | `ε⁽ᴺ⁾ > 0` iff unique ergodic set without cyclic subsets; geometric convergence | `HasCyclicSubsets`, `cyclic_pow`, `hasCyclicSubsets_of_period`, `eventually_mem_of_add_closed`, `theorem_11_4_rate`, `conv_of_eps`, `eps_of_conv`, `uniqueErgodic_of_eps`, `eps_of_uniqueErgodic`, `theorem_11_4` |
| Examples 6–7, pp. 333–334 | Identity and shift on a countable set | `ex6`, `ex7` |

## §11.2 Convergence concepts for measures

| Source | Claim | Lean |
| --- | --- | --- |
| (1)–(2), p. 335 | Setwise convergence | `ConvSetwise`, `ConvIntegrals`, `convSetwise_of_convIntegrals` |
| Exercise 11.2, p. 335 | (1) implies (2) | `ex_11_2`, `convSetwise_iff` |
| p. 336 | The halving example | `halving`, `halving_not_setwise`, `halving_weak` |
| (3), p. 337 | Weak and strong convergence | `ConvWeak`, `ConvStrong` |

## §11.3 Characterizations of strong convergence

| Source | Claim | Lean |
| --- | --- | --- |
| (1), p. 339 | The total variation norm | `IsPartition`, `partSums`, `tvOf`, `tvNorm`, `tvDist` |
| Exercise 11.3, p. 339 | `Φ(S, 𝒮)` is a vector space and `‖·‖` a norm | `exists_sub_measures`, `tvNorm_sub_eq`, `ex_11_3` |
| Lemma 11.5, pp. 339–340 | `‖λ₁ − λ₂‖ = 2 sup_A \|λ₁(A) − λ₂(A)\|` | `supDiff`, `lemma_11_5` |
| Theorem 11.6, pp. 340–341 | Norm convergence iff uniform setwise convergence | `theorem_11_6` |
| Theorem 11.7, pp. 341–343 | Norm convergence iff strong convergence | `abs_integral_sub_le_tvDist`, `theorem_11_7` |
| Lemma 11.8, pp. 343–344 | `Λ(S, 𝒮)` is complete | `lemma_11_8` |

## §11.4 Sufficient conditions

| Source | Claim | Lean |
| --- | --- | --- |
| Condition D, p. 345 | Doeblin's condition; persistence for `N′ ≥ N` | `DoeblinFor`, `ConditionD`, `doeblinFor_mono` |
| Exercise 11.4a–g, p. 346 | Sufficient conditions for Condition D | `ex_11_4a`, `ex_11_4b`, `ex_11_4c`, `ex_11_4d`, `ex_11_4e`, `ex_11_4f`, `ex_11_4g` |
| Exercise 11.4h–j, p. 346 | Kernels violating Condition D | `not_conditionD_deterministic`, `ex_11_4h`, `ex_11_4i`, `ex_11_4j` |
| pp. 346–347 | Consequent, invariant and ergodic sets; existence and finiteness | `IsConsequentSet`, `IsInvariantSet`, `IsErgodicSetD`, `consequent_real_gt`, `invariant_of_consequent`, `exists_ergodic_subset_of_invariant`, `ergodic_disjoint_or_eq`, `card_mul_lt` |
| Theorem 11.9a, p. 347 | Partition into `1 ≤ M ≤ φ(S)/ε` ergodic sets and a transient set | `theorem_11_9a` |
| Theorem 11.9b–c, p. 348 | Cesàro convergence; invariant measures are convex combinations | Not formalised (not proved in the book) |
| Theorem 11.10a, p. 348 | A unique ergodic set | `theorem_11_10a` |
| Theorem 11.10b–c, p. 348 | A unique invariant measure; Cesàro convergence to it | Not formalised (relies on Theorem 11.9b–c) |
| Condition M, p. 348 | Condition M | `ConditionMFor`, `ConditionM` |
| Exercise 11.5, p. 349 | M in Exercise 11.4c, e; M implies D; D without M | `ex_11_5a_c`, `ex_11_5a_e`, `ex_11_5b`, `ex_11_5c` |
| Lemma 11.11, pp. 349–350 | `T*ᴺ` is a contraction of modulus `1 − ε` | `tvDist_comm`, `tvDist_triangle`, `lemma_11_11` |
| Theorem 11.12, pp. 350–351 | Geometric convergence to a unique `λ*`, and the converse | `tvDist_iterate_le`, `theorem_11_12`, `theorem_11_12_converse` |
