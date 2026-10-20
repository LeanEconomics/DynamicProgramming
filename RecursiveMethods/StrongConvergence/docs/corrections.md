# Corrections and conventions

Places where a Lean statement differs from the book: a claim corrected, a gap in a proof closed,
a hypothesis made explicit, or a convention chosen.

## Definitions corrected

| Where | Book | Lean |
| --- | --- | --- |
| Ergodic set, p. 321 | `E` is ergodic if `P(s, E) = 1` for `s ∈ E` and no proper subset has this property. | `∅` satisfies this vacuously. Ergodic sets are required to be nonempty, and minimality is among nonempty closed subsets (`IsErgodic`). |
| Invariant set, p. 346 | `E` is invariant if it is a consequent set of every `s ∈ E`. | `∅` is then invariant, and every nonempty set has an invariant subset (`∅`) of smaller measure, so no set would be ergodic. Invariant sets are required to be nonempty (`IsInvariantSet`). |

## Gaps in proofs closed

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 11.4, pp. 332–333 | "A unique ergodic set with no cyclically moving subsets iff `ε⁽ᴺ⁾ > 0` for some `N`." The converse proof assumes `p₀Πⁿ → p*` for all `p₀` instead of the stated hypothesis, and cyclically moving subsets are never defined. | `HasCyclicSubsets` defines them, following Example 3. Three conditions are proved equivalent (`theorem_11_4`): `ε⁽ᴺ⁾ > 0`; a unique ergodic set without cyclically moving subsets; and convergence of `p₀Πⁿ` to a common limit. From the second to the first: if the return times of a state have greatest common divisor `d ≥ 2`, the residues mod `d` split its ergodic set into cyclically moving subsets (`hasCyclicSubsets_of_period`). Otherwise the return times contain every large integer (`eventually_mem_of_add_closed`, via the Chicken McNugget theorem), and some column of `Πᴺ` is positive. |
| Existence of an ergodic set, p. 347 | A strictly decreasing sequence `E′ ⊃ E₁ ⊃ ⋯` of sets with smaller and smaller measure; "if the sequence is infinite, `∩ Eₙ` is an ergodic set". | The intersection is invariant but need not be minimal. Corrected argument (`exists_ergodic_subset_of_invariant`): choose `G₁` invariant with `φ(G₁)` within `ε/2` of the infimum `m` of `φ` over invariant subsets. Two invariant subsets of `G₁` must meet, since disjoint ones would give `2m ≤ φ(G₁) < m + ε/2` with `m ≥ ε`. So the intersections of a minimizing sequence stay invariant, and their intersection attains `m`. |
| Lemma 11.8, p. 344 | `lim_n Σᵢ λₙ(Aᵢ) = Σᵢ lim_n λₙ(Aᵢ)`, without justification. | The exchange holds because `λₙ(A) → λ(A)` uniformly in `A`. The tails `λ(⋃_{i≥K} Aᵢ)` are within `ε` of `λₙ(⋃_{i≥K} Aᵢ)`, which tend to `0` as `K → ∞` (`lemma_11_8`). |
| Lemma 11.11, pp. 349–350 | Applies Lemma 11.5 to `T*ᴺα₁`, `T*ᴺα₂`, which are not probability measures. | Lemma 11.5 is proved for finite measures of equal mass (`lemma_11_5`). The proof of Lemma 11.11 bounds `\|(T*ᴺλ₁)(A) − (T*ᴺλ₂)(A)\|` directly (`lemma_11_11`). |
| Theorem 11.12, pp. 350–351 | (1) is stated along `n = Nk`, and the proof shows only that `λ*` is a fixed point of `T*ᴺ`. | `λ*` is also invariant under `T*` (`T*λ*` is a fixed point of the contraction `T*ᴺ`), and `‖T*ⁿλ₀ − λ*‖ ≤ 2(1 − ε)^⌊n/N⌋` for every `n` (`theorem_11_12`). |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 11.1, p. 326 | `S = {s₁, …, s_l}`. | `S` nonempty. The book's proof of Step 1 is an induction along transient states; here a state whose consequents are fewest is used. |
| Theorem 11.9a, pp. 346–347 | "`S` can be partitioned into a transient set and `M` ergodic sets." | Ergodic sets are determined only up to `φ`-null sets. `theorem_11_9a` gives `M` pairwise disjoint ergodic sets, `1 ≤ M` and `Mε < φ(S)`, such that every ergodic set agrees with one of them up to a `φ`-null set; the transient set is the complement of their union. |
| Theorem 11.10, p. 348 | "`S` has only one ergodic set." | Any two ergodic sets agree up to `φ`-null sets (`theorem_11_10a`). |
| Exercise 11.4b, p. 346 | "`Σⱼ pᵢⱼ` converges uniformly in `i`." | The tails `Σ_{j≥J} pᵢⱼ` tend to `0` uniformly in `i`. |
| Exercise 11.4g, p. 346 | `P = αP₁ + (1 − α)P₂` satisfies Condition D. | With constants `(φ, N, αᴺε)`, using `Pⁿ ≥ αⁿP₁ⁿ` (`ex_11_4g`). |
| Theorem 11.12 converse, p. 351 | "If (1) holds, then Condition M is satisfied." | (1) with `0 < ε ≤ 1` gives Condition M for `(NK, 1/4)` (`theorem_11_12_converse`). |
| Theorem 11.9b–c, pp. 347–348 | Stated without proof (the book refers to Doob 1953, §V.5, and Neveu 1965, §V.3). | Proved for nonempty `S` (`theorem_11_9b`, `theorem_11_9c`). The limit is in the total variation norm, and the averages run over `n = 1, …, N` with `N = n + 1` (`cesaroM κ n`). In (c), the `M` invariant measures `πₘ` satisfy `πₘ(Eₘ) = 1` for the `M` ergodic sets of Theorem 11.9a. Every invariant `μ` equals `Σₘ μ(Eₘ) πₘ`, with `Σₘ μ(Eₘ) = 1`. |
| Theorem 11.10b–c, p. 348 | "Parts (b) and (c) then follow immediately from Theorem 11.9." | Under the reachability hypothesis the decomposition of Theorem 11.9a has exactly one ergodic set (`ergodic_count_eq_one`), so (b) and (c) follow from Theorem 11.9b–c (`theorem_11_10b`, `theorem_11_10c`). |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Exercise 11.1, p. 330 | The transient block is `w_j Q_j`. | Read as the outer product of the column `w_j` and the common row `q_j` of `Q_j`: `Qᵢⱼ = Σ_E w_E(i) q_E(j)` (`ex_11_1`). `w_E(i) = lim Πⁿ(i, E)`. |
| Halving example, p. 336 | `S = [0, 1]`. | `S = ℝ`. The unit masses lie in `[0, 1]`, and it is shown that no finite measure is a setwise limit (`halving_not_setwise`). Exercise 11.4j uses `S = [0, 1]`. |
| Exercises 11.4h–j | Three separate kernels. | One lemma covers all three: an injective deterministic map on a space with infinitely many points violates Condition D (`not_conditionD_deterministic`). |
| `P`, `T*` | Transition function, adjoint operator. | Markov kernels, `kpow κ n` and `adjointOp`, carried from `RecursiveMethods/MarkovProcesses`. |
