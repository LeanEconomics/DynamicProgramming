# Corrections and conventions

Places where a Lean statement differs from Miao's Chapter 3 (draft of 21 April 2013):
a false claim corrected (with a Lean counterexample), a gap closed, a hypothesis made explicit, or
a convention chosen.

## False as printed

| Where | Book | Lean |
| --- | --- | --- |
| Remark 3.1.1, p. 92 | An ergodic set: a set `E` with `p_{ij} = 0` for `i ∈ E`, `j ∉ E`, no proper subset with the same property. | Taken literally `∅` is the only ergodic set (`remark_3_1_1_literal`). With `E` nonempty and minimality over nonempty subsets, ergodic sets are the recurrent classes (`mc_IsErgodicSet`, `ex_3_1`). |
| Theorem 3.1.1(b), proof, p. 91 | All transient states form one class. | False: `0 → 1 → 2 → 2` (`theorem_3_1_1b_proof_counterexample`). The theorem holds; a state with the smallest accessible set is recurrent. |
| Theorem 3.1.3, p. 94 | `p^k_{ij} > 0` for some `k`. | One `k` must work for all pairs: with `k` depending on `(i, j)` the two-state swap is a counterexample (`theorem_3_1_3_counterexample`). The state space is nonempty. |
| pp. 96–97 | Example 3.1.2 has no stationary distribution. | It has one (`example_3_1_2_stationary`); what fails is convergence of `Pᵗ` (`example_3_1_2_not_tendsto`). |
| p. 98 | Theorem 3.1.1(b) is still true for countable chains. | False: the shift `i ↦ i + 1` has no recurrent state (`theorem_3_1_1b_countable_counterexample`). |
| p. 99 | Theorem 3.1.4 also applies to countable chains. | Not with one `k₀` for all pairs: a birth–death chain is a counterexample (`theorem_3_1_4_countable_counterexample`); the pairwise form holds (`theorem_3_1_4_countable`). |
| Proposition 3.3.1, p. 107 | Minorization ⇔ Condition M; proof of ⇐: "define `μ = δ_A` … `α = ε`". | `δ_A` is meaningless, and ⇐ fails with the same `N`: on `Fin 3`, `P(i, ·) = ½(δ_{i+1} + δ_{i+2})` satisfies Condition M for `(1, 1/2)` but no minorization for `N = 1` (`proposition_3_3_1_counterexample`). Proved: ⇒ as in the book with `ε = α/2` (`proposition_3_3_1_forward`); ⇐ for some larger `N` when the invariant `π` of Theorem 3.3.1 has an atom (`proposition_3_3_1_of_atom`), hence on every nonempty countable space (`proposition_3_3_1`). On `X = ∅`, Condition M holds vacuously and minorization fails. The general case (countably generated σ-algebras, Meyn–Tweedie Thm 16.0.2) is not formalised. |
| Theorem 3.3.2 (Prohorov), p. 109 | "There exist `μ` and a subsequence `μₙₖ ⇒ μ` iff `{μₙ}` is tight." | "Only if" is false: on `ℝ`, `δ₀, δ₁, δ₀, δ₃, …` has a convergent subsequence and is not tight (`theorem_3_3_2_counterexample`). Proved: on a complete separable metric space, tight ⇔ every `μ ∘ ψ` has a weakly convergent subsequence (`theorem_3_3_2`). |
| Theorem 3.3.4, p. 112 | "Every invariant measure is a convex combination of ergodic measures." | False for finite convex combinations: for `P(x, ·) = δₓ` on `ℝ`, the uniform law on `[0, 1]` is invariant but not a finite combination of ergodic measures (`theorem_3_3_4_combination_counterexample`). The true statement (ergodic decomposition, an integral mixture) is not formalised. |
| Definition 3.3.5, p. 111 | `E` is an ergodic set if `P(x, E) = 1` for `π`-a.e. `x ∈ E` and no proper subset has this property. | `∅` has the property and is a proper subset of every nonempty set, so the only ergodic set is `∅` (`definition_3_3_5_ergodicSet_eq_empty`). Not used elsewhere. |
| Theorem 3.2.2 (Kolmogorov), p. 100 | For any measurable space `(X, 𝒳)`. | False for general measurable spaces (Andersen–Jessen; not formalised). Proved for standard Borel `X` (`theorem_3_2_2`), by disintegration and Ionescu Tulcea; Mathlib has no general Kolmogorov extension theorem. |

## Gaps closed and hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 3.3.1, p. 106 | Under Condition M, a unique `π` with (3.8). | `X` nonempty. Also proved: `π` is invariant and `dTV(T*ⁿλ₀, π) ≤ (1 − ε)^⌊n/N⌋` (`theorem_3_3_1_invariant`). Converse needs `0 < ε ≤ 1`, gives Condition M for `(NK, 1/4)` (`theorem_3_3_1_converse`). From SLP Theorem 11.12, with SLP's norm `‖·‖ = 2 dTV`. |
| Theorem 3.2.3, p. 101 | `Pr(Xₜ₊₁ ∈ A ∣ Xₜ = x) = P(x, A)`. | Conditioning on the null event `{Xₜ = x}` is read as: `law(X₀…Xₜ, Xₜ₊₁) = law(X₀…Xₜ) ⊗ P(Xₜ, ·)` (`theorem_3_2_3`), hence `Pr(Xₜ ∈ A, Xₜ₊₁ ∈ B) = ∫_A P(x, B) Pr(Xₜ ∈ dx)` (`theorem_3_2_3_transition`). Uniqueness is with respect to this Markov property and `X₀ ~ μ₀`. `Xₜ ~ T*ᵗμ₀` (`theorem_3_2_3_marginal`). |
| Theorem 3.3.3 (Krylov–Bogolubov), p. 110 | Complete separable metric `X`. | Completeness not needed. Tightness of `{Pⁿ(x, ·)}_{n ≥ 1}`. |
| Corollary 3.3.1, p. 111 | Compact complete separable metric `X`. | Nonempty compact metric `X`. |
| Theorem 3.3.4, p. 112 | Stated without proof (refers to Birkhoff, Ch. 4). | Proved directly, no Birkhoff: `I` convex, `E = ext I`, distinct ergodic measures mutually singular (`theorem_3_3_4_convex`, `theorem_3_3_4_extreme`, `theorem_3_3_4_singular`). |
| Theorem 3.3.6, p. 113 | `X ⊆ ℝˡ` compact, `Θ ⊆ ℝᵐ`. | Any compact metric `X`, metric `Θ` (`theorem_3_3_6`); book setting `theorem_3_3_6_euclidean`. |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Definition 3.0.1, p. 85 | Conditional probabilities. | For countable state spaces, written cross-multiplied (equivalent when the conditioning events have positive probability). `E[τ]` is `Σ (n + 1) f^{(n+1)}`, the mean when `τ < ∞` a.s., which is when Definition 3.1.6 uses it. |
| Definition 3.1.4, p. 92 | The period applies to recurrent states only. | It applies to any state with a return (e.g. the transient state of Example 3.1.3); `mc_period` is `0` for states with none. |
| Example 3.1.3, p. 88 | The formula for `Pᵐ`. | For `m ≥ 1` (stated for `m + 1`). |
| Theorem 3.1.5(b)–(c), p. 98; Examples 3.1.4–3.1.5 | Limits of `p^k_{ij}` for countable chains; recurrence at `p = 1/2`. | Not formalised: they need the renewal theorem or coupling. Everything else in Theorem 3.1.5 is proved; for finite chains the limits are Theorems 3.1.3–3.1.4. |
| Def 3.2.1 | `P : X × 𝒴 → [0, 1]`. | `ℝ≥0∞`-valued; equivalent to Mathlib's `IsMarkovKernel` (`definition_3_2_1`). |
| (3.4) | `Pⁿ(a, A) = ∫ P(x, A) Pⁿ⁻¹(a, dx)`. | `kpow P n` (SLP's recursion `Pⁿ⁺¹ = Pⁿ ∘ P`); `eq_3_4`, `eq_3_4_unique` show it is the book's `Pⁿ`. |
| (3.6), Ex 5 | `dTV = sup_A |λ₁(A) − λ₂(A)|`. | Same normalisation; (3.7), Ex 5(a), 5(b) hold as printed (`eq_3_7`, `ex_3_5a`, `ex_3_5b`). SLP's `tvDist` is `2 dTV` (`gp_tvDist_eq_two_mul_dTV`): no factor-of-2 error in the book. |
| Theorem 3.2.2, 3.2.4 | `Xᵗ`, `Ω₀ × ⋯ × Ωₙ`. | Indexed by `Finset.Iic n = {0, …, n}`; (3.2) as a rectangle condition, equivalent to the projection identity (`eq_3_2_iff`). |
| Theorem 3.3.5 | `[a, b] ⊂ ℝˡ`, increasing. | Subtype `Set.Icc a b` of `Fin l → ℝ`, componentwise order, nondecreasing measurable `f`. |
| Example 3.3.3 | finite irreducible aperiodic chain gives (3.9) "by Theorem 3.1.4". | Stated for a power `Pᴺ` with positive entries (`example_3_3_3_finite`); Theorem 3.1.4 is in the `Chain` modules. |

## Typographical errors

- p. 99: "Definition 3.1.5" for the period should be Definition 3.1.4.

| Where | Book | Correct |
| --- | --- | --- |
| Theorem 3.2.4, p. 102 | `Qₙ : (Ω₀ × ⋯ × Ωₙ) × 𝓕ₙ₊₁ → [0, 1]`, `n ≥ 1`. | `Qₙ : (Ω₀ × ⋯ × Ωₙ₋₁) × 𝓕ₙ → [0, 1]`, as used in the formula for `Pₙ`. |
| Theorem 3.2.3 proof, p. 101 | "`µ (A × A₁ × … × Aₜ)`". | `µₜ(A₀ × A₁ × ⋯ × Aₜ)`. |
| p. 112 | "the set `{0}` is a `δ{0}`-invariant set". | `{0}` and `{1}` are `P`-invariant sets. |
