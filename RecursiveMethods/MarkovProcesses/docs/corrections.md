# Corrections and conventions

Places where a Lean statement differs from the book: a hypothesis made explicit, a claim
corrected, or a convention chosen.

## Proofs that differ

| Where | Book | Lean |
| --- | --- | --- |
| §8.2, p. 222 | Countable additivity of `μ^∞(z₀, ·)` on finite rectangles is omitted (Ionescu-Tulcea, citing Shiryayev). | `μ^∞` is Mathlib's Ionescu-Tulcea measure (`pathMeasure`). Its finite-dimensional distributions are proved to be the book's `μᵗ(z₀, ·)` (`pathMeasure_marginal`), which determine it (`pathMeasure_unique`). |
| Theorems 8.4–8.6, pp. 226–231 | Monotone Class Lemma arguments starting from measurable rectangles. | Mathlib's kernel composition (`Kernel.compProd`), whose proofs are the same argument in π-λ form (`theorem_8_4`, `theorem_8_5`, `theorem_8_6`). |

Theorems 8.1 and 8.3 follow the book's proofs: indicators, then simple functions, then increasing limits.

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Markov process, (2), p. 223 | Defined through conditional probabilities `P(C \| a_{t−s}, …, a_t)` given the events `{σ_τ = a_τ}`. | These events typically have probability zero, and the conditional probabilities are then undefined. The Markov property with stationary transitions is stated as a factorization of the joint law: (history up to `t`, next state) = (law of the history) ⊗ `Q(z_t, ·)` (`ex_8_6ab`). Equivalently, `Q(z_t, ·)` is a regular conditional distribution of `z_{t+1}` given the history (`ex_8_6ab_condDistrib`, for standard Borel `Z`). |
| Exercise 8.10, p. 237 | `Z`, `W` metric spaces with their Borel sets; `g` continuous. | `Z`, `W` separable. Theorem 8.9 needs `g` measurable for the product σ-algebra `𝒵 × 𝒲`, and a continuous `g` is guaranteed to be so only when the Borel sets of `Z × W` are the product σ-algebra, which holds for second-countable spaces (`ex_8_10`). |
| Feller property, monotone transition function, p. 220 | `T` maps bounded continuous (resp. nondecreasing) functions to continuous (resp. nondecreasing) functions. | Stated for bounded functions, so that `Tf` is defined (`IsFeller`, `IsMonotoneTF`). |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Transition functions and stochastic kernels, pp. 212, 226 | Functions `Q : Z × 𝒵 → [0, 1]`. | `IsTransitionFunction` and `IsStochasticKernel` are the book's definitions, identified with Mathlib's Markov kernels (`isTransitionFunction_iff`, `isStochasticKernel_iff`), which carry the later results. |
| `n`-step transitions, p. 219 | `Q¹ = Q`, `Qⁿ⁺¹(z, A) = ∫ Qⁿ(z′, A) Q(z, dz′)`. | Also `Q⁰ = id` (`kpow`). |
| Histories, §8.2–8.3 | `zᵗ = (z₁, …, z_t) ∈ Zᵗ`. | `Fin t → Z`, with entry `i` holding `z_{i+1}`. `μᵗ(z₀, ·)` is `hist Q t z₀`, and `lastState z₀ zᵗ` is `z_t` (`z₀` when `t = 0`). |
| `μ^∞`, p. 222 | A measure on `(z₁, z₂, …)`. | `pathMeasure Q z₀` is the law of `(z₀, z₁, …)`, and `muInf Q z₀` drops the initial state. |
| Exercise 8.7, p. 224 | `σ_t` and `g_t` for `t ≥ 1`. | Indexed from `0`, with `𝓕₀` trivial and `σ₀ = 0` (`headsAt`). |
