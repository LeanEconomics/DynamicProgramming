# Corrections and conventions

Places where a Lean statement differs from the book: a claim corrected, a gap in a proof closed,
a hypothesis made explicit, or a convention chosen.

## Missing pages

Book pp. 422–423 are missing from the scan used: the end of the proof of Theorem 14.4, the
statement and proof of Theorem 14.5, and display (6). Theorem 14.5 is formalised in the form in
which the book later uses it (p. 424): under the hypotheses of Theorem 14.4, the averages converge
a.e. The proof is the method of subsequences along the squares `m²`.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Lemma 14.8, p. 427 | Holds for an arbitrary probability measure `μ` on `S^∞`. | False: with `S = {0, 1}`, `P(s, ·)` uniform, `μ = δ_{(0, 0, …)}`, `f = 1_{1}` and `m = 1`, the averages tend to `−1/2` (`lemma_14_8_counterexample`). The proof uses the Markov property, which needs `μ = μ(s₀, ·)`; that is the only case used, and `lemma_14_8` is stated for it. |
| Introduction, p. 416 | (3) holds when `S` is compact and `P` is Feller. | Assumption 14.3 is also needed. The identity kernel on `{0, 1}` is Feller, and `(1/N) Σ f(sₙ) = f(s₀)`; no single `λ*` serves for both starting points (`feller_compact_not_enough`). |
| Display (4), p. 427 | A threshold `N_m(ε)` uniform over `ω ∉ A_m`. | a.e. convergence gives a threshold depending on `ω`. The proof of Theorem 14.7 here lets every threshold depend on `ω`. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 14.6, p. 424 | No integrability of `fₖ`; `E[(fₖ − E(fₖ \| 𝒜ₖ₋₁))²] < M`. | `fₖ ∈ L²`, so that the conditional expectations exist and the products are integrable. Condition (c) is for `k ≥ 1` only; the indices are shifted to `f (k + 1) − E(f (k + 1) \| 𝒜 k)`. |
| p. 431 | `L` is the space of all linear operators. | It contains unbounded operators, with `‖T‖_L = ∞`. Operators are continuous (`X →L[ℝ] X`). |
| Lemmas 14.12–14.13, pp. 433–434 | `‖T‖ = 1`. | Only `‖T‖ ≤ 1` is used. |
| Assumption 14.1 | `S` a compact subset of `ℝˡ`. | `S` a compact metric space. |

## Gaps in proofs closed

| Where | Book | Lean |
| --- | --- | --- |
| Proof of Lemma 14.8, pp. 429–430 | `E[(Tʲf)(σ_{n−j}) \| 𝓕̂^{n−j−1}] = (T^{j+1}f)(σ_{n−j−1})`, without citation; identities "for all `ω`"; `𝓕̂⁰` undefined. | The Markov property is proved from the Ionescu-Tulcea construction (`markov_property`). The identities hold a.s. The filtration is that of the coordinates `0, …, k` (`Filtration.piLE`), which includes `σ₀ = s₀`. |
| Proof of Lemma 14.9, pp. 436–437 | `Hₙ` uses the powers `0, …, n − 1`; Assumption 14.3 and Lemma 14.9 use `1, …, n`. | The shift costs `O(‖f‖/n)` in (10) (`integral_cesaroOp_tendsto`), and `(1/M) Σ_{m=1}^M Tᵐf = T(H_M f)` with `‖T(H_M f − f̄)‖ ≤ ‖H_M f − f̄‖` (`lemma_14_9_of_repr`). |
| Proof of Lemma 14.13, p. 435 | The weak limit of `(Hₙ − I)x` is written `x − x̄`. | It is `x̄ − x`; the closed subspace is symmetric (`lemma_14_13`). |
| Theorems 14.10 and 14.14 | Stated without proof (Luenberger; Royden). | Proved: minimum norm duality by Hahn–Banach on `X/M` (`theorem_14_10`), and Riesz by splitting the functional into positive parts and applying Riesz–Markov–Kakutani (`theorem_14_14`). |

## Conventions

* Sums run over `k = 0, …, n − 1` in §14.1 (the book's `k = 1, …, n`).
* Paths are `ω : ℕ → S` with `ω 0 = s₀`; the book's `σₙ`, `n ≥ 1`, are the coordinates `n ≥ 1`.
* The book reuses `T` for the functional in Theorem 14.14 and writes "Theorem 14.13" for
  Lemma 14.13 (p. 435). Here the functional is `Λ`.
* Only the representation half of Theorem 14.14 is used, not the isometry with the total variation
  norm.
