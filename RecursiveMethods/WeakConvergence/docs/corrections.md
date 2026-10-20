# Corrections and conventions

Places where a Lean statement differs from the book: a false claim corrected (with a Lean
counterexample), a gap in a proof closed, a hypothesis made explicit, or a convention chosen.

## False as printed

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 12.9 (Helly) and Corollary 1, pp. 372, 374, hypothesis | (3): `Fₙ(a̲) = 0` and `Fₙ(b̄) = 1` for all `n`. | For `l ≥ 2` this does not confine the measures to a compact set. On `ℝ²`, `δ_{(−n, 0)}` satisfies (3) with `a̲ = (0, −1)`, `b̄ = (1, 1)`, but has no weakly convergent subsequence (`theorem_12_9_false_hyp`). The intended hypothesis is that each `λₙ` is concentrated on `[a̲, b̄]`, that is, `Fₙ(x) = 0` whenever some `xᵢ < a̲ᵢ`, and `Fₙ(b̄) = 1` (`concentrated_iff`). |
| Theorem 12.9 and Corollary 1, conclusion | The limit satisfies `F(a̲) = 0`. | False even for `l = 1`: `δ_{1/(n+1)}` satisfies (3) with `a̲ = 0`, `b̄ = 1` and converges weakly to `δ₀`, and every weak limit of every subsequence has `F(a̲) = 1` (`theorem_12_9_false_concl`). The correct conclusion is that `F(x) = 0` whenever some `xᵢ < a̲ᵢ`, and `F(b̄) = 1` (`theorem_12_9`, `theorem_12_9_cor1`). |
| Exercise 12.6a, p. 374 | If `Fₙ(b̄(ε)) − Fₙ(a̲(ε)) > 1 − ε` for all `n`, the conclusion of Helly's theorem holds. | For `l ≥ 2`, `Fₙ(b̄) − Fₙ(a̲)` is not the mass of a rectangle. The sequence `δ_{(−n, 0)}` satisfies the condition with difference `1` but has no weakly convergent subsequence (`ex_12_6a_false`). For `l = 1` the condition is tightness and the claim holds (`ex_12_6a`). |
| Corollary 2 to Theorem 12.9, p. 375 | Monotone sequences satisfying (3) converge weakly. | Inherits the defect in (3). Proved for measures concentrated on `[a̲, b̄]` (`theorem_12_9_cor2`). |

## Gaps in proofs closed

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 12.7b, pp. 366–369 | Countable additivity on boxes: "without loss of generality" order the pieces of a countable disjoint decomposition of `(a, b]` as `b = b₁ ≥ a₁ = b₂ ≥ ⋯ → a`. | No such ordering exists in general for `l ≥ 2`. Replaced by the standard argument (`theorem_12_7b`). The vertex sum is additive when a box is cut by a hyperplane (`vertexSum_split`), hence on all box partitions (`boxContent`). Boxes form a semiring (`isSetSemiring_boxes`), and the content is countably subadditive by compactness and continuity from above (`isSigmaSubadditive`). Carathéodory's theorem then gives the measure. |
| Theorem 12.9, proof, p. 373 | The identity `G(a + θⱼd) = limᵢ G(a + εᵢ + θⱼd + θⱼε̂ᵢ)` at irrational points; "if `F` is continuous at `x`, so is `G`, and `F(x) = lim F_N^{(N)}(x)`". | The identity is asserted without justification, and the second step needs a sandwich argument. The diagonal construction is replaced by Prokhorov's theorem: a tight sequence of probability measures on a separable metric space has a weakly convergent subsequence (`exists_convWeak_subseq_of_tight`). The limit is concentrated on the rectangle by Theorem 12.3b (`measure_eq_one_of_convWeak`). |
| Support, p. 372 | Closed sets of measure one are closed under finite intersections, "and the argument extends to any family". | The extension to an arbitrary family needs separability. `exists_support` proves existence and uniqueness on any second-countable space by Lindelöf's theorem. The finite case is `support_inter`. |
| Theorem 12.10, p. 378 | Corollary 1 to Helly, stated on `ℝˡ`, is applied to measures on a compact `S ⊆ ℝˡ`. | This needs the extension to `ℝˡ` (Exercise 12.4) and the fact that the limit is concentrated on `S`. The Lean proof applies tightness on `S` directly (`theorem_12_10`). |
| Theorem 12.12, p. 383 | `⟨f, λ_a*⟩ = ⟨f, λ_b*⟩` from the upper bound (3); uniqueness of `λ*` is not argued. | The lower bound `(Tⁿf)(b) − (Tⁿf)(a) ≥ 0` (monotonicity of `Tⁿ`) is supplied. An invariant `λ₀` has `T*ⁿλ₀ = λ₀ ⇒ λ*`, so `λ₀ = λ*` (`theorem_12_12`). |
| Exercise 12.5b, p. 371 | Hint: use the functions of "Theorem 12.1" with "monotone" `f`. | There is no Theorem 12.1; Lemma 12.1 is meant, and its functions are nonincreasing. The Lean statement uses continuous nondecreasing `f` only, via the ramps `min 1 (n Σᵢ max 0 (sᵢ − xᵢ))` (`ramp`, `ex_12_5b`). This is the form Theorem 12.12 needs. |
| Lemma 12.14, p. 387 | `∂[E_k(ε)] = {z′ : \|f(y, z′) − f(yₙ, z′)\| ≤ ε for all n ≥ k, with equality for some n}`. | Only `⊆` holds, though only disjointness for distinct `ε` is used. The Lean proof of the key limit (1) avoids boundaries (`tendsto_integral_abs_sub`). It uses the continuous majorants `g_k(z′) = sup_{n≥k} \|f(yₙ, z′) − f(y, z′)\|`: maxima of a jointly continuous function over the compact sets `{y} ∪ {yₙ : n ≥ k}`. Weak convergence applies to each `g_k`, and `g_k ↓ 0` with dominated convergence finishes the proof. |
| Theorem 12.13, p. 384 | `(s, θ) ↦ (T_θ f)(s)` is uniformly continuous on `S × Θ̂`, so `T_{θₙ}f → T_{θ₀}f` uniformly. | Proved as a sequential lemma by compactness of `S` (`tendsto_uniform_markovOp`). Continuity of `(s, θ) ↦ (T_θ f)(s)` is never needed. |

## Hypotheses made explicit, and generalisations

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 12.7b, p. 366 | (D1)–(D3). | `0 ≤ F ≤ 1`, implicit in the limits of (D1), is assumed (`theorem_12_7b`). |
| Theorem 12.10, p. 376 | `S ⊆ ℝˡ` compact. | Any nonempty compact metric space. `S` must be nonempty for a probability measure to exist. |
| Exercise 12.6c, p. 374 | `S` a closed subset of `ℝˡ`. | Any `S ⊆ ℝˡ` (`ex_12_6c`); tightness is all that is used. |
| Exercise 12.10, p. 379 | `S = [a, b]`. | Any `S ⊆ ℝˡ` (`ex_12_10`). |
| Theorem 12.13, p. 384 | `Θ ⊆ ℝᵐ`. | Any metric space. |
| Lemma 12.14, p. 386 | `X ⊆ ℝˡ`, `Z ⊆ ℝᵏ` convex. | Continuity holds for any metric spaces `X`, `Z` (`lemma_12_14_cont`). Convexity of `X` is needed only for the concavity statements. |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Distribution functions, §12.3 | Helly's theorem and its corollaries are stated for distribution functions. | Stated for the distribution functions of probability measures (`distFun`). By Theorem 12.7b these are all functions satisfying (D1)–(D3). |
| `S = [a, b]`, §12.4 | A rectangle in `ℝˡ`. | The subtype `Icc a b` of `Fin l → ℝ` with the componentwise order. `[a, c]` and `[c, b]` are `Iic c` and `Ici c` in it, and `a`, `b` are `IccBot`, `IccTop`. |
| Monotone and dominance, p. 378 | "Increasing" `f`. | Nondecreasing (`Monotone`) bounded measurable `f`. |
| Exercise 12.8, p. 376 | `S = [0, 1]`. | Mathlib's `unitInterval` with `σ(s) = 1 − s`. Part (c) characterises the invariant measures as those symmetric about `1/2` and exhibits infinitely many. |
| Exercise 12.13, pp. 380–381 | `h`, `H` and the sets `E₁`, `F`, `E₂` are given by Figure 12.4. | An explicit choice on `ℝ` with all mass in `[0, 3]`: `E₁ = [0, 1]`, `F = (1, 2)`, `E₂ = [2, 3]` (`lowEnd`, `highEnd`). Since SLP never defines a transient set for general state spaces, "transient" is read in the finite-chain sense of p. 333. From every `s ∈ F` the process enters the invariant set `E₁ ∪ E₂` with positive probability (`ex_12_13b`). Part (c) shows that the two sequences have no common weak limit (`ex_12_13c`). |
| `P`, `T`, `T*` | Transition function and the associated operators. | Markov kernels, `markovOpR`, `adjointOp` and `kpow κ n`, carried from `RecursiveMethods/MarkovProcesses`. |

## Typographical errors

| Where | Book | Correct |
| --- | --- | --- |
| Theorem 12.3, proof (b)⇒(a), p. 359 | `g = 1 − f` takes values in `[0, 1)`. | In `(0, 1]`. |
| Theorem 12.6, proof, p. 363 | "an open set `B` such that `A ⊆ B ⊆ C`". | An open set `C`. |
| Theorem 12.7b, p. 366 | `λ((a, +∞))` written with an undefined `d`. | The generating rectangles are read coordinatewise. |
| Exercise 12.5b, p. 371 | "Theorem 12.1". | Lemma 12.1. |
| Theorem 12.13, proof, p. 384 | `∫ f(s′) P_θ(s, s′)`. | `∫ f(s′) P_θ(s, ds′)`. |
