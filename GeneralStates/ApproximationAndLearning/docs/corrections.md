# Corrections to the source

Places where a claim in Chapter 9 of Sargent and Stachurski, *Dynamic Programming*, Volume 2,
is imprecise as printed, relies on an unstated hypothesis, or where the Lean statement departs
from the printed one. In each case the Lean statement proves the corrected or stated version and
cites the original. Entries are recorded when found and revised if formalisation shows the finding
itself to be wrong.

## Errors and gaps

| Where | Book says | Correction |
| --- | --- | --- |
| Lemma 9.1.7, p. 304 | `T` is a contraction on a closed `Θ ⊆ ℝⁿ`; then `F` is a contraction with the same fixed point. | `Fθ = θ + α(Tθ − θ)` maps `Θ` into itself only when `Θ` is convex (or `α = 1`): on `Θ = {0, 1}` with `T ≡ 1`, `F0 = α ∉ Θ` (`lemma_9_1_7_needs_convex`). The lemma is proved for convex `Θ` in a normed space (`lemma_9_1_7`). |
| Thm 9.1.8, p. 306 | `T` is an order-preserving contraction on `Θ ⊂ ℝⁿ`; under (i)–(iii) `θ_k → θ̄` almost surely. | The norm is not specified, and with noise the iterates (9.14) can leave a proper subset `Θ`, where `T` is undefined. The theorem is proved for `T` a contraction of a real Hilbert space for its own norm (for `ℝⁿ`, the Euclidean norm), defined everywhere, with `α_k ∈ [0, 1]`, square-integrable `θ₀` and `W_k`, and `C ≥ 0` (`robbins_monro`); order preservation is not needed. The book's applications (asset pricing, Q-learning) use supremum-norm contractions, which need not be Euclidean contractions (for `P` with every row `e₁`, `‖βP‖₂ = β√n`); that case is Tsitsiklis's (1994) result, cited and not formalised. |
| Prop 9.1.5, p. 303 | `L` nonexpansive and order preserving. | Order preservation alone makes `(L(V), 𝕋̂)` an ADP (`ADP.approxADP`). |
| Thm 9.2.2, p. 320 | Optimality at one state implies optimality when `P_σ` is irreducible. | Correct as stated (with `β > 0`, as `β ∈ (0, 1)` there, and `X` nonempty); without irreducibility it fails (`theorem_9_2_2_needs_irreducible`: two absorbing states). |

## Hypotheses the book leaves implicit, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| Lemma 9.1.1 | `κᵢ ∈ bX`. | The `κᵢ` are measurable; boundedness follows from (9.2) (`KernelAverager.κ_le_one`). |
| Example 9.1.1 | Grid points in `ℝᵈ`, `h > 0`. | Any normed space with its Borel structure and any `h` (`gaussianAverager`); at least one grid point. |
| Example 9.1.2 | "The obvious modifications at the endpoints." | `κ₀ = 1` left of `x₀` and `κₙ = 1` right of `xₙ` (`hat`), so (9.2) holds on all of `ℝ`; uniqueness is among functions affine on each `[xⱼ, xⱼ₊₁]` (`example_9_1_2_unique`). |
| p. 299 | `Z` has full column rank. | `θ ↦ Zθ` injective (`least_squares`); then `ZᵀZ` is invertible and `θ̂` is the unique minimizer. |
| Assumption 9.1.1 | The metric is complete. | Completeness (`CompleteSpace V`) is used only for the existence of `v*` and `v̂`; Theorems 9.1.3–9.1.4 hold for any fixed point `v*` of `T` (`ADP.theorem_9_1_3`, `ADP.theorem_9_1_4`), stated for consecutive FVI iterates `u`, `v = LTu` (`ADP.theorem_9_1_3_fvi` for `v_N`). |
| Lemma 9.1.7 | `α ∈ (0, 1)`. | `α ∈ (0, 1]`; the geometric bound `damped_iterate_le` also needs `β ≥ 0`. |
| Footnote 1, p. 308 | `𝔼[‖W_{k+1}‖² ∣ ℱ_k] ≤ C(1 + ‖v_k‖²)`. | Shown pointwise for every draw, with the supremum norm and `C = 8|X|β²(1 + ‖d‖∞²)` (`AssetPricing.sum_sq_noise_le`). |
| §9.2.2 | `V̂ = ℝ^G_{++}`. | The subtype of strictly positive functions (`FiniteMDP.QPos`); `F` lands there because `P(x, a, ·)` is a probability vector (`FiniteMDP.expSum_pos`). |
| §9.2.2.3 | Theorem 5.2.18 applies. | Its hypotheses are checked: each primary `T_σ` is a supremum-norm contraction (`FiniteMDP.primary_contraction`), so Theorem 3.1.5 gives the fundamental optimality properties, and the subordinate ADP is well posed by Lemma 5.2.12 (`FiniteMDP.section_9_2_2_3`). |
| Ex 9.2.2 | `d(q, q') = ‖ln q − ln q'‖∞`. | Stated as: `|ln q − ln q'| ≤ c` everywhere implies `|ln T̂_σq − ln T̂_σq'| ≤ βc` everywhere. |
| (9.18) | The update in terms of samples. | The update moves only the visited pair (`FiniteMDP.qUpdate_apply`); the sample's mean under `P(x, a, ·)` is `(Sq)(x, a)` (`FiniteMDP.Shat_unbiased`). |
