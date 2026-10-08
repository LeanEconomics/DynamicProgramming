# Corrections to the source

Places where a claim in Chapter 7 of Sargent and Stachurski, *Dynamic Programming*, Volume 2,
is imprecise as printed, relies on an unstated hypothesis, or where the Lean statement departs
from the printed one. In each case the Lean statement proves the corrected or stated version and
cites the original. Entries are recorded when found and revised if formalisation shows the finding
itself to be wrong.

## Errors and gaps

| Where | Book says | Correction |
| --- | --- | --- |
| Assumption 7.2.1, p. 218 | "The function `B` is bounded". | `B` cannot be bounded on `G × bX` together with Blackwell's condition: for an LDP, `B(x, a, v + κ) = B(x, a, v) + βκ` is unbounded in `κ`. The proof uses boundedness of `(x, a) ↦ B(x, a, v)` on `G` for each `v` (as the proof of Proposition 7.2.10 states it), which is the hypothesis (`BRDP.bdd`). |
| Lemma 7.1.1, proof, p. 216 | The sets `S_k` are Borel, "since [they are] defined by finitely many inequalities involving measurable functions". | The RDP definition makes neither `x ↦ B(x, a, v)` nor `{x : a ∈ Γ(x)}` measurable. Both are hypotheses of `RDP.lemma_7_1_1` (and of Propositions 7.2.1 and 7.2.4). In §7.2.1 and §7.2.2 the first follows from the measurability of `(x, a) ↦ B(x, a, v)`. |
| Ex 7.1.2, (7.5), p. 210 | `π(x) ≤ ηℓ(x) + δ`. | An upper bound on `π` does not make `B(·, σ(·), v)` `ℓ`-bounded; the solution (p. 407) uses `|π(x)| ≤ ηℓ(x) + δ`, which is the hypothesis. `ℓ` is assumed integrable under each `P(x, ·)`, as `∫ ℓ dP(x) ≤ αℓ(x)` presupposes (`exercise_7_1_2`). |
| Ex 7.3.4, solution, p. 410 | `V` is the bounded measurable functions `X → (0, ∞)`, and `V̂ = {ln ∘ v : v ∈ V} = bX`. | `ln v` is unbounded below when `v` is not bounded away from `0`, so `V̂ ≠ bX`. `ln v ∈ bX` exactly when `e^{−K} ≤ v ≤ e^K` for some `K` (`PosValues`), and `r̂ = ln r` must be bounded on `G` for `(Γ, bX, B_RS)` to be an RDP. With these, the isomorphism holds (`exercise_7_3_4`). |
| (7.25), p. 232 | `ℓ(w) = 𝔼 ∑_t δᵗ u(Ŵ_t)` is the weight function. | A weight function satisfies `ℓ ≥ 1` (§A.5.3.5); this `ℓ` can be smaller (for example near `0` when `u(0) = 0`). The expected discounted sum of `u + 1` is a weight function and has every property the solutions use. The formalisation assumes those properties: `ℓ` measurable, increasing, `≥ 1`, with `ℓ(s + ·)` integrable for every shift `s` and `u(w⁺) + δ ∫ ℓ(Rw + y)ψ(dy) ≤ ℓ(w)` (`SavingsU`). The path-space expectation itself is not constructed. |
| Assumption 7.3.1, p. 234 | `Γ(k, z) = [0, θf(k, z)]` with `θ > 0` and `f` bounded and continuous. | `Γ` is empty where `f < 0`. `f ≥ 0` and `θ ≥ 0` are assumed (`Investment`). |

## Hypotheses the book leaves implicit, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| §7.1.1.1 | `V ⊆ ℝ^X` with the pointwise order. | `V` is a type with an order embedding `ev : V → ℝ^X` (`RDP.ev`, `RDP.ev_le_iff`); the book's case is a subtype. This lets `bX`, `bℓX₊` and the value spaces of the examples carry their own structure. `B` is a function of `(x, a)` and of a function `X → ℝ`; only its values on `G × ev(V)` matter. |
| §7.1.1.1 | `X` and `A` separable metric spaces. | Measurable spaces in general; topologies only where continuity is used (first countable in Proposition 7.2.10, sequential for the interval correspondences). |
| Lemma 7.1.2, Props 7.2.2, 7.2.5, 7.2.10 | Theorem A.3.3 (Berge, with a measurable selection) is cited. | Its conclusion is the hypothesis `HasMaxSelections Γ`, proved for interval correspondences (`hasMaxSelections_Icc`, restated from Chapter 6), which covers every application. |
| Lemma 7.1.2, last claim; Prop 7.2.8 | A unique maximizer is continuous (Theorem A.3.3). | Hypothesis `HasContinuousUniqueMax Γ`, proved for interval correspondences on sequential spaces (`hasContinuousUniqueMax_Icc`). |
| §7.2.1.1, §7.2.2.1 | `(x, a) ↦ B(x, a, v)` measurable on `G`. | Measurable on `X × A`; the values of `B` off `G` are irrelevant and can be set to `0` when `G` is measurable. |
| Ex 7.1.1, Ex 7.1.4 | Finite MDPs. | `P(x, a, ·)` nonnegative; for (7.8) also `∑_{x'} P(x, a, x') = 1`, so the sum inside the logarithm is positive. Any `θ ≠ 0`. |
| Ex 7.1.3 | `γ > 0`, `γ ≠ 1`; wealth in `ℝ₊`. | Any `γ ≠ 1` and `0 ≤ β ≤ 1`; wealth in `ℝ` with `Γ(w) = [0, max(w, 0)]`, as in Chapter 6. |
| Prop 7.2.6 | `X` partially ordered. | Any preorder. |
| Prop 7.2.7–7.2.8 | `X` and `A` convex subsets of vector spaces, `G` convex. | `X` and `A` vector spaces and a convex `S ⊆ X`: the feasible pairs over `S` are convex and `B` is concave on them for `v` concave on `S`; `v*` is concave on `S` (`WRDP.feasibleOn`). The savings model uses `S = ℝ₊` inside `X = ℝ`. |
| Ex 7.2.3–7.2.4 | Concavity of `(w, c) ↦ ∫ v(R(w − c) + y)ψ(dy)` for `v` concave on `ℝ₊`. | Needs `R(w − c) + y ∈ ℝ₊`: income is nonnegative almost surely (the book's density lives on `ℝ₊`), assumed. |
| Ex 7.3.2, solution, p. 409 | `∫ ℓ(s̄ + y)φ(y) dy < ∞` for `s̄ = sup sₙ`, "by the definition of `ℓ`". | Integrability of `ℓ(s + ·)` for every shift `s` is assumed (`SavingsU.integrable_ℓ`); with `R > 0` it is the book's condition. The proof applies Scheffé's lemma to `ℓ(x)φ(x − s)`, whose integral `∫ ℓ(s + y)φ(y) dy` is continuous by dominated convergence (`ℓ` increasing and continuous), instead of truncating at `M`. |
| Assumption 7.2.11, Prop 7.2.10 | `r` bounded and continuous; `(x, a) ↦ ℰ[v(f(x, a, ξ))]` measurable (standing assumption). | `r` bounded on `G` and continuous on `G`; the measurability is a hypothesis, proved for `𝔼` and the entropic certainty equivalent (`measurable_meanCE_comp`, `measurable_entropicCE_comp`). |
| (7.21), Ex 7.2.6 | `ℰ_γ(Z) = −γ⁻¹ ln 𝔼 exp(−γZ)`, `γ > 0`. | `ℰ^θ(Z) = θ⁻¹ ln 𝔼 exp(θZ)` for every `θ ≠ 0` (`entropicCE`); `ℰ_γ = ℰ^{−γ}`. This also covers (7.28) for both signs of `θ`. |
| p. 228 | `𝔼` and the pessimistic certainty equivalent are coherent. | Proved for a probability measure (`meanCE_isCoherent`, `pessCE_isCoherent`). |
| p. 229 | `𝒦` fails cash invariance. | A two-point example with `γ = 2` (`kpExp_not_cash_invariant`). |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| §A.5.3.5, Thm A.5.24 | `bℓX` with the norm `‖·‖ℓ` is a Banach lattice. | `bℓX` is represented by `bX` through `v = ℓh`; this is an order isomorphism (`wev_le_iff`) and an isometry (`norm_eq_wnorm`), so the Banach lattice structure is that of `bX`, with `ℓ` corresponding to `𝟙` (`exercise_A_5_25`). `bℓX₊` is the closed cone `bX₊` (`posCone`) and `bℓcX₊` the continuous `h` (`bcPlus`), when `ℓ` is continuous. |
| §7.1.2.2 | "`T` is the Bellman operator for `(Γ, V, B)`". | The generated ADP is `RDP.adp`; Lemmas 7.1.1–7.1.2 give `(Tv)(x)` as the greatest element of `{B(x, a, v) : a ∈ Γ(x)}`. |
| Prop 7.2.1, Prop 7.2.4 | "If `X` is also finite, HPI converges in finitely many steps". | From every `v ∈ V_U`, some iterate of Howard's operator is `v*` (`proposition_7_2_1_finite`, `proposition_7_2_4_finite`). |
| §7.1.1.5 | Savings as an RDP. | Through the LDP of Example 6.1.5 and (7.9) (`savings_B`). |
| §7.3.3 | The robust Bellman equation is rewritten with the duality (7.22). | The risk-sensitive form is proved to satisfy the conclusions of Proposition 7.3.2 (`Investment.section_7_3_3`); the duality is not formalised. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Examples 7.1.1–7.1.3 | ADPs that are not RDPs | Informal (they concern the form of the Bellman equation and of `Σ`). |
| Theorem 7.2.9, Remark 7.2.1, (7.20), (7.22) | Föllmer–Schied duality and its instances | Cited from the literature. |
| §7.2.4.2 | Quantile (VaR) and CVaR certainty equivalents, Example 7.2.2, (7.27), the CVaR part of Example 7.3.1 | Quantile functions and the quantile convergence theorem are not available. |
| (7.25) | The path-space expectation defining `ℓ` | Only its properties are used (see above). |
| §7.3.2.3, Figures 7.1–7.7 | Numerical illustrations | Numerical. |
| §7.4 | Chapter notes | Not mathematical claims. |
