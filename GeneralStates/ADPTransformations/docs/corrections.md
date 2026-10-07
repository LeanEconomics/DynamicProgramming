# Corrections to the source

Places where a claim in Chapter 5 of Sargent and Stachurski, *Dynamic Programming*, Volume 2,
is imprecise as printed, relies on an unstated hypothesis, or where the Lean statement departs
from the printed one. In each case the Lean statement proves the corrected or stated version and
cites the original. Entries are recorded when found and revised if formalisation shows the finding
itself to be wrong.

## Errors

| Where | Book says | Correction |
| --- | --- | --- |
| Lemma 5.2.2 (ii), p. 162; Thm 5.2.3, p. 163 | Strong order stability transfers between strongly semiconjugate systems when `F, G` (Lemma 5.2.2) or `G` (Theorem 5.2.3) are order continuous, i.e. `vₙ ↑ v ⟹ Svₙ ↑ Sv` (§A.5.1.3). | False with that definition. `SemiconjCounterexample.theorem_5_2_3_fails`: `Fork` is a chain `a₀ > a₁ > ⋯` above two incomparable points `⊥₁, ⊥₂`, `Chain = ℕ∞ᵒᵈ`, and in both every increasing sequence is eventually constant, so every order preserving map is order continuous. With `S(aₙ) = aₙ₊₁`, `S(⊥ᵢ) = ⊥₁`, `Ŝc = c + 1`, `F(aₙ) = n + 1`, `F(⊥ᵢ) = ⊤`, `G(n) = aₙ`, `G(⊤) = ⊥₁`, the systems are strongly semiconjugate and `Ŝ` is strongly order stable, but `Sⁿa₀ = aₙ` has no infimum. The proofs also need decreasing limits ("the proof that `Ŝw ≼ w` implies `Ŝⁿw ↓ Fv̄` is similar" uses `F` on a decreasing sequence). Proved with `G` (and `F`) also carrying `↓` limits (`IsStronglySemiconj.lemma_5_2_2_ii`, `IsStronglySemiconj.theorem_5_2_3`). The firm entry map `G` has the property (`FirmEntry.lemma_5_2_8`), so Proposition 5.2.7 stands. |
| Thm 5.2.4, p. 163 | With `wₙ ↓ w ⟹ Gwₙ ↑ Gw`, strong order stability of `Ŝ` transfers to `S`. | False for the same reason, by reversing the order of `Chain` (`SemiconjCounterexample.theorem_5_2_4_fails`). Proved with `G` also turning `↑` limits into `↓` limits (`IsStronglySemiconj.theorem_5_2_4`). |
| Prop 5.3.2, p. 176 | If `X` has no isolated point under `P`, Q-optimal policies are MDP-optimal. | Needs `β > 0`; MDPs in §1.2 allow `β ∈ [0, 1)`. With `β = 0`, every policy is Q-optimal (`S_σ q = r`) but not every policy is MDP-optimal (`proposition_5_3_2_needs_beta_pos`). Example A.1.12 makes `P` strictly order preserving, and `F = r + βP` inherits this only when `β > 0`. |

## Hypotheses the book leaves implicit, gaps, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| Lemma 5.1.11 (ii), p. 159 | The min-results "follow by Exercise 2.2.6". | Exercise 2.2.6 converts them into max-results for the dual ADP on `V̂^∂`, but `V̂^∂` is not an order interval of a Banach lattice, so Theorem 4.1.11 does not apply as is. The reflection `w ↦ −w` carries `[−v₂, −v₁]` onto `V̂^∂`, swaps concave and convex in Du's conditions, and gives `BanachLattice.theorem_4_1_11_min`. |
| §5.1.3, p. 158 | `m₁ = (min r^α − ε)^θ`, `m₂ = (max r^α + ε)^θ`. | Any `0 < c₁ < r^α < c₂` on the feasible pairs (`EZModel.c₁`, `EZModel.c₂`), which includes the book's choice. |
| §5.1.3 | `β`. | `0 ≤ β < 1` is used: `β < 1` for the strict inequalities of Exercise 5.1.9. |
| Thm 5.1.7 (iii)–(v), Thm 5.1.10 | Under the fundamental optimality properties. | The convergence equivalences need only regularity (for VFI) and nothing for OPI and HPI (`ADP.IsIsomorphic.vfiConverges`, `opiConverges`, `hpiConverges`). |
| Lemma 5.2.12 (i), (5.22) | For order-preserving FDPs. | Well-posedness and (5.22) transfer for every FDP; order stability for both order-preserving and order-reversing ones (`FDP.lemma_5_2_12`). |
| Assumption 5.2.1 (i), §5.2.1.3 | `β(z) > 0`; `f ∈ E ⊆ ℝ₊`. | `β ≥ 0`; the fixed cost is any nonnegative measurable function of a draw from `φ` on any measurable space (`FirmEntry`). |
| Lemma 5.2.8, p. 166 | `G` is order continuous. | Also preserves decreasing limits, which the corrected Theorem 5.2.3 needs (`FirmEntry.lemma_5_2_8`). |
| Example 5.1.4 | On `cℝ` and `c(0, ∞)`. | Stated on all functions `ℝ → ℝ` and `ℝ → (0, ∞)`; continuity plays no role in the conjugacy. |
| Example 5.1.3 | `A = EDE⁻¹` diagonalizable. | Over `ℝ`: `E` an invertible real matrix and `D` a real diagonal matrix. |
| §5.3.2 | The model of §4.2.3.1. | Uses Proposition 4.2.4, which needs `X` nonempty. |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| §5.1.1 | Conjugacy `F ∘ S = Ŝ ∘ F` for a bijection, homeomorphism or order isomorphism `F`. | `Function.Semiconj F S Ŝ` with `F : V ≃ V̂`, `V ≃ₜ V̂` or `V ≃o V̂` (`IsConjugate`, `IsTopConjugate`, `IsOrderConjugate`). |
| §5.1.2.3 | `F` an order anti-isomorphism. | `F : V ≃o V̂ᵒᵈ` (`ADP.IsAntiIsomorphic`). |
| Thms 5.1.7, 5.1.10 | `W` and `H` built from a `v`-greedy policy. | OPI and HPI run with a greedy selector `g`; `g` for `(V, 𝕋)` corresponds to `g ∘ F⁻¹` for `(V̂, 𝕋̂)`. |
| Assumption 5.2.1 (iii) | `sup_z 𝔼_z ∏_{t<n} β(Z_t) < 1`. | Operator form `sup_z (Kⁿ𝟙)(z) ≤ λ < 1` with `(Kh)(z) = β(z) ∫ h dQ(z, ·)` (`FirmEntry.DiscountCondition`); the two agree by Lemma 6.1.4. |
| §5.2.3 | Order-reversing FDPs studied directly. | Reduced to the order-preserving case by replacing `V̂` with `V̂^∂` (`FDP.dualize`); the subordinate ADP becomes its dual (`FDP.dualize_sub`). |
| §5.2.2.1 | `T` and `T̂`. | The Bellman operators of the generated ADPs; `T̂▿` is the Bellman operator of the dual subordinate ADP. |
| Algorithm 5.1 | HPI on `(V̂, 𝕋̂)` with greedy step (5.33), then a policy satisfying (5.33) at `v̂*`. | HPI with any greedy selector reaches `v̂*` in finitely many steps, and a policy satisfying (5.33) at `v̂*` is optimal for (5.31) (`EZSavings.section_5_3_3`). |
| §5.1.3 | `P` stochastic on feasible pairs. | `P(x, a, ·)` stochastic for all `(x, a)`; values off `G` are irrelevant. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Figures 5.1–5.3 | Diagrams, the optimal savings policy, the speed gain of Algorithm 5.1 | Numerical or informal. |
| Remark 5.3.1 | Deterministic versus randomized policies in discrete choice, Gumbel shocks and entropy regularization | Discussion, not a stated result. |
| §5.4 | Chapter notes | Not mathematical claims. |
