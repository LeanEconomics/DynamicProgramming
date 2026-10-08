# Corrections to the source

Places where a claim in Chapter 9 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, relies on an unstated hypothesis, and where the Lean
statement departs from the printed one. In each case the Lean statement proves the
stated version and cites the original. Entries are recorded when found and revised
if formalisation shows the finding itself to be wrong.

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Prop 9.2.1, Thm 9.2.4, p. 299 | `Σ` nonempty. | `[Nonempty P]`. If `V = ∅` an ADP may have no policies, and then `T` has no fixed point, so max-stability fails; for nonempty `V` the existence of greedy policies already makes `Σ` nonempty. |
| §9.2.1.6, p. 301 | `T̂_φ` is a self-map of `V`. | Assumed (`hmix`): it holds for `V = ℝ^X` and for order intervals, since `(T̂_φ v)(x)` is a convex combination of values `B(x, a, v)` that each lie in the interval at `x`, but not for every `V` on which the pure policy operators act. |
| Lemmas 9.2.7–9.2.8, p. 302 | `m ≥ 1`. | `1 ≤ m` (with `m = 0`, `W_m` is the identity and `Tv ≼ W_m v` fails). |
| Example 9.1.3, p. 296 | `S_σ` acts on `ℝ^G`. | `S_σ` acts on `ℝ^{X × A}`; values off `G` are carried along and never enter `S_σ q` on `G`. |
| Example 9.1.4, p. 296 | `θ ≠ 0`, `β ≥ 0`. | As stated (from the MDP: `β ∈ (0, 1)`). |
| Footnote 1, p. 298 | A designated `v`-greedy policy for each `v`. | A fixed choice (`ADP.greedy`); min-HPI is HPI for the dual ADP, whose greedy policies are the min-greedy policies of `A` (`ADP.minHpi_isMinGreedy`), which is Exercise 9.2.7 (iii). |

## Proofs

| Where | Book says | How it is proved here |
| --- | --- | --- |
| Lemma B.4.1 (iv), p. 350 | `(vₖ)` lies in the finite set `V_Σ`, so it repeats. | A strictly increasing sequence of values would make `k ↦ σₖ` injective from `ℕ` into the finite policy set. |
| Lemma 9.2.10, p. 303 | Uses `e = min_{σ ∉ Σ*} ‖v_σ − v*‖`. | Each non-optimal policy falls short of `v*` at some state; since there are finitely many policies, from some `K` on every `vₖ` exceeds each such `v_σ` at its state. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Example 9.2.2, Remarks 9.1.1–9.1.2, Figure 9.1, §9.3 | Interpretation, illustration and literature | Not applicable. |
