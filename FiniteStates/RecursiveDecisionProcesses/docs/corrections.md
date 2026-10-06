# Corrections to the source

Places where a claim in Chapter 8 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In each
case the Lean statement proves the stated version and cites the original.
Entries are recorded when found and revised if formalisation shows the finding
itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| (8.54), p. 285 | `ζ ≔ κ/α`. | With `v̂ = v^κ`, `B(x, a, v)^κ = (r + β[∫ f μ]^{α/κ})^{κ/α}`, so Exercise 8.3.9 (i) holds only with `ζ = α/κ`. Both values are negative when `κ < 0 < α`, so Lemma 8.3.6 is unaffected. `SmoothAmbiguity.ζ` is `α/κ` (`SmoothAmbiguity.Bhat_pow`). |
| p. 285 | `V̂ = [v̂₁, v̂₂]` with `v̂₁ ≔ v₂^{1/κ}`, `v̂₂ ≔ v₁^{1/κ}`. | `φ(t) = t^κ` maps `[v₁, v₂]` onto `[v₂^κ, v₁^κ]`, which is the interval Exercises 8.3.8–8.3.9 need. `SmoothAmbiguity.w₁ = v₂^κ`, `SmoothAmbiguity.w₂ = v₁^κ`. |
| §8.1.3.6, p. 259 | `R` is bounded if `V` is convex and (8.20) holds for some `v₁ ≤ v₂` in `V`. | Exercise 8.1.12 and Theorem 8.1.2 apply `B` on all of `[v₁, v₂]`, which needs `[v₁, v₂] ⊆ V`; convexity of `V` gives only the segment between `v₁` and `v₂`. `RDP.IsBoundedBy` asks for `[v₁, v₂] ⊆ V`, which holds in every application (there `V = ℝ^X`). |
| §8.3.3.2, p. 282 | With `r̂(x, a) = r(x, a) + d(P, P̄)`, (8.50) is `inf_P {r̂ + β ∑ vP}`. | The penalty sits inside the `β`-weighted infimum, so the reward must be `r̂ = r + βd(P, P̄)` (`penalty_absorbed`). The conclusion (a special case of (8.49)) is unchanged. |
| Example 8.3.1, p. 281 | `B(w, a, v) = a w/(1 − β) + (1 − a) inf_φ ∑ v(w')φ(w')`. | Unemployment compensation and discounting are missing from the continuation value; `robustJobSearch` uses `c + β inf_φ ∑ vφ`, which is contracting (`robustJobSearch_isContracting`). |
| Ex 8.2.6, Ex 8.3.1, pp. 266, 275 | `τ ∈ [0, 1]`. | At `τ = 0` the quantile set is all of `ℝ` and has no minimum (as in Chapter 7, Exercise 7.3.4); `quantileJobSearch` and `MDP.quantile` take `τ ∈ (0, 1]`. |

## Proofs the book defers

| Where | Book says | How it is proved here |
| --- | --- | --- |
| Thm 8.1.1, p. 257 | Proof deferred to §9.1. | From the comparison property `RDP.Comparable` (`T_τ v_σ ≤ v_σ ⇒ v_τ ≤ v_σ`, `v_σ ≤ T_τ v_σ ⇒ v_σ ≤ v_τ`), which global stability gives by iterating `T_τ`. HPI improves (`RDP.vσ_le_vσ_greedy`) and terminates, since a strictly increasing sequence of values would inject `ℕ` into the finite policy set (`RDP.exists_hpiValue_succ_eq`); the terminal value is a fixed point of `T`, and any fixed point of `T` in `V` dominates every `v_σ`, hence equals `v*`. VFI from `v_σ` is squeezed between `T_{σ*}ᵏv_σ → v*` and `v*`; OPI values satisfy `Tᵏv₀ ≤ vₖ ≤ v_{σₖ} ≤ v*` (`RDP.opiValue_spec`); each of the finitely many suboptimal policies falls short of `v*` at some state, so greedy policies are eventually optimal. No continuity is needed. |
| Thm 8.1.2, p. 260 | Proof deferred to Chapter 9. | Comparability of a well-posed bounded RDP by Knaster–Tarski on `[v₁, v_σ]` and `[v_σ, v₂]` (`RDP.comparable_of_bounded`), then the same argument. |
| Thm 8.3.7, p. 286 | Proof deferred to §9.2.3; min-OPI "details omitted". | Reflection `B⁻(x, a, v) = −B(x, a, −v)` on `−V` (`RDP.neg`): global stability, `σ`-values, the value function, greedy policies and the Bellman operator all transfer (`RDP.isGloballyStable_neg_iff`, `RDP.neg_vσ`, `RDP.neg_vstar`, `RDP.isMinGreedy_iff`, `RDP.neg_T`). Min-HPI is HPI for `R⁻` (`RDP.minHpi_isMinGreedy`); min-VFI converges (`RDP.tendsto_iterate_Tmin`). |
| (8.51), p. 283 | Cites Dupuis and Ellis (2011), Proposition 1.4.2. | On a finite set, termwise `q ln t ≤ q(t − 1)` with `t = e^h p/(qZ)` gives the bound, and the Gibbs distribution `e^h p/Z` attains it (`klDuality`). |
| Lemma 8.3.6, p. 285 | `ψ' > 0`, `ψ'' < 0`, `f(θ, ·)` concave by Lemma 7.3.1. | `ψ(t) = β^{1/ζ}F(t)` with `F` the concave map of Exercise 7.1.8 for `θ = 1/ζ < 0` (`SmoothAmbiguity.concaveOn_psi`); `f(θ, ·)` is the Kreps–Porteus operator with `ξ ∈ (0, 1]`; composition by hand, since Mathlib's `ConcaveOn.comp` needs a convex image. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (8.26), p. 263 | The modulus `β` is nonnegative. | `RDP.IsContracting` includes `0 ≤ β`. |
| Cor 8.2.2, Prop 8.2.3, Prop 8.2.4, pp. 264, 271 | `V` nonempty; Prop 8.2.3 needs `v*` to solve the Bellman equation. | `V` closed and nonempty; Prop 8.2.3 then uses Corollary 8.2.2 and Theorem 8.1.1. |
| Ex 8.2.4, p. 265 | `b ≥ 0`. | `0 ≤ b < 1` and `β ≤ b`. |
| Ex 8.1.14–8.1.15, p. 260 | Which `v₁, v₂`. | The constants `±M/(1 − β)` with `M ≥ |B(x, a, 0)|`, from Blackwell's condition (`RDP.SatisfiesBlackwell.isBoundedBy`). |
| Ex 8.1.17, Prop 8.3.8, pp. 260, 287 | "Only one cycle, a self-loop at `d`; `d` accessible from every vertex"; `C(x)` the maximum path cost. | `O(d) = {d}` and a rank function strictly decreasing along every edge out of `x ≠ d` (equivalent, on a finite graph, to acyclicity away from `d`); `C` is the fixed point of `v ↦ max_{x'} {c(x, x') + βv(x')}`, reached after `max rank` iterations from `0` (`maxCostToGo`, `maxCost_maxCostToGo`), which is the largest cost of a path to `d`. |
| Prop 8.3.8, Prop 8.3.9, pp. 287–289 | `β = 1` resp. `β > 1`. | `pathRDP_minOptimal` holds for every `β ≥ 0`. |
| Prop 8.3.2, p. 278 | `D(x, a)` nonempty on `G`; (d) for all `v, w ∈ ℝ^X`. | `AdvConditions.nonempty`; (d) as `ConcaveOn ℝ univ`. |
| Prop 8.3.4, p. 281 | `𝒫(x, a)` "entirely arbitrary". | Nonempty sets of distributions (the infimum over an empty set is not finite). |
| §8.3.4, p. 283 | `μ(x, ·)` a probability on a finite-dimensional `Θ`; `κ < γ < 0 < α < 1`; `r₁ = min r`, `r₂ = max r`. | `Θ` finite and `μ(x, ·)` a distribution; `κ < γ < 0 < α` (`α < 1` is not used); bounds `0 < r₁ ≤ r ≤ r₂`. |
| Prop 8.1.4, p. 262 | `P` irreducible: every `P_σ` irreducible. | As stated, with `r ≫ 0`, `0 < β < 1`, `α, γ ≠ 0`. |
| Algorithm 8.1, footnote 1, p. 256 | The first `v`-greedy policy in an enumeration of `Σ`. | A fixed choice of greedy action at each state (`RDP.greedy`); the convergence results do not depend on the choice. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Figures 8.1–8.2, Listings 8.1–8.2, Ex 8.3.2 | Plots, code and the replication of Figure 8.2 | Computational. |
| Remark 8.1.1, §8.1.2.3 discussion, §8.4 | Interpretation; literature | Not applicable. |
