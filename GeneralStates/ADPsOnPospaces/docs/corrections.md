# Corrections to the source

Places where a claim in Chapter 3 of Sargent and Stachurski, *Dynamic
Programming*, Volume 2, is imprecise as printed, relies on an unstated hypothesis, or
where the Lean statement departs from the printed one. In each case the Lean statement
proves the corrected or stated version and cites the original. Entries are recorded when
found and revised if formalisation shows the finding itself to be wrong.

## Errors

| Where | Book says | Correction |
| --- | --- | --- |
| §3.1.2, Thm 3.1.5, p. 101 | `(V, 𝕋)` is semi-regular if some closed `V₀ ⊂ V_G` has `TV₀ ⊂ V₀`; then the fundamental optimality properties hold. | The empty set always qualifies, so every ADP would be semi-regular, and the theorem is false for `V₀ = ∅`. On `V = ℝ` with policies `n ∈ ℕ` and `T_n v = v/2 + 1 − 1/(n + 1)`, every `T_n` is a contraction of modulus `1/2`, the metric is complete and sup-nonexpansive, `(V, 𝕋)` is semi-regular on `∅`, but no greedy policy exists anywhere and the fundamental optimality properties fail (`ADP.theorem_3_1_5_needs_nonempty`). The proof's step "`T` has a fixed point in `V₀`" needs `V₀ ≠ ∅`, which `ADP.theorem_3_1_5` assumes. The same applies to Lemma 3.1.9 (iii). |
| Thm 3.1.7, p. 102, proof | Applies Theorem 3.1.5 to the dual ADP. | Theorem 3.1.5 for `(V, 𝕋)^∂` needs the metric to be sup-nonexpansive for the reversed order, that is, inf-nonexpansive (`isInfNonexpansive_iff`), and sup-nonexpansiveness does not imply this. On the three-point poset `0 < 1, 0 < 2` the metric `d(1, 2) = 1`, `d(0, 1) = d(0, 2) = 3/2` is sup-nonexpansive but not inf-nonexpansive (`vShape_sup_not_inf`). `ADP.theorem_3_1_7` is proved under inf-nonexpansiveness. Both properties hold for Banach lattices with a normalized order unit, so the applications are unaffected (`BM.isSupNonexpansive`, `BM.isInfNonexpansive`). |
| Ex 3.2.3, p. 107 | `σ` is `q`-greedy for `(ℝ^G, 𝕊)` iff `σ(x) ∈ argmax_{a ∈ Γ(x)} q(x, a)` for all `x ∈ X`. | "If" holds (`FiniteMDP.exercise_3_2_3`). "Only if" holds only at states `x'` reachable from some feasible pair (`P(x, a, x') > 0`), and only for `β > 0` (`FiniteMDP.exercise_3_2_3_converse`): `S_σ q` sees `q(x', σ(x'))` only through `βP(x, a, x')`. Counterexample: two states, all transitions to state `false`, `β = 1/2`, `q(true, true) = 1` and `q = 0` otherwise. The policy choosing `false` everywhere is `q`-greedy but does not maximize `q(true, ·)` (`exercise_3_2_3_converse_fails`). Exercise 3.2.4, the form (3.7) of the Bellman operator, holds for every `q` all the same (`FiniteMDP.exercise_3_2_4`). |
| §3.2.4.1, p. 117 | The belief state `π` takes values in `X = (0, 1)`. | `(0, 1)` is not invariant under (3.30) when the supports of `f₀` and `f₁` differ. With `f₀ = 𝟙_{[0, 1]}` and `f₁ = 2 · 𝟙_{[0, 1/2]}`, every `π ∈ (0, 1)` and `z ∈ (1/2, 1]` give `ψ(π, z) > 0` and `κ(π, z) = 0`, so beliefs jump to `0` with probability `(1 − π)/2` (`kappa_hits_zero`). The belief kernel is built on `[0, 1]` (`Belief`), where `e(0) = e(1) = 0 ≤ c`, so the endpoints lie in the certain exit region. |

## Hypotheses the book leaves implicit, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| Thms 3.1.7, 3.1.10, Lemma 3.1.9 (ii) | `V` is a (complete) metric space. | `V` must be nonempty for the conclusions (global stability needs a fixed point); `[Nonempty V]` is assumed. |
| Thm 3.1.5, Assumption 3.1.1 | Contraction modulus `β ∈ (0, 1)`. | Any `β ∈ [0, 1)` works in Theorem 3.1.5; the geometric rate is then reported with `max β (1/2) ∈ (0, 1)` (`ADP.VFIGeometric`). |
| Lemma A.5.21, p. 381 | Stated for `v, w ∈ V₀` with `TV₀ ⊂ V₀`. | Holds for all `v, w ∈ V_G` (`ADP.lemma_A_5_21`). |
| Ex 3.2.1, p. 106 | `X`, `A` countable; `bX` the bounded functions. | Proved for any state space with the discrete σ-algebra (every bounded function is then in `bX`). Countability is not used, and `A` may be arbitrary since only the sets `Γ(x)` need be finite (`CountableMDP.exercise_3_2_1`). |
| Prop 3.2.1, p. 108 | Under Assumption 1.3.1, the savings ADP is regular. | Regularity is Lemma 1.3.2 (i), proved by the book later (Lemma 6.1.1). `OptimalSavings.proposition_3_2_1` and `OptimalSavings.remark_3_2_1` take it as a hypothesis, as in Chapters 1 and 2. |
| Ex 3.2.7, p. 109 | A `v`-greedy policy exists for `v ∈ bcℝ₊`. | The selection is explicit: the largest maximizer `σ(w) = max argmax_{c ≤ w}`. It is Borel because `{w : σ(w) ≥ a}` is closed (a sequential compactness argument, `OptimalSavings.isClosed_le_greedyBM`), so no measurable selection theorem is needed. Continuity of `Tv` comes from writing the maximum over `c = tw`, `t ∈ [0, 1]` (`OptimalSavings.continuous_bellmanOp`). |
| Prop 3.2.5 | Global stability on `bX₊`. | Also proved on all of `bX` (`NoDiscountStopping.proposition_3_2_5_bX`). |
| Prop 3.2.10, proof, p. 121 | Splits on whether `c/L₀ + c/L₁ ≥ 1`. | Not needed: with `a = c/L₀` and `b = 1 − c/L₁`, the drift bound holds on the continuation region whether or not it is empty (`SeqAnalysis.assumption321`). |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| §3.1, §A.5.3.1 | Pospaces: Hausdorff spaces with a closed order. | `OrderClosedTopology` (which implies Hausdorff for a partial order). The supremum-norm topology of `bX` is the topology of the Banach lattice `BM X`. |
| (A.22) | Sup-nonexpansive for families `(v_α)`, `(w_α)`. | Paired families are encoded as sets of pairs `S ⊆ V × V`, and `sup_α d(v_α, w_α)` by any bound `c ≥ 0` (`IsSupNonexpansive`). |
| §3.1.4, (3.2) | `v_σ̄ = lim_n T_{σ₀} ⋯ T_{σₙ} v`. | `ADP.planComp σs n = T_{σ₀} ∘ ⋯ ∘ T_{σ_{n-1}}` and `ADP.planValue` is its limit. |
| Thm 3.2.9, §3.1.3 | min-OPI and min-HPI converge. | Defined with min-greedy selectors and decreasing convergence (`ADP.MinOPIConverges`, `ADP.MinHPIConverges`) and identified with the dual's OPI and HPI (`ADP.minOPIConverges_iff`, `ADP.minHPIConverges_iff`). |
| §3.2.3.2–3.2.3.3, (3.12)–(3.17) | Policies `σ : X → {0, 1}`; stopping times `τ_σ`; `ℙ_x`, `𝔼_x`. | Policies are measurable exit regions `E ⊇ Ē`. Probabilities are expressed through the killed kernel `K_E = 𝟙_{Eᶜ}P`: `ℙ_x{τ_E ≥ n} = (K_Eⁿ𝟙)(x)`, the identity derived in the proof of Lemma 3.2.6 (`NoDiscountStopping.surv`). Hence `𝔼_x τ̄ = ∑_{n ≥ 1} (K_Ēⁿ𝟙)(x)` in Assumption 3.2.1 (`NoDiscountStopping.Assumption321`). |
| (3.13), Lemmas 3.2.3–3.2.4 | `g_σ(x) = 𝔼_x[∑_{t < τ_σ} c(X_t) + e(X_{τ_σ})]`, a fixed point of `T_σ` by the Markov property. | `g_E = ∑ₜ K_Eᵗ h_E` with `h_E = 𝟙_E e + 𝟙_{Eᶜ}c` (`NoDiscountStopping.lossFn`, `NoDiscountStopping.lossFn_hasSum`), the limit of `T_Eⁿ 0`. It is bounded (`NoDiscountStopping.lemma_3_2_3`) and fixed by `T_E` (`NoDiscountStopping.lemma_3_2_4`). The identity with the path-space expectation is the strong Markov property, not formalised. |
| Lemma 3.2.12, p. 120 | `𝔼_{π₀}[τ] < 1/δ`, by Theorem A.3.9 for the martingale `(π_n)`. | Drift form: `(PW)(π) + δ ≤ W(π)` on `[a, b]` with `W(π) = 1 − π²` and `δ = a²(1 − b)²Δ` (`SeqAnalysis.lemma_3_2_12`). A general drift criterion then gives `∑_{n ≥ 1} ℙ_π{τ̄ ≥ n} ≤ ‖W‖/δ ≤ 1/δ` (`NoDiscountStopping.assumption321_of_drift`). The variance identity (3.32) and bound (3.33) are proved as stated (`SeqAnalysis.integral_P_sq`, `SeqAnalysis.variance_ge`). |
| Lemma 3.2.11 | `f₀`, `f₁` distinct: not equal almost everywhere. | `¬ f₀ =ᵐ[volume] f₁` (`SeqAnalysis.lemma_3_2_11`). |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Lemma 1.3.2, p. 42 | Existence of measurable greedy policies under a continuous density | Proved by the book in Chapter 6 (Lemma 6.1.1); used as a hypothesis in Proposition 3.2.1. |
| Thm A.3.9, p. 358 | Exit times of bounded martingales | Its use in Lemma 3.2.12 is replaced by the drift argument above; the martingale and optional-stopping theory is not formalised. |
| Lemma 3.2.4, (3.21) | The strong Markov property and shift operators | Probabilistic; the loss function is defined by its series, as described above. |
| Remark 3.2.2, p. 117 | Observations in a general measurable space with a σ-finite reference measure | The formalisation takes densities on `ℝ` with respect to Lebesgue measure, as the text does. |
| Figures, §3.3 | Chapter notes | Not mathematical claims. |
