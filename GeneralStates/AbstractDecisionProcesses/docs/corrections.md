# Corrections to the source

Places where a claim in Chapter 2 of Sargent and Stachurski, *Dynamic
Programming*, Volume 2, is imprecise as printed, relies on an unstated hypothesis, or
where the Lean statement departs from the printed one. In each case the Lean statement
proves the corrected or stated version and cites the original. Entries are recorded when
found and revised if formalisation shows the finding itself to be wrong.

No outright errors were found in Chapter 2.

## Hypotheses the book leaves implicit, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| §2.3.5.4, p. 93 | The LQ ADP `(𝒫, 𝕋)` with `𝕋` indexed by the stable control matrices. | An ADP needs a nonempty policy set, so the construction assumes that some stable `F` exists, i.e. that `(A, B)` is stabilisable (`LQProblem.adp` takes `hne : ∃ F, L.IsStable F`). The state space is also assumed nonempty (`[Nonempty K]`), which the spectral radius bounds use. |
| §2.3.2, p. 81 | The optimal savings ADP is regular. | Regularity is exactly Lemma 1.3.2 (i), the existence of `v`-greedy policies (`OptimalSavings.adp_regular_iff`), which the book proves later (Lemma 6.1.1, Theorem A.3.3). Optimality and convergence are proved given it (`OptimalSavings.adp_optimality`). The step from ADP-greedy to (1.49) needs no Lemma 1.3.2: a policy can be changed at a single wealth level (`OptimalSavings.adp_isGreedy_iff`). |
| Ex 2.1.1, p. 66 | Stated for a regular ADP. | Regularity is not needed when the Bellman equation is read as `v = ⋁_σ T_σ v` (2.3) (`ADP.isOptimal_iff_solvesBellman`). |
| Lemma 2.2.3, Ex 2.2.2, p. 71–73 | Stated for regular ADPs. | Both hold for order stable ADPs without regularity (`ADP.le_vstar_of_mem_VU`, `ADP.le_of_orderBounded`). |
| §2.2.1.1 | Algorithms use "a" greedy selector. | Every convergence result is proved for every greedy selector `g` (`ADP.IsSelector`), not for one chosen selector. |
| §2.1.2.1 | `v* = ⋁_σ v_σ` for a well-posed ADP. | Defined as the supremum of `V_Σ` (`ADP.IsValueFunction`), which needs no well-posedness hypothesis. |
| Ex 2.2.6 (ii)–(iii), p. 78 | Min-OPI and min-HPI converge iff max-OPI and max-HPI converge for the dual. | Immediate from Exercise 2.2.4 (v)–(vi), `W▿ = W^∂` and `H▿ = H^∂` for a common selector (`ADP.dual_opt_howard`), together with Exercise 2.2.4 (vii); part (i) is stated separately (`ADP.minVFIConverges_iff`). |
| §2.3.1, p. 80 | The firm ADP: the book notes that Theorem 2.2.8 could prove optimality, but refrains. | Proved: the firm ADP is regular, order stable, order bounded (with `u = (|s| + M)/(1 − β)`) and order continuous on the countably Dedekind complete `bX`, so Theorem 2.2.8 gives optimality and the convergence of VFI, OPI and HPI (`FirmProblem.adp_optimality`). |
| §2.3.4.1 | `ℋ`: kernels with `sup_x ∫ |z| η(x, dz) < ∞`. | Encoded as Markov kernels `X → ℝ` with each `η(x)` having integrable identity and a uniform first-moment bound (`DistValue`). Stochastic dominance `⊴` is checked against bounded increasing test functions (`FOSD`); monotone functions are measurable, so no measurability condition is needed. Antisymmetry, which makes `(ℋ, ⊴)` a poset, is proved via tails `μ(a, ∞)` (`FOSD.antisymm`). |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| Definition 2.1.4 | `T` defined by `Tv = ⋁_σ T_σ v` on `V_G`. | `Tv = T_σ v` for a chosen `v`-greedy `σ` (`ADP.bellman`), shown to be the supremum on `V_G` (`ADP.isBellmanValue_bellman`). The relation `ADP.IsBellmanValue v w` states "`w = ⋁_σ T_σ v`" wherever the supremum exists. |
| §2.2.3 | Min-objects (`T▿`, min-greedy, `v▿*`, …) and the min-results. | Defined directly and identified with the max-objects of the dual ADP `A^∂ = (V^∂, 𝕋)` (Exercise 2.2.4). Theorem 2.2.9 and Corollary 2.2.10 are proved by transport from Theorem 2.1.5 and Corollary 2.1.6. |
| Thm A.5.2 | Knaster–Tarski for chain complete posets. | Proved via Zorn's lemma applied to the set `{u | v ≼ u ≼ Su}`, with the upward and downward forms (`ChainComplete.exists_fixedPt_ge`, `ChainComplete.exists_fixedPt_le`). |
| (2.21)–(2.22) | `D_σ η` as the law of `r_σ(x) + βV` with `V ∼ (P_σ ⊗ η)(x)`. | `DDP.Dσ` is the kernel image of `x ↦ (x, (η ∘ P_σ)(x))` under `(x, v) ↦ r_σ(x) + βv`; `DDP.Dσ_apply` recovers the book's form pointwise. |
| Ex 2.3.11, p. 87 | `D_σ` is a `β`-contraction for `d̄₁(η, η') = sup_x W₁(η(x), η'(x))`. | Proved in test-function form (`DDP.lipschitz_contraction`) and for `W₁` defined as the supremum over `1`-Lipschitz test functions (`DDP.W1_contraction`). The contraction takes as a hypothesis that the defining sets are bounded above, which holds for measures with finite first moment but is not formalised. |
| Lemma 2.3.5, (2.35) | `T_F` is globally stable on `𝒫` and `P_F = ∑ₜ …`. | Convergence `T_Fⁿ P → P_F` is entrywise, which is the topology of the finite-dimensional matrix space (`LQProblem.IsStable.tendsto_TF_iterate`, `LQProblem.IsStable.globallyStable`). |
| §2.3.5.8, p. 95 | Optimality of `F(P*)` under controllability and observability (Lemma 2.3.4). | Stated given a fixed point `P* ∈ 𝒫_S` of the Riccati map, which is what Lemma 2.3.4 supplies (`LQProblem.optimality`): (a) `P*` is the least element of `𝒫_Σ`, (b) `T▿P* = P*`, (c) a policy is min-optimal iff it is `P*`-min-greedy, (2.38) `xᵀP*x = min_u {…}`, and `F(P*)` is min-optimal. |
| Example 2.3.1, p. 92 | `F = −0.6` is better than `F = −0.9`. | Compared through the scalar lifetime cost `c x₀²` with `c = (F² + 1)/(1 − (A + BF)²)`: `34/21 < 181/99` (`LQProblem.scalar_compare`). |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Lemma 2.3.4, p. 95 | Existence of a stabilising solution of the Riccati equation under controllability and observability | Cited by the book from Bertsekas; used as a hypothesis in `LQProblem.optimality`. |
| §2.3.4.2–2.3.4.3 | Completeness of `(ℋ, d̄₁)`; well-posedness and order stability of the distributional ADP | Needs completeness of the Wasserstein space of measures on `ℝ` with finite first moment, which is not in Mathlib. The contraction itself (Exercise 2.3.11) is proved. |
| Ex 2.3.12 | The law `η̂(x, ·)` of the random return `Z_σ(x) = ∑ₜ βᵗ r_σ(Xₜ)` lies in `ℋ` and is the fixed point `η_σ` of `D_σ` | Needs the Markov chain on path space and the law of an infinite random sum; the operator `D_σ` and its contraction property are formalised, the probabilistic identification is not. |
| §2.3.4.4 | Failure of regularity for distributional DP | An informal discussion with no stated result. |
| Figures, §2.4 | Plots and chapter notes | Not mathematical claims. |
