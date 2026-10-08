# Corrections to the source

Places where a claim in Chapter 1 of Sargent and Stachurski, *Dynamic
Programming*, Volume 2, is imprecise as printed, relies on an unstated hypothesis, or
where the Lean statement departs from the printed one. In each case the Lean statement
proves the corrected or stated version and cites the original. Entries are recorded when
found and revised if formalisation shows the finding itself to be wrong.

## Errors

| Where | Book says | Correction |
| --- | --- | --- |
| (1.29), p. 30 | Uniformize with `m = max_{x, a ∈ Γ(x)} |Q(x, a, x)|`. | `m` must be positive, and it is zero when every diagonal entry on `G` vanishes (then `Q = 0` on `G`, and (1.29) divides by zero). Any `m > 0` with `|Q(x, a, x)| ≤ m` on `G` works, and Exercises 1.2.5–1.2.6 hold for every such `m` (`CTMDP.uniformize`). |
| §1.2.2.4, p. 32 | `m = λ + μ̄`, the largest `|Q(x, a, x)|`. | That is the maximum only when the capacity is `N ≥ 2`, so that an interior queue length exists (`abs_queueQ_diag_interior`). For `N = 1` the maximum is `max(λ, μ̄)` (`abs_queueQ_diag_capacity_one`). `λ + μ̄` always bounds the diagonal (`abs_queueQ_diag_le`), so it remains a valid rate under the reading above. |

## Hypotheses the book leaves implicit, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| §1.2.1.1 | `A` finite. | Only the feasible sets `Γ(x)` need be finite; the policy set is then finite (`FiniteMDP.finite_policy`). Cash management uses `A = ℤ`. |
| Thm 1.2.2, p. 24 | "Converge … when the tolerance is zero". | Stated as convergence of the generated sequences: `Tᵏv → v*` and the OPI sequence `→ v*` uniformly from every `v`, for every `m ≥ 1`; HPI values reach `v*` after finitely many steps and every later policy is optimal. OPI from an arbitrary start is reduced to the monotone case by subtracting a constant, using `T_σ(v − c) = T_σ v − βc`. |
| Assumption 1.3.1 | `φ` has a continuous density. | The density is used only for Lemma 1.3.2. The results here assume only that `φ` is a probability measure on `ℝ₊`. |
| §1.3.2.2, p. 42 | DP results (i)–(iii) under Assumption 1.3.1. | They rest on Lemma 1.3.2 (i), the existence of measurable greedy policies, which the book proves later (Lemma 6.1.1, Theorem A.3.3). Here (i)–(iii) are proved given that conclusion (`OptimalSavings.dp_results`). The step "DP greedy ⟹ (1.49)" in §2.3.2 needs no Lemma 1.3.2: a policy can be changed at one wealth level (`OptimalSavings.isGreedy_iff`). |
| (1.53)–(1.55), p. 44 | `σ(w) = ηw` is the optimal policy. | The book verifies the Bellman equation (1.54); optimality in the unbounded CRRA case is outside the bounded theory of this chapter. Formalised: for `w > 0`, `η^{−γ}u(w) = max_{0 < c < w} {u(c) + βη^{−γ}u(R(w − c))}`, attained at `c = ηw`, under `βR^{1−γ} ∈ (0, 1)` and `R > 0` (`crra_value`, `crra_bellman_le`). Consumption is kept positive because `u(0) = −∞` for `γ > 1`. |
| Ex 1.3.3, p. 43 | `m : ℝ₊ → {−∞} ∪ ℝ`. | A real bound suffices: `u(w)/(1 − βR^{1−γ})` for `γ < 1` and `0` for `γ > 1`. Every partial sum of lifetime utility is bounded (`crra_lifetime_bound`). |
| §1.1.3.4, p. 15 | For `γ > 0`, `e_γ(Z) ≤ E Z`. | Assumes `Z` and `exp(−γZ)` integrable (`entropicCE_le_integral`). |
| §1.1.3.4, p. 16 | VaR increases with downside risk. | Stated as monotonicity: if `Z ≤ Z'` then `VaR_α(Z') ≤ VaR_α(Z)`, provided the sets defining the infima are nonempty and bounded below (`valueAtRisk_anti`). |
| §1.4.2 | State space `X = (0, 1)`. | Bayes updating and the Bellman operator are stated for `π ∈ [0, 1]`. |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| Ex 1.1.1, p. 4 | `V_t = v(X_t)` satisfies `V_t = π_t + βE_t V_{t+1}` (1.1). | The functional equation (1.2), `v = π + βPv`, and the Neumann series (1.3). The step from (1.2) to (1.1) is the Markov property `E_t v(X_{t+1}) = (Pv)(X_t)`, not formalised. |
| (1.5) | `T_σ v = σs + (1 − σ)(π + βPv)` with `σ ∈ {0, 1}`. | Policies are measurable `X → Bool`; `FirmProblem.Tσ_eq` recovers the book's form. |
| §1.1.3.6, p. 18 | Is `v_σ` well defined by (1.14)? The book leaves this to later chapters. | It is, for every aggregator `K` that is order preserving and shifts constants (`K(v + c) = Kv + c`), and then all of Theorem 1.1.1 holds (`FirmProblem.riskAdjusted_optimality`). The entropic aggregator qualifies (`isShiftMonotone_entropicOp`). The mean-variance aggregator does not: it is not order preserving (`meanVariance_not_monotone`), so the order-based theory does not cover it. |
| Lemma 1.3.1, (1.41), (1.45) | `v_σ` equals the expected discounted sum along the wealth process. | The fixed point and the Neumann series `∑ (βP_σ)ᵗr_σ` (1.44); the identification with the expectation over paths is probabilistic and not formalised. |
| (1.28) | `v_σ = ∫₀^∞ e^{t(Q_σ − δI)}r_σ dt = (δI − Q_σ)⁻¹r_σ`. | The resolvent form `(δI − Q_σ)⁻¹r_σ` is the definition (`CTMDP.vσ`). The integral form is proved in Volume 1, §10.2 (the `ContinuousTime` project). |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Lemma 1.3.2, p. 42 | Continuity of the objective, existence of measurable greedy policies, continuity of `Tv` | Proved in the book in Chapter 6 (Lemma 6.1.1) and Appendix A (Theorem A.3.3, Berge); used here as a hypothesis. |
| Thm 1.4.1, p. 52 | Optimality for sequential analysis | No discounting; the book proves it as Theorem 3.2.9 in Chapter 3. |
| §1.1.1.5, §1.1.3.1–1.1.3.2, §1.1.3.5, §1.2.3.1, (1.10)–(1.13), (1.34)–(1.35) | Random payoffs `Z_σ`, nonstationary and randomised policies, non-recursive criteria | Probabilistic or informal discussion; nonstationary policies are treated in Chapter 3. |
| §1.1.3.4, p. 15–16 | Cumulant expansion of `e_γ`; the KL variational formula | A formal series; the variational formula is treated in Chapter 7. |
| §1.1.2.1–1.1.2.2 | State-dependent discounting; unbounded rewards and `L¹(ψ)` | Deferred by the book to §4.2.1 and §7.2.2. |
| §1.2.3.3, (1.37)–(1.39) | Ambiguity | Informal here; treated in §7.3.3. |
| §1.3.3 | Epstein–Zin preferences | Definitions and an informal remark on non-contractivity; treated in Chapter 5. |
| Algorithms 1.1–1.3, Figures 1.1–1.21, §1.5 | Tolerances, simulations, computations, literature | Not applicable. |
