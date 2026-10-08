# Corrections to the source

Places where a claim in Chapter 10 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false as printed, relies on an unstated hypothesis, or
where the Lean statement departs from the printed one. In each case the Lean
statement proves the corrected or stated version and cites the original. Entries
are recorded when found and revised if formalisation shows the finding itself to be
wrong.

## Errors

| Where | Book says | Correction |
| --- | --- | --- |
| Lemma 10.1.2 (iv), p. 311 | `λ` is an eigenvalue of `A` **if and only if** `e^λ` is an eigenvalue of `e^A`. | Only "only if" holds. For `A = (0, −2π; 2π, 0)`, `e^A = I` has eigenvalue `1 = e^0`, but `0` is not an eigenvalue of `A` (`exp_eigenvalue_converse_false_real`; a `1 × 1` complex example is `exp_eigenvalue_converse_false`). The correct converse is the spectral mapping theorem `σ(e^A) = e^{σ(A)}` (`spectrum_complexify_exp`): if `μ` is an eigenvalue of `e^A` then `μ = e^λ` for some eigenvalue `λ` of `A`, and `λ` is determined only up to `2πiℤ`. |
| §10.2.2.1, p. 334 | "two finite sets A and X, called the state and action spaces respectively" | Reversed: `X` is the state space and `A` the action space, as everywhere else in the section. |
| §10.2.4, p. 339 | The optimal policy has "a reservation wage of around 12". | Figures 10.4 and 10.5 put the reservation wage between about 1.1 and 1.35, with wage offers in `[0.5, 4]`; "12" is presumably "1.2". Numerical, not formalised. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Lemma 10.1.1 and (10.5), p. 310 | Right-continuity of `G` at `0`. | The hypotheses (a)–(c) concern `t > 0` only, so they determine `G(t) = e^{−θt}` for `t > 0` (`eq_exp_of_memoryless`) but not `G(0)`. `G(0) = 1` follows once `G` is right-continuous at `0`, as a counter CDF is. |
| Lemma 10.1.4, Thm 10.1.5, p. 316 | `X` nonempty (`n ≥ 1`). | `[Nonempty X]`. With `X = ∅` the spectrum is empty and Lean's `sSup ∅ = 0` gives `s(A) = 0`, so in Theorem 10.1.5 (i) fails while (ii)–(iv) hold. |
| Prop 10.1.8, p. 322 | Differentiability on `ℝ₊` means one-sided at `0`. | The derivatives are `HasDerivWithinAt … (Ici 0)`, entrywise. |
| Prop 10.2.1, p. 329 | Positivity of `(K_t)` is needed only for (iii) and (iv). | (i) and (ii) assume only `s(A) < 0`; (iii) and (iv) add `e^{tA} ≥ 0` for `t ≥ 0`. |
| Thm 10.2.4, p. 337 | `A` finite; `X` nonempty. | `[Finite A]`, as the definition of a continuous-time MDP requires, and `[Nonempty X]`. |
| Algorithm 10.2, p. 336 | A fixed rule for choosing "a `v_k`-greedy policy". | The stopping test `σₖ₊₁ = σₖ` needs a deterministic choice: if ties are broken arbitrarily the policies can alternate between tied optimal policies forever after the values have converged. With a fixed choice (`ADP.greedy`), the values stop increasing after finitely many steps, the next policy repeats, and it is optimal (`CTMDP.optimality`). |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| Lemma 10.1.2, p. 312 | Derivatives and integrals of matrix-valued functions are taken element by element. | Derivative statements are made for each entry `(x, y)` (`hasDerivAt_exp_smul_entry`, `kolmogorov_backward`, …); the Mathlib operator-norm derivative is also given where it is used (`hasDerivAt_exp_smul`). |
| Lemma 10.1.2 (iii), p. 311 | `m` a positive integer. | Every `m ∈ ℕ`. |
| Prop 10.1.9, p. 324; §10.1.4.2 | `λ : X → (0, ∞)`. | The analytic part (`eq_exp_of_integrated`) holds for every `λ : X → ℝ`. |
| Ex 10.2.1, p. 332 | Random variables `η(s, t)` along the chain. | Stated pathwise for any path with locally integrable `δ(X_τ)` (`pathDiscount_properties`). |
| Prop 10.2.3, (10.44), p. 333 | `v(x) = E_x ∫₀^∞ e^{−δt}h(X_t) dt`, rewritten by Fubini as `∫₀^∞ e^{−tδ}(P_th)(x) dt`. | The semigroup form `∫₀^∞ e^{t(Q − δI)}h dt` is the definition (`lifetimeValue`); `CTMDP.vσ_eq_integral` rewrites it as `∫₀^∞ e^{−δt}P^σ_t r_σ dt`. |
| §10.2.2.1, p. 334 | `r` on `G`, `Q` on `G × X`. | `r` and `Q` on `X × A`; the intensity conditions are imposed only on `G`, and values off `G` never enter `Q_σ` or `r_σ` for feasible `σ`. |
| §10.2.4, p. 338 | Firing rate `α > 0` and offer rate `κ`. | `α, κ ≥ 0` suffice. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| §10.1.4.1, (10.30), p. 323 | Continuous-time Markov chains on the path space `C(ℝ₊, X)` | Probabilistic: the library works with the semigroups `P_t = e^{tQ}` that determine the law of the chain. |
| Algorithm 10.1, Prop 10.1.9 (probabilistic part), Lemma 10.1.10, pp. 324–325 | The jump chain construction and the derivation of (10.32) from it | Probabilistic; the analytic step from (10.32) to `P_t = e^{tQ}` is formalised (`eq_exp_of_integrated`). |
| §10.1.3.2, p. 320 | The `o(h)` interpretation of `Q` | The precise statement (10.28) is formalised (`exp_smul_entry_isLittleO`). |
| Prop 10.2.2, (10.42)–(10.43), p. 331 | The Feynman–Kac semigroup of a chain is a positive `C₀`-semigroup | Requires the Markov property of the chain on path space. |
| Example 10.1.2, Figures 10.1–10.5, Ex 10.2.4, §10.3 | Interpretation, simulation, the numerical job-search policy and its comparative statics, literature | Not applicable. |
