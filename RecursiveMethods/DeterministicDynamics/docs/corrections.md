# Corrections and conventions

Places where a Lean statement differs from the book: a hypothesis made explicit, a claim
corrected, or a convention chosen. Corrections to the Chapter 3–5 results carried over here are in
the [Chapter 5 corrections](../../DeterministicApplications/docs/corrections.md) and the
[Chapter 4 corrections](../../DeterministicDP/docs/corrections.md).

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 6.9, proof, p. 154 | "For `x₀ = x̄` the only solution is `x_t = x̄`, so `φ(x₁, x̄) = 0` iff `x₁ = x̄`. Hence `B` has full rank." | An isolated zero does not make a derivative nonsingular, so this step does not go through. It does go through when the second-order form `½u′F_xx u + u′F_xy v + ½v′F_yy v` at `(x̄, x̄)` is negative definite (`hneg` in `theorem_6_9`). Then a stable vector `(z₁, 0)` gives a solution of the linearized Euler equation with `d₀ = 0` and `d_t → 0`. Telescoping `2βᵗq(d_t, d_{t+1}) = βᵗg_t − βᵗ⁺¹g_{t+1}` forces `d = 0` (`hom_euler_eq_zero`, `stable_real_inr_zero`). Strict concavity of `F` alone gives only semidefiniteness. |
| Lemma 6.2, p. 140 | `L` satisfies (a) `L(x) ≤ 0`, zero only at `x̄`, and (b) `L[g(x)] ≥ L(x)`, equality only at `x̄`. | (a) is not needed: on a compact `X` a continuous `L` is bounded, and (b) alone gives convergence (`lemma_6_2`). The book's form is `lemma_6_2_book`. |
| Ex 6.4, p. 143 | Condition (8) holds if `bd − (1 + β)²c²/4 ≥ 0`. | (8) holds iff `βbd ≥ (1 + β)²c²/4` (`ex_6_4`). The book's condition is not sufficient (`ex_6_4_book_condition_fails`). |
| Ex 6.4, p. 143 | `x̄` is the unique stationary point. | Iff `(1 + β)c + d + βb ≠ 0` (`ex_6_4_stationary`). That can fail for a strictly concave `F`: `b = −4`, `c = 104/101`, `d = −1`, `β = 1/100` (`ex_6_4_not_unique`). It cannot fail under the strict form of the corrected condition (`ex_6_4_unique_of_eight`). |
| Ex 6.7a, p. 156 | The problem satisfies Assumptions 4.3–4.4 and 4.7–4.9. | Assumption 4.7 fails: `F(k, 1) = 0` for every `k`, so `F` is affine along the edge `y = 1` (`cd_not_strict`). Every `k₀` still has exactly one optimal plan (`ex_6_7a`). Maximizers are interior and unique, because `V` is strictly increasing and has bounded slopes near `1` (`CDValue.argmax_pos`, `argmax_lt_one`, `argmax_unique`). |
| Ex 6.7f, p. 158 | `(0.29, 0.18)` is an optimal two-cycle for `β = 0.1`, `α = 0.8`, `θ = 0.75`. | It is not a two-cycle. A two-cycle needs `x(1 − x)³ = y(1 − y)³` (`cycle_q_eq`). On `[0.28, 0.30] × [0.17, 0.19]` the left side is at least `0.1029` and the right side at most `0.101` (`ex_6_7f_book_box`). The true optimal two-cycle has `x ∈ [0.483, 0.485]` and `y ∈ (0.087, 0.088)` (`ex_6_7f`, by the intermediate value theorem on certified rational brackets). |
| Ex 6.7g, p. 158 | Linearize around `(0.29, 0.18)`. | Linearized around the true cycle, the two-step map has determinant `β⁻² = 100` and trace above `101`. So one root lies in `(0, 1)` and one above `1`: the cycle is saddle-path stable (`ex_6_7g`). |
| Ex 6.9a, p. 160 | A unique continuous bounded solution `v` on `ℝ₊`. | Every solution on `ℝ₊` is unbounded: `v(x) ≥ S(xφ(0)) + θ(1 − δ)x + βv(0)` (`crs_unbounded`). On `[0, K]` with `Γ(x) = [0, min{αx, K}]` there is a unique bounded continuous solution (`ex_6_9a`). |
| Ex 6.9a, p. 160 | `v` strictly concave (via Theorem 4.8). | Assumption 4.7 fails on the ray `y = αx`, where `φ(y/x) = 0` and `F` is linear. `v` is still strictly concave (`CRSValue.strictConcaveOn`). Optimal choices stay below `αx` because `φ′ → −∞` (`argmax_lt`), and the perspective `xφ(y/x)` is strictly concave across rays (`crsQ_strict`). |
| Ex 6.9c, p. 160 | There is a unique positive stationary point `x̄`. | An interior stationary point satisfies `S′(x̄φ(1))[βφ(1) + (1 − β)φ′(1)] = θ(1 − β(1 − δ))` (`stationary_eq`). So there is at most one (`stationary_unique`), and **none** when `βφ(1) + (1 − β)φ′(1) ≤ 0` (`no_stationary`). That happens under all the exercise's hypotheses with `φ(u) = √(2 − u)`, `S(q) = 1 − e^{−q}`, `α = 2`, `β = 1/4` (`ex_6_9c_counterexample`). |

## Theorems the book states without proof

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 6.1, p. 138 | Boldrin and Montrucchio: every `C²` map `g` of a compact `X ⊆ ℝ` is an optimal policy. | Proved for `X` a compact interval (convexity of `X` is part of Assumption 4.3). The return is `F(x, y) = −Kx²/2 + y²/4 − (y − g(x))²/2` with `β = 1/(2K)`, and `v(x) = −Kx²/2` (`theorem_6_1`). The `C²` hypothesis is used through bounds on `g′` and `g″`. |
| Theorem 6.5, p. 147 | Cited (Scheinkman 1973), with `h` `C¹` near `x̄` and `I − A` nonsingular. | Only differentiability of `h` at `x̄` is used (`theorem_6_5`). |
| Theorem 6.6, p. 147 | Cited: a `C¹` map `φ` whose zero set near `x̄` is the stable manifold, with `Dφ(x̄)` of rank `n − m`. | Proved by a Lyapunov–Perron fixed point in weighted sequence spaces (`theorem_6_6`). `h` need only be strictly differentiable at `x̄`, and `A` may be singular. `φ` is differentiable at `x̄` with derivative the projection onto the unstable subspace, of rank `n − m`. Continuous differentiability of `φ` away from `x̄` is not proved. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 6.9, p. 153 | Assumptions 4.3–4.4 and 4.7–4.9; `F` twice continuously differentiable near `(x̄, x̄)`. | `F` strictly concave on the convex graph of `Γ` and bounded there, with bounded states (for transversality). `x̄` is interior. The gradient `(F_x, F_y)` is strictly differentiable at `(x̄, x̄)` with second derivatives `F_xx, F_xy, F_yy`, and the second-order form is negative definite (see above). |
| Theorem 6.8, p. 151 | `F` strictly concave quadratic; `F′_xy + F_yy + βF_xx + βF_xy` and `F_xy` nonsingular; `A` has `l` roots inside the unit circle. | As stated, with roots counted with multiplicity (`theorem_6_8`). Strict concavity is used through the negative definiteness it gives the quadratic part (`lqQ_neg`, `exists_lqQ_bound`). |
| Ex 6.8, p. 159 | The firm's problem on `ℝ₊`. | On the compact `[0, K]` of Exercise 5.9b, with `K` beyond the steady state: `βpf′(K) < c′(δK)(1 − β(1 − δ))` (`FirmDyn`). Then `g(0) > 0` and `g(K) < K` (`fpol_zero_pos`, `fpol_K_lt`). |
| Ex 6.9b, p. 160 | "Use the envelope condition to prove that `g` is increasing." | `g` is nondecreasing (`argmax_mono`). `z ↦ F(z, y) − F(z, y′)` is strictly increasing for `y′ < y` (strictly increasing differences), so `g` cannot fall. |
| Ex 6.9e, p. 160 | "Use (b)–(d) to prove convergence." | Theorem 6.9 does not apply as stated, because Assumption 4.7 fails. `ex_6_9e` takes the local stability of `x̄` as a hypothesis, and from it and (b)–(c) derives monotone convergence from every `x₀ ∈ (0, K)`. Part (d) is proved for the linearization: one root in `(0, 1)` (`ex_6_9d`). |
| Ex 6.10a, p. 161 | `x̄` is stationary iff `R = W₂[x̄(1 − R), z̄]` and `z̄ = W[x̄(1 − R), z̄]`. | Single good with price `1`. The "if" direction needs `R < 1` and `W₁ ≥ 0` at the point (`ex_6_10a_if`). The "only if" direction needs `x̄ > 0` and `W₁ ≠ 0` there (`ex_6_10a_only_if`). |
| Ex 6.10b, e, f, p. 161 | "Provide sufficient conditions…"; "Can you prove global stability…?" | (b): `z̄` is determined by `x̄` (`exists_unique_fixed_z`), so the pair reduces to one equation in `x̄`. (c) and (d) are proved (`ex_6_10c_eq`, `ex_6_10c_ne`, `ex_6_10d`). (e) and (f) are open-ended and not formalized. |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Chapters 3–5 results | Cited. | The modules of the Chapter 5 project that Chapter 6 uses are carried over, so the project is self-contained. |
| Theorems 6.3–6.4 | Proofs through the Jordan form. | The Jordan form is not in Mathlib. `Aᵗz → 0` iff `z` lies in the sum of the generalized eigenspaces of the roots inside the unit circle (`tendsto_iff_mem_stable`). Theorem 6.4 is stated for `A = B⁻¹ΛB` with `Λ` upper triangular, which includes the Jordan form (`theorem_6_4`). |
| Characteristic roots | Roots of `det(A − λI)`. | Roots of the characteristic polynomial mapped to `ℂ`, with multiplicity (`hasEigenvalue_cplxEnd_iff`). "Real roots" is a conclusion (`quadRoot`). |
| Ex 6.2, Ex 6.7 | `U(c) = c^α`, `f(z) = z^θ`. | The return is `k^a(1 − y)^b` with `a = αθ`, `b = α(1 − θ)` (`cdF`). Ex 6.2 is `ex_6_2`, for every concave solution of the functional equation, and `ex_6_2_fixed`, for the bounded continuous fixed point. |
| Growth example, pp. 154–155 | The roots `λ₁ < 1 < β⁻¹ < λ₂`, and `g′(k*) = λ₁`. | The roots are `growth_roots`, and global monotone convergence is `prop_6_1`. Differentiability of the policy at `k*` is not formalized. |
