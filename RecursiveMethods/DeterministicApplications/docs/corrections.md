# Corrections and conventions

Places where a Lean statement differs from the book (or from the solutions manual, where its
argument was followed): a hypothesis made explicit, a claim corrected, or a convention chosen.
Corrections to Chapter 4 results carried over here are in the
[Chapter 4 corrections](../../DeterministicDP/docs/corrections.md).

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Ex 5.1c, p. 104 | Under (U1)–(U4) and (T1)–(T4), the hypotheses of Theorem 4.8 hold. | False when `f` is only weakly concave, as (T4) allows: Assumption 4.7 can fail (`ex_5_1c_weak_counterexample`). The conclusions still hold. `v` is strictly concave and the policy is a continuous function (`ex_5_1c_weak`). If `v` were affine on a chord, the optimal consumptions at its ends would agree, so `v(x) − v(x′) = βⁿ(v(bₙ) − v(b′ₙ))` for all `n`, which contradicts strict monotonicity (`growth_strictConcave`). |
| Ex 5.7a, p. 110 | (Manual) `(aₙ)` is bounded iff `λ < r`. | Bounded iff `λ ≤ r` (`ex_5_7a_bounded_iff`). At `λ = r` the tangent to the concave `φ` at `1 + λ` bounds `aₙ` by `−φ′(1 + λ)(1 + λ)` (`slope_bound`). |
| Ex 5.8a, p. 112 | The functional equation has a unique continuous solution. | Returns grow with `k`, so uniqueness holds within a growth class: exactly one continuous `v` with `|v(k)| ≤ C(1 + k)` (`ex_5_8a`, a weighted contraction). Every `Ak^{ασ}` with `ασ < 1` lies in the class. |
| Ex 5.10b, p. 114 | Every solution of the functional equation is homogeneous of degree one. | Every solution with `|v(k)| ≤ Ck` is `v*`, hence homogeneous (`ex_5_10b`). Some growth bound is needed: Theorem 4.3 is what rules out other solutions. |
| Ex 5.11b, p. 115 | (Manual) `u(c) = inf_t c_t` shows that `u(cⁿ) → u(c)` can fail. | `inf_t c_t` is not bounded on `L`, so it is not in `S = C(L)`. `u(c) = min{1, dist(c, eventually-zero sequences)}` is in `S`, with `u(1) = 1` and `u(1ⁿ) = 0` (`ex_5_11b_counterexample`). |
| Ex 5.11e, p. 116 | (Manual) The MRS between `c_{it}` and `c_{j,t+k}` has a single factor `W_z`. | Raising `c_{it}` changes utility at the rate `[∏_{s<t} W_z(c_s, u_W(ₛ₊₁c))] · W_{x_i}(c_t, u_W(ₜ₊₁c))`, so the MRS carries the product `∏_{s=t}^{t+k−1} W_z` (`ex_5_11e`). |
| Ex 5.12d, p. 117 | `W̃(C, a) = h(W[C, h⁻¹(a)])` is an aggregator giving the same demands. | It gives the value `h ∘ v` and the same demands (`ex_5_12d`), but it need not be an aggregator. `W(C, z) = z/2` and `h(x) = x/(1 + x)` give `W̃(a) = a/(2 − a)`, which violates (W3) (`ex_5_12d_not_aggregator`). |
| Ex 5.12a, p. 117 | Relate the sequence problem to (2), as Theorems 4.2–4.5 do. | `v` is the supremum function (`ex_5_12a`), and plans satisfying (2) are optimal (`ex_5_12a_optimal`). Optimal plans need not exist: when the policy's consumption path is unbounded, it is not in `L`, and only truncated plans approach the supremum. |
| §5.16, p. 124 | `q = (B − P)/(B − A)` and `(Tf)(A, B) = sup_P …` on `D = {0 ≤ A ≤ B ≤ 1}`. | The formula divides by `B − A`, which is zero on the diagonal of `D`. `T` is parametrized by the probability of sale `q ∈ [0, 1]`, with `P = (1 − q)B + qA` (`priceQ`, `sellerT`). This is the book's operator off the diagonal, and it is continuous on all of `D`. |
| Ex 5.17b, p. 127 | `m₁ > 0` is well defined by `U′(I + m₁) = RβU′(I)`. | Not under the book's hypotheses. `U(c) = c − e^{−c}` with `β = 1/2`, `R = 1`, `I = 1` has `U′ > 1 > RβU′(I)` (`ex_5_17b_m1_fails`). The induction can also stop at a later stage when `U′` is bounded below. `CSHyp` assumes `U′(c) → 0`, under which every stage is well defined and `m_n → ∞` (`ex_5_17f`). |
| Ex 5.17g, p. 128 | Hint: `x_n ≤ Rⁿ(x₀ + W)` with `W = RI/(R − 1)`. | False for `R < 1`, where `W < 0`. With `R = 1/2`, `I = 1`, `x₀ = 0`, the plan `x₁ = 1/2` is feasible, but `R(x₀ + W) = −1/2` (`ex_5_17g_hint_fails`). At `R = 1`, `W` is undefined. The proof of `v = v*` does not use the hint. |
| Ex 5.17h, p. 128 | `0 ≤ g(x′) − g(x) < x′ − x` for `0 ≤ x < x′`. | The right inequality holds for `R ≤ 1` (`ex_5_17h_slope_le_one`) but can fail when `R > 1`. With `R = 2`, `β = 9/20`, `I = 1`, take `U′` almost flat on `[0, 2]` and steep beyond. Then `x = 1 + 55/499 < x′ = 11/10 + 55/498` but `g(x′) − g(x) = 1/5 > x′ − x` (`ex_5_17h_counterexample`, `ex_5_17h_book_bound_fails`). What holds in general is `0 ≤ g(x′) − g(x) < R(x′ − x)`, i.e. consumption rises strictly with wealth. Equality on the left holds only if `g(x) = g(x′) = 0` (`ex_5_17h_slope`). |

## Proofs that differ from the solutions manual

| Where | Manual | Lean |
| --- | --- | --- |
| Ex 5.1e, p. 105 | Iterate `T_{β′}` from `v(·, β)` and compare first-order conditions. | That step needs interior solutions and differentiability. The proof here is a lattice (Topkis) argument and needs neither: `β′v(·, β′) − βv(·, β)` is nondecreasing (`discounted_value_monotone`), so the policy rises with `β` (`ex_5_1e`). |
| Ex 5.6a–c, pp. 108–109 | Optimal output exceeds the current-profit maximizer, by a first-order condition. | The first-order condition needs `v` differentiable, which Theorem 4.11 cannot supply here: Assumption 4.7 fails (`lbd_not_a47`). The proof uses only the convexity of `γ` (`lbd_policy_exceeds`). |
| Ex 5.17, pp. 126–128 | Construct `v` interval by interval: `[0, m₁]`, then `(m_n, m_{n+1}]`, with `h` from (2) and `g = h⁻¹`. | Every optimal plan is written down at once. A multiplier `μ` sets consumption `c_t = max{I, (U′)⁻¹(μ/(Rβ)ᵗ)}`. Summation by parts with `p_t = βᵗU′(c_t)` gives optimality, uniqueness and the supergradient inequality (`value_bound`, `abel_bound`). Differentiability then follows from the supergradient being continuous. The book's `m₁`, `h`, `m_n`, (2), (4) and (5) are recovered as global objects (`ex_5_17b`–`ex_5_17f`). |

## Hypotheses weakened or made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Ex 5.1d, p. 104 | `v′(x) = U′(f(x) − g(x))f′(x)` when `0 < g(x) < f(x)`. | Only `g(x) < f(x)` is used, with `U` differentiable at `f(x) − g(x)` and `f` at `x` (`ex_5_1d`). |
| Ex 5.3a, p. 105 | Which results of Section 5.1 hold with `U(c) = c`? | Exercise 5.1a–b applies and `v` is concave (`ex_5_3a`). With `f` strictly concave, Assumption 4.7 still holds (`ex_5_3a_strict`). The interior result fails: below `k*` nothing is consumed (`ex_5_3a_corner`). |
| §5.6, p. 108 | (Manual) Output is bounded by `q̄`, since output above `q̄` never pays. | That argument ignores the learning gain from extra output. `Γ(Q) = [Q, Q + q̄]` is an assumption of the model here (`lbdΓ`). |
| Ex 5.4, p. 107 | The renormalized problem is that of Section 5.1. | When `β̃ = β(1 + λ)^γ < 1` and `f̃` satisfies (T2) (`ex_5_4`). |
| Ex 5.5, p. 107 | "Under what assumptions about `h` is there a simple rule?" | Answered by sufficient conditions. Without replanting, cut at the first `t` with `h(k_t)/k_t ≤ 1 + r`: optimal when trees grow and `h(k)/k` does not rise with size (`ex_5_5a`). With replanting, cut when `βh(k) − k ≤ (1 − β)L*`: optimal when `βh(k) − k` falls past some size (`ex_5_5b`). |
| Ex 5.8b, p. 112 | `U(c) = c^σ/σ`, `σ < 1`. | `0 < σ < 1` (`ex_5_8b`). For `σ < 0`, `U(0) = −∞`, returns are unbounded below and part (a) does not apply; that case is not covered. |
| Ex 5.9a, p. 112 | The firm's investment problem. | No differentiability is needed: if `y*` maximizes `βG(y) − qy`, the firm jumps to `y*` from any `k` (`invest_fe`). Investment is reversible. |
| Ex 5.9b, p. 113 | Capital adjusts gradually. | `g` is nondecreasing and `g(k′) − g(k) ≤ (1 − δ)(k′ − k)`, by lattice arguments without derivatives (`ex_5_9b_mono`, `ex_5_9b_slope`). |
| Ex 5.10, p. 113 | What must be assumed about `α` and `β`? | `β(1 + α) < 1`, which gives Assumptions 4.10–4.11 (`crs_assumption410`, `crs_assumption411`). |
| Ex 5.11d, p. 116 | (W5) gives concavity of `u_W` (with (W4)). | Monotonicity of `W` is not needed for concavity: a nonnegative concave function on `[0, ∞)` is nondecreasing (`monotoneOn_of_concave_nonneg`, `ex_5_11d_concave`). |
| Ex 5.12b, p. 117 | `v` is concave and demand is continuous. | With `W` concave, nonnegative and strictly concave in `C` (`ex_5_12b_concave`, `ex_5_12b_demand`). |
| §5.13, pp. 117–118 | The Pareto problem with aggregators `W₁`, `W₂`. | Both aggregators are nondecreasing (W4), and `W₂` is strictly increasing in each argument. This gives a Slater condition for lower hemi-continuity of the constraint set (`isLHC_of_approx`, `pareto_lhc`). |
| Ex 5.14a, p. 119 | An optimal ordering policy exists. Is it unique? | It exists: at every `x`, either not ordering is optimal or some `y > 0` attains the supremum (`ex_5_14a_policy`). It is not unique: at `x = 1 + A` both choices are optimal (`ex_5_14_policy`). |
| Ex 5.15a, p. 123 | `Y*` is well defined. | `Y* ≤ ap/r`, and when `Y* > 0` the supremum is attained at a unique `τ*` (`ex_5_15a`, `Gcyc_argmax_unique`). |
| §5.17, p. 126 | `U` continuously differentiable on `ℝ₊`. | A continuous derivative on `(0, ∞)` suffices: consumption never falls below `I > 0` along an optimal plan (`CSHyp`). `U′(c) → 0` is added (see Ex 5.17b above). |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| Chapters 3–4 results | Cited. | The modules of the Chapter 4 project, with its copies of Chapter 3, are carried over so that the project is self-contained. |
| §5.1 | (T2): `x ≤ f(x) ≤ x̄` on `[0, x̄]`, and `f(x) < x` for `x > x̄`. | On `X = [0, x̄]` only the first half is used, so `GrowthHyp` drops the second, and `f(k) = k` fits (Exercise 5.2, `ex_5_2a_not_T2`, `ex_5_2a`). |
| Ex 5.2b, p. 105 | `U = ln` with `Γ(x) = [0, x]`. | `Γ(x) = (0, x)` on `x > 0`, as in Chapter 4's unit-elastic model: `F(x, y) = ln(x − y)` must be real-valued, and the open interval has the same supremum. The unit-elastic model is extended to `α = 1` (`LogModel`). |
| §5.17, p. 126 | `F(x, y) = U(I + x − y/R)` on the graph of `Γ`. | `csF` clamps consumption at `0` off the graph, where `F` is never evaluated. |
| Open-ended exercises | "Under what conditions…?" | Answered with sufficient conditions, listed above. |
