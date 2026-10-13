# Corrections and conventions

Places where a Lean statement differs from the book: a hypothesis made explicit, a claim corrected,
or a convention chosen.

| Where | Book | Lean |
| --- | --- | --- |
| §2.1, p. 9 (assumptions on `F`) | `F` is strictly quasi-concave on `ℝ²₊` and `F(0, n) = 0` for all `n`. | These are inconsistent: `F` vanishes on the whole ray `k = 0`, so on that ray `F(θx + (1 − θ)y) = min{F(x), F(y)} = 0`. `Neoclassical` assumes strict quasi-concavity on the open quadrant, which Cobb–Douglas satisfies (`cobbDouglas_neoclassical`) and which suffices for Ex 2.1. |
| Ex 2.4a, p. 15 | `s > 0`. | A positive stationary point requires `s(1 − δ) < 1`: since `f(k)/k` decreases to `1 − δ`, if `s(1 − δ) ≥ 1` then `s f(k) > k` for all `k > 0` and there is no positive steady state. The hypothesis holds for every savings rate `0 < s ≤ 1` when `δ > 0`, which is the economically relevant case (`savings_crossings`). |
| (21)–(22), p. 27 | Rental rates and wages are given for `t = 1, …, T`. | The equilibrium also needs `r₀` and `w₀`; the same formulas are used for `t = 0, …, T`. |
| (8), p. 25 | The firm's problem over `k, n ≥ 0`. | The case `n = 0` uses continuity of `n ↦ F(k, n)` at `0` (true for the book's `F`, which is C¹ on `ℝ²₊`), stated as a hypothesis. |
| Ex 2.6, p. 19 | The value of the objective `E[∑ βᵗ U(c_t)]` under the policy. | `hasSum_expected_utility` computes `∑ βᵗ E[ln c_t]` under the product measure of the shocks; exchanging expectation and sum is not proved. |
| Ex 2.10, p. 29 | Bond prices `q_t` for `t = 0, …, T − 1`. | A bond bought in period `T` has no payoff date, so the household's terminal holding is set to `b_{T+1} = 0`. |
| Ex 2.5, p. 18 | State the first-order conditions. | They are proved sufficient for an optimum (`tree_euler_optimal`), and the dimension of the plan space is computed (`finrank_plan`). |
| `U = ln` | `U(0) = −∞` keeps consumption interior. | Lean's `log 0 = 0`, so feasibility requires consumption in `(0, ∞)`, the domain `D` of `U`. |
