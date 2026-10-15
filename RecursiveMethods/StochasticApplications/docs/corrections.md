# Corrections and conventions

Places where a Lean statement differs from the book or from the solutions manual (Irigoyen,
Rossi-Hansberg and Wright, *Solutions Manual for Recursive Methods in Economic Dynamics*, 2002): a
claim corrected, a hypothesis made explicit, or a convention chosen. Every correction marked
*Lean* is backed by a proved counterexample or by a proof of the corrected statement.

## Claims corrected

| Where | Book or manual | Lean |
| --- | --- | --- |
| Exercise 10.1c, p. 289; manual | Theorem 9.8 gives strict concavity of `v(·, z)` and a single-valued `g`. | Under (T4), which only asks that `f` be concave, `F(x, y, z) = U[z f(x) − y]` need not be strictly concave in `x`, so Assumption 9.10 fails and Theorem 9.8 does not apply. The conclusion still holds (`growth_strictConcave`, `ex_10_1c`). On a chord where `v(·, z)` were affine, consumption would be constant along the chord. The chord would then be carried to affine chords of `v(·, z′)` with `β` times the rise, and the supremum `S` of the rises would satisfy `S ≤ βS`. |
| Exercise 10.1d, p. 289; manual | `g` and `c = z f(x) − g` are strictly increasing in both arguments. | False (*Lean*: `ex_10_1d_counterexample`, `ex_10_1d_not_strictMono`). With `U(c) = 1 − e^{−c}`, `f(x) = 2x/(1 + x)`, `z̄ = 2`, `x̄ = 3`, `β = 1/10`, which satisfy (U1)–(U4), (T1)–(T4) and (Z1), `v(x, z) − v(0, z) ≤ 4x`. So `G(x, z) = {0}` for `x ≤ 1/10`, under any Feller `Q`. The manual's first-order condition fails at the corner `g = 0`. Both `g` and `c` are nondecreasing (`ex_10_1d`). |
| Exercise 10.1f, p. 290; manual | With `Q` monotone, `g` is increasing in `z`. | Not established. The manual compares `∫ v′(g, z′) Q(z, dz′)` across the different measures `Q(z, ·)` and `Q(ẑ, ·)`, and concavity of `v(·, z′)` does not order these. What is proved is that `v(x, ·)` is nondecreasing, and strictly increasing for `x > 0` (`ex_10_1f`). |
| Exercise 10.2b, p. 290 | `v(·, z)` is strictly concave and the policy is a continuous single-valued function. | False when `f` is only concave, as (T4) allows (*Lean*: `ex_10_2b_counterexample`). With `f(x) = 2(x₁ + x₂)/(1 + x₁ + x₂)`, `v` depends on `x` only through `x₁ + x₂`, so it is affine along `x₁ + x₂ = 1`. At `x = (3, 0)`, `z = 2`, saving is optimal, and any saving `k > 0` can be held as `(k, 0)` or as `(0, k)`. The claims hold for strictly concave `f` (`ex_10_2b`, `ex_10_2b_diff`). |
| Exercise 10.3a and p. 292 | Theorems 9.6–9.8 give `v(·, z)` strictly increasing and strictly concave, and `g` single-valued. | Only the weak forms of Assumptions 9.8 and 9.10 follow from (a)–(c), and the strict conclusions are false (*Lean*: `ex_10_3a_counterexample`). `Φ(x, z) = [0, 1] × X` satisfies (a)–(c), yet `v(·, z)` is constant and every `y ∈ X` is optimal. The weak conclusions are proved (`ex_10_3a`). |
| §10.4; manual pp. 177–178 | For (2′), `F` is bounded (Assumption 9.7). | False (*Lean*: `ind_F_unbounded`). With `c(a) = (a − ½)²` for `a ≥ ½` and `0` below, `x c(M/x) ≥ M²/(4x)` for small `x`, so `F` is unbounded below on the graph of `Γ`. Existence and uniqueness are recovered by truncating `F` at `−K`, which never binds at an optimum (`UpperBounded`, `ex_10_4b`). |
| §10.4; manual pp. 177–178 | `Γ` satisfies Assumption 9.9 (monotone) and Assumption 9.11 (convex graph). | Both fail (*Lean*: `ind_Γ_not_mono`, `ind_Γ_not_convex`). The lower bound `(1 − δ′)x` rises with `x`, so `Γ(x) ⊄ Γ(x′)` for `x < x′`. And `(M/2, M)` and `(2M, 2M)` lie in the graph, but their midpoint does not, since `3M/2 > max{M, 5M/4}`. The conclusions of Theorems 9.7–9.8 are recovered through (2), whose constraint set is all of `X`: no `y` outside `Γ(x)` beats `Γ(x)` (`ind_rhs_le`). |
| Exercise 10.4e, pp. 295–296; manual p. 179 | Since `D = U_x` is increasing in `z`, so is `v_x(x, z) = D(x, z) − c(y/x) + (y/x)c′(y/x)`. | The step ignores that `y = g(x, z)` itself depends on `z`, so `v_x` increasing in `z` does not follow. Not formalised. |

## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Exercise 10.1e, p. 289 | `v_x(x, z) = U′(c) z f′(x)` where `g(x, z) > 0`. | Only positive consumption `c = z f(x) − g(x, z) > 0` is needed, with `U` differentiable at `c` and `f` at an interior `x` (`ex_10_1e`). |
| Exercise 10.3a, p. 291 | `F(x, y, z) = max {U(c) : (c, y) ∈ Φ(x, z)}` is continuous. | Assumed. The Theorem of the Maximum needs the fibre `{c : (c, y) ∈ Φ(x, z)}` to vary continuously in `(x, y, z)`, which continuity of `Φ` does not give. |
| §10.4, p. 294 | `M` "suitably chosen (very large)". | `M c(1) > A/(1 − β)`, with `β = 1/(1 + r)` and `A` a bound on `U` (`IndHyp.M_big`). |
| Exercise 10.4c, p. 295 | `v(·, z)` is continuously differentiable. | `v_x = U_x − c(a) + a c′(a)` at `x` with `a = g(x, z)/x`, wherever `U(·, z)` is differentiable at `x` and `c` at `a` (`ind_hasDerivAt_x`). |
| Exercise 10.4d, p. 295 | `g` strictly increasing in `x`, with slope less than one; `g/x` strictly decreasing. | The weak form, `g` nondecreasing in `x`, is proved by Topkis's argument (`ex_10_4d`). The rest rests on first-order conditions and is not formalised. |
| Exercise 10.4f, p. 296 | The optimal path converges to a stationary point `x̂` independent of `x₀`. | Every optimal path is monotone and converges (`ex_10_4f_monotone`, `ex_10_4f_tendsto`). That the limit is independent of `x₀`, and positive, is not formalised. |
| §10.5, p. 299 | `sup` over `y, n ≥ 0`. | `y ≤ x` is implicit (consumption `x − y ≥ 0`). The bounded problem uses `n ≤ N̄` with `c(N̄) > Ū/(1 − β)`, which exists (`exists_N_big`), and its solution solves the problem over all `n ≥ 0` (`inv_solves_2`). |
| Exercise 10.5c, p. 299 | `v′(x) = U′[x − Y(x)]`. | Proved where consumption is positive, `Y(x) < x`, and `U` is differentiable at `x − Y(x)` (`inv_hasDerivAt`). At `Y(x) = x` the envelope argument gives only a one-sided bound. |
| Exercise 10.5e–g, pp. 299–300 | `Y(x₂) > Y(x₁)` or `Y(x₂) = Y(x₁) = 0`, and `N(x₂) < N(x₁)`, for `x₂ > x₁`, from the first-order conditions. | The weak forms `Y(x₁) ≤ Y(x₂)` and `N(x₂) ≤ N(x₁)` are proved without first-order conditions, by Topkis's argument with choices ordered by `(y, −n)` (`ex_10_5e`). The sign argument of 10.5f is proved as stated (`ex_10_5f`). |
| Exercise 10.6c, p. 303 | The Euler equation (2) from differentiability of `vᵖ`. | Proved when each `vᵖ(·, z′)` has partial derivative `vᵖᵢ(y, z′)` at the interior `y`, measurable in `z′` (`ex_10_6c_euler`). The integral is differentiated under the integral sign, using that a bounded concave function is Lipschitz inside its domain. |
| Exercise 10.10d–e, p. 313 | Do (d)–(e) hold for any prior density positive on `(0, 1)`? | Proved for the beta priors (`ex_10_10d`, `ex_10_10e`); arbitrary priors are not addressed. |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| §§10.1–10.3, 10.6 | Shocks i.i.d. (Z2) or Markov (Z3). | Every result is proved for any Feller transition `Q`; i.i.d. shocks are `Kernel.const` (`isFeller_const`). |
| §10.5 | The state is the stock `x`; the harvest shock enters the law of motion. | The state is `(x, ω)` with `Q(ω, ·) = μ` and `x′ = y + nω′`, in Chapter 9's second formulation. That `v` does not depend on `ω` is proved (`inv_indep`). |
| §10.7, p. 305 | Wage offers with a density `f`. | Any probability measure `μ` on `W`. `F(w) = μ([0, w))`. |
| Interpretive parts | 10.4a, 10.5b (sequence form), 10.6f–g, 10.7i, 10.8d, 10.9, 10.10i, 10.11. | Not formalised: they ask for a formulation or an interpretation, not a claim. Exercise 10.2c is also not formalised. |
