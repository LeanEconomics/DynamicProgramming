# Corrections and conventions

Places where a Lean statement differs from the book: a hypothesis made explicit, a claim corrected,
or a convention chosen.

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 4.4, p. 75 | Under Assumptions 4.1–4.2 (with `β ≥ 0`), an optimal plan satisfies (9) at every `t`. | This needs `β > 0` (`theorem_4_4`). With `β = 0` the continuation of an optimal plan is arbitrary. Two states, `F(x, y) = 1` if `y = true` and `0` otherwise, give an optimal plan that violates (9) at `t = 1` (`theorem_4_4_beta_zero`). The proof cancels `β` in `F + βu(x*′) ≥ F + βu(x′)`. |
| Ex 4.8a, p. 91 | On a convex cone in `ℝˡ₊`, a homogeneous quasi-concave function is concave. | This is false as printed. `f(x, y) = max{x − y, 2(x − y)}` on `ℝ²₊` is homogeneous of degree one and quasi-concave but not concave (`ex_4_8a_counterexample`). The statement holds when `f(x) > 0` for `x ≠ 0` (`ex_4_8a`). |
| Ex 4.8b, p. 91 | Strict inequality for `x ≠ αx′`, all `α`. | With `x′ = 0` this allows any `x ≠ 0`, but then `f(θx) = θf(x)` with equality. `ex_4_8b` also assumes `x′ ≠ αx` (and the positivity of 4.8a). |
| Ex 4.9b, p. 100 | Use Theorem 4.15 to show that the linear policy is optimal in the quadratic model. | Theorem 4.15 does not apply: the state space is `ℝ`, not `ℝˡ₊`, and `F_x = a − bx + c(y − x)` takes both signs. `ex_4_9b` proves optimality by the same variational argument (`euler_sufficient`). A plan with `u(x) > −∞` has `Σ δᵗx_t² < ∞`, so `δᵗx_t → 0` and the boundary terms vanish. |
| pp. 93–95 | Unit-elastic growth with `Γ(k) = (0, k^α]` and `F(k, y) = ln(k^α − y)`. | At `y = k^α`, `F = ln 0 = −∞`, while `F` must be real-valued. `logΓ` and `egΓ` use the open interval `(0, k^α)`, which has the same supremum. |
| Theorem 4.11, p. 85 | "Since `g(x₀) ∈ int Γ(x₀)` and `Γ` is continuous, … `g(x₀) ∈ int Γ(x)` for all `x` in some neighborhood." | Continuity alone does not give this. For example, `Γ(x) = [0, 1] \ (1/2 − x, 1/2 + x)` for `x > 0`, with `Γ(x) = [0, 1]` for `x ≤ 0`, is continuous at `0` with `1/2 ∈ int Γ(0)`. The step uses the convexity of the values of `Γ` (Assumption 4.8) in `ℝˡ` (`eventually_mem_Γ`, from `eventually_mem_of_mem_interior`). |

## Hypotheses weakened or made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 4.3, p. 72 | Under (8) `lim βⁿv(xₙ) = 0`, `v = v*`. | The two halves hold separately. `ex_4_3a` gives `v ≤ v*` under `limsup βⁿv(xₙ) ≤ 0` (`β > 0`). `total_le_of_FE` gives `v* ≤ v` under `liminf βⁿv(xₙ) ≥ 0`. With `β = 0` both sides equal `sup_y F(x, y)` (`theorem_4_3`). |
| Theorem 4.3, proof | Case analysis on `v(x₀)` finite, `+∞`, `−∞`. | One construction covers all cases. For a real `a < v(x₀)`, pick `x_{t+1}` with `a_t < F(x_t, x_{t+1}) + βv(x_{t+1})` and set `a_{t+1} = (a_t − F)/β`; then `a ≤ u(x)` in the limit (`ex_4_3a`). |
| Theorem 4.5, p. 76 | (11) `lim sup βᵗv*(x*_t) ≤ 0`. | As printed (`theorem_4_5`), with `β ≥ 0`. |
| Theorem 4.14, pp. 92–93 | (1) `Tv̂ ≤ v̂`, (2) `lim βⁿv̂(xₙ) ≤ 0`, (3) `u ≤ v̂`; `v = lim Tⁿv̂`. | `v` is defined as `inf Tⁿv̂` (`limitFn`). With (2) as `limsup ≤ 0` and (3), a fixed point `v` equals `v*` (`theorem_4_14`). Condition (1) is needed only to make `v` the limit of the iterates (`tendsto_iterate`). `β > 0`. |
| Assumption 4.3, p. 78 | `X ⊆ ℝˡ` convex; `Γ` nonempty, compact-valued, continuous. | `X` is a metric space for Theorems 4.6–4.7 (`Assumption43`), as the book notes is possible. Theorems 4.8–4.9 use a convex set `S` in a real normed space, and Theorem 4.11 uses `S ⊆ ℝˡ`. |
| Assumption 4.4, p. 78 | `F` bounded and continuous on `A`. | `Assumption44`: bounded and continuous on the graph `A`, `0 < β < 1`. |
| Assumption 4.5, p. 80 | `F(·, y)` strictly increasing in each of its first `l` arguments. | Strict monotonicity in the order of `X`: `x < x′` and `y ∈ Γ(x)` give `F(x, y) < F(x′, y)` (`theorem_4_7`). |
| Theorem 4.9, p. 82 | `gₙ` defined from `vₙ`, `n = 0, 1, …`. | `v₀` is only concave, so `g₀` need not be unique. `argmaxFn` picks one maximizer; the convergence is unaffected. |
| Theorem 4.10, p. 84 | `W` concave and differentiable on a neighborhood `D`. | Only differentiability of `W` at `x₀` is used, not concavity (`theorem_4_10`). The proof is direct and needs no subgradients: near `x₀`, `W(x₀ + h) − W(x₀) ≤ V(x₀ + h) − V(x₀) ≤ W(x₀) − W(x₀ − h)`. |
| Theorem 4.11, p. 85 | `v` is continuously differentiable at `x₀`, with `vᵢ = Fᵢ(x₀, g(x₀))`. | `theorem_4_11` proves differentiability at `x₀` with that derivative. It needs only that `x ↦ F(x, g(x₀))` is differentiable at `x₀`. Continuity of the derivative is not formalised. |
| Ex 4.2a, p. 69 | `‖y‖ ≤ θ‖x‖`. | The sup norm on `ℝˡ`. |
| Ex 4.2b, p. 69 | `F` increasing in its first `l` arguments; `0 ∈ Γ(x)`. | Neither is needed (`ex_4_2b`). |
| Ex 4.4, p. 82 | `X` countable. | Countability is not used: `X` carries the discrete topology, so `X →ᵇ ℝ` is `B(X)` (`DiscreteSetup`). |
| Theorem 4.12, p. 90 | `T : H(X) → H(X)`. | The inequality needs only monotonicity and discounting on `H(X)` (`theorem_4_12`). |
| Ex 4.6c, p. 88 | `v*` homogeneous of degree one with `|v*(x)| ≤ c‖x‖`. | The bound is proved from the plans (`ex_4_6c`). Homogeneity follows from `v* = v ∈ H(X)` (`ex_4_6c_hom`, from Theorem 4.13 and Theorem 4.3). |
| Ex 4.8c–d, p. 92 | "Under what conditions…?" | Answered by sufficient conditions. `ex_4_8c` assumes `F` concave on a convex conical graph, strictly across pairs that are not nonnegative multiples of each other, and gets `v` concave; if also `v ≠ 0` off the origin, `v` is strictly quasi-concave. `ex_4_8d` gets differentiability at an interior `x₀` with an interior maximizer. |
| Theorem 4.15, p. 98 | `X ⊆ ℝˡ₊`; Assumptions 4.3–4.5, 4.7, 4.9. | `theorem_4_15` uses what the proof needs. States lie in an ordered real normed space and feasible plans are nonnegative. `F` is concave on the graph of `Γ` and differentiable along `x*`, with `F_x ≥ 0` there, and Assumption 4.2 holds so that totals exist. |
| Ex 4.1b, p. 66 | `(k_{t+1} + c_t, k_t) ∈ Y`. | Consumption is nonnegative, and `F(k, k′) = max{U(c) : c ≥ 0, (k′ + c, k) ∈ Y}` is assumed attained (`ex_4_1b`). |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| §4.1 | `R̄ = ℝ ∪ {±∞}`. | `EReal`. `F` is real-valued, so the convention `⊥ + ⊤ = ⊥` never applies. `F : X → X → ℝ` is defined on all pairs; only its values on the graph matter. |
| (4)–(7), p. 71 | "`v` satisfies the functional equation" by three cases. | `SatisfiesFE`: `v(x) = sup_{y ∈ Γ(x)} [F(x, y) + βv(y)]` in `R̄`, equivalent to the book's cases by `eq_biSup_iff`. |
| §4.2 | `C(X)`, bounded continuous functions with the sup norm. | `X →ᵇ ℝ`. |
| §4.3 | `H(X)` with `‖f‖ = max_{‖x‖ = 1} |f(x)|`. | Functions on the cone with the predicate `InH` and the norm `hnorm`. The book's Euclidean norm can be any norm. |
| Chapter 3 results | Cited. | `Contraction`, `Correspondences`, `Maximum` and `InteriorPoints` carry them over from the Chapter 3 project. Lemma 3.7 and Theorem 3.8 are restated for objectives with a unique maximizer (`UniqueArgmax`), which covers the subtype state spaces used here. |
| Theorems 4.10–4.11 | Functions on `X ⊆ ℝˡ`. | Functions on `S` are extended by zero to `ℝˡ` (`liftS`), so that derivatives at interior points make sense. |
