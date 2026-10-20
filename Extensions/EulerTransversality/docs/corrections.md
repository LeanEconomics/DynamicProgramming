# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| Sufficiency (Stokey and Lucas, 1989, Thm 4.15) | `X ⊆ ℝ^l_+`, `F` concave, continuously differentiable and increasing in the state; interior Euler equation `F_y(x_t, x_{t+1}) + βF_x(x_{t+1}, x_{t+2}) = 0`; `lim β^tF_x(x_t, x_{t+1})·x_t = 0`. | Any real vector space; derivatives replaced by supergradients `(p_t, q_t)` on the feasible graph, which covers kinks and corners; `p_t(x_t) ≥ 0` along feasible paths replaces nonnegativity of states and of `F_x`. Optimality is the catching-up criterion, which implies optimality whenever values are finite. |
| Growth model | `u`, `f` continuously differentiable, strictly concave, Inada conditions. | `u` and `f` concave on `[0, ∞)`, `u` increasing; derivatives are needed only at the path, and only `u'(c_t), f'(k_t) ≥ 0` is used. Consumption may be zero. |
| Necessity (Kamihigashi, 2001) | General reduced-form models, including utility unbounded below. | The growth model with `β < 1`, `f(0) ≥ 0`, finite `u(0)`, and finite value of the candidate path; the condition proved is `β^tu'(c_t)k_{t+1} → 0`, which equals the sufficiency form `β^{t+1}u'(c_{t+1})f'(k_{t+1})k_{t+1}` along Euler paths. |
