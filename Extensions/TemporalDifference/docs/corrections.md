# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| Sampling | TD(λ) along a single trajectory of an irreducible aperiodic chain (Tsitsiklis and Van Roy, 1997). | TD(0) with i.i.d. sampling: at each step a transition `(X_k, X'_k)` with `X_k ∼ d` and `X'_k ∼ P(X_k, ·)` given `ℱ_k`, so the noise is a martingale difference; the initial parameter is deterministic and the step sizes are deterministic. |
| Features | A full-rank feature matrix `Φ ∈ ℝ^{n×K}`. | Features in any finite-dimensional real inner product space `E`, spanning `E` in the sense that `⟪φ(x), z⟫ = 0` for all `x` forces `z = 0`; the stationary distribution has full support. |
| Error bound | `‖Φr* − J*‖_D ≤ ‖ΠJ* − J*‖_D / (1 − β)` for λ = 0. | The sharper `(1 − β²)‖V_θ* − V‖_d² ≤ ‖ΠV − V‖_d²`, by Pythagoras applied twice. |
