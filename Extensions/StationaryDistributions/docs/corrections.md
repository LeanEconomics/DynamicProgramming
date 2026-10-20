# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| State space | A compact metric space with a closed partial order and a least and a greatest element (Hopenhayn and Prescott, 1992). | The finite grid `{0, …, n}` with its natural order; distributions and kernels are real functions on `ℕ` used only on the grid. On a grid weak convergence is pointwise convergence, which is what `global_stability` proves. |
| Monotone mixing | There are `c`, `m` and `ε > 0` with `Pᵐ(bottom, [c, top]) ≥ ε` and `Pᵐ(top, [bottom, c]) ≥ ε`. | The same condition written with the cdf of the `m`-step rows: `F_{Pᵐ(0,·)}(y) ≤ 1 − ε` for `y < c`, and `F_{Pᵐ(n,·)}(c) ≥ ε` (`MonotoneMixing`). |
| Existence | Tarski's fixed point theorem on the set of distributions. | Monotone iteration from the bottom point mass, whose cdfs decrease and converge; the limit is the least stationary distribution. |
| Comparative statics | Monotone in a parameter. | Two kernels with FOSD-ordered rows; the lower one must mix (`stationary_mono`), and the conclusion covers every stationary distribution of the upper one. |
| Asset chains | A continuum of asset levels and possibly persistent income. | Assets on the grid, i.i.d. income; the saving rule maps grid points to grid points. |
