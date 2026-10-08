# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| Setting (Puterman and Brumelle, 1979) | Banach spaces of value functions, with the derivative of `Tv − v` given by `βP_σ − I`. | Finitely many states with the supremum norm; any set of policies, with a greedy selector given as part of the model (`PolicyModel.greedy_spec`). |
| Quadratic convergence | A Lipschitz condition on the greedy decision rule as an operator. | A Lipschitz condition on greedy transition rows in total variation: `∑_y |P_{greedy v}(x, y) − P_{greedy w}(x, y)| ≤ L‖v − w‖`. The conclusion is written `(1 − β)‖e_{k+1}‖ ≤ βL‖e_k‖²`. |
| Finite termination | Policy iteration terminates because there are finitely many policies and values strictly increase until optimality. | Termination is derived from the linear rate and the optimality gap, which also bounds the number of iterations. |
