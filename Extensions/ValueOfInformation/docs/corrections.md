# Departures from the sources

Places where a Lean statement differs from the published one: a hypothesis made explicit, a
special case proved, or a definition chosen among equivalent ones.

| Where | Published | How it is stated |
| --- | --- | --- |
| Values | Expected payoffs computed with normalized posteriors `π(θ | y)` weighted by signal probabilities. | `V_u(P) = ∑_y max_a ∑_θ π(θ)P(θ, y)u(a, θ)`, which equals the published value and needs no division; it holds for any real `π` (sufficiency) and full-support `π` (equivalence). |
| Experiments | Finite or general measurable signal spaces. | Finite states, signals and actions. Sufficiency needs only that the garbling is a Markov matrix; the converse uses decision problems with the action set equal to the garbled signal space. |
| Converse | `Q` is a garbling of `P`. | Without full support, the conclusion is on the unnormalized posteriors, `π(θ)Q(θ, y') = π(θ)(PM)(θ, y')`; with `π > 0` it is `Q = PM` (`blackwell`). |
