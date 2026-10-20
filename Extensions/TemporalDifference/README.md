# Temporal-difference learning in Lean

This is the `Extensions/TemporalDifference/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/TemporalDifference` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*, whose Chapter 9 of Volume 2
treats fitted value iteration and Q-learning but not learning value functions with a linear
architecture. TD(0) is the workhorse for estimating values in large models from simulated data.
The library contains **31 theorems**.

* **The stationary-distribution norm**: for a Markov matrix with stationary distribution `d`,
  `‖v‖_d² = ∑ d(x)v(x)²` makes `P` nonexpansive (`dsq_applyP_le`) and the Bellman operator of a
  Markov reward process a `β`-contraction (`dsq_bellman_sub_le`).
* **The TD fixed point**: with features `φ` spanning `E` and `d > 0`, the Gram form is coercive
  (`exists_gram_lower`), the TD mean field is strongly monotone and Lipschitz
  (`meanField_lyapunov`, `meanField_lipschitz`), and the TD fixed point exists and is unique
  (`exists_unique_fixedPoint`) — although TD is not gradient descent on any objective.
* **How good it is**: the projection `ΠV` exists and is the best approximation
  (`exists_best_approx`, `best_approx`), and `(1 − β²)‖V_θ* − V‖_d² ≤ ‖ΠV − V‖_d²`
  (`tvr_bound`).
* **TD(0) converges** almost surely to the TD fixed point when transitions are sampled i.i.d.
  from the stationary distribution and the step sizes satisfy the Robbins–Monro conditions
  (`td_converges`), by stochastic approximation with a quadratic Lyapunov function
  (`sa_lyapunov`, copied from `Extensions/AdaptiveLearning`).

All names are in the namespace `DPExtensions.TemporalDifference`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [RobbinsSiegmund](TemporalDifference/RobbinsSiegmund.lean) | 1 | Robbins–Siegmund lemma (copied) |
| [LyapunovSA](TemporalDifference/LyapunovSA.lean) | 1 | Stochastic approximation with a quadratic Lyapunov function (copied) |
| [WeightedNorm](TemporalDifference/WeightedNorm.lean) | 10 | The stationary-distribution norm; `P` nonexpansive; the Bellman contraction |
| [Features](TemporalDifference/Features.lean) | 9 | Linear features, the mean field, the TD fixed point |
| [ErrorBound](TemporalDifference/ErrorBound.lean) | 5 | Projection and the error bound |
| [TDZero](TemporalDifference/TDZero.lean) | 5 | TD(0) with i.i.d. sampling converges almost surely |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
