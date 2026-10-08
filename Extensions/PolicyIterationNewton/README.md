# Policy iteration as Newton's method in Lean

This is the `Extensions/PolicyIterationNewton/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/PolicyIterationNewton` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*. Volume 1 shows that Howard
policy iteration is Newton's method and that it terminates in finite MDPs; here we prove how fast
it converges. That is why policy iteration (and the endogenous-grid and time-iteration methods
built on it) needs so few iterations in practice. The library contains **37 theorems**.

* **The framework**: finitely many states and an arbitrary set of policies (for example
  continuous actions) with a greedy selector; the Bellman and policy operators are
  `β`-contractions, policy iteration improves (`le_vσ_greedy`), and it is Newton's method for
  `Tv − v` (`newton_identity`).
* **Rates**: the linear rate `‖v* − v_{k+1}‖ ≤ β‖v* − v_k‖` (`linear_rate`); the
  **Puterman–Brumelle bound** `(1 − β)‖v* − v_{greedy v}‖ ≤ βδ‖v* − v‖`, where `δ` bounds the
  difference between the greedy transitions at `v` and at `v*` (`pb_bound`); hence **quadratic
  convergence** when greedy transitions are Lipschitz in `v` (`quadratic_rate`), **superlinear
  convergence** when they are continuous at `v*` (`superlinear_rate`), and **exact termination**
  when greedy policies near `v*` are optimal (`pi_terminates`, `exists_pi_terminates`).
* **Finite MDPs**: an optimality gap `g > 0` exists (`exists_gap`); policies greedy for any `v`
  within `g/(2β + 1)` of `v*` are optimal (`greedy_optimal_of_near`); so policy iteration reaches
  `v*` exactly once `β^K‖v* − v₀‖ < g/(2β + 1)` (`pi_terminates_finite`): at most
  `1 + log((2β + 1)‖v* − v₀‖/g)/log(1/β)` steps.

All names are in the namespace `DPExtensions.PolicyIterationNewton`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [PolicyModel](PolicyIterationNewton/PolicyModel.lean) | 16 | Policies, operators, fixed points, the Newton identity |
| [Rates](PolicyIterationNewton/Rates.lean) | 12 | Linear, quadratic and superlinear rates; termination |
| [FiniteActions](PolicyIterationNewton/FiniteActions.lean) | 9 | The optimality gap and the iteration bound for finite MDPs |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
