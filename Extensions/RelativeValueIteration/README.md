# Relative and endogenous value function iteration in Lean

This is the `Extensions/RelativeValueIteration/` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming).
Run the commands below from this directory: `cd Extensions/RelativeValueIteration` from the
repository root. [Return to the library index](../../README.md).

An extension beyond Sargent and Stachurski's *Dynamic Programming*, which treats only standard
(discounted) value function iteration. When `β` is close to one, value iteration converges at
rate `β` — slowly. Since policies depend only on value *differences*, iterating on differences is
enough, and differences converge at rate `β` times the rate at which the state forgets its past.
This is relative value iteration (White, 1963; Morton and Wecker, 1977; Bray, 2019a). When some
state variables are exogenous, it is enough to iterate on differences *within* each exogenous
state: endogenous value iteration (Bray, 2019b). The library contains **88 theorems**.

* **Relative value iteration**: `T(v + c) = Tv + βc` and greedy policies ignore constants
  (`isGreedy_add_const_iff`); relative value iteration is value iteration up to a constant
  (`relT_iterate`); the **span contraction** `sp(Tv − Tw) ≤ βα·sp(v − w)` with `α` the Dobrushin
  coefficient (`sp_T_sub_le`); relative values converge at rate `βα` (`rel_converges`); a policy
  greedy for `v` is within `β/(1 − β)·sp(Tv − v)` of optimal (`policy_error`); **Bray's
  stopping rule** gives `ε`-optimal policies after finitely many steps (`stopping_rule`,
  `stopping_rule_sup`, `stopping_eventually`).
* **Average reward** (`β = 1`): **White's theorem** — if `α < 1`, relative value iteration
  converges to a solution of `Th = h + g` (`white`); the greedy policy earns the gain `g` per
  period and no policy earns more (`avg_greedy`, `avg_upper`, `avg_tendsto`); the gain is unique
  (`gain_unique`).
* **Endogenous value iteration**: with an exogenous component `x`, greedy policies ignore
  functions of `x` (`isGreedy_add_lift_iff`), endogenous value iteration is value iteration up to
  such a function (`endoT_iterate`), and the within-`x` span contracts at rate `βα_y` with `α_y`
  the endogenous Dobrushin coefficient (`spy_T_sub_le`, `endo_converges`). Any bound on the full
  coefficient bounds the endogenous one (`endoCoeff_le`), so endogenous value iteration is never
  slower. `v*` and an optimal policy are recovered from the endogenous value (`vstar_recover`,
  `mean_unique`, `optimal_of_greedy_endo`, `endo_policy_error`).
* **An example** (`relative_slow_endogenous_exact`): with a seasonal exogenous cycle, relative value
  iteration converges no faster than `βⁿ`, while endogenous value iteration is exact at once.

All names are in the namespace `DPExtensions.RelativeValueIteration`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md): the
rates are non-asymptotic, in terms of Dobrushin coefficients, rather than Bray's asymptotic rates
in terms of spectral subradii.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Span](RelativeValueIteration/Span.lean) | 9 | The span seminorm; the Dobrushin bound |
| [MDP](RelativeValueIteration/MDP.lean) | 14 | Bellman operators, constant shifts, relative iteration, the span contraction |
| [Discounted](RelativeValueIteration/Discounted.lean) | 13 | Sup-norm contraction, `v*`, `v_σ`, monotone comparisons |
| [RelativeVI](RelativeValueIteration/RelativeVI.lean) | 12 | Strong convergence, MacQueen–Porteus, Bray's stopping rule |
| [AverageReward](RelativeValueIteration/AverageReward.lean) | 9 | White's theorem, optimal gain, uniqueness |
| [Endogenous](RelativeValueIteration/Endogenous.lean) | 24 | Endogenous value iteration |
| [Example](RelativeValueIteration/Example.lean) | 7 | Relative VFI slow, endogenous VFI exact |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
