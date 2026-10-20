# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book. Results are
listed by their source in the literature. Lean names are relative to
`DPExtensions.ValueOfInformation`. Where the Lean statement departs from the published one, see
[departures from the sources](corrections.md).

## Sufficiency

| Source | Claim | Lean |
| --- | --- | --- |
| Blackwell (1951, 1953) | Experiments, garblings, unnormalized posteriors, decision values | `IsStochastic`, `garble`, `joint`, `payoff`, `value`, `payoff_garble`, `joint_garble` |
| Blackwell (1951, 1953); Marschak and Miyasawa (1968) | Garbling never raises the value of an experiment | `value_garble_le` |
| Blackwell (1953) | The posteriors of an experiment are a mean-preserving spread of those of its garbling (sublinear form) | `IsSublinear`, `IsSublinear.sum_le`, `sublinear_garble_le`, `decisionValue_sublinear` |
| — (standard) | Information has nonnegative value; perfect information is an upper bound | `noInfo`, `value_noInfo`, `value_noInfo_le`, `perfect`, `value_le_perfect` |

## The converse

| Source | Claim | Lean |
| --- | --- | --- |
| Blackwell (1951, 1953) | More valuable in every decision problem implies garbling; the equivalence under a full-support prior | `garbleMap`, `stochSet`, `convex_stochSet`, `isCompact_stochSet`, `blackwell_converse`, `blackwell` |

## Binary signals

| Source | Claim | Lean |
| --- | --- | --- |
| — (standard example) | A less accurate binary symmetric signal is a garbling of a more accurate one; accuracy is valuable; guessing the state is worth the accuracy | `binExp`, `binExp_isStochastic`, `binExp_garble`, `value_mono_accuracy`, `sup'_bool`, `value_guess`, `value_strict` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Blackwell (1953) | The equivalence with mean-preserving spreads of normalized posterior distributions for every convex function on the simplex | Stated here for sublinear functions of unnormalized posteriors, which are the perspectives of convex functions. |
| — | Dynamic value of information (more informative signals every period in a Bayesian dynamic program) | Needs convexity of the value function in beliefs, not developed here. |
