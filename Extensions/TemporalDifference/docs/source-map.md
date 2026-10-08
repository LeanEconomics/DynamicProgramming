# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book. Results are
listed by their source in the literature. Lean names are relative to
`DPExtensions.TemporalDifference`. Where the Lean statement departs from the published one, see
[departures from the sources](corrections.md).

## Stochastic approximation (copied from `Extensions/AdaptiveLearning`)

| Source | Claim | Lean |
| --- | --- | --- |
| Robbins and Siegmund (1971) | Nonnegative almost-supermartingales converge | `robbins_siegmund` |
| Robbins and Monro (1951); Ljung (1977) | Stochastic approximation with a quadratic Lyapunov function | `sa_lyapunov` |

## The stationary-distribution norm

| Source | Claim | Lean |
| --- | --- | --- |
| Tsitsiklis and Van Roy (1997) | `P` is nonexpansive for `‖·‖_d` when `d` is stationary | `dsq`, `dinner`, `applyP`, `dsq_nonneg`, `dinner_self`, `dinner_comm`, `dsq_add`, `dsq_smul`, `dinner_le`, `jensen_sq`, `dsq_applyP_le`, `dinner_applyP_le` |
| Tsitsiklis and Van Roy (1997) | The Bellman operator is a `β`-contraction for `‖·‖_d` | `dsq_bellman_sub_le` |

## Linear features and the TD fixed point

| Source | Claim | Lean |
| --- | --- | --- |
| Tsitsiklis and Van Roy (1997) | Linear architectures; the Gram form is coercive under full rank | `vθ`, `vθ_sub`, `vθ_smul`, `dsq_vθ_pos`, `exists_gram_lower` |
| Sutton (1988); Tsitsiklis and Van Roy (1997) | The TD mean field is strongly monotone and Lipschitz; the TD fixed point exists and is unique | `meanField`, `meanFieldLin`, `meanField_sub`, `inner_meanFieldLin`, `meanField_lyapunov`, `meanField_lipschitz`, `exists_unique_fixedPoint` |

## The error bound

| Source | Claim | Lean |
| --- | --- | --- |
| — (standard) | The projection is characterized by the normal equations, exists, and is the best approximation | `dinner_add_left`, `inner_meanField`, `best_approx`, `exists_best_approx` |
| Tsitsiklis and Van Roy (1997), sharpened by the Pythagorean argument | `(1 − β²)‖V_θ* − V‖_d² ≤ ‖ΠV − V‖_d²` | `tvr_bound` |

## TD(0)

| Source | Claim | Lean |
| --- | --- | --- |
| Sutton (1988); Tsitsiklis and Van Roy (1997) | The expected TD increment is the mean field; TD(0) converges almost surely to the TD fixed point | `tdStep`, `meanField_eq_sum`, `continuous_tdStep`, `continuous_meanField`, `norm_tdStep_le`, `td_converges` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Tsitsiklis and Van Roy (1997) | Sampling along a single trajectory of the chain, TD(λ) with eligibility traces | Markov-noise stochastic approximation (Poisson equation) is beyond the martingale-difference case proved here. |
| Baird (1995) | Divergence of off-policy TD with linear features | Out of scope. |
