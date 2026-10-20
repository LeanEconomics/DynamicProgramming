# Source map

An extension of Sargent and Stachurski, *Dynamic Programming*, beyond the book. Results are
listed by their source in the literature. Lean names are relative to
`DPExtensions.AdaptiveLearning`. Where the Lean statement departs from the published one, see
[departures from the sources](corrections.md).

## Stochastic approximation

| Source | Claim | Lean |
| --- | --- | --- |
| Robbins and Siegmund (1971), Thm 1 | Nonnegative almost-supermartingales converge and `∑ c_k < ∞` | `robbins_siegmund` |
| Robbins and Monro (1951); Ljung (1977); Benveniste, Métivier and Priouret (1990) | Stochastic approximation converges a.s. under a Lyapunov (drift) condition, here quadratic | `sa_lyapunov` |

## The cobweb model

| Source | Claim | Lean |
| --- | --- | --- |
| Ezekiel (1938), the cobweb theorem | Under naive expectations the deviation from equilibrium is `β^t(p_0 − p̄)`, explosive for `|β| > 1` | `naive_eq`, `naive_diverges` |
| Bray and Savin (1986); Evans and Honkapohja (2001), Ch. 2 | Least-squares learning converges to the REE iff `β < 1` | `cobweb_learning`, `learning_eq`, `one_add_sum_le_prod`, `learning_diverges` |
| Evans and Honkapohja (2001), Ch. 2 | The recursive form of the sample mean; the gain `1/(t + 1)` | `harmonic_gain`, `recursive_mean` |
| Muth (1961); Evans and Honkapohja (2001), Ch. 2 | From demand and supply, `β = −s/b < 0`: learnable always, naive expectations explosive when `s > b` | `cobweb_market` |

## E-stability of linear models

| Source | Claim | Lean |
| --- | --- | --- |
| Evans and Honkapohja (2001) | E-stability of `θ ↦ μ + Bθ` (Lyapunov form) | `IsEStable` |
| Evans and Honkapohja (2001) | Sufficient conditions; scalar case `β < 1` | `isEStable_of_inner_le`, `isEStable_of_opNorm_lt_one`, `isEStable_smul_iff` |
| Evans and Honkapohja (2001) | A real eigenvalue `≥ 1` rules out E-stability; E-unstable REE repel learning | `not_isEStable_of_eigen`, `learning_diverges_of_eigen` |
| — | E-stable REE are unique, and exist in finite dimensions | `ree_unique`, `ree_existsUnique` |
| Marcet and Sargent (1989); Evans and Honkapohja (2001) | Steady-state learning converges a.s. to an E-stable REE | `estable_learning` |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Lyapunov's theorem | E-stability (eigenvalues with real part `< 1`) iff a quadratic Lyapunov function exists | Needs the matrix Lyapunov equation; the Lyapunov form is taken as the definition. |
| Marcet and Sargent (1989); Evans and Honkapohja (2001) | Recursive least squares with regressors, the ODE method in general, projection facilities | The general ODE method is beyond the quadratic Lyapunov case. |
| Evans and Honkapohja (2001) | Constant-gain learning, escape dynamics, sunspots | Out of scope. |
