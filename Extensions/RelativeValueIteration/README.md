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
state: endogenous value iteration (Bray, 2019b). The library contains **175 theorems**.

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
* **Asymptotic eigenvalue rates**: the **subradius** `λ(Q) = ρ(ΔQ)`, with `Δ` subtracting the
  reference value, is the largest modulus of an eigenvalue of `Q` other than `1`
  (`spectralRadius_deltaQ`, using that a stochastic matrix has no Jordan block at `1`), it
  governs the span (`sp_pow_mulVec_le`, from Gelfand's formula), and it is at most the Dobrushin
  coefficient (`subradius_le_dobrushin`). Policy evaluation converges at rate `βλ(P_σ)`
  (`sp_policy_eval_le`; Morton, 1971). With a unique, strict optimal decision rule `σ*` the
  greedy policy freezes (`eventually_T_eq_Tσ`), after which relative values converge at rate
  `βλ(P_{σ*})` (`relative_asymptotic_rate`, `rel_asymptotic_rate`; Morton and Wecker, 1977) while
  levels converge no faster than `β` (`level_rate_lower`). Endogenous values converge at rate
  `βρ(ΛP_{σ*})` (`endo_asymptotic_rate`), endogenous policy evaluation at rate `βρ(ΛP_σ)`
  (`endo_policy_eval_le`), and `ρ(ΛF) ≤ λ(F)` (`endoRadius_le_subradius`; Bray, 2019b, Prop 4).
  These are Bray's `O⁺` rates exactly: `O⁺(λⁿ)` means `O((λ + ε)ⁿ)` for every `ε > 0`.
* **When endogenous iteration is strictly faster** (Bray, 2019b, Prop 5 and Cors 2–4): the whole
  chain mixes no faster than its exogenous part, `σ(F_x) ≤ σ(P_σ)` (`subradius_FxMat_le`, via
  `spectrum_exo_subset`); for any vector norm, `ρ(ΛP_σ)` is at most the largest operator norm of
  the demeaned endogenous transitions `ΩF_y(σ, x)` (`endoRadius_le_of_vecNorm`), so endogenous
  iteration is strictly faster whenever `σ(F_x)` exceeds that bound
  (`endoRadius_lt_subradius_of_vecNorm`, `endo_strictly_faster`, `endo_eval_strictly_faster`).
  The bound may be the largest absolute row sum (`endoRadius_le_rowSum`) or the Hajnal coefficient
  (`endoRadius_le_hajnal`). Endogenous iteration is strictly faster when `F_x` is not ergodic and
  every `F_y(σ, x)` is scrambling (`endoRadius_lt_of_nonergodic_scrambling`), and, when `F_y` does
  not depend on `x`, whenever `σ(F_x) > σ(F_y)` (`endoRadius_le_subradius_Fy`,
  `endoRadius_lt_of_Fy_const`).
* **An example** (`relative_slow_endogenous_exact`): with a seasonal exogenous cycle, relative value
  iteration converges no faster than `βⁿ`, while endogenous value iteration is exact at once.

All names are in the namespace `DPExtensions.RelativeValueIteration`. See the
[source map](docs/source-map.md) and [departures from the sources](docs/corrections.md). The
rates come in two forms: non-asymptotic, valid at every step, in terms of Dobrushin coefficients;
and asymptotic, in terms of spectral subradii, which are sharper but hold only after the optimal
policy has been found.

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
| [SpectralRadius](RelativeValueIteration/SpectralRadius.lean) | 12 | Spectral radius of a real matrix; Gelfand's formula and its consequences |
| [Subradius](RelativeValueIteration/Subradius.lean) | 15 | The subradius: eigenvalue characterization, span bound, Dobrushin bound |
| [AsymptoticRates](RelativeValueIteration/AsymptoticRates.lean) | 12 | Policy freezing; Morton–Wecker asymptotic rate of relative VFI; levels no faster than `β` |
| [AsymptoticEndogenous](RelativeValueIteration/AsymptoticEndogenous.lean) | 16 | Asymptotic rate of endogenous VFI; `ρ(ΛF) ≤ λ(F)` |
| [EndogenousSpeedup](RelativeValueIteration/EndogenousSpeedup.lean) | 32 | When endogenous VFI is strictly faster: Bray's Prop 5 and Cors 2–4 |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
