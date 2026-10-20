# SLP Chapter 2: An Overview, in Lean

This is the `RecursiveMethods/Overview` proof project in
[LeanEconomics/DynamicProgramming](https://github.com/LeanEconomics/DynamicProgramming), the first
chapter project for Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics*
(1989). Run the commands below from this directory. [Return to the library index](../../README.md).

Chapter 2 previews the book with the one-sector growth model: the planner's problem with a finite
and an infinite horizon, its stochastic version, and the competitive equilibrium that decentralizes
it. Its formal content is in Exercises 2.1–2.10, all of which are formalised here. The library
contains **114 theorems**.

* **The finite-horizon planner** (pp. 10–11): for concave `U` and `f`, a feasible path satisfying the
  Euler equation (5) and `k_{T+1} = 0` (6) is optimal (`euler_optimal`), and the only optimum when
  `U` is strictly concave (`euler_unique`).
* **The log/Cobb–Douglas economy** (Ex 2.2–2.3): the change of variables `z_t = k_t/k_{t−1}^α`
  (`euler_iff_z`), the backward solution `s_n = αβ(1 − (αβ)ⁿ)/(1 − (αβ)ⁿ⁺¹)` (`z_unique`), the
  path (7) as the unique optimum (`path_optimal`, `path_unique`) with `s_n → αβ`
  (`savingRate_tendsto`); the value `v(k) = A + B ln k` of the policy (8) (`hasSum_value`), which
  solves the functional equation (11) with `αβk^α` as its unique maximizer (`bellman_isGreatest`,
  `bellman_argmax_unique`).
* **The neoclassical technology** (Ex 2.1): `f(k) = F(k, 1) + (1 − δ)k` is continuously
  differentiable, strictly increasing and strictly concave, with `f′(0+) = ∞` and
  `f′(∞) = 1 − δ`; Cobb–Douglas satisfies the assumptions (`cobbDouglas_neoclassical`).
* **A constant savings rate** (Ex 2.4): `k ↦ s f(k)` has exactly one positive steady state, every
  path from `k₀ > 0` converges to it monotonically, and none reaches it in finite time unless it
  starts there (`exists_unique_fixedPoint`, `tendsto_fixedPoint`, `iterate_eq_fixed_iff`).
* **Uncertainty** (Ex 2.5–2.7): the event-tree planner's plans form a space of dimension
  `2(1 + n + ⋯ + nᵀ)` and the stochastic Euler equations are sufficient (`finrank_plan`,
  `tree_euler_optimal`); with i.i.d. shocks `v(k, z) = A + B ln k + C ln z` solves the stochastic
  functional equation (3) and is the expected lifetime utility of the policy `αβzk^α`
  (`stoch_bellman_isGreatest`, `hasSum_expected_utility`); with Gaussian log shocks
  `ln k_t ∼ N(μ_t, σ_t²)` with explicit limits (`hasLaw_logPath`, `meanN_tendsto`,
  `varN_tendsto`).
* **Competitive equilibrium** (§2.3, Ex 2.8–2.10): firms earn zero profit at the equilibrium factor
  prices (`firm_profit_le`); equilibrium allocations are optimal (`first_welfare`); the planner's
  path with the prices (20)–(22) is an equilibrium (`second_welfare`), also when firms own the
  capital (`firmOwned_firm_optimal`, `firmOwned_household_optimal`) and with sequential markets in
  goods, factors and bonds (`sequential_household_optimal`).

All names are in the namespace `StokeyLucasPrescott.Overview`. See the
[source map](docs/source-map.md) and the [corrections](docs/corrections.md).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Basics](Overview/Basics.lean) | 5 | Tangent-line inequalities, telescoping, Euler sufficiency and uniqueness |
| [FiniteHorizon](Overview/FiniteHorizon.lean) | 15 | Ex 2.2: the finite-horizon log/Cobb–Douglas solution |
| [BellmanLog](Overview/BellmanLog.lean) | 8 | Ex 2.3: the value function and the functional equation (11) |
| [Technology](Overview/Technology.lean) | 12 | Ex 2.1: the neoclassical technology; Cobb–Douglas |
| [SavingsRate](Overview/SavingsRate.lean) | 19 | Ex 2.4: steady state and monotone convergence |
| [StochasticLog](Overview/StochasticLog.lean) | 17 | Ex 2.6: the stochastic functional equation and expected utility |
| [StochasticObjective](Overview/StochasticObjective.lean) | 12 | Ex 2.6: the expectation of the discounted sum equals `v(k, z)` |
| [LogNormal](Overview/LogNormal.lean) | 10 | Ex 2.7: Gaussian log capital |
| [Equilibrium](Overview/Equilibrium.lean) | 11 | §2.3, Ex 2.8–2.10: competitive equilibrium and the welfare theorems |
| [EventTree](Overview/EventTree.lean) | 5 | Ex 2.5: contingency plans and the stochastic Euler equations |

## Build and verify

```sh
lake exe cache get
python scripts/verify.py
```

The verifier builds the library, freshly recompiles every contributed proof,
and audits each named declaration's axioms (only `propext`, `Classical.choice`
and `Quot.sound` are allowed). Warnings fail the check.
