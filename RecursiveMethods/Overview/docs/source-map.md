# Source map

Stokey and Lucas with Prescott, *Recursive Methods in Economic Dynamics* (Harvard University Press,
1989), Chapter 2, pp. 8–35. Lean names are relative to `StokeyLucasPrescott.Overview`. Where the
Lean statement departs from the book, see [corrections](corrections.md).

## §2.1 A deterministic model of optimal growth

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 9–10 | The technology `F`, the goods supply `f(k) = F(k, 1) + (1 − δ)k` | `Neoclassical`, `goods` |
| Ex 2.1, pp. 10–11 | `f` is C¹, strictly increasing, strictly concave, `f(0) = 0`, `f′ > 0`, `f′(0+) = ∞`, `f′(∞) = 1 − δ` | `Neoclassical.strictMonoOn_F`, `Neoclassical.F_pos`, `Neoclassical.strictConcaveOn_F`, `Neoclassical.f_zero`, `Neoclassical.hasDerivAt_f`, `Neoclassical.continuousOn_f'`, `Neoclassical.f'_pos`, `Neoclassical.strictMonoOn_f`, `Neoclassical.strictConcaveOn_f`, `Neoclassical.f'_tendsto_zero`, `Neoclassical.f'_tendsto_atTop` |
| — | The assumptions are consistent: Cobb–Douglas satisfies them | `cobbDouglas`, `cobbDouglas_neoclassical` |
| pp. 10–11 | With a finite horizon the problem (3)–(4) is solved by the first-order and boundary conditions (5)–(6), and the solution is unique | `concave_le_tangent`, `strictConcave_lt_tangent`, `sum_telescope`, `planValue`, `Feasible`, `euler_optimal`, `euler_unique` |
| Ex 2.2a, p. 12 | The change of variable `z_t = k_t/k_{t−1}^α` gives a first-order difference equation | `euler_iff_z` |
| Ex 2.2b, p. 12 | The unique solution with `z_{T+1} = 0` | `savingRate`, `savingRate_zero`, `savingRate_succ`, `savingRate_pos`, `savingRate_nonneg`, `savingRate_lt_one`, `z_unique` |
| Ex 2.2c, p. 12 | The path (7) satisfies (5)–(6) | `path`, `path_pos`, `path_terminal`, `path_consumption`, `path_feasible`, `path_euler`, `path_optimal`, `path_unique` |
| (8), p. 12 | As `T → ∞` the coefficient converges to `αβ` | `savingRate_tendsto` |
| Ex 2.3a, p. 14 | The value of (2) along (8) | `coefA`, `coefB`, `logValue`, `cdPath`, `cdPath_pos`, `logCapital`, `cdPath_consumption`, `hasSum_value` |
| Ex 2.3b, p. 15; (11), p. 14 | `v` satisfies the functional equation (11) | `bellmanRHS`, `bellman_le`, `bellman_attained`, `bellman_isGreatest`, `bellman_argmax_unique` |
| Ex 2.4a, p. 15 | Exactly one positive stationary point of `g = s f` | `SavingsMap`, `SavingsMap.pos_of_lt`, `SavingsMap.exists_unique_fixedPoint`, `SavingsMap.kstar`, `SavingsMap.kstar_pos`, `SavingsMap.g_kstar`, `SavingsMap.eq_kstar`, `SavingsMap.lt_of_lt_fixed`, `SavingsMap.gt_of_gt_fixed`, `SavingsMap.g_pos`, `Neoclassical.savings_above`, `Neoclassical.savings_below`, `Neoclassical.savings_crossings`, `Neoclassical.savings_unique_steady_state` |
| Ex 2.4b, p. 15 | Monotone convergence to `k*` from every `k₀ > 0`, not in finitely many periods | `SavingsMap.iterate_mem_below`, `SavingsMap.iterate_mem_above`, `SavingsMap.monotone_of_le`, `SavingsMap.antitone_of_ge`, `SavingsMap.limit_eq_kstar`, `SavingsMap.tendsto_fixedPoint`, `SavingsMap.iterate_eq_fixed_iff` |

## §2.2 A stochastic model of optimal growth

| Source | Claim | Lean |
| --- | --- | --- |
| Ex 2.5, p. 18 | The planner's decision variables and the Euclidean space of contingency plans | `finrank_plan` |
| Ex 2.5, p. 18 | The first-order conditions (here proved sufficient) | `sum_snoc`, `histProb`, `histProb_snoc`, `zOf`, `kIn`, `treeCons`, `fdIn`, `treeValue`, `TreeFeasible`, `sum_shift_telescope`, `tree_euler_optimal` |
| (3), p. 18; Ex 2.6, p. 19 | `v(k, z) = A + B ln k + C ln z` satisfies the functional equation (3) and (5) is the optimal policy | `log_tradeoff`, `log_tradeoff_unique`, `coefC`, `coefAs`, `stochValue`, `integral_stochValue`, `stochRHS`, `stochRHS_attained`, `stochRHS_eq`, `stoch_bellman_isGreatest`, `stoch_argmax_unique` |
| Ex 2.6, p. 19 | The value of the objective (2) under the policy (5) | `shock`, `stochPath`, `stochCons`, `shockMeasure`, `ae_shock_pos`, `integrable_log_coord`, `integral_log_coord`, `meanShock`, `integrable_log_shock`, `integral_log_shock`, `ae_log_path`, `meanLogK`, `integral_log_path`, `integral_log_cons`, `meanLogK_succ`, `hasSum_expected_utility`; the expectation of the sum: `ae_summable_utility`, `integrable_utility`, `hasSum_integral_utility`, `integral_tsum_utility`, `integral_utility_eq_stochValue` |
| Ex 2.7, p. 20 | `ln k_t` is normal; its means and variances and their limits | `capPath`, `logPath`, `log_capPath`, `constPath`, `logPath_eq`, `measurable_logPath`, `indepFun_logPath`, `meanN`, `sqNN`, `coe_sqNN`, `varN`, `hasLaw_logPath`, `meanN_eq`, `varN_eq`, `meanN_tendsto`, `varN_tendsto` |
| (6)–(9), pp. 20–21 | Transition functions, invariant distributions, laws of large numbers | Discussion only; developed in Chapters 8, 11–14. |

## §2.3 Competitive equilibrium growth

| Source | Claim | Lean |
| --- | --- | --- |
| (8)–(10), p. 25 | The firm's problem: factor prices equal marginal products and profits are zero | `firm_profit_le`, `firm_profit_zero` |
| (11)–(16), pp. 25–26 | The household's problem and the definition of competitive equilibrium | `utility`, `HHFeasible`, `HHBudget`, `IsEquilibrium` |
| pp. 26–27 | A competitive equilibrium allocation solves the planner's problem (first welfare theorem) | `first_welfare` |
| (17)–(22), p. 27; Ex 2.8, p. 28 | The planner's solution with the prices (20)–(22) is a competitive equilibrium | `priceP`, `priceP_pos`, `household_optimal`, `second_welfare` |
| Ex 2.9, p. 28 | Firms own the capital | `firmValue`, `firmOwned_firm_optimal`, `firmOwned_household_optimal` |
| Ex 2.10, p. 29 | Sequential markets with one-period bonds and perfect foresight | `pvPrice`, `SeqBudget`, `sequential_budget`, `sequential_household_optimal`, `sequential_planner_feasible` |
| (23)–(28), pp. 29–31 | The recursive competitive equilibrium | Not formalised here: it needs the dynamic programming theory of Chapter 4. |

## Not formalised

| Source | Content | Reason |
| --- | --- | --- |
| Ex 2.2a, Ex 2.4a–b | "Plot … on the same diagram" | Diagrams; the facts they illustrate are proved. |
| §2.4–2.5 | Plan of the book; bibliographic notes | No mathematical content. |
