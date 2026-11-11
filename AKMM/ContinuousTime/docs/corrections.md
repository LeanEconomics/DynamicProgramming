# Corrections and departures: AKMM Chapter 9

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 9, Continuous-time analytical techniques, pp. 241–260, and Appendix 9.A,
pp. 843–848. Lean names are relative to `AKMM.ContinuousTime`. Every book item is located in the
[source map](source-map.md).

## Corrections

1. **p. 844, Appendix 9.A.2, second example.** The book prints
   `d/dt X(t) = g'(f(t))f'(t) = … = Ẋ(t)/X(t)` for `Z(t) = log X(t)`. The left side should be
   `d/dt Z(t) = d/dt log X(t)`; `d/dt X(t)` is `Ẋ(t)`, not `Ẋ(t)/X(t)`
   (`appendix_9A2_log`, `eq_9_5`).

2. **p. 246, §9.2, the no-Ponzi example.** The book: "`lim a_{T+1}/(1 + r)^T ≥ 0` is not
   equivalent to `lim a_{T+1} ≥ 0` (consider the case where `a_t = a > 0` for all `t`; this
   satisfies the former inequality but not the latter inequality)". A constant positive asset
   satisfies both (`discreteBudget_npg_printed_example`). The separating example is a constant
   debt `a_t = a < 0` with `r > 0` (consumption `c_t = w + ra`): `a/(1 + r)^T → 0 ≥ 0`, but
   `lim a_t = a < 0` (`discreteBudget_npg_counterexample`).

3. **p. 846, Appendix 9.A.3, the continuous lifetime budget.** The book multiplies
   `a(T) − e^{∫_0^T r}a(0) = ∫_0^T e^{∫_t^T r}(w − c)dt` (correct:
   `appendix_9A3_continuous_budget_forward`) by `e^{−∫_0^T r}` and prints
   `e^{−∫_0^T r}a(T) = ∫_0^T e^{∫_t^T r}w dt + a(0) − ∫_0^T e^{∫_t^T r}c dt`, and the same kernel
   `e^{∫_t^T r}` in the limiting budget constraint. The kernel must be
   `e^{∫_t^T r}e^{−∫_0^T r} = e^{−∫_0^t r}`:
   `e^{−∫_0^T r}a(T) = a(0) + ∫_0^T e^{−∫_0^t r}(w − c)dt` (`appendix_9A3_continuous_budget`).
   The printed identity is false: with `r ≡ 1`, `w ≡ 1`, `c ≡ 0`, `a(t) = e^t − 1`, `T = 1`, its
   left side is `1 − e^{−1}` and its right side `e − 1` (`appendix_9A3_printed_budget_false`).
   The book also calls the nPg "necessary" for the lifetime budget constraint; given convergent
   integrals the two are equivalent, with equality iff `e^{−∫_0^T r}a(T) → 0`
   (`appendix_9A3_continuous_npg_iff_lbc`; discrete: `appendix_9A3_discrete_npg_iff_lbc`).

4. **p. 251, §9.3.1.** "Using the technique we learned in Section 10.1, we can obtain the growth
   rate of `k(t)`": the technique is that of Section 9.1, (9.5), and the variable is `k̃(t)`
   (`eq_9_31`, via `eq_9_5`).

5. **p. 847, Appendix 9.A.4.** "`f(k(t)) − δ > ε` is satisfied for a (small) `ε > 0`" should be
   `f'(k(t)) − δ > ε`; and "`k(T) → k*`" uses `k*` for the steady state called `k̄ = k**` in the
   main text (`appendix_9A4_saddle_tvc`). On p. 255, "eventually `(k(0), c(0))` reaches the
   region" should be `(k(t), c(t))`.

6. **p. 843, Appendix 9.A header.** "This Appendix includes the proofs of theorems and
   propositions in Chapter 4, and analyzes the NGM with a phase diagram" is copied from
   Appendix 4.A; Appendix 9.A covers logs and exponentials, the chain rule, the nPg with
   time-varying interest and the TVC below the saddle path. (No theorem.)

## Departures and additions

1. **§9.2, Kuhn–Tucker.** The book applies the Kuhn–Tucker theorem without stating its
   hypotheses or proving that the conditions characterize the optimum. Both directions are
   proved directly for the book's problem: sufficiency with `u` concave
   (`discreteHamiltonian_finite_sufficient`, `discreteHamiltonian_infinite_sufficient`) and
   necessity by a one-period perturbation (`discreteHamiltonian_euler_necessary`,
   `discreteHamiltonian_tvc_necessary`, `discreteHamiltonian_euler_necessary_infinite`). In the
   infinite horizon, optimality is catching-up optimality (no feasible path is eventually ahead
   by more than any `δ > 0`), which does not require lifetime utility to be finite; the nPg (9.15)
   is used in its `liminf` form. Necessity of the infinite-horizon TVC is not formalised.

2. **§9.2–9.3, the maximum principle.** The book presents (9.20)–(9.21), the TVC and their
   current-value forms as the conditions that characterize the optimum, derived heuristically.
   Mathlib has no Pontryagin maximum principle, so their *necessity* is not formalised. Their
   *sufficiency* is proved in the Mangasarian–Arrow form for every problem of the chapter
   (`max ∫ e^{−ρt}u(c)` with `ẋ = G(t, x) − c`, `u` and `G(t, ·)` concave): `mangasarian`,
   `mangasarian_catching_up`; for the household problem (9.16)–(9.17)
   (`mangasarian_consumption_saving`), the planner (9.33)–(9.34) (`mangasarian_planner`) and the
   decentralized household (9.36) (`market_household_optimal`). Optimality is catching-up
   optimality; when welfare limits exist it is the usual comparison of lifetime utilities. The
   first-order conditions themselves are proved as calculus identities (`eq_9_20`–`eq_9_26`).

3. **p. 255, the saddle path.** The book reads existence of the saddle path, convergence and
   the failure of the other paths off the phase diagram (Figure 9.2). Existence and convergence
   are imported from EconomicGrowth's `RamseyCassKoopmans`, which solves Cass's problem with
   irreversible gross investment `f(k) − c ≥ 0`; the book's planner may disinvest. Whenever the
   Cass optimum invests strictly throughout, it is shown to solve the book's problem
   (`ramseySaddle_of_interior`, via `mangasarian_planner`); this holds for every
   `0 < k(0) ≤ k**` (`ramseySaddle_path`), and for the book's Cobb–Douglas–CRRA model
   (`ramseySaddle_primitives`, `ramseySaddle_crra_cobbDouglas`). For `k(0) > k**` with large
   `k(0)` the Cass optimum has a zero-investment phase and the book's (disinvesting) saddle
   path is not constructed here: not formalised. The claims that a larger `c(0)` reaches
   `k = 0` and a smaller one enters `f'(k) < δ` are figure claims (deferred); what follows from
   them is proved (`ramseyPlanner_zero_capital_infeasible`,
   `appendix_9A4_below_saddle_violates_tvc`).

4. **§9.4, the Poisson process.** Mathlib has no Poisson process. The book's distributional
   statements are proved: the binomial limit (`poisson_limit`), the Poisson probabilities and
   mean (`poisson_sum_mean`, `poisson_limit_interval`), survival `e^{−λT}` and memorylessness
   of the waiting time (`poisson_survival_memoryless`, `poisson_memoryless_iff_exponential`),
   time-varying survival (`poisson_survival_time_varying`, `productLimits_survival`) and the
   expected duration (`poisson_expected_duration`). The process itself (independence of counts
   on disjoint intervals) and the law-of-large-numbers step to the flow equation (9.44) are not
   formalised; (9.44) is analysed as stated.

5. **Appendix 9.A.3, the discrete-to-continuous limit.** The book's "≈" steps are made
   precise with right-endpoint Riemann sums for continuous `r` and an explicit error bound
   (`productLimits_riemann`, `productLimits_product`, `appendix_9A3_product_limit`).
