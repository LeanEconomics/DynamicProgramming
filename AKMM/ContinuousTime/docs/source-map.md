# Source map: AKMM Chapter 9

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 9, Continuous-time analytical techniques, pp. 241–260, and Appendix 9.A,
pp. 843–848. Page references are the draft's running heads. Lean names are relative to
`AKMM.ContinuousTime`. Departures from the book are in [corrections](corrections.md).

## Introduction (pp. 241–242)

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 241–242 | Discrete vs continuous time, an intuitive overview | not formalised: narrative |

## §9.1, basic tools and notation (pp. 242–243) — `GrowthRates`

| Source | Claim | Lean |
| --- | --- | --- |
| (9.1)–(9.2), p. 242 | `X_t = (1 + γ)^t X_0` solves (9.1), and is the only nonvanishing solution | `eq_9_2`, `growthRates_discrete_unique` |
| (9.3)–(9.4), p. 242 | `X(t) = e^{γt}X(0)` solves (9.3): `Ẋ = γe^{γt}X(0) = γX` | `eq_9_4` |
| (9.3)–(9.4), p. 242 | (9.4) is the solution of (9.3) | `eq_9_4_unique`, `eq_9_3_unique` (via imported `SargentStachurski.ContinuousTime.eq_exp_of_hasDerivAt`) |
| (9.5), p. 243 | `Ẋ/X = d log X/dt` | `eq_9_5` |
| p. 243 | Constant growth: the log is a straight line, `log X(t) = γt + log X(0)` | `growthRates_log_exponential` |
| p. 243 | Growth accounting for `Y = zK^αL^{1−α}`: `log Y = log z + α log K + (1−α) log L`, `Ẏ/Y = ż/z + αK̇/K + (1−α)L̇/L` | `growthRates_growth_accounting`, `growthRates_growth_accounting_rate` |
| p. 243 | Plotting on a log scale; reference to Figure 2.1 and to (2.1) | not formalised: narrative |
| fn. 1, p. 243 | `log X_{t+1} − log X_t = log(1 + γ)`; `log(1 + x) ≈ x` | `growthRates_log_difference`, `growthRates_log_one_add_approx` |

## Appendices 9.A.1–9.A.2, logs and composite functions (pp. 843–844) — `GrowthRates`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 843 | Appendix header ("proofs of … Chapter 4") | corrected: copied from 4.A; no theorem |
| 9.A.1, p. 843 | `e^{log x} = x`, `log e^x = x`, `log(xy) = log x + log y`, `log x^α = α log x`, `d log x/dx = 1/x`, `de^x/dx = e^x` | `appendix_9A1` |
| 9.A.2, p. 843 | Chain rule; `d e^{γt}/dt = γe^{γt}` | `appendix_9A2_exp` |
| 9.A.2, p. 844 | `d log X(t)/dt = Ẋ/X` (printed with `d/dt X(t)` on the left) | corrected: `appendix_9A2_log` |

## §9.2, the discrete-time Hamiltonian (pp. 244–246) — `DiscreteHamiltonian`, `DiscreteOptimality`, `DiscreteBudget`

| Source | Claim | Lean |
| --- | --- | --- |
| (9.6)–(9.7), p. 244 | The finite-horizon consumption–saving problem | `discreteLagrangian`; feasibility as hypotheses of `discreteHamiltonian_finite_sufficient` |
| (9.8), p. 244 | The budget in difference form | `eq_9_8` |
| p. 244 | `H_t = β^t u(c_t) + μ_t(ra_t + w − c_t)`; `L = Σ H_t − Σ μ_t(a_{t+1} − a_t) + λa_{T+1}` | `discreteHamiltonian`, `discreteHamiltonian_lagrangian` |
| (9.9), p. 244 | `∂H_t/∂c_t = 0`, i.e. `β^t u'(c_t) = μ_t` | `eq_9_9` |
| (9.10), p. 245 | `∂H_{t+1}/∂a_{t+1} + μ_{t+1} − μ_t = 0`, i.e. `μ_t = (1 + r)μ_{t+1}` | `eq_9_10` |
| (9.11)–(9.13), p. 245 | `−μ_T + λ = 0`, `λa_{T+1} = 0`, so `β^T u'(c_T)a_{T+1} = 0` and `a_{T+1} = 0` | `eq_9_13` |
| (9.14), p. 245 | The Euler equation `u'(c_t) = β(1 + r)u'(c_{t+1})` | `eq_9_14` |
| p. 245 | `β^T u'(c_T) = u'(c_0)/(1 + r)^T`; (9.13) ⇔ `a_{T+1}/(1 + r)^T = 0` ⇔ `a_{T+1} = 0` | `discreteHamiltonian_marginal`, `discreteHamiltonian_tvc_iff` |
| p. 245 | "this characterizes the optimal paths": sufficiency | `discreteHamiltonian_finite_sufficient` (added: the book gives no proof) |
| p. 244 | The Kuhn–Tucker conditions are necessary | `discreteHamiltonian_euler_necessary`, `discreteHamiltonian_tvc_necessary` (direct perturbation `discreteOptimality_pc`, `discreteOptimality_pa`, with `discreteOptimality_perturb_budget`, `discreteOptimality_perturb_sum`, `discreteOptimality_perturb_pos`, `discreteOptimality_euler_of_localMax`) |
| (9.15), p. 246 | Infinite horizon with the nPg `lim a_{T+1}/(1 + r)^T ≥ 0` | hypothesis `hnpg` of `discreteHamiltonian_infinite_sufficient` |
| p. 246 | Finite horizon: `a_{T+1}/(1 + r)^T ≥ 0 ⇔ a_{T+1} ≥ 0` | `discreteBudget_finite_npg_iff` |
| p. 246 | Infinite horizon: the nPg is not `lim a_{T+1} ≥ 0`; example `a_t = a > 0` | corrected: `discreteBudget_npg_printed_example` (does not separate), `discreteBudget_npg_counterexample` (`a < 0`) |
| p. 246 | "We assume r is not too large"; Section 4.3.1 for why (9.15) | not formalised: refers to Ch. 4 |
| p. 246 | Infinite-horizon FOCs give the same Euler equation (necessity) | `discreteHamiltonian_euler_necessary_infinite` (for catching-up optimality) |
| p. 246 | TVC `lim β^T u'(c_T)a_{T+1} = 0` ⇔ `lim a_{T+1}/(1 + r)^T = 0` | `discreteHamiltonian_tvc_infinite_iff` |
| p. 246 | Euler and TVC characterize the infinite-horizon optimum (sufficiency) | `discreteHamiltonian_infinite_sufficient` (via imported `DPExtensions.EulerTransversality.finite_horizon_bound`); instance `discreteHamiltonian_constant_path_optimal` |
| p. 246 | Necessity of the infinite-horizon TVC | not formalised: the book gives no argument; for the consumption–saving problem with unbounded debt the general necessity results (Kamihigashi) do not apply as stated |

## §9.2, the continuous-time problem and discounting (pp. 246–248) — `ContinuousBudget`

| Source | Claim | Lean |
| --- | --- | --- |
| (9.16)–(9.17), pp. 246–247 | `ȧ = w + ra − c`, nPg `lim e^{−rT}a(T) ≥ 0` | `eq_9_17_budget` (with `R(T) = rT` and the budget identity) |
| p. 247 | Larger `ρ` means less weight on the future; larger `β` more | `eq_9_18` |
| (9.18), p. 247 | `β = 1/(1 + ρ)` | `eq_9_18` |
| box, p. 247 | `(1/(1 + ρΔ))^{t/Δ} → e^{−ρt}` as `Δ → 0` | `continuousBudget_discount_limit` |
| pp. 247–248 | The nPg discount `1/(1 + r)^T` maps to `e^{−rT}` by the same procedure | `continuousBudget_npg_discount_limit` |
| p. 248 | Time-varying nPg: discrete `lim a_{T+1}/∏(1 + r_t) ≥ 0`, continuous `lim e^{−∫_0^T r}a(T) ≥ 0` | `appendix_9A3_discrete_lbc_infinite`, `appendix_9A3_continuous_npg_iff_lbc` |

## Appendix 9.A.3, the nPg with time-varying interest (pp. 844–846) — `DiscreteBudget`, `ContinuousBudget`, `ProductLimits`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 844 | `a_{T+1}/∏_{t=1}^T(1 + r_t) = Σ_s w_s/∏ + (1 + r_0)a_0 − Σ_s c_s/∏` | `discreteDiscount`, `appendix_9A3_discrete_budget`, `discreteBudget_discount_pos`, `discreteBudget_const_discount` |
| p. 844 | The nPg guarantees the lifetime budget constraint, finite `T` | `appendix_9A3_discrete_lbc` (an equivalence) |
| p. 844 | The same as `T → ∞` | `appendix_9A3_discrete_limit`, `appendix_9A3_discrete_lbc_infinite`, `appendix_9A3_discrete_npg_iff_lbc` |
| pp. 844–845 | Subperiods of length `Δ`: `−log ∏(1 + r(tΔ)Δ) = −Σ log(1 + r(tΔ)Δ) ≈ −Σ r(tΔ)Δ → −∫_0^T r` | `productLimits_riemann`, `productLimits_product` (with the explicit error bound `2M²T²/n`) |
| p. 845 | `lim_{Δ→0} a(T + Δ)/∏(1 + r(tΔ)Δ) = e^{−∫_0^T r}a(T)`; with `T → ∞`, the nPg `lim e^{−∫_0^T r}a(T) ≥ 0` | `appendix_9A3_product_limit` (the discount factor; `a(T + Δ) → a(T)` by continuity) |
| p. 845 | `∂/∂t R`, the integrating factor `d/dt[e^{∫_t^T r}a] = e^{∫_t^T r}(ȧ − ra)` | `continuousBudget_hasDerivAt_cumulative`, `appendix_9A3_integrating_factor` (in the equivalent form with `e^{−∫_0^t r}`) |
| p. 845 | `a(T) − e^{∫_0^T r}a(0) = ∫_0^T e^{∫_t^T r}(w − c)dt` | `appendix_9A3_continuous_budget_forward` |
| p. 846 | `e^{−∫_0^T r}a(T) = …`, the continuous lifetime budget | corrected: `appendix_9A3_continuous_budget`; printed form false: `appendix_9A3_printed_budget_false` |
| p. 846 | As `T → ∞` the nPg is necessary for the lifetime budget constraint | corrected kernel; an equivalence: `appendix_9A3_continuous_npg_iff_lbc` |

## §9.2, the maximum principle (pp. 248–250) — `ContinuousHamiltonian`, `Mangasarian`

| Source | Claim | Lean |
| --- | --- | --- |
| (9.19), p. 248 | `H(t) = e^{−ρt}u(c) + μ(ra + w − c)` | `ctHamiltonian` |
| (9.20), (9.24), pp. 248–249 | `∂H/∂c = 0`, i.e. `e^{−ρt}u'(c) = μ` | `eq_9_20` |
| (9.21), (9.25), pp. 248–249 | `∂H/∂a + μ̇ = 0`, i.e. `rμ + μ̇ = 0`, `μ̇/μ = −r` | `eq_9_21` |
| p. 248 | TVC `lim e^{−ρT}u'(c(T))a(T) = 0` | hypothesis `htvc` of `mangasarian_consumption_saving` |
| p. 248 | (9.20)–(9.21) are the (necessary) first-order conditions | not formalised: Pontryagin's maximum principle (not in Mathlib); their sufficiency: `mangasarian`, `mangasarian_consumption_saving` |
| p. 248 | Heuristic derivation: the Lagrangian and integration by parts | `continuousHamiltonian_integration_by_parts` (on `[0, T]`); "taking first-order conditions" in function space not formalised (the heuristic step is Pontryagin) |
| box, p. 249 | Current-value Hamiltonian `Ĥ = u(c) + μ̂(ra + w − c)`; `μ = e^{−ρt}μ̂` | `ctCurrentHamiltonian`, `continuousHamiltonian_present_current` |
| (9.22)–(9.23), p. 249 | The current-value conditions correspond to (9.20)–(9.21) | `eq_9_22`, `eq_9_23` |
| (9.26), p. 249 | `−ρ + (u''/u')ċ = μ̇/μ = −r`, so `−(u''c/u')(ċ/c) = r − ρ` | `eq_9_26` (with time-varying `r`) |
| p. 249 | The coefficient of relative risk aversion is positive | `continuousHamiltonian_crra_coefficient_pos` |
| p. 249 | CRRA: `u(c) = (c^{1−σ} − 1)/(1 − σ)` has coefficient `σ` | `crraUtility`, `continuousHamiltonian_crra_derivs`, `continuousHamiltonian_crra_relative_risk_aversion` |
| box, p. 250 | Interpretation of (9.26): high `ρ`, low consumption growth | not formalised: narrative (the sign is `eq_9_26`) |
| box, p. 250 | First-order expansion of (9.14): `−(u''c/u')(Δc/c) = (r − ρ)/(1 + r)` | `continuousHamiltonian_discrete_euler_linearized`; with the `o(Δc)` remainder `continuousHamiltonian_discrete_euler_remainder` |
| pp. 248–249 | (9.20), (9.21) with the TVC solve the consumption–saving problem (sufficiency) | `mangasarian` (general concave problem, finite horizon), `mangasarian_catching_up`, `mangasarian_consumption_saving`; instance `mangasarian_consumption_saving_constant`; helper `mangasarian_exp_neg_tendsto` |

## §9.3.1, the Solow model (pp. 250–253) — `SolowContinuous`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 250 | Purpose of revisiting the Chapter 3–4 models | not formalised: narrative |
| p. 251 | `Y = F(K, AL)`, assumptions of Ch. 3 | hypotheses `hcrs` (constant returns) and EconomicGrowth's `Solow1956.Neoclassical.Technology` for `f(k) = F(k, 1)` |
| (9.27)–(9.30), p. 251 | `L̇/L = n`, `Ȧ/A = γ`, `K̇ = I − δK`, `I = sF` | hypotheses `h927`–`h929` of `eq_9_32`, `solowContinuous_convergence` |
| (9.31), p. 251 | `k̃̇/k̃ = K̇/K − Ȧ/A − L̇/L` | `eq_9_31` |
| p. 252 | `k̃̇/k̃ = (sF − δK)/K − γ − n`; `F(K, AL)/(AL) = f(k̃)`; `k̃̇/k̃ = sf(k̃)/k̃ − (δ + γ + n)` | `solowContinuous_intensive` |
| (9.32), p. 252 | `k̃̇ = sf(k̃) − (δ + γ + n)k̃` | `eq_9_32` (via `Solow1956.SolowSwan.hasDerivAt_capitalPerEffectiveWorker`) |
| fn. 2, p. 252 | Corresponds to (3.5), (3.7) | not formalised: cross-reference |
| Fig. 9.1, pp. 252–253 | Unique steady state; `k̃̇ > 0` below, `< 0` above; convergence from either side | `solowContinuous_phase_line` (via `Solow1956.Neoclassical.general_solow`, `rate_pos_below`, `rate_neg_above`) |
| p. 253 | Convergence regardless of the initial position, for the economy's `K/(AL)` | `solowContinuous_convergence` (via `Solow1956.Neoclassical.effective_labour_convergence`) |
| p. 253 | `Y/L = f(k̃)A`; on the BGP `Y/L` grows at `γ`; in the long run growth tends to `γ` | `solowContinuous_income_per_capita_growth` |
| p. 253 | "output per worker and capital per worker grow at constant rates … predictable and stable" | covered by `solowContinuous_income_per_capita_growth` for output; otherwise narrative |

## §9.3.2, the planner's problem (pp. 253–255) — `RamseyPlanner`, `Mangasarian`, `RamseySaddle`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 253 | No population growth or technical progress; Section 4.3.3 | not formalised: narrative |
| (9.33), p. 253 | `max ∫ e^{−ρt}u(c)` s.t. `k̇ = f(k) − δk − c`, `c, k ≥ 0`, `k(0)` given; no nPg needed | competitor hypotheses of `mangasarian_planner` (`k' ≥ 0`, `c' > 0`) |
| p. 254 | Hamiltonian and the necessary first-order conditions | sufficiency: `mangasarian_planner`; necessity: not formalised (Pontryagin) |
| (9.34), p. 254 | TVC `lim e^{−ρT}u'(c(T))k(T) = 0` | hypothesis `htvc` of `mangasarian_planner` |
| (9.35), p. 254 | CRRA: `ċ/c = (f'(k) − (δ + ρ))/σ` | `eq_9_35`; along the saddle path `ramseySaddle_path` |
| p. 254, Fig. 9.2 | `k̇ > 0` iff `c < f(k) − δk`; `ċ > 0` iff `k < k**`; `ċ = 0` at `k = k**` | `ramseyPlanner_phase_signs` |
| p. 255, fn. 3 | `k**` (modified golden rule) exists, is below the golden rule; the golden rule maximizes `f(k) − δk` | `ramseyPlanner_modified_golden_rule` (via `RamseyCassKoopmans.existsUnique_stationary_capital_of_inada`, `stationary_capital_lt_golden_rule_of_strictConcave`, `golden_rule_strictly_maximizes_consumption`) |
| p. 255 | The saddle path from `k(0)`: convergence to `(k̄, c̄)`, `k̄ = k**`, (9.A.1)–(9.A.2), TVC, optimality | `ramseySaddle_of_interior`, `ramseySaddle_path`, `ramseySaddle_crra_cobbDouglas` (for `k(0) ≤ k**`; see corrections) |
| p. 254 | The CRRA–Cobb–Douglas model satisfies the assumptions | `ramseySaddle_primitives` (with `ramseySaddle_power_hasDerivAt`, `ramseySaddle_power_derivs`, `ramseySaddle_power_props`) |
| p. 255 | The saddle path satisfies the TVC because `k, c` become constant | `ramseyPlanner_tvc_of_convergent`, `appendix_9A4_saddle_tvc` |
| p. 255 | Steady state optimal from `k**` | `mangasarian_planner_steady_state` |
| p. 255 | Higher `c(0)`: `k(t)` reaches `0`, the Euler path is infeasible | `ramseyPlanner_zero_capital_infeasible`; that the path reaches `k = 0` is a figure claim, deferred |
| p. 255 | Lower `c(0)`: `c → 0`, large `k`, TVC fails (Appendix 9.A.4) | `appendix_9A4_below_saddle_violates_tvc`; that the path enters `f'(k) < δ` is a figure claim, deferred |
| p. 255 | Over-accumulation "is a waste"; `c` lower than on the saddle path | not formalised: narrative / figure claim |

## Appendix 9.A.4, `c(0)` below the saddle path violates the TVC (pp. 846–848) — `RamseyPlanner`

| Source | Claim | Lean |
| --- | --- | --- |
| (9.A.1)–(9.A.2), p. 846 | First-order conditions of the planner | hypotheses `h9A1`, `h9A2` |
| p. 846 | `∂/∂t log u'(c) − ρ = μ̇/μ = −[f'(k) − δ]` | `eq_9_26` (general form) |
| (9.A.3), p. 846 | `log u'(c(T)) − log u'(c(0)) = −∫_0^T [f'(k) − (δ + ρ)]` | `appendix_9A4_marginal_utility` (third part) |
| (9.A.4), p. 847 | `u'(c(T)) = A exp(−∫_0^T [f'(k) − (δ + ρ)])` | `appendix_9A4_marginal_utility` (second part) |
| (9.A.5)–(9.A.6), p. 847 | TVC ⇔ `lim exp(−∫_0^T [f'(k) − δ])k(T) = 0` | `appendix_9A4_tvc_iff` |
| p. 847 | On the saddle path `∫(f' − δ) → ∞`, so (9.A.6) holds | `appendix_9A4_saddle_tvc` (corrected: `f'(k) − δ > ε`, not `f(k) − δ > ε`) |
| pp. 847–848 | Below the saddle path `f'(k) < δ` eventually, so (9.A.6) fails | `appendix_9A4_below_saddle_violates_tvc`, instance `appendix_9A4_below_saddle_instance`; entering the region: figure claim, deferred |
| p. 848 | "Another way of looking": `u'(c(T))` grows faster than `e^{−ρT}` decays; finite `u'(0)` reaches `c = 0` in finite time | not formalised: informal; the first part is equivalent to `appendix_9A4_tvc_iff` |

## §9.3.2, the market equilibrium (pp. 256–257) — `MarketEquilibrium`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 256 | Equivalence follows from the welfare theorems | the direct argument below; Cass's irreversible-investment version is EconomicGrowth's `RamseyCassKoopmans.second_welfare_theorem`, `first_welfare_theorem` (not restated) |
| (9.36), p. 256 | Household: `k̇_i = r k_i + w − δk_i − c_i`, `c_i, k_i ≥ 0` | hypotheses of `market_household_optimal` |
| (9.37), p. 256 | Household Euler equation `ċ_i/c_i = (r(t) − (δ + ρ))/σ` | `eq_9_37` |
| p. 256 | "Applying the same optimization steps" (household optimality) | sufficiency: `market_household_optimal`; necessity: not formalised (Pontryagin) |
| p. 256 | Firm FOCs `F₁ = r`, `F₂ = w`; `F₁ = f'(k̃)`, `F₂ = f(k̃) − k̃f'(k̃)` | `market_firm_marginal_products`, `market_firm_optimal` |
| p. 256 | Walras' law: two markets suffice | not formalised: narrative |
| (9.38)–(9.39), pp. 256–257 | `r = f'(k)`, `w = f(k) − kf'(k)` with `∫k_i = K`, `L = 1` | `market_firm_marginal_products` at `L = 1`; prices in `market_planner_is_equilibrium` |
| p. 257 | Substituting gives (9.33) and (9.35) | `market_equilibrium_planner_system` |
| p. 256 | The planner allocation coincides with the market equilibrium | `market_planner_is_equilibrium` (the planner's solution with prices (9.38)–(9.39) is optimal for households; firms: `market_firm_optimal`) |

## §9.4, uncertainty: the Poisson process (pp. 257–260) — `Poisson`, `Unemployment`, `ProductLimits`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 257–258 | Diffusions vs jump processes; applications (Chs. 13, 20) | not formalised: narrative |
| p. 258 | `n` trials with probability `λ/n`: expected successes `λ` | `poisson_expected_successes` |
| (9.40), p. 258 | `b(k, n) = C(n, k)(λ/n)^k(1 − λ/n)^{n−k}` is a probability distribution | `binomialProb`, `poisson_binomial_sum` |
| (9.41), p. 258 | `b(0, n) = (1 − λ/n)^n` | `eq_9_41` |
| (9.42), p. 258 | `b(k, n)/b(k − 1, n) = ((n − (k − 1))/k)((λ/n)/(1 − λ/n)) = (λ − (k − 1)λ/n)/(k − λk/n)` | `eq_9_42` |
| (9.43), p. 258 | `p(0) = lim b(0, n) = e^{−λ}` | `eq_9_43` |
| p. 258 | `lim b(k, n)/b(k − 1, n) = λ/k` | `poisson_ratio_limit` |
| p. 259 | `p(k) = e^{−λ}λ^k/k!` is the limit of `b(k, n)` | `poisson_limit` |
| p. 259 | `p(k)` are probabilities (sum to 1) | `poisson_sum_mean` |
| p. 259 | Poisson process: counts in `(t, t + T]` are Poisson(`λT`), mean `λT`; limit of trials of length `Δ = T/n` | `poisson_limit_interval` (the distributional statement); the process itself (independent increments): not formalised, not in Mathlib |
| p. 259 | Outcomes on disjoint intervals are independent; "the Poisson process is memoryless" | memorylessness of the waiting time: `poisson_survival_memoryless`, `poisson_memoryless_iff_exponential` (via `SargentStachurski.ContinuousTime.exp_memoryless`, `SargentStachurski.ContinuousTime.eq_exp_of_memoryless`); independent increments: not formalised (no Poisson process in Mathlib) |
| p. 259 | `λ ≤ 1` not needed: take `n` large | covered: `poisson_limit` holds for every real `λ` |
| p. 259 | No success in `(t, t + T]` with probability `e^{−λT}` | `poisson_survival_memoryless` |
| p. 259 | Time-varying `λ(s)`: `e^{−∫_t^{t+T} λ}` | `poisson_survival_time_varying` (hazard equation); as the limit of `∏(1 − λ(s_i)Δ)`: `productLimits_survival` |
| p. 259 | Job kept to `t` with probability `e^{−σt}`; separation density `e^{−σt}σ`; `∫_0^∞ tσe^{−σt}dt = 1/σ` | `poisson_expected_duration` |
| p. 259 | Law of large numbers for flows `u λdt`, `eσdt` | not formalised: the flow equation (9.44) is taken as the model |
| (9.44), p. 260 | `u̇ = (N − u)σ − uλ` | hypotheses of `unemployment_unique`; solution `unemployment_solution` |
| p. 260 | `ū = σN/(σ + λ)` | `unemployment_steady_state` |
| p. 260 | Convergence to `ū` regardless of `u(0)` | `unemployment_unique`, `unemployment_converges` |
| p. 260 | `ū/N = σ/(σ + λ)`, increasing in `σ`, decreasing in `λ` | `unemployment_steady_state`, `unemployment_rate_comparative_statics` |
| p. 260 | Discrete analogue in Ch. 20 | not formalised: cross-reference |
