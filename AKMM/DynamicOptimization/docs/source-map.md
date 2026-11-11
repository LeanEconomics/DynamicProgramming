# Source map: AKMM Chapter 4

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 4, Dynamic optimization, pp. 93–127, and Appendix 4.A, pp. 827–835. Page
references are the draft's running heads. Lean names are relative to `AKMM.DynamicOptimization`.
Departures from the book are in [corrections](corrections.md).

Reused from dependencies. SLP `DeterministicDP` (`StokeyLucasPrescott.DeterministicDP`):
`Feasible`, `vstar`, `total`, `SatisfiesFE`, `Assumption41`–`Assumption48`, `bellman`,
`bellman_contraction`, `theorem_4_2`, `theorem_4_4`, `theorem_4_6`, `theorem_4_7`, `theorem_4_8`,
`theorem_4_10`, `concave_le_fderiv`, `argmax`, `argmaxFn`, `obj`. SLP `DeterministicDynamics`
(`StokeyLucasPrescott.DeterministicDynamics`): `tangent_le`, `deriv_le_of_concave`,
`deriv_lt_of_strictConcave`, `Setting61`, `gpol`, `ex_6_1b`, `prop_6_1`. `EulerTransversality`
(`DPExtensions.EulerTransversality`): `Feasible`, `CatchingUp`, `partialValue`,
`euler_tvc_sufficient`, `GrowthModel`, `GrowthModel.growth_sufficient`,
`GrowthModel.steady_state_optimal`.

## Introduction and §4.1, a dynamic optimization problem (pp. 93–99) — `SequenceProblems`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 93–94 | Motivation, rational expectations, finite vs infinite lives | not formalised: narrative |
| (P1), p. 94 | The problem `max Σ βᵗF̂(y_t)`, `x_{t+1} = h(x_t, y_t) ∈ Γ(x_t)`; reduced form | `objective`, `FeasibleT` |
| p. 95 | Weierstrass: continuous `F`, compact nonempty constraint set ⇒ a maximum | `seq_weierstrass` (with `seq_objective_congr`) |
| p. 95 | Conditions (i)–(iii) suffice | corrected: `seq_weierstrass_counterexample`, `seqCounterGamma` |
| p. 95 | (ii) gives `y_t = ĥ(x_t, x_{t+1})` continuous | not formalised: `F` assumed continuous (corrections, item 1) |
| (P2), pp. 96–97 | Consumption–saving problem; `Γ(a) = [a̲, w + (1 + r)a]` | `cs_gamma_iff` |
| pp. 96–97 | Properties of `u`, additive separability, `a_{T+1} ≥ 0` | definitions; used as hypotheses throughout |
| (4.1)–(4.2), p. 98 | `c_t + k_{t+1} ≤ f(k_t) + (1 − δ)k_t` | `eq_4_2` |
| (4.3), p. 98 | The planner's problem; `Γ(k) = [0, f(k) + (1 − δ)k]` | `ngm_gamma_iff`, `NGMFeasible`, `ngmObjective` |
| p. 98 | The resource constraint holds with equality | `ngm_resource_binds` |
| p. 98 | Competitive allocations solve (4.3) | not formalised: Chapter 6 |

## §4.2.1, the two-period model (pp. 99–100) — `TwoPeriod`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 99 | Lifetime budget constraint `c₀ + c₁/(1 + r) = w₀ + w₁/(1 + r)` | `twoPeriod_lifetime_budget` |
| (4.4)–(4.6), pp. 99–100 | Kuhn–Tucker conditions (sufficient under concavity) | `eq_4_4_to_4_6`, `twoPeriodValue` |
| p. 100 | Interior case: Euler equation `u'(c₀) = β(1 + r)u'(c₁)` | `twoPeriod_euler` |
| p. 100 | `w₀ > w₁`, strictly decreasing `u'`, `β(1 + r) ≥ 1` ⇒ interior | `twoPeriod_interior` |
| p. 100 | `β(1 + r) = 1`: `c₀ = c₁ = (w₀ + βw₁)/(1 + β)`, `a₁ = (w₀ − w₁)/(2 + r) > 0` | `twoPeriod_closed_form`, `twoPeriod_closed_form_optimal` |
| p. 99 | "when `T = 2`" | corrections, item 2 (convention only) |
| fn. 3, p. 100 | General procedure: interior candidate, then check the constraint | not formalised: method |

## §4.2.2–4.2.3, Result 1 and the finite-horizon NGM (pp. 100–102) — `FiniteHorizon`, `FiniteInterior`

| Source | Claim | Lean |
| --- | --- | --- |
| Result 1, pp. 100–101 | Euler equation (i) and `x*_{T+1} = x̲` (ii) ⇒ maximizer | `result_1`, `result_1_of_antitone`, `result_1_F2_nonpos`, `finite_telescope`, `finite_fderiv_apply` |
| p. 101 | Second-order difference equation with `T + 2` conditions | covered by `ngm_finite_unique` |
| (P3), fn. 4, p. 101 | The NGM return is jointly concave; unique maximizer | `ngm_return_concave`, `ngm_return_strictConcave`, `finite_unique_max` |
| (4.7), (4.10), pp. 101–102 | First-order conditions; Euler equation at interior choices | `eq_4_10` (with `ngm_hasFDerivAt`) |
| (4.8)–(4.9), p. 102 | `µ_T > 0`, hence `k_{T+1} = 0` | `ngm_terminal_zero` |
| p. 102 | Inada conditions ⇒ `k_{t+1} > 0` for `t < T` | `ngm_finite_interior`, `ngm_objective_update` |
| p. 102 | FOCs sufficient; unique solution of (4.10) with `k_{T+1} = 0` | `ngm_finite_sufficient`, `ngm_finite_unique` |
| p. 102 | Interpretation of the Euler equation | not formalised: narrative |

## §4.2.4, Example 4.1, CRRA and the EIS (pp. 103–105) — `FiniteExample`, `CRRA`

| Source | Claim | Lean |
| --- | --- | --- |
| (4.11), p. 103 | Euler equation of Example 4.1 along the closed form; `k_{T+1} = 0` | `eq_4_11`, `example41Plan`, `example41_plan_succ`, `example41_plan_pos` |
| p. 103 | `k_T = (αβ/(1 + αβ))Ak_{T−1}^α`, `k_{T−1}` formula | `example41_kT`, `example41_kTminus1` |
| p. 103 | Geometric-sum form and the closed form of the saving rate | `example41Rate`, `example41_rate_geometric`, `example41_rate_recursion`, `example41_rate_zero`, `example41_rate_nonneg`, `example41_rate_pos`, `example41_rate_lt_one` |
| p. 103 | `c_t = ((1 − αβ)/(1 − (αβ)^{T−t+1}))Ak_t^α` | `example41_consumption_share` |
| pp. 103–104 | The plan solves (P3) | `example_4_1` |
| p. 104 | Saving rate depends on time but not on `k`; consumption not smoothed | covered by `example41Rate` (depends on `T − t` only); smoothing: narrative |
| fn. 5, p. 104 | `α = 1`: growth unless `βA = 1` | not formalised: aside |
| CRRA box, p. 104 | `σ → 1`: logarithmic utility | `crra`, `crra_tendsto_log` |
| CRRA box, p. 104 | `σ → ∞`: utility → 0 for all `c` | corrected: `crra_tendsto_zero_of_one_le`, `crra_tendsto_atBot_of_lt_one` |
| CRRA box, p. 104 | Leontief limit of the power transform | `crra_leontief_limit` (finite horizon) |
| p. 105 | EIS definition | used in `example42_eis` |
| Example 4.2, p. 105 | Repeated substitution `u'(c_t) = βˢu'(c_{t+s})R_{t,t+s}` | `example42_repeated` |
| Example 4.2, p. 105 | `c_{t+s}/c_t = (βˢ)^{1/σ}R^{1/σ}`, EIS `= 1/σ` | `example42_ratio`, `example42_eis` |
| p. 105 | Log utility: constant expenditure shares | `example42_log_shares` |
| p. 105 | `σ > 1`: `c_t` rises with `R`; `σ < 1`: falls | `example42_consumption`, `example42_income_effect`, `example42_substitution_effect` |
| p. 105 | `σ = 0`: infinite EIS, discontinuous investment | not formalised: limiting remark |
| p. 105 | CRRA the only utility with balanced growth | `theorem_4A_4` |

## §4.3.1, mathematical considerations (pp. 106–111) — `InfiniteHorizon`, `Proposition44`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 105–106 | Infinite horizons, dynastic altruism, game theory contrast | not formalised: narrative |
| p. 106 | Continuity/compactness in sequence spaces | not formalised: the book refers to SLP |
| p. 106 | Constant streams: bounded iff `β < 1` | `infinite_constant_summable_iff` |
| p. 107 | CRRA growth stream bounded iff `β(1 + γ)^{1−σ} < 1` | `infinite_growth_summable_iff`, `infinite_growth_term` |
| p. 107 | `σ < 1`: upper bound on `γ`; `σ > 1`: `γ > 0` fine, fast negative growth not | `infinite_growth_sigma_lt_one`, `infinite_growth_sigma_gt_one`, `infinite_growth_negative_fails` |
| fn. 9, p. 107 | Finite resources, Chapter 25 | not formalised: refers ahead |
| p. 107 | Borrowing constraints and the terminal constraint | narrative; see `ponzi_improvement` |
| pp. 107–108 | The Ponzi scheme improves any plan; no maximum | `ponziAssets`, `ponzi_improvement`, `ponzi_no_maximum` |
| (4.12), p. 108 | nPg condition | hypothesis of `eq_4_13` |
| p. 108 | Consolidation after `T` substitutions | `eq_4_13_finite` |
| (4.13), p. 108 | Lifetime budget constraint | `eq_4_13` |
| p. 108 | Natural borrowing limit; equivalence in 4.A.1 | `theorem_4A_3` |
| (4.14)–(4.15), pp. 108–109 | TVC; equality in the lifetime budget | `eq_4_14` |
| Example 4.3, p. 109 | `c_t = [β(1 + r)]ᵗc₀`, `c₀ = (1 − β)(1 + r)a₀`, optimal | `example_4_3_path`, `example_4_3_c0`, `example_4_3` |
| p. 110 | Necessity of the TVC | not formalised: not proved in the book (fn. 12); see EulerTransversality `growth_tvc_necessary` |
| Proposition 4.4, p. 110 | Euler + TVC + concavity ⇒ optimal | `proposition_4_4`, `proposition_4_4_F1_nonneg`; corrected: `proposition_4_4_counterexample`, `prop44CounterF` |
| p. 110 | NGM: `F₁ = u'(c)[f'(k) + 1 − δ]`, TVC in NGM form | `ngm_hasFDerivAt`, `proposition_4_4_ngm` |
| p. 111 | Stationary sequences satisfy the TVC automatically | `tvc_stationary`, `ngm_steady_state_optimal` |
| p. 111 | Balanced path: grows at `βγ^{1−σ}`; TVC iff `βγ^{1−σ} < 1` | `tvc_balanced_growth` |
| p. 111 | TVC vs nPg are distinct | not formalised: interpretation (both appear in `eq_4_14`) |

## §4.3.2, the infinite-horizon NGM (pp. 111–113) — `InfiniteNGM`

| Source | Claim | Lean |
| --- | --- | --- |
| (4.16), p. 111 | Steady state from the Euler equation; unique | `eq_4_16_of_euler`, `eq_4_16` |
| Example 4.5, pp. 111–112 | Limit of truncated solutions: (4.17) `k_{t+1} = αβAk_t^α` | `example_4_5_limit` |
| Example 4.5, p. 112 | TVC: `βᵗα/(1 − αβ) → 0` | `example_4_5_tvc` |
| Example 4.5 | (4.17) is optimal | `example_4_5` |
| Example 4.6, p. 112 | `s = αβ` verifies the guess | `example_4_6` |
| p. 112 | Converges to `k̄ = (αβA)^{1/(1−α)}` | `example_4_5_steady`, `example_4_5_convergence` |
| p. 113 | Numerical methods; phase diagram system | not formalised: method; system in `PhaseDiagram` |

## §4.3.3, balanced growth (pp. 113–114) — `BalancedGrowth`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 113 | Utilitarian vs per-capita welfare | not formalised: discussion (the difference is the discount factor, `adjustedDiscount`) |
| (4.18), p. 113 | Detrended resource constraint | `eq_4_18` |
| (4.19)–(4.20), p. 114 | Detrended objective with `β̃ = β(1 + n)(1 + γ)^{1−σ}` | `eq_4_19`, `adjustedDiscount` |
| p. 114 | CRRA the only form consistent with balanced growth | `theorem_4A_4` |
| p. 114 | Detrended Euler equation | `bgp_hasFDerivAt`, `bgp_euler_detrended` |
| p. 114 | With `β`, `1 + n` drops out | `bgp_euler_original` |
| p. 114 | BGP condition `(1 + n)(1 + γ) = β̃(f'(k̃) + 1 − δ)`; `n = γ = 0` | `bgp_condition`, `bgp_no_growth` |
| p. 114 | Cobb–Douglas `k̃` | `bgp_cobbDouglas` |

## §4.4.1–4.4.3, recursive methods and properties of V (pp. 114–120) — `Recursive`

| Source | Claim | Lean |
| --- | --- | --- |
| (4.21)–(4.22), pp. 115–116 | Principle of optimality: `V` solves the Bellman equation | `eq_4_22` |
| p. 117 | `V(x) = F(x, g(x)) + βV(g(x))` | `eq_4_22_policy` |
| p. 116 | Stationarity; finite horizon needs `V_t` | not formalised: discussion |
| (P4), p. 117 | Recursive NGM | instance of `eq_4_22` |
| p. 117–118 | Periodic NGM: recursive in `(k, parity)` | `periodicGamma`, `periodicF`, `periodic_bellman`; corrected: `periodic_printed_gamma` |
| p. 118 | Delayed depreciation: recursive in `(i', i)` | `delayedGamma`, `delayedF`, `delayed_bellman`; corrected: `delayedPrinted`, `delayed_no_discount_not_contraction` |
| pp. 118–119 | Sequence and recursive methods equivalent | not formalised: the book defers to SLP (`theorem_4_2`–`theorem_4_5` there) |
| fn. 13, p. 119 | Discrete choice conditions | not formalised: aside |
| Property 1, p. 119 | VFI converges; `‖V_{n+1} − V‖ ≤ β‖V_n − V‖` | `property_1` |
| fn. 14–15, p. 119 | Sup norm; contraction for `β < 1` | `property_1` (via `bellman_contraction`); fn. 14 corrected (item 11) |
| Property 2, p. 120 | `V` strictly increasing | `property_2` |
| Property 3, p. 120 | `V` strictly concave; unique policy | `property_3` |
| Property 4, p. 120 | `V` differentiable at interior choices | `property_4` |
| Property 5, p. 120 | `g` strictly increasing | corrected: `property_5_counterexample`, `prop5F`, `property_5_corrected`, `property_5_ngm` |
| p. 120 | Proof sketches of properties 1–5 | the cited SLP proofs |

## §4.4.4–4.4.5, solving for V and the functional Euler equation (pp. 120–123) — `ValueFunctionExamples`

| Source | Claim | Lean |
| --- | --- | --- |
| (4.23), p. 121 | `V₁(k) = log A + α log k` | `eq_4_23` |
| Example 4.7, p. 121 | FOC of `V₂`; `V₂ = a₂ + b₂ log k` | `vfe_log_max`, `example_4_7_V2` |
| Example 4.7, p. 121 | `V_n = a_n + b_n log k` for all `n`, converging | `example_4_7_iterate`, `example_4_7_coefficients` |
| Example 4.7, p. 121 | Guess and verify: `a`, `b` as printed; policy `αβAk^α` | `example_4_7` |
| (4.24), p. 122 | `V(x) = F(x, g(x)) + βV(g(x))` | `eq_4_22_policy` |
| p. 122 | Envelope theorem `V'(x) = F₁(x, g(x))` | `property_4` |
| (4.25), p. 122 | Functional Euler equation | `eq_4_25` |
| p. 123 | Functional Euler equation not a contraction; multiple solutions | local multiplicity: `slopeRoot_isRoot`, `slopeRoot_mem`; the rest is discussion |
| Example 4.8, p. 123 | `g(k) = sAk^α` solves (4.25) iff `s = αβ` | `example_4_8` |

## §4.4.6, dynamics (pp. 123–127) — `NGMDynamics`, `PolicySlope`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 123–124 | `k^u`: unique positive solution of `f(k) + (1 − δ)k = k`; `k ≤ k^u` stays below | `ngm_max_capital` |
| (4.26), p. 124 | Functional Euler equation of the NGM | `eq_4_26` |
| (4.27), p. 124 | Steady state `1 = β(f'(k̄) + 1 − δ)` | `eq_4_27` |
| fn. 16, p. 124 | `u(f(k) + (1 − δ)k − k')` concave | `ngm_return_concave`, `ngm_return_strictConcave` |
| (4.28), p. 124 | `u'(c)[f'(k) + 1 − δ − 1/β][k − g(k)] ≤ 0` | `eq_4_28` (corrected argument of `u'`) |
| p. 124 | `k > k̄ ⇒ g(k) < k`, `k < k̄ ⇒ g(k) > k` | `ngm_policy_direction` |
| p. 124 | Global monotone convergence to `k̄` | `ngm_global_convergence`; for `δ = 1` unconditional: `ngm_global_convergence_full` |
| p. 125 | Linear approximation, `a₀ = k̄(1 − a₁)` | by definition of the tangent line; `g'(k̄) = a₁` is the hypothesis of `eq_4_29` |
| (4.29), p. 125 | Differentiating (4.26) at `k̄` | `eq_4_29`, `eq_4_29_quadratic` |
| p. 125 | Two real roots, one in `(0, 1)`, the other above 1 | `slopeRoot`, `slopeRootOther`, `slopeRoot_disc_nonneg`, `slopeRoot_isRoot`, `slopeRoot_sqrt_pos`, `slopeRoot_eq`, `slopeRoot_mem` |
| (4.30), p. 125 | `a₁ ∈ (0, 1]`, decreasing in `Θ`, `= 1` at `Θ = 0`, `→ 0` as `Θ → ∞` | `slopeRoot_mem`, `slopeRoot_zero`, `slopeRoot_strictAnti`, `slopeRoot_tendsto_zero`, `slopeRoot_tendsto_one` |
| p. 125 | Only the root below one solves the Bellman equation | not formalised: the book asserts it; in SLP's setting `DeterministicDynamics.growth_policy_deriv` gives `g'(k*) = λ₁` |
| p. 126 | Higher-order approximations | not formalised: methodological remark |
| p. 126 | Calibration: empirical EIS (Hall; Attanasio–Weber), applied `σ` | not formalised: data |
| p. 126 | CRRA: `Θ = −β²f''(k̄)(f(k̄) − δk̄)/σ`, positive, decreasing in `σ` | `theta_crra`, `theta_crra_strictAnti` |
| p. 126 | `σ → 0`: `Θ → ∞`, `a₁ → 0`; `σ → ∞`: `Θ → 0`, `a₁ → 1` | `crra_slope_limits` |
| pp. 126–127 | Cobb–Douglas `Θ`; decreasing in `α`, increasing in `δ` | `theta_cobbDouglas`, `thetaCD`, `thetaCD_pos`, `theta_cobbDouglas_strictAnti_alpha`, `theta_cobbDouglas_strictMono_delta` |
| p. 127 | Slower convergence for `α` near 1 and small `δ` | `cobbDouglas_slope_mono` |
| §4.5, p. 127 | Concluding remarks | not formalised: narrative |

## Appendix 4.A.1, Theorem .3 (pp. 827–829) — `BorrowingConstraints`

| Source | Claim | Lean |
| --- | --- | --- |
| (4.A.1)–(4.A.2), p. 827 | Flow budget; combination up to `T` | `eq_4A_2`, `appendix_4A_partial` |
| p. 827 | `lim a_{T+1} ≥ 0` too restrictive | `appendix_4A_too_restrictive` |
| (4.A.3)–(4.A.5), p. 827 | nPg, lifetime budget, natural borrowing limit | statements in `theorem_4A_3` |
| p. 827 | nPg prevents the Ponzi scheme | `ponzi_improvement` (the scheme lowers the nPg limit by `ε`) |
| Theorem .3, pp. 828–829 | (i) ⇔ (ii) ⇔ (iii) | `theorem_4A_3` |
| (4.A.6)–(4.A.7), fn. 30 | Steps of the proof | inside `theorem_4A_3` |

## Appendix 4.A.2, Theorem .4 (pp. 829–830) — `BalancedGrowthCRRA`

| Source | Claim | Lean |
| --- | --- | --- |
| p. 829 | Balanced growth: `r` constant | premise |
| p. 830 | `u'((1 + γ)c)/u'(c) = (1 + r)/β` | corrected: `bgp_marginal_ratio` |
| Theorem .4, pp. 829–830 | Balanced growth for every `γ` ⇒ `u = log c` or `c^{1−σ}/(1 − σ)`, `σ > 0` | `theorem_4A_4`, `crraBGP_const`; corrected: `theorem_4A_4_sigma_pos`, `theorem_4A_4_affine_counterexample`, `theorem_4A_4_convex_example` |
| fn. 31, p. 830 | l'Hôpital: `(c^{1−s} − 1)/(1 − s) → log c` | `crra_tendsto_log` |

## Appendix 4.A.3, proof of Proposition 4.4 (pp. 830–831) — `Proposition44`

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 830–831 | Concavity bound, telescoping, Euler equation, TVC | `proposition_4_4` (via EulerTransversality's `euler_tvc_sufficient`); finite form `finite_telescope` |
| p. 831 | Last inequality needs `x_{T+1} ≥ 0` | corrected: `proposition_4_4_counterexample` |
| p. 831 | Finite horizon: `x*_{T+1} = 0` | `result_1`, `ngm_terminal_zero` |

## Appendix 4.A.4, the phase diagram (pp. 831–835) — `PhaseDiagram`

| Source | Claim | Lean |
| --- | --- | --- |
| (4.A.8)–(4.A.12), pp. 831–832 | `k` rises/stays/falls below/on/above `c = f(k) − δk` | `eq_4A_12` |
| (4.A.13), pp. 832–833 | `c` rises iff `k_{t+1} < k̄` iff `c_t > f(k_t) − δk_t + (k_t − k̄)` | `eq_4A_13` |
| p. 832 | Golden rule maximizes `f(k) − δk` | `golden_rule` |
| p. 834 | `k̄ < k^G` | `steady_below_golden` |
| Figs. .1–.3 | Shapes of the loci, the phase diagram | figure claim, deferred |
| p. 834 | Saddle-path dynamics; convergence iff on the saddle path | figure claim, deferred (existence asserted, not proved; for the optimum see `ngm_global_convergence_full`) |
| p. 834 | Above the saddle path: `k` reaches 0 in finite time | `phase_above_saddle_infeasible` (region entry: figure claim, deferred) |
| p. 834 | Below the saddle path: TVC fails | `phase_tvc_identity`, `phase_return_below_one`, `phase_below_saddle_violates_tvc`; corrected index: `phase_tvc_printed_differs` |
| p. 834 | The saddle path satisfies the TVC | `phase_saddle_tvc` |
| p. 835 | Why `k̄ < k^G`: discounting | not formalised: interpretation |
