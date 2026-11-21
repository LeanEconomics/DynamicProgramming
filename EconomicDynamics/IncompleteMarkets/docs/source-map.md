# Source map: Miao Chapter 17

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 17, Incomplete
Markets Models, pp. 559–586. Lean names are relative to `Miao.IncompleteMarkets`. The income
fluctuation problem reuses the Chapter 8 model `SIModel` (§8.3.2); the Aiyagari economy is
`AYEconomy`, the Huggett–Bewley economy `BWEconomy`, and the economy with aggregate shocks
`BWAggEconomy`. Departures from the book are in [corrections](corrections.md).

## Introduction and §17.1

### Chapter introduction, pp. 559–560

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 559–560 | Overview (history dependence, Aiyagari–Bewley–Huggett, plan of the chapter) | Not formalised: no mathematical claim |

### §17.1.1 Income fluctuation problem, pp. 560–562 (`AYHousehold`, `AYIncomeFluct`)

| Source | Claim | Lean |
| --- | --- | --- |
| (17.1)–(17.2), p. 560 | The budget `c_t + a_{t+1} = (1 + r)a_t + wl_t` is (8.3) with `R = 1 + r`, `y = wl` | `ay_Budget`, `eq_17_2` |
| p. 560 | By Theorem 8.3.1, no-Ponzi and `c ≥ 0` give `a_t ≥ −wl_min/r` (natural borrowing constraint) | `ay_natural_limit` (corrections 2) |
| (17.3b), p. 560 | `φ = min{b, wl_min/r}` (`r > 0`), `φ = b` (`r < 0`) | `ay_phi`, `eq_17_3b` (corrections 1) |
| (17.3a), p. 560 | `a_t ≥ −φ` may be imposed (it implies `a ≥ −b` and the natural limit) | `eq_17_3a` |
| p. 561 | Cash on hand `x = (1 + r)a + wl + φ`, `â = a + φ`, `x′ = (1 + r)â′ + wl′ − rφ`, `â′ ∈ [0, x]` | `ay_cash_on_hand` |
| p. 561 | Bellman equation in cash on hand, policy `A(x, l)` | `ay_BellmanCoh` |
| (17.4), p. 561 | Bellman equation in assets, policy `g(a, l)`; equivalent formulation | `ay_Bellman`, `eq_17_4` (corrections 3) |
| p. 561 | iid `l`: `l` can be removed as a state; the §8.3.2 solution solves the problem | `ay_bellmanCoh_of_SI` |
| p. 561 | `(x_t)` is a Markov process; stationary distribution of cash on hand | `ay_IsStationaryCoh` |
| p. 561 | `β(1 + r) < 1`: unique invariant measure `λ*` (Section 8.3, Proposition 8.3.1) | `ay_stationary_exists`, `S.proposition_8_3_1` |
| p. 561 | `β(1 + r) ≥ 1`: `x_t`, `a_t` diverge (so no invariant measure) | `ay_beta_R_lt_one` (no stationary distribution unless `β(1 + r) < 1`; corrections 4); pathwise facts in [Chapter 8](../../Applications/docs/source-map.md) (`SIModel.supermartingale_limit`, `proposition_8_3_2_i`, `lemma_8_3_4`) |
| p. 561 | `Ea(r, w) = E_{λ*}[A(x)] − φ` | `ay_EaIid`, `ay_EaIid_bounds` |
| p. 561 | Huggett (1993) two-state results; general Markov case unknown | Not formalised: cited, no claim proved in the book |
| p. 562 | Transition function `P(A × B, (a, l)) = 1_{g(a,l) ∈ A} Q(B, l)` | `ay_P`, `ay_P_apply`, `ay_P_markov` |
| p. 562 | `λ_{t+1}(A × B) = ∫ P(A × B, (a, l)) dλ_t` | `ay_lamSeq`, `ay_lamSeq_succ` |
| p. 562 | `Ea(r, w) = ∫ g dλ*` (= mean of current assets under (17.7)) | `ay_Ea`, `ay_Ea_eq_mean`, `ay_stationary_fst` |
| p. 562 | Weak convergence of `λ_t` to `λ*` "suppose" | Not formalised: assumed by the book (for iid shocks, `S.proposition_8_3_1`) |

### §17.1.2 Production, p. 562 (`AYFirm`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 562 | CRS technology, profits | `ay_CRS`, `ay_profit`, `ay_cd_crs` |
| (17.5)–(17.6), p. 562 | `F_K = r + δ`, `F_L = w` at the profit maximum | `eq_17_5_17_6`, `ay_isLocalMax_of_max` |
| p. 562 (implicit) | Euler's theorem, zero profits | `ay_euler_crs`, `ay_zero_profit` |
| p. 568 | Cobb–Douglas `F = AK^αL^{1−α}`, marginal products | `ay_cdF`, `ay_cdFK`, `ay_cdFL`, `ay_rpow_ratio`, `ay_cd_hasDerivAt_K`, `ay_cd_hasDerivAt_L`, `ay_cdFK_strictAnti` |

### §17.1.3 Stationary recursive equilibrium, pp. 562–564 (`AYEquilibrium`, `AYExistence`, `AYIncomeFluct`)

| Source | Claim | Lean |
| --- | --- | --- |
| Definition 17.1.1, p. 563 | Stationary recursive competitive equilibrium (i)–(vi), (17.7) | `AYEconomy`, `AYStationaryEqm`, `definition_17_1_1`, `ay_Stationary`, `eq_17_7` (corrections 5) |
| Definition 17.1.1 | The definition is satisfiable | `ay_exampleEconomy`, `ay_example_phi`, `ay_exampleEqm`, `ay_example_exists` |
| p. 563 | The resource constraint is redundant | `ay_resource_redundant` (corrections 6) |
| p. 563 | Aggregate labour is the mean of `l_t` | `ay_labor_iid`, `ay_stationary_snd`, `ay_stationary_snd_iid` |
| p. 563 | No general existence/uniqueness results | Not formalised: no claim |
| p. 564 | `K^d(r)` derived from (17.5) is downward sloping | `ay_Kd`, `ay_Kd_foc`, `ay_Kd_unique`, `ay_Kd_strictAnti`, `ay_Kd_continuousOn` |
| p. 564 | `w` is a continuous function of `r` | `ay_wage`, `ay_wage_continuousOn` |
| p. 564 | `g`, `λ*`, hence `Ea(r)`, continuous in `r`; `Ea → ∞` as `(1 + r)β ↑ 1`; `Ea → −b` for `r < 0` | Hypotheses of `ay_existence`, `ay_existence_cd` (corrections 7) |
| p. 564 (Figure 17.1) | Crossing by the Intermediate Value Theorem | `ay_existence`, `ay_existence_cd`, `ay_existence_example` |
| p. 564 | Possibly multiple crossings; "seldom happens" | Not formalised: no precise claim |
| p. 564 | Equilibrium rate below `ρ = 1/β − 1`, the complete-markets rate | `ay_rho`, `ay_complete_markets_rate`, `ay_beta_R_lt_one`, `ay_r_lt_rho`, `ay_existence` |
| p. 564 | Capital above the complete-markets level (precautionary saving) | `ay_overaccumulation` |

### §17.1.4 Computation and implications, pp. 564–569 (`AYComputation`, `AYFirm`, `AYExistence`)

| Source | Claim | Lean |
| --- | --- | --- |
| Step 1, p. 564 | `r⁰ ∈ (−δ, 1/β − 1)` | `ay_FK_pos_rate`, `ay_Kd_tendsto`, `ay_r_lt_rho` |
| Step 2, p. 566 | `w(r⁰)` from (17.6) | `ay_wage` |
| Steps 3–4, p. 566 | Solve (17.4) on a grid, compute `λ*(r⁰)` and `Ea(r⁰)` | Not formalised: computational (definitions `ay_Bellman`, `ay_Stationary`, `ay_Ea`) |
| Step 5, p. 566 | `K(r⁰) = F_K^{-1}(r⁰ + δ)` | `ay_Kd`, `ay_Kd_foc`, `ay_Kd_unique` |
| Step 6, p. 566 | Bisection update and its direction | `ay_bisect`, `ay_bisect_direction` |
| Step 7, p. 566 | Iterate to convergence | `ay_bisect_fixed` (fixed point = market clearing); iteration itself computational |
| p. 567 | Grid iteration of the distribution | `ay_gridUpdate`, `ay_gridUpdate_rect`, `ay_gridUpdate_mass` |
| p. 567 | Simulation method | Not formalised: computational |
| p. 567 | Ljungqvist–Sargent iteration on capital with damping | `ay_damp`, `ay_damp_fixed`, `ay_damp_between` |
| pp. 567–568 | Aiyagari's quantitative findings | Not formalised: computational |
| Footnote 2, p. 568 | Saving rate `δK/(AF(K, L)) = δα/(r + δ)` | `ay_saving_rate` (corrected), `ay_saving_rate_misprint` (corrections 8); higher under incomplete markets: `ay_overaccumulation` |
| p. 568 | Lorenz curve, `z_i` increasing, `z_n = 1` | `ay_lorenz`, `ay_lorenz_zero`, `ay_lorenz_n`, `ay_lorenz_mono`, `ay_lorenz_le_diag` |
| p. 568 | Gini = twice the area between Lorenz curve and diagonal | `ay_gini`, `ay_gini_eq_area` |
| p. 568 | `x_i ≥ 0` ⇒ Gini in `[0, 1]`; equality ⇒ 0 | `ay_gini_nonneg`, `ay_gini_le`, `ay_gini_equal`, `ay_sum_odd` |
| p. 568 | Complete concentration ⇒ Gini = 1 | False for finite `n`: `ay_gini_concentrated` (`1 − 1/n`), `ay_gini_concentrated_ne_one`, `ay_gini_concentrated_tendsto` (corrections 9) |
| Example 17.1.1, Figure 17.2, pp. 568–569 | Numerical example (`γ = 3`, Tauchen, mean of `l` = 1.0904, `b = 3, 5`) | Not formalised: computational |
| Figure 17.1, p. 565 | Determination of equilibrium | `ay_existence` (the argument it illustrates) |

### Exercises (p. 584; `AYLeisure`)

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.1 | Code the Aiyagari model and replicate | Not formalised: computational |
| Exercise 17.4 | Endogenous leisure: household problem | `ay_BellmanLeisure` |
| Exercise 17.4 | Intratemporal first-order condition `wl u_c = u_{1−n}` | `ex_17_4_foc` |
| Exercise 17.4 | Definition of stationary equilibrium | `AYLeisureEconomy`, `AYLeisureEqm`, `ex_17_4_firm` |
| Exercise 17.4 | The definition is satisfiable | `ay_leisureEconomy`, `ay_leisure_phi`, `ay_leisureEqm`, `ex_17_4` |

## §§17.2–17.3 and Exercises 17.2, 17.3, 17.5, 17.6

### §17.2.1 Risk-free rate (the Huggett economy), pp. 570–572

| Source | Claim | Lean |
| --- | --- | --- |
| p. 570 | Endowment economy: `e_t` Markov with kernel `Q`, `w = 1` | `BWEconomy` |
| (17.2)–(17.4), pp. 560–561 | The household's Bellman equation with rate `r`, limit `φ`, endowment `y` | `BWEconomy.Bellman` |
| (17.7)/(17.8), pp. 562, 570 | Stationary distribution `λ(A × B) = ∫ 1_A(g) Q(B, e) dλ` | `BWEconomy.Stationary` |
| p. 562 | `Ea(r) = ∫ g dλ*` (as a set over solutions and stationary distributions) | `BWEconomy.EaSet` |
| Definition 17.2.1, p. 570 | Stationary recursive competitive equilibrium (i)–(iii) | `BWHuggettEqm` |
| p. 571, Figure 17.3 | Equilibrium rate = intersection of `Ea(r)` with the vertical axis | `definition_17_2_1` |
| Definition 17.2.1 (instance) | A concrete equilibrium (two-state cycle economy, `φ = 1/4`, `r = 0`) | `bw_cycle_huggett`, `bw_cycle`, `bw_cycleV`, `bw_cycleG`, `bw_cycleLam`, `bw_cycle_bellman`, `bw_cycle_stationary`, `bw_cycle_mean`, `bw_cycle_EaSet`, `bw_cycle_Q`, `bw_cycle_integral`, `bw_cycleLam_isProb`, `bw_cycleLam_supp`, `bw_cycle_integrable` |
| p. 571 (proof of Prop. 17.2.1, general `r`) | `â = a + d`: limit `φ − d`, endowment `y − rd` | `bw_bellman_shift`, `bw_bellman_shift_iff`, `bw_stationary_shift`, `bw_supp_shift`, `bw_integrable_shift`, `bw_integral_shift`, `bw_isProb_shift`, `bw_EaSet_shift`, `bw_EaSet_shift_eq`, `bw_shift`, `bw_shift_apply` |
| Proposition 17.2.1, p. 571 | `r = 0`: policy for `â` independent of `b` | `proposition_17_2_1_policy` |
| Proposition 17.2.1, p. 571 | `Ea(0; b) = Ea(0; 0) − b` | `proposition_17_2_1` |
| (17.3), p. 560; p. 571 | A solution needs `rφ ≤ e(s)` (natural borrowing limit) | `bw_natural_limit` |
| p. 571, Figure 17.3 | `Ea(r)` shifts left as `b` rises; rate lower for smaller `b` | Not formalised: numerical (Example 17.1.1 parameters) |
| p. 571 | Rate below `1/β − 1` | `proposition_17_2_3_lt` (see Prop. 17.2.3) |
| pp. 571–572 | Inside money / free banking interpretation | Not formalised: interpretation |

### §17.2.2 Fiat money, pp. 572–573

| Source | Claim | Lean |
| --- | --- | --- |
| p. 572 | Mapping `m′/p = a′`, `w = 1`, `b = 0`, `r = 0` | `bw_fiat_budget` |
| p. 573 | `Ea(0) = M/p` determines `p` (quantity theory) | `bw_fiat_quantity_theory`, `bw_fiat_neutral` |
| p. 573 | Borrowing `b > 0` lowers `Ea(0)` and raises `p` | `bw_fiat_borrowing_raises_price` |
| p. 573 | `b > Ea(0; 0)` ⇒ `Ea(0; b) < 0`, fiat money driven out | `bw_fiat_driven_out` |
| §17.2.2 (instance) | Valued fiat money, `p = 4M`, in the cycle economy | `bw_cycle_fiat` |

### §17.2.3 Interest on currency, pp. 573–577

| Source | Claim | Lean |
| --- | --- | --- |
| (17.9), p. 573 | Government budget constraint | `eq_17_9` |
| (17.10), p. 574 | `τ = r̃M/p` | `eq_17_10` |
| p. 574 | Budget after substituting `τ` | `bw_bewley_budget` |
| pp. 574–575 | Mapping `â = m/p`, `φ = M/p`, `r = r̃` into (17.2) | `bw_bewley_mapping` |
| (17.11), pp. 574–575 | `E m′/p = M/p` iff `Ea(r̃) = 0` | `eq_17_11` |
| pp. 573–575 | Stationary Bewley equilibrium with interest on currency | `BWBewleyEqm`, `BWBewleyEqm.phi_pos`, `BWBewleyEqm.tau_eq` |
| Proposition 17.2.2, p. 575 | Same allocation and rate as Huggett with `φ = M/p` | `proposition_17_2_2`, `BWBewleyEqm.toHuggett` |
| p. 575, Steps 1–3 | Back-solving | `bw_backSolve`, `bw_backsolving` |
| p. 575 | Largest real balances `wl_min/r̃` | `bw_bewley_real_balances_le`, `bw_huggett_limit_le_natural` |
| §17.2.3 (instance) | A Bewley equilibrium exists in the cycle economy | `bw_cycle_bewley` |
| Proposition 17.2.3, p. 576 (first part) | Supportable rates = Huggett rates for limits `0 < φ ≤ e_min/r̃` | `proposition_17_2_3_rates` (the "highest = natural limit" part: not formalised, corrections 3) |
| Proposition 17.2.3, p. 576 (second part) | Rate below the rate of time preference | `proposition_17_2_3_lt`, `bw_cohStationary`, `bw_coh_lintegral`, `bw_coh_integral`, `bw_savc_continuous`, `bw_next_continuous`, `bw_sm_integral`, `bw_ae_ge` |
| p. 576 | `M_{t+1} = M_t(1+g)` in real terms | `bw_implicit_money` |
| p. 576 | Steady state: `1 + r = 1/(1 + g)` | `bw_implicit_rate` |
| p. 576 | `τ = −gM_t/p_t = (M_t/p_{t−1})r` | `bw_implicit_tax` |
| p. 576 | Budget = Huggett with `φ = M_t/p_{t−1}` | `bw_implicit_budget` |
| p. 577 | Money retired at rate `r/(1+r)`, deflation | `bw_implicit_deflation` |

### §17.2.4 Seigniorage, pp. 577–579

| Source | Claim | Lean |
| --- | --- | --- |
| p. 577 | Government budget in real terms | `bw_seign_budget` |
| p. 577 | `m̄ = −G/r` | `bw_seign_mbar` |
| p. 577 | `G > 0` ⇒ `r < 0`; hyperbola in the south-east quadrant | `bw_seign_neg_rate`, `bw_seign_hyperbola` |
| pp. 577–578 | `m̄ = M₀/p₀ + G` determines `p₀`; proportionality in `M₀` | `bw_seign_initial_price`, `bw_seign_quantity_theory` |
| p. 578 | Highest-return selection: raising `G` lowers `r` | `bw_seign_comparative_statics` |
| p. 577, Figure 17.4 | Possible multiplicity of equilibria | Not formalised: figure |
| pp. 578–579 | `b > 0` shifts `Ea` left, may eliminate all equilibria | Not formalised: figure (the `r = 0` shift is Prop. 17.2.1) |

### §17.3 Aggregate shocks, pp. 579–583

| Source | Claim | Lean |
| --- | --- | --- |
| p. 579 | `Y = zF(K, L)`, `(z, l)` Markov with `Q` | `BWAggEconomy`, `bw_aggK`, `bw_aggL` |
| Definition 17.3.1 (i), pp. 579–580 | Bellman equation with `λ′ = G(λ, z; z′)` | `BWAggEconomy.Bellman` |
| Definition 17.3.1 (iv), p. 580, as printed | Book's law of motion has mass `π(z′|z)` | `BWAggEconomy.BookLaw`, `bw_book_law_mass`, `bw_book_law_not_prob` |
| Definition 17.3.1 (iv), corrected | Conditional law of motion | `BWAggEconomy.Law`, `bw_law_isProb`, `bw_law_marginal` |
| Definition 17.3.1, p. 579 | Recursive competitive equilibrium (i)–(iv) | `BWRecEqm` |
| Definition 17.3.1 (instance) | A concrete recursive equilibrium | `bw_recEqm_example`, `bw_aggExample`, `bw_aggExample_Q` |
| p. 580 | Independent shocks ⇒ `G` independent of `z′` | `bw_law_indep` |
| pp. 580–581 | Recursive equilibrium induces a sequential equilibrium | `bw_sequential_of_recursive`, `bw_distPath`, `bw_assetPath` |
| p. 581 | Existence of recursive equilibrium open; Miao (2006), Kubler–Schmedders (2002) | Not formalised: cited results |
| p. 581 | Moments `m = (m₁, …, m_I)`, `m′ = H_I(m, z)` | `bw_moments`, `bw_moments_first` |
| (17.12), p. 581 | `ln K′ = b_{0z} + b_{1z} ln K` | `bw_ksLaw`, `eq_17_12` |
| p. 582 | Law does not depend on `z′` (capital predetermined) | `bw_next_capital_indep` |
| (17.13), p. 582 | Agent's problem with `(K, z)` and prices from FOCs | `bw_ksBellman`, `bw_ksR`, `bw_ksW`, `bw_ks_prices` |
| p. 582, Steps 1–4 | The KS iteration as a map (regression per `z`) | `bw_ksUpdate`, `bw_ksSample`, `bw_olsSlope`, `bw_olsIntercept`, `bw_mean` |
| p. 583, Step 5 | Consistency = fixed point | `bw_ksConsistent`, `bw_ks_fixed_point_of_exact`, `bw_ols_exact` |
| p. 583, Step 6 | `R²` | `bw_rsq`, `bw_rsq_exact`; adding moments: not formalised (computational) |
| p. 582, Step 3 | Simulation with `N = 100000`, `T = 2000`, `T₀ = 500` | Not formalised: computational |
| p. 583 | Reasons for approximate aggregation | Not formalised: qualitative |

### Exercises, pp. 584–585

| Source | Claim | Lean |
| --- | --- | --- |
| Exercise 17.2 | Compute the Huggett model | Not formalised: computational |
| Exercise 17.3 | Compute the Krusell–Smith model | Not formalised: computational |
| Exercise 17.5 | Endogenous leisure in KS: define a recursive equilibrium | `BWLeisureEqm`, instance `ex_17_5` |
| Exercise 17.6 | Primitives, CRRA economy | `BWImroParams`, `BWImroParams.toEconomy`, `BWImroParams.rate`, `BWImroParams.income` |
| Exercise 17.6 | Stationary inflation = money growth | `ex_17_6_inflation` |
| Exercise 17.6 (a) | The household's DP problem in real balances | `ex_17_6_a` (the DP is `BWEconomy.Bellman` for `toEconomy`) |
| Exercise 17.6 (b) | Stationary equilibrium | `BWImroEqm`, instance `ex_17_6_b`, `bw_imroExample`, `bw_imroExample_u`, `bw_imroExample_Q`, `bw_imroExample_rate`, `bw_imroExample_income`, `bw_sqrt_add_le` |
| Exercise 17.6 (c) | Computation, welfare cost of inflation | Not formalised: computational |
