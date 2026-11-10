# Source map: Miao Chapter 18

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 18, Search and
Matching Models of Unemployment, pp. 587–614. Lean names are relative to `Miao.SearchAndMatching`.
The chapter has no numbered results; its derivations are located by equation number and page. The
basic DMP model is built on `DMMatchingFn`; the job-destruction model on the option-value integral
`jd_Phi`. Departures from the book are in [corrections](corrections.md).

## Introduction and §18.1

### Chapter introduction, pp. 587–588

| Source | Claim | Lean |
| --- | --- | --- |
| pp. 587–588 | Limits of the neoclassical labour market (labour wedge, hours vs unemployment), DMP overview, later literature | Not formalised: empirical/historical, no mathematical claim |

### §18.1 Setup and the matching function, pp. 588–589 (`DMMatching`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 588 | Linear utility `Σ βᵗC_t`, CRS technology with productivity `A`, one worker per firm, vacancy cost `κ`, separation `ρ` | Parameters of the theorems below |
| p. 589 | `M(u, v)` increasing, concave, linearly homogeneous | `DMMatchingFn` (corrections 1); instance `dm_cdMatching` (`dm_cd_homog`, `dm_cd_concave`) |
| (18.1), p. 589 | `q^v = M(u, v)/v = q(θ)`, `q^u = M(u, v)/u = q(θ)θ` | `dm_q`, `dm_M_eq_mul_q`, `eq_18_1`, `dm_jobFinding`, `dm_q_pos` |
| p. 589 | `q′(θ) < 0`, `d ln q/d ln θ ∈ (−1, 0)` | `dm_q_hasDerivAt`, `dm_Mu_pos`, `dm_Mu_mul_lt`, `dm_q_elasticity` (corrections 2) |
| p. 589 | Tighter market: harder for firms, easier for workers | `dm_q_strictAntiOn`, `dm_jobFinding_strictMonoOn` |
| (18.2)–(18.3), p. 589 | Employment dynamics, `u_t = 1 − N_t` | Clauses of `dm_IsSearchEqm`; used in `eq_18_21` |
| p. 589 | (auxiliary) `q` continuous, slices of `M` concave | `dm_q_continuousOn`, `dm_concave_u` |
| p. 589 | Cobb–Douglas `q(θ) = μθ^{−α}` | `dm_cd_q`, `dm_cd_hasDerivAt` |

### §18.1 Bellman equations, bargaining and the wage, pp. 590–592 (`DMBellman`)

| Source | Claim | Lean |
| --- | --- | --- |
| (18.4)–(18.6), p. 590 | Filled-job and vacancy values; free entry gives `J^F_{t+1} = κ/(βq^v_t)` | `eq_18_6` |
| (18.7), p. 590 | `J^F_t = A − w_t + (1 − ρ)κ/q^v_t` | `eq_18_7` |
| (18.8), p. 590 | Job creation equation | `eq_18_8` |
| (18.9)–(18.10), p. 590 | Worker and unemployed values | Hypotheses of `eq_18_14`, `eq_18_15` |
| (18.11), pp. 590–591 | Nash bargaining; FOC `ηJ^F = (1 − η)(J^W − J^U)` | `dm_amgm2_strict`, `dm_nash_bound`, `dm_nash_solution`, `eq_18_11` (corrections 3) |
| (18.12)–(18.13), p. 591 | Surplus sharing; `(1 − η)S_{t+1} = κ/(βq^v_t)` | `dm_surplus`, `eq_18_12`, `eq_18_13` |
| (18.14), p. 591 | Surplus equation (three lines) | `eq_18_14` |
| p. 591 | `ηS_t = w_t − b + β(1 − ρ − q^u_t)ηS_{t+1}` | `dm_worker_surplus` |
| (18.15), p. 591 | `w_t = η(A + κθ_t) + (1 − η)b` | `eq_18_15` |
| p. 591 | Every match offers the same wage | Immediate from `eq_18_15` (depends on aggregates only); not stated separately |
| p. 592 | Definition of a search equilibrium | `dm_IsSearchEqm`; Bellman equations imply it: `dm_bellman_implies_eqm` |

### §18.1 Steady state, pp. 592–594 (`DMSteadyState`)

| Source | Claim | Lean |
| --- | --- | --- |
| (18.16), p. 592 | Steady-state job creation; the JC curve slopes down | `eq_18_16`, `dm_jcCurve`, `dm_jc_iff`, `dm_jc_strictAntiOn` |
| (18.17), pp. 592–593 | Wage curve, slopes up | `dm_wageCurve`, `eq_18_17`, `dm_wc_strictMono` |
| (18.18), p. 593 | `θ*` is the unique solution of (18.18) | `dm_ssLHS`, `eq_18_18`, `dm_wc_eq_jc`, `dm_ssLHS_strictMonoOn`, `dm_ss_unique`, `dm_ss_exists`, `dm_ss_not_exists`, `dm_cd_ssLHS`, `dm_cd_ss_existsUnique` (corrections 4) |
| (18.19), p. 593 | Beveridge curve; `u*` on the JC line `v = θu` | `eq_18_19`, `dm_uStar`, `dm_uStar_mem` |
| p. 593 | Beveridge curve downward sloping and convex | `dm_beveridge_anti`, `dm_beveridge_convex` (in `DMMatching`) |
| p. 593 | Higher `A`: JC shifts by more than WC; `θ`, `w`, `v` rise, `u` falls | `dm_cs_shifts`, `dm_cs_A`, `dm_uStar_strictAntiOn`, `dm_vStar_strictMonoOn` |
| pp. 593–594 | Higher `b`: `w` up, `θ` down, `u` up, `v` down | `dm_cs_b` |
| p. 594 | Higher `η`: similar result | `dm_cs_eta` (needs `A > b`) |
| p. 592 | Steady state is a search equilibrium; existence in an example | `dm_steady_isSearchEqm`, `dm_searchEqm_exists` |
| Figures 18.1–18.2 | Diagrams | Content formalised by the rows above |

### §18.1 Transitional dynamics, pp. 594–596 (`DMDynamics`)

| Source | Claim | Lean |
| --- | --- | --- |
| (18.20), p. 594 | Dynamic job creation equation | `eq_18_20` |
| (18.21), p. 594 | `u_{t+1} = (1 − ρ − q(θ_t)θ_t)u_t + ρ` | `eq_18_21` |
| p. 595 | Linearisation, `a₁₁` | `dm_a11`, `dm_lin_a11` |
| p. 595 | `a₂₁ = uq(θ*)[1 − ξ(θ*)]`, `a₂₁ > 0` | `dm_a21`, `dm_a21_sign` (corrections 5) |
| p. 595 | `a₂₂ = 1 − ρ − q(θ*)θ* ∈ (−1, 1)` | `dm_a22`, `dm_a22_mem` (corrections 6) |
| p. 595 | `ξ(θ) ∈ (0, 1)`; `(θq(θ))′ = q(θ)(1 − ξ(θ))` | `dm_xi`, `dm_xi_mem`, `dm_cd_xi`, `dm_jobFinding_hasDerivAt` |
| p. 595 | `1 − ρ − ηqθ/ξ > 0` implies `a₁₁ > 1` | `dm_a11_xi`, `dm_a11_gt_one` |
| p. 595 | Steady state is a local saddle; `θ_t` constant | `dm_saddle_path` (corrections 7) |
| p. 595, Fig. 18.3 | `Δu = 0` downward sloping, `Δθ = 0` horizontal | `dm_du_locus`, `dm_dtheta_locus` |
| p. 595 | `θ` jumps to the saddle path; `u_t` falls to the steady state | `dm_uPath`, `dm_uPath_rec`, `dm_uPath_sub`, `dm_uPath_tendsto`, `dm_uPath_mem`, `dm_uPath_strictAnti`, `dm_transition_isSearchEqm`, `dm_transition_not_monotone` (corrections 8) |
| pp. 595–596, Fig. 18.4 | Vacancies jump above `v*` and then fall | `dm_v0_gt`, `dm_vPath_strictAnti` |

### §18.1 Large firms, pp. 596–598 (`DMLargeFirm`)

| Source | Claim | Lean |
| --- | --- | --- |
| (18.22), p. 596 | Firm-level employment dynamics | `dm_FirmFeasible` |
| p. 597 | Aggregate law of motion is (18.2) | `dm_aggregate_18_2` |
| p. 597 | Firm's problem | `dm_firmProfit`, `dm_FirmOptimal` (corrections 9) |
| (18.23), p. 597 | FOCs; combined they give (18.8) | `eq_18_23`, `dm_firm_euler`, `dm_largeFirm_eq_18_8` |
| p. 597 | (18.23) plays the role of free entry | `dm_firmOptimal_of_euler`, `dm_firmOptimal_exists` |
| (18.24), p. 597 | Bellman equation, envelope `∂J_t/∂N = J^F_t` | `eq_18_24` |
| (18.25), pp. 597–598 | Marginal value of extra workers, `J_n(w, t)` | `dm_Jn` |
| (18.26), p. 598 | Large-firm bargaining equivalent to (18.11) | `eq_18_26` |
| (18.27), p. 598 | Simpler bargaining problem | `eq_18_27` |

### §18.1 Efficiency, pp. 598–599 (`DMEfficiency`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 599 | Planner's problem, FOC for `v_t` | `dm_planner_foc_v` |
| p. 599 | FOC for `N_t` | `dm_planner_foc_N`, `dm_planner_foc_N_misprint` (corrections 10) |
| (18.28), p. 599 | Planner's steady-state condition | `dm_plannerLHS`, `eq_18_28` |
| p. 599 | `ξ(θ) = η` implies efficiency (Hosios) | `dm_hosios`, `dm_cd_plannerLHS`, `dm_cd_planner_existsUnique`, `dm_cd_hosios_iff` (corrections 11) |
| p. 599 | `ξ`, `1 − ξ` are elasticities of expected durations | `dm_xi_duration` |
| p. 599 | High `ξ`: firms over-congest, workers' share should rise | `dm_cd_hosios_compare` |
| p. 599 | "If and only if `ξ(θ) = β`" | `dm_hosios_misprint` (corrections 12) |

### Exercise 18.1, p. 614 (`DMExercise1`)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex. 18.1 | Households trade shares: pricing equation, converse, price = PV of dividends | `dm_hhCons`, `dm_Ex1HHOptimal`, `dm_ex1_share_euler`, `dm_ex1_hhOptimal_of_euler`, `dm_ex1_price` |
| Ex. 18.1 | Firms own capital: investment Euler, job creation, wage | `dm_ex1Div`, `dm_Ex1Feasible`, `dm_Ex1FirmOptimal`, `dm_ex1_capital_euler`, `dm_ex1_job_creation`, `dm_ex1_wage` |
| Ex. 18.1 | Define a search equilibrium | `dm_Ex1IsSearchEqm` |
| Ex. 18.1 | Analyse it (Cobb–Douglas production steady state) | `dm_ex1_FK`, `dm_ex1_FN`, `dm_ex1_kstar`, `dm_ex1_kstar_unique`, `dm_ex1_steady`, `dm_ex1_steady_isSearchEqm`, `dm_ex1_searchEqm_exists` (corrections 13) |

### Exercise 18.2, p. 614 (`DMExercise2`)

| Source | Claim | Lean |
| --- | --- | --- |
| Ex. 18.2 | Planner's problem for §18.2 and its FOCs | `dm_mpLag`, `dm_uf_hasDerivAt`, `dm_mp_foc_v`, `dm_mp_foc_z`, `dm_mp_foc_E` |
| Ex. 18.2 | Planner's steady state (job creation and destruction) | `ex_18_2` |
| Ex. 18.2 | Efficiency of the decentralised equilibrium | `ex_18_2_efficiency` |
| Ex. 18.2 | A distribution satisfying the hypotheses | `dm_mp_exp_dist` (corrections 14) |

## §§18.2–18.3 and Exercises 18.3–18.5

### Tools (used throughout)

| Source | Claim | Lean |
| --- | --- | --- |
| (18.11), p. 590; pp. 601, 612 | Weighted AM–GM for the Nash product, with equality case | `jd_nash_le`, `jd_nash_eq_iff` |
| (18.37)–(18.38), p. 602; p. 613 | Nash bargaining with affine surpluses: maximiser iff the sharing rule | `jd_nash_iff` |
| pp. 601, 609–612 | First-order condition at an interior maximum | `jd_foc` |
| pp. 609–612 | Envelope condition | `jd_envelope` |
| p. 611 | Partial derivatives of a CRS function are homogeneous of degree 0 | `jd_partial_homog_one`, `jd_partial_homog_two` |
| (18.43), pp. 595, 607 | Affine recursion `u_{t+1} = a u_t + r`: solution, monotonicity, convergence | `jd_affine_sol`, `jd_affine_antitone`, `jd_affine_tendsto` |

### §18.2 Endogenous job destruction: the distribution `G`, pp. 600–604

| Source | Claim | Lean |
| --- | --- | --- |
| p. 600 | `G` on `(0, ∞)` with mean 1 (a probability measure `μ`); cdf `G` | `jd_G`, `jd_G_mono`, `jd_G_mem`, `jd_one_sub_G` |
| (18.41), p. 603 | `Φ(c) = ∫_c^∞ (z − c) dG = ∫ max(z − c, 0) dG` | `jd_Phi`, `jd_Phi_eq_setIntegral`, `jd_Phi_integrable` |
| p. 604 | `Φ ≥ 0`, antitone, 1-Lipschitz, continuous | `jd_Phi_nonneg`, `jd_Phi_antitone`, `jd_Phi_sub_le`, `jd_Phi_abs_sub_le`, `jd_Phi_continuous` |
| p. 604 | `Φ(c′) − Φ(c) ≥ (c − c′)(1 − G(c))`; strict decrease; `Φ(c) > 0 ↔ G(c) < 1` | `jd_Phi_gap`, `jd_Phi_strictAnti_of_pos`, `jd_Phi_pos_iff`, `jd_Phi_pos_iff_real` |
| p. 600 | `Φ(c) = 1 − c` for `c ≤ 0` (support and mean) | `jd_Phi_of_nonpos` |
| p. 604 | `Φ(c) → 0` as `c → ∞` | `jd_Phi_tendsto_atTop` |
| p. 607 (linearisation) | `Φ′(c) = −(1 − G(c))` at non-atoms | `jd_Phi_hasDerivAt` |

### §18.2 The equilibrium conditions, pp. 600–603

| Source | Claim | Lean |
| --- | --- | --- |
| p. 600 | Separation rate `ρ_t = ρˣ + (1 − ρˣ) G(z*_t)`, in `[ρˣ, 1]`, nondecreasing in `z*` | `jd_sepRate`, `jd_sepRate_mem`, `jd_sepRate_mono` |
| (18.29), (18.43), pp. 600, 603 | `N_{t+1} = (1 − ρ_t) N_t + q v_t` ⇒ `u_{t+1} = (1 − ρ_t − q θ_t) u_t + ρ_t` | `eq_18_43` |
| p. 600 | Bellman equation for `J^F` with `max(J^F, V)` | `jd_filled_job_cutoff_form` (its rewriting) |
| p. 601 | Rewritten Bellman equation with the cutoff | `jd_filled_job_cutoff_form` |
| (18.30)–(18.31), p. 601 | Free entry: `β ∫_{z*_{t+1}} J^F_{t+1} dG = κ / q_t` | `eq_18_31` |
| (18.32), p. 601 | `J^F_t(z) = A z − w_t(z) + (1 − ρˣ) κ / q_t` | `eq_18_32` |
| (18.33), p. 601 | `κ / q_t = β ∫_{z*_{t+1}} (A z − w_{t+1} + (1 − ρˣ) κ / q_{t+1}) dG` | `eq_18_33` |
| (18.34), p. 601 | Reservation productivity `J^F_t(z*_t) = 0` | `eq_18_34` |
| (18.35)–(18.36), p. 601 | Worker values `J^W`, `J^U` | hypotheses `h35`, `h36` of `eq_18_39` |
| (18.37)–(18.38), p. 602 | Nash bargaining: `η S = J^W − J^U`, `(1 − η) S = J^F` | `eq_18_37_38` |
| p. 602 | `J^W − J^U = w − b + β(1 − ρˣ − q^u) ∫ (J^W − J^U) dG` | `jd_worker_surplus` |
| p. 602 | Intermediate wage expression | `jd_wage_intermediate` |
| (18.39), p. 602 | `w_t(z) = η (A z + θ_t κ) + (1 − η) b` | `eq_18_39` |
| p. 602 | Search equilibrium (18.29), (18.3), (18.33), (18.34), (18.39) | hypotheses of `eq_18_39`–`eq_18_42` |
| (18.40), p. 602 | `J^F_t(z) = (1 − η)(A z − b) − η θ_t κ + (1 − ρˣ) κ / q_t`, zero at `z*_t` | `eq_18_40` |
| p. 603 | `J^F_t(z) = (1 − η) A (z − z*_t)` | `jd_JF_linear` |
| p. 600 | Cutoff: separate iff `z ≤ z*_t` | `jd_cutoff` |
| (18.41), p. 603 | Job creation condition (timing corrected) | `eq_18_41` |
| (18.42), p. 603 | Job destruction condition (timing corrected) | `eq_18_42` |
| p. 603 | Job destruction and job creation rates | `jd_jdRate`, `jd_jcRate` |
| p. 603 | "These equilibrium values are constant over time" | `jd_saddle` (see corrections) |

### §18.2 Steady state and comparative statics, pp. 604–607

| Source | Claim | Lean |
| --- | --- | --- |
| (18.44), p. 604 | Steady-state JC condition | `jd_JC`, `jd_JC_kappaA_iff` |
| (18.44), p. 604 | JC is downward sloping | `eq_18_44` |
| (18.45), p. 604 | Steady-state JD condition, upward sloping | `jd_JD`, `jd_thetaJD`, `jd_JD_iff`, `jd_h_strictMono`, `jd_thetaJD_strictMono`, `jd_thetaJD_continuous`, `eq_18_45` |
| p. 604, Fig. 18.5 | The intersection `(θ*, z̄*)`: uniqueness, existence | `jd_steady_state_unique`, `jd_steady_state_exists`, `jd_steady_state_existsUnique` |
| p. 604 (instance) | Cobb–Douglas `q`, degenerate `G`, `b < A` | `jd_example_steady_state` |
| p. 604 | Beveridge curve (18.19) with `ρ = ρˣ + (1 − ρˣ) G(z̄*)`; `u = ρ/(ρ + qθ)`, `jc = jd` | `jd_jc_eq_jd_of_steady` |
| p. 604 | Beveridge curve downward sloping | `jd_beveridge_downward` |
| p. 604 | Beveridge curve convex | Not formalised here: the §18.1 claim (prefix DM) |
| pp. 604–605 | Higher `A` (fixed `κ`) raises tightness | `jd_compstat_A_theta` |
| p. 605 | Effect of `A` (fixed `κ`) on `z*` ambiguous | Not formalised: no sign is claimed |
| p. 605 | Posting cost `κ A`: `A` cancels from (18.41) | `jd_JC_kappaA_iff` |
| p. 605 | With `κ A`, higher `A` lowers `z*` (and raises `θ`) | `jd_compstat_kappaA` |
| pp. 605–607 | Job destruction rate falls; steady-state job creation rate = jd rate; unemployment falls | `jd_compstat_kappaA_jd`, `jd_jc_eq_jd_of_steady`, `jd_compstat_kappaA_u` |
| p. 607, Fig. 18.6 | Higher `A` rotates JC line `v = θu` anticlockwise; shifts BC down | `jd_compstat_kappaA` (θ rises), `jd_beveridge_shift` |
| p. 607 | Effect on vacancies ambiguous | Not formalised: no sign is claimed |
| p. 607 | Linearised JC/JD system: `dz_t = ψ dz_{t+1}`, `ψ = βg((1 − ρˣ) − ηqθ/ξ)` | `jd_kappa_div_q_hasDerivAt`, `jd_Phi_hasDerivAt`, `jd_linear_psi` |
| p. 607 | Condition for `|ψ| < 1` | `jd_psi_abs_lt_one` |
| p. 607 | Steady state is a saddle point; jump variables at the steady state | `jd_saddle` |
| p. 607 | After a permanent rise in `A`: `u` falls monotonically, `jc` falls to `jd` | `jd_transition_unemployment` |

### §18.3 Unemployment and business cycles, pp. 607–614

| Source | Claim | Lean |
| --- | --- | --- |
| (18.46)–(18.48), pp. 608–609 | Household budget, capital, employment; DP objective | `jd_hhObj`, `jd_hh_budget_forms` |
| p. 608 | Utility `(C^{1−γ} − 1)/(1 − γ) − χ N^{1+φ}/(1 + φ)`: marginal utility, marginal disutility | `jd_crra_hasDerivAt`, `jd_disutility_hasDerivAt` |
| p. 608 | `∫₀^N χ j^φ dj = χ N^{1+φ}/(1 + φ)` | `jd_disutility_integral` |
| p. 609 | First-order condition for investment; envelope for capital | `jd_hh_foc_I`, `jd_hh_envelope_K` |
| (18.49), p. 609 | Euler equation | `eq_18_49` |
| p. 609 | Envelope condition for employment | `jd_hh_envelope_N` |
| (18.50), p. 609 | Household surplus recursion | `eq_18_50` |
| p. 610 | `V_n(w, t) = Λ_t (w − w_t) + ∂V_t/∂N_t` | `jd_hh_Vn`, `jd_hh_Vn_book_budget` |
| pp. 610–611 | Firm DP objective (18.22) | `jd_firmObj` |
| (18.51), p. 611 | `F₁(K^j, A N^j) = R_k` | `eq_18_51` |
| p. 611 | `K^j/N^j` independent of `j` | `jd_capital_ratio_indep` |
| (18.52), p. 611 | Vacancy first-order condition | `eq_18_52` |
| (18.53), p. 611 | Envelope condition | `eq_18_53` |
| (18.54), p. 611 | Firm surplus `S^F = A F₂ − w + (1 − ρ) κ / q^v` | `eq_18_54` |
| (18.55), p. 612 | Job creation condition | `eq_18_55` |
| p. 612 | `J_n(w, t) = w_t − w + ∂J_t/∂N^j_t` | `jd_firm_Jn` |
| pp. 612–613 | Nash problem `max V_n^η J_n^{1−η}`, FOC, `(1 − η) S^H = η S^F` | `jd_nash_18_3` |
| (18.56), p. 613 | Wage equation | `eq_18_56` |
| p. 613 | Wage independent of `j` | `jd_wage_indep` |
| p. 614 | Aggregation `Y = F(K, A N)` | `jd_aggregate_output` |
| (18.48), p. 609 | Firms' and household's employment laws agree | `jd_employment_consistency` |
| p. 614 | Resource constraint | `jd_resource_constraint` |
| p. 614 | Search equilibrium definition | hypotheses of the theorems above |
| §18.3 | Steady state, log-linearisation, simulations | Not in the text (none derived); steady state in Ex. 18.5 |

### Exercises, p. 614

| Source | Claim | Lean |
| --- | --- | --- |
| Ex. 18.3 | Mean-preserving spread (integral condition `Φ_G ≤ Φ_{G′}`), an instance | `jd_mps_example` |
| Ex. 18.3 | Tightness does not fall (strictly rises if `Φ` rises at `z̄*`) | `ex_18_3_theta` |
| Ex. 18.3 | Reservation productivity: `(1 − η) A Δz̄* = ΔH(θ)`; rises if `H` nondecreasing | `ex_18_3_reservation`, `ex_18_3_reservation_mono` |
| Ex. 18.3 | Unemployment falls if separation does not rise | `ex_18_3_unemployment` |
| Ex. 18.4 | Planner's objective | `jd_plannerObj` |
| Ex. 18.4 | Planner's FOCs, envelope conditions, Euler equation | `ex_18_4_foc_K`, `ex_18_4_foc_v`, `ex_18_4_envelope_K`, `ex_18_4_envelope_N`, `ex_18_4_euler` |
| Ex. 18.4 | Planner's surplus and job creation condition | `ex_18_4_surplus` |
| Ex. 18.4 | `M_v = q(1 − ξ)`, `M_u = ξ θ q` | `jd_matching_partial_v`, `jd_matching_partial_u` |
| Ex. 18.4 | Efficiency gap; Hosios (`b = 0`, `η = ξ`) | `ex_18_4_gap`, `ex_18_4_surplus_hosios`, `ex_18_4_hosios` |
| Ex. 18.4 | Steady-state tightness equations (analogues of (18.18), (18.28)) | `ex_18_4_ss_decentralised`, `ex_18_4_ss_planner`, `ex_18_4_ss_hosios` |
| Ex. 18.5 | Steady-state rental rate, employment, separation rate, posting cost, consumption | `ex_18_5_rental`, `ex_18_5_employment`, `ex_18_5_rho`, `ex_18_5_kappa`, `ex_18_5_consumption` |
| Ex. 18.5 | Calibrate to US data and solve numerically | Not formalised: computational/empirical |
