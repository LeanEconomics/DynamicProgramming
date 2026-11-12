# Source map: AKMM Chapter 11

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 11, Consumption (G. L. Violante), pp. 287–323 (no appendix). Page
references are the draft's running heads. Lean names are relative to `AKMM.Consumption`.
Departures from the book are in [corrections](corrections.md).

## §11.2 Autarky and full insurance (`RiskSharing`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 288 | Endowment economy on an event tree, aggregate feasibility | `definition_13` (AKMM Ch. 7, reused) |
| p. 289, (11.1) | Autarky: consumption equals income | `eq_11_1` |
| p. 289, fn. 1 | Example endowments: aggregate higher in `H`, type 1 better off in `L` | `footnote_1` |
| p. 289, (11.2) | Arrow–Debreu budget | `cm_Budget` (AKMM Ch. 7, reused) |
| p. 289, (11.3) | `u′(cᵢ)/u′(cⱼ) = λᵢ/λⱼ` at every history | `eq_11_3` (from `eq_7_20`, `cm_risk_sharing`) |
| p. 290 | CRRA: ratio of consumptions constant | `rs_crra_ratio` |
| p. 290, (11.4) | `cⱼ = λⱼ^{−1/σ}/∫λᵢ^{−1/σ} · C` | `eq_11_4`, `rs_crra_invert` |
| p. 290 | Individual consumption proportional to the aggregate, independent of own endowment | `rs_crra_share_eqm` |
| p. 290, (11.5) | Heterogeneous `σ`: the two curves cross once | `eq_11_5`, `rs_lhs_strictAnti` |
| p. 290, Fig. 11.1 | Less risk-averse agent absorbs more of the aggregate change | `rs_less_risk_averse_absorbs` (exact two-point comparative static; the figure's numbers are not formalised) |
| p. 291, encompassing regression | `β₁, β₂` under autarky / full insurance | not formalised: empirical specification |
| pp. 291–292 | Mace, Cochrane, Attanasio–Davis, rank-mobility tests | not formalised: empirical |
| p. 292, (11.6) | Heterogeneous `βᵢ,₁`; omitted-variable bias sign | not formalised: econometric argument (the sign of `βᵢ,₁` relative to the mean is the content of `rs_less_risk_averse_absorbs`) |
| pp. 292–294 | Endogenous vs exogenous incomplete markets, Kehoe–Levine, Krueger–Perri, Cole–Kocherlakota | not formalised: narrative |

## §11.2.3–11.3.1 The bond economy and the deterministic problem (`Deterministic`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 294, (11.7)–(11.8) | Sequential Arrow budget, bond-economy budget | `seq_Budget` (AKMM Ch. 7, reused); (11.8) in `eq_11_11` |
| p. 294, (11.9)–(11.10) | nPg and TVC give `lim = 0` | `eq_11_10` |
| p. 295, (11.11) | `a′ = (1 + r)(y + a − c)` | `eq_11_11` |
| p. 295, fn. 8 | Alternative timing | not formalised: convention |
| p. 295, (11.12) | The deterministic problem | `cd_Plan`, `cd_Optimal` |
| p. 296, (11.13) | Euler equation from optimality | `eq_11_13` (finite perturbation, `ce_foc_of_perturb` of AKMM Ch. 5) |
| p. 296 | Slope increasing in `β` and `r` | `eq_11_14` (the ratio `(βR)^{1/σ}`) |
| p. 296, fn. 10–11 | Interest rate as relative price; income/substitution effects | not formalised: narrative |
| p. 296, (11.14) | CRRA: `cₜ₊₁/cₜ = (βR)^{1/σ}` | `eq_11_14`, `cd_growth` |
| p. 296 | Iterated budget with (11.10) | `cd_budget_iter`, `cd_tvc_shift`, `cd_intertemporal_budget`, `cd_summable_pv_cons` |
| p. 296 | Euler + (11.10) characterise the optimum | `cd_optimal_of_euler`, `cd_log_optimal` (concrete optimum) |
| p. 297, (11.15) | `cₜ = [1 − R⁻¹(βR)^{1/σ}](aₜ + Σ R⁻ʲyₜ₊ⱼ)` | `cd_rule_of_growth`, `eq_11_15`, `cd_optimal_eq_11_15` |
| p. 297, (11.16) | MPC | `cd_mpc`, `eq_11_16` |
| p. 297, fn. 12 | Transitory income change = wealth change | `cd_transitory_eq_wealth` |
| p. 297, fn. 13 | `βR = 1` ⇒ `MPC = 1 − β ≃ ρ` | `cd_mpc_betaR_one`, `cd_mpc_approx_rho` |
| p. 297 | Log utility: "`MPC ≃ r`" | corrected: `cd_mpc_log`, `cd_mpc_log_eq_r_iff`, `cd_mpc_log_printed_counterexample` |
| p. 297 | MPC out of permanent income is 1 | `cd_mpc_permanent` |
| p. 298, fn. 15 | Annuity value keeps assets constant | `footnote_15` |

## §11.3.2 The permanent income hypothesis (`PIH`)

Conditional expectations are Miao's `CondExpSystem ℝ V` (`Miao.RationalExpectations`, reused;
`condExpSystemL1_real` is the `L¹` instance); `pih_detSystem` is the deterministic instance.

| Source | Claim | Lean |
| --- | --- | --- |
| p. 297, (11.17) | The stochastic problem with quadratic utility, `βR = 1` | hypotheses of `eq_11_18` |
| p. 298, (11.18) | Hall: `cₜ = Eₜcₜ₊₁` | `eq_11_18` |
| p. 298, (11.19) | `Eₜcₜ₊ⱼ = cₜ` | `eq_11_19` |
| p. 298, fn. 14 | Definition of a random walk | the hypothesis of `pih_random_walk` |
| p. 298 | Iterated budget under `Eₜ` | `pih_budget_iter`, `pih_budget_condexp` |
| p. 298, (11.20) | Annuity value of total wealth | `eq_11_20`, `pih_rule`, `pih_one_sub_q`, `pih_annuity_inv` |
| p. 298, (11.21) | Deterministic case | `eq_11_21`, `pih_detSystem` |
| p. 298 | Certainty equivalence | `pih_certainty_equivalence` |
| p. 299 | "Any deviation from quadratic objective and linear constraints breaks certainty equivalence" | not formalised: informal (the prudence results of `Prudence` show it for convex `u′`) |
| p. 299, (11.22) | `Δcₜ = (r/(1 + r))[ϖₜ − Eₜ₋₁ϖₜ]` | `eq_11_22`, `pih_wealth` |
| p. 299, (11.23) | The innovation in total wealth | `eq_11_23` |
| p. 299, (11.24) | Consumption change = annuity value of news | `eq_11_24` |
| p. 299, (11.25)–(11.26) | Permanent/transitory income | `eq_11_26`, `pih_perm_martingale` |
| p. 300 | "after some algebra": the revision of expected income | `pih_news_perm_trans` |
| p. 300, (11.27) | `Δcₜ = (r/(1 + r))uₜ + vₜ` | `eq_11_27` |
| p. 301, (11.29) | Saving `sₜ = yₜ − (r/(1 + r))Σ qʲEₜyₜ₊ⱼ` | `eq_11_29` |
| p. 301 | Saving for a rainy day `sₜ = −Σ_{j≥1} qʲEₜΔyₜ₊ⱼ` | `pih_rainy_day` |
| p. 302 | Random-walk income: `cₜ = (r/(1 + r))aₜ + yₜ`, `aₜ₊₁ = aₜ` | `pih_random_walk` |
| p. 302, (11.30) | i.i.d. income: `cₜ = ȳ/(1 + r) + (r/(1 + r))(aₜ + yₜ)`, `Δaₜ₊₁ = yₜ − ȳ` | `eq_11_30` |
| p. 300, (11.28) | Blundell–Preston: `ΔVar(c) = ΔCov(c, y) ≃ Var(v)` at `r ≃ 0` | `eq_11_28` (exact at `r = 0`), with `bp_var_cons`, `bp_cov_cons_income`, `bp_cov_cons_trans`, `bp_cov_stationary` (module `BlundellPreston`) |
| pp. 300–301 | Blundell–Preston's UK findings, Attanasio–Davis | not formalised: empirical |

## §11.3.3 Borrowing constraints (`BorrowingConstraints`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 302 | i.i.d. case: `yₜ < (1 − r)ȳ`, `aₜ < rȳ` ⇒ next-period wealth negative | `bc_iid_example` |
| p. 302 | Positive probability of hitting the limit in finite time | `bc_iid_hits` |
| p. 302, (11.31) | The constrained problem | hypotheses of `eq_11_32`, `eq_11_33` |
| p. 303, (11.32) | `u′(cₜ) ≥ βREₜu′(cₜ₊₁)`, strict iff binding | `eq_11_32` |
| p. 303 | Binding: `cₜ = aₜ + yₜ`, MPC 1 | `bc_binding_cons` |
| p. 303 | Timing of income matters with constraints | not formalised: informal |
| p. 303 | Natural limit, deterministic: `aₜ₊₁ ≥ −Σ (1 + r)⁻ʲyₜ₊₁₊ⱼ` | `bc_natural_limit_det` |
| p. 303 | Natural limit `−(1 + r)y_min/r` | `bc_natural_limit` |
| p. 304 | At the limit with `y_min`, `cₜ ≤ 0` | `bc_natural_limit_cons_nonpos` |
| p. 304 | With `u(0) = −∞` the consumer never borrows to the limit | not formalised: informal (follows from `bc_natural_limit_cons_nonpos`) |
| p. 304 | `y_min = 0`: no-borrowing = natural limit | `bc_natural_limit_zero` |
| p. 304, fn. 16 | Borrowing wedge `χ` when `r < 0` | not formalised: remark |

## §11.3.4 Precautionary saving (`BorrowingConstraints`, `Prudence`, `ConsumptionShape`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 304 | Quadratic utility: a mean-preserving spread does not affect saving | `pr_quadratic_no_precaution`, `pr_convexOrder_mean` |
| p. 304 | Mean-preserving spread | `pr_ConvexOrderOn` (convex order), `pr_two_point_spread` (instance) |
| p. 305, (11.33) | `cₜ = min{yₜ + aₜ + a/R, Eₜcₜ₊₁}` | `eq_11_33` |
| p. 305, (11.34) | A spread lowers `E min{…}`, raises saving | `eq_11_34_spread` |
| p. 305, Fig. 11.2 | Slope 1 below `a*` | `bc_slope_one` |
| pp. 304–306, Fig. 11.2 | The model behind the figure: (11.32)–(11.33) as a finite-horizon Kuhn–Tucker recursion, quadratic utility with `βR = 1` or CRRA | `CfnHousehold`, `CfnHousehold.KKT`, `CfnHousehold.cons`, `cfn_kkt_exists`, `cfn_kkt_unique`, `cfn_cons_kkt`, `cfn_kkt_iff_min`, `cfn_quadratic_kkt_iff`, `cfn_crra_euler_iff`, `cfn_isMean_expect`, `cfn_isMean_powerMean`, `cfn_quadratic_valid`, `cfn_crra_valid`, `cfn_example_valid` (instance) |
| p. 305, Fig. 11.2 | Constrained below `a*` with slope 1 (an initial interval) | `cfn_binding_initial`, `cfn_cons_le` |
| pp. 305–306, Fig. 11.2 | Concave above `a*` | `cfn_cons_concave` (concave on the whole domain), `cfn_step_good`, `cfn_cont_concave`; strict concavity not formalised |
| p. 306 | MPC between `r/(1 + r)` and `1` | `cfn_cons_slope_bounds` (between `κₙ` and `1`), `cfn_kappa_gt`, `cfn_cons_good` (`κₙx ≤ cₙ ≤ κₙ(x + hₙ)`) |
| pp. 305–306, Fig. 11.2 | Slope → `r/(1 + r)` for large wealth | `cfn_slope_tendsto` (slope → `κₙ`), `cfn_kappa_tendsto`, `cfn_kappa_tendsto_r`, `cfn_fig_11_2_slope` (`βR = 1`, long horizon); CRRA limit (11.16): `cfn_crra_kappa_limit` |
| p. 306, Fig. 11.2 | Tighter limit `a₂ < a₁`: constrained on a wider range | `cfn_tight_binds` |
| p. 306 | … consumption of unconstrained households falls | corrected: weakly, `cfn_tight_le`; not at all one period before the end, `cfn_tight_eq_unconstrained_last` |
| p. 306 | … their MPC increases | `cfn_tight_mpc_last` (one period before the end, on every interval); with more periods left not formalised |
| p. 306, Fig. 11.2 | … the two functions converge as wealth grows | `cfn_tight_eventually_eq` (they coincide), `cfn_tight_shift` |
| p. 306, (11.35) | Unique root `a₁` | `eq_11_35_unique` |
| p. 306, Fig. 11.3 | Comparative statics of the root | `pr_root_mono`, `pr_rhs` |
| p. 306 | `u′` convex ⇒ a spread of `y₁` raises `a₁` | `pr_spread_raises_saving` |
| p. 306 | … and conversely (two-point spreads) | `pr_two_point_iff` |
| p. 306, fn. 17 | Rothschild–Stiglitz | not formalised: cited (the MPS is stated as the convex order) |
| p. 306 | Sibley, Miller: multi-period extension | not formalised: cited |
| p. 307 | Prudence `u‴ > 0`; Kimball's indices | `pr_kappa` (the ratio used in (11.40)) |
| p. 307 | DARA ⇒ `u‴ > (u″)²/u′ > 0` | `pr_ara_deriv`, `pr_dara_prudent` |
| p. 308, (11.36) | Blanchard–Mankiw | `eq_11_36_exact` (exact for quadratic `u′`), `pr_betaR_inv` |
| p. 308, (11.37) | Envelope condition | hypothesis of `eq_11_38` |
| p. 308, (11.38) | `c′ = V″/u″ > 0` | `eq_11_38` |
| p. 308, (11.39) | `c″` | `eq_11_39` |
| p. 309, (11.40) | `c″ ≤ 0` iff `V‴V′/(V″)² ≥ u‴u′/(u″)²` (Carroll–Kimball Lemma 2) | `eq_11_40` |
| p. 308, fn. 18 | HARA: risk tolerance affine | `pr_tolerance_deriv`, `pr_hara_kappa_const` |
| p. 309 | HARA ⇒ `κ` constant `≥ 0` | corrected: `pr_hara_kappa_const`; `κ < 0` possible without prudence, `pr_hara_kappa_neg`, `pr_hara_neg_derivs` |
| p. 309, fn. 19 | Quadratic `κ = 0`, CARA `κ = 1`, CRRA `κ > 1` | `pr_kappa_quadratic`, `pr_kappa_cara`, `pr_kappa_crra` |
| p. 309 | Carroll–Kimball and Jensen: concavity under HARA, finite horizon | `cfn_cons_concave` for CRRA and quadratic utility, with a borrowing limit (the power-mean step is LeanEconomics' `powerMean_concave`); general HARA not formalised |
| p. 309, fn. 20 | Cantor: CARA consumption linear in wealth | not formalised: cited |

## Capital income risk, buffer stock, Zeldes (`CapitalRisk`, `Lognormal`, `BufferStock`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 309 | Euler `u′(y₀ − a₁) = βE[(1 + r)u′((1 + r)a₁)]`, unique root | the hypotheses of `cr_spread_raises_saving` (uniqueness: `eq_11_35_unique`) |
| pp. 309–310 | Under prudence the RHS is convex in `r`, so return risk raises saving | corrected: `cr_deriv`, `cr_second_deriv`, `cr_second_deriv_nonneg_iff`, `cr_convex_of_rel_prudence`, `cr_spread_raises_saving`; counterexamples `cr_log_return_risk_neutral`, `cr_printed_counterexample`, `cr_return_spread_instance` |
| p. 310 | Buffer-stock model (Carroll 1992, 2001), normalised cash on hand | without permanent shocks: the household of `ConsumptionShape`, `CfnHousehold.nextCash`; the normalised model is not formalised |
| p. 310, (11.41) | `EΔlog c ≃ (r − ρ)/σ + ((σ + 1)/2)Var(Δlog c)` | corrected: `eq_11_41`, `cs_lognormal_euler`, `eq_11_41_printed_false` |
| p. 310 | As `x → 0` growth → ∞; as `x → ∞` growth → `(r − ρ)/σ` | not formalised: claims about the buffer-stock policy (Fig. 11.4) |
| pp. 310–311, Fig. 11.4 | Target `x*` (`ρ > r`): accumulate below, decumulate above | `bsk_target` (needs `βR ≤ 1`, `cfn_crra_theta_ge_one_iff`, via `cfn_R_one_sub_kappa_lt`), `bsk_convex_crossing`, `bsk_example_target` (instance) |
| p. 311, Fig. 11.4 | `x*` is stable: wealth converges back to `x*` | `bsk_target_stable`, `bsk_iterate_tendsto`, `bsk_nextCash_mono` |
| p. 311 | Excess sensitivity (Flavin, Campbell–Mankiw) | not formalised: empirical |
| p. 311 | Zeldes Euler equation with `log(1 + λₜ)/σ` | corrected: `cs_zeldes_euler` |
| p. 311 | Zeldes's PSID split and lagged income | not formalised: empirical |
| pp. 311–312, Fig. 11.5 | Comparative statics of the consumption function (CRRA 2, β = .95, R = 1.02) | figure claim, deferred (numerical) |

## §11.3.5 Bounds on wealth accumulation (`BoundedWealth`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 312 | `βR < 1` sufficient for bounded wealth (Schechtman–Escudero, Clarida, Huggett) | `bw_bounded_wealth` (Miao's `SIModel.Solution.lemma_8_3_3_all`, reused), `bw_bounded_wealth_crra`, `bw_crra_rra` |
| p. 312, fn. 23 | Lower bound from the borrowing limit | not formalised: remark |
| p. 312, fn. 24 | Deterministic case `βR ≤ 1` | not formalised: cited (Miao Ch. 8 `cd*` results in `Applications`) |
| p. 313, (11.42) | Euler equation in cash on hand | hypothesis `heuler` of `bw_bounded_of_ratio` |
| p. 313, (11.43) | `u′(c(x)) = βR(E u′(c(x′))/u′(c(x̄′)))u′(c(x̄′))` | `eq_11_43` |
| p. 313, (11.44) | If the ratio → 1 then `x̄′ < x` for large `x` | `bw_bounded_of_ratio` |
| p. 314, (11.45) | Taylor expansion; `x̄′ − x′ = ȳ − y′` | `bw_cash_gap` (the expansion itself is replaced by Miao's proof) |
| p. 314, (11.46) | `α(c) → 0` | `bw_crra_ara_tendsto` (CRRA) |
| p. 314 | (11.46) requires DARA; under DARA `βR < 1` suffices | corrected: `bw_dara_not_ara_zero` |
| p. 314, fn. 25 | Huggett (1993): two-state Markov chain, CRRA | not formalised: cited |

## §11.4.1 The endowment economy (`Huggett`, `AssetDemandContinuity`, `BewleyInsurance`)

Reused from Miao `IncompleteMarkets` (`Miao.IncompleteMarkets`): `BWEconomy`,
`BWEconomy.Bellman`, `BWEconomy.Stationary`, `BWEconomy.EaSet`, `BWHuggettEqm`,
`definition_17_2_1`, `bw_cycle` and its lemmas, `ay_existence`, `ay_existence_cd`,
`ay_beta_R_lt_one`, `ay_r_lt_rho`, `SIModel.Solution.lemma_8_3_3_all`, `ay_Kd` and its lemmas,
`ay_overaccumulation`, `AYStationaryEqm`, `definition_17_1_1`, `ay_resource_redundant`,
`ay_example_exists`. From SLP `WeakConvergence` (`StokeyLucasPrescott.WeakConvergence`):
`theorem_12_12`, `theorem_12_13`, `ConvWeak`, `adjointOp`.

| Source | Claim | Lean |
| --- | --- | --- |
| p. 315 | Endowment economy, budget `c + a′ = Ra + y`, limit `a′ ≥ −a` | `BWEconomy` (Miao) |
| p. 316, (11.47) | The Bellman equation | `BWEconomy.Bellman` (Miao) |
| p. 316, (11.48)–(11.49) | Transition function and the sequence of distributions | `BWEconomy.Stationary` (Miao; the fixed point of (11.49) on rectangles) |
| p. 316 | Stationary equilibrium (zero supply) | `hg_IsStationaryEqm` (with `B = T = 0`), `hg_eqm_iff_miao`, `BWHuggettEqm`, `hg_cycle_huggett` (instance) |
| p. 316 | Goods-market clearing | `hg_goods_clear_zero_supply`, `hg_mean_consumption`, `hg_mean_assets_eq_mean_policy`, `hg_map_fst_eq`, `hg_integrable_assets` |
| p. 317 | `A(r)` continuous if `a′` and `λ*_r` are | `hg_A_continuous`, `hg_A_continuousOn` (with SLP `theorem_12_13`) |
| p. 317 | Theorem of the maximum: policy continuous in `r` | not formalised: hypothesis of `hg_A_continuous` |
| p. 317 | SLP 12.12: monotone mixing ⇒ unique invariant distribution | `theorem_12_12` (SLP, reused; cited) |
| p. 317 | Compactness needs an upper bound on wealth, `βR < 1` | `bw_bounded_wealth` |
| pp. 317–318 | Monotone mixing holds in the model (informal) | not formalised: informal argument |
| p. 318 | `A(1/β − 1) = +∞` | not formalised: hypothesis of `hg_existence` (Chamberlain–Wilson; not proved in the book) |
| p. 318 | `A(−1) = −a` | `hg_policy_at_minus_one`, `hg_A_at_minus_one`, `hg_EaSet_at_minus_one` |
| p. 318, Fig. 11.6 | Existence by continuity | `hg_existence`, `hg_existence_eqm` |
| p. 318 | `r* < 1/β − 1`, `βR* < 1` | `hg_rate_below_cm` (Miao's `ay_beta_R_lt_one`, `ay_r_lt_rho`) |
| p. 318 | Risk-free rate puzzle box | not formalised: narrative |
| p. 318 | Uniqueness if `A` increasing | `hg_unique_of_strictMono` |
| p. 318 | ACHLLM (2022): uniqueness for `σ < 1` in continuous time | not formalised: out of scope (continuous-time HJB/KFE) |
| p. 318 | "the smaller is `σ` the larger is the income effect and a higher `r` increases savings" | corrected: `hg_saving_ratio_crra`, `hg_saving_increasing_iff` |
| p. 319, (11.50) | `rB = T`; `∫a′dλ = B` | `eq_11_50`, `hg_cycle_eqm` (instance, `B = 1/4`) |
| p. 319, Fig. 11.7 | Higher `B` moves the economy towards full insurance | `bwy_rate_tendsto_cm` (`r* → r^{CM}` as `B → ∞`), `bwy_eqm_exists_below_cm` (never reached), `bwy_lower_eqm` (lowest rate rises), `bwy_rate_strictMono` (increasing `A`), corrected for `A = A(r, B)`: `bwy_rate_tendsto_cm_dep`; instance `bwy_example` |

## §11.4.2 The production economy (`Aiyagari`)

| Source | Claim | Lean |
| --- | --- | --- |
| p. 320 | Firm, CRS, Inada | `ay_CRS`, `ay_cdF` (Miao) |
| pp. 320–321 | Stationary equilibrium with production | `AYStationaryEqm`, `definition_17_1_1`, `ay_example_exists` (Miao, reused); goods-market redundancy `ay_resource_redundant` |
| p. 321 | `K(r)` from `F_K = r + δ`; `K → ∞` at `−δ`, `K → 0` at `∞`, continuous, strictly decreasing | `ai_capital_demand_props`, `ai_Kd_tendsto_zero` |
| p. 321, fn. 27 | `K(r) = (αL/(δ + r))^{1/(1−α)}` | corrected: `footnote_27`, `footnote_27_printed_false` |
| p. 321 | Existence | `ai_existence` |
| p. 322, Fig. 11.8 | `K* > K^{CM}`: precautionary wealth | `ai_precautionary_wealth` |
| p. 322 | Aiyagari's quantitative findings (saving rate +3pp, wealth distribution) | not formalised: numerical |
| p. 322, Fig. 11.9 | MPC distribution (Kaplan–Violante) | not formalised: numerical figure |
| p. 323 | PIH MPC with `βR* = 1` ≈ `r` | `ai_mpc_representative` |
| p. 323 | MPC out of anticipated income is zero (PIH) | not formalised: informal |
| p. 323 | Stimulus-payment MPC evidence (15–30%); calibrated model ≤ 5%; heterogeneous β; two-asset models | not formalised: empirical / numerical |

## Not formalised: summary

* §11.1 introduction; the narrative of §11.2.2–11.2.3; the empirical literature throughout
  (Mace, Cochrane, Attanasio–Davis, Fisher–Johnson, Jappelli–Pistaferri, Mazzocco–Saini,
  Schulhofer-Wohl, Blundell–Preston's findings, Flavin, Campbell–Mankiw, Zeldes's PSID estimates,
  Parker et al.).
* Figures 11.1–11.9 as numerical objects; the claims read off Figures 11.5 (numerical
  comparative statics) and 11.9 are not formalised. Figure 11.1's claim is proved exactly
  (`rs_less_risk_averse_absorbs`), Figure 11.3's by `pr_root_mono`, Figure 11.2's in
  `ConsumptionShape`, Figure 11.4's in `BufferStock` and Figure 11.7's in `BewleyInsurance`
  (except the pointwise MPC comparison for a tighter limit more than one period before the end,
  and Figure 11.4's vertical axis, expected consumption growth).
* Cited results without proof in the book: Rothschild–Stiglitz, Sibley/Miller, Carroll–Kimball
  and Jensen beyond CRRA and quadratic utility, Cantor (CARA), Carroll's buffer-stock model
  with permanent shocks,
  Huggett (1993) two-state extension, ACHLLM uniqueness (out of scope), Uhlig's law of large
  numbers.
