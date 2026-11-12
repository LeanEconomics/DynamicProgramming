# Corrections and departures: AKMM Chapter 11

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 11, Consumption (G. L. Violante), pp. 287–323. Lean names are relative to
`AKMM.Consumption`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 297, the MPC with log utility.** "Second, assuming log-utility (`σ = 1`) in the individual
   problem, without imposing `βR = 1`, by following similar steps one obtains `MPC ≃ r`." From
   (11.16) with `σ = 1`, `MPC = 1 − R⁻¹(βR) = 1 − β` for every `R` (`cd_mpc_log`): it does not
   depend on `r`, and it approximates `ρ`, not `r`. It equals the PIH value `r/(1 + r) ≃ r` only
   when `βR = 1` (`cd_mpc_log_eq_r_iff`). Counterexample: `β = 1/2`, `r = 1/100` give
   `MPC = 1/2 = 50r` (`cd_mpc_log_printed_counterexample`).

2. **p. 309, the HARA index.** "If `u` belongs to the HARA class, then one can show that the right
   hand side of (11.40) is equal to a constant `κ ≥ 0`." HARA gives `κ = 1 + s` constant, `s` the
   slope of the risk tolerance (`pr_tolerance_deriv`, `pr_hara_kappa_const`), but `κ ≥ 0` needs
   prudence (`u‴ ≥ 0`). Counterexample: `u′(c) = (1 − 2c)^{1/2}` on `c < 1/2` (`u′ > 0`, `u″ < 0`,
   risk tolerance `1 − 2c`) has `κ = −1` (`pr_hara_kappa_neg`, `pr_hara_neg_derivs`). The values
   of fn. 19 hold (`pr_kappa_quadratic`, `pr_kappa_cara`, `pr_kappa_crra`).

3. **pp. 309–310, capital income risk.** "Under prudence, however, the right-hand side is still a
   convex function of `r` (it is the product of a linear and a convex function), and thus …
   precautionary saving behavior emerges even in the face of higher volatility of returns." The
   product of a linear and a convex function need not be convex:
   `d²/dR²[Ru′(Ra)] = a[2u″(c) + cu‴(c)]`, `c = Ra` (`cr_second_deriv`), which is `≥ 0` iff
   relative prudence `−cu‴/u″ ≥ 2` (`cr_second_deriv_nonneg_iff`); for CRRA, `σ ≥ 1`. Under that
   condition the claim holds (`cr_convex_of_rel_prudence`, `cr_spread_raises_saving`). Prudence
   alone does not suffice: with log utility return risk leaves saving unchanged
   (`cr_log_return_risk_neutral`), and with CRRA `σ = 1/2` (prudent) the spread of `R = 1` into
   `1/2, 3/2` strictly lowers saving (`cr_printed_counterexample`, `cr_return_spread_instance`).
4. **(11.41), p. 310, and the Zeldes equation, p. 311.** The coefficient on `Var(Δlog c)` is
   printed `(σ + 1)/2`. Expanding `1 = βRE e^{−σΔlog c}` to second order, or exactly under
   lognormality, gives `σ/2`: `EΔlog c = (log(1 + r) − log(1 + ρ))/σ + (σ/2)Var(Δlog c)`
   (`eq_11_41`, `cs_lognormal_euler`). `(σ + 1)/2` (half relative prudence) is the coefficient on
   the uncentred second moment of the growth *rate* in (11.36) (`eq_11_36_exact`). The printed
   formula is false whenever the variance is positive (`eq_11_41_printed_false`). The Zeldes
   equation has the same coefficient error, and writes `δ` for `ρ` (`cs_zeldes_euler`).

5. **p. 314, DARA and (11.46).** "Condition (11.46) requires that absolute risk aversion decreases
   with wealth, i.e. that `u` belongs to the DARA class" and "under DARA the condition `βR < 1` is
   sufficient to guarantee a bounded asset space". The argument needs `α(c) → 0`, which DARA does
   not give: `u′(c) = e^{−c}/c` has `α(c) = 1 + 1/c`, strictly decreasing, with limit `1`
   (`bw_dara_not_ara_zero`). A sufficient condition is bounded relative risk aversion (so
   `α(c) ≤ γ/c → 0`), under which `βR < 1` bounds wealth (`bw_bounded_wealth`,
   `bw_bounded_wealth_crra`, `bw_crra_ara_tendsto`).

6. **p. 318, the uniqueness paragraph.** "Recall that the smaller is `σ` the larger is the income
   effect and a higher `r` increases savings." A smaller `σ` (a higher elasticity of substitution
   `1/σ`) strengthens the *substitution* effect, which is why saving rises with `r`. In the
   two-period CRRA problem without second-period income the saving ratio is
   `a/(y₀ − a) = β^{1/σ}R^{1/σ − 1}` (`hg_saving_ratio_crra`), strictly increasing in `R` iff
   `σ < 1` (`hg_saving_increasing_iff`).
7. **Footnote 27, p. 321.** "If `F(K, L) = K^αL^{1−α}`, then `K(r) = (αL/(δ + r))^{1/(1−α)}`."
   From `αK^{α−1}L^{1−α} = r + δ`, `K(r) = L(α/(δ + r))^{1/(1−α)}` (`footnote_27`); the printed
   formula holds only for `L = 1`. Counterexample: `α = 1/2`, `L = 2`, `δ + r = 1/2` give the
   printed `K = 4`, at which `F_K = (1/2)·2^{−1/2} ≠ 1/2`; the correct `K = 2`
   (`footnote_27_printed_false`).
8. **Minor.** p. 292: "estimates the misspecified equation (11.4) instead of (11.6)" refers to the
   unnumbered encompassing regression of p. 291, not to (11.4). p. 304 calls `u(0) = −∞` "the
   Inada condition" (Inada's condition is `u′(0) = ∞`). Footnote 17 cites "Stiglitz and
   Rothschild (1970)" for Rothschild and Stiglitz (1970). Not formalised (citations).

9. **p. 306, a tighter borrowing limit.** "For unconstrained households, consumption falls across
   the board because of the stronger precautionary saving motive." It falls only weakly
   (`cfn_tight_le`, at every horizon): one period before the end a tighter limit leaves the
   consumption of every household it does not constrain unchanged
   (`cfn_tight_eq_unconstrained_last`), and at any horizon the two consumption functions
   coincide at high wealth (`cfn_tight_eventually_eq`, which is the book's "the two consumption
   functions converge", in the strong form). The rest of the paragraph holds: the tight household
   is constrained wherever the loose one is (`cfn_tight_binds`), and one period before the end
   its MPC is at least the loose one on every interval (`cfn_tight_mpc_last`). The pointwise MPC
   comparison with more periods left (Carroll, Holm and Kimball's counterclockwise
   concavification) is not proved. The comparison uses `r ≥ 0` (`cfn_tight_shift`).

10. **p. 319, Figure 11.7: `A` depends on `B`.** The figure moves the vertical line `B` against a
    fixed `A(r)`, but with the tax `T = rB` of (11.50) the household's income `y − T` depends on
    `B`, so the asset demand is `A(r, B)`. "As `B` increases, the economy moves closer to the
    full insurance outcome" needs `A(·, B)` bounded above on each `[−1, r̄]`, `r̄ < 1/β − 1`,
    uniformly in `B`; then every selection of equilibrium rates tends to `1/β − 1`
    (`bwy_rate_tendsto_cm_dep`), and for a fixed continuous `A` (the figure) this holds
    automatically (`bwy_rate_tendsto_cm`). Full insurance is reached only in the limit: at every
    finite `B` the rate is below `1/β − 1` (`bwy_eqm_exists_below_cm`). With several equilibria
    the monotone statement is for the lowest equilibrium rate (`bwy_lower_eqm`); for `A`
    increasing, as drawn, the rate is increasing in `B` (`bwy_rate_strictMono`).

## Departures

1. **§11.2, the continuum of households.** The measure-one continuum `i ∈ [0, 1]` is a finite set
   of households; (11.4) is proved with arbitrary nonnegative population weights (`eq_11_4`),
   which is the integral against any finitely supported population. The book itself sums over
   `i = 1, …, I` before writing the integral.
2. **p. 290, Figure 11.1.** "The consumption of the least risk-averse households fluctuates more"
   is proved as an exact comparative static between two endowment levels:
   `σ₁Δlog c₁ = σ₂Δlog c₂`, so `Δlog c₁ > Δlog c₂ > 0` when `σ₁ < σ₂`
   (`rs_less_risk_averse_absorbs`).
3. **(11.10), p. 294.** Imposed on plans as `aₜ/Rᵗ → 0` (`cd_Plan`); the optimum of (11.12) is
   taken over positive consumption plans with summable discounted utility (`cd_Optimal`).
4. **§11.3.2, the PIH.** Random variables are elements of a normed space `V` with Miao's abstract
   conditional expectations (`CondExpSystem`); the Euler equation behind (11.18) is a hypothesis
   (the book states it); (11.10) is used in expectation, `(1 + r)^{−J}Eₜaₜ₊ᴶ → 0`; the constant
   random variable `1` is a vector `one` with `Eₜ one = one`. Dates `t, t − 1` are written
   `t + 1, t`.
5. **(11.28), p. 300.** "`r ≃ 0` … `≃ Var(v)`" is proved exactly at `r = 0` (`eq_11_28`), with the
   exact error terms `k²Var(uₜ₊₁)` and `k(Var(uₜ₊₁) − Var(uₜ))`, `k = r/(1 + r)`, for `r ≠ 0`
   (`bp_var_cons`, `bp_cov_cons_income`); the covariance is any symmetric bilinear form.
6. **p. 302, hitting the borrowing limit.** "A positive probability that at some point in the
   future the household will hit the borrowing limit" is proved for a run of `n` low draws, of
   probability `pⁿ > 0` (`bc_iid_hits`); the stochastic natural limit is proved along the path
   that stays at `y_min` (`bc_natural_limit`).
7. **§11.3.4, mean-preserving spreads.** A mean-preserving spread is the convex order
   (`pr_ConvexOrderOn`); the Rothschild–Stiglitz equivalence (fn. 17) is not proved. Two-point
   spreads are an instance (`pr_two_point_spread`). "If `u′` is convex … the right-hand side will
   increase" is proved for every spread (`pr_spread_raises_saving`); the converse is proved for
   two-point spreads, as midpoint convexity at the old consumption (`pr_two_point_iff`).
8. **(11.36), p. 308.** The approximation is proved as an exact identity when `u′` is quadratic on
   the support (cubic `u`), with `r − ρ` replaced by `1 − (βR)⁻¹ = (r − ρ)/(1 + r)`
   (`eq_11_36_exact`, `pr_betaR_inv`).
9. **(11.38)–(11.40).** The derivatives are hypotheses (`HasDerivAt`); the book's appeal to the
   value function inheriting differentiability is not formalised.
10. **(11.41).** The book's `≃`, with `r` and `ρ`, becomes the exact identity under lognormal
    consumption growth with `log(1 + r)` and `log(1 + ρ)`.
11. **§11.3.5.** The book's argument is formalised given (11.44) (`bw_bounded_of_ratio`); the
    first-order Taylor step from (11.46) to (11.44) is replaced by Miao's proof of
    Schechtman–Escudero (bounded relative risk aversion, i.i.d. income with bounded support,
    `bw_bounded_wealth`).
12. **§11.4.1, `A(r)`.** The aggregate asset demand is a function `A` given as a hypothesis of the
    existence theorem (`hg_existence`): its continuity is derived from the continuity of the
    policy and SLP Theorem 12.13 (`hg_A_continuous`), but the limit `A(r) → ∞` as `r ↑ 1/β − 1`,
    which the book asserts from §11.3.5, is assumed. Miao's set-valued `Ea(r)` connects the
    crossing to Definition 17.2.1 (`hg_existence_eqm`).
13. **p. 316, the equilibrium.** AKMM's definition lists goods-market clearing separately; it is
    implied by asset-market clearing and stationarity (`hg_goods_clear_zero_supply`), so with zero
    supply AKMM's definition is Miao's Definition 17.2.1 (`hg_eqm_iff_miao`). With positive supply
    goods-market clearing is equivalent to (11.50) (`eq_11_50`). The definition is shown non-vacuous
    with Miao's two-state cycle economy (`hg_cycle_eqm`, `hg_cycle_huggett`).
14. **§11.4.2.** The production equilibrium, its goods-market redundancy and existence are Miao's
    (Definition 17.1.1, `ay_resource_redundant`, `ay_existence_cd`); `K* > K^{CM}` is proved for
    any rate at which the household problem has a stationary distribution
    (`ai_precautionary_wealth`).
15. **Figure 11.2 (`ConsumptionShape`).** The household lives `n` more periods (the book's lives
    for ever) and eats its cash in hand in the last; income is i.i.d. with finitely many values
    `yᵢ ≥ d + a > 0`, so the state is cash in hand `x = a + y ≥ d` (Figure 11.2's horizontal axis
    `a` shifted by the given `y`). Consumption is defined by the Kuhn–Tucker conditions
    (11.32)–(11.33), shown to have a unique solution (`cfn_kkt_exists`, `cfn_kkt_unique`); that
    they characterise the optimum is not re-proved. Utility enters only through the Euler
    equation's certainty equivalent `M` (`cfn_IsMean`): the expectation for quadratic utility with
    `βR = 1` (the book's case, where the conditions are exactly (11.33),
    `cfn_quadratic_kkt_iff`) and the power mean with exponent `−σ` for CRRA
    (`cfn_crra_euler_iff`, imported from LeanEconomics' Carroll–Kimball power mean). The limit
    slope is the `n`-period perfect-foresight MPC `κₙ`, and `r/(1 + r)` is its limit as the
    horizon grows when `βR = 1` (`cfn_fig_11_2_slope`); for CRRA with `βR ≠ 1` it is (11.16)
    (`cfn_crra_kappa_limit`). Concavity is weak; the book's "strictly concave" is not formalised.
16. **Figure 11.4 (`BufferStock`).** The buffer-stock model is the household of
    `ConsumptionShape` without permanent shocks: income is i.i.d. with a positive floor and the
    borrowing limit `a ≥ 0` is imposed (the book's zero natural limit is `a = 0`). The target is
    `E[x′ | x] = x` for the consumption function at each horizon (the book's horizon is finite
    too), under `βR ≤ 1` (the book's `ρ > r`, weakened); with permanent shocks and growth the
    right condition would be Carroll's growth impatience condition, not formalised. Stability is
    convergence of the expected-cash dynamics `x ↦ E[x′ | x]` (`bsk_target_stable`); the
    stochastic process and expected consumption growth (the figure's vertical axis) are not
    formalised.
17. **Figure 11.7 (`BewleyInsurance`).** "Closer to the full insurance outcome" is read as the
    equilibrium rate approaching `r^{CM} = 1/β − 1`, the content of the figure; `A` is a
    hypothesis function as in `Huggett`.
