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
   its MPC is at least the loose one on every interval (`cfn_tight_mpc_last`). At every horizon
   consumption falls by at most `(a₁ − a₂)/R`, the amount the tighter limit removes from the
   current budget (`ctl_gap_le`, from the sharp shift bound `ctl_shift_sharp`). The MPC
   comparison with more periods left is proved for quadratic utility (the book's `βR = 1`, and
   more generally the expectation with factor `θ ≥ 1`) at every horizon and every `r ≥ 0`
   (`cta_tight_mpc`, `cta_gap_antitone`, `cta_quadratic_tight_mpc`). Without income risk it is
   proved for every utility, CRRA with any `β` and `σ` included, at every horizon
   (`ctp_tight_mpc`, `ctp_crra_tight_mpc`). For CRRA with income risk it is **false** two
   periods before the end: with log utility, `β = 1/2`, `R = 1`, `a₁ = 2`, `a₂ = 197/100` and
   income `2003/1000` (probability `1/3000`) or `5003/1000`, the loose household's consumption
   rises by more than the tight one's between cash in hand `43/4` and `279/25`
   (`ctc_counterexample`, `ctc_not_tight_mpc`; departure 18). So for CRRA with risk "their MPC
   increases" holds one period before the end only. The comparison uses `r ≥ 0`
   (`cfn_tight_shift`).

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
18. **p. 306, the MPC under a tighter limit with more periods left (`TighterLimitMPC`,
    `TighterLimitAllHorizons`).** "Their marginal propensity to consume (the slope of the
    consumption function) increases" is read, as in `cfn_tight_mpc_last`, as: on every interval of
    cash in hand the tight household's consumption rises at least as much as the loose household's,
    equivalently the fall `cₙ − c̃ₙ` is nonincreasing (`ctl_gap_antitone_R_one`,
    `cta_gap_antitone`); this implies the comparison of slopes wherever both are differentiable,
    kinks included in the one-sided sense. The proof is a backward induction in the spirit of
    Carroll, Holm and Kimball (2021): their counterconcavity comparison of marginal value functions
    is replaced by a shifted comparison of consumption functions, `τ`-domination (`ctl_IncrDom`: the
    tight function shifted left by `τ` rises at least as much as the loose one). `TighterLimitMPC`
    proves, for the expectation as certainty equivalent (any `θ > 0`, `R ≥ 1`), that
    `(a₁ − a₂)/R`-domination at `n` periods left gives the MPC comparison at `n + 1`
    (`ctl_mpc_step`) and `(a₁ − a₂)`-domination at `n` gives `(a₁ − a₂)/R`-domination at `n + 1`
    (`ctl_incr_step`), hence the comparison two periods before the end (`ctl_tight_mpc_two`) and,
    when `R = 1`, at every horizon (`ctl_incrDom_R_one`, `ctl_tight_mpc_R_one`, instance
    `ctl_example_mpc`). `TighterLimitAllHorizons` closes the induction for every `R ≥ 1` when
    `θ ≥ 1`, which contains quadratic utility with `βR = 1` (`θ = 1`, the book's case). With
    `Δ = a₁ − a₂` the invariant is a pair: the level bound `cₙ(x) + (Δ − Δ/R) ≤ c̃ₙ(x + Δ)`
    (`cta_shift_full`, which propagates on its own and uses `θ ≥ 1`), and `Δ`-domination. The level
    bound caps the gap between the two households' saving at `Δ/R`, so the shift the Euler equation
    passes back is at most `Δ` and `Δ`-domination returns `Δ`-domination (`cta_incr_step`,
    `cta_incrDom_full`); concavity turns it into the MPC comparison at every horizon
    (`cta_tight_mpc`; for the quadratic household `cta_quadratic_tight_mpc`, instance with `r = 1`
    `cta_example_valid`, `cta_example_mpc`). The pair was found from the infinitesimal problem:
    with `η = ∂c/∂a`, unconstrained `η − c′ + (R − 1)/(Rθ)` equals `(1 − c′)·θE` of its next-period
    value plus `(R − 1)(1 − θ)/(Rθ)`, so it stays nonpositive and nonincreasing when `θ ≥ 1`. The
    earlier invariant failed because `Δ`-domination alone does not bound the saving gap; the
    level bound is what it was missing. Not proved: (i) the expectation with `θ < 1`, which is not
    quadratic utility (the constant above is then positive, and `Δ`-domination fails numerically,
    though the MPC comparison held in every case tried). (ii) CRRA with income risk two or more
    periods before the end is settled negatively: the comparison fails (see the last paragraph,
    `TighterLimitCounterexample`).

    *Without income risk* the comparison holds at every horizon for every utility and every
    `θ > 0`, so for CRRA with any `β` and `σ` (`TighterLimitPerfectForesight`: `ctp_tight_mpc`,
    `ctp_gap_antitone`, `ctp_crra_tight_mpc`). The `cta_` invariant is not used: it needs `θ ≥ 1`
    and the linear certainty equivalent. Instead, with one state every certainty equivalent is
    the identity (`ctp_cont_eq`). The invariant is horizontal domination (`ctp_Hor`): to raise
    consumption by a given amount the tight household needs no more extra cash than the loose
    one. It propagates because the one-state Euler condition maps equal consumption today to equal
    consumption tomorrow (`ctp_hor_step`, `ctp_hor_all`). Where the loose household is
    constrained, the sharp shift bound closes the case. Concavity of the tight function turns
    the invariant into the MPC comparison (`ctp_mpc_of_hor`). It does not extend to risk, because
    equal certainty equivalents tomorrow do not mean equal consumption state by state.

    *With risk, two periods before the end* (formerly the first open case), the comparison held
    numerically not only for power means but for exponential certainty equivalents and for
    mixtures of the expectation and the minimum. This suggests a proof from the concavity of `M`
    alone, but none was found. The local form of the claim at cash `x` is
    `∇M(α)·π ≥ ∇M(a)·p`. Here `a`, `p` are the loose household's next-period consumptions and
    slopes, at `uᵢ = Rs + yᵢ`. `α`, `π` are the tight household's, at `vᵢ = uᵢ + t`, where `t` is
    `R` times the consumption gap and lies in `[0, Δ/R]`. The aggregate levels are tied by
    `M(α) = M(a) − γ/θ`. In states where next period's loose household is constrained, both
    slopes are `1` and `αᵢ = aᵢ − (Δ/R − t)`. In states where both points lie on the common
    unconstrained rule `ĉ`, the tight slope `ĉ′(vᵢ) ≤ ĉ′(uᵢ)` and the level `αᵢ ≥ aᵢ` both work
    against the claim: for a power mean the weight `∇ᵢM` falls with the level relative to `M`.
    So the compensation must come from the aggregate level identity across states, and no
    state-by-state comparison, shifted or horizontal, delivers it.

    For CRRA no shift domination can serve as the invariant: one period before the end both
    households have the same strictly concave unconstrained consumption function, so `τ`-domination
    fails for every `τ > 0`, and the step's use of the linearity of the expectation
    (`ctl_cont_incr`) has no power-mean analogue. In marginal-utility units the CRRA perturbation
    obeys the same linear recursion as the quadratic one, but the MPC factor `1 − c′` does not
    match the marginal-utility slope, so the identity found for the expectation becomes only an inequality (by Jensen)
    and loses the monotonicity. Random searches found no counterexample: in exact computations for quadratic
    utility and accurate numerical ones for CRRA (two periods before the end by nested root
    finding, up to six by the endogenous grid method, `σ` from `0.1` to `30`) the comparison
    always held. Two further routes for CRRA fail, for reasons that are proved or exact.
    (a) *Single-date tightenings in reverse chronological order.* Tightening `a₁ → a₂` at every
    date is the chain of economies in which the last `k` dates have the limit `a₂`. Each link
    tightens one date while the earlier dates keep `a₁`, and the link itself can lower today's MPC,
    for every utility: in a deterministic household, tightening only the next date's limit lowers
    the rise in consumption on `[1, 3/2]` from `1/2` to `1/4` (`cta_link_mpc_counterexample`,
    `cta_det_values`). The household saves more today, so today's limit stops binding at lower
    cash. This is CHK's hidden kink (their Figure on how a future constraint moves a current
    kink). CHK's concavification theorem (their Theorem 3) adds constraints in reverse
    chronological order with no constraint yet imposed at earlier dates. A new constraint at a
    date that already has one is handled by dropping the constraint it makes irrelevant and
    starting the construction again. It is also a perfect-foresight result. With risk, their
    Theorem 4 and Corollary 2 compare only with the linear unconstrained, riskless function. So
    neither the tightening of an existing limit at one date with earlier constraints in place nor
    its composition is covered, and the composition fails link by link. (b) *An order on marginal
    values.* Already one period before the end, `v = u′(c)` gives `h = ṽ ∘ v⁻¹` (tight as a
    function of loose) with slope `u″(c̃)c̃′/(u″(c)c′)`. This slope jumps up at the loose kink
    (`c′` falls from `1`, `c̃′` stays `1`) and down at the tight kink, which lies strictly above
    it. So `h` is neither convex nor concave, for every utility, and no such order can be the
    invariant. Holm (Norges Bank Working Paper 14/2016, Theorem 2) proves the MPC increase for a
    higher "cost of the liquidity constraint", HARA utility, but in continuous time, over an
    infinite horizon and with deterministic income. It does not reach the finite-horizon,
    discrete-time household with i.i.d. income here.

    *The counterexample (`TighterLimitCounterexample`).* For CRRA with income risk the claim is
    false two periods before the end. The household `ctc_H` has log utility (`σ = 1`, so `M` is
    the harmonic mean), `β = 1/2`, `R = 1` (so `θ = 2`), `a₁ = 2`, income `2003/1000` with
    probability `1/3000` and `5003/1000` otherwise, and `d = 3/1000` (`ctc_valid`). With
    `a₂ = 197/100`, between cash in hand `43/4` and `279/25` the loose household's consumption
    rises by about `2.5·10⁻⁷` more than the tight one's (`ctc_counterexample`), so `c₂ − c̃₂` is not
    nonincreasing (`ctc_not_tight_mpc`) and horizontal domination fails too (`ctc_not_hor`). The
    four consumption levels are bracketed by the sign of the Euler gap at rational points
    (`ctc_lt_step`, `ctc_step_lt`); next period's low state is constrained (`ctc_step_top`), and
    its high state is bracketed by its own Euler gap, so every check is a rational inequality
    (`ctc_cons2_gt`, `ctc_cons2_lt`). The example was found from the infinitesimal problem, which
    is not formalised. Differentiating the Euler equation in `a` gives
    `∂c₂/∂a = π·(∂c₂/∂x)/R²`, with `π` the share of next period's constrained states in
    `E|V₁″(Rs + yᵢ)|`. The claim at `n = 2` is thus that `π·MPC₂` is nonincreasing in cash. MPC₂
    falls (concavity), but `π` can rise: the weight of an unconstrained state falls at the rate
    of the absolute prudence of `V₁′` there, `P_u(ĉ)ĉ′ − ĉ″/ĉ′`. Just past the kink this includes
    the low-income risk two periods ahead and can exceed the prudence `(1 + σ)/c₁` of the
    constrained state. For an impatient enough household the fall of the MPC is too small to
    absorb the rise of `π`. Earlier searches missed it because the window is narrow: the low state must be
    rare and close to the limit two periods ahead (`y − a₁ = 3/1000`), and `θ` large. Violations
    were found for `θ = 1.5, 2, 3, 4` (`σ = 1`) and for `σ ≈ 0.15`, `θ ≈ 38`; a grid search at
    `θ = 1` (`R` from `1` to `10`) and hill-climbing at `θ = 1, 1.2` found none (scratch files
    `ch11_p2_gridR.py`, `ch11_p2_climbth.py`). Whether the claim holds for CRRA with risk when
    `θ ≤ 1` (`βR ≥ 1`), which includes the book's `βR = 1`, is open.
