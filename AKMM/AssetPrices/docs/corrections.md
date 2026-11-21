# Corrections and departures: AKMM Chapter 16

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 16, Asset prices (Monika Piazzesi and Martin Schneider), pp. 467–492.
Lean names are relative to `AKMM.AssetPrices`. Every book item is located in the
[source map](source-map.md).

## Corrections

1. **p. 481, (16.17).** The book: `1 = E[RⁿM] + Cov(Rⁿ, M) ⟺ E[Rⁿ] − R_f = −Cov(Rⁿ, M)/E[M]`.
   The left identity is false: since `E[RⁿM] = 1`, it would force `Cov(Rⁿ, M) = 0`. The correct
   decomposition is `1 = E[Rⁿ]E[M] + Cov(Rⁿ, M)`, from which the premium formula follows
   (`eq_16_17`). Counterexample to the printed form: two equally likely states, state prices
   `(1/4, 1/2)` (`M = (1/2, 1)`) and the Arrow security for state 1 (`R = (4, 0)`):
   `E[RM] = 1` but `Cov(R, M) = −1/2` (`eq_16_17_printed_counterexample`).

2. **p. 478, (16.14).** The book: if markets are arbitrage-free, the budget set (16.10) "can be
   rewritten as" (16.14), the plans with `c₀ − y₀ + Σ_ω q(ω)(c₁(ω) − y₁(ω)) ≤ 0` and
   `c₁ − y₁ ∈ span(D)`. As sets this is false, because (16.10) has inequalities at date 1 (free
   disposal) while (16.14) asks the net trade to be exactly spanned. Counterexample: two states,
   only a riskless bond, `y = 0`; throwing away one unit in state 1 is in (16.10) but not in
   (16.14) (`eq_16_14_counterexample`). What is true: every plan in (16.10) satisfies the single
   budget constraint (`tp_budget_single`); (16.14) is exactly the budget set with binding date-1
   constraints, which the book has in mind ("the budget equations will bind", p. 473)
   (`eq_16_14`); and with complete markets (16.10) equals the Arrow–Debreu budget set
   (`tp_budget_complete`).

3. **p. 477, existence of an optimal portfolio.** The book: "If the utility function is continuous
   and there are no arbitrage opportunities, then there is a solution". This needs a lower bound
   on consumption: with (16.10) as printed (no `c ≥ 0`), one state, one Arrow security at price 1
   (no arbitrage) and the continuous, strictly increasing `U(c) = c₀ + 2c₁`, there is no optimum
   (`tp_no_optimal_without_nonneg`). With `c ≥ 0` and `y ≥ 0` the claim holds
   (`tp_exists_optimal`, via compactness of the budget set, `tp_budgetPos_isCompact`). The
   converse ("an optimum implies no arbitrage") needs strictly increasing utility, which the book
   assumes (`tp_noArbitrage_of_optimal`).

4. **p. 475, fn. 3, the separating-hyperplane argument.** The footnote separates the two closed
   convex cones `M` and `K = ℝ₊^{S+1}` (and is garbled: "`F(z) < F(x)` for all `z` in `M`", with `x`
   undefined in that clause). Separating two cones that meet only at `0` gives `F ≥ 0` on `K` but
   not `F > 0` on `K ∖ {0}`, which is what makes the state prices strictly positive. The proof here
   separates `M` from the compact simplex in `K` (Stiemke's lemma, Miao's `rd_stiemke`)
   (`tp_ftap`).

5. **p. 484, (16.21).** Printed: `q_{i,t+1}(ω_{t+1}|ω_t) = πₜ₊₁(ωᵗ⁺¹)βᵗ⁺¹(ωᵗ⁺¹)cᵢ,ₜ₊₁(ωᵗ)^{−γ} /
   (πₜ(ωᵗ)βᵗ(ωᵗ)cᵢ,ₜ(ωᵗ)^{−γ}) = πₜ₊₁(ωₜ₊₁|ωᵗ)βcᵢ,ₜ₊₁(ωᵗ)^{−γ}/cᵢ,ₜ(ωᵗ)^{−γ}`. Consumption at
   `t + 1` is `cᵢ,ₜ₊₁(ωᵗ⁺¹)`, the discount factor has no history argument, and the conditioning is
   on `ωᵗ`: `qᵢ,ₜ₊₁(ωₜ₊₁|ωᵗ) = πₜ₊₁(ωₜ₊₁|ωᵗ)β(cᵢ,ₜ₊₁(ωᵗ⁺¹)/cᵢ,ₜ(ωᵗ))^{−γ}` (`eq_16_21`, with the
   marginal utility `eu_crra_partial`).

6. **p. 490, "risk aversion would need to be high, `γ = 16`".** With Table 16.1's
   `σ_cσ_r = 0.0233 × 0.1836 = 0.00427788`, a premium of `0.07` needs `γ ≥ 0.07/0.00427788 =
   16.363…`; at `γ = 16` even perfect correlation gives `0.0684 < 0.07`. Proved with exact
   rational certificates: `lg_gamma_bound` (`γ ≥ 16.36`), `lg_gamma_16_short`. (The book rounds
   `σ_cσ_r` to `0.0043`, `lg_sd_product`, and `0.07/0.0043 = 16.28`.)

7. **p. 482, uniqueness of the risk-neutral probability.** "The risk-neutral probability `π*` is
   unique if markets are complete, otherwise there may be many": the first part is proved
   (`riskNeutral_unique_of_complete`); "otherwise" holds when a riskless bond is traded, and then
   `π*` is unique iff markets are complete (`riskNeutral_unique_iff`). (Without a bond the
   converse can fail: with one state `π* = 1` always.)

8. **Notation and reference slips.** p. 475: "no arbitrage opportunities given asset prices `q`"
   should be `p` (`tp_noArbitrage_of_statePrices`). p. 477: the value map
   `(pˢ − p_fδ₂, p_fδ₁ − pˢ)` uses `p_f` for the bond price `pᵇ` (`ex1_value`). p. 478: "With two
   states, `S = 1`" should be `S = 2`. p. 486, (16.25): `gⱼ` stands for the gross growth rate `Gⱼ`
   (`eq_16_25`). p. 489: the derivation of (16.30) writes `μ_c, σ_c` for `μ_g, σ_g` (`eq_16_30`).
   p. 491: "Table 2" is Table 16.2, and "The approach deviates from the iid assumption" should be
   "The first approach".

## Departures (modelling choices, not errors)

9. **Finite agents and a finite horizon in §16.3.** The book allows infinitely many agents and an
   infinite horizon. The planner and Arrow–Debreu conditions (16.1)–(16.7) are proved for finitely
   many agents and a finite set of date–history pairs, from optimality, with differentiable
   utilities (Fréchet derivatives) and positive prices (`eq_16_1`, `eq_16_2`, `eq_16_4`). The
   envelope theorem (16.2) assumes the planner's value is differentiable at `y`.

10. **The First Welfare Theorem by matching weights.** The book infers from the coincidence of
    first-order conditions with `λᵢ = 1/αᵢ` that "the consumption allocations in the Arrow–Debreu
    equilibrium and the planner problem are the same". Matching first-order conditions identify
    the allocation only when they are sufficient; this is proved for concave utilities
    (`en_fwt_planner`), giving Pareto optimality (`en_fwt_pareto`). For expected utility on the
    infinite tree, Miao's `theorem_13_3_1` proves the First Welfare Theorem from local
    nonsatiation.

11. **The "three results" (p. 472) in the two-period economy.** The equivalence of
    Arrow–Debreu and sequential equilibrium (`eq_seq_to_ad`, `eq_ad_to_seq`) and the
    representative agent (`eq_repAgent`, `eq_repAgent_statePrice`) are proved in the two-period
    economy of §16.4. On the infinite tree the sequential budget (16.8) without a debt limit admits
    Ponzi schemes, which are arbitrages (Miao's `rd_ponzi_arb`); the equivalence needs debt
    constraints and transversality (Miao's `theorem_13_5_1_if`).

12. **Dynamic trading on a finite tree.** The dynamic fundamental theorem is proved on a finite
    event tree (`dt_ftap`, `dt_ftap_deflator`); the infinite-horizon version is not formalised.
    The first-order conditions (16.19) are derived at an interior optimum (`eu_foc`), as are the
    two-period ones (16.15) (`tp_portfolio_foc`, `eq_16_15`).

13. **iid growth.** Uniqueness of the constant price–dividend ratio (16.31) is proved for growth
    with finitely many values (`iid_pd_unique`); for the book's lognormal growth the constant
    ratio is verified to solve the equation (`iid_lognormal_pd`).

14. **Lognormal model.** "Jointly lognormal" is used in the form that `−γg + rˢ` is Gaussian with
    the mean and variance implied by the joint distribution (`lg_equity_euler`, `eq_16_30`).

## Figure claims

15. **p. 488, Figure 16.4: "the equity premium is less than 0.1 percent".** The figure scans
    `β ∈ [0, 1]`, `γ ∈ [0, 100]` and keeps the equilibria with mean riskless rate below 4%, with
    the growth process fixed by Table 16.1 (`μ = 0.0175`, `δ = 0.0233`, `2φ − 1 = 0.1069`, which
    the three moments identify exactly; `mpf_primitives`). With these primitives the printed
    bound is false: at `β = 1`, `γ = 9/4` the price–dividend ratio `v = (I − A)⁻¹A𝟙` exists
    (`ρ(A) < 1`), the mean riskless rate is about 3.78% and the equity premium about 0.103%
    (`mpf_counterexample`, `mpf_fig_16_4_printed_false`; `G^{−9/4}` enclosed to `10⁻⁷` by exact
    rational arithmetic). What is true on the whole region: `E[rᶠ] < 4%` forces `γ < 5/2`
    (`mpf_gamma_lt`), and the equity premium is positive for `γ > 0` and below 0.17%
    (`mpf_premium_bound`), proved from the covariance form of the premium (`mpf_premium_cov`),
    not at grid points. The exact supremum (between 0.103% and 0.17%) is not determined; the
    figure's message (a premium two orders of magnitude below the 7% of Table 16.1) stands. The
    figure's left edge (riskless rates from about 1%) is not reproduced by these primitives and is
    not formalised.
