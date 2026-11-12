# Corrections and departures: AKMM Chapter 17

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 17, Money (A. Hornstein and P. Krusell), pp. 493–531. Lean names are
relative to `AKMM.Money`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 514, inflation under constant money growth.** The book says "a unique steady-state
   equilibrium in which the rate of inflation equals the inverse of the money growth rate". With
   constant real balances `P_{t+1}/P_t = M_{t+1}/M_t`, so inflation *equals* the money growth
   rate. It is the price of money `p_m` that changes at the inverse rate. p. 522 itself says "the
   price level grows at the money growth rate". In the money-growth OLG economy
   `p_{m,t+1}/p_{m,t} = 1/(1 + µ)` and `P_{t+1}/P_t = 1 + µ` (`mg_return`).

2. **p. 503, (17.14), the discount factor of `m_T`.** Printed as `lim q₀q₁⋯q_T m_T`, but the
   expansion stops at `p_{m,T−1}/p_{m,T}`. The discount factor of `m_T` is `q₀⋯q_{T−1}`, and then
   `q₀⋯q_{T−1}m_T = p_{m,0}M_T` (`eq_17_14`). The printed product gives `p_{m,0}M_T q_T`
   (`dyn_printed_product`). The conclusion is unaffected (`dyn_tvc_money_vanishes`,
   `dyn_no_valued_money`).

3. **p. 496, cross-reference.** "Asset pricing, as discussed in Chapter 15". Asset prices are
   Chapter 16; Chapter 15 is government and public policies.

4. **p. 516, (17.40), "If `φ′(1) < 0`, then there is indeterminacy".** The linearised map has
   slope `1 + φ′(1)/(1 + ĩ)` (`rule_map_hasDerivAt`). There is a continuum of solutions near the
   target iff the modulus is below one, i.e. `−2(1 + ĩ) < φ′(1) < 0`
   (`rule_phi_neg_indeterminate`). For `φ′(1) < −2(1 + ĩ)` the deviation is explosive and
   oscillating, and the bounded solution is again unique (`rule_phi_very_neg_determinate`).
   Counterexample to the printed claim: `φ(x) = −3(x − 1)`, `ĩ = 0`, `φ′(1) = −3`, has the unique
   solution `x ≡ 1` near `1` (`rule_printed_counterexample`). The claim for `φ′(1) > 0` is correct
   (`rule_phi_pos_determinate`).

5. **p. 522, the `i = 0` budget.** Printed as
   `(M_t + B_t)/P_t = τ_t − g_t + (1/r_t)(M_{t+1} + B_{t+1})/P_{t+1}`. From (17.44) the discount
   factor is `1/(1 + r_t)` (`gb_zero_rate`). The two differ whenever `r_t > 0` and next-period
   liabilities are nonzero (`gb_zero_rate_printed`).

6. **p. 520, (17.43), the discount factors.** Printed as `q_{0,t} = ∏_{s=0}^{t} q_s`. This
   discounts the date-0 flow by `q₀`. Consistency with (17.42) at `t = 0` (and with (17.46),
   whose sum starts at `β⁰ = 1`) requires `∏_{s=0}^{t−1} q_s`, so that `q_{0,0} = 1` (`eq_17_43`).
   Counterexample to the printed weights: `q ≡ 1/2`, `b̂₀ = s₀ = 1` and all other terms zero
   satisfy every flow budget. The correct weights give `∑ q_{0,t}s_t = 1 = b̂₀`, the printed ones
   `1/2` (`gb_printed_discount`).

7. **p. 519, footnote 18.** Printed as "`u_{1,2}m₁/u₁`, we obtain `(f″/f′)h_{2,2} + h_{1,2}m₁/h₁`".
   Since `u₁ = f′h₁`, `u₁₂ = f″h₂h₁ + f′h₁₂`, so `u₁₂m₁/u₁ = (f″/f′)h₂m₁ + h₁₂m₁/h₁`
   (`cl_footnote_18_identities`). The first term contains `h₂m₁`, not `h_{2,2}`. The limit claims
   hold with the corrected term (`cl_footnote_18_limits`).

## Added hypotheses

1. **p. 513, hyperinflation paths.** The book says "for any initial real balances `0 < m₀ < m̄`
   the path of real balances defined by equation (17.38) converges" to zero. (17.38) defines
   `m_{t+1}` only implicitly, and without monotonicity of `m u′(m)` it can have several solutions.
   Proved: with `u′` continuous and strictly decreasing and `m u′(m) → 0`, from every
   `m₀ ∈ (0, m̄)` *some* path decreases to zero (`hyp_exists_path`). If in addition `m u′(m)` is
   strictly increasing, the path is unique and *every* such path decreases to zero
   (`hyp_all_paths`). Without that hypothesis, convergence of every path is not proved.
   Footnote 11's local statements are proved with `u′ ≷ k` near zero (`hyp_local_stable`,
   `hyp_local_unstable`), in place of a value `u′(0)`.

2. **p. 521, the seigniorage Laffer curve.** "Under rather weak assumptions on `f`, the product
   expression will have a maximum". A strictly decreasing `f` is not enough: `f(i) = 1 + 1/(1 + i)`
   gives revenue `1 − 1/(1 + i)²`, strictly increasing with no maximum (`lf_counterexample`). Proved
   under the added hypotheses that `f` is continuous and positive with `f(i)i → 0` as `i → ∞`
   (`lf_interior_max`). The chapter's own transactions-cost demand (17.29) does not satisfy them:
   its seigniorage is strictly increasing in `i` (`lf_tc_no_max`).

3. **p. 523, the fiscal theory.** "The argument of course requires that `B₀ > 0`". It also
   requires a positive present value of surpluses, `τ̃ > g̃` (and `1 + i_{−1} > 0`). Then `P₀` exists
   and is unique (`ftpl_unique`); with `B₀ > 0` and `τ̃ ≤ g̃` there is no positive price level
   (`ftpl_none`).

4. **p. 516, footnote 15.** "The knife-edge case `φ′(1) = 0` leads to indeterminacy as well: a
   continuum of … (constant) solutions". Proved for an affine rule, for which `φ′(1) = 0` means
   `φ ≡ ĩ` (`rule_knife_edge`). For a nonlinear `φ` with `φ′(1) = 0`, constant solutions other than
   `1` need not exist; this case is not treated.

## Departures

1. **§17.2.1, the equilibrium notion.** The book defines equilibrium informally ("the young buying
   the entire money stock"). Here an equilibrium is a nonnegative price sequence such that at every
   date holding the stock `M` is optimal for the young (`olgIsEquilibrium`). The dichotomy "money
   valued at all dates or at none" is then proved, not assumed (`eq_17_5`). A young agent facing
   `p_{m,t} = 0 < p_{m,t+1}` has no optimum (`olg_moneyOptimal_zero_pos`).

2. **§17.2.2, welfare "left as an exercise".** Proved:
   - the ranking by `p_{m,0}` for every cohort and for the initial old (`olg_ranking`);
   - the improvement on autarky (`olg_monetary_improves_autarky`);
   - dominance by the stationary equilibrium (`olg_stationary_dominates`).

   The efficiency statements use Miao's Pareto notion (`olg_miao_stationary_pareto`,
   `olg_miao_autarky_pareto_iff`).

3. **§17.2.3, money growth.** The book does not say how the new money is distributed. Here it is
   given to the old as a lump-sum transfer `µM_t`, with `µ ≥ 0` (`mgIsEquilibrium`). Only the
   stationary equilibrium and the equilibrium difference equation are formalised
   (`mg_stationary_iff`, `mg_step_iff`). The "same type of characterization" for non-stationary
   paths is not proved.

4. **First-order conditions and transversality.** As in the book, the first-order conditions of
   the dynastic problems (17.20)–(17.23), (17.26)–(17.27) and (17.31)–(17.34) are taken as given
   (they are hypotheses). So is the transversality condition, which the book takes from Chapter 4
   (`dyn_tvc_money_vanishes`, `cia_must_bind`). In (17.43) the vanishing of the discounted terminal
   liabilities is a hypothesis; the book derives it from the household's transversality condition
   and market clearing (fn. 19).

5. **§17.3.3, the CIA peg.** Existence of an equilibrium for every `p_{m,0}` assumes an inverse of
   `u′` on `[1, ∞)` (`peg_exists`).

6. **§17.4.1, Kareken–Wallace with growing stocks.** The steady-state value, Gresham's law and the
   comparison with the `e = 0` equilibrium are proved (`kw_limit_formula`, `kw_gresham`,
   `kw_limit_lower`). Existence of an equilibrium path converging to the limit is **not proved**:
   the book defers the proof to the appendix of Kareken and Wallace (1981).

7. **§17.5, the Huggett economy.** The autarky price, the ranking of valuations and the price level
   are proved (`ma_autarky_price`, `ma_valuation_high_gt_low`, `ma_price_level`). The existence of a
   stationary distribution with positive aggregate saving at `q = 1` is not re-proved; it is a
   hypothesis (`m > 0`), as in Miao's treatment (`IncompleteMarkets`).
