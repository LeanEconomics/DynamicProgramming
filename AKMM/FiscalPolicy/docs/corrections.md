# Corrections and departures: AKMM Chapter 15

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 15, Government and public policies (M. Azzimonti, J. Heathcote and
K. Storesletten), pp. 439–466, and Appendix 15.A, pp. 868–870. Lean names are relative to
`AKMM.FiscalPolicy`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 451, the excess cost of taxation is increasing in `τ_k` and minimised at `τ_k = 0`.** "the
   excess cost of taxation is increasing and convex in the capital tax rate `τ_k`" and (§15.3.3)
   "the excess cost of taxation is minimized when `τ_k = 0`". The text infers this from Figure 15.6
   at its parameters. It is not a property of the model. Counterexample: `α = 1/2`, `β = 2/3`
   (`ρ = 1/2`), `δ = 1/10`, `φ = 1`, `g = 2/5`. The excess cost is `37/6` at `τ_k = 0` and
   `12013321/2706048 ≈ 4.44 < 37/6` at `τ_k = 1/5`, with `τ_ℓ < 1` at both
   (`inc_excess_cost_not_min_at_zero`); in the same economy capitalists' consumption is not
   maximal at `τ_k = 0` either (correction 8, `fig156_ck_not_max_at_zero`). What is true for every parameter value is the claim that
   precedes it, "the excess cost of taxation is always positive": along (15.14), for all
   `g > 0`, `0 ≤ τ_k < 1` with `τ_ℓ < 1`, `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0`
   (`inc_excess_cost_pos`, analytic). At the book's parameters (`α = .33`, `δ = .07`,
   `β = .97`, `φ = 1`, `g = .2`) the monotonicity and the minimum at `τ_k = 0` hold numerically, but
   the exponent `α(1 + φ)/(1 − α) = 66/67` puts them out of reach of the closed-form algebra used
   here; they are **not proved**, and convexity is not proved for any parameters.

2. **p. 456, the debt in the two-period Ricardian example.** "identical to that in the case of
   zero taxes and transfers (`T₀ = τ₁ = B₁ = 0`)". The government issues `B₀` at date 0 and repays
   it at date 1 (p. 455: `τ₁ = (1 + r₁)B₀`); there is no `B₁`. The comparison case is
   `T₀ = τ₁ = B₀ = 0` (`ricGov`, `ric_budgetSet_eq`).

3. **p. 461, household wealth at date 1.** "household wealth `b₁` is already determined". In the
   two-period model the saving carried into date 1 is `b₀` (p. 457: `b_{t−1}` is wealth at the
   start of `t`; date-1 income from wealth is `(1 + r(1 − τ_{b,1}))b₀`). The re-optimisation
   results use `b₀` (`tc_household_line`, `tc_time_inconsistent`).

4. **p. 463, when PAYG raises the young's present value.** "the pension system increases the
   present value of household income for the young if and only if wage growth exceeds the
   interest rate, i.e., iff `γ + n > r`". The derivative of the right side of (15.21) in `τ_p` is
   `((1 + n)(1 + γ)/(1 + r) − 1)y_t`, positive iff `(1 + n)(1 + γ) > 1 + r`
   (`olg_pv_increasing_iff`); `γ + n > r` is its first-order approximation (the book itself writes
   `1 + r_p = (1 + n)(1 + γ) ≈ 1 + n + γ`). Counterexample to the exact "iff": `n = γ = 1/10`,
   `r = 41/200` (`olg_pv_approx_false`). The same applies to "if the interest rate is lower than
   the wage growth rate `n + γ`" for the Pareto improvement (`olg_payg_pareto` uses
   `(1 + n)(1 + γ) > 1 + r`).

5. **p. 869, Appendix 15.A.2, the workers' budget.** "with `c_w = ((1 − τ_t^l)/(1 + τ_t^c))w`".
   Hand-to-mouth workers consume their after-tax labour income, `c_w = ((1 − τ_ℓ)/(1 + τ_c))wℓ`
   (p. 449). With the factor `ℓ` the first-order condition reads `ℓ^{1/φ} = 1/ℓ`, so
   `ℓ^{1+1/φ} = 1` and `ℓ = 1` (`app_15_A_2_foc`), and `ℓ = 1` is the worker's unique optimum
   (`app_15_A_2`). The conclusion `ℓ = 1` is unaffected.

6. **p. 452 and p. 869, figure references.** "The left panel of Figure 24.4 displays the evolution
   of capital and labor income taxes" (p. 452) and "The main difference between Figure 24.4 and
   Figure 15.A.1" (p. 869). The tax-reform figure is Figure 15.7; Figure 24.4 belongs to
   Chapter 24. Not a formal claim; no theorem.

7. **p. 869, `G/Y` along the transition.** "recall that the exercise is constructed such that
   `G/Y = 0.2` throughout the simulation". On p. 451 the exercise is constructed differently: tax
   rates are held constant and "We allow `G_t` to vary during transition to balance the
   government budget date by date"; `G/Y = 0.2` holds in the initial and final steady states
   (p. 452: "recall that `G/Y` is identical in the initial and final steady states"). Not
   formalised (the transition is numerical).

8. **p. 450, Figure 15.6, Panels B–C: the shapes of `c_w` and `c_k`.** "When `τ_k` is restricted
   to be non-negative, steady-state consumption of capitalists is maximized at `τ_k = 0`, while
   consumption of workers is a hump-shaped function of `τ_k`." The text reads both off the figure
   at its parameters. Along (15.14) (`τ_c = 0`, no transfers), with `c = ρ + δ`,
   `s = α(1 − τ_k)/(ρ + δ(1 − τ_k))` and `e = α(1 + φ)/(1 − α)`, one has
   `c_w = (1 − g − cs)^{1+φ}s^e` and `c_k = ρ(1 − g − cs)^φs^{1+e}` (`fig156_cw_eq`,
   `fig156_ck_eq`), and both are single-peaked in `s` (`fig156_hump_strictMonoOn`,
   `fig156_hump_strictAntiOn`). For all `0 < α < 1`, `0 < β < 1`, `δ ≥ 0`, `φ > 0`:
   - **`c_w` is hump-shaped for every `0 < g < 1 − α`** (`g < 1 − α` is `τ_ℓ(0) < 1`, which the
     figure needs to start at `τ_k = 0`): strictly increasing on `[0, τ_w]`, strictly decreasing on
     `[τ_w, 1)`, `τ_w = g(ρ + δ)/(ρ + δg) ∈ (0, 1)` (`fig156_cw_hump`, `fig156_cw_isMaxOn`). At the
     peak the labour tax is exactly `g`, so labour and capital income are taxed at the same average
     rate (`fig156_cw_peak_tauL`). (For `g ≤ 0` the peak `τ_w ≤ 0` and `c_w` falls on `[0, 1)`; this
     case is not stated in Lean.) The book's claim holds for every admissible parameter value; the
     only addition is the explicit range `0 < g < 1 − α`.
   - **`c_k` is maximal at `τ_k = 0` iff `g ≤ (1 − α)/(1 + αφ)`** (equivalently
     `τ_ℓ(0) ≤ 1/(1 + αφ)`), given `g < 1 − α` (`fig156_ck_max_at_zero_iff`); then `c_k` is
     strictly decreasing on `[0, 1)` (`fig156_ck_strictAntiOn`). For
     `(1 − α)/(1 + αφ) < g < 1 − α`, `c_k` rises on `[0, τ_c]` and falls on `[τ_c, 1)`, with
     `τ_c = (1 − K)(ρ + δ)/(ρ + δ(1 − K)) ∈ (0, 1)`, `K = (1 + αφ)(1 − g)/((1 + φ)α)`
     (`fig156_ck_hump`). Counterexample to the unqualified claim, at the parameters of correction 1
     (`α = 1/2`, `β = 2/3`, `δ = 1/10`, `φ = 1`, `g = 2/5 > 1/3`): `c_k = 25/864` at `τ_k = 0` and
     `21600/707281 > 25/864` at `τ_k = 1/5` (`fig156_ck_not_max_at_zero`; there `τ_c = 2/17`).
     At the book's parameters `g = .2 < .67/1.33`, so the claim holds there (as a case of the
     general theorem, not by computation). This is consistent with correction 1: in the same
     economy, where a high `g` makes the labour tax at `τ_k = 0` large (`τ_ℓ(0) = 4/5`), a positive
     capital tax both raises capitalists' consumption and lowers the excess cost.
   Panel A's shape needs no correction: `τ_ℓ` is strictly decreasing and concave in `τ_k`
   (strictly concave for `δ > 0`, affine for `δ = 0`) for all parameters
   (`fig156_tauL_strictAntiOn`, `fig156_tauL_concaveOn`, `fig156_tauL_strictConcaveOn`), and for
   `0 < g < α` it changes sign exactly at `τ_k = g(ρ + δ)/(ρα + gδ)` (`fig156_tauL_neg_iff`).

## Not proved

- **The excess cost of taxation at the book's parameters** (p. 451): increasing and convex in
  `τ_k`, minimal at `τ_k = 0`, for `α = .33`, `δ = .07`, `β = .97`, `φ = 1`, `g = .2`. True
  numerically (Figure 15.6) but not proved; false for other parameters (correction 1).
- **`µ > 0` in general** (p. 461): proved when `1 + µ + µ/φ > 0` or `σ ≥ 1`, together with
  `µ ≠ 0` and `τ > 0` whenever the present value of spending is positive (`rm_mu_pos`,
  `rm_tax_pos`).

## Departures (modelling choices)

- **Definition 15.1, domains and the household optimum.** The book does not state the domains of
  `c` and `ℓ`. We impose only the borrowing constraint `k_{t+1} ≥ 0` and let `u` be any function
  on `ℝ × ℝ`; lifetime utility is the sum of a summable sequence and the household optimum is
  taken over plans with summable utility (`definition_15_1`; non-vacuity `dt_example_ce`). The
  first-order conditions (15.6)–(15.7) are proved where `u` (and `f`) are differentiable and, for
  the Euler equations, where `k_{t+1} > 0` (`eq_15_6`, `dt_planner_euler`). Firms choose
  `k, ℓ ≥ 0`.
- **Steady states (§15.3.1–15.3.4)** are parametrised by `s = (k/ℓ)^{1−α}` (`lrS`); `τ_c = 0` and
  `T = 0` from (15.14) on, as in the book.
- **Theories of G.** `f_k − δ = f_g − δ_g` is proved for the planner's split of a given saving
  between private and public capital (`tg_net_returns_equal`), the margin on which the two Euler
  equations differ; the dynamic planner is not restated.
- **Laffer curve.** Footnote 6's "tax revenue is declining in `τ_k` at `τ_k = 0`" is replaced by
  the global statement that every `τ_k > 0` raises strictly less than the maximum
  (`laf_lt_of_pos`); the first-order condition is replaced by global maximality (`footnote_6`).
- **Ramsey.** A competitive equilibrium is characterised by first-order conditions and budgets,
  as the book does on p. 459 (`rmCE`). The existence of multipliers at a Ramsey optimum (a
  constraint qualification) is assumed, as in the book: the printed first-order conditions are
  proved to be the partial derivatives of the Lagrangian (`rm_foc_c0` …), and the tax results
  hold for allocations satisfying them with explicit interiority conditions
  `1 + µ − µσ ≠ 0`, `1 + µ + µ/φ ≠ 0` (`rm_crra_euler`, `rm_crra_labour`, `rm_ramsey_taxes`).
- **Time consistency.** The comparison is between the Ramsey date-1 allocation and the household's
  optimum under the re-optimised plan, assumed to exist (`tc_time_inconsistent`).
- **OLG.** The aggregate-consumption effects of the tax holiday are proved with consumption
  proportional to lifetime income, which holds for log utility (`olg_log_consumption`,
  `olg_holiday_aggregate`); the book argues for general utility.
