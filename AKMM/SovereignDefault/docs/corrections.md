# Corrections and departures: AKMM Chapter 24

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 24, Sovereign debt and default risk (Juan Carlos Hatchondo and Leonardo
Martinez), pp. 729–748, and Appendix 24.A, pp. 897–908. Lean names are relative to
`AKMM.SovereignDefault`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 741, (24.5), the middle term.** Printed `q₁(B₂) = E[1 − D̂₂(B₂)] = Pr(Y₂ < B₂/φ) =
   1 − F(B₂/φ)`. By (24.4) `Pr(Y₂ < B₂/φ)` is the *default* probability; the repayment
   probability is `Pr(Y₂ ≥ B₂/φ)`, which equals `1 − F(B₂/φ)` because `Y₂` has a density
   (`eq_24_5`). At `B₂ = 0` the printed middle term is `0` while the price is `1`
   (`eq_24_5_printed_false`). PDF page rendered.

2. **p. 748, (24.13), the sign.** Printed `u′(C_t)[q_t + ∂q_t/∂B_{t+1}(B_{t+1} − (1 − δ)B_t)] =
   βE[V₁(B_{t+1}, Y_{t+1}) | Y_t]` with "`V₁` the derivative of the government's value function
   with respect to debt". Differentiating the objective of (24.11) gives
   `u′(C)[q + q′(B′ − (1 − δ)B)] + βE[V₁] = 0`, i.e. the right-hand side is `−βE[V₁]`
   (`eq_24_13`). Since `V` decreases in debt (`sd_V_antitone`, `mpe_V_antitone`), `−βE[V₁] ≥ 0`
   matches the nonnegative marginal revenue on the left (`eq_24_13_sign`) and the two-period
   analogue (24.6), whose right-hand side `βE[u′(Ĉ₂)(1 − D̂₂)]` is `−β d/dB₂ E u(Ĉ₂)`
   (`tp_hasDerivAt_expectedUtility`). The printed equation is false whenever `βE[V₁] ≠ 0`
   (`eq_24_13_printed_false`; explicit instance `eq_24_13_printed_counterexample`). PDF page
   rendered.

3. **p. 902, Table 24.A.1, the mean of log income.** Printed `µ = (−1/2)σ_ε²`, "chosen so that
   the unconditional income expectation `E(Y) = 1`" (p. 901). For
   `log Y_t = (1 − ρ)µ + ρ log Y_{t−1} + ε_t` the stationary variance of `log Y` is
   `σ_ε²/(1 − ρ²)` (`cal_ar1_variance`), so `E Y = exp(µ + σ_ε²/(2(1 − ρ²)))`
   (`cal_lognormal_mean`) and `E Y = 1` iff `µ = −σ_ε²/(2(1 − ρ²))` (`cal_mean_one_iff`). The
   printed value gives `E Y = exp(ρ²σ_ε²/(2(1 − ρ²))) > 1` for `ρ ≠ 0`
   (`cal_table_mu_printed_false`; with `ρ = 0.91` the exponent is `4.8σ_ε²/2`). PDF page
   rendered (the table writes `σ_ε`, so the symbol is not the risk-aversion `σ`).

4. **p. 730, (24.1), timing.** Printed `C_{t+1} + K_{t+1} = Y_t + K_t(1 − d) +
   q(Y_t, η_t, B_{t+1})B_{t+1} − B_t`: every other term is dated by the period in which it is
   paid or received, so the period-`t` resource constraint has `C_t`. Moderate confidence (the
   equation is an empirical sketch); no theorem. PDF page rendered.

5. **p. 898, (24.A.3), a missing `∂`.** Printed `q₁(B̂(B, Y), Y) B̂(B, Y)/∂Y`; read
   `∂B̂(B, Y)/∂Y` (`eq_24_A_3`). PDF page rendered.

6. **p. 900, (24.A.5), the index range.** Printed `max_{h′ = 1, …, N}`: the debt grid is
   `{B¹, …, B^M}` (p. 897) and the shock vector has the `M` borrowing shocks `ε₁, …, ε_M`; the
   range is `h′ = 1, …, M` (as in (24.A.6), `h = 1, …, M`). No theorem.

7. **p. 897, (24.A.1), the default update.** Printed `Σ_j π_{i,j}[ψV_I(0, Y′) +
   (1 − ψ)V_I^D(Y′)]`: the summation variable is `Y^j`; read `V_I(0, Y^j)`, `V_I^D(Y^j)`
   (`SDModel.defaultValue`). Also the update of `V` maximises over `d ∈ {0, 1}` a
   function of `D`. No theorem.

8. **Minor typos.** p. 744, footnote 11: `B′ < (1 − δ)b` for `(1 − δ)B`. p. 899, the initial
   default rule `D̂₀(B, Y) = 1 if V₀^D(Y) and > V₀^R(B, Y)`: read `1 if V₀^D(Y) > V₀^R(B, Y)`.
   p. 901: the broken citation "(?; Neumeyer and Perri, 2005; …)". No theorems.

9. **p. 901, uniqueness for `δ = 1` and the grid of Appendix 24.A.1.** The book states that
   with one-period bonds "a unique equilibrium exists" (Auclert–Rognlie 2016, Aguiar–Amador
   2019) while computing on finite grids (p. 897). The uniqueness holds with a continuum of
   debt choices that allows saving (proved here, `ue_mpe_unique`, departure D10) but not on a
   finite debt grid: with one income level, debt grid `{0, 1}`, `u = id`, `φ = 1/4`,
   `β = 1/2`, `ψ = 0`, `r = 1/4` and `δ = 1` there are two Markov perfect equilibria, one
   without default at the price `4/5` and one with self-fulfilling default on debt `1` at the
   price `0` (`mu_grid_one_period_two_mpe`; the same economy with `δ = 1/2` has two as well,
   `mu_grid_long_term_two_mpe`). On a continuum the sovereign escapes the bad equilibrium by
   issuing slightly less debt (`ue_replication`); on the grid the nearest lower debt is `0`.
   So the computed grid equilibrium need not be unique even when `δ = 1`.

Checked and not an error: (24.A.7) gives the loss fraction `λ₀Y + λ₁(Y − E Y)`, which at
`Y = E Y = 1` equals `λ₀`, so "`λ₀` determines the average fraction of income lost" holds
(`cal_phi_at_mean`). The duration `(1 + i)/(δ + i)` (p. 902) and the yield formula (p. 903) are
correct (`ltd_duration`, `ltd_yield`). (24.4) with ties repaid, (24.6) and (24.12) are correct
as printed (`eq_24_4`, `eq_24_6`, `eq_24_12`).

## Departures and hypotheses made explicit

D1. **Existence of an optimal `B₂` (p. 741).** The book writes "Equilibrium borrowing `B̂₂`
   satisfies (24.6)" without showing that an optimum exists. We prove existence
   (`tp_exists_optimal`) for `u` real valued, continuous, nondecreasing and strictly increasing on
   `[0, ∞)`, with `E|u(Y₂)|`, `E|u((1 − φ)Y₂)|` and `E Y₂` finite, `Y₂ ≥ 0` without atoms and
   `Pr(Y₂ > 0) > 0`. The Inada condition is not used; `u = log` (unbounded at `0`) is outside
   this theorem.

D2. **The Leibniz rule and (24.6) (p. 741).** Differentiating `E u(Ĉ₂)` needs `φ < 1` (the book
   says `φ` is "a fraction", so `φ ≤ 1`; at `φ = 1` default consumption is `0` and the
   Lipschitz bound fails) and `u` differentiable, increasing and concave on `(0, ∞)`; (24.6)
   holds at an interior optimum where `q₁` is differentiable (`F` has a density at `B̂₂/φ`,
   `tp_price_hasDerivAt`) and `C₁ > 0` (`tp_hasDerivAt_expectedUtility`, `eq_24_6`).

D3. **Present value of debt (p. 903).** "the present value of future payment obligations
   discounted at the risk-free rate, that is `δB_t/(δ + r)`": with `B_t` the bonds due at the
   start of `t`, `δB_t/(δ + r)` is the value one period before `t` (equivalently, the value at
   `t` of the end-of-period stock `B_{t+1}` is `δB_{t+1}/(δ + r)`). Valued at `t` the payments
   of `B_t` are worth `δ(1 + r)B_t/(δ + r)` with the current coupon and `δ(1 − δ)B_t/(δ + r)`
   without it (`ltd_pv_bond`, `ltd_pv_stock_timing`). A timing convention, not an error in the
   calibration.

D4. **Finite grids for the infinite-horizon model (§24.4, (24.9)–(24.12)).** The book states the
   recursive problem with a continuous income distribution `F(dY′ | Y)` and a continuous debt
   choice `B′ ≥ 0`. We formalise it on a finite debt grid (containing `0`) and a finite income
   grid with a Markov matrix, the setting of Appendix 24.A.1, (24.A.1)–(24.A.2). Every result
   (contraction of the price map, Bellman uniqueness, monotonicity in debt, default sets, the
   Markov perfect equilibrium as a fixed point) is proved for arbitrary finite grids.

D5. **`φ(Y)/Y` increasing (p. 743) under (24.A.7).** The loss fraction
   `max{λ₀Y + λ₁(Y − E Y), 0}` is nondecreasing in `Y` when `λ₀ + λ₁ ≥ 0` (true for Table
   24.A.1) and constant (zero) for low incomes, so it increases only weakly
   (`cal_phi_div_monotone`).

D6. **The borrowing probabilities in (24.A.6) (p. 900).** The text calls `B(B^m | B^h, Y^i)`
   "the probability that the sovereign chooses debt `B′ = B^m`". In (24.A.6) it multiplies
   `[1 − D]`, so it must be the probability *conditional on repayment* (summing to one); the
   unconditional probability sums to `1 − D` and would count repayment twice. We formalise
   conditional probabilities (`BPAdmissible.B_sum`) and show that under extreme-value shocks
   they are logit over the debt choices (`ev_conditional_borrow`, `eq_24_A_6_logit`).

D7. **Extreme-value choice probabilities (Method 3, p. 900).** The book's shocks are "drawn from
   a multivariate distribution with continuous support"; the logit formula (24.A.6) uses i.i.d.
   standard Gumbel shocks (Dvorkin et al. 2021), which we assume. The choice probability is
   derived from the product law (`ev_logit_of_gumbel`), and it agrees with the conditioning
   formula `∫ g(x) Π_{k≠h} G(x + v_h − v_k) dx` (`ev_choiceProb_eq_gumbel`, `ev_logit`).

D8. **Markov perfect equilibrium (§24.4.3, p. 901).** The definition is formalised on finite
   grids (`IsMPE`, an instance `mpe_example`) and characterised as a fixed point of the
   equilibrium map (`mpe_iff_fixedPt`). Existence and uniqueness for one-period debt
   (Auclert–Rognlie 2016; Aguiar–Amador 2019), cited by the book, are proved beyond the text
   (decision 5) in the continuous-debt setting of departure D10 (`ue_mpe_exists`,
   `ue_mpe_unique`, `ue_mpe_exists_unique`, instance `ue_example_exists_unique`); on finite
   grids they fail (correction 9). Multiplicity with long-term debt is shown on a grid
   (`mu_grid_long_term_two_mpe`) and, with a continuum of debt levels, in an explicit economy
   with two equilibria at `δ = 1/2` and one at `δ = 1` (`ld_two_mpe`, `ld_one_period_unique`,
   departure D12); Aguiar–Amador's (2020) own construction, with strict preference for
   dilution, is not formalised. The limit of the finite-horizon game is proved for `δ = 1`
   (`fh_example_limit` and the theorems of departure D11); for `δ < 1` it is not.

D9. **The default threshold `Y*(B)` (p. 904).** "As is standard in equilibrium default models,
   this threshold is unique": the text gives no argument and the claim needs a single crossing
   of `V^R(B, ·) − V^D` in `Y`; not formalised. What the model implies without it is proved:
   default sets grow with debt (`sd_default_set_mono`, `mpe_default_mono`); in the two-period
   model the threshold `B₂/φ` is explicit (`eq_24_4`).

D10. **The setting of the existence and uniqueness theorem (p. 901, beyond the text).** The
   book's model of §24.4 with one-period debt `δ = 1`, finitely many income states with a
   Markov matrix, risk-neutral lenders with `r > 0` and the following choices (`UEModel`,
   `IsOneMPE`):
   * **permanent exclusion**, `ψ = 0` (the original Eaton–Gersovitz model): with re-entry the
     default value depends on the equilibrium value at zero debt, and the replication argument
     does not compare the two default values; the case `ψ > 0` is not covered;
   * **a continuum of debt levels with saving**: the sovereign chooses any `B′ ≤ B̄` (a
     borrowing limit `B̄ ≥ 0`), including `B′ < 0`, where the book imposes `B′ ≥ 0` (p. 744,
     "not binding in the simulations"); states `B ∈ ℝ`. The replication argument needs the
     sovereign to be able to hold slightly less debt, including below zero; on a grid
     uniqueness fails (correction 9);
   * **utility**: `u : ℝ → ℝ` nondecreasing and uniformly continuous (uniqueness); for
     existence also satiated, `u(c) = u(c̄)` for `c ≥ c̄`, which bounds values and makes
     saving beyond the level that finances `c̄` forever useless, so optimal borrowing exists
     (the book's CRRA utility is unbounded and defined only for `c > 0`, so it is excluded);
   * **default cost** `φ(Y) ≥ 0`;
   * values are bounded functions (part of `IsOneMPE`), and (24.11) is a maximum attained by
     the borrowing rule, as in the book's (c). The borrowing rule is unique only up to the
     choice among maximisers; values, default rule and prices are unique.
   The finite-horizon game (departure D11) and the long-term-debt equilibrium (departure D12)
   use the same setting.

D11. **The limit of the finite-horizon game (App. 24.A.1, pp. 899 and 901, beyond the text).**
   The book starts its iteration from "the solution in the final period of a finite horizon
   model" (`V₀^R = u(Y − δB)`, `V₀^D = u(Y − φ(Y))`, `q₀ = 0`, `B̂₀ = 0`) and states that it
   thereby finds "the equilibrium that is the limit of the finite horizon game as T → ∞",
   without proof. We prove it in the setting of D10 (`δ = 1`, `ψ = 0`, `B′ ≤ B̄` with saving):
   * the finite-horizon game (`IsFHEqm`) uses the book's terminal period as stage `0`; the
     objects of a stage do not depend on the horizon, so the `T`-period game is the first
     stages of one sequence. It is unique by backward induction (`fh_unique`, no hypotheses,
     no replication argument) and exists for `u` nondecreasing, uniformly continuous and
     satiated with `φ ≥ 0` (`fh_exists`);
   * convergence to the unique MPE (`fh_default_sets`, `fh_capacity_tendsto`,
     `fh_values_tendsto`, `fh_price_tendsto`) assumes in addition a **slope condition**:
     `κ(c′ − c) ≤ u(c′) − u(c)` for `c ≤ c′ ≤ c̄`, `κ > 0`, with `Y + B̄/(1 + r) ≤ c̄` for every
     income (consumption under repayment of a debt `B ≥ 0` never exceeds `c̄`). It turns the
     value error of the truncated horizon, `βⁿe₀`, into a debt reduction `βⁿe₀/κ` at the
     repayment boundary. The book's CRRA utility is excluded by D10 anyway; `u = min(c, c̄)`
     satisfies the condition (`fh_example_hyp`). Without it only the one-sided bound is proved
     (`fh_upper`: the finite horizon never repays more than the equilibrium);
   * the argument is the joint one: with `ψ = 0` the default value is exogenous and the
     comparison is on `V^R − V^D`; the debt reduction obeys
     `g_{n+1} = (gₙ + βⁿe₀/κ)/(1 + r)`, a moving contraction, and the general lemma
     `fh_moving_contraction` (`Φₙ → Φ` uniformly, `Φ` a contraction) gives `gₙ → 0`;
   * the sense of convergence: default values, repayment values and values uniformly in
     `(B, Y)`; debt capacities `b̄ₙ(Y) ∈ [b̄(Y) − xₙ, b̄(Y)]`; default rules and prices at every
     debt where the equilibrium default rule is constant on some `[B, B + η]`, and
     `q(B′ + xₙ) ≤ q_{n+1}(B′) ≤ q(B′)` everywhere (at a capacity the finite-horizon price can
     stay strictly below the limit).
   The case `δ < 1`, where the equilibrium need not be unique (D12), is not covered.

D12. **Multiplicity with long-term debt and a continuum of debt levels (p. 901, beyond the
   text).** The equilibrium with long-term debt (`IsLongMPE`) is the book's (a)–(c) with
   (24.7)–(24.12): consumption `Y − δB + q(B′, Y)(B′ − (1 − δ)B)` and the price
   `(1 + r)⁻¹E[(1 − D̂)(δ + (1 − δ)q(B̂(B′, Y′), Y′))]`, in the setting of D10 (`ψ = 0`,
   `B′ ≤ B̄` with saving, states `B ∈ ℝ`, bounded values); at `δ = 1` it is exactly
   `IsOneMPE` (`ld_one_iff`). The economy `ld_econ` (deterministic `Y = 2`,
   `u(c) = min(c, 1)`, `φ = 1/2`, `β = 1/2`, `r = 1/4`, `B̄ = 7`) has two equilibria at
   `δ = 1/2` (`ld_two_mpe`): without dilution, every debt `B′ ≤ 6` trades at the risk-free
   `δ/(r + δ) = 2/3`; with self-fulfilling dilution, a sovereign with `B ≤ 2` issues up to
   `7` and defaults next period, so `B′ ≤ 2` trades at `δ/(1 + r) = 2/5`
   (`ld_dilution_lowers_prices`). At `δ = 1` the same economy has a unique equilibrium
   (`ld_one_period_unique`, by `ue_mpe_exists_unique`). What the example is and is not: the
   value functions and default rules coincide across the two equilibria and only the prices and
   borrowing rules differ; the low-debt sovereign is satiated whatever it issues and default is
   costless in utility (`Y − φ ≥ c̄`), so it is indifferent and lenders' beliefs select its
   rule. It isolates the channel only long-term debt has (the price depends on the expected
   borrowing rule, `bp_long_term_depends_on_borrowing`), not Aguiar and Amador's (2020)
   mechanism, where the sovereign strictly prefers to dilute and values differ; that
   construction is not formalised.
