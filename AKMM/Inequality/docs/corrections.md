# Corrections and departures: AKMM Chapter 21

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 21, Inequality (Per Krusell and José-Víctor Ríos-Rull), pp. 627–662. Lean
names are relative to `AKMM.Inequality`. Every book item is located in the
[source map](source-map.md).

## Corrections

1. **p. 640, the directed-technology first-order condition.** Printed
   `A_s/A_u = (λ/(1 − λ)) (s/u)^{σ/(φ−σ)}`. The first-order conditions of
   `max (A_s s)^σ + (A_u u)^σ` s.t. `λA_s^φ + (1 − λ)A_u^φ = 1` give
   `(A_s/A_u)^{σ−φ} (s/u)^σ = λ/(1 − λ)`, so
   `A_s/A_u = (λ/(1 − λ))^{1/(σ−φ)} (s/u)^{σ/(φ−σ)}` (`dt_ratio`, `dt_foc_iff_ratio`,
   `dt_maximiser_ratio`). The printed factor agrees only when `λ = 1/2`
   (`dt_printed_ratio_iff`). The log-proportionality that follows, and its coefficient
   `(σ − φ(1 − σ))/(φ − σ)`, are unaffected (`dt_log_premium`). PDF page rendered.

2. **p. 648, footnote 25, the gross return under progressive capital taxation.** Printed
   `1 + (r − δ)(1 − τ(a) − τ′(a)/a)`. The derivative of gross capital income
   `a(1 + (r − δ)(1 − τ(a)))` is `1 + (r − δ)(1 − τ(a) − aτ′(a))` (`pt_hasDerivAt`); `τ′/a` is
   not even dimensionless. The two agree only if `r = δ`, `τ′(a) = 0` or `a² = 1`
   (`pt_printed_iff`); with `τ(a) = a/10`, `r − δ = 1/10`, `a = 2` the true return is `1.06`
   and the printed one `1.075` (`pt_printed_counterexample`). The steady-state condition is
   `β(1 + (r − δ)(1 − τ(a) − aτ′(a))) = 1` (`pt_steady_euler`). PDF page rendered.
3. **p. 651, Kesten's theorem.** "`aₜ` converges in probability to a random variable `A`": the
   Kesten–Goldie theorem gives convergence in distribution (the law of `aₜ` converges to the
   stationary law). `aₜ` keeps being hit by fresh i.i.d. shocks and in general does not converge
   in probability; for `sₜ = 0`, `aₜ₊₁ = εₜ` is an i.i.d. sequence. Footnote 31 also omits the
   standard side conditions (`E[s^ζ log⁺ s] < ∞`, `log s` non-arithmetic, `E|ε|^ζ < ∞`; the
   printed `E[ζ] < ∞` has lost its symbol). The tail asymptotics are not formalised (they need
   the implicit renewal theorem; decision 5). Beyond the text, the corrected convergence statement
   is proved: the law of `aₜ` converges weakly to the law of the stationary `A` from any `a₀`
   (`kp_iter_tendsto_law`), while the backward iterates converge almost surely
   (`kp_back_tendsto_ae`); see departures 13 for what else is proved.

## Departures and added hypotheses

1. **p. 640, "`φ > 1` to ensure an interior solution".** The optimum is characterised for
   `0 < σ < φ` (`dt_optimal`, `dt_maximiser_ratio`); with the book's `σ ∈ (0, 1)`, `φ > 1` is
   sufficient but not necessary. The objective is maximised in the monotone form
   `(A_s s)^σ + (A_u u)^σ` (`σ > 0`); the book's case `σ ∈ (0, 1)` is covered.
2. **p. 638, "`k/F(k, h)` is increasing".** Proved for Solow1956's neoclassical technology
   (strictly concave, `f(0) = 0`, Inada) via `Technology.average_strictAnti`.
3. **p. 645, "so long as `cᵢ ≥ 0`".** Chapter 11's problem (11.12), reused, requires `c > 0`;
   the indeterminacy theorem `dy_indeterminacy` takes `cᵢ > 0`. Utility is concave with a
   derivative (tangent inequalities), which is what the sufficiency argument needs.
4. **p. 647, progressive taxes and equal wealth.** Proved for savers (`a ≥ 0`, "the amount
   saved"): `τ′ > 0` nondecreasing makes `τ(a) + aτ′(a)` strictly increasing on `a ≥ 0`
   (`pt_g_strictMonoOn`), so at most one `a ≥ 0` satisfies the steady-state condition
   (`pt_unique`, `pt_equal_wealth`). For `a < 0` the term `aτ′(a)` need not be monotone. The book's
   "strictly increasing `τ′`" is stronger than needed. The necessity of the steady-state condition is
   proved from the absence of a profitable one-period deviation (`pt_steady_euler`), which every
   optimal plan satisfies.
5. **p. 647, discount-factor heterogeneity.** The book's limit statements are proved for the
   consumer's optimal plan at a constant `R` (the steady-state `R = 1/β_max`): consumption of a
   consumer with `βR < 1` falls strictly to zero (`hd_tendsto_zero`) and wealth tends to
   `−εw/(r − δ)` when `r − δ > 0` (`hd_assets_limit`); a consumer with `βR > 1` has strictly rising
   consumption (`hd_strictMono`). These need `u′ > 0` strictly decreasing. The convergence of the
   general-equilibrium `R` to `1/β_max` is not proved.
6. **p. 648, two agents with alternating endowments.** Equilibrium is characterised by the agents'
   Euler (Kuhn–Tucker) conditions and market clearing. Without the limit, the Euler equations and
   constant total endowment force `qₜ = β` and constant consumption (`ta_q_eq_beta`); the footnote
   26 equilibrium is verified to be optimal by Chapter 11's sufficiency theorem
   (`ta_footnote_26`). With the binding limit, the book's equation is the lender's Euler equation;
   `ta_binding_kkt` shows that it implies the borrower's Euler inequality strictly when the
   borrower is poorer (so the limit binds), and uniqueness (`ta_binding_unique`) needs `a < 0` and
   positive consumptions. Existence (`ta_binding_exists`) assumes some `q₁` at which the lender's
   valuation is at least the borrower's (true, e.g., if `u′(c) → ∞` as `c → 0`).
7. **p. 649, return heterogeneity.** Covered by the discount-factor results with `Rᵢ` in place of
   `R` (`rh_lower_return_iff`).
8. **p. 650 (and AKMM §17.4.4), the autarky interest rate with `a = 0`.** Market clearing with
   `a′ ≥ 0` forces autarky (`hu_autarky_clearing`). At autarky every agent's Euler inequality
   `qu′(eᵢ) ≥ βE[u′(e′) | i]` holds iff `q ≥ q* = maxᵢ βE[u′(e′) | i]/u′(eᵢ)` (`hu_kkt_iff`), so
   the first-order conditions alone admit every `q ≥ q*`; the book's closed form `q = q*` is the
   unique price at which some agent (the one valuing the bond most) is unconstrained
   (`hu_price_iff`). Income follows a finite Markov chain; equilibrium is characterised by the
   Kuhn–Tucker conditions at autarky (their sufficiency for the stochastic problem is not
   re-proved).
9. **Footnote 31, the moment condition `E s^ζ = 1`.** Proved for a finitely supported
   multiplier `s > 0`: with `E log s < 0` and `P(s > 1) > 0` a root `ζ > 0` exists
   (`ke_moment_exists`), and it is unique as soon as `s` is not identically `1`
   (`ke_moment_unique`, strict convexity of `ζ ↦ E s^ζ`).
10. **p. 650, determinacy.** Stated for Miao's income fluctuation problem with i.i.d. income and
    `βR < 1` (Proposition 8.3.1 of Miao, reused): the cash-on-hand process has a unique stationary
    distribution (`ui_determinate`). Determinacy for Markov income or in general equilibrium is not
    proved.
11. **p. 630, the Gini coefficient.** Miao's discrete Gini (`ay_gini`, piecewise-linear Lorenz
    curve of `n` equally weighted agents) is used. The book's "tends to 1" when one agent holds
    everything is exact (`gi_gini_concentrated_tendsto`: `G = 1 − 1/n`); the converse of "perfect
    equality gives 0" is added (`gi_gini_eq_zero_iff`).
12. **p. 657, education.** The fraction educated is stated for any wealth distribution (a
    measure on `ℝ`); ties (`w_s − F = w_u`) are resolved against education.

13. **p. 651, Kesten's process, beyond the text (decision 5).** Proved on the canonical i.i.d.
    space `infinitePi ν` (`ν` the law of `(s, ε)`), under `E|s|^κ < 1` and `E|ε|^κ < ∞` for some
    `κ > 0` in place of Kesten's `E log s < 0` (for finitely supported `s` with `E log s < 0` such a
    `κ` exists, `kp_moment_root`): a.s. and `L^κ` convergence of the perpetuity, the fixed-point
    law, weak convergence of the law of `aₜ` (stated as `E f(aₜ) → E f(A)` for bounded continuous
    `f`). The tail index is proved in the moment sense: `E|A|^κ < ∞` for `κ < ζ`, `E A^κ = ∞` for
    `κ > ζ` (with `s, ε ≥ 0`, `ε` not a.s. `0`), hence `sup {κ : E A^κ < ∞} = ζ` (`kp_tail_index`);
    `E A^ζ` itself is not decided. The finitely supported instance (`kp_finite_tail_index_ke`)
    takes `(s, ε)` finitely supported with `ε ≥ 0`; the asymptotics `P(A > a) ~ C a^{−ζ}` are not
    formalised.

## Checked and not errors

* p. 637: the CES capital share `1/(1 + ((1 − α)/α)^{1/ρ} x^{(ρ−1)/ρ})` is correct
  (`fs_ces_capital_share`).
* p. 639: the Katz–Murphy coefficients `−1/ρ` and `(ρ − 1)/ρ` are correct (`km_log_premium`).
* p. 640: `ρ − 1 = σ/(1 − σ) > φ > 1` and "at least above 2" are correct (`dt_exponent_pos_iff`,
  `dt_rho_gt_two`).
* p. 641: the nested-CES claim is correct: the premium rises with `k` iff the elasticity in `F`
  exceeds that in `G` (`cs_ces_nest_strictMono`).
* p. 650: "We saw the model applied to a special case in Chapter 17" is correct: AKMM §17.4.4
  (pp. 528–529) treats Huggett's model with `a′ ≥ 0` (the survey suspected a slip).
* p. 650: "she demonstrated how business cycles affect the welfare costs of business cycles" is
  garbled prose (Imrohoroğlu studied the welfare cost of business cycles with uninsurable
  idiosyncratic risk); no mathematical content.
