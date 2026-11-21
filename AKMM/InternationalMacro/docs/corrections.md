# Corrections and departures: AKMM Chapter 23

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 23, International Macroeconomics (Corsetti, Dedola and Lloyd),
pp. 693–728. Lean names are relative to `AKMM.InternationalMacro`. Every book item is located in
the [source map](source-map.md).

## Corrections

1. **p. 706, fn 15, substitutes and complements.** The book: home and foreign goods are
   substitutes (complements) when `φ > 1` (`φ < 1`), "by calculating the second-order
   cross-partial derivatives of (23.2), `∂²C/∂c_H∂c_F`". The cross partial is
   `a^{1/φ}(1−a)^{1/φ} c_H^{−1/φ} c_F^{−1/φ} S^{1/(φ−1)−1}/φ > 0` for **every** `φ > 0`
   (`subst_hasDerivAt_x`, `subst_hasDerivAt_xy`, `subst_cross_partial_pos`), so its sign does not
   distinguish the two cases. What is true is the demand-side statement: at given expenditure the
   demand (23.3) for the home good rises with the foreign price iff `φ > 1` (gross substitutes,
   `subst_gross_substitutes`) and falls iff `φ < 1` (gross complements,
   `subst_gross_complements`).

2. **p. 709, "the gross real return `R_t ≥ 1`".** Only `R_t > 0` follows from the Euler
   equations (`rs_return_pos`). Counterexample: deterministic tree, log utility, `β = 1/2`,
   `P ≡ 1`, `C_t = 4^{−t}`; (23.9) holds with `q = 2`, so `1/R = 2`, `R = 1/2`
   (`rs_return_lt_one`).

3. **p. 711, (23.14), the sign of the trade balance.** "Define the trade balance as the value of
   exports minus value of imports. In units of home consumption this is
   `tb ≡ (p_F/P)c_F − (p_H/P)c*_H`." That expression is imports minus exports. Net exports are
   `(p_H/P)c*_H − (p_F/P)c_F = p_H Y_H/P − C` (`nx_identity`, `eq_23_14_sign`). Balanced trade
   (23.15) is unaffected (`eq_23_15`).

4. **p. 713, (23.19), the covariance form of UIP.** The book prints
   `R⁻¹Eₜ[π] + covₜ(m, π) = R*⁻¹Eₜ[π*] + covₜ(m*, π*)` with `m = u′(C_{t+1})/u′(C_t)`,
   `π = P_t/P_{t+1}`, `R⁻¹ = βEₜ[m]`. Since `βEₜ[mπ] = R⁻¹Eₜ[π] + β covₜ(m, π)`, the covariances
   must carry the factor `β`; the corrected statement is equivalent to (23.18) (`eq_23_19`).
   Counterexample to the printed form: two equally likely states, log utility, `β = 1/2`, home
   `C ≡ P ≡ 1`, foreign `C*₁ ∈ {2, 2/3}`, `P*₁ ∈ {2/5, 2}`; both Euler equations (23.17) hold with
   `Q = 1/2` but the printed sides are `1/2` and `1/4` (`eq_23_19_printed_counterexample`).

5. **p. 714, `Eₜ[Ŵ_{t+1} − Ŵ_t] = Eₜ[ε̂_{t+1}]`.** With `ε = χ_{t+1}/χ_t − χ*_{t+1}/χ*_t` (23.20)
   and `W = χ*/χ` (23.16), the first-order wedge is `ε̂ = a − b` while
   `Ŵ_{t+1} − Ŵ_t = b − a = −ε̂` (writing `χ_{t+1}/χ_t = e^a`, `χ*_{t+1}/χ*_t = e^b`). The sign
   is reversed; the conclusion `Eₜ[Ŵ_{t+1} − Ŵ_t] = 0` holds (`bond_wealth_loglin`).

6. **p. 717, Figure 23.6, the slope of relative demand.** The text says RD (`φ > 1 − 1/(2a_H)`)
   is "upward sloping in this space" and RD′ (strong complementarity) "slopes downward" in the
   space `{Y_H/Y_F, 1/T}`; the next paragraph ("The upward schedule in the figure (RD′)") and the
   algebra have the opposite. With `Ŷ_H − Ŷ*_F = kT̂`, `k = 1 − 2a(1 − φ)`, the schedule slopes
   downward iff `k > 0`, i.e. iff `φ > 1 − 1/(2a)` (`tot_rd_slope`, `tot_rd_coefficient`).

7. **p. 717, fn 30.** "`Q_t = (Ŷ_{H,t} − Ŷ*_{F,t})/(2φ − 1)`" should read `Q̂_t`; the limit
   `a_H → 1` also needs `φ ≠ 1/2` (`fn_30`).

8. **p. 718, (23.28) and (23.29), the relative supply term.** Both print `(Ŷ_{H,t} − Ŷ*_{H,t})`;
   the relative supply of the endowment economy is `Ŷ_{H,t} − Ŷ*_{F,t}` (p. 716), and the
   equations are proved with it (`eq_23_28`, `eq_23_29`).

9. **p. 721, (23.36), labour demand.** The printed `w_t = (p_{H,t}/P_t) Z_t L_t^{α−1}` is the
   average product; profit maximisation gives `W = α p_H Z L^{α−1}` (`prod_labour_demand`), and
   then profits are `(1 − α)p_H Y`, zero (as stated) only for `α = 1` (`prod_profit`). At the
   printed wage the derivative of profits is `(α − 1)p_H Z L^{α−1} ≠ 0` for `α < 1`
   (`eq_23_36_printed_counterexample`). The constant `α` drops out of the log-linearisation, so
   (23.37)–(23.38) are unaffected (`eq_23_36_log`, `eq_23_37`).

10. **p. 718, (23.27), the scaling of the bond position.** With `b̃_t = b_t − b̄` as defined
    (real bonds), the exact first-order bond term of the wealth gap is
    `2σ(b̃_{t−1} − βb̃_t)/Ȳ` (`eq_23_27`, with `bb = b/Ȳ`). The printed
    `2σβ⁻¹[b̃_{t−1} − βb̃_t]` is correct when `b̃` is the position at steady-state value relative
    to output, `b̃ = β(b − b̄)/Ȳ`, the convention that also makes (23.30)'s accumulation
    `B̂_t − β⁻¹B̂_{t−1}` equal to net exports (`loglin_bond_printed`).

11. **p. 708, the Arrow–Debreu securities.** The text says the security pays "one unit of the
    home consumption basket", but the budget constraint adds `B_{H,t−1}` to nominal income and the
    Euler equation (23.9) carries `1/P_{t+1}`, which is the first-order condition for a claim to
    one unit of **currency**; this is also what the riskless-return argument (buy `P_{t+1}` units
    to guarantee one unit of the basket) uses. We formalise currency claims, matching (23.9)
    (`eq_23_10`–`eq_23_13`).

12. **Notation (pp. 707–713).** `a*_H` and `a_F` are used interchangeably under symmetry, and
    `Q_t` denotes both the real exchange rate and the bond price. In Lean the bond price is `Qb`.

## Departures and added hypotheses

1. **`φ ≠ 1` and `0 < a_H < 1` in the nonlinear model.** The CES aggregator and price index are
   imported from Obstfeld–Rogoff and are stated for `φ ≠ 1` (Cobb–Douglas is the limit) and
   interior weights. All linear results (23.24)–(23.31), (23.37)–(23.38) hold for every `φ > 0`,
   in particular at the Cole–Obstfeld point `σ = φ = 1` (`tot_cole_obstfeld`).

2. **Log-linearisation as exact derivatives.** Each log-linear equation is the derivative at
   `t = 0` of the corresponding nonlinear object along the ray `p_H = e^{t·ph}`, `p_F = e^{t·pf}`,
   `C = Ȳe^{tĉ}`, … around the symmetric steady state (`LogLinear`). The bond-economy wealth gap
   (23.27) is stated for `σ(log C − log C*) − log Q`, which equals `log W` (23.22) wherever
   consumption is positive (`eq_23_22`).

3. **The linearised UIP and the unit root.** `Eₜ[ε̂] = 0` is proved as the derivative of the UIP
   condition along a path of equilibria (`bond_wealth_loglin`); the martingale and unit-root
   statements are proved for an adapted, integrable process satisfying `Eₜ[Ŵ_{t+1}] = Ŵ_t`
   (`unitroot_martingale`, `unitroot_forecast`, `unitroot_innovation`).

4. **(23.29) with a zero denominator.** When `1 − 2a(1 − φ) = 0` the autarky equilibrium has no
   solution unless `Ŷ_H = Ŷ*_F` (`tot_fa_degenerate`); (23.29) is stated for a nonzero denominator.

5. **p. 718, the sign of the (23.28) denominator.** The book says it is positive "when
   `a_H ∈ (0.5, 1)`"; it is positive for every `a_H ∈ (0, 1)` (`tot_cm_denom_pos`). The
   coefficient is largest "as `φ` approaches zero" in the sense of a supremum `σ/(2a − 1)²` that
   is not attained (`tot_cm_coef_strictAntiOn`, `tot_cm_tendsto_zero`, `tot_cm_coef_lt`).

6. **The symmetric steady state is not the only stationary equilibrium.** The book linearises
   around the symmetric steady state `Q = T = 1` without discussing uniqueness. It exists for
   all parameters (`ss_exists`, `ss_cm_exists`) and is the unique autarky equilibrium for
   `φ ≥ 1/2` (`ss_unique`), but with strong complementarity (`a = 9/10`, `φ = 1/4`) the autarky
   economy with symmetric endowments has the further equilibrium `T = ((9 + √77)/2)⁴`
   (`ss_multiple`).

7. **The Marshall–Lerner interpretation (p. 720).** The classic condition is proved for the
   Armington import demands at given consumption with Obstfeld–Rogoff's `marshall_lerner`
   (`nx_marshall_lerner`): `ζ + ζ* = 2aφ > 1`. The general-equilibrium condition (23.31) tends
   to `φ > 1/(2a)` as `σ → ∞` (`nx_ml_limit`) and is `φ > 1` at `σ = 1` (`nx_log_utility`).
