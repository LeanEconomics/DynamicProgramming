# Corrections and departures: AKMM Chapter 18

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 18, Nominal frictions and business cycles (Alisdair McKay and Morten
Ravn), pp. 533–560, and Appendix 18.A, pp. 871–876. Lean names are relative to
`AKMM.NominalFrictions`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 534, the expected time between price changes.** Printed:
   `∑_{t=1}^∞ (1 − θ)θᵗ t = θ/(1 − θ)` is "the expected time between price adjustments". The sum
   is computed correctly (`dur_printed_sum`), but its weights sum to `θ`, not one
   (`dur_printed_weights_sum`, `dur_printed_weights_ne_one`), so it is not an expectation. With
   reset probability `1 − θ` a price lasts `t ≥ 1` periods with probability `(1 − θ)θ^{t−1}`
   (`dur_pmf_sum`) and the mean duration is `1/(1 − θ)` (`dur_mean`, from Galí's
   `mean_duration`). The printed `θ/(1 − θ)` is the expected number of periods *without* a
   change, one less than the duration (`dur_printed_eq_mean_sub_one`); it is never the mean
   (`dur_printed_ne_mean`).

2. **p. 539 and App. 18.A.1, p. 871, the reset-price first-order condition and (18.7), p. 540.**
   The envelope condition (printed correctly in 18.A.1) carries the factor `1/(1 + π′)` at each
   step: `p_{t,τ}` depends on `p^R_t` through `p_{t,τ} = p^R_t P_t/P_τ`. Iterating it
   (`rp_iterate`, `rp_series`) gives
   `V_p = ∑_τ (βθ)^{τ−t} u′(C_τ) Y_τ (P_t/P_τ)[p_{t,τ}^{−ε} − εp_{t,τ}^{−ε−1}(p_{t,τ} − w_τ/A_τ)]`;
   the book's combined condition omits the factor `P_t/P_τ`. Consequently the rearranged
   condition is `p^R ∑(βθ)^k u′Y (P_τ/P_t)^{ε−1} = µ ∑(βθ)^k u′Y (P_τ/P_t)^ε w/A`
   (`rp_term_eq`, `rp_foc_rearranged`), not exponents `ε` and `1 + ε`, and the recursions of (18.7)
   are `p^N_t = µ (w_t/A_t) u′(C_t)Y_t + θβ(1 + π_{t+1})^ε p^N_{t+1}` and
   `p^D_t = u′(C_t)Y_t + θβ(1 + π_{t+1})^{ε−1} p^D_{t+1}` (`eq_18_7`, `rp_pN_rec`, `rp_pD_rec`),
   not `(1 + π)^{1+ε}` and `(1 + π)^ε`. On a constant-inflation path the correct reset price is
   `µm(1 − βθΠ^{ε−1})/(1 − βθΠ^ε)` (`rp_constant_correct`) and the printed one
   `µm(1 − βθΠ^ε)/(1 − βθΠ^{1+ε})` (`rp_constant_printed`); they coincide iff `Π = 1`
   (`rp_printed_ne_iff`). The log-linearisation (18.A.1) and everything downstream are
   unaffected, because the missing factor appears on both sides and is one at zero inflation. The
   union's condition in App. 18.A.3 (p. 875) has the right exponents (`sw_union_term_deriv`,
   `sw_union_foc`): there the derivative was multiplied by `W^R`, which absorbs the factor.

3. **p. 543, the natural rate below (18.15).** Printed:
   `r^n_t = −log β + σ(1 + ψ)/(σ + ψ)(Â_t − E_tÂ_{t+1})`. The sign is wrong: expected productivity
   growth raises the natural rate, `r^n_t = −log β + σ(1 + ψ)/(σ + ψ)(E_tÂ_{t+1} − Â_t)`. Exact under
   perfect foresight (`eq_18_15_exact`); for any expectation system from the log-linear Euler
   equation (`eq_18_15`). The printed IS equation holds only if productivity is expected constant
   (`rn_printed_iff`).

4. **p. 544, the rule (18.17).** `î_t = φ_π(π_t − π*) + φ_x x_t + ω_t` has no intercept, while
   `î_t = log(1 + i_t)` in (18.15) and `r^n` contains `−log β`. A zero-inflation, zero-gap steady
   state then needs `î = −log β` from (18.15) but `î = 0` from (18.17); both hold only if `β = 1`
   (`rule_18_17_no_steady_state`). The rule needs the intercept `−log β` (the book's `ī` for
   `π* = 0`), as in the rule on p. 543 and in the forms used for determinacy
   (`det_system`, `eq_18_18`); determinacy is unaffected.

5. **p. 873, the Jury condition `|a₀| < 1`.** The book says it "holds as we assume `β ∈ [0, 1]`,
   all the parameters are weakly positive and `σ` is strictly positive". At `β = 1`,
   `φ_x = φ_π = 0`, `a₀ = 1` (`det_a0_not_automatic`). It does follow from (18.18), so the
   equivalence of the Jury conditions with (18.18) is correct for `0 ≤ β ≤ 1`, `κ, φ_π, φ_x ≥ 0`
   (`det_jury_iff`, `det_roots_iff`). The equilibrium uniqueness statement is imported from Galí
   for `κ > 0`, `0 < β < 1` (`eq_18_18`).

6. **p. 553, footnote 16, a sign.** `E[z_{t−1}{η_t − β(π_{t+1} − E_tπ_{t+1})}]` is expanded as
   `E[z_{t−1}η_t] + βE[z_{t−1}(π_{t+1} − E_tπ_{t+1})]`; the sign is `−` (`gg_expand`). Harmless:
   both terms vanish (`gg_orthogonal`, `gg_cov_zero`). The orthogonality also needs the instrument
   to be (e.g.) bounded so that the products are integrable; we assume `|z| ≤ C`.

7. **p. 557, sticky wages only.** "Since goods are sold at marginal cost, we have `P_t = W_t` …
   real wages, which are now constant as `w_t = W_t/P_t = 1`." With `y = Aℓ`, marginal cost is
   `W_L/A` for the wage `W_L` of the labour bundle, so `P = W_L/A` and the real wage is `W_L/P = A`
   (`sw_flexprice_real_wage`), not constant when productivity varies (`sw_real_wage_not_constant`).
   `W/P = 1` holds for the book's `W` defined as the labour cost of one unit of goods, but that
   `W` is not the wage index of App. 18.A.3, (18.A.9), used in (18.23)–(18.25).

8. **p. 559, footnote 24, Tobin's Q.** "`ξ(δ) = δ` so that Tobin's Q equals 1 in the deterministic
   steady state". With `K′ = (1 − δ)K + ξ(I/K)K`, `Q = 1/ξ′(I/K)` (`ext_adj_foc`, `ext_tobin_q`);
   `ξ(δ) = δ` makes `I/K = δ` a steady state (`ext_adj_steady`), but `Q = 1` there iff `ξ′(δ) = 1`
   (`ext_q_one_iff`). Counterexample: `ξ(x) = √(δx)` is increasing and concave with `ξ(δ) = δ`, and
   `Q = 2` (`ext_q_counterexample`). Both conditions are needed.

9. **p. 560, labour requirement with capital.** "the elasticity of output with respect to labor is
   `1 − α`, which means we need to use `1/(1 − α) > 1` units of labor in order to produce one more
   unit of output". The elasticity is right (`ext_labour_elasticity`) and gives a percentage
   statement: one per cent more output needs `1/(1 − α)` per cent more labour
   (`ext_labour_requirement_pct`). In units the requirement is `1/MPL = ℓ/((1 − α)y)`
   (`ext_labour_requirement_units`), which equals `1/(1 − α)` iff `y = ℓ`
   (`ext_units_printed_false`).

## Typographical slips (no theorem needed)

10. **p. 872, (18.A.5)–(18.A.6).** `ŵ_t = (σ + ψ)Ŷ_t − ψA_t` and `Y^n_t = (1 + ψ)/(ψ + σ)Â_t` lack
    hats on `A_t` and `Y^n_t`; the hatted forms are proved (`eq_18_A_5_exact`, `nat_gap_loglinear`).
11. **p. 874.** "The term `D^W_t ≥` reflects wage dispersion" omits the bound `1`
    (`sw_wage_dispersion_ge_one`).

## Departures

* **Perfect foresight versus uncertainty.** The reset-price derivation (correction 2), the
  present-value step (18.A.1) ⇒ (18.A.2) (`eq_18_A_2`) and the exact IS curve are along
  perfect-foresight paths; the recursions (18.A.2)–(18.A.4), (18.15), (18.16), (18.23)–(18.24)
  and determinacy hold for Galí's general expectation systems (linear, monotone, tower property),
  which include conditional expectations on finite trees.
* **Log-linearisation.** As in the book, log-linear equations are stated as exact relations among
  log deviations. Where the book's relation is exact in logs we prove it exactly ((18.13),
  (18.14), footnote 9, (18.15) under perfect foresight, (18.A.5)–(18.A.6) with the dispersion term
  `ψ log D`, (18.25)); (18.A.3) and the dispersion recursion are proved as derivatives at the
  zero-inflation steady state (`eq_18_A_3`, `eq_18_A_dispersion`).
* **Calvo aggregation.** The set of non-adjusters has measure `θ` and satisfies the law of large
  numbers `∫_S f = θ∫ f`; both are hypotheses (the book's "firms are chosen randomly"), as in
  Miao's `eq_19_13` and `eq_19_17`, which we import.
* **(18.20)** is cited by the book (Woodford 2003b). We import Galí's second-order approximation
  of period utility at `α = 0` around the efficient (subsidised) steady state
  (`eq_18_20_utility`) and show that the weights give `π² + (κ/ε)x²` with the book's `κ`
  (`eq_18_20_weight`, `eq_18_20_period`); the summation over time with the Calvo dispersion
  recursion is Galí's `Welfare.welfare_eq_loss_calvo`, not restated.
* **Commitment versus discretion (§18.4.4)** uses Galí's perfect-foresight commitment path for a
  one-period cost-push shock and the book's loss (18.22) with weight `λ`; the discretionary
  date-0 problem is solved directly (`pol_discretion_date0`).
* **Price-level targeting.** The book makes no determinacy claim; we record Galí's Exercise 4.6
  result for the rule with the natural-rate intercept and `φ_x = 0` (`pol_price_level_rule`).
