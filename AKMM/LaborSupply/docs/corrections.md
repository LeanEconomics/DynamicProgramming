# Corrections and departures: AKMM Chapter 12

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 12, Labor supply (R. Rogerson and G. L. Violante), pp. 325–367, and
Appendix 12.A, p. 849. Lean names are relative to `AKMM.LaborSupply`. Every book item is located
in the [source map](source-map.md).

## Corrections

1. **p. 333, footnote 2, the income derivative.** "`ℓ₂(w, I) = −σ(1 − s_I)/[1/γ + σ(1 − s_I)]`".
   Differentiating (12.1) gives `ℓ₂ = −σ(1 − s_I)/(w[1/γ + σ(1 − s_I)])` (`st_footnote_2`); the
   printed value is `w·ℓ₂` and is right only at `w = 1`. Counterexample: `ψ = γ = σ = 1`, `w = 2`,
   `I = 1`, with the explicit solution `ℓ = (√(I² + 4w²) − I)/(2w)`
   (`st_footnote_2_printed_false`). The footnote's conclusion (negative at `s_I = 0`) holds.

2. **p. 335, budget-neutral taxes.** "In this case [`T = τwℓ`] there is no income effect associated
   with the change in `τ` and the appropriate elasticity for assessing the impact on hours is the
   Hicksian elasticity." Exactly: with the rebate, the response of hours to the net wage is
   `1/(1/γ + σwℓ/c)`, `c = wℓ + y` (`st_balanced_budget`). This is the Hicksian formula (12.4)
   with `s_I` measured as `y/c` (non-labour income other than the transfer); with `s_I` measured
   from the individual's whole non-labour income `y + T`, as in (12.4), the two agree iff `τ = 0`
   (`st_balanced_budget_hicks_iff`). The claim holds for small reforms around `τ = 0`.

3. **p. 336, (12.6), the constant.** Printed:
   `ℓ_h/ℓ_m = [(1 − θ)/θ]^{1/(η−1)}(w/A)^{η/(η−1)}`. From
   `((1 − θ)/θ)(Aℓ_h/(wℓ_m))^{η−1} = w/A` the constant is `[(1 − θ)/θ]^{1/(1−η)}` (`eq_12_6`); the
   printed and correct values coincide iff `θ = 1/2` (`eq_12_6_printed_false`). The sign of the
   exponent on `w/A`, and so the text's conclusion, is unaffected (`hp_ratio_decreasing`).

4. **p. 339, the elasticity of utility with respect to work.** "the elasticity … is now given by
   `−ℓṽ′(ℓ̄ − ℓ)/v(ℓ̄ − ℓ)`. This value approaches minus infinity as `ℓ` approaches `ℓ̄`." (The
   denominator should be `ṽ`.) The elasticity is `−(1 − 1/γ)ℓ/(ℓ̄ − ℓ)` (`lt_elasticity`); it tends
   to `−∞` only when `γ > 1`; when `γ < 1` (`ṽ < 0`) it tends to `+∞` (`lt_elasticity_limits`).
   What holds for every `γ ≠ 1` is that it is unbounded, unlike the constant `1 + 1/γ` of the
   benchmark (`lt_benchmark_elasticity`).

5. **p. 341, footnote 8.** Printed: `log ℓ_t = (γ/ψ) + γ log w_t + γ(1 − σ) log c_t`. From
   `c_t^{−σ} = λ` and `ψℓ_t^{1/γ} = λw_t`: `log ℓ_t = −γ log ψ + γ log w_t − γσ log c_t`
   (`footnote_8`); both the constant and the consumption coefficient are wrong (the chapter's own
   (12.43), `σ = 1`, has coefficient `−γ` on `log c`). Counterexample at `ψ = γ = σ = w = 1`,
   `c = e`: the printed right side is `1`, while `log ℓ = −1` (`footnote_8_printed_false`).

6. **p. 344, the sign of the compensation.** "as long as `dI_it/dw_it = (1 − τ)ℓ_it`". The
   compensation removes the wage gain, `dI/dw = −(1 − τ)ℓ`; with that sign the response is the
   Hicksian (12.17) (`eq_12_17`; the change in utility is `c^{−σ}(w′ℓ + I′)`,
   `st_compensated_utility`). With the printed `+(1 − τ)ℓ` the response is
   `(1 − 2σ(1 − s_I))/(1/γ + σ(1 − s_I))`, different whenever `σ(1 − s_I) ≠ 0`
   (`dyn_compensation_sign`). The printed (12.16)–(12.17) are consistent with the minus sign.

7. **p. 345, the ordering of the elasticities.** "`ε^F ≥ ε^H ≥ ε^M` with equality holding when
   `σ → ∞`. In this case, utility becomes quasi-linear". The ordering holds (`dyn_ordering`), with
   equality iff `σ = 0` (utility linear in consumption), and the elasticities converge to `γ` as
   `σ → 0` (`dyn_ordering_sigma_zero`), as the text says correctly on p. 344. As `σ → ∞`,
   `ε^H → 0` and `ε^M → −1` while `ε^F = γ`; `ε^H < γ` for every `σ > 0`
   (`dyn_ordering_sigma_infty`).

8. **p. 353, (12.37) as printed.** `U = [(C^{1−σ} − 1)/(1 − σ)]v(1 − L)` (σ ≠ 1) is not of the
   KPR class: it equals `C^{1−σ}v/(1 − σ) − v/(1 − σ)`, whose second term is a non-constant
   `v²`, exactly what Appendix 12.A rules out. Its MRS is not homogeneous of degree one in `C`
   (at `C = 1` it is `0`, at `C = 2` it is not), so hours cannot stay constant with growing
   wages (`eq_12_37_printed_not_bgp`). The corrected form is `C^{1−σ}v(1 − L)/(1 − σ)` (or
   `(C^{1−σ}v(1 − L) − 1)/(1 − σ)`), formalised as `kprU`; for it the "if" direction holds
   (`eq_12_37_if`).

9. **p. 354, the U.S./Italy ratio.** "If we set `γ = 1` … we obtain a ratio of hours worked
   between the U.S. and Italy predicted by the theory of 1.42". By (12.39) the ratio is
   `[(0.60/0.81)/(0.36/0.69)]^{γ/(1+γ)}`, and with `γ = 1` the exponent is `1/2`: the ratio is in
   `(1.19, 1.20)`. The base `(0.60/0.81)/(0.36/0.69) ∈ (1.41, 1.43)` is the limit as `γ → ∞`
   (`eq_12_39_us_italy`).

10. **pp. 360–361, `ψ̃`.** With `U = u(c) − ψv(ℓ)` the lottery objective is
    `u(c) − ψ(v(ℓ̄) − v(0))e − ψv(0)`, so `ψ̃ = ψ(v(ℓ̄) − v(0))`; the book's `ψ̃ = v(ℓ̄) − v(0)`
    drops `ψ` (`il_lottery`).

11. **p. 849, Appendix 12.A.** (12.A.1) omits the factor `α` of the marginal product of capital,
    `β[α(H/κ)^{1−α} + 1 − δ]` (`bg_homog`, `eq_12_37_if`). (12.A.2) has the wrong sign:
    `U_CC C/U_C = −σ` (`eq_12_A_2`), since `U_CC < 0`. (12.A.3) omits `(1 − α)` from the marginal
    product of labour and a sign (it is `−U_H = U_C·MPL`); the growth-rate argument is unaffected
    (`eq_12_A_3`). The log case is "similar" only in that the intratemporal condition forces `v¹`
    (not `v²`) to be constant (`eq_12_A_3_log`). The step from (12.A.1) to a constant `σ` also
    requires that `σ` not depend on hours, which the argument of (12.A.3) delivers
    (`eq_12_A_3`: `σ′ = 0`).

## Minor slips

1. **p. 348, (12.29)** omits the constant `−γκ` coming from `const_i` in (12.27)
   (`eq_12_29`); the first-order term `−φ/λ` replaces `log(1 − φ/λ)` with error at most
   `(φ/λ)²/(1 − φ/λ)` (`fe_log_approx`).
2. **pp. 350–351, (12.32) and the decomposition.** (12.32) maximises over "`c, h`" (for `c, ℓ`).
   In the decomposition, `U(c*_ε, ℓ*)` must mean consumption `w(1 + ε)ℓ*` (the new wage at the
   old hours), not the new optimum `c*_ε = w(1 + ε)ℓ*_ε`; with that reading both brackets are as
   printed (`eq_12_34`).

3. **p. 338** "an exogenous reduction in `ℓ_m` will imply an increase in `ℓ_w`": `ℓ_w` should
   be `ℓ_f` (`hh_added_worker`).

4. **pp. 359, 367** "the same functional forms as in Section 12.2" and "the benchmark model from
   Section 12.2" refer to Section 12.3; p. 367 "greater than `z`" should be `z*`
   (`il_rw_life_cycle`); p. 362 `∫₀^T e(t)dt = e*` should be `e*T` (`il_ljungqvist_sargent`:
   `Σ_t e_t = Ne*`).

## Departures

1. **Differentiability of optimal hours (pp. 333, 343).** The book differentiates the optimal
   `ℓ(w, I)` "using the implicit function theorem". Here every elasticity is stated along a
   path `s ↦ (w(s), I(s))` for an optimal-hours path `ℓ(s)` that is assumed differentiable at
   `0` and to satisfy (12.1) near `0` (`st_path_identity`). The hypotheses are satisfiable: for
   `ψ = γ = σ = 1` the solution is explicit and differentiable along every differentiable path
   (`st_explicit_foc`, `st_explicit_path`).

2. **Deterministic life cycle (§12.4.1).** (12.7) has stochastic wages; two-stage budgeting
   (`dyn_two_stage`) is proved for the deterministic finite-horizon problem (the argument is the
   same pathwise). The Frisch formula (12.21) is proved along a path with `λ` held fixed, which
   is how the book differentiates (12.18)–(12.19).

3. **The log-normal step (12.28)** is proved for a Gaussian law of `log λ′`
   (`eq_12_28`); the conditional expectations in (12.27)–(12.31) are represented by their
   values, and the identities are then exact algebra.

4. **"Only if" of (12.37) (Appendix 12.A).** Proved under this class: (a) for each leisure level,
   `U(·, ℓ)` is twice differentiable in `C` with `U_C > 0`, and the Euler ratio
   `U_C(gC, ℓ)/U_C(C, ℓ)` does not depend on `C`, for every growth factor `g > 0` (balanced paths
   from every initial level and for every growth rate), which gives the candidate forms
   `a(ℓ)C^{1−σ(ℓ)}/(1 − σ(ℓ)) + b(ℓ)` and `a(ℓ) log C + b(ℓ)` (`eq_12_A_2`); (b) `a, σ, b` are
   differentiable in `ℓ`, `a > 0`, and either `σ(ℓ) ≠ 1` on the whole interval of leisure levels
   or `σ ≡ 1`; (c) the MRS is homogeneous of degree one in `C` (constant hours with wages growing
   like consumption). Under (a)–(c), `σ` and `b` are constant (`eq_12_A_3`,
   `eq_12_37_only_if`), resp. `a` is constant (`eq_12_A_3_log`). Classes in which `σ(ℓ)` crosses
   `1`, or `U` is not differentiable in `ℓ`, are not covered.

5. **Imai–Keane (12.41)** is derived for perfect foresight, from the first-order conditions of
   the lifetime problem with one multiplier on the present-value budget (`eq_12_41`); the book's
   `E_t[ℓ_{i,t+j}]` becomes `ℓ_{t+j}`.

6. **Continuous time in §12.8.2 and §12.8.4.** The Ljungqvist–Sargent and Rogerson–Wallenius
   problems are formalised with `N` equal periods, no discounting and `r = 0`: sufficiency of
   pointwise maximisation with a common multiplier (`il_lagrange_suff`), timing indifference
   (`il_ljungqvist_sargent`, which therefore needs `Ne*` to be an integer — the integer constraint
   the book's continuous time avoids), and the pointwise threshold (`il_rw_threshold`,
   `il_rw_life_cycle`). The heterogeneous-`ψ` result is proved for a density `f` and a local
   inverse `Q = F⁻¹` (`il_vtilde_deriv`).
