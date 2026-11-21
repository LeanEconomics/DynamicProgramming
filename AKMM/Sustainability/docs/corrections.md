# Corrections and departures: AKMM Chapter 25

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 25, Sustainability (J. Hassler, P. Krusell and C. Olovsson), pp. 749–784,
and Appendix 25.A, p. 909. Lean names are relative to `AKMM.Sustainability`. Every book item is
located in the [source map](source-map.md).

## Corrections

1. **p. 755, (25.6) and (25.8), signs of the outflows.** As printed,
   `S_t − S_{t−1} = φ₁₂S_{t−1} + φ₂₁Sᵁ_{t−1} + E_{t−1}` and `Sᴸ_t − Sᴸ_{t−1} = φ₂₃Sᵁ_{t−1} + φ₃₂Sᴸ_{t−1}`,
   while (25.7) adds `φ₁₂S` and `φ₃₂Sᴸ` to the upper reservoir. Total carbon then grows by
   `2φ₁₂S + 2φ₃₂Sᴸ + E` (`eq_25_6_printed_total`); with Folini et al.'s flows and no emissions
   it is not conserved (`eq_25_6_printed_false`). The outflows must enter with a minus sign:
   then total carbon grows by exactly `E` (`carbonStep`, `eq_25_6_total`).

2. **p. 756, the shares in (25.10).** The text says "the share that leaves the atmosphere
   within a period [is] `1 − φ₀`". By (25.10) the within-period loss is
   `d₀ = (1 − φ_L)(1 − φ₀)`; `1 − φ₀` is the share of the non-permanent part that leaves
   (`eq_25_10_within_period`); with the decadal calibration it is `0.4856`, not `0.607`
   (`eq_25_10_within_period_printed_false`).

3. **p. 770, (25.29), the rebate in the Euler equation.** The return on saving made at `t` is
   paid at `t + 1` and rebated at rate `Γ_{t+1}`, so the Euler equation is
   `C_{t+1}/C_t = β(1 + Γ_{t+1})r_{t+1}`, not `β(1 + Γ_t)r_{t+1}`. With the printed `Γ_t` the
   constant saving rate does not solve it whenever the rebate changes
   (`eq_25_29_printed_false`). The corrected Euler equation is equivalent to the corrected
   difference equation (`eq_25_29_saving`).

4. **p. 770, the saving-rate difference equation.** Printed:
   `(1 + s_{t+1})/(1 + s_t) = αβ/(s_t(1 − ν))`; correct: `(1 − s_{t+1})/(1 − s_t) = αβ/(s_t(1 − ν))`
   (`eq_25_29_saving`). Counterexample to the printed form: `α = β = ν = 1/2`, `s_t = 3/4`,
   `s_{t+1} = 5/6` (`eq_25_29_saving_printed_false`). The fixed point `s̄ = αβ/(1 − ν)` is the
   same (`saving_const`).

5. **p. 770, "only one non-explosive solution".** Imprecise. Paths starting below `s̄` leave
   `(0, 1)` (`saving_below`), but paths starting above `s̄` stay in `(s̄, 1)` and converge to `1`
   (`saving_above`, `saving_above_tendsto`): they are bounded, not explosive. What rules them out
   is the transversality condition: `β^t K_{t+1}/C_t = β^t s_t/(1 − s_t) → ∞` when
   `α + ν < 1` (`saving_above_tvc`). So `s̄` is the only solution in `(0, 1)` consistent with
   optimality, and the only rest point there (`saving_fixed_iff`).

6. **p. 780, (25.33)–(25.34), the CES weights.** With
   `y = [(1 − ν)X^θ + ν(A_e e)^θ]^{1/θ}`, `θ = (ε − 1)/ε`, the shares are
   `e^{share} = ν(A_e e/y)^θ` and `l^{share} = (1 − α)(1 − ν)(X/y)^θ` (`ces_share_e`,
   `ces_share_l`), so `A_e = (y/e)(e^{share}/ν)^{ε/(ε−1)}` and
   `A = y/(k^αl^{1−α}) · (l^{share}/((1 − α)(1 − ν)))^{ε/(ε−1)}` (`eq_25_34`, `eq_25_33`). The
   printed formulas drop `ν` and `1 − ν` and return `ν^{ε/(ε−1)}A_e` and `(1 − ν)^{ε/(ε−1)}A`
   (`eq_25_34_printed`, `eq_25_33_printed`); with `ε = 2`, `ν = 1/4` the printed `A_e` is
   `A_e/16` (`eq_25_34_printed_false`). Since the factors are constant, the printed formulas give
   the right growth rates (`eq_25_34_printed_growth`), so Figure 25.11, which plots normalised
   logarithms, is unaffected.

7. **p. 767, the two-firm planning problem.** The printed problem
   `max AE₁^{ν₁} + AE₂^{ν₂} − γ(E₁ + E₂)²` and its condition `ν_iAE_i^{ν_i−1} = 2γ(E₁ + E₂)` omit
   the coal cost `p` of (25.17). With it: `ν_iAE_i^{ν_i−1} = p + 2γ(E₁ + E₂)` (`staticW2`,
   `static_two_exists`, `static_two_optimal`, `static_two_unique`, `static_two_pigou`,
   `static_two_cap`).

8. **p. 909, Appendix 25.A.** The relation `λ_o/λ_κ = (e_{o,t}/e_{κ,t})^{1−ρ} p_{1,t}/p_{κ,t}` has
   `p_{1,t}` for `p_{o,t}` (`eq_25_A_ratio`).

9. **p. 779, `e₀ = Ak₀^α`.** "At time 0, this means that `e₀` must be given by `Ak₀^α`" is
   infeasible when `R₀ < Ak₀^α` (`leontief_e0_infeasible`); it needs the book's later assumption
   that `R₀` is high relative to `Ak₀^α`. For `t ≥ 1` the claim holds in the sense that an
   optimal plan has no idle capital and can be taken without waste (`leontief_optimal_no_idle`,
   `leontief_optimal_tight`).

10. **Minor misprints** (no theorem affected). (25.9) writes the summation index as `t` for `s`
    (`eq_25_9`); (25.1) uses `σ` for the text's `σ₁`; (25.14) writes `D(e₁)` for `D(E)`; p. 770
    writes `S_t = Σ_v (1 − d_{t−v}) Σ_i M_t` with `M_t` for `M_v` (`excessCarbon`); (25.26) writes
    `p̂` for the `p` of (25.27); the sign of (25.32) is the opposite of (25.30): the tax is minus
    the marginal externality, `τ_t = −Λ_t` (`ghkt_tax_of_proportional`, `eq_25_32`).

11. **Numerical claims checked by hand (not formalised).** p. 759: 190 trillion m³ of gas at
    0.511 kgC/m³ is 97 GtC, i.e. 0.10–0.22 °C with the CCR range 1.0–2.3 °C per 1,000 GtC, so
    "less than a tenth of a degree" holds only at the bottom of the range. p. 759 and Table 25.1:
    coal reserves of 1,074 are multiplied by a carbon content of 70%, so the 1,074 must be Gt of
    coal (as BP reports), not GtC as the text and Table 25.1 label it. p. 759: "at least 10 °C" if
    all coal resources were burnt holds for the BGR estimate (≈ 11,500 GtC) but not for Rogner's
    (≈ 6,200 GtC gives 6.2 °C at the low CCR). p. 759: oil gives `0.27–0.63 × 0.507` =
    0.14–0.32 °C, printed 0.13–0.33 (rounding).

## Departures

12. **The GHKT optimal tax (25.32) is proved in the GHKT benchmark.** The book's planner
    (pp. 768–770) buys coal and green energy with final goods (25.23); then `C_t/Y_t` need not be
    constant along the optimum, and (25.32) is then not exact. It needs only that consumption is
    proportional to output (`ghkt_tax_of_proportional`). We prove it for a planner whose energy
    choices do not use final goods (`GHKT`): output `e^{z_t − γS_t + g(x_t)}K_t^α`, emissions
    `m(x_t)`, any carbon kernel in `[0, 1]`, deterministic `z`. There the plan with
    `K_{t+1} = αβY_t` and `x_t = e*` maximising `g − γΨm` is optimal among all feasible plans
    with convergent utility (`ghkt_optimal`), and (25.32) holds along it (`eq_25_32`). The
    hypotheses have a proved instance: GHKT's coal sector with coal produced from labour
    (`coalEconomy`, `ghkt_coal_assumptions`, `ghkt_coal_opt`, `ghkt_coal_optimal`). The book's
    "potentially stochastic" `z` and its expectation operator are not formalised. Optimality is
    proved by an exact finite-horizon decomposition, not by first-order conditions and a
    transversality condition (`lg_identity`, `lg_compare`, `ghkt_overtake`).

13. **Optimality of the dynamic plans** (cake eating, the oil owner, Dasgupta–Heal) is proved
    against all feasible plans with convergent utility, and as an overtaking bound at every
    finite horizon (`cake_overtake`, `oil_owner_overtake`); the book's resource constraint
    `Σ c_t = R₀` is relaxed to `Σ_{t<T} c_t ≤ R₀` for all `T`. "Utility is bounded" (p. 776) is
    proved as convergence of the utility series (`cake_utility_hasSum`); period utility is
    unbounded below.

14. **Two-box climate stability (p. 755)** is proved under the sufficient conditions
    `σ₁, σ₂, σ₃, κ > 0`, `σ₃ ≤ 1`, `σ₁(κ + σ₂) ≤ 1` (`climate_twoBox_tendsto`,
    `climate_twoBox_isStable`); the appendix calibration (`σ₁ = 0.22`, `σ₂ = 0.3`, `σ₃ = 0.05`,
    `κ = η/ECS ≈ 1.23`) satisfies them. The comparison of convergence speeds is not formalised.

15. **The technology menu (p. 782)** is proved with the frontier `A_x^ω + A_y^ω = 1` and
    `ω > 0`, which the book leaves unspecified ("a CES minus a positive constant"); the
    reduced-form parameter is `ρ' = ρω/(ω − ρ)` (`menu_reduced_le`, `menu_reduced_attained`,
    `menu_elasticity`).

16. **The Leontief hump (p. 779)** is not formalised for finite `R`: the book argues it "without
    fully solving the model". Proved: no idle capital and no waste on optimal plans, the
    eventual decline of `e` along every feasible plan (`leontief_eventually_declines`) and the
    initial rise when the resource is abundant (`leontief_abundant`). The existence of an
    optimal plan is not proved (the book does not either).

17. **Energy services (25.26)–(25.27)** are proved for any finite set of energy sources, with
    the least-cost (duality) property (`eq_25_26_least_cost`), the many-input analogue of
    Obstfeld–Rogoff's two-good result reused from `RealExchangeRate`.
