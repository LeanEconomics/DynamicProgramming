# Corrections and departures: AKMM Chapter 20

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 20, Frictional labor markets (T. Mukoyama and A. Şahin), pp. 593–625, and
Appendix 20.A, pp. 879–887. Lean names are relative to `AKMM.FrictionalLaborMarkets`. Every book
item is located in the [source map](source-map.md).

## Corrections

1. **p. 608, (20.25), the sign in `B`.** Printed `B = (1 − σ)κθ̄^ηη/((1 − γ)χ) + γκθ̄/(1 − γ)`.
   With Cobb–Douglas matching the bracket of (20.16) is
   `z − b + (1 − σ)κθ^η/((1 − γ)χ) − γκθ/(1 − γ)` (`ll_rhs_eq`), whose derivative in `θ̂` at the
   steady state is `B` with `−γκθ̄/(1 − γ)` (`eq_20_25`). The printed `B` exceeds it by
   `2γκθ̄/(1 − γ) > 0` (`eq_20_25_misprint`). (20.26) as printed is the coefficient obtained with
   the correct sign (`eq_20_26`); the printed `B` would give `−κγθ̄` in (20.26)
   (`eq_20_26_printed_B`).

2. **p. 881, (20.A.2)–(20.A.3), the leading `β`.** Printed `μ_t = βE_t[⋯]`. Differentiating the
   Lagrangian in `u_{t+1}` gives `μ_t = E_t[z_{t+1} − b + κθ_{t+1} +
   βμ_{t+1}(1 − σ − M₁ − θ_{t+1}M₂)]` (`planner_foc_u`), and then (20.A.3) without the `β`
   (`eq_20_A_3`), which is what the comparison with (20.19) needs. The printed form together with
   the correct condition forces `μ_t = 0`, contradicting (20.A.1) when `κ > 0`, `β < 1`
   (`eq_20_A_2_misprint`). Minor: the Lagrangian on p. 880 has an unbalanced parenthesis, and
   p. 881 writes `M_v` for `M₂`.

3. **p. 887, 20.A.8, the formula for `κ`.** Printed
   `κ = βχ(ȳ − b)(1 − β(1 − σ − γχ)/(1 − γ))^{−1}`. The steady state of (20.43) with `θ̄ = 1`,
   `Q = β`, is solved by `κ = β(1 − γ)χ(ȳ − b)/(1 − β(1 − σ − γχ))` (`ngm_calib_kappa`). With
   `β = γ = σ = 1/2`, `χ = 1`, `ȳ − b = 1` the printed formula gives `1/2`, the solution is `1/4`,
   and `1/2` does not solve the steady state (`ngm_calib_kappa_misprint`).

4. **p. 887, 20.A.8, the exponent in `K̄`.** Printed `K̄ = (r/α)^{1/(1−α)}(1 − ū)`. Solving
   `r̄ = α(K̄/(1 − ū))^{α−1}` gives `K̄ = (r̄/α)^{1/(α−1)}(1 − ū)` (`ngm_calib_K`). With
   `α = 1/2`, `r = 2`, `ū = 0` the printed formula gives `K̄ = 16` and
   `α·16^{−1/2} = 1/8 ≠ 2` (`ngm_calib_K_misprint`).

5. **p. 598, (20.6), argument order.** Printed `M(v, ū) + σū = σ`. Setting
   `u_{t+1} = u_t = ū` in (20.4) gives `M(ū, v) + σū = σ` (`eq_20_5`, `eq_20_6`). With the
   asymmetric matching function `M(u, v) = uv/(u + 2v)` (`skewMatch`, which satisfies all the
   book's assumptions, `skewMatch_bounded`), `σ = 2/5`, `v = 1`, the steady state is `ū = 1/2`
   and `M(v, ū) + σū ≠ σ` (`eq_20_6_misprint`).

6. **p. 882, 20.A.5, the first display.** Printed `κθ_t^η/((1 − γ)βχ) = βE[⋯]` has `β` on both
   sides; (20.29) gives `κθ_t^η/((1 − γ)χ) = βE[⋯]`, i.e. `κθ_t^η/((1 − γ)βχ) = E[⋯]`, with
   bracket `es_bracket_cd`. At a steady state the printed form would force `R̄ = βR̄` with
   `R̄ > 0` (`eq_20_A_5_misprint`). The later displays and (20.A.6) are correct
   (`eq_20_A_5_deriv`, `eq_20_A_6`, `es_G`).

7. **p. 619, §20.8.2, `w̃ = max{w̄, y}`.** With `max`, the flow profit `y − w̃` is never positive
   (`ngm_rigid_max_profit`), contrary to "to maintain a positive profit". With
   `w̃ = min{w̄, y}` the profit is nonnegative, positive iff `y > w̄`, and the wage is `w̄` in
   most periods as the text says (`ngm_rigid_min_profit`).

8. **p. 625, the back-of-the-envelope `Mm = 1.031`.** With `β = 0.996`, `σ = 0.034`,
   `λ = 0.45` and `ρ = b/w^M = 0.4`, the book's formula
   `Mm = (1 + βλ/(1 − β(1 − σ)))/(ρ + βλ/(1 − β(1 − σ)))` (proved: `mm_formula`,
   `mm_formula_of_bellman`) gives `Mm ≈ 1.049 > 1.04` (`mm_back_of_envelope`). (The text says
   "`b = 0.4`"; the formula needs the ratio `ρ`.)

9. **p. 623, (20.56), the characterisation of mean-preserving spreads.** The book states that
   `G` being a mean-preserving spread of `F` is equivalent to `∫_0^x G ≥ ∫_0^x F` for all `x`.
   The forward direction is proved (`eq_20_56_of_mps`, with `mps_ibp` for
   `∫_0^x F = ∫max{x − w, 0}dF`). The converse needs equal means (Mas-Colell–Whinston–Green state
   it for distributions with the same mean): the point mass at `0` satisfies (20.56) against the
   point mass at `1` but is not a mean-preserving spread of it (`eq_20_56_not_sufficient`,
   `mps_mean`). The converse with equal means (Rothschild–Stiglitz) is cited and not formalised.

10. **p. 608, comparative statics in `η`.** "A smaller `η` … makes the response of `θ_t`
    larger" (for a given `θ̄`). The coefficient depends on `η` through `θ̄^ηη`, which increases in
    `η` only where `1 + η log θ̄ > 0`. The claim holds for `θ̄ ≥ 1`, including the calibrated
    `θ̄ = 1` (`ll_cs_eta`), and fails for small `θ̄`: with `θ̄ = e^{−4}` the coefficient is
    smaller at `η = 1/2` than at `η = 3/4` (`ll_cs_eta_counterexample`). The other six signs
    hold as stated (`ll_cs_kappa`, `ll_cs_gamma`, `ll_cs_chi`, `ll_cs_rho`, `ll_cs_beta`,
    `ll_cs_sigma`), for `ρβ < 1`.

11. **p. 596, the range of `|1 − λ − σ|`.** The book says `|1 − λ − σ| ∈ (0, 1)`. For
    `λ, σ ∈ (0, 1)` it lies in `[0, 1)`; it is `0` when `λ + σ = 1` (`lake_abs_lt_one`,
    `lake_abs_eq_zero_example`). Convergence is unaffected (`lake_tendsto`).

12. **p. 605, (20.22), the index.** Printed `M₁(u_{t+1}, v_{t+1})u_t/M(u_{t+1}, v_{t+1}) = γ`;
    the elasticity is evaluated at `t + 1` throughout, `M₁(u_{t+1}, v_{t+1})u_{t+1}/M(⋯)`
    (`eq_20_22`, `hosios_node`).

13. **Typos not affecting results.** p. 608: `E[z_{t+1}] = ρz_t` should be
    `E[ẑ_{t+1}] = ρẑ_t` (`ll_undetermined`). p. 619, (20.46), and p. 884, 20.A.6:
    `u′ = (1 − λ_w(θ(X))) + σ(1 − u)` lacks the factor `u` (it is (20.35)).

## Added hypotheses and departures

1. **p. 597, the bounds `M(u, v) ≤ u`, `M(u, v) ≤ v`.** They are inconsistent with the
   Cobb–Douglas function (20.23) used from §20.6 on: `λ_w(θ) = χθ^{1−η}` exceeds `1` for large `θ`
   (`cd_not_bounded`). The bounds are the separate property `MatchFn.Bounded`, assumed only where
   used (`match_lamW_le_one`, `match_lamF_le_one`, `match_ubar_exists`).

2. **p. 598, existence of `ū` for given `v`.** Uniqueness follows from monotonicity
   (`match_ubar_unique`); existence needs continuity of `u ↦ M(u, v)` (added) and the bound
   `M ≤ u` (`match_ubar_exists`).

3. **p. 601, existence of `θ̄`.** The book shows uniqueness only. Existence is proved when `λ_f` is
   continuous, `λ_f(θ) → 0` as `θ → ∞` and the steady-state map is nonnegative somewhere
   (`ss_exists`), e.g. when `λ_f(θ) → ∞` as `θ → 0` (`ss_exists_of_tendsto`); the Cobb–Douglas
   case has a unique steady state for every `z > b` (`ss_cd_existsUnique`). Uniqueness uses
   `z > b` and `γ ≥ 0` (`ss_phi_strictAntiOn`).

4. **Footnotes 6–7.** Footnote 6's condition is imposed on an interval containing the path
   (`fn6_rhs_strictMonoOn`); for Cobb–Douglas matching it cannot hold for all `θ > 0`. The
   divergence of footnote 7 is proved globally from this monotonicity and the uniqueness of
   `θ̄` (`fn7_diverge_above`, `fn7_diverge_below`, `fn7_jump`), not only locally from the slope;
   the slope statement `dθ_{t+1}/dθ_t > 1` assumes the transition map differentiable at `θ̄`
   (`fn7_slope`, `fn7_slope_gt_one`).

5. **Hosios condition (20.A.3).** As in the book, efficiency is established at the level of
   first-order conditions: under constant returns and `η(u, v) = γ` the planner's first-order
   conditions coincide with the equilibrium system (`hosios`). The planner's problem is not
   convex, and sufficiency of its first-order conditions is not claimed. Constant returns enter
   through Euler's theorem (`match_euler`, for `M` differentiable at the point).

6. **Uncertainty.** The book's productivity is a general Markov process and §20.8's aggregate
   state `X = (z, K, u)` has a continuum of values. The formalisation uses a finite state set
   with transition weights or state prices (`dmpEx`); the derivations use only linearity of the
   conditional expectation (`dmp_ex_add`, `dmp_ex_mul`). The deterministic case is `Z = Unit`.

7. **p. 601, (20.13), Nash bargaining.** The maximisation is over wages giving both parties a
   nonnegative surplus, where the Nash product is defined (`eq_20_15`); the first-order condition
   of 20.A.1 is equivalent to (20.15) for positive surpluses (`eq_20_A_1`).

8. **§20.7, `G = Θ/Γ`.** It needs `Γ ≠ 0` (added) and uses the steady-state condition
   `κσ̄θ̄^η/χ = ξc̄` from (20.28) (`es_ss_foc`), which 20.A.5 uses without saying so (`es_G`).
   The relations (20.31)–(20.32) hold exactly, not only to first order (`eq_20_31`,
   `eq_20_32`).

9. **§20.9, strict comparative statics and Leibniz's rule.** The strict signs of `∂G/∂β`,
   `∂G/∂σ` and the strict increase in `β` need `∫_{w > w*}(w − w*)dF > 0` (`mc_G_partials`,
   `mc_cs_beta`); `d/dw*∫_{w*}(w − w*)dF = −(1 − F(w*))` needs `F` to have no atom at `w*`
   (`mc_I_hasDerivAt`). For the shift of offers, the difference bounds
   `0 < R(ε₂) − R(ε₁) < ε₂ − ε₁` need only `F(w ≥ w*) > 0` (`mc_shift_bounds`); the derivative
   formula assumes `w*(ε)` differentiable, as the book's use of the implicit function theorem
   does (`mc_shift_deriv`). `W(0) < U` uses `U > 0`, which follows from `b > 0` (`mc_U_pos`,
   `mc_W0_lt`).

10. **§20.9, the Diamond paradox.** The book's argument is verbal. The formalisation makes the
    game explicit: `n` firms post wages, the worker meets one at random and her acceptance rule
    has the two properties the argument uses (offers below `b` are rejected; offers within the
    search cost `s` of the best offer are accepted) (`DiamondWorker`, with the concrete rule
    `diamondAccept`). The unique Nash equilibrium is every firm offering `b`, for every `s > 0`
    (`diamond_paradox`).

11. **§20.8, the family's problem.** The dynamic programs (20.33), (20.46) and the functional fixed
    point `(Q, Ω, w, d, θ)` are not formalised; (20.36) is proved from the first-order and envelope
    conditions (`eq_20_36`) and, independently, as the first-order condition of a two-period
    problem with Arrow securities (`ngm_arrow_foc`).
