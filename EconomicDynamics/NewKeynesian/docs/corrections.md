# Corrections and departures: Miao Chapter 19

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 19, Dynamic New
Keynesian Models, pp. 615–670. Lean names are relative to `Miao.NewKeynesian`. Every book item is
located in the [source map](source-map.md).

## §19.1 and Exercise 19.1

1. **(19.1), p. 617.** The printed utility is undefined at `γ = 1` or `ϕ = 1` (log cases); the
   derivatives are proved for `γ, ϕ ≠ 1` (`nk_u_C`, `nk_u_m`). `u₂ < 0` needs `χ > 0`, which the
   book does not state (`nk_u_signs`).
2. **Satiation, p. 617.** The book recalls the assumption "`u₃(·, ·, m) ≤ 0` for `m > m*`" and
   then adopts (19.1), for which it fails: `u₃ = m^{−ϕ} > 0` for all `m`
   (`nk_u_no_satiation`). Consequently (19.4) has a solution only if `i_t > 0`
   (`nk_money_demand_pos_rate`), and then the money supply is unique (`nk_money_supply`).
3. **First-order conditions, p. 618,** are listed without derivation; they are the hypotheses
   of `eq_19_2`–`eq_19_4`. In (19.3) `E_t` is Mathlib's conditional expectation, and pulling
   `C_t^γP_t` out of it needs its `F_t`-measurability and the integrability of the integrands
   (`eq_19_3`). The transversality conditions are not used.
4. **(19.6), p. 619.** "Solving yields (19.6)" is proved twice: as the pointwise first-order
   condition (`eq_19_6_foc`, with `p_j > 0`) and as optimality: every input profile costs at
   least `P·Y(y)` (`eq_19_6`, a tangent-line/AM–GM argument). The firms are indexed by a
   general probability space; integrability of `p^{1−ε}`, `y^{(ε−1)/ε}` and `py` is assumed.
5. **The Calvo first-order condition, p. 621,** is derived (by differentiation) for objectives
   with finitely many (date, state) terms (`nk_calvo_term_deriv`, `nk_calvo_foc`); (19.11) is
   derived from the first-order condition for summable infinite families (`eq_19_11`).
6. **Law of large numbers, pp. 621–622.** The law of large numbers for a continuum of Calvo
   draws is replaced by its consequence, used as a hypothesis: the non-adjusters (a measurable
   set of measure `θ`) are representative of last period's prices (`nk_calvo_avg`, `eq_19_13`,
   `eq_19_17`). `P* > 0` is assumed.
7. **"`θ → 0`", p. 623,** is evaluated at `θ = 0` (`nk_flex_reset`); the limit is not taken.
8. **Log-linearisation, pp. 624–627,** is formalised as differentiation along positive paths
   through the steady state (`nk_path_deriv`, `nk_rpow_path`). For (19.11) this is done term by
   term (`nk_loglin_reset_terms`), and the conditional expectation of (19.26)–(19.27) is over
   finitely many successor states (`eq_19_26`, `nk_loglin_natural_rate`).
9. **The interest rate in (19.26)–(19.29).** The book's `ı̂_t = d(1 + i_t)/(1 + i) = i_t + ln β`
   uses `ln(1 + i_t) ≈ i_t`. With `i_t` read as `ln(1 + i_t)` (and `r^n_t` as `ln(1 + r^n_t)`),
   `ı̂_t = ln(1 + i_t) + ln β` exactly and (19.29) holds exactly (`eq_19_29`).
10. **Price dispersion to first order, pp. 625–626.** The book's total differential of (19.16)
    treats last period's dispersion as fixed. The log-linear (19.17) is
    `Δ̂_t = θΔ̂_{t−1} + (ε/(1 − α))(θπ_t − (1 − θ)q_t)` (`nk_loglin_19_17`), which by (19.19) is
    `Δ̂_t = θΔ̂_{t−1}` (`nk_loglin_dispersion`); so `Δ̂_t = 0` for all `t` only from an initial
    `Δ̂_{−1} = 0` (otherwise `Δ̂_t = θ^tΔ̂_0 → 0`) (`nk_dispersion_zero`), and then
    `Ŷ = Â + (1 − α)N̂` (`nk_loglin_output`).
11. **(19.25), p. 626.** Both printed forms of κ agree for `α < 1` (`eq_19_25`); `κ > 0` needs
    `0 < θ < 1`, `βθ < 1`, `0 ≤ α < 1`, `ε ≥ 0` and `ν + α + γ(1 − α) > 0` (`nk_kappa_pos`).
12. **The constant `ln β`.** In the stochastic log-linear system the constant is `ln β · 𝟙` for an
    adapted constant random variable `𝟙` (`eq_19_27`, `eq_19_28`, `nk_dnkSystem`).
13. **Exercise 19.1, p. 668.** The book states (19.31) as necessary and sufficient with no sign
    restriction on the policy coefficients. With `κ, γ > 0`, `0 < β < 1`: for `φ_π, φ_y ≥ 0`
    (Bullard–Mitra's assumption) the claim holds (`ex_19_1`); for `φ_y ≥ 0` and any `φ_π` the
    exact condition is (19.31) **or** `κ(1 + φ_π) + (1 + β)(2γ + φ_y) < 0` (`ex_19_1_exact`),
    and (19.31) is not necessary: `κ = γ = 1`, `β = 1/2`, `φ_π = −5`, `φ_y = 0` is determinate
    (`ex_19_1_not_necessary`). Necessity needs a nonzero adapted `𝟙` (a nontrivial space of
    random variables); determinacy is for all bounded adapted shocks `v`, `r^n`, the book's
    stable solutions being bounded in the sense of Definition 2.3.1. The proof uses the
    Chapter 2 Blanchard–Kahn results through Exercise 2.2 (`nk_dnk_iff`, `ex_2_2_suff`,
    `nk_jump2_nonunique`).
14. **Figures 19.1–19.2.** The qualitative statements are proved for AR(1) shocks under
    (19.31) with `0 ≤ ρ < 1` (`nk_fig_19_1`, `nk_fig_19_2`). The text's "rise in the nominal
    rate" for Figure 19.1 refers to the shock; the equilibrium nominal-rate response
    `(γ(1 − ρ)(1 − βρ) − ρκ)Λ` has a parameter-dependent sign and is not claimed.

## §19.2 and Exercise 19.2

15. **Exercise 19.2 and (19.31), pp. 635 and 669: the rule must track the natural rate.** The
   text says strict inflation targeting "can be implemented by assuming a Taylor rule as in
   (19.29), where the monetary policy shock is removed", i.e. `i_t = −ln β + φ_ππ_t + φ_yx_t`.
   At `π = x = 0` the IS curve (19.28) requires `i_t = r^n_t` (`mp_strict_targeting_rate`), so
   with any constant intercept `c` the zero path is an equilibrium iff `r^n_t = c` at every date
   (`mp_zero_eqm_iff`); when the natural rate moves the printed rule does not implement the
   optimal policy (`mp_printed_rule_fails`; concrete counterexample
   `mp_printed_rule_counterexample`, where (19.31) holds). True statement: the rule
   `i_t = r^n_t + φ_ππ_t + φ_yx_t` implements strict inflation targeting iff (19.31), for
   `φ_π, φ_y ≥ 0` (`ex_19_2`; sufficiency for any `φ_π` and `φ_y ≥ 0` is `eq_19_31`). For
   `φ_π < 0` the exact determinacy condition has a second branch (Chapter 2, `ex_2_2_b_exact`).
   "Implements" is formalised as: `π = x = 0` is an equilibrium and the only stable adapted one
   (`mpImplements`).
16. **Discretionary inflation, p. 638.** The book's closed form
   `λκx*/(κ² + λ − βλ) + λκu_t/(κ² + λ − βλρ_u)` has an extra factor `κ` in the shock
   coefficient: the forward sum it is derived from equals
   `λκx*/(κ² + λ − βλ) + λu_t/(κ² + λ − βλρ_u)` (`mp_discretion_inflation`,
   `mp_ex951pi_closed`); the printed form is false whenever `κ ≠ 1` and `u_t ≠ 0`
   (`mp_discretion_printed_false`).
17. **The price level under commitment, p. 637.** The printed law
   `p_t = ap_{t−1} + au_t/(1 − βaρ_u)` omits a constant: in general
   `p_t = ap_{t−1} + au_t/(1 − βaρ_u) + (1 − a)p_{−1} + aκx*/(1 − βa)`, and `p_t = p_{−1} − βμ_{x,t+1}`
   (`mp_price_level`). The printed law holds iff `(1 − a)p_{−1} + aκx*/(1 − βa) = 0`, in particular
   for `x* = 0` and `p_{−1} = 0`; it fails at `t = 0` for `p_{−1} = 0`, `κx* ≠ 0`
   (`mp_price_level_printed_false`). The stationarity claim is true (`mp_price_level_stationary`).
18. **(19.30) and the Step 1 dispersion law are stated as precise Taylor expansions
   (departure in form).** (19.30) is proved with an explicit cubic remainder bound and as a
   little-o statement (`eq_19_30`, `eq_19_30_littleO`). The second-order dispersion law is proved
   as `δ_t = θδ_{t−1} + Kπ_t² + o(π_t²) + R_t` with `δ = Δ − 1` and the cross term
   `|R_t| ≤ 2θ(ε/(1 − α))|π_t||δ_{t−1}|` (`mp_dispersion_second_order`), which is third order because
   `δ` is second order; `ln Δ` and `Δ − 1` differ by at most `2(Δ − 1)²` (`mp_log_dev`). The
   coefficient `(1 − α + αε)εθ/(2(1 − α)²(1 − θ))` is confirmed (`mp_hasDerivAt_hd`). The printed
   exponent in the display "By (19.13) and (19.17)" is garbled in our text extraction; the
   recursion is proved with the exponent `ε/((1 − α)(ε − 1))` that (19.13) and (19.17) imply
   (`mp_dispersion_recursion`).
19. **Steps 2–3 are exact identities with the neglected terms explicit (departure in form).**
   Step 2 keeps the third- and fourth-order terms of the substitution (`mp_step2_subst`) and the
   term `Φ × [second-order terms]` that the small-distortion assumption drops (`mp_step2_small`);
   the terms independent of policy are given explicitly (`mpTip`). Step 3 is proved path by path
   for bounded paths and the second-order dispersion law with `Δ̂_{−1} = 0` (`mp_step3`), so it
   holds under `E` whenever the sums may be interchanged with the expectation.
20. **Expectations along expected paths (as in Chapter 9).** Forward solutions (the commitment
   multiplier `mp_commit_rule`, the timeless law `mp_timeless_unique`, discretion
   `mp_discretion_inflation`) are proved along the expected path `E_tu_{t+j} = ρ_u^ju_t`; the laws
   of motion derived from the multiplier rule (`mp_commit_x_law`, `mp_commit_pi_law`,
   `mp_price_level`) are identities along every realised path of `u`. Strict inflation targeting
   (`mp_strict_targeting`) is proved for perfect-foresight paths. Exercise 19.2 is proved in the
   stochastic setting of Chapter 2 (a `CondExpSystem`).
21. **Hypotheses added.** (9.29) has the roots `0 < a < 1 < 1/(βa)` only for `κ ≠ 0` (Chapter 9,
   `eq_9_29_kappa_zero`), so the commitment results that use `a = ex942a` assume `κ ≠ 0`;
   `|ρ_u| ≤ 1` is assumed for the forward sums. The efficient-allocation results assume a
   probability space of firms (the book's `dj` on `[0, 1]` is one instance), `0 ≤ α < 1`, `ε > 1`
   and `γ ≠ 1` (the form (19.1)).
22. **Comparisons proved under stated conditions.** "Discretion chooses a higher inflation rate at
   all times" is proved without cost-push shocks, for `κx* > 0` (`mp_discretion_above_commitment`,
   from `a < λ/(κ² + λ)`, `mp_a_lt_theta`); "even larger … following a positive cost-push shock"
   is proved as: the date-0 gap is affine in `u_0` with positive slope (`mp_discretion_gap_impact`).
   The Figure 19.3 statements are proved for all admissible parameters with `x* = 0`, `ρ_u = 0`
   and a single shock (`mp_fig_19_3_commitment`, `mp_fig_19_3_discretion`).
23. **Not formalised:** Yun (2005)'s optimality result and the Dennis (2010) dominance remark
   (cited without derivation); the numbers plotted in Figure 19.3 (computational).

## §19.3 and Exercises 19.3–19.5

### Neoclassical benchmark and monopolistic competition

24. **`v'' < 0`, p. 640 (false as an assumption).** With concave disutility of work `η_v` can be
   negative and the multiplier exceeds one: `u = log`, `f = id`, `v(N) = 2 log(1 + N)` give the
   solution path `Y(G) = 1 + 2G` of (19.40) and `dY/dG = 2` (`fs_eq_19_41_vpp_neg`; there
   `f'' = 0`). The intended assumption is `v'' > 0`; `η_v > 0` holds when `v'' ≥ 0` and `f'' < 0`
   (`fs_vtilde_deriv2_pos`).
25. **`ṽ(Y_t)` in (19.40) and (19.43), pp. 641, 643 (notation).** The right-hand sides are the
   derivative `ṽ'(Y_t)` of `ṽ = v ∘ f⁻¹` (`fs_vtilde_hasDerivAt`, `eq_19_40`, `eq_19_43`), as the
   book itself uses in (19.47) and in `η_v`.
26. **(19.41) (departure).** The multiplier is proved by implicit differentiation of any solution
   path of the steady-state condition that is differentiable at `Ḡ` (`eq_19_41`,
   `fs_multiplier_formula`); existence of such a path (implicit function theorem) is not
   formalised. `f` is taken to be a bijection of `ℝ` with `f' > 0`; differentiability of `f⁻¹`
   is then proved.
27. **The rental first-order condition, p. 645 (misprint).** The printed
   `R^k/P = MC(f'(N/K) − f'(N/K)N/K)` should read `MC(f(n) − nf'(n))`, `n = N/K`
   (`fs_costmin_foc`).

### The DNK model under a Taylor rule

28. **The log-linearised marginal cost, p. 646 (misprint).** The book prints
   `MĈ_t = η_vŶ_t + η_u(Ŷ_t − Ĝ_t) = (η_u + η_v)Ŷ_t − ΓĜ_t`; the last expression is
   `(η_u + η_v)(Ŷ_t − ΓĜ_t)` (`fs_mc_loglin`), which is what (19.48) and its `κ` use (`eq_19_48`).
29. **The log-linearised reset price, p. 645 (departure).** The equation
   `P̂*_t = (1 − βθ)Σθᵏβᵏ(P̂_{t+k} + MĈ_{t+k})` is taken as given: it is (19.20) of §19.1 with
   `MC_{t+k|t} = MC_{t+k}`, outside this section. Its recursive form and the Phillips curve are
   proved (`fs_reset_recursive`, `fs_q_recursive`, `fs_nkpc`); the model is deterministic, so the
   footnote-8 expectations are dropped there.
30. **(19.52), p. 647 (reading of a garbled formula).** The derivation gives
   `γ_y = (1 − ρ + (ψ − σφ_y)Γ)/(1 − ρ + ψ)`, `γ_π = κ(γ_y − Γ)/(1 − βρ)`, `γ_i = φ_πγ_π + φ_yγ_y`
   (`eq_19_52`, an equivalence for `Ĝ₀ ≠ 0`), the reading of the printed formula. It is proved for
   `0 ≤ ρ < 1` (the book does not state the range); `ψ > 0` needs `φ_π > ρ` (`fs_psi_pos`).

### The zero lower bound

31. **"Holds for all `0 ≤ μ ≤ μ̄`", p. 650.** (19.55) fails at `μ = μ̄`
   (`eq_19_55_fails_at_mubar`); on `[0, 1]` it holds iff `μ < μ̄` (`eq_19_55_iff`), with `μ̄ ∈ (0, 1)`
   the unique root of `h` (`fs_mubar_exists`).
32. **"`i_L = 0` iff `Ĝ_L < Ĝ_c`", p. 650.** At `Ĝ_L = Ĝ_c` both branches coincide with `i_L = 0`;
   the correct statement is `i_L = 0` iff `Ĝ_L ≤ Ĝ_c`, and for every `Ĝ_L` the constant
   equilibrium of (19.54), (19.56), (19.57) exists and is unique (`eq_19_54_branches`).
33. **"`Ĝ_c > 0`", p. 650.** Not unconditional: `Ĝ_c > 0` iff
    `r_L < −r̄/((κφ_π/(1 − βμ) + φ_y)ϑ_r)` (`fs_Gc_pos_iff`); the book's next sentence ("can hold
    when `r_L` is sufficiently negative") says as much.
34. **Exercise 19.3 (interpretation).** "Solved forward to obtain a unique bounded solution" is
    formalised as: for every `(r_L, Ĝ_L)` the crisis-state system (the recursive form of (19.48)
    and (19.53) with `i_t = 0`, the absorbing normal state contributing zero) has exactly one
    bounded solution (`ex_19_3`); the summed form of (19.48) is equivalent for bounded paths
    (`fs_zlb_sum_form`); the solution is then the constant one (`ex_19_3_solution`). The proof
    assumes `0 < β < 1`, `κ, σ > 0`, `0 ≤ μ < 1`.
35. **"as shown in Figure 1", p. 652** refers to Figure 19.4.

### Duration of fiscal stimulus

36. **`ϑ_π ≡ (1 − μ)λϑ_r`, p. 655 (false).** The derivation gives
    `ϑ_π = σ(1 − μ)λ/h(μ) = (1 − μ)λϑ_r/(1 − βμ)` (`fs_crisis_three_state`); the printed value is
    `(1 − βμ)ϑ_π` (`fs_thetaPi_printed`) and differs whenever `μ, λ > 0`
    (`fs_thetaPi_printed_ne`). The printed `ϑ_C = σ⁻¹·(1 − μ)λϑ_r` is correct
    (`fs_thetaC_eq_printed`), so `ϑ_C = σ⁻¹ϑ_π` is false for the true `ϑ_π`. (19.61) holds with the
    corrected `ϑ_π` (`eq_19_61`, `ex_19_4`). The text's numbers confirm the correction: at
    `λ = 0.91` the multiplier is negative with the corrected `ϑ_π` but positive with the printed
    one (`fs_fig_19_6_point_nine_one`).
37. **"`T ≥ t < T'`", p. 655**, should read `T ≤ t < T'`. In the transitional state the Taylor rule
    is used without the `max` (as in the text: "when the interest rate is determined by the
    Taylor rule"), `ex_19_4_transitional`.

### Welfare

38. **The weight `λ_y = κ/θ`, p. 658 (notation clash).** `θ` here is Woodford's elasticity of
    substitution `ε` (Figure 19.7's `θ = 12.77`), not the Calvo parameter `θ` used in `κ`; the
    derivation gives `λ_y = κ/ε` (`ex_19_5`).
39. **`λ_g ≡ (η_g/η_u + 1 − Γ)Γγ_y` and `ξ ≡ (κ/(1 − βμ))² + γ_y`, pp. 658–659 (misprints).** In
    both `γ_y` should be `λ_y`: `λ_g = λ_yΓ(η_g/η_u + 1 − Γ)` (`ex_19_5`, `ex_19_5_flex`,
    `fs_weights_pos`) and `ξ = (κ/(1 − βμ))² + λ_y` (`fs_xi`, `fs_loss_reduced`).
40. **`η_g` "the elasticity of `g'` with respect to `G`", p. 658 (imprecise).** The derivation
    (and case B, `η_g = 4η_u`) needs `η_g = −Ȳg''/g'`, the elasticity with respect to `G/Ȳ`, in
    parallel with `η_u = −Ȳu''/u'` (`ex_19_5_flex`).
41. **The zero-output-gap level `Ĝ_L/|r_L| = ϑ_r/ϑ_G`, p. 660 (false).** That level keeps
    `Ŷ_L = 0` but leaves the gap `Γϑ_r r_L/ϑ_G < 0` and deflation (`fs_zero_gap_printed`). The gap
    and inflation are zero at `ϑ_r/(ϑ_G − Γ)` (`fs_zero_gap_GL`), and the optimum lies below it
    (`fs_optimal_GL_lt_zero_gap`), as Figure 19.7 shows; at the figure's parameters the printed
    level is below the optimum (`fs_fig_19_7`).
42. **Exercise 19.5 (departure: what is proved).** The approximation is split into precise
    statements: the second-order Taylor expansion with `o(s²)` remainder of the flexible-price
    period utility along every direction (`ex_19_5_flex`, from `fs_taylor2`); the second-order
    expansion of the Calvo dispersion index in `π` and its exact linearity in last period's
    dispersion at `π = 0` (`ex_19_5_dispersion`, `fs_dispersion_lin`); the first-order labour cost
    of dispersion (`fs_labor_dispersion`); the exact discounting identity for the dispersion
    recursion (`fs_dispersion_sum`); and the exact assembly into `−(u'Ȳε/(2κ̃))·(19.64)`
    (`ex_19_5`). Dropping the third-order terms (e.g. `θ(e^{επ} − 1)(Δ₋₁ − 1)`) between these steps
    is the book's approximation argument and is not a theorem.
