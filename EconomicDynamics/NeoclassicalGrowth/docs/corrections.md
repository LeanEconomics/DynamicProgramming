# Corrections and departures: Miao Chapter 14

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 14,
Neoclassical Growth Models, pp. 455–508. Lean names are relative to `Miao.NeoclassicalGrowth`. Every
book item is located in the [source map](source-map.md).

## Introduction and §14.1

### §14.1.1 A basic Ramsey model

1. **The limit condition on utility, p. 456.** The book assumes `lim_{c→0} u(c, ·) = ∞`. This
   is impossible for a utility increasing in `c` (which `u_c > 0` requires): `u(c) ≤ u(1)` for
   `c < 1` (`rm_inada_u_misprint`). The intended condition is `lim_{c→0} u_c = ∞`, which log
   utility satisfies (`rm_log_inada`).
2. **The limit condition on production, p. 457.** The book assumes `lim_{K→∞} F(K, 1) = 0`.
   With `F(0, 1) = 0` and `F₁ > 0` this is impossible: `F(K, 1) ≥ F(1, 1) > 0` for `K ≥ 1`
   (`rm_inada_F_misprint`). The intended condition is `lim_{K→∞} F₁(K, 1) = 0`; Cobb–Douglas
   satisfies both Inada conditions (`rm_cd_inada_zero`, `rm_cd_inada_top`).
3. **The detrended competitive Euler equation, pp. 459–460.** The printed
   `u_c(c̃_t, n_t) = βu_c(c̃_{t+1}, n_{t+1})(R^k_{t+1} + 1 − δ)` omits the factor `g_a^σ` that
   detrending (14.7) with KPR utility produces (and that the planner's detrended system on
   p. 465 has): the correct equation is `g_a^σu_c(c̃_t, n_t) = βu_c(c̃_{t+1}, n_{t+1})(R^k_{t+1} +
   1 − δ)` (`rm_detrend_planner`). Both together force `g_a^σ = 1`
   (`rm_detrend_euler_misprint`). The claim "the competitive equilibrium allocations are Pareto
   optimal" is correct once the factor is restored (`rm_ce_planner`, `rm_planner_ce`).
4. **The planner's intratemporal condition, p. 464.** Printed `−u_n/u_c = F_N(k_t, A_tn_t)`;
   the correct condition is `−u_n/u_c = A_tF_N(k_t, A_tn_t)` (`rm_planner_intratemporal`).
   Both together force `A_t = 1` when `F_N ≠ 0` (`rm_planner_intratemporal_misprint`). The
   detrended version on p. 465 is correct.
5. **Optimality notion for the planner.** The planner's first-order conditions are proved
   necessary under "no finite improvement" (`RMPlanNFI`), which is implied by maximising the
   infinite discounted sum when all feasible plans have summable utility
   (`rm_planner_nfi_of_optimal`). The utility is assumed Fréchet differentiable at the plan.
6. **Equilibria by first-order conditions.** The Arrow–Debreu, sequential and recursive
   equilibria are represented by their first-order (and envelope) conditions, as in the text;
   the sufficiency of these conditions for household optimality is not formalised. The
   recursive equilibrium is formalised in the direction the text uses (an RCE generates a
   sequential equilibrium, `rm_rce_sequential`), assuming the first-order and envelope
   conditions of the household's Bellman problem.
7. **Steady state, phase diagram and saddle path.** The text of §14.1 states the detrended
   system but does not carry out the steady-state, phase-diagram or linearisation analysis.
   These are formalised for the detrended model (`RMSteady`, `RMDynamics`); the dynamics use
   inelastic labour `n ≡ 1`, generalising Example 1.6.1 to `b = β/g_a^σ` and `γ = gₙg_a`. The
   saddle-path slope is positive and the convergence monotone (`rm_lin_saddle`,
   `rm_lin_saddle_monotone`), with no extra condition.

### §14.1.2 Incorporating fiscal policy

8. **The proof of Proposition 14.1.1, pp. 469–470.** The proof writes
   `Q_tK_{t+1} = βΛ_{t+1}/Λ_t(D_{t+1} + Q_{t+1}K_{t+2})` and
   `Q_tK_{t+1} = ∑_{j≥1} βʲΛ_{t+j}/Λ_t D_{t+j}`. Both drop the factor `1 − τᵈ`: the correct
   identities are `Q_tK_{t+1} = βΛ_{t+1}/Λ_t[(1 − τᵈ_{t+1})D_{t+1} + Q_{t+1}K_{t+2}]`
   (`rm_prop_14_1_1_step`) and `Q_tK_{t+1} = ∑_{j≥1} βʲΛ_{t+j}/Λ_t (1 − τᵈ_{t+j})D_{t+j}`
   (`rm_prop_14_1_1_sum`). The printed step and the true one together force
   `τᵈ_{t+1}D_{t+1} = 0` (`rm_prop_14_1_1_misprint`). The proof also writes `w_tN_{t+1}` for
   `w_{t+1}N_{t+1}`, and the step "Qt Kt+1 is the ex-dividend equity value" needs the
   no-bubble condition `lim β^TΛ_TV_T = 0` in addition to the stated transversality condition
   (`rm_prop_14_1_1_exdiv`). The proposition is correct (`proposition_14_1_1`); it also needs
   `F = F_KK + F_NN` (constant returns) along the path and the firm's labour condition `w = F_N`.
9. **The government budget constraint, p. 469.** The corporate revenue is printed as
   `τᶜ(F(K, N) − wN)`, but the dividend definition `D = (1 − τᶜ)(F − wN) − I + τᶜδK` gives the
   firm a depreciation allowance, so the revenue is `τᶜ(F − wN − δK)`. With the printed
   constraint Walras' law fails: the household budget, the printed government budget, the
   dividend definition and the resource constraint force `τᶜδK = 0`
   (`rm_gov_budget_misprint`). `RMFiscalEq` uses the corrected constraint (`rmGovBudget`),
   under which the household's budget constraint holds (`rm_walras`).
10. **The household's problem (14.17)** is printed with an expectation `E`; the model is
    deterministic and the expectation is dropped.
11. **(14.21) and the neutrality of a permanent distribution tax** need `τᵈ ≠ 1` (`eq_14_21`,
    `rm_distribution_tax_neutral`); the neutrality result also uses constant returns. The
    lump-sum taxes change by `(τᵈ − τᵈ')D`, the price of capital to `1 − τᵈ'` and the equity
    value to `(1 − τᵈ')(D + K_{+1})`.
12. **Temporary changes.** The text does not derive them; a time-varying distribution tax gives
    `(1 − τᵈ_t)/(1 − τᵈ_{t+1}) = βΛ_{t+1}/Λ_t[...]` (`rm_temporary_distribution_tax`), which
    differs from (14.21) whenever `τᵈ_t ≠ τᵈ_{t+1}`
    (`rm_temporary_distribution_tax_distorts`).
13. **Ricardian equivalence** is formalised as: the equilibrium conditions involve `(B, T)` only
    through the government budget constraint, and the household's budget then holds by
    Walras' law (`rm_ricardian`).

### Exercises

14. **Exercise 14.1.** The household-capital formulations are not given in the book; they are
    set up with a capital income tax `τᵏ` on `(R^k − δ)K` (`RMHKEq`, `RMADEq`), and the
    equivalence of allocations holds with `τᵏ = τᶜ` and a constant distribution tax (`ex_14_1`).
    In the Arrow–Debreu formulation the government balances its budget date by date with
    lump-sum taxes. With a time-varying distribution tax the firm-ownership arrangement has a
    different capital condition (item 12), so the equivalence would need a matching
    investment tax in the other two arrangements.
15. **Exercise 14.2** needs `τᵈ ≠ 1` (for `τᵈ = 1` the condition (14.20) is vacuous) and
    `β < 1` (for `V = (1 − τᵈ)D/(1 − β)`), and the government budget at the steady state reads
    `G + (1 − β)B = revenue + T` with the corrected corporate revenue (`ex_14_2`).

## §14.2 and §14.3.1

### §14.2 A basic RBC model

### Corrections

16. **(14.34), second line, p. 476 (sign).** The book prints
   `Ĉ_{t+1} − Ĉ_t = +(1 − α)βα(Y/K)/(α + ζ)·Ĉ_{t+1} + …`. Subtracting `Ĉ_{t+1}` in (14.33) gives
   `−(1 − α)βα(Y/K)/(α + ζ)·Ĉ_{t+1}` (`eq_14_34_C`). The printed equation contradicts (14.33)
   whenever that coefficient is nonzero (`eq_14_34_printed_false`). The book's isocline
   `Ĉ_{t+1} = (1 + ζ)/(1 − α)·ẑ_{t+1} − ζK̂_{t+1}` (p. 477) is the one the corrected equation gives
   (`rb_isocline_C`). The printed sign would give an upward-sloping isocline.
17. **Calibrated `χ`, p. 474.** With `α = 0.33`, `β = 0.99`, `δ = 0.025`, `N = 0.33`, (14.28) gives
   exactly `χ = (1 − α)(1 − N)/(N(1 − δα/(1/β − 1 + δ))) = 623971/350889 ≈ 1.778`
   (`rb_calib_chi`), not the printed `1.75` (`rb_calib_chi_ne`). The same applies to "we still
   obtain `χ = 1.75`" for (14.38) on p. 489, since the steady state does not depend on `γ`
   (`rb_u38_intratemporal`).
18. **Stock return, p. 479.** "`R^s_t = R_kt + 1 − δ ⟹ R̂^s_t = R̂_kt`" is false for log deviations
   when `δ < 1`. The log deviation of `R^s` is `(R_k/R^s)R̂_k = (1 − β(1 − δ))R̂_k`
   (`rb_stock_return_loglin`). Counterexample: `rb_stock_return_printed_false`. It holds when
   `R̂_k` is read as `dR_k/R^s`, the convention the book uses for interest rates on p. 480.

### Departures

19. **First-order conditions (14.26)–(14.27): necessity.** The book asserts that the optimum
   satisfies them. Necessity is proved for the one-step variations: (14.27) for the static
   labour choice given `K_t`, `K_{t+1}` (`rb_labour_nec`), and (14.26) for the variation in
   `K_{t+1}` with finitely many successor states (`rb_euler_node_nec`). Both are also proved
   sufficient (`rb_labour_suff`, `rb_euler_node_suff`). A general measure-theoretic necessity
   theorem (differentiation under `E`) is not formalised.
20. **Sufficiency with transversality (made precise).** In the stochastic setting (probability
   space, filtration, Mathlib's `condExp`), interior feasible adapted plans satisfying (14.27),
   (14.26) a.e. and transversality `βᵀE[K_{T+1}/C_T] → 0` are optimal (`rb_planner_suff`,
   `rb_planner_optimal`). Integrability of the utilities and of the terms `R_tK_t/C_t`,
   `K_{t+1}/C_t` of both plans is assumed. Expected discounted utility is the limit of expected
   partial sums. The same argument gives the household's optimum (`rb_household_suff`,
   `rb_household_optimal`).
21. **Non-vacuity instance.** All hypotheses of `rb_planner_suff` and `rb_IsSCE` are shown to
   hold for the closed-form plan with full depreciation `δ = 1` and a deterministic TFP path
   (`rb_bm_solution`, `rb_bm_sce`), on every probability space. No closed-form stochastic
   instance with `δ < 1` is given.
22. **Equivalence of equilibrium and planner.** The sequential competitive equilibrium
   (`rb_IsSCE`) is defined by the household's first-order conditions (sufficient by item 20), the
   firm's profit maximisation and profit payout, with a unit population (the §14.1 setting with
   `g_a = g_n = 1`). With positive capital and hours, it is equivalent to marginal-product prices,
   zero profit and the planner's conditions (`rb_sce_iff`).
23. **Log-linearisation (made precise).** "Taking logarithms and total differentiation" is the
   derivative at `s = 0` along `X(s) = Xe^{sX̂}`. Each displayed linear equation is the
   vanishing of that derivative (`eq_14_27_loglin`, `rb_resource_loglin`, `rb_euler_loglin`,
   `eq_14_36_loglin`, `rb_riskfree_loglin`); `ln Y`, `ln w`, `ln R_k` are exactly affine along
   the curve (`rb_output_loglin`, `eq_14_37`, `rb_rental_loglin`). The steady-state ratios `Y/K`,
   `C/K` and `ζ` enter as parameters, with the steady-state Euler equation as a hypothesis where
   it is used. With the conditional expectation, (14.33) is derived for an abstract linear `E_t`
   (`CondExpSystem` of Chapter 2, `eq_14_33`).
24. **Saddle path (made precise).** The book argues from the phase diagram. Here: the eigenvalues
   satisfy `0 < λ₁ < 1 < λ₂` for all `0 < α < 1`, `0 < β < 1`, `ζ, Y/K, C/K > 0`
   (`rb_saddle_eigen`). In the deterministic case the bounded solution from `K̂₀` is unique and
   lies on the upward-sloping line `Ĉ = φK̂`, converging monotonically (`rb_saddle_det`). In the
   stochastic case, with `E_tẑ_{t+1} = ρẑ_t`, every `F₀`-measurable `K̂₀` and stable adapted `ẑ`
   give exactly one stable adapted solution (`rb_saddle_stoch`, via Chapter 2's `bkS_exists` and
   `bkS_unique`).
25. **Permanent TFP shock, p. 484.** The new steady state (`rb_permanent_ss`, `rb_ss_permanent`),
    the upward shift of both isoclines (`rb_permanent_shift`) and the monotone rise of capital and
    consumption with a positive interest rate and investment (`rb_permanent_path`) are proved.
    `rb_permanent_path` gives `Ĉ₀ = (1 − φ)ẑ/(1 − α)`, so its sign is ambiguous, as the book says.
    The wage rises when `Ĉ₀ ≥ 0` (labour-market comparative statics, `rb_labour_market`). The
    claims that hours rise, and the temporary-shock comparisons of impact sizes (pp. 484–485),
    rest on numerical solutions and are not formalised.
26. **Not formalised (computational/empirical):** the OLS estimation (14.29)–(14.30), Table 14.1,
    the business-cycle facts, and Figures 14.5–14.6.

### §14.3.1 Various utility functions

27. **"When `γ = 1`, (14.38) reduces to (14.22)", p. 489 (corrected).** (14.38) has no limit as
    `γ → 1` (at `c = 1`, `n = 0` it equals `1/(1 − γ)`; `rb_u38_printed_no_limit`). Subtracting
    the constant `1/(1 − γ)` gives the same preferences for each `γ`, and the result tends to
    `ln c + χ ln(1 − n)` (`rb_u38_limit`).
28. **Indivisible labour (derivation added).** The book only says (14.39) with `ν = 0` is the
    Hansen–Rogerson model. `rb_lottery` derives it: with employment lotteries, full insurance
    is optimal and expected utility is `ln c − BN` with `B = −χ ln(1 − n̄)/n̄ > 0`.
29. **Figures 14.7–14.8 intuition (partial).** The labour-market mechanism the book describes is
    proved as log-linear comparative statics at given `Ĉ`, `K̂`: a larger consumption response
    lowers hours and output and raises the wage (`rb_consumption_channel`), and the hours
    (wage) response to `ẑ` falls (rises) with `ν` (`rb_nu_responses`). The impulse-response
    rankings themselves are computational and not formalised.
30. **GHH, p. 490.** "No wealth effect or intertemporal substitution effect" is formalised as:
    the MRS is `G′(n)`, independent of `c` (`rb_ghh_mrs`), and labour-market equilibrium hours
    are unique when `G′` is monotone (`rb_ghh_hours`). That GHH lies outside the KPR class is
    shown by `G(n) = n²/2` (`rb_ghh_not_kpr`).
31. **Habit formation, p. 492.** The marginal-utility formula `Λ_t` is derived for finitely many
    successor states (`rb_habit_mu`). The recalibration and Figure 14.9 are computational and not
    formalised.

## §14.3.2–§14.3.4 and Exercises 14.3–14.7

### §14.3.3 and Exercise 14.5

32. **Exercise 14.5, decentralisation 3 (pp. 499–500)**. The book says the three
   decentralisations yield the planner's allocation. For the third (capital goods producers
   buy `(1 − δ)Kₜ`, sell `K_{t+1}`; profits rebated lump sum) this is false when `Φ_K ≠ 0`:
   the household's return on capital is `R_k + (1 − δ)Q` (`rx_dec3_euler`), so its Euler
   equation lacks the planner's term `Q_{t+1}Φ_K(I_{t+1}, K_{t+1})`; given it, the planner's
   (14.45) holds iff `Eₜ[Λ_{t+1}Q_{t+1}Φ_K] = 0` (`ex_14_5_dec3_iff`), and the two cannot both
   hold when `ΛQΦ_K > 0` at every successor (`ex_14_5_dec3_counterexample`). This happens for
   (14.43) whenever investment exceeds its steady-state rate (`rx_Phi_K_pos`; concretely
   `rx_phiQuad_K`). The statement is true when `Φ_K ≡ 0` (e.g. `Φ = vI`, CEE-type costs) and
   when the producers' profit `QΦ − I = QΦ_KK` (`rx_producer_profit`) is paid as a return on
   capital, `ρ = R_k + Q(1 − δ + Φ_K)` (`ex_14_5_dec3_corrected`). Decentralisations 1 and 2
   are correct (`ex_14_5_dec1`, `ex_14_5_dec2`, `ex_14_5_budgets`).
33. **Sign of `κ` in (14.43), p. 495.** With `ϕ″ < 0` everywhere, `κ = ϕ″(δ) < 0`
   (`rx_kappa_neg`), unlike `κ = S″(1) > 0` in (14.52); the linearised investment rate is
   `î − k̂ = −q̂/(κδ)` (`ex_14_6_invest_43_solved`), increasing in `q̂`. Also, `I/K = δ` in the
   steady state uses `Φ_I > 0` (`ϕ` strictly increasing) for uniqueness (`eq_14_43_steady`).
34. **Stock return, p. 499.** The second line of the displayed chain has `R_{k,t+1}` where
   `R_{k,t+1}K_{t+1}` is meant; the result is right (`rx_stock_return`).
35. **Proposition 14.3.1, p. 498.** The proof needs the transversality condition
   `Eₜ[M_{t,t+n}Q_{t+n}K_{t+n+1}] → 0` and the firm's labour condition `w = zF_N`, which the
   book does not state; `Pₜ` is the present value of future dividends, which satisfies the
   book's recursive definition (`rx_P_recursion`). `∂Pₜ/∂K_{t+1}` is read as the derivative of
   the ex-dividend value as a function of capital, defined through the firm's value function
   (`rx_firmValue`) for any positively homogeneous valuation (`proposition_14_3_1`,
   `proposition_14_3_1_marginal`).
36. **Derivations of the first-order conditions.** (14.45), (14.48)–(14.49), the household
   conditions and capacity-utilization conditions are proved as necessary conditions at a
   local maximum, by perturbing one variable at one node (`rx_node_foc`); with adjustment costs
   in (14.42) the investment changes are given by the inverse `G(·, K)` of `Φ(·, K)`, assumed
   differentiable (`rx_inverse_partials`, `rx_uzawa_euler`). (14.50)–(14.51) are proved as the
   stationarity of the firm's Lagrangian in `Iₜ` and `K_{t+1}` (`eq_14_50`, `eq_14_51`): with
   investment adjustment costs no one-node perturbation keeps the other constraints, so
   necessity is not proved.

### Setting

37. **Uncertainty.** `Eₜ` is the conditional expectation on an event tree with a finite shock
   set (`RXTree`); the book's normal shocks are not covered. The detrending identities of
   §14.3.4 are pointwise and hold for every realisation of `εₜ`.
38. **Log-linearisation (Exercise 14.6).** Each linearised equation is proved as the derivative
   at `ε = 0` of the equilibrium condition along the path `X = X̄e^{εx̂}` of all variables, at the
   steady state; risk neutrality makes the discount factor `β`.
39. **Steady state of the detrended system (p. 501).** Its existence is proved under
   `R = G/β − 1 + δ > 0` and `β ≤ 1` (which make consumption positive and `0 < N < 1`);
   the book does not state conditions (`rx_trend_steady_exists`).
