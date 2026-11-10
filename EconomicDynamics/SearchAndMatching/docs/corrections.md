# Corrections and departures: Miao Chapter 18

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 18, Search and
Matching Models of Unemployment, pp. 587–614. Lean names are relative to `Miao.SearchAndMatching`.
Every book item is located in the [source map](source-map.md).

## Introduction and §18.1

1. **Matching function, p. 589.** The assumptions "increasing, concave, linearly homogeneous" are
   imposed on the open orthant `u, v > 0` (where the rates are defined), "increasing" is read as
   strictly increasing, and `M > 0` there is assumed (`DMMatchingFn`). Cobb–Douglas matching
   satisfies them (`dm_cdMatching`).
2. **`q′(θ) < 0` and `d ln q/d ln θ ∈ (−1, 0)`, p. 589.** These need differentiability of `M` in
   `u` (assumed at the point); they then follow from strict monotonicity and concavity alone
   (`dm_q_elasticity`, `dm_xi_mem`). Without differentiability the derivative claims are not
   meaningful; monotonicity of `q` and `θq(θ)` holds regardless (`dm_q_strictAntiOn`,
   `dm_jobFinding_strictMonoOn`).
3. **(18.11), pp. 590–591.** The book states only the first-order condition. `eq_18_11` proves
   that, with continuation values taken as given and positive total surplus, the FOC is
   necessary and sufficient for the constrained maximum of the Nash product (by weighted
   AM–GM).
4. **"`θ*` is the unique solution of (18.18)", p. 593.** Uniqueness holds (`dm_ss_unique`);
   existence needs `A > b` (and a condition at small `θ`, automatic for Cobb–Douglas). If
   `A ≤ b` there is no solution (`dm_ss_not_exists`); with Cobb–Douglas matching a solution
   exists iff `A > b` (`dm_cd_ss_existsUnique`). The comparative statics in `η` (p. 594) also
   use `A > b` (`dm_cs_eta`).
5. **`a₂₁ = uq(θ*)[1 − ξ(θ*)]` and "`a₂₁ > 0`", p. 595.** The sign is wrong: differentiating
   (18.21), `∂u_{t+1}/∂θ_t = −uq(θ*)(1 − ξ(θ*)) < 0` (`dm_a21`, `dm_a21_sign`). Since the system
   is lower triangular the saddle-point conclusion is unaffected.
6. **"`a₂₂ ∈ (−1, 1)`", p. 595.** Holds when `ρ ∈ (0, 1)` and the job-finding probability
   satisfies `0 < θ*q(θ*) ≤ 1`; these are made explicit (`dm_a22_mem`).
7. **Saddle point and "the solution for `θ_t` is a constant", p. 595.** Formalised for the
   linearised system: a solution with bounded `dθ` has `dθ_t = 0` for all `t` and `du_t → 0`
   (`dm_saddle_path`); the linearisation coefficient `a₁₁` is derived by implicit
   differentiation (`dm_lin_a11`). For the nonlinear system the constant path `θ_t = θ*` is
   shown to be an equilibrium for every `u₀ ∈ (0, 1)` (`dm_transition_isSearchEqm`); global
   uniqueness of the nonlinear equilibrium path is not claimed by the book's argument and is not
   formalised.
8. **"`u_t` falls until reaching the steady state", p. 595.** Since `u_t − u* = a₂₂ᵗ(u₀ − u*)`
   (`dm_uPath_sub`), monotone decline needs `a₂₂ = 1 − ρ − θ*q(θ*) ≥ 0`
   (`dm_uPath_strictAnti` for `a₂₂ ∈ (0, 1)`). Counterexample: a Cobb–Douglas economy
   satisfying the book's condition `1 − ρ − ηθ*q/ξ > 0` with `a₂₂ = −1/4`, where unemployment
   overshoots, `u₁ < u* < u₀` and `u₁ < u₂` (`dm_transition_not_monotone`). Convergence holds in
   all cases (`dm_uPath_tendsto`).
9. **Large firm's problem, p. 597.** Optimality is defined against plans that differ in finitely
   many periods (`dm_FirmOptimal`), so the infinite sums need not converge. The book derives the
   FOCs (18.23) by a Lagrangian; `dm_firm_euler` proves directly that an optimal plan with
   positive vacancies satisfies (18.8) (perturbation and Fermat's theorem), and
   `dm_firmOptimal_of_euler` proves the converse. The envelope argument (18.24) is formalised for
   affine continuation values (`eq_18_24`), which is the case in equilibrium.
10. **Planner's FOC for `N_t`, p. 599.** The printed condition has
    `μ_t(1 − ρ)[1 − q(θ_t)θ_t + (q(θ_t)θ_t)′θ_t]`; the derivative of the Lagrangian is
    `μ_t[1 − ρ − q(θ_t)θ_t + (q(θ_t)θ_t)′θ_t]` (`dm_planner_foc_N`). The two differ by
    `μ_tρθ_tq(θ_t)ξ(θ_t) > 0` (`dm_planner_foc_N_misprint`); only the corrected condition yields
    (18.28) (`eq_18_28`).
11. **Efficiency, p. 599.** "Efficient" is formalised as "satisfies the planner's steady-state
    first-order condition (18.28)" (`dm_hosios`); second-order conditions are not discussed by
    the book. With Cobb–Douglas matching the book's "when" is strengthened to "iff"
    (`dm_cd_hosios_iff`), with the direction of the inefficiency (`dm_cd_hosios_compare`).
12. **"If and only if `ξ(θ) = β`", p. 599.** Misprint for `ξ(θ) = η`. Counterexample: a
    Cobb–Douglas economy with `ξ = α = β = 1/2 ≠ η = 1/4` in which the equilibrium and efficient
    market tightness differ (`dm_hosios_misprint`).
13. **Exercise 18.1.** The open-ended exercise is formalised as: households with linear utility
    trade shares (pricing equation, its converse, and price = present value of dividends under
    `βᵀp_T → 0`); large firms own capital (investment Euler equation, job creation, wage with
    `A` replaced by `F_N`); a definition of search equilibrium; and the steady-state analysis
    for `F = AK^aN^{1−a}`: the capital–labour ratio is pinned down by the modified golden rule
    and the labour-market block is the basic DMP model with `A_eff = (1 − a)Ak*^a`
    (`dm_ex1_steady`), with existence in an example (`dm_ex1_searchEqm_exists`). The wage
    equation is obtained by the derivation of (18.15) with the period-`t` marginal product in
    place of `A` (`dm_ex1_wage`), as in the large-firm bargaining of (18.26).
14. **Exercise 18.2.** The planner's state is the stock of matches before the idiosyncratic draw;
    the distribution `G` enters only through `P = 1 − G`, `H(z) = ∫_z^∞ x dG` and the density
    relation `H′(z) = zP′(z)` (satisfied by the exponential distribution with mean 1,
    `dm_mp_exp_dist`). The decentralised conditions (18.44)–(18.45) of §18.2 enter
    `ex_18_2_efficiency` as hypotheses (stated with this module's own names, not the §18.2
    theorem names). Result: the decentralised steady state satisfies the planner's conditions iff
    `ξ(θ) = η`.

## §§18.2–18.3, Exercises 18.3–18.5

### §18.2 Endogenous job destruction

15. **Timing in (18.41)–(18.42), p. 603.** The book writes the integrals as
   `∫_{z*_t}^∞ (z_{t+1} − z*_t) dG`. Substituting `J^F_{t+1}(z) = (1 − η) A (z − z*_{t+1})`
   (`jd_JF_linear`) into (18.31) gives the reservation productivity of period `t + 1`:
   `κ / q(θ_t) = β (1 − η) A Φ(z*_{t+1})` (`eq_18_41`) and
   `η θ_t κ = (1 − η)(A z*_t − b) + β (1 − ρˣ)(1 − η) A Φ(z*_{t+1})` (`eq_18_42`). The two
   versions agree along constant paths, so the steady state (18.44)–(18.45) is unaffected.
16. **"These equilibrium values are constant over time" (p. 603) and "the steady state is a
   saddle point" (p. 607).** With the printed timing, constancy is immediate; with the correct
   timing, `(θ_t, z*_t)` is a forward-looking system and constancy is the saddle-path selection.
   Proved for the linearised system: `dz_t = ψ dz_{t+1}` with
   `ψ = β (1 − G(z̄*))((1 − ρˣ) − η q θ / ξ)` (`jd_linear_psi`); if `|ψ| < 1` (e.g. under the
   analogue of the §18.1 condition, `(1 − ρˣ) − η q θ / ξ ≥ 0`, `jd_psi_abs_lt_one`) the only
   bounded solution has `dz ≡ dθ ≡ 0`, and unemployment converges (`jd_saddle`). The book states
   no condition; the nonlinear (global) selection is not claimed.
17. **Existence and uniqueness of `(θ*, z̄*)` (p. 604, Figure 18.5).** The book reads them off the
   figure. Uniqueness holds whenever `q` is strictly decreasing (`jd_steady_state_unique`).
   Existence needs hypotheses the book leaves implicit: `q` positive and continuous on `(0, ∞)`,
   `q(θ) → ∞` as `θ ↓ 0`, and `G(b/A) < 1` (some match is worth more than the benefit `b`); if
   `b ≥ A z` for all `z` in the support, `Φ(b/A) = 0` and no steady state with `θ > 0` exists
   (`jd_steady_state_exists`, `jd_steady_state_existsUnique`; instance `jd_example_steady_state`).
18. **Comparative statics in `A` with fixed `κ` (pp. 604–605).** "The net effect is to raise the
   market tightness" is proved for `b ≥ 0` (`jd_compstat_A_theta`); with `b < 0` the argument
   fails. With posting cost `κ A`, "an increase in `A` reduces the reservation productivity" needs
   `b > 0`: with `b = 0`, `A` cancels from both conditions and nothing moves
   (`jd_compstat_kappaA`, hypothesis `0 < b`).
19. **The job destruction rate falls (p. 607).** It falls weakly: `G(z̄*′) ≤ G(z̄*)`
   (`jd_compstat_kappaA_jd`), strictly only if `G` puts mass on `(z̄*′, z̄*]`. The book's "the
   steady-state effect … is to reduce the job creation and job destruction rates" is therefore
   weak for these two rates (they are equal in a steady state, `jd_jc_eq_jd_of_steady`);
   unemployment falls strictly (`jd_compstat_kappaA_u`, given `θ q(θ)` strictly increasing).
20. **Beveridge curve convexity (p. 604)** is the §18.1 claim (agent DM) and is not repeated;
   downward slope is `jd_beveridge_downward`.

### §18.3 Unemployment and business cycles

21. **`V_n(w, t)` (p. 610).** The budget printed for the problem with `N_t + ε` members is
   `C_t + I_t = D_t + R_kt K_t + w_t N_t + w ε + b (1 − N_t) − T_t`, i.e. the new member keeps the
   benefit `b`. Then `∂V_t(K_t, N_t + ε)/∂ε|_{ε=0} = Λ_t (w − w_t) + ∂V_t/∂N_t + Λ_t b`, and the
   book's second equality fails whenever `Λ_t b ≠ 0` (`jd_hh_Vn_book_budget`). The book's first
   line `−χ N^φ + Λ_t w + …` is consistent with that budget but omits `−Λ_t b` relative to
   `∂V_t/∂N_t`. With the benefit forgone (`b (1 − N_t − ε)`), `V_n = Λ_t (w − w_t) + ∂V_t/∂N_t`
   holds (`jd_hh_Vn`), which is what the Nash bargain (18.56) uses.
22. **Expectations.** The aggregate shock is a Markov chain; at a node the next-period states are
   finite (`E_t X = ∑ s, p s * X s`), so differentiation under the expectation is exact.
   Value functions are given functions with the maximising property as a hypothesis; first-order
   and envelope conditions are proved from differentiability (`jd_foc`, `jd_envelope`), and the
   next-period envelope relations enter as hypotheses (they are `jd_hh_envelope_K`,
   `jd_hh_envelope_N`, `eq_18_53`/`eq_18_54` applied at `t + 1`).
23. **"`K^j/N^j` does not depend on `j`" (p. 611)** needs `k ↦ F₁(k, 1)` injective (e.g. strictly
   concave `F`), besides constant returns (`jd_capital_ratio_indep`).
24. **Steady state, log-linearisation, simulation of §18.3.** The text derives none of them (the
    Shimer-puzzle discussion is in the chapter introduction, not in §18.3); the steady-state
    relations used for calibration are proved under Exercise 18.5.

### Exercises

25. **Exercise 18.3.** "Mean-preserving spread" is used in the Rothschild–Stiglitz integral form
    `Φ_G ≤ Φ_{G′}` with equal means (a concrete spread: `jd_mps_example`). Tightness rises weakly
    (strictly if `Φ` rises at `z̄*`) (`ex_18_3_theta`); the effect on `z̄*` has the sign of
    `H(θ′) − H(θ)`, `H(θ) = η θ κ − (1 − ρˣ) κ / q(θ)` (`ex_18_3_reservation`), which is
    ambiguous in general (`H` is not monotone, e.g. for Cobb–Douglas `q`); `z̄*` rises when `H` is
    nondecreasing (`ex_18_3_reservation_mono`). Unemployment falls when the separation rate does
    not rise (`ex_18_3_unemployment`); otherwise the effect is ambiguous.
26. **Exercise 18.4** (planner for §18.3). With the benefit `b` a pure transfer (financed by
    lump-sum taxes), efficiency requires `b = 0` as well as the Hosios condition `η = ξ`
    (`ex_18_4_gap`, `ex_18_4_hosios`). Node by node the job creation conditions coincide only if
    `ξ` is the same at `t` and `t + 1` (constant elasticity, e.g. Cobb–Douglas matching), since
    `S^F_{t+1} = (1 − ξ_{t+1}) S^P_{t+1}` while the planner divides by `1 − ξ_t`;
    `ex_18_4_hosios` takes `η = ξ` at all nodes.
27. **Exercise numbering.** The task list described item 18 as the planner's problem for §18.2;
    in the text item 18 is the planner's problem for §18.3 (item 16 is the one for §18.2), and item
    4 is what is formalised (`ex_18_4_*`).
