# Corrections and departures: Miao Chapter 16

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 16, Overlapping
Generations Models, pp. 529–557. Lean names are relative to `Miao.OverlappingGenerations`. Every
book item is located in the [source map](source-map.md).

## Introduction and §16.1

### Setting (pp. 530–532)

1. **Preferences.** `u'' < 0` is used only through its consequence that `u'` is strictly
   decreasing; `OXPrefs` assumes `u'` strictly decreasing and continuous on `(0, ∞)` (both follow
   from a continuous `u'' < 0`). Utility lives on `(0, ∞)`: all allocations, including the
   alternatives in the Pareto comparisons, have positive consumption. The second derivative
   appears explicitly only in the offer-curve slope theorems (`OXPrefs.ox_offer_slope_m` and
   the following), as `HasDerivAt u' u''`.
2. **The value of money.** Prices are represented by the value of money `q_t = 1/p_t ≥ 0`, so
   that the book's `p_t = ∞` is `q_t = 0` (`OXEconomy.eq_16_1_16_2` gives the price form).
3. **The initial old's budget, p. 531.** Printed `c₁⁰ ≤ y₂ + m₀⁰/p₁ + …`; the endowment is `e₂`
   (`OXEconomy.ox_oldBudget`).
4. **Money holdings in the nonmonetary equilibrium, p. 531.** The book says no one holds money,
   `m_t^t = 0`, which violates `M_t = N_tm_t^t`. When money has no value holdings are
   indeterminate; we let the young hold the stock, `m_t^t = M_t/N_t`
   (`OXEconomy.ox_autarky_isEquilibrium`). The allocation, autarky, is the same, and it is the only
   nonmonetary equilibrium allocation (`OXEconomy.ox_nonmonetary_autarky`).

### The special case (pp. 532–536)

5. **The offer-curve slopes, p. 533.** The derivation assumes a differentiable saving function
   `m(R)` solving the Euler equation near `R`; the theorems are stated under that hypothesis (no
   implicit-function theorem is invoked): `OXPrefs.ox_offer_slope_m`, `OXPrefs.ox_offer_slope_z`.
6. **"A monetary steady state is unstable iff `|dm_{t+1}/dm_t| > 1`", p. 534.** False as an
   equivalence at `|f'| = 1`: `f(x) = x + x³` has `f'(0) = 1` and an unstable fixed point
   (`ox_unstable_counterexample`). True: `|f'| > 1` implies instability (`ox_fixed_unstable`),
   `|f'| < 1` implies local stability (`ox_fixed_stable`).
7. **Figures 16.2–16.4.** The general equilibrium map is only implicitly defined (it is
   multivalued when the offer curve bends backward). The claims are proved conditionally on a map
   `f` describing the equilibrium relation (`OXEconomy.ox_indeterminacy`) or on given cycle points
   (`OXEconomy.ox_two_cycle`), and the convergence claims of Figure 16.2 are proved for the
   logarithmic economy of Example 16.1.1 (`OXEconomy.example_16_1_1_left`,
   `OXEconomy.example_16_1_1_right`). No concrete economy with a backward-bending offer curve,
   a locally stable monetary steady state or a two-cycle is constructed.

### Examples

8. **Example 16.1.1, p. 536.** The general solution `p_t = 2M/(e₁ − e₂) + c(e₁/e₂)ᵗ` is an
   equilibrium only for `c ≥ 0`; for `c < 0` the price level becomes negative (real balances
   leave `(0, e₁)`). The book discusses `c = 0` and `c > 0` only. Proved: every monetary equilibrium
   has `c ≥ 0` (`OXEconomy.example_16_1_1_general`), every `c ≥ 0` is one
   (`OXEconomy.example_16_1_1_construct`), a path to the right of `m*` leaves `(0, e₁)`
   (`OXEconomy.example_16_1_1_right`).
9. **Example 16.1.2, p. 537, money supply.** "The initial old has no endowment of … money" yet
   "the monetary authority supplies money `M = 0.5 − ε`, `t ≥ 1`": in the model of §16.1
   (`M_t = g_mM_{t−1}`) this is impossible with `M₀ = 0`. We formalise the equivalent economy in
   which the initial old hold `M₀ = 0.5 − ε` and `g_m = 1`; the initial old's consumption
   `ε + (0.5 − ε) = 0.5` is the book's (`OXEconomy.example_16_1_2_high`).
10. **Example 16.1.2, p. 537, the low-interest-rate equilibrium.** With `p₁ = 1` and
    `p_t/p_{t+1} = R_aut` money is valued, so this price system cannot support autarky as an
    equilibrium: the initial old would consume `0.5 ≠ ε`, and by (16.6) every monetary equilibrium
    has `R_{t+1} > R_aut` (`OXEconomy.example_16_1_2_not_monetary`). What is true
    (`OXEconomy.example_16_1_2_low`): at those prices every generation's optimal choice is autarky
    with zero money demand, prices explode, autarky with valueless money (`p_t = ∞`) is an
    equilibrium, the present value of the endowment is infinite, and autarky is not Pareto
    optimal.

### Propositions

11. **Proposition 16.1.1, necessity, p. 538.** In the case `R_autg_m = g_n` the book takes limits
    in (16.6)–(16.7) "if this limit is finite". The limit `m̂_∞ ≤ e₁` is always finite; what the
    argument needs is `m̂_∞ < e₁`, so that `u'` is continuous at `e₁ − m̂_∞` (the case `m̂_∞ = e₁`
    is excluded by the Inada condition, which the book does not invoke). The limit step is proved
    for `0 < m̂_∞ < e₁` (`OXEconomy.proposition_16_1_1_limit`); the necessity theorem
    (`OXEconomy.proposition_16_1_1_necessity`) uses a limit-free argument covering both cases:
    `m̂_t ≥ m̂₁` gives `R_{t+1} ≥ u'(e₁ − m̂₁)/(βu'(e₂)) > R_aut`, so `m̂_t` grows geometrically.
12. **Proposition 16.1.1, sufficiency, p. 538.** "There exists a unique solution `m̂ > 0`": the
    solution is unique in `(0, e₁)` and its existence uses continuity of `u'` and the Inada
    condition (`OXEconomy.proposition_16_1_1_root`).
13. **Proposition 16.1.2, sufficiency, pp. 539–540.** The book argues from the first date at which
    `C̃` differs from autarky and represents the indifference curve as in (16.11) with an
    increasing `f`. The proof here works with all `ε_t = e₁ − c̃_t^t` at once: (16.9) and the
    initial old give `ε₁ ≥ 0`; the tangent inequality gives `g_nε_{t+1} ≥ R_autε_t`, strictly for
    `ε_t ≠ 0` (`OXEconomy.eq_16_11`, the content of `f(ε) > 0`), so `ε_t` is nonnegative and
    nondecreasing (`OXEconomy.eq_16_10`); a uniform chord bound (`OXPrefs.ox_chord`,
    `OXEconomy.ox_eps_geometric`) replaces `f(ε_{t+j}) ≥ f(ε_{t+1})`. The proof is for any
    feasible stationary allocation (`OXEconomy.ox_stationary_optimal`). In the book's display
    `ε_{t+2} ≡ y₁ − c̃_{t+2}^{t+2} = (c̃_{t+2}^{t+1} − y₂)/g_n`, `y₁, y₂` are `e₁, e₂`.
14. **Proposition 16.1.3, p. 541.** The hypothesis `R_autg_m < g_n` only guarantees that the
    stationary monetary equilibrium exists (Proposition 16.1.1); the theorem is stated for every
    monetary equilibrium with a stationary allocation (`OXEconomy.proposition_16_1_3`). The
    necessity half is proved by the `ε`-transfer of Proposition 16.1.2
    (`OXEconomy.ox_stationary_not_optimal`) rather than by the revealed-preference argument of
    Figure 16.5, which needs a maximiser of utility on (16.12); the book's two steps (the budget
    line is flatter; the initial old gain) are `OXEconomy.proposition_16_1_3_steps`.
15. **Balasko–Shell, pp. 542–544.** The general criterion is cited by the book and not
    formalised. Formalised: the equivalence of its two forms (`OXEconomy.ox_balasko_shell_equiv`;
    "`= +∞`" for positive terms is failure of summability), the compensating transfers
    (`OXEconomy.ox_balasko_shell_transfers`) and the criterion for stationary allocations with
    `g_n = 1` (`OXEconomy.ox_balasko_shell_stationary`).

### Exercises

16. **Exercise 16.1(b).** A monetary equilibrium exists only if `e₂ < g_ne₁`; with only `e₁ > e₂`
    assumed this fails when `g_n ≤ e₂/e₁`, and then autarky is the only equilibrium and is Pareto
    optimal (`OXEconomy.ex_16_1_b_exists`, `OXEconomy.ex_16_1_b_autarky`). The ranking holds for
    any preferences with `g_m = 1` (`OXEconomy.ex_16_1_b_rank`).
17. **Exercise 16.2.** Formalised with constant population (`g_n = 1`), per capita: with
    `g_n ≠ 1` the dividend per young agent varies over time and the equilibria have no closed form.
    The initial old consume their resources (`OXPrefs.ox_TreeEquilibrium`). Part (a) is proved for
    any preferences (`OXPrefs.ex_16_2_a`); part (b) for those of Exercise 16.1
    (`OXPrefs.ex_16_2_b_exists`, `OXPrefs.ex_16_2_b_unique`).

## §16.2–§16.3 and Exercises 16.3–16.9

### §16.2 Production economies

18. **Assumptions (made explicit).** The technology is used through `f` strictly concave on
   `[0, ∞)`, `f(0) = 0`, differentiable on `(0, ∞)` with `f′ > 0` and `f′(∞) = 0`; `f′(0) = ∞`
   only where needed (`op_golden_rule_exists`). The saving function is any `s(w, R)` with
   `0 < s < w`, continuous and nondecreasing in `R > 1` and strictly increasing in `w`; its
   existence from the Euler equation needs a continuous strictly decreasing `u′ > 0` with
   `u′(0+) = ∞`, which the text leaves implicit (`op_saving_exists`, `op_saving_unique`).
19. **`0 < s_w < 1` (departure in form).** Proved without differentiability as strict
   monotonicity of both `s` and `w − s` in `w` (`op_saving_wage_mono`), and for a differentiable
   saving function as `s_w = u″(c_y)/(u″(c_y) + βR²u″(c_o)) ∈ (0, 1)` (`op_saving_sw`).
20. **`G` without the implicit function theorem (departure).** The book invokes the implicit
   function theorem under `s_R > 0`. The existence and uniqueness of `k_{t+1} = G(k_t)` is proved
   directly by the intermediate value theorem and monotonicity under the weaker `s_R ≥ 0`
   (`op_temporary_eqm`, `op_G_exists`); monotonicity of `G` needs no derivatives
   (`op_G_strictMono`). The slope formula is proved by implicit differentiation for a
   differentiable `G` (`op_G_slope`). `G(0) = 0` is the limit `G(0+) = 0` (`op_G_tendsto_zero`),
   since `R(0) = ∞`.
21. **The limit `G(k)/k → 0`, p. 546 (misprint).** The text writes
   `lim gnG(k)/k ≤ lim f(k_t)/k_t − f(k_t) = 0`; the bound is `w(k)/k = f(k)/k − f′(k)`
   (`op_wage_div_eq`), which tends to `0` (`op_f_div_tendsto_zero`,
   `op_wage_div_tendsto_zero`, `op_G_div_tendsto_zero`).
22. **"If `G′(0) > 1`, then an odd number of positive steady states exist" (false).** True: at
   least one positive steady state exists (`op_exists_fixed`, with `op_above_diag_of_deriv`).
   The parity claim fails at tangencies: `opOddG` is continuous, strictly increasing,
   `G(0) = 0`, `G′(0) = 2`, `G(k)/k → 0` (`op_oddG_props`) and has exactly the two positive
   steady states `4, 9` (`op_oddG_fixed`, `op_odd_counterexample`).
23. **"If `G′(0) < 1`, then an even number of positive steady states exist" (false).**
   `opEvenG` has the same properties with `G′(0) = 1/2` (`op_evenG_props`) and exactly one
   positive steady state, `9` (`op_evenG_fixed`, `op_even_counterexample`). The "possibly zero"
   case occurs in a Diamond economy: Exercise 16.5(b) with small `A` (`ex_16_5_b_none`).
24. **The Diamond conditions, p. 549 (misprint in (ii)).** As printed, (ii) `G′(0) < 1` with (iii)
   `G′(k*) < 1` at positive steady states admits no positive steady state at all
   (`op_diamond_conditions_printed`), so there would be no `k_D`; and §16.3 uses
   "`db/dk(0) > 0`", which corresponds to `G′(0) > 1`. With (ii) read as `G′(0) > 1` (as `G > id`
   near `0`), plus `G < id` for large `k` and (iii) at every positive steady state, there is
   exactly one positive steady state (`op_diamond_conditions`); for increasing `G` it is globally
   stable (`op_fixed_signs`, `op_global_convergence`). The stability condition `G′(k*) < 1` is
   proved as local asymptotic stability for `|G′(k*)| < 1` (`op_local_stability`).
25. **`s_R < 0`, Figure 16.9 (not formalised).** The possibility of multiple `k_{t+1}` is an
   illustration with no specific economy (with CRRA and Cobb–Douglas `k_{t+1}` is unique).
26. **The planner's first-order conditions, p. 551 (corrected).** The cohort-`1` young consumption
   `c_y` enters both constraints, so stationarity of the Lagrangian (`op_planner_lagrangian`)
   gives `u′(c_y)/(βu′(c_o)) = g_n(1 + θ/µ)` and `f′(k) = g_n − 1 + g_nθ/µ ≥ g_n − 1`
   (`op_planner_foc`), not the printed `= g_n` and `g_n − 1 + θ/µ`; with `θ > 0` the printed
   equalities fail (`op_planner_foc_printed`). The conclusions `f′(k) ≥ g_n − 1` and, for
   `λ₀ = 0`, `θ = 0` and the golden rule hold (`op_planner_golden_rule`).
27. **Pareto optimality of steady states, p. 551 (partly formalised).** The general
    Cass–Balasko–Shell theorem is cited, not proved, in the text and is not formalised. Its
    steady-state form: the sum diverges iff `R ≥ g_n` iff `k* ≤ k_G` (`op_cass_steady_state`,
    `op_cass_corollary`). Pareto optimality is proved directly for `k* < k_G` (for a
    competitive steady state: `u` concave increasing, the Euler equation, `f` concave;
    `op_pareto_optimal_of_lt_golden`), and its failure for `k* > k_G` by an explicit improvement
    that makes every generation strictly better off (`op_dynamic_inefficiency`). The golden-rule
    case `k* = k_G` is not formalised. Allocations are indexed from the book's `t = 1` as `0`
    (`OPFeasible`, `OPParetoDominates`).

### §16.3 Asset price bubbles

28. **Bubbly steady state, p. 552 (misprint).** "`g_b(b + k)`" is `g_n(b + k)`
    (`op_bubbly_steady`).
29. **The slope of the `Δk = 0` locus, p. 553 (corrected).** At a zero of the locus,
    `db/dk = (−s_wkf″ + s_Rf″ − g_n)/R(k)` (`op_kLocus_hasDerivAt`), not over `R²(k)`; the two
    differ whenever the numerator is nonzero (`op_kLocus_slope_printed`). At `k = 0` the formula
    has no meaning (`R(0) = ∞`); "`db/dk(0) > 0`" is proved as: the locus is positive where
    `G(k) > k` (so on `(0, k_D)`) and negative where `G(k) < k` (`op_kLocus_pos`,
    `op_kLocus_neg`). `db/dk(k_D) < 0` follows from (i) and (iii) (`op_kLocus_slope_neg`).
30. **Vector field of `k`, p. 554 (hypothesis made explicit).** The middle step replaces
    `R(k_{t+1})` by `R(k_t)`; the equivalence holds when `s_R ≥ 0` (Diamond condition (i)),
    which `op_k_increase_iff`, `op_k_decrease_iff`, `op_k_stationary_iff` assume.
31. **Existence of a bubbly steady state, p. 554.** Proved as an equivalence under `s_R ≥ 0` and
    the (corrected) Diamond configuration of `G` (`op_bubbly_exists_iff`).
32. **Saddle path, p. 555 (partly formalised).** The saddle property and the unique `b₁` on the
    stable path are proved for the linearised system (`ex_16_9_roots`, `ex_16_9_saddle`). The
    nonlinear saddle path and the convergence of paths with `b₁ < b(k₁)` to `k_D` are not
    formalised.

### Exercises

33. **Exercise 16.3.** The saving function is proved optimal (`ex_16_3_optimal`) and its
    monotonicity is stated for `γ < 1`, `γ > 1` and `γ = 1` separately (`ex_16_3_mono_lt`,
    `ex_16_3_anti_gt`, `ex_16_3_gamma_one`). The law of motion is implicit in `k_{t+1}`
    (`ex_16_3_law`).
34. **Exercise 16.5 (departure at `σ = 1`).** The printed CES formula is undefined at `σ = 1`
    (exponent `σ/(σ − 1)`); `σ = 1` is treated as the Cobb–Douglas limit `Ak^a`
    (`ex_16_5_a_cobbDouglas`); `σ > 1` is `ex_16_5_a`. For `σ < 1`, "`A` sufficiently small" is
    the explicit `βAM < (1 + β)g_n` (`ex_16_5_b_none`), with global convergence to `0`
    (`ex_16_5_b_collapse`); for large `A` there are at least two positive steady states
    (`ex_16_5_b_two`). The stability of these steady states and the bound "at most two" are not
    formalised.
35. **Exercise 16.7.** The law of motion assumes `w_t > G_t` along the path. The permanent
    increase is analysed on the stable branch, where the slope of the law is at most one
    (`ex_16_7_b`); permanent and temporary increases are covered by the path comparison
    `ex_16_7_bc_path`. The requested drawings are not formalised.
36. **Exercise 16.8.** (a)(iii) is proved at given prices (lifetime wealth and utility fall with
    `d` iff `R > g_n`, `ex_16_8_a_iii`), together with the steady-state resource trade-off
    (`ex_16_8_a_iii_resources`) and the fall in capital (`ex_16_8_a_ii`); the full
    general-equilibrium welfare derivative is not formalised. (b): neutrality holds when private
    saving may be negative (`d > βw/(1 + β)`), which the text does not discuss (`ex_16_8_b`).
37. **Exercise 16.9 (departure in method).** The linearisation is taken as the total differential
    of the two equilibrium equations with given partials `s_w`, `s_R` and `f″(k_G)`
    (`ex_16_9_linearization`), and the roots are located with Chapter 1's 2×2 saddle toolkit
    (`ex_16_9_roots`, `ex_16_9_saddle`).
