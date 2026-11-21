# Corrections and departures: Miao Chapter 13

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 13, Complete
Markets Exchange Economies, pp. 415–454. Lean names are relative to `Miao.CompleteMarkets`. Every
book item is located in the [source map](source-map.md).

## §§13.1–13.3 and Exercises 13.1–13.2

### §13.1

1. **Representation (convention).** With `s₀` given, a node `sᵗ` is the list `[s_t, …, s₁]`
   of later shocks (`List S`, newest first); the root is `[]`. Probabilities are a consistent
   family `POProb` (`Pr(sᵗ) = Σ_s Pr(sᵗ, s)`), of which the i.i.d. tree `po_iid` is an instance.
2. **Assumption 13.1.1, domain (departure).** The text does not give the domain. Since
   consumption lies in `L∞₊ ∋ 0`, `Assumption13_1_1` asks strict monotonicity, strict concavity
   and continuity on `[0, ∞)`, and `C²` and the Inada conditions on `(0, ∞)`
   (`assumption_13_1_1_sqrt`). Strict monotonicity on `[0, ∞)` is part of `POEconomy` and makes
   `Uⁱ` finite on `L∞₊` (`eq_13_1`). CRRA with `γ ≥ 1` is `−∞` at `0` and so is not covered by
   the economy (Example 13.3.1 is treated through marginal utilities, item 7).

### §13.2

3. **Proposition 13.2.1, hypotheses.** Proved as stated (`proposition_13_2_1`) with each `uⁱ`
   concave (for "only if") and continuous (for the book's transfer argument in "if") on
   `[0, ∞)`, and `I ≥ 1`; the book leaves these to Assumption 13.1.1.
4. **First-order conditions (13.3)–(13.4) (made precise).** They are derived for interior
   consumption, differentiable `uⁱ`, at nodes of positive probability, and with `λⁱ > 0`
   (`po_planner_foc`, `po_planner_foc_ratio`, `eq_13_3`, `eq_13_4`). At a node with
   `Pr(sᵗ) = 0` the planner is indifferent and the conditions need not hold.
5. **"`c¹_t` is a function of the aggregate endowment only" (proof replaced).** The book argues
   that (13.4) is one equation in `c¹_t`; the Lean proof shows directly that two nodes of positive
   probability with equal aggregate endowment give each agent equal consumption, using strictly
   decreasing marginal utilities (`po_risk_sharing`, `po_consumption_fn_aggregate`,
   `po_no_history_dependence`).

### §13.3

6. **(13.6)–(13.10) (made precise).** The Lagrangian argument is replaced by a perturbation along
   the budget line between `sᵗ` and `s₀` (`eq_13_6`); it needs interior consumption and
   differentiability, and gives `μᵢ = uⁱ'(cⁱ₀(s₀))` under `q⁰₀(s₀) = 1`. (13.8)–(13.10) hold at
   nodes of positive probability (`eq_13_8`, `eq_13_9`, `eq_13_10`). "The equilibrium allocation
   is Pareto optimal with `λᵢ = μᵢ⁻¹`" is proved as: it solves the planner's problem with these
   weights, for concave `uⁱ` (`po_AD_solves_planner`, `po_AD_shadow_price`).
7. **Example 13.3.1 (`γ = 1`).** `c^{1−γ}/(1−γ)` is undefined at `γ = 1`; its derivative is
   `c^{−γ}` for `γ ≠ 1` (`po_crra_hasDerivAt`). The risk-sharing formulas use only `u'(c) = c^{−γ}`
   and hold for every `γ > 0`, including log utility (`example_13_3_1`,
   `example_13_3_1_shares`).
8. **Negishi algorithm.** Step 4 ("iterate to convergence") is not formalised: the text claims
   no convergence. Proved: scale invariance (`po_negishi_scale`), `q⁰₀(s₀) = 1` iff
   `μ₁ = u¹'(c¹₀(s₀))` (`po_negishi_q0`), the direction of step 3 (`po_negishi_step3`) and that a
   stopping point is an equilibrium (`po_negishi_fixed_point`).
9. **Theorem 13.3.1.** Proved as stated under strict monotonicity only (`theorem_13_3_1`),
   with endowments in `L∞₊` so that their values are defined.
10. **Theorem 13.3.2 is false as printed (corrected).** With the economy's endowments a Pareto
    optimum need not be an equilibrium allocation at any prices: in `po_exampleEconomy`, giving
    agent `1` the whole endowment of agent `0` is Pareto optimal but agent `0` can always afford
    her endowment, which she prefers (`theorem_13_3_2_counterexample`). The corrected theorem
    (`theorem_13_3_2`) relocates the endowments to the allocation (equivalently, lump-sum
    transfers) and finds `q⁰ ∈ L¹` with `q⁰₀(s₀) = 1`.
11. **Theorem 13.3.2, hypotheses and proof (departure).** The book assumes continuity and strict
    concavity and outlines a Hahn–Banach/Yosida–Hewitt/Mackey-continuity proof that also needs a
    cheaper point. The Lean theorem assumes concavity on `[0, ∞)`, differentiability on `(0, ∞)`
    and uniformly interior consumption `cⁱ_t(sᵗ) ≥ δ > 0`; the planner weights of Proposition
    13.2.1 are all positive (`po_pareto_foc`), the planner's first-order conditions define the
    prices, which lie in `L¹` because marginal utility is bounded on `[δ, ∞)`, and concavity makes
    the first-order conditions sufficient. Strict concavity is not needed. The general
    commodity-space versions are the copied SLP Theorems 15.4 and 15.6.
12. **Asset pricing.** The book's `p₀(sᵗ)` on p. 423 is read as the date-`t` price at `sᵗ`
    (`po_assetPrice`), with the root case `po_assetPrice_root`; with (13.7) substituted it is the
    expected discounted marginal-rate-of-substitution formula (`po_assetPrice_eq`).

### Exercises

13. **Exercise 13.1 (departure).** The exercise starts from a Radner equilibrium with nonbinding
    debt constraints, zero asset supply and complete markets. Its allocation and prices are those
    of an Arrow–Debreu equilibrium (§13.5, outside this part), so `ex_13_1` starts from an
    interior Arrow–Debreu equilibrium with `q⁰₀(s₀) = 1` and concave, differentiable `uⁱ`. The
    weights are explicit, `λᵢ = uⁱ'(cⁱ₀(s₀))⁻¹ > 0`; `c` attains the supremum (13.37) at `ȳ`, and
    `ȳ` maximises `U_λ` on the representative agent's budget set.
14. **Exercise 13.2 (solution).** With a constant aggregate endowment `Y` and Assumption 13.1.1,
    interior Pareto optima are constant at nodes of positive probability, `cⁱ_t(sᵗ) = κᵢ`, with
    `Σᵢ κᵢ = Y` and `λⁱ uⁱ'(κᵢ)` equal across agents (`ex_13_2`); conversely every positive
    constant allocation summing to `Y` is Pareto optimal (`ex_13_2_converse`).

## §13.4–§13.5, Exercises 13.3, 13.4, 13.8

### §13.4

15. **Theorem 13.4.2 for borrowing constraints is false as printed.** The book claims that no
   one-period arbitrage on `R(Θ_BC)` at every node is equivalent to a positive state price process
   with (13.16). Since `R(Θ_BC) = {p_t · θ_t ≥ 0}` (`rd_rec_BC`), a one-period arbitrage there must
   cost exactly zero; if all securities pay nothing at some node there is none, yet (13.16) fails
   because prices are positive: one security with price `1` and payoff `0`
   (`theorem_13_4_2_BC_counterexample`). True: with positive prices, nonnegative payoffs and some
   nonzero payoff at every node (`theorem_13_4_2_BC`; the proof applies Stiemke's Lemma on
   `ker(p_t ·)` and shows the multiplier of `p_t` is positive). The debt-constraint case holds as
   printed (`theorem_13_4_2`), with `D̄ ≥ 0` (so that `0 ∈ Θ_DC`).
16. **Short sales (p. 430).** "One can show that (13.16) holds as an inequality (Huang (2002))":
   proved directly (`rd_SC_inequality`): with positive prices some `q⁰ ≫ 0` gives
   `q⁰_t p_t ≥ ∑ q⁰_{t+1} f_{t+1}`, and any such `q⁰` excludes one-period arbitrage on
   `R(Θ_SC) = {θ ≥ 0}`. With positive prices both facts are automatic (a nonnegative portfolio
   with nonpositive cost is zero). That (13.16) itself can fail is `rd_SC_no_statePrice`.
17. **The book's definition of complete markets is too weak** (pp. 430–431). It asks that every
   bounded `x` be the net cash flow of *some* strategy; with positive prices this always holds by
   rolling one security over, whatever the payoff matrix (`rd_completePrinted_of_pos`). Hence:
   * **Exercise 13.8** ("complete iff `D_{t+1}(sᵗ)` has rank `S`"): the "if" direction holds
     (`ex_13_8_printed_if`), the "only if" direction is false: two states and one riskless bond
     (`ex_13_8_counterexample`). True with completeness for finite-horizon payoffs replicated by
     strategies liquidated at the horizon (`rd_Complete`): complete iff rank `S` at every node
     (`ex_13_8`). (The text on p. 431 calls this "Exercise 7"; it is Exercise 8.)
   * **Theorem 13.4.3** is false with the printed definition: in the same economy there is no
     arbitrage on `R(Θ_DC)` and the state price processes from ratios `(1/2, 1/2)` and
     `(1/3, 2/3)` are not proportional (`theorem_13_4_3_counterexample`). With rank `S` at every
     node (the property the book's proof uses) it is true (`theorem_13_4_3`, uniqueness
     `rd_statePrice_unique`, the formula `theorem_13_4_3_formula`). For borrowing constraints the
     existence part needs the hypotheses of item 15 (`theorem_13_4_2_BC`).
18. **(13.21)** is printed with `T → 0`; it is `T → ∞` (`rd_TVC`).
19. **(13.23) does not follow from (13.21).** The book takes limits in (13.19) at a node `sᵗ`
   using the date-0 condition (13.21). The limit needs the transversality condition conditional
   on `sᵗ` (`eq_13_23` assumes it). Counterexample: in the economy of item 22 the plan of agent
   `true` satisfies (13.11) and (13.21) but (13.23) fails at the node `(false)`
   (`eq_13_23_counterexample`). The natural debt and borrowing limits (13.24) are proved under the
   conditional condition (`eq_13_24`, `rd_naturalDebt_nonbinding`, `rd_naturalBorrowing`).
20. **Readings.** At `t = 0` the goods-market condition of Definition 13.4.1 uses `f₀ := p₀`, as
   in (13.11b) (`rd_fz`). "`π ∈ L¹`" in Definition 13.4.2 is read as `q⁰ = π Pr ∈ L¹`
   (expected-value summability), which is what (13.22) needs. Condition (iii) of
   Definition 13.4.2 is stated as (13.16) for `q⁰ = π Pr`, equivalent to (13.18) (`eq_13_18`).
   "Strictly increasing `uⁱ`" in Theorem 13.4.1 is strict monotonicity of the utility functional
   on `L^∞₊` (`rd_StrictIncr`), which (13.1) has when `u` is strictly increasing (`rd_eq_13_1`); the
   proof consumes the arbitrage surplus truncated at `1` so that consumption stays bounded.
21. **Pareto optima are supported (pp. 433–434).** The step after the Second Welfare Theorem
   (which belongs to §13.3) is proved: an Arrow–Debreu equilibrium with positive prices in `L¹`,
   securities of rank `S` priced by (13.16) and `p ∈ (L^∞₊)ᴶ` is a competitive equilibrium with
   transversality condition (`rd_ad_cetvc`). The trading strategy is the replicating one
   (`rd_repl`); the bare definition of completeness would not give the transversality condition.

### §13.5

22. **Theorem 13.5.1 ("if") is false as printed.** The date-0 transversality condition allows an
   agent to hold a zero-cost position that is a bubble on one branch and a Ponzi scheme on another;
   its value is unbounded, so no bounded borrowing or debt limits admit it, while optimality and
   (13.21) are unaffected. Counterexample (`theorem_13_5_1_counterexample`): two equally likely
   states, `β = 1/2`, two agents with linear expected utility and endowment `1`, Arrow securities
   priced `1/4`, strategies `±ψ` with value `4ᵗ m(sᵗ)` for the martingale `rd_mg`; markets are
   complete and Assumption 13.5.1 holds. True (`theorem_13_5_1_if`): `(c, θ̃, p)` is a Radner
   equilibrium with nonbinding bounded borrowing constraints and with nonbinding bounded debt
   constraints, where `θ̃ⁱ` is the replicating strategy of `cⁱ − yⁱ`. The book's scaling
   argument is carried out in the Arrow–Debreu problem (ii) (`rd_impatience_bound`): scaling the
   given `θⁱ` on a subtree need not preserve (13.21), and "there exists an agent `i` with
   `p_t θⁱ_t > 0` at each node" is not needed. "Nonbinding" limits are read as bounded limits with
   strict inequalities (`rd_RadnerBCnb`, `rd_RadnerDCnb`), as Example 13.5.1 requires.
23. **Assumption 13.5.1 as printed is not satisfied by continuous discounted expected utility.**
   With `u = √·`, `β = 1/2`, `ȳ ≡ 1`, `κ = 1`, for every `α ∈ (0, 1)` the constant plan
   `(1 − √α)⁻²` is weakly preferred to the modified plan (`assumption_13_5_1_printed_fails`): the
   gain `√(c + κ) − √c` vanishes while the loss `(1 − √α)√c` grows. Corrected (as in Magill and
   Quinzii): the assumption for plans in `[0, ȳ]` (`rd_Assumption1351`), with `κ > 0`; continuous
   strictly increasing discounted expected utility satisfies it when `0 < m ≤ ȳ ≤ Y`
   (`assumption_13_5_1`). This is all the proof of Theorem 13.5.1 uses.
24. **Theorem 13.5.1 ("only if").** The book sketches a separation argument with Mackey continuity
    and cites Magill and Quinzii; this is not formalised. The statement is proved for (13.1)
    (`theorem_13_5_1_onlyIf`) with `uⁱ` strictly increasing, differentiable with `u′ > 0`, concave
    (gradient inequality `rd_GradIneq`, derived from `ConcaveOn` in `rd_gradIneq_of_concave`),
    consumption bounded away from zero, `p ∈ (L^∞₊)ᴶ`, and borrowing constraints: the Euler
    equations give `q⁰ = βᵗ Pr u′(c)/u′(c₀)` (common across agents by `rd_statePrice_unique`),
    bounded limits and clearing bound `p · θ`, which gives (13.21), and concavity gives
    optimality under (13.22). The debt-constraint version of "only if" is not formalised.
25. **Example 13.5.1.** `p_T θ¹_T = −∑_{s≥1} T²/(T+s)²` holds for `T ≥ 1`; at `T = 0`,
    `p₀ θ¹₀ = −∑_{t≥1} 1/t²` (`example_13_5_1_unlimited` is stated for `T ≥ 1`). The other formulas
    hold as printed. Utilities in the example are not of the form (13.1); Definition 13.4.2 is
    formalised for general utility functionals.

### Exercises

26. **Exercise 13.4.** The first-order conditions are proved necessary (at nodes with positive
    consumption) for borrowing constraints (`ex_13_4_BC_foc`, needs `p_t ≠ 0`), short-sales
    constraints (`ex_13_4_SC_foc`) and, when `D_{t+1}(sᵗ)` has rank `S`, debt constraints
    (`ex_13_4_DC_foc`); without rank `S` the debt case needs Farkas' lemma and is not formalised.
    Sufficiency of the first-order conditions with the transversality conditions is proved for all
    three (`ex_13_4_BC_suff`, `ex_13_4_SC_suff`, `ex_13_4_DC_suff`) and for equilibrium
    (`ex_13_4_BC_eqm`). (13.40) is printed as `p_T · θ_T + h̄_T`, a scalar plus a vector; it is
    read as `p_T · (θ_T + h̄_T)`, and nonnegative prices are assumed. Necessity of the
    transversality conditions is not formalised.

## §§13.6–13.8 and Exercises 13.5–13.7, 13.9–13.10

### §13.6 Asset price bubbles

27. **Bubble bounds, p. 440.** The book states `0 < b_t ≤ p_t`. The strict inequality is false:
   an asset priced at its fundamental value has `b_t = 0` (`eq_13_6_bubble_pos_counterexample`:
   zero price and dividends, `π = 1`). True: `0 ≤ b_t ≤ p_t` for `p, d ≥ 0`
   (`eq_13_6_bubble_bounds`). The fundamental value's series converges automatically for
   `p, d ≥ 0` (`bp_summable_dividends`).
28. **Theorem 13.6.1, last step of the proof.** "This contradicts agent `i`'s optimality" uses
   that, with complete markets, the Radner consumption plan is optimal among plans satisfying the
   Arrow–Debreu budget (13.22) (Definition 13.4.2(ii) / Theorem 13.5.1, §13.5) and that
   preferences are strictly increasing in date-0 consumption. These are hypotheses `hopt`,
   `hmono` of `theorem_13_6_1` rather than derived from Radner optimality (§13.5 is formalised
   separately). The theorem also assumes nonnegative prices, dividends, endowments and supplies
   (as for stocks), and reads `E ∑_{t=0}^T π_t ȳ_t < ∞` as convergence of `∑_t E[π_t ȳ_t]`.
   The conclusion holds at every node, not only the root (`bp_bubble_eq_zero_of_root`). All
   hypotheses are jointly satisfiable (`theorem_13_6_1_instance`).
29. **Example 13.6.1 needs `p_t > 0`.** If `p_t = 0` (no dividends) the original economy has no
   trade while `p̂ = η/π` permits trade, so the budget sets differ and optimality need not
   transfer. `example_13_6_1` assumes `p > 0` (true for the book's `p_t = (1/π_t)∑_{s>t}π_s d_s`
   with positive dividends). The borrowing limits may be any limits (in particular the natural
   ones, `bp_natLimit`, which depend only on `π` and `y` and are therefore the same for `p̂`).
30. **Example 13.6.2, "the transversality condition holds".** In the book's state-price form
   (13.21), `lim π_t p_t θⁱ_t = 0` fails (`π_t = 1`, `p_t θ¹_t` alternates between `−η/3` and
   `2η/3`; `example_13_6_2_tvc_21_fails`). What holds is each agent's transversality condition
   `lim βᵗ u'(cⁱ_t) p_t (θⁱ_t + 1) = 0`, the form (13.40) for short-sales constraints
   (`example_13_6_2_tvc`). The example also needs `β < 1` (implicit in the book).
31. **Consumption positivity.** In the deterministic economies the consumption set is
   `c_t > 0` (log and CRRA utility), and optimality is over plans whose discounted utility
   converges (`bp_detAdm`).

### §13.7 Recursive formulation

32. **Definition 13.7.1(ii)** requires market clearing at every state `(w, s)`. When budgets bind,
   clearing at `(w, s)` forces `∑ᵢ wⁱ = ∑_j (p_j(w, s) + d_j(s))` (`bp_rce_walras`), so clearing
   cannot be required at arbitrary wealth distributions. `BPRCE` imposes (ii) and (iii) on a
   state space `Ωs` invariant under `G` (in `definition_13_7_1_instance`, the distributions with
   aggregate wealth equal to the value of the tree).
33. **Typographical, p. 445.** The clearing conditions are written with `hⁱ` and `gⁱ` for the
   consumption and portfolio functions `cⁱ`, `θⁱ`; the law of motion is written `G(w, s, s)` for
   `G(w, s, s')`. Supplies are one share of each stock.

### §13.8 Asset pricing

34. **CAPM beta, p. 448.** The book defines `β_{jt} = Cov_t[R_{j,t+1}, M_{t+1}]/Var_t(M_{t+1})`.
   With `M = a + bR_m` this equals `Cov(R_j, R_m)/(b Var(R_m))`, and
   `E[R_j − R_f] = β_j E[R_m − R_f]` then holds only when `b = 1`. The book's gloss ("the
   regression coefficient of the asset return `j` on the market portfolio return") is the
   correct `β_j = Cov(R_j, R_m)/Var(R_m)` (`bp_capm`). Counterexample to the printed beta:
   `bp_capm_book_beta_counterexample` (two equally likely states, `R_m = (1, 3)`,
   `M = 9/8 − R_m/4`, `j = m`: the printed beta is `−4`).
35. **Equation (13.36), p. 450.** With `σ_{jc} = Cov(r_{j,t+1} − E_t r_{j,t+1}, ε_{t+1})` as defined,
   the correct premium is `E[r_j − r_f] + σ_j²/2 = γσ_c Cov(r_j, ε) = γ Cov(r_j, Δc)`: the factor
   `σ_c` is missing (`eq_13_36`). Counterexample to the printed formula:
   `eq_13_36_counterexample` (`γ = 1`, `σ_c = 1/2`, `Cov(r_j, ε) = 1`: premium `1/2`, not `1`).
36. **Lognormal setting.** Joint lognormality is used only through the Gaussian laws of `m`,
    `r_j` and `m + r_j` (`eq_13_34`); `σ_{jm} = Cov(r_j, m)` is then recovered from
    `Var(m + r_j)`. The Euler equations are hypotheses at a single node (homoskedastic case).

### Exercises

37. **Exercise 13.5, initial wealth.** The bracket `θⁱ_{−1}(q_0 + d_0 + η)` (in `θⁱ_t` and
    `sⁱ(η)`) counts `η` twice when `q_0` denotes the equilibrium price, which already contains
    `η/π_0 = η`. The correct date-0 wealth is `θⁱ_{−1}(q_0 + d_0) = θⁱ_{−1}(∑_{s≥0}π_s d_s + η)`
    (`bp_k5_wealth`, `bp_k5_value`).
38. **Exercise 13.5, "a continuum of equilibria indexed by `η ≥ 0`".** False for large `η`:
    zero supply and `θ_{−1} ≠ 0` force some `θⁱ_{−1} < 0`, and then `sⁱ(η) < 0` for large `η`,
    so `cⁱ = sⁱ(η)ȳ` is negative (`ex_13_5_share_counterexample`: two agents, endowments 1,
    `β = 1/2`, `γ = 2`, `d = 0`, `θ_{−1} = (1, −1)`, `η = 3`). True: for every `η ≥ 0` with
    `sⁱ(η) > 0` for all `i` and `q_t > 0` (which holds when `η > 0` or dividends are positive)
    the stated objects form an equilibrium with natural borrowing constraints (`ex_13_5`), and
    different `η` give different prices (`ex_13_5_continuum`). The hypothesis
    `θⁱ_{−1} ≠ 0` for some `i` is not needed. Finite present values `∑ π_t ȳ_t`, `∑ π_t d_t` are
    assumed. `γ ≠ 1` (CRRA as printed).
39. **Exercise 13.6, autarky.** The `q = 0` equilibrium (`ex_13_6_autarky`) assumes each
    endowment stream has convergent discounted utility.
40. **Exercise 13.7.** "Prove that the equilibrium price is given by `q = βPr`,
    `p^f = βd/(1 − β)`": we prove that these prices (and `p^f + b̃` with the perturbed limit)
    support the no-trade equilibrium and solve the Euler equations (`ex_13_7`,
    `ex_13_7_bubble`, `ex_13_7_prices`); uniqueness of the equilibrium price is not formalised.
    The utility is any `u` with a supergradient `u'(y + d) ≥ 0` at `y + d`.
41. **Exercise 13.9, "derive the CAPM".** With log utility `M = 1/R_w` (`ex_13_9_sdf`), which is
    not affine in `R_w` in general, so the CAPM in `R_w` is exact only when `1/R_w` is affine in
    `R_w` on the support, e.g. with two states (`ex_13_9_capm_two_states`); it fails with three
    (`ex_13_9_capm_counterexample`: `R_w = (1, 2, 4)`, an Arrow security, `E[R_j − R_f] = −5/7`
    versus `β_j E[R_w − R_f] = −26/49`). In general the log-utility CAPM is an approximation.
42. **Exercise 13.10.** Joint normality of consumption and returns is expressed by
    `R_j = a_j + κ_j C + e_j` with `e_j` independent of `C ~ N(μ, v)`; the first-order condition
    `E[e^{−αC}(R_j − R_f)] = 0` is a hypothesis (the static analogue of `bp_ccapm_euler`), and
    consumption equals `W_0 R_m`.
