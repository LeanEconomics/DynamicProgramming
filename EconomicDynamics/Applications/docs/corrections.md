# Corrections and departures: Miao Chapter 8

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 8,
Applications, pp. 231–290. Lean names are relative to `Miao.Applications`. Every book
item is located in the [source map](source-map.md).

## §8.1, §8.2, §8.4 and Exercises 8.1–8.2

### §8.1 Option exercise

1. **"`z* > I`", p. 233,** holds iff `F` puts positive mass above `I`
   (`od_option_threshold_gt_iff`). In general `z* ≥ I`; with every payoff at `0` (`F = δ₀`) the
   continuation value is `0` and `z* = I` (`od_option_threshold_dirac`).
2. **"A unique solution in `(0, B)`", p. 233.** The threshold equation has exactly one root, and
   it lies in `[I, B)` (`od_option_threshold_root_unique`); it lies in `(0, B)` when `I > 0`. With
   `I = 0` and `F = δ₀` the root is `0` (`od_option_threshold_dirac`).
3. **Mean waiting time, p. 233.** With `Pr(N = j) = (1 − λ)λʲ`, `j = 0, 1, …` (as printed,
   `od_wait_prob`), `E[N] = λ/(1 − λ)` (`od_wait_mean`), never the printed `1/(1 − λ)`
   (`od_wait_mean_misprint`). `1/(1 − λ)` is the mean number of draws `N + 1` until investment
   (`od_wait_mean_dates`). The monotonicity claim holds for both (`od_wait_mean_mono`).
4. **Riskier project, pp. 233–234 (departure in the proof).** `od_option_riskier` is stated with
   `F₁` the riskier distribution, as in the book's definition (the book's project 2). The book
   argues "by the convexity of the value function"; the proof applies the definition of
   second-order dominance to the concave increasing `min(z − q, I)` and compares the fixed points
   of the two scalar Bellman maps.
5. **Not formalised:** that the solution of the Bellman equation is the value of the stopping
   problem (the book's appeal to Section 7.3.1). The Bellman equation is identified with the
   stationary Bellman equation of Chapter 5's `optionExercise` and `jobSearch`
   (`od_option_bellman_iff_stopping`, `od_mccall_bellman_iff_stopping`); existence and uniqueness
   are proved for the Bellman equation itself, which is all §8.1 uses.

### §8.2 Discrete choice

6. **Setting.** `c` is a bounded continuous function on `ℝ` (the book's `c` on `[0, ∞)` extends);
   the Bellman equation is imposed on `[0, ∞)`. Existence is on `C(ℝ)` (`od_dc_exists`),
   uniqueness among bounded continuous functions on `[0, ∞)` (`od_dc_unique`). Monotonicity of `V`
   needs only `c` increasing (`od_dc_antitone`).
7. **Existence of the trigger `s*`, p. 235.** The book assumes an indifference point exists. It
   does when `c(s₁) − c(0) > P_b − P_s` for some `s₁` (`od_dc_trigger_exists`), but not when the
   cost rises by at most `D < (1 − β)(P_b − P_s)`: maintaining is then strictly optimal everywhere
   (`od_dc_no_trigger`; concrete model `c = ((1 − β)/2) arctan`, `P_b − P_s = 1`,
   `od_dc_example_no_trigger`). All results about `s*` take an indifference point as a
   hypothesis; it is then unique (`od_dc_trigger`), so "the smaller value" is the only one.
8. **The solution formula, p. 236.** The printed
   `V(s) = max{−c(s*)/(1 − β), −c(s)/(1 − β) + ∫_s^{s*} c′(y)/(1 − β)[1 − βe^{−λ(1 − β)(y − s)}]dy}`
   is false: its second term equals `V(s) + (c(s*) − c(s))/(1 − β)`, strictly above `V(s)` on
   `[0, s*)` (`od_dc_solution_misprint`; concrete model `c = 2 arctan`, `P_b − P_s = 1`, at
   `s = 0`: `od_dc_example_misprint`). It also contradicts the printed trigger equation. The
   correct formula on `[0, s*]` is
   `V(s) = −c(s*)/(1 − β) + ∫_s^{s*} c′(y)/(1 − β)[1 − βe^{−λ(1 − β)(y − s)}]dy`
   (`od_dc_solution_book`), equivalently `−c(s)/(1 − β) − ∫_s^{s*} βc′(y)/(1 − β)e^{−λ(1 − β)(y − s)}dy`
   (`od_dc_solution`), and `V = −c(s*)/(1 − β)` on `[s*, ∞)` (`od_dc_trigger`, `eq_8_2`). We do
   not claim the `max` representation beyond `s*`.
9. **The trigger equation, p. 236,** is correct (`od_dc_trigger_eq`); its uniqueness needs `c`
   increasing, which gives `c′ ≥ 0` (`od_dcH_strictMonoOn`, `od_dc_trigger_eq_unique`). (8.1),
   (8.2) and the trigger equation use `c` differentiable with continuous `c′` (the book's
   "continuously differentiable").

### §8.4 Consumption/portfolio choice

10. **Wealth, p. 260:** `W_t = ∑(P_{jt} + D_{jt})ψ_{j,t−1} + R_t B_{t−1}` has `R_t` for `R^f_t`.
    (8.17) needs `P_j ≠ 0` (to define `R_j`) and `W − C ≠ 0` (to define `π_j`) (`eq_8_17`).
11. **First-order and envelope conditions, p. 261,** are proved for finitely many next-period
    states (differentiating `E` is differentiating a finite sum) at an unconstrained maximum, with
    `V_t` assumed differentiable for the envelope condition (`od_portfolio_foc`,
    `od_portfolio_envelope`). The `π_j` condition is printed without `β`; it is derived as
    `β·E[…] = 0` and divided by `β ≠ 0`.
12. **Euler equations, p. 261.** "Combining the above conditions" uses the envelope identity at
    `t + 1`, `V′_{t+1}(W_{t+1}) = u′(C_{t+1})`, a hypothesis of `od_portfolio_euler` (it is the
    date-`t` identity `u′(C_t) = V_t′(W_t)`, proved there, one period later). Dividing the `π_j`
    condition by `W − C` and forming `βu′(C_{t+1})/u′(C_t)` need `W ≠ C` and `u′(C_t) ≠ 0`, which
    the book leaves implicit. The Euler step itself holds for any probability measure.

### Exercises

13. **Exercise 8.1** is solved in the bounded continuous setting of §7.3.1: bounded continuous
    wage, Feller transition function `Q` (`ex_8_1`). The characterisation proved: the acceptance
    rule `wage(w) ≥ (1 − β)Ψ(w)` with `Ψ(w) = c + β∫V dQ(w)` (`ex_8_1_policy`), monotonicity of
    `V` and `Ψ` for monotone `Q` (`ex_8_1_mono`), and the i.i.d. case (`ex_8_1_iid`). The
    reservation-wage property (acceptance set an upper set) is not claimed: with Markov offers the
    reservation wage depends on the current offer.
14. **Exercise 8.2** is formalised with the reading that a fired worker receives `c` while
    waiting and draws an offer the following period, so his value equals that of a worker who
    rejects an offer (`od_FiringBellman`). The results hold for every `α ≥ 0` (`α ≤ 1` is not
    needed); `α = 0` is McCall's model (`od_mccall_iff_firing`).

## §8.3 (introduction), §8.3.1 and Exercise 8.8

15. **Positive consumption.** The book allows `c_t ≥ 0`. Utility is real-valued on `(0, ∞)`
   (`cd_Utility`), so log or CRRA with `γ ≥ 1` (`u(0) = −∞`) are covered, and feasible plans
   have `c_t > 0` (`cd_Feasible`, `cd8_Feasible`). Under the Inada condition zero consumption is
   never optimal. `u′′ < 0` is used only as "`u′` strictly decreasing"; `u′` is assumed
   continuous.
16. **Optimality with unbounded utility.** The objective may diverge, so optimality
   (`cd_Optimal`, `cd8_Optimal`) is by partial sums: no feasible plan overtakes the optimal one
   by more than `ε` eventually. For plans with summable utility this is maximal value
   (`cd_tsum_le_of_optimal`).
17. **(8.5)** is read as `liminf a_{T+1}/R^T ≥ 0` (`cd_NoPonzi`), since the limit need not exist.
   Under the hypotheses of the first part of Theorem 8.3.1 the limit exists (`theorem_8_3_1`).
   That part needs `b ≥ 0` fixed (the book's "and any `b ≥ 0`"); it is stated pathwise, hence
   almost surely for stochastic income.
18. **Rolling over debt, p. 238.** The book writes `a_{T+1} = R^t a_1`; the exponent is `T`
   (`cd_rollover`).
19. **Theorem 8.3.1, converse, p. 238.** With only "support `[y_min, y_max]`" the claim is false:
   constant income `y_max > y_min`, `c_t = 0`, `a_t = −y_max/r` satisfies (8.3) and (8.5) with
   `a_t < −y_min/r` (`theorem_8_3_1_converse_counterexample`). The proof is also incomplete: it
   shows that for each `n`, with positive probability, `a_{t+n}/Rⁿ < −ε/2`, and concludes that
   with positive probability the limit is negative; that needs one event for all `n` (income
   low forever), which is null for i.i.d. income. The corrected statement
   (`theorem_8_3_1_converse`) assumes that any event `{a_t < −y_min/r − ε}` of positive
   probability keeps positive probability when intersected with `{y_{t+k} ≤ y_min + δ, k < N}`
   (true for i.i.d. income with `y_min` in the support); the proof truncates at `N` and bounds
   the tail of income by `y_max/(rR^N)` (`cd_converse_path`). The printed bound
   `a_{t+n} ≤ −y_min/r + (rε/2)(1 + … + R^{n−1}) − Rⁿε` holds; its rearrangement for
   `a_{t+n}/(1 + r)ⁿ` is garbled in the draft and is replaced by `a_{t+n}/Rⁿ < −ε/2` for `n ≥ N`.
20. **(8.7)–(8.8), pp. 239–240, deterministic income.** The Euler inequality is derived from
   optimality by one-period perturbations of saving (`eq_8_7`), not from the Maximum Principle
   of §7.4; sufficiency (`eq_8_7_8_8_sufficient`) is the argument of Theorem 7.5.2 done directly
   in these variables. Sufficiency uses (8.8) through `βᵗu′(c_t)â_{t+1} → 0`, which follows
   from (8.8) and (8.7) when `y_t ≥ rb` (`cd_TVCs_of_TVC`). The stochastic versions, the
   stochastic Bellman equation and the properties of `V` the book assumes on p. 240 are not
   formalised here (§8.3.2).
21. **Case 1 construction, pp. 241–245.** The maps `h_t` and intervals are parametrised by the
   cash on hand `z ∈ [y − rb, x*_0]` at which the limit first binds: `X_k(z)` is cash `k` periods
   earlier (`cd1_Params.X`), `h_k = X_{k+1} ∘ X_k⁻¹` and `x*_k = X_k(x*_0) = X_{k+1}(y − rb)`
   (`cd1_Params.X_succ_w`). The book does not show that the critical levels go to infinity,
   which is needed for "by induction, we can define … on the whole state space `[y − rb, ∞)`";
   it holds since `u′(φᵏ(z)) = (βR)ᵏu′(z) → 0` (`cd1_Params.xstar_tendsto`,
   `cd1_Params.exists_kz`). The value function is defined as the value of the optimal plan
   (`cd1_Params.V`); its strict monotonicity and strict concavity are proved directly from the
   sequence problem rather than "as in Section 6.4", and the envelope condition by
   Benveniste–Scheinkman (`theorem_4_10`). The book's agreement conditions at `x*_s`
   (`h_s(x*_s) = h_{s+1}(x*_s)`, `V_s(x*_s) = V_{s+1}(x*_s)`, `V_s′ = V_{s+1}′`) are automatic
   for the single function `V`. The Bellman maximum is over `â ∈ [0, x)` (positive
   consumption). `b ≥ 0` is not needed.
22. **Case 1 dynamics, p. 245.** "Constant over time … for `t > t`" should read `t > T`
   (`cd1_Params.plan_dynamics`, `cd1_Params.plan_binding`).
23. **Case 2, p. 246.** The book's proof uses `V′` and the envelope condition (assumed); the
   proofs here use the Euler inequality (8.7) of an optimal plan, and `u′(c_t) = (βR)^{−t}u′(c_0)
   → 0` instead of continuity of `u′` at a finite limit (`cd2_never_binding`,
   `cd2_c_tendsto`). The results are conditional on an optimal plan and need `x₀ ≥ y − rb`.
24. **Annuity value `A_t`, p. 247.** The printed `A_t = r∑_{j≥1}R^{−j}(y_{t+j} − rb)` omits
    period-`t` income; the proof uses `∑_{j≥t}R^{t−j}A_t = ∑_{j≥t}R^{t−j}(y_j − rb)`, i.e.
    `A_t = (r/R)∑_{j≥0}R^{−j}(y_{t+j} − rb)` (`cd3_A`). Counterexample to the printed formula
    (`cd3_Abook_counterexample`): `b = 0`, `y = (Y, 0, 0, …)`, `a₀ = 0`: every printed `A_t` is
    `0` but the optimal plan consumes `(r/R)Y` forever.
25. **Chamberlain–Wilson, p. 247.** `lim c_t = sup_t A_t` is false for general initial wealth:
    with constant income and `a₀ > −b` the optimal plan `c_t = y + ra₀` (the book's own p. 249
    paragraph) has `lim c_t = y + ra₀ > y − rb = sup_t A_t`
    (`cd3_chamberlain_wilson_counterexample`). The proof of `c* ≤ A*` assumes "there is a `t`
    such that the consumer is borrowing constrained in period `t − 1`" without justification.
    Corrected: `c* ≥ A_t` for all `t` always (`cd3_lower`, for any `β`); `c_j ≤ sup A` once the
    consumer is constrained at some date (`cd3_upper`; after the last constrained date
    consumption is constant); so `lim c_t = sup_t A_t` when `a₀ = −b`
    (`cd3_chamberlain_wilson`). Income is assumed bounded, `rb ≤ y_t ≤ M`. The deviation in the
    `c* ≥ A*` step is spelled out: consuming `ε` more at one date `τ` keeps saving nonnegative
    because `â_{t+N+1} ≥ εRᴺ` for `N ≥ N₀`.
26. **Example 8.3.1, p. 248.** The saving for even `t` is `a_{t+1} = (y_h − y_l)/(1 + R)`, not
    `(y_h − y_l)R/(1 + R)` (`example_8_3_1_savings`; `example_8_3_1_savings_misprint`: the
    printed value violates the budget when `R ≠ 1`, `y_h ≠ y_l`).
27. **Exercise 8.8.** Income is deterministic with `0 ≤ y_t ≤ M` and `R > 1`. The natural
    borrowing constraint is the no-Ponzi condition (8.5). The value is finite iff
    `βR^{1−γ} < 1` (given `W > 0`): sufficiency `ex_8_8_value` (`γ ≠ 1`), necessity for
    `γ < 1` in `ex_8_8_infinite`; for `γ ≥ 1` the condition holds automatically
    (`ex_8_8_gamma_gt_one`, `γ > 1`; `β < 1` at `γ = 1`). At `γ = 1` (log) the policy and
    optimality are covered (`ex_8_8`), the closed-form value is not.

## §8.3.2 and Exercises 8.9–8.11

### The setting

28. **What is assumed and what is derived.** As on p. 240, a solution of the Bellman equation
   (`SIModel.Solution`) is assumed: `V` strictly increasing, strictly concave, differentiable at
   every `x ≥ x_min` with continuous derivative, the maximum attained at `â(x)`, and the
   envelope condition. `u` is real-valued and continuous on `[0, ∞)` (consumption `0` is
   feasible), which excludes the logarithm, as in §6.6.2. The Euler inequality (8.7) is **not**
   assumed: it is derived from the maximisation in the Bellman equation (`S.euler`, `S.eq_8_7`),
   together with interior consumption (`S.cons_pos`). The book's `R > 1` is weakened to `R > 0`
   (Lemma 8.3.1 is stated for `R > 0`); `x_min = y_min − rb > 0` is the book's standing
   `b < y_min/r` (p. 239).

### Case 1 (`βR < 1`)

29. **Lemma 8.3.2, proof.** The book argues from a constraint that "never binds". The proof here
   shows directly that the constraint binds at `x_min` (`S.sav_xmin`:
   `βR E V′(y − rb) ≤ βR V′(x_min) < V′(x_min)`) and characterises the binding region
   (`S.sav_eq_zero_iff`); the statement is as printed (`S.lemma_8_3_2`).
30. **Proof of Lemma 8.3.3, p. 253.** "By definition,
   `c(y_max − rb + Râ(x_t)) = c(y_min − rb + Râ(x_t)) + y_max − y_min`" is false: Lemma 8.3.1
   gives only `≤` (`S.cons_high_le`), and the inequality is strict whenever `y_min < y_max` and
   the constraint does not bind at `y_min − rb + Râ(x_t)` (`S.eq_8_16_identity_false`), which is
   the case in the proof (`â → ∞`). The `≤` suffices for (8.16) (`S.eq_8_16`). In the step
   `c(x) → ∞` the contradiction is `u′(c̄) = βRu′(c̄)`, printed `c̄ = βRc̄`
   (`S.cons_unbounded`). The RRA hypothesis is used through footnote 2, proved as
   `M.footnote_2` from the monotonicity of `u′(c)c^γ` (`M.footnote_2_mono`); `u′′` enters as a
   derivative `ddu` of `u′`.
31. **Proof of Proposition 8.3.1.** (a) "It follows by induction that `{φₙ(x_min, y_max)}` is a
   strictly increasing sequence" is false in general: the sequence is nondecreasing
   (`S.phi_high_monotone`), and `φ₂ = φ₁` whenever the constraint binds at
   `φ₁ = y_max − rb + Râ(x_min)` (`S.phi_two_eq_one`; by Lemma 8.3.2 this happens when
   `y_max − rb ≤ x̂`). Also its limit `ξ` is `≤ x_max`, not `< x_max`. (b) "A similar argument
   applies to `x₀ = x_max`" needs that, with income `y_min` forever, cash on hand falls to
   `x_min`; this is proved from the Euler equation (`S.next_low_lt`, `S.phi_low_tendsto`).
   (c) The mixing point: instead of `x̄ = lim φₙ(x_min, Ey)` (and `ξ > x̄`), the proof uses
   `x̄ = x_min + (y_max − y_min)/2`, which lies above `lim φₙ(x_max, y_min) = x_min` and below
   `φₙ(x_min, y_max − δ) ≥ y_max − δ − rb` (`S.mixing`). The displayed bounds are proved as
   stated, for every `x` and every `[a, b] ⊆ [y_min, y_max]` (`S.kpow_ge`, `S.kpow_ge_real`).
   Theorems 3.3.5–3.3.6 are applied as SLP Theorem 12.12 (`SIWC.theorem_12_12_real`); the
   proposition (`S.proposition_8_3_1`) needs `y_min < y_max` (for `x_max > x_min`, Exercise 8.9)
   and is stated for the kernel on `[x_min, x_max]`.
32. **Continuity in `(R, b)`** (Proposition 8.3.1, last sentence) is not formalised: it needs the
   policy to be jointly continuous in `(x, R, b)`, which does not follow from the book's
   assumption of a solution `V` for each parameter value, and the state space `[x_min, x_max]`
   itself depends on `(R, b)`, outside the fixed-state-space Theorem 12.13.
33. **Exercise 8.9** needs `y_min < y_max` (and the hypotheses of Lemma 8.3.3, which make
   `x_max` finite): if `y_min = y_max` then `â(x_min) = 0` (`S.sav_xmin`) makes `x_min` itself
   a fixed point of `x ↦ Râ(x) + y_max − rb`. `x_max` is defined as the largest fixed point
   (`S.xmax`) and shown to be the smallest critical value of Lemma 8.3.3 (`S.ex_8_9`).

### Cases 2 and 3

34. **Proposition 8.3.2 (ii), proof.** The display ends with
   `(c(y_max − rb + Râ)/c(y_min − rb + Râ))^γ`, which is `≥ 1`; footnote 2 gives the reciprocal
   `(c(m)/c(M))^γ ≤ 1`, which tends to `1` because `c(m) → ∞` (`S.cons_unbounded_gt`, the
   "similar argument"). The proof is otherwise as printed (`S.proposition_8_3_2_ii`).
   Proposition 8.3.2 (i) is proved in one step: at `z₀ = Rk + y_max − rb` the Euler inequality
   gives `V′(z₀) ≥ βRV′(z₀)` (`S.proposition_8_3_2_i`).
35. **Case 3, p. 258.** "The set of sample paths for which there are infinitely many `t` such that
   `y_{t+1} = y_min` … has probability one" requires atoms at `y_min` and `y_max`; for a
   distribution with a density (as in Proposition 8.3.1) it has probability zero. The argument
   works with "`y_{t+1} ≤ y_min + δ` and `y_{t+1} ≥ y_max − δ` infinitely often"
   (`S.not_converge`, from `S.limit_of_converge`). The almost-sure statements (Supermartingale
   Convergence Theorem, Chamberlain–Wilson) are not formalised; their deterministic consequence
   is `M.supermartingale_limit`. **Lemma 8.3.4** needs non-degenerate income,
   `μ((y_min, ∞)) > 0` (hypothesis `hnd` of `S.lemma_8_3_4`).

### Exercises

36. **Exercise 8.10** (Levhari–Mirman–Zilcha) is not formalised: "characterise the policies" has
   no definite statement, there is no closed form, and with `u = −e^{−γc}` the Inada condition
   fails (`u′(0) = γ`), so the results of §8.3.2 do not apply; the same exercise is not
   formalised in Chapter 7 (Exercise 7.9).
37. **Exercise 8.11.** (a) The printed constraint `x_{t+1} = R(x − c_t) + y_t` is read as
    `x_{t+1} = R(x_t − c_t) + y_{t+1}` (the timing of §8.3 and Exercise 7.7); `ρ < R` is
    assumed. (b) The solution is proved at the level of the Bellman equation (`ex_8_11`), by
    reduction to Exercise 7.7 in `z = x + ρy/(R − ρ)`; as Exercise 7.7 shows (`ex_7_7`,
    `ex_7_7_ponzi`), without a no-Ponzi condition the policy is optimal only among plans
    satisfying (7.4). (c) **"There is no stationary distribution for `(x_t)`" is false as
    stated**: with `ρ = 0`, `x_{t+1} = x_t + L̄/γ + ε_{t+1}`, and if `ε = e₀` a.s. and `βR = 1`
    then `L̄/γ + e₀ = 0` and every point mass is stationary (`ex_8_11_counterexample`). It is
    true iff `L̄/γ + ε` is not a.s. `0` (`ex_8_11_no_stationary`, `si_no_stationary`).

## §8.5 Inventory and Exercises 8.3–8.7

38. **Assumption 8.5.1, p. 263, is too weak.** `L ≥ 0` convex and coercive does not make
   `G_1(y) = L(y) + py` attain its minimum, so `S_1` (and the one-period (s, S) policy of
   Figure 8.5) need not exist: `L(y) = √(1 + y²)/2` is nonnegative, convex, coercive and
   differentiable, but `L(y) + y` has no minimiser (`INModel.assumption_8_5_1_counterexample`).
   We add `L(y) + py → ∞` as `y → −∞` (`INModel.Assumption851.G1_coercive`).
39. **Implicit hypotheses.** The book leaves implicit that demand is nonnegative with finite mean
   (`demand_nonneg`, `demand_int`; needed for `Ef_n(y − z)` to be finite, as `f_n(x)` grows
   like `−px` as `x → −∞`), that `β ∈ (0, 1)`, `c, p ≥ 0` (`C ≥ 0`, p. 262) and `L ≥ 0`.
40. **Definition 8.5.1 and Lemma 8.5.1.** We take (8.25) as the definition (`in_CConvex`) and
   prove that it implies (8.24) for differentiable `h` (`definition_8_5_1`); Lemma 8.5.1 uses
   both (`lemma_8_5_1`). Property (iii) is proved for `α, γ ≥ 0` (book: `> 0`).
41. **(8.23) and `s_n < S_n`, p. 265.** For `c = 0` there is no solution with `s_n < S_n` when
   `S_n` is the smallest minimiser; we define `s_n` as the least `x` with
   `G_n(x) ≤ c + G_n(S_n)` (`in_sbar`), which equals `S_n` for `c = 0`
   (`in_sbar_eq_of_zero`) and is `< S_n` for `c > 0` (`INModel.eq_8_23`).
42. **Lemma 8.5.2, p. 268.** The proof as printed has misprints (`(G_n(s_n) − G_n(x))/(s_n − s)`,
   `G_n(x_n)`); we give our own proof (`lemma_8_5_2`, `in_ss_key`). Continuity of `G` is needed
   for (8.23) (`in_ss_eq`); at `x = s_n` the firm is indifferent and the rule orders.
43. **(8.27)(ii), p. 270, is false for demand distributions with atoms.** With `β = 1/2`,
   `c = 1`, `p = 0`, `L(y) = y²` and demand `z ≡ 0`, `s_1 = −1` and
   `G_2(y) = y² + (max(y, −1))²/2` is not differentiable at `−1`
   (`INModel.eq_8_27_ii_counterexample`). The book writes the demand with a density `ϕ(z)`;
   the positive statement under a density is not formalised. None of our proofs use
   derivatives: Lemmas 8.5.4–8.5.6 and Propositions 8.5.1–8.5.4 do not need Assumption 8.5.2
   (only Exercise 8.7's first-order condition does); (8.27)(i) is proved (`INModel.eq_8_27`).
44. **Lemma 8.5.4 / Exercise 8.3.** The hint "`G′_n(x) < 0` for `x < S_1`" is replaced by its
   difference form, `G_n` strictly decreasing on `(−∞, S_1]` (`INModel.ex_8_3`); the lemma holds
   for every `n` (`INModel.lemma_8_5_4`).
45. **Lemma 8.5.5.** The bound is `M = max(R, ζ)` with `ζ` a minimiser of `L` and `L ≥ L(ζ) + c`
   on `[R, ∞)`; convexity of `L` is not needed (`INModel.lemma_8_5_5`).
46. **Lemma 8.5.6, p. 272, is false for `c = 0`.** With `c = p = 0`, `L(y) = y²`, demand `0`,
   `s_1 = S_1 = s_2 = 0`, so `2s_1 − S_1 < s_2` fails (`INModel.lemma_8_5_6_counterexample`).
   True: `2s_1 − S_1 < s_n` for `c > 0` (`INModel.lemma_8_5_6`) and `≤` for all `c ≥ 0`
   (`INModel.lemma_8_5_6_le`). The proof's "`f′_n(x) ≤ −c` for `x ≤ s_1`" is only used as "`f_n`
   is nonincreasing on `(−∞, s_1]`".
47. **Proposition 8.5.1, p. 274.** The iteration `max |f_{n+1} − f_n| ≤ βⁿ max |f_1|` uses that
    `f_n − f_{n−1}` is constant left of `−A`, which fails for `n = 1` (`f_1(x) = −px + G_1(s_1)`
    while `f_0 = 0`, unbounded when `p > 0`); we start from `f_2 − f_1`
    (`INModel.diff_bound`). The statement is unaffected (`INModel.proposition_8_5_1`).
48. **Proposition 8.5.2, p. 274.** The "tedious" interchange of limit and minimum is done with
    the uniform estimate `0 ≤ f − f_{n+1} ≤ βⁿK` on `(−∞, B]` (`INModel.tail_bound`), no
    compactness needed (`INModel.proposition_8_5_2`).
49. **Proposition 8.5.3, p. 275.** A limit point `s` of `{s_n}` and a limit point `S` of `{S_n}`
    need not satisfy `s ≤ S` when `c = 0` (both are minimisers of `G`, possibly different, and
    `d(x) = S − x` must be `≥ 0`). We prove: every limit point `s` of `{s_n}` has `G(s) = c +
    G(S)` for every minimiser `S`; the (s, S) policy is optimal whenever `s ≤ S`
    (`INModel.ex_8_4_policy`), which is automatic for `c > 0` (`INModel.ex_8_4_lt`) and holds
    with `S = s` for `c = 0` (`INModel.ex_8_7`). A limit point `s` need not be the least
    solution of `G(s) = c + G(S)`; the policy is still optimal because `G = c + min G` between
    the two (`INModel.Glim_ge_of_le`).
50. **Proposition 8.5.4, p. 275** (proof omitted in the book). We read "solution of (8.21)" as:
    `EF(y − z)` exists for every `y` and `F(x)` is the infimum (not necessarily attained) in
    (8.21) (`IsGLB`). Upper boundedness on finite intervals is not used
    (`INModel.proposition_8_5_4`).
51. **Exercises 8.5–8.7 refer to "the inventory model in Section 8.4".** §8.4 is
    Consumption/Portfolio Choice; this is a misprint for §8.5.
52. **Exercise 8.5: uniqueness needs a condition on demand.** With `z ≡ 0` and `s < S`, both
    `δ_S` and `δ_{(s+S)/2}` are stationary (`ex_8_5_counterexample`). Under
    `ϕ(z > S − s) > 0` the chain on the absorbing set `(−∞, S]` (`ex_8_5_absorbing`) satisfies
    the Minorization Condition with `N = 2` (`ex_8_5_minorization`), hence Condition M and
    Theorem 3.3.1 give a unique stationary distribution with geometric convergence (`ex_8_5`).
    The Markov property is proved for any history independent of the next demand
    (`ex_8_5_markov`). The policy `(s, S)` is any pair with `s ≤ S`. Uniqueness among
    stationary distributions on all of `ℝ` (stocks above `S` are transient) is not formalised.
53. **Exercise 8.6** has no definite claim ("characterize `s` and `S`"). We prove, for any demand
    law, `G(x) = L(x) + p(1 − β)x + βpEz + β(c + min G)` for `x ≤ s`, so `s` solves
    `L(s) + p(1 − β)s + βpEz = (1 − β)(c + min G)` and `S` minimises `G` (`INModel.ex_8_6`);
    for exponential demand `Ez = 1/λ` (not computed in Lean).
54. **Exercise 8.7.** `s_n = S_n` for every `n`; limit points of `{s_n}` are minimisers of `G`
    and satisfy `p(1 − β) + L′(s) = 0` (Assumption 8.5.2), via: every minimiser of `G`
    minimises `L(y) + p(1 − β)y` (`INModel.ex_8_7_H`, `INModel.ex_8_7`).

## §8.6 and Exercises 8.12–8.14

55. **Assumptions on `Ψ`, p. 278.** `Ψ : ℝ × ℝ₊ → ℝ₊` with `Ψ(0, ·) = 0` and `Ψ₁ > 0` everywhere
   is impossible (`Ψ(−1, K) < Ψ(0, K) = 0`; `iv_psi_assumptions_inconsistent`), and with the
   printed `Ψ₁₁ < 0` investment would *decrease* with `Q` (`iv_invest_anti_of_concave`). The
   intended assumptions are `Ψ₁₁ > 0` with `Ψ₁` of the sign of `I` (`Ψ₁(0, K) = 0`, as stated
   in §8.6.3); `iv_invest_mono` uses `Ψ₁` strictly increasing.
56. **The tail condition behind (8.33), p. 279.** `lim βᵀ(1 − δ)ᵀQ_{T+1} = 0` does not follow
   from the transversality condition (8.32) in general (`iv_tvc_not_implies`: `β = δ = 1/2`,
   `Qₜ = 4ᵗ`, `Kₜ = 4^{−t}`, negative investment, (8.31) holding with `π′ = Ψ₂`). It does follow
   when `Q ≥ 0`, investment is nonnegative and `K₀ > 0` (`iv_tvc_implies`). `eq_8_33` assumes the
   book's tail condition directly. Infinite sums in (8.33) and Hayashi's result are limits of
   partial sums (the series need not converge absolutely).
57. **Sufficiency of (8.30)–(8.32)** is not stated in the book; we prove it for concave
   `π(K) − I − Ψ(I, K)` and `Q ≥ 0`, against plans with nonnegative capital
   (`iv_q_sufficient`, `iv_q_optimal`). Hayashi's result (`iv_hayashi`) assumes linear
   homogeneity of `Ψ` for every `λ > 0` and differentiability along the plan.
58. **"The two problems give identical solutions", p. 277.** Proved as the exact
   summation-by-parts identity `iv_owned_partialSum` (the owning firm's objective is the rental
   firm's objective at `R_k = r + δ` plus date-0 terms minus `βᵀK_{T+1}`) and the comparison
   `iv_owned_le_of_rental`; the terminal capital term is explicit.
59. **Cobb–Douglas profit, p. 277**, needs `0 < α_l < 1` (else `max_L` is infinite or not
   attained); convexity / concavity under increasing / decreasing returns are proved strict
   (`iv_cd_convex`, `iv_cd_concave`; the concave case uses `α_k > 0`).
60. **(8.36), p. 282.** As printed, (8.36) subtracts `φ(K)` for every `I`, including `I = 0`,
   whereas the Bellman equation charges the fixed cost only when `I ≠ 0`; the printed objective
   can select a non-optimal investment (`iv_eq_8_36_misprint`: linear continuation value,
   `p_b = 1`, `p_s = 0`, `Ψ = I²/2`, `φ = 1/2`, `Q = 3/2`: the printed problem picks `I = 1/2`,
   inaction is strictly better). With the fixed cost charged for `I ≠ 0` only, `R(I) − R(0)` is
   the (8.36) objective (`eq_8_36`) and `ϕ = max(Vᵇ, Vˢ) − Vⁱ` (`iv_phi_eq`); the boundary
   characterisation `ϕ = 0` of p. 287 holds either way when `φ > 0` (`eq_8_46_8_47`).
61. **Example 8.6.1, p. 286.** The fixed-cost thresholds are `p_b + √(2φ)` and `p_s − √(2φ)`
   (profit `(Q − p_b)²/2 − φ ≥ 0` iff `Q − p_b ≥ √(2φ)`), not `p_b + 2√φ` and `p_s − 2√φ`
   (`example_8_6_1_fixed_buy`, `example_8_6_1_fixed_inaction`, `example_8_6_1_fixed_sell`;
   counterexample `example_8_6_1_misprint`: `φ = 1/2`, `Q = p_b + 6/5 ≤ p_b + 2√φ`, yet buying
   `6/5` earns `0.22 > 0`).
62. **Heuristic parts of §8.6.3** (the book: "we will proceed heuristically"). The Taylor step
   `ϕ ≃ ψ` is formalised as the first-order expansion `eq_8_37_taylor` and the exact
   first-order condition of footnote 8 (`iv_footnote_8`); the static problem `ψ(Q, K)` is
   solved exactly. The monotonicity of `Kᵇ(z)` (p. 283) is proved for the *largest* solution of
   (8.41) with `E[·|z]` abstracted as a monotone operator mapping increasing functions to
   increasing functions (`iv_q_monotone`, `iv_boundary_mono`); the region statements need `Q`
   strictly decreasing in `K` (`iv_buy_region`, `iv_sell_region`). The fixed-cost rule
   (8.43)–(8.45) is proved with `Q₁`, `Q₂` characterised as the points where the
   no-fixed-cost profit equals `φ` at the FOC solution (`eq_8_43`–`eq_8_45`). Not formalised:
   the p. 287 claims (stated as "intuitive") that with fixed costs the firm buys iff
   `K < Kᵇ(z)` and that the boundaries increase in `z`.
63. **Exercise 8.12.** The Bellman equation is taken on `K > 0` with next-period capital
   positive (`iv_SolvesBellman`). A solution's scaling `λ⁻¹V(λK)` is again a solution
   (`ex_8_12_scaling`), so linear homogeneity `V(K) = V(1)K` holds under uniqueness
   (`ex_8_12_homog`); Hayashi's result is derived for `V(K) = vK` (`ex_8_12_hayashi`).
   Existence/uniqueness of the solution is not proved (unbounded returns).
64. **Exercise 8.13.** With `β = 1/(1 + r)` and `D = (r + δ)² + 2(r + δ) − 2A`, the solution is
    `i = r + δ − √D`, `Q = 1 + i`, `V(K₀) = (1 + r)(1 + i)K₀`; we assume `D > 0`, `δ ≥ 0` and
    `1 − δ + i > 0` (capital stays positive, where `I²/(2K)` is defined and convex) and prove
    optimality among plans with `Kₜ > 0` whose discounted profits converge (`ex_8_13`). For
    `D < 0` the value is `+∞` (`ex_8_13_unbounded`); the boundary case `D = 0` is not treated.
65. **Exercise 8.14 / (8.34).** The first-order conditions of Uzawa's model are proved
    sufficient (with transversality, `Q ≥ 0`, `π(K) − I` and `Φ` concave), not necessary
    (`ex_8_14_sufficient`, `ex_8_14_optimal`). "Both formulations deliver similar results" is
    formalised as the change of variables `X = Φ(I, K)`, `Ψ(X, K) = G(X, K) − X` with `G` the
    inverse of `Φ(·, K)` (`ex_8_14_equiv`), under which the two `Q`'s agree (`ex_8_14_Q_same`).
