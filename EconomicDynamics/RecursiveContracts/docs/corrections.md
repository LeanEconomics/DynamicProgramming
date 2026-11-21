# Corrections and departures: Miao Chapter 22

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 22, Recursive
Contracts, pp. 773–801. Lean names are relative to `Miao.RecursiveContracts`. Every book item is
located in the [source map](source-map.md).

## Introduction, §22.1 Limited Commitment and Exercises 22.1–22.2

### Corrections

1. **p. 777, "States where `λᵢ = 0`", and p. 778, "The Optimal Contract".** The book: (22.9)
   "implies that `wᵢ = v`", hence `w = max{U_d(y), v}` and "promised values never decrease".
   True when endowments are i.i.d. (the case of Ljungqvist–Sargent that the text follows): then
   `P(θᵢ, v) − θᵢ` does not depend on `i` (`lc_iid_value_shift`), and for strictly concave `P`
   the promised value after `θⱼ` is `max{U_d(θⱼ), v}` (`lc_iid_promised_value`), so promised
   values are nondecreasing and constant once the state with the largest autarky value has
   occurred (`lc_iid_full_insurance`). False for the general Markov chain of §22.1: with three
   states, `β = 1/2`, `u = log`, endowments `(1, e², e⁻²)`, state 0 moving to 1 or 2 with
   probability 1/2 and 1, 2 absorbing, the optimal contract at `(θ₀, v = 1)` is `c = 1`,
   `w = (0, 4, 0)`: after state 2 the incentive constraint is slack (`w₂ = 0 > U_d(θ₂) = −4`)
   but `w₂ = 0 < v = 1 = max{U_d(θ₂), v}` (`lc_promise_decrease_counterexample`). What is true
   in general is the statement about consumption: next-period consumption after `θⱼ` is
   `max{h(θⱼ), c}` with `h(θⱼ)` the consumption at `(θⱼ, U_d(θⱼ))`; consumption never falls and
   rises only when the incentive constraint binds (`lc_optimal_contract`, `eq_22_11`,
   `lc_binding_case`, `lc_slack_case`).
2. **Exercise 22.1(c), p. 798.** The book: `h(θᵢ) = u⁻¹(min_{τ ≥ 1} Σ_{t<τ} β^t u(y_t) /
   Σ_{t<τ} β^t)`. The minimum need not exist: for `u(y) = (1, 0, 0, …)` (e.g. `u = log`,
   `y = (e, 1, 1, …)`) the averages strictly decrease in `τ` (`lc_ex_22_1c_min_not_attained`).
   With `inf` (as in the main text, p. 781) the characterisation holds (`ex_22_1c`, `lc_m`).
3. **Exercise 22.1(c) and p. 781, the notation `h(θᵢ)`.** In the deterministic model the
   minimum consumption level depends on the date through the whole future endowment path, not
   on the current endowment: for `u(y) = (1, 0, 1, 1, …)`, `u(y₀) = u(y₂)` but `m₀ < m₂`
   (`lc_h_depends_on_future`). In Lean `h` is a function of the date (`lc_m`). In the Markov
   model `h(θⱼ) = σc(θⱼ, U_d(θⱼ))` is a function of the state (`eq_22_11`).

### Conventions and departures

1. **The Bellman equation (p. 776).** `lc_Bellman` requires the Bellman equation at every
   promised value `v ∈ ℝ` (the problem is well defined for all `v`; the book uses
   `v ≥ U_d(θᵢ)`). Existence of a solution for a general chain is not proved; theorems are
   stated for any solution `P`, and explicit solutions are given for log utility at absorbing
   states and in the one-state economy (`lc_absorbing_bellman`, `lc_bellman_one_state`).
2. **Concavity (p. 776).** "One can show that ... `P` is concave": proved as preservation of
   concavity by the Bellman operator (`lc_bellman_concave`); the theorems that use concavity of
   the solution take it as a hypothesis in derivative form (`P_v` decreasing in
   `lc_optimal_contract`, strictly decreasing in `lc_iid_promised_value`).
3. **First-order and envelope conditions (pp. 776–777).** Differentiability of `P` is a
   hypothesis. The envelope condition (22.8) is derived (not assumed) by perturbing `v` and
   `u(c)` together (`eq_22_8`), and the multipliers `λⱼ ≥ 0` of (22.6) with complementary
   slackness are constructed from one-sided perturbations of `wⱼ` (`eq_22_6`). Utility enters
   through hypotheses: consumption `c > 0`, `u` strictly increasing with a continuous inverse
   `g : ℝ → (0, ∞)` (as for `u = log`), derivative `du > 0` and strictly decreasing.
4. **"`wᵢ = U_d(θᵢ) > v`" (p. 777).** Proved in the i.i.d. case in the form `v ≤ wⱼ`
   (`lc_iid_promised_value`); for a Markov chain we prove instead that consumption rises
   strictly when `λⱼ > 0` (`lc_binding_case`).
5. **The sequence problem (p. 775).** Plans live on the event tree of histories; (22.1) is
   imposed at every node (`lc_IC`), which does not affect values at `y₀`. Of the equivalence
   between the sequence problem and the Bellman equation, which the book does not prove, we
   prove the decomposition direction (`eq_22_3`, `eq_22_4`, `lc_principal_recursion`,
   `lc_continuation_feasible`).
6. **The Lagrangian method (§22.1.2).** The rewriting of the Lagrangian and the sufficiency of
   the saddle-point conditions are proved for deterministic endowments
   (`lc_lagrangian_rewrite`, `lc_lagrangian_sufficiency`), the case of Exercise 22.1; the
   infinite-horizon rewriting needs nonnegative multipliers with bounded cumulative sums. The
   first best (p. 775) is likewise deterministic (`lc_first_best`).
7. **Zhang's characterisation (§22.1.3).** Proved in the deterministic model
   (`lc_zhang_identity`, `ex_22_1c`, `lc_c0_strictMono`, `lc_c0_gt_h`). In the Markov model
   (22.11) is derived from the dynamic programming analysis (`eq_22_11`) and `dᵢ(τ)` is treated
   for deterministic dates `τ` (`lc_d_markov`); general stopping times are not formalised.
8. **Exercise 22.1(a)–(b), p. 797.** "`y₀ > y₁ > ⋯ > y_n`" is read as an (weakly) decreasing,
   resp. increasing, infinite bounded sequence; we prove that the stated contract is optimal
   (not that it is the unique optimum). Concavity of `u` is used in supporting-line form
   `u(z) ≤ u(c) + du(c)(z − c)` with `du > 0` decreasing.
9. **Exercise 22.2, p. 798.** Part (a) is represented by the Bellman equation of §22.1.1 for a
   discretised chain and by the closed-form autarky value `ln y/(1 − βρ)` under log utility
   (`ex_22_2a`; the exercise does not specify `u`). Parts (b)–(c) are computational and not
   formalised.

## §22.2 Hidden Action

### §22.2

10. **Proposition 22.2.3 integrates against next period's effort.** The book prints
   `1/φ′(c(v, y)) = ∫ 1/φ′(c(w(v, y), y′)) f(y′ | a(v)) dy′`. Its proof substitutes `w(v, y)` into
   (22.21), which at the promised value `w(v, y)` integrates against `f(y′ | a(w(v, y)))`, the
   density under the effort recommended next period. `proposition_22_2_3` proves the corrected
   equation (and `ha_inverse_euler_inv`, `ha_jensen*`, `ha_rogerson_save` use it). The printed
   one fails whenever the recommended effort changes: with outputs in `[0, 1]`, densities
   `f(y | a) = 1 + a(2y − 1)` and `1/φ′(c(w(v, y), y′)) = y′`, the two right sides are
   `1/2 + a(w(v, y))/6` and `1/2 + a(v)/6` (`ha_proposition_22_2_3_printed_false`), so they
   cannot both equal `1/φ′(c(v, y))` when `a(w(v, y)) ≠ a(v)`. The same misprint appears in the
   displayed `P′(w(v, y))` formula in the proof.
11. **Proposition 22.2.2: `c_y > 0` and `w_y > 0` need a positive derivative of the likelihood
   ratio.** Differentiating (22.17) gives `−φ″(c)/φ′(c)² c_y = μ(v) r_y` with `r = f_a/f`
   (`ha_eq_22_17_deriv`), so `μ(v) > 0` gives `c_y > 0` only where `r_y > 0`; where `r_y = 0`,
   `c_y = 0` (`ha_cy_eq_zero_of_ry_zero`), and `w_y = 0` with it by the differentiated (22.20).
   The strict MLRC allows `r_y = 0`: the densities `f(y | a) = 1 + a(y − 1/2)³` on `[0, 1]`
   (`|a| ≤ 1`) have strictly increasing likelihood ratio with `r_y(1/2) = 0`
   (`ha_flat_mlrc_density`). `proposition_22_2_2` adds the hypothesis `r_y(y) > 0`; without
   derivatives, `ha_c_strictMonoOn` and `ha_w_strictMonoOn` give strict monotonicity of
   `c(v, ·)` and `w(v, ·)` under the strict MLRC alone.
12. **The MLRC is used in its strict form.** The book states MLRC as "`f_a/f` is an increasing
   function of `y`"; the last step of the proof of Proposition 22.2.2 ("`E[y f_a/f] = 0`,
   contradicting MLRC") needs `∫ y f_a > 0`, which fails for a constant likelihood ratio.
   `ha_mu_pos` and `proposition_22_2_2` assume `f_a/f` strictly increasing on the output
   interval, with `y_lo < y_hi` (`ha_mlrc_integral_pos`); the covariance step uses only the weak
   form (`ha_mlrc_integral_nonneg`, `ha_cov_lr_nonneg`). The agent's second-order condition
   `∫ [φ(c) + β w] f_aa − ψ″ < 0` is a hypothesis (`hsoc`), as in the book.
13. **"Promised `w(v, y) > y`" reads `w(v, y) > v`** (p. 787): a high output is rewarded by a
   promised value above the current one, `ha_contract_dynamics`.
14. **Jensen's strict inequality needs a non-constant next payment schedule.** The harmonic-mean
   inequality `(E[1/h])⁻¹ ≤ E[h]` holds in general (`ha_inv_expect_inv_le`, `ha_jensen`); it is
   strict when `c(w(v, y), ·)` is not constant (`ha_inv_expect_inv_lt`, `ha_jensen_strict`),
   which holds in the model when `μ(w(v, y)) > 0` and the MLRC is strict
   (`ha_jensen_strict_of_mu_pos`). The saving conclusion is proved as: borrowing any `b > 0` at
   gross rate `1/β` strictly lowers the agent's utility given the weak inequality
   (`ha_no_borrow`), and some small saving `s > 0` strictly raises it given the strict one
   (`ha_wants_to_save`, `ha_rogerson_save`), efforts held fixed.
15. **The first-order conditions are derived pointwise and the envelope condition from a saddle
   point.** The book lists (22.17)–(22.19) as "the first-order conditions" of `L`. In Lean
   (22.17) and (22.19) are derived from the maximisation of the Lagrangian's integrand
   (`ha_pointLagr`) output by output, and (22.18) from the maximisation of `L` in effort given
   differentiation under the integral sign, using (22.16) to drop the `λ` term (`eq_22_18`).
   The envelope condition `P′(v) = −λ(v)` (`ha_envelope`, `ha_envelope_condition`) is derived
   from: `P(v′)` attained by a feasible contract for each `v′`, the optimal contract at `v`
   maximising the Lagrangian with `λ(v) ≥ 0`, complementary slackness, and differentiability
   of `P` at `v`.
16. **Cited results are hypotheses.** That `P` is concave, decreasing and (if differentiable)
   strictly concave (Spear and Srivastava 1987) and that the first-order approach is valid
   (Rogerson 1985b) are not proved in the text; they enter as hypotheses (`StrictAnti dP`,
   `Antitone P`, and (22.16) in place of (22.14)). `eq_22_16` proves the direction the text
   uses: (22.14) at an interior effort implies (22.16).
17. **Setting.** Outputs lie in a compact interval `[y_lo, y_hi]` with continuous densities, and
   the functions of output (`c(v, ·)`, `w(v, ·)`, `f(· | a)`, `f_a(· | a)`) are continuous on
   `ℝ` (only their values on the interval enter); the mean value theorem for integration in
   (22.22) needs this continuity and a connected output set. In (22.12)–(22.13) the book writes
   the agent's discount factor as `α` after assuming both parties discount at `β`; the Lean
   definitions take it as an argument. In (22.21) the book's integrand mixes the variables
   `x` and `y`; the Lean statement integrates in `y`.

## §22.3 Hidden Information, Exercises 22.3–22.4

18. **Domain of `u`, p. 788.** The book takes `u : (a, ∞) → ℝ`. Here `u` is defined on all of `ℝ`
   (the book's `a = −∞`), as for the CARA utility of Exercise 22.4; the condition
   `lim_{c→a} u'(c) = ∞` is read at `−∞` (`assumption_22_3_1`). Utilities with a finite lower end
   such as CRRA are not covered. The assumption is satisfied by CARA
   (`hi_cara_assumption_22_3_1`), and `hi_modelOfAssumption` derives the model's continuity,
   strict monotonicity and strict concavity from it.
19. **Contract space, p. 789.** The book allows `cᵢ ∈ [a − θᵢ, ∞]` and `wᵢ ∈ [−∞, vmax]`. Real
   transfers and real continuation values `wᵢ < vmax` are used (`hi_Feasible`).
20. **(22.26), p. 789: misprint.** The upper bound is printed as
   `Σ πₛ [θᵢ − c*(v)]/(1 − β) = v`, and `c*` as solving `Σ πₛ u(c*)/(1 − β) = v`. The index is `i`,
   and the trailing `= v` is wrong: the bound equals `(θ̄ − c*(v))/(1 − β)` with
   `u(c*(v)) = (1 − β)v` (`hi_U`, `hi_U_eq_sum`, `hi_cstar_spec`). For the recursive problem the
   bounds are proved as `T` mapping `F` into `F` (`eq_22_26`), via the constant contract
   (`hi_const_feasible`) and Jensen's inequality (`hi_principal_le_U`).
21. **Proposition 22.3.1, pp. 791–794: what is proved.** The book's `F` is continuous functions;
   here `F` is all functions between the bounds, which is enough for the contraction argument.
   Existence and uniqueness of `P` in `F`, monotonicity (`proposition_22_3_1`) and concavity
   (`proposition_22_3_1_concave`, under Assumption 22.3.1) are proved. The book's repair of the
   averaged contract is replaced: on p. 793 it reduces `c*ᵢ` until `Cᵢ,ᵢ₋₁` binds and then adds a
   constant to every `c*ᵢ` to keep `Σ πᵢ c*ᵢ`, which changes the agent's utility and so breaks
   promise keeping. The proof here (`hi_repair`) alternates (a) mean-preserving reductions of the
   increments of `w` to the binding level `max(Dᵢ, 0)` (`hi_adjust_increments`), and (b) where
   `cᵢ₋₁ < cᵢ` at equal continuation values, pooling the transfers of all states with that
   continuation value at their expected utility (`hi_pool`), which lowers the expected transfer
   (`hi_pool_cost`). It terminates by induction on the number of steps of the contract. The
   iteration starts from the concave lower bound `L` (`hi_L_concaveOn`) rather than the book's
   `P₀ = 0`, which need not lie in `F`. Not formalised: strict concavity of `TP` (the strict gain
   for each pair of contracts does not survive taking suprema unless optimal contracts exist, and
   their existence is not proved), so Assumption 22.3.2 is not derived; uniqueness of the optimal
   contract; and continuous differentiability via Benveniste–Scheinkman.
22. **Proposition 22.3.2, p. 794: "local upward constraints never bind".** The proof shows only
   that the local downward constraints bind; the local upward constraints then hold
   (`Cᵢ₋₁,ᵢ ≥ 0`) and are slack exactly when `cᵢ < cᵢ₋₁` (`proposition_22_3_2`). If
   `cᵢ = cᵢ₋₁`, binding gives `wᵢ = wᵢ₋₁` and `Cᵢ₋₁,ᵢ = 0`; ruling out such pooling needs a
   perturbation argument using differentiability of `P`, which the book does not give. The
   proposition is proved for an optimal contract against any continuation `f` that is strictly
   concave on `(−∞, vmax)` (Assumption 22.3.2 for `f`, `hi_Optimal`). Without Assumption 22.3.2,
   concavity of `P` gives the weaker statement that whenever an optimal contract exists, one
   exists with every local downward constraint binding (`hi_proposition_22_3_2_concave`). The proof reduces only the
   slack increment `w_k − w_{k−1}` (one block shift), rather than the book's sequential
   reductions.
23. **Proposition 22.3.3, p. 795.** Proved for an optimal contract against a strictly concave
   continuation (`proposition_22_3_3`), as the proof uses Proposition 22.3.2.
24. **(22.27)–(22.29), p. 795.** The first-order conditions are taken as hypotheses (`hi_FOC`), with
   the bracketing `πᵢ[1 − λu'(θᵢ + cᵢ)]` and `πᵢ[P'(wᵢ) + λ]` (the extracted text drops the
   brackets; the summation giving (22.30) needs them). The existence of multipliers is not
   derived. The martingale property (22.30) is proved both from (22.28)–(22.29) (`eq_22_30`) and,
   without multipliers, from the intuition on p. 796 (shift every `wᵢ`, envelope theorem)
   assuming only that `P` is differentiable at `v` and the `wᵢ` (`hi_martingale_of_shift`).
25. **Lemma 22.3.3, p. 796.** Proved from the first-order conditions, as in the book, with `P'`
   strictly decreasing on `(−∞, vmax)` and `u'` strictly decreasing (`lemma_22_3_3`). It needs
   `n ≥ 2`: with one state `w₁ = wₙ` and the claim is false (`hi_lemma_22_3_3_one_state`).
26. **Proposition 22.3.4, pp. 796–797.** The shocks are an iid sequence on a probability space and
   `vₜ₊₁ = w_{ξₜ}(vₜ)` (`hi_vseq`). The properties of `P'` that the book recalls (continuous,
   strictly decreasing, negative, `P'(−∞) = 0`, `P'(vmax) = −∞`), the martingale property
   (22.30) of the policies and Lemma 22.3.3 are hypotheses on `G = P'` and the policies `W`. The
   book's argument also needs the continuity of the top policy `wₙ(v)`, which is assumed
   (`proposition_22_3_4`). All hypotheses hold in a concrete CARA example with iid fair-coin
   shocks (`hi_poverty_example`).
27. **Exercise 22.3, p. 798: not formalised as a limit.** Read in per-period terms
    (`v = ṽ/(1 − β)`), the claim is `(1 − β)P_β(ṽ/(1 − β)) → θ̄ − u⁻¹(ṽ)`. The inequality `≤`
    holds for every `β` (`ex_22_3_upper`). Both bounds of (22.26) are independent of `β` in these
    terms (`hi_normalized_bounds`), so they cannot give the limit; the lower half needs the
    construction of nearly efficient incentive-compatible contracts as `β → 1`, which is not
    attempted. For fixed unnormalised `v` both `P_β(v)` and the bounds diverge, so the printed
    "for any given `v`" needs the normalisation.
28. **Exercise 22.4, p. 799: the constant `A` must be `0`.** The printed form
    `cᵢ = −(1/γ) ln(−aᵢ(v + A))`, `wᵢ = dᵢ v + (dᵢ − 1)A`, `P(v) = [ln(−v − A) + K]/(γ(1 − β))`
    with `A = Σ πᵢ/aᵢ` is inconsistent: promise keeping at two values of `v` forces `A = 0`
    (`hi_ex_22_4_A_eq_zero`), contradicting `A = Σ πᵢ/aᵢ > 0`
    (`ex_22_4_printed_inconsistent`). The corrected statement is proved (`ex_22_4`,
    `ex_22_4_value`): `P(v) = [ln(−v) + K]/(γ(1 − β))`, `cᵢ(v) = −(1/γ) ln(−aᵢ v)`,
    `wᵢ(v) = dᵢ v` with `0 < aᵢ₋₁ ≤ aᵢ`, `dᵢ₋₁ ≥ dᵢ > 0`, `Σ πᵢ/dᵢ = 1`, the book's formula for `K`,
    and, in place of `Σ πᵢ/aᵢ = A`, promise keeping `Σ πᵢ (e^{−γθᵢ} aᵢ + β dᵢ) = 1`. The policy
    form is proved for every optimal contract obtained by rescaling an optimal contract at
    `v = −1` (`hi_cara_optimal_scale`); existence of an optimal contract is not proved (see item 21).
29. **Lemma 22.3.1, p. 790.** Proved from the two local constraints `Cᵢ,ᵢ₋₁ ≥ 0`, `Cᵢ₋₁,ᵢ ≥ 0`
    alone (`hi_local_mono`), which is what the book's proof uses and what Lemma 22.3.2 needs.
30. **Hypotheses of Propositions 22.3.2–22.3.4.** Of the properties of `P` assumed there, only
    concavity is now derived (`proposition_22_3_1_concave`). Strict concavity (Assumption 22.3.2,
    used by Propositions 22.3.2–22.3.3) and the differentiability properties of `P'` used by
    Lemma 22.3.3 and Proposition 22.3.4 remain hypotheses, because existence of optimal
    contracts and Benveniste–Scheinkman are not formalised.
