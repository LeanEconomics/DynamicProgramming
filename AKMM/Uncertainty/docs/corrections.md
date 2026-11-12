# Corrections and departures: AKMM Chapter 7

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 7, Uncertainty, pp. 187–215, and Appendix 7.A, pp. 840–841. Lean names
are relative to `AKMM.Uncertainty`. Every book item is located in the [source map](source-map.md).

## Corrections

1. **p. 189, the marginal distribution.** "Notice that this sum is the product of `π₀` against the
   `i`th column of `P`." The sum `Σᵢ Pᵢⱼ[π₀]ᵢ` is the product of `π₀` with the `j`th column
   (`markov_marginal_column`).

2. **p. 190, fn. 3, the solution of the unemployment dynamics.** The book: by repeated
   substitution `u_t = s(1 + λ + λ² + ⋯ + λᵗu₀)`. The solution of `u_{t+1} = s + λu_t` is
   `u_t = s(1 + λ + ⋯ + λ^{t−1}) + λᵗu₀` (`employment_fn3`), equivalently
   `u_t = ū + λᵗ(u₀ − ū)` (`employment_closed_form`). Counterexample to the printed formula:
   `s = f = 1/4` (`λ = 1/2`), `u₀ = 1` give `u₁ = 3/4`, the printed formula `3/8`
   (`employment_fn3_printed_counterexample`). The conclusion (`u_t → s/(s + f)`) holds
   (`employment_converges`).

3. **p. 190, "a simple necessary condition for convergence and uniqueness is that from each state
   there is a positive probability of moving to any other state. This condition is actually
   substantially stronger than we need."** A condition that is stronger than needed is
   sufficient, not necessary; and as worded (positive probability to every *other* state) it is not
   sufficient either: the book's own flip matrix `[0 1; 1 0]` satisfies it, and `[1, 0]Pᵗ` does not
   converge (`offdiag_positive_not_sufficient`). What is true: if all entries of `P` are positive
   there is a unique stationary distribution and `π₀Pᵗ → π̄` for all `π₀`
   (`positive_matrix_converges`), and this is not necessary (`[0 1; 1/2 1/2]` converges,
   `positive_matrix_not_necessary`).

4. **p. 190, the definition of aperiodicity.** "State `i` is aperiodic if there is some `n` such
   that for all `n′ ≥ n`, `Pr(x_{n′} = x̄ᵢ | x_n = x̄ᵢ) > 0`." For a time-homogeneous chain this is
   `(P^{n′−n})ᵢᵢ > 0` for all `n′ ≥ n`, i.e. `(Pᵐ)ᵢᵢ > 0` for every `m ≥ 0`
   (`aperiodic_printed_iff`), which forces `Pᵢᵢ > 0` and is much stronger than aperiodicity. The
   intended definition conditions on `x₀ = x̄ᵢ`: `(P^{n′})ᵢᵢ > 0` for all `n′ ≥ n` (`ak_Aperiodic`).
   Counterexample: in `[0 1; 1/2 1/2]` state `0` is aperiodic in the corrected sense but not in the
   printed one (`aperiodic_printed_counterexample`). The convergence theorem is proved with the
   corrected definition (`markov_irreducible_aperiodic_converges`).

5. **p. 195, the elasticity of intertemporal substitution.** "The consumption Euler equation for
   power utility implies `d log[c_{t+1}/c_t]/dR_{t+1} = 1/σ`." The derivative with respect to
   `R` is `1/(σR)`; the elasticity `1/σ` is the derivative with respect to `log R`, as in
   Chapter 4 (`eis_crra`; `eis_printed_counterexample`: at `σ = 1`, `R = 2` the printed derivative
   is `1/2`).

6. **p. 201, the Euler equation after the envelope condition.** The book:
   `u′(C) = β Σ_{A′} π(A′|A)[u′(C′)f₂(A, K)]`. The marginal product is evaluated next period:
   `f₂(A′, K′)`, as in (7.16) (`rb_euler`, `eq_7_16`). Counterexample to the printed equation:
   with `u = log`, `β = 1/2`, `f(A, K) = aK`, two states with `a = (1, 2)` and state `1` reached
   from state `0` for sure, `V(s, K) = 2 log K + v_s` and `g(s, K) = aK/2` solve the Bellman
   equation (`recEx_bellman`); at `(0, 1)` (7.16) holds with both sides `2`, while the printed
   right-hand side is `1` (`rec_euler_printed_counterexample`).

7. **p. 202, the linearised (7.16).** The first display omits the factor `β` that appears in the
   second; the equations are stated with `β` (`lin_match`, `lin_Keq`, `lin_Aeq`).

8. **p. 213, the incomplete-markets first-order condition and Euler equation.** The book states
   `u′(c)q = βE[V₁(a′, y′)|y]` and `u′(c) = (1 + r)βE[u′(c′)|y]` as equalities, although the
   borrowing limit `a′ ≥ a̲` can bind (and the text then says low-income consumers hit it). The
   correct conditions are `u′(c)q ≥ βE[V₁(a′, y′)|y]` and `u′(c) ≥ (1 + r)βE[u′(c′)|y]`, with
   equality when `a′ > a̲` (`im_foc`, `im_euler`); at the limit the envelope argument gives only
   `V₁ ≥ u′(c)` (`im_envelope_boundary`). (The existence of the upper bound `ā` of the ergodic set
   also needs `β(1 + r) < 1`, which the text does not state; that claim is read off Figure 7.4 and
   is deferred.)

9. **p. 840, Definition 16.** The printed Bellman equation
   `V(k, K, ω) = max u(…) + βV(k′, G*(K, ω), ω′)` leaves `ω′` free: the expectation
   `Σ_{ω′} P(ω, ω′)V(k′, G*(K, ω), ω′)` given `ω` is missing, and "∀(k, K)" should be "∀(k, K, ω)"
   (`definition_16`, with an equilibrium `definition_16_example` and the functional Euler equation
   `definition_16_euler`).

10. **p. 840, Appendix 7.A.2.** The statement reads `E₀{Eₜ[x_τ(ωᵗ)]}`; the argument is `ω^τ`. In
    the first two displays the inner expectation is written `E_τ[x_τ(ω^τ)]` and the text says
    "replace the conditional expectation `E_τ`"; it is `Eₜ` (conditional on `ωᵗ`), for which the
    computation is correct (`appendix_7A_2`, `appendix_7A_2_sum`, `appendix_7A_2_root`).

## Departures

11. **Event trees.** The event tree is Miao's `BPTree`: finitely many events per date and every
    history has positive probability.

12. **The AR(1) and (7.5).** The processes start at a given `x₀` (`t ≥ 0`), so the book's infinite
    moving average appears as a finite sum plus `ρᵗ(x₀ − µ)` (`ar1_ma`), and the moments are proved
    for every covariance-stationary solution (`ar1_moments`, `eq_7_6`).

13. **Portfolio homogeneity.** The book reads the homogeneity off the first-order condition; it is
    proved for any maximiser by scaling the objective (`portfolio_crra_scale`,
    `portfolio_cara_invariant`), without uniqueness or interiority.

14. **Planner on the tree.** Plans have positive consumption and convergent utility; (7.13) is
    proved at histories with `K_{t+1} > 0` (`eq_7_13`). The book only says that a transversality
    condition "must be added"; its sufficiency is proved with tangent (concavity) hypotheses
    (`pt_euler_tvc_optimal`). The closed form needs `0 < α < 1`, `0 < β < 1` and TFP in a compact
    subset of `(0, ∞)` (so that utility converges) (`pt_log_optimal`).

15. **Recursive problems.** The existence and differentiability of `V` are hypotheses, as in the
    book; choices are interior (`rb_Bellman`). The envelope condition is derived from the Bellman
    equation for a differentiable `V` (`rb_envelope`).

16. **Linearisation.** The coefficient equations are proved as exact algebra; the `K̂` equation is
    shown to be the derivative of the deterministic functional Euler equation at the steady state
    (`lin_K_eq_of_policy`, from Chapter 4's (4.29)), and the roots of (7.17) are Chapter 4's
    `slopeRoot`/`slopeRootOther` (`eq_7_17_roots`). The positivity of the denominator of `g_A`
    (`lin_gA_denominator_pos`) is added.

17. **Sequential trading.** The no-Ponzi condition (7.25) is used in its date-0 aggregated form
    (`seq_ad_budget_le`); the equivalence of sequential and Arrow–Debreu equilibria, which the book
    asserts with a sketch, is formalised through its key step, the consolidated budget
    (`seq_consolidated`, `seq_ad_budget_eq`), and the maps between the two price systems
    (`seq_price_map`, `seq_price_of_ad`). Of the two clearing conditions of Definition 14 ("one of
    these implies the other"), asset clearing ⇒ goods clearing is proved
    (`definition_14_goods_of_assets`); the converse holds only together with the later budgets and
    is not formalised.

18. **Definition 15.** The household's problem includes `k_{t+1} ≥ 0` (the book assumes it does
    not bind); the equilibrium results use `k_{t+1} > 0`.

## Figure 7.4 (Markov income)

19. **Figure 7.4(A), the decision rules (p. 214).** The book reads the properties of `g(a, y)`
    off a computed figure for a two-state income process. They are proved for any finite-state
    Markov income process under the standing assumptions of §7.6 (`imf_Standing`: `β ≥ 0`,
    `1 + r > 0`, `β(1 + r) < 1`, `P` stochastic, `u′ > 0` strictly decreasing, `V(·, y)`
    differentiable on `[a̲, ∞)` with nonincreasing derivative, i.e. concave; the book assumes the
    existence and differentiability of `V`): `g` and `c` are nondecreasing in assets with slopes in
    `[0, 1 + r]` and `[0, 1]` (`imf_g_mono`, `imf_c_mono`, `imf_g_lipschitz`, `imf_c_lipschitz`).
    The low-income rule's position is proved for the state with the lowest consumption at `a`:
    `g(a, y) ≤ a`, strictly for `a > a̲` (`imf_min_dissave`); it is the low-income state whenever
    consumption increases with income, which Markov income alone does not guarantee. The bound
    `ā` needs more than the text states: with `r > 0` it is proved under
    `β(1 + r)u′(c) < u′(c + D)` for large `c` (`D` the income spread; it holds whenever
    `u′(c + D)/u′(c) → 1`, e.g. CRRA, `imf_crra_spread`) (`imf_abar_exists`); with `r < 0` no
    condition is needed (`imf_abar_exists_neg`); `r = 0` is not covered. The figure's `ā` satisfies
    `g(a, y) < a` for all `a ≥ ā` in every state; `[a̲, ā]` is invariant
    (`imf_ergodic_invariant`), and "they will continuously spend down their assets ... until
    their assets reach `ā`" holds in the form: along every income history, assets are in
    `[a̲, ā]` from some date on (`imf_enters_ergodic`). "The consumer spends down their savings
    until it reaches the borrowing constraint": the constraint binds on an interval `[a̲, a̲ + δ)`
    in the lowest-consumption state, so the limit is reached exactly (`imf_binds_near_limit`, with
    `u′` continuous).

20. **Figure 7.4(A), the high-income rule (p. 214).** "When income is high, the consumer
    accumulates savings up to the point `ā` where the upper line crosses the 45-degree line" and
    "the decision rule of high-income consumers has ... an intercept above the 45 degree line"
    describe the parameters behind the figure, not the model. In the solved two-state Markov
    economy of `IncomeFluctuationExample` (`u(c) = c + log c`, `β = 1/4`, `r = 1`, `y ∈ {1, 2}`,
    `P = [3/4 1/4; 1/4 3/4]`), which satisfies every assumption, the constraint binds in both
    states, `g(a, y) = a̲ < a` for all `a > a̲`, and the ergodic set is `{a̲}`
    (`imf_example_no_accumulation`).

21. **Figure 7.4(B), the stationary distribution (p. 215).** "In the long run, the distribution
    will converge to a stationary distribution" is given without argument. It is proved for the
    joint distribution of `(a, y)` on `[a̲, b] × S` for every `b ≥ ā` (assets above `b` are covered
    path by path by correction 19), under the assumptions of correction 19 with `r > 0`, `u′`
    continuous and a transition matrix with positive entries (`imf_stationary`): there is a unique
    stationary distribution and the distribution converges to it in total variation, at a
    geometric rate, from every initial distribution. The proof does not use the monotone mixing
    condition (SLP Theorem 12.12, Miao Theorem 3.3.5, used by Miao's Proposition 8.3.1 for i.i.d.
    income): on `(a, y)` the transition is monotone only if the savings rule is increasing in
    income and `P` is stochastically monotone, which Markov income does not imply. Instead the
    binding constraint makes `(a̲, y₀)` an atom reached from every state in `N` steps with
    probability at least `pᴺ` (`imf_kernel_hit`), which is Miao's Condition M (Example 3.3.1),
    and Theorem 3.3.1 gives the conclusion (`imf_kernel_stationary`). The model's hypotheses are
    satisfied by a solved instance (`imf_example_stationary`).
