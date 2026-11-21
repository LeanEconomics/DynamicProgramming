# Corrections and departures: Miao Chapter 9

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 9,
Linear-Quadratic Models, pp. 291–326. Lean names are relative to `Miao.LinearQuadratic`.
Every book item is located in the [source map](source-map.md).

## §9.1–§9.3 and Exercises 9.1, 9.2, 9.4

### §9.1

1. **Controllability as reachability needs `r ≥ nₓ`.** The book says controllability means that
   any target can be reached from any `x₀` "for any `r > 0`", and calls this equivalent to
   Definition 9.1.2. True: the Gramian condition holds iff every target is reachable in `r` steps
   for every `r ≥ nₓ` (`definition_9_1_2_iff`). False for small `r`: the shift
   `A = [[0, 0], [1, 0]]`, `B = e₁` is controllable but `e₂` cannot be reached from `0` in one
   step (`ls_controllable_not_reach_one`).
2. **Observability as reconstruction needs `r ≥ nₓ − 1`.** Likewise `x₀` is determined by
   `y₀, …, y_r` (given inputs and shocks) for every `r ≥ nₓ − 1` iff `(A, G)` is observable
   (`definition_9_1_3_iff`), but not "for any `r > 0`": for the 3-state shift with `G = e₃'`,
   `y₀, y₁` do not determine `x₀` (`ls_observable_not_two_outputs`). Determination is read as
   injectivity of `x₀ ↦ (y₀, …, y_r)` for given `u`, `ε` (the outputs (9.2) use `w_t = u_{t−1}`).
3. **The error equation below (9.3).** The book prints
   `Δ_{t+1} = (A − AKG)Δ_{t−1} + Cε_{t+1} + AKDε_t`. Subtracting (9.3) from (9.1) gives
   `Δ_{t+1} = (A − AKG)Δ_t + Cε_{t+1} − AKDε_t` (`eq_9_3_error`). The printed form is false: with
   `A = 2` and all other matrices zero, `Δ_t = 2ᵗ`, so `Δ₂ = 4 ≠ 2Δ₀` (`eq_9_3_misprint`).
   "`Δ_t` is stable iff `A − AKG` is stable" is proved in the direction used (the noise-free
   error vanishes when `A − AKG` is stable, `eq_9_3_tendsto`). That detectability yields an
   updating rule of the form (9.3) is proved for invertible `A` (`K = A⁻¹J`,
   `definition_9_1_4_rule`); the general case and the derivation of (9.3) itself (Section 10.1.1)
   are not formalised.
4. **Controllability implies stabilizability** is proved by the controllable case of
   Proposition 9.3.1 with `Q = R = I` (`controllable_stabilizable`), not by pole placement.
5. **Assumption 9.1.1 and the shock law.** `LSAssumption911` is the book's conditional
   statement, and the computation of p. 296 is proved in that setting for `F_t`-measurable,
   square-integrable `y` and square-integrable `ε_{t+1}` (`ls_condExp_quad`). The Bellman
   recursion of Proposition 9.2.1 integrates against the conditional law of `ε_{t+1}`, modelled
   as a probability measure `ν` on `ℝ^{nε}` with mean `0` and second moments `I` (`LSShockLaw`),
   the same for every date.

### §9.2

6. **Proposition 9.2.1: the value function is the Bellman recursion.** `V_t` is defined by
   backward induction, `V_T(x) = −x'P_Tx` and
   `V_t(x) = sup_u {−r_t(x, u) + β∫V_{t+1}(A_tx + B_tu + C_te) dν(e)}`, as in the book's proof;
   `proposition_9_2_1` shows the supremum is attained, exactly at `u = −F_tx`. For the
   deterministic problem the feedback rule is also shown optimal among all control sequences
   (`ls_finite_seq_optimal`). Only `β ≥ 0` is used (the book has `β ∈ (0, 1]`; strict positivity
   is needed only for uniqueness along sequences).
7. **Certainty equivalence** is stated as: `P_t`, `F_t` do not depend on `C_t`, `d_t = 0` when
   `C_t = 0`, the stochastic value is the deterministic one minus `d_t`, and the maximisers
   coincide (`certainty_equivalence`).
8. **Footnote 1** (differential rules) is replaced by completing the square; the first-order
   condition and the first variation of the objective are `ls_foc` and `ls_first_variation`.

### §9.3

9. **Discounting and the normalisation.** Propositions 9.3.1–9.3.2 are stated, as in the book,
   for `S = 0`; the reduction of `S ≠ 0` is Exercise 9.1 (`ex_9_1`). The discounted operator
   (9.11) with `S = 0` is the undiscounted Riccati map of `(√βA, √βB)` (`toSS_riccati`), and the
   proofs work in that form (`ls_riccati_main`). Only `β ≥ 0` is used; `Nonempty X` (`nₓ ≥ 1`)
   is assumed in the infinite-horizon theorems.
10. **`P(s)` is weakly, not strictly, increasing.** The proof of Proposition 9.3.1 claims
    `V_{s+1}(x) < V_s(x)` and `P(s + 1) > P(s)` for all `s`. True: `P(s) ≤ P(s + 1)`
    (`ls_P_mono`), and `V₁ < V₀` for `x ≠ 0` (`ls_P_one`). False in general: for `A = 0`,
    `T(P) = Q` for every `P`, so `P(2) = P(1)` (`ls_P_mono_not_strict`).
11. **Convergence of `P(s)`.** Monotone bounded quadratic forms converge, and symmetric matrices
    converge with their quadratic forms (`ls_exists_tendsto_of_quad`); the limit solves (9.12) by
    continuity of `T` on the positive semidefinite cone (`ls_tendsto_riccati`). In the
    controllable case the bound is the cost of steering `x₀` to `0` in `nₓ` steps
    (`ls_iter_bdd_of_controllable`).
12. **The upper bound of p. 300.** The book writes
    `P(s) ≤ ∑_{j<s} βʲΓ'ʲ(Q + F'RF)Γʲ + Γ'ˢP(0)Γˢ → P`. The bound holds with the remainder
    `βˢΓ'ˢP(0)Γˢ` (`ls_P_le_policy`), which tends to `0` because `√βΓ` is stable; the printed
    remainder `Γ'ˢP(0)Γˢ` need not tend to zero (with `A = 1`, `B = 0`, `β = 1/4`, `Γ = 1` and
    the remainder is `P(0)` for every `s`, `ls_P_le_policy_misprint`).
13. **Proposition 9.3.2's limit system.** The book says `x_t` "enters a system" with `Lx_t = 0`,
    `x_{t+1} = √βAx_t`. This is made asymptotic: `Lx_t → 0` and `Fx_t → 0`; with observability,
    `x_{t+j} − (√βA)ʲx_t → 0` for each `j`, so the observability Gramian applied to `x_t` tends
    to zero (`ls_detects_of_observable`); with detectability, `x_{t+1} = (√βA − HL)x_t + w_t`
    with `w_t → 0` and `√βA − HL` stable (`ls_detects_of_detectable`,
    `ls_tendsto_zero_of_stable_input`).
14. **The side condition replacing detectability** (p. 301) is proved as: if every path of the
    closed loop satisfies `∑βᵗx_t·x_t < ∞` then `√βΓ` is stable (`ls_stable_of_side_condition`).
15. **The infinite-horizon value function.** "These limits give the value function and the
    optimal policy" is proved for the deterministic problem with `S = 0`: every control sequence
    costs at least `x₀'Px₀` and `u = −Fx` costs exactly `x₀'Px₀` (`ls_infinite_value`); and,
    with the side condition, for any `S` given a symmetric solution of (9.12)
    (`ls_verification`). With uncertainty and `S ≠ 0` it is the Bellman equation for
    `V = −x'Px − d` (`eq_9_16_9_17`), which needs `β < 1` for
    `d = (1 − β)⁻¹β tr(PCC')` (the book allows `β ∈ (0, 1]`); `d(s) → d` also needs `β < 1`
    (`ls_dIter_tendsto`).
16. **Policy improvement.** The condition "eigenvalues of `A − BF_j` less than `1/√β` in modulus"
    is used as stability of `√β(A − BF_j)` (`ls_policy_lyapunov`).
17. **The envelope condition.** The book prints
    `∂V(x_t)/∂x_t = Qλ_t + Su_t + βA'E_tλ_{t+1} = λ_t`. The first-order condition in `x` is
    `λ_t = Qx_t + Su_t + βA'E_tλ_{t+1}` (`Qx_t`, not `Qλ_t`), satisfied by `λ_t = Px_t`
    (`ls_lagrange`); and for `V(x) = −x'Px − d`, `V(x + h) = V(x) − 2λ·h − h'Ph`
    (`ls_envelope`), so `∂V/∂x = −2λ_t` with the multiplier scaling `2β^{t+1}λ_{t+1}`; `λ_t` is
    the shadow price up to this factor.

### Exercises

18. **Exercise 9.1: `R⁻¹S'`, not `R⁻¹S`.** With `S` of size `nₓ × n_u`, the transformation is
    `ũ_t = u_t + R⁻¹S'x_t` (the printed `R⁻¹Sx_t` is not conformable unless `nₓ = n_u`). It gives
    `Q̃ = Q − SR⁻¹S'`, `Ã = A − BR⁻¹S'`, `S̃ = 0`, `T̃ = T`, `F = F̃ + R⁻¹S'` (`ex_9_1_loss`,
    `ex_9_1_transition`, `ex_9_1`).
19. **Exercise 9.2.** The printed loss `(x_t − x*)'[[Q, S], [S', R]](u_t − u*)` is read as the
    quadratic form of the stacked vector `[x_t − x*; u_t − u*]` (`ex_9_2_loss`). The solution is
    given through the augmented state `z_t = [x_t − x*; 1]` (`augment`, `ex_9_2_transition`) for
    `β < 1` (with `β = 1` the constant state makes the value infinite in general): given a
    positive semidefinite solution `P̃` of the augmented Riccati equation, `u = u* − F̃z` is the
    unique Bellman maximiser (`ex_9_2`). Existence of `P̃` is not derived (Propositions 9.3.1–9.3.2
    do not apply directly: `Q̃` is singular).
20. **Exercise 9.4 (Hall).** Here `Q − SR⁻¹S' = 0`, so Propositions 9.3.1–9.3.2 do not apply and
    (9.12) has two positive semidefinite solutions when `βR² > 1`: `P = q ww'`
    (`ex_9_4_riccati`) and `P = 0` with rule `c = b` (`ex_9_4_zero_solution`,
    `ex_9_4_two_solutions`). The rule `c = −Fx` of `P = q ww'` (`ex_9_4_rule`; Hall's martingale
    rule when `βR = 1`, `ex_9_4_martingale`) is optimal among plans with `βᵗx_t'Px_t → 0`
    (`ex_9_4_optimal`), and solves the stochastic Bellman equation (`ex_9_4_bellman`, `β < 1`).
    The rule `c = b` attains the infimum `0` only by borrowing at rate `R`, which the side
    condition (9.10) excludes when `βR² > 1` (this remark is not formalised). The shock is only required to have mean zero and
    unit variance (Gaussianity is not used).

## §9.4–§9.5

### §9.4 Optimal policy under commitment

21. **Expectations in the first-order conditions, pp. 306 and 309.** The Lagrangians are
   written along one realised (perfect-foresight) path, truncated at a horizon `T`; their exact
   variations give the first-order conditions with `μ_{t+1}` in place of `E_tμ_{t+1}`
   (`eq_foc_9_4`, `eq_9_25`, `eq_9_26`, `eq_9_27`). The conditioning step (the multiplier enters
   linearly) is not formalised, as in Chapter 2's `LQKlein`.
22. **The initial multiplier term, p. 306.** The book writes `μ_{z0}'D̄(z₀ − z̄₀)`, which is not
   dimensionally consistent; `cpLagrangian` uses `μ_{z0}'(z₀ − z̄₀)`. With `μ_{y0} = 0` and
   `D = [I 0; D₂₁ D₂₂]` the date-0 condition then has the book's form (`cp_init_eq_Dbar`,
   `cp_grad_eq`). The garbled `D̄` is read as `[D 0]`, the only reading consistent with (9.22).
23. **Saddle path and recursive form, pp. 307–308.** The deterministic statement
   (`cp_saddle_path`, `cp_time_inconsistency`) is the perfect-foresight form with a given bounded
   shock path. The recursive form (`cp_recursive_form`) uses Chapter 2's stochastic Klein theorem
   and delivers complex coefficient matrices (the QZ form is complex); that they are real is not
   proved.
24. **(9.29), p. 310.** The roots satisfy `0 < a₁ < 1 < a₂` only when `κ ≠ 0` (`eq_9_29`, with
   `λ > 0`, `0 < β < 1`); for `κ = 0` the roots are `1` and `1/β` (`eq_9_29_kappa_zero`).
25. **The `5 × 5` system, p. 310: misprint.** The fourth row of the left matrix is printed
   `(0, β, 0, 0, 0)`; the row that encodes (9.23) is `(0, 0, 0, β, 0)` (`example_9_4_2_system`).
   With the printed row the system does not imply (9.23)
   (`example_9_4_2_printed_row_false`).
26. **Expected paths in Example 9.4.2, pp. 310–311.** (9.28), the rule, its uniqueness and the
   solution are proved along the expected path `E_t z_{t+j} = ρʲz_t` (`eq_9_28`,
   `ex942_unique_bounded`, `ex942_solution`); the one-step conditional expectation of the rule is
   computed for any integrable mean-zero shock (`ex942_rule_expected`). Uniqueness needs the
   solution bounded and `|ρ| ≤ 1` (`ex942_unique_bounded`), which the book leaves implicit in the
   forward inversion of `L⁻¹ − a₂`.

### §9.5 Optimal discretional policy

27. **(9.36), p. 312.** The lower block of (9.18) is `D₂₁E_t z_{t+1} + D₂₂E_t y_{t+1} = …`; the book
   drops `D₂₁E_t z_{t+1}`, so `D_yy M_{t+1}` in `H_zt`, `H_ut` and in the invertibility condition
   must be `G = D₂₁ + D₂₂M_{t+1}` (`eq_9_37`). The book's formulas hold when `D₂₁ = 0`
   (`eq_9_37_book`); with `D₂₁ ≠ 0` its rule violates the constraint (`eq_9_36_false`). (9.35) also
   takes `C = I`, as `CPDisc` does.
28. **Step 2, p. 313.** `S*_t = Q_zy H_ut + S_z + H_zt S_y` lacks the transpose (`H_zt'S_y`) and the
   cross term `H_zt'Q_yy H_ut` (`step2_book_S_false`); `R*_t = R + H_ut'Q_yy H_ut + H_ut'S_y` lacks a
   factor 2 on `H_ut'S_y` (`step2_book_R_false`). The correct (symmetric) forms are
   `R* = R + H_u'Q_yy H_u + H_u'S_y + S_y'H_u`, `S* = Q_zy H_u + S_z + H_z'S_y + H_z'Q_yy H_u`
   (`eq_step2`, with `Q_yy` symmetric). `Q*_t = Q_zz + H_z'Q_yy H_z + 2Q_zy H_z` is right as a
   quadratic form (`cp_Qbook_quad`) but not symmetric; we use `Q_zy H_z + H_z'Q_zy'`.
29. **(9.41), p. 314.** The printed `V_t` (with `−2S*F`) gives the right value as a quadratic form
   (`eq_9_41`) but is not a symmetric matrix, while the gain (9.40) at the next step presumes a
   symmetric `V_{t+1}`. The iteration uses the symmetrised `cpVnext`, with the same quadratic form
   (`cp_Vnext_quad`) and symmetric when `Q*`, `R*`, `V_{t+1}` are (`cp_Vnext_symm`). (9.40) needs
   `R* + βB*'V_{t+1}B*` positive definite for the first-order condition to give the minimum
   (`eq_9_40`).
30. **Definition 9.5.1, p. 311.** Part (i) takes `E_t y_{t+1} = f(z_t)` as given, but the
   derivation (9.32)–(9.33) has the policymaker take the private sector's rule
   `y_{t+1} = M_{t+1}z_{t+1}` as given, so that `u_t` moves `E_t y_{t+1}` through `E_t z_{t+1}`.
   `IsMPE` formalises the definition as the derivation uses it, with (ii) `f(z_t) = ME_t z_{t+1}`
   built into the constraint `Feasible`; the expectation `E_t J(z_{t+1})` is evaluated through the
   shock's mean and covariance (`cp_expected_quadratic`).
31. **Convergence of the iteration, pp. 314–315.** "Iterating this process until convergence gives
   `V` and `M` in a Markov perfect equilibrium" is not proved in the book; we prove that a fixed
   point of the Step 1–3 map is a Markov perfect equilibrium (`cp_mpe_of_fixed_point`), not that
   the iteration converges.
32. **Example 9.5.1, p. 315.** The forward solution needs the expected inflation path bounded
   (`ex951_forward`); the Markov perfect equilibrium is proved to exist and to be unique among
   affine rules (`example_9_5_1`, `example_9_5_1_unique`), for `0 < β < 1`, `λ > 0`, `|ρ| ≤ 1`.
33. **Commitment versus discretion.** The book only remarks that discretionary policy is time
   consistent; the comparison `cp_commitment_vs_discretion` (commitment inflation
   `a^{t+1}κx*/(1 − βa) → 0` without cost-push shocks; discretion has the constant bias
   `λκx*/(κ² + (1 − β)λ)`) is derived from Examples 9.4.2 and 9.5.1.

## §9.6 and Exercises 9.3, 9.5

### Belief distortions and the two problems

34. **Bounded likelihood ratios.** The book computes with `E[M_t ln M_t]` and the decomposition of
   entropy without integrability conditions. We assume `0 ≤ m_{t+1} ≤ K` (`RCRatios`), which
   makes every expectation finite; the martingale property, `E^Qφ = E[M_tφ]`, the entropy
   identities and (9.45) are proved in that setting (`rc_martingale`, `rc_distorted_integral`,
   `rc_entropy_decomp`, `rc_discounted_entropy`). The general LQ results do not rely on this
   (the Gaussian worst-case ratio is unbounded): the inner problem there is treated through the
   Gibbs principle (`eq_9_47_9_48`) with only `E exp(−V/θ) < ∞`.
35. **The distorted measure and (9.46) over a finite horizon.** `Q` is constructed on `ℱ_t` as
   `Q_t = M_t·P` (`rcQ`), consistent across horizons (`rc_distorted_consistent`), and its
   Radon–Nikodym derivative is `M_t` (`rc_rnDeriv`); the measure on the full path space (a
   projective limit) is not constructed. Accordingly (9.46) is proved over a finite horizon `T`
   with `Q = Q_T` (`eq_9_46`).
36. **θ as a Lagrange multiplier** is proved in the standard sufficiency form: a minimiser of the
   multiplier objective satisfying complementary slackness solves the constraint problem, and the
   multiplier value minus `θη` is a lower bound for every `θ ≥ 0` (`rc_lagrange`,
   `rc_weak_duality`). The existence of a multiplier for a given `η` (strong duality) is not
   formalised.
37. **θ → ∞.** "The multiplier problem converges to the standard control problem" needs continuity
   of the objective in the distortion. We assume the Pinsker-type bound
   `|J(u, m) − J(u, m₀)| ≤ c√ent(m)` (true for bounded rewards by Pinsker's inequality, not proved
   here) and prove `W₀ − c²/(4θ) ≤ W(θ) ≤ W₀` and `W(θ) → W₀` (`rc_mult_tendsto`). The LQ case is
   Exercise 9.3 (item 44).

### The recursive problem

38. **The first-order condition (p. 320).** The book prints `m*(ε) = −V(f(x, u, ε))/θ + λ`. The
   derivative of `m ↦ mV + θ m ln m` is `V + θ(ln m + 1)`, so the condition is
   `ln m*(ε) = −V(f(x, u, ε))/θ + λ` (`eq_9_47_foc`, `eq_9_47_log`), which gives (9.47). The
   printed rule is false: for the two-point law `(δ_true + δ_false)/2` with `W(true) = 0`,
   `W(false) = 4θ`, normalising gives `λ = 3` and the printed "likelihood ratio" equals `−1` at
   `false` (`eq_9_47_misprint`).
39. **(9.47)–(9.48) are proved as the Gibbs variational principle** over likelihood ratios with an
   integrable objective (`rcAdm`): `m*` is the unique minimiser a.e. and the minimum is
   `−θ ln E exp(−V/θ)` (`eq_9_47_9_48`); (9.49) follows (`eq_9_49`). The book's integral
   `∫ m ln m π` is not defined for every `m`; admissibility requires it.

### The LQ model with Gaussian shocks

40. **Gaussian integrals.** The LQ results are stated for any shock law with the Gaussian moment
   generating identity `E exp(½ε'Kε + b'ε) = det(I − K)^{−1/2} exp(½b'(I − K)⁻¹b)` for symmetric
   `K` with `I − K > 0` (`RCGaussian`). The IID standard normal shock
   `Measure.pi fun _ => gaussianReal 0 1` satisfies it (`rc_gaussian_std`: rotation by the
   orthogonal eigenvector matrix of `K`, `rc_std_map_eigen`, then one-dimensional Gaussian
   integrals, `rc_gauss_1d`), so the book's results hold for it (`eq_9_51_9_55_std`,
   `rc_robust_bellman_std`, `rc_R_quad_std`, `ex_9_5_bellman_std`). In the entropy computation
   (p. 323) "π̂ is normal with mean `w` and covariance `Σ`" enters through the explicit density in
   the log-likelihood ratio and through the two moments of the law integrated against
   (`RCMoments`, `eq_9_56`, `rc_R_first_line`); the worst-case density is proved proportional to
   the normal density with mean `w*` and covariance `K⁻¹` (`rc_worst_density`).
41. **Positive definite, not nonsingular (p. 321).** The book says "we must assume that the matrix
   `I − θ⁻¹C'PC` is nonsingular". It must be positive definite: then (and only then) the worst-case
   kernel is integrable and `π*` is a normal density (`rc_worst_density`, `rc_R_quad`). With
   `θ = 1`, `C = 1`, `P = 2` (scalar), `I − θ⁻¹C'PC = −1` is nonsingular but
   `exp(−ε²/2)exp(ε²)` is not integrable (`rc_nonsingular_not_enough`); in the deterministic
   problem a direction of negative curvature of `θI − C'PC` makes the minimisation unbounded below
   (`rc_breakdown`). This is the breakdown point.
42. **The Bellman equation and (9.55).** The robust Bellman equation is proved for `0 ≤ β < 1`,
   `R > 0`, `P ≥ 0` (`eq_9_51_9_55`); `β < 1` is needed for the constant (9.55). "Matching
   coefficients" is proved as the converse (`rc_bellman_converse`, which uses `Q` symmetric).
   The book's display of `R(V)` writes `V(f(x, u, ε), u)`; `V` has one argument.
43. **A sign in the entropy computation (p. 323).** The book prints
    `−∫½(ε − w)'Σ⁻¹(ε − w)π̂(ε)dε = ½ tr(I)`. The integral `∫(ε − w)'Σ⁻¹(ε − w)π̂ = tr(I)`, so the
    left side is `−½ tr(I)` (`rc_moment_half`, `rc_moment_trace_inv`); the printed value differs
    whenever `nε ≥ 1` (`rc_moment_sign_misprint`). (9.56) itself is correct (`eq_9_56`).

### Exercises

44. **Exercise 9.3** is proved for families of robust solutions that converge: if `P_θ ≥ 0` solve
    `P_θ = T(D_θ(P_θ))` with `θI − C'P_θC > 0` and `P_θ → P`, then `P` solves (9.12), the robust
    gain and `D_θ(P_θ)` converge to the standard ones, and `d_θ → (1 − β)⁻¹β tr(PCC')`
    (`ex_9_3`); under Proposition 9.3.1's hypotheses `P` is the unique positive semidefinite
    solution (`ex_9_3_unique`). Convergence of `P_θ` itself (e.g. from boundedness) is assumed,
    not derived. The constant uses `tr Y ≤ −ln det(I − Y) ≤ tr Y/(1 − tr Y)`
    (`rc_log_det_bounds`).
45. **Exercise 9.5** is solved in the normalisation of §9.6: the reward `−(c − b)²` is
    `−½(x'Qx + u'Ru + 2x'Su)` with Hall's `Q, R, S` doubled (`rcHallRobust`). For `βR² > 1` and
    `θ > 2k`, `k = σ²R²/(R − ρ)²`, the robust Riccati solution is `P = 2q_θww'` with
    `q_θ = θ(βR² − 1)/(θβR² − 2k)` and the robust rule is
    `c = b + q_θ(Ra + Ry/(R − ρ) + μR/(R − 1) − μR/(R − ρ) − bR/(R − 1))` (`ex_9_5`,
    `ex_9_5_rule`); it solves the robust Bellman equation under `RCGaussian` (`ex_9_5_bellman`),
    in particular for a standard normal income shock (`ex_9_5_bellman_std`).
    The solution is the robust analogue of the `P = q ww'` solution of Exercise 9.4 (the second
    solution `P = 0` of Exercise 9.4 also has a robust analogue, not treated). The breakdown point
    is `θ = 2k` (`ex_9_5_breakdown`), and `q_θ → 1 − 1/(βR²)` (`ex_9_5_limit`).
