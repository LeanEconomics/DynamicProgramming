# Corrections and departures: Miao Chapter 10

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 10, Control
under Partial Information, pp. 327–346. Lean names are relative to `Miao.PartialInformation`. Every
book item is located in the [source map](source-map.md).

## §10.1.1 (Kalman filter), §10.3 and Exercises 10.1–10.5

1. **Reading of the filter (pp. 328–333).** The book states the filter for Gaussian conditional
   distributions. What is proved is the linear-projection (second-moment) version on an
   arbitrary probability space: shocks square integrable, mean zero, `Eε_sε_t' = δ_{st}I`,
   `x₀` with mean `x̄₀` and covariance `Σ₀`, uncorrelated with the shocks; controls and
   measurement inputs are arbitrary random vectors, because the estimation error does not
   depend on them (`KFSystem.kf_err_control_free`). The statements that conditional laws are
   normal, that conditional and unconditional covariances agree, and that the innovations are
   *independent* normals are not formalised; their second-moment content (mean zero, covariance
   `Ω_{t|t−1}`, mutually uncorrelated innovations, orthogonality of errors to past innovations,
   optimality among predictors affine in the innovations) is (`KFSystem.kf_moments`,
   `KFSystem.eq_10_8`, `KFSystem.kf_innov_orth`, `KFSystem.kf_err_orth`, `KFSystem.eq_10_12`).
2. **(10.9), p. 330, and every formula using it.** `E[(x_t − x̂_{t|t−1})ε_t'] = C_{t−1}` (the
   loading of `ε_t` in `x_t = A_{t−1}x_{t−1} + B_{t−1}u_{t−1} + C_{t−1}ε_t`), not `C_t`; and it is
   `0` at `t = 0`, since `x₀` is independent of `ε₀` (`KFSystem.eq_10_9`, `KFSystem.Cl`;
   counterexample to the printed formula at `t = 0`: `kf_cross_book_false`). So the `C_t` in
   (10.8), (10.10), (10.11), in `Σ_{t|t} = (I − K_tG_t)Σ_{t|t−1} − K_tD_tC_t'` and in the two
   Riccati equations of p. 333 is `C_{t−1}` (and `0` at `t = 0`).
3. **(10.11) → `Σ_{t|t} = (I − KG)Σ − KDC'`, p. 332.** The simplification at the Kalman gain
   needs `Ω_{t|t−1}` invertible (`eq_10_11_gain`, `kf_filtCov_eq`; hypothesis `hΩ`). (10.11)
   itself holds for every gain (`KFSystem.eq_10_11`).
4. **The first-order condition, p. 331.** The printed derivative
   `−2(Σ_{t|t−1}G_t' + D_tC_t') + 2K_t(G_tΣG_t' + D_tD_t' + G_tC_tD_t' + D_tC_t'G_t)` has the
   non-conformable terms `D_tC_t'` (it is `C_tD_t'`) and `D_tC_t'G_t` (it is `D_tC_t'G_t'`). The
   correct expansion `tr Σ(K + sΔ) = tr Σ(K) + 2s tr(Δ(ΩK' − M')) + s² tr(ΔΩΔ')` is
   `kf_trace_perturb`, the condition is `eq_10_10_foc`, and the minimisation is proved directly
   by completing the square, in the Loewner order and in trace, with uniqueness (`eq_10_10`,
   `KFSystem.eq_10_10_random`).
5. **Step 1, p. 332.** The `Q` in `Σ₀ = AΣ₀A' + Q` is undefined in the text; it is the state
   noise covariance `CC'`. For stable `A` the stationary mean `x̂₀ = Ax̂₀` is forced to be `0`
   (`kf_step1_mean`), and `I − A ⊗ A` is invertible (`kf_step1_cov`).
6. **The stationary filter, pp. 333–334.** The book asserts `Σ_t → Σ`, `K_t → K` without
   conditions. Proved (`kf_steady_state`) for uncorrelated noise `CD' = 0`, `DD' > 0`, `(A, G)`
   detectable and `(A, C)` stabilizable, by duality with Proposition 9.3.2 (dual problem
   `(A', G', CC', DD', 0, β = 1)`, `kf_dual`, `kf_dual_T`): unique positive semidefinite
   steady-state covariance, convergence from every `Σ₀ ≥ 0`, convergence of the gains, and
   stability of `A − AKG`. The correlated case `CD' ≠ 0` is not covered.
7. **Example 10.1.1, p. 329.** The printed measurement equation uses the shock
   `(η_{t+1}, v_{t+1})'`; with `y_t = α + βt + z_t + v_t` and (10.2) it is `(η_t, v_t)'`
   (`example_10_1_1`; `example_10_1_1_misprint` shows the printed form fails). The loadings
   `C, D` must carry `σ_η, σ_v` for `Eε_tε_t' = I` (the book writes unit loadings).
8. **Example 10.1.2, p. 334.** The limit `Σ` is not given in the text; it is
   `(Q + √(Q² + 4QR))/2` (for `Q > 0`), and the convergence holds from every `Σ₀ ≥ 0`
   (`example_10_1_2`). The adaptive-expectations formula with a constant `K` is exact when the
   filter starts at the steady state (`example_10_1_2_adaptive`); otherwise it holds with `K_t`
   and in the limit.
9. **Example 10.1.3, p. 335.** "`Eε_t = Ev_t = 0`" should read `Eη_t = Ev_t = 0`. The closed
   forms of `Σ` and `K` are correct (`example_10_1_3`); the stationary `Σ` is the unique
   nonnegative solution when `σ_η, σ_v ≠ 0`.
10. **Example 10.1.4, pp. 336–337.** The factorisation `ln p(y^T) = ∑ ln p(y_t|y^{t−1})` and the
    identification of `p(y_t|y^{t−1})` with the `N(ŷ_{t|t−1}, Ω_{t|t−1})` density are the
    Gaussian reading (not formalised); what is proved is that the log of the `N(0, Ω_t)` density
    at the innovation is `−(n_y/2)ln 2π − ½ln|Ω_t| − ½a_t'Ω_t⁻¹a_t` and the summed formula
    (`example_10_1_4`). `|Ω|` is the determinant.
11. **§10.3, pp. 343–345.** The book's sketch is formalised as one Bellman step
    (`kf_certainty_equivalence`) in the project's Chapter 9 conventions (loss without the `½`,
    `V = −x'Px − d`): with `Δ_t` having (conditional) mean zero and the innovation entering as
    `KWξ`, `WW' = Ω`, the same Riccati fixed point `P` and the same gain `F(P)` solve the
    partial-information Bellman equation, with constant
    `d̂ = (1 − β)⁻¹(EΔ'QΔ + β tr(PKWW'K'))`. That `Δ_t` and `a_{t+1}` are conditionally mean zero
    given `y^t` is the Gaussian reading. The book's `Δ_t = Ax_{t−1} + η_t − Ax̂_{t−1|t−1} − Ka_t`
    omits the control terms, which cancel (`KFSystem.kf_Delta_succ`).
12. **Exercise 10.2.** With `ρ` unknown, the state `(ρ, z_t)` has the non-linear transition
    `(ρ, z) ↦ (ρ, ρz)` (`ex_10_2_nonlinear`), so the Kalman filter does not apply; what is
    proved is the filter conditional on `ρ` (`ex_10_2`).
13. **Exercise 10.4.** The "equivalent" second form `y_t = Gx_t + Hu_{t−1} + Dε_t`,
    `x_{t+1} = Ax_t + Bu_t + Cε_t` is the first form only after re-dating the shock and the
    observation, and with `Hu_{t−1}` in place of `Hu_t` (`ex_10_4_equiv`). The filter
    (`ex_10_4`) uses the cross term `CD'`: its Riccati operator is that of the dual problem
    `(A', G', CC', DD', CD', 1)` (`kf_ex4Dual`, `kf_ex4_TF`).
14. **Exercise 10.5.** The assumption that `z_t` is independent of `x_s, ε_s` (`s ≥ t`) is not
    needed: the estimation error and the covariances do not depend on the known input `Hz_t`
    (`ex_10_5`).

## §10.1.2–§10.2 and Exercise 10.6

### §10.1.2–§10.1.3

15. **The probability model is built explicitly.** The book computes conditional probabilities
   directly. Here the joint law of state and signal paths is the product
   `μ₀(x₀)f(x₀,y₀)∏P(xₛ,xₛ₊₁)f(xₛ₊₁,yₛ₊₁)` (`hm_weight`) and every filter quantity is a ratio of
   its marginals. That it is a probability, that the states alone form the Markov chain `(μ₀, P)`
   and that the filter is a probability vector are proved (`hm_lik_sum`, `hm_markov`,
   `hm_post_sum`). Conditional expectations given `x_t = eᵢ` in (10.13)–(10.14) are the finite
   sums `Σⱼ pᵢⱼ g(eⱼ)` (`hm_condE`).
16. **Bayes' rule needs `Pr(yᵗ⁻¹) ≠ 0`.** The updating formulas of pp. 338 and 340 are proved under
   the hypothesis that the conditioning history has positive probability (density)
   (`hm_bayes`, `hm_post_update`, `hm_lik_snoc`).
17. **`E[u_tu′_t | x_t]` should be `E[w_tw′_t | x_t]`** (p. 338). Proved for `w_t`
   (`eq_10_14_cov`).
18. **`f(x, y_t)` in the Hamilton update should be `f(eᵢ, y_t)`** (p. 340), and the book writes
   `π_t(i | yᵗ⁻¹)` and `π_t(eᵢ | yᵗ⁻¹)` for the same object. Proved with `f(eᵢ, y_t)`
   (`hm_hamilton_update`).
19. **`f(x, y) = Pr(h(x, ε) = y)` is a density.** For the Gaussian example the probability is zero;
   the filter uses the density of `h(x, ε)`, which is proved to be the Gaussian density
   (`hm_switch_density`). The filter algebra is the same for densities (`HMFilter` takes any
   nonnegative emission weight).
20. **Indexing.** In `HMFilter` the date `t − 1` of the book is `t` and `yᵗ⁻¹` is a path of length
   `t + 1` (`Fin (t + 1) → Y`).

### §10.2

21. **Finite states, signals and actions; deterministic history-dependent policies.** The book's
   general "posterior distribution as state" is formalised for finite `X`, `Y`, `U` (the book's
   discrete case). Policies choose `u_k` from the signals `y₁ … y_k` (past actions are functions
   of them). Assumption (iii) is read as `Pr(y_{t+1} | x_{t+1}, u_t)` (the book writes
   `Pr(y_t | x_t, u_t, yᵗ⁻¹) = Pr(y_t | x_t, u_{t−1})`, with `u_t` on the left chosen after `y_t`).
   The prior `P₀` is the belief at the first decision date.
22. **Sufficiency of the belief is proved, not assumed.** The book "can then establish" the
   Bellman equation in `P`. Proved: the expected reward of every history-dependent policy is at
   most `V(P₀, 0)` and the belief policy attains it (`hm_J_le_V`, `hm_J_beliefPol`,
   `hm_value_isGreatest`), assuming `β ≥ 0` and stochastic kernels. The posterior recursion is
   proved to be the conditional probability for one period (`hm_posterior_one_step`); when
   `Pr(y | P, u) = 0` the posterior `P*` is `0/0` (Lean: `0`), harmless since it is weighted by
   `Pr(y | P, u)` (`hm_py_mul_V`).

### Example 10.2.1 and Exercise 10.6

23. **Notation in Example 10.2.1.** The maximisation is over `c_t, s_{t+1}` (printed
   `c_t, a_{t+1}`), and the conditional law of `y_{t+1}` is `N(G_{t+1}x̂_{t+1|t}, Ω_{t+1|t})`
   (printed `G_t`; `G_t = (1, t, 1)` is time-varying in Example 10.1.1). In Exercise 10.6
   (`α = β = 0`, `G = 1`) it is `N(x̂_{t+1|t}, Ω_{t+1|t})`, proved by Gaussian conditioning and
   convolution (`ex_10_6_a_predictive`). The maximum in the Bellman equation is read as `sSup`
   (`hm_gV`); in (b) and (c) it is proved to be attained.
24. **Exercise 10.6(a): two readings of the Kalman filter.** The gain and variance recursions are
    derived (i) as the minimum-mean-square-error linear update from second moments, scalar
    (10.8)–(10.11) (`hm_mse_eq`, `hm_mse_min`, `hm_mse_le`), and (ii) by Gaussian conditioning
    with densities (`hm_gauss_bayes`, `hm_gauss_marginal`, `hm_gauss_predict`). Example 10.1.1 is
    not re-used; its scalar case is restated here (`ex_10_6_a_shocks`).
25. **Exercise 10.6(b): the budget has `exp(y_t)` income.** With CARA utility the expectation
    `N = E[exp(−γ exp(y₁))]` is a lognormal Laplace transform without closed form; the solution
    is explicit up to `N`, which is proved positive (`ex_10_6_b`). Consumption may be negative
    under CARA; only `s_{t+1} ≥ 0` is imposed, as in (10.15).
26. **Exercise 10.6(c) is solved with the borrowing constraint only at the end.** With
    `s_{t+1} ≥ 0` at every date the optimal rule already has a kink for `T = 1`
    (`max(0, ·)` in `ex_10_6_b`), and the value is not exponential in wealth, so there is no
    closed form for `T ≥ 2`. We solve the standard CARA version: `s_{T+1} ≥ 0`, borrowing allowed
    before `T` (`ex_10_6_c`, `ex_10_6_c_policy`). The value is
    `−(1/γ)φ_k(x̂_{t+1|t})exp(−γa_kW)` with `1/a_k = Σ_{j≤k}R⁻ʲ` (`hm_a_inv`); the factors `φ_k`
    are defined by Gaussian integrals and are proved continuous, positive and bounded
    (`hm_phi_props`), so all expectations are finite. The kink claim for the constrained problem
    is a remark, not a theorem.
27. **Exercise 10.6(d).** The Bellman equation with `x̂_{t|t}` as state (`hm_gVf`) is proved to
    give the same value as the book's (`ex_10_6_d`), for any utility and feasible sets.
