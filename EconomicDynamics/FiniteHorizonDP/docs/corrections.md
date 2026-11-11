# Corrections and departures: Miao Chapter 6

## §§6.1–6.3, the secretary problem, Exercises 1–4

1. **(6.8), p. 159**: `C_{T−1} = K_{T−1}^α/(1 + αβ)`, not `K_T^{α−1}/(1 + αβ)` (`eq_6_8`;
   `eq_6_8_misprint`: the printed formula fails for every `α, β`). (6.3)–(6.6), `b_t` and
   `A_T = 0` are correct as printed (`eq_6_5_6_6`, `po61_b_succ`).
2. **The Euler equation, p. 158,** holds for `t = 0, …, T − 1`, not `t = 0, …, T` (there is no
   `K_{T+2}`); `eq_6_3` states it on that range.
3. **The projection identity, p. 162,** `{V₁ < c} = proj {u < c}` is false for a supremum
   (`proj_identity_6_2_misprint`); the true identity is `{V₁* > c} = proj {u > c}`
   (`proj_identity_6_2`). Mathlib v4.34.0 has no Borel set with a non-Borel projection, so
   Blackwell's point is formalised as "`V₁*` is measurable iff `proj E` is", for `u = 1_E`
   (`blackwell_6_2`).
4. **Assumption 5.1.3 at every date.** §6.3 uses it for the problems from every date, not only
   date 0 (`po_Assumption513`); bounded rewards suffice (`po_assumption513_of_bounded`).
5. **Assumption 6.3.1(b)** requires joint measurability of the ε-optimal plans in the history
   and the later states (`po_JointMeas`): separate measurability, as printed, does not make the
   glued plan of the proof of Theorem 6.3.1 measurable. The ε-plans are indexed by the current
   state.
6. **Integrability.** Integrability of `V_{t+1}` against `P_{t+1}(s, a; ·)` is derived in
   Theorem 6.3.1 and is a hypothesis of Theorems 6.3.2–6.3.3. Only `β ≥ 0` is used (`β > 0` in
   Theorem 6.3.3), not all of Assumption 5.1.2.
7. **Theorem 6.3.3** holds only for `μᵗ(s₀, ·; π*)`-almost every history (`theorem_6_3_3`); the
   printed "all `t, sᵗ`" is false (`theorem_6_3_3_counterexample`: an optimal plan may act
   arbitrarily on histories it reaches with probability zero). The hypothesis that `G_t` has a
   measurable selection is not needed.
8. **Exercise 1.** In the deterministic case Theorem 6.3.1 needs only that `V_{t+1}` is finite,
   any selection of `G_t` works in Theorem 6.3.2, and Theorem 6.3.3 holds along the optimal
   path everywhere.
9. **Exercise 2.** Assumption 5.1.3 fails for log utility (`ln C` is unbounded below), so
   optimality is among plans with integrable rewards (`ex_6_2_optimal`,
   `po_verification_intPlans`); the shock enters as `z = ζ(x) > 0` with `ln ζ` measurable and
   bounded. The saving rate does not depend on the shock (`ex_6_2_policies`).
10. **`τ(4)` and Proposition 6.6.1, pp. 185–186.** By (6.43), `τ(4) = 2`, not `1`
    (`sec_tau_four`); the book's `1` is `τ − 1`, the number of candidates rejected. The rule as
    printed, "interview `τ` candidates and choose the first better one", is off by one: at
    `N = 4` it wins with probability `5/12 < 11/24` (`prop_6_6_1_misprint`). The optimal rule
    rejects the first `τ − 1` candidates and then takes the first best-so-far (`prop_6_6_1`).
11. **The threshold, p. 186.** "`t/N ≤ V_t(0)` for all `t ≤ τ`" fails at `t = τ`
    (`sec_threshold_misprint`: `5/12 < 1/2` at `N = 4`); it holds for `t < τ` (`sec_threshold`).
12. **Exercise 4** asks to "maximize the expected rank"; with rank 1 the best, this means
    minimising the expected rank number. The payoffs of Exercises 3–4 (the probability that a
    candidate of relative rank `r` among `k` is among the two best, and the expected rank
    `r(N + 1)/(k + 1)`) are taken as model data, not derived by counting.
13. **Chapter 5's secretary model** uses date `t` for the book's date `t + 1` and horizon
    `N − 1`, and `β = 1`, outside Assumption 5.1.2, which finite horizons do not need.

## §§6.4–6.5

14. **Lemma 6.4.1, case (i)** (p. 174) is false for unbounded continuous `f`:
   `lemma_6_4_1_countable_counterexample` (`Z = ℕ`, geometric `Q`, `φ = x`,
   `f(x, n) = 2^{n+1} max(0, 1 − |(n+1)x − 1|)`; each `f(x, ·)` is bounded, `h(1/(m+1)) ≥ 1`,
   `h(0) = 0`). It holds for bounded `f` (`lemma_6_4_1_countable`). Case (ii) (compact `Z`, Feller
   `Q`) holds for every continuous `f` (`lemma_6_4_1_compact`). Countability is not used.
15. **Theorem 6.4.1, case (i)** therefore assumes bounded rewards (`theorem_6_4_1_countable`).
   Assumptions 6.4.1–6.4.2 and 5.1.2 are not used.
16. **Theorems 6.4.2–6.4.4** use `β ≥ 0` (6.4.3's single-valuedness `β > 0`) instead of all of
   Assumption 5.1.2.
17. **Theorem 6.4.3: strict concavity of `V_t` is correct**, but **`G_t` need not be
   single-valued**: Assumption 6.4.10 is strict only in `x` (`theorem_6_4_3_counterexample`:
   `X = (−∞, 0]`, `Γ = [0, 1]`, `u = −x²`, `φ = x`; all of 6.4.1–6.4.12 and 5.1.2 hold,
   `G_0(0, z) = [0, 1]`). `theorem_6_4_3` adds that `φ(x, ·, z, z′)` is one-to-one on `A` and
   `β > 0`. The composite `V_{t+1}(φ(·, ·, z, z′), z′)` is concave only with `V_{t+1}` monotone
   (the book's remark, p. 177; `compConcave_of_mono`) or `φ` affine (`compConcave_of_affine`).
18. **Theorem 6.4.4** is formalised for `X, A ⊆ ℝ` only (`n_x = n_a = 1`, the case of §§6.5 and
   6.6.2). Corrections to its hypotheses:
   * differentiating under `∫ Q(z, dz′)` in (6.31) and (6.33) needs a domination; we use
     concavity plus a local uniform bound (`LocBounded`), automatic for compact `Z`
     (`locBounded_of_compact`);
   * interiority is needed at every interior state and for the next states:
     `g_t(x, z) ∈ int Γ(x, z)` and `φ(x, g_t(x, z), z, z′) ∈ int X` for all `x ∈ int X`
     (`InteriorPolicy`); the pointwise hypothesis does not give the differentiability of
     `V_{t+1}` at `x_{t+1}` that (6.31) and (6.33) use;
   * "`g_t(x_t, z_t) ∈ int Γ(x, z_t)` near `x_t`" needs `Γ` convex-valued (6.4.11) as well as
     continuous (`eventually_mem_Γ`);
   * (6.31) holds for `t = 0` too (stated for `t = 1, …, T − 1`);
   * `C¹` follows from concavity plus differentiability (`oc_continuousOn_deriv_of_concave`).
19. **Measurable selection** (p. 175) is proved for actions in `ℝ^m` as `Fin m → ℝ`.
20. **Theorem 6.5.1**: the hypothesis "`H_t(·, ·, z_t, μ_{t+1})` concave" is replaced by
   concavity of the pathwise Hamiltonian `u_t(x, z_t, a) + β μ_{t+1} φ(x, a, z_t, z_{t+1})`, since
   (6.37) contains `E_t` of a function of `(x, a)` and is not well defined at the random arguments
   the proof substitutes; the p. 183 sufficient conditions give the pathwise form. The telescoping
   needs integrability (`MPIntegrable`) for the candidate and the competitor, so optimality is
   among plans satisfying it. `(6.38)`–`(6.39)` take `∂/∂x`, `∂/∂a` inside `E_t`, as the book
   does when it rewrites (6.34)–(6.35).
21. **(6.40)**: the terminal condition is `λ_{T−1} = β E_{T−1}[∂u_T(x_T, z_T)/∂x]`
   (`eq_6_40_terminal`), not `E_{T−1}[u_T(x_T, z_T)]`; with the printed one the first-order
   system can be inconsistent (`eq_6_40_terminal_misprint`).
22. **The link `μ_t = ∂V_t/∂x`** (p. 183) needs the Markov property of `z_t` relative to the
   filtration (`IsMarkovCond`) to identify `E_t` with `∫ Q(z_t, dz′)`.
23. **p. 175 (Theorem 6.3.2 applied to §6.4)** needs Assumption 5.1.3, which continuous rewards do
    not give on a non-compact `X` (they need not be integrable along feasible plans). `p175`,
    `p175_date_zero`, `p175_control`, `p175_compact` and `p175_countable` assume the rewards
    bounded on `X × Z × A` (`|u_t| ≤ B` for `t < T`, `|u_T| ≤ B`); in case (ii) compact `X` and `A`
    suffice instead (`p175_compact_XA`, via `bounded_of_compact`). Also used: `β ≥ 0`, `X ⊆ ℝⁿ`,
    `A ⊆ ℝᵐ` (the Measurable Selection Theorem), and `Z` a second-countable metric space (true in
    both cases of Assumption 6.4.3). The MDP has state space `X × Z` and action space `A`
    (Assumption 6.4.5 keeps `φ` in `X`); its rewards for `t ≥ T`, which the book does not define,
    are set to `0`. The optimality for (6.28) is for the Bolza objective in the shock-history form
    (5.12) of Chapter 5 (`controlObj`, `controlV`), not the filtered-space form `bolza`.

## §6.6.2 and Exercises 5–10

24. **§6.6.2, the hypotheses on `u`.** Consumption `c = 0` is feasible (`s = x`), so `u` must be
    finite and continuous on `[0, ∞)` (`CSModel.Basic.u_cont`); the logarithm is excluded. The
    first-order condition at `s = 0` and the Inada argument need the next cash on hand bounded
    away from `0`: `w > 0`, for the book the cash floor `y_min − rb > 0` (`bookModel_basic`).
25. **"We can apply the theory developed in Section 6.4"** (p. 188) holds for Theorem 6.4.1
    (`CSModel.standing`), but **not for Theorems 6.4.2–6.4.4**: Assumption 6.4.10 fails for the
    reward `u(x − s)`, which is constant along `x − s = c` (`CSModel.not_assumption6410`), and no
    concave differentiable extension of `u(x − s)` to `s > x` exists under the Inada condition
    (Assumptions 6.4.7 and 6.4.13 ask for `u_t` on all of `X × A`). Strict monotonicity, strict
    concavity, differentiability and the first-order condition are proved directly
    (`strictMonoOn_v`, `strictConcaveOn_v`, `hasDerivAt_v`, `foc`).
26. **"`g_n(x)` and `s_n(x)` are increasing in `x`"**: `g_n` is strictly increasing
    (`strictMonoOn_cons`), `s_n` only weakly: for `n ≥ 1` the borrowing constraint binds,
    `s_n = 0`, on an interval `(0, x̄]` (`exists_sav_eq_zero`, `not_strictMonoOn_sav`).
27. **"`g_n` decreasing in `n`, `s_n` and `v_n′` increasing in `n`"** hold weakly
    (`cons_succ_le`, `sav_le_sav_succ`, `deriv_v_le`), not strictly
    (`exists_cons_succ_eq`: `g_{n+2}(x) = g_{n+1}(x)` and `g_1(x) = g_0(x)` for small `x`).
28. **The FOC/envelope bullet** is stated for `n ≥ 1` with `x > 0` (`foc`, `deriv_v`). The
    comparison `c_t(x; y_max) ≥ c_t(x) ≥ c_t(x; y_min)` (p. 189) holds as stated, with no condition
    on `u′′′`, `β` or `R`, and also for Markov income (`cons_ge_low`, `cons_le_high`); "increasing"
    and "decreasing" in it are weak.
29. **Exercise 8**: with no borrowing constraint a terminal condition is needed; we impose
    `a_{T+1} ≥ 0` (binding at the optimum, `ex_6_8`). `γ = 1` is log utility (`cs_crra`).
30. **Exercise 9**: utility is bounded above, so without a terminal condition the consumer borrows
    without bound; we impose `a_{T+1} = 0` (`v_0 = u`). The solution is linear in cash on hand
    `x = Ra + y` with the certainty marginal propensity to consume (`ex_6_9`).
31. **Exercise 10**: the Inada condition fails (`u′(0) = γ`), so consumption may be `0`; the
    derivative-free results apply (`ex_6_10`, threshold structure). Only the one-period policy is
    explicit, the Exercise 9 saving clamped to `[0, x]` (`ex_6_10_one`); for `n ≥ 2` the
    continuation value is not exponential and no closed form is given.
