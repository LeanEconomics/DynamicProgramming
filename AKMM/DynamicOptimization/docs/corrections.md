# Corrections and departures: AKMM Chapter 4

Marina Azzimonti, Per Krusell, Alisdair McKay and Toshihiko Mukoyama, *Macroeconomics* (draft of
December 2025), Chapter 4, Dynamic optimization, pp. 93–127, and Appendix 4.A, pp. 827–835. Lean
names are relative to `AKMM.DynamicOptimization`. Every book item is located in the
[source map](source-map.md).

## Corrections

1. **p. 95, the Weierstrass conditions.** The book: (i) `F̂` continuous, (ii) `h` continuous and
   strictly monotone in `y`, (iii) `Γ(x)` nonempty, closed and bounded for every `x` give a maximum
   of (P1). Condition (iii) is pointwise and does not make the set of feasible plans compact. With
   `F(x, x') = x'`, `T = 1`, `x₀ = 0` and `Γ(0) = [0, 1]`, `Γ(x) = [0, x]` on `(0, 1)`,
   `Γ(x) = {0}` otherwise (nonempty, closed, bounded everywhere), the objective `x₁ + βx₂` has
   supremum `1 + β` and no maximizer (`seq_weierstrass_counterexample`). With
   `Γ(x) = [x̲, γ(x)]`, `γ` continuous, the maximum exists (`seq_weierstrass`). The step from (ii)
   to continuity of the reduced return `F` is not formalised; `F` is assumed continuous.

2. **p. 99, "the consumption-saving model when `T = 2`".** The model has periods `0` and `1` and
   `a₂ = 0`; under (P2)'s convention `t ∈ {0, …, T}` this is `T = 1`. No theorem depends on it.

3. **p. 104, CRRA box: "as `σ → ∞` utility converges to zero for all `c`".** True for `c ≥ 1`
   (`crra_tendsto_zero_of_one_le`); for `0 < c < 1`, `(c^{1−σ} − 1)/(1 − σ) → −∞`
   (`crra_tendsto_atBot_of_lt_one`). The Leontief limit of the transformed objective is proved for
   finitely many periods (`crra_leontief_limit`); for infinite sums the minimum need not exist.

4. **p. 110, Proposition 4.4 and its proof (App. 4.A.3) omit a hypothesis.** The last step of the
   proof, `β^{T+1}F₁(x*_{T+1}, x*_{T+2})(x_{T+1} − x*_{T+1}) ≥ −β^{T+1}F₁(…)x*_{T+1}`, needs `F₁ ≥ 0`
   (from "increasing in its first argument") *and* `x_{T+1} ≥ 0` for every competitor. Without the
   latter the proposition is false: `F(x, y) = x − βy` is linear (concave), increasing in `x`,
   `Γ(x) = ℝ` is convex, `x* = 0` satisfies the Euler equation and the TVC, but `x₀ = 0`,
   `x_t = −β^{−t}` has value `1 > 0` (`proposition_4_4_counterexample`). The corrected statement
   assumes that feasible plans are nonnegative (`proposition_4_4`; SLP Theorem 4.15 assumes
   `X ⊆ ℝ^l_+`). The proof's restriction to *interior* competitors and the interiority of `x*` are
   not needed. "Maximizes the objective" is proved as catching-up optimality, and as the largest
   value whenever values are finite.

5. **p. 118, the periodic NGM.** The printed `Γ_i(k) = [0, A_if(k) + (1 − δ)k − k']` uses the choice
   `k'` in its own constraint set; read literally it is `0 ≤ k' ≤ (A_if(k) + (1 − δ)k)/2` and
   excludes, e.g., `k' = A_if(k) + (1 − δ)k` (`periodic_printed_gamma`). The correct set is
   `[0, A_if(k) + (1 − δ)k]` (`periodic_bellman`).

6. **p. 118, the delayed-depreciation NGM.** The printed Bellman equation
   `V(i', i) = max {u(c) + V(i'', i')}` omits `β`. Without it the operator satisfies
   `T(v + c) = Tv + c` and is not a contraction for any modulus `< 1`
   (`delayed_no_discount_not_contraction`), contradicting fn. 15. The corrected equation with `β`
   is `delayed_bellman`.

7. **p. 120, property 5: "the policy function `g(x)` is strictly increasing".** False under the
   stated conditions (`F` strictly concave, strictly increasing in `x`, `C¹`; `Γ` monotone and
   convex). `F(x, y) = 3x − x² − (y − 1 + x/2)²` on `[0, 1]²` with `Γ(x) = [0, 1]` satisfies all of
   them, yet for every continuous `V` a policy exists and none is strictly increasing, because
   `F₁₂ < 0` (`property_5_counterexample`). The book's argument needs `−F₂(x, x')` decreasing in
   `x`, i.e. `F₁₂ > 0`. With strictly increasing differences the policy is nondecreasing
   (`property_5_corrected`); in the NGM it is strictly increasing (`property_5_ngm`, SLP
   Exercise 6.1b).

8. **p. 124, (4.28).** The printed `u'(f(k) − g(k))[f'(k) + 1 − δ − 1/β][k − g(k)] ≤ 0` drops the
   undepreciated capital; the argument of `u'` is `c = f(k) + (1 − δ)k − g(k)`, as in the two
   displays before it (`eq_4_28`). The inequality alone gives only `g(k) ≤ k` for `k > k̄`; the
   strict `g(k) < k` needs strict concavity of `V` and (4.27) (`ngm_policy_direction`). Global
   convergence also uses continuity of `g` (`ngm_global_convergence`; for `δ = 1` all hypotheses
   are discharged by SLP Proposition 6.1, `ngm_global_convergence_full`).

9. **p. 830, proof of Theorem .4.** "`u'((1 + γ)c)/u'(c) = (1 + r)/β`": from the Euler equation
   `u'(c_t) = β(1 + r)u'(c_{t+1})` the ratio is `1/(β(1 + r))` (`bgp_marginal_ratio`). Only its
   independence of `c` is used.

10. **p. 829, Theorem .4: "`u(c)` has to be `log c` or `c^{1−σ}/(1 − σ)`, `σ > 0`".** The
    hypothesis is invariant under positive affine transformations, so the conclusion holds only up
    to them: `u = 2 log c` satisfies it (`theorem_4A_4_affine_counterexample`). The proof gives
    `u'(c) = u'(1)c^{−σ}` and `u = u'(1) log c + u(1)` or `u'(1)c^{1−σ}/(1 − σ) + b`
    (`theorem_4A_4`). `σ > 0` holds iff `u'` is strictly decreasing (`theorem_4A_4_sigma_pos`); the
    theorem does not assume concavity, and `u = c²/2` satisfies its hypotheses with `σ = −1`
    (`theorem_4A_4_convex_example`).

11. **p. 834, the TVC computation in 4.A.4.** Iterating (4.A.9) gives
    `βᵗu'(c_t)(f'(k_t) + 1 − δ)k_t = u'(c₀)k_t/∏_{s=1}^{t−1}(f'(k_s) + 1 − δ)`
    (`phase_tvc_identity`); the printed product starts at `s = 0` and is off by the factor
    `f'(k₀) + 1 − δ` (`phase_tvc_printed_differs`). The limit argument is unaffected
    (`phase_below_saddle_violates_tvc`).

12. **Minor.** p. 119, fn. 14: the sup norm is `sup_x |f(x)|`, not `sup_x f(x)` (`property_1` uses
    the sup metric). p. 111 uses `γ` as a *gross* growth rate (`βγ^{1−σ} < 1`) right after p. 107
    used it as a net rate (`β(1 + γ)^{1−σ} < 1`); `tvc_balanced_growth` uses the gross rate. p. 112
    "using what we have learned in Chapter 2" should be Chapter 3; p. 124 "(4.27) … identical to
    (4.10)" and p. 125 "`k̄` solves (4.10)" should cite (4.16). p. 125: "two real solutions, one
    strictly between zero and one, the other strictly greater than one" holds for `Θ > 0`; at
    `Θ = 0` the roots are `1` and `1/β` (`slopeRoot_mem`, `slopeRoot_zero`).

## Departures

13. **Result 1 (p. 100) needs less than stated.** Concavity, the Euler equation for `t < T`, the
    terminal condition and `F₂(x*_T, x*_{T+1}) ≤ 0` suffice (`result_1`); "increasing in its first
    argument" and interiority are not used. The book's "decreasing in its second argument" gives
    `F₂ ≤ 0` (`result_1_of_antitone`).

14. **Concavity of the NGM return (fn. 4, fn. 16)** is proved from concavity of `u` and of
    `f(k) + (1 − δ)k` directly (`ngm_return_concave`, `ngm_return_strictConcave`), not through the
    Hessian.

15. **Kuhn–Tucker.** Mathlib has no general Kuhn–Tucker theorem. The two-period conditions
    (4.4)–(4.6) are proved sufficient (`eq_4_4_to_4_6`); in (P3) the Euler equation (4.10) is
    derived at interior maxima by Fermat's theorem (`eq_4_10`), `k_{T+1} = 0` by a direct
    improvement (`ngm_terminal_zero`), and interiority under the Inada conditions by a perturbation
    argument (`ngm_finite_interior`, with the hypotheses listed there).

16. **Logarithmic utility.** In Examples 4.1, 4.3, 4.5 and 4.7 the competing plans have positive
    consumption (the others have value `−∞` in the book, but `Real.log 0 = 0` in Lean).

17. **The value function** of (4.21) is SLP's supremum function in the extended reals (`vstar`), and
    the recursive formulations (periodic, delayed depreciation) are SLP's Theorem 4.2 for an
    augmented state; Assumptions 4.1–4.2 are hypotheses.

18. **Properties 1–4 of `V` (pp. 119–120)** are SLP Theorems 4.6–4.8 and 4.10 under SLP's
    assumptions (bounded continuous `F`, compact-valued continuous `Γ`). Property 4 is stated in the
    envelope form `V'(x₀) = F₁(x₀, g(x₀))` for a concave `V`, which is also the envelope step of
    §4.4.5 (`property_4`).

19. **(4.29)** assumes, as the book does (fn. 17), that `g` is differentiable at `k̄`, and that (4.26)
    holds near `k̄` (`eq_4_29`).

20. **Theorem .3** reads the no-Ponzi condition (4.A.3) as "`a_{T+1}/(1 + r)ᵀ` converges to a limit
    `≥ 0`", assumes `r > −1`, `c ≥ 0` and summable discounted wages (as the book does), and
    determines `a` from `c` by the flow budget (`theorem_4A_3`).

21. **Saddle path.** The book asserts the existence of the saddle path (4.A.4). It is proved in the
    difference system itself, for every `k₀ > 0` and every `δ ≤ 1`, by a shooting argument
    (`saddle_path_general`): with the forward map `saddleFwd`, the set of `c₀` whose path reaches
    `k ≤ 0` is open, upward closed and bounded below by a feasible `c₀`; its infimum `c*` is
    feasible, never enters the open quadrant `k > k̄`, `c < c̄` (whose paths are feasible), and a
    feasible path avoiding both regions converges (`saddle_trapped_converges`). With
    `saddle_path_iff`, a positive path converges iff `c₀ = g(k₀)`. The saddle path is also the
    optimal policy for `δ = 1` (`saddle_path_slp`), and for log utility, Cobb–Douglas and `δ = 1`
    it is `(1 − αβ)Ak^α` (`saddle_logCobbDouglas`, `saddle_path_general_logCobbDouglas`).

22. **Assumptions used in App. 4.A.4.** The book's "standard assumptions" are made explicit: `f`
    concave on `[0, ∞)` with derivative `f' > 0` strictly decreasing, `δ ≤ 1` (so total resources
    rise with `k` and `f'(k) + 1 − δ > 0`), `u' > 0` strictly decreasing, and `f'` continuous at
    `k̄` (uniqueness; the capital gap between two paths then grows by the factor
    `f'(k_t) + 1 − δ → 1/β > 1`); for the region below the saddle path also `u'` continuous at
    `c̄`, `f(0) = 0` and the existence of the golden rule `f'(k^G) = δ`; for the existence of the
    saddle path also `f'`, `u'` continuous on `(0, ∞)`, `u'(c) → ∞` as `c → 0⁺`, and an inverse
    `ui` of `u'` on `(0, ∞)`, continuous (so the Euler equation determines `c_{t+1}`; it exists
    when `u'` maps `(0, ∞)` onto `(0, ∞)`). Paths are solutions with
    `k_t, c_t > 0` for all `t`; convergence means `k_t → k̄` and `c_t → c̄`.

23. **Figure .2: the `c_{t+1} = c_t` locus is not vertical.** In the discrete-time system it is
    `c = f(k) − δk + (k − k̄)` in the `(k_t, c_t)` plane, increasing with slope `f'(k) + 1 − δ`,
    which equals `1/β` at the steady state (`saddle_cloc_shape`); the near-vertical line of
    Figures .2 and .3 is the continuous-time picture. It meets `c = 0` at a unique `k̲ ∈ (0, k̄)`.

24. **Below the saddle path (p. 834).** The book says the path enters the region "where both `k_t`
    and `c_t` keep decreasing", while Figure .3 shows `k` rising there and the text later says
    "`k_t` keeps growing". What holds (`saddle_below`): from some date on `k_t ≥ k̄ + η` and `c_t`
    falls strictly, `c_t → 0`, `k_t > k^G` (indeed `≥ k^G + m/2` for an `m > 0`), and the TVC
    expression tends to `+∞`. Capital need not rise: from `k₀` above the maximum sustainable stock
    it falls at first.

25. **Above the saddle path (p. 834).** "In a finite time, `k_t` becomes zero" is proved as: some
    `k_{T+1} ≤ 0` with `k_s > 0` for `s ≤ T` (`saddle_above_infeasible`), by comparison with the
    saddle path rather than by the region argument; the region where `k` falls and `c` rises is
    absorbing (`saddle_regionA_absorbing`). Capital need not hit exactly zero.
