# Corrections and departures: Miao Chapter 21

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 21, Dynamic
Games, pp. 737–784. Lean names are relative to `Miao.DynamicGames`. Every book item is located in
the [source map](source-map.md).

## Introduction and §21.1.1–21.1.4, Exercises 21.1–21.2

1. **Proposition 21.1.3, p. 748: the punishment restarts.** The printed condition has
   `δ Uⱼ(Qʲ; t + 1)` on the deviation side; after a deviation by `j` the path `Qʲ` starts from
   its first period, so the term is `δ Uⱼ(Qʲ; 1)` (`proposition_21_1_3`). The printed version is
   false: in the repeated prisoner's dilemma with `δ = 9/10`, `Q⁰ = (C, C)` forever and the
   two-period stick-and-carrot punishments `Qʲ = (D, D), (D, D), (C, C), …`, the simple
   strategy is an SPE but the printed condition fails at the first date
   (`rg_proposition_21_1_3_misprint_restart`).
2. **Proposition 21.1.3, p. 748: only actual deviations.** The condition must range over
   `a'ⱼ ≠ aⁱⱼ(t)`, not over all `a'ⱼ ∈ Aⱼ` (the printed "a^i" is also `aⁱ(t)`). With
   `a'ⱼ = aⁱⱼ(t)` it demands `Uⱼ(Qʲ; 1) ≤ Uⱼ(Qⁱ; t + 1)`, which SPE does not require:
   `rg_proposition_21_1_3_misprint_own` gives a game (`rg_ownU`, `δ = 1/2`) and an SPE simple
   strategy (`rg_ownQ`) for which the condition with `a'ⱼ = aⁱⱼ(t)` fails, both as printed and
   with `Uⱼ(Qʲ; 1)`.
3. **Proposition 21.1.3, "only if".** The converse direction assumes every player has at least
   two actions (`[∀ j, Nontrivial (A j)]`), so that every punishment path is reached
   (`rg_simple_reach`); otherwise the conditions on a never-reached path `Qʲ` are not implied by
   subgame perfection. The "if" direction holds without it (`rg_proposition_21_1_3_if`).
4. **Theorem 21.1.2, p. 745.** For finite action sets it is proved as printed, on the subsets of
   the feasible set `co {u(a)}` (`theorem_21_1_2`). For infinite action sets the convex hull need
   not be closed and `V` is only shown to lie in its closure (`rg_U_mem_closure_feasible`); the
   theorem is proved on the subsets of the closed feasible set (`theorem_21_1_2_closure`). The
   greatest fixed point is Mathlib's `OrderHom.gfp` on `Set.Iic F`.
5. **Proposition 21.1.2, p. 745, and Exercise 21.1.** The book's second proof extracts a
   convergent subsequence of admissible pairs `(aₖ, wₖ)`, which needs finite `A` (for compact
   `A` the functions `wₖ` need not have a convergent subsequence). Both are proved through the
   compactness of `B(cl V)` (`ex_21_2`), obtained from the worst-punishment form of `B`
   (`rg_mem_B_iff_punish`): `cl V ⊆ B(cl V) ⊆ V`.
6. **Lemma 21.1.2, p. 743.** The book's construction picks admissible pairs at each history;
   here the pairs are chosen once, as functions `g, nx` of the continuation value, and the
   strategy is the state recursion `rg_recStrat` (the recursive strategy of p. 744). The
   identity `U(σ|hᵗ) = w_{t−1}(hᵗ)` "because W is bounded" is proved as a geometric bound
   (`rg_recStrat_spec`).
7. **Proposition 21.1.1, p. 742.** The proof sketch (finite deviations, then truncation) is
   replaced by the bound `gain ≤ 2Mδⁿ` for every `n` on the gain of any deviation in any
   subgame (`rg_gain_le_of_noOneShot`). Bounded payoffs and `0 ≤ δ < 1` are assumed.
8. **Theorem 21.1.3, p. 746.** "`V = lim Bᵗ(W₀)`" is proved both as `V = ⋂ₜ Bᵗ(W₀)`
   (`theorem_21_1_3`) and as convergence in the Hausdorff distance
   (`theorem_21_1_3_hausdorff`). "Nonempty because `V` is nonempty" needs a pure-strategy SPE;
   `rg_stageNash_mem_V` gives one from a stage-game Nash equilibrium, and the prisoner's dilemma
   is a concrete instance (`rg_pd_stageNash`, `rg_pd_V_nonempty`). The convergence results do
   not need `V ≠ ∅`.
9. **The Cronshaw–Luenberger operator, p. 747.** `ICᵢ` is stated for every `a'ᵢ` (equivalent to
   the max form for finite `Aᵢ`). It equals `B` on compact sets (`rg_BCL_eq`) and `V` is its
   largest compact fixed point (`rg_cronshaw_luenberger`); on non-compact sets the infimum need
   not be attained and the two operators can differ, so the statement is restricted to compact
   sets. That `B*` preserves compactness is not formalised (see the source map).
10. **Assumption 21.1.1** is not a bundled structure: boundedness, finiteness or compactness and
    continuity appear as explicit hypotheses where each result needs them. Pure strategies
    throughout, as in the book; time is indexed from `0` (the book's period `t + 1`).
11. **Abreu's simple strategies, pp. 748–749.** Proved for compact action sets and continuous
    payoffs (`rg_abreu_simple`), using the corrected Proposition 21.1.3 ("if" direction) and the
    compactness of `V` for the harshest punishments.

## §21.1.5, §21.2, §21.3 and Exercise 21.3

### Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Example 21.1.2, p. 752 | "If `1/(p − r) ≥ δ ≥ 1/(p + q − 2r)`, then `W` is self-generating." | The book's own proof needs `1/(p − q + p − r) ≤ δ ≤ 1/(p − r + q − r)`: the (D, D) incentive constraint holds iff `δ ≤ 1/(p − r + q − r)` (`example_21_1_2_DD_ic_iff`) and the (C, C) one iff `δ ≥ 1/(p − q + p − r)` (`example_21_1_2_CC_ic_iff`). On that interval `W` is self-generating (`example_21_1_2`) and consists of PPE payoffs (`example_21_1_2_ppe`; instance `p = 9/10`, `q = 2/5`, `r = 1/10`, `δ = 4/5`: `example_21_1_2_instance`). `p − q > q − r` is exactly what makes the interval nonempty (`example_21_1_2_interval`). The printed claim is false: for `p = 9/10`, `q = 2/5`, `r = 1/10`, `δ = 19/20` its hypotheses hold but `(v, v) ∉ B(W)` (`example_21_1_2_printed_false`). |
| p. 757 | The follower's rule is `c₂ = αβ₂κ₂(x − c₁)/(1 + αβ₂κ₂)`. | (21.2) gives `c₂ = (x − c₁)/(1 + αβ₂κ₂)`, the unique best reply (`dg_fish_follower_reaction`); the printed expression is the follower's saving. For `α = β₂ = 1/2`, `κ₂ = 4/3`, `x = 2`, `c₁ = 1` the printed `c₂ = 1/4` violates (21.2) and does strictly worse than `3/4` (`dg_fish_follower_printed_false`). The leader's result is unaffected, since either rule leaves a multiple of `x − c₁` (`dg_fish_leader_foc`, `dg_fish_leader`). |
| p. 757 | `lim x_t = x̄ = (αβ₁β₂x_t/(β₁ + β₂ − αβ₁β₂))^{α/(1−α)}`. | The `x_t` inside the steady-state formula is a typo: `x̄ = (αβ₁β₂/(β₁ + β₂ − αβ₁β₂))^{α/(1−α)}` (`dg_fish_mpe_steady_state`). |
| p. 757 | "Substituting this rule back into the above Bellman equation yields `k₁ = 1/(1 − αβ₁)`." | `k₁` is `κ₁` (`dg_fish_leader`). |

### Conventions and departures

| Where | Book | Lean |
| --- | --- | --- |
| §21.1.5, p. 749 | `f` continuous, full support, `A_i` finite or compact. | Not needed for the PPE theory: `Y` finite, `f(·|a)` a probability vector, rewards bounded, actions arbitrary (`DGPublicGame`). Compactness of `B(W)` is proved for finitely many action profiles (`dg_B_isCompact`). Example 21.1.2 needs only `0 ≤ r < q < p ≤ 1`. |
| Definition 21.1.6, p. 750 | `U_i(σ*|h) ≥ U_i(σ_i, σ*₋ᵢ|h)` for all strategies `σ_i` on private histories. | Deviations are public pure strategies. A pure strategy's own past actions are a function of the public history, so every pure strategy is outcome-equivalent to a public one. Histories are lists of signals, oldest first; date `0` is the first period. |
| p. 751 | "Almost all the results for the case of perfect monitoring carry over." | Proved for PPE: the one-shot deviation principle (`dg_oneShot_ppe`), Lemma 21.1.1 (`dg_ppe_subset_B`), Lemma 21.1.2 (`dg_selfGeneration_ppe`), Theorem 21.1.1 (`dg_factorization_ppe`), Theorem 21.1.2 (`dg_ppe_greatest_fixedPoint`, as the largest bounded fixed point), Lemmas 21.1.3–21.1.4 (`dg_B_mono`, `dg_B_isCompact`). Not formalised: PPE versions of Proposition 21.1.2 and Theorem 21.1.3, which the text does not state. |
| §21.2, p. 753 | `S` in a Euclidean space, transition probability `p`. | Finitely many states, bounded payoffs (`DGStochGame`). |
| Definition 21.2.1, p. 754 | "for all `σ_i`". | Deviations are Markov strategies `τ_t : S → A_i`, possibly time-varying (`dg_IsMPE`). A stationary profile is an MPE iff its values solve the coupled Bellman equations (`definition_21_2_1_bellman_iff`, `dg_stationaryMPE_bellman`). |
| p. 755 | `B` is monotone; `V*` (the "MPE payoff correspondence") is its maximal fixed point. | Monotonicity needs nonempty `W_s` and `W'_s` bounded below, so that `μ_{i,s}` is defined; the text works with compact-valued correspondences (`dg_SY_mono`). Compactness is preserved for finite action sets (`dg_SY_isCompact`). The maximal-fixed-point claim is not formalised: the continuation values in `B` depend on history (the punishments `μ_{i,s}`), so its fixed points describe subgame perfect payoffs, not Markov perfect ones, and the text gives no proof. |
| §21.3, p. 756 | Guess and verify with `V_i(x) = κ_i ln x + ν_i`. | Each best-response problem is the fishing problem "catch `c ∈ (0, Rx)`, next stock `(θ(Rx − c))^α`" (`dg_fp*`). The Bellman equation is verified with its unique maximiser (`dg_fp_bellman`, `dg_fp_bellman_unique`). Optimality is proved against every feasible catch sequence whose discounted log-utility series converges (`dg_fp_optimal`), which covers all plans with finite utility. |
| §21.3 | Comparison with the cooperative solution. | Not carried out in the text. Added for `β₁ = β₂ = β`: planner's Bellman equation (`dg_fish_cooperative`) and overfishing (`dg_fish_overfishing`). |

## §21.4 Credible Government Policies and Exercises 21.4–21.6

### Setting

12. **Modelling choices.** The set `C` of competitive equilibria is a primitive of the repeated
   economy (the examples give it by a table; `cg_CE u` constructs it from `u`). A strategy
   profile is one map from histories (lists of past pairs, oldest first) to `X × Y`; the
   book's `X^{t−1} × Y^{t−1}` histories are these lists zipped. Paths are indexed from `0`. The
   payoff `r` is bounded (`|r| ≤ M`, which the book's compact `X`, `Y` and continuous `u` give)
   and `0 ≤ δ < 1`; compactness and continuity are assumed only where used (`lemma_21_4_2`,
   `cg_aps_step3`). The book writes the government's choice set in §21.4.2 as `y_t ∈ X`; it is
   `Y`. The state map of Definition 21.4.5 is `Vf` in Lean, as `V` names the value set.

### §21.4.3

13. **Lemma 21.4.2, p. 764.** "The operator `W` is monotone" means the operator `B`. Compactness
   of `B(W)` needs `X`, `Y` compact, `C` closed and `r` continuous (the book's standing
   assumptions of §21.4.1) and `δ ≥ 0`; the proof writes `B(W)` as a continuous image of a
   compact set of tuples with a single punishment value `min W` (`cg_B_eq_image`,
   `cg_K_isCompact`, `lemma_21_4_2`).
14. **Lemma 21.4.3, p. 764–765.** The proof's conclusion "`U^g(σ) = V`" should read
   `Uᵍ(σ) = v`. The proof's construction is the recursive strategy of §21.4.5 with states in
   `W`; that the state equals the value needs `W` bounded (`cg_recStrat_value`,
   `cg_selfGenerating_subset_V`, `lemma_21_4_3`).
15. **Theorem 21.4.1, p. 765: "`V` is the largest fixed point of `B`".** True only among
   bounded sets. In Example 21.4.2 at `δ = 0.9`, `B(ℝ) = ℝ` but `ℝ ⊄ V`
   (`cg_theorem_21_4_1_unbounded`). Proved: `V = B(V)`, `V` is bounded and contains every
   bounded fixed point (`theorem_21_4_1`).
16. **Step 2 of the algorithm, p. 765.** The problem for `w¹_max` has `w¹_max` and `w¹_min` in
   its constraint; they must be the bounds `w⁰_max`, `w⁰_min` of `W₀` (the unknown `w¹_max`
   appears on both sides as printed). Proved with `W₀ = [a, b]`: `max B([a, b])` solves
   `max (1 − δ) r(x, y) + δb` subject to `(1 − δ) r(x, y) + δb ≥ (1 − δ) r(x, y') + δa`
   (`cg_aps_step2_max`); the `w¹_min` problem describes `B([a, b])` exactly (`cg_aps_step2`).
   Step 3's "iterate until the sets converge" is proved with the limit identified:
   `⋂_j B^j(W₀) = V` (`cg_aps_step3`).

### §21.4.4

17. **Definition of `U_tᵍ`, p. 766.** Printed as `(1 − δ) ∑_{s=t} δ^{s−t} r(x_{t+s}, y_{t+s})`;
   the intended sum is `(1 − δ) ∑_{s≥0} δ^s r(x_{t+s}, y_{t+s})` (`cg_Ut`).
18. **Proposition 21.4.1, p. 766.** The characterisation omits `(x_t, y_t) ∈ C`, without which it
   is false: in Example 21.4.2 at `δ = 0.9` (`v_min = 7`), the path `(x_L, y_M)` forever satisfies
   `U_t ≥ (1 − δ) r(x_t, y') + δ v_min` for all `t`, `y'`, but it is not an SPE path
   (`cg_proposition_21_4_1_counterexample`). Corrected: `proposition_21_4_1`.
19. **Proposition 21.4.2, p. 767.** The condition must range over `y' ≠ y_t` and needs
   `(x_t, y_t) ∈ C`. At `y' = y_t` the printed inequality says `U_{t+1} ≥ U_1`, which a
   self-enforcing path need not satisfy: in a two-action game with `δ = 1/2`
   (`cg_rBool`), the path `(T, T), (F, F), …` is self-enforcing but violates the printed
   condition at `t = 2` (`cg_proposition_21_4_2_counterexample`). Corrected:
   `proposition_21_4_2`. Proposition 21.4.3 holds as stated (`proposition_21_4_3`).
20. **Computation of `v_min`, `v_max`, pp. 767–768.** The constraint for `v_min` has a typo
   `H(y(h))` for `H(h(y))`. "`v_min = min_y r(h(y), H(h(y)))`" is proved as a lower bound for all
   SPE values (`cg_V_lower`) and as an equality when the binding continuation `v₁` is an SPE
   value (`cg_vmin_eq`), which is the check the book then describes. "`v_max` solves
   `max r(h(y), y)` subject to the constraint" is proved in the form: every feasible stationary
   `r(x, y)` is an SPE value, and a greatest SPE value, if one exists, is the largest of them
   (`cg_vmax`); existence of the maximum is not claimed without compactness. The four-equation
   system is proved sufficient (its solutions are SPE values), with the fourth equation read
   with `H` the best response, i.e. as an inequality for every `y'` (`cg_four_equations`).
21. **Example 21.4.4, p. 769.** The figures `72`, `71.8`, `94.8` and `97` are unnormalised sums
   (the book's values of §21.4.2 are normalised by `1 − δ`); the normalised values are `7.2`,
   `7.18`, `9.48`, `9.7` (`example_21_4_4_arith`). The Ramsey outcome is played forever, not only
   "in the first period" (`example_21_4_4`).

### §21.4.5

22. **SPE characterisation of recursive strategies, p. 770.** As printed ((i)–(iii) at the
    initial state `v`, and (ii) only for `V(v, zʰ(v), y)`) the "if" direction is false: in
    Example 21.4.2 at `δ = 0.9`, a recursive strategy satisfies `v = 8 ∈ V` and (i)–(iii) at `v`
    but after the household-side history `(x_H, y_M)` it prescribes a non-competitive pair
    (`cg_definition_21_4_5_counterexample`). Corrected: the conditions must hold at every state
    of a bounded set closed under all `V(s, ξ, η)`, with promise keeping
    `s = (1 − δ) r(zʰ(s), zᵍ(s)) + δ V(s, zʰ(s), zᵍ(s))` (`cg_recursive_spe`). The "only if"
    direction holds when states are promised values (`cg_recursive_spe_only_if`), with (ii) for
    all `(ξ, η)`.
23. **Example 21.4.5, p. 770.** "Suppose `v^b > v^N` … we can construct the following SPE" is
    false: the trigger strategy needs the incentive constraint
    `(1 − δ) r(x^b, y') + δ v^N ≤ v^b` for all `y'`. In Example 21.4.2 at `δ = 0.9` the Ramsey value
    `9.7` exceeds `v^N = 8` but the trigger strategy is not an SPE (deviating pays
    `0.1 · 30 + 0.9 · 8 = 10.2`) (`cg_example_21_4_5_counterexample`). Corrected:
    `example_21_4_5` (the hypothesis `v^b > v^N` is not needed). The book refers to
    "Example 21.4.1"; the trigger strategy is that of Example 21.4.3.
24. **Example 21.4.6, pp. 770–771.** The stick-and-carrot strategy also needs the carrot's
    incentive constraint `v^R ≥ (1 − δ) r(x^R, y') + δṽ` for all `y'`. In Example 21.4.2 at
    `δ = 0.9`, the stick `(x_H, y_H)` with carrot `(x_L, y_L)` gives `ṽ = 8.73`, which satisfies
    the book's condition, but the strategy is not an SPE (deviating from the carrot pays
    `0.1 · 30 + 0.9 · 8.73 = 10.857 > 9.7`) (`cg_example_21_4_6_counterexample`). Corrected:
    `example_21_4_6`. Example 21.4.3's trigger strategy is proved through Example 21.4.5
    (`example_21_4_3`) on the compact action set `[0, K]`, `K ≥ λa`, because the repeated-game
    values need bounded payoffs (on `ℝ` a perpetual deviation has a divergent value).
25. **Example 21.4.3, p. 764: "`(1 − 2δ)λa ≤ π ≤ λa`, for `0 < δ < 0.5`".** The equivalence holds
    for every `δ ∈ [0, 1)` (`example_21_4_3_range`); the restriction only keeps the lower end
    positive.

### Exercises

26. **Exercise 21.6 (c), p. 772.** The worst value depends on `δ`, which part (c) leaves open.
    Proved for `5/8 ≤ δ < 1` (which includes part (d)'s `δ = 0.9`): `V = [1, 10]`, the worst value
    is `1`, every SPE attaining it starts with `(x_L, y_L)` and continues with value `1/δ`, and
    an explicit recursive strategy attains it; its outcome path is given recursively by
    `definition_21_4_5` (`ex_21_6_c`, `cg_ex216_V`).
27. **Exercise 21.6 (f), p. 772.** The naive answer `δ = 5/14` (from `10 ≥ 15(1 − δ) + δ v_min`
    with `v_min = 1`) is not attained: at `δ = 5/14` the value `1` is not an SPE value
    (`1 → 14/5 → 196/25 → 2744/125 > 10`, `cg_ex216_step`), so Ramsey repetition requires
    `δ > 5/14`; it is an SPE for every `δ ∈ [1/2, 1)` (`ex_21_6_f`). The exact infimum of the set
    of such `δ`, which lies in `(5/14, 1/2]`, is not formalised.
28. **Exercise 21.5, p. 771.** Proved in the strong form: at `δ = 0.88` no SPE has the repeated
    Ramsey outcome as its path (`ex_21_5`), besides the failure of the specific strategy of
    Example 21.4.4.
