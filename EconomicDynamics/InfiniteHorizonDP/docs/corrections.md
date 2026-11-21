# Corrections and departures: Miao Chapter 7

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 7,
Infinite-Horizon Dynamic Programming, pp. 193–230. Lean names are relative to
`Miao.InfiniteHorizonDP`. Every book item is located in the [source map](source-map.md).

## §7.1

1. **The integrals of Lemma 7.1.1 and (7.2) are extended integrals.** `J(s₁, C(π, s₁))` and `V`
   take values in `[−∞, +∞]` and need not be integrable, so `∫ J dP` and `∫ V dP` are read as
   `∫ f⁺ − ∫ f⁻ ∈ [−∞, +∞]` (`ih_eint`, convention `∞ − ∞ = −∞`). It is monotone with no
   measurability or integrability conditions (`ih_eint_mono`), equals `∫⁻` for `f ≥ 0`
   (`ih_eint_of_nonneg`), `−∫⁻ (−f)` for `f ≤ 0` (`ih_eint_of_nonpos`) and the Bochner integral for
   integrable real `f` (`ih_eint_coe`). Lemma 7.1.1 is proved in the three cases the proof names
   (`lemma_7_1_1` for all three via `ih_SignCases`; `lemma_7_1_1_nonneg`, `lemma_7_1_1_nonpos` by
   monotone convergence, `lemma_7_1_1_bounded` by dominated convergence, where `J(s₁, C(π, s₁))`
   comes out real, bounded and integrable). The bound of Assumption 7.1.1 is read for every
   history `sᵗ` (`Assumption711`); the measurability of `L_t` is not used. Lemma 7.1.1 does not
   use Assumption 5.1.1, and uses only `β > 0` from Assumption 5.1.2.
2. **Assumption 7.1.2(b) needs joint measurability.** The proof of Theorem 7.1.1 builds
   `d_t(s₁, …, s_t) = π^{s₁}_{t−1}(s₂, …, s_t)` and needs `d ∈ Π(s)`, i.e. `d_t` measurable on
   `Sᵗ` (Definition 5.1.1). The printed condition, measurability "as functions of `s`" of `π^s_0`
   and of `π^s_t(s^t_1)` for each fixed `s^t_1`, together with the measurability of each `π^s`, is
   *separate* measurability in `s₁` and in `(s₂, …, s_t)`, which does not give measurability on
   the product. As for Assumption 6.3.1 in Chapter 6, `Assumption712` asks for joint measurability
   (`po_JointMeas`), which makes the glued plan feasible (`ih_glue_feasible`). (No counterexample
   theorem: separately measurable non-jointly-measurable maps need non-standard σ-algebras.)
3. **Theorem 7.1.1 uses only Assumption 7.1.2(b).** Part (a) (`V` real-valued and measurable) is
   not needed: `ih_bellman_of_eps` proves (7.2) for the extended-real `V` from the ε-optimal
   jointly measurable plans alone; `theorem_7_1_1` is the book's statement. The last inequality of
   the proof is obtained with `2βε` instead of `βε` (`ih_eint_le_add`), which suffices.
   Assumption 5.1.1 is not used.
4. **Theorem 7.1.2: integrability, and hypotheses not used.** (7.4) and (7.5) presuppose the
   integrals `∫ V*(s_n) dμⁿ` and `∫ V* dP(s, a; ·)`; `theorem_7_1_2` assumes that `V*` is
   integrable against `P(s, a; ·)` for `a ∈ Γ(s)` and `V*(s_n)` against `μⁿ(s₀, ·; π)` for feasible
   `π` (measurability of `V*` is then not needed separately). Assumption 7.1.1 is not used (the
   proof telescopes finite sums and never uses Lemma 7.1.1), nor Assumption 5.1.1; from Assumption
   5.1.2 only `β ≥ 0` is used. "`G` nonempty with a measurable selection" is used as: a sequence
   of measurable selections `g_t` of `G` is given (`ih_GeneratedBy`).
   The remark "(7.4) is trivially satisfied if `V*` is bounded" is `ih_tvc_of_bounded` (with
   `0 ≤ β < 1` and `V*` measurable).
5. **The borrowing example, pp. 198–199.** The book writes the choice as `(c_t, a_{t+1})` but the
   constraint with `s_{t+1}`; we formalise the choice as the next state `s_{t+1} ≤ Rs_t`, with
   consumption `c_t = Rs_t − s_{t+1}` (`ih_borrowΓ`, `ih_borrowF`). `V ≡ +∞` holds for every
   `s₀`, not only `s₀ > 0` (`ih_borrow_V`). **Misprint:** along `c_t = 0`, `s_t = Rᵗs₀`,
   `βⁿ V̂*(s_n) = R s₀`, not `s₀` (`ih_borrow_tvc_fails`, `ih_borrow_tvc_misprint`); the
   conclusion (7.4 fails for `V̂*`) is unaffected.
6. **Corollary 7.1.1.** Same integrability reading as item 4: `Π̂(s)` (`ih_PiHat`) consists of the
   feasible plans for which the expectations in (7.4) exist and (7.4) holds. The finiteness of `V`
   is a conclusion, not a hypothesis; Assumption 7.1.1 is not used; only `β ≥ 0`
   (`corollary_7_1_1`). For Example 7.1.1 a deterministic version is proved
   (`ih_det_corollary_7_1_1`).
7. **Example 7.1.1: the printed value function is wrong.** The book prints
   `V(K) = (1/(1 − β))[ln(1 − αβ) + (β/(1 − αβ)) ln(αβ)] + (α/(1 − αβ)) ln K`. The coefficient of
   `ln(αβ)` is `αβ/(1 − αβ)`, not `β/(1 − αβ)`: the value function is
   `A + B ln K` with `B = α/(1 − αβ)`, `A = [ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ)]/(1 − β)`
   (`example_7_1_1`, `example_7_1_1_guess`), and the printed function differs from it at every `K`
   for all `0 < α, β < 1` (`example_7_1_1_value_misprint`). The policy `K′ = αβK^α`, (7.7) and the
   book's verification of conditions (a) and (b) of Corollary 7.1.1 are correct
   (`example_7_1_1_policy`, `eq_7_7`, `example_7_1_1_PiHat_iff`, `example_7_1_1_dichotomy`).
   The model is the deterministic dynamic program on `K > 0` with `K′ ∈ (0, K^α)`: the book's
   `C, K′ ≥ 0` allow `ln 0 = −∞`, while rewards are real-valued; the supremum is the same. The
   example is formalised in the deterministic framework rather than the Markov decision model of
   Theorem 7.1.2, where log utility fails the integrability of Assumption 5.1.4 along some plans.
   The book's derivation, the limit `T → ∞` of the `T`-horizon values (6.5), also gives the
   corrected constant (`example_7_1_1_limit`): the coefficient of `ln(αβ)` in the limit of `A₀`
   is `Σ βʲ · αβ/(1 − αβ) = αβ/((1 − αβ)(1 − β))`.
8. **Theorem 7.1.3 holds only almost surely.** As for Theorem 6.3.3, `π*_t(sᵗ) ∈ G(s_t)` holds for
   `μᵗ(s₀, ·; π*)`-almost every `sᵗ` (`theorem_7_1_3`), not for all `sᵗ`
   (`theorem_7_1_3_counterexample`: `S = A = Bool`, next state always `true`, reward `1` for the
   action `true`, `β = 1/2`, `V ≡ 2`; the plan `π₀ = true`, `π_t(sᵗ) = s₁` is optimal from `true`
   but `π₁(false) = false ∉ G(false) = {true}`).
9. **The proof of Theorem 7.1.3 has a gap; the (a.e.) statement survives.** The book's proof uses
   Theorem 7.1.2 to get `V(s₁) = J(s₁, C(π^g, s₁))` (7.13) for the plan `π^g` generated by a
   selection of `G`. Theorem 7.1.2 needs the transversality condition (7.4), which is not a
   hypothesis of Theorem 7.1.3, and without (7.4) a plan generated by `G` need not be optimal
   (`theorem_7_1_3_proof_gap`: without borrowing, `V(s) = Rs` solves the Bellman equation, every
   feasible choice is in `G`, and never consuming, `g(s) = Rs`, is worth `0 < V(s₀)`). The
   statement nevertheless holds without (7.4): `ih_converse_step` compares `π*` with `V` directly
   (`V(s₀) = u + β∫J(·, C(π*, ·)) ≤ u + β∫V ≤ V(s₀)`, as in SLP Theorem 9.4), which gives
   `π*_0 ∈ G(s₀)` and (7.15) without `π^g`; `ih_converse_ae` runs the induction. So the hypotheses
   that `G` is nonempty with a measurable selection are not needed. Added hypotheses: `V`
   integrable against `P(s, a; ·)` for `a ∈ Γ(s)` (so `G` is defined by a Bochner integral), `u`
   measurable (so the set of histories where `π*_t ∈ G` is measurable), and `β > 0` (to cancel
   `β`). Assumption 5.1.1 is not used.
10. **The plan `π^g`, p. 202,** is defined "for `t = 1, …, T − 1`", a leftover from the finite
    horizon; it is meant for all `t ≥ 1` (the proof of `theorem_7_1_3` does not use `π^g`).
11. **The model.** All results are stated for Chapter 5's `MDP` with Assumption 5.1.4 (which makes
    the process stationary, so the process from date `1` is the process itself, `ih_shift_eq`)
    and Markov kernels (`MDP.IsMarkov`, part of the model on p. 136). The rewards and kernels are
    those of date `0`, `u = u₀`, `P = P₀`.

## §7.2 and §7.3–7.3.1

### §7.2

12. **Misprints in (7.16) and around it, p. 205.** (7.16) integrates against `dz′`; the integral
   is against `ds′` (`eq_7_16`). The text calls the fixed-point equation "the Bellman equation
   (7.19)"; it is (7.2) (`br_bellman_iff`: `f ∈ C(S)` solves (7.2) of §7.1 iff `Tf = f`). The sup
   norm is printed `sup_{s ∈ X}` (read `S`), and "`Tf` is continuous in `(x, z)`" means
   continuous in `s ∈ S`: `S` is a general state space in §7.2.
13. **Setting of Theorem 7.2.1.** `S` and `A` are metric spaces whose σ-algebra on `S` contains
   the open sets; Assumptions 6.4.1–6.4.2 (convex Borel sets) are not used. From Assumption 5.1.2
   only `0 < β < 1` is used (`theorem_7_2_1`). The policy correspondence `G` of the theorem is the
   one of §7.1 (`ih_G`, defined with the extended integral), which equals the argmax
   correspondence of (7.16) at the fixed point (`br_ih_G_eq`).
14. **The deduction of p. 205** ("By this theorem and the Measurable Selection Theorem … any plan
   generated by `G` gives an optimal Markov plan"). The process must be stationary (as in all of
   Chapter 7), and the rewards measurable for Assumption 5.1.4 (they are, by continuity, once the
   open sets of `S × A` are measurable) (`p205`). The Measurable Selection Theorem (SLP Theorem
   7.6) needs actions in a set `A₀ ⊆ ℝᵐ` (`br_exists_selection`, `p205_selection`,
   `p205_stationary`). The transversality condition (7.4) of Theorem 7.1.2 holds because `V` is
   bounded (`ih_tvc_of_bounded`).
15. **Theorem 7.2.2.** The `N`-horizon problem has `u_t = u` and `u_N = 0`; `V_t^N = T^{N−t}0`
   comes from Theorem 6.3.2 with measurable selections of the maximizers of
   `u + β ∫ T^{N−t−1}0 dP` (`br_finite_horizon`, `br_V0_eq`), whose existence again needs actions
   in `A₀ ⊆ ℝᵐ` (`br_exists_policy`). With this, (7.17), `T^N v₀ → V`, `V₀^N = T^N 0` and (7.18)
   hold as stated (`eq_7_17`, `br_tendsto_iterate`, `theorem_7_2_2`, `p206_notation`).

### §7.3 and §7.3.1

16. **The control model as a Markov decision process.** Following the book ("using Lemma 6.4.1
   and Theorem 7.2.1"), Theorems 7.3.1–7.3.5 are proved for the stationary MDP of the control
   model (`br_ctrlMDP`: state space `X × Z`, action space `A`, reward `u 0` of `OCModel` at every
   date, kernel `(x, z) ↦ (φ(x, a, z, z′), z′)`), so that (7.20) is the operator (7.16) of this
   MDP, equal to the right side of (6.29) (`eq_7_20`). The spaces `E ⊇ X`, `F ⊇ A`, `Z` are
   metric with their Borel sets, `F` and `Z` second countable. Lemma 6.4.1 enters as a class `P`
   of functions on which it holds and which contains the bounded functions (`OCModel.ExpCont`);
   both cases of Assumption 6.4.3 give one (`theorem_7_3_1_compact`, `theorem_7_3_1_countable`).
   Assumptions 6.4.3–6.4.5 and 7.3.1 are packaged as `br_Standing (br_ctrlMDP M h645.1)`
   (`br_ctrl_standing`), which the later theorems take as a hypothesis. Assumptions 6.4.1–6.4.2
   are not used in Theorems 7.3.1–7.3.2.
17. **Theorem 7.3.2.** Correct as stated; the proof's "increasing" for `C′(S)` is read as
   nondecreasing, which makes `C′(S)` closed (`br_isClosed_mono`), and `T` maps it into the
   strictly increasing functions (`br_T_strictMono`). Only `β ≥ 0` is used.
18. **Theorem 7.3.3 is false without Assumption 6.4.11.** The hypotheses list Assumptions 5.1.2,
   6.4.1–6.4.5, 6.4.8, 6.4.9, 6.4.12, 7.3.1, 7.3.2 and 7.3.3 but not 6.4.11 (convexity of the graph
   of `Γ(·, z)`), which the concavity argument needs. Counterexample
   (`theorem_7_3_3_counterexample`): `X = A = [0, 1]`, `Z` a point, `Γ(x, z) = {0, 1}`,
   `φ(x, a, z, z′) = a`, `u(x, z, a) = 4x − x²/2 − (x − a)²`, `β = 1/10`. All the listed
   assumptions hold, but the solution of (7.19), `V(x) = 4x − 3x²/2 + max(0, 2x − 11/18)`
   (`br_cexV_fixed`), has `V(11/36) < (V(0) + V(11/18))/2`. `theorem_7_3_3` adds Assumption
   6.4.11.
19. **The proof of Theorem 7.3.3: the closed set `C′(S)`.** The book takes `C′(S)` = the functions
   concave in `x`. `f(φ(x, a, z, z′), z′)` is concave in `(x, a)` only if `f(·, z′)` is also
   nondecreasing (with `φ` concave, Assumption 6.4.12) or `φ` is affine, so `T` need not map
   `C′(S)` into itself. We take `C′(S)` = concave and nondecreasing in `x` (closed:
   `br_isClosed_concave`, `br_isClosed_mono`), mapped by `T` into the strictly concave, strictly
   increasing functions (`br_T_strictConcave`, `br_compConcave_of_mono`, `br_T_strictMono`), as
   in SLP Exercise 9.7d. For affine `φ` (e.g. the Euler class) concavity alone suffices and
   Assumptions 6.4.8, 6.4.9 and 7.3.2 can be dropped (`theorem_7_3_3_affine`,
   `br_compConcave_of_affine`).
20. **`G` need not be single-valued** (the same issue as Theorem 6.4.3 in Chapter 6). Assumption
   7.3.3 is strict only in `x`. Counterexample (`theorem_7_3_3_policy_counterexample`):
   `X = A = Γ(x, z) = [0, 1]`, `φ(x, a, z, z′) = x`, `u(x, z, a) = 4x − x²/2`, `β = 1/10`; all the
   book's hypotheses and Assumption 6.4.11 hold, but every feasible action is optimal at every
   state. `theorem_7_3_3` and `theorem_7_3_3_affine` add that `φ(x, ·, z, z′)` is one-to-one on
   `A` (`OCModel.PhiInjA`, true for `φ = a`) and use `β > 0`; then the maximizer is unique
   (`br_G_unique`) and `g` is continuous (`br_policy_spec`).
21. **p. 209, the optimal plan generated by `g`.** Proved as: the stationary plan
    `π_t(sᵗ) = g(s_t)` of the control MDP is optimal and attains `V` (by `p205`), and the policy
    it induces on shock histories is `a_t(zᵗ) = g(x_t, z_t)` with
    `x_{t+1} = φ(x_t, a_t, z_t, z_{t+1})` (`p209`, `br_dyn`, `br_dyn_spec`).
22. **Theorem 7.3.4: the neighborhood step.** The proof says "By Assumption 6.4.4, there is some
    open neighborhood `D` of `x₀` such that `g(x₀, z₀) ∈ int(Γ(x, z₀))`, all `x ∈ D`". Continuity
    of `Γ` does not give this (e.g. `Γ(x) = {y : |x| ≤ |y| ≤ 1}` is continuous and compact-valued,
    `0 ∈ int Γ(0)`, but `0 ∉ Γ(x)` for `x ≠ 0`; not formalised). It holds because `Γ(·, z₀)` is
    lower hemicontinuous and convex-valued (Assumption 6.4.11, which is a hypothesis of the
    theorem), and only `g(x₀, z₀) ∈ Γ(x, z₀)` is needed, not interiority (`p210_neighborhood`, via
    `br_eventually_mem_of_mem_interior`, valid in `ℝⁿ`).
23. **Theorem 7.3.4: hypotheses and statement.** The theorem is proved for `X, A ⊆ ℝⁿ` with `n`
    arbitrary (Chapter 6 had `n = 1`) (`theorem_7_3_4`, `eq_7_22`). Its hypothesis list omits what
    makes `V` and `g` exist: Assumption 7.3.1 (`u` bounded and continuous; Assumption 7.3.4 only
    gives differentiability on the interior) and the half of Assumption 6.4.5 saying that
    `φ = a` maps `X × A` into `X` (`A ⊆ X`); both are added. "By Theorems 7.3.1 and 7.3.3": the
    strict concavity of `V` and the single-valuedness of `G` come from the affine version of
    Theorem 7.3.3 (`theorem_7_3_3_affine`; `φ = a` is affine and one-to-one, `br_euler_affine`),
    so Assumptions 6.4.8, 6.4.9, 6.4.12 and 7.3.2 are not needed. The book writes
    `g : X × Z → ℝ`; `g` maps into `A`. "`V(·, z₀)` is continuously differentiable at `x₀`" is
    proved as differentiability at `x₀` with derivative (7.22).
24. **Theorem 7.3.5.** The hypotheses need the corrections of items 18–20 (Assumption 6.4.11 and
    `φ(x, ·, z, z′)` one-to-one), and `v₀` must be concave **and nondecreasing** in `x` (the
    book's `C′(S)`: concave on `X`), for the reason of item 19 (`theorem_7_3_5`,
    `br_iterate_concave`). Then `gₙ`, the maximizer for `vₙ = Tⁿv₀`, is unique for `n ≥ 1`
    (the book's `n = 1, 2, …`), `gₙ → g` pointwise, and uniformly when `X` and `Z` are compact
    (SLP Theorem 3.8).
25. **The remark after Theorem 7.3.5, p. 211: off by one.** `Tⁿ0 = V₀ⁿ` is correct (`p211`, from
    `theorem_7_2_2`). But "`gₙ` is equal to the associated initial policy function" of the
    `n`-horizon problem is off by one: the `n`-horizon initial decision maximizes
    `u + β ∫ V₀^{n−1}`, `V₀^{n−1} = T^{n−1}0`, while `gₙ` maximizes `u + β ∫ Tⁿ0`. So `gₙ` is the
    initial policy of the `(n + 1)`-horizon problem: every optimal plan of the `(n + 1)`-horizon
    problem generated by measurable selections of the Bellman maximizers starts with `gₙ`
    (`p211`, stated for `n + 1 ≥ 1` with actions in `A ⊆ ℝᵐ`).

## §7.3.2 and Exercises 7.1–7.3

### The weighted space and Theorem 7.3.6

26. **`C_ϕ(S)` (p. 212)** is stated with the bound `|f| ≤ Bϕ`, equivalent to
   `sup |f/ϕ| < ∞` for `ϕ > 0` (`wn_inC_iff`). The state space is any topological space.
   Completeness (Exercise 7.1, `ex_7_1`) is proved as "every `‖·‖_ϕ`-Cauchy sequence in
   `C_ϕ(S)` converges in `‖·‖_ϕ` to an element of `C_ϕ(S)`", by transport to bounded continuous
   functions `f ↦ f/ϕ`; the norm axioms are `ex_7_1_norm`.
27. **Theorem 7.3.6, discounting with `a = 0`.** The proof applies (b) with
   `a = ‖f − g‖_ϕ`, but (b) is assumed only for `a > 0`. When `‖f − g‖_ϕ = 0`, `f = g` and the
   estimate is immediate (`wn_le_add_of_disc`); the theorem is true as stated.
28. **Theorem 7.3.6, condition (c) and continuity.** As stated (`T : C_ϕ(S) → C_ϕ(S)`), (c) is
   redundant (`theorem_7_3_6_c`), and `theorem_7_3_6` omits it. The proof uses (c) to get
   `‖Tf‖_ϕ < ∞`, which does not give continuity of `Tf`. What the proof shows is
   `wn_theorem_7_3_6_of_continuous`: if `T` maps `C_ϕ(S)` into continuous functions, (a)–(c)
   make it a self-map of `C_ϕ(S)` (`wn_theorem_7_3_6_selfMap`). The book's bound
   `Tf ≤ T0 + θ‖f‖_ϕϕ` is one-sided; bounding `|Tf|` also needs `T0 ≤ Tf + θ‖f‖_ϕϕ`.

### Example 7.3.1

29. **Discounting** holds for every `a ≥ 0` (the step uses `a ≥ 0`, `β ≥ 0` and `y ≤ AK`)
   (`example_7_3_1_discount`). The weight `ϕ(K) = K^γ` vanishes at `0`, so Theorem 7.3.6 does
   not apply literally; the example is proved directly on the homogeneous functions, which are
   `f(K) = f(1)K^γ` (`wn_homog_eq`), so that `‖f‖_ϕ = |f(1)|` (`example_7_3_1_norm`) and the
   fixed-point problem is the scalar contraction `c ↦ Tf_c(1)` (`example_7_3_1`). Uniqueness is
   as functions on `ℝ₊`.
30. **"If" is "iff" (for `γ < 1`).** If `βA^γ ≥ 1` there is no fixed point among the homogeneous
   functions (`example_7_3_1_no_fixedPoint`). The explicit fixed point `V = BK^γ` is not
   formalised.

### Duran's approach

31. **Exercise 7.2.** Only nonempty compact `Γ(x)` and continuous `u, f, g` are used; both sups
   are attained, so finite (`ex_7_2_attained`, `ex_7_2`). (7.27) is stated with the attained
   sup; `eq_7_27_iff` gives the pointwise form. The contraction (`wn_duran_contraction`) also
   assumes `θ ≥ 0`, which (7.27) implies when `X` is nonempty.
32. **(7.28).** The book bounds `Tf` only from above; `eq_7_28` bounds `|Tf|` through
   `|Tf − T0| ≤ θ‖f‖_ϕϕ`. "Continuity is routine" is the Theorem of the Maximum (copied SLP
   Theorem 3.6), under Assumptions 7.3.6–7.3.7 (`wn_duran_continuous`). The fixed point result
   is `wn_duran_fixed_point`.

### Example 7.3.2 and Exercise 7.3

33. **The chain on p. 216 is false at its middle step.** Writing
   `r(z) = (1 + F(z)^γ)/(1 + z^γ)`, the first step is an equality
   (`example_7_3_2_first_step`) and `r(z) → A^γ` (`example_7_3_2_limit`), but `r(z) ≤ A^γ` fails:
   for `A = 441/400`, `α = γ = 1/2`, some `x, y` give `ϕ(y)/ϕ(x) = 49/40 > 21/20 = A^γ`
   (`example_7_3_2_counterexample`); with `β = 40/49`, `βA^γ = 6/7 < 1` but (7.27) holds for
   no `θ < 1` (`example_7_3_2_7_27_fails`). Whenever `γ + α > 1` the bound fails for every
   `A > 1` (`example_7_3_2_fails`: `F(z)^γ − (Az)^γ ≥ γ(A + 1)^{γ−1}z^{γ+α−1} → ∞`).
34. **Corrected condition.** For the weight `ϕ_M = M + F^γ`, `M > 0`,
   `ϕ_M(y)/ϕ_M(x) ≤ A^γ + M^{α−1}` on `Γ(x)` (`wn_ratio_le`), so (7.27) holds with
   `θ = β(A^γ + M^{α−1})` (`example_7_3_2`); for the book's weight (`M = 1`) this is
   `θ = β(A^γ + 1)`. Under the book's assumption `βA^γ < 1`, a large `M` gives `θ < 1`
   (`wn_exists_M`), and since `ϕ ≤ ϕ_M ≤ Mϕ` the space `C_{ϕ_M}` is the book's `C_ϕ`; so the
   book's conclusion, a unique solution of the Bellman equation in `C_ϕ(ℝ₊)` when `βA^γ < 1`,
   is true (`ex_7_3`, which is Exercise 7.3). (7.28) holds as printed: `T0 = F^γ < ϕ_M`
   (`example_7_3_2_T0`). `γ ∈ (0, 1]` suffices.

### The log AK model (p. 217)

35. **"(7.27) can never be satisfied"** is proved in the strong form: for every `A > 0`,
    `β > 0`, `θ`, and every state `x > 0`, some `y ∈ (0, Ax]` has `βϕ(y)/ϕ(x) > θ`
    (`wn_log_ak_7_27_fails`, `wn_log_ak_7_27_never`): the sup in (7.27) is `+∞` at every state.
    The choice set is `(0, Ax]`, since `ln 0` is undefined (Lean's `log 0 = 0` would make
    `ϕ(0) = 1`, which the book does not intend).

## §§7.4–7.5

### Setting (both sections)

36. **Stochastic setting.** As in the Chapter 6 Maximum Principle, the shocks are an adapted
   process on a filtered probability space, plans are adapted, and `E_t` is `P[· | ℱ_t]`. The
   Markov structure (Assumption 6.4.3, `Q`) is used only where the book integrates against
   `Q(z, ·)` (the links with dynamic programming, `OCModel.link_7_30`, `OCModel.link_7_31`,
   `eu_EulerModel.eq_7_34`, via `IsMarkovCond` / `EulerMarkov`); Theorems 7.4.1, 7.5.1 and 7.5.2
   hold for any adapted shock process (the book's remark on p. 225 that 6.4.3 can be weakened).
37. **The objective.** The objective `J = E Σ βᵗ u` is replaced by the limit of the partial sums
   `S_T = Σ_{t ≤ T} βᵗ E u(·)` (`OCModel.eu_partialJ`, `eu_EulerModel.eu_partialJ`), which is
   what all the proofs compare; the two agree under dominated or monotone convergence. All
   rewards and the products appearing in the telescoping sums are assumed integrable
   (`OCModel.eu_MPIntInf`, `eu_EulerModel.EulerInt`, and the integrability hypotheses of
   Theorem 7.5.1 and Example 7.5.1); optimality is among plans with these properties.
38. **Optimality and the limit step.** The sufficiency proofs give `S_T(x) ≤ S_T(x*) + w_T` with
   `w_T → 0`. The book then "takes limits", which needs both limits to exist; the competing plan
   may have `J = −∞` or partial sums that do not converge. We prove the conclusion both for limits
   in `[−∞, +∞]` (`OCModel.theorem_7_4_1_limit`, `eu_EulerModel.theorem_7_5_2_limit`) and, when
   only `S_T(x*) → J*`, in the form "eventually `S_T(x) ≤ J* + ε`" (`theorem_7_4_1_eventually`,
   `theorem_7_5_2_eventually`); `eu_EulerModel.IsOptimal` uses the latter form.

### §7.4

39. **(7.30)–(7.31) from (7.29).** The derivative is taken pathwise in the summands of the
   Lagrangian (`OCModel.eq_7_29_a`, `OCModel.eq_7_29_x`) and the first-order conditions are
   `E_t[∂L/∂a_t] = 0`, `E_t[∂L/∂x_t] = 0`; their `E_t` are `∂H/∂a` and `∂H/∂x − μ_t`
   (`OCModel.eq_7_30`, `OCModel.eq_7_31`), given measurability and integrability of the terms.
40. **Theorem 7.4.1, hypotheses.** As in Theorem 6.5.1 the concavity used is that of the
   pathwise Hamiltonian `u + βμ_{t+1}φ` on `X × A`; it follows from Assumptions 7.3.3 and 6.4.12
   and `μ*_{t+1} ≥ 0`. Only `β ≥ 0`, not the strict part of Assumption 7.3.3, and not
   Assumption 6.4.3 are used. The interiority `x*_t ∈ int X`, `a*_t ∈ int Γ(x*_t, z_t)` is used
   only for differentiability of `u` and `φ` at `(x*_t, a*_t)`, and we need `Γ ⊆ A`. The
   rewards may depend on `t` (`OCModel.u t`). `OCModel.theorem_7_4_1`, `OCModel.eu_mp_core`.
41. **The remark "if `φ` is linear in `(x, a)`, `μ*_{t+1} ≥ 0` is not needed" (p. 220) is false.**
   `μ* ≥ 0` is used twice: for the concavity of the Hamiltonian (which an affine `φ` makes
   unnecessary) and in the last step `−Eβ^{T+1}μ*(x* − x) ≥ −Eβ^{T+1}μ*x*`, which needs
   `μ*_{T+1}x_{T+1} ≥ 0`. Counterexample (`remark_7_4_1_counterexample`): `X = A = Γ = ℝ₊`,
   `x_{t+1} = a_t` (linear), `β = 1/2`, `u(x, a) = −x + 3a/8 − 1/(1 + x)` (Assumptions 6.4.12,
   6.4.14, 7.3.3 with the strict inequality, 7.3.4 hold); the constant plan `x* = a* = 1` with
   `μ* = −3/4` is interior and satisfies (7.30), (7.31), (7.32), but `x_t = 8ᵗ` has partial sums
   larger by at least `1` at every `T`. Corrected statement (`OCModel.remark_7_4_1_affine`):
   for affine `φ` the sign of `μ*` may be dropped, against competing plans with
   `E[μ*_{T+1}x_{T+1}] ≥ 0` for all `T` (e.g. `μ* ≥ 0`, as in the theorem).

### §7.5

42. **Euler equation from the Bellman equation (p. 221).** The first-order condition of (7.21)
   needs `y ↦ ∫ V(y, z′)Q(z, dz′)` differentiable with the derivative under the integral sign
   (a hypothesis of `eu_EulerModel.foc_7_21`); the functional Euler equation needs the envelope
   condition (7.22) at `g(x, z)` (`euler_functional`); the sequence form (7.34) needs the Markov
   property and integrability of `u_x` along the plan (`eq_7_34`).
43. **The variational characterisation (p. 222)** holds in expectation: `x*_{t+1}` maximises
   `E[u(x*_t, z_t, y) + βu(y, z_{t+1}, x*_{t+2})]` over `ℱ_t`-measurable feasible `y`
   (`variational_7_5`, `β > 0`). The pathwise Euler equation is derived from it for
   deterministic plans and shocks, assuming every `y` near `x*_{t+1}` is a feasible variation
   (local interiority in the graph of `Γ`, which "`x*_{t+1} ∈ int Γ(x*_t, z_t)`" does not give
   for the constraint `x*_{t+2} ∈ Γ(y, z_{t+1})`) (`theorem_7_5_1_euler`,
   `theorem_7_5_1_euler_seq`). The stochastic necessity of (7.34) ("we have outlined the
   proof") is not formalised: it needs differentiation under `E_t` and a uniform interiority
   radius across states; in `theorem_7_5_1` the Euler equation is a hypothesis.
44. **(7.36).** The last-period problem is solved state by state over `x_{T+1} ∈ [0, z_TF(x_T)]`;
   the first-order condition gives `u′(c*_T)x*_{T+1} = 0` pathwise when `x*_{T+1} < z_TF(x_T)`,
   hence `E[βᵀu′(c*_T)x*_{T+1}] = 0` (`eq_7_36`, `eq_7_36_expect`). The book's
   "`E[βᵀu′(c*_T)] ≥ 0`, with inequality if `x*_{T+1} = 0`" is the sign `u′ ≥ 0`.
45. **(7.35) ⇔ (7.37)** holds given the Euler equation, `x_{T+1}` `ℱ_T`-measurable and
    integrability of `u_x(T + 1)` and `u_x(T + 1) · x_{T+1}`, through the identity
    `E βᵀu_a(T)·x_{T+1} = −E β^{T+1}u_x(T + 1)·x_{T+1}` (`eq_7_35_iff_7_37`). (7.37) is (7.32) with
    `μ_T = V_x(x_T, z_T)` given the envelope condition (`eq_7_37_is_7_32`).
46. **(7.38)** is stated for real-valued concave `f` on `[0, 1]` (`eq_7_38`); for
    `f(γ) = −∞` the right side is `+∞` and there is nothing to prove.
47. **Theorem 7.5.1: feasibility of the shifted plan.** After date `T` the plan
    `(λx*_t, λx*_{t+1})` is feasible by convexity of `X ∋ 0`, Assumption 6.4.11 and
    `0 ∈ Γ(0, z)` (`eu_cone_feasible`). At the junction the proof needs
    `λx*_{T+1} ∈ Γ(x*_T, z_T)`, which these hypotheses do not give: `theorem_7_5_1_shift_infeasible`
    (convex-graph `Γ_k(x) = [x(1 − 1/(k+1)), 2x]`, `0 ∈ Γ_k(0)`, `1 ∈ int Γ_k(1)` for every `k`,
    yet for every `λ < 1` some `k` has `λ ∉ Γ_k(1)`; with a shock taking each value `k` with
    positive probability no shifted plan with `λ < 1` is feasible). We assume the junction
    condition for `λ ∈ [λ₀, 1)` (`hjunc` of `theorem_7_5_1`); it holds when `0 ∈ Γ(x, z)` for all
    `x` (`eu_junction_of_zero_mem`, `theorem_7_5_1_of_zero_mem`), and for deterministic plans for
    `λ` near `1` by interiority. Only `λ` near `1` is needed: the `ξ`-plan enters only through
    the convergence of its partial sums.
48. **Theorem 7.5.1: the sign of `u_a · x*`.** The first inequality of the final display,
    `0 ≤ −Eβᵀu_a·x*_{T+1}`, needs `u_a ≤ 0` (from the Euler equation and `u_x ≥ 0`, which
    Assumption 7.3.2 gives at interior points, `eu_ux_nonneg`) and `x*_{T+1} ≥ 0`. The theorem
    assumes only `0 ∈ X`; we assume `X ⊆ ℝⁿ₊`. Without it the argument still gives
    `−Eβᵀu_a·x*_{T+1} ≤ R_T/(1 − ξ)` with `R_T → 0` (`eu_kami_limit`), i.e. only
    `liminf_T Eβᵀu_a·x*_{T+1} ≥ 0`.
49. **Theorem 7.5.1: the passage `λ → 1`** exchanges a limit with `E`. We use monotone
    convergence: by (7.38) the junction quotient `(u(x*_T, z_T, λx*_{T+1}) − u(x*_T, z_T, x*_{T+1}))/(1 − λ)`
    is increasing in `λ`, and by differentiability (Assumption 7.3.4 and interiority, which needs
    `x₀ ∈ int X` at `T = 0`) it tends to `−u_a·x*_{T+1}`; this needs `u_a·x*_{T+1}` integrable
    (`eu_kami_limit`). The tail `R_T → 0` uses that both `J(x*)` and `J(ξx*)` are finite, as the
    book says. `theorem_7_5_1` concludes (7.35); `theorem_7_5_1_737` adds (7.37).
50. **Theorem 7.5.2: "`u_a < 0`".** Assumption 7.3.2 (strictly increasing) gives only
    `u_x ≥ 0` at interior points (`eu_ux_nonneg`): a strictly increasing function can have zero
    derivative (`eu_strictMono_deriv_zero`, `x ↦ x³` at `0`). Hence `u_a = −βE_t u_x ≤ 0` a.s.,
    which with `x_{T+1} ≥ 0` is all the proof uses. With concavity (Assumption 7.3.3) `u_x > 0` at
    interior points (`eu_ux_pos`), so the strict sign holds for deterministic plans with `β > 0`.
51. **Theorem 7.5.2: the displayed identity** has two misprints: the Euler terms
    `βᵗ(u_a(t) + βu_x(t + 1))·(x*_{t+1} − x_{t+1})` carry `β` in front of `u_x`, and their sum runs
    to `T − 1`, not `T` (the date-`T` term is the boundary term written separately)
    (`eu_euler_sufficient`).
52. **Theorem 7.5.2: hypotheses.** The derivative of `u` at `(x*_0, x*_1)` is used, so
    `x₀ ∈ int X` is needed (`x*_{t+1} ∈ int Γ(x*_t, z_t)` covers `t ≥ 1` only), and `Γ ⊆ X`.
    Only concavity (not the strict part of 7.3.3) is used. The core `eu_euler_sufficient` needs
    concavity only on a set containing the candidate's and the competitor's `(x_t, x_{t+1})`
    (e.g. the graph of `Γ`), differentiability along `x*`, and `u_x ≥ 0` along `x*`
    (`theorem_7_5_2` derives these from the book's assumptions).
53. **Example 7.5.1: applying Theorem 7.5.2.** In the book's change of variables (state = saving
    `y_t = x_{t−1} − c_{t−1}`, `R_0 = 1`; `eu_phelpsModel`) the problem is in the Euler class
    with `X = ℝ₊` and `u_x = Ru′(c) > 0`, `u_a = −u′(c) < 0`. Theorem 7.5.2 does not apply
    verbatim: off the graph of `Γ` (`c ≤ 0`) the reward is undefined (`−∞` for `γ ≥ 1`), so
    Assumptions 7.3.2–7.3.4 fail on `X × X`, and the strict part of 7.3.3 fails on the graph
    (`u` is constant along `(y, y′) + s(1, R)`). Optimality follows from `eu_euler_sufficient` with
    concavity on the graph (`example_7_5_1`). Consumption is kept positive (`y′ < Ry`; the book
    allows `c = 0` for `γ < 1`).
54. **Example 7.5.1: iid returns.** The iid assumption is used only through
    `E_t[R_{t+1}^{1−γ}] = m` (which follows from independence of `R_{t+1}` and `ℱ_t`:
    `example_7_5_1_condmoment`). Integrability of `R_{t+1}^{1−γ}`, of the partial products
    `Π_{s≤t+1} R_s^{1−γ}` and of `((1 − A)x_t)^{−γ}R_{t+1}^{1−γ}` is assumed: the last needs a
    moment such as `E[R^{−γ}] < ∞`, which the book does not state. With these, the printed
    computation `E[βᵗc_t^{−γ}x_t] = βᵗA^{−γ}(1 − A)^{t(1−γ)}x₀^{1−γ}E[Π_{s=1}^t R_s^{1−γ}]` is
    correct (`example_7_5_1_tvc_formula`), `E[Π] = mᵗ` (`example_7_5_1_prod_moment`), and by (7.39)
    the expression is `A^{−γ}x₀^{1−γ}(1 − A)ᵗ → 0` (`example_7_5_1_tvc_det`, `example_7_5_1_tvc`).
    The book's condition "`0 < βE[R^{1−γ}]^{1/γ} < 1`" is equivalent to `0 < βm < 1`
    (`example_7_5_1_A_mem`); (7.39) is the unique solution in `(0, 1)` (`eq_7_39_unique`); the
    book's transversality condition `lim E[βᵗc_t^{−γ}x_t] = 0` is (7.37) in the saving variables,
    and (7.35) is `−(1 − A)` times it.

## §7.6, Exercises 4–10

### Cross-references

55. **Exercises 7.7–7.9 cite the wrong Chapter 6 exercises (off by one).** Exercise 7.7
   (Schechtman–Escudero) says "Exercise 8 of Chapter 6" (the deterministic CRRA problem); the
   Schechtman–Escudero model is Exercise 6.9. Exercise 7.8 (Phelps) says "the model in Exercise 6
   of Chapter 6" (Markov labour income); the Phelps model is Exercise 6.7. Exercise 7.9
   (Levhari–Mirman–Zilcha) says "Exercise 9 of Chapter 6"; the LMZ model is Exercise 6.10. We
   treat the intended exercises 6.9, 6.7 and 6.10 (`ex_7_7_limit`, `ex_7_8_finite`).

### Exercise 7.4

56. **"Restrict the state space" made precise.** For `b ≥ x_m`, `[0, b]` is invariant under
   `Γ(K) = [0, f(K)]` (`ex_7_4_invariant`); the value of the problem from `K₀ ∈ [0, b]` equals
   the value of the problem whose state space is `[0, b]` (`ex7_vstar_restrict`,
   `ex_7_4_restrict`), and with `u` continuous on `[0, b]` the reward is bounded there
   (`ex_7_4_bounded`). For `K₀ ∈ [0, x_m]` this is the book's `X = [0, x_m]` (`ex_7_4`). Only
   monotonicity, `f(0) = 0` and the bounds on `f` are used; continuity of `f` and of `u` enter only
   in `ex_7_4_eventually` and `ex_7_4_bounded`.
57. **`X = [0, x_m]` is not a valid state space for `K₀ > x_m`.** Feasible paths from `K₀ > x_m`
   need not enter `[0, x_m]`: with `f(x) = min(x, (1 + x)/2)` (which satisfies all hypotheses
   with `x_m = 1`, `ex7_cex_hyp`), the path `K_t = 1 + 2^{−t}` from `K₀ = 2` is feasible and stays
   above `1` (`ex_7_4_not_enter`). What is true: `X = [0, max(K₀, x_m)]` works for every `K₀ ≥ 0`
   (`ex_7_4_large`), and every feasible path satisfies `limsup K_t ≤ x_m`
   (`ex_7_4_eventually`).

### Exercise 7.5

58. **The Euler approach in the setting of §7.5.** We prove the policy optimal by the sufficiency
   argument of Theorem 7.5.2 (`eu_EulerModel.eu_euler_sufficient`), with concavity of
   `ln(zK^α − K′)` on the graph of `Γ` (`ex7_lg_concave`); Theorem 7.5.2 itself does not apply
   verbatim, since off the graph the reward is undefined (as for Example 7.5.1). The shock is any
   positive adapted process: the Euler equation holds because `E_t[u_x(t + 1)]` is the
   `ℱ_t`-measurable `α/((1 − αβ)K_{t+1})` (`ex7_lg_euler`), so the Markov kernel `Q` plays no role
   in the policy. Integrability of `1/K_{t+1}` and of the competing plan's terms (`EulerInt`) is
   assumed (`ex_7_5`).
59. **The value function needs summability of the expected log shocks.** With `e_t = E ln z_t`
   (for a Markov `z` from `z₀`, `e_t = ∫ ln z Q^t(z₀, dz)`), the value is
   `(α/(1 − αβ)) ln K₀ + (ln(1 − αβ) + (αβ/(1 − αβ)) ln(αβ))/(1 − β) + (1/(1 − αβ)) Σ βᵗ e_t`
   under the hypotheses `ln z_t` integrable and `Σ βᵗ|e_t| < ∞` (`ex_7_5_value`, `ex7_lgV`);
   `sup_t |e_t| < ∞` suffices (`ex7_lg_bounded`). The identification of `e_t` with the `t`-step
   kernel is not formalised.
60. **Relation to Exercise 6.2.** The finite-horizon policy coefficient converges, `θ_n → αβ`
   (`ex_7_5_limit`).

### Exercise 7.6 and Exercise 7.10

61. **(7.4) holds for all plans only when `γ < 1`.** For `0 < γ < 1`, Assumption 5.1.4 holds
   (`ex7_ph_assumption514`) and `0 ≤ βⁿ E V(x_n) ≤ (A^{−γ}/(1 − γ)) x₀^{1−γ}(βm)ⁿ` along every
   feasible plan (`ex7_ph_tvc_all`), so Theorem 7.1.2 applies verbatim (`ex_7_6`). For `γ > 1`,
   (7.4) fails along the plan saving a small fraction `δ` with `βmδ^{1−γ} > 1`
   (`ex_7_10_tvc_fails`, `ex7_exists_bad_delta`, `ex_7_10_all_plans`); Theorem 7.1.2 does not
   apply and the dominance version, Corollary 7.1.1, is needed: plans outside `Π̂` have
   `J = −∞` (`ex7_ph_J_bot`), giving `ex_7_6_gt`.
62. **Assumption 5.1.4 for `γ > 1`.** Corollary 7.1.1 is stated under Assumption 5.1.4 (all
   feasible plans have integrable rewards). For `γ > 1` the reward is unbounded below and this
   restricts the return distribution `ν` (it holds, e.g., for deterministic returns); `ex_7_6_gt`
   takes it as a hypothesis. The log case `γ = 1` is verified by the Euler approach
   (`example_7_5_1`); its Bellman equation is `ex_7_6_bellman_log`.
63. **Moments.** `m = E[R^{1−γ}]` is assumed finite and `0 < βm < 1` (the book's condition for
   `A ∈ (0, 1)`); for `γ = 1`, `E ln R` is assumed finite. The model is posed on the positive
   reals with saving `s ∈ (0, x)` (positive consumption).
64. **(7.4) versus (7.35).** Along the optimal plan, `γ ≠ 1`, the envelope condition
    `V′(x) = u′(Ax)` and homogeneity `V(x) = xV′(x)/(1 − γ)` (`ex_7_10_envelope`) give
    `u_a · y_{t+1} = −(1 − γ)(1 − A)V(x_t)` pathwise (`ex_7_10_pathwise`), so (7.35) and (7.4) are
    equivalent (`ex_7_10`), with no integrability hypotheses. For `γ = 1` they are not
    proportional: the (7.35) term is the constant `−βᵀβ/(1 − β)`, while (7.4) holds when
    `E ln R` is a finite constant (`ex_7_10_log`).

### Exercise 7.7

65. **The limit exists for `R > 1`.** `α_n → γ(1 − 1/R)`, the marginal propensity to consume
    tends to `1 − 1/R`, and `A_n` converges (via the affine recursion of `ln A_n`,
    `ex7_affine_tendsto`, and dominated convergence for `M_n`), so the saving policy converges
    pointwise (`ex_7_7_limit`); the limit value solves the Bellman equation (`ex_7_7_bellman`).
    `R > 1` is needed (for `R ≤ 1`, `α_n → 0`).
66. **The limit policy is not optimal as claimed (no borrowing constraint).** Over all feasible
    plans the value is `V ≡ 0`: consuming `c` forever and rolling the debt over is feasible with
    `J = −e^{−γc}/(1 − β) → 0` (`ex7_ca_ponzi_J`), while the limit policy gives
    `V̄(x) = −Āe^{−ᾱx} < 0`; so it is not an optimal plan and the supremum is not attained
    (`ex_7_7_ponzi`). Condition (b) of Corollary 7.1.1 fails. What is true (`ex_7_7`): the limit
    policy plan satisfies (7.4) (`βⁿ E V̄(x_n) = V̄(x₀)R^{−n}`), attains `V̄(x₀)`, and is optimal
    among the feasible plans that satisfy (7.4) — a no-Ponzi condition — and have integrable
    rewards.
67. **Verification without Assumption 5.1.4.** In this model Assumption 5.1.4 need not hold (a
    measurable plan can make `e^{−γc_t}` non-integrable), so we use the proof of Theorem 7.1.2
    plan by plan (`ex7_verif_le_plan`, `ex7_verif_eq_plan`, built on `ih_partialSum_telescope`);
    with `u ≤ 0` the partial sums of every plan converge (`ex7_J_spec_nonpos`). The claim
    `V̄ = V̂` is not made: `J` of a plan in `Π̂` with non-integrable rewards is not controlled by
    the argument (its expected rewards are not defined).

### Exercise 7.8

68. **The closed form needs `y = 0`.** The Phelps model of Exercise 6.7 has constant labour
    income `y` and no borrowing; with `y > 0` the policy is not linear and has no closed form
    (not formalised). With `y = 0` (the model of Example 7.5.1, `γ ≠ 1` as printed), the
    finite-horizon value is `v_n = b_n^γ u`, `b_n = Σ_{k ≤ n} ρᵏ`, `ρ = (βm)^{1/γ}`, and
    `c_{n+1}(x) = x/b_{n+1}` (`ex_7_8_finite`); as `n → ∞`, `1/b_n → A = 1 − ρ` and
    `b_n^γ → A^{−γ}` when `βm < 1` (`ex_7_8_limit`), the policy and value of Example 7.5.1, optimal
    by `ex_7_6`, `ex_7_6_gt` and `example_7_5_1`.

### Exercise 7.9

69. **Not formalised.** Chapter 6 (Exercise 6.10) gives the LMZ policy explicitly only with one
    period to go (`ex_6_10_one`); for longer horizons the continuation value is not exponential
    and there is no closed form, so "the limiting policy and value functions" cannot be derived by
    taking limits of explicit formulas; the convergence argument of LMZ (1980) is outside the
    scope.
