# Corrections and departures: Miao Chapter 17

Jianjun Miao, *Economic Dynamics in Discrete Time* (draft of 21 April 2013), Chapter 17, Incomplete
Markets Models, pp. 559–586. Lean names are relative to `Miao.IncompleteMarkets`. Every book item is
located in the [source map](source-map.md).

## Introduction and §17.1

1. **(17.3b), p. 560: `φ` at `r = 0`.** The book defines `φ` for `r > 0` and `r < 0` only.
   `ay_phi` uses `φ = b` for `r = 0` too (`eq_17_3b`).
2. **Natural borrowing constraint, p. 560.** "By Theorem 8.3.1, the no-Ponzi-scheme condition
   and nonnegative consumption imply `a_t ≥ −wl_min/r`" needs a support hypothesis (the shock
   can stay near `l_min` after any event of positive probability), as in the corrected
   converse of Theorem 8.3.1 in the Chapter 8 project; `ay_natural_limit` carries it.
3. **(17.4), p. 561.** The equivalence of the cash-on-hand and asset formulations needs
   `1 + r ≥ 0` (so that `a ≥ −φ` gives `x ≥ wl − rφ`) (`eq_17_4`). When `φ = wl_min/r`
   exactly, `x_min = 0`; the copied §8.3.2 model needs `x_min > 0` (`b < y_min/r`).
4. **"If `β(1 + r) ≥ 1`, `x_t` and `a_t` converge to infinity", p. 561, and "the equilibrium
   interest rate is less than `ρ`", p. 564.** The almost-sure divergence is not formalised in
   the Chapter 8 project; the consequence used in §17.1.3 is proved by a different argument:
   if income is not almost surely constant, every stationary distribution of the cash-on-hand
   process has `β(1 + r) < 1`, i.e. `r < ρ` (`ay_beta_R_lt_one`, `ay_r_lt_rho`). Proof:
   integrating the Euler inequality against `λ*` gives `β(1 + r) ≤ 1`; at `β(1 + r) = 1`,
   `m = u′∘c` is harmonic and `∫∫ (m(x′) − m(x))² = 0`, which forces constant income.
5. **Definition 17.1.1, p. 563.** (i) is read as the Bellman equation (17.4) with the maximum
   attained at `g` (`ay_Bellman`); (ii) as profit maximisation over `K, L ≥ 0`, from which
   (17.5)–(17.6) follow at the interior optimum when `F` is differentiable
   (`definition_17_1_1`); `λ*` is required to live on the state space `a ≥ −φ`,
   `l ∈ [l_min, l_max]`. (17.7) on rectangles is equivalent to `λ* = λ*P` (`eq_17_7`).
6. **"The resource constraint is redundant", p. 563.** True for CRS technologies (Euler's
   theorem gives zero profits) when `a`, `l` and `g` are `λ*`-integrable
   (`ay_resource_redundant`).
7. **Continuity and limits of `Ea(r)`, p. 564.** "We can show" that `g`, `λ*` and `Ea` are
   continuous in `r`, that `Ea → ∞` as `(1 + r)β ↑ 1`, and that `Ea(r)` "approaches `−b`" for
   `r < 0`: none is proved in the book (the Chapter 8 project leaves the continuity of the
   stationary distribution unformalised). They are hypotheses of the crossing theorems
   `ay_existence`, `ay_existence_cd` (the last read as: `Ea` bounded above near `−δ`), which are
   shown non-vacuous by `ay_existence_example`.
8. **Footnote 2, p. 568: the saving rate.** "`δK/(AF(K, L)) = δα/(r + δ)` for
   `F(K, L) = AK^αL^{1−α}`" double counts `A`: the correct identity is
   `δK/F(K, L) = δα/(r + δ)` (`ay_saving_rate`); the printed ratio equals `δα/((r + δ)A)`,
   different unless `A = 1` (`ay_saving_rate_misprint`).
9. **Gini coefficient, p. 568: "for complete concentration ... the Gini coefficient is 1".**
   With the book's Lorenz curve through `(i/n, z_i)`, complete concentration in a sample of `n`
   gives `G = 1 − 1/n` (`ay_gini_concentrated`), never `1` (`ay_gini_concentrated_ne_one`);
   `G → 1` as `n → ∞` (`ay_gini_concentrated_tendsto`). In general `0 ≤ G ≤ 1 − 1/n`
   (`ay_gini_nonneg`, `ay_gini_le`); "between zero and one" also needs a positive total.
10. **Exercise 17.4.** The book asks only for the definition; the first-order condition
    (`ex_17_4_foc`) and a concrete equilibrium (`ex_17_4`) are added. The borrowing limit is
    that of (17.3b).

## §§17.2–17.3

### §17.2 Endowment economies

11. **`Ea(r)` is a set.** The book writes `Ea(r)` as a function, which presumes a unique
   solution of (17.4) and a unique stationary distribution. `BWEconomy.EaSet` collects all
   values `∫ g dλ`; Proposition 17.2.1 is the set identity `Ea(0; b) = Ea(0; 0) − b`
   (`proposition_17_2_1`), with the policy-level statement `proposition_17_2_1_policy`.
12. **Proof of Proposition 17.2.1, p. 571**, ends "Hence `Ea(0; b) = Ea(0; b) − b`", a typo for
   `Ea(0; 0) − b`, which is what is proved. The change of variables is proved for every `r`
   (`bw_EaSet_shift_eq`): with `r ≠ 0` it also shifts the endowment by `−rφ`, which is why the
   proposition needs `r = 0`.
13. **Proposition 17.2.3, first part, p. 576.** "The highest interest rate that can be supported
   … equals that associated with the Huggett model with the natural borrowing limit" relies on
   the `Ea(r)` curve shifting left as the limit rises (Figure 17.3), a numerical finding that does
   not follow from the model in general. Proved instead: the supportable rates are exactly the
   Huggett equilibrium rates for limits `φ > 0` (`proposition_17_2_3_rates`), every such `φ`
   satisfies `r̃φ ≤ e(s)` for all `s`, i.e. is at most the natural limit `e_min/r̃`
   (`bw_bewley_real_balances_le`, `bw_huggett_limit_le_natural`).
14. **Proposition 17.2.3, second part (rate below `1/β − 1`).** The book infers it from the
   divergence of `x_t` when `β(1 + r) ≥ 1` (§8.3, almost-sure path statements). Proved, in the
   iid cash-on-hand setting of §17.1.1/§8.3.2, by a different argument: if income is not
   almost surely constant and cash on hand has a stationary distribution, then `βR < 1`
   (`proposition_17_2_3_lt`; the Euler inequality integrated against `λ`, plus the `L²`
   stationary-martingale argument for `βR = 1`). Non-degenerate income is needed: with constant
   income and `βR = 1`, `x′ = x` is stationary.
15. **Integrability** of `V(a′, ·)` under `Q(·, s)` and of `g` under `λ` is part of the Bellman
   equation and of the equilibrium definitions; the book leaves it implicit.
16. **Bewley equilibrium.** The money stock `M > 0` and the price level `p > 0` are required
   (`BWBewleyEqm`); real balances `φ = M/p` are then positive, and the back-solving method needs
   `φ > 0` (Step 1's `0 ≤ φ`: `φ = 0` gives no price level).
17. **Implicit interest, p. 576**, opens "there is explicit interest on currency"; the setting is
   *no* explicit interest (`r̃ = 0` in (17.9)), as the rest of the paragraph says
   (`bw_implicit_tax` uses (17.9) with `r̃ = 0`).
18. **Seigniorage comparative statics, p. 578,** is stated for the highest-return selection; it is
   proved in the form "every equilibrium for `G₂` lies strictly below an equilibrium for any
   `0 < G₁ < G₂`" under continuity of `Ea` on `[r₂, 0]` (`bw_seign_comparative_statics`).

### §17.3 Aggregate shocks

19. **Definition 17.3.1 (iv), p. 580, as printed is wrong.**
   `G(λ, z; z′)(A × B) = ∫ 1_A(g) Q(z′, B; z, l) dλ` gives `G(λ, z; z′)` total mass `π(z′|z)`
   (`bw_book_law_mass`), so it is not a probability measure whenever `π(z′|z) < 1`
   (`bw_book_law_not_prob`). The correct law of motion is the conditional distribution,
   `π(z′|z) G(λ, z; z′)(A × B) = ∫ 1_A(g) Q(z′, B; z, l) dλ` (`BWAggEconomy.Law`), which needs the
   aggregate shock's transition `π(z′|z) = Q({z′} × L; z, l)` not to depend on `l`
   (`BWAggEconomy.marg`); then `G(λ, z; z′)` is a probability measure (`bw_law_isProb`).
20. **"If the shocks are independent, `G` does not depend on `z′`" (p. 580)** is true for the
    corrected law (`bw_law_indep`); for the printed law it fails (the factor `π(z′|z)`). The
    capital component of the law of motion never depends on `z′` (`bw_next_capital_indep`).
21. **Definition 17.3.1 (i)** writes `V(k, l; λ, z)`; the individual state is `a`.
22. **Moments, p. 581.** `bw_moments` are raw moments `∫ aⁱ dλ`; the book's "mean, variance,
    skewness, kurtosis" carry the same information.
23. **Existence of a recursive equilibrium** is open in the book; Definition 17.3.1 and
    Exercise 17.5 are shown non-vacuous by explicit (degenerate: linear technology, linear
    utility, `β(1 + r) = 1`) instances (`bw_recEqm_example`, `ex_17_5`).

### Instances

24. **Non-vacuity witnesses** use simple economies: the two-state deterministic-cycle economy
    with `u(c) = min(c, 3/2)` (`bw_cycle`; Definition 17.2.1, fiat money, Bewley equilibrium with
    `r̃ = 0`), and for Exercise 17.6 the CRRA (`γ = 1/2`) economy at the Friedman rule
    `1 + g = β` with absorbing employment states (`ex_17_6_b`).
