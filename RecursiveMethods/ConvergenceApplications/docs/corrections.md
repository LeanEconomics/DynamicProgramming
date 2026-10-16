# Corrections and conventions

Places where a Lean statement differs from the book: a claim corrected, a gap in a proof closed,
a hypothesis made explicit, or a convention chosen. Every false claim below has a Lean
counterexample.

## Claims corrected

| Where | Book | Lean |
| --- | --- | --- |
| Exercise 13.1a, p. 390 | "Under suitable restrictions" a finite optimal order size exists. | `c₁ > 0` is the restriction: then a minimiser of `(c₀ + c₁S)/(1 − γˢ)` exists and is the optimal `S` (`ex_13_1a`). With `c₁ = 0 < c₀` the cost is strictly decreasing and no finite `S` is optimal (`ex_13_1a_c1_zero`). |
| Exercise 13.1a (manual) | Stopping rule `K(1 − γ)γ^{S+1} ≤ c₁`. | The exponent is `S`. With `θ = 1/2`, `β = 2/3`, `c₀ = 10`, `c₁ = 1` the manual's rule picks `S = 2`, which is not optimal (`ex_13_1a_manual_counterexample`). |
| Exercise 13.1b–c, p. 390 | Unique invariant distribution, convergence from every initial distribution. | Needs `0 < θ < 1`. At `θ = 1`, `S ≥ 2`, the chain is a deterministic cycle and `T*ⁿδ₀` does not converge (`ex_13_1b_theta_one`). Condition M fails on all of `ℕ` (`ex_13_1c_not_conditionM_nat`), and convergence is not uniform in `λ₀` (`ex_13_1c_nat_not_uniform`); it holds from every `λ₀` (`ex_13_1c_nat_convergence`). |
| Exercise 13.1c (manual) | `p̄ᵢ = 1/S` on `0, …, S`. | Its mass is `(S + 1)/S` (`ex_13_1c_manual_mass`) and it is not invariant for `S ≥ 2` (`ex_13_1c_manual_not_invariant`). The invariant distribution is `π₀ = θ/S`, `πₓ = 1/S` for `1 ≤ x ≤ S − 1`, `π_S = (1 − θ)/S` (`ex_13_1c_weights`). |
| Exercise 13.2a, p. 391 | Does `P` have the Feller property? | No: `μ = δ₀`, `s = 1`, `S = 2` (`ex_13_2a_not_feller`). |
| Exercise 13.2b, p. 391 | `Pᴺ(x, {0}) ≥ ε` on `[0, S]` for some `N`, `ε`. | False without a condition on `μ`: with `μ = δ₁`, `s = 1/2`, `S = 2`, `z̄ = 3` the chain alternates `0 ↔ 1`, no `N` works, and `T*ⁿδ₀` does not converge (`ex_13_2b_counterexample`, `ex_13_2b_not_convergent`). It also fails whenever `z̄ ≤ s` (`ex_13_2b_fails_of_zbar_le_s`). With `μ([S, ∞)) > 0` it holds with `N = 1`, and Theorem 11.12 applies on `[0, S]` (`ex_13_2b`, `ex_13_2b_invariant`). |
| p. 391 | `(S, ∞)` is transient. | Needs `μ((0, z̄]) > 0`: with `μ = δ₀` every `x > s` is absorbing (`ex_13_2_not_transient`). With `μ((0, ∞)) > 0` every invariant measure is null on `(S, ∞)` (`ex_13_2_invariant_null_above`). |
| p. 392 | `x̄` is "the unique value" with `x̄ = z̄f(x̄)`. | Unique if it exists (`xbar_unique`), but existence does not follow: `f(x) = 1 + 0.9x + 2(1 − e^{−x})`, `z̄ = 2`, `β = 1/2` meets the modified (T1)–(T5) and `βf′(0) > 1`, yet `2f(x) > x` for all `x ≥ 0` (`xbar_counterexample`). |
| Exercise 13.3b, p. 392 | `0 < g(x) < x` for `0 < x ≤ x̄`, `g` and `c` strictly increasing. | False under the book's own assumptions (no Inada condition is needed): `U = 1 − e^{−20c}`, `f = 5/6 + 2y/(1 + y)`, `β = 3/4`, `z̄ = 2`, `x̄ = 5` gives `g = 0` on `[0, 1/100]` (`ex_13_3b_counterexample`, `ex_13_3b_not_strictMono`). Proved: `g` continuous and nondecreasing, `c` nondecreasing (`ex_13_3b`), and strictly increasing where `c > 0` (`out_consumption_strictMono`). |
| p. 396 | Unique positive `x̲ = g(x̲, z̲)`, `x̄ = g(x̄, z̄)`. | Uniqueness holds; existence does not follow from Ex. 10.4(d,e): `g = x/2` (`industry_no_fixedPoint_half`), and a condition at the bottom alone is not enough, `g = x + 1/(1 + x)` (`industry_no_fixedPoint_above`). With conditions at both ends they exist (`industry_exists_xlo_xhi`). |
| Exercise 13.5d, p. 399 | `φ(z) > 0` for every `z`. | False: with `U = z(1 − e^{−c})` and `z̲ < βe^{−y} E z` (all §13.5 assumptions hold), `g(m, z̲) > y` for every `m > 0` (`ex_13_5d_counterexample`, `ex_13_5d_counterexample_uniform`). Corrected: `φ(z) ≥ 0`, `g = y` on `[0, φ(z)]` and strictly increasing beyond (`ex_13_5d_corrected`). |
| Exercise 13.5e, p. 400 | `c(·, z)` strictly increasing, so `g(m₂, z) − g(m₁, z) < m₂ − m₁`. | False in the same example: `g(m, z̲) = m + y` (nothing consumed) on `[0, m*]`, `m* > 0` (`ex_13_5e_counterexample`). The manual's first-order argument misses the corner `c = 0`. Corrected: `c(m₁) < c(m₂)` when `m₁ < m₂` and `c(m₂) > 0` (`ex_13_5e_corrected`); the weak slope bound always holds (`cashPolicy_mono`, `cashCons_mono`). |
| Exercise 13.5f (manual) | `U₁(y, z̲) < β∫v₁(y, ·)dμ`, "otherwise `g ≡ y`". | Can fail: with `β ≤ z̲`, `g(y, z̲) = y`, so `m̄ = y` and `λ* = δ_y` (`ex_13_5f_mbar_eq_y`). The book's (f) still holds with `m̄ ≥ y` (`ex_13_5f`). |
| Exercise 13.6b, p. 402 | The ergodic set is `{iy : i ≥ 1}`. | Needs `μ([0, ζ)) > 0` (true under the §13.5 density bound, `ex_13_6b_density`): with `μ = δ₁` the ergodic set is `{y}` (`ex_13_6b_counterexample`). |
| Exercise 13.7b, p. 403 | `T*ⁿΨ₀` does not converge weakly to an invariant measure. | False: `δ₀` is invariant and `T*ⁿΨ₀ ⇒ δ₀` for every `Ψ₀`, geometrically in total variation (`ex_13_7b`, `ex_13_7b_counterexample`). What fails is market clearing (1) in the limit: along an equilibrium every `Ψₙ` has mean `1`, while `δ₀` and every invariant measure have mean `0` (`ex_13_7b_corrected`). |
| Exercise 13.7b (manual) | `P` is not Feller. | `P` is Feller; only `w ↦ P(w, {0})` is discontinuous (`ex_13_7b_feller`). |
| Exercise 13.7c, p. 403 | `q` is characterised "in terms of `β` and `μ`". | `q` is proportional to `y` (`ex_13_7c_scaling`, `ex_13_7c_counterexample`); `β` and `μ` determine `q/y` (`ex_13_7c_unique`). |
| p. 405 | (F1) `f(x̄, z) = 0`; (F2) `f(x, ·)` strictly increasing on `[0, x̄]`. | Inconsistent at `x = x̄` (`ex_13_8_F1F2_inconsistent`); (F2) is imposed on `[0, x̄)`. |
| Exercise 13.8d hint, p. 410 | For every `θ ∈ (0, θ̄)` both (2a) and (2c) occur. | (2c) never occurs for `θ ≥ βθ̄` (`ex_13_8d_noCaseC`), and `[βθ̄, θ̄)` is never empty (`ex_13_8d_hint_counterexample`, a concrete instance in `ex_13_8d_hint_counterexample_concrete`). The conclusion of (d) still holds there (`ex_13_8d`, `ex_13_8d_delta`). "(6) implies (7) for large `θ`" does not need (6) (`ex_13_8d_seven`). |
| Exercise 13.8h, p. 412 | `D` is strictly decreasing for `θ > 0`. | `D = 0` on `[θ̄, ∞)` (`ex_13_8h_counterexample`, `ex_13_8h_counterexample_concrete`), and under (6) already on `[βθ̄, ∞)` (`ex_13_8h_zero`). `D` is nonincreasing (`ex_13_8h`). That `D` is strictly decreasing where `D > 0` is not proved; the cutoffs `g_A`, `g_C` are strictly decreasing in `θ` where positive (`searchCutoffs_theta_strict`). |
| p. 411 | `θ` with `D(θ) = N` exists. | Only for `N ∈ [0, x̄]` (`ex_13_8g_existence`). |

## Gaps in proofs closed

| Where | Book | Lean |
| --- | --- | --- |
| Exercise 13.1c, p. 390 | Uniqueness and convergence (the manual: Condition M on `{0, …, S}`). | Condition M is proved with `P^{S+1}(x, {S}) ≥ θˢ(1 − θ)^{S+1}` (`ex_13_1c_conditionM`), and Theorem 11.12 applies on `{0, …, S}` (`ex_13_1c`). |
| (3a)–(3b), p. 394 | `φₙ(x, ·)` strictly increasing for a constant shock. | The argument needs the `n`-step map monotone in each shock separately; proved with `g` only nondecreasing (`growth_kpow_Ioc`). |
| pp. 393–394 | `x*` "the unique value" with `βf′(g(x*))z* = 1`. | `f` is only weakly concave, so `x*` need not be unique; it exists by the intermediate value theorem (`growth_xstar_exists`), and every such `x*` works (`growth_xstar_between`). At a corner `g = 0` the Euler equation is an inequality, which points the right way. |
| Exercise 13.4b, p. 396 | Stated without proof. | Runs of high and low shocks, with probabilities bounded below through the Feller property and (2) (`ex_13_4b`). |
| Exercise 13.4c, p. 397 | Stated without proof. | Every point of `S` lies in an invariant rectangle containing `Ŝ`, and paths are squeezed into `Ŝ` (`ex_13_4c`). The degenerate case `x̲ = x̄` needs a separate argument, since Assumption 12.1 then fails on every larger rectangle (`ex_13_4c_degenerate_no_assumption`). |
| Exercise 13.8d (manual) | Equates `v(x, ·)` with `w(x, ·)`. | Valid only once `x` is in Case B at every `z`; proved via `searchNoCaseB`. |
| Exercise 13.8e (manual) | `g_C(z̲) < g_C(z̄)` without (6). | Fails (`g_C ≡ 0` for `θ ≥ θ̄`); uniqueness is proved by a decay and a burn-in argument (`searchLeave_unique`). |
| Exercise 13.5b, p. 398 | The hint treats the kink where cash in advance just binds. | The corner `m′ = m + y` (`c = 0`) also occurs. Differentiability on `(0, ∞)` is proved by propagating kinks, `J(x) ≤ βJ(x + y)` (`cash_jump_le`, `ex_13_5b_deriv`, `ex_13_5b_C1`). Strict concavity cannot come from Theorem 9.8 and is proved by a chord argument (`cash_strictConcave`). |
| Exercise 13.5i, p. 400 | Theorem 12.12's hypotheses hold. | Because (d) and (e) fail, the slope argument is unavailable. (i) is proved from weak monotonicity and two crossing conditions, `g(m, z̲) > m` on `[y, m̄)` and `g(m̄, z̄) < m̄` (`cash_down`, proved directly). This needs `z̲ < z̄` (`ex_13_5i`, `ex_13_5ij_economy`). |
## Hypotheses made explicit

| Where | Book | Lean |
| --- | --- | --- |
| §13.3 convergence | The Euler equation (2). | A hypothesis on the policy (`GrowthEuler`): equality where `g > 0`, inequality at corners, and `c > 0` for `x > 0`. It is not derived from first-order conditions. |
| §13.4 | The policy of §10.4 with the properties of Ex. 10.4(d,e). | An abstract policy with those properties (`IndustryPolicy`); Ex. 10.4e is not proved in the Chapter 10 project. |
| Exercise 13.6c, 13.7 | `μ ≠ δ₀`. | `∫ z dμ > 0`. Existence of the §13.7c root assumes `a ↦ μ([0, a))` continuous (`ex_13_7c_exists`). |

## Notes on the transcription

Some remarks in the working transcription were corrected by the formalisation and are recorded
here because they bear on the book's claims:

* §13.1c: the bound `Pˢ(x, {0}) ≥ θˢ` on `{0, …, S}` is false, because state `0` has no self-loop:
  `P²(1, {0}) = 3/16 < 9/16` for `S = 2`, `θ = 3/4` (`ex_13_1c_note_counterexample`).
* §13.4c: "`0 ≤ x_{t+1} − x̄` whenever `x_t > x̄`" is false: `g = (x + z)/2`, `Z = [1, 3]`, `x₀ = 4`,
  `z₀ = 1` gives `x₁ = 5/2 < x̄ = 3` (`ex_13_4c_remark_counterexample`). The correct statement is
  `x_{t+1} − x̄ < x_t − x̄` and `x_{t+1} > x̲` (`ex_13_4c_gap`).
* §13.7a: "a root `ζ ∈ (0, 1)` exists iff `βR < 1`" needs `μ` to charge every `(a, 1]`
  (`ex_13_7a_counterexample`); §13.7c: "`βR < 1` holds automatically" needs a condition on `μ`
  (`ex_13_7c_betaR_counterexample`). Both hold under the book's density bound.

## Conventions

* The copied modules keep their own names; three clashes were resolved by renaming in the
  Chapter 10 copies (`integrable_of_abs_le_bound`, `integral_lt_integral_of_forall_lt`,
  `crossVertex`).
* Theorem 12.12 is stated for order intervals of `ℝˡ`; `RealIntervals` transports it to real
  intervals and to rectangles in `ℝ × ℝ`.
* Exercise 13.4b asks for `> ε`; `≥ ε` is proved, which is equivalent.
