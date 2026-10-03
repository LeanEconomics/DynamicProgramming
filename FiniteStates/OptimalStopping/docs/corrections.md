# Corrections to the source

Places where a claim in Chapter 4 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In
each case the Lean statement proves the stated version and cites the
original. Entries are recorded when found and revised if formalisation shows
the finding itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| (4.4), p. 107 | `v_σ = (I − L_σ)⁻¹ r_σ` "by Exercise 4.1.1 and the Neumann series lemma". | Proved without the spectral radius: `I − L_σ` is invertible because `u = L_σ u` forces `‖u‖ ≤ β‖u‖`, and the Neumann series `∑ L_σᵗ r_σ` is summed directly in the supremum norm (`StoppingProblem.isUnit_one_sub_L`, `StoppingProblem.vσ_eq_tsum`). Exercise 4.1.1 is proved separately. |
| Prop 4.1.3, p. 110 | "We shall prove this principle in a more general setting in Chapter 5." | Proved here directly (`StoppingProblem.isOptimal_iff_isGreedy`): a `v*`-greedy `σ` has `T_σ v* = Tv* = v*`, so `v_σ = v*`; conversely `v_σ = v*` forces `σ(x)` to attain the maximum in the Bellman equation at every `x`. |
| Ex 4.1.13, p. 119 | Densities `φ_a, φ_b` on `ℝ₊` with `φ_a ≼_F φ_b` give `σ*_a ≥ σ*_b`. | Proved with scrap values on a finite set `W ⊂ ℝ₊` carrying distributions `φ_a, φ_b` (`scrapFirm_sigmaStar_ge`), which is the discretisation the section itself recommends; dominance is the finite-set `FOSD` of Vol. 1 (2.9). The density statement needs integration against densities and is not claimed. The conclusion is stated for every `(w, z)`, not only "on `Z`". |
| §4.2.1, p. 122 | "the size of the exercise region expands with `t`", read off Figure 4.3. | Proved as a theorem (`AmericanOption.exercise_region_expands`): `v*` is nonnegative and nonincreasing in the date, hence so is `h*(t, z)`, and exercise at `(t, w, z)` implies exercise at `(m(t), w, z)` while the option is alive at `m(t)`. |
| §4.1.1, p. 107 | Lifetime rewards `E ∑ βᵗRₜ` define `v_σ`, which "Section 4.1.1.2 shows is well defined". | `v_σ` is defined as the unique fixed point of `T_σ`, i.e. by (4.2), as the book does in effect; the expected-sum formula is Chapter 5's (and Volume 2's) concern. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| p. 106 | `β ∈ (0, 1)`, `P` Markov. | Fields `β_pos`, `β_lt_one`, `P_markov` of `StoppingProblem`. |
| Ex 4.1.1, p. 107 | `X` nonempty. | The bound `ρ(A) ≤ ‖A‖` is Mathlib's `spectralRadius_le_nnnorm`, which needs `‖I‖ = 1`, i.e. a nonempty state space; `[Nonempty X]` in `StoppingProblem.specRad_L_lt_one`. No other result needs it. |
| (4.6), p. 108 | `max_σ v_σ(x)` exists: `Σ` is finite and nonempty. | `Policy X = X → Bool` is a `Fintype` when `X` has decidable equality; `vstar` is a `Finset.sup'` over it, so `[DecidableEq X]` appears on everything downstream of `v*`. |
| (4.9), p. 110 | `σ(x) ∈ argmax`: ties may be broken either way. | `IsGreedy` requires `σ(x) = 1 ⇒ e(x) ≥ c(x) + β(Pv)(x)` and `σ(x) = 0 ⇒ e(x) ≤ c(x) + β(Pv)(x)`; `greedy v` and `σ*` stop on ties, as the book's `1{e ≥ h*}` does. |
| Ex 4.1.9–4.1.11, p. 115 | `X ⊂ ℝ` with the usual order; "the optimal policy `σ*`". | Proved for any partially ordered `X` and for the tie-stopping policy `σ* = 1{e ≥ h*}`; policies are ordered pointwise with `false < true`. With arbitrary tie-breaking across states a greedy policy need not be monotone. |
| p. 116 | The threshold `x*` is the smallest `x` with `σ*(x) = 1`. | `exists_threshold_of_monotone` needs some `x` with `σ(x) = 1`, which the book takes for granted; a totally ordered finite `X`. |
| §4.1.2, p. 111 | `r > 0`, `s > 0`, `Z ⊂ ℝ`. | `0 < r` is a hypothesis; `s` may be any real (positivity is not needed for the results proved); `Z` is any finite type, with `[PartialOrder Z]` for Examples 4.1.3–4.1.4. |
| Ex 4.1.7, p. 114 | `Q ≫ 0`; `s > w(z)` for at least one `z`. | `∀ z z', 0 < Q z z'` and `∃ z₀, w z₀ < s`. |
| Ex 4.1.8, p. 114 | `w > 0`, `p ≥ 0`, `ℓ ≥ 0`. | `0 < w`, `0 ≤ p` in `isGreatest_profit`; the maximiser is `ℓ = (p/(2w))²`. |
| §4.1.4.2, p. 118 | `(Wₜ)` and `(Zₜ)` independent. | Encoded by the product kernel `P((w, z), (w', z')) = φ(w')Q(z, z')`. |
| §4.2.1, p. 120 | Dates `t ∈ {1, …, T + 1}`; the state `(t, w, z)`. | Dates are `Fin (T + 1)`, zero-based (`t` stands for `t + 1`); the option is alive when `t.val < T`. The state is ordered `(w, (t, z))`, IID component first, so that the product reduction of §4.1.4.2 applies verbatim with `Z` replaced by `T × Z`. |
| §4.2.1, p. 121 | `W` nonempty (so that `φ` is a distribution). | Derived from `∑ φ = 1` where needed (`AmericanOption.hstar_antitone`). |
| §4.2.2.1, p. 125 | `c ∈ ℝ₊`. | Any real `c₀`; nonnegativity is not used. |
| §4.2.2.2, p. 125 | Costs `Cₜ ∼ φ ∈ D(W)`. | Costs are indexed by a finite type `Wc` with `cost : Wc → ℝ` and distribution `φ`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| §4.1.1.7, p. 111 | Theorem 8.1.1: finitely many VFI steps produce an optimal policy | Chapter 8's result; VFI convergence itself is proved. |
| Ex 4.1.6, p. 112 | Replicate Figure 4.1 | Computational. |
| §4.1.2, Figures 4.1–4.2, Listing 4.1 | Plots and code | Computational. |
| Remark 4.1.1, p. 116 | The monotonicity conditions are sufficient but not necessary (Figure 3.5) | An observation about a figure; no theorem. |
| Ex 4.1.12, p. 119 | Continuation value operator with a density `φ` on `ℝ₊` | Formalised for a finite scrap distribution (`scrapFirm_reducedC`); the integral version needs measure theory and is not claimed. |
| §4.2.1, Figures 4.3–4.4, Listing 4.2 | Exercise regions and simulations | Computational; the qualitative claim about the exercise region is proved. |
| Remark 4.2.1, p. 126 | The expected value function method in general (§5.3) | Chapter 5. |
| §4.3 Chapter notes | Literature | Not applicable. |
