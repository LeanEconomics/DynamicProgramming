# Corrections to the source

Places where a claim in Chapter 3 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In
each case the Lean statement proves the stated version and cites the
original. Entries are recorded when found and revised if formalisation shows
the finding itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 3.1.3, p. 85 | The S–s inventory chain is irreducible. The book's solution handles `x > s` by the path `x → s → S + s → x'` and leaves `x ≤ s` to the reader. | For `x ≤ s` the chain is proved to reach `S` in one step (demand exactly `x`), then `s`, then `S + s`. This needs `s < S`, which holds in the book's calibration (`S = 100`, `s = 10`) and is a field of `Inventory`. Without `s < S` the chain is still irreducible but the route is longer; that case is not formalised. |
| Ex 3.1.7, p. 89 | "Prove this using the Perron–Frobenius theorem." | Proved instead by Dobrushin's ℓ¹ contraction estimate (`l1_vecMul_le`): no spectral theory is needed, and the proof gives the geometric rate `(1 − nε)ᵗ` where `ε` is the smallest entry. The statement proved is the book's. |
| Ex 3.2.3, p. 93 | `α, β ∈ [0, 1]`. | The equivalence "monotone increasing iff `α + β ≤ 1`" holds for all real `α, β`, so the bounds are dropped (`monotoneIncreasing_two_state_iff`). |
| Lemma 3.2.1, p. 94 | Proved by the Neumann series lemma applied to `βP`, using `ρ(βP) = β`. | Proved directly: the series `∑ (βP)ᵗh` converges in the supremum norm since `‖(βP)ᵗh‖ ≤ βᵗ‖h‖`, telescoping gives `(I − βP)v = h`, and `I − βP` is invertible because `u = βPu` forces `u = 0` (`IsMarkov.lifetimeValue_eq_inv`). The spectral radius is not used. |
| Ex 3.2.8, p. 96 | Prove for the CRRA model when `ρ ≥ 0`. | Needs `γ ≠ 1`, since `c^{1−γ}/(1 − γ)` is undefined at `γ = 1` (the book's `γ = 2`); proved for all `γ ≠ 1` (`monotone_crra_exp`, `Tauchen.monotone_crra_value`). |
| §3.3.2, p. 102 | "when `0 < α, β < 1`, the system (3.25)–(3.26) has a unique solution in `V × V`". | Only `α ≥ 0` is used: the denominator `1 − β(1 − α)` is positive and the stopping branch's modulus `αβ/(1 − β(1 − α))` is below one for every `α ≥ 0` because `β < 1`. Proved for `0 ≤ α` (`MarkovJobSearch.system_unique`), which includes the permanent-job case `α = 0` of §3.3.1. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (3.1), p. 82 | A `P`-Markov chain `(Xₜ)` is a sequence of random variables on a probability space. | Not formalised as such. Everything the chapter proves about chains is a statement about `P`, its powers and the row vectors `ψPᵗ`, and is stated in that form: (3.2) as the path-sum formula `pow_apply_eq_sum_paths`, (3.3)–(3.6) as identities in `ψ ↦ ψP`, (3.12)–(3.15) as identities in `h ↦ Ph`. |
| Ex 3.1.1, p. 83 | `h(x, d) = max{x − d, 0} + S·1{x ≤ s}` on `ℤ₊`. | `ℕ` subtraction is the truncation `max{x − d, 0}` (`Inventory.h`). |
| p. 83 | `P(x, x') = ∑_{d ≥ 0} 1{h(x, d) = x'}φ(d)` is an infinite sum. | A `tsum` over `ℕ`, summable because the geometric `φ` is (`Inventory.summable_term`); rows sum to one via `∑' φ = 1`. |
| Ex 3.1.7, p. 89 | `X` nonempty, so that `D(X)` is nonempty. | `[Nonempty X]` in `globallyStable_of_pos` and `globallyStable_distMap`. |
| p. 88 | The day labourer's `α, β ∈ (0, 1)`. | Fields of `DayLaborer`; `|1 − α − β| < 1` follows. |
| §3.1.3, p. 90 | `n ≥ 2` grid points, `s = (xₙ − x₁)/(n − 1) > 0`; `F` is the CDF of `N(0, ν²)`. | `Tauchen` takes `2 ≤ n`, `x₁`, `s > 0` and an abstract `F` that is increasing with values in `[0, 1]`; the Gaussian CDF is one instance. The grid is `xⱼ = x₁ + j·s` with zero-based `j`. The shift by `μₓ` for `b ≠ 0` is a relabelling of the grid and is not formalised. |
| Ex 3.2.2, p. 93 | Tauchen's matrix is monotone increasing "if `ρ ≥ 0`". | `0 ≤ ρ` and the Tauchen hypotheses above (`Tauchen.monotoneIncreasing_P`). |
| §3.2.1.3, p. 93 | `X` partially ordered. | `[PartialOrder X]` on `FOSD`, `MonotoneIncreasing` and Exercises 3.2.4–3.2.6; the state space carries both the `Fintype` and the order. |
| Ex 3.2.1 (ii), p. 92 | `max` over `X`, so `X` nonempty. | `(univ : Finset X).Nonempty` in `IsMarkov.sup'_abs_mulVec_le`; the norm form `IsMarkov.norm_mulVec_le` needs nothing. |
| Lemma 3.2.1, p. 94 | `β ∈ ℝ₊` and `β < 1`. | `0 ≤ β` and `β < 1`. |
| §3.2.2.2, p. 95 | Interest rate `r > 0`. | `0 < r` in `IsMarkov.firm_value`. |
| §3.2.2.3, p. 96 | `u : ℝ₊ → ℝ`, `c ∈ ℝ^X₊`. | `crra γ c = c^{1−γ}/(1 − γ)` uses the real power, defined for all `c`; Exercise 3.2.8 takes `c(x) = eˣ > 0`. |
| §3.3.1, p. 97 | `W ⊂ ℝ₊` finite, `P ∈ M(ℝ^W)`, `c > 0`, `β ∈ (0, 1)`. | Fields of `MarkovJobSearch`; offers are indexed by a `Fintype W` with `wage : W → ℝ`, `wage ≥ 0`, so repeated wage values are allowed. |
| Lemma 3.3.1, p. 98 | `W` ordered by `≤` on wages. | `[PartialOrder W]` with `Monotone wage` and `MonotoneIncreasing P` (`MarkovJobSearch.monotone_vstar`); the book's `(W, ≤)` with `W ⊂ ℝ` is the case where the order is the wage order. |
| p. 98 | A `v`-greedy policy satisfies `σ(w) = 1{w/(1 − β) ≥ c + β ∑ v(w')P(w, w')}`. | `IsGreedy` is the biconditional `σ w = true ↔ c + β(Pv)(w) ≤ w/(1 − β)`; ties accept, as in the book's `≥`. |
| §3.3.2, p. 101 | `V = ℝ^W₊` for both value functions; `v_e*` is also nonnegative. | `MarkovJobSearch.veStar_mem`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Thm 3.1.2, (3.7), p. 87 | Ergodicity: the fraction of time spent in `x` converges to `ψ*(x)` almost surely. | Cited by the book from Brémaud (2020) without proof; a statement about almost every sample path, which needs the probability space of the chain and the strong law for Markov chains. Not in Mathlib; not claimed. |
| p. 87 | Every irreducible `P` has exactly one stationary distribution (Ex 2.3.2 (iv)). | Rests on the irreducible Perron–Frobenius theorem, deferred to the Chapter 6 project; the everywhere-positive case is proved here (`globallyStable_of_pos`). |
| Ex 3.1.5, 3.1.8, 3.1.9, p. 88 | Explain Listing 3.3; compute `ψPᵗ`; simulate the chain | Computational or descriptive. |
| Ex 3.1.10, p. 90 | `N(μₓ, σₓ²)` is stationary for the Gaussian AR(1); independence matters | Needs the Gaussian measure on `ℝ` and convolution of normals; the chapter's finite-state results do not use it. |
| Ex 3.1.11, (3.11), p. 90 | `P{t − δ < Xₜ₊₁ ≤ t + δ | Xₜ = x} = F(t − ρx + δ) − F(t − ρx − δ)` | A statement about the continuous process; Tauchen's rule (iii) is formalised as a definition and its consequences proved. |
| Figures 3.1–3.7, Listings 3.1–3.5, Ex 3.2.7, Ex 3.3.6 | Plots, code and replications | Computational. |
| Ex 3.3.2, p. 100 | Explain why `h*` is increasing in Figure 3.5 | Discussion; the mathematical content is Lemma 3.3.1 together with monotonicity of `P`, both formalised. |
| §3.3.1, p. 98 | "A full proof [that `v*` solves (3.23)] is given in Chapter 4" | `v*` is defined here as the unique fixed point of `T` in `V`; optimality for the sequence problem is Chapter 4's. |
| §3.3.1.2, p. 101 | Efficiency comparison of iterating with `T` and with `Q` | Descriptive. |
| §3.4 Chapter notes | Literature | Not applicable. |
