# Corrections to the source

Places where a claim in Chapter 1 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In
each case the Lean statement proves the stated version and cites the
original. Entries are recorded when found and revised if formalisation shows
the finding itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 1.2.18, p. 22 | The fixed point of a globally stable `T` lies in every closed invariant `C`. | False for `C = ∅`, which is closed and invariant. Proved with `C` nonempty (`GloballyStable.fixedPt_mem_of_isClosed`). |
| Lemma 1.2.2, p. 19 | `ρ(B)ᵏ ≤ ‖Bᵏ‖` and `‖Bᵏ‖^{1/k} → ρ(B)` for *any* matrix norm, quoted from Bollobás. | Proved for the ℓ∞ operator norm (`specRad_pow_le_norm_pow`, `tendsto_norm_pow_rpow`), from Mathlib's Gelfand formula. The statement for other norms follows from norm equivalence (Ex 1.2.6–1.2.7) and is not stated separately. |
| Ex 1.2.13, p. 19 | `∑ Aᵏ` converges "in the sense that every element of the partial sums converges". | Stated as convergence in the matrix norm (`summable_pow`), which is equivalent by Ex 1.2.8 (pointwise and norm convergence coincide in finite dimensions). |
| Ex 1.2.25, p. 27 | Hint: use the derivative `g'(k) → ∞` as `k → 0`. | Proved without derivatives: the chord from `k/2` to `k` has slope `2sA(1 − 2^{−α})k^{α−1} + 1 − δ`, which exceeds any modulus for small `k` (`Solow.not_isContractionOn_g`). |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Ex 1.2.18, p. 22 | The closed invariant set `C` must be nonempty: `∅` is closed and invariant and contains no fixed point. | `hCne : C.Nonempty` in `GloballyStable.fixedPt_mem_of_isClosed`. |
| Thm 1.2.3, p. 23 | `U` nonempty (stated on p. 22 for contractions, not repeated in the theorem); `λ ≥ 0` (stated on p. 31). | `hne : U.Nonempty`; `IsContractionOn.nonneg`. |
| Thm 1.2.3, p. 23 | "closed in `ℝⁿ` ... with respect to some norm": the statement is for `ℝⁿ`, the proof uses only completeness. | Stated for any complete normed group `E`; `ℝⁿ` under any norm is an instance. |
| (1.12), p. 16 | The operator norm is defined with the Euclidean vector norm. | `opNorm` uses the supremum vector norm instead (Mathlib's `linfty` operator norm, the maximum absolute row sum), since the sup norm is the one the chapter's contraction arguments use (p. 33). Submultiplicativity (Ex 1.2.9) holds for either. |
| Ex 1.2.3, p. 14 | Weights with `∑ pᵢ = 1`. | Only `pᵢ > 0` is needed for the norm axioms; the normalisation is dropped. |
| Ex 1.2.16, p. 21 | Uniqueness of limits, so the ambient space is Hausdorff. | `[T2Space U]`; automatic for `ℝⁿ`. |
| §1.2.1.4, p. 18 | `A` is `n × n` with `n ≥ 1`, so that the spectrum is nonempty and `‖I‖ = 1`. | `[NeZero n]` on every spectral-radius statement in `NeumannSeries`. |
| (1.15), p. 18 | `ρ(A)` is a maximum over complex eigenvalues of a real matrix. | `specRad A := (spectralRadius ℂ (complexify A)).toReal`; `mem_spectrum_iff_eigenpair` identifies the spectrum with the eigenvalues. |
| Ex 1.2.27, p. 31 | `argmax_x h(x)` exists, so `X` is nonempty. | `[Nonempty X]` in `expectation_maximiser_iff`. |
| (1.24), p. 32 | `min{x ∈ X : Φ(x) ≥ τ}` exists for `τ ∈ [0, 1]`. | The set is nonempty when `τ ≤ 1` (`quantileSet_nonempty`); `quantile` takes that nonemptiness as an argument. |
| Assumption 1.1.1, p. 11 | `W ⊂ ℝ₊` is a finite set of wages. | `Model` indexes offers by a finite type `W` with `wage : W → ℝ`, `wage ≥ 0`; repeated wage values are allowed and harmless. |
| (1.7), p. 11 | `w + βw + β²w + ⋯ = w/(1 − β)`. | Needs `β < 1`, part of Assumption 1.1.1 (`tsum_geometric_wage`). |
| Prop 1.3.1, p. 33 | `T` is a contraction on `V = ℝ^W₊`. | `T` is a contraction on all of `ℝ^W` (`isContractionOn_T_univ`), which gives uniqueness of `v*` among all functions, not only nonnegative ones. `V` closed and nonempty are supplied for Theorem 1.2.3. |
| §1.3.1.3, p. 35 | A `v`-greedy policy satisfies (1.29). | Policies are `W → Bool`; `IsGreedy` is the biconditional `σ(w) = 1 ↔ w/(1 − β) ≥ c + β ∑ v(w')φ(w')`. Ties are accepted, as in the book's `⩾`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Exercise 1.1.1, p. 7 | Whether higher unemployment compensation is detrimental to society | A discussion question with no mathematical claim. |
| Exercise 1.1.3, p. 10 (second half) | Julia function returning the reservation wages for `T` periods | Computational; the `T`-period reservation wage itself is a theorem here. |
| Listings 1.1–1.6, Algorithm 1.1, Figures 1.3, 1.5–1.7, 1.10–1.12 | Code and plots | Computational, no claim beyond the theorems formalised. |
| Exercise 1.3.3, p. 41 | Compare `v*` computed two ways numerically | Computational; the identity `v*(w) = max(w/(1−β), h*)` is a theorem here. |
| p. 12, §1.3.1.3 p. 35 | Bellman's principle of optimality: a `v*`-greedy policy is optimal for the sequence problem (1.6) | The book states it and defers the proof ("later we prove it in a general setting"). Not claimed in this chapter project. |
| Examples 1.0.1–1.0.2, pp. 1–3 | The retailer's inventory problem and the size `11¹⁰⁰` of its state space | Motivational; no theorem. |
| Remarks 1.2.1, 1.2.2, 1.3.1; Example 1.3.1 | Conventions on vectors, functions and states | Descriptive. |
| §1.4 Chapter notes | Literature | Not applicable. |
