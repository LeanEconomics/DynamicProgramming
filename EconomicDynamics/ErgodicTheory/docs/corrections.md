# Corrections and conventions

Places where a Lean statement differs from Miao's Chapter 4 (draft of 21 April 2013): a claim
corrected, a hypothesis made explicit, or a convention chosen.

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Definition 4.2.2, p. 123 | `A` is shift-invariant if `θA ⊆ A`; this class "is the same as" the σ-algebra of transformation-invariant sets. | It is not a σ-algebra: `A = {0}` is shift-invariant and its complement is not (`shiftInvariant_compl_counterexample`). Every invariant set is shift-invariant (`isShiftInvariant_of_preimage_eq`), and every measurable shift-invariant set equals `⋃ₙ θ⁻ⁿA` up to a null set (`exists_invariant_ae_eq`), so the two ergodicity notions agree (`isErgodicProcess_iff_isErgodic`). In Theorem 4.2.1 `I` is the pullback of the invariant σ-algebra (`invariantField`). |
| Ex 4, p. 129 | `E[f(x)g(z) | F_y] = E[f(x) | F_y]E[g(z) | F_y]` and `E[g(z) | F_{x,y}] = E[g(z) | F_y]` are equivalent, for integrable `f`, `g`. | The second implies the first for each `f` (`ex_4_4`), but the first for one `f` does not give the second: for `f ≡ 1` the first always holds (`ex_4_4_one`), while for a fair coin with `x = z` and `y` constant the second fails (`ex_4_4_counterexample`). The equivalence holds with the first for all bounded `f` (`ex_4_4_of_condExp_eq`). `f`, `g` are taken bounded, since integrable `f`, `g` do not make `fg` integrable. |
| Example 4.1.1, p. 116 | The shift on `(ℝ^∞, B(ℝ^∞), Pr)`. | The shift is measurable (`example_4_1_1_measurable`) but preserves only some measures, e.g. not the point mass at `(1, 0, 0, …)` (`example_4_1_1_not_measurePreserving`). |

## Conventions and departures

| Where | Book | Lean |
| --- | --- | --- |
| Theorem 4.1.1, p. 117 | Birkhoff's theorem, a.s. | Also in `L¹` (`theorem_4_1_1_L1`); the limit is identified with `E[f | I]` (`birkhoffLimit_ae_eq_condExp`). The proof is the copied Meyn–Tweedie one, not the book's `lim sup η̄` argument. |
| Ex 2, p. 129 | `f` integrable. | Integrability is not needed (`ex_4_2`). |
| Example 4.1.2, p. 116 | `n ≥ 2`. | Any `n + 1 ≥ 1` points; ergodicity is proved as well (`example_4_1_2_ergodic`). |
| p. 120 | Functions of IID windows are stationary. | Functions of windows of any stationary process are (`isStationary_comp_window`). |
| Theorem 4.2.2, p. 124 | Items (a) and (b) are literally the same statement. | (b) is read with strictly invariant sets, so (a) ⇔ (b) carries the content of the Definition 4.2.2 correction. |
| Definition 4.2.4, p. 124 | Mixing, with a right-hand side depending on `n`. | Stated as: the difference tends to `0` (`IsMixing`). |
| §4.3, p. 125 | The two-sided chain on `X^ℤ` built by Kolmogorov's theorem. | The one-sided chain on `X^ℕ` (the book's first construction); Exercise 3, (4.4), Lemma 4.3.1 and Theorem 4.3.1 are proved for it. Lemma 4.3.1 is proved with Lévy's upward theorem and stationarity rather than the remote-past argument with Exercise 4. |
| p. 128, footnote 2 | "`π`-a.e. `x ∈ A₁`" versus Definition 3.3.5's "every `x ∈ A₁`". | Lemma 4.3.1 produces the strict form and the restriction lemmas need only the a.e. form, so both readings give the same ergodic measures (`theorem_4_3_1_iff_isErgodicMeasure`). |
| Theorem 4.3.1, p. 126 | Ergodic ⇒ extreme, via `E₁ ∩ E₂ = ∅`. | Via Birkhoff and absolute continuity of `P_{π₁}` with respect to `P_π` (`eq_of_ergodic_of_absolutelyContinuous`). |
| Theorem 4.2.4, p. 125; Ex 7, p. 130 | A central limit theorem; Gaussian sequences with `R_n → 0` are ergodic. | Not formalised in full: Theorem 4.2.4 needs a martingale CLT; for Exercise 7 the reduction to mixing and mixing for characters are proved, but not the passage from characters to sets. |
