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

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Ex 1.2.18, p. 22 | The closed invariant set `C` must be nonempty: `∅` is closed and invariant and contains no fixed point. | `hCne : C.Nonempty` in `GloballyStable.fixedPt_mem_of_isClosed`. |
| Thm 1.2.3, p. 23 | `U` nonempty (stated on p. 22 for contractions, not repeated in the theorem); `λ ≥ 0` (stated on p. 31). | `hne : U.Nonempty`; `IsContractionOn.nonneg`. |
| Thm 1.2.3, p. 23 | "closed in `ℝⁿ` ... with respect to some norm": the statement is for `ℝⁿ`, the proof uses only completeness. | Stated for any complete normed group `E`; `ℝⁿ` under any norm is an instance. |
| Ex 1.2.16, p. 21 | Uniqueness of limits, so the ambient space is Hausdorff. | `[T2Space U]`; automatic for `ℝⁿ`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Exercise 1.1.1, p. 7 | Whether higher unemployment compensation is detrimental to society | A discussion question with no mathematical claim. |
| Exercise 1.1.3, p. 10 (second half) | Julia function returning the reservation wages for `T` periods | Computational; the `T`-period reservation wage itself is a theorem here. |
| Listings 1.1–1.6, Algorithm 1.1, Figures 1.3, 1.5–1.7, 1.10–1.12 | Code and plots | Computational, no claim beyond the theorems formalised. |
| Exercise 1.3.3, p. 41 | Compare `v*` computed two ways numerically | Computational; the identity `v*(w) = max(w/(1−β), h*)` is a theorem here. |
