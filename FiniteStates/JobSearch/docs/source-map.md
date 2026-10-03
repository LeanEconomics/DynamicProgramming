# Source map

Sargent and Stachurski, *Dynamic Programming*, Volume 1: *Finite States*,
Chapter 1, "Introduction" (pp. 1–41). Result, equation and exercise numbers
are the book's; page numbers are book pages. Lean names are relative to
`SargentStachurski.JobSearch`. Where the Lean statement adds a hypothesis the
book leaves implicit, or departs from the printed claim, see
[corrections](corrections.md).

## §1.2.1.1 Real and complex vectors (pp. 12–13) and §1.2.4.1 Pointwise operations (pp. 29–30)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 12 | `|a| := a ∨ (−a)` | `abs_eq_max_neg'` |
| Ex 1.2.1, p. 13 | `α ∨ (s + t) ≤ s + α ∨ t` for `s ≥ 0` | `max_add_le_add_max` |
| (1.20), p. 29 | `(αu + βv)(x) = αu(x) + βv(x)`, `(uv)(x) = u(x)v(x)` | `smul_add_smul_apply`, `mul_apply'` |
| (1.21), p. 29 | `|u|(x)`, `(u ∨ v)(x)`, `(u ∧ v)(x)` pointwise | `abs_apply'`, `sup_apply'`, `inf_apply'` |
| (1.28), Ex 1.3.1, p. 34 | `|α ∨ x − α ∨ y| ≤ |x − y|`, via Ex 1.2.1 | `max_le_abs_sub_add_max`, `abs_max_sub_max_le` |
| (1.29), p. 35 | `x ↦ α ∨ x` is order preserving | `max_le_max_of_le` |

## §1.2.2.1 Fixed points and §1.2.2.2 Global stability (pp. 20–22)

| Book | Claim | Lean |
| --- | --- | --- |
| p. 20 | Fixed point `Tu* = u*` | Mathlib's `Function.IsFixedPt` |
| Ex 1.2.3, p. 20 | Every point is fixed by the identity | `isFixedPt_id` |
| Ex 1.2.4, p. 20 | `u ↦ u + 1` on `ℕ` has no fixed point | `not_isFixedPt_succ` |
| Ex 1.2.15, p. 21 | Eventually constant iterates give the unique fixed point | `isFixedPt_of_iterate_eventually_const`, `eq_of_isFixedPt_of_iterate_eventually_const` |
| Ex 1.2.16, p. 21 | A limit of iterates where `T` is continuous is a fixed point | `isFixedPt_of_tendsto_iterate` |
| p. 22 | Global stability | `GloballyStable`, `GloballyStable.exists_unique`, `globallyStable_of_tendsto` |
| p. 22 | Invariant set | Mathlib's `Set.MapsTo`; `iterate_mem_of_mapsTo` |
| Ex 1.2.18, p. 22 | The fixed point lies in every closed invariant `C` | `GloballyStable.fixedPt_mem_of_isClosed` (`C` nonempty added) |

## §1.2.2.3 Banach's fixed-point theorem (pp. 22–23) and the function-space restatement (p. 31)

| Book | Claim | Lean |
| --- | --- | --- |
| (1.17), p. 22 | Contraction of modulus `λ` on `U` | `IsContractionOn` |
| Ex 1.2.19, p. 22 | A contraction is continuous and has at most one fixed point in `U` | `IsContractionOn.continuousOn`, `IsContractionOn.fixedPt_unique` |
| Ex 1.2.21, p. 23 | `‖uₘ − uₖ‖ ≤ ∑_{i=m}^{k−1} λⁱ‖u₀ − u₁‖` | `IsContractionOn.norm_iterate_sub_iterate_succ_le`, `IsContractionOn.norm_iterate_sub_iterate_le_sum` |
| Ex 1.2.22, p. 23 | `(uₘ)` is Cauchy; the solution's closed-form bound | `IsContractionOn.cauchySeq_iterate`, `IsContractionOn.norm_iterate_sub_iterate_le` |
| Ex 1.2.23, p. 23 | The limit lies in the closed set `U` | `IsContractionOn.limit_mem` |
| Proof of Thm 1.2.3, p. 23 | The limit is a fixed point (Ex 1.2.16 + Ex 1.2.19) | `IsContractionOn.isFixedPt_of_tendsto` |
| (1.18), p. 23 | `‖Tᵏu − u*‖ ≤ λᵏ‖u − u*‖` | `IsContractionOn.norm_iterate_sub_fixedPt_le`, `IsContractionOn.tendsto_iterate_fixedPt` |
| Thm 1.2.3, p. 23 | Banach: existence, uniqueness, rate | `IsContractionOn.exists_fixedPt`, `IsContractionOn.banach` |
| Thm 1.2.3, p. 23 | "in particular `T` is globally stable on `U`" | `IsContractionOn.globallyStable` |
| Ex 1.2.24, p. 23 | Damped iteration `(1 − α)u + αTu` converges for `0 < α ≤ 1` | `isContractionOn_damped`, `isFixedPt_damped_iff`, `tendsto_damped_iterate` |
| p. 31 | Banach on `ℝ^X`, `X` finite, sup norm | `IsContractionOn.banach_pi` |
