# Corrections to the source

Places where a claim in Chapter 2 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In
each case the Lean statement proves the stated version and cites the
original. Entries are recorded when found and revised if formalisation shows
the finding itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 2.2.12, p. 54 | The bounded subsets of `ℝⁿ` have no greatest element under inclusion. | False for `n = 0`, where `ℝ⁰` is a point and `{•}` is the greatest bounded set. Proved for `n ≥ 1` (`not_exists_isGreatest_bounded`). |
| Ex 2.1.7, p. 47 | Assumes `T` twice continuously differentiable and uses a second-order Taylor expansion. | A continuous first derivative at `u*` suffices: the mean value theorem gives `eₖ₊₁ = |T'(ξₖ)| eₖ` with `ξₖ → u*` (`error_ratio_near`, `tendsto_error_ratio`). Proved under the weaker hypothesis. |
| Example 2.2.11, p. 63 | Two specific random variables with `X ≤ Y` have dominated laws. | Proved in general: on any finite probability space, `X ≤ Y` pointwise implies `law(X) ≼_F law(Y)` (`fosd_law_of_le`); the example is an instance. |
| Lemma 2.3.3, p. 70 | `‖Aᵏh‖^{1/k} → ρ(A)` for `h ≫ 0`, cited from Krasnosel'skii et al. (1972) without specifying the norm. | Proved for the supremum norm on vectors and the induced ℓ∞ operator norm (`tendsto_norm_pow_mulVec_rpow`); other norms follow from norm equivalence and are not stated separately. |
| Lemma 2.2.3, p. 59 | Each `T_σ` is a contraction "on `V`" with no norm named. | Proved for the supremum norm (`isContractionOn_upperEnvelope`), the only norm for which Lemma 2.2.2 gives the bound. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Ex 2.2.4, p. 52 | `≪` fails reflexivity only when `X ≠ ∅`; on `X = ∅` the relation is vacuous and reflexive. | `[Nonempty X]` in `not_strictLt_refl`, `strictLt_not_isPartialOrder`. |
| Example 2.2.10, p. 61 | `P = {1, …, n}` with `n` unspecified; `x ↦ −x` and `x ↦ 1{x ≤ 2}` fail to be increasing only when `P` has at least two, respectively three, elements. | Stated on `P = Fin 5 = {0, …, 4}` (`monotone_two_mul`, `monotone_indicator_ge`, `not_monotone_neg`, `not_monotone_indicator_le`); the witnesses are `0 < 1` and `2 < 3`. |
| Ex 2.2.33, p. 64 | `X = {1, 2}` with `1 < 2`. | `X = Fin 2` with `0 < 1` in the two roles (`fosd_fin_two_iff`). |
| Lemma 2.2.5 (ii), p. 64 | The converse `G_φ ≤ G_ψ ⇒ φ ≼_F ψ` is for `X ⊂ ℝ`, i.e. totally ordered; the book's proof is in its Appendix B. | `[LinearOrder X]` in `fosd_of_ccdf_le`, proved by Abel summation after transporting along an order isomorphism with `Fin n`; `φ, ψ` distributions. The forward direction (i) holds on any finite poset. |
| Lemma 2.2.4, p. 62 | `U` is such that `u + c ∈ U` for `u ∈ U`, `c ≥ 0`, and `T` maps `U` to itself. | `hU : ∀ u ∈ U, ∀ c, 0 ≤ c → u + (fun _ => c) ∈ U` and `MapsTo T U U` in `isContractionOn_of_blackwell`; `0 ≤ β < 1`. |
| Ex 2.2.38, p. 67 | Global stability of the Solow–Swan map on `(0, ∞)`, proved in Chapter 1 (Ex 1.2.26). | Taken as a hypothesis of `solow_fixedPt_le`; each project is self-contained and Chapter 1's closed-form proof is not repeated. The comparison `g₁ ≤ g₂` and order preservation are proved here. |
| Ex 2.2.39, p. 67 | `h*` increasing in `β`; wages nonnegative, `∑ φ = 1`, `φ ≥ 0`, `β ∈ [0, 1)`. | All stated; `contMap_fixedPt_le` compares fixed points in `ℝ₊`. |
| Prop 2.2.7, p. 67 | `M ⊆ ℝⁿ` with the pointwise order, so limits preserve `≤`. | Stated for any topological space with a closed order (`[OrderClosedTopology]`), which covers `ℝⁿ`. |
| p. 45 | The derivative criterion `|g'(x*)| < 1 ⇒` local stability is sketched for `g` "differentiable". | `g` differentiable near `x*` with derivative continuous at `x*` (`locallyStable_of_abs_deriv_lt_one`); the mean value theorem then gives a contraction on a ball. |
| §2.3.1, p. 69 | `A` is `n × n` with `n ≥ 1`, so the spectrum is nonempty. | `[NeZero n]` on every spectral-radius statement, including Theorem 2.3.1. |
| Thm 2.3.1, p. 69 | The eigenvector `e` is "nonzero and nonnegative". | `e ≠ 0` and `∀ i, 0 ≤ e i`; the proof produces `∑ e = 1`. |
| Ex 2.3.2 (iii), p. 71 | A stationary distribution is a row vector `ψ ≥ 0`, `ψ𝟙 = 1`, `ψP = ψ`. | `IsMarkov.exists_stationary` states exactly this via `ᵥ*`. |
| Ex 2.3.3, p. 71 | "there is no `h` with `Ph ≥ h + ε`" for `ε > 0`. | `ε > 0` stated; `h + ε` is `h + (fun _ => ε)`. |
| §2.3.2, p. 72 | Rates `d, b, α, λ ∈ (0, 1)`. | Fields of `LakeModel`; `1 + g > 0` follows. |
| Ex 2.3.7, p. 73 | `x̄` is "the" eigenvector with `1ᵀx̄ = 1`. | Uniqueness is proved (`LakeModel.eq_xbar_of_eigen`), from the two scalar eigen-equations. |
| Thm 2.3.4, p. 76 | Linear operators on `ℝⁿ`; `ℝ^X` identified with `ℝⁿ`. | Stated on `ℝ^X` for a `Fintype X` with `DecidableEq`, via Mathlib's `LinearMap.toMatrix'`. |
| Example 2.2.9, p. 60 | Integration over `[a, b]` of continuous functions. | `a ≤ b` and `f, g` continuous on `[a, b]` (`integral_mono_of_le`), with `f ≤ g` required only on `[a, b]`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Thm 2.1.3 (Hartman–Grobman), Cor 2.1.4, p. 45 | Local conjugacy to the linearisation at a hyperbolic fixed point; local stability when all eigenvalues of the Jacobian have modulus `< 1`. | Quoted by the book from the literature without proof; a substantial theorem of smooth dynamics not in Mathlib. The one-dimensional derivative criterion is proved instead. |
| §2.1.4, p. 48 | Quadratic convergence of Newton's fixed-point iteration, cited from Atkinson and Han (2005). | Not claimed; the Newton map and its fixed points are formalised. |
| §2.1.4, pp. 48–51 | Newton iteration for the Solow–Swan model, Figures 2.1–2.3, Listing 2.1 | Computational. |
| Thm 2.3.1, p. 69 | The irreducible and everywhere-positive cases: `ρ(A) > 0`, positive and unique eigenvectors, and the convergence `r(A)^{−m}Aᵐ → eεᵀ` (2.11). | Not claimed here; the plan proves them with Chapter 6, where irreducibility and ergodicity are treated. The nonnegative case, which the chapter uses, is proved. |
| Ex 2.3.2 (iv), p. 71 | Irreducible `P` has a unique, everywhere-positive stationary distribution. | Rests on the irreducible Perron–Frobenius theorem; deferred with it. |
| §2.3.2, p. 74 | The long-run approximation `Aᵗx₀ ≈ (1 + g)ᵗn₀x̄` and Figure 2.4 | Rests on (2.11). |
| Ex 2.2.35, p. 64 | The distributional phrasing "`X ≼_F Y` implies `Q_τ(X) ≤ Q_τ(Y)`" | Proved for the laws `φ ≼_F ψ`, which is what the exercise means. |
| §2.3.3, p. 75 | "Operators on infinite-dimensional spaces need not be matrices" | Descriptive; Volume 2 material. |
| §2.4 Chapter notes | Literature | Not applicable. |
