# Corrections and conventions

Places where a Lean statement differs from the book: a hypothesis made explicit, a claim corrected,
or a convention chosen.

## Corrections

| Where | Book | Lean |
| --- | --- | --- |
| Ex 3.7c, p. 49 | `C^k[a, b]` with `‖f‖ = ∑ᵢ αᵢ max |f⁽ⁱ⁾|` is complete if and only if every `αᵢ > 0`. | The "if" holds (`isComplete_ckNorm`). The "only if" is false. On `C²[a, b]`, `α = (1, 0, 1)` gives a norm, `max |f| + max |f″|`, and it is complete (`ex_3_7c_counterexample`). The reason is the interpolation inequality `max |f′| ≤ (4/(b − a)) max |f| + ((b − a)/2) max |f″|` (`interpolation`). With `α₀ = 0` the formula is not a norm at all, since the constant `1` gets size `0` (`not_isNorm_of_alpha0`). With `α_k = 0` and `k = 1` the space is not complete: this is Ex 3.7b (`ex_3_7b`). The correct characterisation is completeness iff `α₀ > 0` and `α_k > 0`; only the cases above are formalised. |
| Theorem 3.2, p. 50 | A contraction on a complete metric space has exactly one fixed point. | The space must be nonempty: the empty space is complete and has no fixed point. `theorem_3_2` assumes `[Nonempty S]`, as does `corollary_2`. |
| Corollary 1, p. 52 | If `S'` is closed and `T(S') ⊆ S'`, then `v ∈ S'`. | `S'` must be nonempty, since `S' = ∅` satisfies the hypotheses. `corollary_1` assumes `S'.Nonempty`. |
| Ex 3.3d, Ex 3.4f, p. 45 | `ρ(x, y) = ∫ₐᵇ |x(t) − y(t)| dt` is a metric and `∫ₐᵇ |x(t)| dt` is a norm on `C[a, b]`. | This needs `a < b`. When `a = b`, `C[a, a]` contains nonzero functions of size `0`. Definiteness also uses the continuity of `x` (`integral_pos_of_pos`, `l1_eq_zero_iff`). |
| Ex 3.14c, p. 60 | Where does `Γ` fail to be l.h.c.? | At `|x| = 1` (`ex_3_14c`: `Γ` is l.h.c. at `x` iff `|x| < 1`). For `|x| > 1`, `Γ(x)` is empty, and `IsLHC` includes nonemptiness. |

## Hypotheses weakened or made explicit

| Where | Book | Lean |
| --- | --- | --- |
| Ex 3.3f, p. 45 | `f` is continuous, strictly increasing and strictly concave, with `f(0) = 0`. | Continuity and strictness of concavity are not needed. `isMetric_comp` assumes `f` strictly increasing and concave on `[0, ∞)` with `f(0) = 0`. |
| Theorem 3.1, p. 47 | `X ⊆ ℝˡ`. | `X` is any topological space, and `C(X)` is Mathlib's space of bounded continuous functions `X →ᵇ ℝ` (`theorem_3_1`). The proof follows the book's three steps. |
| Theorem 3.3, p. 54 | `T : B(X) → B(X)` with (a) monotonicity and (b) discounting; `T` is a contraction. | `theorem_3_3` proves the inequality `‖Tf − Tg‖ ≤ β‖f − g‖` for bounded `f, g`. It needs (a) and (b) only on bounded functions and does not need `T` to preserve boundedness. `X` is nonempty, so that the sup distance is defined. |
| pp. 54–55 | The growth model's operator `max_{0 ≤ y ≤ f(k)} {U[f(k) − y] + βv(y)}`. | `bellmanOp` takes a general nonempty-valued feasibility correspondence `Γ` and a bounded return `F(x, y)`, with `sup` in place of `max`. |
| Ex 3.1, p. 41 | `w₀(k) = U[f(k) − g₀(k)] + βw₀[g₀(k)]`. | `exercise_3_1` is stated for a general one-period return `R(k)`, here `U[f(k) − g₀(k)]`. It holds whenever the series defining `w₀(k)` converges. |
| Theorem 3.6, Lemma 3.7, Theorem 3.8, pp. 62–64 | `f : X × Y → ℝ` is continuous. | `f` need only be continuous on the graph `A` of `Γ`, as Lemma 3.7 already states. `X` is a metric space and `Y` a normed space. In Lemma 3.7 and Theorem 3.8, `ArgmaxSetup` collects the hypotheses: `Γ` nonempty-, compact- and convex-valued and continuous, and `f(x, ·)` strictly concave. |
| Theorem 3.4, p. 60 | `Y ⊆ ℝᵐ`. | `Y` is a proper metric space, in which closed bounded sets are compact (`theorem_3_4`). |
| Theorem 3.5, p. 61 | `X ⊆ ℝˡ`, `Y ⊆ ℝᵐ`. | `X` and `Γ(x)` lie in real normed spaces `E` and `F` (`theorem_3_5`). As in the book, the conclusion is at interior points. |
| Ex 3.14b, p. 60 | `H` is concave, and `Γ` is compact-valued. | Only concavity of `H(x, ·)` for each `x` is used, and only boundedness of `Γ(x)` at the point `x` itself. The space of `y` is any proper real normed space (`ex_3_14b`). |
| Ex 3.14a, p. 60 | `H` is strictly increasing in its first `l` arguments and strictly decreasing in its last `m`. | Monotonicity is stated in the vector order: `x < x'` means `x ≤ x'` and `x ≠ x'`, which the coordinatewise reading implies. `Γ` is defined on `ℝˡ₊` with values in `ℝᵐ₊`, the domain of `H`, and "compact-valued" is used as bounded at every point (`ex_3_14a`). |
| Ex 3.15, p. 61 | `Γ` compact-valued and u.h.c., `X` compact. | `isCompact_graph` assumes only that `X` is compact and `Γ` u.h.c. at every point. |

## Conventions

| Where | Book | Lean |
| --- | --- | --- |
| §3.1, pp. 43–47 | Metric spaces, normed spaces, convergence, Cauchy sequences and completeness. | The book's definitions are stated for an arbitrary distance function `ρ : S → S → ℝ` (`IsMetric`, `IsNorm`, `Converges`, `IsCauchy`, `IsCompleteFor`), so that one set can carry several metrics. Mathlib's notions are linked by `isNorm_norm` and `isCompleteFor_of_completeSpace`. |
| Ex 3.2, p. 44 | "Show that the following are (not) vector spaces." | A set of vectors or functions with the usual operations is a vector space exactly when it is a subspace of the ambient space (`IsSubspace`). Ex 3.2c, the space of all real sequences, is the whole space `ℕ → ℝ` (`isSubspace_univ`). |
| Ex 3.4b, 3.4d–e, p. 45 | The max and sup norms. | The library uses Mathlib's sup norms on `Fin l → ℝ`, bounded sequences (`ellInf`, `supNorm`) and `C[a, b]`. It proves that they are the book's maxima and suprema (`abs_le_max_norm`, `max_norm_le`, `abs_le_supNorm`, `supNorm_le`). |
| §3.1 | `C[a, b]`. | `C(Icc a b, ℝ)`. Integrals use the continuous extension `ext` of a function to `ℝ`. |
| Ex 3.7, p. 49 | `C¹[a, b]`, `C^k[a, b]`. | A function is recorded together with its derivatives, as `F : Fin (k + 1) → C[a, b]` with `F (i + 1)` the derivative of `F i` on `[a, b]`, one-sided at the ends (`IsCk`, `ckSub`). For `a < b` the derivatives are determined by `F 0`. |
| Ex 3.10, pp. 53–54 | The unique fixed point of `T` is differentiable and is the unique solution on `[0, τ]`. | Existence is stated with one-sided derivatives at `0` and `τ`. Uniqueness is stated for any `x` continuous on `[0, τ]` with `x(0) = c` and `x′(s) = f(x(s))` on `(0, τ)`, which is a weaker requirement than differentiability on `[0, τ]`. The modulus is `τB` for any `τ` with `τB < 1` (`ex_3_10b`). |
| §3.3, p. 56 | Correspondences between subsets of Euclidean spaces; u.h.c. is defined for compact-valued correspondences. | `X` and `Y` are metric spaces. `IsLHC` and `IsUHC` are the book's sequential definitions, each including nonemptiness of `Γ(x)`. Compact-valuedness is a separate hypothesis where it is used. |
| Ex 3.11b, 3.12b, pp. 57–58 | `Γ : ℝᵏ → ℝ^{l+m}` and its projection to `ℝˡ`. | `Γ : X → Y × Z`, projected to `Y` (`isUHC_proj`, `isLHC_proj`). |
| Ex 3.11f, 3.12f, pp. 58–59 | Products of `k` correspondences. | Products over any finite index type (`isUHC_pi`, `isLHC_pi`). |
| Ex 3.12d, p. 59 | Convex-valued correspondences into `ℝᵐ`. | `ℝᵐ` is `Fin m → ℝ` with the sup norm. All norms on it are equivalent, so interiors are the usual ones (`isLHC_inter_of_interior`). The proof separates `z` from the convex hull of points near the `2m` vertices `z ± 2δeⱼ` (`no_separation`). |
| Ex 3.13c, p. 59 | `Γ(x, z) = {y ∈ ℝˡ₊ : 0 ≤ yᵢ ≤ fᵢ(xⁱ, z), i = 1, …, l; and ∑ xⁱ ≤ x}`. | As printed, the `xⁱ` are free. `budget` reads them as a split of the input vector `x ∈ ℝˡ₊` into `x¹, …, xˡ ∈ ℝˡ₊` with `∑ xⁱ ≤ x`. `y` is in `Γ(x, z)` if some split gives `0 ≤ yᵢ ≤ fᵢ(xⁱ, z)`. Each `fᵢ` is continuous on `ℝˡ × ℝᵐ` and nonnegative on the orthant. A continuous function on `ℝˡ₊ × ℝᵐ` extends by `fᵢ(max(a, 0), z)`, so this is no restriction. |
| Ex 3.13a, 3.14a, 3.16c | `ℝ₊`, `ℝˡ₊`. | The subtypes `NNR` and `Orthant l`. |
