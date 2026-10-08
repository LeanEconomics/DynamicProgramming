# Corrections to the source

Places where a claim in Chapter 7 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In each
case the Lean statement proves the stated version and cites the original.
Entries are recorded when found and revised if formalisation shows the finding
itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 7.3.4, p. 233 | For `τ ∈ [0, 1]`, `(R_τ v)(x) = min{y ∈ ℝ : ∑ 1{v(x') ≤ y}P(x, x') ≥ τ}`. | At `τ = 0` every `y` qualifies, so the set is all of `ℝ` and has no minimum. For `τ ∈ (0, 1]` and Markov `P` the minimum exists and is a value of `v` (`isLeast_quantR`); the operator, Exercise 7.3.7 and the quantile preferences (7.20) are formalised for `τ ∈ (0, 1]`. |
| Prop 7.3.4, p. 242 | (a) `bRv ≤ c + Lv` for some `c` and `L ∈ L(ℝ^X)` with `ρ(L) < 1`; `V = [0, v̄]`, `v̄ = (I − L)⁻¹(r + c)`. | `V` is a nonempty order interval containing `0` only if `v̄ ≥ 0`, which needs `L ≥ 0` (then `(I − L)⁻¹ = ∑ Lᵗ ≥ 0`). `globallyStableOn_uzawa_concave` assumes `L ≥ 0`; `c ≥ 0` then follows from (a) at `v = 0`, since `R0 = 0`. |
| Ex 7.1.9, p. 219 | A unique solution `σ ≫ 0` exists iff `ρ(A)^ψ < 1`. | The proof goes through Theorem 7.1.4, which needs `A` irreducible. `existsUnique_kleinmanSol_iff` assumes `P` irreducible, `f ≫ 0` (gross returns are positive) and `β > 0`, which make `A` irreducible. |
| Lemma 7.3.2, p. 239 | Hypotheses include `iℝ^X ⊂ V`. | Exercise 7.3.16 applies the lemma with `V = (0, ∞)^X`, which does not contain every increasing function. `monotone_of_globallyStableOn` and `monotone_koopmans_fixedPt` assume only that `V` contains one increasing function and that `K` maps increasing functions in `V` to increasing functions, which covers both uses. |
| §7.3.1.4, p. 236 | An aggregator has `y ↦ A(x, y)` increasing on `ℝ`. | The CES aggregator `(r^α + βy^α)^{1/α}` is only defined (and increasing) for `y > 0`. `IsAggregator` asks for monotonicity on a set `D` containing the values of the functions in `V` (`D = (0, ∞)` for the CES and CES–Uzawa aggregators, `D = ℝ` otherwise). |

## Proofs the book cites or defers

| Where | Book says | How it is proved here |
| --- | --- | --- |
| Thm 7.1.3, p. 217 | Full proof in Du (1990) or Zhang (2012); uniqueness on p. 349. | `du_concave`: with `1 − λₖ = (1 − δ)ᵏ`, `Tᵏv₁ ≥ (1 − λₖ)v₁ + λₖTᵏv₂` by concavity, so `Tᵏv₂ − Tᵏv₁ ≤ (1 − δ)ᵏ(v₂ − v₁)`, and every orbit is squeezed onto the Knaster–Tarski fixed point. Conditions (i) and (iii) reduce to (ii) and (iv) (`exists_delta_of_lt`), and the convex cases to the concave ones by `v ↦ −T(−v)`. Existence uses Knaster–Tarski; continuity of `T` is not needed. |
| Thm 7.1.4, p. 218 | "A full proof can be found in Stachurski et al. (2022)." | Necessity pairs a positive fixed point with the left Perron–Frobenius eigenvector. Sufficiency: with `e ≫ 0`, `Ae = ρ(A)e`, explicit thresholds give `G(ce) ≫ ce` for small `c` and `G(Ce) ≪ Ce` for large `C` (`exists_thresholds`); any two points of `V` lie in such an interval, on which Du's theorem applies with the convexity or concavity of Exercise 7.1.8. |
| Example 7.3.5, p. 234 | Subadditivity of `R_γ` "follows from Minkowski's inequality"; superadditivity from Bullen (2003). | A level-set argument: with `a = (Pv^γ)^{1/γ}`, `b = (Pw^γ)^{1/γ}`, the point `(v + w)/(a + b)` is a convex combination of `v/a` and `w/b`, which lie on the unit level set of `u ↦ Pu^γ`; convexity of `t^γ` (`γ ≥ 1` or `γ < 0`) or concavity (`0 < γ ≤ 1`) gives the bound (`sum_rpow_add_le`, `le_sum_rpow_add`). |
| Example 7.3.6, (7.17), p. 235 | Cites Föllmer and Knispel (2011). | `log_sum_exp_le`, from the weighted AM–GM inequality, then `concaveOn_entR`. |
| Lemma 7.2.1, p. 224 | Strictness cites a strict Jensen inequality (Liao and Berg, 2018). | Mathlib's strict Jensen on the support of `q` (`entExp_ne_mean`); the equality case is `entExp_eq_mean`. |
| Prop 7.2.2, p. 224 | Proof postponed to §7.3.2.2. | `globallyStable_riskSensitive`, via Proposition 7.3.3. |
| Prop 7.1.2, p. 215 | Concave functions are continuous on open sets (Barbu and Precupanu, 2012). | Mathlib's `ConcaveOn.continuousOn_interior`. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| Thm 7.1.1, Thm 7.1.3, pp. 214, 217 | `T` is a self-map of `V = [v₁, v₂]`, `v₁ ≤ v₂`. | `MapsTo T (Icc v₁ v₂) (Icc v₁ v₂)` and `MonotoneOn T (Icc v₁ v₂)`; convexity and concavity are Mathlib's `ConvexOn`, `ConcaveOn` on the interval. |
| Ex 7.1.1, p. 214 | "A continuum of fixed points". | The identity fixes `t ↦ v₁ + t(v₂ − v₁)`, injective on `[0, 1]` (`exists_continuum_fixedPts`). |
| Ex 7.1.4, p. 216 | `f'` exists. | `f` is differentiable on `(0, ∞)`, as the Inada conditions on `f'` presuppose. |
| Ex 7.1.5, p. 216 | The printed formula is `g(s) = ρ²(1/s + a/η²)⁻¹ + γ`. | Read so (`fajgelbaum`); `ρ > 0` is used only to make `g` well defined as stated. |
| Ex 7.1.7–7.1.8, p. 218 | `h ≥ 0` for `F`; `Av ≫ 0` on `V` for `G`. | `0 ≤ h`; every row of `A` has a positive entry, which irreducibility gives (`Irreducible.exists_pos_row`). |
| Thm 7.1.4, p. 218 | `A` positive (`≥ 0`) and irreducible, `h ≫ 0`, `θ ≠ 0`. | As stated; `ρ(A) > 0` follows from irreducibility. |
| Prop 7.2.2, p. 224 | `β < 1`. | `0 ≤ β < 1`. |
| Ex 7.2.4, p. 225 | Continuous state, `|ρ| < 1`. | Proved for any `ρβ ≠ 1`, `β ≠ 1`, `θ ≠ 0`, with `W` of law `N(0, 1)` under any measure (Mathlib's `HasLaw`). |
| Ex 7.2.6, p. 225 | "Propose a method and confirm it is convergent". | The fixed point is `r + κ` with `κ` solving the linear equation `κ = βκ + βE_θ[r]`; its uniqueness is Proposition 7.2.2 (`riskSensitive_iid_unique`). |
| Ex 7.2.7, p. 228 | `h ≥ 0`. | Also `β > 0` (more generally `b ≫ 0`): with `β = 0` and `h(x) = 0`, `(Kv)(x) = 0 ∉ (0, ∞)`. |
| Prop 7.2.3, p. 228 | `β ∈ (0, 1)`; `h = (1 − β)c^α ≫ 0`. | `0 < β < 1`, `h ≫ 0`; the proof is Proposition 7.3.5 with `b ≡ β`, where `ρ(β^θP)^{1/θ} = β`. |
| Ex 7.3.14, p. 237 | EIS `= d log(y/c)/d log(U_c/U_y)`. | `ces_eis` computes both partial derivatives and proves `log(U_c/U_y) = log((1 − β)/β) + (1 − α) log(y/c)`, so the slope is `1/(1 − α)`. |
| Ex 7.3.16, p. 239 | `c ∈ iℝ^X`. | `c ≫ 0` increasing, `P` irreducible Markov and monotone increasing, `0 < β < 1`, so that Proposition 7.2.3 applies. |
| Prop 7.3.3, Ex 7.3.18, p. 240 | `A` increasing in `y`. | `∀ x, Monotone (A x)` on `ℝ`. |
| Prop 7.3.5, p. 243 | `h, b ∈ V`, `P` irreducible. | `h, b ≫ 0`, `P` irreducible Markov, `α, γ ≠ 0`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| §7.2.1.2, p. 221 | The coin-flip comparison of options A and B, and the rejection of time additivity by data | Illustrative; the point (lifetime utility depends only on marginal distributions) is a property of expectations of sums, outside the chapter's operator theory. |
| Figures 7.1–7.5, Listings 7.1–7.2, Ex 7.2.5 | Plots and code | Computational. |
| Remark 7.2.1, §7.4 | Terminology; literature | Not applicable. |
