# Corrections to the source

Places where a claim in Chapter 6 of Sargent and Stachurski, *Dynamic
Programming*, Volume 1, is false, imprecise, or relies on an unstated
hypothesis, and where the Lean statement departs from the printed one. In each
case the Lean statement proves the stated version and cites the original.
Entries are recorded when found and revised if formalisation shows the finding
itself to be wrong.

## Claims that need a changed statement

| Where | Book says | Finding |
| --- | --- | --- |
| Ex 6.1.2, p. 186 | `v` is increasing whenever `P` is monotone increasing, `π` is increasing and `r` is decreasing. | False without `π ≥ 0`. Take `X = {1, 2}`, `P = I`, `r = (1, 0.1)`, `π = (−2, −1.9)`: `ρ(L) = 1/1.1 < 1`, and `v = (−4, −20.9)` is decreasing, because a negative increasing function times the increasing factor `1/(1 + r)` is decreasing. `monotone_firmValue` adds `π ≥ 0` (and `r > −1`, so that the factors are positive as the book assumes of `b`). |
| Prop 6.2.3, Ex 6.2.4, p. 196 | "Use Lemma 6.1.3" to prove `ρ(L_σ) = ρ(L_Z)`. | Lemma 6.1.3 as printed has a kernel `R(y, y')` on `Y` that does not depend on `z`, but under a policy the kernel is `R(y, σ(y, z), y')`, which does. `specRad_productDiscountOp` proves the lemma for any kernel `R((y, z), y')` with unit row sums, from which `Exogenous.specRad_Lσ` and Proposition 6.2.3 follow; the printed lemma is the special case `specRad_productDiscountOp_isMarkov`. |
| Lemma 6.1.2, p. 187 | "`ρ(L) < 1` iff there exists `t ∈ ℕ` with `ℓₜ < 1`", citing Stachurski and Zhang (2021). | Proved directly (`specRad_lt_one_iff_exists_norm_pow_mulVec_one_lt`): for `L ≥ 0`, `ℓₜ = ‖Lᵗ𝟙‖_∞ = ‖Lᵗ‖`, `‖Lᵗ‖ → 0` when `ρ(L) < 1`, and `ρ(L) ≤ ‖Lᵗ‖^{1/t}`. The index `t` is required to be positive (`ℓ₀ = 1`). |
| Prop 6.2.2, pp. 194–195 | "In §8.2.2 we prove a result that includes Proposition 6.2.2 as a special case." | Proved here without Chapter 8, from the order preservation and global stability of each `T_σ` (Lemma 6.2.1, Exercise 6.2.2): `v* ≤ Tv*` always; for a `v*`-greedy `σ`, `v* ≤ T_σ v*` gives `v* ≤ v_σ`. No contraction property of `T` is used. |
| Thm 2.3.1, (2.11), p. 69 | `ρ(A)⁻ᵗAᵗ → eεᵀ` for `A ≫ 0`, "with `e` and `ε` normalised so that `⟨ε, e⟩ = 1`"; the book cites Meyer (2000). | Proved (`tendsto_pow_of_pos`) entry by entry by conjugating to the positive Markov matrix `P = ρ⁻¹D⁻¹AD`, `D = diag e`, and applying Dobrushin's estimate (Exercise 3.1.7); the limit `ε = ψ*/e` is the left eigenvector with `⟨ε, e⟩ = ∑ψ* = 1`. The convergence is stated coordinatewise rather than in a matrix norm. |
| Thm 2.3.1, p. 69 | For irreducible `A` the eigenvectors are "everywhere positive and unique". | Made precise: `ρ(A) > 0`; every nonnegative nonzero eigenvector has eigenvalue `ρ(A)` and is everywhere positive; two such are proportional (`Irreducible.pos_of_mulVec_eq_smul`, `Irreducible.eq_specRad_of_mulVec_eq_smul`, `Irreducible.exists_eq_smul_of_mulVec_eq_smul`). Irreducibility is `∑_{k≥1}Aᵏ ≫ 0` with `k ≥ 1`, as on p. 69; with `k = 0` allowed the `1 × 1` zero matrix would be irreducible with `ρ = 0`. |

## Hypotheses the book leaves implicit

| Where | Implicit hypothesis | How it is stated |
| --- | --- | --- |
| (6.3), (6.6), (6.19), §6.3.1.6 | Lifetime values are expectations `E_x[∑ₜ β₁⋯βₜ h(Xₜ)]` along the chain. | Taken in the operator form the book derives, `∑ₜ Lᵗh` with `(Lᵗh)(x) = E_x[β₁⋯βₜ h(Xₜ)]` by (6.6); the chain itself is not constructed, as in the Chapter 3 and 5 projects. Theorem 6.1.1 is then `summable_pow_mulVec` and `inv_mulVec_eq_tsum`; the recursion (6.7) is `pow_succ_mulVec`. |
| Thm 6.1.1, p. 185 | `b : X × X → (0, ∞)`. | The results on `L` only need `L` to be a matrix with `ρ(L) < 1` (`inv_mulVec_eq_tsum` etc.); `b ≥ 0` enters where nonnegativity of `L` is used (Lemmas 6.1.2–6.1.4). |
| Ex 6.1.1, p. 186 | `βₜ = 1/(1 + rₜ)` with `rₜ = r(Xₜ)`, so `b(x, x') = 1/(1 + r(x'))` under the convention (6.2) `β₀ = 1`. | `firmDiscountOp r P = discountOp (fun _ x' => 1/(1 + r x')) P`. Example 6.1.1's `β₀ = 1/(1 + r₀)` differs from (6.2) by the factor `1/(1 + r(x))`, which does not affect finiteness. |
| Ex 6.1.2, p. 186 | `P` "monotone increasing" (§3.2.2); `r > −1`. | `MonotoneKernel P`: `Ph` increasing for every increasing `h`; `∀ x, −1 < r x`. |
| Lemma 6.1.2, p. 186 | `L ≥ 0` (so that `ℓₜ = ‖Lᵗ𝟙‖_∞`); `X` nonempty. | `hL : ∀ x x', 0 ≤ L x x'`, `[Nonempty X]` throughout the spectral results. |
| Ex 6.1.3, p. 187 | `P` irreducible with unique stationary `ψ*`; the weighted norm `‖h‖_* = ∑|h(x)|ψ*(x)`. | Any stationary distribution `ψ` is used; irreducibility supplies `ψ ≫ 0` (Exercise 2.3.2 (iv)), and the expectation `E_{ψ}[β₁⋯βₜ] = ⟨ψ, Lᵗ𝟙⟩` is squeezed between `(min ψ)‖Lᵗ𝟙‖_∞` and `‖Lᵗ𝟙‖_∞` instead of invoking norm equivalence (`tendsto_dotProduct_pow_mulVec_one_rpow`). |
| Lemma 6.1.3, p. 188 | `b : Z × Z → ℝ₊`, `Q`, `R` Markov, `Y`, `Z` nonempty. | `b ≥ 0`, `Q ≥ 0`, `R ≥ 0` with unit row sums, `[Nonempty Y] [Nonempty Z]`; `Q` need not have unit row sums. |
| Lemma 6.1.4, p. 189 | "`L` a positive linear operator on `ℝ^X`." | A matrix `L ≥ 0` (`hL : ∀ x x', 0 ≤ L x x'`), equivalent by Exercise 2.3.11. |
| Thm 6.1.5, p. 190 | "there exists `k ∈ ℕ` and a norm such that `Tᵏ` is a contraction". | Stated for the given norm of a complete normed group with `k ≥ 1` (`globallyStable_of_iterate_contraction`); Exercise 6.1.5 (`exists_iterate_contraction_of_norm_equiv`) then transfers the hypothesis between norms, taking the equivalence constants `N_b ≤ c₂Nₐ`, `Nₐ ≤ c₁N_b` as hypotheses, since any two norms on `ℝ^X` have them. |
| Ex 6.1.5, p. 190 | "`‖·‖ₐ`, `‖·‖_b` norms on `ℝ^X`". | Only the two equivalence inequalities are used; the maps `Nₐ, N_b` need not be norms. |
| Prop 6.1.6, p. 191 | The Euclidean norm. | The supremum norm, with modulus `‖Lᵏ‖` in the induced ℓ∞ operator norm; the conclusion is the same. |
| Prop 6.1.7, p. 191 | `U` closed under `v, c ∈ U, c ≥ 0 ⇒ v + c ∈ U`; the inequality "for all `c, v ∈ ℝ^X`". | `∀ v ∈ U, ∀ c ≥ 0, v + c ∈ U`; monotonicity and the inequality are required for `v ∈ U` and `c ≥ 0` only, since `T` is only a self-map of `U`. |
| §6.2.1.1, p. 192 | `β`, `r`, `P` defined on `G × X`. | Given on all of `X × A × X` with `β ≥ 0` and `P(x, a, ·)` a distribution for every `a`, as in the Chapter 5 project; off-`G` values never enter. |
| Assumption 6.2.1, p. 193 | `Σ` is the set of feasible policies. | `SpectralCondition M := ∀ σ, IsFeasible σ → specRad (Lσ σ) < 1`. |
| Lemma 6.2.1, p. 193 | `v_σ` is defined as the fixed point of `T_σ`. | `vσ σ := (1 − Lσ σ)⁻¹ *ᵥ rσ σ` for every `σ` (Mathlib's matrix inverse is total); under `ρ(L_σ) < 1` it is the unique fixed point (`isFixedPt_vσ`, `eq_vσ_of_isFixedPt`), and `v*` is defined from these `v_σ` without assuming Assumption 6.2.1, which the theorems about `v*` take as the hypothesis `hM`. |
| Ex 6.2.1, p. 194 | `βₜ = β(Xₜ₋₁, σ(Xₜ₋₁), Xₜ)`, `(Xₜ)` `P_σ`-Markov. | Operator form `v_σ = ∑ₜ L_σᵗ r_σ` (`vσ_eq_tsum`) with `L_σ = discountOp (β(·, σ(·), ·)) P_σ` (`Lσ_eq_discountOp`). |
| Ex 6.2.3, p. 194 | (6.20) for `(x, a) ∈ G`. | `∀ x a x', a ∈ Γ x → β x a x' * P x a x' ≤ L x x'`. |
| §6.2.1.4, p. 195 | VFI, OPI and HPI converge under Assumption 6.2.1 (Chapter 8). | Not claimed under Assumption 6.2.1 alone. The per-step facts are proved (`vσ_le_vσ_of_isGreedy`, `isOptimal_of_hpi_fixed`, `opi_one_step_eq_vfi`, `tendsto_opi_inner`), and VFI converges under (6.20) (`tendsto_iterate_T_of_dominated`) and in the exogenous discount model (`Exogenous.tendsto_iterate_T`). |
| §6.2.1.5, p. 195–196 | `Γ` from `Y × Z` to `A`; `r` on `G ⊂ Y × A`; `R` a kernel from `G` to `Y`. | `Γ : Y × Z → Finset A`, `r : Y → A → ℝ`, `R : Y → A → Y → ℝ` with nonnegative entries and unit row sums for every `(y, a)`. |
| §6.2.2, p. 198 | `β(z) = 1/(1 + r(z))`; the AR(1) discretisation of Listing 6.1. | Any `β : Z → ℝ₊` and Markov `Q`; the test `ρ(L) < 1` is the hypothesis `hρ`. The inventory kernel is the one of the Chapter 5 project, clamped at `K` off the feasible set. |
| §6.3.1.4, p. 205 | `m, g : X × X → ℝ₊`. | No sign restriction is needed for the pricing identities; `m ≫ 0`, `d ≫ 0` appear in Exercise 6.3.1 as stated. |
| Ex 6.3.1, p. 206 | "whenever `m, d ≫ 0`"; `P` Markov. | `hm : ∀ x x', 0 < m x x'`, `hd : ∀ x, 0 < d x`, `hP : IsMarkov P`, needed for `Ad ≫ 0`. |
| Ex 6.3.2, p. 206 | `β ∈ ℝ₊`. | `0 ≤ β`; then `ρ(A) = β` (`specRad_adOp_const`), so the condition is `β < 1`. |
| Ex 6.3.5, (6.38), p. 207 | `Vₜ = E_t[Mₜ₊₁ exp(κ)(1 + Vₜ₊₁)]` from `Πₜ = E_t[Mₜ₊₁(Dₜ₊₁ + Πₜ₊₁)]`. | Stated for a finite conditional distribution with weights `wᵢ` and `D, D'ᵢ ≠ 0` (`price_dividend_ratio`); `exp(κ) = D'/D`. |
| (6.39)–(6.40), p. 207–208 | `∫ exp(κ(x, η))φ(dη)`. | The expected gross growth factor is a given function `κbar : X → ℝ` (`pdOp`); for Exercise 6.3.7 it is computed from the Gaussian moment generating function (`integral_exp_add_mul_gaussian`). |
| Ex 6.3.7, p. 208 | `m(x, x') = E[β exp(−γ(μ_c + x + σ_c η_c))]` and `∫ exp(κ)φ(dη) = E[exp(μ_d + x + σ_d η_d)]`, independent standard normal shocks. | `lucas_growth_factor`: the product of the two expectations, for random variables with law `gaussianReal 0 1` under a measure `ν` (Mathlib's `HasLaw`), equals `β exp(−γμ_c + μ_d + (1 − γ)x + (γ²σ_c² + σ_d²)/2)`; independence is not needed because the factors are separate expectations. |
| §6.3.3, p. 209–210 | Two types `i ∈ {1, 2}`; `d ≥ 0`; `β ∈ (0, 1)`. | Any nonempty finite index type `ι` of beliefs; `0 ≤ d`; `0 ≤ β < 1`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| §6.1.1.1, Example 6.1.1, Figures 6.1–6.4 | Interest rate data, the firm valuation motivation, the contour plot of `ρ(L)` | Descriptive and computational. |
| (6.8), §B.2 | Interchange of expectation and infinite sum | The operator form makes it `Pi.tsum_apply`; the probabilistic statement is Volume 2 material. |
| §6.1.2.1, p. 187–188 | The AR(1) discretisation (6.12) and Figure 6.3 | Computational. |
| §6.1.3.1, p. 190 | "eventually contracting with respect to every norm" as a statement quantifying over all norms on `ℝ^X` | Exercise 6.1.5 is proved with explicit equivalence constants; quantifying over norm structures on a fixed type is not expressed. |
| §6.2.1.4, p. 195 | Convergence of VFI, OPI and HPI under Assumption 6.2.1; finite termination of HPI | Chapter 8; see above for what is proved. |
| §6.2.1.6, Figure 6.4, footnote 2 | Hills et al. (2019) calibration, `ρ(L) = 0.9996` | Computational. |
| §6.2.2, Figures 6.5–6.6, Listing 6.1, Exercise 6.3.8, Listing 6.2, Figure 6.7 | Simulations, timings, code | Computational. |
| §6.3.1.1–§6.3.1.3 | Risk-neutral pricing and its implausibility, Examples 6.3.1–6.3.4, the stochastic discount factor from the agent's first-order condition, the general specification (6.31) and the existence of an SDF | Economics outside the chapter's mathematical content; the Markov forms (6.27) and (6.32) are formalised. |
| (6.33), (6.38) | Pricing equations as conditional expectations of random variables | Taken in Markov form (6.34) and finite form (`price_dividend_ratio`). |
| §6.3.3, p. 209 | The derivation of (6.42) from the Harrison–Kreps model | The book sets it aside; (6.42) is the starting point. |
| §6.4 Chapter notes | Literature | Not applicable. |
