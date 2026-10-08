# Corrections to the source

Places where a claim in Chapter 6 of Sargent and Stachurski, *Dynamic Programming*, Volume 2,
is imprecise as printed, relies on an unstated hypothesis, or where the Lean statement departs
from the printed one. In each case the Lean statement proves the corrected or stated version and
cites the original. Entries are recorded when found and revised if formalisation shows the finding
itself to be wrong.

## Gaps in proofs

| Where | Book says | Correction |
| --- | --- | --- |
| Prop 6.1.6, proof, p. 196 | `(Dh)(y, z) = β(z) sup_{a ∈ Γ(y, z)} ∫ ∑_{z'} h(y', z')Q(z, z')R(y, z, a, dy')` is a discount operator on `bX`. | For `h ∈ bX`, a supremum over an uncountable action set need not be Borel measurable in `y`, so `D` need not map `bX` into `bX`. The proof uses `(Dh)(y, z) = β(z) ∑_{z'} sup_{y'} h(y', z') Q(z, z')` (`LDP.Dexo`). It depends on `z` only, so it is measurable; it dominates every `K_σ` (`LDP.K_le_Dexo`); and `Dⁿh = K_Qⁿ m_h` with `m_h(z') = sup_{y'} h(y', z')`, so the book's eventual-contraction argument applies (`LDP.Dexo_isDiscountOperator`). The proposition stands. |
| Prop 6.1.7, proof, p. 198 | `(Dh)(x) = β max_{a ∈ Γ(x)} ∫ h(x')P(x, a, dx')`. | The same measurability problem. `Dh = β (sup h) 𝟙` dominates every `K_σ` and contracts with modulus `β` (`Dsup`, `Dsup_isDiscountOperator`, `K_le_Dsup`). |
| Ex 6.2.1, solution, p. 406 | `D` as a maximum over `c`, and `K_σ ≤ D` since `q(t) ≤ 1`. | The same `Dh = β (sup h) 𝟙` is used. The bound `βq(t) ∫ h dP ≤ β sup h` holds on `bX₊`, which is where a discount operator must dominate (`ReturnsModel.exercise_6_2_1`). |
| Prop 6.1.2, proof, p. 192 | "Regularity is obvious in the finite case". | True, but it needs an argument: finitely many policy operators `T_{σ₁}, …, T_{σ_k}` are pasted into the measurable policy `σ(x) = σ_{i(x)}(x)`, with `i(x)` the least index maximizing `(T_{σ_i}v)(x)` (`LDP.regular_of_isFinite`, `measurable_argmaxSel`). |

## Hypotheses the book leaves implicit, and generalisations

| Where | Point | How it is stated |
| --- | --- | --- |
| Thm A.3.3, p. 351 | Berge's maximum theorem with a measurable selection, cited from Aliprantis and Border. | Its conclusion is `HasMaxSelections Γ`, a hypothesis of Propositions 6.1.3, 6.1.6 and 6.1.7. It is proved for `Γ(x) = [g(x), h(x)]` with `g ≤ h` continuous (`hasMaxSelections_Icc`), which covers every application in the chapter. The selection is the largest maximizer, shown upper semicontinuous and hence Borel. |
| Assumption 6.1.1 (i) | `Γ` nonempty, continuous and compact-valued. | Replaced by `HasMaxSelections Γ`, the conclusion of Theorem A.3.3 that the proofs use. |
| Ex A.3.1 | `X`, `A` subsets of Euclidean space. | Any topological state space, with actions in `ℝ` (`exercise_A_3_1`); Theorem A.3.3 for intervals holds on any sequential state space. |
| Example 6.1.1 | `(x, a) ↦ F(x, a, w)` continuous for every `w`. | For `φ`-almost every `w`, as the book remarks (`example_6_1_1`). |
| Example 6.1.2 | `X = ℝᵐ` with Lebesgue measure. | Any normed group with a translation-invariant measure (`example_6_1_2`). |
| Lemma 6.1.5 | For `K_Q`. | For every bounded linear operator on a Banach lattice (`BanachLattice.lemma_6_1_5`). |
| §6.1.4.2 | `β ∈ bcZ`, nonnegative. | `β : Z → ℝ` nonnegative; with `Z` finite and discrete every function is continuous. |
| Prop 6.2.1, §6.2.2, Ex 6.2.1 | Stock and wealth in `ℝ₊`; `ξ` on `ℝ₊`; `R`, `y` such that wealth stays nonnegative. | Real stock or wealth with `Γ(x) = [0, max(x, 0)]`; any shock distribution; no sign conditions are needed for the optimality results. |
| Example 6.1.8 | `φ(y) = 0` for `y ≤ 0`, so that wealth stays in `ℝ₊`. | Real wealth and any continuous density `φ` with `∫ φ = 1` (`Savings.example_6_1_8`). |

## Statements that differ in form

| Where | Book | Lean |
| --- | --- | --- |
| §6.1.2.1 | `K` a transition kernel from `G` to `X` with `Kv ∈ bG`. | `K(x, a, dx') = β(x, a)P(x, a, dx')` with `β ≥ 0` bounded measurable and `P` stochastic on `X × A` (`LDP`); every kernel in the chapter has this form, and values off `G` are irrelevant. The reward is `r ∈ b(X × A)`. |
| §6.1.2.1 | Feasible policies Borel measurable maps `X → A`. | `LDP.Policy`: measurable selections of `Γ`. |
| (6.6) | `v_σ = (I − K_σ)⁻¹ r_σ = ∑_t K_σ^t r_σ`. | `v_σ` is the unique fixed point of `T_σ`, and it is the limit of the partial sums (`LDP.lifetime_value`). |
| Lemma 6.1.4 | `𝔼_z β₀ ⋯ β_{n−1} h(Z_n)` for a `Q`-Markov process. | For finite `Z` (the case of §6.1.4.2), the expectation is the sum over paths `z = z₀, …, z_n` weighted by `∏ Q(z_t, z_{t+1})` (`Exo.pathExp`). The path-space expectation for general `Z` is not formalised. |
| Ex 6.1.1 | `q = (I − K_Q)⁻¹h`. | `q` is the unique solution of `q = h + K_Q q` and the limit of `∑_{t<n} K_Q^t h`; for finite `Z`, of `∑_{t<n} 𝔼_z β₀ ⋯ β_{t−1} h(Z_t)` (`Exo.exercise_6_1_1`). |
| Prop 6.1.6 | `K` of product form. | Stated as the integral identity `∫ h dP(y, z, a) = ∫ ∑_{z'} h(y', z')Q(z, z')R(y, z, a, dy')` and `β(y, z, a) = β(z)`; Assumption 6.1.2 is stated slice by slice, as in the book. |
| Example 6.1.6 | "cannot be represented as an LDP". | The risk-sensitive policy operator is not affine in `v` on a two-state example (`example_6_1_6`), so it is not of the form `r_σ + K_σ v`. |

## Not formalised

| Where | Content | Reason |
| --- | --- | --- |
| Example 6.1.7 | The real option problem is not an LDP | Informal (it concerns equivalence classes in `L¹`). |
| Figures 6.1–6.7 | Correspondences, simulated policies, kernels and stationary distributions | Numerical or illustrative. |
| §6.3 | Chapter notes | Not mathematical claims. |
